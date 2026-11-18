#!/usr/bin/env python3
"""Build, query, or serve the offline RealRooted navigation index over MCP stdio."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from typing import Any, TextIO

sys.dont_write_bytecode = True

from agent_index import ROOT, SCHEMA_VERSION, Search, build_index, source_state, write_index

DEFAULT_CACHE = Path("/cargo-target/mcp-tools/rr-nav")
VERSIONS = ("2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05")
STRING = {"type": "string"}
LIMIT = {"type": "integer", "minimum": 1, "maximum": 50}
TOOL_ARGUMENTS = {
    "find_start": ({"query": STRING, "kind": STRING, "property": STRING,
                    "topic": STRING, "limit": LIMIT}, []),
    "get_page": ({"slug": STRING, "name": STRING, "limit": LIMIT,
                  "offset": {"type": "integer", "minimum": 0}}, []),
    "get_declaration": ({"name": STRING}, ["name"]),
    "route_links": ({"name": STRING, "limit": LIMIT,
                     "offset": {"type": "integer", "minimum": 0}}, ["name"]),
    "search_declarations": ({"query": STRING, "conclusion_key": STRING,
                             "module_prefix": STRING, "limit": LIMIT}, ["query"]),
    "index_status": ({}, []),
}
DESCRIPTIONS = {
    "find_start": "Find catalog pages, families, theorems and routes to start a proof.",
    "get_page": "Look up a catalog page by slug, section/slug, or selected Lean name.",
    "get_declaration": "Look up a public source declaration and its catalog and route links.",
    "route_links": "Follow polytool route, tactic route, or Lean name links in both directions.",
    "search_declarations": "Search source-parsed public declarations, without elaboration.",
    "index_status": "Report source revisions, fingerprint, layers, size and refresh status.",
}


def tool_list() -> list[dict[str, Any]]:
    """Describe the six bounded, read-only MCP tools."""
    return [{"name": name, "description": DESCRIPTIONS[name],
             "inputSchema": {"type": "object", "properties": properties,
                             "required": required, "additionalProperties": False},
             "annotations": {"readOnlyHint": True}}
            for name, (properties, required) in TOOL_ARGUMENTS.items()]


class Navigator:
    """Refresh a per-checkout external cache before every query, including status."""

    def __init__(self, repo: Path, polytool: Path | None = None,
                 cache: Path = DEFAULT_CACHE, force_python: bool = False):
        self.repo = repo.resolve()
        self.polytool = polytool.resolve() if polytool else None
        self.cache = cache.resolve()
        self.force_python = force_python
        if self.cache == self.repo or self.cache.is_relative_to(self.repo):
            raise ValueError("cache must be outside the repository")
        if any((parent / ".git").exists() for parent in (self.cache, *self.cache.parents)):
            raise ValueError("cache must be outside every Git repository")
        if "Dropbox" in self.cache.parts:
            raise ValueError("cache must be outside Dropbox")
        key = hashlib.sha256((str(self.repo) + str(self.polytool)).encode()).hexdigest()[:20]
        self.path = self.cache / key / "agent-index.json"
        self.index: dict[str, Any] | None = None
        self.rebuilds = 0
        self.refresh()

    def refresh(self) -> None:
        """Never answer using an index whose source content or revision moved."""
        state = source_state(self.repo, self.polytool)
        if self.index is not None and self.index["sources"] == state:
            return
        index = None
        try:
            cached = json.loads(self.path.read_text(encoding="utf-8"))
            if cached.get("schema_version") == SCHEMA_VERSION and cached.get("sources") == state:
                index = cached
        except (OSError, ValueError):
            pass
        if index is None:
            index = build_index(self.repo, self.polytool)
            write_index(index, self.path)
            self.rebuilds += 1
        self.index = index
        for name in ("declaration_search", "start_search"):
            previous = getattr(self, name, None)
            if previous is not None:
                previous.db.close()
        self.declarations = {d["name"]: d for d in index["declarations"]}
        self.pages = {p["slug"]: p for p in index["pages"]}
        self.tactics = {r["name"]: r for r in index["tactic_routes"]}
        self.poly_routes = {r["name"]: r for r in index["polytool_routes"]}
        self.declaration_search = Search(index["declarations"], self.force_python)
        records = []
        for page in index["pages"]:
            records.append({**page, "type": "page", "page": page["slug"]})
            for name in page["theorems"] + page["definitions"]:
                decl = self.declarations[name]
                records.append({**decl, "type": "declaration", "summary": page["summary"]})
        for family in index["families"]:
            # The catalog family entry names the selected declaration and its page title.
            name = family["name"]
            decl = self.declarations[name]
            records.append({**decl, **family, "type": "family", "page": decl["page"],
                            "label": family["family"]})
        records += [{**r, "type": "tactic_route"} for r in index["tactic_routes"]]
        records += [{**r, "type": "polytool_route"} for r in index["polytool_routes"]]
        self.start_search = Search(records, self.force_python)

    def links(self, name: str, limit: int = 20, offset: int = 0) -> dict[str, Any]:
        """Resolve immediate route edges, avoiding transitive route-component explosions."""
        names = {name} if name in self.declarations or "." in name else set()
        tactics = [self.tactics[name]] if name in self.tactics else []
        polys = [self.poly_routes[name]] if name in self.poly_routes else []
        for route in tactics:
            names.update(route["theorems"])
        for route in polys:
            names.update(route["lean_names"])
            tactics += [self.tactics[n] for n in route["tactic_routes"] if n in self.tactics]
        if not polys:
            polys = [r for r in self.poly_routes.values()
                     if names.intersection(r["lean_names"])
                     or any(t["name"] in r["tactic_routes"] for t in tactics)]
        if not tactics:
            tactics = [r for r in self.tactics.values() if names.intersection(r["theorems"])]
        # Include a route's cited names when looking up the route itself.
        if name in self.tactics or name in self.poly_routes:
            for r in polys:
                names.update(r["lean_names"])
            for r in tactics:
                names.update(r["theorems"])
        declarations = []
        for n in sorted(names):
            decl = self.declarations.get(n, {})
            declarations.append({"name": n, "unresolved_at_head": not bool(decl),
                                 **{k: decl[k] for k in ("module", "source_path", "source_line",
                                                        "page") if k in decl}})
        tactics = list({r["name"]: r for r in tactics}.values())
        return {
            "name": name, "declarations": declarations[offset:offset + limit],
            "tactic_routes": tactics[offset:offset + limit],
            "polytool_routes": polys[offset:offset + limit],
            "pages": [self.page_brief(p) for p in sorted({d["page"] for d in declarations
                                                         if "page" in d})][:limit],
            "totals": {"declarations": len(declarations), "tactic_routes": len(tactics),
                       "polytool_routes": len(polys)},
            "offset": offset,
        }

    def page_brief(self, slug: str) -> dict[str, Any]:
        page = self.pages[slug]
        return {k: page[k] for k in ("slug", "title", "url", "kind", "references")}

    def compact(self, record: dict[str, Any]) -> dict[str, Any]:
        """Keep search hits bounded; full statements are available via exact lookup."""
        keys = ("type", "name", "label", "title", "module", "source_path", "source_line",
                "rust_path", "conclusion_key", "uses", "property", "object", "headline")
        result = {k: record[k] for k in keys if k in record}
        result["statement"] = record.get("statement", "")[:1500]
        if isinstance(record.get("page"), str) and record["page"] in self.pages:
            result["page"] = self.page_brief(record["page"])
        if "name" in record:
            name = record["name"]
            result["routes"] = {
                "tactic": [r["name"] for r in self.tactics.values() if name in r["theorems"]],
                "polytool": [r["name"] for r in self.poly_routes.values()
                             if name in r["lean_names"]],
            }
        return result

    def call(self, tool: str, arguments: dict[str, Any]) -> dict[str, Any]:
        """Validate tool arguments, refresh sources, then return compact JSON data."""
        if tool not in TOOL_ARGUMENTS:
            raise ValueError(f"unknown tool: {tool}")
        properties, required = TOOL_ARGUMENTS[tool]
        if not isinstance(arguments, dict) or set(arguments) - properties.keys():
            raise ValueError("invalid tool arguments")
        if any(k not in arguments for k in required):
            raise ValueError("missing required argument")
        for key, value in arguments.items():
            schema = properties[key]
            if schema["type"] == "string" and not isinstance(value, str):
                raise ValueError(f"{key} must be a string")
            if schema["type"] == "integer":
                if type(value) is not int or not schema.get("minimum", 0) <= value:
                    raise ValueError(f"invalid {key}")
                if value > schema.get("maximum", sys.maxsize):
                    raise ValueError(f"invalid {key}")
        self.refresh()
        limit = arguments.get("limit", 20)
        offset = arguments.get("offset", 0)
        if tool == "index_status":
            result = {
                "sources": self.index["sources"], "checkout_head": self.index["revision"],
                "layers": ["catalog", "tactic_routes", "source_declarations"]
                + (["polytool_routes"] if self.polytool else []),
                "counts": {k: len(self.index[k]) for k in (
                    "pages", "families", "declarations", "tactic_routes", "polytool_routes")},
                "search_backend": self.start_search.backend,
                "build_seconds": self.index["build_seconds"], "cache_path": str(self.path),
                "bytes": self.path.stat().st_size, "rebuilds_this_process": self.rebuilds,
                "declaration_mode": "source-parsed; not elaborated or axiom-audited",
            }
        elif tool == "route_links":
            result = self.links(arguments["name"], limit, offset)
        elif tool == "get_declaration":
            name = arguments["name"]
            decl = self.declarations.get(name)
            result = {"declaration": decl, "links": self.links(name, limit),
                      "unresolved_at_head": decl is None}
        elif tool == "get_page":
            slug = arguments.get("slug") or self.declarations.get(
                arguments.get("name", ""), {}).get("page", "")
            slug = slug.strip("/").split("/")[-1]
            if slug not in self.pages:
                raise ValueError("unknown catalog page")
            page = self.pages[slug]
            names = page["definitions"] + page["theorems"]
            result = {"page": page,
                      "references": {key: self.index["references"][key]
                                     for key in page["references"]},
                      "declarations": [self.declarations[n] for n in names[offset:offset + limit]],
                      "families": [f for f in self.index["families"]
                                   if f["name"] in names],
                      "routes": {n: self.compact(self.declarations[n])["routes"]
                                 for n in names if any(self.compact(self.declarations[n])[
                                     "routes"].values())},
                      "total_declarations": len(names), "offset": offset}
        else:
            search = self.start_search if tool == "find_start" else self.declaration_search
            hits = []
            seen = set()
            ranked = search.ranked(arguments.get("query", ""))
            if tool == "find_start":
                # Curated headline theorems are the catalog's intended starting points.
                ranked = sorted(((i, score * (1.8 if search.records[i].get("headline")
                                             is True else 1)) for i, score in ranked),
                                key=lambda pair: (-pair[1], pair[0]))
            for i, score in ranked:
                record = search.records[i]
                page = self.pages.get(record.get("page", ""), {})
                if tool == "find_start":
                    if arguments.get("kind") and page.get("kind") != arguments["kind"]:
                        continue
                    if arguments.get("topic") and page.get("topic") != arguments["topic"]:
                        continue
                    if arguments.get("property") and record.get("property") != arguments[
                        "property"
                    ]:
                        continue
                    # A kind-only listing returns pages once, rather than all their declarations.
                    if (not arguments.get("query") and not arguments.get("property")
                            and record["type"] != "page"):
                        continue
                if arguments.get("conclusion_key") and record.get("conclusion_key") != arguments[
                    "conclusion_key"
                ]:
                    continue
                if not record.get("module", "").startswith(arguments.get("module_prefix", "")):
                    continue
                identity = record.get("name") or record.get("slug")
                if identity in seen:
                    continue
                seen.add(identity)
                hits.append({**self.compact(record), "score": round(score, 6)})
                if len(hits) == limit:
                    break
            result = {"hits": hits}
        return {"index_revision": self.index["revision"], "stale": False, **result}


def serve(navigator: Navigator, source: TextIO = sys.stdin, sink: TextIO = sys.stdout) -> None:
    """Serve newline-delimited JSON-RPC 2.0 per the MCP stdio transport."""
    initialized = False
    ready = False
    for line in source:
        request: Any = None
        request_id = None
        try:
            try:
                request = json.loads(line)
            except ValueError:
                raise RpcError(-32700, "Parse error")
            if not isinstance(request, dict) or request.get("jsonrpc") != "2.0":
                raise RpcError(-32600, "Invalid Request")
            request_id = request.get("id")
            if "id" in request and type(request_id) not in (int, float, str, type(None)):
                request_id = None
                raise RpcError(-32600, "Invalid request id")
            method = request.get("method")
            params = request.get("params", {})
            if not isinstance(method, str) or not isinstance(params, dict):
                raise RpcError(-32600, "Invalid Request")
            if "id" not in request:
                if method == "notifications/initialized" and initialized:
                    ready = True
                continue
            if method == "initialize":
                if initialized:
                    raise RpcError(-32600, "Already initialized")
                if not isinstance(params.get("protocolVersion"), str):
                    raise RpcError(-32602, "protocolVersion is required")
                version = params["protocolVersion"]
                initialized = True
                result = {"protocolVersion": version if version in VERSIONS else VERSIONS[0],
                          "capabilities": {"tools": {"listChanged": False}},
                          "serverInfo": {"name": "rr-nav", "version": "0.1.0"}}
            elif method == "ping":
                result = {}
            elif not ready:
                raise RpcError(-32000, "Complete initialize and notifications/initialized first")
            elif method == "tools/list":
                result = {"tools": tool_list()}
            elif method == "tools/call":
                if not isinstance(params.get("name"), str):
                    raise RpcError(-32602, "Tool name is required")
                if params["name"] not in TOOL_ARGUMENTS:
                    raise RpcError(-32602, "Unknown tool")
                try:
                    data = navigator.call(params["name"], params.get("arguments", {}))
                    result = {"content": [{"type": "text", "text": json.dumps(
                        data, ensure_ascii=False)}], "isError": False}
                except (ValueError, OSError, RuntimeError) as error:
                    result = {"content": [{"type": "text", "text": str(error)}], "isError": True}
            else:
                raise RpcError(-32601, "Method not found")
            response = {"jsonrpc": "2.0", "id": request_id, "result": result}
        except RpcError as error:
            # Invalid JSON/requests receive errors; valid notifications never receive replies.
            response = {"jsonrpc": "2.0", "id": request_id,
                        "error": {"code": error.code, "message": str(error)}}
        sink.write(json.dumps(response, ensure_ascii=False) + "\n")
        sink.flush()


class RpcError(Exception):
    """A JSON-RPC protocol error (distinct from a failed tool execution)."""

    def __init__(self, code: int, message: str):
        super().__init__(message)
        self.code = code


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("build", "query", "serve"):
        subparser = subparsers.add_parser(command)
        subparser.add_argument("--repo", type=Path, default=ROOT)
        subparser.add_argument("--polytool", type=Path)
        subparser.add_argument("--cache", type=Path, default=Path(os.environ.get(
            "RR_NAV_CACHE", str(DEFAULT_CACHE))))
        if command == "build":
            subparser.add_argument("--output", type=Path, required=True)
        if command == "query":
            subparser.add_argument("tool", choices=TOOL_ARGUMENTS)
            subparser.add_argument("arguments", nargs="?", default="{}", help="JSON object")
    args = parser.parse_args()
    try:
        if args.command == "build":
            index = build_index(args.repo, args.polytool)
            write_index(index, args.output)
            print(json.dumps({"output": str(args.output), "bytes": args.output.stat().st_size,
                              "build_seconds": index["build_seconds"]}))
        else:
            navigator = Navigator(args.repo, args.polytool, args.cache)
            if args.command == "serve":
                serve(navigator)
            else:
                print(json.dumps(navigator.call(args.tool, json.loads(args.arguments)),
                                 ensure_ascii=False))
        return 0
    except (ValueError, OSError, RuntimeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
