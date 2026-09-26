#!/usr/bin/env python3
"""Parse and render the curated RealRooted challenge catalogue.

This module deliberately implements a small, conservative subset of Lean
source syntax.  It is a catalogue source guard, not a Lean parser: an
ambiguous selected declaration is an error and is left for the Lean audit to
resolve.  The companion audit verifies selected constants in Lean's
environment after a successful build.
"""

from __future__ import annotations

import hashlib
import html
import json
import pathlib
import posixpath
import re
import subprocess
import tomllib
from dataclasses import dataclass
from html.parser import HTMLParser
from typing import Any, Iterable
from urllib.parse import urlsplit


BASE_PATH = "/RealRooted/"
SECTIONS = ("concepts", "families", "theorems")
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
NAME_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)+")
SLUG_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)*")
METADATA_RE = re.compile(r"<!--\s*realrooted-catalog\s*\n(.*?)-->", re.DOTALL)
CONTENT_RE = re.compile(
    r"<!--\s*realrooted-catalog-content\s*-->\s*\n?(.*?)"
    r"<!--\s*/realrooted-catalog-content\s*-->",
    re.DOTALL,
)
DECLARATION_RE = re.compile(
    r"^\s*(?P<attributes>(?:@\[[^\n]*\]\s*)*)"
    r"(?P<modifiers>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|opaque|instance)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
END_NAMESPACE_RE = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$")
IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$"
)


class CatalogError(ValueError):
    """A deterministic catalogue source or audit validation error."""


@dataclass(frozen=True)
class CatalogItem:
    name: str
    expected_kind: str
    module: str | None


@dataclass(frozen=True)
class CatalogPage:
    source_path: str
    section: str
    slug: str
    definitions: tuple[CatalogItem, ...]
    theorems: tuple[CatalogItem, ...]
    content: str
    title: str

    @property
    def items(self) -> tuple[CatalogItem, ...]:
        return self.definitions + self.theorems

    @property
    def url(self) -> str:
        return f"{BASE_PATH}{self.section}/{self.slug}/"


@dataclass(frozen=True)
class SourceDeclaration:
    name: str
    actual_kind: str
    source_path: str
    source_line: int
    deprecated: bool = False


def strip_comments_and_strings(text: str) -> str:
    """Replace comments and strings by whitespace without moving source lines."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        char = text[index]
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
            continue
        if char == "/" and next_char == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
            continue
        if char == '"':
            in_string = True
            output.append(" ")
            index += 1
            continue
        output.append(char)
        index += 1
    return "".join(output)


def _doc_comments(text: str) -> list[str]:
    """Return module documentation comments, preserving their contents."""
    comments: list[str] = []
    index = 0
    while True:
        start = text.find("/-!", index)
        if start == -1:
            return comments
        depth = 1
        cursor = start + 3
        while cursor < len(text) and depth:
            if text.startswith("/-", cursor):
                depth += 1
                cursor += 2
            elif text.startswith("-/", cursor):
                depth -= 1
                cursor += 2
            else:
                cursor += 1
        if depth:
            raise CatalogError("unterminated module documentation comment")
        comments.append(text[start + 3 : cursor - 2])
        index = cursor


def _source_error(path: str, message: str) -> CatalogError:
    return CatalogError(f"{path}: {message}")


def _read_items(path: str, raw: Any, expected_kind: str) -> tuple[CatalogItem, ...]:
    if raw is None:
        return ()
    if not isinstance(raw, list) or not raw:
        raise _source_error(path, f"{expected_kind}s must be a nonempty array of tables")
    result: list[CatalogItem] = []
    seen: set[str] = set()
    for index, record in enumerate(raw, start=1):
        if not isinstance(record, dict) or set(record) - {"name", "module"}:
            raise _source_error(path, f"invalid {expected_kind} record {index}")
        name = record.get("name")
        module = record.get("module")
        if not isinstance(name, str) or not NAME_RE.fullmatch(name):
            raise _source_error(path, f"{expected_kind} record {index} needs a fully qualified name")
        if module is not None:
            valid_module = isinstance(module, str) and MODULE_RE.fullmatch(module)
            if isinstance(module, str) and module.endswith(".lean"):
                module_path = pathlib.PurePosixPath(module)
                valid_module = (
                    not module_path.is_absolute()
                    and ".." not in module_path.parts
                    and module_path.parts[:1] == ("RealRooted",)
                )
            if not valid_module:
                raise _source_error(
                    path, f"{expected_kind} record {index} has an invalid module"
                )
        if name in seen:
            raise _source_error(path, f"duplicate {expected_kind} declaration {name}")
        seen.add(name)
        result.append(CatalogItem(name, expected_kind, module))
    return tuple(result)


def _published_title(path: str, content: str) -> str:
    lines = content.splitlines()
    headings = [line[2:].strip() for line in lines if re.fullmatch(r"#\s+.+", line)]
    if len(headings) != 1:
        raise _source_error(path, "published content must contain exactly one H1")
    reference_at = next(
        (index for index, line in enumerate(lines) if re.fullmatch(r"##\s+References\s*", line)),
        None,
    )
    if reference_at is None:
        raise _source_error(path, 'published content must contain a "## References" section')
    if not any(line.strip() for line in lines[reference_at + 1 :]):
        raise _source_error(path, "References must not be empty")
    return headings[0]


def parse_challenge_source(source_path: str, text: str) -> CatalogPage | None:
    """Parse one opted-in module, or return ``None`` if it is not curated."""
    comments = _doc_comments(text)
    metadata_matches: list[tuple[int, re.Match[str]]] = []
    content_matches: list[tuple[int, re.Match[str]]] = []
    for comment_index, comment in enumerate(comments):
        metadata_matches.extend((comment_index, match) for match in METADATA_RE.finditer(comment))
        content_matches.extend((comment_index, match) for match in CONTENT_RE.finditer(comment))
    marker_count = text.count("realrooted-catalog")
    if not metadata_matches and not content_matches:
        if marker_count:
            raise _source_error(source_path, "catalogue markers must occur in a module doc comment")
        return None
    if len(metadata_matches) != 1 or len(content_matches) != 1:
        raise _source_error(source_path, "requires exactly one metadata and one content block")
    metadata_comment, metadata_match = metadata_matches[0]
    content_comment, content_match = content_matches[0]
    if metadata_comment != content_comment or marker_count != 3:
        raise _source_error(source_path, "catalogue blocks must occur together in one module doc comment")
    try:
        metadata = tomllib.loads(metadata_match.group(1))
    except tomllib.TOMLDecodeError as error:
        raise _source_error(source_path, f"invalid TOML metadata: {error}") from error
    if not isinstance(metadata, dict):
        raise _source_error(source_path, "metadata must be a TOML table")
    allowed = {"version", "section", "slug", "definitions", "theorems"}
    unknown = set(metadata) - allowed
    if unknown:
        raise _source_error(source_path, f"unknown metadata keys: {', '.join(sorted(unknown))}")
    if metadata.get("version") != 1:
        raise _source_error(source_path, "metadata requires version = 1")
    section = metadata.get("section")
    slug = metadata.get("slug")
    if section not in SECTIONS:
        raise _source_error(source_path, f"section must be one of {', '.join(SECTIONS)}")
    if not isinstance(slug, str) or not SLUG_RE.fullmatch(slug):
        raise _source_error(source_path, "slug must be lowercase hyphenated text")
    definitions = _read_items(source_path, metadata.get("definitions"), "definition")
    theorems = _read_items(source_path, metadata.get("theorems"), "theorem")
    if not definitions and not theorems:
        raise _source_error(source_path, "requires at least one definition or theorem")
    content = content_match.group(1).strip()
    return CatalogPage(
        source_path=source_path,
        section=section,
        slug=slug,
        definitions=definitions,
        theorems=theorems,
        content=content,
        title=_published_title(source_path, content),
    )


def _tracked_challenge_paths(repo_root: pathlib.Path) -> list[pathlib.Path]:
    try:
        result = subprocess.run(
            ["git", "ls-files", "-z", "--", "RealRooted/Challenges"],
            cwd=repo_root,
            capture_output=True,
            check=True,
            text=False,
        )
    except (OSError, subprocess.CalledProcessError):
        return sorted((repo_root / "RealRooted" / "Challenges").rglob("*.lean"))
    paths = [
        repo_root / entry.decode("utf-8")
        for entry in result.stdout.split(b"\0")
        if entry.endswith(b".lean")
    ]
    return sorted(paths)


def load_catalogue(repo_root: pathlib.Path) -> tuple[CatalogPage, ...]:
    """Load and validate every opted-in tracked challenge module."""
    pages: list[CatalogPage] = []
    for path in _tracked_challenge_paths(repo_root):
        page = parse_challenge_source(
            path.relative_to(repo_root).as_posix(), path.read_text(encoding="utf-8")
        )
        if page is not None:
            pages.append(page)
    paths: set[str] = set()
    for page in pages:
        if page.url in paths:
            raise CatalogError(f"duplicate catalogue URL {page.url}")
        paths.add(page.url)
    return tuple(sorted(pages, key=lambda page: (SECTIONS.index(page.section), page.title, page.slug)))


def canonical_catalogue_data(pages: Iterable[CatalogPage]) -> dict[str, Any]:
    """The frozen, prose-independent selected-declaration digest input."""
    return {
        "schema_version": 1,
        "pages": [
            {
                "source_path": page.source_path,
                "section": page.section,
                "slug": page.slug,
                "definitions": [item.name for item in page.definitions],
                "theorems": [item.name for item in page.theorems],
            }
            for page in sorted(pages, key=lambda page: page.source_path)
        ],
    }


def catalog_digest(pages: Iterable[CatalogPage]) -> str:
    payload = json.dumps(
        canonical_catalogue_data(pages), sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def module_source_path(repo_root: pathlib.Path, module: str) -> pathlib.Path:
    if module.endswith(".lean"):
        candidate = repo_root / module
    else:
        candidate = repo_root / (module.replace(".", "/") + ".lean")
    if not candidate.is_file():
        raise CatalogError(f"owning module {module!r} does not name a source file")
    return candidate


def module_name_for_path(repo_root: pathlib.Path, source_path: pathlib.Path) -> str:
    return ".".join(source_path.relative_to(repo_root).with_suffix("").parts)


def _local_imports(source_path: pathlib.Path) -> set[str]:
    clean = strip_comments_and_strings(source_path.read_text(encoding="utf-8"))
    return {
        match.group(1)
        for line in clean.splitlines()
        if (match := IMPORT_RE.match(line)) is not None
    }


def _module_in_import_closure(
    repo_root: pathlib.Path, challenge_path: pathlib.Path, owner_path: pathlib.Path
) -> bool:
    """Check local imports only; external dependencies cannot own a selection."""
    owner_module = module_name_for_path(repo_root, owner_path)
    pending = [module_name_for_path(repo_root, challenge_path)]
    seen: set[str] = set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        if current == owner_module:
            return True
        try:
            current_path = module_source_path(repo_root, current)
        except CatalogError:
            continue
        pending.extend(_local_imports(current_path) - seen)
    return False


def _qualified_name(namespace: list[str], name: str) -> str:
    prefix = ".".join(namespace)
    if not prefix or name.startswith("RealRooted.") or name.startswith(prefix + "."):
        return name
    return f"{prefix}.{name}"


def source_declarations(repo_root: pathlib.Path, source_path: pathlib.Path) -> dict[str, SourceDeclaration]:
    """Find ordinary public declaration headers in one Lean source file."""
    relative_path = source_path.relative_to(repo_root).as_posix()
    clean = strip_comments_and_strings(source_path.read_text(encoding="utf-8"))
    namespaces: list[str] = []
    found: dict[str, SourceDeclaration] = {}
    pending_deprecated = False
    for line_number, line in enumerate(clean.splitlines(), start=1):
        namespace_match = NAMESPACE_RE.match(line)
        if namespace_match:
            pending_deprecated = False
            namespaces.extend(namespace_match.group(1).split("."))
            continue
        end_match = END_NAMESPACE_RE.match(line)
        if end_match:
            pending_deprecated = False
            ending = end_match.group(1).split(".")
            if namespaces[-len(ending) :] == ending:
                del namespaces[-len(ending) :]
            continue
        declaration_match = DECLARATION_RE.match(line)
        stripped = line.strip()
        if not declaration_match:
            if stripped.startswith("@["):
                pending_deprecated = pending_deprecated or "deprecated" in stripped
            elif stripped:
                pending_deprecated = False
            continue
        modifiers = declaration_match.group("modifiers").split()
        attributes = declaration_match.group("attributes")
        deprecated = pending_deprecated or "deprecated" in attributes
        pending_deprecated = False
        if "private" in modifiers:
            continue
        raw_kind = declaration_match.group("kind")
        raw_name = declaration_match.group("name")
        actual_kind = "theorem" if raw_kind in {"theorem", "lemma"} else "definition"
        if raw_kind in {"opaque", "class", "instance"}:
            actual_kind = raw_kind
        name = _qualified_name(namespaces, raw_name)
        if name in found:
            raise CatalogError(f"{relative_path}:{line_number}: ambiguous declaration {name}")
        found[name] = SourceDeclaration(
            name, actual_kind, relative_path, line_number, deprecated
        )
    return found


def resolve_item(
    repo_root: pathlib.Path, page: CatalogPage, item: CatalogItem
) -> SourceDeclaration:
    module = item.module or page.source_path.removesuffix(".lean").replace("/", ".")
    owner_path = module_source_path(repo_root, module)
    challenge_path = repo_root / page.source_path
    if item.module is not None and not _module_in_import_closure(repo_root, challenge_path, owner_path):
        raise CatalogError(
            f"{page.source_path}: owning module {module} is outside this module's import closure"
        )
    declarations = source_declarations(repo_root, owner_path)
    declaration = declarations.get(item.name)
    if declaration is None:
        raise CatalogError(f"{page.source_path}: cannot resolve {item.name} in {module}")
    if declaration.actual_kind != item.expected_kind:
        raise CatalogError(
            f"{page.source_path}: {item.name} is a {declaration.actual_kind}, "
            f"not a {item.expected_kind}"
        )
    if declaration.deprecated:
        raise CatalogError(f"{page.source_path}: {item.name} is a deprecated compatibility alias")
    if item.expected_kind == "definition" and re.search(
        r"(?:Statement|Target|Route|Inputs|Backend)$", item.name
    ):
        raise CatalogError(f"{page.source_path}: {item.name} looks like a statement scaffold")
    return declaration


def validate_sources(repo_root: pathlib.Path, pages: Iterable[CatalogPage]) -> dict[str, SourceDeclaration]:
    resolved: dict[str, SourceDeclaration] = {}
    for page in pages:
        for item in page.items:
            declaration = resolve_item(repo_root, page, item)
            if item.name in resolved:
                raise CatalogError(f"duplicate selected declaration {item.name}")
            resolved[item.name] = declaration
    return resolved


def revision_at(repo_root: pathlib.Path) -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            check=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise CatalogError("cannot determine Git revision") from error
    revision = result.stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise CatalogError("Git did not return a full revision")
    return revision


def validate_audit_report(
    report_path: pathlib.Path,
    pages: Iterable[CatalogPage],
    resolved: dict[str, SourceDeclaration],
    revision: str,
) -> dict[str, Any]:
    """Validate the frozen post-Lean audit report interface."""
    try:
        report = json.loads(report_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CatalogError(f"invalid audit report {report_path}: {error}") from error
    if not isinstance(report, dict) or set(report) != {
        "schema_version", "revision", "catalog_digest", "lean_toolchain", "declarations"
    }:
        raise CatalogError("audit report has an invalid schema")
    if report["schema_version"] != 1 or report["revision"] != revision:
        raise CatalogError("audit report revision does not match the checked-out source")
    if report["catalog_digest"] != catalog_digest(pages):
        raise CatalogError("audit report catalogue digest does not match the selected declarations")
    if not isinstance(report["lean_toolchain"], str) or not report["lean_toolchain"]:
        raise CatalogError("audit report lacks its Lean toolchain")
    declarations = report["declarations"]
    if not isinstance(declarations, list):
        raise CatalogError("audit report declarations must be an array")
    by_name: dict[str, dict[str, Any]] = {}
    required = {
        "name", "expected_kind", "actual_kind", "source_path", "source_line", "axioms"
    }
    for record in declarations:
        if not isinstance(record, dict) or set(record) != required:
            raise CatalogError("audit report has an invalid declaration record")
        name = record["name"]
        if not isinstance(name, str) or name in by_name:
            raise CatalogError("audit report has duplicate or invalid declaration names")
        if record["expected_kind"] not in {"definition", "theorem"}:
            raise CatalogError("audit report has an invalid expected declaration kind")
        if record["actual_kind"] != record["expected_kind"]:
            raise CatalogError(f"audit reports kind mismatch for {name}")
        if not isinstance(record["source_path"], str) or not isinstance(record["source_line"], int):
            raise CatalogError(f"audit report source location is invalid for {name}")
        axioms = record["axioms"]
        if not isinstance(axioms, list) or axioms != sorted(axioms) or not all(
            isinstance(axiom, str) for axiom in axioms
        ):
            raise CatalogError(f"audit report axioms are invalid for {name}")
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise CatalogError(f"audit reports unapproved axioms for {name}: {sorted(unexpected)}")
        by_name[name] = record
    if set(by_name) != set(resolved):
        raise CatalogError("audit report does not cover exactly the selected declarations")
    for name, source in resolved.items():
        record = by_name[name]
        if (
            record["expected_kind"] != source.actual_kind
            or record["source_path"] != source.source_path
            or record["source_line"] != source.source_line
        ):
            raise CatalogError(f"audit report source location mismatch for {name}")
    return report


def _safe_url(url: str) -> str | None:
    parsed = urlsplit(url)
    if parsed.scheme and parsed.scheme.lower() not in {"http", "https", "mailto"}:
        return None
    if any(character.isspace() or ord(character) < 32 for character in url):
        return None
    return url


def render_markdown(markdown: str) -> str:
    """Render the deliberate Markdown subset, escaping raw HTML by default."""
    blocks: list[str] = []
    paragraph: list[str] = []
    list_items: list[str] = []
    code_lines: list[str] = []
    in_code = False

    def flush_paragraph() -> None:
        if paragraph:
            blocks.append(f"<p>{_inline(' '.join(paragraph))}</p>")
            paragraph.clear()

    def flush_list() -> None:
        if list_items:
            blocks.append("<ul>" + "".join(f"<li>{_inline(item)}</li>" for item in list_items) + "</ul>")
            list_items.clear()

    for line in markdown.splitlines():
        if line.startswith("```"):
            flush_paragraph()
            flush_list()
            if in_code:
                blocks.append("<pre><code>" + html.escape("\n".join(code_lines)) + "</code></pre>")
                code_lines.clear()
            in_code = not in_code
            continue
        if in_code:
            code_lines.append(line)
            continue
        heading = re.fullmatch(r"(#{1,3})\s+(.+?)\s*", line)
        if heading:
            flush_paragraph()
            flush_list()
            level = len(heading.group(1))
            text = heading.group(2)
            identifier = _anchor(text)
            blocks.append(f"<h{level} id=\"{identifier}\">{_inline(text)}</h{level}>")
            continue
        bullet = re.fullmatch(r"[-*]\s+(.+)", line)
        if bullet:
            flush_paragraph()
            list_items.append(bullet.group(1))
            continue
        if not line.strip():
            flush_paragraph()
            flush_list()
            continue
        flush_list()
        paragraph.append(line.strip())
    if in_code:
        raise CatalogError("unterminated Markdown code fence")
    flush_paragraph()
    flush_list()
    return "\n".join(blocks)


def _anchor(text: str) -> str:
    plain = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return plain or "section"


def _inline(text: str) -> str:
    escaped = html.escape(text, quote=False)
    pattern = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")

    def link(match: re.Match[str]) -> str:
        target = html.unescape(match.group(2).strip())
        safe = _safe_url(target)
        label = match.group(1)
        if safe is None:
            return html.escape(label, quote=False)
        return f'<a href="{html.escape(safe, quote=True)}">{label}</a>'

    rendered = pattern.sub(link, escaped)
    rendered = re.sub(r"`([^`\n]+)`", r"<code>\1</code>", rendered)
    return re.sub(r"\*([^*\n]+)\*", r"<em>\1</em>", rendered)


def _source_link(revision: str, source: SourceDeclaration) -> str:
    return (
        "https://github.com/PerAlexandersson/RealRooted/blob/"
        f"{revision}/{source.source_path}#L{source.source_line}"
    )


def _relative_url(target: str, current_url: str) -> str:
    if not target.startswith(BASE_PATH) or not current_url.startswith(BASE_PATH):
        raise CatalogError("generator received a URL outside its base path")
    current_relative = current_url.removeprefix(BASE_PATH).strip("/")
    target_relative = target.removeprefix(BASE_PATH).strip("/")
    current_directory = pathlib.PurePosixPath(current_relative).parts if current_relative else ()
    target_parts = pathlib.PurePosixPath(target_relative).parts if target_relative else ()
    common = 0
    while common < min(len(current_directory), len(target_parts)) and (
        current_directory[common] == target_parts[common]
    ):
        common += 1
    upwards = [".."] * (len(current_directory) - common)
    remainder = list(target_parts[common:])
    relative = "/".join(upwards + remainder)
    if target.endswith("/"):
        return f"{relative}/" if relative else "./"
    return relative


def _template(repo_root: pathlib.Path, body: str, title: str, current_url: str) -> str:
    template_path = repo_root / "website" / "templates" / "page.html"
    template = template_path.read_text(encoding="utf-8")
    home = _relative_url(BASE_PATH, current_url)
    stylesheet = _relative_url(f"{BASE_PATH}assets/site.css", current_url)
    return template.replace("{{ title }}", html.escape(title)).replace("{{ body }}", body).replace(
        "{{ home }}", home
    ).replace("{{ stylesheet }}", stylesheet)


def _item_list(
    items: Iterable[CatalogItem], resolved: dict[str, SourceDeclaration], revision: str
) -> str:
    rows: list[str] = []
    for item in items:
        source = resolved[item.name]
        rows.append(
            "<li><code>"
            + html.escape(item.name)
            + "</code> <a class=\"source\" href=\""
            + html.escape(_source_link(revision, source), quote=True)
            + "\">source</a></li>"
        )
    return "<ul class=\"declarations\">" + "".join(rows) + "</ul>"


class _HrefCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "a":
            self.hrefs.extend(value for name, value in attrs if name == "href" and value is not None)


def validate_internal_links(files: dict[str, str]) -> None:
    """Reject generated links that cannot resolve under the project-site base path."""
    known = set(files)
    for source_name, document in files.items():
        collector = _HrefCollector()
        collector.feed(document)
        source_directory = pathlib.PurePosixPath(source_name).parent
        for href in collector.hrefs:
            parsed = urlsplit(href)
            if parsed.scheme or parsed.netloc or href.startswith("#"):
                continue
            if href.startswith("/"):
                if not href.startswith(BASE_PATH):
                    raise CatalogError(f"{source_name}: link escapes {BASE_PATH}: {href}")
                target_path = href[len(BASE_PATH) :].split("#", 1)[0]
                target = target_path
            else:
                target_path = href.split("#", 1)[0]
                target = posixpath.normpath((source_directory / target_path).as_posix())
            if target in {"", "."}:
                target = "index.html"
            elif target_path.endswith("/"):
                target = target.rstrip("/") + "/index.html"
            if target not in known:
                raise CatalogError(f"{source_name}: broken internal link {href}")


def render_site(
    repo_root: pathlib.Path,
    pages: tuple[CatalogPage, ...],
    resolved: dict[str, SourceDeclaration],
    revision: str,
) -> dict[str, str]:
    """Render deterministic generated files keyed by their output-relative path."""
    files: dict[str, str] = {}
    grouped = {section: [page for page in pages if page.section == section] for section in SECTIONS}
    index_rows = "".join(
        f"<li><a href=\"{page.section}/{page.slug}/\">{html.escape(page.title)}</a>"
        f" <span>{html.escape(page.section)}</span></li>"
        for page in pages
    )
    index_body = (
        "<main><h1>RealRooted catalogue</h1><p>Curated checked definitions and results. "
        "Each declaration links to the exact source revision used to build this page.</p>"
        f"<ul class=\"catalogue-index\">{index_rows}</ul></main>"
    )
    files["index.html"] = _template(repo_root, index_body, "RealRooted catalogue", BASE_PATH)
    for section, section_pages in grouped.items():
        links = "".join(
            f"<li><a href=\"{page.slug}/\">{html.escape(page.title)}</a></li>" for page in section_pages
        )
        body = f"<main><h1>{html.escape(section.title())}</h1><ul>{links}</ul></main>"
        section_url = f"{BASE_PATH}{section}/"
        files[f"{section}/index.html"] = _template(repo_root, body, section.title(), section_url)
    for page in pages:
        definition_html = _item_list(page.definitions, resolved, revision) if page.definitions else ""
        theorem_html = _item_list(page.theorems, resolved, revision) if page.theorems else ""
        selected = ""
        if definition_html:
            selected += "<section><h2>Definitions in Lean</h2>" + definition_html + "</section>"
        if theorem_html:
            selected += "<section><h2>Theorems in Lean</h2>" + theorem_html + "</section>"
        source = html.escape(_source_link(revision, SourceDeclaration("", "", page.source_path, 1)), quote=True)
        body = (
            "<main><p class=\"breadcrumb\"><a href=\"../\">"
            + html.escape(page.section.title())
            + "</a></p>"
            + render_markdown(page.content)
            + selected
            + f"<p class=\"verification\">Source revision <code>{html.escape(revision)}</code>; "
            + f"<a href=\"{source}\">challenge module</a>.</p></main>"
        )
        files[f"{page.section}/{page.slug}/index.html"] = _template(
            repo_root, body, page.title, page.url
        )
    manifest = {
        "schema_version": 1,
        "revision": revision,
        "catalog_digest": catalog_digest(pages),
        "pages": [
            {
                "title": page.title,
                "url": page.url,
                "source_path": page.source_path,
                "definitions": [item.name for item in page.definitions],
                "theorems": [item.name for item in page.theorems],
            }
            for page in pages
        ],
    }
    files["catalogue-manifest.json"] = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    asset = repo_root / "website" / "assets" / "site.css"
    files["assets/site.css"] = asset.read_text(encoding="utf-8")
    validate_internal_links(files)
    return files


def write_site(output: pathlib.Path, files: dict[str, str]) -> None:
    for relative, content in files.items():
        path = output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
