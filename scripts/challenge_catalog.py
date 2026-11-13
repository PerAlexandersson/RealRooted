#!/usr/bin/env python3
"""Parse and render the curated RealRooted challenge catalog.

This module deliberately implements a small, conservative subset of Lean
source syntax.  It is a catalog source guard, not a Lean parser: an
ambiguous selected declaration is an error and is left for the Lean audit to
resolve.  The companion audit verifies selected constants in Lean's
environment after a successful build.
"""

from __future__ import annotations

import functools
import hashlib
import html
import json
import pathlib
import posixpath
import re
import subprocess
import tomllib
import unicodedata
from datetime import date
from dataclasses import dataclass
from html.parser import HTMLParser
from typing import Any, Iterable
from urllib.parse import urlsplit


BASE_PATH = "/RealRooted/"
SITE_ORIGIN = "https://peralexandersson.github.io"
SYMCAT_ORIGIN = "https://www.symmetricfunctions.com/"
# Lean identifier characters (Lean's `isLetterLike` and `isSubScriptAlnum`), so
# names such as `embedComplₗ` or `forall₂_le` are not truncated to an ASCII prefix.
_LEAN_LETTER = (
    "A-Za-z_"
    "\u03b1-\u03ba\u03bc-\u03c9"  # Greek lowercase except λ
    "\u0391-\u039f\u03a1\u03a4-\u03a9"  # Greek uppercase except Π, Σ
    "\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
)
_LEAN_SUBSCRIPT = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
ID_START = f"[{_LEAN_LETTER}]"
ID_REST = f"[{_LEAN_LETTER}0-9'!?{_LEAN_SUBSCRIPT}]"
ID_REST_DOT = f"[{_LEAN_LETTER}0-9'!?.{_LEAN_SUBSCRIPT}]"
SECTIONS = ("concepts", "families", "theorems")
TOPICS = {
    "Interlacing": "Interlacing",
    "Roots": "Roots",
    "Preservers": "Preservers",
    "PolyaFrequency": "Pólya frequency",
    "Stability": "Stability",
    "Matrices": "Matrices",
    "Orthogonal": "Orthogonal",
    "Graphs": "Graphs",
    "Combinatorial": "Combinatorial",
}
PROVENANCE_TAGS = {
    "coauthored-paper": (
        "Coauthored paper",
        "Result from a paper coauthored by Per Alexandersson",
    ),
    "realrooted-original": (
        "RealRooted original",
        "Result first developed in RealRooted and not currently attached to a paper",
    ),
}
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
NAME_RE = re.compile(f"{ID_START}{ID_REST_DOT}*(?:\\.{ID_START}{ID_REST_DOT}*)+")
SLUG_RE = re.compile(r"[a-z0-9]+(?:-[a-z0-9]+)*")
MODULE_RE = re.compile(f"{ID_START}{ID_REST_DOT}*(?:\\.{ID_START}{ID_REST_DOT}*)*")
METADATA_RE = re.compile(r"<!--\s*realrooted-catalog\s*\n(.*?)-->", re.DOTALL)
CONTENT_RE = re.compile(
    r"<!--\s*realrooted-catalog-content\s*-->\s*\n?(.*?)"
    r"<!--\s*/realrooted-catalog-content\s*-->",
    re.DOTALL,
)
DECLARATION_RE = re.compile(
    r"^\s*(?P<attributes>(?:@\[[^\n]*\]\s*)*)"
    r"(?P<modifiers>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|irreducible_def|abbrev|structure|inductive|class|opaque|instance)\s+"
    f"(?P<name>{ID_START}{ID_REST_DOT}*)(?!{ID_REST_DOT})"
)
NAMESPACE_RE = re.compile(f"^\\s*namespace\\s+({ID_START}{ID_REST_DOT}*)\\s*$")
END_NAMESPACE_RE = re.compile(f"^\\s*end\\s+({ID_START}{ID_REST_DOT}*)\\s*$")
IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$"
)
FORWARDING_ABBREV_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?abbrev\b[\s\S]*?:=\s*"
    r"(?:_root_\.)?[A-Za-z_][A-Za-z0-9_'.]*"
    r"(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*\s*$"
)
CITATION_GROUP_RE = re.compile(
    r"\[((?:\s*@[^\];,\s]+(?:\s*,\s*[^;\]\n]+)?\s*)"
    r"(?:;\s*@[^\];,\s]+(?:\s*,\s*[^;\]\n]+)?\s*)*)\]"
)
SF_TARGET_RE = re.compile(r"(?:\]\(\s*|\]:\s*)sf:([^)\s]+)")


class CatalogError(ValueError):
    """A deterministic catalog source or audit validation error."""


@dataclass(frozen=True)
class Citation:
    key: str
    at: str | None = None


@dataclass(frozen=True)
class CatalogItem:
    name: str
    expected_kind: str
    module: str | None
    label: str | None = None
    headline: bool = False
    symcat: str | None = None
    tags: tuple[str, ...] | None = None
    objects: tuple[str, ...] = ()
    object_property: str | None = None

    @property
    def anchor(self) -> str:
        """The fragment identifying this declaration on its catalog page."""
        return "decl-" + re.sub(r"[^A-Za-z0-9_-]+", "-", self.name).strip("-")


@dataclass(frozen=True)
class CatalogPage:
    source_path: str
    section: str
    slug: str
    authors: tuple[str, ...]
    years: tuple[int, ...]
    formalized: str
    tags: tuple[str, ...]
    references: tuple[Citation, ...]
    definitions: tuple[CatalogItem, ...]
    theorems: tuple[CatalogItem, ...]
    content: str
    title: str
    kind: str | None = None
    conjecture: str | None = None
    symcat: tuple[str, ...] = ()
    objects: tuple[str, ...] = ()
    object_property: str | None = None

    @property
    def topic(self) -> str:
        parts = pathlib.PurePosixPath(self.source_path).parts
        # Root-level entry points predate the topical directory layout.
        directory = parts[2] if len(parts) > 3 else "Combinatorial"
        if directory not in TOPICS:
            raise _source_error(self.source_path, f"unknown topic directory {directory}")
        return TOPICS[directory]

    @property
    def symcat_labels(self) -> tuple[str, ...]:
        return tuple(dict.fromkeys(
            self.symcat + tuple(item.symcat for item in self.items if item.symcat)
            + extract_sf_labels(self.content)
        ))

    @property
    def items(self) -> tuple[CatalogItem, ...]:
        return self.definitions + self.theorems

    @property
    def url(self) -> str:
        return f"{BASE_PATH}{self.section}/{self.slug}/"

    @property
    def citations(self) -> tuple[Citation, ...]:
        """All listed and inline citations, in stable first-occurrence order."""
        result: list[Citation] = []
        seen: set[str] = set()
        for citation in self.references + extract_citations(self.content):
            if citation.key not in seen:
                seen.add(citation.key)
                result.append(citation)
        return tuple(result)


@dataclass(frozen=True)
class SourceDeclaration:
    name: str
    actual_kind: str
    source_path: str
    source_line: int
    deprecated: bool = False
    source_code: str = ""


@dataclass(frozen=True)
class AuthorProfile:
    """A curated display name and optional external link for an attribution key."""

    display_name: str
    url: str | None = None


@dataclass(frozen=True)
class AuthorIndexEntry:
    """One credited person and the catalog pages that credit that person."""

    identity: str
    display_name: str
    url: str | None
    pages: tuple[CatalogPage, ...]

    @property
    def anchor(self) -> str:
        # Fold accents so that, for example, "Brändén" gives "branden".
        folded = unicodedata.normalize("NFKD", self.identity)
        return "author-" + _anchor("".join(ch for ch in folded if not unicodedata.combining(ch)))


@functools.lru_cache(maxsize=None)
def strip_comments_and_strings(text: str) -> str:
    """Replace comments and strings by whitespace without moving source lines.

    Validation strips the same imported modules many times, so results are
    cached by source text.
    """
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


OBJECT_PROPERTIES = {
    "real-rooted": "Real-rooted",
    "interlacing": "Interlacing",
    "pf": "PF (Pólya frequency)",
    "real-stable": "Real stable",
    "gamma-positive": "γ-positive",
    "log-concave": "Log-concave",
    "unimodal": "Unimodal",
    "totally-nonnegative": "Totally nonnegative",
    "orthogonal": "Orthogonal",
}


def _read_objects(path: str, record: dict[str, Any]) -> tuple[tuple[str, ...], str | None]:
    objects = record.get("objects", [])
    if not isinstance(objects, list) or not all(
        isinstance(name, str) and name.strip() == name and name
        and not any(ch in name for ch in "\n\r\t") for name in objects
    ):
        raise _source_error(path, "objects must be an array of nonempty single-line strings")
    if len({name.casefold() for name in objects}) != len(objects):
        raise _source_error(path, "objects must not contain duplicates (ignoring case)")
    property_name = record.get("property")
    if "property" in record and (
        not isinstance(property_name, str) or property_name not in OBJECT_PROPERTIES
    ):
        raise _source_error(path, "unknown object property; expected " + ", ".join(OBJECT_PROPERTIES))
    if property_name and not objects:
        raise _source_error(path, "property requires nonempty objects")
    return tuple(objects), property_name


def _read_items(path: str, raw: Any, expected_kind: str) -> tuple[CatalogItem, ...]:
    if raw is None:
        return ()
    if not isinstance(raw, list) or not raw:
        raise _source_error(path, f"{expected_kind}s must be a nonempty array of tables")
    result: list[CatalogItem] = []
    seen: set[str] = set()
    for index, record in enumerate(raw, start=1):
        if not isinstance(record, dict) or set(record) - {
            "name", "module", "label", "headline", "symcat", "tags", "objects", "property"
        }:
            raise _source_error(path, f"invalid {expected_kind} record {index}")
        name = record.get("name")
        module = record.get("module")
        label = record.get("label")
        headline = record.get("headline", False)
        symcat = record.get("symcat")
        tags = (
            _read_tags(path, record["tags"], f"{expected_kind} record {index}")
            if "tags" in record
            else None
        )
        objects, property_name = _read_objects(path, record)
        if objects and expected_kind != "theorem":
            raise _source_error(path, "objects must select a theorem, not a definition")
        if label is not None and (
            not isinstance(label, str) or not label.strip() or label.strip() != label or "\n" in label
        ):
            raise _source_error(path, f"{expected_kind} record {index} has an invalid label")
        if not isinstance(headline, bool):
            raise _source_error(path, f"{expected_kind} record {index}: headline must be a boolean")
        if headline and expected_kind != "theorem":
            raise _source_error(path, f"{expected_kind} record {index}: only theorems can be headlines")
        if headline and label is None:
            raise _source_error(path, f"{expected_kind} record {index}: a headline needs a label")
        if symcat is not None and (
            not isinstance(symcat, str)
            or not symcat
            or symcat.strip() != symcat
            or any(character.isspace() for character in symcat)
        ):
            raise _source_error(path, f"{expected_kind} record {index} has an invalid symcat label")
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
        result.append(CatalogItem(name, expected_kind, module, label, headline, symcat, tags,
                                  objects, property_name))
    return tuple(result)


def _read_tags(path: str, raw: Any, context: str = "metadata") -> tuple[str, ...]:
    if raw is None:
        return ()
    if not isinstance(raw, list) or not all(isinstance(tag, str) for tag in raw):
        raise _source_error(path, f"{context}: tags must be an array of strings")
    if len(set(raw)) != len(raw):
        raise _source_error(path, f"{context}: tags must not contain duplicates")
    unknown = set(raw) - set(PROVENANCE_TAGS)
    if unknown:
        raise _source_error(path, f"{context}: unknown tags: {', '.join(sorted(unknown))}")
    return tuple(raw)


def extract_citations(content: str) -> tuple[Citation, ...]:
    """Extract the supported Pandoc-style citation groups from catalog Markdown."""
    citations: list[Citation] = []
    for group in CITATION_GROUP_RE.finditer(content):
        for raw in group.group(1).split(";"):
            key_and_at = raw.strip().removeprefix("@").split(",", 1)
            key = key_and_at[0].strip()
            at = key_and_at[1].strip() if len(key_and_at) == 2 else None
            citations.append(Citation(key, at or None))
    return tuple(citations)


def extract_sf_labels(content: str) -> tuple[str, ...]:
    """Return labels used as ``sf:`` Markdown link targets."""
    return tuple(match.group(1) for match in SF_TARGET_RE.finditer(content))


def _read_references(path: str, raw: Any) -> tuple[Citation, ...]:
    if raw is None:
        return ()
    if not isinstance(raw, list):
        raise _source_error(path, "references must be an array")
    result: list[Citation] = []
    seen: set[str] = set()
    for index, item in enumerate(raw, start=1):
        if isinstance(item, str):
            key, at = item, None
        elif isinstance(item, dict) and set(item) <= {"key", "at"}:
            key, at = item.get("key"), item.get("at")
        else:
            raise _source_error(path, f"invalid reference record {index}")
        if not isinstance(key, str) or not key or key.strip() != key or any(
            character.isspace() for character in key
        ):
            raise _source_error(path, f"reference record {index} has an invalid key")
        if at is not None and (
            not isinstance(at, str) or not at or at.strip() != at or "\n" in at
        ):
            raise _source_error(path, f"reference record {index} has an invalid locator")
        if key in seen:
            raise _source_error(path, f"duplicate reference key {key}")
        seen.add(key)
        result.append(Citation(key, at))
    return tuple(result)


def _published_title(path: str, content: str, has_reference_keys: bool = False) -> str:
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
    reference_end = next(
        (
            index
            for index, line in enumerate(lines[reference_at + 1 :], start=reference_at + 1)
            if re.fullmatch(r"#{1,2}\s+.+", line)
        ),
        len(lines),
    )
    if not has_reference_keys and not any(
        line.strip() for line in lines[reference_at + 1 : reference_end]
    ):
        raise _source_error(path, "References must not be empty")
    return headings[0]


def _read_attribution(
    path: str, metadata: dict[str, Any]
) -> tuple[tuple[str, ...], tuple[int, ...]]:
    raw_authors = metadata.get("authors", [])
    if not isinstance(raw_authors, list) or not all(
        isinstance(author, str) and author.strip() == author and author for author in raw_authors
    ):
        raise _source_error(path, "authors must be an array of nonempty names")
    if len(set(raw_authors)) != len(raw_authors):
        raise _source_error(path, "authors must not contain duplicates")

    raw_years = metadata.get("years", [])
    if not isinstance(raw_years, list) or not all(
        isinstance(year, int) and not isinstance(year, bool) and 1000 <= year <= 2999
        for year in raw_years
    ):
        raise _source_error(path, "years must be an array of four-digit years")
    if raw_years != sorted(set(raw_years)):
        raise _source_error(path, "years must be strictly increasing")
    return tuple(raw_authors), tuple(raw_years)


def _read_formalized(
    path: str, metadata: dict[str, Any], commit_date: date | None
) -> str:
    """Read the required, revision-bounded catalog formalization date."""
    value = metadata.get("formalized")
    if value is None:
        raise _source_error(
            path,
            'metadata requires formalized = "YYYY-MM-DD"; use the date the selected result was added',
        )
    if not isinstance(value, str) or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", value):
        raise _source_error(path, 'formalized must be an ISO date written as "YYYY-MM-DD"')
    try:
        parsed = date.fromisoformat(value)
    except ValueError as error:
        raise _source_error(path, 'formalized must be a valid ISO date written as "YYYY-MM-DD"') from error
    if commit_date is not None and parsed > commit_date:
        raise _source_error(path, f"formalized {value} is after this revision's commit date {commit_date}")
    return value


def parse_challenge_source(
    source_path: str, text: str, commit_date: date | None = None
) -> CatalogPage | None:
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
            raise _source_error(source_path, "catalog markers must occur in a module doc comment")
        return None
    if len(metadata_matches) != 1 or len(content_matches) != 1:
        raise _source_error(source_path, "requires exactly one metadata and one content block")
    metadata_comment, metadata_match = metadata_matches[0]
    content_comment, content_match = content_matches[0]
    if metadata_comment != content_comment or marker_count != 3:
        raise _source_error(source_path, "catalog blocks must occur together in one module doc comment")
    try:
        metadata = tomllib.loads(metadata_match.group(1))
    except tomllib.TOMLDecodeError as error:
        raise _source_error(source_path, f"invalid TOML metadata: {error}") from error
    if not isinstance(metadata, dict):
        raise _source_error(source_path, "metadata must be a TOML table")
    allowed = {
        "version",
        "section",
        "slug",
        "authors",
        "years",
        "formalized",
        "tags",
        "references",
        "symcat",
        "objects",
        "property",
        "kind",
        "conjecture",
        "definitions",
        "theorems",
    }
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
    authors, years = _read_attribution(source_path, metadata)
    formalized = _read_formalized(source_path, metadata, commit_date)
    tags = _read_tags(source_path, metadata.get("tags"))
    references = _read_references(source_path, metadata.get("references"))
    symcat = metadata.get("symcat", [])
    if isinstance(symcat, str):
        symcat = [symcat]
    if not isinstance(symcat, list) or not all(
        isinstance(label, str) and label and not any(ch.isspace() for ch in label)
        for label in symcat
    ) or len(set(symcat)) != len(symcat):
        raise _source_error(source_path, "symcat must be a label or an array of unique labels")
    definitions = _read_items(source_path, metadata.get("definitions"), "definition")
    theorems = _read_items(source_path, metadata.get("theorems"), "theorem")
    objects, property_name = _read_objects(source_path, metadata)
    if objects and not theorems:
        raise _source_error(source_path, "page objects require a selected theorem")
    if not definitions and not theorems:
        raise _source_error(source_path, "requires at least one definition or theorem")
    content = content_match.group(1).strip()
    kind = metadata.get("kind")
    conjecture = metadata.get("conjecture")
    if kind is not None and kind != "sequence":
        raise _source_error(source_path, "kind must be sequence when specified")
    if conjecture is not None and (not isinstance(conjecture, str) or not conjecture.strip()):
        raise _source_error(source_path, "conjecture must be a nonempty locator")
    if kind == "sequence" and not conjecture:
        raise _source_error(source_path, "sequence pages require a conjecture locator")
    return CatalogPage(
        kind=kind,
        conjecture=conjecture,
        symcat=tuple(symcat),
        objects=objects,
        object_property=property_name,
        source_path=source_path,
        section=section,
        slug=slug,
        authors=authors,
        years=years,
        formalized=formalized,
        tags=tags,
        references=references,
        definitions=definitions,
        theorems=theorems,
        content=content,
        title=_published_title(
            source_path, content, bool(references or extract_citations(content))
        ),
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


def _commit_date_at(repo_root: pathlib.Path) -> date | None:
    """Return the current revision's calendar date when Git is available."""
    try:
        result = subprocess.run(
            ["git", "show", "-s", "--format=%cs", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            check=True,
            text=True,
        )
        return date.fromisoformat(result.stdout.strip())
    except (OSError, subprocess.CalledProcessError, ValueError):
        return None


def load_catalog(repo_root: pathlib.Path) -> tuple[CatalogPage, ...]:
    """Load and validate every opted-in tracked challenge module."""
    pages: list[CatalogPage] = []
    commit_date = _commit_date_at(repo_root)
    for path in _tracked_challenge_paths(repo_root):
        page = parse_challenge_source(
            path.relative_to(repo_root).as_posix(), path.read_text(encoding="utf-8"), commit_date
        )
        if page is not None:
            pages.append(page)
    paths: set[str] = set()
    for page in pages:
        if page.url in paths:
            raise CatalogError(f"duplicate catalog URL {page.url}")
        paths.add(page.url)
    return tuple(sorted(pages, key=lambda page: (SECTIONS.index(page.section), page.title, page.slug)))


def _read_author_profile(path: str, key: str, raw: Any) -> AuthorProfile:
    """Validate one record from the small hand-curated author directory."""
    if not isinstance(raw, dict) or set(raw) - {"name", "url"}:
        raise _source_error(path, f"author record {key!r} must contain only name and url")
    name = raw.get("name")
    if not isinstance(name, str) or not name or name.strip() != name or "\n" in name:
        raise _source_error(path, f"author record {key!r} needs a nonempty display name")
    url = raw.get("url")
    if url is not None:
        parsed = urlsplit(url) if isinstance(url, str) else None
        if (
            not isinstance(url, str)
            or url.strip() != url
            or parsed is None
            or parsed.scheme.lower() not in {"http", "https"}
            or not parsed.netloc
        ):
            raise _source_error(path, f"author record {key!r} has an invalid URL")
    return AuthorProfile(name, url)


def load_author_profiles(
    repo_root: pathlib.Path,
) -> tuple[dict[str, AuthorProfile], dict[tuple[str, str], AuthorProfile]]:
    """Load optional global and per-page author names from ``website/authors.toml``.

    Global entries live in ``[authors]``.  Per-page entries live in
    ``[overrides]`` and use ``"page-slug:author key"`` as their key, so a
    compact surname can name different people on different catalog pages.
    """
    path = repo_root / "website" / "authors.toml"
    if not path.is_file():
        return {}, {}
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise CatalogError(f"invalid author directory {path}: {error}") from error
    if not isinstance(data, dict) or set(data) - {"authors", "overrides"}:
        raise CatalogError(f"{path}: author directory only permits [authors] and [overrides]")
    global_raw = data.get("authors", {})
    override_raw = data.get("overrides", {})
    if not isinstance(global_raw, dict) or not isinstance(override_raw, dict):
        raise CatalogError(f"{path}: [authors] and [overrides] must be tables")
    global_profiles: dict[str, AuthorProfile] = {}
    for key, raw in global_raw.items():
        if not isinstance(key, str) or not key or key.strip() != key:
            raise CatalogError(f"{path}: author keys must be nonempty strings")
        global_profiles[key] = _read_author_profile(path.as_posix(), key, raw)
    overrides: dict[tuple[str, str], AuthorProfile] = {}
    for qualified_key, raw in override_raw.items():
        if not isinstance(qualified_key, str):
            raise CatalogError(f"{path}: override keys must be strings")
        slug, separator, key = qualified_key.partition(":")
        if not separator or not SLUG_RE.fullmatch(slug) or not key or key.strip() != key:
            raise CatalogError(
                f"{path}: override key {qualified_key!r} must be 'page-slug:author key'"
            )
        overrides[(slug, key)] = _read_author_profile(path.as_posix(), qualified_key, raw)
    return global_profiles, overrides


def _surname_sort_key(display_name: str) -> str:
    """Use the final word of a display name, or its compact key, as a surname."""
    words = re.findall(r"[^\W_]+", display_name, flags=re.UNICODE)
    return (words[-1] if words else display_name).casefold()


def build_author_index(
    pages: Iterable[CatalogPage],
    profiles: tuple[dict[str, AuthorProfile], dict[tuple[str, str], AuthorProfile]],
) -> tuple[AuthorIndexEntry, ...]:
    """Group catalog attributions by the person they resolve to.

    A resolved name (global or page-scoped) identifies one person, so several
    surname keys and overrides that resolve to the same name and URL share one
    entry.  An unresolved key stays its own entry.
    """
    global_profiles, overrides = profiles
    grouped: dict[str, tuple[AuthorProfile, list[CatalogPage]]] = {}
    for page in pages:
        for key in page.authors:
            resolved = overrides.get((page.slug, key)) or global_profiles.get(key)
            profile = resolved or AuthorProfile(key)
            identity = profile.display_name if resolved is not None else key
            if identity in grouped and grouped[identity][0] != profile:
                raise CatalogError(
                    f"author {identity!r} resolves to conflicting profiles; "
                    "give each person one name and URL in website/authors.toml"
                )
            if identity not in grouped:
                grouped[identity] = (profile, [])
            grouped[identity][1].append(page)
    entries = [
        AuthorIndexEntry(
            identity,
            profile.display_name,
            profile.url,
            tuple(sorted(credited_pages, key=lambda page: (page.title.casefold(), page.slug))),
        )
        for identity, (profile, credited_pages) in grouped.items()
    ]
    return tuple(
        sorted(entries, key=lambda entry: (_surname_sort_key(entry.display_name), entry.display_name.casefold(), entry.identity))
    )


def canonical_catalog_data(pages: Iterable[CatalogPage]) -> dict[str, Any]:
    """The frozen, prose-independent selected-declaration digest input."""
    return {
        "schema_version": 1,
        "pages": [
            {
                "source_path": page.source_path,
                "section": page.section,
                "slug": page.slug,
                "formalized": page.formalized,
                "definitions": [item.name for item in page.definitions],
                "theorems": [item.name for item in page.theorems],
            }
            for page in sorted(pages, key=lambda page: page.source_path)
        ],
    }


def catalog_digest(pages: Iterable[CatalogPage]) -> str:
    payload = json.dumps(
        canonical_catalog_data(pages), sort_keys=True, separators=(",", ":"), ensure_ascii=True
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
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    prefix = ".".join(namespace)
    if not prefix or name.startswith("RealRooted.") or name.startswith(prefix + "."):
        return name
    return f"{prefix}.{name}"


def _declaration_source_code(
    source_path: pathlib.Path, source_line: int, actual_kind: str
) -> str:
    """Extract a definition body or theorem statement from its owning Lean source."""
    original = source_path.read_text(encoding="utf-8")
    clean = strip_comments_and_strings(original)
    original_lines = original.splitlines(keepends=True)
    clean_lines = clean.splitlines(keepends=True)
    start = source_line - 1

    if actual_kind == "theorem":
        original_tail = "".join(original_lines[start:])
        clean_tail = "".join(clean_lines[start:])
        depth = 0
        line_start = 0
        for index, character in enumerate(clean_tail[:-1]):
            if character == "\n":
                line_start = index + 1
            elif character in "([{":
                depth += 1
            elif character in ")]}":
                depth -= 1
            elif depth == 0 and (
                (character == ":" and clean_tail[index + 1] == "=")
                # Equation-style proofs (`| 0 => ...`) start their first
                # alternative on a fresh line instead of using `:=`.
                or (
                    character == "|"
                    and clean_tail[index + 1].isspace()
                    and not clean_tail[line_start:index].strip()
                )
            ):
                return original_tail[:index].rstrip()
        relative = source_path.as_posix()
        raise CatalogError(f"{relative}:{source_line}: cannot isolate theorem statement")

    end = len(original_lines)
    for index in range(start + 1, len(original_lines)):
        clean_line = clean_lines[index]
        original_line = original_lines[index]
        if original_line.startswith(("/--", "/-!", "@[")):
            end = index
            break
        if clean_line and not clean_line[0].isspace() and (
            DECLARATION_RE.match(clean_line)
            or clean_line.startswith(("namespace ", "end ", "section "))
            or clean_line.startswith(("noncomputable section", "open ", "variable "))
        ):
            end = index
            break
    source_code = "".join(original_lines[start:end]).rstrip()
    if not source_code:
        relative = source_path.as_posix()
        raise CatalogError(f"{relative}:{source_line}: empty declaration source")
    return source_code


def _attribute_tail(line: str, depth: int) -> tuple[int, str]:
    """Track `@[...]` attribute brackets and return any text following them.

    `depth` is the bracket depth carried over from earlier lines.  The result is
    the new depth and the stripped remainder after the last closed attribute
    list (empty while the attribute list is still open).
    """
    index = 0
    while index < len(line):
        character = line[index]
        if depth:
            depth += {"[": 1, "]": -1}.get(character, 0)
            index += 1
        elif character.isspace():
            index += 1
        elif line.startswith("@[", index):
            depth = 1
            index += 2
        else:
            return 0, line[index:].strip()
    return depth, ""


def source_declarations(repo_root: pathlib.Path, source_path: pathlib.Path) -> dict[str, SourceDeclaration]:
    """Find ordinary public declaration headers in one Lean source file."""
    relative_path = source_path.relative_to(repo_root).as_posix()
    clean = strip_comments_and_strings(source_path.read_text(encoding="utf-8"))
    namespaces: list[str] = []
    found: dict[str, SourceDeclaration] = {}
    pending_deprecated = False
    attribute_depth = 0
    for line_number, line in enumerate(clean.splitlines(), start=1):
        namespace_match = NAMESPACE_RE.match(line)
        if namespace_match:
            pending_deprecated = False
            attribute_depth = 0
            namespaces.extend(namespace_match.group(1).split("."))
            continue
        end_match = END_NAMESPACE_RE.match(line)
        if end_match:
            pending_deprecated = False
            attribute_depth = 0
            ending = end_match.group(1).split(".")
            if namespaces[-len(ending) :] == ending:
                del namespaces[-len(ending) :]
            continue
        declaration_match = DECLARATION_RE.match(line)
        stripped = line.strip()
        if not declaration_match:
            if attribute_depth or stripped.startswith("@["):
                pending_deprecated = pending_deprecated or "deprecated" in stripped
                attribute_depth, tail = _attribute_tail(line, attribute_depth)
                if tail:
                    # The attributes already applied to a declaration on this
                    # line, such as a one-line `@[deprecated] alias old := new`.
                    pending_deprecated = False
            elif stripped:
                pending_deprecated = False
            continue
        modifiers = declaration_match.group("modifiers").split()
        attributes = declaration_match.group("attributes")
        deprecated = pending_deprecated or "deprecated" in attributes
        pending_deprecated = False
        attribute_depth = 0
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
        source_code = _declaration_source_code(source_path, line_number, actual_kind)
        found[name] = SourceDeclaration(
            name, actual_kind, relative_path, line_number, deprecated, source_code
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
    if item.expected_kind == "definition" and FORWARDING_ABBREV_RE.fullmatch(
        strip_comments_and_strings(declaration.source_code)
    ):
        raise CatalogError(
            f"{page.source_path}: {item.name} is only a forwarding abbreviation; "
            "select its full definition instead"
        )
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
        raise CatalogError("audit report catalog digest does not match the selected declarations")
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


def load_symcat_snapshots(
    repo_root: pathlib.Path,
) -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    """Load and validate the committed symmetricfunctions.com snapshots."""
    directory = repo_root / "website" / "symcat"
    labels_path = directory / "labels.json"
    bibliography_path = directory / "bibliography.json"
    try:
        labels = json.loads(labels_path.read_text(encoding="utf-8"))
        bibliography = json.loads(bibliography_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CatalogError(f"cannot load SymCat snapshots: {error}") from error
    if not isinstance(labels, dict) or not all(
        isinstance(label, str)
        and label
        and isinstance(href, str)
        and href
        and not urlsplit(href).scheme
        and not urlsplit(href).netloc
        and not href.startswith("/")
        for label, href in labels.items()
    ):
        raise CatalogError(f"{labels_path}: expected a mapping of labels to relative links")
    if (
        not isinstance(bibliography, dict)
        or bibliography.get("schema_version") != 1
        or set(bibliography) != {"schema_version", "entries"}
        or not isinstance(bibliography["entries"], dict)
    ):
        raise CatalogError(f"{bibliography_path}: invalid bibliography snapshot schema")
    entries = bibliography["entries"]
    for key, entry in entries.items():
        if (
            not isinstance(key, str)
            or not isinstance(entry, dict)
            or set(entry) != {"label", "csl", "bibtex"}
            or not isinstance(entry["label"], str)
            or not entry["label"]
            or not isinstance(entry["csl"], dict)
            or not isinstance(entry["bibtex"], str)
        ):
            raise CatalogError(f"{bibliography_path}: invalid entry {key!r}")
    return labels, entries


def _safe_url(url: str) -> str | None:
    parsed = urlsplit(url)
    if parsed.scheme and parsed.scheme.lower() not in {"http", "https", "mailto"}:
        return None
    if any(character.isspace() or ord(character) < 32 for character in url):
        return None
    return url


LINK_DEFINITION_RE = re.compile(r"\s{0,3}\[([^\]]+)\]:\s*(\S+)\s*")
LIST_ITEM_RE = re.compile(r"(\s*)(?:([-*])|(\d+)\.)\s+(.+)")


def render_markdown(
    markdown: str,
    *,
    symcat_labels: dict[str, str] | None = None,
    bibliography: dict[str, dict[str, Any]] | None = None,
    base_path: str = BASE_PATH,
    generated_references: str = "",
    catalog_links: dict[str, str] | None = None,
) -> str:
    """Render the deliberate Markdown subset, escaping raw HTML by default.

    Supported: headings, paragraphs, `-`/`*` and numbered lists whose items may
    continue on indented lines, fenced code blocks (also indented inside a
    list item), inline code, `**strong**`, `*emphasis*`, inline or
    reference-style links (`[text](url)`, `[text][id]` with `[id]: url`), and
    TeX math with dollar or backslash delimiters, left untouched for KaTeX.
    A paragraph consisting of one double-dollar or bracket-delimited formula
    is rendered as display math.
    """
    lines = markdown.splitlines()
    references: dict[str, str] = {}
    body: list[str] = []
    for line in lines:
        definition = LINK_DEFINITION_RE.fullmatch(line)
        if definition:
            references[definition.group(1).casefold()] = definition.group(2)
        else:
            body.append(line)

    blocks: list[str] = []
    paragraph: list[str] = []
    list_items: list[list[str]] = []
    list_kind = ""
    code_lines: list[str] = []
    in_code = False
    code_indent = 0

    def inline(text: str) -> str:
        return _inline(text, references, symcat_labels, bibliography, base_path, catalog_links)

    def flush_paragraph() -> None:
        if paragraph:
            text = " ".join(paragraph)
            if re.fullmatch(
                r"(?:\$\$(?:(?!\$\$).)+\$\$|\\\[(?:(?!\\\[|\\\]).)+\\\])[.,;]?",
                text, re.DOTALL,
            ):
                blocks.append(f'<div class="math-display">{inline(text)}</div>')
            else:
                blocks.append(f"<p>{inline(text)}</p>")
            paragraph.clear()

    def flush_list() -> None:
        nonlocal list_kind
        if list_items:
            items = "".join(f"<li>{inline(' '.join(item))}</li>" for item in list_items)
            blocks.append(f"<{list_kind}>{items}</{list_kind}>")
            list_items.clear()
        list_kind = ""

    for line in body:
        stripped = line.strip()
        if stripped.startswith("```"):
            flush_paragraph()
            flush_list()
            if in_code:
                blocks.append("<pre><code>" + html.escape("\n".join(code_lines)) + "</code></pre>")
                code_lines.clear()
            else:
                code_indent = len(line) - len(line.lstrip())
            in_code = not in_code
            continue
        if in_code:
            code_lines.append(line[code_indent:] if line[:code_indent].strip() == "" else line)
            continue
        heading = re.fullmatch(r"(#{1,3})\s+(.+?)\s*", line)
        if heading:
            flush_paragraph()
            flush_list()
            level = len(heading.group(1))
            text = heading.group(2)
            identifier = _anchor(text)
            blocks.append(f"<h{level} id=\"{identifier}\">{inline(text)}</h{level}>")
            continue
        item = LIST_ITEM_RE.fullmatch(line)
        if item and not item.group(1):
            flush_paragraph()
            kind = "ol" if item.group(3) else "ul"
            if list_kind and kind != list_kind:
                flush_list()
            list_kind = kind
            list_items.append([item.group(4)])
            continue
        if not stripped:
            flush_paragraph()
            flush_list()
            continue
        if list_items and line[:1].isspace():
            list_items[-1].append(stripped)
            continue
        flush_list()
        paragraph.append(stripped)
    if in_code:
        raise CatalogError("unterminated Markdown code fence")
    flush_paragraph()
    flush_list()
    rendered = "\n".join(blocks)
    if generated_references:
        marker = '<h2 id="references">References</h2>'
        marker_at = rendered.find(marker)
        if marker_at == -1:
            raise CatalogError('generated references need a "## References" section')
        following = rendered.find("<h2 ", marker_at + len(marker))
        insert_at = len(rendered) if following == -1 else following
        rendered = (
            rendered[:insert_at].rstrip()
            + "\n"
            + generated_references
            + "\n"
            + rendered[insert_at:]
        )
    return rendered


def _anchor(text: str) -> str:
    plain = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    return plain or "section"


def _topic_anchor(topic: str) -> str:
    folded = unicodedata.normalize("NFKD", topic)
    return "topic-" + _anchor("".join(ch for ch in folded if not unicodedata.combining(ch)))


def _inline(
    text: str,
    references: dict[str, str] | None = None,
    symcat_labels: dict[str, str] | None = None,
    bibliography: dict[str, dict[str, Any]] | None = None,
    base_path: str = BASE_PATH,
    catalog_links: dict[str, str] | None = None,
) -> str:
    references = references or {}
    symcat_labels = symcat_labels or {}
    bibliography = bibliography or {}
    escaped = html.escape(text, quote=False)
    # protect code spans from emphasis and link rewriting
    codes: list[str] = []

    def stash(match: re.Match[str]) -> str:
        codes.append(match.group(1))
        return f"\x00{len(codes) - 1}\x00"

    rendered = re.sub(r"`([^`\n]+)`", stash, escaped)
    # protect TeX math from emphasis and link rewriting
    maths: list[str] = []

    def stash_math(match: re.Match[str]) -> str:
        maths.append(match.group(0))
        return f"\x01{len(maths) - 1}\x01"

    rendered = re.sub(
        r"\$\$.+?\$\$|\$[^$\n]+?\$|\\\[.+?\\\]|\\\(.+?\\\)",
        stash_math, rendered, flags=re.DOTALL,
    )

    def citation_group(match: re.Match[str]) -> str:
        rendered_citations: list[str] = []
        for raw in match.group(1).split(";"):
            key_and_at = raw.strip().removeprefix("@").split(",", 1)
            key = html.unescape(key_and_at[0].strip())
            at = key_and_at[1].strip() if len(key_and_at) == 2 else None
            entry = bibliography.get(key)
            if entry is None:
                return match.group(0)
            label = html.escape(entry["label"])
            suffix = f", {at}" if at else ""
            rendered_citations.append(
                f'<a class="citation" href="#ref-{html.escape(key, quote=True)}">'
                f"[{label}{suffix}]</a>"
            )
        return "; ".join(rendered_citations)

    rendered = CITATION_GROUP_RE.sub(citation_group, rendered)

    def anchor(label: str, target: str) -> str:
        raw_target = html.unescape(target.strip())
        if raw_target.startswith("sf:"):
            href = symcat_labels.get(raw_target.removeprefix("sf:"))
            raw_target = SYMCAT_ORIGIN + href if href else raw_target
        elif raw_target.startswith("rr:"):
            slug, separator, fragment = raw_target[3:].partition("#")
            if catalog_links is None or slug not in catalog_links:
                raise CatalogError(f"unknown catalog slug {slug}")
            raw_target = catalog_links[slug] + (separator + fragment if separator else "")
        elif raw_target.startswith(BASE_PATH) and base_path != BASE_PATH:
            raw_target = base_path + raw_target.removeprefix(BASE_PATH)
        safe = _safe_url(raw_target)
        if safe is None:
            return label
        return f'<a href="{html.escape(safe, quote=True)}">{label}</a>'

    rendered = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", lambda m: anchor(m.group(1), m.group(2)), rendered)

    def reference(match: re.Match[str]) -> str:
        key = (match.group(2) or match.group(1)).casefold()
        target = references.get(html.unescape(key))
        return anchor(match.group(1), target) if target else match.group(0)

    rendered = re.sub(r"\[([^\]]+)\]\[([^\]]*)\]", reference, rendered)
    rendered = re.sub(r"\*\*([^*\n]+)\*\*", r"<strong>\1</strong>", rendered)
    rendered = re.sub(r"(?<![\w*])\*([^*\n]+)\*(?![\w*])", r"<em>\1</em>", rendered)
    rendered = re.sub(r"\x01(\d+)\x01", lambda m: maths[int(m.group(1))], rendered)
    return re.sub(r"\x00(\d+)\x00", lambda m: f"<code>{codes[int(m.group(1))]}</code>", rendered)


def _csl_authors(csl: dict[str, Any]) -> str:
    authors = csl.get("author", [])
    if not isinstance(authors, list):
        return ""
    names: list[str] = []
    for author in authors:
        if not isinstance(author, dict):
            continue
        literal = author.get("literal")
        if isinstance(literal, str) and literal:
            names.append(literal)
            continue
        given = author.get("given") if isinstance(author.get("given"), str) else ""
        family = author.get("family") if isinstance(author.get("family"), str) else ""
        name = " ".join(part for part in (given, family) if part)
        if name:
            names.append(name)
    if len(names) == 2:
        return " & ".join(names)
    if len(names) > 2:
        return ", ".join(names[:-1]) + ", & " + names[-1]
    return "".join(names)


def _csl_year(csl: dict[str, Any]) -> str:
    issued = csl.get("issued")
    if not isinstance(issued, dict):
        return ""
    parts = issued.get("date-parts")
    if (
        isinstance(parts, list)
        and parts
        and isinstance(parts[0], list)
        and parts[0]
        and isinstance(parts[0][0], int)
    ):
        return str(parts[0][0])
    return ""


def _bibtex_fields(bibtex: str) -> dict[str, str]:
    """Read literal fields from the committed BibTeX (balanced braces/quotes)."""
    fields: dict[str, str] = {}
    cursor = bibtex.find(",") + 1
    while cursor > 0 and cursor < len(bibtex):
        match = re.match(r"\s*,?\s*([A-Za-z-]+)\s*=\s*", bibtex[cursor:])
        if not match:
            break
        key = match.group(1).lower()
        cursor += match.end()
        start = cursor
        opener = bibtex[cursor:cursor + 1]
        if opener in {"{", '"'}:
            cursor += 1
            start = cursor
            depth = 1
            while cursor < len(bibtex):
                char = bibtex[cursor]
                if char == "\\":
                    cursor += 2
                    continue
                if opener == "{" and char == "{":
                    depth += 1
                elif (opener == "{" and char == "}") or (opener == '"' and char == '"'):
                    depth -= 1
                    if not depth:
                        break
                cursor += 1
            value = bibtex[start:cursor]
            cursor += 1
        else:
            while cursor < len(bibtex) and bibtex[cursor] not in ",}\n":
                cursor += 1
            value = bibtex[start:cursor].strip()
        fields[key] = _bibtex_text(value)
    return fields


def _bibtex_text(value: str) -> str:
    """Remove case-protection braces and decode common BibTeX text accents."""
    maths: list[str] = []

    def stash_math(match: re.Match[str]) -> str:
        maths.append(match.group(0))
        return f"\x00{len(maths) - 1}\x00"

    value = re.sub(r"\$[^$]+\$", stash_math, value)
    accents = {'"': "\u0308", "'": "\u0301", "`": "\u0300", "^": "\u0302",
               "~": "\u0303", "=": "\u0304", ".": "\u0307", "c": "\u0327",
               "v": "\u030c", "H": "\u030b", "u": "\u0306"}
    value = re.sub(
        r"\\([\"'`^~=.cvHu])\s*\{?([A-Za-z])\}?",
        lambda m: unicodedata.normalize("NFC", m.group(2) + accents[m.group(1)]), value,
    )
    value = re.sub(r"\\([&%_#$])", r"\1", value)
    value = value.replace("{", "").replace("}", "").replace("~", " ")
    value = re.sub(r"\x00(\d+)\x00", lambda m: maths[int(m.group(1))], value)
    return " ".join(value.split())


def _reference_list(
    citations: tuple[Citation, ...], bibliography: dict[str, dict[str, Any]]
) -> str:
    rows: list[str] = []
    for citation in citations:
        entry = bibliography[citation.key]
        csl = entry["csl"]
        bib = _bibtex_fields(entry["bibtex"])
        authors = _csl_authors(csl)
        title = bib.get("title") or (
            csl.get("title") if isinstance(csl.get("title"), str) else citation.key
        )
        doi = csl.get("DOI") if isinstance(csl.get("DOI"), str) else ""
        url = csl.get("URL") if isinstance(csl.get("URL"), str) else ""
        target = f"https://doi.org/{doi}" if doi else url
        title_html = html.escape(title)
        if target and _safe_url(target):
            title_html = f'<a href="{html.escape(target, quote=True)}">{title_html}</a>'
        venue = csl.get("container-title", "")
        if isinstance(venue, list):
            venue = ", ".join(str(part) for part in venue)
        if not isinstance(venue, str):
            venue = ""
        volume = csl.get("volume") if isinstance(csl.get("volume"), str) else ""
        issue = csl.get("issue") if isinstance(csl.get("issue"), str) else ""
        pages = csl.get("page") if isinstance(csl.get("page"), str) else ""
        venue_parts = [venue]
        if volume:
            venue_parts.append(volume + (f"({issue})" if issue else ""))
        elif issue:
            venue_parts.append(f"({issue})")
        if pages:
            venue_parts.append(pages)
        if re.match(r"\s*@book\s*\{", entry["bibtex"], re.I):
            series = bib.get("series") or csl.get("collection-title", "")
            publisher = bib.get("publisher") or csl.get("publisher", "")
            book_volume = bib.get("volume") or volume
            venue_parts = [str(series)] if series else []
            if book_volume:
                venue_parts.append(f"vol. {book_volume}")
            if publisher:
                venue_parts.append(str(publisher))
        year = _csl_year(csl)
        if year:
            venue_parts.append(year)
        details = ", ".join(part for part in venue_parts if part)
        label = entry["label"] + (f", {citation.at}" if citation.at else "")
        rows.append(
            f'<li id="ref-{html.escape(citation.key, quote=True)}">'
            f'<span class="reference-label">[{html.escape(label)}]</span> '
            + (
                f'<span class="reference-authors">{html.escape(authors)}.</span> '
                if authors
                else ""
            )
            + f'<span class="reference-title">{title_html}.</span> '
            + (f'<span class="reference-venue">{html.escape(details)}.</span>' if details else "")
            + '<details class="bibtex"><summary>BibTeX</summary><pre><code>'
            + html.escape(entry["bibtex"].strip())
            + "</code></pre></details></li>"
        )
    return '<ol class="reference-list">' + "".join(rows) + "</ol>"


def _normalize_base_path(base_path: str) -> str:
    if not isinstance(base_path, str) or not base_path.startswith("/"):
        raise CatalogError("site base path must start with /")
    if "?" in base_path or "#" in base_path or any(character.isspace() for character in base_path):
        raise CatalogError("site base path must not contain whitespace, a query, or a fragment")
    normalized = "/" + base_path.strip("/")
    return "/" if normalized == "/" else normalized + "/"


def _page_url(page: CatalogPage, base_path: str) -> str:
    return f"{base_path}{page.section}/{page.slug}/"


def _source_link(revision: str, source: SourceDeclaration) -> str:
    return (
        "https://github.com/PerAlexandersson/RealRooted/blob/"
        f"{revision}/{source.source_path}#L{source.source_line}"
    )


def _relative_url(target: str, current_url: str, base_path: str = BASE_PATH) -> str:
    if not target.startswith(base_path) or not current_url.startswith(base_path):
        raise CatalogError("generator received a URL outside its base path")
    current_relative = current_url.removeprefix(base_path).strip("/")
    target_relative = target.removeprefix(base_path).strip("/")
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


def _template(
    repo_root: pathlib.Path,
    body: str,
    title: str,
    current_url: str,
    base_path: str = BASE_PATH,
) -> str:
    template_path = repo_root / "website" / "templates" / "page.html"
    template = template_path.read_text(encoding="utf-8")
    home = _relative_url(base_path, current_url, base_path)
    stylesheet = _relative_url(f"{base_path}assets/site.css", current_url, base_path)
    script = _relative_url(f"{base_path}assets/site.js", current_url, base_path)
    results = _relative_url(f"{base_path}results/", current_url, base_path)
    authors = _relative_url(f"{base_path}authors/", current_url, base_path)
    return (
        template.replace("{{ title }}", html.escape(title))
        .replace("{{ body }}", body)
        .replace("{{ home }}", home)
        .replace("{{ stylesheet }}", stylesheet)
        .replace("{{ script }}", script)
        .replace("{{ results }}", results)
        .replace("{{ authors }}", authors)
        .replace("{{ families_index }}",
                 _relative_url(f"{base_path}families-index/", current_url, base_path))
        .replace("{{ about }}", _relative_url(f"{base_path}about/", current_url, base_path))
    )


def _authors_label(authors: tuple[str, ...]) -> str:
    if len(authors) < 2:
        return "".join(authors)
    if len(authors) == 2:
        return " & ".join(authors)
    return ", ".join(authors[:-1]) + " & " + authors[-1]


def _years_label(years: tuple[int, ...]) -> str:
    if not years:
        return ""
    if len(years) == 1:
        return str(years[0])
    return f"{years[0]}–{years[-1]}"


SECTION_LABELS = {"concepts": "Concept", "families": "Family", "theorems": "Theorem"}


def _plural(count: int, word: str) -> str:
    return f"{count} {word}" + ("" if count == 1 else "s")


def _attribution(page: CatalogPage) -> str:
    parts = [part for part in (_authors_label(page.authors), _years_label(page.years)) if part]
    return " · ".join(parts)


def _formalized_label(page: CatalogPage) -> str:
    return f"formalized {page.formalized}"


def _effective_tags(page: CatalogPage, item: CatalogItem | None = None) -> tuple[str, ...]:
    if item is None:
        return page.tags
    if item.tags is not None:
        return item.tags
    return page.tags if item.expected_kind == "theorem" else ()


def _tag_badges(tags: Iterable[str]) -> str:
    badges = []
    for tag in tags:
        label, description = PROVENANCE_TAGS[tag]
        badges.append(
            f'<span class="provenance-tag provenance-tag--{tag}" '
            f'title="{html.escape(description, quote=True)}">{html.escape(label)}</span>'
        )
    return '<span class="provenance-tags">' + "".join(badges) + "</span>" if badges else ""


def _count(count: int, word: str, kind: str) -> str:
    words = _plural(count, word)
    return (
        f'<span class="count count--{kind}" title="{words}">'
        f'{words}</span>'
    )


def _counts(page: CatalogPage) -> str:
    """What a page contains: its numbers of definitions and theorems."""
    parts = []
    if page.definitions:
        parts.append(_count(len(page.definitions), "definition", "definition"))
    if page.theorems:
        parts.append(_count(len(page.theorems), "theorem", "theorem"))
    return '<span class="card-counts">' + ' <span aria-hidden="true">·</span> '.join(parts) + "</span>"


def _title_sort_key(title: str) -> str:
    return re.sub(r"^(?:a|an|the)\s+", "", title.casefold())


def _headline(page: CatalogPage) -> CatalogItem | None:
    return next((item for item in page.theorems if item.headline),
                next(iter(page.theorems), None))


def _page_card(page: CatalogPage, href: str) -> str:
    kind = "theorem" if page.section == "theorems" else "definition"
    label = SECTION_LABELS[page.section]
    year = page.years[0] if page.years else ""
    selected = _headline(page)
    headline_html = (f'<span class="card-headlines">{html.escape(selected.label or "")}</span>'
                     if selected else "")
    return (
        f'<li class="catalog-card catalog-card--{kind} catalog-card--{page.section}" '
        f'data-title="{html.escape(_title_sort_key(page.title), quote=True)}" data-year="{year}" '
        f'data-formalized="{page.formalized}" data-slug="{page.slug}" '
        f'data-tags="{html.escape(" ".join(page.tags))}">'
        f'<a href="{html.escape(href, quote=True)}">'
        f'<span class="card-top"><span class="kind-badge kind-badge--{kind}">{label}</span>'
        + _counts(page)
        + f'</span><strong class="card-title">{html.escape(page.title)}</strong>'
        + headline_html
        + _tag_badges(page.tags)
        + f'<span class="card-attribution">{html.escape(_attribution(page))}</span>'
        + f'<span class="card-formalized">{_formalized_label(page)}</span>'
        '<span class="card-arrow" aria-hidden="true">→</span></a></li>'
    )


def _sort_controls() -> str:
    return (
        '<div class="catalog-toolbar" role="group" aria-labelledby="catalog-sort-label" '
        'data-catalog-sort><span id="catalog-sort-label" class="catalog-sort-label">Sort by</span>'
        '<label class="catalog-sort-option"><input type="radio" name="catalog-sort" '
        'value="name" checked><span class="catalog-sort-indicator" aria-hidden="true"></span>'
        '<span>Name</span></label><label class="catalog-sort-option"><input type="radio" '
        'name="catalog-sort" value="year"><span class="catalog-sort-indicator" '
        'aria-hidden="true"></span><span>Year</span></label><label class="catalog-sort-option">'
        '<input type="radio" name="catalog-sort" value="newest"><span class="catalog-sort-indicator" '
        'aria-hidden="true"></span><span>Newest</span></label></div>'
    )


def _catalog_group(identifier: str, title: str, intro: str, rows: str) -> str:
    return (
        f'<section class="catalog-group" id="{identifier}">'
        f"<h2>{title}</h2>" + (f'<p class="group-intro">{intro}</p>' if intro else "")
        + f'<ul class="catalog-index" data-catalog-list>{rows}</ul></section>'
    )


def _item_list(
    page: CatalogPage,
    items: Iterable[CatalogItem],
    resolved: dict[str, SourceDeclaration],
    revision: str,
    symcat_labels: dict[str, str],
) -> str:
    rows: list[str] = []
    for item in items:
        source = resolved[item.name]
        tags = _effective_tags(page, item)
        label = ""
        if item.label:
            label = (
                "<p class=\"declaration-label\">"
                + html.escape(item.label)
                + ("<span class=\"headline-tag\">Main result</span>" if item.headline else "")
                + _tag_badges(tags)
                + "</p>"
            )
        elif tags:
            label = _tag_badges(tags)
        symcat_link = ""
        if item.symcat:
            symcat_url = SYMCAT_ORIGIN + symcat_labels[item.symcat]
            symcat_link = (
                '<a class="symcat-source" href="'
                + html.escape(symcat_url, quote=True)
                + '">statement on symmetricfunctions.com <span aria-hidden="true">↗</span></a>'
            )
        rows.append(
            f"<li id=\"{item.anchor}\">"
            + label
            + "<div class=\"declaration-meta\"><code class=\"declaration-name\">"
            + html.escape(item.name)
            + "</code><a class=\"source\" href=\""
            + html.escape(_source_link(revision, source), quote=True)
            + '">source</a>'
            + symcat_link
            + '</div><pre class="lean-declaration"><code>'
            + html.escape(source.source_code)
            + "</code></pre></li>"
        )
    return "<ul class=\"declarations\">" + "".join(rows) + "</ul>"


def _authors_page(
    entries: Iterable[AuthorIndexEntry], base_path: str = BASE_PATH
) -> str:
    """Render the page-level credits index without adding editorial data to Lean files."""
    entries = tuple(entries)
    current_url = f"{base_path}authors/"
    rows: list[str] = []
    for entry in entries:
        heading = html.escape(entry.display_name)
        if entry.url:
            heading = (
                f'<a href="{html.escape(entry.url, quote=True)}">{heading}</a>'
                '<span class="visually-hidden"> (external link)</span>'
            )
        credits: list[str] = []
        for page in entry.pages:
            years = _years_label(page.years) or "year not recorded"
            href = _relative_url(_page_url(page, base_path), current_url, base_path)
            credits.append(
                '<li><a class="author-credit-title" href="'
                + html.escape(href, quote=True)
                + '">'
                + html.escape(page.title)
                + '</a><span class="author-credit-meta">'
                + html.escape(years)
                + " · "
                + html.escape(SECTION_LABELS[page.section])
                + "</span></li>"
            )
        rows.append(
            f'<li class="author-entry" id="{html.escape(entry.anchor, quote=True)}">'
            f"<h2>{heading}</h2><ul class=\"author-credits\">{''.join(credits)}</ul></li>"
        )
    return (
        '<main class="authors-page"><p class="eyebrow">Catalog credits</p>'
        "<h1>Authors</h1>"
        '<p class="lede">Mathematicians credited in the catalog metadata for the results '
        "formalized here.</p>"
        f'<p class="author-summary">{_plural(len(entries), "credited author")}.</p>'
        f'<ul class="authors-index">{"".join(rows)}</ul></main>'
    )


def _search_controls(index_url: str) -> str:
    return (
        f'<div class="catalog-search" data-catalog-search="{html.escape(index_url, quote=True)}">'
        '<label class="results-search" for="catalog-query">Search the whole catalog'
        '<input id="catalog-query" type="search" autocomplete="off" '
        'placeholder="Family, theorem, author, year or SymCat label" '
        'aria-describedby="search-status" data-catalog-query></label>'
        '<p id="search-status" class="search-status" role="status" aria-live="polite" '
        'aria-atomic="true" data-search-status>Search all pages and selected declarations.</p>'
        '<noscript><p>Search needs JavaScript. Browse the catalog using the links below.</p>'
        '</noscript></div>'
    )


def _search_results() -> str:
    return (
        '<section class="search-matches" aria-labelledby="search-matches-title" '
        'data-search-matches hidden><h2 id="search-matches-title">Matching declarations</h2>'
        '<ul class="search-list" data-search-list></ul>'
        '<button class="search-more" type="button" data-search-more hidden>Show more results</button>'
        '</section>'
    )


def _family_entries(pages: Iterable[CatalogPage], base_path: str) -> list[dict[str, Any]]:
    """Only explicit object metadata selects a family; page defaults target its headline."""
    entries: list[dict[str, Any]] = []
    for page in pages:
        headline = _headline(page)
        for item in page.theorems:
            # Declaration metadata overrides the page default for that theorem.
            objects = item.objects or (page.objects if item == headline else ())
            property_name = item.object_property or (
                page.object_property if item == headline and not item.objects else None
            ) or "real-rooted"
            for name in objects:
                entries.append({
                    "family": name, "property": property_name,
                    "label": item.label or item.name, "name": item.name,
                    "page": page.title, "url": _page_url(page, base_path) + f"#{item.anchor}",
                    "references": [citation.key for citation in page.citations],
                    "authors": list(page.authors), "years": list(page.years),
                })
    return sorted(entries, key=lambda entry: (
        entry["family"].casefold(), entry["label"].casefold(), entry["name"]
    ))


def _families_page(entries: list[dict[str, Any]], bibliography: dict[str, Any],
                   base_path: str) -> str:
    current_url = f"{base_path}families-index/"
    rows = []
    for entry in entries:
        target = _relative_url(entry["url"], current_url, base_path)
        page_url = entry["url"].split("#", 1)[0]
        references = "; ".join(
            f'<a href="{html.escape(_relative_url(page_url, current_url, base_path), quote=True)}'
            f'#ref-{html.escape(key, quote=True)}">'
            f'{html.escape(bibliography[key]["label"])}</a>' for key in entry["references"]
        )
        if not references:
            reference_label = (_authors_label(tuple(entry["authors"])) + " "
                               + _years_label(tuple(entry["years"]))).strip() or "See references"
            references = (
                '<a href="' + html.escape(
                    _relative_url(page_url, current_url, base_path), quote=True
                ) + '#references">' + html.escape(reference_label) + '</a>'
            )
        rows.append(
            '<tr><th scope="row">' + html.escape(entry["family"]) + '</th>'
            '<td data-label="Property">' + OBJECT_PROPERTIES[entry["property"]] + '</td>'
            '<td data-label="Theorem"><a href="' + html.escape(target, quote=True) + '">'
            + html.escape(entry["label"]) + '</a><span class="family-page">'
            + html.escape(entry["page"]) + '</span><code>' + html.escape(entry["name"])
            + '</code></td><td data-label="Reference">' + (references or "See theorem page")
            + '</td></tr>'
        )
    return (
        '<main class="families-page"><p class="eyebrow">Browse by object</p>'
        '<h1>Polynomial families</h1><p class="lede">Find a named family, its known property, '
        'and the theorem and reference. Parameter restrictions are stated in the linked theorem.</p>'
        f'<p>{len({entry["family"] for entry in entries})} families · {len(entries)} entries. '
        'This list grows as object metadata is added to the catalog.</p>'
        '<table class="families-table"><caption class="visually-hidden">'
        'Polynomial families in A–Z order</caption><thead><tr><th>Family</th><th>Property</th>'
        '<th>Theorem</th><th>Reference</th></tr></thead><tbody>' + ''.join(rows)
        + '</tbody></table></main>'
    )


def _search_index(pages: Iterable[CatalogPage], base_path: str) -> dict[str, Any]:
    """Normalize shared page metadata once to keep the declaration index compact."""
    page_records = []
    declarations = []
    for number, page in enumerate(pages):
        headline = _headline(page)
        page_records.append({
            "slug": page.slug, "title": page.title,
            "headline": headline.label if headline else "",
            "labels": [item.label for item in page.items if item.label],
            "authors": list(page.authors), "years": list(page.years), "topic": page.topic,
            "symcat": list(page.symcat_labels), "objects": list(page.objects),
            "url": _page_url(page, base_path),
        })
        for item in page.items:
            declarations.append({
                "page": number, "name": item.name, "label": item.label or "",
                "kind": item.expected_kind, "headline": item.headline,
                "symcat": item.symcat or "", "objects": list(item.objects),
                "tags": [PROVENANCE_TAGS[tag][0] for tag in _effective_tags(page, item)],
                "url": _page_url(page, base_path) + f"#{item.anchor}",
            })
    return {"schema_version": 1, "pages": page_records, "declarations": declarations}


def _results_page(
    pages: Iterable[CatalogPage], resolved: dict[str, SourceDeclaration], revision: str,
    offset: int = 0, limit: int = 200
) -> str:
    """Every selected declaration, filterable by text and kind."""
    rows: list[str] = []
    entries = [
        (page, item) for page in pages for item in page.items
    ]
    entries.sort(key=lambda entry: ((entry[1].label or entry[1].name).casefold(), entry[1].name))
    total_entries = len(entries)
    for page, item in entries[offset:offset + limit]:
        kind = item.expected_kind
        symbol = "⊢" if kind == "theorem" else "≔"
        title = item.label or ""
        tags = _effective_tags(page, item)
        href = f"../{page.section}/{page.slug}/#{item.anchor}"
        rows.append(
            f'<tr data-kind="{kind}" data-headline="{"true" if item.headline else "false"}">'
            f'<td class="result-kind result-kind--{kind}"><span aria-hidden="true">{symbol}</span>'
            f'<span class="visually-hidden">{kind}</span></td>'
            "<td class=\"result-name\">"
            + (f"<span class=\"result-label\">{html.escape(title)}</span>" if title else "")
            + ("<span class=\"headline-tag\">Main result</span>" if item.headline else "")
            + _tag_badges(tags)
            + f"<a href=\"{html.escape(href, quote=True)}\"><code>{html.escape(item.name)}</code></a></td>"
            + f"<td class=\"result-page\"><a href=\"../{page.section}/{page.slug}/\">"
            + html.escape(page.title)
            + "</a></td>"
            + "<td class=\"result-source\"><a href=\""
            + html.escape(_source_link(revision, resolved[item.name]), quote=True)
            + "\">source</a></td></tr>"
        )
    definitions = sum(1 for _, item in entries if item.expected_kind == "definition")
    theorems = len(entries) - definitions
    return (
        "<main class=\"results-page\"><p class=\"eyebrow\">Browse the catalog</p>"
        "<h1>All results</h1>"
        f"<p class=\"lede\">All {_plural(definitions, 'definition')} and "
        f"{_plural(theorems, 'theorem')} in the catalog.</p>"
        + _search_controls("../search-index.json")
        + '<p data-results-browse>Browse pages: ' + " ".join(
            f'<a href="{("../results/" if n == 0 else f"../results-{n + 1}/")}">{n + 1}</a>'
            for n in range((total_entries + limit - 1) // limit)
        ) + '</p>'
        + '<div class="results-toolbar" data-results-filter>'
        '<div class="catalog-toolbar" role="group" aria-label="Kind">'
        + "".join(
            '<label class="catalog-sort-option"><input type="radio" name="results-kind" '
            f'value="{value}"{" checked" if value == "all" else ""}>'
            '<span class="catalog-sort-indicator" aria-hidden="true"></span>'
            f"<span>{text}</span></label>"
            for value, text in (
                ("all", "All"),
                ("headline", "Main results"),
                ("definition", "Definitions"),
                ("theorem", "Theorems"),
            )
        )
        + "</div></div>" + _search_results()
        + '<table class="results-table" data-results-browse><thead><tr><th><span class="visually-hidden">Kind</span></th>'
        "<th>Result</th><th>Page</th><th><span class=\"visually-hidden\">Source</span></th></tr></thead>"
        "<tbody>" + "".join(rows) + "</tbody></table></main>"
    )


class _HrefCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []
        self.ids: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self.ids.update(value for name, value in attrs if name == "id" and value is not None)
        if tag == "a":
            self.hrefs.extend(value for name, value in attrs if name == "href" and value is not None)


def validate_internal_links(files: dict[str, str], base_path: str = BASE_PATH) -> None:
    """Reject generated links that cannot resolve under the project-site base path."""
    known = set(files)
    documents: dict[str, _HrefCollector] = {}
    for source_name, document in files.items():
        if not source_name.endswith(".html"):
            continue
        collector = _HrefCollector()
        collector.feed(document)
        documents[source_name] = collector
    for source_name, collector in documents.items():
        source_directory = pathlib.PurePosixPath(source_name).parent
        for href in collector.hrefs:
            parsed = urlsplit(href)
            if parsed.scheme or parsed.netloc:
                continue
            if not parsed.path:
                target = source_name
                target_path = ""
            elif href.startswith("/"):
                if not href.startswith(base_path):
                    raise CatalogError(f"{source_name}: link escapes {base_path}: {href}")
                target_path = href[len(base_path) :].split("#", 1)[0]
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
            if parsed.fragment and target in documents and parsed.fragment not in documents[target].ids:
                raise CatalogError(f"{source_name}: broken internal fragment {href}")


PROSE_PATTERNS = {
    "backticks": re.compile(r"`+[^`]+`+"),
    "the-library": re.compile(r"\bthe\s+library\b", re.I),
    "lean": re.compile(r"\bLean\b", re.I),
    "no-published-source": re.compile(r"\bNo\s+published\s+source\b", re.I),
    "unless-stated": re.compile(r"\bunless\s+stated\b", re.I),
    "bracket-display": re.compile(r"\\\["),
    "absolute-link": re.compile(r"(?<![\w./-])/RealRooted/"),
}


def prose_findings(pages: Iterable[CatalogPage]) -> set[str]:
    """Stable baseline records: source path, rule, normalized offending text."""
    findings: set[str] = set()
    allowed = ("Results", "Use", "Proof", "References")
    for page in pages:
        def add(rule: str, text: str) -> None:
            findings.add(f"{page.source_path}\t{rule}\t{' '.join(text.split())}")

        # Work on paragraphs so wrapped phrases cannot evade lint. Code fences
        # are removed first; inline code is deliberately still checked.
        prose: list[str] = []
        fence: str | None = None
        for line in page.content.splitlines():
            marker = re.match(r"\s*(`{3,}|~{3,})", line)
            if marker:
                token = marker.group(1)
                if fence is None:
                    fence = token
                elif token[0] == fence[0] and len(token) >= len(fence):
                    fence = None
                prose.append("")
            elif fence is None:
                prose.append(line)
        headings: list[str] = []
        for line in prose:
            match = re.fullmatch(r"##\s+(.+?)\s*", line)
            if match:
                heading = match.group(1)
                if heading not in allowed:
                    add("h2-unknown", heading)
                elif heading in headings:
                    add("h2-duplicate", heading)
                elif any(allowed.index(previous) > allowed.index(heading) for previous in headings):
                    add("h2-order", heading)
                if heading in allowed:
                    headings.append(heading)
        for required in ("Results", "References"):
            if required not in headings:
                add("h2-missing", required)
        for paragraph in re.split(r"\n\s*\n", "\n".join(prose)):
            text = " ".join(paragraph.split())
            for rule, pattern in PROSE_PATTERNS.items():
                if pattern.search(text):
                    add(rule, text)
    return findings


def validate_prose_baseline(repo_root: pathlib.Path, pages: Iterable[CatalogPage]) -> None:
    path = repo_root / "scripts/prose_baseline.txt"
    try:
        baseline = {line for line in path.read_text(encoding="utf-8").splitlines()
                    if line and not line.startswith("#")}
    except OSError as error:
        raise CatalogError(f"cannot load prose baseline: {error}") from error
    findings = prose_findings(pages)
    errors = [f"new prose offender: {record}" for record in sorted(findings - baseline)]
    errors += [f"stale prose baseline entry: {record}" for record in sorted(baseline - findings)]
    if errors:
        raise CatalogError("\n".join(errors))


def load_redirects(repo_root: pathlib.Path, catalog_links: dict[str, str]) -> dict[str, str]:
    """Map retired section/slug paths directly to existing canonical URLs."""
    path = repo_root / "website/redirects.toml"
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise CatalogError(f"cannot load redirects: {error}") from error
    if set(data) != {"redirects"} or not isinstance(data["redirects"], dict):
        raise CatalogError(f"{path}: expected a [redirects] table")
    redirects: dict[str, str] = {}
    for retired, slug in data["redirects"].items():
        if not re.fullmatch(r"(?:concepts|families|theorems)/[a-z0-9]+(?:-[a-z0-9]+)*", retired):
            raise CatalogError(f"{path}: invalid retired path {retired}")
        if not isinstance(slug, str) or slug not in catalog_links:
            raise CatalogError(f"{path}: unknown redirect target {slug}")
        redirects[retired + "/index.html"] = catalog_links[slug]
    return redirects


def _page_header(page: CatalogPage, labels: dict[str, str], base_path: str) -> str:
    topic_href = f"{base_path}#{_topic_anchor(page.topic)}"
    parts = [
        '<div class="page-metadata">',
        f'<p class="page-attribution">{html.escape(_attribution(page))}</p>'
        if _attribution(page) else "",
        _tag_badges(page.tags),
        f'<p class="topic-breadcrumb"><a href="{topic_href}">{html.escape(page.topic)}</a>'
        f' › <a href="{base_path}{page.section}/">{SECTION_LABELS[page.section]}</a></p>',
    ]
    if page.symcat_labels:
        links = [f'<a href="{html.escape(SYMCAT_ORIGIN + labels[label], quote=True)}">'
                 f'{html.escape(label)}</a>' for label in page.symcat_labels]
        parts.append('<p class="page-symcat">SymCat: ' + " · ".join(links) + "</p>")
    headline = _headline(page)
    if headline:
        parts.append(f'<p class="page-headline">Main result: <a href="#{headline.anchor}">'
                     f'{html.escape(headline.label or headline.name)}</a></p>')
    return "".join(parts) + "</div>"


class _SummaryText(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.in_paragraph = False
        self.done = False
        self.parts: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "p" and not self.done:
            self.in_paragraph = True

    def handle_endtag(self, tag: str) -> None:
        if tag == "p" and self.in_paragraph:
            self.in_paragraph = False
            self.done = True

    def handle_data(self, data: str) -> None:
        if self.in_paragraph:
            self.parts.append(data)


def _summary(rendered_content: str) -> str:
    parser = _SummaryText()
    parser.feed(rendered_content)
    return " ".join("".join(parser.parts).split())


def render_site(
    repo_root: pathlib.Path,
    pages: tuple[CatalogPage, ...],
    resolved: dict[str, SourceDeclaration],
    revision: str,
    *,
    base_path: str = BASE_PATH,
    site_origin: str = SITE_ORIGIN,
) -> dict[str, str]:
    """Render deterministic generated files keyed by their output-relative path."""
    base_path = _normalize_base_path(base_path)
    parsed_origin = urlsplit(site_origin)
    if parsed_origin.scheme not in {"http", "https"} or not parsed_origin.netloc:
        raise CatalogError("site origin must be an absolute HTTP(S) URL")
    site_origin = site_origin.rstrip("/")
    symcat_labels, bibliography = load_symcat_snapshots(repo_root)
    catalog_links = {"about": f"{base_path}about/",
                     "families-index": f"{base_path}families-index/"}
    for page in pages:
        if page.slug in catalog_links:
            raise _source_error(page.source_path, f"duplicate catalog slug {page.slug}")
        catalog_links[page.slug] = _page_url(page, base_path)
    for page in pages:
        for citation in page.citations:
            if citation.key not in bibliography:
                raise _source_error(page.source_path, f"unknown bibliography key {citation.key}")
        for label in page.symcat_labels:
            if label not in symcat_labels:
                raise _source_error(
                    page.source_path, f"unknown symmetricfunctions.com label {label}"
                )
        for item in page.items:
            if item.symcat and item.symcat not in symcat_labels:
                raise _source_error(
                    page.source_path,
                    f"unknown symmetricfunctions.com label {item.symcat} for {item.name}",
                )
    files: dict[str, str] = {}
    author_entries = build_author_index(pages, load_author_profiles(repo_root))
    grouped = {section: [page for page in pages if page.section == section] for section in SECTIONS}
    index_pages = sorted(pages, key=lambda page: (_title_sort_key(page.title), page.slug))
    topics = [topic for topic in TOPICS.values() if any(page.topic == topic for page in pages)]
    jump_bar = '<nav class="topic-jump" id="topics" aria-label="Topics">' + "".join(
        f'<a href="#{_topic_anchor(topic)}">{html.escape(topic)}</a>' for topic in topics
    ) + '</nav>'
    total_definitions = sum(len(page.definitions) for page in pages)
    total_theorems = sum(len(page.theorems) for page in pages)
    total_headlines = sum(item.headline for page in pages for item in page.theorems)
    index_body = (
        "<main class=\"catalog-home\"><section class=\"hero\">"
        "<p class=\"eyebrow\">Reference catalog</p>"
        "<h1>Real-rooted polynomials</h1>"
        "<p class=\"lede\">Definitions and theorems on real-rooted polynomials, interlacing "
        "and total positivity, formalized in Lean. Each statement links to its Lean source.</p>"
        f"<p class=\"hero-stats\"><a href=\"results/\">{_plural(total_definitions, 'definition')} and "
        f"{_plural(total_theorems, 'theorem')}</a>"
        + (
            f", including {_plural(total_headlines, 'main result')}"
            if total_headlines
            else ""
        )
        + ".</p></section>"
        + _search_controls("search-index.json")
        + jump_bar
        + _sort_controls()
        + '<div class="catalog-groups">'
        + "".join(_catalog_group(
            _topic_anchor(topic), html.escape(topic), "",
            "".join(_page_card(page, f"{page.section}/{page.slug}/")
                    for page in index_pages if page.topic == topic),
        ) for topic in topics)
        + "</div>" + _search_results() + "</main>"
    )
    files["index.html"] = _template(
        repo_root, index_body, "RealRooted catalog", base_path, base_path
    )
    for section, section_pages in grouped.items():
        links = "".join(_page_card(page, f"{page.slug}/") for page in sorted(
            section_pages, key=lambda page: (_title_sort_key(page.title), page.slug)
        ))
        body = (
            "<main class=\"section-page\"><p class=\"eyebrow\">Browse the catalog</p>"
            f"<h1>{html.escape(section.title())}</h1>"
            + _sort_controls()
            + f'<ul class="section-index" data-catalog-list>{links}</ul></main>'
        )
        section_url = f"{base_path}{section}/"
        files[f"{section}/index.html"] = _template(
            repo_root, body, section.title(), section_url, base_path
        )
    summaries: dict[str, str] = {}
    for page in pages:
        definition_html = (
            _item_list(page, page.definitions, resolved, revision, symcat_labels)
            if page.definitions
            else ""
        )
        theorem_html = (
            _item_list(page, page.theorems, resolved, revision, symcat_labels)
            if page.theorems
            else ""
        )
        selected = ""
        if definition_html:
            selected += (
                '<section class="declaration-group declaration-group--definition" id="definitions">'
                '<h2><span aria-hidden="true">≔</span> Definitions</h2>'
                + definition_html
                + "</section>"
            )
        if theorem_html:
            selected += (
                '<section class="declaration-group declaration-group--theorem" id="theorems">'
                '<h2><span aria-hidden="true">⊢</span> Theorems</h2>'
                + theorem_html
                + "</section>"
            )
        source = html.escape(_source_link(revision, SourceDeclaration("", "", page.source_path, 1)), quote=True)
        rendered_content = render_markdown(
            page.content,
            symcat_labels=symcat_labels,
            bibliography=bibliography,
            base_path=base_path,
            catalog_links=catalog_links,
            generated_references=_reference_list(page.citations, bibliography)
            if page.citations
            else "",
        )
        summaries[page.slug] = _summary(rendered_content)
        rendered_content = rendered_content.replace(
            "</h1>", "</h1>" + _page_header(page, symcat_labels, base_path), 1
        )
        body = (
            "<main class=\"catalog-page\"><article class=\"prose\">"
            + rendered_content
            + "</article><div class=\"lean-results\">"
            + selected
            + "</div>"
            + f"<p class=\"verification\"><span>Lean source</span> "
            + f"<a href=\"{source}\">{html.escape(page.source_path)}</a> at revision "
            + f"<code>{html.escape(revision[:8])}</code>. <span class=\"formalized\">"
            + f"Formalized {page.formalized}</span>.</p></main>"
        )
        files[f"{page.section}/{page.slug}/index.html"] = _template(
            repo_root, body, page.title, _page_url(page, base_path), base_path
        )
    files["results/index.html"] = _template(
        repo_root,
        _results_page(pages, resolved, revision),
        "All results",
        f"{base_path}results/",
        base_path,
    )
    result_count = sum(len(page.items) for page in pages)
    for number in range(1, (result_count + 199) // 200):
        files[f"results-{number + 1}/index.html"] = _template(
            repo_root, _results_page(pages, resolved, revision, number * 200),
            "All results", f"{base_path}results-{number + 1}/", base_path,
        )
    files["authors/index.html"] = _template(
        repo_root,
        _authors_page(author_entries, base_path),
        "Authors",
        f"{base_path}authors/",
        base_path,
    )
    family_entries = _family_entries(pages, base_path)
    files["families-index/index.html"] = _template(
        repo_root, _families_page(family_entries, bibliography, base_path),
        "Polynomial families", f"{base_path}families-index/", base_path,
    )
    about_source = (repo_root / "website/about.md").read_text(encoding="utf-8")
    about_body = '<main class="catalog-page"><article class="prose">' + render_markdown(
        about_source, base_path=base_path, catalog_links=catalog_links,
    ) + '</article></main>'
    files["about/index.html"] = _template(
        repo_root, about_body, "Conventions", f"{base_path}about/", base_path,
    )
    for retired, target in load_redirects(repo_root, catalog_links).items():
        if retired in files:
            raise CatalogError(f"redirect collides with an existing page: {retired}")
        # Relative URLs also work when the preview is served below a different base.
        current = base_path + retired.removesuffix("index.html")
        href = html.escape(_relative_url(target, current, base_path), quote=True)
        files[retired] = (
            '<!doctype html><html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width, initial-scale=1">'
            '<meta name="color-scheme" content="light dark">'
            f'<meta http-equiv="refresh" content="0; url={href}">'
            f'<link rel="canonical" href="{html.escape(site_origin + target, quote=True)}">'
            '<title>Page moved · RealRooted</title></head><body><main>'
            f'<h1>Page moved</h1><p><a href="{href}">Continue to the catalog page</a>.</p>'
            '</main></body></html>\n'
        )
    manifest = {
        "schema_version": 1,
        "revision": revision,
        "catalog_digest": catalog_digest(pages),
        "families_index": {
            "url": f"{base_path}families-index/", "entries": family_entries,
        },
        "pages": [
            {
                "title": page.title,
                "url": _page_url(page, base_path),
                "source_path": page.source_path,
                "topic": page.topic,
                "section": page.section,
                "summary": summaries[page.slug],
                "headline": {"name": _headline(page).name, "label": _headline(page).label}
                if _headline(page) else None,
                "symcat": list(page.symcat_labels),
                "objects": list(page.objects),
                "property": page.object_property,
                "references": [citation.key for citation in page.citations],
                "authors": list(page.authors),
                "years": list(page.years),
                "formalized": page.formalized,
                "tags": list(page.tags),
                "definitions": [item.name for item in page.definitions],
                "theorems": [item.name for item in page.theorems],
                "headlines": [item.name for item in page.theorems if item.headline],
                "labels": {item.name: item.label for item in page.items if item.label},
                "declarations": [
                    {
                        "name": item.name,
                        "kind": item.expected_kind,
                        "url": site_origin + _page_url(page, base_path) + f"#{item.anchor}",
                        "tags": list(_effective_tags(page, item)),
                        "objects": list(item.objects),
                        "property": item.object_property,
                        **({"symcat": item.symcat} if item.symcat else {}),
                    }
                    for item in page.items
                ],
            }
            for page in pages
        ],
    }
    files["catalog-manifest.json"] = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    files["search-index.json"] = json.dumps(
        _search_index(pages, base_path), ensure_ascii=False, separators=(",", ":")
    ) + "\n"
    files["llms.txt"] = (
        "# RealRooted catalog\n\nPolynomial families — A–Z properties, theorems and references — "
        + site_origin + base_path + "families-index/\n\n"
    ) + "\n".join(
        " — ".join((page.title, headline.label or "", headline.name,
                    site_origin + _page_url(page, base_path)))
        if (headline := _headline(page)) else " — ".join((
            page.title, "", "", site_origin + _page_url(page, base_path)
        ))
        for page in index_pages
    ) + "\n"
    asset = repo_root / "website" / "assets" / "site.css"
    files["assets/site.css"] = asset.read_text(encoding="utf-8")
    script = repo_root / "website" / "assets" / "site.js"
    files["assets/site.js"] = script.read_text(encoding="utf-8")
    validate_internal_links(files, base_path)
    return files


def write_site(output: pathlib.Path, files: dict[str, str]) -> None:
    for relative, content in files.items():
        path = output / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
