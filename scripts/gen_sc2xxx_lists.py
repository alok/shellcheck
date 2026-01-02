#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HS_DIR = ROOT / "src" / "ShellCheck"
LEAN_DIR = ROOT / "ShellCheck"
OUT1 = ROOT / "ShellCheck" / "Tests" / "SC1xxxLists.lean"
OUT2 = ROOT / "ShellCheck" / "Tests" / "SC2xxxLists.lean"
OUT3 = ROOT / "ShellCheck" / "Tests" / "SC3xxxLists.lean"
OUT4 = ROOT / "ShellCheck" / "Tests" / "SC4xxxLists.lean"

CODE_RE = re.compile(r"\b[1-4]\d{3}\b")
LEAN_LINE_RE = None
IGNORED_CODES = {1234}  # Upstream parser property placeholder, not a real check.


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        ch = text[i]
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
                continue
            if ch == "\"":
                in_string = False
            i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        if ch == "\"":
            in_string = True
        out.append(ch)
        i += 1
    return "".join(out)


def strip_haskell_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_char = False
    while i < len(text):
        if depth > 0:
            if text.startswith("{-", i):
                depth += 1
                i += 2
            elif text.startswith("-}", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        ch = text[i]
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
                continue
            if ch == "\"":
                in_string = False
            i += 1
            continue
        if in_char:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
                continue
            if ch == "'":
                in_char = False
            i += 1
            continue
        if text.startswith("{-", i):
            depth += 1
            i += 2
            continue
        if text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        if ch == "\"":
            in_string = True
        if ch == "'":
            in_char = True
        out.append(ch)
        i += 1
    return "".join(out)


def extract_haskell_codes() -> list[int]:
    codes: set[int] = set()
    for path in HS_DIR.rglob("*.hs"):
        text = strip_haskell_comments(path.read_text(encoding="utf-8"))
        for match in CODE_RE.findall(text):
            codes.add(int(match))
    return sorted(codes)


def extract_lean_codes() -> list[int]:
    codes: set[int] = set()
    lean_files = [
        path
        for path in LEAN_DIR.rglob("*.lean")
        if "Tests" not in path.parts
    ]
    for path in lean_files:
        text = strip_lean_comments(path.read_text(encoding="utf-8"))
        for match in CODE_RE.findall(text):
            codes.add(int(match))
    return sorted(codes)


def format_list(codes: list[int]) -> str:
    return "[" + ", ".join(str(code) for code in codes) + "]"


def filter_prefix(codes: list[int], prefix: int) -> list[int]:
    return [code for code in codes if code // 1000 == prefix]


def write_list(
    out_path: Path,
    namespace: str,
    upstream: list[int],
    implemented: list[int],
    ignored: list[int],
) -> None:
    content = f"""import Std

namespace {namespace}

def upstream : List Nat := {format_list(upstream)}

def implemented : List Nat := {format_list(implemented)}

def ignored : List Nat := {format_list(ignored)}

def upstreamFiltered : List Nat :=
  upstream.filter (fun code => !ignored.contains code)

def implementedFiltered : List Nat :=
  implemented.filter (fun code => !ignored.contains code)

def missing : List Nat :=
  upstreamFiltered.filter (fun code => !implementedFiltered.contains code)

def extra : List Nat :=
  implementedFiltered.filter (fun code => !upstreamFiltered.contains code)

end {namespace}
"""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(content, encoding="utf-8")


def main() -> None:
    upstream_all = extract_haskell_codes()
    implemented_all = extract_lean_codes()

    ignored_all = sorted(IGNORED_CODES)
    upstream1 = filter_prefix(upstream_all, 1)
    implemented1 = filter_prefix(implemented_all, 1)
    ignored1 = filter_prefix(ignored_all, 1)
    upstream2 = filter_prefix(upstream_all, 2)
    implemented2 = filter_prefix(implemented_all, 2)
    ignored2 = filter_prefix(ignored_all, 2)
    upstream3 = filter_prefix(upstream_all, 3)
    implemented3 = filter_prefix(implemented_all, 3)
    ignored3 = filter_prefix(ignored_all, 3)
    upstream4 = filter_prefix(upstream_all, 4)
    implemented4 = filter_prefix(implemented_all, 4)
    ignored4 = filter_prefix(ignored_all, 4)

    write_list(OUT1, "ShellCheck.Tests.SC1xxxLists", upstream1, implemented1, ignored1)
    write_list(OUT2, "ShellCheck.Tests.SC2xxxLists", upstream2, implemented2, ignored2)
    write_list(OUT3, "ShellCheck.Tests.SC3xxxLists", upstream3, implemented3, ignored3)
    write_list(OUT4, "ShellCheck.Tests.SC4xxxLists", upstream4, implemented4, ignored4)

    upstream1_f = [code for code in upstream1 if code not in ignored1]
    implemented1_f = [code for code in implemented1 if code not in ignored1]
    upstream2_f = [code for code in upstream2 if code not in ignored2]
    implemented2_f = [code for code in implemented2 if code not in ignored2]
    upstream3_f = [code for code in upstream3 if code not in ignored3]
    implemented3_f = [code for code in implemented3 if code not in ignored3]
    upstream4_f = [code for code in upstream4 if code not in ignored4]
    implemented4_f = [code for code in implemented4 if code not in ignored4]

    missing1 = [code for code in upstream1_f if code not in implemented1_f]
    extra1 = [code for code in implemented1_f if code not in upstream1_f]
    missing2 = [code for code in upstream2_f if code not in implemented2_f]
    extra2 = [code for code in implemented2_f if code not in upstream2_f]
    missing3 = [code for code in upstream3_f if code not in implemented3_f]
    extra3 = [code for code in implemented3_f if code not in upstream3_f]
    missing4 = [code for code in upstream4_f if code not in implemented4_f]
    extra4 = [code for code in implemented4_f if code not in upstream4_f]

    print(f"Wrote {OUT1}")
    print(f"Wrote {OUT2}")
    print(f"Wrote {OUT3}")
    print(f"Wrote {OUT4}")
    print(f"Upstream SC1xxx: {len(upstream1)}")
    print(f"Implemented SC1xxx: {len(implemented1)}")
    print(f"Missing SC1xxx: {len(missing1)}")
    print(f"Extra SC1xxx: {len(extra1)}")
    if missing1:
        print("Missing SC1xxx codes:", ", ".join(str(code) for code in missing1))
    if extra1:
        print("Extra SC1xxx codes:", ", ".join(str(code) for code in extra1))
    print(f"Upstream SC2xxx: {len(upstream2)}")
    print(f"Implemented SC2xxx: {len(implemented2)}")
    print(f"Missing SC2xxx: {len(missing2)}")
    print(f"Extra SC2xxx: {len(extra2)}")
    if missing2:
        print("Missing SC2xxx codes:", ", ".join(str(code) for code in missing2))
    if extra2:
        print("Extra SC2xxx codes:", ", ".join(str(code) for code in extra2))
    print(f"Upstream SC3xxx: {len(upstream3)}")
    print(f"Implemented SC3xxx: {len(implemented3)}")
    print(f"Missing SC3xxx: {len(missing3)}")
    print(f"Extra SC3xxx: {len(extra3)}")
    if missing3:
        print("Missing SC3xxx codes:", ", ".join(str(code) for code in missing3))
    if extra3:
        print("Extra SC3xxx codes:", ", ".join(str(code) for code in extra3))
    print(f"Upstream SC4xxx: {len(upstream4)}")
    print(f"Implemented SC4xxx: {len(implemented4)}")
    print(f"Missing SC4xxx: {len(missing4)}")
    print(f"Extra SC4xxx: {len(extra4)}")
    if missing4:
        print("Missing SC4xxx codes:", ", ".join(str(code) for code in missing4))
    if extra4:
        print("Extra SC4xxx codes:", ", ".join(str(code) for code in extra4))


if __name__ == "__main__":
    main()
