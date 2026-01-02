#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
HS_DIR = ROOT / "src" / "ShellCheck"
LEAN_ANALYTICS = ROOT / "ShellCheck" / "Analytics.lean"
LEAN_CHECKS = ROOT / "ShellCheck" / "Checks"
OUT = ROOT / "ShellCheck" / "Tests" / "SC2xxxLists.lean"

CODE_RE = re.compile(r"\b2\d{3}\b")
LEAN_LINE_RE = re.compile(r"\b(makeCommentWithFix|makeComment|warnOn|warn)\b")


def extract_haskell_codes() -> list[int]:
    codes: set[int] = set()
    for path in HS_DIR.rglob("*.hs"):
        text = path.read_text(encoding="utf-8")
        for match in CODE_RE.findall(text):
            codes.add(int(match))
    return sorted(codes)


def extract_lean_codes() -> list[int]:
    codes: set[int] = set()
    lean_files = [LEAN_ANALYTICS] + list(LEAN_CHECKS.rglob("*.lean"))
    for path in lean_files:
        for line in path.read_text(encoding="utf-8").splitlines():
            if LEAN_LINE_RE.search(line):
                for match in CODE_RE.findall(line):
                    codes.add(int(match))
    return sorted(codes)


def format_list(codes: list[int]) -> str:
    return "[" + ", ".join(str(code) for code in codes) + "]"


def main() -> None:
    upstream = extract_haskell_codes()
    implemented = extract_lean_codes()

    OUT.parent.mkdir(parents=True, exist_ok=True)
    content = f"""import Std

namespace ShellCheck.Tests.SC2xxxLists

def upstreamSC2xxx : List Nat := {format_list(upstream)}

def implementedSC2xxx : List Nat := {format_list(implemented)}

def missingSC2xxx : List Nat :=
  upstreamSC2xxx.filter (fun code => !implementedSC2xxx.contains code)

def extraSC2xxx : List Nat :=
  implementedSC2xxx.filter (fun code => !upstreamSC2xxx.contains code)

end ShellCheck.Tests.SC2xxxLists
"""
    OUT.write_text(content, encoding="utf-8")

    missing = [code for code in upstream if code not in implemented]
    extra = [code for code in implemented if code not in upstream]

    print(f"Wrote {OUT}")
    print(f"Upstream SC2xxx: {len(upstream)}")
    print(f"Implemented SC2xxx: {len(implemented)}")
    print(f"Missing: {len(missing)}")
    print(f"Extra: {len(extra)}")
    if missing:
        print("Missing codes:", ", ".join(str(code) for code in missing))


if __name__ == "__main__":
    main()
