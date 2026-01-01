#!/usr/bin/env python3
import datetime
import pathlib
import re
from typing import Iterable, Set

HS_RX = re.compile(
    r"\b(?:warn|err|info|style|warnWithFix|errWithFix|infoWithFix|styleWithFix)\b"
    r"[^\n]*?\b([0-9]{4})\b"
)
LEAN_RX = re.compile(
    r"\b(?:makeCommentWithFix|makeComment|warnCmd|errorCmd|styleCmd|infoCmd|"
    r"warnArg|errorArg|styleArg|infoArg|warnWithFix|errWithFix|infoWithFix|"
    r"styleWithFix|warn|err|info|style)\b[^\n]*?\b([0-9]{4})\b"
)


def extract_codes(paths: Iterable[pathlib.Path], rx: re.Pattern, lo: int, hi: int) -> Set[int]:
    codes: Set[int] = set()
    for path in paths:
        try:
            text = path.read_text()
        except Exception:
            continue
        for m in rx.finditer(text):
            code = int(m.group(1))
            if lo <= code <= hi:
                codes.add(code)
    return codes


def main() -> None:
    root = pathlib.Path(__file__).resolve().parents[1]
    hs_paths = root.joinpath("src", "ShellCheck").rglob("*.hs")
    lean_paths = root.joinpath("ShellCheck").rglob("*.lean")

    hs_codes = extract_codes(hs_paths, HS_RX, 1000, 3999)
    lean_codes = extract_codes(lean_paths, LEAN_RX, 1000, 3999)
    missing = sorted(hs_codes - lean_codes)

    out = root / "doc" / "sc_parity_report.txt"
    today = datetime.date.today().isoformat()
    lines = []
    lines.append(f"ShellCheck parity report (generated {today})\n")
    lines.append(f"Haskell codes:      {len(hs_codes)}")
    lines.append(f"Lean codes:      {len(lean_codes)}")
    lines.append(f"Missing in Lean:      {len(missing)}\n")
    if missing:
        lines.append("Missing SC codes (Haskell-only):")
        lines.extend([f"SC{code}" for code in missing])
    out.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
