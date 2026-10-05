#!/usr/bin/env python3
"""docs 配下の {{#include path:anchor}} が、実在するファイルの実在する ANCHOR を指すか検査する。

mdBook は存在しない ANCHOR を空ブロックとして黙って出力するので、CI でこのスクリプトを回す。
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DOCS = ROOT / "docs" / "src"
INCLUDE = re.compile(r"\{\{#include\s+([^\s:}]+)(?::([A-Za-z0-9_\-]+))?\s*\}\}")
ANCHOR = re.compile(r"ANCHOR:\s*([A-Za-z0-9_\-]+)")


def anchors_of(path: pathlib.Path) -> set[str]:
    return set(ANCHOR.findall(path.read_text(encoding="utf-8")))


def main() -> int:
    errors: list[str] = []
    cache: dict[pathlib.Path, set[str]] = {}
    for md in sorted(DOCS.rglob("*.md")):
        for m in INCLUDE.finditer(md.read_text(encoding="utf-8")):
            target = (md.parent / m.group(1)).resolve()
            anchor = m.group(2)
            if not target.is_file():
                errors.append(f"{md.relative_to(ROOT)}: missing file {m.group(1)}")
                continue
            if anchor is not None:
                if target not in cache:
                    cache[target] = anchors_of(target)
                if anchor not in cache[target]:
                    errors.append(f"{md.relative_to(ROOT)}: missing anchor {anchor} in {m.group(1)}")
    for e in errors:
        print(e)
    print(f"check_includes: {len(errors)} error(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
