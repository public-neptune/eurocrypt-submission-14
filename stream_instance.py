#!/usr/bin/env python3
"""Stream the bundled line-oriented challenge format without materializing it."""
from __future__ import annotations

import gzip
import string
from typing import Iterator


LO, UP = string.ascii_lowercase, string.ascii_uppercase


def _plain_rule(text: str) -> tuple[str, str]:
    text = text.strip()
    if text.endswith(","):
        text = text[:-1].rstrip()
    if not text.startswith('"') or "\\" in text:
        raise ValueError("instance is not in the bundled one-rule-per-line format")
    end_u = text.find('"', 1)
    start_v = text.find('"', end_u + 1)
    end_v = text.find('"', start_v + 1)
    if end_u < 0 or start_v < 0 or end_v < 0 or text[end_v + 1:].strip():
        raise ValueError("malformed line-oriented rule")
    if ":" not in text[end_u + 1:start_v]:
        raise ValueError("missing rule separator")
    return text[1:end_u], text[start_v + 1:end_v]


def iter_rules(path: str) -> Iterator[tuple[str, str]]:
    """Yield the rules from a bundled line-oriented challenge."""
    in_rules = False
    with gzip.open(path, "rt", encoding="utf-8", newline="") as source:
        for raw in source:
            line = raw.strip()
            if in_rules:
                closes = line.endswith("},") or line == "}"
                if closes:
                    line = line[:-2].rstrip() if line.endswith("},") else ""
                if line:
                    yield _plain_rule(line)
                if closes:
                    in_rules = False
                continue

            if line.startswith("{"):
                line = line[1:].lstrip()
            if line.startswith('"rules"') or line.startswith('"rules":'):
                brace = line.find("{")
                if brace < 0:
                    raise ValueError("malformed rules object")
                rest = line[brace + 1:].strip()
                closes = rest.endswith("},") or rest == "}"
                if closes:
                    rest = rest[:-2].rstrip() if rest.endswith("},") else ""
                if rest:
                    yield _plain_rule(rest)
                in_rules = not closes
    if in_rules:
        raise ValueError("truncated instance JSON")


def parse_coupling(left: str, right: str):
    """Decode a relation V u = u W linking the two generator copies."""
    li = 0
    while li < len(left) and left[li].isupper():
        li += 1
    ri = 0
    while ri < len(right) and right[ri].islower():
        ri += 1
    V, u = left[:li], left[li:]
    same_u, W = right[:ri], right[ri:]
    if (not V or not u or not W or u != same_u or
            not V.isupper() or not u.islower() or not W.isupper()):
        return None
    try:
        return {
            "V": [UP.index(c) for c in V],
            "u": [LO.index(c) for c in u],
            "W": [UP.index(c) for c in W],
        }
    except ValueError:
        return None
