#!/usr/bin/env python3
"""Dependency-ordered source audit queue, not a semantic-equivalence certificate.

Use actual coqdep edges/order and compiler .glob declaration positions. Require
the pinned clean sources and matching .glob digests. Compiled Lean candidates
and source anchors never automatically become reviewed contracts. Review state
comes only from the separate, evidence-bearing manual manifest.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

from flocq_bridge import ROOT, lean_source_fingerprint, require_lean_source_snapshot, run, verify_reference
from validate_flocq_source_refs import validate_references

DECL_KINDS = {"abbrev", "def", "prf", "ind", "constr", "rec", "proj", "inst", "scheme"}
CONTEXT_KINDS = {"binder", "var", "sec", "mod"}
STATES = {"reviewed-contract", "adapted-proof-infrastructure"}


def parse_glob(source: bytes, glob: str, path: str) -> tuple[list[dict], list[str]]:
    lines = glob.splitlines()
    expected = "DIGEST " + hashlib.md5(source).hexdigest()
    if not lines or lines[0] != expected:
        raise ValueError(f"stale or missing compiled .glob digest: {path}")
    if len(lines) < 2 or not lines[1].startswith("FFlocq."):
        raise ValueError(f"unexpected logical module: {path}")
    declarations, imports = [], set()
    for line in lines[2:]:
        if not line:
            continue
        fields = line.split()
        if line.startswith("R"):
            if fields[-1] == "lib":
                imports.add(fields[1])
            continue
        kind = fields[0]
        if kind in CONTEXT_KINDS:
            continue
        if kind not in DECL_KINDS or len(fields) != 4:
            raise ValueError(f"unknown declaration metadata in {path}: {line}")
        span = re.fullmatch(r"(\d+):(\d+)", fields[1])
        if span is None:
            raise ValueError(f"invalid declaration range: {line}")
        start, end = map(int, span.groups())
        if not 0 <= start <= end < len(source):
            raise ValueError(f"declaration outside source: {line}")
        name = fields[3] if fields[2] == "<>" else fields[2] + "." + fields[3]
        source_key = f"{path}:{name}"
        identity = f"{source_key}@{start}"
        previous = next((d for d in declarations if d['id'] == identity), None)
        if previous is not None:
            # Rocq records its single-field classes twice: inductive/record and
            # constructor/projection facets at exactly the same source token.
            if (previous['offset'] != start or
                    {previous['kind'], kind} not in ({'ind', 'rec'}, {'constr', 'proj'})):
                raise ValueError(f"ambiguous source declaration IDs: {path}:{name}")
            previous['kind'] = '+'.join(sorted((previous['kind'], kind)))
        else:
            declarations.append({"id": identity, "source_key": source_key, "name": name, "kind": kind,
                                 "offset": start, "line": source[:start].count(b"\n") + 1})
    declarations.sort(key=lambda entry: (entry["offset"], entry["name"]))
    # This source pin has no mutual declaration blocks. Do not silently apply
    # sequential-declaration reasoning to a future source that introduces one.
    if re.search(rb"(?m)^\s*with\s+[A-Za-z_][A-Za-z_0-9']*\s*[:({]", source):
        raise ValueError(f"mutual declaration block needs grouping support: {path}")
    if len({d["id"] for d in declarations}) != len(declarations):
        raise ValueError(f"ambiguous source declaration IDs: {path}")
    return declarations, sorted(imports)


def dependency_order(reference: Path, coqdep: str) -> tuple[list[str], dict[str, list[str]]]:
    paths = sorted(str(p.relative_to(reference)) for p in (reference / "src").rglob("*.v"))
    def invoke(*extra: str) -> str:
        result = subprocess.run([coqdep, *extra, "-R", "src", "Flocq", *paths],
                                cwd=reference, text=True, capture_output=True, timeout=120)
        if result.returncode or result.stderr.strip():
            raise ValueError(f"coqdep failed or warned: {result.stderr}")
        return result.stdout
    ordered = invoke("-sort").split()
    if len(ordered) != len(paths) or set(ordered) != set(paths):
        raise ValueError("coqdep sorted output omitted or duplicated source modules")
    dependencies = {}
    for line in invoke().splitlines():
        _, rhs = line.split(": ", 1)
        words = rhs.split()
        path = words[0]
        if path in dependencies or path not in paths:
            raise ValueError(f"unexpected dependency rule: {path}")
        dependencies[path] = sorted(str(Path(word).with_suffix(".v")) for word in words[1:]
                                    if word.endswith(".vo") and word.startswith("src/"))
    validate_order(ordered, dependencies)
    return ordered, dependencies


def validate_order(order: list[str], dependencies: dict[str, list[str]]) -> None:
    if len(order) != len(set(order)) or set(order) != set(dependencies):
        raise ValueError("dependency graph coverage mismatch")
    seen = set()
    for path in order:
        if not set(dependencies[path]) <= seen:
            raise ValueError(f"dependency not earlier in the queue (or cycle): {path}")
        seen.add(path)


def validate_reviews(inventory: dict, reviews: list[dict]) -> dict[str, dict]:
    lean = {d["name"]: d for d in inventory["declarations"]}
    by_id = {}
    for review in reviews:
        key = review["source_id"]
        if key in by_id or review["status"] not in STATES or not review.get("scope"):
            raise ValueError(f"invalid or duplicate manual review: {key}")
        if not review.get("evidence") or not all((ROOT / p).is_file() for p in review["evidence"]):
            raise ValueError(f"review without existing evidence: {key}")
        if not set(review["lean_names"]) <= lean.keys():
            raise ValueError(f"review points to absent compiled Lean declarations: {key}")
        current = {name: {field: lean[name][field] for field in
                         ('type_hash', 'value_hash', 'noncomputable')}
                   for name in review['lean_names']}
        if review.get('lean_fingerprints') != current:
            raise ValueError(f"compiled declaration changed since manual review: {key}")
        by_id[key] = review
    return by_id


def annotate(modules: list[dict], inventory: dict, reviews: list[dict]) -> None:
    by_id = validate_reviews(inventory, reviews)
    by_base, anchors = {}, {}
    for declaration in inventory['declarations']:
        name = declaration['name']
        by_base.setdefault(name.rsplit(".", 1)[-1], []).append(name)
    for ref in inventory["references"]:
        anchors.setdefault(f'{ref["path"]}:{ref["name"]}', []).append(ref["lean_name"])
    observed = set()
    for module in modules:
        for d in module["declarations"]:
            observed.add(d["id"])
            d["anchors"] = sorted(anchors.get(d.get("source_key", d["id"]), []))
            d["name_candidates"] = sorted(by_base.get(d["name"].rsplit(".", 1)[-1], []))
            d["review"] = by_id.get(d["id"])
            d["status"] = d["review"]["status"] if d["review"] else "unreviewed"
    if by_id.keys() - observed:
        raise ValueError(f"review IDs absent from pinned source: {sorted(by_id.keys() - observed)}")


def validate_compiled_anchors(modules: list[dict], references: list[dict]) -> None:
    sites = {(m['path'], d['line'], d['name']) for m in modules for d in m['declarations']}
    for ref in references:
        if (ref['path'], ref['line'], ref['name']) not in sites:
            raise ValueError(f"anchor does not name a compiled source declaration: {ref}")


def markdown(report: dict) -> str:
    lines = ["# Dependency-ordered Flocq review queue", "",
        f"Pinned source: `{report['flocq_commit']}`.", "",
        "Generated from actual `coqdep` dependencies and compiled `.glob` declaration offsets.",
        "Module dependencies come first; declarations within each module follow source order.",
        "Independent modules may be reviewed in parallel. Existing Lean names and source links",
        "are candidates, **not reviewed contracts**. Generated recursors, constructors, notations,",
        "and proof infrastructure are included, so totals are not a port-completion percentage.", "",
        "This queue's manual review manifest starts conservatively. Historical reviewed slices",
        "in SOURCE_CONTRACT_REVIEW.md are not automatically reclassified without precise entries.",
        "External Rocq imports are recorded in the JSON report, not counted as Flocq declarations.", "",
        "| Order | Source module | Declarations | Anchored | Name candidates | Reviewed |",
        "|---:|---|---:|---:|---:|---:|"]
    for index, module in enumerate(report["modules"], 1):
        ds = module["declarations"]
        lines.append(f"| {index} | {module['path']} | {len(ds)} | "
                     f"{sum(bool(d['anchors']) for d in ds)} | "
                     f"{sum(bool(d['name_candidates']) for d in ds)} | "
                     f"{sum(d['status'] != 'unreviewed' for d in ds)} |")
    pending = [(m, d) for m in report["modules"] for d in m["declarations"]
               if d["status"] == "unreviewed"]
    lines += ["", "## Next source-ordered checks", "",
              "Take the first outstanding contract, inspect its imported dependencies, compare",
              "the full Lean type/body with Rocq, and add an evidence-bearing review entry.",
              "Resolve aliases and generated proof infrastructure explicitly; do not create",
              "unnecessary numerical APIs to satisfy a raw name count.", ""]
    for m, d in pending[:20]:
        names = d["anchors"] or d["name_candidates"]
        candidate = ", ".join(f"`{n}`" for n in names[:3]) if names else "no exact-name candidate"
        if len(names) > 3:
            candidate += f" (+{len(names)-3} ambiguous candidates)"
        lines.append(f"- `{m['path']}:{d['line']}` — `{d['name']}` ({d['kind']}): {candidate}.")
    lines += ["", "## Reproduce", "", "```sh",
        "uv run scripts/flocq_port_queue.py --flocq-dir /path/to/pinned-built-flocq \\",
        "  --coqdep /path/to/coqdep --output /tmp/flocq-queue.json \\",
        "  --markdown /tmp/SOURCE_REVIEW_QUEUE.md", "```", "",
        "The generator checks the source pin, tracked-source cleanliness, every `.glob` digest,",
        "dependency precedence, source-anchor validity, manifest references, and a stable Lean",
        "source snapshot. It rejects unsupported mutual blocks rather than inventing their order.",
        "Manual reviews record Lean structural type/body hashes and the noncomputable flag.",
        "These detect direct-declaration drift, not changes hidden in transitive dependencies,",
        "and are noncryptographic change detectors, not semantic or security certificates.",
        "CI runs `uv run scripts/flocq_port_queue.py --check-lean-reviews --skip-build`.",
        "It does not infer semantic correspondence from matching names, compilation, or runtime tests.", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--flocq-dir", type=Path)
    parser.add_argument("--coqdep", default="coqdep")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--markdown", type=Path)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--check-lean-reviews", action="store_true",
                        help="compiler-backed review drift gate; no Rocq installation required")
    args = parser.parse_args()
    if not args.check_lean_reviews and (args.flocq_dir is None or args.output is None):
        parser.error("queue generation requires --flocq-dir and --output")
    reference = args.flocq_dir.resolve() if args.flocq_dir else None
    pin = (run(['git', 'rev-parse', 'HEAD:Deps/flocq']).strip() if args.check_lean_reviews
           else verify_reference(reference))
    snapshot = lean_source_fingerprint()
    if not args.skip_build:
        run(["lake", "build", "FloatSpec", "FloatSpec.src.IEEE754.ComputableCompare"], timeout=600)
    inventory = json.loads(run(["lake", "env", "lean", "scripts/ExportPortInventory.lean"], timeout=600))
    if inventory["flocq_commit"] != pin:
        raise ValueError("compiled Lean inventory and source pin differ")
    manifest = json.loads((ROOT / "FloatSpec/docs/source_review_queue.json").read_text())
    if manifest["flocq_commit"] != pin:
        raise ValueError("manual review source pin differs")
    if args.check_lean_reviews:
        validate_reviews(inventory, manifest['reviews'])
        require_lean_source_snapshot(snapshot)
        print(f"Compiled review drift gate passed: {len(manifest['reviews'])} manual source entries.")
        return
    errors = validate_references(inventory["references"], reference)
    if errors:
        raise ValueError("\n".join(errors))
    order, dependencies = dependency_order(reference, args.coqdep)
    modules = []
    for path in order:
        source = (reference / path).read_bytes()
        declarations, imports = parse_glob(source, (reference / path).with_suffix(".glob").read_text(), path)
        modules.append({"path": path, "source_sha256": hashlib.sha256(source).hexdigest(),
                        "dependencies": dependencies[path], "imports": imports,
                        "declarations": declarations})
    validate_compiled_anchors(modules, inventory['references'])
    annotate(modules, inventory, manifest["reviews"])
    require_lean_source_snapshot(snapshot)
    report = {"flocq_commit": pin, "lean_source_sha256": snapshot, "modules": modules,
              "counts": dict(Counter(d["status"] for m in modules for d in m["declarations"]))}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if args.markdown:
        args.markdown.write_text(markdown(report))
    print(f"Source queue: {len(modules)} modules; {report['counts']}; no equivalence percentage inferred.")


if __name__ == "__main__":
    main()
