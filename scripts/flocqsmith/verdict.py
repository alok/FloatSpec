"""The closed verdict taxonomy and the pure judge (FLOCQSMITH.md §7).

Each (case, clone path) pair gets exactly one verdict, judged against the
``rocq-vm`` reference. The judge is a pure function of the parsed path
outcomes, so ``verify`` can recompute every verdict offline from retained raw
streams. ``match`` is produced in exactly two places: both documents decoded
against the signature and are equal, or the kernel accepted the reference
values. Every other outcome, including every infrastructure failure, is a
non-match.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from .observe import DecodeError, decode, first_divergence, flatten

CLONE_PATHS = ("lean-meta", "lean-ir", "lean-kernel")
REFERENCE_PATH = "rocq-vm"

VERDICTS = ("match", "observation-mismatch", "reference-infra-failure", "clone-infra-failure",
            "both-infra-failure", "harness-error")

# Outcome statuses a path parser may report.
STATUSES = ("ok", "infra", "harness", "kernel-true", "kernel-false", "not-run")

# Closed infrastructure stages. ``lean-elab:<kind>`` carries the JSON message
# kind. ``process-crash`` (a Lean process died without per-case attribution on
# the meta or kernel paths) is an addition to the §7 list.
STAGES = frozenset({"noncomputable", "meta-stuck", "heartbeats", "max-recdepth", "ir-panic", "ir-crash",
                    "kernel-stuck", "timeout", "process-crash"})


def valid_stage(stage: str) -> bool:
    return stage in STAGES or (stage.startswith("lean-elab:") and len(stage) > len("lean-elab:"))


@dataclass(frozen=True)
class Outcome:
    """One path's parsed result for one case."""

    status: str
    stage: str | None = None
    document: tuple[int, ...] | None = None
    detail: str = ""

    def __post_init__(self) -> None:
        if self.status not in STATUSES:
            raise ValueError(f"unknown status {self.status}")
        if (self.status == "infra") != (self.stage is not None):
            raise ValueError("infra outcomes, and only they, carry a stage")
        if self.stage is not None and not valid_stage(self.stage):
            raise ValueError(f"stage {self.stage} is outside the closed set")
        if (self.status == "ok") != (self.document is not None):
            raise ValueError("ok outcomes, and only they, carry a document")

    def to_json(self) -> dict[str, object]:
        row: dict[str, object] = {"status": self.status}
        if self.stage is not None:
            row["stage"] = self.stage
        if self.document is not None:
            row["document"] = list(self.document)
        if self.detail:
            row["detail"] = self.detail
        return row

    @staticmethod
    def from_json(row: Mapping[str, object]) -> "Outcome":
        document = row.get("document")
        stage = row.get("stage")
        return Outcome(str(row["status"]), None if stage is None else str(stage),
                       tuple(int(n) for n in document) if isinstance(document, list) else None,
                       str(row.get("detail", "")))


@dataclass(frozen=True)
class Verdict:
    path: str
    verdict: str
    stage: str | None = None
    divergence: dict[str, object] | None = None
    detail: str = ""

    def __post_init__(self) -> None:
        if self.verdict not in VERDICTS:
            raise ValueError(f"unknown verdict {self.verdict}")
        if self.path not in CLONE_PATHS:
            raise ValueError(f"unknown clone path {self.path}")

    def to_json(self) -> dict[str, object]:
        row: dict[str, object] = {"path": self.path, "verdict": self.verdict}
        if self.stage is not None:
            row["stage"] = self.stage
        if self.divergence is not None:
            row["divergence"] = self.divergence
        if self.detail:
            row["detail"] = self.detail
        return row


def judge(signature: dict[str, object], path: str, reference: Outcome, clone: Outcome) -> Verdict:
    """Classify one clone path's outcome against the reference outcome."""
    if reference.status == "harness" or clone.status == "harness":
        return Verdict(path, "harness-error", detail=(reference.detail or clone.detail))
    if reference.status == "infra":
        if clone.status == "infra":
            return Verdict(path, "both-infra-failure", stage=clone.stage, detail=reference.detail)
        return Verdict(path, "reference-infra-failure", detail=reference.detail)
    if reference.status != "ok" or reference.document is None:
        return Verdict(path, "harness-error", detail=f"reference status {reference.status}")
    try:
        ref_values = decode(signature, reference.document)
    except DecodeError as error:
        return Verdict(path, "harness-error", detail=f"reference document invalid: {error}")
    if clone.status == "infra":
        return Verdict(path, "clone-infra-failure", stage=clone.stage, detail=clone.detail)
    if path == "lean-kernel":
        if clone.status == "kernel-true":
            return Verdict(path, "match")
        if clone.status == "kernel-false":
            return Verdict(path, "observation-mismatch", detail="decide +kernel: proposition is false")
        return Verdict(path, "harness-error", detail=f"kernel status {clone.status}")
    if clone.status != "ok" or clone.document is None:
        return Verdict(path, "harness-error", detail=f"{path} status {clone.status}")
    try:
        clone_values = decode(signature, clone.document)
    except DecodeError as error:
        return Verdict(path, "harness-error", detail=f"{path} document invalid: {error}")
    divergent = first_divergence(ref_values, clone_values)
    if divergent is None:
        return Verdict(path, "match")
    clone_by_id = {v.id: v for v in flatten(clone_values)}
    return Verdict(path, "observation-mismatch", divergence={
        "id": divergent.id, "op": divergent.op, "type": divergent.type,
        "reference": list(divergent.value), "clone": list(clone_by_id[divergent.id].value)})


def meta_ir_disagreement(signature: dict[str, object], meta: Outcome, ir: Outcome) -> bool:
    """Both Lean evaluators produced valid, different documents (§7)."""
    if meta.status != "ok" or ir.status != "ok" or meta.document is None or ir.document is None:
        return False
    try:
        decode(signature, meta.document)
        decode(signature, ir.document)
    except DecodeError:
        return False
    return meta.document != ir.document
