"""flocqsmith: generated Flocq programs for differential conformance testing.

Design: FloatSpec/docs/FLOCQSMITH.md. The generator emits small straight-line
programs over the executable BinarySingleNaN API that are valid by
construction, renders each program once in Rocq and once in Lean, and judges
every observed binding of every Lean execution path against pinned Rocq
``vm_compute``. Agreement is finite testing, not a proof of equivalence.

Modules:

- ``choose``: the single choice primitive and the replayable draw tape.
- ``formats``: format parameters and the boundary value catalogue.
- ``table``: the signature table (the one source of truth for both renderers).
- ``ir``: the typed SSA program, its JSON form, type checking and the
  observation signature.
- ``cost``: the emission-time cost model and batch packing.
- ``generate``: the program generator.
- ``render``: Lean and Rocq renderings, including planted-defect variants.
- ``mutants``: positive controls (planted defects and encoder mutations).
- ``observe``: typed decoding and validation of observation documents.
- ``verdict``: the closed verdict taxonomy and the pure judge.
- ``numeric``: exact-rational numeric tags (a separate axis; never votes).
- ``process``: subprocess execution that reports instead of raising.
- ``harness``: batch emission, execution and per-case attribution.
- ``shrink``: verdict-preserving program minimization.
- ``campaign``: campaigns, controls, replay, staging, manifests and reports.
"""

from __future__ import annotations

SCHEMA_CASE = "flocqsmith-case-v1"
SCHEMA_IR = "flocqsmith-ir-v1"
SCHEMA_OBSERVATION = "flocqsmith-observation-v1"
SCHEMA_REPORT = "flocqsmith-report-v1"
