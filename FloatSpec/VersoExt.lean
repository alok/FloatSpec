import FloatSpecRoles

/-!
FloatSpec documentation extension hooks.

The Flocq docstring extensions live in `FloatSpecRoles` and use Lean's built-in Verso
docstrings (no external Verso package): the `{coq}` and `{coq_file}` roles cite and link the
pinned Flocq source, and `coq` code blocks quote it verbatim. A declaration opts in with
`set_option doc.verso true in`; see `scripts/fixtures/CoqDocRole.lean` for examples.
This module re-exports them for files that import `FloatSpec.VersoExt`.
-/
