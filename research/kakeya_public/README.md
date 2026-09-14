# Finite arithmetic Kakeya proof supplement

This public-ready package contains two scoped formal results for a finite
two-coordinate integer-row model.

1. For a finite integer row system, rational and integer forcing witnesses are
   equivalent when the target may be any nonzero multiple of ((1,-1)).
2. If a fixed finite family of admissibly labelled site and edge rows completes
   by the stated forcing process, every nonempty finite cut that is initially
   unknown has two surviving labels with nonzero determinant.

The second statement is a necessary obstruction, not a sufficient condition.

## Included material

- Five final Lean modules: the two proofs, their representation adapter, and
  two boundary-control modules.
- A defining-module declaration audit.
- A public verification script and GitHub workflow.
- A checksum receipt for the exact source files.

The package intentionally excludes development history, mixer payloads,
intermediate drafts, unpublished search results, candidate constructions, and
unrelated research lanes. Those records are not included in this export.

## Verification

The project uses Lean 4.33.0 and the mathlib revision pinned by the repository.
Run:

```sh
lake exe cache get
python3 scripts/verify_kakeya_public.py
```

The gate builds all five modules, replays each through `leanchecker -v`,
audits declarations by defining module, permits only `propext`,
`Classical.choice`, and `Quot.sound`, and requires two deliberately false
boundary statements to be rejected for mathematical—not infrastructure—reasons.

## Scope

This is the nonzero-multiple operational forcing model. It does not establish
equivalence to a coefficient-one target rule. It proves no Kakeya exponent,
winning construction, exhaustive-search theorem, converse to the cut
obstruction, or analytic transport result.

The code is a downstream project using mathlib. It has not been accepted into
upstream mathlib.
