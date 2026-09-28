<div align="center">

# Arithmetic Kakeya — finite bridges in Lean

**Two machine-checked bridges for the Epoch FrontierMath arithmetic Kakeya problem: rational forcing equals integer forcing, and every completed configuration leaves two independent labels on every cut.**

[![Lean proof check](https://github.com/dicipler-pixel/arithmetic-kakeya-finite-bridges/actions/workflows/kakeya-public.yml/badge.svg)](https://github.com/dicipler-pixel/arithmetic-kakeya-finite-bridges/actions/workflows/kakeya-public.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
[![Full library check](https://github.com/dicipler-pixel/arithmetic-kakeya-finite-bridges/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/arithmetic-kakeya-finite-bridges/actions/workflows/build.yml)
![Theorems](https://img.shields.io/badge/theorems-127-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22812167-blue)](https://doi.org/10.5281/zenodo.22812167)

Jeromie Beasley

</div>

---

## The two results

**1. Clearing denominators.** For a finite system of integer rows, a rational
forcing witness exists exactly when an integer one does, with the same zero
pattern and a nonzero multiple of the target `(1, −1)`. Rational row reduction
can therefore be trusted to decide the challenge's integer forcing step.
(`KakeyaDenominators.rational_integer_witness_iff`,
`KakeyaForcingBridge.canForce_iff_stepZ`, `canForce_iff_stepQ`)

**2. The cut obstruction.** If a finite family of admissibly labelled site and
edge rows completes under the forcing process, then every nonempty finite cut
that starts unknown keeps two surviving labels whose 2 × 2 determinant is
nonzero. (`KakeyaCutCompletion.completion_has_independent_surviving_labels`)

Result 2 is a **necessary** condition, a screen that rules configurations out.
It is not sufficient to build one.

## What is in the repository

| File | Theorems | What it does |
| :--- | :-: | :--- |
| [`KakeyaDenominators.lean`](OperatorFirst/KakeyaDenominators.lean) | 8 | Common denominators; rational and integer witnesses are equivalent |
| [`KakeyaForcingBridge.lean`](OperatorFirst/KakeyaForcingBridge.lean) | 5 | Connects pair-valued rows to coordinate rows, so the two forcing conventions agree |
| [`KakeyaCutCompletion.lean`](OperatorFirst/KakeyaCutCompletion.lean) | 12 | The iterative cut obstruction: completion escapes every admissible line |
| [`KakeyaAuditControls.lean`](OperatorFirst/KakeyaAuditControls.lean) | 3 | Proved counterexamples to two stronger statements the bridge must never be used for |
| [`KakeyaCutAssumptionControl.lean`](OperatorFirst/KakeyaCutAssumptionControl.lean) | 5 | Shows the admissibility hypothesis cannot be dropped |
| | **33** | |

## The wider library: forcing, the Figure 3 family, and Earth–Moon

Nine more modules, 94 theorems, carry the rest of the paper's finite mathematics. They were
first checked in the research repository and are copied here byte for byte.

| File | Theorems | What it does |
| :--- | :-: | :--- |
| [`KakeyaCut.lean`](OperatorFirst/KakeyaCut.lean) | 9 | The column-sum mechanism of the cut theorem: restriction, internal cancellation, the rank-one obstruction |
| [`KakeyaForcingLinear.lean`](OperatorFirst/KakeyaForcingLinear.lean) | 10 | Exact forcing criteria: forcing iff the kernel is not contained in the target's, dual certificates, presentation invariance, the projector test |
| [`KakeyaSeedingControl.lean`](OperatorFirst/KakeyaSeedingControl.lean) | 11 | A complete forcing sequence on the paper's own Figure 3 that refutes the seeding lemma as first stated |
| [`KakeyaAtlasFamily.lean`](OperatorFirst/KakeyaAtlasFamily.lean) | 18 | The Figure 3 family with edge label `(1, q)`: it completes exactly at `q = 2`, with score `7/4` |
| [`KakeyaAtlasProjector.lean`](OperatorFirst/KakeyaAtlasProjector.lean) | 16 | The exact rational rank-one projector `ccᵀ/13` onto the first forcing kernel at `q = 2` |
| [`KakeyaExtension.lean`](OperatorFirst/KakeyaExtension.lean) | 5 | Products add density exactly, so a positive density eventually exceeds any bound |
| [`AK_original.lean`](MixedIntake/AK_original.lean) | 7 | Score granularity (the `67/40` record and the `5/3` ceiling below denominator 40) and density additivity |
| [`RestrictionBridge.lean`](OperatorFirst/RestrictionBridge.lean) | 5 | Restriction identities shared by both obstructions: internal flux cancels, capacity transfers |
| [`EarthMoon.lean`](OperatorFirst/EarthMoon.lean) | 13 | `C₇[K₄]`: triangle-free joins, 112 join and 154 host edges, a proper 10-colouring, and the two-layer capacity obstruction with the planar Euler bounds as stated premises |
| | **94** | |

This wider library is checked by [a second workflow](.github/workflows/build.yml): every module
builds against Lean v4.33.0 and Mathlib v4.33.0, is replayed in the kernel checker, and every
theorem is axiom-audited; three false statements (an integer unit for 2, equal kernels for maps
with equal range, a host graph failing the Euler count) must be rejected.

## How it is checked

Every push runs [the proof check](.github/workflows/kakeya-public.yml):

1. every module builds against Lean v4.33.0 and the pinned Mathlib;
2. every module is replayed in the independent kernel checker (`leanchecker`);
3. every declaration is audited by defining module and may depend only on
   `propext`, `Classical.choice` and `Quot.sound`;
4. two deliberately false boundary statements must be rejected, for a
   mathematical reason and not a build error.

To run it yourself with Lean installed:

```bash
lake exe cache get
python3 scripts/verify_kakeya_public.py
```

## Scope

These results use the nonzero-multiple forcing model. They do not show
equivalence to a coefficient-one target rule, and they prove no Kakeya
exponent, winning construction, exhaustive-search theorem, converse to the cut
obstruction, or analytic transport result. The Epoch problem is not claimed
solved. The full scope note is in
[`research/kakeya_public/README.md`](research/kakeya_public/README.md).

## The paper

*Certified Obstructions and Exact Forcing: Earth–Moon Graph Coloring and
Arithmetic Kakeya*, Jeromie Beasley, Version 2 (2026).
DOI [10.5281/zenodo.22812167](https://doi.org/10.5281/zenodo.22812167).
Manuscript and full reproduction supplement:
[earth-moon-kakeya-certificates](https://github.com/dicipler-pixel/earth-moon-kakeya-certificates).

## Citation

Citation metadata is in [`CITATION.cff`](CITATION.cff). The code is a
downstream project using Mathlib; it has not been accepted into upstream
Mathlib.

---

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text: [CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md).
