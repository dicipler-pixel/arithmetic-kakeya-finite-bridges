# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* **No new Kakeya bound.** The Figure 3 family scores `7/4`; nothing here beats the `67/40` record.
* **The cut theorem is a necessary condition.** It rules configurations out; it does not build one.
  `KakeyaCut` formalizes the column-sum mechanism, not the whole iterative forcing process.
* **Earth–Moon.** The planar Euler bounds (`e ≤ 3N − 6` per layer) are explicit premises, because
  Mathlib has no planarity theory. The full biplanarity statement for `C₇[K₄]`, the all-`n`
  thickness theorem, the forest partitions and the SAT certificate are not formalized.
* **`AK_original.below_floor_excluded`** restates its own hypothesis; it records the
  bookkeeping step and carries no mathematical content of its own. The granularity and
  density theorems beside it are genuine.
* **Searches.** Search closures, enumeration counts and timing results in the paper are
  computations, not theorems, and are not formalized.
