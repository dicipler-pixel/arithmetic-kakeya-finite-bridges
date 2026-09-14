import Mathlib.Algebra.Ring.Rat
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.NormNum

/-!
# Boundary controls for the arithmetic Kakeya bridge

These are proved counterexamples to two stronger statements that the new
bridge must never be used to infer. They are not search results or new
Kakeya constructions.
-/

namespace OperatorFirst.KakeyaAuditControls

/-- Denominator clearing does not preserve a primitive/unit target. -/
theorem rational_unit_without_integer_unit :
    (∃ q : ℚ, 2 * q = 1) ∧ ¬ (∃ z : ℤ, 2 * z = 1) := by
  constructor
  · exact ⟨1 / 2, by norm_num⟩
  · rintro ⟨z, hz⟩
    omega

/-- Equal image subspaces (hence equal ranks) do not determine the kernel. -/
theorem same_range_different_kernels :
    LinearMap.range (LinearMap.fst ℚ ℚ ℚ) =
      LinearMap.range (LinearMap.snd ℚ ℚ ℚ) ∧
    LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) ≠
      LinearMap.ker (LinearMap.snd ℚ ℚ ℚ) := by
  constructor
  · rw [Submodule.range_fst, Submodule.range_snd]
  · intro h
    have hmem : ((0, 1) : ℚ × ℚ) ∈ LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
      simp
    rw [h] at hmem
    simp at hmem

/-- A target can be detected on one kernel and vanish on another, even when
the constraint maps in the previous control have equal ranges. -/
theorem different_forcing_with_equal_range :
    (∃ w : ℚ × ℚ, w.2 = 0 ∧ w.1 ≠ 0) ∧
    ¬ (∃ w : ℚ × ℚ, w.1 = 0 ∧ w.1 ≠ 0) := by
  constructor
  · exact ⟨(1, 0), rfl, by norm_num⟩
  · rintro ⟨w, hw, hn⟩
    exact hn hw

end OperatorFirst.KakeyaAuditControls
