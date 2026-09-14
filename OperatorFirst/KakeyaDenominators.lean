import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Clearing denominators for finite arithmetic Kakeya forcing witnesses

An integer row system has a rational witness with prescribed zero coordinates
and a nonzero target coordinate exactly when it has an integer witness with
those properties. Clearing denominators scales the entire output by one
positive integer. It does not assert that the target coefficient is a unit.

The statements are independent of any particular Kakeya configuration or
search coverage. They supply the algebraic bridge from rational row reduction
to the challenge's integer, nonzero-multiple forcing rule.
-/

namespace OperatorFirst.KakeyaDenominators

open scoped BigOperators

section Denominators

variable {ι : Type*}

/-- A finite family of rational numbers has a common positive natural
denominator. We assert equality after casting, not integrality by rounding. -/
theorem finite_common_denominator (s : Finset ι) (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : ι → ℤ,
      ∀ i ∈ s, (z i : ℚ) = (D : ℚ) * c i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, Nat.zero_lt_one, fun _ => 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨D, hD, z, hz⟩ := ih
      refine ⟨(c a).den * D, Nat.mul_pos (c a).pos hD,
        fun i => if i = a then (c a).num * D else (c a).den * z i, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with hia | his
      · subst i
        simp only [ite_true, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
        rw [mul_assoc, mul_comm (D : ℚ) (c a), ← mul_assoc, Rat.den_mul_eq_num]
      · by_cases hia : i = a
        · subst i
          simp only [ite_true, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
          rw [mul_assoc, mul_comm (D : ℚ) (c a), ← mul_assoc, Rat.den_mul_eq_num]
        · simp only [if_neg hia, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
          rw [hz i his, mul_assoc]

/-- The same denominator clears every coordinate in a finite type. -/
theorem common_denominator [Fintype ι] (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : ι → ℤ,
      ∀ i, (z i : ℚ) = (D : ℚ) * c i := by
  obtain ⟨D, hD, z, hz⟩ := finite_common_denominator Finset.univ c
  exact ⟨D, hD, z, fun i => hz i (Finset.mem_univ i)⟩

end Denominators

section Rows

variable {ι κ : Type*} [Fintype ι]

/-- Linear combination of integer rows using rational coefficients. -/
def rationalRowCombination (A : ι → κ → ℤ) (c : ι → ℚ) (j : κ) : ℚ :=
  ∑ i, c i * (A i j : ℚ)

/-- Linear combination of the same integer rows using integer coefficients. -/
def integerRowCombination (A : ι → κ → ℤ) (z : ι → ℤ) (j : κ) : ℤ :=
  ∑ i, z i * A i j

/-- Casting an integer row combination agrees exactly with rational evaluation. -/
theorem cast_integerRowCombination (A : ι → κ → ℤ) (z : ι → ℤ) (j : κ) :
    (integerRowCombination A z j : ℚ) =
      rationalRowCombination A (fun i => (z i : ℚ)) j := by
  simp [integerRowCombination, rationalRowCombination]

/-- Common-denominator clearing scales every output coordinate by the same
positive integer, including all zero coordinates and the target coordinate. -/
theorem clear_row_denominators (A : ι → κ → ℤ) (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : ι → ℤ, ∀ j,
      (integerRowCombination A z j : ℚ) =
        (D : ℚ) * rationalRowCombination A c j := by
  obtain ⟨D, hD, z, hz⟩ := common_denominator c
  refine ⟨D, hD, z, ?_⟩
  intro j
  rw [cast_integerRowCombination]
  simp only [rationalRowCombination, hz, Finset.mul_sum, mul_assoc]

/-- Integer and rational forcing agree for arbitrary required zero coordinates.
The target output is required to be nonzero, not equal to one. -/
theorem rational_integer_witness_iff (A : ι → κ → ℤ) (zeroCoords : Set κ)
    (target : κ) :
    (∃ c : ι → ℚ,
      (∀ j ∈ zeroCoords, rationalRowCombination A c j = 0) ∧
      rationalRowCombination A c target ≠ 0) ↔
    (∃ z : ι → ℤ,
      (∀ j ∈ zeroCoords, integerRowCombination A z j = 0) ∧
      integerRowCombination A z target ≠ 0) := by
  constructor
  · rintro ⟨c, hzero, htarget⟩
    obtain ⟨D, hD, z, hz⟩ := clear_row_denominators A c
    have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
    refine ⟨z, ?_, ?_⟩
    · intro j hj
      have hcast : (integerRowCombination A z j : ℚ) = 0 := by
        rw [hz, hzero j hj, mul_zero]
      exact Int.cast_eq_zero.mp hcast
    · intro ht
      have hcast : (integerRowCombination A z target : ℚ) = 0 := by
        rw [ht, Int.cast_zero]
      rw [hz] at hcast
      exact (mul_ne_zero hDQ htarget) hcast
  · rintro ⟨z, hzero, htarget⟩
    refine ⟨fun i => (z i : ℚ), ?_, ?_⟩
    · intro j hj
      rw [← cast_integerRowCombination, hzero j hj, Int.cast_zero]
    · rw [← cast_integerRowCombination]
      exact Int.cast_ne_zero.mpr htarget

/-- In the forcing formulation, all coordinates outside the known set and
the target vanish; the target is an explicit nonzero integer multiple. -/
theorem forcing_nonzero_multiple_iff (A : ι → κ → ℤ) (known : Set κ)
    (target : κ) :
    (∃ c : ι → ℚ,
      (∀ j, j ∉ known → j ≠ target → rationalRowCombination A c j = 0) ∧
      rationalRowCombination A c target ≠ 0) ↔
    (∃ z : ι → ℤ, ∃ d : ℤ, d ≠ 0 ∧
      integerRowCombination A z target = d ∧
      ∀ j, j ∉ known → j ≠ target → integerRowCombination A z j = 0) := by
  have h := rational_integer_witness_iff A
    {j | j ∉ known ∧ j ≠ target} target
  simp only [Set.mem_ofPred_eq, and_imp] at h
  rw [h]
  constructor
  · rintro ⟨z, hz, ht⟩
    exact ⟨z, integerRowCombination A z target, ht, rfl, hz⟩
  · rintro ⟨z, d, hd, hzd, hz⟩
    exact ⟨z, hz, by simpa [hzd] using hd⟩

end Rows

section TwoCoordinates

variable {ι V : Type*} [Fintype ι]

/-- Pair-valued integer row evaluation is the pair of coordinate evaluations.
This identifies the coordinate convention with the legal-step pair convention. -/
theorem pair_row_sum_eq (A : ι → (V × Fin 2) → ℤ) (z : ι → ℤ) (v : V) :
    (∑ i, z i • (A i (v, 0), A i (v, 1))) =
      (integerRowCombination A z (v, 0), integerRowCombination A z (v, 1)) := by
  apply Prod.ext
  · simp [Prod.fst_sum, integerRowCombination]
  · simp [Prod.snd_sum, integerRowCombination]

/-- Rational relaxation of one legal forcing step. Both target coordinates
are specified: their values are a common nonzero multiple of `(1,-1)`. -/
def StepQ (A : ι → (V × Fin 2) → ℤ) (known : Set V) (target : V) : Prop :=
  ∃ c : ι → ℚ, ∃ a : ℚ, a ≠ 0 ∧
    rationalRowCombination A c (target, 0) = a ∧
    rationalRowCombination A c (target, 1) = -a ∧
    ∀ v, v ∉ known → v ≠ target → ∀ k,
      rationalRowCombination A c (v, k) = 0

/-- Integer legal forcing step, with an explicitly nonzero target multiple. -/
def StepZ (A : ι → (V × Fin 2) → ℤ) (known : Set V) (target : V) : Prop :=
  ∃ z : ι → ℤ, ∃ d : ℤ, d ≠ 0 ∧
    integerRowCombination A z (target, 0) = d ∧
    integerRowCombination A z (target, 1) = -d ∧
    ∀ v, v ∉ known → v ≠ target → ∀ k,
      integerRowCombination A z (v, k) = 0

/-- Clearing denominators preserves the full two-coordinate legal-step rule.
In particular, the two target outputs remain negatives of one another. -/
theorem stepQ_iff_stepZ (A : ι → (V × Fin 2) → ℤ) (known : Set V)
    (target : V) : StepQ A known target ↔ StepZ A known target := by
  constructor
  · rintro ⟨c, a, ha, h0, h1, hzero⟩
    obtain ⟨D, hD, z, hz⟩ := clear_row_denominators A c
    let d := integerRowCombination A z (target, 0)
    have hdcast : (d : ℚ) = (D : ℚ) * a := by
      change (integerRowCombination A z (target, 0) : ℚ) = _
      rw [hz, h0]
    have hDQ : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
    have hd : d ≠ 0 := by
      intro h
      have heq : (D : ℚ) * a = 0 := by simpa [h] using hdcast.symm
      exact (mul_ne_zero hDQ ha) heq
    refine ⟨z, d, hd, rfl, ?_, ?_⟩
    · have hcast : (integerRowCombination A z (target, 1) : ℚ) = -(d : ℚ) := by
        rw [hz, h1, hdcast, mul_neg]
      apply Rat.intCast_injective
      simpa only [Int.cast_neg] using hcast
    · intro v hv hvt k
      have hcast : (integerRowCombination A z (v, k) : ℚ) = 0 := by
        rw [hz, hzero v hv hvt k, mul_zero]
      exact Int.cast_eq_zero.mp hcast
  · rintro ⟨z, d, hd, h0, h1, hzero⟩
    refine ⟨fun i => (z i : ℚ), (d : ℚ), ?_, ?_, ?_, ?_⟩
    · exact Int.cast_ne_zero.mpr hd
    · rw [← cast_integerRowCombination, h0]
    · rw [← cast_integerRowCombination, h1, Int.cast_neg]
    · intro v hv hvt k
      rw [← cast_integerRowCombination, hzero v hv hvt k, Int.cast_zero]

end TwoCoordinates

end OperatorFirst.KakeyaDenominators

#print axioms OperatorFirst.KakeyaDenominators.finite_common_denominator
#print axioms OperatorFirst.KakeyaDenominators.common_denominator
#print axioms OperatorFirst.KakeyaDenominators.cast_integerRowCombination
#print axioms OperatorFirst.KakeyaDenominators.clear_row_denominators
#print axioms OperatorFirst.KakeyaDenominators.rational_integer_witness_iff
#print axioms OperatorFirst.KakeyaDenominators.forcing_nonzero_multiple_iff
#print axioms OperatorFirst.KakeyaDenominators.stepQ_iff_stepZ
#print axioms OperatorFirst.KakeyaDenominators.pair_row_sum_eq
