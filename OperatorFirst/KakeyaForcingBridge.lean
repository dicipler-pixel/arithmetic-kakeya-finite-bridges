import OperatorFirst.KakeyaCutCompletion
import OperatorFirst.KakeyaDenominators

/-!
# Exact bridge between the integer legal step and its rational relaxation

Only the rows in `G` are retained, by indexing them with the finite subtype
`G`. Pair-valued rows and two-coordinate rows are identified explicitly.
Restriction and zero-extension of coefficients connect the two conventions.
-/

namespace OperatorFirst.KakeyaForcingBridge

open scoped BigOperators
open KakeyaCutCompletion KakeyaDenominators

variable {I V : Type*}

/-- The same active pair-valued rows, with finite row indices and explicit
coordinate indices. This introduces no new rows or label values. -/
def coordinateRows (G : Finset I) (rows : I → V → ℤ × ℤ) :
    G → (V × Fin 2) → ℤ :=
  fun i p => if p.2 = 0 then (rows i.val p.1).1 else (rows i.val p.1).2

/-- Restricting coefficients to the active rows preserves their full output. -/
theorem combination_eq_coordinate_sums (G : Finset I) (rows : I → V → ℤ × ℤ)
    (c : I → ℤ) (v : V) :
    combination G rows c v =
      (integerRowCombination (coordinateRows G rows) (fun i => c i.val) (v, 0),
       integerRowCombination (coordinateRows G rows) (fun i => c i.val) (v, 1)) := by
  rw [combination, ← Finset.sum_coe_sort G (fun i => c i • rows i v)]
  simpa [coordinateRows] using
    pair_row_sum_eq (coordinateRows G rows) (fun i => c i.val) v

/-- Coefficients outside the active set may be set to zero. -/
noncomputable def extendCoefficients (G : Finset I) (z : G → ℤ) : I → ℤ := by
  classical
  exact fun i => if hi : i ∈ G then z ⟨i, hi⟩ else 0

theorem extendCoefficients_apply (G : Finset I) (z : G → ℤ) (i : G) :
    extendCoefficients G z i.val = z i := by
  simp [extendCoefficients, i.property]

/-- Zero-extension from the finite subtype also preserves the full output. -/
theorem extended_combination_eq_coordinate_sums (G : Finset I)
    (rows : I → V → ℤ × ℤ) (z : G → ℤ) (v : V) :
    combination G rows (extendCoefficients G z) v =
      (integerRowCombination (coordinateRows G rows) z (v, 0),
       integerRowCombination (coordinateRows G rows) z (v, 1)) := by
  simpa only [extendCoefficients_apply] using
    combination_eq_coordinate_sums G rows (extendCoefficients G z) v

/-- The pair-valued legal integer step is exactly the two-coordinate step. -/
theorem canForce_iff_stepZ (G : Finset I) (rows : I → V → ℤ × ℤ)
    (known : Set V) (target : V) :
    CanForce G rows known target ↔ StepZ (coordinateRows G rows) known target := by
  constructor
  · rintro ⟨c, a, ha, ht, hz⟩
    refine ⟨fun i => c i.val, a, ha, ?_, ?_, ?_⟩
    · have h := (combination_eq_coordinate_sums G rows c target).symm.trans ht
      exact congrArg Prod.fst h
    · have h := (combination_eq_coordinate_sums G rows c target).symm.trans ht
      exact congrArg Prod.snd h
    · intro v hv hvt
      have h := (combination_eq_coordinate_sums G rows c v).symm.trans (hz v hv hvt)
      exact Fin.forall_fin_two.mpr ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨z, d, hd, h0, h1, hz⟩
    refine ⟨extendCoefficients G z, d, hd, ?_, ?_⟩
    · rw [extended_combination_eq_coordinate_sums]
      exact Prod.ext h0 h1
    · intro v hv hvt
      rw [extended_combination_eq_coordinate_sums]
      exact Prod.ext (hz v hv hvt 0) (hz v hv hvt 1)

/-- The actual legal integer step and rational row-linear-algebra step agree.
This equivalence preserves the nonzero-multiple rule and both target signs. -/
theorem canForce_iff_stepQ (G : Finset I) (rows : I → V → ℤ × ℤ)
    (known : Set V) (target : V) :
    CanForce G rows known target ↔ StepQ (coordinateRows G rows) known target :=
  (canForce_iff_stepZ G rows known target).trans
    (stepQ_iff_stepZ (coordinateRows G rows) known target).symm

end OperatorFirst.KakeyaForcingBridge

#print axioms OperatorFirst.KakeyaForcingBridge.combination_eq_coordinate_sums
#print axioms OperatorFirst.KakeyaForcingBridge.extendCoefficients_apply
#print axioms OperatorFirst.KakeyaForcingBridge.extended_combination_eq_coordinate_sums
#print axioms OperatorFirst.KakeyaForcingBridge.canForce_iff_stepZ
#print axioms OperatorFirst.KakeyaForcingBridge.canForce_iff_stepQ
