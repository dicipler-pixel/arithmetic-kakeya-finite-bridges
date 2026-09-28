import Mathlib

/-!
Countercontrol to Lemma 4 in arithmetic_kakeya_full_v2.pdf, page 4.
The rows are the paper's own Appendix A.1 Figure 3, pages 12-13.
Vertices 0,1,2,3 are g4,g1,g3,g2. Edge rows come first, then generators
(1,1) at g1, (1,1) at g2, (0,1) at g4. All initial vertex sites differ.
The exact integer combinations below implement the stated forcing rule.
No claim of a new Kakeya bound: score is the known 7/4.
-/
open scoped BigOperators
namespace OperatorFirst.KakeyaSeedingControl

def rows : Fin 7 → Fin 8 → ℤ := ![
  ![1,0,0,0,-1,0,0,0],
  ![0,0,1,0,0,0,-1,0],
  ![1,2,-1,-2,0,0,0,0],
  ![0,0,0,0,0,1,0,-1],
  ![0,0,1,1,0,0,0,0],
  ![0,0,0,0,0,0,1,1],
  ![0,1,0,0,0,0,0,0]]

def coeff₁ : Fin 7 → ℤ := ![-1,-1,1,-1,2,-1,-2]
def coeff₂ : Fin 7 → ℤ := ![3,1,-1,1,-2,1,0]
def coeff₃ : Fin 7 → ℤ := ![0,0,2,0,3,0,0]
def coeff₄ : Fin 7 → ℤ := ![0,-1,0,1,0,0,0]
def combine (c : Fin 7 → ℤ) (j : Fin 8) : ℤ := ∑ i, c i * rows i j
def coord (v : Fin 4) (b : Fin 2) : Fin 8 := ⟨2*v.val+b.val, by omega⟩

def Step (c : Fin 7 → ℤ) (T : Finset (Fin 4)) (e : Fin 4) : Prop :=
  combine c (coord e 0) ≠ 0 ∧
  combine c (coord e 0) + combine c (coord e 1) = 0 ∧
  ∀ v : Fin 4, v ∉ T → v ≠ e →
    combine c (coord v 0) = 0 ∧ combine c (coord v 1) = 0
instance (c : Fin 7 → ℤ) (T : Finset (Fin 4)) (e : Fin 4) : Decidable (Step c T e) :=
  inferInstanceAs (Decidable (combine c (coord e 0) ≠ 0 ∧
    combine c (coord e 0) + combine c (coord e 1) = 0 ∧
    ∀ v : Fin 4, v ∉ T → v ≠ e →
      combine c (coord v 0) = 0 ∧ combine c (coord v 1) = 0))

theorem first_witness : combine coeff₁ = ![0,0,0,0,1,-1,0,0] := by
  funext j
  fin_cases j <;> norm_num [combine, coeff₁, rows, Fin.sum_univ_succ]

theorem first_step : Step coeff₁ ∅ 2 := by decide
theorem second_step : Step coeff₂ {2} 0 := by decide
theorem third_step : Step coeff₃ {2,0} 1 := by decide
theorem fourth_step : Step coeff₄ {2,0,1} 3 := by decide

def initialSites : Fin 3 → Fin 4 := ![1,3,0]
theorem distinct_initial_sites : Function.Injective initialSites := by decide
theorem first_vertex_has_no_generator : ∀ i, initialSites i ≠ 2 := by decide

theorem complete_forcing_sequence :
    Step coeff₁ ∅ 2 ∧ Step coeff₂ {2} 0 ∧
    Step coeff₃ {2,0} 1 ∧ Step coeff₄ {2,0,1} 3 :=
  ⟨first_step,second_step,third_step,fourth_step⟩

theorem seeding_claim_counterexample :
    Step coeff₁ ∅ 2 ∧ (∀ i, initialSites i ≠ 2) ∧ Function.Injective initialSites :=
  ⟨first_step,first_vertex_has_no_generator,distinct_initial_sites⟩

theorem labels_admissible :
    (1 : ℤ)+0 ≠ 0 ∧ (1 : ℤ)+2 ≠ 0 ∧ (0 : ℤ)+1 ≠ 0 ∧ (1 : ℤ)+1 ≠ 0 := by decide

/-- Combinatorial counts for six sites and seven distinct labels. This counts
candidate sets, not completing objects. Independent pairs are automatic only
for the paper's particular seven pairwise nonparallel labels. -/
theorem missing_distributed_pattern_counts :
    Nat.choose 42 3 = 11480 ∧
    Nat.choose 6 3 * 7^3 = 6860 ∧
    6 * Nat.choose 7 2 * 5 * 7 = 4410 ∧
    6 * Nat.choose 7 3 = 210 ∧
    6860+4410+210=11480 := by decide

end OperatorFirst.KakeyaSeedingControl
#print axioms OperatorFirst.KakeyaSeedingControl.first_witness
#print axioms OperatorFirst.KakeyaSeedingControl.first_step
#print axioms OperatorFirst.KakeyaSeedingControl.second_step
#print axioms OperatorFirst.KakeyaSeedingControl.third_step
#print axioms OperatorFirst.KakeyaSeedingControl.fourth_step
#print axioms OperatorFirst.KakeyaSeedingControl.distinct_initial_sites
#print axioms OperatorFirst.KakeyaSeedingControl.first_vertex_has_no_generator
#print axioms OperatorFirst.KakeyaSeedingControl.complete_forcing_sequence
#print axioms OperatorFirst.KakeyaSeedingControl.seeding_claim_counterexample
#print axioms OperatorFirst.KakeyaSeedingControl.labels_admissible
#print axioms OperatorFirst.KakeyaSeedingControl.missing_distributed_pattern_counts
