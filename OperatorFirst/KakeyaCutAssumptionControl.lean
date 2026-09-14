import OperatorFirst.KakeyaCutCompletion

/-!
# An essential-assumption control for the iterative cut theorem

One site carrying the forbidden label `(1,-1)` forces its unique vertex
immediately. Its labels cannot have rank two. This is an intentional
out-of-domain control: it proves the admissibility hypothesis cannot be
dropped. It is not a legal arithmetic Kakeya construction.
-/

namespace OperatorFirst.KakeyaCutAssumptionControl

open OperatorFirst.KakeyaCutCompletion

def singletonGenerators : Finset Unit := {()}

def forbiddenGenerator (_ : Unit) : Generator Unit :=
  .site () (1, -1)

theorem forbidden_label_not_admissible :
    ¬ (forbiddenGenerator ()).IsAdmissible := by
  simp [forbiddenGenerator, Generator.IsAdmissible, Generator.label, admissible]

theorem forbidden_singleton_can_force :
    CanForce singletonGenerators (fun i => (forbiddenGenerator i).row) ∅ () := by
  refine ⟨fun _ => 1, 1, by decide, ?_, ?_⟩
  · simp [combination, singletonGenerators, forbiddenGenerator, Generator.row, siteRow]
  · intro v hv hne
    cases v
    exact False.elim (hne rfl)

theorem forbidden_singleton_completes :
    Completes singletonGenerators (fun i => (forbiddenGenerator i).row) ∅ := by
  have hreach : Reachable singletonGenerators (fun i => (forbiddenGenerator i).row)
      ∅ (insert () ∅) :=
    Reachable.step Reachable.start (by simp) forbidden_singleton_can_force
  have hall : (insert () (∅ : Set Unit)) = Set.univ := by
    ext v
    cases v
    simp
  rw [hall] at hreach
  exact hreach

theorem forbidden_singleton_determinants_zero (i j : Unit) :
    determinant (forbiddenGenerator i).label (forbiddenGenerator j).label = 0 := by
  simp [forbiddenGenerator, Generator.label, determinant]

theorem forbidden_singleton_has_no_independent_labels :
    ¬ ∃ i ∈ singletonGenerators, ∃ j ∈ singletonGenerators,
      determinant (forbiddenGenerator i).label (forbiddenGenerator j).label ≠ 0 := by
  rintro ⟨i, hi, j, hj, hdet⟩
  exact hdet (forbidden_singleton_determinants_zero i j)

end OperatorFirst.KakeyaCutAssumptionControl

#print axioms OperatorFirst.KakeyaCutAssumptionControl.forbidden_singleton_completes
#print axioms OperatorFirst.KakeyaCutAssumptionControl.forbidden_singleton_has_no_independent_labels
