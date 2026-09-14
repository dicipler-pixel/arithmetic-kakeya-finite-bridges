import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# The iterative arithmetic Kakeya cut obstruction

This development supplies the first-vertex/iteration bridge absent from the
original `KakeyaCut.lean`. Labels and forcing coefficients are integers.
Completion is reachability by the actual supported integer-witness rule.

The conclusion is an explicit pair of surviving labels with nonzero 2-by-2
determinant. This is the rank-two cut screen, and remains only necessary.
No local-seeding premise, constructibility grammar, or search completeness
assumption occurs in these theorems.
-/

open scoped BigOperators

namespace OperatorFirst.KakeyaCutCompletion

abbrev Label := ℤ × ℤ

def determinant (x y : Label) : ℤ := x.1 * y.2 - x.2 * y.1

def admissible (x : Label) : Prop := x.1 + x.2 ≠ 0

def determinantHom (x : Label) : Label →+ ℤ where
  toFun := determinant x
  map_zero' := by simp [determinant]
  map_add' y z := by simp [determinant]; ring

variable {V I : Type*}

def combination (G : Finset I) (rows : I → V → Label)
    (c : I → ℤ) (v : V) : Label := ∑ i ∈ G, c i • rows i v

def restriction (S : Finset V) (w : V → Label) : Label := ∑ v ∈ S, w v

theorem restriction_combination (S : Finset V) (G : Finset I)
    (rows : I → V → Label) (c : I → ℤ) :
    restriction S (combination G rows c) =
      ∑ i ∈ G, c i • restriction S (rows i) := by
  unfold restriction combination
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.smul_sum.symm

/-- One ordinary legal forcing move, using only the fixed generator rows.
The known sites may carry arbitrary slack. -/
def CanForce (G : Finset I) (rows : I → V → Label) (T : Set V) (e : V) : Prop :=
  ∃ (c : I → ℤ) (a : ℤ), a ≠ 0 ∧ combination G rows c e = (a, -a) ∧
    ∀ v, v ∉ T → v ≠ e → combination G rows c v = 0

/-- A finite legal forcing sequence from the initially known set. -/
inductive Reachable (G : Finset I) (rows : I → V → Label) (T₀ : Set V) :
    Set V → Prop
  | start : Reachable G rows T₀ T₀
  | step {T : Set V} {e : V} : Reachable G rows T₀ T → e ∉ T →
      CanForce G rows T e → Reachable G rows T₀ (insert e T)

def Completes (G : Finset I) (rows : I → V → Label) (T₀ : Set V) : Prop :=
  Reachable G rows T₀ Set.univ

/-- Before the first vertex of a cut is known, a forcing witness restricts to
a nonzero forbidden-direction vector on the whole cut. -/
theorem first_forcing_restriction (S : Finset V) (G : Finset I)
    (rows : I → V → Label) (T : Set V) (e : V)
    (hunknown : ∀ v ∈ S, v ∉ T) (he : e ∈ S) (hforce : CanForce G rows T e) :
    ∃ (c : I → ℤ) (a : ℤ), a ≠ 0 ∧
      (∑ i ∈ G, c i • restriction S (rows i)) = (a, -a) := by
  classical
  obtain ⟨c, a, ha, htarget, hzero⟩ := hforce
  refine ⟨c, a, ha, ?_⟩
  rw [← restriction_combination]
  change (∑ v ∈ S, combination G rows c v) = (a, -a)
  rw [Finset.sum_eq_single_of_mem e he]
  · exact htarget
  · intro v hv hve
    exact hzero v (hunknown v hv) hve

/-- The first forcing witness cannot be made from cut restrictions contained
in one admissible line. -/
theorem first_forcing_escapes_line (S : Finset V) (G : Finset I)
    (rows : I → V → Label) (T : Set V) (e : V) (q : Label)
    (hq : admissible q) (hunknown : ∀ v ∈ S, v ∉ T) (he : e ∈ S)
    (hforce : CanForce G rows T e) :
    ∃ i ∈ G, determinant q (restriction S (rows i)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨c, a, ha, hsum⟩ := first_forcing_restriction S G rows T e hunknown he hforce
  have hz : determinantHom q (∑ i ∈ G, c i • restriction S (rows i)) = 0 := by
    simp only [map_sum, map_zsmul]
    apply Finset.sum_eq_zero
    intro i hi
    change c i • determinant q (restriction S (rows i)) = 0
    rw [h i hi, smul_zero]
  rw [hsum] at hz
  have hprod : a * (q.1 + q.2) = 0 := by
    change q.1 * -a - q.2 * a = 0 at hz
    calc
      a * (q.1 + q.2) = -(q.1 * -a - q.2 * a) := by ring
      _ = 0 := by rw [hz, neg_zero]
  exact ((mul_ne_zero ha hq) hprod)

/-- A cut trapped in an admissible line stays entirely unknown under every
finite legal forcing sequence, even while vertices outside it are forced. -/
theorem line_cut_remains_unknown (S : Finset V) (G : Finset I)
    (rows : I → V → Label) (T₀ : Set V) (q : Label)
    (hq : admissible q) (hinitial : ∀ v ∈ S, v ∉ T₀)
    (hline : ∀ i ∈ G, determinant q (restriction S (rows i)) = 0)
    {T : Set V} (hreach : Reachable G rows T₀ T) :
    ∀ v ∈ S, v ∉ T := by
  induction hreach with
  | start => exact hinitial
  | @step T e hreach hnew hforce ih =>
      have henot : e ∉ S := by
        intro he
        obtain ⟨i, hi, hdet⟩ := first_forcing_escapes_line S G rows T e q hq ih he hforce
        exact hdet (hline i hi)
      intro v hv hmem
      rcases hmem with hve | hvT
      · exact henot (hve ▸ hv)
      · exact ih v hv hvT

/-- General iterative cut theorem, in line-exclusion form. -/
theorem completion_escapes_every_admissible_line (S : Finset V) (G : Finset I)
    (rows : I → V → Label) (T₀ : Set V) (q : Label)
    (hne : S.Nonempty) (hinitial : ∀ v ∈ S, v ∉ T₀)
    (hq : admissible q) (hcomplete : Completes G rows T₀) :
    ∃ i ∈ G, determinant q (restriction S (rows i)) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨v, hv⟩ := hne
  exact line_cut_remains_unknown S G rows T₀ q hq hinitial h hcomplete v hv (Set.mem_univ v)

/-- If every nonzero cut restriction is admissible, completion supplies an
explicit independent pair. Signed crossing labels satisfy this hypothesis. -/
theorem completion_has_independent_cut_rows (S : Finset V) (G : Finset I)
    (rows : I → V → Label) (T₀ : Set V)
    (hne : S.Nonempty) (hinitial : ∀ v ∈ S, v ∉ T₀)
    (hadmissible : ∀ i ∈ G, restriction S (rows i) ≠ 0 → admissible (restriction S (rows i)))
    (hcomplete : Completes G rows T₀) :
    ∃ i ∈ G, ∃ j ∈ G,
      determinant (restriction S (rows i)) (restriction S (rows j)) ≠ 0 := by
  obtain ⟨i, hi, hdet⟩ := completion_escapes_every_admissible_line S G rows T₀ (1, 0)
    hne hinitial (by unfold admissible; decide) hcomplete
  have hnz : restriction S (rows i) ≠ 0 := by
    intro hz
    apply hdet
    rw [hz]
    simp [determinant]
  obtain ⟨j, hj, hij⟩ := completion_escapes_every_admissible_line S G rows T₀
    (restriction S (rows i)) hne hinitial (hadmissible i hi hnz) hcomplete
  exact ⟨i, hi, j, hj, hij⟩

/-- The two permitted kinds of fixed integer generator rows. -/
inductive Generator (V : Type*)
  | site (vertex : V) (label : Label)
  | edge (source target : V) (label : Label)

def Generator.label : Generator V → Label
  | .site _ x => x
  | .edge _ _ x => x

def siteRow [DecidableEq V] (u : V) (x : Label) (v : V) : Label :=
  if v = u then x else 0

def Generator.row [DecidableEq V] : Generator V → V → Label
  | .site u x => siteRow u x
  | .edge u v x => fun w => siteRow u x w - siteRow v x w

/-- Site rows inside the cut have coefficient 1. Crossing edges have
coefficient 1 or -1; internal and exterior edges have coefficient 0. -/
def Generator.cutCoefficient [DecidableEq V] (S : Finset V) : Generator V → ℤ
  | .site u _ => if u ∈ S then 1 else 0
  | .edge u v _ => (if u ∈ S then 1 else 0) - (if v ∈ S then 1 else 0)

def Generator.Survives [DecidableEq V] (S : Finset V) (g : Generator V) : Prop :=
  g.cutCoefficient S ≠ 0

/-- Zero slots are allowed; every active label must avoid the target line. -/
def Generator.IsAdmissible (g : Generator V) : Prop :=
  g.label = 0 ∨ admissible g.label

theorem restriction_site [DecidableEq V] (S : Finset V) (u : V) (x : Label) :
    restriction S (siteRow u x) = if u ∈ S then x else 0 := by
  simp [restriction, siteRow]

theorem restriction_generator [DecidableEq V] (S : Finset V) (g : Generator V) :
    restriction S g.row = g.cutCoefficient S • g.label := by
  cases g with
  | site u x =>
      simp only [Generator.row, Generator.cutCoefficient, Generator.label, restriction_site]
      split <;> simp
  | edge u v x =>
      simp only [Generator.row, restriction, Finset.sum_sub_distrib]
      change restriction S (siteRow u x) - restriction S (siteRow v x) = _
      rw [restriction_site, restriction_site]
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
        simp [Generator.cutCoefficient, Generator.label, hu, hv]

theorem admissible_zsmul (k : ℤ) (x : Label) (hk : k ≠ 0) (hx : admissible x) :
    admissible (k • x) := by
  change k * x.1 + k * x.2 ≠ 0
  rw [← mul_add]
  exact mul_ne_zero hk hx

theorem restriction_generator_admissible [DecidableEq V] (S : Finset V)
    (g : Generator V) (hg : g.IsAdmissible) (hnz : restriction S g.row ≠ 0) :
    admissible (restriction S g.row) := by
  rw [restriction_generator] at hnz ⊢
  have hk : g.cutCoefficient S ≠ 0 := by
    intro hzero
    apply hnz
    rw [hzero, zero_smul]
  rcases hg with hz | had
  · exact False.elim (hnz (by rw [hz, smul_zero]))
  · exact admissible_zsmul _ _ hk had

theorem determinant_zsmul (k l : ℤ) (x y : Label) :
    determinant (k • x) (l • y) = k * l * determinant x y := by
  change (k * x.1) * (l * y.2) - (k * x.2) * (l * y.1) =
    k * l * (x.1 * y.2 - x.2 * y.1)
  ring

/-- Full general subset obstruction for site/edge forcing: every nonempty
initially unknown cut contains two independent surviving generator labels.
The nonzero determinant is an exact rank-two witness over ℚ. -/
theorem completion_has_independent_surviving_labels [DecidableEq V]
    (S : Finset V) (G : Finset I) (generators : I → Generator V) (T₀ : Set V)
    (hne : S.Nonempty) (hinitial : ∀ v ∈ S, v ∉ T₀)
    (hadmissible : ∀ i ∈ G, (generators i).IsAdmissible)
    (hcomplete : Completes G (fun i => (generators i).row) T₀) :
    ∃ i ∈ G, ∃ j ∈ G,
      (generators i).Survives S ∧ (generators j).Survives S ∧
      determinant (generators i).label (generators j).label ≠ 0 := by
  obtain ⟨i, hi, j, hj, hdet⟩ := completion_has_independent_cut_rows S G
    (fun i => (generators i).row) T₀ hne hinitial
    (fun i hi hnz => restriction_generator_admissible S (generators i) (hadmissible i hi) hnz)
    hcomplete
  rw [restriction_generator, restriction_generator, determinant_zsmul] at hdet
  refine ⟨i, hi, j, hj, ?_, ?_, ?_⟩
  · intro hz
    apply hdet
    rw [hz, zero_mul, zero_mul]
  · intro hz
    apply hdet
    rw [hz, mul_zero, zero_mul]
  · intro hz
    apply hdet
    rw [hz, mul_zero]

end OperatorFirst.KakeyaCutCompletion

#print axioms OperatorFirst.KakeyaCutCompletion.completion_has_independent_surviving_labels
