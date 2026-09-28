import Mathlib

/-! The actual column-sum mechanism of Theorem 2 in arithmetic_kakeya_full_v2.pdf.
This formalizes generator restriction, internal cancellation, combination
linearity and the rank-one obstruction, not the whole iterative forcing process. -/
open scoped BigOperators
namespace OperatorFirst.KakeyaCut
abbrev Label := ℤ × ℤ

def site {V : Type*} [DecidableEq V] (g : V) (x : Label) (v : V) : Label :=
  if v=g then x else 0
def edge {V : Type*} [DecidableEq V] (u v : V) (x : Label) (i : V) : Label :=
  site u x i - site v x i

theorem site_restriction {V : Type*} [DecidableEq V]
    (S : Finset V) (g : V) (x : Label) :
    (∑ i ∈ S, site g x i) = if g ∈ S then x else 0 := by simp [site]

theorem edge_restriction {V : Type*} [DecidableEq V]
    (S : Finset V) (u v : V) (x : Label) :
    (∑ i ∈ S, edge u v x i) =
      (if u ∈ S then x else 0) - (if v ∈ S then x else 0) := by
  simp only [edge, Finset.sum_sub_distrib]
  rw [site_restriction,site_restriction]

theorem internal_edge_cancels {V : Type*} [DecidableEq V]
    (S : Finset V) (u v : V) (x : Label) (hu : u ∈ S) (hv : v ∈ S) :
    (∑ i ∈ S, edge u v x i) = 0 := by
  rw [edge_restriction, if_pos hu, if_pos hv, sub_self]

theorem exterior_edge_cancels {V : Type*} [DecidableEq V]
    (S : Finset V) (u v : V) (x : Label) (hu : u ∉ S) (hv : v ∉ S) :
    (∑ i ∈ S, edge u v x i) = 0 := by
  rw [edge_restriction, if_neg hu, if_neg hv, sub_self]

theorem entering_edge_survives {V : Type*} [DecidableEq V]
    (S : Finset V) (u v : V) (x : Label) (hu : u ∈ S) (hv : v ∉ S) :
    (∑ i ∈ S, edge u v x i) = x := by
  rw [edge_restriction, if_pos hu, if_neg hv, sub_zero]

theorem restriction_of_integer_combination {V I : Type*}
    (S : Finset V) (G : Finset I) (c : I → ℤ) (w : I → V → Label) :
    (∑ v ∈ S, ∑ g ∈ G, c g • w g v) =
      ∑ g ∈ G, c g • (∑ v ∈ S, w g v) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  exact Finset.smul_sum.symm

theorem first_vertex_restriction {V : Type*} [DecidableEq V]
    (S : Finset V) (e : V) (w : V → Label) (he : e ∈ S)
    (hzero : ∀ v ∈ S, v ≠ e → w v = 0) :
    (∑ v ∈ S, w v) = w e := by
  exact Finset.sum_eq_single_of_mem e he hzero

/-- A nonzero forbidden vector and any admissible label have nonzero determinant. -/
theorem forbidden_admissible_determinant (a b c : ℤ)
    (ha : a ≠ 0) (hs : b+c ≠ 0) : a*c-(-a)*b ≠ 0 := by
  have h : a*c-(-a)*b = a*(b+c) := by ring
  rw [h]
  exact mul_ne_zero ha hs

/-- Rational rank-one span cannot contain a nonzero forbidden vector. -/
theorem forbidden_not_rank_one (a b c k : ℚ)
    (ha : a ≠ 0) (hs : b+c ≠ 0) : ¬ (a=k*b ∧ -a=k*c) := by
  rintro ⟨h₁,h₂⟩
  have h : k*(b+c)=0 := by nlinarith
  have hk : k=0 := (mul_eq_zero.mp h).resolve_right hs
  rw [hk,zero_mul] at h₁
  exact ha h₁

end OperatorFirst.KakeyaCut
#print axioms OperatorFirst.KakeyaCut.site_restriction
#print axioms OperatorFirst.KakeyaCut.edge_restriction
#print axioms OperatorFirst.KakeyaCut.internal_edge_cancels
#print axioms OperatorFirst.KakeyaCut.exterior_edge_cancels
#print axioms OperatorFirst.KakeyaCut.entering_edge_survives
#print axioms OperatorFirst.KakeyaCut.restriction_of_integer_combination
#print axioms OperatorFirst.KakeyaCut.first_vertex_restriction
#print axioms OperatorFirst.KakeyaCut.forbidden_admissible_determinant
#print axioms OperatorFirst.KakeyaCut.forbidden_not_rank_one
