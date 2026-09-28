import Mathlib

/-!
Restriction identities common to the two obstruction strategies.
These prove finite cancellation and capacity transfer. They do not identify
the arithmetic Kakeya module with a graph, or a graph with spacetime.
-/
open scoped BigOperators
namespace OperatorFirst.RestrictionBridge

def flux {ι : Type*} (f : ι → ι → ℝ) (S T : Finset ι) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, (f i j - f j i)

theorem internal_flux_zero {ι : Type*} (f : ι → ι → ℝ) (S : Finset ι) :
    flux f S S = 0 := by
  unfold flux
  simp only [Finset.sum_sub_distrib]
  have h : (∑ i ∈ S, ∑ j ∈ S, f j i) = ∑ j ∈ S, ∑ i ∈ S, f j i :=
    Finset.sum_comm
  exact sub_eq_zero.mpr h.symm

/-- Summing antisymmetric exchanges over S removes internal exchanges. -/
theorem restriction_is_boundary_flux {ι : Type*} [DecidableEq ι]
    (f : ι → ι → ℝ) (S T : Finset ι) (h : Disjoint S T) :
    flux f S (S ∪ T) = flux f S T := by
  have hsplit : flux f S (S ∪ T) = flux f S S + flux f S T := by
    unfold flux
    simp only [Finset.sum_union h, Finset.sum_add_distrib]
  rw [hsplit, internal_flux_zero, zero_add]

/-- Actual finite-set coverage-to-cardinality bridge, with no planarity assumption. -/
theorem restricted_cover_card {α : Type*} [DecidableEq α]
    (H E₁ E₂ : Finset α) (hcover : H ⊆ E₁ ∪ E₂) :
    H.card ≤ (H ∩ E₁).card + (H ∩ E₂).card := by
  have hsub : H ⊆ (H ∩ E₁) ∪ (H ∩ E₂) := by
    intro x hx
    have he := hcover hx
    simp only [Finset.mem_union, Finset.mem_inter] at he ⊢
    exact he.elim (fun h₁ => Or.inl ⟨hx,h₁⟩) (fun h₂ => Or.inr ⟨hx,h₂⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The missing planar Euler theorem is explicitly supplied as two inequalities. -/
theorem two_layer_restriction_bound {α : Type*} [DecidableEq α]
    (H E₁ E₂ : Finset α) (N : ℕ) (hcover : H ⊆ E₁ ∪ E₂)
    (h₁ : (H ∩ E₁).card + 4 ≤ 2*N)
    (h₂ : (H ∩ E₂).card + 4 ≤ 2*N) : H.card + 8 ≤ 4*N := by
  have hc := restricted_cover_card H E₁ E₂ hcover
  omega

theorem two_layer_restriction_obstruction {α : Type*} [DecidableEq α]
    (H E₁ E₂ : Finset α) (N : ℕ) (hcover : H ⊆ E₁ ∪ E₂)
    (h₁ : (H ∩ E₁).card + 4 ≤ 2*N)
    (h₂ : (H ∩ E₂).card + 4 ≤ 2*N)
    (hlarge : 4*N < H.card+8) : False := by
  have hb := two_layer_restriction_bound H E₁ E₂ N hcover h₁ h₂
  omega

end OperatorFirst.RestrictionBridge
#print axioms OperatorFirst.RestrictionBridge.internal_flux_zero
#print axioms OperatorFirst.RestrictionBridge.restriction_is_boundary_flux
#print axioms OperatorFirst.RestrictionBridge.restricted_cover_card
#print axioms OperatorFirst.RestrictionBridge.two_layer_restriction_bound
#print axioms OperatorFirst.RestrictionBridge.two_layer_restriction_obstruction
