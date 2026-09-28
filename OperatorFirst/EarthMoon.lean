import Mathlib
import OperatorFirst.RestrictionBridge

/-! Finite C7[K4] certificates. Planar Euler bounds remain explicit premises.
No proof of the full Earth-Moon construction or general all-n planarity. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace EarthMoon

def CycleAdjacent (i j : Nat) : Prop :=
  (i+1)%7 = j ∨ (j+1)%7 = i

instance (i j : Nat) : Decidable (CycleAdjacent i j) :=
  inferInstanceAs (Decidable ((i+1)%7 = j ∨ (j+1)%7 = i))

def JoinAdjacent (u v : Nat) : Prop := CycleAdjacent (u/4) (v/4)
instance (u v : Nat) : Decidable (JoinAdjacent u v) :=
  inferInstanceAs (Decidable (CycleAdjacent (u/4) (v/4)))

def HostAdjacent (u v : Nat) : Prop :=
  u ≠ v ∧ (u/4 = v/4 ∨ JoinAdjacent u v)
instance (u v : Nat) : Decidable (HostAdjacent u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ (u/4 = v/4 ∨ JoinAdjacent u v)))

def pairs : List (Nat × Nat) :=
  (List.range 28).flatMap fun u => (List.range 28).map fun v => (u,v)
def joinEdges : List (Nat × Nat) :=
  pairs.filter fun p => decide (p.1 < p.2 ∧ JoinAdjacent p.1 p.2)
def hostEdges : List (Nat × Nat) :=
  pairs.filter fun p => decide (p.1 < p.2 ∧ HostAdjacent p.1 p.2)

theorem cycle_triangle_free : ∀ i j k : Fin 7,
    ¬ (CycleAdjacent i.val j.val ∧ CycleAdjacent j.val k.val ∧
       CycleAdjacent k.val i.val) := by decide

theorem joins_triangle_free (u v w : Nat) (hu : u < 28)
    (hv : v < 28) (hw : w < 28) :
    ¬ (JoinAdjacent u v ∧ JoinAdjacent v w ∧ JoinAdjacent w u) := by
  exact cycle_triangle_free ⟨u/4, by omega⟩ ⟨v/4, by omega⟩ ⟨w/4, by omega⟩

theorem join_edge_count : joinEdges.length = 112 := by decide
theorem host_edge_count : hostEdges.length = 154 := by decide

/-- Arithmetic only; layer bounds and coverage are explicit premises. -/
theorem two_layer_capacity (N E e1 e2 : Nat) (hN : 3 ≤ N)
    (hcover : E ≤ e1+e2) (h1 : e1+4 ≤ 2*N) (h2 : e2+4 ≤ 2*N) :
    E+8 ≤ 4*N := by omega

theorem c7_no_capacity_cover (e1 e2 : Nat)
    (hcover : joinEdges.length ≤ e1+e2)
    (h1 : e1+4 ≤ 2*28) (h2 : e2+4 ≤ 2*28) : False := by
  have hc := join_edge_count
  omega

/-- All n >= 4, r >= 4 exceed the putative two-layer join capacity.
    The graph-theoretic count r*r*n is not derived for all n,r here. -/
theorem inflated_capacity_impossible (n r : Nat) (hr : 4 ≤ r)
    (h : r*r*n+8 ≤ 4*(r*n)) : False := by
  have hm := Nat.mul_le_mul_right (r*n) hr
  have he : r*r*n = r*(r*n) := Nat.mul_assoc r r n
  omega

theorem whole_graph_euler_passes : 154 ≤ 6*28-12 := by decide
theorem nine_classes_too_small : 9*3 < 28 := by decide

def color (u : Nat) : Nat :=
  ([0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,0,1,8,9,2,3,4,5,6,7,8,9] : List Nat).getD u 0
theorem color_range : ∀ u : Fin 28, color u.val < 10 := by decide
theorem proper_ten_coloring : ∀ u v : Fin 28,
    HostAdjacent u.val v.val → color u.val ≠ color v.val := by decide

def joinSet : Finset (Nat × Nat) := joinEdges.toFinset
theorem join_set_card : joinSet.card = 112 := by decide

theorem c7_no_two_euler_layers (E₁ E₂ : Finset (Nat × Nat))
    (hcover : joinSet ⊆ E₁ ∪ E₂)
    (h₁ : (joinSet ∩ E₁).card+4 ≤ 2*28)
    (h₂ : (joinSet ∩ E₂).card+4 ≤ 2*28) : False := by
  have hb := OperatorFirst.RestrictionBridge.two_layer_restriction_bound
    joinSet E₁ E₂ 28 hcover h₁ h₂
  rw [join_set_card] at hb
  omega
end EarthMoon


#print axioms EarthMoon.cycle_triangle_free
#print axioms EarthMoon.joins_triangle_free
#print axioms EarthMoon.join_edge_count
#print axioms EarthMoon.host_edge_count
#print axioms EarthMoon.two_layer_capacity
#print axioms EarthMoon.c7_no_capacity_cover
#print axioms EarthMoon.inflated_capacity_impossible
#print axioms EarthMoon.whole_graph_euler_passes
#print axioms EarthMoon.nine_classes_too_small
#print axioms EarthMoon.color_range
#print axioms EarthMoon.proper_ten_coloring
#print axioms EarthMoon.join_set_card
#print axioms EarthMoon.c7_no_two_euler_layers

