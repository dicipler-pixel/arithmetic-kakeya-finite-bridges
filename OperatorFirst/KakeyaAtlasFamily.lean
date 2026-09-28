import Mathlib

/-! The fixed Figure 3 graph with edge label (1,q). Vertices 0,1,2,3
are g4,g1,g3,g2. All coefficients and q are rational. Reachability allows
every fresh-vertex forcing order. The combinatorial topology stays [2,2]. -/
open scoped BigOperators
namespace OperatorFirst.KakeyaAtlasFamily

def rows (q : ℚ) : Fin 7 → Fin 8 → ℚ := ![
  ![1,0,0,0,-1,0,0,0], ![0,0,1,0,0,0,-1,0],
  ![1,q,-1,-q,0,0,0,0], ![0,0,0,0,0,1,0,-1],
  ![0,0,1,1,0,0,0,0], ![0,0,0,0,0,0,1,1],
  ![0,1,0,0,0,0,0,0]]

def witness (q : ℚ) (c : Fin 7 → ℚ) : Fin 8 → ℚ :=
  ![c 0+c 2, q*c 2+c 6, c 1-c 2+c 4, -q*c 2+c 4,
    -c 0, c 3, -c 1+c 5, -c 3+c 5]
def coord (v : Fin 4) (b : Fin 2) : Fin 8 := ⟨2*v.val+b.val, by omega⟩
def Step (q : ℚ) (c : Fin 7 → ℚ) (T : Finset (Fin 4)) (e : Fin 4) : Prop :=
  witness q c (coord e 0) ≠ 0 ∧
  witness q c (coord e 0) + witness q c (coord e 1) = 0 ∧
  ∀ v : Fin 4, v ∉ T → v ≠ e →
    witness q c (coord v 0) = 0 ∧ witness q c (coord v 1) = 0

theorem witness_is_generator_combination (q : ℚ) (c : Fin 7 → ℚ) (j : Fin 8) :
    witness q c j = ∑ i, c i * rows q i j := by
  simp only [Fin.sum_univ_succ]
  change witness q c j = c 0*rows q 0 j + (c 1*rows q 1 j + (c 2*rows q 2 j + (c 3*rows q 3 j + (c 4*rows q 4 j + (c 5*rows q 5 j + (c 6*rows q 6 j + 0))))))
  fin_cases j
  · change c 0+c 2 = c 0*(1) + (c 1*(0) + (c 2*(1) + (c 3*(0) + (c 4*(0) + (c 5*(0) + (c 6*(0) + (0)))))))
    ring
  · change q*c 2+c 6 = c 0*(0) + (c 1*(0) + (c 2*(q) + (c 3*(0) + (c 4*(0) + (c 5*(0) + (c 6*(1) + (0)))))))
    ring
  · change c 1-c 2+c 4 = c 0*(0) + (c 1*(1) + (c 2*(-1) + (c 3*(0) + (c 4*(1) + (c 5*(0) + (c 6*(0) + (0)))))))
    ring
  · change -q*c 2+c 4 = c 0*(0) + (c 1*(0) + (c 2*(-q) + (c 3*(0) + (c 4*(1) + (c 5*(0) + (c 6*(0) + (0)))))))
    ring
  · change -c 0 = c 0*(-1) + (c 1*(0) + (c 2*(0) + (c 3*(0) + (c 4*(0) + (c 5*(0) + (c 6*(0) + (0)))))))
    ring
  · change c 3 = c 0*(0) + (c 1*(0) + (c 2*(0) + (c 3*(1) + (c 4*(0) + (c 5*(0) + (c 6*(0) + (0)))))))
    ring
  · change -c 1+c 5 = c 0*(0) + (c 1*(-1) + (c 2*(0) + (c 3*(0) + (c 4*(0) + (c 5*(1) + (c 6*(0) + (0)))))))
    ring
  · change -c 3+c 5 = c 0*(0) + (c 1*(0) + (c 2*(0) + (c 3*(-1) + (c 4*(0) + (c 5*(1) + (c 6*(0) + (0)))))))
    ring

theorem label_admissible_iff (q : ℚ) : 1+q ≠ 0 ↔ q ≠ -1 := by constructor <;> intro h <;> contrapose! h <;> linarith

theorem first_step_parameters (q : ℚ) (c : Fin 7 → ℚ) (e : Fin 4)
    (h : Step q c ∅ e) : (q=1 ∧ e=0) ∨ (q=2 ∧ e=2) := by
  rcases h with ⟨hn, hs, hz⟩
  fin_cases e
  · have h1 := hz 1 (by simp) (by decide)
    have h2 := hz 2 (by simp) (by decide)
    have h3 := hz 3 (by simp) (by decide)
    norm_num [coord, witness] at hn hs h1 h2 h3
    have hc1 : c 1=0 := by linarith [h2.2,h3.1,h3.2]
    have hp : (q-1)*c 2=0 := by nlinarith [h1.1,h1.2]
    have hn2 : c 2 ≠ 0 := by simpa [h2.1] using hn
    have hq := (mul_eq_zero.mp hp).resolve_right hn2
    exact Or.inl ⟨by linarith, rfl⟩
  · have h0 := hz 0 (by simp) (by decide)
    have h2 := hz 2 (by simp) (by decide)
    have h3 := hz 3 (by simp) (by decide)
    norm_num [coord, witness] at hn hs h0 h2 h3
    exfalso
    apply hn
    have hc2 : c 2=0 := by linarith [h0.1,h2.1]
    rw [hc2,mul_zero] at hs
    linarith [h2.2,h3.1,h3.2]
  · have h0 := hz 0 (by simp) (by decide)
    have h1 := hz 1 (by simp) (by decide)
    have h3 := hz 3 (by simp) (by decide)
    norm_num [coord, witness] at hn hs h0 h1 h3
    have hc2 : c 2 = -c 0 := by linarith [h0.1]
    rw [hc2] at h1
    have hp : (q-2)*c 0=0 := by nlinarith [h1.1,h1.2,h3.1,h3.2]
    have hq := (mul_eq_zero.mp hp).resolve_right hn
    exact Or.inr ⟨by linarith, rfl⟩
  · have h0 := hz 0 (by simp) (by decide)
    have h1 := hz 1 (by simp) (by decide)
    have h2 := hz 2 (by simp) (by decide)
    norm_num [coord, witness] at hn hs h0 h1 h2
    exfalso
    apply hn
    have hc2 : c 2=0 := by linarith [h0.1,h2.1]
    rw [hc2,mul_zero] at h1
    linarith [h1.1,h1.2,h2.2]

theorem q_one_step_with_known_zero (c : Fin 7 → ℚ) (T : Finset (Fin 4))
    (hT : T ⊆ {0}) (e : Fin 4) (h : Step 1 c T e) : e=0 := by
  have hn1 : (1 : Fin 4) ∉ T := by intro h; have := hT h; simp at this
  have hn2 : (2 : Fin 4) ∉ T := by intro h; have := hT h; simp at this
  have hn3 : (3 : Fin 4) ∉ T := by intro h; have := hT h; simp at this
  rcases h with ⟨hn, hs, hz⟩
  fin_cases e
  · rfl
  · have h2 := hz 2 hn2 (by decide)
    have h3 := hz 3 hn3 (by decide)
    norm_num [coord, witness] at hn hs h2 h3
    exfalso; apply hn; linarith [h2.1,h2.2,h3.1,h3.2]
  · have h1 := hz 1 hn1 (by decide)
    have h3 := hz 3 hn3 (by decide)
    norm_num [coord, witness] at hn hs h1 h3
    exfalso; apply hn; linarith [h1.1,h1.2,h3.1,h3.2]
  · have h1 := hz 1 hn1 (by decide)
    have h2 := hz 2 hn2 (by decide)
    norm_num [coord, witness] at hn hs h1 h2
    exfalso; apply hn; linarith [h1.1,h1.2,h2.1,h2.2]

inductive Reachable (q : ℚ) : Finset (Fin 4) → Prop
  | start : Reachable q ∅
  | add {T : Finset (Fin 4)} {e : Fin 4} (c : Fin 7 → ℚ) :
      Reachable q T → e ∉ T → Step q c T e → Reachable q (insert e T)
def Complete (q : ℚ) : Prop := Reachable q Finset.univ

theorem q_one_reachable_subset {T : Finset (Fin 4)} (h : Reachable 1 T) : T ⊆ {0} := by
  induction h with
  | start => simp
  | @add T e c h hf hs ih =>
    have he := q_one_step_with_known_zero c T ih e hs
    subst e
    exact Finset.insert_subset (by simp) ih

theorem q_one_not_complete : ¬ Complete 1 := by
  intro h
  have hsub := q_one_reachable_subset h
  have := hsub (Finset.mem_univ (1 : Fin 4))
  simp at this

theorem reachable_nonempty_has_first (q : ℚ) {T : Finset (Fin 4)}
    (h : Reachable q T) (hne : T ≠ ∅) : ∃ c e, Step q c ∅ e := by
  induction h with
  | start => exact False.elim (hne rfl)
  | @add T e c h hf hs ih =>
    by_cases ht : T=∅
    · subst T; exact ⟨c,e,hs⟩
    · exact ih ht

theorem complete_only_at_two (q : ℚ) (h : Complete q) : q=2 := by
  obtain ⟨c,e,hs⟩ := reachable_nonempty_has_first q (T := Finset.univ) h (by decide)
  rcases first_step_parameters q c e hs with hq | hq
  · rcases hq with ⟨rfl,he⟩
    exact False.elim (q_one_not_complete h)
  · exact hq.1

def coeff₁ : Fin 7 → ℚ := ![-1,-1,1,-1,2,-1,-2]
def coeff₂ : Fin 7 → ℚ := ![3,1,-1,1,-2,1,0]
def coeff₃ : Fin 7 → ℚ := ![0,0,2,0,3,0,0]
def coeff₄ : Fin 7 → ℚ := ![0,-1,0,1,0,0,0]

theorem q_two_first : Step 2 coeff₁ ∅ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · change (-(-1 : ℚ)) ≠ 0
    norm_num
  · change (-(-1 : ℚ)) + ((-1 : ℚ)) = 0
    norm_num
  · intro v hv he
    fin_cases v
    · change ((-1 : ℚ)+(1 : ℚ))=0 ∧ ((2 : ℚ)*(1 : ℚ)+(-2 : ℚ))=0
      norm_num
    · change ((-1 : ℚ)-(1 : ℚ)+(2 : ℚ))=0 ∧ (-(2 : ℚ)*(1 : ℚ)+(2 : ℚ))=0
      norm_num
    · exact (he rfl).elim
    · change (-(-1 : ℚ)+(-1 : ℚ))=0 ∧ (-(-1 : ℚ)+(-1 : ℚ))=0
      norm_num

theorem q_two_second : Step 2 coeff₂ {2} 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change ((3 : ℚ)+(-1 : ℚ)) ≠ 0
    norm_num
  · change ((3 : ℚ)+(-1 : ℚ)) + ((2 : ℚ)*(-1 : ℚ)+(0 : ℚ)) = 0
    norm_num
  · intro v hv he
    fin_cases v
    · exact (he rfl).elim
    · change ((1 : ℚ)-(-1 : ℚ)+(-2 : ℚ))=0 ∧ (-(2 : ℚ)*(-1 : ℚ)+(-2 : ℚ))=0
      norm_num
    · exact (hv (by decide)).elim
    · change (-(1 : ℚ)+(1 : ℚ))=0 ∧ (-(1 : ℚ)+(1 : ℚ))=0
      norm_num

theorem q_two_third : Step 2 coeff₃ {2,0} 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change ((0 : ℚ)-(2 : ℚ)+(3 : ℚ)) ≠ 0
    norm_num
  · change ((0 : ℚ)-(2 : ℚ)+(3 : ℚ)) + (-(2 : ℚ)*(2 : ℚ)+(3 : ℚ)) = 0
    norm_num
  · intro v hv he
    fin_cases v
    · exact (hv (by decide)).elim
    · exact (he rfl).elim
    · exact (hv (by decide)).elim
    · change (-(0 : ℚ)+(0 : ℚ))=0 ∧ (-(0 : ℚ)+(0 : ℚ))=0
      norm_num

theorem q_two_fourth : Step 2 coeff₄ {2,0,1} 3 := by
  refine ⟨?_, ?_, ?_⟩
  · change (-(-1 : ℚ)+(0 : ℚ)) ≠ 0
    norm_num
  · change (-(-1 : ℚ)+(0 : ℚ)) + (-(1 : ℚ)+(0 : ℚ)) = 0
    norm_num
  · intro v hv he
    fin_cases v
    · exact (hv (by decide)).elim
    · exact (hv (by decide)).elim
    · exact (hv (by decide)).elim
    · exact (he rfl).elim

theorem q_two_complete : Complete 2 := by
  have h1 : Reachable 2 {2} := Reachable.add coeff₁ Reachable.start (by simp) q_two_first
  have h2 : Reachable 2 {0,2} := Reachable.add coeff₂ h1 (by simp) q_two_second
  have h3 : Reachable 2 {1,0,2} := Reachable.add coeff₃ h2 (by simp)
    (by simpa [Finset.pair_comm] using q_two_third)
  have ht : ({1,0,2} : Finset (Fin 4)) = {2,0,1} := by decide
  have h4 : Reachable 2 {3,1,0,2} := Reachable.add coeff₄ h3 (by decide)
    (by rw [ht]; exact q_two_fourth)
  have hu : ({3,1,0,2} : Finset (Fin 4)) = Finset.univ := by decide
  simpa [Complete, hu] using h4

theorem completion_iff_q_two (q : ℚ) : Complete q ↔ q=2 := by
  constructor
  · exact complete_only_at_two q
  · intro h; subst q; exact q_two_complete

theorem generic_family_cannot_start (q : ℚ) (h1 : q ≠ 1) (h2 : q ≠ 2) :
    ¬ ∃ c e, Step q c ∅ e := by
  rintro ⟨c,e,h⟩
  rcases first_step_parameters q c e h with h | h
  · exact h1 h.1
  · exact h2 h.1

theorem q_one_first : Step 1 ![0,0,1,0,1,0,-2] ∅ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change ((0 : ℚ)+(1 : ℚ)) ≠ 0
    norm_num
  · change ((0 : ℚ)+(1 : ℚ)) + ((1 : ℚ)*(1 : ℚ)+(-2 : ℚ)) = 0
    norm_num
  · intro v hv he
    fin_cases v
    · exact (he rfl).elim
    · change ((0 : ℚ)-(1 : ℚ)+(1 : ℚ))=0 ∧ (-(1 : ℚ)*(1 : ℚ)+(1 : ℚ))=0
      norm_num
    · change (-(0 : ℚ))=0 ∧ ((0 : ℚ))=0
      norm_num
    · change (-(0 : ℚ)+(0 : ℚ))=0 ∧ (-(0 : ℚ)+(0 : ℚ))=0
      norm_num

theorem fixed_family_score : ((4+3 : ℚ)/4) = 7/4 := by norm_num
theorem fixed_family_misses_target : (67/40 : ℚ) < (4+3)/4 := by norm_num

end OperatorFirst.KakeyaAtlasFamily

#print axioms OperatorFirst.KakeyaAtlasFamily.witness_is_generator_combination
#print axioms OperatorFirst.KakeyaAtlasFamily.label_admissible_iff
#print axioms OperatorFirst.KakeyaAtlasFamily.first_step_parameters
#print axioms OperatorFirst.KakeyaAtlasFamily.q_one_step_with_known_zero
#print axioms OperatorFirst.KakeyaAtlasFamily.q_one_reachable_subset
#print axioms OperatorFirst.KakeyaAtlasFamily.q_one_not_complete
#print axioms OperatorFirst.KakeyaAtlasFamily.reachable_nonempty_has_first
#print axioms OperatorFirst.KakeyaAtlasFamily.complete_only_at_two
#print axioms OperatorFirst.KakeyaAtlasFamily.q_two_first
#print axioms OperatorFirst.KakeyaAtlasFamily.q_two_second
#print axioms OperatorFirst.KakeyaAtlasFamily.q_two_third
#print axioms OperatorFirst.KakeyaAtlasFamily.q_two_fourth
#print axioms OperatorFirst.KakeyaAtlasFamily.q_two_complete
#print axioms OperatorFirst.KakeyaAtlasFamily.completion_iff_q_two
#print axioms OperatorFirst.KakeyaAtlasFamily.generic_family_cannot_start
#print axioms OperatorFirst.KakeyaAtlasFamily.q_one_first
#print axioms OperatorFirst.KakeyaAtlasFamily.fixed_family_score
#print axioms OperatorFirst.KakeyaAtlasFamily.fixed_family_misses_target
