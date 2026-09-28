import Mathlib
import MixedIntake.AK_original

/-! Positive-denominator interpretation and product-growth implications only.
No forcing graph, attainability, or subset-rank theorem is assumed as an axiom. -/
namespace OperatorFirst.KakeyaExtension

theorem powN_positive (n : ℕ) (hn : 0 < n) : ∀ k, 0 < AK.powN n k := by
  intro k
  induction k with
  | zero => simp [AK.powN]
  | succ k ih => exact Nat.mul_pos ih hn

theorem power_density_exact (m n k : ℕ) (hn : 0 < n) :
    (AK.powM m n k : ℚ) / (AK.powN n k : ℚ) = (k : ℚ) * ((m : ℚ)/n) := by
  have hnp : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hkp : (AK.powN n k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (powN_positive n hn k))
  have hi : (AK.powM m n k : ℚ) * n = (k : ℚ) * ((m : ℚ) * AK.powN n k) := by
    exact_mod_cast AK.density_of_power m n k
  field_simp [hnp, hkp]
  nlinarith [hi]

/-- A full score needs its own lower bound; it is not asserted monotone. -/
theorem product_score_exclusion (m n k : ℕ) (hn : 0 < n) (score bound : ℚ)
    (hlower : (AK.powM m n k : ℚ) / AK.powN n k ≤ score)
    (hbudget : bound < (k : ℚ)*((m : ℚ)/n)) : bound < score := by
  rw [power_density_exact m n k hn] at hlower
  exact hbudget.trans_le hlower

/-- Eventual density growth requires a strictly positive initial density. -/
theorem positive_density_eventually_exceeds (d bound : ℝ) (hd : 0 < d) :
    ∃ k : ℕ, bound < (k : ℝ)*d := by
  obtain ⟨k,hk⟩ := exists_nat_gt (bound/d)
  refine ⟨k, ?_⟩
  exact (div_lt_iff₀ hd).mp hk

theorem zero_density_does_not_grow (k : ℕ) : (k : ℝ)*0 = 0 := by ring

end OperatorFirst.KakeyaExtension
#print axioms OperatorFirst.KakeyaExtension.powN_positive
#print axioms OperatorFirst.KakeyaExtension.power_density_exact
#print axioms OperatorFirst.KakeyaExtension.product_score_exclusion
#print axioms OperatorFirst.KakeyaExtension.positive_density_eventually_exceeds
#print axioms OperatorFirst.KakeyaExtension.zero_density_does_not_grow
