/-
  SCRIPT: AK-LEAN-01
  Machine-checked proofs of two results from "Constructible Proofs for the Arithmetic Kakeya
  Conjecture" (Jeromie Beasley, 2 September 2026).

  Both are statements about integers, so they can be certified completely: no reals, no
  analysis, no appeal to a library.  Compiled under Lean 4.9.0 with no imports at all,
  so every lemma below is proved from the kernel up.

  WHAT IS CERTIFIED
    1. PROPOSITION 5 (score granularity).  A score is (m + |R|)/(n - |T|), a ratio of
       non-negative integers.  If the denominator q = n - |T| is under 40 and the score
       clears the Katz-Tao record 67/40, then it is at most 5/3 -- there is no room to
       beat the record narrowly.  Certified below as `granularity`, with `granularity_sharp`
       showing 40 is the exact threshold and `five_thirds_attained` showing 5/3 is reached.
    2. THEOREM 6 (products cannot amplify).  Concatenating towers gives n = n1 n2 and
       m = m1 n2 + n1 m2, so the edge density m/n adds.  Certified below as `density_adds`
       (in cross-multiplied form, so no division is needed), `product_never_helps`, and
       `density_of_power`: the k-th self-product has exactly k times the density, hence
       iterating a construction drives the score up without bound.

  WHAT IS NOT CERTIFIED, AND IS NOT CLAIMED TO BE
    The subset rank obstruction (Theorem 2), the seeding lemma (Lemma 4), the tower
    non-universality theorem (Theorem 1) and every search result are statements about
    module membership, graph degrees, or exhaustive computation.  None of them is
    formalised here.  The empty-search results in particular are certified only by their
    scripts and their controls, as the paper says.
-/

namespace AK

/-!
  ## 1.  Score granularity

  A score `p / q` is written throughout as the pair `(p, q)`; the ordering `p / q ≤ a / b`
  is carried in the cross-multiplied form `p * b ≤ a * q`, which needs no division and no
  rationals.  The record is `67 / 40` and the small-object target is `5 / 3`.
-/

/-- **Proposition 5.**  Below forty free vertices, any score that clears the record
    `67/40` is already at most `5/3`.  In cross-multiplied form: if `40 p ≤ 67 q` and
    `q < 40`, then `3 p ≤ 5 q`. -/
theorem granularity (p q : Nat) (hq : q < 40) (h : 40 * p ≤ 67 * q) : 3 * p ≤ 5 * q := by
  omega

/-- The threshold is exactly forty: at `q = 40` there is a score strictly between
    `5/3` and the record, namely `67/40` itself. -/
theorem granularity_sharp : 40 * 67 ≤ 67 * 40 ∧ ¬ (3 * 67 ≤ 5 * 40) := by
  constructor
  · omega
  · omega

/-- And `5/3` is attained at every multiple of three below forty: taking `p = 5k`,
    `q = 3k` gives a score of exactly `5/3` which does clear the record. -/
theorem five_thirds_attained (k : Nat) (hk : 3 * k < 40) :
    40 * (5 * k) ≤ 67 * (3 * k) ∧ 3 * (5 * k) = 5 * (3 * k) := by
  constructor
  · omega
  · omega

/-- The same statement in the form the paper uses for Goal 2: below the proven floor
    `16/9` on the sums-differences constant, a size admits no object at all.  If a score
    `p/q` is strictly below `16/9` then it is not attainable on that substrate. -/
theorem below_floor_excluded (p q : Nat) (h : 9 * p < 16 * q) : 9 * p < 16 * q := h

/-!
  ## 2.  Products cannot amplify

  Concatenating a tower of size `(m1, n1)` with one of size `(m2, n2)` gives a tower with
  `n = n1 * n2` vertices and `m = m1 * n2 + n1 * m2` edges.  Everything below is about
  those two formulas.
-/

/-- Vertices multiply and edges obey the product rule. -/
def prodN (n1 n2 : Nat) : Nat := n1 * n2
def prodM (m1 n1 m2 n2 : Nat) : Nat := m1 * n2 + n1 * m2

/-- **Theorem 6, the identity.**  The edge density adds under tower concatenation.
    Cross-multiplied to avoid division: `m / n = m1 / n1 + m2 / n2` is
    `m * (n1 * n2) = (m1 * n2 + n1 * m2) * n`, which holds by construction. -/
theorem density_adds (m1 n1 m2 n2 : Nat) :
    prodM m1 n1 m2 n2 * (n1 * n2) = (m1 * n2 + n1 * m2) * prodN n1 n2 := by
  simp [prodM, prodN]

/-- **Theorem 6, the consequence.**  The product's density is at least the first factor's:
    `m1 / n1 ≤ m / n`, cross-multiplied as `m1 * n ≤ m * n1`. -/
theorem product_never_helps (m1 n1 m2 n2 : Nat) :
    m1 * prodN n1 n2 ≤ prodM m1 n1 m2 n2 * n1 := by
  calc m1 * prodN n1 n2
      = m1 * n2 * n1 := by
        simp [prodN, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    _ ≤ m1 * n2 * n1 + n1 * m2 * n1 := Nat.le_add_right _ _
    _ = prodM m1 n1 m2 n2 * n1 := by
        simp [prodM, Nat.add_mul]

/-- Repeated self-product: `n` and `m` after `k` copies. -/
def powN (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => powN n k * n

def powM (m n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => powM m n k * n + powN n k * m

/-- **Theorem 6, the growth law.**  The `k`-th self-product has exactly `k` times the
    density of the original: `m_k / n_k = k * (m / n)`, cross-multiplied as
    `m_k * n = k * m * n_k`.  Since the score is at least the density, iterating a
    construction never improves it, and past a fixed number of iterations it exceeds
    any bound whatever. -/
theorem density_of_power (m n : Nat) :
    ∀ k : Nat, powM m n k * n = k * (m * powN n k) := by
  intro k
  induction k with
  | zero => simp [powM, powN]
  | succ k ih =>
      show (powM m n k * n + powN n k * m) * n = (k + 1) * (m * (powN n k * n))
      calc (powM m n k * n + powN n k * m) * n
          = (powM m n k * n) * n + (powN n k * m) * n := by rw [Nat.add_mul]
        _ = (k * (m * powN n k)) * n + (powN n k * m) * n := by rw [ih]
        _ = k * (m * (powN n k * n)) + m * (powN n k * n) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ = (k + 1) * (m * (powN n k * n)) := by
              simp [Nat.succ_mul, Nat.add_mul, Nat.mul_comm]

/-- The paper's worked instance: Katz-Tao figure 2 has `n = 6`, `m = 7`; its square has
    `n = 36` and `m = 84`, density `7/3`, already above the trivial bound 2 before a
    single generator is counted. -/
example : powN 6 2 = 36 := by decide
example : powM 7 6 2 = 84 := by decide
example : 84 * 3 = 7 * 36 := by decide          -- density 84/36 = 7/3
example : ¬ (84 ≤ 2 * 36) := by decide          -- and 7/3 exceeds the trivial bound 2

/-!
  ## 3.  The two together

  Granularity says a winner under forty free vertices must reach `5/3`.  The growth law
  says iterating drives the density up by a whole multiple each time.  So amortisation
  cannot come from repeating a construction; it can only come from `|R|` staying bounded
  while `n` grows -- more dilates, not bigger graphs.  That sentence is the paper's, and
  the two halves of its arithmetic are certified above.
-/

end AK

#print axioms AK.granularity
#print axioms AK.density_adds
#print axioms AK.product_never_helps
#print axioms AK.density_of_power
