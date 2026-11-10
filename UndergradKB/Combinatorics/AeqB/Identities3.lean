import UndergradKB.Combinatorics.AeqB.Database
import UndergradKB.Common.Attr

namespace UndergradKB.Combinatorics.AeqB.Identities3
open Finset UndergradKB.Combinatorics.AeqB
open scoped Nat
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### CO-385: the Pfaff–Saalschütz binomial-product identity (p. 203)

We use reciprocal factorials `rf` (zero at negative integers) so that the telescoping identity
holds at every integer summation index.  The recurrence in `c` is certified by
`G(c,n) = -(a+b+c+1-n)! rf(a-n) rf(b-n) rf(c+1-n) rf(n+k-1) rf(n-k-1)`. -/

/-- Summand `(a+b+c-n)! / ((a-n)!(b-n)!(c-n)!(n+k)!(n-k)!)`, written with reciprocal factorials. -/
def sT (a b c k n : ℤ) : ℚ :=
  fct (a + b + c - n) * (rf (a - n) * rf (b - n) * rf (c - n) * rf (n + k) * rf (n - k))

/-- The telescoping potential of the certificate. -/
def sG (a b c k n : ℤ) : ℚ :=
  -(fct (a + b + c + 1 - n) *
    (rf (a - n) * rf (b - n) * rf (c + 1 - n) * rf (n + k - 1) * rf (n - k - 1)))

theorem sstep (a b c k n : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hn : n ≤ a) :
    ((c : ℚ) + k + 1) * ((c : ℚ) - k + 1) * sT a b (c + 1) k n
        - ((a : ℚ) + c + 1) * ((b : ℚ) + c + 1) * sT a b c k n
      = sG a b c k (n + 1) - sG a b c k n := by
  unfold sT sG
  simp only [show a + b + (c + 1) - n = a + b + c - n + 1 by ring,
    show a + b + c + 1 - (n + 1) = a + b + c - n by ring,
    show a + b + c + 1 - n = a + b + c - n + 1 by ring,
    show a - (n + 1) = a - n - 1 by ring, show b - (n + 1) = b - n - 1 by ring,
    show c + 1 - (n + 1) = c - n by ring, show n + 1 + k - 1 = n + k by ring,
    show n + 1 - k - 1 = n - k by ring]
  have f1 := fct_rec (a + b + c - n) (a + b + c - n + 1) rfl (by omega)
  have ra := rf_rec (a - n - 1) (a - n) (by ring)
  have rb := rf_rec (b - n - 1) (b - n) (by ring)
  have rc := rf_rec (c - n) (c + 1 - n) (by ring)
  have rp := rf_rec (n + k - 1) (n + k) (by ring)
  have rq := rf_rec (n - k - 1) (n - k) (by ring)
  rw [f1, ra, rb, rc, rp, rq]
  push_cast
  ring

lemma fct_mul_rf (m : ℤ) (hm : 0 ≤ m) : fct m * rf m = 1 := by
  unfold fct rf
  rw [if_pos hm]
  have : (((m.toNat)! : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

lemma binom_eq (m j : ℕ) :
    (m.choose j : ℚ) = fct (m : ℤ) * rf (j : ℤ) * rf ((m : ℤ) - j) := by
  have := zchoose_cast m (j : ℤ)
  simpa [zchoose, fct_natCast] using this

/-- The sum over `n` of the summands, for naturals. -/
def sSum (a b c k : ℕ) : ℚ := ∑ n ∈ range (a + 1), sT a b c k n

lemma sSum_rec (a b c k : ℕ) :
    ((c : ℚ) + k + 1) * ((c : ℚ) - k + 1) * sSum a b (c + 1) k
      = ((a : ℚ) + c + 1) * ((b : ℚ) + c + 1) * sSum a b c k := by
  have h : ((c : ℚ) + k + 1) * ((c : ℚ) - k + 1) * sSum a b (c + 1) k
      - ((a : ℚ) + c + 1) * ((b : ℚ) + c + 1) * sSum a b c k
      = ∑ n ∈ range (a + 1), (sG a b c k ((n : ℤ) + 1) - sG a b c k n) := by
    unfold sSum
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn' : (n : ℤ) ≤ a := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hn)
    have := sstep (a : ℤ) (b : ℤ) (c : ℤ) (k : ℤ) (n : ℤ) (by positivity) (by positivity)
      (by positivity) hn'
    push_cast at this ⊢
    exact this
  have h2 := sum_range_sub (fun n : ℕ => sG a b c k (n : ℤ)) (a + 1)
  simp only [Nat.cast_add, Nat.cast_one] at h2
  have h3 : sG a b c k ((a : ℤ) + 1) = 0 := by
    unfold sG
    rw [show (a : ℤ) - ((a : ℤ) + 1) = -1 by ring, rf_zero_of_neg (by norm_num)]
    simp
  have h4 : sG a b c k ((0 : ℕ) : ℤ) = 0 := by
    unfold sG
    rw [show ((0 : ℕ) : ℤ) - (k : ℤ) - 1 = -((k : ℤ) + 1) by push_cast; ring,
      rf_zero_of_neg (m := -((k : ℤ) + 1)) (by omega)]
    simp
  rw [h2, h3, h4, sub_zero] at h
  linarith

/-- The right-hand side as a product of binomials, in reciprocal-factorial form. -/
def sR (a b c k : ℤ) : ℚ :=
  (fct (a + b) * rf (a + k) * rf (b - k)) * (fct (a + c) * rf (c + k) * rf (a - k))
    * (fct (b + c) * rf (b + k) * rf (c - k))

lemma sR_rec (a b c k : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((c : ℚ) + k + 1) * ((c : ℚ) - k + 1) * sR a b (c + 1) k
      = ((a : ℚ) + c + 1) * ((b : ℚ) + c + 1) * sR a b c k := by
  unfold sR
  have f1 := fct_rec (a + c) (a + (c + 1)) (by ring) (by omega)
  have f2 := fct_rec (b + c) (b + (c + 1)) (by ring) (by omega)
  have r1 := rf_rec (c + k) (c + 1 + k) (by ring)
  have r2 := rf_rec (c - k) (c + 1 - k) (by ring)
  rw [f1, f2, r1, r2]
  push_cast
  ring

lemma sSum_zero_of_lt (a b c k : ℕ) (h : c < k) : sSum a b c k = 0 := by
  unfold sSum
  refine sum_eq_zero fun n _ => ?_
  unfold sT
  by_cases hn : (n : ℤ) < k
  · rw [rf_zero_of_neg (m := (n : ℤ) - k) (by omega)]; ring
  · rw [rf_zero_of_neg (m := (c : ℤ) - n) (by omega)]; ring

lemma sR_zero_of_lt (a b c k : ℕ) (h : c < k) : sR a b c k = 0 := by
  unfold sR
  rw [rf_zero_of_neg (m := (c : ℤ) - k) (by omega)]; ring

lemma sSum_base (a b k : ℕ) (ha : k ≤ a) (hb : k ≤ b) : sSum a b k k = sR a b k k := by
  unfold sSum
  rw [sum_eq_single k]
  · unfold sT sR
    have e2 := fct_mul_rf ((a : ℤ) + k) (by positivity)
    have e3 := fct_mul_rf ((b : ℤ) + k) (by positivity)
    have e5 : rf (0 : ℤ) = 1 := by simp [rf]
    simp only [show (a : ℤ) + b + k - k = a + b by ring, sub_self, e5]
    linear_combination
      (-(fct ((a : ℤ) + b) * rf ((a : ℤ) - k) * rf ((b : ℤ) - k) * rf ((k : ℤ) + k))
        * (fct ((b : ℤ) + k) * rf ((b : ℤ) + k))) * e2
      + (-(fct ((a : ℤ) + b) * rf ((a : ℤ) - k) * rf ((b : ℤ) - k) * rf ((k : ℤ) + k))) * e3
  · intro n hn hne
    unfold sT
    rcases lt_or_gt_of_ne (show (n : ℤ) ≠ k by exact_mod_cast hne) with h | h
    · rw [rf_zero_of_neg (m := (n : ℤ) - k) (by omega)]; ring
    · rw [rf_zero_of_neg (m := (k : ℤ) - n) (by omega)]; ring
  · intro h; exfalso; apply h; simp; omega

lemma sSum_eq_sR (a b k : ℕ) (ha : k ≤ a) (hb : k ≤ b) (c : ℕ) :
    sSum a b c k = sR a b c k := by
  by_cases hc : c < k
  · rw [sSum_zero_of_lt a b c k hc, sR_zero_of_lt a b c k hc]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hc)
    induction j with
    | zero => simpa using sSum_base a b k ha hb
    | succ j ih =>
      have ih' := ih (by omega)
      have h1 := sSum_rec a b (k + j) k
      have h2 := sR_rec a b ((k + j : ℕ) : ℤ) k (by positivity) (by positivity) (by positivity)
      have hpos : ((↑(k + j : ℕ) : ℚ) + k + 1) * ((↑(k + j : ℕ) : ℚ) - k + 1) ≠ 0 := by
        push_cast
        have : (0 : ℚ) < (k : ℚ) + j + k + 1 := by positivity
        have : (0 : ℚ) < (j : ℚ) + 1 := by positivity
        nlinarith [mul_pos ‹(0 : ℚ) < (k : ℚ) + j + k + 1› ‹(0 : ℚ) < (j : ℚ) + 1›]
      rw [ih'] at h1
      have h3 : sR (a : ℤ) (b : ℤ) (((k + j : ℕ) : ℤ) + 1) k = sR a b ((k + (j + 1) : ℕ) : ℤ) k := by
        rw [show (((k + j : ℕ) : ℤ) + 1) = ((k + (j + 1) : ℕ) : ℤ) by push_cast; ring]
      rw [h3] at h2
      have h4 : sSum a b (k + j + 1) k = sSum a b (k + (j + 1)) k := by
        congr 1
      rw [h4] at h1
      apply mul_left_cancel₀ hpos
      rw [h1]
      push_cast at h2 ⊢
      linarith

/-- Term of the sum for natural arguments. -/
lemma sT_nat (a b c k n : ℕ) (hna : n ≤ a) (hnb : n ≤ b) (hnc : n ≤ c) (hkn : k ≤ n) :
    sT a b c k n = ((a + b + c - n).factorial : ℚ) /
      ((a - n).factorial * (b - n).factorial * (c - n).factorial * (n + k).factorial
        * (n - k).factorial) := by
  unfold sT
  have e1 : (a : ℤ) + b + c - n = ((a + b + c - n : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : n ≤ a + b + c)]; ring
  have e2 : (a : ℤ) - n = ((a - n : ℕ) : ℤ) := by push_cast [Nat.cast_sub hna]; ring
  have e3 : (b : ℤ) - n = ((b - n : ℕ) : ℤ) := by push_cast [Nat.cast_sub hnb]; ring
  have e4 : (c : ℤ) - n = ((c - n : ℕ) : ℤ) := by push_cast [Nat.cast_sub hnc]; ring
  have e5 : (n : ℤ) + k = ((n + k : ℕ) : ℤ) := by push_cast; ring
  have e6 : (n : ℤ) - k = ((n - k : ℕ) : ℤ) := by push_cast [Nat.cast_sub hkn]; ring
  rw [e1, e2, e3, e4, e5, e6, fct_natCast, rf_natCast, rf_natCast, rf_natCast, rf_natCast,
    rf_natCast]
  have : ∀ m : ℕ, ((m.factorial : ℕ) : ℚ) ≠ 0 := fun m => by positivity
  field_simp

/-- CO-385 (Pfaff–Saalschütz, binomial-product form). For naturals `a b c k`,
`C(a+b,a+k) C(a+c,c+k) C(b+c,b+k) = ∑_n (a+b+c-n)! / ((a-n)!(b-n)!(c-n)!(n+k)!(n-k)!)`,
the sum running over `k ≤ n ≤ min(a,b,c)` (the range where all factorials are defined; the
formula is symmetric under `k ↦ -k`, so `k ≥ 0` is no restriction). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 203"]
theorem pfaff_saalschutz (a b c k : ℕ) :
    ((a + b).choose (a + k) : ℚ) * ((a + c).choose (c + k) : ℚ) * ((b + c).choose (b + k) : ℚ)
      = ∑ n ∈ Icc k (min a (min b c)), ((a + b + c - n).factorial : ℚ) /
        ((a - n).factorial * (b - n).factorial * (c - n).factorial * (n + k).factorial
          * (n - k).factorial) := by
  by_cases hk : k ≤ min a (min b c)
  · have ha : k ≤ a := le_trans hk (min_le_left _ _)
    have hb : k ≤ b := le_trans hk (le_trans (min_le_right _ _) (min_le_left _ _))
    have hc : k ≤ c := le_trans hk (le_trans (min_le_right _ _) (min_le_right _ _))
    have h := sSum_eq_sR a b k ha hb c
    have hL : sSum a b c k = ∑ n ∈ Icc k (min a (min b c)), ((a + b + c - n).factorial : ℚ) /
        ((a - n).factorial * (b - n).factorial * (c - n).factorial * (n + k).factorial
          * (n - k).factorial) := by
      unfold sSum
      symm
      rw [← sum_subset (s₁ := Icc k (min a (min b c))) (s₂ := range (a + 1))]
      · refine sum_congr rfl fun n hn => ?_
        rw [mem_Icc] at hn
        have := hn.2
        simp only [le_min_iff] at this
        exact (sT_nat a b c k n this.1 this.2.1 this.2.2 hn.1).symm
      · intro n hn
        rw [mem_Icc] at hn
        simp only [mem_range]
        have := hn.2
        simp only [le_min_iff] at this
        omega
      · intro n hn hn'
        rw [mem_range] at hn
        rw [mem_Icc] at hn'
        unfold sT
        by_cases hnk : n < k
        · rw [rf_zero_of_neg (m := (n : ℤ) - k) (by omega)]; ring
        · rcases le_or_gt n b with hnb | hnb
          · have hnc : c < n := by
              by_contra hcc
              exact hn' ⟨not_lt.1 hnk, by simp only [le_min_iff]; omega⟩
            rw [rf_zero_of_neg (m := (c : ℤ) - n) (by omega)]; ring
          · rw [rf_zero_of_neg (m := (b : ℤ) - n) (by omega)]; ring
    rw [← hL, h]
    unfold sR
    have b1 := binom_eq (a + b) (a + k)
    have b2 := binom_eq (a + c) (c + k)
    have b3 := binom_eq (b + c) (b + k)
    rw [b1, b2, b3]
    push_cast
    rw [show (a : ℤ) + b - (a + k) = b - k by ring, show (a : ℤ) + c - (c + k) = a - k by ring,
      show (b : ℤ) + c - (b + k) = c - k by ring]
  · rw [Icc_eq_empty hk, sum_empty]
    simp only [le_min_iff, not_and_or, not_le] at hk
    rcases hk with h | h | h
    · rw [Nat.choose_eq_zero_of_lt (n := a + c) (k := c + k) (by omega)]; simp
    · rw [Nat.choose_eq_zero_of_lt (n := a + b) (k := a + k) (by omega)]; simp
    · rw [Nat.choose_eq_zero_of_lt (n := b + c) (k := b + k) (by omega)]; simp

end UndergradKB.Combinatorics.AeqB.Identities3
