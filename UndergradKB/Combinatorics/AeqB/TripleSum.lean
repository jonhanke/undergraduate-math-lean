import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Identities3

namespace UndergradKB.Combinatorics.AeqB

open Finset
open scoped Nat

/-! ### The summand `F(n,m)` and the telescoping term `G(n,m)` -/

/-- `F(n,m) = (n-m)! 3^(n-3m) / (m!^2 (n-3m)!)` for `3m ≤ n`, and `0` otherwise
(this equals `C(2m,m) C(n-m,2m) 3^(n-3m)`). -/
noncomputable def tbF (n m : ℕ) : ℚ :=
  if 3 * m ≤ n then ((n - m)! : ℚ) * 3 ^ (n - 3 * m) / ((m ! : ℚ) ^ 2 * ((n - 3 * m)! : ℚ))
  else 0

/-- Telescoping term of the Zeilberger certificate, poles already cancelled. -/
noncomputable def tbG (n m : ℕ) : ℚ :=
  if 3 * m ≤ n + 2 then
    (m : ℚ) ^ 2 * ((n + 1 - m)! : ℚ) * 3 ^ (n + 2 - 3 * m)
      / (9 * (m ! : ℚ) ^ 2 * ((n + 2 - 3 * m)! : ℚ))
  else 0

lemma tbF_val (n m e a : ℕ) (h : n = 3 * m + e) (ha : a = 2 * m + e) :
    tbF n m = (a ! : ℚ) * 3 ^ e / ((m ! : ℚ) ^ 2 * (e ! : ℚ)) := by
  unfold tbF
  rw [if_pos (by omega), show n - m = a by omega, show n - 3 * m = e by omega]

lemma tbF_zero (n m : ℕ) (h : n < 3 * m) : tbF n m = 0 := by
  unfold tbF; rw [if_neg (by omega)]

lemma tbG_val (n p f a : ℕ) (h : n + 2 = 3 * (p + 1) + f) (ha : a = 2 * p + f + 1) :
    tbG n (p + 1) = (a ! : ℚ) * 3 ^ f / (9 * (p ! : ℚ) ^ 2 * (f ! : ℚ)) := by
  unfold tbG
  rw [if_pos (by omega), show n + 1 - (p + 1) = a by omega,
    show n + 2 - 3 * (p + 1) = f by omega, Nat.factorial_succ]
  have h1 : (p ! : ℚ) ≠ 0 := by positivity
  have h2 : (f ! : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma tbG_zero (n m : ℕ) (h : n + 2 < 3 * m) : tbG n m = 0 := by
  unfold tbG; rw [if_neg (by omega)]

lemma tbG_zero' (n : ℕ) : tbG n 0 = 0 := by simp [tbG]

/-- The step lemma: the telescoping identity for the certificate. -/
lemma tb_step (n m : ℕ) :
    ((n : ℚ) + 2) * tbF (n + 2) m - (5 * n + 8) * tbF (n + 1) m + 2 * (2 * n + 3) * tbF n m
      = 54 * (tbG n m - tbG n (m + 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [tbG_zero' , tbG_zero 0 (0 + 1) (by omega),
        tbF_val (0 + 2) 0 2 2 (by omega) (by omega), tbF_val (0 + 1) 0 1 1 (by omega) (by omega),
        tbF_val 0 0 0 0 (by omega) (by omega)]
      simp [Nat.factorial]
      norm_num
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [tbG_zero', tbG_val (n + 1) 0 n (n + 1) (by omega) (by omega),
        tbF_val (n + 1 + 2) 0 (n + 3) (n + 3) (by omega) (by omega),
        tbF_val (n + 1 + 1) 0 (n + 2) (n + 2) (by omega) (by omega),
        tbF_val (n + 1) 0 (n + 1) (n + 1) (by omega) (by omega)]
      have h2 : (n ! : ℚ) ≠ 0 := by positivity
      simp only [Nat.factorial_succ, Nat.factorial_zero, pow_succ]
      push_cast
      field_simp
      ring
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    by_cases h0 : n + 2 < 3 * (p + 1)
    · rw [tbF_zero (n + 2) (p + 1) h0, tbF_zero (n + 1) (p + 1) (by omega),
        tbF_zero n (p + 1) (by omega), tbG_zero n (p + 1) h0,
        tbG_zero n (p + 1 + 1) (by omega)]
      ring
    · have hp : (p ! : ℚ) ≠ 0 := by positivity
      rcases (by omega : n = 3 * p + 1 ∨ n = 3 * p + 2 ∨ n = 3 * p + 3 ∨ 3 * p + 4 ≤ n)
        with h | h | h | h
      · rw [tbF_val (n + 2) (p + 1) 0 (2 * p + 1 + 1) (by omega) (by omega),
          tbF_zero (n + 1) (p + 1) (by omega), tbF_zero n (p + 1) (by omega),
          tbG_val n p 0 (2 * p + 1) (by omega) (by omega),
          tbG_zero n (p + 1 + 1) (by omega)]
        subst h
        simp only [Nat.factorial_succ, Nat.factorial_zero, pow_succ]
        push_cast
        field_simp
        ring
      · rw [tbF_val (n + 2) (p + 1) 1 (2 * p + 2 + 1) (by omega) (by omega),
          tbF_val (n + 1) (p + 1) 0 (2 * p + 1 + 1) (by omega) (by omega),
          tbF_zero n (p + 1) (by omega),
          tbG_val n p 1 (2 * p + 1 + 1) (by omega) (by omega),
          tbG_zero n (p + 1 + 1) (by omega)]
        subst h
        simp only [Nat.factorial_succ, Nat.factorial_zero, pow_succ]
        push_cast
        field_simp
        ring
      · rw [tbF_val (n + 2) (p + 1) 2 (2 * p + 3 + 1) (by omega) (by omega),
          tbF_val (n + 1) (p + 1) 1 (2 * p + 2 + 1) (by omega) (by omega),
          tbF_val n (p + 1) 0 (2 * p + 1 + 1) (by omega) (by omega),
          tbG_val n p 2 (2 * p + 2 + 1) (by omega) (by omega),
          tbG_zero n (p + 1 + 1) (by omega)]
        subst h
        simp only [Nat.factorial_succ, Nat.factorial_zero, pow_succ]
        push_cast
        field_simp
        ring
      · obtain ⟨g, rfl⟩ : ∃ g, n = 3 * p + g + 4 := ⟨n - 3 * p - 4, by omega⟩
        have hg : (g ! : ℚ) ≠ 0 := by positivity
        have hq : ((2 * p + g)! : ℚ) ≠ 0 := by positivity
        rw [tbF_val (3 * p + g + 4 + 2) (p + 1) (g + 3) (2 * p + g + 4 + 1) (by omega) (by omega),
          tbF_val (3 * p + g + 4 + 1) (p + 1) (g + 2) (2 * p + g + 3 + 1) (by omega) (by omega),
          tbF_val (3 * p + g + 4) (p + 1) (g + 1) (2 * p + g + 2 + 1) (by omega) (by omega),
          tbG_val (3 * p + g + 4) p (g + 3) (2 * p + g + 3 + 1) (by omega) (by omega),
          tbG_val (3 * p + g + 4) (p + 1) g (2 * p + g + 2 + 1) (by omega) (by omega)]
        simp only [Nat.factorial_succ, pow_succ]
        push_cast
        field_simp
        ring

/-! ### The sum `U(n)` and its recurrence -/

/-- `U(n) = ∑_m F(n,m)`. -/
noncomputable def tbU (n : ℕ) : ℚ := ∑ m ∈ range (n + 1), tbF n m

/-- `T(n) = ∑_{j ≤ n} C(2j,j)`. -/
def tbT (n : ℕ) : ℚ := ∑ j ∈ range (n + 1), ((2 * j).choose j : ℚ)

lemma tbU_ext (n M : ℕ) (hM : n + 1 ≤ M) : ∑ m ∈ range M, tbF n m = tbU n := by
  symm
  apply Finset.sum_subset (Finset.range_mono hM)
  intro m _ hm
  apply tbF_zero
  simp at hm
  omega

lemma tbU_rec (n : ℕ) :
    ((n : ℚ) + 2) * tbU (n + 2) - (5 * n + 8) * tbU (n + 1) + 2 * (2 * n + 3) * tbU n = 0 := by
  rw [← tbU_ext (n + 2) (n + 3) (by omega), ← tbU_ext (n + 1) (n + 3) (by omega),
    ← tbU_ext n (n + 3) (by omega)]
  have h := Finset.sum_congr (s₁ := range (n + 3)) rfl (fun m _ => tb_step n m)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [h, ← Finset.sum_sub_distrib, Finset.sum_range_sub',tbG_zero', tbG_zero n (n + 3) (by omega)]
  ring

lemma tbT_rec (n : ℕ) :
    ((n : ℚ) + 2) * tbT (n + 2) - (5 * n + 8) * tbT (n + 1) + 2 * (2 * n + 3) * tbT n = 0 := by
  have h := Nat.succ_mul_centralBinom_succ (n + 1)
  simp only [Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((n : ℚ) + 2) * ((2 * (n + 2)).choose (n + 2) : ℚ)
      = 2 * (2 * n + 3) * ((2 * (n + 1)).choose (n + 1) : ℚ) := by
    have h2 : ((n + 1 + 1 : ℕ) : ℚ) * (((2 * (n + 1 + 1)).choose (n + 1 + 1) : ℕ) : ℚ)
        = ((2 * (2 * (n + 1) + 1) : ℕ) : ℚ) * (((2 * (n + 1)).choose (n + 1) : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at h2
    linarith
  unfold tbT
  have e1 : ∑ j ∈ range (n + 2 + 1), ((2 * j).choose j : ℚ)
      = ∑ j ∈ range (n + 1 + 1), ((2 * j).choose j : ℚ) + ((2 * (n + 2)).choose (n + 2) : ℚ) :=
    Finset.sum_range_succ _ _
  have e2 : ∑ j ∈ range (n + 1 + 1), ((2 * j).choose j : ℚ)
      = ∑ j ∈ range (n + 1), ((2 * j).choose j : ℚ) + ((2 * (n + 1)).choose (n + 1) : ℚ) :=
    Finset.sum_range_succ _ _
  rw [e1, e2]
  linear_combination h'

lemma tbU_zero : tbU 0 = 1 := by simp [tbU, tbF]
lemma tbU_one : tbU 1 = 3 := by
  simp [tbU, Finset.sum_range_succ, tbF]

lemma tbT_zero : tbT 0 = 1 := by simp [tbT]
lemma tbT_one : tbT 1 = 3 := by
  simp [tbT, Finset.sum_range_succ]; norm_num

lemma tbU_eq_tbT (n : ℕ) : tbU n = tbT n := by
  have : ∀ n, tbU n = tbT n ∧ tbU (n + 1) = tbT (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [tbU_zero, tbT_zero], by rw [tbU_one, tbT_one]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := tbU_rec k
      have h2 := tbT_rec k
      rw [ih.1, ih.2] at h1
      have hk : ((k : ℚ) + 2) ≠ 0 := by positivity
      apply mul_left_cancel₀ hk
      linarith
  exact (this n).1

lemma tbF_choose (n m : ℕ) :
    tbF n m = (((2 * m).choose m * (n - m).choose (2 * m) * 3 ^ (n - 3 * m) : ℕ) : ℚ) := by
  by_cases h : 3 * m ≤ n
  · unfold tbF
    rw [if_pos h]
    have h1 : m ≤ 2 * m := by omega
    have h2 : 2 * m ≤ n - m := by omega
    push_cast
    rw [Nat.cast_choose ℚ h1, Nat.cast_choose ℚ h2, show 2 * m - m = m by omega,
      show n - m - 2 * m = n - 3 * m by omega]
    have a1 : (m ! : ℚ) ≠ 0 := by positivity
    have a2 : ((2 * m)! : ℚ) ≠ 0 := by positivity
    have a3 : ((n - 3 * m)! : ℚ) ≠ 0 := by positivity
    field_simp
  · rw [tbF_zero n m (by omega), Nat.choose_eq_zero_of_lt (by omega : n - m < 2 * m)]
    simp

/-- `∑_{m} C(2m,m) C(n-m,2m) 3^(n-3m) = ∑_{j ≤ n} C(2j,j)`, found by the repo's executable
Zeilberger algorithm (certificate proved in `tb_step`). -/
theorem thirds_sum_eq (n : ℕ) :
    ∑ m ∈ range (n + 1), (2 * m).choose m * (n - m).choose (2 * m) * 3 ^ (n - 3 * m)
      = ∑ j ∈ range (n + 1), (2 * j).choose j := by
  apply Nat.cast_injective (R := ℚ)
  have h := tbU_eq_tbT n
  unfold tbU tbT at h
  simp only [Nat.cast_sum]
  rw [← h]
  exact (Finset.sum_congr rfl fun m _ => (tbF_choose n m).symm)

/-! ### Reduction of the triple sum to `U(n)` -/

lemma tb_sum_tri {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i), f i j
      = ∑ x ∈ (range (n + 1) ×ˢ range (n + 1)).filter (fun x => x.1 + x.2 ≤ n), f x.1 x.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp at hi ⊢
  omega

lemma tb_trinomial (N : ℕ) :
    ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1 - a),
      (N ! : ℚ) / ((a ! : ℚ) * (b ! : ℚ) * ((N - a - b)! : ℚ)) = 3 ^ N := by
  calc _ = ∑ a ∈ range (N + 1), (N.choose a : ℚ) * 2 ^ (N - a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have haN : a ≤ N := by simp at ha; omega
        rw [show N + 1 - a = (N - a) + 1 by omega]
        have h2 : ∑ b ∈ range (N - a + 1), (N ! : ℚ) / ((a ! : ℚ) * (b ! : ℚ) * ((N - a - b)! : ℚ))
            = (N.choose a : ℚ) * ∑ b ∈ range (N - a + 1), (((N - a).choose b : ℕ) : ℚ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          have hb' : b ≤ N - a := by simp at hb; omega
          rw [Nat.cast_choose ℚ haN, Nat.cast_choose ℚ hb']
          have a1 : (a ! : ℚ) ≠ 0 := by positivity
          have a2 : (b ! : ℚ) ≠ 0 := by positivity
          have a3 : ((N - a - b)! : ℚ) ≠ 0 := by positivity
          have a4 : ((N - a)! : ℚ) ≠ 0 := by positivity
          field_simp
        rw [h2]
        congr 1
        have := Nat.sum_range_choose (N - a)
        exact_mod_cast this
    _ = 3 ^ N := by
        have h := add_pow (1 : ℚ) 2 N
        rw [show (1 : ℚ) + 2 = 3 by norm_num] at h
        rw [h]
        apply Finset.sum_congr rfl
        intro m _
        simp only [one_pow, one_mul]
        ring

lemma tb_pfaff_pt (n i j : ℕ) (h : i + j ≤ n) :
    ((((i + j).choose i * (j + (n - i - j)).choose j * ((n - i - j) + i).choose (n - i - j) : ℕ))
        : ℚ)
      = ∑ m ∈ range (n + 1), if (m ≤ i ∧ m ≤ j ∧ m ≤ n - i - j) then
          ((n - m)! : ℚ) / ((i - m)! * (j - m)! * (n - i - j - m)! * (m ! : ℚ) * (m ! : ℚ))
        else 0 := by
  obtain ⟨k, hk⟩ : ∃ k, k = n - i - j := ⟨_, rfl⟩
  have hn : i + j + k = n := by omega
  rw [← hk]
  have hp := Identities3.pfaff_saalschutz i j k 0
  simp only [add_zero, Nat.sub_zero] at hp
  rw [hn] at hp
  rw [← Finset.sum_filter]
  have hset : (range (n + 1)).filter (fun m => m ≤ i ∧ m ≤ j ∧ m ≤ k)
      = Icc 0 (min i (min j k)) := by
    ext m
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [hset]
  have e : ((((i + j).choose i * (j + k).choose j * (k + i).choose k : ℕ)) : ℚ)
      = ((i + j).choose i : ℚ) * ((i + k).choose k : ℚ) * ((j + k).choose j : ℚ) := by
    push_cast
    rw [add_comm k i]
    ring
  rw [e, hp]

lemma tb_slice (n m : ℕ) :
    ∑ x ∈ (range (n + 1) ×ˢ range (n + 1)).filter (fun x => x.1 + x.2 ≤ n),
      (if (m ≤ x.1 ∧ m ≤ x.2 ∧ m ≤ n - x.1 - x.2) then
        ((n - m)! : ℚ) / ((x.1 - m)! * (x.2 - m)! * (n - x.1 - x.2 - m)! * (m ! : ℚ) * (m ! : ℚ))
      else 0) = tbF n m := by
  by_cases h : 3 * m ≤ n
  · rw [← Finset.sum_filter]
    have a1 : (m ! : ℚ) ≠ 0 := by positivity
    have a3 : ((n - 3 * m)! : ℚ) ≠ 0 := by positivity
    have hs : ∑ x ∈ ((range (n + 1) ×ˢ range (n + 1)).filter (fun x => x.1 + x.2 ≤ n)).filter
          (fun x => m ≤ x.1 ∧ m ≤ x.2 ∧ m ≤ n - x.1 - x.2),
        ((n - m)! : ℚ) / ((x.1 - m)! * (x.2 - m)! * (n - x.1 - x.2 - m)! * (m ! : ℚ) * (m ! : ℚ))
        = ∑ y ∈ (range (n - 3 * m + 1) ×ˢ range (n - 3 * m + 1)).filter
              (fun y => y.1 + y.2 ≤ n - 3 * m),
          ((n - m)! : ℚ) / ((m ! : ℚ) * (m ! : ℚ) * ((n - 3 * m)! : ℚ))
            * (((n - 3 * m)! : ℚ) / ((y.1 ! : ℚ) * (y.2 ! : ℚ) * ((n - 3 * m - y.1 - y.2)! : ℚ))) := by
      apply Finset.sum_nbij' (fun x => (x.1 - m, x.2 - m)) (fun y => (y.1 + m, y.2 + m))
      · intro x hx
        simp only [mem_filter, mem_product, mem_range] at hx ⊢
        omega
      · intro y hy
        simp only [mem_filter, mem_product, mem_range] at hy ⊢
        omega
      · intro x hx
        simp only [mem_filter, mem_product, mem_range] at hx
        ext <;> simp <;> omega
      · intro y hy
        ext <;> simp
      · intro x hx
        simp only [mem_filter, mem_product, mem_range] at hx
        rw [show n - 3 * m - (x.1 - m) - (x.2 - m) = n - x.1 - x.2 - m by omega]
        have b1 : ((x.1 - m)! : ℚ) ≠ 0 := by positivity
        have b2 : ((x.2 - m)! : ℚ) ≠ 0 := by positivity
        have b3 : ((n - x.1 - x.2 - m)! : ℚ) ≠ 0 := by positivity
        field_simp
    rw [hs, ← Finset.mul_sum, ← tb_sum_tri (n - 3 * m) (fun a b =>
      ((n - 3 * m)! : ℚ) / ((a ! : ℚ) * (b ! : ℚ) * ((n - 3 * m - a - b)! : ℚ))),
      tb_trinomial]
    unfold tbF
    rw [if_pos h, show n - 3 * m = n - 3 * m from rfl]
    field_simp
  · rw [tbF_zero n m (by omega)]
    apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg]
    simp only [mem_filter, mem_product, mem_range] at hx
    omega

/-- Reduction lemma: the triple sum equals `∑_m C(2m,m) C(n-m,2m) 3^(n-3m)`. -/
theorem triple_sum_eq_thirds (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
      (i + j).choose i * (j + (n - i - j)).choose j * ((n - i - j) + i).choose (n - i - j)
      = ∑ m ∈ range (n + 1), (2 * m).choose m * (n - m).choose (2 * m) * 3 ^ (n - 3 * m) := by
  refine Eq.trans (tb_sum_tri n _) ?_
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun x hx =>
    tb_pfaff_pt n x.1 x.2 (by simp only [mem_filter] at hx; exact hx.2))) ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl (fun m _ => tb_slice n m)) ?_
  exact Finset.sum_congr rfl (fun m _ => tbF_choose n m)

/-- CO-043. The triple sum of products of three binomials `C(i+j,i) C(j+k,j) C(k+i,k)` over all
`i + j + k = n` (here `k = n - i - j`) equals the partial sum `∑_{j ≤ n} C(2j,j)` of the central
binomial coefficients. Proof: MacMahon's formula (Pfaff–Saalschütz with `k = 0`) reduces the sum
to `∑_m C(2m,m) C(n-m,2m) 3^(n-3m)`, which is shown to satisfy the same recurrence as the
partial sums; the Zeilberger certificate was found by the repo's executable Zeilberger algorithm. -/
@[kb "petkovsekwilfzeilberger1996" "Eq (2.2.2), p. 33"]
theorem triple_binom_sum (n : ℕ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
      (i + j).choose i * (j + (n - i - j)).choose j * ((n - i - j) + i).choose (n - i - j)
      = ∑ j ∈ range (n + 1), (2 * j).choose j :=
  (triple_sum_eq_thirds n).trans (thirds_sum_eq n)

end UndergradKB.Combinatorics.AeqB
