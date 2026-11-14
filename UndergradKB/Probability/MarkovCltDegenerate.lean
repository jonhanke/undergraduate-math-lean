import UndergradKB.Common.Attr
import UndergradKB.Probability.MarkovClt

/-!
# Probability: the degenerate case of the central limit theorem for Markov chains (Theorem 11.17)

For an ergodic chain with fixed vector `w` and fundamental matrix `Z`, the number
`σ_j² = 2 w_j z_jj - w_j - w_j²` of equation (11.10) equals `∑_m w_m ∑_l p_ml (h_l - (P h)_m)²`, where
`h = Z f` solves the Poisson equation `h - P h = f` for the centred indicator `f = 1_j - w_j`. Hence
`σ_j² ≥ 0` always, and if `σ_j² = 0` then `h_l = (P h)_m` along every possible transition `m → l`, so the
centred number of visits telescopes: `S_j^(n) - n w_j = h(x_0) - (P h)(x_n) + w_j` on every path of positive
probability. The number of visits then stays within a bounded distance of `n w_j`, and no normal limit is
possible; this is the case the book's Theorem 11.17 tacitly excludes (`markov_clt` assumes `σ_j² > 0`).
-/

open Finset Matrix

namespace UndergradKB.Probability

open MarkovClt

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The variance identity: `σ_j² = ∑_m w_m ∑_l p_ml (h_l - (P h)_m)²` with `h = Z (1_j - w_j)`. -/
theorem markov_sigma_sq_eq {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {w : S → ℝ}
    (hsum : ∑ j, w j = 1) (hfix : IsFixedRow P w) (hunit : IsUnit (1 - P + rowsMatrix w)) (j : S) :
    2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2 =
      ∑ m, w m * ∑ l, P m l *
        ((((1 - P + rowsMatrix w)⁻¹ *ᵥ fun l => (if l = j then 1 else 0) - w j) l -
          (P *ᵥ ((1 - P + rowsMatrix w)⁻¹ *ᵥ fun l => (if l = j then 1 else 0) - w j)) m) ^ 2) := by
  set Z := (1 - P + rowsMatrix w)⁻¹ with hZ
  set f : S → ℝ := fun l => (if l = j then 1 else 0) - w j with hf
  have hf0 : ∑ k, w k * f k = 0 := by
    simp only [hf, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
      if_true, ← sum_mul, hsum, one_mul, sub_self]
  obtain ⟨hh, hwh⟩ := poisson_solve hsum hfix hunit f hf0
  set h := Z *ᵥ f with hhdef
  set ph := P *ᵥ h with hph
  have hhj : h j = Z j j - w j := by
    have : h j = ∑ l, Z j l * f l := rfl
    rw [this]
    simp only [hf, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ, if_true,
      ← sum_mul]
    rw [fundamental_row_sum hP hsum hunit j, one_mul]
  have hwfh : ∑ l, w l * (f l * h l) = w j * h j := by
    have : ∀ l, w l * (f l * h l) = (if l = j then w l * h l else 0) - w j * (w l * h l) := by
      intro l; simp only [hf]; split_ifs <;> ring
    rw [sum_congr rfl fun l _ => this l, sum_sub_distrib, sum_ite_eq', if_pos (mem_univ j), ← mul_sum,
      hwh, mul_zero, sub_zero]
  have hwff : ∑ l, w l * f l ^ 2 = w j - w j ^ 2 := by
    have : ∀ l, w l * f l ^ 2 = (if l = j then w l * (1 - 2 * w j) else 0) + w j ^ 2 * w l := by
      intro l; simp only [hf]; split_ifs <;> ring
    rw [sum_congr rfl fun l _ => this l, sum_add_distrib, sum_ite_eq', if_pos (mem_univ j), ← mul_sum, hsum]
    ring
  -- the inner sum
  have hrow : ∀ m, ∑ l, P m l = 1 := fun m => by
    simpa [mulVec, dotProduct] using sum_row_of_mem_rowStochastic hP m
  have hinner : ∀ m, ∑ l, P m l * (h l - ph m) ^ 2 = (P *ᵥ fun l => h l ^ 2) m - ph m ^ 2 := by
    intro m
    have e1 : ph m = ∑ l, P m l * h l := rfl
    have e2 : (P *ᵥ fun l => h l ^ 2) m = ∑ l, P m l * h l ^ 2 := rfl
    have : ∀ l, P m l * (h l - ph m) ^ 2 =
        P m l * h l ^ 2 - 2 * ph m * (P m l * h l) + ph m ^ 2 * P m l := fun l => by ring
    rw [sum_congr rfl fun l _ => this l, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
      hrow, ← e1, e2]
    ring
  have hphm : ∀ m, ph m = h m - f m := fun m => by have := hh m; simp only [hph]; linarith
  rw [sum_congr rfl fun m _ => by rw [hinner m]]
  simp only [mul_sub, sum_sub_distrib, sum_w_mulVec hfix (fun l => h l ^ 2), hphm]
  have e3 : ∑ m, w m * (h m - f m) ^ 2 =
      ∑ m, w m * h m ^ 2 - 2 * ∑ m, w m * (f m * h m) + ∑ m, w m * f m ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [e3, hwfh, hwff, hhj]
  ring

/-- `σ_j² ≥ 0` for every state of an ergodic chain. -/
theorem markov_sigma_sq_nonneg {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {w : S → ℝ}
    (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hfix : IsFixedRow P w)
    (hunit : IsUnit (1 - P + rowsMatrix w)) (j : S) :
    0 ≤ 2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2 := by
  rw [markov_sigma_sq_eq hP hsum hfix hunit j]
  exact sum_nonneg fun m _ => mul_nonneg (hw m).le
    (sum_nonneg fun l _ => mul_nonneg (nonneg_of_mem_rowStochastic hP) (sq_nonneg _))

variable [Nonempty S]

/-- Grinstead–Snell Theorem 11.17 (PR-121), the degenerate case. Let `P` be an ergodic chain with fixed
probability vector `w` and fundamental matrix `Z = (I - P + W)⁻¹`. Then `σ_j² = 2 w_j z_jj - w_j - w_j² ≥ 0`
for every state `j`, and if `σ_j² = 0` there is a constant `C` such that, for every initial vector `u`, every
`n` and every path `x_0, …, x_n` of positive probability, the number `S_j^(n)` of visits to `j` at the times
`0, …, n` satisfies `|S_j^(n) - n w_j| ≤ C`. So the hypothesis `σ_j² > 0` of `markov_clt` is exactly what is
needed for a normal limit. -/
@[kb "grinsteadsnell2006" "Theorem 11.17, p. 472"]
theorem markov_clt_degenerate {P : Matrix S S ℝ} (hP : IsErgodicChain P) :
    ∃ w : S → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧ IsFixedRow P w ∧ IsUnit (1 - P + rowsMatrix w) ∧
      (∀ j, 0 ≤ 2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2) ∧
      ∀ j : S, 2 * w j * (1 - P + rowsMatrix w)⁻¹ j j - w j - w j ^ 2 = 0 →
        ∃ C : ℝ, ∀ (u : S → ℝ) (n : ℕ) (x : Fin (n + 1) → S), pathProb u P n x ≠ 0 →
          |((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j| ≤ C := by
  obtain ⟨w, hpos, hsum, hfix, hunit, -⟩ := meanFirstPassage_eq_fundamental hP
  have hPs := hP.1
  refine ⟨w, hpos, hsum, hfix, hunit, markov_sigma_sq_nonneg hPs hpos hsum hfix hunit,
    fun j hσ => ?_⟩
  have hid := markov_sigma_sq_eq hPs hsum hfix hunit j
  set Z := (1 - P + rowsMatrix w)⁻¹ with hZ
  set f : S → ℝ := fun l => (if l = j then 1 else 0) - w j with hf
  have hf0 : ∑ k, w k * f k = 0 := by
    simp only [hf, mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
      if_true, ← sum_mul, hsum, one_mul, sub_self]
  obtain ⟨hh, -⟩ := poisson_solve hsum hfix hunit f hf0
  set h := Z *ᵥ f with hhdef
  set ph := P *ᵥ h with hph
  -- along every possible transition, `h l = (P h) m`
  have hzero : ∀ m l, P m l ≠ 0 → h l = ph m := by
    intro m l hml
    rw [hσ] at hid
    have h1 := (sum_eq_zero_iff_of_nonneg fun m _ => mul_nonneg (hpos m).le
      (sum_nonneg fun l _ => mul_nonneg (nonneg_of_mem_rowStochastic hPs) (sq_nonneg _))).1
      hid.symm m (mem_univ m)
    have h2 : ∑ l, P m l * (h l - ph m) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1 with h3 | h3
      · exact absurd h3 (hpos m).ne'
      · exact h3
    have h4 := (sum_eq_zero_iff_of_nonneg fun l _ => mul_nonneg
      (nonneg_of_mem_rowStochastic hPs) (sq_nonneg _)).1 h2 l (mem_univ l)
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 hml
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h5
      linarith
  refine ⟨∑ l, |h l| + ∑ l, |ph l| + 1, fun u n x hx => ?_⟩
  have hstep : ∀ k : Fin n, P (x k.castSucc) (x k.succ) ≠ 0 := by
    intro k hk
    apply hx
    unfold pathProb
    rw [prod_eq_zero (mem_univ k) hk, mul_zero]
  have hcard : ((univ.filter fun k : Fin (n + 1) => x k = j).card : ℝ) - n * w j =
      ∑ k : Fin (n + 1), f (x k) + w j := by
    simp only [hf, sum_sub_distrib, sum_boole, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hphm : ∀ m, f m = h m - ph m := fun m => by have := hh m; simp only [hph]; linarith
  have htel : ∑ k : Fin (n + 1), f (x k) = h (x 0) - ph (x (Fin.last n)) := by
    simp only [hphm, sum_sub_distrib]
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (f := fun k => ph (x k))]
    have : ∑ k : Fin n, h (x k.succ) = ∑ k : Fin n, ph (x k.castSucc) :=
      sum_congr rfl fun k _ => hzero _ _ (hstep k)
    rw [this]
    ring
  rw [hcard, htel]
  have b1 : |h (x 0)| ≤ ∑ l, |h l| :=
    single_le_sum (f := fun l => |h l|) (fun l _ => abs_nonneg _) (mem_univ _)
  have b2 : |ph (x (Fin.last n))| ≤ ∑ l, |ph l| :=
    single_le_sum (f := fun l => |ph l|) (fun l _ => abs_nonneg _) (mem_univ _)
  have b3 : w j ≤ 1 := by
    rw [← hsum]
    exact single_le_sum (f := w) (fun l _ => (hpos l).le) (mem_univ j)
  have hw0 := hpos j
  calc |h (x 0) - ph (x (Fin.last n)) + w j|
      ≤ |h (x 0)| + |ph (x (Fin.last n))| + |w j| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by rw [abs_of_pos hw0]; linarith

end UndergradKB.Probability
