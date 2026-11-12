import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Ring.Pow
import UndergradKB.Common.Attr

/-!
# Polynomial bump functions (Morris, Lemmas 12.1.3 and 12.1.4)

Auxiliary steps of the book's proof of the Weierstrass theorem: the sequence `(1 - U^n)^(k^n)` tends to
`1` where `U < 1/k` and to `0` where `U > 1/k`, and the resulting polynomials which are close to `1`
on `[a, d]` and close to `0` on `[c, b]`.
-/

namespace UndergradKB.Topology

open Filter Polynomial
open scoped _root_.Topology

/-- Pointwise limit `1` of `(1 - u^n)^(k^n)` for `0 < u < 1/k`. -/
theorem tendsto_bump_pow_one {u : ℝ} {k : ℕ} (hk : 0 < k) (hu0 : 0 < u) (hu : u < 1 / k) :
    Tendsto (fun n : ℕ => (1 - u ^ n) ^ (k ^ n)) atTop (𝓝 1) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hku : (k : ℝ) * u < 1 := by rwa [lt_div_iff₀ hk', mul_comm] at hu
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hu1 : u < 1 := by
    calc u < 1 / k := hu
      _ ≤ 1 := by rw [div_le_one hk']; exact hk1
  have hlim : Tendsto (fun n : ℕ => 1 - ((k : ℝ) * u) ^ n) atTop (𝓝 1) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hk'.le hu0.le) hku
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · have hun : u ^ n ≤ 1 := pow_le_one₀ hu0.le hu1.le
    have := one_add_mul_le_pow (a := -(u ^ n)) (by linarith) (k ^ n)
    have e : (1 : ℝ) + ((k ^ n : ℕ) : ℝ) * -(u ^ n) = 1 - ((k : ℝ) * u) ^ n := by
      push_cast; rw [mul_pow]; ring
    rw [e] at this
    simpa [sub_eq_add_neg] using this
  · have hun : u ^ n ≤ 1 := pow_le_one₀ hu0.le hu1.le
    exact pow_le_one₀ (by linarith) (by linarith [pow_nonneg hu0.le n])

/-- Pointwise limit `0` of `(1 - u^n)^(k^n)` for `1/k < u < 1`. -/
theorem tendsto_bump_pow_zero {u : ℝ} {k : ℕ} (hk : 0 < k) (hu : 1 / k < u) (hu1 : u < 1) :
    Tendsto (fun n : ℕ => (1 - u ^ n) ^ (k ^ n)) atTop (𝓝 0) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hku : 1 < (k : ℝ) * u := by rwa [div_lt_iff₀ hk', mul_comm] at hu
  have hu0 : 0 < u := lt_trans (by positivity) hu
  have hlim : Tendsto (fun n : ℕ => (1 + ((k : ℝ) * u) ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop_atTop_of_one_lt hku))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => ?_) (fun n => ?_)
  · have hun : u ^ n ≤ 1 := pow_le_one₀ hu0.le hu1.le
    exact pow_nonneg (by linarith) _
  · have hv0 : 0 ≤ u ^ n := pow_nonneg hu0.le n
    have hun : u ^ n ≤ 1 := pow_le_one₀ hu0.le hu1.le
    set v := u ^ n with hv
    set N := k ^ n with hN
    have hb : (1 : ℝ) + (N : ℝ) * v ≤ (1 + v) ^ N := one_add_mul_le_pow (by linarith) N
    have e : (N : ℝ) * v = ((k : ℝ) * u) ^ n := by
      rw [hN, hv]; push_cast; rw [mul_pow]
    have h1 : (1 - v) ^ N * (1 + v) ^ N ≤ 1 := by
      rw [← mul_pow]
      apply pow_le_one₀
      · nlinarith
      · nlinarith
    have hpos : 0 ≤ (1 - v) ^ N := pow_nonneg (by linarith) _
    have hp : (0 : ℝ) < 1 + (N : ℝ) * v := by positivity
    rw [← e]
    have h2 : (1 - v) ^ N * (1 + (N : ℝ) * v) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hb hpos) h1
    calc (1 - v) ^ N = (1 - v) ^ N * (1 + (N : ℝ) * v) / (1 + (N : ℝ) * v) := by
          field_simp
      _ ≤ 1 / (1 + (N : ℝ) * v) := div_le_div_of_nonneg_right h2 hp.le
      _ = (1 + (N : ℝ) * v)⁻¹ := one_div _

/-- Morris, Topology Without Tears, Lemma 12.1.3 (TP-331). For `U : X → ℝ` with `0 < U x < 1`,
disjoint `A, B ⊆ X`, `U < 1/k` on `A` and `U > 1/k` on `B`: `(1 - U x ^ n)^(k^n)` tends to `1` on `A`
and to `0` on `B`. -/
@[kb "morris2024" "Lemma 12.1.3, p. 358"]
theorem tendsto_bump_pow {X : Type*} (U : X → ℝ) (hU : ∀ x, 0 < U x ∧ U x < 1) (A B : Set X)
    (hAB : Disjoint A B) {k : ℕ} (hk : 0 < k) (hA : ∀ x ∈ A, U x < 1 / k)
    (hB : ∀ x ∈ B, 1 / (k : ℝ) < U x) :
    (∀ x ∈ A, Tendsto (fun n : ℕ => (1 - U x ^ n) ^ (k ^ n)) atTop (𝓝 1)) ∧
      (∀ x ∈ B, Tendsto (fun n : ℕ => (1 - U x ^ n) ^ (k ^ n)) atTop (𝓝 0)) := by
  have _ := hAB
  exact ⟨fun x hx => tendsto_bump_pow_one hk (hU x).1 (hA x hx),
    fun x hx => tendsto_bump_pow_zero hk (hB x hx) (hU x).2⟩

/-- The affine function `U` of the proof of Lemma 12.1.4. -/
noncomputable def bumpU (a b c d : ℝ) (x : ℝ) : ℝ := 1 / 2 + (x - (c + d) / 2) / (2 * (b - a))

/-- The polynomials `(1 - U^n)^(2^n)` of the proof of Lemma 12.1.4. -/
noncomputable def bumpPoly (a b c d : ℝ) (n : ℕ) : ℝ[X] :=
  (1 - (C (1 / 2 - ((c + d) / 2) / (2 * (b - a))) + C (1 / (2 * (b - a))) * X) ^ n) ^ (2 ^ n)

theorem bumpPoly_eval (a b c d : ℝ) (n : ℕ) (x : ℝ) :
    (bumpPoly a b c d n).eval x = (1 - bumpU a b c d x ^ n) ^ (2 ^ n) := by
  simp only [bumpPoly, bumpU, eval_pow, eval_sub, eval_one, eval_add, eval_C, eval_mul, eval_X]
  congr 3
  ring

theorem bumpU_bounds {a b c d : ℝ} (had : a < d) (hdc : d < c) (hcb : c < b) {x : ℝ}
    (hx : x ∈ Set.Icc a b) : 0 < bumpU a b c d x ∧ bumpU a b c d x < 1 := by
  have hba : 0 < b - a := by linarith
  unfold bumpU
  constructor
  · have : -(1 / 2 : ℝ) < (x - (c + d) / 2) / (2 * (b - a)) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [hx.1, hx.2]
    linarith
  · have : (x - (c + d) / 2) / (2 * (b - a)) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hx.1, hx.2]
    linarith

theorem bumpU_mono (a b c d : ℝ) (hab : a < b) {x y : ℝ} (hxy : x ≤ y) :
    bumpU a b c d x ≤ bumpU a b c d y := by
  unfold bumpU
  have : 0 < 2 * (b - a) := by linarith
  have := div_le_div_of_nonneg_right (show x - (c + d) / 2 ≤ y - (c + d) / 2 by linarith) this.le
  linarith

/-- Morris, Topology Without Tears, Lemma 12.1.4 (TP-331). For `a < d < c < b` and `η > 0` there is a
sequence of polynomials `p n` with `0 ≤ p n ≤ 1` on `[a, b]`, tending pointwise to `1` on `[a, d]` and
to `0` on `[c, b]`, and which (for all large `n`) are `≥ 1 - η` on `[a, d]` and `≤ η` on `[c, b]`. -/
@[kb "morris2024" "Lemma 12.1.4, p. 359"]
theorem exists_bump_polynomials {a b c d : ℝ} (had : a < d) (hdc : d < c) (hcb : c < b) {η : ℝ}
    (hη : 0 < η) :
    ∃ p : ℕ → ℝ[X],
      (∀ n, ∀ x ∈ Set.Icc a b, 0 ≤ (p n).eval x ∧ (p n).eval x ≤ 1) ∧
      (∀ x ∈ Set.Icc a d, Tendsto (fun n => (p n).eval x) atTop (𝓝 1)) ∧
      (∀ x ∈ Set.Icc c b, Tendsto (fun n => (p n).eval x) atTop (𝓝 0)) ∧
      (∀ᶠ n in atTop, (∀ x ∈ Set.Icc a d, 1 - η ≤ (p n).eval x) ∧
        ∀ x ∈ Set.Icc c b, (p n).eval x ≤ η) := by
  have hab : a < b := by linarith
  have hhalf_a : ∀ x ∈ Set.Icc a d, bumpU a b c d x < 1 / (2 : ℕ) := by
    intro x hx
    have hba : 0 < b - a := by linarith
    unfold bumpU
    have : (x - (c + d) / 2) / (2 * (b - a)) < 0 := by
      apply div_neg_of_neg_of_pos <;> linarith [hx.2]
    push_cast; linarith
  have hhalf_b : ∀ x ∈ Set.Icc c b, 1 / ((2 : ℕ) : ℝ) < bumpU a b c d x := by
    intro x hx
    have hba : 0 < b - a := by linarith
    unfold bumpU
    have : 0 < (x - (c + d) / 2) / (2 * (b - a)) := by
      apply div_pos <;> linarith [hx.1]
    push_cast; linarith
  have hlimA : ∀ x ∈ Set.Icc a d,
      Tendsto (fun n : ℕ => (bumpPoly a b c d n).eval x) atTop (𝓝 1) := by
    intro x hx
    simp only [bumpPoly_eval]
    exact tendsto_bump_pow_one (k := 2) (by norm_num)
      (bumpU_bounds had hdc hcb ⟨hx.1, by linarith [hx.2]⟩).1 (hhalf_a x hx)
  have hlimB : ∀ x ∈ Set.Icc c b,
      Tendsto (fun n : ℕ => (bumpPoly a b c d n).eval x) atTop (𝓝 0) := by
    intro x hx
    simp only [bumpPoly_eval]
    exact tendsto_bump_pow_zero (k := 2) (by norm_num) (hhalf_b x hx)
      (bumpU_bounds had hdc hcb ⟨by linarith [hx.1], hx.2⟩).2
  refine ⟨bumpPoly a b c d, ?_, hlimA, hlimB, ?_⟩
  · intro n x hx
    rw [bumpPoly_eval]
    obtain ⟨h0, h1⟩ := bumpU_bounds had hdc hcb hx
    have : 0 ≤ bumpU a b c d x ^ n := pow_nonneg h0.le n
    have : bumpU a b c d x ^ n ≤ 1 := pow_le_one₀ h0.le h1.le
    exact ⟨pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith)⟩
  · have e1 : ∀ᶠ n in atTop, 1 - η < (bumpPoly a b c d n).eval d :=
      (tendsto_order.1 (hlimA d ⟨had.le, le_rfl⟩)).1 _ (by linarith)
    have e2 : ∀ᶠ n in atTop, (bumpPoly a b c d n).eval c < η :=
      (tendsto_order.1 (hlimB c ⟨le_rfl, hcb.le⟩)).2 _ hη
    filter_upwards [e1, e2] with n h1 h2
    have mono : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
        (bumpPoly a b c d n).eval y ≤ (bumpPoly a b c d n).eval x := by
      intro x y hx hy hxy
      rw [bumpPoly_eval, bumpPoly_eval]
      obtain ⟨hx0, _⟩ := bumpU_bounds had hdc hcb hx
      obtain ⟨hy0, hy1⟩ := bumpU_bounds had hdc hcb hy
      have hm := bumpU_mono a b c d hab hxy
      have hpn : bumpU a b c d x ^ n ≤ bumpU a b c d y ^ n := pow_le_pow_left₀ hx0.le hm n
      have : bumpU a b c d y ^ n ≤ 1 := pow_le_one₀ hy0.le hy1.le
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · exact (h1.trans_le (mono x d ⟨hx.1, by linarith [hx.2]⟩ ⟨by linarith, by linarith⟩ hx.2)).le
    · exact ((mono c x ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1).trans h2.le)

/-- Morris, Topology Without Tears, Lemma 12.1.4 (TP-331), the single-polynomial form: there is a
polynomial `p` with `0 ≤ p ≤ 1` on `[a,b]`, `p ≥ 1 - η` on `[a,d]` and `p ≤ η` on `[c,b]`. -/
@[kb "morris2024" "Lemma 12.1.4, p. 359"]
theorem exists_bump_polynomial {a b c d : ℝ} (had : a < d) (hdc : d < c) (hcb : c < b) {η : ℝ}
    (hη : 0 < η) :
    ∃ p : ℝ[X], (∀ x ∈ Set.Icc a b, 0 ≤ p.eval x ∧ p.eval x ≤ 1) ∧
      (∀ x ∈ Set.Icc a d, 1 - η ≤ p.eval x) ∧ (∀ x ∈ Set.Icc c b, p.eval x ≤ η) := by
  obtain ⟨p, h1, -, -, h4⟩ := exists_bump_polynomials had hdc hcb hη
  obtain ⟨n, hn1, hn2⟩ := h4.exists
  exact ⟨p n, h1 n, hn1, hn2⟩

end UndergradKB.Topology
