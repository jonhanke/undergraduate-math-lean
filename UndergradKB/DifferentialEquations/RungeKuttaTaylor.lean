import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import UndergradKB.Common.Attr

/-! # Taylor expansions used for the order of the Runge-Kutta method (Lebl, §1.7)

* `taylor_two_sided`: Taylor's theorem of order `n` at `x₀` with remainder `N |u|^{n+1}` for `|u| ≤ 1`, where `N`
  bounds the `(n+1)`-st derivative on `[x₀ - 1, x₀ + 1]` (both signs of `u`).
* `iteratedDeriv_line`: the iterated derivative along a line `t ↦ F(p + t v)` is the iterated Fréchet derivative
  applied to `(v, …, v)`.
* `taylor2D_cubic`: a function `F` of class `C⁴` on `ℝ²` agrees near `(x₀, y₀)` with a cubic polynomial in
  `(a, b) = (x - x₀, y - y₀)` up to `K (|a| + |b|)⁴` (expand in `b`, then each coefficient in `a`).
-/

namespace UndergradKB.DifferentialEquations

open Set Finset

/-- A cubic polynomial in two variables `(a, b)`. -/
structure Cub where
  c00 : ℝ
  c10 : ℝ
  c01 : ℝ
  c20 : ℝ
  c11 : ℝ
  c02 : ℝ
  c30 : ℝ
  c21 : ℝ
  c12 : ℝ
  c03 : ℝ

/-- Evaluation of a two-variable cubic. -/
def Cub.eval (c : Cub) (a b : ℝ) : ℝ :=
  c.c00 + c.c10 * a + c.c01 * b + c.c20 * a ^ 2 + c.c11 * a * b + c.c02 * b ^ 2 + c.c30 * a ^ 3 +
    c.c21 * a ^ 2 * b + c.c12 * a * b ^ 2 + c.c03 * b ^ 3

/-- One-sided Taylor bound (`u ≥ 0`). -/
theorem taylor_one_sided {g : ℝ → ℝ} {n : ℕ} (hg : ContDiff ℝ (n + 1) g) {x₀ N : ℝ}
    (hN : ∀ z ∈ Icc (x₀ - 1) (x₀ + 1), |iteratedDeriv (n + 1) g z| ≤ N) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    |g (x₀ + u) - ∑ k ∈ range (n + 1), iteratedDeriv k g x₀ * u ^ k / k.factorial| ≤ N * u ^ (n + 1) := by
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN x₀ ⟨by linarith, by linarith⟩)
  rcases eq_or_lt_of_le hu0 with h0 | hpos
  · subst h0
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [zero_pow hk]
    · simp
  have hlt : x₀ < x₀ + u := by linarith
  have hw : ∀ k : ℕ, k ≤ n + 1 → ∀ z ∈ Icc x₀ (x₀ + u),
      iteratedDerivWithin k g (Icc x₀ (x₀ + u)) z = iteratedDeriv k g z := fun k hk z hz =>
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
      (hg.contDiffAt.of_le (by exact_mod_cast hk)) hz
  have hT := taylor_mean_remainder_bound (f := g) (a := x₀) (b := x₀ + u) (C := N) (x := x₀ + u) (n := n)
    hlt.le hg.contDiffOn (right_mem_Icc.2 hlt.le)
    (fun z hz => by
      rw [hw (n + 1) le_rfl z hz, Real.norm_eq_abs]
      exact hN z ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  rw [taylor_within_apply] at hT
  have hsum : ∑ k ∈ range (n + 1), ((k.factorial : ℝ)⁻¹ * (x₀ + u - x₀) ^ k) •
      iteratedDerivWithin k g (Icc x₀ (x₀ + u)) x₀ =
      ∑ k ∈ range (n + 1), iteratedDeriv k g x₀ * u ^ k / k.factorial := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hw k (by simp at hk; omega) x₀ (left_mem_Icc.2 hlt.le), smul_eq_mul]
    ring
  rw [hsum, Real.norm_eq_abs] at hT
  refine hT.trans ?_
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
  rw [show x₀ + u - x₀ = u by ring, div_le_iff₀ (by positivity)]
  have : 0 ≤ N * u ^ (n + 1) := by positivity
  nlinarith

/-- **Two-sided Taylor bound.**  If `g` is `C^{n+1}` and `|g^{(n+1)}| ≤ N` on `[x₀ - 1, x₀ + 1]`, then for `|u| ≤ 1`
the Taylor polynomial of degree `n` at `x₀` approximates `g (x₀ + u)` within `N |u|^{n+1}`. -/
theorem taylor_two_sided {g : ℝ → ℝ} {n : ℕ} (hg : ContDiff ℝ (n + 1) g) {x₀ N : ℝ}
    (hN : ∀ z ∈ Icc (x₀ - 1) (x₀ + 1), |iteratedDeriv (n + 1) g z| ≤ N) {u : ℝ} (hu : |u| ≤ 1) :
    |g (x₀ + u) - ∑ k ∈ range (n + 1), iteratedDeriv k g x₀ * u ^ k / k.factorial| ≤ N * |u| ^ (n + 1) := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu ⊢
    exact taylor_one_sided hg hN h hu
  · set g' : ℝ → ℝ := fun t => g (-t) with hg'
    have hg'c : ContDiff ℝ (n + 1) g' := hg.comp contDiff_neg
    have hder : ∀ k z, iteratedDeriv k g' z = (-1) ^ k * iteratedDeriv k g (-z) := fun k z => by
      rw [hg', iteratedDeriv_comp_neg, smul_eq_mul]
    have hN' : ∀ z ∈ Icc (-x₀ - 1) (-x₀ + 1), |iteratedDeriv (n + 1) g' z| ≤ N := by
      intro z hz
      rw [hder, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hN (-z) ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have := taylor_one_sided hg'c hN' (u := -u) (by linarith) (by rw [abs_of_nonpos h] at hu; linarith)
    have e1 : g' (-x₀ + -u) = g (x₀ + u) := by simp [hg']; ring_nf
    have e2 : ∑ k ∈ range (n + 1), iteratedDeriv k g' (-x₀) * (-u) ^ k / k.factorial =
        ∑ k ∈ range (n + 1), iteratedDeriv k g x₀ * u ^ k / k.factorial := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hder, neg_neg, neg_pow u k]
      have : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
      calc (-1) ^ k * iteratedDeriv k g x₀ * ((-1) ^ k * u ^ k) / k.factorial
          = ((-1) ^ k * (-1) ^ k) * (iteratedDeriv k g x₀ * u ^ k / k.factorial) := by ring
        _ = _ := by rw [this, one_mul]
    rw [e1, e2] at this
    rwa [abs_of_nonpos h]

/-- The iterated derivative along a line is the iterated Fréchet derivative applied to the direction. -/
theorem iteratedDeriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ} {n : ℕ}
    (hF : ContDiff ℝ n F) (p v : E) {k : ℕ} (hk : k ≤ n) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => F (p + t • v)) t = iteratedFDeriv ℝ k F (p + t • v) (fun _ => v) := by
  set ℓ : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hℓ
  set G : E → ℝ := fun z => F (z + p) with hG
  have hGc : ContDiff ℝ n G := hF.comp (contDiff_id.add contDiff_const)
  have hfun : (fun t : ℝ => F (p + t • v)) = G ∘ ℓ := by
    funext s; simp [hG, hℓ, add_comm]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, ContinuousLinearMap.iteratedFDeriv_comp_right ℓ hGc t
    (by exact_mod_cast hk)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hG, iteratedFDeriv_comp_add_right]
  simp [hℓ, add_comm]

/-- The function `p ↦ D^j F(p)(v, …, v)` is `C^{4-j}` for `F` of class `C⁴`. -/
lemma contDiff_iteratedFDeriv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    (hF : ContDiff ℝ 4 F) {j : ℕ} (hj : j ≤ 4) (v : E) :
    ContDiff ℝ (4 - j : ℕ) (fun p => iteratedFDeriv ℝ j F p (fun _ => v)) := by
  have h1 : ContDiff ℝ (4 - j : ℕ) (iteratedFDeriv ℝ j F) :=
    hF.iteratedFDeriv_right (by norm_cast; omega)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) ℝ (fun _ => v)).contDiff.comp h1

/-- Bound of a continuous function on the square `[x₀ - 1, x₀ + 1] × [y₀ - 1, y₀ + 1]`. -/
lemma exists_bound_square {Φ : ℝ × ℝ → ℝ} (hΦ : Continuous Φ) (x₀ y₀ : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ a z, |a| ≤ 1 → z ∈ Icc (y₀ - 1) (y₀ + 1) → |Φ (x₀ + a, z)| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x₀ - 1) (b := x₀ + 1)).prod (isCompact_Icc (a := y₀ - 1) (b := y₀ + 1))
    |>.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun a z ha hz => ?_⟩
  have hmem : (x₀ + a, z) ∈ Icc (x₀ - 1) (x₀ + 1) ×ˢ Icc (y₀ - 1) (y₀ + 1) := by
    rw [abs_le] at ha
    exact ⟨⟨by linarith, by linarith⟩, hz⟩
  exact (hM _ hmem).trans (le_max_left _ _)

/-- Taylor bound for a coefficient function `a ↦ φ(a)` of class `C^{4-j}`. -/
lemma coeff_taylor {φ : ℝ → ℝ} {j : ℕ} (hj : j ≤ 3) (hφ : ContDiff ℝ (4 - j : ℕ) φ) :
    ∃ N, 0 ≤ N ∧ ∀ a, |a| ≤ 1 →
      |φ a - ∑ i ∈ range (4 - j), iteratedDeriv i φ 0 * a ^ i / i.factorial| ≤ N * |a| ^ (4 - j) := by
  have hc : ContDiff ℝ ((3 - j + 1 : ℕ) : WithTop ℕ∞) φ := by
    rw [show 3 - j + 1 = 4 - j by omega]; exact hφ
  have hcont : Continuous (iteratedDeriv (3 - j + 1) φ) := hc.continuous_iteratedDeriv _ le_rfl
  obtain ⟨N, hN⟩ := (isCompact_Icc (a := (0 : ℝ) - 1) (b := 0 + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max N 0, le_max_right _ _, fun a ha => ?_⟩
  have := taylor_two_sided (x₀ := 0) (N := max N 0) (n := 3 - j) (u := a) (by exact_mod_cast hc)
    (fun z hz => (hN z hz).trans (le_max_left _ _)) ha
  rw [show 3 - j + 1 = 4 - j by omega, zero_add] at this
  exact this

lemma pow_le_sum_pow {a b : ℝ} (i j : ℕ) (h : i + j = 4) : |a| ^ i * |b| ^ j ≤ (|a| + |b|) ^ 4 := by
  have ha : |a| ≤ |a| + |b| := by linarith [abs_nonneg b]
  have hb : |b| ≤ |a| + |b| := by linarith [abs_nonneg a]
  calc |a| ^ i * |b| ^ j ≤ (|a| + |b|) ^ i * (|a| + |b|) ^ j := by gcongr
    _ = _ := by rw [← pow_add, h]

/-- **Cubic Taylor polynomial in two variables.**  A function of class `C⁴` on `ℝ²` agrees with a cubic in
`(a, b)` up to `K (|a| + |b|)⁴` on the square `|a|, |b| ≤ 1` around `(x₀, y₀)`. -/
theorem taylor2D_cubic {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 4 F) (x₀ y₀ : ℝ) :
    ∃ c : Cub, ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ 1 →
      |F (x₀ + a, y₀ + b) - c.eval a b| ≤ K * (|a| + |b|) ^ 4 := by
  set e2 : ℝ × ℝ := (0, 1)
  set e1 : ℝ × ℝ := (1, 0)
  set Φ : ℕ → ℝ × ℝ → ℝ := fun j p => iteratedFDeriv ℝ j F p (fun _ => e2) with hΦdef
  have hΦ : ∀ j, j ≤ 4 → ContDiff ℝ (4 - j : ℕ) (Φ j) := fun j hj =>
    contDiff_iteratedFDeriv_apply hF hj e2
  obtain ⟨M, hM0, hM⟩ := exists_bound_square (hΦ 4 le_rfl).continuous x₀ y₀
  set φ : ℕ → ℝ → ℝ := fun j a => Φ j (x₀ + a, y₀) / j.factorial with hφdef
  have hφ : ∀ j, j ≤ 4 → ContDiff ℝ (4 - j : ℕ) (φ j) := fun j hj => by
    have h1 : ContDiff ℝ (4 - j : ℕ) (fun a : ℝ => ((x₀ + a, y₀) : ℝ × ℝ)) := by fun_prop
    exact ((hΦ j hj).comp h1).div_const _
  obtain ⟨N0, hN00, hN0⟩ := coeff_taylor (by norm_num : 0 ≤ 3) (hφ 0 (by norm_num))
  obtain ⟨N1, hN10, hN1⟩ := coeff_taylor (by norm_num : 1 ≤ 3) (hφ 1 (by norm_num))
  obtain ⟨N2, hN20, hN2⟩ := coeff_taylor (by norm_num : 2 ≤ 3) (hφ 2 (by norm_num))
  obtain ⟨N3, hN30, hN3⟩ := coeff_taylor (by norm_num : 3 ≤ 3) (hφ 3 (by norm_num))
  set d : ℕ → ℕ → ℝ := fun i j => iteratedDeriv i (φ j) 0 / i.factorial with hd
  refine ⟨⟨d 0 0, d 1 0, d 0 1, d 2 0, d 1 1, d 0 2, d 3 0, d 2 1, d 1 2, d 0 3⟩,
    M + N0 + N1 + N2 + N3, by positivity, fun a b ha hb => ?_⟩
  -- expansion in `b`
  have hline : (fun s : ℝ => F (x₀ + a, s)) = fun s => F ((x₀ + a, 0) + s • e2) := by
    funext s; simp [e2]
  have hGc : ContDiff ℝ ((3 + 1 : ℕ) : WithTop ℕ∞) (fun s : ℝ => F (x₀ + a, s)) := by
    have : ContDiff ℝ 4 (fun s : ℝ => ((x₀ + a, s) : ℝ × ℝ)) := by fun_prop
    exact hF.comp this
  have hGd : ∀ k, k ≤ 4 → ∀ s, iteratedDeriv k (fun s : ℝ => F (x₀ + a, s)) s = Φ k (x₀ + a, s) := by
    intro k hk s
    rw [hline, iteratedDeriv_line hF _ _ hk s]
    simp [hΦdef, e2]
  have hb_exp := taylor_two_sided (x₀ := y₀) (N := M) (u := b) hGc
    (fun z hz => by rw [hGd 4 le_rfl z]; exact hM a z ha hz) hb
  have hsumb : ∑ k ∈ range (3 + 1), iteratedDeriv k (fun s : ℝ => F (x₀ + a, s)) y₀ * b ^ k / k.factorial =
      φ 0 a + φ 1 a * b + φ 2 a * b ^ 2 + φ 3 a * b ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      hGd 0 (by norm_num), hGd 1 (by norm_num), hGd 2 (by norm_num), hGd 3 (by norm_num)]
    simp only [hφdef, Nat.factorial]
    push_cast
    ring
  rw [hsumb] at hb_exp
  -- expansions of the coefficients in `a`
  have e0 := hN0 a ha
  have e1' := hN1 a ha
  have e2' := hN2 a ha
  have e3 := hN3 a ha
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, show 4 - 0 = 4 from rfl,
    show 4 - 1 = 3 from rfl, show 4 - 2 = 2 from rfl, show 4 - 3 = 1 from rfl] at e0 e1' e2' e3
  have hdecomp : F (x₀ + a, y₀ + b) - Cub.eval ⟨d 0 0, d 1 0, d 0 1, d 2 0, d 1 1, d 0 2, d 3 0, d 2 1, d 1 2,
      d 0 3⟩ a b =
      (F (x₀ + a, y₀ + b) - (φ 0 a + φ 1 a * b + φ 2 a * b ^ 2 + φ 3 a * b ^ 3)) +
      (φ 0 a - (iteratedDeriv 0 (φ 0) 0 * a ^ 0 / (Nat.factorial 0) + iteratedDeriv 1 (φ 0) 0 * a ^ 1 /
        (Nat.factorial 1) + iteratedDeriv 2 (φ 0) 0 * a ^ 2 / (Nat.factorial 2) +
        iteratedDeriv 3 (φ 0) 0 * a ^ 3 / (Nat.factorial 3))) +
      b * (φ 1 a - (iteratedDeriv 0 (φ 1) 0 * a ^ 0 / (Nat.factorial 0) + iteratedDeriv 1 (φ 1) 0 * a ^ 1 /
        (Nat.factorial 1) + iteratedDeriv 2 (φ 1) 0 * a ^ 2 / (Nat.factorial 2))) +
      b ^ 2 * (φ 2 a - (iteratedDeriv 0 (φ 2) 0 * a ^ 0 / (Nat.factorial 0) + iteratedDeriv 1 (φ 2) 0 * a ^ 1 /
        (Nat.factorial 1))) +
      b ^ 3 * (φ 3 a - iteratedDeriv 0 (φ 3) 0 * a ^ 0 / (Nat.factorial 0)) := by
    simp only [Cub.eval, hd]
    ring
  rw [hdecomp]
  have t1 : |b * (φ 1 a - (iteratedDeriv 0 (φ 1) 0 * a ^ 0 / (Nat.factorial 0) + iteratedDeriv 1 (φ 1) 0 *
      a ^ 1 / (Nat.factorial 1) + iteratedDeriv 2 (φ 1) 0 * a ^ 2 / (Nat.factorial 2)))| ≤
      N1 * (|a| + |b|) ^ 4 := by
    rw [abs_mul]
    calc _ ≤ |b| * (N1 * |a| ^ 3) := by gcongr
      _ = N1 * (|a| ^ 3 * |b| ^ 1) := by ring
      _ ≤ _ := by gcongr; exact pow_le_sum_pow 3 1 rfl
  have t2 : |b ^ 2 * (φ 2 a - (iteratedDeriv 0 (φ 2) 0 * a ^ 0 / (Nat.factorial 0) + iteratedDeriv 1 (φ 2) 0 *
      a ^ 1 / (Nat.factorial 1)))| ≤ N2 * (|a| + |b|) ^ 4 := by
    rw [abs_mul, abs_pow]
    calc _ ≤ |b| ^ 2 * (N2 * |a| ^ 2) := by gcongr
      _ = N2 * (|a| ^ 2 * |b| ^ 2) := by ring
      _ ≤ _ := by gcongr; exact pow_le_sum_pow 2 2 rfl
  have t3 : |b ^ 3 * (φ 3 a - iteratedDeriv 0 (φ 3) 0 * a ^ 0 / (Nat.factorial 0))| ≤ N3 * (|a| + |b|) ^ 4 := by
    rw [abs_mul, abs_pow]
    calc _ ≤ |b| ^ 3 * (N3 * |a| ^ 1) := by gcongr
      _ = N3 * (|a| ^ 1 * |b| ^ 3) := by ring
      _ ≤ _ := by gcongr; exact pow_le_sum_pow 1 3 rfl
  have t0 : |φ 0 a - (iteratedDeriv 0 (φ 0) 0 * a ^ 0 / (Nat.factorial 0) + iteratedDeriv 1 (φ 0) 0 * a ^ 1 /
        (Nat.factorial 1) + iteratedDeriv 2 (φ 0) 0 * a ^ 2 / (Nat.factorial 2) +
        iteratedDeriv 3 (φ 0) 0 * a ^ 3 / (Nat.factorial 3))| ≤ N0 * (|a| + |b|) ^ 4 :=
    e0.trans (mul_le_mul_of_nonneg_left (by simpa using pow_le_sum_pow (a := a) (b := b) 4 0 rfl) hN00)
  have tb : |F (x₀ + a, y₀ + b) - (φ 0 a + φ 1 a * b + φ 2 a * b ^ 2 + φ 3 a * b ^ 3)| ≤
      M * (|a| + |b|) ^ 4 :=
    hb_exp.trans (mul_le_mul_of_nonneg_left (by simpa using pow_le_sum_pow (a := a) (b := b) 0 4 rfl) hM0)
  have hsum5 : ∀ x1 x2 x3 x4 x5 : ℝ, |x1 + x2 + x3 + x4 + x5| ≤ |x1| + |x2| + |x3| + |x4| + |x5| := by
    intro x1 x2 x3 x4 x5
    have h1 := abs_add_le (x1 + x2 + x3 + x4) x5
    have h2 := abs_add_le (x1 + x2 + x3) x4
    have h3 := abs_add_le (x1 + x2) x3
    have h4 := abs_add_le x1 x2
    linarith
  refine (hsum5 _ _ _ _ _).trans ?_
  linarith [tb, t0, t1, t2, t3]

end UndergradKB.DifferentialEquations
