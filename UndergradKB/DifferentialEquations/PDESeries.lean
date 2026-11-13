import Mathlib.Analysis.Calculus.SmoothSeries
import UndergradKB.DifferentialEquations.PDE
import UndergradKB.Common.Attr

/-! # Infinite trigonometric series solutions of the heat, wave and Laplace equations

Lebl, *Notes on Diffy Qs*, §§4.6-4.10.  Termwise differentiation of trigonometric series
(`trigTerm`), the wave equation with general initial data (Theorem 4.7.1, DE-145), the Dirichlet problem on a
rectangle (DE-149), and the Laplacian in polar coordinates (DE-150).  Partial derivatives are taken as in
`PDE.lean`: derivatives of slices of `u : ℝ → ℝ → ℝ`. -/

namespace UndergradKB.DifferentialEquations

open Real

/-! ## Termwise differentiation of trigonometric series -/

lemma summable_aux_of_sq {u : ℕ → ℝ} (hu : Summable fun n : ℕ => (n : ℝ) ^ 2 * |u n|) :
    Summable (fun n : ℕ => |u n|) ∧ Summable (fun n : ℕ => (n : ℝ) * |u n|) := by
  constructor
  · refine Summable.of_norm_bounded_eventually hu ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    rw [Real.norm_eq_abs, abs_abs]
    nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ (n:ℝ)^2 - 1) (abs_nonneg (u n))]
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hu
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

lemma abs_nat_mul_aux (n : ℕ) (k c : ℝ) : |(n : ℝ) * k * c| = n * |k| * |c| := by
  rw [abs_mul, abs_mul, Nat.abs_cast]

/-- The `n`-th term `pₙ cos(n k s) + qₙ sin(n k s)` of a trigonometric series. -/
noncomputable def trigTerm (p q : ℕ → ℝ) (k : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  p n * cos (n * k * s) + q n * sin (n * k * s)

/-- Termwise differentiation of `∑ pₙ cos(n k s) + qₙ sin(n k s)` when `∑ |pₙ|, ∑ |qₙ|, ∑ n|pₙ|, ∑ n|qₙ|`
converge. -/
lemma trig_hasDerivAt {p q : ℕ → ℝ} (k : ℝ) (hp0 : Summable fun n => |p n|)
    (hq0 : Summable fun n => |q n|) (hp1 : Summable fun n : ℕ => (n : ℝ) * |p n|)
    (hq1 : Summable fun n : ℕ => (n : ℝ) * |q n|) (s : ℝ) :
    HasDerivAt (fun s => ∑' n, trigTerm p q k n s)
      (∑' n, trigTerm (fun n => n * k * q n) (fun n => -(n * k * p n)) k n s) s := by
  have hu : Summable fun n : ℕ => |k| * ((n : ℝ) * |p n| + (n : ℝ) * |q n|) :=
    (hp1.add hq1).mul_left _
  refine hasDerivAt_tsum (g := fun n s => trigTerm p q k n s)
    (g' := fun n s => trigTerm (fun n => n * k * q n) (fun n => -(n * k * p n)) k n s)
    hu (fun n y => ?_) (fun n y => ?_) (y₀ := 0) ?_ s
  · have h := ((hasDerivAt_cos_mul (n * k) y).const_mul (p n)).add
      ((hasDerivAt_sin_mul (n * k) y).const_mul (q n))
    exact h.congr_deriv (by simp only [trigTerm]; ring)
  · have hc := abs_cos_le_one ((n : ℝ) * k * y)
    have hs := abs_sin_le_one ((n : ℝ) * k * y)
    have h1 : |(n : ℝ) * k * q n * cos ((n : ℝ) * k * y)| ≤ n * |k| * |q n| := by
      rw [abs_mul, abs_nat_mul_aux]
      calc _ ≤ (n : ℝ) * |k| * |q n| * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
        _ = _ := mul_one _
    have h2 : |-((n : ℝ) * k * p n) * sin ((n : ℝ) * k * y)| ≤ n * |k| * |p n| := by
      rw [abs_mul, abs_neg, abs_nat_mul_aux]
      calc _ ≤ (n : ℝ) * |k| * |p n| * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := mul_one _
    simp only [trigTerm, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    nlinarith [h1, h2]
  · refine Summable.of_norm_bounded (hp0.add hq0) fun n => ?_
    have hc := abs_cos_le_one ((n : ℝ) * k * 0)
    have hs := abs_sin_le_one ((n : ℝ) * k * 0)
    simp only [trigTerm, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg (p n)),
      mul_le_mul_of_nonneg_left hs (abs_nonneg (q n))]

/-- Second termwise derivative of a trigonometric series: if `∑ n²|pₙ|` and `∑ n²|qₙ|` converge, then
`(d/ds)² ∑ (pₙ cos(nks) + qₙ sin(nks)) = -∑ (nk)² (pₙ cos(nks) + qₙ sin(nks))`. -/
lemma deriv2_trig {p q : ℕ → ℝ} (k : ℝ) (hp : Summable fun n : ℕ => (n : ℝ) ^ 2 * |p n|)
    (hq : Summable fun n : ℕ => (n : ℝ) ^ 2 * |q n|) (s : ℝ) :
    deriv (fun s => deriv (fun s => ∑' n, trigTerm p q k n s) s) s
      = ∑' n : ℕ, -(((n : ℝ) * k) ^ 2 * trigTerm p q k n s) := by
  obtain ⟨hp0, hp1⟩ := summable_aux_of_sq hp
  obtain ⟨hq0, hq1⟩ := summable_aux_of_sq hq
  have h1 : (fun s => deriv (fun s => ∑' n, trigTerm p q k n s) s)
      = fun s => ∑' n, trigTerm (fun n => n * k * q n) (fun n => -(n * k * p n)) k n s :=
    funext fun s => (trig_hasDerivAt k hp0 hq0 hp1 hq1 s).deriv
  have a0 : Summable fun n : ℕ => |(n : ℝ) * k * q n| := by
    refine (hq1.mul_left |k|).congr fun n => ?_
    rw [abs_nat_mul_aux]; ring
  have a1 : Summable fun n : ℕ => |-((n : ℝ) * k * p n)| := by
    refine (hp1.mul_left |k|).congr fun n => ?_
    rw [abs_neg, abs_nat_mul_aux]; ring
  have a2 : Summable fun n : ℕ => (n : ℝ) * |(n : ℝ) * k * q n| := by
    refine (hq.mul_left |k|).congr fun n => ?_
    rw [abs_nat_mul_aux]; ring
  have a3 : Summable fun n : ℕ => (n : ℝ) * |-((n : ℝ) * k * p n)| := by
    refine (hp.mul_left |k|).congr fun n => ?_
    rw [abs_neg, abs_nat_mul_aux]; ring
  rw [h1, (trig_hasDerivAt k a0 a1 a2 a3 s).deriv]
  refine tsum_congr fun n => ?_
  simp only [trigTerm]; ring

lemma deriv2_trigF {p q : ℕ → ℝ} {F : ℝ → ℝ} (k : ℝ) (hp : Summable fun n : ℕ => (n : ℝ) ^ 2 * |p n|)
    (hq : Summable fun n : ℕ => (n : ℝ) ^ 2 * |q n|) (hF : ∀ s, F s = ∑' n, trigTerm p q k n s)
    (s : ℝ) :
    deriv (fun s => deriv (fun s => F s) s) s
      = ∑' n : ℕ, -(((n : ℝ) * k) ^ 2 * trigTerm p q k n s) := by
  have : F = fun s => ∑' n, trigTerm p q k n s := funext hF
  subst this
  exact deriv2_trig k hp hq s

lemma summable_sq_of_le {u : ℕ → ℝ} {w : ℕ → ℝ} (hw : Summable w)
    (h : ∀ n : ℕ, (n : ℝ) ^ 2 * |u n| ≤ w n) : Summable fun n : ℕ => (n : ℝ) ^ 2 * |u n| :=
  Summable.of_nonneg_of_le (fun n => by positivity) h hw

/-! ## The wave equation with general initial data (DE-145) -/

/-- The series solution `∑ (bₙ cos(nπat/L) + cₙ L/(nπa) sin(nπat/L)) sin(nπx/L)` (indices `n = 0` contribute
nothing since `sin 0 = 0`). -/
noncomputable def waveSeries (a L : ℝ) (b c : ℕ → ℝ) (x t : ℝ) : ℝ :=
  ∑' n : ℕ, (b n * cos (n * π * a / L * t) + c n * (L / (n * π * a)) * sin (n * π * a / L * t))
    * sin (n * π / L * x)

lemma waveSeries_eq (a L : ℝ) (b c : ℕ → ℝ) :
    waveSeries a L b c = fun x t => ∑' n : ℕ,
      (b n * cos (n * (π * a / L) * t) + c n * (L / (n * π * a)) * sin (n * (π * a / L) * t))
        * sin (n * (π / L) * x) := by
  have e1 : ∀ n : ℕ, (n : ℝ) * π * a / L = n * (π * a / L) := fun n => by ring
  have e2 : ∀ n : ℕ, (n : ℝ) * π / L = n * (π / L) := fun n => by ring
  funext x t
  simp only [waveSeries, e1, e2]

lemma abs_coeff_le {a L : ℝ} (n : ℕ) (c : ℕ → ℝ) :
    |c n * (L / (n * π * a))| ≤ |L / (π * a)| * |c n| := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp; positivity
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    have : L / ((n : ℝ) * π * a) = (L / (π * a)) / n := by
      have : (n : ℝ) ≠ 0 := by positivity
      rcases eq_or_ne (π * a) 0 with h0 | h0
      · have : (n : ℝ) * π * a = 0 := by rw [mul_assoc, h0, mul_zero]
        rw [this, h0]; simp
      · field_simp
    rw [this, abs_mul, abs_div, Nat.abs_cast, mul_comm]
    exact mul_le_mul_of_nonneg_right (div_le_self (abs_nonneg _) h1) (abs_nonneg _)

/-- **Wave equation with fixed ends and general initial data (DE-145, Theorem 4.7.1).** Let `f = ∑ bₙ sin(nπx/L)`
and `g = ∑ cₙ sin(nπx/L)` be the initial position and velocity (the roles of the letters `b, c` are the
reverse of the book's), with `∑ n² (|bₙ| + |cₙ|) < ∞`.  Then
`y(x,t) = ∑ (bₙ cos(nπat/L) + cₙ L/(nπa) sin(nπat/L)) sin(nπx/L)` solves `y_tt = a² y_xx`, vanishes at `x = 0, L`,
and satisfies `y(x,0) = f(x)`, `y_t(x,0) = g(x)`.  The summability hypothesis justifies termwise
differentiation (the equation is shown for all real `x, t`). -/
@[kb "lebldiffyqs2026" "Theorem 4.7.1, p. 246"]
theorem wave_series_solution {a L : ℝ} (ha : a ≠ 0) (hL : L ≠ 0) {b c : ℕ → ℝ}
    (hbc : Summable fun n : ℕ => (n : ℝ) ^ 2 * (|b n| + |c n|)) {f g : ℝ → ℝ}
    (hf : ∀ x, f x = ∑' n : ℕ, b n * sin (n * π / L * x))
    (hg : ∀ x, g x = ∑' n : ℕ, c n * sin (n * π / L * x)) :
    WaveEq a (waveSeries a L b c) ∧ (∀ t, waveSeries a L b c 0 t = 0) ∧
      (∀ t, waveSeries a L b c L t = 0) ∧ (∀ x, waveSeries a L b c x 0 = f x) ∧
      ∀ x, deriv (fun t => waveSeries a L b c x t) 0 = g x := by
  set C : ℝ := |L / (π * a)| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  set d : ℕ → ℝ := fun n => c n * (L / (n * π * a)) with hd
  have hb : Summable fun n : ℕ => (n : ℝ) ^ 2 * |b n| :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by
        have := abs_nonneg (c n)
        nlinarith [sq_nonneg (n : ℝ)]) hbc
  have hc : Summable fun n : ℕ => (n : ℝ) ^ 2 * |c n| :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by
        have := abs_nonneg (b n)
        nlinarith [sq_nonneg (n : ℝ)]) hbc
  have hw : Summable fun n : ℕ => (n : ℝ) ^ 2 * |b n| + C * ((n : ℝ) ^ 2 * |c n|) :=
    hb.add (hc.mul_left C)
  have hdle : ∀ n, |d n| ≤ C * |c n| := fun n => abs_coeff_le n c
  have hbd : ∀ n : ℕ, (n : ℝ) ^ 2 * |d n| ≤ C * ((n : ℝ) ^ 2 * |c n|) := fun n => by
    nlinarith [mul_le_mul_of_nonneg_left (hdle n) (sq_nonneg (n : ℝ))]
  have ha1 : ∀ (n : ℕ) (z : ℝ), |b n * sin z| ≤ |b n| := fun n z => by
    rw [abs_mul]
    calc _ ≤ |b n| * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one z) (abs_nonneg _)
      _ = _ := mul_one _
  have ha2 : ∀ (n : ℕ) (z : ℝ), |d n * sin z| ≤ C * |c n| := fun n z => by
    rw [abs_mul]
    calc _ ≤ |d n| * 1 := mul_le_mul_of_nonneg_left (abs_sin_le_one z) (abs_nonneg _)
      _ = _ := mul_one _
      _ ≤ _ := hdle n
  -- representation of the series as a trigonometric series in `t` and in `x`
  have repT : ∀ x s, waveSeries a L b c x s = ∑' n : ℕ, trigTerm
      (fun n => b n * sin (n * (π / L) * x)) (fun n => d n * sin (n * (π / L) * x))
      (π * a / L) n s := by
    intro x s
    rw [waveSeries_eq]
    refine tsum_congr fun n => ?_
    simp only [trigTerm, hd]; ring
  have repX : ∀ t ξ, waveSeries a L b c ξ t = ∑' n : ℕ, trigTerm (fun _ => 0)
      (fun n => b n * cos (n * (π * a / L) * t) + d n * sin (n * (π * a / L) * t))
      (π / L) n ξ := by
    intro t ξ
    rw [waveSeries_eq]
    refine tsum_congr fun n => ?_
    simp only [trigTerm, hd]; ring
  have sP : ∀ x, Summable fun n : ℕ => (n : ℝ) ^ 2 * |b n * sin ((n : ℝ) * (π / L) * x)| :=
    fun x => summable_sq_of_le hw fun n => by
      have := mul_le_mul_of_nonneg_left (ha1 n ((n : ℝ) * (π / L) * x)) (sq_nonneg (n : ℝ))
      nlinarith [mul_nonneg hC0 (mul_nonneg (sq_nonneg (n : ℝ)) (abs_nonneg (c n)))]
  have sQ : ∀ x, Summable fun n : ℕ => (n : ℝ) ^ 2 * |d n * sin ((n : ℝ) * (π / L) * x)| :=
    fun x => summable_sq_of_le hw fun n => by
      have := mul_le_mul_of_nonneg_left (ha2 n ((n : ℝ) * (π / L) * x)) (sq_nonneg (n : ℝ))
      nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (abs_nonneg (b n))]
  have sV : ∀ t, Summable fun n : ℕ => (n : ℝ) ^ 2 * |b n * cos ((n : ℝ) * (π * a / L) * t)
      + d n * sin ((n : ℝ) * (π * a / L) * t)| :=
    fun t => summable_sq_of_le hw fun n => by
      have h1 : |b n * cos ((n : ℝ) * (π * a / L) * t)| ≤ |b n| := by
        rw [abs_mul]
        calc _ ≤ |b n| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
          _ = _ := mul_one _
      have h2 := ha2 n ((n : ℝ) * (π * a / L) * t)
      have h3 := (abs_add_le (b n * cos ((n : ℝ) * (π * a / L) * t))
        (d n * sin ((n : ℝ) * (π * a / L) * t)))
      have := mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) (sq_nonneg (n : ℝ))
      nlinarith
  have hs0 : ∀ n : ℕ, sin ((n : ℝ) * π / L * 0) = 0 := fun n => by simp
  have hsL : ∀ n : ℕ, sin ((n : ℝ) * π / L * L) = 0 := fun n => by
    have : (n : ℝ) * π / L * L = n * π := by field_simp
    rw [this, sin_nat_mul_pi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x t
    have hL' := deriv2_trigF (F := fun s => waveSeries a L b c x s) (π * a / L) (sP x) (sQ x)
      (repT x) t
    have hR' := deriv2_trigF (F := fun ξ => waveSeries a L b c ξ t) (π / L) (p := fun _ => 0)
      (by simp) (sV t) (repX t) x
    rw [hL', hR', ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [trigTerm]; ring
  · intro t; simp [waveSeries]
  · intro t; simp [waveSeries, hsL]
  · intro x; rw [hf]; simp [waveSeries]
  · intro x
    have hp0 := (summable_aux_of_sq (sP x)).1
    have hq0 := (summable_aux_of_sq (sQ x)).1
    have hp1 := (summable_aux_of_sq (sP x)).2
    have hq1 := (summable_aux_of_sq (sQ x)).2
    have hfun : (fun t => waveSeries a L b c x t) = fun s => ∑' n : ℕ, trigTerm
        (fun n => b n * sin (n * (π / L) * x)) (fun n => d n * sin (n * (π / L) * x))
        (π * a / L) n s := funext (repT x)
    rw [hfun, (trig_hasDerivAt (π * a / L) hp0 hq0 hp1 hq1 0).deriv, hg]
    refine tsum_congr fun n => ?_
    simp only [trigTerm, hd]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn : (n : ℝ) ≠ 0 := by positivity
      have hπ : π ≠ 0 := Real.pi_ne_zero
      simp only [mul_zero, cos_zero, sin_zero, mul_one, add_zero]
      have e : (n : ℝ) * (π * a / L) * (c n * (L / (n * π * a)) * sin (n * (π / L) * x))
          = c n * sin (n * π / L * x) := by
        have e2 : (n : ℝ) * (π / L) * x = n * π / L * x := by ring
        rw [e2]; field_simp
      rw [← e]

/-! ## The Dirichlet problem on a rectangle (DE-149) -/

lemma sinh_ratio_bounds {ω y h : ℝ} (hω : 0 < ω) (hh : 0 < h) (hy0 : 0 ≤ y) (hyh : y ≤ h) :
    0 ≤ Real.sinh (ω * y) / Real.sinh (ω * h) ∧ Real.sinh (ω * y) / Real.sinh (ω * h) ≤ 1 := by
  have hS : 0 < Real.sinh (ω * h) := Real.sinh_pos_iff.2 (mul_pos hω hh)
  refine ⟨div_nonneg (Real.sinh_nonneg_iff.2 (mul_nonneg hω.le hy0)) hS.le, ?_⟩
  rw [div_le_one hS]
  exact Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_left hyh hω.le)

lemma cosh_ratio_bounds {ω ω1 y h : ℝ} (hω1 : 0 < ω1) (hle : ω1 ≤ ω) (hh : 0 < h) (hy0 : 0 ≤ y)
    (hyh : y ≤ h) :
    0 ≤ Real.cosh (ω * y) / Real.sinh (ω * h) ∧
      Real.cosh (ω * y) / Real.sinh (ω * h) ≤ 1 + 1 / Real.sinh (ω1 * h) := by
  have hω : 0 < ω := lt_of_lt_of_le hω1 hle
  have hS : 0 < Real.sinh (ω * h) := Real.sinh_pos_iff.2 (mul_pos hω hh)
  have hS1 : 0 < Real.sinh (ω1 * h) := Real.sinh_pos_iff.2 (mul_pos hω1 hh)
  refine ⟨div_nonneg (Real.cosh_pos _).le hS.le, ?_⟩
  have h1 : Real.cosh (ω * y) ≤ Real.cosh (ω * h) := by
    refine Real.cosh_le_cosh.2 ?_
    rw [abs_of_nonneg (mul_nonneg hω.le hy0), abs_of_nonneg (mul_nonneg hω.le hh.le)]
    exact mul_le_mul_of_nonneg_left hyh hω.le
  have h2 : Real.cosh (ω * h) ≤ Real.sinh (ω * h) + 1 := by
    have e := Real.cosh_sub_sinh (ω * h)
    have : Real.exp (-(ω * h)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hω.le hh.le))
    linarith
  have h3 : Real.sinh (ω1 * h) ≤ Real.sinh (ω * h) :=
    Real.sinh_le_sinh.2 (mul_le_mul_of_nonneg_right hle hh.le)
  have h4 : 1 ≤ Real.sinh (ω * h) / Real.sinh (ω1 * h) := (one_le_div hS1).2 h3
  rw [div_le_iff₀ hS]
  have : (1 + 1 / Real.sinh (ω1 * h)) * Real.sinh (ω * h)
      = Real.sinh (ω * h) + Real.sinh (ω * h) / Real.sinh (ω1 * h) := by ring
  rw [this]; linarith

/-- The series `∑ bₙ sinh(nπy/w)/sinh(nπh/w) · sin(nπx/w)`. -/
noncomputable def rectSeries (w h : ℝ) (b : ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑' n : ℕ, b n * (Real.sinh (n * π / w * y) / Real.sinh (n * π / w * h)) * sin (n * π / w * x)

/-- **Dirichlet problem on a rectangle (DE-149).** On the rectangle `[0,w] × [0,h]` let
`f(x) = ∑ bₙ sin(nπx/w)` with `∑ n² |bₙ| < ∞`.  Then
`u(x,y) = ∑ bₙ sinh(nπy/w)/sinh(nπh/w) sin(nπx/w)` satisfies `u_xx + u_yy = 0` for `0 < y < h` (all `x`),
vanishes on the sides `x = 0`, `x = w` and on the edge `y = 0`, and equals `f` on the edge `y = h`.
This is the book's problem with the data edge at the top (the book's `sinh(nπ(h-y)/w)` form is the mirror
image `y ↦ h - y`).  The hypothesis `∑ n² |bₙ| < ∞` (stronger than the book's, which only needs bounded
coefficients inside) justifies termwise differentiation up to the boundary. -/
@[kb "lebldiffyqs2026" "§4.9 Dirichlet problem, p. 259"]
theorem dirichlet_rectangle_series {w h : ℝ} (hw : 0 < w) (hh : 0 < h) {b : ℕ → ℝ}
    (hb : Summable fun n : ℕ => (n : ℝ) ^ 2 * |b n|) {f : ℝ → ℝ}
    (hf : ∀ x, f x = ∑' n : ℕ, b n * sin (n * π / w * x)) :
    (∀ x, ∀ y ∈ Set.Ioo 0 h,
      deriv (fun ξ => deriv (fun ξ => rectSeries w h b ξ y) ξ) x
        + deriv (fun η => deriv (fun η => rectSeries w h b x η) η) y = 0) ∧
    (∀ y, rectSeries w h b 0 y = 0) ∧ (∀ y, rectSeries w h b w y = 0) ∧
    (∀ x, rectSeries w h b x 0 = 0) ∧ ∀ x, rectSeries w h b x h = f x := by
  have hπw : 0 < π / w := div_pos Real.pi_pos hw
  have e2 : ∀ n : ℕ, (n : ℝ) * π / w = n * (π / w) := fun n => by ring
  have hrect : rectSeries w h b = fun x y => ∑' n : ℕ,
      b n * (Real.sinh (n * (π / w) * y) / Real.sinh (n * (π / w) * h)) * sin (n * (π / w) * x) := by
    funext x y; simp only [rectSeries, e2]
  obtain ⟨hb0, hb1⟩ := summable_aux_of_sq hb
  have hωpos : ∀ n : ℕ, 0 < n → 0 < (n : ℝ) * (π / w) := fun n hn => by positivity
  have hωge : ∀ n : ℕ, 0 < n → π / w ≤ (n : ℝ) * (π / w) := fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  set K : ℝ := 1 + 1 / Real.sinh (π / w * h) with hK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hy
    obtain ⟨hy0, hyh⟩ := hy
    -- the `x`-derivatives
    set V : ℕ → ℝ := fun n => b n * (Real.sinh (n * (π / w) * y) / Real.sinh (n * (π / w) * h))
      with hV
    have hVle : ∀ n, |V n| ≤ |b n| := fun n => by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hV]
      · obtain ⟨r0, r1⟩ := sinh_ratio_bounds (hωpos n h0) hh hy0.le hyh.le
        simp only [hV]
        rw [abs_mul, abs_of_nonneg r0]
        calc _ ≤ |b n| * 1 := mul_le_mul_of_nonneg_left r1 (abs_nonneg _)
          _ = _ := mul_one _
    have sV : Summable fun n : ℕ => (n : ℝ) ^ 2 * |V n| :=
      summable_sq_of_le hb fun n => mul_le_mul_of_nonneg_left (hVle n) (sq_nonneg _)
    have hz : Summable fun n : ℕ => (n : ℝ) ^ 2 * |(fun _ : ℕ => (0 : ℝ)) n| := by simp
    have hxx := deriv2_trigF (F := fun ξ => rectSeries w h b ξ y) (p := fun _ => 0) (q := V)
      (π / w) hz sV
      (fun ξ => by
        rw [hrect]
        refine tsum_congr fun n => ?_
        simp only [trigTerm, hV]; ring) x
    -- the `y`-derivatives
    set ee : ℕ → ℝ := fun n => b n * sin (n * (π / w) * x) / Real.sinh (n * (π / w) * h) with hee
    have hrep : ∀ η, rectSeries w h b x η = ∑' n : ℕ, ee n * Real.sinh (n * (π / w) * η) := by
      intro η
      rw [hrect]
      refine tsum_congr fun n => ?_
      simp only [hee]; ring
    have hg : ∀ (n : ℕ) (η : ℝ), HasDerivAt (fun η => ee n * Real.sinh (n * (π / w) * η))
        (ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * η))) η := fun n η =>
      (hasDerivAt_sinh_mul _ η).const_mul _
    have hg' : ∀ (n : ℕ) (η : ℝ), HasDerivAt
        (fun η => ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * η)))
        (ee n * ((n * (π / w)) * ((n * (π / w)) * Real.sinh (n * (π / w) * η)))) η :=
      fun n η => ((hasDerivAt_cosh_mul _ η).const_mul _).const_mul _
    set u1 : ℕ → ℝ := fun n => |b n| * ((n : ℝ) * (π / w)) * K with hu1def
    set u2 : ℕ → ℝ := fun n => |b n| * ((n : ℝ) * (π / w)) ^ 2 with hu2def
    have hu1 : Summable u1 := by
      refine ((hb1.mul_left (π / w * K))).congr fun n => ?_
      simp only [hu1def]; ring
    have hu2 : Summable u2 := by
      refine ((hb.mul_left ((π / w) ^ 2))).congr fun n => ?_
      simp only [hu2def]; ring
    have hb1' : ∀ n η, η ∈ Set.Ioo 0 h → ‖ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * η))‖
        ≤ u1 n := by
      intro n η hη
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hu1def]
      · obtain ⟨r0, r1⟩ := cosh_ratio_bounds hπw (hωge n h0) hh hη.1.le hη.2.le
        have hω := (hωpos n h0).le
        have e : ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * η))
            = (b n * sin (n * (π / w) * x)) * (((n : ℝ) * (π / w)) *
              (Real.cosh (n * (π / w) * η) / Real.sinh (n * (π / w) * h))) := by
          simp only [hee]; ring
        rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg hω r0)]
        have hs := abs_sin_le_one ((n : ℝ) * (π / w) * x)
        simp only [hu1def]
        have hbn := abs_nonneg (b n)
        have h5 : (n : ℝ) * (π / w) * (Real.cosh (n * (π / w) * η) / Real.sinh (n * (π / w) * h))
            ≤ (n : ℝ) * (π / w) * K := mul_le_mul_of_nonneg_left r1 hω
        have h6 : |b n| * |sin ((n : ℝ) * (π / w) * x)| ≤ |b n| :=
          (mul_le_mul_of_nonneg_left hs hbn).trans_eq (mul_one _)
        have h7 : 0 ≤ (n : ℝ) * (π / w) * (Real.cosh (n * (π / w) * η) /
            Real.sinh (n * (π / w) * h)) := mul_nonneg hω r0
        calc _ ≤ |b n| * ((n : ℝ) * (π / w) * K) :=
              mul_le_mul h6 h5 h7 hbn
          _ = _ := by ring
    have hb2' : ∀ n η, η ∈ Set.Ioo 0 h →
        ‖ee n * ((n * (π / w)) * ((n * (π / w)) * Real.sinh (n * (π / w) * η)))‖ ≤ u2 n := by
      intro n η hη
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hu2def]
      · obtain ⟨r0, r1⟩ := sinh_ratio_bounds (hωpos n h0) hh hη.1.le hη.2.le
        have hω := (hωpos n h0).le
        have e : ee n * ((n * (π / w)) * ((n * (π / w)) * Real.sinh (n * (π / w) * η)))
            = (b n * sin (n * (π / w) * x)) * (((n : ℝ) * (π / w)) ^ 2 *
              (Real.sinh (n * (π / w) * η) / Real.sinh (n * (π / w) * h))) := by
          simp only [hee]; ring
        rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) r0)]
        have hs := abs_sin_le_one ((n : ℝ) * (π / w) * x)
        simp only [hu2def]
        have hbn := abs_nonneg (b n)
        have h5 : ((n : ℝ) * (π / w)) ^ 2 * (Real.sinh (n * (π / w) * η) /
            Real.sinh (n * (π / w) * h)) ≤ ((n : ℝ) * (π / w)) ^ 2 :=
          (mul_le_mul_of_nonneg_left r1 (sq_nonneg _)).trans_eq (mul_one _)
        have h6 : |b n| * |sin ((n : ℝ) * (π / w) * x)| ≤ |b n| :=
          (mul_le_mul_of_nonneg_left hs hbn).trans_eq (mul_one _)
        have h7 : 0 ≤ ((n : ℝ) * (π / w)) ^ 2 * (Real.sinh (n * (π / w) * η) /
            Real.sinh (n * (π / w) * h)) := mul_nonneg (sq_nonneg _) r0
        calc _ ≤ |b n| * ((n : ℝ) * (π / w)) ^ 2 := mul_le_mul h6 h5 h7 hbn
          _ = _ := rfl
    have hy0' : h / 2 ∈ Set.Ioo 0 h := ⟨by linarith, by linarith⟩
    have hs0 : Summable fun n : ℕ => ee n * Real.sinh (n * (π / w) * (h / 2)) := by
      refine Summable.of_norm_bounded hb0 fun n => ?_
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hee]
      · obtain ⟨r0, r1⟩ := sinh_ratio_bounds (hωpos n h0) hh hy0'.1.le hy0'.2.le
        have e : ee n * Real.sinh (n * (π / w) * (h / 2))
            = (b n * sin (n * (π / w) * x)) * (Real.sinh (n * (π / w) * (h / 2)) /
              Real.sinh (n * (π / w) * h)) := by simp only [hee]; ring
        rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg r0]
        have hs := abs_sin_le_one ((n : ℝ) * (π / w) * x)
        have hbn := abs_nonneg (b n)
        have h6 : |b n| * |sin ((n : ℝ) * (π / w) * x)| ≤ |b n| :=
          (mul_le_mul_of_nonneg_left hs hbn).trans_eq (mul_one _)
        calc _ ≤ |b n| * 1 := mul_le_mul h6 r1 r0 hbn
          _ = _ := mul_one _
    have hs1 : Summable fun n : ℕ => ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * (h / 2))) :=
      Summable.of_norm_bounded hu1 fun n => hb1' n _ hy0'
    have d1 : ∀ η ∈ Set.Ioo 0 h, HasDerivAt (fun z => rectSeries w h b x z)
        (∑' n : ℕ, ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * η))) η := by
      intro η hη
      have e : (fun z => rectSeries w h b x z)
          = fun z => ∑' n : ℕ, ee n * Real.sinh (n * (π / w) * z) := funext hrep
      rw [e]
      exact hasDerivAt_tsum_of_isPreconnected (g := fun n z => ee n * Real.sinh (n * (π / w) * z))
        (g' := fun n z => ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * z))) hu1
        isOpen_Ioo isPreconnected_Ioo (fun n z _ => hg n z) (fun n z hz => hb1' n z hz) hy0'
        hs0 hη
    have ev : (fun η => deriv (fun z => rectSeries w h b x z) η)
        =ᶠ[nhds y] fun η => ∑' n : ℕ, ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * η)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Set.Ioo 0 h from ⟨hy0, hyh⟩)] with η hη
      exact (d1 η hη).deriv
    have d2 := (hasDerivAt_tsum_of_isPreconnected
      (g := fun n z => ee n * ((n * (π / w)) * Real.cosh (n * (π / w) * z)))
      (g' := fun n z => ee n * ((n * (π / w)) * ((n * (π / w)) * Real.sinh (n * (π / w) * z))))
      hu2 isOpen_Ioo isPreconnected_Ioo (fun n z _ => hg' n z) (fun n z hz => hb2' n z hz) hy0'
      hs1 (show y ∈ Set.Ioo 0 h from ⟨hy0, hyh⟩)).congr_of_eventuallyEq ev
    rw [hxx, d2.deriv]
    refine add_eq_zero_iff_eq_neg.2 ?_
    rw [← tsum_neg]
    refine tsum_congr fun n => ?_
    simp only [trigTerm, hV, hee]; ring
  · intro y; simp [rectSeries]
  · intro y
    have : ∀ n : ℕ, sin ((n : ℝ) * π / w * w) = 0 := fun n => by
      have : (n : ℝ) * π / w * w = n * π := by field_simp
      rw [this, sin_nat_mul_pi]
    simp [rectSeries, this]
  · intro x; simp [rectSeries]
  · intro x
    rw [hf]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have hS : 0 < Real.sinh ((n : ℝ) * π / w * h) :=
        Real.sinh_pos_iff.2 (by positivity)
      rw [div_self hS.ne', mul_one]

/-! ## The Laplacian in polar coordinates (DE-150) -/

lemma clm_prod_apply {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] (L : ℝ × ℝ →L[ℝ] M)
    (a b : ℝ) : L (a, b) = a • L (1, 0) + b • L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul]

lemma expand1 (A : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) : A (a, b) = a * A (1, 0) + b * A (0, 1) := by
  rw [clm_prod_apply A a b]; simp [smul_eq_mul]

lemma expand2 (H : ℝ × ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ)) (a b a' b' : ℝ) :
    H (a, b) (a', b') = a * a' * H (1, 0) (1, 0) + a * b' * H (1, 0) (0, 1)
      + b * a' * H (0, 1) (1, 0) + b * b' * H (0, 1) (0, 1) := by
  rw [clm_prod_apply H a b]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [expand1 (H (1, 0)) a' b', expand1 (H (0, 1)) a' b']
  ring

lemma chain_along {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ 2 U) {γ : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : ℝ}
    (hγ : HasDerivAt γ d s) :
    HasDerivAt (fun s => U (γ s)) (fderiv ℝ U (γ s) d) s :=
  ((hU.differentiable (by norm_num)) (γ s)).hasFDerivAt.comp_hasDerivAt s hγ

lemma hasDerivAt_fderiv_apply {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ 2 U) {γ e : ℝ → ℝ × ℝ}
    {γ' e' : ℝ × ℝ} {s : ℝ} (hγ : HasDerivAt γ γ' s) (he : HasDerivAt e e' s) :
    HasDerivAt (fun s => fderiv ℝ U (γ s) (e s))
      (fderiv ℝ (fderiv ℝ U) (γ s) γ' (e s) + fderiv ℝ U (γ s) e') s := by
  have hA : Differentiable ℝ (fderiv ℝ U) :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : HasDerivAt (fun s => fderiv ℝ U (γ s)) (fderiv ℝ (fderiv ℝ U) (γ s) γ') s :=
    (hA (γ s)).hasFDerivAt.comp_hasDerivAt s hγ
  exact h1.clm_apply he

lemma second_along {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ 2 U) {γ : ℝ → ℝ × ℝ} {d : ℝ × ℝ}
    (hγ : ∀ s, HasDerivAt γ d s) (s : ℝ) :
    deriv (fun s => deriv (fun s => U (γ s)) s) s = fderiv ℝ (fderiv ℝ U) (γ s) d d := by
  have h1 : (fun s => deriv (fun s => U (γ s)) s) = fun s => fderiv ℝ U (γ s) d :=
    funext fun s => (chain_along hU (hγ s)).deriv
  rw [h1]
  have := hasDerivAt_fderiv_apply hU (hγ s) (hasDerivAt_const s d)
  rw [this.deriv]; simp

/-- **Laplacian in polar coordinates (DE-150).** Let `u(x,y)` be `C²` (as a function on `ℝ × ℝ`) and
`v(r,θ) = u(r cos θ, r sin θ)`.  For `r ≠ 0`,
`v_rr + v_r / r + v_θθ / r² = u_xx + u_yy` at `(r cos θ, r sin θ)`.  (Partial derivatives are derivatives of
the slices, as elsewhere in this file; the book assumes `r > 0`.) -/
@[kb "lebldiffyqs2026" "§4.10 Laplace in polar coordinates, p. 264"]
theorem laplacian_polar {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2))
    {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    deriv (fun ρ => deriv (fun ρ => u (ρ * cos θ) (ρ * sin θ)) ρ) r
      + (1 / r) * deriv (fun ρ => u (ρ * cos θ) (ρ * sin θ)) r
      + (1 / r ^ 2) * deriv (fun φ => deriv (fun φ => u (r * cos φ) (r * sin φ)) φ) θ
    = deriv (fun ξ => deriv (fun ξ => u ξ (r * sin θ)) ξ) (r * cos θ)
      + deriv (fun η => deriv (fun η => u (r * cos θ) η) η) (r * sin θ) := by
  have hγr : ∀ s, HasDerivAt (fun ρ : ℝ => (ρ * cos θ, ρ * sin θ)) (cos θ, sin θ) s := fun s => by
    have := ((hasDerivAt_id s).mul_const (cos θ)).prodMk ((hasDerivAt_id s).mul_const (sin θ))
    simpa using this
  have hγx : ∀ s, HasDerivAt (fun ξ : ℝ => (ξ, r * sin θ)) ((1 : ℝ), (0 : ℝ)) s := fun s => by
    have := (hasDerivAt_id s).prodMk (hasDerivAt_const s (r * sin θ))
    simpa using this
  have hγy : ∀ s, HasDerivAt (fun η : ℝ => (r * cos θ, η)) ((0 : ℝ), (1 : ℝ)) s := fun s => by
    have := (hasDerivAt_const s (r * cos θ)).prodMk (hasDerivAt_id s)
    simpa using this
  have hγθ : ∀ φ, HasDerivAt (fun φ : ℝ => (r * cos φ, r * sin φ)) (-(r * sin φ), r * cos φ) φ :=
    fun φ => by
      have := ((hasDerivAt_cos φ).const_mul r).prodMk ((hasDerivAt_sin φ).const_mul r)
      simpa using this
  have heθ : ∀ φ, HasDerivAt (fun φ : ℝ => (-(r * sin φ), r * cos φ)) (-(r * cos φ), -(r * sin φ)) φ :=
    fun φ => by
      have := (((hasDerivAt_sin φ).const_mul r).neg).prodMk ((hasDerivAt_cos φ).const_mul r)
      simpa using this
  have F1 : deriv (fun ρ => deriv (fun ρ => u (ρ * cos θ) (ρ * sin θ)) ρ) r
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ)
        (cos θ, sin θ) (cos θ, sin θ) :=
    second_along hu hγr r
  have F2 : deriv (fun ρ => u (ρ * cos θ) (ρ * sin θ)) r
      = fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (r * cos θ, r * sin θ) (cos θ, sin θ) :=
    (chain_along hu (hγr r)).deriv
  have F4 : deriv (fun ξ => deriv (fun ξ => u ξ (r * sin θ)) ξ) (r * cos θ)
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ)
        (1, 0) (1, 0) :=
    second_along hu hγx (r * cos θ)
  have F5 : deriv (fun η => deriv (fun η => u (r * cos θ) η) η) (r * sin θ)
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ)
        (0, 1) (0, 1) :=
    second_along hu hγy (r * sin θ)
  have F3a : (fun φ => deriv (fun φ => u (r * cos φ) (r * sin φ)) φ)
      = fun φ => fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (r * cos φ, r * sin φ)
        (-(r * sin φ), r * cos φ) := funext fun φ => (chain_along hu (hγθ φ)).deriv
  have F3 : deriv (fun φ => deriv (fun φ => u (r * cos φ) (r * sin φ)) φ) θ
      = fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ)
          (-(r * sin θ), r * cos θ) (-(r * sin θ), r * cos θ)
        + fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (r * cos θ, r * sin θ)
          (-(r * cos θ), -(r * sin θ)) := by
    rw [F3a]
    exact (hasDerivAt_fderiv_apply hu (hγθ θ) (heθ θ)).deriv
  rw [F1, F2, F3, F4, F5]
  rw [expand2 _ (cos θ) (sin θ) (cos θ) (sin θ),
    expand2 _ (-(r * sin θ)) (r * cos θ) (-(r * sin θ)) (r * cos θ),
    expand1 _ (-(r * cos θ)) (-(r * sin θ)), expand1 _ (cos θ) (sin θ)]
  have h := sin_sq_add_cos_sq θ
  generalize fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ) (1, 0) (1, 0)
    = B11
  generalize fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ) (1, 0) (0, 1)
    = B12
  generalize fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ) (0, 1) (1, 0)
    = B21
  generalize fderiv ℝ (fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2)) (r * cos θ, r * sin θ) (0, 1) (0, 1)
    = B22
  generalize fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (r * cos θ, r * sin θ) (1, 0) = A1
  generalize fderiv ℝ (fun p : ℝ × ℝ => u p.1 p.2) (r * cos θ, r * sin θ) (0, 1) = A2
  field_simp
  linear_combination (r * (B11 + B22)) * h

/-! ## Homogeneous side conditions for superposition (DE-138) -/

/-- **Superposition with insulated ends (DE-138, DE-140).** A finite linear combination of solutions of the
heat equation, each satisfying the homogeneous Neumann condition `u_x(p,t) = 0`, satisfies that condition
too (together with `heat_superposition`, which treats the Dirichlet condition `u(p,t) = 0`). -/
@[kb "lebldiffyqs2026" "§4.6 linear PDE, homogeneous conditions, p. 232"]
theorem heat_superposition_neumann {ι : Type*} (S : Finset ι) (c : ι → ℝ) (u : ι → ℝ → ℝ → ℝ)
    (hreg : ∀ i, HeatReg (u i)) (p : ℝ) (hp : ∀ i t, deriv (fun ξ => u i ξ t) p = 0) (t : ℝ) :
    deriv (fun ξ => ∑ i ∈ S, c i * u i ξ t) p = 0 := by
  have hx : HasDerivAt (fun ξ => ∑ i ∈ S, c i * u i ξ t)
      (∑ i ∈ S, c i * deriv (fun ξ => u i ξ t) p) p :=
    HasDerivAt.fun_sum fun i _ => (((hreg i).dx t) p).hasDerivAt.const_mul (c i)
  rw [hx.deriv]
  exact Finset.sum_eq_zero fun i _ => by rw [hp i t, mul_zero]

end UndergradKB.DifferentialEquations
