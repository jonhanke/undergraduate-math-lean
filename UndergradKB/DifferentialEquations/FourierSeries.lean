import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.PDE

/-! # Fourier series: real coefficients, periodic extension, sine and cosine series

Lebl, *Notes on Diffy Qs*, §§4.2-4.4.  For a `2L`-periodic `f` the real Fourier coefficients are
`a_n = (1/L) ∫_{-L}^{L} f(t) cos(nπt/L) dt` and `b_n = (1/L) ∫_{-L}^{L} f(t) sin(nπt/L) dt`.
Only the coefficients are treated here (convergence of the series is elsewhere).  In the code the
argument of the trigonometric functions is written `n * π / L * t`, i.e. `nπt/L`.

Contents: periodic extension (DE-120), coefficients and trigonometric polynomials (DE-123),
sawtooth and square wave (DE-124), rescaling (DE-127), piecewise continuity (DE-128),
coefficients of derivatives and integrals (DE-130, DE-131), decay (DE-132), odd and even
extensions (DE-133), sine and cosine series coefficients (DE-134). -/

namespace UndergradKB.DifferentialEquations

open Real intervalIntegral MeasureTheory Set

/-! ## Periodic extension (DE-120) -/

/-- The periodic extension to `ℝ` (period `P`) of the values of `f` on `[a, a+P)`. -/
noncomputable def periodicExt {P : ℝ} (hP : 0 < P) (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f (toIcoMod hP a t)

lemma periodicExt_periodic {P : ℝ} (hP : 0 < P) (a : ℝ) (f : ℝ → ℝ) :
    Function.Periodic (periodicExt hP a f) P := by
  intro t
  simp [periodicExt]

lemma periodicExt_eq {P : ℝ} (hP : 0 < P) (a : ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : t ∈ Ico a (a + P)) :
    periodicExt hP a f t = f t := by
  simp [periodicExt, (toIcoMod_eq_self hP).2 ht]

/-- **Periodic extension (DE-120).** A function given on `[a, a+P)` (`P > 0`) has exactly one
`P`-periodic extension to `ℝ`. -/
@[kb "lebldiffyqs2026" "Example 4.2.1, p. 198"]
theorem exists_unique_periodic_extension {P : ℝ} (hP : 0 < P) (a : ℝ) (f : ℝ → ℝ) :
    ∃! g : ℝ → ℝ, Function.Periodic g P ∧ ∀ t ∈ Ico a (a + P), g t = f t := by
  refine ⟨periodicExt hP a f, ⟨periodicExt_periodic hP a f, fun t ht => periodicExt_eq hP a f ht⟩, ?_⟩
  rintro g ⟨hg, hgf⟩
  funext t
  have h1 : g (toIcoMod hP a t) = g t := by
    unfold toIcoMod
    exact hg.sub_zsmul_eq _
  have h2 : g (toIcoMod hP a t) = f (toIcoMod hP a t) := hgf _ (by
    have := toIcoMod_mem_Ico hP a t
    simpa using this)
  rw [← h1, h2]
  rfl

/-! ## Fourier coefficients (DE-123) -/

/-- Cosine coefficient `a_n = (1/L) ∫_{-L}^{L} f(t) cos(nπt/L) dt` of a `2L`-periodic `f`. -/
noncomputable def fourierA (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  (1 / L) * ∫ t in (-L)..L, f t * cos (n * π / L * t)

/-- Sine coefficient `b_n = (1/L) ∫_{-L}^{L} f(t) sin(nπt/L) dt` of a `2L`-periodic `f`. -/
noncomputable def fourierB (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  (1 / L) * ∫ t in (-L)..L, f t * sin (n * π / L * t)

lemma integral_odd_symm (g : ℝ → ℝ) (hg : ∀ t, g (-t) = - g t) (L : ℝ) :
    ∫ t in (-L)..L, g t = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -L) (b := L) g
  simp only [hg, intervalIntegral.integral_neg, neg_neg] at h
  linarith

lemma integral_even_symm (g : ℝ → ℝ) (L : ℝ) (hg : ∀ t, g (-t) = g t)
    (hint : IntervalIntegrable g volume 0 L) :
    ∫ t in (-L)..L, g t = 2 * ∫ t in (0 : ℝ)..L, g t := by
  have h1 : IntervalIntegrable g volume (-L) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := g) (a := 0) (b := L) enorm_ne_top).1 hint
    simp only [hg, neg_zero] at this
    exact this.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 hint]
  have := intervalIntegral.integral_comp_neg (a := 0) (b := L) g
  simp only [hg, neg_zero] at this
  rw [this]
  ring

lemma fourierA_of_odd {f : ℝ → ℝ} (hf : ∀ t, f (-t) = - f t) (L : ℝ) (n : ℕ) :
    fourierA f L n = 0 := by
  unfold fourierA
  rw [integral_odd_symm _ _ L]
  · simp
  · intro t
    simp [hf]

lemma fourierB_of_even {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (L : ℝ) (n : ℕ) :
    fourierB f L n = 0 := by
  unfold fourierB
  rw [integral_odd_symm _ _ L]
  · simp
  · intro t
    simp [hf]

/-- The trigonometric polynomial `a₀/2 + ∑_{k=1}^{N} (a_k cos(kπt/L) + b_k sin(kπt/L))`. -/
noncomputable def trigPoly (L : ℝ) (a b : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  a 0 / 2 + ∑ k ∈ Finset.Icc 1 N, (a k * cos (k * π / L * t) + b k * sin (k * π / L * t))

lemma continuous_trigPoly (L : ℝ) (a b : ℕ → ℝ) (N : ℕ) : Continuous (trigPoly L a b N) := by
  unfold trigPoly
  fun_prop

/-- **Coefficients of a trigonometric polynomial (DE-123).** The cosine coefficients
`a_n` (`0 ≤ n ≤ N`, with the convention `a₀/2` for the constant term) are recovered. -/
@[kb "lebldiffyqs2026" "§4.2 Fourier series, p. 200"]
theorem fourierA_trigPoly {L : ℝ} (hL : 0 < L) (a b : ℕ → ℝ) {N n : ℕ} (hn : n ≤ N) :
    fourierA (trigPoly L a b N) L n = a n := by
  unfold fourierA
  have expand : ∀ t : ℝ, trigPoly L a b N t * cos (n * π / L * t)
      = a 0 / 2 * (cos (n * π / L * t) * cos (((0 : ℕ) : ℝ) * π / L * t))
        + ∑ k ∈ Finset.Icc 1 N, (a k * (cos (k * π / L * t) * cos (n * π / L * t))
          + b k * (sin (k * π / L * t) * cos (n * π / L * t))) := by
    intro t
    unfold trigPoly
    rw [add_mul, Finset.sum_mul]
    simp only [Nat.cast_zero, zero_mul, zero_div, cos_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [expand]
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g volume (-L) L :=
    fun g hg => hg.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => hc _ (by fun_prop))]
  have hk : ∀ k ∈ Finset.Icc 1 N, ∫ t in (-L)..L, (a k * (cos (k * π / L * t) * cos (n * π / L * t))
          + b k * (sin (k * π / L * t) * cos (n * π / L * t))) = a k * (if k = n then L else 0) := by
    intro k hk
    have hk1 : k ≠ 0 := by simp at hk; omega
    rw [intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_mul_cos hL, integral_sin_mul_cos]
    simp [hk1]
  rw [Finset.sum_congr rfl hk, integral_cos_mul_cos hL]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rw [Finset.sum_eq_zero]
    · simp
      field_simp
    · intro k hk
      have : k ≠ 0 := by simp at hk; omega
      simp [this]
  · rw [Finset.sum_eq_single n]
    · have : n ≠ 0 := by omega
      simp [this]
      field_simp
    · intro k _ hkn
      simp [hkn]
    · intro h
      exact absurd (by simp; omega) h

/-- **Coefficients of a trigonometric polynomial (DE-123).** The sine coefficients `b_n`
(`1 ≤ n ≤ N`) are recovered. -/
@[kb "lebldiffyqs2026" "§4.2 Fourier series, p. 200"]
theorem fourierB_trigPoly {L : ℝ} (hL : 0 < L) (a b : ℕ → ℝ) {N n : ℕ} (hn0 : 1 ≤ n) (hn : n ≤ N) :
    fourierB (trigPoly L a b N) L n = b n := by
  unfold fourierB
  have expand : ∀ t : ℝ, trigPoly L a b N t * sin (n * π / L * t)
      = a 0 / 2 * (sin (n * π / L * t) * cos (((0 : ℕ) : ℝ) * π / L * t))
        + ∑ k ∈ Finset.Icc 1 N, (a k * (cos (k * π / L * t) * sin (n * π / L * t))
          + b k * (sin (k * π / L * t) * sin (n * π / L * t))) := by
    intro t
    unfold trigPoly
    rw [add_mul, Finset.sum_mul]
    simp only [Nat.cast_zero, zero_mul, zero_div, cos_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  simp_rw [expand]
  have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g volume (-L) L :=
    fun g hg => hg.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => hc _ (by fun_prop))]
  have hk : ∀ k ∈ Finset.Icc 1 N, ∫ t in (-L)..L, (a k * (cos (k * π / L * t) * sin (n * π / L * t))
          + b k * (sin (k * π / L * t) * sin (n * π / L * t))) = b k * (if k = n then L else 0) := by
    intro k hk
    have hk1 : 0 < k := by simp at hk; omega
    have hcs : ∫ t in (-L)..L, cos (k * π / L * t) * sin (n * π / L * t) = 0 := by
      have := integral_sin_mul_cos L n k
      simpa only [mul_comm] using this
    rw [intervalIntegral.integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hcs, integral_sin_mul_sin hL hk1 (by omega)]
    simp
  rw [Finset.sum_congr rfl hk, integral_sin_mul_cos]
  rw [Finset.sum_eq_single n]
  · have : n ≠ 0 := by omega
    simp
    field_simp
  · intro k _ hkn
    simp [hkn]
  · intro h
    exact absurd (by simp; omega) h

/-! ## Sawtooth and square wave (DE-124) -/

/-- **Sawtooth, cosine coefficients (DE-124).** For `f(t) = t` on `(-π, π)` all `a_n = 0`. -/
@[kb "lebldiffyqs2026" "Example 4.2.3, p. 201"]
theorem fourierA_sawtooth (n : ℕ) : fourierA (fun t => t) π n = 0 :=
  fourierA_of_odd (f := fun t => t) (fun _ => rfl) π n

/-- **Sawtooth, sine coefficients (DE-124).** For `f(t) = t` on `(-π, π)`,
`b_n = 2 (-1)^{n+1} / n` for `n ≥ 1`. -/
@[kb "lebldiffyqs2026" "Example 4.2.3, p. 201"]
theorem fourierB_sawtooth {n : ℕ} (hn : 1 ≤ n) :
    fourierB (fun t => t) π n = 2 * (-1) ^ (n + 1) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => sin (n * t) / n ^ 2 - t * cos (n * t) / n)
      (x * sin (n * x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (n : ℝ) * t) n x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have h4 := (hasDerivAt_id x).mul h1.cos
    refine ((h1.sin.div_const ((n : ℝ) ^ 2)).sub (h4.div_const (n : ℝ))).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  unfold fourierB
  have e : (n : ℝ) * π / π = n := by field_simp
  simp only [e]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun x : ℝ => x * sin (n * x)).intervalIntegrable _ _)]
  simp only [mul_neg, sin_neg, cos_neg, sin_nat_mul_pi, cos_nat_mul_pi]
  field_simp
  ring

/-- The square wave: `-1` on `(-π, 0)` and `1` on `(0, π)` (values at the jumps are immaterial for
the coefficients; here `-1` at `0`). -/
noncomputable def squareWave (t : ℝ) : ℝ := if t ≤ 0 then -1 else 1

lemma integral_squareWave_mul (h : ℝ → ℝ) (hc : Continuous h) {L : ℝ} (hL : 0 < L) :
    ∫ t in (-L)..L, squareWave t * h t
      = (∫ t in (0 : ℝ)..L, h t) - ∫ t in (-L)..0, h t := by
  have e1 : ∀ t ∈ Ioc (-L) 0, squareWave t * h t = - h t := by
    intro t ht
    simp [squareWave, ht.2]
  have e2 : ∀ t ∈ Ioc 0 L, squareWave t * h t = h t := by
    intro t ht
    simp [squareWave, not_le.2 ht.1]
  have i1 : IntervalIntegrable (fun t => squareWave t * h t) volume (-L) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact ((hc.neg.intervalIntegrable (-L) 0).1.congr_fun (fun t ht => (e1 t ht).symm)
      measurableSet_Ioc)
  have i2 : IntervalIntegrable (fun t => squareWave t * h t) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
    exact (((hc.intervalIntegrable 0 L)).1.congr_fun (fun t ht => (e2 t ht).symm)
      measurableSet_Ioc)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_Ioo_of_le (by linarith) (g := fun t => - h t)
      (fun t ht => e1 t (Ioo_subset_Ioc_self ht)),
    intervalIntegral.integral_congr_Ioo_of_le hL.le (g := h)
      (fun t ht => e2 t (Ioo_subset_Ioc_self ht)), intervalIntegral.integral_neg]
  ring

lemma integral_neg_half (h : ℝ → ℝ) (L : ℝ) :
    ∫ t in (-L)..0, h t = ∫ t in (0 : ℝ)..L, h (-t) := by
  simp

/-- **Square wave, cosine coefficients (DE-124).** All `a_n = 0`. -/
@[kb "lebldiffyqs2026" "Example 4.2.4, p. 203"]
theorem fourierA_squareWave (n : ℕ) : fourierA squareWave π n = 0 := by
  unfold fourierA
  rw [integral_squareWave_mul (fun t => cos (n * π / π * t)) (by fun_prop) pi_pos,
    integral_neg_half]
  simp

/-- **Square wave, sine coefficients (DE-124).** `b_n = 4/(nπ)` for odd `n` and `0` for even
`n ≥ 1`. -/
@[kb "lebldiffyqs2026" "Example 4.2.4, p. 203"]
theorem fourierB_squareWave {n : ℕ} (hn : 1 ≤ n) :
    fourierB squareWave π n = if Odd n then 4 / (n * π) else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  unfold fourierB
  rw [integral_squareWave_mul (fun t => sin (n * π / π * t)) (by fun_prop) pi_pos,
    integral_neg_half]
  have e : (n : ℝ) * π / π = n := by field_simp
  simp only [e, mul_neg, sin_neg, intervalIntegral.integral_neg, sub_neg_eq_add]
  have hd : ∀ x ∈ uIcc (0 : ℝ) π, HasDerivAt (fun t : ℝ => -cos (n * t) / n) (sin (n * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (n : ℝ) * t) n x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    refine (h1.cos.neg.div_const (n : ℝ)).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x : ℝ => sin (n * x)).intervalIntegrable _ _)]
  simp only [mul_zero, cos_zero, cos_nat_mul_pi]
  rcases Nat.even_or_odd n with he | ho
  · have : ¬ Odd n := Nat.not_odd_iff_even.2 he
    simp [this, he.neg_one_pow]
  · simp [ho, ho.neg_one_pow]
    field_simp
    ring

/-! ## Rescaling (DE-127) -/

/-- **Rescaling (DE-127).** The cosine coefficients of a `2L`-periodic `f` are those of the
`2π`-periodic function `s ↦ f(Ls/π)`. -/
@[kb "lebldiffyqs2026" "§4.3 2L-periodic functions, p. 208"]
theorem fourierA_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) (n : ℕ) :
    fourierA f L n = fourierA (fun s => f (L * s / π)) π n := by
  unfold fourierA
  have hc : L / π ≠ 0 := by positivity
  have key := intervalIntegral.integral_comp_mul_left (a := -π) (b := π)
    (fun t => f t * cos (n * π / L * t)) hc
  have e1 : L / π * -π = -L := by field_simp
  have e2 : L / π * π = L := by field_simp
  rw [e1, e2] at key
  have : ∀ x : ℝ, f (L * x / π) * cos (n * π / π * x)
      = f (L / π * x) * cos (n * π / L * (L / π * x)) := by
    intro x
    rw [show L * x / π = L / π * x by ring, show (n : ℝ) * π / π * x = n * π / L * (L / π * x) by
      field_simp]
  simp_rw [this]
  rw [key, smul_eq_mul]
  field_simp

/-- **Rescaling (DE-127).** The sine coefficients of a `2L`-periodic `f` are those of the
`2π`-periodic function `s ↦ f(Ls/π)`. -/
@[kb "lebldiffyqs2026" "§4.3 2L-periodic functions, p. 208"]
theorem fourierB_rescale {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) (n : ℕ) :
    fourierB f L n = fourierB (fun s => f (L * s / π)) π n := by
  unfold fourierB
  have hc : L / π ≠ 0 := by positivity
  have key := intervalIntegral.integral_comp_mul_left (a := -π) (b := π)
    (fun t => f t * sin (n * π / L * t)) hc
  have e1 : L / π * -π = -L := by field_simp
  have e2 : L / π * π = L := by field_simp
  rw [e1, e2] at key
  have : ∀ x : ℝ, f (L * x / π) * sin (n * π / π * x)
      = f (L / π * x) * sin (n * π / L * (L / π * x)) := by
    intro x
    rw [show L * x / π = L / π * x by ring, show (n : ℝ) * π / π * x = n * π / L * (L / π * x) by
      field_simp]
  simp_rw [this]
  rw [key, smul_eq_mul]
  field_simp

/-! ## Piecewise continuity (DE-128) -/

open Filter Topology

/-- **Piecewise continuous on `[a, b]` (DE-128, bridging definition).** There is a finite set `S`
of exceptional points such that `f` is continuous (within `[a,b]`) at every other point of
`[a,b]`, and at every point of `S` the one-sided limits exist (where the side lies in `[a,b]`). -/
def PiecewiseContinuousOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ S : Finset ℝ, (∀ x ∈ Icc a b, x ∉ S → ContinuousWithinAt f (Icc a b) x) ∧
    ∀ x ∈ S, (a < x → ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)) ∧ (x < b → ∃ l, Tendsto f (𝓝[>] x) (𝓝 l))

/-- **Piecewise smooth on `[a, b]` (DE-128, bridging definition).** `f` and its derivative (away
from a finite set where `f` fails to be differentiable) are piecewise continuous. -/
def PiecewiseSmoothOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  PiecewiseContinuousOn f a b ∧ ∃ S : Finset ℝ, (∀ x ∈ Ioo a b, x ∉ S → DifferentiableAt ℝ f x) ∧
    PiecewiseContinuousOn (deriv f) a b

/-- **Continuous implies piecewise continuous (DE-128).** -/
@[kb "lebldiffyqs2026" "§4.3 piecewise smooth, p. 211"]
theorem ContinuousOn.piecewiseContinuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) :
    PiecewiseContinuousOn f a b :=
  ⟨∅, fun x hx _ => hf x hx, by simp⟩

/-- **A step function is piecewise continuous (DE-128).** `t ↦ if t < c then u else v`
on any interval `[a, b]`. -/
@[kb "lebldiffyqs2026" "Example 4.3.2, p. 211"]
theorem piecewiseContinuousOn_step (a b c u v : ℝ) :
    PiecewiseContinuousOn (fun t => if t < c then u else v) a b := by
  refine ⟨{c}, ?_, ?_⟩
  · intro x _ hx
    have hx' : x ≠ c := by simpa using hx
    rcases lt_or_gt_of_ne hx' with h | h
    · have hev : (fun _ : ℝ => u) =ᶠ[𝓝 x] (fun t : ℝ => if t < c then u else v) :=
        (eventually_lt_nhds h).mono fun y hy => by simp [hy]
      exact ((continuousAt_const (y := u)).congr hev).continuousWithinAt
    · have hev : (fun _ : ℝ => v) =ᶠ[𝓝 x] (fun t : ℝ => if t < c then u else v) :=
        (eventually_gt_nhds h).mono fun y hy => by simp [not_lt.2 hy.le]
      exact ((continuousAt_const (y := v)).congr hev).continuousWithinAt
  · intro x hx
    have hx' : x = c := by simpa using hx
    subst hx'
    refine ⟨fun _ => ⟨u, ?_⟩, fun _ => ⟨v, ?_⟩⟩
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.mono (self_mem_nhdsWithin : Iio x ∈ 𝓝[<] x)
        (fun y hy => by simp [show y < x from hy])
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      exact Filter.Eventually.mono (self_mem_nhdsWithin : Ioi x ∈ 𝓝[>] x)
        (fun y hy => by simp [not_lt.2 (show x < y from hy).le])

/-! ## Termwise differentiation and integration, decay (DE-130 to DE-132) -/

lemma ibp_cos {f f' : ℝ → ℝ} {L : ℝ} (ω : ℝ) (hf : ∀ x ∈ uIcc (-L) L, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (-L) L) :
    ∫ x in (-L)..L, f' x * cos (ω * x)
      = f L * cos (ω * L) - f (-L) * cos (ω * (-L)) + ω * ∫ x in (-L)..L, f x * sin (ω * x) := by
  have hcf : ContinuousOn f (uIcc (-L) L) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hv : ∀ x ∈ uIcc (-L) L, HasDerivAt (fun t => cos (ω * t)) (-ω * sin (ω * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => ω * t) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    refine h1.cos.congr_deriv ?_
    ring
  have hv' : IntervalIntegrable (fun x => -ω * sin (ω * x)) volume (-L) L :=
    (by fun_prop : Continuous fun x : ℝ => -ω * sin (ω * x)).intervalIntegrable _ _
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub hf hv hf' hv'
  have i1 : IntervalIntegrable (fun x => f' x * cos (ω * x)) volume (-L) L :=
    hf'.mul_continuousOn (by fun_prop)
  have i2 : IntervalIntegrable (fun x => f x * (-ω * sin (ω * x))) volume (-L) L :=
    (hcf.mul (by fun_prop : Continuous fun x : ℝ => -ω * sin (ω * x)).continuousOn
      ).intervalIntegrable
  have i3 : IntervalIntegrable (fun x => f x * sin (ω * x)) volume (-L) L :=
    (hcf.mul (by fun_prop : Continuous fun x : ℝ => sin (ω * x)).continuousOn).intervalIntegrable
  rw [intervalIntegral.integral_add i1 i2] at ibp
  have : ∀ x, f x * (-ω * sin (ω * x)) = -ω * (f x * sin (ω * x)) := fun x => by ring
  simp_rw [this] at ibp
  rw [intervalIntegral.integral_const_mul] at ibp
  linarith

lemma ibp_sin {f f' : ℝ → ℝ} {L : ℝ} (ω : ℝ) (hf : ∀ x ∈ uIcc (-L) L, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume (-L) L) :
    ∫ x in (-L)..L, f' x * sin (ω * x)
      = f L * sin (ω * L) - f (-L) * sin (ω * (-L)) - ω * ∫ x in (-L)..L, f x * cos (ω * x) := by
  have hcf : ContinuousOn f (uIcc (-L) L) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hv : ∀ x ∈ uIcc (-L) L, HasDerivAt (fun t => sin (ω * t)) (ω * cos (ω * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => ω * t) ω x := by
      simpa using (hasDerivAt_id x).const_mul ω
    refine h1.sin.congr_deriv ?_
    ring
  have hv' : IntervalIntegrable (fun x => ω * cos (ω * x)) volume (-L) L :=
    (by fun_prop : Continuous fun x : ℝ => ω * cos (ω * x)).intervalIntegrable _ _
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub hf hv hf' hv'
  have i1 : IntervalIntegrable (fun x => f' x * sin (ω * x)) volume (-L) L :=
    hf'.mul_continuousOn (by fun_prop)
  have i2 : IntervalIntegrable (fun x => f x * (ω * cos (ω * x))) volume (-L) L :=
    (hcf.mul (by fun_prop : Continuous fun x : ℝ => ω * cos (ω * x)).continuousOn
      ).intervalIntegrable
  rw [intervalIntegral.integral_add i1 i2] at ibp
  have : ∀ x, f x * (ω * cos (ω * x)) = ω * (f x * cos (ω * x)) := fun x => by ring
  simp_rw [this] at ibp
  rw [intervalIntegral.integral_const_mul] at ibp
  linarith

/-- **Termwise differentiation, coefficient form (DE-130).** If `f` is `C¹` on `[-L, L]` (derivative
`f'` interval integrable) with `f(-L) = f(L)` (so the periodic extension is continuous), then
`a_n(f') = (nπ/L) b_n(f)`. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.2, p. 212"]
theorem fourierA_deriv {f f' : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : ∀ x ∈ uIcc (-L) L, HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume (-L) L)
    (hper : f (-L) = f L) (n : ℕ) :
    fourierA f' L n = (n * π / L) * fourierB f L n := by
  unfold fourierA fourierB
  rw [ibp_cos _ hf hf']
  have h1 : (n : ℝ) * π / L * L = n * π := by field_simp
  rw [mul_neg, cos_neg, h1, hper]
  ring

/-- **Termwise differentiation, coefficient form (DE-130).** Under the same hypotheses,
`b_n(f') = -(nπ/L) a_n(f)`. -/
@[kb "lebldiffyqs2026" "Theorem 4.3.2, p. 212"]
theorem fourierB_deriv {f f' : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : ∀ x ∈ uIcc (-L) L, HasDerivAt f (f' x) x) (hf' : IntervalIntegrable f' volume (-L) L)
    (hper : f (-L) = f L) (n : ℕ) :
    fourierB f' L n = -(n * π / L) * fourierA f L n := by
  unfold fourierA fourierB
  rw [ibp_sin _ hf hf']
  have h1 : (n : ℝ) * π / L * L = n * π := by field_simp
  rw [mul_neg, sin_neg, h1, hper, sin_nat_mul_pi]
  ring

lemma fourierA_sub_const (f : ℝ → ℝ) (c : ℝ) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n)
    (hf : IntervalIntegrable f volume (-L) L) :
    fourierA (fun t => f t - c) L n = fourierA f L n := by
  unfold fourierA
  have h0 : ∫ t in (-L)..L, cos (n * π / L * t) = 0 := by
    have := integral_cos_mul_cos hL n 0
    have hn' : n ≠ 0 := by omega
    simpa [hn'] using this
  have e : ∀ t : ℝ, (f t - c) * cos (n * π / L * t)
      = f t * cos (n * π / L * t) - c * cos (n * π / L * t) := fun t => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub (hf.mul_continuousOn (by fun_prop))
    ((by fun_prop : Continuous fun t : ℝ => c * cos (n * π / L * t)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, h0]
  ring

lemma fourierB_sub_const (f : ℝ → ℝ) (c : ℝ) {L : ℝ} (n : ℕ)
    (hf : IntervalIntegrable f volume (-L) L) :
    fourierB (fun t => f t - c) L n = fourierB f L n := by
  unfold fourierB
  have h0 : ∫ t in (-L)..L, sin (n * π / L * t) = 0 := by
    have := integral_sin_mul_cos L n 0
    simpa using this
  have e : ∀ t : ℝ, (f t - c) * sin (n * π / L * t)
      = f t * sin (n * π / L * t) - c * sin (n * π / L * t) := fun t => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub (hf.mul_continuousOn (by fun_prop))
    ((by fun_prop : Continuous fun t : ℝ => c * sin (n * π / L * t)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, h0]
  ring

/-- **Termwise integration, coefficient form (DE-131).** For continuous `f` on `[-L, L]` let
`F(t) = ∫₀ᵗ f - (a₀/2) t`, where `a₀ = fourierA f L 0`.  Then `F(-L) = F(L)` and for `n ≥ 1`,
`b_n(F) = (L/(nπ)) a_n(f)` and `a_n(F) = -(L/(nπ)) b_n(f)`.  (The constant term `a₀(F)/2` is the
mean of `F` and is not determined by the coefficients of `f`.) -/
@[kb "lebldiffyqs2026" "Theorem 4.3.3, p. 212"]
theorem fourier_integral {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hf : Continuous f) {n : ℕ} (hn : 1 ≤ n) :
    (fun t => (∫ s in (0 : ℝ)..t, f s) - fourierA f L 0 / 2 * t) (-L)
        = (fun t => (∫ s in (0 : ℝ)..t, f s) - fourierA f L 0 / 2 * t) L ∧
    fourierB (fun t => (∫ s in (0 : ℝ)..t, f s) - fourierA f L 0 / 2 * t) L n
        = L / (n * π) * fourierA f L n ∧
    fourierA (fun t => (∫ s in (0 : ℝ)..t, f s) - fourierA f L 0 / 2 * t) L n
        = -(L / (n * π)) * fourierB f L n := by
  set a0 := fourierA f L 0 with ha0
  set F : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, f s) - a0 / 2 * t with hF
  have hint : ∫ s in (-L)..L, f s = L * a0 := by
    rw [ha0]
    unfold fourierA
    simp
    field_simp
  have hFd : ∀ x ∈ uIcc (-L) L, HasDerivAt F (f x - a0 / 2) x := by
    intro x _
    have h1 := (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
    have h2 := (hasDerivAt_id x).const_mul (a0 / 2)
    refine (h1.sub h2).congr_deriv ?_
    simp
  have hper : F (-L) = F L := by
    have := intervalIntegral.integral_interval_sub_left (f := f) (μ := volume) (a := 0) (b := L) (c := -L)
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    simp only [hF]
    linarith
  have hf'i : IntervalIntegrable (fun x => f x - a0 / 2) volume (-L) L :=
    (by fun_prop : Continuous fun x => f x - a0 / 2).intervalIntegrable _ _
  have hA := fourierA_deriv hL hFd hf'i hper n
  have hB := fourierB_deriv hL hFd hf'i hper n
  rw [fourierA_sub_const f _ hL hn (hf.intervalIntegrable _ _)] at hA
  rw [fourierB_sub_const f _ n (hf.intervalIntegrable _ _)] at hB
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  refine ⟨hper, ?_, ?_⟩
  · rw [hA]
    field_simp
  · have : fourierA F L n = - (L / (n * π)) * fourierB f L n := by
      have h2 : (n : ℝ) * π / L ≠ 0 := by positivity
      field_simp
      field_simp at hB
      linarith
    exact this

/-- If `|g| ≤ M` on `[-L, L]` then `|a_n(g)| ≤ 2M`. -/
lemma abs_fourierA_le {g : ℝ → ℝ} {L M : ℝ} (hL : 0 < L) (hg : ∀ x ∈ uIcc (-L) L, |g x| ≤ M)
    (n : ℕ) : |fourierA g L n| ≤ 2 * M := by
  unfold fourierA
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -L) (b := L)
    (f := fun t => g t * cos (n * π / L * t)) (C := M) (by
      intro x hx
      have := hg x (uIoc_subset_uIcc hx)
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)).trans this)
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / L)]
  have e : |L - -L| = 2 * L := by rw [abs_of_pos (by linarith)]; ring
  rw [e] at h
  calc 1 / L * |∫ t in (-L)..L, g t * cos (n * π / L * t)| ≤ 1 / L * (M * (2 * L)) := by gcongr
    _ = 2 * M := by field_simp

/-- If `|g| ≤ M` on `[-L, L]` then `|b_n(g)| ≤ 2M`. -/
lemma abs_fourierB_le {g : ℝ → ℝ} {L M : ℝ} (hL : 0 < L) (hg : ∀ x ∈ uIcc (-L) L, |g x| ≤ M)
    (n : ℕ) : |fourierB g L n| ≤ 2 * M := by
  unfold fourierB
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -L) (b := L)
    (f := fun t => g t * sin (n * π / L * t)) (C := M) (by
      intro x hx
      have := hg x (uIoc_subset_uIcc hx)
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)).trans this)
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / L)]
  have e : |L - -L| = 2 * L := by rw [abs_of_pos (by linarith)]; ring
  rw [e] at h
  calc 1 / L * |∫ t in (-L)..L, g t * sin (n * π / L * t)| ≤ 1 / L * (M * (2 * L)) := by gcongr
    _ = 2 * M := by field_simp

/-- **Decay of the coefficients of a `C¹` function (DE-132).** If `f` is `C¹` on `[-L, L]`
with `f(-L) = f(L)` and `|f'| ≤ M`, then for `n ≥ 1`, `|a_n| ≤ 2LM/(nπ)` and `|b_n| ≤ 2LM/(nπ)`,
i.e. the coefficients are `O(1/n)`. -/
@[kb "lebldiffyqs2026" "§4.3 rates of convergence and smoothness, p. 212"]
theorem abs_fourier_le_of_C1 {f f' : ℝ → ℝ} {L M : ℝ} (hL : 0 < L)
    (hf : ∀ x ∈ uIcc (-L) L, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (uIcc (-L) L))
    (hper : f (-L) = f L) (hM : ∀ x ∈ uIcc (-L) L, |f' x| ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    |fourierA f L n| ≤ 2 * L * M / (n * π) ∧ |fourierB f L n| ≤ 2 * L * M / (n * π) := by
  have hi : IntervalIntegrable f' volume (-L) L := hf'.intervalIntegrable
  have hω : 0 < (n : ℝ) * π / L := by positivity
  have hA := fourierA_deriv hL hf hi hper n
  have hB := fourierB_deriv hL hf hi hper n
  have e : 2 * L * M / (n * π) = 2 * M / ((n : ℝ) * π / L) := by field_simp
  rw [e, le_div_iff₀ hω, le_div_iff₀ hω]
  constructor
  · have h := abs_fourierB_le hL hM n
    rw [hB, abs_mul, abs_neg, abs_of_pos hω] at h
    linarith
  · have h := abs_fourierA_le hL hM n
    rw [hA, abs_mul, abs_of_pos hω] at h
    linarith

/-- **Faster decay for `C²` functions (DE-132).** If moreover `f'` is `C¹` with `f'(-L) = f'(L)`
and `|f''| ≤ M`, then `|a_n|, |b_n| ≤ 2 L² M/(nπ)²` for `n ≥ 1`, i.e. `O(1/n²)`. -/
@[kb "lebldiffyqs2026" "Example 4.3.6, p. 212"]
theorem abs_fourier_le_of_C2 {f f' f'' : ℝ → ℝ} {L M : ℝ} (hL : 0 < L)
    (hf : ∀ x ∈ uIcc (-L) L, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc (-L) L, HasDerivAt f' (f'' x) x) (hf'' : ContinuousOn f'' (uIcc (-L) L))
    (hper : f (-L) = f L) (hper' : f' (-L) = f' L) (hM : ∀ x ∈ uIcc (-L) L, |f'' x| ≤ M)
    {n : ℕ} (hn : 1 ≤ n) :
    |fourierA f L n| ≤ 2 * L ^ 2 * M / (n * π) ^ 2 ∧
      |fourierB f L n| ≤ 2 * L ^ 2 * M / (n * π) ^ 2 := by
  have hcf' : ContinuousOn f' (uIcc (-L) L) := fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable f' volume (-L) L := hcf'.intervalIntegrable
  have hω : 0 < (n : ℝ) * π / L := by positivity
  have hA := fourierA_deriv hL hf hi hper n
  have hB := fourierB_deriv hL hf hi hper n
  obtain ⟨h1, h2⟩ := abs_fourier_le_of_C1 hL hf' hf'' hper' hM hn
  have e : 2 * L ^ 2 * M / (n * π) ^ 2 = (2 * L * M / (n * π)) / ((n : ℝ) * π / L) := by
    field_simp
  rw [e, le_div_iff₀ hω, le_div_iff₀ hω]
  constructor
  · have : fourierB f' L n = -(n * π / L) * fourierA f L n := hB
    have h := congrArg abs this
    rw [abs_mul, abs_neg, abs_of_pos hω] at h
    linarith
  · have h := congrArg abs hA
    rw [abs_mul, abs_of_pos hω] at h
    linarith

/-! ## Odd and even extensions (DE-133) -/

/-- The odd extension of a function given on `(0, L]` (value `0` at `0`). -/
noncomputable def oddExt (f : ℝ → ℝ) (t : ℝ) : ℝ := if 0 < t then f t else if t < 0 then - f (-t) else 0

/-- The even extension of a function given on `[0, L]`. -/
noncomputable def evenExt (f : ℝ → ℝ) (t : ℝ) : ℝ := f |t|

/-- The `2L`-periodic odd extension of `f` from `[0, L]`. -/
noncomputable def oddPeriodicExt {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) : ℝ → ℝ :=
  periodicExt (by linarith : 0 < 2 * L) (-L) (oddExt f)

/-- The `2L`-periodic even extension of `f` from `[0, L]`. -/
noncomputable def evenPeriodicExt {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) : ℝ → ℝ :=
  periodicExt (by linarith : 0 < 2 * L) (-L) (evenExt f)

/-- The odd extension is odd. -/
theorem oddExt_odd (f : ℝ → ℝ) (t : ℝ) : oddExt f (-t) = - oddExt f t := by
  unfold oddExt
  rcases lt_trichotomy t 0 with h | h | h
  · simp [h, not_lt.2 h.le, neg_neg]
  · simp [h]
  · simp [h, not_lt.2 h.le]

/-- The odd extension extends `f` on `(0, ∞)`. -/
theorem oddExt_eq (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) : oddExt f t = f t := by
  simp [oddExt, ht]

/-- The even extension is even. -/
theorem evenExt_even (f : ℝ → ℝ) (t : ℝ) : evenExt f (-t) = evenExt f t := by
  simp [evenExt]

/-- The even extension extends `f` on `[0, ∞)`. -/
theorem evenExt_eq (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) : evenExt f t = f t := by
  simp [evenExt, abs_of_nonneg ht]

/-- **Odd and even periodic extensions (DE-133).** The `2L`-periodic odd extension of `f` is
`2L`-periodic, odd on `(-L, L)` and agrees with `f` on `(0, L)`. -/
@[kb "lebldiffyqs2026" "§4.4 odd and even periodic extension, p. 218"]
theorem oddPeriodicExt_spec {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    Function.Periodic (oddPeriodicExt hL f) (2 * L) ∧
      (∀ t ∈ Ioo (-L) L, oddPeriodicExt hL f (-t) = - oddPeriodicExt hL f t) ∧
      (∀ t ∈ Ioo 0 L, oddPeriodicExt hL f t = f t) := by
  refine ⟨periodicExt_periodic _ _ _, ?_, ?_⟩
  · intro t ht
    have h1 : t ∈ Ico (-L) (-L + 2 * L) := ⟨ht.1.le, by linarith [ht.2]⟩
    have h2 : -t ∈ Ico (-L) (-L + 2 * L) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    unfold oddPeriodicExt
    rw [periodicExt_eq _ _ _ h1, periodicExt_eq _ _ _ h2, oddExt_odd]
  · intro t ht
    have h1 : t ∈ Ico (-L) (-L + 2 * L) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    unfold oddPeriodicExt
    rw [periodicExt_eq _ _ _ h1, oddExt_eq f ht.1]

/-- **Odd and even periodic extensions (DE-133).** The `2L`-periodic even extension of `f` is
`2L`-periodic, even on `(-L, L)` and agrees with `f` on `[0, L)`. -/
@[kb "lebldiffyqs2026" "Example 4.4.1, p. 218"]
theorem evenPeriodicExt_spec {L : ℝ} (hL : 0 < L) (f : ℝ → ℝ) :
    Function.Periodic (evenPeriodicExt hL f) (2 * L) ∧
      (∀ t ∈ Ioo (-L) L, evenPeriodicExt hL f (-t) = evenPeriodicExt hL f t) ∧
      (∀ t ∈ Ico 0 L, evenPeriodicExt hL f t = f t) := by
  refine ⟨periodicExt_periodic _ _ _, ?_, ?_⟩
  · intro t ht
    have h1 : t ∈ Ico (-L) (-L + 2 * L) := ⟨ht.1.le, by linarith [ht.2]⟩
    have h2 : -t ∈ Ico (-L) (-L + 2 * L) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    unfold evenPeriodicExt
    rw [periodicExt_eq _ _ _ h1, periodicExt_eq _ _ _ h2, evenExt_even]
  · intro t ht
    have h1 : t ∈ Ico (-L) (-L + 2 * L) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    unfold evenPeriodicExt
    rw [periodicExt_eq _ _ _ h1, evenExt_eq f ht.1]

/-! ## Sine and cosine series coefficients (DE-134) -/

lemma intervalIntegrable_congr_Ioc {g h : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hg : IntervalIntegrable g volume 0 L) (heq : ∀ t ∈ Ioc 0 L, g t = h t) :
    IntervalIntegrable h volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le] at hg ⊢
  exact hg.congr_fun heq measurableSet_Ioc

lemma integral_congr_Ioc {g h : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (heq : ∀ t ∈ Ioc 0 L, g t = h t) :
    ∫ t in (0 : ℝ)..L, g t = ∫ t in (0 : ℝ)..L, h t :=
  intervalIntegral.integral_congr_Ioo_of_le hL.le (fun t ht => heq t (Ioo_subset_Ioc_self ht))

/-- **Sine series coefficients (DE-134).** For the odd extension of `f` from `(0, L]`,
all `a_n = 0`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem fourierA_oddExt (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : fourierA (oddExt f) L n = 0 :=
  fourierA_of_odd (oddExt_odd f) L n

/-- **Sine series coefficients (DE-134).** For the odd extension of `f` (interval integrable on
`[0, L]`), `b_n = (2/L) ∫₀ᴸ f(t) sin(nπt/L) dt`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem fourierB_oddExt {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 L)
    (n : ℕ) :
    fourierB (oddExt f) L n = (2 / L) * ∫ t in (0 : ℝ)..L, f t * sin (n * π / L * t) := by
  unfold fourierB
  have heq : ∀ t ∈ Ioc 0 L, f t * sin (n * π / L * t) = oddExt f t * sin (n * π / L * t) := by
    intro t ht
    rw [oddExt_eq f ht.1]
  have hint : IntervalIntegrable (fun t => oddExt f t * sin (n * π / L * t)) volume 0 L :=
    intervalIntegrable_congr_Ioc hL (hf.mul_continuousOn (by fun_prop)) heq
  rw [integral_even_symm _ L (fun t => by simp [oddExt_odd]) hint,
    ← integral_congr_Ioc hL heq]
  field_simp

/-- **Cosine series coefficients (DE-134).** For the even extension of `f`, all `b_n = 0`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem fourierB_evenExt (f : ℝ → ℝ) (L : ℝ) (n : ℕ) : fourierB (evenExt f) L n = 0 :=
  fourierB_of_even (evenExt_even f) L n

/-- **Cosine series coefficients (DE-134).** For the even extension of `f` (interval integrable on
`[0, L]`), `a_n = (2/L) ∫₀ᴸ f(t) cos(nπt/L) dt`. -/
@[kb "lebldiffyqs2026" "Theorem 4.4.1, p. 220"]
theorem fourierA_evenExt {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 L)
    (n : ℕ) :
    fourierA (evenExt f) L n = (2 / L) * ∫ t in (0 : ℝ)..L, f t * cos (n * π / L * t) := by
  unfold fourierA
  have heq : ∀ t ∈ Ioc 0 L, f t * cos (n * π / L * t) = evenExt f t * cos (n * π / L * t) := by
    intro t ht
    rw [evenExt_eq f ht.1.le]
  have hint : IntervalIntegrable (fun t => evenExt f t * cos (n * π / L * t)) volume 0 L :=
    intervalIntegrable_congr_Ioc hL (hf.mul_continuousOn (by fun_prop)) heq
  rw [integral_even_symm _ L (fun t => by simp [evenExt_even]) hint,
    ← integral_congr_Ioc hL heq]
  field_simp

end UndergradKB.DifferentialEquations
