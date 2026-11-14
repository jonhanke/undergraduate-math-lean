import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.Nonlinear
import UndergradKB.DifferentialEquations.AlmostLinear

/-! # Spiral points wind around the critical point (Lebl, *Notes on Diffy Qs*, Table 8.1)

At an almost linear critical point whose Jacobian `[[a, b], [c, d]]` has complex eigenvalues
(`(a + d)² < 4 (ad - bc)`), a solution that tends to the point (and never equals it) crosses every line through the
point at arbitrarily large times: the trajectory spirals.  This is the "spiral" part of the node/spiral type in the
table.

Proof.  Write `z = (u, v) = (x - x₀, y - y₀)`.  The quadratic form `Q(u,v) = u (cu + dv) - v (au + bv)` is definite
(discriminant `(a+d)² - 4(ad - bc) < 0`): `4 (c - b) Q ≥ D |z|²` with `D = 4(ad - bc) - (a+d)²`.  The almost linear
condition makes the angular momentum `u v' - v u'` differ from `Q` by at most `(D/(8|c-b|)) |z|²`, so
`(c - b)(u v' - v u') ≥ (D/8)|z|²` near the point.  If the cross product `p×z` with a fixed vector stayed `≤ 0`, then
`(p·z)/(p×z)` would decrease (after multiplying by `c - b`) at a definite rate, making `p·z` eventually of a fixed sign,
and then `(p×z)/(p·z)` would have to move at a definite rate through its sign, a contradiction. -/

namespace UndergradKB.DifferentialEquations

open Filter Topology Set

/-- A function with derivative `≤ -k` on `[t₁, ∞)` lies below the line of slope `-k` through `(t₁, g t₁)`. -/
lemma lin_bound {g g' : ℝ → ℝ} {k t₁ : ℝ} (h : ∀ t, t₁ ≤ t → HasDerivAt g (g' t) t)
    (hk : ∀ t, t₁ ≤ t → g' t ≤ -k) : ∀ t, t₁ ≤ t → g t ≤ g t₁ - k * (t - t₁) := by
  intro t ht
  have := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Ici t₁) (f := g)
    (fun s hs => (h s hs).continuousAt.continuousWithinAt)
    (fun s hs => by
      rw [interior_Ici] at hs
      exact (h s (le_of_lt hs)).differentiableAt.differentiableWithinAt)
    (C := -k) (fun s hs => by
      rw [interior_Ici] at hs
      rw [(h s (le_of_lt hs)).deriv]
      exact hk s (le_of_lt hs)) t₁ (mem_Ici.mpr le_rfl) t (mem_Ici.mpr ht) ht
  linarith

/-- Core lemma: if `(p, c)` is a nowhere-zero planar curve whose angular momentum `p c' - c p'` has the sign of
`s` and size at least `k (p² + c²)`, then `c ≤ 0` cannot hold for all large times. -/
lemma no_lower_half {p c p' c' : ℝ → ℝ} {s k T : ℝ} (hk : 0 < k) (hs : s ≠ 0)
    (hp : ∀ t, T ≤ t → HasDerivAt p (p' t) t) (hc : ∀ t, T ≤ t → HasDerivAt c (c' t) t)
    (hA : ∀ t, T ≤ t → k * (p t ^ 2 + c t ^ 2) ≤ s * (p t * c' t - c t * p' t))
    (hne : ∀ t, T ≤ t → 0 < p t ^ 2 + c t ^ 2) (hle : ∀ t, T ≤ t → c t ≤ 0) : False := by
  have hneg : ∀ t, T < t → c t < 0 := by
    intro t0 ht0
    rcases (hle t0 ht0.le).lt_or_eq with h | h
    · exact h
    · exfalso
      have hmax : IsLocalMax c t0 := by
        filter_upwards [Ioi_mem_nhds ht0] with t ht
        show c t ≤ c t0
        rw [h]; exact hle t ht.le
      have hd := hmax.hasDerivAt_eq_zero (hc t0 ht0.le)
      have h1 := hA t0 ht0.le
      have h2 := hne t0 ht0.le
      rw [hd, h] at h1
      rw [h] at h2
      nlinarith
  set t₁ := T + 1 with ht₁
  have ht1T : ∀ t, t₁ ≤ t → T < t := fun t ht => by linarith
  -- stage 1: `G = s p / c`
  set G : ℝ → ℝ := fun t => s * (p t / c t) with hG
  have hGd : ∀ t, t₁ ≤ t → HasDerivAt G (s * ((p' t * c t - p t * c' t) / c t ^ 2)) t := by
    intro t ht
    exact ((hp t (ht1T t ht).le).div (hc t (ht1T t ht).le) (hneg t (ht1T t ht)).ne).const_mul s
  have hGb : ∀ t, t₁ ≤ t → s * ((p' t * c t - p t * c' t) / c t ^ 2) ≤ -k := by
    intro t ht
    have hc2 : 0 < c t ^ 2 := by have := hneg t (ht1T t ht); nlinarith
    have h1 := hA t (ht1T t ht).le
    rw [← mul_div_assoc, div_le_iff₀ hc2]
    nlinarith [mul_nonneg hk.le (sq_nonneg (p t))]
  have hGl := lin_bound hGd hGb
  set M := |G t₁| + 1 with hM
  have hMpos : 0 < M := by positivity
  set t₂ := t₁ + M / k with ht₂
  have ht21 : t₁ ≤ t₂ := by have : 0 < M / k := by positivity
                            linarith
  have hGneg : ∀ t, t₂ ≤ t → G t < 0 := by
    intro t ht
    have h1 := hGl t (le_trans ht21 ht)
    have h2 : M ≤ k * (t - t₁) := by
      calc M = k * (M / k) := by field_simp
        _ ≤ k * (t - t₁) := by apply mul_le_mul_of_nonneg_left _ hk.le; rw [ht₂] at ht; linarith
    have := le_abs_self (G t₁)
    linarith
  have hsp : ∀ t, t₂ ≤ t → 0 < s * p t := by
    intro t ht
    have hct := hneg t (ht1T t (le_trans ht21 ht))
    have h := hGneg t ht
    have hcne := hct.ne
    have : s * p t = G t * c t := by
      simp only [hG]; field_simp
    rw [this]; exact mul_pos_of_neg_of_neg h hct
  have hp0 : ∀ t, t₂ ≤ t → p t ≠ 0 := by
    intro t ht h0
    have := hsp t ht
    rw [h0] at this; simp at this
  -- stage 2: `H = -(s c / p)`
  set H : ℝ → ℝ := fun t => -(s * (c t / p t)) with hH
  have hHd : ∀ t, t₂ ≤ t → HasDerivAt H (-(s * ((c' t * p t - c t * p' t) / p t ^ 2))) t := by
    intro t ht
    have ht' := le_trans ht21 ht
    exact (((hc t (ht1T t ht').le).div (hp t (ht1T t ht').le) (hp0 t ht)).const_mul s).neg
  have hHb : ∀ t, t₂ ≤ t → -(s * ((c' t * p t - c t * p' t) / p t ^ 2)) ≤ -k := by
    intro t ht
    have ht' := le_trans ht21 ht
    have hp2 : 0 < p t ^ 2 := by have := hp0 t ht; positivity
    have h1 := hA t (ht1T t ht').le
    rw [neg_le_neg_iff, ← mul_div_assoc, le_div_iff₀ hp2]
    nlinarith [mul_nonneg hk.le (sq_nonneg (c t))]
  have hHl := lin_bound hHd hHb
  have hHnn : ∀ t, t₂ ≤ t → 0 ≤ H t := by
    intro t ht
    have hct := hneg t (ht1T t (le_trans ht21 ht))
    have hspt := hsp t ht
    have hpt := hp0 t ht
    have : s * (c t / p t) = (s ^ 2 * c t) / (s * p t) := by field_simp
    simp only [hH]
    rw [this, neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg s]) hspt.le
  set M' := |H t₂| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  set t₃ := t₂ + M' / k with ht₃
  have ht32 : t₂ ≤ t₃ := by have : 0 < M' / k := by positivity
                            linarith
  have h1 := hHl t₃ ht32
  have h2 : M' = k * (t₃ - t₂) := by
    calc M' = k * (M' / k) := by field_simp
      _ = k * (t₃ - t₂) := by rw [ht₃]; ring
  have h3 := le_abs_self (H t₂)
  have h4 := hHnn t₃ ht32
  linarith

/-- Positivity of `u² + v²` away from the critical point. -/
lemma sq_add_sq_pos_of_ne {u v : ℝ} (h : ¬(u = 0 ∧ v = 0)) : 0 < u ^ 2 + v ^ 2 := by
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg u) (sq_nonneg v)) with h0 | h0
  · exfalso
    apply h
    have h1 : u ^ 2 = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have h2 : v ^ 2 = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    exact ⟨pow_eq_zero_iff (by norm_num) |>.mp h1, pow_eq_zero_iff (by norm_num) |>.mp h2⟩
  · exact h0

/-- The algebraic core of the angular-speed estimate. With `D = 4(ad - bc) - (a+d)² > 0`, `s = c - b` and
`η = D / (8 |s|)`: if the remainder `(f₁ - (au+bv), g₁ - (cu+dv))` has squared size at most `η² (u²+v²)`, then
`(D/8)(u²+v²) ≤ s (u g₁ - v f₁)`. -/
lemma angular_alg {a b c d u v f₁ g₁ : ℝ} (hD : (a + d) ^ 2 < 4 * (a * d - b * c))
    (hr : (f₁ - (a * u + b * v)) ^ 2 + (g₁ - (c * u + d * v)) ^ 2
      ≤ (((4 * (a * d - b * c) - (a + d) ^ 2)) / (8 * |c - b|)) ^ 2 * (u ^ 2 + v ^ 2)) :
    (4 * (a * d - b * c) - (a + d) ^ 2) / 8 * (u ^ 2 + v ^ 2)
      ≤ (c - b) * (u * g₁ - v * f₁) := by
  set D := 4 * (a * d - b * c) - (a + d) ^ 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hbc : b * c < 0 := by nlinarith [sq_nonneg (d - a)]
  have hs : c - b ≠ 0 := by
    intro h
    have : c = b := by linarith
    rw [this] at hbc; nlinarith [sq_nonneg b]
  have hsabs : 0 < |c - b| := abs_pos.mpr hs
  set η := D / (8 * |c - b|) with hη
  have hηpos : 0 < η := by positivity
  set r₁ := f₁ - (a * u + b * v)
  set r₂ := g₁ - (c * u + d * v)
  have hQ : D * (u ^ 2 + v ^ 2) ≤ 4 * (c - b) * (u * (c * u + d * v) - v * (a * u + b * v)) := by
    rw [hDdef]
    nlinarith [sq_nonneg (2 * c * u + (d - a) * v), sq_nonneg (2 * b * v - (d - a) * u)]
  have herr2 : (u * r₂ - v * r₁) ^ 2 ≤ (η * (u ^ 2 + v ^ 2)) ^ 2 := by
    have h1 : (u * r₂ - v * r₁) ^ 2 ≤ (u ^ 2 + v ^ 2) * (r₁ ^ 2 + r₂ ^ 2) := by
      nlinarith [sq_nonneg (u * r₁ + v * r₂)]
    have h2 : (u ^ 2 + v ^ 2) * (r₁ ^ 2 + r₂ ^ 2) ≤ (u ^ 2 + v ^ 2) * (η ^ 2 * (u ^ 2 + v ^ 2)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    calc (u * r₂ - v * r₁) ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ = (η * (u ^ 2 + v ^ 2)) ^ 2 := by ring
  have herr : |u * r₂ - v * r₁| ≤ η * (u ^ 2 + v ^ 2) :=
    abs_le_of_sq_le_sq herr2 (by positivity)
  have hsη : |c - b| * η = D / 8 := by rw [hη]; field_simp
  have h3 : |(c - b) * (u * r₂ - v * r₁)| ≤ D / 8 * (u ^ 2 + v ^ 2) := by
    rw [abs_mul]
    calc |c - b| * |u * r₂ - v * r₁| ≤ |c - b| * (η * (u ^ 2 + v ^ 2)) :=
          mul_le_mul_of_nonneg_left herr hsabs.le
      _ = D / 8 * (u ^ 2 + v ^ 2) := by rw [← mul_assoc, hsη]
  have h4 := neg_abs_le ((c - b) * (u * r₂ - v * r₁))
  have e : (c - b) * (u * g₁ - v * f₁)
      = (c - b) * (u * (c * u + d * v) - v * (a * u + b * v)) + (c - b) * (u * r₂ - v * r₁) := by
    simp only [r₁, r₂]; ring
  rw [e]
  nlinarith

/-- Near the critical point, `(c - b)(u v' - v u') ≥ (D/8)(u² + v²)` along a solution tending to it. -/
lemma spiral_angular_data {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : (a + d) ^ 2 < 4 * (a * d - b * c)) {x y : ℝ → ℝ}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀)) :
    ∃ s k T₀ : ℝ, s ≠ 0 ∧ 0 < k ∧ 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      k * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2)
        ≤ s * ((x t - x₀) * g (x t) (y t) - (y t - y₀) * f (x t) (y t)) := by
  have hDpos : 0 < 4 * (a * d - b * c) - (a + d) ^ 2 := by linarith
  have hbc : b * c < 0 := by nlinarith [sq_nonneg (d - a)]
  have hs : c - b ≠ 0 := by
    intro h
    have : c = b := by linarith
    rw [this] at hbc; nlinarith [sq_nonneg b]
  have hsabs : 0 < |c - b| := abs_pos.mpr hs
  obtain ⟨ρ, hρ, hρb⟩ := hlin ((((4 * (a * d - b * c) - (a + d) ^ 2)) / (8 * |c - b|)) ^ 2) (by positivity)
  have hlim : Tendsto (fun t => (x t - x₀) ^ 2 + (y t - y₀) ^ 2) atTop (𝓝 (0 ^ 2 + 0 ^ 2)) :=
    (((hx.sub_const x₀).pow 2).add ((hy.sub_const y₀).pow 2)).congr' (by simp) |>.trans (by simp)
  have hev : ∀ᶠ t in atTop, (x t - x₀) ^ 2 + (y t - y₀) ^ 2 < ρ ^ 2 :=
    hlim.eventually_lt_const (by nlinarith [hρ])
  obtain ⟨T', hT'⟩ := eventually_atTop.mp hev
  refine ⟨c - b, (4 * (a * d - b * c) - (a + d) ^ 2) / 8, max T' 0, hs, by positivity, le_max_right _ _, ?_⟩
  intro t ht
  have hlt := hT' t (le_trans (le_max_left _ _) ht)
  have hr := hρb (x t - x₀) (y t - y₀) hlt
  simp only [add_sub_cancel] at hr
  exact angular_alg hD hr

/-- The cross product `w × z` takes positive values at arbitrarily large times (one half of the winding). -/
lemma spiral_cross_pos {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : (a + d) ^ 2 < 4 * (a * d - b * c)) {x y : ℝ → ℝ} (hsol : IsPlanarSol f g x y)
    (hne : ∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀))
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀)) {w₁ w₂ : ℝ}
    (hw : 0 < w₁ ^ 2 + w₂ ^ 2) :
    ∀ T, ∃ t, T ≤ t ∧ 0 < w₁ * (y t - y₀) - w₂ * (x t - x₀) := by
  obtain ⟨s, k, T₀, hs, hk, hT₀, hA⟩ := spiral_angular_data hlin hD hx hy
  intro T
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have ht0 : ∀ t, max T T₀ ≤ t → 0 ≤ t := fun t ht => le_trans hT₀ (le_trans (le_max_right _ _) ht)
  refine no_lower_half (p := fun t => w₁ * (x t - x₀) + w₂ * (y t - y₀))
    (c := fun t => w₁ * (y t - y₀) - w₂ * (x t - x₀))
    (p' := fun t => w₁ * f (x t) (y t) + w₂ * g (x t) (y t))
    (c' := fun t => w₁ * g (x t) (y t) - w₂ * f (x t) (y t)) (s := s) (k := k) (T := max T T₀) hk hs
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have h := hsol t (ht0 t ht)
    exact ((h.1.sub_const x₀).const_mul w₁).add ((h.2.sub_const y₀).const_mul w₂)
  · intro t ht
    have h := hsol t (ht0 t ht)
    exact ((h.2.sub_const y₀).const_mul w₁).sub ((h.1.sub_const x₀).const_mul w₂)
  · intro t ht
    have h := hA t (le_trans (le_max_right _ _) ht)
    have hW := mul_le_mul_of_nonneg_left h hw.le
    show k * ((w₁ * (x t - x₀) + w₂ * (y t - y₀)) ^ 2 + (w₁ * (y t - y₀) - w₂ * (x t - x₀)) ^ 2)
      ≤ s * ((w₁ * (x t - x₀) + w₂ * (y t - y₀)) * (w₁ * g (x t) (y t) - w₂ * f (x t) (y t))
        - (w₁ * (y t - y₀) - w₂ * (x t - x₀)) * (w₁ * f (x t) (y t) + w₂ * g (x t) (y t)))
    nlinarith [hW]
  · intro t ht
    have hz := sq_add_sq_pos_of_ne (u := x t - x₀) (v := y t - y₀)
      (fun h => hne t (ht0 t ht) ⟨by linarith [h.1], by linarith [h.2]⟩)
    show 0 < (w₁ * (x t - x₀) + w₂ * (y t - y₀)) ^ 2 + (w₁ * (y t - y₀) - w₂ * (x t - x₀)) ^ 2
    have : (w₁ * (x t - x₀) + w₂ * (y t - y₀)) ^ 2 + (w₁ * (y t - y₀) - w₂ * (x t - x₀)) ^ 2
        = (w₁ ^ 2 + w₂ ^ 2) * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2) := by ring
    rw [this]; positivity
  · intro t ht
    exact hcon t (le_trans (le_max_left _ _) ht)

/-- **Spiral points wind (DE-222, spiral type in Table 8.1).** Let `(x₀, y₀)` be an almost linear critical point
of `x' = f(x,y)`, `y' = g(x,y)` with Jacobian `[[a, b], [c, d]]` having complex eigenvalues
(`(a + d)² < 4 (ad - bc)`).  If a solution never equals the critical point for `t ≥ 0` and tends to it as `t → ∞`,
then for every nonzero direction `(w₁, w₂)` the cross product `w₁ (y - y₀) - w₂ (x - x₀)` is positive at some
arbitrarily large time and negative at another: the trajectory crosses every line through the critical point
infinitely often, i.e. it spirals. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem spiral_point_winds {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : (a + d) ^ 2 < 4 * (a * d - b * c)) {x y : ℝ → ℝ} (hsol : IsPlanarSol f g x y)
    (hne : ∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀))
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀)) {w₁ w₂ : ℝ}
    (hw : w₁ ≠ 0 ∨ w₂ ≠ 0) :
    ∀ T, ∃ t₁, T ≤ t₁ ∧ ∃ t₂, T ≤ t₂ ∧
      0 < w₁ * (y t₁ - y₀) - w₂ * (x t₁ - x₀) ∧ w₁ * (y t₂ - y₀) - w₂ * (x t₂ - x₀) < 0 := by
  have hW : 0 < w₁ ^ 2 + w₂ ^ 2 := by
    rcases hw with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg w₂]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg w₁]
  intro T
  obtain ⟨t₁, h1, h1'⟩ := spiral_cross_pos hlin hD hsol hne hx hy hW T
  obtain ⟨t₂, h2, h2'⟩ := spiral_cross_pos hlin hD hsol hne hx hy (w₁ := -w₁) (w₂ := -w₂)
    (by nlinarith) T
  exact ⟨t₁, h1, t₂, h2, h1', by nlinarith⟩

/-- **Spiral sinks wind (DE-222, Table 8.1).** At an almost linear critical point with complex eigenvalues of
negative real part (`(a + d)² < 4 (ad - bc)`, `a + d < 0`), there is `δ > 0` such that every solution starting
within `δ` of the point and never equal to it tends to it (asymptotic stability) and winds around it, crossing every
line through the point at arbitrarily large times. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem spiral_sink_winds {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : (a + d) ^ 2 < 4 * (a * d - b * c)) (htr : a + d < 0) :
    ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
      (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 → (∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀)) →
      Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      ∀ w₁ w₂ : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) → ∀ T, ∃ t₁, T ≤ t₁ ∧ ∃ t₂, T ≤ t₂ ∧
        0 < w₁ * (y t₁ - y₀) - w₂ * (x t₁ - x₀) ∧ w₁ * (y t₂ - y₀) - w₂ * (x t₂ - x₀) < 0 := by
  have hdet : 0 < a * d - b * c := by nlinarith [sq_nonneg (a + d)]
  obtain ⟨_, δ, hδ, hconv⟩ := almost_linear_asymp_stable hlin htr hdet
  refine ⟨δ, hδ, fun x y hsol h0 hne => ?_⟩
  obtain ⟨hx, hy⟩ := hconv x y hsol h0
  exact ⟨hx, hy, fun w₁ w₂ hw T => spiral_point_winds hlin hD hsol hne hx hy hw T⟩

/-! ## Nodes do not wind -/

/-- A continuous nowhere-vanishing function on `[t₀, ∞)` has a constant sign there. -/
lemma const_sign {g : ℝ → ℝ} {t₀ : ℝ} (hc : ∀ t, t₀ ≤ t → ContinuousAt g t)
    (hne : ∀ t, t₀ ≤ t → g t ≠ 0) :
    (∀ t, t₀ ≤ t → 0 < g t) ∨ (∀ t, t₀ ≤ t → g t < 0) := by
  have hcont : ∀ t, t₀ ≤ t → ContinuousOn g (Icc t₀ t) :=
    fun t _ x hx => (hc x hx.1).continuousWithinAt
  rcases lt_or_gt_of_ne (hne t₀ le_rfl) with h0 | h0
  · right
    intro t ht
    by_contra hn
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht (hcont t ht) (show (0 : ℝ) ∈ Icc (g t₀) (g t) from
      ⟨h0.le, not_lt.mp hn⟩)
    exact hne s hs.1 hs0
  · left
    intro t ht
    by_contra hn
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht (hcont t ht) (show (0 : ℝ) ∈ Icc (g t) (g t₀) from
      ⟨not_lt.mp hn, h0.le⟩)
    exact hne s hs.1 hs0

/-- Abstract node lemma.  In eigen-coordinates `(α, β)` with `α' = l₁ α + ρ₁`, `β' = l₂ β + ρ₂`, `l₁ < l₂`
and small remainder, the quantity `β² - α²` has positive derivative where it vanishes, so the region
`|β| ≥ |α|` is trapping; hence eventually either `β` or `α` has a constant sign. -/
lemma node_abstract {α β α' β' : ℝ → ℝ} {l₁ l₂ T : ℝ} (hl : l₁ < l₂)
    (hα : ∀ t, T ≤ t → HasDerivAt α (α' t) t) (hβ : ∀ t, T ≤ t → HasDerivAt β (β' t) t)
    (hρ : ∀ t, T ≤ t → (α' t - l₁ * α t) ^ 2 + (β' t - l₂ * β t) ^ 2
      ≤ ((l₂ - l₁) / 4) ^ 2 * (α t ^ 2 + β t ^ 2))
    (hne : ∀ t, T ≤ t → 0 < α t ^ 2 + β t ^ 2) :
    ∃ T', (∀ t, T' ≤ t → 0 < α t) ∨ (∀ t, T' ≤ t → α t < 0) ∨ (∀ t, T' ≤ t → 0 < β t) ∨
      (∀ t, T' ≤ t → β t < 0) := by
  set F : ℝ → ℝ := fun t => β t * β t - α t * α t with hF
  set F' : ℝ → ℝ := fun t => (β' t * β t + β t * β' t) - (α' t * α t + α t * α' t) with hF'
  have hFd : ∀ t, T ≤ t → HasDerivAt F (F' t) t := fun t ht =>
    ((hβ t ht).mul (hβ t ht)).sub ((hα t ht).mul (hα t ht))
  have hpos : ∀ t, T ≤ t → F t = 0 → 0 < F' t := by
    intro t ht h0
    have hS := hne t ht
    have hρt := hρ t ht
    have hgpos : 0 < l₂ - l₁ := by linarith
    obtain ⟨ρ₁, hρ₁⟩ : ∃ r, r = α' t - l₁ * α t := ⟨_, rfl⟩
    obtain ⟨ρ₂, hρ₂⟩ : ∃ r, r = β' t - l₂ * β t := ⟨_, rfl⟩
    rw [← hρ₁, ← hρ₂] at hρt
    have he2 : (β t * ρ₂ - α t * ρ₁) ^ 2 ≤ ((l₂ - l₁) / 4 * (α t ^ 2 + β t ^ 2)) ^ 2 := by
      have h1 : (β t * ρ₂ - α t * ρ₁) ^ 2 ≤ (α t ^ 2 + β t ^ 2) * (ρ₁ ^ 2 + ρ₂ ^ 2) := by
        nlinarith [sq_nonneg (α t * ρ₂ + β t * ρ₁)]
      calc (β t * ρ₂ - α t * ρ₁) ^ 2 ≤ _ := h1
        _ ≤ (α t ^ 2 + β t ^ 2) * (((l₂ - l₁) / 4) ^ 2 * (α t ^ 2 + β t ^ 2)) :=
          mul_le_mul_of_nonneg_left hρt hS.le
        _ = _ := by ring
    have he := (abs_le.mp (abs_le_of_sq_le_sq he2 (mul_nonneg (by linarith) hS.le))).1
    have hFt : F' t = 2 * (l₂ * β t ^ 2 - l₁ * α t ^ 2) + 2 * (β t * ρ₂ - α t * ρ₁) := by
      rw [hρ₁, hρ₂]; simp only [F']; ring
    have hβα : β t ^ 2 = α t ^ 2 := by simp only [F] at h0; nlinarith
    have hS2 : α t ^ 2 + β t ^ 2 = 2 * α t ^ 2 := by rw [hβα]; ring
    have hα2 : 0 < α t ^ 2 := by linarith
    rw [hS2] at he
    have hexp : l₂ * β t ^ 2 - l₁ * α t ^ 2 = (l₂ - l₁) * α t ^ 2 := by rw [hβα]; ring
    rw [hFt, hexp]
    nlinarith [mul_pos hgpos hα2]
  have htrap : ∀ t₀, T ≤ t₀ → 0 ≤ F t₀ → ∀ t, t₀ ≤ t → 0 ≤ F t := by
    intro t₀ ht₀ h0 t ht
    have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun s => -F s) (a := t₀) (b := t)
      (f' := fun s => -F' s) (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ))
      (fun s hs => (hFd s (le_trans ht₀ hs.1)).neg.continuousAt.continuousWithinAt)
      (fun s hs => (hFd s (le_trans ht₀ hs.1)).neg.hasDerivWithinAt)
      (by simpa using h0)
      continuousOn_const
      (fun s _ => (hasDerivAt_const s (0 : ℝ)).hasDerivWithinAt)
      (fun s hs h => by
        have := hpos s (le_trans ht₀ hs.1) (by simpa using h)
        show -F' s < 0
        linarith)
    have := key (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)
    simpa using this
  by_cases h : ∃ t₀, T ≤ t₀ ∧ 0 ≤ F t₀
  · obtain ⟨t₀, ht₀, h0⟩ := h
    have hβne : ∀ t, t₀ ≤ t → β t ≠ 0 := by
      intro t ht hb
      have hFt := htrap t₀ ht₀ h0 t ht
      have hS := hne t (le_trans ht₀ ht)
      simp only [F] at hFt
      rw [hb] at hFt hS
      nlinarith [sq_nonneg (α t)]
    rcases const_sign (fun t ht => (hβ t (le_trans ht₀ ht)).continuousAt) hβne with h1 | h1
    · exact ⟨t₀, Or.inr (Or.inr (Or.inl h1))⟩
    · exact ⟨t₀, Or.inr (Or.inr (Or.inr h1))⟩
  · have h' : ∀ t₀, T ≤ t₀ → F t₀ < 0 := fun t₀ ht₀ => not_le.mp (fun hh => h ⟨t₀, ht₀, hh⟩)
    have hαne : ∀ t, T ≤ t → α t ≠ 0 := by
      intro t ht ha
      have := h' t ht
      simp only [F] at this
      rw [ha] at this
      nlinarith [sq_nonneg (β t)]
    rcases const_sign (fun t ht => (hα t ht).continuousAt) hαne with h1 | h1
    · exact ⟨T, Or.inl h1⟩
    · exact ⟨T, Or.inr (Or.inl h1)⟩

/-- Every root `l` of the characteristic polynomial of `[[a, b], [c, d]]` has a nonzero left eigenvector. -/
lemma left_eigvec {a b c d l : ℝ} (hl : l ^ 2 - (a + d) * l + (a * d - b * c) = 0) :
    ∃ p q : ℝ, (p ≠ 0 ∨ q ≠ 0) ∧ p * a + q * c = l * p ∧ p * b + q * d = l * q := by
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · subst hc; subst hb
      have : (l - a) * (l - d) = 0 := by linear_combination hl
      rcases mul_eq_zero.mp this with h | h
      · refine ⟨1, 0, Or.inl one_ne_zero, ?_, ?_⟩ <;> linarith
      · refine ⟨0, 1, Or.inr one_ne_zero, ?_, ?_⟩ <;> linarith
    · subst hc
      exact ⟨l - d, b, Or.inr hb, by linear_combination (-1) * hl, by ring⟩
  · exact ⟨c, l - a, Or.inl hc, by ring, by linear_combination (-1) * hl⟩

/-- Left eigenvectors for distinct eigenvalues are linearly independent. -/
lemma left_eigvec_indep {a b c d l₁ l₂ p₁ q₁ p₂ q₂ : ℝ} (hl : l₁ ≠ l₂) (h1 : p₁ ≠ 0 ∨ q₁ ≠ 0)
    (h2 : p₂ ≠ 0 ∨ q₂ ≠ 0) (e1 : p₁ * a + q₁ * c = l₁ * p₁) (e1' : p₁ * b + q₁ * d = l₁ * q₁)
    (e2 : p₂ * a + q₂ * c = l₂ * p₂) (e2' : p₂ * b + q₂ * d = l₂ * q₂) : p₁ * q₂ - p₂ * q₁ ≠ 0 := by
  intro hδ
  have hsub : l₂ - l₁ ≠ 0 := sub_ne_zero.mpr hl.symm
  have hp : (l₂ - l₁) * (p₁ * p₂) = 0 := by linear_combination (-p₁) * e2 + p₂ * e1 + c * hδ
  have hq : (l₂ - l₁) * (q₁ * q₂) = 0 := by linear_combination (-q₁) * e2' + q₂ * e1' - b * hδ
  have hp' : p₁ * p₂ = 0 := (mul_eq_zero.mp hp).resolve_left hsub
  have hq' : q₁ * q₂ = 0 := (mul_eq_zero.mp hq).resolve_left hsub
  rcases mul_eq_zero.mp hp' with hp1 | hp2 <;> rcases mul_eq_zero.mp hq' with hq1 | hq2
  · rcases h1 with h | h <;> contradiction
  · subst hp1; subst hq2
    have : p₂ * q₁ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · rcases h2 with h' | h' <;> simp_all
    · rcases h1 with h' | h' <;> simp_all
  · subst hp2; subst hq1
    have : p₁ * q₂ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · rcases h1 with h' | h' <;> simp_all
    · rcases h2 with h' | h' <;> simp_all
  · rcases h2 with h | h <;> contradiction

/-- Cauchy-Schwarz for two rows. -/
lemma node_cauchy (p₁ q₁ p₂ q₂ r₁ r₂ : ℝ) :
    (p₁ * r₁ + q₁ * r₂) ^ 2 + (p₂ * r₁ + q₂ * r₂) ^ 2
      ≤ (p₁ ^ 2 + q₁ ^ 2 + p₂ ^ 2 + q₂ ^ 2) * (r₁ ^ 2 + r₂ ^ 2) := by
  nlinarith [sq_nonneg (p₁ * r₂ - q₁ * r₁), sq_nonneg (p₂ * r₂ - q₂ * r₁)]

/-- Eigen-coordinates control the size of `(u, v)`. -/
lemma node_coord_bound (p₁ q₁ p₂ q₂ u v : ℝ) :
    (p₁ * q₂ - p₂ * q₁) ^ 2 * (u ^ 2 + v ^ 2)
      ≤ (p₁ ^ 2 + q₁ ^ 2 + p₂ ^ 2 + q₂ ^ 2) * ((p₁ * u + q₁ * v) ^ 2 + (p₂ * u + q₂ * v) ^ 2) := by
  obtain ⟨α, hα⟩ : ∃ α, α = p₁ * u + q₁ * v := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = p₂ * u + q₂ * v := ⟨_, rfl⟩
  have e1 : (p₁ * q₂ - p₂ * q₁) * u = q₂ * α - q₁ * β := by rw [hα, hβ]; ring
  have e2 : (p₁ * q₂ - p₂ * q₁) * v = p₁ * β - p₂ * α := by rw [hα, hβ]; ring
  have h1 : ((p₁ * q₂ - p₂ * q₁) * u) ^ 2 ≤ (q₁ ^ 2 + q₂ ^ 2) * (α ^ 2 + β ^ 2) := by
    rw [e1]; nlinarith [sq_nonneg (q₂ * β + q₁ * α)]
  have h2 : ((p₁ * q₂ - p₂ * q₁) * v) ^ 2 ≤ (p₁ ^ 2 + p₂ ^ 2) * (α ^ 2 + β ^ 2) := by
    rw [e2]; nlinarith [sq_nonneg (p₁ * α + p₂ * β)]
  rw [← hα, ← hβ]
  nlinarith [h1, h2]

/-- **Nodes do not wind (DE-222, node type in Table 8.1).** Let `(x₀, y₀)` be an almost linear critical point with
real distinct eigenvalues of the Jacobian (`(a + d)² > 4 (ad - bc)`; this covers nodes, saddles being the case
`ad - bc < 0`).  A solution that never equals the point and tends to it eventually stays on one side of a line
through the point: there are a nonzero direction `(w₁, w₂)` and `T` such that `w₁ (y - y₀) - w₂ (x - x₀)` is
`≥ 0` for all `t ≥ T`, or `≤ 0` for all `t ≥ T`.  So it does not spiral (compare `spiral_point_winds`). -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem node_point_no_winding {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : 4 * (a * d - b * c) < (a + d) ^ 2) {x y : ℝ → ℝ} (hsol : IsPlanarSol f g x y)
    (hne : ∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀))
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀)) :
    ∃ w₁ w₂ T : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) ∧
      ((∀ t, T ≤ t → 0 ≤ w₁ * (y t - y₀) - w₂ * (x t - x₀)) ∨
        (∀ t, T ≤ t → w₁ * (y t - y₀) - w₂ * (x t - x₀) ≤ 0)) := by
  have hDpos : 0 < (a + d) ^ 2 - 4 * (a * d - b * c) := by linarith
  obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt ((a + d) ^ 2 - 4 * (a * d - b * c)) := ⟨_, rfl⟩
  have hRpos : 0 < R := by rw [hR]; exact Real.sqrt_pos.mpr hDpos
  have hR2 : R ^ 2 = (a + d) ^ 2 - 4 * (a * d - b * c) := by rw [hR]; exact Real.sq_sqrt hDpos.le
  obtain ⟨l₁, hl₁⟩ : ∃ l, l = ((a + d) - R) / 2 := ⟨_, rfl⟩
  obtain ⟨l₂, hl₂⟩ : ∃ l, l = ((a + d) + R) / 2 := ⟨_, rfl⟩
  have hch1 : l₁ ^ 2 - (a + d) * l₁ + (a * d - b * c) = 0 := by
    rw [hl₁]; linear_combination (1 / 4) * hR2
  have hch2 : l₂ ^ 2 - (a + d) * l₂ + (a * d - b * c) = 0 := by
    rw [hl₂]; linear_combination (1 / 4) * hR2
  have hl12 : l₁ < l₂ := by rw [hl₁, hl₂]; linarith
  have hgap : l₂ - l₁ = R := by rw [hl₁, hl₂]; ring
  obtain ⟨p₁, q₁, hv₁, e₁, e₁'⟩ := left_eigvec hch1
  obtain ⟨p₂, q₂, hv₂, e₂, e₂'⟩ := left_eigvec hch2
  have hδ := left_eigvec_indep hl12.ne hv₁ hv₂ e₁ e₁' e₂ e₂'
  have hδ2 : 0 < (p₁ * q₂ - p₂ * q₁) ^ 2 := by positivity
  obtain ⟨S, hSdef⟩ : ∃ S, S = p₁ ^ 2 + q₁ ^ 2 + p₂ ^ 2 + q₂ ^ 2 := ⟨_, rfl⟩
  have hS : 0 < S := by
    rw [hSdef]
    rcases hv₁ with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg q₁, sq_nonneg p₂, sq_nonneg q₂]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg p₁, sq_nonneg p₂, sq_nonneg q₂]
  obtain ⟨η, hη⟩ : ∃ η, η = (l₂ - l₁) / 4 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨ρ, hρ, hρb⟩ := hlin (η ^ 2 * (p₁ * q₂ - p₂ * q₁) ^ 2 / S ^ 2)
    (div_pos (mul_pos (pow_pos hηpos 2) hδ2) (pow_pos hS 2))
  have hlim : Tendsto (fun t => (x t - x₀) ^ 2 + (y t - y₀) ^ 2) atTop (𝓝 (0 ^ 2 + 0 ^ 2)) :=
    (((hx.sub_const x₀).pow 2).add ((hy.sub_const y₀).pow 2)).congr' (by simp) |>.trans (by simp)
  have hev : ∀ᶠ t in atTop, (x t - x₀) ^ 2 + (y t - y₀) ^ 2 < ρ ^ 2 :=
    hlim.eventually_lt_const (by nlinarith [hρ])
  obtain ⟨T', hT'⟩ := eventually_atTop.mp hev
  have ht0 : ∀ t, max T' 0 ≤ t → 0 ≤ t := fun t ht => le_trans (le_max_right _ _) ht
  have hmain := node_abstract (α := fun t => p₁ * (x t - x₀) + q₁ * (y t - y₀))
    (β := fun t => p₂ * (x t - x₀) + q₂ * (y t - y₀))
    (α' := fun t => p₁ * f (x t) (y t) + q₁ * g (x t) (y t))
    (β' := fun t => p₂ * f (x t) (y t) + q₂ * g (x t) (y t)) (l₁ := l₁) (l₂ := l₂) (T := max T' 0) hl12
    (fun t ht => by
      have h := hsol t (ht0 t ht)
      exact ((h.1.sub_const x₀).const_mul p₁).add ((h.2.sub_const y₀).const_mul q₁))
    (fun t ht => by
      have h := hsol t (ht0 t ht)
      exact ((h.1.sub_const x₀).const_mul p₂).add ((h.2.sub_const y₀).const_mul q₂))
    (fun t ht => by
      have hlt := hT' t (le_trans (le_max_left _ _) ht)
      have hr := hρb (x t - x₀) (y t - y₀) hlt
      simp only [add_sub_cancel] at hr
      show (p₁ * f (x t) (y t) + q₁ * g (x t) (y t) - l₁ * (p₁ * (x t - x₀) + q₁ * (y t - y₀))) ^ 2
        + (p₂ * f (x t) (y t) + q₂ * g (x t) (y t) - l₂ * (p₂ * (x t - x₀) + q₂ * (y t - y₀))) ^ 2
        ≤ ((l₂ - l₁) / 4) ^ 2 * ((p₁ * (x t - x₀) + q₁ * (y t - y₀)) ^ 2
          + (p₂ * (x t - x₀) + q₂ * (y t - y₀)) ^ 2)
      obtain ⟨u, hu⟩ : ∃ u, u = x t - x₀ := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v, v = y t - y₀ := ⟨_, rfl⟩
      obtain ⟨r₁, hr₁⟩ : ∃ r, r = f (x t) (y t) - (a * u + b * v) := ⟨_, rfl⟩
      obtain ⟨r₂, hr₂⟩ : ∃ r, r = g (x t) (y t) - (c * u + d * v) := ⟨_, rfl⟩
      rw [← hu, ← hv] at hr ⊢
      rw [← hu, ← hv] at hlt
      rw [← hr₁, ← hr₂] at hr
      have hf : f (x t) (y t) = a * u + b * v + r₁ := by rw [hr₁]; ring
      have hg : g (x t) (y t) = c * u + d * v + r₂ := by rw [hr₂]; ring
      rw [hf, hg]
      have hA1 : p₁ * (a * u + b * v + r₁) + q₁ * (c * u + d * v + r₂)
          - l₁ * (p₁ * u + q₁ * v) = p₁ * r₁ + q₁ * r₂ := by
        linear_combination u * e₁ + v * e₁'
      have hA2 : p₂ * (a * u + b * v + r₁) + q₂ * (c * u + d * v + r₂)
          - l₂ * (p₂ * u + q₂ * v) = p₂ * r₁ + q₂ * r₂ := by
        linear_combination u * e₂ + v * e₂'
      rw [hA1, hA2, ← hη]
      have hsum : (p₁ * r₁ + q₁ * r₂) ^ 2 + (p₂ * r₁ + q₂ * r₂) ^ 2 ≤ S * (r₁ ^ 2 + r₂ ^ 2) := by
        rw [hSdef]; exact node_cauchy _ _ _ _ _ _
      have hz : (p₁ * q₂ - p₂ * q₁) ^ 2 * (u ^ 2 + v ^ 2)
          ≤ S * ((p₁ * u + q₁ * v) ^ 2 + (p₂ * u + q₂ * v) ^ 2) := by
        rw [hSdef]; exact node_coord_bound _ _ _ _ _ _
      have hε : S * ((η ^ 2 * (p₁ * q₂ - p₂ * q₁) ^ 2 / S ^ 2) * (u ^ 2 + v ^ 2))
          = η ^ 2 / S * ((p₁ * q₂ - p₂ * q₁) ^ 2 * (u ^ 2 + v ^ 2)) := by
        field_simp
      calc (p₁ * r₁ + q₁ * r₂) ^ 2 + (p₂ * r₁ + q₂ * r₂) ^ 2 ≤ S * (r₁ ^ 2 + r₂ ^ 2) := hsum
        _ ≤ S * ((η ^ 2 * (p₁ * q₂ - p₂ * q₁) ^ 2 / S ^ 2) * (u ^ 2 + v ^ 2)) :=
          mul_le_mul_of_nonneg_left hr hS.le
        _ = η ^ 2 / S * ((p₁ * q₂ - p₂ * q₁) ^ 2 * (u ^ 2 + v ^ 2)) := hε
        _ ≤ η ^ 2 / S * (S * ((p₁ * u + q₁ * v) ^ 2 + (p₂ * u + q₂ * v) ^ 2)) :=
          mul_le_mul_of_nonneg_left hz (by positivity)
        _ = η ^ 2 * ((p₁ * u + q₁ * v) ^ 2 + (p₂ * u + q₂ * v) ^ 2) := by field_simp)
    (fun t ht => by
      have hz0 := sq_add_sq_pos_of_ne (u := x t - x₀) (v := y t - y₀)
        (fun h => hne t (ht0 t ht) ⟨by linarith [h.1], by linarith [h.2]⟩)
      show 0 < (p₁ * (x t - x₀) + q₁ * (y t - y₀)) ^ 2 + (p₂ * (x t - x₀) + q₂ * (y t - y₀)) ^ 2
      by_contra hh
      have hz : (p₁ * q₂ - p₂ * q₁) ^ 2 * ((x t - x₀) ^ 2 + (y t - y₀) ^ 2)
          ≤ S * ((p₁ * (x t - x₀) + q₁ * (y t - y₀)) ^ 2 + (p₂ * (x t - x₀) + q₂ * (y t - y₀)) ^ 2) := by
        rw [hSdef]; exact node_coord_bound _ _ _ _ _ _
      have := mul_nonpos_of_nonneg_of_nonpos hS.le (not_lt.mp hh)
      have := mul_pos hδ2 hz0
      linarith)
  obtain ⟨T₁, h | h | h | h⟩ := hmain
  · refine ⟨q₁, -p₁, T₁, ?_, Or.inl fun t ht => ?_⟩
    · rcases hv₁ with h' | h'
      · exact Or.inr (neg_ne_zero.mpr h')
      · exact Or.inl h'
    · have := h t ht; beta_reduce at this; linarith
  · refine ⟨q₁, -p₁, T₁, ?_, Or.inr fun t ht => ?_⟩
    · rcases hv₁ with h' | h'
      · exact Or.inr (neg_ne_zero.mpr h')
      · exact Or.inl h'
    · have := h t ht; beta_reduce at this; linarith
  · refine ⟨q₂, -p₂, T₁, ?_, Or.inl fun t ht => ?_⟩
    · rcases hv₂ with h' | h'
      · exact Or.inr (neg_ne_zero.mpr h')
      · exact Or.inl h'
    · have := h t ht; beta_reduce at this; linarith
  · refine ⟨q₂, -p₂, T₁, ?_, Or.inr fun t ht => ?_⟩
    · rcases hv₂ with h' | h'
      · exact Or.inr (neg_ne_zero.mpr h')
      · exact Or.inl h'
    · have := h t ht; beta_reduce at this; linarith

/-- **Node sinks do not wind (DE-222, Table 8.1).** If `(a + d)² > 4 (ad - bc) > 0` and `a + d < 0` (both
eigenvalues real and negative: asymptotically stable node), there is `δ > 0` such that every solution starting
within `δ` of the point and never equal to it tends to it and eventually stays on one side of a line through it. -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem node_sink_no_winding {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (hD : 4 * (a * d - b * c) < (a + d) ^ 2) (htr : a + d < 0) (hdet : 0 < a * d - b * c) :
    ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
      (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 → (∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀)) →
      Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      ∃ w₁ w₂ T : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) ∧
        ((∀ t, T ≤ t → 0 ≤ w₁ * (y t - y₀) - w₂ * (x t - x₀)) ∨
          (∀ t, T ≤ t → w₁ * (y t - y₀) - w₂ * (x t - x₀) ≤ 0)) := by
  obtain ⟨_, δ, hδ, hconv⟩ := almost_linear_asymp_stable hlin htr hdet
  refine ⟨δ, hδ, fun x y hsol h0 hne => ?_⟩
  obtain ⟨hx, hy⟩ := hconv x y hsol h0
  exact ⟨hx, hy, node_point_no_winding hlin hD hsol hne hx hy⟩

/-- **Type of an asymptotically stable almost linear point (DE-222, Table 8.1).** With `a + d < 0` and
`ad - bc > 0`: complex eigenvalues give a spiral sink (nearby solutions wind around the point, crossing every line
through it at arbitrarily large times), and real distinct eigenvalues give a node sink (nearby solutions eventually
stay on one side of a line through it, so they do not wind). -/
@[kb "lebldiffyqs2026" "Table 8.1, p. 358"]
theorem almost_linear_type_sink {f g : ℝ → ℝ → ℝ} {x₀ y₀ a b c d : ℝ}
    (hlin : ∀ ε > 0, ∃ ρ > 0, ∀ u v, u ^ 2 + v ^ 2 < ρ ^ 2 →
      (f (x₀ + u) (y₀ + v) - (a * u + b * v)) ^ 2 + (g (x₀ + u) (y₀ + v) - (c * u + d * v)) ^ 2
        ≤ ε * (u ^ 2 + v ^ 2))
    (htr : a + d < 0) (hdet : 0 < a * d - b * c) :
    ((a + d) ^ 2 < 4 * (a * d - b * c) →
      ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
        (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 → (∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀)) →
        Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
        ∀ w₁ w₂ : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) → ∀ T, ∃ t₁, T ≤ t₁ ∧ ∃ t₂, T ≤ t₂ ∧
          0 < w₁ * (y t₁ - y₀) - w₂ * (x t₁ - x₀) ∧ w₁ * (y t₂ - y₀) - w₂ * (x t₂ - x₀) < 0) ∧
    (4 * (a * d - b * c) < (a + d) ^ 2 →
      ∃ δ > 0, ∀ x y : ℝ → ℝ, IsPlanarSol f g x y →
        (x 0 - x₀) ^ 2 + (y 0 - y₀) ^ 2 < δ ^ 2 → (∀ t, 0 ≤ t → ¬(x t = x₀ ∧ y t = y₀)) →
        Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
        ∃ w₁ w₂ T : ℝ, (w₁ ≠ 0 ∨ w₂ ≠ 0) ∧
          ((∀ t, T ≤ t → 0 ≤ w₁ * (y t - y₀) - w₂ * (x t - x₀)) ∨
            (∀ t, T ≤ t → w₁ * (y t - y₀) - w₂ * (x t - x₀) ≤ 0))) :=
  ⟨fun hD => spiral_sink_winds hlin hD htr, fun hD => node_sink_no_winding hlin hD htr hdet⟩

end UndergradKB.DifferentialEquations
