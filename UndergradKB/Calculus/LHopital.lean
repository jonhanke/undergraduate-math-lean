import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set Filter Topology

theorem cauchy_step_lt {f g f' g' : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y) (hg : ∀ y ∈ s, HasDerivAt g (g' y) y)
    (hg' : ∀ y ∈ s, g' y ≠ 0) {L ε : ℝ} (hb : ∀ y ∈ s, |f' y / g' y - L| < ε)
    {p q : ℝ} (hp : p ∈ s) (hq : q ∈ s) (hlt : p < q) :
    g q - g p ≠ 0 ∧ |(f q - f p) / (g q - g p) - L| < ε := by
  have hsub : Icc p q ⊆ s := hs.out hp hq
  have hfc : ContinuousOn f (Icc p q) := fun y hy => (hf y (hsub hy)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc p q) := fun y hy => (hg y (hsub hy)).continuousAt.continuousWithinAt
  have hIoo : Ioo p q ⊆ s := fun y hy => hsub (Ioo_subset_Icc_self hy)
  obtain ⟨ξ, hξ, e⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hlt hfc
    (fun y hy => hf y (hIoo hy)) g g' hgc (fun y hy => hg y (hIoo hy))
  obtain ⟨η, hη, e2⟩ := exists_hasDerivAt_eq_slope g g' hlt hgc (fun y hy => hg y (hIoo hy))
  have hne : g q - g p ≠ 0 := by
    intro h0
    rw [h0, zero_div] at e2
    exact hg' η (hIoo hη) e2
  refine ⟨hne, ?_⟩
  have h1 : (f q - f p) / (g q - g p) = f' ξ / g' ξ := by
    have := hg' ξ (hIoo hξ)
    rw [div_eq_div_iff hne this]
    linarith
  rw [h1]
  exact hb ξ (hIoo hξ)

theorem cauchy_step {f g f' g' : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y) (hg : ∀ y ∈ s, HasDerivAt g (g' y) y)
    (hg' : ∀ y ∈ s, g' y ≠ 0) {L ε : ℝ} (hb : ∀ y ∈ s, |f' y / g' y - L| < ε)
    {x c : ℝ} (hx : x ∈ s) (hc : c ∈ s) (hne : x ≠ c) :
    g x - g c ≠ 0 ∧ |(f x - f c) / (g x - g c) - L| < ε := by
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨h1, h2⟩ := cauchy_step_lt hs hf hg hg' hb hx hc h
    refine ⟨?_, ?_⟩
    · intro h0; apply h1; linarith
    · have : (f x - f c) / (g x - g c) = (f c - f x) / (g c - g x) := by
        rw [← neg_sub (f x), ← neg_sub (g x), neg_div_neg_eq]
      rw [this]; exact h2
  · exact cauchy_step_lt hs hf hg hg' hb hc hx h

/-- Core of the ∞/∞ rule: abstract filter version. -/
theorem lhopital_core {l : Filter ℝ} {f g : ℝ → ℝ} {L : ℝ}
    (hg : Tendsto (fun x => |g x|) l atTop)
    (hC : ∀ ε > 0, ∃ c, ∀ᶠ x in l, g x - g c ≠ 0 ∧ |(f x - f c) / (g x - g c) - L| < ε) :
    Tendsto (fun x => f x / g x) l (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨c, hc⟩ := hC (min 1 (ε / 2)) (lt_min one_pos (by linarith))
  set B := (|L| + 1) * |g c| + |f c| with hB
  have hB0 : 0 ≤ B := by positivity
  have hbig : ∀ᶠ x in l, 2 * B / ε < |g x| := hg.eventually_gt_atTop _
  have hpos : ∀ᶠ x in l, 0 < |g x| := hg.eventually_gt_atTop 0
  filter_upwards [hc, hbig, hpos] with x ⟨hne, hlt⟩ hbx hpx
  set h := (f x - f c) / (g x - g c) with hh
  have hgx : g x ≠ 0 := abs_pos.mp hpx
  have hlt1 : |h - L| < 1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt2 : |h - L| < ε / 2 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hhabs : |h| ≤ |L| + 1 := by
    have := abs_sub_abs_le_abs_sub h L
    linarith
  have hid : f x / g x - L = (h - L) - h * g c / g x + f c / g x := by
    have : f x = h * (g x - g c) + f c := by
      rw [hh]; field_simp; ring
    rw [this]; field_simp; ring
  have hsmall : B / |g x| < ε / 2 := by
    rw [div_lt_iff₀ hpx]
    have := (div_lt_iff₀ hε).mp hbx
    linarith
  have hbound : |h * g c / g x - f c / g x| ≤ B / |g x| := by
    rw [← sub_div, abs_div, div_le_div_iff_of_pos_right hpx]
    calc |h * g c - f c| ≤ |h * g c| + |f c| := abs_sub _ _
      _ = |h| * |g c| + |f c| := by rw [abs_mul]
      _ ≤ B := by
        have := mul_le_mul_of_nonneg_right hhabs (abs_nonneg (g c))
        linarith
  rw [Real.dist_eq, hid]
  have e : (h - L) - h * g c / g x + f c / g x = (h - L) - (h * g c / g x - f c / g x) := by ring
  rw [e]
  calc |(h - L) - (h * g c / g x - f c / g x)| ≤ |h - L| + |h * g c / g x - f c / g x| := abs_sub _ _
    _ < ε := by linarith

theorem lhopital_aux {l : Filter ℝ} {f g f' g' : ℝ → ℝ} {L : ℝ}
    (hgt : Tendsto (fun x => |g x|) l atTop)
    (hfam : ∀ ε > 0, ∃ s : Set ℝ, s.OrdConnected ∧
      (∀ y ∈ s, HasDerivAt f (f' y) y ∧ HasDerivAt g (g' y) y ∧ g' y ≠ 0 ∧
        |f' y / g' y - L| < ε) ∧
      ∃ c ∈ s, ∀ᶠ x in l, x ∈ s ∧ x ≠ c) :
    Tendsto (fun x => f x / g x) l (𝓝 L) := by
  refine lhopital_core hgt fun ε hε => ?_
  obtain ⟨s, hs, hP, c, hc, hev⟩ := hfam ε hε
  refine ⟨c, ?_⟩
  filter_upwards [hev] with x ⟨hx, hxc⟩
  exact cauchy_step hs (fun y hy => (hP y hy).1) (fun y hy => (hP y hy).2.1)
    (fun y hy => (hP y hy).2.2.1) (fun y hy => (hP y hy).2.2.2) hx hc hxc

theorem eventually_quot_near {l : Filter ℝ} {f' g' : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto (fun x => f' x / g' x) l (𝓝 L)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, |f' x / g' x - L| < ε := by
  have := Metric.tendsto_nhds.mp hlim ε hε
  simpa [Real.dist_eq] using this

/-- OpenStax Calculus 1:Theorem 4.13 (CA-164), right-hand limit at `a`, `∞/∞` form: `|g| → ∞`
as `x → a⁺`, `f, g` differentiable near `a` on the right with `g' ≠ 0`, and `f'/g' → L`
imply `f/g → L`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.13, p. 406"]
theorem lhopital_infty_nhdsGT {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x) (hg : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in 𝓝[>] a, g' x ≠ 0)
    (hgt : Tendsto (fun x => |g x|) (𝓝[>] a) atTop)
    (hlim : Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L) := by
  refine lhopital_aux (f' := f') (g' := g') hgt fun ε hε => ?_
  have hall := hf.and (hg.and (hg'.and (eventually_quot_near hlim hε)))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  have hau : a < u := hu
  refine ⟨Ioo a u, ordConnected_Ioo, fun y hy => ?_, (a + u) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hsub hy
    exact ⟨h1, h2, h3, h4⟩
  · filter_upwards [Ioo_mem_nhdsGT (show a < (a + u) / 2 by linarith)] with x hx
    exact ⟨⟨hx.1, by linarith [hx.2]⟩, by linarith [hx.2]⟩

/-- OpenStax Calculus 1:Theorem 4.13 (CA-164), left-hand limit at `a`, `∞/∞` form. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.13, p. 406"]
theorem lhopital_infty_nhdsLT {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x) (hg : ∀ᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in 𝓝[<] a, g' x ≠ 0)
    (hgt : Tendsto (fun x => |g x|) (𝓝[<] a) atTop)
    (hlim : Tendsto (fun x => f' x / g' x) (𝓝[<] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[<] a) (𝓝 L) := by
  refine lhopital_aux (f' := f') (g' := g') hgt fun ε hε => ?_
  have hall := hf.and (hg.and (hg'.and (eventually_quot_near hlim hε)))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hall
  have hau : u < a := hu
  refine ⟨Ioo u a, ordConnected_Ioo, fun y hy => ?_, (u + a) / 2, ⟨by linarith, by linarith⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hsub hy
    exact ⟨h1, h2, h3, h4⟩
  · filter_upwards [Ioo_mem_nhdsLT (show (u + a) / 2 < a by linarith)] with x hx
    exact ⟨⟨by linarith [hx.1], hx.2⟩, by linarith [hx.1]⟩

/-- OpenStax Calculus 1:Theorem 4.13 (CA-164), two-sided limit at `a` (punctured neighbourhood). -/
@[kb "openstaxcalculus2016" "1:Theorem 4.13, p. 406"]
theorem lhopital_infty_nhdsNE {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x) (hg : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hgt : Tendsto (fun x => |g x|) (𝓝[≠] a) atTop)
    (hlim : Tendsto (fun x => f' x / g' x) (𝓝[≠] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 L) := by
  rw [← nhdsLT_sup_nhdsGT] at hf hg hg' hgt hlim ⊢
  rw [eventually_sup] at hf hg hg'
  exact (lhopital_infty_nhdsLT hf.1 hg.1 hg'.1 (hgt.mono_left le_sup_left)
    (hlim.mono_left le_sup_left)).sup
    (lhopital_infty_nhdsGT hf.2 hg.2 hg'.2 (hgt.mono_left le_sup_right)
    (hlim.mono_left le_sup_right))

/-- OpenStax Calculus 1:Theorem 4.13 (CA-164), limit at `+∞`, `∞/∞` form. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.13, p. 406"]
theorem lhopital_infty_atTop {f g f' g' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in atTop, HasDerivAt f (f' x) x) (hg : ∀ᶠ x in atTop, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in atTop, g' x ≠ 0)
    (hgt : Tendsto (fun x => |g x|) atTop atTop)
    (hlim : Tendsto (fun x => f' x / g' x) atTop (𝓝 L)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 L) := by
  refine lhopital_aux (f' := f') (g' := g') hgt fun ε hε => ?_
  have hall := hf.and (hg.and (hg'.and (eventually_quot_near hlim hε)))
  obtain ⟨u, hsub⟩ := eventually_atTop.mp hall
  refine ⟨Ici u, ordConnected_Ici, fun y hy => ?_, u, self_mem_Ici, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hsub y hy
    exact ⟨h1, h2, h3, h4⟩
  · filter_upwards [eventually_gt_atTop u] with x hx
    exact ⟨hx.le, hx.ne'⟩

/-- OpenStax Calculus 1:Theorem 4.13 (CA-164), limit at `-∞`, `∞/∞` form. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.13, p. 406"]
theorem lhopital_infty_atBot {f g f' g' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in atBot, HasDerivAt f (f' x) x) (hg : ∀ᶠ x in atBot, HasDerivAt g (g' x) x)
    (hg' : ∀ᶠ x in atBot, g' x ≠ 0)
    (hgt : Tendsto (fun x => |g x|) atBot atTop)
    (hlim : Tendsto (fun x => f' x / g' x) atBot (𝓝 L)) :
    Tendsto (fun x => f x / g x) atBot (𝓝 L) := by
  refine lhopital_aux (f' := f') (g' := g') hgt fun ε hε => ?_
  have hall := hf.and (hg.and (hg'.and (eventually_quot_near hlim hε)))
  obtain ⟨u, hsub⟩ := eventually_atBot.mp hall
  refine ⟨Iic u, ordConnected_Iic, fun y hy => ?_, u, self_mem_Iic, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hsub y hy
    exact ⟨h1, h2, h3, h4⟩
  · filter_upwards [eventually_lt_atBot u] with x hx
    exact ⟨hx.le, hx.ne⟩

end UndergradKB.Calculus
