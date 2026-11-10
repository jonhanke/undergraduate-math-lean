import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Artanh
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HyperbolicDisc2
import UndergradKB.Geometry.Inversion

/-! # H-lines, h-segments and h-motions in the conformal disc model (Petrunin, chapter 12)

Builds on `HyperbolicDisc` and `HyperbolicDisc2`.  Contents: Corollary 10.18 (a unique h-line
through two points of the disc), Möbius maps and rotations send h-lines to h-lines, h-segments,
the equality case of the triangle inequality (Claim 12.14), additivity along any h-line
(Lemma 12.9), Exercise 12.3, Axiom II (Claim 12.15) and Claim 12.20 for an arbitrary h-line. -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-- The defining expression of the circline of `hline α c`: `z` lies on it iff this vanishes. -/
noncomputable def hE (α : ℝ) (c z : ℂ) : ℝ := α * (‖z‖ ^ 2 + 1) - 2 * (conj c * z).re

theorem hE_coord (α : ℝ) (c z : ℂ) :
    hE α c z = α * (z.re ^ 2 + z.im ^ 2 + 1) - 2 * (c.re * z.re + c.im * z.im) := by
  unfold hE; rw [sq_norm_eq, re_conj_mul]

theorem mem_hline_iff {α : ℝ} {c z : ℂ} : z ∈ hline α c ↔ ‖z‖ < 1 ∧ hE α c z = 0 := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by unfold hE; linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by unfold hE at h2; linarith⟩

theorem norm_lt_one_of_mem_hline {α : ℝ} {c z : ℂ} (h : z ∈ hline α c) : ‖z‖ < 1 := h.1

/-! ### Corollary 10.18: the h-line through two points -/

/-- Parameters of the circline through `p` and `q` (the cross product of the coefficient vectors). -/
def lα (p q : ℂ) : ℝ := 4 * (p.re * q.im - p.im * q.re)

/-- See `lα`. -/
def lc (p q : ℂ) : ℂ :=
  ⟨2 * ((p.re ^ 2 + p.im ^ 2 + 1) * q.im - (q.re ^ 2 + q.im ^ 2 + 1) * p.im),
    2 * ((q.re ^ 2 + q.im ^ 2 + 1) * p.re - (p.re ^ 2 + p.im ^ 2 + 1) * q.re)⟩

theorem hE_lineParam_left (p q : ℂ) : hE (lα p q) (lc p q) p = 0 := by
  rw [hE_coord]; simp only [lα, lc]; ring

theorem hE_lineParam_right (p q : ℂ) : hE (lα p q) (lc p q) q = 0 := by
  rw [hE_coord]; simp only [lα, lc]; ring

theorem lineParam_disc (p q : ℂ) :
    ‖lc p q‖ ^ 2 - lα p q ^ 2 =
      4 * ‖p - q‖ ^ 2 * ((1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2) + ‖p - q‖ ^ 2) := by
  simp only [sq_norm_eq, lα, lc, Complex.sub_re, Complex.sub_im]
  ring

theorem lineParam_lt {p q : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) (hpq : p ≠ q) :
    lα p q ^ 2 < ‖lc p q‖ ^ 2 := by
  have h1 := mul_pos (one_sub_sq_pos hp) (one_sub_sq_pos hq)
  have h2 : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  have := lineParam_disc p q
  have h3 : 0 < 4 * ‖p - q‖ ^ 2 * ((1 - ‖p‖ ^ 2) * (1 - ‖q‖ ^ 2) + ‖p - q‖ ^ 2) := by positivity
  linarith

theorem hline_eq_of_minors {α α' : ℝ} {c c' : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hc' : c' ≠ 0)
    (m1 : α * c'.re = α' * c.re) (m2 : α * c'.im = α' * c.im) (m3 : c.re * c'.im = c.im * c'.re) :
    hline α' c' = hline α c := by
  have hN : 0 < c.re ^ 2 + c.im ^ 2 := by rw [← sq_norm_eq]; nlinarith [sq_nonneg α]
  set μ := (c.re * c'.re + c.im * c'.im) / (c.re ^ 2 + c.im ^ 2) with hμ
  have hc1 : c'.re = μ * c.re := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (-c.im) * m3
  have hc2 : c'.im = μ * c.im := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination c.re * m3
  have hα : α' = μ * α := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
    linear_combination (-c.re) * m1 - c.im * m2
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc1 hc2
    exact hc' (Complex.ext (by simpa using hc1) (by simpa using hc2))
  exact hline_eq_of_proportional hμ0 hc1 hc2 hα

theorem lineParam_minors {α' : ℝ} {c' p q : ℂ} (hp : hE α' c' p = 0) (hq : hE α' c' q = 0) :
    lα p q * c'.re = α' * (lc p q).re ∧ lα p q * c'.im = α' * (lc p q).im ∧
      (lc p q).re * c'.im = (lc p q).im * c'.re := by
  rw [hE_coord] at hp hq
  refine ⟨?_, ?_, ?_⟩
  · simp only [lα, lc]
    linear_combination (2 * p.im) * hq - (2 * q.im) * hp
  · simp only [lα, lc]
    linear_combination (-2 * p.re) * hq + (2 * q.re) * hp
  · simp only [lα, lc]
    linear_combination (-(p.re ^ 2 + p.im ^ 2 + 1)) * hq + (q.re ^ 2 + q.im ^ 2 + 1) * hp

/-- Corollary 10.18 (in the disc model, all cases including lines through the centre): two
distinct points of the open unit disc lie on an h-line `hline α c` (`α² < ‖c‖²`), and the h-line
is unique: any other such h-line through both points is the same set. -/
@[kb "petrunin2025" "Corollary 10.18, p. 80"]
theorem exists_unique_hline {p q : ℂ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) (hpq : p ≠ q) :
    ∃ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 ∧ p ∈ hline α c ∧ q ∈ hline α c ∧
      ∀ (α' : ℝ) (c' : ℂ), α' ^ 2 < ‖c'‖ ^ 2 → p ∈ hline α' c' → q ∈ hline α' c' →
        hline α' c' = hline α c := by
  refine ⟨lα p q, lc p q, lineParam_lt hp hq hpq, mem_hline_iff.mpr ⟨hp, hE_lineParam_left p q⟩,
    mem_hline_iff.mpr ⟨hq, hE_lineParam_right p q⟩, ?_⟩
  intro α' c' hd hp' hq'
  have hc' : c' ≠ 0 := by
    rintro rfl
    simp at hd
    nlinarith [sq_nonneg α']
  obtain ⟨m1, m2, m3⟩ := lineParam_minors (mem_hline_iff.mp hp').2 (mem_hline_iff.mp hq').2
  exact hline_eq_of_minors (lineParam_lt hp hq hpq) hc' m1 m2 m3

/-! ### Möbius maps and rotations send h-lines to h-lines -/

/-- The new `α` for the h-line `hline α c` pulled back along `mobius b`. -/
noncomputable def mα (b : ℂ) (α : ℝ) (c : ℂ) : ℝ := α * (1 + ‖b‖ ^ 2) + 2 * (conj c * b).re

/-- The new `c` for the h-line `hline α c` pulled back along `mobius b`. -/
noncomputable def mc (b : ℂ) (α : ℝ) (c : ℂ) : ℂ := c + conj c * (b * b) + 2 * (α : ℂ) * b

theorem mobius_hE_poly (α : ℝ) (c b w : ℂ) :
    α * (‖w - b‖ ^ 2 + ‖1 - conj b * w‖ ^ 2) -
        2 * (conj c * ((w - b) * conj (1 - conj b * w))).re = hE (mα b α c) (mc b α c) w := by
  simp only [hE_coord, sq_norm_eq]
  simp only [mα, mc, sq_norm_eq, re_conj_mul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem hE_mobius {α : ℝ} {c b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    hE α c (mobius b w) * ‖1 - conj b * w‖ ^ 2 = hE (mα b α c) (mc b α c) w := by
  have hD := mobius_den_ne hb hw
  set D := 1 - conj b * w with hDdef
  have hz : mobius b w * D = w - b := by unfold mobius; exact div_mul_cancel₀ _ hD
  rw [← mobius_hE_poly]
  have hn : ‖mobius b w‖ ^ 2 * ‖D‖ ^ 2 = ‖w - b‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, hz]
  have e : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : (conj c * mobius b w).re * ‖D‖ ^ 2 = (conj c * ((w - b) * conj D)).re := by
    have : conj c * ((w - b) * conj D) = (conj c * mobius b w) * ((‖D‖ ^ 2 : ℝ) : ℂ) := by
      rw [e, ← hz]; ring
    rw [this, Complex.re_mul_ofReal]
  unfold hE
  linear_combination α * hn - 2 * hre

theorem mc_disc (b : ℂ) (α : ℝ) (c : ℂ) :
    ‖mc b α c‖ ^ 2 - mα b α c ^ 2 = (1 - ‖b‖ ^ 2) ^ 2 * (‖c‖ ^ 2 - α ^ 2) := by
  simp only [sq_norm_eq]
  simp only [mα, mc, sq_norm_eq, re_conj_mul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

theorem mα_lt {b : ℂ} {α : ℝ} {c : ℂ} (hb : ‖b‖ < 1) (h : α ^ 2 < ‖c‖ ^ 2) :
    mα b α c ^ 2 < ‖mc b α c‖ ^ 2 := by
  have h1 := mc_disc b α c
  have h2 : 0 < (1 - ‖b‖ ^ 2) ^ 2 := by have := one_sub_sq_pos hb; positivity
  nlinarith [mul_pos h2 (sub_pos.mpr h)]

theorem mobius_mem_hline_iff {α : ℝ} {c b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    mobius b w ∈ hline α c ↔ w ∈ hline (mα b α c) (mc b α c) := by
  have h := hE_mobius (α := α) (c := c) hb hw
  have hD := norm_den_pos hb hw
  rw [mem_hline_iff, mem_hline_iff]
  constructor
  · rintro ⟨_, h0⟩; exact ⟨hw, by rw [← h, h0, zero_mul]⟩
  · rintro ⟨_, h0⟩
    refine ⟨norm_mobius_lt_one hb hw, ?_⟩
    rw [← h] at h0
    exact (mul_eq_zero.mp h0).resolve_right (by positivity)

theorem mobius_mobius_neg' {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    mobius a (mobius (-a) w) = w := by
  have han : ‖-a‖ < 1 := by simpa using ha
  simpa using mobius_neg_mobius han hw

/-- The image of an h-line under the h-motion `mobius a` is an h-line. -/
theorem mobius_image_hline {α : ℝ} {c a : ℂ} (ha : ‖a‖ < 1) :
    mobius a '' hline α c = hline (mα (-a) α c) (mc (-a) α c) := by
  have han : ‖-a‖ < 1 := by simpa using ha
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz1 := hz.1
    exact (mobius_mem_hline_iff (α := α) (c := c) han (norm_mobius_lt_one ha hz1)).mp
      (by rwa [mobius_neg_mobius ha hz1])
  · intro hw
    have hw1 := hw.1
    exact ⟨mobius (-a) w, (mobius_mem_hline_iff han hw1).mpr hw, mobius_mobius_neg' ha hw1⟩

theorem hE_rot {u : ℂ} (hu : ‖u‖ = 1) (α : ℝ) (c z : ℂ) :
    hE α c (u * z) = hE α (c * conj u) z := by
  unfold hE
  rw [norm_mul, hu, one_mul, map_mul, Complex.conj_conj, mul_assoc]

theorem rot_mem_hline_iff {u : ℂ} (hu : ‖u‖ = 1) {α : ℝ} {c z : ℂ} :
    u * z ∈ hline α c ↔ z ∈ hline α (c * conj u) := by
  rw [mem_hline_iff, mem_hline_iff, hE_rot hu, norm_mul, hu, one_mul]

theorem conj_mul_self_unit {u : ℂ} (hu : ‖u‖ = 1) : conj u * u = 1 := by
  rw [Complex.conj_mul', hu]; simp

/-! ### Moving an h-line to the real diameter -/

theorem exists_mem_hline {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) : ∃ a, a ∈ hline α c := by
  by_cases hα : α = 0
  · exact ⟨0, mem_hline_iff.mpr ⟨by simp, by simp [hE, hα]⟩⟩
  · set C := ‖c‖ with hC
    have hC0 : 0 < C := by
      have h0 : 0 ≤ C := norm_nonneg c
      rcases h0.lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1] at h; nlinarith [sq_nonneg α]
    have hα2 : 0 < α ^ 2 := by positivity
    set s := Real.sqrt (C ^ 2 - α ^ 2) with hs
    have hs2 : s ^ 2 = C ^ 2 - α ^ 2 := Real.sq_sqrt (by linarith)
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have hsC : s < C := by
      by_contra hh
      push Not at hh
      nlinarith
    set r := (C - s) / α with hr
    have key : α * (r ^ 2 + 1) - 2 * r * C = 0 := by
      rw [hr]; field_simp; linear_combination hs2
    have hr2 : r ^ 2 < 1 := by
      rw [hr, div_pow, div_lt_one hα2]; nlinarith
    have hCsq : C ^ 2 = c.re ^ 2 + c.im ^ 2 := sq_norm_eq c
    have hre : (((r / C : ℝ) : ℂ) * c).re = r / C * c.re := by simp
    have him : (((r / C : ℝ) : ℂ) * c).im = r / C * c.im := by simp
    have hn2 : ‖((r / C : ℝ) : ℂ) * c‖ ^ 2 = r ^ 2 := by
      rw [sq_norm_eq, hre, him]
      have : (r / C * c.re) ^ 2 + (r / C * c.im) ^ 2 = (r / C) ^ 2 * (c.re ^ 2 + c.im ^ 2) := by ring
      rw [this, ← hCsq]; field_simp
    refine ⟨((r / C : ℝ) : ℂ) * c, mem_hline_iff.mpr ⟨?_, ?_⟩⟩
    · nlinarith [norm_nonneg (((r / C : ℝ) : ℂ) * c)]
    · rw [hE_coord, hre, him]
      have : α * ((r / C * c.re) ^ 2 + (r / C * c.im) ^ 2 + 1) -
          2 * (c.re * (r / C * c.re) + c.im * (r / C * c.im)) =
          α * ((r / C) ^ 2 * (c.re ^ 2 + c.im ^ 2) + 1) - 2 * (r / C) * (c.re ^ 2 + c.im ^ 2) := by
        ring
      rw [this, ← hCsq]
      have e : (r / C) ^ 2 * C ^ 2 = r ^ 2 := by field_simp
      rw [e]
      have e2 : 2 * (r / C) * C ^ 2 = 2 * r * C := by field_simp
      rw [e2]
      exact key

theorem exists_motion {α : ℝ} {c a : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (ha : a ∈ hline α c) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z : ℂ, ‖z‖ < 1 →
      (z ∈ hline α c ↔ u * mobius a z ∈ hline 0 Complex.I) := by
  have ha1 := ha.1
  have han : ‖-a‖ < 1 := by simpa using ha1
  have hd := mα_lt han h
  have h0 : mα (-a) α c = 0 := by
    have := Set.mem_image_of_mem (mobius a) ha
    rw [mobius_image_hline ha1, mobius_self ha1] at this
    have h2 := (mem_hline_iff.mp this).2
    rw [hE_coord] at h2
    simpa using h2
  rw [h0] at hd
  set c₂ := mc (-a) α c with hc₂
  have hr : 0 < ‖c₂‖ := by
    by_contra hh
    have : ‖c₂‖ = 0 := le_antisymm (not_lt.mp hh) (norm_nonneg _)
    rw [this] at hd; norm_num at hd
  set r := ‖c₂‖ with hrdef
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcc : c₂ ≠ 0 := by
    intro h0'; rw [h0'] at hrdef; simp at hrdef; rw [hrdef] at hr; exact lt_irrefl _ hr
  refine ⟨Complex.I * conj c₂ / (r : ℂ), ?_, ?_⟩
  · rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg hr.le, one_mul, div_self hr.ne']
  · intro z hz
    have hu : ‖Complex.I * conj c₂ / (r : ℂ)‖ = 1 := by
      rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg hr.le, one_mul, div_self hr.ne']
    have hz' := norm_mobius_lt_one ha1 hz
    have e1 : z ∈ hline α c ↔ mobius a z ∈ hline (mα (-a) α c) c₂ := by
      have := mobius_mem_hline_iff (α := α) (c := c) han hz'
      rw [mobius_neg_mobius ha1 hz] at this
      exact this
    rw [e1, h0, rot_mem_hline_iff hu]
    have e2 : Complex.I * conj (Complex.I * conj c₂ / (r : ℂ)) = c₂ / (r : ℂ) := by
      simp only [map_div₀, map_mul, Complex.conj_conj, Complex.conj_I, Complex.conj_ofReal]
      field_simp
      simp
    rw [e2]
    have : hline 0 (c₂ / (r : ℂ)) = hline 0 c₂ := by
      refine hline_eq_of_proportional (μ := 1 / r) (by positivity) ?_ ?_ (by simp)
      · simp [Complex.div_ofReal_re]; field_simp
      · simp [Complex.div_ofReal_im]; field_simp
    rw [this]

/-! ### Isometric parametrisation of an h-line (Claim 12.15, first half) -/

theorem hcosh_rot {v : ℂ} (hv : ‖v‖ = 1) (z w : ℂ) : hcosh (v * z) (v * w) = hcosh z w := by
  unfold hcosh
  rw [← mul_sub, norm_mul, norm_mul, norm_mul, hv]; simp

theorem hdist_rot {v : ℂ} (hv : ‖v‖ = 1) (z w : ℂ) : hdist (v * z) (v * w) = hdist z w := by
  unfold hdist; rw [hcosh_rot hv]

theorem mem_hline_zero_I {x : ℂ} : x ∈ hline 0 Complex.I ↔ ‖x‖ < 1 ∧ x.im = 0 := by
  rw [mem_hline_iff, hE_coord]
  simp

theorem hcoord_tanh (t : ℝ) : hcoord (Real.tanh (t / 2)) = t := by
  unfold hcoord
  rw [tanh_half_eq]
  have hp : 0 < Real.exp t + 1 := by positivity
  have e : (1 + (Real.exp t - 1) / (Real.exp t + 1)) / (1 - (Real.exp t - 1) / (Real.exp t + 1))
      = Real.exp t := by
    field_simp; ring
  rw [e, Real.log_exp]

theorem tanh_half_le_iff (s t : ℝ) : Real.tanh (s / 2) ≤ Real.tanh (t / 2) ↔ s ≤ t := by
  have h1 : ∀ x : ℝ, Real.tanh x ∈ Set.Ioo (-1 : ℝ) 1 :=
    fun x => ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  rw [← Real.artanh_le_artanh_iff (h1 _) (h1 _), Real.artanh_tanh, Real.artanh_tanh]
  constructor <;> intro h <;> linarith

theorem norm_tanh_lt (t : ℝ) : ‖((Real.tanh (t / 2) : ℝ) : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

theorem hdist_tanh (s t : ℝ) :
    hdist ((Real.tanh (s / 2) : ℝ) : ℂ) ((Real.tanh (t / 2) : ℝ) : ℂ) = |s - t| := by
  have key : ∀ s t : ℝ, s ≤ t →
      hdist ((Real.tanh (s / 2) : ℝ) : ℂ) ((Real.tanh (t / 2) : ℝ) : ℂ) = t - s := by
    intro s t hst
    rw [hdist_ofReal_of_le (Real.neg_one_lt_tanh _) (Real.tanh_lt_one _)
      ((tanh_half_le_iff s t).mpr hst), hcoord_tanh, hcoord_tanh]
  rcases le_total s t with h | h
  · rw [key s t h, abs_sub_comm, abs_of_nonneg (by linarith)]
  · rw [hdist_comm, key t s h, abs_of_nonneg (by linarith)]

/-- The standard parametrisation of the h-line obtained from the diameter by an h-motion. -/
noncomputable def hpar (a u : ℂ) (t : ℝ) : ℂ :=
  mobius (-a) (conj u * ((Real.tanh (t / 2) : ℝ) : ℂ))

theorem norm_conj_mul_tanh {u : ℂ} (hu : ‖u‖ = 1) (t : ℝ) :
    ‖conj u * ((Real.tanh (t / 2) : ℝ) : ℂ)‖ < 1 := by
  rw [norm_mul, Complex.norm_conj, hu, one_mul]; exact norm_tanh_lt t

theorem hdist_hpar {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (s t : ℝ) :
    hdist (hpar a u s) (hpar a u t) = |s - t| := by
  have han : ‖-a‖ < 1 := by simpa using ha
  unfold hpar
  rw [hdist_mobius han (norm_conj_mul_tanh hu s) (norm_conj_mul_tanh hu t),
    hdist_rot (by rw [Complex.norm_conj, hu]), hdist_tanh]

theorem norm_hpar_lt {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (t : ℝ) : ‖hpar a u t‖ < 1 := by
  have han : ‖-a‖ < 1 := by simpa using ha
  exact norm_mobius_lt_one han (norm_conj_mul_tanh hu t)

theorem range_hpar {α : ℝ} {c a u : ℂ} (ha : a ∈ hline α c) (hu : ‖u‖ = 1)
    (hz : ∀ z : ℂ, ‖z‖ < 1 → (z ∈ hline α c ↔ u * mobius a z ∈ hline 0 Complex.I)) :
    Set.range (hpar a u) = hline α c := by
  have ha1 := ha.1
  have han : ‖-a‖ < 1 := by simpa using ha1
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine (hz _ (norm_hpar_lt ha1 hu t)).mpr ?_
    have : mobius a (hpar a u t) = conj u * ((Real.tanh (t / 2) : ℝ) : ℂ) :=
      mobius_mobius_neg' ha1 (norm_conj_mul_tanh hu t)
    rw [this, ← mul_assoc, show u * conj u = 1 by rw [mul_comm]; exact conj_mul_self_unit hu, one_mul]
    exact mem_hline_zero_I.mpr ⟨norm_tanh_lt t, Complex.ofReal_im _⟩
  · intro hzl
    have hz1 := hzl.1
    have hx := mem_hline_zero_I.mp ((hz z hz1).mp hzl)
    set x := u * mobius a z with hxdef
    have hxr : x = ((x.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hx.2)
    have hxlt : |x.re| < 1 := by
      have := hx.1
      rw [hxr, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    refine ⟨2 * Real.artanh x.re, ?_⟩
    unfold hpar
    have : Real.tanh (2 * Real.artanh x.re / 2) = x.re := by
      rw [mul_div_cancel_left₀ _ (two_ne_zero)]
      exact Real.tanh_artanh (abs_lt.mp hxlt |> fun h => ⟨h.1, h.2⟩)
    rw [this, ← hxr, hxdef, ← mul_assoc, conj_mul_self_unit hu, one_mul]
    have := mobius_neg_mobius ha1 hz1
    simpa using (by simpa using this : mobius (-a) (mobius a z) = z)

/-- Claim 12.15 (first half) for a given h-line: every h-line `hline α c` (`α² < ‖c‖²`) is the
image of a map `f : ℝ → disc` with `hdist (f s) (f t) = |s - t|` (so `f` is an isometric copy of the
real line). -/
@[kb "petrunin2025" "Claim 12.15, p. 99"]
theorem exists_isometric_param {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) :
    ∃ f : ℝ → ℂ, (∀ s t, hdist (f s) (f t) = |s - t|) ∧ Set.range f = hline α c := by
  obtain ⟨a, ha⟩ := exists_mem_hline h
  obtain ⟨u, hu, hz⟩ := exists_motion h ha
  exact ⟨hpar a u, hdist_hpar ha.1 hu, range_hpar ha hu hz⟩

/-! ### H-segments and the equality case of the triangle inequality (Claim 12.14) -/

/-- The h-segment `[PQ]_h`: the image of the Euclidean segment from the centre to `φ_P Q`
(where `φ_P = mobius P` moves `P` to the centre) under the inverse h-motion `mobius (-P)`.  It is
the part of the h-line `PQ` between `P` and `Q` (see `hsegment_subset_hline`). -/
@[kb "petrunin2025" "Exercise 12.3, p. 93"]
noncomputable def hsegment (P Q : ℂ) : Set ℂ := mobius (-P) '' segment ℝ 0 (mobius P Q)

theorem norm_lt_one_of_mem_segment {M s : ℂ} (hM : ‖M‖ < 1) (hs : s ∈ segment ℝ 0 M) : ‖s‖ < 1 := by
  have := (convex_ball (0 : ℂ) 1).segment_subset (by simp) (by simpa using hM) hs
  simpa using this

theorem mem_hsegment_iff {P Q z : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) :
    z ∈ hsegment P Q ↔ ‖z‖ < 1 ∧ mobius P z ∈ segment ℝ 0 (mobius P Q) := by
  have hPn : ‖-P‖ < 1 := by simpa using hP
  have hM := norm_mobius_lt_one hP hQ
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs1 := norm_lt_one_of_mem_segment hM hs
    exact ⟨norm_mobius_lt_one hPn hs1, by rwa [mobius_mobius_neg' hP hs1]⟩
  · rintro ⟨hz, h⟩
    exact ⟨mobius P z, h, mobius_neg_mobius hP hz⟩

theorem hsegment_self {P : ℂ} (hP : ‖P‖ < 1) : hsegment P P = {P} := by
  unfold hsegment
  rw [mobius_self hP]
  simp [mobius]

theorem norm_sub_eq_of_hdist_eq {P Q : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (h : hdist P Q = hdist P 0 + hdist 0 Q) : ‖P - Q‖ = ‖P‖ + ‖Q‖ := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have hP' := one_sub_sq_pos hP
  have hQ' := one_sub_sq_pos hQ
  have hD := mul_pos hP' hQ'
  rw [hdist_comm P 0] at h
  have hc : Real.cosh (hdist P Q) = Real.cosh (hdist 0 P + hdist 0 Q) := by rw [h]
  rw [cosh_hdist hP hQ, Real.cosh_add, cosh_hdist h0 hP, cosh_hdist h0 hQ, hcosh_zero_left hP,
    hcosh_zero_left hQ, sinh_hdist_zero hP, sinh_hdist_zero hQ] at hc
  unfold hcosh at hc
  have e : (1 + ‖P‖ ^ 2) / (1 - ‖P‖ ^ 2) * ((1 + ‖Q‖ ^ 2) / (1 - ‖Q‖ ^ 2)) +
      2 * ‖P‖ / (1 - ‖P‖ ^ 2) * (2 * ‖Q‖ / (1 - ‖Q‖ ^ 2)) -
      (1 + 2 * ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2))) =
      2 * ((‖P‖ + ‖Q‖) ^ 2 - ‖P - Q‖ ^ 2) / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) := by
    field_simp
    ring
  have h3 : 2 * ((‖P‖ + ‖Q‖) ^ 2 - ‖P - Q‖ ^ 2) / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) = 0 := by
    rw [← e]; linarith
  rcases div_eq_zero_iff.mp h3 with h4 | h4
  · have : ‖P - Q‖ ^ 2 = (‖P‖ + ‖Q‖) ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp this
  · exact absurd h4 hD.ne'

theorem mobius_zero_right (a : ℂ) : mobius a 0 = -a := by simp [mobius]

/-- Equality case of the triangle inequality, centred form: `OR_h = OQ_h + QR_h` iff `Q` lies on
the Euclidean segment `[OR]` (which is the h-segment `[OR]_h`). -/
theorem hdist_zero_add_iff {Q R : ℂ} (hQ : ‖Q‖ < 1) (hR : ‖R‖ < 1) :
    hdist 0 R = hdist 0 Q + hdist Q R ↔ Q ∈ segment ℝ 0 R := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  constructor
  · intro h
    have hX : ‖mobius Q 0‖ < 1 := norm_mobius_lt_one hQ h0
    have hY : ‖mobius Q R‖ < 1 := norm_mobius_lt_one hQ hR
    have e1 : hdist (mobius Q 0) (mobius Q R) = hdist 0 R := hdist_mobius hQ h0 hR
    have e2 : hdist (mobius Q 0) 0 = hdist 0 Q := by
      have := hdist_mobius hQ h0 hQ
      rwa [mobius_self hQ] at this
    have e3 : hdist 0 (mobius Q R) = hdist Q R := by
      have := hdist_mobius hQ hQ hR
      rwa [mobius_self hQ] at this
    have h1 : hdist (mobius Q 0) (mobius Q R) = hdist (mobius Q 0) 0 + hdist 0 (mobius Q R) := by
      rw [e1, e2, e3]; exact h
    have h2 := norm_sub_eq_of_hdist_eq hX hY h1
    rw [mobius_zero_right] at h2 hX
    have h3 : SameRay ℝ (-Q) (-mobius Q R) := by
      rw [sameRay_iff_norm_add]
      rw [norm_neg (mobius Q R), ← sub_eq_add_neg]
      exact h2
    rw [sameRay_neg_iff] at h3
    have hD := mobius_den_ne hQ hR
    rcases h3 with h3 | h3 | ⟨r1, r2, hr1, hr2, h3⟩
    · rw [h3]; exact left_mem_segment ℝ 0 R
    · have : R - Q = 0 := by
        have h4 : mobius Q R = 0 := h3
        unfold mobius at h4
        exact (div_eq_zero_iff.mp h4).resolve_right hD
      have : Q = R := (sub_eq_zero.mp this).symm
      rw [this]; exact right_mem_segment ℝ 0 R
    · set s : ℝ := r1 / r2 with hs
      have hs0 : 0 < s := div_pos hr1 hr2
      have hY' : mobius Q R = (s : ℂ) * Q := by
        rw [hs]
        rw [Complex.real_smul, Complex.real_smul] at h3
        have : (r2 : ℂ) ≠ 0 := by exact_mod_cast hr2.ne'
        push_cast
        field_simp
        linear_combination -h3
      have hRQ : R - Q = (s : ℂ) * Q * (1 - conj Q * R) := by
        rw [← hY']; unfold mobius; rw [div_mul_cancel₀ _ hD]
      have hQQ : (‖Q‖ : ℂ) ^ 2 = Q * conj Q := by
        have := Complex.mul_conj Q
        rw [Complex.normSq_eq_norm_sq] at this
        push_cast at this
        exact this.symm
      have hrel : (1 + (s : ℂ) * (‖Q‖ : ℂ) ^ 2) * R = Q * (1 + (s : ℂ)) := by
        rw [hQQ]; linear_combination hRQ
      have hs1 : (1 + (s : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (1 + s) ≠ 0)
      have hQn2 : ‖Q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Q]
      rw [segment_eq_image']
      refine ⟨(1 + s * ‖Q‖ ^ 2) / (1 + s), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; nlinarith
      · simp only [zero_add, sub_zero, Complex.real_smul]
        push_cast
        rw [div_mul_eq_mul_div, div_eq_iff hs1]
        linear_combination hrel
  · intro hseg
    rw [segment_eq_image'] at hseg
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := hseg
    by_cases hR0 : R = 0
    · subst hR0
      simp at hθ
      subst hθ
      simp [hdist_eq_zero_iff h0 h0]
    · have hRn : 0 < ‖R‖ := norm_pos_iff.mpr hR0
      have hRn' : ((‖R‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hRn.ne'
      set z : ℝ := ‖R‖ with hzdef
      set v : ℂ := (z : ℂ)⁻¹ * R with hv
      have hvn : ‖v‖ = 1 := by
        rw [hv, norm_mul, norm_inv, Complex.norm_real, hzdef, norm_norm, inv_mul_cancel₀ hRn.ne']
      have hRv : v * (z : ℂ) = R := by
        rw [hv]; field_simp
      have hQv : v * ((θ * z : ℝ) : ℂ) = Q := by
        rw [← hθ]; simp only [zero_add, sub_zero, Complex.real_smul]
        push_cast
        rw [← hRv]; ring
      have key := hdist_add_ofReal (x := 0) (y := θ * z) (z := z) (by norm_num) hR
        (by positivity) (by nlinarith)
      have e0 : hdist 0 R = hdist ((0 : ℝ) : ℂ) (z : ℂ) := by
        have := hdist_rot hvn ((0 : ℝ) : ℂ) (z : ℂ)
        rw [Complex.ofReal_zero, mul_zero, hRv] at this
        simpa using this
      have e1 : hdist 0 Q = hdist ((0 : ℝ) : ℂ) ((θ * z : ℝ) : ℂ) := by
        have := hdist_rot hvn ((0 : ℝ) : ℂ) ((θ * z : ℝ) : ℂ)
        rw [Complex.ofReal_zero, mul_zero, hQv] at this
        simpa using this
      have e2 : hdist Q R = hdist ((θ * z : ℝ) : ℂ) (z : ℂ) := by
        have := hdist_rot hvn ((θ * z : ℝ) : ℂ) (z : ℂ)
        rw [hQv, hRv] at this
        exact this
      rw [e0, e1, e2]
      exact key.symm

/-- Claim 12.14 (equality case): for points `P, Q, R` of the disc, `PR_h = PQ_h + QR_h` iff `Q`
lies on the h-segment `[PR]_h`, i.e. `P, Q, R` lie in this order on an h-line.  (The inequality
is `hdist_triangle`.) -/
@[kb "petrunin2025" "Claim 12.14, p. 98"]
theorem hdist_add_iff_mem_hsegment {P Q R : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (hR : ‖R‖ < 1) :
    hdist P R = hdist P Q + hdist Q R ↔ Q ∈ hsegment P R := by
  have hQ' := norm_mobius_lt_one hP hQ
  have hR' := norm_mobius_lt_one hP hR
  rw [mem_hsegment_iff hP hR, ← hdist_zero_add_iff hQ' hR']
  have e1 : hdist 0 (mobius P R) = hdist P R := by
    have := hdist_mobius hP hP hR; rwa [mobius_self hP] at this
  have e2 : hdist 0 (mobius P Q) = hdist P Q := by
    have := hdist_mobius hP hP hQ; rwa [mobius_self hP] at this
  have e3 : hdist (mobius P Q) (mobius P R) = hdist Q R := hdist_mobius hP hQ hR
  rw [e1, e2, e3]
  exact ⟨fun h => ⟨hQ, h⟩, fun h => h.2⟩

theorem hline_eq_of_two_pts {α α' : ℝ} {c c' P R : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (h' : α' ^ 2 < ‖c'‖ ^ 2) (hPR : P ≠ R) (hP : P ∈ hline α c) (hR : R ∈ hline α c)
    (hP' : P ∈ hline α' c') (hR' : R ∈ hline α' c') : hline α c = hline α' c' := by
  obtain ⟨a0, c0, _, _, _, hu⟩ := exists_unique_hline hP.1 hR.1 hPR
  rw [hu α c h hP hR, hu α' c' h' hP' hR']

theorem hsegment_subset_hline {α : ℝ} {c P R : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : P ∈ hline α c)
    (hR : R ∈ hline α c) : hsegment P R ⊆ hline α c := by
  have hP1 := hP.1
  have hR1 := hR.1
  by_cases hPR : P = R
  · subst hPR
    rw [hsegment_self hP1]
    simpa using hP
  have hM1 := norm_mobius_lt_one hP1 hR1
  have hM0 : mobius P R ≠ 0 := by
    intro h0
    unfold mobius at h0
    have : R - P = 0 := (div_eq_zero_iff.mp h0).resolve_right (mobius_den_ne hP1 hR1)
    exact hPR (sub_eq_zero.mp this).symm
  set M := mobius P R with hMdef
  set c0 : ℂ := -Complex.I * M with hc0def
  have hc0 : ‖c0‖ = ‖M‖ := by rw [hc0def, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hMpos : 0 < ‖M‖ := norm_pos_iff.mpr hM0
  have hd0 : (0 : ℝ) ^ 2 < ‖c0‖ ^ 2 := by
    rw [hc0, zero_pow two_ne_zero]; positivity
  have hseg0 : segment ℝ 0 M ⊆ hline 0 c0 := by
    intro z hz
    refine mem_hline_iff.mpr ⟨norm_lt_one_of_mem_segment hM1 hz, ?_⟩
    rw [segment_eq_image'] at hz
    obtain ⟨θ, _, rfl⟩ := hz
    rw [hE_coord]
    simp [c0]
    ring
  have hPn : ‖-P‖ < 1 := by simpa using hP1
  have himg : mobius (-P) '' hline 0 c0 = hline (mα P 0 c0) (mc P 0 c0) := by
    have := mobius_image_hline (α := 0) (c := c0) hPn
    rwa [neg_neg] at this
  have hdL : mα P 0 c0 ^ 2 < ‖mc P 0 c0‖ ^ 2 := mα_lt hP1 hd0
  have hsub : hsegment P R ⊆ hline (mα P 0 c0) (mc P 0 c0) := by
    rw [← himg]; exact Set.image_mono hseg0
  have hPL : P ∈ hline (mα P 0 c0) (mc P 0 c0) := by
    rw [← himg]
    refine ⟨0, hseg0 (left_mem_segment ℝ 0 M), ?_⟩
    rw [mobius_zero_right, neg_neg]
  have hRL : R ∈ hline (mα P 0 c0) (mc P 0 c0) := by
    rw [← himg]
    exact ⟨M, hseg0 (right_mem_segment ℝ 0 M), mobius_neg_mobius hP1 hR1⟩
  rw [hline_eq_of_two_pts h hdL hPR hP hR hPL hRL]
  exact hsub

/-- Lemma 12.9 (additivity of the h-distance along an arbitrary h-line): if `P, R` lie on the
h-line `hline α c` and `Q` lies on the h-segment `[PR]_h` (so `P, Q, R` are in this order on the
h-line), then `Q` is on the h-line and `PQ_h + QR_h = PR_h`.  (Wave 1 has the diameter case
`hdist_add_ofReal`.) -/
@[kb "petrunin2025" "Lemma 12.9, p. 95"]
theorem hdist_add_of_mem_hsegment {α : ℝ} {c P Q R : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (hP : P ∈ hline α c) (hR : R ∈ hline α c) (hQ : Q ∈ hsegment P R) :
    Q ∈ hline α c ∧ hdist P Q + hdist Q R = hdist P R := by
  have hQL := hsegment_subset_hline h hP hR hQ
  exact ⟨hQL, ((hdist_add_iff_mem_hsegment hP.1 hQL.1 hR.1).mpr hQ).symm⟩

theorem mem_hline_of_mem_hsegment {α : ℝ} {c A B C : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (hA : A ∈ hline α c) (hB : B ∈ hline α c) (hAB : A ≠ B) (hC : ‖C‖ < 1)
    (hbet : B ∈ hsegment A C) : C ∈ hline α c := by
  have hAC : A ≠ C := by
    rintro rfl
    rw [hsegment_self hA.1] at hbet
    exact hAB (Set.mem_singleton_iff.mp hbet).symm
  obtain ⟨α₀, c₀, hd₀, hA₀, hC₀, -⟩ := exists_unique_hline hA.1 hC hAC
  have hB₀ : B ∈ hline α₀ c₀ := hsegment_subset_hline hd₀ hA₀ hC₀ hbet
  rw [hline_eq_of_two_pts h hd₀ hAB hA hB hA₀ hB₀]
  exact hC₀

/-! ### Axiom II (Claim 12.15, converse half) -/

theorem real_isometry_surjective (φ : ℝ → ℝ) (h : ∀ s t, |φ s - φ t| = |s - t|) :
    Function.Surjective φ := by
  have hsq : ∀ s t, (φ s - φ t) ^ 2 = (s - t) ^ 2 := fun s t => by
    have := congrArg (fun x => x ^ 2) (h s t)
    simpa [sq_abs] using this
  intro τ
  refine ⟨(φ 1 - φ 0) * (τ - φ 0), ?_⟩
  set t := (φ 1 - φ 0) * (τ - φ 0) with ht
  have h1 := hsq t 0
  have h2 := hsq t 1
  have h3 := hsq 1 0
  have k : (φ 1 - φ 0) * (φ t - φ 0) = t := by
    linear_combination (1 / 2) * h1 + (1 / 2) * h3 - (1 / 2) * h2
  have k2 : (φ 1 - φ 0) ^ 2 = 1 := by linear_combination h3
  have : φ t - φ 0 = (φ 1 - φ 0) * t := by
    linear_combination (φ 1 - φ 0) * k - (φ t - φ 0) * k2
  have e2 : (φ 1 - φ 0) * t = τ - φ 0 := by
    rw [ht]; linear_combination (τ - φ 0) * k2
  linarith [this, e2]

/-- Claim 12.15 (converse): the image of any isometric copy of the real line in the h-plane is an
h-line.  Here `f : ℝ → ℂ` takes values in the disc and satisfies `hdist (f s) (f t) = |s - t|`.
Together with `exists_isometric_param` this says that the h-lines are exactly the lines of the
h-metric (Axiom II). -/
@[kb "petrunin2025" "Claim 12.15, p. 99"]
theorem exists_hline_of_isometric {f : ℝ → ℂ} (hf1 : ∀ t, ‖f t‖ < 1)
    (hf : ∀ s t, hdist (f s) (f t) = |s - t|) :
    ∃ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 ∧ Set.range f = hline α c := by
  have hne : f 0 ≠ f 1 := by
    intro h
    have := hf 0 1
    rw [h, (hdist_eq_zero_iff (hf1 1) (hf1 1)).mpr rfl] at this
    norm_num at this
  obtain ⟨α, c, hd, hP, hQ, -⟩ := exists_unique_hline (hf1 0) (hf1 1) hne
  refine ⟨α, c, hd, ?_⟩
  obtain ⟨g, hg, hrange⟩ := exists_isometric_param hd
  have betw : ∀ a b d : ℝ, ((a ≤ b ∧ b ≤ d) ∨ (d ≤ b ∧ b ≤ a)) →
      f b ∈ hsegment (f a) (f d) := by
    intro a b d hb
    refine (hdist_add_iff_mem_hsegment (hf1 a) (hf1 b) (hf1 d)).mp ?_
    rw [hf, hf, hf]
    rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring
  have hmem : ∀ t, f t ∈ hline α c := by
    intro t
    rcases lt_trichotomy t 0 with h0 | h0 | h0
    · exact mem_hline_of_mem_hsegment hd hQ hP hne.symm (hf1 t) (betw 1 0 t (Or.inr ⟨h0.le, by norm_num⟩))
    · rw [h0]; exact hP
    · rcases lt_trichotomy t 1 with h1 | h1 | h1
      · exact hsegment_subset_hline hd hP hQ (betw 0 t 1 (Or.inl ⟨h0.le, h1.le⟩))
      · rw [h1]; exact hQ
      · exact mem_hline_of_mem_hsegment hd hP hQ hne (hf1 t) (betw 0 1 t (Or.inl ⟨by norm_num, h1.le⟩))
  choose φ hφ using fun t => (hrange ▸ hmem t : f t ∈ Set.range g)
  have hiso : ∀ s t, |φ s - φ t| = |s - t| := by
    intro s t; rw [← hg, hφ, hφ, hf]
  have hsurj := real_isometry_surjective φ hiso
  ext z
  rw [← hrange]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨φ t, hφ t⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨t, rfl⟩ := hsurj x
    exact ⟨t, (hφ t).symm⟩

/-! ### Axiom h-V for an arbitrary h-line (Claim 12.20) -/

theorem c_eq_of_hline_one_eq {c c' : ℂ} (h : 1 ^ 2 < ‖c‖ ^ 2)
    (heq : hline 1 c = hline 1 c') : c = c' := by
  obtain ⟨f, hf, hr⟩ := exists_isometric_param h
  have hp : f 0 ∈ hline 1 c := by rw [← hr]; exact ⟨0, rfl⟩
  have hq : f 1 ∈ hline 1 c := by rw [← hr]; exact ⟨1, rfl⟩
  have hp' : f 0 ∈ hline 1 c' := heq ▸ hp
  have hq' : f 1 ∈ hline 1 c' := heq ▸ hq
  have hne : f 0 ≠ f 1 := by
    intro h0
    have := hf 0 1
    rw [h0, (hdist_eq_zero_iff hq.1 hq.1).mpr rfl] at this
    norm_num at this
  obtain ⟨a1, a2, -⟩ := lineParam_minors (mem_hline_iff.mp hp).2 (mem_hline_iff.mp hq).2
  obtain ⟨b1, b2, -⟩ := lineParam_minors (mem_hline_iff.mp hp').2 (mem_hline_iff.mp hq').2
  have hlt := lineParam_lt hp.1 hq.1 hne
  have hα : lα (f 0) (f 1) ≠ 0 := by
    intro h0
    rw [h0] at a1 a2 hlt
    have e1 : (lc (f 0) (f 1)).re = 0 := by linarith
    have e2 : (lc (f 0) (f 1)).im = 0 := by linarith
    have : lc (f 0) (f 1) = 0 := Complex.ext e1 e2
    rw [this] at hlt
    norm_num at hlt
  apply Complex.ext
  · exact mul_left_cancel₀ hα (by linarith)
  · exact mul_left_cancel₀ hα (by linarith)

/-- Claim 12.20 (general form of axiom h-V): for any h-line `ℓ = hline α c` and any point `P` of
the disc not on `ℓ`, there are two distinct h-lines through `P` which do not meet `ℓ`.  Proved by
moving `ℓ` to the real diameter with an h-motion and a rotation (`exists_motion`) and applying the
diameter case `hV_exists_two_parallels`. -/
@[kb "petrunin2025" "Claim 12.20, p. 101"]
theorem hV_exists_two_parallels_general {α : ℝ} {c P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPL : P ∉ hline α c) :
    ∃ (α₁ α₂ : ℝ) (c₁ c₂ : ℂ), α₁ ^ 2 < ‖c₁‖ ^ 2 ∧ α₂ ^ 2 < ‖c₂‖ ^ 2 ∧
      P ∈ hline α₁ c₁ ∧ P ∈ hline α₂ c₂ ∧
      Disjoint (hline α₁ c₁) (hline α c) ∧ Disjoint (hline α₂ c₂) (hline α c) ∧
      hline α₁ c₁ ≠ hline α₂ c₂ := by
  obtain ⟨a, ha⟩ := exists_mem_hline h
  obtain ⟨u, hu, hmot⟩ := exists_motion h ha
  have ha1 := ha.1
  have hP' : ‖u * mobius a P‖ < 1 := by
    rw [norm_mul, hu, one_mul]; exact norm_mobius_lt_one ha1 hP
  have hPim : (u * mobius a P).im ≠ 0 := by
    intro him
    exact hPL ((hmot P hP).mpr (mem_hline_zero_I.mpr ⟨hP', him⟩))
  obtain ⟨c₁, c₂, h1, h2, hP1, hP2, hd1, hd2, hne⟩ := hV_exists_two_parallels hP' hPim
  have key : ∀ (γ : ℂ) (z : ℂ), ‖z‖ < 1 →
      (z ∈ hline (mα a 1 (γ * conj u)) (mc a 1 (γ * conj u)) ↔ u * mobius a z ∈ hline 1 γ) := by
    intro γ z hz
    exact ((mobius_mem_hline_iff ha1 hz).symm).trans (rot_mem_hline_iff hu).symm
  have hnorm : ∀ γ : ℂ, ‖γ * conj u‖ = ‖γ‖ := by
    intro γ; rw [norm_mul, Complex.norm_conj, hu, mul_one]
  have hT : ∀ x : ℂ, ‖x‖ < 1 → ∃ z, ‖z‖ < 1 ∧ u * mobius a z = x := by
    intro x hx
    have hx' : ‖conj u * x‖ < 1 := by rw [norm_mul, Complex.norm_conj, hu, one_mul]; exact hx
    have han : ‖-a‖ < 1 := by simpa using ha1
    refine ⟨mobius (-a) (conj u * x), norm_mobius_lt_one han hx', ?_⟩
    rw [mobius_mobius_neg' ha1 hx', ← mul_assoc, mul_comm u, conj_mul_self_unit hu, one_mul]
  have disj : ∀ γ : ℂ, Disjoint (hline 1 γ) (hline 0 Complex.I) →
      Disjoint (hline (mα a 1 (γ * conj u)) (mc a 1 (γ * conj u))) (hline α c) := by
    intro γ hd
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have hzn := hz1.1
    exact Set.disjoint_left.mp hd ((key γ z hzn).mp hz1) ((hmot z hzn).mp hz2)
  refine ⟨mα a 1 (c₁ * conj u), mα a 1 (c₂ * conj u), mc a 1 (c₁ * conj u), mc a 1 (c₂ * conj u),
    mα_lt ha1 (by rw [hnorm]; exact h1), mα_lt ha1 (by rw [hnorm]; exact h2),
    (key c₁ P hP).mpr hP1, (key c₂ P hP).mpr hP2, disj c₁ hd1, disj c₂ hd2, ?_⟩
  intro heq
  have hx : hline 1 c₁ = hline 1 c₂ := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := hT x hx.1
      have := (key c₁ z hz).mpr hx
      rw [heq] at this
      exact (key c₂ z hz).mp this
    · intro hx
      obtain ⟨z, hz, rfl⟩ := hT x hx.1
      have := (key c₂ z hz).mpr hx
      rw [← heq] at this
      exact (key c₁ z hz).mp this
  have hc := c_eq_of_hline_one_eq h1 hx
  exact hne (by rw [hc])

/-! ### Exercise 12.3: when is the h-segment a Euclidean segment? -/

theorem mobius_rot' {u : ℂ} (hu : ‖u‖ = 1) (a z : ℂ) :
    mobius (u * a) (u * z) = u * mobius a z := by
  have h := conj_mul_self_unit hu
  unfold mobius
  rw [map_mul, show 1 - conj u * conj a * (u * z) = 1 - conj a * z by
    linear_combination (-(conj a * z)) * h, ← mul_sub, mul_div_assoc]

theorem mobius_ofReal (p y : ℝ) :
    mobius (p : ℂ) (y : ℂ) = (((y - p) / (1 - p * y) : ℝ) : ℂ) := by
  simp [mobius]

/-- The real Möbius map `y ↦ (y - p)/(1 - p y)` of the diameter. -/
noncomputable def hr (p y : ℝ) : ℝ := (y - p) / (1 - p * y)

theorem one_sub_mul_pos {p y : ℝ} (hp : |p| < 1) (hy : |y| < 1) : 0 < 1 - p * y := by
  rw [abs_lt] at hp hy; nlinarith

theorem hr_self {p : ℝ} : hr p p = 0 := by simp [hr]

theorem hr_lt {p y y' : ℝ} (hp : |p| < 1) (hy : |y| < 1) (hy' : |y'| < 1) (h : y < y') :
    hr p y < hr p y' := by
  have d1 := one_sub_mul_pos hp hy
  have d2 := one_sub_mul_pos hp hy'
  have hp1 := (abs_lt.mp hp)
  unfold hr
  rw [div_lt_div_iff₀ d1 d2]
  nlinarith [mul_pos (sub_pos.mpr h) (by nlinarith : 0 < 1 - p ^ 2)]

theorem hr_le_iff {p y y' : ℝ} (hp : |p| < 1) (hy : |y| < 1) (hy' : |y'| < 1) :
    hr p y ≤ hr p y' ↔ y ≤ y' := by
  constructor
  · intro h
    by_contra hh
    push Not at hh
    exact absurd (hr_lt hp hy' hy hh) (not_lt.mpr h)
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (hr_lt hp hy hy' h).le
    · rw [h]

theorem hr_mem_uIcc {p q x : ℝ} (hp : |p| < 1) (hq : |q| < 1) (hx : |x| < 1) :
    x ∈ Set.uIcc p q ↔ hr p x ∈ Set.uIcc 0 (hr p q) := by
  have i1 := hr_le_iff hp hp hx
  have i2 := hr_le_iff hp hx hq
  have i3 := hr_le_iff hp hp hq
  have i4 := hr_le_iff hp hq hx
  have i5 := hr_le_iff hp hx hp
  have i6 := hr_le_iff hp hq hp
  rw [hr_self] at i1 i3 i5 i6
  simp only [Set.mem_uIcc]
  rw [i1, i2, i4, i5]

theorem mem_segment_zero_rot {u : ℂ} (hu : ‖u‖ = 1) (A B : ℝ) :
    u * (A : ℂ) ∈ segment ℝ 0 (u * (B : ℂ)) ↔ (A : ℝ) ∈ segment ℝ 0 B := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [segment_eq_image', segment_eq_image']
  constructor
  · rintro ⟨θ, hθ, h⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [zero_add, sub_zero, Complex.real_smul] at h ⊢
    have : u * (θ * B : ℂ) = u * A := by rw [← h]; ring
    have := mul_left_cancel₀ hu0 this
    simp only [smul_eq_mul]
    exact_mod_cast this
  · rintro ⟨θ, hθ, h⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [zero_add, sub_zero, Complex.real_smul, smul_eq_mul] at h ⊢
    rw [← h]; push_cast; ring

/-- The h-segment between two points on the diameter `ℝ u` is the part of the diameter between
them, in terms of the real coordinates. -/
theorem mem_hsegment_rot_iff {u : ℂ} (hu : ‖u‖ = 1) {p q x : ℝ} (hp : |p| < 1) (hq : |q| < 1)
    (hx : |x| < 1) :
    u * (x : ℂ) ∈ hsegment (u * (p : ℂ)) (u * (q : ℂ)) ↔ x ∈ Set.uIcc p q := by
  have hn : ∀ y : ℝ, ‖u * (y : ℂ)‖ = |y| := by
    intro y; rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mem_hsegment_iff (by rw [hn]; exact hp) (by rw [hn]; exact hq), mobius_rot' hu,
    mobius_rot' hu, mobius_ofReal, mobius_ofReal, mem_segment_zero_rot hu, segment_eq_uIcc,
    hr_mem_uIcc hp hq hx]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by rw [hn]; exact hx, h⟩

theorem rot_mem_segment_iff {u : ℂ} (hu : ‖u‖ = 1) (p q x : ℝ) :
    u * (x : ℂ) ∈ segment ℝ (u * (p : ℂ)) (u * (q : ℂ)) ↔ x ∈ Set.uIcc p q := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [segment_eq_image', ← segment_eq_uIcc, segment_eq_image']
  constructor
  · rintro ⟨θ, hθ, h⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [Complex.real_smul, smul_eq_mul] at h ⊢
    have : u * ((p + θ * (q - p) : ℝ) : ℂ) = u * x := by push_cast; rw [← h]; ring
    exact_mod_cast mul_left_cancel₀ hu0 this
  · rintro ⟨θ, hθ, h⟩
    refine ⟨θ, hθ, ?_⟩
    simp only [Complex.real_smul, smul_eq_mul] at h ⊢
    rw [← h]; push_cast; ring

theorem hsegment_real_dir {u : ℂ} (hu : ‖u‖ = 1) {p q : ℝ} (hp : |p| < 1) (hq : |q| < 1) :
    hsegment (u * (p : ℂ)) (u * (q : ℂ)) = segment ℝ (u * (p : ℂ)) (u * (q : ℂ)) := by
  have hn : ∀ y : ℝ, ‖u * (y : ℂ)‖ = |y| := by
    intro y; rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hxlt : ∀ x ∈ Set.uIcc p q, |x| < 1 := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rw [abs_lt] at hp hq ⊢
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  ext z
  constructor
  · intro hz
    have hz1 := (mem_hsegment_iff (by rw [hn]; exact hp) (by rw [hn]; exact hq)).mp hz
    obtain ⟨hzn, s, hs, hsz⟩ : ‖z‖ < 1 ∧ ∃ s, s ∈ segment ℝ 0 (mobius (u * p) (u * q)) ∧
        mobius (u * p) z = s := ⟨hz1.1, _, hz1.2, rfl⟩
    rw [mobius_rot' hu, mobius_ofReal] at hs
    rw [segment_eq_image'] at hs
    obtain ⟨θ, hθ, hθs⟩ := hs
    simp only [zero_add, sub_zero, Complex.real_smul] at hθs
    -- z = u * x with x real
    have hzs : z = mobius (-(u * (p : ℂ))) s := by
      rw [← hsz, mobius_neg_mobius (by rw [hn]; exact hp) hzn]
    have hsd : s = u * (((θ * hr p q : ℝ)) : ℂ) := by
      rw [← hθs]; unfold hr; push_cast; ring
    have hs1 : ‖s‖ < 1 := by
      rw [hsz.symm]; exact norm_mobius_lt_one (by rw [hn]; exact hp) hzn
    have hzx : z = u * (((hr (-p) (θ * hr p q) : ℝ)) : ℂ) := by
      rw [hzs, hsd, show -(u * (p : ℂ)) = u * (((-p : ℝ)) : ℂ) by push_cast; ring,
        mobius_rot' hu, mobius_ofReal]
      rfl
    set x := hr (-p) (θ * hr p q) with hx
    have hxl : |x| < 1 := by
      have := hzn; rw [hzx, hn] at this; exact this
    have hmem : x ∈ Set.uIcc p q :=
      (mem_hsegment_rot_iff hu hp hq hxl).mp (by rw [← hzx]; exact hz)
    rw [hzx]
    exact (rot_mem_segment_iff hu p q x).mpr hmem
  · intro hz0
    have hz := hz0
    rw [segment_eq_image'] at hz
    obtain ⟨θ, hθ, hz⟩ := hz
    have hzx : z = u * ((p + θ * (q - p) : ℝ) : ℂ) := by
      rw [← hz]; simp only [Complex.real_smul]; push_cast; ring
    rw [hzx] at hz0
    have hmem := (rot_mem_segment_iff hu p q _).mp hz0
    rw [hzx]
    exact (mem_hsegment_rot_iff hu hp hq (hxlt _ hmem)).mpr hmem

/-- Exercise 12.3: the h-segment `[PQ]_h` coincides with the Euclidean segment `[PQ]` iff the
Euclidean line `PQ` passes through the centre of the absolute (`P ≠ Q`). -/
@[kb "petrunin2025" "Exercise 12.3, p. 93"]
theorem hsegment_eq_segment_iff {P Q : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (hPQ : P ≠ Q) :
    hsegment P Q = segment ℝ P Q ↔ (0 : ℂ) ∈ line[ℝ, P, Q] := by
  constructor
  · intro h
    obtain ⟨α, c, hd, hPL, hQL, -⟩ := exists_unique_hline hP hQ hPQ
    have hsub := hsegment_subset_hline hd hPL hQL
    have hm : (P + (1 / 2 : ℝ) • (Q - P)) ∈ hline α c := by
      apply hsub
      rw [h, segment_eq_image']
      exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    have hE0 := (mem_hline_iff.mp hm).2
    have hEP := (mem_hline_iff.mp hPL).2
    have hEQ := (mem_hline_iff.mp hQL).2
    have hnd : 0 < (Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2 := by
      by_contra hh
      apply hPQ
      have h1 : Q.re - P.re = 0 := by
        nlinarith [sq_nonneg (Q.re - P.re), sq_nonneg (Q.im - P.im)]
      have h2 : Q.im - P.im = 0 := by
        nlinarith [sq_nonneg (Q.re - P.re), sq_nonneg (Q.im - P.im)]
      exact Complex.ext (by linarith) (by linarith)
    rw [hE_coord] at hE0 hEP hEQ
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.sub_re,
      Complex.sub_im, smul_eq_mul] at hE0
    have key : α * ((Q.re - P.re) ^ 2 + (Q.im - P.im) ^ 2) = 0 := by
      linear_combination 2 * hEP + 2 * hEQ - 4 * hE0
    obtain rfl : α = 0 := (mul_eq_zero.mp key).resolve_right hnd.ne'
    have hc0 : c ≠ 0 := by rintro rfl; simp at hd
    rw [mem_hline_zero hc0] at hPL hQL
    obtain ⟨-, s, hs⟩ := hPL
    obtain ⟨-, t, ht⟩ := hQL
    have hst : (t : ℂ) - s ≠ 0 := by
      intro h0
      apply hPQ
      have : (t : ℂ) = s := sub_eq_zero.mp h0
      rw [hs, ht, this]
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨-s / (t - s), ?_⟩
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    rw [hs, ht]
    push_cast
    field_simp
    ring
  · intro h0
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h0
    rw [AffineMap.lineMap_apply] at hr
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul] at hr
    have hd0 : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
    have hdn : 0 < ‖Q - P‖ := norm_pos_iff.mpr hd0
    have hdn' : ((‖Q - P‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdn.ne'
    set u : ℂ := ((‖Q - P‖ : ℝ) : ℂ)⁻¹ * (Q - P) with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_mul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hdn.ne']
    have hdu : Q - P = u * ((‖Q - P‖ : ℝ) : ℂ) := by rw [hudef]; field_simp
    have hPu : P = u * (((-r * ‖Q - P‖ : ℝ)) : ℂ) := by
      push_cast
      linear_combination hr - (r : ℂ) * hdu
    have hQu : Q = u * ((((1 - r) * ‖Q - P‖ : ℝ)) : ℂ) := by
      have hPu' := hPu
      push_cast at hPu' ⊢
      linear_combination hdu + hPu'
    have hn : ∀ y : ℝ, ‖u * (y : ℂ)‖ = |y| := by
      intro y; rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hp : |(-r * ‖Q - P‖ : ℝ)| < 1 := by rw [← hn, ← hPu]; exact hP
    have hq : |((1 - r) * ‖Q - P‖ : ℝ)| < 1 := by rw [← hn, ← hQu]; exact hQ
    have := hsegment_real_dir hu hp hq
    rwa [← hPu, ← hQu] at this

/-! ### H-circles (Lemma 12.10) -/

/-- Lemma 12.10: every h-circle `hcircle P r` (`r > 0`) is a Euclidean circle `Metric.sphere C ρ`
lying inside the disc (`‖C‖ + ρ < 1`), with centre `C = P/(1+K)` a positive real multiple of `P`
(so on the ray `OP`) and radius `ρ = √(K (1 - ‖P‖² + K))/(1+K)`, where
`K = (cosh r - 1)(1 - ‖P‖²)/2`. -/
@[kb "petrunin2025" "Lemma 12.10, p. 96"]
theorem hcircle_eq_sphere {P : ℂ} (hP : ‖P‖ < 1) {r : ℝ} (hr : 0 < r) :
    ∃ (C : ℂ) (ρ : ℝ), 0 < ρ ∧ ‖C‖ + ρ < 1 ∧ (∃ l : ℝ, 0 < l ∧ C = (l : ℂ) * P) ∧
      hcircle P r = Metric.sphere C ρ := by
  have hnP0 : 0 < 1 - ‖P‖ ^ 2 := one_sub_sq_pos hP
  set K := (Real.cosh r - 1) * (1 - ‖P‖ ^ 2) / 2 with hK
  have hcr : 1 < Real.cosh r := Real.one_lt_cosh.mpr hr.ne'
  have hK0 : 0 < K := by rw [hK]; have := sub_pos.mpr hcr; positivity
  have hL : 0 < 1 + K := by linarith
  have hQ0 : 0 < K * (1 - ‖P‖ ^ 2 + K) := by positivity
  set ρ := Real.sqrt (K * (1 - ‖P‖ ^ 2 + K)) / (1 + K) with hρ
  have hρ0 : 0 < ρ := div_pos (Real.sqrt_pos.mpr hQ0) hL
  have hρ2 : ρ ^ 2 = K * (1 - ‖P‖ ^ 2 + K) / (1 + K) ^ 2 := by
    rw [hρ, div_pow, Real.sq_sqrt hQ0.le]
  have hl : 0 < 1 / (1 + K) := by positivity
  have hCn : ‖(((1 / (1 + K) : ℝ)) : ℂ) * P‖ = ‖P‖ / (1 + K) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.le]; ring
  have hin : ‖(((1 / (1 + K) : ℝ)) : ℂ) * P‖ + ρ < 1 := by
    rw [hCn, hρ, ← add_div, div_lt_one hL]
    have hs : Real.sqrt (K * (1 - ‖P‖ ^ 2 + K)) < 1 + K - ‖P‖ := by
      rw [Real.sqrt_lt' (by linarith)]
      nlinarith [mul_pos hL (sq_pos_of_pos (sub_pos.mpr hP)), norm_nonneg P]
    linarith
  have alg : ∀ Q : ℂ, ‖Q - (((1 / (1 + K) : ℝ)) : ℂ) * P‖ ^ 2 - ρ ^ 2 =
      ((1 + K) * ‖Q‖ ^ 2 - 2 * (P.re * Q.re + P.im * Q.im) + ‖P‖ ^ 2 - K) / (1 + K) := by
    intro Q
    rw [hρ2, sq_norm_eq, sq_norm_eq Q, sq_norm_eq P]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, zero_sub]
    field_simp
    ring
  have hcosh_iff : ∀ Q : ℂ, ‖Q‖ < 1 → (hdist P Q = r ↔ ‖P - Q‖ ^ 2 = K * (1 - ‖Q‖ ^ 2)) := by
    intro Q hQ
    have hnQ := one_sub_sq_pos hQ
    constructor
    · intro h
      have h1 := cosh_hdist hP hQ
      rw [h] at h1
      unfold hcosh at h1
      have : 2 * ‖P - Q‖ ^ 2 / ((1 - ‖P‖ ^ 2) * (1 - ‖Q‖ ^ 2)) = Real.cosh r - 1 := by linarith
      rw [div_eq_iff (by positivity)] at this
      rw [hK]; linear_combination this / 2
    · intro h
      unfold hdist
      have : hcosh P Q = Real.cosh r := by
        unfold hcosh
        rw [h, hK]
        field_simp
        ring
      rw [this, Real.arcosh_cosh hr.le]
  have e : ∀ Q : ℂ, ‖P - Q‖ ^ 2 = ‖P‖ ^ 2 - 2 * (P.re * Q.re + P.im * Q.im) + ‖Q‖ ^ 2 := by
    intro Q
    rw [sq_norm_eq, sq_norm_eq P, sq_norm_eq Q]; simp only [Complex.sub_re, Complex.sub_im]; ring
  refine ⟨(((1 / (1 + K) : ℝ)) : ℂ) * P, ρ, hρ0, hin, ⟨1 / (1 + K), hl, rfl⟩, ?_⟩
  ext Q
  simp only [Metric.mem_sphere, dist_eq_norm]
  constructor
  · rintro ⟨hQ, h⟩
    have h1 := (hcosh_iff Q hQ).mp h
    have h2 := alg Q
    have : ‖Q - (((1 / (1 + K) : ℝ)) : ℂ) * P‖ ^ 2 = ρ ^ 2 := by
      have h3 : (1 + K) * ‖Q‖ ^ 2 - 2 * (P.re * Q.re + P.im * Q.im) + ‖P‖ ^ 2 - K = 0 := by
        linarith [e Q]
      rw [h3, zero_div] at h2; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) hρ0.le).mp this
  · intro h
    have hQ : ‖Q‖ < 1 := by
      have h5 : ‖Q‖ ≤ ‖Q - (((1 / (1 + K) : ℝ)) : ℂ) * P‖ + ‖(((1 / (1 + K) : ℝ)) : ℂ) * P‖ := by
        have := norm_add_le (Q - (((1 / (1 + K) : ℝ)) : ℂ) * P) ((((1 / (1 + K) : ℝ)) : ℂ) * P)
        simpa using this
      linarith
    refine ⟨hQ, (hcosh_iff Q hQ).mpr ?_⟩
    have h2 := alg Q
    rw [h, sub_self] at h2
    have h3 := (div_eq_zero_iff.mp h2.symm).resolve_right hL.ne'
    linarith [e Q]

/-! ### The aiming lemma (Lemma 12.6) -/

/-- Lemma 12.6 (aiming lemma, book form): for `0 < ‖P‖ < 1`, the circle `Γ` with centre
`P' = P/‖P‖²` (the inverse of `P` in the absolute) and radius `√(1 - ‖P‖²)/‖P‖` is perpendicular
to the absolute (the unit circle) and the inversion in `Γ` sends `P` to the centre `O = 0`. -/
@[kb "petrunin2025" "Lemma 12.6, p. 94"]
theorem aiming_lemma {P : ℂ} (hP0 : 0 < ‖P‖) (hP : ‖P‖ < 1) :
    OrthogonalCircles
        (⟨P / ((‖P‖ ^ 2 : ℝ) : ℂ), Real.sqrt (1 - ‖P‖ ^ 2) / ‖P‖⟩ : EuclideanGeometry.Sphere ℂ)
        (⟨0, 1⟩ : EuclideanGeometry.Sphere ℂ) ∧
      EuclideanGeometry.inversion (P / ((‖P‖ ^ 2 : ℝ) : ℂ)) (Real.sqrt (1 - ‖P‖ ^ 2) / ‖P‖) P
        = 0 := by
  have hn := one_sub_sq_pos hP
  have hs : (0 : ℝ) < ‖P‖ ^ 2 := by positivity
  have hsq : Real.sqrt (1 - ‖P‖ ^ 2) ^ 2 = 1 - ‖P‖ ^ 2 := Real.sq_sqrt hn.le
  have hP0' : (‖P‖ : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
  constructor
  · rw [orthogonalCircles_iff (by positivity) one_pos (by simp)]
    simp only [dist_eq_norm, zero_sub, norm_neg]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le,
      div_pow (Real.sqrt (1 - ‖P‖ ^ 2)) ‖P‖ 2, hsq]
    field_simp
    ring
  · have hd : dist P (P / ((‖P‖ ^ 2 : ℝ) : ℂ)) = (1 - ‖P‖ ^ 2) / ‖P‖ := by
      rw [dist_eq_norm]
      have : P - P / ((‖P‖ ^ 2 : ℝ) : ℂ) = (((-(1 - ‖P‖ ^ 2) / ‖P‖ ^ 2 : ℝ)) : ℂ) * P := by
        have : ((‖P‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        push_cast at this ⊢
        field_simp
        ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
        abs_of_pos hn, abs_of_pos hs]
      field_simp
    unfold EuclideanGeometry.inversion
    rw [hd]
    simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    have h1 : (Real.sqrt (1 - ‖P‖ ^ 2) / ‖P‖ / ((1 - ‖P‖ ^ 2) / ‖P‖)) ^ 2 = 1 / (1 - ‖P‖ ^ 2) := by
      rw [div_pow, div_pow, hsq]
      field_simp
    rw [h1]
    have : ((‖P‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have h2 : ((1 - ‖P‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast at this h2 ⊢
    field_simp
    ring

/-! ### Inversions in circles perpendicular to the absolute (Observation 12.7) -/

section InversionMotion

/-- The inversion in the circle with centre `o` and radius `R`, `‖o‖² = 1 + R²`, written as
`z ↦ (o z̄ - 1)/(z̄ - ō)`. -/
noncomputable def invF (o z : ℂ) : ℂ := (o * conj z - 1) / (conj z - conj o)

theorem norm_conj_sub (z o : ℂ) : ‖conj z - conj o‖ = ‖z - o‖ := by
  rw [← map_sub, Complex.norm_conj]

theorem norm_N_sq (o z : ℂ) :
    ‖o * conj z - 1‖ ^ 2 = ‖z - o‖ ^ 2 + (‖o‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
  simp only [sq_norm_eq]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

theorem norm_sub_pos_of_one_lt {o z : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) : 0 < ‖z - o‖ := by
  apply norm_pos_iff.mpr
  intro h
  have : z = o := sub_eq_zero.mp h
  rw [this] at hz; linarith

theorem den_ne {o z : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) : conj z - conj o ≠ 0 := by
  intro h
  have := norm_sub_pos_of_one_lt ho hz
  rw [← norm_conj_sub, h, norm_zero] at this
  exact lt_irrefl _ this

theorem one_sub_norm_invF {o z : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) :
    1 - ‖invF o z‖ ^ 2 = (‖o‖ ^ 2 - 1) * (1 - ‖z‖ ^ 2) / ‖z - o‖ ^ 2 := by
  have hM := norm_sub_pos_of_one_lt ho hz
  unfold invF
  rw [norm_div, div_pow, norm_conj_sub, norm_N_sq]
  field_simp
  ring

theorem norm_invF_lt_one {o z : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) : ‖invF o z‖ < 1 := by
  have h := one_sub_norm_invF ho hz
  have hM := norm_sub_pos_of_one_lt ho hz
  have hK : 0 < ‖o‖ ^ 2 - 1 := by nlinarith
  have hpos : 0 < (‖o‖ ^ 2 - 1) * (1 - ‖z‖ ^ 2) / ‖z - o‖ ^ 2 :=
    div_pos (mul_pos hK (one_sub_sq_pos hz)) (by positivity)
  by_contra hc
  rw [not_lt] at hc
  nlinarith [norm_nonneg (invF o z)]

theorem invF_sub {o z w : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    invF o z - invF o w =
      ((‖o‖ ^ 2 - 1 : ℝ) : ℂ) * conj (w - z) / ((conj z - conj o) * (conj w - conj o)) := by
  have h1 := den_ne ho hz
  have h2 := den_ne ho hw
  have hoo : (‖o‖ : ℂ) ^ 2 = o * conj o := by
    have := Complex.mul_conj o
    rw [Complex.normSq_eq_norm_sq] at this
    push_cast at this
    exact this.symm
  unfold invF
  rw [div_sub_div _ _ h1 h2]
  congr 1
  rw [map_sub]
  push_cast
  rw [hoo]
  ring

theorem norm_invF_sub {o z w : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖invF o z - invF o w‖ = (‖o‖ ^ 2 - 1) * ‖z - w‖ / (‖z - o‖ * ‖w - o‖) := by
  have hK : 0 ≤ ‖o‖ ^ 2 - 1 := by nlinarith
  rw [invF_sub ho hz hw, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hK, Complex.norm_conj, norm_sub_rev w z, norm_conj_sub, norm_conj_sub]

theorem hcosh_invF {o z w : ℂ} (ho : 1 < ‖o‖) (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hcosh (invF o z) (invF o w) = hcosh z w := by
  have hK : 0 < ‖o‖ ^ 2 - 1 := by nlinarith
  have hz' := one_sub_sq_pos hz
  have hw' := one_sub_sq_pos hw
  have dz := norm_sub_pos_of_one_lt ho hz
  have dw := norm_sub_pos_of_one_lt ho hw
  unfold hcosh
  rw [norm_invF_sub ho hz hw, one_sub_norm_invF ho hz, one_sub_norm_invF ho hw]
  generalize ‖z - o‖ = Dz at dz ⊢
  generalize ‖w - o‖ = Dw at dw ⊢
  generalize ‖o‖ ^ 2 - 1 = K at hK ⊢
  have := hK.ne'
  have := hz'.ne'
  have := hw'.ne'
  have := dz.ne'
  have := dw.ne'
  field_simp

/-- Parameters of the h-line `hline α c` pulled back along the inversion with centre `o`. -/
noncomputable def iα (o : ℂ) (α : ℝ) (c : ℂ) : ℝ := α * (‖o‖ ^ 2 + 1) - 2 * (conj c * o).re

/-- See `iα`. -/
noncomputable def ic (o : ℂ) (α : ℝ) (c : ℂ) : ℂ := 2 * (α : ℂ) * o - c - conj c * (o * o)

theorem invF_hE_poly (α : ℝ) (c o w : ℂ) :
    α * (‖o * conj w - 1‖ ^ 2 + ‖conj w - conj o‖ ^ 2) -
        2 * (conj c * ((o * conj w - 1) * conj (conj w - conj o))).re =
      hE (iα o α c) (ic o α c) w := by
  simp only [hE_coord, sq_norm_eq]
  simp only [iα, ic, sq_norm_eq, re_conj_mul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem ic_disc (o : ℂ) (α : ℝ) (c : ℂ) :
    ‖ic o α c‖ ^ 2 - iα o α c ^ 2 = (‖o‖ ^ 2 - 1) ^ 2 * (‖c‖ ^ 2 - α ^ 2) := by
  simp only [sq_norm_eq]
  simp only [iα, ic, sq_norm_eq, re_conj_mul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

theorem iα_lt {o : ℂ} {α : ℝ} {c : ℂ} (ho : 1 < ‖o‖) (h : α ^ 2 < ‖c‖ ^ 2) :
    iα o α c ^ 2 < ‖ic o α c‖ ^ 2 := by
  have h1 := ic_disc o α c
  have hK : 0 < ‖o‖ ^ 2 - 1 := by nlinarith
  have h2 : 0 < (‖o‖ ^ 2 - 1) ^ 2 := by positivity
  nlinarith [mul_pos h2 (sub_pos.mpr h)]

theorem hE_invF {α : ℝ} {c o w : ℂ} (ho : 1 < ‖o‖) (hw : ‖w‖ < 1) :
    hE α c (invF o w) * ‖w - o‖ ^ 2 = hE (iα o α c) (ic o α c) w := by
  have hD := den_ne ho hw
  set D := conj w - conj o with hDdef
  have hz : invF o w * D = o * conj w - 1 := by unfold invF; exact div_mul_cancel₀ _ hD
  rw [← invF_hE_poly, ← hDdef]
  have hDn : ‖D‖ = ‖w - o‖ := norm_conj_sub w o
  have hn : ‖invF o w‖ ^ 2 * ‖D‖ ^ 2 = ‖o * conj w - 1‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, hz]
  have e : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : (conj c * invF o w).re * ‖D‖ ^ 2 =
      (conj c * ((o * conj w - 1) * conj D)).re := by
    have : conj c * ((o * conj w - 1) * conj D) = (conj c * invF o w) * ((‖D‖ ^ 2 : ℝ) : ℂ) := by
      rw [e, ← hz]; ring
    rw [this, Complex.re_mul_ofReal]
  rw [← hDn]
  unfold hE
  linear_combination α * hn - 2 * hre

theorem invF_mem_hline_iff {α : ℝ} {c o w : ℂ} (ho : 1 < ‖o‖) (hw : ‖w‖ < 1) :
    invF o w ∈ hline α c ↔ w ∈ hline (iα o α c) (ic o α c) := by
  have h := hE_invF (α := α) (c := c) ho hw
  have hD := norm_sub_pos_of_one_lt ho hw
  rw [mem_hline_iff, mem_hline_iff]
  constructor
  · rintro ⟨_, h0⟩; exact ⟨hw, by rw [← h, h0, zero_mul]⟩
  · rintro ⟨_, h0⟩
    refine ⟨norm_invF_lt_one ho hw, ?_⟩
    rw [← h] at h0
    exact (mul_eq_zero.mp h0).resolve_right (by positivity)

theorem inversion_eq_invF {o z : ℂ} {R : ℝ} (hR : 0 < R) (ho : ‖o‖ ^ 2 = 1 + R ^ 2)
    (hz : ‖z‖ < 1) :
    EuclideanGeometry.inversion o R z = invF o z := by
  have hoR : 1 < ‖o‖ := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg o, sq_pos_of_pos hR]
  have hzo : z - o ≠ 0 := norm_pos_iff.mp (norm_sub_pos_of_one_lt hoR hz)
  have hzo' : conj z - conj o ≠ 0 := den_ne hoR hz
  unfold invF
  rw [eq_div_iff hzo']
  unfold EuclideanGeometry.inversion
  rw [dist_eq_norm]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  have hN : ((‖z - o‖ : ℝ) : ℂ) ^ 2 = (z - o) * (conj z - conj o) := by
    rw [← map_sub, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hoo : (‖o‖ : ℂ) ^ 2 = o * conj o := by
    have := Complex.mul_conj o
    rw [Complex.normSq_eq_norm_sq] at this
    push_cast at this
    exact this.symm
  have hRo : (R : ℂ) ^ 2 = o * conj o - 1 := by
    have : ((‖o‖ ^ 2 : ℝ) : ℂ) = ((1 + R ^ 2 : ℝ) : ℂ) := by rw [ho]
    push_cast at this
    rw [← hoo, this]; ring
  push_cast
  rw [div_pow, hN, hRo]
  field_simp
  ring

theorem inversion_hmotion_core {o : ℂ} {R : ℝ} (hR : 0 < R) (ho : ‖o‖ ^ 2 = 1 + R ^ 2) :
    (∀ z : ℂ, ‖z‖ < 1 → ‖EuclideanGeometry.inversion o R z‖ < 1) ∧
    EuclideanGeometry.inversion o R '' {z : ℂ | ‖z‖ < 1} = {z : ℂ | ‖z‖ < 1} ∧
    (∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 →
      hdist (EuclideanGeometry.inversion o R z) (EuclideanGeometry.inversion o R w) = hdist z w) ∧
    (∀ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 → ∃ (α' : ℝ) (c' : ℂ), α' ^ 2 < ‖c'‖ ^ 2 ∧
      EuclideanGeometry.inversion o R '' hline α c = hline α' c') := by
  have hoR : 1 < ‖o‖ := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg o, sq_pos_of_pos hR]
  have key : ∀ z : ℂ, ‖z‖ < 1 → EuclideanGeometry.inversion o R z = invF o z :=
    fun z hz => inversion_eq_invF hR ho hz
  have inv : ∀ x, EuclideanGeometry.inversion o R (EuclideanGeometry.inversion o R x) = x :=
    EuclideanGeometry.inversion_inversion o hR.ne'
  have p1 : ∀ z : ℂ, ‖z‖ < 1 → ‖EuclideanGeometry.inversion o R z‖ < 1 := by
    intro z hz; rw [key z hz]; exact norm_invF_lt_one hoR hz
  refine ⟨p1, ?_, ?_, ?_⟩
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact p1 z hz
    · intro hw; exact ⟨EuclideanGeometry.inversion o R w, p1 w hw, inv w⟩
  · intro z w hz hw
    rw [key z hz, key w hw]
    unfold hdist
    rw [hcosh_invF hoR hz hw]
  · intro α c h
    refine ⟨iα o α c, ic o α c, iα_lt hoR h, ?_⟩
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hw' := p1 z hz.1
      refine (invF_mem_hline_iff hoR hw').mp ?_
      rw [← key _ hw', inv]; exact hz
    · intro hw
      have hw1 := hw.1
      refine ⟨EuclideanGeometry.inversion o R w, ?_, inv w⟩
      rw [key w hw1]
      exact (invF_mem_hline_iff hoR hw1).mpr hw

/-- Observation 12.7: the inversion in a circle `Γ` perpendicular to the absolute maps the open
disc onto itself, preserves the h-distance, and sends h-lines to h-lines (hence also h-segments,
by `hdist_add_iff_mem_hsegment`).  Here `Γ` is any sphere of `ℂ` with positive radius that is
perpendicular (`OrthogonalCircles`) to the unit circle.  (Negation of h-angles is not
formalized: h-angles are not defined here.) -/
@[kb "petrunin2025" "Observation 12.7, p. 94"]
theorem inversion_hmotion (Γ : EuclideanGeometry.Sphere ℂ) (hΓ : 0 < Γ.radius)
    (hperp : OrthogonalCircles Γ (⟨0, 1⟩ : EuclideanGeometry.Sphere ℂ)) :
    (∀ z : ℂ, ‖z‖ < 1 → ‖EuclideanGeometry.inversion Γ.center Γ.radius z‖ < 1) ∧
    EuclideanGeometry.inversion Γ.center Γ.radius '' {z : ℂ | ‖z‖ < 1} = {z : ℂ | ‖z‖ < 1} ∧
    (∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 →
      hdist (EuclideanGeometry.inversion Γ.center Γ.radius z)
        (EuclideanGeometry.inversion Γ.center Γ.radius w) = hdist z w) ∧
    (∀ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 → ∃ (α' : ℝ) (c' : ℂ), α' ^ 2 < ‖c'‖ ^ 2 ∧
      EuclideanGeometry.inversion Γ.center Γ.radius '' hline α c = hline α' c') := by
  rw [orthogonalCircles_iff hΓ.le one_pos (by simp)] at hperp
  simp only [dist_eq_norm, zero_sub, norm_neg] at hperp
  exact inversion_hmotion_core hΓ (by simpa using hperp)

end InversionMotion

end UndergradKB.Geometry
