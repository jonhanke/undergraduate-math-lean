import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Between
import UndergradKB.Common.Attr
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import UndergradKB.Geometry.AffineTheorems
import UndergradKB.Geometry.KleinModel

/-! # The projective model, continued (Petrunin, chapter 17C, 17B and chapter 13C)

Bolyai's construction (Construction 17.12 and Proposition 17.14, in the projective model with the
centre `O` as the point `P`, which is the book's reduction), hyperbolic Pappus (Theorem 17.4) and
motions in the projective model (Remark p. 143), equidistants and horocycles (chapter 13C). -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

/-! ### Bolyai's construction (Construction 17.12, Proposition 17.14) -/

section Bolyai

theorem norm_kleinInv_lt_one {X : ℂ} (hX : ‖X‖ < 1) : ‖kleinInv X‖ < 1 := by
  obtain ⟨P, hP, rfl⟩ := kleinMap_bijOn.surjOn (show X ∈ Metric.ball (0 : ℂ) 1 by simpa using hX)
  rw [kleinInv_kleinMap (by simpa using hP)]; simpa using hP

/-- The conformal-model distance of the preimages equals the projective distance. -/
theorem hdist_kleinInv {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    hdist (kleinInv X) (kleinInv Y) = kdist X Y := by
  rw [hdist_eq_kdist (norm_kleinInv_lt_one hX) (norm_kleinInv_lt_one hY), kleinMap_kleinInv hX,
    kleinMap_kleinInv hY]

theorem one_le_kcosh {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) : 1 ≤ kcosh X Y := by
  have hX' := norm_kleinInv_lt_one hX
  have hY' := norm_kleinInv_lt_one hY
  have := one_le_hcosh hX' hY'
  rwa [hcosh_eq_kcosh _ _ hX' hY', kleinMap_kleinInv hX, kleinMap_kleinInv hY] at this

theorem kdist_eq_iff {X Y X' Y' : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (hX' : ‖X'‖ < 1)
    (hY' : ‖Y'‖ < 1) : kdist X Y = kdist X' Y' ↔ kcosh X Y = kcosh X' Y' := by
  rw [kdist_eq_arcosh hX hY, kdist_eq_arcosh hX' hY']
  constructor
  · intro h
    have := congrArg Real.cosh h
    rwa [Real.cosh_arcosh (one_le_kcosh hX hY), Real.cosh_arcosh (one_le_kcosh hX' hY')] at this
  · intro h; rw [h]

theorem div_sqrt_eq_iff {n1 m1 n2 m2 : ℝ} (hn1 : 0 < n1) (hn2 : 0 < n2) (hm1 : 0 < m1)
    (hm2 : 0 < m2) : n1 / Real.sqrt m1 = n2 / Real.sqrt m2 ↔ n1 ^ 2 * m2 = n2 ^ 2 * m1 := by
  have a1 := Real.sqrt_pos.mpr hm1
  have a2 := Real.sqrt_pos.mpr hm2
  rw [← sq_eq_sq₀ (by positivity) (by positivity), div_pow, div_pow, Real.sq_sqrt hm1.le,
    Real.sq_sqrt hm2.le, div_eq_div_iff hm1.ne' hm2.ne']

theorem perp_smul {Q W : ℂ} (hQ : Q ≠ 0) (h : Q.re * W.re + Q.im * W.im = 0) :
    W = ((Q.re * W.im - Q.im * W.re) / (Q.re ^ 2 + Q.im ^ 2)) • (Complex.I * Q) := by
  have hN : Q.re ^ 2 + Q.im ^ 2 ≠ 0 := by rw [← sq_norm_eq]; simpa using hQ
  apply Complex.ext
  · simp only [Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im, smul_eq_mul]
    field_simp
    linear_combination Q.re * h
  · simp only [Complex.smul_im, Complex.mul_im, Complex.I_re, Complex.I_im, smul_eq_mul]
    field_simp
    linear_combination Q.im * h

theorem par_smul {Q W : ℂ} (hQ : Q ≠ 0) (h : Q.re * W.im - Q.im * W.re = 0) :
    W = ((Q.re * W.re + Q.im * W.im) / (Q.re ^ 2 + Q.im ^ 2)) • Q := by
  have hN : Q.re ^ 2 + Q.im ^ 2 ≠ 0 := by rw [← sq_norm_eq]; simpa using hQ
  apply Complex.ext
  · simp only [Complex.smul_re, smul_eq_mul]
    field_simp
    linear_combination (-Q.im) * h
  · simp only [Complex.smul_im, smul_eq_mul]
    field_simp
    linear_combination Q.re * h

theorem bolyai_coords {Q R S T : ℂ} (hQ0 : Q ≠ 0) (hS0 : S ≠ 0)
    (h1 : (Q * conj (R - Q)).re = 0) (h2 : (S * conj Q).re = 0)
    (h3 : ((T - R) * conj S).re = 0) :
    ∃ ρ μ : ℝ, R = (((1 : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q ∧
      T = (((1 + μ : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im] at h1 h2 h3
  have hR := perp_smul hQ0 (W := R - Q) (by simp only [Complex.sub_re, Complex.sub_im]; linarith)
  have hS := perp_smul hQ0 (W := S) (by linarith)
  obtain ⟨ρ, hρR⟩ : ∃ ρ : ℝ, R - Q = ρ • (Complex.I * Q) := ⟨_, hR⟩
  obtain ⟨σ, hS⟩ : ∃ σ : ℝ, S = σ • (Complex.I * Q) := ⟨_, hS⟩
  have hσ0 : σ ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hS; exact hS0 hS
  have hSre : S.re = -σ * Q.im := by
    have := congrArg Complex.re hS
    simpa [Complex.mul_re] using this
  have hSim : S.im = σ * Q.re := by
    have := congrArg Complex.im hS
    simpa [Complex.mul_im] using this
  have hpar : Q.re * (T - R).im - Q.im * (T - R).re = 0 := by
    rw [hSre, hSim] at h3
    have : σ * (Q.re * (T - R).im - Q.im * (T - R).re) = 0 := by
      simp only [Complex.sub_re, Complex.sub_im] at h3 ⊢
      linarith
    exact (mul_eq_zero.mp this).resolve_left hσ0
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, T - R = μ • Q := ⟨_, par_smul hQ0 hpar⟩
  have e : R = Q + ρ • (Complex.I * Q) := by rw [← hρR]; ring
  refine ⟨ρ, μ, ?_, ?_⟩
  · rw [e, Complex.real_smul]; push_cast; ring
  · have hTe : T = R + μ • Q := by rw [← hμ]; ring
    rw [hTe, e]
    simp only [Complex.real_smul]
    push_cast
    ring

theorem norm_form_sq (a b : ℝ) (Q : ℂ) :
    ‖((a : ℂ) + (b : ℂ) * Complex.I) * Q‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖Q‖ ^ 2 := by
  rw [norm_mul, mul_pow, sq_norm_eq]; simp

theorem re_conj_form (a b : ℝ) (Q : ℂ) :
    (conj Q * (((a : ℂ) + (b : ℂ) * Complex.I) * Q)).re = a * ‖Q‖ ^ 2 := by
  rw [sq_norm_eq]; simp [Complex.mul_re, Complex.mul_im]; ring

theorem kcosh_bolyai_iff {Q R T : ℂ} {ρ μ : ℝ} (hQ0 : Q ≠ 0) (hQ : ‖Q‖ < 1)
    (hRe : R = (((1 : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q)
    (hTe : T = (((1 + μ : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q) (hR : ‖R‖ < 1) (hT : ‖T‖ < 1) :
    kcosh Q R = kcosh 0 T ↔ ‖Q‖ ^ 2 * ρ ^ 2 = (1 - ‖Q‖ ^ 2) * (1 + μ) ^ 2 := by
  subst hRe hTe
  have hq := one_sub_sq_pos hQ
  have hq0 : 0 < ‖Q‖ ^ 2 := by have := norm_pos_iff.mpr hQ0; positivity
  have hRq0 := one_sub_sq_pos hR
  have hTq0 := one_sub_sq_pos hT
  have h0 : kcosh 0 ((((1 + μ : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q) =
      1 / Real.sqrt (1 - ‖(((1 + μ : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q‖ ^ 2) := by
    unfold kcosh; simp
  have h1 : kcosh Q ((((1 : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q) =
      (1 - ‖Q‖ ^ 2) / Real.sqrt ((1 - ‖Q‖ ^ 2) *
        (1 - ‖(((1 : ℝ) : ℂ) + (ρ : ℂ) * Complex.I) * Q‖ ^ 2)) := by
    unfold kcosh; rw [re_conj_form]; ring_nf
  rw [h0, h1, div_sqrt_eq_iff hq one_pos (mul_pos hq hRq0) hTq0, norm_form_sq, norm_form_sq]
  have key : (1 - ‖Q‖ ^ 2) ^ 2 * (1 - ((1 + μ) ^ 2 + ρ ^ 2) * ‖Q‖ ^ 2) -
      1 ^ 2 * ((1 - ‖Q‖ ^ 2) * (1 - (1 ^ 2 + ρ ^ 2) * ‖Q‖ ^ 2)) =
      (1 - ‖Q‖ ^ 2) * ‖Q‖ ^ 2 * (‖Q‖ ^ 2 * ρ ^ 2 - (1 - ‖Q‖ ^ 2) * (1 + μ) ^ 2) := by ring
  constructor
  · intro h
    have h' : (1 - ‖Q‖ ^ 2) * ‖Q‖ ^ 2 * (‖Q‖ ^ 2 * ρ ^ 2 - (1 - ‖Q‖ ^ 2) * (1 + μ) ^ 2) = 0 := by
      rw [← key]; linarith
    have := (mul_eq_zero.mp h').resolve_left (mul_pos hq hq0).ne'
    linarith
  · intro h
    have : (1 - ‖Q‖ ^ 2) * ‖Q‖ ^ 2 * (‖Q‖ ^ 2 * ρ ^ 2 - (1 - ‖Q‖ ^ 2) * (1 + μ) ^ 2) = 0 := by
      rw [h]; ring
    rw [← key] at this
    linarith

/-- The core of Proposition 17.14 and of Bolyai's construction, in the projective model with
`P = O` the centre (the book's reduction).  Let `Q, R, T` be points of the disc, `S ≠ O` an
auxiliary point, with `(PQ) ⊥ (QR)`, `(PS) ⊥ (PQ)`, `(RT) ⊥ (PS)` as Euclidean perpendicularities
(which by Observation 17.5 are the h-perpendicularities).  Then `QR_k = PT_k` if and only if the
lines `(PT)` and `(QR)` have a common point `A` of the absolute (that is, `(PT)_h` and `(QR)_h`
are asymptotically parallel).  (The point `S ∈ (RT)` of the book is only the foot of the
perpendicular `k` on `n` and plays no role in the statement.) -/
theorem bolyai_iff {Q R S T : ℂ} (hQ0 : Q ≠ 0) (hS0 : S ≠ 0) (hRQ : R ≠ Q)
    (hQ : ‖Q‖ < 1) (hR : ‖R‖ < 1) (hT : ‖T‖ < 1)
    (h1 : (Q * conj (R - Q)).re = 0) (h2 : (S * conj Q).re = 0)
    (h3 : ((T - R) * conj S).re = 0) :
    kdist Q R = kdist 0 T ↔
      ∃ A : ℂ, ‖A‖ = 1 ∧ (∃ t : ℝ, A = t • T) ∧ ∃ u : ℝ, A = Q + u • (R - Q) := by
  obtain ⟨ρ, μ, hRe, hTe⟩ := bolyai_coords hQ0 hS0 h1 h2 h3
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  rw [kdist_eq_iff hQ hR h0 hT, kcosh_bolyai_iff hQ0 hQ hRe hTe hR hT]
  have hρ : ρ ≠ 0 := by
    intro h; apply hRQ; rw [hRe, h]; simp
  have hq0 : 0 < ‖Q‖ ^ 2 := by have := norm_pos_iff.mpr hQ0; positivity
  have hnT : ‖T‖ ^ 2 = ((1 + μ) ^ 2 + ρ ^ 2) * ‖Q‖ ^ 2 := by rw [hTe, norm_form_sq]
  constructor
  · intro hE
    have hμ : 1 + μ ≠ 0 := by
      intro h
      rw [h] at hE
      have : ‖Q‖ ^ 2 * ρ ^ 2 = 0 := by rw [hE]; ring
      exact mul_ne_zero hq0.ne' (pow_ne_zero 2 hρ) this
    have hμC : (1 + (μ : ℂ)) ≠ 0 := by exact_mod_cast hμ
    refine ⟨(1 / (1 + μ)) • T, ?_, ⟨1 / (1 + μ), rfl⟩, 1 / (1 + μ), ?_⟩
    · have hsq : ‖(1 / (1 + μ)) • T‖ ^ 2 = 1 := by
        rw [norm_smul_sq, hnT]
        field_simp
        linear_combination hE
      have := norm_nonneg ((1 / (1 + μ)) • T)
      nlinarith
    · rw [hTe, hRe]
      simp only [Complex.real_smul]
      push_cast
      field_simp
      ring
  · rintro ⟨A, hA, ⟨t, ht⟩, u, hu⟩
    have hcomp : ((t * (1 + μ) : ℝ) : ℂ) + ((t * ρ : ℝ) : ℂ) * Complex.I =
        (((1 : ℝ) : ℂ) + ((u * ρ : ℝ) : ℂ) * Complex.I) := by
      apply mul_right_cancel₀ hQ0
      have e : A = t • T := ht
      rw [hu, hRe, Complex.real_smul] at e
      rw [hTe] at e
      simp only [Complex.real_smul] at e
      push_cast at e ⊢
      linear_combination -e
    have hre := congrArg Complex.re hcomp
    have him := congrArg Complex.im hcomp
    simp at hre him
    have hut : u = t := by
      rcases him with h | h
      · exact h.symm
      · exact absurd h hρ
    have hnA : ‖A‖ ^ 2 = (1 ^ 2 + (u * ρ) ^ 2) * ‖Q‖ ^ 2 := by
      have e : A = (((1 : ℝ) : ℂ) + ((u * ρ : ℝ) : ℂ) * Complex.I) * Q := by
        rw [hu, hRe]; simp only [Complex.real_smul]; push_cast; ring
      rw [e, norm_form_sq]
    rw [hA, hut] at hnA
    linear_combination (1 + μ) ^ 2 * hnA.symm - ‖Q‖ ^ 2 * ρ ^ 2 * (t * (1 + μ) + 1) * hre

theorem kleinInv_zero : kleinInv 0 = 0 := by simp [kleinInv]

/-- Proposition 17.14 (in the projective model, with `P` the centre, the book's reduction; the
hypotheses are the perpendicularities of the proof, p. 145, by Observation 17.5).  The points
`Q, R, T` are given in the projective model (so the conformal points are `kleinInv Q, ...`).  If the
lines `(PT)` and `(QR)` meet at the point `A` of the absolute (that is, `(PT)_h` and `(QR)_h` are
asymptotically parallel) then `QR_h = PT_h`. -/
@[kb "petrunin2025" "Proposition 17.14, p. 145"]
theorem bolyai_prop_17_14 {Q R S T A : ℂ} (hQ0 : Q ≠ 0) (hS0 : S ≠ 0) (hRQ : R ≠ Q)
    (hQ : ‖Q‖ < 1) (hR : ‖R‖ < 1) (hT : ‖T‖ < 1)
    (h1 : (Q * conj (R - Q)).re = 0) (h2 : (S * conj Q).re = 0)
    (h3 : ((T - R) * conj S).re = 0) (hA : ‖A‖ = 1) (hA1 : ∃ t : ℝ, A = t • T)
    (hA2 : ∃ u : ℝ, A = Q + u • (R - Q)) :
    hdist (kleinInv Q) (kleinInv R) = hdist (kleinInv 0) (kleinInv T) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  rw [hdist_kleinInv hQ hR, hdist_kleinInv h0 hT]
  exact (bolyai_iff hQ0 hS0 hRQ hQ hR hT h1 h2 h3).mpr ⟨A, hA, hA1, hA2⟩

/-- Construction 17.12 (Bolyai), correctness of step 6 in the projective model with `P` the
centre: if `T` is a point of the perpendicular `k` to `n` through `R` (the hypothesis `h3`) with
`PT_h = QR_h` (the circle `Γ`), then the line `(PT)` meets `(QR)` at a point `A` of the absolute,
that is `(PT)_h` is asymptotically parallel to `ℓ = (QR)_h`. -/
@[kb "petrunin2025" "Construction 17.12, p. 144"]
theorem bolyai_construction {Q R S T : ℂ} (hQ0 : Q ≠ 0) (hS0 : S ≠ 0) (hRQ : R ≠ Q)
    (hQ : ‖Q‖ < 1) (hR : ‖R‖ < 1) (hT : ‖T‖ < 1)
    (h1 : (Q * conj (R - Q)).re = 0) (h2 : (S * conj Q).re = 0)
    (h3 : ((T - R) * conj S).re = 0)
    (hd : hdist (kleinInv Q) (kleinInv R) = hdist (kleinInv 0) (kleinInv T)) :
    ∃ A : ℂ, ‖A‖ = 1 ∧ (∃ t : ℝ, A = t • T) ∧ ∃ u : ℝ, A = Q + u • (R - Q) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  rw [hdist_kleinInv hQ hR, hdist_kleinInv h0 hT] at hd
  exact (bolyai_iff hQ0 hS0 hRQ hQ hR hT h1 h2 h3).mp hd

end Bolyai

/-! ### Hyperbolic Pappus (Theorem 17.4) -/

section Pappus

open AffineSubspace Affine

/-- Points of the h-plane are h-collinear if they lie on one h-line `hline α c`
(`α² < ‖c‖²`, so the circline meets the open disc). -/
def HCollinear (S : Set ℂ) : Prop := ∃ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 ∧ S ⊆ hline α c

theorem collinear_of_chord {α : ℝ} {c : ℂ} (hc : c ≠ 0) (T : Set ℂ)
    (hT : ∀ z ∈ T, (conj c * z).re = α) : Collinear ℝ T := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  have hN : c.re ^ 2 + c.im ^ 2 ≠ 0 := by rw [← sq_norm_eq]; simpa using hc
  refine ⟨((α / ‖c‖ ^ 2 : ℝ) : ℂ) * c, Complex.I * c, fun z hz => ?_⟩
  refine ⟨(c.re * z.im - c.im * z.re) / (c.re ^ 2 + c.im ^ 2), ?_⟩
  have h := hT z hz
  rw [re_conj_mul] at h
  rw [vadd_eq_add, sq_norm_eq]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.smul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]
    field_simp
    linear_combination c.re * h
  · simp only [Complex.add_im, Complex.smul_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]
    field_simp
    linear_combination c.im * h

theorem mem_hline_of_kleinMap {α : ℝ} {c z : ℂ} (hz : ‖z‖ < 1)
    (h : (conj c * kleinMap z).re = α) : z ∈ hline α c := by
  refine ⟨hz, ?_⟩
  rw [re_conj_mul_kleinMap] at h
  have : (1 + ‖z‖ ^ 2) ≠ 0 := by positivity
  field_simp at h
  linarith

/-- Section 17B (Lines): h-collinearity is Euclidean collinearity of the images in the projective
model. -/
@[kb "petrunin2025" "Section 17B, Lines, p. 141"]
theorem hcollinear_iff {S : Set ℂ} (hS : ∀ z ∈ S, ‖z‖ < 1) :
    HCollinear S ↔ Collinear ℝ (kleinMap '' S) := by
  constructor
  · rintro ⟨α, c, h, hsub⟩
    apply collinear_of_chord (c_ne_zero h)
    rintro _ ⟨z, hz, rfl⟩
    exact re_conj_mul_kleinMap_of_hline (hsub hz)
  · intro hcol
    rcases S.eq_empty_or_nonempty with rfl | ⟨z0, hz0⟩
    · exact ⟨0, 1, by simp, by simp⟩
    · have hp0 : kleinMap z0 ∈ kleinMap '' S := ⟨z0, hz0, rfl⟩
      obtain ⟨v, hv⟩ := (collinear_iff_of_mem hp0).mp hcol
      set c : ℂ := if v = 0 then 1 else Complex.I * v with hcdef
      have hc0 : c ≠ 0 := by
        by_cases hv0 : v = 0
        · simp [hcdef, hv0]
        · simp [hcdef, hv0]
      have hcv : (conj c * v).re = 0 := by
        by_cases hv0 : v = 0
        · simp [hv0]
        · simp only [hcdef, hv0, ite_false, re_conj_mul]; simp; ring
      have hnorm : ‖kleinMap z0‖ < 1 := norm_kleinMap_lt_one (hS z0 hz0)
      refine ⟨(conj c * kleinMap z0).re, c, ?_, ?_⟩
      · have h1 : |(conj c * kleinMap z0).re| ≤ ‖conj c * kleinMap z0‖ := Complex.abs_re_le_norm _
        rw [norm_mul, Complex.norm_conj] at h1
        have h2 : 0 < ‖c‖ := norm_pos_iff.mpr hc0
        have h3 : (conj c * kleinMap z0).re ^ 2 ≤ (‖c‖ * ‖kleinMap z0‖) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        have hk2 : ‖kleinMap z0‖ ^ 2 < 1 := by nlinarith [norm_nonneg (kleinMap z0)]
        have := mul_lt_mul_of_pos_left hk2 (pow_pos h2 2)
        rw [mul_pow] at h3
        linarith
      · intro z hz
        obtain ⟨r, hr⟩ := hv (kleinMap z) ⟨z, hz, rfl⟩
        apply mem_hline_of_kleinMap (hS z hz)
        rw [hr, vadd_eq_add, mul_add, Complex.add_re, mul_smul_comm, Complex.smul_re, smul_eq_mul,
          hcv]
        ring

theorem kleinMap_injOn_disc {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hab : a ≠ b) :
    kleinMap a ≠ kleinMap b := fun h =>
  hab (kleinMap_bijOn.injOn (by simpa using ha) (by simpa using hb) h)

theorem hcollinear_triple {a b x : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hx : ‖x‖ < 1) :
    HCollinear {a, b, x} ↔ Collinear ℝ ({kleinMap a, kleinMap b, kleinMap x} : Set ℂ) := by
  have := hcollinear_iff (S := {a, b, x}) (by
    intro z hz
    rcases hz with rfl | rfl | rfl <;> assumption)
  simpa [Set.image_insert_eq] using this

/-- The point `X` lies on the h-line `(BC)_h` iff its image lies on the Euclidean line through
the images (projective model). -/
theorem kleinMap_mem_line_of_hcollinear {b c x : ℂ} (hb : ‖b‖ < 1) (hc : ‖c‖ < 1) (hx : ‖x‖ < 1)
    (hbc : b ≠ c) (h : HCollinear {b, c, x}) :
    kleinMap x ∈ line[ℝ, kleinMap b, kleinMap c] := by
  have := (hcollinear_triple hb hc hx).mp h
  exact this.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) (kleinMap_injOn_disc hb hc hbc)

/-- Theorem 17.4 (hyperbolic Pappus).  Let the h-points `A, B, C` be h-collinear and `A', B', C'`
be h-collinear (in the projective model: they lie on two Euclidean lines `(OE)`, `(OE')` through a
point `O`, which may lie outside the disc), and let `X ∈ (BC')_h ∩ (B'C)_h`, `Y ∈ (CA')_h ∩ (C'A)_h`,
`Z ∈ (AB')_h ∩ (A'B)_h`, each pair of the Euclidean lines being non-parallel.  Then `X, Y, Z` are
h-collinear.  This is the Euclidean Pappus theorem (`pappus`) applied to the images under `P ↦ P̂`
(`hcollinear_iff`).  The case of two lines of the projective model that are parallel (meeting at
infinity) is omitted, as in the affine version. -/
@[kb "petrunin2025" "Theorem 17.4, p. 142"]
theorem hyperbolic_pappus {O E E' A B C A' B' C' X Y Z : ℂ}
    (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) (hC : ‖C‖ < 1) (hA' : ‖A'‖ < 1) (hB' : ‖B'‖ < 1)
    (hC' : ‖C'‖ < 1) (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (hZ : ‖Z‖ < 1)
    (h : ¬Collinear ℝ ({O, E, E'} : Set ℂ))
    (hA1 : kleinMap A ∈ line[ℝ, O, E]) (hB1 : kleinMap B ∈ line[ℝ, O, E])
    (hC1 : kleinMap C ∈ line[ℝ, O, E])
    (hA2 : kleinMap A' ∈ line[ℝ, O, E']) (hB2 : kleinMap B' ∈ line[ℝ, O, E'])
    (hC2 : kleinMap C' ∈ line[ℝ, O, E'])
    (hAO : kleinMap A ≠ O) (hBO : kleinMap B ≠ O) (hCO : kleinMap C ≠ O)
    (hA'O : kleinMap A' ≠ O) (hB'O : kleinMap B' ≠ O) (hC'O : kleinMap C' ≠ O)
    (hBC' : B ≠ C') (hB'C : B' ≠ C) (hCA' : C ≠ A') (hC'A : C' ≠ A) (hAB' : A ≠ B')
    (hA'B : A' ≠ B)
    (hX1 : HCollinear {B, C', X}) (hX2 : HCollinear {B', C, X})
    (hY1 : HCollinear {C, A', Y}) (hY2 : HCollinear {C', A, Y})
    (hZ1 : HCollinear {A, B', Z}) (hZ2 : HCollinear {A', B, Z})
    (hXp : ¬ line[ℝ, kleinMap B, kleinMap C'] ∥ line[ℝ, kleinMap B', kleinMap C])
    (hYp : ¬ line[ℝ, kleinMap C, kleinMap A'] ∥ line[ℝ, kleinMap C', kleinMap A])
    (hZp : ¬ line[ℝ, kleinMap A, kleinMap B'] ∥ line[ℝ, kleinMap A', kleinMap B]) :
    HCollinear {X, Y, Z} := by
  have hcol := pappus h hA1 hB1 hC1 hA2 hB2 hC2 hAO hBO hCO hA'O hB'O hC'O
    (kleinMap_mem_line_of_hcollinear hB hC' hX hBC' hX1)
    (kleinMap_mem_line_of_hcollinear hB' hC hX hB'C hX2)
    (kleinMap_mem_line_of_hcollinear hC hA' hY hCA' hY1)
    (kleinMap_mem_line_of_hcollinear hC' hA hY hC'A hY2)
    (kleinMap_mem_line_of_hcollinear hA hB' hZ hAB' hZ1)
    (kleinMap_mem_line_of_hcollinear hA' hB hZ hA'B hZ2) hXp hYp hZp
  exact (hcollinear_triple hX hY hZ).mpr hcol

end Pappus

/-! ### Motions in the projective model (Remark p. 143) -/

section Motions

/-- The projective map of the plane corresponding to the h-motion `mobius a` (`a` real): the
Lorentz boost along the real axis, `X ↦ ((X.re - v) + i s X.im)/(1 - v X.re)` with
`v = 2a/(1+a²)` (the image of `a` under `P ↦ P̂`) and `s = (1-a²)/(1+a²)`.  It is a quotient of two
affine functions of `(X.re, X.im)` with a common denominator, that is, a projective transformation. -/
noncomputable def projBoost (a : ℝ) (X : ℂ) : ℂ :=
  ⟨(X.re - 2 * a / (1 + a ^ 2)) / (1 - 2 * a / (1 + a ^ 2) * X.re),
    (1 - a ^ 2) / (1 + a ^ 2) * X.im / (1 - 2 * a / (1 + a ^ 2) * X.re)⟩

theorem mobius_real_re_im {a : ℝ} (z : ℂ) :
    (mobius (a : ℂ) z).re = ((z.re - a) * (1 - a * z.re) - a * z.im ^ 2) /
        ((1 - a * z.re) ^ 2 + (a * z.im) ^ 2) ∧
      (mobius (a : ℂ) z).im = z.im * (1 - a ^ 2) / ((1 - a * z.re) ^ 2 + (a * z.im) ^ 2) := by
  unfold mobius
  rw [Complex.conj_ofReal]
  have e : Complex.normSq (1 - (a : ℂ) * z) = (1 - a * z.re) ^ 2 + (a * z.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  constructor
  · rw [Complex.div_re, e]
    simp
    field_simp
    ring
  · rw [Complex.div_im, e]
    simp
    field_simp
    ring

theorem boost_re_alg (a x y D Dn : ℝ) (hDdef : D = (1 - a * x) ^ 2 + (a * y) ^ 2)
    (hDn : Dn = (1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2)) - 4 * a * x) (hD : D ≠ 0)
    (hDD : D + ((x - a) ^ 2 + y ^ 2) ≠ 0) (hp1 : 1 + a ^ 2 ≠ 0) (hp2 : 1 + (x ^ 2 + y ^ 2) ≠ 0)
    (hDn0 : Dn ≠ 0) :
    2 / (1 + ((x - a) ^ 2 + y ^ 2) / D) * (((x - a) * (1 - a * x) - a * y ^ 2) / D) =
      (2 / (1 + (x ^ 2 + y ^ 2)) * x - 2 * a / (1 + a ^ 2)) /
        (Dn / ((1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2)))) := by
  field_simp
  subst hDdef hDn
  ring

theorem boost_im_alg (a x y D Dn : ℝ) (hDdef : D = (1 - a * x) ^ 2 + (a * y) ^ 2)
    (hDn : Dn = (1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2)) - 4 * a * x) (hD : D ≠ 0)
    (hDD : D + ((x - a) ^ 2 + y ^ 2) ≠ 0) (hp1 : 1 + a ^ 2 ≠ 0) (hp2 : 1 + (x ^ 2 + y ^ 2) ≠ 0)
    (hDn0 : Dn ≠ 0) :
    2 / (1 + ((x - a) ^ 2 + y ^ 2) / D) * (y * (1 - a ^ 2) / D) =
      (1 - a ^ 2) / (1 + a ^ 2) * (2 / (1 + (x ^ 2 + y ^ 2)) * y) /
        (Dn / ((1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2)))) := by
  field_simp
  subst hDdef hDn
  ring

/-- Remark p. 143 (motions): for real `a`, the h-motion `mobius a` of the conformal model
corresponds, under `P ↦ P̂`, to the projective transformation `projBoost a` of the projective
model (the book's statement that motions of the projective model are the projective
transformations preserving the h-plane, checked here for the motions along the real axis). -/
@[kb "petrunin2025" "Section 17B, Motions, p. 143"]
theorem kleinMap_mobius_real {a : ℝ} (ha : |a| < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    kleinMap (mobius (a : ℂ) z) = projBoost a (kleinMap z) := by
  have hz2 : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := one_sub_sq_pos hz; rw [sq_norm_eq] at this; linarith
  have ha2 : a ^ 2 < 1 := by
    have := sq_lt_one_iff_abs_lt_one a |>.mpr ha; exact this
  have hxa : |a * z.re| < 1 := by
    rw [abs_mul]
    have h1 : |z.re| < 1 := by
      rw [abs_lt]; constructor <;> nlinarith [sq_nonneg z.im]
    calc |a| * |z.re| ≤ |a| * 1 := by gcongr
      _ < 1 := by linarith
  have hD : 0 < (1 - a * z.re) ^ 2 + (a * z.im) ^ 2 := by
    have : 0 < 1 - a * z.re := by rw [abs_lt] at hxa; linarith [hxa.2]
    positivity
  obtain ⟨hre, him⟩ := mobius_real_re_im (a := a) z
  have hwn : ‖mobius (a : ℂ) z‖ ^ 2 =
      ((z.re - a) ^ 2 + z.im ^ 2) / ((1 - a * z.re) ^ 2 + (a * z.im) ^ 2) := by
    unfold mobius
    rw [norm_div, div_pow, sq_norm_eq (z - (a : ℂ)), sq_norm_eq (1 - conj (a : ℂ) * z),
      Complex.conj_ofReal]
    simp
  set x := z.re with hx
  set y := z.im with hy
  have hp1 : 0 < 1 + a ^ 2 := by positivity
  have hp2 : 0 < 1 + (x ^ 2 + y ^ 2) := by positivity
  have hDn : 0 < (1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2)) - 4 * a * x := by
    nlinarith [sq_nonneg (x - a), sq_nonneg y, sq_nonneg (1 - a * x), sq_nonneg (a * y)]
  have eden : 1 - 2 * a / (1 + a ^ 2) * (2 / (1 + (x ^ 2 + y ^ 2)) * x) =
      ((1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2)) - 4 * a * x) / ((1 + a ^ 2) * (1 + (x ^ 2 + y ^ 2))) := by
    field_simp; ring
  have hnz : ‖z‖ ^ 2 = x ^ 2 + y ^ 2 := sq_norm_eq z
  have hD' := hD.ne'
  have hp1' := hp1.ne'
  have hp2' := hp2.ne'
  have hDn' := hDn.ne'
  have hDD : (1 - a * x) ^ 2 + (a * y) ^ 2 + ((x - a) ^ 2 + y ^ 2) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [projBoost, kleinMap_re, kleinMap_im, hnz, hwn, hre, him]
    simp only [← hx, ← hy]
    rw [eden]
    exact boost_re_alg a x y _ _ rfl rfl hD' hDD hp1' hp2' hDn'
  · simp only [projBoost, kleinMap_re, kleinMap_im, hnz, hwn, hre, him]
    simp only [← hx, ← hy]
    rw [eden]
    exact boost_im_alg a x y _ _ rfl rfl hD' hDD hp1' hp2' hDn'

/-- Rotations about the centre act on the projective model by the same rotations. -/
theorem kleinMap_rotation {u z : ℂ} (hu : ‖u‖ = 1) : kleinMap (u * z) = u * kleinMap z := by
  unfold kleinMap
  rw [norm_mul, hu, one_mul, mul_smul_comm]

/-- Exercise 17.3: `2 · OP_h = OP̂_h`, where `O` is the centre of the absolute. -/
@[kb "petrunin2025" "Exercise 17.3, p. 141"]
theorem hdist_zero_kleinMap {P : ℂ} (hP : ‖P‖ < 1) : hdist 0 (kleinMap P) = 2 * hdist 0 P := by
  have hn : ‖kleinMap P‖ = 2 * ‖P‖ / (1 + ‖P‖ ^ 2) := by
    unfold kleinMap
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have h1 : 0 < 1 - ‖P‖ := by linarith
  have h0 := norm_nonneg P
  have hp : 1 + ‖P‖ ^ 2 ≠ 0 := by positivity
  rw [hdist_zero_eq_log (norm_kleinMap_lt_one hP), hdist_zero_eq_log hP, hn]
  have e : (1 + 2 * ‖P‖ / (1 + ‖P‖ ^ 2)) / (1 - 2 * ‖P‖ / (1 + ‖P‖ ^ 2)) =
      ((1 + ‖P‖) / (1 - ‖P‖)) ^ 2 := by
    have : 1 - ‖P‖ ≠ 0 := h1.ne'
    have h2 : (1 + ‖P‖ ^ 2) - 2 * ‖P‖ ≠ 0 := by nlinarith
    field_simp
    ring
  rw [e, Real.log_pow]
  push_cast
  ring

end Motions

/-! ### Equidistants (chapter 13C, p. 106) -/

section Equidistant

theorem mem_hline_real {w : ℂ} : w ∈ hline 0 Complex.I ↔ ‖w‖ < 1 ∧ w.im = 0 := by
  unfold hline
  simp only [Set.mem_ofPred_eq, zero_mul, re_conj_mul]
  simp

theorem kcosh_real_right (X : ℂ) (t : ℝ) :
    kcosh X (t : ℂ) = (1 - X.re * t) / Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - t ^ 2)) := by
  unfold kcosh
  rw [re_conj_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp

theorem div_sqrt_le_iff {n1 m1 n2 m2 : ℝ} (hn1 : 0 < n1) (hn2 : 0 < n2) (hm1 : 0 < m1)
    (hm2 : 0 < m2) : n1 / Real.sqrt m1 ≤ n2 / Real.sqrt m2 ↔ n1 ^ 2 * m2 ≤ n2 ^ 2 * m1 := by
  have a1 := Real.sqrt_pos.mpr hm1
  have a2 := Real.sqrt_pos.mpr hm2
  rw [← sq_le_sq₀ (by positivity) (by positivity), div_pow, div_pow, Real.sq_sqrt hm1.le,
    Real.sq_sqrt hm2.le, div_le_div_iff₀ hm1 hm2]

/-- The foot of the perpendicular from `z` to the real diameter, its distance, and the formula
`sinh d = 2 |Im z| / (1 - ‖z‖²)`: the closest point of the real diameter `hline 0 i` to `z` exists. -/
theorem isLeast_hdist_diameter {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ F ∈ hline 0 Complex.I, IsLeast (hdist z '' hline 0 Complex.I) (hdist z F) ∧
      Real.sinh (hdist z F) = 2 * |z.im| / (1 - ‖z‖ ^ 2) := by
  set X := kleinMap z with hX
  have hXn : ‖X‖ < 1 := norm_kleinMap_lt_one hz
  have hre : |X.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm X) hXn
  have hrn : ‖(X.re : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  set F := kleinInv (X.re : ℂ) with hF
  have hFn : ‖F‖ < 1 := norm_kleinInv_lt_one hrn
  have hFk : kleinMap F = (X.re : ℂ) := kleinMap_kleinInv hrn
  have hFim : F.im = 0 := by
    have h3 := kleinMap_im F
    rw [hFk, Complex.ofReal_im] at h3
    have hne : 2 / (1 + ‖F‖ ^ 2) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h3.symm).resolve_left hne
  have hFl : F ∈ hline 0 Complex.I := mem_hline_real.mpr ⟨hFn, hFim⟩
  have hu : 0 < 1 - X.re ^ 2 := by rw [abs_lt] at hre; nlinarith [hre.1, hre.2]
  have hnX : ‖X‖ ^ 2 = X.re ^ 2 + X.im ^ 2 := sq_norm_eq X
  have hm : 0 < 1 - ‖X‖ ^ 2 := one_sub_sq_pos hXn
  have hcF : hcosh z F = (1 - X.re ^ 2) / Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - X.re ^ 2)) := by
    rw [hcosh_eq_kcosh z F hz hFn, hFk, ← hX, kcosh_real_right]; ring_nf
  refine ⟨F, hFl, ⟨⟨F, hFl, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwn, hwim⟩ := mem_hline_real.mp hw
    have hwk : kleinMap w = ((kleinMap w).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp only [Complex.ofReal_im]; rw [kleinMap_im, hwim]; ring
    set t := (kleinMap w).re with ht
    have htn : |t| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm _) (norm_kleinMap_lt_one hwn)
    have hv : 0 < 1 - t ^ 2 := by rw [abs_lt] at htn; nlinarith [htn.1, htn.2]
    have hcw : hcosh z w = (1 - X.re * t) / Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - t ^ 2)) := by
      rw [hcosh_eq_kcosh z w hz hwn, hwk, ← hX, kcosh_real_right]
    have hle : hcosh z F ≤ hcosh z w := by
      rw [hcF, hcw, div_sqrt_le_iff hu (by rw [abs_lt] at hre htn; nlinarith [hre.1, hre.2, htn.1, htn.2])
        (mul_pos hm hu) (mul_pos hm hv)]
      have : 0 ≤ (X.re - t) ^ 2 := sq_nonneg _
      have h2 : (1 - X.re ^ 2) * (1 - t ^ 2) ≤ (1 - X.re * t) ^ 2 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 (mul_pos hm hu).le
      nlinarith [h3]
    have h1 := cosh_hdist hz hFn
    have h2 := cosh_hdist hz hwn
    have key : Real.cosh (hdist z F) ≤ Real.cosh (hdist z w) := by rw [h1, h2]; exact hle
    have := Real.cosh_le_cosh.mp key
    rwa [abs_of_nonneg (hdist_nonneg hz hFn), abs_of_nonneg (hdist_nonneg hz hwn)] at this
  · have hsq : Real.sinh (hdist z F) ^ 2 = (2 * |z.im| / (1 - ‖z‖ ^ 2)) ^ 2 := by
      have hc := Real.cosh_sq (hdist z F)
      rw [cosh_hdist hz hFn, hcF] at hc
      have hq : (Real.sqrt ((1 - ‖X‖ ^ 2) * (1 - X.re ^ 2))) ^ 2 = (1 - ‖X‖ ^ 2) * (1 - X.re ^ 2) :=
        Real.sq_sqrt (mul_pos hm hu).le
      rw [div_pow, hq] at hc
      have hXim : X.im = 2 / (1 + ‖z‖ ^ 2) * z.im := kleinMap_im z
      have hmX : 1 - ‖X‖ ^ 2 = (1 - ‖z‖ ^ 2) ^ 2 / (1 + ‖z‖ ^ 2) ^ 2 := one_sub_norm_kleinMap_sq z
      have hpz := one_sub_sq_pos hz
      have h1p : (1 + ‖z‖ ^ 2) ≠ 0 := by positivity
      rw [div_pow, mul_pow, sq_abs]
      have e : Real.sinh (hdist z F) ^ 2 = X.im ^ 2 / (1 - ‖X‖ ^ 2) := by
        have : (1 - X.re ^ 2) ^ 2 / ((1 - ‖X‖ ^ 2) * (1 - X.re ^ 2)) = (1 - X.re ^ 2) / (1 - ‖X‖ ^ 2) := by
          field_simp
        rw [this] at hc
        have hm' := hm.ne'
        field_simp at hc ⊢
        nlinarith [hc, hnX]
      rw [e, hXim, hmX]
      field_simp
    have hpz := one_sub_sq_pos hz
    have h0 : 0 ≤ Real.sinh (hdist z F) := Real.sinh_nonneg_iff.mpr (hdist_nonneg hz hFn)
    exact (sq_eq_sq₀ h0 (div_nonneg (by positivity) hpz.le)).mp hsq

/-- Section 13C (Equidistants), the real diameter: for a point `z` of the h-plane, the h-distance
to the h-line `hline 0 i` (the diameter with ideal points `±1`, attained at the foot of the
perpendicular) is `r` iff `sinh r · (1 - ‖z‖²) = 2 |Im z|`. -/
theorem isLeast_hdist_diameter_iff {z : ℂ} (hz : ‖z‖ < 1) (r : ℝ) :
    IsLeast (hdist z '' hline 0 Complex.I) r ↔ Real.sinh r * (1 - ‖z‖ ^ 2) = 2 * |z.im| := by
  obtain ⟨F, hFl, hFleast, hs⟩ := isLeast_hdist_diameter hz
  have hpz := one_sub_sq_pos hz
  constructor
  · intro h
    have := hFleast.unique h
    rw [← this, hs]
    field_simp
  · intro h
    have : Real.sinh r = Real.sinh (hdist z F) := by
      rw [hs]; field_simp; linarith
    have := Real.sinh_injective this
    rw [this]; exact hFleast

/-- Section 13C (Equidistants), the real diameter, as circles: for `r > 0` the points of the disc at
h-distance `r` from the h-line with ideal points `A = -1`, `B = 1` are exactly the points of the
disc lying on one of the two Euclidean circles `‖z ± i/sinh r‖² = 1 + 1/sinh² r` through `A` and
`B`, the book's equidistants (one circle for each side of the h-line). -/
@[kb "petrunin2025" "Equidistants of h-lines, p. 106"]
theorem equidistant_diameter {z : ℂ} (hz : ‖z‖ < 1) {r : ℝ} (hr : 0 < r) :
    IsLeast (hdist z '' hline 0 Complex.I) r ↔
      ‖z + Complex.I / (Real.sinh r : ℂ)‖ ^ 2 = 1 + 1 / Real.sinh r ^ 2 ∨
      ‖z - Complex.I / (Real.sinh r : ℂ)‖ ^ 2 = 1 + 1 / Real.sinh r ^ 2 := by
  rw [isLeast_hdist_diameter_iff hz]
  have hs : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have hp := one_sub_sq_pos hz
  generalize Real.sinh r = s at hs ⊢
  have e1 : ‖z + Complex.I / (s : ℂ)‖ ^ 2 = z.re ^ 2 + (z.im + 1 / s) ^ 2 := by
    rw [sq_norm_eq]; simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  have e2 : ‖z - Complex.I / (s : ℂ)‖ ^ 2 = z.re ^ 2 + (z.im - 1 / s) ^ 2 := by
    rw [sq_norm_eq]; simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  have hn := sq_norm_eq z
  rw [e1, e2]
  constructor
  · intro h
    rcases le_total 0 z.im with h0 | h0
    · left
      rw [abs_of_nonneg h0] at h
      field_simp
      nlinarith [h, hn]
    · right
      rw [abs_of_nonpos h0] at h
      field_simp
      nlinarith [h, hn]
  · rintro (h | h)
    · have : 0 ≤ z.im := by
        by_contra hneg
        rw [not_le] at hneg
        field_simp at h
        nlinarith [h, hn, sq_nonneg z.re, mul_pos hs hs]
      rw [abs_of_nonneg this]
      field_simp at h
      nlinarith [h, hn]
    · have : z.im ≤ 0 := by
        by_contra hneg
        rw [not_le] at hneg
        field_simp at h
        nlinarith [h, hn, sq_nonneg z.re, mul_pos hs hs]
      rw [abs_of_nonpos this]
      field_simp at h
      nlinarith [h, hn]

end Equidistant

/-! ### Horocycles (chapter 13C, p. 107) -/

section Horocycle

/-- A horocycle (book p. 107): for a point `A` of the absolute and `0 < ρ < 1`, the Euclidean
circle `Γ` with centre `(1-ρ)A` and radius `ρ` touches the absolute from inside at `A`; the
horocycle is `Γ \ {A}`. -/
@[kb "petrunin2025" "Horocycles, p. 107"]
def horocycle (A : ℂ) (ρ : ℝ) : Set ℂ :=
  {z | ‖z - (((1 - ρ : ℝ)) : ℂ) * A‖ = ρ ∧ z ≠ A}

theorem norm_sub_mul_sq {A : ℂ} (hA : ‖A‖ = 1) (c : ℝ) (z : ℂ) :
    ‖z - (c : ℂ) * A‖ ^ 2 = ‖z‖ ^ 2 + c ^ 2 - 2 * c * (A.re * z.re + A.im * z.im) := by
  have h1 := sq_norm_eq A
  rw [hA] at h1
  rw [sq_norm_eq, sq_norm_eq]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  nlinarith [h1]

theorem norm_sub_sq_ideal {A : ℂ} (hA : ‖A‖ = 1) (z : ℂ) :
    ‖z - A‖ ^ 2 = ‖z‖ ^ 2 + 1 - 2 * (A.re * z.re + A.im * z.im) := by
  have := norm_sub_mul_sq hA 1 z
  simpa using this

/-- Section 13C (Horocycles), basic property: the horocycle `Γ \ {A}` lies in the h-plane and is the
level set `ρ (1 - ‖z‖²) = (1 - ρ) ‖z - A‖²` of the function `(1 - ‖z‖²)/‖z - A‖²` (the conformal
model analogue of a Busemann function). -/
@[kb "petrunin2025" "Horocycles, p. 107"]
theorem mem_horocycle_iff {A : ℂ} (hA : ‖A‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z : ℂ} :
    z ∈ horocycle A ρ ↔ ‖z‖ < 1 ∧ ρ * (1 - ‖z‖ ^ 2) = (1 - ρ) * ‖z - A‖ ^ 2 := by
  have e1 := norm_sub_mul_sq hA (1 - ρ) z
  have e2 := norm_sub_sq_ideal hA z
  constructor
  · rintro ⟨h, hne⟩
    have hsq : ‖z - ((1 - ρ : ℝ) : ℂ) * A‖ ^ 2 = ρ ^ 2 := by rw [h]
    have hid : ρ * (1 - ‖z‖ ^ 2) = (1 - ρ) * ‖z - A‖ ^ 2 := by
      rw [e2]; rw [hsq] at e1; nlinarith [e1]
    refine ⟨?_, hid⟩
    have hd : 0 < ‖z - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have : 0 < ρ * (1 - ‖z‖ ^ 2) := by rw [hid]; positivity
    have : 0 < 1 - ‖z‖ ^ 2 := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    nlinarith [norm_nonneg z]
  · rintro ⟨hz, hid⟩
    have hp := one_sub_sq_pos hz
    refine ⟨?_, ?_⟩
    · have : ‖z - ((1 - ρ : ℝ) : ℂ) * A‖ ^ 2 = ρ ^ 2 := by
        rw [e1]; rw [e2] at hid; push_cast at *; nlinarith [hid]
      exact (sq_eq_sq₀ (norm_nonneg _) hρ0.le).mp this
    · rintro rfl
      rw [sub_self, norm_zero] at hid
      have : ρ * (1 - ‖z‖ ^ 2) = 0 := by rw [hid]; ring
      exact (mul_pos hρ0 hp).ne' this

/-- Section 13C (Horocycles): through every point `P` of the h-plane there passes exactly one
horocycle centred at a given point `A` of the absolute. -/
@[kb "petrunin2025" "Horocycles, p. 107"]
theorem exists_unique_horocycle {A : ℂ} (hA : ‖A‖ = 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃! ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ z ∈ horocycle A ρ := by
  have hp := one_sub_sq_pos hz
  have hne : z ≠ A := by rintro rfl; linarith
  have hd : 0 < ‖z - A‖ ^ 2 := by have := norm_pos_iff.mpr (sub_ne_zero.mpr hne); positivity
  have hs : 0 < ‖z - A‖ ^ 2 + (1 - ‖z‖ ^ 2) := by linarith
  refine ⟨‖z - A‖ ^ 2 / (‖z - A‖ ^ 2 + (1 - ‖z‖ ^ 2)), ⟨div_pos hd hs, ?_, ?_⟩, ?_⟩
  · rw [div_lt_one hs]; linarith
  · refine (mem_horocycle_iff hA (div_pos hd hs) ?_).mpr ⟨hz, ?_⟩
    · rw [div_lt_one hs]; linarith
    · field_simp; ring
  · rintro ρ ⟨hρ0, hρ1, hmem⟩
    obtain ⟨-, hid⟩ := (mem_horocycle_iff hA hρ0 hρ1).mp hmem
    rw [eq_div_iff hs.ne']
    nlinarith [hid]

end Horocycle

end UndergradKB.Geometry
