import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HypTriangles

/-! # The inradius of an h-triangle (Petrunin, chapter 13, Theorem 13.6)

Book proof (p. 105): the angles at the incentre `I` between the three vertices sum to `2π`, so one,
say `∡XIY`, is `≥ 2π/3`; since the side `XY` lies on an h-line at h-distance `r` from `I`,
Proposition 13.3 gives `cos (π/3) > (e^{2r} - 1)/(e^{2r} + 1)`, i.e. `r < ½ ln 3`.

Formalization in the centred model (the incentre is the centre `0` of the absolute; the general
case follows by the h-motion `mobius I`).  The h-triangle `ABC` has its sides on the h-lines
`hline αᵢ cᵢ`; the incentre `0` is inside the triangle iff the tangent directions `A, B, C` at `0`
of the three vertices are positively dependent (`l₁A + l₂B + l₃C = 0`, `lᵢ > 0`; this replaces the
book's angle sum `2π`).  We prove: any h-disc about `0` of radius `r > 0` which does not meet the
three side lines has `r < ½ ln 3`.  The incircle (tangent to the three sides) is such a disc, so
the inradius is `< ½ ln 3`.  The step "angle at `I` subtended by a side `< 2φ`" of the book is
proved here directly (`line_big_radius`): all points `X` of `hline α c` satisfy
`⟨X, c/α⟩ = (‖X‖²+1)/2 > ‖X‖`, so `X` makes an angle `< φ` with the centre `c/α` of the circle,
where `cos φ = α/‖c‖`. -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate

theorem inner_cplx (x y : ℂ) : inner ℝ x y = x.re * y.re + x.im * y.im := by
  rw [Complex.inner]; simp [Complex.mul_re]; ring

/-- If two points `X, Y` of the disc satisfy `⟨X, Z⟩ = (‖X‖²+1)/2` (they lie on the circle with
centre `Z` orthogonal to the absolute) and subtend an angle `≥ 2π/3` at the origin, then `‖Z‖ > 2`. -/
theorem line_big_radius {Z X Y : ℂ} (hZ : 1 < ‖Z‖) (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) (hX0 : X ≠ 0)
    (hY0 : Y ≠ 0) (hXe : ‖X‖ ^ 2 + 1 = 2 * (X.re * Z.re + X.im * Z.im))
    (hYe : ‖Y‖ ^ 2 + 1 = 2 * (Y.re * Z.re + Y.im * Z.im))
    (hxy : X.re * Y.re + X.im * Y.im ≤ -(1 / 2) * ‖X‖ * ‖Y‖) : 2 < ‖Z‖ := by
  by_contra hle
  push Not at hle
  have hZ0 : 0 < ‖Z‖ := by linarith
  have hpi3 : π / 3 ≤ π := by linarith [Real.pi_pos]
  have cosbound : ∀ W : ℂ, ‖W‖ < 1 → W ≠ 0 → ‖W‖ ^ 2 + 1 = 2 * (W.re * Z.re + W.im * Z.im) →
      InnerProductGeometry.angle W Z < π / 3 := by
    intro W hW hW0 hWe
    have hn : 0 < ‖W‖ := norm_pos_iff.mpr hW0
    apply lt_of_cos_lt (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
      (by linarith [Real.pi_pos]) hpi3
    rw [Real.cos_pi_div_three, InnerProductGeometry.cos_angle, inner_cplx,
      lt_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hle hn.le
    have h2 : 0 < (1 - ‖W‖) ^ 2 := pow_pos (sub_pos.mpr hW) 2
    nlinarith
  have a := cosbound X hX hX0 hXe
  have b := cosbound Y hY hY0 hYe
  have tri := InnerProductGeometry.angle_le_angle_add_angle X Z Y
  rw [InnerProductGeometry.angle_comm Z Y] at tri
  have hlt : InnerProductGeometry.angle X Y < 2 * π / 3 := by linarith
  have hc : Real.cos (2 * π / 3) < Real.cos (InnerProductGeometry.angle X Y) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg _ _)
      (by linarith [Real.pi_pos]) hlt
  have e : Real.cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hn1 : 0 < ‖X‖ := norm_pos_iff.mpr hX0
  have hn2 : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
  have : Real.cos (InnerProductGeometry.angle X Y) ≤ -(1 / 2) := by
    rw [InnerProductGeometry.cos_angle, inner_cplx, div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- Three tangent directions `A, B, C` at the origin that are positively dependent contain a pair
making an angle `≥ 2π/3` (cosine `≤ -1/2`). -/
theorem exists_obtuse_pair {A B C : ℂ} {l1 l2 l3 : ℝ} (h1 : 0 < l1) (h2 : 0 < l2) (h3 : 0 < l3)
    (hs : (l1 : ℂ) * A + l2 * B + l3 * C = 0) :
    (A.re * B.re + A.im * B.im ≤ -(1 / 2) * ‖A‖ * ‖B‖) ∨
    (B.re * C.re + B.im * C.im ≤ -(1 / 2) * ‖B‖ * ‖C‖) ∨
    (C.re * A.re + C.im * A.im ≤ -(1 / 2) * ‖C‖ * ‖A‖) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  have hre : l1 * A.re + l2 * B.re + l3 * C.re = 0 := by
    have := congrArg Complex.re hs; simpa using this
  have him : l1 * A.im + l2 * B.im + l3 * C.im = 0 := by
    have := congrArg Complex.im hs; simpa using this
  have key : (l1 * A.re + l2 * B.re + l3 * C.re) ^ 2 + (l1 * A.im + l2 * B.im + l3 * C.im) ^ 2 = 0 := by
    rw [hre, him]; ring
  have n1 := sq_norm_eq A
  have n2 := sq_norm_eq B
  have n3 := sq_norm_eq C
  have E : l1 ^ 2 * ‖A‖ ^ 2 + l2 ^ 2 * ‖B‖ ^ 2 + l3 ^ 2 * ‖C‖ ^ 2 +
      2 * (l1 * l2) * (A.re * B.re + A.im * B.im) + 2 * (l2 * l3) * (B.re * C.re + B.im * C.im) +
      2 * (l3 * l1) * (C.re * A.re + C.im * A.im) = 0 := by
    linear_combination key + l1 ^ 2 * n1 + l2 ^ 2 * n2 + l3 ^ 2 * n3
  have p12 := mul_lt_mul_of_pos_left c1 (mul_pos h1 h2)
  have p23 := mul_lt_mul_of_pos_left c2 (mul_pos h2 h3)
  have p31 := mul_lt_mul_of_pos_left c3 (mul_pos h3 h1)
  nlinarith [sq_nonneg (l1 * ‖A‖ - l2 * ‖B‖), sq_nonneg (l2 * ‖B‖ - l3 * ‖C‖),
    sq_nonneg (l3 * ‖C‖ - l1 * ‖A‖)]

theorem mem_hline_iff_Z {α : ℝ} {c P : ℂ} (hα : α ≠ 0) :
    P ∈ hline α c ↔ ‖P‖ < 1 ∧
      ‖P‖ ^ 2 + 1 = 2 * (P.re * (c / (α : ℂ)).re + P.im * (c / (α : ℂ)).im) := by
  simp only [hline, Set.mem_ofPred_eq]
  refine and_congr_right (fun _ => ?_)
  have e1 : (c / (α : ℂ)).re = c.re / α := by simp [Complex.div_ofReal_re]
  have e2 : (c / (α : ℂ)).im = c.im / α := by simp [Complex.div_ofReal_im]
  rw [e1, e2, re_conj_mul]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

theorem aux_num {m : ℝ} (hm : 2 < m) :
    Real.sqrt (m ^ 2 - 1) ^ 2 = m ^ 2 - 1 ∧ Real.sqrt (m ^ 2 - 1) < m ∧
      0 < m - Real.sqrt (m ^ 2 - 1) ∧ m - Real.sqrt (m ^ 2 - 1) < 2 - Real.sqrt 3 ∧
      Real.sqrt 3 < 2 ∧ 1 < Real.sqrt 3 := by
  have hR2 : Real.sqrt (m ^ 2 - 1) ^ 2 = m ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hR0 : 0 ≤ Real.sqrt (m ^ 2 - 1) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsR : Real.sqrt 3 < Real.sqrt (m ^ 2 - 1) := Real.sqrt_lt_sqrt (by norm_num) (by nlinarith)
  generalize Real.sqrt (m ^ 2 - 1) = R at *
  generalize Real.sqrt 3 = s at *
  have hs1 : s < 2 := by nlinarith
  have hs1' : 1 < s := by nlinarith
  have hRm : R < m := by nlinarith
  have hq0 : 0 < m - R := by linarith
  have hqR : (m - R) * (m + R) = 1 := by nlinarith
  have hq1 : (m - R) * (2 + s) < 1 := by nlinarith
  refine ⟨hR2, hRm, hq0, ?_, hs1, hs1'⟩
  calc m - R = ((m - R) * (2 + s)) * (2 - s) := by nlinarith
    _ < 1 * (2 - s) := mul_lt_mul_of_pos_right hq1 (by linarith)
    _ = 2 - s := one_mul _

/-- One side: if two vertices `X, Y` lie on the h-line `hline α c`, subtend an angle `≥ 2π/3` at
the centre, and the h-disc about the centre of radius `r > 0` misses the line, then
`r < ½ ln 3`. -/
theorem inradius_line {α : ℝ} {c X Y : ℂ} {r : ℝ} (hr : 0 < r) (h : α ^ 2 < ‖c‖ ^ 2)
    (hX : X ∈ hline α c) (hY : Y ∈ hline α c) (hX0 : X ≠ 0) (hY0 : Y ≠ 0)
    (hxy : X.re * Y.re + X.im * Y.im ≤ -(1 / 2) * ‖X‖ * ‖Y‖)
    (hav : ∀ P ∈ hline α c, ¬ hdist 0 P < r) : r < Real.log 3 / 2 := by
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  have hα : α ≠ 0 := by
    rintro rfl
    have : (0 : ℂ) ∈ hline 0 c := ⟨h00, by simp⟩
    exact hav 0 this (by rw [(hdist_eq_zero_iff h00 h00).mpr rfl]; exact hr)
  have hZ : 1 < ‖c / (α : ℂ)‖ := (one_lt_norm_div hα).mpr h
  obtain ⟨hXn, hXe⟩ := (mem_hline_iff_Z hα).mp hX
  obtain ⟨hYn, hYe⟩ := (mem_hline_iff_Z hα).mp hY
  obtain ⟨Z, hZd⟩ : ∃ Z : ℂ, Z = c / (α : ℂ) := ⟨_, rfl⟩
  rw [← hZd] at hZ hXe hYe
  have hm := line_big_radius hZ hXn hYn hX0 hY0 hXe hYe hxy
  obtain ⟨hR2, hRm, hq0, hq2, hs1, hs1'⟩ := aux_num hm
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hQmem' : ∀ (Q : ℂ), Q = ((1 - Real.sqrt (‖Z‖ ^ 2 - 1) / ‖Z‖ : ℝ) : ℂ) * Z →
      ‖Q‖ = ‖Z‖ - Real.sqrt (‖Z‖ ^ 2 - 1) ∧
      ‖Q‖ ^ 2 + 1 = 2 * (Q.re * Z.re + Q.im * Z.im) := by
    intro Q hQ
    have hmpos : 0 < ‖Z‖ := by linarith
    have hspos : 0 < 1 - Real.sqrt (‖Z‖ ^ 2 - 1) / ‖Z‖ := by
      rw [sub_pos, div_lt_one hmpos]; exact hRm
    have hQn : ‖Q‖ = ‖Z‖ - Real.sqrt (‖Z‖ ^ 2 - 1) := by
      rw [hQ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hspos.le]
      field_simp
    refine ⟨hQn, ?_⟩
    have hZsq : Z.re ^ 2 + Z.im ^ 2 = ‖Z‖ ^ 2 := (sq_norm_eq Z).symm
    have hQre : Q.re = (1 - Real.sqrt (‖Z‖ ^ 2 - 1) / ‖Z‖) * Z.re := by simp [hQ]
    have hQim : Q.im = (1 - Real.sqrt (‖Z‖ ^ 2 - 1) / ‖Z‖) * Z.im := by simp [hQ]
    rw [hQn, hQre, hQim]
    generalize Real.sqrt (‖Z‖ ^ 2 - 1) = R at *
    generalize ‖Z‖ = m at *
    have e : (1 - R / m) * (Z.re ^ 2 + Z.im ^ 2) = m ^ 2 - m * R := by
      rw [hZsq]; field_simp
    nlinarith [e, hR2]
  obtain ⟨hQn, hQe⟩ := hQmem' _ rfl
  have hq3 : ‖(((1 - Real.sqrt (‖Z‖ ^ 2 - 1) / ‖Z‖ : ℝ) : ℂ) * Z)‖ < 1 := by
    rw [hQn]; linarith
  have hQmem : (((1 - Real.sqrt (‖Z‖ ^ 2 - 1) / ‖Z‖ : ℝ) : ℂ) * Z) ∈ hline α c := by
    rw [mem_hline_iff_Z hα, ← hZd]
    exact ⟨hq3, hQe⟩
  have hge := hav _ hQmem
  rw [not_lt, hdist_zero_eq_log hq3, hQn] at hge
  have hq1 : ‖Z‖ - Real.sqrt (‖Z‖ ^ 2 - 1) < 1 := by linarith
  have hlog : Real.log ((1 + (‖Z‖ - Real.sqrt (‖Z‖ ^ 2 - 1))) / (1 - (‖Z‖ - Real.sqrt (‖Z‖ ^ 2 - 1))))
      < Real.log (Real.sqrt 3) := by
    apply Real.log_lt_log (div_pos (by linarith) (by linarith))
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have : Real.log (Real.sqrt 3) = Real.log 3 / 2 := Real.log_sqrt (by norm_num)
  linarith

theorem ne_zero_of_avoid {α : ℝ} {c X : ℂ} {r : ℝ} (hr : 0 < r) (hX : X ∈ hline α c)
    (hav : ∀ P ∈ hline α c, ¬ hdist 0 P < r) : X ≠ 0 := by
  rintro rfl
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  exact hav 0 hX (by rw [(hdist_eq_zero_iff h00 h00).mpr rfl]; exact hr)

/-- Theorem 13.6 (the inradius of every h-triangle is less than `½ ln 3`), centred form.  The
h-triangle `ABC` has its three sides on the h-lines `hline αᵢ cᵢ` (`A, B` on the first, `B, C` on
the second, `C, A` on the third); its incentre is the centre `0` of the absolute, which lies inside
the triangle iff the tangent directions `A, B, C` at `0` are positively dependent
(`l₁ A + l₂ B + l₃ C = 0`, `lᵢ > 0`).  If an h-disc about `0` of h-radius `r > 0` meets none of
the three side lines, then `r < ½ ln 3`.  The incircle (the h-circle about the incentre tangent to
the three sides) is such a disc, so the inradius is `< ½ ln 3`.  The general incentre reduces to
this case by the h-motion `mobius I`, which is not formalized here. -/
@[kb "petrunin2025" "Theorem 13.6, p. 105"]
theorem inradius_lt {A B C : ℂ} {α₁ α₂ α₃ : ℝ} {c₁ c₂ c₃ : ℂ} {l1 l2 l3 r : ℝ}
    (h₁ : α₁ ^ 2 < ‖c₁‖ ^ 2) (h₂ : α₂ ^ 2 < ‖c₂‖ ^ 2) (h₃ : α₃ ^ 2 < ‖c₃‖ ^ 2)
    (hA1 : A ∈ hline α₁ c₁) (hB1 : B ∈ hline α₁ c₁) (hB2 : B ∈ hline α₂ c₂)
    (hC2 : C ∈ hline α₂ c₂) (hC3 : C ∈ hline α₃ c₃) (hA3 : A ∈ hline α₃ c₃)
    (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3) (hs : (l1 : ℂ) * A + l2 * B + l3 * C = 0)
    (hr : 0 < r) (hav1 : ∀ P ∈ hline α₁ c₁, ¬ hdist 0 P < r)
    (hav2 : ∀ P ∈ hline α₂ c₂, ¬ hdist 0 P < r) (hav3 : ∀ P ∈ hline α₃ c₃, ¬ hdist 0 P < r) :
    r < Real.log 3 / 2 := by
  have hA0 := ne_zero_of_avoid hr hA1 hav1
  have hB0 := ne_zero_of_avoid hr hB1 hav1
  have hC0 := ne_zero_of_avoid hr hC2 hav2
  rcases exists_obtuse_pair hl1 hl2 hl3 hs with h | h | h
  · exact inradius_line hr h₁ hA1 hB1 hA0 hB0 h hav1
  · exact inradius_line hr h₂ hB2 hC2 hB0 hC0 h hav2
  · exact inradius_line hr h₃ hC3 hA3 hC0 hA0 h hav3

/-! ### Transport of h-lines along `mobius` (self-contained copy of the computation in `HypLines`,
which cannot be imported together with `HypAngles`) -/

/-- The defining expression of `hline α c`: `z ∈ hline α c` iff `‖z‖ < 1` and `irE α c z = 0`. -/
noncomputable def irE (α : ℝ) (c z : ℂ) : ℝ := α * (‖z‖ ^ 2 + 1) - 2 * (conj c * z).re

theorem mem_hline_irE {α : ℝ} {c z : ℂ} : z ∈ hline α c ↔ ‖z‖ < 1 ∧ irE α c z = 0 := by
  simp only [hline, Set.mem_ofPred_eq]
  refine and_congr_right (fun _ => ?_)
  unfold irE
  constructor <;> intro h <;> linarith

noncomputable def irα (b : ℂ) (α : ℝ) (c : ℂ) : ℝ := α * (1 + ‖b‖ ^ 2) + 2 * (conj c * b).re

noncomputable def irc (b : ℂ) (α : ℝ) (c : ℂ) : ℂ := c + conj c * (b * b) + 2 * (α : ℂ) * b

theorem irE_poly (α : ℝ) (c b w : ℂ) :
    α * (‖w - b‖ ^ 2 + ‖1 - conj b * w‖ ^ 2) -
        2 * (conj c * ((w - b) * conj (1 - conj b * w))).re = irE (irα b α c) (irc b α c) w := by
  unfold irE
  simp only [irα, irc, sq_norm_eq, re_conj_mul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem irE_mobius {α : ℝ} {c b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    irE α c (mobius b w) * ‖1 - conj b * w‖ ^ 2 = irE (irα b α c) (irc b α c) w := by
  have hD := mobius_den_ne hb hw
  set D := 1 - conj b * w with hDdef
  have hz : mobius b w * D = w - b := by unfold mobius; exact div_mul_cancel₀ _ hD
  rw [← irE_poly]
  have hn : ‖mobius b w‖ ^ 2 * ‖D‖ ^ 2 = ‖w - b‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul, hz]
  have e : ((‖D‖ ^ 2 : ℝ) : ℂ) = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : (conj c * mobius b w).re * ‖D‖ ^ 2 = (conj c * ((w - b) * conj D)).re := by
    have : conj c * ((w - b) * conj D) = (conj c * mobius b w) * ((‖D‖ ^ 2 : ℝ) : ℂ) := by
      rw [e, ← hz]; ring
    rw [this, Complex.re_mul_ofReal]
  unfold irE
  linear_combination α * hn - 2 * hre

theorem irα_lt {b : ℂ} {α : ℝ} {c : ℂ} (hb : ‖b‖ < 1) (h : α ^ 2 < ‖c‖ ^ 2) :
    irα b α c ^ 2 < ‖irc b α c‖ ^ 2 := by
  have h1 : ‖irc b α c‖ ^ 2 - irα b α c ^ 2 = (1 - ‖b‖ ^ 2) ^ 2 * (‖c‖ ^ 2 - α ^ 2) := by
    simp only [sq_norm_eq]
    simp only [irα, irc, sq_norm_eq, re_conj_mul, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have h2 : 0 < (1 - ‖b‖ ^ 2) ^ 2 := by have := one_sub_sq_pos hb; positivity
  nlinarith [mul_pos h2 (sub_pos.mpr h)]

theorem mobius_mem_hline_iff' {α : ℝ} {c b w : ℂ} (hb : ‖b‖ < 1) (hw : ‖w‖ < 1) :
    mobius b w ∈ hline α c ↔ w ∈ hline (irα b α c) (irc b α c) := by
  have h := irE_mobius (α := α) (c := c) hb hw
  have hD := norm_den_pos hb hw
  rw [mem_hline_irE, mem_hline_irE]
  constructor
  · rintro ⟨_, h0⟩; exact ⟨hw, by rw [← h, h0, zero_mul]⟩
  · rintro ⟨_, h0⟩
    refine ⟨norm_mobius_lt_one hb hw, ?_⟩
    rw [← h] at h0
    exact (mul_eq_zero.mp h0).resolve_right (by positivity)

theorem transport_line {α : ℝ} {c I A : ℂ} {r : ℝ} (hI : ‖I‖ < 1) (h : α ^ 2 < ‖c‖ ^ 2)
    (hA : A ∈ hline α c) (hav : ∀ X ∈ hline α c, ¬ hdist I X < r) :
    irα (-I) α c ^ 2 < ‖irc (-I) α c‖ ^ 2 ∧
    mobius I A ∈ hline (irα (-I) α c) (irc (-I) α c) ∧
    ∀ P ∈ hline (irα (-I) α c) (irc (-I) α c), ¬ hdist 0 P < r := by
  have hn : ‖(-I)‖ < 1 := by simpa using hI
  refine ⟨irα_lt hn h, ?_, ?_⟩
  · have hm := norm_mobius_lt_one hI hA.1
    exact (mobius_mem_hline_iff' hn hm).mp (by rw [mobius_neg_mobius hI hA.1]; exact hA)
  · intro P hP
    have hP1 := hP.1
    have hX := (mobius_mem_hline_iff' hn hP1).mpr hP
    have e : mobius I (mobius (-I) P) = P := mobius_mobius_neg hI hP1
    have := hav _ hX
    rwa [hdist_eq_mobius hI hX.1, e] at this

/-- Theorem 13.6 for an arbitrary centre `I` of the disc (general form of `inradius_lt`).  The
h-triangle `ABC` has its sides on `hline αᵢ cᵢ`; `I` lies inside it iff the tangent directions
`mobius I A, mobius I B, mobius I C` at `I` (images of the vertices under the h-motion taking `I`
to the centre) are positively dependent.  If the h-disc `{X | hdist I X < r}` (`r > 0`) meets none
of the three side lines, then `r < ½ ln 3`; in particular the inradius is `< ½ ln 3`. -/
@[kb "petrunin2025" "Theorem 13.6, p. 105"]
theorem inradius_lt_general {I A B C : ℂ} {α₁ α₂ α₃ : ℝ} {c₁ c₂ c₃ : ℂ} {l1 l2 l3 r : ℝ}
    (hI : ‖I‖ < 1)
    (h₁ : α₁ ^ 2 < ‖c₁‖ ^ 2) (h₂ : α₂ ^ 2 < ‖c₂‖ ^ 2) (h₃ : α₃ ^ 2 < ‖c₃‖ ^ 2)
    (hA1 : A ∈ hline α₁ c₁) (hB1 : B ∈ hline α₁ c₁) (hB2 : B ∈ hline α₂ c₂)
    (hC2 : C ∈ hline α₂ c₂) (hC3 : C ∈ hline α₃ c₃) (hA3 : A ∈ hline α₃ c₃)
    (hl1 : 0 < l1) (hl2 : 0 < l2) (hl3 : 0 < l3)
    (hs : (l1 : ℂ) * mobius I A + l2 * mobius I B + l3 * mobius I C = 0)
    (hr : 0 < r) (hav1 : ∀ X ∈ hline α₁ c₁, ¬ hdist I X < r)
    (hav2 : ∀ X ∈ hline α₂ c₂, ¬ hdist I X < r) (hav3 : ∀ X ∈ hline α₃ c₃, ¬ hdist I X < r) :
    r < Real.log 3 / 2 := by
  obtain ⟨d1, tA1, v1⟩ := transport_line hI h₁ hA1 hav1
  obtain ⟨-, tB1, -⟩ := transport_line hI h₁ hB1 hav1
  obtain ⟨d2, tB2, v2⟩ := transport_line hI h₂ hB2 hav2
  obtain ⟨-, tC2, -⟩ := transport_line hI h₂ hC2 hav2
  obtain ⟨d3, tC3, v3⟩ := transport_line hI h₃ hC3 hav3
  obtain ⟨-, tA3, -⟩ := transport_line hI h₃ hA3 hav3
  exact inradius_lt d1 d2 d3 tA1 tB1 tB2 tC2 tC3 tA3 hl1 hl2 hl3 hs hr v1 v2 v3

end UndergradKB.Geometry
