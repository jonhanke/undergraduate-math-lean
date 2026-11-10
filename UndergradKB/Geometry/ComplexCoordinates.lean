import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Inversion.Basic
import UndergradKB.Common.Attr

/-! # Complex coordinates (Petrunin, chapter 18)

Points of the Euclidean plane are complex numbers `ℂ`. We prove Ptolemy's inequality via the complex
identity (Exercise 18.2), the angle formula `∡ V Z W = arg ((w - z) / (v - z))` (formula 6), the
inscribed-quadrangle criterion by the reality of the cross-ratio (Theorem 18.5), the description of
`z ↦ 1/z` as inversion in the unit circle followed by conjugation (Section 18H), the decomposition of
fractional linear maps into elementary transformations (Proposition 18.12), the fact that they map
circlines to circlines (Corollary 18.13) and the behaviour of the cross-ratio under inversion
(Theorem 18.17).

The plane `ℂ` is oriented by `Complex.orientation`. A *circline* (circle or line) is encoded by the
equation `a * ‖z‖^2 + Re (conj w * z) + c = 0` with real `a`, `c` and `4 a c < ‖w‖^2`; the case `a = 0`
gives lines and `a ≠ 0` gives circles. -/

namespace UndergradKB.Geometry

open EuclideanGeometry ComplexConjugate

namespace ComplexCoordinates

/-- The standard orientation of `ℂ`. -/
noncomputable local instance instOrientedComplex : Module.Oriented ℝ ℂ (Fin 2) := ⟨Complex.orientation⟩

local instance instFactFinrankComplex : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

/-- Ptolemy's inequality for four points of `ℂ` (Petrunin, Exercise 18.2). The proof uses the identity
`(a - c) * (b - d) = (a - b) * (c - d) + (b - c) * (a - d)` (the book's identity with the origin at
`d`) and the triangle inequality. -/
@[kb "petrunin2025" "Exercise 18.2, p. 148"]
theorem ptolemy_inequality (a b c d : ℂ) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by
  simp only [Complex.dist_eq]
  have h : (a - c) * (b - d) = (a - b) * (c - d) + (b - c) * (a - d) := by ring
  calc ‖a - c‖ * ‖b - d‖ = ‖(a - c) * (b - d)‖ := (norm_mul _ _).symm
    _ = ‖(a - b) * (c - d) + (b - c) * (a - d)‖ := by rw [h]
    _ ≤ ‖(a - b) * (c - d)‖ + ‖(b - c) * (a - d)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]

/-- The signed angle `∡ V Z W` of points of `ℂ` is the argument of `(w - z) / (v - z)`
(Petrunin, formula 6 on p. 149), for `v, w ≠ z`. -/
@[kb "petrunin2025" "Formula 6, p. 149"]
theorem oangle_eq_arg_div {v z w : ℂ} (hv : v ≠ z) (hw : w ≠ z) :
    ∡ v z w = (Complex.arg ((w - z) / (v - z)) : Real.Angle) := by
  have hv' : v - z ≠ 0 := sub_ne_zero.mpr hv
  have hw' : w - z ≠ 0 := sub_ne_zero.mpr hw
  show Complex.orientation.oangle (v -ᵥ z) (w -ᵥ z) = _
  rw [vsub_eq_sub, vsub_eq_sub, Complex.oangle,
    Complex.arg_div_coe_angle hw' hv', Complex.arg_mul_coe_angle ((map_ne_zero _).2 hv') hw',
    Complex.arg_conj_coe_angle]
  abel

/-- The complex cross-ratio `(u, w; v, z) = (v - u) (w - z) / ((v - w) (z - u))` of Petrunin's first
definition (p. 150). -/
noncomputable def crossRatio₁ (u w v z : ℂ) : ℂ := (v - u) * (w - z) / ((v - w) * (z - u))

/-- The complex cross-ratio `(u, v; w, z) = (u - w) (v - z) / ((v - w) (u - z))` of Petrunin's second
definition (Section 18I, p. 154). -/
noncomputable def crossRatio (u v w z : ℂ) : ℂ := (u - w) * (v - z) / ((v - w) * (u - z))

/-- A nonzero complex number is real iff twice its argument is `0` modulo `2π`
(Petrunin, Exercise 18.6). -/
theorem im_eq_zero_iff_two_zsmul_arg {x : ℂ} :
    x.im = 0 ↔ (2 : ℤ) • (Complex.arg x : Real.Angle) = 0 := by
  rw [Real.Angle.two_zsmul_eq_zero_iff]
  constructor
  · intro h
    rcases le_or_gt 0 x.re with h0 | h0
    · left
      rw [Complex.arg_eq_zero_iff.2 ⟨h0, h⟩]; simp
    · right
      rw [Complex.arg_eq_pi_iff.2 ⟨h0, h⟩]
  · intro h
    rcases h with h | h
    · have : Complex.arg x = 0 := by
        have := Complex.arg_coe_angle_eq_iff.1 (h.trans (by simp : ((0 : ℝ) : Real.Angle) = ((Complex.arg 1 : ℝ) : Real.Angle)))
        simpa using this
      exact (Complex.arg_eq_zero_iff.1 this).2
    · have : Complex.arg x = Real.pi := by
        have := Complex.arg_coe_angle_eq_iff.1 (h.trans (by simp : ((Real.pi : ℝ) : Real.Angle) = ((Complex.arg (-1) : ℝ) : Real.Angle)))
        simpa using this
      exact (Complex.arg_eq_pi_iff.1 this).2

/-- Equality of doubled oriented angles at `v` and `z` is the reality of the ratio
`(v-u)(z-w) / ((v-w)(z-u))`. -/
theorem two_zsmul_oangle_eq_iff_im {u v w z : ℂ} (huv : u ≠ v) (huz : u ≠ z)
    (hvw : v ≠ w) (hwz : w ≠ z) :
    (2 : ℤ) • ∡ u v w = (2 : ℤ) • ∡ u z w ↔ ((v - u) * (z - w) / ((v - w) * (z - u))).im = 0 := by
  have h1 : (v - u) ≠ 0 := sub_ne_zero.2 huv.symm
  have h2 : (w - v) ≠ 0 := sub_ne_zero.2 hvw.symm
  have h3 : (w - z) ≠ 0 := sub_ne_zero.2 hwz
  have h4 : (u - z) ≠ 0 := sub_ne_zero.2 huz
  have h5 : (u - v) ≠ 0 := sub_ne_zero.2 huv
  have h6 : (z - u) ≠ 0 := sub_ne_zero.2 huz.symm
  have h7 : (v - w) ≠ 0 := sub_ne_zero.2 hvw
  have h8 : (z - w) ≠ 0 := sub_ne_zero.2 hwz.symm
  set A := (w - v) / (u - v) with hA
  set B := (w - z) / (u - z) with hB
  have hAne : A ≠ 0 := div_ne_zero h2 h5
  have hBne : B ≠ 0 := div_ne_zero h3 h4
  have hR : (v - u) * (z - w) / ((v - w) * (z - u)) = B / A := by
    rw [hA, hB]; field_simp
    ring
  rw [hR, im_eq_zero_iff_two_zsmul_arg,
    Complex.arg_div_coe_angle hBne hAne,
    oangle_eq_arg_div huv hvw.symm, oangle_eq_arg_div huz hwz,
    Complex.arg_div_coe_angle h2 h5, Complex.arg_div_coe_angle h3 h4]
  simp only [smul_sub]
  rw [eq_comm, ← sub_eq_zero (a := _ - _)]

/-- **Theorem 18.5** (Petrunin, p. 150; complex coordinates): four distinct points `u, v, w, z` of `ℂ`
are inscribed (lie on a circle, or on a line, the degenerate circline) iff the cross-ratio
`(v - u) (z - w) / ((v - w) (z - u))` is real. -/
@[kb "petrunin2025" "Theorem 18.5, p. 150"]
theorem inscribed_iff_im_eq_zero {u v w z : ℂ} (huv : u ≠ v) (_huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (_hvz : v ≠ z) (hwz : w ≠ z) :
    (Cospherical ({u, v, w, z} : Set ℂ) ∨ Collinear ℝ ({u, v, w, z} : Set ℂ)) ↔
      ((v - u) * (z - w) / ((v - w) * (z - u))).im = 0 := by
  rw [← two_zsmul_oangle_eq_iff_im huv huz hvw hwz]
  have hset : ({u, v, w, z} : Set ℂ) = {u, v, z, w} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  constructor
  · rintro (h | h)
    · exact (Cospherical.two_zsmul_oangle_eq h huv.symm hvw huz.symm hwz.symm)
    · have c1 : Collinear ℝ ({u, v, w} : Set ℂ) := h.subset (by
        intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
      have c2 : Collinear ℝ ({u, z, w} : Set ℂ) := h.subset (by
        intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
      have e1 := (Real.Angle.two_zsmul_eq_zero_iff).2 (oangle_eq_zero_or_eq_pi_iff_collinear.2 c1)
      have e2 := (Real.Angle.two_zsmul_eq_zero_iff).2 (oangle_eq_zero_or_eq_pi_iff_collinear.2 c2)
      rw [e1, e2]
  · intro h
    exact cospherical_or_collinear_of_two_zsmul_oangle_eq h

/-- Inversion in the unit circle centred at `0` is `z ↦ 1 / conj z` on `ℂ`. -/
theorem inversion_zero_one (z : ℂ) : inversion (0 : ℂ) 1 z = (conj z)⁻¹ := by
  rw [inversion, Complex.inv_def]
  simp [Complex.normSq_eq_norm_sq, Complex.real_smul]
  exact mul_comm _ _

/-- The map `z ↦ 1 / z` is the inversion in the unit circle followed by the complex conjugation
(reflection in the real line) (Petrunin, Section 18H, pp. 152-153). -/
@[kb "petrunin2025" "Section 18H, p. 152"]
theorem inv_eq_conj_inversion (z : ℂ) : z⁻¹ = conj (inversion (0 : ℂ) 1 z) := by
  rw [inversion_zero_one, map_inv₀, Complex.conj_conj]

/-- The two orders of composition agree: `1 / z` is also the inversion of `conj z`. -/
theorem inv_eq_inversion_conj (z : ℂ) : z⁻¹ = inversion (0 : ℂ) 1 (conj z) := by
  rw [inversion_zero_one, Complex.conj_conj]

/-- The cross-ratio is invariant under `z ↦ 1 / z`. -/
theorem crossRatio_inv {u v w z : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (hz : z ≠ 0)
    (huz : u ≠ z) (hvw : v ≠ w) :
    crossRatio u⁻¹ v⁻¹ w⁻¹ z⁻¹ = crossRatio u v w z := by
  have h1 : u - z ≠ 0 := sub_ne_zero.2 huz
  have h2 : v - w ≠ 0 := sub_ne_zero.2 hvw
  unfold crossRatio
  rw [inv_sub_inv hu hw, inv_sub_inv hv hz, inv_sub_inv hv hw, inv_sub_inv hu hz]
  field_simp
  ring

/-- **Theorem 18.17** (Petrunin, p. 155): inversion in the unit circle sends the complex cross-ratio
of four points to its complex conjugate. (The book writes equality; with the inversion as a map of
the plane the correct statement is up to conjugation, i.e. the cross-ratio is preserved up to the
reflection in the real line, as the book's proof via moduli and angles shows; for the cross-ratios of
real value the two agree.) The points are nonzero with `u ≠ z`, `v ≠ w`. -/
@[kb "petrunin2025" "Theorem 18.17, p. 155"]
theorem crossRatio_inversion {u v w z : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (hz : z ≠ 0)
    (huz : u ≠ z) (hvw : v ≠ w) :
    crossRatio (inversion (0 : ℂ) 1 u) (inversion (0 : ℂ) 1 v) (inversion (0 : ℂ) 1 w)
      (inversion (0 : ℂ) 1 z) = conj (crossRatio u v w z) := by
  simp only [inversion_zero_one]
  rw [crossRatio_inv ((map_ne_zero _).2 hu) ((map_ne_zero _).2 hv) ((map_ne_zero _).2 hw)
    ((map_ne_zero _).2 hz) (fun h => huz ((starRingEnd ℂ).injective h)) (fun h => hvw ((starRingEnd ℂ).injective h))]
  simp [crossRatio]

/-! ### Circlines and fractional linear maps -/

/-- The circline (circle or line) `a ‖z‖² + Re (conj w * z) + c = 0` of `ℂ`; it is a genuine circle
or line when `4 a c < ‖w‖²` (see `IsCircline`). -/
def circline (a : ℝ) (w : ℂ) (c : ℝ) : Set ℂ := {z | a * ‖z‖ ^ 2 + (conj w * z).re + c = 0}

/-- A circline of `ℂ`: a circle (`a ≠ 0`) or a line (`a = 0`), given by a nondegenerate equation. -/
def IsCircline (S : Set ℂ) : Prop :=
  ∃ (a c : ℝ) (w : ℂ), 4 * a * c < ‖w‖ ^ 2 ∧ S = circline a w c

theorem mem_circline_iff {a c : ℝ} {w z : ℂ} :
    z ∈ circline a w c ↔
      a * (z.re ^ 2 + z.im ^ 2) + (w.re * z.re + w.im * z.im) + c = 0 := by
  simp only [circline, Set.mem_setOf_eq, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  constructor <;> intro h <;> linarith

theorem image_translate (a c : ℝ) (w : ℂ) (t : ℂ) :
    (fun z => z + t) '' circline a w c =
      circline a (w - ((2 * a : ℝ) : ℂ) * t) (c + a * ‖t‖ ^ 2 - (conj w * t).re) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_circline_iff] at hx ⊢
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply,
      Complex.conj_re, Complex.conj_im]
    linear_combination hx
  · intro hy
    refine ⟨y - t, ?_, by simp⟩
    rw [mem_circline_iff] at hy ⊢
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply,
      Complex.conj_re, Complex.conj_im] at hy ⊢
    linear_combination hy

theorem image_mul {m : ℂ} (hm : m ≠ 0) (a c : ℝ) (w : ℂ) :
    (fun z => m * z) '' circline a w c = circline a (w * m) (c * ‖m‖ ^ 2) := by
  have hm2 : 0 < ‖m‖ ^ 2 := by positivity
  have key : ∀ x : ℂ, m * x ∈ circline a (w * m) (c * ‖m‖ ^ 2) ↔ x ∈ circline a w c := by
    intro x
    have e : conj (w * m) * (m * x) = ((‖m‖ ^ 2 : ℝ) : ℂ) * (conj w * x) := by
      rw [map_mul, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      push_cast; ring
    simp only [circline, Set.mem_setOf_eq, norm_mul, e, Complex.re_ofReal_mul]
    constructor
    · intro h
      have : ‖m‖ ^ 2 * (a * ‖x‖ ^ 2 + (conj w * x).re + c) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hm2.ne'
      · exact h0
    · intro h
      linear_combination ‖m‖ ^ 2 * h
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine ⟨m⁻¹ * y, ?_, by simp [mul_inv_cancel_left₀ hm]⟩
    rw [← key, mul_inv_cancel_left₀ hm]
    exact hy

theorem inv_mem_circline_iff {a c : ℝ} {w x : ℂ} (hx : x ≠ 0) :
    x⁻¹ ∈ circline c (conj w) a ↔ x ∈ circline a w c := by
  have hN : x.re * x.re + x.im * x.im ≠ 0 := by
    have : 0 < Complex.normSq x := Complex.normSq_pos.2 hx
    rw [Complex.normSq_apply] at this
    exact this.ne'
  rw [mem_circline_iff, mem_circline_iff]
  simp only [Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    neg_neg]
  have e : c * ((x.re / (x.re * x.re + x.im * x.im)) ^ 2 +
        (-x.im / (x.re * x.re + x.im * x.im)) ^ 2) +
      (w.re * (x.re / (x.re * x.re + x.im * x.im)) +
        -w.im * (-x.im / (x.re * x.re + x.im * x.im))) + a =
      (a * (x.re ^ 2 + x.im ^ 2) + (w.re * x.re + w.im * x.im) + c) /
        (x.re * x.re + x.im * x.im) := by
    have hN2 : x.re ^ 2 + x.im ^ 2 ≠ 0 := by
      intro h; apply hN; linarith
    field_simp
    ring
  rw [e, div_eq_zero_iff]
  simp [hN]

theorem image_inv (a c : ℝ) (w : ℂ) :
    (fun z : ℂ => z⁻¹) '' (circline a w c \ {0}) = circline c (conj w) a \ {0} := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
    exact ⟨(inv_mem_circline_iff hx0).2 hx, by simpa using hx0⟩
  · rintro ⟨hy, hy0⟩
    have hy0' : y ≠ 0 := hy0
    refine ⟨y⁻¹, ⟨?_, by simpa using hy0'⟩, inv_inv y⟩
    exact (inv_mem_circline_iff (inv_ne_zero hy0')).1 (by rwa [inv_inv])

theorem IsCircline.translate {S : Set ℂ} (hS : IsCircline S) (t : ℂ) :
    IsCircline ((fun z => z + t) '' S) := by
  obtain ⟨a, c, w, h, rfl⟩ := hS
  refine ⟨a, _, _, ?_, image_translate a c w t⟩
  have : ‖w - ((2 * a : ℝ) : ℂ) * t‖ ^ 2 - 4 * a * (c + a * ‖t‖ ^ 2 - (conj w * t).re) =
      ‖w‖ ^ 2 - 4 * a * c := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    push_cast
    ring
  linarith

theorem IsCircline.mul {S : Set ℂ} (hS : IsCircline S) {m : ℂ} (hm : m ≠ 0) :
    IsCircline ((fun z => m * z) '' S) := by
  obtain ⟨a, c, w, h, rfl⟩ := hS
  refine ⟨a, _, _, ?_, image_mul hm a c w⟩
  have hm2 : 0 < ‖m‖ ^ 2 := by positivity
  rw [norm_mul, mul_pow]
  nlinarith

theorem IsCircline.inv_diff {S : Set ℂ} (hS : IsCircline S) :
    ∃ S', IsCircline S' ∧ (fun z : ℂ => z⁻¹) '' (S \ {0}) = S' \ {0} := by
  obtain ⟨a, c, w, h, rfl⟩ := hS
  refine ⟨_, ⟨c, a, conj w, ?_, rfl⟩, image_inv a c w⟩
  rw [Complex.norm_conj]
  linarith

theorem IsCircline.translate_diff {S : Set ℂ} (hS : IsCircline S) (t p : ℂ) :
    ∃ S', IsCircline S' ∧ (fun z => z + t) '' (S \ {p}) = S' \ {p + t} := by
  refine ⟨_, hS.translate t, ?_⟩
  rw [Set.image_sdiff (add_left_injective t), Set.image_singleton]

theorem IsCircline.mul_diff {S : Set ℂ} (hS : IsCircline S) {m : ℂ} (hm : m ≠ 0) (p : ℂ) :
    ∃ S', IsCircline S' ∧ (fun z => m * z) '' (S \ {p}) = S' \ {m * p} := by
  refine ⟨_, hS.mul hm, ?_⟩
  rw [Set.image_sdiff (mul_right_injective₀ hm), Set.image_singleton]

/-- Decomposition of a fractional linear map with `c ≠ 0` into elementary transformations
(Petrunin, Proposition 18.12, `f = f₄ ∘ f₃ ∘ f₂ ∘ f₁`, formula 7), at all points that are not the
pole `-d/c`:  `z ↦ z + d/c`, `z ↦ 1/z`, `z ↦ -(ad-bc)/c² · z`, `z ↦ z + a/c`. -/
@[kb "petrunin2025" "Proposition 18.12, p. 153"]
theorem mobius_eq_comp {a b c d : ℂ} (hc : c ≠ 0) {z : ℂ} (hz : c * z + d ≠ 0) :
    (a * z + b) / (c * z + d) =
      (fun y => y + a / c) ((fun y => (-((a * d - b * c) / c ^ 2)) * y)
        ((fun y : ℂ => y⁻¹) ((fun y => y + d / c) z))) := by
  have : z + d / c ≠ 0 := by
    intro h
    apply hz
    have : c * (z + d / c) = 0 := by rw [h, mul_zero]
    rw [mul_add, mul_div_cancel₀ _ hc] at this
    exact this
  have hz2 : z * c + d ≠ 0 := by rwa [mul_comm]
  simp only
  field_simp
  ring

/-- Decomposition for `c = 0` (Proposition 18.12): `z ↦ (a z + b)/d` is `z ↦ a/d · z` followed by
`z ↦ z + b/d`. -/
@[kb "petrunin2025" "Proposition 18.12, p. 153"]
theorem mobius_eq_comp_of_c_eq_zero {a b d : ℂ} (hd : d ≠ 0) (z : ℂ) :
    (a * z + b) / (0 * z + d) = (fun y => y + b / d) ((fun y => (a / d) * y) z) := by
  simp only [zero_mul, zero_add]
  field_simp

/-- **Corollary 18.13** (Petrunin, p. 154), case `c ≠ 0`: a fractional linear map `(az+b)/(cz+d)`
(`ad - bc ≠ 0`) sends a circline minus the pole `-d/c` onto a circline minus the point `a/c`
(the images of the pole and of `∞` being `∞` and `a/c` on the extended plane `Ĉ`). -/
@[kb "petrunin2025" "Corollary 18.13, p. 154"]
theorem IsCircline.mobius_image {S : Set ℂ} (hS : IsCircline S) {a b c d : ℂ} (hc : c ≠ 0)
    (hdet : a * d - b * c ≠ 0) :
    ∃ S', IsCircline S' ∧
      (fun z => (a * z + b) / (c * z + d)) '' (S \ {-d / c}) = S' \ {a / c} := by
  obtain ⟨S1, h1, e1⟩ := hS.translate_diff (d / c) (-d / c)
  obtain ⟨S2, h2, e2⟩ := h1.inv_diff
  have hm : -((a * d - b * c) / c ^ 2) ≠ 0 := by
    simpa [hc] using hdet
  obtain ⟨S3, h3, e3⟩ := h2.mul_diff hm 0
  obtain ⟨S4, h4, e4⟩ := h3.translate_diff (a / c) (-((a * d - b * c) / c ^ 2) * 0)
  refine ⟨S4, h4, ?_⟩
  have hp : -d / c + d / c = 0 := by ring
  have hq : -((a * d - b * c) / c ^ 2) * 0 + a / c = a / c := by ring
  rw [hq] at e4
  rw [hp] at e1
  rw [Set.image_congr (g := fun y => (fun y => y + a / c) ((fun y => (-((a * d - b * c) / c ^ 2)) * y)
      ((fun y : ℂ => y⁻¹) ((fun y => y + d / c) y)))), ← e4]
  · rw [← e3, ← e2, ← e1]
    simp only [Set.image_image]
  · intro z hz
    apply mobius_eq_comp hc
    intro h
    apply hz.2
    simp only [Set.mem_singleton_iff]
    field_simp
    linear_combination h

/-- **Corollary 18.13**, case `c = 0`: `z ↦ (az+b)/d` maps a circline onto a circline. -/
@[kb "petrunin2025" "Corollary 18.13, p. 154"]
theorem IsCircline.mobius_image_of_c_eq_zero {S : Set ℂ} (hS : IsCircline S) {a b d : ℂ}
    (hd : d ≠ 0) (ha : a ≠ 0) :
    ∃ S', IsCircline S' ∧ (fun z => (a * z + b) / (0 * z + d)) '' S = S' := by
  refine ⟨_, (hS.mul (div_ne_zero ha hd)).translate (b / d), ?_⟩
  rw [Set.image_image]
  exact Set.image_congr fun z _ => mobius_eq_comp_of_c_eq_zero hd z

end ComplexCoordinates

end UndergradKB.Geometry
