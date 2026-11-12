import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import UndergradKB.Common.Attr

/-! # Mobius transformations (rows CX-035, CX-036, CX-037, CX-038, CX-041, CX-042, CX-043)

Mathlib has the action of `GL (Fin 2) K` on `OnePoint K`, but no Mobius function on `ℂ` itself.
We work with the finite-point formulation: `mobius a b c d z = (a z + b)/(c z + d)`, and "the pole"
or "the image is infinity" is expressed by the vanishing of the denominator `c z + d`.  Where a
statement needs the value at the point at infinity, we say so in the docstring and use the
vanishing-denominator condition instead.

Contents: the bridge to the `OnePoint` action, the explicit inverse, the decomposition into
translations, dilations and the inversion, the cross ratio with its uniqueness property, the
three-point transitivity, and the circle-preserving property (via generalized circles
`α|z|² + 2 Re(conj β · z) + γ = 0`). -/

namespace UndergradKB.ComplexAnalysis

open ComplexConjugate

/-! ## Definition and the link to `OnePoint` -/

/-- Beck Definition 3.1.1 (CX-035). The linear fractional map `z ↦ (a z + b)/(c z + d)`
(a Mobius map when `a d - b c ≠ 0`), on the finite points where Lean's total division is
meaningful, i.e. `c z + d ≠ 0`. -/
@[kb "beck2025" "Definition 3.1.1, p. 48"]
noncomputable def mobius (a b c d : ℂ) (z : ℂ) : ℂ := (a * z + b) / (c * z + d)

/-- Beck Definition 3.1.1 (CX-035), link to Mathlib: where the denominator does not vanish,
the `GL₂(ℂ)` action on `OnePoint ℂ` of the matrix `g` at the point `z` is `mobius` of its entries. -/
@[kb "beck2025" "Definition 3.1.1, p. 48"]
theorem glAction_coe_eq_mobius (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    g • (z : OnePoint ℂ) = ((mobius (g 0 0) (g 0 1) (g 1 0) (g 1 1) z : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.smul_some_eq_ite, if_neg hz]
  rfl

/-- Where the denominator vanishes, the `GL₂(ℂ)` action sends the finite point to `∞`. -/
theorem glAction_coe_eq_infty (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 = 0) : g • (z : OnePoint ℂ) = OnePoint.infty := by
  rw [OnePoint.smul_some_eq_ite, if_pos hz]

/-- Composition of linear fractional maps corresponds to the product of matrices. -/
theorem mobius_comp {a b c d a' b' c' d' z : ℂ} (hz : c * z + d ≠ 0)
    (_hw : c' * mobius a b c d z + d' ≠ 0) :
    mobius a' b' c' d' (mobius a b c d z) =
      mobius (a' * a + b' * c) (a' * b + b' * d) (c' * a + d' * c) (c' * b + d' * d) z := by
  have e1 : (c' * a + d' * c) * z + (c' * b + d' * d) = (c' * mobius a b c d z + d') * (c * z + d) := by
    unfold mobius; field_simp; ring
  have e2 : (a' * a + b' * c) * z + (a' * b + b' * d) =
      (a' * mobius a b c d z + b') * (c * z + d) := by
    unfold mobius; field_simp; ring
  unfold mobius at *
  rw [e1, e2]
  rw [mul_div_mul_right _ _ hz]

/-! ## Inverse -/

/-- Beck Proposition 3.1.2 (CX-036), first composition: for `a d - b c ≠ 0`, if `c z + d ≠ 0`
then `-c w + a ≠ 0` for `w = f z`, and `(d w - b)/(-c w + a) = z`. -/
@[kb "beck2025" "Proposition 3.1.2, p. 48"]
theorem mobius_inv_mobius {a b c d z : ℂ} (hdet : a * d - b * c ≠ 0) (hz : c * z + d ≠ 0) :
    -c * mobius a b c d z + a ≠ 0 ∧ mobius d (-b) (-c) a (mobius a b c d z) = z := by
  have hw : -c * mobius a b c d z + a = (a * d - b * c) / (c * z + d) := by
    unfold mobius; field_simp; ring
  have hne : -c * mobius a b c d z + a ≠ 0 := by
    rw [hw]; exact div_ne_zero hdet hz
  refine ⟨hne, ?_⟩
  unfold mobius at *
  have hz2 : d + z * c ≠ 0 := by rw [add_comm, mul_comm]; exact hz
  have hz3 : z * c + d ≠ 0 := by rw [mul_comm]; exact hz
  rw [div_eq_iff hne]
  field_simp
  ring

/-- Beck Proposition 3.1.2 (CX-036), second composition: if `-c w + a ≠ 0`, then with
`z = (d w - b)/(-c w + a)` one has `c z + d ≠ 0` and `(a z + b)/(c z + d) = w`. -/
@[kb "beck2025" "Proposition 3.1.2, p. 48"]
theorem mobius_mobius_inv {a b c d w : ℂ} (hdet : a * d - b * c ≠ 0) (hw : -c * w + a ≠ 0) :
    c * mobius d (-b) (-c) a w + d ≠ 0 ∧ mobius a b c d (mobius d (-b) (-c) a w) = w := by
  have hdet' : d * a - -b * -c ≠ 0 := by
    intro h; apply hdet; linear_combination h
  have := mobius_inv_mobius (a := d) (b := -b) (c := -c) (d := a) (z := w) hdet' hw
  simpa [neg_neg] using this

/-! ## Decomposition into translations, dilations and the inversion -/

/-- Beck Proposition 3.1.4 (CX-037), case `c ≠ 0`: where `c z + d ≠ 0`,
`(a z + b)/(c z + d) = a/c - ((a d - b c)/c²) · 1/(z + d/c)`, i.e. a translation by `d/c`,
then the inversion, then a dilation by `-(a d - b c)/c²`, then a translation by `a/c`. -/
@[kb "beck2025" "Proposition 3.1.4, p. 49"]
theorem mobius_eq_comp {a b c d : ℂ} (hc : c ≠ 0) (hdet : a * d - b * c ≠ 0) {z : ℂ}
    (hz : c * z + d ≠ 0) :
    (-(a * d - b * c) / c ^ 2 ≠ 0) ∧
    mobius a b c d z =
      ((fun w : ℂ => w + a / c) ∘ (fun w : ℂ => (-(a * d - b * c) / c ^ 2) * w) ∘
        (fun w : ℂ => w⁻¹) ∘ (fun w : ℂ => w + d / c)) z := by
  refine ⟨div_ne_zero (neg_ne_zero.mpr hdet) (pow_ne_zero 2 hc), ?_⟩
  have h2 : z + d / c ≠ 0 := by
    intro h; apply hz
    have : c * z + d = c * (z + d / c) := by field_simp
    rw [this, h, mul_zero]
  have hz2 : d + z * c ≠ 0 := by rw [add_comm, mul_comm]; exact hz
  have hz3 : z * c + d ≠ 0 := by rw [mul_comm]; exact hz
  simp only [Function.comp_apply, mobius]
  field_simp
  ring

/-- Beck Proposition 3.1.4 (CX-037), case `c = 0`: the map is affine, `(a/d) z + b/d`
(a dilation followed by a translation). -/
@[kb "beck2025" "Proposition 3.1.4, p. 49"]
theorem mobius_eq_affine {a b d : ℂ} (hdet : a * d - b * 0 ≠ 0) (z : ℂ) :
    a / d ≠ 0 ∧ mobius a b 0 d z = (fun w : ℂ => w + b / d) ((a / d) * z) := by
  have hd : d ≠ 0 := by
    intro h; apply hdet; simp [h]
  have ha : a ≠ 0 := by
    intro h; apply hdet; simp [h]
  refine ⟨div_ne_zero ha hd, ?_⟩
  simp only [mobius, zero_mul, zero_add]
  ring

/-! ## Cross ratio -/

/-- Beck Definition 3.2.8 (CX-041): the cross ratio `[z, z₁, z₂, z₃]`, for distinct finite
`z₁ z₂ z₃`. -/
@[kb "beck2025" "Definition 3.2.8, p. 53"]
noncomputable def crossRatio (z z1 z2 z3 : ℂ) : ℂ :=
  ((z - z1) * (z2 - z3)) / ((z - z3) * (z2 - z1))

/-- Coefficients of the cross ratio as a linear fractional map in `z`. -/
def crossA (_z1 z2 z3 : ℂ) : ℂ := z2 - z3
/-- See `crossA`. -/
def crossB (z1 z2 z3 : ℂ) : ℂ := -(z1 * (z2 - z3))
/-- See `crossA`. -/
def crossC (z1 z2 _z3 : ℂ) : ℂ := z2 - z1
/-- See `crossA`. -/
def crossD (z1 z2 z3 : ℂ) : ℂ := -(z3 * (z2 - z1))

/-- The cross ratio is the linear fractional map with the coefficients `crossA` .. `crossD`. -/
theorem crossRatio_eq_mobius (z z1 z2 z3 : ℂ) :
    crossRatio z z1 z2 z3 =
      mobius (crossA z1 z2 z3) (crossB z1 z2 z3) (crossC z1 z2 z3) (crossD z1 z2 z3) z := by
  unfold crossRatio mobius crossA crossB crossC crossD
  congr 1 <;> ring

theorem cross_det (z1 z2 z3 : ℂ) :
    crossA z1 z2 z3 * crossD z1 z2 z3 - crossB z1 z2 z3 * crossC z1 z2 z3 =
      (z2 - z3) * (z2 - z1) * (z1 - z3) := by
  unfold crossA crossB crossC crossD; ring

/-- Beck Proposition 3.2.10 (CX-042), part 1: the cross ratio is a Mobius map in `z`
(coefficients `crossA`..`crossD`, nonzero determinant for distinct points). -/
@[kb "beck2025" "Proposition 3.2.10, p. 53"]
theorem crossRatio_isMobius {z1 z2 z3 : ℂ} (h12 : z1 ≠ z2) (h13 : z1 ≠ z3) (h23 : z2 ≠ z3) :
    crossA z1 z2 z3 * crossD z1 z2 z3 - crossB z1 z2 z3 * crossC z1 z2 z3 ≠ 0 := by
  rw [cross_det]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h23) (sub_ne_zero.mpr h12.symm))
    (sub_ne_zero.mpr h13)

/-- Beck Proposition 3.2.10 (CX-042), part 2: `z₁ ↦ 0`. -/
@[kb "beck2025" "Proposition 3.2.10, p. 53"]
theorem crossRatio_z1 (z1 z2 z3 : ℂ) : crossRatio z1 z1 z2 z3 = 0 := by
  simp [crossRatio]

/-- Beck Proposition 3.2.10 (CX-042), part 3: `z₂ ↦ 1`. -/
@[kb "beck2025" "Proposition 3.2.10, p. 53"]
theorem crossRatio_z2 {z1 z2 z3 : ℂ} (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) :
    crossRatio z2 z1 z2 z3 = 1 := by
  unfold crossRatio
  have h1 : z2 - z1 ≠ 0 := sub_ne_zero.mpr h12.symm
  have h2 : z2 - z3 ≠ 0 := sub_ne_zero.mpr h23
  field_simp

/-- Beck Proposition 3.2.10 (CX-042), part 4: `z₃` is the pole (the map sends `z₃` to `∞`;
finite-point formulation: the denominator `c z + d` vanishes at `z₃`). -/
@[kb "beck2025" "Proposition 3.2.10, p. 53"]
theorem crossRatio_pole (z1 z2 z3 : ℂ) :
    crossC z1 z2 z3 * z3 + crossD z1 z2 z3 = 0 := by
  unfold crossC crossD; ring

/-- Beck Proposition 3.2.10 (CX-042), uniqueness (finite-point version): a Mobius map `f` with
`f z₁ = 0`, `f z₂ = 1` and denominator vanishing at `z₃` (so `f z₃ = ∞`) coincides with the cross
ratio at every `z ≠ z₃`. -/
@[kb "beck2025" "Proposition 3.2.10, p. 53"]
theorem crossRatio_unique {a b c d z1 z2 z3 : ℂ} (h12 : z1 ≠ z2) (_h23 : z2 ≠ z3)
    (hdet : a * d - b * c ≠ 0)
    (hf1 : mobius a b c d z1 = 0) (h1 : c * z1 + d ≠ 0)
    (hf2 : mobius a b c d z2 = 1) (h2 : c * z2 + d ≠ 0)
    (h3 : c * z3 + d = 0) {z : ℂ} (hz : z ≠ z3) :
    mobius a b c d z = crossRatio z z1 z2 z3 := by
  have e1 : a * z1 + b = 0 := by
    unfold mobius at hf1
    rcases div_eq_zero_iff.mp hf1 with h | h
    · exact h
    · exact absurd h h1
  have e2 : a * z2 + b = c * z2 + d := by
    unfold mobius at hf2
    exact (div_eq_one_iff_eq h2).mp hf2
  have hc : c ≠ 0 := by
    intro hc0
    have hd0 : d = 0 := by simpa [hc0] using h3
    apply hdet; simp [hc0, hd0]
  have hb : b = -(a * z1) := by linear_combination e1
  have hd : d = -(c * z3) := by linear_combination h3
  have key : a * (z2 - z1) = c * (z2 - z3) := by
    rw [hb, hd] at e2; linear_combination e2
  have hz3 : z - z3 ≠ 0 := sub_ne_zero.mpr hz
  have h21 : z2 - z1 ≠ 0 := sub_ne_zero.mpr h12.symm
  have hden : c * z + d ≠ 0 := by
    have : c * z + d = c * (z - z3) := by rw [hd]; ring
    rw [this]; exact mul_ne_zero hc hz3
  unfold mobius crossRatio
  rw [div_eq_div_iff hden (mul_ne_zero hz3 h21)]
  rw [hb, hd]
  linear_combination (z - z1) * (z - z3) * key

/-! ## Three-point transitivity -/

/-- Beck Corollary 3.2.11 (CX-043), existence (finite-point version): for distinct `z₁ z₂ z₃`
and distinct `w₁ w₂ w₃` there is a Mobius map with nonvanishing denominators at the `zᵢ` sending
`zᵢ` to `wᵢ`. -/
@[kb "beck2025" "Corollary 3.2.11, p. 54"]
theorem exists_mobius_three_points {z1 z2 z3 w1 w2 w3 : ℂ}
    (hz12 : z1 ≠ z2) (hz13 : z1 ≠ z3) (hz23 : z2 ≠ z3)
    (hw12 : w1 ≠ w2) (hw13 : w1 ≠ w3) (hw23 : w2 ≠ w3) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧
      (c * z1 + d ≠ 0 ∧ mobius a b c d z1 = w1) ∧
      (c * z2 + d ≠ 0 ∧ mobius a b c d z2 = w2) ∧
      (c * z3 + d ≠ 0 ∧ mobius a b c d z3 = w3) := by
  obtain ⟨a, ha⟩ : ∃ a, a = crossD w1 w2 w3 * crossA z1 z2 z3 - crossB w1 w2 w3 * crossC z1 z2 z3 :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = crossD w1 w2 w3 * crossB z1 z2 z3 - crossB w1 w2 w3 * crossD z1 z2 z3 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = -crossC w1 w2 w3 * crossA z1 z2 z3 + crossA w1 w2 w3 * crossC z1 z2 z3 :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = -crossC w1 w2 w3 * crossB z1 z2 z3 + crossA w1 w2 w3 * crossD z1 z2 z3 :=
    ⟨_, rfl⟩
  have s12 : z2 - z1 ≠ 0 := sub_ne_zero.mpr hz12.symm
  have s13 : z1 - z3 ≠ 0 := sub_ne_zero.mpr hz13
  have s23 : z2 - z3 ≠ 0 := sub_ne_zero.mpr hz23
  have t12 : w2 - w1 ≠ 0 := sub_ne_zero.mpr hw12.symm
  have t13 : w1 - w3 ≠ 0 := sub_ne_zero.mpr hw13
  have t23 : w2 - w3 ≠ 0 := sub_ne_zero.mpr hw23
  have s31 : z3 - z1 ≠ 0 := sub_ne_zero.mpr hz13.symm
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩
  · have : a * d - b * c = ((w2 - w3) * (w2 - w1) * (w1 - w3)) * ((z2 - z3) * (z2 - z1) * (z1 - z3)) := by
      rw [ha, hb, hc, hd]; unfold crossA crossB crossC crossD; ring
    rw [this]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero t23 t12) t13)
      (mul_ne_zero (mul_ne_zero s23 s12) s13)
  · have hden : c * z1 + d = (w2 - w3) * (z2 - z1) * (z1 - z3) := by
      rw [hc, hd]; unfold crossA crossB crossC crossD; ring
    have hne : c * z1 + d ≠ 0 := by rw [hden]; exact mul_ne_zero (mul_ne_zero t23 s12) s13
    refine ⟨hne, ?_⟩
    unfold mobius
    rw [div_eq_iff hne, hden, ha, hb]
    unfold crossA crossB crossC crossD; ring
  · have hden : c * z2 + d = (w1 - w3) * (z2 - z1) * (z2 - z3) := by
      rw [hc, hd]; unfold crossA crossB crossC crossD; ring
    have hne : c * z2 + d ≠ 0 := by rw [hden]; exact mul_ne_zero (mul_ne_zero t13 s12) s23
    refine ⟨hne, ?_⟩
    unfold mobius
    rw [div_eq_iff hne, hden, ha, hb]
    unfold crossA crossB crossC crossD; ring
  · have hden : c * z3 + d = -((w2 - w1) * (z3 - z1) * (z2 - z3)) := by
      rw [hc, hd]; unfold crossA crossB crossC crossD; ring
    have hne : c * z3 + d ≠ 0 := by
      rw [hden]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero t12 s31) s23)
    refine ⟨hne, ?_⟩
    unfold mobius
    rw [div_eq_iff hne, hden, ha, hb]
    unfold crossA crossB crossC crossD; ring

/-- Beck Corollary 3.2.11 (CX-043), uniqueness (finite-point version): two linear fractional
maps agreeing at three distinct points, with nonvanishing denominators there, agree at every point
where both are defined. -/
@[kb "beck2025" "Corollary 3.2.11, p. 54"]
theorem mobius_eq_of_three_points {a b c d a' b' c' d' z1 z2 z3 w1 w2 w3 : ℂ}
    (hz12 : z1 ≠ z2) (hz13 : z1 ≠ z3) (hz23 : z2 ≠ z3)
    (h1 : c * z1 + d ≠ 0) (h1' : c' * z1 + d' ≠ 0)
    (h2 : c * z2 + d ≠ 0) (h2' : c' * z2 + d' ≠ 0)
    (h3 : c * z3 + d ≠ 0) (h3' : c' * z3 + d' ≠ 0)
    (f1 : mobius a b c d z1 = w1) (f1' : mobius a' b' c' d' z1 = w1)
    (f2 : mobius a b c d z2 = w2) (f2' : mobius a' b' c' d' z2 = w2)
    (f3 : mobius a b c d z3 = w3) (f3' : mobius a' b' c' d' z3 = w3)
    {z : ℂ} (hz : c * z + d ≠ 0) (hz' : c' * z + d' ≠ 0) :
    mobius a b c d z = mobius a' b' c' d' z := by
  -- the polynomial (a z + b)(c' z + d') - (a' z + b')(c z + d) of degree ≤ 2 has three roots
  have root : ∀ {x w : ℂ}, c * x + d ≠ 0 → c' * x + d' ≠ 0 → mobius a b c d x = w →
      mobius a' b' c' d' x = w →
      (a * c' - a' * c) * x ^ 2 + (a * d' + b * c' - a' * d - b' * c) * x + (b * d' - b' * d) = 0 := by
    intro x w hx hx' e e'
    unfold mobius at e e'
    rw [div_eq_iff hx] at e
    rw [div_eq_iff hx'] at e'
    linear_combination (c' * x + d') * e - (c * x + d) * e'
  have r1 := root h1 h1' f1 f1'
  have r2 := root h2 h2' f2 f2'
  have r3 := root h3 h3' f3 f3'
  set A := a * c' - a' * c
  set B := a * d' + b * c' - a' * d - b' * c
  set C := b * d' - b' * d
  have s12 : z1 - z2 ≠ 0 := sub_ne_zero.mpr hz12
  have s13 : z1 - z3 ≠ 0 := sub_ne_zero.mpr hz13
  have s23 : z2 - z3 ≠ 0 := sub_ne_zero.mpr hz23
  have q1 : A * (z1 + z2) + B = 0 := by
    have : (z1 - z2) * (A * (z1 + z2) + B) = 0 := by linear_combination r1 - r2
    exact (mul_eq_zero.mp this).resolve_left s12
  have q2 : A * (z1 + z3) + B = 0 := by
    have : (z1 - z3) * (A * (z1 + z3) + B) = 0 := by linear_combination r1 - r3
    exact (mul_eq_zero.mp this).resolve_left s13
  have hA : A = 0 := by
    have : (z2 - z3) * A = 0 := by linear_combination q1 - q2
    exact (mul_eq_zero.mp this).resolve_left s23
  have hB : B = 0 := by rw [hA] at q1; simpa using q1
  have hC : C = 0 := by rw [hA, hB] at r1; simpa using r1
  unfold mobius
  rw [div_eq_div_iff hz hz']
  linear_combination z ^ 2 * hA + z * hB + hC

/-! ## Circles and lines -/

/-- The defining expression of a generalized circle: `α |z|² + 2 Re(conj β · z) + γ`
written with real coordinates. -/
def circE (α : ℝ) (β : ℂ) (γ : ℝ) (z : ℂ) : ℝ :=
  α * (z.re ^ 2 + z.im ^ 2) + 2 * (β.re * z.re + β.im * z.im) + γ

/-- A generalized circle (circle, or line when `α = 0`): the zero set of `circE`; the
nondegeneracy condition is `α γ < |β|²`. -/
def genCircle (α : ℝ) (β : ℂ) (γ : ℝ) : Set ℂ := {z | circE α β γ z = 0}

/-- Nondegeneracy of the parameters of a generalized circle. -/
def GenCircleParam (α : ℝ) (β : ℂ) (γ : ℝ) : Prop := α * γ < β.re ^ 2 + β.im ^ 2

/-- A map `f` transfers generalized circles on the domain `P`: it carries every generalized
circle to a generalized circle, in the sense that membership of `z` and of `f z` agree for `z`
in `P`. -/
def Transfers (P : ℂ → Prop) (f : ℂ → ℂ) : Prop :=
  ∀ α β γ, GenCircleParam α β γ → ∃ α' β' γ', GenCircleParam α' β' γ' ∧
    ∀ z, P z → (z ∈ genCircle α β γ ↔ f z ∈ genCircle α' β' γ')

theorem Transfers.comp {P Q : ℂ → Prop} {f g : ℂ → ℂ} (hf : Transfers P f) (hg : Transfers Q g)
    (hPQ : ∀ z, P z → Q (f z)) : Transfers P (g ∘ f) := by
  intro α β γ h
  obtain ⟨α1, β1, γ1, h1, e1⟩ := hf α β γ h
  obtain ⟨α2, β2, γ2, h2, e2⟩ := hg α1 β1 γ1 h1
  exact ⟨α2, β2, γ2, h2, fun z hz => (e1 z hz).trans (e2 _ (hPQ z hz))⟩

theorem Transfers.mono {P Q : ℂ → Prop} {f : ℂ → ℂ} (hPQ : ∀ z, P z → Q z)
    (hf : Transfers Q f) : Transfers P f := by
  intro α β γ h
  obtain ⟨α1, β1, γ1, h1, e1⟩ := hf α β γ h
  exact ⟨α1, β1, γ1, h1, fun z hz => e1 z (hPQ z hz)⟩

theorem Transfers.congr {P : ℂ → Prop} {f g : ℂ → ℂ} (hfg : ∀ z, P z → f z = g z)
    (hg : Transfers P g) : Transfers P f := by
  intro α β γ h
  obtain ⟨α1, β1, γ1, h1, e1⟩ := hg α β γ h
  exact ⟨α1, β1, γ1, h1, fun z hz => by rw [hfg z hz]; exact e1 z hz⟩

/-- Affine maps `z ↦ a z + b` (`a ≠ 0`) carry generalized circles to generalized circles. -/
theorem transfers_affine {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    Transfers (fun _ => True) (fun z => a * z + b) := by
  intro α β γ h
  have hn : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha
  refine ⟨α, β * a - (α : ℂ) * b,
    α * Complex.normSq b - 2 * ((conj (β * a)) * b).re + γ * Complex.normSq a, ?_, ?_⟩
  · unfold GenCircleParam at *
    have : (β * a - (α : ℂ) * b).re ^ 2 + (β * a - (α : ℂ) * b).im ^ 2 -
        α * (α * Complex.normSq b - 2 * ((conj (β * a)) * b).re + γ * Complex.normSq a) =
        Complex.normSq a * (β.re ^ 2 + β.im ^ 2 - α * γ) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    nlinarith [mul_pos hn (sub_pos.mpr h)]
  · intro z _
    have key : circE α (β * a - (α : ℂ) * b)
        (α * Complex.normSq b - 2 * ((conj (β * a)) * b).re + γ * Complex.normSq a) (a * z + b) =
        Complex.normSq a * circE α β γ z := by
      simp only [circE, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im]
      ring
    simp only [genCircle, Set.mem_ofPred_eq]
    rw [key, mul_eq_zero]
    simp [hn.ne']

/-- The inversion `z ↦ 1/z` carries generalized circles (off the origin) to generalized circles:
`z ∈ G(α, β, γ) ↔ 1/z ∈ G(γ, conj β, α)`. -/
theorem inv_mem_genCircle_iff {α : ℝ} {β : ℂ} {γ : ℝ} {z : ℂ} (hz : z ≠ 0) :
    z⁻¹ ∈ genCircle γ (conj β) α ↔ z ∈ genCircle α β γ := by
  have hs : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hsne : z.re * z.re + z.im * z.im ≠ 0 := by
    rw [Complex.normSq_apply] at hs; exact hs.ne'
  have hs' : z.re ^ 2 + z.im ^ 2 ≠ 0 := by rw [sq, sq]; exact hsne
  have key : circE γ (conj β) α z⁻¹ = circE α β γ z / (z.re ^ 2 + z.im ^ 2) := by
    simp only [circE, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    field_simp
    ring
  simp only [genCircle, Set.mem_ofPred_eq]
  rw [key, div_eq_zero_iff]
  simp [hs']

theorem transfers_inv : Transfers (fun z => z ≠ 0) (fun z => z⁻¹) := by
  intro α β γ h
  refine ⟨γ, conj β, α, ?_, fun z hz => (inv_mem_genCircle_iff hz).symm⟩
  unfold GenCircleParam at *
  simp only [Complex.conj_re, Complex.conj_im, neg_sq]
  linarith [mul_comm α γ]

/-- Beck Theorem 3.1.5 (CX-038): a Mobius map carries generalized circles (circles and lines) to
generalized circles. Finite-point version: on points with `c z + d ≠ 0`, `z` lies on a given
generalized circle iff `f z` lies on a suitable generalized circle (the point at infinity, where
a line closes up, is not tracked). -/
@[kb "beck2025" "Theorem 3.1.5, p. 50"]
theorem mobius_transfers_genCircle {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) :
    Transfers (fun z => c * z + d ≠ 0) (mobius a b c d) := by
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by intro h; apply hdet; simp [h]
    obtain ⟨hne, _⟩ := mobius_eq_affine (b := b) (by simpa using hdet) 0
    refine Transfers.congr (g := fun z => (a / d) * z + b / d) ?_
      ((transfers_affine (a := a / d) (b / d) hne).mono (fun _ _ => trivial))
    intro z _
    simp only [mobius, zero_mul, zero_add]
    ring
  · have hk : (-(a * d - b * c) / c ^ 2) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr hdet) (pow_ne_zero 2 hc)
    have t1 : Transfers (fun z => c * z + d ≠ 0) (fun w : ℂ => w + d / c) :=
      (by simpa using transfers_affine (a := 1) (d / c) one_ne_zero :
        Transfers (fun _ => True) (fun w : ℂ => w + d / c)).mono (fun _ _ => trivial)
    have t3 : Transfers (fun _ => True) (fun w : ℂ => (-(a * d - b * c) / c ^ 2) * w + a / c) :=
      transfers_affine (a / c) hk
    have hP : ∀ z, c * z + d ≠ 0 → z + d / c ≠ 0 := by
      intro z hz h; apply hz
      have : c * z + d = c * (z + d / c) := by field_simp
      rw [this, h, mul_zero]
    have t12 := t1.comp transfers_inv hP
    have t123 := t12.comp t3 (fun _ _ => trivial)
    refine Transfers.congr ?_ t123
    intro z hz
    simpa [Function.comp_def] using (mobius_eq_comp hc hdet hz).2

end UndergradKB.ComplexAnalysis
