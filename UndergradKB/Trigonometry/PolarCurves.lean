import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Trigonometry.Reciprocal

/-! # Graphs of polar equations (OpenStax §10.3, §10.4)

The plane is `ℂ`; the point with polar coordinates `(r, θ)` is `r (cos θ + i sin θ)`, negative `r` allowed (the
books' convention). The graph of a polar equation, given as a relation `F r θ`, is the set of points having
some pair of polar coordinates that satisfies it (`polarGraph`; a small bridging definition, Mathlib has no
polar equations).

* `polarGraph_symm_polarAxis`, `polarGraph_symm_line_pi_div_two`, `polarGraph_symm_pole`: the symmetry tests
  of OpenStax §10.4 (sufficient conditions);
* `polarGraph_cos_eq_sphere`, `polarGraph_sin_eq_sphere`: `r = a cos θ` and `r = a sin θ` are circles of
  diameter `|a|` through the pole;
* `polarGraph_sec_eq`, `polarGraph_csc_eq`: `r = a sec θ` and `r = a csc θ` are the lines `x = a`, `y = a`;
* `lemniscate_symmetries`: the symmetries of the lemniscates `r² = a² cos 2θ` and `r² = a² sin 2θ`.
-/

namespace UndergradKB.Trigonometry

open Complex ComplexConjugate

/-- The point with polar coordinates `(r, θ)`. -/
noncomputable def polarPoint (r θ : ℝ) : ℂ := r * (Real.cos θ + Real.sin θ * I)

/-- The graph of a polar equation `F r θ`: the points having polar coordinates satisfying `F`. -/
def polarGraph (F : ℝ → ℝ → Prop) : Set ℂ := {z | ∃ r θ, F r θ ∧ z = polarPoint r θ}

lemma polarPoint_re (r θ : ℝ) : (polarPoint r θ).re = r * Real.cos θ := by
  simp only [polarPoint, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im]; ring

lemma polarPoint_im (r θ : ℝ) : (polarPoint r θ).im = r * Real.sin θ := by
  simp only [polarPoint, mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im]; ring

/-- Every complex number is `polarPoint ‖z‖ (arg z)`. -/
lemma eq_polarPoint_norm_arg (z : ℂ) : z = polarPoint ‖z‖ (arg z) := by
  rw [polarPoint, Complex.ofReal_cos, Complex.ofReal_sin]
  exact (norm_mul_cos_add_sin_mul_I z).symm

lemma conj_polarPoint (r θ : ℝ) : conj (polarPoint r θ) = polarPoint r (-θ) := by
  apply Complex.ext <;> simp [polarPoint_re, polarPoint_im, conj_re, conj_im]

lemma neg_polarPoint (r θ : ℝ) : -polarPoint r θ = polarPoint (-r) θ := by
  simp [polarPoint]

lemma polarPoint_pi_sub (r θ : ℝ) : polarPoint (-r) (Real.pi - θ) = polarPoint r (-θ) := by
  apply Complex.ext <;> simp [polarPoint_re, polarPoint_im, Real.cos_pi_sub, Real.sin_pi_sub]

/-- **Symmetry about the polar axis** (OpenStax §10.4): if replacing `(r, θ)` by `(r, -θ)`, or by
`(-r, π - θ)`, preserves the equation, the graph is symmetric about the polar axis (closed under complex
conjugation). (TR-134) -/
@[kb "openstaxalgtrig2e" "§10.4 Symmetry tests, p. 925"]
theorem polarGraph_symm_polarAxis {F : ℝ → ℝ → Prop}
    (h : (∀ r θ, F r θ → F r (-θ)) ∨ ∀ r θ, F r θ → F (-r) (Real.pi - θ)) :
    ∀ z ∈ polarGraph F, conj z ∈ polarGraph F := by
  rintro _ ⟨r, θ, hF, rfl⟩
  rcases h with h | h
  · exact ⟨r, -θ, h r θ hF, conj_polarPoint r θ⟩
  · exact ⟨-r, Real.pi - θ, h r θ hF, by rw [conj_polarPoint, polarPoint_pi_sub]⟩

/-- **Symmetry about the line `θ = π/2`** (OpenStax §10.4): if replacing `(r, θ)` by `(-r, -θ)`, or by
`(r, π - θ)`, preserves the equation, the graph is symmetric about the line `θ = π/2` (closed under
`z ↦ -conj z`). (TR-133) -/
@[kb "openstaxalgtrig2e" "§10.4 Symmetry tests, p. 925"]
theorem polarGraph_symm_line_pi_div_two {F : ℝ → ℝ → Prop}
    (h : (∀ r θ, F r θ → F (-r) (-θ)) ∨ ∀ r θ, F r θ → F r (Real.pi - θ)) :
    ∀ z ∈ polarGraph F, -conj z ∈ polarGraph F := by
  rintro _ ⟨r, θ, hF, rfl⟩
  rcases h with h | h
  · exact ⟨-r, -θ, h r θ hF, by rw [conj_polarPoint, neg_polarPoint]⟩
  · refine ⟨r, Real.pi - θ, h r θ hF, ?_⟩
    rw [conj_polarPoint, neg_polarPoint, ← polarPoint_pi_sub, neg_neg]

/-- **Symmetry about the pole** (OpenStax §10.4): if replacing `(r, θ)` by `(-r, θ)` preserves the equation,
the graph is symmetric about the pole (closed under `z ↦ -z`). (TR-135) -/
@[kb "openstaxalgtrig2e" "§10.4 Symmetry tests, p. 925"]
theorem polarGraph_symm_pole {F : ℝ → ℝ → Prop} (h : ∀ r θ, F r θ → F (-r) θ) :
    ∀ z ∈ polarGraph F, -z ∈ polarGraph F := by
  rintro _ ⟨r, θ, hF, rfl⟩
  exact ⟨-r, θ, h r θ hF, neg_polarPoint r θ⟩

/-- **The circle `r = a cos θ`**: the graph is the circle of centre `a/2` (on the polar axis) and radius
`|a|/2`, which passes through the pole. (TR-137) -/
@[kb "openstaxalgtrig2e" "§10.4 Circles r = a cos θ, r = a sin θ, p. 929"]
theorem polarGraph_cos_eq_sphere (a : ℝ) :
    polarGraph (fun r θ => r = a * Real.cos θ) = Metric.sphere ((a / 2 : ℝ) : ℂ) (|a| / 2) := by
  ext z
  rw [mem_sphere_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) (by positivity), Complex.sq_norm,
    Complex.normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero, div_pow, sq_abs]
  constructor
  · rintro ⟨r, θ, rfl, rfl⟩
    rw [polarPoint_re, polarPoint_im]
    linear_combination (a ^ 2 * Real.cos θ ^ 2) * Real.sin_sq_add_cos_sq θ
  · intro hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨0, Real.pi / 2, by simp, by simp [polarPoint]⟩
    · refine ⟨‖z‖, arg z, ?_, eq_polarPoint_norm_arg z⟩
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
      show ‖z‖ = a * Real.cos (arg z)
      rw [cos_arg hz0, mul_div_assoc', eq_div_iff hn.ne', ← sq, Complex.sq_norm,
        Complex.normSq_apply]
      linear_combination hz

/-- **The circle `r = a sin θ`**: the graph is the circle of centre `ia/2` and radius `|a|/2`. (TR-137) -/
theorem polarGraph_sin_eq_sphere (a : ℝ) :
    polarGraph (fun r θ => r = a * Real.sin θ) = Metric.sphere ((a / 2 : ℝ) * I) (|a| / 2) := by
  ext z
  rw [mem_sphere_iff_norm, ← sq_eq_sq₀ (norm_nonneg _) (by positivity), Complex.sq_norm,
    Complex.normSq_apply]
  simp only [sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero, add_zero, div_pow, sq_abs]
  constructor
  · rintro ⟨r, θ, rfl, rfl⟩
    rw [polarPoint_re, polarPoint_im]
    linear_combination (a ^ 2 * Real.sin θ ^ 2) * Real.sin_sq_add_cos_sq θ
  · intro hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨0, 0, by simp, by simp [polarPoint]⟩
    · refine ⟨‖z‖, arg z, ?_, eq_polarPoint_norm_arg z⟩
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
      show ‖z‖ = a * Real.sin (arg z)
      rw [sin_arg, mul_div_assoc', eq_div_iff hn.ne', ← sq, Complex.sq_norm, Complex.normSq_apply]
      linear_combination hz

/-- **The line `r = a sec θ`**: for `a ≠ 0` the graph of `r = a sec θ` (where `cos θ ≠ 0`) is the vertical
line `x = a`. (TR-199) -/
@[kb "openstaxalgtrig2e" "§10.3 Example 9, p. 920"]
theorem polarGraph_sec_eq {a : ℝ} (ha : a ≠ 0) :
    polarGraph (fun r θ => Real.cos θ ≠ 0 ∧ r = a * sec θ) = {z | z.re = a} := by
  ext z
  constructor
  · rintro ⟨r, θ, ⟨hc, rfl⟩, rfl⟩
    show (polarPoint _ θ).re = a
    rw [polarPoint_re, sec]
    field_simp
  · intro (hz : z.re = a)
    have hz0 : z ≠ 0 := by rintro rfl; exact ha (by simpa using hz.symm)
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hc : Real.cos (arg z) ≠ 0 := by rw [cos_arg hz0, hz]; exact div_ne_zero ha hn.ne'
    refine ⟨‖z‖, arg z, ⟨hc, ?_⟩, eq_polarPoint_norm_arg z⟩
    rw [sec, cos_arg hz0, hz]
    field_simp

/-- **The line `r = a csc θ`**: for `a ≠ 0` the graph of `r = a csc θ` (where `sin θ ≠ 0`) is the horizontal
line `y = a`. (TR-199) -/
theorem polarGraph_csc_eq {a : ℝ} (ha : a ≠ 0) :
    polarGraph (fun r θ => Real.sin θ ≠ 0 ∧ r = a * csc θ) = {z | z.im = a} := by
  ext z
  constructor
  · rintro ⟨r, θ, ⟨hc, rfl⟩, rfl⟩
    show (polarPoint _ θ).im = a
    rw [polarPoint_im, csc]
    field_simp
  · intro (hz : z.im = a)
    have hz0 : z ≠ 0 := by rintro rfl; exact ha (by simpa using hz.symm)
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hc : Real.sin (arg z) ≠ 0 := by rw [sin_arg, hz]; exact div_ne_zero ha hn.ne'
    refine ⟨‖z‖, arg z, ⟨hc, ?_⟩, eq_polarPoint_norm_arg z⟩
    rw [csc, sin_arg, hz]
    field_simp

/-- **Symmetries of the lemniscates** (OpenStax §10.4): the graph of `r² = a² cos 2θ` is symmetric about
the pole, the polar axis and the line `θ = π/2`; the graph of `r² = a² sin 2θ` is symmetric about the pole.
(TR-141) -/
@[kb "openstaxalgtrig2e" "§10.4 Lemniscates, p. 935"]
theorem lemniscate_symmetries (a : ℝ) :
    (∀ z ∈ polarGraph (fun r θ => r ^ 2 = a ^ 2 * Real.cos (2 * θ)),
        -z ∈ polarGraph (fun r θ => r ^ 2 = a ^ 2 * Real.cos (2 * θ)) ∧
        conj z ∈ polarGraph (fun r θ => r ^ 2 = a ^ 2 * Real.cos (2 * θ)) ∧
        -conj z ∈ polarGraph (fun r θ => r ^ 2 = a ^ 2 * Real.cos (2 * θ))) ∧
      ∀ z ∈ polarGraph (fun r θ => r ^ 2 = a ^ 2 * Real.sin (2 * θ)),
        -z ∈ polarGraph (fun r θ => r ^ 2 = a ^ 2 * Real.sin (2 * θ)) := by
  refine ⟨fun z hz => ⟨polarGraph_symm_pole ?_ z hz, polarGraph_symm_polarAxis (Or.inl ?_) z hz,
    polarGraph_symm_line_pi_div_two (Or.inl ?_) z hz⟩, polarGraph_symm_pole ?_⟩
  · intro r θ h; simpa using h
  · intro r θ h; simpa [mul_neg, Real.cos_neg] using h
  · intro r θ h; simpa [mul_neg, Real.cos_neg] using h
  · intro r θ h; simpa using h

end UndergradKB.Trigonometry
