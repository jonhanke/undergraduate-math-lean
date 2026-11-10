import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Topology.MetricSpace.Congruence
import UndergradKB.Common.Attr

/-! # Triangles with given data (Petrunin, chapters 3 and 4)

Existence of a triangle with prescribed side lengths (Theorem 3.18), intersection of two circles
(Exercise 3.21), a point at prescribed distance and angle (Proposition 3.19), the isosceles base
(Lemma 3.20), a motion fixing a triangle (Exercise 4.8), and the counterexamples for SSA and AAA
(Section 4E remarks). Existence results are proved in any real inner product space of dimension at
least two, and specialised to the Euclidean plane `EuclideanSpace ℝ (Fin 2)`. -/

namespace UndergradKB.Geometry

open EuclideanGeometry Real InnerProductGeometry Module Filter Topology

section General

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- In a space of dimension at least two, every vector has a unit vector orthogonal to it. -/
theorem exists_unit_orthogonal [FiniteDimensional ℝ V] (h2 : 2 ≤ finrank ℝ V) (w : V) :
    ∃ v : V, ‖v‖ = 1 ∧ inner ℝ w v = 0 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ w)
  have h3 : finrank ℝ (ℝ ∙ w) ≤ 1 := by simpa using finrank_span_le_card ({w} : Set V)
  have hpos : 0 < finrank ℝ (ℝ ∙ w)ᗮ := by omega
  obtain ⟨v, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv0' : (v : V) ≠ 0 := by simpa using hv0
  refine ⟨(‖(v : V)‖⁻¹) • (v : V), ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0')]
  · rw [inner_smul_right]
    have : inner ℝ w (v : V) = 0 :=
      (Submodule.mem_orthogonal _ _).mp v.2 w (Submodule.mem_span_singleton_self w)
    simp [this]

theorem norm_sq_smul_add {u v : V} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (s t : ℝ) : ‖s • u + t • v‖ ^ 2 = s ^ 2 + t ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, huv, hu, hv]
  simp

/-- Two circles in a space of dimension at least two with distinct centres meet when
`|r₁ - r₂| ≤ d ≤ r₁ + r₂`. -/
theorem exists_dist_eq_of_circles [FiniteDimensional ℝ V] (h2 : 2 ≤ finrank ℝ V) {O₁ O₂ : P}
    (hO : O₁ ≠ O₂) {r₁ r₂ : ℝ} (h1 : |r₁ - r₂| ≤ dist O₁ O₂) (h3 : dist O₁ O₂ ≤ r₁ + r₂) :
    ∃ X : P, dist X O₁ = r₁ ∧ dist X O₂ = r₂ := by
  set d := dist O₁ O₂ with hd
  have hdpos : 0 < d := dist_pos.mpr hO
  obtain ⟨ha, hb⟩ := abs_le.mp h1
  set w : V := O₂ -ᵥ O₁ with hw
  have hwn : ‖w‖ = d := by rw [hd, dist_comm, dist_eq_norm_vsub V]
  obtain ⟨v, hv, hwv⟩ := exists_unit_orthogonal h2 w
  set u : V := d⁻¹ • w with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, hwn, norm_inv, Real.norm_eq_abs, abs_of_pos hdpos, inv_mul_cancel₀ hdpos.ne']
  have huv : inner ℝ u v = 0 := by rw [hu, inner_smul_left]; simp [hwv]
  have hdu : d • u = w := by rw [hu, smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
  set x : ℝ := (d ^ 2 + r₁ ^ 2 - r₂ ^ 2) / (2 * d) with hx
  have hy : 0 ≤ r₁ ^ 2 - x ^ 2 := by
    have key : (r₁ ^ 2 - x ^ 2) * (4 * d ^ 2)
        = (r₂ ^ 2 - (d - r₁) ^ 2) * ((d + r₁) ^ 2 - r₂ ^ 2) := by
      rw [hx]; field_simp; ring
    have e1 : 0 ≤ r₂ ^ 2 - (d - r₁) ^ 2 := by nlinarith
    have e2 : 0 ≤ (d + r₁) ^ 2 - r₂ ^ 2 := by nlinarith
    have : 0 ≤ (r₁ ^ 2 - x ^ 2) * (4 * d ^ 2) := by rw [key]; exact mul_nonneg e1 e2
    exact nonneg_of_mul_nonneg_left this (by positivity)
  set y : ℝ := Real.sqrt (r₁ ^ 2 - x ^ 2) with hyd
  have hy2 : y ^ 2 = r₁ ^ 2 - x ^ 2 := Real.sq_sqrt hy
  have hr1 : 0 ≤ r₁ := by linarith [abs_nonneg (r₁ - r₂)]
  have hr2 : 0 ≤ r₂ := by linarith [abs_nonneg (r₁ - r₂)]
  refine ⟨(x • u + y • v) +ᵥ O₁, ?_, ?_⟩
  · rw [dist_vadd_left]
    have := norm_sq_smul_add hun hv huv x y
    rw [hy2] at this
    have h' : ‖x • u + y • v‖ ^ 2 = r₁ ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg _) hr1 two_ne_zero).mp h'
  · have hO2 : O₂ = (d • u) +ᵥ O₁ := by rw [hdu, hw, vsub_vadd]
    rw [hO2, dist_vadd_cancel_right, dist_eq_norm]
    have e : x • u + y • v - d • u = (x - d) • u + y • v := by rw [sub_smul]; abel
    rw [e]
    have := norm_sq_smul_add hun hv huv (x - d) y
    have h' : ‖(x - d) • u + y • v‖ ^ 2 = r₂ ^ 2 := by
      rw [this, hy2]; rw [hx]; field_simp; ring
    exact (pow_left_inj₀ (norm_nonneg _) hr2 two_ne_zero).mp h'

/-- **Existence of a triangle with given sides** (Petrunin, Theorem 3.18), in any real inner product
space of dimension at least two: for `0 < a ≤ b ≤ c ≤ a + b` there are points `A B C` with
`BC = a`, `CA = b`, `AB = c` (degenerate only when `c = a + b`). -/
@[kb "petrunin2025" "Theorem 3.18, p. 29"]
theorem exists_triangle_of_sides [FiniteDimensional ℝ V] (h2 : 2 ≤ finrank ℝ V) {a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ a + b) :
    ∃ A B C : P, dist B C = a ∧ dist C A = b ∧ dist A B = c := by
  obtain ⟨v, hv, -⟩ := exists_unit_orthogonal h2 0
  obtain ⟨A⟩ := (inferInstance : Nonempty P)
  set B : P := (c • v) +ᵥ A with hB
  have hdAB : dist A B = c := by
    rw [hB, dist_comm, dist_vadd_left, norm_smul, hv, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]; simp
  have hne : A ≠ B := by
    intro h; rw [h, dist_self] at hdAB; linarith
  obtain ⟨X, h1, h2'⟩ := exists_dist_eq_of_circles h2 hne (r₁ := b) (r₂ := a)
    (by rw [hdAB]; exact abs_le.mpr ⟨by linarith, by linarith⟩) (by rw [hdAB]; linarith)
  exact ⟨A, B, X, by rw [dist_comm]; exact h2', h1, hdAB⟩

end General

/-- Theorem 3.18 in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`. -/
@[kb "petrunin2025" "Theorem 3.18, p. 29"]
theorem exists_triangle_of_sides_plane {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ a + b) :
    ∃ A B C : EuclideanSpace ℝ (Fin 2), dist B C = a ∧ dist C A = b ∧ dist A B = c :=
  exists_triangle_of_sides (by simp) ha hab hbc hc

/-- **Intersection of two circles** (Petrunin, Exercise 3.21) in the Euclidean plane: circles of radii
`r₁, r₂ > 0` about `O₁, O₂` meet iff `|r₁ - r₂| ≤ O₁O₂ ≤ r₁ + r₂`. -/
@[kb "petrunin2025" "Exercise 3.21, p. 30"]
theorem circles_intersect_iff {O₁ O₂ : EuclideanSpace ℝ (Fin 2)} {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₂ : 0 < r₂) :
    (∃ X : EuclideanSpace ℝ (Fin 2), dist X O₁ = r₁ ∧ dist X O₂ = r₂) ↔
      |r₁ - r₂| ≤ dist O₁ O₂ ∧ dist O₁ O₂ ≤ r₁ + r₂ := by
  constructor
  · rintro ⟨X, hX1, hX2⟩
    have t1 := dist_triangle O₁ X O₂
    have t2 := dist_triangle X O₁ O₂
    have t3 := dist_triangle X O₂ O₁
    rw [dist_comm O₁ X] at t1
    rw [dist_comm O₂ O₁] at t3
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, by linarith⟩ <;> linarith
  · rintro ⟨h1, h3⟩
    by_cases hO : O₁ = O₂
    · subst hO
      rw [dist_self] at h1
      have : r₁ = r₂ := by
        have := abs_nonneg (r₁ - r₂); have := abs_le.mp h1; linarith
      subst this
      obtain ⟨v, hv, -⟩ := exists_unit_orthogonal (V := EuclideanSpace ℝ (Fin 2)) (by simp) 0
      exact ⟨(r₁ • v) +ᵥ O₁, by
        rw [dist_vadd_left, norm_smul, hv, Real.norm_eq_abs, abs_of_pos h₁]; simp, by
        rw [dist_vadd_left, norm_smul, hv, Real.norm_eq_abs, abs_of_pos h₁]; simp⟩
    · exact exists_dist_eq_of_circles (by simp) hO h1 h3

section General2

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **A motion fixing the vertices of a nondegenerate triangle is the identity** (Petrunin,
Exercise 4.8), in any Euclidean plane (a real inner product space `V` of dimension two with
affine space `P`). Proof: Mazur-Ulam makes the motion affine, and an affine map fixing an affinely
spanning triple is the identity. -/
@[kb "petrunin2025" "Exercise 4.8, p. 34"]
theorem motion_eq_refl_of_fixes_triangle [FiniteDimensional ℝ V] (hd : finrank ℝ V = 2)
    (f : P ≃ᵢ P) {A B C : P} (h : ¬Collinear ℝ ({A, B, C} : Set P)) (hA : f A = A)
    (hB : f B = B) (hC : f C = C) : f = IsometryEquiv.refl P := by
  have hi : AffineIndependent ℝ ![A, B, C] := affineIndependent_iff_not_collinear_set.mpr h
  have hspan : affineSpan ℝ (Set.range ![A, B, C]) = ⊤ :=
    hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hd])
  have hr : Set.range ![A, B, C] = {A, B, C} := by
    ext x; simp; tauto
  rw [hr] at hspan
  have key : f.toRealAffineIsometryEquiv.toAffineEquiv = AffineEquiv.refl ℝ P := by
    apply AffineEquiv.ext_on hspan
    intro x hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  ext x
  have := congrArg (fun T : P ≃ᵃ[ℝ] P => T x) key
  show f x = x
  simpa using this

variable [FiniteDimensional ℝ V]

/-- **Point at given distance and angle** (Petrunin, Proposition 3.19, existence part): for `r > 0`,
`A ≠ B` and `β ∈ [0, π]` there is `C` with `BC = r` and `∠ABC = β`. Stated in any real inner product
space of dimension at least two; the book's uniqueness on a chosen side and continuity in `β` are not
formalized. -/
@[kb "petrunin2025" "Proposition 3.19, p. 29"]
theorem exists_point_dist_angle (h2 : 2 ≤ finrank ℝ V) {A B : P} (hAB : A ≠ B) {r β : ℝ}
    (hr : 0 < r) (hβ0 : 0 ≤ β) (hβ : β ≤ π) : ∃ C : P, dist B C = r ∧ ∠ A B C = β := by
  set w : V := A -ᵥ B with hw
  have hw0 : w ≠ 0 := vsub_ne_zero.mpr hAB
  have hD : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨v, hv, -⟩ := exists_unit_orthogonal h2 0
  set u : V := ‖w‖⁻¹ • w with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hD.ne']
  have e1 : A -ᵥ B = ‖w‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
  clear_value u
  obtain ⟨v, hv, huv⟩ := exists_unit_orthogonal h2 u
  set z : V := Real.cos β • u + Real.sin β • v with hz
  have hzn : ‖z‖ = 1 := by
    have := norm_sq_smul_add hun hv huv (Real.cos β) (Real.sin β)
    rw [Real.cos_sq_add_sin_sq] at this
    have h1 : ‖z‖ ^ 2 = 1 ^ 2 := by rw [hz, this]; norm_num
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h1
  refine ⟨(r • z) +ᵥ B, ?_, ?_⟩
  · rw [dist_comm, dist_vadd_left, norm_smul, hzn, Real.norm_eq_abs, abs_of_pos hr]; simp
  · rw [EuclideanGeometry.angle, vadd_vsub, e1, InnerProductGeometry.angle_smul_left_of_pos _ _ hD,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hr]
    have hcos : Real.cos (InnerProductGeometry.angle u z) = Real.cos β := by
      rw [InnerProductGeometry.cos_angle, hun, hzn, hz, inner_add_right, inner_smul_right,
        inner_smul_right, huv, real_inner_self_eq_norm_sq, hun]
      simp
    exact Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨hβ0, hβ⟩ hcos

end General2

section Isosceles

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The base of an isosceles triangle with legs `r` and apex angle `β = ∠ABC` is `2 r sin (β / 2)`. -/
theorem dist_isosceles_base {A B C : P} {r : ℝ} (hA : dist B A = r) (hC : dist B C = r) :
    dist A C = 2 * r * Real.sin (∠ A B C / 2) := by
  have hl := law_cos A B C
  rw [dist_comm A B, dist_comm C B, hA, hC] at hl
  have hr : 0 ≤ r := hA ▸ dist_nonneg
  have hθ : ∠ A B C = 2 * (∠ A B C / 2) := by ring
  have hs : 0 ≤ Real.sin (∠ A B C / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [angle_nonneg A B C])
      (by linarith [angle_le_pi A B C, Real.pi_pos])
  have hc : Real.cos (∠ A B C) = 1 - 2 * Real.sin (∠ A B C / 2) ^ 2 := by
    rw [hθ, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (∠ A B C / 2)
    rw [← hθ] at *
    nlinarith [this]
  have h1 : dist A C ^ 2 = (2 * r * Real.sin (∠ A B C / 2)) ^ 2 := by
    rw [hc] at hl; nlinarith [hl]
  exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1

/-- **The base of a thin isosceles triangle is small** (Petrunin, Lemma 3.20): if `BA = BC = r` and the
apex angle `∠ABC` tends to `0` (along any filter), then `AC` tends to `0`. -/
@[kb "petrunin2025" "Lemma 3.20, p. 29"]
theorem tendsto_dist_isosceles_base {ι : Type*} {l : Filter ι} {A B : P} {C : ι → P} {r : ℝ}
    (hA : dist B A = r) (hC : ∀ i, dist B (C i) = r)
    (h : Tendsto (fun i => ∠ A B (C i)) l (𝓝 0)) :
    Tendsto (fun i => dist A (C i)) l (𝓝 0) := by
  have hcont : Continuous fun x : ℝ => 2 * r * Real.sin (x / 2) := by fun_prop
  have h0 := (hcont.tendsto 0).comp h
  simp only [zero_div, Real.sin_zero, mul_zero] at h0
  refine h0.congr fun i => ?_
  simp only [Function.comp]
  exact (dist_isosceles_base hA (hC i)).symm

end Isosceles

section Examples

/-- Helper: a nondegenerate configuration from an angle equal to `π / 3`. -/
theorem not_collinear_of_angle_eq_pi_div_three {A B C : EuclideanSpace ℝ (Fin 2)}
    (h : ∠ B A C = π / 3) : ¬Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [Set.insert_comm, collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
  have := Real.pi_pos
  rintro (rfl | rfl | h0 | hp)
  · simp at h; linarith
  · simp at h; linarith
  · linarith
  · linarith

/-- Helper: an angle whose cosine is `1/2` equals `π / 3`. -/
theorem angle_eq_pi_div_three_of {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (h : inner ℝ x y / (‖x‖ * ‖y‖) = 1 / 2) : InnerProductGeometry.angle x y = π / 3 := by
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [InnerProductGeometry.cos_angle, h, Real.cos_pi_div_three]

/-- **SSA is not a congruence criterion** (Petrunin, remark in Section 4E): two nondegenerate triangles
in the Euclidean plane with `AB`, `BC` and the angle at `A` (opposite to `BC`) equal, but whose third
sides `AC` differ (`1` and `2`), so that they are not congruent. -/
@[kb "petrunin2025" "SSA remark, p. 34"]
theorem ssa_not_congruent :
    ∃ t₁ t₂ : Fin 3 → EuclideanSpace ℝ (Fin 2), AffineIndependent ℝ t₁ ∧ AffineIndependent ℝ t₂ ∧
      dist (t₁ 0) (t₁ 1) = dist (t₂ 0) (t₂ 1) ∧ dist (t₁ 1) (t₁ 2) = dist (t₂ 1) (t₂ 2) ∧
      ∠ (t₁ 1) (t₁ 0) (t₁ 2) = ∠ (t₂ 1) (t₂ 0) (t₂ 2) ∧ ¬ Congruent t₁ t₂ := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := by positivity
  have hnorm : ∀ p q : ℝ, ‖(!₂[p, q] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt (p ^ 2 + q ^ 2) := by
    intro p q; simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hinner : ∀ p q p' q' : ℝ, inner ℝ (!₂[p, q] : EuclideanSpace ℝ (Fin 2)) !₂[p', q'] =
      p * p' + q * q' := by
    intro p q p' q'; simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  have n1 : ‖(!₂[1 / 2, Real.sqrt 3 / 2] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [hnorm, Real.sqrt_eq_one]; nlinarith
  have n2 : ‖(!₂[1, Real.sqrt 3] : EuclideanSpace ℝ (Fin 2))‖ = 2 := by
    rw [hnorm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]; nlinarith
  have n3 : ‖(!₂[3, 0] : EuclideanSpace ℝ (Fin 2))‖ = 3 := by
    rw [hnorm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by norm_num)]; norm_num
  have a1 : ∠ (!₂[3, 0] : EuclideanSpace ℝ (Fin 2)) 0 !₂[1 / 2, Real.sqrt 3 / 2] = π / 3 := by
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero]
    apply angle_eq_pi_div_three_of
    rw [hinner, n1, n3]; norm_num
  have a2 : ∠ (!₂[3, 0] : EuclideanSpace ℝ (Fin 2)) 0 !₂[1, Real.sqrt 3] = π / 3 := by
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero]
    apply angle_eq_pi_div_three_of
    rw [hinner, n2, n3]; norm_num
  have hdist : ∀ p q p' q' : ℝ, dist (!₂[p, q] : EuclideanSpace ℝ (Fin 2)) !₂[p', q'] =
      Real.sqrt ((p - p') ^ 2 + (q - q') ^ 2) := by
    intro p q p' q'; simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have d1 : dist (!₂[3, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1 / 2, Real.sqrt 3 / 2] = Real.sqrt 7 := by
    rw [hdist]; congr 1; nlinarith
  have d2 : dist (!₂[3, 0] : EuclideanSpace ℝ (Fin 2)) !₂[1, Real.sqrt 3] = Real.sqrt 7 := by
    rw [hdist]; congr 1; nlinarith
  have z : (0 : EuclideanSpace ℝ (Fin 2)) = !₂[0, 0] := by ext i; fin_cases i <;> simp
  have e1 : dist (0 : EuclideanSpace ℝ (Fin 2)) !₂[1 / 2, Real.sqrt 3 / 2] = 1 := by
    rw [dist_zero_left, n1]
  have e2 : dist (0 : EuclideanSpace ℝ (Fin 2)) !₂[1, Real.sqrt 3] = 2 := by
    rw [dist_zero_left, n2]
  refine ⟨![0, !₂[3, 0], !₂[1 / 2, Real.sqrt 3 / 2]], ![0, !₂[3, 0], !₂[1, Real.sqrt 3]],
    affineIndependent_iff_not_collinear_set.mpr (not_collinear_of_angle_eq_pi_div_three a1),
    affineIndependent_iff_not_collinear_set.mpr (not_collinear_of_angle_eq_pi_div_three a2),
    ?_, ?_, ?_, ?_⟩
  · simp
  · simpa using d1.trans d2.symm
  · simpa using a1.trans a2.symm
  · intro h
    have := h 0 2
    simp only [edist_dist] at this
    rw [ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg] at this
    replace this : dist (0 : EuclideanSpace ℝ (Fin 2)) !₂[1 / 2, Real.sqrt 3 / 2] =
        dist (0 : EuclideanSpace ℝ (Fin 2)) !₂[1, Real.sqrt 3] := by simpa using this
    rw [e1, e2] at this
    norm_num at this

/-- **AAA is not a congruence criterion** (Petrunin, remark in Section 4E): scaling a nondegenerate
triangle `t` of the Euclidean plane by a factor `k > 0`, `k ≠ 1` (for instance `k = 2`) keeps all three
angles but gives a triangle that is not congruent to `t`. -/
@[kb "petrunin2025" "AAA remark, p. 34"]
theorem aaa_not_congruent {t : Fin 3 → EuclideanSpace ℝ (Fin 2)} (ht : AffineIndependent ℝ t)
    {k : ℝ} (hk : 0 < k) (hk1 : k ≠ 1) :
    ∠ (t 0) (t 1) (t 2) = ∠ (k • t 0) (k • t 1) (k • t 2) ∧
    ∠ (t 1) (t 2) (t 0) = ∠ (k • t 1) (k • t 2) (k • t 0) ∧
    ∠ (t 2) (t 0) (t 1) = ∠ (k • t 2) (k • t 0) (k • t 1) ∧
    ¬ Congruent t (fun i => k • t i) := by
  have key : ∀ p q r : EuclideanSpace ℝ (Fin 2), ∠ p q r = ∠ (k • p) (k • q) (k • r) := by
    intro p q r
    simp only [EuclideanGeometry.angle, vsub_eq_sub, ← smul_sub]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hk,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hk]
  refine ⟨key _ _ _, key _ _ _, key _ _ _, ?_⟩
  intro h
  have h01 := h 0 1
  simp only [edist_dist] at h01
  rw [ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos hk] at h01
  have h0 : dist (t 0) (t 1) = 0 := by
    have : (k - 1) * dist (t 0) (t 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith) hk1
    · exact h
  have := ht.injective (dist_eq_zero.mp h0)
  exact absurd this (by decide)

end Examples

end UndergradKB.Geometry
