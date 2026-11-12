import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Convex.Segment
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import UndergradKB.Common.Attr

/-!
# Vectors in the plane and parametric curves (Stitz–Zeager, Precalculus, §11.8–§11.10)

Vectors of the plane are explicit pairs `ℝ × ℝ`; the dot product is `dotProd2` and the
magnitude is `vecMag`. A parametrized curve is a map `ℝ → ℝ × ℝ`.
-/

namespace UndergradKB.Precalculus

open UndergradKB

/-- Dot product of two plane vectors given by coordinates. -/
def dotProd2 (v w : ℝ × ℝ) : ℝ := v.1 * w.1 + v.2 * w.2

/-- Magnitude `√(v₁² + v₂²)` of a plane vector. -/
noncomputable def vecMag (v : ℝ × ℝ) : ℝ := Real.sqrt (v.1 ^ 2 + v.2 ^ 2)

private lemma unit_circle_angle {u v : ℝ} (h : u ^ 2 + v ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = u ∧ Real.sin θ = v := by
  set z : ℂ := ⟨u, v⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    have : z.re * z.re + z.im * z.im = 1 := by simp only [hz]; nlinarith
    rw [this]; simp
  refine ⟨Complex.arg z, ?_, ?_⟩
  · have := Complex.norm_mul_cos_arg z
    rw [hn] at this; simpa [hz] using this
  · have := Complex.norm_mul_sin_arg z
    rw [hn] at this; simpa [hz] using this

/-! ### Magnitude and direction (PC-275) -/

/-- The magnitude of `(a, b)` agrees with the Euclidean norm, and `(a, b)` is its magnitude
times `⟨cos θ, sin θ⟩` for a polar angle `θ`; conversely, if `(a,b)` has polar form `(r, θ)`
with `r > 0` then `r` is the magnitude and `⟨cos θ, sin θ⟩` is `(a,b)` divided by it
(PC-275). -/
@[kb "stitzzeager2013" "Definition 11.8, p. 1032"]
theorem vector_magnitude_direction (a b : ℝ) :
    ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ = vecMag (a, b) ∧
    (∃ θ : ℝ, a = vecMag (a, b) * Real.cos θ ∧ b = vecMag (a, b) * Real.sin θ) ∧
    (∀ r θ : ℝ, 0 < r → a = r * Real.cos θ → b = r * Real.sin θ →
      vecMag (a, b) = r ∧ Real.cos θ = a / vecMag (a, b) ∧ Real.sin θ = b / vecMag (a, b)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclideanSpace.norm_eq]
    simp [vecMag, Fin.sum_univ_two]
  · by_cases h : a ^ 2 + b ^ 2 = 0
    · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      exact ⟨0, by simp [vecMag, ha, hb]⟩
    · have hp : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
      have hm : 0 < vecMag (a, b) := Real.sqrt_pos.mpr hp
      have hm2 : vecMag (a, b) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hp.le
      obtain ⟨θ, h1, h2⟩ := unit_circle_angle (u := a / vecMag (a, b)) (v := b / vecMag (a, b))
        (by field_simp; linarith)
      exact ⟨θ, by rw [h1]; field_simp, by rw [h2]; field_simp⟩
  · intro r θ hr ha hb
    have hmag : vecMag (a, b) = r := by
      unfold vecMag
      simp only
      rw [ha, hb]
      have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      rw [this, Real.sqrt_sq hr.le]
    refine ⟨hmag, ?_, ?_⟩
    · rw [hmag, ha]; field_simp
    · rw [hmag, hb]; field_simp

/-! ### Projection (PC-287, PC-289) -/

/-- Orthogonal projection of `v` onto `w`: `((v·w)/(w·w)) w`. -/
noncomputable def vecProj (v w : ℝ × ℝ) : ℝ × ℝ :=
  (dotProd2 v w / dotProd2 w w) • w

/-- For `w ≠ 0` the projection equals `(v · ŵ) ŵ` with `ŵ = w / ‖w‖` the unit vector (PC-287). -/
@[kb "stitzzeager2013" "Definition 11.12, p. 1051"]
theorem vecProj_eq_unit_form (v w : ℝ × ℝ) (hw : w ≠ 0) :
    vecProj v w = dotProd2 v ((vecMag w)⁻¹ • w) • ((vecMag w)⁻¹ • w) := by
  have hp : 0 < w.1 ^ 2 + w.2 ^ 2 := by
    rcases Classical.em (w.1 = 0) with h1 | h1
    · have h2 : w.2 ≠ 0 := fun h2 => hw (Prod.ext h1 h2)
      positivity
    · positivity
  have hm : vecMag w ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hm2 : vecMag w ^ 2 = w.1 ^ 2 + w.2 ^ 2 := Real.sq_sqrt hp.le
  have hww : dotProd2 w w = vecMag w ^ 2 := by unfold dotProd2; rw [hm2]; ring
  unfold vecProj
  rw [hww]
  ext <;> simp [dotProd2] <;> field_simp

/-- Every `v` splits uniquely as `p + q` with `p` a multiple of `w ≠ 0` and `q · w = 0`; the
splitting is `p = vecProj v w` (PC-289). -/
@[kb "stitzzeager2013" "Theorem 11.27, p. 1052"]
theorem vector_decomposition_unique (v w : ℝ × ℝ) (hw : w ≠ 0) :
    ∃! pq : (ℝ × ℝ) × (ℝ × ℝ), v = pq.1 + pq.2 ∧ (∃ c : ℝ, pq.1 = c • w) ∧
      dotProd2 pq.2 w = 0 := by
  have hp : 0 < dotProd2 w w := by
    unfold dotProd2
    rcases Classical.em (w.1 = 0) with h1 | h1
    · have h2 : w.2 ≠ 0 := fun h2 => hw (Prod.ext h1 h2)
      nlinarith [sq_pos_of_ne_zero h2]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg w.2]
  have hne : dotProd2 w w ≠ 0 := hp.ne'
  refine ⟨(vecProj v w, v - vecProj v w), ⟨?_, ⟨_, rfl⟩, ?_⟩, ?_⟩
  · simp
  · simp only [vecProj, dotProd2, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    unfold dotProd2 at hne
    have key : ((v.1 * w.1 + v.2 * w.2) / (w.1 * w.1 + w.2 * w.2)) * (w.1 * w.1 + w.2 * w.2) =
        v.1 * w.1 + v.2 * w.2 := div_mul_cancel₀ _ hne
    linear_combination (-1 : ℝ) * key
  · rintro ⟨p, q⟩ ⟨h1, ⟨c, hc⟩, h2⟩
    simp only at h1 hc h2
    have hq : q = v - p := by rw [h1]; simp
    have hc' : c = dotProd2 v w / dotProd2 w w := by
      rw [eq_div_iff hne]
      have : dotProd2 q w = dotProd2 v w - c * dotProd2 w w := by
        rw [hq, hc]; simp only [dotProd2, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      linarith
    have hpp : p = vecProj v w := by rw [hc, hc']; rfl
    rw [hq, hpp]

/-! ### Work (PC-290) -/

/-- Work done by a constant force `F` moving an object from `P` to `Q`: `F · PQ`. -/
noncomputable def workDone (F P Q : EuclideanSpace ℝ (Fin 2)) : ℝ := inner ℝ F (Q - P)

/-- `W = F · PQ = F₁(Q₁ − P₁) + F₂(Q₂ − P₂) = ‖F‖ ‖PQ‖ cos θ` where `θ` is the angle between
`F` and `PQ` (PC-290). -/
@[kb "stitzzeager2013" "Theorem 11.28, p. 1054"]
theorem work_eq_norm_mul_norm_mul_cos (F P Q : EuclideanSpace ℝ (Fin 2)) :
    workDone F P Q = F 0 * (Q 0 - P 0) + F 1 * (Q 1 - P 1) ∧
    workDone F P Q = ‖F‖ * ‖Q - P‖ * Real.cos (InnerProductGeometry.angle F (Q - P)) := by
  constructor
  · unfold workDone
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  · unfold workDone
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
    ring

/-! ### Parametrized curves (PC-291 to PC-294) -/

/-- The curve `x = r cos ωt`, `y = r sin ωt`. -/
noncomputable def circleParam (r ω t : ℝ) : ℝ × ℝ := (r * Real.cos (ω * t), r * Real.sin (ω * t))

/-- For `r > 0`, `ω > 0` the curve `x = r cos ωt, y = r sin ωt` covers the circle
`x² + y² = r²`, and it runs counterclockwise: the velocity `(-rω sin ωt, rω cos ωt)` has
positive cross product `x y' − y x' = r² ω` with the position (PC-291). -/
@[kb "stitzzeager2013" "§11.10, p. 1060"]
theorem circle_param_counterclockwise {r ω : ℝ} (hr : 0 < r) (hω : 0 < ω) :
    Set.range (circleParam r ω) = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = r ^ 2} ∧
    ∀ t : ℝ, HasDerivAt (circleParam r ω) (-(r * ω * Real.sin (ω * t)), r * ω * Real.cos (ω * t)) t ∧
      (circleParam r ω t).1 * (r * ω * Real.cos (ω * t)) -
        (circleParam r ω t).2 * (-(r * ω * Real.sin (ω * t))) = r ^ 2 * ω := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · ext ⟨x, y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, h⟩
      simp only [circleParam, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      nlinarith [Real.sin_sq_add_cos_sq (ω * t)]
    · intro h
      obtain ⟨θ, h1, h2⟩ := unit_circle_angle (u := x / r) (v := y / r)
        (by field_simp; linarith)
      refine ⟨θ / ω, ?_⟩
      simp only [circleParam]
      rw [mul_div_cancel₀ _ hω.ne', h1, h2]
      ext <;> simp <;> field_simp
  · have h1 : HasDerivAt (fun t => r * Real.cos (ω * t)) (-(r * ω * Real.sin (ω * t))) t := by
      have := ((hasDerivAt_id t).const_mul ω).cos.const_mul r
      simp only [id, mul_one] at this
      exact this.congr_deriv (by ring)
    have h2 : HasDerivAt (fun t => r * Real.sin (ω * t)) (r * ω * Real.cos (ω * t)) t := by
      have := ((hasDerivAt_id t).const_mul ω).sin.const_mul r
      simp only [id, mul_one] at this
      exact this.congr_deriv (by ring)
    exact h1.prodMk h2
  · simp only [circleParam]
    linear_combination (r ^ 2 * ω) * Real.sin_sq_add_cos_sq (ω * t)

/-- Standard parametrizations: the graph `y = f(x)` by `(t, f t)`; the graph `x = g(y)` by
`(g t, t)`; the segment from `P` to `Q` by `P + t (Q − P)`, `0 ≤ t ≤ 1`; the ellipse
`((x−h)/a)² + ((y−k)/b)² = 1` by `(h + a cos t, k + b sin t)` for `a, b ≠ 0` (PC-292). -/
@[kb "stitzzeager2013" "§11.10, p. 1065"]
theorem standard_parametrizations (f g : ℝ → ℝ) (P Q : ℝ × ℝ) (h k a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Set.range (fun t : ℝ => (t, f t)) = {p : ℝ × ℝ | p.2 = f p.1} ∧
    Set.range (fun t : ℝ => (g t, t)) = {p : ℝ × ℝ | p.1 = g p.2} ∧
    (fun t : ℝ => P + t • (Q - P)) '' Set.Icc 0 1 = segment ℝ P Q ∧
    Set.range (fun t : ℝ => (h + a * Real.cos t, k + b * Real.sin t)) =
      {p : ℝ × ℝ | ((p.1 - h) / a) ^ 2 + ((p.2 - k) / b) ^ 2 = 1} := by
  refine ⟨?_, ?_, (segment_eq_image' ℝ P Q).symm, ?_⟩
  · ext ⟨x, y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨t, rfl, rfl⟩; rfl
    · intro hy; exact ⟨x, rfl, hy.symm⟩
  · ext ⟨x, y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨t, rfl, rfl⟩; rfl
    · intro hx; exact ⟨y, hx.symm, rfl⟩
  · ext ⟨x, y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨t, rfl, rfl⟩
      have e1 : (h + a * Real.cos t - h) / a = Real.cos t := by
        rw [add_sub_cancel_left]; field_simp
      have e2 : (k + b * Real.sin t - k) / b = Real.sin t := by
        rw [add_sub_cancel_left]; field_simp
      rw [e1, e2]
      linarith [Real.sin_sq_add_cos_sq t]
    · intro hxy
      obtain ⟨θ, h1, h2⟩ := unit_circle_angle hxy
      refine ⟨θ, ?_, ?_⟩
      · rw [h1]; field_simp; ring
      · rw [h2]; field_simp; ring

/-- Replacing `t` by `-t` or by `t - c` does not change the traced set; on a parameter interval
the reversed curve starts where the original ended, and the shifted curve starts at the
shifted parameter (PC-293). -/
@[kb "stitzzeager2013" "§11.10, p. 1066"]
theorem reparametrization_reverse_shift (γ : ℝ → ℝ × ℝ) (c s e : ℝ) (_hse : s ≤ e) :
    Set.range (fun t => γ (-t)) = Set.range γ ∧
    Set.range (fun t => γ (t - c)) = Set.range γ ∧
    (fun t => γ (-t)) '' Set.Icc (-e) (-s) = γ '' Set.Icc s e ∧
    (fun t => γ (-t)) (-e) = γ e ∧ (fun t => γ (-t)) (-s) = γ s ∧
    (fun t => γ (t - c)) '' Set.Icc (s + c) (e + c) = γ '' Set.Icc s e ∧
    (fun t => γ (t - c)) (s + c) = γ s ∧ (fun t => γ (t - c)) (e + c) = γ e := by
  refine ⟨?_, ?_, ?_, by simp, by simp, ?_, by simp, by simp⟩
  · ext p
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨-t, rfl⟩
    · rintro ⟨t, rfl⟩; exact ⟨-t, by simp⟩
  · ext p
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t - c, rfl⟩
    · rintro ⟨t, rfl⟩; exact ⟨t + c, by simp⟩
  · ext p
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; exact ⟨-t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; exact ⟨-t, ⟨by linarith, by linarith⟩, by simp⟩
  · ext p
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; exact ⟨t - c, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩; exact ⟨t + c, ⟨by linarith, by linarith⟩, by simp⟩

/-- The point of the cycloid traced by a point on the rim of a circle of radius `r` rolling
along the `x`-axis, after the circle has turned through the angle `t`. -/
noncomputable def cycloid (r t : ℝ) : ℝ × ℝ := (r * (t - Real.sin t), r * (1 - Real.cos t))

/-- The cycloid point is at distance `|r|` from the centre `(r t, r)` of the rolling circle, it
never lies below the `x`-axis (for `r > 0`), and it touches the axis exactly when `t` is a
multiple of `2π`, at the point `(2π r n, 0)` (PC-294). -/
@[kb "stitzzeager2013" "Example 11.10.5, p. 1069"]
theorem cycloid_on_rolling_circle {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ((cycloid r t).1 - r * t) ^ 2 + ((cycloid r t).2 - r) ^ 2 = r ^ 2 ∧
    0 ≤ (cycloid r t).2 ∧
    ((cycloid r t).2 = 0 ↔ ∃ n : ℤ, t = n * (2 * Real.pi)) ∧
    (∀ n : ℤ, cycloid r (n * (2 * Real.pi)) = (r * (n * (2 * Real.pi)), 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [cycloid]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · simp only [cycloid]
    nlinarith [Real.cos_le_one t]
  · simp only [cycloid]
    constructor
    · intro h
      have hc : Real.cos t = 1 := by
        have : r * (1 - Real.cos t) = 0 := h
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hr.ne'
        · linarith
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff t).mp hc
      exact ⟨n, by rw [← hn]⟩
    · rintro ⟨n, rfl⟩
      simp [Real.cos_int_mul_two_pi]
  · intro n
    have := Real.sin_add_int_mul_two_pi 0 n
    simp [cycloid, Real.cos_int_mul_two_pi]
    exact Or.inl (by simpa using this)

end UndergradKB.Precalculus
