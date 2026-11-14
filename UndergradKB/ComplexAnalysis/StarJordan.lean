import UndergradKB.ComplexAnalysis.StarPath

/-!
# The Jordan curve theorem for star-shaped paths

Wave 4 (`StarPath.lean`) proved the Jordan curve theorem and both assumed fields of
`IsPositivelyOrientedSimpleClosed` (Beck et al., Section 4.4 and Definition 4.4.4) for a path that
is star-shaped about a point `c` *and* lies on the boundary of a convex set. Here the convexity
hypothesis is removed: every closed path `γ` with `IsStarPath γ c φ` (every ray from `c` meets the
path exactly once, and the path winds once counterclockwise around `c`) qualifies. This covers every
polar curve `c + ρ(θ) e^{iθ}` with `ρ` continuous and positive (star polygons, limaçons
`r = 2 + cos θ`, ...), not only convex curves.

* `IsStarPath.radius`: the distance from `c` to the path in the direction of `z`; it is continuous
  off `c` (`continuousOn_radius`, by a closed-map argument on the compact parameter interval).
* `IsStarPath.inner`, `IsStarPath.outer`: the points nearer to, resp. farther from, `c` than the path
  in their direction. `IsStarPath.jordan_curve_star`: the Jordan curve theorem (two components,
  open, connected, the first bounded and the second not, the path the frontier of each), and
  `insideOf_eq_inner`.
* `IsStarPath.retract`: the retraction of the plane onto the closed star region (points outside are
  pushed back along their ray onto the path). The annulus homotopy is built in the plane minus the
  disc (radial projection, moving the centre of projection along a segment of the star-convex inner
  region, homotopy of angles) and then pushed into the region by the retraction
  (`annulus_homotopy_star`).
* `IsStarPath.isPositivelyOrientedSimpleClosed_star`: every piecewise smooth star-shaped path is a
  positively oriented simple closed path in the sense of Definition 4.4.4, with no assumption.
-/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

namespace IsStarPath

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ}

/-! ### The radius in a given direction -/

/-- The distance from `c` to the path `γ` along the ray from `c` through `z` (for a star-shaped
path the ray meets the path exactly once; the value at `z = c` is a harmless default). -/
noncomputable def radius (γ : ℝ → ℂ) (c : ℂ) (z : ℂ) : ℝ := by
  classical
  exact if hz : ∃ t ∈ Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ z = c + r * (γ t - c) then
    ‖γ hz.choose - c‖ else ‖γ 0 - c‖

lemma radius_eq (h : IsStarPath γ c φ) {z : ℂ} {t r : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hr : 0 < r)
    (hz : z = c + r * (γ t - c)) : radius γ c z = ‖γ t - c‖ := by
  have hex : ∃ t ∈ Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ z = c + r * (γ t - c) := ⟨t, ht, r, hr, hz⟩
  classical
  rw [radius, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨ht', r', hr', hz'⟩ := hex.choose_spec
  rw [(h.eq_of_ray_eq ht' ht hr' hr (hz'.symm.trans hz)).1]

lemma exists_radius (_h : IsStarPath γ c φ) (z : ℂ) :
    ∃ t ∈ Icc (0 : ℝ) 1, radius γ c z = ‖γ t - c‖ := by
  classical
  unfold radius
  split_ifs with hex
  · exact ⟨_, hex.choose_spec.1, rfl⟩
  · exact ⟨0, zero_mem, rfl⟩

lemma radius_pos (h : IsStarPath γ c φ) (z : ℂ) : 0 < radius γ c z := by
  obtain ⟨t, ht, e⟩ := h.exists_radius z
  rw [e]
  exact h.norm_pos ht

/-- Every `z ≠ c` is `c + r (γ t - c)` with `r > 0`, and then `|z - c| = r · radius z`. -/
lemma exists_ray_radius (h : IsStarPath γ c φ) {z : ℂ} (hz : z ≠ c) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ z = c + r * (γ t - c) ∧ radius γ c z = ‖γ t - c‖ ∧
      ‖z - c‖ = r * radius γ c z := by
  obtain ⟨t, ht, r, hr, hzr⟩ := h.exists_ray hz
  have ht' := Ico_subset_Icc_self ht
  refine ⟨t, ht', r, hr, hzr, h.radius_eq ht' hr hzr, ?_⟩
  rw [h.radius_eq ht' hr hzr, hzr, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]

/-- The radius only depends on the direction from `c`. -/
lemma radius_smul (h : IsStarPath γ c φ) {z : ℂ} (hz : z ≠ c) {l : ℝ} (hl : 0 < l) :
    radius γ c (c + l * (z - c)) = radius γ c z := by
  obtain ⟨t, ht, r, hr, hzr, hrad, -⟩ := h.exists_ray_radius hz
  rw [hrad, h.radius_eq ht (mul_pos hl hr) (by rw [hzr]; push_cast; ring)]

/-- The radius is bounded below by the distance from `c` to the path. -/
lemma exists_radius_bounds (h : IsStarPath γ c φ) :
    ∃ m M : ℝ, 0 < m ∧ ∀ z, m ≤ radius γ c z ∧ radius γ c z ≤ M := by
  have hn : ContinuousOn (fun t => ‖γ t - c‖) (Icc 0 1) := (h.cont.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hn
  obtain ⟨t₁, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) hn
  refine ⟨‖γ t₀ - c‖, ‖γ t₁ - c‖, h.norm_pos ht₀, fun z => ?_⟩
  obtain ⟨t, ht, e⟩ := h.exists_radius z
  rw [e]
  exact ⟨isMinOn_iff.1 hmin t ht, isMaxOn_iff.1 hmax t ht⟩

/-- The unit vector in the direction of `x` is unchanged by positive scaling. -/
lemma dir_smul {x : ℂ} (hx : x ≠ 0) {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) * x) / (‖(r : ℂ) * x‖ : ℂ) = x / (‖x‖ : ℂ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h1 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2 : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hx).ne'
  push_cast
  field_simp

/-- **The radius is continuous off the centre.** A closed set of radii is the preimage of the
image of a compact set of parameters under the direction map. -/
theorem continuousOn_radius (h : IsStarPath γ c φ) : ContinuousOn (radius γ c) {c}ᶜ := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  have hAc : IsCompact (Icc (0 : ℝ) 1 ∩ (fun t => ‖γ t - c‖) ⁻¹' C) :=
    isCompact_Icc.of_isClosed_subset
      ((h.cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed isClosed_Icc hC)
      inter_subset_left
  have hdc : ContinuousOn (fun z : ℂ => (z - c) / (‖z - c‖ : ℂ)) {c}ᶜ := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro z hz
    exact_mod_cast (norm_pos_iff.2 (sub_ne_zero.2 hz)).ne'
  have hγA : ContinuousOn γ (Icc (0 : ℝ) 1 ∩ (fun t => ‖γ t - c‖) ⁻¹' C) :=
    h.cont.mono inter_subset_left
  have himg : IsCompact ((fun z : ℂ => (z - c) / (‖z - c‖ : ℂ)) ''
      (γ '' (Icc (0 : ℝ) 1 ∩ (fun t => ‖γ t - c‖) ⁻¹' C))) := by
    refine (hAc.image_of_continuousOn hγA).image_of_continuousOn (hdc.mono ?_)
    rintro _ ⟨t, ht, rfl⟩
    exact h.ne t ht.1
  obtain ⟨u, hu, hue⟩ := continuousOn_iff_isClosed.1 hdc _ himg.isClosed
  refine ⟨u, hu, ?_⟩
  rw [← hue]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hzC, hzc⟩
    refine ⟨?_, hzc⟩
    obtain ⟨t, ht, r, hr, hzr, hrad, -⟩ := h.exists_ray_radius hzc
    refine ⟨γ t, ⟨t, ⟨ht, ?_⟩, rfl⟩, ?_⟩
    · show ‖γ t - c‖ ∈ C
      rw [← hrad]; exact hzC
    · show (γ t - c) / (‖γ t - c‖ : ℂ) = (z - c) / (‖z - c‖ : ℂ)
      rw [hzr, add_sub_cancel_left, dir_smul (sub_ne_zero.2 (h.ne t ht)) hr]
  · rintro ⟨⟨_, ⟨t, ⟨ht, htC⟩, rfl⟩, he⟩, hzc⟩
    refine ⟨?_, hzc⟩
    change (γ t - c) / (‖γ t - c‖ : ℂ) = (z - c) / (‖z - c‖ : ℂ) at he
    have hz0 : (‖z - c‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 (sub_ne_zero.2 hzc)).ne'
    have hg0 : (‖γ t - c‖ : ℂ) ≠ 0 := by exact_mod_cast (h.norm_pos ht).ne'
    have hzr : z = c + ((‖z - c‖ / ‖γ t - c‖ : ℝ) : ℂ) * (γ t - c) := by
      have e2 : z - c = (‖z - c‖ : ℂ) * ((γ t - c) / (‖γ t - c‖ : ℂ)) := by
        rw [he]; field_simp
      push_cast
      rw [div_mul_eq_mul_div, mul_div_assoc, ← e2]
      ring
    rw [h.radius_eq ht (div_pos (norm_pos_iff.2 (sub_ne_zero.2 hzc)) (h.norm_pos ht)) hzr]
    exact htC

/-! ### The two regions -/

/-- The points nearer to `c` than the path, in their direction (the inside). -/
def inner (γ : ℝ → ℂ) (c : ℂ) : Set ℂ := {z | ‖z - c‖ < radius γ c z}

/-- The points farther from `c` than the path, in their direction (the outside). -/
def outer (γ : ℝ → ℂ) (c : ℂ) : Set ℂ := {z | radius γ c z < ‖z - c‖}

lemma mem_inner {z : ℂ} : z ∈ inner γ c ↔ ‖z - c‖ < radius γ c z := Iff.rfl

lemma mem_outer {z : ℂ} : z ∈ outer γ c ↔ radius γ c z < ‖z - c‖ := Iff.rfl

lemma center_mem_inner (h : IsStarPath γ c φ) : c ∈ inner γ c := by
  rw [mem_inner, sub_self, norm_zero]
  exact h.radius_pos c

lemma ne_of_mem_outer (h : IsStarPath γ c φ) {z : ℂ} (hz : z ∈ outer γ c) : z ≠ c := by
  intro hzc
  rw [hzc, mem_outer, sub_self, norm_zero] at hz
  linarith [h.radius_pos c]

lemma mem_pathImage_iff (h : IsStarPath γ c φ) {z : ℂ} :
    z ∈ pathImage γ ↔ ‖z - c‖ = radius γ c z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [h.radius_eq ht one_pos (by push_cast; ring)]
  · intro hz
    have hzc : z ≠ c := by
      intro hzc
      rw [hzc, sub_self, norm_zero] at hz
      exact (h.radius_pos c).ne hz
    obtain ⟨t, ht, r, hr, hzr, -, hn⟩ := h.exists_ray_radius hzc
    have hr1 : r = 1 := by
      have := h.radius_pos z
      rw [hz] at hn
      nlinarith
    exact ⟨t, ht, by rw [hzr, hr1]; push_cast; ring⟩

lemma ray_mem_inner (h : IsStarPath γ c φ) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Ico (0 : ℝ) 1) : c + s * (γ t - c) ∈ inner γ c := by
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · rw [← hs0]; simpa using h.center_mem_inner
  · rw [mem_inner]
    rw [h.radius_eq ht hs0 rfl, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs0]
    have := h.norm_pos ht
    nlinarith [hs.2]

lemma mem_outer_iff (h : IsStarPath γ c φ) {z : ℂ} :
    z ∈ outer γ c ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ s : ℝ, 1 < s ∧ z = c + s * (γ t - c) := by
  constructor
  · intro hz
    obtain ⟨t, ht, r, hr, hzr, -, hn⟩ := h.exists_ray_radius (h.ne_of_mem_outer hz)
    refine ⟨t, ht, r, ?_, hzr⟩
    have h1 : radius γ c z < r * radius γ c z := hn ▸ hz
    have := h.radius_pos z
    nlinarith
  · rintro ⟨t, ht, s, hs, rfl⟩
    rw [mem_outer]
    rw [h.radius_eq ht (by linarith) rfl, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    have := h.norm_pos ht
    nlinarith

lemma mem_inner_or (h : IsStarPath γ c φ) (z : ℂ) :
    z ∈ inner γ c ∨ z ∈ pathImage γ ∨ z ∈ outer γ c := by
  rcases lt_trichotomy ‖z - c‖ (radius γ c z) with hz | hz | hz
  · exact Or.inl hz
  · exact Or.inr (Or.inl (h.mem_pathImage_iff.2 hz))
  · exact Or.inr (Or.inr hz)

lemma disjoint_inner_pathImage (h : IsStarPath γ c φ) : Disjoint (inner γ c) (pathImage γ) := by
  rw [Set.disjoint_left]
  intro z hz hp
  exact (ne_of_lt hz) (h.mem_pathImage_iff.1 hp)

lemma disjoint_outer_pathImage (h : IsStarPath γ c φ) : Disjoint (outer γ c) (pathImage γ) := by
  rw [Set.disjoint_left]
  intro z hz hp
  exact (ne_of_lt hz).symm (h.mem_pathImage_iff.1 hp)

lemma disjoint_inner_outer : Disjoint (inner γ c) (outer γ c) := by
  rw [Set.disjoint_left]
  intro z hz ho
  exact lt_asymm (mem_inner.1 hz) (mem_outer.1 ho)

lemma isOpen_outer (h : IsStarPath γ c φ) : IsOpen (outer γ c) := by
  have e : outer γ c = {c}ᶜ ∩ (fun z => radius γ c z - ‖z - c‖) ⁻¹' Iio 0 := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_compl_iff, mem_singleton_iff, sub_neg]
    exact ⟨fun hz => ⟨h.ne_of_mem_outer hz, hz⟩, fun hz => hz.2⟩
  rw [e]
  exact (h.continuousOn_radius.sub (continuousOn_id.sub continuousOn_const).norm).isOpen_inter_preimage
    isOpen_compl_singleton isOpen_Iio

lemma isOpen_inner (h : IsStarPath γ c φ) : IsOpen (inner γ c) := by
  obtain ⟨m, M, hm, hb⟩ := h.exists_radius_bounds
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  by_cases hzc : z = c
  · refine ⟨ball c m, fun y hy => ?_, isOpen_ball, hzc ▸ mem_ball_self hm⟩
    rw [mem_inner]
    rw [mem_ball, dist_eq_norm] at hy
    exact hy.trans_le (hb y).1
  · refine ⟨{c}ᶜ ∩ (fun z => ‖z - c‖ - radius γ c z) ⁻¹' Iio 0, fun y hy => ?_,
      ((continuousOn_id.sub continuousOn_const).norm.sub h.continuousOn_radius).isOpen_inter_preimage
        isOpen_compl_singleton isOpen_Iio, ⟨hzc, ?_⟩⟩
    · have := hy.2
      simp only [mem_preimage, mem_Iio, sub_neg] at this
      exact this
    · simp only [mem_preimage, mem_Iio, sub_neg]
      exact hz

/-- The inner region is star-convex about `c`. -/
lemma starConvex_inner (h : IsStarPath γ c φ) : StarConvex ℝ c (inner γ c) := by
  intro y hy a b ha hb hab
  have e : a • c + b • y = c + (b : ℂ) * (y - c) := by
    rw [Complex.real_smul, Complex.real_smul, show a = 1 - b by linarith]
    push_cast; ring
  rw [e]
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · rw [← hb0]; simpa using h.center_mem_inner
  by_cases hyc : y = c
  · rw [hyc, sub_self, mul_zero, add_zero]; exact h.center_mem_inner
  rw [mem_inner]
  rw [h.radius_smul hyc hb0, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hb0]
  have hy' : ‖y - c‖ < radius γ c y := hy
  have hb1 : b ≤ 1 := by linarith
  nlinarith [norm_nonneg (y - c)]

lemma outer_eq_image (h : IsStarPath γ c φ) :
    outer γ c = (fun p : ℝ × ℝ => c + p.1 * (γ p.2 - c)) '' (Ioi 1 ×ˢ Icc 0 1) := by
  ext z
  rw [h.mem_outer_iff]
  constructor
  · rintro ⟨t, ht, s, hs, rfl⟩
    exact ⟨(s, t), ⟨hs, ht⟩, rfl⟩
  · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    exact ⟨t, ht, s, hs, rfl⟩

lemma isBounded_inner (h : IsStarPath γ c φ) : Bornology.IsBounded (inner γ c) := by
  obtain ⟨m, M, -, hb⟩ := h.exists_radius_bounds
  refine (isBounded_closedBall (x := c) (r := M)).subset fun z hz => ?_
  rw [mem_closedBall, dist_eq_norm]
  exact (le_of_lt hz).trans (hb z).2

lemma pathImage_subset_closure_inner (h : IsStarPath γ c φ) :
    pathImage γ ⊆ closure (inner γ c) := by
  rintro _ ⟨t, ht, rfl⟩
  have hl : Tendsto (fun s : ℝ => c + s * (γ t - c)) (𝓝[<] 1) (𝓝 (γ t)) := by
    have : Tendsto (fun s : ℝ => c + s * (γ t - c)) (𝓝 1) (𝓝 (c + (1 : ℝ) * (γ t - c))) :=
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 1)
    rw [show c + ((1 : ℝ) : ℂ) * (γ t - c) = γ t by push_cast; ring] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hl ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact h.ray_mem_inner ht ⟨hs.1.le, hs.2⟩

lemma pathImage_subset_closure_outer (h : IsStarPath γ c φ) :
    pathImage γ ⊆ closure (outer γ c) := by
  rintro _ ⟨t, ht, rfl⟩
  have hl : Tendsto (fun s : ℝ => c + s * (γ t - c)) (𝓝[>] 1) (𝓝 (γ t)) := by
    have : Tendsto (fun s : ℝ => c + s * (γ t - c)) (𝓝 1) (𝓝 (c + (1 : ℝ) * (γ t - c))) :=
      ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 1)
    rw [show c + ((1 : ℝ) : ℂ) * (γ t - c) = γ t by push_cast; ring] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hl ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact h.mem_outer_iff.2 ⟨t, ht, s, hs, rfl⟩

/-- **The inside of a star-shaped path is the inner region.** -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem insideOf_eq_inner (h : IsStarPath γ c φ) : insideOf γ = inner γ c := by
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    rcases h.mem_inner_or z with hi | hp | ho
    · exact hi
    · exact absurd hp hz
    · exfalso
      obtain ⟨t, ht, r, hr, rfl⟩ := h.mem_outer_iff.1 ho
      refine not_isBounded_connectedComponentIn_of_ray (sub_ne_zero.2 (h.ne t ht))
        (fun u hu hm => ?_) hb
      have hmo : c + (r : ℂ) * (γ t - c) + u * (γ t - c) ∈ outer γ c :=
        h.mem_outer_iff.2 ⟨t, ht, r + u, by linarith, by push_cast; ring⟩
      exact Set.disjoint_left.1 h.disjoint_outer_pathImage hmo hm
  · intro hz
    have hz' : z ∉ pathImage γ := fun hm => Set.disjoint_left.1 h.disjoint_inner_pathImage hz hm
    refine ⟨hz', ?_⟩
    have hsub : connectedComponentIn (pathImage γ)ᶜ z ⊆ inner γ c := by
      refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset h.isOpen_inner
        ⟨z, mem_connectedComponentIn hz', hz⟩ ?_
      rintro y ⟨hy1, hy2⟩
      have hyc : y ∈ (outer γ c)ᶜ := by
        exact closure_minimal (fun x hx => Set.disjoint_left.1 disjoint_inner_outer hx)
          h.isOpen_outer.isClosed_compl hy1
      rcases h.mem_inner_or y with hi | hp | ho
      · exact hi
      · exact absurd hp (connectedComponentIn_subset _ _ hy2)
      · exact absurd ho hyc
    exact h.isBounded_inner.subset hsub

/-- **The Jordan curve theorem for star-shaped paths** (Beck, Section 4.4, assumed there in
general): for every closed path that is star-shaped about a point `c`, the complement of the path is
the union of the inner and the outer region; these are disjoint, open and connected, the first is
bounded and the second is not, and the path is the frontier of each. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem jordan_curve_star (h : IsStarPath γ c φ) :
    (pathImage γ)ᶜ = inner γ c ∪ outer γ c ∧ Disjoint (inner γ c) (outer γ c) ∧
    IsOpen (inner γ c) ∧ IsOpen (outer γ c) ∧ IsConnected (inner γ c) ∧
    IsConnected (outer γ c) ∧ Bornology.IsBounded (inner γ c) ∧
    ¬ Bornology.IsBounded (outer γ c) ∧
    frontier (inner γ c) = pathImage γ ∧ frontier (outer γ c) = pathImage γ := by
  have hpi := h.disjoint_inner_pathImage
  have hpo := h.disjoint_outer_pathImage
  have hcl_i : closure (inner γ c) ⊆ (outer γ c)ᶜ :=
    closure_minimal (fun x hx => Set.disjoint_left.1 disjoint_inner_outer hx)
      h.isOpen_outer.isClosed_compl
  have hcl_o : closure (outer γ c) ⊆ (inner γ c)ᶜ :=
    closure_minimal (fun x hx => Set.disjoint_right.1 disjoint_inner_outer hx)
      h.isOpen_inner.isClosed_compl
  refine ⟨?_, disjoint_inner_outer, h.isOpen_inner, h.isOpen_outer,
    (h.starConvex_inner.isPathConnected h.center_mem_inner).isConnected, ?_, h.isBounded_inner,
    ?_, ?_, ?_⟩
  · ext z
    simp only [mem_compl_iff, mem_union]
    constructor
    · intro hz
      rcases h.mem_inner_or z with hi | hp | ho
      · exact Or.inl hi
      · exact absurd hp hz
      · exact Or.inr ho
    · rintro (hi | ho) hp
      · exact Set.disjoint_left.1 hpi hi hp
      · exact Set.disjoint_left.1 hpo ho hp
  · rw [h.outer_eq_image]
    exact (isConnected_Ioi.prod (isConnected_Icc zero_le_one)).image _ h.continuousOn_ray
  · intro hb
    have hu : Bornology.IsBounded (inner γ c ∪ pathImage γ ∪ outer γ c) :=
      (h.isBounded_inner.union (isCompact_pathImage h.cont).isBounded).union hb
    have : inner γ c ∪ pathImage γ ∪ outer γ c = univ := by
      ext z
      simp only [mem_union, mem_univ, iff_true]
      rcases h.mem_inner_or z with hi | hp | ho
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hp)
      · exact Or.inr ho
    rw [this] at hu
    exact NormedSpace.unbounded_univ ℝ ℂ hu
  · rw [frontier, h.isOpen_inner.interior_eq]
    refine Subset.antisymm (fun z ⟨hz1, hz2⟩ => ?_) (fun z hz => ⟨h.pathImage_subset_closure_inner hz,
      fun hi => Set.disjoint_left.1 hpi hi hz⟩)
    rcases h.mem_inner_or z with hi | hp | ho
    · exact absurd hi hz2
    · exact hp
    · exact absurd ho (hcl_i hz1)
  · rw [frontier, h.isOpen_outer.interior_eq]
    refine Subset.antisymm (fun z ⟨hz1, hz2⟩ => ?_) (fun z hz => ⟨h.pathImage_subset_closure_outer hz,
      fun ho => Set.disjoint_left.1 hpo ho hz⟩)
    rcases h.mem_inner_or z with hi | hp | ho
    · exact absurd hi (hcl_o hz1)
    · exact hp
    · exact absurd ho hz2

/-! ### The retraction onto the closed star region -/

/-- The retraction of the plane onto the closed star region: a point outside is moved along its
ray from `c` onto the path; points of the closed region are fixed. -/
noncomputable def retract (γ : ℝ → ℂ) (c : ℂ) (z : ℂ) : ℂ :=
  c + ((min 1 (radius γ c z / ‖z - c‖) : ℝ) : ℂ) * (z - c)

lemma retract_eq_self (_h : IsStarPath γ c φ) {z : ℂ} (hz : ‖z - c‖ ≤ radius γ c z) :
    retract γ c z = z := by
  by_cases hzc : z = c
  · rw [hzc, retract, sub_self, mul_zero, add_zero]
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  have h1 : min 1 (radius γ c z / ‖z - c‖) = 1 :=
    min_eq_left ((one_le_div hpos).2 hz)
  rw [retract, h1]
  push_cast
  ring

lemma retract_of_lt (h : IsStarPath γ c φ) {z : ℂ} (hz : radius γ c z < ‖z - c‖) :
    ‖retract γ c z - c‖ = radius γ c (retract γ c z) := by
  have hzc : z ≠ c := h.ne_of_mem_outer hz
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  have hl : radius γ c z / ‖z - c‖ < 1 := (div_lt_one hpos).2 hz
  have hl0 : 0 < radius γ c z / ‖z - c‖ := div_pos (h.radius_pos z) hpos
  have h1 : min 1 (radius γ c z / ‖z - c‖) = radius γ c z / ‖z - c‖ := min_eq_right hl.le
  rw [retract, h1, h.radius_smul hzc hl0, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hl0, div_mul_cancel₀ _ hpos.ne']

lemma retract_mem (h : IsStarPath γ c φ) (z : ℂ) :
    retract γ c z ∈ inner γ c ∪ pathImage γ := by
  by_cases hz : ‖z - c‖ ≤ radius γ c z
  · rw [h.retract_eq_self hz]
    rcases eq_or_lt_of_le hz with he | hl
    · exact Or.inr (h.mem_pathImage_iff.2 he)
    · exact Or.inl hl
  · exact Or.inr (h.mem_pathImage_iff.2 (h.retract_of_lt (not_le.1 hz)))

lemma continuous_retract (h : IsStarPath γ c φ) : Continuous (retract γ c) := by
  obtain ⟨m, M, hm, hb⟩ := h.exists_radius_bounds
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hzc : z = c
  · subst hzc
    refine continuousAt_id.congr ?_
    filter_upwards [ball_mem_nhds z hm] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (h.retract_eq_self (hy.le.trans (hb y).1)).symm
  · have hc : ContinuousOn (retract γ c) {c}ᶜ := by
      refine continuousOn_const.add (ContinuousOn.mul ?_ (continuousOn_id.sub continuousOn_const))
      refine continuous_ofReal.comp_continuousOn (continuous_min.comp_continuousOn (continuousOn_const.prodMk ?_))
      refine h.continuousOn_radius.div (continuousOn_id.sub continuousOn_const).norm ?_
      intro y hy
      exact (norm_pos_iff.2 (sub_ne_zero.2 hy)).ne'
    exact hc.continuousAt (isOpen_compl_singleton.mem_nhds hzc)

/-! ### The annulus homotopy -/

/-- In the plane minus the open disc `D(w, R)`, the path is homotopic to the circle `C[w, R]`
whenever the closed disc lies in the inner region: radial projection from `w`, then moving the
centre of projection along the segment from `w` to `c` (inside the star-convex inner region), then
a homotopy of angles. -/
theorem annulus_homotopy_plane (h : IsStarPath γ c φ) {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : closedBall w R ⊆ inner γ c) :
    IsGHomotopic (univ \ ball w R) γ (circlePath w R) := by
  have hw : w ∈ inner γ c := hsub (mem_closedBall_self hR.le)
  have hpi := h.disjoint_inner_pathImage
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ pathImage γ := fun t ht => ⟨t, ht, rfl⟩
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hS
  have hγw : ∀ t ∈ Icc (0 : ℝ) 1, R < ‖γ t - w‖ := by
    intro t ht
    by_contra hcon
    push Not at hcon
    exact Set.disjoint_left.1 hpi (hsub (mem_closedBall.2 (by rw [dist_eq_norm]; exact hcon)))
      (hmem t ht)
  have hγw0 : ∀ t ∈ Icc (0 : ℝ) 1, (‖γ t - w‖ : ℂ) ≠ 0 := fun t ht => by
    exact_mod_cast (hR.trans (hγw t ht)).ne'
  have hsph : ∀ z : ℂ, ‖z - w‖ = R → z ∈ univ \ ball w R := fun z hz =>
    ⟨mem_univ _, fun hb => by rw [mem_ball, dist_eq_norm, hz] at hb; exact lt_irrefl R hb⟩
  have hnc : ∀ x : ℂ, x ≠ 0 → ‖x / (‖x‖ : ℂ)‖ = 1 := fun x hx => by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 hx)]
  have hγ1 : ContinuousOn (fun q : ℝ × ℝ => γ q.1) S :=
    h.cont.comp continuousOn_fst (fun q (hq : q ∈ S) => hq.1)
  -- first stage: radial projection from `w`
  set u : ℝ → ℂ := fun t => (γ t - w) / (‖γ t - w‖ : ℂ) with hu
  have hun : ∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ = 1 := fun t ht =>
    hnc _ (fun e => hγw0 t ht (by rw [e, norm_zero, ofReal_zero]))
  have hγu : ∀ t ∈ Icc (0 : ℝ) 1, γ t = w + ‖γ t - w‖ * u t := fun t ht => by
    simp only [hu]
    rw [mul_div_cancel₀ _ (hγw0 t ht)]
    ring
  have h1 : IsGHomotopic (univ \ ball w R) γ (fun t => w + R * u t) := by
    refine ⟨fun t s => w + (((1 - s) * ‖γ t - w‖ + s * R : ℝ) : ℂ) * u t, ?_, ?_, ?_, ?_, ?_⟩
    · have hn : ContinuousOn (fun q : ℝ × ℝ => ‖γ q.1 - w‖) S := (hγ1.sub continuousOn_const).norm
      have huq : ContinuousOn (fun q : ℝ × ℝ => u q.1) S :=
        (hγ1.sub continuousOn_const).div (continuous_ofReal.comp_continuousOn hn)
          (fun q hq => hγw0 q.1 hq.1)
      refine continuousOn_const.add (ContinuousOn.mul ?_ huq)
      exact continuous_ofReal.comp_continuousOn
        (((continuousOn_const.sub continuousOn_snd).mul hn).add
          (continuousOn_snd.mul continuousOn_const))
    · intro t ht s hs
      have hd := hγw t ht
      refine ⟨mem_univ _, ?_⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hun t ht, mul_one,
        Complex.norm_real, Real.norm_eq_abs, not_lt]
      rw [abs_of_nonneg (by nlinarith [hs.1, hs.2])]
      nlinarith [hs.1, hs.2]
    · intro t ht
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact (hγu t ht).symm
    · intro t _
      simp
    · intro s _
      simp only [hu, h.closed]
  -- second stage: move the centre of projection from `w` to `c`
  set v : ℝ → ℂ := fun s => w + s * (c - w) with hv
  have hvK : ∀ s ∈ Icc (0 : ℝ) 1, v s ∈ inner γ c := fun s hs => by
    have := h.starConvex_inner hw hs.1 (sub_nonneg.2 hs.2) (by ring : s + (1 - s) = 1)
    convert this using 1
    rw [Complex.real_smul, Complex.real_smul]
    push_cast; ring
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, γ t - v s ≠ 0 := fun t ht s hs e =>
    Set.disjoint_left.1 hpi (sub_eq_zero.1 e ▸ hvK s hs) (hmem t ht)
  have h2 : IsGHomotopic (univ \ ball w R) (fun t => w + R * u t)
      (fun t => w + R * exp (φ t * I)) := by
    refine ⟨fun t s => w + R * ((γ t - v s) / (‖γ t - v s‖ : ℂ)), ?_, ?_, ?_, ?_, ?_⟩
    · have hf : ContinuousOn (fun q : ℝ × ℝ => γ q.1 - v q.2) S :=
        hγ1.sub (continuousOn_const.add
          ((continuous_ofReal.comp_continuousOn continuousOn_snd).mul continuousOn_const))
      refine continuousOn_const.add (continuousOn_const.mul ?_)
      refine hf.div (continuous_ofReal.comp_continuousOn hf.norm) (fun q hq => ?_)
      exact_mod_cast norm_ne_zero_iff.2 (hne q.1 hq.1 q.2 hq.2)
    · intro t ht s hs
      refine hsph _ ?_
      rw [add_sub_cancel_left, norm_mul, hnc _ (hne t ht s hs), Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, mul_one]
    · intro t _
      simp [hv, hu]
    · intro t ht
      have e := h.sub_eq ht
      have hN : (‖γ t - c‖ : ℂ) ≠ 0 := by exact_mod_cast (h.norm_pos ht).ne'
      simp only [hv, ofReal_one, one_mul, add_sub_cancel]
      have e2 : (γ t - c) / (‖γ t - c‖ : ℂ) = exp (φ t * I) := by
        rw [div_eq_iff hN, mul_comm]
        exact e
      rw [e2]
    · intro s _
      simp only [h.closed]
  -- third stage: a homotopy of angles on the circle
  have h3 : IsGHomotopic (univ \ ball w R) (fun t => w + R * exp (φ t * I)) (circlePath w R) := by
    have hcl : w + (R : ℂ) * exp (φ 0 * I) = w + R * exp (φ 1 * I) := by
      rw [h.angle_one]
      push_cast
      rw [add_mul, exp_add, show (2 * (π : ℂ)) * I = 2 * π * I by ring, exp_two_pi_mul_I, mul_one]
    have hnr : ∀ t : ℝ, ‖w + (R : ℂ) * exp (φ t * I) - w‖ = R := fun t => by
      rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, mul_one]
    exact isGHomotopic_circlePath_of_angle (K := univ) convex_univ
      (γ := fun t => w + R * exp (φ t * I))
      (continuousOn_const.add (continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn
        ((continuous_ofReal.comp_continuousOn h.angle_cont).mul continuousOn_const)))) hcl hR
      (subset_univ _) (fun t _ => mem_univ _) (fun t _ => (hnr t).ge)
      h.angle_cont (fun t _ => by simp only [hnr]) h.angle_one
  exact h1.trans (h2.trans h3)

/-- **The annulus homotopy for star-shaped paths.** For a closed disc `D[w, R]` inside the path,
the path is homotopic to the circle `C[w, R]` within the closed inside minus the open disc: the
homotopy in the plane minus the disc (`annulus_homotopy_plane`) composed with the retraction onto
the closed star region. -/
theorem annulus_homotopy_star (h : IsStarPath γ c φ) {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : closedBall w R ⊆ inner γ c) :
    IsGHomotopic ((inner γ c ∪ pathImage γ) \ ball w R) γ (circlePath w R) := by
  obtain ⟨H, hc, hm, h0, h1, hcl⟩ := h.annulus_homotopy_plane hR hsub
  have hpi := h.disjoint_inner_pathImage
  refine ⟨fun t s => retract γ c (H t s), h.continuous_retract.comp_continuousOn hc, ?_, ?_, ?_, ?_⟩
  · intro t ht s hs
    have hH := (hm t ht s hs).2
    refine ⟨h.retract_mem _, ?_⟩
    show retract γ c (H t s) ∉ ball w R
    by_cases hz : ‖H t s - c‖ ≤ radius γ c (H t s)
    · rw [h.retract_eq_self hz]; exact hH
    · intro hb
      have hp := h.mem_pathImage_iff.2 (h.retract_of_lt (not_le.1 hz))
      exact Set.disjoint_left.1 hpi (hsub (ball_subset_closedBall hb)) hp
  · intro t ht
    simp only
    rw [h0 t ht]
    exact h.retract_eq_self (h.mem_pathImage_iff.1 ⟨t, ht, rfl⟩).le
  · intro t ht
    simp only
    rw [h1 t ht]
    refine h.retract_eq_self (le_of_lt (hsub ?_))
    rw [mem_closedBall, dist_eq_norm, circlePath_eq, add_sub_cancel_left, norm_mul,
      norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, mul_one]
  · intro s hs
    simp only
    rw [hcl s hs]

/-- **Star-shaped paths are positively oriented simple closed paths.** Every piecewise smooth
closed path that is star-shaped about a point (`IsStarPath`) satisfies
`IsPositivelyOrientedSimpleClosed` (Definition 4.4.4), with both fields that the book assumes in
Section 4.4 proved: its inside is the inner region, and the annulus homotopy exists. So Cauchy's
integral formula 4.4.5, the residue theorem 9.2.2, the argument principle 9.3.2 and Rouché's
theorem 9.3.3 apply to it unconditionally. No convexity is needed (compare
`IsStarPath.isPositivelyOrientedSimpleClosed`). -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem isPositivelyOrientedSimpleClosed_star (h : IsStarPath γ c φ)
    (hs : IsPiecewiseSmooth γ 0 1) : IsPositivelyOrientedSimpleClosed γ where
  smooth := hs
  closed := h.closed
  simple := h.injOn
  inside_nonempty := ⟨c, by rw [h.insideOf_eq_inner]; exact h.center_mem_inner⟩
  annulus := by
    intro w R hR hsub
    rw [h.insideOf_eq_inner] at hsub ⊢
    exact h.annulus_homotopy_star hR hsub

end IsStarPath

end UndergradKB.ComplexAnalysis
