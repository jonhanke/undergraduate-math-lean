import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Connected.LocallyConnected
import UndergradKB.ComplexAnalysis.HomotopyGeneral

/-!
# Cauchy's integral formula for simple closed paths (rows CX-070, CX-071, CX-072, CX-073)

Beck et al., Section 4.4, *assume* two theorems of topology: the Jordan curve theorem (a simple
closed path has an inside) and the annulus theorem (if `γ` is positively oriented and the closed
disc `D[w, R]` lies inside `γ`, there is a homotopy from `γ` to the counterclockwise circle
`C[w, R]` staying inside `γ` or on `γ` and away from the open disc). Neither is in Mathlib.

Here `insideOf γ` is defined directly (the points off the path whose connected component of the
complement of the path is bounded; it is open), and the book's assumptions are recorded as the
named fields `inside_nonempty` and `annulus` of the structure `IsPositivelyOrientedSimpleClosed`
(Definition 4.4.4). The structure is satisfied by every counterclockwise circle
(`isPositivelyOrientedSimpleClosed_circlePath`, proved), so it is not vacuous. From it, with
Cauchy's theorem for continuous homotopies, the book's proofs give:

* Proposition 4.4.6: `G` contains the inside of `γ` if and only if `γ` is `G`-contractible;
* Theorem 4.4.5 (Cauchy's integral formula) and Example 4.4.7;
* Theorem 5.1.1 (Cauchy's integral formula for derivatives), from Mathlib's circle version.
-/

open Set Metric Complex Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-! ### The circle parametrised on `[0, 1]` -/

/-- The counterclockwise circle `C[c, R]` parametrised on `[0, 1]`. -/
noncomputable def circlePath (c : ℂ) (R : ℝ) (t : ℝ) : ℂ := circleMap c R (2 * π * t)

lemma circlePath_eq (c : ℂ) (R t : ℝ) :
    circlePath c R t = c + R * exp ((2 * π * t : ℝ) * I) := rfl

lemma deriv_circlePath (c : ℂ) (R t : ℝ) :
    deriv (circlePath c R) t = 2 * π * deriv (circleMap c R) (2 * π * t) := by
  have := deriv_comp_mul_left (f := circleMap c R) (c := 2 * π) (x := t)
  rw [show circlePath c R = fun t => circleMap c R (2 * π * t) from rfl, this, Complex.real_smul]
  push_cast; ring

lemma isC1On_circlePath (c : ℂ) (R a b : ℝ) : IsC1On (circlePath c R) a b := by
  have hd : ∀ t, HasDerivAt (circlePath c R) (2 * π * deriv (circleMap c R) (2 * π * t)) t := by
    intro t
    have h2 : HasDerivAt (fun t : ℝ => 2 * π * t) (2 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * π)
    have h3 := (hasDerivAt_circleMap c R (2 * π * t)).scomp t h2
    rw [deriv_circleMap]
    have h4 : HasDerivAt (circlePath c R) ((2 * π) • (circleMap 0 R (2 * π * t) * I)) t := h3
    rw [Complex.real_smul] at h4
    convert h4 using 1
    push_cast; ring
  refine ⟨fun t _ => (hd t).differentiableAt, ?_⟩
  have : deriv (circlePath c R) = fun t => 2 * π * (circleMap 0 R (2 * π * t) * I) := by
    funext t; rw [deriv_circlePath, deriv_circleMap]
  rw [this]
  exact (continuous_const.mul (((continuous_circleMap 0 R).comp
    (continuous_const.mul continuous_id)).mul continuous_const)).continuousOn

lemma isPiecewiseSmooth_circlePath (c : ℂ) (R : ℝ) : IsPiecewiseSmooth (circlePath c R) 0 1 :=
  (isC1On_circlePath c R 0 1).isPiecewiseSmooth zero_le_one

lemma circlePath_closed (c : ℂ) (R : ℝ) : circlePath c R 0 = circlePath c R 1 := by
  simp only [circlePath, mul_zero, mul_one]
  exact (periodic_circleMap c R 0).symm.trans (by rw [zero_add])

/-- The integral along `circlePath c R` on `[0, 1]` is Mathlib's circle integral. -/
theorem pathIntegral_circlePath (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    pathIntegral f (circlePath c R) 0 1 = ∮ z in C(c, R), f z := by
  rw [← pathIntegral_circleMap]
  unfold pathIntegral
  simp only [deriv_circlePath, circlePath]
  have e : ∀ t : ℝ, f (circleMap c R (2 * π * t)) * (2 * π * deriv (circleMap c R) (2 * π * t))
      = (2 * π : ℂ) * (fun u : ℝ => f (circleMap c R u) * deriv (circleMap c R) u) (2 * π * t) := by
    intro t; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun u : ℝ => f (circleMap c R u) *
      deriv (circleMap c R) u) (by positivity : (2 * π : ℝ) ≠ 0)]
  simp only [mul_zero, mul_one, Complex.real_smul]
  push_cast
  field_simp

lemma circlePath_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    circlePath c R t ∈ sphere c R := by
  have := circleMap_mem_sphere c hR (2 * π * t)
  exact this

/-! ### The inside of a closed path -/

/-- The image of a path on `[0, 1]`. -/
def pathImage (γ : ℝ → ℂ) : Set ℂ := γ '' Icc 0 1

/-- The inside of the closed path `γ`: the points off `γ` whose connected component in the
complement of `γ` is bounded. (The Jordan curve theorem says that for a simple closed path this is
one of the two components of the complement.) -/
def insideOf (γ : ℝ → ℂ) : Set ℂ :=
  {w | w ∉ pathImage γ ∧ Bornology.IsBounded (connectedComponentIn (pathImage γ)ᶜ w)}

lemma isCompact_pathImage {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) :
    IsCompact (pathImage γ) :=
  isCompact_Icc.image_of_continuousOn hγ

/-- The inside of a path is open. -/
theorem isOpen_insideOf {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) : IsOpen (insideOf γ) := by
  have hS : IsOpen (pathImage γ)ᶜ := (isCompact_pathImage hγ).isClosed.isOpen_compl
  refine isOpen_iff_forall_mem_open.2 (fun w hw => ⟨connectedComponentIn (pathImage γ)ᶜ w,
    fun z hz => ⟨connectedComponentIn_subset _ _ hz, ?_⟩, hS.connectedComponentIn,
    mem_connectedComponentIn hw.1⟩)
  rw [← connectedComponentIn_eq hz]
  exact hw.2

lemma insideOf_disjoint {γ : ℝ → ℂ} {w : ℂ} (hw : w ∈ insideOf γ) : w ∉ pathImage γ := hw.1

/-! ### Positively oriented simple closed paths -/

/-- Beck Definition 4.4.4 (CX-070), with the topology the book assumes in Section 4.4 as named
fields: a positively oriented, simple, closed, piecewise smooth path `γ` on `[0, 1]`.
`inside_nonempty` is the part of the Jordan curve theorem used (the inside is not empty) and
`annulus` is the annulus theorem with the orientation: for every closed disc `D[w, R]` inside `γ`
there is a homotopy from `γ` to the counterclockwise circle `C[w, R]` within the inside of `γ` and
`γ` itself, avoiding the open disc of radius `R` about `w` (Beck p. 83). -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
structure IsPositivelyOrientedSimpleClosed (γ : ℝ → ℂ) : Prop where
  smooth : IsPiecewiseSmooth γ 0 1
  closed : γ 0 = γ 1
  simple : InjOn γ (Ico 0 1)
  inside_nonempty : (insideOf γ).Nonempty
  annulus : ∀ (w : ℂ) (R : ℝ), 0 < R → closedBall w R ⊆ insideOf γ →
    IsGHomotopic ((insideOf γ ∪ pathImage γ) \ ball w R) γ (circlePath w R)

/-- `G`-homotopy is monotone in `G`. -/
lemma IsGHomotopic.mono {G G' : Set ℂ} {γ₀ γ₁ : ℝ → ℂ} (h : IsGHomotopic G γ₀ γ₁)
    (hG : G ⊆ G') : IsGHomotopic G' γ₀ γ₁ := by
  obtain ⟨h, hc, hm, h0, h1, hcl⟩ := h
  exact ⟨h, hc, fun t ht s hs => hG (hm t ht s hs), h0, h1, hcl⟩

/-- The trace of a path is contained in any set through which it is homotopic to something. -/
lemma IsGHomotopic.mem_left {G : Set ℂ} {γ₀ γ₁ : ℝ → ℂ} (h : IsGHomotopic G γ₀ γ₁) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ₀ t ∈ G := by
  obtain ⟨h, -, hm, h0, -, -⟩ := h
  intro t ht
  rw [← h0 t ht]
  exact hm t ht 0 ⟨le_rfl, zero_le_one⟩

namespace IsPositivelyOrientedSimpleClosed

variable {γ : ℝ → ℂ}

lemma isOpen_inside (hγ : IsPositivelyOrientedSimpleClosed γ) : IsOpen (insideOf γ) :=
  isOpen_insideOf hγ.smooth.continuousOn

/-- Around every point inside `γ` there is a closed disc inside `γ`. -/
lemma exists_closedBall (hγ : IsPositivelyOrientedSimpleClosed γ) {w : ℂ} (hw : w ∈ insideOf γ) :
    ∃ R > 0, closedBall w R ⊆ insideOf γ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hγ.isOpen_inside w hw
  exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩

/-- The integral of `1 / (z - w)` along `γ` is `2 π i` for every `w` inside `γ`
(by the annulus homotopy and Cauchy's theorem). -/
theorem pathIntegral_inv_sub (hγ : IsPositivelyOrientedSimpleClosed γ) {w : ℂ}
    (hw : w ∈ insideOf γ) :
    pathIntegral (fun z => (z - w)⁻¹) γ 0 1 = 2 * π * I := by
  obtain ⟨R, hR, hRin⟩ := hγ.exists_closedBall hw
  have hH : ((insideOf γ ∪ pathImage γ) \ ball w R) ⊆ {w}ᶜ := by
    rintro z ⟨-, hz⟩ rfl
    exact hz (mem_ball_self hR)
  have hd : DifferentiableOn ℂ (fun z => (z - w)⁻¹) {w}ᶜ := fun z hz =>
    ((differentiableAt_id.sub_const w).inv (sub_ne_zero.2 hz)).differentiableWithinAt
  rw [cauchy_theorem_homotopy isOpen_compl_singleton hd hγ.smooth
    (isPiecewiseSmooth_circlePath w R) ((hγ.annulus w R hR hRin).mono hH),
    pathIntegral_circlePath]
  exact circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR)

/-- Beck Proposition 4.4.6 (CX-072), the direction proved in the book by contradiction: if the
simple closed path `γ` is `G`-contractible then `G` contains the inside of `γ`. -/
@[kb "beck2025" "Proposition 4.4.6, p. 84"]
theorem inside_subset_of_contractible (hγ : IsPositivelyOrientedSimpleClosed γ) {G : Set ℂ}
    (hG : IsOpen G) {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) : insideOf γ ⊆ G := by
  intro w hw
  by_contra hwG
  have hd : DifferentiableOn ℂ (fun z => (z - w)⁻¹) G := fun z hz =>
    ((differentiableAt_id.sub_const w).inv
      (sub_ne_zero.2 (fun h => hwG (h ▸ hz)))).differentiableWithinAt
  have h0 := pathIntegral_eq_zero_of_contractible hG hd hγ.smooth hc
  rw [hγ.pathIntegral_inv_sub hw] at h0
  simp [Real.pi_ne_zero, I_ne_zero] at h0

end IsPositivelyOrientedSimpleClosed

/-! ### The circle is a positively oriented simple closed path -/

section Circle

variable {c : ℂ} {r : ℝ}

lemma pathImage_circlePath_subset (hr : 0 ≤ r) : pathImage (circlePath c r) ⊆ sphere c r := by
  rintro _ ⟨t, -, rfl⟩
  exact circlePath_mem_sphere c hr t

lemma ball_subset_insideOf_circlePath (hr : 0 < r) : ball c r ⊆ insideOf (circlePath c r) := by
  intro w hw
  have hnot : w ∉ pathImage (circlePath c r) := fun h => by
    have := pathImage_circlePath_subset hr.le h
    rw [mem_sphere] at this
    rw [mem_ball] at hw
    linarith
  refine ⟨hnot, (Metric.isBounded_ball : Bornology.IsBounded (ball c r)).subset ?_⟩
  -- the ball is clopen in the complement of the circle
  have hsub : connectedComponentIn (pathImage (circlePath c r))ᶜ w ⊆
      ball c r ∪ {z | r < dist z c} := by
    intro z hz
    have hz' := connectedComponentIn_subset _ _ hz
    rcases lt_trichotomy (dist z c) r with h | h | h
    · exact Or.inl h
    · exfalso
      apply hz'
      -- z lies on the circle
      have : z ∈ sphere c r := h
      have himg : sphere c |r| = circleMap c r '' Ioc 0 (2 * π) := (image_circleMap_Ioc c r).symm
      rw [abs_of_pos hr] at himg
      rw [himg] at this
      obtain ⟨θ, hθ, rfl⟩ := this
      refine ⟨θ / (2 * π), ⟨by positivity [hθ.1.le], ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; exact hθ.2
      · simp only [circlePath]
        congr 1
        field_simp
    · exact Or.inr h
  exact (isPreconnected_connectedComponentIn).subset_left_of_subset_union isOpen_ball
    (isOpen_lt continuous_const (continuous_id.dist continuous_const))
    (by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      rw [mem_ball] at hz1
      exact lt_asymm hz1 hz2)
    hsub ⟨w, mem_connectedComponentIn hnot, hw⟩

lemma insideOf_circlePath_subset_ball (hr : 0 < r) : insideOf (circlePath c r) ⊆ ball c r := by
  intro w ⟨hnot, hbdd⟩
  by_contra hwb
  rw [mem_ball, not_lt] at hwb
  have hwr : r < dist w c := by
    rcases eq_or_lt_of_le hwb with h | h
    · exfalso
      apply hnot
      have : w ∈ sphere c r := h.symm
      have himg : sphere c |r| = circleMap c r '' Ioc 0 (2 * π) := (image_circleMap_Ioc c r).symm
      rw [abs_of_pos hr] at himg
      rw [himg] at this
      obtain ⟨θ, hθ, rfl⟩ := this
      refine ⟨θ / (2 * π), ⟨by positivity [hθ.1.le], ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; exact hθ.2
      · simp only [circlePath]
        congr 1
        field_simp
    · exact h
  -- the ray from `w` away from `c` stays in the complement and is unbounded
  set ray : ℝ → ℂ := fun t => c + (t : ℂ) * (w - c)
  have hray_dist : ∀ t : ℝ, 0 ≤ t → dist (ray t) c = t * dist w c := by
    intro t ht
    simp only [ray, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht]
  have hconn : IsPreconnected (ray '' Ici 1) :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hsub : ray '' Ici 1 ⊆ (pathImage (circlePath c r))ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hmem
    have h1 := pathImage_circlePath_subset hr.le hmem
    rw [mem_sphere, hray_dist t (le_trans zero_le_one ht)] at h1
    have : dist w c ≤ t * dist w c := le_mul_of_one_le_left dist_nonneg ht
    linarith
  have hw1 : w ∈ ray '' Ici 1 := ⟨1, mem_Ici.2 le_rfl, by simp [ray]⟩
  have hin := hconn.subset_connectedComponentIn hw1 hsub
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall c).1 hbdd
  have hpos : 0 < dist w c := lt_trans hr hwr
  have hmem : ray ((C + 1) / dist w c + 1) ∈ closedBall c C := by
    refine hC (hin ⟨_, ?_, rfl⟩)
    rw [mem_Ici]
    have : 0 ≤ (C + 1) / dist w c := by
      have hC0 : 0 ≤ C := by
        have := hC (mem_connectedComponentIn hnot)
        exact le_trans dist_nonneg this
      positivity
    linarith
  rw [mem_closedBall, hray_dist _ (by
    have hC0 : 0 ≤ C := le_trans dist_nonneg (hC (mem_connectedComponentIn hnot))
    positivity)] at hmem
  have : ((C + 1) / dist w c + 1) * dist w c = C + 1 + dist w c := by
    field_simp
  rw [this] at hmem
  linarith

theorem insideOf_circlePath (hr : 0 < r) : insideOf (circlePath c r) = ball c r :=
  (insideOf_circlePath_subset_ball hr).antisymm (ball_subset_insideOf_circlePath hr)

/-- If the closed disc `D[w, R]` lies in the open disc `D(c, r)` then `|w - c| + R < r`. -/
lemma dist_add_lt_of_closedBall_subset_ball {w : ℂ} {R : ℝ} (hR : 0 < R)
    (h : closedBall w R ⊆ ball c r) : dist w c + R < r := by
  by_cases hwc : w = c
  · subst hwc
    have := h (show w + R ∈ closedBall w R by simp [abs_of_pos hR])
    simpa [dist_eq_norm, abs_of_pos hR] using this
  · have hd : 0 < dist w c := dist_pos.2 hwc
    set u : ℂ := (w - c) / (dist w c : ℂ)
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, ← dist_eq_norm]
      exact div_self hd.ne'
    have hp : w + R * u ∈ closedBall w R := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hu, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have := h hp
    rw [mem_ball, dist_eq_norm] at this
    have e : w + R * u - c = ((dist w c + R : ℝ) : ℂ) * u := by
      simp only [u]
      have : (dist w c : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      push_cast
      ring
    rw [e, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at this
    exact this

/-- The straight-line homotopy between two circles, the second disc inside the first. -/
lemma circlePath_homotopic {w : ℂ} {R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (h : closedBall w R ⊆ ball c r) :
    IsGHomotopic (closedBall c r \ ball w R) (circlePath c r) (circlePath w R) := by
  have hlt := dist_add_lt_of_closedBall_subset_ball hR h
  refine ⟨fun t s => ((1 - s : ℝ) : ℂ) * c + (s : ℂ) * w +
      (((1 - s) * r + s * R : ℝ) : ℂ) * exp ((2 * π * t : ℝ) * I), ?_, ?_, ?_, ?_, ?_⟩
  · refine Continuous.continuousOn ?_
    fun_prop
  · intro t _ s hs
    set e : ℂ := exp ((2 * π * t : ℝ) * I)
    have he : ‖e‖ = 1 := by simp only [e]; exact norm_exp_ofReal_mul_I _
    have hρ : 0 ≤ (1 - s) * r + s * R := by nlinarith [hs.1, hs.2]
    constructor
    · rw [mem_closedBall, dist_eq_norm]
      have e1 : ((1 - s : ℝ) : ℂ) * c + (s : ℂ) * w + (((1 - s) * r + s * R : ℝ) : ℂ) * e - c
          = (s : ℂ) * (w - c) + (((1 - s) * r + s * R : ℝ) : ℂ) * e := by push_cast; ring
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hs.1, abs_of_nonneg hρ, ← dist_eq_norm]
      nlinarith [hs.1, hs.2, dist_nonneg (x := w) (y := c)]
    · rw [mem_ball, not_lt, dist_eq_norm]
      have e1 : ((1 - s : ℝ) : ℂ) * c + (s : ℂ) * w + (((1 - s) * r + s * R : ℝ) : ℂ) * e - w
          = (((1 - s) * r + s * R : ℝ) : ℂ) * e - ((1 - s : ℝ) : ℂ) * (w - c) := by push_cast; ring
      rw [e1]
      refine le_trans ?_ (norm_sub_norm_le _ _)
      rw [norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hρ, abs_of_nonneg (by linarith [hs.2]), ← dist_eq_norm]
      nlinarith [hs.1, hs.2, dist_nonneg (x := w) (y := c)]
  · intro t _
    simp [circlePath_eq]
  · intro t _
    simp [circlePath_eq]
  · intro s _
    simp only [mul_zero, mul_one, ofReal_zero, zero_mul, exp_zero]
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, exp_two_pi_mul_I, mul_one]

/-- The counterclockwise circle `C[c, r]` (`r > 0`) is a positively oriented simple closed path, and
its inside is the open disc: the structure `IsPositivelyOrientedSimpleClosed` is not vacuous. -/
theorem isPositivelyOrientedSimpleClosed_circlePath (hr : 0 < r) :
    IsPositivelyOrientedSimpleClosed (circlePath c r) where
  smooth := isPiecewiseSmooth_circlePath c r
  closed := circlePath_closed c r
  simple := by
    intro s hs t ht hst
    have hinj := injOn_circleMap_of_abs_sub_le' (c := c) hr.ne' (a := 0) (b := 2 * π) (by simp)
    have := hinj ⟨by nlinarith [hs.1, Real.pi_pos], by nlinarith [hs.2, Real.pi_pos]⟩
      ⟨by nlinarith [ht.1, Real.pi_pos], by nlinarith [ht.2, Real.pi_pos]⟩ hst
    have hπ : (2 * π) ≠ 0 := by positivity
    exact mul_left_cancel₀ hπ this
  inside_nonempty := ⟨c, by rw [insideOf_circlePath hr]; exact mem_ball_self hr⟩
  annulus := by
    intro w R hR hsub
    rw [insideOf_circlePath hr] at hsub ⊢
    refine (circlePath_homotopic hr hR hsub).mono ?_
    rintro z ⟨hz, hzw⟩
    refine ⟨?_, hzw⟩
    rcases eq_or_lt_of_le (mem_closedBall.1 hz) with h | h
    · right
      have : z ∈ sphere c r := h
      have himg : sphere c |r| = circleMap c r '' Ioc 0 (2 * π) := (image_circleMap_Ioc c r).symm
      rw [abs_of_pos hr] at himg
      rw [himg] at this
      obtain ⟨θ, hθ, rfl⟩ := this
      refine ⟨θ / (2 * π), ⟨by positivity [hθ.1.le], ?_⟩, ?_⟩
      · rw [div_le_one (by positivity)]; exact hθ.2
      · simp only [circlePath]
        congr 1
        field_simp
    · exact Or.inl h

end Circle

/-! ### Transitivity of homotopy and Proposition 4.4.6 -/

/-- Beck Exercise 4.5.23 (part): `G`-homotopy of closed paths is transitive. -/
theorem IsGHomotopic.trans {G : Set ℂ} {γ₀ γ₁ γ₂ : ℝ → ℂ} (h₁ : IsGHomotopic G γ₀ γ₁)
    (h₂ : IsGHomotopic G γ₁ γ₂) : IsGHomotopic G γ₀ γ₂ := by
  obtain ⟨a, hac, ham, ha0, ha1, hacl⟩ := h₁
  obtain ⟨b, hbc, hbm, hb0, hb1, hbcl⟩ := h₂
  refine ⟨fun t s => if s ≤ 1 / 2 then a t (2 * s) else b t (2 * s - 1), ?_, ?_, ?_, ?_, ?_⟩
  · have hK : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 =
        (Icc (0 : ℝ) 1 ×ˢ Icc 0 (1 / 2)) ∪ (Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2) 1) := by
      rw [← prod_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
    rw [hK]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_Icc.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_Icc)
    · have : ContinuousOn (fun p : ℝ × ℝ => a p.1 (2 * p.2)) (Icc (0 : ℝ) 1 ×ˢ Icc 0 (1 / 2)) :=
        hac.comp (f := fun p : ℝ × ℝ => (p.1, 2 * p.2)) (by fun_prop)
          (fun p hp => ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩)
      exact this.congr (fun p hp => if_pos hp.2.2)
    · have : ContinuousOn (fun p : ℝ × ℝ => b p.1 (2 * p.2 - 1))
          (Icc (0 : ℝ) 1 ×ˢ Icc (1 / 2) 1) :=
        hbc.comp (f := fun p : ℝ × ℝ => (p.1, 2 * p.2 - 1)) (by fun_prop)
          (fun p hp => ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩)
      refine this.congr (fun p hp => ?_)
      by_cases hs : p.2 ≤ 1 / 2
      · have e : p.2 = 1 / 2 := le_antisymm hs hp.2.1
        simp only [if_pos hs, e]
        norm_num
        rw [ha1 p.1 hp.1, ← hb0 p.1 hp.1]
      · simp only [if_neg hs]
  · intro t ht s hs
    by_cases h : s ≤ 1 / 2
    · simp only [if_pos h]; exact ham t ht _ ⟨by linarith [hs.1], by linarith⟩
    · simp only [if_neg h]; exact hbm t ht _ ⟨by linarith, by linarith [hs.2]⟩
  · intro t ht; simp only [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_zero]; exact ha0 t ht
  · intro t ht
    simp only [if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2)]
    norm_num; exact hb1 t ht
  · intro s hs
    by_cases h : s ≤ 1 / 2
    · simp only [if_pos h]; exact hacl _ ⟨by linarith [hs.1], by linarith⟩
    · simp only [if_neg h]; exact hbcl _ ⟨by linarith, by linarith [hs.2]⟩

/-- A circle is contractible in its closed disc. -/
lemma circlePath_contractible (w : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsGHomotopic (closedBall w R) (circlePath w R) (fun _ => w) := by
  refine ⟨fun t s => w + (((1 - s) * R : ℝ) : ℂ) * exp ((2 * π * t : ℝ) * I), ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.continuousOn (by fun_prop)
  · intro t _ s hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hs.2])]
    nlinarith [hs.1]
  · intro t _; simp [circlePath_eq]
  · intro t _; simp
  · intro s _
    simp only [mul_zero, mul_one, ofReal_zero, zero_mul, exp_zero]
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, exp_two_pi_mul_I, mul_one]

namespace IsPositivelyOrientedSimpleClosed

/-- Beck Proposition 4.4.6 (CX-072): a positively oriented simple closed piecewise smooth path `γ`
in the open set `G` is `G`-contractible if and only if `G` contains the inside of `γ`. -/
@[kb "beck2025" "Proposition 4.4.6, p. 84"]
theorem contractible_iff_inside_subset {γ : ℝ → ℂ} (hγ : IsPositivelyOrientedSimpleClosed γ)
    {G : Set ℂ} (hG : IsOpen G) (himg : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G) :
    (∃ c : ℂ, IsGHomotopic G γ (fun _ => c)) ↔ insideOf γ ⊆ G := by
  refine ⟨fun ⟨c, hc⟩ => hγ.inside_subset_of_contractible hG hc, fun hin => ?_⟩
  obtain ⟨w, hw⟩ := hγ.inside_nonempty
  obtain ⟨R, hR, hRin⟩ := hγ.exists_closedBall hw
  refine ⟨w, ((hγ.annulus w R hR hRin).mono ?_).trans
    ((circlePath_contractible w hR.le).mono (hRin.trans hin))⟩
  rintro z ⟨hz | ⟨t, ht, rfl⟩, -⟩
  · exact hin hz
  · exact himg t ht

end IsPositivelyOrientedSimpleClosed

/-! ### Cauchy's integral formula -/

namespace IsPositivelyOrientedSimpleClosed

variable {γ : ℝ → ℂ} {f : ℂ → ℂ} {G : Set ℂ}

/-- For `w` inside a `G`-contractible `γ` and a small closed disc about `w` inside `γ`, the path `γ`
is homotopic to the circle within `G` minus the open disc. -/
lemma homotopic_circle_in (hγ : IsPositivelyOrientedSimpleClosed γ) (hG : IsOpen G) {c : ℂ}
    (hc : IsGHomotopic G γ (fun _ => c)) {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hRin : closedBall w R ⊆ insideOf γ) :
    IsGHomotopic (G \ {w}) γ (circlePath w R) := by
  have hin := hγ.inside_subset_of_contractible hG hc
  refine (hγ.annulus w R hR hRin).mono ?_
  rintro z ⟨hz, hzw⟩
  refine ⟨?_, fun h => hzw (h ▸ mem_ball_self hR)⟩
  rcases hz with hz | ⟨t, ht, rfl⟩
  · exact hin hz
  · exact hc.mem_left t ht

/-- Beck Theorem 4.4.5 (CX-071), Cauchy's integral formula: if `f` is holomorphic on the open set
`G`, `γ` is a positively oriented simple closed piecewise smooth path that is `G`-contractible, and
`w` is inside `γ`, then `f w = (2 π i)⁻¹ ∫_γ f z / (z - w) dz`. -/
@[kb "beck2025" "Theorem 4.4.5, p. 84"]
theorem cauchy_integral_formula (hγ : IsPositivelyOrientedSimpleClosed γ) (hG : IsOpen G)
    (hf : DifferentiableOn ℂ f G) {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) {w : ℂ}
    (hw : w ∈ insideOf γ) :
    f w = (2 * π * I)⁻¹ * pathIntegral (fun z => f z / (z - w)) γ 0 1 := by
  obtain ⟨R, hR, hRin⟩ := hγ.exists_closedBall hw
  have hin := hγ.inside_subset_of_contractible hG hc
  have hd : DifferentiableOn ℂ (fun z => f z / (z - w)) (G \ {w}) := fun z hz =>
    ((hf.differentiableAt (hG.mem_nhds hz.1)).div (differentiableAt_id.sub_const w)
      (sub_ne_zero.2 hz.2)).differentiableWithinAt
  rw [cauchy_theorem_homotopy (hG.sdiff isClosed_singleton) hd hγ.smooth
    (isPiecewiseSmooth_circlePath w R) (hγ.homotopic_circle_in hG hc hR hRin),
    pathIntegral_circlePath]
  have hcif := (hf.mono (hRin.trans hin)).diffContOnCl_ball (subset_refl _) |>.circleIntegral_sub_inv_smul
    (mem_ball_self hR)
  have e : (∮ z in C(w, R), f z / (z - w)) = ∮ z in C(w, R), (z - w)⁻¹ • f z := by
    congr 1; funext z; rw [smul_eq_mul, div_eq_inv_mul]
  rw [e, hcif, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]),
    one_mul]

/-- Beck Theorem 5.1.1 (CX-073), Cauchy's integral formula for derivatives along a positively
oriented simple closed path: under the hypotheses of Theorem 4.4.5,
`f^(k) w = k! / (2 π i) ∫_γ f z / (z - w)^(k+1) dz`. -/
@[kb "beck2025" "Theorem 5.1.1, p. 91"]
theorem cauchy_integral_formula_deriv (hγ : IsPositivelyOrientedSimpleClosed γ) (hG : IsOpen G)
    (hf : DifferentiableOn ℂ f G) {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) {w : ℂ}
    (hw : w ∈ insideOf γ) (k : ℕ) :
    iteratedDeriv k f w =
      k.factorial / (2 * π * I) * pathIntegral (fun z => f z / (z - w) ^ (k + 1)) γ 0 1 := by
  obtain ⟨R, hR, hRin⟩ := hγ.exists_closedBall hw
  have hin := hγ.inside_subset_of_contractible hG hc
  have hd : DifferentiableOn ℂ (fun z => f z / (z - w) ^ (k + 1)) (G \ {w}) := fun z hz =>
    ((hf.differentiableAt (hG.mem_nhds hz.1)).div ((differentiableAt_id.sub_const w).pow _)
      (pow_ne_zero _ (sub_ne_zero.2 hz.2))).differentiableWithinAt
  rw [cauchy_theorem_homotopy (hG.sdiff isClosed_singleton) hd hγ.smooth
    (isPiecewiseSmooth_circlePath w R) (hγ.homotopic_circle_in hG hc hR hRin),
    pathIntegral_circlePath]
  have hcif := (hf.mono (hRin.trans hin)).circleIntegral_one_div_sub_center_pow_smul hR k
  have e : (∮ z in C(w, R), f z / (z - w) ^ (k + 1)) =
      ∮ z in C(w, R), (1 / (z - w) ^ (k + 1)) • f z := by
    congr 1; funext z; rw [smul_eq_mul, one_div, div_eq_inv_mul]
  rw [e, hcif, smul_eq_mul]
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

/-- Beck Example 4.4.7 (CX-071): for every positively oriented simple closed path `γ` with `i`
inside that is contractible in `ℂ \ {-i}`, `∫_γ dz / (z² + 1) = π`. -/
@[kb "beck2025" "Example 4.4.7, p. 84"]
theorem pathIntegral_inv_sq_add_one (hγ : IsPositivelyOrientedSimpleClosed γ) {c : ℂ}
    (hc : IsGHomotopic {-I}ᶜ γ (fun _ => c)) (hi : I ∈ insideOf γ) :
    pathIntegral (fun z => 1 / (z ^ 2 + 1)) γ 0 1 = π := by
  have hd : DifferentiableOn ℂ (fun z => (z + I)⁻¹) {-I}ᶜ := fun z hz =>
    ((differentiableAt_id.add_const I).inv (fun h => hz (eq_neg_of_add_eq_zero_left h)))
      |>.differentiableWithinAt
  have key := hγ.cauchy_integral_formula isOpen_compl_singleton hd hc hi
  have e : (fun z : ℂ => 1 / (z ^ 2 + 1)) = fun z => (z + I)⁻¹ / (z - I) := by
    funext z
    rw [one_div, div_eq_mul_inv, ← mul_inv]
    congr 1
    ring_nf
    rw [I_sq]
    ring
  rw [e]
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hI0 : (2 * I : ℂ) ≠ 0 := by simp [I_ne_zero]
  set P := pathIntegral (fun z => (z + I)⁻¹ / (z - I)) γ 0 1
  have hP : P = 2 * π * I * (I + I)⁻¹ := by rw [key, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  rw [hP, show I + I = 2 * I by ring]
  field_simp

end IsPositivelyOrientedSimpleClosed

end UndergradKB.ComplexAnalysis
