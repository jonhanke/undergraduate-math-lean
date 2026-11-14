import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Algebra.Order.ToIntervalMod
import UndergradKB.ComplexAnalysis.Rectangle

/-!
# Convex star-shaped paths are positively oriented simple closed paths

Beck et al. assume the Jordan curve theorem and the annulus theorem in Section 4.4; in this
library they are the fields `inside_nonempty` and `annulus` of `IsPositivelyOrientedSimpleClosed`
(Definition 4.4.4), proved so far for circles and rectangles. Here they are proved for every closed
path that

* is *star-shaped about a point `c`* (`IsStarPath γ c φ`): `γ t = c + |γ t - c| e^{i φ(t)}` with a
  continuous, strictly increasing angle `φ` that gains `2π` over `[0, 1]`, so every ray from `c`
  meets the path exactly once; and
* lies on the boundary of a convex set `K` containing `c` (`γ t ∈ K`, `γ t ∉ interior K`).

This covers circles, ellipses, triangles and every convex polygon or convex curve. Results:

* `IsStarPath.insideOf_eq_interior`: the inside of `γ` is the interior of `K`;
* `IsStarPath.jordan_curve`: the Jordan curve theorem for such paths (two components, the
  interior of `K` and the complement of `K`, the path the frontier of each);
* `IsStarPath.isPositivelyOrientedSimpleClosed`: both assumed fields hold, by an explicit annulus
  homotopy (radial projection onto the circle, then moving the centre of projection, then a
  homotopy of angles), so Cauchy's integral formula, the residue theorem, the argument principle and
  Rouché's theorem hold for these paths with no assumption.
-/

open Set Metric Complex Filter Topology
open scoped Real

namespace UndergradKB.ComplexAnalysis

/-- A closed path `γ` on `[0, 1]` that is *star-shaped about `c`* with angle `φ`: it avoids `c`,
`γ t = c + |γ t - c| e^{i φ(t)}` with `φ` continuous and strictly increasing on `[0, 1]`, and
`φ 1 = φ 0 + 2π`. So every ray from `c` meets the path exactly once, and the path winds once
counterclockwise around `c`. -/
structure IsStarPath (γ : ℝ → ℂ) (c : ℂ) (φ : ℝ → ℝ) : Prop where
  cont : ContinuousOn γ (Icc 0 1)
  closed : γ 0 = γ 1
  ne : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ c
  angle_cont : ContinuousOn φ (Icc 0 1)
  angle_mono : StrictMonoOn φ (Icc 0 1)
  eq_angle : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c + ‖γ t - c‖ * exp (φ t * I)
  angle_one : φ 1 = φ 0 + 2 * π

namespace IsStarPath

variable {γ : ℝ → ℂ} {c : ℂ} {φ : ℝ → ℝ}

lemma zero_mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
lemma one_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩

lemma angle_mem (h : IsStarPath γ c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    φ 0 ≤ φ t ∧ φ t ≤ φ 0 + 2 * π := by
  rw [← h.angle_one]
  exact ⟨h.angle_mono.monotoneOn zero_mem ht ht.1, h.angle_mono.monotoneOn ht one_mem ht.2⟩

lemma sub_eq (h : IsStarPath γ c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ t - c = ‖γ t - c‖ * exp (φ t * I) :=
  sub_eq_iff_eq_add'.2 (h.eq_angle t ht)

lemma norm_pos (h : IsStarPath γ c φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < ‖γ t - c‖ :=
  norm_pos_iff.2 (sub_ne_zero.2 (h.ne t ht))

/-- Two parameters with the same direction from `c` are equal or are the two ends `0, 1`. -/
lemma param_of_exp_eq (h : IsStarPath γ c φ) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t' ∈ Icc (0 : ℝ) 1) (he : exp (φ t * I) = exp (φ t' * I)) :
    t = t' ∨ (t = 0 ∧ t' = 1) ∨ (t = 1 ∧ t' = 0) := by
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 he
  have hr : φ t = φ t' + n * (2 * π) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  obtain ⟨a1, a2⟩ := h.angle_mem ht
  obtain ⟨b1, b2⟩ := h.angle_mem ht'
  have hπ := Real.pi_pos
  have hn1 : (n : ℝ) < 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hn2 : (-2 : ℝ) < n := by
    by_contra hc
    push Not at hc
    nlinarith
  have hn3 : n = -1 ∨ n = 0 ∨ n = 1 := by
    have h1 : n < 2 := by exact_mod_cast hn1
    have h2 : -2 < n := by exact_mod_cast hn2
    omega
  rcases hn3 with rfl | rfl | rfl
  · right; left
    push_cast at hr
    have e1 : φ t = φ 0 := by linarith
    have e2 : φ t' = φ 1 := by rw [h.angle_one]; linarith
    exact ⟨h.angle_mono.injOn ht zero_mem e1, h.angle_mono.injOn ht' one_mem e2⟩
  · left
    simp at hr
    exact h.angle_mono.injOn ht ht' hr
  · right; right
    push_cast at hr
    have e1 : φ t = φ 1 := by rw [h.angle_one]; linarith
    have e2 : φ t' = φ 0 := by linarith
    exact ⟨h.angle_mono.injOn ht one_mem e1, h.angle_mono.injOn ht' zero_mem e2⟩

lemma eq_of_exp_eq (h : IsStarPath γ c φ) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t' ∈ Icc (0 : ℝ) 1) (he : exp (φ t * I) = exp (φ t' * I)) : γ t = γ t' := by
  rcases h.param_of_exp_eq ht ht' he with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact h.closed
  · exact h.closed.symm

/-- Every point `z ≠ c` lies on the ray from `c` through some point of the path. -/
lemma exists_ray (h : IsStarPath γ c φ) {z : ℂ} (hz : z ≠ c) :
    ∃ t ∈ Ico (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ z = c + r * (γ t - c) := by
  set ψ := toIcoMod Real.two_pi_pos (φ 0) (arg (z - c)) with hψ
  have hψm := toIcoMod_mem_Ico Real.two_pi_pos (φ 0) (arg (z - c))
  obtain ⟨t, ht, hφt⟩ : ψ ∈ φ '' Icc 0 1 := intermediate_value_Icc zero_le_one h.angle_cont
    ⟨hψm.1, by rw [h.angle_one]; exact hψm.2.le⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [h.angle_one] at hφt
    exact (ne_of_lt hψm.2) hφt.symm
  have hex : exp (ψ * I) = exp (arg (z - c) * I) := by
    rw [exp_eq_exp_iff_exists_int]
    refine ⟨-toIcoDiv Real.two_pi_pos (φ 0) (arg (z - c)), ?_⟩
    have := self_sub_toIcoMod_eq_mul Real.two_pi_pos (φ 0) (arg (z - c))
    rw [← hψ] at this
    have h2 : ψ = arg (z - c) - (toIcoDiv Real.two_pi_pos (φ 0) (arg (z - c)) : ℝ) * (2 * π) := by
      linarith
    rw [h2]
    push_cast
    ring
  have hγc := h.norm_pos ht
  refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩, ‖z - c‖ / ‖γ t - c‖,
    div_pos (norm_pos_iff.2 (sub_ne_zero.2 hz)) hγc, ?_⟩
  have hne : (‖γ t - c‖ : ℂ) ≠ 0 := by exact_mod_cast hγc.ne'
  calc z = c + (z - c) := by ring
    _ = c + ‖z - c‖ * exp (arg (z - c) * I) := by rw [norm_mul_exp_arg_mul_I]
    _ = c + ((‖z - c‖ / ‖γ t - c‖ : ℝ) : ℂ) * (‖γ t - c‖ * exp (φ t * I)) := by
      rw [hφt, hex]; push_cast; field_simp
    _ = c + ((‖z - c‖ / ‖γ t - c‖ : ℝ) : ℂ) * (γ t - c) := by rw [← h.sub_eq ht]

/-- Two points on rays through the path coincide only on the same ray at the same distance. -/
lemma eq_of_ray_eq (h : IsStarPath γ c φ) {t t' r r' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t' ∈ Icc (0 : ℝ) 1) (hr : 0 < r) (hr' : 0 < r')
    (he : c + r * (γ t - c) = c + r' * (γ t' - c)) : γ t = γ t' ∧ r = r' := by
  have e : (r : ℂ) * (γ t - c) = r' * (γ t' - c) := add_left_cancel he
  have hn : r * ‖γ t - c‖ = r' * ‖γ t' - c‖ := by
    have := congrArg norm e
    simpa [norm_mul, abs_of_pos hr, abs_of_pos hr'] using this
  have hN : 0 < r * ‖γ t - c‖ := mul_pos hr (h.norm_pos ht)
  have hexp : exp (φ t * I) = exp (φ t' * I) := by
    rw [h.sub_eq ht, h.sub_eq ht'] at e
    have e2 : ((r * ‖γ t - c‖ : ℝ) : ℂ) * exp (φ t * I) =
        ((r' * ‖γ t' - c‖ : ℝ) : ℂ) * exp (φ t' * I) := by
      push_cast
      rw [mul_assoc, mul_assoc]
      exact e
    rw [hn] at e2
    exact mul_left_cancel₀ (by exact_mod_cast (hn ▸ hN).ne') e2
  have hg := h.eq_of_exp_eq ht ht' hexp
  refine ⟨hg, ?_⟩
  rw [← hg] at e
  exact_mod_cast mul_right_cancel₀ (sub_ne_zero.2 (h.ne t ht)) e

lemma injOn (h : IsStarPath γ c φ) : InjOn γ (Ico 0 1) := by
  intro t ht t' ht' hg
  have ht0 : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
  have ht0' : t' ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht'
  have hexp : exp (φ t * I) = exp (φ t' * I) := by
    have e1 := h.sub_eq ht0
    have e2 := h.sub_eq ht0'
    rw [hg] at e1
    have e3 := e1.symm.trans e2
    have hne : (‖γ t' - c‖ : ℂ) ≠ 0 := by exact_mod_cast (h.norm_pos ht0').ne'
    exact mul_left_cancel₀ hne e3
  rcases h.param_of_exp_eq ht0 ht0' hexp with h' | ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact h'
  · exact absurd ht'.2 (lt_irrefl _)
  · exact absurd ht.2 (lt_irrefl _)

/-! ### The convex set bounded by the path -/

section Convex

variable {K : Set ℂ}

lemma combo_eq (t : ℝ) (s : ℝ) : c + (s : ℂ) * (γ t - c) = (1 - s) • c + s • γ t := by
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- Under the convexity hypotheses, `c` is an interior point of `K`. -/
lemma center_mem_interior (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) : c ∈ interior K := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (h.cont.sub continuousOn_const).norm
  have hm := h.norm_pos ht₀
  refine mem_interior.2 ⟨ball c ‖γ t₀ - c‖, fun z hz => ?_, isOpen_ball, mem_ball_self hm⟩
  by_cases hzc : z = c
  · rw [hzc]; exact hcK
  obtain ⟨t, ht, r, hr, rfl⟩ := h.exists_ray hzc
  have ht' := Ico_subset_Icc_self ht
  have hr1 : r ≤ 1 := by
    have h1 := mem_ball.1 hz
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] at h1
    have h2 : ‖γ t₀ - c‖ ≤ ‖γ t - c‖ := by simpa using isMinOn_iff.1 hmin t ht'
    by_contra hc
    push Not at hc
    nlinarith [h.norm_pos ht']
  rw [combo_eq]
  exact hK hcK (himK t ht') (by linarith) hr.le (by ring)

/-- The interior of `K` is exactly the set of points `c + s (γ t - c)` with `0 ≤ s < 1`. -/
lemma mem_interior_iff (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K)
    {z : ℂ} : z ∈ interior K ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Ico (0 : ℝ) 1, z = c + s * (γ t - c) := by
  have hc := h.center_mem_interior hK hcK himK
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact ⟨0, zero_mem, 0, ⟨le_rfl, zero_lt_one⟩, by simp [hzc]⟩
    obtain ⟨t, ht, r, hr, rfl⟩ := h.exists_ray hzc
    have ht' := Ico_subset_Icc_self ht
    refine ⟨t, ht', r, ⟨hr.le, ?_⟩, rfl⟩
    by_contra hr1
    push Not at hr1
    refine hint t ht' ?_
    have : γ t = (1 - 1 / r) • c + (1 / r) • (c + r * (γ t - c)) := by
      rw [Complex.real_smul, Complex.real_smul]
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      push_cast
      field_simp
      ring
    rw [this]
    exact hK.combo_closure_interior_mem_interior (subset_closure hcK) hz
      (by rw [sub_nonneg, div_le_one hr]; exact hr1) (by positivity) (by ring)
  · rintro ⟨t, ht, s, hs, rfl⟩
    rw [combo_eq]
    exact hK.combo_interior_closure_mem_interior hc (subset_closure (himK t ht))
      (by linarith [hs.2]) hs.1 (by ring)

/-- Every point of `K` is `c + s (γ t - c)` with `0 ≤ s ≤ 1`; so `K` is the image of the compact
square under a continuous map. -/
lemma eq_image (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    K = (fun p : ℝ × ℝ => c + p.1 * (γ p.2 - c)) '' (Icc 0 1 ×ˢ Icc 0 1) := by
  have hc := h.center_mem_interior hK hcK himK
  ext z
  constructor
  · intro hz
    by_cases hzc : z = c
    · exact ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, zero_mem⟩, by simp [hzc]⟩
    obtain ⟨t, ht, r, hr, rfl⟩ := h.exists_ray hzc
    have ht' := Ico_subset_Icc_self ht
    refine ⟨(r, t), ⟨⟨hr.le, ?_⟩, ht'⟩, rfl⟩
    by_contra hr1
    push Not at hr1
    refine hint t ht' ?_
    have : γ t = (1 - 1 / r) • c + (1 / r) • (c + r * (γ t - c)) := by
      rw [Complex.real_smul, Complex.real_smul]
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      push_cast
      field_simp
      ring
    rw [this]
    have hlt : 1 / r < 1 := (div_lt_one hr).2 hr1
    exact hK.combo_interior_closure_mem_interior hc (subset_closure hz)
      (by linarith) (by positivity) (by ring)
  · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
    simp only
    rw [combo_eq]
    exact hK hcK (himK t ht) (by linarith [hs.2]) hs.1 (by ring)

lemma isCompact (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    IsCompact K := by
  rw [h.eq_image hK hcK himK hint]
  refine (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn ?_
  refine continuousOn_const.add (ContinuousOn.mul ?_ ?_)
  · exact continuous_ofReal.comp_continuousOn continuousOn_fst
  · exact (h.cont.comp continuousOn_snd
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) => hp.2)).sub continuousOn_const

/-- `K` is the interior of `K` together with the path. -/
lemma eq_interior_union (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    K = interior K ∪ pathImage γ := by
  refine Subset.antisymm ?_ (union_subset interior_subset ?_)
  · intro z hz
    rw [h.eq_image hK hcK himK hint] at hz
    obtain ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩ := hz
    rcases eq_or_lt_of_le hs.2 with rfl | hs1
    · right
      exact ⟨t, ht, by simp⟩
    · left
      exact (h.mem_interior_iff hK hcK himK hint).2 ⟨t, ht, s, ⟨hs.1, hs1⟩, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact himK t ht

lemma pathImage_eq (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    pathImage γ = K \ interior K := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨himK t ht, hint t ht⟩
  · rintro ⟨hz, hzi⟩
    rw [h.eq_interior_union hK hcK himK hint] at hz
    exact hz.resolve_left hzi

/-- The complement of `K` is the set of points `c + r (γ t - c)` with `r > 1`. -/
lemma compl_eq_image (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    Kᶜ = (fun p : ℝ × ℝ => c + p.1 * (γ p.2 - c)) '' (Ioi 1 ×ˢ Icc 0 1) := by
  have hKe := h.eq_image hK hcK himK hint
  ext z
  constructor
  · intro hz
    have hzc : z ≠ c := fun e => hz (e ▸ hcK)
    obtain ⟨t, ht, r, hr, rfl⟩ := h.exists_ray hzc
    refine ⟨(r, t), ⟨?_, Ico_subset_Icc_self ht⟩, rfl⟩
    by_contra hr1
    simp only [mem_Ioi, not_lt] at hr1
    refine hz ?_
    rw [hKe]
    exact ⟨(r, t), ⟨⟨hr.le, hr1⟩, Ico_subset_Icc_self ht⟩, rfl⟩
  · rintro ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩ hz
    simp only [mem_Ioi] at hr
    rw [hKe] at hz
    obtain ⟨⟨s, t'⟩, ⟨hs, ht'⟩, he⟩ := hz
    simp only at he hs ht' ht
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · rw [← hs0] at he
      push_cast at he
      have : (r : ℂ) * (γ t - c) = 0 := by linear_combination -he
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (by exact_mod_cast h0 : r = 0) (by linarith)
      · exact h.ne t ht (sub_eq_zero.1 h0)
    · have := (h.eq_of_ray_eq ht' ht hs0 (by linarith) he).2
      linarith [hs.2]

/-! ### The inside and the Jordan curve theorem -/

lemma continuousOn_ray (h : IsStarPath γ c φ) {A : Set ℝ} :
    ContinuousOn (fun p : ℝ × ℝ => c + p.1 * (γ p.2 - c)) (A ×ˢ Icc 0 1) := by
  refine continuousOn_const.add (ContinuousOn.mul ?_ ?_)
  · exact continuous_ofReal.comp_continuousOn continuousOn_fst
  · exact (h.cont.comp continuousOn_snd
      (fun p (hp : p ∈ A ×ˢ Icc (0 : ℝ) 1) => hp.2)).sub continuousOn_const

/-- **The inside of a convex star-shaped path is the interior of the convex set.** -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem insideOf_eq_interior (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    insideOf γ = interior K := by
  have hKc := h.isCompact hK hcK himK hint
  have hP := h.pathImage_eq hK hcK himK hint
  have hO := h.compl_eq_image hK hcK himK hint
  ext z
  constructor
  · rintro ⟨hz, hb⟩
    by_contra hzi
    have hzK : z ∈ Kᶜ := fun hzK => hz (hP ▸ ⟨hzK, hzi⟩)
    rw [hO] at hzK
    obtain ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩ := hzK
    simp only [mem_Ioi] at hr ht
    refine not_isBounded_connectedComponentIn_of_ray (sub_ne_zero.2 (h.ne t ht)) (fun u hu hm => ?_)
      hb
    have hmK : c + (r : ℂ) * (γ t - c) + u * (γ t - c) ∈ Kᶜ := by
      rw [hO]
      exact ⟨(r + u, t), ⟨by simp only [mem_Ioi]; linarith, ht⟩, by simp only; push_cast; ring⟩
    exact hmK (hP ▸ hm).1
  · intro hz
    have hz' : z ∉ pathImage γ := fun hm => (hP ▸ hm).2 hz
    refine ⟨hz', ?_⟩
    have hsub : connectedComponentIn (pathImage γ)ᶜ z ⊆ interior K := by
      refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset isOpen_interior
        ⟨z, mem_connectedComponentIn hz', hz⟩ ?_
      rintro y ⟨hy1, hy2⟩
      have hyK : y ∈ K := closure_minimal interior_subset hKc.isClosed hy1
      by_contra hyi
      exact connectedComponentIn_subset _ _ hy2 (hP ▸ ⟨hyK, hyi⟩)
    exact hKc.isBounded.subset (hsub.trans interior_subset)

/-- **The Jordan curve theorem for convex star-shaped paths** (Beck, Section 4.4, assumed there in
general): the complement of the path is the union of the interior of `K` and the complement of
`K`; these are disjoint, open and connected, the first is bounded and the second is not, and the
path is the frontier of each. -/
@[kb "beck2025" "Jordan curve theorem, §4.4, p. 82"]
theorem jordan_curve (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) :
    (pathImage γ)ᶜ = interior K ∪ Kᶜ ∧ Disjoint (interior K) Kᶜ ∧
    IsOpen (interior K) ∧ IsOpen Kᶜ ∧ IsConnected (interior K) ∧ IsConnected Kᶜ ∧
    Bornology.IsBounded (interior K) ∧ ¬ Bornology.IsBounded Kᶜ ∧
    frontier (interior K) = pathImage γ ∧ frontier Kᶜ = pathImage γ := by
  have hKc := h.isCompact hK hcK himK hint
  have hP := h.pathImage_eq hK hcK himK hint
  have hc := h.center_mem_interior hK hcK himK
  refine ⟨?_, disjoint_compl_right_iff_subset.2 interior_subset, isOpen_interior,
    hKc.isClosed.isOpen_compl, ⟨⟨c, hc⟩, hK.interior.isPreconnected⟩, ?_,
    hKc.isBounded.subset interior_subset, ?_, ?_, ?_⟩
  · rw [hP]
    ext z
    simp only [mem_compl_iff, Set.mem_sdiff, not_and, not_not, mem_union]
    constructor
    · intro hz
      by_cases hzK : z ∈ K
      · exact Or.inl (hz hzK)
      · exact Or.inr hzK
    · rintro (hz | hz) hzK
      · exact hz
      · exact absurd hzK hz
  · rw [h.compl_eq_image hK hcK himK hint]
    exact (isConnected_Ioi.prod (isConnected_Icc zero_le_one)).image _ h.continuousOn_ray
  · intro hb
    have := hKc.isBounded.union hb
    rw [union_compl_self] at this
    exact NormedSpace.unbounded_univ ℝ ℂ this
  · rw [frontier, interior_interior, hK.closure_interior_eq_closure_of_nonempty_interior ⟨c, hc⟩,
      hKc.isClosed.closure_eq, hP]
  · rw [frontier_compl, frontier, hKc.isClosed.closure_eq, hP]

/-! ### The annulus homotopy -/

/-- For a closed disc `D[w, R]` in the interior of `K`, the path is homotopic to the circle
`C[w, R]` within `K` minus the open disc: radial projection from `w` onto the circle, then moving
the centre of projection from `w` to `c`, then a homotopy of angles. -/
theorem annulus_homotopy (h : IsStarPath γ c φ) (hK : Convex ℝ K) (hcK : c ∈ K)
    (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K) (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K)
    {w : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall w R ⊆ interior K) :
    IsGHomotopic (K \ ball w R) γ (circlePath w R) := by
  have hc := h.center_mem_interior hK hcK himK
  have hw : w ∈ interior K := hsub (mem_closedBall_self hR.le)
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hS
  have hγw : ∀ t ∈ Icc (0 : ℝ) 1, R < ‖γ t - w‖ := by
    intro t ht
    by_contra hcon
    push Not at hcon
    exact hint t ht (hsub (mem_closedBall.2 (by rw [dist_eq_norm]; exact hcon)))
  have hγw0 : ∀ t ∈ Icc (0 : ℝ) 1, (‖γ t - w‖ : ℂ) ≠ 0 := fun t ht => by
    exact_mod_cast (hR.trans (hγw t ht)).ne'
  have hsph : ∀ z : ℂ, ‖z - w‖ = R → z ∈ K \ ball w R := fun z hz =>
    ⟨interior_subset (hsub (mem_closedBall.2 (by rw [dist_eq_norm, hz]))), fun hb => by
      rw [mem_ball, dist_eq_norm, hz] at hb; exact lt_irrefl R hb⟩
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
  have h1 : IsGHomotopic (K \ ball w R) γ (fun t => w + R * u t) := by
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
      refine ⟨?_, ?_⟩
      · have hp : w + (R : ℂ) * u t ∈ K := by
          refine interior_subset (hsub (mem_closedBall.2 ?_))
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, hun t ht, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hR, mul_one]
        have := hK (himK t ht) hp (sub_nonneg.2 hs.2) hs.1 (by ring)
        convert this using 1
        rw [Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [hγu t ht]
        push_cast; ring
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hun t ht, mul_one,
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
  have hvK : ∀ s ∈ Icc (0 : ℝ) 1, v s ∈ interior K := fun s hs => by
    have := hK.interior hw hc (sub_nonneg.2 hs.2) hs.1 (by ring)
    convert this using 1
    rw [Complex.real_smul, Complex.real_smul]
    push_cast; ring
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, γ t - v s ≠ 0 := fun t ht s hs e =>
    hint t ht (sub_eq_zero.1 e ▸ hvK s hs)
  have h2 : IsGHomotopic (K \ ball w R) (fun t => w + R * u t)
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
  have h3 : IsGHomotopic (K \ ball w R) (fun t => w + R * exp (φ t * I)) (circlePath w R) := by
    have hcl : w + (R : ℂ) * exp (φ 0 * I) = w + R * exp (φ 1 * I) := by
      rw [h.angle_one]
      push_cast
      rw [add_mul, exp_add, show (2 * (π : ℂ)) * I = 2 * π * I by ring, exp_two_pi_mul_I, mul_one]
    have hnr : ∀ t : ℝ, ‖w + (R : ℂ) * exp (φ t * I) - w‖ = R := fun t => by
      rw [add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, mul_one]
    have H := isGHomotopic_circlePath_of_angle (K := K) hK
      (γ := fun t => w + R * exp (φ t * I))
      (continuousOn_const.add (continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn
        ((continuous_ofReal.comp_continuousOn h.angle_cont).mul continuousOn_const)))) hcl hR
      (hsub.trans interior_subset) (fun t _ => (hsph _ (hnr t)).1) (fun t _ => (hnr t).ge)
      h.angle_cont (fun t _ => by simp only [hnr]) h.angle_one
    refine H.mono ?_
    rintro z ⟨hz, hzb⟩
    exact ⟨hz, hzb⟩
  exact h1.trans (h2.trans h3)

/-- **Convex star-shaped paths are positively oriented simple closed paths.** A piecewise smooth
closed path that is star-shaped about `c` (`IsStarPath`) and lies on the boundary of a convex set
`K` containing `c` satisfies `IsPositivelyOrientedSimpleClosed` (Definition 4.4.4) with both
fields that the book assumes in Section 4.4 proved: its inside is the interior of `K`, and the
annulus homotopy exists. So Cauchy's integral formula 4.4.5, the residue theorem 9.2.2, the
argument principle 9.3.2 and Rouché's theorem 9.3.3 apply to it unconditionally. -/
@[kb "beck2025" "Definition 4.4.4, p. 83"]
theorem isPositivelyOrientedSimpleClosed (h : IsStarPath γ c φ) (hs : IsPiecewiseSmooth γ 0 1)
    (hK : Convex ℝ K) (hcK : c ∈ K) (himK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ interior K) : IsPositivelyOrientedSimpleClosed γ where
  smooth := hs
  closed := h.closed
  simple := h.injOn
  inside_nonempty := ⟨c, by
    rw [h.insideOf_eq_interior hK hcK himK hint]
    exact h.center_mem_interior hK hcK himK⟩
  annulus := by
    intro w R hR hsub
    rw [h.insideOf_eq_interior hK hcK himK hint] at hsub ⊢
    rw [← h.eq_interior_union hK hcK himK hint]
    exact h.annulus_homotopy hK hcK himK hint hR hsub

end Convex

end IsStarPath

end UndergradKB.ComplexAnalysis
