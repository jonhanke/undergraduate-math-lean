import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import UndergradKB.DifferentialEquations.LinearSystems
import UndergradKB.DifferentialEquations.SecondOrderLinear
import UndergradKB.DifferentialEquations.NthOrderLinear
import UndergradKB.DifferentialEquations.MatrixSystems
import UndergradKB.Common.Attr

/-! # Picard's theorem and global existence for linear equations (Lebl §1.2, §2.1, §3.1)

* `picard_core`: local existence and uniqueness for `x' = f(t, x)` when `f` is continuous, bounded and
  Lipschitz in `x` on a box around `(t₀, x₀)`; every solution on the short interval automatically stays in the box.
* `picard_theorem`, `picard_theorem_systems`: the book's form, with `f` continuous and `∂f/∂x` continuous near
  the initial point (scalar and finite-dimensional systems).
* `linear_exists`, `lin2_exists`: existence on a whole compact interval for linear equations with continuous
  coefficients (Picard steps of uniform length glued together). -/

namespace UndergradKB.DifferentialEquations

open Set Metric
open scoped NNReal Topology

section Core

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One-sided "stays in the box" estimate: a solution starting at `x₀` at time `t₀` moves at speed at most `M`
while it is inside the ball, hence stays within `M (t - t₀) < b` for `t ∈ [t₀, t₀ + h)`. -/
lemma picard_stay_right {f : ℝ → E → E} {y : ℝ → E} {t₀ h b M : ℝ} {x₀ : E}
    (hbd : ∀ t ∈ Icc t₀ (t₀ + h), ∀ x ∈ closedBall x₀ b, ‖f t x‖ ≤ M) (hMh : M * h < b)
    (hy : ∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (f t (y t)) t) (hy0 : y t₀ = x₀) (hh : 0 < h)
    (hM : 0 ≤ M) :
    ∀ t ∈ Ico t₀ (t₀ + h), ‖y t - x₀‖ ≤ M * (t - t₀) := by
  intro T hT
  have hcont : ContinuousOn y (Icc t₀ T) := fun u hu =>
    (hy u ⟨by linarith [hu.1, hT.1], by linarith [hu.2, hT.2]⟩).continuousAt.continuousWithinAt
  let S : Set ℝ := {t | ‖y t - x₀‖ ≤ M * (t - t₀)}
  have hS : IsClosed (S ∩ Icc t₀ T) := by
    have hc : ContinuousOn (fun t => ‖y t - x₀‖ - M * (t - t₀)) (Icc t₀ T) :=
      (hcont.sub continuousOn_const).norm.sub (by fun_prop)
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
    convert this using 1
    ext t
    simp only [S, mem_inter_iff, mem_preimage, mem_Iic, sub_nonpos]
    show _ ∧ _ ↔ _
    tauto
  have := hS.Icc_subset_of_forall_mem_nhdsWithin (a := t₀) (b := T) (s := S)
    (by simp [S, hy0]) ?_
  · exact this ⟨hT.1, le_rfl⟩
  rintro x ⟨hxS, hx0, hxT⟩
  have hxh : x < t₀ + h := lt_of_lt_of_le hxT hT.2.le
  have hlt : ‖y x - x₀‖ < b := by
    calc ‖y x - x₀‖ ≤ M * (x - t₀) := hxS
      _ ≤ M * h := mul_le_mul_of_nonneg_left (by linarith) hM
      _ < b := hMh
  have hev : ∀ᶠ u in 𝓝 x, y u ∈ ball x₀ b ∧ u ∈ Ioo (t₀ - h) (t₀ + h) := by
    have h1 : ∀ᶠ u in 𝓝 x, y u ∈ ball x₀ b :=
      (hy x ⟨by linarith, hxh⟩).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (by simpa [dist_eq_norm] using hlt))
    have h2 : Ioo (t₀ - h) (t₀ + h) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) hxh
    exact h1.and h2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hIoo : Ioo x (x + ε) ∈ 𝓝[>] x := Ioo_mem_nhdsGT (by linarith)
  filter_upwards [hIoo] with t ht
  have hsub : Icc x t ⊆ ball x ε := fun u hu => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2, ht.2]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := y)
    (f' := fun u => f u (y u)) (s := Icc x t) (C := M) (x := x) (y := t)
    (fun u hu => (hy u (hball u (hsub hu)).2).hasDerivWithinAt)
    (fun u hu => by
      have hb := hball u (hsub hu)
      refine hbd u ⟨by linarith [hu.1], by linarith [hu.2, hb.2.2]⟩ _ ?_
      exact (ball_subset_closedBall hb.1))
    (convex_Icc _ _) ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩
  have h3 : ‖y t - y x‖ ≤ M * (t - x) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])] at key
    exact key
  show ‖y t - x₀‖ ≤ M * (t - t₀)
  calc ‖y t - x₀‖ = ‖(y t - y x) + (y x - x₀)‖ := by congr 1; abel
    _ ≤ ‖y t - y x‖ + ‖y x - x₀‖ := norm_add_le _ _
    _ ≤ M * (t - x) + M * (x - t₀) := add_le_add h3 hxS
    _ = M * (t - t₀) := by ring

/-- A solution on a symmetric interval around `t₀` starting at the centre `x₀` of the box stays in the closed
ball of radius `b`, provided `M h < b` for a bound `M` of the field on the box. -/
lemma picard_stay {f : ℝ → E → E} {y : ℝ → E} {t₀ h b M : ℝ} {x₀ : E}
    (hbd : ∀ t ∈ Icc (t₀ - h) (t₀ + h), ∀ x ∈ closedBall x₀ b, ‖f t x‖ ≤ M) (hMh : M * h < b)
    (hy : ∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (f t (y t)) t) (hy0 : y t₀ = x₀) (hh : 0 < h)
    (hM : 0 ≤ M) :
    ∀ t ∈ Ioo (t₀ - h) (t₀ + h), y t ∈ closedBall x₀ b := by
  intro t ht
  have hMb : ∀ s, 0 ≤ s → s < h → M * s ≤ b := fun s hs0 hsh =>
    (mul_le_mul_of_nonneg_left hsh.le hM).trans hMh.le
  rcases le_total t₀ t with h1 | h1
  · have := picard_stay_right (fun t ht => hbd t ⟨by linarith [ht.1], ht.2⟩) hMh hy hy0 hh hM t
      ⟨h1, ht.2⟩
    rw [mem_closedBall, dist_eq_norm]
    exact this.trans (hMb _ (by linarith) (by linarith [ht.2]))
  · -- reflect time
    set g : ℝ → E := fun s => y (2 * t₀ - s) with hg
    set F : ℝ → E → E := fun s z => -f (2 * t₀ - s) z with hF
    have hgd : ∀ s ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt g (F s (g s)) s := by
      intro s hs
      have := (hy (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).comp_const_sub (2 * t₀) s
      simpa [hg, hF] using this
    have := picard_stay_right (f := F) (y := g)
      (fun s hs z hz => by
        simpa [hF] using hbd (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ z hz)
      hMh hgd (by show y (2 * t₀ - t₀) = x₀; rw [show 2 * t₀ - t₀ = t₀ by ring]; exact hy0) hh hM (2 * t₀ - t) ⟨by linarith, by linarith [ht.1]⟩
    simp only [hg, sub_sub_cancel] at this
    rw [mem_closedBall, dist_eq_norm]
    exact this.trans (hMb _ (by linarith) (by linarith [ht.1]))

/-- **Local existence and uniqueness (core form).** If `f` is continuous in `t`, `K`-Lipschitz in `x` and bounded
by `M` on the box `[t₀ - a, t₀ + a] × closedBall x₀ b`, then there is `h > 0` such that `x' = f(t, x)`,
`x(t₀) = x₀` has a solution on `(t₀ - h, t₀ + h)` and any two solutions there (which then automatically stay in
the box) coincide. -/
theorem picard_core [CompleteSpace E] {f : ℝ → E → E} {t₀ a : ℝ} {x₀ : E} {b K M : ℝ≥0} (ha : 0 < a)
    (hb : 0 < b) (hcont : ∀ x ∈ closedBall x₀ b, ContinuousOn (fun t => f t x) (Icc (t₀ - a) (t₀ + a)))
    (hlip : ∀ t ∈ Icc (t₀ - a) (t₀ + a), LipschitzOnWith K (f t) (closedBall x₀ b))
    (hbd : ∀ t ∈ Icc (t₀ - a) (t₀ + a), ∀ x ∈ closedBall x₀ b, ‖f t x‖ ≤ M) :
    ∃ h > 0, (∃ y : ℝ → E, y t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (f t (y t)) t) ∧
      ∀ y z : ℝ → E, y t₀ = x₀ → z t₀ = x₀ →
        (∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (f t (y t)) t) →
        (∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt z (f t (z t)) t) →
        EqOn y z (Ioo (t₀ - h) (t₀ + h)) := by
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  set h : ℝ := min a ((b : ℝ) / ((M : ℝ) + 1)) with hh
  have hhpos : 0 < h := lt_min ha (by positivity)
  have hha : h ≤ a := min_le_left _ _
  have hMh : (M : ℝ) * h < b := by
    have h1 : h ≤ (b : ℝ) / ((M : ℝ) + 1) := min_le_right _ _
    calc (M : ℝ) * h ≤ M * ((b : ℝ) / ((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h1 M.2
      _ < b := by
          rw [mul_div_assoc', div_lt_iff₀ hM1]
          nlinarith [(NNReal.coe_pos.mpr hb)]
  have hsub : Icc (t₀ - h) (t₀ + h) ⊆ Icc (t₀ - a) (t₀ + a) :=
    Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨h, hhpos, ?_, ?_⟩
  · have hmem : t₀ ∈ Icc (t₀ - h) (t₀ + h) := ⟨by linarith, by linarith⟩
    have hpl : IsPicardLindelof f (⟨t₀, hmem⟩ : Icc (t₀ - h) (t₀ + h)) x₀ b 0 M K :=
      { lipschitzOnWith := fun t ht => hlip t (hsub ht)
        continuousOn := fun x hx => (hcont x hx).mono hsub
        norm_le := fun t ht x hx => hbd t (hsub ht) x hx
        mul_max_le := by
          have : max (t₀ + h - t₀) (t₀ - (t₀ - h)) = h := by simp
          simp only [this]
          push_cast
          linarith }
    obtain ⟨y, hy0, hy⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨y, hy0, fun t ht => (hy t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  · intro y z hy0 hz0 hy hz
    have hb' : ∀ t ∈ Icc (t₀ - h) (t₀ + h), ∀ x ∈ closedBall x₀ (b : ℝ), ‖f t x‖ ≤ (M : ℝ) :=
      fun t ht => hbd t (hsub ht)
    have hys := picard_stay hb' hMh hy hy0 hhpos M.2
    have hzs := picard_stay hb' hMh hz hz0 hhpos M.2
    exact ODE_solution_unique_of_mem_Ioo (a := t₀ - h) (b := t₀ + h) (v := f) (s := fun _ => closedBall x₀ b) (K := K)
      (fun t ht => hlip t (hsub (Ioo_subset_Icc_self ht)))
      (show t₀ ∈ Ioo (t₀ - h) (t₀ + h) from ⟨by linarith, by linarith⟩) (fun t ht => ⟨hy t ht, hys t ht⟩) (fun t ht => ⟨hz t ht, hzs t ht⟩)
      (by rw [hy0, hz0])

/-- **Picard's theorem for systems** (Lebl, Theorem 3.1.1, in the coordinate-free form for a finite-dimensional
space `E`, e.g. `E = Fin n → ℝ`; DE-077). If `f(t, x)` is continuous on an open set `U` around `(t₀, x₀)` and
differentiable in `x` with derivative `D(t, x)` (the matrix of the partials `∂fⱼ/∂xₖ`) continuous on `U`, then
`x' = f(t, x)`, `x(t₀) = x₀` has a solution on some `(t₀ - h, t₀ + h)` and any two solutions there agree. -/
@[kb "lebldiffyqs2026" "Theorem 3.1.1, p. 125"]
theorem picard_theorem_systems [FiniteDimensional ℝ E] {f : ℝ → E → E} {D : ℝ × E → E →L[ℝ] E}
    {U : Set (ℝ × E)} (hU : IsOpen U) {t₀ : ℝ} {x₀ : E} (h0 : (t₀, x₀) ∈ U)
    (hf : ContinuousOn (fun p : ℝ × E => f p.1 p.2) U) (hD : ∀ p ∈ U, HasFDerivAt (f p.1) (D p) p.2)
    (hDc : ContinuousOn D U) :
    ∃ h > 0, (∃ y : ℝ → E, y t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (f t (y t)) t) ∧
      ∀ y z : ℝ → E, y t₀ = x₀ → z t₀ = x₀ →
        (∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (f t (y t)) t) →
        (∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt z (f t (z t)) t) →
        EqOn y z (Ioo (t₀ - h) (t₀ + h)) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU _ h0
  set r : ℝ := ρ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hR : closedBall (t₀, x₀) r ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hRc : IsCompact (closedBall (t₀, x₀) r) := isCompact_closedBall _ _
  obtain ⟨M0, hM0⟩ := hRc.exists_bound_of_continuousOn (hf.mono hR)
  obtain ⟨C0, hC0⟩ := hRc.exists_bound_of_continuousOn (hDc.mono hR)
  have hmem : ∀ t x, t ∈ Icc (t₀ - r) (t₀ + r) → x ∈ closedBall x₀ r.toNNReal →
      (t, x) ∈ closedBall (t₀, x₀) r := by
    intro t x ht hx
    rw [Real.coe_toNNReal _ hrpos.le] at hx
    rw [← closedBall_prod_same]
    exact ⟨by rwa [Real.closedBall_eq_Icc], hx⟩
  refine picard_core (a := r) (b := r.toNNReal) (K := C0.toNNReal) (M := M0.toNNReal)
    hrpos (by simpa using hrpos) ?_ ?_ ?_
  · intro x hx
    exact hf.comp (f := fun t => (t, x)) (by fun_prop) (fun t ht => hR (hmem t x ht hx))
  · intro t ht
    refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun x hx => ?_) (fun x hx => ?_)
      (convex_closedBall _ _)
    · exact (hD (t, x) (hR (hmem t x ht hx))).differentiableAt
    · rw [(hD (t, x) (hR (hmem t x ht hx))).fderiv, ← NNReal.coe_le_coe]
      simpa using (hC0 _ (hmem t x ht hx)).trans (Real.le_coe_toNNReal C0)
  · intro t ht x hx
    simpa using (hM0 _ (hmem t x ht hx)).trans (Real.le_coe_toNNReal M0)

/-- **Picard's theorem** (Lebl, Theorem 1.2.1; DE-018). Let `f(x, y)` be continuous on an open set `U` around
`(x₀, y₀)` and let `∂f/∂y` exist on `U` and be continuous there. Then `y' = f(x, y)`, `y(x₀) = y₀` has a solution on
some interval `(x₀ - h, x₀ + h)`, and any two solutions on that interval agree. -/
@[kb "lebldiffyqs2026" "Theorem 1.2.1, p. 30"]
theorem picard_theorem {f fy : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {x₀ y₀ : ℝ}
    (h0 : (x₀, y₀) ∈ U) (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) U)
    (hfy : ∀ p ∈ U, HasDerivAt (f p.1) (fy p.1 p.2) p.2)
    (hfyc : ContinuousOn (fun p : ℝ × ℝ => fy p.1 p.2) U) :
    ∃ h > 0, (∃ y : ℝ → ℝ, y x₀ = y₀ ∧ ∀ x ∈ Ioo (x₀ - h) (x₀ + h), HasDerivAt y (f x (y x)) x) ∧
      ∀ y z : ℝ → ℝ, y x₀ = y₀ → z x₀ = y₀ →
        (∀ x ∈ Ioo (x₀ - h) (x₀ + h), HasDerivAt y (f x (y x)) x) →
        (∀ x ∈ Ioo (x₀ - h) (x₀ + h), HasDerivAt z (f x (z x)) x) →
        EqOn y z (Ioo (x₀ - h) (x₀ + h)) :=
  picard_theorem_systems (D := fun p => ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1 (fy p.1 p.2)) hU h0 hf
    (fun p hp => (hfy p hp).hasFDerivAt)
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp_continuousOn hfyc)

/-- **Local solutions of `C¹` systems** (Lebl, Definition candidate D034, §3.1; DE-074). If `F(t, x)` is continuously
differentiable on an open set `U ⊆ ℝ × E`, then through every point `(t₀, x₀) ∈ U` there passes a solution of
`x' = F(t, x)` on some interval around `t₀`, and it is unique there. -/
@[kb "lebldiffyqs2026" "Definition candidate D034, p. 120"]
theorem picard_contDiff [FiniteDimensional ℝ E] {F : ℝ → E → E} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 (fun p : ℝ × E => F p.1 p.2) U) {t₀ : ℝ} {x₀ : E} (h0 : (t₀, x₀) ∈ U) :
    ∃ h > 0, (∃ y : ℝ → E, y t₀ = x₀ ∧ ∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (F t (y t)) t) ∧
      ∀ y z : ℝ → E, y t₀ = x₀ → z t₀ = x₀ →
        (∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt y (F t (y t)) t) →
        (∀ t ∈ Ioo (t₀ - h) (t₀ + h), HasDerivAt z (F t (z t)) t) →
        EqOn y z (Ioo (t₀ - h) (t₀ + h)) := by
  refine picard_theorem_systems (D := fun p => (fderiv ℝ (fun q : ℝ × E => F q.1 q.2) p).comp
    ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))) hU h0 hF.continuousOn ?_ ?_
  · intro p hp
    have hg : HasFDerivAt (fun q : ℝ × E => F q.1 q.2) (fderiv ℝ (fun q : ℝ × E => F q.1 q.2) p) p :=
      ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)).hasFDerivAt
    have hi : HasFDerivAt (fun x : E => (p.1, x)) ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
      (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
    exact hg.comp p.2 hi
  · exact (hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_comp continuousOn_const

/-- **Time translates of solutions of an autonomous system** (Lebl, §3.1, Definition candidates D036-D038; DE-076):
if `x` solves `x' = F(x)` at the points of `I`, then `t ↦ x(t + c)` solves it at the points `t` with `t + c ∈ I`. -/
@[kb "lebldiffyqs2026" "Definition candidates D036-D038, p. 124"]
theorem autonomous_translate {F : E → E} {x : ℝ → E} {I : Set ℝ}
    (hx : ∀ t ∈ I, HasDerivAt x (F (x t)) t) (c : ℝ) :
    ∀ t, t + c ∈ I → HasDerivAt (fun s => x (s + c)) (F (x (t + c))) t := fun t ht =>
  (hx (t + c) ht).comp_add_const t c

end Core

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Gluing.** Solutions on adjacent closed intervals `[p, q]` and `[q, r]` that agree at `q` glue to a solution
on `[p, r]` (one-sided derivatives at the junction add up through `HasDerivWithinAt.union`). -/
lemma picard_glue {u w : ℝ → E} {v : ℝ → E → E} {p q r : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) (huq : u q = w q)
    (hu : ∀ t ∈ Icc p q, HasDerivWithinAt u (v t (u t)) (Icc p q) t)
    (hw : ∀ t ∈ Icc q r, HasDerivWithinAt w (v t (w t)) (Icc q r) t) :
    ∃ x : ℝ → E, x q = u q ∧ (∀ t ∈ Icc p q, x t = u t) ∧
      ∀ t ∈ Icc p r, HasDerivWithinAt x (v t (x t)) (Icc p r) t := by
  classical
  let x : ℝ → E := fun t => if t ≤ q then u t else w t
  have hx1 : ∀ t ∈ Icc p q, x t = u t := fun t ht => by simp [x, ht.2]
  have hx2 : ∀ t ∈ Icc q r, x t = w t := by
    intro t ht
    by_cases h : t ≤ q
    · have : t = q := le_antisymm h ht.1
      subst this
      simp [x, huq]
    · simp [x, h]
  have hnot : ∀ {a b t : ℝ}, t ∉ Icc a b → HasDerivWithinAt x (v t (x t)) (Icc a b) t := by
    intro a b t ht
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    refine HasFDerivWithinAt.of_notMem_closure ?_
    rwa [closure_Icc]
  refine ⟨x, by simp [x], hx1, ?_⟩
  intro t ht
  rw [← Icc_union_Icc_eq_Icc hpq hqr]
  by_cases h : t ≤ q
  · have h1 : HasDerivWithinAt x (v t (x t)) (Icc p q) t := by
      rw [hx1 t ⟨ht.1, h⟩]
      exact (hu t ⟨ht.1, h⟩).congr hx1 (hx1 t ⟨ht.1, h⟩)
    refine h1.union ?_
    by_cases htq : t = q
    · subst htq
      rw [hx2 t ⟨le_rfl, hqr⟩]
      exact (hw t ⟨le_rfl, hqr⟩).congr hx2 (hx2 t ⟨le_rfl, hqr⟩)
    · exact hnot (fun hh => htq (le_antisymm h hh.1))
  · have h : q < t := not_le.mp h
    have h2 : HasDerivWithinAt x (v t (x t)) (Icc q r) t := by
      rw [hx2 t ⟨h.le, ht.2⟩]
      exact (hw t ⟨h.le, ht.2⟩).congr hx2 (hx2 t ⟨h.le, ht.2⟩)
    exact (hnot (fun hh => absurd hh.2 (not_le.mpr h))).union h2

/-- The uniform step length of the Picard steps for a linear field with `‖A‖ ≤ K`, `‖f‖ ≤ F`. -/
noncomputable def picard_delta (K F : ℝ≥0) : ℝ := 1 / (2 * (K : ℝ) + F + 1)

lemma picard_delta_pos (K F : ℝ≥0) : 0 < picard_delta K F := by
  unfold picard_delta; positivity

lemma picard_delta_mul (K F : ℝ≥0) : (2 * (K : ℝ) + F) * picard_delta K F ≤ 1 := by
  unfold picard_delta
  rw [mul_one_div, div_le_one (by positivity)]
  linarith

/-- **One Picard step for a linear system** of length `δ` that is uniform in the initial point: for a field
`A(t) x + f(t)` with `‖A‖ ≤ K`, `‖f‖ ≤ F` on `[a, b]`, a solution with arbitrary value at `s ∈ [a, b]` exists on
`[s - δ, s + δ] ∩ [a, b]`. -/
lemma picard_linear_step [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {a b : ℝ} {K F : ℝ≥0}
    (hA : ContinuousOn A (Icc a b)) (hf : ContinuousOn f (Icc a b)) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    (hF : ∀ t ∈ Icc a b, ‖f t‖ ≤ F) {s : ℝ} (hs : s ∈ Icc a b) (z : E) :
    ∃ w : ℝ → E, w s = z ∧ ∀ t ∈ Icc (max a (s - picard_delta K F)) (min b (s + picard_delta K F)),
      HasDerivWithinAt w (A t (w t) + f t) (Icc (max a (s - picard_delta K F)) (min b (s + picard_delta K F))) t := by
  set δ := picard_delta K F with hδdef
  have hδ : 0 < δ := picard_delta_pos K F
  have hδK : (2 * (K : ℝ) + F) * δ ≤ 1 := picard_delta_mul K F
  have hmem : s ∈ Icc (max a (s - δ)) (min b (s + δ)) :=
    ⟨max_le hs.1 (by linarith), le_min hs.2 (by linarith)⟩
  have hsub : Icc (max a (s - δ)) (min b (s + δ)) ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  set a' : ℝ≥0 := 1 + ‖z‖₊ with ha'
  have ha1 : (1 : ℝ) ≤ a' := by simp [ha']
  have hza : ‖z‖ ≤ a' := by simp [ha']
  have hpl : IsPicardLindelof (fun t y => A t y + f t)
      (⟨s, hmem⟩ : Icc (max a (s - δ)) (min b (s + δ))) z a' 0 ((2 * K + F) * a') K :=
    { lipschitzOnWith := fun t ht => LipschitzOnWith.of_dist_le_mul fun x _ y _ => by
        rw [dist_eq_norm, dist_eq_norm]
        have : A t x + f t - (A t y + f t) = A t (x - y) := by simp [map_sub]
        rw [this]
        exact ((A t).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hK t (hsub ht)) (norm_nonneg _))
      continuousOn := fun x _ =>
        (((hA.mono hsub).clm_apply continuousOn_const).add (hf.mono hsub))
      norm_le := fun t ht x hx => by
        have hx' : ‖x‖ ≤ 2 * (a' : ℝ) := by
          have := mem_closedBall_iff_norm.mp hx
          calc ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
            _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
            _ ≤ a' + a' := add_le_add this hza
            _ = 2 * a' := by ring
        have h1 : ‖A t x‖ ≤ K * ‖x‖ := ((A t).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hK t (hsub ht)) (norm_nonneg _))
        have h2 := hF t (hsub ht)
        calc ‖A t x + f t‖ ≤ ‖A t x‖ + ‖f t‖ := norm_add_le _ _
          _ ≤ K * (2 * a') + F * a' := by
              have e1 := mul_le_mul_of_nonneg_left hx' (NNReal.coe_nonneg K)
              have e2 := mul_le_mul_of_nonneg_left ha1 (NNReal.coe_nonneg F)
              linarith
          _ = (((2 * K + F) * a' : ℝ≥0) : ℝ) := by push_cast; ring
      mul_max_le := by
        have hm : max (min b (s + δ) - s) (s - max a (s - δ)) ≤ δ :=
          max_le (by have := min_le_right b (s + δ); linarith)
            (by have := le_max_right a (s - δ); linarith)
        have hL : (0 : ℝ) ≤ (((2 * K + F) * a' : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
        calc (((2 * K + F) * a' : ℝ≥0) : ℝ) * max (min b (s + δ) - s) (s - max a (s - δ))
            ≤ (((2 * K + F) * a' : ℝ≥0) : ℝ) * δ := mul_le_mul_of_nonneg_left hm hL
          _ = ((2 * (K : ℝ) + F) * δ) * a' := by push_cast; ring
          _ ≤ 1 * a' := mul_le_mul_of_nonneg_right hδK (NNReal.coe_nonneg _)
          _ = (a' : ℝ) - ((0 : ℝ≥0) : ℝ) := by simp }
  obtain ⟨w, hw0, hw⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨w, hw0, hw⟩

/-- Existence on `[t₀, b]` for a linear system, starting at the left endpoint (induction on the number of steps
of length `δ`, gluing with `picard_glue`). -/
lemma picard_linear_right [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {t₀ b : ℝ} (hb : t₀ ≤ b)
    (hA : ContinuousOn A (Icc t₀ b)) (hf : ContinuousOn f (Icc t₀ b)) (z : E) :
    ∃ x : ℝ → E, x t₀ = z ∧ ∀ t ∈ Icc t₀ b, HasDerivWithinAt x (A t (x t) + f t) (Icc t₀ b) t := by
  obtain ⟨K0, hK0⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨F0, hF0⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hK : ∀ t ∈ Icc t₀ b, ‖A t‖ ≤ K0.toNNReal := fun t ht =>
    (hK0 t ht).trans (Real.le_coe_toNNReal K0)
  have hF : ∀ t ∈ Icc t₀ b, ‖f t‖ ≤ F0.toNNReal := fun t ht =>
    (hF0 t ht).trans (Real.le_coe_toNNReal F0)
  set δ := picard_delta K0.toNNReal F0.toNNReal with hδdef
  have hδ : 0 < δ := picard_delta_pos _ _
  have key : ∀ n : ℕ, ∀ c ∈ Icc t₀ b, c ≤ t₀ + (n + 1) * δ →
      ∃ x : ℝ → E, x t₀ = z ∧ ∀ t ∈ Icc t₀ c, HasDerivWithinAt x (A t (x t) + f t) (Icc t₀ c) t := by
    intro n
    induction n with
    | zero =>
      intro c hc hcδ
      obtain ⟨w, hw0, hw⟩ := picard_linear_step hA hf hK hF (s := t₀) ⟨le_rfl, hb⟩ z
      have hsub : Icc t₀ c ⊆ Icc (max t₀ (t₀ - δ)) (min b (t₀ + δ)) := Icc_subset_Icc
        (by simp [hδ.le]) (le_min hc.2 (by simpa using hcδ))
      exact ⟨w, hw0, fun t ht => (hw t (hsub ht)).mono hsub⟩
    | succ n ih =>
      intro c hc hcδ
      set c' := max t₀ (c - δ) with hc'
      have hc'mem : c' ∈ Icc t₀ b := ⟨le_max_left _ _, max_le hb (by linarith [hc.2])⟩
      have hc'c : c' ≤ c := max_le hc.1 (by linarith)
      have hc'δ : c' ≤ t₀ + (n + 1) * δ := max_le (by nlinarith) (by push_cast at hcδ; nlinarith)
      obtain ⟨u, hu0, hu⟩ := ih c' hc'mem hc'δ
      obtain ⟨w, hw0, hw⟩ := picard_linear_step hA hf hK hF (s := c') hc'mem (u c')
      have hsub : Icc c' c ⊆ Icc (max t₀ (c' - δ)) (min b (c' + δ)) := Icc_subset_Icc
        (max_le hc'mem.1 (by linarith [hc'c])) (le_min hc.2 (by
          have : c - δ ≤ c' := le_max_right _ _
          linarith))
      obtain ⟨x, hxq, hxu, hx⟩ := picard_glue (v := fun t y => A t y + f t) hc'mem.1 hc'c
        (hw0.symm) hu (fun t ht => (hw t (hsub ht)).mono hsub)
      exact ⟨x, by rw [hxu t₀ ⟨le_rfl, hc'mem.1⟩, hu0], hx⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - t₀) / δ)
  have hbn : b ≤ t₀ + (n + 1) * δ := by
    rw [div_le_iff₀ hδ] at hn
    nlinarith
  exact key n b ⟨hb, le_rfl⟩ hbn

/-- **Existence for linear systems on a whole compact interval** (the existence half of Lebl, Theorems 2.1.2 and
2.3.2 for the equivalent first-order systems; DE-051, DE-062): if `A` and `f` are continuous on `[a, b]`, then for any
`t₀ ∈ [a, b]` and any `x₀` there is a solution of `x' = A(t) x + f(t)` on all of `[a, b]` (one-sided derivatives at
the endpoints) with `x(t₀) = x₀`. Uniqueness is `linear_unique`. -/
@[kb "lebldiffyqs2026" "Theorem 2.1.2, p. 80"]
theorem linear_exists [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {a b : ℝ}
    (hA : ContinuousOn A (Icc a b)) (hf : ContinuousOn f (Icc a b)) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b)
    (x₀ : E) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ Icc a b, HasDerivWithinAt x (A t (x t) + f t) (Icc a b) t := by
  obtain ⟨xr, hxr0, hxr⟩ := picard_linear_right ht₀.2 (hA.mono (Icc_subset_Icc_left ht₀.1))
    (hf.mono (Icc_subset_Icc_left ht₀.1)) x₀
  have hmap : MapsTo (fun s : ℝ => 2 * t₀ - s) (Icc t₀ (2 * t₀ - a)) (Icc a b) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1, ht₀.2]⟩
  have hmap' : MapsTo (fun s : ℝ => 2 * t₀ - s) (Icc a t₀) (Icc t₀ (2 * t₀ - a)) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨xl', hxl0, hxl⟩ := picard_linear_right (A := fun s => -A (2 * t₀ - s))
    (f := fun s => -f (2 * t₀ - s)) (t₀ := t₀) (b := 2 * t₀ - a) (by linarith [ht₀.1])
    ((hA.comp (by fun_prop) hmap).neg) ((hf.comp (by fun_prop) hmap).neg) x₀
  have hl : ∀ t ∈ Icc a t₀, HasDerivWithinAt (fun s => xl' (2 * t₀ - s))
      (A t (xl' (2 * t₀ - t)) + f t) (Icc a t₀) t := by
    intro t ht
    have hd := hxl (2 * t₀ - t) (hmap' ht)
    have hh : HasDerivWithinAt (fun s : ℝ => 2 * t₀ - s) (-1) (Icc a t₀) t :=
      ((hasDerivAt_id t).const_sub (2 * t₀)).hasDerivWithinAt
    have := HasDerivWithinAt.scomp t hd hh hmap'
    refine this.congr_deriv ?_
    have e : 2 * t₀ - (2 * t₀ - t) = t := by ring
    rw [e]
    simp
  have e0 : 2 * t₀ - t₀ = t₀ := by ring
  obtain ⟨x, hxq, hxu, hx⟩ := picard_glue (v := fun t y => A t y + f t) (u := fun s => xl' (2 * t₀ - s))
    (w := xr) ht₀.1 ht₀.2 (by rw [e0]; simp [hxl0, hxr0]) hl hxr
  refine ⟨x, ?_, hx⟩
  rw [hxq]; simp only [e0, hxl0]

/-- **Existence on an open interval for linear systems** (Lebl, Theorems 2.1.2 and 2.3.2 in system form; DE-051,
DE-062): if `A` and `f` are continuous on an open interval `I`, the solution of `x' = A(t) x + f(t)` with
`x(t₀) = x₀` exists on all of `I`. (Compact pieces `[c, d] ⊆ I` are solved by `linear_exists`; the pieces agree on
their common part by `linear_unique`.) -/
@[kb "lebldiffyqs2026" "Theorem 2.1.2, p. 80"]
theorem linear_exists_open [CompleteSpace E] {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {I : Set ℝ}
    (hIo : IsOpen I) (hI : I.OrdConnected) (hA : ContinuousOn A I) (hf : ContinuousOn f I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (x₀ : E) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ I, HasDerivAt x (A t (x t) + f t) t := by
  have key : ∀ c d : ℝ, ∃ y : ℝ → E, (c ∈ I → d ∈ I → c < t₀ → t₀ < d → y t₀ = x₀ ∧
      ∀ t ∈ Icc c d, HasDerivWithinAt y (A t (y t) + f t) (Icc c d) t) := by
    intro c d
    by_cases h : c ∈ I ∧ d ∈ I ∧ c < t₀ ∧ t₀ < d
    · obtain ⟨hc, hd, h1, h2⟩ := h
      have hsub : Icc c d ⊆ I := hI.out hc hd
      obtain ⟨y, hy0, hy⟩ := linear_exists (hA.mono hsub) (hf.mono hsub) ⟨h1.le, h2.le⟩ x₀
      exact ⟨y, fun _ _ _ _ => ⟨hy0, hy⟩⟩
    · exact ⟨0, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose Y hY using key
  have cons : ∀ c d c' d' : ℝ, c ∈ I → d ∈ I → c < t₀ → t₀ < d → c' ∈ I → d' ∈ I → c' < t₀ →
      t₀ < d' → ∀ s ∈ Ioo (max c c') (min d d'), Y c d s = Y c' d' s := by
    intro c d c' d' hc hd h1 h2 hc' hd' h1' h2'
    obtain ⟨h0, h⟩ := hY c d hc hd h1 h2
    obtain ⟨h0', h'⟩ := hY c' d' hc' hd' h1' h2'
    have hJ : Ioo (max c c') (min d d') ⊆ I := fun s hs =>
      hI.out hc hd ⟨(le_max_left c c').trans hs.1.le, hs.2.le.trans (min_le_left _ _)⟩
    have hJ' : Ioo (max c c') (min d d') ⊆ Icc c d := fun s hs =>
      ⟨(le_max_left c c').trans hs.1.le, hs.2.le.trans (min_le_left _ _)⟩
    have hJ'' : Ioo (max c c') (min d d') ⊆ Icc c' d' := fun s hs =>
      ⟨(le_max_right c c').trans hs.1.le, hs.2.le.trans (min_le_right _ _)⟩
    have hx : ∀ s ∈ Ioo (max c c') (min d d'), HasDerivAt (Y c d) (A s (Y c d s) + f s) s :=
      fun s hs => (h s (hJ' hs)).hasDerivAt (Icc_mem_nhds
        (lt_of_le_of_lt (le_max_left _ _) hs.1) (lt_of_lt_of_le hs.2 (min_le_left _ _)))
    have hy : ∀ s ∈ Ioo (max c c') (min d d'), HasDerivAt (Y c' d') (A s (Y c' d' s) + f s) s :=
      fun s hs => (h' s (hJ'' hs)).hasDerivAt (Icc_mem_nhds
        (lt_of_le_of_lt (le_max_right _ _) hs.1) (lt_of_lt_of_le hs.2 (min_le_right _ _)))
    exact linear_unique (ordConnected_Ioo) (hA.mono hJ) hx hy
      (show t₀ ∈ Ioo (max c c') (min d d') from ⟨max_lt h1 h1', lt_min h2 h2'⟩) (h0.trans h0'.symm)
  have hcd : ∀ t ∈ I, ∃ c d : ℝ, c ∈ I ∧ d ∈ I ∧ c < t₀ ∧ c < t ∧ t₀ < d ∧ t < d := by
    intro t ht
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hIo t₀ ht₀
    obtain ⟨ε', hε', hb'⟩ := Metric.isOpen_iff.mp hIo t ht
    refine ⟨min (t₀ - ε / 2) (t - ε' / 2), max (t₀ + ε / 2) (t + ε' / 2), ?_, ?_,
      lt_of_le_of_lt (min_le_left _ _) (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith),
      lt_of_lt_of_le (by linarith) (le_max_left _ _), lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
    · rcases min_choice (t₀ - ε / 2) (t - ε' / 2) with h | h <;> rw [h]
      · exact hb (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
      · exact hb' (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    · rcases max_choice (t₀ + ε / 2) (t + ε' / 2) with h | h <;> rw [h]
      · exact hb (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
      · exact hb' (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  choose! C D hCD using hcd
  refine ⟨fun t => Y (C t) (D t) t, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, -, h5, -⟩ := hCD t₀ ht₀
    exact (hY _ _ h1 h2 h3 h5).1
  · intro t ht
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hCD t ht
    have hd := ((hY (C t) (D t) h1 h2 h3 h5).2 t ⟨h4.le, h6.le⟩).hasDerivAt (Icc_mem_nhds h4 h6)
    have hev : (fun s => Y (C s) (D s) s) =ᶠ[𝓝 t] Y (C t) (D t) := by
      filter_upwards [Ioo_mem_nhds h4 h6] with s hs
      have hsI : s ∈ I := hI.out h1 h2 ⟨hs.1.le, hs.2.le⟩
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hCD s hsI
      exact cons (C s) (D s) (C t) (D t) g1 g2 g3 g5 h1 h2 h3 h5 s ⟨max_lt g4 hs.1, lt_min g6 hs.2⟩
    exact hd.congr_of_eventuallyEq hev

/-- **Existence for the second-order linear equation** (Lebl, Theorem 2.1.2, existence half; DE-051): if `p, q, f`
are continuous on an open interval `I`, then for every `t₀ ∈ I` and all values `y₀, y₁` the equation
`y'' + p y' + q y = f` has a solution on all of `I` with `y(t₀) = y₀`, `y'(t₀) = y₁`. Uniqueness is `lin2_unique`. -/
@[kb "lebldiffyqs2026" "Theorem 2.1.2, p. 80"]
theorem lin2_exists {p q f : ℝ → ℝ} {I : Set ℝ} (hIo : IsOpen I) (hI : I.OrdConnected)
    (hp : ContinuousOn p I) (hq : ContinuousOn q I) (hf : ContinuousOn f I) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (y₀ y₁ : ℝ) : ∃ y : ℝ → ℝ, SolvesLin2 p q f I y ∧ y t₀ = y₀ ∧ deriv y t₀ = y₁ := by
  obtain ⟨x, hx0, hx⟩ := linear_exists_open hIo hI (continuousOn_companion2 hp hq)
    (f := fun t => ((0 : ℝ), f t)) (continuousOn_const.prodMk hf) ht₀ (y₀, y₁)
  have h1 : ∀ t ∈ I, HasDerivAt (fun s => (x s).1) (x t).2 t := fun t ht => by
    have := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hx t ht)
    refine this.congr_deriv ?_
    simp
  have h2 : ∀ t ∈ I, HasDerivAt (fun s => (x s).2) (-(q t) * (x t).1 - p t * (x t).2 + f t) t :=
    fun t ht => by
      have := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hx t ht)
      refine this.congr_deriv ?_
      simp
  have hdy : ∀ t ∈ I, deriv (fun s => (x s).1) t = (x t).2 := fun t ht => (h1 t ht).deriv
  refine ⟨fun s => (x s).1, ?_, by simp [hx0], by rw [hdy t₀ ht₀, hx0]⟩
  intro t ht
  have hev : deriv (fun s => (x s).1) =ᶠ[𝓝 t] fun s => (x s).2 :=
    Filter.eventually_of_mem (hIo.mem_nhds ht) fun s hs => hdy s hs
  refine ⟨(h1 t ht).differentiableAt, (h2 t ht).differentiableAt.congr_of_eventuallyEq hev, ?_⟩
  rw [hev.deriv_eq, (h2 t ht).deriv, hdy t ht]
  ring

end Linear

section MatrixSys

open Matrix

variable {n : ℕ}

/-- **Existence for matrix systems** `x' = P(t) x + f(t)` in `ℝⁿ` with `P`, `f` continuous on an open interval `I`
(existence half of Lebl, Theorem 3.1.1 for linear systems; uniqueness is `matrix_linear_unique`). -/
theorem matrix_linear_exists {I : Set ℝ} (hIo : IsOpen I) (hI : I.OrdConnected)
    {P : ℝ → Matrix (Fin n) (Fin n) ℝ} {f : ℝ → Fin n → ℝ} (hP : ContinuousOn P I)
    (hf : ContinuousOn f I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (x₀ : Fin n → ℝ) :
    ∃ x : ℝ → Fin n → ℝ, x t₀ = x₀ ∧ ∀ t ∈ I, HasDerivAt x (P t *ᵥ x t + f t) t := by
  obtain ⟨x, hx0, hx⟩ := linear_exists_open hIo hI (continuousOn_matCLM hP) hf ht₀ x₀
  exact ⟨x, hx0, fun t ht => by simpa using hx t ht⟩

/-- **Existence for the `n`-th order linear equation** (Lebl, Theorem 2.3.2, existence half; DE-062): for
coefficients `a₀, …, aₙ₋₁` and `f` continuous on an open interval `I`, every initial vector
`(y(t₀), …, y⁽ⁿ⁻¹⁾(t₀))` is the initial data of a solution of `y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾ = f` on all of `I`
(a derivative chain `D`, with `D 0 = y`). Uniqueness is `linN_unique`. -/
@[kb "lebldiffyqs2026" "Theorem 2.3.2, p. 90"]
theorem linN_exists {a : Fin n → ℝ → ℝ} {f : ℝ → ℝ} {I : Set ℝ} (hIo : IsOpen I) (hI : I.OrdConnected)
    (ha : ∀ k, ContinuousOn (a k) I) (hf : ContinuousOn f I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (b : Fin n → ℝ) :
    ∃ D : Fin (n + 1) → ℝ → ℝ, SolvesLinN a f I D ∧ ∀ k : Fin n, D k.castSucc t₀ = b k := by
  obtain ⟨x, hx0, hx⟩ := matrix_linear_exists hIo hI (continuousOn_companionN ha)
    (f := fun t => lastVec (f t)) (continuousOn_pi.2 fun i => by
      simp only [lastVec]; split_ifs
      · exact hf
      · exact continuousOn_const) ht₀ b
  let D : Fin (n + 1) → ℝ → ℝ := fun k t =>
    if h : (k : ℕ) < n then x t ⟨k, h⟩ else f t - ∑ j, a j t * x t j
  have hDc : ∀ k : Fin n, D k.castSucc = fun s => x s k := fun k => by
    funext s; simp [D]
  have hDl : ∀ t, D (Fin.last n) t = f t - ∑ j, a j t * x t j := fun t => by simp [D]
  refine ⟨D, ⟨fun k t ht => ?_, fun t ht => ?_⟩, fun k => by rw [hDc k]; show x t₀ k = b k; rw [hx0]⟩
  · have hk := (hasDerivAt_pi.1 (hx t ht)) k
    rw [hDc k]
    convert hk using 1
    rw [Pi.add_apply, companionN_mulVec]
    simp only [lastVec]
    by_cases h : (k : ℕ) + 1 < n
    · have h' : (k : ℕ) + 1 ≠ n := by omega
      simp [D, h, h']
    · have h' : (k : ℕ) + 1 = n := by omega
      simp [D, h']
      ring
  · rw [hDl]
    have : ∀ j : Fin n, D j.castSucc t = x t j := fun j => by rw [hDc j]
    simp only [this]
    ring

end MatrixSys

end UndergradKB.DifferentialEquations
