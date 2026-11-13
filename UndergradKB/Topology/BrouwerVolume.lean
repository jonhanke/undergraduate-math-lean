import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import UndergradKB.Common.Attr

/-!
# No smooth retraction of the ball onto its sphere (volume argument)

The analytic step of Brouwer's fixed point theorem (Morris, *Topology Without Tears*, Remark 5.2.12,
TP-093).  Let `r` be a `C¹` map, defined on an open set containing the closed unit ball of a finite
dimensional real inner product space, sending the open ball into the unit sphere and fixing the sphere.
For small `t > 0` the map `f_t = id + t (r - id)` is injective on the closed ball and maps the open ball
onto itself (inverse function theorem and connectedness), so by the change of variables formula
`vol (ball) = ∫_{ball} det Df_t`.  The right side is a polynomial of degree at most `dim E` in `t`
(Lagrange interpolation), hence equal to `vol (ball)` also at `t = 1`; but `Df_1 = Dr` is singular
everywhere, since `‖r‖ = 1` forces the range of `Dr x` into the hyperplane orthogonal to `r x`.
-/

open Metric Set MeasureTheory Polynomial Filter Topology
open scoped RealInnerProductSpace

namespace UndergradKB.Topology

section DetPoly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `t ↦ det (1 + t A)` is a polynomial of degree at most `dim E`. -/
theorem exists_poly_det_one_add_smul (A : E →L[ℝ] E) :
    ∃ p : ℝ[X], p.natDegree ≤ Module.finrank ℝ E ∧
      ∀ t : ℝ, p.eval t = ((1 : E →L[ℝ] E) + t • A).det := by
  classical
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin _) (Fin _) ℝ).map C), ?_, ?_⟩
  · simpa using Polynomial.natDegree_det_X_add_C_le M 1
  · intro t
    have h1 : (Polynomial.evalRingHom t).mapMatrix
        ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin _) (Fin _) ℝ).map C) = t • M + 1 := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> simp [mul_comm]
    have h2 : LinearMap.toMatrix b b
        ((((1 : E →L[ℝ] E) + t • A : E →L[ℝ] E)) : E →ₗ[ℝ] E) = t • M + 1 := by
      rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul]
      rw [show ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = LinearMap.id from rfl, LinearMap.toMatrix_id]
      abel
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det, h1, ContinuousLinearMap.det,
      ← LinearMap.det_toMatrix b, h2]

/-- Interpolation weights: a polynomial of degree at most `d` is determined at `1` by its values at
`d + 1` fixed points of `(0, δ)`. -/
theorem exists_interpolation_weights (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v w : ℕ → ℝ, (∀ k, 0 < v k ∧ v k < δ) ∧
      ∀ p : ℝ[X], p.natDegree ≤ d → p.eval 1 = ∑ k ∈ Finset.range (d + 1), w k * p.eval (v k) := by
  classical
  let v : ℕ → ℝ := fun k => δ / (k + 2)
  refine ⟨v, fun k => (Lagrange.basis (Finset.range (d + 1)) v k).eval 1, ?_, ?_⟩
  · intro k
    have hk : (1 : ℝ) < k + 2 := by have := k.cast_nonneg (α := ℝ); linarith
    refine ⟨div_pos hδ (by linarith), ?_⟩
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  · intro p hp
    have hinj : Set.InjOn v (Finset.range (d + 1) : Set ℕ) := by
      intro i _ j _ hij
      have hi : (0 : ℝ) < i + 2 := by positivity
      have hj : (0 : ℝ) < j + 2 := by positivity
      simp only [v] at hij
      rw [div_eq_div_iff hi.ne' hj.ne'] at hij
      have : ((i : ℝ) + 2) = j + 2 := by
        have := mul_left_cancel₀ hδ.ne' (by linarith : δ * (j + 2) = δ * (i + 2))
        linarith
      exact_mod_cast (by linarith : (i : ℝ) = j)
    have hdeg : p.degree < (Finset.range (d + 1)).card := by
      rw [Finset.card_range]
      exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
    conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]

/-- If `‖B‖ < 1` then `det (1 + B) > 0`. -/
theorem det_one_add_pos {B : E →L[ℝ] E} (hB : ‖B‖ < 1) : 0 < ((1 : E →L[ℝ] E) + B).det := by
  have hunit : ∀ s ∈ Icc (0 : ℝ) 1, ((1 : E →L[ℝ] E) + s • B).det ≠ 0 := by
    intro s hs
    have hsB : ‖-(s • B)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖B‖ ≤ 1 * ‖B‖ := by gcongr; exact hs.2
        _ < 1 := by simpa using hB
    let u := Units.oneSub (-(s • B)) hsB
    have hu : (u : E →L[ℝ] E) = 1 + s • B := by simp [u, sub_eq_add_neg]
    have hlin : IsUnit (((1 : E →L[ℝ] E) + s • B : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
      refine ⟨⟨((u : E →L[ℝ] E) : E →ₗ[ℝ] E), ((u⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E), ?_, ?_⟩, ?_⟩
      · rw [← ContinuousLinearMap.toLinearMap_mul, u.mul_inv]; rfl
      · rw [← ContinuousLinearMap.toLinearMap_mul, u.inv_mul]; rfl
      · simp [hu]
    exact (LinearMap.isUnit_det _ hlin).ne_zero
  have hcont : ContinuousOn (fun s : ℝ => ((1 : E →L[ℝ] E) + s • B).det) (Icc 0 1) :=
    (ContinuousLinearMap.continuous_det.comp (continuous_const.add
      (continuous_id.smul continuous_const))).continuousOn
  by_contra hle
  push Not at hle
  have h0 : ((1 : E →L[ℝ] E) + (0 : ℝ) • B).det = 1 := by
    simp [ContinuousLinearMap.det]
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont
    ⟨by simpa using hle, by rw [h0]; norm_num⟩
  exact hunit s hs hs0

end DetPoly

section Retraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- If `‖r‖ = 1` near `x` and `r` has derivative `r'` at `x`, then `det r' = 0`. -/
theorem det_eq_zero_of_norm_eq_one {r : E → E} {r' : E →L[ℝ] E} {x : E}
    (hr : HasFDerivAt r r' x) (h1 : ∀ᶠ y in 𝓝 x, ‖r y‖ = 1) : r'.det = 0 := by
  have hsq : HasFDerivAt (fun y => ‖r y‖ ^ 2) (2 • (innerSL ℝ (r x)).comp r') x := by
    simpa using hr.norm_sq
  have hconst : HasFDerivAt (fun y => ‖r y‖ ^ 2) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq (h1.mono fun y hy => by simp [hy])
  have hzero := hsq.unique hconst
  have horth : ∀ v, ⟪r x, r' v⟫ = 0 := by
    intro v
    have := congrArg (fun L : E →L[ℝ] ℝ => L v) hzero
    simpa using this
  have hrx : ‖r x‖ = 1 := h1.self_of_nhds
  by_contra hdet
  have hu : IsUnit (r' : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨v, hv⟩ := (Module.End.isUnit_iff _).1 hu |>.2 (r x)
  have := horth v
  rw [show r' v = r x from hv, real_inner_self_eq_norm_sq, hrx] at this
  norm_num at this

/-- **No smooth retraction.** There is no `C¹` map `r`, defined on an open set containing the closed
unit ball, that sends the open ball into the unit sphere and fixes every point of the sphere. -/
theorem no_contDiff_retraction (μ : Measure E) [μ.IsAddHaarMeasure] {r : E → E} {U : Set E}
    (hU : IsOpen U) (hBU : closedBall (0 : E) 1 ⊆ U) (hr : ContDiffOn ℝ 1 r U)
    (hsph : ∀ x ∈ ball (0 : E) 1, ‖r x‖ = 1) (hid : ∀ x ∈ sphere (0 : E) 1, r x = x) : False := by
  classical
  set K := closedBall (0 : E) 1
  set B := ball (0 : E) 1
  let r' : E → E →L[ℝ] E := fun x => fderiv ℝ r x
  have hder : ∀ x ∈ U, HasFDerivAt r (r' x) x := fun x hx =>
    ((hr.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx) |>.hasFDerivAt
  have hr'c : ContinuousOn r' U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  have hKc : IsCompact K := isCompact_closedBall 0 1
  have hBK : B ⊆ K := ball_subset_closedBall
  -- a bound on the derivative of `g = r - id` on the closed ball
  obtain ⟨L₀, hL₀⟩ := hKc.exists_bound_of_continuousOn
    ((hr'c.mono hBU).sub continuousOn_const : ContinuousOn (fun x => r' x - 1) K)
  set L := max L₀ 0
  have hL : ∀ x ∈ K, ‖r' x - 1‖ ≤ L := fun x hx => (hL₀ x hx).trans (le_max_left _ _)
  have hL0 : 0 ≤ L := le_max_right _ _
  set δ := 1 / (L + 1)
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- the deformation
  let f : ℝ → E → E := fun t x => x + t • (r x - x)
  let f' : ℝ → E → E →L[ℝ] E := fun t x => 1 + t • (r' x - 1)
  have hf'der : ∀ t, ∀ x ∈ U, HasFDerivAt (f t) (f' t x) x := by
    intro t x hx
    exact (hasFDerivAt_id x).add (((hder x hx).sub (hasFDerivAt_id x)).const_smul t)
  -- volume identity for small `t`
  have hsmall : ∀ t, 0 < t → t < δ →
      ∫ x in B, (f' t x).det ∂μ = μ.real B := by
    intro t ht0 htδ
    have htL : t * L < 1 := by
      have : t * (L + 1) < 1 := by
        rw [lt_div_iff₀ (by linarith : (0 : ℝ) < L + 1)] at htδ
        simpa [δ] using htδ
      nlinarith
    have ht1 : t < 1 := lt_of_lt_of_le htδ hδ1
    have hnorm : ∀ x ∈ K, ‖t • (r' x - 1)‖ < 1 := by
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      calc t * ‖r' x - 1‖ ≤ t * L := by gcongr; exact hL x hx
        _ < 1 := htL
    -- injectivity on the closed ball
    have hlip : ∀ x ∈ K, ∀ y ∈ K, ‖(r y - y) - (r x - x)‖ ≤ L * ‖y - x‖ := by
      intro x hx y hy
      refine (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun z => r z - z) (f' := fun z => r' z - 1) (fun z hz => ?_) hL hx hy
      exact ((hder z (hBU hz)).sub (hasFDerivAt_id z)).hasFDerivWithinAt
    have hinj : InjOn (f t) K := by
      intro x hx y hy hxy
      by_contra hne
      have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
      have heq : (y - x) = -(t • ((r y - y) - (r x - x))) := by
        have : f t y - f t x = 0 := by rw [hxy, sub_self]
        simp only [f] at this
        rw [smul_sub] at *
        linear_combination (norm := module) this
      have : ‖y - x‖ ≤ t * (L * ‖y - x‖) := by
        calc ‖y - x‖ = t * ‖(r y - y) - (r x - x)‖ := by
              conv_lhs => rw [heq]
              rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
          _ ≤ t * (L * ‖y - x‖) := by gcongr; exact hlip x hx y hy
      nlinarith
    -- the image of the open ball is the open ball
    have hmapsB : MapsTo (f t) B B := by
      intro x hx
      rw [mem_ball_zero_iff] at hx ⊢
      have : f t x = (1 - t) • x + t • r x := by simp only [f]; module
      rw [this]
      calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * 1 := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith),
            abs_of_pos ht0, hsph x (mem_ball_zero_iff.2 hx)]
        _ < (1 - t) * 1 + t * 1 := by gcongr
        _ = 1 := by ring
    have hopen : IsOpen (f t '' B) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨x, hx, rfl⟩
      have hxU : x ∈ U := hBU (hBK hx)
      let u := Units.oneSub (-(t • (r' x - 1))) (by rw [norm_neg]; exact hnorm x (hBK hx))
      let e := ContinuousLinearEquiv.unitsEquiv ℝ E u
      have he : (e : E →L[ℝ] E) = f' t x := by
        ext v
        rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply]
        simp [u, f', sub_neg_eq_add]
      have hcd : ContDiffAt ℝ 1 (f t) x :=
        contDiffAt_id.add ((((hr.contDiffAt (hU.mem_nhds hxU))).sub contDiffAt_id).const_smul t)
      have hstrict : HasStrictFDerivAt (f t) (e : E →L[ℝ] E) x := by
        rw [he]; exact hcd.hasStrictFDerivAt (hf'der t x hxU) one_ne_zero
      rw [← hstrict.map_nhds_eq_of_equiv]
      exact image_mem_map (isOpen_ball.mem_nhds hx)
    have hsurj : f t '' B = B := by
      refine Subset.antisymm (image_subset_iff.2 hmapsB) ?_
      refine (convex_ball (0 : E) 1).isPreconnected.subset_of_closure_inter_subset hopen
        ⟨f t 0, hmapsB (mem_ball_self one_pos), mem_image_of_mem _ (mem_ball_self one_pos)⟩ ?_
      rintro y ⟨hycl, hyB⟩
      have hcK : IsClosed (f t '' K) :=
        (hKc.image_of_continuousOn (continuousOn_id.add
          ((((hr.continuousOn.mono hBU).sub continuousOn_id).const_smul t)))).isClosed
      have : y ∈ f t '' K := (closure_minimal (image_mono hBK) hcK) hycl
      obtain ⟨x, hxK, rfl⟩ := this
      by_cases hxB : x ∈ B
      · exact mem_image_of_mem _ hxB
      · exfalso
        have hxs : x ∈ sphere (0 : E) 1 := by
          rw [mem_sphere_zero_iff_norm]
          rw [mem_closedBall_zero_iff] at hxK
          rw [mem_ball_zero_iff] at hxB
          linarith
        have : f t x = x := by simp [f, hid x hxs]
        rw [this, mem_ball_zero_iff] at hyB
        rw [mem_sphere_zero_iff_norm] at hxs
        linarith
    -- change of variables
    have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_ball
      (fun x hx => (hf'der t x (hBU (hBK hx))).hasFDerivWithinAt) (hinj.mono hBK)
      (fun _ => (1 : ℝ))
    rw [hsurj] at hcv
    simp only [smul_eq_mul, mul_one, integral_const, smul_eq_mul, mul_one] at hcv
    have hre : (μ.restrict B).real univ = μ.real B := by
      simp [Measure.real, Measure.restrict_apply MeasurableSet.univ]
    rw [hre] at hcv
    rw [hcv]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    exact (abs_of_pos (det_one_add_pos (hnorm x (hBK hx)))).symm
  -- polynomial interpolation
  obtain ⟨v, w, hv, hw⟩ := exists_interpolation_weights (Module.finrank ℝ E) hδ
  have hint : ∀ t, IntegrableOn (fun x => (f' t x).det) B μ := by
    intro t
    refine (ContinuousOn.integrableOn_compact hKc ?_).mono_set hBK
    exact ContinuousLinearMap.continuous_det.comp_continuousOn
      (continuousOn_const.add (((hr'c.mono hBU).sub continuousOn_const).const_smul t))
  have hpt : ∀ x, (f' 1 x).det =
      ∑ k ∈ Finset.range (Module.finrank ℝ E + 1), w k * (f' (v k) x).det := by
    intro x
    obtain ⟨p, hp, hpe⟩ := exists_poly_det_one_add_smul (r' x - 1)
    rw [← hpe, hw p hp]
    simp only [hpe, f']
  have hconst : (1 : ℝ) = ∑ k ∈ Finset.range (Module.finrank ℝ E + 1), w k := by
    have := hw (C 1) (by simp)
    simpa using this
  have h1 : ∫ x in B, (f' 1 x).det ∂μ = μ.real B := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ => (hint (v k)).const_mul (w k)]
    simp_rw [integral_const_mul]
    rw [Finset.sum_congr rfl fun k _ => by rw [hsmall (v k) (hv k).1 (hv k).2], ← Finset.sum_mul,
      ← hconst, one_mul]
  -- but `det Dr = 0`
  have h0 : ∫ x in B, (f' 1 x).det ∂μ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have : f' 1 x = r' x := by simp [f']
    rw [this]
    exact det_eq_zero_of_norm_eq_one (hder x (hBU (hBK hx)))
      (eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy => hsph y hy)
  have hpos : 0 < μ.real B := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

end Retraction

end UndergradKB.Topology
