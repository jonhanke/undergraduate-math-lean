import UndergradKB.Topology.BrouwerVolume
import UndergradKB.Topology.Brouwer
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import UndergradKB.Common.Attr

/-!
# Brouwer's fixed point theorem (TP-093)

Morris, *Topology Without Tears*, Remark 5.2.12: a continuous self-map of the closed `n`-cube (and of
the closed unit ball of `ℝⁿ`) has a fixed point.  Route: a fixed-point-free continuous self-map of the
closed ball is approximated uniformly by a smooth one that is still a fixed-point-free self-map of the
ball (Stone-Weierstrass on the coordinates, then a slight shrinking); the ray from `G x` through `x`
gives a smooth retraction onto the sphere, defined on an open set containing the ball, which
`no_contDiff_retraction` (file `BrouwerVolume.lean`) rules out.
-/

open Metric Set MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace UndergradKB.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Smooth

/-- The real functions on a set `K` that are restrictions of smooth functions form a subalgebra. -/
def smoothRestrictions (K : Set E) : Subalgebra ℝ C(K, ℝ) where
  carrier := {g | ∃ φ : E → ℝ, ContDiff ℝ ⊤ φ ∧ ∀ x : K, g x = φ x}
  mul_mem' := by
    rintro g h ⟨φ, hφ, hg⟩ ⟨ψ, hψ, hh⟩
    exact ⟨fun x => φ x * ψ x, hφ.mul hψ, fun x => by simp [hg, hh]⟩
  add_mem' := by
    rintro g h ⟨φ, hφ, hg⟩ ⟨ψ, hψ, hh⟩
    exact ⟨fun x => φ x + ψ x, hφ.add hψ, fun x => by simp [hg, hh]⟩
  algebraMap_mem' := by
    intro c
    exact ⟨fun _ => c, contDiff_const, fun x => by simp⟩

omit [FiniteDimensional ℝ E] in
theorem smoothRestrictions_separatesPoints (K : Set E) :
    (smoothRestrictions K).SeparatesPoints := by
  intro x y hxy
  have hne : (x : E) ≠ y := fun h => hxy (Subtype.ext h)
  let φ : E → ℝ := fun z => ⟪(x : E) - y, z⟫
  have hφ : ContDiff ℝ ⊤ φ := contDiff_const.inner ℝ contDiff_id
  let gK : C(K, ℝ) := ⟨fun z => φ z, hφ.continuous.comp continuous_subtype_val⟩
  have hmem : gK ∈ smoothRestrictions K := ⟨φ, hφ, fun z => rfl⟩
  refine ⟨gK, ⟨gK, hmem, rfl⟩, ?_⟩
  intro h
  apply hne
  have : ⟪(x : E) - y, (x : E) - y⟫ = 0 := by
    have h' : ⟪(x : E) - y, (x : E)⟫ = ⟪(x : E) - y, (y : E)⟫ := h
    rw [inner_sub_right]; linarith
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

/-- A continuous map on a compact set `K` with values in `E` is a uniform limit on `K` of smooth maps
`E → E`. -/
theorem exists_contDiff_near {K : Set E} (hK : IsCompact K) {f : E → E} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) : ∃ h : E → E, ContDiff ℝ ⊤ h ∧ ∀ x ∈ K, ‖h x - f x‖ < ε := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let b := stdOrthonormalBasis ℝ E
  set d := Module.finrank ℝ E
  set ε' := ε / (d + 1)
  have hε' : 0 < ε' := by positivity
  have happrox : ∀ i, ∃ φ : E → ℝ, ContDiff ℝ ⊤ φ ∧ ∀ x ∈ K, |φ x - ⟪b i, f x⟫| < ε' := by
    intro i
    have hc : Continuous fun x : K => ⟪b i, f x⟫ :=
      continuous_const.inner (continuousOn_iff_continuous_domRestrict.1 hf)
    obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      (smoothRestrictions K) (smoothRestrictions_separatesPoints K) _ hc ε' hε'
    obtain ⟨φ, hφ, hgφ⟩ := g.2
    refine ⟨φ, hφ, fun x hx => ?_⟩
    have := hg ⟨x, hx⟩
    rw [hgφ] at this
    simpa [Real.norm_eq_abs] using this
  choose φ hφ hφK using happrox
  refine ⟨fun x => ∑ i, φ i x • b i, ContDiff.sum fun i _ => (hφ i).smul contDiff_const, ?_⟩
  intro x hx
  have hfx : f x = ∑ i, ⟪b i, f x⟫ • b i := (b.sum_repr' (f x)).symm
  calc ‖∑ i, φ i x • b i - f x‖ = ‖∑ i, (φ i x - ⟪b i, f x⟫) • b i‖ := by
        conv_lhs => rw [hfx]
        rw [← Finset.sum_sub_distrib]
        simp_rw [sub_smul]
    _ ≤ ∑ i, ‖(φ i x - ⟪b i, f x⟫) • b i‖ := norm_sum_le _ _
    _ = ∑ i, |φ i x - ⟪b i, f x⟫| := by
        simp_rw [norm_smul, b.orthonormal.1, mul_one, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin d, ε' := Finset.sum_le_sum fun i _ => (hφK i x hx).le
    _ = d * ε' := by simp
    _ < ε := by
        simp only [ε']
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- A fixed-point-free continuous self-map of the closed unit ball can be replaced by a smooth one. -/
theorem exists_contDiff_fixedPointFree {f : E → E} (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) (hfix : ∀ x ∈ closedBall (0 : E) 1, f x ≠ x) :
    ∃ G : E → E, ContDiff ℝ ⊤ G ∧ MapsTo G (closedBall 0 1) (closedBall 0 1) ∧
      ∀ x ∈ closedBall (0 : E) 1, G x ≠ x := by
  have hK : IsCompact (closedBall (0 : E) 1) := isCompact_closedBall 0 1
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn ⟨0, mem_closedBall_self zero_le_one⟩
    ((hf.sub continuousOn_id).norm)
  set m := ‖f x₀ - x₀‖
  have hm : 0 < m := norm_pos_iff.2 (sub_ne_zero.2 (hfix x₀ hx₀))
  set η := m / 3
  have hη : 0 < η := by positivity
  obtain ⟨h, hh, hhf⟩ := exists_contDiff_near hK hf hη
  refine ⟨fun x => (1 + η)⁻¹ • h x, contDiff_const.smul hh, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + η), inv_mul_le_iff₀ (by linarith), mul_one]
    have h1 : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hmaps hx)
    calc ‖h x‖ = ‖(h x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖h x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ η + 1 := by linarith [hhf x hx]
      _ = 1 + η := by ring
  · intro x hx heq
    have hmx : m ≤ ‖f x - x‖ := hmin hx
    have hfx1 : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hmaps hx)
    have hhx : ‖h x‖ ≤ 1 + η := by
      calc ‖h x‖ = ‖(h x - f x) + f x‖ := by rw [sub_add_cancel]
        _ ≤ ‖h x - f x‖ + ‖f x‖ := norm_add_le _ _
        _ ≤ 1 + η := by linarith [hhf x hx]
    have hGh : ‖(1 + η)⁻¹ • h x - h x‖ ≤ η := by
      have : (1 + η)⁻¹ • h x - h x = (-(η / (1 + η))) • h x := by
        rw [show (1 + η)⁻¹ • h x - h x = ((1 + η)⁻¹ - 1) • h x by rw [sub_smul, one_smul]]
        congr 1
        field_simp
        ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity),
        div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    have : ‖f x - x‖ ≤ ‖(1 + η)⁻¹ • h x - h x‖ + ‖h x - f x‖ := by
      have heq' : (1 + η)⁻¹ • h x = x := heq
      calc ‖f x - x‖ = ‖-(((1 + η)⁻¹ • h x - h x) + (h x - f x))‖ := by
            rw [heq']; congr 1; abel
        _ =‖((1 + η)⁻¹ • h x - h x) + (h x - f x)‖ := norm_neg _
        _ ≤ _ := norm_add_le _ _
    have := hhf x hx
    simp only [η] at *
    linarith

end Smooth

section Ray

omit [FiniteDimensional ℝ E] in
/-- **The ray retraction is smooth.** For a smooth fixed-point-free self-map `G` of the closed unit
ball, the map sending `x` to the point where the ray from `G x` through `x` meets the sphere is `C¹` on
an open set containing the ball, has norm one there and fixes the sphere. -/
theorem exists_contDiff_retraction_of_fixedPointFree {G : E → E} (hG : ContDiff ℝ ⊤ G)
    (hmaps : MapsTo G (closedBall 0 1) (closedBall 0 1)) (hfix : ∀ x ∈ closedBall (0 : E) 1, G x ≠ x) :
    ∃ (r : E → E) (U : Set E), IsOpen U ∧ closedBall (0 : E) 1 ⊆ U ∧ ContDiffOn ℝ 1 r U ∧
      (∀ x ∈ U, ‖r x‖ = 1) ∧ ∀ x ∈ sphere (0 : E) 1, r x = x := by
  let d : E → E := fun x => x - G x
  let a : E → ℝ := fun x => ‖d x‖ ^ 2
  let b : E → ℝ := fun x => ⟪x, d x⟫
  let q : E → ℝ := fun x => b x ^ 2 + a x * (1 - ‖x‖ ^ 2)
  let lam : E → ℝ := fun x => (Real.sqrt (q x) - b x) / a x
  let r : E → E := fun x => x + lam x • d x
  have hd : ContDiff ℝ ⊤ d := contDiff_id.sub hG
  have ha : ContDiff ℝ ⊤ a := (contDiff_norm_sq ℝ).comp hd
  have hb : ContDiff ℝ ⊤ b := contDiff_id.inner ℝ hd
  have hq : ContDiff ℝ ⊤ q := (hb.pow 2).add (ha.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))
  let U : Set E := {x | 0 < a x} ∩ {x | 0 < q x}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const ha.continuous).inter (isOpen_lt continuous_const hq.continuous)
  have hKU : closedBall (0 : E) 1 ⊆ U := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hG1 : ‖G x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hmaps hx)
    have hapos : 0 < a x := pow_pos (norm_pos_iff.2 (sub_ne_zero.2 (hfix x hx).symm)) 2
    refine ⟨hapos, ?_⟩
    show 0 < b x ^ 2 + a x * (1 - ‖x‖ ^ 2)
    rcases hx1.lt_or_eq with hlt | heq
    · have : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (b x), mul_pos hapos this]
    · -- on the sphere `b ≥ a / 2 > 0`
      have hab : a x ≤ 2 * b x := by
        have e1 : a x = ‖x‖ ^ 2 - 2 * ⟪x, G x⟫ + ‖G x‖ ^ 2 := by
          simp only [a, d]; rw [norm_sub_sq_real]
        have e2 : b x = ‖x‖ ^ 2 - ⟪x, G x⟫ := by
          simp only [b, d]; rw [inner_sub_right, real_inner_self_eq_norm_sq]
        rw [e1, e2, heq]
        nlinarith [norm_nonneg (G x)]
      have : 0 < b x := by linarith
      have : 1 - ‖x‖ ^ 2 = 0 := by rw [heq]; norm_num
      rw [this, mul_zero, add_zero]
      positivity
  refine ⟨r, U, hU, hKU, ?_, ?_, ?_⟩
  · intro x hx
    refine ContDiffAt.contDiffWithinAt ?_
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (q y)) x :=
      (hq.contDiffAt.of_le le_top).sqrt hx.2.ne'
    have hlam : ContDiffAt ℝ 1 lam x :=
      (hsq.sub (hb.contDiffAt.of_le le_top)).div (ha.contDiffAt.of_le le_top) hx.1.ne'
    exact contDiffAt_id.add (hlam.smul (hd.contDiffAt.of_le le_top))
  · intro x hx
    have hapos : 0 < a x := hx.1
    have hq0 : 0 ≤ q x := hx.2.le
    set s := Real.sqrt (q x)
    have hs : s ^ 2 = q x := Real.sq_sqrt hq0
    have hlamx : lam x * a x = s - b x := by
      show (Real.sqrt (q x) - b x) / a x * a x = s - b x
      rw [div_mul_cancel₀ _ hapos.ne']
    have hn : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * b x + lam x ^ 2 * a x := by
      simp only [r, a, b]
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have h1 : ‖r x‖ ^ 2 = 1 := by
      rw [hn]
      have : lam x * (lam x * a x + 2 * b x) = 1 - ‖x‖ ^ 2 := by
        rw [hlamx]
        have hlam' : lam x = (s - b x) / a x := rfl
        rw [hlam']
        field_simp
        have : s ^ 2 - b x ^ 2 = a x * (1 - ‖x‖ ^ 2) := by rw [hs]; simp only [q]; ring
        nlinarith [this]
      nlinarith [this]
    have := norm_nonneg (r x)
    nlinarith [sq_nonneg (‖r x‖ - 1), sq_nonneg (‖r x‖ + 1)]
  · intro x hx
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
    have hxK : x ∈ closedBall (0 : E) 1 := sphere_subset_closedBall hx
    have hb0 : 0 ≤ b x := by
      have hG1 : ‖G x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hmaps hxK)
      have e2 : b x = ‖x‖ ^ 2 - ⟪x, G x⟫ := by
        simp only [b, d]; rw [inner_sub_right, real_inner_self_eq_norm_sq]
      have : ⟪x, G x⟫ ≤ 1 := by
        calc ⟪x, G x⟫ ≤ ‖x‖ * ‖G x‖ := real_inner_le_norm _ _
          _ ≤ 1 := by rw [hx1, one_mul]; exact hG1
      rw [e2, hx1]; linarith
    have hqx : q x = b x ^ 2 := by simp only [q]; rw [hx1]; ring
    have : lam x = 0 := by
      simp only [lam]; rw [hqx, Real.sqrt_sq hb0, sub_self, zero_div]
    simp [r, this]

end Ray

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093). **Brouwer's fixed point theorem** for the
closed unit ball of a finite-dimensional real inner product space: a continuous self-map of the
ball has a fixed point. -/
@[kb "morris2024" "Remark 5.2.12, p. 120"]
theorem brouwer_closedBall {f : E → E} (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) : ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  by_contra hno
  push Not at hno
  obtain ⟨G, hG, hGmaps, hGfix⟩ := exists_contDiff_fixedPointFree hf hmaps hno
  obtain ⟨r, U, hU, hKU, hr, hr1, hrid⟩ :=
    exists_contDiff_retraction_of_fixedPointFree hG hGmaps hGfix
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact no_contDiff_retraction Measure.addHaar hU hKU hr
    (fun x hx => hr1 x (hKU (ball_subset_closedBall hx))) hrid

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093). There is no continuous retraction of the
closed unit ball of `ℝⁿ` onto its boundary sphere. -/
@[kb "morris2024" "Remark 5.2.12, p. 120"]
theorem no_retraction_cell (n : ℕ) :
    ¬ ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn r (Cell n) ∧ (∀ x ∈ Cell n, r x ∈ UnitSphere n) ∧ ∀ x ∈ UnitSphere n, r x = x := by
  rintro ⟨r, hr, hrS, hrid⟩
  obtain ⟨x, hx, hfx⟩ := brouwer_closedBall (f := fun x => -r x) hr.neg (by
    intro x hx
    have := hrS x hx
    rw [mem_closedBall_zero_iff, norm_neg]
    exact (mem_sphere_zero_iff_norm.1 this).le)
  have h1 : ‖r x‖ = 1 := mem_sphere_zero_iff_norm.1 (hrS x hx)
  have hrx : r x = -x := neg_eq_iff_eq_neg.1 hfx
  have hxs : x ∈ UnitSphere n := by
    rw [mem_sphere_zero_iff_norm, ← norm_neg, ← hrx, h1]
  have h2 : x = -x := (hrid x hxs).symm.trans hrx
  have h0 : x = 0 := by
    have : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rw 1 [h2]; exact neg_add_cancel x
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hxs
  exact zero_ne_one hxs

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093). **Brouwer's fixed point theorem**: every
continuous self-map of the closed unit ball `Cell n` of `ℝⁿ` has a fixed point. -/
@[kb "morris2024" "Remark 5.2.12, p. 120"]
theorem hasFixedPointProp_cell (n : ℕ) : HasFixedPointProp ↥(Cell n) :=
  hasFixedPointProp_cell_of_no_retraction n (no_retraction_cell n)

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093). **Brouwer's fixed point theorem**: every
continuous self-map of the closed `n`-cube `[0,1]ⁿ` has a fixed point. -/
@[kb "morris2024" "Remark 5.2.12, p. 120"]
theorem hasFixedPointProp_cube (n : ℕ) : HasFixedPointProp (Fin n → unitInterval) :=
  hasFixedPointProp_cube_of_no_retraction n (no_retraction_cell n)

end UndergradKB.Topology
