import UndergradKB.Topology.ProductsQuotients
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UndergradKB.Common.Attr

/-!
# Brouwer's fixed point theorem: plan and the reductions that are proved (TP-093)

Morris, *Topology Without Tears*, Remark 5.2.12: a continuous self-map of a closed `n`-cube has a fixed
point.  Mathlib has neither degree theory, homology, Sperner's lemma, nor the KKM lemma, so the whole
theorem must be built.  Status of the attempt (see also `docs/coverage/topology/parts/lean-b2z.tsv`).
Wave 2: the theorem is now proved (`hasFixedPointProp_cube`, `hasFixedPointProp_cell`,
`brouwer_closedBall` in `BrouwerSmooth.lean`) by a variant of the plan below that avoids the Piola
identity: the volume argument of `BrouwerVolume.lean` (change of variables for `id + t (r - id)` and
Lagrange interpolation in `t`).

## Plan (analytic route, Milnor-Rogers/Lax)

1. (DONE here, `brouwer_of_no_retraction`) A continuous self-map of the closed unit ball of
   `EuclideanSpace ℝ (Fin n)` without fixed point yields a continuous retraction of the ball onto the
   sphere (follow the ray from `f x` through `x`; the quadratic formula gives a continuous coefficient).
2. (DONE here, `HasFixedPointProp.of_homeomorph`) The fixed point property is invariant under
   homeomorphism, so the cube, the ball and any cell are interchangeable once one cell homeomorphism
   is available.
3. (NOT DONE) No continuous retraction `Cell n → UnitSphere n` exists.  Route: a continuous retraction
   can be replaced by a `C²` one (polynomial approximation of `f`, then the explicit formula of step 1
   with a polynomial `f`); for a `C²` retraction `r`, `∫_{B} det Dr = vol B` because `∫_B det Dφ`
   depends only on `φ|∂B` (Piola identity `∑_j ∂_j cof(Dφ)_{ij} = 0` plus the fundamental theorem of
   calculus applied to `h = r - id`, which vanishes on `∂B`), whereas `|r| = 1` forces `det Dr = 0`.
4. (NOT DONE) The cube version follows from the ball version by a homeomorphism of the two cells.

The missing lemmas are therefore: (a) the Piola identity for `C²` maps `ℝⁿ → ℝⁿ`; (b) the integral
identity `∫_B det Dφ = ∫_B det Dψ` for `C²` maps agreeing on `∂B`; (c) polynomial approximation of
the retraction; (d) the cube/ball homeomorphism.
-/

open Metric Set
open scoped RealInnerProductSpace

namespace UndergradKB.Topology

/-- A space has the fixed point property if every continuous self-map has a fixed point. -/
def HasFixedPointProp (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : X → X, Continuous f → ∃ x, f x = x

/-- The fixed point property is invariant under homeomorphism. -/
theorem HasFixedPointProp.of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : HasFixedPointProp X) : HasFixedPointProp Y := by
  intro f hf
  obtain ⟨x, hx⟩ := h (e.symm ∘ f ∘ e) (e.symm.continuous.comp (hf.comp e.continuous))
  refine ⟨e x, ?_⟩
  have : e.symm (f (e x)) = x := hx
  calc f (e x) = e (e.symm (f (e x))) := (e.apply_symm_apply _).symm
    _ = e x := by rw [this]

section Ray

variable {n : ℕ}

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093), reduction. If there is no continuous
retraction of the closed unit ball of `ℝⁿ` onto the unit sphere, every continuous self-map of the ball
has a fixed point. -/
theorem brouwer_of_no_retraction
    (hno : ¬ ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn r (Cell n) ∧ (∀ x ∈ Cell n, r x ∈ UnitSphere n) ∧ ∀ x ∈ UnitSphere n, r x = x)
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : ContinuousOn f (Cell n))
    (hmaps : MapsTo f (Cell n) (Cell n)) : ∃ x ∈ Cell n, f x = x := by
  by_contra hfix
  push Not at hfix
  -- quantities of the ray construction
  let d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => x - f x
  let a : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ‖d x‖ ^ 2
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪x, d x⟫
  let s : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.sqrt (b x ^ 2 + a x * (1 - ‖x‖ ^ 2))
  let lam : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (s x - b x) / a x
  let r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => x + lam x • d x
  have hd : ContinuousOn d (Cell n) := continuousOn_id.sub hf
  have ha_pos : ∀ x ∈ Cell n, 0 < a x := by
    intro x hx
    have : d x ≠ 0 := sub_ne_zero.2 (hfix x hx).symm
    exact pow_pos (norm_pos_iff.2 this) 2
  have ha : ContinuousOn a (Cell n) := hd.norm.pow 2
  have hb : ContinuousOn b (Cell n) := continuousOn_id.inner hd
  have hs : ContinuousOn s (Cell n) :=
    Real.continuous_sqrt.comp_continuousOn
      ((hb.pow 2).add (ha.mul ((continuousOn_const.sub (continuousOn_id.norm.pow 2)))))
  have hlam : ContinuousOn lam (Cell n) :=
    (hs.sub hb).div ha (fun x hx => (ha_pos x hx).ne')
  have hr : ContinuousOn r (Cell n) := continuousOn_id.add (hlam.smul hd)
  apply hno
  refine ⟨r, hr, fun x hx => ?_, fun x hx => ?_⟩
  · -- r x lies on the sphere
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hax := ha_pos x hx
    have hnn : 0 ≤ b x ^ 2 + a x * (1 - ‖x‖ ^ 2) := by
      have : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      positivity
    have hs2 : s x ^ 2 = b x ^ 2 + a x * (1 - ‖x‖ ^ 2) := Real.sq_sqrt hnn
    have hsq : ‖r x‖ ^ 2 = 1 := by
      have e1 : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, lam x • d x⟫ + ‖lam x • d x‖ ^ 2 :=
        norm_add_sq_real _ _
      rw [inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at e1
      rw [e1]
      have : (lam x) ^ 2 * ‖d x‖ ^ 2 + 2 * (lam x * b x) = 1 - ‖x‖ ^ 2 := by
        show (lam x) ^ 2 * a x + 2 * (lam x * b x) = 1 - ‖x‖ ^ 2
        simp only [lam]
        field_simp
        nlinarith [hs2]
      show ‖x‖ ^ 2 + 2 * (lam x * b x) + lam x ^ 2 * ‖d x‖ ^ 2 = 1
      linarith
    rw [mem_sphere_zero_iff_norm]
    have h0 := norm_nonneg (r x)
    nlinarith
  · -- r x = x on the sphere
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
    have hxc : x ∈ Cell n := mem_closedBall_zero_iff.2 hx1.le
    have hb0 : 0 ≤ b x := by
      show 0 ≤ ⟪x, x - f x⟫
      rw [inner_sub_right, real_inner_self_eq_norm_sq, hx1]
      have h1 : ⟪x, f x⟫ ≤ ‖x‖ * ‖f x‖ := real_inner_le_norm _ _
      have h2 : ‖f x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hmaps hxc)
      rw [hx1] at h1
      linarith
    have hs0 : s x = b x := by
      show Real.sqrt (b x ^ 2 + a x * (1 - ‖x‖ ^ 2)) = b x
      rw [hx1]
      simp [Real.sqrt_sq hb0]
    have : lam x = 0 := by simp [lam, hs0]
    simp [r, this]

end Ray

section CubeCell

/-- The embedding of the `n`-cube `[0,1]ⁿ` into Euclidean space. -/
noncomputable def cubeToEuclid (n : ℕ) (c : Fin n → unitInterval) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => (c i : ℝ))

theorem continuous_cubeToEuclid (n : ℕ) : Continuous (cubeToEuclid n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp
    (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))

theorem cubeToEuclid_apply (n : ℕ) (c : Fin n → unitInterval) (i : Fin n) :
    cubeToEuclid n c i = (c i : ℝ) := rfl

theorem injective_cubeToEuclid (n : ℕ) : Function.Injective (cubeToEuclid n) := by
  intro c c' h
  funext i
  apply Subtype.ext
  have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
  simpa [cubeToEuclid_apply] using this

theorem range_cubeToEuclid (n : ℕ) :
    range (cubeToEuclid n) = {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩ i
    exact (c i).2
  · intro hx
    refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
    ext i
    rfl

/-- The `n`-cube `[0,1]ⁿ` is homeomorphic to the closed unit ball of `ℝⁿ` (Morris, Proposition 11.2.9
and the surrounding discussion of cells; used to move Brouwer's theorem between cube and ball). -/
theorem nonempty_homeomorph_cube_cell (n : ℕ) :
    Nonempty ((Fin n → unitInterval) ≃ₜ ↥(Cell n)) := by
  have hemb : Topology.IsClosedEmbedding (cubeToEuclid n) :=
    (continuous_cubeToEuclid n).isClosedEmbedding (injective_cubeToEuclid n)
  let e0 : (Fin n → unitInterval) ≃ₜ range (cubeToEuclid n) :=
    hemb.isEmbedding.toHomeomorph
  set s := range (cubeToEuclid n) with hs
  have hseq : s = {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Icc (0 : ℝ) 1} :=
    range_cubeToEuclid n
  have hconv : Convex ℝ s := by
    rw [hseq]
    intro x hx y hy a b ha hb hab i
    have h1 := hx i
    have h2 := hy i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hbdd : Bornology.IsBounded s := (isCompact_range (continuous_cubeToEuclid n)).isBounded
  have hne : (interior s).Nonempty := by
    refine ⟨cubeToEuclid n (fun _ => ⟨1 / 2, by norm_num, by norm_num⟩), ?_⟩
    rw [mem_interior]
    refine ⟨{x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1}, ?_, ?_, ?_⟩
    · intro x hx
      rw [hseq]
      exact fun i => Ioo_subset_Icc_self (hx i)
    · have : {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Ioo (0 : ℝ) 1} =
          ⋂ i, (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' Ioo (0 : ℝ) 1 := by
        ext x; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous
    · intro i
      simp [cubeToEuclid_apply]
      norm_num
  obtain ⟨h, -, hcl, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hne hbdd
  have hclosed : closure s = s := hemb.isClosed_range.closure_eq
  rw [hclosed] at hcl
  exact ⟨e0.trans ((h.image s).trans (Homeomorph.setCongr hcl))⟩

end CubeCell

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093), conditional form. If there is no
continuous retraction of the closed unit ball of `ℝⁿ` onto the unit sphere (the missing analytic
lemma, see the header), then the ball and the `n`-cube have the fixed point property. -/
theorem hasFixedPointProp_cell_of_no_retraction (n : ℕ)
    (hno : ¬ ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn r (Cell n) ∧ (∀ x ∈ Cell n, r x ∈ UnitSphere n) ∧ ∀ x ∈ UnitSphere n, r x = x) :
    HasFixedPointProp ↥(Cell n) := by
  classical
  intro f hf
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => if h : x ∈ Cell n then (f ⟨x, h⟩ : EuclideanSpace ℝ (Fin n)) else 0
  have hFc : ContinuousOn F (Cell n) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (Cell n).domRestrict F = fun x => (f x : EuclideanSpace ℝ (Fin n)) := by
      funext x
      show F x = _
      simp only [F]
      rw [dif_pos x.2]
    rw [this]
    exact continuous_subtype_val.comp hf
  have hmaps : MapsTo F (Cell n) (Cell n) := by
    intro x hx
    simp only [F, dif_pos hx]
    exact (f ⟨x, hx⟩).2
  obtain ⟨x, hx, hfx⟩ := brouwer_of_no_retraction hno hFc hmaps
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  simp only [F] at hfx
  rw [dif_pos hx] at hfx
  exact hfx

/-- Morris, Topology Without Tears, Remark 5.2.12 (TP-093), conditional form for the cube. -/
theorem hasFixedPointProp_cube_of_no_retraction (n : ℕ)
    (hno : ¬ ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn r (Cell n) ∧ (∀ x ∈ Cell n, r x ∈ UnitSphere n) ∧ ∀ x ∈ UnitSphere n, r x = x) :
    HasFixedPointProp (Fin n → unitInterval) := by
  obtain ⟨e⟩ := nonempty_homeomorph_cube_cell n
  exact (hasFixedPointProp_cell_of_no_retraction n hno |>.of_homeomorph e.symm)

end UndergradKB.Topology
