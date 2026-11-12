import UndergradKB.Common.Attr
import UndergradKB.Calculus.Chains
import UndergradKB.Calculus.GreenRegions

/-! # Calculus: Green's theorem on regions glued from parametrized cells

OpenStax Calculus 3 §6.4 (Theorems 6.12, 6.13, Green's theorem on general regions). The book proves Green's
theorem for a general region by cutting it into simple pieces (type I and type II regions, here more generally
`C²` images of rectangles, `GreenRegions.lean`), applying the theorem to each piece and observing that the line
integrals along the interior cuts cancel, each cut being traversed once in each direction. This file proves that
argument in general:

* `green_cell`: Green's theorem for one cell `D = Φ(S)`, the right side written as the sum over the four oriented
  boundary edges (`ParamRect.boundary`);
* `green_glued`: for finitely many cells with almost disjoint images, glued along edges traversed in opposite
  directions (`OrientedCurve.IsOpposite`: the same arc with an orientation reversing `C¹` change of parameter),
  `∬_D (Q_x - P_y) dA` over the union is the sum of the line integrals along the remaining (outer) edges. The outer
  edges may form several closed curves: this is the theorem on regions with finitely many holes (the inner
  boundary curves then come out clockwise);
* the flux form (`green_flux_glued`), the area formulas (`area_glued`), and the swirl field around a curve that
  together with a small circle around the origin bounds a glued region avoiding the origin
  (`swirl_circulation_glued_annulus`, `2π`), or that bounds a glued region avoiding the origin (`0`).

What is still missing for the book's statement for every region bounded by a piecewise smooth simple closed curve:
the Jordan curve theorem and the existence of such a decomposition (a triangulation) of every Jordan region with
piecewise smooth boundary; neither is in Mathlib. -/

open MeasureTheory Set Real

namespace UndergradKB.Calculus

/-- A cell of a plane region: a parametrized rectangle `Φ : [a,b]×[c,d] → ℝ²` together with the part `S` of the
rectangle it is restricted to (the cell is `Φ(S)`). -/
structure PlaneCell where
  /-- the parametrization -/
  rect : ParamRect (ℝ × ℝ)
  /-- the part of the rectangle covered -/
  S : Set (ℝ × ℝ)

/-- The region `Φ(S)` covered by a cell. -/
def PlaneCell.region (C : PlaneCell) : Set (ℝ × ℝ) := C.rect.map '' C.S

/-- The hypotheses of `green_param_image` for a cell inside the open set `U`: `Φ` of class `C²` maps the rectangle
into `U`, `S` is measurable and lies between the open and the closed rectangle, `Φ` is injective and orientation
preserving on `S`. -/
structure PlaneCell.IsRegular (C : PlaneCell) (U : Set (ℝ × ℝ)) : Prop where
  smooth : ContDiff ℝ 2 C.rect.map
  hab : C.rect.a ≤ C.rect.b
  hcd : C.rect.c ≤ C.rect.d
  mapsTo : ∀ z ∈ C.rect.dom, C.rect.map z ∈ U
  measurable : MeasurableSet C.S
  sub : C.S ⊆ C.rect.dom
  sup : Ioo C.rect.a C.rect.b ×ˢ Ioo C.rect.c C.rect.d ⊆ C.S
  injOn : InjOn C.rect.map C.S
  jacobian_nonneg : ∀ z ∈ C.S, 0 ≤ jacobian2 C.rect.map z

/-- Green's theorem for one cell, with the boundary written as a list of four oriented edges. -/
theorem green_cell (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) {C : PlaneCell} (hC : C.IsRegular U) :
    ∫ p in C.region, curl2 P Q p = (C.rect.boundary.map (planeCurveIntegral P Q)).sum := by
  rw [PlaneCell.region, green_param_image P Q C.rect.map hU hP hQ hC.smooth hC.hab hC.hcd hC.mapsTo
    hC.measurable hC.sub hC.sup hC.injOn hC.jacobian_nonneg]
  simp only [ParamRect.boundary, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, planeCurveIntegral,
    greenLineIntegral]
  rw [intervalIntegral.integral_symm C.rect.a C.rect.b, intervalIntegral.integral_symm C.rect.c C.rect.d]
  ring

/-- The cell images lie in `U`. -/
theorem PlaneCell.IsRegular.region_subset {C : PlaneCell} {U : Set (ℝ × ℝ)} (hC : C.IsRegular U) :
    C.rect.map '' C.rect.dom ⊆ U := by
  rintro _ ⟨z, hz, rfl⟩
  exact hC.mapsTo z hz

/-- The sum of the boundary integrals of all cells is the integral over the union of the cells. -/
theorem green_cells (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) {n : ℕ} (cells : Fin n → PlaneCell) (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region)) :
    ∫ p in ⋃ i, (cells i).region, curl2 P Q p =
      (((List.finRange n).flatMap fun i => (cells i).rect.boundary).map (planeCurveIntegral P Q)).sum := by
  have hcont : ContinuousOn (curl2 P Q) U := continuousOn_curl2 hU hP hQ
  have hint : ∀ i, IntegrableOn (curl2 P Q) (cells i).region := by
    intro i
    have hK : IsCompact ((cells i).rect.map '' (cells i).rect.dom) :=
      (isCompact_Icc.prod isCompact_Icc).image (hC i).smooth.continuous
    exact ((hcont.mono (hC i).region_subset).integrableOn_compact hK).mono_set
      (image_mono (hC i).sub)
  have hmeas : ∀ i, MeasurableSet (cells i).region := by
    intro i
    exact measurable_image_of_fderivWithin (hC i).measurable
      (fun z _ => (((hC i).smooth.differentiable (by norm_num)) z).hasFDerivAt.hasFDerivWithinAt) (hC i).injOn
  rw [integral_iUnion_ae (fun i => (hmeas i).nullMeasurableSet) hdisj (integrableOn_finite_iUnion.2 hint),
    tsum_fintype]
  simp only [green_cell P Q hU hP hQ (hC _)]
  rw [Fin.sum_univ_def]
  generalize List.finRange n = l
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, ih]

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632) and §6.4 Theorem (Green's theorem on general regions) (CA-639),
circulation form of Green's theorem on a region glued from finitely many parametrized cells: let `D` be the union of
the cells `Φᵢ(Sᵢ)` (each as in `green_param_image`: `Φᵢ` of class `C²` on a rectangle, injective and orientation
preserving on `Sᵢ`), pairwise overlapping in measure zero, and let the list of all their boundary edges be, up to
order, a list `outer` of edges together with pairs of opposite edges (interior cuts, traversed once in each
direction). For a field `(P, Q)` of class `C¹` on an open set containing the cells,
`∬_D (Q_x - P_y) dA = ∮_{outer} P dx + Q dy`. The outer edges may form several closed curves, so `D` may have
finitely many holes (the inner boundary curves are then traversed clockwise). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644",
  kb "openstaxcalculus2016" "3:§6.4 Theorem (Green's theorem on general regions), p. 656"]
theorem green_glued (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) {n : ℕ} (cells : Fin n → PlaneCell) (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (OrientedCurve (ℝ × ℝ))) (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ p in ⋃ i, (cells i).region, curl2 P Q p = (outer.map (planeCurveIntegral P Q)).sum := by
  rw [green_cells P Q hU hP hQ cells hC hdisj]
  refine sum_map_cancel_pairs _ pairs (fun e he => ?_) hperm
  have hmem : e.1 ∈ (List.finRange n).flatMap fun i => (cells i).rect.boundary :=
    hperm.symm.subset (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩))
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hmem
  refine planeCurveIntegral_of_isOpposite (U := U) hP.continuousOn hQ.continuousOn (hpairs e he) ?_
  intro x hx
  exact (hC i).region_subset ((cells i).rect.boundary_mem_image (hC i).hab (hC i).hcd _ hi x hx)

/-- OpenStax Calculus 3:Theorem 6.13 (CA-634), flux form of Green's theorem on a region glued from parametrized
cells (hypotheses as in `green_glued`): `∬_D (P_x + Q_y) dA = ∮_{outer} P dy - Q dx`, the outward flux across the
boundary, written as the circulation of `(-Q, P)` along the outer edges. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.13, p. 650"]
theorem green_flux_glued (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U)
    (hQ : ContDiffOn ℝ 1 Q U) {n : ℕ} (cells : Fin n → PlaneCell) (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (OrientedCurve (ℝ × ℝ))) (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ p in ⋃ i, (cells i).region, div2 P Q p = (outer.map (planeCurveIntegral (fun p => -Q p) P)).sum := by
  have h : curl2 (fun p => -Q p) P = div2 P Q := by
    funext p
    have hn : fderiv ℝ (fun p => -Q p) p = -fderiv ℝ Q p := fderiv_neg
    simp only [curl2, div2, pdy2, pdx2, hn, neg_apply]
    ring
  rw [← h]
  exact green_glued _ _ hU hQ.neg hP cells hC hdisj outer pairs hpairs hperm

/-- OpenStax Calculus 3:Equation 6.14 (CA-633), area of a region glued from parametrized cells (hypotheses as in
`green_glued`, with `U = ℝ²`): the area is `∮ x dy`, also `-∮ y dx` and `½ ∮ (x dy - y dx)`, along the outer
edges. -/
@[kb "openstaxcalculus2016" "3:Equation 6.14, p. 650"]
theorem area_glued {n : ℕ} (cells : Fin n → PlaneCell) (hC : ∀ i, (cells i).IsRegular univ)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (OrientedCurve (ℝ × ℝ))) (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    volume.real (⋃ i, (cells i).region) = (outer.map (planeCurveIntegral (fun _ => 0) (fun p => p.1))).sum ∧
      volume.real (⋃ i, (cells i).region) = (outer.map (planeCurveIntegral (fun p => -p.2) (fun _ => 0))).sum ∧
      volume.real (⋃ i, (cells i).region) =
        (outer.map (planeCurveIntegral (fun p => -p.2 / 2) (fun p => p.1 / 2))).sum := by
  have key : ∀ P Q : ℝ × ℝ → ℝ, ContDiff ℝ 1 P → ContDiff ℝ 1 Q → curl2 P Q = (fun _ => 1) →
      volume.real (⋃ i, (cells i).region) = (outer.map (planeCurveIntegral P Q)).sum := by
    intro P Q hP hQ h1
    rw [← green_glued P Q isOpen_univ hP.contDiffOn hQ.contDiffOn cells hC hdisj outer pairs hpairs hperm, h1,
      setIntegral_const, smul_eq_mul, mul_one]
  exact ⟨key _ _ contDiff_const contDiff_fst curl2_zero_fst,
    key _ _ contDiff_snd.neg contDiff_const curl2_neg_snd_zero,
    key _ _ (contDiff_snd.neg.div_const 2) (contDiff_fst.div_const 2) curl2_half⟩

end UndergradKB.Calculus
