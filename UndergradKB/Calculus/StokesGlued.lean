import UndergradKB.Common.Attr
import UndergradKB.Calculus.Chains
import UndergradKB.Calculus.StokesParam

/-! # Calculus: Stokes' theorem on surfaces glued from parametrized patches

OpenStax Calculus 3 §6.7 (Theorem 6.19, Example 6.74). A piecewise smooth oriented surface is glued from finitely
many parametrized patches `rᵢ : [aᵢ,bᵢ]×[cᵢ,dᵢ] → ℝ³`, each oriented by `∂ᵤrᵢ × ∂ᵥrᵢ`; the orientations are
compatible when every interior edge is traversed in opposite directions by the two patches it bounds
(`OrientedCurve.IsOpposite`). The flux of `curl F` across the glued surface is the sum of the patch fluxes.

* `stokes_patch`: Stokes' theorem for one patch, the boundary written as four oriented edges;
* `stokes_glued`: for a surface glued from patches, the flux of `curl F` equals the circulation of `F` along the
  remaining (outer) edges: the interior edges cancel;
* `curl_flux_glued_independent`: two glued surfaces (with any numbers of patches and any parameter rectangles)
  with the same outer boundary edges have the same flux of `curl F`.

This removes the restriction of `stokes_param` (wave 3) to surfaces given by a single parametrization. -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-- The hypotheses of `stokes_param` for a patch inside the open set `U`: `r` of class `C²` maps the rectangle
`[a,b]×[c,d]` (with `a ≤ b`, `c ≤ d`) into `U`. -/
structure ParamRect.IsRegular (p : ParamRect (Fin 3 → ℝ)) (U : Set (Fin 3 → ℝ)) : Prop where
  smooth : ContDiff ℝ 2 p.map
  hab : p.a ≤ p.b
  hcd : p.c ≤ p.d
  mapsTo : ∀ z ∈ p.dom, p.map z ∈ U

/-- Stokes' theorem for one patch, with the boundary written as a list of four oriented edges. -/
theorem stokes_patch (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {p : ParamRect (Fin 3 → ℝ)} (hp : p.IsRegular U) :
    patchFlux (curlVec F) p = (p.boundary.map (spaceCurveIntegral F)).sum := by
  rw [patchFlux, ParamRect.dom, stokes_param F hU hF p.map hp.smooth hp.hab hp.hcd hp.mapsTo]
  simp only [ParamRect.boundary, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, spaceCurveIntegral,
    partialU, partialV]
  rw [intervalIntegral.integral_symm p.a p.b, intervalIntegral.integral_symm p.c p.d]
  ring

/-- OpenStax Calculus 3:Theorem 6.19 (CA-658), Stokes' theorem on a surface glued from parametrized patches: let
`S` be glued from the patches `rᵢ` (each `C²` on a rectangle, mapping it into the open set `U`, oriented by
`∂ᵤrᵢ × ∂ᵥrᵢ`) such that the list of all their boundary edges is, up to order, a list `outer` (the boundary curve
`C` of `S`, positively oriented) together with pairs of opposite edges (each interior edge is traversed once in each
direction: the orientations of the patches are compatible). For `F` of class `C¹` on `U`, the flux of `curl F`
across `S` (the sum of the patch fluxes) equals the circulation `∮_C F · dr` along the outer edges. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.19, p. 714"]
theorem stokes_glued (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {n : ℕ} (patches : Fin n → ParamRect (Fin 3 → ℝ))
    (hp : ∀ i, (patches i).IsRegular U) (outer : List (OrientedCurve (Fin 3 → ℝ)))
    (pairs : List (OrientedCurve (Fin 3 → ℝ) × OrientedCurve (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (patches i).boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∑ i, patchFlux (curlVec F) (patches i) = (outer.map (spaceCurveIntegral F)).sum := by
  have hsum : ∑ i, patchFlux (curlVec F) (patches i) =
      (((List.finRange n).flatMap fun i => (patches i).boundary).map (spaceCurveIntegral F)).sum := by
    simp only [stokes_patch F hU hF (hp _)]
    rw [Fin.sum_univ_def]
    generalize List.finRange n = l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, ih]
  rw [hsum]
  refine sum_map_cancel_pairs _ pairs (fun e he => ?_) hperm
  have hmem : e.1 ∈ (List.finRange n).flatMap fun i => (patches i).boundary :=
    hperm.symm.subset (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, List.mem_cons_self⟩))
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hmem
  refine spaceCurveIntegral_of_isOpposite (U := U) hF.continuousOn (hpairs e he) ?_
  intro x hx
  obtain ⟨z, hz, hzx⟩ := (patches i).boundary_mem_image (hp i).hab (hp i).hcd _ hi x hx
  rw [← hzx]
  exact (hp i).mapsTo z hz

/-- OpenStax Calculus 3:Example 6.74 (CA-659), surface independence for glued surfaces: two surfaces glued from
parametrized patches (any numbers of patches, any parameter rectangles; hypotheses as in `stokes_glued`) whose
boundary edges reduce, after cancelling the interior edges, to the same outer boundary curve have the same flux of
`curl F`, for every `C¹` field `F` on an open set containing both. -/
@[kb "openstaxcalculus2016" "3:Example 6.74, p. 718"]
theorem curl_flux_glued_independent (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (outer : List (OrientedCurve (Fin 3 → ℝ)))
    {n₁ : ℕ} (patches₁ : Fin n₁ → ParamRect (Fin 3 → ℝ)) (hp₁ : ∀ i, (patches₁ i).IsRegular U)
    (pairs₁ : List (OrientedCurve (Fin 3 → ℝ) × OrientedCurve (Fin 3 → ℝ)))
    (hpairs₁ : ∀ e ∈ pairs₁, e.1.IsOpposite e.2)
    (hperm₁ : ((List.finRange n₁).flatMap fun i => (patches₁ i).boundary).Perm
      (outer ++ pairs₁.flatMap fun e => [e.1, e.2]))
    {n₂ : ℕ} (patches₂ : Fin n₂ → ParamRect (Fin 3 → ℝ)) (hp₂ : ∀ i, (patches₂ i).IsRegular U)
    (pairs₂ : List (OrientedCurve (Fin 3 → ℝ) × OrientedCurve (Fin 3 → ℝ)))
    (hpairs₂ : ∀ e ∈ pairs₂, e.1.IsOpposite e.2)
    (hperm₂ : ((List.finRange n₂).flatMap fun i => (patches₂ i).boundary).Perm
      (outer ++ pairs₂.flatMap fun e => [e.1, e.2])) :
    ∑ i, patchFlux (curlVec F) (patches₁ i) = ∑ i, patchFlux (curlVec F) (patches₂ i) := by
  rw [stokes_glued F hU hF patches₁ hp₁ outer pairs₁ hpairs₁ hperm₁,
    stokes_glued F hU hF patches₂ hp₂ outer pairs₂ hpairs₂ hperm₂]

end UndergradKB.Calculus
