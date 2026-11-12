import UndergradKB.Common.Attr
import UndergradKB.Calculus.Chains
import UndergradKB.Calculus.DivergenceInvSquare

/-! # Calculus: the divergence theorem on solids glued from parametrized boxes

OpenStax Calculus 3 §6.8 (Theorems 6.20, 6.21, Gauss' law). A solid `E` is glued from finitely many cells
`Φᵢ(Sᵢ)` (each `Φᵢ` of class `C²` on a box, injective and orientation preserving on `Sᵢ`, as in
`divergence_param_image`), overlapping in measure zero. Each cell's boundary is a list of six patches
(`SolidCell.faces`): for each coordinate `i`, the face `zᵢ = hiᵢ` parametrized by the two other coordinates in
cyclic order (outward normal for an orientation preserving `Φ`), and the face `zᵢ = loᵢ` with the opposite
orientation (`ParamRect.reverse`).

* `face_integral_eq_patchFlux`: the face terms of `divergence_param_box` are patch fluxes (`patchFlux`);
* `divergence_cell`: `∭_{Φ(S)} div F dV` is the sum of the fluxes through the six faces;
* `divergence_glued`: for a glued solid whose faces are, up to order, a list `outer` and pairs of opposite patches
  (interior walls, crossed once in each direction: `ParamRect.IsOpposite`), `∭_E div F dV` is the outward flux
  through the outer patches;
* `flux_invSquare_glued_shell`, `gauss_law_glued_shell`: the flux of `r/‖r‖³` through a closed surface `S` that,
  together with a sphere about the origin (oriented inward), bounds a glued solid avoiding the origin is `4π` (the
  extended divergence theorem for a solid with a hole, `div (r/‖r‖³) = 0`), and Gauss' law `q/ε₀`;
* `flux_invSquare_glued_zero`, `gauss_law_glued_no_charge`: the flux is `0` through the boundary of a glued solid
  avoiding the origin.

Still missing for the book's statement for every closed piecewise smooth surface: the Jordan-Brouwer separation
theorem and the decomposition of the solid it encloses into parametrized cells (not in Mathlib). -/

open MeasureTheory Set Real Matrix

namespace UndergradKB.Calculus

/-! ### Faces of a parametrized box -/

/-- The point of `ℝ³` with coordinate `i` equal to `c` and coordinates `i + 1`, `i + 2` (cyclically) equal to
`z.1`, `z.2`. -/
def facePoint (i : Fin 3) (c : ℝ) (z : ℝ × ℝ) : Fin 3 → ℝ :=
  fun m => if m = i then c else if m = cyc1 i then z.1 else z.2

/-- The face `zᵢ = c` of the image of the box `[lo, hi]` under `Φ`, parametrized by the coordinates `i + 1`, `i + 2`
(cyclically) over `[loᵢ₊₁, hiᵢ₊₁] × [loᵢ₊₂, hiᵢ₊₂]`. -/
def boxFace (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (lo hi : Fin 3 → ℝ) (i : Fin 3) (c : ℝ) : ParamRect (Fin 3 → ℝ) :=
  ⟨fun z => Φ (facePoint i c z), lo (cyc1 i), hi (cyc1 i), lo (cyc2 i), hi (cyc2 i)⟩

/-- Along the first face coordinate, `facePoint` has derivative `Pi.single (cyc1 i) 1`. -/
theorem hasDerivAt_facePoint_fst (i : Fin 3) (c : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun u => facePoint i c (u, z.2)) (Pi.single (cyc1 i) 1) z.1 := by
  rw [hasDerivAt_pi]
  intro m
  fin_cases i <;> fin_cases m <;> simp [facePoint, hasDerivAt_const] <;> exact hasDerivAt_id' _

/-- Along the second face coordinate, `facePoint` has derivative `Pi.single (cyc2 i) 1`. -/
theorem hasDerivAt_facePoint_snd (i : Fin 3) (c : ℝ) (z : ℝ × ℝ) :
    HasDerivAt (fun v => facePoint i c (z.1, v)) (Pi.single (cyc2 i) 1) z.2 := by
  rw [hasDerivAt_pi]
  intro m
  fin_cases i <;> fin_cases m <;> simp [facePoint, hasDerivAt_const] <;> exact hasDerivAt_id' _

/-- The normal of a box face is the cross product of the two edge derivatives of `Φ`. -/
theorem surfNormal_boxFace {Φ : (Fin 3 → ℝ) → Fin 3 → ℝ} (hΦ : Differentiable ℝ Φ) (i : Fin 3) (c : ℝ)
    (z : ℝ × ℝ) (lo hi : Fin 3 → ℝ) :
    surfNormal (boxFace Φ lo hi i c).map z = crossProduct
      (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc1 i) 1))
      (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc2 i) 1)) := by
  have h1 := ((hΦ (facePoint i c (z.1, z.2))).hasFDerivAt.comp_hasDerivAt z.1
    (hasDerivAt_facePoint_fst i c z)).deriv
  have h2 := ((hΦ (facePoint i c (z.1, z.2))).hasFDerivAt.comp_hasDerivAt z.2
    (hasDerivAt_facePoint_snd i c z)).deriv
  simp only [surfNormal, partialU, partialV, boxFace]
  rw [show deriv (fun u => Φ (facePoint i c (u, z.2))) z.1 = _ from h1,
    show deriv (fun v => Φ (facePoint i c (z.1, v))) z.2 = _ from h2]

/-- Integration over a box of `Fin 2 → ℝ` through a measure preserving equivalence with `ℝ × ℝ`. -/
theorem setIntegral_icc_fin_two (e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) (he : MeasurePreserving e) (G : ℝ × ℝ → ℝ)
    (S : Set (Fin 2 → ℝ)) (R : Set (ℝ × ℝ)) (hS : S = e ⁻¹' R) :
    ∫ y in S, G (e y) = ∫ z in R, G z := by
  rw [hS]
  exact he.setIntegral_preimage_emb e.measurableEmbedding G R

/-- The face terms of `divergence_param_box` are patch fluxes. -/
theorem face_integral_eq_patchFlux (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {Φ : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hΦ : Differentiable ℝ Φ) (lo hi : Fin 3 → ℝ) (i : Fin 3) (c : ℝ) :
    (∫ y in Icc (lo ∘ i.succAbove) (hi ∘ i.succAbove),
      F (Φ (i.insertNth c y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth c y) (Pi.single (cyc1 i) 1))
        (fderiv ℝ Φ (i.insertNth c y) (Pi.single (cyc2 i) 1))) = patchFlux F (boxFace Φ lo hi i c) := by
  have hG : patchFlux F (boxFace Φ lo hi i c) = ∫ z in Icc (lo (cyc1 i)) (hi (cyc1 i)) ×ˢ
      Icc (lo (cyc2 i)) (hi (cyc2 i)), F (Φ (facePoint i c z)) ⬝ᵥ crossProduct
        (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc1 i) 1))
        (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc2 i) 1)) := by
    unfold patchFlux surfaceFlux
    refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun z _ => ?_)
    show F (Φ (facePoint i c z)) ⬝ᵥ surfNormal (boxFace Φ lo hi i c).map z = _
    rw [surfNormal_boxFace hΦ]
  rw [hG]
  have key : ∀ (e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ), MeasurePreserving e →
      (∀ y, i.insertNth c y = facePoint i c (e y)) →
      Icc (lo ∘ i.succAbove) (hi ∘ i.succAbove) =
        e ⁻¹' (Icc (lo (cyc1 i)) (hi (cyc1 i)) ×ˢ Icc (lo (cyc2 i)) (hi (cyc2 i))) →
      (∫ y in Icc (lo ∘ i.succAbove) (hi ∘ i.succAbove),
        F (Φ (i.insertNth c y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth c y) (Pi.single (cyc1 i) 1))
          (fderiv ℝ Φ (i.insertNth c y) (Pi.single (cyc2 i) 1))) =
      ∫ z in Icc (lo (cyc1 i)) (hi (cyc1 i)) ×ˢ Icc (lo (cyc2 i)) (hi (cyc2 i)),
        F (Φ (facePoint i c z)) ⬝ᵥ crossProduct
          (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc1 i) 1))
          (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc2 i) 1)) := by
    intro e he hins hS
    rw [← setIntegral_icc_fin_two e he (fun z => F (Φ (facePoint i c z)) ⬝ᵥ crossProduct
          (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc1 i) 1))
          (fderiv ℝ Φ (facePoint i c z) (Pi.single (cyc2 i) 1))) _ _ hS]
    simp only [hins]
  have hsw : MeasurePreserving
      ((MeasurableEquiv.finTwoArrow (α := ℝ)).trans MeasurableEquiv.prodComm : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).comp
      (volume_preserving_finTwoArrow ℝ)
  have hid : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)) := volume_preserving_finTwoArrow ℝ
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl
  · refine key _ hid ?_ ?_
    · intro y
      ext m
      fin_cases m <;> simp [facePoint]; rfl
    · ext y
      simp [Pi.le_def, Fin.forall_fin_two]
  · refine key _ hsw ?_ ?_
    · intro y
      ext m
      fin_cases m <;> simp [facePoint] <;> rfl
    · ext y
      simp [Pi.le_def, Fin.forall_fin_two, Fin.succAbove, MeasurableEquiv.prodComm, Prod.le_def]
      tauto
  · refine key _ hid ?_ ?_
    · intro y
      ext m
      fin_cases m <;> simp [facePoint] <;> rfl
    · ext y
      simp [Pi.le_def, Fin.forall_fin_two, Fin.succAbove]

/-! ### Cells -/

/-- A cell of a solid: a map `Φ` of the box `[lo, hi]` of `ℝ³` restricted to a part `S` of the box. -/
structure SolidCell where
  /-- the parametrization -/
  map : (Fin 3 → ℝ) → Fin 3 → ℝ
  /-- lower corner of the box -/
  lo : Fin 3 → ℝ
  /-- upper corner of the box -/
  hi : Fin 3 → ℝ
  /-- the part of the box covered -/
  S : Set (Fin 3 → ℝ)

/-- The solid `Φ(S)` covered by a cell. -/
def SolidCell.region (C : SolidCell) : Set (Fin 3 → ℝ) := C.map '' C.S

/-- The six faces of a cell, oriented outward (for an orientation preserving parametrization). -/
def SolidCell.faces (C : SolidCell) : List (ParamRect (Fin 3 → ℝ)) :=
  [boxFace C.map C.lo C.hi 0 (C.hi 0), (boxFace C.map C.lo C.hi 0 (C.lo 0)).reverse,
    boxFace C.map C.lo C.hi 1 (C.hi 1), (boxFace C.map C.lo C.hi 1 (C.lo 1)).reverse,
    boxFace C.map C.lo C.hi 2 (C.hi 2), (boxFace C.map C.lo C.hi 2 (C.lo 2)).reverse]

/-- The hypotheses of `divergence_param_image` for a cell inside the open set `U`. -/
structure SolidCell.IsRegular (C : SolidCell) (U : Set (Fin 3 → ℝ)) : Prop where
  smooth : ContDiff ℝ 2 C.map
  le : C.lo ≤ C.hi
  mapsTo : ∀ z ∈ Icc C.lo C.hi, C.map z ∈ U
  measurable : MeasurableSet C.S
  sub : C.S ⊆ Icc C.lo C.hi
  sup : (Set.pi univ fun i => Ioo (C.lo i) (C.hi i)) ⊆ C.S
  injOn : InjOn C.map C.S
  jacobian_nonneg : ∀ z ∈ C.S, 0 ≤ jacobian3 C.map z

/-- The divergence theorem for one cell: `∭_{Φ(S)} div F dV` is the sum of the fluxes through the six faces. -/
theorem divergence_cell (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {C : SolidCell} (hC : C.IsRegular U) :
    ∫ x in C.region, divVec F x = (C.faces.map (patchFlux F)).sum := by
  have hd : Differentiable ℝ C.map := hC.smooth.differentiable (by norm_num)
  rw [SolidCell.region, divergence_param_image F hU hF C.map hC.smooth hC.le hC.mapsTo hC.measurable hC.sub hC.sup
    hC.injOn hC.jacobian_nonneg]
  simp only [face_integral_eq_patchFlux F hd, Fin.sum_univ_three, SolidCell.faces, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, patchFlux_reverse]
  ring

/-! ### Opposite patches -/

/-- Two patches with the same rectangle whose maps agree on it have the same flux. -/
theorem patchFlux_congr (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {p q : ParamRect (Fin 3 → ℝ)} (ha : q.a = p.a)
    (hb : q.b = p.b) (hc : q.c = p.c) (hd : q.d = p.d) (h : ∀ z ∈ p.dom, q.map z = p.map z) :
    patchFlux F q = patchFlux F p := by
  have hdom : q.dom = p.dom := by simp only [ParamRect.dom, ha, hb, hc, hd]
  rw [patchFlux, patchFlux, hdom, surfaceFlux, surfaceFlux, ParamRect.dom,
    setIntegral_congr_set (ae_eq_Icc_prod (S := Ioo p.a p.b ×ˢ Ioo p.c p.d)
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) le_rfl).symm,
    setIntegral_congr_set (ae_eq_Icc_prod (S := Ioo p.a p.b ×ˢ Ioo p.c p.d)
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) le_rfl).symm]
  refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) (fun z hz => ?_)
  have hopen : IsOpen (Ioo p.a p.b ×ˢ Ioo p.c p.d) := isOpen_Ioo.prod isOpen_Ioo
  have hev : q.map =ᶠ[nhds z] p.map := Filter.eventually_of_mem (hopen.mem_nhds hz)
    (fun w hw => h w (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hw))
  have hU : partialU q.map z = partialU p.map z := by
    have : (fun u => q.map (u, z.2)) =ᶠ[nhds z.1] (fun u => p.map (u, z.2)) :=
      (continuous_id.prodMk continuous_const).continuousAt.eventually hev (f := fun u : ℝ => (u, z.2))
    exact this.deriv_eq
  have hV : partialV q.map z = partialV p.map z := by
    have : (fun v => q.map (z.1, v)) =ᶠ[nhds z.2] (fun v => p.map (z.1, v)) :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually hev (f := fun v : ℝ => (z.1, v))
    exact this.deriv_eq
  simp only [surfNormal, hU, hV, h z (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hz)]

/-- `q` is the patch `p` with the opposite orientation: the same rectangle, and `q` agrees on it with the reverse
`(u, v) ↦ p(a + b - u, v)` of `p`. Two cells glued along a common face carry it with opposite orientations in
this sense. -/
def ParamRect.IsOpposite (p q : ParamRect (Fin 3 → ℝ)) : Prop :=
  q.a = p.a ∧ q.b = p.b ∧ q.c = p.c ∧ q.d = p.d ∧ ∀ z ∈ p.dom, q.map z = p.reverse.map z

/-- Opposite patches have opposite fluxes. -/
theorem patchFlux_of_isOpposite (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {p q : ParamRect (Fin 3 → ℝ)}
    (h : p.IsOpposite q) : patchFlux F q = -patchFlux F p := by
  obtain ⟨ha, hb, hc, hd, hm⟩ := h
  rw [← patchFlux_reverse]
  exact patchFlux_congr F ha hb hc hd hm

/-! ### Glued solids -/

/-- `div F` is continuous on the open set where `F` is `C¹`. -/
theorem continuousOn_divVec {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) : ContinuousOn (divVec F) U := by
  have h := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hm : ∀ m : Fin 3, ContinuousOn (fun x => fderiv ℝ F x (Pi.single m 1) m) U := fun m =>
    (continuous_apply m).comp_continuousOn (h.clm_apply continuousOn_const)
  unfold divVec
  simp only [Fin.sum_univ_three]
  exact ((hm 0).add (hm 1)).add (hm 2)

/-- OpenStax Calculus 3:Theorem 6.20 (CA-661), divergence theorem on a solid glued from parametrized cells: let `E`
be the union of the cells `Φᵢ(Sᵢ)` (each as in `divergence_param_image`, inside the open set `U`), pairwise
overlapping in measure zero, and let the list of all their faces (`SolidCell.faces`, oriented outward) be, up to
order, a list `outer` of patches (the boundary surface `S` of `E`) together with pairs of opposite patches
(interior walls, crossed once in each direction). For `F` of class `C¹` on `U`, `∭_E div F dV` is the outward flux
of `F` through `S`, the sum of the fluxes through the outer patches. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.20, p. 730"]
theorem divergence_glued (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {n : ℕ} (cells : Fin n → SolidCell) (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (ParamRect (Fin 3 → ℝ))) (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ x in ⋃ i, (cells i).region, divVec F x = (outer.map (patchFlux F)).sum := by
  have hcont : ContinuousOn (divVec F) U := continuousOn_divVec hU hF
  have hint : ∀ i, IntegrableOn (divVec F) (cells i).region := by
    intro i
    have hK : IsCompact ((cells i).map '' Icc (cells i).lo (cells i).hi) :=
      isCompact_Icc.image (hC i).smooth.continuous
    have hsub : (cells i).map '' Icc (cells i).lo (cells i).hi ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hC i).mapsTo z hz
    exact ((hcont.mono hsub).integrableOn_compact hK).mono_set (image_mono (hC i).sub)
  have hmeas : ∀ i, MeasurableSet (cells i).region := by
    intro i
    exact measurable_image_of_fderivWithin (hC i).measurable
      (fun z _ => (((hC i).smooth.differentiable (by norm_num)) z).hasFDerivAt.hasFDerivWithinAt) (hC i).injOn
  rw [integral_iUnion_ae (fun i => (hmeas i).nullMeasurableSet) hdisj (integrableOn_finite_iUnion.2 hint),
    tsum_fintype]
  simp only [divergence_cell F hU hF (hC _)]
  have hsum : ∑ i, ((cells i).faces.map (patchFlux F)).sum =
      (((List.finRange n).flatMap fun i => (cells i).faces).map (patchFlux F)).sum := by
    rw [Fin.sum_univ_def]
    generalize List.finRange n = l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, ih]
  rw [hsum]
  exact sum_map_cancel_pairs _ pairs (fun e he => patchFlux_of_isOpposite F (hpairs e he)) hperm

/-! ### The inverse-square field and Gauss' law -/

/-- The sphere of radius `R` about the origin as a patch (spherical coordinates `(φ, θ) ∈ [0,π]×[0,2π]`, outward
normal). -/
noncomputable def spherePatch (R : ℝ) : ParamRect (Fin 3 → ℝ) := ⟨sphereParam R, 0, π, 0, 2 * π⟩

theorem patchFlux_smul (c : ℝ) (F : (Fin 3 → ℝ) → Fin 3 → ℝ) (p : ParamRect (Fin 3 → ℝ)) :
    patchFlux (fun x => c • F x) p = c * patchFlux F p := by
  unfold patchFlux surfaceFlux
  simp only [smul_dotProduct, smul_eq_mul]
  exact integral_const_mul _ _

/-- The flux of `r/‖r‖³` out of a glued solid avoiding the origin is `0`. -/
theorem divergence_glued_invSquare {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (ParamRect (Fin 3 → ℝ))) (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    (outer.map (patchFlux invSquareField)).sum = 0 := by
  rw [← divergence_glued invSquareField isOpen_ne contDiffOn_invSquareField cells hC hdisj outer pairs hpairs
    hperm]
  refine setIntegral_eq_zero_of_forall_eq_zero (fun x hx => divVec_invSquareField ?_)
  obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 hx
  exact (hC i).mapsTo z ((hC i).sub hz)

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664), surfaces not enclosing the origin: the flux of `r/‖r‖³` through the
boundary `S` (a list of outward patches) of a solid glued from parametrized cells avoiding the origin is `0`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_glued_zero {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (S : List (ParamRect (Fin 3 → ℝ))) (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      (S ++ pairs.flatMap fun e => [e.1, e.2])) :
    (S.map (patchFlux invSquareField)).sum = 0 :=
  divergence_glued_invSquare cells hC hdisj S pairs hpairs hperm

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664), surfaces enclosing the origin: let the closed surface `S` (a list
of patches) and a sphere of radius `R > 0` about the origin, oriented inward, together bound a solid glued from
parametrized cells avoiding the origin (the faces of the cells are, up to order, `S`, the reversed sphere and pairs
of opposite patches). Then the flux of `r/‖r‖³` through `S` is `4π`. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_glued_shell {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (S : List (ParamRect (Fin 3 → ℝ))) {R : ℝ} (hR : 0 < R)
    (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      ((S ++ [(spherePatch R).reverse]) ++ pairs.flatMap fun e => [e.1, e.2])) :
    (S.map (patchFlux invSquareField)).sum = 4 * π := by
  have key := divergence_glued_invSquare cells hC hdisj _ pairs hpairs hperm
  rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, patchFlux_reverse] at key
  have hs : patchFlux invSquareField (spherePatch R) = 4 * π := flux_invSquare_sphere hR
  linarith

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665), for glued solids: the flux of the field
`q/(4πε₀) · r/‖r‖³` of a point charge `q` at the origin through a closed surface `S` that, together with a sphere
about the charge (oriented inward), bounds a solid glued from parametrized cells avoiding the charge is `q/ε₀`. -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_glued_shell {q ε₀ : ℝ} (hε : 0 < ε₀) {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (S : List (ParamRect (Fin 3 → ℝ))) {R : ℝ} (hR : 0 < R)
    (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      ((S ++ [(spherePatch R).reverse]) ++ pairs.flatMap fun e => [e.1, e.2])) :
    (S.map (patchFlux fun x => (q / (4 * π * ε₀)) • invSquareField x)).sum = q / ε₀ := by
  have hs : patchFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) =
      fun p => (q / (4 * π * ε₀)) * patchFlux invSquareField p := funext fun p => patchFlux_smul _ _ p
  rw [hs, List.sum_map_mul_left, flux_invSquare_glued_shell cells hC hdisj S hR pairs hpairs hperm]
  field_simp

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665), no charge enclosed: the flux of the field of a point charge at the
origin through the boundary of a solid glued from parametrized cells avoiding the origin is `0`. -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_glued_no_charge (q ε₀ : ℝ) {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (S : List (ParamRect (Fin 3 → ℝ))) (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      (S ++ pairs.flatMap fun e => [e.1, e.2])) :
    (S.map (patchFlux fun x => (q / (4 * π * ε₀)) • invSquareField x)).sum = 0 := by
  have hs : patchFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) =
      fun p => (q / (4 * π * ε₀)) * patchFlux invSquareField p := funext fun p => patchFlux_smul _ _ p
  rw [hs, List.sum_map_mul_left, flux_invSquare_glued_zero cells hC hdisj S pairs hpairs hperm, mul_zero]

end UndergradKB.Calculus
