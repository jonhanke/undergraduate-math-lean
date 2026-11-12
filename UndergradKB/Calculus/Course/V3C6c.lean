import UndergradKB.Calculus.GreenGlued
import UndergradKB.Calculus.WindingNumber
import UndergradKB.Calculus.StokesGlued
import UndergradKB.Calculus.DivergenceGlued
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 3, Chapter 6 (vector calculus), part 3 (wave 5): Green's, Stokes' and
the divergence theorem on regions, surfaces and solids glued from parametrized pieces. -/

namespace UndergradKB.Calculus.Course.V3C6

open UndergradKB.Calculus MeasureTheory Set Real Matrix

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632). Green's theorem, circulation form, for a region glued from finitely
many parametrized cells: the double integral of `Q_x - P_y` equals the line integral along the outer edges (the
interior edges, traversed once in each direction, cancel). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_theorem_circulation_glued_region (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (OrientedCurve (ℝ × ℝ))) (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ p in ⋃ i, (cells i).region, curl2 P Q p = (outer.map (planeCurveIntegral P Q)).sum :=
  green_glued P Q hU hP hQ cells hC hdisj outer pairs hpairs hperm

/-- OpenStax Calculus 3:§6.4 Theorem (Green's theorem on general regions) (CA-639). Regions with finitely many
holes, glued from parametrized cells: the outer edges form the outer boundary (counterclockwise) and the boundaries
of the holes (clockwise). -/
@[kb "openstaxcalculus2016" "3:§6.4 Theorem (Green's theorem on general regions), p. 656"]
theorem green_theorem_glued_region_with_holes (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outerCurve : List (OrientedCurve (ℝ × ℝ))) (holes : List (List (OrientedCurve (ℝ × ℝ))))
    (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      ((outerCurve ++ holes.flatten) ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ p in ⋃ i, (cells i).region, curl2 P Q p =
      (outerCurve.map (planeCurveIntegral P Q)).sum + (holes.map fun h => (h.map (planeCurveIntegral P Q)).sum).sum := by
  rw [green_glued P Q hU hP hQ cells hC hdisj _ pairs hpairs hperm, List.map_append, List.sum_append,
    List.map_flatten, List.sum_flatten, List.map_map]
  rfl

/-- OpenStax Calculus 3:Equation 6.14 (CA-633). Area of a region glued from parametrized cells as `∮ x dy`,
`-∮ y dx` and `½∮ (x dy - y dx)` along the outer edges. -/
@[kb "openstaxcalculus2016" "3:Equation 6.14, p. 650"]
theorem area_glued_region_line_integrals {n : ℕ} (cells : Fin n → PlaneCell) (hC : ∀ i, (cells i).IsRegular univ)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (OrientedCurve (ℝ × ℝ))) (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    volume.real (⋃ i, (cells i).region) = (outer.map (planeCurveIntegral (fun _ => 0) (fun p => p.1))).sum ∧
      volume.real (⋃ i, (cells i).region) = (outer.map (planeCurveIntegral (fun p => -p.2) (fun _ => 0))).sum ∧
      volume.real (⋃ i, (cells i).region) =
        (outer.map (planeCurveIntegral (fun p => -p.2 / 2) (fun p => p.1 / 2))).sum :=
  area_glued cells hC hdisj outer pairs hpairs hperm

/-- OpenStax Calculus 3:Theorem 6.13 (CA-634). Green's theorem, flux form, for a region glued from parametrized
cells: `∬_D (P_x + Q_y) dA = ∮ P dy - Q dx` along the outer edges. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.13, p. 650"]
theorem green_theorem_flux_glued_region (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (OrientedCurve (ℝ × ℝ))) (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ p in ⋃ i, (cells i).region, div2 P Q p = (outer.map (planeCurveIntegral (fun p => -Q p) P)).sum :=
  green_flux_glued P Q hU hP hQ cells hC hdisj outer pairs hpairs hperm

/-- OpenStax Calculus 3:Example 6.47 (CA-640). The circulation of `(-y, x)/(x²+y²)` along a closed `C¹` curve
avoiding the origin is `2π` times an integer (the winding number). -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_winding_number (γ : ℝ → ℝ × ℝ) (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hcl : γ a = γ b) (h0 : ∀ t ∈ Icc a b, γ t ≠ 0) :
    ∃ k : ℤ, greenLineIntegral swirlP swirlQ (fun t => (γ t).1) (fun t => (γ t).2) a b = 2 * π * k :=
  swirl_circulation_mem_zmultiples γ hγ hab hcl h0

/-- OpenStax Calculus 3:Example 6.47 (CA-640). The circulation of `(-y, x)/(x²+y²)` is `2π` along curves that,
with a clockwise circle about the origin, bound a region glued from parametrized cells avoiding the origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_glued_enclosing {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular {p | p ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (C : List (OrientedCurve (ℝ × ℝ))) {r : ℝ} (hr : 0 < r)
    (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      ((C ++ [(⟨fun t => (r * Real.cos t, r * Real.sin t), 0, 2 * π⟩ : OrientedCurve (ℝ × ℝ)).reverse]) ++
        pairs.flatMap fun e => [e.1, e.2])) :
    (C.map (planeCurveIntegral swirlP swirlQ)).sum = 2 * π :=
  swirl_circulation_glued_annulus cells hC hdisj C hr pairs hpairs hperm

/-- OpenStax Calculus 3:Example 6.47 (CA-640). The circulation of `(-y, x)/(x²+y²)` is `0` along the boundary of a
region glued from parametrized cells avoiding the origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_glued_not_enclosing {n : ℕ} (cells : Fin n → PlaneCell)
    (hC : ∀ i, (cells i).IsRegular {p | p ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (C : List (OrientedCurve (ℝ × ℝ)))
    (pairs : List (OrientedCurve (ℝ × ℝ) × OrientedCurve (ℝ × ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).rect.boundary).Perm
      (C ++ pairs.flatMap fun e => [e.1, e.2])) :
    (C.map (planeCurveIntegral swirlP swirlQ)).sum = 0 :=
  swirl_circulation_glued_zero cells hC hdisj C pairs hpairs hperm

/-- OpenStax Calculus 3:Theorem 6.19 (CA-658). Stokes' theorem on a surface glued from parametrized patches with
compatible orientations: the flux of `curl F` equals the circulation of `F` along the outer edges. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.19, p. 714"]
theorem stokes_theorem_glued_surface (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {n : ℕ} (patches : Fin n → ParamRect (Fin 3 → ℝ))
    (hp : ∀ i, (patches i).IsRegular U) (outer : List (OrientedCurve (Fin 3 → ℝ)))
    (pairs : List (OrientedCurve (Fin 3 → ℝ) × OrientedCurve (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (patches i).boundary).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∑ i, patchFlux (curlVec F) (patches i) = (outer.map (spaceCurveIntegral F)).sum :=
  stokes_glued F hU hF patches hp outer pairs hpairs hperm

/-- OpenStax Calculus 3:Example 6.74 (CA-659). Two glued surfaces with the same outer boundary edges have the same
flux of `curl F`. -/
@[kb "openstaxcalculus2016" "3:Example 6.74, p. 718"]
theorem curl_flux_glued_surfaces_equal (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
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
    ∑ i, patchFlux (curlVec F) (patches₁ i) = ∑ i, patchFlux (curlVec F) (patches₂ i) :=
  curl_flux_glued_independent F hU hF outer patches₁ hp₁ pairs₁ hpairs₁ hperm₁ patches₂ hp₂ pairs₂ hpairs₂ hperm₂

/-- OpenStax Calculus 3:Theorem 6.20 (CA-661). The divergence theorem on a solid glued from parametrized cells:
`∭_E div F dV` is the outward flux through the outer patches. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.20, p. 730"]
theorem divergence_theorem_glued_solid (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) {n : ℕ} (cells : Fin n → SolidCell) (hC : ∀ i, (cells i).IsRegular U)
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (outer : List (ParamRect (Fin 3 → ℝ))) (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      (outer ++ pairs.flatMap fun e => [e.1, e.2])) :
    ∫ x in ⋃ i, (cells i).region, divVec F x = (outer.map (patchFlux F)).sum :=
  divergence_glued F hU hF cells hC hdisj outer pairs hpairs hperm

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664). Flux of `r/‖r‖³`: `4π` through a closed surface that, with an
inward sphere about the origin, bounds a glued solid avoiding the origin; `0` through the boundary of a glued solid
avoiding the origin. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_glued_enclosing_or_not {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (S : List (ParamRect (Fin 3 → ℝ))) (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ)))
    (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2) :
    (((List.finRange n).flatMap fun i => (cells i).faces).Perm (S ++ pairs.flatMap fun e => [e.1, e.2]) →
      (S.map (patchFlux invSquareField)).sum = 0) ∧
    (∀ R : ℝ, 0 < R → ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      ((S ++ [(spherePatch R).reverse]) ++ pairs.flatMap fun e => [e.1, e.2]) →
      (S.map (patchFlux invSquareField)).sum = 4 * π) :=
  ⟨fun h => flux_invSquare_glued_zero cells hC hdisj S pairs hpairs h,
    fun _ hR h => flux_invSquare_glued_shell cells hC hdisj S hR pairs hpairs h⟩

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665). The flux of the field of a point charge `q` through a closed
surface that, with an inward sphere about the charge, bounds a glued solid avoiding the charge is `q/ε₀`. -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_glued_solid {q ε₀ : ℝ} (hε : 0 < ε₀) {n : ℕ} (cells : Fin n → SolidCell)
    (hC : ∀ i, (cells i).IsRegular {x | x ≠ 0})
    (hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i => (cells i).region))
    (S : List (ParamRect (Fin 3 → ℝ))) {R : ℝ} (hR : 0 < R)
    (pairs : List (ParamRect (Fin 3 → ℝ) × ParamRect (Fin 3 → ℝ))) (hpairs : ∀ e ∈ pairs, e.1.IsOpposite e.2)
    (hperm : ((List.finRange n).flatMap fun i => (cells i).faces).Perm
      ((S ++ [(spherePatch R).reverse]) ++ pairs.flatMap fun e => [e.1, e.2])) :
    (S.map (patchFlux fun x => (q / (4 * π * ε₀)) • invSquareField x)).sum = q / ε₀ :=
  gauss_law_glued_shell hε cells hC hdisj S hR pairs hpairs hperm

end UndergradKB.Calculus.Course.V3C6
