import UndergradKB.Calculus.GreenRegions
import UndergradKB.Calculus.GreenHoles
import UndergradKB.Calculus.StokesParam
import UndergradKB.Calculus.DivergenceParam
import UndergradKB.Calculus.InverseSquareFlux
import UndergradKB.Calculus.DivergenceInvSquare
import UndergradKB.Common.Attr

/-! Course layer, OpenStax Calculus Volume 3, Chapter 6 (vector calculus), part 2. -/

namespace UndergradKB.Calculus.Course.V3C6

open UndergradKB.Calculus MeasureTheory Set Real Matrix

/-- OpenStax Calculus 3:Theorem 6.12 (CA-632). Green's theorem, circulation form, for regions that are
`C²` images of a rectangle (curvilinear quadrilaterals): the double integral of `Q_x - P_y` over the
region equals the line integral of `(P, Q)` around the image of the rectangle boundary. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.12, p. 644"]
theorem green_theorem_circulation_param_region (P Q : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℝ × ℝ) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (hΦ : ContDiff ℝ 2 Φ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hΦU : ∀ z ∈ Icc a b ×ˢ Icc c d, Φ z ∈ U)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d)
    (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S) (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    ∫ p in Φ '' S, curl2 P Q p =
      greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral P Q (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral P Q (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral P Q (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d :=
  green_param_image P Q Φ hU hP hQ hΦ hab hcd hΦU hS hSsub hSsup hinj hjac

/-- OpenStax Calculus 3:Example 6.40 (CA-633). The area of a region that is a `C²` image of a rectangle
equals the boundary line integral of `x dy`, of `-y dx`, and of `(x dy - y dx)/2`. -/
@[kb "openstaxcalculus2016" "3:Example 6.40, p. 648"]
theorem area_param_region_line_integrals (Φ : ℝ × ℝ → ℝ × ℝ) (hΦ : ContDiff ℝ 2 Φ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d) (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S)
    (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    let circ := fun P Q : ℝ × ℝ → ℝ =>
      greenLineIntegral P Q (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral P Q (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral P Q (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral P Q (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d
    (volume (Φ '' S)).toReal = circ (fun _ => 0) (fun p => p.1) ∧
      (volume (Φ '' S)).toReal = circ (fun p => -p.2) (fun _ => 0) ∧
      (volume (Φ '' S)).toReal = circ (fun p => -p.2 / 2) (fun p => p.1 / 2) :=
  area_param_image Φ hΦ hab hcd hS hSsub hSsup hinj hjac

/-- OpenStax Calculus 3:Theorem 6.13 (CA-634). Green's theorem, flux form, for regions that are `C²`
images of a rectangle: the double integral of the divergence equals the outward flux through the
image of the rectangle boundary (written as the circulation of `(-Q, P)`). -/
@[kb "openstaxcalculus2016" "3:Theorem 6.13, p. 650"]
theorem green_theorem_flux_param_region (P Q : ℝ × ℝ → ℝ) (Φ : ℝ × ℝ → ℝ × ℝ) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (hΦ : ContDiff ℝ 2 Φ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hΦU : ∀ z ∈ Icc a b ×ˢ Icc c d, Φ z ∈ U)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSsub : S ⊆ Icc a b ×ˢ Icc c d)
    (hSsup : Ioo a b ×ˢ Ioo c d ⊆ S) (hinj : InjOn Φ S) (hjac : ∀ z ∈ S, 0 ≤ jacobian2 Φ z) :
    ∫ p in Φ '' S, div2 P Q p =
      greenLineIntegral (fun p => -Q p) P (fun t => (Φ (t, c)).1) (fun t => (Φ (t, c)).2) a b +
        greenLineIntegral (fun p => -Q p) P (fun t => (Φ (b, t)).1) (fun t => (Φ (b, t)).2) c d -
        greenLineIntegral (fun p => -Q p) P (fun t => (Φ (t, d)).1) (fun t => (Φ (t, d)).2) a b -
        greenLineIntegral (fun p => -Q p) P (fun t => (Φ (a, t)).1) (fun t => (Φ (a, t)).2) c d :=
  green_flux_param_image P Q Φ hU hP hQ hΦ hab hcd hΦU hS hSsub hSsup hinj hjac

/-- OpenStax Calculus 3:§6.4 Theorem (Green's theorem on general regions) (CA-639). Green's theorem for a
region with a hole, namely the region swept between two closed `C²` curves by straight-line
interpolation: the double integral equals the outer boundary integral minus the inner one. -/
@[kb "openstaxcalculus2016" "3:§6.4 Theorem (Green's theorem on general regions), p. 656"]
theorem green_theorem_region_between_curves (P Q : ℝ × ℝ → ℝ) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) (γ₀ γ₁ : ℝ → ℝ × ℝ) (h₀ : ContDiff ℝ 2 γ₀)
    (h₁ : ContDiff ℝ 2 γ₁) {a b : ℝ} (hab : a ≤ b) (hc₀ : γ₀ a = γ₀ b) (hc₁ : γ₁ a = γ₁ b)
    (hΦU : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, (1 - s) • γ₀ t + s • γ₁ t ∈ U) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hSsub : S ⊆ Icc 0 1 ×ˢ Icc a b) (hSsup : Ioo 0 1 ×ˢ Ioo a b ⊆ S)
    (hinj : InjOn (fun z : ℝ × ℝ => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2) S)
    (hjac : ∀ z ∈ S, 0 ≤ jacobian2 (fun z : ℝ × ℝ => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2) z) :
    ∫ p in (fun z : ℝ × ℝ => (1 - z.1) • γ₀ z.2 + z.1 • γ₁ z.2) '' S, curl2 P Q p =
      greenLineIntegral P Q (fun t => (γ₁ t).1) (fun t => (γ₁ t).2) a b -
        greenLineIntegral P Q (fun t => (γ₀ t).1) (fun t => (γ₀ t).2) a b :=
  green_between_curves P Q hU hP hQ γ₀ γ₁ h₀ h₁ hab hc₀ hc₁ hΦU hS hSsub hSsup hinj hjac

/-- OpenStax Calculus 3:Example 6.47 (CA-640). For the swirl field `(-y, x)/(x²+y²)`, the circulation is
`0` around a `C²` closed curve that avoids a ray from the origin (so it does not enclose the origin), and
`2π` around a counterclockwise star-shaped polar-graph curve `r = ρ(θ)` enclosing the origin. -/
@[kb "openstaxcalculus2016" "3:Example 6.47, p. 658"]
theorem swirl_circulation_cases :
    (∀ (γ : ℝ → ℝ × ℝ), ContDiff ℝ 2 γ → ∀ {a b : ℝ}, a ≤ b → γ a = γ b → ∀ u : ℝ × ℝ, u ≠ 0 →
      (∀ t ∈ Icc a b, ∀ τ : ℝ, 0 ≤ τ → γ t ≠ τ • u) →
      greenLineIntegral swirlP swirlQ (fun t => (γ t).1) (fun t => (γ t).2) a b = 0) ∧
    (∀ (ρ : ℝ → ℝ), Differentiable ℝ ρ → (∀ θ ∈ Icc 0 (2 * π), 0 < ρ θ) →
      greenLineIntegral swirlP swirlQ (fun θ => ρ θ * Real.cos θ) (fun θ => ρ θ * Real.sin θ) 0 (2 * π) =
        2 * π) :=
  ⟨fun γ hγ _ _ hab hcl u hu hray => swirl_circulation_avoiding_ray γ hγ hab hcl u hu hray,
    fun ρ hρ hpos => swirl_circulation_polar_graph ρ hρ hpos⟩

/-- OpenStax Calculus 3:Theorem 6.19 (CA-658). Stokes' theorem for a `C²` parametrized surface over a
rectangle: the flux of the curl of a `C¹` field through the surface equals the line integral of the field
around the image of the rectangle boundary. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.19, p. 714"]
theorem stokes_theorem_param_surface (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (r : ℝ × ℝ → Fin 3 → ℝ) (hr : ContDiff ℝ 2 r) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hrU : ∀ z ∈ Icc a b ×ˢ Icc c d, r z ∈ U) :
    surfaceFlux (curlVec F) r (Icc a b ×ˢ Icc c d) =
      (∫ x in a..b, F (r (x, c)) ⬝ᵥ partialU r (x, c)) + (∫ y in c..d, F (r (b, y)) ⬝ᵥ partialV r (b, y)) -
        (∫ x in a..b, F (r (x, d)) ⬝ᵥ partialU r (x, d)) - (∫ y in c..d, F (r (a, y)) ⬝ᵥ partialV r (a, y)) :=
  stokes_param F hU hF r hr hab hcd hrU

/-- OpenStax Calculus 3:Example 6.74 (CA-659). Two `C²` parametrized surfaces over the same rectangle with
the same boundary curves (any such pair of surfaces) have equal flux of the curl of a `C¹` field. -/
@[kb "openstaxcalculus2016" "3:Example 6.74, p. 718"]
theorem curl_flux_same_boundary_equal (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (r₁ r₂ : ℝ × ℝ → Fin 3 → ℝ) (hr₁ : ContDiff ℝ 2 r₁) (hr₂ : ContDiff ℝ 2 r₂)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hrU₁ : ∀ z ∈ Icc a b ×ˢ Icc c d, r₁ z ∈ U)
    (hrU₂ : ∀ z ∈ Icc a b ×ˢ Icc c d, r₂ z ∈ U)
    (hx : ∀ x ∈ Icc a b, r₁ (x, c) = r₂ (x, c) ∧ r₁ (x, d) = r₂ (x, d))
    (hy : ∀ y ∈ Icc c d, r₁ (a, y) = r₂ (a, y) ∧ r₁ (b, y) = r₂ (b, y)) :
    surfaceFlux (curlVec F) r₁ (Icc a b ×ˢ Icc c d) = surfaceFlux (curlVec F) r₂ (Icc a b ×ˢ Icc c d) :=
  curl_flux_surface_independent F hU hF r₁ r₂ hr₁ hr₂ hab hcd hrU₁ hrU₂ hx hy

/-- OpenStax Calculus 3:Theorem 6.20 (CA-661). Divergence theorem for solids that are `C²` images of a
box: the triple integral of the divergence of a `C¹` field over the solid equals the outward flux through
the six image faces. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.20, p. 730"]
theorem divergence_theorem_param_solid (F : (Fin 3 → ℝ) → Fin 3 → ℝ) {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ) (hΦ : ContDiff ℝ 2 Φ) {a b : Fin 3 → ℝ}
    (hle : a ≤ b) (hΦU : ∀ z ∈ Icc a b, Φ z ∈ U) {S : Set (Fin 3 → ℝ)} (hS : MeasurableSet S)
    (hSsub : S ⊆ Icc a b) (hSsup : (Set.pi univ fun i => Ioo (a i) (b i)) ⊆ S) (hinj : InjOn Φ S)
    (hjac : ∀ z ∈ S, 0 ≤ jacobian3 Φ z) :
    ∫ x in Φ '' S, divVec F x =
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Φ (i.insertNth (b i) y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          F (Φ (i.insertNth (a i) y)) ⬝ᵥ crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
            (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) :=
  divergence_param_image F hU hF Φ hΦ hle hΦU hS hSsub hSsup hinj hjac

/-- OpenStax Calculus 3:Theorem 6.21 (CA-664). The flux of `r/‖r‖³` is `4π` through any closed surface
given as a differentiable radial graph around the origin (enclosing it), and is `0` through the boundary
of a `C²` parametrized box-solid that avoids the origin. -/
@[kb "openstaxcalculus2016" "3:Theorem 6.21, p. 738"]
theorem flux_invSquare_enclosing_or_not :
    (∀ (ρ : ℝ × ℝ → ℝ), Differentiable ℝ ρ → (∀ p ∈ sphereDomain, 0 < ρ p) →
      surfaceFlux invSquareField (radialGraph ρ) sphereDomain = 4 * π) ∧
    (∀ (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ), ContDiff ℝ 2 Φ → ∀ {a b : Fin 3 → ℝ}, a ≤ b →
      (∀ z ∈ Icc a b, Φ z ≠ 0) →
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          invSquareField (Φ (i.insertNth (b i) y)) ⬝ᵥ
            crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
              (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          invSquareField (Φ (i.insertNth (a i) y)) ⬝ᵥ
            crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
              (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) = 0) :=
  ⟨fun ρ hρ hpos => flux_invSquare_radialGraph ρ hρ hpos,
    fun Φ hΦ _ _ hle h0 => flux_invSquare_param_solid_eq_zero Φ hΦ hle h0⟩

/-- OpenStax Calculus 3:§6.8 Gauss' law (CA-665). For a point charge `q` at the origin, the field
`(q/(4π ε₀)) r/‖r‖³` has flux `q/ε₀` through any radial-graph surface enclosing the charge, and zero flux
through the boundary of a `C²` parametrized box-solid not containing the charge. -/
@[kb "openstaxcalculus2016" "3:§6.8 Gauss' law, p. 739"]
theorem gauss_law_enclosed_or_not :
    (∀ {q ε₀ : ℝ}, 0 < ε₀ → ∀ (ρ : ℝ × ℝ → ℝ), Differentiable ℝ ρ → (∀ p ∈ sphereDomain, 0 < ρ p) →
      surfaceFlux (fun x => (q / (4 * π * ε₀)) • invSquareField x) (radialGraph ρ) sphereDomain = q / ε₀) ∧
    (∀ (q ε₀ : ℝ) (Φ : (Fin 3 → ℝ) → Fin 3 → ℝ), ContDiff ℝ 2 Φ → ∀ {a b : Fin 3 → ℝ}, a ≤ b →
      (∀ z ∈ Icc a b, Φ z ≠ 0) →
      ∑ i : Fin 3, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          ((q / (4 * π * ε₀)) • invSquareField (Φ (i.insertNth (b i) y))) ⬝ᵥ
            crossProduct (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc1 i) 1))
              (fderiv ℝ Φ (i.insertNth (b i) y) (Pi.single (cyc2 i) 1))) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          ((q / (4 * π * ε₀)) • invSquareField (Φ (i.insertNth (a i) y))) ⬝ᵥ
            crossProduct (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc1 i) 1))
              (fderiv ℝ Φ (i.insertNth (a i) y) (Pi.single (cyc2 i) 1))) = 0) :=
  ⟨fun hε ρ hρ hpos => gauss_law_radialGraph hε ρ hρ hpos,
    fun q ε₀ Φ hΦ _ _ hle h0 => gauss_law_param_solid_no_charge q ε₀ Φ hΦ hle h0⟩

end UndergradKB.Calculus.Course.V3C6
