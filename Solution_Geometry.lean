/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import UndergradKB.Geometry.GaussWantzelSuff
import UndergradKB.Geometry.WallaceBolyai
import UndergradKB.Geometry.PonceletSteiner
import UndergradKB.Geometry.ProjectivePlane
import UndergradKB.Geometry.AffineFundamental
import UndergradKB.Geometry.ProjectiveFundamental
import UndergradKB.Geometry.NeutralTheorem1116
import UndergradKB.Geometry.NeutralLegendre

/-!
# Proofs of the geometry headline statements (Petrunin)

Each statement of `Challenge_Geometry.lean` is proved here from the library. `lake comparator` (configured by
`comparator/Geometry.json`) checks that each statement here is exactly the one in `Challenge_Geometry.lean` and
that the proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace UndergradKB.Headlines.Geometry

theorem gauss_wantzel {n : ℕ} (hn : 0 < n) :
    UndergradKB.Geometry.RCConstructible {(0, 0), (1, 0)}
        (.point (Real.cos (2 * Real.pi / n), Real.sin (2 * Real.pi / n))) ↔
      ∃ m : ℕ, Nat.totient n = 2 ^ m :=
  UndergradKB.Geometry.rcConstructible_ngon_vertex_iff hn

theorem wallace_bolyai_gerwien {P P' : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : UndergradKB.Geometry.IsPolygonal P) (hP' : UndergradKB.Geometry.IsPolygonal P')
    (hA : UndergradKB.Geometry.area P = UndergradKB.Geometry.area P')
    (hpos : 0 < UndergradKB.Geometry.area P) : UndergradKB.Geometry.Equidecomposable P P' :=
  UndergradKB.Geometry.equidecomposable_of_area_eq hP hP' hA hpos

theorem poncelet_steiner {O P : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hO : O ∈ S) (hP : P ∈ S)
    {E : ℝ × ℝ} (hE : E ∈ S)
    (hEoff : (P.1 - O.1) * (E.2 - O.2) - (P.2 - O.2) * (E.1 - O.1) ≠ 0)
    (hEcirc : (E.1 - O.1) ^ 2 + (E.2 - O.2) ^ 2 ≠ (P.1 - O.1) ^ 2 + (P.2 - O.2) ^ 2) (x : ℝ × ℝ) :
    UndergradKB.Geometry.RGConstructible O P S (.point x) ↔
      UndergradKB.Geometry.RCConstructible S (.point x) :=
  UndergradKB.Geometry.rgConstructible_iff_rcConstructible hO hP hE hEoff hEcirc x

theorem desargues {A B C A' B' C' X Y Z : UndergradKB.Geometry.ProjPoint}
    (hABC : ¬ UndergradKB.Geometry.ProjCollinear A B C)
    (hA'B'C' : ¬ UndergradKB.Geometry.ProjCollinear A' B' C')
    (hAA' : A ≠ A') (hBB' : B ≠ B') (hCC' : C ≠ C')
    (hX : UndergradKB.Geometry.ProjCollinear B C X ∧ UndergradKB.Geometry.ProjCollinear B' C' X)
    (hY : UndergradKB.Geometry.ProjCollinear C A Y ∧ UndergradKB.Geometry.ProjCollinear C' A' Y)
    (hZ : UndergradKB.Geometry.ProjCollinear A B Z ∧ UndergradKB.Geometry.ProjCollinear A' B' Z)
    (hlX : ¬ ∃ ℓ : UndergradKB.Geometry.ProjLine, B.LiesOn ℓ ∧ C.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C'.LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : UndergradKB.Geometry.ProjLine, C.LiesOn ℓ ∧ A.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ A'.LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : UndergradKB.Geometry.ProjLine, A.LiesOn ℓ ∧ B.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ B'.LiesOn ℓ) :
    (∃ O : UndergradKB.Geometry.ProjPoint,
        UndergradKB.Geometry.ProjCollinear A A' O ∧ UndergradKB.Geometry.ProjCollinear B B' O ∧
          UndergradKB.Geometry.ProjCollinear C C' O) ↔
      UndergradKB.Geometry.ProjCollinear X Y Z :=
  UndergradKB.Geometry.desargues_iff hABC hA'B'C' hAA' hBB' hCC' hX hY hZ hlX hlY hlZ

theorem pappus {A B C A' B' C' X Y Z : UndergradKB.Geometry.ProjPoint}
    (hABC : UndergradKB.Geometry.ProjCollinear A B C)
    (hA'B'C' : UndergradKB.Geometry.ProjCollinear A' B' C')
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) (hA'B' : A' ≠ B') (hB'C' : B' ≠ C') (hC'A' : C' ≠ A')
    (hAB' : A ≠ B') (hA'B : A' ≠ B) (hBC' : B ≠ C') (hB'C : B' ≠ C) (hCA' : C ≠ A') (hC'A : C' ≠ A)
    (hX : UndergradKB.Geometry.ProjCollinear B C' X ∧ UndergradKB.Geometry.ProjCollinear B' C X)
    (hY : UndergradKB.Geometry.ProjCollinear C A' Y ∧ UndergradKB.Geometry.ProjCollinear C' A Y)
    (hZ : UndergradKB.Geometry.ProjCollinear A B' Z ∧ UndergradKB.Geometry.ProjCollinear A' B Z)
    (hlX : ¬ ∃ ℓ : UndergradKB.Geometry.ProjLine, B.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ C.LiesOn ℓ)
    (hlY : ¬ ∃ ℓ : UndergradKB.Geometry.ProjLine, C.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ C'.LiesOn ℓ ∧ A.LiesOn ℓ)
    (hlZ : ¬ ∃ ℓ : UndergradKB.Geometry.ProjLine, A.LiesOn ℓ ∧ B'.LiesOn ℓ ∧ A'.LiesOn ℓ ∧ B.LiesOn ℓ) :
    UndergradKB.Geometry.ProjCollinear X Y Z :=
  UndergradKB.Geometry.pappus_proj hABC hA'B'C' hAB hBC hCA hA'B' hB'C' hC'A' hAB' hA'B hBC' hB'C hCA' hC'A
    hX hY hZ hlX hlY hlZ

theorem fundamental_affine {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
    [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂] {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) :
    ∃ g : P₁ ≃ᵃ[ℝ] P₂, ⇑g = f :=
  UndergradKB.Geometry.exists_affineEquiv_of_collinear_preserving hf hfwd hV₁ hV₂

theorem fundamental_projective {F : UndergradKB.Geometry.ProjPoint → UndergradKB.Geometry.ProjPoint}
    (hF : UndergradKB.Geometry.IsProjectiveTransformation F) :
    ∃ M : UndergradKB.Geometry.Space3 ≃ₗ[ℝ] UndergradKB.Geometry.Space3,
      F = UndergradKB.Geometry.ProjPoint.map M :=
  UndergradKB.Geometry.fundamental_projective hF

theorem neutral_plane_parallel_axiom {P : Type*} [MetricSpace P] (N : UndergradKB.Geometry.NeutralPlane P) :
    (N.AxiomV ↔ N.OnlyOneParallel) ∧ (N.AxiomV ↔ N.AllTrianglesCircumscribable) ∧
      (N.AxiomV ↔ N.BoundedDistantLines) ∧ (N.AxiomV ↔ N.ArbitrarilyLargeInradius) ∧
        (N.AxiomV ↔ N.ZeroDefectTriangle) ∧ (N.AxiomV ↔ N.HasRectangle) :=
  UndergradKB.Geometry.NeutralPlane.theorem_11_16 N

theorem saccheri_legendre {P : Type*} [MetricSpace P] (N : UndergradKB.Geometry.NeutralPlane P) {A B C : P}
    (hT : UndergradKB.Geometry.IsTriangle A B C) :
    N.uangle A B C + N.uangle B C A + N.uangle C A B ≤ Real.pi :=
  UndergradKB.Geometry.NeutralPlane.uangle_sum_le_pi N hT

end UndergradKB.Headlines.Geometry
