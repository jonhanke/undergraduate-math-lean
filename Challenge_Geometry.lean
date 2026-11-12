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
# Headline statements of undergraduate-math-lean 0.2.0: geometry (Petrunin)

The main results of this topic that Mathlib and Tau Ceti lack, one theorem each, with every proof a deliberate
`sorry`: to check what is claimed, read this file. They are: the Gauss–Wantzel theorem on constructible regular
polygons; the Wallace–Bolyai–Gerwien theorem on cutting polygons into congruent pieces; the Poncelet–Steiner
theorem (a ruler and one given circle with its centre construct what ruler and compass construct); and the
theorems of Desargues (with its converse) and Pappus in the real projective plane; new in 0.2.0, the fundamental
theorems of affine and of projective geometry in the real plane, and, for a plane satisfying only the first four
axioms (a neutral plane), the equivalence of the parallel axiom with six classical conditions and the
Saccheri–Legendre theorem.
`Solution_Geometry.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/Geometry.json`) checks that each proved statement is exactly the one here and uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `UndergradKB.Geometry.RCObj`: the objects of a construction in coordinates: a point, the line through two
  points, or the circle with a given centre through a given point.
* `UndergradKB.Geometry.RCConstructible`: the objects obtainable from an initial set of points of the plane
  `ℝ × ℝ` by ruler and compass (new points are intersections of two non-parallel lines, of a line and a circle, or
  of two circles with different centres).
* `UndergradKB.Geometry.RGConstructible`: the objects obtainable from an initial set of points by a ruler
  together with one given circle (centre `O`, passing through `P`): new points are intersections of two
  non-parallel lines or of a line with the given circle.
* `UndergradKB.Geometry.IsPolygonal`: a subset of the Euclidean plane is polygonal when it is a finite union of
  points, segments and solid triangles.
* `UndergradKB.Geometry.area`: the area of a subset of the Euclidean plane, the real number given by its
  Lebesgue measure.
* `UndergradKB.Geometry.Equidecomposable`: two polygonal sets are equidecomposable when they can be subdivided
  into the same number of polygonal pieces (overlapping only in points and segments) that are pairwise congruent.
* `UndergradKB.Geometry.ProjPoint`, `UndergradKB.Geometry.ProjLine`: the points and lines of the real projective
  plane, as the one-dimensional and two-dimensional subspaces of three-dimensional Euclidean space.
* `UndergradKB.Geometry.ProjPoint.LiesOn`: a point lies on a line when the subspace is contained in the other.
* `UndergradKB.Geometry.ProjCollinear`: three points of the projective plane are collinear when they lie on a
  common line.
* `UndergradKB.Geometry.IsProjectiveTransformation F`: `F` is a bijection of the points of the projective plane that
  maps the points of every line onto the points of a line; `ProjPoint.map M` is the map induced by a linear
  automorphism `M` of `Space3 = EuclideanSpace ℝ (Fin 3)`.
* `UndergradKB.Geometry.NeutralPlane P` (Petrunin, p. 83): a metric space `P` with an angle measure `angle A O B`
  (in `Real.Angle`) satisfying Petrunin's Axioms I to IV (p. 19): two distinct points; a unique line (a subset
  isometric to `ℝ`) through two points; the protractor axioms (constructing an angle, additivity, continuity away
  from straight angles); side-angle-side congruence by motions of the plane. Both the Euclidean plane and the
  hyperbolic plane are neutral planes (`euclideanNeutralPlane`, `hyperbolicNeutralPlane`).
* `NeutralPlane.AxiomV` (Petrunin's Axiom V): scaling two sides of a triangle at a vertex by `k > 0` scales the third
  side by `k` and keeps the other two angles. Theorem 11.16's conditions: `OnlyOneParallel` (some line and point off
  it with exactly one parallel through the point); `AllTrianglesCircumscribable` (every nondegenerate triangle lies
  on a circle); `BoundedDistantLines` (two distinct lines at bounded distance); `ArbitrarilyLargeInradius`
  (triangles containing discs of every radius); `ZeroDefectTriangle` (a nondegenerate triangle with angle sum `π`);
  `HasRectangle` (four distinct points with four right angles).
* `IsTriangle A B C`: `A`, `B`, `C` are distinct; `N.uangle A O B = |angle A O B|` (as a real number in `[0, π]`).
-/

namespace UndergradKB.Headlines.Geometry

/-- **Gauss–Wantzel theorem** (Petrunin, Theorem 19.6, p. 158): for `n ≥ 1`, the vertex
`(cos (2π / n), sin (2π / n))` of the regular `n`-gon with centre `(0, 0)` and first vertex `(1, 0)` can be
constructed from `(0, 0)` and `(1, 0)` by ruler and compass if and only if Euler's totient `φ(n)` is a power of
2, that is, if and only if `n` is a power of 2 times distinct odd Fermat primes. Neither Mathlib nor Tau Ceti has
a theory of ruler-and-compass constructions. -/
theorem gauss_wantzel {n : ℕ} (hn : 0 < n) :
    UndergradKB.Geometry.RCConstructible {(0, 0), (1, 0)}
        (.point (Real.cos (2 * Real.pi / n), Real.sin (2 * Real.pi / n))) ↔
      ∃ m : ℕ, Nat.totient n = 2 ^ m := by
  sorry

/-- **Wallace–Bolyai–Gerwien theorem** (Petrunin, remark after Proposition 20.10, p. 170): two polygonal sets of
the Euclidean plane with equal positive area are equidecomposable, that is, each can be cut into finitely many
polygonal pieces so that the pieces of one are congruent to the pieces of the other. Positivity of the area
cannot be dropped for this definition: a point and a segment both have area 0. Absent from Mathlib; Tau Ceti's
`Equidecomp` is abstract equidecomposition for group actions. -/
theorem wallace_bolyai_gerwien {P P' : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : UndergradKB.Geometry.IsPolygonal P) (hP' : UndergradKB.Geometry.IsPolygonal P')
    (hA : UndergradKB.Geometry.area P = UndergradKB.Geometry.area P')
    (hpos : 0 < UndergradKB.Geometry.area P) : UndergradKB.Geometry.Equidecomposable P P' := by
  sorry

/-- **Poncelet–Steiner theorem** (Petrunin, p. 164): a ruler together with one given circle (centre `O`, passing
through `P`) constructs every point that ruler and compass construct, from an initial set `S` containing `O`,
`P` and a point `E` that is off the line `OP` (this is the first hypothesis on `E`) and off the given circle (the
second hypothesis, which cannot be dropped: if `E` lies on the circle, the ruler constructs only `O` and the four
vertices of a rectangle). The easy inclusion, from ruler and given circle to ruler and compass, is part of the
equivalence. Neither Mathlib nor Tau Ceti has a theory of ruler-and-compass constructions. -/
theorem poncelet_steiner {O P : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hO : O ∈ S) (hP : P ∈ S)
    {E : ℝ × ℝ} (hE : E ∈ S)
    (hEoff : (P.1 - O.1) * (E.2 - O.2) - (P.2 - O.2) * (E.1 - O.1) ≠ 0)
    (hEcirc : (E.1 - O.1) ^ 2 + (E.2 - O.2) ^ 2 ≠ (P.1 - O.1) ^ 2 + (P.2 - O.2) ^ 2) (x : ℝ × ℝ) :
    UndergradKB.Geometry.RGConstructible O P S (.point x) ↔
      UndergradKB.Geometry.RCConstructible S (.point x) := by
  sorry

/-- **Desargues' theorem with its converse** (Petrunin, Theorems 15.5 and 15.14, p. 129): for two nondegenerate
triangles `ABC` and `A'B'C'` of the real projective plane (with `A ≠ A'`, `B ≠ B'`, `C ≠ C'`) such that each pair
of corresponding sides are distinct lines, the lines `AA'`, `BB'`, `CC'` are concurrent if and only if the
intersection points `X`, `Y`, `Z` of corresponding sides are collinear. No Desargues theorem in Mathlib or Tau
Ceti. -/
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
      UndergradKB.Geometry.ProjCollinear X Y Z := by
  sorry

/-- **Pappus' theorem** (Petrunin, Theorem 15.6, p. 126): if `A, B, C` are collinear and `A', B', C'` are
collinear in the real projective plane, then the points `X = BC' ∩ B'C`, `Y = CA' ∩ C'A`, `Z = AB' ∩ A'B` are
collinear. The book's hypotheses are replaced by explicit nondegeneracy conditions: the six points are pairwise
distinct as needed and the pairs of lines are distinct. No Pappus theorem in Mathlib or Tau Ceti. -/
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
    UndergradKB.Geometry.ProjCollinear X Y Z := by
  sorry

/-- **The fundamental theorem of affine geometry** (Petrunin, Theorem 14.12 with Exercise 14.4; new in 0.2.0): a
bijection between two real affine planes that maps collinear triples to collinear triples is an affine
isomorphism. Related: neither Mathlib nor Tau Ceti has it. -/
theorem fundamental_affine {V₁ V₂ P₁ P₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddTorsor V₁ P₁]
    [AddCommGroup V₂] [Module ℝ V₂] [AddTorsor V₂ P₂] {f : P₁ → P₂} (hf : Function.Bijective f)
    (hfwd : ∀ A B C : P₁, Collinear ℝ ({A, B, C} : Set P₁) → Collinear ℝ ({f A, f B, f C} : Set P₂))
    (hV₁ : Module.finrank ℝ V₁ = 2) (hV₂ : Module.finrank ℝ V₂ = 2) :
    ∃ g : P₁ ≃ᵃ[ℝ] P₂, ⇑g = f := by
  sorry

/-- **The fundamental theorem of projective geometry** (Petrunin, Theorem 15.2; new in 0.2.0): every bijection of
the real projective plane that maps lines onto lines is induced by an invertible linear map of `ℝ³`. Related:
Mathlib has collinearity in projective spaces but no such theorem; Tau Ceti has none. -/
theorem fundamental_projective {F : UndergradKB.Geometry.ProjPoint → UndergradKB.Geometry.ProjPoint}
    (hF : UndergradKB.Geometry.IsProjectiveTransformation F) :
    ∃ M : UndergradKB.Geometry.Space3 ≃ₗ[ℝ] UndergradKB.Geometry.Space3,
      F = UndergradKB.Geometry.ProjPoint.map M := by
  sorry

/-- **Equivalent forms of the parallel axiom** (Petrunin, Theorem 11.16; new in 0.2.0): in a neutral plane (Axioms
I to IV only), Axiom V holds if and only if each of the following holds: some point off some line has exactly one
parallel; every triangle can be circumscribed; two distinct lines are at bounded distance; there are triangles of
arbitrarily large inradius; some triangle has angle sum `π`; there is a rectangle. Related: neither Mathlib nor Tau
Ceti has axiomatic plane geometry. -/
theorem neutral_plane_parallel_axiom {P : Type*} [MetricSpace P] (N : UndergradKB.Geometry.NeutralPlane P) :
    (N.AxiomV ↔ N.OnlyOneParallel) ∧ (N.AxiomV ↔ N.AllTrianglesCircumscribable) ∧
      (N.AxiomV ↔ N.BoundedDistantLines) ∧ (N.AxiomV ↔ N.ArbitrarilyLargeInradius) ∧
        (N.AxiomV ↔ N.ZeroDefectTriangle) ∧ (N.AxiomV ↔ N.HasRectangle) := by
  sorry

/-- **The Saccheri–Legendre theorem** (Petrunin, Theorem 11.10; new in 0.2.0): in a neutral plane, the angles of
every triangle add up to at most `π`. Related: neither Mathlib nor Tau Ceti has axiomatic plane geometry. -/
theorem saccheri_legendre {P : Type*} [MetricSpace P] (N : UndergradKB.Geometry.NeutralPlane P) {A B C : P}
    (hT : UndergradKB.Geometry.IsTriangle A B C) :
    N.uangle A B C + N.uangle B C A + N.uangle C A B ≤ Real.pi := by
  sorry

end UndergradKB.Headlines.Geometry
