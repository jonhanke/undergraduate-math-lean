import UndergradKB.RepresentationTheory.DynkinClassification
import UndergradKB.RepresentationTheory.DynkinForms
import UndergradKB.RepresentationTheory.RootsA
import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.QuiverExamples
import UndergradKB.RepresentationTheory.QuiverA3
import UndergradKB.RepresentationTheory.ReflectionFunctors
import UndergradKB.RepresentationTheory.ReflectionFunctorsMore
import UndergradKB.RepresentationTheory.GabrielD4
import UndergradKB.RepresentationTheory.GabrielTheorem
import UndergradKB.RepresentationTheory.GabrielConverse
import UndergradKB.RepresentationTheory.AffineClassification
import UndergradKB.RepresentationTheory.McKayAffine
import UndergradKB.RepresentationTheory.McKayClassification
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: Chapter 5 (quiver representations)

Thin theorems in the book's terms for the items of Chapter 5 that are proved in this repository
(Dynkin and affine Dynkin diagrams, roots and reflections, indecomposable quiver representations,
reflection functors and Gabriel's theorem), each tagged with the source key `etingof2011` and the
locator of the item in the book.
-/

namespace UndergradKB.RepresentationTheory.Course

open UndergradKB.RepresentationTheory UndergradKB.RepresentationTheory.Roots
  UndergradKB.RepresentationTheory.Gabriel

universe u v w w' a

/-- Etingof et al., Problem 5.3: the paths `A_n`, the graphs `D_n`, `E_6`, `E_7`, `E_8` are Dynkin
diagrams (connected with positive definite form), and Mathlib's Cartan matrices `D` and `E` are the
Cartan matrices of the corresponding graphs. -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem etingof_5_3_a :
    (∀ n : ℕ, IsDynkin (SimpleGraph.pathGraph (n + 1))) ∧
    (∀ k : ℕ, IsDynkin (graphOfCartan (CartanMatrix.D (k + 3)))) ∧
    IsDynkin (graphOfCartan (CartanMatrix.E 6)) ∧
    IsDynkin (graphOfCartan (CartanMatrix.E 7)) ∧
    IsDynkin (graphOfCartan (CartanMatrix.E 8)) ∧
    (∀ m : ℕ, cartanMatrix (graphOfCartan (CartanMatrix.D m)) = CartanMatrix.D m) ∧
    (∀ m : ℕ, cartanMatrix (graphOfCartan (CartanMatrix.E m)) = CartanMatrix.E m) :=
  ⟨isDynkin_pathGraph, isDynkin_D, isDynkin_E6, isDynkin_E7, isDynkin_E8, cartanMatrix_D_eq,
    cartanMatrix_E_eq⟩

/-- Etingof et al., Problem 5.3: a connected graph with positive definite form is isomorphic to a
path `A_n`, to `D_n`, or to `E_6`, `E_7`, `E_8` (the classification of Dynkin diagrams). -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
theorem etingof_5_3_b {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : IsDynkin G) :
    Nonempty (SimpleGraph.pathGraph n ≃g G) ∨
    (3 ≤ n ∧ Nonempty (graphOfCartan (CartanMatrix.D n) ≃g G)) ∨
    (n = 6 ∧ Nonempty (graphOfCartan (CartanMatrix.E 6) ≃g G)) ∨
    (n = 7 ∧ Nonempty (graphOfCartan (CartanMatrix.E 7) ≃g G)) ∨
    (n = 8 ∧ Nonempty (graphOfCartan (CartanMatrix.E 8) ≃g G)) :=
  classification_dynkin G h

/-- Etingof et al., Problem 5.3(g): the cycle graphs and the diagrams `D̃_4`, `Ẽ_6`, `Ẽ_7`, `Ẽ_8` have
positive semidefinite form whose kernel is a line spanned by an explicit positive vector. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem etingof_5_3_g_a :
    (∀ k : ℕ, IsAffineKernel (affineCycle k) (fun _ => 1)) ∧
    IsAffineKernel affineD4 ![1, 1, 1, 1, 2] ∧
    IsAffineKernel affineE6 ![1, 2, 1, 2, 1, 2, 3] ∧
    IsAffineKernel affineE7 ![1, 2, 3, 1, 2, 3, 2, 4] ∧
    IsAffineKernel (graphOfCartan (CartanMatrix.E 9)) ![2, 3, 4, 6, 5, 4, 3, 2, 1] :=
  ⟨affine_cycle, affine_D4, affine_E6, affine_E7, affine_E8⟩

/-- Etingof et al., Problem 5.3(g): a graph with positive definite form contains none of the affine
diagrams as a subgraph. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem etingof_5_3_g_b {m n : ℕ} [NeZero m] {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {v : Fin m → ℤ} (hH : IsAffineKernel H v) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : PosDefinite G) (f : Fin m → Fin n) (hf : Function.Injective f)
    (hHG : ∀ i j, H.Adj i j → G.Adj (f i) (f j)) : False :=
  PosDefinite.not_embed_affine hH hG f hf hHG

/-- Etingof et al., Example 5.7: the quiver with one vertex and no arrows has exactly one
indecomposable representation, the line; a representation is indecomposable exactly when its space
has dimension one. -/
@[kb "etingof2011" "Example 5.7, p. 81"]
theorem etingof_5_7 {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] [Unique Q]
    [∀ i j : Q, IsEmpty (i ⟶ j)] (V : QRep k Q) :
    V.IsIndecomposable ↔ Module.rank k (V.obj default) = 1 :=
  isIndecomposable_iff_rank_eq_one V

/-- Etingof et al., Example 5.8: every indecomposable representation of the quiver `A₂` is isomorphic to
`k → 0`, `k → k` or `0 → k`. -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem etingof_5_8_a {k : Type u} [Field k] (V : QRep.{u, 0, u, 0} k A2V)
    (hV : V.IsIndecomposable) :
    QRep.Isomorphic V (A2Rep.kToZero k) ∨ QRep.Isomorphic V (A2Rep.kToK k) ∨
      QRep.Isomorphic V (A2Rep.zeroToK k) :=
  a2_classification V hV

/-- Etingof et al., Example 5.8: the three representations of `A₂` are pairwise non-isomorphic. -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem etingof_5_8_b (k : Type u) [Field k] :
    ¬ QRep.Isomorphic (A2Rep.kToZero k) (A2Rep.kToK k) ∧
    ¬ QRep.Isomorphic (A2Rep.kToZero k) (A2Rep.zeroToK k) ∧
    ¬ QRep.Isomorphic (A2Rep.kToK k) (A2Rep.zeroToK k) :=
  A2Rep.pairwise_not_isomorphic k

/-- Etingof et al., Example 5.9: the quiver `A₃` has six indecomposable representations up to
isomorphism; every indecomposable one is isomorphic to one of six models, the models are
indecomposable, and they are pairwise non-isomorphic. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem etingof_5_9 {k : Type u} [Field k] :
    (∀ V : QRep.{u, 0, u, 0} k A3V, V.IsIndecomposable →
      ∃ i : Fin 6, QRep.Isomorphic V (A3Rep.model k i)) ∧
    (∀ i : Fin 6, (A3Rep.model k i).IsIndecomposable) ∧
    (∀ i j : Fin 6, QRep.Isomorphic (A3Rep.model k i) (A3Rep.model k j) → i = j) :=
  ⟨fun V hV => a3_classification V hV, A3Rep.isIndecomposable_models,
    fun i j h => A3Rep.model_injective k i j h⟩

section D4

attribute [local instance] GabrielD4.d4Quiver

/-- Etingof et al., Example 5.10: the quiver `D₄` with the subspace orientation has twelve
indecomposable representations: a family of twelve finite-dimensional indecomposables such that every
finite-dimensional indecomposable is isomorphic to exactly one of them. -/
@[kb "etingof2011" "Example 5.10, p. 83"]
theorem etingof_5_10_a (k : Type u) [Field k] :
    ∃ M : Fin 12 → QRep.{u, 0, u, 0} k (Fin 4),
      (∀ i, (∀ j, Module.Finite k ((M i).obj j)) ∧ (M i).IsIndecomposable) ∧
      ∀ (V : QRep.{u, 0, w, 0} k (Fin 4)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
        ∃! i, V.Isomorphic (M i) :=
  GabrielD4.d4_twelve_indecomposables k

end D4

/-- Etingof et al., Example 5.10: the graph `D₄` has exactly twelve positive roots. -/
@[kb "etingof2011" "Example 5.10, p. 83"]
theorem etingof_5_10_b :
    {β : Fin 4 → ℤ | IsPositiveRoot GabrielD4.d4Graph β}.ncard = 12 :=
  GabrielD4.d4_positiveRoots_ncard

/-- Etingof et al., Example 5.10: the twelve explicit models of `D₄`-representations are
indecomposable and pairwise non-isomorphic. -/
@[kb "etingof2011" "Example 5.10, p. 83"]
theorem etingof_5_10_c (k : Type u) [Field k] :
    (∀ i : Fin 12, (D4Rep.model k i).IsIndecomposable) ∧
    (∀ i j : Fin 12, QRep.Isomorphic (D4Rep.model k i) (D4Rep.model k j) → i = j) :=
  ⟨D4Rep.isIndecomposable_models k, fun i j h => D4Rep.model_injective k i j h⟩

/-- Etingof et al., Lemma 5.12: the quadratic form of a graph takes only even values on integer
vectors. -/
@[kb "etingof2011" "Lemma 5.12, p. 87"]
theorem etingof_5_12_a {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℤ) :
    Even (form G x x) :=
  form_self_even G x

/-- Etingof et al., Lemma 5.12: if the form of a graph is positive definite, it takes values at
least two on nonzero integer vectors. -/
@[kb "etingof2011" "Lemma 5.12, p. 87"]
theorem etingof_5_12_b {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : PosDefinite G)
    {x : Fin n → ℤ} (hx : x ≠ 0) : 2 ≤ form G x x :=
  PosDefinite.two_le h hx

/-- Etingof et al., Lemma 5.16: a root of a graph with positive definite form has all coordinates
nonnegative or all nonpositive. -/
@[kb "etingof2011" "Lemma 5.16, p. 87"]
theorem etingof_5_16 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : PosDefinite G)
    {x : Fin n → ℤ} (hx : IsRoot G x) : (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) :=
  isRoot_sign G h hx

/-- Etingof et al., Example 5.19: the roots of the path graph (type `A`) are exactly the plus or minus
interval vectors `e_a - e_b`. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem etingof_5_19_a (n : ℕ) (x : Fin n → ℤ) :
    IsRoot (SimpleGraph.pathGraph n) x ↔
      ∃ a b : ℕ, a < b ∧ b ≤ n ∧ (x = intervalRoot n a b ∨ x = -intervalRoot n a b) :=
  isRoot_pathGraph_iff n x

/-- Etingof et al., Example 5.19: the path graph on `n` vertices has `(n + 1) n` roots. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem etingof_5_19_b (n : ℕ) :
    {x | IsRoot (SimpleGraph.pathGraph n) x}.ncard = (n + 1) * n :=
  ncard_roots_pathGraph n

/-- Etingof et al., Example 5.19: the path graph on `n` vertices has `(n + 1) n / 2` positive
roots. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem etingof_5_19_c (n : ℕ) :
    {x | IsPositiveRoot (SimpleGraph.pathGraph n) x}.ncard = (n + 1) * n / 2 :=
  ncard_positiveRoots_pathGraph n

/-- Etingof et al., Remark 5.21: the reflection in a root preserves the form of the graph. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem etingof_5_21_a {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (α : Fin n → ℤ)
    (hα : IsRoot G α) (u v : Fin n → ℤ) :
    form G (reflect G α hα u) (reflect G α hα v) = form G u v :=
  form_reflect G α hα u v

/-- Etingof et al., Remark 5.21: the reflection in a root is an involution. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem etingof_5_21_b {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (α : Fin n → ℤ)
    (hα : IsRoot G α) : Function.Involutive (reflect G α hα) :=
  reflect_involutive G α hα

/-- Etingof et al., Remark 5.21: the reflection in a root permutes the set of roots. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem etingof_5_21_c {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (α : Fin n → ℤ)
    (hα : IsRoot G α) :
    Set.BijOn (reflect G α hα) {x | IsRoot G x} {x | IsRoot G x} :=
  bijOn_reflect_roots G α hα

/-- Etingof et al., Remark 5.21: the Weyl group generated by the simple reflections of a graph with
positive definite form is finite. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem etingof_5_21_d {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : PosDefinite G) :
    Finite (weylGroup G) :=
  weylGroup_finite G h

/-- Etingof et al., Theorem 5.23 (Gabriel): for an orientation of a Dynkin diagram the set of positive
roots is finite, the dimension vector of every finite-dimensional indecomposable is a positive root,
every positive root occurs, and indecomposables with equal dimension vectors are isomorphic. -/
@[kb "etingof2011" "Theorem 5.23, p. 89"]
theorem etingof_5_23_a {k : Type u} [Field k] {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hD : IsDynkin G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q) :
    {β : Fin n → ℤ | IsPositiveRoot G β}.Finite ∧
    (∀ (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
      IsPositiveRoot G V.dimZ) ∧
    (∀ β, IsPositiveRoot G β → ∃ V : QRep.{u, 0, u, a} k (Fin n),
      (∀ j, Module.Finite k (V.obj j)) ∧ V.IsIndecomposable ∧ V.dimZ = β) ∧
    (∀ (V : QRep.{u, 0, w, a} k (Fin n)) (V' : QRep.{u, 0, w', a} k (Fin n))
      [∀ j, Module.Finite k (V.obj j)]
      [∀ j, Module.Finite k (V'.obj j)], V.IsIndecomposable → V'.IsIndecomposable →
      V.dimVec = V'.dimVec → V.Isomorphic V') :=
  gabriel G hD hQ

/-- Etingof et al., Theorem 5.23 (Gabriel, finite type): an orientation of a Dynkin diagram has a
finite family of finite-dimensional indecomposables indexed by the positive roots such that every
finite-dimensional indecomposable is isomorphic to exactly one member. -/
@[kb "etingof2011" "Theorem 5.23, p. 89"]
theorem etingof_5_23_b {k : Type u} [Field k] {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hD : IsDynkin G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q) :
    ∃ M : {β : Fin n → ℤ // IsPositiveRoot G β} → QRep.{u, 0, u, a} k (Fin n),
      Finite {β : Fin n → ℤ // IsPositiveRoot G β} ∧
      (∀ β, (∀ j, Module.Finite k ((M β).obj j)) ∧ (M β).IsIndecomposable ∧
        (M β).dimZ = β.1) ∧
      ∀ (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)], V.IsIndecomposable →
        ∃! β, V.Isomorphic (M β) :=
  gabriel_finiteType G hD hQ

section Reflection

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

/-- Etingof et al., Proposition 5.28: for an indecomposable representation and a sink `i`, either it is
the simple representation at `i` or the sum map into `V_i` is surjective. -/
@[kb "etingof2011" "Proposition 5.28, p. 90"]
theorem etingof_5_28_a (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)]
    (hi : Quiver.IsSink i) (hV : V.IsIndecomposable) :
    V.IsSimpleAt i ∨ Function.Surjective (sumIn V i) :=
  isSimpleAt_or_surjective_sumIn V i hi hV

/-- Etingof et al., Proposition 5.28: for an indecomposable representation and a source `i`, either it
is the simple representation at `i` or the map out of `V_i` is injective. -/
@[kb "etingof2011" "Proposition 5.28, p. 90"]
theorem etingof_5_28_b (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)]
    (hi : Quiver.IsSource i) (hV : V.IsIndecomposable) :
    V.IsSimpleAt i ∨ Function.Injective (outMap V i) :=
  isSimpleAt_or_injective_outMap V i hi hV

/-- Etingof et al., Proposition 5.29: if the sum map into the sink `i` is surjective, then applying the
reflection functors at a sink and then at the resulting source returns a representation isomorphic to
the original. -/
@[kb "etingof2011" "Proposition 5.29, p. 91"]
theorem etingof_5_29_a (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)]
    (hi : Quiver.IsSink i) (hsurj : Function.Surjective (sumIn V i)) :
    RevRevIso V (@reflectSource k _ Q (reversedAt i) (reflectSink V i hi) i
      (isSource_reversedAt hi)) :=
  reflectSource_reflectSink_iso V i hi hsurj

/-- Etingof et al., Proposition 5.29: if the map out of the source `i` is injective, then applying the
reflection functors at a source and then at the resulting sink returns a representation isomorphic to
the original. -/
@[kb "etingof2011" "Proposition 5.29, p. 91"]
theorem etingof_5_29_b (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)]
    (hi : Quiver.IsSource i) (hinj : Function.Injective (outMap V i)) :
    RevRevIso V (@reflectSink k _ Q (reversedAt i) (reflectSource V i hi) i
      (fintypeInArrowsRev i) (isSink_reversedAt hi)) :=
  reflectSink_reflectSource_iso V i hi hinj

/-- Etingof et al., Proposition 5.30: the reflection functor at a sink sends an indecomposable
representation that is not simple at `i` to an indecomposable one. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem etingof_5_30_a (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)]
    (hi : Quiver.IsSink i) (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSink V i hi) :=
  reflectSink_isIndecomposable hV hne

/-- Etingof et al., Proposition 5.30: the reflection functor at a source sends an indecomposable
representation that is not simple at `i` to an indecomposable one. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem etingof_5_30_b (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)]
    (hi : Quiver.IsSource i) (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSource V i hi) :=
  reflectSource_isIndecomposable hV hne

end Reflection

section Dimension

variable {k : Type u} [Field k] {n : ℕ} [Quiver.{a} (Fin n)] [∀ x y : Fin n, Fintype (x ⟶ y)]
  (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Etingof et al., Proposition 5.30: at a sink `i`, an indecomposable finite-dimensional
representation that is not simple at `i` goes to an indecomposable one with dimension vector `s_i d(V)`. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem etingof_5_30_c
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n)
    (hi : Quiver.IsSink i) (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSink V i hi) ∧
      (fun x => ((reflectSink V i hi).dimVec x : ℤ)) =
        Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) :=
  reflectSink_indecomposable_dimVec G hG V i hi hV hne

/-- Etingof et al., Proposition 5.30: at a source `i`, an indecomposable finite-dimensional
representation that is not simple at `i` goes to an indecomposable one with dimension vector `s_i d(V)`. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem etingof_5_30_d
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n)
    (hi : Quiver.IsSource i) (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSource V i hi) ∧
      (fun x => ((reflectSource V i hi).dimVec x : ℤ)) =
        Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) :=
  reflectSource_indecomposable_dimVec G hG V i hi hV hne

/-- Etingof et al., Proposition 5.31: if the sum map into a sink `i` is surjective, the dimension vector
of the reflected representation is `s_i` applied to that of `V`. -/
@[kb "etingof2011" "Proposition 5.31, p. 93"]
theorem etingof_5_31_a
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n)
    (hi : Quiver.IsSink i) (hsurj : Function.Surjective (sumIn V i)) :
    (fun x => ((reflectSink V i hi).dimVec x : ℤ)) =
      Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) :=
  dimVec_reflectSink G hG V i hi hsurj

/-- Etingof et al., Proposition 5.31: if the map out of a source `i` is injective, the dimension vector
of the reflected representation is `s_i` applied to that of `V`. -/
@[kb "etingof2011" "Proposition 5.31, p. 93"]
theorem etingof_5_31_b
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n)
    (hi : Quiver.IsSource i) (hinj : Function.Injective (outMap V i)) :
    (fun x => ((reflectSource V i hi).dimVec x : ℤ)) =
      Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) :=
  dimVec_reflectSource G hG V i hi hinj

end Dimension

/-- Etingof et al., Lemma 5.33: for a graph with positive definite form, a nonzero nonnegative vector
has some power of the Coxeter element with a strictly negative coordinate. -/
@[kb "etingof2011" "Lemma 5.33, p. 93"]
theorem etingof_5_33_a {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hP : PosDefinite G)
    {β : Fin n → ℤ} (hβ0 : β ≠ 0) (hβ : ∀ i, 0 ≤ β i) :
    ∃ N : ℕ, ∃ i, (coxeterElement G ^ N) β i < 0 :=
  exists_pow_coxeterElement_neg G hP hβ0 hβ

/-- Etingof et al., Lemma 5.33: for a graph with positive definite form, a vector fixed by the Coxeter
element is zero. -/
@[kb "etingof2011" "Lemma 5.33, p. 93"]
theorem etingof_5_33_b {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hP : PosDefinite G)
    {v : Fin n → ℤ} (hv : coxeterElement G v = v) : v = 0 :=
  eq_zero_of_coxeterElement_fixed G hP hv

section Gabriel

variable {k : Type u} [Field k] {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Etingof et al., Theorem 5.34: for a Dynkin quiver, a chain of reflection functors at sinks takes any
finite-dimensional indecomposable representation to one that is simple at some vertex, with dimension
vector the corresponding simple root. -/
@[kb "etingof2011" "Theorem 5.34, p. 95"]
theorem etingof_5_34 (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    (V : QRep.{u, 0, u, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (hV : V.IsIndecomposable) :
    ∃ (Q' : Quiver.{a} (Fin n)) (V' : @QRep.{u, 0, u, a} k (Fin n) _ Q') (i : Fin n),
      ReflChain Q V Q' V' ∧ @QRep.IsSimpleAt _ _ _ Q' V' i ∧
        @QRep.dimZ _ _ _ Q' V' = simpleRoot i :=
  exists_reflChain_simple G hP hQ V hV

/-- Etingof et al., Corollary 5.35: the dimension vector of a finite-dimensional indecomposable
representation of a Dynkin quiver is a positive root. -/
@[kb "etingof2011" "Corollary 5.35, p. 95"]
theorem etingof_5_35 (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    (V : QRep.{u, 0, w, a} k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (hV : V.IsIndecomposable) :
    IsPositiveRoot G V.dimZ :=
  isPositiveRoot_dimVec G hP hQ V hV

/-- Etingof et al., Corollary 5.36: two finite-dimensional indecomposable representations of a Dynkin
quiver with the same dimension vector are isomorphic. -/
@[kb "etingof2011" "Corollary 5.36, p. 95"]
theorem etingof_5_36 (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    (V : QRep.{u, 0, w, a} k (Fin n)) (V' : QRep.{u, 0, w', a} k (Fin n))
    [∀ j, Module.Finite k (V.obj j)] [∀ j, Module.Finite k (V'.obj j)]
    (hV : V.IsIndecomposable) (hV' : V'.IsIndecomposable) (hd : V.dimVec = V'.dimVec) :
    V.Isomorphic V' :=
  isomorphic_of_dimVec_eq G hP hQ V V' hV hV' hd

/-- Etingof et al., Corollary 5.37: every positive root of a Dynkin quiver is the dimension vector of a
finite-dimensional indecomposable representation. -/
@[kb "etingof2011" "Corollary 5.37, p. 96"]
theorem etingof_5_37 (hP : PosDefinite G) [Q : Quiver.{a} (Fin n)] (hQ : IsOrientation G Q)
    {β : Fin n → ℤ} (hβ : IsPositiveRoot G β) :
    ∃ V : QRep.{u, 0, u, a} k (Fin n), (∀ j, Module.Finite k (V.obj j)) ∧ V.IsIndecomposable ∧
      V.dimZ = β :=
  exists_indecomposable_of_isPositiveRoot G hP hQ hβ

end Gabriel

section D4Central

attribute [local instance] GabrielD4.d4Quiver

/-- Etingof et al., Example 5.38: for `D₄` oriented toward the center, there is a finite-dimensional
indecomposable representation with dimension vector `(1, 2, 1, 1)`, unique up to isomorphism. -/
@[kb "etingof2011" "Example 5.38, p. 96"]
theorem etingof_5_38_a (k : Type u) [Field k] :
    (∃ V : QRep.{u, 0, u, 0} k (Fin 4), (∀ j, Module.Finite k (V.obj j)) ∧ V.IsIndecomposable ∧
      V.dimZ = GabrielD4.d4Central) ∧
    ∀ (V V' : QRep.{u, 0, u, 0} k (Fin 4)) [∀ j, Module.Finite k (V.obj j)]
      [∀ j, Module.Finite k (V'.obj j)], V.IsIndecomposable → V'.IsIndecomposable →
      V.dimZ = GabrielD4.d4Central → V'.dimZ = GabrielD4.d4Central → V.Isomorphic V' :=
  GabrielD4.d4_central_indecomposable k

end D4Central

/-- Etingof et al., Example 5.38: the vector `(1, 2, 1, 1)` is a positive root of `D₄`. -/
@[kb "etingof2011" "Example 5.38, p. 96"]
theorem etingof_5_38_b : IsPositiveRoot GabrielD4.d4Graph GabrielD4.d4Central :=
  GabrielD4.d4_isPositiveRoot_central

/-- Etingof et al., Problem 5.3(g): a connected simply laced graph whose form is positive
semidefinite but not definite is a cycle `Ã_k`, a graph `D̃_k`, or one of `Ẽ_6`, `Ẽ_7`, `Ẽ_8`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem etingof_5_3_g_c {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : IsAffineDynkin G) :
    (∃ k, Nonempty (affineCycle k ≃g G)) ∨ (∃ k, Nonempty (affineD k ≃g G)) ∨
    Nonempty (affineE6 ≃g G) ∨ Nonempty (affineE7 ≃g G) ∨
    Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g G) :=
  classification_affine G h

/-- Etingof et al., Problem 5.3(g): conversely, every graph isomorphic to one of the affine
diagrams `Ã_k`, `D̃_k`, `Ẽ_6`, `Ẽ_7`, `Ẽ_8` is an affine Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem etingof_5_3_g_d {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : (∃ k, Nonempty (affineCycle k ≃g G)) ∨ (∃ k, Nonempty (affineD k ≃g G)) ∨
      Nonempty (affineE6 ≃g G) ∨ Nonempty (affineE7 ≃g G) ∨
      Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g G)) : IsAffineDynkin G :=
  isAffineDynkin_of_classification G h

/-- Etingof et al., Problem 5.3(g): the graph `D̃_k` has an explicit positive vector spanning the
kernel of its form (an affine kernel). -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem etingof_5_3_g_e (k : ℕ) : IsAffineKernel (affineD k) (affineDVec k) :=
  affine_D k

/-- Etingof et al., Problem 5.4(a): over an infinite field, if a quiver has finitely many
indecomposable representations, then its Tits form is positive on every nonzero dimension
vector. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem etingof_5_4_a {k : Type u} [Field k] {n : ℕ} [Q : Quiver.{a} (Fin n)]
    [∀ i j : Fin n, Fintype (i ⟶ j)] [Infinite k] (h : IsFiniteType Q k) (d : Fin n → ℕ)
    (hd : d ≠ 0) : 0 < titsForm (fun i => (d i : ℤ)) :=
  titsForm_pos_of_isFiniteType h d hd

open scoped Classical in
/-- Etingof et al., Problem 5.4(b): a connected quiver of finite type over an infinite field has no
loops, at most one arrow between two vertices, and a Dynkin diagram as underlying graph. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem etingof_5_4_b {k : Type u} [Field k] {n : ℕ} [Q : Quiver.{a} (Fin n)]
    [∀ i j : Fin n, Fintype (i ⟶ j)] [Infinite k] (hc : (underlyingGraph Q).Connected)
    (h : IsFiniteType Q k) :
    (∀ i : Fin n, IsEmpty (i ⟶ i)) ∧
      (∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) ∧
      IsDynkin (underlyingGraph Q) :=
  isDynkin_of_isFiniteType hc h

open scoped Classical Matrix in
/-- Etingof et al., Problem 5.5: for a nontrivial finite subgroup of `SU(2)`, the McKay matrix of
its natural two-dimensional representation has natural number entries, is symmetric with zero
diagonal, is connected, and `2I` minus it is positive semidefinite but not definite, with kernel
spanned by the vector of dimensions of the irreducible representations. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem etingof_5_5_a (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hG : G ≠ ⊥) :
    (∀ i j, ∃ n : ℕ, mckay (natRep G) i j = n) ∧
    (∀ i j, mckay (natRep G) i j = mckay (natRep G) j i) ∧
    (∀ i, mckay (natRep G) i i = 0) ∧
    (∀ i j, Relation.ReflTransGen (fun a b ↦ mckay (natRep G) a b ≠ 0) i j) ∧
    (mckayCartan G).PosSemidef ∧ ¬ (mckayCartan G).PosDef ∧
    ∀ x, mckayCartan G *ᵥ x = 0 → ∃ c : ℝ, x = c • dimVec G :=
  mckay_isAffineDynkin G hG

open scoped Classical in
/-- Etingof et al., Problem 5.5: the McKay graph of a nontrivial finite subgroup of `SU(2)` is a
double edge on two vertices (`Ã_1`), or a simple graph isomorphic to a cycle `Ã_k`, to `D̃_k`, or
to `Ẽ_6`, `Ẽ_7`, `Ẽ_8`. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem etingof_5_5_b (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hG : G ≠ ⊥) :
    (∃ i j : irrChars ℂ G, i ≠ j ∧ mckay (natRep G) i j = 2 ∧ ∀ k, k = i ∨ k = j) ∨
    ∃ (N : ℕ) (e : irrChars ℂ G ≃ Fin N) (M : SimpleGraph (Fin N)),
      (∀ i j, mckay (natRep G) i j = 0 ∨ mckay (natRep G) i j = 1) ∧
      (∀ i j, M.Adj (e i) (e j) ↔ mckay (natRep G) i j = 1) ∧
      ((∃ k, Nonempty (affineCycle k ≃g M)) ∨ (∃ k, Nonempty (affineD k ≃g M)) ∨
        Nonempty (affineE6 ≃g M) ∨ Nonempty (affineE7 ≃g M) ∨
        Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g M)) :=
  mckay_affine_classification G hG

end UndergradKB.RepresentationTheory.Course
