import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.ReflectionFunctors
import UndergradKB.RepresentationTheory.Roots
import UndergradKB.RepresentationTheory.IsotypicDecomposition
import UndergradKB.RepresentationTheory.Unitary
import UndergradKB.RepresentationTheory.VirtualCharacters
import UndergradKB.RepresentationTheory.SymmetricGroup
import UndergradKB.RepresentationTheory.KostkaNumbers
import UndergradKB.RepresentationTheory.Categories
import UndergradKB.RepresentationTheory.ProblemIcosahedron
import UndergradKB.Common.Attr

/-!
# Etingof et al., Introduction to Representation Theory: book definitions, wave 5

Course names for Problem 3.21 (at the end) and for sixteen book definitions that are formalized in this library as definitions rather than
theorems.  Each theorem below states the defining property of the repository's definition in the book's terms
and is proved directly from the definition (by `rfl`, `Iff.rfl`, a field projection or an existing lemma).
All are tagged with the source key `etingof2011` and the locator of the book item.
-/

namespace UndergradKB.RepresentationTheory.Course

open UndergradKB.RepresentationTheory

universe u v w a

/-! ### Quiver representations (Sections 1.7 and 5.1) -/

section QuiverReps

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{a} Q]

/-- Etingof et al., Definition 1.30: a representation of a quiver is a vector space at each vertex together with
a linear map for each arrow; the space at a vertex of the representation built from such data is the given one. -/
@[kb "etingof2011" "Definition 1.30, p. 13"]
theorem etingof_def_1_30_a (obj : Q → Type w) [∀ i, AddCommGroup (obj i)] [∀ i, Module k (obj i)]
    (f : ∀ {i j : Q}, (i ⟶ j) → obj i →ₗ[k] obj j) (i : Q) :
    (QRep.mk (k := k) (Q := Q) obj f).obj i = obj i := rfl

/-- Etingof et al., Definition 1.30: the map attached to an arrow `e : i ⟶ j` is the given linear map. -/
@[kb "etingof2011" "Definition 1.30, p. 13"]
theorem etingof_def_1_30_b (obj : Q → Type w) [∀ i, AddCommGroup (obj i)] [∀ i, Module k (obj i)]
    (f : ∀ {i j : Q}, (i ⟶ j) → obj i →ₗ[k] obj j) {i j : Q} (e : i ⟶ j) :
    (QRep.mk (k := k) (Q := Q) obj f).map e = f e := rfl

/-- Etingof et al., Definition 1.30: the map along an arrow of a representation of a quiver is a linear map
between the spaces at its endpoints. -/
@[kb "etingof2011" "Definition 1.30, p. 13"]
theorem etingof_def_1_30_c (V : QRep.{u, v, w, a} k Q) {i j : Q} (e : i ⟶ j) (c : k) (x y : V.obj i) :
    V.map e (c • x + y) = c • V.map e x + V.map e y := by
  simp

/-- Etingof et al., Definition 1.35: a subrepresentation of a quiver representation is a choice of a subspace
at each vertex, stable under the maps of all arrows. -/
@[kb "etingof2011" "Definition 1.35, p. 14"]
theorem etingof_def_1_35 {V : QRep.{u, v, w, a} k Q} (S : QRep.Subrep V) {i j : Q} (e : i ⟶ j)
    {x : V.obj i} (hx : x ∈ S.carrier i) : V.map e x ∈ S.carrier j :=
  S.map_mem e hx

/-- Etingof et al., Definition 1.36: the direct sum of two representations has, at each vertex, the direct sum
(product) of the two spaces. -/
@[kb "etingof2011" "Definition 1.36, p. 14"]
theorem etingof_def_1_36_a (V W : QRep.{u, v, w, a} k Q) (i : Q) :
    (QRep.directSum V W).obj i = (V.obj i × W.obj i) := rfl

/-- Etingof et al., Definition 1.36: the map of an arrow on the direct sum is the direct sum of the two maps. -/
@[kb "etingof2011" "Definition 1.36, p. 14"]
theorem etingof_def_1_36_b (V W : QRep.{u, v, w, a} k Q) {i j : Q} (e : i ⟶ j) :
    (QRep.directSum V W).map e = LinearMap.prodMap (V.map e) (W.map e) := rfl

/-- Etingof et al., Definition 1.37: a homomorphism of quiver representations is a family of linear maps at the
vertices which commute with the maps of the arrows (written as an equality of composites). -/
@[kb "etingof2011" "Definition 1.37, p. 14"]
theorem etingof_def_1_37_a {V W : QRep.{u, v, w, a} k Q} (f : QRep.Hom V W) {i j : Q} (e : i ⟶ j) :
    (f.app j).comp (V.map e) = (W.map e).comp (f.app i) :=
  f.comm e

/-- Etingof et al., Definition 1.37: the commutation condition on vectors: `f_j (V_e x) = W_e (f_i x)`. -/
@[kb "etingof2011" "Definition 1.37, p. 14"]
theorem etingof_def_1_37_b {V W : QRep.{u, v, w, a} k Q} (f : QRep.Hom V W) {i j : Q} (e : i ⟶ j)
    (x : V.obj i) : f.app j (V.map e x) = W.map e (f.app i x) :=
  LinearMap.congr_fun (f.comm e) x

/-- Etingof et al., Definition 1.37: homomorphisms compose vertexwise. -/
@[kb "etingof2011" "Definition 1.37, p. 14"]
theorem etingof_def_1_37_c {V W X : QRep.{u, v, w, a} k Q} (g : QRep.Hom W X) (f : QRep.Hom V W) (i : Q) :
    (g.comp f).app i = (g.app i).comp (f.app i) := rfl

/-- Etingof et al., Definition 1.37: two representations are isomorphic when there are homomorphisms in both
directions whose composites are the identities. -/
@[kb "etingof2011" "Definition 1.37, p. 14"]
theorem etingof_def_1_37_d (V W : QRep.{u, v, w, a} k Q) :
    QRep.Isomorphic V W ↔
      ∃ (f : QRep.Hom V W) (g : QRep.Hom W V), f.comp g = QRep.Hom.id W ∧ g.comp f = QRep.Hom.id V :=
  Iff.rfl

/-- Etingof et al., Definition 5.22: the dimension vector of a representation has, at each vertex, the dimension
of the space at that vertex. -/
@[kb "etingof2011" "Definition 5.22, p. 89"]
theorem etingof_def_5_22 (V : QRep.{u, v, w, a} k Q) (i : Q) :
    V.dimVec i = Module.finrank k (V.obj i) := rfl

end QuiverReps

section SinkSource

variable {Q : Type v} [Quiver.{a} Q]

/-- Etingof et al., Definition 5.24: a vertex is a sink if no arrow starts at it. -/
@[kb "etingof2011" "Definition 5.24, p. 90"]
theorem etingof_def_5_24_a (i : Q) :
    UndergradKB.RepresentationTheory.Quiver.IsSink i ↔ ∀ j : Q, IsEmpty (i ⟶ j) :=
  Iff.rfl

/-- Etingof et al., Definition 5.24: a vertex is a source if no arrow ends at it. -/
@[kb "etingof2011" "Definition 5.24, p. 90"]
theorem etingof_def_5_24_b (i : Q) :
    UndergradKB.RepresentationTheory.Quiver.IsSource i ↔ ∀ j : Q, IsEmpty (j ⟶ i) :=
  Iff.rfl

/-- Etingof et al., Definition 5.25: the quiver `Q_i` obtained by reversing the arrows at `i` has, from `x` to
`y`, the arrows of `Q` from `x` to `y` not touching `i`, together with the reversals of the arrows of `Q` from
`y` to `x` that touch `i`. -/
@[kb "etingof2011" "Definition 5.25, p. 90"]
theorem etingof_def_5_25 (i x y : Q) :
    @Quiver.Hom Q (reversedAt i) x y = RevHom i x y := rfl

end SinkSource

/-! ### Reflection functors (Section 5.5) -/

section Reflections

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{a} Q]

/-- Etingof et al., Definition 5.26: the space of `F_i^+ V` at a vertex `x` is the subspace `sinkL V i x` of the
ambient space (the kernel of the sum map out of the incoming spaces at `i`, and `V_x` elsewhere). -/
@[kb "etingof2011" "Definition 5.26, p. 90"]
theorem etingof_def_5_26_a (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)]
    (hi : UndergradKB.RepresentationTheory.Quiver.IsSink i) (x : Q) :
    @QRep.obj k Q _ (reversedAt i) (reflectSink V i hi) x = ↥(sinkL V i x) := rfl

/-- Etingof et al., Definition 5.26: at the sink `i` itself the space of `F_i^+ V` is the kernel of the sum map
`⨁_{j → i} V_j → V_i`. -/
@[kb "etingof2011" "Definition 5.26, p. 90"]
theorem etingof_def_5_26_b (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)] {x : Q} (h : x = i)
    (z : V.obj x × inProd V i) : z ∈ sinkL V i x ↔ z.1 = 0 ∧ sumIn V i z.2 = 0 :=
  mem_sinkL_of_eq V i h z

/-- Etingof et al., Definition 5.26: away from `i` the space of `F_i^+ V` is `V_x` itself. -/
@[kb "etingof2011" "Definition 5.26, p. 90"]
theorem etingof_def_5_26_c (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)] {x : Q} (h : x ≠ i)
    (z : V.obj x × inProd V i) : z ∈ sinkL V i x ↔ z.2 = 0 :=
  mem_sinkL_of_ne V i h z

/-- Etingof et al., Definition 5.27: the space of `F_i^- V` at a vertex `x` is the subspace `sourceL V i x` of the
ambient space (the cokernel of `V_i → ⨁_{i → j} V_j` at `i`, and `V_x` elsewhere). -/
@[kb "etingof2011" "Definition 5.27, p. 90"]
theorem etingof_def_5_27_a (V : QRep.{u, v, w, a} k Q) (i : Q)
    (hi : UndergradKB.RepresentationTheory.Quiver.IsSource i) (x : Q) :
    @QRep.obj k Q _ (reversedAt i) (reflectSource V i hi) x = ↥(sourceL V i x) := rfl

/-- Etingof et al., Definition 5.27: at the source `i` itself the space of `F_i^- V` is the cokernel of the map
`V_i → ⨁_{i → j} V_j` (the second factor, with the first factor zero). -/
@[kb "etingof2011" "Definition 5.27, p. 90"]
theorem etingof_def_5_27_b (V : QRep.{u, v, w, a} k Q) (i : Q) {x : Q} (h : x = i)
    (z : V.obj x × outCoker V i) : z ∈ sourceL V i x ↔ z.1 = 0 :=
  mem_sourceL_of_eq V i h z

/-- Etingof et al., Definition 5.27: away from `i` the space of `F_i^- V` is `V_x` itself. -/
@[kb "etingof2011" "Definition 5.27, p. 90"]
theorem etingof_def_5_27_c (V : QRep.{u, v, w, a} k Q) (i : Q) {x : Q} (h : x ≠ i)
    (z : V.obj x × outCoker V i) : z ∈ sourceL V i x ↔ z.2 = 0 :=
  mem_sourceL_of_ne V i h z

end Reflections

/-! ### Coxeter element (Section 5.7) -/

section Coxeter

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Etingof et al., Definition 5.32: the Coxeter element is the product `s_0 s_1 ⋯ s_{n-1}` of the simple
reflections of the graph. -/
@[kb "etingof2011" "Definition 5.32, p. 93"]
theorem etingof_def_5_32 :
    Roots.coxeterElement G = (List.ofFn (Roots.simpleReflection G)).prod := rfl

end Coxeter

/-! ### Isotypic decomposition (Definition 2.1 example) -/

section Isotypic

open scoped TensorProduct

variable (k : Type*) {A : Type*} [Field k] [Ring A] [Algebra k A]
  {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  {ι : Type*} [Fintype ι] (X : ι → Type*) [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)]
  [∀ i, Module A (X i)] [∀ i, IsScalarTower k A (X i)]
  [IsAlgClosed k] [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [IsSemisimpleModule A V] [FiniteDimensional k V]

/-- Etingof et al., Definition 2.1 example: the isomorphism `⨁ᵢ Xᵢ ⊗ Hom_A(Xᵢ, V) → V` is the evaluation map
`(xᵢ ⊗ fᵢ)ᵢ ↦ ∑ᵢ fᵢ(xᵢ)`. -/
@[kb "etingof2011" "Definition 2.1 example, p. 23"]
theorem etingof_def_2_1_a (hX : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
    (hcov : ∀ S : Submodule A V, IsSimpleModule A S → ∃ i, Nonempty (X i ≃ₗ[A] S))
    (z : Π i, X i ⊗[k] (X i →ₗ[A] V)) :
    isotypicDecomposition k X hX hcov z = ∑ i, evalHom k (X i) V (z i) :=
  isotypicEval_apply z

/-- Etingof et al., Definition 2.1 example: on the summand `Xᵢ ⊗ Hom_A(Xᵢ, V)` the isomorphism sends
`x ⊗ f` to `f x`. -/
@[kb "etingof2011" "Definition 2.1 example, p. 23"]
theorem etingof_def_2_1_b [DecidableEq ι] (hX : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
    (hcov : ∀ S : Submodule A V, IsSimpleModule A S → ∃ i, Nonempty (X i ≃ₗ[A] S))
    (i : ι) (x : X i) (f : X i →ₗ[A] V) :
    isotypicDecomposition k X hX hcov (Pi.single i (x ⊗ₜ[k] f)) = f x :=
  (isotypicEval_single i (x ⊗ₜ[k] f)).trans (evalHom_tmul x f)

end Isotypic

/-! ### Unitary representations, virtual characters -/

section Characters

open scoped InnerProductSpace

/-- Etingof et al., Definition 3.10: a complex representation on an inner product space is unitary when every
`ρ(g)` preserves the inner product. -/
@[kb "etingof2011" "Definition 3.10, p. 38"]
theorem etingof_def_3_10 {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V) :
    IsUnitaryRepresentation ρ ↔ ∀ (g : G) (v w : V), ⟪ρ g v, ρ g w⟫_ℂ = ⟪v, w⟫_ℂ :=
  Iff.rfl

/-- Etingof et al., Definition 4.26: a virtual character is an integer combination of irreducible characters. -/
@[kb "etingof2011" "Definition 4.26, p. 54"]
alias etingof_def_4_26 := mem_virtualChars_iff

end Characters

/-! ### Young diagrams, tableaux and Kostka numbers (Sections 4.11 and 4.15) -/

section Young

/-- Etingof et al., Definition 4.35: a tableau of the Young diagram of a partition of `n` is a filling of its
boxes by the numbers `1, …, n` (here `0, …, n-1`), each used once: a bijection from the boxes to `Fin n`. -/
@[kb "etingof2011" "Definition 4.35, p. 58"]
theorem etingof_def_4_35_a (μ : YoungDiagram) : YoungTableau μ = (μ ≃ Fin μ.card) := rfl

/-- Etingof et al., Definition 4.35: the row of the box containing the number `i` is the first coordinate of
that box. -/
@[kb "etingof2011" "Definition 4.35, p. 58"]
theorem etingof_def_4_35_b {μ : YoungDiagram} (T : YoungTableau μ) (i : Fin μ.card) :
    T.rowOf i = (T.symm i : ℕ × ℕ).1 := rfl

/-- Etingof et al., Definition 4.35: the column of the box containing the number `i` is the second coordinate of
that box. -/
@[kb "etingof2011" "Definition 4.35, p. 58"]
theorem etingof_def_4_35_c {μ : YoungDiagram} (T : YoungTableau μ) (i : Fin μ.card) :
    T.colOf i = (T.symm i : ℕ × ℕ).2 := rfl

/-- Etingof et al., Definition 4.45: the Kostka number `K_{μλ}` is the dimension of
`Hom_{S_n}(U_λ, V_μ)`, computed with the standard fillings of the two diagrams. -/
@[kb "etingof2011" "Definition 4.45, p. 60"]
theorem etingof_def_4_45_a {n : ℕ} (mu la : DiagramsOfSize n) :
    kostka mu la = kostkaDim (spechtTableau la) (spechtTableau mu) := rfl

/-- Etingof et al., Definition 4.45: the Kostka number is the dimension of the space of `S_n`-module maps from
`U_λ = ℂ[S_n] a_λ` to the Specht module `V_μ = ℂ[S_n] c_μ`. -/
@[kb "etingof2011" "Definition 4.45, p. 60"]
theorem etingof_def_4_45_b {n : ℕ} (mu la : DiagramsOfSize n) :
    kostka mu la =
      Module.finrank ℂ (permIdeal (spechtTableau la) →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
        Ideal.span {youngSymmetrizerN (spechtTableau mu)}) := rfl

end Young

/-! ### Semisimple abelian categories (Section 6.3) -/

section Semisimple

open CategoryTheory CategoryTheory.Limits

/-- Etingof et al., Definition 6.21: an abelian category is semisimple when every short exact sequence splits. -/
@[kb "etingof2011" "Definition 6.21, p. 105"]
theorem etingof_def_6_21 (C : Type u) [Category.{v} C] [Abelian C] :
    IsSemisimpleAbelianCategory C ↔ ∀ S : ShortComplex C, S.ShortExact → Nonempty S.Splitting :=
  Iff.rfl

end Semisimple

/-! ### Problem 3.21 (wave 5) -/

/-- Etingof et al., Problem 3.21(a): functions on the 12 vertices of the icosahedron (any transitive `A5`-set of
size 12) decompose as `1 ⊕ 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_a := Icosahedron.character_vertices

/-- Etingof et al., Problem 3.21(b): functions on the 20 faces decompose as `1 ⊕ 2 · 4 ⊕ 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_b := Icosahedron.character_faces

/-- Etingof et al., Problem 3.21(b): functions on the 30 edges decompose as `1 ⊕ 2 · 4 ⊕ 3 · 5 ⊕ 3 ⊕ 3'`. -/
@[kb "etingof2011" "Problem 3.21, p. 44"]
alias etingof_3_21_c := Icosahedron.character_edges

end UndergradKB.RepresentationTheory.Course
