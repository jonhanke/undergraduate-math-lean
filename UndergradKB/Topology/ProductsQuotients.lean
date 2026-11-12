import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Order
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Preorder.Chain
import UndergradKB.Common.Attr

/-!
# Products and quotients

Morris, *Topology Without Tears*, Chapters 10 and 11: projections and embeddings into products,
the Embedding Lemma, comparability, quotient maps, cells and spheres, cones, suspensions, and the
Moebius strip, projective plane and Klein bottle as quotients of the square.
-/

open Set Topology Filter unitInterval

namespace UndergradKB.Topology

/-! ### TP-243, TP-244: projections and factors of a product -/

section Pi

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- Morris, Topology Without Tears, Proposition 10.1.5 (TP-243).  Each coordinate projection of a
product is continuous, open, and surjective when all factors are nonempty. -/
@[kb "morris2024" "Proposition 10.1.5, p. 262"]
theorem proj_continuous_surjective_isOpenMap [∀ i, Nonempty (X i)] (j : ι) :
    Continuous (fun x : ∀ i, X i => x j) ∧ Function.Surjective (fun x : ∀ i, X i => x j) ∧
      IsOpenMap (fun x : ∀ i, X i => x j) :=
  ⟨continuous_apply j, Function.surjective_eval j, isOpenMap_eval j⟩

/-- Morris, Topology Without Tears, Proposition 10.1.5 (TP-243).  The product topology is the
coarsest topology making every coordinate projection continuous: any topology `t` for which all
projections are continuous is finer than the product topology (in Mathlib's order, `t ≤ product`). -/
@[kb "morris2024" "Proposition 10.1.5, p. 262"]
theorem le_productTopology_of_continuous_proj (t : TopologicalSpace (∀ i, X i))
    (h : ∀ j, Continuous[t, (inferInstance : TopologicalSpace (X j))] (fun x : ∀ i, X i => x j)) :
    t ≤ (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) :=
  le_iInf fun i => continuous_iff_le_induced.mp (h i)

/-- Morris, Topology Without Tears, Proposition 10.1.6 (TP-244).  If all factors are nonempty, each
factor embeds into the product (by freezing the other coordinates at fixed values). -/
@[kb "morris2024" "Proposition 10.1.6, p. 262"]
theorem exists_isEmbedding_factor [∀ i, Nonempty (X i)] (j : ι) :
    ∃ f : X j → ∀ i, X i, IsEmbedding f := by
  classical
  let x : ∀ i, X i := fun i => (Classical.arbitrary (X i))
  exact ⟨Function.update x j,
    Function.LeftInverse.isEmbedding (f := fun y : ∀ i, X i => y j) (by intro a; simp)
      (continuous_apply j) (continuous_const.update j continuous_id)⟩

/-- Morris, Topology Without Tears, Proposition 10.1.6 (TP-244).  Each factor is homeomorphic to a
subspace of the product space (when all factors are nonempty). -/
@[kb "morris2024" "Proposition 10.1.6, p. 262"]
theorem exists_homeomorph_range_factor [∀ i, Nonempty (X i)] (j : ι) :
    ∃ (f : X j → ∀ i, X i), Nonempty (X j ≃ₜ range f) := by
  obtain ⟨f, hf⟩ := exists_isEmbedding_factor (X := X) j
  exact ⟨f, ⟨hf.toHomeomorph⟩⟩

end Pi

/-! ### TP-247: the Embedding Lemma -/

section Embedding

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]

/-- Morris, Topology Without Tears, Lemma 10.1.9 (TP-247).  The Embedding Lemma: continuous maps
`f i : X → Y i` that separate points and separate points from closed sets give an embedding
`x ↦ (f i x)_i` of `X` into the product. -/
@[kb "morris2024" "Lemma 10.1.9, p. 263"]
theorem isEmbedding_eval (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hpt : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y)
    (hcl : ∀ x (A : Set X), IsClosed A → x ∉ A → ∃ i, f i x ∉ closure (f i '' A)) :
    IsEmbedding (fun x i => f i x) := by
  refine ⟨?_, fun x y hxy => ?_⟩
  · rw [isInducing_iff_nhds]
    intro x
    refine le_antisymm (Filter.tendsto_iff_comap.mp (continuous_pi hf).continuousAt) ?_
    intro U hU
    obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
    obtain ⟨i, hi⟩ := hcl x U'ᶜ hU'o.isClosed_compl (fun h => h hxU')
    rw [Filter.mem_comap]
    refine ⟨(fun z : ∀ i, Y i => z i) ⁻¹' (closure (f i '' U'ᶜ))ᶜ, ?_, ?_⟩
    · exact ((continuous_apply i).isOpen_preimage _ isClosed_closure.isOpen_compl).mem_nhds hi
    · intro t ht
      apply hU'U
      by_contra hn
      exact ht (subset_closure ⟨t, hn, rfl⟩)
  · by_contra hne
    obtain ⟨i, hi⟩ := hpt x y hne
    exact hi (congrFun hxy i)

/-- Morris, Topology Without Tears, Corollary 10.1.10 (TP-247).  For a T1 domain, separating points
from closed sets already gives the embedding. -/
@[kb "morris2024" "Corollary 10.1.10, p. 263"]
theorem isEmbedding_eval_of_t1 [T1Space X] (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hcl : ∀ x (A : Set X), IsClosed A → x ∉ A → ∃ i, f i x ∉ closure (f i '' A)) :
    IsEmbedding (fun x i => f i x) := by
  refine isEmbedding_eval f hf (fun x y hxy => ?_) hcl
  obtain ⟨i, hi⟩ := hcl x {y} isClosed_singleton (fun h => hxy h)
  exact ⟨i, fun h => hi (by rw [h]; exact subset_closure ⟨y, rfl, rfl⟩)⟩

/-- Morris, Topology Without Tears, Lemma 10.1.9 (TP-247).  The evaluation map is a homeomorphism
of `X` onto its image with the subspace topology. -/
@[kb "morris2024" "Lemma 10.1.9, p. 263"]
theorem nonempty_homeomorph_range_eval (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hpt : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y)
    (hcl : ∀ x (A : Set X), IsClosed A → x ∉ A → ∃ i, f i x ∉ closure (f i '' A)) :
    Nonempty (X ≃ₜ range (fun x i => f i x)) :=
  ⟨(isEmbedding_eval f hf hpt hcl).toHomeomorph⟩

end Embedding

/-! ### TP-250: comparable elements -/

/-- Morris, Topology Without Tears, Definition 10.2.7 (TP-250).  Two elements of an ordered set are
comparable if one is below the other. -/
@[kb "morris2024" "Definition 10.2.7, p. 269"]
def AreComparable {α : Type*} [LE α] (x y : α) : Prop := x ≤ y ∨ y ≤ x

/-- Morris, Topology Without Tears, Definition 10.2.7 (TP-250).  Two elements are comparable iff
the pair is a chain in the sense of Mathlib. -/
@[kb "morris2024" "Definition 10.2.7, p. 269"]
theorem areComparable_iff_isChain_pair {α : Type*} [Preorder α] (x y : α) :
    AreComparable x y ↔ IsChain (· ≤ ·) ({x, y} : Set α) := by
  unfold AreComparable IsChain
  rw [Set.pairwise_pair]
  constructor
  · rintro h -
    exact ⟨h, h.symm⟩
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy.le
    · exact (h hxy).1

/-! ### TP-258, TP-262: quotient maps -/

section QuotientMaps

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Morris, Topology Without Tears, Remark 11.1.4 (TP-258).  A bijection is a homeomorphism iff it
is a quotient map. -/
@[kb "morris2024" "Remark 11.1.4, p. 340"]
theorem isHomeomorph_iff_isQuotientMap_of_bijective {f : X → Y} (hf : Function.Bijective f) :
    IsHomeomorph f ↔ IsQuotientMap f := by
  rw [isHomeomorph_iff_isQuotientMap_injective]
  exact ⟨fun h => h.1, fun h => ⟨h, hf.1⟩⟩

/-- Morris, Topology Without Tears, Remark 11.1.9 (TP-262).  A continuous surjective open map is a
quotient map. -/
@[kb "morris2024" "Remark 11.1.9, p. 341"]
theorem isQuotientMap_of_isOpenMap {f : X → Y} (hc : Continuous f) (hs : Function.Surjective f)
    (ho : IsOpenMap f) : IsQuotientMap f :=
  ho.isQuotientMap hc hs

/-- Morris, Topology Without Tears, Remark 11.1.9 (TP-262).  A continuous surjective closed map is
a quotient map. -/
@[kb "morris2024" "Remark 11.1.9, p. 341"]
theorem isQuotientMap_of_isClosedMap {f : X → Y} (hc : Continuous f) (hs : Function.Surjective f)
    (ho : IsClosedMap f) : IsQuotientMap f :=
  ho.isQuotientMap hc hs

end QuotientMaps

private theorem not_isOpen_singleton_false : ¬ IsOpen ({False} : Set Prop) := by
  intro h
  have h1 : ({False} : Set Prop) ∈ 𝓝 False := h.mem_nhds rfl
  rw [nhds_false, Filter.mem_top] at h1
  have : True ∈ ({False} : Set Prop) := by rw [h1]; trivial
  exact absurd this (by simp)

/-- Morris, Topology Without Tears, Remark 11.1.9 (TP-262).  A quotient map need be neither open
nor closed: the map `ℝ → Prop`, `x ↦ (0 < x)`, onto the Sierpinski space is a quotient map that is
neither an open map nor a closed map. -/
@[kb "morris2024" "Remark 11.1.9, p. 341"]
theorem exists_isQuotientMap_not_isOpenMap_not_isClosedMap :
    ∃ f : ℝ → Prop, IsQuotientMap f ∧ ¬ IsOpenMap f ∧ ¬ IsClosedMap f := by
  have hcont : Continuous (fun x : ℝ => 0 < x) := continuous_Prop.mpr isOpen_Ioi
  have hsurj : Function.Surjective (fun x : ℝ => 0 < x) := by
    intro p
    by_cases hp : p
    · exact ⟨1, by simpa using hp⟩
    · exact ⟨0, by simpa using hp⟩
  refine ⟨fun x => 0 < x, ⟨isCoinducing_iff.mpr fun s => ⟨fun hs => ?_, fun hs => ?_⟩, hsurj⟩,
    ?_, ?_⟩
  · by_cases hT : True ∈ s
    · by_cases hF : False ∈ s
      · have : s = univ := eq_univ_of_forall fun p => by
          by_cases hp : p
          · rw [eq_true hp]; exact hT
          · rw [eq_false hp]; exact hF
        rw [this]; exact isOpen_univ
      · have : s = {True} := by
          ext p
          by_cases hp : p
          · rw [eq_true hp]; simp [hT]
          · rw [eq_false hp]; simp [hF]
        rw [this]; exact isOpen_singleton_true
    · by_cases hF : False ∈ s
      · exfalso
        have h0 : (0 : ℝ) ∈ (fun x : ℝ => 0 < x) ⁻¹' s := by simpa using hF
        obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds h0)
        have hu : (0 : ℝ) < u / 2 := by linarith [hlu.2]
        have hmem : u / 2 ∈ Ioo l u := ⟨by linarith [hlu.1, hlu.2], by linarith [hlu.2]⟩
        have := hsub hmem
        simp only [mem_preimage, eq_true hu] at this
        exact hT this
      · have : s = ∅ := by
          ext p
          by_cases hp : p
          · rw [eq_true hp]; simp [hT]
          · rw [eq_false hp]; simp [hF]
        rw [this]; exact isOpen_empty
  · exact hs.preimage hcont
  · intro h
    apply not_isOpen_singleton_false
    have := h _ (isOpen_Iio (a := (0 : ℝ)))
    convert this using 1
    ext p
    constructor
    · intro hp
      refine ⟨-1, by simp, ?_⟩
      rw [show p = False from hp]
      simp
    · rintro ⟨x, hx, rfl⟩
      simpa using hx.le
  · intro h
    have h1 := h _ (isClosed_Ici (a := (1 : ℝ)))
    have h2 : (fun x : ℝ => 0 < x) '' Ici 1 = {True} := by
      ext p
      constructor
      · rintro ⟨x, hx, rfl⟩
        have : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
        simpa using this
      · intro hp
        exact ⟨1, Set.mem_Ici.mpr le_rfl, by rw [show p = True from hp]; simp⟩
    rw [h2, ← isOpen_compl_iff] at h1
    apply not_isOpen_singleton_false
    convert h1 using 1
    ext p
    simp [eq_iff_iff]

/-! ### TP-267, TP-268: cells, balls and spheres in Euclidean space -/

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The cell (closed unit ball) `E^n`
in Euclidean `n`-space. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
noncomputable abbrev Cell (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The open unit ball `B^n`. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
noncomputable abbrev OpenBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The unit sphere `S^(n-1)` in
Euclidean `n`-space. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
noncomputable abbrev UnitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.sphere 0 1

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The cell is the set of vectors of
norm at most one. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem mem_cell_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : x ∈ Cell n ↔ ‖x‖ ≤ 1 :=
  mem_closedBall_zero_iff

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The open ball is the set of vectors
of norm less than one. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem mem_openBall_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : x ∈ OpenBall n ↔ ‖x‖ < 1 :=
  mem_ball_zero_iff

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The sphere is the set of vectors
of norm one. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem mem_unitSphere_iff {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : x ∈ UnitSphere n ↔ ‖x‖ = 1 :=
  mem_sphere_zero_iff_norm

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The cell is compact (closed and
bounded). -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem isCompact_cell (n : ℕ) : IsCompact (Cell n) := isCompact_closedBall 0 1

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The sphere is compact. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem isCompact_unitSphere (n : ℕ) : IsCompact (UnitSphere n) := isCompact_sphere 0 1

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The cell and the sphere are closed
sets. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem isClosed_cell_and_isClosed_unitSphere (n : ℕ) : IsClosed (Cell n) ∧ IsClosed (UnitSphere n) :=
  ⟨Metric.isClosed_closedBall, Metric.isClosed_sphere⟩

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  The open ball and the sphere lie in
the cell, and the cell is their union. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem cell_eq_openBall_union_unitSphere (n : ℕ) : Cell n = OpenBall n ∪ UnitSphere n := by
  ext x
  simp only [mem_cell_iff, mem_openBall_iff, mem_unitSphere_iff, mem_union]
  exact le_iff_lt_or_eq

/-- Morris, Topology Without Tears, Definition 11.2.8 (TP-267).  `E^0 = B^0 = {0}`. -/
@[kb "morris2024" "Definition 11.2.8, p. 345"]
theorem cell_zero_eq_openBall_zero_eq_singleton :
    Cell 0 = {0} ∧ OpenBall 0 = {0} := by
  have h : ∀ x : EuclideanSpace ℝ (Fin 0), x = 0 := fun x => Subsingleton.elim _ _
  constructor
  · ext x; simp [h x]
  · ext x; simp [h x]

/-- Morris, Topology Without Tears, Proposition 11.2.9 (TP-268).  The product of the cells `E^m` and
`E^n` is homeomorphic to the cell `E^(m+n)`. -/
@[kb "morris2024" "Proposition 11.2.9, p. 345"]
theorem nonempty_homeomorph_cell_prod_cell (m n : ℕ) :
    Nonempty (↥(Cell m) × ↥(Cell n) ≃ₜ ↥(Cell (m + n))) := by
  let P := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  have hfin : Module.finrank ℝ P = Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + n))) := by
    simp [P]
  let e : P ≃L[ℝ] EuclideanSpace ℝ (Fin (m + n)) :=
    (LinearEquiv.ofFinrankEq _ _ hfin).toContinuousLinearEquiv
  let A : Set P := Cell m ×ˢ Cell n
  have hAconv : Convex ℝ A := (convex_closedBall _ _).prod (convex_closedBall _ _)
  have hAcpt : IsCompact A := (isCompact_cell m).prod (isCompact_cell n)
  have hAnhds : A ∈ 𝓝 (0 : P) :=
    prod_mem_nhds (Metric.closedBall_mem_nhds _ one_pos) (Metric.closedBall_mem_nhds _ one_pos)
  have hsnhds : e '' A ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin (m + n))) := by
    simpa using e.toHomeomorph.isOpenMap.image_mem_nhds hAnhds
  have hsconv : Convex ℝ (e '' A) :=
    hAconv.is_linear_image (f := e) e.toLinearEquiv.toLinearMap.isLinear
  have hsbdd : Bornology.IsBounded (e '' A) :=
    (e.toContinuousLinearMap.lipschitzWith.isBounded_image hAcpt.isBounded)
  have hscl : closure (e '' A) = e '' A := (hAcpt.image e.continuous).isClosed.closure_eq
  obtain ⟨h, -, hh, -⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hsconv
    ⟨0, mem_interior_iff_mem_nhds.mpr hsnhds⟩ hsbdd
  rw [hscl] at hh
  let g : P ≃ₜ EuclideanSpace ℝ (Fin (m + n)) := e.toHomeomorph.trans h
  have hg : g '' A = Cell (m + n) := by
    exact (image_image h e A).symm.trans hh
  exact ⟨((Homeomorph.Set.prod (Cell m) (Cell n)).symm.trans (g.image A)).trans
    (Homeomorph.setCongr hg)⟩

/-! ### TP-266, TP-270: cone and suspension -/

section Cone

set_option linter.unusedSectionVars false

variable (X : Type*) [TopologicalSpace X]

/-- The equivalence relation on `X × [0,1]` collapsing `X × {0}` to a point. -/
def coneSetoid : Setoid (X × unitInterval) where
  r p q := p = q ∨ (p.2 = 0 ∧ q.2 = 0)
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro p q (h | ⟨h1, h2⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨h2, h1⟩
      trans := by
        rintro p q r (rfl | ⟨h1, h2⟩) (rfl | ⟨h3, h4⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨h3, h4⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h4⟩ }

/-- Morris, Topology Without Tears, Definition 11.2.5 (TP-266).  The cone `CX` over a space `X`:
the quotient of `X × [0,1]` collapsing `X × {0}` to a point. -/
@[kb "morris2024" "Definition 11.2.5, p. 344"]
abbrev Cone : Type _ := Quotient (coneSetoid X)

variable {X}

/-- The quotient map `X × [0,1] → CX`, `(x, a) ↦ ⟨x, a⟩`. -/
def coneMk : X × unitInterval → Cone X := Quotient.mk (coneSetoid X)

/-- Morris, Topology Without Tears, Definition 11.2.5 (TP-266).  Two points of `X × [0,1]` have the
same image in `CX` iff they are equal or both lie on `X × {0}`. -/
@[kb "morris2024" "Definition 11.2.5, p. 344"]
theorem coneMk_eq_iff (p q : X × unitInterval) :
    coneMk p = coneMk q ↔ p = q ∨ (p.2 = 0 ∧ q.2 = 0) :=
  Quotient.eq (r := coneSetoid X)

/-- Morris, Topology Without Tears, Definition 11.2.5 (TP-266).  The map `X × [0,1] → CX` is a
quotient map (by definition of the quotient topology). -/
@[kb "morris2024" "Definition 11.2.5, p. 344"]
theorem isQuotientMap_coneMk : IsQuotientMap (coneMk : X × unitInterval → Cone X) :=
  isQuotientMap_quotient_mk'

/-- Morris, Topology Without Tears, Definition 11.2.5 (TP-266).  The cone over a compact space is
compact. -/
@[kb "morris2024" "Definition 11.2.5, p. 344"]
theorem compactSpace_cone [CompactSpace X] : CompactSpace (Cone X) := inferInstance

/-- Morris, Topology Without Tears, Definition 11.2.5 (TP-266).  The cone over a nonempty space is
path connected: every point is joined to the apex along the segment `s ↦ ⟨x, s a⟩`. -/
@[kb "morris2024" "Definition 11.2.5, p. 344"]
theorem pathConnectedSpace_cone [Nonempty X] : PathConnectedSpace (Cone X) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have key : ∀ p : X × unitInterval, Joined (coneMk (x₀, 0)) (coneMk p) := by
    rintro ⟨x, t⟩
    have h0 : coneMk (x₀, 0) = coneMk (x, 0) := (coneMk_eq_iff _ _).mpr (Or.inr ⟨rfl, rfl⟩)
    rw [h0]
    refine ⟨{ toFun := fun s => coneMk (x, s * t)
              continuous_toFun := ?_
              source' := by simp
              target' := by simp }⟩
    exact isQuotientMap_coneMk.continuous.comp (by fun_prop)
  refine ⟨⟨coneMk (x₀, 0)⟩, fun a b => ?_⟩
  obtain ⟨p, rfl⟩ := isQuotientMap_coneMk.surjective a
  obtain ⟨q, rfl⟩ := isQuotientMap_coneMk.surjective b
  exact (key p).symm.trans (key q)

/-- Morris, Topology Without Tears, Remark 11.2.6 (TP-266).  The map `x ↦ ⟨x, 1⟩` embeds `X` in its
cone. -/
@[kb "morris2024" "Remark 11.2.6, p. 344"]
theorem isEmbedding_coneMk_one : IsEmbedding (fun x : X => coneMk (x, 1)) := by
  let U : Set (X × unitInterval) := {p | p.2 ≠ 0}
  let s : Set (Cone X) := coneMk '' U
  have hmem : ∀ p, coneMk p ∈ s → p ∈ U := by
    rintro p ⟨q, hq, hqp⟩
    rcases (coneMk_eq_iff q p).mp hqp with rfl | ⟨h1, h2⟩
    · exact hq
    · exact absurd h1 hq
  have hUo : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hpre : coneMk ⁻¹' s = U := by
    ext p
    exact ⟨hmem p, fun hp => ⟨p, hp, rfl⟩⟩
  have hso : IsOpen s := by
    rw [← isQuotientMap_coneMk.isOpen_preimage, hpre]
    exact hUo
  have hq := isQuotientMap_coneMk.restrictPreimage_isOpen hso
  have hinj : Function.Injective (s.restrictPreimage coneMk) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : coneMk a = coneMk b := congrArg Subtype.val hab
    rcases (coneMk_eq_iff a b).mp hab' with h | ⟨h1, -⟩
    · exact Subtype.ext h
    · exact absurd h1 (hmem a ha)
  have hhom : IsHomeomorph (s.restrictPreimage coneMk) :=
    isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hinj⟩
  let φ : X → coneMk ⁻¹' s := fun x => ⟨(x, 1), by
    show coneMk (x, 1) ∈ s
    exact ⟨(x, 1), show ((1 : unitInterval) ≠ 0) from one_ne_zero, rfl⟩⟩
  have hφc : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hφ : IsEmbedding φ :=
    IsEmbedding.of_comp hφc continuous_subtype_val (isEmbedding_prodMkLeft (1 : unitInterval))
  have h2 : IsEmbedding (Subtype.val ∘ (s.restrictPreimage coneMk) ∘ φ) :=
    IsEmbedding.subtypeVal.comp (hhom.isEmbedding.comp hφ)
  exact h2

/-- The equivalence relation generating the suspension: both ends of the cylinder collapsed. -/
def SuspensionRel (X : Type*) (p q : X × unitInterval) : Prop :=
  (p.2 = 0 ∧ q.2 = 0) ∨ (p.2 = 1 ∧ q.2 = 1)

variable (X)

/-- Morris, Topology Without Tears, Definition 11.2.11 (TP-270).  The suspension `SX`: the quotient
of `X × [0,1]` collapsing each of `X × {0}` and `X × {1}` to a point (the book's `CX/(X × {1})`). -/
@[kb "morris2024" "Definition 11.2.11, p. 346"]
abbrev Suspension : Type _ := Quot (SuspensionRel X)

variable {X}

/-- The quotient map `X × [0,1] → SX`. -/
def suspensionMk : X × unitInterval → Suspension X := Quot.mk _

/-- Morris, Topology Without Tears, Definition 11.2.11 (TP-270).  `X × [0,1] → SX` is a quotient
map. -/
@[kb "morris2024" "Definition 11.2.11, p. 346"]
theorem isQuotientMap_suspensionMk : IsQuotientMap (suspensionMk : X × unitInterval → Suspension X) :=
  isQuotientMap_quot_mk

/-- Morris, Topology Without Tears, Definition 11.2.11 (TP-270).  The two ends of the cylinder are
each collapsed to a point. -/
@[kb "morris2024" "Definition 11.2.11, p. 346"]
theorem suspensionMk_eq_of_snd_eq (x x' : X) (a : unitInterval) (ha : a = 0 ∨ a = 1) :
    suspensionMk (x, a) = suspensionMk (x', a) := by
  apply Quot.sound
  rcases ha with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Morris, Topology Without Tears, Definition 11.2.11 (TP-270).  The suspension of a compact space
is compact. -/
@[kb "morris2024" "Definition 11.2.11, p. 346"]
theorem compactSpace_suspension [CompactSpace X] : CompactSpace (Suspension X) := inferInstance

/-- Morris, Topology Without Tears, Definition 11.2.11 (TP-270).  The suspension of a nonempty space
is path connected. -/
@[kb "morris2024" "Definition 11.2.11, p. 346"]
theorem pathConnectedSpace_suspension [Nonempty X] : PathConnectedSpace (Suspension X) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have key : ∀ p : X × unitInterval, Joined (suspensionMk (x₀, 0)) (suspensionMk p) := by
    rintro ⟨x, t⟩
    have h0 : suspensionMk (x₀, 0) = suspensionMk (x, 0) :=
      suspensionMk_eq_of_snd_eq x₀ x 0 (Or.inl rfl)
    rw [h0]
    refine ⟨{ toFun := fun s => suspensionMk (x, s * t)
              continuous_toFun := ?_
              source' := by simp
              target' := by simp }⟩
    exact isQuotientMap_suspensionMk.continuous.comp (by fun_prop)
  refine ⟨⟨suspensionMk (x₀, 0)⟩, fun a b => ?_⟩
  obtain ⟨p, rfl⟩ := isQuotientMap_suspensionMk.surjective a
  obtain ⟨q, rfl⟩ := isQuotientMap_suspensionMk.surjective b
  exact (key p).symm.trans (key q)

end Cone

/-! ### TP-272: Moebius strip, real projective plane, Klein bottle -/

local instance : PathConnectedSpace unitInterval :=
  isPathConnected_iff_pathConnectedSpace.mp ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)

private theorem pathConnectedSpace_quot{α : Type*} [TopologicalSpace α] [PathConnectedSpace α]
    (r : α → α → Prop) : PathConnectedSpace (Quot r) :=
  Function.Surjective.pathConnectedSpace (f := Quot.mk r) (fun q => Quot.exists_rep q)
    continuous_quot_mk

/-- The relation `(t, 0) ∼ (1 - t, 1)` generating the Moebius strip. -/
def MobiusRel (p q : unitInterval × unitInterval) : Prop := p.2 = 0 ∧ q = (σ p.1, 1)

/-- Morris, Topology Without Tears, Example 11.3.3 (TP-272).  The Moebius strip: the quotient of
`I × I` by `(t, 0) ∼ (1 - t, 1)`. -/
@[kb "morris2024" "Example 11.3.3, p. 350"]
abbrev MobiusStrip : Type := Quot MobiusRel

/-- The relation `(0, t) ∼ (1, 1 - t)`, `(t, 0) ∼ (1 - t, 1)` generating the projective plane. -/
def ProjectivePlaneRel (p q : unitInterval × unitInterval) : Prop :=
  (p.1 = 0 ∧ q = (1, σ p.2)) ∨ (p.2 = 0 ∧ q = (σ p.1, 1))

/-- Morris, Topology Without Tears, Example 11.3.4 (TP-272).  The real projective plane `RP²`: the
quotient of `I × I` by `(0, t) ∼ (1, 1 - t)` and `(t, 0) ∼ (1 - t, 1)`. -/
@[kb "morris2024" "Example 11.3.4, p. 351"]
abbrev ProjectivePlane : Type := Quot ProjectivePlaneRel

/-- The relation `(0, t) ∼ (1, t)`, `(t, 0) ∼ (1 - t, 1)` generating the Klein bottle. -/
def KleinRel (p q : unitInterval × unitInterval) : Prop :=
  (p.1 = 0 ∧ q = (1, p.2)) ∨ (p.2 = 0 ∧ q = (σ p.1, 1))

/-- Morris, Topology Without Tears, Example 11.3.5 (TP-272).  The Klein bottle: the quotient of
`I × I` by `(0, t) ∼ (1, t)` and `(t, 0) ∼ (1 - t, 1)`. -/
@[kb "morris2024" "Example 11.3.5, p. 352"]
abbrev KleinBottle : Type := Quot KleinRel

/-- Morris, Topology Without Tears, Example 11.3.3 (TP-272).  In the Moebius strip, `(t, 0)` and
`(1 - t, 1)` are identified. -/
@[kb "morris2024" "Example 11.3.3, p. 350"]
theorem mobius_mk_eq (t : unitInterval) :
    (Quot.mk MobiusRel (t, 0) : MobiusStrip) = Quot.mk MobiusRel (σ t, 1) :=
  Quot.sound ⟨rfl, rfl⟩

/-- Morris, Topology Without Tears, Example 11.3.3 (TP-272).  The Moebius strip is compact and path
connected. -/
@[kb "morris2024" "Example 11.3.3, p. 350"]
theorem compactSpace_pathConnectedSpace_mobiusStrip :
    CompactSpace MobiusStrip ∧ PathConnectedSpace MobiusStrip :=
  ⟨inferInstance, pathConnectedSpace_quot MobiusRel⟩

/-- Morris, Topology Without Tears, Example 11.3.4 (TP-272).  In the real projective plane,
`(0, t) ∼ (1, 1 - t)` and `(t, 0) ∼ (1 - t, 1)`. -/
@[kb "morris2024" "Example 11.3.4, p. 351"]
theorem projectivePlane_mk_eq (t : unitInterval) :
    (Quot.mk ProjectivePlaneRel (0, t) : ProjectivePlane) = Quot.mk ProjectivePlaneRel (1, σ t) ∧
    (Quot.mk ProjectivePlaneRel (t, 0) : ProjectivePlane) = Quot.mk ProjectivePlaneRel (σ t, 1) :=
  ⟨Quot.sound (Or.inl ⟨rfl, rfl⟩), Quot.sound (Or.inr ⟨rfl, rfl⟩)⟩

/-- Morris, Topology Without Tears, Example 11.3.4 (TP-272).  The real projective plane is compact
and path connected. -/
@[kb "morris2024" "Example 11.3.4, p. 351"]
theorem compactSpace_pathConnectedSpace_projectivePlane :
    CompactSpace ProjectivePlane ∧ PathConnectedSpace ProjectivePlane :=
  ⟨inferInstance, pathConnectedSpace_quot ProjectivePlaneRel⟩

/-- Morris, Topology Without Tears, Example 11.3.5 (TP-272).  In the Klein bottle,
`(0, t) ∼ (1, t)` and `(t, 0) ∼ (1 - t, 1)`. -/
@[kb "morris2024" "Example 11.3.5, p. 352"]
theorem kleinBottle_mk_eq (t : unitInterval) :
    (Quot.mk KleinRel (0, t) : KleinBottle) = Quot.mk KleinRel (1, t) ∧
    (Quot.mk KleinRel (t, 0) : KleinBottle) = Quot.mk KleinRel (σ t, 1) :=
  ⟨Quot.sound (Or.inl ⟨rfl, rfl⟩), Quot.sound (Or.inr ⟨rfl, rfl⟩)⟩

/-- Morris, Topology Without Tears, Example 11.3.5 (TP-272).  The Klein bottle is compact and path
connected. -/
@[kb "morris2024" "Example 11.3.5, p. 352"]
theorem compactSpace_pathConnectedSpace_kleinBottle :
    CompactSpace KleinBottle ∧ PathConnectedSpace KleinBottle :=
  ⟨inferInstance, pathConnectedSpace_quot KleinRel⟩

end UndergradKB.Topology
