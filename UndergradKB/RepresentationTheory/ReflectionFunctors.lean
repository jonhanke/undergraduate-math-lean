import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.Roots
import UndergradKB.RepresentationTheory.QuiverExamples
import Mathlib.Data.Fintype.Sigma
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import UndergradKB.Common.Attr

/-! # Reflection functors (Etingof et al., §5.5-5.7)

* Definition 5.25: the quiver `Q_i` obtained by reversing all arrows at the vertex `i` (`reversedAt`).
* Definition 5.26: the reflection functor `F_i^+` at a sink `i`, on objects (`reflectSink`) and on morphisms
  (`reflectSinkMap`): the space at `i` is the kernel of the sum map from the spaces at the sources of the arrows
  entering `i`.
* Definition 5.27: `F_i^-` at a source (`reflectSource`), with the cokernel of the map to the outgoing spaces.
* Proposition 5.28: for an indecomposable `V` and a sink (source) `i`, either `V` is the simple representation at
  `i` or the sum map into `V_i` is surjective (the map out of `V_i` is injective).
* Proposition 5.31: dimension vectors, in the form `d(F_i^+ V) = s_i d(V)` for a quiver whose underlying graph is
  a given simple graph on `Fin n`.
* Lemma 5.33: for a positive definite graph, every nonzero nonnegative vector has a power of the Coxeter element
  with a negative coordinate.
* Example 5.8: every indecomposable representation of `A₂` is isomorphic to `k → 0`, `k → k` or `0 → k`
  (`a2_classification`).

Only the action of the reflection functors on objects is formalized (not on morphisms), and the statements
that `F_i^∓ F_i^±` is the identity and that reflections preserve indecomposables are not included, since they
need an identification of `(Q_i)_i` with `Q`.

To avoid casts, the spaces of the new representation are realised as submodules of a fixed ambient space
`V_x × (product of the incoming (resp. quotient by the outgoing) spaces)`; at the changed vertex `i` the first
factor is zero, elsewhere the second factor is zero.
-/

namespace UndergradKB.RepresentationTheory

open scoped Classical

noncomputable section

universe u v w a

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

/-- The arrows `x ⟶ y` of the quiver with the arrows at `i` reversed: the arrows of `Q` not touching `i`, and the
reversals of the arrows of `Q` that touch `i`. -/
abbrev RevHom (i x y : Q) :=
  PSum {_e : x ⟶ y // x ≠ i ∧ y ≠ i} {_e : y ⟶ x // x = i ∨ y = i}

/-- The quiver `Q_i`: `Q` with all arrows at the vertex `i` reversed (for a sink or a source `i` these are all
the arrows adjacent to `i`; the definition is made for every vertex). -/
@[kb "etingof2011" "Definition 5.25, p. 90"]
abbrev reversedAt (i : Q) : Quiver.{a} Q := ⟨fun x y => RevHom i x y⟩

/-- The type of representations of `Q_i`. -/
abbrev RevRep.{u', v', w', a'} (k : Type u') [Field k] {Q : Type v'} [Quiver.{a'} Q] (i : Q) : Type _ :=
  @QRep.{u', v', w', a'} k Q _ (reversedAt i)

/-- The arrows of `Q` ending at `i`. -/
abbrev InArrows (i : Q) := Σ' j : Q, (j ⟶ i)

/-- The arrows of `Q` starting at `i`. -/
abbrev OutArrows (i : Q) := Σ' j : Q, (i ⟶ j)

/-! ### The reflection functor at a sink -/

section Sink

variable (V : QRep k Q) (i : Q)

/-- The product of the spaces at the sources of the arrows entering `i`. -/
abbrev inProd : Type _ := (e : InArrows i) → V.obj e.1

/-- The sum map `⨁_{j → i} V_j → V_i`. -/
def sumIn [Fintype (InArrows i)] : inProd V i →ₗ[k] V.obj i :=
  ∑ e : InArrows i, (V.map e.2).comp (LinearMap.proj e)

theorem sumIn_apply [Fintype (InArrows i)] (p : inProd V i) : sumIn V i p = ∑ e : InArrows i, V.map e.2 (p e) := by
  simp [sumIn, LinearMap.sum_apply]

/-- The subspace of the ambient space `V_x × ∏ V_j` that is the space at `x` of `F_i^+ V`. -/
def sinkL [Fintype (InArrows i)] (x : Q) : Submodule k (V.obj x × inProd V i) :=
  if x = i then (LinearMap.ker (sumIn V i)).map (LinearMap.inr k (V.obj x) (inProd V i))
  else (⊤ : Submodule k (V.obj x)).map (LinearMap.inl k (V.obj x) (inProd V i))

variable [Fintype (InArrows i)]

theorem mem_sinkL_of_ne {x : Q} (h : x ≠ i) (z : V.obj x × inProd V i) :
    z ∈ sinkL V i x ↔ z.2 = 0 := by
  simp only [sinkL, h, ↓reduceIte, Submodule.mem_map]
  constructor
  · rintro ⟨u, -, rfl⟩; simp
  · intro h2; exact ⟨z.1, trivial, Prod.ext (by simp) (by simp [h2])⟩

theorem mem_sinkL_of_eq {x : Q} (h : x = i) (z : V.obj x × inProd V i) :
    z ∈ sinkL V i x ↔ z.1 = 0 ∧ sumIn V i z.2 = 0 := by
  simp only [sinkL, h, ↓reduceIte, Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩; simpa using hu
  · rintro ⟨h1, h2⟩
    exact ⟨z.2, by simpa using h2, Prod.ext (by simp [h1]) (by simp)⟩

/-- The ambient map for an arrow of `Q` not touching `i`. -/
def sinkKeep {x y : Q} (e : x ⟶ y) : V.obj x × inProd V i →ₗ[k] V.obj y × inProd V i :=
  ((V.map e).comp (LinearMap.fst k _ _)).prod 0

/-- The ambient map for a reversed arrow: the arrow `e : y ⟶ x` of `Q` entering `i = x` becomes `i ⟶ y`, and
the map is the projection to the component of `e`. -/
def sinkRev {x y : Q} (e : y ⟶ x) : V.obj x × inProd V i →ₗ[k] V.obj y × inProd V i :=
  if h : x = i then ((LinearMap.proj (⟨y, h ▸ e⟩ : InArrows i)).comp (LinearMap.snd k _ _)).prod 0
  else 0

theorem sinkKeep_mem {x y : Q} {e : x ⟶ y} (hx : x ≠ i) (hy : y ≠ i) {z : V.obj x × inProd V i}
    (hz : z ∈ sinkL V i x) : sinkKeep V i e z ∈ sinkL V i y := by
  rw [mem_sinkL_of_ne V i hx] at hz
  rw [mem_sinkL_of_ne V i hy]
  simp [sinkKeep]

theorem sinkRev_mem (hi : Quiver.IsSink i) {x y : Q} (e : y ⟶ x) {z : V.obj x × inProd V i}
    (hz : z ∈ sinkL V i x) : sinkRev V i e z ∈ sinkL V i y := by
  by_cases hx : x = i
  · have hy : y ≠ i := by
      intro hy
      exact (hi i).false (cast (by rw [hy, hx]) e)
    rw [mem_sinkL_of_ne V i hy]
    simp [sinkRev, hx]
  · simp only [sinkRev, hx, ↓reduceDIte]
    simp

/-- **The reflection functor `F_i^+`** at a sink `i`, on objects. The space at `i` is the kernel of the sum map
`⨁_{j → i} V_j → V_i`, the other spaces are unchanged, and the arrows at `i` are reversed, the new map
along `i ⟶ j` being the projection of the kernel to the component `V_j`. -/
@[kb "etingof2011" "Definition 5.26, p. 90"]
def reflectSink (hi : Quiver.IsSink i) : RevRep.{u, v, max (max a v) w, a} k i :=
  @QRep.mk k Q _ (reversedAt i) (fun x => ↥(sinkL V i x)) _ _ (fun {x y} e =>
    match e with
    | PSum.inl ⟨e, hx, hy⟩ => (sinkKeep V i e).restrict (fun _ hz => sinkKeep_mem V i hx hy hz)
    | PSum.inr ⟨e, _⟩ => (sinkRev V i e).restrict (fun _ hz => sinkRev_mem V i hi e hz))

end Sink

/-! ### The reflection functor at a source -/

section Source

variable (V : QRep k Q) (i : Q)

/-- The product of the spaces at the targets of the arrows leaving `i`. -/
abbrev outProd : Type _ := (e : OutArrows i) → V.obj e.1

/-- The map `V_i → ⨁_{i → j} V_j` whose components are the maps of the arrows leaving `i`. -/
def outMap : V.obj i →ₗ[k] outProd V i := LinearMap.pi fun e => V.map e.2

theorem outMap_apply (z : V.obj i) (e : OutArrows i) : outMap V i z e = V.map e.2 z := rfl

/-- The cokernel of `V_i → ⨁_{i → j} V_j`. -/
abbrev outCoker : Type _ := outProd V i ⧸ LinearMap.range (outMap V i)

/-- The subspace of the ambient space `V_x × coker` that is the space at `x` of `F_i^- V`. -/
def sourceL (x : Q) : Submodule k (V.obj x × outCoker V i) :=
  if x = i then (⊤ : Submodule k (outCoker V i)).map (LinearMap.inr k (V.obj x) (outCoker V i))
  else (⊤ : Submodule k (V.obj x)).map (LinearMap.inl k (V.obj x) (outCoker V i))

theorem mem_sourceL_of_ne {x : Q} (h : x ≠ i) (z : V.obj x × outCoker V i) :
    z ∈ sourceL V i x ↔ z.2 = 0 := by
  simp only [sourceL, h, ↓reduceIte, Submodule.mem_map]
  constructor
  · rintro ⟨u, -, rfl⟩; simp
  · intro h2; exact ⟨z.1, trivial, Prod.ext (by simp) (by simp [h2])⟩

theorem mem_sourceL_of_eq {x : Q} (h : x = i) (z : V.obj x × outCoker V i) :
    z ∈ sourceL V i x ↔ z.1 = 0 := by
  simp only [sourceL, h, ↓reduceIte, Submodule.mem_map]
  constructor
  · rintro ⟨u, -, rfl⟩; simp
  · intro h1; exact ⟨z.2, trivial, Prod.ext (by simp [h1]) (by simp)⟩

/-- The ambient map for an arrow of `Q` not touching `i`. -/
def sourceKeep {x y : Q} (e : x ⟶ y) : V.obj x × outCoker V i →ₗ[k] V.obj y × outCoker V i :=
  ((V.map e).comp (LinearMap.fst k _ _)).prod 0

/-- The ambient map for a reversed arrow: the arrow `e : i ⟶ x` of `Q` becomes `x ⟶ i`, and the map sends
`u ∈ V_x` to the class of `u` placed in the component of `e`. -/
def sourceRev {x y : Q} (e : y ⟶ x) : V.obj x × outCoker V i →ₗ[k] V.obj y × outCoker V i :=
  if h : y = i then
    (0 : V.obj x × outCoker V i →ₗ[k] V.obj y).prod
      ((Submodule.mkQ (LinearMap.range (outMap V i))).comp
        ((LinearMap.single k (fun e : OutArrows i => V.obj e.1) (⟨x, h ▸ e⟩ : OutArrows i)).comp
          (LinearMap.fst k _ _)))
  else 0

theorem sourceKeep_mem {x y : Q} {e : x ⟶ y} (hx : x ≠ i) (hy : y ≠ i) {z : V.obj x × outCoker V i}
    (hz : z ∈ sourceL V i x) : sourceKeep V i e z ∈ sourceL V i y := by
  rw [mem_sourceL_of_ne V i hx] at hz
  rw [mem_sourceL_of_ne V i hy]
  simp [sourceKeep]

theorem sourceRev_mem {x y : Q} (e : y ⟶ x) {z : V.obj x × outCoker V i}
    (hz : z ∈ sourceL V i x) : sourceRev V i e z ∈ sourceL V i y := by
  by_cases hy : y = i
  · rw [mem_sourceL_of_eq V i hy]
    simp [sourceRev, hy]
  · simp only [sourceRev, hy, ↓reduceDIte]
    simp

/-- **The reflection functor `F_i^-`** at a source `i`, on objects. The space at `i` is the cokernel of
`V_i → ⨁_{i → j} V_j`, the other spaces are unchanged, and the arrows at `i` are reversed. (The hypothesis that
`i` is a source is only needed for the construction to be the book's; the definition does not use it.) -/
@[kb "etingof2011" "Definition 5.27, p. 90"]
def reflectSource (_hi : Quiver.IsSource i) : RevRep.{u, v, max (max a v) w, a} k i :=
  @QRep.mk k Q _ (reversedAt i) (fun x => ↥(sourceL V i x)) _ _ (fun {_ _} e =>
    match e with
    | PSum.inl ⟨e, hx, hy⟩ => (sourceKeep V i e).restrict (fun _ hz => sourceKeep_mem V i hx hy hz)
    | PSum.inr ⟨e, _⟩ => (sourceRev V i e).restrict (fun _ hz => sourceRev_mem V i e hz))

end Source

/-! ### Proposition 5.28: indecomposables at a sink or a source -/

section Prop528

variable (V : QRep k Q) (i : Q)

/-- `V` is the simple representation at `i` (the one-dimensional space at `i`, zero elsewhere): all spaces at the
other vertices vanish and the space at `i` has dimension one. (Since there are no loops at a sink or a source,
the maps are then zero, so this determines `V` up to isomorphism.) -/
def QRep.IsSimpleAt : Prop :=
  (∀ j, j ≠ i → Subsingleton (V.obj j)) ∧ Module.rank k (V.obj i) = 1

theorem bot_eq_top_of_subsingleton' {M : Type*} [AddCommGroup M] [Module k M] [Subsingleton M] :
    (⊥ : Submodule k M) = ⊤ :=
  eq_top_iff.2 fun z _ => by rw [Subsingleton.elim z 0]; exact zero_mem _

theorem isCompl_bot_bot_of_subsingleton {M : Type*} [AddCommGroup M] [Module k M] [Subsingleton M] :
    IsCompl (⊥ : Submodule k M) ⊥ := by
  refine ⟨disjoint_bot_left, ?_⟩
  rw [codisjoint_iff, sup_bot_eq]
  exact bot_eq_top_of_subsingleton'

/-- The subrepresentation with the subspace `p` at `i` and `0` elsewhere (valid when `V` vanishes away from `i`
and there is no loop at `i`). -/
def pointSub (hloop : IsEmpty (i ⟶ i)) (hs : ∀ j, j ≠ i → Subsingleton (V.obj j))
    (p : Submodule k (V.obj i)) : QRep.Subrep V where
  carrier := Function.update (fun x => (⊥ : Submodule k (V.obj x))) i p
  map_mem := by
    intro x y a z hz
    by_cases hx : x = i
    · subst hx
      have hy : y ≠ x := by
        intro hy
        exact hloop.false (cast (by rw [hy]) a)
      have := hs y hy
      rw [Function.update_of_ne hy]
      have : V.map a z = 0 := Subsingleton.elim _ _
      rw [this]
      exact zero_mem _
    · rw [Function.update_of_ne hx] at hz
      have hz0 : z = 0 := by simpa using hz
      rw [hz0, map_zero]
      exact zero_mem _

theorem pointSub_carrier_self (hloop : IsEmpty (i ⟶ i)) (hs : ∀ j, j ≠ i → Subsingleton (V.obj j))
    (p : Submodule k (V.obj i)) : (pointSub V i hloop hs p).carrier i = p :=
  by simp [pointSub]

theorem pointSub_carrier_of_ne (hloop : IsEmpty (i ⟶ i)) (hs : ∀ j, j ≠ i → Subsingleton (V.obj j))
    (p : Submodule k (V.obj i)) {x : Q} (hx : x ≠ i) : (pointSub V i hloop hs p).carrier x = ⊥ :=
  by simp [pointSub, hx]

theorem subsingleton_of_bot_eq_top {M : Type*} [AddCommGroup M] [Module k M]
    (h : (⊥ : Submodule k M) = ⊤) : Subsingleton M :=
  ⟨fun a b => by
    have ha : a ∈ (⊥ : Submodule k M) := by rw [h]; trivial
    have hb : b ∈ (⊥ : Submodule k M) := by rw [h]; trivial
    rw [Submodule.mem_bot] at ha hb
    rw [ha, hb]⟩

/-- An indecomposable representation that vanishes away from `i` (with no loop at `i`) has a one-dimensional
space at `i`; this is the rank-one argument of Example 5.7 transported to a single vertex. -/
theorem rank_eq_one_of_isIndecomposable_of_vanishing (hloop : IsEmpty (i ⟶ i)) (hV : V.IsIndecomposable)
    (hs : ∀ j, j ≠ i → Subsingleton (V.obj j)) : Module.rank k (V.obj i) = 1 := by
  have hnt : Nontrivial (V.obj i) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply hV.1
    apply QRep.Subrep.ext
    intro x
    rw [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier]
    by_cases hx : x = i
    · subst hx; exact bot_eq_top_of_subsingleton'
    · have := hs x hx; exact bot_eq_top_of_subsingleton'
  obtain ⟨v, hv⟩ := exists_ne (0 : V.obj i)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span k {v})
  have hcompl : ∀ x, IsCompl ((pointSub V i hloop hs (Submodule.span k {v})).carrier x)
      ((pointSub V i hloop hs q).carrier x) := by
    intro x
    by_cases hx : x = i
    · subst hx
      rw [pointSub_carrier_self, pointSub_carrier_self]; exact hq
    · rw [pointSub_carrier_of_ne V i hloop hs _ hx, pointSub_carrier_of_ne V i hloop hs _ hx]
      have := hs x hx
      exact isCompl_bot_bot_of_subsingleton
  rw [rank_eq_one_iff]
  refine ⟨v, hv, fun w => ?_⟩
  rcases hV.2 _ _ hcompl with h | h
  · exfalso
    have := congrArg (fun S : QRep.Subrep V => S.carrier i) h
    simp only [pointSub_carrier_self, QRep.Subrep.bot_carrier] at this
    exact hv (by simpa using (Submodule.span_eq_bot.mp this) v (by simp))
  · have h2 := congrArg (fun S : QRep.Subrep V => S.carrier i) h
    simp only [pointSub_carrier_self, QRep.Subrep.bot_carrier] at h2
    have hq' : Submodule.span k {v} = ⊤ := by
      have := hq.sup_eq_top
      rwa [h2, sup_bot_eq] at this
    have hw : w ∈ Submodule.span k {v} := by rw [hq']; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨r, hr⟩

theorem map_mem_range_sumIn [Fintype (InArrows i)] {x : Q} (a : x ⟶ i) (z : V.obj x) :
    V.map a z ∈ LinearMap.range (sumIn V i) :=
  ⟨Pi.single (⟨x, a⟩ : InArrows i) z, by
    rw [sumIn_apply, Finset.sum_eq_single (⟨x, a⟩ : InArrows i)]
    · simp
    · intro e _ he; simp [Pi.single_eq_of_ne he]
    · simp⟩

/-- **Proposition 5.28 (sink).** If `V` is indecomposable and `i` is a sink, then either `V` is the simple
representation at `i`, or the sum map `⨁_{j → i} V_j → V_i` is surjective. -/
@[kb "etingof2011" "Proposition 5.28, p. 90"]
theorem isSimpleAt_or_surjective_sumIn [Fintype (InArrows i)] (hi : Quiver.IsSink i)
    (hV : V.IsIndecomposable) : V.IsSimpleAt i ∨ Function.Surjective (sumIn V i) := by
  by_cases hsurj : Function.Surjective (sumIn V i)
  · exact Or.inr hsurj
  left
  have hloop : IsEmpty (i ⟶ i) := hi i
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (LinearMap.range (sumIn V i))
  let S : QRep.Subrep V :=
    { carrier := Function.update (fun x => (⊤ : Submodule k (V.obj x))) i (LinearMap.range (sumIn V i))
      map_mem := by
        intro x y a z _
        by_cases hx : x = i
        · exact ((hi y).false (cast (by rw [hx]) a)).elim
        · by_cases hy : y = i
          · subst hy
            rw [Function.update_self]
            exact map_mem_range_sumIn V y a z
          · rw [Function.update_of_ne hy]; trivial }
  let T : QRep.Subrep V :=
    { carrier := Function.update (fun x => (⊥ : Submodule k (V.obj x))) i D
      map_mem := by
        intro x y a z hz
        by_cases hx : x = i
        · exact ((hi y).false (cast (by rw [hx]) a)).elim
        · rw [Function.update_of_ne hx] at hz
          have hz0 : z = 0 := by simpa using hz
          rw [hz0, map_zero]
          exact zero_mem _ }
  have hS_i : S.carrier i = LinearMap.range (sumIn V i) :=
    Function.update_self i _ (fun x => (⊤ : Submodule k (V.obj x)))
  have hS_ne : ∀ x, x ≠ i → S.carrier x = ⊤ := fun x hx =>
    Function.update_of_ne hx _ (fun x => (⊤ : Submodule k (V.obj x)))
  have hT_i : T.carrier i = D := Function.update_self i _ (fun x => (⊥ : Submodule k (V.obj x)))
  have hT_ne : ∀ x, x ≠ i → T.carrier x = ⊥ := fun x hx =>
    Function.update_of_ne hx _ (fun x => (⊥ : Submodule k (V.obj x)))
  have hcompl : ∀ x, IsCompl (S.carrier x) (T.carrier x) := by
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hS_i, hT_i]; exact hD
    · rw [hS_ne x hx, hT_ne x hx]
      exact isCompl_top_bot
  rcases hV.2 S T hcompl with h | h
  · have hs : ∀ j, j ≠ i → Subsingleton (V.obj j) := by
      intro j hj
      have := congrArg (fun S : QRep.Subrep V => S.carrier j) h
      simp only [hS_ne j hj, QRep.Subrep.bot_carrier] at this
      exact subsingleton_of_bot_eq_top this.symm
    exact ⟨hs, rank_eq_one_of_isIndecomposable_of_vanishing V i hloop hV hs⟩
  · exfalso
    have := congrArg (fun S : QRep.Subrep V => S.carrier i) h
    simp only [hT_i, QRep.Subrep.bot_carrier] at this
    apply hsurj
    have h2 := hD.sup_eq_top
    rw [this, sup_bot_eq] at h2
    intro y
    have : y ∈ LinearMap.range (sumIn V i) := by rw [h2]; trivial
    exact this

/-- **Proposition 5.28 (source).** If `V` is indecomposable and `i` is a source, then either `V` is the simple
representation at `i`, or the map `V_i → ⨁_{i → j} V_j` is injective. -/
@[kb "etingof2011" "Proposition 5.28, p. 90"]
theorem isSimpleAt_or_injective_outMap (hi : Quiver.IsSource i) (hV : V.IsIndecomposable) :
    V.IsSimpleAt i ∨ Function.Injective (outMap V i) := by
  by_cases hinj : Function.Injective (outMap V i)
  · exact Or.inr hinj
  left
  have hloop : IsEmpty (i ⟶ i) := ⟨fun a => (hi i).false a⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (outMap V i))
  let S : QRep.Subrep V :=
    { carrier := Function.update (fun x => (⊥ : Submodule k (V.obj x))) i (LinearMap.ker (outMap V i))
      map_mem := by
        intro x y a z hz
        by_cases hx : x = i
        · subst hx
          have hy : y ≠ x := by
            intro hy
            exact (hi x).false (cast (by rw [hy]) a)
          rw [Function.update_of_ne hy]
          rw [Function.update_self] at hz
          have := congrFun hz ⟨y, a⟩
          have h0 : V.map a z = 0 := by simpa [outMap_apply] using this
          rw [h0]; exact zero_mem _
        · rw [Function.update_of_ne hx] at hz
          have hz0 : z = 0 := by simpa using hz
          rw [hz0, map_zero]
          exact zero_mem _ }
  let T : QRep.Subrep V :=
    { carrier := Function.update (fun x => (⊤ : Submodule k (V.obj x))) i C
      map_mem := by
        intro x y a z _
        by_cases hy : y = i
        · exact ((hi x).false (cast (by rw [hy]) a)).elim
        · rw [Function.update_of_ne hy]; trivial }
  have hS_i : S.carrier i = LinearMap.ker (outMap V i) :=
    Function.update_self i _ (fun x => (⊥ : Submodule k (V.obj x)))
  have hS_ne : ∀ x, x ≠ i → S.carrier x = ⊥ := fun x hx =>
    Function.update_of_ne hx _ (fun x => (⊥ : Submodule k (V.obj x)))
  have hT_i : T.carrier i = C := Function.update_self i _ (fun x => (⊤ : Submodule k (V.obj x)))
  have hT_ne : ∀ x, x ≠ i → T.carrier x = ⊤ := fun x hx =>
    Function.update_of_ne hx _ (fun x => (⊤ : Submodule k (V.obj x)))
  have hcompl : ∀ x, IsCompl (S.carrier x) (T.carrier x) := by
    intro x
    by_cases hx : x = i
    · subst hx
      rw [hS_i, hT_i]; exact hC
    · rw [hS_ne x hx, hT_ne x hx]
      exact isCompl_bot_top
  rcases hV.2 S T hcompl with h | h
  · exfalso
    have := congrArg (fun S : QRep.Subrep V => S.carrier i) h
    simp only [hS_i, QRep.Subrep.bot_carrier] at this
    exact hinj ((LinearMap.ker_eq_bot).1 this)
  · have hs : ∀ j, j ≠ i → Subsingleton (V.obj j) := by
      intro j hj
      have := congrArg (fun S : QRep.Subrep V => S.carrier j) h
      simp only [hT_ne j hj, QRep.Subrep.bot_carrier] at this
      exact subsingleton_of_bot_eq_top this.symm
    exact ⟨hs, rank_eq_one_of_isIndecomposable_of_vanishing V i hloop hV hs⟩

end Prop528

/-! ### Proposition 5.31: dimension vectors -/

section Dim

/-- The dimension vector of a representation of `Q_i` (the structure projections need the quiver `Q_i` as an
explicit instance, so we spell this out). -/
def RevRep.dimVec {i : Q} (W : RevRep.{u, v, w, a} k i) (x : Q) : ℕ :=
  @QRep.dimVec k Q _ (reversedAt i) W x

variable (V : QRep k Q) (i : Q)

theorem sinkL_of_ne [Fintype (InArrows i)] {x : Q} (h : x ≠ i) :
    sinkL V i x = (⊤ : Submodule k (V.obj x)).map (LinearMap.inl k (V.obj x) (inProd V i)) := by
  simp [sinkL, h]

theorem sinkL_self [Fintype (InArrows i)] :
    sinkL V i i = (LinearMap.ker (sumIn V i)).map (LinearMap.inr k (V.obj i) (inProd V i)) := by
  simp [sinkL]

theorem sourceL_of_ne {x : Q} (h : x ≠ i) :
    sourceL V i x = (⊤ : Submodule k (V.obj x)).map (LinearMap.inl k (V.obj x) (outCoker V i)) := by
  simp [sourceL, h]

theorem sourceL_self :
    sourceL V i i = (⊤ : Submodule k (outCoker V i)).map (LinearMap.inr k (V.obj i) (outCoker V i)) := by
  simp [sourceL]

theorem finrank_sinkL_of_ne [Fintype (InArrows i)] {x : Q} (h : x ≠ i) :
    Module.finrank k (sinkL V i x) = Module.finrank k (V.obj x) := by
  rw [sinkL_of_ne V i h]
  exact LinearEquiv.finrank_eq
    ((Submodule.equivMapOfInjective (LinearMap.inl k (V.obj x) (inProd V i))
      LinearMap.inl_injective ⊤).symm.trans Submodule.topEquiv)

theorem finrank_sinkL_self [Fintype (InArrows i)] :
    Module.finrank k (sinkL V i i) = Module.finrank k (LinearMap.ker (sumIn V i)) := by
  rw [sinkL_self]
  exact LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (LinearMap.inr k (V.obj i) (inProd V i))
      LinearMap.inr_injective _).symm

theorem finrank_sourceL_of_ne {x : Q} (h : x ≠ i) :
    Module.finrank k (sourceL V i x) = Module.finrank k (V.obj x) := by
  rw [sourceL_of_ne V i h]
  exact LinearEquiv.finrank_eq
    ((Submodule.equivMapOfInjective (LinearMap.inl k (V.obj x) (outCoker V i))
      LinearMap.inl_injective ⊤).symm.trans Submodule.topEquiv)

theorem finrank_sourceL_self :
    Module.finrank k (sourceL V i i) = Module.finrank k (outCoker V i) := by
  rw [sourceL_self]
  exact LinearEquiv.finrank_eq
    ((Submodule.equivMapOfInjective (LinearMap.inr k (V.obj i) (outCoker V i))
      LinearMap.inr_injective ⊤).symm.trans Submodule.topEquiv)

/-- At a vertex where the sum map is surjective, the new space at `i` has dimension
`∑_{j → i} dim V_j - dim V_i`, in additive form. -/
theorem finrank_sinkL_self_add [Fintype (InArrows i)] [∀ j, Module.Finite k (V.obj j)]
    (hsurj : Function.Surjective (sumIn V i)) :
    Module.finrank k (sinkL V i i) + Module.finrank k (V.obj i) =
      ∑ e : InArrows i, Module.finrank k (V.obj e.1) := by
  have hp : Module.finrank k (inProd V i) = ∑ e : InArrows i, Module.finrank k (V.obj e.1) :=
    Module.finrank_pi_fintype k
  rw [finrank_sinkL_self, ← hp]
  have h := LinearMap.finrank_range_add_finrank_ker (sumIn V i)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
  omega

/-- At a vertex where the map out of `V_i` is injective, the new space at `i` has dimension
`∑_{i → j} dim V_j - dim V_i`, in additive form. -/
theorem finrank_sourceL_self_add [Fintype (OutArrows i)] [∀ j, Module.Finite k (V.obj j)]
    (hinj : Function.Injective (outMap V i)) :
    Module.finrank k (sourceL V i i) + Module.finrank k (V.obj i) =
      ∑ e : OutArrows i, Module.finrank k (V.obj e.1) := by
  have hp : Module.finrank k (outProd V i) = ∑ e : OutArrows i, Module.finrank k (V.obj e.1) :=
    Module.finrank_pi_fintype k
  rw [finrank_sourceL_self, ← hp]
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (outMap V i))
  rw [LinearMap.finrank_range_of_inj hinj] at h
  exact h

theorem sum_inArrows [Fintype Q] [∀ j, Fintype (j ⟶ i)] (f : Q → ℕ) :
    ∑ e : InArrows i, f e.1 = ∑ j, Fintype.card (j ⟶ i) * f j := by
  calc ∑ e : InArrows i, f e.1 = ∑ s : (j : Q) × (j ⟶ i), f s.1 :=
        Fintype.sum_equiv (Equiv.psigmaEquivSigma _) _ _ (fun _ => rfl)
    _ = ∑ j, ∑ _e : j ⟶ i, f j := Fintype.sum_sigma (fun s : (j : Q) × (j ⟶ i) => f s.1)
    _ = ∑ j, Fintype.card (j ⟶ i) * f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp

theorem sum_outArrows [Fintype Q] [∀ j, Fintype (i ⟶ j)] (f : Q → ℕ) :
    ∑ e : OutArrows i, f e.1 = ∑ j, Fintype.card (i ⟶ j) * f j := by
  calc ∑ e : OutArrows i, f e.1 = ∑ s : (j : Q) × (i ⟶ j), f s.1 :=
        Fintype.sum_equiv (Equiv.psigmaEquivSigma _) _ _ (fun _ => rfl)
    _ = ∑ j, ∑ _e : i ⟶ j, f j := Fintype.sum_sigma (fun s : (j : Q) × (i ⟶ j) => f s.1)
    _ = ∑ j, Fintype.card (i ⟶ j) * f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp

end Dim

/-! ### Proposition 5.31 -/

section Prop531

variable {n : ℕ} [Quiver.{a} (Fin n)] [∀ x y : Fin n, Fintype (x ⟶ y)]
  (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem form_dimVec_simpleRoot (d : Fin n → ℤ) (i : Fin n) :
    Roots.form G d (Roots.simpleRoot i) = 2 * d i - ∑ j, (if G.Adj j i then d j else 0) := by
  rw [Roots.simpleRoot, Roots.form_single_right]
  simp only [Roots.cartanMatrix_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq, mul_comm]

/-- **Proposition 5.31 (sink).** Let `Q` be a quiver on `Fin n` whose underlying graph is `G` (between two
vertices there is exactly one arrow, in one direction, if they are adjacent in `G`, and none otherwise).
If `i` is a sink and `V` is finite dimensional with `⨁_{j → i} V_j → V_i` surjective, then the dimension vector of
`F_i^+ V` is `s_i` applied to that of `V`. -/
@[kb "etingof2011" "Proposition 5.31, p. 93"]
theorem dimVec_reflectSink
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n) (hi : Quiver.IsSink i)
    (hsurj : Function.Surjective (sumIn V i)) :
    (fun x => ((reflectSink V i hi).dimVec x : ℤ)) =
      Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) := by
  have hcard : ∀ j, Fintype.card (j ⟶ i) = if G.Adj j i then 1 else 0 := by
    intro j
    have h0 : Fintype.card (i ⟶ j) = 0 := Fintype.card_eq_zero_iff.2 (hi j)
    simpa [h0] using hG j i
  have key := finrank_sinkL_self_add V i hsurj
  rw [sum_inArrows i (fun j => Module.finrank k (V.obj j))] at key
  simp only [hcard] at key
  have key' : ((reflectSink V i hi).dimVec i : ℤ) + V.dimVec i =
      ∑ j, (if G.Adj j i then (V.dimVec j : ℤ) else 0) := by
    have e : ∀ j, (((if G.Adj j i then 1 else 0) * Module.finrank k (V.obj j) : ℕ) : ℤ) =
        if G.Adj j i then (V.dimVec j : ℤ) else 0 := by
      intro j
      split_ifs <;> simp [QRep.dimVec]
    have := congrArg (Nat.cast : ℕ → ℤ) key
    rw [Nat.cast_sum] at this
    simp only [Nat.cast_add, e] at this
    exact this
  funext x
  rw [Roots.simpleReflection_apply, form_dimVec_simpleRoot G]
  by_cases hx : x = i
  · subst hx
    simp only [Roots.simpleRoot, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    linarith
  · have hd : (reflectSink V i hi).dimVec x = V.dimVec x := finrank_sinkL_of_ne V i hx
    simp [Roots.simpleRoot, Pi.single_apply, hx, hd]

/-- **Proposition 5.31 (source).** Dual statement: if `i` is a source and `V_i → ⨁_{i → j} V_j` is injective, then
the dimension vector of `F_i^- V` is `s_i` applied to that of `V`. -/
@[kb "etingof2011" "Proposition 5.31, p. 93"]
theorem dimVec_reflectSource
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n) (hi : Quiver.IsSource i)
    (hinj : Function.Injective (outMap V i)) :
    (fun x => ((reflectSource V i hi).dimVec x : ℤ)) =
      Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) := by
  have hcard : ∀ j, Fintype.card (i ⟶ j) = if G.Adj j i then 1 else 0 := by
    intro j
    have h0 : Fintype.card (j ⟶ i) = 0 := Fintype.card_eq_zero_iff.2 (hi j)
    simpa [h0, G.adj_comm i j] using hG i j
  have key := finrank_sourceL_self_add V i hinj
  rw [sum_outArrows i (fun j => Module.finrank k (V.obj j))] at key
  simp only [hcard] at key
  have key' : ((reflectSource V i hi).dimVec i : ℤ) + V.dimVec i =
      ∑ j, (if G.Adj j i then (V.dimVec j : ℤ) else 0) := by
    have e : ∀ j, (((if G.Adj j i then 1 else 0) * Module.finrank k (V.obj j) : ℕ) : ℤ) =
        if G.Adj j i then (V.dimVec j : ℤ) else 0 := by
      intro j
      split_ifs <;> simp [QRep.dimVec]
    have := congrArg (Nat.cast : ℕ → ℤ) key
    rw [Nat.cast_sum] at this
    simp only [Nat.cast_add, e] at this
    exact this
  funext x
  rw [Roots.simpleReflection_apply, form_dimVec_simpleRoot G]
  by_cases hx : x = i
  · subst hx
    simp only [Roots.simpleRoot, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    linarith
  · have hd : (reflectSource V i hi).dimVec x = V.dimVec x := finrank_sourceL_of_ne V i hx
    simp [Roots.simpleRoot, Pi.single_apply, hx, hd]

end Prop531

/-! ### Lemma 5.33: powers of the Coxeter element -/

section Coxeter

open Roots

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem prod_simpleReflection_apply_of_notMem (l : List (Fin n)) {j : Fin n} (hj : j ∉ l)
    (w : Fin n → ℤ) : ((l.map (simpleReflection G)).prod w) j = w j := by
  induction l generalizing w with
  | nil => simp
  | cons b l ih =>
    have hb : j ≠ b := fun h => hj (h ▸ List.mem_cons_self)
    have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp, simpleReflection_apply]
    simp [simpleRoot, Pi.single_apply, hb, ih hjl]

/-- If a product of distinct simple reflections fixes `v`, then `v` is `B`-orthogonal to all the corresponding
simple roots (the induction of the book's proof of Lemma 5.33). -/
theorem form_eq_zero_of_prod_fixed (l : List (Fin n)) (hl : l.Nodup) :
    ∀ v : Fin n → ℤ, (l.map (simpleReflection G)).prod v = v → ∀ j ∈ l, form G v (simpleRoot j) = 0 := by
  induction l with
  | nil => intro v _ j hj; simp at hj
  | cons a l ih =>
    intro v hv j hj
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp] at hv
    have hwa := prod_simpleReflection_apply_of_notMem G l ha v
    generalize hw : (l.map (simpleReflection G)).prod v = w at hv hwa
    have h1 : form G w (simpleRoot a) = 0 := by
      have := congrFun hv a
      rw [simpleReflection_apply] at this
      simp only [Pi.sub_apply, Pi.smul_apply, simpleRoot, Pi.single_eq_same, smul_eq_mul,
        mul_one] at this
      unfold simpleRoot
      linarith
    have h2 : w = v := by
      rw [simpleReflection_apply, h1] at hv
      simpa using hv
    rcases List.mem_cons.1 hj with rfl | hj'
    · rw [← h2]; exact h1
    · exact ih hl' v (hw.trans h2) j hj'

/-- For a positive definite graph, `1` is not an eigenvalue of the Coxeter element: a fixed vector is zero
(Lemma 5.33, first part). -/
theorem eq_zero_of_coxeterElement_fixed (hP : PosDefinite G) {v : Fin n → ℤ}
    (hv : coxeterElement G v = v) : v = 0 := by
  have hl := form_eq_zero_of_prod_fixed G (List.finRange n) (List.nodup_finRange n) v
    (by simpa [coxeterElement, List.ofFn_eq_map] using hv)
  by_contra hne
  have hpos := hP.form_pos hne
  have hsum : form G v v = ∑ j, v j * form G v (simpleRoot j) := by
    simp only [simpleRoot, form_single_right]
    rw [form_eq_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, Finset.sum_eq_zero] at hpos
  · exact lt_irrefl _ hpos
  · intro j _
    rw [hl j (List.mem_finRange j), mul_zero]

theorem coxeterElement_mem_weylGroup : coxeterElement G ∈ weylGroup G := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact Subgroup.subset_closure ⟨j, rfl⟩

/-- **Lemma 5.33.** For a positive definite graph, if `β` is a nonzero vector with nonnegative coordinates, then
some power `c^N β` of the Coxeter element has a strictly negative coordinate. The proof follows the book:
the Coxeter element has finite order `m`, so `∑_{N<m} c^N β` is fixed by `c`, hence zero, which is impossible if
all the terms are nonnegative and `β ≠ 0`. -/
@[kb "etingof2011" "Lemma 5.33, p. 93"]
theorem exists_pow_coxeterElement_neg (hP : PosDefinite G) {β : Fin n → ℤ} (hβ0 : β ≠ 0)
    (hβ : ∀ i, 0 ≤ β i) : ∃ N : ℕ, ∃ i, (coxeterElement G ^ N) β i < 0 := by
  by_contra hcon
  push Not at hcon
  haveI := weylGroup_finite G hP
  set c := coxeterElement G with hc
  let c' : weylGroup G := ⟨c, coxeterElement_mem_weylGroup G⟩
  have hm : 0 < orderOf c' := orderOf_pos c'
  set m := orderOf c' with hmdef
  have hcm : c ^ m = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one c')
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  set γ : Fin n → ℤ := ∑ N ∈ Finset.range m, (c ^ N) β with hγ
  have hfix : c γ = γ := by
    rw [hγ, map_sum]
    have h1 : ∑ N ∈ Finset.range m, c ((c ^ N) β) = ∑ N ∈ Finset.range m, (c ^ (N + 1)) β := by
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [pow_succ', mul_apply_eq_comp]
    rw [h1]
    have h2 := Finset.sum_range_succ (fun N => (c ^ N) β) m
    have h3 := Finset.sum_range_succ' (fun N => (c ^ N) β) m
    beta_reduce at h2 h3
    have h0 : (c ^ 0) β = β := by rw [pow_zero]; rfl
    have h1' : (c ^ m) β = β := by rw [hcm]; rfl
    rw [h1'] at h2
    rw [h0] at h3
    exact add_right_cancel (h3.symm.trans h2)
  have hγ0 : γ = 0 := eq_zero_of_coxeterElement_fixed G hP hfix
  obtain ⟨i, hi⟩ : ∃ i, 0 < β i := by
    by_contra h
    push Not at h
    exact hβ0 (funext fun i => le_antisymm (h i) (hβ i))
  have hle : β i ≤ γ i := by
    have : (c ^ 0) β i ≤ γ i := by
      rw [hγ, Finset.sum_apply]
      exact Finset.single_le_sum (f := fun N => (c ^ N) β i) (fun N _ => hcon N i) (Finset.mem_range.2 hm)
    simpa using this
  rw [hγ0] at hle
  simp at hle
  omega

end Coxeter

/-! ### Example 5.8: classification of the indecomposable representations of `A₂` -/

section A2

/-- The arrow of `A₂`. -/
def a2arr : A2V.src ⟶ A2V.tgt := A2Arrow.arr

/-- A subrepresentation of a representation of `A₂`, given by its two subspaces. -/
def a2Sub (V : QRep.{u, 0, u, 0} k A2V) (p : Submodule k (V.obj A2V.src)) (q : Submodule k (V.obj A2V.tgt))
    (h : ∀ z ∈ p, V.map a2arr z ∈ q) : QRep.Subrep V where
  carrier := fun x => match x with
    | A2V.src => p
    | A2V.tgt => q
  map_mem := by
    intro x y a z hz
    cases a
    exact h z hz

theorem a2Sub_isCompl (V : QRep.{u, 0, u, 0} k A2V) {p p' : Submodule k (V.obj A2V.src)}
    {q q' : Submodule k (V.obj A2V.tgt)} (h : ∀ z ∈ p, V.map a2arr z ∈ q)
    (h' : ∀ z ∈ p', V.map a2arr z ∈ q') (hp : IsCompl p p') (hq : IsCompl q q') :
    ∀ x, IsCompl ((a2Sub V p q h).carrier x) ((a2Sub V p' q' h').carrier x) := by
  intro x
  cases x
  · exact hp
  · exact hq

theorem a2Sub_eq_bot (V : QRep.{u, 0, u, 0} k A2V) {p : Submodule k (V.obj A2V.src)}
    {q : Submodule k (V.obj A2V.tgt)} (h : ∀ z ∈ p, V.map a2arr z ∈ q) (hS : (a2Sub V p q h) = ⊥) :
    p = ⊥ ∧ q = ⊥ :=
  ⟨congrArg (fun S : QRep.Subrep V => S.carrier A2V.src) hS,
    congrArg (fun S : QRep.Subrep V => S.carrier A2V.tgt) hS⟩

/-- Two representations of `A₂` are isomorphic when linear equivalences of the two spaces intertwine the maps. -/
theorem a2_isomorphic_of_equiv {V V' : QRep.{u, 0, u, 0} k A2V} (eU : V.obj A2V.src ≃ₗ[k] V'.obj A2V.src)
    (eW : V.obj A2V.tgt ≃ₗ[k] V'.obj A2V.tgt) (h : ∀ z, eW (V.map a2arr z) = V'.map a2arr (eU z)) :
    QRep.Isomorphic V V' := by
  refine ⟨⟨fun x => match x with
      | A2V.src => eU.toLinearMap
      | A2V.tgt => eW.toLinearMap, ?_⟩,
    ⟨fun x => match x with
      | A2V.src => eU.symm.toLinearMap
      | A2V.tgt => eW.symm.toLinearMap, ?_⟩, ?_, ?_⟩
  · intro x y a
    cases a
    exact LinearMap.ext fun z => h z
  · intro x y a
    cases a
    refine LinearMap.ext fun z => ?_
    show eW.symm (V'.map a2arr z) = V.map a2arr (eU.symm z)
    rw [LinearEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]
  · refine QRep.Hom.ext fun x => ?_
    cases x <;> exact LinearMap.ext fun z => by simp
  · refine QRep.Hom.ext fun x => ?_
    cases x <;> exact LinearMap.ext fun z => by simp

theorem isCompl_map_of_bijective {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (hb : Function.Bijective f) {p q : Submodule k M} (h : IsCompl p q) :
    IsCompl (p.map f) (q.map f) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro y hy hy'
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨b, hb', hab⟩ := Submodule.mem_map.1 hy'
    have : b = a := hb.1 hab
    subst this
    have := Submodule.disjoint_def.1 h.disjoint b ha hb'
    simp [this]
  · rw [codisjoint_iff, ← Submodule.map_sup, h.sup_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hb.2]

theorem a2_rank_eq_one_of_bijective (V : QRep.{u, 0, u, 0} k A2V) (hV : V.IsIndecomposable)
    (hb : Function.Bijective (V.map a2arr)) : Module.rank k (V.obj A2V.src) = 1 := by
  have hnt : Nontrivial (V.obj A2V.src) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have hW : Subsingleton (V.obj A2V.tgt) := hb.2.subsingleton
    apply hV.1
    apply QRep.Subrep.ext
    intro x
    rw [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier]
    cases x
    · exact bot_eq_top_of_subsingleton'
    · exact bot_eq_top_of_subsingleton'
  obtain ⟨v, hv⟩ := exists_ne (0 : V.obj A2V.src)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span k {v})
  have hS : ∀ z ∈ Submodule.span k {v}, V.map a2arr z ∈ (Submodule.span k {v}).map (V.map a2arr) :=
    fun z hz => Submodule.mem_map_of_mem hz
  have hT : ∀ z ∈ q, V.map a2arr z ∈ q.map (V.map a2arr) := fun z hz => Submodule.mem_map_of_mem hz
  have hcompl := a2Sub_isCompl V hS hT hq (isCompl_map_of_bijective _ hb hq)
  rw [rank_eq_one_iff]
  refine ⟨v, hv, fun w => ?_⟩
  rcases hV.2 _ _ hcompl with h | h
  · exfalso
    have := (a2Sub_eq_bot V hS h).1
    exact hv (by simpa using (Submodule.span_eq_bot.mp this) v (by simp))
  · have h2 := (a2Sub_eq_bot V hT h).1
    have hq' : Submodule.span k {v} = ⊤ := by
      have := hq.sup_eq_top
      rwa [h2, sup_bot_eq] at this
    have hw : w ∈ Submodule.span k {v} := by rw [hq']; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨r, hr⟩

/-- **Example 5.8.** Every indecomposable representation of the quiver `A₂` is isomorphic to one of `k → 0`,
`k → k` (identity), `0 → k`. Together with `A2Rep.pairwise_not_isomorphic` and the indecomposability of these
three, `A₂` has exactly three indecomposable representations up to isomorphism. (No finite-dimensionality is
needed.) -/
@[kb "etingof2011" "Example 5.8, p. 81"]
theorem a2_classification (V : QRep.{u, 0, u, 0} k A2V) (hV : V.IsIndecomposable) :
    QRep.Isomorphic V (A2Rep.kToZero k) ∨ QRep.Isomorphic V (A2Rep.kToK k) ∨
      QRep.Isomorphic V (A2Rep.zeroToK k) := by
  have hloop_src : IsEmpty (A2V.src ⟶ A2V.src) := ⟨fun a => by cases a⟩
  have hloop_tgt : IsEmpty (A2V.tgt ⟶ A2V.tgt) := ⟨fun a => by cases a⟩
  set f := V.map a2arr with hf
  -- first splitting: kernel and a complement
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hS1 : ∀ z ∈ LinearMap.ker f, V.map a2arr z ∈ (⊥ : Submodule k (V.obj A2V.tgt)) :=
    fun z hz => hz
  have hT1 : ∀ z ∈ C, V.map a2arr z ∈ (⊤ : Submodule k (V.obj A2V.tgt)) := fun _ _ => trivial
  rcases hV.2 _ _ (a2Sub_isCompl V hS1 hT1 hC isCompl_bot_top) with h1 | h1
  · -- the map is injective: second splitting, image and a complement
    have hker : LinearMap.ker f = ⊥ := (a2Sub_eq_bot V hS1 h1).1
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hker
    obtain ⟨D, hD⟩ := Submodule.exists_isCompl (LinearMap.range f)
    have hS2 : ∀ z ∈ (⊤ : Submodule k (V.obj A2V.src)), V.map a2arr z ∈ LinearMap.range f :=
      fun z _ => ⟨z, rfl⟩
    have hT2 : ∀ z ∈ (⊥ : Submodule k (V.obj A2V.src)), V.map a2arr z ∈ D := by
      intro z hz
      rw [Submodule.mem_bot] at hz
      rw [hz, map_zero]
      exact zero_mem _
    rcases hV.2 _ _ (a2Sub_isCompl V hS2 hT2 isCompl_top_bot hD) with h2 | h2
    · -- the representation is `0 → k`
      have hU : Subsingleton (V.obj A2V.src) := subsingleton_of_bot_eq_top (a2Sub_eq_bot V hS2 h2).1.symm
      have hs : ∀ j, j ≠ A2V.tgt → Subsingleton (V.obj j) := by
        intro j hj
        cases j
        · exact hU
        · exact absurd rfl hj
      have hrank := rank_eq_one_of_isIndecomposable_of_vanishing V A2V.tgt hloop_tgt hV hs
      right; right
      have eW := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
      have : Subsingleton ((A2Rep.zeroToK k).obj A2V.src) := inferInstanceAs (Subsingleton PUnit.{u + 1})
      refine a2_isomorphic_of_equiv (LinearEquiv.ofSubsingleton _ _) eW fun z => ?_
      have hz : z = 0 := Subsingleton.elim _ _
      subst hz
      show eW (V.map a2arr 0) = (0 : PUnit.{u + 1} →ₗ[k] k) _
      rw [map_zero, map_zero]
      rfl
    · -- the representation is `k → k`
      have hD : D = ⊥ := (a2Sub_eq_bot V hT2 h2).2
      have hsurj : Function.Surjective f := by
        have h3 := hD
        have := hD
        rw [← LinearMap.range_eq_top]
        have h4 := (‹IsCompl (LinearMap.range f) D›).sup_eq_top
        rwa [hD, sup_bot_eq] at h4
      have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
      have hrank := a2_rank_eq_one_of_bijective V hV hbij
      right; left
      have eU := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
      refine a2_isomorphic_of_equiv eU ((LinearEquiv.ofBijective f hbij).symm.trans eU) fun z => ?_
      show ((LinearEquiv.ofBijective f hbij).symm.trans eU) (V.map a2arr z) = (LinearMap.id : k →ₗ[k] k) (eU z)
      have h : (LinearEquiv.ofBijective f hbij).symm (V.map a2arr z) = z :=
        (LinearEquiv.symm_apply_eq _).2 rfl
      rw [LinearEquiv.trans_apply, h]
      rfl
  · -- the map is zero and the target vanishes: `k → 0`
    have hW : Subsingleton (V.obj A2V.tgt) := subsingleton_of_bot_eq_top (a2Sub_eq_bot V hT1 h1).2.symm
    have hs : ∀ j, j ≠ A2V.src → Subsingleton (V.obj j) := by
      intro j hj
      cases j
      · exact absurd rfl hj
      · exact hW
    have hrank := rank_eq_one_of_isIndecomposable_of_vanishing V A2V.src hloop_src hV hs
    left
    have eU := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
    have : Subsingleton ((A2Rep.kToZero k).obj A2V.tgt) := inferInstanceAs (Subsingleton PUnit.{u + 1})
    exact a2_isomorphic_of_equiv eU (LinearEquiv.ofSubsingleton _ _) fun z => Subsingleton.elim _ _

end A2

end

end UndergradKB.RepresentationTheory
