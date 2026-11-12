import UndergradKB.RepresentationTheory.ReflectionFunctorsMore
import UndergradKB.Common.Attr

/-! # Reflection functors: `F_i^-` is left adjoint to `F_i^+` (Etingof et al., exercise after §5.7)

Let `i` be a source of `Q`, so that `i` is a sink of `Q_i`, and let `V` be a representation of `Q` and `W` one of
`Q_i`. The reflection functor `F_i^-` sends `V` to a representation of `Q_i` (`reflectSource`) and `F_i^+` sends
`W` to a representation of `(Q_i)_i` (`reflectSink`). Since `(Q_i)_i` is only identified with `Q` on arrows through
`toRR`, a morphism `V → F_i^+ W` is expressed as a family of linear maps compatible with the arrows of `Q` after
this identification (`RevRevHom`, the analogue of `RevRevIso`).

* `adjFwd`, `adjBwd`: the two constructions. Forward, a morphism `g : F_i^- V → W` gives at `x ≠ i` the map
  `V_x → W_x` obtained from `g_x`, and at `i` the map `V_i → ⨁ W_j` whose `j`-th component is `g_j` applied to the
  image of the arrow `i → j` (it lands in the kernel of the sum map because the class of an image of `V_i` is zero
  in the cokernel). Backward, a morphism `h : V → F_i^+ W` gives the map out of the cokernel induced by the
  components of `h` and the arrows of `Q_i` into `i`.
* `adjBwd_adjFwd`, `adjFwd_adjBwd`: the two constructions are mutually inverse.
* `reflectAdjEquiv`: the resulting bijection between morphisms `F_i^- V → W` of representations of `Q_i` and
  `RevRevHom`s `V → F_i^+ W`.
* `reflectAdjEquiv_postcomp`, `reflectAdjEquiv_precomp`: naturality of the bijection in `W` (composition with a
  morphism of representations of `Q_i`, transported by `F_i^+`, i.e. `reflectSinkMap`) and in `V` (composition
  with a morphism of representations of `Q`, transported by `F_i^-`, i.e. `reflectSourceMap`). The composition
  operations on `RevRevHom` are `RevRevHom.postcomp` and `RevRevHom.precomp`.

The exactness consequences (`F_i^+` left exact and `F_i^-` right exact) are not formalized.
-/

namespace UndergradKB.RepresentationTheory

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

universe u v w w' a

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

/-! ### Notation for representations of `Q_i` -/

/-- The space at the vertex `x` of a representation of `Q_i`. -/
abbrev adjObj {i : Q} (W : RevRep.{u, v, w', a} k i) (x : Q) : Type w' := @QRep.obj k Q _ (reversedAt i) W x

/-- The linear map of an arrow of `Q_i` in a representation of `Q_i`. -/
abbrev adjMap {i : Q} (W : RevRep.{u, v, w', a} k i) {x y : Q} (b : @Quiver.Hom Q (reversedAt i) x y) :
    adjObj W x →ₗ[k] adjObj W y :=
  @QRep.map k Q _ (reversedAt i) W x y b

/-- The component at `x` of a morphism of representations of `Q_i`. -/
abbrev adjApp {i : Q} {W W' : RevRep.{u, v, w', a} k i} (g : RevRep.Hom W W') (x : Q) :
    adjObj W x →ₗ[k] adjObj W' x :=
  @QRep.Hom.app k Q _ (reversedAt i) W W' g x

theorem adj_comm {i : Q} {W W' : RevRep.{u, v, w', a} k i} (g : RevRep.Hom W W') {x y : Q}
    (b : @Quiver.Hom Q (reversedAt i) x y) (z : adjObj W x) :
    adjApp g y (adjMap W b z) = adjMap W' b (adjApp g x z) :=
  LinearMap.congr_fun (@QRep.Hom.comm k Q _ (reversedAt i) W W' g x y b) z

/-- The product of the spaces at the sources of the arrows of `Q_i` entering `i`. -/
abbrev adjInProd {i : Q} (W : RevRep.{u, v, w', a} k i) : Type _ := @inProd k _ Q (reversedAt i) W i

/-- The ambient subspace at `x` for `F_i^+ W`, where `W` is a representation of `Q_i`. -/
abbrev adjSinkL {i : Q} [Fintype (OutArrows i)] (W : RevRep.{u, v, w', a} k i) (x : Q) :
    Submodule k (adjObj W x × adjInProd W) :=
  @sinkL k _ Q (reversedAt i) W i (fintypeInArrowsRev i) x

/-- The sum map into `W_i` of a representation of `Q_i`. -/
abbrev adjSumIn {i : Q} [Fintype (OutArrows i)] (W : RevRep.{u, v, w', a} k i) :
    adjInProd W →ₗ[k] adjObj W i :=
  @sumIn k _ Q (reversedAt i) W i (fintypeInArrowsRev i)

/-- `F_i^+ W` for a representation `W` of `Q_i` (a representation of `(Q_i)_i`), for a source `i` of `Q`. -/
abbrev adjSink {i : Q} [Fintype (OutArrows i)] (hi : Quiver.IsSource i) (W : RevRep.{u, v, w', a} k i) :=
  @reflectSink k _ Q (reversedAt i) W i (fintypeInArrowsRev i) (isSink_reversedAt hi)

theorem adj_mem_sinkL_of_ne {i : Q} [Fintype (OutArrows i)] (W : RevRep.{u, v, w', a} k i) {x : Q}
    (h : x ≠ i) (z : adjObj W x × adjInProd W) : z ∈ adjSinkL W x ↔ z.2 = 0 :=
  @mem_sinkL_of_ne k _ Q (reversedAt i) W i (fintypeInArrowsRev i) x h z

theorem adj_mem_sinkL_of_eq {i : Q} [Fintype (OutArrows i)] (W : RevRep.{u, v, w', a} k i) {x : Q}
    (h : x = i) (z : adjObj W x × adjInProd W) : z ∈ adjSinkL W x ↔ z.1 = 0 ∧ adjSumIn W z.2 = 0 :=
  @mem_sinkL_of_eq k _ Q (reversedAt i) W i (fintypeInArrowsRev i) x h z

/-- The arrow `i ⟶ j` of `Q` underlying an arrow `j ⟶ i` of `Q_i`. -/
def arrOfRev {i j : Q} (b : @Quiver.Hom Q (reversedAt i) j i) : i ⟶ j :=
  match b with
  | PSum.inl ⟨_, _, h2⟩ => (h2 rfl).elim
  | PSum.inr ⟨a, _⟩ => a

/-! ### Morphisms from a representation of `Q` to a reflected representation -/

/-- A morphism from a representation `V` of `Q` to a representation `X` of `(Q_i)_i`, where the arrows of `Q` are
identified with those of `(Q_i)_i` by `toRR`: linear maps `V_x → X_x` compatible with the arrows. -/
structure RevRevHom (V : QRep.{u, v, w, a} k Q) {i : Q} (X : @QRep.{u, v, w', a} k Q _ (revrev i)) where
  /-- The component at each vertex. -/
  app : ∀ x : Q, V.obj x →ₗ[k] @QRep.obj k Q _ (revrev i) X x
  /-- Compatibility with every arrow of `Q`. -/
  comm : ∀ {x y : Q} (b : x ⟶ y) (z : V.obj x),
    app y (V.map b z) = @QRep.map k Q _ (revrev i) X x y (toRR i b) (app x z)

theorem RevRevHom.ext {V : QRep.{u, v, w, a} k Q} {i : Q} {X : @QRep.{u, v, w', a} k Q _ (revrev i)}
    {f g : RevRevHom V X} (h : ∀ x, f.app x = g.app x) : f = g := by
  cases f; cases g
  congr
  exact funext h

section Basic

variable (V : QRep.{u, v, w, a} k Q) (i : Q)

/-- The embedding `V_x → V_x × coker`, landing in the space at `x ≠ i` of `F_i^- V`. -/
def adjIn {x : Q} (hx : x ≠ i) : V.obj x →ₗ[k] sourceL V i x :=
  LinearMap.codRestrict _ (LinearMap.inl k (V.obj x) (outCoker V i))
    fun _ => (mem_sourceL_of_ne V i hx _).2 rfl

theorem adjIn_val {x : Q} (hx : x ≠ i) (u : V.obj x) : (adjIn V i hx u).1 = (u, 0) := rfl

/-- The element of the space at `i` of `F_i^- V` given by a class in the cokernel. -/
def adjCoker (c : outCoker V i) : sourceL V i i := ⟨(0, c), (mem_sourceL_of_eq V i rfl _).2 rfl⟩

theorem adjCoker_val (c : outCoker V i) : (adjCoker V i c).1 = (0, c) := rfl

end Basic

section Fwd

variable {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (OutArrows i)] {hi : Quiver.IsSource i}
  {W : RevRep.{u, v, max (max a v) w, a} k i} (g : RevRep.Hom (reflectSource V i hi) W)

/-- The image in the space at `i` of `F_i^- V` of `p_o` placed in the summand of the arrow `o`. -/
def adjRevTerm (V : QRep.{u, v, w, a} k Q) (i : Q) (hi : Quiver.IsSource i) (p : outProd V i) (o : OutArrows i) :
    sourceL V i i :=
  adjMap (reflectSource V i hi) (revInOfOut i o).2 (adjIn V i (ne_of_arrow_source hi o.2) (p o))

theorem adjRevTerm_val (V : QRep.{u, v, w, a} k Q) (i : Q) (hi : Quiver.IsSource i) (p : outProd V i)
    (o : OutArrows i) :
    (adjRevTerm V i hi p o).1 = (0, Submodule.mkQ (LinearMap.range (outMap V i)) (Pi.single o (p o))) :=
  sourceMap_revOut hi o.2 _

theorem adjCoker_eq_sum (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)] (hi : Quiver.IsSource i)
    (p : outProd V i) :
    adjCoker V i (Submodule.mkQ (LinearMap.range (outMap V i)) p) = ∑ o : OutArrows i, adjRevTerm V i hi p o := by
  refine Subtype.ext ?_
  rw [Submodule.coe_sum]
  simp only [adjRevTerm_val, adjCoker_val]
  refine Prod.ext (by simp [Prod.fst_sum]) ?_
  simp only [Prod.snd_sum]
  rw [← map_sum]
  congr 1
  exact (Finset.univ_sum_single p).symm

theorem adj_keyA (p : outProd V i) :
    adjApp g i (adjCoker V i (Submodule.mkQ (LinearMap.range (outMap V i)) p)) =
      ∑ o : OutArrows i, adjMap W (revInOfOut i o).2
        (adjApp g o.1 (adjIn V i (ne_of_arrow_source hi o.2) (p o))) := by
  rw [adjCoker_eq_sum V i hi p]
  refine (map_sum (adjApp g i) (fun o => (adjRevTerm V i hi p o : adjObj (reflectSource V i hi) i))
    Finset.univ).trans ?_
  exact Finset.sum_congr rfl fun o _ => adj_comm g _ _

theorem adjSumIn_eq (W : RevRep.{u, v, w', a} k i) (p : adjInProd W) :
    adjSumIn W p = ∑ o : OutArrows i, adjMap W (revInOfOut i o).2 (p (revInOfOut i o)) := by
  have hsum := @sumIn_apply k _ Q (reversedAt i) W i (fintypeInArrowsRev i) p
  have hbij : Function.Bijective (revInOfOut i) := ⟨revInOfOut_injective i, revInOfOut_surjective i⟩
  refine hsum.trans ?_
  exact (Fintype.sum_bijective (revInOfOut i) hbij
    (fun o : OutArrows i => adjMap W (revInOfOut i o).2 (p (revInOfOut i o)))
    (fun e : @InArrows Q (reversedAt i) i => adjMap W e.2 (p e)) (fun _ => rfl)).symm

theorem adj_sum_eq_zero (g : RevRep.Hom (reflectSource V i hi) W) (u : V.obj i) :
    ∑ o : OutArrows i, adjMap W (revInOfOut i o).2
      (adjApp g o.1 (adjIn V i (ne_of_arrow_source hi o.2) (V.map o.2 u))) = 0 := by
  have h := adj_keyA g (outMap V i u)
  have h0 : Submodule.mkQ (LinearMap.range (outMap V i)) (outMap V i u) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨u, rfl⟩
  have h1 : adjCoker V i (Submodule.mkQ (LinearMap.range (outMap V i)) (outMap V i u)) = 0 := by
    rw [h0]; rfl
  rw [h1] at h
  exact h.symm.trans (adjApp g i).map_zero

/-- The component at a vertex `x` of the map `V_i → ⨁_{j → i in Q_i} W_j` used for the space at `i` (zero for
`x ≠ i`). -/
def adjFwdPi (g : RevRep.Hom (reflectSource V i hi) W) : V.obj i →ₗ[k] adjInProd W :=
  LinearMap.pi fun e : @InArrows Q (reversedAt i) i =>
    (adjApp g e.1).comp ((adjIn V i (ne_of_arrow_source hi (arrOfRev e.2))).comp (V.map (arrOfRev e.2)))

theorem adjFwdPi_apply (g : RevRep.Hom (reflectSource V i hi) W) (u : V.obj i) (e : @InArrows Q (reversedAt i) i) :
    adjFwdPi g u e = adjApp g e.1 (adjIn V i (ne_of_arrow_source hi (arrOfRev e.2)) (V.map (arrOfRev e.2) u)) := rfl

theorem adjFwdPi_sum (g : RevRep.Hom (reflectSource V i hi) W) (u : V.obj i) :
    adjSumIn W (adjFwdPi g u) = 0 := by
  rw [adjSumIn_eq]
  exact adj_sum_eq_zero g u

end Fwd

section Fwd2

variable {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (OutArrows i)] {hi : Quiver.IsSource i}
  {W : RevRep.{u, v, max (max a v) w, a} k i}

theorem adjIn_map_keep (hi : Quiver.IsSource i) {x y : Q} (b : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i) (z : V.obj x) :
    adjMap (reflectSource V i hi) (PSum.inl ⟨b, hx, hy⟩) (adjIn V i hx z) = adjIn V i hy (V.map b z) :=
  Subtype.ext (sourceMap_keep hi b hx hy _)

theorem adjSink_map_keep (hi : Quiver.IsSource i) {x y : Q} (b : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i)
    (z : adjSinkL W x) :
    (@QRep.map k Q _ (revrev i) (adjSink hi W) x y (toRR i b) z).1 =
      (adjMap W (PSum.inl ⟨b, hx, hy⟩) z.1.1, 0) := by
  rw [toRR_of_ne b hx hy]
  exact @sinkMap_keep k _ Q (reversedAt i) W i (fintypeInArrowsRev i) (isSink_reversedAt hi) x y
    (PSum.inl ⟨b, hx, hy⟩) hx hy z

theorem adjSink_map_from (hi : Quiver.IsSource i) {j : Q} (b : i ⟶ j) (z : adjSinkL W i) :
    (@QRep.map k Q _ (revrev i) (adjSink hi W) i j (toRR i b) z).1 =
      (z.1.2 (revInOfOut i ⟨j, b⟩), 0) := by
  rw [toRR_of_eq_left b rfl]
  exact @sinkMap_revIn k _ Q (reversedAt i) W i (fintypeInArrowsRev i) (isSink_reversedAt hi) j
    (PSum.inr ⟨b, Or.inr rfl⟩) z

variable (g : RevRep.Hom (reflectSource V i hi) W)

/-- The first component of the morphism `V → F_i^+ W` attached to `g`: `g` on the summand `V_x` for `x ≠ i`, zero
at `i`. -/
def adjFwdFst (x : Q) : V.obj x →ₗ[k] adjObj W x :=
  if hx : x = i then 0 else (adjApp g x).comp (adjIn V i hx)

/-- The second component: zero for `x ≠ i`, and at `i` the map `V_i → ⨁_{j → i in Q_i} W_j` with components
`g_j` composed with the maps of the arrows leaving `i`. -/
def adjFwdSnd (x : Q) : V.obj x →ₗ[k] adjInProd W :=
  if h : i = x then by subst h; exact adjFwdPi g else 0

theorem adjFwdFst_of_ne {x : Q} (hx : x ≠ i) : adjFwdFst g x = (adjApp g x).comp (adjIn V i hx) :=
  by simp [adjFwdFst, hx]

theorem adjFwdFst_self : adjFwdFst g i = 0 := by simp [adjFwdFst]

theorem adjFwdSnd_of_ne {x : Q} (hx : x ≠ i) : adjFwdSnd g x = 0 := by
  have : ¬ i = x := fun h => hx h.symm
  simp [adjFwdSnd, this]

theorem adjFwdSnd_self : adjFwdSnd g i = adjFwdPi g := by simp [adjFwdSnd]

/-- The ambient linear map of the morphism `V → F_i^+ W` attached to `g`. -/
def adjFwdAmb (x : Q) : V.obj x →ₗ[k] adjObj W x × adjInProd W :=
  (adjFwdFst g x).prod (adjFwdSnd g x)

theorem adjFwdAmb_mem (x : Q) (u : V.obj x) : adjFwdAmb g x u ∈ adjSinkL W x := by
  by_cases hx : x = i
  · subst hx
    refine (adj_mem_sinkL_of_eq W rfl _).2 ⟨?_, ?_⟩
    · show adjFwdFst g x u = 0
      rw [adjFwdFst_self]; rfl
    · show adjSumIn W (adjFwdSnd g x u) = 0
      rw [adjFwdSnd_self]
      exact adjFwdPi_sum g u
  · refine (adj_mem_sinkL_of_ne W hx _).2 ?_
    show adjFwdSnd g x u = 0
    rw [adjFwdSnd_of_ne g hx]; rfl

theorem adjFwdAmb_comm {x y : Q} (b : x ⟶ y) (z : V.obj x) :
    adjFwdAmb g y (V.map b z) =
      (@QRep.map k Q _ (revrev i) (adjSink hi W) x y (toRR i b)
        (⟨adjFwdAmb g x z, adjFwdAmb_mem g x z⟩ : adjSinkL W x)).1 := by
  have hy : y ≠ i := by
    rintro rfl
    exact (hi x).false b
  by_cases hx : x = i
  · subst hx
    rw [adjSink_map_from hi b]
    refine Prod.ext ?_ ?_
    · show adjFwdFst g y (V.map b z) = (adjFwdSnd g x z) (revInOfOut x ⟨y, b⟩)
      rw [adjFwdFst_of_ne g hy, adjFwdSnd_self]
      rfl
    · show adjFwdSnd g y (V.map b z) = 0
      rw [adjFwdSnd_of_ne g hy]; rfl
  · rw [adjSink_map_keep hi b hx hy]
    refine Prod.ext ?_ ?_
    · show adjFwdFst g y (V.map b z) = adjMap W (PSum.inl ⟨b, hx, hy⟩) (adjFwdFst g x z)
      rw [adjFwdFst_of_ne g hy, adjFwdFst_of_ne g hx]
      show adjApp g y (adjIn V i hy (V.map b z)) =
        adjMap W (PSum.inl ⟨b, hx, hy⟩) (adjApp g x (adjIn V i hx z))
      rw [← adjIn_map_keep hi b hx hy z]
      exact adj_comm g _ _
    · show adjFwdSnd g y (V.map b z) = 0
      rw [adjFwdSnd_of_ne g hy]; rfl

/-- The morphism `V → F_i^+ W` attached to a morphism `g : F_i^- V → W`. -/
def adjFwd : RevRevHom V (adjSink hi W) where
  app x := LinearMap.codRestrict (adjSinkL W x) (adjFwdAmb g x) (adjFwdAmb_mem g x)
  comm := fun b z => Subtype.ext (adjFwdAmb_comm g b z)

end Fwd2

section Bwd

variable {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (OutArrows i)] {hi : Quiver.IsSource i}
  {W : RevRep.{u, v, max (max a v) w, a} k i} (h : RevRevHom V (adjSink hi W))

/-- The `W_x`-component (first coordinate in the ambient space) of the component at `x` of a morphism
`V → F_i^+ W`. -/
def adjBwdFst (x : Q) : V.obj x →ₗ[k] adjObj W x :=
  ((LinearMap.fst k (adjObj W x) (adjInProd W)).comp (adjSinkL W x).subtype).comp (h.app x)

theorem adjBwdFst_apply (x : Q) (u : V.obj x) : adjBwdFst h x u = (h.app x u).1.1 := rfl

/-- The map `⨁_{i → j} V_j → W_i` induced by a morphism `V → F_i^+ W`. -/
def adjBwdPi : outProd V i →ₗ[k] adjObj W i :=
  ∑ o : OutArrows i, (adjMap W (revInOfOut i o).2).comp
    ((adjBwdFst h o.1).comp (LinearMap.proj (R := k) (φ := fun e : OutArrows i => V.obj e.1) o))

theorem adjBwdPi_apply (p : outProd V i) :
    adjBwdPi h p = ∑ o : OutArrows i, adjMap W (revInOfOut i o).2 ((h.app o.1 (p o)).1.1) := by
  simp [adjBwdPi, LinearMap.sum_apply]
  rfl

theorem adjBwd_val (o : OutArrows i) (u : V.obj i) :
    (h.app o.1 (V.map o.2 u)).1.1 = (h.app i u).1.2 (revInOfOut i o) := by
  have h1 := congrArg Subtype.val (h.comm o.2 u)
  exact (congrArg Prod.fst h1).trans (congrArg Prod.fst (adjSink_map_from hi o.2 (h.app i u)))

theorem adjBwdPi_outMap (u : V.obj i) : adjBwdPi h (outMap V i u) = 0 := by
  rw [adjBwdPi_apply]
  have h2 : ∀ o : OutArrows i, (h.app o.1 (outMap V i u o)).1.1 = (h.app i u).1.2 (revInOfOut i o) :=
    fun o => adjBwd_val h o u
  simp only [h2]
  rw [← adjSumIn_eq]
  exact ((adj_mem_sinkL_of_eq W rfl _).1 (h.app i u).2).2

/-- The map from the cokernel at `i` to `W_i` induced by a morphism `V → F_i^+ W`. -/
def adjBwdCoker : outCoker V i →ₗ[k] adjObj W i :=
  Submodule.liftQ _ (adjBwdPi h) (by
    rintro _ ⟨u, rfl⟩
    exact adjBwdPi_outMap h u)

theorem adjBwdCoker_mk (p : outProd V i) :
    adjBwdCoker h (Submodule.mkQ (LinearMap.range (outMap V i)) p) = adjBwdPi h p := rfl

/-- The part of the ambient map at `x` acting on `V_x` (zero at `i`). -/
def adjBwdA (x : Q) : V.obj x →ₗ[k] adjObj W x :=
  if x = i then 0 else adjBwdFst h x

/-- The part of the ambient map at `x` acting on the cokernel (zero away from `i`). -/
def adjBwdB (x : Q) : outCoker V i →ₗ[k] adjObj W x :=
  if hx : i = x then by subst hx; exact adjBwdCoker h else 0

theorem adjBwdA_of_ne {x : Q} (hx : x ≠ i) : adjBwdA h x = adjBwdFst h x := by simp [adjBwdA, hx]

theorem adjBwdA_self : adjBwdA h i = 0 := by simp [adjBwdA]

theorem adjBwdB_of_ne {x : Q} (hx : x ≠ i) : adjBwdB h x = 0 := by
  have : ¬ i = x := fun h => hx h.symm
  simp [adjBwdB, this]

theorem adjBwdB_self : adjBwdB h i = adjBwdCoker h := by simp [adjBwdB]

/-- The component at `x` of the morphism `F_i^- V → W` attached to a morphism `V → F_i^+ W`. -/
def adjBwdApp (x : Q) : adjObj (reflectSource V i hi) x →ₗ[k] adjObj W x :=
  ((adjBwdA h x).comp (LinearMap.fst k (V.obj x) (outCoker V i)) +
    (adjBwdB h x).comp (LinearMap.snd k (V.obj x) (outCoker V i))).comp (sourceL V i x).subtype

theorem adjBwdApp_of_ne {x : Q} (hx : x ≠ i) (z : sourceL V i x) :
    adjBwdApp h x z = (h.app x z.1.1).1.1 := by
  have hz : z.1.2 = 0 := (mem_sourceL_of_ne V i hx _).1 z.2
  show adjBwdA h x z.1.1 + adjBwdB h x z.1.2 = _
  rw [hz, adjBwdA_of_ne h hx, adjBwdB_of_ne h hx]
  simp only [LinearMap.zero_apply, add_zero]
  rfl

theorem adjBwdApp_self (z : sourceL V i i) : adjBwdApp h i z = adjBwdCoker h z.1.2 := by
  have hz : z.1.1 = 0 := (mem_sourceL_of_eq V i rfl _).1 z.2
  show adjBwdA h i z.1.1 + adjBwdB h i z.1.2 = _
  rw [hz, adjBwdA_self, adjBwdB_self]
  simp

/-- The morphism `F_i^- V → W` attached to a morphism `V → F_i^+ W`. -/
def adjBwd : RevRep.Hom (reflectSource V i hi) W :=
  @QRep.Hom.mk k Q _ (reversedAt i) _ _ (adjBwdApp h) (by
    intro x y e
    refine LinearMap.ext fun z => ?_
    show adjBwdApp h y (adjMap (reflectSource V i hi) e z) = adjMap W e (adjBwdApp h x z)
    rcases e with ⟨b, hx, hy⟩ | ⟨b, hxy⟩
    · have e1 : (adjMap (reflectSource V i hi) (PSum.inl ⟨b, hx, hy⟩) z).1.1 = V.map b z.1.1 :=
        congrArg Prod.fst (sourceMap_keep hi b hx hy z)
      refine (adjBwdApp_of_ne h hy _).trans (Eq.trans ?_ (congrArg (adjMap W _) (adjBwdApp_of_ne h hx z)).symm)
      rw [e1]
      have h1 := congrArg Subtype.val (h.comm b z.1.1)
      exact (congrArg Prod.fst h1).trans (congrArg Prod.fst (adjSink_map_keep hi b hx hy (h.app x z.1.1)))
    · have hx : x ≠ i := by
        rintro rfl
        exact (hi y).false b
      have hy : y = i := hxy.resolve_left hx
      subst hy
      refine (adjBwdApp_self h _).trans (Eq.trans ?_ (congrArg (adjMap W _) (adjBwdApp_of_ne h hx z)).symm)
      have e1 : (adjMap (reflectSource V y hi) (PSum.inr ⟨b, hxy⟩) z).1.2 =
          Submodule.mkQ (LinearMap.range (outMap V y)) (Pi.single ⟨x, b⟩ z.1.1) :=
        congrArg Prod.snd (sourceMap_revOut hi b z)
      rw [e1, adjBwdCoker_mk, adjBwdPi_apply, Finset.sum_eq_single (⟨x, b⟩ : OutArrows y)]
      · rw [Pi.single_eq_same]
        rfl
      · intro o _ ho
        rw [Pi.single_eq_of_ne ho]
        have : h.app o.1 0 = 0 := (h.app o.1).map_zero
        rw [this]
        exact (adjMap W _).map_zero
      · simp)

end Bwd

section Equiv

variable {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (OutArrows i)] {hi : Quiver.IsSource i}
  {W : RevRep.{u, v, max (max a v) w, a} k i}

theorem adjBwd_adjFwd (g : RevRep.Hom (reflectSource V i hi) W) : adjBwd (adjFwd g) = g := by
  refine @QRep.Hom.ext k Q _ (reversedAt i) _ _ _ _ fun x => LinearMap.ext fun z => ?_
  show adjBwdApp (adjFwd g) x z = adjApp g x z
  rcases z with ⟨⟨u, c⟩, hz⟩
  by_cases hx : x = i
  · subst hx
    have hu : u = 0 := (mem_sourceL_of_eq V x rfl _).1 hz
    subst hu
    induction c using Submodule.Quotient.induction_on with
    | _ p =>
      refine (adjBwdApp_self (adjFwd g) _).trans ?_
      refine Eq.trans ?_ (adj_keyA g p).symm
      show adjBwdPi (adjFwd g) p = _
      rw [adjBwdPi_apply]
      refine Finset.sum_congr rfl fun o _ => ?_
      show adjMap W (revInOfOut x o).2 (adjFwdFst g o.1 (p o)) = _
      rw [adjFwdFst_of_ne g (ne_of_arrow_source hi o.2)]
      rfl
  · have hc : c = 0 := (mem_sourceL_of_ne V i hx _).1 hz
    subst hc
    refine (adjBwdApp_of_ne (adjFwd g) hx _).trans ?_
    show adjFwdFst g x u = _
    rw [adjFwdFst_of_ne g hx]
    rfl

theorem adjFwd_adjBwd (h : RevRevHom V (adjSink hi W)) : adjFwd (adjBwd h) = h := by
  refine RevRevHom.ext fun x => LinearMap.ext fun u => Subtype.ext (Prod.ext ?_ ?_)
  · by_cases hx : x = i
    · subst hx
      show adjFwdFst (adjBwd h) x u = (h.app x u).1.1
      rw [adjFwdFst_self]
      exact ((adj_mem_sinkL_of_eq W rfl _).1 (h.app x u).2).1.symm
    · show adjFwdFst (adjBwd h) x u = (h.app x u).1.1
      rw [adjFwdFst_of_ne _ hx]
      exact adjBwdApp_of_ne h hx (adjIn V i hx u)
  · by_cases hx : x = i
    · subst hx
      show adjFwdSnd (adjBwd h) x u = (h.app x u).1.2
      rw [adjFwdSnd_self]
      funext e
      obtain ⟨o, rfl⟩ := revInOfOut_surjective x e
      refine Eq.trans ?_ (adjBwd_val h o u)
      exact adjBwdApp_of_ne h (ne_of_arrow_source hi o.2) (adjIn V x (ne_of_arrow_source hi o.2) (V.map o.2 u))
    · show adjFwdSnd (adjBwd h) x u = (h.app x u).1.2
      rw [adjFwdSnd_of_ne _ hx, (adj_mem_sinkL_of_ne W hx _).1 (h.app x u).2]
      rfl

/-- **Adjunction between reflection functors** (Etingof et al., exercise after §5.7). At a source `i` of `Q`,
morphisms `F_i^- V → W` of representations of `Q_i` correspond bijectively to morphisms `V → F_i^+ W`
(with `(Q_i)_i` identified with `Q` through `toRR`). -/
@[kb "etingof2011" "Exercise, p. 105"]
def reflectAdjEquiv : RevRep.Hom (reflectSource V i hi) W ≃ RevRevHom V (adjSink hi W) where
  toFun := adjFwd
  invFun := adjBwd
  left_inv := adjBwd_adjFwd
  right_inv := adjFwd_adjBwd

end Equiv

/-! ### Naturality -/

/-- Composition of a morphism `V → X` with a morphism `X → X'` of representations of `(Q_i)_i`. -/
def RevRevHom.postcomp {V : QRep.{u, v, w, a} k Q} {i : Q} {X X' : @QRep.{u, v, w', a} k Q _ (revrev i)}
    (t : @QRep.Hom k Q _ (revrev i) X X') (h : RevRevHom V X) : RevRevHom V X' where
  app x := (@QRep.Hom.app k Q _ (revrev i) X X' t x).comp (h.app x)
  comm := by
    intro x y b z
    show @QRep.Hom.app k Q _ (revrev i) X X' t y (h.app y (V.map b z)) = _
    rw [h.comm b z]
    exact LinearMap.congr_fun (@QRep.Hom.comm k Q _ (revrev i) X X' t x y (toRR i b)) _

/-- Composition of a morphism `V' → V` of representations of `Q` with a morphism `V → X`. -/
def RevRevHom.precomp {V V' : QRep.{u, v, w, a} k Q} {i : Q} {X : @QRep.{u, v, w', a} k Q _ (revrev i)}
    (h : RevRevHom V X) (f : QRep.Hom V' V) : RevRevHom V' X where
  app x := (h.app x).comp (f.app x)
  comm := by
    intro x y b z
    exact (congrArg (h.app y) (LinearMap.congr_fun (f.comm b) z)).trans (h.comm b (f.app x z))

section Natural

variable {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (OutArrows i)] {hi : Quiver.IsSource i}
  {W W' : RevRep.{u, v, max (max a v) w, a} k i}

/-- **Naturality in `W`** of `reflectAdjEquiv`: composing `g : F_i^- V → W` with `g' : W → W'` corresponds to
composing the image of `g` with `F_i^+ g'`. -/
@[kb "etingof2011" "Exercise, p. 105"]
theorem reflectAdjEquiv_postcomp (g' : RevRep.Hom W W') (g : RevRep.Hom (reflectSource V i hi) W) :
    reflectAdjEquiv (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) =
      RevRevHom.postcomp
        (@reflectSinkMap k _ Q (reversedAt i) W W' g' i (fintypeInArrowsRev i) (isSink_reversedAt hi))
        (reflectAdjEquiv g) := by
  refine RevRevHom.ext fun x => LinearMap.ext fun u => Subtype.ext ?_
  show adjFwdAmb (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) x u =
    @sinkAmb k _ Q (reversedAt i) W W' g' i x (adjFwdAmb g x u)
  by_cases hx : x = i
  · subst x
    refine Prod.ext ?_ ?_
    · show adjFwdFst (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) i u = adjApp g' i (adjFwdFst g i u)
      have h1 : adjFwdFst (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) i u = 0 := by
        rw [adjFwdFst_self]; rfl
      have h2 : adjFwdFst g i u = 0 := by rw [adjFwdFst_self]; rfl
      rw [h1, h2]
      exact (adjApp g' i).map_zero.symm
    · show adjFwdSnd (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) i u =
        fun e => adjApp g' e.1 (adjFwdSnd g i u e)
      rw [adjFwdSnd_self, adjFwdSnd_self]
      funext e
      rfl
  · refine Prod.ext ?_ ?_
    · show adjFwdFst (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) x u = adjApp g' x (adjFwdFst g x u)
      rw [adjFwdFst_of_ne _ hx, adjFwdFst_of_ne _ hx]
      rfl
    · show adjFwdSnd (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) x u =
        fun e => adjApp g' e.1 (adjFwdSnd g x u e)
      have h1 : adjFwdSnd (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g' g) x u = 0 := by
        rw [adjFwdSnd_of_ne _ hx]; rfl
      have h2 : adjFwdSnd g x u = 0 := by rw [adjFwdSnd_of_ne _ hx]; rfl
      rw [h1, h2]
      funext e
      exact (adjApp g' e.1).map_zero.symm

theorem adjIn_reflectSourceMap {V V' : QRep.{u, v, w, a} k Q} (f : QRep.Hom V' V) (hi : Quiver.IsSource i) {x : Q}
    (hx : x ≠ i) (u : V'.obj x) :
    @QRep.Hom.app k Q _ (reversedAt i) _ _ (reflectSourceMap f i hi) x (adjIn V' i hx u) =
      adjIn V i hx (f.app x u) := by
  refine Subtype.ext ?_
  show sourceAmb f i x (u, 0) = (f.app x u, 0)
  simp [sourceAmb_apply]

/-- **Naturality in `V`** of `reflectAdjEquiv`: precomposing `g : F_i^- V → W` with `F_i^- f` for a morphism
`f : V' → V` corresponds to precomposing the image of `g` with `f`. -/
@[kb "etingof2011" "Exercise, p. 105"]
theorem reflectAdjEquiv_precomp {V' : QRep.{u, v, w, a} k Q} (f : QRep.Hom V' V)
    (g : RevRep.Hom (reflectSource V i hi) W) :
    reflectAdjEquiv (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) =
      RevRevHom.precomp (reflectAdjEquiv g) f := by
  refine RevRevHom.ext fun x => LinearMap.ext fun u => Subtype.ext ?_
  show adjFwdAmb (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) x u =
    adjFwdAmb g x (f.app x u)
  by_cases hx : x = i
  · subst x
    refine Prod.ext ?_ ?_
    · show adjFwdFst (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) i u =
        adjFwdFst g i (f.app i u)
      have h1 : adjFwdFst (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) i u = 0 := by
        rw [adjFwdFst_self]; rfl
      have h2 : adjFwdFst g i (f.app i u) = 0 := by rw [adjFwdFst_self]; rfl
      rw [h1, h2]
    · show adjFwdSnd (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) i u =
        adjFwdSnd g i (f.app i u)
      rw [adjFwdSnd_self, adjFwdSnd_self]
      funext e
      show adjApp g e.1 (@QRep.Hom.app k Q _ (reversedAt i) _ _ (reflectSourceMap f i hi) e.1
          (adjIn V' i (ne_of_arrow_source hi (arrOfRev e.2)) (V'.map (arrOfRev e.2) u))) =
        adjApp g e.1 (adjIn V i (ne_of_arrow_source hi (arrOfRev e.2)) (V.map (arrOfRev e.2) (f.app i u)))
      rw [adjIn_reflectSourceMap f hi (ne_of_arrow_source hi (arrOfRev e.2))]
      have hc : f.app e.1 (V'.map (arrOfRev e.2) u) = V.map (arrOfRev e.2) (f.app i u) :=
        LinearMap.congr_fun (f.comm (arrOfRev e.2)) u
      exact congrArg (fun t => adjApp g e.1 (adjIn V i (ne_of_arrow_source hi (arrOfRev e.2)) t)) hc
  · refine Prod.ext ?_ ?_
    · show adjFwdFst (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) x u =
        adjFwdFst g x (f.app x u)
      rw [adjFwdFst_of_ne _ hx, adjFwdFst_of_ne _ hx]
      show adjApp g x (@QRep.Hom.app k Q _ (reversedAt i) _ _ (reflectSourceMap f i hi) x (adjIn V' i hx u)) =
        adjApp g x (adjIn V i hx (f.app x u))
      rw [adjIn_reflectSourceMap f hi hx]
    · show adjFwdSnd (@QRep.Hom.comp k Q _ (reversedAt i) _ _ _ g (reflectSourceMap f i hi)) x u =
        adjFwdSnd g x (f.app x u)
      rw [adjFwdSnd_of_ne _ hx, adjFwdSnd_of_ne _ hx]
      rfl

end Natural

end

end UndergradKB.RepresentationTheory
