import UndergradKB.RepresentationTheory.ReflectionFunctors
import UndergradKB.Common.Attr

/-! # Reflection functors: morphisms, `F^- F^+`, and indecomposability (Etingof et al., §5.5-5.7)

Complements `ReflectionFunctors.lean`.

* The action of `F_i^+` (`reflectSinkMap`) and `F_i^-` (`reflectSourceMap`) on morphisms of representations, with
  functoriality (`reflectSinkMap_id`, `reflectSinkMap_comp`, and the same for sources).
* Proposition 5.29: at a sink `i` where the sum map is surjective, `F_i^- F_i^+ V` is isomorphic to `V`
  (`reflectSource_reflectSink_iso`); dually at a source with injective map out of `V_i`
  (`reflectSink_reflectSource_iso`). Since `(Q_i)_i` is only canonically in bijection with `Q` on arrows, the
  isomorphism is stated through the identification `toRR` of the arrows (`RevRevIso`).
* Proposition 5.30: `F_i^+ V` (resp. `F_i^- V`) is indecomposable when `V` is indecomposable and not the simple
  representation at the sink (source) `i` (`reflectSink_isIndecomposable`, `reflectSource_isIndecomposable`),
  and the dimension vector is `s_i d(V)` (`reflectSink_indecomposable_dimVec`, ...). The proof builds directly a
  decomposition of `V` from a decomposition of `F_i^+ V` (using surjectivity of the sum map), so it does not go
  through additivity of the functor.
-/

namespace UndergradKB.RepresentationTheory

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

universe u v w a

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

/-- Homomorphisms of representations of `Q_i`. -/
abbrev RevRep.Hom.{u', v', w', a'} {k : Type u'} [Field k] {Q : Type v'} [Quiver.{a'} Q] {i : Q}
    (W W' : RevRep.{u', v', w', a'} k i) : Type _ :=
  @QRep.Hom k Q _ (reversedAt i) W W'

section SinkMap

theorem reflectSink_map_inl {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (InArrows i)] (hi : Quiver.IsSink i)
    {x y : Q} (e : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i) (z : sinkL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSink V i hi) x y (PSum.inl ⟨e, hx, hy⟩) z).1 =
      sinkKeep V i e z.1 := rfl

theorem reflectSink_map_inr {V : QRep.{u, v, w, a} k Q} {i : Q} [Fintype (InArrows i)] (hi : Quiver.IsSink i)
    {x y : Q} (e : y ⟶ x) (h : x = i ∨ y = i) (z : sinkL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSink V i hi) x y (PSum.inr ⟨e, h⟩) z).1 =
      sinkRev V i e z.1 := rfl

variable {V V' : QRep.{u, v, w, a} k Q} (f : QRep.Hom V V') (i : Q) [Fintype (InArrows i)]

/-- The ambient map `V_x × ∏ V_j → V'_x × ∏ V'_j` induced by `f`. -/
def sinkAmb (x : Q) : V.obj x × inProd V i →ₗ[k] V'.obj x × inProd V' i :=
  LinearMap.prodMap (f.app x)
    (LinearMap.pi fun e : InArrows i => (f.app e.1).comp (LinearMap.proj (R := k) (φ := fun e : InArrows i => V.obj e.1) e))

theorem sinkAmb_apply (x : Q) (z : V.obj x × inProd V i) :
    sinkAmb f i x z = (f.app x z.1, fun e => f.app e.1 (z.2 e)) := rfl

theorem sumIn_comm (p : inProd V i) :
    sumIn V' i (fun e => f.app e.1 (p e)) = f.app i (sumIn V i p) := by
  rw [sumIn_apply, sumIn_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact (LinearMap.congr_fun (f.comm e.2) (p e)).symm

theorem sinkAmb_mem (x : Q) {z : V.obj x × inProd V i} (hz : z ∈ sinkL V i x) :
    sinkAmb f i x z ∈ sinkL V' i x := by
  by_cases hx : x = i
  · rw [mem_sinkL_of_eq V i hx] at hz
    rw [mem_sinkL_of_eq V' i hx]
    subst hx
    refine ⟨by simp [sinkAmb_apply, hz.1], ?_⟩
    simp only [sinkAmb_apply]
    rw [sumIn_comm, hz.2, map_zero]
  · rw [mem_sinkL_of_ne V i hx] at hz
    rw [mem_sinkL_of_ne V' i hx]
    simp [sinkAmb_apply, hz]
    rfl

/-- The action of `F_i^+` on a morphism `f : V → V'`: on the new space at `i` it is the restriction of
`⨁ f_j`, elsewhere it is `f`. -/
@[kb "etingof2011" "Definition 5.26, p. 90"]
def reflectSinkMap (hi : Quiver.IsSink i) :
    RevRep.Hom (reflectSink V i hi) (reflectSink V' i hi) :=
  @QRep.Hom.mk k Q _ (reversedAt i) _ _ (fun x => (sinkAmb f i x).restrict (fun _ hz => sinkAmb_mem f i x hz)) (by
    intro x y e
    rcases e with ⟨e, hx, hy⟩ | ⟨e, h⟩
    · refine LinearMap.ext fun z => Subtype.ext ?_
      have := LinearMap.congr_fun (f.comm e) z.1.1
      change sinkAmb f i y (sinkKeep V i e z.1) = sinkKeep V' i e (sinkAmb f i x z.1)
      simp only [LinearMap.comp_apply] at this
      simp [sinkKeep, sinkAmb_apply, this]
      rfl
    · refine LinearMap.ext fun z => Subtype.ext ?_
      change sinkAmb f i y (sinkRev V i e z.1) = sinkRev V' i e (sinkAmb f i x z.1)
      by_cases hxi : x = i
      · subst hxi
        simp [sinkRev, sinkAmb_apply]
        rfl
      · simp [sinkRev, hxi])

theorem reflectSinkMap_app_val (hi : Quiver.IsSink i) (x : Q) (z : sinkL V i x) :
    (@QRep.Hom.app k Q _ (reversedAt i) _ _ (reflectSinkMap f i hi) x z).1 = sinkAmb f i x z.1 := rfl

theorem reflectSinkMap_id (hi : Quiver.IsSink i) :
    reflectSinkMap (QRep.Hom.id V) i hi = @QRep.Hom.id k Q _ (reversedAt i) (reflectSink V i hi) := by
  refine @QRep.Hom.ext k Q _ (reversedAt i) _ _ _ _ fun x => LinearMap.ext fun z => Subtype.ext ?_
  change sinkAmb (QRep.Hom.id V) i x z.1 = z.1
  rcases z with ⟨⟨u, p⟩, hz⟩
  simp [sinkAmb_apply]

theorem reflectSinkMap_comp {V'' : QRep.{u, v, w, a} k Q} (g : QRep.Hom V' V'') (hi : Quiver.IsSink i) :
    reflectSinkMap (g.comp f) i hi = @QRep.Hom.comp k Q _ (reversedAt i) _ _ _
      (reflectSinkMap g i hi) (reflectSinkMap f i hi) := by
  refine @QRep.Hom.ext k Q _ (reversedAt i) _ _ _ _ fun x => LinearMap.ext fun z => Subtype.ext ?_
  change sinkAmb (g.comp f) i x z.1 = sinkAmb g i x (sinkAmb f i x z.1)
  simp [sinkAmb_apply]

end SinkMap

section SourceMap

theorem reflectSource_map_inl {V : QRep.{u, v, w, a} k Q} {i : Q} (hi : Quiver.IsSource i)
    {x y : Q} (e : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i) (z : sourceL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) x y (PSum.inl ⟨e, hx, hy⟩) z).1 =
      sourceKeep V i e z.1 := rfl

theorem reflectSource_map_inr {V : QRep.{u, v, w, a} k Q} {i : Q} (hi : Quiver.IsSource i)
    {x y : Q} (e : y ⟶ x) (h : x = i ∨ y = i) (z : sourceL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) x y (PSum.inr ⟨e, h⟩) z).1 =
      sourceRev V i e z.1 := rfl

variable {V V' : QRep.{u, v, w, a} k Q} (f : QRep.Hom V V') (i : Q)

/-- The map `⨁_{i → j} V_j → ⨁_{i → j} V'_j` induced by `f`. -/
def outProdMap : outProd V i →ₗ[k] outProd V' i :=
  LinearMap.pi fun e : OutArrows i =>
    (f.app e.1).comp (LinearMap.proj (R := k) (φ := fun e : OutArrows i => V.obj e.1) e)

theorem outProdMap_apply (p : outProd V i) (e : OutArrows i) : outProdMap f i p e = f.app e.1 (p e) := rfl

theorem outProdMap_outMap (z : V.obj i) : outProdMap f i (outMap V i z) = outMap V' i (f.app i z) := by
  funext e
  simp only [outProdMap_apply, outMap_apply]
  exact LinearMap.congr_fun (f.comm e.2) z

theorem outProdMap_single (e : OutArrows i) (u : V.obj e.1) :
    outProdMap f i (Pi.single e u) = Pi.single e (f.app e.1 u) := by
  funext e'
  by_cases h : e' = e
  · subst h; simp [outProdMap_apply]
  · simp [outProdMap_apply, Pi.single_eq_of_ne h]

/-- The map on cokernels induced by `f`. -/
def outCokerMap : outCoker V i →ₗ[k] outCoker V' i :=
  Submodule.mapQ _ _ (outProdMap f i) (by
    rintro _ ⟨z, rfl⟩
    exact ⟨f.app i z, (outProdMap_outMap f i z).symm⟩)

theorem outCokerMap_mk (p : outProd V i) :
    outCokerMap f i (Submodule.mkQ _ p) = Submodule.mkQ _ (outProdMap f i p) := rfl

/-- The ambient map `V_x × coker → V'_x × coker'` induced by `f`. -/
def sourceAmb (x : Q) : V.obj x × outCoker V i →ₗ[k] V'.obj x × outCoker V' i :=
  LinearMap.prodMap (f.app x) (outCokerMap f i)

theorem sourceAmb_apply (x : Q) (z : V.obj x × outCoker V i) :
    sourceAmb f i x z = (f.app x z.1, outCokerMap f i z.2) := rfl

theorem sourceAmb_mem (x : Q) {z : V.obj x × outCoker V i} (hz : z ∈ sourceL V i x) :
    sourceAmb f i x z ∈ sourceL V' i x := by
  by_cases hx : x = i
  · rw [mem_sourceL_of_eq V i hx] at hz
    rw [mem_sourceL_of_eq V' i hx]
    simp [sourceAmb_apply, hz]
  · rw [mem_sourceL_of_ne V i hx] at hz
    rw [mem_sourceL_of_ne V' i hx]
    simp [sourceAmb_apply, hz]

/-- The action of `F_i^-` on a morphism `f : V → V'`: the induced map on cokernels at `i`, `f` elsewhere. -/
@[kb "etingof2011" "Definition 5.27, p. 90"]
def reflectSourceMap (hi : Quiver.IsSource i) :
    RevRep.Hom (reflectSource V i hi) (reflectSource V' i hi) :=
  @QRep.Hom.mk k Q _ (reversedAt i) _ _
    (fun x => (sourceAmb f i x).restrict (fun _ hz => sourceAmb_mem f i x hz)) (by
    intro x y e
    rcases e with ⟨e, hx, hy⟩ | ⟨e, h⟩
    · refine LinearMap.ext fun z => Subtype.ext ?_
      have := LinearMap.congr_fun (f.comm e) z.1.1
      change sourceAmb f i y (sourceKeep V i e z.1) = sourceKeep V' i e (sourceAmb f i x z.1)
      simp only [LinearMap.comp_apply] at this
      simp [sourceKeep, sourceAmb_apply, this]
    · refine LinearMap.ext fun z => Subtype.ext ?_
      change sourceAmb f i y (sourceRev V i e z.1) = sourceRev V' i e (sourceAmb f i x z.1)
      by_cases hyi : y = i
      · subst hyi
        simp [sourceRev, sourceAmb_apply]
        exact congrArg Submodule.Quotient.mk (outProdMap_single f y ⟨x, e⟩ _)
      · simp [sourceRev, hyi])

theorem reflectSourceMap_id (hi : Quiver.IsSource i) :
    reflectSourceMap (QRep.Hom.id V) i hi = @QRep.Hom.id k Q _ (reversedAt i) (reflectSource V i hi) := by
  refine @QRep.Hom.ext k Q _ (reversedAt i) _ _ _ _ fun x => LinearMap.ext fun z => Subtype.ext ?_
  change sourceAmb (QRep.Hom.id V) i x z.1 = z.1
  rcases z with ⟨⟨u, p⟩, hz⟩
  induction p using Submodule.Quotient.induction_on with
  | _ q => rfl

theorem reflectSourceMap_comp {V'' : QRep.{u, v, w, a} k Q} (g : QRep.Hom V' V'') (hi : Quiver.IsSource i) :
    reflectSourceMap (g.comp f) i hi = @QRep.Hom.comp k Q _ (reversedAt i) _ _ _
      (reflectSourceMap g i hi) (reflectSourceMap f i hi) := by
  refine @QRep.Hom.ext k Q _ (reversedAt i) _ _ _ _ fun x => LinearMap.ext fun z => Subtype.ext ?_
  change sourceAmb (g.comp f) i x z.1 = sourceAmb g i x (sourceAmb f i x z.1)
  rcases z with ⟨⟨u, p⟩, hz⟩
  induction p using Submodule.Quotient.induction_on with
  | _ q => rfl

end SourceMap

/-! ### Helpers on complements -/

theorem isCompl_of_forall {M : Type*} [AddCommGroup M] [Module k M] {p q : Submodule k M}
    (hd : ∀ z ∈ p, z ∈ q → z = 0) (hs : ∀ z, ∃ a ∈ p, ∃ b ∈ q, a + b = z) : IsCompl p q := by
  refine ⟨Submodule.disjoint_def.2 hd, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro z _
  obtain ⟨a, ha, b, hb, rfl⟩ := hs z
  exact Submodule.add_mem_sup ha hb

theorem exists_add_of_isCompl {M : Type*} [AddCommGroup M] [Module k M] {p q : Submodule k M}
    (h : IsCompl p q) (z : M) : ∃ a ∈ p, ∃ b ∈ q, a + b = z := by
  have : z ∈ p ⊔ q := by rw [h.sup_eq_top]; trivial
  exact Submodule.mem_sup.1 this

theorem eq_zero_of_isCompl' {M : Type*} [AddCommGroup M] [Module k M] {p q : Submodule k M}
    (h : IsCompl p q) {z : M} (hp : z ∈ p) (hq : z ∈ q) : z = 0 :=
  Submodule.disjoint_def.1 h.disjoint z hp hq

/-- Subrepresentations of a representation of `Q_i`. -/
abbrev RevRep.Subrep.{u', v', w', a'} {k : Type u'} [Field k] {Q : Type v'} [Quiver.{a'} Q] {i : Q}
    (W : RevRep.{u', v', w', a'} k i) : Type _ :=
  @QRep.Subrep k Q _ (reversedAt i) W

/-- Indecomposability of a representation of `Q_i`. -/
abbrev RevRep.IsIndecomposable.{u', v', w', a'} {k : Type u'} [Field k] {Q : Type v'} [Quiver.{a'} Q] {i : Q}
    (W : RevRep.{u', v', w', a'} k i) : Prop :=
  @QRep.IsIndecomposable k Q _ (reversedAt i) W

namespace RevRep.Subrep

/-- The subspace at the vertex `x` of a subrepresentation of a representation of `Q_i`. -/
abbrev car {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] {i : Q} {W : RevRep.{u, v, w, a} k i}
    (S : RevRep.Subrep W) (x : Q) : Submodule k (@QRep.obj k Q _ (reversedAt i) W x) :=
  @QRep.Subrep.carrier k Q _ (reversedAt i) W S x

theorem map_mem' {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] {i : Q} {W : RevRep.{u, v, w, a} k i}
    (S : RevRep.Subrep W) {x y : Q} (a : @Quiver.Hom Q (reversedAt i) x y)
    {z : @QRep.obj k Q _ (reversedAt i) W x} (hz : z ∈ S.car x) :
    @QRep.map k Q _ (reversedAt i) W x y a z ∈ S.car y :=
  @QRep.Subrep.map_mem k Q _ (reversedAt i) W S x y a z hz

end RevRep.Subrep

theorem ne_of_arrow_sink {i j : Q} (hi : Quiver.IsSink i) (a : j ⟶ i) : j ≠ i := by
  rintro rfl
  exact (hi _).false a

/-! ### Proposition 5.30, sink case -/

section Prop530Sink

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)] (hi : Quiver.IsSink i)

/-- The part of a subrepresentation `S` of `F_i^+ V` at the vertex `x`, seen inside `V_x`. -/
def sinkSubAt (S : RevRep.Subrep (reflectSink V i hi)) (x : Q) : Submodule k (V.obj x) :=
  ((S.car x).map (sinkL V i x).subtype).comap (LinearMap.inl k (V.obj x) (inProd V i))

variable {V i hi}

theorem mem_sinkSubAt {S : RevRep.Subrep (reflectSink V i hi)} {x : Q} {u : V.obj x} :
    u ∈ sinkSubAt V i hi S x ↔ ∃ z : sinkL V i x, z ∈ S.car x ∧ z.1 = (u, 0) := by
  exact Iff.rfl

theorem sinkMap_revIn (hi : Quiver.IsSink i) {j : Q} (a : j ⟶ i) (z : sinkL V i i) :
    (@QRep.map k Q _ (reversedAt i) (reflectSink V i hi) i j (PSum.inr ⟨a, Or.inl rfl⟩) z).1 =
      (z.1.2 ⟨j, a⟩, 0) := by
  rw [reflectSink_map_inr]
  simp [sinkRev]

theorem sinkMap_keep (hi : Quiver.IsSink i) {x y : Q} (a : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i)
    (z : sinkL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSink V i hi) x y (PSum.inl ⟨a, hx, hy⟩) z).1 =
      (V.map a z.1.1, 0) := by
  refine (reflectSink_map_inl hi a hx hy z).trans ?_
  simp [sinkKeep]

theorem sinkSubAt_of_mem (S : RevRep.Subrep (reflectSink V i hi)) {x : Q} {z : sinkL V i x}
    (hz : z ∈ S.car x) (h2 : z.1.2 = 0) : z.1.1 ∈ sinkSubAt V i hi S x :=
  mem_sinkSubAt.2 ⟨z, hz, Prod.ext rfl h2⟩

theorem sinkSub_pi_mem (S : RevRep.Subrep (reflectSink V i hi)) {z : sinkL V i i}
    (hz : z ∈ S.car i) (e : InArrows i) : z.1.2 e ∈ sinkSubAt V i hi S e.1 := by
  have hm := S.map_mem' (PSum.inr ⟨e.2, Or.inl rfl⟩ : @Quiver.Hom Q (reversedAt i) i e.1) hz
  exact mem_sinkSubAt.2 ⟨_, hm, sinkMap_revIn hi e.2 z⟩

/-- The part of `S` at the vertex `i`, as a subspace of `⨁_{j → i} V_j`. -/
def sinkSubPi (S : RevRep.Subrep (reflectSink V i hi)) : Submodule k (inProd V i) :=
  Submodule.pi Set.univ fun e : InArrows i => sinkSubAt V i hi S e.1

theorem mem_sinkSubPi {S : RevRep.Subrep (reflectSink V i hi)} {p : inProd V i} :
    p ∈ sinkSubPi S ↔ ∀ e : InArrows i, p e ∈ sinkSubAt V i hi S e.1 := by
  simp [sinkSubPi, Submodule.mem_pi]

/-- The subrepresentation of `V` obtained from a subrepresentation `S` of `F_i^+ V` (assuming the sum map is
surjective): the same subspaces away from `i`, and the image of `⨁ S_j` under the sum map at `i`. -/
def sinkSub (S : RevRep.Subrep (reflectSink V i hi)) : QRep.Subrep V where
  carrier := Function.update (fun x => sinkSubAt V i hi S x) i ((sinkSubPi S).map (sumIn V i))
  map_mem := by
    intro x y a z hz
    by_cases hx : x = i
    · exact ((hi y).false (cast (by rw [hx]) a)).elim
    · rw [Function.update_of_ne hx] at hz
      by_cases hy : y = i
      · subst hy
        rw [Function.update_self]
        refine ⟨Pi.single (⟨x, a⟩ : InArrows y) z, ?_, ?_⟩
        · refine mem_sinkSubPi.2 fun e => ?_
          by_cases he : e = ⟨x, a⟩
          · subst he; simpa using hz
          · rw [Pi.single_eq_of_ne he]; exact zero_mem _
        · rw [sumIn_apply, Finset.sum_eq_single (⟨x, a⟩ : InArrows y)]
          · simp
          · intro e _ he; simp [Pi.single_eq_of_ne he]
          · simp
      · rw [Function.update_of_ne hy]
        obtain ⟨z', hz', hz'1⟩ := mem_sinkSubAt.1 hz
        refine mem_sinkSubAt.2 ⟨_, S.map_mem' (PSum.inl ⟨a, hx, hy⟩ : @Quiver.Hom Q (reversedAt i) x y) hz', ?_⟩
        rw [sinkMap_keep hi a hx hy, hz'1]


theorem sinkSub_carrier_self (S : RevRep.Subrep (reflectSink V i hi)) :
    (sinkSub S).carrier i = (sinkSubPi S).map (sumIn V i) :=
  Function.update_self i _ (fun x => sinkSubAt V i hi S x)

theorem sinkSub_carrier_ne (S : RevRep.Subrep (reflectSink V i hi)) {x : Q} (hx : x ≠ i) :
    (sinkSub S).carrier x = sinkSubAt V i hi S x :=
  Function.update_of_ne hx _ (fun x => sinkSubAt V i hi S x)

variable {S T : RevRep.Subrep (reflectSink V i hi)}

theorem sinkSubAt_compl (hST : ∀ x, IsCompl (S.car x) (T.car x)) {x : Q} (hx : x ≠ i) :
    IsCompl (sinkSubAt V i hi S x) (sinkSubAt V i hi T x) := by
  refine isCompl_of_forall (fun u hS hT => ?_) (fun u => ?_)
  · obtain ⟨z, hz, hz1⟩ := mem_sinkSubAt.1 hS
    obtain ⟨z', hz', hz1'⟩ := mem_sinkSubAt.1 hT
    have : z = z' := Subtype.ext (hz1.trans hz1'.symm)
    subst this
    have h0 := eq_zero_of_isCompl' (hST x) hz hz'
    rw [h0] at hz1
    exact (congrArg Prod.fst hz1).symm
  · let z0 : sinkL V i x := ⟨(u, 0), (mem_sinkL_of_ne V i hx _).2 rfl⟩
    obtain ⟨s, hs, t, ht, hst⟩ := exists_add_of_isCompl (hST x) z0
    have hs2 : s.1.2 = 0 := (mem_sinkL_of_ne V i hx _).1 s.2
    have ht2 : t.1.2 = 0 := (mem_sinkL_of_ne V i hx _).1 t.2
    refine ⟨s.1.1, sinkSubAt_of_mem S hs hs2, t.1.1, sinkSubAt_of_mem T ht ht2, ?_⟩
    exact congrArg (fun w : sinkL V i x => w.1.1) hst

theorem sinkSubPi_disjoint (hST : ∀ x, IsCompl (S.car x) (T.car x)) {r : inProd V i}
    (h1 : r ∈ sinkSubPi S) (h2 : r ∈ sinkSubPi T) : r = 0 := by
  funext e
  exact eq_zero_of_isCompl' (sinkSubAt_compl hST (ne_of_arrow_sink hi e.2))
    (mem_sinkSubPi.1 h1 e) (mem_sinkSubPi.1 h2 e)

theorem exists_sinkSubPi_add (hST : ∀ x, IsCompl (S.car x) (T.car x)) (r : inProd V i) :
    ∃ a ∈ sinkSubPi S, ∃ b ∈ sinkSubPi T, a + b = r := by
  choose a ha b hb hab using fun e : InArrows i =>
    exists_add_of_isCompl (sinkSubAt_compl hST (ne_of_arrow_sink hi e.2)) (r e)
  exact ⟨a, mem_sinkSubPi.2 ha, b, mem_sinkSubPi.2 hb, funext hab⟩

theorem sinkSub_compl_self (hsurj : Function.Surjective (sumIn V i)) (hST : ∀ x, IsCompl (S.car x) (T.car x)) :
    IsCompl ((sinkSubPi S).map (sumIn V i)) ((sinkSubPi T).map (sumIn V i)) := by
  refine isCompl_of_forall (fun v hv hv' => ?_) (fun v => ?_)
  · obtain ⟨p, hp, rfl⟩ := hv
    obtain ⟨q, hq, hpq⟩ := hv'
    let z0 : sinkL V i i := ⟨(0, p - q), (mem_sinkL_of_eq V i rfl _).2 ⟨rfl, by
      show sumIn V i (p - q) = 0
      rw [map_sub, hpq, sub_self]⟩⟩
    obtain ⟨s, hs, t, ht, hst⟩ := exists_add_of_isCompl (hST i) z0
    have hs1 : s.1.2 ∈ sinkSubPi S := mem_sinkSubPi.2 (sinkSub_pi_mem S hs)
    have ht1 : t.1.2 ∈ sinkSubPi T := mem_sinkSubPi.2 (sinkSub_pi_mem T ht)
    have hs0 : sumIn V i s.1.2 = 0 := ((mem_sinkL_of_eq V i rfl _).1 s.2).2
    have hst2 : s.1.2 + t.1.2 = p - q := congrArg (fun w : sinkL V i i => w.1.2) hst
    have hr : p - s.1.2 = q + t.1.2 := by
      have h1 : p - s.1.2 = (p - q) - s.1.2 + q := by abel
      rw [h1, ← hst2]; abel
    have h0 : p - s.1.2 = 0 :=
      sinkSubPi_disjoint hST (sub_mem hp hs1) (hr ▸ add_mem hq ht1)
    have : p = s.1.2 := sub_eq_zero.1 h0
    rw [this]; exact hs0
  · obtain ⟨r, rfl⟩ := hsurj v
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_sinkSubPi_add hST r
    exact ⟨sumIn V i a, ⟨a, ha, rfl⟩, sumIn V i b, ⟨b, hb, rfl⟩, (map_add _ _ _).symm⟩

theorem sinkSub_isCompl (hsurj : Function.Surjective (sumIn V i)) (hST : ∀ x, IsCompl (S.car x) (T.car x))
    (x : Q) : IsCompl ((sinkSub S).carrier x) ((sinkSub T).carrier x) := by
  by_cases hx : x = i
  · subst hx
    rw [sinkSub_carrier_self, sinkSub_carrier_self]
    exact sinkSub_compl_self hsurj hST
  · rw [sinkSub_carrier_ne S hx, sinkSub_carrier_ne T hx]
    exact sinkSubAt_compl hST hx

theorem car_eq_bot_of_sinkSubAt (hA : ∀ x, x ≠ i → sinkSubAt V i hi S x = ⊥) (x : Q) : S.car x = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_cases hx : x = i
  · subst hx
    have hz2 : z.1.2 = 0 := by
      funext e
      have := mem_sinkSubPi.1 (mem_sinkSubPi.2 (sinkSub_pi_mem S hz)) e
      rw [hA e.1 (ne_of_arrow_sink hi e.2), Submodule.mem_bot] at this
      exact this
    have hz1 : z.1.1 = 0 := ((mem_sinkL_of_eq V x rfl _).1 z.2).1
    exact Subtype.ext (Prod.ext hz1 hz2)
  · have hz2 : z.1.2 = 0 := (mem_sinkL_of_ne V i hx _).1 z.2
    have := sinkSubAt_of_mem S hz hz2
    rw [hA x hx, Submodule.mem_bot] at this
    exact Subtype.ext (Prod.ext this hz2)

theorem sinkSub_eq_bot_imp {S : RevRep.Subrep (reflectSink V i hi)} (h : sinkSub S = ⊥) (x : Q) :
    S.car x = ⊥ := by
  refine car_eq_bot_of_sinkSubAt (fun y hy => ?_) x
  have := congrArg (fun S' : QRep.Subrep V => S'.carrier y) h
  simp only [QRep.Subrep.bot_carrier] at this
  rw [← sinkSub_carrier_ne S hy]
  exact this

/-- **Proposition 5.30 (sink).** If `V` is indecomposable and `i` is a sink, and `V` is not the simple
representation at `i`, then `F_i^+ V` is indecomposable. (The book's statement also covers `V` the simple
representation, where `F_i^+ V = 0`.) -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem reflectSink_isIndecomposable (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSink V i hi) := by
  have hsurj : Function.Surjective (sumIn V i) :=
    (isSimpleAt_or_surjective_sumIn V i hi hV).resolve_left hne
  refine ⟨fun heq => ?_, fun S T hST => ?_⟩
  · have hsub : ∀ x, Subsingleton (sinkL V i x) := fun x => by
      have h1 := congrArg (fun S' : @QRep.Subrep k Q _ (reversedAt i) (reflectSink V i hi) =>
        @QRep.Subrep.carrier k Q _ (reversedAt i) _ S' x) heq
      simp only [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier] at h1
      exact subsingleton_of_bot_eq_top h1
    have hVx : ∀ x, x ≠ i → Subsingleton (V.obj x) := fun x hx => by
      have := hsub x
      refine Function.Injective.subsingleton (f := fun u : V.obj x =>
        (⟨(u, 0), (mem_sinkL_of_ne V i hx _).2 rfl⟩ : sinkL V i x)) ?_
      intro u u' h
      exact congrArg Prod.fst (congrArg Subtype.val h)
    have : ∀ e : InArrows i, Subsingleton (V.obj e.1) := fun e => hVx e.1 (ne_of_arrow_sink hi e.2)
    have hVi : Subsingleton (V.obj i) := hsurj.subsingleton
    apply hV.1
    apply QRep.Subrep.ext
    intro x
    rw [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier]
    by_cases hx : x = i
    · subst hx; exact bot_eq_top_of_subsingleton'
    · have := hVx x hx; exact bot_eq_top_of_subsingleton'
  · rcases hV.2 (sinkSub S) (sinkSub T) (sinkSub_isCompl hsurj hST) with h | h
    · left
      refine @QRep.Subrep.ext k Q _ (reversedAt i) _ S _ fun x => ?_
      exact sinkSub_eq_bot_imp h x
    · right
      refine @QRep.Subrep.ext k Q _ (reversedAt i) _ T _ fun x => ?_
      exact sinkSub_eq_bot_imp h x

end Prop530Sink

/-! ### Proposition 5.30, source case -/

theorem ne_of_arrow_source {i j : Q} (hi : Quiver.IsSource i) (a : i ⟶ j) : j ≠ i := by
  rintro rfl
  exact (hi _).false a

section Prop530Source

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)] (hi : Quiver.IsSource i)

/-- The part of a subrepresentation `S` of `F_i^- V` at the vertex `x`, seen inside `V_x`. -/
def sourceSubAt (S : RevRep.Subrep (reflectSource V i hi)) (x : Q) : Submodule k (V.obj x) :=
  ((S.car x).map (sourceL V i x).subtype).comap (LinearMap.inl k (V.obj x) (outCoker V i))

/-- The part of a subrepresentation `S` of `F_i^- V` at the vertex `i`, seen inside the cokernel. -/
def sourceSubCoker (S : RevRep.Subrep (reflectSource V i hi)) : Submodule k (outCoker V i) :=
  ((S.car i).map (sourceL V i i).subtype).comap (LinearMap.inr k (V.obj i) (outCoker V i))

variable {V i hi}

theorem mem_sourceSubAt {S : RevRep.Subrep (reflectSource V i hi)} {x : Q} {u : V.obj x} :
    u ∈ sourceSubAt V i hi S x ↔ ∃ z : sourceL V i x, z ∈ S.car x ∧ z.1 = (u, 0) :=
  Iff.rfl

theorem mem_sourceSubCoker {S : RevRep.Subrep (reflectSource V i hi)} {c : outCoker V i} :
    c ∈ sourceSubCoker V i hi S ↔ ∃ z : sourceL V i i, z ∈ S.car i ∧ z.1 = (0, c) :=
  Iff.rfl

omit [Fintype (OutArrows i)] in
theorem sourceMap_revOut (hi : Quiver.IsSource i) {x : Q} (a : i ⟶ x) (z : sourceL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) x i (PSum.inr ⟨a, Or.inr rfl⟩) z).1 =
      (0, Submodule.mkQ (LinearMap.range (outMap V i)) (Pi.single ⟨x, a⟩ z.1.1)) := by
  rw [reflectSource_map_inr]
  simp [sourceRev]

omit [Fintype (OutArrows i)] in
theorem sourceMap_keep (hi : Quiver.IsSource i) {x y : Q} (a : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i)
    (z : sourceL V i x) :
    (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) x y (PSum.inl ⟨a, hx, hy⟩) z).1 =
      (V.map a z.1.1, 0) := by
  refine (reflectSource_map_inl hi a hx hy z).trans ?_
  simp [sourceKeep]

theorem sourceSubAt_of_mem (S : RevRep.Subrep (reflectSource V i hi)) {x : Q} {z : sourceL V i x}
    (hz : z ∈ S.car x) (h2 : z.1.2 = 0) : z.1.1 ∈ sourceSubAt V i hi S x :=
  mem_sourceSubAt.2 ⟨z, hz, Prod.ext rfl h2⟩

/-- The part of `S` away from `i`, as a subspace of `⨁_{i → j} V_j`. -/
def sourceSubPi (S : RevRep.Subrep (reflectSource V i hi)) : Submodule k (outProd V i) :=
  Submodule.pi Set.univ fun e : OutArrows i => sourceSubAt V i hi S e.1

theorem mem_sourceSubPi {S : RevRep.Subrep (reflectSource V i hi)} {p : outProd V i} :
    p ∈ sourceSubPi S ↔ ∀ e : OutArrows i, p e ∈ sourceSubAt V i hi S e.1 := by
  simp [sourceSubPi, Submodule.mem_pi]

theorem mkQ_single_mem (S : RevRep.Subrep (reflectSource V i hi)) (e : OutArrows i)
    {u : V.obj e.1} (hu : u ∈ sourceSubAt V i hi S e.1) :
    Submodule.mkQ (LinearMap.range (outMap V i)) (Pi.single e u) ∈ sourceSubCoker V i hi S := by
  obtain ⟨z, hz, hz1⟩ := mem_sourceSubAt.1 hu
  have hm := S.map_mem' (PSum.inr ⟨e.2, Or.inr rfl⟩ : @Quiver.Hom Q (reversedAt i) e.1 i) hz
  refine mem_sourceSubCoker.2 ⟨_, hm, ?_⟩
  rw [sourceMap_revOut hi e.2 z, hz1]

theorem mkQ_mem_of_pi (S : RevRep.Subrep (reflectSource V i hi)) {p : outProd V i}
    (hp : p ∈ sourceSubPi S) :
    Submodule.mkQ (LinearMap.range (outMap V i)) p ∈ sourceSubCoker V i hi S := by
  have h1 : p = ∑ e, Pi.single e (p e) := (Finset.univ_sum_single p).symm
  rw [h1, map_sum]
  exact Submodule.sum_mem _ fun e _ => mkQ_single_mem S e (mem_sourceSubPi.1 hp e)

/-- The subrepresentation of `V` obtained from a subrepresentation `S` of `F_i^- V` (assuming `V_i → ⨁ V_j` is
injective): the same subspaces away from `i`, and the preimage of `⨁ S_j` at `i`. -/
def sourceSub (S : RevRep.Subrep (reflectSource V i hi)) : QRep.Subrep V where
  carrier := Function.update (fun x => sourceSubAt V i hi S x) i ((sourceSubPi S).comap (outMap V i))
  map_mem := by
    intro x y a z hz
    by_cases hx : x = i
    · subst hx
      have hy : y ≠ x := ne_of_arrow_source hi a
      rw [Function.update_of_ne hy]
      rw [Function.update_self] at hz
      exact mem_sourceSubPi.1 hz ⟨y, a⟩
    · rw [Function.update_of_ne hx] at hz
      have hy : y ≠ i := by
        rintro rfl
        exact (hi x).false a
      rw [Function.update_of_ne hy]
      obtain ⟨z', hz', hz'1⟩ := mem_sourceSubAt.1 hz
      refine mem_sourceSubAt.2 ⟨_, S.map_mem' (PSum.inl ⟨a, hx, hy⟩ : @Quiver.Hom Q (reversedAt i) x y) hz', ?_⟩
      rw [sourceMap_keep hi a hx hy, hz'1]

theorem sourceSub_carrier_self (S : RevRep.Subrep (reflectSource V i hi)) :
    (sourceSub S).carrier i = (sourceSubPi S).comap (outMap V i) :=
  Function.update_self i _ (fun x => sourceSubAt V i hi S x)

theorem sourceSub_carrier_ne (S : RevRep.Subrep (reflectSource V i hi)) {x : Q} (hx : x ≠ i) :
    (sourceSub S).carrier x = sourceSubAt V i hi S x :=
  Function.update_of_ne hx _ (fun x => sourceSubAt V i hi S x)

variable {S T : RevRep.Subrep (reflectSource V i hi)}

theorem sourceSubAt_compl (hST : ∀ x, IsCompl (S.car x) (T.car x)) {x : Q} (hx : x ≠ i) :
    IsCompl (sourceSubAt V i hi S x) (sourceSubAt V i hi T x) := by
  refine isCompl_of_forall (fun u hS hT => ?_) (fun u => ?_)
  · obtain ⟨z, hz, hz1⟩ := mem_sourceSubAt.1 hS
    obtain ⟨z', hz', hz1'⟩ := mem_sourceSubAt.1 hT
    have : z = z' := Subtype.ext (hz1.trans hz1'.symm)
    subst this
    have h0 := eq_zero_of_isCompl' (hST x) hz hz'
    rw [h0] at hz1
    exact (congrArg Prod.fst hz1).symm
  · let z0 : sourceL V i x := ⟨(u, 0), (mem_sourceL_of_ne V i hx _).2 rfl⟩
    obtain ⟨s, hs, t, ht, hst⟩ := exists_add_of_isCompl (hST x) z0
    have hs2 : s.1.2 = 0 := (mem_sourceL_of_ne V i hx _).1 s.2
    have ht2 : t.1.2 = 0 := (mem_sourceL_of_ne V i hx _).1 t.2
    refine ⟨s.1.1, sourceSubAt_of_mem S hs hs2, t.1.1, sourceSubAt_of_mem T ht ht2, ?_⟩
    exact congrArg (fun w : sourceL V i x => w.1.1) hst

theorem sourceSubPi_disjoint (hST : ∀ x, IsCompl (S.car x) (T.car x)) {r : outProd V i}
    (h1 : r ∈ sourceSubPi S) (h2 : r ∈ sourceSubPi T) : r = 0 := by
  funext e
  exact eq_zero_of_isCompl' (sourceSubAt_compl hST (ne_of_arrow_source hi e.2))
    (mem_sourceSubPi.1 h1 e) (mem_sourceSubPi.1 h2 e)

theorem exists_sourceSubPi_add (hST : ∀ x, IsCompl (S.car x) (T.car x)) (r : outProd V i) :
    ∃ a ∈ sourceSubPi S, ∃ b ∈ sourceSubPi T, a + b = r := by
  choose a ha b hb hab using fun e : OutArrows i =>
    exists_add_of_isCompl (sourceSubAt_compl hST (ne_of_arrow_source hi e.2)) (r e)
  exact ⟨a, mem_sourceSubPi.2 ha, b, mem_sourceSubPi.2 hb, funext hab⟩

theorem sourceSubCoker_disjoint (hST : ∀ x, IsCompl (S.car x) (T.car x)) {c : outCoker V i}
    (h1 : c ∈ sourceSubCoker V i hi S) (h2 : c ∈ sourceSubCoker V i hi T) : c = 0 := by
  obtain ⟨z, hz, hz1⟩ := mem_sourceSubCoker.1 h1
  obtain ⟨z', hz', hz1'⟩ := mem_sourceSubCoker.1 h2
  have : z = z' := Subtype.ext (hz1.trans hz1'.symm)
  subst this
  have h0 := eq_zero_of_isCompl' (hST i) hz hz'
  rw [h0] at hz1
  exact (congrArg Prod.snd hz1).symm

theorem sourceSub_compl_self (hinj : Function.Injective (outMap V i))
    (hST : ∀ x, IsCompl (S.car x) (T.car x)) :
    IsCompl ((sourceSubPi S).comap (outMap V i)) ((sourceSubPi T).comap (outMap V i)) := by
  refine isCompl_of_forall (fun v hv hv' => ?_) (fun v => ?_)
  · have h0 := sourceSubPi_disjoint hST hv hv'
    exact hinj (by rw [h0, map_zero])
  · obtain ⟨s, hs, t, ht, hst⟩ := exists_sourceSubPi_add hST (outMap V i v)
    have hsum : Submodule.mkQ (LinearMap.range (outMap V i)) s +
        Submodule.mkQ (LinearMap.range (outMap V i)) t = 0 := by
      rw [← map_add, hst]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨v, rfl⟩
    have hs' : Submodule.mkQ (LinearMap.range (outMap V i)) s =
        -Submodule.mkQ (LinearMap.range (outMap V i)) t := eq_neg_of_add_eq_zero_left hsum
    have hs0 : Submodule.mkQ (LinearMap.range (outMap V i)) s = 0 :=
      sourceSubCoker_disjoint hST (mkQ_mem_of_pi S hs) (hs' ▸ neg_mem (mkQ_mem_of_pi T ht))
    obtain ⟨vS, hvS⟩ := (Submodule.Quotient.mk_eq_zero _).1 hs0
    refine ⟨vS, ?_, v - vS, ?_, by abel⟩
    · show outMap V i vS ∈ sourceSubPi S
      rw [hvS]; exact hs
    · show outMap V i (v - vS) ∈ sourceSubPi T
      rw [map_sub, hvS, ← hst]
      simpa using ht

theorem sourceSub_isCompl (hinj : Function.Injective (outMap V i)) (hST : ∀ x, IsCompl (S.car x) (T.car x))
    (x : Q) : IsCompl ((sourceSub S).carrier x) ((sourceSub T).carrier x) := by
  by_cases hx : x = i
  · subst hx
    rw [sourceSub_carrier_self, sourceSub_carrier_self]
    exact sourceSub_compl_self hinj hST
  · rw [sourceSub_carrier_ne S hx, sourceSub_carrier_ne T hx]
    exact sourceSubAt_compl hST hx

theorem car_eq_bot_of_sourceSubAt (hST : ∀ x, IsCompl (S.car x) (T.car x))
    (hA : ∀ x, x ≠ i → sourceSubAt V i hi S x = ⊥) (x : Q) : S.car x = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_cases hx : x = i
  · subst hx
    -- every component of `T` is everything
    have hT : ∀ e : OutArrows x, sourceSubAt V x hi T e.1 = ⊤ := by
      intro e
      have h := sourceSubAt_compl hST (ne_of_arrow_source hi e.2)
      rw [hA e.1 (ne_of_arrow_source hi e.2)] at h
      refine eq_top_iff.2 fun u _ => ?_
      obtain ⟨a, ha, b, hb, hab⟩ := exists_add_of_isCompl h u
      rw [Submodule.mem_bot] at ha
      rw [ha, zero_add] at hab
      rw [← hab]; exact hb
    have hc : z.1.2 ∈ sourceSubCoker V x hi T := by
      obtain ⟨p, hp⟩ := Submodule.mkQ_surjective (LinearMap.range (outMap V x)) z.1.2
      rw [← hp]
      exact mkQ_mem_of_pi T (mem_sourceSubPi.2 fun e => by rw [hT e]; trivial)
    obtain ⟨z', hz', hz1'⟩ := mem_sourceSubCoker.1 hc
    have hz1 : z.1.1 = 0 := ((mem_sourceL_of_eq V x rfl _).1 z.2)
    have : z' = z := Subtype.ext (hz1'.trans (Prod.ext hz1.symm rfl))
    subst this
    exact eq_zero_of_isCompl' (hST x) hz hz'
  · have hz2 : z.1.2 = 0 := (mem_sourceL_of_ne V i hx _).1 z.2
    have := sourceSubAt_of_mem S hz hz2
    rw [hA x hx, Submodule.mem_bot] at this
    exact Subtype.ext (Prod.ext this hz2)

theorem sourceSub_eq_bot_imp (hST : ∀ x, IsCompl (S.car x) (T.car x)) (h : sourceSub S = ⊥) (x : Q) :
    S.car x = ⊥ := by
  refine car_eq_bot_of_sourceSubAt hST (fun y hy => ?_) x
  have := congrArg (fun S' : QRep.Subrep V => S'.carrier y) h
  simp only [QRep.Subrep.bot_carrier] at this
  rw [← sourceSub_carrier_ne S hy]
  exact this

/-- **Proposition 5.30 (source).** If `V` is indecomposable and `i` is a source, and `V` is not the simple
representation at `i`, then `F_i^- V` is indecomposable. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem reflectSource_isIndecomposable (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSource V i hi) := by
  have hinj : Function.Injective (outMap V i) :=
    (isSimpleAt_or_injective_outMap V i hi hV).resolve_left hne
  refine ⟨fun heq => ?_, fun S T hST => ?_⟩
  · have hsub : ∀ x, Subsingleton (sourceL V i x) := fun x => by
      have h1 := congrArg (fun S' : @QRep.Subrep k Q _ (reversedAt i) (reflectSource V i hi) =>
        @QRep.Subrep.carrier k Q _ (reversedAt i) _ S' x) heq
      simp only [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier] at h1
      exact subsingleton_of_bot_eq_top h1
    have hVx : ∀ x, x ≠ i → Subsingleton (V.obj x) := fun x hx => by
      have := hsub x
      refine Function.Injective.subsingleton (f := fun u : V.obj x =>
        (⟨(u, 0), (mem_sourceL_of_ne V i hx _).2 rfl⟩ : sourceL V i x)) ?_
      intro u u' h
      exact congrArg Prod.fst (congrArg Subtype.val h)
    have : ∀ e : OutArrows i, Subsingleton (V.obj e.1) := fun e => hVx e.1 (ne_of_arrow_source hi e.2)
    have hVi : Subsingleton (V.obj i) := hinj.subsingleton
    apply hV.1
    apply QRep.Subrep.ext
    intro x
    rw [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier]
    by_cases hx : x = i
    · subst hx; exact bot_eq_top_of_subsingleton'
    · have := hVx x hx; exact bot_eq_top_of_subsingleton'
  · rcases hV.2 (sourceSub S) (sourceSub T) (sourceSub_isCompl hinj hST) with h | h
    · left
      refine @QRep.Subrep.ext k Q _ (reversedAt i) _ S _ fun x => ?_
      exact sourceSub_eq_bot_imp hST h x
    · right
      refine @QRep.Subrep.ext k Q _ (reversedAt i) _ T _ fun x => ?_
      exact sourceSub_eq_bot_imp (fun x => (hST x).symm) h x

end Prop530Source

/-! ### Proposition 5.29: the double reflection -/

/-- The identification of an arrow `x ⟶ y` of `Q` with an arrow of `(Q_i)_i` (the quiver obtained by reversing
the arrows at `i` twice). -/
def toRR (i : Q) {x y : Q} (a : x ⟶ y) : @Quiver.Hom Q (@reversedAt Q (reversedAt i) i) x y :=
  if h : x ≠ i ∧ y ≠ i then PSum.inl ⟨PSum.inl ⟨a, h⟩, h⟩
  else PSum.inr ⟨PSum.inr ⟨a, by
      by_contra hc
      exact h ⟨fun hx => hc (Or.inr hx), fun hy => hc (Or.inl hy)⟩⟩, by
      by_contra hc
      exact h ⟨fun hx => hc (Or.inl hx), fun hy => hc (Or.inr hy)⟩⟩

theorem toRR_of_ne {i x y : Q} (a : x ⟶ y) (hx : x ≠ i) (hy : y ≠ i) :
    toRR i a = PSum.inl ⟨PSum.inl ⟨a, hx, hy⟩, hx, hy⟩ := by
  simp [toRR, hx, hy]

theorem toRR_of_eq_right {i x y : Q} (a : x ⟶ y) (hy : y = i) :
    toRR i a = PSum.inr ⟨PSum.inr ⟨a, Or.inl hy⟩, Or.inr hy⟩ := by
  have : ¬ (x ≠ i ∧ y ≠ i) := fun h => h.2 hy
  simp [toRR, this]

theorem toRR_of_eq_left {i x y : Q} (a : x ⟶ y) (hx : x = i) :
    toRR i a = PSum.inr ⟨PSum.inr ⟨a, Or.inr hx⟩, Or.inl hx⟩ := by
  have : ¬ (x ≠ i ∧ y ≠ i) := fun h => h.1 hx
  simp [toRR, this]

instance revObjAddCommGroup {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] {i : Q}
    (W : @QRep.{u, v, w, a} k Q _ (reversedAt i)) (x : Q) :
    AddCommGroup (@QRep.obj k Q _ (reversedAt i) W x) :=
  @QRep.addCommGroup k Q _ (reversedAt i) W x

instance revObjModule {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] {i : Q}
    (W : @QRep.{u, v, w, a} k Q _ (reversedAt i)) (x : Q) :
    Module k (@QRep.obj k Q _ (reversedAt i) W x) :=
  @QRep.module k Q _ (reversedAt i) W x

instance revrevObjAddCommGroup {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] {i : Q}
    (W : @QRep.{u, v, w, a} k Q _ (@reversedAt Q (reversedAt i) i)) (x : Q) :
    AddCommGroup (@QRep.obj k Q _ (@reversedAt Q (reversedAt i) i) W x) :=
  @QRep.addCommGroup k Q _ (@reversedAt Q (reversedAt i) i) W x

instance revrevObjModule {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q] {i : Q}
    (W : @QRep.{u, v, w, a} k Q _ (@reversedAt Q (reversedAt i) i)) (x : Q) :
    Module k (@QRep.obj k Q _ (@reversedAt Q (reversedAt i) i) W x) :=
  @QRep.module k Q _ (@reversedAt Q (reversedAt i) i) W x

/-- The quiver `(Q_i)_i`. -/
abbrev revrev (i : Q) : Quiver.{a} Q := @reversedAt Q (reversedAt i) i

/-- Equivalence of a representation `V` of `Q` with a representation `X` of `(Q_i)_i`, transported along the
identification of arrows `toRR`: linear equivalences of the spaces at each vertex, commuting with the maps. -/
def RevRevIso.{w'} (V : QRep.{u, v, w, a} k Q) {i : Q}
    (X : @QRep.{u, v, w', a} k Q _ (revrev i)) : Prop :=
  ∃ e : ∀ x, (@QRep.obj k Q _ (revrev i) X x) ≃ₗ[k] V.obj x,
    ∀ {x y : Q} (a : x ⟶ y) (z : @QRep.obj k Q _ (revrev i) X x),
      e y (@QRep.map k Q _ (revrev i) X x y (toRR i a) z) = V.map a (e x z)

theorem isSource_reversedAt {i : Q} (hi : Quiver.IsSink i) : @Quiver.IsSource Q (reversedAt i) i := by
  intro j
  refine ⟨fun e => ?_⟩
  rcases e with ⟨e, h1, h2⟩ | ⟨e, h⟩
  · exact h2 rfl
  · exact (hi j).false e

theorem isSink_reversedAt {i : Q} (hi : Quiver.IsSource i) : @Quiver.IsSink Q (reversedAt i) i := by
  intro j
  refine ⟨fun e => ?_⟩
  rcases e with ⟨e, h1, h2⟩ | ⟨e, h⟩
  · exact h1 rfl
  · exact (hi j).false e

section Prop529Sink

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)] (hi : Quiver.IsSink i)

/-- The arrow `i ⟶ j` of `Q_i` given by an arrow `j ⟶ i` of `Q`. -/
def revOutOfIn (e : InArrows i) : @OutArrows Q (reversedAt i) i := ⟨e.1, PSum.inr ⟨e.2, Or.inl rfl⟩⟩

theorem revOutOfIn_injective : Function.Injective (revOutOfIn (Q := Q) i) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  simp only [revOutOfIn, PSigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have h1 := PSum.inr.inj (eq_of_heq h)
  have h2 : a = a' := congrArg Subtype.val h1
  subst h2
  rfl

theorem revOutOfIn_surjective : Function.Surjective (revOutOfIn (Q := Q) i) := by
  rintro ⟨j, e⟩
  rcases e with ⟨e, h1, h2⟩ | ⟨e, h⟩
  · exact (h1 rfl).elim
  · exact ⟨⟨j, e⟩, rfl⟩

/-- The comparison map `⨁_{i → j in Q_i} (F_i^+ V)_j → ⨁_{j → i in Q} V_j`. -/
def sinkT : (@outProd k _ Q (reversedAt i) (reflectSink V i hi) i) →ₗ[k] inProd V i :=
  LinearMap.pi fun e : InArrows i =>
    ((LinearMap.fst k (V.obj e.1) (inProd V i)).comp (sinkL V i e.1).subtype).comp
      (LinearMap.proj (R := k)
        (φ := fun e' : @OutArrows Q (reversedAt i) i => @QRep.obj k Q _ (reversedAt i) (reflectSink V i hi) e'.1)
        (revOutOfIn i e))

theorem sinkT_apply (p : @outProd k _ Q (reversedAt i) (reflectSink V i hi) i) (e : InArrows i) :
    sinkT V i hi p e = (p (revOutOfIn i e)).1.1 := rfl

end Prop529Sink

section Prop529Sink2

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)] (hi : Quiver.IsSink i)

/-- The cokernel at the vertex `i` for the second reflection (of `F_i^+ V`). -/
abbrev rOutCoker : Type _ := @outCoker k _ Q (reversedAt i) (reflectSink V i hi) i

/-- The ambient subspace at `x` for the second reflection. -/
abbrev rSourceL (x : Q) : Submodule k ((sinkL V i x) × rOutCoker V i hi) :=
  @sourceL k _ Q (reversedAt i) (reflectSink V i hi) i x

theorem rmem_sourceL_of_eq {x : Q} (h : x = i) (z : (sinkL V i x) × rOutCoker V i hi) :
    z ∈ rSourceL V i hi x ↔ z.1 = 0 :=
  @mem_sourceL_of_eq k _ Q (reversedAt i) (reflectSink V i hi) i x h z

theorem rmem_sourceL_of_ne {x : Q} (h : x ≠ i) (z : (sinkL V i x) × rOutCoker V i hi) :
    z ∈ rSourceL V i hi x ↔ z.2 = 0 :=
  @mem_sourceL_of_ne k _ Q (reversedAt i) (reflectSink V i hi) i x h z

theorem sinkT_outMap (z : sinkL V i i) :
    sinkT V i hi (@outMap k _ Q (reversedAt i) (reflectSink V i hi) i z) = z.1.2 := by
  funext e
  rw [sinkT_apply]
  exact congrArg Prod.fst (sinkMap_revIn hi e.2 z)

theorem sinkT_injective : Function.Injective (sinkT V i hi) := by
  intro p p' h
  funext e
  obtain ⟨e0, rfl⟩ := revOutOfIn_surjective i e
  have h0 := congrFun h e0
  rw [sinkT_apply, sinkT_apply] at h0
  have hne := ne_of_arrow_sink hi e0.2
  apply Subtype.ext
  refine Prod.ext h0 ?_
  rw [(mem_sinkL_of_ne V i hne _).1 (p (revOutOfIn i e0)).2, (mem_sinkL_of_ne V i hne _).1 (p' (revOutOfIn i e0)).2]

theorem sinkT_surjective : Function.Surjective (sinkT V i hi) := by
  intro r
  refine ⟨fun e : @OutArrows Q (reversedAt i) i => match e with
    | ⟨j, PSum.inl ⟨a, h1, h2⟩⟩ => (h1 rfl).elim
    | ⟨j, PSum.inr ⟨a, h⟩⟩ =>
        (⟨(r ⟨j, a⟩, 0), (mem_sinkL_of_ne V i (ne_of_arrow_sink hi a) _).2 rfl⟩ : sinkL V i j), ?_⟩
  funext e
  rfl

/-- The map from the cokernel of `F_i^+ V`'s outgoing map at `i` to `V_i`, induced by the sum map. -/
def sinkPhi : rOutCoker V i hi →ₗ[k] V.obj i :=
  Submodule.liftQ _ ((sumIn V i).comp (sinkT V i hi)) (by
    rintro _ ⟨z, rfl⟩
    exact (congrArg (sumIn V i) (sinkT_outMap V i hi z)).trans ((mem_sinkL_of_eq V i rfl _).1 z.2).2)

theorem sinkPhi_mk (p : @outProd k _ Q (reversedAt i) (reflectSink V i hi) i) :
    sinkPhi V i hi (Submodule.Quotient.mk p) = sumIn V i (sinkT V i hi p) := rfl

theorem sinkPhi_injective : Function.Injective (sinkPhi V i hi) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
  induction c using Submodule.Quotient.induction_on with
  | _ p =>
    rw [sinkPhi_mk] at hc
    let z0 : sinkL V i i := ⟨(0, sinkT V i hi p), (mem_sinkL_of_eq V i rfl _).2 ⟨rfl, hc⟩⟩
    have hz : @outMap k _ Q (reversedAt i) (reflectSink V i hi) i z0 = p :=
      sinkT_injective V i hi (by rw [sinkT_outMap])
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨z0, hz⟩

theorem sinkPhi_surjective (hsurj : Function.Surjective (sumIn V i)) : Function.Surjective (sinkPhi V i hi) := by
  intro v
  obtain ⟨r, hr⟩ := hsurj v
  obtain ⟨p, hp⟩ := sinkT_surjective V i hi r
  exact ⟨Submodule.Quotient.mk p, by rw [sinkPhi_mk, hp, hr]⟩

omit [Fintype (InArrows i)] in
/-- The linear map `V_i → V_x` which is the identity for `x = i` and zero otherwise. -/
def iota (x : Q) : V.obj i →ₗ[k] V.obj x :=
  if h : i = x then by subst h; exact LinearMap.id else 0

omit [Fintype (InArrows i)] in
theorem iota_self : iota V i i = LinearMap.id := by
  simp [iota]

omit [Fintype (InArrows i)] in
theorem iota_ne {x : Q} (hx : x ≠ i) : iota V i x = 0 := by
  have : ¬ i = x := fun h => hx h.symm
  simp [iota, this]

/-- The map from the space at `x` of `F_i^- F_i^+ V` to `V_x`. -/
def sinkPsi (x : Q) : rSourceL V i hi x →ₗ[k] V.obj x :=
  ((LinearMap.fst k (V.obj x) (inProd V i)).comp (sinkL V i x).subtype).comp
      ((LinearMap.fst k (sinkL V i x) (rOutCoker V i hi)).comp (rSourceL V i hi x).subtype) +
  (iota V i x).comp ((sinkPhi V i hi).comp
      ((LinearMap.snd k (sinkL V i x) (rOutCoker V i hi)).comp (rSourceL V i hi x).subtype))

theorem sinkPsi_apply (x : Q) (z : rSourceL V i hi x) :
    sinkPsi V i hi x z = z.1.1.1.1 + iota V i x (sinkPhi V i hi z.1.2) := rfl

end Prop529Sink2

section Prop529Sink3

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (InArrows i)] (hi : Quiver.IsSink i)

theorem sinkPsi_bijective (hsurj : Function.Surjective (sumIn V i)) (x : Q) :
    Function.Bijective (sinkPsi V i hi x) := by
  by_cases hx : x = i
  · have hx' : i = x := hx.symm
    subst hx'
    have key : ∀ z : rSourceL V i hi i, sinkPsi V i hi i z = sinkPhi V i hi z.1.2 := by
      intro z
      have h0 : z.1.1 = 0 := (rmem_sourceL_of_eq V i hi rfl _).1 z.2
      have h1 : z.1.1.1.1 = 0 := by rw [h0]; rfl
      rw [sinkPsi_apply, iota_self, h1]
      simp
    refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun v => ?_⟩
    · rw [key] at hz
      have h2 : z.1.2 = 0 := (injective_iff_map_eq_zero _).1 (sinkPhi_injective V i hi) _ hz
      have h0 : z.1.1 = 0 := (rmem_sourceL_of_eq V i hi rfl _).1 z.2
      exact Subtype.ext (Prod.ext h0 h2)
    · obtain ⟨c, hc⟩ := sinkPhi_surjective V i hi hsurj v
      exact ⟨⟨(0, c), (rmem_sourceL_of_eq V i hi rfl _).2 rfl⟩, by rw [key]; exact hc⟩
  · have key : ∀ z : rSourceL V i hi x, sinkPsi V i hi x z = z.1.1.1.1 := by
      intro z
      rw [sinkPsi_apply, iota_ne V i hx]
      simp
    refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun u => ?_⟩
    · rw [key] at hz
      have h2 : z.1.2 = 0 := (rmem_sourceL_of_ne V i hi hx _).1 z.2
      have h3 : z.1.1.1.2 = 0 := (mem_sinkL_of_ne V i hx _).1 z.1.1.2
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hz h3)) h2)
    · refine ⟨⟨(⟨(u, 0), (mem_sinkL_of_ne V i hx _).2 rfl⟩, 0), (rmem_sourceL_of_ne V i hi hx _).2 rfl⟩, ?_⟩
      rw [key]

/-- The linear equivalences realising Proposition 5.29 at each vertex. -/
def sinkE (hsurj : Function.Surjective (sumIn V i)) (x : Q) : rSourceL V i hi x ≃ₗ[k] V.obj x :=
  LinearEquiv.ofBijective (sinkPsi V i hi x) (sinkPsi_bijective V i hi hsurj x)

theorem sinkT_single (e0 : InArrows i) (w : sinkL V i e0.1) :
    sinkT V i hi (Pi.single (revOutOfIn i e0) w : @outProd k _ Q (reversedAt i) (reflectSink V i hi) i) =
      Pi.single e0 w.1.1 := by
  funext e
  rw [sinkT_apply]
  by_cases he : e = e0
  · subst he
    have h2 := Pi.single_eq_same (M := fun e' : @OutArrows Q (reversedAt i) i =>
      @QRep.obj k Q _ (reversedAt i) (reflectSink V i hi) e'.1) (revOutOfIn i e) w
    exact (congrArg (fun z : sinkL V i e.1 => z.1.1) h2).trans (by simp)
  · have hne : revOutOfIn i e ≠ revOutOfIn i e0 := fun h => he (revOutOfIn_injective i h)
    have h2 := Pi.single_eq_of_ne (M := fun e' : @OutArrows Q (reversedAt i) i =>
      @QRep.obj k Q _ (reversedAt i) (reflectSink V i hi) e'.1) hne w
    exact (congrArg (fun z : sinkL V i e.1 => z.1.1) h2).trans (by simp [Pi.single_eq_of_ne he]; rfl)

theorem sumIn_single (e0 : InArrows i) (u : V.obj e0.1) : sumIn V i (Pi.single e0 u) = V.map e0.2 u := by
  rw [sumIn_apply, Finset.sum_eq_single e0]
  · simp
  · intro e _ he; simp [Pi.single_eq_of_ne he]
  · simp

theorem sinkPsi_comm (hsurj : Function.Surjective (sumIn V i)) {x y : Q} (a : x ⟶ y)
    (z : rSourceL V i hi x) :
    sinkE V i hi hsurj y
      (@QRep.map k Q _ (revrev i) (@reflectSource k _ Q (reversedAt i) (reflectSink V i hi) i
        (isSource_reversedAt hi)) x y (toRR i a) z) = V.map a (sinkE V i hi hsurj x z) := by
  by_cases hx : x = i
  · have hx' : i = x := hx.symm
    subst hx'
    exact ((hi y).false a).elim
  have hz2 : z.1.2 = 0 := (rmem_sourceL_of_ne V i hi hx _).1 z.2
  have hxz : sinkE V i hi hsurj x z = z.1.1.1.1 := by
    show sinkPsi V i hi x z = _
    rw [sinkPsi_apply, iota_ne V i hx, hz2]
    simp
  rw [hxz]
  by_cases hy : y = i
  · have hy' : i = y := hy.symm
    subst hy'
    let z' : rSourceL V i hi i := @QRep.map k Q _ (revrev i)
      (@reflectSource k _ Q (reversedAt i) (reflectSink V i hi) i (isSource_reversedAt hi)) x i
      (PSum.inr ⟨PSum.inr ⟨a, Or.inl rfl⟩, Or.inr rfl⟩) z
    have h1 : z'.1 = (0, Submodule.mkQ (LinearMap.range (@outMap k _ Q (reversedAt i) (reflectSink V i hi) i))
        (Pi.single (⟨x, PSum.inr ⟨a, Or.inl rfl⟩⟩ : @OutArrows Q (reversedAt i) i) z.1.1)) :=
      @sourceMap_revOut k _ Q (reversedAt i) (reflectSink V i hi) i (isSource_reversedAt hi) x
        (PSum.inr ⟨a, Or.inl rfl⟩) z
    have e1 : z'.1.1 = 0 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    have e3 : z'.1.1.1.1 = 0 := by rw [e1]; rfl
    have key : sinkE V i hi hsurj i z' = V.map a z.1.1.1.1 := by
      show sinkPsi V i hi i z' = _
      rw [sinkPsi_apply, iota_self, e3]
      simp only [zero_add, LinearMap.id_apply]
      rw [e2]
      exact (sinkPhi_mk V i hi (Pi.single (revOutOfIn i ⟨x, a⟩) z.1.1)).trans
        ((congrArg (sumIn V i) (sinkT_single V i hi ⟨x, a⟩ z.1.1)).trans (sumIn_single V i ⟨x, a⟩ _))
    rw [toRR_of_eq_right a rfl]
    exact key
  · let z' : rSourceL V i hi y := @QRep.map k Q _ (revrev i)
      (@reflectSource k _ Q (reversedAt i) (reflectSink V i hi) i (isSource_reversedAt hi)) x y
      (PSum.inl ⟨PSum.inl ⟨a, hx, hy⟩, hx, hy⟩) z
    have h1 : z'.1 = (@QRep.map k Q _ (reversedAt i) (reflectSink V i hi) x y (PSum.inl ⟨a, hx, hy⟩) z.1.1, 0) :=
      @sourceMap_keep k _ Q (reversedAt i) (reflectSink V i hi) i (isSource_reversedAt hi) x y
        (PSum.inl ⟨a, hx, hy⟩) hx hy z
    have e1 : z'.1.1 = @QRep.map k Q _ (reversedAt i) (reflectSink V i hi) x y (PSum.inl ⟨a, hx, hy⟩) z.1.1 :=
      congrArg Prod.fst h1
    have e2 : z'.1.2 = 0 := congrArg Prod.snd h1
    have e3 : z'.1.1.1.1 = V.map a z.1.1.1.1 := by
      rw [e1]
      exact congrArg Prod.fst (sinkMap_keep hi a hx hy z.1.1)
    have key : sinkE V i hi hsurj y z' = V.map a z.1.1.1.1 := by
      show sinkPsi V i hi y z' = _
      rw [sinkPsi_apply, e2, e3, map_zero, map_zero, add_zero]
    rw [toRR_of_ne a hx hy]
    exact key

/-- **Proposition 5.29 (sink).** If `i` is a sink and the sum map `⨁_{j → i} V_j → V_i` is surjective, then
`F_i^- F_i^+ V` is isomorphic to `V`, the identification of `(Q_i)_i` with `Q` being the canonical one (`toRR`). -/
@[kb "etingof2011" "Proposition 5.29, p. 91"]
theorem reflectSource_reflectSink_iso (hsurj : Function.Surjective (sumIn V i)) :
    RevRevIso V (@reflectSource k _ Q (reversedAt i) (reflectSink V i hi) i (isSource_reversedAt hi)) :=
  ⟨sinkE V i hi hsurj, fun a z => sinkPsi_comm V i hi hsurj a z⟩

end Prop529Sink3

section SigmaDefs

variable (i : Q)

/-- The arrow `j ⟶ i` of `Q_i` given by an arrow `i ⟶ j` of `Q`. -/
def revInOfOut (e : OutArrows i) : @InArrows Q (reversedAt i) i := ⟨e.1, PSum.inr ⟨e.2, Or.inr rfl⟩⟩

theorem revInOfOut_injective : Function.Injective (revInOfOut (Q := Q) i) := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  simp only [revInOfOut, PSigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have h1 := PSum.inr.inj (eq_of_heq h)
  have h2 : a = a' := congrArg Subtype.val h1
  subst h2
  rfl

theorem revInOfOut_surjective : Function.Surjective (revInOfOut (Q := Q) i) := by
  rintro ⟨j, e⟩
  rcases e with ⟨e, h1, h2⟩ | ⟨e, h⟩
  · exact (h2 rfl).elim
  · exact ⟨⟨j, e⟩, rfl⟩

/-- The arrows of `Q_i` entering `i` are in bijection with the arrows of `Q` leaving `i`. -/
noncomputable instance fintypeInArrowsRev [Fintype (OutArrows i)] : Fintype (@InArrows Q (reversedAt i) i) :=
  Fintype.ofBijective (revInOfOut i) ⟨revInOfOut_injective i, revInOfOut_surjective i⟩

end SigmaDefs

/-! #### Proposition 5.29, source case -/

section Prop529Source

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)] (hi : Quiver.IsSource i)

/-- The product of the spaces at the sources of the arrows entering `i` in `Q_i`, for `F_i^- V`. -/
abbrev rInProd : Type _ := @inProd k _ Q (reversedAt i) (reflectSource V i hi) i

/-- The ambient subspace at `x` for the reflection of `F_i^- V` at the sink `i` of `Q_i`. -/
abbrev rSinkL (x : Q) : Submodule k ((sourceL V i x) × rInProd V i hi) :=
  @sinkL k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i) x

/-- The comparison map `⨁_{j → i in Q_i} (F_i^- V)_j → ⨁_{i → j in Q} V_j`. -/
def srcS : rInProd V i hi →ₗ[k] outProd V i :=
  LinearMap.pi fun e : OutArrows i =>
    ((LinearMap.fst k (V.obj e.1) (outCoker V i)).comp (sourceL V i e.1).subtype).comp
      (LinearMap.proj (R := k)
        (φ := fun e' : @InArrows Q (reversedAt i) i => @QRep.obj k Q _ (reversedAt i) (reflectSource V i hi) e'.1)
        (revInOfOut i e))

theorem srcS_apply (p : rInProd V i hi) (e : OutArrows i) : srcS V i hi p e = (p (revInOfOut i e)).1.1 := rfl

theorem rsumIn_val (p : rInProd V i hi) :
    (@sumIn k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i) p).1 =
      (0, Submodule.mkQ (LinearMap.range (outMap V i)) (srcS V i hi p)) := by
  have hsum := @sumIn_apply k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i) p
  have h1 : ∀ e : OutArrows i,
      (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) e.1 i (revInOfOut i e).2 (p (revInOfOut i e))).1 =
        (0, Submodule.mkQ (LinearMap.range (outMap V i)) (Pi.single e (p (revInOfOut i e)).1.1)) :=
    fun e => sourceMap_revOut hi e.2 (p (revInOfOut i e))
  have hbij : Function.Bijective (revInOfOut i) := ⟨revInOfOut_injective i, revInOfOut_surjective i⟩
  refine (congrArg (sourceL V i i).subtype hsum).trans ?_
  refine (map_sum (sourceL V i i).subtype _ _).trans ?_
  refine (Fintype.sum_bijective (revInOfOut i) hbij
    (fun e : OutArrows i => (sourceL V i i).subtype
      (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) e.1 i (revInOfOut i e).2 (p (revInOfOut i e)))) _
    (fun _ => rfl)).symm.trans ?_
  refine (Finset.sum_congr rfl fun e _ => h1 e).trans ?_
  refine Prod.ext (by simp [Prod.fst_sum]) ?_
  simp only [Prod.snd_sum]
  rw [← map_sum]
  congr 1
  exact Finset.univ_sum_single (srcS V i hi p)

end Prop529Source

section Prop529Source2

variable (V : QRep.{u, v, w, a} k Q) (i : Q) [Fintype (OutArrows i)] (hi : Quiver.IsSource i)

theorem rsumIn_eq_zero_iff (p : rInProd V i hi) :
    @sumIn k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i) p = 0 ↔
      Submodule.mkQ (LinearMap.range (outMap V i)) (srcS V i hi p) = 0 := by
  have h1 := rsumIn_val V i hi p
  constructor
  · intro h
    rw [h] at h1
    exact (congrArg Prod.snd h1).symm
  · intro h
    refine Subtype.ext ?_
    rw [h1, h]
    rfl

theorem rmem_sinkL_of_eq {x : Q} (h : x = i) (z : (sourceL V i x) × rInProd V i hi) :
    z ∈ rSinkL V i hi x ↔ z.1 = 0 ∧ Submodule.mkQ (LinearMap.range (outMap V i)) (srcS V i hi z.2) = 0 := by
  refine (@mem_sinkL_of_eq k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i) x h z).trans ?_
  refine and_congr Iff.rfl ?_
  subst h
  exact rsumIn_eq_zero_iff V x hi z.2

theorem rmem_sinkL_of_ne {x : Q} (h : x ≠ i) (z : (sourceL V i x) × rInProd V i hi) :
    z ∈ rSinkL V i hi x ↔ z.2 = 0 :=
  @mem_sinkL_of_ne k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i) x h z

theorem srcS_injective : Function.Injective (srcS V i hi) := by
  intro p p' h
  funext e'
  obtain ⟨e, rfl⟩ := revInOfOut_surjective i e'
  have h0 := congrFun h e
  rw [srcS_apply, srcS_apply] at h0
  have hne := ne_of_arrow_source hi e.2
  apply Subtype.ext
  refine Prod.ext h0 ?_
  rw [(mem_sourceL_of_ne V i hne _).1 (p (revInOfOut i e)).2, (mem_sourceL_of_ne V i hne _).1 (p' (revInOfOut i e)).2]

theorem exists_leftInverse (hinj : Function.Injective (outMap V i)) :
    ∃ g : outProd V i →ₗ[k] V.obj i, ∀ v, g (outMap V i v) = v := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (outMap V i) (LinearMap.ker_eq_bot.2 hinj)
  exact ⟨g, fun v => LinearMap.congr_fun hg v⟩

/-- A left inverse of the injective map `outMap`. -/
def srcG (hinj : Function.Injective (outMap V i)) : outProd V i →ₗ[k] V.obj i :=
  (exists_leftInverse V i hinj).choose

theorem srcG_outMap (hinj : Function.Injective (outMap V i)) (v : V.obj i) :
    srcG V i hinj (outMap V i v) = v :=
  (exists_leftInverse V i hinj).choose_spec v

/-- The map from the space at `x` of `F_i^+ F_i^- V` to `V_x`. -/
def srcPsi (hinj : Function.Injective (outMap V i)) (x : Q) : rSinkL V i hi x →ₗ[k] V.obj x :=
  ((LinearMap.fst k (V.obj x) (outCoker V i)).comp (sourceL V i x).subtype).comp
      ((LinearMap.fst k (sourceL V i x) (rInProd V i hi)).comp (rSinkL V i hi x).subtype) +
  (iota V i x).comp ((srcG V i hinj).comp ((srcS V i hi).comp
      ((LinearMap.snd k (sourceL V i x) (rInProd V i hi)).comp (rSinkL V i hi x).subtype)))

theorem srcPsi_apply (hinj : Function.Injective (outMap V i)) (x : Q) (z : rSinkL V i hi x) :
    srcPsi V i hi hinj x z = z.1.1.1.1 + iota V i x (srcG V i hinj (srcS V i hi z.1.2)) := rfl

theorem exists_outMap_of_mem (z : rSinkL V i hi i) : ∃ v, srcS V i hi z.1.2 = outMap V i v := by
  have h := ((rmem_sinkL_of_eq V i hi rfl _).1 z.2).2
  obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).1 h
  exact ⟨v, hv.symm⟩

theorem srcPsi_bijective (hinj : Function.Injective (outMap V i)) (x : Q) :
    Function.Bijective (srcPsi V i hi hinj x) := by
  by_cases hx : x = i
  · have hx' : i = x := hx.symm
    subst hx'
    have key : ∀ z : rSinkL V i hi i, srcPsi V i hi hinj i z = srcG V i hinj (srcS V i hi z.1.2) := by
      intro z
      have h0 : z.1.1 = 0 := ((rmem_sinkL_of_eq V i hi rfl _).1 z.2).1
      have h1 : z.1.1.1.1 = 0 := by rw [h0]; rfl
      rw [srcPsi_apply, iota_self, h1]
      simp
    refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun v => ?_⟩
    · rw [key] at hz
      obtain ⟨v, hv⟩ := exists_outMap_of_mem V i hi z
      rw [hv, srcG_outMap] at hz
      subst hz
      have h2 : z.1.2 = 0 := srcS_injective V i hi (by rw [hv, map_zero, map_zero])
      have h0 : z.1.1 = 0 := ((rmem_sinkL_of_eq V i hi rfl _).1 z.2).1
      exact Subtype.ext (Prod.ext h0 h2)
    · let p0 : rInProd V i hi := fun e' : @InArrows Q (reversedAt i) i => match e' with
        | ⟨j, PSum.inl ⟨a, h1, h2⟩⟩ => (h2 rfl).elim
        | ⟨j, PSum.inr ⟨a, h⟩⟩ =>
            (⟨(outMap V i v ⟨j, a⟩, 0), (mem_sourceL_of_ne V i (ne_of_arrow_source hi a) _).2 rfl⟩ :
              sourceL V i j)
      have hp0 : srcS V i hi p0 = outMap V i v := by
        funext e
        rfl
      refine ⟨⟨(0, p0), (rmem_sinkL_of_eq V i hi rfl _).2 ⟨rfl, ?_⟩⟩, ?_⟩
      · show Submodule.mkQ (LinearMap.range (outMap V i)) (srcS V i hi p0) = 0
        rw [hp0]
        exact (Submodule.Quotient.mk_eq_zero _).2 ⟨v, rfl⟩
      · rw [key]
        show srcG V i hinj (srcS V i hi p0) = v
        rw [hp0, srcG_outMap]
  · have key : ∀ z : rSinkL V i hi x, srcPsi V i hi hinj x z = z.1.1.1.1 := by
      intro z
      have h2 : z.1.2 = 0 := (rmem_sinkL_of_ne V i hi hx _).1 z.2
      rw [srcPsi_apply, h2, map_zero, map_zero, map_zero, add_zero]
    refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun u => ?_⟩
    · rw [key] at hz
      have h2 : z.1.2 = 0 := (rmem_sinkL_of_ne V i hi hx _).1 z.2
      have h3 : z.1.1.1.2 = 0 := (mem_sourceL_of_ne V i hx _).1 z.1.1.2
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hz h3)) h2)
    · refine ⟨⟨(⟨(u, 0), (mem_sourceL_of_ne V i hx _).2 rfl⟩, 0), (rmem_sinkL_of_ne V i hi hx _).2 rfl⟩, ?_⟩
      rw [key]

/-- The linear equivalences realising the dual form of Proposition 5.29 at each vertex. -/
def srcE (hinj : Function.Injective (outMap V i)) (x : Q) : rSinkL V i hi x ≃ₗ[k] V.obj x :=
  LinearEquiv.ofBijective (srcPsi V i hi hinj x) (srcPsi_bijective V i hi hinj x)

theorem srcPsi_comm (hinj : Function.Injective (outMap V i)) {x y : Q} (a : x ⟶ y) (z : rSinkL V i hi x) :
    srcE V i hi hinj y
      (@QRep.map k Q _ (revrev i) (@reflectSink k _ Q (reversedAt i) (reflectSource V i hi) i
        (fintypeInArrowsRev i) (isSink_reversedAt hi)) x y (toRR i a) z) = V.map a (srcE V i hi hinj x z) := by
  by_cases hy : y = i
  · have hy' : i = y := hy.symm
    subst hy'
    exact ((hi x).false a).elim
  by_cases hx : x = i
  · have hx' : i = x := hx.symm
    subst hx'
    obtain ⟨v, hv⟩ := exists_outMap_of_mem V i hi z
    have hz1 : z.1.1 = 0 := ((rmem_sinkL_of_eq V i hi rfl _).1 z.2).1
    have hz1' : z.1.1.1.1 = 0 := by rw [hz1]; rfl
    let z' : rSinkL V i hi y := @QRep.map k Q _ (revrev i)
      (@reflectSink k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i)
        (isSink_reversedAt hi)) i y (PSum.inr ⟨PSum.inr ⟨a, Or.inr rfl⟩, Or.inl rfl⟩) z
    have h1 : z'.1 = (z.1.2 (revInOfOut i ⟨y, a⟩), 0) :=
      @sinkMap_revIn k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i)
        (isSink_reversedAt hi) y (PSum.inr ⟨a, Or.inr rfl⟩) z
    have e1 : z'.1.1 = z.1.2 (revInOfOut i ⟨y, a⟩) := congrArg Prod.fst h1
    have e2 : z'.1.2 = 0 := congrArg Prod.snd h1
    have e3 : z'.1.1.1.1 = srcS V i hi z.1.2 ⟨y, a⟩ := by rw [e1]; rfl
    have key : srcE V i hi hinj y z' = V.map a (srcE V i hi hinj i z) := by
      show srcPsi V i hi hinj y z' = V.map a (srcPsi V i hi hinj i z)
      rw [srcPsi_apply, srcPsi_apply, e2, e3, hz1', hv, srcG_outMap]
      simp only [zero_add, map_zero, add_zero, iota_self, LinearMap.id_apply]
      rfl
    rw [toRR_of_eq_left a rfl]
    exact key
  · let z' : rSinkL V i hi y := @QRep.map k Q _ (revrev i)
      (@reflectSink k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i)
        (isSink_reversedAt hi)) x y (PSum.inl ⟨PSum.inl ⟨a, hx, hy⟩, hx, hy⟩) z
    have h1 : z'.1 = (@QRep.map k Q _ (reversedAt i) (reflectSource V i hi) x y (PSum.inl ⟨a, hx, hy⟩) z.1.1, 0) :=
      @sinkMap_keep k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i)
        (isSink_reversedAt hi) x y (PSum.inl ⟨a, hx, hy⟩) hx hy z
    have e1 : z'.1.1 = @QRep.map k Q _ (reversedAt i) (reflectSource V i hi) x y (PSum.inl ⟨a, hx, hy⟩) z.1.1 :=
      congrArg Prod.fst h1
    have e2 : z'.1.2 = 0 := congrArg Prod.snd h1
    have e3 : z'.1.1.1.1 = V.map a z.1.1.1.1 := by
      rw [e1]
      exact congrArg Prod.fst (sourceMap_keep hi a hx hy z.1.1)
    have key : srcE V i hi hinj y z' = V.map a (srcE V i hi hinj x z) := by
      show srcPsi V i hi hinj y z' = V.map a (srcPsi V i hi hinj x z)
      have hz2 : z.1.2 = 0 := (rmem_sinkL_of_ne V i hi hx _).1 z.2
      rw [srcPsi_apply, srcPsi_apply, e2, e3, hz2]
      simp only [map_zero, add_zero]
    rw [toRR_of_ne a hx hy]
    exact key

/-- **Proposition 5.29 (source).** If `i` is a source and `V_i → ⨁_{i → j} V_j` is injective, then
`F_i^+ F_i^- V` is isomorphic to `V`, the identification of `(Q_i)_i` with `Q` being the canonical one (`toRR`). -/
@[kb "etingof2011" "Proposition 5.29, p. 91"]
theorem reflectSink_reflectSource_iso (hinj : Function.Injective (outMap V i)) :
    RevRevIso V (@reflectSink k _ Q (reversedAt i) (reflectSource V i hi) i (fintypeInArrowsRev i)
      (isSink_reversedAt hi)) :=
  ⟨srcE V i hi hinj, fun a z => srcPsi_comm V i hi hinj a z⟩

end Prop529Source2

/-! ### Proposition 5.30 together with the dimension vectors -/

section Prop530Dim

variable {n : ℕ} [Quiver.{a} (Fin n)] [∀ x y : Fin n, Fintype (x ⟶ y)]
  (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- **Proposition 5.30 (sink, with dimension vectors).** For a quiver on `Fin n` with underlying graph `G`,
a finite-dimensional indecomposable representation `V` that is not the simple representation at a sink `i` is sent
by `F_i^+` to an indecomposable representation whose dimension vector is `s_i d(V)`. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem reflectSink_indecomposable_dimVec
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n) (hi : Quiver.IsSink i)
    (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSink V i hi) ∧
      (fun x => ((reflectSink V i hi).dimVec x : ℤ)) =
        Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) :=
  ⟨reflectSink_isIndecomposable hV hne,
    dimVec_reflectSink G hG V i hi
      ((isSimpleAt_or_surjective_sumIn V i hi hV).resolve_left hne)⟩

/-- **Proposition 5.30 (source, with dimension vectors).** The dual statement for a source `i`. -/
@[kb "etingof2011" "Proposition 5.30, p. 92"]
theorem reflectSource_indecomposable_dimVec
    (hG : ∀ x y : Fin n, Fintype.card (x ⟶ y) + Fintype.card (y ⟶ x) = if G.Adj x y then 1 else 0)
    (V : QRep k (Fin n)) [∀ j, Module.Finite k (V.obj j)] (i : Fin n) (hi : Quiver.IsSource i)
    (hV : V.IsIndecomposable) (hne : ¬ V.IsSimpleAt i) :
    RevRep.IsIndecomposable (reflectSource V i hi) ∧
      (fun x => ((reflectSource V i hi).dimVec x : ℤ)) =
        Roots.simpleReflection G i (fun x => (V.dimVec x : ℤ)) :=
  ⟨reflectSource_isIndecomposable hV hne,
    dimVec_reflectSource G hG V i hi
      ((isSimpleAt_or_injective_outMap V i hi hV).resolve_left hne)⟩

end Prop530Dim

end

end UndergradKB.RepresentationTheory
