import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.QuiverExamples
import UndergradKB.RepresentationTheory.ReflectionFunctors
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import UndergradKB.Common.Attr

/-! # Example 5.9: representations of the quiver `A₃` (Etingof et al., §5.1)

We treat the orientation `• → • ← •` (both outer vertices map into the middle one). A representation is given by
two linear maps `A : U → W` and `B : Y → W`; `A3Rep A B` builds it. We prove:

* the six representations with dimension vectors `(1,0,0)`, `(0,1,0)`, `(0,0,1)`, `(1,1,0)`, `(0,1,1)`, `(1,1,1)`
  (all nonzero maps being the identity) are indecomposable (`A3Rep.isIndecomposable_models`);
* they are pairwise non-isomorphic (`A3Rep.model_injective`);
* every indecomposable representation (of arbitrary dimension) is isomorphic to one of them
  (`a3_classification`). The proof follows the book: split off `ker A`, `ker B`, then the part of the middle
  space outside the intersection `im A ∩ im B`, then the part outside `im A + im B`, and finally decompose
  `im A ⊕ im B`.

The other orientation `• → • → •` of the book is not treated.

Example 5.10: for `D₄` with the subspace orientation (three arrows into the centre) we define the twelve
representations of the book (`D4Rep.model`) and prove that they are indecomposable
(`D4Rep.isIndecomposable_models`) and pairwise non-isomorphic (`D4Rep.model_injective`). That every indecomposable
representation is isomorphic to one of them (the triple of subspaces problem) is not proved.
-/

namespace UndergradKB.RepresentationTheory

noncomputable section

universe u

/-- The three vertices of `A₃`. -/
inductive A3V : Type
  | left
  | mid
  | right

/-- The two arrows of `A₃`, both ending at the middle vertex. -/
inductive A3Arrow : A3V → A3V → Type
  | l : A3Arrow A3V.left A3V.mid
  | r : A3Arrow A3V.right A3V.mid

instance : Quiver.{0} A3V := ⟨A3Arrow⟩

/-- The arrow from the left vertex to the middle vertex. -/
def a3l : A3V.left ⟶ A3V.mid := A3Arrow.l

/-- The arrow from the right vertex to the middle vertex. -/
def a3r : A3V.right ⟶ A3V.mid := A3Arrow.r

/-- The spaces of the representation attached to `U → W ← Y`. -/
def A3obj (U W Y : Type u) : A3V → Type u
  | A3V.left => U
  | A3V.mid => W
  | A3V.right => Y

section

variable (U W Y : Type u) (k : Type u) [Field k] [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [AddCommGroup Y] [Module k Y]

instance (i : A3V) : AddCommGroup (A3obj U W Y i) := by
  cases i
  · exact inferInstanceAs (AddCommGroup U)
  · exact inferInstanceAs (AddCommGroup W)
  · exact inferInstanceAs (AddCommGroup Y)

instance (i : A3V) : Module k (A3obj U W Y i) := by
  cases i
  · exact inferInstanceAs (Module k U)
  · exact inferInstanceAs (Module k W)
  · exact inferInstanceAs (Module k Y)

end

section Basics

variable {k : Type u} [Field k] {U W Y : Type u} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [AddCommGroup Y] [Module k Y]

/-- The representation `U → W ← Y` of `A₃` given by two linear maps. -/
def A3Rep (A : U →ₗ[k] W) (B : Y →ₗ[k] W) : QRep k A3V where
  obj := A3obj U W Y
  map := by
    intro i j a
    cases a
    · exact A
    · exact B

theorem A3Rep_dimVec_left (A : U →ₗ[k] W) (B : Y →ₗ[k] W) :
    (A3Rep A B).dimVec A3V.left = Module.finrank k U := rfl

theorem A3Rep_dimVec_mid (A : U →ₗ[k] W) (B : Y →ₗ[k] W) :
    (A3Rep A B).dimVec A3V.mid = Module.finrank k W := rfl

theorem A3Rep_dimVec_right (A : U →ₗ[k] W) (B : Y →ₗ[k] W) :
    (A3Rep A B).dimVec A3V.right = Module.finrank k Y := rfl

end Basics

/-! ### Subrepresentations and isomorphisms -/

section Sub

variable {k : Type u} [Field k]

/-- A subrepresentation of a representation of `A₃`, given by its three subspaces. -/
def a3Sub (V : QRep.{u, 0, u, 0} k A3V) (p : Submodule k (V.obj A3V.left)) (q : Submodule k (V.obj A3V.mid))
    (r : Submodule k (V.obj A3V.right)) (hp : ∀ z ∈ p, V.map a3l z ∈ q) (hr : ∀ z ∈ r, V.map a3r z ∈ q) :
    QRep.Subrep V where
  carrier := fun x => match x with
    | A3V.left => p
    | A3V.mid => q
    | A3V.right => r
  map_mem := by
    intro x y a z hz
    cases a
    · exact hp z hz
    · exact hr z hz

theorem a3_eq_bot {V : QRep.{u, 0, u, 0} k A3V} (S : QRep.Subrep V) (h1 : S.carrier A3V.left = ⊥)
    (h2 : S.carrier A3V.mid = ⊥) (h3 : S.carrier A3V.right = ⊥) : S = ⊥ := by
  apply QRep.Subrep.ext
  intro i
  cases i
  · exact h1
  · exact h2
  · exact h3

theorem a3_bot_eq_top {V : QRep.{u, 0, u, 0} k A3V} (h1 : Subsingleton (V.obj A3V.left))
    (h2 : Subsingleton (V.obj A3V.mid)) (h3 : Subsingleton (V.obj A3V.right)) :
    (⊥ : QRep.Subrep V) = ⊤ := by
  apply QRep.Subrep.ext
  intro i
  rw [QRep.Subrep.bot_carrier, QRep.Subrep.top_carrier]
  cases i
  · exact bot_eq_top_of_subsingleton'
  · exact bot_eq_top_of_subsingleton'
  · exact bot_eq_top_of_subsingleton'

/-- The basic splitting principle: two complementary subrepresentations of an indecomposable one, one of them
is zero. -/
theorem a3_split (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    {p p' : Submodule k (V.obj A3V.left)} {q q' : Submodule k (V.obj A3V.mid)}
    {r r' : Submodule k (V.obj A3V.right)} (hp : ∀ z ∈ p, V.map a3l z ∈ q) (hr : ∀ z ∈ r, V.map a3r z ∈ q)
    (hp' : ∀ z ∈ p', V.map a3l z ∈ q') (hr' : ∀ z ∈ r', V.map a3r z ∈ q')
    (cp : IsCompl p p') (cq : IsCompl q q') (cr : IsCompl r r') :
    (p = ⊥ ∧ q = ⊥ ∧ r = ⊥) ∨ (p' = ⊥ ∧ q' = ⊥ ∧ r' = ⊥) := by
  have hc : ∀ x, IsCompl ((a3Sub V p q r hp hr).carrier x) ((a3Sub V p' q' r' hp' hr').carrier x) := by
    intro x
    cases x
    · exact cp
    · exact cq
    · exact cr
  rcases hV.2 _ _ hc with h | h
  · left
    exact ⟨congrArg (fun S : QRep.Subrep V => S.carrier A3V.left) h,
      congrArg (fun S : QRep.Subrep V => S.carrier A3V.mid) h,
      congrArg (fun S : QRep.Subrep V => S.carrier A3V.right) h⟩
  · right
    exact ⟨congrArg (fun S : QRep.Subrep V => S.carrier A3V.left) h,
      congrArg (fun S : QRep.Subrep V => S.carrier A3V.mid) h,
      congrArg (fun S : QRep.Subrep V => S.carrier A3V.right) h⟩

/-- Two representations of `A₃` are isomorphic when linear equivalences of the three spaces intertwine the
maps. -/
theorem a3_isomorphic_of_equiv {V V' : QRep.{u, 0, u, 0} k A3V} (eU : V.obj A3V.left ≃ₗ[k] V'.obj A3V.left)
    (eW : V.obj A3V.mid ≃ₗ[k] V'.obj A3V.mid) (eY : V.obj A3V.right ≃ₗ[k] V'.obj A3V.right)
    (hA : ∀ z, eW (V.map a3l z) = V'.map a3l (eU z)) (hB : ∀ z, eW (V.map a3r z) = V'.map a3r (eY z)) :
    QRep.Isomorphic V V' := by
  refine ⟨⟨fun x => match x with
      | A3V.left => eU.toLinearMap
      | A3V.mid => eW.toLinearMap
      | A3V.right => eY.toLinearMap, ?_⟩,
    ⟨fun x => match x with
      | A3V.left => eU.symm.toLinearMap
      | A3V.mid => eW.symm.toLinearMap
      | A3V.right => eY.symm.toLinearMap, ?_⟩, ?_, ?_⟩
  · intro x y a
    cases a
    · exact LinearMap.ext fun z => hA z
    · exact LinearMap.ext fun z => hB z
  · intro x y a
    cases a
    · refine LinearMap.ext fun z => ?_
      show eW.symm (V'.map a3l z) = V.map a3l (eU.symm z)
      rw [LinearEquiv.symm_apply_eq, hA, LinearEquiv.apply_symm_apply]
    · refine LinearMap.ext fun z => ?_
      show eW.symm (V'.map a3r z) = V.map a3r (eY.symm z)
      rw [LinearEquiv.symm_apply_eq, hB, LinearEquiv.apply_symm_apply]
  · refine QRep.Hom.ext fun x => ?_
    cases x <;> exact LinearMap.ext fun z => by simp
  · refine QRep.Hom.ext fun x => ?_
    cases x <;> exact LinearMap.ext fun z => by simp

end Sub

/-! ### Linear algebra lemmas -/

section LinAlg

variable {k : Type u} [Field k]

theorem a3_isCompl_comap {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (hf : Function.Injective f) {I J : Submodule k N} (h : IsCompl I J)
    (hI : I ≤ LinearMap.range f) : IsCompl (I.comap f) (J.comap f) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : f x = 0 := by
      have := Submodule.disjoint_def.1 h.disjoint (f x) hx hx'
      exact this
    exact hf (by rw [h0, map_zero])
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : f x ∈ I ⊔ J := by rw [h.sup_eq_top]; trivial
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, ha⟩ := hI hi
    have hxa : x - a ∈ J.comap f := by
      show f (x - a) ∈ J
      rw [map_sub, ha, ← hij]
      simpa using hj
    have : x = a + (x - a) := by abel
    rw [this]
    refine Submodule.add_mem_sup ?_ hxa
    show f a ∈ I
    rw [ha]; exact hi

theorem a3_rank_one_of_split {M : Type*} [AddCommGroup M] [Module k M] [Nontrivial M]
    (h : ∀ p q : Submodule k M, IsCompl p q → p = ⊥ ∨ q = ⊥) : Module.rank k M = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span k {v})
  rw [rank_eq_one_iff]
  refine ⟨v, hv, fun w => ?_⟩
  rcases h _ _ hq with h | h
  · exfalso
    exact hv (by simpa using (Submodule.span_eq_bot.mp h) v (by simp))
  · have hq' : Submodule.span k {v} = ⊤ := by
      have := hq.sup_eq_top
      rwa [h, sup_bot_eq] at this
    have hw : w ∈ Submodule.span k {v} := by rw [hq']; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨r, hr⟩

theorem a3_bot_mem {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) {q : Submodule k N} : ∀ z ∈ (⊥ : Submodule k M), f z ∈ q := by
  intro z hz
  rw [Submodule.mem_bot] at hz
  rw [hz, map_zero]
  exact zero_mem _

theorem a3_top_mem {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) : ∀ z ∈ (⊤ : Submodule k M), f z ∈ (⊤ : Submodule k N) := fun _ _ => trivial

end LinAlg

/-! ### The six models -/

section Models

variable (k : Type u) [Field k]

/-- The representation `k → 0 ← 0`. -/
def A3Rep.d100 : QRep k A3V := A3Rep (0 : k →ₗ[k] PUnit.{u + 1}) (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1})

/-- The representation `0 → k ← 0`. -/
def A3Rep.d010 : QRep k A3V := A3Rep (0 : PUnit.{u + 1} →ₗ[k] k) (0 : PUnit.{u + 1} →ₗ[k] k)

/-- The representation `0 → 0 ← k`. -/
def A3Rep.d001 : QRep k A3V := A3Rep (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1}) (0 : k →ₗ[k] PUnit.{u + 1})

/-- The representation `k → k ← 0` (identity). -/
def A3Rep.d110 : QRep k A3V := A3Rep (LinearMap.id : k →ₗ[k] k) (0 : PUnit.{u + 1} →ₗ[k] k)

/-- The representation `0 → k ← k` (identity). -/
def A3Rep.d011 : QRep k A3V := A3Rep (0 : PUnit.{u + 1} →ₗ[k] k) (LinearMap.id : k →ₗ[k] k)

/-- The representation `k → k ← k` (identities). -/
def A3Rep.d111 : QRep k A3V := A3Rep (LinearMap.id : k →ₗ[k] k) (LinearMap.id : k →ₗ[k] k)

/-- The six representations, indexed by `Fin 6`. -/
def A3Rep.model : Fin 6 → QRep k A3V
  | 0 => A3Rep.d100 k
  | 1 => A3Rep.d010 k
  | 2 => A3Rep.d001 k
  | 3 => A3Rep.d110 k
  | 4 => A3Rep.d011 k
  | 5 => A3Rep.d111 k

end Models

/-! ### Indecomposability of the six models -/

section Indec

variable {k : Type u} [Field k]

/-- A space that is zero or one-dimensional. -/
def A3OneOrZero (k : Type u) [Field k] (M : Type u) [AddCommGroup M] [Module k M] : Prop :=
  Subsingleton M ∨ ∃ v : M, v ≠ 0 ∧ ∀ w, ∃ r : k, r • v = w

theorem a3_compl_cases {M : Type u} [AddCommGroup M] [Module k M] (h : A3OneOrZero k M)
    {S T : Submodule k M} (hST : IsCompl S T) : S = ⊥ ∨ T = ⊥ := by
  rcases h with h | h
  · exact Or.inl (Subsingleton.elim _ _)
  · exact rank_one_isCompl h hST

theorem a3_bot_of_subsingleton {M : Type*} [AddCommGroup M] [Module k M] (h : Subsingleton M)
    (p : Submodule k M) : p = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun x _ => Subsingleton.elim x 0

theorem a3_mixed {X Z : Type u} [AddCommGroup X] [Module k X] [AddCommGroup Z] [Module k Z] (f : X →ₗ[k] Z)
    (hf : Nontrivial X → Nontrivial Z → Function.Injective f) {S T : Submodule k X} {T' : Submodule k Z}
    (hST : IsCompl S T) (hS : S = ⊥) (hT' : T' = ⊥) (hmap : ∀ z ∈ T, f z ∈ T') :
    Subsingleton X ∨ Subsingleton Z := by
  by_contra hcon
  rw [not_or, not_subsingleton_iff_nontrivial, not_subsingleton_iff_nontrivial] at hcon
  obtain ⟨hX, hZ⟩ := hcon
  have hTtop : T = ⊤ := by
    have := hST.sup_eq_top
    rwa [hS, bot_sup_eq] at this
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  have hmem : f u ∈ T' := hmap u (by rw [hTtop]; trivial)
  rw [hT', Submodule.mem_bot] at hmem
  exact hu (hf hX hZ (by rw [hmem, map_zero]))

theorem a3_prop (sl tl sm tm sr tr ul um ur : Prop) (cl : sl ∨ tl) (cm : sm ∨ tm) (cr : sr ∨ tr)
    (hl : ul → sl ∧ tl) (hm : um → sm ∧ tm) (hr : ur → sr ∧ tr) (mA1 : sl → tm → ul ∨ um)
    (mA2 : tl → sm → ul ∨ um) (mB1 : sr → tm → ur ∨ um) (mB2 : tr → sm → ur ∨ um) (nW : ul ∨ ur ∨ ¬ um) :
    (sl ∧ sm ∧ sr) ∨ (tl ∧ tm ∧ tr) := by
  by_cases a : ul <;> by_cases b : um <;> by_cases c : ur <;>
    rcases cl with x | x <;> rcases cm with y | y <;> rcases cr with z | z <;> simp_all

theorem a3_isIndecomposable {U W Y : Type u} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    [AddCommGroup Y] [Module k Y] (A : U →ₗ[k] W) (B : Y →ₗ[k] W) (hU : A3OneOrZero k U)
    (hW : A3OneOrZero k W) (hY : A3OneOrZero k Y) (hnt : Nontrivial U ∨ Nontrivial W ∨ Nontrivial Y)
    (hA : Nontrivial U → Nontrivial W → Function.Injective A)
    (hB : Nontrivial Y → Nontrivial W → Function.Injective B)
    (hW' : Nontrivial U → Nontrivial Y → Nontrivial W) : (A3Rep A B).IsIndecomposable := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases hnt with hn | hn | hn
    · have h' : (⊥ : Submodule k U) = ⊤ := congrArg (fun S : QRep.Subrep (A3Rep A B) => S.carrier A3V.left) h
      exact bot_ne_top h'
    · have h' : (⊥ : Submodule k W) = ⊤ := congrArg (fun S : QRep.Subrep (A3Rep A B) => S.carrier A3V.mid) h
      exact bot_ne_top h'
    · have h' : (⊥ : Submodule k Y) = ⊤ :=
        congrArg (fun S : QRep.Subrep (A3Rep A B) => S.carrier A3V.right) h
      exact bot_ne_top h'
  · intro S T hST
    have cl : S.carrier A3V.left = ⊥ ∨ T.carrier A3V.left = ⊥ := a3_compl_cases hU (hST A3V.left)
    have cm : S.carrier A3V.mid = ⊥ ∨ T.carrier A3V.mid = ⊥ := a3_compl_cases hW (hST A3V.mid)
    have cr : S.carrier A3V.right = ⊥ ∨ T.carrier A3V.right = ⊥ := a3_compl_cases hY (hST A3V.right)
    have ul : Subsingleton U → S.carrier A3V.left = ⊥ ∧ T.carrier A3V.left = ⊥ :=
      fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩
    have um : Subsingleton W → S.carrier A3V.mid = ⊥ ∧ T.carrier A3V.mid = ⊥ :=
      fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩
    have ur : Subsingleton Y → S.carrier A3V.right = ⊥ ∧ T.carrier A3V.right = ⊥ :=
      fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩
    have mA1 : S.carrier A3V.left = ⊥ → T.carrier A3V.mid = ⊥ → Subsingleton U ∨ Subsingleton W :=
      fun hs ht => a3_mixed A hA (hST A3V.left) hs ht (fun z hz => T.map_mem a3l hz)
    have mA2 : T.carrier A3V.left = ⊥ → S.carrier A3V.mid = ⊥ → Subsingleton U ∨ Subsingleton W :=
      fun hs ht => a3_mixed A hA (hST A3V.left).symm hs ht (fun z hz => S.map_mem a3l hz)
    have mB1 : S.carrier A3V.right = ⊥ → T.carrier A3V.mid = ⊥ → Subsingleton Y ∨ Subsingleton W :=
      fun hs ht => a3_mixed B hB (hST A3V.right) hs ht (fun z hz => T.map_mem a3r hz)
    have mB2 : T.carrier A3V.right = ⊥ → S.carrier A3V.mid = ⊥ → Subsingleton Y ∨ Subsingleton W :=
      fun hs ht => a3_mixed B hB (hST A3V.right).symm hs ht (fun z hz => S.map_mem a3r hz)
    have nW : Subsingleton U ∨ Subsingleton Y ∨ ¬ Subsingleton W := by
      by_cases h1 : Subsingleton U
      · exact Or.inl h1
      by_cases h2 : Subsingleton Y
      · exact Or.inr (Or.inl h2)
      rw [not_subsingleton_iff_nontrivial] at h1 h2
      exact Or.inr (Or.inr (not_subsingleton_iff_nontrivial.2 (hW' h1 h2)))
    have key : (S.carrier A3V.left = ⊥ ∧ S.carrier A3V.mid = ⊥ ∧ S.carrier A3V.right = ⊥) ∨
        (T.carrier A3V.left = ⊥ ∧ T.carrier A3V.mid = ⊥ ∧ T.carrier A3V.right = ⊥) := by
      exact a3_prop _ _ _ _ _ _ _ _ _ cl cm cr ul um ur mA1 mA2 mB1 mB2 nW
    rcases key with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl (a3_eq_bot S h1 h2 h3)
    · exact Or.inr (a3_eq_bot T h1 h2 h3)

private theorem a3_oneOrZero_self : A3OneOrZero k k :=
  Or.inr ⟨1, one_ne_zero, fun w => ⟨w, by simp⟩⟩

private theorem a3_oneOrZero_punit : A3OneOrZero k PUnit.{u + 1} :=
  Or.inl inferInstance

private theorem a3_noPunit {M : Type u} [Subsingleton M] : ¬ Nontrivial M := by
  rw [not_nontrivial_iff_subsingleton]; infer_instance

/-- **Example 5.9** (part): the representation `k → 0 ← 0` of `A₃` is indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.d100_isIndecomposable : (A3Rep.d100 k).IsIndecomposable :=
  a3_isIndecomposable _ _ a3_oneOrZero_self a3_oneOrZero_punit a3_oneOrZero_punit (Or.inl inferInstance)
    (fun _ h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit)

/-- **Example 5.9** (part): the representation `0 → k ← 0` of `A₃` is indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.d010_isIndecomposable : (A3Rep.d010 k).IsIndecomposable :=
  a3_isIndecomposable _ _ a3_oneOrZero_punit a3_oneOrZero_self a3_oneOrZero_punit
    (Or.inr (Or.inl inferInstance)) (fun h => absurd h a3_noPunit) (fun h => absurd h a3_noPunit)
    (fun h => absurd h a3_noPunit)

/-- **Example 5.9** (part): the representation `0 → 0 ← k` of `A₃` is indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.d001_isIndecomposable : (A3Rep.d001 k).IsIndecomposable :=
  a3_isIndecomposable _ _ a3_oneOrZero_punit a3_oneOrZero_punit a3_oneOrZero_self
    (Or.inr (Or.inr inferInstance)) (fun h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit)
    (fun h => absurd h a3_noPunit)

/-- **Example 5.9** (part): the representation `k → k ← 0` of `A₃` is indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.d110_isIndecomposable : (A3Rep.d110 k).IsIndecomposable :=
  a3_isIndecomposable _ _ a3_oneOrZero_self a3_oneOrZero_self a3_oneOrZero_punit (Or.inl inferInstance)
    (fun _ _ => fun _ _ h => h) (fun h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit)

/-- **Example 5.9** (part): the representation `0 → k ← k` of `A₃` is indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.d011_isIndecomposable : (A3Rep.d011 k).IsIndecomposable :=
  a3_isIndecomposable _ _ a3_oneOrZero_punit a3_oneOrZero_self a3_oneOrZero_self
    (Or.inr (Or.inl inferInstance)) (fun h => absurd h a3_noPunit) (fun _ _ => fun _ _ h => h)
    (fun h => absurd h a3_noPunit)

/-- **Example 5.9** (part): the representation `k → k ← k` of `A₃` is indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.d111_isIndecomposable : (A3Rep.d111 k).IsIndecomposable :=
  a3_isIndecomposable _ _ a3_oneOrZero_self a3_oneOrZero_self a3_oneOrZero_self (Or.inl inferInstance)
    (fun _ _ => fun _ _ h => h) (fun _ _ => fun _ _ h => h) (fun _ _ => inferInstance)

/-- **Example 5.9** (part): all six representations are indecomposable. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.isIndecomposable_models (i : Fin 6) : (A3Rep.model k i).IsIndecomposable := by
  fin_cases i
  · exact A3Rep.d100_isIndecomposable
  · exact A3Rep.d010_isIndecomposable
  · exact A3Rep.d001_isIndecomposable
  · exact A3Rep.d110_isIndecomposable
  · exact A3Rep.d011_isIndecomposable
  · exact A3Rep.d111_isIndecomposable

end Indec

/-! ### The six models are pairwise non-isomorphic -/

section Distinct

variable (k : Type u) [Field k]

/-- The dimension at the left vertex of each model. -/
def A3Rep.dimLeft : Fin 6 → ℕ := ![1, 0, 0, 1, 0, 1]

/-- The dimension at the middle vertex of each model. -/
def A3Rep.dimMid : Fin 6 → ℕ := ![0, 1, 0, 1, 1, 1]

/-- The dimension at the right vertex of each model. -/
def A3Rep.dimRight : Fin 6 → ℕ := ![0, 0, 1, 0, 1, 1]

theorem A3Rep.dimVec_model (i : Fin 6) :
    (A3Rep.model k i).dimVec A3V.left = A3Rep.dimLeft i ∧
    (A3Rep.model k i).dimVec A3V.mid = A3Rep.dimMid i ∧
    (A3Rep.model k i).dimVec A3V.right = A3Rep.dimRight i := by
  fin_cases i <;> refine ⟨?_, ?_, ?_⟩ <;>
    first
    | exact Module.finrank_self k
    | exact Module.finrank_zero_of_subsingleton (R := k) (M := PUnit.{u + 1})

/-- **Example 5.9** (part): the six representations are pairwise non-isomorphic (they have different dimension
vectors, namely the six positive roots of `A₃`). -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem A3Rep.model_injective (i j : Fin 6) (h : QRep.Isomorphic (A3Rep.model k i) (A3Rep.model k j)) :
    i = j := by
  have h1 := (A3Rep.dimVec_model k i).1.symm.trans
    ((congrFun h.dimVec_eq A3V.left).trans (A3Rep.dimVec_model k j).1)
  have h2 := (A3Rep.dimVec_model k i).2.1.symm.trans
    ((congrFun h.dimVec_eq A3V.mid).trans (A3Rep.dimVec_model k j).2.1)
  have h3 := (A3Rep.dimVec_model k i).2.2.symm.trans
    ((congrFun h.dimVec_eq A3V.right).trans (A3Rep.dimVec_model k j).2.2)
  have key : ∀ i j : Fin 6, A3Rep.dimLeft i = A3Rep.dimLeft j → A3Rep.dimMid i = A3Rep.dimMid j →
      A3Rep.dimRight i = A3Rep.dimRight j → i = j := by decide
  exact key i j h1 h2 h3

end Distinct

/-! ### Classification -/

section Classify

variable {k : Type u} [Field k]

theorem a3_conc_left (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    (hm : Subsingleton (V.obj A3V.mid)) (hr : Subsingleton (V.obj A3V.right)) :
    QRep.Isomorphic V (A3Rep.d100 k) := by
  have hloop : IsEmpty (A3V.left ⟶ A3V.left) := ⟨fun a => by cases a⟩
  have hs : ∀ j, j ≠ A3V.left → Subsingleton (V.obj j) := by
    intro j hj
    cases j
    · exact absurd rfl hj
    · exact hm
    · exact hr
  have hrank := rank_eq_one_of_isIndecomposable_of_vanishing V A3V.left hloop hV hs
  have eU := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
  have : Subsingleton ((A3Rep.d100 k).obj A3V.mid) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  have : Subsingleton ((A3Rep.d100 k).obj A3V.right) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  exact a3_isomorphic_of_equiv eU (LinearEquiv.ofSubsingleton _ _) (LinearEquiv.ofSubsingleton _ _)
    (fun z => Subsingleton.elim _ _) (fun z => Subsingleton.elim _ _)

theorem a3_conc_right (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    (hl : Subsingleton (V.obj A3V.left)) (hm : Subsingleton (V.obj A3V.mid)) :
    QRep.Isomorphic V (A3Rep.d001 k) := by
  have hloop : IsEmpty (A3V.right ⟶ A3V.right) := ⟨fun a => by cases a⟩
  have hs : ∀ j, j ≠ A3V.right → Subsingleton (V.obj j) := by
    intro j hj
    cases j
    · exact hl
    · exact hm
    · exact absurd rfl hj
  have hrank := rank_eq_one_of_isIndecomposable_of_vanishing V A3V.right hloop hV hs
  have eY := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
  have : Subsingleton ((A3Rep.d001 k).obj A3V.left) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  have : Subsingleton ((A3Rep.d001 k).obj A3V.mid) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  exact a3_isomorphic_of_equiv (LinearEquiv.ofSubsingleton _ _) (LinearEquiv.ofSubsingleton _ _) eY
    (fun z => Subsingleton.elim _ _) (fun z => Subsingleton.elim _ _)

theorem a3_conc_mid (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    (hl : Subsingleton (V.obj A3V.left)) (hr : Subsingleton (V.obj A3V.right)) :
    QRep.Isomorphic V (A3Rep.d010 k) := by
  have hloop : IsEmpty (A3V.mid ⟶ A3V.mid) := ⟨fun a => by cases a⟩
  have hs : ∀ j, j ≠ A3V.mid → Subsingleton (V.obj j) := by
    intro j hj
    cases j
    · exact hl
    · exact absurd rfl hj
    · exact hr
  have hrank := rank_eq_one_of_isIndecomposable_of_vanishing V A3V.mid hloop hV hs
  have eW := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
  have : Subsingleton ((A3Rep.d010 k).obj A3V.left) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  have : Subsingleton ((A3Rep.d010 k).obj A3V.right) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  refine a3_isomorphic_of_equiv (LinearEquiv.ofSubsingleton _ _) eW (LinearEquiv.ofSubsingleton _ _)
    (fun z => ?_) (fun z => ?_)
  · rw [Subsingleton.elim z 0]; simp; exact map_zero eW
  · rw [Subsingleton.elim z 0]; simp; exact map_zero eW

theorem a3_iso_111 (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    (hA : Function.Bijective (V.map a3l)) (hB : Function.Bijective (V.map a3r)) :
    QRep.Isomorphic V (A3Rep.d111 k) := by
  have hnt : Nontrivial (V.obj A3V.mid) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hV.1 (a3_bot_eq_top hA.1.subsingleton hn hB.1.subsingleton)
  have hrank : Module.rank k (V.obj A3V.mid) = 1 := by
    apply a3_rank_one_of_split
    intro p q hpq
    have hp : p ≤ LinearMap.range (V.map a3l) := by
      rw [LinearMap.range_eq_top.2 hA.2]; exact le_top
    have hp2 : p ≤ LinearMap.range (V.map a3r) := by
      rw [LinearMap.range_eq_top.2 hB.2]; exact le_top
    rcases a3_split V hV (p := p.comap (V.map a3l)) (p' := q.comap (V.map a3l)) (q := p) (q' := q)
      (r := p.comap (V.map a3r)) (r' := q.comap (V.map a3r)) (fun z hz => hz) (fun z hz => hz)
      (fun z hz => hz) (fun z hz => hz) (a3_isCompl_comap _ hA.1 hpq hp) hpq
      (a3_isCompl_comap _ hB.1 hpq hp2) with h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2.1
  have eW : V.obj A3V.mid ≃ₗ[k] k := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
  exact a3_isomorphic_of_equiv ((LinearEquiv.ofBijective _ hA).trans eW) eW
    ((LinearEquiv.ofBijective _ hB).trans eW) (fun z => rfl) (fun z => rfl)

theorem a3_iso_011 (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    (hl : Subsingleton (V.obj A3V.left)) (hB : Function.Bijective (V.map a3r)) :
    QRep.Isomorphic V (A3Rep.d011 k) := by
  have hnt : Nontrivial (V.obj A3V.mid) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hV.1 (a3_bot_eq_top hl hn hB.1.subsingleton)
  have hrank : Module.rank k (V.obj A3V.mid) = 1 := by
    apply a3_rank_one_of_split
    intro p q hpq
    have hp2 : p ≤ LinearMap.range (V.map a3r) := by
      rw [LinearMap.range_eq_top.2 hB.2]; exact le_top
    rcases a3_split V hV (p := ⊥) (p' := ⊥) (q := p) (q' := q)
      (r := p.comap (V.map a3r)) (r' := q.comap (V.map a3r)) (a3_bot_mem _) (fun z hz => hz)
      (a3_bot_mem _) (fun z hz => hz) isCompl_bot_bot_of_subsingleton hpq
      (a3_isCompl_comap _ hB.1 hpq hp2) with h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2.1
  have eW : V.obj A3V.mid ≃ₗ[k] k := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
  have : Subsingleton ((A3Rep.d011 k).obj A3V.left) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  refine a3_isomorphic_of_equiv (LinearEquiv.ofSubsingleton _ _) eW
    ((LinearEquiv.ofBijective _ hB).trans eW) (fun z => ?_) (fun z => rfl)
  rw [Subsingleton.elim z 0]; simp; exact map_zero eW

theorem a3_iso_110 (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable)
    (hr : Subsingleton (V.obj A3V.right)) (hA : Function.Bijective (V.map a3l)) :
    QRep.Isomorphic V (A3Rep.d110 k) := by
  have hnt : Nontrivial (V.obj A3V.mid) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hV.1 (a3_bot_eq_top hA.1.subsingleton hn hr)
  have hrank : Module.rank k (V.obj A3V.mid) = 1 := by
    apply a3_rank_one_of_split
    intro p q hpq
    have hp : p ≤ LinearMap.range (V.map a3l) := by
      rw [LinearMap.range_eq_top.2 hA.2]; exact le_top
    rcases a3_split V hV (p := p.comap (V.map a3l)) (p' := q.comap (V.map a3l)) (q := p) (q' := q)
      (r := ⊥) (r' := ⊥) (fun z hz => hz) (a3_bot_mem _) (fun z hz => hz) (a3_bot_mem _)
      (a3_isCompl_comap _ hA.1 hpq hp) hpq isCompl_bot_bot_of_subsingleton with h | h
    · exact Or.inl h.2.1
    · exact Or.inr h.2.1
  have eW : V.obj A3V.mid ≃ₗ[k] k := (Module.nonempty_linearEquiv_iff_rank_eq_one.2 hrank).some.symm
  have : Subsingleton ((A3Rep.d110 k).obj A3V.right) := inferInstanceAs (Subsingleton PUnit.{u + 1})
  refine a3_isomorphic_of_equiv ((LinearEquiv.ofBijective _ hA).trans eW) eW
    (LinearEquiv.ofSubsingleton _ _) (fun z => rfl) (fun z => ?_)
  rw [Subsingleton.elim z 0]; simp; exact map_zero eW

/-- **Example 5.9.** Every indecomposable representation of the quiver `• → • ← •` (of any dimension) is
isomorphic to one of the six representations `A3Rep.model k i`, with dimension vectors the positive roots. Together
with `A3Rep.isIndecomposable_models` and `A3Rep.model_injective`, `A₃` has exactly six indecomposable
representations up to isomorphism. -/
@[kb "etingof2011" "Example 5.9, p. 81"]
theorem a3_classification (V : QRep.{u, 0, u, 0} k A3V) (hV : V.IsIndecomposable) :
    ∃ i : Fin 6, QRep.Isomorphic V (A3Rep.model k i) := by
  -- split off the kernel of `A`
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker (V.map a3l))
  rcases a3_split V hV (p := LinearMap.ker (V.map a3l)) (p' := C) (q := ⊥) (q' := ⊤) (r := ⊥) (r' := ⊤)
    (fun z hz => hz) (a3_bot_mem _) (fun _ _ => trivial) (fun _ _ => trivial) hC isCompl_bot_top
    isCompl_bot_top with ⟨hkerA, -, -⟩ | ⟨-, hm, hr⟩
  swap
  · exact ⟨0, a3_conc_left V hV (subsingleton_of_bot_eq_top hm.symm) (subsingleton_of_bot_eq_top hr.symm)⟩
  have hAinj : Function.Injective (V.map a3l) := LinearMap.ker_eq_bot.1 hkerA
  -- split off the kernel of `B`
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (LinearMap.ker (V.map a3r))
  rcases a3_split V hV (p := ⊥) (p' := ⊤) (q := ⊥) (q' := ⊤) (r := LinearMap.ker (V.map a3r)) (r' := C')
    (a3_bot_mem _) (fun z hz => hz) (fun _ _ => trivial) (fun _ _ => trivial) isCompl_bot_top
    isCompl_bot_top hC' with ⟨-, -, hkerB⟩ | ⟨hl, hm, -⟩
  swap
  · exact ⟨2, a3_conc_right V hV (subsingleton_of_bot_eq_top hl.symm) (subsingleton_of_bot_eq_top hm.symm)⟩
  have hBinj : Function.Injective (V.map a3r) := LinearMap.ker_eq_bot.1 hkerB
  -- split along the intersection of the images
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range (V.map a3l) ⊓ LinearMap.range (V.map a3r))
  rcases a3_split V hV (p := (LinearMap.range (V.map a3l) ⊓ LinearMap.range (V.map a3r)).comap (V.map a3l))
    (p' := W'.comap (V.map a3l)) (q := LinearMap.range (V.map a3l) ⊓ LinearMap.range (V.map a3r)) (q' := W')
    (r := (LinearMap.range (V.map a3l) ⊓ LinearMap.range (V.map a3r)).comap (V.map a3r))
    (r' := W'.comap (V.map a3r)) (fun z hz => hz) (fun z hz => hz) (fun z hz => hz) (fun z hz => hz)
    (a3_isCompl_comap _ hAinj hW' inf_le_left) hW' (a3_isCompl_comap _ hBinj hW' inf_le_right)
    with ⟨-, hI, -⟩ | ⟨-, hW0, -⟩
  swap
  · have hItop : LinearMap.range (V.map a3l) ⊓ LinearMap.range (V.map a3r) = ⊤ := by
      have := hW'.sup_eq_top
      rwa [hW0, sup_bot_eq] at this
    have hPtop : LinearMap.range (V.map a3l) = ⊤ := eq_top_iff.2 (by rw [← hItop]; exact inf_le_left)
    have hRtop : LinearMap.range (V.map a3r) = ⊤ := eq_top_iff.2 (by rw [← hItop]; exact inf_le_right)
    exact ⟨5, a3_iso_111 V hV ⟨hAinj, LinearMap.range_eq_top.1 hPtop⟩ ⟨hBinj, LinearMap.range_eq_top.1 hRtop⟩⟩
  -- split off the part of the middle space outside the sum of the images
  obtain ⟨W'', hW''⟩ := Submodule.exists_isCompl (LinearMap.range (V.map a3l) ⊔ LinearMap.range (V.map a3r))
  rcases a3_split V hV (p := ⊤) (p' := ⊥) (q := LinearMap.range (V.map a3l) ⊔ LinearMap.range (V.map a3r))
    (q' := W'') (r := ⊤) (r' := ⊥) (fun z _ => Submodule.mem_sup_left ⟨z, rfl⟩)
    (fun z _ => Submodule.mem_sup_right ⟨z, rfl⟩) (a3_bot_mem _) (a3_bot_mem _) isCompl_top_bot hW''
    isCompl_top_bot with ⟨hl, -, hr⟩ | ⟨-, hW0', -⟩
  · exact ⟨1, a3_conc_mid V hV (subsingleton_of_bot_eq_top hl.symm) (subsingleton_of_bot_eq_top hr.symm)⟩
  have hQ : LinearMap.range (V.map a3l) ⊔ LinearMap.range (V.map a3r) = ⊤ := by
    have := hW''.sup_eq_top
    rwa [hW0', sup_bot_eq] at this
  have hPR : IsCompl (LinearMap.range (V.map a3l)) (LinearMap.range (V.map a3r)) :=
    ⟨disjoint_iff.2 hI, codisjoint_iff.2 hQ⟩
  -- finally decompose `im A ⊕ im B`
  rcases a3_split V hV (p := ⊤) (p' := ⊥) (q := LinearMap.range (V.map a3l))
    (q' := LinearMap.range (V.map a3r)) (r := ⊥) (r' := ⊤) (fun z _ => ⟨z, rfl⟩) (a3_bot_mem _)
    (a3_bot_mem _) (fun z _ => ⟨z, rfl⟩) isCompl_top_bot hPR isCompl_bot_top
    with ⟨hl, hP0, -⟩ | ⟨-, hR0, hr⟩
  · have hRtop : LinearMap.range (V.map a3r) = ⊤ := by
      have := hPR.sup_eq_top
      rwa [hP0, bot_sup_eq] at this
    exact ⟨4, a3_iso_011 V hV (subsingleton_of_bot_eq_top hl.symm)
      ⟨hBinj, LinearMap.range_eq_top.1 hRtop⟩⟩
  · have hPtop : LinearMap.range (V.map a3l) = ⊤ := by
      have := hPR.sup_eq_top
      rwa [hR0, sup_bot_eq] at this
    exact ⟨3, a3_iso_110 V hV (subsingleton_of_bot_eq_top hr.symm)
      ⟨hAinj, LinearMap.range_eq_top.1 hPtop⟩⟩

end Classify

/-! ### Example 5.10: the quiver `D₄` with subspace orientation

Three outer vertices `v1, v2, v3` with an arrow each into the central vertex `c`. We exhibit the twelve
representations of the book (dimension vectors the twelve positive roots of `D₄`), show that they are indecomposable
and pairwise non-isomorphic. The converse (every indecomposable one is among them, the triple of subspaces
problem) is not proved here. -/

/-- The four vertices of `D₄`: three outer vertices and the centre. -/
inductive D4V : Type
  | v1
  | v2
  | v3
  | c

/-- The three arrows of `D₄`, from each outer vertex into the centre. -/
inductive D4Arrow : D4V → D4V → Type
  | a1 : D4Arrow D4V.v1 D4V.c
  | a2 : D4Arrow D4V.v2 D4V.c
  | a3 : D4Arrow D4V.v3 D4V.c

instance : Quiver.{0} D4V := ⟨D4Arrow⟩

/-- The arrow from `v1` to the centre. -/
def d4a1 : D4V.v1 ⟶ D4V.c := D4Arrow.a1

/-- The arrow from `v2` to the centre. -/
def d4a2 : D4V.v2 ⟶ D4V.c := D4Arrow.a2

/-- The arrow from `v3` to the centre. -/
def d4a3 : D4V.v3 ⟶ D4V.c := D4Arrow.a3

/-- The spaces of the representation attached to three maps `V1 → V ← V2`, `V3 → V`. -/
def D4obj (V1 V2 V3 V : Type u) : D4V → Type u
  | D4V.v1 => V1
  | D4V.v2 => V2
  | D4V.v3 => V3
  | D4V.c => V

section

variable (V1 V2 V3 V : Type u) (k : Type u) [Field k] [AddCommGroup V1] [Module k V1] [AddCommGroup V2]
  [Module k V2] [AddCommGroup V3] [Module k V3] [AddCommGroup V] [Module k V]

instance (i : D4V) : AddCommGroup (D4obj V1 V2 V3 V i) := by
  cases i
  · exact inferInstanceAs (AddCommGroup V1)
  · exact inferInstanceAs (AddCommGroup V2)
  · exact inferInstanceAs (AddCommGroup V3)
  · exact inferInstanceAs (AddCommGroup V)

instance (i : D4V) : Module k (D4obj V1 V2 V3 V i) := by
  cases i
  · exact inferInstanceAs (Module k V1)
  · exact inferInstanceAs (Module k V2)
  · exact inferInstanceAs (Module k V3)
  · exact inferInstanceAs (Module k V)

end

section D4

variable {k : Type u} [Field k] {V1 V2 V3 V : Type u} [AddCommGroup V1] [Module k V1] [AddCommGroup V2]
  [Module k V2] [AddCommGroup V3] [Module k V3] [AddCommGroup V] [Module k V]

/-- The representation of `D₄` given by three linear maps into the central space. -/
def D4Rep (A1 : V1 →ₗ[k] V) (A2 : V2 →ₗ[k] V) (A3 : V3 →ₗ[k] V) : QRep k D4V where
  obj := D4obj V1 V2 V3 V
  map := by
    intro i j a
    cases a
    · exact A1
    · exact A2
    · exact A3

/-- A subrepresentation of a representation of `D₄`, given by its four subspaces. -/
def d4Sub (R : QRep.{u, 0, u, 0} k D4V) (p1 : Submodule k (R.obj D4V.v1)) (p2 : Submodule k (R.obj D4V.v2))
    (p3 : Submodule k (R.obj D4V.v3)) (q : Submodule k (R.obj D4V.c)) (h1 : ∀ z ∈ p1, R.map d4a1 z ∈ q)
    (h2 : ∀ z ∈ p2, R.map d4a2 z ∈ q) (h3 : ∀ z ∈ p3, R.map d4a3 z ∈ q) : QRep.Subrep R where
  carrier := fun x => match x with
    | D4V.v1 => p1
    | D4V.v2 => p2
    | D4V.v3 => p3
    | D4V.c => q
  map_mem := by
    intro x y a z hz
    cases a
    · exact h1 z hz
    · exact h2 z hz
    · exact h3 z hz

theorem d4_eq_bot {R : QRep.{u, 0, u, 0} k D4V} (S : QRep.Subrep R) (h1 : S.carrier D4V.v1 = ⊥)
    (h2 : S.carrier D4V.v2 = ⊥) (h3 : S.carrier D4V.v3 = ⊥) (h4 : S.carrier D4V.c = ⊥) : S = ⊥ := by
  apply QRep.Subrep.ext
  intro i
  cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem d4_conn {U Y W : Type u} (hc : Nontrivial U → Nontrivial Y → Nontrivial W) :
    Subsingleton U ∨ Subsingleton Y ∨ ¬ Subsingleton W := by
  by_cases h1 : Subsingleton U
  · exact Or.inl h1
  by_cases h2 : Subsingleton Y
  · exact Or.inr (Or.inl h2)
  rw [not_subsingleton_iff_nontrivial] at h1 h2
  exact Or.inr (Or.inr (not_subsingleton_iff_nontrivial.2 (hc h1 h2)))

theorem d4_prop (s1 t1 s2 t2 s3 t3 sc tc u1 u2 u3 uc : Prop) (c1 : s1 ∨ t1) (c2 : s2 ∨ t2) (c3 : s3 ∨ t3)
    (cc : sc ∨ tc) (e1 : u1 → s1 ∧ t1) (e2 : u2 → s2 ∧ t2) (e3 : u3 → s3 ∧ t3) (ec : uc → sc ∧ tc)
    (m1 : s1 → tc → u1 ∨ uc) (m1' : t1 → sc → u1 ∨ uc) (m2 : s2 → tc → u2 ∨ uc)
    (m2' : t2 → sc → u2 ∨ uc) (m3 : s3 → tc → u3 ∨ uc) (m3' : t3 → sc → u3 ∨ uc)
    (n12 : u1 ∨ u2 ∨ ¬ uc) (n13 : u1 ∨ u3 ∨ ¬ uc) (n23 : u2 ∨ u3 ∨ ¬ uc) :
    (s1 ∧ s2 ∧ s3 ∧ sc) ∨ (t1 ∧ t2 ∧ t3 ∧ tc) := by
  by_cases a : u1 <;> by_cases b : u2 <;> by_cases c : u3 <;> by_cases d : uc <;>
    rcases c1 with x | x <;> rcases c2 with y | y <;> rcases c3 with z | z <;> rcases cc with w | w <;>
    simp_all

/-- Criterion for indecomposability of a representation of `D₄` whose spaces are all zero or one-dimensional,
with injective maps between nonzero spaces and nonzero centre whenever two outer spaces are nonzero. -/
theorem d4_isIndecomposable (A1 : V1 →ₗ[k] V) (A2 : V2 →ₗ[k] V) (A3 : V3 →ₗ[k] V)
    (h1 : A3OneOrZero k V1) (h2 : A3OneOrZero k V2) (h3 : A3OneOrZero k V3) (hc : A3OneOrZero k V)
    (hnt : Nontrivial V1 ∨ Nontrivial V2 ∨ Nontrivial V3 ∨ Nontrivial V)
    (hA1 : Nontrivial V1 → Nontrivial V → Function.Injective A1)
    (hA2 : Nontrivial V2 → Nontrivial V → Function.Injective A2)
    (hA3 : Nontrivial V3 → Nontrivial V → Function.Injective A3)
    (c12 : Nontrivial V1 → Nontrivial V2 → Nontrivial V) (c13 : Nontrivial V1 → Nontrivial V3 → Nontrivial V)
    (c23 : Nontrivial V2 → Nontrivial V3 → Nontrivial V) : (D4Rep A1 A2 A3).IsIndecomposable := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases hnt with hn | hn | hn | hn
    · have h' : (⊥ : Submodule k V1) = ⊤ :=
        congrArg (fun S : QRep.Subrep (D4Rep A1 A2 A3) => S.carrier D4V.v1) h
      exact bot_ne_top h'
    · have h' : (⊥ : Submodule k V2) = ⊤ :=
        congrArg (fun S : QRep.Subrep (D4Rep A1 A2 A3) => S.carrier D4V.v2) h
      exact bot_ne_top h'
    · have h' : (⊥ : Submodule k V3) = ⊤ :=
        congrArg (fun S : QRep.Subrep (D4Rep A1 A2 A3) => S.carrier D4V.v3) h
      exact bot_ne_top h'
    · have h' : (⊥ : Submodule k V) = ⊤ :=
        congrArg (fun S : QRep.Subrep (D4Rep A1 A2 A3) => S.carrier D4V.c) h
      exact bot_ne_top h'
  · intro S T hST
    have cl1 : S.carrier D4V.v1 = ⊥ ∨ T.carrier D4V.v1 = ⊥ := a3_compl_cases h1 (hST D4V.v1)
    have cl2 : S.carrier D4V.v2 = ⊥ ∨ T.carrier D4V.v2 = ⊥ := a3_compl_cases h2 (hST D4V.v2)
    have cl3 : S.carrier D4V.v3 = ⊥ ∨ T.carrier D4V.v3 = ⊥ := a3_compl_cases h3 (hST D4V.v3)
    have clc : S.carrier D4V.c = ⊥ ∨ T.carrier D4V.c = ⊥ := a3_compl_cases hc (hST D4V.c)
    have key : (S.carrier D4V.v1 = ⊥ ∧ S.carrier D4V.v2 = ⊥ ∧ S.carrier D4V.v3 = ⊥ ∧ S.carrier D4V.c = ⊥) ∨
        (T.carrier D4V.v1 = ⊥ ∧ T.carrier D4V.v2 = ⊥ ∧ T.carrier D4V.v3 = ⊥ ∧ T.carrier D4V.c = ⊥) :=
      d4_prop _ _ _ _ _ _ _ _ (Subsingleton V1) (Subsingleton V2) (Subsingleton V3) (Subsingleton V)
        cl1 cl2 cl3 clc
        (fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩)
        (fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩)
        (fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩)
        (fun h => ⟨a3_bot_of_subsingleton h _, a3_bot_of_subsingleton h _⟩)
        (fun hs ht => a3_mixed A1 hA1 (hST D4V.v1) hs ht (fun z hz => T.map_mem d4a1 hz))
        (fun hs ht => a3_mixed A1 hA1 (hST D4V.v1).symm hs ht (fun z hz => S.map_mem d4a1 hz))
        (fun hs ht => a3_mixed A2 hA2 (hST D4V.v2) hs ht (fun z hz => T.map_mem d4a2 hz))
        (fun hs ht => a3_mixed A2 hA2 (hST D4V.v2).symm hs ht (fun z hz => S.map_mem d4a2 hz))
        (fun hs ht => a3_mixed A3 hA3 (hST D4V.v3) hs ht (fun z hz => T.map_mem d4a3 hz))
        (fun hs ht => a3_mixed A3 hA3 (hST D4V.v3).symm hs ht (fun z hz => S.map_mem d4a3 hz))
        (d4_conn c12) (d4_conn c13) (d4_conn c23)
    rcases key with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
    · exact Or.inl (d4_eq_bot S e1 e2 e3 e4)
    · exact Or.inr (d4_eq_bot T e1 e2 e3 e4)

end D4

/-! #### The twelve models -/

section D4Models

variable (k : Type u) [Field k]

/-- The representation of `D₄` attached to three subspaces of a space `M`. -/
def D4Rep.sub {M : Type u} [AddCommGroup M] [Module k M] (L1 L2 L3 : Submodule k M) : QRep k D4V :=
  D4Rep L1.subtype L2.subtype L3.subtype

/-- The simple representation at the outer vertex `v1`. -/
def D4Rep.simple1 : QRep k D4V :=
  D4Rep (0 : k →ₗ[k] PUnit.{u + 1}) (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1})
    (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1})

/-- The simple representation at the outer vertex `v2`. -/
def D4Rep.simple2 : QRep k D4V :=
  D4Rep (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1}) (0 : k →ₗ[k] PUnit.{u + 1})
    (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1})

/-- The simple representation at the outer vertex `v3`. -/
def D4Rep.simple3 : QRep k D4V :=
  D4Rep (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1}) (0 : PUnit.{u + 1} →ₗ[k] PUnit.{u + 1})
    (0 : k →ₗ[k] PUnit.{u + 1})

/-- The line spanned by `(1, 0)` in `k²`. -/
def D4Rep.line1 : Submodule k (k × k) := Submodule.span k {((1 : k), (0 : k))}

/-- The line spanned by `(0, 1)` in `k²`. -/
def D4Rep.line2 : Submodule k (k × k) := Submodule.span k {((0 : k), (1 : k))}

/-- The line spanned by `(1, 1)` in `k²`. -/
def D4Rep.line3 : Submodule k (k × k) := Submodule.span k {((1 : k), (1 : k))}

/-- The representation of dimension vector `(1,1,1;2)`: three distinct lines in the plane `k²`. -/
def D4Rep.lines : QRep k D4V := D4Rep.sub k (D4Rep.line1 k) (D4Rep.line2 k) (D4Rep.line3 k)

/-- The twelve representations of Example 5.10, indexed by `Fin 12`: first the eight representations with
one-dimensional centre (each outer space zero or the whole centre), then the three simple outer ones, then
`D4Rep.lines`. -/
def D4Rep.model : Fin 12 → QRep k D4V
  | 0 => D4Rep.sub k (⊥ : Submodule k k) ⊥ ⊥
  | 1 => D4Rep.sub k (⊤ : Submodule k k) ⊥ ⊥
  | 2 => D4Rep.sub k (⊥ : Submodule k k) ⊤ ⊥
  | 3 => D4Rep.sub k (⊥ : Submodule k k) ⊥ ⊤
  | 4 => D4Rep.sub k (⊤ : Submodule k k) ⊤ ⊥
  | 5 => D4Rep.sub k (⊤ : Submodule k k) ⊥ ⊤
  | 6 => D4Rep.sub k (⊥ : Submodule k k) ⊤ ⊤
  | 7 => D4Rep.sub k (⊤ : Submodule k k) ⊤ ⊤
  | 8 => D4Rep.simple1 k
  | 9 => D4Rep.simple2 k
  | 10 => D4Rep.simple3 k
  | 11 => D4Rep.lines k

theorem D4Rep.line1_finrank : Module.finrank k (D4Rep.line1 k) = 1 :=
  finrank_span_singleton (by simp)

theorem D4Rep.line2_finrank : Module.finrank k (D4Rep.line2 k) = 1 :=
  finrank_span_singleton (by simp)

theorem D4Rep.line3_finrank : Module.finrank k (D4Rep.line3 k) = 1 :=
  finrank_span_singleton (by simp)

theorem D4Rep.line1_ne_line2 : D4Rep.line1 k ≠ D4Rep.line2 k := by
  intro h
  have hm : ((1 : k), (0 : k)) ∈ D4Rep.line2 k := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
  simp [Prod.ext_iff] at hr

theorem D4Rep.line1_ne_line3 : D4Rep.line1 k ≠ D4Rep.line3 k := by
  intro h
  have hm : ((1 : k), (0 : k)) ∈ D4Rep.line3 k := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
  simp [Prod.ext_iff] at hr
  exact one_ne_zero (hr.1.symm.trans hr.2)

theorem D4Rep.line2_ne_line3: D4Rep.line2 k ≠ D4Rep.line3 k := by
  intro h
  have hm : ((0 : k), (1 : k)) ∈ D4Rep.line3 k := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
  simp [Prod.ext_iff] at hr
  exact zero_ne_one (hr.1.symm.trans hr.2)

/-- The dimension at the outer vertex `v1` of each model. -/
def D4Rep.dim1 : Fin 12 → ℕ := ![0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1]

/-- The dimension at the outer vertex `v2` of each model. -/
def D4Rep.dim2 : Fin 12 → ℕ := ![0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1]

/-- The dimension at the outer vertex `v3` of each model. -/
def D4Rep.dim3 : Fin 12 → ℕ := ![0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1]

/-- The dimension at the centre of each model. -/
def D4Rep.dimC : Fin 12 → ℕ := ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 2]

theorem D4Rep.dimVec_model (i : Fin 12) :
    (D4Rep.model k i).dimVec D4V.v1 = D4Rep.dim1 i ∧ (D4Rep.model k i).dimVec D4V.v2 = D4Rep.dim2 i ∧
    (D4Rep.model k i).dimVec D4V.v3 = D4Rep.dim3 i ∧ (D4Rep.model k i).dimVec D4V.c = D4Rep.dimC i := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact Module.finrank_self k
    | exact finrank_bot k k
    | exact (finrank_top k k).trans (Module.finrank_self k)
    | exact Module.finrank_zero_of_subsingleton (R := k) (M := PUnit.{u + 1})
    | exact D4Rep.line1_finrank k
    | exact D4Rep.line2_finrank k
    | exact D4Rep.line3_finrank k
    | exact (Module.finrank_prod (R := k) (M := k) (M' := k)).trans (by rw [Module.finrank_self]; rfl)

/-- **Example 5.10** (part): the twelve representations are pairwise non-isomorphic (their dimension vectors are
the twelve positive roots of `D₄`). -/
@[kb "etingof2011" "Example 5.10, p. 83"]
theorem D4Rep.model_injective (i j : Fin 12)
    (h : QRep.Isomorphic (D4Rep.model k i) (D4Rep.model k j)) : i = j := by
  have h1 := (D4Rep.dimVec_model k i).1.symm.trans
    ((congrFun h.dimVec_eq D4V.v1).trans (D4Rep.dimVec_model k j).1)
  have h2 := (D4Rep.dimVec_model k i).2.1.symm.trans
    ((congrFun h.dimVec_eq D4V.v2).trans (D4Rep.dimVec_model k j).2.1)
  have h3 := (D4Rep.dimVec_model k i).2.2.1.symm.trans
    ((congrFun h.dimVec_eq D4V.v3).trans (D4Rep.dimVec_model k j).2.2.1)
  have h4 := (D4Rep.dimVec_model k i).2.2.2.symm.trans
    ((congrFun h.dimVec_eq D4V.c).trans (D4Rep.dimVec_model k j).2.2.2)
  have key : ∀ i j : Fin 12, D4Rep.dim1 i = D4Rep.dim1 j → D4Rep.dim2 i = D4Rep.dim2 j →
      D4Rep.dim3 i = D4Rep.dim3 j → D4Rep.dimC i = D4Rep.dimC j → i = j := by decide
  exact key i j h1 h2 h3 h4

end D4Models

/-! #### Indecomposability of the twelve models -/

section D4Indec

variable {k : Type u} [Field k]

theorem d4_oneOrZero_of_bot_or_top (L : Submodule k k) (h : L = ⊥ ∨ L = ⊤) : A3OneOrZero k L := by
  rcases h with rfl | rfl
  · exact Or.inl inferInstance
  · refine Or.inr ⟨⟨1, trivial⟩, ?_, fun w => ⟨w.1, ?_⟩⟩
    · intro h0
      exact one_ne_zero (congrArg Subtype.val h0)
    · exact Subtype.ext (by simp)

theorem d4_oneOrZero_self : A3OneOrZero k k :=
  Or.inr ⟨1, one_ne_zero, fun w => ⟨w, by simp⟩⟩

theorem D4Rep.sub_isIndecomposable (L1 L2 L3 : Submodule k k) (h1 : L1 = ⊥ ∨ L1 = ⊤)
    (h2 : L2 = ⊥ ∨ L2 = ⊤) (h3 : L3 = ⊥ ∨ L3 = ⊤) : (D4Rep.sub k L1 L2 L3).IsIndecomposable :=
  d4_isIndecomposable _ _ _ (d4_oneOrZero_of_bot_or_top L1 h1) (d4_oneOrZero_of_bot_or_top L2 h2)
    (d4_oneOrZero_of_bot_or_top L3 h3) d4_oneOrZero_self (Or.inr (Or.inr (Or.inr inferInstance)))
    (fun _ _ => Submodule.injective_subtype _) (fun _ _ => Submodule.injective_subtype _)
    (fun _ _ => Submodule.injective_subtype _) (fun _ _ => inferInstance) (fun _ _ => inferInstance)
    (fun _ _ => inferInstance)

theorem d4_simple_isIndecomposable {V1 V2 V3 : Type u} [AddCommGroup V1] [Module k V1] [AddCommGroup V2]
    [Module k V2] [AddCommGroup V3] [Module k V3] (A1 : V1 →ₗ[k] PUnit.{u + 1}) (A2 : V2 →ₗ[k] PUnit.{u + 1})
    (A3 : V3 →ₗ[k] PUnit.{u + 1}) (h1 : A3OneOrZero k V1) (h2 : A3OneOrZero k V2) (h3 : A3OneOrZero k V3)
    (hnt : Nontrivial V1 ∨ Nontrivial V2 ∨ Nontrivial V3)
    (c12 : Nontrivial V1 → Nontrivial V2 → False) (c13 : Nontrivial V1 → Nontrivial V3 → False)
    (c23 : Nontrivial V2 → Nontrivial V3 → False) : (D4Rep A1 A2 A3).IsIndecomposable :=
  d4_isIndecomposable A1 A2 A3 h1 h2 h3 a3_oneOrZero_punit
    (by rcases hnt with h | h | h; exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h))])
    (fun _ h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit)
    (fun a b => (c12 a b).elim) (fun a b => (c13 a b).elim) (fun a b => (c23 a b).elim)

theorem d4_bot_of_inj {X M : Type u} [AddCommGroup X] [Module k X] [AddCommGroup M] [Module k M]
    (f : X →ₗ[k] M) (hf : Function.Injective f) {Sx : Submodule k X} {Sm : Submodule k M}
    (h : ∀ z ∈ Sx, f z ∈ Sm) (hb : Sm = ⊥) : Sx = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  have := h z hz
  rw [hb, Submodule.mem_bot] at this
  exact hf (by rw [this, map_zero])

theorem d4_line_le {M : Type u} [AddCommGroup M] [Module k M] (L Sc Tc : Submodule k M)
    (Si Ti : Submodule k L) (hc : IsCompl Si Ti) (hS : ∀ z ∈ Si, (z : M) ∈ Sc) (hT : ∀ z ∈ Ti, (z : M) ∈ Tc)
    (hone : Si = ⊥ ∨ Ti = ⊥) : L ≤ Sc ∨ L ≤ Tc := by
  rcases hone with h | h
  · right
    have : Ti = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, bot_sup_eq] at this
    intro x hx
    exact hT ⟨x, hx⟩ (by rw [this]; trivial)
  · left
    have : Si = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, sup_bot_eq] at this
    intro x hx
    exact hS ⟨x, hx⟩ (by rw [this]; trivial)

theorem d4_line_eq {M : Type u} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (L Sc Tc : Submodule k M) (hL : Module.finrank k L = 1) (hS : Module.finrank k Sc = 1)
    (hT : Module.finrank k Tc = 1) (h : L ≤ Sc ∨ L ≤ Tc) : L = Sc ∨ L = Tc := by
  rcases h with h | h
  · exact Or.inl (Submodule.eq_of_le_of_finrank_eq h (hL.trans hS.symm))
  · exact Or.inr (Submodule.eq_of_le_of_finrank_eq h (hL.trans hT.symm))

theorem d4_dim_aux (Sc Tc : Submodule k (k × k)) (hcc : IsCompl Sc Tc) (hSc : ¬ Sc = ⊥) (hTc : ¬ Tc = ⊥) :
    Module.finrank k Sc = 1 ∧ Module.finrank k Tc = 1 := by
  have hsum := Submodule.finrank_add_eq_of_isCompl hcc
  have h2 : Module.finrank k (k × k) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hSpos : Module.finrank k Sc ≠ 0 := fun h => hSc (Submodule.finrank_eq_zero.1 h)
  have hTpos : Module.finrank k Tc ≠ 0 := fun h => hTc (Submodule.finrank_eq_zero.1 h)
  omega

theorem d4_lines_aux (L1 L2 L3 : Submodule k (k × k)) (f1 : Module.finrank k L1 = 1)
    (f2 : Module.finrank k L2 = 1) (f3 : Module.finrank k L3 = 1) (n12 : L1 ≠ L2) (n13 : L1 ≠ L3)
    (n23 : L2 ≠ L3) : (D4Rep.sub k L1 L2 L3).IsIndecomposable := by
  have o1 : A3OneOrZero k L1 := Or.inr (finrank_eq_one_iff'.1 f1)
  have o2 : A3OneOrZero k L2 := Or.inr (finrank_eq_one_iff'.1 f2)
  have o3 : A3OneOrZero k L3 := Or.inr (finrank_eq_one_iff'.1 f3)
  refine ⟨?_, ?_⟩
  · intro h
    have h' : (⊥ : Submodule k (k × k)) = ⊤ :=
      congrArg (fun S : QRep.Subrep (D4Rep.sub k L1 L2 L3) => S.carrier D4V.c) h
    exact bot_ne_top h'
  · intro S T hST
    have c1 : S.carrier D4V.v1 = ⊥ ∨ T.carrier D4V.v1 = ⊥ := a3_compl_cases o1 (hST D4V.v1)
    have c2 : S.carrier D4V.v2 = ⊥ ∨ T.carrier D4V.v2 = ⊥ := a3_compl_cases o2 (hST D4V.v2)
    have c3 : S.carrier D4V.v3 = ⊥ ∨ T.carrier D4V.v3 = ⊥ := a3_compl_cases o3 (hST D4V.v3)
    have hcc : IsCompl (S.carrier D4V.c) (T.carrier D4V.c) := hST D4V.c
    by_cases hSc : S.carrier D4V.c = ⊥
    · left
      exact d4_eq_bot S
        (d4_bot_of_inj L1.subtype (Submodule.injective_subtype _) (fun z hz => S.map_mem d4a1 hz) hSc)
        (d4_bot_of_inj L2.subtype (Submodule.injective_subtype _) (fun z hz => S.map_mem d4a2 hz) hSc)
        (d4_bot_of_inj L3.subtype (Submodule.injective_subtype _) (fun z hz => S.map_mem d4a3 hz) hSc) hSc
    by_cases hTc : T.carrier D4V.c = ⊥
    · right
      exact d4_eq_bot T
        (d4_bot_of_inj L1.subtype (Submodule.injective_subtype _) (fun z hz => T.map_mem d4a1 hz) hTc)
        (d4_bot_of_inj L2.subtype (Submodule.injective_subtype _) (fun z hz => T.map_mem d4a2 hz) hTc)
        (d4_bot_of_inj L3.subtype (Submodule.injective_subtype _) (fun z hz => T.map_mem d4a3 hz) hTc) hTc
    exfalso
    obtain ⟨hS1, hT1⟩ := d4_dim_aux _ _ hcc hSc hTc
    have e1 := d4_line_eq L1 _ _ f1 hS1 hT1
      (d4_line_le L1 _ _ _ _ (hST D4V.v1) (fun z hz => S.map_mem d4a1 hz) (fun z hz => T.map_mem d4a1 hz) c1)
    have e2 := d4_line_eq L2 _ _ f2 hS1 hT1
      (d4_line_le L2 _ _ _ _ (hST D4V.v2) (fun z hz => S.map_mem d4a2 hz) (fun z hz => T.map_mem d4a2 hz) c2)
    have e3 := d4_line_eq L3 _ _ f3 hS1 hT1
      (d4_line_le L3 _ _ _ _ (hST D4V.v3) (fun z hz => S.map_mem d4a3 hz) (fun z hz => T.map_mem d4a3 hz) c3)
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3 <;>
      first
      | exact n12 (e1.trans e2.symm)
      | exact n13 (e1.trans e3.symm)
      | exact n23 (e2.trans e3.symm)

variable (k)

/-- **Example 5.10** (part): the twelve representations of `D₄` are indecomposable. -/
@[kb "etingof2011" "Example 5.10, p. 83"]
theorem D4Rep.isIndecomposable_models (i : Fin 12) : (D4Rep.model k i).IsIndecomposable := by
  have hb : ∀ L : Submodule k k, L = ⊥ ∨ L = ⊤ := fun L => by
    by_cases h : L = ⊥
    · exact Or.inl h
    · right
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      rw [eq_top_iff]
      intro w _
      have : w = (w * v⁻¹) • v := by simp [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv0]
      rw [this]
      exact L.smul_mem _ hv
  fin_cases i
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact D4Rep.sub_isIndecomposable _ _ _ (hb _) (hb _) (hb _)
  · exact d4_simple_isIndecomposable _ _ _ d4_oneOrZero_self a3_oneOrZero_punit a3_oneOrZero_punit
      (Or.inl inferInstance) (fun _ h => absurd h a3_noPunit) (fun _ h => absurd h a3_noPunit)
      (fun h _ => absurd h a3_noPunit)
  · exact d4_simple_isIndecomposable _ _ _ a3_oneOrZero_punit d4_oneOrZero_self a3_oneOrZero_punit
      (Or.inr (Or.inl inferInstance)) (fun h _ => absurd h a3_noPunit) (fun h _ => absurd h a3_noPunit)
      (fun _ h => absurd h a3_noPunit)
  · exact d4_simple_isIndecomposable _ _ _ a3_oneOrZero_punit a3_oneOrZero_punit d4_oneOrZero_self
      (Or.inr (Or.inr inferInstance)) (fun h _ => absurd h a3_noPunit) (fun h _ => absurd h a3_noPunit)
      (fun h _ => absurd h a3_noPunit)
  · exact d4_lines_aux _ _ _ (D4Rep.line1_finrank k) (D4Rep.line2_finrank k) (D4Rep.line3_finrank k)
      (D4Rep.line1_ne_line2 k) (D4Rep.line1_ne_line3 k) (D4Rep.line2_ne_line3 k)

end D4Indec

end

end UndergradKB.RepresentationTheory
