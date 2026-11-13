import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.PathAlgebraModules
import UndergradKB.RepresentationTheory.GabrielBasics
import UndergradKB.Common.Attr

/-! # Problem 2.23: representations of a quiver without oriented cycles (Etingof et al., §2.9)

Throughout, `Q` is a finite quiver without oriented cycles (every path from a vertex to itself is trivial) and
representations are the `QRep k Q` of the repository (a representation of `Q` is the same thing as a module over
the path algebra, as discussed in §1.8; this identification is not used below).

* `QRep.isIrreducible_iff_exists_isSimpleAt` (Problem 2.23, irreducibles): a representation is irreducible iff
  it is one of the one-dimensional representations `S_i` at a vertex (`QRep.IsSimpleAt`); in that case it is
  isomorphic to `simpleRep k i`, and `S_i`, `S_j` are non-isomorphic for `i ≠ j`.
* `QExt` : the space `Ext¹(V, W)` of a quiver, as the quotient of `∏ₐ Hom(V_{s a}, W_{t a})` by the image of
  `f ↦ (W_a f_{s a} - f_{t a} V_a)`; `extRep_equiv_iff` shows that this quotient classifies the extensions
  `0 → W → E → V → 0` with `E_x = W_x ⊕ V_x`.
* `finrank_qExt_simpleRep` (Problem 2.23, Ext¹): `dim Ext¹(S_i, S_j)` is the number of arrows `i → j`.

Differences from the book: Ext¹ is computed in the (two-term) cocycle model adapted to quivers, not through
`Extensions.lean` for the algebra `P_Q`; irreducibility is in the category of quiver representations.
-/

namespace UndergradKB.RepresentationTheory

open _root_.Quiver

universe u v w a

/-- The quiver `Q` has no oriented cycles: every path from a vertex to itself has length `0`. -/
def NoOrientedCycles (Q : Type v) [Quiver.{a} Q] : Prop := ∀ (i : Q) (p : Path i i), p.length = 0

namespace QRep

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

section Irreducible

open scoped Classical

theorem exists_isSimpleAt_of_isIrreducible [Finite Q] (hQ : NoOrientedCycles Q) {V : QRep.{u, v, w, a} k Q}
    (hV : V.IsIrreducible) : ∃ i, V.IsSimpleAt i := by
  -- reachability by a nontrivial path is a strict order
  let r : Q → Q → Prop := fun x y => ∃ p : Path y x, 0 < p.length
  have : IsTrans Q r := ⟨fun x y z hxy hyz => by
    obtain ⟨p, hp⟩ := hxy
    obtain ⟨q, hq⟩ := hyz
    exact ⟨q.comp p, by rw [Path.length_comp]; omega⟩⟩
  have : Std.Irrefl r := ⟨fun x ⟨p, hp⟩ => by have := hQ x p; omega⟩
  have hwf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  have hne : ∃ j, Nontrivial (V.obj j) := by
    by_contra hcon
    push Not at hcon
    apply hV.1
    apply Subrep.ext
    intro j
    have := hcon j
    exact bot_eq_top_of_subsingleton'
  obtain ⟨i, hi, hmin⟩ := hwf.has_min {j | Nontrivial (V.obj j)} hne
  have hi' : Nontrivial (V.obj i) := hi
  have hsub : ∀ {x y : Q} (_ : x ⟶ y), x = i → Subsingleton (V.obj y) := by
    intro x y e hx
    subst hx
    by_contra hcon
    exact hmin y (not_subsingleton_iff_nontrivial.1 hcon) ⟨(Path.cons Path.nil e), by simp⟩
  have hloop : ∀ e : i ⟶ i, False := fun e => by
    have := hQ i (Path.cons Path.nil e)
    simp at this
  -- the subrepresentation concentrated at `i`
  have hout : ∀ j, j ≠ i → Subsingleton (V.obj j) := by
    let S : Subrep V :=
      { carrier := fun j => if j = i then ⊤ else ⊥
        map_mem := by
          intro x y e v hv
          by_cases hy : y = i
          · simp [hy]
          · simp only [hy, ite_false, Submodule.mem_bot]
            by_cases hx : x = i
            · have := hsub e hx
              exact Subsingleton.elim _ _
            · simp only [hx, ite_false, Submodule.mem_bot] at hv
              rw [hv, map_zero] }
    have hS : S ≠ ⊥ := fun h => by
      have := congrArg (fun T : Subrep V => T.carrier i) h
      simp only [S, ite_true, Subrep.bot_carrier] at this
      exact bot_ne_top this.symm
    have hS' : S = ⊤ := (hV.2 S).resolve_left hS
    intro j hj
    have := congrArg (fun T : Subrep V => T.carrier j) hS'
    simp only [S, hj, ite_false, Subrep.top_carrier] at this
    exact ⟨fun p q => by
      have hp : p ∈ (⊥ : Submodule k (V.obj j)) := this ▸ Submodule.mem_top
      have hq : q ∈ (⊥ : Submodule k (V.obj j)) := this ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hp hq
      rw [hp, hq]⟩
  refine ⟨i, hout, ?_⟩
  -- the space at `i` is a simple module
  have hsimple : IsSimpleModule k (V.obj i) := by
    refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := fun W => ?_ }
    let T : Subrep V :=
      { carrier := fun j => if h : j = i then (h ▸ W : Submodule k (V.obj j)) else ⊥
        map_mem := by
          intro x y e v hv
          by_cases hx : x = i
          · subst hx
            by_cases hy : y = x
            · subst hy
              exact (hloop e).elim
            · have := hsub e rfl
              simp only [hy, dite_false, Submodule.mem_bot]
              exact Subsingleton.elim _ _
          · simp only [hx, dite_false, Submodule.mem_bot] at hv
            rw [hv, map_zero]
            exact zero_mem _ }
    rcases hV.2 T with h | h
    · left
      have := congrArg (fun T : Subrep V => T.carrier i) h
      simpa [T, Subrep.bot_carrier] using this
    · right
      have := congrArg (fun T : Subrep V => T.carrier i) h
      simpa [T, Subrep.top_carrier] using this
  have hfr := isSimpleModule_iff_finrank_eq_one.1 hsimple
  have : Module.Finite k (V.obj i) := Module.finite_of_finrank_eq_succ hfr
  rw [← Module.finrank_eq_rank, hfr]
  simp

/-- A representation that is simple at a vertex is irreducible. -/
theorem isIrreducible_of_isSimpleAt {V : QRep.{u, v, w, a} k Q} {i : Q} (h : V.IsSimpleAt i) :
    V.IsIrreducible := by
  obtain ⟨h1, h2⟩ := h
  have hfr : Module.finrank k (V.obj i) = 1 := Module.finrank_eq_of_rank_eq h2
  have : IsSimpleModule k (V.obj i) := isSimpleModule_iff_finrank_eq_one.2 hfr
  have hnt : Nontrivial (V.obj i) := Module.nontrivial_of_finrank_eq_succ hfr
  refine ⟨fun h => ?_, fun S => ?_⟩
  · have := congrArg (fun T : Subrep V => T.carrier i) h
    simp only [Subrep.bot_carrier, Subrep.top_carrier] at this
    exact bot_ne_top this
  · rcases IsSimpleOrder.eq_bot_or_eq_top (S.carrier i) with hS | hS
    · left
      apply Subrep.ext
      intro j
      by_cases hj : j = i
      · subst hj; exact hS
      · have := h1 j hj
        exact eq_bot_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _
    · right
      apply Subrep.ext
      intro j
      by_cases hj : j = i
      · subst hj; exact hS
      · have := h1 j hj
        exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact zero_mem _

/-- **Problem 2.23 (irreducible representations).** For a finite quiver without oriented cycles, a
representation is irreducible if and only if it is the simple representation `S_i` at some vertex `i`
(one-dimensional at `i`, zero elsewhere). -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
theorem isIrreducible_iff_exists_isSimpleAt [Finite Q] (hQ : NoOrientedCycles Q) {V : QRep.{u, v, w, a} k Q} :
    V.IsIrreducible ↔ ∃ i, V.IsSimpleAt i :=
  ⟨exists_isSimpleAt_of_isIrreducible hQ, fun ⟨_, h⟩ => isIrreducible_of_isSimpleAt h⟩

/-- Every irreducible representation of a finite quiver without oriented cycles is isomorphic to `S_i` for some
vertex `i`. -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
theorem exists_isomorphic_simpleRep [Finite Q] (hQ : NoOrientedCycles Q) {V : QRep.{u, v, w, a} k Q}
    (hV : V.IsIrreducible) : ∃ i, Isomorphic V (simpleRep k i : QRep.{u, v, u, a} k Q) := by
  obtain ⟨i, hi⟩ := exists_isSimpleAt_of_isIrreducible hQ hV
  refine ⟨i, isomorphic_of_isSimpleAt (fun e => ?_) hi (simpleRep_isSimpleAt i)⟩
  have := hQ i (Path.cons Path.nil e)
  simp at this

/-- The simple representations `S_i` and `S_j` at different vertices are not isomorphic. -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
theorem simpleRep_not_isomorphic {i j : Q} (h : i ≠ j) :
    ¬ Isomorphic (simpleRep k i : QRep.{u, v, u, a} k Q) (simpleRep k j) := by
  intro hiso
  have := hiso.dim_eq i
  change Module.finrank k (Fin (if i = i then 1 else 0) → k) =
    Module.finrank k (Fin (if i = j then 1 else 0) → k) at this
  simp [h] at this

end Irreducible

/-! ### Ext¹ for quiver representations -/

section Ext

variable (V W : QRep.{u, v, w, a} k Q)

/-- Extension cochains: a linear map `V_x → W_y` for each arrow `x → y`. -/
abbrev ExtCochain : Type _ := ∀ (x y : Q), (x ⟶ y) → (V.obj x →ₗ[k] W.obj y)

/-- The coboundary of a family `f_x : V_x → W_x` is `(W_e f_x - f_y V_e)_e`. -/
def coboundary : (∀ x, V.obj x →ₗ[k] W.obj x) →ₗ[k] ExtCochain V W where
  toFun f := fun x y e => (W.map e).comp (f x) - (f y).comp (V.map e)
  map_add' f g := by
    funext x y e
    apply LinearMap.ext
    intro v
    simp only [Pi.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add]
    abel
  map_smul' r f := by
    funext x y e
    apply LinearMap.ext
    intro v
    simp only [Pi.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      RingHom.id_apply, smul_sub]

/-- `Ext¹(V, W)` for representations of a quiver: cochains modulo coboundaries. -/
abbrev QExt : Type _ := ExtCochain V W ⧸ LinearMap.range (coboundary V W)

variable {V W}

/-- The extension of `V` by `W` attached to a cochain `c`: the space `W_x × V_x` at each vertex `x`, with arrow
maps `(w, v) ↦ (W_e w + c_e v, V_e v)`. -/
def extMap (c : ExtCochain V W) (x y : Q) (e : x ⟶ y) : W.obj x × V.obj x →ₗ[k] W.obj y × V.obj y :=
  LinearMap.prod ((W.map e).comp (LinearMap.fst k _ _) + (c x y e).comp (LinearMap.snd k _ _))
    ((V.map e).comp (LinearMap.snd k _ _))

@[simp] theorem extMap_apply (c : ExtCochain V W) (x y : Q) (e : x ⟶ y) (w : W.obj x) (v : V.obj x) :
    extMap c x y e (w, v) = (W.map e w + c x y e v, V.map e v) := rfl

/-- The extension of `V` by `W` attached to a cochain `c` (as a quiver representation). -/
def extRep (c : ExtCochain V W) : QRep.{u, v, w, a} k Q where
  obj x := W.obj x × V.obj x
  map {x y} e := extMap c x y e

/-- Two such extensions are equivalent if there is a homomorphism between them that is the identity on `W` and
on the quotient `V`. -/
def ExtEquiv (c c' : ExtCochain V W) : Prop :=
  ∃ F : Hom (extRep c) (extRep c'),
    (∀ x (w : W.obj x), F.app x (w, 0) = (w, 0)) ∧ ∀ x (p : W.obj x × V.obj x), (F.app x p).2 = p.2

/-- Two extension cochains give equivalent extensions exactly when their difference is a coboundary; hence
`Ext¹(V, W) = QExt V W` classifies the extensions of `V` by `W` (those with underlying spaces `W_x × V_x`). -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
theorem extEquiv_iff (c c' : ExtCochain V W) :
    ExtEquiv c c' ↔ c - c' ∈ LinearMap.range (coboundary V W) := by
  constructor
  · rintro ⟨F, h1, h2⟩
    let G : ∀ x, (W.obj x × V.obj x) →ₗ[k] (W.obj x × V.obj x) := fun x => F.app x
    have hG1 : ∀ x (w : W.obj x), G x (w, 0) = (w, 0) := h1
    have hG2 : ∀ x (p : W.obj x × V.obj x), (G x p).2 = p.2 := h2
    have hcomm : ∀ (x y : Q) (e : x ⟶ y) (p : W.obj x × V.obj x),
        G y (extMap c x y e p) = extMap c' x y e (G x p) :=
      fun x y e p => LinearMap.congr_fun (F.comm e) p
    let f : ∀ x, V.obj x →ₗ[k] W.obj x := fun x =>
      (LinearMap.fst k _ _).comp ((G x).comp (LinearMap.inr k _ _))
    have hF : ∀ x (w : W.obj x) (v : V.obj x), G x (w, v) = (w + f x v, v) := by
      intro x w v
      have e1 : ((w, v) : W.obj x × V.obj x) = (w, 0) + (0, v) := by simp
      have e2 : G x (0, v) = ((f x) v, v) := by
        apply Prod.ext
        · rfl
        · simpa using hG2 x (0, v)
      rw [e1, map_add, hG1, e2]
      simp
    refine ⟨f, ?_⟩
    funext x y e
    apply LinearMap.ext
    intro v
    have hc := congrArg Prod.fst (hcomm x y e (0, v))
    simp only [extMap_apply, map_zero, zero_add, hF] at hc
    simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, LinearMap.comp_apply,
      Pi.sub_apply]
    rw [sub_eq_sub_iff_add_eq_add]
    exact hc.symm
  · rintro ⟨f, hf⟩
    let P : ∀ x, (W.obj x × V.obj x) →ₗ[k] (W.obj x × V.obj x) := fun x =>
      LinearMap.prod (LinearMap.fst k _ _ + (f x).comp (LinearMap.snd k _ _)) (LinearMap.snd k _ _)
    have hP : ∀ x (w : W.obj x) (v : V.obj x), P x (w, v) = (w + f x v, v) := fun _ _ _ => rfl
    have key : ∀ (x y : Q) (e : x ⟶ y) (p : W.obj x × V.obj x),
        P y (extMap c x y e p) = extMap c' x y e (P x p) := by
      rintro x y e ⟨w, v⟩
      have := congrArg (fun T => T x y e v) hf
      simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, LinearMap.comp_apply,
        Pi.sub_apply] at this
      rw [sub_eq_sub_iff_add_eq_add] at this
      simp only [extMap_apply, hP, map_add]
      rw [add_assoc, add_assoc, this]
    exact ⟨⟨fun x => P x, fun {x y} e => LinearMap.ext fun p => key x y e p⟩,
      fun x w => (hP x w 0).trans (by simp), fun x p => rfl⟩

open scoped Classical in
theorem finrank_simpleRep_obj (i x : Q) :
    Module.finrank k ((simpleRep k i : QRep.{u, v, u, a} k Q).obj x) = if x = i then 1 else 0 := by
  change Module.finrank k (Fin (if x = i then 1 else 0) → k) = _
  rw [Module.finrank_fin_fun]

/-- **Problem 2.23 (Ext¹ between simples).** For a finite quiver, `dim Ext¹(S_i, S_j)` is the number of
arrows `i → j`. (Since the arrow maps of `S_i`, `S_j` vanish, all coboundaries are zero and the space of
cochains is already `Ext¹`.) -/
@[kb "etingof2011" "Problem 2.23, p. 30"]
theorem finrank_qExt_simpleRep [Fintype Q] [∀ x y : Q, Fintype (x ⟶ y)] (i j : Q) :
    Module.finrank k (QExt (simpleRep k i : QRep.{u, v, u, a} k Q) (simpleRep k j)) =
      Fintype.card (i ⟶ j) := by
  classical
  have h0 : coboundary (simpleRep k i : QRep.{u, v, u, a} k Q) (simpleRep k j) = 0 := by
    apply LinearMap.ext
    intro f
    funext x y e
    apply LinearMap.ext
    intro v
    have h1 : ((simpleRep k i : QRep.{u, v, u, a} k Q).map e) = 0 := rfl
    have h2 : ((simpleRep k j : QRep.{u, v, u, a} k Q).map e) = 0 := rfl
    simp [coboundary, h1, h2]
  rw [(Submodule.quotEquivOfEqBot _ (LinearMap.range_eq_bot.2 h0)).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_linearMap, finrank_simpleRep_obj]
  simp

end Ext

end QRep

/-! ### Problem 1.33: the path algebra is presented by the idempotent and arrow relations -/

section Presentation

universe u₁ v₁

variable {k : Type*} [Field k] {Q : Type u₁} [_root_.Quiver.{v₁ + 1} Q] [DecidableEq Q] [Fintype Q]
variable {B : Type*} [Semiring B] [Algebra k B]

/-- The relations of Problem 1.33 (in the multiplication convention of `PathAlgebra`, where the product of two
paths is "first this, then that", so `p_s a_h = a_h = a_h p_t` for an arrow `h : s → t`): the elements `P i`
are orthogonal idempotents with sum `1`, and `A h` is absorbed by `P (source h)` on the left and `P (target h)`
on the right and killed by the other idempotents. -/
structure PathRelations (P : Q → B) (A : ∀ {i j : Q}, (i ⟶ j) → B) : Prop where
  sum_eq_one : ∑ i, P i = 1
  idem_mul : ∀ i j, P i * P j = if i = j then P i else 0
  idem_mul_arrow : ∀ {i j : Q} (h : i ⟶ j) (l : Q), P l * A h = if l = i then A h else 0
  arrow_mul_idem : ∀ {i j : Q} (h : i ⟶ j) (l : Q), A h * P l = if l = j then A h else 0

/-- The value of the product `P_{i₀} A_{e₁} ⋯ A_{eₙ}` along a path. -/
def evPath (P : Q → B) (A : ∀ {i j : Q}, (i ⟶ j) → B) : ∀ {i j : Q}, Path i j → B
  | i, _, Path.nil => P i
  | _, _, Path.cons p e => evPath P A p * A e

variable {P : Q → B} {A : ∀ {i j : Q}, (i ⟶ j) → B}

theorem evPath_mul_idem (hR : PathRelations P A) {i j : Q} (p : Path i j) :
    evPath P A p * P j = evPath P A p := by
  induction p with
  | nil => simp [evPath, hR.idem_mul]
  | cons p e ih => rw [evPath, mul_assoc, hR.arrow_mul_idem]; simp

theorem idem_mul_evPath (hR : PathRelations P A) {i j : Q} (p : Path i j) :
    P i * evPath P A p = evPath P A p := by
  induction p with
  | nil => simp [evPath, hR.idem_mul]
  | cons p e ih => rw [evPath, ← mul_assoc, ih]

theorem evPath_comp (hR : PathRelations P A) {i j l : Q} (p : Path i j) (q : Path j l) :
    evPath P A (p.comp q) = evPath P A p * evPath P A q := by
  induction q with
  | nil => rw [Path.comp_nil, evPath, evPath_mul_idem hR]
  | cons q e ih => rw [Path.comp_cons, evPath, evPath, ih, mul_assoc]

theorem evPath_mul_evPath_ne (hR : PathRelations P A) {i j j' l : Q} (p : Path i j) (q : Path j' l)
    (h : j ≠ j') : evPath P A p * evPath P A q = 0 := by
  calc evPath P A p * evPath P A q = (evPath P A p * P j) * (P j' * evPath P A q) := by
        rw [evPath_mul_idem hR, idem_mul_evPath hR]
    _ = 0 := by
        rw [mul_assoc, ← mul_assoc (P j), hR.idem_mul]; simp [h]

/-- The linear map `P_Q → B` sending the path `p` to `evPath p`. -/
noncomputable def pathLift (P : Q → B) (A : ∀ {i j : Q}, (i ⟶ j) → B) : PathAlgebra k Q →ₗ[k] B :=
  (pathAlgebraBasis (k := k) (Q := Q)).constr k fun p => evPath P A p.2.2

theorem pathLift_pathElem (p : AnyPath Q) :
    pathLift (k := k) P A (pathElem p) = evPath P A p.2.2 := by
  have : (pathElem p : PathAlgebra k Q) = pathAlgebraBasis p := by simp [pathAlgebraBasis]
  rw [this, pathLift, Module.Basis.constr_basis]

theorem pathLift_mul (hR : PathRelations P A) (x y : PathAlgebra k Q) :
    pathLift (k := k) P A (x * y) = pathLift P A x * pathLift P A y := by
  have hbil : ((LinearMap.mul k (PathAlgebra k Q)).compr₂ (pathLift (k := k) P A)) =
      (LinearMap.mul k B).compl₁₂ (pathLift P A) (pathLift P A) := by
    apply (pathAlgebraBasis (k := k) (Q := Q)).ext
    intro p
    apply (pathAlgebraBasis (k := k) (Q := Q)).ext
    intro q
    have hp : (pathAlgebraBasis (k := k) (Q := Q) p) = pathElem p := by simp [pathAlgebraBasis]
    have hq : (pathAlgebraBasis (k := k) (Q := Q) q) = pathElem q := by simp [pathAlgebraBasis]
    obtain ⟨i, j, p⟩ := p
    obtain ⟨j', l, q⟩ := q
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply, hp, hq]
    rw [pathLift_pathElem, pathLift_pathElem, pathElem_mul]
    by_cases hj : j = j'
    · subst hj
      rw [concatPath_eq_some]
      simp only [Option.elim]
      rw [pathLift_pathElem]
      exact evPath_comp hR p q
    · rw [concatPath_eq_none _ _ hj]
      simp only [Option.elim, map_zero]
      exact (evPath_mul_evPath_ne hR p q hj).symm
  exact LinearMap.congr_fun₂ hbil x y

/-- The algebra homomorphism `P_Q → B` determined by elements satisfying the relations. -/
noncomputable def pathAlgLift (hR : PathRelations P A) : PathAlgebra k Q →ₐ[k] B :=
  AlgHom.ofLinearMap (pathLift P A)
    (by
      rw [pathElem_one, map_sum]
      simp only [pathLift_pathElem, trivialPath, evPath]
      exact hR.sum_eq_one)
    (pathLift_mul hR)

theorem pathAlgLift_idem (hR : PathRelations P A) (i : Q) :
    pathAlgLift (k := k) hR (idem k i) = P i := by
  change pathLift (k := k) P A (pathElem (trivialPath i)) = P i
  rw [pathLift_pathElem]
  simp only [trivialPath, evPath]

theorem pathAlgLift_arrow (hR : PathRelations P A) {i j : Q} (h : i ⟶ j) :
    pathAlgLift (k := k) hR (arrowElem k h) = A h := by
  change pathLift (k := k) P A (pathElem ⟨i, j, h.toPath⟩) = A h
  rw [pathLift_pathElem]
  simp only [Quiver.Hom.toPath, evPath]
  rw [hR.idem_mul_arrow]; simp

/-- Two algebra homomorphisms out of the path algebra that agree on the idempotents and the arrows are equal:
the idempotents and arrows generate the path algebra. -/
theorem pathAlgebra_hom_ext {Ψ Ψ' : PathAlgebra k Q →ₐ[k] B} (h1 : ∀ i, Ψ (idem k i) = Ψ' (idem k i))
    (h2 : ∀ {i j : Q} (h : i ⟶ j), Ψ (arrowElem k h) = Ψ' (arrowElem k h)) : Ψ = Ψ' := by
  have hpath : ∀ {i j : Q} (p : Path i j), Ψ (pathElem ⟨i, j, p⟩) = Ψ' (pathElem ⟨i, j, p⟩) := by
    intro i j p
    induction p with
    | nil => exact h1 i
    | cons p e ih => rw [pathElem_cons k, map_mul, map_mul, ih, h2]
  apply AlgHom.toLinearMap_injective
  apply (pathAlgebraBasis (k := k) (Q := Q)).ext
  rintro ⟨i, j, p⟩
  have hp : (pathAlgebraBasis (k := k) (Q := Q) ⟨i, j, p⟩) = pathElem ⟨i, j, p⟩ := by
    simp [pathAlgebraBasis]
  simp only [AlgHom.toLinearMap_apply, hp]
  exact hpath p

/-- **Problem 1.33 (universal property).** Families `P_i`, `A_h` in an algebra `B` satisfying the relations
extend uniquely to an algebra homomorphism `P_Q → B` with `p_i ↦ P_i`, `a_h ↦ A_h`. Together with the fact
that the relations hold for `p_i`, `a_h` themselves (`idem_mul_idem`, `idem_mul_pathElem`, `sum_idem`, ...), this
says that `P_Q` is generated by the `p_i` and `a_h` subject exactly to these relations. -/
@[kb "etingof2011" "Problem 1.33, p. 13"]
theorem exists_unique_pathAlgebra_lift (hR : PathRelations P A) :
    ∃! Φ : PathAlgebra k Q →ₐ[k] B,
      (∀ i, Φ (idem k i) = P i) ∧ ∀ {i j : Q} (h : i ⟶ j), Φ (arrowElem k h) = A h := by
  refine ⟨pathAlgLift hR, ⟨pathAlgLift_idem hR, pathAlgLift_arrow hR⟩, ?_⟩
  rintro Ψ ⟨h1, h2⟩
  exact pathAlgebra_hom_ext (fun i => by rw [h1, pathAlgLift_idem]) (fun h => by rw [h2, pathAlgLift_arrow])

/-- The elements `p_i` and `a_h` satisfy the relations of Problem 1.33 in the path algebra itself. -/
@[kb "etingof2011" "Problem 1.33, p. 13"]
theorem pathRelations_pathAlgebra :
    PathRelations (fun i : Q => (idem k i : PathAlgebra k Q)) (fun {_ _} h => arrowElem k h) where
  sum_eq_one := sum_idem k
  idem_mul i j := by
    by_cases h : i = j
    · subst h; simp [idem_mul_idem]
    · simp [h, idem_mul_idem_ne k h]
  idem_mul_arrow {i j} h l := by
    by_cases hl : l = i
    · subst hl; rw [if_pos rfl]; exact idem_mul_pathElem k h.toPath
    · rw [if_neg hl]
      unfold idem trivialPath arrowElem
      rw [pathElem_mul, concatPath_eq_none _ _ hl]
      rfl
  arrow_mul_idem {i j} h l := by
    by_cases hl : l = j
    · subst hl; rw [if_pos rfl]; exact pathElem_mul_idem k h.toPath
    · rw [if_neg hl]; exact pathElem_mul_idem_ne k h.toPath (Ne.symm hl)

end Presentation

end UndergradKB.RepresentationTheory
