import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Defs.Unbundled
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.RepresentationTheory.ProblemsQuiversSym2
import UndergradKB.Common.Attr

/-! # Jordan-Hölder series of quiver representations (Etingof et al., Problem 5.41 (b))

For a finite quiver `Q` without oriented cycles and a finite-dimensional representation `V` we build a
chain of subrepresentations `0 = V_0 ≤ V_1 ≤ ⋯ ≤ V_N = V`, `N = Σ_x dim V_x`, in which each step adds
exactly one dimension, at a vertex `i_t`.  Each successive quotient is therefore the simple
representation `S_{i_t}` (one-dimensional at `i_t`, zero elsewhere), and the vertex `x` occurs exactly
`dim V_x` times among the `i_t`.  For `V_α` (dimension vector `α`) the composition factors are `S_x` with
multiplicity `α_x`.

The quotients themselves are not formalised as representations; the statement is the dimension
condition at each step.
-/

namespace UndergradKB.RepresentationTheory

open _root_.Quiver

universe u v w a

namespace QRep

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

/-- The relation "there is an arrow from `x` to `y`" (as a `Prop`). -/
def arrowRel (Q : Type v) [Quiver.{a} Q] (x y : Q) : Prop := Nonempty (x ⟶ y)

lemma exists_path_of_transGen {x y : Q} (h : Relation.TransGen (arrowRel Q) x y) :
    ∃ p : Path x y, 0 < p.length := by
  induction h with
  | single hr =>
    obtain ⟨e⟩ := hr
    exact ⟨Path.nil.cons e, by simp⟩
  | tail _ hr ih =>
    obtain ⟨e⟩ := hr
    obtain ⟨p, _⟩ := ih
    exact ⟨p.cons e, by simp⟩

lemma not_transGen_self [Finite Q] (hQ : NoOrientedCycles Q) (x : Q) :
    ¬ Relation.TransGen (arrowRel Q) x x := by
  intro h
  obtain ⟨p, hp⟩ := exists_path_of_transGen h
  have := hQ x p
  omega

lemma exists_source [Finite Q] (hQ : NoOrientedCycles Q) (P : Q → Prop) (hne : ∃ x, P x) :
    ∃ j, P j ∧ ∀ x, P x → ¬ Relation.TransGen (arrowRel Q) x j := by
  haveI : Std.Irrefl (Relation.TransGen (arrowRel Q)) := ⟨not_transGen_self hQ⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen (arrowRel Q))
  obtain ⟨a, ha, hmin⟩ := wf.has_min {x | P x} hne
  exact ⟨a, ha, fun x hx => hmin x hx⟩

lemma exists_hyperplane {M : Type*} [AddCommGroup M] [Module k M] (N : Submodule k M)
    [Module.Finite k N] (hN : N ≠ ⊥) : ∃ H : Submodule k M, H ≤ N ∧
      Module.finrank k N = Module.finrank k H + 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl (Submodule.span k {(⟨v, hv⟩ : N)})
  refine ⟨K.map N.subtype, by
    rintro _ ⟨y, _, rfl⟩; exact y.2, ?_⟩
  rw [Submodule.finrank_map_subtype_eq]
  have h1 := Submodule.finrank_add_eq_of_isCompl hK
  have h2 : Module.finrank k (Submodule.span k {(⟨v, hv⟩ : N)}) = 1 :=
    finrank_span_singleton (by simpa using hv0)
  omega

variable [Finite Q]

/-- The inductive construction of the chain (for a subrepresentation `T`, by induction on its total
dimension `n`). -/
theorem exists_chain (hQ : NoOrientedCycles Q) (V : QRep.{u, v, w, a} k Q)
    [∀ x, Module.Finite k (V.obj x)] [Fintype Q] [DecidableEq Q] [Nonempty Q] :
    ∀ (n : ℕ) (T : Subrep V), ∑ x, Module.finrank k (T.carrier x) = n →
    ∃ (c : ℕ → Subrep V) (i : ℕ → Q), c 0 = ⊥ ∧ c n = T ∧ ∀ t < n,
      (∀ x, (c t).carrier x ≤ (c (t + 1)).carrier x) ∧
      ∀ x, Module.finrank k ((c (t + 1)).carrier x) =
        Module.finrank k ((c t).carrier x) + if x = i t then 1 else 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro T hT
    have hz : ∀ x, T.carrier x = ⊥ := by
      intro x
      have := (Finset.sum_eq_zero_iff.1 hT) x (Finset.mem_univ x)
      exact Submodule.finrank_eq_zero.1 this
    have hTb : T = ⊥ := Subrep.ext fun x => by rw [hz x]; rfl
    exact ⟨fun _ => ⊥, fun _ => Classical.arbitrary _, rfl, hTb.symm, fun t ht => absurd ht (by omega)⟩
  | succ n ih =>
    intro T hT
    have hex : ∃ x, T.carrier x ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      have : ∑ x, Module.finrank k (T.carrier x) = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [hcon x]; simp
      omega
    obtain ⟨j, hj, hmin⟩ := exists_source hQ (fun x => T.carrier x ≠ ⊥) hex
    obtain ⟨H, hHle, hH⟩ := exists_hyperplane (T.carrier j) hj
    let T' : Subrep V :=
      { carrier := Function.update (fun x => T.carrier x) j H
        map_mem := by
          intro x y e z hz
          by_cases hy : y = j
          · subst hy
            have hx : x ≠ y := by
              rintro rfl
              exact not_transGen_self hQ x (Relation.TransGen.single ⟨e⟩)
            have hTx : T.carrier x = ⊥ := by
              by_contra hne
              exact hmin x hne (Relation.TransGen.single ⟨e⟩)
            rw [Function.update_of_ne hx, hTx] at hz
            rw [Submodule.mem_bot] at hz
            subst hz
            simp
          · have hz' : z ∈ T.carrier x := by
              by_cases hx : x = j
              · subst hx
                rw [Function.update_self] at hz
                exact hHle hz
              · rwa [Function.update_of_ne hx] at hz
            rw [Function.update_of_ne hy]
            exact T.map_mem e hz' }
    have hdim : ∀ x, Module.finrank k (T.carrier x) =
        Module.finrank k (T'.carrier x) + if x = j then 1 else 0 := by
      intro x
      by_cases hx : x = j
      · subst hx
        show _ = Module.finrank k (Function.update (fun x => T.carrier x) x H x) + _
        rw [Function.update_self]; simpa using hH
      · show _ = Module.finrank k (Function.update (fun x => T.carrier x) j H x) + _
        rw [Function.update_of_ne hx]; simp [hx]
    have hsum : ∑ x, Module.finrank k (T'.carrier x) = n := by
      have : ∑ x, Module.finrank k (T.carrier x) =
          ∑ x, Module.finrank k (T'.carrier x) + 1 := by
        rw [Finset.sum_congr rfl fun x _ => hdim x, Finset.sum_add_distrib]
        simp
      omega
    obtain ⟨c', i', hc0, hcn, hstep⟩ := ih T' hsum
    refine ⟨fun t => if t ≤ n then c' t else T, fun t => if t < n then i' t else j, ?_, ?_, ?_⟩
    · simp [hc0]
    · simp
    · intro t ht
      by_cases htn : t < n
      · have h1 : t ≤ n := by omega
        have h2 : t + 1 ≤ n := by omega
        beta_reduce
        rw [if_pos h1, if_pos h2, if_pos htn]
        exact hstep t htn
      · have htn' : t = n := by omega
        subst htn'
        beta_reduce
        rw [if_pos le_rfl, if_neg (show ¬ (t + 1 ≤ t) by omega), if_neg (lt_irrefl t), hcn]
        refine ⟨fun x => ?_, hdim⟩
        show Function.update (fun x => T.carrier x) j H x ≤ T.carrier x
        by_cases hx : x = j
        · subst hx; rw [Function.update_self]; exact hHle
        · rw [Function.update_of_ne hx]

/-- The quotient representation `T / S` of a subrepresentation `T` by a smaller subrepresentation
`S` (the smallness `S ≤ T` is only needed to interpret it). -/
def Subrep.quot {V : QRep.{u, v, w, a} k Q} (S T : Subrep V) : QRep.{u, v, w, a} k Q where
  obj x := ↥(T.carrier x) ⧸ (S.carrier x).comap (T.carrier x).subtype
  map {x y} e := Submodule.mapQ _ _ ((V.map e).restrict (fun z hz => T.map_mem e hz))
    (fun z hz => S.map_mem e hz)

lemma finrank_quot_obj {V : QRep.{u, v, w, a} k Q} [∀ x, Module.Finite k (V.obj x)]
    {S T : Subrep V} (h : ∀ x, S.carrier x ≤ T.carrier x) (x : Q) :
    Module.finrank k ((Subrep.quot S T).obj x) + Module.finrank k (S.carrier x) =
      Module.finrank k (T.carrier x) := by
  have h1 := Submodule.finrank_quotient_add_finrank
    ((S.carrier x).comap (T.carrier x).subtype)
  have h2 := (Submodule.comapSubtypeEquivOfLe (h x)).finrank_eq
  show Module.finrank k (↥(T.carrier x) ⧸ (S.carrier x).comap (T.carrier x).subtype) + _ = _
  omega

variable [DecidableEq Q]

/-- If `T` has exactly one more dimension than `S` at the vertex `i` and the same dimension
elsewhere, then `T / S` is the simple representation at `i`. -/
theorem quot_isSimpleAt {V : QRep.{u, v, w, a} k Q} [∀ x, Module.Finite k (V.obj x)]
    {S T : Subrep V} (h : ∀ x, S.carrier x ≤ T.carrier x) (i : Q)
    (hd : ∀ x, Module.finrank k (T.carrier x) =
      Module.finrank k (S.carrier x) + if x = i then 1 else 0) :
    (Subrep.quot S T).IsSimpleAt i := by
  have key : ∀ x, Module.finrank k ((Subrep.quot S T).obj x) = if x = i then 1 else 0 := by
    intro x
    have := finrank_quot_obj h x
    have := hd x
    omega
  haveI : ∀ x, Module.Finite k ((Subrep.quot S T).obj x) := fun x =>
    inferInstanceAs (Module.Finite k (↥(T.carrier x) ⧸
      (S.carrier x).comap (T.carrier x).subtype))
  refine ⟨fun j hj => ?_, ?_⟩
  · have := key j
    rw [if_neg hj] at this
    exact Module.finrank_zero_iff.1 this
  · rw [← Module.finrank_eq_rank, key i, if_pos rfl]
    simp

variable [Fintype Q] [Nonempty Q]

/-- **Problem 5.41 (b), Jordan-Hölder series.**  Let `Q` be a finite quiver without oriented cycles and
`V` a finite-dimensional representation, with `N = Σ_x dim V_x`.  There is a chain of
subrepresentations `0 = V_0 ≤ V_1 ≤ ⋯ ≤ V_N = V` and vertices `i_0, …, i_{N-1}` such that each
successive quotient `V_{t+1}/V_t` is the simple representation at `i_t`, and every vertex `x` occurs
exactly `dim V_x` times among the `i_t` (so for `V_α` the composition factors are `S_x` with
multiplicity `α_x`). -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem jordanHolder (hQ : NoOrientedCycles Q) (V : QRep.{u, v, w, a} k Q)
    [∀ x, Module.Finite k (V.obj x)] :
    ∃ (c : ℕ → Subrep V) (i : ℕ → Q), c 0 = ⊥ ∧ c (∑ x, V.dimVec x) = ⊤ ∧
      (∀ t < ∑ x, V.dimVec x, (∀ x, (c t).carrier x ≤ (c (t + 1)).carrier x) ∧
        (Subrep.quot (c t) (c (t + 1))).IsSimpleAt (i t)) ∧
      ∀ x, ((Finset.range (∑ y, V.dimVec y)).filter (fun t => i t = x)).card = V.dimVec x := by
  obtain ⟨c, i, h0, hN, hstep⟩ := exists_chain hQ V (∑ x, V.dimVec x) ⊤ (by
    refine Finset.sum_congr rfl fun x _ => ?_
    exact finrank_top k (V.obj x))
  refine ⟨c, i, h0, hN, fun t ht => ⟨(hstep t ht).1, quot_isSimpleAt (hstep t ht).1 (i t)
    (hstep t ht).2⟩, fun x => ?_⟩
  have hcount : ∀ t, t ≤ ∑ y, V.dimVec y →
      Module.finrank k ((c t).carrier x) = ((Finset.range t).filter (fun s => i s = x)).card := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [h0, Subrep.bot_carrier]; simp
    | succ t ih =>
      intro ht
      have h1 := (hstep t (by omega)).2 x
      rw [h1, ih (by omega), Finset.range_add_one, Finset.filter_insert]
      by_cases hx : x = i t
      · simp [hx]
      · simp [hx, Ne.symm hx]
  have := hcount _ le_rfl
  rw [hN] at this
  have e : Module.finrank k ((⊤ : Subrep V).carrier x) = V.dimVec x := finrank_top k _
  rw [e] at this
  exact this.symm

end QRep

end UndergradKB.RepresentationTheory
