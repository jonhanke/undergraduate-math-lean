import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import UndergradKB.Common.Attr

/-! # The path algebra of a finite quiver (Etingof et al., Definition 1.31, Remark 1.32)

Mathlib has quiver paths (`Quiver.Path`) but no path algebra.  To avoid proving associativity of a
partially defined product by hand, the path algebra `PathAlgebra k Q` is realised inside the
endomorphism algebra of the free `k`-module on all paths: the path `p` acts by `pathOp p`, sending the
basis vector `q` to the concatenation `p q` when the end of `p` is the start of `q` and to `0`
otherwise.  The path algebra is the span of these operators.

* `pathOp_mul`: `pathOp p * pathOp q` is `pathOp (p q)` if `p, q` are composable and `0` otherwise
  (the multiplication of Definition 1.31).
* `pathOp_linearIndependent` and `pathAlgebraBasis`: the paths form a basis.
* `one_eq_sum_trivial`: for a finite quiver the unit is the sum of the trivial paths (Remark 1.32).
* Not included: the correspondence between quiver representations and path algebra modules.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Quiver

variable (Q : Type u) [Quiver.{v + 1} Q]

/-- A path in `Q` together with its endpoints. -/
abbrev AnyPath : Type _ := Σ i j : Q, Path i j

variable {Q} [DecidableEq Q]

/-- Concatenation of two paths (end of the first equal to the start of the second), `none` if
they are not composable. -/
def concatPath : AnyPath Q → AnyPath Q → Option (AnyPath Q)
  | ⟨i, j, p⟩, ⟨j', l, q⟩ => if h : j = j' then some ⟨i, l, p.comp (h ▸ q)⟩ else none

theorem concatPath_eq_some {i j l : Q} (p : Path i j) (q : Path j l) :
    concatPath ⟨i, j, p⟩ ⟨j, l, q⟩ = some ⟨i, l, p.comp q⟩ := by
  simp [concatPath]

theorem concatPath_eq_none {i j j' l : Q} (p : Path i j) (q : Path j' l) (h : j ≠ j') :
    concatPath ⟨i, j, p⟩ ⟨j', l, q⟩ = none := by
  simp [concatPath, h]

variable (k : Type*) [CommRing k]

/-- The operator of left multiplication by the path `p` on the free module on all paths. -/
noncomputable def pathOp (p : AnyPath Q) : Module.End k (AnyPath Q →₀ k) :=
  Finsupp.linearCombination k fun q => (concatPath p q).elim 0 fun s => Finsupp.single s 1

variable {k}

theorem pathOp_single (p q : AnyPath Q) (c : k) :
    pathOp k p (Finsupp.single q c) = (concatPath p q).elim 0 fun s => Finsupp.single s c := by
  simp only [pathOp, Finsupp.linearCombination_single]
  cases concatPath p q <;> simp

theorem pathOp_mul (p q : AnyPath Q) :
    pathOp k p * pathOp k q = (concatPath p q).elim 0 (pathOp k) := by
  refine Finsupp.lhom_ext fun r c => ?_
  obtain ⟨i, j, p⟩ := p
  obtain ⟨j', l, q⟩ := q
  obtain ⟨a, b, r⟩ := r
  by_cases h1 : j = j'
  · subst h1
    rw [concatPath_eq_some]
    by_cases h2 : l = a
    · subst h2
      simp [pathOp_single, concatPath_eq_some, Path.comp_assoc]
    · simp [pathOp_single, concatPath_eq_none _ _ h2]
  · rw [concatPath_eq_none _ _ h1]
    by_cases h2 : l = a
    · subst h2
      simp [pathOp_single, concatPath_eq_some, concatPath_eq_none _ _ h1]
    · simp [pathOp_single, concatPath_eq_none _ _ h2]

/-- The trivial path at a vertex. -/
def trivialPath (i : Q) : AnyPath Q := ⟨i, i, Path.nil⟩

theorem pathOp_trivial_single (i : Q) (a b : Q) (r : Path a b) (c : k) :
    pathOp k (trivialPath i) (Finsupp.single ⟨a, b, r⟩ c) =
      if i = a then Finsupp.single ⟨a, b, r⟩ c else 0 := by
  by_cases h : i = a
  · subst h
    simp [pathOp_single, trivialPath, concatPath_eq_some]
  · simp [pathOp_single, trivialPath, concatPath_eq_none _ _ h, h]

theorem pathOp_single_trivial_self (a b : Q) (r : Path a b) :
    pathOp k ⟨a, b, r⟩ (Finsupp.single (trivialPath b) 1) = Finsupp.single ⟨a, b, r⟩ 1 := by
  simp [pathOp_single, trivialPath, concatPath_eq_some]

theorem pathOp_single_trivial_ne (a b' b : Q) (r : Path a b') (h : b' ≠ b) :
    pathOp k ⟨a, b', r⟩ (Finsupp.single (trivialPath b) 1) = 0 := by
  simp [pathOp_single, trivialPath, concatPath_eq_none _ _ h]

/-- For a finite quiver the unit is the sum of the trivial paths. -/
@[kb "etingof2011" "Remark 1.32, p. 13"]
theorem one_eq_sum_trivial [Fintype Q] :
    (1 : Module.End k (AnyPath Q →₀ k)) = ∑ i : Q, pathOp k (trivialPath i) := by
  refine Finsupp.lhom_ext fun r c => ?_
  obtain ⟨a, b, r⟩ := r
  simp [LinearMap.sum_apply, pathOp_trivial_single]

theorem linearCombination_pathOp_coord (l : AnyPath Q →₀ k) (a b : Q) (r : Path a b) :
    (Finsupp.linearCombination k (pathOp k) l) (Finsupp.single (trivialPath b) 1) ⟨a, b, r⟩ =
      l ⟨a, b, r⟩ := by
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single p c =>
    obtain ⟨a', b', r'⟩ := p
    rw [Finsupp.linearCombination_single]
    by_cases h : b' = b
    · subst h
      simp [pathOp_single_trivial_self, Finsupp.single_apply]
    · have : (⟨a', b', r'⟩ : AnyPath Q) ≠ ⟨a, b, r⟩ := fun e => h (by cases e; rfl)
      simp [pathOp_single_trivial_ne _ _ _ _ h, Finsupp.single_apply, this]

/-- Distinct paths give linearly independent operators. -/
theorem pathOp_linearIndependent :
    LinearIndependent k (pathOp k : AnyPath Q → Module.End k (AnyPath Q →₀ k)) := by
  show Function.Injective (Finsupp.linearCombination k (pathOp k))
  intro l l' h
  ext ⟨a, b, r⟩
  rw [← linearCombination_pathOp_coord l a b r, ← linearCombination_pathOp_coord l' a b r, h]

theorem pathOp_mul_mem (p q : AnyPath Q) :
    pathOp k p * pathOp k q ∈ Submodule.span k (Set.range (pathOp k)) := by
  rw [pathOp_mul]
  cases concatPath p q with
  | none => exact Submodule.zero_mem _
  | some s => exact Submodule.subset_span (Set.mem_range_self s)

theorem one_mem_pathSpan [Fintype Q] :
    (1 : Module.End k (AnyPath Q →₀ k)) ∈ Submodule.span k (Set.range (pathOp k)) := by
  rw [one_eq_sum_trivial]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_range_self _)

theorem mul_mem_pathSpan {a b : Module.End k (AnyPath Q →₀ k)}
    (ha : a ∈ Submodule.span k (Set.range (pathOp k)))
    (hb : b ∈ Submodule.span k (Set.range (pathOp k))) :
    a * b ∈ Submodule.span k (Set.range (pathOp k)) := by
  have := Submodule.mul_mem_mul ha hb
  rw [Submodule.span_mul_span] at this
  refine Submodule.span_le.2 ?_ this
  rintro _ ⟨_, ⟨p, rfl⟩, _, ⟨q, rfl⟩, rfl⟩
  exact pathOp_mul_mem p q

/-- The path algebra of a finite quiver: the span of the path operators `pathOp`. -/
@[kb "etingof2011" "Definition 1.31, p. 13"]
noncomputable def PathAlgebra (k : Type*) (Q : Type u) [CommRing k] [Quiver.{v + 1} Q]
    [DecidableEq Q] [Fintype Q] : Subalgebra k (Module.End k (AnyPath Q →₀ k)) :=
  Submodule.toSubalgebra (Submodule.span k (Set.range (pathOp k))) one_mem_pathSpan
    fun _ _ ha hb => mul_mem_pathSpan ha hb

variable [Fintype Q]

theorem mem_pathAlgebra_iff (x : Module.End k (AnyPath Q →₀ k)) :
    x ∈ PathAlgebra k Q ↔ x ∈ Submodule.span k (Set.range (pathOp k)) := Iff.rfl

/-- The path `p` as an element of the path algebra. -/
noncomputable def pathElem (p : AnyPath Q) : PathAlgebra k Q :=
  ⟨pathOp k p, (mem_pathAlgebra_iff _).2 (Submodule.subset_span (Set.mem_range_self p))⟩

theorem coe_pathElem (p : AnyPath Q) : ((pathElem p : PathAlgebra k Q) : Module.End k _) =
    pathOp k p := rfl

/-- The product of two path elements is their concatenation, or zero if they are not composable. -/
@[kb "etingof2011" "Definition 1.31, p. 13"]
theorem pathElem_mul (p q : AnyPath Q) :
    (pathElem p : PathAlgebra k Q) * pathElem q = (concatPath p q).elim 0 pathElem := by
  apply Subtype.ext
  have := pathOp_mul (k := k) p q
  cases hc : concatPath p q with
  | none => rw [hc] at this; simpa [coe_pathElem] using this
  | some s => rw [hc] at this; simpa [coe_pathElem] using this

/-- The unit of the path algebra is the sum of the trivial paths. -/
@[kb "etingof2011" "Remark 1.32, p. 13"]
theorem pathElem_one : (1 : PathAlgebra k Q) = ∑ i : Q, pathElem (trivialPath i) := by
  apply Subtype.ext
  simpa [coe_pathElem] using one_eq_sum_trivial (k := k) (Q := Q)

theorem pathElem_linearIndependent :
    LinearIndependent k (pathElem : AnyPath Q → PathAlgebra k Q) := by
  show Function.Injective (Finsupp.linearCombination k (pathElem : AnyPath Q → PathAlgebra k Q))
  intro l l' h
  have h1 : Finsupp.linearCombination k (pathOp k) l = Finsupp.linearCombination k (pathOp k) l' := by
    have := congrArg (fun z : PathAlgebra k Q => (z : Module.End k (AnyPath Q →₀ k))) h
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, coe_pathElem] using this
  exact pathOp_linearIndependent h1

theorem pathElem_span :
    (⊤ : Submodule k (PathAlgebra k Q)) ≤
      Submodule.span k (Set.range (pathElem : AnyPath Q → PathAlgebra k Q)) := by
  intro z _
  obtain ⟨x, hx⟩ := z
  have hx' : x ∈ Submodule.span k (Set.range (pathOp k)) := (mem_pathAlgebra_iff _).1 hx
  refine Submodule.span_induction
    (p := fun x _ => ∀ h : x ∈ PathAlgebra k Q, (⟨x, h⟩ : PathAlgebra k Q) ∈
      Submodule.span k (Set.range (pathElem : AnyPath Q → PathAlgebra k Q)))
    ?_ ?_ ?_ ?_ hx' hx
  · rintro _ ⟨p, rfl⟩ h
    exact Submodule.subset_span ⟨p, Subtype.ext rfl⟩
  · intro h
    exact Submodule.zero_mem _
  · intro x y hx hy ihx ihy h
    have hx2 := (mem_pathAlgebra_iff _).2 hx
    have hy2 := (mem_pathAlgebra_iff _).2 hy
    have e : (⟨x + y, h⟩ : PathAlgebra k Q) = ⟨x, hx2⟩ + ⟨y, hy2⟩ := rfl
    rw [e]
    exact Submodule.add_mem _ (ihx hx2) (ihy hy2)
  · intro c x hx ih h
    have hx2 := (mem_pathAlgebra_iff _).2 hx
    have e : (⟨c • x, h⟩ : PathAlgebra k Q) = c • ⟨x, hx2⟩ := rfl
    rw [e]
    exact Submodule.smul_mem _ c (ih hx2)

/-- The paths form a basis of the path algebra. -/
@[kb "etingof2011" "Definition 1.31, p. 13"]
noncomputable def pathAlgebraBasis : Module.Basis (AnyPath Q) k (PathAlgebra k Q) :=
  Module.Basis.mk pathElem_linearIndependent pathElem_span

end UndergradKB.RepresentationTheory

