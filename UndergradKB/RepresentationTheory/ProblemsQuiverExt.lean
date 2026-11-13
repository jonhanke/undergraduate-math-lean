import UndergradKB.RepresentationTheory.ProblemsQuiversSym2
import UndergradKB.Common.Attr

/-!
# Ext¹ against a simple representation at a source or sink

For a source `i` (no arrow ends at `i`) we have `Ext¹(V, S_i) = 0` for all `V`; for a sink `i` (no arrow starts
at `i`) we have `Ext¹(S_i, V) = 0` for all `V`.  In the cocycle model every cochain is already zero.
-/

universe u v w a

namespace UndergradKB.RepresentationTheory

open _root_.Quiver

namespace QRep

open scoped Classical

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{a} Q]

theorem subsingleton_simpleRep_obj {i x : Q} (h : x ≠ i) :
    Subsingleton ((simpleRep k i : QRep.{u, v, u, a} k Q).obj x) := by
  change Subsingleton (Fin (if x = i then 1 else 0) → k)
  rw [if_neg h]
  infer_instance

/-- At a source `i`, every extension cochain with values in `S_i` is zero. -/
theorem extCochain_simpleRep_source (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ x, IsEmpty (x ⟶ i))
    (c : ExtCochain V (simpleRep k i : QRep.{u, v, u, a} k Q)) : c = 0 := by
  funext x y e
  have hy : y ≠ i := by
    rintro rfl
    exact (hi x).false e
  haveI : Subsingleton ((simpleRep k i : QRep.{u, v, u, a} k Q).obj y) := subsingleton_simpleRep_obj hy
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _

/-- At a sink `i`, every extension cochain out of `S_i` is zero. -/
theorem extCochain_simpleRep_sink (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ y, IsEmpty (i ⟶ y))
    (c : ExtCochain (simpleRep k i : QRep.{u, v, u, a} k Q) V) : c = 0 := by
  funext x y e
  have hx : x ≠ i := by
    rintro rfl
    exact (hi y).false e
  haveI : Subsingleton ((simpleRep k i : QRep.{u, v, u, a} k Q).obj x) := subsingleton_simpleRep_obj hx
  apply LinearMap.ext
  intro v
  rw [Subsingleton.elim v 0]
  simp

/-- `Ext¹(V, S_i) = 0` at a source `i`: the coboundary map is surjective. -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem coboundary_surjective_source (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ x, IsEmpty (x ⟶ i)) :
    Function.Surjective (coboundary V (simpleRep k i : QRep.{u, v, u, a} k Q)) := fun c =>
  ⟨0, by rw [extCochain_simpleRep_source V hi c]; exact map_zero _⟩

/-- `Ext¹(S_i, V) = 0` at a sink `i`: the coboundary map is surjective. -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem coboundary_surjective_sink (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ y, IsEmpty (i ⟶ y)) :
    Function.Surjective (coboundary (simpleRep k i : QRep.{u, v, u, a} k Q) V) := fun c =>
  ⟨0, by rw [extCochain_simpleRep_sink V hi c]; exact map_zero _⟩

/-- `Ext¹(V, S_i)` is trivial at a source `i`. -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem subsingleton_qExt_source (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ x, IsEmpty (x ⟶ i)) :
    Subsingleton (QExt V (simpleRep k i : QRep.{u, v, u, a} k Q)) :=
  ⟨fun p q => by
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [extCochain_simpleRep_source V hi p, extCochain_simpleRep_source V hi q]⟩

/-- `Ext¹(S_i, V)` is trivial at a sink `i`. -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem subsingleton_qExt_sink (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ y, IsEmpty (i ⟶ y)) :
    Subsingleton (QExt (simpleRep k i : QRep.{u, v, u, a} k Q) V) :=
  ⟨fun p q => by
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [extCochain_simpleRep_sink V hi p, extCochain_simpleRep_sink V hi q]⟩

/-- At a source `i`, every extension of `V` by `S_i` splits: it is equivalent to the zero cochain. -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem extEquiv_zero_source (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ x, IsEmpty (x ⟶ i))
    (c : ExtCochain V (simpleRep k i : QRep.{u, v, u, a} k Q)) : ExtEquiv c 0 := by
  rw [extEquiv_iff, extCochain_simpleRep_source V hi (c - 0)]
  exact Submodule.zero_mem _

/-- At a sink `i`, every extension of `S_i` by `V` splits: it is equivalent to the zero cochain. -/
@[kb "etingof2011" "Problem 5.41, p. 97"]
theorem extEquiv_zero_sink (V : QRep.{u, v, u, a} k Q) {i : Q} (hi : ∀ y, IsEmpty (i ⟶ y))
    (c : ExtCochain (simpleRep k i : QRep.{u, v, u, a} k Q) V) : ExtEquiv c 0 := by
  rw [extEquiv_iff, extCochain_simpleRep_sink V hi (c - 0)]
  exact Submodule.zero_mem _

end QRep

end UndergradKB.RepresentationTheory
