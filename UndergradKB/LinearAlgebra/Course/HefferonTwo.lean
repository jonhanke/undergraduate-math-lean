import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.SupIndep
import UndergradKB.Common.Attr

/-! # Hefferon chapter Two (Hefferon-only rows) -/

namespace UndergradKB.LinearAlgebra.Course

open Matrix Submodule

section Two_I

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A one-element vector space is a trivial space (every vector is zero); every space has a zero. -/
@[kb "hefferon2020" "Two.I.1.6, p. 97", kb "hefferon2020" "Two.I.1.7, p. 98"]
theorem hefferon_Two_I_1_6 : (Subsingleton V ↔ ∀ v : V, v = 0) ∧ Nonempty V :=
  ⟨subsingleton_iff_forall_eq 0, ⟨0⟩⟩

/-- The solution set of a homogeneous system `A x = 0` is a subspace of `K^n`. -/
@[kb "hefferon2020" "Two.I.1.15, p. 101"]
theorem hefferon_Two_I_1_15 {m n : Type*} [Fintype n] (A : Matrix m n K) :
    ∃ W : Submodule K (n → K), (W : Set (n → K)) = {x | A *ᵥ x = 0} :=
  ⟨LinearMap.ker (Matrix.mulVecLin A), by ext x; simp⟩

/-- Every space has the trivial subspace and itself as subspaces; a subspace other than the whole
space is proper. -/
@[kb "hefferon2020" "Two.I.2.4, p. 107"]
theorem hefferon_Two_I_2_4 (W : Submodule K V) :
    (∀ v : V, v ∈ (⊥ : Submodule K V) ↔ v = 0) ∧ (∀ v : V, v ∈ (⊤ : Submodule K V)) ∧
      ⊥ ≤ W ∧ W ≤ ⊤ ∧ (W ≠ ⊤ ↔ W < ⊤) :=
  ⟨fun _ => Submodule.mem_bot K, fun _ => Submodule.mem_top, bot_le, le_top, lt_top_iff_ne_top.symm⟩

/-- Independence of subspaces: no nonzero vector of one lies in the join of the others. -/
@[kb "hefferon2020" "Two.III.4.9, p. 157"]
theorem hefferon_Two_III_4_9 {ι : Type*} (W : ι → Submodule K V) :
    iSupIndep W ↔ ∀ i, ∀ v ∈ W i, v ∈ ⨆ (j) (_ : j ≠ i), W j → v = 0 := by
  rw [iSupIndep_def]
  refine forall_congr' fun i => ?_
  rw [Submodule.disjoint_def]

/-- Every subspace of a vector space has a complement. -/
@[kb "hefferon2020" "Two.III.4.14, p. 158"]
theorem hefferon_Two_III_4_14 (W : Submodule K V) : ∃ W' : Submodule K V, IsCompl W W' :=
  Submodule.exists_isCompl W

/-- Two subspaces are complements iff they meet only in zero and together span. -/
@[kb "hefferon2020" "Two.III.4.14, p. 158"]
theorem hefferon_Two_III_4_14_iff (W₁ W₂ : Submodule K V) :
    IsCompl W₁ W₂ ↔ W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ :=
  ⟨fun h => ⟨h.inf_eq_bot, h.sup_eq_top⟩, fun h => ⟨disjoint_iff.2 h.1, codisjoint_iff.2 h.2⟩⟩

end Two_I

section Two_II

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The empty set is independent; a set containing the zero vector is dependent. -/
@[kb "hefferon2020" "Two.II.1.11, p. 122", kb "hefferon2020" "Two.II.1.12, p. 122"]
theorem hefferon_Two_II_1_11 :
    LinearIndepOn K id (∅ : Set V) ∧ ∀ S : Set V, (0 : V) ∈ S → ¬ LinearIndepOn K id S :=
  ⟨linearIndepOn_empty K id, fun S h hS => hS.ne_zero h rfl⟩

/-- A set is independent iff removing any one member strictly shrinks the span. -/
@[kb "hefferon2020" "Two.II.1.14, p. 123"]
theorem hefferon_Two_II_1_14 (S : Set V) :
    LinearIndepOn K id S ↔ ∀ v ∈ S, span K (S \ {v}) < span K S := by
  rw [linearIndepOn_iff_notMem_span]
  simp only [Set.image_id]
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  constructor
  · intro h
    refine lt_of_le_of_ne (span_mono Set.sdiff_subset) fun e => h ?_
    rw [e]; exact subset_span hv
  · intro h hmem
    refine h.not_ge (span_le.2 fun s hs => ?_)
    by_cases e : s = v
    · exact e ▸ hmem
    · exact subset_span ⟨hs, e⟩

/-- Adding a new vector to an independent set keeps independence iff the vector is outside the
span. -/
@[kb "hefferon2020" "Two.II.1.15, p. 123"]
theorem hefferon_Two_II_1_15 {S : Set V} (hS : LinearIndepOn K id S) {v : V} (hv : v ∉ S) :
    LinearIndepOn K id (insert v S) ↔ v ∉ span K S :=
  (linearIndepOn_id_insert hv).trans ⟨fun h => h.2, fun h => ⟨hS, h⟩⟩

/-- A subset of an independent set is independent; a superset of a dependent set is dependent. -/
@[kb "hefferon2020" "Two.II.1.20, p. 126"]
theorem hefferon_Two_II_1_20 {S T : Set V} (h : T ⊆ S) :
    (LinearIndepOn K id S → LinearIndepOn K id T) ∧
      (¬ LinearIndepOn K id T → ¬ LinearIndepOn K id S) :=
  ⟨fun hS => hS.mono h, fun hT hS => hT (hS.mono h)⟩

/-- The trivial space has the empty basis and dimension zero. -/
@[kb "hefferon2020" "Two.III.1.8, p. 132", kb "hefferon2020" "Two.III.2.9, p. 141"]
theorem hefferon_Two_III_1_8 [Subsingleton V] :
    Nonempty (Module.Basis (Fin 0) K V) ∧ Module.finrank K V = 0 :=
  ⟨⟨Module.Basis.empty V⟩, Module.finrank_zero_of_subsingleton⟩

end Two_II

end UndergradKB.LinearAlgebra.Course
