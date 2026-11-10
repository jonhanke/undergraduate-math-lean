import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.Polynomial.Basic
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 2 (finite-dimensional vector spaces): book-named wrappers of Mathlib results
-/

namespace UndergradKB.LinearAlgebra.Course

open UndergradKB Module Submodule

universe v

variable {K : Type*} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-! ## 2A Span and linear independence -/

/-- Axler 2.2: a linear combination of `v₁, …, vₘ` is `a₁v₁ + ⋯ + aₘvₘ`. -/
@[kb "axler2024" "2.2, p. 46"]
theorem axler_2_2 {m : ℕ} (v : Fin m → V) (a : Fin m → K) :
    Fintype.linearCombination K v a = ∑ k, a k • v k := by
  simp [Fintype.linearCombination_apply]

/-- Axler 2.4: the span of a list is the set of its linear combinations; the empty list spans
`{0}`. -/
@[kb "axler2024" "2.4, p. 47", kb "hefferon2020" "One.I.3.Span, p. 37",
  kb "hefferon2020" "Two.I.2.13, p. 110", kb "hefferon2020" "Two.I.2.14, p. 110"]
theorem axler_2_4 {m : ℕ} (v : Fin m → V) :
    (∀ w : V, w ∈ span K (Set.range v) ↔ ∃ a : Fin m → K, ∑ k, a k • v k = w) ∧
    span K (Set.range (fun _ : Fin 0 => (0 : V))) = ⊥ :=
  ⟨fun w => mem_span_range_iff_exists_fun K, by simp⟩

/-- Axler 2.6: the span of a list is the smallest subspace containing every vector of the list. -/
@[kb "axler2024" "2.6, p. 47", kb "hefferon2020" "Two.I.2.15, p. 110",
  kb "hefferon2020" "Two.I.2.converse, p. 111",
  kb "hefferon2020" "Two.I.2.smallest, p. 111"]
theorem axler_2_6 {ι : Type*} (v : ι → V) :
    IsLeast {W : Submodule K V | ∀ i, v i ∈ W} (span K (Set.range v)) :=
  ⟨fun i => subset_span ⟨i, rfl⟩, fun W h => span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)⟩

/-- Axler 2.7: a list spans `V` when its span is `V`. -/
@[kb "axler2024" "2.7, p. 47"]
theorem axler_2_7 {ι : Type*} (v : ι → V) :
    span K (Set.range v) = ⊤ ↔ ∀ x : V, x ∈ span K (Set.range v) :=
  eq_top_iff'

/-- Axler 2.9: `V` is finite-dimensional iff some finite list spans it. -/
@[kb "axler2024" "2.9, p. 48", kb "hefferon2020" "Two.III.2.1, p. 139"]
theorem axler_2_9 :
    FiniteDimensional K V ↔ ∃ (m : ℕ) (v : Fin m → V), span K (Set.range v) = ⊤ := by
  classical
  constructor
  · intro h
    exact Module.Finite.exists_fin
  · rintro ⟨m, v, h⟩
    exact ⟨⟨Finset.univ.image v, by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact h⟩⟩

/-- Axler 2.11: degree of a polynomial: largest exponent with nonzero coefficient, and `-∞` for
the zero polynomial. -/
@[kb "axler2024" "2.11, p. 49"]
theorem axler_2_11 (p : Polynomial K) :
    (p ≠ 0 → p.coeff p.natDegree ≠ 0 ∧ ∀ k, p.coeff k ≠ 0 → k ≤ p.natDegree) ∧
    (0 : Polynomial K).degree = ⊥ :=
  ⟨fun h => ⟨Polynomial.leadingCoeff_ne_zero.mpr h, fun _ hk => Polynomial.le_natDegree_of_ne_zero hk⟩,
    Polynomial.degree_zero⟩

/-- Axler 2.12: `𝒫ₘ(F)` is the subspace of polynomials of degree at most `m`. -/
@[kb "axler2024" "2.12, p. 49", kb "hefferon2020" "Two.I.1.8, p. 98"]
theorem axler_2_12 (m : ℕ) (p : Polynomial K) :
    p ∈ Polynomial.degreeLE K (m : WithBot ℕ) ↔ p.degree ≤ m :=
  Polynomial.mem_degreeLE

/-- Axler 2.13: infinite-dimensional means no finite list spans. -/
@[kb "axler2024" "2.13, p. 49"]
theorem axler_2_13 :
    ¬ FiniteDimensional K V ↔ ∀ (m : ℕ) (v : Fin m → V), span K (Set.range v) ≠ ⊤ := by
  rw [axler_2_9]; push Not; rfl

/-- Axler 2.14: the space of polynomials `𝒫(F)` is infinite-dimensional. -/
@[kb "axler2024" "2.14, p. 49"]
theorem axler_2_14 : ¬ FiniteDimensional K (Polynomial K) :=
  Polynomial.not_finite

/-- Axler 2.15: a list is linearly independent iff the only vanishing combination is trivial. -/
@[kb "axler2024" "2.15, p. 50", kb "hefferon2020" "Two.II.1.4, p. 119",
  kb "hefferon2020" "Two.II.1.5, p. 120"]
theorem axler_2_15 {m : ℕ} (v : Fin m → V) :
    LinearIndependent K v ↔ ∀ a : Fin m → K, ∑ k, a k • v k = 0 → ∀ k, a k = 0 :=
  Fintype.linearIndependent_iff

/-- Axler 2.17: a list is linearly dependent iff some nontrivial combination vanishes. -/
@[kb "axler2024" "2.17, p. 51"]
theorem axler_2_17 {m : ℕ} (v : Fin m → V) :
    ¬ LinearIndependent K v ↔ ∃ a : Fin m → K, ∑ k, a k • v k = 0 ∧ ∃ k, a k ≠ 0 :=
  Fintype.not_linearIndependent_iff

/-- Axler 2.22: a linearly independent list is no longer than a spanning list. -/
@[kb "axler2024" "2.22, p. 53", kb "hefferon2020" "Two.III.2.10, p. 142"]
theorem axler_2_22 {m n : ℕ} (v : Fin m → V) (w : Fin n → V) (hv : LinearIndependent K v)
    (hw : span K (Set.range w) = ⊤) : m ≤ n := by
  have : FiniteDimensional K V := axler_2_9.mpr ⟨n, w, hw⟩
  have h1 := hv.fintype_card_le_finrank
  have h2 := finrank_range_le_card (R := K) w
  rw [Set.finrank, hw, finrank_top] at h2
  simp only [Fintype.card_fin] at h1 h2
  omega

/-- Axler 2.25: every subspace of a finite-dimensional space is finite-dimensional. -/
@[kb "axler2024" "2.25, p. 54"]
theorem axler_2_25 [FiniteDimensional K V] (U : Submodule K V) : FiniteDimensional K U :=
  inferInstance

/-! ## 2B Bases -/

/-- Axler 2.26: a basis is a linearly independent spanning list. -/
@[kb "axler2024" "2.26, p. 57", kb "hefferon2020" "Two.III.1.1, p. 131"]
theorem axler_2_26 (n : ℕ) :
    Nonempty (Basis (Fin n) K V) ↔
      ∃ v : Fin n → V, LinearIndependent K v ∧ span K (Set.range v) = ⊤ :=
  ⟨fun ⟨b⟩ => ⟨b, b.linearIndependent, b.span_eq⟩,
    fun ⟨_, h1, h2⟩ => ⟨Basis.mk h1 (le_of_eq h2.symm)⟩⟩

/-- Axler 2.28: a list is a basis iff each vector is a linear combination of it in exactly one
way. -/
@[kb "axler2024" "2.28, p. 57", kb "hefferon2020" "Two.III.1.12, p. 133"]
theorem axler_2_28 {n : ℕ} (v : Fin n → V) :
    (LinearIndependent K v ∧ span K (Set.range v) = ⊤) ↔
      ∀ x : V, ∃! a : Fin n → K, ∑ i, a i • v i = x := by
  constructor
  · rintro ⟨hli, hsp⟩ x
    have hx : x ∈ span K (Set.range v) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun K).mp hx
    refine ⟨a, ha, fun b hb => ?_⟩
    funext i
    have := Fintype.linearIndependent_iff.mp hli (b - a)
      (by simp [sub_smul, Finset.sum_sub_distrib, hb, ha])
    simpa [sub_eq_zero] using this i
  · intro h
    refine ⟨Fintype.linearIndependent_iff.mpr fun a ha i => ?_, ?_⟩
    · obtain ⟨c, _, hc⟩ := h 0
      have e1 := hc a ha
      have e2 := hc 0 (by simp)
      exact congrFun (e1.trans e2.symm) i
    · rw [eq_top_iff]
      intro x _
      obtain ⟨a, ha, _⟩ := h x
      exact (mem_span_range_iff_exists_fun K).mpr ⟨a, ha⟩

/-- Axler 2.30: every spanning list contains (a sublist that is) a basis. -/
@[kb "axler2024" "2.30, p. 58", kb "hefferon2020" "Two.II.1.17, p. 125",
  kb "hefferon2020" "Two.III.2.13, p. 142"]
theorem axler_2_30 {m : ℕ} (v : Fin m → V) (hv : span K (Set.range v) = ⊤) :
    ∃ s : Set (Fin m), LinearIndepOn K v s ∧ span K (v '' s) = ⊤ := by
  obtain ⟨b, -, -, h1, h2⟩ := exists_linearIndepOn_extension (K := K) (v := v)
    (linearIndepOn_empty K v) (Set.empty_subset (Set.univ : Set (Fin m)))
  refine ⟨b, h2, ?_⟩
  rw [eq_top_iff, ← hv]
  exact span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h1 ⟨i, Set.mem_univ i, rfl⟩)

/-- Axler 2.31: every finite-dimensional vector space has a basis (a list). -/
@[kb "axler2024" "2.31, p. 59"]
theorem axler_2_31 [FiniteDimensional K V] : ∃ n : ℕ, Nonempty (Basis (Fin n) K V) :=
  ⟨finrank K V, ⟨finBasis K V⟩⟩

/-- Axler 2.32: every linearly independent list in a finite-dimensional space extends to a basis
(a basis, indexed by a finite type, that contains every vector of the list). -/
@[kb "axler2024" "2.32, p. 59", kb "hefferon2020" "Two.III.2.12, p. 142"]
theorem axler_2_32 [FiniteDimensional K V] {m : ℕ} (v : Fin m → V) (hv : LinearIndependent K v) :
    ∃ (κ : Type v) (_ : Finite κ) (b : Basis κ K V), ∀ i, ∃ j, b j = v i :=
  ⟨_, Module.Finite.finite_basis (Basis.extend hv.linearIndepOn_id), Basis.extend hv.linearIndepOn_id,
    fun i => ⟨⟨v i, Basis.subset_extend hv.linearIndepOn_id ⟨i, rfl⟩⟩,
      Basis.extend_apply_self _ _⟩⟩

/-- Axler 2.33: every subspace `U` of `V` has a complement `W` with `V = U ⊕ W`. -/
@[kb "axler2024" "2.33, p. 60"]
theorem axler_2_33 (U : Submodule K V) : ∃ W : Submodule K V, IsCompl U W :=
  Submodule.exists_isCompl U

/-- Axler 2.34: any two bases of a finite-dimensional space have the same length. -/
@[kb "axler2024" "2.34, p. 62", kb "hefferon2020" "Two.III.2.4, p. 141"]
theorem axler_2_34 {m n : ℕ} (b : Basis (Fin m) K V) (b' : Basis (Fin n) K V) : m = n := by
  have h1 := finrank_eq_card_basis b
  have h2 := finrank_eq_card_basis b'
  simp only [Fintype.card_fin] at h1 h2
  omega

/-- Axler 2.35: the dimension is the length of any basis. -/
@[kb "axler2024" "2.35, p. 62", kb "hefferon2020" "Two.III.2.5, p. 141"]
theorem axler_2_35 {n : ℕ} (b : Basis (Fin n) K V) : finrank K V = n := by
  simpa using finrank_eq_card_basis b

/-- Axler 2.37: a subspace of a finite-dimensional space has dimension at most `dim V`. -/
@[kb "axler2024" "2.37, p. 63"]
theorem axler_2_37 [FiniteDimensional K V] (U : Submodule K V) : finrank K U ≤ finrank K V :=
  Submodule.finrank_le U

/-- Axler 2.38: a linearly independent list of length `dim V` is a basis (it spans). -/
@[kb "axler2024" "2.38, p. 63", kb "hefferon2020" "Two.III.2.14, p. 142"]
theorem axler_2_38 [FiniteDimensional K V] {n : ℕ} (v : Fin n → V) (hv : LinearIndependent K v)
    (hn : n = finrank K V) : span K (Set.range v) = ⊤ :=
  hv.span_eq_top_of_card_eq_finrank' (by simpa using hn)

/-- Axler 2.39: a subspace of full dimension is the whole space. -/
@[kb "axler2024" "2.39, p. 63", kb "hefferon2020" "Five.III.1.12, p. 438"]
theorem axler_2_39 [FiniteDimensional K V] (U : Submodule K V) (h : finrank K U = finrank K V) :
    U = ⊤ :=
  Submodule.eq_top_of_finrank_eq h

/-- Axler 2.42: a spanning list of length `dim V` is a basis (it is linearly independent). -/
@[kb "axler2024" "2.42, p. 64"]
theorem axler_2_42 [FiniteDimensional K V] {n : ℕ} (v : Fin n → V)
    (hv : span K (Set.range v) = ⊤) (hn : n = finrank K V) : LinearIndependent K v :=
  linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simpa using hn)

/-- Axler 2.43: `dim (U₁ + U₂) = dim U₁ + dim U₂ - dim (U₁ ∩ U₂)`. -/
@[kb "axler2024" "2.43, p. 65"]
theorem axler_2_43 [FiniteDimensional K V] (U₁ U₂ : Submodule K V) :
    finrank K (U₁ ⊔ U₂ : Submodule K V) = finrank K U₁ + finrank K U₂ - finrank K (U₁ ⊓ U₂ : Submodule K V) := by
  have := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
  omega

end UndergradKB.LinearAlgebra.Course
