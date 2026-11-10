import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 20: vector spaces (course layer)

Thin wrappers around Mathlib for the basic results on vector spaces: scalar identities, spans,
linear independence, bases and dimension. -/

namespace UndergradKB.AbstractAlgebra.Course

open Module Set

/-- AA-353. In a vector space `0 v = 0`, `α 0 = 0`, `α v = 0` forces `α = 0` or `v = 0`,
`(-1) v = -v`, and `-(α v) = (-α) v = α (-v)`. -/
@[kb "judson2026" "Proposition 20.1.5, p. 276"]
theorem judson_20_1_5 {F V : Type*} [Field F] [AddCommGroup V] [Module F V] (α : F) (v : V) :
    (0 : F) • v = 0 ∧ α • (0 : V) = 0 ∧ (α • v = 0 → α = 0 ∨ v = 0) ∧
    (-1 : F) • v = -v ∧ -(α • v) = (-α) • v ∧ (-α) • v = α • (-v) :=
  ⟨zero_smul F v, smul_zero α, fun h => smul_eq_zero.mp h, neg_one_smul F v, (neg_smul α v).symm,
    (neg_smul α v).trans (smul_neg α v).symm⟩

/-- AA-356. The span of finitely many vectors is a subspace, namely the set of their linear
combinations. -/
@[kb "judson2026" "Proposition 20.2.3, p. 277"]
theorem judson_20_2_3 {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {n : ℕ}
    (v : Fin n → V) :
    ∃ W : Submodule F V, (W : Set V) = {x | ∃ α : Fin n → F, ∑ i, α i • v i = x} := by
  refine ⟨Submodule.span F (range v), ?_⟩
  ext x
  exact Submodule.mem_span_range_iff_exists_fun F

/-- AA-358. If `v₁, …, vₙ` are linearly independent, the coefficients of a vector with respect
to them are unique. -/
@[kb "judson2026" "Proposition 20.3.1, p. 278"]
theorem judson_20_3_1 {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {n : ℕ}
    {v : Fin n → V} (hv : LinearIndependent F v) (α β : Fin n → F)
    (h : ∑ i, α i • v i = ∑ i, β i • v i) : α = β := by
  have h0 : ∑ i, (α - β) i • v i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  funext i
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hv (α - β) h0 i)

/-- AA-359. A family of vectors is linearly dependent iff one of its members is a linear
combination of the others. -/
@[kb "judson2026" "Proposition 20.3.2, p. 278"]
theorem judson_20_3_2 {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {ι : Type*}
    (v : ι → V) :
    ¬ LinearIndependent F v ↔ ∃ i, v i ∈ Submodule.span F (v '' (univ \ {i})) := by
  rw [linearIndependent_iff_notMem_span]
  simp only [not_forall, not_not]

/-- AA-360. If `V` is spanned by `n` vectors then any `m > n` vectors of `V` are linearly
dependent. -/
@[kb "judson2026" "Proposition 20.3.3, p. 278"]
theorem judson_20_3_3 {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {n m : ℕ}
    (v : Fin n → V) (hv : Submodule.span F (range v) = ⊤) (hnm : n < m) (w : Fin m → V) :
    ¬ LinearIndependent F w := by
  intro hw
  classical
  have h := linearIndependent_le_span_finset w hw (Finset.univ.image v) (by simpa using hv)
  have h2 : (Finset.univ.image v).card ≤ n := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := v)
  have h3 : (m : Cardinal.{0}) ≤ ((Finset.univ.image v).card : Cardinal.{0}) := by
    simpa using h
  have := Nat.cast_le.mp h3
  omega

/-- AA-362. Any two bases of a vector space have the same size (there is a bijection of the index
types), so the dimension is well defined: it is the cardinality of any basis. -/
@[kb "judson2026" "Proposition 20.3.6, p. 279"]
theorem judson_20_3_6 {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {ι κ : Type*}
    (b : Basis ι F V) (b' : Basis κ F V) :
    Nonempty (ι ≃ κ) ∧ finrank F V = Nat.card ι :=
  ⟨⟨b.indexEquiv b'⟩, finrank_eq_nat_card_basis b⟩

/-- AA-363. In an `n`-dimensional space, any `n` independent vectors span, hence form a basis. -/
@[kb "judson2026" "Theorem 20.3.7, p. 279"]
theorem judson_20_3_7_indep {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n : ℕ} (hn : finrank F V = n) (v : Fin n → V)
    (hv : LinearIndependent F v) : Submodule.span F (range v) = ⊤ :=
  hv.span_eq_top_of_card_eq_finrank' (by simpa using hn.symm)

/-- AA-363. In an `n`-dimensional space, any `n` spanning vectors are linearly independent, hence
form a basis. -/
theorem judson_20_3_7_span {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {n : ℕ} (hn : finrank F V = n) (v : Fin n → V) (hv : Submodule.span F (range v) = ⊤) :
    LinearIndependent F v :=
  linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simpa using hn.symm)

/-- AA-364. In an `n`-dimensional space, linearly independent vectors `v₁, …, v_k` extend to a
basis (a set of `n` independent vectors spanning `V`, containing all the `vᵢ`). -/
@[kb "judson2026" "Theorem 20.3.7, p. 279"]
theorem judson_20_3_7_extend {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n k : ℕ} (hn : finrank F V = n) (v : Fin k → V)
    (hv : LinearIndependent F v) :
    ∃ B : Set V, range v ⊆ B ∧ LinearIndepOn F id B ∧ Submodule.span F B = ⊤ ∧
      B.ncard = n := by
  have hs : LinearIndepOn F id (range v) := hv.linearIndepOn_id
  refine ⟨range (Basis.extend hs), ?_, ?_, ?_, ?_⟩
  · rw [Basis.range_extend]
    exact hs.subset_extend (subset_univ _)
  · exact (Basis.extend hs).linearIndependent.linearIndepOn_id
  · exact (Basis.extend hs).span_eq
  · rw [← hn, finrank_eq_nat_card_basis (Basis.extend hs), ← Nat.card_range_of_injective
      (Basis.extend hs).injective]
    exact (Nat.card_coe_set_eq _).symm

end UndergradKB.AbstractAlgebra.Course
