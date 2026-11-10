import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Module
import UndergradKB.Common.Attr

/-! # Vector spaces (Axler 1-2 and 3E, Hefferon Two)

Subspace criteria, direct sums, spanning and independence lemmas, bases and dimension, the subspaces of
a three-dimensional space, translates of a subspace. -/

open Module Set Submodule

namespace UndergradKB.LinearAlgebra

section Subspace

variable {K V : Type*}

/-- For a nonempty subset `S`: being a subspace, being closed under combinations `a u + b v` of two
vectors, and being closed under all finite linear combinations are equivalent. -/
@[kb "hefferon2020" "Two.I.2.9, p. 108"]
theorem hefferon_Two_I_2_9 [Semiring K] [AddCommMonoid V] [Module K V] (S : Set V) (hS : S.Nonempty) :
    List.TFAE [∃ U : Submodule K V, (U : Set V) = S,
      ∀ (a b : K) (u v : V), u ∈ S → v ∈ S → a • u + b • v ∈ S,
      ∀ (k : ℕ) (c : Fin k → K) (v : Fin k → V), (∀ i, v i ∈ S) → ∑ i, c i • v i ∈ S] := by
  tfae_have 1 → 3 := by
    rintro ⟨U, rfl⟩ k c v hv
    exact U.sum_mem fun i _ => U.smul_mem _ (hv i)
  tfae_have 3 → 2 := fun h a b u v hu hv => by
    have := h 2 ![a, b] ![u, v] (by intro i; fin_cases i <;> simpa)
    simpa [Fin.sum_univ_two] using this
  tfae_have 2 → 1 := fun h => by
    obtain ⟨u₀, hu₀⟩ := hS
    have hz : (0 : V) ∈ S := by simpa using h 0 0 u₀ u₀ hu₀ hu₀
    have ha : ∀ {u v : V}, u ∈ S → v ∈ S → u + v ∈ S := fun {u v} hu hv => by
      simpa using h 1 1 u v hu hv
    have hm : ∀ (c : K) {u : V}, u ∈ S → c • u ∈ S := fun c {u} hu => by
      simpa using h c 0 u u hu hu
    exact ⟨{ carrier := S, zero_mem' := hz, add_mem' := ha, smul_mem' := hm }, rfl⟩
  tfae_finish

end Subspace

section DirectSum

variable {K N ι : Type*} [Ring K] [AddCommGroup N] [Module K N]

/-- A sum `V₁ + ... + Vₘ` is direct (every element of the sum has a unique representation) iff the only
way to write `0` as a sum is with all summands `0`. -/
@[kb "axler2024" "1.45, p. 41"]
theorem axler_1_45 [Fintype ι] (V : ι → Submodule K N) :
    (∀ x y : (∀ i, V i), ∑ i, (x i : N) = ∑ i, (y i : N) → x = y) ↔
      (∀ v : (∀ i, V i), ∑ i, (v i : N) = 0 → ∀ i, v i = 0) := by
  constructor
  · intro h v hv i
    have := h v 0 (by simpa using hv)
    exact congrFun this i
  · intro h x y hxy
    funext i
    have := h (x - y) (by simp [Finset.sum_sub_distrib, hxy]) i
    simpa [sub_eq_zero] using this

/-- The sum map `V₁ × ... × Vₘ → N`, `(v₁, ..., vₘ) ↦ v₁ + ... + vₘ`. -/
def sumMap [Fintype ι] (V : ι → Submodule K N) : (∀ i, V i) →ₗ[K] N :=
  ∑ i, (V i).subtype ∘ₗ LinearMap.proj i

@[simp] theorem sumMap_apply [Fintype ι] (V : ι → Submodule K N) (x : ∀ i, V i) :
    sumMap V x = ∑ i, (x i : N) := by
  simp [sumMap]

theorem range_sumMap [Fintype ι] (V : ι → Submodule K N) :
    LinearMap.range (sumMap V) = ⨆ i, V i := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [sumMap_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (x i).2
  · refine iSup_le fun i y hy => ⟨Pi.single i ⟨y, hy⟩, ?_⟩
    rw [sumMap_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp

/-- The sum map from the product `V₁ × ... × Vₘ` is injective iff the sum is direct (in Mathlib's
terms: the family of subspaces is independent). -/
@[kb "axler2024" "3.93, p. 116"]
theorem axler_3_93 [Fintype ι] [DecidableEq ι] (V : ι → Submodule K N) :
    Function.Injective (sumMap V) ↔ iSupIndep V := by
  classical
  rw [iSupIndep_iff_dfinsupp_lsum_injective]
  have key : ∀ d : Π₀ i, V i,
      DFinsupp.lsum ℕ (fun i => (V i).subtype) d = sumMap V (DFinsupp.equivFunOnFintype d) := by
    intro d
    rw [sumMap_apply, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
      DFinsupp.sum_eq_sum_fintype]
    · rfl
    · intro i; simp
  constructor
  · intro h d₁ d₂ hd
    rw [key, key] at hd
    exact DFinsupp.equivFunOnFintype.injective (h hd)
  · intro h x y hxy
    have := @h (DFinsupp.equivFunOnFintype.symm x) (DFinsupp.equivFunOnFintype.symm y)
      (by rw [key, key]; simpa using hxy)
    simpa using congrArg DFinsupp.equivFunOnFintype this

end DirectSum

section DirectSumDim

variable {K N ι : Type*} [DivisionRing K] [AddCommGroup N] [Module K N]

/-- A sum of finite-dimensional subspaces is direct iff the dimension of the sum is the sum of the
dimensions. -/
@[kb "axler2024" "3.94, p. 116"]
theorem axler_3_94 [Fintype ι] [DecidableEq ι] [FiniteDimensional K N]
    (V : ι → Submodule K N) :
    iSupIndep V ↔ finrank K (⨆ i, V i : Submodule K N) = ∑ i, finrank K (V i) := by
  rw [← axler_3_93, ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero, ← range_sumMap]
  have h1 := (sumMap V).finrank_range_add_finrank_ker
  rw [Module.finrank_pi_fintype] at h1
  omega

end DirectSumDim

section DecompBases

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

private lemma span_range_coe_basis {κ : Type*} (W : Submodule K V) (B : Basis κ K W) :
    span K (range fun j => (B j : V)) = W := by
  have := congrArg (Submodule.map W.subtype) B.span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, W.range_subtype] at this
  simpa [Function.comp_def] using this

/-- If `V = W₁ + ... + Wₖ` and `Bᵢ` is a basis of `Wᵢ`, these are equivalent: every vector decomposes
uniquely; the concatenation of the `Bᵢ` is linearly independent (hence a basis of `V`); nonzero vectors
from different `Wᵢ` satisfy only trivial relations. -/
@[kb "hefferon2020" "Two.III.4.8, p. 156"]
theorem hefferon_Two_III_4_8 (W : ι → Submodule K V) (hW : ⨆ i, W i = ⊤) {κ : ι → Type*}
    (B : ∀ i, Basis (κ i) K (W i)) :
    List.TFAE [∀ v : V, ∃! w : (∀ i, W i), ∑ i, (w i : V) = v,
      LinearIndependent K (fun p : (Σ i, κ i) => (B p.1 p.2 : V)),
      ∀ (s : Finset ι) (u : ι → V), (∀ i ∈ s, u i ∈ W i ∧ u i ≠ 0) →
        LinearIndependent K (fun i : s => u i)] := by
  classical
  have hsurj : Function.Surjective (sumMap W) := by
    rw [← LinearMap.range_eq_top, range_sumMap, hW]
  have h1 : (∀ v : V, ∃! w : (∀ i, W i), ∑ i, (w i : V) = v) ↔ iSupIndep W := by
    rw [← axler_3_93]
    have : (∀ v : V, ∃! w : (∀ i, W i), ∑ i, (w i : V) = v) ↔ Function.Bijective (sumMap W) := by
      rw [Function.bijective_iff_existsUnique]
      simp only [sumMap_apply]
    rw [this]
    exact ⟨fun h => h.1, fun h => ⟨h, hsurj⟩⟩
  have h3 : (∀ (s : Finset ι) (u : ι → V), (∀ i ∈ s, u i ∈ W i ∧ u i ≠ 0) →
        LinearIndependent K (fun i : s => u i)) ↔ iSupIndep W := by
    constructor
    · intro h
      rw [← axler_3_93]
      rw [injective_iff_map_eq_zero]
      intro x hx
      rw [sumMap_apply] at hx
      by_contra hne
      have hne' : ∃ i, x i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (funext hcon)
      set s : Finset ι := Finset.univ.filter fun i => x i ≠ 0 with hs
      have hli := h s (fun i => (x i : V)) (by
        intro i hi
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact ⟨(x i).2, fun h0 => hi (Subtype.ext h0)⟩)
      have hsum : ∑ i : s, (1 : K) • (x i : V) = 0 := by
        simp only [one_smul]
        rw [Finset.sum_coe_sort s (fun i => (x i : V)), hs, Finset.sum_filter]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_ : _ = ∑ i, (x i : V)) hx
        by_cases h0 : x i = 0 <;> simp [h0]
      obtain ⟨i, hi⟩ := hne'
      have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) hsum ⟨i, by simp [hs, hi]⟩
      exact one_ne_zero this
    · intro hind s u hu
      have := hind.comp (f := (Subtype.val : s → ι)) Subtype.val_injective
      exact iSupIndep.linearIndependent (W ∘ (Subtype.val : s → ι)) this (v := fun i => u i)
        (fun i => (hu i i.2).1) (fun i => (hu i i.2).2)
  have h2 : LinearIndependent K (fun p : (Σ i, κ i) => (B p.1 p.2 : V)) ↔ iSupIndep W := by
    constructor
    · intro hv
      have hle : ∀ j, W j ≤ span K ((fun p : (Σ i, κ i) => (B p.1 p.2 : V)) '' {p | p.1 = j}) :=
        fun j x hx => by
          have : x ∈ span K (range fun a => (B j a : V)) := by
            rw [span_range_coe_basis]; exact hx
          refine span_mono ?_ this
          rintro _ ⟨a, rfl⟩
          exact ⟨⟨j, a⟩, rfl, rfl⟩
      intro i
      refine Disjoint.mono (hle i) (iSup₂_le fun j hj => (hle j).trans (span_mono
        (Set.image_mono fun p hp => ?_))) (hv.disjoint_span_image (s := {p | p.1 = i})
          (t := {p | p.1 ≠ i}) (Set.disjoint_left.2 fun p hp hq => hq hp))
      exact fun h => hj (hp.symm.trans h)
    · intro hind
      have hint := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hind, hW⟩
      have := (hint.collectedBasis B).linearIndependent
      simpa [DirectSum.IsInternal.collectedBasis_coe] using this
  tfae_have 1 ↔ 2 := h1.trans h2.symm
  tfae_have 1 ↔ 3 := h1.trans h3.symm
  tfae_finish

end DecompBases

section Polynomials

open Polynomial

/-- Polynomials over a field form a vector space, and over an infinite field a polynomial is determined
by the function `z ↦ p(z)` it defines: the evaluation map into `K → K` is an injective linear map, so the
function-style definition of a polynomial agrees with Mathlib's formal polynomials. -/
@[kb "axler2024" "2.10, p. 48"]
theorem axler_2_10 (K : Type*) [Field K] [Infinite K] :
    ∃ L : K[X] →ₗ[K] (K → K), Function.Injective L ∧ ∀ p z, L p z = p.eval z := by
  refine ⟨LinearMap.pi fun z => Polynomial.leval z, fun p q h => ?_, fun p z => rfl⟩
  exact Polynomial.funext fun r => congrFun h r

end Polynomials

section SpanLemmas

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A linearly independent set is maximal (no linearly independent proper superset) iff it spans. -/
@[kb "hefferon2020" "Two.II.1.maximal, p. 127"]
theorem hefferon_Two_II_1_maximal (S : Set V) (hS : LinearIndepOn K id S) :
    (∀ T : Set V, LinearIndepOn K id T → S ⊆ T → T = S) ↔ span K S = ⊤ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨v, hv⟩ : ∃ v, v ∉ span K S := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_top_iff.2 fun v _ => hcon v)
    have hvS : v ∉ S := fun hv' => hv (subset_span hv')
    have hind : LinearIndepOn K id (insert v S) := ((linearIndepOn_id_insert hvS).2 ⟨hS, hv⟩)
    have := h _ hind (subset_insert v S)
    exact hvS (this ▸ mem_insert v S)
  · intro h T hT hST
    refine Subset.antisymm (fun v hvT => ?_) hST
    have hvspan : v ∈ span K S := by rw [h]; trivial
    rw [hS.mem_span_iff_id] at hvspan
    exact hvspan (hT.mono (insert_subset hvT hST))

/-- Linear dependence lemma: in a linearly dependent list some vector lies in the span of the earlier
ones, and deleting it does not change the span. -/
@[kb "axler2024" "2.19, p. 51"]
theorem axler_2_19 {m : ℕ} (v : Fin m → V) (h : ¬ LinearIndependent K v) :
    ∃ k : Fin m, v k ∈ span K (v '' {j | j < k}) ∧
      span K (v '' {j | j ≠ k}) = span K (range v) := by
  rcases m with _ | m
  · exact (h (linearIndependent_empty_type)).elim
  have hlast : ¬ LinearIndepOn K v (Set.Iic (Fin.last m)) := by
    have : Set.Iic (Fin.last m) = Set.univ := Set.eq_univ_of_forall fun i => Fin.le_last i
    rw [this, linearIndepOn_univ_iff]; exact h
  obtain ⟨k, hk, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Fin (m + 1)))
    {k | ¬ LinearIndepOn K v (Set.Iic k)} ⟨Fin.last m, hlast⟩
  have hIio : LinearIndepOn K v (Set.Iio k) := by
    by_cases hk0 : k = 0
    · subst hk0
      have : Set.Iio (0 : Fin (m + 1)) = ∅ := by
        ext j; simp
      rw [this]; exact linearIndepOn_empty _ _
    · have hlt : (⟨k.val - 1, by omega⟩ : Fin (m + 1)) < k := by
        rw [Fin.lt_def]; have : k.val ≠ 0 := fun h0 => hk0 (Fin.ext h0)
        show k.val - 1 < k.val
        omega
      have : LinearIndepOn K v (Set.Iic (⟨k.val - 1, by omega⟩ : Fin (m + 1))) := by
        by_contra hbad
        exact hmin _ hbad hlt
      convert this using 1
      ext j
      simp only [Set.mem_Iio, Set.mem_Iic, Fin.lt_def, Fin.le_def]
      have : k.val ≠ 0 := fun h0 => hk0 (Fin.ext h0)
      omega
  have hins : Set.Iic k = insert k (Set.Iio k) := by
    ext j; simp [le_iff_lt_or_eq, or_comm, eq_comm]
  have hkn : k ∉ Set.Iio k := by simp
  have hmem : v k ∈ span K (v '' Set.Iio k) := by
    by_contra hcon
    apply hk
    rw [hins, linearIndepOn_insert hkn]
    exact ⟨hIio, hcon⟩
  refine ⟨k, hmem, le_antisymm (span_mono (image_subset_range _ _)) ?_⟩
  rw [span_le]
  rintro _ ⟨j, rfl⟩
  by_cases hj : j = k
  · subst hj
    exact span_mono (image_mono fun i hi => ne_of_lt hi) hmem
  · exact subset_span ⟨j, hj, rfl⟩

/-- Adding `v` to a set leaves the span unchanged iff `v` is already in the span. -/
@[kb "hefferon2020" "Two.II.1.2, p. 119"]
theorem hefferon_Two_II_1_2 (S : Set V) (v : V) :
    span K (insert v S) = span K S ↔ v ∈ span K S :=
  ⟨fun h => h ▸ subset_span (mem_insert v S), fun h => span_insert_eq_span h⟩

/-- Removing an element of `S` keeps the span iff the element lies in the span of the others. -/
@[kb "hefferon2020" "Two.II.1.3, p. 119"]
theorem hefferon_Two_II_1_3 (S : Set V) (v : V) (hv : v ∈ S) :
    span K (S \ {v}) = span K S ↔ v ∈ span K (S \ {v}) := by
  have : S = insert v (S \ {v}) := by simp [hv]
  conv_rhs => rw [← hefferon_Two_II_1_2 (K := K)]
  rw [← this]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

end SpanLemmas

section Bases

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The standard bases: `e₁, ..., eₙ` of `Kⁿ`, and `1, z, ..., zᵐ` of the polynomials of degree at most
`m` (the space of polynomials of degree less than `m + 1`). -/
@[kb "axler2024" "2.27, p. 57"]
theorem axler_2_27 (K : Type*) [Field K] :
    (∀ n : ℕ, ∃ b : Basis (Fin n) K (Fin n → K), ∀ i, b i = Pi.single i 1) ∧
    (∀ m : ℕ, ∃ b : Basis (Fin (m + 1)) K (Polynomial.degreeLT K (m + 1)),
      ∀ i, (b i : Polynomial K) = Polynomial.X ^ (i : ℕ)) :=
  ⟨fun n => ⟨Pi.basisFun K (Fin n), fun i => by simp⟩,
    fun m => ⟨Polynomial.degreeLT.basis K (m + 1), fun i => Polynomial.degreeLT.basis_val i⟩⟩

/-- Dimensions: `dim Kⁿ = n` and `dim P_m(K) = m + 1`. -/
@[kb "axler2024" "2.36, p. 62"]
theorem axler_2_36 (K : Type*) [Field K] (n m : ℕ) :
    finrank K (Fin n → K) = n ∧ finrank K (Polynomial.degreeLT K (m + 1)) = m + 1 := by
  refine ⟨by simp, ?_⟩
  rw [finrank_eq_card_basis (Polynomial.degreeLT.basis K (m + 1)), Fintype.card_fin]

/-- Exchange lemma: if `B` is a basis and `v = ∑ cⱼ bⱼ` with `cᵢ ≠ 0`, then replacing `bᵢ` by `v`
gives another basis. -/
@[kb "hefferon2020" "Two.III.2.3, p. 140"]
theorem hefferon_Two_III_2_3 {ι : Type*} [DecidableEq ι] (B : Basis ι K V) (i : ι) (v : V)
    (hv : B.repr v i ≠ 0) :
    ∃ B' : Basis ι K V, ∀ j, B' j = Function.update B i v j := by
  have hli : LinearIndependent K (Function.update B i v) := by
    refine B.linearIndependent.update i v ⟨1, Submonoid.one_mem _, B.repr v, ?_, ?_⟩
    · exact mem_nonZeroDivisors_of_ne_zero hv
    · simp
  have hspan : ⊤ ≤ span K (range (Function.update B i v)) := by
    set S := span K (range (Function.update B i v)) with hS
    set l := B.repr v with hl
    have hrest : Finsupp.linearCombination K B (l.erase i) ∈ S := by
      have h1 : Finsupp.linearCombination K B (l.erase i) ∈ span K (B '' {j | j ≠ i}) := by
        refine (Finsupp.mem_span_image_iff_linearCombination K).2 ⟨l.erase i, ?_, rfl⟩
        rw [Finsupp.mem_supported]
        intro j hj
        simp [Finsupp.support_erase] at hj
        exact hj.2
      refine span_mono ?_ h1
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨j, by simp [Function.update_of_ne hj]⟩
    have hvS : v ∈ S := subset_span ⟨i, by simp⟩
    have hv' : v = l i • B i + Finsupp.linearCombination K B (l.erase i) := by
      conv_lhs => rw [← B.linearCombination_repr v, ← hl, ← Finsupp.single_add_erase i l]
      rw [map_add, Finsupp.linearCombination_single]
    have hBi : B i ∈ S := by
      have : B i = (l i)⁻¹ • (v - Finsupp.linearCombination K B (l.erase i)) := by
        rw [hv']
        simp [smul_smul, inv_mul_cancel₀ hv]
      rw [this]
      exact S.smul_mem _ (S.sub_mem hvS hrest)
    have hall : ∀ j, B j ∈ S := fun j => by
      by_cases hj : j = i
      · subst hj; exact hBi
      · exact subset_span ⟨j, by simp [Function.update_of_ne hj]⟩
    rw [← B.span_eq]
    exact span_le.2 (by rintro _ ⟨j, rfl⟩; exact hall j)
  exact ⟨Basis.mk hli hspan, fun j => by simp [Basis.mk_apply]⟩

end Bases

section ThreeSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private lemma exists_indep_span [FiniteDimensional K V] (U : Submodule K V) :
    ∃ (r : ℕ) (f : Fin r → V), r = finrank K U ∧ LinearIndependent K f ∧ span K (range f) = U := by
  obtain ⟨f, -, hf, hli⟩ := exists_fun_fin_finrank_span_eq K (U : Set V)
  refine ⟨_, f, by rw [Submodule.span_eq], hli, by rw [hf, Submodule.span_eq]⟩

/-- The subspaces of a three-dimensional coordinate space are exactly: the zero subspace, the lines
through the origin, the planes through the origin, and the whole space (each of these is clearly a
subspace; here we show that every subspace is of one of the four forms). -/
@[kb "hefferon2020" "Two.III.2.11, p. 142"]
theorem hefferon_Two_III_2_11 (U : Submodule K (Fin 3 → K)) :
    U = ⊥ ∨ (∃ v ≠ 0, U = K ∙ v) ∨
      (∃ v w : Fin 3 → K, LinearIndependent K ![v, w] ∧ U = span K {v, w}) ∨ U = ⊤ := by
  obtain ⟨r, f, hr, hli, hspan⟩ := exists_indep_span U
  have hr3 : r ≤ 3 := by
    have := U.finrank_le
    simp at this
    omega
  interval_cases r
  · left
    rw [← hspan]; simp
  · right; left
    refine ⟨f 0, hli.ne_zero 0, ?_⟩
    rw [← hspan, Set.range_unique]
    simp
  · right; right; left
    have hf : f = ![f 0, f 1] := by ext i; fin_cases i <;> rfl
    rw [hf] at hli hspan
    refine ⟨f 0, f 1, hli, ?_⟩
    rw [← hspan]
    congr 1
    ext x
    simp [or_comm]
  · right; right; right
    exact Submodule.eq_top_of_finrank_eq (by simpa using hr.symm)

end ThreeSpace

section Translates

open Pointwise

variable {K V : Type*} [Ring K] [AddCommGroup V] [Module K V]

private lemma vadd_coe_eq (v : V) (U : Submodule K V) :
    v +ᵥ (U : Set V) = {x | x - v ∈ U} := by
  ext x
  simp only [Set.mem_vadd_set, SetLike.mem_coe, vadd_eq_add, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨x - v, h, by abel⟩

/-- The translate `v + U` of a subspace, as a pointwise set, is the set of `x` with `x - v ∈ U`, i.e. the
coset of `v` (the fibre of the quotient map over the class of `v`). -/
@[kb "axler2024" "3.95, p. 116"]
theorem axler_3_95 (v : V) (U : Submodule K V) :
    v +ᵥ (U : Set V) = {x | x - v ∈ U} ∧
      v +ᵥ (U : Set V) = Submodule.Quotient.mk ⁻¹' {(Submodule.Quotient.mk v : V ⧸ U)} := by
  refine ⟨vadd_coe_eq v U, ?_⟩
  rw [vadd_coe_eq]
  ext x
  simp [Submodule.Quotient.eq]

/-- Translates of a subspace: `v - w ∈ U` iff `v + U = w + U` iff the two translates meet; hence two
translates are equal or disjoint. -/
@[kb "axler2024" "3.101, p. 118"]
theorem axler_3_101 (v w : V) (U : Submodule K V) :
    (v - w ∈ U ↔ v +ᵥ (U : Set V) = w +ᵥ (U : Set V)) ∧
    (v +ᵥ (U : Set V) = w +ᵥ (U : Set V) ↔
      ((v +ᵥ (U : Set V)) ∩ (w +ᵥ (U : Set V))).Nonempty) ∧
    (v +ᵥ (U : Set V) = w +ᵥ (U : Set V) ∨ Disjoint (v +ᵥ (U : Set V)) (w +ᵥ (U : Set V))) := by
  have h1 : v - w ∈ U ↔ v +ᵥ (U : Set V) = w +ᵥ (U : Set V) := by
    rw [vadd_coe_eq, vadd_coe_eq]
    constructor
    · intro h
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hx
        have := U.add_mem hx h
        simpa using this
      · intro hx
        have := U.sub_mem hx h
        simpa using this
    · intro h
      have : v ∈ {x | x - w ∈ U} := by
        rw [← h]; simp
      simpa using this
  have h2 : v +ᵥ (U : Set V) = w +ᵥ (U : Set V) ↔
      ((v +ᵥ (U : Set V)) ∩ (w +ᵥ (U : Set V))).Nonempty := by
    constructor
    · intro h
      refine ⟨v, ?_, h ▸ ?_⟩ <;> rw [vadd_coe_eq] <;> simp
    · rintro ⟨x, hxv, hxw⟩
      rw [vadd_coe_eq] at hxv hxw
      apply h1.1
      have := U.sub_mem hxw hxv
      simpa using this
  refine ⟨h1, h2, ?_⟩
  by_cases h : ((v +ᵥ (U : Set V)) ∩ (w +ᵥ (U : Set V))).Nonempty
  · exact Or.inl (h2.2 h)
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 h))

end Translates

section Flats

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A `k`-flat in a vector space (Hefferon's linear surface): the set of all `p + t₁ v₁ + ... + tₖ vₖ`.
A hyperplane of `Kⁿ` is an `(n-1)`-flat. -/
def IsFlat (k : ℕ) (S : Set V) : Prop :=
  ∃ (p : V) (v : Fin k → V), S = {x | ∃ t : Fin k → K, x = p + ∑ i, t i • v i}

/-- The `k`-flats of a finite-dimensional space are exactly the nonempty affine subspaces of dimension at
most `k` (Hefferon's flat may be degenerate, so the dimension may be smaller than `k`). -/
@[kb "hefferon2020" "One.II.1.Flat, p. 50"]
theorem hefferon_One_II_1_flat [FiniteDimensional K V] (k : ℕ) (S : Set V) :
    IsFlat (K := K) k S ↔
      ∃ A : AffineSubspace K V, (A : Set V) = S ∧ (A : Set V).Nonempty ∧
        finrank K A.direction ≤ k := by
  constructor
  · rintro ⟨p, v, rfl⟩
    refine ⟨AffineSubspace.mk' p (span K (range v)), ?_, ⟨p, by simp⟩, ?_⟩
    · ext x
      simp only [AffineSubspace.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, Set.mem_ofPred_eq,
        Submodule.mem_span_range_iff_exists_fun]
      constructor
      · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩
      · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩
    · rw [AffineSubspace.direction_mk']
      have := finrank_range_le_card (R := K) v
      rw [Fintype.card_fin] at this
      exact this
  · rintro ⟨A, rfl, ⟨p, hp⟩, hk⟩
    obtain ⟨r, f, hr, -, hspan⟩ := exists_indep_span A.direction
    have hrk : r ≤ k := hr ▸ hk
    let w : Fin k → V := fun i => if h : i.val < r then f ⟨i.val, h⟩ else 0
    have hw : span K (range w) = A.direction := by
      rw [← hspan]
      apply le_antisymm
      · rw [span_le]
        rintro _ ⟨i, rfl⟩
        by_cases h : i.val < r
        · simp only [w, h, dite_true]; exact subset_span ⟨_, rfl⟩
        · simp only [w, h, dite_false]; exact zero_mem _
      · rw [span_le]
        rintro _ ⟨j, rfl⟩
        refine subset_span ⟨⟨j.val, by omega⟩, ?_⟩
        simp [w]
    refine ⟨p, w, ?_⟩
    ext x
    have hx : x ∈ (A : Set V) ↔ x -ᵥ p ∈ A.direction :=
      (AffineSubspace.vsub_right_mem_direction_iff_mem hp x).symm
    simp only [Set.mem_ofPred_eq]
    rw [hx, ← hw, Submodule.mem_span_range_iff_exists_fun]
    simp only [vsub_eq_sub]
    constructor
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩

end Flats

section Complexification

/-- The complexification of a real vector space `V` (Axler Exercise 1B.8): pairs `(u, v)`, standing for
`u + i v`. A `def`, not an `abbrev`, so that its complex scalar multiplication never applies to a plain `V × V`.
(Mathlib's general complexification is the base change `ℂ ⊗[ℝ] V`; this is the book's concrete model.) -/
def Complexification (V : Type*) := V × V

namespace Complexification

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

instance : AddCommGroup (Complexification V) := inferInstanceAs (AddCommGroup (V × V))

/-- The element `u + i v` of the complexification. -/
def mk (u v : V) : Complexification V := (u, v)

/-- Complex scalar multiplication: `(a + b i)(u + i v) = (a u - b v) + i (a v + b u)`. -/
instance : SMul ℂ (Complexification V) :=
  ⟨fun z x => ((z.re • x.1 - z.im • x.2 : V), (z.re • x.2 + z.im • x.1 : V))⟩

theorem smul_def (z : ℂ) (x : Complexification V) :
    z • x = ((z.re • x.1 - z.im • x.2 : V), (z.re • x.2 + z.im • x.1 : V)) := rfl

theorem fst_smul (z : ℂ) (x : Complexification V) : (z • x).1 = z.re • x.1 - z.im • x.2 := rfl
theorem snd_smul (z : ℂ) (x : Complexification V) : (z • x).2 = z.re • x.2 + z.im • x.1 := rfl
theorem fst_add (x y : Complexification V) : (x + y).1 = x.1 + y.1 := rfl
theorem snd_add (x y : Complexification V) : (x + y).2 = x.2 + y.2 := rfl
theorem fst_zero : (0 : Complexification V).1 = 0 := rfl
theorem snd_zero : (0 : Complexification V).2 = 0 := rfl

theorem ext_iff' {x y : Complexification V} : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/-- The complexification of a real vector space is a complex vector space. -/
instance : Module ℂ (Complexification V) where
  one_smul x := by
    rw [ext_iff']; simp [fst_smul, snd_smul]
  mul_smul z w x := by
    rw [ext_iff']; simp only [fst_smul, snd_smul, Complex.mul_re, Complex.mul_im]
    constructor <;> module
  smul_zero z := by
    rw [ext_iff']; simp [fst_smul, snd_smul, fst_zero, snd_zero]
  smul_add z x y := by
    rw [ext_iff']; simp only [fst_smul, snd_smul, fst_add, snd_add]
    constructor <;> module
  add_smul z w x := by
    rw [ext_iff']; simp only [fst_smul, snd_smul, fst_add, snd_add, Complex.add_re, Complex.add_im]
    constructor <;> module
  zero_smul x := by
    rw [ext_iff']; simp [fst_smul, snd_smul, fst_zero, snd_zero]

/-- In the complexification, `i · (u + i v) = -v + i u`, and a real scalar acts on both components; so the
complexification is a complex vector space extending the real one. -/
@[kb "axler2024" "Ex1B.8, p. 35"]
theorem smul_I_and_real (u v : V) (r : ℝ) :
    (Complex.I • mk u v = mk (-v) u) ∧ ((r : ℂ) • mk u v = mk (r • u) (r • v)) := by
  have h1 : ∀ a b : V, (mk a b).1 = a := fun _ _ => rfl
  have h2 : ∀ a b : V, (mk a b).2 = b := fun _ _ => rfl
  constructor <;> rw [ext_iff'] <;> simp only [fst_smul, snd_smul, h1, h2] <;> simp

end Complexification

end Complexification

end UndergradKB.LinearAlgebra
