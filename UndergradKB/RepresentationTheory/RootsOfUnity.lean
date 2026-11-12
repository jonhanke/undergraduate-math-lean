import UndergradKB.Common.Attr
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Averages of roots of unity (Etingof et al., Lemma 4.22)

If `ε₁, …, εₙ` are complex roots of unity whose average is an algebraic integer, then either all the `εᵢ` are
equal or their sum vanishes. The proof takes the field norm of the average down to `ℚ`: it is an integer, and
it is the product of the Galois conjugates of the average, each of absolute value at most `1`, and the
identity conjugate has absolute value `< 1` unless all the `εᵢ` coincide.
-/

namespace UndergradKB.RepresentationTheory

open Finset

/-- Two distinct unit complex numbers have sum of norm `< 2`. -/
lemma norm_add_lt_two_of_ne {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) : ‖x + y‖ < 2 := by
  have h := norm_add_le x y
  rcases h.lt_or_eq with h | h
  · linarith
  · exfalso
    have : SameRay ℝ x y := sameRay_iff_norm_add.mpr h
    exact hxy (this.eq_of_norm_eq (by rw [hx, hy]))

/-- If not all unit complex numbers `ε i` are equal, their sum has norm `< card`. -/
lemma norm_sum_lt_card {ι : Type*} [Fintype ι] (ε : ι → ℂ) (h1 : ∀ i, ‖ε i‖ = 1)
    (hne : ¬ ∀ i j, ε i = ε j) : ‖∑ i, ε i‖ < Fintype.card ι := by
  classical
  push Not at hne
  obtain ⟨i, j, hij⟩ := hne
  have hji : j ∈ univ.erase i := mem_erase.mpr ⟨fun h => hij (by rw [h]), mem_univ _⟩
  have hsum : ∑ k, ε k = (ε i + ε j) + ∑ k ∈ (univ.erase i).erase j, ε k := by
    rw [← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ hji, add_assoc]
  have hcard : ((univ.erase i).erase j).card + 2 = Fintype.card ι := by
    rw [card_erase_of_mem hji, card_erase_of_mem (mem_univ i), card_univ]
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    have h2 : 1 < Fintype.card ι := by
      by_contra hc
      have : Fintype.card ι ≤ 1 := by omega
      exact hij (by rw [Fintype.card_le_one_iff.mp this i j])
    omega
  have hrest : ‖∑ k ∈ (univ.erase i).erase j, ε k‖ ≤ ((univ.erase i).erase j).card := by
    calc ‖∑ k ∈ (univ.erase i).erase j, ε k‖ ≤ ∑ k ∈ (univ.erase i).erase j, ‖ε k‖ := norm_sum_le _ _
      _ = ((univ.erase i).erase j).card := by simp [h1]
  have := norm_add_lt_two_of_ne (h1 i) (h1 j) hij
  rw [hsum]
  calc ‖(ε i + ε j) + ∑ k ∈ (univ.erase i).erase j, ε k‖
      ≤ ‖ε i + ε j‖ + ‖∑ k ∈ (univ.erase i).erase j, ε k‖ := norm_add_le _ _
    _ < Fintype.card ι := by
      have : (((univ.erase i).erase j).card : ℝ) + 2 = Fintype.card ι := by exact_mod_cast hcard
      linarith

/-- **Etingof et al., Lemma 4.22**: if `ε₁, …, εₙ` are complex roots of unity whose average is an algebraic
integer, then either all the `εᵢ` are equal or their sum is zero. -/
@[kb "etingof2011" "Lemma 4.22, p. 53"]
theorem eq_or_sum_eq_zero_of_isIntegral_average {ι : Type*} [Fintype ι] [Nonempty ι] (ε : ι → ℂ) (m : ℕ)
    (hm : 0 < m) (hε : ∀ i, ε i ^ m = 1) (hint : IsIntegral ℤ ((∑ i, ε i) / Fintype.card ι)) :
    (∀ i j, ε i = ε j) ∨ ∑ i, ε i = 0 := by
  classical
  by_cases hall : ∀ i j, ε i = ε j
  · exact Or.inl hall
  right
  set n : ℕ := Fintype.card ι with hn
  have hn0 : (n : ℂ) ≠ 0 := by
    have : 0 < n := Fintype.card_pos
    exact_mod_cast this.ne'
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range ε)
  have : FiniteDimensional ℚ L := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨i, rfl⟩
    exact IsIntegral.of_pow hm (by rw [hε]; exact isIntegral_one)
  have hnorm1 : ∀ i, ‖ε i‖ = 1 := fun i => Complex.norm_eq_one_of_pow_eq_one (hε i) hm.ne'
  let ε' : ι → L := fun i => ⟨ε i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  have hε' : ∀ i, ε' i ^ m = 1 := fun i => Subtype.ext (by simp [ε', hε])
  let a' : L := (∑ i, ε' i) / (n : L)
  have hval : (a' : ℂ) = (∑ i, ε i) / n := by simp [a', ε']
  have hint' : IsIntegral ℤ a' := by
    let f : L →ₐ[ℤ] ℂ := (L.val : L →ₐ[ℚ] ℂ).restrictScalars ℤ
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have : f a' = (∑ i, ε i) / n := hval
    rw [this]
    exact hint
  have hσ : ∀ σ : L →ₐ[ℚ] ℂ, ‖σ a'‖ ≤ 1 := by
    intro σ
    have h1 : ∀ i, ‖σ (ε' i)‖ = 1 := fun i =>
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hε', map_one]) hm.ne'
    have : σ a' = (∑ i, σ (ε' i)) / n := by simp [a']
    rw [this, norm_div, Complex.norm_natCast]
    have hpos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos (α := ι)
    rw [div_le_one hpos]
    calc ‖∑ i, σ (ε' i)‖ ≤ ∑ i, ‖σ (ε' i)‖ := norm_sum_le _ _
      _ = n := by simp [h1, hn]
  have hlt : ‖(L.val : L →ₐ[ℚ] ℂ) a'‖ < 1 := by
    have : (L.val : L →ₐ[ℚ] ℂ) a' = (∑ i, ε i) / n := hval
    rw [this, norm_div, Complex.norm_natCast]
    have hpos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos (α := ι)
    rw [div_lt_one hpos]
    exact norm_sum_lt_card ε hnorm1 hall
  have hN := Algebra.norm_eq_prod_embeddings ℚ ℂ a'
  have hNlt : ‖algebraMap ℚ ℂ (Algebra.norm ℚ a')‖ < 1 := by
    rw [hN, ← mul_prod_erase univ _ (mem_univ (L.val : L →ₐ[ℚ] ℂ)), norm_mul]
    have hp : ‖∏ σ ∈ univ.erase (L.val : L →ₐ[ℚ] ℂ), σ a'‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun σ _ => hσ σ)
    calc ‖(L.val : L →ₐ[ℚ] ℂ) a'‖ * ‖∏ σ ∈ univ.erase (L.val : L →ₐ[ℚ] ℂ), σ a'‖
        ≤ ‖(L.val : L →ₐ[ℚ] ℂ) a'‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  have hNint : IsIntegral ℤ (Algebra.norm ℚ a') := Algebra.isIntegral_norm ℚ hint'
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hNint
  have hy0 : y = 0 := by
    rw [← hy] at hNlt
    have h : ((|y| : ℤ) : ℝ) < 1 := by simpa using hNlt
    have : |y| < 1 := by exact_mod_cast h
    exact abs_nonpos_iff.mp (by omega)
  have hN0 : Algebra.norm ℚ a' = 0 := by rw [← hy, hy0]; simp
  have ha0 : a' = 0 := Algebra.norm_eq_zero_iff.mp hN0
  have : (a' : ℂ) = 0 := by rw [ha0]; rfl
  rw [hval, div_eq_zero_iff] at this
  exact this.resolve_right hn0

end UndergradKB.RepresentationTheory
