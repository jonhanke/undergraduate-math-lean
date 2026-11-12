import Mathlib.Data.Fin.Tuple.Sort
import UndergradKB.RepresentationTheory.FrobeniusFormula
import UndergradKB.Common.Attr

/-! # Dominance of the exponents `λ + ρ - ρ σ⁻¹` (Etingof et al., proof of Theorem 4.47)

In the expansion `θ_λ = ∑_σ sign σ · c_{λ + ρ - ρ σ⁻¹}`, every term with `σ ≠ 1` has an exponent vector whose
decreasing rearrangement strictly dominates `λ` at some partial sum.  The proof uses the rearrangement inequality
for partial sums (`sum_le_pre_of_antitone`): the sum of `k` values of a nonincreasing vector is at most the sum of
its first `k` values.
-/

namespace UndergradKB.RepresentationTheory

open Finset

variable {N : ℕ}

/-- The partial sum `v_0 + ⋯ + v_{k-1}` of a vector indexed by `Fin N`. -/
def pre (k : ℕ) (v : Fin N → ℕ) : ℕ := ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < k), v i

lemma card_filter_lt {k : ℕ} (hk : k ≤ N) : (univ.filter fun i : Fin N => (i : ℕ) < k).card = k := by
  have : (univ.filter fun i : Fin N => (i : ℕ) < k).map Fin.valEmbedding = range k := by
    ext a
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro ha; exact ⟨⟨a, by omega⟩, ha, rfl⟩
  rw [← card_map, this, card_range]

/-- **Rearrangement inequality for partial sums.**  For `w` nonincreasing and `S` a set of `k ≤ N` indices,
`∑_{i ∈ S} w i ≤ w_0 + ⋯ + w_{k-1}`. -/
lemma sum_le_pre_of_antitone {w : Fin N → ℕ} (hw : Antitone w) {k : ℕ} (hk : k ≤ N)
    (S : Finset (Fin N)) (hS : S.card = k) : ∑ i ∈ S, w i ≤ pre k w := by
  classical
  set T := univ.filter fun i : Fin N => (i : ℕ) < k with hT
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [card_eq_zero] at hS
    simp [hS]
  set c : Fin N := ⟨k - 1, by omega⟩
  have hA : ∀ x ∈ S \ T, w x ≤ w c := fun x hx => by
    simp only [mem_sdiff, hT, mem_filter, mem_univ, true_and, not_lt] at hx
    exact hw (Fin.le_def.2 (by simp [c]; omega))
  have hB : ∀ y ∈ T \ S, w c ≤ w y := fun y hy => by
    simp only [mem_sdiff, hT, mem_filter, mem_univ, true_and] at hy
    exact hw (Fin.le_def.2 (by simp [c]; omega))
  have hcard : (S \ T).card = (T \ S).card := by
    have h1 := card_sdiff_add_card_inter S T
    have h2 := card_sdiff_add_card_inter T S
    rw [inter_comm] at h2
    have h3 : T.card = k := card_filter_lt hk
    omega
  have hST : S \ (S ∩ T) = S \ T := by ext; simp
  have hTS : T \ (S ∩ T) = T \ S := by ext; simp
  have e1 : ∑ i ∈ S, w i = ∑ i ∈ S \ T, w i + ∑ i ∈ S ∩ T, w i := by
    rw [← hST]; exact (sum_sdiff inter_subset_left).symm
  have e2 : pre k w = ∑ i ∈ T \ S, w i + ∑ i ∈ S ∩ T, w i := by
    rw [pre, ← hT, ← hTS]; exact (sum_sdiff inter_subset_right).symm
  have i1 : ∑ i ∈ S \ T, w i ≤ (S \ T).card * w c := by
    simpa using sum_le_card_nsmul (S \ T) w (w c) hA
  have i2 : (T \ S).card * w c ≤ ∑ i ∈ T \ S, w i := by
    simpa using card_nsmul_le_sum (T \ S) w (w c) hB
  rw [e1, e2]
  have := hcard ▸ i1
  omega

/-- Partial sums only increase under a nonincreasing rearrangement. -/
lemma pre_le_pre_comp {v : Fin N → ℕ} {π : Equiv.Perm (Fin N)} (hv : Antitone (v ∘ π)) {k : ℕ}
    (hk : k ≤ N) : pre k v ≤ pre k (v ∘ π) := by
  classical
  have : pre k v = ∑ i ∈ (univ.filter fun i : Fin N => (i : ℕ) < k).map π.symm.toEmbedding, (v ∘ π) i := by
    rw [sum_map, pre]
    simp
  rw [this]
  exact sum_le_pre_of_antitone hv hk _ (by rw [card_map, card_filter_lt hk])

lemma pre_succ (v : Fin N → ℕ) {k : ℕ} (hk : k < N) : pre (k + 1) v = pre k v + v ⟨k, hk⟩ := by
  classical
  unfold pre
  have : (univ.filter fun i : Fin N => (i : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (univ.filter fun i : Fin N => (i : ℕ) < k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp), add_comm]

lemma rhoExp_antitone : Antitone (rhoExp N) := by
  intro i j hij
  simp only [rhoExp, Fin.val_rev]
  have : (i : ℕ) ≤ j := hij
  omega

lemma rhoExp_injective : Function.Injective (rhoExp N) := by
  intro i j h
  simp only [rhoExp, Fin.val_rev] at h
  have := i.isLt
  have := j.isLt
  exact Fin.ext (by omega)

/-- If the partial sums of `ρ ∘ σ⁻¹` and `ρ` agree, then `σ = 1`. -/
lemma eq_one_of_pre_rho (σ : Equiv.Perm (Fin N))
    (h : ∀ k ≤ N, pre k (fun i => rhoExp N (σ.symm i)) = pre k (rhoExp N)) : σ = 1 := by
  have hpt : ∀ i : Fin N, σ.symm i = i := by
    intro i
    have h1 := h (i + 1) (by omega)
    have h2 := h i (by omega)
    rw [pre_succ _ i.isLt, pre_succ _ i.isLt, h2] at h1
    exact rhoExp_injective (by simpa using h1)
  ext i
  have := hpt (σ i)
  simp only [Equiv.symm_apply_apply] at this
  simp [← this]

/-- **Dominance.**  For `λ` nonincreasing and `σ ≠ 1` with all exponents of `λ + ρ - ρ σ⁻¹` defined, any
nonincreasing rearrangement of `λ + ρ - ρ σ⁻¹` has some partial sum strictly larger than that of `λ`. -/
theorem exists_pre_lt_termExp {lam : Fin N → ℕ} {σ : Equiv.Perm (Fin N)} (hσ : σ ≠ 1) (hP : TermOK lam σ)
    {π : Equiv.Perm (Fin N)} (hπ : Antitone (termExp lam σ ∘ π)) :
    ∃ k ≤ N, pre k lam < pre k (termExp lam σ ∘ π) := by
  have hρ : ∀ k ≤ N, pre k (fun i => rhoExp N (σ.symm i)) ≤ pre k (rhoExp N) := fun k hk => by
    have := pre_le_pre_comp (v := fun i => rhoExp N (σ.symm i)) (π := σ)
      (by simpa [Function.comp_def] using rhoExp_antitone) hk
    simpa [Function.comp_def] using this
  obtain ⟨k, hk, hlt⟩ : ∃ k ≤ N, pre k (fun i => rhoExp N (σ.symm i)) < pre k (rhoExp N) := by
    by_contra hcon
    push Not at hcon
    exact hσ (eq_one_of_pre_rho σ fun k hk => le_antisymm (hρ k hk) (hcon k hk))
  have hsum : pre k (termExp lam σ) + pre k (fun i => rhoExp N (σ.symm i)) = pre k lam + pre k (rhoExp N) := by
    unfold pre
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    have := hP i
    unfold termExp
    omega
  refine ⟨k, hk, ?_⟩
  have := pre_le_pre_comp hπ hk
  omega

/-- Partial sums of a vector extended by zero, as sums over `range k`. -/
lemma sum_range_eq_pre (f : ℕ → ℕ) {k : ℕ} (hk : k ≤ N) :
    ∑ i ∈ range k, f i = pre k (fun j : Fin N => f j) := by
  classical
  unfold pre
  rw [sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) N, ← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

/-- The decreasing rearrangement of a vector. -/
lemma antitone_comp_sortDesc (v : Fin N → ℕ) : Antitone (v ∘ Tuple.sortDesc v) := Tuple.antitone_sortDesc v

end UndergradKB.RepresentationTheory
