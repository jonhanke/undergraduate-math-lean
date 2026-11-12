import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import UndergradKB.RepresentationTheory.SymmetricGroup
import UndergradKB.Common.Attr

/-! # Combinatorics of Young symmetrizers (Etingof et al., §4.12-4.13)

The counting argument behind Lemmas 4.39-4.41.  Fix a Young diagram `λ` with a bijective filling
`T_λ : λ ≃ Fin n` and a diagram `μ` with `T_μ : μ ≃ Fin n`, and a permutation `g`.  Let `ρ a` be the row
of the box of `T_λ` holding `a` and `γ a` the column of the box of `T_μ` holding `g⁻¹ a`.  If no two
distinct numbers lie in the same row of `T_λ` and in the same column of `g T_μ` (no "collision"), then
the partial sums of the rows of `λ` are bounded by those of `μ`, and when the shapes coincide the column
labelling `γ` is obtained from the column labelling of `T` by permuting inside rows.

Results: `rowSum_mul_x_mul_colSum` (Lemma 4.40), `rowSumN_mul_x_mul_colSumN_of_lex_lt` (Lemma 4.41).
-/

namespace UndergradKB.RepresentationTheory

open Finset

/-! ### Counting lemmas -/

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma sum_min_colLen (mu : YoungDiagram) (k : ℕ) :
    ∑ j ∈ range (mu.rowLen 0), min k (mu.colLen j) = ∑ i ∈ range k, mu.rowLen i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ j, min (k + 1) (mu.colLen j) =
        min k (mu.colLen j) + (if k < mu.colLen j then 1 else 0) := by
      intro j
      split_ifs with h <;> omega
    simp only [h1, sum_add_distrib, ih, sum_range_succ]
    congr 1
    rw [← card_filter]
    have : (range (mu.rowLen 0)).filter (fun j => k < mu.colLen j) = range (mu.rowLen k) := by
      ext j
      simp only [mem_filter, mem_range]
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨lt_of_lt_of_le h (mu.rowLen_anti 0 k (Nat.zero_le k)), h⟩
    rw [this, card_range]

omit [DecidableEq α] in
lemma card_filter_lt_eq (la : YoungDiagram) (ρ : α → ℕ)
    (hρ : ∀ i, (univ.filter (fun a => ρ a = i)).card = la.rowLen i) (k : ℕ) :
    (univ.filter (fun a => ρ a < k)).card = ∑ i ∈ range k, la.rowLen i := by
  rw [card_eq_sum_card_fiberwise (f := ρ) (t := range k)
    (fun a ha => by simpa using (mem_filter.1 ha).2)]
  refine sum_congr rfl (fun i hi => ?_)
  rw [← hρ i]
  congr 1
  ext a
  simp only [mem_range] at hi
  simp only [mem_filter, mem_univ, true_and]
  omega

omit [DecidableEq α] in
lemma lt_rowLen_zero_of_card (mu : YoungDiagram) (γ : α → ℕ)
    (hγ : ∀ j, (univ.filter (fun a => γ a = j)).card = mu.colLen j) (a : α) :
    γ a < mu.rowLen 0 := by
  have h1 : 0 < (univ.filter (fun b => γ b = γ a)).card :=
    card_pos.2 ⟨a, by simp⟩
  rw [hγ] at h1
  rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
  exact h1

lemma card_fiber_le (mu : YoungDiagram) (ρ γ : α → ℕ)
    (hγ : ∀ j, (univ.filter (fun a => γ a = j)).card = mu.colLen j)
    (hnc : ∀ a b, a ≠ b → ρ a = ρ b → γ a ≠ γ b) (k j : ℕ) :
    (univ.filter (fun a => ρ a < k ∧ γ a = j)).card ≤ min k (mu.colLen j) := by
  refine le_min ?_ ?_
  · calc (univ.filter (fun a => ρ a < k ∧ γ a = j)).card ≤ (range k).card := by
          refine card_le_card_of_injOn ρ (fun a ha => ?_) (fun a ha b hb hab => ?_)
          · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha
            simpa using ha.1
          · by_contra hne
            simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
            exact hnc a b hne hab (by rw [ha.2, hb.2])
      _ = k := card_range k
  · rw [← hγ j]
    exact card_le_card (fun a ha => by simp only [mem_filter, mem_univ, true_and] at ha ⊢; exact ha.2)

omit [DecidableEq α] in
lemma card_lt_eq_sum_fibers (mu : YoungDiagram) (ρ γ : α → ℕ)
    (hγ : ∀ j, (univ.filter (fun a => γ a = j)).card = mu.colLen j) (k : ℕ) :
    (univ.filter (fun a => ρ a < k)).card =
      ∑ j ∈ range (mu.rowLen 0), (univ.filter (fun a => ρ a < k ∧ γ a = j)).card := by
  rw [card_eq_sum_card_fiberwise (f := γ) (t := range (mu.rowLen 0))
    (fun a _ => mem_range.2 (lt_rowLen_zero_of_card mu γ hγ a))]
  refine sum_congr rfl (fun j _ => ?_)
  rw [filter_filter]

/-- Dominance: without collisions the partial row sums of `λ` are bounded by those of `μ`. -/
lemma sum_rowLen_le_of_noCollision (la mu : YoungDiagram) (ρ γ : α → ℕ)
    (hρ : ∀ i, (univ.filter (fun a => ρ a = i)).card = la.rowLen i)
    (hγ : ∀ j, (univ.filter (fun a => γ a = j)).card = mu.colLen j)
    (hnc : ∀ a b, a ≠ b → ρ a = ρ b → γ a ≠ γ b) (k : ℕ) :
    ∑ i ∈ range k, la.rowLen i ≤ ∑ i ∈ range k, mu.rowLen i := by
  rw [← card_filter_lt_eq la ρ hρ k, card_lt_eq_sum_fibers mu ρ γ hγ k, ← sum_min_colLen mu k]
  exact sum_le_sum (fun j _ => card_fiber_le mu ρ γ hγ hnc k j)

/-- Equality case: if the shapes agree, then every box `(k, j)` of the diagram contains exactly one
number of row `k` of the first filling whose column label is `j`. -/
lemma card_row_col_of_noCollision (la mu : YoungDiagram) (ρ γ : α → ℕ)
    (hρ : ∀ i, (univ.filter (fun a => ρ a = i)).card = la.rowLen i)
    (hγ : ∀ j, (univ.filter (fun a => γ a = j)).card = mu.colLen j)
    (hnc : ∀ a b, a ≠ b → ρ a = ρ b → γ a ≠ γ b) (hrow : ∀ i, la.rowLen i = mu.rowLen i)
    (k j : ℕ) :
    (univ.filter (fun a => ρ a = k ∧ γ a = j)).card = if j < mu.rowLen k then 1 else 0 := by
  have hE : ∀ k, ∀ j ∈ range (mu.rowLen 0),
      (univ.filter (fun a => ρ a < k ∧ γ a = j)).card = min k (mu.colLen j) := by
    intro k
    have hsum : ∑ j ∈ range (mu.rowLen 0), (univ.filter (fun a => ρ a < k ∧ γ a = j)).card =
        ∑ j ∈ range (mu.rowLen 0), min k (mu.colLen j) := by
      rw [← card_lt_eq_sum_fibers mu ρ γ hγ k, card_filter_lt_eq la ρ hρ k, sum_min_colLen mu k]
      exact sum_congr rfl (fun i _ => hrow i)
    exact (sum_eq_sum_iff_of_le (fun j _ => card_fiber_le mu ρ γ hγ hnc k j)).1 hsum
  have hsplit : (univ.filter (fun a => ρ a < k + 1 ∧ γ a = j)).card =
      (univ.filter (fun a => ρ a < k ∧ γ a = j)).card +
        (univ.filter (fun a => ρ a = k ∧ γ a = j)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [disjoint_left]
      intro a h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      omega
  by_cases hj : j < mu.rowLen 0
  · have h1 := hE (k + 1) j (mem_range.2 hj)
    have h2 := hE k j (mem_range.2 hj)
    rw [hsplit, h2] at h1
    have h3 : (k < mu.colLen j) ↔ j < mu.rowLen k := by
      rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    by_cases hk : j < mu.rowLen k
    · simp only [hk, ↓reduceIte]
      have := h3.2 hk
      omega
    · simp only [hk, ↓reduceIte]
      have := mt h3.1 hk
      omega
  · have : ¬ j < mu.rowLen k := fun h => hj (lt_of_lt_of_le h (mu.rowLen_anti 0 k (Nat.zero_le k)))
    simp only [this, ↓reduceIte]
    rw [card_eq_zero, filter_eq_empty_iff]
    intro a _ ha
    exact hj (ha.2 ▸ lt_rowLen_zero_of_card mu γ hγ a)

end Counting

/-! ### Fibres of a filling -/

section Fibres

variable {mu : YoungDiagram} {n : ℕ}

lemma card_filter_row (T : mu ≃ Fin n) (e : Equiv.Perm (Fin n)) (i : ℕ) :
    (univ.filter (fun a : Fin n => (T.symm (e a) : ℕ × ℕ).1 = i)).card = mu.rowLen i := by
  rw [YoungDiagram.rowLen_eq_card]
  refine card_bij (fun a _ => (T.symm (e a) : ℕ × ℕ)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    rw [YoungDiagram.mem_row_iff]
    exact ⟨(T.symm (e a)).2, ha⟩
  · intro a _ b _ h
    exact e.injective (T.symm.injective (Subtype.ext h))
  · intro c hc
    rw [YoungDiagram.mem_row_iff] at hc
    refine ⟨e.symm (T ⟨c, hc.1⟩), ?_, ?_⟩
    · simp [hc.2]
    · simp

lemma card_filter_col (T : mu ≃ Fin n) (e : Equiv.Perm (Fin n)) (j : ℕ) :
    (univ.filter (fun a : Fin n => (T.symm (e a) : ℕ × ℕ).2 = j)).card = mu.colLen j := by
  rw [YoungDiagram.colLen_eq_card]
  refine card_bij (fun a _ => (T.symm (e a) : ℕ × ℕ)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    rw [YoungDiagram.mem_col_iff]
    exact ⟨(T.symm (e a)).2, ha⟩
  · intro a _ b _ h
    exact e.injective (T.symm.injective (Subtype.ext h))
  · intro c hc
    rw [YoungDiagram.mem_col_iff] at hc
    refine ⟨e.symm (T ⟨c, hc.1⟩), ?_, ?_⟩
    · simp [hc.2]
    · simp

end Fibres

/-! ### Lemma 4.39: the double coset `P Q` -/

lemma swap_mem_fiberSubgroup {α β : Type*} [DecidableEq α] (f : α → β) {x y : α} (h : f x = f y) :
    Equiv.swap x y ∈ fiberSubgroup f := by
  intro z
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, h]
  · rw [h2, h]
  · rfl

lemma signChar_swap {α : Type*} [DecidableEq α] [Fintype α] {x y : α} (h : x ≠ y) :
    signChar α (Equiv.swap x y) = -1 := by
  simp [signChar, Equiv.Perm.sign_swap h]

section Lemma439

variable {mu : YoungDiagram}

/-- **Lemma 4.39 (combinatorial core).** If no two numbers of the same row of `T` lie in the same column
of the filling `g T`, then `g ∈ P_T Q_T`.  (Stated for the pair `g⁻¹`: `γ a` is the column of `g⁻¹ a`.) -/
@[kb "etingof2011" "Lemma 4.40, p. 59"]
theorem exists_mem_rowSubgroup_mul_colSubgroup (T : YoungTableau mu) (g : Equiv.Perm (Fin mu.card))
    (hnc : ∀ a b, a ≠ b → T.rowOf a = T.rowOf b → T.colOf (g⁻¹ a) ≠ T.colOf (g⁻¹ b)) :
    ∃ p ∈ rowSubgroup T, ∃ q ∈ colSubgroup T, g = p * q := by
  have hρ : ∀ i, (univ.filter (fun a : Fin mu.card => T.rowOf a = i)).card = mu.rowLen i :=
    fun i => card_filter_row T 1 i
  have hγ : ∀ j, (univ.filter (fun a : Fin mu.card => T.colOf (g⁻¹ a) = j)).card = mu.colLen j :=
    fun j => card_filter_col T g⁻¹ j
  have key := card_row_col_of_noCollision mu mu (fun a : Fin mu.card => T.rowOf a)
    (fun a => T.colOf (g⁻¹ a)) hρ hγ hnc (fun _ => rfl)
  have hmem : ∀ a : Fin mu.card, (T.rowOf a, T.colOf (g⁻¹ a)) ∈ mu := by
    intro a
    rw [YoungDiagram.mem_iff_lt_rowLen]
    by_contra hlt
    have h1 := key (T.rowOf a) (T.colOf (g⁻¹ a))
    simp only [hlt, ↓reduceIte] at h1
    have h2 : 0 < (univ.filter (fun b : Fin mu.card =>
        T.rowOf b = T.rowOf a ∧ T.colOf (g⁻¹ b) = T.colOf (g⁻¹ a))).card :=
      card_pos.2 ⟨a, by simp⟩
    omega
  set s : Fin mu.card → Fin mu.card := fun a => T ⟨(T.rowOf a, T.colOf (g⁻¹ a)), hmem a⟩ with hs
  have hs_row : ∀ a, T.rowOf (s a) = T.rowOf a := by
    intro a
    simp [YoungTableau.rowOf, hs]
  have hs_col : ∀ a, T.colOf (s a) = T.colOf (g⁻¹ a) := by
    intro a
    simp [YoungTableau.colOf, hs]
  have hs_inj : Function.Injective s := by
    intro a b hab
    by_contra hne
    refine hnc a b hne ?_ ?_
    · rw [← hs_row a, ← hs_row b, hab]
    · rw [← hs_col a, ← hs_col b, hab]
  set p' : Equiv.Perm (Fin mu.card) := Equiv.ofBijective s (Finite.injective_iff_bijective.1 hs_inj)
    with hp'
  have hp'apply : ∀ a, p' a = s a := fun a => rfl
  have hp'P : p' ∈ rowSubgroup T := fun a => by rw [hp'apply, hs_row]
  have hq : p' * g ∈ colSubgroup T := fun a => by
    show T.colOf (p' (g a)) = T.colOf a
    rw [hp'apply, hs_col]
    simp
  exact ⟨p'⁻¹, inv_mem hp'P, p' * g, hq, by simp⟩

/-- A collision (two numbers of the same row of `T` and the same column of `g T`) yields a transposition
`t` of `P_T` with `g⁻¹ t g ∈ Q_T`. -/
lemma exists_transposition_of_collision (T : YoungTableau mu) (g : Equiv.Perm (Fin mu.card))
    (h : ¬ ∀ a b, a ≠ b → T.rowOf a = T.rowOf b → T.colOf (g⁻¹ a) ≠ T.colOf (g⁻¹ b)) :
    ∃ t : Equiv.Perm (Fin mu.card), t ∈ rowSubgroup T ∧ g⁻¹ * t * g ∈ colSubgroup T ∧
      signChar _ (g⁻¹ * t * g)⁻¹ = -1 := by
  simp only [not_forall, not_not] at h
  obtain ⟨a, b, hab, hr, hc⟩ := h
  have hconj : g⁻¹ * Equiv.swap a b * g = Equiv.swap (g⁻¹ a) (g⁻¹ b) := by
    rw [Equiv.swap_apply_apply]
    simp
  refine ⟨Equiv.swap a b, swap_mem_fiberSubgroup _ hr, ?_, ?_⟩
  · rw [hconj]
    exact swap_mem_fiberSubgroup _ hc
  · rw [hconj, Equiv.swap_inv]
    exact signChar_swap (fun h => hab (g⁻¹.injective h))

/-- For each group element `g`, `a_T g b_T` is a scalar multiple of the Young symmetrizer. -/
lemma rowSum_mul_single_mul_colSum_exists (T : YoungTableau mu) (g : Equiv.Perm (Fin mu.card)) :
    ∃ s : ℂ, rowSum T * MonoidAlgebra.single g 1 * colSum T = s • youngSymmetrizer T := by
  by_cases hnc : ∀ a b, a ≠ b → T.rowOf a = T.rowOf b → T.colOf (g⁻¹ a) ≠ T.colOf (g⁻¹ b)
  · obtain ⟨p, hp, q, hq, rfl⟩ := exists_mem_rowSubgroup_mul_colSubgroup T g hnc
    exact ⟨_, rowSum_mul_single_mul_colSum_of_mul T hp hq⟩
  · obtain ⟨t, ht, hu, hneg⟩ := exists_transposition_of_collision T g hnc
    exact ⟨0, by rw [zero_smul]; exact rowSum_mul_single_mul_colSum_of_transposition T ht hu hneg⟩

/-- **Lemma 4.40.** For every `x ∈ ℂ[S_n]`, `a_T x b_T` is a scalar multiple of `c_T`, the scalar being a
linear functional of `x`. -/
@[kb "etingof2011" "Lemma 4.40, p. 59"]
theorem rowSum_mul_mul_colSum (T : YoungTableau mu) :
    ∃ ℓ : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₗ[ℂ] ℂ,
      ∀ x, rowSum T * x * colSum T = ℓ x • youngSymmetrizer T := by
  choose s hs using rowSum_mul_single_mul_colSum_exists T
  refine ⟨(Finsupp.linearCombination ℂ s).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap, ?_⟩
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, add_mul, hx, hy, map_add, add_smul]
  | single g r =>
    have h1 : (MonoidAlgebra.single g r : MonoidAlgebra ℂ _) = r • MonoidAlgebra.single g 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    have hl : ((Finsupp.linearCombination ℂ s).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap)
        (MonoidAlgebra.single g 1) = s g := by
      simp [MonoidAlgebra.coeff_single]
    rw [h1, mul_smul_comm, smul_mul_assoc, hs, smul_smul, map_smul, hl, smul_eq_mul]

end Lemma439

/-! ### Lemma 4.41: tableaux of two different shapes -/

section Lemma441

/-- Row sum `a` of a filling `T : λ ≃ Fin n` (for any `n`, not only `n = |λ|` with the canonical type). -/
noncomputable def rowSumN {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  twistedSum (fiberSubgroup fun a : Fin n => (T.symm a : ℕ × ℕ).1) 1

/-- Column sum `b` of a filling `T : μ ≃ Fin n`. -/
noncomputable def colSumN {mu : YoungDiagram} {n : ℕ} (T : mu ≃ Fin n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n)) :=
  twistedSum (fiberSubgroup fun a : Fin n => (T.symm a : ℕ × ℕ).2) (signChar _)

lemma rowSumN_eq_rowSum {mu : YoungDiagram} (T : YoungTableau mu) : rowSumN T = rowSum T := rfl

lemma colSumN_eq_colSum {mu : YoungDiagram} (T : YoungTableau mu) : colSumN T = colSum T := rfl

open scoped Classical in
lemma twistedSum_mul_single_mul_twistedSum_eq_zero {G : Type*} [Group G] [Fintype G]
    (H₁ H₂ : Subgroup G) (χ : G →* ℂ) {t g : G} (ht : t ∈ H₁) (hu : g⁻¹ * t * g ∈ H₂)
    (hneg : χ (g⁻¹ * t * g)⁻¹ = -1) :
    twistedSum H₁ 1 * MonoidAlgebra.single g 1 * twistedSum H₂ χ = 0 := by
  set X : MonoidAlgebra ℂ G := twistedSum H₁ 1 * MonoidAlgebra.single g 1 * twistedSum H₂ χ
  have h1 : X = -X := by
    have e1 : twistedSum H₁ 1 = twistedSum H₁ 1 * MonoidAlgebra.single t 1 := by
      rw [twistedSum_mul_single _ _ ht]; simp
    have e2 : MonoidAlgebra.single t 1 * MonoidAlgebra.single g 1 =
        (MonoidAlgebra.single g 1 : MonoidAlgebra ℂ _) * MonoidAlgebra.single (g⁻¹ * t * g) 1 := by
      simp only [MonoidAlgebra.single_mul_single, mul_one]
      congr 1
      simp [mul_assoc]
    have e3 := single_mul_twistedSum H₂ χ hu
    calc X = (twistedSum H₁ 1 * MonoidAlgebra.single t 1) * MonoidAlgebra.single g 1 *
          twistedSum H₂ χ := by rw [← e1]
      _ = twistedSum H₁ 1 * (MonoidAlgebra.single g 1 * MonoidAlgebra.single (g⁻¹ * t * g) 1) *
          twistedSum H₂ χ := by rw [mul_assoc (twistedSum H₁ 1), e2]
      _ = twistedSum H₁ 1 * MonoidAlgebra.single g 1 *
          (MonoidAlgebra.single (g⁻¹ * t * g) 1 * twistedSum H₂ χ) := by simp only [mul_assoc]
      _ = -X := by
          rw [e3, hneg]
          simp [X]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel X
  rcases smul_eq_zero.1 h2 with h | h
  · norm_num at h
  · exact h

/-- Dominance form of the "no collision" hypothesis: lexicographically larger shapes always collide. -/
lemma exists_collision_of_lex {la mu : YoungDiagram} {n : ℕ} (Tl : la ≃ Fin n) (Tm : mu ≃ Fin n)
    (g : Equiv.Perm (Fin n))
    (hlex : ∃ k, (∀ i < k, la.rowLen i = mu.rowLen i) ∧ mu.rowLen k < la.rowLen k) :
    ∃ a b : Fin n, a ≠ b ∧ (Tl.symm a : ℕ × ℕ).1 = (Tl.symm b : ℕ × ℕ).1 ∧
      (Tm.symm (g⁻¹ a) : ℕ × ℕ).2 = (Tm.symm (g⁻¹ b) : ℕ × ℕ).2 := by
  by_contra hcon
  have hnc : ∀ a b : Fin n, a ≠ b → (Tl.symm a : ℕ × ℕ).1 = (Tl.symm b : ℕ × ℕ).1 →
      (Tm.symm (g⁻¹ a) : ℕ × ℕ).2 ≠ (Tm.symm (g⁻¹ b) : ℕ × ℕ).2 :=
    fun a b hab hr hc => hcon ⟨a, b, hab, hr, hc⟩
  obtain ⟨k, hk1, hk2⟩ := hlex
  have := sum_rowLen_le_of_noCollision la mu (fun a : Fin n => (Tl.symm a : ℕ × ℕ).1)
    (fun a : Fin n => (Tm.symm (g⁻¹ a) : ℕ × ℕ).2) (fun i => card_filter_row Tl 1 i)
    (fun j => card_filter_col Tm g⁻¹ j) hnc (k + 1)
  have e : ∑ i ∈ range k, la.rowLen i = ∑ i ∈ range k, mu.rowLen i :=
    sum_congr rfl (fun i hi => hk1 i (mem_range.1 hi))
  rw [sum_range_succ, sum_range_succ, e] at this
  omega

/-- **Lemma 4.41.** If `λ` is lexicographically larger than `μ`, then `a_λ x b_μ = 0` for every
`x ∈ ℂ[S_n]` (for fillings `T_λ`, `T_μ` of the two diagrams by `0, …, n-1`). -/
@[kb "etingof2011" "Lemma 4.41, p. 59"]
theorem rowSumN_mul_mul_colSumN_of_lex {la mu : YoungDiagram} {n : ℕ} (Tl : la ≃ Fin n)
    (Tm : mu ≃ Fin n)
    (hlex : ∃ k, (∀ i < k, la.rowLen i = mu.rowLen i) ∧ mu.rowLen k < la.rowLen k)
    (x : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) : rowSumN Tl * x * colSumN Tm = 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, add_mul, hx, hy, add_zero]
  | single g r =>
    have h1 : (MonoidAlgebra.single g r : MonoidAlgebra ℂ _) = r • MonoidAlgebra.single g 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    obtain ⟨a, b, hab, hr, hc⟩ := exists_collision_of_lex Tl Tm g hlex
    have hconj : g⁻¹ * Equiv.swap a b * g = Equiv.swap (g⁻¹ a) (g⁻¹ b) := by
      rw [Equiv.swap_apply_apply]
      simp
    have hz : rowSumN Tl * MonoidAlgebra.single g 1 * colSumN Tm = 0 := by
      refine twistedSum_mul_single_mul_twistedSum_eq_zero _ _ (signChar _)
        (swap_mem_fiberSubgroup _ hr) ?_ ?_
      · rw [hconj]
        exact swap_mem_fiberSubgroup _ hc
      · rw [hconj, Equiv.swap_inv]
        exact signChar_swap (fun h => hab (g⁻¹.injective h))
    rw [h1, mul_smul_comm, smul_mul_assoc, hz, smul_zero]

end Lemma441

/-! ### Lemma 4.42: `c_λ² = (n! / dim V_λ) c_λ` -/

section Lemma442

variable {mu : YoungDiagram}

open scoped Classical in
/-- The coefficient of the identity in `c_T = a_T b_T` is `1`. -/
lemma coeff_one_youngSymmetrizer (T : YoungTableau mu) : (youngSymmetrizer T).coeff 1 = 1 := by
  set L : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₗ[ℂ] ℂ :=
    (Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap with hLdef
  have hL : ∀ x, L x = x.coeff 1 := fun x => rfl
  have hLs : ∀ (g : Equiv.Perm (Fin mu.card)) (r : ℂ),
      L (MonoidAlgebra.single g r) = if g = 1 then r else 0 := by
    intro g r
    rw [hL, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [← hL]
  unfold youngSymmetrizer rowSum colSum twistedSum
  rw [Finset.sum_mul_sum, map_sum]
  rw [Finset.sum_eq_single (⟨1, one_mem _⟩ : rowSubgroup T)]
  · rw [map_sum]
    rw [Finset.sum_eq_single (⟨1, one_mem _⟩ : colSubgroup T)]
    · simp [hLs, MonoidAlgebra.single_mul_single]
    · intro q _ hq
      have : (q : Equiv.Perm (Fin mu.card)) ≠ 1 := fun h => hq (Subtype.ext h)
      simp [MonoidAlgebra.single_mul_single, hLs, this]
    · simp
  · intro p _ hp
    have hp1 : (p : Equiv.Perm (Fin mu.card)) ≠ 1 := fun h => hp (Subtype.ext h)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun q _ => ?_)
    simp only [smul_mul_smul_comm, MonoidAlgebra.single_mul_single, map_smul, hLs]
    have : (p : Equiv.Perm (Fin mu.card)) * q ≠ 1 := by
      intro h
      have hpq : (p : Equiv.Perm (Fin mu.card)) = (q : Equiv.Perm (Fin mu.card))⁻¹ :=
        eq_inv_of_mul_eq_one_left h
      have hpQ : (p : Equiv.Perm (Fin mu.card)) ∈ colSubgroup T := by
        rw [hpq]; exact inv_mem q.2
      have hmem : (p : Equiv.Perm (Fin mu.card)) ∈ rowSubgroup T ⊓ colSubgroup T := ⟨p.2, hpQ⟩
      rw [rowSubgroup_inf_colSubgroup] at hmem
      exact hp1 (Subgroup.mem_bot.1 hmem)
    simp [this]
  · simp

instance : Module.Finite ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))) :=
  Module.Finite.equiv (MonoidAlgebra.coeffLinearEquiv ℂ).symm

/-- The trace of right multiplication by `c_T` on the group algebra is `n!`. -/
lemma trace_mulRight_youngSymmetrizer (T : YoungTableau mu) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)))
        (LinearMap.mulRight ℂ (youngSymmetrizer T)) = (mu.card.factorial : ℂ) := by
  classical
  let b : Module.Basis (Equiv.Perm (Fin mu.card)) ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))) :=
    Module.Basis.ofRepr (MonoidAlgebra.coeffLinearEquiv ℂ)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  have : ∀ g : Equiv.Perm (Fin mu.card),
      LinearMap.toMatrix b b (LinearMap.mulRight ℂ (youngSymmetrizer T)) g g = 1 := by
    intro g
    simp only [LinearMap.toMatrix_apply]
    have hb : b g = MonoidAlgebra.single g 1 := rfl
    rw [hb, LinearMap.mulRight_apply]
    show (MonoidAlgebra.single g 1 * youngSymmetrizer T).coeff g = 1
    rw [MonoidAlgebra.coeff_single_mul_apply, inv_mul_cancel, coeff_one_youngSymmetrizer, mul_one]
  simp [this, Fintype.card_perm]

/-- `c_T * c_T` is a scalar multiple of `c_T`. -/
lemma youngSymmetrizer_mul_self_exists (T : YoungTableau mu) :
    ∃ k : ℂ, youngSymmetrizer T * youngSymmetrizer T = k • youngSymmetrizer T := by
  obtain ⟨ℓ, hℓ⟩ := rowSum_mul_mul_colSum T
  refine ⟨ℓ (colSum T * rowSum T), ?_⟩
  have : youngSymmetrizer T * youngSymmetrizer T =
      rowSum T * (colSum T * rowSum T) * colSum T := by
    simp only [youngSymmetrizer, mul_assoc]
  rw [this, hℓ]

/-- **Lemma 4.42.** The square of the Young symmetrizer is `(n! / dim V) c`, where `V = ℂ[S_n] c`
is the left ideal generated by `c` (and `dim V ≠ 0`). -/
@[kb "etingof2011" "Lemma 4.42, p. 60"]
theorem youngSymmetrizer_mul_self (T : YoungTableau mu) :
    Module.finrank ℂ ((Ideal.span {youngSymmetrizer T}).restrictScalars ℂ) ≠ 0 ∧
      youngSymmetrizer T * youngSymmetrizer T =
        ((mu.card.factorial : ℂ) /
          (Module.finrank ℂ ((Ideal.span {youngSymmetrizer T}).restrictScalars ℂ) : ℂ)) •
          youngSymmetrizer T := by
  obtain ⟨k, hk⟩ := youngSymmetrizer_mul_self_exists T
  set c := youngSymmetrizer T with hc
  set F : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) :=
    LinearMap.mulRight ℂ c with hF
  have hFF : F * F = k • F := by
    refine LinearMap.ext fun x => ?_
    show (x * c) * c = k • (x * c)
    rw [mul_assoc, hk, mul_smul_comm]
  have htr : LinearMap.trace ℂ _ F = (mu.card.factorial : ℂ) := trace_mulRight_youngSymmetrizer T
  have hfact : (mu.card.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hFF
    have hnil : IsNilpotent F := ⟨2, by rw [pow_two]; exact hFF⟩
    have := (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    exact hfact (htr ▸ this)
  set e : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) :=
    k⁻¹ • F with he
  have hidem : IsIdempotentElem e := by
    show e * e = e
    rw [he, smul_mul_smul_comm, hFF, smul_smul]
    congr 1
    field_simp
  have hrange : LinearMap.range e = (Ideal.span {c}).restrictScalars ℂ := by
    ext z
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨k⁻¹ • y, by simp [he, hF]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨k • a, by simp [he, hF, smul_smul, hk0]⟩
  have htr2 : LinearMap.trace ℂ _ e = (Module.finrank ℂ (LinearMap.range e) : ℂ) :=
    ((LinearMap.isProj_range_iff_isIdempotentElem e).2 hidem).trace
  rw [he, map_smul, htr, hrange, smul_eq_mul] at htr2
  have hne : (Module.finrank ℂ ((Ideal.span {c}).restrictScalars ℂ) : ℂ) ≠ 0 := by
    rw [← htr2]; exact mul_ne_zero (inv_ne_zero hk0) hfact
  refine ⟨fun h => hne (by rw [h]; simp), ?_⟩
  rw [hk]
  congr 1
  rw [eq_div_iff hne, ← htr2]
  field_simp

end Lemma442

end UndergradKB.RepresentationTheory
