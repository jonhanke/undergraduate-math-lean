import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Sym.Card
import UndergradKB.Common.Attr

/-!
# Counting graphs, avoiding functions, surjections, derangements (Keller–Trotter)

CO-017, CO-181, CO-182, CO-184, CO-186, CO-190.
-/

namespace UndergradKB.Combinatorics

open Finset

/-! ### CO-017: graphs on `[n]` -/

section Graphs

/-- A simple graph on `V` is the same as a set of non-diagonal unordered pairs (its edges). -/
noncomputable def graphEquivEdgeSubsets (V : Type*) :
    SimpleGraph V ≃ Set {e : Sym2 V // ¬ e.IsDiag} where
  toFun G := {e | e.1 ∈ G.edgeSet}
  invFun T := SimpleGraph.fromEdgeSet (Subtype.val '' T)
  left_inv G := by
    have : (Subtype.val '' {e : {e : Sym2 V // ¬ e.IsDiag} | e.1 ∈ G.edgeSet}) = G.edgeSet := by
      ext e
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists, exists_and_right,
        exists_eq_right]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨G.not_isDiag_of_mem_edgeSet h, h⟩⟩
    simp only
    rw [this, SimpleGraph.fromEdgeSet_edgeSet]
  right_inv T := by
    ext e
    simp only [Set.mem_ofPred_eq, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
      Subtype.val_injective.mem_set_image, Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h, e.2⟩⟩

theorem image_val_graphEquiv {V : Type*} (G : SimpleGraph V) :
    Subtype.val '' (graphEquivEdgeSubsets V G) = G.edgeSet := by
  ext e
  simp only [graphEquivEdgeSubsets, Equiv.coe_fn_mk, Set.mem_image, Set.mem_ofPred_eq,
    Subtype.exists, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨G.not_isDiag_of_mem_edgeSet h, h⟩⟩

/-- CO-017. There are `2 ^ C(n,2)` simple graphs on the vertex set `[n]`. -/
@[kb "kellertrotter2017" "text, p. 330"]
theorem card_simpleGraph_fin (n : ℕ) : Nat.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  classical
  rw [Nat.card_congr (graphEquivEdgeSubsets (Fin n)), Nat.card_eq_fintype_card,
    Fintype.card_set, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- CO-017. For `0 ≤ k`, there are `C(C(n,2), k)` simple graphs on `[n]` with exactly `k` edges. -/
@[kb "kellertrotter2017" "text, p. 330"]
theorem card_simpleGraph_fin_edges (n k : ℕ) :
    Nat.card {G : SimpleGraph (Fin n) // G.edgeSet.ncard = k} = (n.choose 2).choose k := by
  classical
  let e1 : {G : SimpleGraph (Fin n) // G.edgeSet.ncard = k} ≃
      {T : Set {e : Sym2 (Fin n) // ¬ e.IsDiag} // T.ncard = k} :=
    (graphEquivEdgeSubsets (Fin n)).subtypeEquiv (fun G => by
      rw [← image_val_graphEquiv G, Set.ncard_image_of_injective _ Subtype.val_injective])
  rw [Nat.card_congr e1]
  refine (Nat.card_coe_set_eq {T : Set {e : Sym2 (Fin n) // ¬ e.IsDiag} | T.ncard = k}).trans ?_
  have := Set.ncard_powerset_ncard (s := (Set.univ : Set {e : Sym2 (Fin n) // ¬ e.IsDiag}))
    Set.finite_univ k
  simp only [Set.subset_univ, true_and, Set.ncard_univ] at this
  rw [this, Nat.card_eq_fintype_card, Sym2.card_subtype_not_diag, Fintype.card_fin]

end Graphs

/-! ### CO-181, CO-182: avoiding values, fixing points -/

/-- CO-181. The functions `[n] → [m]` which avoid every value of a `k`-set `S` number `(m-k)^n`. -/
@[kb "kellertrotter2017" "Lemma 7.8, p. 170"]
theorem card_functions_avoiding (n m : ℕ) (S : Finset (Fin m)) :
    Fintype.card {f : Fin n → Fin m // ∀ i, f i ∉ S} = (m - #S) ^ n := by
  classical
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ (b : Fin m) => b ∉ S)),
    Fintype.card_pi]
  simp [Fintype.card_subtype_compl]

/-- CO-182. The permutations of `[n]` fixing every point of a `k`-set `S` number `(n-k)!`. -/
@[kb "kellertrotter2017" "Lemma 7.10, p. 171"]
theorem card_perms_fixing (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i ∈ S, σ i = i} = (n - #S).factorial := by
  classical
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ∉ S)
  rw [← Fintype.card_congr (e.trans (Equiv.subtypeEquivRight (by simp))), Fintype.card_perm]
  simp [Fintype.card_subtype_compl]

/-! ### CO-184: surjections -/

/-- CO-184. The number of surjections `[n] → [m]` is `∑ₖ (-1)^k C(m,k) (m-k)^n`. -/
@[kb "kellertrotter2017" "Theorem 7.9, p. 170"]
theorem card_surjections (n m : ℕ) :
    (Fintype.card {f : Fin n → Fin m // Function.Surjective f} : ℤ) =
      ∑ k ∈ range (m + 1), (-1 : ℤ) ^ k * (m.choose k) * ((m : ℤ) - k) ^ n := by
  classical
  let S : Fin m → Finset (Fin n → Fin m) := fun j => univ.filter (fun f => ∀ i, f i ≠ j)
  have h1 : (Finset.univ : Finset (Fin m)).inf (fun j => (S j)ᶜ) =
      univ.filter (fun f : Fin n → Fin m => Function.Surjective f) := by
    ext f
    rw [Finset.mem_inf, mem_filter]
    refine ⟨fun h => ⟨mem_univ _, fun j => ?_⟩, fun h j _ => ?_⟩
    · have := mem_compl.1 (h j (mem_univ j))
      simpa [S] using this
    · obtain ⟨i, hi⟩ := h.2 j
      simp only [mem_compl, S, mem_filter, mem_univ, true_and, not_forall, not_not]
      exact ⟨i, hi⟩
  have h2 : ∀ t : Finset (Fin m), #(t.inf S) = (m - #t) ^ n := by
    intro t
    have : t.inf S = univ.filter (fun f : Fin n → Fin m => ∀ i, f i ∉ t) := by
      ext f
      simp only [Finset.mem_inf, S, mem_filter, mem_univ, true_and]
      constructor
      · intro h i hi
        exact (h _ hi) i rfl
      · intro h j hj i hij
        exact h i (hij ▸ hj)
    rw [this, ← Fintype.card_subtype, card_functions_avoiding]
  rw [Fintype.card_subtype, ← h1, inclusion_exclusion_card_inf_compl]
  simp_rw [h2]
  rw [Finset.sum_powerset_apply_card (fun k => (-1 : ℤ) ^ k * (((m - k) ^ n : ℕ) : ℤ)),
    Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
  rw [nsmul_eq_mul]
  push_cast [Nat.cast_sub hk']
  ring

/-! ### CO-186: derangements -/

/-- CO-186. The number of derangements of `[n]` is `∑ₖ (-1)^k C(n,k) (n-k)!`. -/
@[kb "kellertrotter2017" "Theorem 7.11, p. 171"]
theorem card_derangements_sum (n : ℕ) :
    (Fintype.card (derangements (Fin n)) : ℤ) =
      ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (n.choose k) * (n - k).factorial := by
  rw [card_derangements_fin_eq_numDerangements, numDerangements_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  have h1 := Nat.factorial_mul_ascFactorial k (n - k)
  have h2 := Nat.choose_mul_factorial_mul_factorial hk'
  rw [Nat.add_sub_cancel' hk'] at h1
  have h3 : (k + 1).ascFactorial (n - k) = n.choose k * (n - k).factorial := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
    rw [h1, ← h2]; ring
  rw [h3]
  push_cast
  ring

/-! ### CO-190: multiples of a product of primes -/

/-- CO-190, general form: the divisibility hypothesis `p ∣ n` is not needed for the count
`⌊n / (p₁⋯p_k)⌋`. -/
theorem card_multiples_of_primes_general (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    #{x ∈ Icc 1 n | ∀ p ∈ P, p ∣ x} = n / ∏ p ∈ P, p := by
  classical
  have key : ∀ x, (∀ p ∈ P, p ∣ x) ↔ (∏ p ∈ P, p) ∣ x := fun x =>
    ⟨fun h => Finset.prod_primes_dvd x (fun p hp => (hP p hp).prime) h,
      fun h p hp => (Finset.dvd_prod_of_mem _ hp).trans h⟩
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1
  ext x
  simp only [mem_filter, mem_Icc, mem_Ioc, key]
  omega

/-- CO-190. If distinct primes `p₁, …, p_k` all divide `n`, then exactly `n / (p₁⋯p_k)` of the
integers in `1..n` are divisible by all of them. -/
@[kb "kellertrotter2017" "Proposition 7.15, p. 174"]
theorem card_multiples_of_primes (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (_hdvd : ∀ p ∈ P, p ∣ n) :
    #{x ∈ Icc 1 n | ∀ p ∈ P, p ∣ x} = n / ∏ p ∈ P, p :=
  card_multiples_of_primes_general n P hP

/-! ### CO-040, CO-041, CO-042: binomial coefficients with half-integer top -/

section HalfBinomial

/-- The recursion `C(a, k+1) = C(a, k) (a - k) / (k + 1)` for the generalized binomial
coefficient over `ℚ`. -/
theorem ring_choose_succ_rat (a : ℚ) (k : ℕ) :
    Ring.choose a (k + 1) = Ring.choose a k * (a - k) / (k + 1) := by
  have e1 := Ring.choose_eq_smul (a := a) (n := k + 1)
  have e0 := Ring.choose_eq_smul (a := a) (n := k)
  have key : (descPochhammer ℤ (k + 1)).smeval a = (descPochhammer ℤ k).smeval a * (a - k) := by
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast, npow_one, npow_zero, nsmul_one]
  refine e1.trans ?_
  refine Eq.trans ?_ (congrArg (fun x => x * (a - k) / (k + 1)) e0.symm)
  rw [key, Nat.factorial_succ]
  simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv]
  have : ((k.factorial : ℚ)) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- CO-040. `C(-1/2, k) = (-1)^k C(2k,k) / 2^(2k)`. -/
@[kb "kellertrotter2017" "Lemma 8.12, p. 191"]
theorem choose_neg_half (k : ℕ) :
    Ring.choose (-1 / 2 : ℚ) k = (-1) ^ k * ((2 * k).choose k : ℚ) / 2 ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ring_choose_succ_rat, ih]
    have h : ((k : ℚ) + 1) * ((2 * (k + 1)).choose (k + 1) : ℚ) =
        2 * (2 * k + 1) * ((2 * k).choose k : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h3 : ((2 * (k + 1)).choose (k + 1) : ℚ) =
        2 * (2 * k + 1) * ((2 * k).choose k : ℚ) / (k + 1) := by
      field_simp; linarith
    rw [h3]
    field_simp
    ring

/-- CO-042. For `k ≥ 1`, `C(1/2, k) = (-1)^(k-1) C(2k-2, k-1) / (k 2^(2k-1))`. -/
@[kb "kellertrotter2017" "Lemma 9.27, p. 231"]
theorem choose_half (k : ℕ) (hk : 1 ≤ k) :
    Ring.choose (1 / 2 : ℚ) k =
      (-1) ^ (k - 1) * ((2 * k - 2).choose (k - 1) : ℚ) / (k * 2 ^ (2 * k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, show 2 * (j + 1) - 2 = 2 * j by omega,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
  clear hk
  induction j with
  | zero =>
    simp
  | succ j ih =>
    rw [ring_choose_succ_rat, ih]
    have h : ((j : ℚ) + 1) * ((2 * (j + 1)).choose (j + 1) : ℚ) =
        2 * (2 * j + 1) * ((2 * j).choose j : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ j
    have h2 : ((j : ℚ) + 1) ≠ 0 := by positivity
    have h3 : ((2 * (j + 1)).choose (j + 1) : ℚ) =
        2 * (2 * j + 1) * ((2 * j).choose j : ℚ) / (j + 1) := by
      field_simp; linarith
    rw [h3]
    push_cast
    field_simp
    ring

/-- CO-041. `∑_{k=0}^n C(2k,k) C(2n-2k,n-k) = 4^n`, from the Chu–Vandermonde identity for
`C(-1/2, ·)` (the book squares the generating function `(1-4x)^(-1/2)`). -/
@[kb "kellertrotter2017" "Corollary 8.14, p. 192"]
theorem sum_centralBinom_mul (n : ℕ) :
    ∑ k ∈ range (n + 1), (2 * k).choose k * (2 * (n - k)).choose (n - k) = 4 ^ n := by
  have h := Ring.add_choose_eq (r := (-1 / 2 : ℚ)) (s := (-1 / 2 : ℚ)) n (Commute.refl _)
  rw [show (-1 / 2 + -1 / 2 : ℚ) = -(1 : ℚ) by norm_num, Ring.choose_neg',
    Ring.multichoose_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [choose_neg_half] at h
  have h4 : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ k * ((2 * k).choose k : ℚ) / 2 ^ (2 * k) *
      ((-1) ^ (n - k) * ((2 * (n - k)).choose (n - k) : ℚ) / 2 ^ (2 * (n - k))) =
      (-1) ^ n / 4 ^ n * (((2 * k).choose k * (2 * (n - k)).choose (n - k) : ℕ) : ℚ) := by
    intro k hk
    have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have e1 : (-1 : ℚ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
      rw [← pow_add]; congr 1; omega
    have e2 : (4 : ℚ) ^ n = 2 ^ (2 * k) * 2 ^ (2 * (n - k)) := by
      rw [← pow_add, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; omega
    rw [e1, e2]; push_cast; field_simp
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum] at h
  have h5 : (Int.negOnePow n • (1 : ℚ)) = (-1) ^ n := by
    simp [Int.negOnePow_def, Units.smul_def]
  rw [h5] at h
  have hn : ((-1 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h6 : ((∑ k ∈ range (n + 1), (2 * k).choose k * (2 * (n - k)).choose (n - k) : ℕ) : ℚ)
      = 4 ^ n := by
    field_simp at h
    push_cast at h ⊢
    linarith
  exact_mod_cast h6

end HalfBinomial

end UndergradKB.Combinatorics
