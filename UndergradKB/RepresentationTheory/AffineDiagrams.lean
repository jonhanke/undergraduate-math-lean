import UndergradKB.RepresentationTheory.DynkinForms
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Fin
import UndergradKB.Common.Attr

/-! # The positive-kernel criterion and the affine diagrams `D̃_k` (Etingof et al., Problem 5.3(g))

* `isAffineKernel_of_pos`: if `G` is a connected graph and `v` is a vector with positive integer entries
  killed by the Cartan matrix, then the form of `G` is positive semidefinite with kernel the line spanned by
  `v`.  The proof writes the form as a weighted sum of squares of the differences `x_i / v_i - x_j / v_j`
  over the edges of `G`.
* `affineD k`: the graph `D̃_k` on `k + 5` vertices (a path `0, ..., k` with two leaves attached at each
  end), with the marks vector `affineDVec k`; `affine_D` and `isAffineDynkin_D` show it is an affine Dynkin
  diagram.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Matrix Finset

/-! ### The positive-kernel criterion -/

theorem mulVec_cartanMatrix_apply {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n → ℤ)
    (i : Fin n) :
    (cartanMatrix G *ᵥ v) i = 2 * v i - ∑ j, if G.Adj i j then v j else 0 := by
  simp only [mulVec, dotProduct, cartanMatrix_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp

theorem neighbour_sum_of_kernel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n → ℤ)
    (hMv : cartanMatrix G *ᵥ v = 0) (i : Fin n) :
    ∑ j, (if G.Adj i j then v j else 0) = 2 * v i := by
  have := congrFun hMv i
  rw [mulVec_cartanMatrix_apply] at this
  simp only [Pi.zero_apply] at this
  linarith

/-- The quadratic form of a graph with a positive kernel vector is a weighted sum of squares over edges. -/
theorem dot_cartanReal_eq_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n → ℤ)
    (hv : ∀ i, 0 < v i) (hMv : cartanMatrix G *ᵥ v = 0) (x : Fin n → ℝ) :
    x ⬝ᵥ (cartanReal G *ᵥ x) =
      (1 / 2) * ∑ i, ∑ j, (if G.Adj i j then (v i : ℝ) * v j * (x i / v i - x j / v j) ^ 2 else 0) := by
  have hvR : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast hv i
  have hs : ∀ i, ∑ j, (if G.Adj i j then (v j : ℝ) else 0) = 2 * v i := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (neighbour_sum_of_kernel G v hMv i)
    push_cast at this
    exact this
  rw [dot_cartanReal_eq_sum]
  have h1 : ∀ i j, x i * (cartanMatrix G i j : ℝ) * x j =
      (if i = j then 2 * (x i * x j) else 0) - (if G.Adj i j then x i * x j else 0) := by
    intro i j
    rw [cartanMatrix_apply]
    push_cast
    split_ifs <;> ring
  have h2 : ∀ i j, (if G.Adj i j then (v i : ℝ) * v j * (x i / v i - x j / v j) ^ 2 else 0) =
      (if G.Adj i j then (v j : ℝ) * (x i ^ 2 / v i) else 0) +
      (if G.Adj j i then (v i : ℝ) * (x j ^ 2 / v j) else 0) -
      (if G.Adj i j then x i * x j else 0) - (if G.Adj i j then x i * x j else 0) := by
    intro i j
    have hvi := (hvR i).ne'
    have hvj := (hvR j).ne'
    by_cases h : G.Adj i j
    · have h' : G.Adj j i := h.symm
      simp only [h, h', ite_true]
      field_simp
      ring
    · have h' : ¬ G.Adj j i := fun e => h e.symm
      simp [h, h']
  have hS1 : ∀ i, ∑ j, (if G.Adj i j then (v j : ℝ) * (x i ^ 2 / v i) else 0) = 2 * x i ^ 2 := by
    intro i
    have hvi := (hvR i).ne'
    have : ∀ j, (if G.Adj i j then (v j : ℝ) * (x i ^ 2 / v i) else 0) =
        (x i ^ 2 / v i) * (if G.Adj i j then (v j : ℝ) else 0) := by
      intro j; split_ifs <;> ring
    simp only [this, ← Finset.mul_sum, hs]
    field_simp
  have hS2 : ∑ i, ∑ j, (if G.Adj j i then (v i : ℝ) * (x j ^ 2 / v j) else 0) = ∑ i, 2 * x i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hS1 i
  have e : ∀ i, 2 * (x i * x i) = 2 * x i ^ 2 := fun i => by ring
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, hS1, hS2, e]
  ring

/-- **Problem 5.3(g), criterion.**  If a connected graph has a vector with all entries positive killed by its
Cartan matrix, then its form is positive semidefinite and the kernel is the line spanned by that vector. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineKernel_of_pos {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hc : G.Connected)
    (v : Fin n → ℤ) (hv : ∀ i, 0 < v i) (hMv : cartanMatrix G *ᵥ v = 0) : IsAffineKernel G v := by
  have hvR : ∀ i, (0 : ℝ) < v i := fun i => by exact_mod_cast hv i
  refine isAffineKernel_of_nonneg G v hv hMv _ (dot_cartanReal_eq_edges G v hv hMv) ?_ ?_
  · intro x
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
    split_ifs
    · exact mul_nonneg (mul_nonneg (hvR i).le (hvR j).le) (sq_nonneg _)
    · exact le_rfl
  · intro x hx
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ∑ j, (if G.Adj i j then
        (v i : ℝ) * v j * (x i / v i - x j / v j) ^ 2 else 0) := fun i _ =>
      Finset.sum_nonneg fun j _ => by
        split_ifs
        · exact mul_nonneg (mul_nonneg (hvR i).le (hvR j).le) (sq_nonneg _)
        · exact le_rfl
    have hx' : ∑ i, ∑ j, (if G.Adj i j then
        (v i : ℝ) * v j * (x i / v i - x j / v j) ^ 2 else 0) = 0 := by linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hx'
    have hedge : ∀ i j, G.Adj i j → x i / v i = x j / v j := by
      intro i j hij
      have h1 := hi i (Finset.mem_univ _)
      have hnn' : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (if G.Adj i j then
          (v i : ℝ) * v j * (x i / v i - x j / v j) ^ 2 else 0) := fun j _ => by
        split_ifs
        · exact mul_nonneg (mul_nonneg (hvR i).le (hvR j).le) (sq_nonneg _)
        · exact le_rfl
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 h1 j (Finset.mem_univ _)
      simp only [hij, ite_true] at h2
      have h3 : (x i / v i - x j / v j) ^ 2 = 0 := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h (mul_pos (hvR i) (hvR j)).ne'
        · exact h
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
      linarith
    have hall : ∀ i j, G.Reachable i j → x i / v i = x j / v j := by
      intro i j ⟨w⟩
      induction w with
      | nil => rfl
      | cons h _ ih => exact (hedge _ _ h).trans ih
    obtain ⟨i0⟩ := hc.nonempty
    refine ⟨x i0 / v i0, ?_⟩
    funext i
    have := hall i i0 (hc i i0)
    have hvi := (hvR i).ne'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← this]
    field_simp

/-! ### The family `D̃_k` -/

/-- The edge relation (one orientation) of `D̃_k` on natural numbers: a path `0, ..., k`, two leaves
`k + 1`, `k + 2` joined to `0`, and two leaves `k + 3`, `k + 4` joined to `k`. -/
def affineDAdj (k : ℕ) (a b : ℕ) : Prop :=
  (a + 1 = b ∧ b ≤ k) ∨ (a = 0 ∧ (b = k + 1 ∨ b = k + 2)) ∨ (a = k ∧ (b = k + 3 ∨ b = k + 4))

instance (k a b : ℕ) : Decidable (affineDAdj k a b) := by
  unfold affineDAdj; infer_instance

/-- The affine Dynkin diagram `D̃_k` on `k + 5` vertices. -/
def affineD (k : ℕ) : SimpleGraph (Fin (k + 5)) :=
  SimpleGraph.fromRel fun a b => affineDAdj k a.val b.val

theorem affineD_adj_iff (k : ℕ) (a b : Fin (k + 5)) :
    (affineD k).Adj a b ↔ affineDAdj k a b ∨ affineDAdj k b a := by
  simp only [affineD, SimpleGraph.fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun e => ?_, h⟩
    subst e
    unfold affineDAdj at h
    omega

instance (k : ℕ) : DecidableRel (affineD k).Adj := fun a b =>
  decidable_of_iff _ (affineD_adj_iff k a b).symm

/-- The marks of `D̃_k`: `2` on the path vertices and `1` on the four leaves. -/
def affineDVec (k : ℕ) : Fin (k + 5) → ℤ := fun i => if i.val ≤ k then 2 else 1

theorem connected_affineD (k : ℕ) : (affineD k).Connected := by
  refine connected_of_parent _ ⟨0, by omega⟩ (fun i => i.val) fun i hi => ?_
  have hi0 : i.val ≠ 0 := fun e => hi (Fin.ext e)
  by_cases h1 : i.val ≤ k
  · refine ⟨⟨i.val - 1, by omega⟩, (affineD_adj_iff _ _ _).2 (Or.inr ?_), ?_⟩
    · unfold affineDAdj; dsimp only; omega
    · dsimp only; omega
  · by_cases h2 : i.val ≤ k + 2
    · refine ⟨⟨0, by omega⟩, (affineD_adj_iff _ _ _).2 (Or.inr ?_), ?_⟩
      · unfold affineDAdj; dsimp only; omega
      · dsimp only; omega
    · refine ⟨⟨k, by omega⟩, (affineD_adj_iff _ _ _).2 (Or.inr ?_), ?_⟩
      · unfold affineDAdj; dsimp only; omega
      · dsimp only; omega

/-- The marks as a function on natural numbers. -/
def affineDMark (k b : ℕ) : ℤ := if b ≤ k then 2 else 1

theorem affineD_neighbour_sum (k a : ℕ) (ha : a < k + 5) :
    ∑ b ∈ range (k + 5), (if affineDAdj k a b ∨ affineDAdj k b a then affineDMark k b else 0) =
      2 * affineDMark k a := by
  rw [← Finset.sum_filter]
  by_cases hk : k = 0
  · subst hk
    by_cases h0 : a = 0
    · subst h0
      have : (range (0 + 5)).filter (fun b => affineDAdj 0 0 b ∨ affineDAdj 0 b 0) = {1, 2, 3, 4} := by
        ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; unfold affineDAdj; omega
      rw [this]
      simp [affineDMark]
    · have : (range (0 + 5)).filter (fun b => affineDAdj 0 a b ∨ affineDAdj 0 b a) = {0} := by
        ext b; simp only [mem_filter, mem_range, mem_singleton]; unfold affineDAdj; omega
      rw [this]
      simp only [Finset.sum_singleton, affineDMark]
      split_ifs <;> omega
  · by_cases h0 : a = 0
    · subst h0
      have : (range (k + 5)).filter (fun b => affineDAdj k 0 b ∨ affineDAdj k b 0) =
          {1, k + 1, k + 2} := by
        ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; unfold affineDAdj; omega
      rw [this, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
      simp only [affineDMark]
      split_ifs <;> omega
    · by_cases h1 : a < k
      · have : (range (k + 5)).filter (fun b => affineDAdj k a b ∨ affineDAdj k b a) =
            {a - 1, a + 1} := by
          ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; unfold affineDAdj; omega
        rw [this, Finset.sum_pair (by omega)]
        simp only [affineDMark]
        split_ifs <;> omega
      · by_cases h2 : a = k
        · subst h2
          have : (range (a + 5)).filter (fun b => affineDAdj a a b ∨ affineDAdj a b a) =
              {a - 1, a + 3, a + 4} := by
            ext b; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; unfold affineDAdj; omega
          rw [this, Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega)]
          simp only [affineDMark]
          split_ifs <;> omega
        · by_cases h3 : a ≤ k + 2
          · have : (range (k + 5)).filter (fun b => affineDAdj k a b ∨ affineDAdj k b a) = {0} := by
              ext b; simp only [mem_filter, mem_range, mem_singleton]; unfold affineDAdj; omega
            rw [this]
            simp only [Finset.sum_singleton, affineDMark]
            split_ifs <;> omega
          · have : (range (k + 5)).filter (fun b => affineDAdj k a b ∨ affineDAdj k b a) = {k} := by
              ext b; simp only [mem_filter, mem_range, mem_singleton]; unfold affineDAdj; omega
            rw [this]
            simp only [Finset.sum_singleton, affineDMark]
            split_ifs <;> omega

theorem cartanMatrix_affineD_mulVec (k : ℕ) : cartanMatrix (affineD k) *ᵥ affineDVec k = 0 := by
  funext i
  rw [mulVec_cartanMatrix_apply]
  have h := affineD_neighbour_sum k i.val i.isLt
  rw [← Fin.sum_univ_eq_sum_range (fun b => if affineDAdj k i.val b ∨ affineDAdj k b i.val
    then affineDMark k b else 0)] at h
  have h' : ∑ j : Fin (k + 5), (if (affineD k).Adj i j then affineDVec k j else 0) =
      2 * affineDVec k i := by
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    exact if_congr (affineD_adj_iff k i j) rfl rfl
  simp only [h', Pi.zero_apply]
  ring

/-- **Problem 5.3(g).**  The diagram `D̃_k` (on `k + 5` vertices) is positive semidefinite with kernel spanned
by the marks `(2, ..., 2, 1, 1, 1, 1)`. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem affine_D (k : ℕ) : IsAffineKernel (affineD k) (affineDVec k) :=
  isAffineKernel_of_pos _ (connected_affineD k) _
    (fun i => by unfold affineDVec; split_ifs <;> norm_num) (cartanMatrix_affineD_mulVec k)

/-- **Problem 5.3(g).**  `D̃_k` is an affine Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.3(g), p. 80"]
theorem isAffineDynkin_D (k : ℕ) : IsAffineDynkin (affineD k) :=
  (affine_D k).isAffineDynkin (connected_affineD k)

end UndergradKB.RepresentationTheory.Roots
