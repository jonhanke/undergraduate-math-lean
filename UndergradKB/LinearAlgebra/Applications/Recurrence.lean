import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import UndergradKB.Common.Attr

/-! # Linear recurrences (Hefferon, Topic: Linear Recurrences) -/

namespace UndergradKB.LinearAlgebra

open Polynomial Matrix

section Companion

variable {K : Type*} [CommRing K]

/-- The companion matrix of a linear recurrence: the matrix of the map `tupleSucc` sending
`(s₀, …, s_{d-1})` to `(s₁, …, s_{d-1}, Σ cᵢ sᵢ)`; it is Hefferon's companion matrix up to
transposition and reversal of the order of the coordinates. -/
noncomputable def recurrenceCompanion (E : LinearRecurrence K) :
    Matrix (Fin E.order) (Fin E.order) K :=
  LinearMap.toMatrix' E.tupleSucc

private lemma companion_apply {n : ℕ} (c : Fin (n + 1) → K) (i j : Fin (n + 1)) :
    recurrenceCompanion ⟨n + 1, c⟩ i j =
      if (i : ℕ) + 1 < n + 1 then (if (j : ℕ) = i + 1 then 1 else 0) else c j := by
  simp only [recurrenceCompanion, LinearMap.toMatrix'_apply, LinearRecurrence.tupleSucc,
    LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h : (i : ℕ) + 1 < n + 1
  · simp only [h, dite_true, ite_true]
    congr 1
    by_cases hj : (j : ℕ) = i + 1
    · have : (⟨(i : ℕ) + 1, h⟩ : Fin (n + 1)) = j := Fin.ext hj.symm
      simp [this, hj]
    · have : (⟨(i : ℕ) + 1, h⟩ : Fin (n + 1)) ≠ j := fun e => hj (by rw [← e])
      simp [this, hj, Ne.symm this]
  · simp [h, Pi.single_apply, mul_ite]

/-- The characteristic polynomial of the companion matrix of a recurrence is the polynomial
associated with the recurrence (`x^d - c_{d-1} x^{d-1} - ... - c_0` in Mathlib's indexing); the
sign is `+` because both polynomials are monic. -/
@[kb "hefferon2020" "Topic-Recurrence.3, p. 487"]
theorem hefferon_Topic_Recurrence_3 (E : LinearRecurrence K) :
    (recurrenceCompanion E).charpoly = E.charPoly := by
  obtain ⟨d, c⟩ := E
  cases d with
  | zero =>
    simp [Matrix.charpoly, LinearRecurrence.charPoly]
  | succ n =>
    set M := recurrenceCompanion ⟨n + 1, c⟩ with hM
    set N := charmatrix M with hN
    set p : K[X] := (LinearRecurrence.mk (n + 1) c).charPoly with hp
    let v : Fin (n + 1) → K[X] := fun i => X ^ (i : ℕ)
    have hNv : N.mulVec v = p • Pi.single (Fin.last n) 1 := by
      funext i
      have e1 : ∑ j, (Matrix.diagonal (fun _ => (X : K[X])) i j) * v j = X * v i := by
        simp [Matrix.diagonal_apply]
      have e2 : ∑ j, C (M i j) * v j = if (i : ℕ) + 1 < n + 1 then X ^ ((i : ℕ) + 1)
          else ∑ j, C (c j) * X ^ (j : ℕ) := by
        simp only [hM, companion_apply]
        by_cases h : (i : ℕ) + 1 < n + 1
        · simp only [h, ite_true]
          rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, h⟩ : Fin (n + 1))]
          · simp [v]
          · intro j _ hj
            have : (j : ℕ) ≠ i + 1 := fun e => hj (Fin.ext e)
            simp [this]
          · simp
        · simp [h, v]
      have : (N.mulVec v) i = X * v i - ∑ j, C (M i j) * v j := by
        simp only [Matrix.mulVec, dotProduct, hN, charmatrix_apply, sub_mul,
          Finset.sum_sub_distrib]
        rw [e1]
      rw [this, e2]
      by_cases h : (i : ℕ) + 1 < n + 1
      · have hi : i ≠ Fin.last n := by
          intro e; subst e; simp at h
        simp [h, hi, v, pow_succ, mul_comm]
      · have hi : i = Fin.last n := by
          apply Fin.ext
          have h2 : (i : ℕ) < n + 1 := i.isLt
          simp only [Fin.val_last]; omega
        subst hi
        have hmon : ∀ (k : ℕ) (a : K), (monomial k a : K[X]) = C a * X ^ k :=
          fun k a => C_mul_X_pow_eq_monomial.symm
        simp only [v, hp, LinearRecurrence.charPoly, Pi.smul_apply, Pi.single_eq_same,
          smul_eq_mul, mul_one, hmon, map_one, one_mul, Fin.val_last, lt_self_iff_false, ite_false]
        rw [← pow_succ']
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) K[X] :=
      Matrix.of fun i j => if j = 0 then v i else if i = j then 1 else 0
    have hU : U.det = 1 := by
      rw [det_of_isLowerTriangular U ?_]
      · apply Finset.prod_eq_one
        intro i _
        by_cases hi : i = 0
        · subst hi; simp [U, v]
        · simp [U, hi]
      · intro i j hij
        have hij' : i < j := hij
        have hj : j ≠ 0 := by
          intro hj; subst hj; exact absurd hij' (by simp)
        simp [U, hj, hij'.ne]
    have hNU : N * U = N.updateCol 0 (p • Pi.single (Fin.last n) 1) := by
      ext i j
      by_cases hj : j = 0
      · subst hj
        rw [Matrix.updateCol_self, ← hNv]
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, U]
      · rw [Matrix.updateCol_ne hj]
        simp [Matrix.mul_apply, U, hj]
    have hmin : (N.updateCol 0 (Pi.single (Fin.last n) 1)).det = 1 := by
      rw [det_succ_column_zero, Finset.sum_eq_single (Fin.last n)]
      · rw [Fin.succAbove_last]
        have hl : ((N.updateCol 0 (Pi.single (Fin.last n) 1)).submatrix Fin.castSucc
            Fin.succ).det = (-1) ^ n := by
          rw [det_of_isLowerTriangular _ ?_]
          · rw [Finset.prod_congr rfl (g := fun _ => (-1 : K[X]))]
            · simp
            · intro i _
              have : (Fin.castSucc i : Fin (n + 1)) ≠ Fin.succ i := by
                intro e; have := congrArg Fin.val e; simp at this
              simp [hN, charmatrix_apply, hM, companion_apply, Matrix.diagonal_apply, this]
          · intro i j hij
            have hij' : i < j := hij
            have h1 : (Fin.castSucc i : Fin (n + 1)) ≠ Fin.succ j := by
              intro e; have := congrArg Fin.val e; simp at this; omega
            have h2 : ¬ ((i : ℕ) + 1 < n + 1 ∧ (j : ℕ) + 1 = i + 1) := by
              omega
            simp [hN, charmatrix_apply, hM, companion_apply, Matrix.diagonal_apply, h1]
            intro h; omega
        rw [hl]
        simp [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      · intro i _ hi
        simp [hi]
      · simp
    calc M.charpoly = N.det := rfl
      _ = (N * U).det := by rw [det_mul, hU, mul_one]
      _ = p := by
        rw [hNU, det_updateCol_smul, hmin, mul_one]

end Companion

section Solutions

variable {K : Type*} [Field K]

/-- If the associated polynomial of `E` has `E.order` distinct roots `r₀, …, r_{d-1}` (the
hypothesis of Hefferon's Topic), then the geometric sequences `n ↦ rᵢⁿ` are solutions, they are
linearly independent, and every solution is uniquely `Σ cᵢ rᵢⁿ`. -/
@[kb "hefferon2020" "Topic-Recurrence.4, p. 488"]
theorem hefferon_Topic_Recurrence_4 (E : LinearRecurrence K) (r : Fin E.order → K)
    (hr : Function.Injective r) (hroot : ∀ i, E.charPoly.IsRoot (r i)) :
    (∀ i, E.IsSolution fun n => r i ^ n) ∧
    LinearIndependent K (fun i (n : ℕ) => r i ^ n) ∧
    ∀ u : ℕ → K, E.IsSolution u → ∃! c : Fin E.order → K, ∀ n, u n = ∑ i, c i * r i ^ n := by
  have hsol : ∀ i, E.IsSolution fun n => r i ^ n := fun i =>
    (E.geom_sol_iff_root_charPoly (r i)).2 (hroot i)
  have hli : LinearIndependent K (fun i (n : ℕ) => r i ^ n) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : g ᵥ* Matrix.vandermonde r = 0 := by
      ext j
      have := congrFun hg (j : ℕ)
      simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde, mul_comm] using this
    exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero
      (Matrix.det_vandermonde_ne_zero_iff.2 hr) h1) i
  refine ⟨hsol, hli, fun u hu => ?_⟩
  let f : Fin E.order → E.solSpace := fun i => ⟨fun n => r i ^ n, hsol i⟩
  have hf : LinearIndependent K f := by
    apply LinearIndependent.of_comp E.solSpace.subtype
    exact hli
  have : Module.Finite K E.solSpace := Module.Finite.of_basis E.basis
  have hcard : Fintype.card (Fin E.order) = Module.finrank K E.solSpace := by
    rw [Module.finrank_eq_of_rank_eq E.solSpace_rank]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank' f hf hcard
  have hb : ∀ i, b i = f i := fun i => by simp [b]
  refine ⟨fun i => b.repr ⟨u, hu⟩ i, fun n => ?_, fun c hc => ?_⟩
  · have := b.sum_repr ⟨u, hu⟩
    have h2 := congrArg (fun w : E.solSpace => (w : ℕ → K) n) this
    simp only [hb, f] at h2
    rw [← h2]
    simp [Submodule.coe_sum]
  · have : (⟨u, hu⟩ : E.solSpace) = ∑ i, c i • b i := by
      apply Subtype.ext
      funext n
      simp [hb, f, hc n, Submodule.coe_sum]
    ext i
    rw [this]
    exact (congrFun (b.repr_sum_self c) i).symm

/-- A solution of the nonhomogeneous recurrence `u(n+d) = Σ cᵢ u(n+i) + g(n)`. -/
def IsNonhomSolution (E : LinearRecurrence K) (g u : ℕ → K) : Prop :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i) + g n

/-- Nonhomogeneous recurrences: if `p` is one particular solution, then the solutions are exactly
the sequences `p + h` with `h` a solution of the associated homogeneous recurrence. -/
@[kb "hefferon2020" "Topic-Recurrence.5, p. 489"]
theorem hefferon_Topic_Recurrence_5 (E : LinearRecurrence K) (g p : ℕ → K)
    (hp : IsNonhomSolution E g p) (u : ℕ → K) :
    IsNonhomSolution E g u ↔ ∃ h, E.IsSolution h ∧ u = p + h := by
  constructor
  · intro hu
    refine ⟨u - p, fun n => ?_, by abel⟩
    have h1 := hu n
    have h2 := hp n
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    linear_combination h1 - h2
  · rintro ⟨h, hh, rfl⟩ n
    have := hh n
    have h2 := hp n
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    linear_combination h2 + this

end Solutions

end UndergradKB.LinearAlgebra
