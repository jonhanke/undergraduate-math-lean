import UndergradKB.DifferentialEquations.MatrixSystems
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Linear equations of order `n` (Lebl §2.3)

`y⁽ⁿ⁾ + aₙ₋₁(x) y⁽ⁿ⁻¹⁾ + ⋯ + a₀(x) y = f(x)` on an interval `I`. A solution is recorded together with its derivatives
`D 0 = y, D 1 = y', …, D n = y⁽ⁿ⁾` (`IsDerivChain`); on an open interval `D k` is the iterated derivative
(`IsDerivChain.iteratedDeriv_eq`). The equation is the first-order system `Y' = M(x) Y + (0, …, 0, f)` for
`Y = (y, y', …, y⁽ⁿ⁻¹⁾)` and the companion matrix `M` (Lebl §3.1.3), so the theory follows from
`MatrixSystems.lean`. -/

namespace UndergradKB.DifferentialEquations

open Set Matrix

variable {n : ℕ}

/-- `D 0, D 1, …, D n` are successive derivatives on `I`: `(D k)' = D (k+1)` at every point of `I`. -/
def IsDerivChain (I : Set ℝ) (D : Fin (n + 1) → ℝ → ℝ) : Prop :=
  ∀ k : Fin n, ∀ t ∈ I, HasDerivAt (D k.castSucc) (D k.succ t) t

/-- `D` is a derivative chain on `I` solving `y⁽ⁿ⁾ + ∑ aₖ(x) y⁽ᵏ⁾ = f(x)`. -/
def SolvesLinN (a : Fin n → ℝ → ℝ) (f : ℝ → ℝ) (I : Set ℝ) (D : Fin (n + 1) → ℝ → ℝ) : Prop :=
  IsDerivChain I D ∧ ∀ t ∈ I, D (Fin.last n) t + ∑ k, a k t * D k.castSucc t = f t

/-- On an open set the chain consists of the iterated derivatives of `y = D 0`. -/
theorem IsDerivChain.iteratedDeriv_eq {I : Set ℝ} (hI : IsOpen I) {D : Fin (n + 1) → ℝ → ℝ}
    (hD : IsDerivChain I D) : ∀ k : Fin (n + 1), ∀ t ∈ I, iteratedDeriv k (D 0) t = D k t := by
  intro k
  induction k using Fin.induction with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [Fin.val_succ, iteratedDeriv_succ]
    have hev : iteratedDeriv k (D 0) =ᶠ[nhds t] D k.castSucc :=
      Filter.eventually_of_mem (hI.mem_nhds ht) fun u hu => by simpa using ih u hu
    rw [hev.deriv_eq, (hD k t ht).deriv]

/-- The companion matrix of `y⁽ⁿ⁾ + ∑ aₖ y⁽ᵏ⁾`: ones above the diagonal and last row `-a₀, …, -aₙ₋₁`. -/
def companionN (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if (i : ℕ) + 1 = j then 1 else 0) + (if (i : ℕ) + 1 = n then -a j else 0)

/-- The vector `(y, y', …, y⁽ⁿ⁻¹⁾)`. -/
def chainVec (D : Fin (n + 1) → ℝ → ℝ) (t : ℝ) : Fin n → ℝ := fun i => D i.castSucc t

/-- The forcing vector `(0, …, 0, f)`. -/
def lastVec (c : ℝ) : Fin n → ℝ := fun i => if (i : ℕ) + 1 = n then c else 0

@[simp] lemma lastVec_zero : lastVec (n := n) 0 = 0 := by ext i; simp [lastVec]

lemma companionN_mulVec (a : Fin n → ℝ) (Y : Fin n → ℝ) (i : Fin n) :
    (companionN a *ᵥ Y) i =
      (if h : (i : ℕ) + 1 < n then Y ⟨i + 1, h⟩ else 0) +
        (if (i : ℕ) + 1 = n then -∑ j, a j * Y j else 0) := by
  simp only [Matrix.mulVec, dotProduct, companionN, add_mul, Finset.sum_add_distrib]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single ⟨i + 1, h⟩]
      · simp
      · intro j _ hj
        have : (i : ℕ) + 1 ≠ j := fun e => hj (Fin.ext e.symm)
        simp [this]
      · simp
    · apply Finset.sum_eq_zero
      intro j _
      have : (i : ℕ) + 1 ≠ j := by omega
      simp [this]
  · split_ifs <;> simp [Finset.sum_neg_distrib]

lemma SolvesLinN.hasDerivAt_vec {a : Fin n → ℝ → ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    {D : Fin (n + 1) → ℝ → ℝ} (hD : SolvesLinN a f I D) :
    ∀ t ∈ I, HasDerivAt (chainVec D) (companionN (fun j => a j t) *ᵥ chainVec D t + lastVec (f t)) t := by
  intro t ht
  rw [hasDerivAt_pi]
  intro i
  show HasDerivAt (D i.castSucc) _ t
  convert hD.1 i t ht using 1
  rw [Pi.add_apply, companionN_mulVec]
  simp only [chainVec, lastVec]
  by_cases h : (i : ℕ) + 1 < n
  · have h' : (i : ℕ) + 1 ≠ n := by omega
    simp only [h, h', dite_true, ite_false, add_zero]
    congr 1
  · have h' : (i : ℕ) + 1 = n := by omega
    have hi : i.succ = Fin.last n := Fin.ext (by simp [h'])
    rw [dif_neg h, if_pos h', if_pos h', hi]
    linarith [hD.2 t ht]

lemma continuousOn_companionN {a : Fin n → ℝ → ℝ} {I : Set ℝ} (ha : ∀ k, ContinuousOn (a k) I) :
    ContinuousOn (fun t => companionN (fun j => a j t)) I := by
  apply continuousOn_pi.2; intro i
  apply continuousOn_pi.2; intro j
  simp only [companionN]
  split_ifs
  · exact continuousOn_const.add (ha j).neg
  · exact continuousOn_const.add continuousOn_const
  · exact continuousOn_const.add (ha j).neg
  · exact continuousOn_const.add continuousOn_const

/-- **Uniqueness for the `n`-th order linear equation** (Lebl, Theorem 2.3.2, uniqueness half): with coefficients
continuous on an interval `I`, two solutions with the same `y(a), y'(a), …, y⁽ⁿ⁻¹⁾(a)` at a point `a ∈ I` are equal
on `I`. -/
@[kb "lebldiffyqs2026" "Theorem 2.3.2, p. 90"]
theorem linN_unique {a : Fin n → ℝ → ℝ} {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (ha : ∀ k, ContinuousOn (a k) I) {D E : Fin (n + 1) → ℝ → ℝ} (hD : SolvesLinN a f I D)
    (hE : SolvesLinN a f I E) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (h0 : ∀ k : Fin n, D k.castSucc t₀ = E k.castSucc t₀) :
    ∀ k : Fin n, ∀ t ∈ I, D k.castSucc t = E k.castSucc t := by
  have := matrix_linear_unique hI (continuousOn_companionN ha) hD.hasDerivAt_vec hE.hasDerivAt_vec ht₀
    (show chainVec D t₀ = chainVec E t₀ from funext h0)
  intro k t ht
  exact congrFun (this t ht) k

/-- **Superposition** (Lebl, Theorem 2.3.1): a linear combination of solutions of the homogeneous `n`-th order
equation (with their derivatives) is a solution. -/
@[kb "lebldiffyqs2026" "Theorem 2.3.1, p. 90"]
theorem linN_superposition {a : Fin n → ℝ → ℝ} {I : Set ℝ} {ι : Type*} (s : Finset ι)
    {D : ι → Fin (n + 1) → ℝ → ℝ} (hD : ∀ i ∈ s, SolvesLinN a 0 I (D i)) (c : ι → ℝ) :
    SolvesLinN a 0 I (fun k t => ∑ i ∈ s, c i * D i k t) := by
  constructor
  · intro k t ht
    exact HasDerivAt.fun_sum fun i hi => ((hD i hi).1 k t ht).const_mul (c i)
  · intro t ht
    have h : ∀ i ∈ s, c i * (D i (Fin.last n) t + ∑ k, a k t * D i k.castSucc t) = 0 := by
      intro i hi; rw [(hD i hi).2 t ht]; simp
    calc (∑ i ∈ s, c i * D i (Fin.last n) t) + ∑ k, a k t * ∑ i ∈ s, c i * D i k.castSucc t
        = ∑ i ∈ s, c i * (D i (Fin.last n) t + ∑ k, a k t * D i k.castSucc t) := by
          simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := Finset.sum_eq_zero h
      _ = (0 : ℝ → ℝ) t := rfl

/-- **General solution of the `n`-th order homogeneous equation** (Lebl, Theorem 2.3.3): with coefficients
continuous on an interval `I`, if `y₁, …, yₙ` are linearly independent solutions on `I`, every solution is
`y = C₁ y₁ + ⋯ + Cₙ yₙ` on `I` (together with its derivatives). -/
@[kb "lebldiffyqs2026" "Theorem 2.3.3, p. 92"]
theorem linN_general_solution {a : Fin n → ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected) (hne : I.Nonempty)
    (ha : ∀ k, ContinuousOn (a k) I) {D : Fin n → Fin (n + 1) → ℝ → ℝ}
    (hD : ∀ i, SolvesLinN a 0 I (D i)) (hli : LinearIndependent ℝ (fun i (t : I) => D i 0 t))
    {E : Fin (n + 1) → ℝ → ℝ} (hE : SolvesLinN a 0 I E) :
    ∃ C : Fin n → ℝ, ∀ k : Fin n, ∀ t ∈ I, E k.castSucc t = ∑ i, C i * D i k.castSucc t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun k => k.elim0⟩
  have hlast : ∀ c : ℝ, lastVec (n := n) c = c • lastVec 1 := fun c => by
    ext i; simp [lastVec]
  have hx : ∀ i, ∀ t ∈ I, HasDerivAt (chainVec (D i))
      (companionN (fun j => a j t) *ᵥ chainVec (D i) t) t := by
    intro i t ht
    simpa [lastVec] using (hD i).hasDerivAt_vec t ht
  have hlix : LinearIndependent ℝ (fun i (t : I) => chainVec (D i) t) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc
    apply hli c
    funext t
    have := congrFun (congrFun hc t) ⟨0, hn⟩
    simpa [chainVec] using this
  obtain ⟨C, hC, -⟩ := matrix_general_solution hI hne (continuousOn_companionN ha) hx hlix
    (y := chainVec E) (fun t ht => by simpa [lastVec] using hE.hasDerivAt_vec t ht)
  refine ⟨C, fun k t ht => ?_⟩
  have := congrFun (hC t ht) k
  simpa [chainVec, Finset.sum_apply] using this

end UndergradKB.DifferentialEquations
