import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import UndergradKB.Combinatorics.AeqB.Zeilberger
import UndergradKB.Common.Attr

/-!
# Creative telescoping: first-order case, continuous analogue, recurrence operators
(Petkovsek–Wilf–Zeilberger, "A = B", Sections 6.4, 8.1, 8.2)

* CO-431 (Proposition 8.1.1): for `F` whose sum `f(n)` is hypergeometric, `f(n+1) = r(n) f(n)`,
  creative telescoping yields the first-order recurrence `f(n+1) - r(n) f(n) = 0` iff the WZ method
  applied to `F̄ = F / f` succeeds (both with the right-hand side `G` a rational multiple of `F`).
* CO-428: the continuous analogue of creative telescoping.
* CO-478: the shift operator `N` on `K^ℕ`, recurrence operators `∑ a_k N^k` with sequence
  coefficients, order, kernel, solution sets of `L y = f` as affine subspaces over `Ker L`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace UndergradKB.Combinatorics.AeqB

open Finset MeasureTheory Filter Topology
open Zeilberger

/-! ### CO-431: Proposition 8.1.1 -/

namespace Prop811

variable {K : Type*} [Field K]

/-- CO-431. "Creative telescoping with input `F` produces the first-order recurrence
`f(n+1) - r(n) f(n) = 0`": there is a function `G` which is a rational multiple of `F`
(`G(n,k) = R(n,k) F(n,k)`) with `F(n+1,k) - r(n) F(n,k) = G(n,k+1) - G(n,k)` for all `n, k`
(i.e. `F(n+1,·) - r(n) F(n,·)` is Gosper-summable in `k`). -/
def CTFirstOrder (F : ℤ → ℤ → K) (r : ℤ → K) : Prop :=
  ∃ R G : ℤ → ℤ → K, (∀ n k, G n k = R n k * F n k) ∧
    IsTelescopedRecurrence 1 (fun j n => if j = 0 then -r n else 1) F G

/-- CO-431. "The WZ method proves `∑_k F(n,k) = f(n)`": `F̄ = F / f` admits a partner `Ḡ`, a
rational multiple of `F̄`, forming a WZ pair, so that `∑_k F̄(n,k)` is constant in `n`. -/
def WZProves (F : ℤ → ℤ → K) (f : ℤ → K) : Prop :=
  ∃ R Gb : ℤ → ℤ → K, (∀ n k, Gb n k = R n k * (F n k / f n)) ∧
    WZEq (fun n k => F n k / f n) Gb

/-- CO-431. Proposition 8.1.1. Let `f(n)` be nowhere zero with `f(n+1) = r(n) f(n)`. Creative
telescoping with input `F` produces a first-order recurrence for `f` iff the WZ method proves
`∑_k F(n,k) = f(n)`.  (We state the identities for all integers `n, k`; hypergeometricity of `F`
is not needed for the equivalence of the two identities.) -/
@[kb "petkovsekwilfzeilberger1996" "Proposition 8.1.1, p. 153"]
theorem ctFirstOrder_iff_wzProves (F : ℤ → ℤ → K) (f r : ℤ → K) (hf : ∀ n, f n ≠ 0)
    (hr : ∀ n, f (n + 1) = r n * f n) : CTFirstOrder F r ↔ WZProves F f := by
  have hrn : ∀ n, r n ≠ 0 := fun n h0 => hf (n + 1) (by rw [hr, h0, zero_mul])
  -- the middle steps of the book's chain: divide by `f(n+1)`
  have key : ∀ n k, F (n + 1) k / f (n + 1) - F n k / f n =
      (F (n + 1) k - r n * F n k) / f (n + 1) := by
    intro n k
    have := hf n
    have := hrn n
    have := hf (n + 1)
    rw [hr n] at *
    field_simp
  constructor
  · rintro ⟨R, G, hG, h⟩
    refine ⟨fun n k => R n k * f n / f (n + 1), fun n k => G n k / f (n + 1), ?_, ?_⟩
    · intro n k
      have := hf n
      have := hf (n + 1)
      beta_reduce
      rw [hG]
      field_simp
    · intro n k
      have e := h n k
      simp [Finset.sum_range_succ] at e
      simp only
      rw [key, ← sub_div]
      congr 1
      linear_combination e
  · rintro ⟨R, Gb, hG, h⟩
    refine ⟨fun n k => f (n + 1) * R n k / f n, fun n k => f (n + 1) * Gb n k, ?_, ?_⟩
    · intro n k
      have := hf n
      beta_reduce
      rw [hG]
      field_simp
    · intro n k
      have e := h n k
      have e2 := key n k
      have := hf (n + 1)
      simp [Finset.sum_range_succ]
      simp only at e
      rw [e] at e2
      field_simp at e2
      linear_combination -e2

end Prop811

/-! ### CO-428: continuous analogue of creative telescoping -/

namespace Continuous

/-- CO-428. Continuous creative telescoping, in abstract form.  If `∑_{j ≤ J} a_j H_j(y)` is the
derivative of `G` for all real `y`, the `H_j` are integrable and `G(y) → 0` as `y → ±∞`, then
`∑_j a_j ∫ H_j = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 122"]
theorem integral_recurrence (J : ℕ) (a : ℕ → ℝ) (H : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hH : ∀ j ≤ J, Integrable (H j))
    (hG : ∀ y, HasDerivAt G (∑ j ∈ range (J + 1), a j * H j y) y)
    (hGt : Tendsto G atTop (𝓝 0)) (hGb : Tendsto G atBot (𝓝 0)) :
    ∑ j ∈ range (J + 1), a j * ∫ y, H j y = 0 := by
  have hi : ∀ j ∈ range (J + 1), Integrable (fun y => a j * H j y) := fun j hj =>
    (hH j (Nat.lt_succ_iff.1 (mem_range.1 hj))).const_mul (a j)
  have h1 := integral_of_hasDerivAt_of_tendsto hG (integrable_finsetSum _ hi) hGb hGt
  rw [integral_finsetSum _ hi] at h1
  simpa [integral_const_mul] using h1

/-- CO-428 (recurrence for `a_n = ∫ F(n,y) dy`). If
`∑_{j ≤ J} a_j(n) F(n+j, y) = ∂/∂y G(n, y)` for all `y`, each `F(n+j, ·)` is integrable and
`G(n, y) → 0` as `y → ±∞`, then `∑_j a_j(n) ∫ F(n+j, y) dy = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 122"]
theorem integral_telescoping_recurrence (J : ℕ) (a : ℕ → ℤ → ℝ) (F : ℤ → ℝ → ℝ)
    (G : ℤ → ℝ → ℝ) (n : ℤ) (hF : ∀ j ≤ J, Integrable (F (n + j)))
    (hG : ∀ y, HasDerivAt (G n) (∑ j ∈ range (J + 1), a j n * F (n + j) y) y)
    (hGt : Tendsto (G n) atTop (𝓝 0)) (hGb : Tendsto (G n) atBot (𝓝 0)) :
    ∑ j ∈ range (J + 1), a j n * ∫ y, F (n + j) y = 0 :=
  integral_recurrence J (fun j => a j n) (fun j => F (n + j)) (G n) hF hG hGt hGb

/-- CO-428 (differential equation for `f(x) = ∫ F(x,y) dy`). Let `D j x y` stand for
`∂ₓʲ F(x, y)`, suppose `∑_{j ≤ J} a_j(x) D j x y = ∂/∂y G(x, y)`, each `D j x ·` is integrable and
`G(x, y) → 0` as `y → ±∞`.  If `f⁽ʲ⁾(x) = ∫ D j x y dy` (differentiation under the integral sign,
taken as a hypothesis), then `f` satisfies the linear ODE `∑_j a_j(x) f⁽ʲ⁾(x) = 0`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 122"]
theorem integral_telescoping_ode (J : ℕ) (a : ℕ → ℝ → ℝ) (D : ℕ → ℝ → ℝ → ℝ)
    (G : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (x : ℝ) (hD : ∀ j ≤ J, Integrable (D j x))
    (hG : ∀ y, HasDerivAt (G x) (∑ j ∈ range (J + 1), a j x * D j x y) y)
    (hGt : Tendsto (G x) atTop (𝓝 0)) (hGb : Tendsto (G x) atBot (𝓝 0))
    (hf : ∀ j ≤ J, iteratedDeriv j f x = ∫ y, D j x y) :
    ∑ j ∈ range (J + 1), a j x * iteratedDeriv j f x = 0 := by
  have := integral_recurrence J (fun j => a j x) (fun j => D j x) (G x) hD hG hGt hGb
  rw [← this]
  refine sum_congr rfl fun j hj => ?_
  rw [hf j (Nat.lt_succ_iff.1 (mem_range.1 hj))]

end Continuous

/-! ### CO-478: recurrence operators on `K^ℕ` -/

namespace SeqOp

variable {K : Type*} [Field K]

/-- CO-478. The shift operator `N` on `K^ℕ`: `(N y)(n) = y(n+1)`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (linear recurrence operator), p. 155"]
def shiftN : Module.End K (ℕ → K) where
  toFun y n := y (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication of sequences by a fixed sequence `a`, as a `K`-linear operator on `K^ℕ`. -/
def mulSeq (a : ℕ → K) : Module.End K (ℕ → K) where
  toFun y n := a n * y n
  map_add' y z := by ext n; simp [mul_add]
  map_smul' c y := by ext n; simp [mul_left_comm]

theorem shiftN_apply (y : ℕ → K) (n : ℕ) : shiftN y n = y (n + 1) := rfl

theorem mulSeq_apply (a y : ℕ → K) (n : ℕ) : mulSeq a y n = a n * y n := rfl

theorem shiftN_pow_apply (k : ℕ) (y : ℕ → K) (n : ℕ) : (shiftN ^ k : Module.End K (ℕ → K)) y n =
    y (n + k) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, shiftN_apply]
    rfl

/-- The operator ring relation `N a = (N a) N` (where `(N a)(n) = a(n+1)`). -/
theorem shiftN_mul_mulSeq (a : ℕ → K) :
    (shiftN * mulSeq a : Module.End K (ℕ → K)) = mulSeq (fun n => a (n + 1)) * shiftN := rfl

theorem mulSeq_mul (a b : ℕ → K) :
    (mulSeq a * mulSeq b : Module.End K (ℕ → K)) = mulSeq (a * b) := by
  ext y n
  simp [mulSeq_apply, mul_assoc]

/-- CO-478. The linear recurrence operator `L = ∑_{k ≤ r} a_k N^k` with sequence coefficients
`a_k ∈ K^ℕ`, an element of the ring `End_K(K^ℕ)`. -/
@[kb "petkovsekwilfzeilberger1996" "Definition (linear recurrence operator), p. 155"]
def recOp (r : ℕ) (a : ℕ → ℕ → K) : Module.End K (ℕ → K) :=
  ∑ k ∈ range (r + 1), mulSeq (a k) * shiftN ^ k

/-- Termwise form: `(L y)(n) = ∑_{k ≤ r} a_k(n) y(n+k)`. -/
theorem recOp_apply (r : ℕ) (a : ℕ → ℕ → K) (y : ℕ → K) (n : ℕ) :
    recOp r a y n = ∑ k ∈ range (r + 1), a k n * y (n + k) := by
  simp [recOp, LinearMap.sum_apply, Finset.sum_apply, mulSeq_apply, shiftN_pow_apply]

/-- CO-478. The order of `L = ∑_{k ≤ r} a_k N^k` is `r` when `a_r ≠ 0` and `a_0 ≠ 0`
(as sequences). -/
@[kb "petkovsekwilfzeilberger1996" "Definition (linear recurrence operator), p. 155"]
def HasOrder (r : ℕ) (a : ℕ → ℕ → K) : Prop := a r ≠ 0 ∧ a 0 ≠ 0

/-- CO-478. `y ∈ Ker L` iff `∑_k a_k(n) y(n+k) = 0` for all `n`; the kernel is a linear subspace
of `K^ℕ` (it is `LinearMap.ker`). -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 155"]
theorem mem_ker_recOp (r : ℕ) (a : ℕ → ℕ → K) (y : ℕ → K) :
    y ∈ LinearMap.ker (recOp r a) ↔ ∀ n, ∑ k ∈ range (r + 1), a k n * y (n + k) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h n
    rw [← recOp_apply, h]; rfl
  · intro h
    ext n
    rw [recOp_apply, h n]; rfl

/-- The solution set of the recurrence equation `L y = f`. -/
def solSet (L : Module.End K (ℕ → K)) (f : ℕ → K) : Set (ℕ → K) := {y | L y = f}

/-- CO-478. Homogeneous equation: the solutions of `L y = 0` form `Ker L`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 155"]
theorem solSet_zero (L : Module.End K (ℕ → K)) : solSet L 0 = LinearMap.ker L := rfl

/-- CO-478. Inhomogeneous equation (`f ≠ 0`): the zero sequence is not a solution, so the solution
set is never a subspace. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 155"]
theorem zero_notMem_solSet (L : Module.End K (ℕ → K)) {f : ℕ → K} (hf : f ≠ 0) :
    (0 : ℕ → K) ∉ solSet L f := fun h => hf (by simpa [solSet] using h.symm)

/-- CO-478. If `y₀` solves `L y = f`, then `y` solves it iff `y - y₀ ∈ Ker L`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 155"]
theorem mem_solSet_iff {L : Module.End K (ℕ → K)} {f y₀ : ℕ → K} (h₀ : y₀ ∈ solSet L f)
    (y : ℕ → K) : y ∈ solSet L f ↔ y - y₀ ∈ LinearMap.ker L := by
  simp only [solSet, Set.mem_ofPred_eq, LinearMap.mem_ker, map_sub] at h₀ ⊢
  rw [h₀, sub_eq_zero]

/-- CO-478. The solutions of `L y = f` form a coset of `Ker L`: `y₀ + Ker L`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 155"]
theorem solSet_eq_image {L : Module.End K (ℕ → K)} {f y₀ : ℕ → K} (h₀ : y₀ ∈ solSet L f) :
    solSet L f = (fun z => y₀ + z) '' (LinearMap.ker L : Set (ℕ → K)) := by
  ext y
  rw [mem_solSet_iff h₀]
  constructor
  · intro h
    exact ⟨y - y₀, h, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    simpa using hz

/-- CO-478. If `L y = f` has a solution `y₀`, its solution set is the affine subspace through `y₀`
with direction `Ker L`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 155"]
theorem solSet_eq_affineSubspace {L : Module.End K (ℕ → K)} {f y₀ : ℕ → K}
    (h₀ : y₀ ∈ solSet L f) :
    solSet L f = (AffineSubspace.mk' y₀ (LinearMap.ker L) : Set (ℕ → K)) ∧
      (AffineSubspace.mk' y₀ (LinearMap.ker L)).direction = LinearMap.ker L := by
  refine ⟨?_, AffineSubspace.direction_mk' _ _⟩
  ext y
  rw [mem_solSet_iff h₀, SetLike.mem_coe, AffineSubspace.mem_mk']
  rfl

/-- CO-478. Superposition: if `y₁` solves `L y = f₁` and `y₂` solves `L y = f₂`, then `y₁ + y₂`
solves `L y = f₁ + f₂`. -/
theorem add_mem_solSet {L : Module.End K (ℕ → K)} {f₁ f₂ y₁ y₂ : ℕ → K}
    (h₁ : y₁ ∈ solSet L f₁) (h₂ : y₂ ∈ solSet L f₂) : y₁ + y₂ ∈ solSet L (f₁ + f₂) := by
  simp only [solSet, Set.mem_ofPred_eq] at *
  rw [map_add, h₁, h₂]

end SeqOp

end UndergradKB.Combinatorics.AeqB
