import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import UndergradKB.Common

/-!
# Foundations: generating functions (Levin, Section 6.1)

Levin treats a generating series `a₀ + a₁ x + a₂ x² + ⋯` purely as a bookkeeping device ("we are never
going to plug anything in for `x`"), so the faithful setting is the ring `ℚ⟦X⟧` of formal power series
with rational coefficients. The generating series of a sequence `a` is `PowerSeries.mk a`; a
"generating function" such as `1/(1 - x)` is the inverse in `ℚ⟦X⟧` of a series with nonzero constant
term (`PowerSeries.inv`, available because `ℚ` is a field). Every statement `mk a = f⁻¹` below is
equivalent to `mk a * f = 1` (`PowerSeries.eq_inv_iff_mul_eq_one`), which is how the book checks it
("multiply, shift and subtract").

Rows FO-425..FO-441 of docs/coverage/foundations/checklist.md (wave 3).
-/

namespace UndergradKB.Foundations.GeneratingFunctions

open PowerSeries Finset

/-- The generating series of a sequence: the formal power series whose `n`-th coefficient is `a n`. -/
noncomputable abbrev genSeries (a : ℕ → ℚ) : ℚ⟦X⟧ := PowerSeries.mk a

/-- `1 - c x` has constant term `1`, so it is invertible. -/
theorem constantCoeff_one_sub_C_mul_X (c : ℚ) : constantCoeff (1 - C c * X : ℚ⟦X⟧) ≠ 0 := by
  simp

/-- The basic computation behind all of Section 6.1: `(c⁰ + c¹ x + c² x² + ⋯)(1 - c x) = 1`. -/
theorem mk_pow_mul_one_sub (c : ℚ) : (PowerSeries.mk fun n => c ^ n) * (1 - C c * X) = 1 := by
  ext n
  rcases n with _ | n
  · simp
  · rw [mul_sub, mul_one, map_sub, ← mul_assoc, coeff_succ_mul_X, mul_comm, coeff_C_mul]
    simp [pow_succ, mul_comm]

/-- FO-425. Reading off a generating series: the coefficient of `x^n` in the generating series of
`a` is `a n` (Example 6.1.1: the sequence is read from the coefficients, starting at `a₀`). -/
@[kb "levin2025" "Example 6.1.1, p. 441"]
theorem levin_ex_6_1_1_coeff (a : ℕ → ℚ) (n : ℕ) : coeff n (genSeries a) = a n :=
  coeff_mk n a

/-- FO-425. Two sequences with the same generating series are equal: the generating series keeps
track of which term is which. -/
@[kb "levin2025" "Sec 6.1, p. 442"]
theorem levin_s6_1_genSeries_injective : Function.Injective genSeries := by
  intro a b h
  funext n
  simpa using congrArg (coeff n) h

/-- FO-426. The generating function for `1, 1, 1, 1, …` is `1/(1 - x)`. -/
@[kb "levin2025" "Sec 6.1.1, p. 443"]
theorem levin_s6_1_1_ones : genSeries (fun _ => 1) = (1 - X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one (by simp)]
  exact mk_one_mul_one_sub_eq_one ℚ

/-- FO-427. Substituting `c x` for `x`: `1/(1 - c x)` generates `1, c, c², c³, …`; with `c = -1`
and `c = 3` this is the book's `1/(1+x)` (`1, -1, 1, -1, …`) and `1/(1-3x)` (`1, 3, 9, 27, …`). -/
@[kb "levin2025" "Sec 6.1.1, p. 443"]
theorem levin_s6_1_1_geometric (c : ℚ) : genSeries (fun n => c ^ n) = (1 - C c * X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one (constantCoeff_one_sub_C_mul_X c)]
  exact mk_pow_mul_one_sub c

/-- FO-427, the case `c = -1`: `1/(1 + x)` generates `1, -1, 1, -1, …`. -/
@[kb "levin2025" "Sec 6.1.1, p. 443"]
theorem levin_s6_1_1_alternating : genSeries (fun n => (-1) ^ n) = (1 + X)⁻¹ := by
  rw [levin_s6_1_1_geometric]
  congr 1
  simp [sub_eq_add_neg]

/-- FO-428. Generating series are additive and respect constant multiples: the generating function
of `a + b` is the sum of the generating functions, and that of `k a` is `k` times it (`2/(1-x)`
generates `2, 2, 2, …`; `1/(1-x) + 1/(1-3x)` generates `2, 4, 10, 28, …`). -/
@[kb "levin2025" "Sec 6.1.1, p. 443"]
theorem levin_s6_1_1_add_smul (a b : ℕ → ℚ) (k : ℚ) :
    genSeries (a + b) = genSeries a + genSeries b ∧
      genSeries (fun n => k * a n) = C k * genSeries a := by
  constructor
  · ext n; simp
  · ext n; simp [coeff_C_mul]

/-- FO-428, the book's instance: `1/(1-x) + 1/(1-3x)` generates `3^n + 1`, i.e. `2, 4, 10, 28, 82, …`. -/
@[kb "levin2025" "Sec 6.1.1, p. 443"]
theorem levin_s6_1_1_pow_three_add_one :
    genSeries (fun n => 3 ^ n + 1) = (1 - X)⁻¹ + (1 - C 3 * X)⁻¹ := by
  rw [← levin_s6_1_1_ones, ← levin_s6_1_1_geometric, add_comm]
  ext n; simp

/-- FO-429. Multiplying by `x` shifts a sequence right, putting a `0` in front: the generating
series of `0, a₀, a₁, a₂, …` is `x A`. -/
@[kb "levin2025" "Sec 6.1.1, p. 444"]
theorem levin_s6_1_1_shift (a : ℕ → ℚ) :
    genSeries (fun n => if n = 0 then 0 else a (n - 1)) = X * genSeries a := by
  ext n
  rcases n with _ | n
  · simp
  · rw [mul_comm, coeff_succ_mul_X]; simp

/-- FO-430. Substituting `x²` for `x`: `1/(1 - x²)` generates `1, 0, 1, 0, …` and `x/(1 - x²)`
generates `0, 1, 0, 1, …`; their sum is `1/(1 - x)`. -/
@[kb "levin2025" "Sec 6.1.1, p. 444"]
theorem levin_s6_1_1_even_odd :
    genSeries (fun n => if Even n then 1 else 0) = (1 - X ^ 2)⁻¹ ∧
      genSeries (fun n => if Even n then 0 else 1) = X * (1 - X ^ 2)⁻¹ ∧
      (1 - X ^ 2 : ℚ⟦X⟧)⁻¹ + X * (1 - X ^ 2)⁻¹ = (1 - X)⁻¹ := by
  have hc : constantCoeff (1 - X ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  have he : genSeries (fun n => if Even n then 1 else 0) * (1 - X ^ 2) = 1 := by
    ext n
    rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
    rcases n with _ | _ | n <;> simp [Nat.even_add_one]
  refine ⟨(eq_inv_iff_mul_eq_one hc).2 he, ?_, ?_⟩
  · have h1 : genSeries (fun n => if Even n then 0 else 1) =
        X * genSeries (fun n => if Even n then 1 else 0) := by
      rw [← levin_s6_1_1_shift]
      ext n
      rcases n with _ | n
      · simp
      · by_cases h : Even n <;> simp [h, Nat.even_add_one, ← Nat.not_even_iff_odd]
    rw [h1, (eq_inv_iff_mul_eq_one hc).2 he]
  · rw [← levin_s6_1_1_ones, ← (eq_inv_iff_mul_eq_one hc).2 he]
    ext n
    rcases n with _ | n
    · simp
    · rw [map_add, mul_comm, coeff_succ_mul_X]
      by_cases h : Even n <;> simp [h, Nat.even_add_one]

/-- FO-431. Differentiating `1/(1-x)`: the derivative of the generating function `1/(1-x)` is
`1/(1-x)²`, and differentiating the series `1 + x + x² + ⋯` term by term gives `1 + 2x + 3x² + ⋯`
(the book's argument for the next theorem). -/
@[kb "levin2025" "Sec 6.1.1, p. 444"]
theorem levin_s6_1_1_derivative :
    d⁄dX ((1 - X : ℚ⟦X⟧)⁻¹) = ((1 - X) ^ 2)⁻¹ ∧
      d⁄dX (genSeries fun _ => 1) = genSeries fun n => (n : ℚ) + 1 := by
  constructor
  · rw [derivative_inv', map_sub, derivative_one, derivative_X, PowerSeries.inv_pow]
    ring
  · ext n
    simp [coeff_derivative]

/-- FO-431. The generating function for `1, 2, 3, 4, …` is `1/(1-x)²`. -/
@[kb "levin2025" "Sec 6.1.1, p. 444"]
theorem levin_s6_1_1_naturals : genSeries (fun n => (n : ℚ) + 1) = ((1 - X) ^ 2)⁻¹ := by
  rw [← levin_s6_1_1_derivative.2, levin_s6_1_1_ones, levin_s6_1_1_derivative.1]

/-- FO-432. `1/(1-x)³` generates the triangular numbers `1, 3, 6, 10, …` (the `n`-th coefficient is
`(n+1)(n+2)/2`, the triangular number `T_{n+1}`). -/
@[kb "levin2025" "Sec 6.1.1, p. 444"]
theorem levin_s6_1_1_triangular :
    genSeries (fun n => ((n : ℚ) + 1) * (n + 2) / 2) = ((1 - X) ^ 3)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one (by simp)]
  have h := mk_add_choose_mul_one_sub_pow_eq_one ℚ 2
  convert h using 3
  funext n
  rw [Nat.cast_choose_two]
  push_cast
  field_simp
  ring

/-- FO-433. Differencing: if `A` generates `a₀, a₁, a₂, …` then `(1 - x) A` generates
`a₀, a₁ - a₀, a₂ - a₁, …`, the first term followed by the sequence of differences. -/
@[kb "levin2025" "Sec 6.1.2, p. 445"]
theorem levin_s6_1_2_differencing (a : ℕ → ℚ) :
    (1 - X) * genSeries a = genSeries (fun n => if n = 0 then a 0 else a n - a (n - 1)) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [sub_mul, one_mul, map_sub, mul_comm X, coeff_succ_mul_X]; simp

/-- FO-434 (Example 6.1.2). The odd numbers `1, 3, 5, 7, …` have generating function
`(1 + x)/(1 - x)²`. -/
@[kb "levin2025" "Example 6.1.2, p. 445"]
theorem levin_ex_6_1_2_odds :
    genSeries (fun n => 2 * (n : ℚ) + 1) = (1 + X) * ((1 - X) ^ 2)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp)]
  have h : genSeries (fun n => 2 * (n : ℚ) + 1) =
      2 * genSeries (fun n => (n : ℚ) + 1) - genSeries (fun _ => 1) := by
    ext n; simp [coeff_C_mul, ← map_ofNat C]; ring
  rw [h, levin_s6_1_1_naturals, levin_s6_1_1_ones, sub_mul, mul_assoc,
    PowerSeries.inv_mul_cancel _ (by simp), pow_two, ← mul_assoc,
    PowerSeries.inv_mul_cancel _ (by simp)]
  ring

/-- FO-435 (Example 6.1.3). The squares `1, 4, 9, 16, …` (with `a₀ = 1`) have generating function
`(1 + x)/(1 - x)³`. -/
@[kb "levin2025" "Example 6.1.3, p. 446"]
theorem levin_ex_6_1_3_squares :
    genSeries (fun n => ((n : ℚ) + 1) ^ 2) = (1 + X) * ((1 - X) ^ 3)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq (by simp)]
  -- differencing: `(1 - x) A` generates the odd numbers
  have hd : (1 - X) * genSeries (fun n => ((n : ℚ) + 1) ^ 2) = genSeries (fun n => 2 * (n : ℚ) + 1) := by
    rw [levin_s6_1_2_differencing]
    ext n
    rcases n with _ | n
    · simp
    · simp; ring
  have ho := levin_ex_6_1_2_odds
  rw [eq_mul_inv_iff_mul_eq (by simp)] at ho
  calc genSeries (fun n => ((n : ℚ) + 1) ^ 2) * (1 - X) ^ 3
      = ((1 - X) * genSeries (fun n => ((n : ℚ) + 1) ^ 2)) * (1 - X) ^ 2 := by ring
    _ = 1 + X := by rw [hd, ho]

/-- FO-436. A sequence satisfying a two-term linear recurrence `aₙ = p aₙ₋₁ + q aₙ₋₂` (`n ≥ 2`) has
generating function `A` with `(1 - p x - q x²) A = a₀ + (a₁ - p a₀) x`: all later coefficients
cancel. -/
@[kb "levin2025" "Sec 6.1.2, p. 446"]
theorem levin_s6_1_2_recurrence (a : ℕ → ℚ) (p q : ℚ)
    (h : ∀ n, a (n + 2) = p * a (n + 1) + q * a n) :
    (1 - C p * X - C q * X ^ 2) * genSeries a = C (a 0) + C (a 1 - p * a 0) * X := by
  have e : (1 - C p * X - C q * X ^ 2) * genSeries a =
      genSeries a - C p * (X * genSeries a) - C q * (X ^ 2 * genSeries a) := by ring
  rw [e]
  ext n
  rcases n with _ | _ | n
  · simp
  · simp [coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul']
  · simp [coeff_C_mul, coeff_succ_X_mul, coeff_X_pow_mul']
    linear_combination h n

/-- FO-437 (Example 6.1.4). The sequence `1, 3, 7, 15, 31, …` given by `aₙ = 3aₙ₋₁ - 2aₙ₋₂` with
`a₀ = 1`, `a₁ = 3` has generating function `1/(1 - 3x + 2x²)`. -/
@[kb "levin2025" "Example 6.1.4, p. 446"]
theorem levin_ex_6_1_4_recurrence_gf (a : ℕ → ℚ) (h0 : a 0 = 1) (h1 : a 1 = 3)
    (h : ∀ n, a (n + 2) = 3 * a (n + 1) - 2 * a n) :
    genSeries a = (1 - C 3 * X + C 2 * X ^ 2)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one (by simp)]
  have := levin_s6_1_2_recurrence a 3 (-2) (fun n => by rw [h]; ring)
  rw [h0, h1] at this
  rw [mul_comm]
  convert this using 1
  · simp [sub_eq_add_neg]
  · simp

/-- FO-438. Multiplying generating functions convolves the sequences: the `n`-th coefficient of
`A B` is `a₀ bₙ + a₁ bₙ₋₁ + ⋯ + aₙ b₀`. -/
@[kb "levin2025" "Sec 6.1.3, p. 447"]
theorem levin_s6_1_3_mul (a b : ℕ → ℚ) (n : ℕ) :
    coeff n (genSeries a * genSeries b) = ∑ i ∈ range (n + 1), a i * b (n - i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (mk a) * coeff j (mk b))]
  simp

/-- FO-439 (Example 6.1.5). Multiplying `1, 2, 3, 4, …` by `1, 2, 4, 8, …` gives `1, 4, 11, 26, 57, …`
(the `n`-th term is `2^(n+2) - n - 3`), with generating function `1/((1-x)²(1-2x))`. -/
@[kb "levin2025" "Example 6.1.5, p. 447"]
theorem levin_ex_6_1_5_product :
    (∀ n, ∑ i ∈ range (n + 1), ((i : ℚ) + 1) * 2 ^ (n - i) = 2 ^ (n + 2) - n - 3) ∧
      genSeries (fun n => 2 ^ (n + 2) - n - 3) = ((1 - X) ^ 2 * (1 - C 2 * X))⁻¹ := by
  have hsum : ∀ n, ∑ i ∈ range (n + 1), ((i : ℚ) + 1) * 2 ^ (n - i) = 2 ^ (n + 2) - n - 3 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one]
      have : ∑ i ∈ range (n + 1), ((i : ℚ) + 1) * 2 ^ (n + 1 - i) =
          2 * ∑ i ∈ range (n + 1), ((i : ℚ) + 1) * 2 ^ (n - i) := by
        rw [mul_sum]
        refine sum_congr rfl fun i hi => ?_
        rw [Nat.sub_add_comm (Nat.lt_succ_iff.1 (mem_range.1 hi)), pow_succ]
        ring
      rw [this, ih]
      push_cast
      ring
  refine ⟨hsum, ?_⟩
  rw [PowerSeries.mul_inv_rev, ← levin_s6_1_1_naturals, ← levin_s6_1_1_geometric, mul_comm]
  ext n
  rw [levin_s6_1_3_mul, levin_ex_6_1_1_coeff, hsum]

/-- FO-440. Partial sums: multiplying a generating function by `1/(1-x)` gives the generating
function of the sequence of partial sums `a₀, a₀ + a₁, a₀ + a₁ + a₂, …`. -/
@[kb "levin2025" "Sec 6.1.3, p. 447"]
theorem levin_s6_1_3_partial_sums (a : ℕ → ℚ) :
    (1 - X)⁻¹ * genSeries a = genSeries (fun n => ∑ i ∈ range (n + 1), a i) := by
  rw [← levin_s6_1_1_ones]
  ext n
  rw [levin_s6_1_3_mul, levin_ex_6_1_1_coeff, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have := mem_range.1 hi
  simp only [one_mul]
  congr 1
  omega

/-- FO-441 (Example 6.1.6). Solving `aₙ = 3aₙ₋₁ - 2aₙ₋₂`, `a₀ = 1`, `a₁ = 3` with generating
functions: the partial fraction decomposition `1/((1-x)(1-2x)) = -1/(1-x) + 2/(1-2x)` gives
`aₙ = 2^(n+1) - 1`. -/
@[kb "levin2025" "Example 6.1.6, p. 448"]
theorem levin_ex_6_1_6_solve (a : ℕ → ℚ) (h0 : a 0 = 1) (h1 : a 1 = 3)
    (h : ∀ n, a (n + 2) = 3 * a (n + 1) - 2 * a n) : ∀ n, a n = 2 ^ (n + 1) - 1 := by
  have hA := levin_ex_6_1_4_recurrence_gf a h0 h1 h
  -- factor the denominator and decompose into partial fractions
  have hpf : (1 - C 3 * X + C 2 * X ^ 2 : ℚ⟦X⟧)⁻¹ = C (-1 : ℚ) * (1 - X : ℚ⟦X⟧)⁻¹ + C (2 : ℚ) * (1 - C (2 : ℚ) * X : ℚ⟦X⟧)⁻¹ := by
    rw [inv_eq_iff_mul_eq_one (by simp)]
    have e1 := (PowerSeries.inv_mul_cancel (1 - X : ℚ⟦X⟧) (by simp))
    have e2 := (PowerSeries.inv_mul_cancel (1 - C 2 * X : ℚ⟦X⟧) (by simp))
    have hfac : (1 - C 3 * X + C 2 * X ^ 2 : ℚ⟦X⟧) = (1 - X) * (1 - C 2 * X) := by
      have : (C 3 : ℚ⟦X⟧) = 1 + C 2 := by rw [← map_one C, ← map_add]; norm_num
      rw [this]; ring
    rw [hfac]
    calc (C (-1 : ℚ) * (1 - X : ℚ⟦X⟧)⁻¹ + C (2 : ℚ) * (1 - C (2 : ℚ) * X : ℚ⟦X⟧)⁻¹) *
          ((1 - X) * (1 - C (2 : ℚ) * X))
        = C (-1 : ℚ) * ((1 - X : ℚ⟦X⟧)⁻¹ * (1 - X)) * (1 - C (2 : ℚ) * X)
          + C (2 : ℚ) * ((1 - C (2 : ℚ) * X : ℚ⟦X⟧)⁻¹ * (1 - C (2 : ℚ) * X)) * (1 - X) := by ring
      _ = 1 := by
        have h2 : (C (2 : ℚ) : ℚ⟦X⟧) = 1 + 1 := by rw [← map_one C, ← map_add]; norm_num
        rw [e1, e2, map_neg, map_one, h2]
        ring
  rw [hpf, ← levin_s6_1_1_ones, ← levin_s6_1_1_geometric] at hA
  intro n
  have := congrArg (coeff n) hA
  simp only [map_add, coeff_C_mul, coeff_mk] at this
  rw [this, pow_succ]
  ring

/-- FO-442. The exponential function `e^x` is the generating function of `1, 1, 1/2, 1/6, …, 1/n!, …`. -/
@[kb "levin2025" "Sec 6.1, p. 442"]
theorem levin_s6_1_exp : genSeries (fun n => 1 / (n.factorial : ℚ)) = PowerSeries.exp ℚ := by
  ext n
  simp [coeff_exp]

end UndergradKB.Foundations.GeneratingFunctions
