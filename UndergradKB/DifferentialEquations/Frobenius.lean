import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import UndergradKB.Common.Attr
import UndergradKB.DifferentialEquations.OrdinaryPoints

/-! # Method of Frobenius for polynomial coefficients (Lebl, *Notes on Diffy Qs*, §7.3)

For `x² y'' + x p(x) y' + q(x) y = 0` with real polynomials `p`, `q`, the indicial polynomial is
`F(t) = t (t-1) + p(0) t + q(0)`.  For a real root `r` of `F` with `F(r+k) ≠ 0` for all integers `k ≥ 1`, the
coefficients `a₀ = 1`, `a_k F(r+k) = -∑_{j<k} a_j ((r+j) p_{k-j} + q_{k-j})` are bounded (so the series
`S(x) = ∑ a_k x^k` converges for `|x| < 1`) and `y = x^r S(x)` solves the equation on `0 < x < 1`.
For two real roots not differing by an integer both roots give solutions.
-/

namespace UndergradKB.DifferentialEquations

open Polynomial Filter Topology Finset

/-- The indicial polynomial `F(t) = t (t-1) + p(0) t + q(0)` of `x² y'' + x p y' + q y = 0`. -/
noncomputable def indF (p q : ℝ[X]) (t : ℝ) : ℝ := t * (t - 1) + p.coeff 0 * t + q.coeff 0

/-- A bound `N` for the degrees of `p` and `q`. -/
noncomputable def frobN (p q : ℝ[X]) : ℕ := max p.natDegree q.natDegree

set_option linter.unusedVariables false in
/-- The Frobenius coefficients for the exponent `r`: `a₀ = 1` and
`a_k = - (∑_{i=1}^{N} a_{k-i} ((r+k-i) p_i + q_i)) / F(r+k)` (terms with `i > k` omitted). -/
noncomputable def frobCoef (p q : ℝ[X]) (r : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else
    -(∑ i ∈ range (frobN p q), if h : i + 1 ≤ k then
        frobCoef p q r (k - (i + 1)) * ((r + ((k - (i + 1) : ℕ) : ℝ)) * p.coeff (i + 1) + q.coeff (i + 1))
      else 0) / indF p q (r + k)
termination_by k
decreasing_by omega

/-- The right-hand side of the recurrence, for a sequence `a`. -/
noncomputable def frobTail (p q : ℝ[X]) (r : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (frobN p q),
    if i + 1 ≤ k then a (k - (i + 1)) * ((r + ((k - (i + 1) : ℕ) : ℝ)) * p.coeff (i + 1) + q.coeff (i + 1))
    else 0

lemma frobCoef_zero (p q : ℝ[X]) (r : ℝ) : frobCoef p q r 0 = 1 := by
  rw [frobCoef]; simp

lemma frobCoef_rec (p q : ℝ[X]) (r : ℝ) {k : ℕ} (hk : k ≠ 0) (hF : indF p q (r + k) ≠ 0) :
    frobCoef p q r k * indF p q (r + k) = - frobTail p q r (frobCoef p q r) k := by
  have h : frobCoef p q r k = -(frobTail p q r (frobCoef p q r) k) / indF p q (r + k) := by
    rw [frobCoef]
    simp only [hk, ↓reduceIte, frobTail, dite_eq_ite]
  rw [h, div_mul_cancel₀ _ hF]

/-- Coefficient bound `B`. -/
noncomputable def frobB (p q : ℝ[X]) : ℝ :=
  ∑ i ∈ range (frobN p q + 1), (|p.coeff i| + |q.coeff i|)

lemma frobB_nonneg (p q : ℝ[X]) : 0 ≤ frobB p q := Finset.sum_nonneg fun i _ => by positivity

lemma frobTail_le (p q : ℝ[X]) (r : ℝ) (a : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) {k : ℕ} (hk : 1 ≤ k)
    (ha : ∀ j < k, |a j| ≤ A) :
    |frobTail p q r a k| ≤ frobN p q * (A * ((|r| + k) * frobB p q)) := by
  unfold frobTail
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (A * ((|r| + k) * frobB p q)) fun i hi => ?_).trans (by simp)
  have hi' : i < frobN p q := Finset.mem_range.mp hi
  have hB := frobB_nonneg p q
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  split_ifs with h
  · rw [abs_mul]
    have h1 : |a (k - (i + 1))| ≤ A := ha _ (by omega)
    have hj : ((k - (i + 1) : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le _ _
    have hj0 : (0 : ℝ) ≤ ((k - (i + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : |(r + ((k - (i + 1) : ℕ) : ℝ)) * p.coeff (i + 1) + q.coeff (i + 1)| ≤
        (|r| + k) * frobB p q := by
      have hs : |p.coeff (i + 1)| + |q.coeff (i + 1)| ≤ frobB p q :=
        Finset.single_le_sum (f := fun i => |p.coeff i| + |q.coeff i|) (fun _ _ => by positivity)
          (Finset.mem_range.mpr (by omega))
      have hr : |r + ((k - (i + 1) : ℕ) : ℝ)| ≤ |r| + k :=
        (abs_add_le _ _).trans (by rw [abs_of_nonneg hj0]; linarith)
      calc _ ≤ |(r + ((k - (i + 1) : ℕ) : ℝ)) * p.coeff (i + 1)| + |q.coeff (i + 1)| := abs_add_le _ _
        _ = |r + ((k - (i + 1) : ℕ) : ℝ)| * |p.coeff (i + 1)| + |q.coeff (i + 1)| := by rw [abs_mul]
        _ ≤ (|r| + k) * |p.coeff (i + 1)| + (|r| + k) * |q.coeff (i + 1)| := by
            gcongr
            nlinarith [abs_nonneg r, abs_nonneg (q.coeff (i + 1))]
        _ = (|r| + k) * (|p.coeff (i + 1)| + |q.coeff (i + 1)|) := by ring
        _ ≤ _ := by gcongr
    exact mul_le_mul h1 h2 (abs_nonneg _) hA
  · rw [abs_zero]; positivity

/-- For a root `r` of `F`: `F(r+k) = k (k + 2r - 1 + p(0))`. -/
lemma indF_shift (p q : ℝ[X]) {r : ℝ} (hr : indF p q r = 0) (k : ℕ) :
    indF p q (r + k) = k * (k + (2 * r - 1 + p.coeff 0)) := by
  unfold indF at *
  linear_combination hr

/-- **Majorant estimate**: the Frobenius coefficients are bounded. -/
theorem frobCoef_bounded (p q : ℝ[X]) {r : ℝ} (hr : indF p q r = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → indF p q (r + k) ≠ 0) : ∃ A : ℝ, 0 ≤ A ∧ ∀ k, |frobCoef p q r k| ≤ A := by
  set s : ℝ := 2 * r - 1 + p.coeff 0 with hs
  set B := frobB p q with hB
  obtain ⟨K, hK⟩ := exists_nat_ge (|s| + 2 * (frobN p q * B) + |r| + 1)
  have hB0 := frobB_nonneg p q
  have hN0 : (0 : ℝ) ≤ frobN p q := Nat.cast_nonneg _
  have hNB : 0 ≤ (frobN p q : ℝ) * B := mul_nonneg hN0 hB0
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := by
      have := abs_nonneg s; have := abs_nonneg r; linarith
    exact_mod_cast this
  set A : ℝ := ∑ j ∈ range (K + 1), |frobCoef p q r j| with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨A, hA0, fun k => ?_⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hkK : k ≤ K
    · exact Finset.single_le_sum (f := fun j => |frobCoef p q r j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    · rw [not_le] at hkK
      have hk0 : k ≠ 0 := by omega
      have hkR : (K : ℝ) + 1 ≤ k := by exact_mod_cast hkK
      have hF' := hF k (by omega)
      have hrec := frobCoef_rec p q r hk0 hF'
      have hT := frobTail_le p q r (frobCoef p q r) hA0 (by omega) ih
      have hpos : 0 < |indF p q (r + k)| := abs_pos.mpr hF'
      -- lower bound for |F(r+k)|
      have hlow : (frobN p q : ℝ) * (A * ((|r| + k) * B)) ≤ A * |indF p q (r + k)| := by
        have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        have hs0 := abs_nonneg s
        have hr0 := abs_nonneg r
        have hsk : |s| + 2 * (frobN p q * B) + |r| + 1 ≤ k := by
          have := abs_nonneg r; have := abs_nonneg s; linarith
        have h1 : (k : ℝ) - |s| ≤ |(k : ℝ) + s| := by
          have := abs_sub_abs_le_abs_sub (k : ℝ) (-s)
          rw [abs_neg, sub_neg_eq_add, abs_of_nonneg hk'] at this
          exact this
        have h2 : |indF p q (r + k)| = k * |(k : ℝ) + s| := by
          rw [indF_shift p q hr, abs_mul, abs_of_nonneg hk']
        have h3 : (frobN p q : ℝ) * B * (|r| + k) ≤ |indF p q (r + k)| := by
          rw [h2]
          have : |r| ≤ k := by linarith
          have h4 : 2 * (frobN p q * B) ≤ |(k : ℝ) + s| := by linarith
          calc (frobN p q : ℝ) * B * (|r| + k) ≤ (frobN p q * B) * (k + k) := by gcongr
            _ = (2 * (frobN p q * B)) * k := by ring
            _ ≤ |(k : ℝ) + s| * k := by gcongr
            _ = _ := by ring
        calc (frobN p q : ℝ) * (A * ((|r| + k) * B)) = A * ((frobN p q : ℝ) * B * (|r| + k)) := by ring
          _ ≤ _ := by gcongr
      have h5 : |frobCoef p q r k| * |indF p q (r + k)| ≤ A * |indF p q (r + k)| := by
        rw [← abs_mul, hrec, abs_neg]
        exact hT.trans hlow
      exact le_of_mul_le_mul_right h5 hpos

/-! ### Power series with bounded coefficients on `|x| < 1` -/

/-- The series `∑ a_k x^k`. -/
noncomputable def fS0 (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, a k * x ^ k

/-- Its termwise derivative. -/
noncomputable def fS1 (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k, a k * ((k : ℝ) * x ^ (k - 1))

/-- Its termwise second derivative. -/
noncomputable def fS2 (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k, a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)))

section Bounds

variable {a : ℕ → ℝ} {A : ℝ}

lemma fb0 (hA : ∀ k, |a k| ≤ A) {y ρ : ℝ} (hy : |y| ≤ ρ) (k : ℕ) :
    ‖a k * y ^ k‖ ≤ A * ρ ^ k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (hA k) (pow_le_pow_left₀ (abs_nonneg _) hy k) (by positivity)
    ((abs_nonneg _).trans (hA k))

lemma fb1 (hA : ∀ k, |a k| ≤ A) {y ρ : ℝ} (hρ : 0 < ρ) (hy : |y| ≤ ρ) (k : ℕ) :
    ‖a k * ((k : ℝ) * y ^ (k - 1))‖ ≤ A / ρ * ((k : ℝ) * ρ ^ k) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  cases k with
  | zero => simp
  | succ j =>
    have e : A / ρ * (((j + 1 : ℕ) : ℝ) * ρ ^ (j + 1)) = A * (((j + 1 : ℕ) : ℝ) * ρ ^ j) := by
      rw [pow_succ]; field_simp
    rw [e]
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, Nat.add_sub_cancel]
    exact mul_le_mul (hA _) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy j)
      (Nat.cast_nonneg _)) (by positivity) hA0

lemma fb2 (hA : ∀ k, |a k| ≤ A) {y ρ : ℝ} (hρ : 0 < ρ) (hy : |y| ≤ ρ) (k : ℕ) :
    ‖a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * y ^ (k - 1 - 1)))‖ ≤ A / ρ ^ 2 * ((k : ℝ) ^ 2 * ρ ^ k) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  rcases k with _ | _ | i
  · simp
  · simp; positivity
  · have e : A / ρ ^ 2 * (((i + 1 + 1 : ℕ) : ℝ) ^ 2 * ρ ^ (i + 1 + 1)) =
        A * (((i + 1 + 1 : ℕ) : ℝ) ^ 2 * ρ ^ i) := by
      field_simp; ring
    rw [e]
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, Nat.add_sub_cancel]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hyp : |y| ^ i ≤ ρ ^ i := pow_le_pow_left₀ (abs_nonneg _) hy i
    have hyp0 : 0 ≤ |y| ^ i := by positivity
    have h1 : ((i + 1 + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * |y| ^ i) ≤
        ((i + 1 + 1 : ℕ) : ℝ) ^ 2 * ρ ^ i := by
      push_cast
      have : ((i : ℝ) + 1) * |y| ^ i ≤ ((i : ℝ) + 1 + 1) * ρ ^ i :=
        mul_le_mul (by linarith) hyp hyp0 (by linarith)
      calc ((i : ℝ) + 1 + 1) * (((i : ℝ) + 1) * |y| ^ i) ≤ ((i : ℝ) + 1 + 1) * (((i : ℝ) + 1 + 1) * ρ ^ i) :=
            mul_le_mul_of_nonneg_left this (by linarith)
        _ = _ := by ring
    exact mul_le_mul (hA _) h1 (by positivity) hA0

lemma geo_summable {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (m : ℕ) :
    Summable fun k : ℕ => (k : ℝ) ^ m * ρ ^ k :=
  summable_pow_mul_geometric_of_norm_lt_one m (by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0])

lemma fsum0 (hA : ∀ k, |a k| ≤ A) {y ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hy : |y| ≤ ρ) :
    Summable fun k => a k * y ^ k :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ).mul_left A) (fb0 hA hy)

lemma fsum1 (hA : ∀ k, |a k| ≤ A) {y ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1) (hy : |y| ≤ ρ) :
    Summable fun k => a k * ((k : ℝ) * y ^ (k - 1)) := by
  have := (geo_summable hρ0.le hρ 1).mul_left (A / ρ)
  simp only [pow_one] at this
  exact Summable.of_norm_bounded this (fb1 hA hρ0 hy)

lemma fsum2 (hA : ∀ k, |a k| ≤ A) {y ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1) (hy : |y| ≤ ρ) :
    Summable fun k => a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * y ^ (k - 1 - 1))) :=
  Summable.of_norm_bounded ((geo_summable hρ0.le hρ 2).mul_left (A / ρ ^ 2)) (fb2 hA hρ0 hy)

lemma exists_rho {x : ℝ} (hx : |x| < 1) : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ |x| < ρ :=
  ⟨(1 + |x|) / 2, by positivity, by linarith, by linarith⟩

theorem hasDerivAt_fS0 (hA : ∀ k, |a k| ≤ A) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fS0 a) (fS1 a x) x := by
  obtain ⟨ρ, hρ0, hρ, hxρ⟩ := exists_rho hx
  have hmem : x ∈ Metric.ball (0 : ℝ) ρ := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; exact hxρ
  have hu := (geo_summable hρ0.le hρ 1).mul_left (A / ρ)
  simp only [pow_one] at hu
  exact hasDerivAt_tsum_of_isPreconnected (g := fun n z => a n * z ^ n)
    (g' := fun n z => a n * ((n : ℝ) * z ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) _).isPreconnected
    (fun n z _ => (hasDerivAt_pow n z).const_mul (a n))
    (fun n z hz => fb1 hA hρ0 (by rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz; exact hz.le) n)
    hmem (fsum0 hA hρ0.le hρ hxρ.le) hmem

theorem hasDerivAt_fS1 (hA : ∀ k, |a k| ≤ A) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fS1 a) (fS2 a x) x := by
  obtain ⟨ρ, hρ0, hρ, hxρ⟩ := exists_rho hx
  have hmem : x ∈ Metric.ball (0 : ℝ) ρ := by
    rw [mem_ball_zero_iff, Real.norm_eq_abs]; exact hxρ
  exact hasDerivAt_tsum_of_isPreconnected (g := fun n z => a n * ((n : ℝ) * z ^ (n - 1)))
    (g' := fun n z => a n * ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * z ^ (n - 1 - 1))))
    ((geo_summable hρ0.le hρ 2).mul_left (A / ρ ^ 2)) Metric.isOpen_ball
    (convex_ball (0 : ℝ) _).isPreconnected
    (fun n z _ => ((hasDerivAt_pow (n - 1) z).const_mul (n : ℝ)).const_mul (a n))
    (fun n z hz => fb2 hA hρ0 (by rw [mem_ball_zero_iff, Real.norm_eq_abs] at hz; exact hz.le) n)
    hmem (fsum1 hA hρ0 hρ hxρ.le) hmem

lemma fS0_zero (a : ℕ → ℝ) : fS0 a 0 = a 0 := by
  unfold fS0
  rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
  simp

end Bounds

/-! ### Multiplication by a polynomial, and the coefficient identity -/

lemma poly_shift (c : ℕ → ℝ) (x : ℝ) (hc : Summable fun j => c j * x ^ j) (i : ℕ) :
    Summable (fun m => (if i ≤ m then c (m - i) else 0) * x ^ m) ∧
      ∑' m, (if i ≤ m then c (m - i) else 0) * x ^ m = x ^ i * ∑' j, c j * x ^ j := by
  have hf : ∀ j : ℕ, (if i ≤ j + i then c (j + i - i) else 0) * x ^ (j + i) = c j * x ^ j * x ^ i := by
    intro j; simp [pow_add]; ring
  have hs : Summable fun m => (if i ≤ m then c (m - i) else 0) * x ^ m := by
    rw [← summable_nat_add_iff i]
    simp only [hf]
    exact hc.mul_right _
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add i]
  have h0 : ∑ m ∈ range i, (if i ≤ m then c (m - i) else 0) * x ^ m = 0 :=
    Finset.sum_eq_zero fun m hm => by
      have : ¬ i ≤ m := by have := Finset.mem_range.mp hm; omega
      simp [this]
  rw [h0, zero_add]
  simp only [hf]
  rw [tsum_mul_right, mul_comm]

lemma poly_mul_tsum (P : ℝ[X]) (N : ℕ) (hN : P.natDegree < N) (c : ℕ → ℝ) (x : ℝ)
    (hc : Summable fun j => c j * x ^ j) :
    Summable (fun m => (∑ i ∈ range N, if i ≤ m then P.coeff i * c (m - i) else 0) * x ^ m) ∧
      P.eval x * ∑' j, c j * x ^ j =
        ∑' m, (∑ i ∈ range N, if i ≤ m then P.coeff i * c (m - i) else 0) * x ^ m := by
  have hcs : ∀ i ∈ range N, Summable (fun m => P.coeff i * ((if i ≤ m then c (m - i) else 0) * x ^ m)) :=
    fun i _ => (poly_shift c x hc i).1.mul_left _
  have hform : (fun m => (∑ i ∈ range N, if i ≤ m then P.coeff i * c (m - i) else 0) * x ^ m) =
      fun m => ∑ i ∈ range N, P.coeff i * ((if i ≤ m then c (m - i) else 0) * x ^ m) := by
    funext m
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_assoc]
  rw [hform]
  refine ⟨summable_sum hcs, ?_⟩
  rw [Summable.tsum_finsetSum hcs, eval_eq_sum_range' hN x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, (poly_shift c x hc i).2]
  ring

/-- The coefficient identity: the Frobenius recurrence says that the coefficient of `x^(r+m)` in the
equation vanishes. -/
lemma frobCoef_identity (p q : ℝ[X]) {r : ℝ} (hr : indF p q r = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → indF p q (r + k) ≠ 0) (m : ℕ) :
    frobCoef p q r m * ((r + m) * (r + m - 1)) +
      ∑ i ∈ range (frobN p q + 1),
        (if i ≤ m then frobCoef p q r (m - i) *
          ((r + ((m - i : ℕ) : ℝ)) * p.coeff i + q.coeff i) else 0) = 0 := by
  rw [Finset.sum_range_succ']
  have hT : ∑ i ∈ range (frobN p q),
      (if i + 1 ≤ m then frobCoef p q r (m - (i + 1)) *
        ((r + ((m - (i + 1) : ℕ) : ℝ)) * p.coeff (i + 1) + q.coeff (i + 1)) else 0) =
      frobTail p q r (frobCoef p q r) m := rfl
  rw [hT]
  simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  by_cases hm : m = 0
  · subst hm
    have : frobTail p q r (frobCoef p q r) 0 = 0 := by
      unfold frobTail
      exact Finset.sum_eq_zero fun i _ => by simp
    rw [this, frobCoef_zero]
    unfold indF at hr
    simp
    linear_combination hr
  · have hrec := frobCoef_rec p q r hm (hF m (Nat.one_le_iff_ne_zero.mpr hm))
    unfold indF at hrec
    linear_combination hrec

/-! ### The differential equation for the series -/

lemma frob_series_eq (p q : ℝ[X]) {r : ℝ} {a : ℕ → ℝ} {A : ℝ} (hA : ∀ k, |a k| ≤ A)
    (hcoef : ∀ m : ℕ, a m * ((r + m) * (r + m - 1)) +
      ∑ i ∈ range (frobN p q + 1),
        (if i ≤ m then a (m - i) * ((r + ((m - i : ℕ) : ℝ)) * p.coeff i + q.coeff i) else 0) = 0)
    {x : ℝ} (hx : |x| < 1) :
    x ^ 2 * fS2 a x + (2 * r + p.eval x) * (x * fS1 a x) +
      (r * (r - 1) + r * p.eval x + q.eval x) * fS0 a x = 0 := by
  obtain ⟨ρ, hρ0, hρ, hxρ⟩ := exists_rho hx
  have s0 := fsum0 hA hρ0.le hρ hxρ.le
  have s1 := fsum1 hA hρ0 hρ hxρ.le
  have s2 := fsum2 hA hρ0 hρ hxρ.le
  -- pointwise identities
  have E1 : ∀ k : ℕ, x ^ 2 * (a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)))) +
      2 * r * (x * (a k * ((k : ℝ) * x ^ (k - 1)))) + r * (r - 1) * (a k * x ^ k) =
      a k * ((r + k) * (r + k - 1)) * x ^ k := by
    intro k
    rcases k with _ | _ | k
    · simp; ring
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ, pow_succ]
      ring
  have E2 : ∀ k : ℕ, r * (a k * x ^ k) + x * (a k * ((k : ℝ) * x ^ (k - 1))) =
      (a k * (r + k)) * x ^ k := by
    intro k
    rcases k with _ | k
    · simp; ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      ring
  have HU := ((s2.hasSum.mul_left (x ^ 2)).add ((s1.hasSum.mul_left x).mul_left (2 * r))).add
    (s0.hasSum.mul_left (r * (r - 1)))
  have HU' : HasSum (fun k : ℕ => a k * ((r + k) * (r + k - 1)) * x ^ k)
      (x ^ 2 * fS2 a x + 2 * r * (x * fS1 a x) + r * (r - 1) * fS0 a x) := by
    have : (fun k : ℕ => a k * ((r + k) * (r + k - 1)) * x ^ k) = fun k : ℕ =>
        x ^ 2 * (a k * ((k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)))) +
          2 * r * (x * (a k * ((k : ℝ) * x ^ (k - 1)))) + r * (r - 1) * (a k * x ^ k) :=
      funext fun k => (E1 k).symm
    rw [this]
    exact HU
  have HP := (s0.hasSum.mul_left r).add (s1.hasSum.mul_left x)
  have HP' : HasSum (fun k : ℕ => (a k * (r + k)) * x ^ k) (r * fS0 a x + x * fS1 a x) := by
    have : (fun k : ℕ => (a k * (r + k)) * x ^ k) = fun k : ℕ =>
        r * (a k * x ^ k) + x * (a k * ((k : ℝ) * x ^ (k - 1))) := funext fun k => (E2 k).symm
    rw [this]
    exact HP
  have hNp : p.natDegree < frobN p q + 1 := Nat.lt_succ_of_le (le_max_left _ _)
  have hNq : q.natDegree < frobN p q + 1 := Nat.lt_succ_of_le (le_max_right _ _)
  obtain ⟨hsp, hep⟩ := poly_mul_tsum p (frobN p q + 1) hNp (fun j => a j * (r + j)) x HP'.summable
  obtain ⟨hsq, heq⟩ := poly_mul_tsum q (frobN p q + 1) hNq a x s0
  rw [HP'.tsum_eq] at hep
  have Hp := hsp.hasSum
  rw [← hep] at Hp
  have Hq := hsq.hasSum
  rw [← heq] at Hq
  have Htot := (HU'.add Hp).add Hq
  have hz : (fun m : ℕ => a m * ((r + m) * (r + m - 1)) * x ^ m +
      (∑ i ∈ range (frobN p q + 1),
        if i ≤ m then p.coeff i * (fun j => a j * (r + j)) (m - i) else 0) * x ^ m +
      (∑ i ∈ range (frobN p q + 1), if i ≤ m then q.coeff i * a (m - i) else 0) * x ^ m) =
      fun _ => 0 := by
    funext m
    have h := hcoef m
    have hc : (∑ i ∈ range (frobN p q + 1),
        if i ≤ m then p.coeff i * (fun j => a j * (r + j)) (m - i) else 0) +
        (∑ i ∈ range (frobN p q + 1), if i ≤ m then q.coeff i * a (m - i) else 0) =
        ∑ i ∈ range (frobN p q + 1),
          (if i ≤ m then a (m - i) * ((r + ((m - i : ℕ) : ℝ)) * p.coeff i + q.coeff i) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp; ring
    calc _ = (a m * ((r + m) * (r + m - 1)) + ((∑ i ∈ range (frobN p q + 1),
        if i ≤ m then p.coeff i * (fun j => a j * (r + j)) (m - i) else 0) +
        (∑ i ∈ range (frobN p q + 1), if i ≤ m then q.coeff i * a (m - i) else 0))) * x ^ m := by ring
      _ = 0 := by rw [hc, h, zero_mul]
  rw [hz] at Htot
  have h0 := Htot.unique hasSum_zero
  unfold fS0 at *
  linear_combination h0

/-! ### The Frobenius solution `x^r S(x)` -/

/-- `x ↦ x^r ∑ a_k x^k`. -/
noncomputable def frobY (a : ℕ → ℝ) (r : ℝ) (x : ℝ) : ℝ := x ^ r * fS0 a x

lemma hasDerivAt_rpow_div (r x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ r) (r * x ^ r / x) x := by
  have h := Real.hasDerivAt_rpow_const (p := r) (x := x) (Or.inl hx.ne')
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hx.ne']
  field_simp

lemma hasDerivAt_rpow_div2 (r x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => r * y ^ r / y) (r * (r - 1) * x ^ r / x ^ 2) x := by
  have h := ((hasDerivAt_rpow_div r x hx).const_mul r).div (hasDerivAt_id x) hx.ne'
  have h' : HasDerivAt (fun y : ℝ => r * y ^ r / y)
      ((r * (r * x ^ r / x) * x - r * x ^ r * 1) / x ^ 2) x := h
  refine h'.congr_deriv ?_
  field_simp

/-- Explicit first derivative of `frobY`. -/
noncomputable def frobY1 (a : ℕ → ℝ) (r x : ℝ) : ℝ :=
  r * x ^ r / x * fS0 a x + x ^ r * fS1 a x

/-- Explicit second derivative of `frobY`. -/
noncomputable def frobY2 (a : ℕ → ℝ) (r x : ℝ) : ℝ :=
  r * (r - 1) * x ^ r / x ^ 2 * fS0 a x + r * x ^ r / x * fS1 a x +
    (r * x ^ r / x * fS1 a x + x ^ r * fS2 a x)

theorem frob_ode (p q : ℝ[X]) {r : ℝ} {a : ℕ → ℝ} {A : ℝ} (hA : ∀ k, |a k| ≤ A)
    (hcoef : ∀ m : ℕ, a m * ((r + m) * (r + m - 1)) +
      ∑ i ∈ range (frobN p q + 1),
        (if i ≤ m then a (m - i) * ((r + ((m - i : ℕ) : ℝ)) * p.coeff i + q.coeff i) else 0) = 0)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ 2 * deriv (deriv (frobY a r)) x + x * p.eval x * deriv (frobY a r) x +
      q.eval x * frobY a r x = 0 := by
  have hab : ∀ z : ℝ, 0 < z → z < 1 → |z| < 1 := fun z h0 h1 => by rw [abs_of_pos h0]; exact h1
  have hd1 : ∀ z : ℝ, 0 < z → z < 1 → HasDerivAt (frobY a r) (frobY1 a r z) z := fun z h0 h1 =>
    (hasDerivAt_rpow_div r z h0).mul (hasDerivAt_fS0 hA (hab z h0 h1))
  have hd1' : deriv (frobY a r) =ᶠ[𝓝 x] frobY1 a r := by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with z hz using (hd1 z hz.1 hz.2).deriv
  have hd2 : HasDerivAt (frobY1 a r) (frobY2 a r x) x :=
    ((hasDerivAt_rpow_div2 r x hx0).mul (hasDerivAt_fS0 hA (hab x hx0 hx1))).add
      ((hasDerivAt_rpow_div r x hx0).mul (hasDerivAt_fS1 hA (hab x hx0 hx1)))
  rw [hd1'.deriv_eq, hd2.deriv, (hd1 x hx0 hx1).deriv]
  have E := frob_series_eq p q hA hcoef (hab x hx0 hx1)
  unfold frobY1 frobY2 frobY
  have key : ∀ S S1 S2 u : ℝ,
      x ^ 2 * S2 + (2 * r + p.eval x) * (x * S1) + (r * (r - 1) + r * p.eval x + q.eval x) * S = 0 →
      x ^ 2 * (r * (r - 1) * u / x ^ 2 * S + r * u / x * S1 + (r * u / x * S1 + u * S2)) +
        x * p.eval x * (r * u / x * S + u * S1) + q.eval x * (u * S) = 0 := by
    intro S S1 S2 u h
    have hx : x ≠ 0 := hx0.ne'
    have : x ^ 2 * (r * (r - 1) * u / x ^ 2 * S + r * u / x * S1 + (r * u / x * S1 + u * S2)) +
        x * p.eval x * (r * u / x * S + u * S1) + q.eval x * (u * S) =
        u * (x ^ 2 * S2 + (2 * r + p.eval x) * (x * S1) +
          (r * (r - 1) + r * p.eval x + q.eval x) * S) := by
      field_simp
      ring
    rw [this, h, mul_zero]
  exact key _ _ _ _ E

/-- The conclusion of the method of Frobenius for the exponent `r`: a coefficient sequence `a` with
`a₀ = 1`, bounded (so `∑ a_k x^k` converges for `|x| < 1`), satisfying the recurrence
`a_k F(r+k) = -∑_{i=1}^{N} a_{k-i} ((r+k-i) p_i + q_i)` (`N` the larger degree, the sum over `j = k - i`
being the book's `∑_{j<k} a_j ((r+j) p_{k-j} + q_{k-j})`), such that `y(x) = x^r ∑ a_k x^k` solves
`x² y'' + x p(x) y' + q(x) y = 0` on `0 < x < 1` and is not identically zero. -/
def HasFrobeniusSolution (p q : ℝ[X]) (r : ℝ) : Prop :=
  ∃ a : ℕ → ℝ, a 0 = 1 ∧ (∃ C : ℝ, ∀ k, |a k| ≤ C) ∧
    (∀ k : ℕ, 1 ≤ k → a k * indF p q (r + k) = - frobTail p q r a k) ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      x ^ 2 * deriv (deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k)) x +
        x * p.eval x * deriv (fun t : ℝ => t ^ r * ∑' k, a k * t ^ k) x +
        q.eval x * (x ^ r * ∑' k, a k * x ^ k) = 0) ∧
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x ^ r * ∑' k, a k * x ^ k ≠ 0

/-- **Method of Frobenius** (Lebl, Theorem 7.3.1; DE-207), for polynomial coefficients.  For the equation
`x² y'' + x p(x) y' + q(x) y = 0` (a regular singular point at `0`, indicial polynomial
`F(t) = t(t-1) + p(0) t + q(0)`; see `frob_regularSingPt`) and a real root `r` of `F` such that
`F(r+k) ≠ 0` for all integers `k ≥ 1` (e.g. the larger real root), there is a Frobenius-type solution
`y = x^r ∑ a_k x^k`, `a₀ = 1`, with bounded coefficients, on `0 < x < 1`.  Only the special case of
polynomial `p`, `q` is proved, and the radius of convergence obtained is at least `1` (the true radius is
infinite). -/
@[kb "lebldiffyqs2026" "Theorem 7.3.1, p. 345"]
theorem frobenius_exists (p q : ℝ[X]) {r : ℝ} (hr : indF p q r = 0)
    (hF : ∀ k : ℕ, 1 ≤ k → indF p q (r + k) ≠ 0) : HasFrobeniusSolution p q r := by
  obtain ⟨A, hA0, hA⟩ := frobCoef_bounded p q hr hF
  have hcoef := frobCoef_identity p q hr hF
  refine ⟨frobCoef p q r, frobCoef_zero p q r, ⟨A, hA⟩,
    fun k hk => frobCoef_rec p q r (by omega) (hF k hk), fun x hx0 hx1 => ?_, ?_⟩
  · exact frob_ode p q hA hcoef hx0 hx1
  · have hc := (hasDerivAt_fS0 hA (by simp : |(0 : ℝ)| < 1)).continuousAt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
    set z : ℝ := min (δ / 2) (1 / 2) with hz
    have hz0 : 0 < z := lt_min (by positivity) (by norm_num)
    have hz1 : z < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hzδ : dist z 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hz0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h1 := hδ' hzδ
    rw [Real.dist_eq, fS0_zero, frobCoef_zero] at h1
    have hne : fS0 (frobCoef p q r) z ≠ 0 := by
      intro h0
      rw [h0] at h1
      norm_num [abs_of_neg] at h1
    exact ⟨z, hz0, hz1, mul_ne_zero (Real.rpow_pos_of_pos hz0 r).ne' hne⟩

/-- `F(t) = (t - r₁)(t - r₂)` when `r₁ ≠ r₂` are both roots of `F`. -/
lemma indF_factor (p q : ℝ[X]) {r₁ r₂ : ℝ} (h : r₁ ≠ r₂) (h1 : indF p q r₁ = 0) (h2 : indF p q r₂ = 0)
    (t : ℝ) : indF p q t = (t - r₁) * (t - r₂) := by
  unfold indF at *
  have hm : (r₁ - r₂) * (r₁ + r₂ + p.coeff 0 - 1) = 0 := by linear_combination h1 - h2
  have hs : r₁ + r₂ + p.coeff 0 - 1 = 0 := by
    rcases mul_eq_zero.mp hm with h' | h'
    · exact absurd (sub_eq_zero.mp h') h
    · exact h'
  linear_combination (t - r₁) * hs + h1

/-- **Frobenius, distinct roots not differing by an integer** (Lebl §7.3.2, the first case; DE-208): if the
indicial polynomial has two real roots `r₁ > r₂` with `r₁ - r₂` not an integer, then each root gives a
Frobenius solution `x^{r_i} ∑ a_k x^k` (the equation here has polynomial coefficients).  The other cases
(double root, integer difference, complex roots) with their logarithmic terms are not formalized. -/
@[kb "lebldiffyqs2026" "§7.3.2 Frobenius cases (i)-(vi), p. 346"]
theorem frobenius_two_roots (p q : ℝ[X]) {r₁ r₂ : ℝ} (hlt : r₂ < r₁) (h1 : indF p q r₁ = 0)
    (h2 : indF p q r₂ = 0) (hint : ∀ n : ℤ, r₁ - r₂ ≠ n) :
    HasFrobeniusSolution p q r₁ ∧ HasFrobeniusSolution p q r₂ := by
  have hfac := indF_factor p q hlt.ne' h1 h2
  constructor
  · refine frobenius_exists p q h1 fun k hk => ?_
    rw [hfac]
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (r₁ + k - r₁) * (r₁ + k - r₂) ≠ 0 := by
      refine mul_ne_zero (by linarith) ?_
      intro h; linarith
    exact this
  · refine frobenius_exists p q h2 fun k hk => ?_
    rw [hfac]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    refine mul_ne_zero (fun h => ?_) (by linarith)
    exact hint k (by push_cast; linarith)

/-- The equation `x² y'' + x p(x) y' + q(x) y = 0` has a regular singular point at `0`. -/
lemma frob_regularSingPt (p q : ℝ[X]) : IsRegularSingPt (X ^ 2) (X * p) q 0 := by
  refine ⟨by simp [IsSingularPt], ⟨p.eval 0, ?_⟩, ⟨q.eval 0, ?_⟩⟩
  · refine ((p.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp
    field_simp
  · refine ((q.continuous.tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ≠ 0 := hx
    simp
    field_simp

end UndergradKB.DifferentialEquations

