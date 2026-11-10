import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set Filter Topology Polynomial Asymptotics

/-! ### End behaviour of power functions and polynomials (CA-158, CA-012) -/

/-- OpenStax Calculus 1:§4.6 (CA-158): `x^n → +∞` as `x → +∞` for `n ≥ 1`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of power functions, p. 370"]
theorem tendsto_pow_atTop_kb {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => x ^ n) atTop atTop :=
  tendsto_pow_atTop hn

/-- OpenStax Calculus 1:§4.6 (CA-158): for even `n ≥ 2`, `x^n → +∞` as `x → -∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of power functions, p. 370"]
theorem tendsto_pow_atBot_even {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    Tendsto (fun x : ℝ => x ^ n) atBot atTop :=
  ((tendsto_pow_atTop hn0).comp (tendsto_neg_atBot_atTop (G := ℝ))).congr fun x => by
    simp [hn.neg_pow]

/-- OpenStax Calculus 1:§4.6 (CA-158): for odd `n`, `x^n → -∞` as `x → -∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 End behavior of power functions, p. 370"]
theorem tendsto_pow_atBot_odd {n : ℕ} (hn : Odd n) :
    Tendsto (fun x : ℝ => x ^ n) atBot atBot := by
  have h := (tendsto_neg_atTop_atBot (G := ℝ)).comp
    ((tendsto_pow_atTop hn.pos.ne').comp (tendsto_neg_atBot_atTop (G := ℝ)))
  exact h.congr fun x => by simp [hn.neg_pow]

/-- OpenStax Calculus 1:Example 4.24 (CA-158): `c x^n → +∞` as `x → +∞` for `c > 0`. -/
@[kb "openstaxcalculus2016" "1:Example 4.24, p. 371"]
theorem tendsto_const_mul_pow_atTop_pos {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => c * x ^ n) atTop atTop :=
  tendsto_const_mul_pow_atTop hn hc

/-- OpenStax Calculus 1:Example 4.24 (CA-158): `c x^n → -∞` as `x → +∞` for `c < 0`. -/
@[kb "openstaxcalculus2016" "1:Example 4.24, p. 371"]
theorem tendsto_const_mul_pow_atTop_neg {c : ℝ} (hc : c < 0) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : ℝ => c * x ^ n) atTop atBot :=
  (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc

/-- OpenStax Calculus 1:Example 4.24 (CA-158): `c x^n` as `x → -∞`, `c > 0`, `n` even: `+∞`. -/
@[kb "openstaxcalculus2016" "1:Example 4.24, p. 371"]
theorem tendsto_const_mul_pow_atBot_pos_even {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : Even n)
    (hn0 : n ≠ 0) : Tendsto (fun x : ℝ => c * x ^ n) atBot atTop :=
  (tendsto_pow_atBot_even hn hn0).const_mul_atTop hc

/-- OpenStax Calculus 1:Example 4.24 (CA-158): `c x^n` as `x → -∞`, `c > 0`, `n` odd: `-∞`. -/
@[kb "openstaxcalculus2016" "1:Example 4.24, p. 371"]
theorem tendsto_const_mul_pow_atBot_pos_odd {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : Odd n) :
    Tendsto (fun x : ℝ => c * x ^ n) atBot atBot :=
  (tendsto_pow_atBot_odd hn).const_mul_atBot hc

/-- OpenStax Calculus 1:Example 4.24 (CA-158): `c x^n` as `x → -∞`, `c < 0`, `n` even: `-∞`. -/
@[kb "openstaxcalculus2016" "1:Example 4.24, p. 371"]
theorem tendsto_const_mul_pow_atBot_neg_even {c : ℝ} (hc : c < 0) {n : ℕ} (hn : Even n)
    (hn0 : n ≠ 0) : Tendsto (fun x : ℝ => c * x ^ n) atBot atBot :=
  (tendsto_pow_atBot_even hn hn0).const_mul_atTop_of_neg hc

/-- OpenStax Calculus 1:Example 4.24 (CA-158): `c x^n` as `x → -∞`, `c < 0`, `n` odd: `+∞`. -/
@[kb "openstaxcalculus2016" "1:Example 4.24, p. 371"]
theorem tendsto_const_mul_pow_atBot_neg_odd {c : ℝ} (hc : c < 0) {n : ℕ} (hn : Odd n) :
    Tendsto (fun x : ℝ => c * x ^ n) atBot atTop :=
  (tendsto_pow_atBot_odd hn).const_mul_atBot_of_neg hc

/-- OpenStax Calculus 1:§1.2 end behavior of polynomials (CA-012): as `x → -∞`, a polynomial of positive
degree tends to `+∞` when (even degree, positive leading coefficient) or (odd degree, negative leading
coefficient). -/
@[kb "openstaxcalculus2016" "1:§1.2 end behavior of polynomial, p. 43"]
theorem polynomial_tendsto_atBot_atTop (P : ℝ[X]) (hdeg : 0 < P.degree)
    (h : (Even P.natDegree ∧ 0 < P.leadingCoeff) ∨ (Odd P.natDegree ∧ P.leadingCoeff < 0)) :
    Tendsto (fun x => P.eval x) atBot atTop := by
  have hn : P.natDegree ≠ 0 := (natDegree_pos_iff_degree_pos.2 hdeg).ne'
  refine (isEquivalent_atBot_lead P).symm.tendsto_atTop ?_
  rcases h with ⟨he, hc⟩ | ⟨ho, hc⟩
  · exact tendsto_const_mul_pow_atBot_pos_even hc he hn
  · exact tendsto_const_mul_pow_atBot_neg_odd hc ho

/-- OpenStax Calculus 1:§1.2 end behavior of polynomials (CA-012): as `x → -∞`, a polynomial of positive
degree tends to `-∞` when (odd degree, positive leading coefficient) or (even degree, negative leading
coefficient). -/
@[kb "openstaxcalculus2016" "1:§1.2 end behavior of polynomial, p. 43"]
theorem polynomial_tendsto_atBot_atBot (P : ℝ[X]) (hdeg : 0 < P.degree)
    (h : (Odd P.natDegree ∧ 0 < P.leadingCoeff) ∨ (Even P.natDegree ∧ P.leadingCoeff < 0)) :
    Tendsto (fun x => P.eval x) atBot atBot := by
  have hn : P.natDegree ≠ 0 := (natDegree_pos_iff_degree_pos.2 hdeg).ne'
  refine (isEquivalent_atBot_lead P).symm.tendsto_atBot ?_
  rcases h with ⟨ho, hc⟩ | ⟨he, hc⟩
  · exact tendsto_const_mul_pow_atBot_pos_odd hc ho
  · exact tendsto_const_mul_pow_atBot_neg_even hc he hn

/-! ### Horizontal and oblique asymptotes (CA-155, CA-161) -/

/-- OpenStax Calculus 1:§4.6 Definition (horizontal asymptote) (CA-155). The line `y = L` is a horizontal
asymptote of `f` if `f(x) → L` as `x → +∞` or as `x → -∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (horizontal asymptote), p. 363"]
def IsHorizontalAsymptote (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto f atTop (𝓝 L) ∨ Tendsto f atBot (𝓝 L)

/-- OpenStax Calculus 1:§4.6 (CA-155). The line `y = 0` is a horizontal asymptote of `1/x`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (horizontal asymptote), p. 363"]
theorem isHorizontalAsymptote_inv : IsHorizontalAsymptote (fun x : ℝ => 1 / x) 0 :=
  Or.inl (by simpa using tendsto_inv_atTop_zero)

/-- OpenStax Calculus 1:§4.6 Definition (oblique asymptote) (CA-161). The line `y = m x + b` (`m ≠ 0`) is an
oblique asymptote of `f` if `f(x) - (m x + b) → 0` as `x → +∞` or as `x → -∞`. -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (oblique asymptote), p. 375"]
def IsObliqueAsymptote (f : ℝ → ℝ) (m b : ℝ) : Prop :=
  m ≠ 0 ∧ (Tendsto (fun x => f x - (m * x + b)) atTop (𝓝 0) ∨
    Tendsto (fun x => f x - (m * x + b)) atBot (𝓝 0))

/-- OpenStax Calculus 1:§4.6 (CA-161). If `deg p = deg q + 1` (`q ≠ 0`), the quotient of `p` by `q` in
polynomial long division is a line `m x + b` with `m ≠ 0`, and `p/q - (m x + b) → 0` at both `+∞` and
`-∞`; so `y = m x + b` is an oblique asymptote of `p/q` (with `m x + b` the long-division quotient). -/
@[kb "openstaxcalculus2016" "1:§4.6 Definition (oblique asymptote), p. 375"]
theorem rational_oblique_asymptote (p q : ℝ[X]) (hq : q ≠ 0) (hdeg : p.degree = q.degree + 1) :
    ∃ m b : ℝ, p / q = C m * X + C b ∧ m ≠ 0 ∧
      Tendsto (fun x => p.eval x / q.eval x - (m * x + b)) atTop (𝓝 0) ∧
      Tendsto (fun x => p.eval x / q.eval x - (m * x + b)) atBot (𝓝 0) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.degree = n := ⟨q.natDegree, (degree_eq_natDegree hq)⟩
  have hle : q.degree ≤ p.degree := by
    rw [hdeg, hn]; exact_mod_cast Nat.le_succ n
  have hsum := degree_add_div hq hle
  have hd1 : (p / q).degree = 1 := by
    rw [hdeg, hn] at hsum
    by_cases hz : p / q = 0
    · rw [hz, degree_zero] at hsum
      have h2 : ((n + 1 : ℕ) : WithBot ℕ) = ⊥ := by push_cast; exact hsum.symm
      exact absurd h2 (WithBot.coe_ne_bot)
    · rw [degree_eq_natDegree hz] at hsum ⊢
      have : (n + (p / q).natDegree : ℕ) = n + 1 := by exact_mod_cast hsum
      have hk : (p / q).natDegree = 1 := by omega
      rw [hk]; rfl
  set d := p / q with hd
  have hform : d = C (d.coeff 1) * X + C (d.coeff 0) := eq_X_add_C_of_degree_le_one hd1.le
  have hm : d.coeff 1 ≠ 0 := coeff_ne_zero_of_eq_degree hd1
  refine ⟨d.coeff 1, d.coeff 0, hform, hm, ?_, ?_⟩
  all_goals
    have hr : (p % q).degree < q.degree := degree_mod_lt p hq
    have hpq : p = q * d + p % q := (EuclideanDomain.div_add_mod p q).symm
    have key : ∀ x : ℝ, q.eval x ≠ 0 → p.eval x / q.eval x - (d.coeff 1 * x + d.coeff 0)
        = (p % q).eval x / q.eval x := by
      intro x hx
      have h1 : p.eval x = q.eval x * (d.coeff 1 * x + d.coeff 0) + (p % q).eval x := by
        conv_lhs => rw [hpq, hform]
        simp
      rw [h1]; field_simp; ring
  · refine ((div_tendsto_atTop_zero_of_degree_lt (p % q) q hr)).congr' ?_
    filter_upwards [eventually_atTop_not_isRoot q hq] with x hx
    exact (key x hx).symm
  · refine ((div_tendsto_atBot_zero_of_degree_lt (p % q) q hr)).congr' ?_
    filter_upwards [eventually_atBot_not_isRoot q hq] with x hx
    exact (key x hx).symm

end UndergradKB.Calculus
