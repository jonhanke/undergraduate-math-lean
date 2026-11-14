import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UndergradKB.Precalculus.Radicals
import UndergradKB.Precalculus.SignDiagrams

/-!
# Rational exponents of any real base (Stitz-Zeager, Precalculus, §5.3)

Definition 5.5 of the book gives `x^(m/n)` the value `(ⁿ√x)ᵐ` whenever that radical expression is defined, so
negative bases are allowed when `n` is odd: `(-8)^(1/3) = -2`. Mathlib's `Real.rpow` deliberately differs for
negative bases (it takes the real part of the complex power: `(-1) ^ (1/3 : ℝ) = 1/2`), so the book's operation is
the bridging definition `bookRatPow x m n`, built on the topic's principal root `principalRoot`.

Proved here:
* `bookRatPow_eq_principalRoot_zpow`: the two forms of Definition 5.5 agree, `(ⁿ√x)ᵐ = ⁿ√(xᵐ)`, for every integer
  `m` wherever `(ⁿ√x)ᵐ` is defined;
* `bookRatPow_mul_mul`: the value does not depend on how the fraction `m/n` is written, as long as both writings are
  defined (so Definition 5.5 is a definition on rational exponents);
* `bookRatPow_eq_rpow`: for `x ≥ 0` it is Mathlib's `x ^ ((m : ℝ) / n)`;
* the book's warning after Definition 5.5: `(x^(2/3))^(3/2) = |x|` for every real `x` (`bookRatPow_two_thirds_three_halves`),
  so the law `(x^a)^b = x^(ab)` fails at `x = -1`, while `(x^(3/2))^(2/3) = x` for `x ≥ 0`;
* radical functions are continuous on their domains (`principalRoot_continuous_odd`,
  `principalRoot_continuousOn_even`), which the book states and leaves to calculus, and the sign-diagram box for
  algebraic functions (`sign_diagram_algebraic`) that the book builds on it.
-/

namespace UndergradKB.Precalculus

open Real

/-- The book's rational power `x^(m/n) = (ⁿ√x)ᵐ` (Definition 5.5), for a real `x`, an integer `m` and a natural
number `n`. It is meaningful exactly when `BookRatPowDefined x m n` holds. -/
noncomputable def bookRatPow (x : ℝ) (m : ℤ) (n : ℕ) : ℝ := (principalRoot n x) ^ m

/-- When `(ⁿ√x)ᵐ` is defined: `n ≥ 1`, the root is real (`n` odd or `x ≥ 0`), and it is not a negative power of
zero. -/
def BookRatPowDefined (x : ℝ) (m : ℤ) (n : ℕ) : Prop :=
  n ≠ 0 ∧ (Odd n ∨ 0 ≤ x) ∧ (0 ≤ m ∨ x ≠ 0)

lemma principalRoot_ne_zero {n : ℕ} {x : ℝ} (hn : n ≠ 0) (h : Odd n ∨ 0 ≤ x) (hx : x ≠ 0) :
    principalRoot n x ≠ 0 := by
  intro h0
  have := principalRoot_pow hn h
  rw [h0, zero_pow hn] at this
  exact hx this.symm

lemma principalRoot_inv {n : ℕ} (hn : n ≠ 0) {x : ℝ} (h : Odd n ∨ 0 ≤ x) :
    principalRoot n x⁻¹ = (principalRoot n x)⁻¹ := by
  symm
  apply principalRoot_unique hn
  · exact h.imp_right inv_nonneg.2
  · exact h.imp_right fun hx => inv_nonneg.2 (principalRoot_nonneg hx)
  · rw [inv_pow, principalRoot_pow hn h]

/-- Definition 5.5, the two forms agree: for every integer `m`, `ⁿ√(xᵐ) = (ⁿ√x)ᵐ` whenever `(ⁿ√x)ᵐ` is defined
(PC-091). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_eq_principalRoot_zpow {x : ℝ} {m : ℤ} {n : ℕ} (h : BookRatPowDefined x m n) :
    bookRatPow x m n = principalRoot n (x ^ m) := by
  obtain ⟨hn, hx, hm⟩ := h
  unfold bookRatPow
  rcases le_or_gt 0 m with h0 | h0
  · lift m to ℕ using h0
    simp only [zpow_natCast]
    exact (principalRoot_pow_nat hn m hx).symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨m.natAbs, by omega⟩
    simp only [zpow_neg, zpow_natCast]
    rw [principalRoot_inv hn (hx.imp_right fun hx => pow_nonneg hx k), principalRoot_pow_nat hn k hx]

/-- Definition 5.5, first line: `x^(1/n) = ⁿ√x` (PC-091). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_one (x : ℝ) (n : ℕ) : bookRatPow x 1 n = principalRoot n x := by
  simp [bookRatPow]

/-- Definition 5.5 agrees with Mathlib's real power for nonnegative bases: `x^(m/n) = x ^ ((m : ℝ) / n)` for
`x ≥ 0` (PC-091). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (m : ℤ) (n : ℕ) :
    bookRatPow x m n = x ^ ((m : ℝ) / n) :=
  (rpow_intCast_div_eq_principalRoot_zpow hx m).symm

/-- Definition 5.5 does not depend on how the exponent is written: if `x^(m/n)` and `x^(km/kn)` are both defined
(this forces `k ≥ 1`), they are equal (PC-091). For example `(-1)^(1/3) = -1`, while `(-1)^(2/6)` is not defined by the book. -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_mul_mul {x : ℝ} {m : ℤ} {n k : ℕ} (h : BookRatPowDefined x m n)
    (h' : BookRatPowDefined x (k * m) (k * n)) :
    bookRatPow x (k * m) (k * n) = bookRatPow x m n := by
  obtain ⟨hn, hx, -⟩ := h
  obtain ⟨hkn, hx', -⟩ := h'
  set s := principalRoot (k * n) x with hs
  have hsk : s ^ k = principalRoot n x := by
    apply principalRoot_unique hn hx
    · rcases hx with ho | h0
      · exact Or.inl ho
      · exact Or.inr (pow_nonneg (principalRoot_nonneg h0) k)
    · rw [← pow_mul, principalRoot_pow hkn hx']
  unfold bookRatPow
  rw [← hs, ← hsk, ← zpow_natCast, ← zpow_mul]

/-- The book's warning after Definition 5.5: `(x^(2/3))^(3/2) = |x|` for every real `x`, not `x`. -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_two_thirds_three_halves (x : ℝ) :
    bookRatPow (bookRatPow x 2 3) 3 2 = |x| := by
  have h3 : Odd 3 := by decide
  have hx := principalRoot_pow (n := 3) (by norm_num) (x := x) (Or.inl h3)
  unfold bookRatPow
  simp only [zpow_ofNat]
  rw [principalRoot_pow_self_even (by decide) (by norm_num), ← abs_pow, hx]

/-- The book's warning, the instance `x = -1`: `((-1)^(2/3))^(3/2) = 1`, while `(-1)^((2/3)(3/2)) = (-1)^1 = -1`, so
the usual law `(x^a)^b = x^(ab)` fails for rational exponents of negative bases. -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_exponent_law_fails :
    bookRatPow (bookRatPow (-1) 2 3) 3 2 = 1 ∧ bookRatPow (-1) 1 1 = -1 := by
  refine ⟨by rw [bookRatPow_two_thirds_three_halves]; norm_num, ?_⟩
  rw [bookRatPow_one]
  exact ((principalRoot_eq_iff_odd (n := 1) (by decide) (-1) (-1)).2 (by norm_num)).symm

/-- The companion fact the book leaves as an exercise: `(x^(3/2))^(2/3) = x` where `x^(3/2)` is defined (`x ≥ 0`). -/
@[kb "stitzzeager2013" "Definition 5.5, p. 410"]
theorem bookRatPow_three_halves_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    bookRatPow (bookRatPow x 3 2) 2 3 = x := by
  have h0 : 0 ≤ bookRatPow x 3 2 := by
    unfold bookRatPow; simp only [zpow_ofNat]; exact pow_nonneg (principalRoot_nonneg hx) 3
  rw [bookRatPow_eq_rpow h0, bookRatPow_eq_rpow hx, ← Real.rpow_mul hx]
  norm_num

/-- Mathlib's `Real.rpow` is not the book's power on negative bases: `(-1) ^ (1/3 : ℝ) = 1/2` in Mathlib, while the
book's `(-1)^(1/3)` is `-1`. -/
theorem rpow_neg_one_one_third_ne_bookRatPow :
    (-1 : ℝ) ^ ((1 : ℝ) / 3) = 1 / 2 ∧ bookRatPow (-1) 1 3 = -1 := by
  constructor
  · rw [Real.rpow_def_of_neg (by norm_num), Real.log_neg_eq_log, Real.log_one, zero_mul, Real.exp_zero, one_mul,
      one_div_mul_eq_div, Real.cos_pi_div_three]
  · rw [bookRatPow_one]
    have h := (principalRoot_eq_iff_odd (n := 3) (by decide) (-1) (-1)).2 (by norm_num)
    exact h.symm

/-- Radical functions are continuous on their domains, odd index: `x ↦ ⁿ√x` is continuous on all of `ℝ` (stated in
§5.3 and left to calculus). -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem principalRoot_continuous_odd {n : ℕ} (hn : Odd n) : Continuous (principalRoot n) := by
  have hn0 : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hn.pos.ne')
  have hc : Continuous fun x : ℝ => x ^ ((n : ℝ)⁻¹) :=
    Real.continuous_rpow_const (inv_nonneg.2 (Nat.cast_nonneg n))
  have : principalRoot n = fun x => if (0 : ℝ) ≤ x then x ^ ((n : ℝ)⁻¹) else -((-x) ^ ((n : ℝ)⁻¹)) := by
    funext x; rfl
  rw [this]
  refine Continuous.if_le hc (hc.comp continuous_neg).neg continuous_const continuous_id ?_
  intro x hx
  subst hx
  simp [Real.zero_rpow hn0]

/-- Radical functions are continuous on their domains, even index: `x ↦ ⁿ√x` is continuous on `[0, ∞)` (stated in
§5.3 and left to calculus). -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem principalRoot_continuousOn_even (n : ℕ) : ContinuousOn (principalRoot n) (Set.Ici 0) := by
  have hc : Continuous fun x : ℝ => x ^ ((n : ℝ)⁻¹) :=
    Real.continuous_rpow_const (inv_nonneg.2 (Nat.cast_nonneg n))
  exact hc.continuousOn.congr fun x hx => principalRoot_of_nonneg hx

/-- Sign diagram of an algebraic function (§5.3): an algebraic function (built from polynomials, rational functions
and radicals) is continuous on each interval of its domain, by the two continuity theorems above; on an interval of
the domain containing no zero it has one constant sign, so one test value per interval cut out by the zeros and the
excluded values gives the sign. -/
@[kb "stitzzeager2013" "§5.3, p. 411"]
theorem sign_diagram_algebraic {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected) (hf : ContinuousOn f I)
    (hz : ∀ x ∈ I, f x ≠ 0) {x t : ℝ} (hx : x ∈ I) (ht : t ∈ I) :
    SignType.sign (f x) = SignType.sign (f t) :=
  sign_eq_of_continuousOn_ne_zero hI hf hz hx ht

end UndergradKB.Precalculus
