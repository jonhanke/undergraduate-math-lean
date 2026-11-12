import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Topology.Algebra.Polynomial
import UndergradKB.Common.Attr

/-!
# Real polynomials (Stitz-Zeager, chapter 3)

Zeros by sign change, end behaviour, multiplicity, polynomial division, Descartes' rule of signs,
bounds on zeros, the imaginary unit and complex conjugation, and the real factorization theorem.
-/

namespace UndergradKB.Precalculus

open Polynomial Filter Topology
open scoped ComplexConjugate

/-- A real polynomial whose values at `a < b` have opposite signs has a zero strictly between
`a` and `b` (intermediate value theorem, zero form) (PC-052). -/
@[kb "stitzzeager2013" "Theorem 3.1, p. 253"]
theorem poly_zero_of_sign_change (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨c, hc', hc0⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨c, hc', hc0⟩
  · obtain ⟨c, hc', hc0⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨c, hc', hc0⟩

/-- Division algorithm over `ℝ`: for a nonzero divisor `d`, there is exactly one pair
`(q, r)` with `p = d * q + r` and `r = 0` or `deg r < deg d` (PC-056). -/
@[kb "stitzzeager2013" "Theorem 3.4, p. 270"]
theorem poly_division_algorithm_unique (p d : ℝ[X]) (hd : d ≠ 0) :
    ∃! qr : ℝ[X] × ℝ[X], p = d * qr.1 + qr.2 ∧ (qr.2 = 0 ∨ qr.2.degree < d.degree) := by
  refine ⟨(p / d, p % d), ⟨(EuclideanDomain.div_add_mod p d).symm, Or.inr (degree_mod_lt p hd)⟩, ?_⟩
  rintro ⟨q, r⟩ ⟨h1, h2⟩
  simp only at h1 h2
  have h2' : r.degree < d.degree := by
    rcases h2 with h | h
    · rw [h, degree_zero]; exact bot_lt_iff_ne_bot.mpr (by simpa using hd)
    · exact h
  have e := EuclideanDomain.div_add_mod p d
  have key : d * (q - p / d) = p % d - r := by linear_combination -h1 - e
  have hq : q - p / d = 0 := by
    by_contra hne
    have h3 : d.degree ≤ (d * (q - p / d)).degree := by
      rw [degree_mul]
      have : (0 : WithBot ℕ) ≤ (q - p / d).degree := zero_le_degree_iff.mpr hne
      exact le_add_of_nonneg_right this
    have h4 : (p % d - r).degree < d.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_mod_lt p hd) h2')
    rw [key] at h3
    exact absurd h3 (not_le.mpr h4)
  have hq' : q = p / d := sub_eq_zero.mp hq
  have hr : r = p % d := by
    rw [hq'] at h1
    linear_combination -h1 - e
  simp [hq', hr]

/-- Basic facts for the imaginary unit: `i ^ 2 = -1`, and for `c ≥ 0` the principal square root
of `-c` is `i √c` (PC-064). -/
@[kb "stitzzeager2013" "Definition 3.4, p. 299"]
theorem imaginary_unit_sq_and_sqrt_neg (c : ℝ) (hc : 0 ≤ c) :
    Complex.I ^ 2 = -1 ∧ (-(c : ℂ)) ^ (1 / 2 : ℂ) = Complex.I * (Real.sqrt c : ℝ) := by
  refine ⟨Complex.I_sq, ?_⟩
  rcases hc.eq_or_lt with h | hc
  · subst h; simp
  have h0 : (-(c : ℂ)) ≠ 0 := by simpa using hc.ne'
  rw [Complex.cpow_def_of_ne_zero h0]
  have hlog : Complex.log (-(c : ℂ)) = (Real.log c : ℂ) + Real.pi * Complex.I := by
    have : (-(c : ℂ)) = ((-c : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.log, Complex.arg_ofReal_of_neg (by linarith)]
    simp [Complex.norm_real, abs_of_pos hc]
  rw [hlog]
  have : ((Real.log c : ℂ) + Real.pi * Complex.I) * (1 / 2) =
      ((Real.log c / 2 : ℝ) : ℂ) + (Real.pi / 2 : ℝ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
  have hs : Real.exp (Real.log c / 2) = Real.sqrt c := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hc]; congr 1; ring
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two, hs]
  push_cast; ring

/-- Properties of complex conjugation: it is an involution, respects sums, products and powers,
and fixes exactly the real numbers (PC-067). -/
@[kb "stitzzeager2013" "Theorem 3.12, p. 301"]
theorem complex_conj_properties (z w : ℂ) (n : ℕ) :
    conj (conj z) = z ∧ conj (z + w) = conj z + conj w ∧ conj (z * w) = conj z * conj w ∧
      conj (z ^ n) = conj z ^ n ∧ (conj z = z ↔ ∃ r : ℝ, z = r) :=
  ⟨Complex.conj_conj z, map_add _ z w, map_mul _ z w, map_pow _ z n, Complex.conj_eq_iff_real⟩

/-! ### End behaviour -/

/-- At `+∞` a polynomial of positive degree is asymptotically equivalent to its leading term
(PC-053, right end). -/
@[kb "stitzzeager2013" "Theorem 3.2, p. 255"]
theorem poly_end_behavior_atTop (p : ℝ[X]) :
    Asymptotics.IsEquivalent atTop (fun x => p.eval x)
      (fun x => p.leadingCoeff * x ^ p.natDegree) :=
  Polynomial.isEquivalent_atTop_lead p

/-- At `-∞` a polynomial is asymptotically equivalent to its leading term (PC-053, left end). -/
@[kb "stitzzeager2013" "Theorem 3.2, p. 255"]
theorem poly_end_behavior_atBot (p : ℝ[X]) :
    Asymptotics.IsEquivalent atBot (fun x => p.eval x)
      (fun x => p.leadingCoeff * x ^ p.natDegree) := by
  have h := (Polynomial.isEquivalent_atTop_lead (p.comp (-X))).comp_tendsto
    (tendsto_neg_atBot_atTop : Tendsto (Neg.neg : ℝ → ℝ) atBot atTop)
  have hn : (p.comp (-X)).natDegree = p.natDegree := by
    rw [natDegree_comp]; simp
  have e1 : ((fun x => eval x (p.comp (-X))) ∘ Neg.neg) = fun x => eval x p := by
    funext x; simp
  have e2 : ((fun x => (p.comp (-X)).leadingCoeff * x ^ (p.comp (-X)).natDegree) ∘ Neg.neg) =
      fun x => p.leadingCoeff * x ^ p.natDegree := by
    funext x
    simp only [Function.comp, comp_neg_X_leadingCoeff_eq, hn]
    rw [mul_comm ((-1 : ℝ) ^ p.natDegree), mul_assoc, ← mul_pow]
    simp
  rw [e1, e2] at h
  exact h

/-- Sign of a polynomial at `-∞` and `+∞` by parity of the degree and sign of the leading
coefficient: the left-end limits (PC-053). -/
@[kb "stitzzeager2013" "Theorem 3.2, p. 255"]
theorem poly_tendsto_atBot_cases (p : ℝ[X]) (hp : 0 < p.degree) :
    (Even p.natDegree →
      (0 < p.leadingCoeff → Tendsto (fun x => p.eval x) atBot atTop) ∧
      (p.leadingCoeff < 0 → Tendsto (fun x => p.eval x) atBot atBot)) ∧
    (Odd p.natDegree →
      (0 < p.leadingCoeff → Tendsto (fun x => p.eval x) atBot atBot) ∧
      (p.leadingCoeff < 0 → Tendsto (fun x => p.eval x) atBot atTop)) := by
  have hn : (p.comp (-X)).natDegree = p.natDegree := by
    rw [natDegree_comp]; simp
  have hqd : 0 < (p.comp (-X)).degree := by
    rw [← natDegree_pos_iff_degree_pos, hn]; exact natDegree_pos_iff_degree_pos.mpr hp
  have hlc := comp_neg_X_leadingCoeff_eq p
  have key : (fun x => p.eval x) = (fun x => eval x (p.comp (-X))) ∘ Neg.neg := by
    funext x; simp
  have hA : 0 ≤ (p.comp (-X)).leadingCoeff → Tendsto (fun x => p.eval x) atBot atTop := fun h => by
    rw [key]
    exact (tendsto_atTop_of_leadingCoeff_nonneg _ hqd h).comp tendsto_neg_atBot_atTop
  have hB : (p.comp (-X)).leadingCoeff ≤ 0 → Tendsto (fun x => p.eval x) atBot atBot := fun h => by
    rw [key]
    exact (tendsto_atBot_of_leadingCoeff_nonpos _ hqd h).comp tendsto_neg_atBot_atTop
  refine ⟨fun he => ⟨fun h => hA ?_, fun h => hB ?_⟩, fun ho => ⟨fun h => hB ?_, fun h => hA ?_⟩⟩
  · rw [hlc, he.neg_one_pow]; linarith
  · rw [hlc, he.neg_one_pow]; linarith
  · rw [hlc, ho.neg_one_pow]; linarith
  · rw [hlc, ho.neg_one_pow]; linarith

/-! ### Multiplicity and sign changes -/

private lemma eventually_same_sign (q : ℝ[X]) (c : ℝ) (hq : q.eval c ≠ 0) :
    ∀ᶠ x in 𝓝 c, 0 < q.eval x * q.eval c := by
  have hcont : Continuous fun x => q.eval x * q.eval c := q.continuous.mul continuous_const
  exact hcont.continuousAt.eventually (lt_mem_nhds (mul_self_pos.mpr hq))

/-- Zero of even multiplicity `m` (given as `p = (X - c)^m * q` with `q c ≠ 0`): the sign of
`p` near `c`, away from `c`, equals the sign of `q c`, so the graph touches and rebounds
(PC-055, even case). -/
@[kb "stitzzeager2013" "Theorem 3.3, p. 257"]
theorem poly_no_sign_change_even_multiplicity (p q : ℝ[X]) (c : ℝ) (m : ℕ) (hm : Even m)
    (hp : p = (X - C c) ^ m * q) (hq : q.eval c ≠ 0) :
    ∀ᶠ x in 𝓝[≠] c, 0 < p.eval x * q.eval c := by
  filter_upwards [nhdsWithin_le_nhds (eventually_same_sign q c hq), self_mem_nhdsWithin]
    with x h1 h2
  have hx : x - c ≠ 0 := sub_ne_zero.mpr h2
  have : p.eval x * q.eval c = (x - c) ^ m * (q.eval x * q.eval c) := by
    rw [hp]; simp [eval_mul, eval_pow]; ring
  rw [this]
  exact mul_pos (hm.pow_pos hx) h1

/-- Zero of odd multiplicity `m` (given as `p = (X - c)^m * q` with `q c ≠ 0`): just to the
right of `c` the sign of `p` is that of `q c`, just to the left it is the opposite, so the
graph crosses the axis (PC-055, odd case). -/
@[kb "stitzzeager2013" "Theorem 3.3, p. 257"]
theorem poly_sign_change_odd_multiplicity (p q : ℝ[X]) (c : ℝ) (m : ℕ) (hm : Odd m)
    (hp : p = (X - C c) ^ m * q) (hq : q.eval c ≠ 0) :
    (∀ᶠ x in 𝓝[>] c, 0 < p.eval x * q.eval c) ∧ (∀ᶠ x in 𝓝[<] c, p.eval x * q.eval c < 0) := by
  have hev : ∀ x, p.eval x * q.eval c = (x - c) ^ m * (q.eval x * q.eval c) := fun x => by
    rw [hp]; simp [eval_mul, eval_pow]; ring
  constructor
  · filter_upwards [nhdsWithin_le_nhds (eventually_same_sign q c hq), self_mem_nhdsWithin]
      with x h1 h2
    rw [hev]
    exact mul_pos (pow_pos (sub_pos.mpr h2) _) h1
  · filter_upwards [nhdsWithin_le_nhds (eventually_same_sign q c hq), self_mem_nhdsWithin]
      with x h1 h2
    rw [hev]
    exact mul_neg_of_neg_of_pos (hm.pow_neg (sub_neg.mpr h2)) h1

/-- Every nonzero polynomial factors at a point `c` as `(X - c)^m * q` with `m` the multiplicity
of `c` as a zero and `q c ≠ 0` (supports PC-055). -/
theorem poly_factor_root_multiplicity (p : ℝ[X]) (hp : p ≠ 0) (c : ℝ) :
    ∃ q : ℝ[X], p = (X - C c) ^ rootMultiplicity c p * q ∧ q.eval c ≠ 0 := by
  obtain ⟨q, h1, h2⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp c
  exact ⟨q, h1, fun h => h2 (dvd_iff_isRoot.mpr h)⟩

/-! ### Bounds on real zeros -/

private lemma eval_sign_pos (q : ℝ[X]) (ε x : ℝ)
    (h : ∀ i, 0 ≤ ε * (q.coeff i * x ^ i))
    (hn : 0 < ε * (q.coeff q.natDegree * x ^ q.natDegree)) : 0 < ε * q.eval x := by
  rw [eval_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_pos' (fun i _ => h i)
    ⟨q.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _), hn⟩

/-- Upper bound from synthetic division by `X - c`, `c > 0`: if `p = (X - c) q + r` and all
numbers in the last line (coefficients of `q` and `r`) have a common sign (`ε = 1`: all
nonnegative, `ε = -1`: all nonpositive; zeros may count either way), then `p` has no zero
larger than `c` (PC-063, upper bound). -/
@[kb "stitzzeager2013" "Theorem 3.11, p. 286"]
theorem poly_upper_bound_synthetic_division (p q : ℝ[X]) (c r ε : ℝ) (hc : 0 < c) (hq : q ≠ 0)
    (hp : p = (X - C c) * q + C r) (hε : ε = 1 ∨ ε = -1)
    (hqc : ∀ i, 0 ≤ ε * q.coeff i) (hr : 0 ≤ ε * r) : ∀ x, c < x → p.eval x ≠ 0 := by
  intro x hx h0
  have hx0 : 0 < x := hc.trans hx
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hlc : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hq1 : 0 < ε * q.eval x := by
    apply eval_sign_pos
    · intro i
      rw [← mul_assoc]; exact mul_nonneg (hqc i) (pow_nonneg hx0.le _)
    · rw [← mul_assoc]
      exact mul_pos (lt_of_le_of_ne (hqc _) (fun h => mul_ne_zero hε0 hlc h.symm))
        (pow_pos hx0 _)
  have : ε * p.eval x = (x - c) * (ε * q.eval x) + ε * r := by
    rw [hp]; simp [eval_mul]; ring
  have h3 : 0 < (x - c) * (ε * q.eval x) := mul_pos (sub_pos.mpr hx) hq1
  rw [h0] at this
  linarith

/-- Lower bound from synthetic division by `X - c`, `c < 0`: if `p = (X - c) q + r` and the
numbers in the last line alternate in sign (the coefficient of `X^i` in `q` has the sign of
`ε (-1)^i` and the remainder the sign of `-ε`; zeros may count either way), then `p` has no
zero smaller than `c` (PC-063, lower bound). -/
@[kb "stitzzeager2013" "Theorem 3.11, p. 286"]
theorem poly_lower_bound_synthetic_division (p q : ℝ[X]) (c r ε : ℝ) (hc : c < 0) (hq : q ≠ 0)
    (hp : p = (X - C c) * q + C r) (hε : ε = 1 ∨ ε = -1)
    (hqc : ∀ i, 0 ≤ ε * (-1) ^ i * q.coeff i) (hr : 0 ≤ -ε * r) :
    ∀ x, x < c → p.eval x ≠ 0 := by
  intro x hx h0
  have hx0 : 0 < -x := by linarith
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hlc : q.coeff q.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hpow : ∀ i : ℕ, x ^ i = (-1) ^ i * (-x) ^ i := fun i => by
    rw [← mul_pow]; simp
  have hq1 : 0 < ε * q.eval x := by
    apply eval_sign_pos
    · intro i
      have : ε * (q.coeff i * x ^ i) = (ε * (-1) ^ i * q.coeff i) * (-x) ^ i := by
        rw [hpow]; ring
      rw [this]; exact mul_nonneg (hqc i) (pow_nonneg hx0.le _)
    · have : ε * (q.coeff q.natDegree * x ^ q.natDegree)
          = (ε * (-1) ^ q.natDegree * q.coeff q.natDegree) * (-x) ^ q.natDegree := by
        rw [hpow]; ring
      rw [this]
      refine mul_pos (lt_of_le_of_ne (hqc _) (fun h => ?_)) (pow_pos hx0 _)
      have h' := h.symm
      simp only [mul_eq_zero, hε0, hlc, false_or, or_false] at h'
      exact absurd h' (pow_ne_zero _ (by norm_num))
  have : ε * p.eval x = (x - c) * (ε * q.eval x) + ε * r := by
    rw [hp]; simp [eval_mul]; ring
  have h3 : (x - c) * (ε * q.eval x) < 0 := mul_neg_of_neg_of_pos (by linarith) hq1
  rw [h0] at this
  linarith

/-! ### Descartes' rule of signs -/

/-- Descartes' rule of signs, upper bounds: the number of positive zeros of a real polynomial
(counted with multiplicity) is at most the number of sign variations of its coefficients, and the
number of negative zeros is at most the number of sign variations of the coefficients of
`p(-x)`. The parity refinement ("minus an even number") is `descartes_rule_of_signs` in DescartesParity.lean (PC-062). -/
@[kb "stitzzeager2013" "Theorem 3.10, p. 285"]
theorem descartes_rule_of_signs_bounds (p : ℝ[X]) :
    p.roots.countP (0 < ·) ≤ p.signVariations ∧
      p.roots.countP (· < 0) ≤ (p.comp (-X)).signVariations := by
  refine ⟨roots_countP_pos_le_signVariations p, ?_⟩
  have h := roots_countP_pos_le_signVariations (p.comp (-X))
  rw [roots_comp_neg_X, Multiset.countP_map] at h
  simpa [Multiset.countP_eq_card_filter] using h

/-! ### Real factorization -/

/-- Real Factorization Theorem: a nonzero real polynomial is its leading coefficient times a
product of monic factors, each either linear `X - r` or an irreducible monic quadratic
without real zeros (PC-071). -/
@[kb "stitzzeager2013" "Theorem 3.16, p. 304"]
theorem real_polynomial_factorization (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ s : Multiset ℝ[X], p = C p.leadingCoeff * s.prod ∧
      ∀ f ∈ s, f.Monic ∧ ((∃ r : ℝ, f = X - C r) ∨
        (Irreducible f ∧ f.natDegree = 2 ∧ ∀ x : ℝ, f.eval x ≠ 0)) := by
  classical
  have hmonic : ∀ f ∈ UniqueFactorizationMonoid.normalizedFactors p, f.Monic := by
    intro f hf
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor f hf
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor f hf
    rw [← hn]
    exact monic_normalize hirr.ne_zero
  refine ⟨UniqueFactorizationMonoid.normalizedFactors p, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hp
    obtain ⟨a, ha, hau⟩ := Polynomial.isUnit_iff.mp u.isUnit
    have hm : (UniqueFactorizationMonoid.normalizedFactors p).prod.Monic :=
      by simpa using monic_multiset_prod_of_monic _ id hmonic
    have : p.leadingCoeff = a := by
      rw [← hu, ← hau, leadingCoeff_mul, hm.leadingCoeff, one_mul, leadingCoeff_C]
    have hu' : C a * (UniqueFactorizationMonoid.normalizedFactors p).prod = p := by
      rw [hau, mul_comm]; exact hu
    rw [this]; exact hu'.symm
  · intro f hf
    refine ⟨hmonic f hf, ?_⟩
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor f hf
    have hmon := hmonic f hf
    by_cases hroot : ∃ x : ℝ, f.eval x = 0
    · obtain ⟨x, hx⟩ := hroot
      left
      have hdeg := degree_eq_one_of_irreducible_of_root hirr (x := x) hx
      have hnd : f.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg
      have h1 := hmon.eq_X_add_C hnd
      refine ⟨-f.coeff 0, ?_⟩
      rw [C_neg, sub_neg_eq_add]; exact h1
    · right
      push Not at hroot
      refine ⟨hirr, ?_, hroot⟩
      have hle := hirr.natDegree_le_two
      have h0 : f.natDegree ≠ 0 := fun h0 =>
        hirr.not_isUnit (by rw [eq_one_of_monic_natDegree_zero hmon h0]; exact isUnit_one)
      have h1 : f.natDegree ≠ 1 := fun h1 => by
        have : f.degree = 1 := by rw [degree_eq_natDegree hirr.ne_zero, h1]; rfl
        obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one this
        exact hroot x hx
      omega

end UndergradKB.Precalculus
