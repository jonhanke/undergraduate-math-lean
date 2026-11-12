import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import UndergradKB.Common.Attr

/-!
# Descartes' Rule of Signs, parity refinement (PC-062)

The number of positive zeros (with multiplicity) of a nonzero real polynomial equals the number
of sign variations of its coefficients minus an even natural number.  Mathlib provides the
inequality; here the parity is proved.
-/

namespace UndergradKB.Precalculus

open Polynomial Filter Topology

private lemma trailingCoeff_eraseLead_of_ne {p : ℝ[X]} (hp : p ≠ 0) (he : p.eraseLead ≠ 0) :
    p.eraseLead.trailingCoeff = p.trailingCoeff := by
  have hlt : p.eraseLead.natDegree < p.natDegree := by
    rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
    · exact h
    · exact absurd h he
  set t := p.eraseLead.natTrailingDegree with ht
  have htle : t ≤ p.eraseLead.natDegree := natTrailingDegree_le_natDegree _
  have h1 : p.coeff t = p.eraseLead.coeff t := by
    rw [eraseLead_coeff_of_ne]; omega
  have h2 : p.eraseLead.coeff t ≠ 0 := by
    have : p.eraseLead.trailingCoeff ≠ 0 := mt trailingCoeff_eq_zero.mp he
    exact this
  have h3 : p.natTrailingDegree ≤ t := natTrailingDegree_le_of_ne_zero (by rw [h1]; exact h2)
  have h4 : t ≤ p.natTrailingDegree := by
    apply le_natTrailingDegree hp
    intro m hm
    have : p.eraseLead.coeff m = 0 := coeff_eq_zero_of_lt_natTrailingDegree hm
    rw [← this, eraseLead_coeff_of_ne]; omega
  have : p.natTrailingDegree = t := le_antisymm h3 h4
  simp only [trailingCoeff]
  rw [this, h1]

private lemma trailingCoeff_monomial' (n : ℕ) (c : ℝ) : (monomial n c).trailingCoeff = c := by
  by_cases hc : c = 0
  · simp [hc]
  · simp [trailingCoeff, natTrailingDegree_monomial hc]

private lemma trailingCoeff_eq_leadingCoeff_of_eraseLead {p : ℝ[X]} (_hp : p ≠ 0)
    (he : p.eraseLead = 0) : p.trailingCoeff = p.leadingCoeff := by
  have h := eraseLead_add_monomial_natDegree_leadingCoeff p
  rw [he, zero_add] at h
  conv_lhs => rw [← h]
  rw [trailingCoeff_monomial']

/-- Parity of sign variations: it is odd exactly when the leading and trailing coefficients have
opposite signs. -/
lemma signVariations_mod_two (p : ℝ[X]) (hp : p ≠ 0) :
    p.signVariations % 2 =
      if SignType.sign p.leadingCoeff = SignType.sign p.trailingCoeff then 0 else 1 := by
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with | _ d ih =>
  have hl : SignType.sign p.leadingCoeff ≠ 0 := by simp [hp]
  rw [signVariations_eq_eraseLead_add_ite hp]
  by_cases he : p.eraseLead = 0
  · rw [trailingCoeff_eq_leadingCoeff_of_eraseLead hp he]
    simp [he, hp]
  · have hlt : p.eraseLead.natDegree < p.natDegree := by
      rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
      · exact h
      · exact absurd h he
    have := ih _ (hd ▸ hlt) p.eraseLead he rfl
    rw [trailingCoeff_eraseLead_of_ne hp he] at this
    have hl' : SignType.sign p.eraseLead.leadingCoeff ≠ 0 := by simp [he]
    have ht : SignType.sign p.trailingCoeff ≠ 0 := by simp [hp]
    revert this hl hl' ht
    generalize p.eraseLead.signVariations = n
    generalize SignType.sign p.leadingCoeff = a
    generalize SignType.sign p.eraseLead.leadingCoeff = b
    generalize SignType.sign p.trailingCoeff = c
    intro this hl hl' ht
    cases a <;> cases b <;> cases c <;> simp_all <;> omega

/-- A nonzero real polynomial without positive zeros and nonzero constant term has constant term
and leading coefficient of the same sign. -/
private lemma eval_zero_mul_leadingCoeff_pos {r : ℝ[X]} (h0 : r.eval 0 ≠ 0)
    (hpos : ∀ x : ℝ, 0 < x → r.eval x ≠ 0) : 0 < r.eval 0 * r.leadingCoeff := by
  have hr : r ≠ 0 := by rintro rfl; simp at h0
  have hlc : r.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hr
  by_contra hcon
  rw [not_lt] at hcon
  by_cases hdeg : 0 < r.degree
  · have hcont : Continuous fun x => r.eval x := r.continuous
    rcases lt_or_gt_of_ne h0 with h0' | h0'
    · have hlc' : 0 < r.leadingCoeff := by
        rcases lt_or_gt_of_ne hlc with h | h
        · nlinarith
        · exact h
      have := tendsto_atTop_of_leadingCoeff_nonneg r hdeg hlc'.le
      obtain ⟨N, hN⟩ := (this.eventually_gt_atTop 1).and (eventually_gt_atTop 0) |>.exists
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hN.2.le hcont.continuousOn
        (show (0:ℝ) ∈ Set.Icc (r.eval 0) (r.eval N) from ⟨h0'.le, by linarith [hN.1]⟩)
      rcases hc.1.eq_or_lt with h | h
      · subst h; exact h0 hc0
      · exact hpos c h hc0
    · have hlc' : r.leadingCoeff < 0 := by
        rcases lt_or_gt_of_ne hlc with h | h
        · exact h
        · nlinarith
      have := tendsto_atBot_of_leadingCoeff_nonpos r hdeg hlc'.le
      obtain ⟨N, hN⟩ := (this.eventually_lt_atBot (-1)).and (eventually_gt_atTop 0) |>.exists
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hN.2.le hcont.continuousOn
        (show (0:ℝ) ∈ Set.Icc (r.eval N) (r.eval 0) from ⟨by linarith [hN.1], h0'.le⟩)
      rcases hc.1.eq_or_lt with h | h
      · subst h; exact h0 hc0
      · exact hpos c h hc0
  · have hd : r.natDegree = 0 := by
      have : r.degree ≤ 0 := not_lt.mp hdeg
      exact natDegree_eq_zero_iff_degree_le_zero.mpr this
    have : r.eval 0 = r.leadingCoeff := by
      rw [leadingCoeff, hd, ← coeff_zero_eq_eval_zero]
    rw [this] at hcon
    exact absurd hcon (by nlinarith [mul_self_pos.mpr hlc])

/-- Without positive zeros, leading and trailing coefficients have the same sign. -/
private lemma sign_lead_eq_sign_trail {q : ℝ[X]} (hq : q ≠ 0)
    (hpos : ∀ x : ℝ, 0 < x → q.eval x ≠ 0) :
    SignType.sign q.leadingCoeff = SignType.sign q.trailingCoeff := by
  obtain ⟨r, hqr, hnd⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq 0
  simp only [map_zero, sub_zero] at hqr hnd
  have h0 : r.eval 0 ≠ 0 := by
    intro h
    exact hnd (by simpa using dvd_iff_isRoot.mpr h)
  have hr : ∀ x : ℝ, 0 < x → r.eval x ≠ 0 := by
    intro x hx h
    apply hpos x hx
    rw [hqr]; simp [h]
  have key := eval_zero_mul_leadingCoeff_pos h0 hr
  have hlead : q.leadingCoeff = r.leadingCoeff := by
    rw [hqr]; simp [leadingCoeff_mul]
  have htrail : q.trailingCoeff = r.eval 0 := by
    rw [hqr, trailingCoeff_mul]
    have : (X : ℝ[X]) ^ q.rootMultiplicity 0 = monomial (q.rootMultiplicity 0) 1 := by
      simp [X_pow_eq_monomial]
    have hnt : r.natTrailingDegree = 0 :=
      Nat.eq_zero_of_le_zero (natTrailingDegree_le_of_ne_zero (n := 0)
        (by rwa [coeff_zero_eq_eval_zero]))
    rw [this, trailingCoeff_monomial', one_mul, trailingCoeff, hnt, coeff_zero_eq_eval_zero]
  rw [hlead, htrail]
  rcases lt_or_gt_of_ne h0 with h | h
  · have : r.leadingCoeff < 0 := by nlinarith
    simp [sign_neg, h, this]
  · have : 0 < r.leadingCoeff := by nlinarith
    simp [sign_pos, h, this]

/-- Leading and trailing coefficients have the same sign exactly when the number of positive
zeros (with multiplicity) is even. -/
private lemma sign_eq_iff_even_countP (n : ℕ) :
    ∀ p : ℝ[X], p ≠ 0 → p.roots.countP (0 < ·) = n →
      (SignType.sign p.leadingCoeff = SignType.sign p.trailingCoeff ↔ n % 2 = 0) := by
  induction n with
  | zero =>
    intro p hp hn
    refine ⟨fun _ => rfl, fun _ => sign_lead_eq_sign_trail hp ?_⟩
    intro x hx hev
    have hmem : x ∈ p.roots := (mem_roots hp).mpr hev
    have := (Multiset.countP_pos (p := fun x : ℝ => 0 < x)).mpr ⟨x, hmem, hx⟩
    omega
  | succ n ih =>
    intro p hp hn
    obtain ⟨η, hη, hηpos⟩ : ∃ x, x ∈ p.roots ∧ 0 < x := 
      (Multiset.countP_pos (p := fun x : ℝ => 0 < x)).mp (by omega)
    obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots hη)
    have hQ0 : Q ≠ 0 := right_ne_zero_of_mul (hQ ▸ hp)
    have hcnt : Q.roots.countP (0 < ·) = n := by
      have h1 : p.roots.countP (0 < ·) = Q.roots.countP (0 < ·) + 1 := by
        rw [hQ, roots_mul (hQ ▸ hp)]
        simp [hηpos]
      omega
    have hih := ih Q hQ0 hcnt
    have hlead : p.leadingCoeff = Q.leadingCoeff := by
      rw [hQ]; simp [leadingCoeff_mul]
    have hnt : (X - C η).natTrailingDegree = 0 :=
      Nat.eq_zero_of_le_zero (natTrailingDegree_le_of_ne_zero (n := 0)
        (by simp [coeff_zero_eq_eval_zero, hηpos.ne']))
    have htr : p.trailingCoeff = -η * Q.trailingCoeff := by
      have : (X - C η).trailingCoeff = -η := by
        rw [trailingCoeff, hnt, coeff_zero_eq_eval_zero]; simp
      rw [hQ, trailingCoeff_mul, this]
    have hl : SignType.sign Q.leadingCoeff ≠ 0 := by simp [hQ0]
    have ht : SignType.sign Q.trailingCoeff ≠ 0 := by simp [hQ0]
    rw [hlead, htr, sign_mul, Left.sign_neg, sign_pos hηpos]
    revert hih hl ht
    generalize SignType.sign Q.leadingCoeff = a
    generalize SignType.sign Q.trailingCoeff = c
    intro hih hl ht
    cases a <;> cases c <;> simp_all <;> omega

/-- Descartes' Rule of Signs, with parity: for a nonzero real polynomial, the number of sign
variations in the coefficient list exceeds the number of positive zeros (counted with
multiplicity) by an even natural number (PC-062). -/
@[kb "stitzzeager2013" "Theorem 3.10, p. 285"]
theorem descartes_rule_of_signs (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.signVariations = p.roots.countP (0 < ·) + 2 * k := by
  have hle := roots_countP_pos_le_signVariations p
  have hmod := signVariations_mod_two p hp
  have hiff := sign_eq_iff_even_countP _ p hp rfl
  refine ⟨(p.signVariations - p.roots.countP (0 < ·)) / 2, ?_⟩
  by_cases h : SignType.sign p.leadingCoeff = SignType.sign p.trailingCoeff
  · simp only [h, ↓reduceIte] at hmod
    have := hiff.mp h
    omega
  · simp only [h, ↓reduceIte] at hmod
    have : ¬ (p.roots.countP (0 < ·)) % 2 = 0 := fun h' => h (hiff.mpr h')
    omega

/-- Descartes' Rule of Signs for negative zeros, with parity: the sign variations of `p(-x)`
exceed the number of negative zeros of `p` (with multiplicity) by an even natural number
(PC-062). -/
@[kb "stitzzeager2013" "Theorem 3.10, p. 285"]
theorem descartes_rule_of_signs_neg (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, (p.comp (-X)).signVariations = p.roots.countP (· < 0) + 2 * k := by
  have hq : p.comp (-X) ≠ 0 := by
    intro h
    apply hp
    have := congrArg (fun q => q.comp (-X)) h
    simpa [comp_assoc] using this
  obtain ⟨k, hk⟩ := descartes_rule_of_signs (p.comp (-X)) hq
  refine ⟨k, ?_⟩
  rw [hk, roots_comp_neg_X, Multiset.countP_map]
  simp [Multiset.countP_eq_card_filter]

end UndergradKB.Precalculus
