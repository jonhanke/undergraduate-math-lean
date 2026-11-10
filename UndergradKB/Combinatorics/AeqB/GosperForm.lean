import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.Gosper

/-!
# Existence of Gosper's canonical form (Petkovsek–Wilf–Zeilberger, "A = B", Theorem 5.3.1)

Every nonzero rational function `f/g` can be written `a(n) c(n+1) / (b(n) c(n))` with `b, c` monic,
`gcd(a(n), b(n+h)) = 1` for all `h ∈ ℕ`, `gcd(a, c) = 1` and `gcd(b, c(n+1)) = 1`.
The proof follows Step 2 of Gosper's algorithm: while some shift `g(n+h)` has a common factor `s`
with `f`, for the least such `h`, cancel `s(n)/s(n-h)` and recurse on the cancelled pair,
collecting the telescoping factor `∏_{j=1}^h s(n-j)` into `c`.
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.Combinatorics.AeqB
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- `∏_{j=1}^h s(n-j)`. -/
noncomputable def gosperQ (s : K[X]) (h : ℕ) : K[X] :=
  ∏ j ∈ Finset.range h, s.comp (X + C (-((j : K) + 1)))

/-- `∏_{j=0}^{h-1} s(n-j)`. -/
noncomputable def gosperR (s : K[X]) (h : ℕ) : K[X] :=
  ∏ j ∈ Finset.range h, s.comp (X + C (-(j : K)))

theorem gosperQ_comp (s : K[X]) (h : ℕ) : (gosperQ s h).comp (X + 1) = gosperR s h := by
  induction h with
  | zero => simp [gosperQ, gosperR]
  | succ h ih =>
    simp only [gosperQ, gosperR] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_comp, ih, comp_X_add_one_eq,
      comp_shift_comp_shift, show (-((h : K) + 1) + 1) = -(h : K) by ring]

theorem gosperR_mul (s : K[X]) (h : ℕ) :
    gosperR s h * s.comp (X + C (-(h : K))) = s * gosperQ s h := by
  induction h with
  | zero => simp [gosperR, gosperQ]
  | succ h ih =>
    simp only [gosperR, gosperQ] at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast
    linear_combination (s.comp (X + C (-((h : K) + 1)))) * ih

theorem monic_comp_shift {p : K[X]} (hp : p.Monic) (c : K) : (p.comp (X + C c)).Monic := by
  unfold Monic
  rw [leadingCoeff_comp_shift]; exact hp

theorem exists_gosper_form_aux : ∀ (N : ℕ) (f g : K[X]), f.natDegree + g.natDegree = N →
    f ≠ 0 → g ≠ 0 →
    ∃ a b c : K[X], a ∣ f ∧ b ∣ g ∧ a ≠ 0 ∧ b.Monic ∧ c.Monic ∧
      f * (b * c) = g * (a * c.comp (X + 1)) ∧
      (∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) ∧ IsCoprime a c ∧
      IsCoprime b (c.comp (X + 1)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f g hN hf hg
  by_cases hall : ∀ h : ℕ, IsCoprime f (g.comp (X + C (h : K)))
  · have hu : IsUnit (C (g.leadingCoeff)⁻¹ : K[X]) :=
      isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hg)))
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg
    refine ⟨f * C g.leadingCoeff⁻¹, g * C g.leadingCoeff⁻¹, 1,
      Dvd.intro (C g.leadingCoeff) (by
        rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]),
      Dvd.intro (C g.leadingCoeff) (by
        rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]), mul_ne_zero hf hu.ne_zero, monic_mul_leadingCoeff_inv hg, monic_one,
      ?_, ?_, isCoprime_one_right, ?_⟩
    · simp only [one_comp]; ring
    · intro h
      rw [mul_comp, C_comp, isCoprime_mul_unit_right_left hu, isCoprime_mul_unit_right_right hu]
      exact hall h
    · rw [one_comp]; exact isCoprime_one_right
  · push Not at hall
    obtain ⟨h, hbad, hmin⟩ : ∃ h : ℕ, ¬ IsCoprime f (g.comp (X + C (h : K))) ∧
        ∀ h' < h, IsCoprime f (g.comp (X + C (h' : K))) := by
      classical
      refine ⟨Nat.find hall, Nat.find_spec hall, fun h' hh' => ?_⟩
      have := Nat.find_min hall hh'
      push Not at this
      exact this
    obtain ⟨d, hdf, hdG, hdu⟩ : ∃ d, d ∣ f ∧ d ∣ g.comp (X + C (h : K)) ∧ ¬ IsUnit d := by
      by_contra hcon
      push Not at hcon
      exact hbad (isRelPrime_iff_isCoprime.1 (fun d h1 h2 => hcon d h1 h2))
    have hd0 : d ≠ 0 := fun h0 => hf (zero_dvd_iff.1 (h0 ▸ hdf))
    have hdeg : 0 < d.natDegree := by
      by_contra hlt
      push Not at hlt
      have hC : d = C (d.coeff 0) := eq_C_of_natDegree_le_zero hlt
      apply hdu
      rw [hC]
      exact isUnit_C.2 (isUnit_iff_ne_zero.2 (fun h0 => hd0 (by rw [hC, h0, C_0])))
    obtain ⟨s, hsm, hsf, hsG, hsdeg⟩ : ∃ s : K[X], s.Monic ∧ s ∣ f ∧ s ∣ g.comp (X + C (h : K)) ∧
        0 < s.natDegree := by
      have hlc : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hd0
      have hsd : (d * C d.leadingCoeff⁻¹) ∣ d := ⟨C d.leadingCoeff, by
        rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]⟩
      exact ⟨d * C d.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hd0, hsd.trans hdf,
        hsd.trans hdG, by rw [natDegree_mul_C (inv_ne_zero hlc)]; exact hdeg⟩
    obtain ⟨f', hf'⟩ := hsf
    obtain ⟨G', hG'⟩ := hsG
    obtain ⟨t, ht⟩ : ∃ t, t = s.comp (X + C (-(h : K))) := ⟨_, rfl⟩
    obtain ⟨g', hg'⟩ : ∃ g', g' = G'.comp (X + C (-(h : K))) := ⟨_, rfl⟩
    have hgt : g = t * g' := by
      have := congrArg (fun q => q.comp (X + C (-(h : K)))) hG'
      simp only [mul_comp, comp_shift_comp_shift, add_neg_cancel, C_0, add_zero, comp_X] at this
      rw [ht, hg']; exact this
    have hf'0 : f' ≠ 0 := by
      intro h0; apply hf; rw [hf', h0, mul_zero]
    have ht0 : t ≠ 0 := by rw [ht]; exact comp_X_add_C_ne_zero' hsm.ne_zero _
    have hg'0 : g' ≠ 0 := by
      intro h0; apply hg; rw [hgt, h0, mul_zero]
    have hfd : f.natDegree = s.natDegree + f'.natDegree := by
      rw [hf']; exact natDegree_mul hsm.ne_zero hf'0
    have hgd : g.natDegree = s.natDegree + g'.natDegree := by
      rw [hgt, natDegree_mul ht0 hg'0, ht, natDegree_comp_shift]
    obtain ⟨a, b, c', haf, hbg, ha0, hbm, hcm, hid, hi, hii, hiii⟩ :=
      ih (f'.natDegree + g'.natDegree) (by omega) f' g' rfl hf'0 hg'0
    have haf0 : a ∣ f := haf.trans (Dvd.intro_left s hf'.symm)
    have hbg0 : b ∣ g := hbg.trans (Dvd.intro_left t hgt.symm)
    have hsf : s ∣ f := Dvd.intro f' hf'.symm
    have hsG : s ∣ g.comp (X + C (h : K)) := Dvd.intro G' hG'.symm
    refine ⟨a, b, c' * gosperQ s h, haf0, hbg0, ha0, hbm, ?_, ?_, hi, ?_, ?_⟩
    · exact hcm.mul (monic_prod_of_monic _ _ fun j _ => monic_comp_shift hsm _)
    · have F1 := gosperR_mul s h
      rw [← ht] at F1
      rw [mul_comp, gosperQ_comp, hf', hgt]
      linear_combination (s * gosperQ s h) * hid
        - (g' * a * c'.comp (X + 1)) * F1
    · refine IsCoprime.mul_right hii (IsCoprime.prod_right fun j hj => ?_)
      have hj' : j < h := Finset.mem_range.1 hj
      have hcast : (h : K) + -((j : K) + 1) = ((h - 1 - j : ℕ) : K) := by
        rw [show h - 1 - j = h - (j + 1) by omega, Nat.cast_sub (by omega)]
        push_cast; ring
      have hdvd : s.comp (X + C (-((j : K) + 1))) ∣ g.comp (X + C ((h - 1 - j : ℕ) : K)) := by
        have := dvd_comp_shift hsG (-((j : K) + 1))
        rwa [comp_shift_comp_shift, hcast] at this
      exact ((hmin (h - 1 - j) (by omega)).of_isCoprime_of_dvd_left haf0).of_isCoprime_of_dvd_right
        hdvd
    · rw [mul_comp, gosperQ_comp]
      refine IsCoprime.mul_right hiii (IsCoprime.prod_right fun j hj => ?_)
      have hj' : j < h := Finset.mem_range.1 hj
      have hdvd : s.comp (X + C (-(j : K))) ∣ f.comp (X + C (-(j : K))) :=
        dvd_comp_shift hsf (-(j : K))
      have hcop := isCoprime_comp_shift (hmin j hj') (-(j : K))
      rw [comp_shift_comp_shift, add_neg_cancel, C_0, add_zero, comp_X] at hcop
      exact (hcop.symm.of_isCoprime_of_dvd_left hbg0).of_isCoprime_of_dvd_right hdvd

/-- CO-404. Theorem 5.3.1 (existence of Gosper's canonical form): for nonzero polynomials `f, g`
(the rational function `r = f/g`, over a field of characteristic zero) there are polynomials
`a, b, c` with `b, c` monic such that `r = a(n) c(n+1) / (b(n) c(n))`, written without division as
`f b c = g a c(n+1)`, and (i) `gcd(a(n), b(n+h)) = 1` for every `h ∈ ℕ`, (ii) `gcd(a, c) = 1`,
(iii) `gcd(b(n), c(n+1)) = 1`. -/
@[kb "petkovsekwilfzeilberger1996" "Theorem 5.3.1, p. 92"]
theorem exists_gosper_form (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ a b c : K[X], a ≠ 0 ∧ b.Monic ∧ c.Monic ∧
      f * (b * c) = g * (a * c.comp (X + 1)) ∧
      (∀ h : ℕ, IsCoprime a (b.comp (X + C (h : K)))) ∧ IsCoprime a c ∧
      IsCoprime b (c.comp (X + 1)) := by
  obtain ⟨a, b, c, -, -, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_gosper_form_aux _ f g rfl hf hg
  exact ⟨a, b, c, h1, h2, h3, h4, h5, h6, h7⟩

end UndergradKB.Combinatorics.AeqB
