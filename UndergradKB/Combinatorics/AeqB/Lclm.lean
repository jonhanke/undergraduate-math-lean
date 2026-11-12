import Mathlib.Algebra.SkewPolynomial.Basic
import Mathlib.Tactic.NoncommRing
import UndergradKB.Common.Attr
import UndergradKB.Combinatorics.AeqB.OperatorsMore

/-!
# Least common left multiples of recurrence operators (Petkovsek–Wilf–Zeilberger, "A = B", p. 172)
-/

noncomputable section

namespace UndergradKB.Combinatorics.AeqB

section Lclm

variable {F : Type*} [Field F] [MulSemiringAction (Multiplicative ℕ) F]

theorem skew_coeff_sum {ι : Type*} (s : Finset ι) (f : ι → SkewPolynomial F) (n : ℕ) :
    SkewPolynomial.coeff (∑ i ∈ s, f i) n = ∑ i ∈ s, SkewPolynomial.coeff (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SkewPolynomial.coeff_add, ih]

theorem skew_coeff_top_mul (P Q : SkewPolynomial F) {p q : ℕ} (hp : ∀ k ∈ P.support, k ≤ p)
    (hq : ∀ k ∈ Q.support, k ≤ q) (hpS : p ∈ P.support) (hqS : q ∈ Q.support) :
    SkewPolynomial.coeff (P * Q) (p + q) =
      P.coeff p * (⇑(SkewPolynomial.φ : F →+* F))^[p] (Q.coeff q) := by
  have hP : P = ∑ i ∈ P.support, SkewPolynomial.monomial i (P.coeff i) :=
    (SkewPolynomial.sum_monomial P).symm.trans (SkewPolynomial.sum_def P _)
  have hQ : Q = ∑ i ∈ Q.support, SkewPolynomial.monomial i (Q.coeff i) :=
    (SkewPolynomial.sum_monomial Q).symm.trans (SkewPolynomial.sum_def Q _)
  have key : P * Q = ∑ i ∈ P.support, ∑ j ∈ Q.support, SkewPolynomial.monomial (i + j)
      (P.coeff i * (⇑(SkewPolynomial.φ : F →+* F))^[i] (Q.coeff j)) := by
    calc P * Q = (∑ i ∈ P.support, SkewPolynomial.monomial i (P.coeff i)) *
        (∑ i ∈ Q.support, SkewPolynomial.monomial i (Q.coeff i)) := by rw [← hP, ← hQ]
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => SkewPolynomial.monomial_mul_monomial _ _ _ _
  rw [key, skew_coeff_sum, Finset.sum_eq_single p ?_ (fun h => absurd hpS h)]
  · rw [skew_coeff_sum, Finset.sum_eq_single q ?_ (fun h => absurd hqS h)]
    · simp [SkewPolynomial.coeff_monomial]
    · intro j hj hjq
      rw [SkewPolynomial.coeff_monomial, if_neg]
      have := hq j hj
      omega
  · intro i hi hip
    rw [skew_coeff_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [SkewPolynomial.coeff_monomial, if_neg]
    have := hp i hi
    have := hq j hj
    omega

theorem skew_top_exists {P : SkewPolynomial F} (hP : P ≠ 0) :
    ∃ p ∈ P.support, ∀ k ∈ P.support, k ≤ p := by
  have hne : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hP (SkewPolynomial.support_eq_empty.1 he)
  obtain ⟨p, hp, h⟩ := Finset.exists_max_image P.support id hne
  exact ⟨p, hp, h⟩

/-- Skew polynomials over a field (with an action) have no zero divisors. -/
theorem skew_mul_ne_zero {P Q : SkewPolynomial F} (hP : P ≠ 0) (hQ : Q ≠ 0) : P * Q ≠ 0 := by
  obtain ⟨p, hpS, hp⟩ := skew_top_exists hP
  obtain ⟨q, hqS, hq⟩ := skew_top_exists hQ
  intro h
  have h1 := skew_coeff_top_mul P Q hp hq hpS hqS
  rw [h] at h1
  have ha : P.coeff p ≠ 0 := SkewPolynomial.mem_support_iff.1 hpS
  have hb : Q.coeff q ≠ 0 := SkewPolynomial.mem_support_iff.1 hqS
  exact mul_ne_zero ha (skew_phi_iterate_ne_zero hb p) (by simpa using h1.symm)

theorem skew_common_multiple_aux (n : ℕ) : ∀ L₁ L₂ : SkewPolynomial F, L₁ ≠ 0 → L₂ ≠ 0 →
    skewOrder L₂ = n → ∃ A B : SkewPolynomial F, A * L₁ = B * L₂ ∧ A * L₁ ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L₁ L₂ h1 h2 hn
  obtain ⟨Q, R, hQR, hRs⟩ := skew_right_division L₁ L₂ h2
  by_cases hR : R = 0
  · exact ⟨1, Q, by rw [hQR, hR]; simp, by simpa using h1⟩
  · have hlt : skewOrder R < n := hn ▸ skewOrder_lt_of_support hR hRs
    obtain ⟨A, B, hAB, hne⟩ := ih _ hlt L₂ R h2 hR rfl
    have hB : B ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hAB)
    refine ⟨B, B * Q + A, ?_, skew_mul_ne_zero hB h1⟩
    rw [add_mul, mul_assoc, hAB, hQR]
    noncomm_ring

/-- CO-507. Existence of a nonzero common left multiple of two nonzero recurrence operators. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem skew_common_multiple (L₁ L₂ : SkewPolynomial F) (h₁ : L₁ ≠ 0) (h₂ : L₂ ≠ 0) :
    ∃ A B : SkewPolynomial F, A * L₁ = B * L₂ ∧ A * L₁ ≠ 0 :=
  skew_common_multiple_aux _ L₁ L₂ h₁ h₂ rfl

/-- CO-507. Least common left multiples: two nonzero recurrence operators have a nonzero common
left multiple `M` (of minimal order), and every common left multiple is a left multiple of `M`. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem skew_lclm (L₁ L₂ : SkewPolynomial F) (h₁ : L₁ ≠ 0) (h₂ : L₂ ≠ 0) :
    ∃ M, M ≠ 0 ∧ (∃ A, M = A * L₁) ∧ (∃ B, M = B * L₂) ∧
      ∀ P, (∃ A, P = A * L₁) → (∃ B, P = B * L₂) → ∃ Q, P = Q * M := by
  classical
  have hex : ∃ n, ∃ M : SkewPolynomial F, M ≠ 0 ∧ (∃ A, M = A * L₁) ∧ (∃ B, M = B * L₂) ∧
      skewOrder M = n := by
    obtain ⟨A, B, hAB, hne⟩ := skew_common_multiple L₁ L₂ h₁ h₂
    exact ⟨_, A * L₁, hne, ⟨A, rfl⟩, ⟨B, hAB⟩, rfl⟩
  obtain ⟨M, hM0, ⟨A₀, hA₀⟩, ⟨B₀, hB₀⟩, hMn⟩ := Nat.find_spec hex
  refine ⟨M, hM0, ⟨A₀, hA₀⟩, ⟨B₀, hB₀⟩, ?_⟩
  rintro P ⟨A, hA⟩ ⟨B, hB⟩
  obtain ⟨Q, R, hQR, hRs⟩ := skew_right_division P M hM0
  have hRe : R = P - Q * M := by rw [hQR]; abel
  refine ⟨Q, ?_⟩
  by_cases hR : R = 0
  · rw [hQR, hR, add_zero]
  · exfalso
    have hlt : skewOrder R < skewOrder M := skewOrder_lt_of_support hR hRs
    have hle : Nat.find hex ≤ skewOrder R := Nat.find_min' hex
      ⟨R, hR, ⟨A - Q * A₀, by rw [hRe, hA, sub_mul, mul_assoc, ← hA₀]⟩,
        ⟨B - Q * B₀, by rw [hRe, hB, sub_mul, mul_assoc, ← hB₀]⟩, rfl⟩
    omega

end Lclm

/-- CO-507, book shape: least common left multiples of recurrence operators with rational
function coefficients. -/
@[kb "petkovsekwilfzeilberger1996" "text, p. 172"]
theorem ratfunc_lclm {K : Type*} [Field K] [CharZero K] (L₁ L₂ : SkewPolynomial (RatFunc K))
    (h₁ : L₁ ≠ 0) (h₂ : L₂ ≠ 0) :
    ∃ M, M ≠ 0 ∧ (∃ A, M = A * L₁) ∧ (∃ B, M = B * L₂) ∧
      ∀ P, (∃ A, P = A * L₁) → (∃ B, P = B * L₂) → ∃ Q, P = Q * M :=
  skew_lclm L₁ L₂ h₁ h₂

end UndergradKB.Combinatorics.AeqB

end
