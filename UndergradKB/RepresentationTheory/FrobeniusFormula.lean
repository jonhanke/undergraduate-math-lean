import UndergradKB.RepresentationTheory.FrobeniusCounting
import UndergradKB.RepresentationTheory.FrobeniusDeterminant
import UndergradKB.Common.Attr

/-! # Orthonormality of the functions `θ_λ` (Etingof et al., proof of Theorem 4.47)

For a vector `λ = (λ_1 ≥ ⋯ ≥ λ_N)` of naturals with sum `n`, `θ_λ(g)` (`frobChar n N λ g`) is the coefficient of
`x^{λ + ρ}` in `Δ(x) ∏_m (x_1^m + ⋯ + x_N^m)^{i_m(g)}`.

* `frobChar_eq_sum'`: `θ_λ = ∑_σ sign σ · c_{λ + ρ - ρ σ⁻¹}`, where `c_α(g)` is the coefficient of `x^α` in
  `∏_m (x_1^m + ⋯ + x_N^m)^{i_m(g)}`, the character of the permutation representation on colourings of content `α`.
* `frobChar_mem_virtualChars`: hence `θ_λ` is a virtual character.
* `pairing_frobChar`: `(θ_λ, θ_μ) = δ_{λμ}`, by Burnside's lemma (the pairing of `c_α` and `c_β` counts
  contingency tables) and the Cauchy identity (`FrobeniusDet.signed_sum_contingency_strictAnti`).
* `frobChar_mem_irrChars_or_neg`: so `θ_λ` or `-θ_λ` is an irreducible character (Lemma 4.27).
-/

namespace UndergradKB.RepresentationTheory

open Finset FrobeniusDet

variable {n N : ℕ}

/-- The exponent vector `λ + ρ - ρ σ⁻¹` of the term of `θ_λ` indexed by `σ`. -/
def termExp (lam : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) : Fin N → ℕ :=
  fun i => lam i + rhoExp N i - rhoExp N (σ.symm i)

/-- The term of `θ_λ` indexed by `σ` is present: `ρ σ⁻¹ ≤ λ + ρ` componentwise. -/
def TermOK (lam : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ i, rhoExp N (σ.symm i) ≤ lam i + rhoExp N i

instance (lam : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) : Decidable (TermOK lam σ) :=
  inferInstanceAs (Decidable (∀ _i, _ ≤ _))

/-- The coefficient function `c_α(g)`. -/
noncomputable abbrev coeffChar (n N : ℕ) (α : Fin N → ℕ) (g : Equiv.Perm (Fin n)) : ℂ :=
  (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α)

/-- `θ_λ = ∑_σ sign σ · c_{λ + ρ - ρ σ⁻¹}` (terms with a negative exponent omitted). -/
theorem frobChar_eq_sum' (lam : Fin N → ℕ) (g : Equiv.Perm (Fin n)) :
    frobChar n N lam g = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      (if TermOK lam σ then coeffChar n N (termExp lam σ) g else 0) := by
  rw [frobChar_eq_sum]
  refine sum_congr rfl fun σ _ => ?_
  have hle : deltaExp σ ≤ shiftExp lam ↔ TermOK lam σ := by
    simp only [Finsupp.le_def, deltaExp_apply, TermOK, shiftExp]
    exact Iff.rfl
  have hsub : shiftExp lam - deltaExp σ = Finsupp.equivFunOnFinite.symm (termExp lam σ) := by
    ext i
    simp [shiftExp, deltaExp_apply, termExp]
  by_cases h : TermOK lam σ
  · rw [if_pos (hle.2 h), if_pos h, hsub]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

lemma sum_termExp {lam : Fin N → ℕ} {σ : Equiv.Perm (Fin N)} (h : TermOK lam σ) :
    ∑ i, termExp lam σ i = ∑ i, lam i := by
  unfold termExp
  rw [sum_tsub_distrib _ fun i _ => h i, sum_add_distrib,
    Equiv.sum_comp σ.symm (fun i => rhoExp N i)]
  omega

/-- **`θ_λ` is a virtual character** (an integer combination of permutation characters). -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem frobChar_mem_virtualChars (lam : Fin N → ℕ) :
    frobChar n N lam ∈ virtualChars ℂ (Equiv.Perm (Fin n)) := by
  have : frobChar n N lam = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ)) •
      (if TermOK lam σ then coeffChar n N (termExp lam σ) else 0) := by
    funext g
    rw [frobChar_eq_sum', Finset.sum_apply]
    refine sum_congr rfl fun σ _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]
    split_ifs <;> simp
  rw [this]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_mem _ _ ?_
  split_ifs
  · exact coeffChar_mem_virtualChars n N _
  · exact Submodule.zero_mem _

lemma strictAnti_add_rho {lam : Fin N → ℕ} (hl : Antitone lam) :
    StrictAnti fun i => lam i + rhoExp N i := by
  intro i j hij
  have h1 := hl hij.le
  have h2 : rhoExp N j < rhoExp N i := by
    simp only [rhoExp, Fin.val_rev]
    have := i.isLt
    have := j.isLt
    have : (i : ℕ) < j := hij
    omega
  simp only
  omega

/-- **Orthonormality of the `θ_λ`.**  For `λ, μ` nonincreasing with sum `n`, `(θ_λ, θ_μ) = δ_{λμ}`. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem pairing_frobChar {lam mu : Fin N → ℕ} (hl : Antitone lam) (hm : Antitone mu)
    (hsl : ∑ i, lam i = n) (hsm : ∑ i, mu i = n) :
    pairing (frobChar n N lam) (frobChar n N mu) = if lam = mu then 1 else 0 := by
  classical
  have hcard : (Nat.card (Equiv.Perm (Fin n)) : ℂ) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hsum : ∑ g : Equiv.Perm (Fin n), frobChar n N lam g * frobChar n N mu g⁻¹ =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤ) : ℂ) *
          (if TermOK lam σ ∧ TermOK mu τ then (n.factorial : ℂ) *
            contingency (termExp lam σ) (termExp mu τ) else 0) := by
    simp_rw [frobChar_eq_sum', coeffChar, coeff_cyclePoly_inv, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun σ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun τ _ => ?_
    by_cases hP : TermOK lam σ
    · by_cases hQ : TermOK mu τ
      · simp only [hP, hQ, if_true, and_self]
        rw [← sum_coeff_cyclePoly_mul n N _ _ ((sum_termExp hP).trans hsl) ((sum_termExp hQ).trans hsm),
          mul_sum]
        refine sum_congr rfl fun g _ => ?_
        push_cast
        ring
      · simp [hP, hQ]
    · simp [hP]
  rw [pairing_apply, hsum, hcard, mul_sum]
  have key := signed_sum_contingency_strictAnti (strictAnti_add_rho hl) (strictAnti_add_rho hm)
  have hab : ((fun i => lam i + rhoExp N i) = fun i => mu i + rhoExp N i) ↔ lam = mu := by
    constructor
    · intro h
      funext i
      have := congrFun h i
      simpa using this
    · rintro rfl
      rfl
  simp only [hab] at key
  rw [← key]
  refine sum_congr rfl fun σ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  unfold TermOK termExp
  split_ifs
  · field_simp
  · simp

/-- **Lemma 4.27 applied to `θ_λ`.**  `θ_λ` or `-θ_λ` is an irreducible character of `S_n`. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem frobChar_mem_irrChars_or_neg {lam : Fin N → ℕ} (hl : Antitone lam) (hsl : ∑ i, lam i = n) :
    frobChar n N lam ∈ irrChars ℂ (Equiv.Perm (Fin n)) ∨
      -frobChar n N lam ∈ irrChars ℂ (Equiv.Perm (Fin n)) := by
  refine mem_irrChars_or_neg_of_pairing_eq_one (frobChar_mem_virtualChars lam) ?_
  rw [pairing_frobChar hl hl hsl hsl, if_pos rfl]

end UndergradKB.RepresentationTheory
