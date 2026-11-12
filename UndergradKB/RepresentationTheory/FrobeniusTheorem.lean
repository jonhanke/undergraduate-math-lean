import UndergradKB.RepresentationTheory.FrobeniusDominance
import UndergradKB.RepresentationTheory.FrobeniusKostka
import UndergradKB.RepresentationTheory.FrobeniusDimension
import UndergradKB.Common.Attr

/-! # The Frobenius character formula (Etingof et al., Theorem 4.47)

**Theorem 4.47.**  Let `λ` be a partition of `n` with at most `N` parts, `λ_1 ≥ ⋯ ≥ λ_N`, and `ρ = (N - 1, …, 0)`.
For a permutation `g` of `{1, …, n}` with `i_m` cycles of length `m`, the character of the Specht module `V_λ` at
`g` is the coefficient of `x^{λ + ρ}` in `Δ(x) ∏_m (x_1^m + ⋯ + x_N^m)^{i_m}`, where `Δ = ∏_{i<j} (x_i - x_j)`
(`frobenius_character_formula`).

Proof (the book's): `θ_λ` is a virtual character of norm one (`FrobeniusFormula.lean`), so `±θ_λ` is irreducible.
Expanding `Δ`, `θ_λ = ∑_σ sign σ · χ_{U_{λ + ρ - ρ σ⁻¹}}` with permutation characters `χ_U`; the pairing of `χ_{U_μ}`
with `χ_{V_λ}` is the Kostka number `K_{λμ}`, which is `1` for `μ = λ` and `0` when `μ` strictly dominates `λ`
somewhere, as happens for `σ ≠ 1` (`FrobeniusDominance.lean`).  Hence `(θ_λ, χ_{V_λ}) = 1` and `θ_λ = χ_{V_λ}`.
-/

namespace UndergradKB.RepresentationTheory

open Finset

variable {n N : ℕ}

lemma frobChar_eq_sum_smul (lam : Fin N → ℕ) :
    frobChar n N lam = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ)) •
      (if TermOK lam σ then coeffChar n N (termExp lam σ) else 0) := by
  funext g
  rw [frobChar_eq_sum', Finset.sum_apply]
  refine sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, zsmul_eq_mul]
  split_ifs <;> simp

lemma sum_rowLen_eq (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    ∑ j : Fin N, la.1.rowLen j = n := by
  have h1 : ∑ j : Fin N, la.1.rowLen j = ∑ i ∈ range N, la.1.rowLen i :=
    Fin.sum_univ_eq_sum_range (fun i => la.1.rowLen i) N
  have h2 : ∑ i ∈ range N, la.1.rowLen i = ∑ i ∈ range (la.1.colLen 0), la.1.rowLen i := by
    refine (sum_subset (range_subset_range.2 hN) fun i hi hni => ?_).symm
    simp only [mem_range, not_lt] at hni
    rw [← Nat.le_zero, ← not_lt, ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    omega
  have h3 : ∑ i ∈ range (la.1.colLen 0), la.1.rowLen i = la.1.card := by
    rw [← YoungDiagram.sum_rowLens_eq_card, Finset.sum_eq_multiset_sum]
    simp [YoungDiagram.rowLens, Finset.range_val, Multiset.range]
  rw [h1, h2, h3, la.2]

/-- **Theorem 4.47 (Frobenius character formula).** -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem frobenius_character_formula (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    ((spechtChar n la : irrChars ℂ (Equiv.Perm (Fin n))) : Equiv.Perm (Fin n) → ℂ) =
      frobChar n N (fun j => la.1.rowLen j) := by
  classical
  set lam : Fin N → ℕ := fun j => la.1.rowLen j with hlam
  have hl : Antitone lam := fun i j hij => la.1.rowLen_anti i j hij
  have hs : ∑ i, lam i = n := sum_rowLen_eq la hN
  set χ : Equiv.Perm (Fin n) → ℂ := (spechtChar n la).1
  have hχ : χ ∈ irrChars ℂ (Equiv.Perm (Fin n)) := (spechtChar n la).2
  -- the pairing of each term with `χ_{V_λ}`
  have hterm : ∀ σ : Equiv.Perm (Fin N), TermOK lam σ →
      pairing (coeffChar n N (termExp lam σ)) χ = if σ = 1 then 1 else 0 := by
    intro σ hP
    by_cases hσ : σ = 1
    · subst hσ
      have : termExp lam 1 = lam := by
        funext i
        show lam i + rhoExp N i - rhoExp N i = lam i
        omega
      rw [this, if_pos rfl]
      have := pairing_coeffChar_spechtChar n N la la hN
      rw [kostka_self] at this
      exact_mod_cast this
    · rw [if_neg hσ]
      set α := termExp lam σ
      set π := Tuple.sortDesc α
      have hπ : Antitone (α ∘ π) := antitone_comp_sortDesc α
      have hsα : ∑ i, (α ∘ π) i = n := by
        rw [Function.comp_def, Equiv.sum_comp π α]
        exact (sum_termExp hP).trans hs
      obtain ⟨mu, hmuN, hmu⟩ := exists_diagram_of_antitone (α ∘ π) hπ hsα
      have hc : coeffChar n N α = fun g => (cyclePoly n N g).coeff
          (Finsupp.equivFunOnFinite.symm fun j : Fin N => mu.1.rowLen j) := by
        funext g
        rw [coeffChar, ← coeff_cyclePoly_comp n N g α π]
        congr 2
        funext j
        exact (hmu j).symm
      rw [hc, pairing_coeffChar_spechtChar n N mu la hmuN, Nat.cast_eq_zero]
      refine kostka_eq_zero_of_not_rowDominance la mu fun hdom => ?_
      obtain ⟨k, hk, hlt⟩ := exists_pre_lt_termExp hσ hP hπ
      have h1 := hdom k
      rw [sum_range_eq_pre _ hk, sum_range_eq_pre _ hk] at h1
      have : (fun j : Fin N => mu.1.rowLen j) = α ∘ π := funext hmu
      rw [this] at h1
      exact absurd h1 (not_le.2 hlt)
  have hpair : pairing (frobChar n N lam) χ = 1 := by
    rw [frobChar_eq_sum_smul, map_sum, LinearMap.sum_apply, sum_eq_single (1 : Equiv.Perm (Fin N))]
    · have h1 : TermOK lam 1 := fun i => by show rhoExp N i ≤ lam i + rhoExp N i; omega
      rw [if_pos h1, LinearMap.map_smul_of_tower, LinearMap.smul_apply, hterm 1 h1, if_pos rfl]
      simp
    · intro σ _ hσ
      split_ifs with hP
      · rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, hterm σ hP, if_neg hσ, smul_zero]
      · simp
    · simp
  rcases frobChar_mem_irrChars_or_neg hl hs with h | h
  · have := pairing_irrChars h hχ
    rw [hpair] at this
    split_ifs at this with heq
    · exact heq.symm
    · exact absurd this one_ne_zero
  · exfalso
    have := pairing_irrChars h hχ
    rw [map_neg, LinearMap.neg_apply, hpair] at this
    split_ifs at this <;> norm_num at this

/-- **Formula (5) (dimension of `V_λ`).**  With `l_j = λ_j + N - j` (`0`-based: `λ_j + (N - 1 - j)`),
`dim V_λ = n! ∏_{i<j} (l_i - l_j) / ∏_j l_j!`. -/
@[kb "etingof2011" "formula (5), p. 63"]
theorem finrank_specht_eq (la : DiagramsOfSize n) (hN : la.1.colLen 0 ≤ N) :
    (Module.finrank ℂ (spechtIrrRep n la).V : ℂ) =
      ((n.factorial : ℂ) * ∏ i : Fin N, ∏ j ∈ Ioi i,
        ((((la.1.rowLen i + rhoExp N i : ℕ)) : ℂ) - ((la.1.rowLen j + rhoExp N j : ℕ) : ℂ))) /
      ∏ i : Fin N, (((la.1.rowLen i + rhoExp N i).factorial : ℕ) : ℂ) := by
  have h := congrFun (frobenius_character_formula la hN) 1
  rw [frobChar_one_eq _ (sum_rowLen_eq la hN)] at h
  rw [← h]
  exact ((spechtIrrRep n la).ρ.char_one).symm

end UndergradKB.RepresentationTheory
