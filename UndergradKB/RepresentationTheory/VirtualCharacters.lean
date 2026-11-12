import UndergradKB.RepresentationTheory.Characters
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Order

/-! # Virtual characters (Etingof et al., §4.6)

A virtual representation is a formal integer combination of irreducible representations; its character is the
same integer combination of irreducible characters (Definition 4.26). We work with the characters directly: the
virtual characters are the `ℤ`-span of the irreducible characters.

Lemma 4.27: a virtual character `ζ` with `(ζ, ζ) = 1` is plus or minus an irreducible character; if moreover
`ζ(1) > 0` (over `ℂ`), it is an irreducible character.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

variable (k G) in
/-- **Etingof et al., Definition 4.26**: the virtual characters, integer combinations of the characters of the
irreducible representations. -/
@[kb "etingof2011" "Definition 4.26, p. 54"]
noncomputable def virtualChars : Submodule ℤ (G → k) := Submodule.span ℤ (irrChars k G)

theorem mem_virtualChars_iff {ζ : G → k} :
    ζ ∈ virtualChars k G ↔ ∃ n : irrChars k G → ℤ, ∑ χ, n χ • (χ : G → k) = ζ := by
  have := Submodule.mem_span_range_iff_exists_fun ℤ (v := fun χ : irrChars k G ↦ (χ : G → k)) (x := ζ)
  rw [Subtype.range_coe] at this
  exact this

theorem pairing_virtual (n : irrChars k G → ℤ) :
    pairing (∑ χ, n χ • (χ : G → k)) (∑ χ, n χ • (χ : G → k)) = ((∑ χ, n χ ^ 2 : ℤ) : k) := by
  classical
  simp only [map_sum, LinearMap.sum_apply, ← Int.cast_smul_eq_zsmul k, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  push_cast
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [Finset.sum_eq_single χ]
  · rw [pairing_irrChars χ.2 χ.2, if_pos rfl]; ring
  · intro ψ _ hψ
    rw [pairing_irrChars ψ.2 χ.2, if_neg (fun h ↦ hψ (Subtype.ext h))]; ring
  · simp

/-- Integers whose squares add up to `1`: exactly one of them is `±1`, the others vanish. -/
theorem exists_of_sum_sq_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℤ)
    (h : ∑ i, n i ^ 2 = 1) : ∃ i, n i ^ 2 = 1 ∧ ∀ j, j ≠ i → n j = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra hall
    push Not at hall
    simp [hall] at h
  have hsplit := Finset.add_sum_erase Finset.univ (fun j ↦ n j ^ 2) (Finset.mem_univ i)
  rw [h] at hsplit
  have hpos : 1 ≤ n i ^ 2 := by
    have := pow_pos (abs_pos.mpr hi) 2
    rw [sq_abs] at this
    omega
  have hrest : ∑ j ∈ Finset.univ.erase i, n j ^ 2 = 0 := by
    have hnn : 0 ≤ ∑ j ∈ Finset.univ.erase i, n j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    omega
  refine ⟨i, by omega, fun j hj ↦ ?_⟩
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (n j))).mp hrest j
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-- **Etingof et al., Lemma 4.27** (sign form, characteristic zero): a virtual character of norm one is an
irreducible character or the negative of one. -/
@[kb "etingof2011" "Lemma 4.27, p. 54"]
theorem mem_irrChars_or_neg_of_pairing_eq_one [CharZero k] {ζ : G → k} (hζ : ζ ∈ virtualChars k G)
    (h1 : pairing ζ ζ = 1) : ζ ∈ irrChars k G ∨ -ζ ∈ irrChars k G := by
  classical
  obtain ⟨n, rfl⟩ := mem_virtualChars_iff.mp hζ
  rw [pairing_virtual] at h1
  have h1' : ∑ χ, n χ ^ 2 = 1 := by exact_mod_cast h1
  obtain ⟨χ, hχ, hrest⟩ := exists_of_sum_sq_eq_one n h1'
  have hsum : ∑ ψ, n ψ • (ψ : G → k) = n χ • (χ : G → k) := by
    rw [Finset.sum_eq_single χ]
    · intro ψ _ hψ; rw [hrest ψ hψ, zero_smul]
    · simp
  rw [hsum]
  rcases sq_eq_one_iff.mp hχ with h | h
  · left; rw [h, one_smul]; exact χ.2
  · right; rw [h, neg_smul, one_smul, neg_neg]; exact χ.2

open scoped ComplexOrder in
/-- **Etingof et al., Lemma 4.27**: over `ℂ`, a virtual character `ζ` with `(ζ, ζ) = 1` and `ζ(1) > 0` is the
character of an irreducible representation. -/
@[kb "etingof2011" "Lemma 4.27, p. 54"]
theorem mem_irrChars_of_pairing_eq_one {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {ζ : G → ℂ} (hζ : ζ ∈ virtualChars ℂ G) (h1 : pairing ζ ζ = 1) (hpos : 0 < ζ 1) :
    ζ ∈ irrChars ℂ G := by
  rcases mem_irrChars_or_neg_of_pairing_eq_one hζ h1 with h | h
  · exact h
  · exfalso
    obtain ⟨X, hX⟩ := h
    have h1 : X.ρ.character 1 = finrank ℂ X.V := char_one _
    rw [show X.ρ.character = -ζ from hX, Pi.neg_apply] at h1
    have : (0 : ℂ) ≤ (finrank ℂ X.V : ℂ) := Nat.cast_nonneg _
    rw [← h1] at this
    exact (lt_irrefl (0 : ℂ)) (lt_of_lt_of_le hpos (neg_nonneg.mp this))

end UndergradKB.RepresentationTheory
