import UndergradKB.RepresentationTheory.Characters

/-! # The Frobenius-Schur count of square roots of `1` (Etingof et al., §4.1)

For an irreducible character `χ` the Frobenius-Schur indicator is `FS(χ) = |G|⁻¹ ∑_g χ(g²)`; the book shows it is `0`,
`1` or `-1` according as the representation is of complex, real or quaternionic type. Here we take the averaged
formula as the indicator and prove the counting formula of Theorem 4.4: the number of `g` with `g² = 1` is
`∑_V dim V · FS(V)`, together with Corollary 4.5. The identification of the indicator with the type of the
representation (via invariant bilinear forms) is not formalized here.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open Representation Module

variable {k : Type u} {G : Type v} [Field k] [Group G] [Fintype G] [IsAlgClosed k] [Invertible (Nat.card G : k)]

/-- The Frobenius-Schur indicator of a function on `G`, `|G|⁻¹ ∑_g f(g²)` (for an irreducible character, the
book's `FS(V)`). -/
noncomputable def fsIndicator (f : G → k) : k := (Nat.card G : k)⁻¹ * ∑ g : G, f (g ^ 2)

open scoped Classical in
/-- **Etingof et al., Theorem 4.4**: the number of elements `g` with `g² = 1` equals the sum over the irreducible
representations `V` of `dim V · FS(V)` (here `χ(1) = dim V`, and `FS` is the averaged indicator). -/
@[kb "etingof2011" "Theorem 4.4, p. 47"]
theorem sum_irrChars_one_mul_fsIndicator :
    ∑ χ : irrChars k G, (χ : G → k) 1 * fsIndicator (χ : G → k) =
      ((Finset.univ.filter fun g : G ↦ g ^ 2 = 1).card : k) := by
  have hG : (Nat.card G : k) ≠ 0 := NeZero.ne _
  simp only [fsIndicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ g : G, ∑ χ : irrChars k G, (χ : G → k) 1 * ((Nat.card G : k)⁻¹ * (χ : G → k) (g ^ 2)) =
      if g ^ 2 = 1 then 1 else 0 := by
    intro g
    have h := sum_irrChars_mul_inv (k := k) (g ^ 2) 1
    simp only [inv_one, isConj_one_left] at h
    have : ∑ χ : irrChars k G, (χ : G → k) 1 * ((Nat.card G : k)⁻¹ * (χ : G → k) (g ^ 2)) =
        (Nat.card G : k)⁻¹ * ∑ χ : irrChars k G, (χ : G → k) (g ^ 2) * (χ : G → k) 1 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ ↦ by ring
    rw [this, h]
    split_ifs with h2
    · rw [h2]
      have hc : Subgroup.centralizer {(1 : G)} = ⊤ := by
        ext x; simp [Subgroup.mem_centralizer_singleton_iff]
      rw [hc, Subgroup.card_top, inv_mul_cancel₀ hG]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun g _ ↦ key g, Finset.sum_boole]

open scoped Classical in
/-- **Etingof et al., Corollary 4.5**: if every irreducible representation has indicator `1` (all are of real type),
the sum of the dimensions of the irreducible representations is the number of `g` with `g² = 1`. -/
@[kb "etingof2011" "Corollary 4.5, p. 48"]
theorem sum_irrChars_one_of_fsIndicator_eq_one (h : ∀ χ : irrChars k G, fsIndicator (χ : G → k) = 1) :
    ∑ χ : irrChars k G, (χ : G → k) 1 = ((Finset.univ.filter fun g : G ↦ g ^ 2 = 1).card : k) := by
  rw [← sum_irrChars_one_mul_fsIndicator]
  exact Finset.sum_congr rfl fun χ _ ↦ by rw [h χ, mul_one]

end UndergradKB.RepresentationTheory
