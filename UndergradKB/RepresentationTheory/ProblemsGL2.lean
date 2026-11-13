import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.ProblemsFiniteGroups

/-! # Tensor squares for the dihedral and Heisenberg groups (Etingof et al., Problems 3.17 (b), 3.25)

Both results are identities of class functions, obtained from the character lists of
`ProblemsFiniteGroups.lean` together with the product formula `Representation.char_tensor`.

Problem 3.17 (b), dihedral group of order `2N` with `V = dihRep 1` the rotation representation:

* `dihChar_one_sq`: `χ_V² = 1 + sgn + θ_2`, where `1 = dihLinChar 0 _ false`, `sgn = dihLinChar 0 _ true` and
  `θ_2 = dihChar 2` is the character of the two-dimensional representation of index `2`.
* `character_tprod_dihRep_one`: the same statement for the character of the representation `V ⊗ V`.
* `isIrreducible_dihRep_two`: the summand `ρ_2` is irreducible as soon as `4 ≠ 0` in `ZMod N`.

Problem 3.25, Heisenberg group `Heis p` of Problem 3.18:

* `repChar_psi_apply`, `repChar_psi_eq_zero`: the `p`-dimensional irreducible characters `repChar (psi k)`
  (`k ≠ 0`) vanish outside the centre and take the value `p ψ_k(-w)` at the central element `(0, 0, w)`.
* `linHom_mul_linHom`, `linHom_mul_repChar_psi`, `repChar_psi_mul_repChar_psi`: products of irreducible
  characters.  Two linear characters multiply to the linear character with the sum of the parameters; a linear
  character times a `p`-dimensional one gives the latter back; and for `k + l ≠ 0` the product of
  `repChar (psi k)` and `repChar (psi l)` is `p` times `repChar (psi (k + l))`, whereas
  `repChar (psi k) * repChar (psi (-k))` is the sum of all `p²` linear characters.
* `character_tprod_rep_psi`: the same identities for the characters of the tensor product representations.

Differences from the book: the identities are stated for characters (class functions), which determine the
representations by complete reducibility; the explicit isomorphism of representations is not constructed.
Only `V = dihRep 1` is used for the dihedral group (any faithful rotation representation is isomorphic to it).
-/

set_option linter.unusedSectionVars false

namespace UndergradKB.RepresentationTheory

open Representation Module DihedralGroup

section Dihedral

variable {N : ℕ} [NeZero N]

/-- The trivial character of the dihedral group, as the linear character with parameters `(0, +1)`. -/
noncomputable def dihTrivChar (N : ℕ) [NeZero N] : DihedralGroup N → ℂ :=
  dihLinChar (0 : ZMod N) (add_zero 0) false

/-- The sign character (`r i ↦ 1`, `sr i ↦ -1`) of the dihedral group. -/
noncomputable def dihSignChar (N : ℕ) [NeZero N] : DihedralGroup N → ℂ :=
  dihLinChar (0 : ZMod N) (add_zero 0) true

lemma dihTrivChar_r (i : ZMod N) : dihTrivChar N (r i) = 1 := by
  simp [dihTrivChar, dihLinChar, dihLinHom_r]

lemma dihTrivChar_sr (i : ZMod N) : dihTrivChar N (sr i) = 1 := by
  simp [dihTrivChar, dihLinChar, dihLinHom_sr, signC]

lemma dihSignChar_r (i : ZMod N) : dihSignChar N (r i) = 1 := by
  simp [dihSignChar, dihLinChar, dihLinHom_r]

lemma dihSignChar_sr (i : ZMod N) : dihSignChar N (sr i) = -1 := by
  simp [dihSignChar, dihLinChar, dihLinHom_sr, signC]

/-- **Problem 3.17 (b).**  The square of the character of the rotation representation `V` of the dihedral group
is the sum of the trivial character, the sign character and the character `θ_2` of the representation `ρ_2`
(rotation by twice the angle), so `V ⊗ V = 1 ⊕ sgn ⊕ ρ_2`. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem dihChar_one_sq : dihChar (1 : ZMod N) * dihChar (1 : ZMod N) =
    dihTrivChar N + dihSignChar N + dihChar (2 : ZMod N) := by
  funext g
  cases g with
  | r i =>
    have h3 := ee_ne_zero (N := N) i
    have h2 : ee ((2 : ZMod N) * i) = ee i * ee i := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    simp only [Pi.mul_apply, Pi.add_apply, dihChar, dihTrivChar_r, dihSignChar_r, one_mul, h2]
    field_simp
    ring
  | sr i =>
    simp [dihChar, dihTrivChar_sr, dihSignChar_sr]

/-- The character of `V ⊗ V` for the rotation representation `V` is `1 + sgn + θ_2`. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem character_tprod_dihRep_one :
    ((dihRep (1 : ZMod N)).tprod (dihRep (1 : ZMod N))).character =
      dihTrivChar N + dihSignChar N + dihChar (2 : ZMod N) := by
  rw [char_tensor, character_dihRep_eq]
  exact dihChar_one_sq

/-- The summand `ρ_2` of `V ⊗ V` is irreducible as soon as `4 ≠ 0` in `ZMod N`. -/
@[kb "etingof2011" "Problem 3.17, p. 43"]
theorem isIrreducible_dihRep_two (h : (2 : ZMod N) + 2 ≠ 0) : IsIrreducible (dihRep (2 : ZMod N)) :=
  isIrreducible_dihRep _ h

end Dihedral

section Heisenberg

namespace Heis

variable {p : ℕ} [Fact p.Prime]

/-- **Problem 3.25, values.**  The character of the `p`-dimensional irreducible representation `R_k` at an
element `(x, y, w)`: it vanishes unless `x = y = 0`, and at the central element `(0, 0, w)` it equals
`p · ψ_k(-w)`. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
theorem repChar_psi_apply (k : ZMod p) (g : Heis p) :
    repChar (psi k) g = if g.x = 0 ∧ g.y = 0 then (p : ℂ) * ee (-(k * g.w)) else 0 := by
  unfold repChar
  split_ifs <;> simp [psi_apply]

/-- The `p`-dimensional characters vanish off the centre. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
theorem repChar_psi_eq_zero (k : ZMod p) {g : Heis p} (hg : ¬ (g.x = 0 ∧ g.y = 0)) :
    repChar (psi k) g = 0 := by
  simp [repChar_psi_apply, hg]

lemma psi_add (k l s : ZMod p) : psi (k + l) s = psi k s * psi l s := by
  rw [psi_apply, psi_apply, psi_apply, ← AddChar.map_add_eq_mul]; congr 1; ring

/-- **Problem 3.25, linear times linear.** -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
theorem linHom_mul_linHom (a b a' b' : ZMod p) :
    (⇑(linHom a b) : Heis p → ℂ) * ⇑(linHom a' b') = ⇑(linHom (a + a') (b + b')) := by
  funext g
  simp only [Pi.mul_apply, linHom_apply, ← AddChar.map_add_eq_mul]
  congr 1; ring

/-- **Problem 3.25, linear times `p`-dimensional.**  A linear character is trivial on the centre, so tensoring a
`p`-dimensional irreducible with it does not change its character. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
theorem linHom_mul_repChar_psi (a b k : ZMod p) :
    (⇑(linHom a b) : Heis p → ℂ) * repChar (psi k) = repChar (psi k) := by
  funext g
  rw [Pi.mul_apply, repChar_psi_apply]
  by_cases h : g.x = 0 ∧ g.y = 0
  · simp [h.1, h.2, linHom_apply]
  · simp [h]

/-- **Problem 3.25, product of two `p`-dimensional characters.**  For `k + l ≠ 0` it is `p` times the character
`repChar (psi (k + l))`; for `k + l = 0` it is the sum of all `p²` linear characters. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
theorem repChar_psi_mul_repChar_psi (k l : ZMod p) :
    repChar (psi k) * repChar (psi l) =
      if k + l = 0 then ∑ q : ZMod p × ZMod p, (⇑(linHom q.1 q.2) : Heis p → ℂ)
      else (p : ℂ) • repChar (psi (k + l)) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  funext g
  by_cases hc : g.x = 0 ∧ g.y = 0
  · have e1 : ee (-(k * g.w)) * ee (-(l * g.w)) = ee (-((k + l) * g.w)) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    split_ifs with hkl
    · rw [Finset.sum_apply, Pi.mul_apply, repChar_psi_apply, repChar_psi_apply]
      simp only [linHom_apply, hc.1, hc.2, mul_zero, add_zero, AddChar.map_zero_eq_one, Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul, and_self, ite_true]
      have : ee (-(k * g.w)) * ee (-(l * g.w)) = 1 := by rw [e1, hkl, zero_mul, neg_zero]; simp
      push_cast
      linear_combination (p : ℂ) ^ 2 * this
    · simp only [Pi.mul_apply, Pi.smul_apply, repChar_psi_apply, hc.1, hc.2, and_self, ite_true, smul_eq_mul]
      linear_combination (p : ℂ) ^ 2 * e1
  · have hz : ∀ m : ZMod p, repChar (psi m) g = 0 := fun m => repChar_psi_eq_zero m hc
    split_ifs with hkl
    · rw [Finset.sum_apply, Pi.mul_apply, hz, zero_mul]
      symm
      simp only [linHom_apply]
      have : ∑ q : ZMod p × ZMod p, ee (q.1 * g.x + q.2 * g.y) =
          (∑ a : ZMod p, ee (a * g.x)) * ∑ b : ZMod p, ee (b * g.y) := by
        rw [Finset.sum_mul_sum, ← Finset.sum_product']
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [AddChar.map_add_eq_mul]
      rw [this, sum_ee_mul, sum_ee_mul]
      by_cases hx : g.x = 0
      · have hy : g.y ≠ 0 := fun hy => hc ⟨hx, hy⟩
        simp [hy]
      · simp [hx]
    · rw [Pi.mul_apply, Pi.smul_apply, hz, hz, hz]; simp

/-- **Problem 3.25, tensor products of representations.**  The character of `R_k ⊗ R_l` for the
representations `rep (psi k)`, `rep (psi l)` with `k, l ≠ 0`. -/
@[kb "etingof2011" "Problem 3.25, p. 45"]
theorem character_tprod_rep_psi {k l : ZMod p} (hk : k ≠ 0) (hl : l ≠ 0) :
    ((rep (psi k)).tprod (rep (psi l))).character =
      if k + l = 0 then ∑ q : ZMod p × ZMod p, (⇑(linHom q.1 q.2) : Heis p → ℂ)
      else (p : ℂ) • repChar (psi (k + l)) := by
  rw [char_tensor, character_rep _ (psi_ne_one hk), character_rep _ (psi_ne_one hl)]
  exact repChar_psi_mul_repChar_psi k l

end Heis

end Heisenberg

end UndergradKB.RepresentationTheory
