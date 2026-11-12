import Mathlib.LinearAlgebra.Lagrange
import UndergradKB.RepresentationTheory.McKay
import UndergradKB.RepresentationTheory.Burnside
import UndergradKB.Common.Attr

/-! # Connectedness of the McKay graph (Etingof et al., Problem 5.5)

For a faithful finite-dimensional complex representation `ρ` of a finite group `G`:

* `eq_one_of_character_eq_finrank`: if `χ_ρ(g) = dim ρ` then `g` acts trivially (the eigenvalues of `ρ g` are
  roots of unity whose real parts sum to the dimension);
* `exists_pairing_character_pow_ne_zero` (Burnside-Brauer): every irreducible character `ψ` has non-zero pairing
  with some power `χ_ρ ^ k`, i.e. occurs in some tensor power of `ρ`. The proof groups the sum
  `∑_g χ(g)^k ψ(g⁻¹)` by the value of `χ` and uses Lagrange interpolation to isolate the fibre `{1}`;
* `mckay_reachable`: every irreducible character is reachable from the trivial one in the McKay graph, and
  `mckay_connected` is the undirected version when the character of `ρ` is real;
* the specialisation to the natural representation of a finite subgroup of `SU(2)`.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module Polynomial

set_option linter.unusedSectionVars false

section Faithful

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V)

/-- **Etingof et al., Problem 5.5** (step): if the character of `ρ` at `g` equals the dimension, then `g` acts
as the identity. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem eq_one_of_character_eq_finrank (g : G) (h : ρ.character g = finrank ℂ V) : ρ g = 1 := by
  classical
  set T := ρ g with hTdef
  set s := T.charpoly.roots with hsdef
  have hm : 0 < orderOf g := orderOf_pos g
  have hTm : T ^ orderOf g = 1 := by rw [hTdef, ← map_pow, pow_orderOf_eq_one, map_one]
  have hnorm : ∀ μ ∈ s, ‖μ‖ = 1 := fun μ hμ ↦
    Complex.norm_eq_one_of_pow_eq_one (pow_eq_one_of_mem_roots T _ hTm hμ) hm.ne'
  have hcard : s.card = finrank ℂ V := card_roots_charpoly T
  have h1 : s.sum = (finrank ℂ V : ℂ) := by rw [← trace_eq_sum_roots]; exact h
  have hre : (s.map Complex.re).sum = (finrank ℂ V : ℝ) := by
    have h2 : s.sum.re = (s.map Complex.re).sum := map_multiset_sum Complex.reAddGroupHom s
    have h3 := congrArg Complex.re h1
    rw [h2, Complex.natCast_re] at h3
    exact h3
  have hall : ∀ μ ∈ s, μ = 1 := by
    intro μ0 hμ0
    have e1 := Multiset.sum_map_erase (f := Complex.re) hμ0
    have e2 : ((s.erase μ0).map Complex.re).sum ≤ Multiset.card ((s.erase μ0).map Complex.re) • (1 : ℝ) :=
      Multiset.sum_le_card_nsmul _ _ (by
        intro x hx
        obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
        exact (Complex.re_le_norm μ).trans (hnorm μ (Multiset.mem_of_mem_erase hμ)).le)
    have e3 := Multiset.card_erase_add_one hμ0
    rw [Multiset.card_map, nsmul_eq_mul, mul_one] at e2
    have e4 : ((s.erase μ0).card : ℝ) + 1 = (finrank ℂ V : ℝ) := by
      rw [← hcard]; exact_mod_cast e3
    have hle : μ0.re ≤ 1 := (Complex.re_le_norm μ0).trans (hnorm μ0 hμ0).le
    have hre1 : μ0.re = 1 := by linarith
    have hsq : ‖μ0‖ ^ 2 = 1 := by rw [hnorm μ0 hμ0]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply, hre1] at hsq
    have him : μ0.im = 0 := by nlinarith [sq_nonneg μ0.im]
    exact Complex.ext (by simpa using hre1) (by simpa using him)
  have := eq_smul_id_of_forall_mem_roots T _ hm hTm 1 hall
  rw [this, one_smul]; rfl

variable [Invertible (Nat.card G : ℂ)]

/-- **Etingof et al., Problem 5.5** (Burnside-Brauer): for a faithful finite-dimensional representation `ρ`,
every irreducible character has non-zero pairing with some power of the character of `ρ`, so every irreducible
representation occurs in some tensor power of `ρ`. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem exists_pairing_character_pow_ne_zero (hρ : Function.Injective ρ) (ψ : irrChars ℂ G) :
    ∃ k : ℕ, pairing (ρ.character ^ k) (ψ : G → ℂ) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set χ := ρ.character with hχ
  set S : Finset ℂ := Finset.univ.image χ with hS
  set b : ℂ → ℂ := fun a ↦ ∑ g ∈ Finset.univ.filter (fun g ↦ χ g = a), (ψ : G → ℂ) g⁻¹ with hb
  have key : ∀ k : ℕ, ∑ a ∈ S, a ^ k * b a = 0 := by
    intro k
    have h0 := hcon k
    rw [pairing_apply] at h0
    have hne : (Nat.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero (NeZero.ne _)
    have h1 : ∑ g, (χ ^ k) g * (ψ : G → ℂ) g⁻¹ = 0 := (mul_eq_zero.mp h0).resolve_left hne
    calc ∑ a ∈ S, a ^ k * b a
        = ∑ a ∈ S, ∑ g ∈ Finset.univ.filter (fun g ↦ χ g = a), (χ ^ k) g * (ψ : G → ℂ) g⁻¹ := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hb, Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg ↦ ?_
          rw [Pi.pow_apply, (Finset.mem_filter.mp hg).2]
      _ = ∑ g, (χ ^ k) g * (ψ : G → ℂ) g⁻¹ :=
          Finset.sum_fiberwise_of_maps_to
            (fun g _ ↦ Finset.mem_image_of_mem χ (Finset.mem_univ g)) _
      _ = 0 := h1
  have poly : ∀ p : ℂ[X], ∑ a ∈ S, p.eval a * b a = 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [eval_add, add_mul, Finset.sum_add_distrib, hp, hq, add_zero]
    | monomial n c =>
      simp only [eval_monomial, mul_assoc, ← Finset.mul_sum]
      rw [key n, mul_zero]
  have ha0 : (finrank ℂ V : ℂ) ∈ S :=
    Finset.mem_image.mpr ⟨1, Finset.mem_univ _, char_one ρ⟩
  have h := poly (Lagrange.basis S id (finrank ℂ V : ℂ))
  rw [Finset.sum_eq_single (finrank ℂ V : ℂ)] at h
  · have h1 : (Lagrange.basis S id (finrank ℂ V : ℂ)).eval (finrank ℂ V : ℂ) = 1 :=
      Lagrange.eval_basis_self (v := id) (Set.injOn_id _) ha0
    rw [h1, one_mul] at h
    have hfib : Finset.univ.filter (fun g ↦ χ g = (finrank ℂ V : ℂ)) = {1} := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine ⟨fun hg ↦ hρ ?_, fun hg ↦ by rw [hg]; exact char_one ρ⟩
      rw [map_one]
      exact eq_one_of_character_eq_finrank ρ g hg
    rw [hb] at h
    simp only [hfib, Finset.sum_singleton, inv_one] at h
    obtain ⟨X, hX⟩ := ψ.2
    have : (ψ : G → ℂ) 1 ≠ 0 := by
      rw [← hX]
      show X.ρ.character 1 ≠ 0
      rw [char_one]
      exact finrank_ne_zero' X.ρ
    exact this h
  · intro a ha hne
    have : (Lagrange.basis S id (finrank ℂ V : ℂ)).eval a = 0 :=
      Lagrange.eval_basis_of_ne (v := id) (Ne.symm hne) ha
    rw [this, zero_mul]
  · intro hn
    exact absurd ha0 hn

/-- The trivial character, as an irreducible character. -/
noncomputable def trivIrrChar : irrChars ℂ G :=
  ⟨(trivialIrrRep G).ρ.character, ⟨trivialIrrRep G, rfl⟩⟩

theorem coe_trivIrrChar : ((trivIrrChar : irrChars ℂ G) : G → ℂ) = 1 :=
  character_trivialIrrRep G

variable {ρ}

/-- A power of `χ_ρ` having non-zero pairing with `ψ` forces `ψ` to be reachable from the trivial character. -/
theorem reachable_of_pairing_pow_ne_zero (k : ℕ) :
    ∀ ψ : irrChars ℂ G, pairing (ρ.character ^ k) (ψ : G → ℂ) ≠ 0 →
      Relation.ReflTransGen (fun i j ↦ mckay ρ i j ≠ 0) trivIrrChar ψ := by
  classical
  induction k with
  | zero =>
    intro ψ h
    rw [pow_zero, ← coe_trivIrrChar (G := G), pairing_irrChars (trivIrrChar (G := G)).2 ψ.2] at h
    have : (trivIrrChar : irrChars ℂ G) = ψ := by
      by_contra hne
      exact h (by split_ifs with h' <;> first | rfl | exact absurd (Subtype.ext h') hne)
    rw [← this]
  | succ k ih =>
    intro ψ h
    have hmem : ρ.character ^ k ∈ classFunctions ℂ G := by
      rw [mem_classFunctions]
      intro g h'
      have := character_mem_classFunctions ρ
      rw [mem_classFunctions] at this
      simp only [Pi.pow_apply, this g h']
    have hexp := eq_sum_pairing_smul hmem
    have h2 : pairing (ρ.character ^ (k + 1)) (ψ : G → ℂ)
        = ∑ i : irrChars ℂ G, pairing (ρ.character ^ k) (i : G → ℂ) * mckay ρ i ψ := by
      rw [pow_succ]
      conv_lhs => rw [hexp]
      simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, mckay, mul_comm (ρ.character)]
    rw [h2] at h
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hi1 : pairing (ρ.character ^ k) (i : G → ℂ) ≠ 0 := left_ne_zero_of_mul hi
    have hi2 : mckay ρ i ψ ≠ 0 := right_ne_zero_of_mul hi
    exact (ih i hi1).tail hi2

/-- **Etingof et al., Problem 5.5**: for a faithful representation `ρ`, every irreducible character is reachable
from the trivial character along edges `r_ij ≠ 0` of the McKay graph. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_reachable (hρ : Function.Injective ρ) (ψ : irrChars ℂ G) :
    Relation.ReflTransGen (fun i j ↦ mckay ρ i j ≠ 0) trivIrrChar ψ := by
  obtain ⟨k, hk⟩ := exists_pairing_character_pow_ne_zero ρ hρ ψ
  exact reachable_of_pairing_pow_ne_zero k ψ hk

/-- **Etingof et al., Problem 5.5**: if the character of the faithful representation `ρ` is real valued, the McKay
graph is connected: any two irreducible characters are joined by a path. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_connected (hρ : Function.Injective ρ) (hreal : ∀ g, ρ.character g⁻¹ = ρ.character g)
    (i j : irrChars ℂ G) : Relation.ReflTransGen (fun i j ↦ mckay ρ i j ≠ 0) i j := by
  have : Std.Symm (fun i j : irrChars ℂ G ↦ mckay ρ i j ≠ 0) :=
    ⟨fun a b hab ↦ by
      show mckay ρ b a ≠ 0
      rwa [mckay_symm ρ hreal] at hab⟩
  exact (Std.Symm.symm _ _ (mckay_reachable hρ i)).trans (mckay_reachable hρ j)

end Faithful

section SU2

variable (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ))

/-- The natural representation of a subgroup of `SU(2)` is faithful. -/
theorem natRep_injective : Function.Injective (natRep G) := by
  intro a b hab
  have h : (a.1.1 : Matrix (Fin 2) (Fin 2) ℂ) = b.1.1 :=
    Matrix.toLin'.injective hab
  exact Subtype.ext (Subtype.ext h)

/-- **Etingof et al., Problem 5.5**: for a finite subgroup of `SU(2)`, the McKay graph of the natural
representation is connected. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_natRep_connected [Fintype G] [Invertible (Nat.card G : ℂ)] (i j : irrChars ℂ G) :
    Relation.ReflTransGen (fun i j ↦ mckay (natRep G) i j ≠ 0) i j :=
  mckay_connected (natRep_injective G) (natRep_character_inv G) i j

end SU2

end UndergradKB.RepresentationTheory
