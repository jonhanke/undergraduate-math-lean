import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr

/-! # Commuting operators (Axler 5.78, 5.81, Exercises 5E.3)

Common eigenvectors of commuting families over an algebraically closed field, eigenvalues of sums
and products of commuting operators, and invariance of kernels and ranges of polynomials.
Simultaneous triangularization lives in `Triangular.lean` and simultaneous diagonalization in
`Diagonalizable.lean` (they need the corresponding predicates).
-/

open Module Polynomial

namespace UndergradKB.LinearAlgebra

universe u v

section

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

private theorem commute_restrict' {T₁ T₂ : Module.End K V} (h : Commute T₁ T₂)
    (U : Submodule K V) (h₁ : ∀ x ∈ U, T₁ x ∈ U) (h₂ : ∀ x ∈ U, T₂ x ∈ U) :
    Commute (T₁.restrict h₁) (T₂.restrict h₂) := by
  show T₁.restrict h₁ * T₂.restrict h₂ = T₂.restrict h₂ * T₁.restrict h₁
  ext x
  have := congrArg (fun f => f (x : V)) h.eq
  simpa using this

/-- Over an algebraically closed field, a commuting family of operators on a nonzero
finite-dimensional space has a common eigenvector.  (Induction on the dimension: restrict to an
eigenspace of a non-scalar member.) -/
theorem exists_common_eigenvector [IsAlgClosed K] {ι : Type*} :
    ∀ (n : ℕ) (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → Nontrivial V → ∀ (T : ι → Module.End K V),
      (∀ i j, Commute (T i) (T j)) → ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : K, T i v = μ • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn hV T hc
  by_cases hsc : ∀ i, ∃ c : K, T i = c • (1 : Module.End K V)
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun i => ?_⟩
    obtain ⟨c, hci⟩ := hsc i
    exact ⟨c, by rw [hci]; simp⟩
  · have hex : ∃ j, ∀ c : K, T j ≠ c • (1 : Module.End K V) := by
      by_contra hcon
      apply hsc
      intro i
      by_contra hi
      exact hcon ⟨i, fun c hc => hi ⟨c, hc⟩⟩
    obtain ⟨j, hj⟩ := hex
    obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (T j)
    have hlt : finrank K ((T j).eigenspace l) < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hj l
      ext x
      have : x ∈ (T j).eigenspace l := by rw [htop]; trivial
      simpa using Module.End.mem_eigenspace_iff.mp this
    have hinv : ∀ i, ∀ x ∈ (T j).eigenspace l, T i x ∈ (T j).eigenspace l := by
      intro i x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      have := congrArg (fun f => f x) (hc j i).eq
      simp only [mul_apply_eq_comp, LinearMap.comp_apply] at this
      rw [this, hx, map_smul]
    have hnt : Nontrivial ((T j).eigenspace l) := Submodule.nontrivial_iff_ne_bot.mpr hl
    obtain ⟨v, hv0, hv⟩ := ih _ hlt ((T j).eigenspace l) rfl hnt
      (fun i => (T i).restrict (hinv i)) (fun i i' => commute_restrict' (hc i i') _ _ _)
    refine ⟨v, fun h => hv0 (Subtype.ext h), fun i => ?_⟩
    obtain ⟨μ, hμ⟩ := hv i
    exact ⟨μ, by simpa using congrArg Subtype.val hμ⟩

variable [FiniteDimensional K V]

/-- **Axler 5.78 / Exercise 5E.9** (common eigenvector): any commuting family of operators on a
nonzero finite-dimensional space over an algebraically closed field (e.g. `ℂ`) has a common
eigenvector. -/
@[kb "axler2024" "5.78, p. 195"]
theorem axler_5_78 [IsAlgClosed K] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hc : ∀ i j, Commute (T i) (T j)) : ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : K, T i v = μ • v :=
  exists_common_eigenvector (finrank K V) V rfl ‹_› T hc

/-- Common eigenvector of two commuting operators inside a subspace invariant under both. -/
theorem exists_common_eigenvector_pair [IsAlgClosed K] (S T : Module.End K V)
    (h : Commute S T) (W : Submodule K V) (hW : W ≠ ⊥) (hS : ∀ x ∈ W, S x ∈ W)
    (hT : ∀ x ∈ W, T x ∈ W) :
    ∃ v : V, v ∈ W ∧ v ≠ 0 ∧ ∃ a b : K, S v = a • v ∧ T v = b • v := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let F : Fin 2 → Module.End K W := ![S.restrict hS, T.restrict hT]
  have hF : ∀ i j, Commute (F i) (F j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact commute_restrict' h W hS hT
    · exact (commute_restrict' h W hS hT).symm
    · exact Commute.refl _
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector (finrank K W) W rfl ‹_› F hF
  obtain ⟨a, ha⟩ := hv 0
  obtain ⟨b, hb⟩ := hv 1
  refine ⟨v, v.2, fun h0 => hv0 (Subtype.ext h0), a, b, ?_, ?_⟩
  · simpa [F] using congrArg Subtype.val ha
  · simpa [F] using congrArg Subtype.val hb

private theorem sub_smul_eq_zero_aux {v : V} (hv : v ≠ 0) {c d : K} (h : c • v = d • v) :
    c = d := by
  have : (c - d) • v = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hv)

/-- **Axler 5.81**: for commuting operators on a finite-dimensional space over an algebraically
closed field, every eigenvalue of `S + T` is a sum of an eigenvalue of `S` and an eigenvalue of
`T`, and every eigenvalue of `S T` is a product of an eigenvalue of `S` and one of `T`. -/
@[kb "axler2024" "5.81, p. 197"]
theorem axler_5_81 [IsAlgClosed K] (S T : Module.End K V) (h : Commute S T) :
    (∀ l, (S + T).HasEigenvalue l → ∃ a b, S.HasEigenvalue a ∧ T.HasEigenvalue b ∧ l = a + b) ∧
    (∀ l, (S * T).HasEigenvalue l → ∃ a b, S.HasEigenvalue a ∧ T.HasEigenvalue b ∧ l = a * b) := by
  constructor
  · intro l hl
    have h1 : Commute S (S + T) := (Commute.refl S).add_right h
    have h2 : Commute T (S + T) := h.symm.add_right (Commute.refl T)
    obtain ⟨v, hvW, hv0, a, b, ha, hb⟩ := exists_common_eigenvector_pair S T h
      ((S + T).eigenspace l) hl
      (fun x hx => by
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        have := congrArg (fun f => f x) h1.eq
        simp only [mul_apply_eq_comp, LinearMap.comp_apply] at this
        rw [← this, hx, map_smul])
      (fun x hx => by
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        have := congrArg (fun f => f x) h2.eq
        simp only [mul_apply_eq_comp, LinearMap.comp_apply] at this
        rw [← this, hx, map_smul])
    refine ⟨a, b, Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr ha, hv0⟩,
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hb, hv0⟩, ?_⟩
    have := Module.End.mem_eigenspace_iff.mp hvW
    rw [LinearMap.add_apply, ha, hb, ← add_smul] at this
    exact (sub_smul_eq_zero_aux hv0 this).symm
  · intro l hl
    have h1 : Commute S (S * T) := (Commute.refl S).mul_right h
    have h2 : Commute T (S * T) := h.symm.mul_right (Commute.refl T)
    obtain ⟨v, hvW, hv0, a, b, ha, hb⟩ := exists_common_eigenvector_pair S T h
      ((S * T).eigenspace l) hl
      (fun x hx => by
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        have := congrArg (fun f => f x) h1.eq
        simp only [mul_apply_eq_comp] at this hx ⊢
        rw [← this, hx, map_smul])
      (fun x hx => by
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        have := congrArg (fun f => f x) h2.eq
        simp only [mul_apply_eq_comp] at this hx ⊢
        rw [← this, hx, map_smul])
    refine ⟨a, b, Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr ha, hv0⟩,
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hb, hv0⟩, ?_⟩
    have := Module.End.mem_eigenspace_iff.mp hvW
    rw [mul_apply_eq_comp, hb, map_smul, ha, smul_smul] at this
    exact (sub_smul_eq_zero_aux hv0 this).symm.trans (mul_comm _ _)

end

section

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- A polynomial in `S` commutes with everything commuting with `S`. -/
theorem commute_aeval_left (S T : Module.End K V) (h : Commute S T) (p : K[X]) :
    Commute (aeval S p) T := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_left hq
  | monomial n a =>
    rw [aeval_monomial]
    exact (show Commute (algebraMap K (Module.End K V) a) T from Algebra.commutes a T).mul_left
      (h.pow_left n)

/-- **Axler Exercise 5E.3**: if `S` and `T` commute, then `null p(S)` and `range p(S)` are
`T`-invariant for every polynomial `p`. -/
@[kb "axler2024" "Ex5E.3, p. 198"]
theorem axler_ex5E_3 (S T : Module.End K V) (h : Commute S T) (p : K[X]) :
    (∀ x ∈ LinearMap.ker (aeval S p), T x ∈ LinearMap.ker (aeval S p)) ∧
    (∀ x ∈ LinearMap.range (aeval S p), T x ∈ LinearMap.range (aeval S p)) := by
  have hc := commute_aeval_left S T h p
  have key : ∀ x, aeval S p (T x) = T (aeval S p x) := fun x => by
    have := congrArg (fun f => f x) hc.eq
    simpa using this
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [LinearMap.mem_ker] at hx ⊢
    rw [key, hx, map_zero]
  · rintro _ ⟨y, rfl⟩
    exact ⟨T y, key y⟩

end

end UndergradKB.LinearAlgebra
