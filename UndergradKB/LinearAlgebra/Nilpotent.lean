import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import UndergradKB.Common.Attr

/-! # Nilpotent operators

Axler 8.16-8.17 and Hefferon Five.IV.2.1-2.3.  (Axler 8.18 is in `Jordan.lean`, where the
Jordan basis it needs is built.) -/

open Module

namespace UndergradKB.LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Axler 8.16: a nilpotent operator on `V` already vanishes at the power `dim V`. -/
@[kb "axler2024" "8.16, p. 322"]
theorem axler_8_16 {T : Module.End K V} (hT : IsNilpotent T) : T ^ finrank K V = 0 := by
  have h := LinearMap.aeval_self_charpoly T
  rw [hT.charpoly_eq_X_pow_finrank] at h
  simpa using h

lemma eq_of_hasEigenvalue_of_isNilpotent_sub {T : Module.End K V} {lam μ : K}
    (hN : IsNilpotent (T - lam • (1 : Module.End K V))) (h : T.HasEigenvalue μ) : μ = lam := by
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  obtain ⟨k, hk⟩ := hN
  have hpow : ∀ n : ℕ, ((T - lam • (1 : Module.End K V)) ^ n) x = (μ - lam) ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul]
      have := hx.apply_eq_smul
      have e : (T - lam • (1 : Module.End K V)) x = (μ - lam) • x := by
        simp [this, sub_smul]
      rw [e, smul_smul, pow_succ]
  have h0 : (μ - lam) ^ k • x = 0 := by rw [← hpow, hk]; rfl
  have : (μ - lam) ^ k = 0 := (smul_eq_zero.mp h0).resolve_right hx.2
  exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨k, this⟩)

private lemma maxGenEigenspace_eq_bot_of_not' (T : Module.End K V) {μ : K}
    (h : ¬ T.HasEigenvalue μ) : T.maxGenEigenspace μ = ⊥ := by
  rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq,
    Polynomial.rootMultiplicity_eq_zero]
  rwa [Module.End.hasEigenvalue_iff_isRoot_charpoly] at h

/-- Hefferon Lemma Five.IV.2.2 (and its converse): over an algebraically closed field,
`T - lam` is nilpotent exactly when `lam` is the only eigenvalue of `T`. -/
@[kb "hefferon2020" "Five.IV.2.2, p. 459"]
theorem hefferon_Five_IV_2_2 [IsAlgClosed K] {T : Module.End K V} {lam : K} :
    IsNilpotent (T - lam • (1 : Module.End K V)) ↔ ∀ μ, T.HasEigenvalue μ → μ = lam := by
  refine ⟨fun hN μ h => eq_of_hasEigenvalue_of_isNilpotent_sub hN h, fun h => ?_⟩
  have htop : T.maxGenEigenspace lam = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top T]
    refine iSup_le fun μ => ?_
    by_cases hμ : T.HasEigenvalue μ
    · rw [h μ hμ]
    · rw [maxGenEigenspace_eq_bot_of_not' T hμ]; exact bot_le
  refine ((LinearMap.charpoly_nilpotent_tfae (T - lam • (1 : Module.End K V))).out 1 3).mpr ?_
  intro x
  have : x ∈ T.maxGenEigenspace lam := by rw [htop]; trivial
  exact (Module.End.mem_maxGenEigenspace _ _ _).mp this

/-- Hefferon Lemma Five.IV.2.2, nontrivial-space clause: when `V ≠ 0` and `T - lam` is nilpotent,
`lam` is an eigenvalue of `T`. -/
theorem hasEigenvalue_of_isNilpotent_sub [IsAlgClosed K] [Nontrivial V] {T : Module.End K V}
    {lam : K} (hN : IsNilpotent (T - lam • (1 : Module.End K V))) : T.HasEigenvalue lam := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  rwa [← eq_of_hasEigenvalue_of_isNilpotent_sub hN hμ]

/-- Axler 8.17(a): the only eigenvalue of a nilpotent operator is `0`. -/
@[kb "axler2024" "8.17, p. 322"]
theorem axler_8_17_a {T : Module.End K V} (hT : IsNilpotent T) {μ : K}
    (h : T.HasEigenvalue μ) : μ = 0 :=
  eq_of_hasEigenvalue_of_isNilpotent_sub (lam := 0) (by simpa using hT) h

/-- Axler 8.17(b): over `ℂ` (any algebraically closed field), an operator whose only eigenvalue is
`0` is nilpotent. -/
@[kb "axler2024" "8.17, p. 322"]
theorem axler_8_17_b [IsAlgClosed K] {T : Module.End K V}
    (h : ∀ μ, T.HasEigenvalue μ → μ = 0) : IsNilpotent T := by
  simpa using (hefferon_Five_IV_2_2 (T := T) (lam := 0)).mpr h

/-- Hefferon Theorem Five.IV.2.1: over `ℂ`, a map is nilpotent iff its only eigenvalue is `0`. -/
@[kb "hefferon2020" "Five.IV.2.1, p. 458"]
theorem hefferon_Five_IV_2_1 [IsAlgClosed K] {T : Module.End K V} :
    IsNilpotent T ↔ ∀ μ, T.HasEigenvalue μ → μ = 0 :=
  ⟨fun h _ hμ => axler_8_17_a h hμ, axler_8_17_b⟩

/-- Hefferon Lemma Five.IV.2.3: if `T - lam I` is similar to `N` via `P`, then `T` is similar to
`N + lam I` via the same `P`. -/
@[kb "hefferon2020" "Five.IV.2.3, p. 459"]
theorem hefferon_Five_IV_2_3 {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (T N : Matrix n n R) (lam : R) (P : (Matrix n n R)ˣ)
    (h : (P : Matrix n n R) * N * (↑P⁻¹ : Matrix n n R) = T - lam • 1) :
    (P : Matrix n n R) * (N + lam • 1) * (↑P⁻¹ : Matrix n n R) = T := by
  rw [mul_add, add_mul, h]
  simp

end UndergradKB.LinearAlgebra
