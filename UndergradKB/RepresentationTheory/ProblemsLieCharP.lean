import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime.Defs
import UndergradKB.Common.Attr

/-! # Problem 1.57 in characteristic `p`: classification of the irreducible representations

Over an algebraically closed field of characteristic `p`, a finite-dimensional irreducible representation of the
two-dimensional Lie algebra `[X, Y] = Y` (given by operators with `X Y - Y X = Y`) is either one-dimensional
with `Y = 0`, or `p`-dimensional with `Y` invertible (`aff1_irrep_char_p_classification`).
-/

namespace UndergradKB.RepresentationTheory

section Aff1Classification

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [IsAlgClosed k] [CharP k p]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]

/-- `X Y^n = Y^n X + n Y^n`. -/
theorem aff1_pow_comm (X Y : Module.End k V) (h : X * Y - Y * X = Y) (n : ℕ) :
    X * Y ^ n = Y ^ n * X + (n : k) • Y ^ n := by
  have hxy : X * Y = Y * X + Y := by rw [add_comm]; exact sub_eq_iff_eq_add.mp h
  induction n with
  | zero => simp
  | succ n ih =>
    calc X * Y ^ (n + 1) = (X * Y ^ n) * Y := by rw [pow_succ, ← mul_assoc]
      _ = (Y ^ n * X + (n : k) • Y ^ n) * Y := by rw [ih]
      _ = Y ^ n * (X * Y) + (n : k) • (Y ^ n * Y) := by rw [add_mul, mul_assoc, smul_mul_assoc]
      _ = Y ^ (n + 1) * X + ((n + 1 : ℕ) : k) • Y ^ (n + 1) := by
        rw [hxy, mul_add, ← mul_assoc, ← pow_succ, Nat.cast_succ, add_smul, one_smul]
        abel

/-- Schur: an operator commuting with both `X` and `Y` is a scalar. -/
theorem aff1_schur (X Y : Module.End k V)
    (hirr : ∀ W : Submodule k V, W.map X ≤ W → W.map Y ≤ W → W = ⊥ ∨ W = ⊤)
    (Z : Module.End k V) (hX : Z * X = X * Z) (hY : Z * Y = Y * Z) : ∃ c : k, ∀ v, Z v = c • v := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue Z
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hinv : ∀ T : Module.End k V, Z * T = T * Z →
      (Module.End.eigenspace Z μ).map T ≤ Module.End.eigenspace Z μ := by
    intro T hT
    rintro _ ⟨w, hw, rfl⟩
    have hw' : Z w = μ • w := Module.End.mem_eigenspace_iff.mp hw
    show T w ∈ Module.End.eigenspace Z μ
    rw [Module.End.mem_eigenspace_iff]
    have : Z (T w) = T (Z w) := by
      have := congrArg (fun S => S w) hT
      simpa using this
    rw [this, hw', map_smul]
  rcases hirr _ (hinv X hX) (hinv Y hY) with h | h
  · have hvE : v ∈ Module.End.eigenspace Z μ := hv.1
    rw [h, Submodule.mem_bot] at hvE
    exact absurd hvE hv.2
  · refine ⟨μ, fun w => ?_⟩
    have : w ∈ Module.End.eigenspace Z μ := by rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.mp this

/-- **Etingof et al., Problem 1.57 (classification in characteristic `p`)**: over an algebraically closed field
of characteristic `p`, a finite-dimensional irreducible pair `X, Y` with `[X, Y] = Y` is either
one-dimensional with `Y = 0`, or `p`-dimensional with `Y` bijective. -/
@[kb "etingof2011" "Problem 1.57, p. 22"]
theorem aff1_irrep_char_p_classification (X Y : Module.End k V) (h : X * Y - Y * X = Y)
    (hirr : ∀ W : Submodule k V, W.map X ≤ W → W.map Y ≤ W → W = ⊥ ∨ W = ⊤) :
    (Module.finrank k V = 1 ∧ Y = 0) ∨ (Module.finrank k V = p ∧ Function.Bijective Y) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hrel := aff1_pow_comm X Y h
  have hxy : X * Y = Y * X + Y := by rw [add_comm]; exact sub_eq_iff_eq_add.mp h
  -- `Y ^ p` is a scalar
  obtain ⟨c, hc⟩ := aff1_schur X Y hirr (Y ^ p) (by
      have := hrel p
      rw [CharP.cast_eq_zero, zero_smul, add_zero] at this
      exact this.symm)
    (Commute.pow_self Y p).eq
  by_cases hc0 : c = 0
  · -- `Y` is nilpotent
    left
    have hYp : ∀ v, (Y ^ p) v = 0 := fun v => by rw [hc, hc0, zero_smul]
    have hker : LinearMap.ker Y ≠ ⊥ := by
      intro hbot
      have hinj : Function.Injective Y := LinearMap.ker_eq_bot.mp hbot
      have hpow : ∀ n : ℕ, Function.Injective (Y ^ n) := by
        intro n
        induction n with
        | zero => simpa using Function.injective_id
        | succ n ih =>
          rw [pow_succ]
          exact ih.comp hinj
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (hpow p (by rw [hYp v, map_zero]))
    have hY0 : Y = 0 := by
      rcases hirr (LinearMap.ker Y) (by
          rintro _ ⟨w, hw, rfl⟩
          have hw' : Y w = 0 := LinearMap.mem_ker.mp hw
          refine LinearMap.mem_ker.mpr ?_
          -- `Y (X w) = X (Y w) - Y w = 0`
          have := congrArg (fun S => S w) hxy
          simp only [mul_apply_eq_comp, LinearMap.add_apply, hw', map_zero] at this
          simpa using this.symm)
        (by
          rintro _ ⟨w, hw, rfl⟩
          have hw' : Y w = 0 := LinearMap.mem_ker.mp hw
          exact LinearMap.mem_ker.mpr (by rw [hw']; simp)) with h' | h'
      · exact absurd h' hker
      · exact LinearMap.ext fun v => by
          have : v ∈ LinearMap.ker Y := by rw [h']; trivial
          simpa using this
    refine ⟨?_, hY0⟩
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue X
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hvX : X v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    have hspan : (k ∙ v) = ⊤ := by
      rcases hirr (k ∙ v) (by
          rintro _ ⟨w, hw, rfl⟩
          obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
          rw [map_smul, hvX]
          exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (by rintro _ ⟨w, hw, rfl⟩; rw [hY0]; simp) with h' | h'
      · exact absurd h' (by simpa using hv0)
      · exact h'
    rw [← finrank_top k V, ← hspan, finrank_span_singleton hv0]
  · right
    have hYinj : Function.Injective Y := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have hpY : Y ^ p = Y ^ (p - 1) * Y := by
        rw [← pow_succ]; congr 1; omega
      have h1 : (Y ^ p) a = 0 := by
        rw [hpY, mul_apply_eq_comp, ha, map_zero]
      rw [hc, smul_eq_zero] at h1
      exact h1.resolve_left hc0
    have hbij : Function.Bijective Y := ⟨hYinj, LinearMap.injective_iff_surjective.mp hYinj⟩
    refine ⟨?_, hbij⟩
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue X
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hvX : X v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    have hu0 : ∀ n : ℕ, (Y ^ n) v ≠ 0 := by
      intro n
      induction n with
      | zero => simpa using hv0
      | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp]
        intro h0
        exact ih (hYinj (by rw [h0, map_zero]))
    have hXu : ∀ n : ℕ, X ((Y ^ n) v) = (μ + (n : k)) • (Y ^ n) v := by
      intro n
      have := congrArg (fun S => S v) (hrel n)
      simp only [mul_apply_eq_comp, LinearMap.add_apply, LinearMap.smul_apply] at this
      rw [this, hvX, map_smul, add_smul]
    let u : Fin p → V := fun j => (Y ^ (j : ℕ)) v
    have hinj : Function.Injective (fun j : Fin p => μ + ((j : ℕ) : k)) := by
      intro a b hab
      have h1 : ((a : ℕ) : k) = ((b : ℕ) : k) := add_left_cancel hab
      have h2 := (CharP.natCast_eq_natCast k p).mp h1
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 a.2 b.2)
    have hli : LinearIndependent k u :=
      Module.End.eigenvectors_linearIndependent' X (fun j : Fin p => μ + ((j : ℕ) : k)) hinj u
        (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (hXu j), hu0 j⟩)
    have hmem : ∀ j, u j ∈ Submodule.span k (Set.range u) := fun j => Submodule.subset_span ⟨j, rfl⟩
    have hW : Submodule.span k (Set.range u) = ⊤ := by
      rcases hirr (Submodule.span k (Set.range u)) (by
          rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          rw [SetLike.mem_coe, Submodule.mem_comap]
          have : X (u j) = (μ + (((j : ℕ)) : k)) • u j := hXu j
          rw [this]
          exact Submodule.smul_mem _ _ (hmem j))
        (by
          rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          rw [SetLike.mem_coe, Submodule.mem_comap]
          have hYu : Y (u j) = (Y ^ ((j : ℕ) + 1)) v := by
            show Y ((Y ^ (j : ℕ)) v) = _
            rw [pow_succ', mul_apply_eq_comp]
          rw [hYu]
          by_cases hj : (j : ℕ) + 1 < p
          · exact hmem ⟨(j : ℕ) + 1, hj⟩
          · have hjp : (j : ℕ) + 1 = p := by have := j.2; omega
            rw [hjp, hc]
            exact Submodule.smul_mem _ _ (by simpa [u] using hmem ⟨0, hp⟩)) with h' | h'
      · exfalso
        have := hmem ⟨0, hp⟩
        rw [h', Submodule.mem_bot] at this
        exact hv0 (by simpa [u] using this)
      · exact h'
    rw [← finrank_top k V, ← hW, finrank_span_eq_card hli, Fintype.card_fin]

end Aff1Classification

end UndergradKB.RepresentationTheory
