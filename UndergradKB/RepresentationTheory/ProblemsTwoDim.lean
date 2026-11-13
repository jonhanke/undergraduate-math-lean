import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Module
import UndergradKB.Common.Attr

/-! # Two-dimensional representations (Etingof et al., Problems 2.22(a) and 2.23)

* Problem 2.22(a), classification: a representation of `ℂ[x_1, ..., x_n]` on a 2-dimensional space is a family of
  commuting operators `X_i`.  In a suitable basis either all `X_i` are diagonal (`V = V_a ⊕ V_b`) or
  `X_i = [[a_i, c_i], [0, a_i]]` with `c ≠ 0` (a non-split self-extension of `V_a`).  In the second case two such
  representations are isomorphic iff the `a`'s agree and the `c`'s are proportional by a nonzero scalar.
-/

namespace UndergradKB.RepresentationTheory

section TwoDim

variable {n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem exists_basis_pair (hV : Module.finrank ℂ V = 2) (v w : V)
    (h : ∀ s t : ℂ, s • v + t • w = 0 → s = 0 ∧ t = 0) :
    ∃ b : Module.Basis (Fin 2) ℂ V, b 0 = v ∧ b 1 = w := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by omega)
  have hli : LinearIndependent ℂ ![v, w] := LinearIndependent.pair_iff.mpr h
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV]), by simp, by simp⟩

theorem exists_common_eigenvector (hV : Module.finrank ℂ V = 2) (X : Fin n → Module.End ℂ V)
    (hX : ∀ i j, Commute (X i) (X j)) :
    ∃ v : V, v ≠ 0 ∧ ∃ a : Fin n → ℂ, ∀ i, X i v = a i • v := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  by_cases hs : ∀ i, ∃ s : ℂ, ∀ v, X i v = s • v
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    choose a ha using hs
    exact ⟨v, hv, a, fun i => ha i v⟩
  · push Not at hs
    obtain ⟨j, hj⟩ := hs
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (X j)
    obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
    have hvE : v ∈ Module.End.eigenspace (X j) lam := hv.1
    have hv0 : v ≠ 0 := hv.2
    have hEtop : Module.End.eigenspace (X j) lam ≠ ⊤ := by
      intro h
      obtain ⟨w, hw⟩ := hj lam
      have : w ∈ Module.End.eigenspace (X j) lam := by rw [h]; trivial
      exact hw (Module.End.mem_eigenspace_iff.mp this)
    have hlt := Submodule.finrank_lt hEtop
    have hspan : (ℂ ∙ v) ≤ Module.End.eigenspace (X j) lam := by
      rw [Submodule.span_singleton_le_iff_mem]; exact hvE
    have hge : 1 ≤ Module.finrank ℂ (Module.End.eigenspace (X j) lam) := by
      calc 1 = Module.finrank ℂ (ℂ ∙ v) := (finrank_span_singleton hv0).symm
        _ ≤ _ := Submodule.finrank_mono hspan
    have heq : (ℂ ∙ v) = Module.End.eigenspace (X j) lam :=
      Submodule.eq_of_le_of_finrank_eq hspan (by rw [finrank_span_singleton hv0]; omega)
    have hmem : ∀ i, X i v ∈ ℂ ∙ v := by
      intro i
      rw [heq, Module.End.mem_eigenspace_iff]
      have h1 : X j (X i v) = X i (X j v) := by
        have := congrArg (fun T => T v) (hX j i).eq
        simpa using this
      rw [h1, Module.End.mem_eigenspace_iff.mp hvE, map_smul]
    choose a ha using fun i => Submodule.mem_span_singleton.mp (hmem i)
    exact ⟨v, hv0, fun i => a i, fun i => (ha i).symm⟩

/-- Vector form of the classification of 2-dimensional representations of `ℂ[x_1, ..., x_n]`. -/
theorem twoDim_vector_form (hV : Module.finrank ℂ V = 2) (X : Fin n → Module.End ℂ V)
    (hX : ∀ i j, Commute (X i) (X j)) :
    (∃ (b : Module.Basis (Fin 2) ℂ V) (a d : Fin n → ℂ),
        ∀ i, X i (b 0) = a i • b 0 ∧ X i (b 1) = d i • b 1) ∨
      (∃ (b : Module.Basis (Fin 2) ℂ V) (a c : Fin n → ℂ), c ≠ 0 ∧
        ∀ i, X i (b 0) = a i • b 0 ∧ X i (b 1) = c i • b 0 + a i • b 1) := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨v, hv0, a, ha⟩ := exists_common_eigenvector hV X hX
  -- a vector outside the line through v
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ ℂ ∙ v := by
    by_contra hcon
    push Not at hcon
    have h1 : (ℂ ∙ v) = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    have := finrank_span_singleton (K := ℂ) hv0
    rw [h1, finrank_top] at this
    omega
  have hli : ∀ s t : ℂ, s • v + t • w = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      apply hw
      have : w = (-(s / t)) • v := by
        have h2 : t • w = -(s • v) := eq_neg_of_add_eq_zero_right h
        calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(s / t)) • v := by rw [h2]; module
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    subst ht
    refine ⟨?_, rfl⟩
    simpa [hv0] using h
  obtain ⟨b, hb0, hb1⟩ := exists_basis_pair hV v w hli
  have h0 : ∀ i, X i (b 0) = a i • b 0 := fun i => by rw [hb0]; exact ha i
  have hind : ∀ s t : ℂ, s • b 0 + t • b 1 = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    rw [hb0, hb1] at h
    exact hli s t h
  set c : Fin n → ℂ := fun i => b.repr (X i (b 1)) 0 with hc
  set d : Fin n → ℂ := fun i => b.repr (X i (b 1)) 1 with hd
  have hexp : ∀ i, X i (b 1) = c i • b 0 + d i • b 1 := by
    intro i
    have := b.sum_repr (X i (b 1))
    rw [Fin.sum_univ_two] at this
    exact this.symm
  have hrel : ∀ i k, c k * (a i - d i) = c i * (a k - d k) := by
    intro i k
    have e := congrArg (fun T => b.repr (T (b 1)) 0) (hX i k).eq
    simp only [mul_apply_eq_comp, hexp, map_add, map_smul, h0] at e
    simp at e
    linear_combination e
  by_cases hδ : ∀ i, a i = d i
  · by_cases hcz : c = 0
    · left
      refine ⟨b, a, d, fun i => ⟨h0 i, ?_⟩⟩
      rw [hexp, show c i = 0 from congr_fun hcz i, zero_smul, zero_add]
    · right
      refine ⟨b, a, c, hcz, fun i => ⟨h0 i, ?_⟩⟩
      rw [hexp, ← hδ i]
  · push Not at hδ
    obtain ⟨i0, hi0⟩ := hδ
    have hne : a i0 - d i0 ≠ 0 := sub_ne_zero.mpr hi0
    set s : ℂ := -(c i0 / (a i0 - d i0)) with hs
    obtain ⟨b', hb'0, hb'1⟩ := exists_basis_pair hV (b 0) (b 1 + s • b 0) (by
      intro s1 t1 h
      have := hind (s1 + t1 * s) t1 (by rw [← h]; module)
      refine ⟨?_, this.2⟩
      have h2 := this.1
      rw [this.2] at h2
      simpa using h2)
    left
    refine ⟨b', a, d, fun i => ⟨by rw [hb'0]; exact h0 i, ?_⟩⟩
    rw [hb'1, map_add, map_smul, hexp, h0]
    have hci : c i = c i0 / (a i0 - d i0) * (a i - d i) := by
      have := hrel i0 i
      field_simp
      linear_combination this
    rw [hci, hs]
    module

theorem toMatrix_two (b : Module.Basis (Fin 2) ℂ V) (f : Module.End ℂ V) (p q r s : ℂ)
    (h0 : f (b 0) = p • b 0 + q • b 1) (h1 : f (b 1) = r • b 0 + s • b 1) :
    LinearMap.toMatrix b b f = !![p, r; q, s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, h0, h1]

/-- **Etingof et al., Problem 2.22(a)**: a 2-dimensional representation of `ℂ[x_1, ..., x_n]`, i.e. commuting
operators `X_i` on a 2-dimensional complex space, has a basis in which either every `X_i` is diagonal (so
`V = V_a ⊕ V_d`), or every `X_i` has matrix `[[a_i, c_i], [0, a_i]]` with `c ≠ 0` (a non-split
self-extension of `V_a`). -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem twoDim_classification (hV : Module.finrank ℂ V = 2) (X : Fin n → Module.End ℂ V)
    (hX : ∀ i j, Commute (X i) (X j)) :
    (∃ (b : Module.Basis (Fin 2) ℂ V) (a d : Fin n → ℂ),
        ∀ i, LinearMap.toMatrix b b (X i) = !![a i, 0; 0, d i]) ∨
      (∃ (b : Module.Basis (Fin 2) ℂ V) (a c : Fin n → ℂ), c ≠ 0 ∧
        ∀ i, LinearMap.toMatrix b b (X i) = !![a i, c i; 0, a i]) := by
  rcases twoDim_vector_form hV X hX with ⟨b, a, d, h⟩ | ⟨b, a, c, hc, h⟩
  · exact Or.inl ⟨b, a, d, fun i => toMatrix_two b _ _ _ _ _ (by simp [(h i).1]) (by simp [(h i).2])⟩
  · exact Or.inr ⟨b, a, c, hc, fun i => toMatrix_two b _ _ _ _ _ (by simp [(h i).1]) (h i).2⟩

/-- **Etingof et al., Problem 2.22(a), isomorphism criterion**: two non-split self-extensions, given by bases
in which `X_i = [[a_i, c_i], [0, a_i]]` and `X'_i = [[a'_i, c'_i], [0, a'_i]]` with `c' ≠ 0`, are isomorphic
iff `a = a'` and `c'` is a nonzero scalar multiple of `c`. -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem twoDim_nonsplit_iso_iff (X : Fin n → Module.End ℂ V) (X' : Fin n → Module.End ℂ V')
    (b : Module.Basis (Fin 2) ℂ V) (b' : Module.Basis (Fin 2) ℂ V') (a c a' c' : Fin n → ℂ)
    (hc' : c' ≠ 0)
    (hX : ∀ i, X i (b 0) = a i • b 0 ∧ X i (b 1) = c i • b 0 + a i • b 1)
    (hX' : ∀ i, X' i (b' 0) = a' i • b' 0 ∧ X' i (b' 1) = c' i • b' 0 + a' i • b' 1) :
    (∃ T : V ≃ₗ[ℂ] V', ∀ i v, T (X i v) = X' i (T v)) ↔ a = a' ∧ ∃ t : ℂ, t ≠ 0 ∧ c' = t • c := by
  have hind : ∀ s t : ℂ, s • b 0 + t • b 1 = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h2 : (![b 0, b 1] : Fin 2 → V) = b := by funext j; fin_cases j <;> rfl
    have h3 : LinearIndependent ℂ ![b 0, b 1] := by rw [h2]; exact b.linearIndependent
    exact LinearIndependent.pair_iff.mp h3 s t h
  have dec : ∀ x : V', x = b'.repr x 0 • b' 0 + b'.repr x 1 • b' 1 := fun x => by
    have := b'.sum_repr x
    rw [Fin.sum_univ_two] at this
    exact this.symm
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨p, q, hu⟩ : ∃ p q : ℂ, T (b 0) = p • b' 0 + q • b' 1 := ⟨_, _, dec _⟩
    obtain ⟨r, s, hu1⟩ : ∃ r s : ℂ, T (b 1) = r • b' 0 + s • b' 1 := ⟨_, _, dec _⟩
    have e : ∀ i, X' i (T (b 0)) = a i • T (b 0) := fun i => by
      rw [← hT, (hX i).1, map_smul]
    have k : ∀ i, p * a' i + q * c' i = a i * p ∧ q * a' i = a i * q := by
      intro i
      have h := e i
      rw [hu, map_add, map_smul, map_smul, (hX' i).1, (hX' i).2] at h
      have k0 := congrArg (fun x => b'.repr x 0) h
      have k1 := congrArg (fun x => b'.repr x 1) h
      simp at k0 k1
      exact ⟨by linear_combination k0, by linear_combination k1⟩
    have hq0 : q = 0 := by
      by_contra hq
      apply hc'
      funext i
      have h1 : a' i = a i := by
        have := (k i).2
        exact mul_left_cancel₀ hq (by linear_combination this)
      have := (k i).1
      rw [h1] at this
      have h2 : q * c' i = 0 := by linear_combination this
      simpa [hq] using h2
    have hp0 : p ≠ 0 := by
      intro hp
      have : T (b 0) = 0 := by rw [hu, hp, hq0]; simp
      exact b.ne_zero 0 (T.map_eq_zero_iff.mp this)
    have haa : a = a' := by
      funext i
      have := (k i).1
      rw [hq0] at this
      exact mul_left_cancel₀ hp0 (by linear_combination -this)
    subst haa
    have hs := fun i => by
      have h := hT i (b 1)
      rw [(hX i).2, map_add, map_smul, map_smul, hu, hu1, map_add, map_smul, map_smul,
        (hX' i).1, (hX' i).2, hq0] at h
      have k0 := congrArg (fun x => b'.repr x 0) h
      simp at k0
      show s * c' i = c i * p
      linear_combination -k0
    have hs0 : s ≠ 0 := by
      intro hs0
      have := (hind (-r) p (T.injective (by
        rw [map_add, map_smul, map_smul, hu, hu1, T.map_zero, hq0, hs0]
        simp
        module))).2
      exact hp0 this
    refine ⟨rfl, p / s, div_ne_zero hp0 hs0, ?_⟩
    funext i
    have := hs i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination this
  · rintro ⟨rfl, t, ht, rfl⟩
    let bb : Module.Basis (Fin 2) ℂ V' :=
      b'.unitsSMul (fun i => if i = 0 then Units.mk0 t ht else 1)
    have hbb0 : bb 0 = t • b' 0 := by simp [bb, Module.Basis.unitsSMul_apply]
    have hbb1 : bb 1 = b' 1 := by simp [bb, Module.Basis.unitsSMul_apply]
    let T : V ≃ₗ[ℂ] V' := b.equiv bb (Equiv.refl _)
    have hT0 : T (b 0) = t • b' 0 := by
      show b.equiv bb (Equiv.refl _) (b 0) = _
      rw [Module.Basis.equiv_apply]; exact hbb0
    have hT1 : T (b 1) = b' 1 := by
      show b.equiv bb (Equiv.refl _) (b 1) = _
      rw [Module.Basis.equiv_apply]; exact hbb1
    refine ⟨T, fun i => ?_⟩
    have key : T.toLinearMap ∘ₗ X i = X' i ∘ₗ T.toLinearMap := by
      refine b.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [(hX i).1, map_smul, hT0, map_smul, (hX' i).1]
        module
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [(hX i).2, map_add, map_smul, map_smul, hT0, hT1, (hX' i).2]
        simp only [Pi.smul_apply, smul_eq_mul]
        module
    exact fun v => LinearMap.congr_fun key v

end TwoDim

end UndergradKB.RepresentationTheory
