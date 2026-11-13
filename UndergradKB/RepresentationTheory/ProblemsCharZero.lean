import UndergradKB.Common.Attr
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.MeanInequalities
import UndergradKB.RepresentationTheory.ComplexCharacters

namespace UndergradKB.RepresentationTheory

open Module Polynomial Representation

section TraceA

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A linear map `T` with `T ^ n = 1` is diagonalizable, so `tr (T ^ k) = ∑ d_μ μ ^ k` over its eigenvalues. -/
theorem exists_trace_pow_eq_sum (T : Module.End ℂ V) (n : ℕ) (hn : 0 < n) (hT : T ^ n = 1) :
    ∃ (s : Finset ℂ) (d : ℂ → ℕ), (∀ μ ∈ s, μ ^ n = 1) ∧
      ∀ k : ℕ, LinearMap.trace ℂ V (T ^ k) = ∑ μ ∈ s, (d μ : ℂ) * μ ^ k := by
  have hss : T.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ n - C 1)
    · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hn.ne') one_ne_zero).squarefree
    · simp [hT]
  have hint : DirectSum.IsInternal (fun μ : ℂ ↦ T.eigenspace μ) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨T.eigenspaces_iSupIndep, hss.iSup_eigenspace_eq_top⟩
  have hfin : {μ : ℂ | T.eigenspace μ ≠ ⊥}.Finite := by
    refine T.finite_hasEigenvalue.subset ?_
    intro μ hμ
    exact Module.End.hasEigenvalue_iff.mpr hμ
  have hpow : ∀ (k : ℕ) (μ : ℂ), ∀ x ∈ T.eigenspace μ, (T ^ k) x = μ ^ k • x := by
    intro k μ x hx
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, Module.End.mem_eigenspace_iff.mp hx, map_smul, ih,
        smul_smul, pow_succ, mul_comm]
  refine ⟨hfin.toFinset, fun μ ↦ finrank ℂ (T.eigenspace μ), ?_, ?_⟩
  · intro μ hμ
    have hμ' : T.eigenspace μ ≠ ⊥ := by simpa using hμ
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ'
    have h1 := hpow n μ v hv
    rw [hT] at h1
    have : (μ ^ n - 1) • v = 0 := by rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  · intro k
    have hmaps : ∀ μ, Set.MapsTo (T ^ k) (T.eigenspace μ) (T.eigenspace μ) := by
      intro μ x hx
      rw [SetLike.mem_coe, hpow k μ x hx]
      exact Submodule.smul_mem _ _ hx
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    have : (T ^ k).restrict (hmaps μ) = (μ ^ k) • LinearMap.id := by
      ext ⟨x, hx⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
      exact hpow k μ x hx
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end TraceA

section Galois

open ComplexConjugate

/-- The product over `(ℤ/n)ˣ` of the squared absolute values of the Galois conjugates of a nonzero sum of
`n`-th roots of unity is at least `1` (it is a nonzero rational integer, the norm of `a * ā`). -/
theorem one_le_prod_norm_sq (n : ℕ) [NeZero n] (s : Finset ℂ) (d : ℂ → ℕ) (hs : ∀ μ ∈ s, μ ^ n = 1)
    (h0 : ∑ μ ∈ s, (d μ : ℂ) * μ ≠ 0) :
    1 ≤ ∏ u : (ZMod n)ˣ, ‖∑ μ ∈ s, (d μ : ℂ) * μ ^ (u : ZMod n).val‖ ^ 2 := by
  classical
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have halg : IsAlgebraic ℚ ζ := ((hζ.isIntegral hpos).tower_top (A := ℚ)).isAlgebraic
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ζ}
  have : IsCyclotomicExtension {n} ℚ K := by
    change IsCyclotomicExtension {n} ℚ K.toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {n} ℚ K
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have hirr := cyclotomic.irreducible_rat hpos
  let e := IsCyclotomicExtension.autEquivPow K hirr
  let ζK : K := ⟨ζ, IntermediateField.subset_adjoin _ _ rfl⟩
  have hζK : ζK ^ n = 1 := Subtype.ext (by simpa [ζK] using hζ.pow_eq_one)
  have hlift : ∀ μ ∈ s, ∃ x : K, (x : ℂ) = μ ∧ x ^ n = 1 := by
    intro μ hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (hs μ hμ)
    refine ⟨ζK ^ i, by simp [ζK, hi], ?_⟩
    rw [← pow_mul, mul_comm, pow_mul, hζK, one_pow]
  choose! x hx1 hx2 using hlift
  have hnorm1 : ∀ μ ∈ s, ‖μ‖ = 1 := fun μ hμ ↦
    Complex.norm_eq_one_of_pow_eq_one (hs μ hμ) hpos.ne'
  let a : K := ∑ μ ∈ s, (d μ : K) * x μ
  let b : K := ∑ μ ∈ s, (d μ : K) * (x μ)⁻¹
  have hinvconj : ∀ μ ∈ s, ∀ k : ℕ, (μ ^ k)⁻¹ = conj (μ ^ k) := by
    intro μ hμ k
    rw [map_pow, ← Complex.inv_eq_conj (hnorm1 μ hμ), inv_pow]
  have key : ∀ u : (ZMod n)ˣ, (((e.symm u) (a * b) : K) : ℂ) =
      ((‖∑ μ ∈ s, (d μ : ℂ) * μ ^ (u : ZMod n).val‖ ^ 2 : ℝ) : ℂ) := by
    intro u
    have hσ : ∀ μ ∈ s, (e.symm u) (x μ) = (x μ) ^ (u : ZMod n).val := fun μ hμ ↦ by
      rw [IsCyclotomicExtension.autEquivPow_apply_of_pow_eq_one K hirr _ (hx2 μ hμ)]
      simp [e]
    set c : ℂ := ∑ μ ∈ s, (d μ : ℂ) * μ ^ (u : ZMod n).val with hc
    have hv : ∀ μ ∈ s, K.val (x μ) = μ := hx1
    have h1 : (((e.symm u) a : K) : ℂ) = c := by
      change K.val ((e.symm u) a) = c
      simp only [a, map_sum, map_mul, map_natCast, hc]
      refine Finset.sum_congr rfl fun μ hμ ↦ ?_
      rw [hσ μ hμ, map_pow, hv μ hμ]
    have h2 : (((e.symm u) b : K) : ℂ) = conj c := by
      change K.val ((e.symm u) b) = conj c
      simp only [b, map_sum, map_mul, map_natCast, hc, map_inv₀]
      refine Finset.sum_congr rfl fun μ hμ ↦ ?_
      rw [hσ μ hμ, map_pow, hv μ hμ, hinvconj μ hμ]
    change K.val ((e.symm u) (a * b)) = _
    rw [map_mul, map_mul]
    change (((e.symm u) a : K) : ℂ) * (((e.symm u) b : K) : ℂ) = _
    rw [h1, h2, Complex.mul_conj']
    simp
  have hsum_a : ((a : K) : ℂ) = ∑ μ ∈ s, (d μ : ℂ) * μ := by
    change K.val a = _
    simp only [a, map_sum, map_mul, map_natCast]
    exact Finset.sum_congr rfl fun μ hμ ↦ by rw [show K.val (x μ) = μ from hx1 μ hμ]
  have hsum_b : ((b : K) : ℂ) = conj (∑ μ ∈ s, (d μ : ℂ) * μ) := by
    change K.val b = _
    simp only [b, map_sum, map_mul, map_natCast, map_inv₀]
    refine Finset.sum_congr rfl fun μ hμ ↦ ?_
    rw [show K.val (x μ) = μ from hx1 μ hμ, ← Complex.inv_eq_conj (hnorm1 μ hμ)]
  have hint_x : ∀ μ ∈ s, IsIntegral ℤ (x μ) := fun μ hμ ↦
    IsIntegral.of_pow hpos (by rw [hx2 μ hμ]; exact isIntegral_one)
  have hint_xi : ∀ μ ∈ s, IsIntegral ℤ (x μ)⁻¹ := fun μ hμ ↦
    IsIntegral.of_pow hpos (by rw [inv_pow, hx2 μ hμ, inv_one]; exact isIntegral_one)
  have hna : ∀ m : ℕ, IsIntegral ℤ (m : K) := fun m ↦ by
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := (m : ℤ))
  have hya : IsIntegral ℤ a := IsIntegral.sum _ fun μ hμ ↦ (hna _).mul (hint_x μ hμ)
  have hyb : IsIntegral ℤ b := IsIntegral.sum _ fun μ hμ ↦ (hna _).mul (hint_xi μ hμ)
  have hy0 : a * b ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h
      apply h0
      rw [← hsum_a, h]; rfl
    · intro h
      apply h0
      have : conj (∑ μ ∈ s, (d μ : ℂ) * μ) = 0 := by rw [← hsum_b, h]; rfl
      exact (map_eq_zero (starRingEnd ℂ)).mp this
  have hN := Algebra.norm_eq_prod_automorphisms ℚ (a * b)
  have hNint : IsIntegral ℤ (Algebra.norm ℚ (a * b)) := Algebra.isIntegral_norm ℚ (hya.mul hyb)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hNint
  have hNne : Algebra.norm ℚ (a * b) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hy0
  have hmne : m ≠ 0 := by
    rintro rfl
    exact hNne (by rw [← hm]; simp)
  have hprod : ((m : ℝ)) = ∏ u : (ZMod n)ˣ, ‖∑ μ ∈ s, (d μ : ℂ) * μ ^ (u : ZMod n).val‖ ^ 2 := by
    have h3 : ((algebraMap ℚ K (Algebra.norm ℚ (a * b)) : K) : ℂ) =
        ((∏ u : (ZMod n)ˣ, ‖∑ μ ∈ s, (d μ : ℂ) * μ ^ (u : ZMod n).val‖ ^ 2 : ℝ) : ℂ) := by
      change K.val (algebraMap ℚ K (Algebra.norm ℚ (a * b))) = _
      rw [hN, map_prod, Complex.ofReal_prod]
      rw [Fintype.prod_equiv e.toEquiv (fun σ ↦ K.val (σ (a * b)))
        (fun u ↦ K.val ((e.symm u) (a * b))) (fun σ ↦ by simp)]
      exact Finset.prod_congr rfl fun u _ ↦ key u
    rw [← hm] at h3
    have h4 : ((m : ℚ) : ℂ) = (m : ℂ) := by simp
    simp only [eq_ratCast] at h3
    have : ((m : ℝ) : ℂ) = ((∏ u : (ZMod n)ˣ, ‖∑ μ ∈ s, (d μ : ℂ) * μ ^ (u : ZMod n).val‖ ^ 2 : ℝ) : ℂ) := by
      rw [← h3]; push_cast; rfl
    exact_mod_cast this
  have hge : (0 : ℝ) ≤ m := by
    rw [hprod]; exact Finset.prod_nonneg fun u _ ↦ by positivity
  have : (1 : ℤ) ≤ m := by
    have : 0 < m := lt_of_le_of_ne (by exact_mod_cast hge) (Ne.symm hmne)
    omega
  rw [← hprod]; exact_mod_cast this

end Galois

section Main

open ComplexConjugate

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V)

/-- Character values at powers of `g` are the power sums of the eigenvalues. -/
theorem exists_character_pow_eq_sum (g : G) :
    ∃ (s : Finset ℂ) (d : ℂ → ℕ), (∀ μ ∈ s, μ ^ Nat.card G = 1) ∧
      ∀ k : ℕ, ρ.character (g ^ k) = ∑ μ ∈ s, (d μ : ℂ) * μ ^ k := by
  obtain ⟨s, d, hs, h⟩ := exists_trace_pow_eq_sum (ρ g) (Nat.card G) Nat.card_pos (by
    rw [← map_pow, pow_card_eq_one', map_one])
  exact ⟨s, d, hs, fun k ↦ by rw [Representation.character, map_pow, h]⟩

/-- For each `g` with `χ(g) ≠ 0`, the sum of `|χ(g ^ a)|²` over `a ∈ (ℤ/|G|)ˣ` is at least `φ(|G|)`. -/
theorem card_units_le_sum_norm_sq (g : G) (hg : ρ.character g ≠ 0) :
    (Fintype.card (ZMod (Nat.card G))ˣ : ℝ) ≤
      ∑ u : (ZMod (Nat.card G))ˣ, ‖ρ.character (g ^ (u : ZMod (Nat.card G)).val)‖ ^ 2 := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨s, d, hs, h⟩ := exists_character_pow_eq_sum ρ g
  have h1 : ∑ μ ∈ s, (d μ : ℂ) * μ ≠ 0 := by
    have := h 1
    rw [pow_one] at this
    simpa [this] using hg
  have hP := one_le_prod_norm_sq (Nat.card G) s d hs h1
  simp only [← h] at hP
  have hm : 0 < (Fintype.card (ZMod (Nat.card G))ˣ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have := Real.geom_mean_le_arith_mean (Finset.univ : Finset (ZMod (Nat.card G))ˣ) (fun _ ↦ (1 : ℝ))
    (fun u ↦ ‖ρ.character (g ^ (u : ZMod (Nat.card G)).val)‖ ^ 2) (fun _ _ ↦ zero_le_one)
    (by simpa using hm) (fun _ _ ↦ by positivity)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at this
  have h2 : 1 ≤ (∏ u : (ZMod (Nat.card G))ˣ, ‖ρ.character (g ^ (u : ZMod (Nat.card G)).val)‖ ^ 2) ^
      ((Fintype.card (ZMod (Nat.card G))ˣ : ℝ))⁻¹ :=
    Real.one_le_rpow hP (by positivity)
  have h3 := h2.trans this
  rwa [le_div_iff₀ hm, one_mul] at h3

variable [IsIrreducible ρ]

/-- Sum of squared character norms over an irreducible complex representation. -/
theorem sum_norm_sq_character : ∑ g, ‖ρ.character g‖ ^ 2 = (Nat.card G : ℝ) := by
  classical
  have h := hermitianPairing_irreducible ρ ρ
  rw [if_pos (⟨Representation.Equiv.refl ρ⟩ : Nonempty (Representation.Equiv ρ ρ))] at h
  unfold hermitianPairing at h
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : ∑ g, ρ.character g * conj (ρ.character g) = (Nat.card G : ℂ) := by
    field_simp at h
    exact h
  simp only [Complex.mul_conj'] at h2
  exact_mod_cast h2

/-- **Burnside** (Etingof et al., Problem 4.15(b)): an irreducible complex representation of a finite group
of dimension greater than `1` has a group element whose character value is zero. -/
@[kb "etingof2011" "Problem 4.15, p. 51"]
theorem exists_character_eq_zero_of_one_lt_finrank (h : 1 < Module.finrank ℂ V) :
    ∃ g : G, ρ.character g = 0 := by
  by_contra hne
  push Not at hne
  set n := Nat.card G with hn
  have : NeZero n := ⟨Nat.card_pos.ne'⟩
  set m : ℕ := Fintype.card (ZMod n)ˣ with hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Fintype.card_pos
  have hcol : ∀ u : (ZMod n)ˣ, ∑ g : G, ‖ρ.character (g ^ (u : ZMod n).val)‖ ^ 2 = n := by
    intro u
    have hcop : (Nat.card G).Coprime (u : ZMod n).val := (ZMod.val_coe_unit_coprime u).symm
    rw [← sum_norm_sq_character ρ]
    exact Equiv.sum_comp (powCoprime hcop) (fun g ↦ ‖ρ.character g‖ ^ 2)
  have hA : ∑ g : G, ∑ u : (ZMod n)ˣ, ‖ρ.character (g ^ (u : ZMod n).val)‖ ^ 2 = m * n := by
    rw [Finset.sum_comm]
    simp [hcol, hm, mul_comm]
  have hB : ∑ g : G, (m : ℝ) < ∑ g : G, ∑ u : (ZMod n)ˣ, ‖ρ.character (g ^ (u : ZMod n).val)‖ ^ 2 := by
    refine Finset.sum_lt_sum (fun g _ ↦ card_units_le_sum_norm_sq ρ g (hne g)) ⟨1, Finset.mem_univ _, ?_⟩
    simp only [one_pow, char_one, Complex.norm_natCast]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← hm]
    have : (1 : ℝ) < Module.finrank ℂ V := by exact_mod_cast h
    have h2 : (1 : ℝ) < (Module.finrank ℂ V : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h2 hmpos]
  rw [hA] at hB
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hB
  have : Fintype.card G = n := (Nat.card_eq_fintype_card).symm
  rw [this] at hB
  linarith

end Main

end UndergradKB.RepresentationTheory
