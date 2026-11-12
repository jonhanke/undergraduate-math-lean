import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.Floor
import UndergradKB.Common.Attr
import UndergradKB.Geometry.Constructible
import UndergradKB.Geometry.RulerCompassConverse

/-! # Squaring the circle is impossible

Petrunin's list of impossible constructions (p. 158) includes squaring the circle: a square with the area of the
unit disc has side `√π`, and this length cannot be built by ruler and compass. The argument has two parts.

* `π` is transcendental over `ℚ` (Lindemann, 1882). Mathlib supplies the analytic half of the
  Lindemann-Weierstrass theorem and the evaluation of symmetric polynomials at roots; we complete Hermite's
  and Lindemann's argument. If `π` were algebraic, so would be `x = π i`, with conjugates `α₁, …, αₙ`. From
  `e^{π i} = -1` the product `∏ (1 + e^{αⱼ})` vanishes; expanding it gives `k + ∑_T e^{σ_T} = 0` where
  `σ_T` are the nonzero subset sums of the `αⱼ` (roots of an integer polynomial, as the coefficients of
  `∏_T (X - σ_T)` are symmetric in the `αⱼ`) and `k ≥ 1`. The analytic estimate then yields, for large
  primes `p`, a nonzero integer of absolute value below `1`.
* A constructible number is algebraic over `ℚ` (its degree is a power of 2, see `Constructible.lean`), so `√π`
  constructible would make `π = (√π)²` algebraic.

Finally, via Theorem 19.8 (`rcConstructible_iff`), no ruler-and-compass construction starting from `(0,0)`
and `(1,0)` produces the point `(√π, 0)`. -/

namespace UndergradKB.Geometry

open Polynomial Complex Finset
open scoped Nat

section Analytic

/-- The arithmetic heart of the proof: if `F` is an integer polynomial with `F 0 ≠ 0` and `k ≥ 1`, then
`k + ∑_{r root of F} e^r ≠ 0`. -/
theorem pi_nat_add_sum_exp_aroots_ne_zero (F : ℤ[X]) (hF0 : F.eval 0 ≠ 0) (k : ℕ) (hk : 0 < k) :
    (k : ℂ) + ((F.aroots ℂ).map exp).sum ≠ 0 := by
  intro hsum
  have hsplit : (F.map (algebraMap ℤ ℂ)).Splits := IsAlgClosed.splits _
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx F hF0
  set d := F.leadingCoeff with hd
  set m := F.natDegree with hm
  set N := (F.aroots ℂ).card with hN
  have hF : F ≠ 0 := by rintro rfl; simp at hF0
  have hd0 : d ≠ 0 := leadingCoeff_ne_zero.mpr hF
  set A : ℝ := |(d : ℝ)| ^ m * |c| with hA
  have hA0 : 0 ≤ A := by positivity
  -- eventually `N * A * A ^ q / q! < 1`
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop A
  have hev : ∀ᶠ q : ℕ in Filter.atTop, A ^ q / q ! < 1 / (N * A + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨p, hpge, hp⟩ :=
    Nat.exists_infinite_primes (Q + (F.eval 0).natAbs + k + d.natAbs + 2)
  have hpF : p > (F.eval 0).natAbs := by omega
  obtain ⟨np, hnp, gp, hgp, hbound⟩ := hc p hpF hp
  set e := p * m with he
  have hmem := pow_smul_sum_map_aroots_aeval_mem_range_algebraMap (A := ℂ) F gp d e dvd_rfl
    (hgp.trans (Nat.sub_le _ _)) hsplit
  obtain ⟨z, hz⟩ := hmem
  -- the integer `W`
  set W : ℤ := d ^ e * np * k + p * z with hW
  have hWC : (W : ℂ) = - (d : ℂ) ^ e *
      ((F.aroots ℂ).map (fun r => (np : ℂ) * exp r - (p : ℂ) * aeval r gp)).sum := by
    have hz' : ((z : ℤ) : ℂ) = (d : ℂ) ^ e * ((F.aroots ℂ).map (fun r => aeval r gp)).sum := by
      have hz2 : ((z : ℤ) : ℂ) = algebraMap ℤ ℂ z := rfl
      rw [hz2, hz]; simp [zsmul_eq_mul]
    have hk' : (k : ℂ) = - ((F.aroots ℂ).map exp).sum := by linear_combination hsum
    rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
    simp only [hW, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, hz', hk']
    ring
  -- `p` does not divide `W`, hence `W ≠ 0`
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hW0 : W ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ d ^ e * np * k := by
      have : (p : ℤ) ∣ W := h0 ▸ dvd_zero _
      rw [hW] at this
      exact (dvd_add_left (dvd_mul_right _ _)).mp this
    rcases hpZ.dvd_or_dvd hdvd with h1 | h3
    · rcases hpZ.dvd_or_dvd h1 with h2 | h2
      · have := Int.natAbs_dvd_natAbs.mpr (hpZ.dvd_of_dvd_pow h2)
        simp only [Int.natAbs_natCast] at this
        have := Nat.le_of_dvd (Int.natAbs_pos.mpr hd0) this
        omega
      · exact hnp h2
    · have := Int.natAbs_dvd_natAbs.mpr h3
      simp only [Int.natAbs_natCast] at this
      have := Nat.le_of_dvd hk this
      omega
  have hW1 : (1 : ℝ) ≤ ‖(W : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hW0
  -- the upper bound
  have hp1 : 1 ≤ p := hp.one_le
  have hsumle : ‖((F.aroots ℂ).map (fun r => (np : ℂ) * exp r - (p : ℂ) * aeval r gp)).sum‖ ≤
      N * (|c| ^ p / (p - 1)!) := by
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map]
    refine (Multiset.sum_le_card_nsmul _ (|c| ^ p / (p - 1)!) ?_).trans ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      have := hbound hr
      simp only [zsmul_eq_mul, nsmul_eq_mul] at this
      refine this.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      rw [← abs_pow]
      exact le_abs_self _
    · simp [hN, Multiset.card_map, nsmul_eq_mul]
  have hupper : ‖(W : ℂ)‖ ≤ N * A * (A ^ (p - 1) / (p - 1)!) := by
    rw [hWC, norm_mul, norm_neg, norm_pow, Complex.norm_intCast]
    calc |(d : ℝ)| ^ e * ‖_‖ ≤ |(d : ℝ)| ^ e * (N * (|c| ^ p / (p - 1)!)) := by gcongr
      _ = N * A * (A ^ (p - 1) / (p - 1)!) := by
        have e1 : |(d : ℝ)| ^ e = (|(d : ℝ)| ^ m) ^ (p - 1) * |(d : ℝ)| ^ m := by
          rw [← pow_succ, Nat.sub_add_cancel hp1, ← pow_mul, he, mul_comm]
        have e2 : |c| ^ p = |c| ^ (p - 1) * |c| := by rw [← pow_succ, Nat.sub_add_cancel hp1]
        rw [e1, e2, hA, mul_pow]
        ring
  have hsmall : A ^ (p - 1) / (p - 1)! < 1 / (N * A + 1) := hQ (p - 1) (by omega)
  have hNA : 0 ≤ (N : ℝ) * A := by positivity
  have : (N : ℝ) * A * (A ^ (p - 1) / (p - 1)!) < 1 := by
    calc (N : ℝ) * A * (A ^ (p - 1) / (p - 1)!) ≤ (N * A) * (1 / (N * A + 1)) := by
          gcongr
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]
          linarith
  linarith

end Analytic

section Algebraic

/-- The generic subset-sum polynomial `∏_T (X - ∑_{i ∈ T} Xᵢ)`, over all subsets `T` of `{0, …, n-1}`, with
coefficients in the polynomials in `n` variables over `ℚ`. -/
noncomputable def piSubsetSumPoly (n : ℕ) : (MvPolynomial (Fin n) ℚ)[X] :=
  ∏ T : Finset (Fin n), (X - C (∑ i ∈ T, MvPolynomial.X i))

/-- The coefficients of the subset-sum polynomial are symmetric. -/
theorem piSubsetSumPoly_coeff_mem (n j : ℕ) :
    (piSubsetSumPoly n).coeff j ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℚ := by
  rw [MvPolynomial.mem_symmetricSubalgebra]
  intro e
  have h : (piSubsetSumPoly n).map (MvPolynomial.rename (R := ℚ) e).toRingHom = piSubsetSumPoly n := by
    simp only [piSubsetSumPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine Fintype.prod_equiv (Equiv.finsetCongr e) _ _ (fun T => ?_)
    simp [Equiv.finsetCongr_apply, Finset.sum_map, map_sum, MvPolynomial.rename_X]
  conv_rhs => rw [← h]
  rw [Polynomial.coeff_map]
  rfl

/-- If `α₁, …, αₙ` are the complex roots of a monic rational polynomial, then `∏_T (X - ∑_{i ∈ T} αᵢ)` has
rational coefficients. -/
theorem pi_prod_subsetSum_mem_lifts (f : ℚ[X]) (hf : f.Monic) {n : ℕ} (α : Fin n → ℂ)
    (hα : univ.val.map α = f.aroots ℂ) :
    (∏ T : Finset (Fin n), (X - C (∑ i ∈ T, α i))) ∈ Polynomial.lifts (algebraMap ℚ ℂ) := by
  rw [lifts_iff_coeff_lifts]
  intro j
  have key : (∏ T : Finset (Fin n), (X - C (∑ i ∈ T, α i))) =
      (piSubsetSumPoly n).map (MvPolynomial.aeval (R := ℚ) α).toRingHom := by
    simp only [piSubsetSumPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine Finset.prod_congr rfl (fun T _ => ?_)
    simp [map_sum, MvPolynomial.aeval_X]
  rw [key, Polynomial.coeff_map]
  have := MvPolynomial.symmetricSubalgebra.aevalMultiset_map_aroots_mem_range_algebraMap
    (σ := Fin n) (R := ℚ) (S := ℚ) (A := ℂ) (q := f)
    (p := ⟨_, piSubsetSumPoly_coeff_mem n j⟩) (IsAlgClosed.splits _)
  rw [hf.leadingCoeff, ← hα] at this
  simp only [one_smul, Multiset.map_id'] at this
  rw [MvPolynomial.symmetricSubalgebra.aevalMultiset_map] at this
  exact this

/-- Lindemann's theorem (1882): `π` is transcendental over `ℚ`. -/
@[kb "petrunin2025" "Impossible-constructions list, p. 158"]
theorem transcendental_pi : Transcendental ℚ Real.pi := by
  classical
  intro hπ
  set x : ℂ := (Real.pi : ℂ) * I with hx
  have hxint : IsIntegral ℚ x := by
    have h1 : IsIntegral ℚ ((Real.pi : ℝ) : ℂ) := (hπ.algebraMap (A := ℂ)).isIntegral
    have h2 : IsIntegral ℚ I := by
      refine ⟨X ^ 2 + 1, by monicity!, ?_⟩
      simp
    exact h1.mul h2
  set f := minpoly ℚ x with hfdef
  have hfm : f.Monic := minpoly.monic hxint
  have hxroot : x ∈ f.aroots ℂ :=
    mem_aroots.mpr ⟨minpoly.ne_zero hxint, minpoly.aeval ℚ x⟩
  set L := (f.aroots ℂ).toList with hL
  let α : Fin L.length → ℂ := L.get
  have hα : univ.val.map α = f.aroots ℂ := by
    rw [Fin.univ_val_map]
    show ((List.ofFn L.get : List ℂ) : Multiset ℂ) = _
    rw [List.ofFn_get, hL, Multiset.coe_toList]
  obtain ⟨i₀, hi₀⟩ : ∃ i, α i = x := List.mem_iff_get.mp (Multiset.mem_toList.mpr hxroot)
  -- the vanishing product and its expansion
  have hprod : ∏ i, (1 + exp (α i)) = 0 :=
    Finset.prod_eq_zero (mem_univ i₀) (by rw [hi₀, hx, exp_pi_mul_I]; ring)
  rw [Finset.prod_one_add, Finset.powerset_univ] at hprod
  simp_rw [← Complex.exp_sum] at hprod
  set σ : Finset (Fin L.length) → ℂ := fun T => ∑ i ∈ T, α i with hσ
  set Z := univ.filter (fun T => σ T = 0) with hZ
  set NZ := univ.filter (fun T => ¬ σ T = 0) with hNZ
  have hk : 0 < Z.card := Finset.card_pos.mpr ⟨∅, by simp [Z, σ]⟩
  have hsum : (Z.card : ℂ) + ∑ T ∈ NZ, exp (σ T) = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun T => σ T = 0)] at hprod
    have : ∑ T ∈ Z, exp (σ T) = Z.card := by
      rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_filter.mp hT).2, exp_zero])]
      simp
    rw [← this]
    exact hprod
  -- the polynomial with roots the nonzero subset sums
  set G : ℂ[X] := ∏ T ∈ NZ, (X - C (σ T)) with hG
  have hP : (∏ T : Finset (Fin L.length), (X - C (σ T))) = X ^ Z.card * G := by
    rw [← Finset.prod_filter_mul_prod_filter_not univ (fun T => σ T = 0)]
    congr 1
    rw [Finset.prod_congr rfl (fun T hT => by rw [(Finset.mem_filter.mp hT).2, C_0, sub_zero]),
      Finset.prod_const]
  obtain ⟨Pq, hPq⟩ := (mem_lifts _).mp (pi_prod_subsetSum_mem_lifts f hfm α hα)
  set Gq := Pq /ₘ X ^ Z.card with hGqdef
  have hGq : Gq.map (algebraMap ℚ ℂ) = G := by
    rw [hGqdef, map_divByMonic _ (monic_X_pow _), hPq, hP, Polynomial.map_pow, Polynomial.map_X]
    exact mul_divByMonic_cancel_left G (monic_X_pow _)
  obtain ⟨b, hb, hbG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Gq
  set F := IsLocalization.integerNormalization (nonZeroDivisors ℤ) Gq with hFdef
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hFC : F.map (algebraMap ℤ ℂ) = C (b : ℂ) * G := by
    have hbs : b • Gq = C (b : ℚ) * Gq := by rw [← smul_eq_C_mul, Int.cast_smul_eq_zsmul]
    rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hbG, hbs,
      Polynomial.map_mul, Polynomial.map_C, hGq]
    simp
  have hroots : F.aroots ℂ = NZ.val.map σ := by
    have hcomp : (fun T => X - C (σ T)) = (fun a => X - C a) ∘ σ := rfl
    rw [aroots, hFC, roots_C_mul _ (by exact_mod_cast hb0), hG, Finset.prod_eq_multiset_prod,
      hcomp, ← Multiset.map_map, roots_multiset_prod_X_sub_C]
  have hF0 : F.eval 0 ≠ 0 := by
    intro h
    have h' : (F.map (algebraMap ℤ ℂ)).eval 0 = 0 := by
      rw [eval_zero_map, h, map_zero]
    rw [hFC, eval_mul, eval_C, hG, eval_prod] at h'
    simp only [eval_sub, eval_X, eval_C, zero_sub, mul_eq_zero, Int.cast_eq_zero, hb0, false_or,
      Finset.prod_eq_zero_iff, neg_eq_zero] at h'
    obtain ⟨T, hT, hT0⟩ := h'
    exact (Finset.mem_filter.mp hT).2 hT0
  apply pi_nat_add_sum_exp_aroots_ne_zero F hF0 Z.card hk
  rw [hroots, Multiset.map_map]
  exact hsum

end Algebraic

/-- Squaring the circle is impossible: `√π`, the side of a square with the area of the unit disc, is not a
constructible number. -/
@[kb "petrunin2025" "Impossible-constructions list, p. 158"]
theorem not_isConstructible_sqrt_pi : ¬ IsConstructible (Real.sqrt Real.pi) := by
  intro h
  obtain ⟨hint, -⟩ := h.natDegree_minpoly
  apply transcendental_pi
  have h2 : IsAlgebraic ℚ (Real.sqrt Real.pi ^ 2) := hint.isAlgebraic.pow 2
  rwa [Real.sq_sqrt Real.pi_pos.le] at h2

/-- Squaring the circle by ruler and compass (Theorem 19.8): starting from `(0,0)` and `(1,0)`, one cannot
construct the vertex `(√π, 0)` of a square with the area of the unit disc. -/
@[kb "petrunin2025" "Impossible-constructions list, p. 158"]
theorem not_rcConstructible_sqrt_pi :
    ¬ RCConstructible {(0, 0), (1, 0)} (.point (Real.sqrt Real.pi, 0)) := by
  intro h
  exact not_isConstructible_sqrt_pi (rcConstructible_iff.mp h).1

end UndergradKB.Geometry
