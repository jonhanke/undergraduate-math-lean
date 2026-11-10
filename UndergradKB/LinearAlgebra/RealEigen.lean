import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.IsRealClosed.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import UndergradKB.Common.Attr

/-! # Operators on real vector spaces (Axler 5.B)

Eigenvalues in odd dimension, the even dimension of the null space of `T^2 + bT + cI`, and invariant
subspaces of dimension two.  `V` is a finite-dimensional real vector space.
-/

open Polynomial Module End

namespace UndergradKB.LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Every operator on an odd-dimensional real vector space has an eigenvalue. (Proof: the
characteristic polynomial has odd degree `dim V`, hence a real root.) -/
@[kb "axler2024" "5.34, p. 168"]
theorem axler_5_34 (hodd : Odd (finrank ℝ V)) (T : End ℝ V) : ∃ μ : ℝ, HasEigenvalue T μ := by
  have hdeg : Odd (LinearMap.charpoly T).natDegree := by
    rwa [LinearMap.charpoly_natDegree]
  obtain ⟨μ, hμ⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hdeg
  exact ⟨μ, (hasEigenvalue_iff_isRoot_charpoly T μ).mpr hμ⟩

/-- For `b^2 < 4c`, the null space of `T^2 + bT + cI` on a real vector space has even dimension. -/
@[kb "axler2024" "5.33, p. 167"]
theorem axler_5_33 (T : End ℝ V) {b c : ℝ} (hbc : b ^ 2 < 4 * c) :
    Even (finrank ℝ (LinearMap.ker (T ^ 2 + b • T + c • (1 : End ℝ V)))) := by
  have hc : Commute T (T ^ 2 + b • T + c • (1 : End ℝ V)) :=
    (((Commute.refl T).pow_right 2).add_right ((Commute.refl T).smul_right b)).add_right
      ((Commute.one_right T).smul_right c)
  have hU : ∀ x ∈ LinearMap.ker (T ^ 2 + b • T + c • (1 : End ℝ V)),
      T x ∈ LinearMap.ker (T ^ 2 + b • T + c • (1 : End ℝ V)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h := congr($(hc.eq) x)
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hx, map_zero] at h
    exact h.symm
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨μ, hμ⟩ := axler_5_34 hodd (LinearMap.restrict T hU)
  obtain ⟨u, hu⟩ := hμ.exists_hasEigenvector
  have h1 : T (u : V) = μ • (u : V) := by
    have := mem_eigenspace_iff.mp hu.1
    exact congrArg Subtype.val this
  have h2 : (T ^ 2 + b • T + c • (1 : End ℝ V)) (u : V) = 0 := LinearMap.mem_ker.mp u.2
  have h2' : (T ^ 2 + b • T + c • (1 : End ℝ V)) (u : V) = T (T u) + b • T u + c • (u : V) := by
    simp [pow_two]
  have h3 : (μ ^ 2 + b * μ + c) • (u : V) = 0 := by
    rw [h2', h1, map_smul, h1] at h2
    rw [← h2]
    simp only [add_smul, mul_smul, pow_two]
  have hu0 : (u : V) ≠ 0 := fun h => hu.2 (Subtype.ext h)
  have h4 : μ ^ 2 + b * μ + c = 0 := (smul_eq_zero.mp h3).resolve_right hu0
  nlinarith [sq_nonneg (2 * μ + b)]

section TwoDim

/-- A monic irreducible real polynomial is `x - l` or `x^2 + b x + c` with `b^2 < 4c`. -/
lemma real_irreducible_cases {q : ℝ[X]} (hm : q.Monic) (hi : Irreducible q) :
    (∃ l : ℝ, q = X - C l) ∨ ∃ b c : ℝ, b ^ 2 < 4 * c ∧ q = X ^ 2 + C b * X + C c := by
  have h1 := hi.natDegree_pos
  have h2 := hi.natDegree_le_two
  by_cases hroot : ∃ μ, q.IsRoot μ
  · obtain ⟨μ, hμ⟩ := hroot
    have hd : q.degree = 1 := degree_eq_one_of_irreducible_of_root hi hμ
    have hnd : q.natDegree = 1 := natDegree_eq_of_degree_eq_some hd
    obtain ⟨a, ha⟩ : ∃ a, q = X + C a := ⟨_, hm.eq_X_add_C hnd⟩
    left
    exact ⟨-a, by rw [ha]; simp [sub_eq_add_neg]⟩
  · push Not at hroot
    have hnd : q.natDegree = 2 := by
      by_contra hne
      have h1' : q.natDegree = 1 := by omega
      obtain ⟨a, ha⟩ : ∃ a, q = X + C a := ⟨_, hm.eq_X_add_C h1'⟩
      apply hroot (-a)
      rw [ha]
      simp
    have hq : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
      ext n
      have hlead : q.coeff 2 = 1 := by simpa [hnd] using hm.coeff_natDegree
      rcases n with _ | _ | _ | n
      · simp [coeff_C]
      · simp [coeff_C]
      · simp [hlead]
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    obtain ⟨b, c, hbc⟩ : ∃ b c : ℝ, q = X ^ 2 + C b * X + C c := ⟨_, _, hq⟩
    right
    refine ⟨b, c, ?_, hbc⟩
    by_contra hlt
    push Not at hlt
    have hs2 : Real.sqrt (b ^ 2 - 4 * c) ^ 2 = b ^ 2 - 4 * c := Real.sq_sqrt (by linarith)
    apply hroot ((-b + Real.sqrt (b ^ 2 - 4 * c)) / 2)
    rw [hbc]
    simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    nlinarith

/-- Every nonzero real operator-vector has a "small" annihilator: some nonzero `v` is an eigenvector
or satisfies `T^2 v + b T v + c v = 0` with `b^2 < 4c`. -/
lemma exists_vec [Nontrivial V] (T : End ℝ V) :
    ∃ v : V, v ≠ 0 ∧ ((∃ l : ℝ, T v = l • v) ∨
      ∃ b c : ℝ, b ^ 2 < 4 * c ∧ T (T v) + b • T v + c • v = 0) := by
  have hint : IsIntegral ℝ T := Algebra.IsIntegral.isIntegral T
  have hm := minpoly.monic hint
  have hnu : ¬ IsUnit (minpoly ℝ T) := by
    rw [hm.isUnit_iff]
    exact minpoly.ne_one ℝ T
  obtain ⟨q, hqm, hqi, r, hr⟩ := exists_monic_irreducible_factor _ hnu
  have hr0 : aeval T r ≠ 0 := by
    intro h
    have hd := minpoly.dvd ℝ T h
    have hrne : r ≠ 0 := right_ne_zero_of_mul (hr ▸ hm.ne_zero)
    have h1 := natDegree_le_of_dvd hd hrne
    have h2 : (minpoly ℝ T).natDegree = q.natDegree + r.natDegree := by
      rw [hr, natDegree_mul hqi.ne_zero hrne]
    have := hqi.natDegree_pos
    omega
  obtain ⟨w, hw⟩ : ∃ w, aeval T r w ≠ 0 := by
    by_contra h
    push Not at h
    exact hr0 (LinearMap.ext h)
  have hq0 : aeval T q (aeval T r w) = 0 := by
    have h := congr($(minpoly.aeval ℝ T) w)
    rw [hr, map_mul, mul_apply_eq_comp] at h
    simpa using h
  generalize aeval T r w = v at hw hq0
  refine ⟨v, hw, ?_⟩
  rcases real_irreducible_cases hqm hqi with ⟨l, rfl⟩ | ⟨b, c, hbc, rfl⟩
  · left
    refine ⟨l, ?_⟩
    have : T v - l • v = 0 := by simpa [Module.algebraMap_end_apply] using hq0
    exact sub_eq_zero.mp this
  · right
    refine ⟨b, c, hbc, ?_⟩
    simpa [pow_two, Module.algebraMap_end_apply] using hq0

omit [FiniteDimensional ℝ V] in
lemma two_dim_of_quad (T : End ℝ V) {v : V} (hv : v ≠ 0) {b c : ℝ} (hbc : b ^ 2 < 4 * c)
    (h : T (T v) + b • T v + c • v = 0) :
    ∃ S : Submodule ℝ V, (∀ x ∈ S, T x ∈ S) ∧ finrank ℝ S = 2 := by
  have hT2 : T (T v) = (-b) • T v + (-c) • v := by
    have : T (T v) = -(b • T v + c • v) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact h
    rw [this]; module
  have hli : LinearIndependent ℝ ![v, T v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      have h1 : t • T v = -(s • v) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have hTv : T v = (-(s / t)) • v := by
        calc T v = t⁻¹ • (t • T v) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(s / t)) • v := by rw [h1]; module
      have h3 : ((-(s / t)) * (-(s / t)) + b * (-(s / t)) + c) • v = 0 := by
        have h' := h
        rw [hTv, map_smul, hTv] at h'
        rw [← h']
        module
      have h4 := (smul_eq_zero.mp h3).resolve_right hv
      nlinarith [sq_nonneg (2 * (-(s / t)) + b)]
    subst ht
    refine ⟨?_, rfl⟩
    simp only [zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right hv
  refine ⟨Submodule.span ℝ (Set.range ![v, T v]), ?_, ?_⟩
  · intro x hx
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
      ⟨![-(cf 1 * c), cf 0 - cf 1 * b], ?_⟩
    simp only [Fin.sum_univ_two, map_add, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, hT2]
    module
  · rw [finrank_span_eq_card hli]
    simp

/-- Every operator on a finite-dimensional real vector space of dimension at least `2` has an
invariant subspace of dimension `2`. -/
@[kb "axler2024" "Ex5B.29, p. 171"]
theorem axler_5B_29 (hV : 2 ≤ finrank ℝ V) (T : End ℝ V) :
    ∃ S : Submodule ℝ V, (∀ x ∈ S, T x ∈ S) ∧ finrank ℝ S = 2 := by
  have hpos : 0 < finrank ℝ V := by omega
  have : Nontrivial V := Module.finrank_pos_iff.mp hpos
  obtain ⟨v, hv, h | ⟨b, c, hbc, h⟩⟩ := exists_vec T
  · obtain ⟨l, hl⟩ := h
    set W : Submodule ℝ V := Submodule.span ℝ {v} with hWdef
    have hvW : v ∈ W := Submodule.mem_span_singleton_self v
    have hW : W ≤ W.comap T := by
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [Submodule.mem_comap, map_smul, hl, smul_smul]
      exact Submodule.smul_mem _ _ hvW
    have hmk : ∀ x, W.mkQ x = 0 ↔ x ∈ W := fun x => by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    set T' := W.mapQ W T hW with hT'def
    have hT' : ∀ x, T' (W.mkQ x) = W.mkQ (T x) := fun x => rfl
    have hfin : finrank ℝ (V ⧸ W) + finrank ℝ W = finrank ℝ V := Submodule.finrank_quotient_add_finrank W
    have hW1 : finrank ℝ W = 1 := finrank_span_singleton hv
    have hQpos : 0 < finrank ℝ (V ⧸ W) := by omega
    have hQ : Nontrivial (V ⧸ W) := Module.finrank_pos_iff.mp hQpos
    obtain ⟨ub, hub, h' | ⟨b, c, hbc, h'⟩⟩ := exists_vec T'
    all_goals obtain ⟨u, rfl⟩ := W.mkQ_surjective ub
    · obtain ⟨l', hl'⟩ := h'
      rw [hT', ← map_smul] at hl'
      have hmem : T u - l' • u ∈ W := by
        rw [← hmk, map_sub, hl', sub_self]
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      have hTu : T u = l' • u + a • v := by rw [ha]; abel
      have hli : LinearIndependent ℝ ![v, u] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congrArg W.mkQ hst
        rw [map_add, map_smul, map_smul, (hmk v).mpr hvW, smul_zero, zero_add, map_zero] at h1
        have ht : t = 0 := (smul_eq_zero.mp h1).resolve_right hub
        subst ht
        refine ⟨?_, rfl⟩
        simp only [zero_smul, add_zero] at hst
        exact (smul_eq_zero.mp hst).resolve_right hv
      refine ⟨Submodule.span ℝ (Set.range ![v, u]), ?_, ?_⟩
      · intro x hx
        obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
        refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
          ⟨![cf 0 * l + cf 1 * a, cf 1 * l'], ?_⟩
        simp only [Fin.sum_univ_two, map_add, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
          hl, hTu]
        module
      · rw [finrank_span_eq_card hli]
        simp
    · have hmem : T (T u) + b • T u + c • u ∈ W := by
        rw [← hmk]
        have e : W.mkQ (T (T u) + b • T u + c • u) =
            T' (T' (W.mkQ u)) + b • T' (W.mkQ u) + c • W.mkQ u := by
          simp only [map_add, map_smul, hT']
        rw [e]
        exact h'
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      have hqpos : 0 < l * l + b * l + c := by nlinarith [sq_nonneg (2 * l + b)]
      have hqne : l * l + b * l + c ≠ 0 := hqpos.ne'
      have hTv2 : T (T v) + b • T v + c • v = (l * l + b * l + c) • v := by
        rw [hl, map_smul, hl]; module
      have hu'0 : T (T (u - (a / (l * l + b * l + c)) • v)) + b • T (u - (a / (l * l + b * l + c)) • v)
          + c • (u - (a / (l * l + b * l + c)) • v) = 0 := by
        calc _ = (T (T u) + b • T u + c • u) -
              (a / (l * l + b * l + c)) • (T (T v) + b • T v + c • v) := by
              simp only [map_sub, map_smul]; module
          _ = 0 := by
              rw [← ha, hTv2, smul_smul, div_mul_cancel₀ _ hqne, sub_self]
      have hu'ne : u - (a / (l * l + b * l + c)) • v ≠ 0 := by
        intro h0
        have h1 := congrArg W.mkQ h0
        rw [map_sub, map_smul, (hmk v).mpr hvW, smul_zero, sub_zero, map_zero] at h1
        exact hub h1
      exact two_dim_of_quad T hu'ne hbc hu'0
  · exact two_dim_of_quad T hv hbc h

end TwoDim

end UndergradKB.LinearAlgebra
