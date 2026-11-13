import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import UndergradKB.Common.Attr
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import UndergradKB.RepresentationTheory.QWeylAlgebra

/-! # Problem 1.27 (c): irreducible representations of the `q`-Weyl algebra at a root of unity

Note: the repository's `QWeylAlgebra k q` has the relation `y x = q x y` (the book writes
`x y = q y x`), which replaces `q` by `q⁻¹` and does not affect the statements below.
-/

namespace UndergradKB.RepresentationTheory

open Module

section Dim

variable {k : Type*} [Field k] {q : kˣ} {V : Type*} [AddCommGroup V] [Module k V]

theorem qrel_Y_mul_X_pow {X Xi Y Yi : Module.End k V} (r : IsQWeylRel q X Xi Y Yi) (j : ℕ) :
    Y * X ^ j = (q : k) ^ j • (X ^ j * Y) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, r.yx, mul_smul_comm, ← mul_assoc,
      smul_smul, ← pow_succ]

/-- Schur-type lemma for four generators: an endomorphism commuting with `X` and `Y` is a scalar if
there is no proper nonzero subspace stable under `X, Xi, Y, Yi`. -/
theorem qrel_scalar [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    {X Xi Y Yi : Module.End k V} (r : IsQWeylRel q X Xi Y Yi)
    (hirr : ∀ W : Submodule k V, (∀ w ∈ W, X w ∈ W) → (∀ w ∈ W, Xi w ∈ W) →
      (∀ w ∈ W, Y w ∈ W) → (∀ w ∈ W, Yi w ∈ W) → W = ⊥ ∨ W = ⊤)
    (T : Module.End k V) (hX : T * X = X * T) (hY : T * Y = Y * T) :
    ∃ μ : k, T = μ • (1 : Module.End k V) := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  have hne : T.eigenspace μ ≠ ⊥ := hμ
  have hXi : T * Xi = Xi * T := by
    calc T * Xi = Xi * X * (T * Xi) := by rw [r.xix, one_mul]
      _ = Xi * (X * T) * Xi := by simp only [mul_assoc]
      _ = Xi * (T * X) * Xi := by rw [hX]
      _ = Xi * T * (X * Xi) := by simp only [mul_assoc]
      _ = Xi * T := by rw [r.xxi, mul_one]
  have hYi : T * Yi = Yi * T := by
    calc T * Yi = Yi * Y * (T * Yi) := by rw [r.yiy, one_mul]
      _ = Yi * (Y * T) * Yi := by simp only [mul_assoc]
      _ = Yi * (T * Y) * Yi := by rw [hY]
      _ = Yi * T * (Y * Yi) := by simp only [mul_assoc]
      _ = Yi * T := by rw [r.yyi, mul_one]
  have hinv : ∀ S : Module.End k V, T * S = S * T → ∀ w ∈ T.eigenspace μ, S w ∈ T.eigenspace μ := by
    intro S hS w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    have := congrArg (fun F => F w) hS
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_smul]
  have htop := (hirr _ (hinv X hX) (hinv Xi hXi) (hinv Y hY) (hinv Yi hYi)).resolve_left hne
  refine ⟨μ, LinearMap.ext fun w => ?_⟩
  have : w ∈ T.eigenspace μ := by rw [htop]; trivial
  simpa [Module.End.mem_eigenspace_iff] using this

/-- Abstract form of Problem 1.27(c): if `q` has order `m`, a finite-dimensional irreducible
representation (no proper nonzero subspace stable under `X, X⁻¹, Y, Y⁻¹`, with `Y X = q X Y`)
over an algebraically closed field has dimension `m`. -/
theorem qrel_finrank [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    {X Xi Y Yi : Module.End k V} (r : IsQWeylRel q X Xi Y Yi) {m : ℕ} (hm0 : 0 < m) (hm : orderOf q = m)
    (hirr : ∀ W : Submodule k V, (∀ w ∈ W, X w ∈ W) → (∀ w ∈ W, Xi w ∈ W) →
      (∀ w ∈ W, Y w ∈ W) → (∀ w ∈ W, Yi w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank k V = m := by
  have hqm : (q : k) ^ m = 1 := by
    have : q ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one q
    simpa using congrArg Units.val this
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue Y
  obtain ⟨v, hv⟩ := hβ.exists_hasEigenvector
  have hYv : Y v = β • v := Module.End.mem_eigenspace_iff.1 hv.1
  have hv0 : v ≠ 0 := hv.2
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hv0
    have := congrArg Yi hYv
    rw [h0, zero_smul, map_zero] at this
    have h2 := congrArg (fun F => F v) r.yiy
    simp only [Module.End.mul_apply, Module.End.one_apply] at h2
    rw [← h2, hYv, h0, zero_smul, map_zero]
  have hXinj : Function.Injective X := fun a b h => by
    have := congrArg Xi h
    have h2 := fun w => congrArg (fun F => F w) r.xix
    simp only [Module.End.mul_apply, Module.End.one_apply] at h2
    rwa [h2, h2] at this
  have hXpow_ne : ∀ j : ℕ, (X ^ j) v ≠ 0 := by
    intro j
    induction j with
    | zero => simpa using hv0
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      intro h
      exact ih (hXinj (by rw [h, map_zero]))
  have hYX : ∀ j : ℕ, Y ((X ^ j) v) = ((q : k) ^ j * β) • (X ^ j) v := by
    intro j
    have h := congrArg (fun F => F v) (qrel_Y_mul_X_pow r j)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hYv, map_smul] at h
    rw [h, smul_smul]
  -- lower bound
  have hge : m ≤ Module.finrank k V := by
    have hli : LinearIndependent k (fun j : Fin m => (X ^ (j : ℕ)) v) := by
      refine Module.End.eigenvectors_linearIndependent' Y (fun j : Fin m => (q : k) ^ (j : ℕ) * β)
        ?_ _ fun j => ⟨Module.End.mem_eigenspace_iff.2 (hYX j), hXpow_ne j⟩
      intro i j hij
      have h1 : (q : k) ^ (i : ℕ) = (q : k) ^ (j : ℕ) := mul_right_cancel₀ hβ0 hij
      have h2 : q ^ (i : ℕ) = q ^ (j : ℕ) := Units.ext (by simpa using h1)
      exact Fin.ext (pow_injOn_Iio_orderOf (x := q) (by simpa [hm] using i.2)
        (by simpa [hm] using j.2) h2)
    simpa using hli.fintype_card_le_finrank
  -- `X^m` is a scalar
  obtain ⟨c, hc⟩ := qrel_scalar r hirr (X ^ m) (Commute.self_pow X m).eq.symm (by
    have := qrel_Y_mul_X_pow r m
    rw [hqm, one_smul] at this
    exact this.symm)
  have hXm : (X ^ m) v = c • v := by rw [hc]; simp
  have hc0 : c ≠ 0 := by
    intro h0
    apply hXpow_ne m
    rw [hXm, h0, zero_smul]
  set W : Submodule k V := Submodule.span k (Set.range fun j : Fin m => (X ^ (j : ℕ)) v) with hW
  have hmemW : ∀ j : ℕ, (X ^ j) v ∈ W := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < m
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · have e : (X ^ j) v = c • (X ^ (j - m)) v := by
          conv_lhs => rw [show j = (j - m) + m by omega, pow_add, Module.End.mul_apply, hXm,
            map_smul]
        rw [e]
        exact W.smul_mem _ (ih _ (by omega))
  have hXW : ∀ w ∈ W, X w ∈ W := by
    have : W ≤ W.comap X := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show X ((X ^ (j : ℕ)) v) ∈ W
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hmemW _
    exact fun w hw => this hw
  have hXiX : ∀ w, Xi (X w) = w := fun w => by
    have := congrArg (fun F => F w) r.xix
    simpa using this
  have hXiW : ∀ w ∈ W, Xi w ∈ W := by
    have : W ≤ W.comap Xi := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Xi ((X ^ (j : ℕ)) v) ∈ W
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · rw [h0, pow_zero, Module.End.one_apply]
        have h3 : (X ^ (m - 1)) v = c • Xi v := by
          have h5 : X ((X ^ (m - 1)) v) = c • v := by
            rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hm0, hXm]
          have := congrArg Xi h5
          rwa [hXiX, map_smul] at this
        have : Xi v = c⁻¹ • (X ^ (m - 1)) v := by
          rw [h3, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this]
        exact W.smul_mem _ (hmemW _)
      · have : (X ^ (j : ℕ)) v = X ((X ^ ((j : ℕ) - 1)) v) := by
          rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel h0]
        rw [this, hXiX]
        exact hmemW _
    exact fun w hw => this hw
  have hYW : ∀ w ∈ W, Y w ∈ W := by
    have : W ≤ W.comap Y := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Y ((X ^ (j : ℕ)) v) ∈ W
      rw [hYX]
      exact W.smul_mem _ (hmemW _)
    exact fun w hw => this hw
  have hYiW : ∀ w ∈ W, Yi w ∈ W := by
    have : W ≤ W.comap Yi := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Yi ((X ^ (j : ℕ)) v) ∈ W
      have hμ0 : (q : k) ^ (j : ℕ) * β ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (Units.ne_zero q)) hβ0
      have h1 := congrArg Yi (hYX j)
      have h2 := fun w => congrArg (fun F => F w) r.yiy
      simp only [Module.End.mul_apply, Module.End.one_apply] at h2
      rw [h2, map_smul] at h1
      have : Yi ((X ^ (j : ℕ)) v) = ((q : k) ^ (j : ℕ) * β)⁻¹ • (X ^ (j : ℕ)) v := by
        exact (eq_inv_smul_iff₀ hμ0).2 h1.symm
      rw [this]
      exact W.smul_mem _ (hmemW _)
    exact fun w hw => this hw
  have hWtop : W = ⊤ := by
    refine (hirr W hXW hXiW hYW hYiW).resolve_left fun h => hv0 ?_
    have := hmemW 0
    rw [h] at this
    simpa using this
  have hle : Module.finrank k V ≤ m := by
    have := finrank_range_le_card (R := k) (fun j : Fin m => (X ^ (j : ℕ)) v)
    unfold Set.finrank at this
    rw [← hW, hWtop, finrank_top] at this
    simpa using this
  exact le_antisymm hle hge

end Dim

section Alg

variable {k : Type*} [Field k] {q : kˣ} {V : Type*} [AddCommGroup V] [Module k V]

/-- The images of the generators in a representation satisfy the `q`-Weyl relations. -/
theorem isQWeylRel_rep (ρ : QWeylAlgebra k q →ₐ[k] Module.End k V) :
    IsQWeylRel q (ρ (qWeylX k q)) (ρ (qWeylXinv k q)) (ρ (qWeylY k q)) (ρ (qWeylYinv k q)) where
  xxi := by rw [← map_mul, qWeylX_mul_qWeylXinv, map_one]
  xix := by rw [← map_mul, qWeylXinv_mul_qWeylX, map_one]
  yyi := by rw [← map_mul, qWeylY_mul_qWeylYinv, map_one]
  yiy := by rw [← map_mul, qWeylYinv_mul_qWeylY, map_one]
  yx := by rw [← map_mul, ← map_mul, ← map_smul, qWeylY_mul_qWeylX]

/-- A subspace stable under the four generators is stable under the whole `q`-Weyl algebra. -/
theorem qweyl_stable_all (ρ : QWeylAlgebra k q →ₐ[k] Module.End k V) (W : Submodule k V)
    (hX : ∀ w ∈ W, ρ (qWeylX k q) w ∈ W) (hXi : ∀ w ∈ W, ρ (qWeylXinv k q) w ∈ W)
    (hY : ∀ w ∈ W, ρ (qWeylY k q) w ∈ W) (hYi : ∀ w ∈ W, ρ (qWeylYinv k q) w ∈ W) :
    ∀ z : QWeylAlgebra k q, ∀ w ∈ W, ρ z w ∈ W := by
  intro z
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (QWeylRel k q) z
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    intro w hw
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    simpa using W.smul_mem r hw
  | grade1 i =>
    intro w hw
    fin_cases i
    · exact hX w hw
    · exact hXi w hw
    · exact hY w hw
    · exact hYi w hw
  | mul a b ha hb =>
    intro w hw
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact ha _ (hb w hw)
  | add a b ha hb =>
    intro w hw
    rw [map_add, map_add, LinearMap.add_apply]
    exact W.add_mem (ha w hw) (hb w hw)

/-- Problem 1.27(c): if `q` is a primitive `m`-th root of unity (`orderOf q = m`) and `k` is
algebraically closed, every finite-dimensional irreducible representation of the `q`-Weyl algebra
has dimension `m`.  (The repository's relation is `y x = q x y`, the book's with `q ↦ q⁻¹`.) -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_irrep_finrank [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] {m : ℕ}
    (hm0 : 0 < m) (hm : orderOf q = m) (ρ : QWeylAlgebra k q →ₐ[k] Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ z : QWeylAlgebra k q, ∀ w ∈ W, ρ z w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank k V = m :=
  qrel_finrank (isQWeylRel_rep ρ) hm0 hm fun W hX hXi hY hYi =>
    hirr W (qweyl_stable_all ρ W hX hXi hY hYi)

end Alg

section Center

variable {k : Type*} [Field k] {q : kˣ}

local notation "QA" => QWeylAlgebra k q

/-- Conjugation by `x`. -/
noncomputable def qConjX : QA →ₗ[k] QA :=
  (LinearMap.mulLeft k (qWeylX k q)).comp (LinearMap.mulRight k (qWeylXinv k q))

/-- Conjugation by `y`. -/
noncomputable def qConjY : QA →ₗ[k] QA :=
  (LinearMap.mulLeft k (qWeylY k q)).comp (LinearMap.mulRight k (qWeylYinv k q))

theorem qConjX_apply (z : QA) : qConjX z = qWeylX k q * z * qWeylXinv k q := by
  simp [qConjX, mul_assoc]

theorem qConjY_apply (z : QA) : qConjY z = qWeylY k q * z * qWeylYinv k q := by
  simp [qConjY, mul_assoc]

theorem qConjX_mon (i j : ℤ) :
    qConjX (qWeylMon k q i j) = (((q⁻¹ ^ j : kˣ)) : k) • qWeylMon k q i j := by
  have hrel := qmon_unit_rel (k := k) (q := q) (X := qWeylXUnit) (Y := qWeylYUnit)
    qWeylYUnit_mul_qWeylXUnit
  set c := scalarUnit k (A := QA) q with hc
  have hcx : Commute c⁻¹ (qWeylYUnit : (QA)ˣ) := (commute_scalarUnit (A := QA) (k := k) q _).inv_left
  have h2 : (qWeylXUnit : (QA)ˣ) * qWeylYUnit = c⁻¹ * (qWeylYUnit * qWeylXUnit) := by
    rw [hrel]; group
  have h3 := zpow_comm_rule hcx h2 j
  have key : (qWeylXUnit : (QA)ˣ) * (qWeylXUnit ^ i * qWeylYUnit ^ j) * qWeylXUnit⁻¹ =
      scalarUnit k (q⁻¹ ^ j) * (qWeylXUnit ^ i * qWeylYUnit ^ j) := by
    have e1 : (qWeylXUnit : (QA)ˣ) * qWeylXUnit ^ i = qWeylXUnit ^ i * qWeylXUnit :=
      (Commute.self_zpow _ _).eq
    have hs : c⁻¹ ^ j = scalarUnit k (q⁻¹ ^ j) := by
      rw [hc, scalarUnit_inv, scalarUnit_zpow]
    calc (qWeylXUnit : (QA)ˣ) * (qWeylXUnit ^ i * qWeylYUnit ^ j) * qWeylXUnit⁻¹
        = qWeylXUnit ^ i * (qWeylXUnit * qWeylYUnit ^ j) * qWeylXUnit⁻¹ := by
          rw [← mul_assoc (qWeylXUnit : (QA)ˣ), e1]; simp only [mul_assoc]
      _ = qWeylXUnit ^ i * (scalarUnit k (q⁻¹ ^ j) * (qWeylYUnit ^ j * qWeylXUnit)) *
            qWeylXUnit⁻¹ := by rw [h3, hs]
      _ = qWeylXUnit ^ i * scalarUnit k (q⁻¹ ^ j) * qWeylYUnit ^ j *
            (qWeylXUnit * qWeylXUnit⁻¹) := by group
      _ = scalarUnit k (q⁻¹ ^ j) * (qWeylXUnit ^ i * qWeylYUnit ^ j) := by
          rw [mul_inv_cancel, mul_one, ← (commute_scalarUnit (A := QA) (k := k) (q⁻¹ ^ j) _).eq,
            mul_assoc]
  have := congrArg (fun u : (QA)ˣ => (u : QA)) key
  rw [qConjX_apply]
  have e1' : (qWeylX k q) = ((qWeylXUnit : (QA)ˣ) : QA) := rfl
  have e2' : (qWeylXinv k q) = (((qWeylXUnit : (QA)ˣ)⁻¹ : (QA)ˣ) : QA) := rfl
  rw [e1', e2']
  unfold qWeylMon
  simp only [Units.val_mul] at this ⊢
  rw [this, Algebra.smul_def]
  congr 1

theorem qConjY_mon (i j : ℤ) :
    qConjY (qWeylMon k q i j) = (((q ^ i : kˣ)) : k) • qWeylMon k q i j := by
  have hrel := qmon_unit_rel (k := k) (q := q) (X := qWeylXUnit) (Y := qWeylYUnit)
    qWeylYUnit_mul_qWeylXUnit
  set c := scalarUnit k (A := QA) q with hc
  have h1 := zpow_comm_rule (commute_scalarUnit (A := QA) (k := k) q (qWeylXUnit : (QA)ˣ)) hrel i
  have key : (qWeylYUnit : (QA)ˣ) * (qWeylXUnit ^ i * qWeylYUnit ^ j) * qWeylYUnit⁻¹ =
      scalarUnit k (q ^ i) * (qWeylXUnit ^ i * qWeylYUnit ^ j) := by
    have hs : c ^ i = scalarUnit k (q ^ i) := by rw [hc, scalarUnit_zpow]
    calc (qWeylYUnit : (QA)ˣ) * (qWeylXUnit ^ i * qWeylYUnit ^ j) * qWeylYUnit⁻¹
        = (qWeylYUnit * qWeylXUnit ^ i) * qWeylYUnit ^ j * qWeylYUnit⁻¹ := by
          simp only [mul_assoc]
      _ = scalarUnit k (q ^ i) * (qWeylXUnit ^ i * qWeylYUnit) * qWeylYUnit ^ j *
            qWeylYUnit⁻¹ := by rw [h1, hs]
      _ = scalarUnit k (q ^ i) * (qWeylXUnit ^ i * qWeylYUnit ^ j) := by group
  have := congrArg (fun u : (QA)ˣ => (u : QA)) key
  rw [qConjY_apply]
  have e1' : (qWeylY k q) = ((qWeylYUnit : (QA)ˣ) : QA) := rfl
  have e2' : (qWeylYinv k q) = (((qWeylYUnit : (QA)ˣ)⁻¹ : (QA)ˣ) : QA) := rfl
  rw [e1', e2']
  unfold qWeylMon
  simp only [Units.val_mul] at this ⊢
  rw [this, Algebra.smul_def]
  congr 1

theorem repr_diag {ι M : Type*} [AddCommGroup M] [Module k M] (b : Module.Basis ι k M)
    (T : M →ₗ[k] M) (lam : ι → k) (hT : ∀ r, T (b r) = lam r • b r) (z : M) (p : ι) :
    b.repr (T z) p = lam p * b.repr z p := by
  have : (Finsupp.lapply p ∘ₗ b.repr.toLinearMap ∘ₗ T) =
      lam p • (Finsupp.lapply p ∘ₗ b.repr.toLinearMap) := by
    refine b.ext fun r => ?_
    simp only [LinearMap.comp_apply, hT, LinearEquiv.coe_coe, map_smul, Module.Basis.repr_self,
      Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul]
    by_cases h : r = p
    · subst h; simp
    · simp [h, Ne.symm h]
  exact congrArg (fun f => f z) this

theorem finOrder_of_zpow_eq_one {j : ℤ} (hj : j ≠ 0) (h : q ^ j = 1) : IsOfFinOrder q := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨j.natAbs, Int.natAbs_pos.2 hj, ?_⟩
  rcases Int.natAbs_eq j with e | e
  · rw [e, zpow_natCast] at h; exact h
  · rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h; exact h

theorem qweyl_central_repr_y {z : QA} (hz : z ∈ Subalgebra.center k QA) (i j : ℤ)
    (h : (q ^ j : kˣ) ≠ 1) : qWeylBasis.repr z (i, j) = 0 := by
  rw [Subalgebra.mem_center_iff] at hz
  have hxz : qConjX z = z := by
    rw [qConjX_apply, hz (qWeylX k q), mul_assoc, qWeylX_mul_qWeylXinv, mul_one]
  have := repr_diag (qWeylBasis (k := k) (q := q)) qConjX (fun p => (((q⁻¹ ^ p.2 : kˣ)) : k))
    (fun r => by rw [qWeylBasis_apply]; exact qConjX_mon r.1 r.2) z (i, j)
  rw [hxz] at this
  have hne : (((q⁻¹ ^ j : kˣ)) : k) ≠ 1 := by
    intro h1
    apply h
    have : q⁻¹ ^ j = 1 := Units.ext h1
    rw [inv_zpow'] at this
    simpa using this
  have h2 : (1 - (((q⁻¹ ^ j : kˣ)) : k)) * qWeylBasis.repr z (i, j) = 0 := by
    simp only at this
    linear_combination this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne.symm)

theorem qweyl_central_repr_x {z : QA} (hz : z ∈ Subalgebra.center k QA) (i j : ℤ)
    (h : (q ^ i : kˣ) ≠ 1) : qWeylBasis.repr z (i, j) = 0 := by
  rw [Subalgebra.mem_center_iff] at hz
  have hyz : qConjY z = z := by
    rw [qConjY_apply, hz (qWeylY k q), mul_assoc, qWeylY_mul_qWeylYinv, mul_one]
  have := repr_diag (qWeylBasis (k := k) (q := q)) qConjY (fun p => (((q ^ p.1 : kˣ)) : k))
    (fun r => by rw [qWeylBasis_apply]; exact qConjY_mon r.1 r.2) z (i, j)
  rw [hyz] at this
  have hne : (((q ^ i : kˣ)) : k) ≠ 1 := fun h1 => h (Units.ext h1)
  have h2 : (1 - (((q ^ i : kˣ)) : k)) * qWeylBasis.repr z (i, j) = 0 := by
    simp only at this
    linear_combination this
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne.symm)

theorem qWeylBasis_zero : qWeylBasis (k := k) (q := q) (0, 0) = 1 := by
  simp [qWeylBasis_apply, qWeylMon]

/-- Problem 1.27(a), non-root-of-unity case: the centre of the `q`-Weyl algebra is the scalars. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_center_eq_bot (hq : ¬ IsOfFinOrder q) :
    Subalgebra.center k QA = ⊥ := by
  refine le_antisymm (fun z hz => ?_) bot_le
  have hcoef : ∀ i j : ℤ, (i, j) ≠ ((0 : ℤ), (0 : ℤ)) → qWeylBasis.repr z (i, j) = 0 := by
    intro i j hij
    by_cases hj : j = 0
    · have hi : i ≠ 0 := fun h => hij (by rw [h, hj])
      exact qweyl_central_repr_x hz i j fun h => hq (finOrder_of_zpow_eq_one hi h)
    · exact qweyl_central_repr_y hz i j fun h => hq (finOrder_of_zpow_eq_one hj h)
  have hz' : z = qWeylBasis.repr z (0, 0) • (1 : QA) := by
    apply qWeylBasis.repr.injective
    ext ⟨i, j⟩
    rw [map_smul, ← qWeylBasis_zero, Module.Basis.repr_self]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hij : (i, j) = ((0 : ℤ), (0 : ℤ))
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
      simp
    · rw [hcoef i j hij, if_neg (fun h => hij (by rw [h.1.symm, h.2.symm])), mul_zero]
  rw [hz', Algebra.mem_bot]
  exact ⟨_, by rw [Algebra.algebraMap_eq_smul_one]⟩

theorem qweyl_central_repr_dvd {m : ℕ} (hm : orderOf q = m) {z : QA}
    (hz : z ∈ Subalgebra.center k QA) (i j : ℤ) (h : qWeylBasis.repr z (i, j) ≠ 0) :
    (m : ℤ) ∣ i ∧ (m : ℤ) ∣ j := by
  constructor
  · by_contra hi
    refine h (qweyl_central_repr_x hz i j fun h1 => hi ?_)
    rw [← hm]; exact orderOf_dvd_iff_zpow_eq_one.2 h1
  · by_contra hj
    refine h (qweyl_central_repr_y hz i j fun h1 => hj ?_)
    rw [← hm]; exact orderOf_dvd_iff_zpow_eq_one.2 h1

theorem unit_zpow_mem {S : Subalgebra k QA} (U : (QA)ˣ) (h1 : (U : QA) ∈ S)
    (h2 : ((U⁻¹ : (QA)ˣ) : QA) ∈ S) (a : ℤ) : ((U ^ a : (QA)ˣ) : QA) ∈ S := by
  rcases a with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    exact S.pow_mem h1 n
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    exact S.pow_mem h2 _

theorem central_of_unit_commute (U : (QA)ˣ) (hX : Commute U (qWeylXUnit : (QA)ˣ))
    (hY : Commute U (qWeylYUnit : (QA)ˣ)) :
    (U : QA) ∈ Subalgebra.center k QA ∧ ((U⁻¹ : (QA)ˣ) : QA) ∈ Subalgebra.center k QA := by
  have key : ∀ W : (QA)ˣ, Commute W (qWeylXUnit : (QA)ˣ) → Commute W (qWeylYUnit : (QA)ˣ) →
      (W : QA) ∈ Subalgebra.center k QA := by
    intro W hWX hWY
    rw [Subalgebra.mem_center_iff]
    intro b
    have hb : b ∈ Submodule.span k (Set.range fun p : ℤ × ℤ => qWeylMon k q p.1 p.2) := by
      rw [qWeyl_span]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hb
      have : Commute (qWeylXUnit ^ i * qWeylYUnit ^ j : (QA)ˣ) W :=
        (hWX.symm.zpow_left i).mul_left (hWY.symm.zpow_left j)
      exact (Commute.units_val this).eq
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul, mul_add, ha, hb]
    | smul r a _ ha => rw [smul_mul_assoc, mul_smul_comm, ha]
  exact ⟨key U hX hY, key U⁻¹ hX.inv_left hY.inv_left⟩

/-- Problem 1.27(a), root-of-unity case: if `q` has order `m`, the centre of the `q`-Weyl algebra
is generated by `x^{±m}` and `y^{±m}`. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_center_eq_adjoin {m : ℕ} (hm0 : 0 < m) (hm : orderOf q = m) :
    Subalgebra.center k QA = Algebra.adjoin k
      {qWeylX k q ^ m, qWeylXinv k q ^ m, qWeylY k q ^ m, qWeylYinv k q ^ m} := by
  have hqm : q ^ (m : ℤ) = 1 := by
    rw [zpow_natCast, ← hm]; exact pow_orderOf_eq_one q
  have hrel := qmon_unit_rel (k := k) (q := q) (X := qWeylXUnit) (Y := qWeylYUnit)
    qWeylYUnit_mul_qWeylXUnit
  set c := scalarUnit k (A := QA) q with hc
  have hcm : c ^ (m : ℤ) = 1 := by rw [hc, scalarUnit_zpow, hqm]; simp [scalarUnit]
  -- the units `x^m` and `y^m` commute with `x` and `y`
  have hUX : Commute (qWeylXUnit ^ (m : ℤ) : (QA)ˣ) qWeylXUnit := (Commute.self_zpow _ _).symm
  have hUY : Commute (qWeylXUnit ^ (m : ℤ) : (QA)ˣ) qWeylYUnit := by
    have h1 := zpow_comm_rule (commute_scalarUnit (A := QA) (k := k) q (qWeylXUnit : (QA)ˣ))
      hrel (m : ℤ)
    rw [← hc, hcm, one_mul] at h1
    exact h1.symm
  have hVX : Commute (qWeylYUnit ^ (m : ℤ) : (QA)ˣ) qWeylXUnit := by
    have hcx : Commute c⁻¹ (qWeylYUnit : (QA)ˣ) :=
      (commute_scalarUnit (A := QA) (k := k) q _).inv_left
    have h2 : (qWeylXUnit : (QA)ˣ) * qWeylYUnit = c⁻¹ * (qWeylYUnit * qWeylXUnit) := by
      rw [hrel]; group
    have h3 := zpow_comm_rule hcx h2 (m : ℤ)
    rw [inv_zpow, hcm, inv_one, one_mul] at h3
    exact h3.symm
  have hVY : Commute (qWeylYUnit ^ (m : ℤ) : (QA)ˣ) qWeylYUnit := (Commute.self_zpow _ _).symm
  obtain ⟨hU1, hU2⟩ := central_of_unit_commute (k := k) _ hUX hUY
  obtain ⟨hV1, hV2⟩ := central_of_unit_commute (k := k) _ hVX hVY
  have eX : ((qWeylXUnit ^ (m : ℤ) : (QA)ˣ) : QA) = qWeylX k q ^ m := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  have eXi : (((qWeylXUnit ^ (m : ℤ) : (QA)ˣ)⁻¹ : (QA)ˣ) : QA) = qWeylXinv k q ^ m := by
    rw [zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]; rfl
  have eY : ((qWeylYUnit ^ (m : ℤ) : (QA)ˣ) : QA) = qWeylY k q ^ m := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  have eYi : (((qWeylYUnit ^ (m : ℤ) : (QA)ˣ)⁻¹ : (QA)ˣ) : QA) = qWeylYinv k q ^ m := by
    rw [zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]; rfl
  rw [eX] at hU1
  rw [eXi] at hU2
  rw [eY] at hV1
  rw [eYi] at hV2
  apply le_antisymm
  · intro z hz
    have hsum := (qWeylBasis (k := k) (q := q)).linearCombination_repr z
    rw [← hsum, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Subalgebra.sum_mem _ fun p hp => ?_
    refine Subalgebra.smul_mem _ ?_ _
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := qweyl_central_repr_dvd hm hz p.1 p.2
      (Finsupp.mem_support_iff.1 hp)
    rw [qWeylBasis_apply]
    unfold qWeylMon
    rw [ha, hb, zpow_mul, zpow_mul, Units.val_mul]
    refine Subalgebra.mul_mem _ (unit_zpow_mem _ ?_ ?_ a) (unit_zpow_mem _ ?_ ?_ b)
    · rw [eX]; exact Algebra.subset_adjoin (by simp)
    · rw [eXi]; exact Algebra.subset_adjoin (by simp)
    · rw [eY]; exact Algebra.subset_adjoin (by simp)
    · rw [eYi]; exact Algebra.subset_adjoin (by simp)
  · refine Algebra.adjoin_le ?_
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hU1
    · exact hU2
    · exact hV1
    · exact hV2

end Center

section Simple

variable {k : Type*} [Field k] {q : kˣ}

local notation "QA" => QWeylAlgebra k q

theorem zpow_ne_of_not_finOrder (hq : ¬ IsOfFinOrder q) {a b : ℤ} (hab : a ≠ b) :
    q ^ a ≠ q ^ b := fun h =>
  hq (finOrder_of_zpow_eq_one (sub_ne_zero.2 hab) (by rw [zpow_sub, h, mul_inv_cancel]))

theorem qConjX_sub_mem (I : TwoSidedIdeal QA) (α : k) {z : QA} (hz : z ∈ I) :
    qConjX z - α • z ∈ I := by
  refine I.sub_mem ?_ ?_
  · rw [qConjX_apply]; exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hz)
  · rw [Algebra.smul_def]; exact I.mul_mem_left _ _ hz

theorem qConjY_sub_mem (I : TwoSidedIdeal QA) (α : k) {z : QA} (hz : z ∈ I) :
    qConjY z - α • z ∈ I := by
  refine I.sub_mem ?_ ?_
  · rw [qConjY_apply]; exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hz)
  · rw [Algebra.smul_def]; exact I.mul_mem_left _ _ hz

theorem repr_conjX_sub (α : k) (z : QA) (p : ℤ × ℤ) :
    qWeylBasis.repr (qConjX z - α • z) p =
      ((((q⁻¹ ^ p.2 : kˣ)) : k) - α) * qWeylBasis.repr z p := by
  have := repr_diag (qWeylBasis (k := k) (q := q)) qConjX (fun p => (((q⁻¹ ^ p.2 : kˣ)) : k))
    (fun r => by rw [qWeylBasis_apply]; exact qConjX_mon r.1 r.2) z p
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, this]
  simp only [smul_eq_mul]; ring

theorem repr_conjY_sub (α : k) (z : QA) (p : ℤ × ℤ) :
    qWeylBasis.repr (qConjY z - α • z) p =
      ((((q ^ p.1 : kˣ)) : k) - α) * qWeylBasis.repr z p := by
  have := repr_diag (qWeylBasis (k := k) (q := q)) qConjY (fun p => (((q ^ p.1 : kˣ)) : k))
    (fun r => by rw [qWeylBasis_apply]; exact qConjY_mon r.1 r.2) z p
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, this]
  simp only [smul_eq_mul]; ring

/-- Problem 1.27(a), non-root-of-unity case: every nonzero two-sided ideal of the `q`-Weyl algebra
is the whole algebra. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_ideal_eq_top (hq : ¬ IsOfFinOrder q) (I : TwoSidedIdeal QA) (h : I ≠ ⊥) : I = ⊤ := by
  classical
  obtain ⟨z0, hz0I, hz00⟩ : ∃ z ∈ I, z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (le_bot_iff.1 fun z hz => (TwoSidedIdeal.mem_bot _).2 (hcon z hz))
  have key : ∀ n : ℕ, ∀ z ∈ I, (qWeylBasis.repr z).support.card = n → z ≠ 0 → (1 : QA) ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hzI hcard hz0
      have hne : (qWeylBasis.repr z).support.Nonempty := by
        apply Finsupp.support_nonempty_iff.2
        intro h0
        exact hz0 (qWeylBasis.repr.injective (by simpa using h0))
      by_cases h1 : (qWeylBasis.repr z).support.card = 1
      · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
        have hpz : qWeylBasis.repr z p ≠ 0 := Finsupp.mem_support_iff.1 (by rw [hp]; simp)
        have hrepr : qWeylBasis.repr z = Finsupp.single p (qWeylBasis.repr z p) :=
          Finsupp.eq_single_iff.2 ⟨by rw [hp], rfl⟩
        have hzp : z = qWeylBasis.repr z p • qWeylBasis (k := k) (q := q) p := by
          apply qWeylBasis.repr.injective
          rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
          exact hrepr
        generalize qWeylBasis.repr z p = c at hzp hpz
        let U : (QA)ˣ := qWeylXUnit ^ p.1 * qWeylYUnit ^ p.2
        have hU : qWeylBasis (k := k) (q := q) p = (U : QA) := by
          rw [qWeylBasis_apply]; rfl
        have h2 : ((U⁻¹ : (QA)ˣ) : QA) * z = c • (1 : QA) := by
          rw [hzp, hU, mul_smul_comm, Units.inv_mul]
        have h3 : (c • (1 : QA)) ∈ I := h2 ▸ I.mul_mem_left _ _ hzI
        have h4 := I.mul_mem_left (algebraMap k QA c⁻¹) _ h3
        rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hpz, one_smul] at h4
        exact h4
      · have hlt : 1 < (qWeylBasis.repr z).support.card := by
          have := hne.card_pos; omega
        obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.1 hlt
        have step : ∀ z' ∈ I, (∀ r, qWeylBasis.repr z' r ≠ 0 → qWeylBasis.repr z r ≠ 0) →
            qWeylBasis.repr z' p = 0 → qWeylBasis.repr z' p' ≠ 0 → (1 : QA) ∈ I := by
          intro z' hz'I hsub hp0 hp'0
          have hz'0 : z' ≠ 0 := fun h0 => hp'0 (by rw [h0]; simp)
          refine ih _ ?_ z' hz'I rfl hz'0
          rw [← hcard]
          refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨p, hp, ?_⟩)
          · intro r hr
            exact Finsupp.mem_support_iff.2 (hsub r (Finsupp.mem_support_iff.1 hr))
          · simpa using hp0
        have hpz : qWeylBasis.repr z p ≠ 0 := Finsupp.mem_support_iff.1 hp
        have hp'z : qWeylBasis.repr z p' ≠ 0 := Finsupp.mem_support_iff.1 hp'
        by_cases hj : p.2 = p'.2
        · have hi : p.1 ≠ p'.1 := fun h => hpp (Prod.ext h hj)
          have hne' : (((q ^ p'.1 : kˣ)) : k) - (((q ^ p.1 : kˣ)) : k) ≠ 0 := by
            rw [sub_ne_zero]
            exact fun h => zpow_ne_of_not_finOrder hq (Ne.symm hi) (Units.ext h)
          refine step _ (qConjY_sub_mem I (((q ^ p.1 : kˣ)) : k) hzI) ?_ ?_ ?_
          · intro r hr
            rw [repr_conjY_sub] at hr
            exact right_ne_zero_of_mul hr
          · rw [repr_conjY_sub]; simp
          · rw [repr_conjY_sub]; exact mul_ne_zero hne' hp'z
        · have hne' : (((q⁻¹ ^ p'.2 : kˣ)) : k) - (((q⁻¹ ^ p.2 : kˣ)) : k) ≠ 0 := by
            rw [sub_ne_zero]
            intro h
            have h' : q⁻¹ ^ p'.2 = q⁻¹ ^ p.2 := Units.ext h
            rw [inv_zpow', inv_zpow'] at h'
            exact zpow_ne_of_not_finOrder hq (by omega) h'
          refine step _ (qConjX_sub_mem I (((q⁻¹ ^ p.2 : kˣ)) : k) hzI) ?_ ?_ ?_
          · intro r hr
            rw [repr_conjX_sub] at hr
            exact right_ne_zero_of_mul hr
          · rw [repr_conjX_sub]; simp
          · rw [repr_conjX_sub]; exact mul_ne_zero hne' hp'z
  exact eq_top_iff.2 fun a _ => by
    have := key _ z0 hz0I rfl hz00
    simpa using I.mul_mem_left a _ this

/-- Problem 1.27(a): for `q` not a root of unity, the `q`-Weyl algebra is a simple ring. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_isSimpleRing (hq : ¬ IsOfFinOrder q) : IsSimpleRing QA := by
  haveI : Nontrivial QA := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg (fun a => qWeylBasis.repr a (0, 0)) h
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [← qWeylBasis_zero, Module.Basis.repr_self] at h2
    simp at h2
  classical
  exact IsSimpleRing.of_eq_bot_or_eq_top fun I =>
    if hI : I = ⊥ then Or.inl hI else Or.inr (qweyl_ideal_eq_top hq I hI)

end Simple

end UndergradKB.RepresentationTheory
