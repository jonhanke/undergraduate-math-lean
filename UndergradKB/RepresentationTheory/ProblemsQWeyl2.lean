import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.QWeylAlgebra
import UndergradKB.RepresentationTheory.ProblemsQWeyl

/-! # Problem 1.27 (c): explicit models of the irreducible representations at a root of unity

For `q` of order `m`, nonzero `a, b ∈ k`, the space `k^m` (basis `g₀, …, g_{m-1}`) carries the
representation `x gₙ = gₙ₊₁` (and `x g_{m-1} = a g₀`), `y gₙ = b qⁿ gₙ`.  It is irreducible; over an
algebraically closed field every finite-dimensional irreducible representation is isomorphic to one
of these; two of them are isomorphic iff they have the same `(a, bᵐ)`.

(The repository's `q`-Weyl relation is `y x = q x y`, the book's with `q ↦ q⁻¹`.)
-/

namespace UndergradKB.RepresentationTheory

open Module

section Model

variable {k : Type*} [Field k] {q : kˣ} {m : ℕ}

/-- The `n`-th standard basis vector of `k^m` (zero if `n ≥ m`). -/
noncomputable def qg (k : Type*) [Field k] (m n : ℕ) : Fin m → k :=
  if h : n < m then Pi.single ⟨n, h⟩ (1 : k) else 0

/-- The endomorphism of `k^m` sending `g_n` to `v n` for `n < m`. -/
noncomputable def qmk (v : ℕ → (Fin m → k)) : Module.End k (Fin m → k) :=
  (Pi.basisFun k (Fin m)).constr k (fun i => v i)

theorem qmk_g (v : ℕ → (Fin m → k)) (n : ℕ) (h : n < m) : qmk v (qg k m n) = v n := by
  have : qg k m n = Pi.basisFun k (Fin m) ⟨n, h⟩ := by simp [qg, h]
  rw [this, qmk, Module.Basis.constr_basis]

theorem qmk_ext {F G : Module.End k (Fin m → k)} (h : ∀ n < m, F (qg k m n) = G (qg k m n)) :
    F = G := by
  refine (Pi.basisFun k (Fin m)).ext fun i => ?_
  have := h i i.2
  simpa [qg] using this

/-- `x`: the weighted cyclic shift with `x^m = a`. -/
noncomputable def qX (a : k) : Module.End k (Fin m → k) :=
  qmk fun n => if n + 1 < m then qg k m (n + 1) else a • qg k m 0

/-- `x⁻¹`. -/
noncomputable def qXi (a : k) : Module.End k (Fin m → k) :=
  qmk fun n => if n = 0 then a⁻¹ • qg k m (m - 1) else qg k m (n - 1)

/-- `y`: diagonal with entries `b qⁿ`. -/
noncomputable def qY (q : kˣ) (b : k) : Module.End k (Fin m → k) :=
  qmk fun n => (b * (q : k) ^ n) • qg k m n

/-- `y⁻¹`. -/
noncomputable def qYi (q : kˣ) (b : k) : Module.End k (Fin m → k) :=
  qmk fun n => (b * (q : k) ^ n)⁻¹ • qg k m n

theorem qX_g (a : k) (n : ℕ) (hn : n < m) :
    qX a (qg k m n) = if n + 1 < m then qg k m (n + 1) else a • qg k m 0 :=
  qmk_g _ n hn

theorem qXi_g (a : k) (n : ℕ) (hn : n < m) :
    qXi a (qg k m n) = if n = 0 then a⁻¹ • qg k m (m - 1) else qg k m (n - 1) :=
  qmk_g _ n hn

theorem qY_g (b : k) (n : ℕ) (hn : n < m) :
    qY q b (qg k m n) = (b * (q : k) ^ n) • qg k m n :=
  qmk_g _ n hn

theorem qYi_g (b : k) (n : ℕ) (hn : n < m) :
    qYi q b (qg k m n) = (b * (q : k) ^ n)⁻¹ • qg k m n :=
  qmk_g _ n hn

/-- The model satisfies the `q`-Weyl relations. -/
theorem isQWeylRel_model (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsQWeylRel q (qX (m := m) a) (qXi a) (qY q b) (qYi q b) := by
  have hqm : (q : k) ^ m = 1 := by
    have : q ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one q
    simpa using congrArg Units.val this
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hμ : ∀ n : ℕ, b * (q : k) ^ n ≠ 0 := fun n => mul_ne_zero hb (pow_ne_zero _ hq0)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine qmk_ext fun n hn => ?_
    rw [Module.End.mul_apply, qXi_g a n hn]
    by_cases h0 : n = 0
    · subst h0
      simp only [if_true, map_smul]
      rw [qX_g a (m - 1) (by omega), if_neg (by omega), smul_smul, inv_mul_cancel₀ ha, one_smul]
      rfl
    · rw [if_neg h0, qX_g a (n - 1) (by omega), if_pos (by omega), Nat.sub_add_cancel (by omega)]
      rfl
  · refine qmk_ext fun n hn => ?_
    rw [Module.End.mul_apply, qX_g a n hn]
    by_cases h1 : n + 1 < m
    · rw [if_pos h1, qXi_g a (n + 1) h1, if_neg (by omega), Nat.add_sub_cancel]
      rfl
    · rw [if_neg h1, map_smul, qXi_g a 0 hm0, if_pos rfl, smul_smul, mul_inv_cancel₀ ha, one_smul,
        show n = m - 1 by omega]
      rfl
  · refine qmk_ext fun n hn => ?_
    rw [Module.End.mul_apply, qYi_g b n hn, map_smul, qY_g b n hn, smul_smul,
      inv_mul_cancel₀ (hμ n), one_smul]
    rfl
  · refine qmk_ext fun n hn => ?_
    rw [Module.End.mul_apply, qY_g b n hn, map_smul, qYi_g b n hn, smul_smul,
      mul_inv_cancel₀ (hμ n), one_smul]
    rfl
  · refine qmk_ext fun n hn => ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply]
    rw [qY_g b n hn, map_smul, qX_g a n hn]
    by_cases h1 : n + 1 < m
    · rw [if_pos h1, qY_g b (n + 1) h1, smul_smul]
      congr 1
      rw [pow_succ]; ring
    · have hn1 : n + 1 = m := by omega
      rw [if_neg h1, map_smul, qY_g b 0 hm0, smul_smul, smul_smul, smul_smul]
      congr 1
      have h2 : (q : k) ^ n * q = 1 := by rw [← pow_succ, hn1, hqm]
      simp only [pow_zero]
      linear_combination (-(a * b)) * h2

/-- The `m`-dimensional model representation of the `q`-Weyl algebra with parameters `a, b`. -/
noncomputable def qmodRep (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    QWeylAlgebra k q →ₐ[k] Module.End k (Fin m → k) :=
  qWeylLift (isQWeylRel_model hm0 hm ha hb)

theorem qmodRep_X (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    qmodRep hm0 hm ha hb (qWeylX k q) = qX a := qWeylLift_X _

theorem qmodRep_Xi (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    qmodRep hm0 hm ha hb (qWeylXinv k q) = qXi a := qWeylLift_Xinv _

theorem qmodRep_Y (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    qmodRep hm0 hm ha hb (qWeylY k q) = qY q b := qWeylLift_Y _

theorem qmodRep_Yi (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    qmodRep hm0 hm ha hb (qWeylYinv k q) = qYi q b := qWeylLift_Yinv _

theorem qY_apply (b : k) (f : Fin m → k) (i : Fin m) : qY q b f i = (b * (q : k) ^ (i : ℕ)) * f i := by
  have := repr_diag (Pi.basisFun k (Fin m)) (qY (m := m) q b) (fun i => b * (q : k) ^ (i : ℕ))
    (fun r => by
      have := qY_g (q := q) (m := m) b r r.2
      have e : qg k m r = Pi.basisFun k (Fin m) r := by simp [qg]
      rw [e] at this
      simpa using this) f i
  simpa using this

theorem qg_sum (f : Fin m → k) : f = ∑ i : Fin m, f i • qg k m i := by
  conv_lhs => rw [← Finset.univ_sum_single f]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext j
  by_cases hj : j = i
  · subst hj; simp [qg]
  · simp [qg, Pi.single_apply, hj]

/-- The model representation is irreducible. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qmodRep_irreducible (hm0 : 0 < m) (hm : orderOf q = m) {a b : k} (ha : a ≠ 0)
    (hb : b ≠ 0) (W : Submodule k (Fin m → k))
    (hW : ∀ z : QWeylAlgebra k q, ∀ w ∈ W, qmodRep hm0 hm ha hb z w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have hX : ∀ w ∈ W, qX a w ∈ W := fun w hw => by
    simpa [qmodRep_X hm0 hm ha hb] using hW (qWeylX k q) w hw
  have hY : ∀ w ∈ W, qY q b w ∈ W := fun w hw => by
    simpa [qmodRep_Y hm0 hm ha hb] using hW (qWeylY k q) w hw
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w0, hw0W, hw00⟩ := (Submodule.ne_bot_iff W).1 hbot
  -- a basis vector lies in `W`
  have key : ∀ N : ℕ, ∀ w ∈ W, w ≠ 0 → (Finset.univ.filter fun i => w i ≠ 0).card = N →
      ∃ n, ∃ h : n < m, qg k m n ∈ W := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro w hwW hw0 hcard
      have hne : (Finset.univ.filter fun i => w i ≠ 0).Nonempty := by
        by_contra h
        apply hw0
        funext i
        by_contra hi
        exact h ⟨i, by simpa using hi⟩
      by_cases h1 : (Finset.univ.filter fun i => w i ≠ 0).card = 1
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
        have hwi : w i ≠ 0 := by
          have : i ∈ Finset.univ.filter fun i => w i ≠ 0 := by rw [hi]; simp
          simpa using this
        have hw : w = w i • qg k m i := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [qg]
          · have : w j = 0 := by
              by_contra hne'
              have : j ∈ Finset.univ.filter fun i => w i ≠ 0 := by simpa using hne'
              rw [hi] at this
              exact hj (by simpa using this)
            simp [qg, this, Pi.single_apply, hj]
        refine ⟨i, i.2, ?_⟩
        generalize w i = c at hw hwi
        have := W.smul_mem c⁻¹ hwW
        rwa [hw, smul_smul, inv_mul_cancel₀ hwi, one_smul] at this
      · have hlt : 1 < (Finset.univ.filter fun i => w i ≠ 0).card := by
          have := hne.card_pos; omega
        obtain ⟨i, hi, i', hi', hii⟩ := Finset.one_lt_card.1 hlt
        have hwi : w i ≠ 0 := by simpa using hi
        have hwi' : w i' ≠ 0 := by simpa using hi'
        set w' := qY q b w - (b * (q : k) ^ (i : ℕ)) • w with hw'
        have hw'W : w' ∈ W := W.sub_mem (hY w hwW) (W.smul_mem _ hwW)
        have hcoef : ∀ j, w' j = (b * (q : k) ^ (j : ℕ) - b * (q : k) ^ (i : ℕ)) * w j := by
          intro j
          simp only [hw', Pi.sub_apply, Pi.smul_apply, qY_apply, smul_eq_mul]; ring
        have hdist : b * (q : k) ^ (i' : ℕ) - b * (q : k) ^ (i : ℕ) ≠ 0 := by
          rw [sub_ne_zero]
          intro h
          have h2 : (q : k) ^ (i' : ℕ) = (q : k) ^ (i : ℕ) := by
            have hb' := mul_left_cancel₀ hb h
            exact hb'
          have h3 : q ^ (i' : ℕ) = q ^ (i : ℕ) := Units.ext (by simpa using h2)
          have := pow_injOn_Iio_orderOf (x := q) (by simpa [hm] using i'.2)
            (by simpa [hm] using i.2) h3
          exact hii (Fin.ext this).symm
        have hw'i : w' i = 0 := by rw [hcoef]; simp
        have hw'i' : w' i' ≠ 0 := by rw [hcoef]; exact mul_ne_zero hdist hwi'
        refine ih _ ?_ w' hw'W (fun h0 => hw'i' (by rw [h0]; rfl)) rfl
        rw [← hcard]
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, hi, ?_⟩)
        · intro j hj
          have hj' : w' j ≠ 0 := by simpa using hj
          rw [hcoef] at hj'
          simpa using right_ne_zero_of_mul hj'
        · simpa using hw'i
  obtain ⟨n, hn, hgn⟩ := key _ w0 hw0W hw00 rfl
  -- all basis vectors lie in `W`
  have hfwd : ∀ d, n + d < m → qg k m (n + d) ∈ W := by
    intro d
    induction d with
    | zero => intro _; simpa using hgn
    | succ d ih =>
      intro hd
      have := hX _ (ih (by omega))
      rwa [qX_g a (n + d) (by omega), if_pos (by omega)] at this
  have hlast : qg k m (m - 1) ∈ W := by
    have := hfwd (m - 1 - n) (by omega)
    rwa [show n + (m - 1 - n) = m - 1 by omega] at this
  have hzero : qg k m 0 ∈ W := by
    have := hX _ hlast
    rw [qX_g a (m - 1) (by omega), if_neg (by omega)] at this
    have := W.smul_mem a⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  have hall : ∀ j, j < m → qg k m j ∈ W := by
    intro j
    induction j with
    | zero => intro _; exact hzero
    | succ j ih =>
      intro hj
      have := hX _ (ih (by omega))
      rwa [qX_g a j (by omega), if_pos hj] at this
  rw [eq_top_iff]
  intro f _
  rw [qg_sum f]
  exact Submodule.sum_mem _ fun i _ => W.smul_mem _ (hall i i.2)

theorem qg_ext {M : Type*} [AddCommGroup M] [Module k M] {F G : (Fin m → k) →ₗ[k] M}
    (h : ∀ n < m, F (qg k m n) = G (qg k m n)) : F = G := by
  refine (Pi.basisFun k (Fin m)).ext fun i => ?_
  have := h i i.2
  simpa [qg] using this

/-- Intertwining on the four generators implies intertwining everywhere. -/
theorem qweyl_intertwine_all {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂]
    [Module k V₂] (ρ₁ : QWeylAlgebra k q →ₐ[k] Module.End k V₁)
    (ρ₂ : QWeylAlgebra k q →ₐ[k] Module.End k V₂) (φ : V₁ →ₗ[k] V₂)
    (hx : φ ∘ₗ ρ₁ (qWeylX k q) = ρ₂ (qWeylX k q) ∘ₗ φ)
    (hxi : φ ∘ₗ ρ₁ (qWeylXinv k q) = ρ₂ (qWeylXinv k q) ∘ₗ φ)
    (hy : φ ∘ₗ ρ₁ (qWeylY k q) = ρ₂ (qWeylY k q) ∘ₗ φ)
    (hyi : φ ∘ₗ ρ₁ (qWeylYinv k q) = ρ₂ (qWeylYinv k q) ∘ₗ φ) (z : QWeylAlgebra k q) :
    φ ∘ₗ ρ₁ z = ρ₂ z ∘ₗ φ := by
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k (QWeylRel k q) z
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    refine LinearMap.ext fun w => ?_
    simp [Algebra.algebraMap_eq_smul_one]
  | grade1 i =>
    fin_cases i
    · exact hx
    · exact hxi
    · exact hy
    · exact hyi
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, ha, LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]

section Classify

variable [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [Nontrivial V]

/-- Problem 1.27(c): over an algebraically closed field, let `q` have order `m` and let `V` be a
finite-dimensional irreducible representation of the `q`-Weyl algebra.  If `v ≠ 0` is an eigenvector
of `y` with eigenvalue `β`, then `β ≠ 0`, `x^m` acts by a nonzero scalar `c`, and `V` is isomorphic to
the model `qmodRep` with parameters `(c, β)`. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_irrep_iso (hm0 : 0 < m) (hm : orderOf q = m)
    (ρ : QWeylAlgebra k q →ₐ[k] Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ z : QWeylAlgebra k q, ∀ w ∈ W, ρ z w ∈ W) → W = ⊥ ∨ W = ⊤)
    (v : V) (β : k) (hv0 : v ≠ 0) (hYv : ρ (qWeylY k q) v = β • v) :
    ∃ (c : k) (hc : c ≠ 0) (hβ : β ≠ 0) (e : (Fin m → k) ≃ₗ[k] V),
      ρ (qWeylX k q ^ m) = c • 1 ∧
      ∀ (z : QWeylAlgebra k q) (w : Fin m → k), e (qmodRep hm0 hm hc hβ z w) = ρ z (e w) := by
  set X := ρ (qWeylX k q) with hXdef
  set Xi := ρ (qWeylXinv k q) with hXidef
  set Y := ρ (qWeylY k q) with hYdef
  set Yi := ρ (qWeylYinv k q) with hYidef
  have r : IsQWeylRel q X Xi Y Yi := isQWeylRel_rep ρ
  have hYv' : Y v = β • v := hYv
  have hirr' : ∀ W : Submodule k V, (∀ w ∈ W, X w ∈ W) → (∀ w ∈ W, Xi w ∈ W) →
      (∀ w ∈ W, Y w ∈ W) → (∀ w ∈ W, Yi w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hx hxi hy hyi => hirr W (qweyl_stable_all ρ W hx hxi hy hyi)
  have hqm : (q : k) ^ m = 1 := by
    have : q ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one q
    simpa using congrArg Units.val this
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hXiX : ∀ w, Xi (X w) = w := fun w => by
    have := congrArg (fun F => F w) r.xix
    simpa using this
  have hXXi : ∀ w, X (Xi w) = w := fun w => by
    have := congrArg (fun F => F w) r.xxi
    simpa using this
  have hYiY : ∀ w, Yi (Y w) = w := fun w => by
    have := congrArg (fun F => F w) r.yiy
    simpa using this
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hv0
    rw [← hYiY v, hYv, h0, zero_smul, map_zero]
  have hXinj : Function.Injective X := fun a b h => by
    have := congrArg Xi h
    rwa [hXiX, hXiX] at this
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
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hYv', map_smul] at h
    rw [h, smul_smul]
  obtain ⟨c, hc⟩ := qrel_scalar r hirr' (X ^ m) (Commute.self_pow X m).eq.symm (by
    have := qrel_Y_mul_X_pow r m
    rw [hqm, one_smul] at this
    exact this.symm)
  have hXm : (X ^ m) v = c • v := by rw [hc]; simp
  have hc0 : c ≠ 0 := by
    intro h0
    apply hXpow_ne m
    rw [hXm, h0, zero_smul]
  have hXiv : Xi v = c⁻¹ • (X ^ (m - 1)) v := by
    have h5 : X ((X ^ (m - 1)) v) = c • v := by
      rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hm0, hXm]
    have := congrArg Xi h5
    rw [hXiX, map_smul] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  -- the map `φ`
  let φ : (Fin m → k) →ₗ[k] V := (Pi.basisFun k (Fin m)).constr k (fun i => (X ^ (i : ℕ)) v)
  have hφ : ∀ n < m, φ (qg k m n) = (X ^ n) v := by
    intro n hn
    have : qg k m n = Pi.basisFun k (Fin m) ⟨n, hn⟩ := by simp [qg, hn]
    rw [this, Module.Basis.constr_basis]
  have hφ0 : φ (qg k m 0) = v := by rw [hφ 0 hm0]; simp
  have hx : φ ∘ₗ qmodRep hm0 hm hc0 hβ0 (qWeylX k q) = X ∘ₗ φ := by
    rw [qmodRep_X]
    refine qg_ext fun n hn => ?_
    simp only [LinearMap.comp_apply]
    rw [qX_g c n hn]
    by_cases h1 : n + 1 < m
    · rw [if_pos h1, hφ _ h1, hφ _ hn, pow_succ', Module.End.mul_apply]
    · rw [if_neg h1, map_smul, hφ 0 hm0, hφ n hn, show n = m - 1 by omega,
        ← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hm0, hXm]
      simp
  have hxi : φ ∘ₗ qmodRep hm0 hm hc0 hβ0 (qWeylXinv k q) = Xi ∘ₗ φ := by
    rw [qmodRep_Xi]
    refine qg_ext fun n hn => ?_
    simp only [LinearMap.comp_apply]
    rw [qXi_g c n hn]
    by_cases h0 : n = 0
    · subst h0
      rw [if_pos rfl, map_smul, hφ _ (by omega), hφ 0 hm0, pow_zero, Module.End.one_apply, hXiv]
    · rw [if_neg h0, hφ _ (by omega), hφ n hn]
      conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ', Module.End.mul_apply, hXiX]
  have hy : φ ∘ₗ qmodRep hm0 hm hc0 hβ0 (qWeylY k q) = Y ∘ₗ φ := by
    rw [qmodRep_Y]
    refine qg_ext fun n hn => ?_
    simp only [LinearMap.comp_apply]
    rw [qY_g β n hn, map_smul, hφ n hn, hYX, mul_comm]
  have hyi : φ ∘ₗ qmodRep hm0 hm hc0 hβ0 (qWeylYinv k q) = Yi ∘ₗ φ := by
    rw [qmodRep_Yi]
    refine qg_ext fun n hn => ?_
    simp only [LinearMap.comp_apply]
    rw [qYi_g β n hn, map_smul, hφ n hn]
    have hμ : (q : k) ^ n * β ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) hβ0
    have h1 := congrArg Yi (hYX n)
    rw [hYiY, map_smul] at h1
    rw [mul_comm β, eq_comm]
    exact (eq_inv_smul_iff₀ hμ).2 h1.symm |>.symm ▸ rfl
  have hall := qweyl_intertwine_all (qmodRep hm0 hm hc0 hβ0) ρ φ hx hxi hy hyi
  have hall' : ∀ z w, φ (qmodRep hm0 hm hc0 hβ0 z w) = ρ z (φ w) := fun z w =>
    congrArg (fun F => F w) (hall z)
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range φ) (fun z w hw => by
      obtain ⟨u, rfl⟩ := hw
      exact ⟨qmodRep hm0 hm hc0 hβ0 z u, hall' z u⟩) with h | h
    · exfalso
      have : v ∈ LinearMap.range φ := ⟨qg k m 0, hφ0⟩
      rw [h] at this
      exact hv0 (by simpa using this)
    · exact h
  have hdim : Module.finrank k V = m := qweyl_irrep_finrank hm0 hm ρ hirr
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hdim])).2 hsurj
  refine ⟨c, hc0, hβ0, LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, ?_, fun z w => hall' z w⟩
  rw [map_pow]
  exact hc

end Classify

theorem qX_pow_g (a : k) (n j : ℕ) (h : n + j < m) :
    (qX a ^ j : Module.End k (Fin m → k)) (qg k m n) = qg k m (n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih (by omega), ← add_assoc,
      qX_g a (n + j) (by omega), if_pos (by omega)]

theorem qX_pow_m (a : k) : (qX a ^ m : Module.End k (Fin m → k)) = a • 1 := by
  rcases Nat.eq_zero_or_pos m with h0 | hm0
  · subst h0; exact Subsingleton.elim _ _
  refine qmk_ext ?_
  intro n hn
  have e2 : (qX a ^ m : Module.End k (Fin m → k)) =
      qX a ^ n * (qX a * qX a ^ (m - n - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [e2, Module.End.mul_apply, Module.End.mul_apply, qX_pow_g a n (m - n - 1) (by omega),
    qX_g a (n + (m - n - 1)) (by omega), if_neg (by omega), map_smul]
  have h2 := qX_pow_g (m := m) a 0 n (by omega)
  rw [zero_add] at h2
  rw [h2]
  rfl

theorem qY_pow_g (b : k) (n j : ℕ) (hn : n < m) :
    (qY q b ^ j : Module.End k (Fin m → k)) (qg k m n) = (b * (q : k) ^ n) ^ j • qg k m n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, qY_g b n hn, smul_smul, pow_succ]

theorem qY_pow_m (hm : orderOf q = m) (b : k) :
    (qY q b ^ m : Module.End k (Fin m → k)) = (b ^ m) • 1 := by
  have hqm : (q : k) ^ m = 1 := by
    have : q ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one q
    simpa using congrArg Units.val this
  refine qmk_ext ?_
  intro n hn
  rw [qY_pow_g b n m hn, mul_pow, ← pow_mul, mul_comm n m, pow_mul, hqm, one_pow, mul_one]
  rfl

theorem qg_zero_ne (hm0 : 0 < m) : qg k m 0 ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hm0⟩
  simp [qg, hm0] at this

/-- Problem 1.27(c), uniqueness: if two model representations are isomorphic, then `x^m` acts by
the same scalar `a = a'` and `y^m` by the same scalar `b^m = b'^m`. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qmodRep_iso_unique (hm0 : 0 < m) (hm : orderOf q = m) {a b a' b' : k} (ha : a ≠ 0)
    (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0) (e : (Fin m → k) ≃ₗ[k] (Fin m → k))
    (he : ∀ (z : QWeylAlgebra k q) (w : Fin m → k),
      e (qmodRep hm0 hm ha hb z w) = qmodRep hm0 hm ha' hb' z (e w)) :
    a = a' ∧ b ^ m = b' ^ m := by
  have hu : e (qg k m 0) ≠ 0 := fun h => qg_zero_ne hm0 (e.injective (by rw [h, map_zero]))
  constructor
  · have h1 := he (qWeylX k q ^ m) (qg k m 0)
    rw [map_pow, map_pow, qmodRep_X, qmodRep_X, qX_pow_m, qX_pow_m] at h1
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul] at h1
    exact smul_left_injective k hu h1
  · have h1 := he (qWeylY k q ^ m) (qg k m 0)
    rw [map_pow, map_pow, qmodRep_Y, qmodRep_Y, qY_pow_m hm, qY_pow_m hm] at h1
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul] at h1
    exact smul_left_injective k hu h1

/-- Problem 1.27(c), uniqueness (converse): over an algebraically closed field, model
representations with the same invariants `(a, b^m)` are isomorphic.  Together with
`qmodRep_iso_unique` this shows that `(a, b^m)` is a complete invariant of the isomorphism class. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qmodRep_iso_of_eq [IsAlgClosed k] (hm0 : 0 < m) (hm : orderOf q = m) {a b a' b' : k}
    (ha : a ≠ 0) (hb : b ≠ 0) (ha' : a' ≠ 0) (hb' : b' ≠ 0) (h1 : a = a') (h2 : b ^ m = b' ^ m) :
    ∃ e : (Fin m → k) ≃ₗ[k] (Fin m → k), ∀ (z : QWeylAlgebra k q) (w : Fin m → k),
      e (qmodRep hm0 hm ha hb z w) = qmodRep hm0 hm ha' hb' z (e w) := by
  subst h1
  haveI : NeZero m := ⟨hm0.ne'⟩
  have hprim : IsPrimitiveRoot (q : k) m := by
    rw [← hm, ← orderOf_units]; exact IsPrimitiveRoot.orderOf _
  have h3 : (b / b') ^ m = 1 := by
    rw [div_pow, h2, div_self (pow_ne_zero _ hb')]
  obtain ⟨s, hs, hqs⟩ := hprim.eq_pow_of_pow_eq_one h3
  have hb_eq : b = b' * (q : k) ^ s := by
    rw [hqs]; field_simp
  have hv0 : qg k m s ≠ 0 := by
    intro h
    have := congrFun h ⟨s, hs⟩
    simp [qg, hs] at this
  have hYv : qmodRep hm0 hm ha hb' (qWeylY k q) (qg k m s) = b • qg k m s := by
    rw [qmodRep_Y, qY_g b' s hs, hb_eq]
  obtain ⟨c, hc, hβ, e, hcX, he⟩ := qweyl_irrep_iso hm0 hm (qmodRep hm0 hm ha hb')
    (fun W hW => qmodRep_irreducible hm0 hm ha hb' W hW) (qg k m s) b hv0 hYv
  have hca : c = a := by
    have h4 := congrArg (fun F => F (qg k m 0)) hcX
    simp only [map_pow, qmodRep_X, qX_pow_m, LinearMap.smul_apply, Module.End.one_apply] at h4
    exact (smul_left_injective k (qg_zero_ne hm0) h4).symm
  subst hca
  exact ⟨e, he⟩

end Model

end UndergradKB.RepresentationTheory
