import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.SchurWeyl

/-! # Problem 4.69: invariants of matrices; the multilinear first fundamental theorem (Etingof et al.)

Let `V = ℂ^N`, `W = V^{⊗n}`.  For matrices `X₁, …, X_n` put `tensorOp X = X₁ ⊗ ⋯ ⊗ X_n ∈ End W`.

* `trace_comp_tensorOp`: `tr(H ∘ (X₁ ⊗ ⋯ ⊗ X_n)) = ∑_{I,K} H_{I,K} ∏_l (X_l)_{K_l I_l}` for any `H ∈ End W`.
* `multilinear_fft`: every conjugation-invariant multilinear function `f : M_N(ℂ)^n → ℂ` is a linear combination
  of the functions `T_σ(X) = ∑_I ∏_l (X_l)_{I(σ l), I(l)}` (`σ ∈ S_n`), i.e. of the products over the cycles of `σ`
  of traces of the corresponding ordered products of the `X_l`.  The proof: `f(X) = tr(F ∘ (X₁ ⊗ ⋯ ⊗ X_n))` for a
  unique `F ∈ End W`; invariance of `f` says that `F` commutes with all `g^{⊗n}`; by Schur-Weyl duality (the
  centralizer of `GL(V)` in `End W` is the image of `ℂ[S_n]`) `F` is a combination of permutation operators; and
  `tr(P_σ ∘ (X₁ ⊗ ⋯ ⊗ X_n)) = T_σ(X)`.
-/

namespace UndergradKB.RepresentationTheory

open PiTensorProduct Finset
open scoped TensorProduct Classical

namespace MatrixInv

variable (N n : ℕ)

/-- The tensor power `V^{⊗n}` of `V = ℂ^N`. -/
abbrev TP := ⨂[ℂ] _ : Fin n, (Fin N → ℂ)

/-- The standard basis of `V^{⊗n}` indexed by `Fin n → Fin N`. -/
noncomputable def stdB : Module.Basis (Fin n → Fin N) ℂ (TP N n) :=
  Basis.piTensorProduct fun _ => Pi.basisFun ℂ (Fin N)

variable {N n}

/-- The operator `X₁ ⊗ ⋯ ⊗ X_n` on `V^{⊗n}`. -/
noncomputable def tensorOp (X : Fin n → Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n :=
  PiTensorProduct.map fun l => Matrix.toLin' (X l)

theorem stdB_apply (I : Fin n → Fin N) : stdB N n I = tprod ℂ fun l => (Pi.single (I l) 1 : Fin N → ℂ) := by
  simp [stdB, Basis.piTensorProduct_apply]

theorem repr_tensorOp (X : Fin n → Matrix (Fin N) (Fin N) ℂ) (I K : Fin n → Fin N) :
    (stdB N n).repr (tensorOp X (stdB N n I)) K = ∏ l, X l (K l) (I l) := by
  rw [stdB_apply, tensorOp, PiTensorProduct.map_tprod]
  simp only [stdB, Basis.piTensorProduct_repr_tprod_apply]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [Matrix.toLin'_apply, Matrix.mulVec_single_one]

/-- `tr(H ∘ (X₁ ⊗ ⋯ ⊗ X_n)) = ∑_{I,K} H_{I,K} ∏_l (X_l)_{K_l I_l}`. -/
theorem trace_comp_tensorOp (H : TP N n →ₗ[ℂ] TP N n) (X : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.trace ℂ (TP N n) (H ∘ₗ tensorOp X) =
      ∑ I, ∑ K, (stdB N n).repr (H (stdB N n K)) I * ∏ l, X l (K l) (I l) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (stdB N n), Matrix.trace]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply]
  have h : tensorOp X (stdB N n I) = ∑ K, (∏ l, X l (K l) (I l)) • stdB N n K := by
    conv_lhs => rw [← (stdB N n).sum_repr (tensorOp X (stdB N n I))]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [repr_tensorOp]
  rw [h, map_sum]
  simp only [map_smul, map_sum, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun K _ => ?_
  ring

/-- The matrix unit with a `1` in position `(a, b)`. -/
noncomputable def unitMat (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ := Matrix.single a b (1 : ℂ)

/-- Multilinear expansion of a multilinear function of `n` matrices in matrix units. -/
theorem multilinear_expand (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ)
    (X : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    f X = ∑ K : Fin n → Fin N, ∑ I : Fin n → Fin N,
      (∏ l, X l (K l) (I l)) * f (fun l => unitMat (K l) (I l)) := by
  have hX : ∀ l, X l = ∑ p : Fin N × Fin N, X l p.1 p.2 • unitMat p.1 p.2 := by
    intro l
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single (X l)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp [unitMat, Matrix.smul_single]
  have h1 : f X = f (fun l => ∑ p : Fin N × Fin N, X l p.1 p.2 • unitMat p.1 p.2) := by
    congr 1; funext l; exact hX l
  rw [h1, MultilinearMap.map_sum]
  simp_rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _) _ _ (fun r => ?_))
  simp [Equiv.arrowProdEquivProdArrow]

/-- The operator `F` on `V^{⊗n}` representing a multilinear function `f` through the trace pairing. -/
noncomputable def opOf (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ) :
    TP N n →ₗ[ℂ] TP N n :=
  Matrix.toLin (stdB N n) (stdB N n)
    (Matrix.of fun I K => f (fun l => unitMat (K l) (I l)))

theorem repr_opOf (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ)
    (I K : Fin n → Fin N) :
    (stdB N n).repr (opOf f (stdB N n K)) I = f (fun l => unitMat (K l) (I l)) := by
  rw [← LinearMap.toMatrix_apply, opOf, LinearMap.toMatrix_toLin]
  rfl

/-- `f (X₁, …, X_n) = tr (F ∘ (X₁ ⊗ ⋯ ⊗ X_n))`. -/
theorem eq_trace_opOf (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ)
    (X : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    f X = LinearMap.trace ℂ (TP N n) (opOf f ∘ₗ tensorOp X) := by
  rw [trace_comp_tensorOp, multilinear_expand f X, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun K _ => ?_
  rw [repr_opOf, mul_comm]

/-- An operator `H` with `tr (H ∘ (X₁ ⊗ ⋯ ⊗ X_n)) = 0` for all `X` is zero. -/
theorem eq_zero_of_trace_tensorOp (H : TP N n →ₗ[ℂ] TP N n)
    (h : ∀ X : Fin n → Matrix (Fin N) (Fin N) ℂ, LinearMap.trace ℂ (TP N n) (H ∘ₗ tensorOp X) = 0) :
    H = 0 := by
  refine (stdB N n).ext fun K => ?_
  refine (stdB N n).repr.injective ?_
  ext I
  have h1 := h (fun l => unitMat (K l) (I l))
  rw [trace_comp_tensorOp] at h1
  have h2 : ∀ I' K' : Fin n → Fin N,
      (∏ l, unitMat (K l) (I l) (K' l) (I' l)) = if I' = I ∧ K' = K then 1 else 0 := by
    intro I' K'
    by_cases hc : I' = I ∧ K' = K
    · obtain ⟨rfl, rfl⟩ := hc
      simp [unitMat]
    · rw [if_neg hc]
      have : ∃ l, ¬(K l = K' l ∧ I l = I' l) := by
        by_contra hall
        push Not at hall
        exact hc ⟨funext fun l => (hall l).2.symm, funext fun l => (hall l).1.symm⟩
      obtain ⟨l, hl⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [unitMat, Matrix.single_apply, hl])
  simp only [h2, mul_ite, mul_one, mul_zero] at h1
  rw [Finset.sum_eq_single I] at h1
  · rw [Finset.sum_eq_single K] at h1
    · simpa using h1
    · intro K' _ hK'
      simp [hK']
    · simp
  · intro I' _ hI'
    refine Finset.sum_eq_zero fun K' _ => ?_
    simp [hI']
  · simp

/-- The operator `g ⊗ ⋯ ⊗ g` on `V^{⊗n}`. -/
noncomputable def Gop (g : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n :=
  PiTensorProduct.map fun _ => Matrix.toLin' g

theorem Gop_mul (g g' : Matrix (Fin N) (Fin N) ℂ) : (Gop g : TP N n →ₗ[ℂ] TP N n) * Gop g' = Gop (g * g') := by
  unfold Gop
  rw [Module.End.mul_eq_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext l
  rw [Matrix.toLin'_mul]

theorem Gop_one : (Gop (1 : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n) = 1 := by
  unfold Gop
  simp only [Matrix.toLin'_one]
  exact PiTensorProduct.map_one

theorem Gop_tensorOp_Gop (g g' : Matrix (Fin N) (Fin N) ℂ) (X : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    (Gop g : TP N n →ₗ[ℂ] TP N n) * tensorOp X * Gop g' = tensorOp (fun l => g * X l * g') := by
  unfold Gop tensorOp
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 1
  funext l
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]

/-- Invariance of `f` under conjugation says that `F` commutes with every `g^{⊗n}`. -/
theorem opOf_commute (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ)
    (hf : ∀ g : (Matrix (Fin N) (Fin N) ℂ)ˣ, ∀ X : Fin n → Matrix (Fin N) (Fin N) ℂ,
      f (fun l => (g : Matrix (Fin N) (Fin N) ℂ) * X l * ((g⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ)) = f X)
    (g : (Matrix (Fin N) (Fin N) ℂ)ˣ) :
    (Gop (g : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n) * opOf f =
      opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ) := by
  set g' : Matrix (Fin N) (Fin N) ℂ := ((g⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ) with hg'
  have h1 : (Gop g' : TP N n →ₗ[ℂ] TP N n) * Gop (g : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [Gop_mul, hg', Units.inv_mul, Gop_one]
  have h2 : (Gop (g : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n) * Gop g' = 1 := by
    rw [Gop_mul, hg', Units.mul_inv, Gop_one]
  have hH : Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ) - opOf f = 0 := by
    apply eq_zero_of_trace_tensorOp
    intro X
    have e1 : (Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ) - opOf f) ∘ₗ tensorOp X
        = (Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ)) * tensorOp X - opOf f * tensorOp X := by
      rw [LinearMap.sub_comp]; rfl
    have e2 : LinearMap.trace ℂ (TP N n)
        ((Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ)) * tensorOp X) =
        LinearMap.trace ℂ (TP N n) (opOf f * tensorOp (fun l => (g : Matrix (Fin N) (Fin N) ℂ) * X l * g')) := by
      rw [← Gop_tensorOp_Gop]
      generalize (Gop g' : TP N n →ₗ[ℂ] TP N n) = G'
      generalize (Gop (g : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n) = G
      generalize (opOf f : TP N n →ₗ[ℂ] TP N n) = F
      generalize (tensorOp X : TP N n →ₗ[ℂ] TP N n) = T
      calc LinearMap.trace ℂ (TP N n) (G' * F * G * T) = LinearMap.trace ℂ (TP N n) (G' * (F * G * T)) := by
            rw [show G' * F * G * T = G' * (F * G * T) by simp only [mul_assoc]]
        _ = LinearMap.trace ℂ (TP N n) (F * G * T * G') := LinearMap.trace_mul_comm _ _ _
        _ = LinearMap.trace ℂ (TP N n) (F * (G * T * G')) := by
            rw [show F * G * T * G' = F * (G * T * G') by simp only [mul_assoc]]
    have e3 := eq_trace_opOf f (fun l => (g : Matrix (Fin N) (Fin N) ℂ) * X l * g')
    have e4 := eq_trace_opOf f X
    rw [hf g X] at e3
    have key : LinearMap.trace ℂ (TP N n)
        ((Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ)) * tensorOp X) =
        LinearMap.trace ℂ (TP N n) (opOf f * tensorOp X) := by
      rw [e2, Module.End.mul_eq_comp, Module.End.mul_eq_comp]
      exact e3.symm.trans e4
    rw [e1]
    have hz : LinearMap.trace ℂ (TP N n) ((Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ)) * tensorOp X) -
        LinearMap.trace ℂ (TP N n) (opOf f * tensorOp X) = 0 := by
      rw [key]; exact sub_self _
    have hms := (LinearMap.trace ℂ (TP N n)).map_sub
      ((Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ)) * tensorOp X) (opOf f * tensorOp X)
    exact hms.trans hz
  have hH' : Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ) = opOf f := sub_eq_zero.mp hH
  calc (Gop (g : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n) * opOf f
      = Gop (g : Matrix (Fin N) (Fin N) ℂ) * (Gop g' * opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ)) := by
        rw [hH']
    _ = opOf f * Gop (g : Matrix (Fin N) (Fin N) ℂ) := by
        rw [← mul_assoc, ← mul_assoc, h2, one_mul]

/-- **Schur-Weyl step**: for a conjugation-invariant multilinear `f`, the operator `F` lies in the image of
`ℂ[S_n]` in `End(V^{⊗n})` (the centralizer of `GL(V)`). -/
theorem opOf_mem_swImage (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ)
    (hf : ∀ g : (Matrix (Fin N) (Fin N) ℂ)ˣ, ∀ X : Fin n → Matrix (Fin N) (Fin N) ℂ,
      f (fun l => (g : Matrix (Fin N) (Fin N) ℂ) * X l * ((g⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ)) = f X) :
    opOf f ∈ swImage (Fin N → ℂ) n := by
  have hcomm : ∀ u : ((Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))ˣ,
      tensorPowerMap n (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) * opOf f =
        opOf f * tensorPowerMap n (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) := by
    intro u
    let g : (Matrix (Fin N) (Fin N) ℂ)ˣ :=
      Units.map (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin N)).symm.toAlgHom.toMonoidHom u
    have hg : Matrix.toLin' (g : Matrix (Fin N) (Fin N) ℂ) = (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) := by
      have : (g : Matrix (Fin N) (Fin N) ℂ) = LinearMap.toMatrix' (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) := rfl
      rw [this]
      exact Matrix.toLin'_toMatrix' _
    have := opOf_commute f hf g
    have e : tensorPowerMap n (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) = Gop (g : Matrix (Fin N) (Fin N) ℂ) := by
      unfold tensorPowerMap Gop
      rw [hg]
    rw [e]
    exact this
  rw [(schurWeyl_duality (V := Fin N → ℂ) n).2.1.symm]
  refine (Subalgebra.mem_centralizer_iff (R := ℂ)).mpr ?_
  intro a ha
  have ha' : a ∈ Subalgebra.centralizer ℂ (Set.range (tensorPowerPermRep ℂ n (Fin N → ℂ))) := by
    rw [centralizer_perm_eq_adjoin_diagAction]
    exact ha
  have ha'' : a ∈ Submodule.span ℂ (Set.range fun u : ((Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))ˣ =>
      tensorPowerMap n (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))) := by
    rw [span_tensorPowerMap_units_eq_centralizer]
    exact ha'
  have key : ∀ b ∈ Submodule.span ℂ (Set.range fun u : ((Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))ˣ =>
      tensorPowerMap n (u : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))), b * opOf f = opOf f * b := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact hcomm u
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  exact key a ha''

/-- The invariant `T_σ (X₁, …, X_n) = ∑_I ∏_l (X_l)_{I(σ l), I(l)}`; it is the product over the cycles of `σ` of
the traces of the products of the `X_l` along the cycle. -/
noncomputable def Tperm (σ : Equiv.Perm (Fin n)) (X : Fin n → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ I : Fin n → Fin N, ∏ l, X l (I (σ l)) (I l)

/-- `tr(P_σ ∘ (X₁ ⊗ ⋯ ⊗ X_n)) = T_σ(X)`. -/
theorem trace_perm_tensorOp (σ : Equiv.Perm (Fin n)) (X : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    LinearMap.trace ℂ (TP N n) (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ tensorOp X) = Tperm σ X := by
  rw [trace_comp_tensorOp]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hrepr : ∀ K : Fin n → Fin N, (stdB N n).repr (tensorPowerPermRep ℂ n (Fin N → ℂ) σ (stdB N n K)) I =
      if K = fun m => I (σ m) then 1 else 0 := by
    intro K
    rw [stdB_apply, tensorPowerPermRep_tprod]
    simp only [stdB, Basis.piTensorProduct_repr_tprod_apply]
    have : ∀ l, (Pi.basisFun ℂ (Fin N)).repr (Pi.single (K (σ⁻¹ l)) (1 : ℂ)) (I l) =
        if I l = K (σ⁻¹ l) then 1 else 0 := by
      intro l
      simp [Pi.single_apply, eq_comm]
    simp_rw [this]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    constructor
    · intro h
      funext m
      have := h (σ m) (Finset.mem_univ _)
      simpa using this.symm
    · intro h l _
      rw [h]
      simp
  simp_rw [hrepr]
  rw [Finset.sum_eq_single (fun m => I (σ m))]
  · simp [Tperm]
  · intro K _ hK
    simp [hK]
  · simp

/-- Traces against group algebra elements are combinations of the `T_σ`. -/
theorem trace_asAlgebraHom_tensorOp (a : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) :
    ∃ c : Equiv.Perm (Fin n) → ℂ, ∀ X : Fin n → Matrix (Fin N) (Fin N) ℂ,
      LinearMap.trace ℂ (TP N n)
        ((tensorPowerPermRep ℂ n (Fin N → ℂ)).asAlgebraHom a ∘ₗ tensorOp X) = ∑ σ, c σ * Tperm σ X := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, fun X => by simp⟩
  | add x y hx hy =>
    obtain ⟨c₁, h₁⟩ := hx
    obtain ⟨c₂, h₂⟩ := hy
    refine ⟨c₁ + c₂, fun X => ?_⟩
    have : ((tensorPowerPermRep ℂ n (Fin N → ℂ)).asAlgebraHom (x + y)) ∘ₗ tensorOp X =
        (tensorPowerPermRep ℂ n (Fin N → ℂ)).asAlgebraHom x ∘ₗ tensorOp X +
          (tensorPowerPermRep ℂ n (Fin N → ℂ)).asAlgebraHom y ∘ₗ tensorOp X := by
      rw [map_add, LinearMap.add_comp]
    rw [this, map_add, h₁ X, h₂ X, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [add_mul]
  | single σ r =>
    refine ⟨Pi.single σ r, fun X => ?_⟩
    rw [Representation.asAlgebraHom_single, LinearMap.smul_comp, map_smul, trace_perm_tensorOp]
    rw [Finset.sum_eq_single σ]
    · simp
    · intro τ _ hτ
      simp [hτ]
    · simp

/-- The functions `T_σ` are conjugation invariant (the easy converse of the multilinear FFT). -/
@[kb "etingof2011" "Problem 4.69, p. 68"]
theorem Tperm_conj (σ : Equiv.Perm (Fin n)) (g : (Matrix (Fin N) (Fin N) ℂ)ˣ)
    (X : Fin n → Matrix (Fin N) (Fin N) ℂ) :
    Tperm σ (fun l => (g : Matrix (Fin N) (Fin N) ℂ) * X l * ((g⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ))
      = Tperm σ X := by
  set g' : Matrix (Fin N) (Fin N) ℂ := ((g⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ) with hg'
  have h1 : (Gop g' : TP N n →ₗ[ℂ] TP N n) * Gop (g : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [Gop_mul, hg', Units.inv_mul, Gop_one]
  have hP : (tensorPowerPermRep ℂ n (Fin N → ℂ) σ : TP N n →ₗ[ℂ] TP N n) * Gop (g : Matrix (Fin N) (Fin N) ℂ) =
      Gop (g : Matrix (Fin N) (Fin N) ℂ) * tensorPowerPermRep ℂ n (Fin N → ℂ) σ := by
    refine LinearMap.ext fun x => ?_
    exact (tensorPowerMap_perm (Matrix.toLin' (g : Matrix (Fin N) (Fin N) ℂ)) σ x).symm
  rw [← trace_perm_tensorOp, ← trace_perm_tensorOp, ← Gop_tensorOp_Gop]
  have e : (tensorPowerPermRep ℂ n (Fin N → ℂ) σ ∘ₗ (Gop (g : Matrix (Fin N) (Fin N) ℂ) * tensorOp X * Gop g')) =
      (tensorPowerPermRep ℂ n (Fin N → ℂ) σ * (Gop (g : Matrix (Fin N) (Fin N) ℂ) * tensorOp X * Gop g')) := rfl
  rw [e]
  generalize (tensorPowerPermRep ℂ n (Fin N → ℂ) σ : TP N n →ₗ[ℂ] TP N n) = P at hP ⊢
  generalize (Gop g' : TP N n →ₗ[ℂ] TP N n) = G' at h1 ⊢
  generalize (Gop (g : Matrix (Fin N) (Fin N) ℂ) : TP N n →ₗ[ℂ] TP N n) = G at hP h1 ⊢
  generalize (tensorOp X : TP N n →ₗ[ℂ] TP N n) = T
  calc LinearMap.trace ℂ (TP N n) (P * (G * T * G')) = LinearMap.trace ℂ (TP N n) (G * P * T * G') := by
        rw [show P * (G * T * G') = (P * G) * T * G' by simp only [mul_assoc], hP]
    _ = LinearMap.trace ℂ (TP N n) (G' * (G * P * T)) := LinearMap.trace_mul_comm _ _ _
    _ = LinearMap.trace ℂ (TP N n) (P * T) := by
        rw [show G' * (G * P * T) = (G' * G) * P * T by simp only [mul_assoc], h1, one_mul]

/-- **Multilinear first fundamental theorem for matrices.** A multilinear function of `n` matrices
`f : M_N(ℂ)^n → ℂ` that is invariant under simultaneous conjugation by `GL_N(ℂ)` is a linear combination of the
functions `T_σ(X₁, …, X_n) = ∑_I ∏_l (X_l)_{I(σ l), I(l)}`, `σ ∈ S_n` (the products over the cycles of `σ` of the
traces of the corresponding products of the `X_l`). -/
@[kb "etingof2011" "Problem 4.69, p. 68"]
theorem multilinear_fft (f : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ)
    (hf : ∀ g : (Matrix (Fin N) (Fin N) ℂ)ˣ, ∀ X : Fin n → Matrix (Fin N) (Fin N) ℂ,
      f (fun l => (g : Matrix (Fin N) (Fin N) ℂ) * X l * ((g⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ) : Matrix (Fin N) (Fin N) ℂ)) = f X) :
    ∃ c : Equiv.Perm (Fin n) → ℂ, ∀ X : Fin n → Matrix (Fin N) (Fin N) ℂ, f X = ∑ σ, c σ * Tperm σ X := by
  obtain ⟨a, ha⟩ := opOf_mem_swImage f hf
  obtain ⟨c, hc⟩ := trace_asAlgebraHom_tensorOp (N := N) a
  refine ⟨c, fun X => ?_⟩
  rw [eq_trace_opOf f X, ← ha]
  exact hc X

end MatrixInv

end UndergradKB.RepresentationTheory
