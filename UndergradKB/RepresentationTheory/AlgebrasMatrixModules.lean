import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basis
import UndergradKB.Common.Attr

/-! # Modules over a product of matrix algebras (Etingof et al., Theorem 2.6)

For `B = ∏ᵢ Mat_{dᵢ}(k)` the standard module `k^{dᵢ}` is a simple `B`-module on which `B` acts through the
`i`-th factor; every simple `B`-module is isomorphic to exactly one of them, and every finitely generated
`B`-module is a finite direct sum of them.
-/

namespace UndergradKB.RepresentationTheory

open Module

section

variable (k : Type*) [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)

/-- The algebra `∏ᵢ Mat_{dᵢ}(k)`. -/
abbrev MatProd := ∀ i, Matrix (Fin (d i)) (Fin (d i)) k

/-- The standard module `k^{dᵢ}` of `∏ᵢ Mat_{dᵢ}(k)`, on which the product acts through its `i`-th factor. -/
def StdModule (i : ι) : Type _ := Fin (d i) → k

instance (i : ι) : AddCommGroup (StdModule k d i) := inferInstanceAs (AddCommGroup (Fin (d i) → k))

instance (i : ι) : Module k (StdModule k d i) := inferInstanceAs (Module k (Fin (d i) → k))

instance (i : ι) : Module (MatProd k d) (StdModule k d i) :=
  Module.compHom (Fin (d i) → k)
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin (d i))).toRingEquiv.toRingHom.comp
      (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) i))

omit [Fintype ι] [DecidableEq ι] in
theorem MatProd_smul_def {i : ι} (b : MatProd k d) (v : StdModule k d i) :
    b • v = (b i).mulVec (v : Fin (d i) → k) := rfl

variable {k d}

/-- **Etingof et al., Theorem 2.6 (first part)**: the standard module `k^{dᵢ}` is a simple module over
`∏ᵢ Mat_{dᵢ}(k)`. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem isSimpleModule_stdModule (i : ι) [NeZero (d i)] : IsSimpleModule (MatProd k d) (StdModule k d i) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  refine ⟨inferInstanceAs (Nontrivial (Fin (d i) → k)), fun v hv w => ?_⟩
  have hv' : (v : Fin (d i) → k) ≠ 0 := hv
  obtain ⟨j, hj⟩ : ∃ j, (v : Fin (d i) → k) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv' (funext h)
  refine ⟨Pi.single i (Matrix.of fun r c => if c = j then (w : Fin (d i) → k) r / (v : Fin (d i) → k) j else 0), ?_⟩
  show (Pi.single i _ : MatProd k d) • v = w
  rw [MatProd_smul_def]
  funext r
  simp [Matrix.mulVec, dotProduct, hj]

/-- The matrix unit `E_{jj}` in the `i`-th factor of `∏ᵢ Mat_{dᵢ}(k)`. -/
def unitMat (i : ι) (j : Fin (d i)) : MatProd k d := Pi.single i (Matrix.single j j 1)

theorem sum_unitMat : ∑ i, ∑ j, unitMat (k := k) (d := d) i j = 1 := by
  funext i'
  simp only [Finset.sum_apply, unitMat]
  rw [Finset.sum_eq_single i']
  · ext r c
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases h : r = c
    · subst h
      simp only [and_self, Finset.filter_eq', Finset.mem_univ, if_true, Finset.card_singleton,
        Nat.cast_one]
    · have : (Finset.univ.filter fun x : Fin (d i') => x = r ∧ x = c) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x _ hx
        exact h (hx.1.symm.trans hx.2)
      rw [this]
      simp [h]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

theorem unitMat_mul_self (i : ι) (j : Fin (d i)) :
    unitMat (k := k) (d := d) i j * unitMat i j = unitMat i j := by
  funext i'
  by_cases h : i' = i
  · subst h
    simp [unitMat, Matrix.single_mul_single_same]
  · simp [unitMat, h]

/-- The element of `∏ᵢ Mat_{dᵢ}(k)` that is, in the `i`-th factor, the matrix whose `j`-th column is `v` and
whose other columns vanish. -/
def colMat (i : ι) (j : Fin (d i)) (v : StdModule k d i) : MatProd k d :=
  Pi.single i (Matrix.of fun r c => if c = j then (v : Fin (d i) → k) r else 0)

theorem colMat_add (i : ι) (j : Fin (d i)) (v w : StdModule k d i) :
    colMat i j (v + w) = colMat i j v + colMat i j w := by
  funext i'
  by_cases h : i' = i
  · subst h
    ext r c
    by_cases hc : c = j
    · simp [colMat, hc]
      rfl
    · simp [colMat, hc]
  · simp [colMat, h]

theorem colMat_smul (i : ι) (j : Fin (d i)) (b : MatProd k d) (v : StdModule k d i) :
    colMat i j (b • v) = b * colMat i j v := by
  funext i'
  by_cases h : i' = i
  · subst h
    ext r c
    by_cases hc : c = j
    · simp [colMat, hc, MatProd_smul_def, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    · simp [colMat, hc, Matrix.mul_apply]
  · simp [colMat, h]

theorem colMat_single_one (i : ι) (j : Fin (d i)) :
    colMat i j (show StdModule k d i from Pi.single j 1) = unitMat i j := by
  simp only [colMat, unitMat]
  congr 1
  ext r c
  by_cases hc : c = j <;> by_cases hr : r = j <;>
    simp [hc, hr, Matrix.single_apply, Pi.single_apply, eq_comm] <;> grind

variable {S : Type*} [AddCommGroup S] [Module (MatProd k d) S] [IsSimpleModule (MatProd k d) S]

/-- **Etingof et al., Theorem 2.6 (second part)**: every simple module over `∏ᵢ Mat_{dᵢ}(k)` is isomorphic to
one of the standard modules `k^{dᵢ}`. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem exists_linearEquiv_stdModule [∀ i, NeZero (d i)] :
    ∃ i, Nonempty (S ≃ₗ[MatProd k d] StdModule k d i) := by
  have := IsSimpleModule.nontrivial (MatProd k d) S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨i, j, ht⟩ : ∃ i j, (unitMat (k := k) (d := d) i j) • s ≠ 0 := by
    by_contra h
    push Not at h
    apply hs
    calc s = (1 : MatProd k d) • s := (one_smul _ s).symm
      _ = 0 := by
        rw [← sum_unitMat, Finset.sum_smul]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_eq_zero fun j _ => h i j
  let t : S := unitMat (k := k) (d := d) i j • s
  let f : StdModule k d i →ₗ[MatProd k d] S :=
    { toFun := fun v => colMat i j v • t
      map_add' := fun v w => by rw [colMat_add, add_smul]
      map_smul' := fun b v => by
        simp only [colMat_smul, mul_smul, RingHom.id_apply] }
  have hf : f ≠ 0 := by
    intro h0
    apply ht
    have := LinearMap.congr_fun h0 (show StdModule k d i from Pi.single j 1)
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, colMat_single_one, LinearMap.zero_apply, t] at this
    rwa [← mul_smul, unitMat_mul_self] at this
  have := isSimpleModule_stdModule (k := k) (d := d) i
  have hb := LinearMap.bijective_of_ne_zero hf
  exact ⟨i, ⟨(LinearEquiv.ofBijective f hb).symm⟩⟩

/-- **Etingof et al., Theorem 2.6 (uniqueness)**: the standard modules for distinct factors are not isomorphic. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem isEmpty_linearEquiv_stdModule [∀ i, NeZero (d i)] {i j : ι} (hij : i ≠ j) :
    IsEmpty (StdModule k d i ≃ₗ[MatProd k d] StdModule k d j) := by
  refine ⟨fun φ => ?_⟩
  have : Nonempty (Fin (d i)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  have : Nonempty (Fin (d j)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  let v : StdModule k d i := Pi.single (Classical.arbitrary _) 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun (show (Pi.single (Classical.arbitrary (Fin (d i))) (1 : k) : Fin (d i) → k) = 0 from h)
      (Classical.arbitrary _)
    have h3 : (Pi.single (Classical.arbitrary (Fin (d i))) (1 : k) : Fin (d i) → k)
        (Classical.arbitrary _) = 1 := Pi.single_eq_same _ _
    exact one_ne_zero (h3.symm.trans h0)
  have h1 : (Pi.single i 1 : MatProd k d) • v = v := by
    rw [MatProd_smul_def, Pi.single_eq_same, Matrix.one_mulVec]
  have h2 : (Pi.single i 1 : MatProd k d) • φ v = 0 := by
    rw [MatProd_smul_def, Pi.single_eq_of_ne hij.symm]
    exact Matrix.zero_mulVec _
  have := φ.map_smul (Pi.single i 1 : MatProd k d) v
  rw [h1] at this
  rw [h2] at this
  exact hv (φ.injective (by simpa using this))

/-- **Etingof et al., Theorem 2.6 (third part)**: every finitely generated module over `∏ᵢ Mat_{dᵢ}(k)` is a
finite direct sum of standard modules. -/
@[kb "etingof2011" "Theorem 2.6, p. 24"]
theorem exists_linearEquiv_pi_stdModule [∀ i, NeZero (d i)] (M : Type*) [AddCommGroup M]
    [Module (MatProd k d) M] [Module.Finite (MatProd k d) M] :
    ∃ (n : ℕ) (c : Fin n → ι), Nonempty (M ≃ₗ[MatProd k d] ∀ j, StdModule k d (c j)) := by
  classical
  have : IsSemisimpleRing (MatProd k d) := inferInstance
  obtain ⟨n, S, e, hS⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MatProd k d) M
  have hc : ∀ j, ∃ i, Nonempty (S j ≃ₗ[MatProd k d] StdModule k d i) := fun j =>
    exists_linearEquiv_stdModule
  choose c hc using hc
  refine ⟨n, c, ⟨e.trans ((DFinsupp.mapRange.linearEquiv fun j => (hc j).some).trans
    DFinsupp.linearEquivFunOnFintype)⟩⟩

end

end UndergradKB.RepresentationTheory
