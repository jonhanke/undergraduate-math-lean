import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RepresentationTheory.Irreducible
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PeterWeylBasics
import UndergradKB.RepresentationTheory.AlgebrasChapter2

/-! # The Peter-Weyl theorem for `GL_N(ℂ)` (Etingof et al., Theorem 4.66 (ii))

For each highest weight `λ` (a non-increasing sequence of `N` integers, `HighestWeights N`) fix a model `L_λ` of the
irreducible rational representation with that highest weight (`Lrep λ`, chosen among the `L_ν ⊗ det^a`).  The matrix
coefficients `A ↦ (x ↦ tr(A ρ_λ(x)))`, `A ∈ End(L_λ) ≅ L_λ^* ⊗ L_λ`, assemble to a linear map
`peterWeylMap : ⨁_λ End(L_λ) → (GL_N(ℂ) → ℂ)` which

* is injective (`peterWeylMap_injective`: the `L_λ` are simple and pairwise non-isomorphic, so the group algebra maps
  onto `∏ End(L_λ)` by the density theorem),
* has image exactly the algebra `R` of rational functions on `GL_N(ℂ)` (`range_peterWeylMap`: every rational
  function lies in a finite-dimensional right-invariant subspace, which decomposes into `L_λ`'s),
* intertwines `(g, h) · A = ρ_λ(h) A ρ_λ(g)⁻¹` with `(g, h) · φ = (x ↦ φ(g⁻¹ x h))` (`matCoeff_act`).

`peterWeyl`: `R ≅ ⨁_λ L_λ^* ⊗ L_λ` as a linear isomorphism compatible with the actions of `GL_N(ℂ) × GL_N(ℂ)`.
-/

namespace UndergradKB.RepresentationTheory

open scoped TensorProduct DirectSum

variable {N : ℕ}

section Models

variable (N) in
/-- Highest weights for `GL_N`: non-increasing sequences of `N` integers. -/
abbrev HighestWeights : Type := {lam : Fin N → ℤ // Antitone lam}

theorem exists_hwData (lam : HighestWeights N) :
    ∃ p : (Σ n : ℕ, DiagramsOfSize n) × ℤ, p.1.2.1.colLen 0 ≤ N ∧ highestWeight N p.1.2 p.2 = lam.1 := by
  obtain ⟨n, ν, a, h1, h2⟩ := exists_highestWeight_eq lam.1 lam.2
  exact ⟨⟨⟨n, ν⟩, a⟩, h1, h2⟩

/-- The chosen data `(ν, a)` with `L_λ = L_ν ⊗ det^a`. -/
noncomputable def hwData (lam : HighestWeights N) : (Σ n : ℕ, DiagramsOfSize n) × ℤ := (exists_hwData lam).choose

theorem hwData_colLen (lam : HighestWeights N) : (hwData lam).1.2.1.colLen 0 ≤ N :=
  (exists_hwData lam).choose_spec.1

theorem hwData_highestWeight (lam : HighestWeights N) :
    highestWeight N (hwData lam).1.2 (hwData lam).2 = lam.1 :=
  (exists_hwData lam).choose_spec.2

/-- The space of the model `L_λ`. -/
abbrev LCarrier (lam : HighestWeights N) : Type :=
  (spechtModule (hwData lam).1.2 →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin (hwData lam).1.1))]
    tensorPowerModule (Fin N → ℂ) (hwData lam).1.1) ⊗[ℂ] ℂ

/-- The model `L_λ` of the irreducible rational representation of highest weight `λ`. -/
noncomputable abbrev Lrep (lam : HighestWeights N) : Representation ℂ (GL (Fin N) ℂ) (LCarrier lam) :=
  glIrrep (N := N) (hwData lam).1.2 (hwData lam).2

theorem isIrredRep_Lrep (lam : HighestWeights N) : IsIrredRep (Lrep lam) :=
  isIrredRep_glIrrep _ (hwData_colLen lam) _

theorem isRationalRep_Lrep (lam : HighestWeights N) : IsRationalRep (Lrep lam) :=
  isRationalRep_glIrrep _ _

/-- Every `L_ν ⊗ det^a` is isomorphic to the chosen model of its highest weight. -/
theorem nonempty_equiv_Lrep {n : ℕ} (ν : DiagramsOfSize n) (hν : ν.1.colLen 0 ≤ N) (a : ℤ) :
    Nonempty (Representation.Equiv (glIrrep (N := N) ν a)
      (Lrep (⟨highestWeight N ν a, highestWeight_antitone ν a⟩ : HighestWeights N))) := by
  rw [glIrrep_equiv_iff ν _ hν (hwData_colLen _) a _, hwData_highestWeight]

/-- Different highest weights give non-isomorphic models. -/
theorem eq_of_equiv_Lrep {lam mu : HighestWeights N} (e : Representation.Equiv (Lrep lam) (Lrep mu)) :
    lam = mu := by
  have := (glIrrep_equiv_iff _ _ (hwData_colLen lam) (hwData_colLen mu) _ _).1 ⟨e⟩
  rw [hwData_highestWeight, hwData_highestWeight] at this
  exact Subtype.ext this

end Models

section MatCoeff

/-- Matrix coefficients of `L_λ`: `A ↦ (x ↦ tr(A ρ_λ(x)))`. -/
noncomputable def matCoeff (lam : HighestWeights N) : Module.End ℂ (LCarrier lam) →ₗ[ℂ] (GL (Fin N) ℂ → ℂ) where
  toFun A x := LinearMap.trace ℂ _ (A * Lrep lam x)
  map_add' A B := by funext x; simp [add_mul]
  map_smul' c A := by funext x; simp

theorem matCoeff_apply (lam : HighestWeights N) (A : Module.End ℂ (LCarrier lam)) (x : GL (Fin N) ℂ) :
    matCoeff lam A x = LinearMap.trace ℂ _ (A * Lrep lam x) := rfl

/-- The matrix coefficient of the rank-one operator `w ↦ f(w) v` is `x ↦ f(ρ_λ(x) v)`. -/
theorem matCoeff_smulRight (lam : HighestWeights N) (f : Module.Dual ℂ (LCarrier lam)) (v : LCarrier lam)
    (x : GL (Fin N) ℂ) : matCoeff lam (f.smulRight v) x = f (Lrep lam x v) := by
  rw [matCoeff_apply]
  have : f.smulRight v * Lrep lam x = (f ∘ₗ Lrep lam x).smulRight v := by
    ext w
    simp
  rw [this, LinearMap.trace_smulRight]
  rfl

/-- **Equivariance.**  `(g, h)` acts on `End(L_λ)` by `A ↦ ρ(h) A ρ(g)⁻¹` and on functions by
`φ ↦ (x ↦ φ(g⁻¹ x h))`. -/
theorem matCoeff_act (lam : HighestWeights N) (g h : GL (Fin N) ℂ) (A : Module.End ℂ (LCarrier lam))
    (x : GL (Fin N) ℂ) :
    matCoeff lam (Lrep lam h * A * Lrep lam g⁻¹) x = matCoeff lam A (g⁻¹ * x * h) := by
  simp only [matCoeff_apply, map_mul]
  rw [show Lrep lam h * A * Lrep lam g⁻¹ * Lrep lam x = Lrep lam h * (A * Lrep lam g⁻¹ * Lrep lam x) by
    simp only [mul_assoc], LinearMap.trace_mul_comm]
  simp only [mul_assoc]

theorem matCoeff_mem (lam : HighestWeights N) (A : Module.End ℂ (LCarrier lam)) :
    matCoeff lam A ∈ ratFunctions N ℂ := by
  classical
  let b := Module.finBasis ℂ (LCarrier lam)
  have : matCoeff lam A = ∑ i, fun x => (b.coord i ∘ₗ A) (Lrep lam x (b i)) := by
    funext x
    rw [matCoeff_apply, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [LinearMap.toMatrix_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun i _ => isRationalRep_Lrep lam (b i) _

end MatCoeff

section Map

/-- The Peter-Weyl map `⨁_λ End(L_λ) → (GL_N(ℂ) → ℂ)`. -/
noncomputable def peterWeylMap : (⨁ lam : HighestWeights N, Module.End ℂ (LCarrier lam)) →ₗ[ℂ]
    (GL (Fin N) ℂ → ℂ) :=
  DirectSum.toModule ℂ _ _ matCoeff

theorem peterWeylMap_lof (lam : HighestWeights N) (A : Module.End ℂ (LCarrier lam)) :
    peterWeylMap (DirectSum.lof ℂ _ (fun lam => Module.End ℂ (LCarrier lam)) lam A) = matCoeff lam A :=
  DirectSum.toModule_lof _ _ _

theorem range_peterWeylMap_le : LinearMap.range (peterWeylMap (N := N)) ≤ (ratFunctions N ℂ).toSubmodule := by
  rintro _ ⟨A, rfl⟩
  induction A using DirectSum.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | of lam A => rw [← DirectSum.lof_eq_of ℂ, peterWeylMap_lof]; exact matCoeff_mem lam A
  | add A B hA hB => rw [map_add]; exact Submodule.add_mem _ hA hB

theorem matCoeff_mem_range (lam : HighestWeights N) (A : Module.End ℂ (LCarrier lam)) :
    matCoeff lam A ∈ LinearMap.range (peterWeylMap (N := N)) :=
  ⟨_, peterWeylMap_lof lam A⟩

end Map

section Surjective

/-- A function in a finite-dimensional right-invariant space of rational functions is a sum of matrix coefficients. -/
theorem le_range_peterWeylMap (Y : Submodule ℂ (GL (Fin N) ℂ → ℂ)) [FiniteDimensional ℂ Y]
    (hY : ∀ h, ∀ φ ∈ Y, rightTr h φ ∈ Y) (hYR : Y ≤ (ratFunctions N ℂ).toSubmodule) :
    Y ≤ LinearMap.range (peterWeylMap (N := N)) := by
  classical
  have hrat := isRationalRep_rightRegRep Y hY hYR
  obtain ⟨s, hinv, hint, hiso⟩ := hrat.exists_isInternal_glIrrep
  -- each summand consists of matrix coefficients
  have hU : ∀ U (hU : U ∈ s), ∀ u ∈ U, ((u : Y) : GL (Fin N) ℂ → ℂ) ∈ LinearMap.range (peterWeylMap (N := N)) := by
    intro U hUs u hu
    obtain ⟨n, ν, a, hν, ⟨e⟩⟩ := hiso U hUs
    obtain ⟨e'⟩ := nonempty_equiv_Lrep (N := N) ν hν a
    let E := e.trans e'
    let lam : HighestWeights N := ⟨highestWeight N ν a, highestWeight_antitone ν a⟩
    -- evaluation at the identity on `U`
    let ev : Module.Dual ℂ U :=
      { toFun := fun w => ((w : Y) : GL (Fin N) ℂ → ℂ) 1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let f : Module.Dual ℂ (LCarrier lam) := ev ∘ₗ E.toLinearEquiv.symm.toLinearMap
    have key : ((u : Y) : GL (Fin N) ℂ → ℂ) = matCoeff lam (f.smulRight (E.toLinearEquiv ⟨u, hu⟩)) := by
      funext x
      rw [matCoeff_smulRight]
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← equiv_apply_rep' E, LinearEquiv.symm_apply_apply]
      show (u : GL (Fin N) ℂ → ℂ) x = (u : GL (Fin N) ℂ → ℂ) (1 * x)
      rw [one_mul]
    rw [key]
    exact matCoeff_mem_range lam _
  intro φ hφ
  have hsum := hint.submodule_iSup_eq_top
  have hmem : (⟨φ, hφ⟩ : Y) ∈ ⨆ U : s, (U : Submodule ℂ Y) := by rw [hsum]; trivial
  have hle : (⨆ U : s, (U : Submodule ℂ Y)) ≤
      (LinearMap.range (peterWeylMap (N := N))).comap Y.subtype :=
    iSup_le fun U u hu => hU U U.2 u hu
  exact hle hmem

/-- **Etingof et al., Theorem 4.66 (ii), image.**  The matrix coefficients of the `L_λ` span exactly the rational
functions on `GL_N(ℂ)`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem range_peterWeylMap : LinearMap.range (peterWeylMap (N := N)) = (ratFunctions N ℂ).toSubmodule := by
  refine le_antisymm range_peterWeylMap_le fun φ hφ => ?_
  obtain ⟨m, D, hD⟩ := mem_sum_homogRatSpace hφ
  have : (⨆ d ∈ Finset.range D, homogRatSpace N d m) ≤ LinearMap.range (peterWeylMap (N := N)) :=
    iSup₂_le fun d _ => le_range_peterWeylMap _ (fun h φ hφ => homogRatSpace_rightTr d m h hφ)
      (homogRatSpace_le d m)
  exact this hD

end Surjective

section GroupDensity

variable {G : Type*} [Group G]

/-- The representation space viewed as a module over the group algebra (a type synonym with the instances of `W`). -/
def RepMod {W : Type*} [AddCommGroup W] [Module ℂ W] (_ : Representation ℂ G W) : Type _ := W

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W)

instance : AddCommGroup (RepMod ρ) := inferInstanceAs (AddCommGroup W)

instance : Module ℂ (RepMod ρ) := inferInstanceAs (Module ℂ W)

noncomputable instance : Module (MonoidAlgebra ℂ G) (RepMod ρ) where
  smul a v := (ρ.asAlgebraHom a : W →ₗ[ℂ] W) (show W from v)
  one_smul v := by
    show (ρ.asAlgebraHom 1 : W →ₗ[ℂ] W) (show W from v) = v
    rw [map_one]; rfl
  mul_smul a b v := by
    show (ρ.asAlgebraHom (a * b) : W →ₗ[ℂ] W) (show W from v) =
      (ρ.asAlgebraHom a : W →ₗ[ℂ] W) ((ρ.asAlgebraHom b : W →ₗ[ℂ] W) (show W from v))
    rw [map_mul]; rfl
  smul_zero a := map_zero (ρ.asAlgebraHom a : W →ₗ[ℂ] W)
  smul_add a v w := map_add (ρ.asAlgebraHom a : W →ₗ[ℂ] W) (show W from v) (show W from w)
  add_smul a b v := by
    show (ρ.asAlgebraHom (a + b) : W →ₗ[ℂ] W) (show W from v) =
      (ρ.asAlgebraHom a : W →ₗ[ℂ] W) (show W from v) + (ρ.asAlgebraHom b : W →ₗ[ℂ] W) (show W from v)
    rw [map_add]; rfl
  zero_smul v := by
    show (ρ.asAlgebraHom 0 : W →ₗ[ℂ] W) (show W from v) = 0
    rw [map_zero]; rfl

theorem RepMod.smul_def (a : MonoidAlgebra ℂ G) (v : RepMod ρ) :
    a • v = (ρ.asAlgebraHom a : W →ₗ[ℂ] W) (show W from v) := rfl

instance : IsScalarTower ℂ (MonoidAlgebra ℂ G) (RepMod ρ) :=
  ⟨fun c a v => by
    show (ρ.asAlgebraHom (c • a) : W →ₗ[ℂ] W) (show W from v) =
      c • (ρ.asAlgebraHom a : W →ₗ[ℂ] W) (show W from v)
    rw [map_smul]
    rfl⟩

instance [FiniteDimensional ℂ W] : FiniteDimensional ℂ (RepMod ρ) := inferInstanceAs (FiniteDimensional ℂ W)

theorem RepMod.of_smul (g : G) (v : RepMod ρ) :
    MonoidAlgebra.of ℂ G g • v = (ρ g : W →ₗ[ℂ] W) (show W from v) := by
  rw [RepMod.smul_def, Representation.asAlgebraHom_of]

theorem isSimpleModule_repMod (h : IsIrredRep ρ) : IsSimpleModule (MonoidAlgebra ℂ G) (RepMod ρ) := by
  obtain ⟨hn, hU⟩ := h
  have : Nontrivial (RepMod ρ) := hn
  refine { toNontrivial := (Submodule.nontrivial_iff _).2 this, eq_bot_or_eq_top := fun S => ?_ }
  have h1 : ∀ g, ∀ w ∈ (S.restrictScalars ℂ : Submodule ℂ W), ρ g w ∈ (S.restrictScalars ℂ : Submodule ℂ W) := by
    intro g w hw
    have := S.smul_mem (MonoidAlgebra.of ℂ G g) hw
    rwa [RepMod.of_smul] at this
  rcases hU _ h1 with h | h
  · left
    apply Submodule.restrictScalars_injective ℂ (MonoidAlgebra ℂ G) (RepMod ρ)
    rw [Submodule.restrictScalars_bot]
    exact h
  · right
    apply Submodule.restrictScalars_injective ℂ (MonoidAlgebra ℂ G) (RepMod ρ)
    rw [Submodule.restrictScalars_top]
    exact h

/-- **Density for groups.**  For finitely many irreducible, pairwise non-isomorphic, finite-dimensional complex
representations, the group algebra maps onto the product of their endomorphism algebras. -/
theorem exists_asAlgebraHom_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (hirr : ∀ i, IsIrredRep (ρ i))
    (hne : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (ρ i) (ρ j))) (T : ∀ i, Module.End ℂ (V i)) :
    ∃ a : MonoidAlgebra ℂ G, ∀ i, (ρ i).asAlgebraHom a = T i := by
  have hs : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (RepMod (ρ i)) := fun i => isSimpleModule_repMod _ (hirr i)
  have hV : ∀ i j, i ≠ j → IsEmpty (RepMod (ρ i) ≃ₗ[MonoidAlgebra ℂ G] RepMod (ρ j)) := by
    intro i j hij
    refine ⟨fun e => (hne i j hij).false ?_⟩
    refine Representation.Equiv.mk (e.restrictScalars ℂ) fun g => LinearMap.ext fun v => ?_
    have := e.map_smul (MonoidAlgebra.of ℂ G g) (show RepMod (ρ i) from v)
    rw [RepMod.of_smul, RepMod.of_smul] at this
    exact this
  obtain ⟨a, ha⟩ := density_pi_surjective (k := ℂ) (A := MonoidAlgebra ℂ G) (V := fun i => RepMod (ρ i)) hV T
  refine ⟨a, fun i => LinearMap.ext fun v => ?_⟩
  have := LinearMap.congr_fun (congrFun ha i) (show RepMod (ρ i) from v)
  exact this

end GroupDensity

section Injective

/-- The trace pairing is nondegenerate. -/
theorem eq_zero_of_trace_mul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (h : ∀ T : Module.End ℂ V, LinearMap.trace ℂ V (A * T) = 0) : A = 0 := by
  refine LinearMap.ext fun v => (Module.forall_dual_apply_eq_zero_iff ℂ (A v)).1 fun f => ?_
  have := h (f.smulRight v)
  have e : A * f.smulRight v = f.smulRight (A v) := by ext w; simp
  rw [e, LinearMap.trace_smulRight] at this
  exact this

theorem eq_zero_of_peterWeylMap_eq_zero (A : ⨁ lam : HighestWeights N, Module.End ℂ (LCarrier lam))
    (hA : peterWeylMap A = 0) : A = 0 := by
  classical
  let F := A.support
  have hsumA : ∀ x : GL (Fin N) ℂ, ∑ i ∈ F, matCoeff i (A i) x = 0 := by
    intro x
    have h0 := congrFun hA x
    rw [← DirectSum.sum_support_of A, map_sum] at h0
    simp only [← DirectSum.lof_eq_of ℂ, peterWeylMap_lof, Finset.sum_apply] at h0
    exact h0
  have hlin : ∀ a : MonoidAlgebra ℂ (GL (Fin N) ℂ),
      ∑ i : F, LinearMap.trace ℂ (LCarrier i.1) (A i.1 * (Lrep i.1).asAlgebraHom a) = 0 := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [← hsumA g, ← Finset.sum_attach F]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Representation.asAlgebraHom_of]
      rfl
    | add a b ha hb =>
      rw [← add_zero (0 : ℂ)]
      nth_rewrite 1 [← ha]
      rw [← hb, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, mul_add, map_add]
    | smul c a ha =>
      rw [← smul_zero c, ← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, mul_smul_comm, map_smul]
  have hirr : ∀ i : F, IsIrredRep (Lrep i.1) := fun i => isIrredRep_Lrep i.1
  have hne : ∀ i j : F, i ≠ j → IsEmpty (Representation.Equiv (Lrep i.1) (Lrep j.1)) :=
    fun i j hij => ⟨fun e => hij (Subtype.ext (eq_of_equiv_Lrep e))⟩
  refine DFinsupp.ext fun lam => ?_
  by_cases hlam : lam ∈ F
  swap
  · exact DFinsupp.notMem_support_iff.1 hlam
  let i0 : F := ⟨lam, hlam⟩
  have key : ∀ T : Module.End ℂ (LCarrier lam), LinearMap.trace ℂ (LCarrier lam) (A lam * T) = 0 := by
    intro T
    obtain ⟨a, ha⟩ := exists_asAlgebraHom_eq (fun i : F => Lrep i.1) hirr hne
      (Pi.single (M := fun i : F => Module.End ℂ (LCarrier i.1)) i0 T)
    have h := hlin a
    rw [Finset.sum_eq_single i0] at h
    · rw [ha i0, Pi.single_eq_same] at h
      exact h
    · intro j _ hj
      have hj' : (Lrep j.1).asAlgebraHom a = 0 := by
        rw [ha j]
        simp [hj]
      simp [hj']
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  exact eq_zero_of_trace_mul_eq_zero (A lam) key

/-- **Etingof et al., Theorem 4.66 (ii), injectivity.**  Matrix coefficients of pairwise different `L_λ` are
linearly independent. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem peterWeylMap_injective : Function.Injective (peterWeylMap (N := N)) := by
  letI : AddCommGroup (⨁ lam : HighestWeights N, Module.End ℂ (LCarrier lam)) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro A B hAB
  have h := eq_zero_of_peterWeylMap_eq_zero (A - B) (by rw [map_sub, hAB, sub_self])
  exact sub_eq_zero.1 h

end Injective

section Main

/-- **Etingof et al., Theorem 4.66 (ii) (the Peter-Weyl theorem for `GL(V)`).**  The algebra `R` of rational
functions on `GL_N(ℂ)` (polynomials in the matrix entries and `1 / det`) is isomorphic to `⨁_λ L_λ^* ⊗ L_λ`, the sum
over all highest weights `λ`, by `f ⊗ v ↦ (x ↦ f(ρ_λ(x) v))`; this isomorphism intertwines `(g, h) · φ =
(x ↦ φ(g⁻¹ x h))` on `R` with `ρ_λ^*(g) ⊗ ρ_λ(h)` on `L_λ^* ⊗ L_λ` (`matCoeff_act`, `peterWeyl_apply_tmul`). -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
noncomputable def peterWeyl :
    (⨁ lam : HighestWeights N, Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) ≃ₗ[ℂ]
      (ratFunctions N ℂ).toSubmodule :=
  (DFinsupp.mapRange.linearEquiv fun lam => dualTensorHomEquiv ℂ (LCarrier lam) (LCarrier lam)).trans
    ((LinearEquiv.ofInjective _ peterWeylMap_injective).trans (LinearEquiv.ofEq _ _ range_peterWeylMap))

theorem peterWeyl_apply_tmul (lam : HighestWeights N) (f : Module.Dual ℂ (LCarrier lam)) (v : LCarrier lam)
    (x : GL (Fin N) ℂ) :
    (peterWeyl (DirectSum.lof ℂ _ (fun lam => Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) lam (f ⊗ₜ v)) :
      GL (Fin N) ℂ → ℂ) x = f (Lrep lam x v) := by
  have h1 : (DFinsupp.mapRange.linearEquiv fun lam => dualTensorHomEquiv ℂ (LCarrier lam) (LCarrier lam))
      (DirectSum.lof ℂ _ (fun lam => Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) lam (f ⊗ₜ v)) =
      DirectSum.lof ℂ _ (fun lam => Module.End ℂ (LCarrier lam)) lam (f.smulRight v) := by
    rw [DFinsupp.mapRange.linearEquiv_apply]
    show DFinsupp.mapRange _ _ (DFinsupp.single lam (f ⊗ₜ[ℂ] v) :
      Π₀ lam, Module.Dual ℂ (LCarrier lam) ⊗[ℂ] LCarrier lam) = DFinsupp.single lam _
    rw [DFinsupp.mapRange_single]
    congr 1
  simp only [peterWeyl, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]
  rw [h1, peterWeylMap_lof, matCoeff_smulRight]

end Main

end UndergradKB.RepresentationTheory
