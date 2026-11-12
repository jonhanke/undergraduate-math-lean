import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Trace
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.AlgebraCharacters

/-! # Density theorem and the radical of a finite-dimensional algebra (Etingof et al., §2.3-2.5)

For a finite-dimensional simple module `V` over an algebra `A` over an algebraically closed field `k`, the action
map `A → End_k V` is surjective (density theorem); consequently any prescribed images of linearly independent
vectors can be realised by a single algebra element.  The radical of `A` is the set of elements acting by zero on
every simple module; we identify it with Mathlib's `Ring.jacobson A`, and show it is a two-sided nilpotent ideal
containing every nilpotent two-sided ideal.
-/

namespace UndergradKB.RepresentationTheory

open Module

section Density

variable {k A V : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [AddCommGroup V] [Module A V]
  [Module k V] [IsScalarTower k A V] [IsSimpleModule A V] [FiniteDimensional k V]

/-- **Etingof et al., Theorem 2.5 (density theorem)**: for a finite-dimensional simple module `V` over an
algebraically closed field, the action map `A → End_k V` is surjective. -/
@[kb "etingof2011" "Theorem 2.5, p. 24"]
theorem density_surjective : Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] Module.End k V) := by
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) k
  have : Module.Finite (Module.End A V) V := by
    have : Module.Finite k V := inferInstance
    exact Module.Finite.of_restrictScalars_finite k (Module.End A V) V
  intro f
  have hf : ∀ (e : Module.End A V) (v : V), f (e • v) = e • f v := by
    intro e v
    obtain ⟨c, rfl⟩ := hb.2 e
    simp
  let f' : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun e v => hf e v }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) f'
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  have := congrArg (fun g : Module.End (Module.End A V) V => g v) ha
  simpa [f'] using this

/-- **Etingof et al., Corollary 2.4**: for a finite-dimensional simple module `V`, linearly independent vectors
`v₁, …, vₙ` and arbitrary vectors `w₁, …, wₙ`, there is a single `a ∈ A` with `a vᵢ = wᵢ`. -/
@[kb "etingof2011" "Corollary 2.4, p. 24"]
theorem exists_smul_eq_of_linearIndependent {ι : Type*} [Finite ι] (v : ι → V)
    (hv : LinearIndependent k v) (w : ι → V) : ∃ a : A, ∀ i, a • v i = w i := by
  classical
  let b := Module.Basis.span hv
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (b.constr k w)
  obtain ⟨a, ha⟩ := density_surjective (k := k) (A := A) (V := V) g
  refine ⟨a, fun i => ?_⟩
  have h1 : g (v i) = w i := by
    have := congrArg (fun h => h (b i)) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.constr_basis] at this
    simpa [b, Module.Basis.span_apply] using this
  rw [← h1, ← ha]
  rfl

end Density

section DensityProduct

variable {k A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module k (V i)]
  [∀ i, IsScalarTower k A (V i)] [∀ i, IsSimpleModule A (V i)] [∀ i, FiniteDimensional k (V i)]

/-- **Etingof et al., Theorem 2.5 (second part)**: for pairwise non-isomorphic finite-dimensional simple
modules `V₁, …, Vₙ` over an algebraically closed field, the action map `A → ∏ End_k Vᵢ` is surjective. -/
@[kb "etingof2011" "Theorem 2.5, p. 24"]
theorem density_pi_surjective (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Function.Surjective (fun a : A => fun i => (Algebra.lsmul k k (V i) a : Module.End k (V i))) := by
  classical
  intro g
  have hb := fun i => IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V i) k
  -- every `A`-endomorphism of the product acts by a scalar on each factor
  have key : ∀ e : Module.End A (∀ i, V i), ∀ i, ∃ c : k, ∀ v : ∀ i, V i, e v i = c • v i := by
    intro e i
    let φ : ∀ j, V j →ₗ[A] V i := fun j =>
      (LinearMap.proj i : (∀ i, V i) →ₗ[A] V i) ∘ₗ e ∘ₗ LinearMap.single A V j
    have hφ : ∀ j, j ≠ i → φ j = 0 := by
      intro j hji
      rcases LinearMap.bijective_or_eq_zero (φ j) with h | h
      · exact ((hV j i hji).false (LinearEquiv.ofBijective _ h)).elim
      · exact h
    obtain ⟨c, hc⟩ := (hb i).2 (φ i)
    refine ⟨c, fun v => ?_⟩
    have hv : v = ∑ j, Pi.single j (v j) := (Finset.univ_sum_single v).symm
    have : e v i = ∑ j, φ j (v j) := by
      conv_lhs => rw [hv]
      simp [φ, map_sum]
    rw [this, Finset.sum_eq_single i (fun j _ hj => by simp [hφ j hj]) (by simp)]
    have := congrArg (fun h => h (v i)) hc
    simpa using this.symm
  let F : Module.End k (∀ i, V i) := LinearMap.pi fun i => g i ∘ₗ LinearMap.proj i
  have hF : ∀ (e : Module.End A (∀ i, V i)) (v : ∀ i, V i), F (e • v) = e • F v := by
    intro e v
    funext i
    obtain ⟨c, hc⟩ := key e i
    simp only [Module.End.smul_def, F, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      hc, map_smul]
  have : Module.Finite (Module.End A (∀ i, V i)) (∀ i, V i) :=
    Module.Finite.of_restrictScalars_finite k (Module.End A (∀ i, V i)) (∀ i, V i)
  let F' : Module.End (Module.End A (∀ i, V i)) (∀ i, V i) :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := fun e v => hF e v }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := ∀ i, V i) F'
  refine ⟨a, funext fun i => LinearMap.ext fun w => ?_⟩
  have := congrArg (fun h => h (Pi.single i w) i) ha
  simpa [F', F] using this

/-- **Etingof et al., Corollary 2.13**: for pairwise non-isomorphic finite-dimensional simple modules
`V₁, …, Vₙ` over an algebraically closed field, `∑ (dim Vᵢ)² ≤ dim A`. -/
@[kb "etingof2011" "Corollary 2.13, p. 26"]
theorem sum_finrank_sq_le_finrank [FiniteDimensional k A] (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    ∑ i, Module.finrank k (V i) ^ 2 ≤ Module.finrank k A := by
  let f : A →ₗ[k] ∀ i, Module.End k (V i) :=
    LinearMap.pi fun i => (Algebra.lsmul k k (V i) : A →ₐ[k] Module.End k (V i)).toLinearMap
  have hs : Function.Surjective f := density_pi_surjective hV
  have := LinearMap.finrank_le_finrank_of_surjective hs
  rw [Module.finrank_pi_fintype] at this
  simpa [Module.finrank_linearMap, sq] using this

/-- **Etingof et al., Theorem 2.17 (first part)**: the characters of pairwise non-isomorphic finite-dimensional
simple modules over an algebraically closed field are linearly independent. -/
@[kb "etingof2011" "Theorem 2.17, p. 27"]
theorem linearIndependent_algebraCharacter (hV : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    LinearIndependent k (fun i => algebraCharacter k (A := A) (V := V i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have : Nontrivial (V j) := IsSimpleModule.nontrivial A (V j)
  obtain ⟨v, hv⟩ := exists_ne (0 : V j)
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hv
  obtain ⟨a, ha⟩ := density_pi_surjective (k := k) (A := A) hV
    (Pi.single j (l.smulRight v : Module.End k (V j)))
  have ht : ∀ i, algebraCharacter k (V := V i) a = if i = j then 1 else 0 := by
    intro i
    rw [algebraCharacter_apply]
    have := congr_fun ha i
    simp only at this
    rw [this]
    by_cases h : i = j
    · subst h
      simp [LinearMap.trace_smulRight, hl]
    · simp [h]
  have := congrArg (fun φ => φ a) hc
  simpa [LinearMap.sum_apply, ht] using this

end DensityProduct

section Radical

universe u

variable (A : Type u) [Ring A]

/-- **Etingof et al., Definition 2.9**: the radical of an algebra, the left ideal of elements acting by zero on
every simple module (simple modules of a finite-dimensional algebra live in the same universe as `A`, being
quotients of `A`). -/
@[kb "etingof2011" "Definition 2.9, p. 26"]
def algebraRadical : Ideal A :=
  sInf {I : Ideal A | ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module A V) (_ : IsSimpleModule A V),
    I = Module.annihilator A V}

theorem mem_algebraRadical_iff {a : A} :
    a ∈ algebraRadical A ↔ ∀ (V : Type u) [AddCommGroup V] [Module A V] [IsSimpleModule A V],
      ∀ v : V, a • v = 0 := by
  rw [algebraRadical, Submodule.mem_sInf]
  constructor
  · intro h V _ _ _ v
    exact Module.mem_annihilator.mp (h _ ⟨V, inferInstance, inferInstance, inferInstance, rfl⟩) v
  · rintro h I ⟨V, _, _, _, rfl⟩
    exact Module.mem_annihilator.mpr (h V)

/-- **Etingof et al., Definition 2.9 / Proposition 2.10**: the radical (elements killing all simple modules)
is Mathlib's Jacobson radical of the ring. -/
@[kb "etingof2011" "Definition 2.9, p. 26"]
theorem algebraRadical_eq_jacobson : algebraRadical A = Ring.jacobson A := by
  ext a
  rw [mem_algebraRadical_iff]
  constructor
  · intro h
    rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
    intro m hm
    have : IsSimpleModule A (A ⧸ m) := isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hm)
    have h1 := h (A ⧸ m) (Submodule.Quotient.mk 1)
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero] at h1
    exact h1
  · intro h V _ _ _ v
    exact Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator A V h) v

/-- **Etingof et al., Proposition 2.10**: the radical is a two-sided ideal. -/
@[kb "etingof2011" "Proposition 2.10, p. 26"]
instance algebraRadical_isTwoSided : (algebraRadical A).IsTwoSided := by
  rw [algebraRadical_eq_jacobson]
  infer_instance

/-- **Etingof et al., Proposition 2.11 (i)**: every nilpotent two-sided ideal lies in the radical. -/
@[kb "etingof2011" "Proposition 2.11, p. 26"]
theorem le_algebraRadical_of_isNilpotent (I : Ideal A) [I.IsTwoSided] (hI : IsNilpotent I) :
    I ≤ algebraRadical A := by
  rw [algebraRadical_eq_jacobson]
  intro x hx
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
  intro m hm
  by_contra hxm
  have hc : IsCoatom m := Ideal.isMaximal_def.mp hm
  have htop : m ⊔ Submodule.span A {x} = ⊤ :=
    hc.2 _ (lt_of_le_of_ne le_sup_left fun h =>
      hxm (h ▸ (le_sup_right : Submodule.span A {x} ≤ m ⊔ Submodule.span A {x})
        (Submodule.mem_span_singleton_self x)))
  have h1 : (1 : A) ∈ m ⊔ Submodule.span A {x} := htop ▸ Submodule.mem_top
  obtain ⟨m0, hm0, z, hz, e⟩ := Submodule.mem_sup.mp h1
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
  obtain ⟨n, hn⟩ := hI
  have hbx : b * x ∈ I := I.smul_mem b hx
  have hnil : IsNilpotent (b * x) := ⟨n, by
    have : (b * x) ^ n ∈ I ^ n := Ideal.pow_mem_pow hbx n
    rw [hn] at this
    exact (Submodule.mem_bot A).mp this⟩
  have hu : IsUnit (1 - b * x) := hnil.isUnit_one_sub
  have : m0 = 1 - b * x := by
    rw [← e, smul_eq_mul]; abel
  rw [this] at hm0
  exact hc.1 (Ideal.eq_top_of_isUnit_mem m hm0 hu)

/-- **Etingof et al., Proposition 2.11 (ii)**: the radical of a finite-dimensional algebra is nilpotent. -/
@[kb "etingof2011" "Proposition 2.11, p. 26"]
theorem isNilpotent_algebraRadical [IsArtinianRing A] : IsNilpotent (algebraRadical A) := by
  rw [algebraRadical_eq_jacobson]
  exact IsArtinianRing.isNilpotent_jacobson A

/-- **Etingof et al., Proposition 2.11**: the radical is the largest nilpotent two-sided ideal. -/
@[kb "etingof2011" "Proposition 2.11, p. 26"]
theorem isGreatest_algebraRadical [IsArtinianRing A] :
    IsGreatest {I : Ideal A | I.IsTwoSided ∧ IsNilpotent I} (algebraRadical A) :=
  ⟨⟨inferInstance, isNilpotent_algebraRadical A⟩, fun I ⟨h2, hn⟩ =>
    have := h2; le_algebraRadical_of_isNilpotent A I hn⟩

end Radical

end UndergradKB.RepresentationTheory
