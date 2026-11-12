import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
import UndergradKB.Common.Attr

/-!
# Characters and small notions of topological group theory (Morris, Appendix 5, sections A5.3 to A5.15)

Characters of abstract abelian groups, the dual of `ℤ` and of the circle, the canonical map into
the double dual, and a number of the small definitions of Appendix 5 (monothetic, solenoidal,
maximally and minimally almost periodic, topologically simple, almost connected, characterAnnihilator,
compact element, locally `kω`, three-space property, exact sequences, `PGL(n, ℝ)`), each with
a characterisation or basic fact.
-/

open Set Filter Topology

universe u

namespace UndergradKB.Topology

/-! ### Separation of points by characters -/

/-- The inclusion of the rational circle `ℚ / ℤ` into the real circle `ℝ / ℤ`. -/
noncomputable def ratCircleToRealCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by simp⟩)

theorem ratCircleToRealCircle_injective : Function.Injective ratCircleToRealCircle := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h : ((q : ℝ) : AddCircle (1 : ℝ)) = 0 := hx
  rw [QuotientAddGroup.eq_zero_iff] at h ⊢
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
  exact ⟨k, by
    have : ((k • (1 : ℚ) : ℚ) : ℝ) = (q : ℝ) := by simpa using hk
    exact_mod_cast this⟩

/-- Morris, Topology Without Tears, Corollary A5.3.7 (TP-529), additive form. In an abelian group,
two distinct elements are separated by a homomorphism into the circle `ℝ / ℤ`. -/
@[kb "morris2024" "Corollary A5.3.7, p. 532"]
theorem exists_addMonoidHom_addCircle_apply_ne {A : Type*} [AddCommGroup A] {a b : A}
    (hab : a ≠ b) : ∃ φ : A →+ AddCircle (1 : ℝ), φ a ≠ φ b := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero (sub_ne_zero.2 hab)
  refine ⟨ratCircleToRealCircle.comp (c : A →+ AddCircle (1 : ℚ)), fun h => hc ?_⟩
  have h' : ratCircleToRealCircle (c a) = ratCircleToRealCircle (c b) := h
  have := ratCircleToRealCircle_injective h'
  have e : c (a - b) = c a - c b := map_sub c a b
  rw [e, sub_eq_zero]
  exact this

/-- Morris, Topology Without Tears, Corollary A5.3.7 (TP-529). In an abelian group `G`, two
distinct elements are separated by a homomorphism into the circle group `T`. -/
@[kb "morris2024" "Corollary A5.3.7, p. 532"]
theorem exists_monoidHom_circle_apply_ne {G : Type*} [CommGroup G] {g h : G} (hgh : g ≠ h) :
    ∃ φ : G →* Circle, φ g ≠ φ h := by
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom_addCircle_apply_ne
    (A := Additive G) (a := Additive.ofMul g) (b := Additive.ofMul h) (fun e => hgh e)
  let ψ : G →* Circle :=
    { toFun := fun x => AddCircle.toCircle (φ (Additive.ofMul x))
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [ofMul_mul, map_add]
        exact AddCircle.toCircle_add _ _ }
  refine ⟨ψ, fun e => hφ ?_⟩
  exact AddCircle.injective_toCircle one_ne_zero e

/-! ### The dual of `ℤ` and of the circle -/

/-- Morris, Topology Without Tears, Example A5.7.2 (TP-566), algebraic part. Every character of
`ℤ` (written multiplicatively as `Multiplicative ℤ`) is `n ↦ x ^ n`, where `x` is its value at `1`. -/
@[kb "morris2024" "Example A5.7.2, p. 557"]
theorem dual_int_apply (χ : PontryaginDual (Multiplicative ℤ)) (n : ℤ) :
    χ (Multiplicative.ofAdd n) = (χ (Multiplicative.ofAdd 1)) ^ n := by
  have : (Multiplicative.ofAdd n) = (Multiplicative.ofAdd (1 : ℤ)) ^ n := by
    rw [← ofAdd_zsmul]; simp
  rw [this, map_zpow]

/-- Morris, Topology Without Tears, Example A5.7.2 (TP-566). The dual group of `ℤ` is
topologically isomorphic to the circle group, via `χ ↦ χ 1`. -/
noncomputable def dualIntEquivCircle : PontryaginDual (Multiplicative ℤ) ≃ₜ* Circle where
  toFun χ := χ (Multiplicative.ofAdd 1)
  invFun z := ⟨zpowersHom Circle z, continuous_of_discreteTopology⟩
  left_inv χ := by
    apply PontryaginDual.ext
    intro n
    show (zpowersHom Circle (χ (Multiplicative.ofAdd 1))) n = χ n
    rw [zpowersHom_apply]
    have := dual_int_apply χ n.toAdd
    simpa using this.symm
  right_inv z := by
    show (zpowersHom Circle z) (Multiplicative.ofAdd 1) = z
    rw [zpowersHom_apply]; simp
  map_mul' χ ψ := rfl
  continuous_toFun := by
    have h1 : Continuous (fun χ : Multiplicative ℤ →ₜ* Circle => χ.toContinuousMap) :=
      continuous_induced_dom
    have h2 : Continuous (fun f : C(Multiplicative ℤ, Circle) => f (Multiplicative.ofAdd (1 : ℤ))) :=
      continuous_eval_const _
    exact h2.comp h1
  continuous_invFun := by
    refine ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : Circle × Multiplicative ℤ => p.1 ^ (Multiplicative.toAdd p.2))
    exact continuous_prod_of_discrete_right.2 fun n => continuous_zpow n

/-- Morris, Topology Without Tears, Example A5.7.2 (TP-566), restated. The dual group of `ℤ` is
topologically isomorphic to the circle group, the isomorphism sending a character `χ` to `χ 1`
(so the character `χ` is `n ↦ (χ 1) ^ n`). -/
@[kb "morris2024" "Example A5.7.2, p. 557"]
theorem exists_continuousMulEquiv_dual_int_circle :
    ∃ e : PontryaginDual (Multiplicative ℤ) ≃ₜ* Circle,
      ∀ χ, e χ = χ (Multiplicative.ofAdd 1) :=
  ⟨dualIntEquivCircle, fun χ => by rfl⟩

/-- Morris, Topology Without Tears, Example A5.7.3 (i) (TP-567). Every continuous character of the
circle group is `z ↦ z ^ m` for an integer `m` (proved by lifting the character through the
covering map `exp : ℝ → Circle`). -/
@[kb "morris2024" "Example A5.7.3, p. 558"]
theorem dual_circle_apply (χ : PontryaginDual Circle) :
    ∃ m : ℤ, ∀ z : Circle, χ z = z ^ m := by
  let ψ : C(ℝ, Circle) := (χ.toContinuousMap).comp Circle.exp
  have lift : ∀ (f : C(ℝ, Circle)) (e₀ : ℝ), Circle.exp e₀ = f 0 →
      ∃! F : C(ℝ, ℝ), F 0 = e₀ ∧ (Circle.exp ∘ F) = f := fun f e₀ he =>
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 e₀ he
  have hψ0 : Circle.exp 0 = ψ 0 := by
    show Circle.exp 0 = χ (Circle.exp 0)
    rw [Circle.exp_zero, map_one]
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ := lift ψ 0 hψ0
  have hFexp : ∀ t, Circle.exp (F t) = χ (Circle.exp t) := fun t => congrFun hFlift t
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s t
    let f : C(ℝ, Circle) := ⟨fun t => χ (Circle.exp s) * ψ t, by fun_prop⟩
    have hf0 : Circle.exp (F s) = f 0 := by
      show Circle.exp (F s) = χ (Circle.exp s) * χ (Circle.exp 0)
      rw [hFexp, Circle.exp_zero, map_one, mul_one]
    obtain ⟨F', -, huniq⟩ := lift f (F s) hf0
    have h1 := huniq ⟨fun t => F (s + t), by fun_prop⟩ ⟨by simp, by
      funext u
      show Circle.exp (F (s + u)) = χ (Circle.exp s) * χ (Circle.exp u)
      rw [hFexp, Circle.exp_add, map_mul]⟩
    have h2 := huniq ⟨fun t => F s + F t, by fun_prop⟩ ⟨by simp [hF0], by
      funext u
      show Circle.exp (F s + F u) = χ (Circle.exp s) * χ (Circle.exp u)
      rw [Circle.exp_add, hFexp, hFexp]⟩
    exact congrArg (fun G : C(ℝ, ℝ) => G t) (h1.trans h2.symm)
  let A : ℝ →+ ℝ := AddMonoidHom.mk' F hadd
  have hlin : ∀ t, F t = t * F 1 := by
    intro t
    have := map_real_smul A F.continuous t (1 : ℝ)
    simpa [A] using this
  have hc : ∃ n : ℤ, F 1 = n := by
    have h1 : Circle.exp (F (2 * Real.pi)) = 1 := by
      rw [hFexp, ← Circle.exp_int_mul_two_pi 1]
      simp
    rw [hlin, Circle.exp_eq_one] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : (2 * Real.pi) * F 1 = (2 * Real.pi) * n := by linarith
    exact mul_left_cancel₀ hpi this
  obtain ⟨n, hn⟩ := hc
  refine ⟨n, fun z => ?_⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [← hFexp, hlin, hn, mul_comm, Circle.exp_intCast_mul]

/-- Two integer exponents which define the same power map on the circle are equal. -/
theorem circle_zpow_injective {m m' : ℤ} (h : ∀ z : Circle, z ^ m = z ^ m') : m = m' := by
  by_contra hne
  have hd : ((m : ℝ) - m') ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast sub_eq_zero.1 h0)
  set x : ℝ := Real.pi / ((m : ℝ) - m') with hx
  have h1 := h (Circle.exp x)
  rw [← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul] at h1
  have h2 : Circle.exp (((m : ℝ) - m') * x) = 1 := by
    rw [sub_mul, Circle.exp_sub, h1, div_self']
  have h3 : ((m : ℝ) - m') * x = Real.pi := by rw [hx]; field_simp
  rw [h3] at h2
  exact Circle.exp_pi_ne_one h2

/-- The integer exponent of a character of the circle group. -/
noncomputable def circleCharacterExponent (χ : PontryaginDual Circle) : ℤ :=
  Classical.choose (dual_circle_apply χ)

theorem circleCharacterExponent_spec (χ : PontryaginDual Circle) (z : Circle) :
    χ z = z ^ circleCharacterExponent χ :=
  Classical.choose_spec (dual_circle_apply χ) z

/-- Morris, Topology Without Tears, Corollary A5.7.10 (TP-567). The dual group of the circle group
is topologically isomorphic to `ℤ` (with the discrete topology), via `χ ↦ m` where
`χ z = z ^ m`. -/
noncomputable def dualCircleEquivInt : PontryaginDual Circle ≃ₜ* Multiplicative ℤ where
  toFun χ := Multiplicative.ofAdd (circleCharacterExponent χ)
  invFun n :=
    { toMonoidHom := zpowGroupHom (Multiplicative.toAdd n)
      continuous_toFun := continuous_zpow _ }
  left_inv χ := by
    apply PontryaginDual.ext
    intro z
    show z ^ (circleCharacterExponent χ) = χ z
    exact (circleCharacterExponent_spec χ z).symm
  right_inv n := by
    apply Multiplicative.toAdd.injective
    apply circle_zpow_injective
    intro z
    show z ^ (circleCharacterExponent
      ({ toMonoidHom := zpowGroupHom (Multiplicative.toAdd n), continuous_toFun := continuous_zpow _ } :
        PontryaginDual Circle)) = z ^ (Multiplicative.toAdd n)
    exact (circleCharacterExponent_spec _ z).symm
  map_mul' χ ψ := by
    apply Multiplicative.toAdd.injective
    apply circle_zpow_injective
    intro z
    show z ^ circleCharacterExponent (χ * ψ) = z ^ (circleCharacterExponent χ + circleCharacterExponent ψ)
    rw [← circleCharacterExponent_spec, zpow_add, ← circleCharacterExponent_spec,
      ← circleCharacterExponent_spec]
    rfl
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- Morris, Topology Without Tears, Corollary A5.7.10 (TP-567). The dual group of the circle group
is topologically isomorphic to `ℤ`, the isomorphism sending a character `z ↦ z ^ m` to `m`. -/
@[kb "morris2024" "Corollary A5.7.10, p. 561"]
theorem exists_continuousMulEquiv_dual_circle_int :
    ∃ e : PontryaginDual Circle ≃ₜ* Multiplicative ℤ,
      ∀ (χ : PontryaginDual Circle) (m : ℤ), e χ = Multiplicative.ofAdd m →
        ∀ z : Circle, χ z = z ^ m := by
  refine ⟨dualCircleEquivInt, fun χ m hm z => ?_⟩
  have : circleCharacterExponent χ = m := Multiplicative.ofAdd.injective hm
  rw [circleCharacterExponent_spec χ z, this]

/-! ### The canonical map into the double dual -/

section Duality

variable (A : Type*) [CommGroup A] [TopologicalSpace A]

/-- Evaluation at a point `a`, as a character of the dual group. -/
noncomputable def evalAtPoint (a : A) : PontryaginDual A →ₜ* Circle where
  toFun χ := χ a
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    have h : Continuous (fun χ : A →ₜ* Circle => χ a) := continuous_eval_const a
    exact h

/-- The canonical map `A → A^**` of a topological group into the dual of its dual. -/
noncomputable def toDualDual [LocallyCompactSpace A] :
    A →ₜ* PontryaginDual (PontryaginDual A) where
  toFun a := evalAtPoint A a
  map_one' := PontryaginDual.ext fun χ => by
    show χ 1 = 1
    exact map_one χ
  map_mul' a b := PontryaginDual.ext fun χ => by
    show χ (a * b) = χ a * χ b
    exact map_mul χ a b
  continuous_toFun := by
    refine ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_
    have h : Continuous (fun p : (A →ₜ* Circle) × A => p.1 p.2) := continuous_eval
    exact h.comp (continuous_snd.prodMk continuous_fst)

/-- Morris, Topology Without Tears, Lemma A5.8.2 (TP-571). For a locally compact abelian
topological group `A`, the canonical map `α : A → A^**`, `α a χ = χ a`, is a continuous
homomorphism into the dual of the dual. -/
@[kb "morris2024" "Lemma A5.8.2, p. 564"]
theorem exists_continuousMonoidHom_dualDual [LocallyCompactSpace A] :
    ∃ α : A →ₜ* PontryaginDual (PontryaginDual A), ∀ a χ, α a χ = χ a :=
  ⟨toDualDual A, fun _ _ => rfl⟩

end Duality

/-! ### Small definitions of Appendix 5 -/

section Monothetic

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Morris, Topology Without Tears, Definition A5.12.1 (TP-595). A topological group is monothetic
if it has a dense cyclic subgroup. -/
def IsMonothetic (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ g : G, Dense (Subgroup.zpowers g : Set G)

/-- Morris, Topology Without Tears, Definition A5.12.1 (TP-595). A group is monothetic iff some
element has dense set of integer powers. -/
@[kb "morris2024" "Definition A5.12.1, p. 581"]
theorem isMonothetic_iff_exists_denseRange_zpow :
    IsMonothetic G ↔ ∃ g : G, DenseRange (fun n : ℤ => g ^ n) := by
  have : ∀ g : G, (Subgroup.zpowers g : Set G) = Set.range (fun n : ℤ => g ^ n) := by
    intro g
    ext x
    simp [Subgroup.mem_zpowers_iff]
  simp only [IsMonothetic, this, DenseRange]

/-- Morris, Topology Without Tears, Definition A5.12.1 (TP-595), basic fact. A Hausdorff monothetic
topological group is abelian. -/
@[kb "morris2024" "Definition A5.12.1, p. 581"]
theorem IsMonothetic.mul_comm [IsTopologicalGroup G] [T2Space G] (h : IsMonothetic G) (x y : G) :
    x * y = y * x := by
  obtain ⟨g, hg⟩ := h
  have hz : ∀ k : ℤ, Commute (g ^ k) g := fun k => (Commute.refl g).zpow_left k
  have h1 : ∀ x : G, x * g = g * x := by
    intro x
    have hcl : IsClosed {x : G | x * g = g * x} :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    have hsub : (Subgroup.zpowers g : Set G) ⊆ {x : G | x * g = g * x} := by
      rintro _ ⟨k, rfl⟩
      exact (hz k).eq
    have := closure_minimal hsub hcl
    rw [hg.closure_eq] at this
    exact this (Set.mem_univ x)
  have h2 : ∀ k : ℤ, x * g ^ k = g ^ k * x := fun k => (Commute.zpow_right (show Commute x g from h1 x) k).eq
  have hcl : IsClosed {y : G | x * y = y * x} :=
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  have hsub : (Subgroup.zpowers g : Set G) ⊆ {y : G | x * y = y * x} := by
    rintro _ ⟨k, rfl⟩
    exact h2 k
  have := closure_minimal hsub hcl
  rw [hg.closure_eq] at this
  exact this (Set.mem_univ y)

/-- Morris, Topology Without Tears, Definition A5.12.1 (TP-595), basic fact. A continuous
surjective homomorphic image of a monothetic group is monothetic. -/
@[kb "morris2024" "Definition A5.12.1, p. 581"]
theorem IsMonothetic.of_surjective {H : Type*} [Group H] [TopologicalSpace H]
    (h : IsMonothetic G) (f : G →ₜ* H) (hf : Function.Surjective f) : IsMonothetic H := by
  obtain ⟨g, hg⟩ := h
  refine ⟨f g, ?_⟩
  have : (Subgroup.zpowers (f g) : Set H) = f '' (Subgroup.zpowers g : Set G) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨g ^ k, ⟨k, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by simp⟩
  rw [this]
  exact (hf.denseRange).dense_image f.continuous hg

/-- The group `ℤ` (written multiplicatively) is monothetic, generated by `1`. -/
@[kb "morris2024" "Definition A5.12.1, p. 581"]
theorem isMonothetic_multiplicative_int : IsMonothetic (Multiplicative ℤ) := by
  refine ⟨Multiplicative.ofAdd 1, ?_⟩
  have : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) : Set (Multiplicative ℤ)) = Set.univ := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_univ, iff_true]
    exact ⟨x.toAdd, by rw [← ofAdd_zsmul]; simp⟩
  rw [this]
  exact dense_univ

end Monothetic

section Exact

variable {A B C : Type*} [Group A] [Group B] [Group C] [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace C]

/-- Morris, Topology Without Tears, Definition A5.13.1 (TP-603). The sequence
`1 → A → B → C → 1` of topological groups and continuous homomorphisms is exact: `f₁` is
injective, `f₂` is surjective and `ker f₂ = f₁ (A)`. -/
def IsTopExact (f₁ : A →ₜ* B) (f₂ : B →ₜ* C) : Prop :=
  Function.Injective f₁ ∧ Function.Surjective f₂ ∧ ∀ b : B, f₂ b = 1 ↔ b ∈ Set.range f₁

/-- Morris, Topology Without Tears, Definition A5.13.1 (TP-603). Exactness in terms of the
kernel and the range subgroups. -/
@[kb "morris2024" "Definition A5.13.1, p. 591"]
theorem isTopExact_iff (f₁ : A →ₜ* B) (f₂ : B →ₜ* C) :
    IsTopExact f₁ f₂ ↔ Function.Injective f₁ ∧ Function.Surjective f₂ ∧
      (f₂ : B →* C).ker = (f₁ : A →* B).range := by
  unfold IsTopExact
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    ext b
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
    exact h b
  · intro h b
    have := congrArg (fun S : Subgroup B => b ∈ S) h
    simpa using this

/-- The short exact sequence `1 → N → G → G ⧸ N → 1` of a normal subgroup is exact (Morris,
Topology Without Tears, Definition A5.13.1, TP-603). -/
@[kb "morris2024" "Definition A5.13.1, p. 591"]
theorem isTopExact_subtype_mk (N : Subgroup B) [N.Normal] :
    IsTopExact
      ({ toMonoidHom := N.subtype, continuous_toFun := continuous_subtype_val } : N →ₜ* B)
      ({ toMonoidHom := QuotientGroup.mk' N, continuous_toFun := QuotientGroup.continuous_mk } :
        B →ₜ* B ⧸ N) := by
  refine ⟨Subtype.val_injective, QuotientGroup.mk_surjective, fun b => ?_⟩
  show QuotientGroup.mk' N b = 1 ↔ b ∈ Set.range N.subtype
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  simp

end Exact

section AlmostPeriodic

/-- Morris, Topology Without Tears, Definition §A5.13 (TP-612). A topological group is maximally
almost periodic if it admits a continuous injective homomorphism into a compact Hausdorff group. -/
def IsMaximallyAlmostPeriodic (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (K : Type u) (_ : Group K) (_ : TopologicalSpace K) (_ : IsTopologicalGroup K)
    (_ : CompactSpace K) (_ : T2Space K) (f : G →ₜ* K), Function.Injective f

/-- Morris, Topology Without Tears, Definition §A5.13 (TP-613). A topological group is minimally
almost periodic if every continuous homomorphism into a compact Hausdorff group is trivial. -/
def IsMinimallyAlmostPeriodic (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] (f : G →ₜ* K), ∀ g : G, f g = 1

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- Morris, Topology Without Tears, Exercises A5.13 #7 (TP-612). Every compact Hausdorff group is
maximally almost periodic (the identity map is the embedding). -/
@[kb "morris2024" "Exercises A5.13, p. 601"]
theorem isMaximallyAlmostPeriodic_of_compact [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] : IsMaximallyAlmostPeriodic G :=
  ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ContinuousMonoidHom.id G, Function.injective_id⟩

/-- Morris, Topology Without Tears, Exercises A5.13 #8 (TP-613). A group which is both maximally
and minimally almost periodic is trivial. -/
@[kb "morris2024" "Exercises A5.13, p. 601"]
theorem subsingleton_of_isMaximally_of_isMinimallyAlmostPeriodic
    (hmax : IsMaximallyAlmostPeriodic G) (hmin : IsMinimallyAlmostPeriodic G) : Subsingleton G := by
  obtain ⟨K, _, _, _, _, _, f, hf⟩ := hmax
  refine ⟨fun a b => hf ?_⟩
  rw [hmin K f a, hmin K f b]

/-- Morris, Topology Without Tears, Exercises A5.13 #8 (TP-613). The trivial group is minimally
almost periodic. -/
@[kb "morris2024" "Exercises A5.13, p. 601"]
theorem isMinimallyAlmostPeriodic_of_subsingleton [Subsingleton G] :
    IsMinimallyAlmostPeriodic G := by
  intro K _ _ _ _ _ f g
  rw [Subsingleton.elim g 1]
  exact map_one f

end AlmostPeriodic

section Simple

/-- Morris, Topology Without Tears, Definition §A5.13 (TP-615). A topological group is
topologically simple if its only closed normal subgroups are `{1}` and the whole group. -/
def IsTopologicallySimple (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ N : Subgroup G, N.Normal → IsClosed (N : Set G) → N = ⊥ ∨ N = ⊤

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Morris, Topology Without Tears, Exercises A5.13 #8 (i) (TP-615). Every simple group with the
discrete topology is topologically simple. -/
@[kb "morris2024" "Exercises A5.13, p. 601"]
theorem isTopologicallySimple_of_isSimpleGroup [IsSimpleGroup G] :
    IsTopologicallySimple G :=
  fun N hN _ => by
    have := hN
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N

/-- Morris, Topology Without Tears, Definition §A5.13 (TP-615). For the discrete topology,
topological simplicity is the absence of proper nontrivial normal subgroups. -/
@[kb "morris2024" "Exercises A5.13, p. 601"]
theorem isTopologicallySimple_iff_of_discreteTopology [DiscreteTopology G] :
    IsTopologicallySimple G ↔ ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤ :=
  ⟨fun h N hN => h N hN (isClosed_discrete _), fun h N hN _ => h N hN⟩

end Simple

section AlmostConnected

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Morris, Topology Without Tears, Exercises A5.13 #10 (TP-616). A topological group is almost
connected if the quotient by the connected component of the identity is compact. -/
def IsAlmostConnected : Prop :=
  CompactSpace (G ⧸ Subgroup.connectedComponentOfOne G)

/-- Morris, Topology Without Tears, Exercises A5.13 #10 (TP-616). Every compact group is almost
connected. -/
@[kb "morris2024" "Exercises A5.13, p. 602"]
theorem isAlmostConnected_of_compactSpace [CompactSpace G] : IsAlmostConnected G := by
  unfold IsAlmostConnected
  infer_instance

/-- Morris, Topology Without Tears, Exercises A5.13 #10 (TP-616). Every connected group is almost
connected. -/
@[kb "morris2024" "Exercises A5.13, p. 602"]
theorem isAlmostConnected_of_connectedSpace [ConnectedSpace G] : IsAlmostConnected G := by
  have h : Subgroup.connectedComponentOfOne G = ⊤ := by
    rw [eq_top_iff]
    intro x _
    show x ∈ connectedComponent (1 : G)
    exact isPreconnected_univ.subset_connectedComponent (Set.mem_univ 1) (Set.mem_univ x)
  have hs : Subsingleton (G ⧸ Subgroup.connectedComponentOfOne G) :=
    ⟨fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact QuotientGroup.eq.2 (by rw [h]; trivial)⟩
  unfold IsAlmostConnected
  infer_instance

end AlmostConnected

section Annihilator

variable (A : Type*) [CommGroup A] [TopologicalSpace A]

/-- Morris, Topology Without Tears, Definition A5.14.1 (TP-617). The characterAnnihilator of a subgroup `H`
of `A`: the characters of `A` that are trivial on `H`. -/
def characterAnnihilator (H : Subgroup A) : Subgroup (PontryaginDual A) where
  carrier := {χ | ∀ h ∈ H, χ h = 1}
  one_mem' := fun h _ => rfl
  mul_mem' := by
    intro a b ha hb h hh
    show a h * b h = 1
    rw [ha h hh, hb h hh, mul_one]
  inv_mem' := by
    intro a ha h hh
    show (a h)⁻¹ = 1
    rw [ha h hh, inv_one]

variable {A}

/-- Morris, Topology Without Tears, Definition A5.14.1 (TP-617). The characterAnnihilator of a subgroup is a
closed subgroup of the dual group. -/
@[kb "morris2024" "Definition A5.14.1, p. 602"]
theorem isClosed_characterAnnihilator (H : Subgroup A) : IsClosed (characterAnnihilator A H : Set (PontryaginDual A)) := by
  have : (characterAnnihilator A H : Set (PontryaginDual A)) =
      ⋂ h ∈ H, (evalAtPoint A h) ⁻¹' {(1 : Circle)} := by
    ext χ
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact Iff.rfl
  rw [this]
  exact isClosed_biInter fun h _ => isClosed_singleton.preimage (evalAtPoint A h).continuous

/-- Morris, Topology Without Tears, Definition A5.14.1 (TP-617). Membership in the characterAnnihilator. -/
@[kb "morris2024" "Definition A5.14.1, p. 602"]
theorem mem_characterAnnihilator_iff (H : Subgroup A) (χ : PontryaginDual A) :
    χ ∈ characterAnnihilator A H ↔ ∀ h ∈ H, χ h = 1 := Iff.rfl

/-- Morris, Topology Without Tears, Definition A5.14.1 (TP-617). The characterAnnihilator reverses the
order of subgroups. -/
@[kb "morris2024" "Definition A5.14.1, p. 602"]
theorem characterAnnihilator_antitone {H K : Subgroup A} (h : H ≤ K) :
    characterAnnihilator A K ≤ characterAnnihilator A H :=
  fun _ hχ x hx => hχ x (h hx)

end Annihilator

section CompactElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Morris, Topology Without Tears, Definition A5.15.4 (TP-628). An element `g` is compact if the
smallest closed subgroup containing `g` (the closure of `⟨g⟩`) is compact. -/
def IsCompactElement (g : G) : Prop :=
  IsCompact ((Subgroup.zpowers g).topologicalClosure : Set G)

/-- Morris, Topology Without Tears, Definition A5.15.4 (TP-628). In terms of the closure of the set
of integer powers. -/
@[kb "morris2024" "Definition A5.15.4, p. 609"]
theorem isCompactElement_iff (g : G) :
    IsCompactElement g ↔ IsCompact (closure (Set.range fun n : ℤ => g ^ n)) := by
  have : (Subgroup.zpowers g : Set G) = Set.range (fun n : ℤ => g ^ n) := by
    ext x; simp [Subgroup.mem_zpowers_iff]
  unfold IsCompactElement
  rw [Subgroup.topologicalClosure_coe, this]

/-- Morris, Topology Without Tears, Definition A5.15.4 (TP-628). In a compact group every element
is compact (a closed subset of a compact space is compact). -/
@[kb "morris2024" "Definition A5.15.4, p. 609"]
theorem isCompactElement_of_compactSpace [CompactSpace G] (g : G) : IsCompactElement g :=
  (Subgroup.isClosed_topologicalClosure _).isCompact

/-- Morris, Topology Without Tears, Definition A5.15.4 (TP-628). An element is compact iff its
inverse is. -/
@[kb "morris2024" "Definition A5.15.4, p. 609"]
theorem isCompactElement_inv_iff (g : G) : IsCompactElement g⁻¹ ↔ IsCompactElement g := by
  unfold IsCompactElement
  rw [Subgroup.zpowers_inv]

end CompactElement

section LocallyKOmega

/-- Morris, Topology Without Tears, Exercises 10.3 #5 (used in §A5.12, TP-637). A `kω`-space: a
Hausdorff space which is the union of an increasing sequence of compact subsets such that a set
is closed iff its intersection with each of them is closed (in a Hausdorff space, iff each
intersection is compact). -/
def IsKOmegaSpace (X : Type*) [TopologicalSpace X] : Prop :=
  T2Space X ∧ ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ Monotone K ∧ (⋃ n, K n) = Set.univ ∧
    ∀ A : Set X, IsClosed A ↔ ∀ n, IsClosed (A ∩ K n)

/-- Morris, Topology Without Tears, §A5.12 (TP-637). A space is locally `kω` if each point has an
open neighbourhood which is a `kω`-space (in the subspace topology). -/
def IsLocallyKOmega (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsKOmegaSpace U

/-- Every compact Hausdorff space is a `kω`-space. -/
@[kb "morris2024" "Exercises 10.3, p. 300"]
theorem isKOmegaSpace_of_compactSpace (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : IsKOmegaSpace X := by
  refine ⟨inferInstance, fun _ => Set.univ, fun _ => isCompact_univ, monotone_const, ?_, ?_⟩
  · exact Set.iUnion_const _
  · intro A
    simp

/-- Morris, Topology Without Tears, §A5.12 (TP-637), basic fact. Every compact Hausdorff space is a
locally `kω`-space. -/
@[kb "morris2024" "Exercises A5.12, p. 589"]
theorem isLocallyKOmega_of_compactSpace (X : Type*) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : IsLocallyKOmega X := by
  intro x
  have : CompactSpace (Set.univ : Set X) := isCompact_iff_compactSpace.1 isCompact_univ
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ x, isKOmegaSpace_of_compactSpace _⟩

/-- Morris, Topology Without Tears, §A5.12 (TP-637), basic fact. Every discrete space is a locally
`kω`-space (each point is an open one-point neighbourhood). -/
@[kb "morris2024" "Exercises A5.12, p. 589"]
theorem isLocallyKOmega_of_discreteTopology (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    IsLocallyKOmega X := by
  intro x
  have : CompactSpace ({x} : Set X) := isCompact_iff_compactSpace.1 isCompact_singleton
  exact ⟨{x}, isOpen_discrete _, rfl, isKOmegaSpace_of_compactSpace _⟩

end LocallyKOmega

section ThreeSpace

/-- Morris, Topology Without Tears, Exercises A5.12 #5 (TP-638). A property `P` of topological
groups is a three-space property if whenever a closed normal subgroup `N` and the quotient `G ⧸ N`
have `P`, so does `G`. -/
def IsThreeSpaceProperty
    (P : (G : Type u) → [Group G] → [TopologicalSpace G] → Prop) : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
    [N.Normal], IsClosed (N : Set G) → P N → P (G ⧸ N) → P G

/-- Morris, Topology Without Tears, Exercises A5.12 #5 (iv) (TP-638). Being a discrete group is a
three-space property. -/
@[kb "morris2024" "Exercises A5.12, p. 590"]
theorem isThreeSpaceProperty_discreteTopology :
    IsThreeSpaceProperty.{u} (fun G _ _ => DiscreteTopology G) := by
  intro G _ _ _ N _ _ hN hQ
  have hopen : IsOpen (N : Set G) := QuotientGroup.discreteTopology_iff.1 hQ
  apply discreteTopology_of_isOpen_singleton_one
  obtain ⟨t, ht, htN⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set N))
  have : ({1} : Set G) = t ∩ (N : Set G) := by
    ext x
    constructor
    · rintro rfl
      refine ⟨?_, N.one_mem⟩
      have : (1 : N) ∈ Subtype.val ⁻¹' t := by rw [htN]; rfl
      exact this
    · rintro ⟨hxt, hxN⟩
      have : (⟨x, hxN⟩ : N) ∈ Subtype.val ⁻¹' t := hxt
      rw [htN] at this
      have h1 : (⟨x, hxN⟩ : N) = 1 := this
      exact congrArg Subtype.val h1
  rw [this]
  exact ht.inter hopen

/-- Morris, Topology Without Tears, Exercises A5.12 #5 (i) (TP-638). Being a finite group is a
three-space property. -/
@[kb "morris2024" "Exercises A5.12, p. 590"]
theorem isThreeSpaceProperty_finite :
    IsThreeSpaceProperty.{u} (fun G _ _ => Finite G) := by
  intro G _ _ _ N _ _ hN hQ
  exact Finite.of_subgroup_quotient N

end ThreeSpace

section Divisible

/-- A group is divisible (multiplicatively) if every element has a `k`-th root for each `k ≥ 1`. -/
def IsDivisibleMulGroup (G : Type*) [Group G] : Prop :=
  ∀ k : ℕ, 0 < k → ∀ x : G, ∃ y : G, y ^ k = x

/-- Morris, Topology Without Tears, §A5.15 (TP-640). A group is somewhat divisible if it is a
product `H₁ ⋯ Hₙ` of divisible subgroups. -/
def IsSomewhatDivisible (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin n → Subgroup G),
    (∀ i, ∀ k : ℕ, 0 < k → ∀ x ∈ H i, ∃ y ∈ H i, y ^ k = x) ∧
    ∀ g : G, ∃ f : Fin n → G, (∀ i, f i ∈ H i) ∧ (List.ofFn f).prod = g

/-- Morris, Topology Without Tears, §A5.15 (TP-640). Every divisible group is somewhat divisible
(take `n = 1` and `H₁ = G`). -/
@[kb "morris2024" "Remark (somewhat divisible groups, after Corollary A5.15.16), p. 614"]
theorem isSomewhatDivisible_of_isDivisible {G : Type*} [Group G] (h : IsDivisibleMulGroup G) :
    IsSomewhatDivisible G := by
  refine ⟨1, fun _ => ⊤, ?_, fun g => ⟨fun _ => g, fun _ => trivial, by simp⟩⟩
  intro i k hk x _
  obtain ⟨y, hy⟩ := h k hk x
  exact ⟨y, trivial, hy⟩

/-- Morris, Topology Without Tears, §A5.15 (TP-640). An abelian group is divisible iff it is
somewhat divisible. -/
@[kb "morris2024" "Remark (somewhat divisible groups, after Corollary A5.15.16), p. 614"]
theorem isDivisibleMulGroup_iff_isSomewhatDivisible {G : Type*} [CommGroup G] :
    IsDivisibleMulGroup G ↔ IsSomewhatDivisible G := by
  refine ⟨isSomewhatDivisible_of_isDivisible, ?_⟩
  rintro ⟨n, H, hH, hG⟩ k hk x
  obtain ⟨f, hf, rfl⟩ := hG x
  choose y hyH hy using fun i => hH i k hk (f i) (hf i)
  refine ⟨(List.ofFn y).prod, ?_⟩
  rw [List.prod_ofFn, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => hy i

end Divisible

section Solenoidal

/-- Morris, Topology Without Tears, Exercises A5.13 #4 (TP-641). A topological group is solenoidal
if some continuous homomorphism `ℝ → G` (from the additive reals) maps onto it. -/
def IsSolenoidal (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ f : ℝ → G, Continuous f ∧ (∀ s t, f (s + t) = f s * f t) ∧ Set.range f = Set.univ

/-- Morris, Topology Without Tears, Exercises A5.13 #4 (TP-641). The additive group of the reals
is solenoidal. -/
@[kb "morris2024" "Exercises A5.13, p. 599"]
theorem isSolenoidal_multiplicative_real : IsSolenoidal (Multiplicative ℝ) :=
  ⟨Multiplicative.ofAdd, continuous_ofAdd, fun _ _ => rfl, by
    ext x; simp⟩

/-- Morris, Topology Without Tears, Exercises A5.13 #4 (TP-641). The circle group is solenoidal. -/
@[kb "morris2024" "Exercises A5.13, p. 599"]
theorem isSolenoidal_circle : IsSolenoidal Circle :=
  ⟨Circle.exp, Circle.exp.continuous, Circle.exp_add, by
    ext x; simp [Circle.exp_surjective x]⟩

/-- Morris, Topology Without Tears, Exercises A5.13 #4 (TP-641), basic fact. A solenoidal group is
abelian. -/
@[kb "morris2024" "Exercises A5.13, p. 599"]
theorem IsSolenoidal.mul_comm {G : Type*} [Group G] [TopologicalSpace G] (h : IsSolenoidal G)
    (x y : G) : x * y = y * x := by
  obtain ⟨f, -, hf, hr⟩ := h
  have hx : x ∈ Set.range f := by rw [hr]; trivial
  have hy : y ∈ Set.range f := by rw [hr]; trivial
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  rw [← hf, ← hf, add_comm]

/-- Morris, Topology Without Tears, Exercises A5.13 #4 (TP-641), basic fact. A solenoidal group is
connected. -/
@[kb "morris2024" "Exercises A5.13, p. 599"]
theorem IsSolenoidal.connectedSpace {G : Type*} [Group G] [TopologicalSpace G]
    (h : IsSolenoidal G) : ConnectedSpace G := by
  obtain ⟨f, hc, -, hr⟩ := h
  have : IsConnected (Set.range f) := isConnected_range hc
  rw [hr] at this
  exact connectedSpace_iff_univ.2 this

end Solenoidal

section PGL

open Matrix

/-- Morris, Topology Without Tears, §A5.0 (TP-482). The projective group `PGL(n, ℝ)`: the quotient
of `GL(n, ℝ)` by the subgroup of scalar matrices (the centre), with the quotient topology. This is
Mathlib's `Matrix.ProjGenLinGroup (Fin n) ℝ`, here equipped with the quotient topology. -/
abbrev PGLReal (n : ℕ) : Type :=
  GL (Fin n) ℝ ⧸ Subgroup.center (GL (Fin n) ℝ)

/-- Morris, Topology Without Tears, §A5.0 (TP-482). `PGLReal n` is Mathlib's projective general
linear group `PGL(n, ℝ)` as a group. -/
@[kb "morris2024" "Remark (projective group, §A5.0), p. 496"]
theorem pglReal_eq_projGenLinGroup (n : ℕ) : PGLReal n = Matrix.ProjGenLinGroup (Fin n) ℝ := rfl

/-- Morris, Topology Without Tears, §A5.0 (TP-482). `PGL(n, ℝ)` with the quotient topology is a
topological group. -/
@[kb "morris2024" "Remark (projective group, §A5.0), p. 496"]
theorem pglReal_isTopologicalGroup (n : ℕ) : IsTopologicalGroup (PGLReal n) := by
  have : IsTopologicalGroup (GL (Fin n) ℝ) :=
    inferInstanceAs (IsTopologicalGroup (Matrix (Fin n) (Fin n) ℝ)ˣ)
  infer_instance

/-- Morris, Topology Without Tears, §A5.0 (TP-482). The kernel of `GL(n, ℝ) → PGL(n, ℝ)` is the
group of nonzero scalar matrices `λ Iₙ`, and two matrices have the same class iff they differ by
a nonzero scalar. -/
@[kb "morris2024" "Remark (projective group, §A5.0), p. 496"]
theorem pglReal_mk_eq_mk_iff {n : ℕ} (g₁ g₂ : GL (Fin n) ℝ) :
    (QuotientGroup.mk g₁ : PGLReal n) = QuotientGroup.mk g₂ ↔
      ∃ u : ℝˣ, g₁ * GeneralLinearGroup.scalar (Fin n) u = g₂ :=
  ProjGenLinGroup.mk_eq_mk_iff

/-- Morris, Topology Without Tears, §A5.0 (TP-482). The kernel of the quotient map is the range of
the scalar matrices. -/
@[kb "morris2024" "Remark (projective group, §A5.0), p. 496"]
theorem pglReal_ker_mk (n : ℕ) :
    (QuotientGroup.mk' (Subgroup.center (GL (Fin n) ℝ))).ker =
      (GeneralLinearGroup.scalar (Fin n) (R := ℝ)).range := by
  rw [QuotientGroup.ker_mk', GeneralLinearGroup.center_eq_range_scalar]

end PGL

end UndergradKB.Topology
