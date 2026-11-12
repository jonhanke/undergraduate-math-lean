import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import UndergradKB.Topology.Characters
import UndergradKB.Topology.GroupsExtra
import UndergradKB.Common.Attr

/-!
# Duals of the classical groups (Morris, Appendix 5, section 5.9)

The characters of `ℝ`, the self-duality of `ℝⁿ`, the duality of `Tⁿ` and `ℤⁿ`, and the Pontryagin-van
Kampen duality property for finite products of `ℝ`, `ℤ` and the circle.
-/

namespace UndergradKB.Topology

open Set Filter
open scoped _root_.Topology
open scoped Real

/-! ### Functoriality and finite products of duals -/

section Functorial

variable {A B : Type*} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B]

/-- A topological isomorphism `A ≃ₜ* B` induces one between the duals. -/
noncomputable def dualCongr (e : A ≃ₜ* B) : PontryaginDual A ≃ₜ* PontryaginDual B where
  toFun χ := PontryaginDual.map ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩ χ
  invFun ψ := PontryaginDual.map ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩ ψ
  left_inv χ := PontryaginDual.ext fun a => by
    show χ (e.symm (e a)) = χ a
    rw [e.symm_apply_apply]
  right_inv ψ := PontryaginDual.ext fun b => by
    show ψ (e (e.symm b)) = ψ b
    rw [e.apply_symm_apply]
  map_mul' _ _ := rfl
  continuous_toFun := (PontryaginDual.map _).continuous
  continuous_invFun := (PontryaginDual.map _).continuous

theorem dualCongr_symm_apply (e : A ≃ₜ* B) (ψ : PontryaginDual B) (a : A) :
    (dualCongr e).symm ψ a = ψ (e a) := rfl

/-- Product of two topological isomorphisms. -/
def prodCongr {C D : Type*} [CommGroup C] [CommGroup D] [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* C) (f : B ≃ₜ* D) : (A × B) ≃ₜ* (C × D) where
  toFun p := (e p.1, f p.2)
  invFun p := (e.symm p.1, f.symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_mul' p q := by simp
  continuous_toFun := (e.continuous.comp continuous_fst).prodMk (f.continuous.comp continuous_snd)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_fst).prodMk (f.symm.continuous.comp continuous_snd)

end Functorial

section PiDual

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*} [∀ i, CommGroup (G i)]
  [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

/-- Componentwise product of topological isomorphisms. -/
def piCongr {H : ι → Type*} [∀ i, CommGroup (H i)] [∀ i, TopologicalSpace (H i)]
    (e : ∀ i, G i ≃ₜ* H i) : (∀ i, G i) ≃ₜ* (∀ i, H i) where
  toFun g i := e i (g i)
  invFun h i := (e i).symm (h i)
  left_inv g := by funext i; simp
  right_inv h := by funext i; simp
  map_mul' g h := by funext i; simp
  continuous_toFun := continuous_pi fun i => (e i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (e i).symm.continuous.comp (continuous_apply i)

omit [DecidableEq ι] [∀ i, IsTopologicalGroup (G i)] in
/-- Evaluating a finite product of characters. -/
theorem prod_apply_pontryaginDual {X : Type*} [CommGroup X] [TopologicalSpace X]
    (q : ι → PontryaginDual X) (y : X) : (∏ j, q j) y = ∏ j, q j y :=
  map_prod (evalAtPoint X y) q Finset.univ

/-- The `i`-th coordinate inclusion as a continuous homomorphism. -/
def mulSingleHom (i : ι) : G i →ₜ* (∀ i, G i) :=
  ⟨MonoidHom.mulSingle G i, continuous_mulSingle i⟩

/-- The `i`-th coordinate projection as a continuous homomorphism. -/
def evalHom (i : ι) : (∀ i, G i) →ₜ* G i :=
  ⟨Pi.evalMonoidHom G i, continuous_apply i⟩

/-- Morris, Topology Without Tears, Theorem A5.9.1 (TP-573), finite products with any index type.
The Pontryagin dual of a finite product of topological groups is topologically isomorphic to the
product of the duals. -/
@[kb "morris2024" "Theorem A5.9.1, p. 566"]
noncomputable def pontryaginDualPiEquiv :
    PontryaginDual (∀ i, G i) ≃ₜ* ∀ i, PontryaginDual (G i) where
  toFun ψ i := PontryaginDual.map (mulSingleHom i) ψ
  invFun p := ∏ i, PontryaginDual.map (evalHom i) (p i)
  left_inv ψ := PontryaginDual.ext fun x => by
    rw [prod_apply_pontryaginDual]
    show ∏ i, ψ (Pi.mulSingle i (x i)) = ψ x
    rw [← map_prod, Finset.univ_prod_mulSingle]
  right_inv p := funext fun i => PontryaginDual.ext fun x => by
    show (∏ j, PontryaginDual.map (evalHom j) (p j)) (Pi.mulSingle i x) = p i x
    rw [prod_apply_pontryaginDual, Finset.prod_eq_single i]
    · show p i (Pi.mulSingle i x i) = p i x
      simp
    · intro j _ hj
      show p j (Pi.mulSingle i x j) = 1
      simp [Pi.mulSingle_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  map_mul' _ _ := funext fun i => rfl
  continuous_toFun := continuous_pi fun i => (PontryaginDual.map (mulSingleHom i)).continuous
  continuous_invFun := continuous_finsetProd _ fun i _ =>
    (PontryaginDual.map (evalHom i)).continuous.comp (continuous_apply i)

end PiDual

/-! ### The dual of `ℝ` -/

section Real

/-- Morris, Topology Without Tears, Corollary A5.9.2 (TP-574), characters of `ℝ`. Every continuous
character of the additive group `ℝ` (written multiplicatively) is `x ↦ exp (2 π i t x)`. -/
@[kb "morris2024" "Corollary A5.9.2, p. 566"]
theorem dual_real_apply (χ : PontryaginDual (Multiplicative ℝ)) :
    ∃ t : ℝ, ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Circle.exp (2 * π * t * x) := by
  let ψ : C(ℝ, Circle) :=
    ⟨fun x => χ (Multiplicative.ofAdd x), χ.continuous.comp continuous_ofAdd⟩
  have hψadd : ∀ s u, ψ (s + u) = ψ s * ψ u := fun s u => by
    show χ (Multiplicative.ofAdd (s + u)) = χ (Multiplicative.ofAdd s) * χ (Multiplicative.ofAdd u)
    rw [ofAdd_add, map_mul]
  have lift : ∀ (f : C(ℝ, Circle)) (e₀ : ℝ), Circle.exp e₀ = f 0 →
      ∃! F : C(ℝ, ℝ), F 0 = e₀ ∧ (Circle.exp ∘ F) = f := fun f e₀ he =>
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 e₀ he
  have hψ0 : Circle.exp 0 = ψ 0 := by
    show Circle.exp 0 = χ (Multiplicative.ofAdd 0)
    rw [Circle.exp_zero, ofAdd_zero, map_one]
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ := lift ψ 0 hψ0
  have hFexp : ∀ t, Circle.exp (F t) = ψ t := fun t => congrFun hFlift t
  have hadd : ∀ s t, F (s + t) = F s + F t := by
    intro s t
    let f : C(ℝ, Circle) := ⟨fun t => ψ s * ψ t, by fun_prop⟩
    have hf0 : Circle.exp (F s) = f 0 := by
      show Circle.exp (F s) = ψ s * ψ 0
      rw [hFexp, ← hψ0, Circle.exp_zero, mul_one]
    obtain ⟨F', -, huniq⟩ := lift f (F s) hf0
    have h1 := huniq ⟨fun t => F (s + t), by fun_prop⟩ ⟨by simp, by
      funext u
      show Circle.exp (F (s + u)) = ψ s * ψ u
      rw [hFexp, hψadd]⟩
    have h2 := huniq ⟨fun t => F s + F t, by fun_prop⟩ ⟨by simp [hF0], by
      funext u
      show Circle.exp (F s + F u) = ψ s * ψ u
      rw [Circle.exp_add, hFexp, hFexp]⟩
    exact congrArg (fun G : C(ℝ, ℝ) => G t) (h1.trans h2.symm)
  let A : ℝ →+ ℝ := AddMonoidHom.mk' F hadd
  have hlin : ∀ t, F t = t * F 1 := by
    intro t
    have := map_real_smul A F.continuous t (1 : ℝ)
    simpa [A] using this
  refine ⟨F 1 / (2 * π), fun x => ?_⟩
  show ψ x = _
  rw [← hFexp, hlin]
  congr 1
  field_simp

/-- The character `x ↦ exp (2 π i t x)` of `ℝ`. -/
noncomputable def realChar (t : ℝ) : PontryaginDual (Multiplicative ℝ) where
  toFun x := Circle.exp (2 * π * t * Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, Circle.exp_add]
  continuous_toFun := by
    have : Continuous fun x : ℝ => Circle.exp (2 * π * t * x) := by fun_prop
    exact this.comp continuous_toAdd

theorem realChar_apply (t x : ℝ) :
    realChar t (Multiplicative.ofAdd x) = Circle.exp (2 * π * t * x) := rfl

/-- The parameter of a character of `ℝ` is unique. -/
theorem realChar_injective {t s : ℝ}
    (h : ∀ x : ℝ, Circle.exp (2 * π * t * x) = Circle.exp (2 * π * s * x)) : t = s := by
  by_contra hne
  have hd : t - s ≠ 0 := sub_ne_zero.2 hne
  have h1 := h (1 / (2 * (t - s)))
  have h2 : Circle.exp (2 * π * (t - s) * (1 / (2 * (t - s)))) = 1 := by
    have : 2 * π * (t - s) * (1 / (2 * (t - s))) = 2 * π * t * (1 / (2 * (t - s))) -
        2 * π * s * (1 / (2 * (t - s))) := by ring
    rw [this, Circle.exp_sub, h1, div_self']
  have h3 : 2 * π * (t - s) * (1 / (2 * (t - s))) = π := by field_simp
  rw [h3] at h2
  exact Circle.exp_pi_ne_one h2

/-- The parameter of a character of `ℝ`. -/
noncomputable def realCharParam (χ : PontryaginDual (Multiplicative ℝ)) : ℝ :=
  Classical.choose (dual_real_apply χ)

theorem realCharParam_spec (χ : PontryaginDual (Multiplicative ℝ)) (x : ℝ) :
    χ (Multiplicative.ofAdd x) = Circle.exp (2 * π * realCharParam χ * x) :=
  Classical.choose_spec (dual_real_apply χ) x

theorem realCharParam_realChar (t : ℝ) : realCharParam (realChar t) = t :=
  realChar_injective fun x => by rw [← realCharParam_spec, realChar_apply]

theorem realChar_realCharParam (χ : PontryaginDual (Multiplicative ℝ)) :
    realChar (realCharParam χ) = χ :=
  PontryaginDual.ext fun x => by
    rw [← ofAdd_toAdd x, realChar_apply, realCharParam_spec]

theorem realCharParam_mul (χ ψ : PontryaginDual (Multiplicative ℝ)) :
    realCharParam (χ * ψ) = realCharParam χ + realCharParam ψ :=
  realChar_injective fun x => by
    rw [← realCharParam_spec (χ * ψ)]
    show χ (Multiplicative.ofAdd x) * ψ (Multiplicative.ofAdd x) = _
    rw [realCharParam_spec χ, realCharParam_spec ψ, ← Circle.exp_add]
    congr 1
    ring

theorem realCharParam_one : realCharParam (1 : PontryaginDual (Multiplicative ℝ)) = 0 :=
  realChar_injective fun x => by
    rw [← realCharParam_spec]
    simp

/-- The parameter map is continuous at the trivial character: the compact-open topology on the
characters of `ℝ` is the usual topology of the parameter. -/
theorem tendsto_realCharParam :
    Tendsto realCharParam (𝓝 (1 : PontryaginDual (Multiplicative ℝ))) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K : Set (Multiplicative ℝ) := Multiplicative.ofAdd '' Icc 0 (1 / (4 * ε)) with hK
  have hKc : IsCompact K := isCompact_Icc.image continuous_ofAdd
  let W : Set (PontryaginDual (Multiplicative ℝ)) :=
    {χ | Set.MapsTo χ K (Circle.centeredArc (π / 2))}
  have hW : IsOpen W :=
    isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hKc (Circle.isOpen_centeredArc (π / 2)))
  have h1 : (1 : PontryaginDual (Multiplicative ℝ)) ∈ W := by
    intro x _
    show (1 : Circle) ∈ _
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  filter_upwards [hW.mem_nhds h1] with χ hχ
  rw [Real.dist_eq, sub_zero]
  by_contra hge
  push Not at hge
  set t := realCharParam χ with ht
  have htpos : 0 < |t| := lt_of_lt_of_le hε hge
  have htne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at htpos
    exact lt_irrefl _ htpos
  set x0 : ℝ := 1 / (4 * |t|) with hx0
  have hx0nn : 0 ≤ x0 := by positivity
  have hx0le : x0 ≤ 1 / (4 * ε) := by
    rw [hx0]
    gcongr
  have hmem := hχ (show Multiplicative.ofAdd x0 ∈ K from ⟨x0, ⟨hx0nn, hx0le⟩, rfl⟩)
  rw [realCharParam_spec] at hmem
  have hθ : 2 * π * t * x0 = if 0 ≤ t then π / 2 else -(π / 2) := by
    rw [hx0]
    split_ifs with h
    · rw [abs_of_nonneg h]
      field_simp
      norm_num
    · rw [abs_of_neg (not_le.1 h)]
      field_simp
      norm_num
  rw [Circle.mem_centeredArc (by linarith [Real.pi_pos]), hθ] at hmem
  split_ifs at hmem
  · rw [Circle.arg_exp (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      abs_of_pos (by positivity)] at hmem
    exact lt_irrefl _ hmem
  · rw [Circle.arg_exp (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]), abs_neg,
      abs_of_pos (by positivity)] at hmem
    exact lt_irrefl _ hmem

/-- Morris, Topology Without Tears, Corollary A5.9.2 (TP-574), `n = 1`. The dual group of `ℝ`
(written multiplicatively) is topologically isomorphic to `ℝ`, a character `x ↦ exp (2 π i t x)`
corresponding to its parameter `t`. -/
noncomputable def dualRealEquiv : PontryaginDual (Multiplicative ℝ) ≃ₜ* Multiplicative ℝ :=
  let Ψ : PontryaginDual (Multiplicative ℝ) →* Multiplicative ℝ :=
    { toFun := fun χ => Multiplicative.ofAdd (realCharParam χ)
      map_one' := by rw [realCharParam_one]; rfl
      map_mul' := fun χ ψ => by rw [realCharParam_mul]; rfl }
  have hΨ : Continuous Ψ := by
    refine continuous_of_continuousAt_one Ψ ?_
    have h := (continuous_ofAdd.tendsto 0).comp tendsto_realCharParam
    show Tendsto (fun χ => Multiplicative.ofAdd (realCharParam χ)) _ (𝓝 (Multiplicative.ofAdd
      (realCharParam (1 : PontryaginDual (Multiplicative ℝ)))))
    rw [realCharParam_one]
    exact h
  { toFun := Ψ
    invFun := fun s => realChar (Multiplicative.toAdd s)
    left_inv := realChar_realCharParam
    right_inv := fun s => by
      apply Multiplicative.toAdd.injective
      show realCharParam (realChar (Multiplicative.toAdd s)) = _
      exact realCharParam_realChar _
    map_mul' := Ψ.map_mul
    continuous_toFun := hΨ
    continuous_invFun := by
      refine ContinuousMonoidHom.continuous_of_continuous_uncurry
        (fun s : Multiplicative ℝ => realChar (Multiplicative.toAdd s)) ?_
      have h : Continuous fun q : ℝ × ℝ => Circle.exp (2 * π * q.1 * q.2) := by fun_prop
      exact h.comp ((continuous_toAdd.comp continuous_fst).prodMk
        (continuous_toAdd.comp continuous_snd)) }

theorem dualRealEquiv_apply (χ : PontryaginDual (Multiplicative ℝ)) :
    dualRealEquiv χ = Multiplicative.ofAdd (realCharParam χ) := rfl

theorem dualRealEquiv_symm_apply (s : Multiplicative ℝ) (x : ℝ) :
    dualRealEquiv.symm s (Multiplicative.ofAdd x) =
      Circle.exp (2 * π * Multiplicative.toAdd s * x) := rfl

end Real

/-! ### Self-duality of `ℝⁿ`, duality of `Tⁿ` and `ℤⁿ` -/

section Powers

/-- Morris, Topology Without Tears, Corollary A5.9.2 (TP-574). `ℝⁿ` (here `Fin n → ℝ`, written
multiplicatively) is topologically isomorphic to its own dual group. -/
@[kb "morris2024" "Corollary A5.9.2, p. 566"]
noncomputable def selfDualRealPow (n : ℕ) :
    PontryaginDual (Fin n → Multiplicative ℝ) ≃ₜ* (Fin n → Multiplicative ℝ) :=
  (pontryaginDualPiEquiv (G := fun _ : Fin n => Multiplicative ℝ)).trans
    (piCongr fun _ => dualRealEquiv)

/-- Morris, Topology Without Tears, Corollary A5.9.3 (TP-574). The dual group of `Tⁿ` is
topologically isomorphic to `ℤⁿ`. -/
@[kb "morris2024" "Corollary A5.9.3, p. 567"]
noncomputable def dualCirclePowEquiv (n : ℕ) :
    PontryaginDual (Fin n → Circle) ≃ₜ* (Fin n → Multiplicative ℤ) :=
  (pontryaginDualPiEquiv (G := fun _ : Fin n => Circle)).trans (piCongr fun _ => dualCircleEquivInt)

/-- Morris, Topology Without Tears, Corollary A5.9.3 (TP-574). The dual group of `ℤⁿ` is
topologically isomorphic to `Tⁿ`. -/
@[kb "morris2024" "Corollary A5.9.3, p. 567"]
noncomputable def dualIntPowEquiv (n : ℕ) :
    PontryaginDual (Fin n → Multiplicative ℤ) ≃ₜ* (Fin n → Circle) :=
  (pontryaginDualPiEquiv (G := fun _ : Fin n => Multiplicative ℤ)).trans
    (piCongr fun _ => dualIntEquivCircle)

/-- Morris, Topology Without Tears, Corollary A5.9.2 (TP-574), as a statement. -/
@[kb "morris2024" "Corollary A5.9.2, p. 566"]
theorem exists_continuousMulEquiv_dual_real_pow (n : ℕ) :
    Nonempty (PontryaginDual (Fin n → Multiplicative ℝ) ≃ₜ* (Fin n → Multiplicative ℝ)) :=
  ⟨selfDualRealPow n⟩

/-- Morris, Topology Without Tears, Corollary A5.9.3 (TP-574), as a statement: `Tⁿ` and `ℤⁿ` are
dual groups of each other. -/
@[kb "morris2024" "Corollary A5.9.3, p. 567"]
theorem exists_continuousMulEquiv_dual_circle_int_pow (n : ℕ) :
    Nonempty (PontryaginDual (Fin n → Circle) ≃ₜ* (Fin n → Multiplicative ℤ)) ∧
      Nonempty (PontryaginDual (Fin n → Multiplicative ℤ) ≃ₜ* (Fin n → Circle)) :=
  ⟨⟨dualCirclePowEquiv n⟩, ⟨dualIntPowEquiv n⟩⟩

end Powers

/-! ### The duality property for products (TP-575) -/

section Duality

/-- The Pontryagin-van Kampen duality property for `G`: the canonical map `G → G^**` is an
isomorphism of topological groups. -/
def DualityHolds (G : Type*) [CommGroup G] [TopologicalSpace G] : Prop :=
  ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ g χ, e g χ = χ g

variable {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The duality property follows from a perfect pairing: isomorphisms `G^ ≅ H` and `H^ ≅ G` such
that `G` acts on `G^` through them as evaluation. -/
theorem dualityHolds_of_pairing (ρ : PontryaginDual G ≃ₜ* H) (σ : PontryaginDual H ≃ₜ* G)
    (h : ∀ g χ, σ.symm g (ρ χ) = χ g) : DualityHolds G :=
  ⟨σ.symm.trans (dualCongr ρ).symm, fun g χ => h g χ⟩

/-- The duality property for `ℤ`. -/
theorem dualityHolds_int : DualityHolds (Multiplicative ℤ) :=
  dualityHolds_of_pairing dualIntEquivCircle dualCircleEquivInt fun n χ => by
    show (χ (Multiplicative.ofAdd 1)) ^ (Multiplicative.toAdd n) = χ n
    have := dual_int_apply χ (Multiplicative.toAdd n)
    rw [ofAdd_toAdd] at this
    exact this.symm

/-- The duality property for the circle group. -/
theorem dualityHolds_circle : DualityHolds Circle :=
  dualityHolds_of_pairing dualCircleEquivInt dualIntEquivCircle fun z χ => by
    show z ^ (circleCharacterExponent χ) = χ z
    exact (circleCharacterExponent_spec χ z).symm

/-- The duality property for `ℝ`. -/
theorem dualityHolds_real : DualityHolds (Multiplicative ℝ) :=
  dualityHolds_of_pairing dualRealEquiv dualRealEquiv fun x χ => by
    show Circle.exp (2 * π * Multiplicative.toAdd x * realCharParam χ) = χ x
    rw [← ofAdd_toAdd x, realCharParam_spec, ofAdd_toAdd, mul_right_comm]

/-- Morris, Topology Without Tears, Corollary A5.9.4 (TP-575). If two groups satisfy the duality
property, so does their product. -/
@[kb "morris2024" "Corollary A5.9.4, p. 567"]
theorem DualityHolds.prod (hG : DualityHolds G) (hH : DualityHolds H) : DualityHolds (G × H) := by
  obtain ⟨eG, hG⟩ := hG
  obtain ⟨eH, hH⟩ := hH
  refine dualityHolds_of_pairing (pontryaginDualProdEquiv G H)
    ((pontryaginDualProdEquiv (PontryaginDual G) (PontryaginDual H)).trans
      (prodCongr eG.symm eH.symm)) fun g χ => ?_
  obtain ⟨a, b⟩ := g
  show (eG a) (PontryaginDual.map (ContinuousMonoidHom.inl G H) χ) *
    (eH b) (PontryaginDual.map (ContinuousMonoidHom.inr G H) χ) = χ (a, b)
  rw [hG, hH]
  show χ (a, 1) * χ (1, b) = χ (a, b)
  rw [← map_mul]
  simp

/-- Morris, Topology Without Tears, Corollary A5.9.4 (TP-575). A finite product of groups satisfying
the duality property satisfies it. -/
@[kb "morris2024" "Corollary A5.9.4, p. 567"]
theorem DualityHolds.pi {ι : Type*} [Fintype ι] [DecidableEq ι] {G : ι → Type*}
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    (h : ∀ i, DualityHolds (G i)) : DualityHolds (∀ i, G i) := by
  choose e he using h
  refine dualityHolds_of_pairing (pontryaginDualPiEquiv (G := G))
    ((pontryaginDualPiEquiv (G := fun i => PontryaginDual (G i))).trans
      (piCongr fun i => (e i).symm)) fun g χ => ?_
  show (∏ i, PontryaginDual.map (evalHom i) (e i (g i)))
    (fun i => PontryaginDual.map (mulSingleHom i) χ) = χ g
  rw [prod_apply_pontryaginDual]
  have hi : ∀ i, (PontryaginDual.map (evalHom i) (e i (g i)))
      (fun j => PontryaginDual.map (mulSingleHom j) χ) = χ (Pi.mulSingle i (g i)) := by
    intro i
    show e i (g i) (PontryaginDual.map (mulSingleHom i) χ) = _
    rw [he]
    rfl
  rw [Finset.prod_congr rfl fun i _ => hi i, ← map_prod, Finset.univ_prod_mulSingle]

/-- Morris, Topology Without Tears, Corollary A5.9.4 (TP-575), the classical cases. The groups
`ℝᵃ × Tᵇ × ℤᶜ` satisfy the duality property (the book also allows a finite factor in the discrete
part, which needs the separation of points of a finite abelian group by characters). -/
@[kb "morris2024" "Corollary A5.9.4, p. 567"]
theorem dualityHolds_real_circle_int_pow (a b c : ℕ) :
    DualityHolds (((Fin a → Multiplicative ℝ) × (Fin b → Circle)) × (Fin c → Multiplicative ℤ)) :=
  (DualityHolds.pi fun _ => dualityHolds_real).prod
    (DualityHolds.pi fun _ => dualityHolds_circle) |>.prod
    (DualityHolds.pi fun _ => dualityHolds_int)

end Duality

/-! ### Kronecker's theorem (TP-623, TP-624) -/

section Kronecker

/-- The approximation property of Kronecker's theorem: for every `ε > 0` there are integers `q_i`
and `p_j` with `|∑ᵢ qᵢ aᵢⱼ − pⱼ − bⱼ| ≤ ε` for all `j`. -/
def KroneckerApprox {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin n → ℝ) : Prop :=
  ∀ ε > 0, ∃ (q : Fin m → ℤ) (p : Fin n → ℤ), ∀ j, |∑ i, (q i : ℝ) * a i j - p j - b j| ≤ ε

/-- The relation property of Kronecker's theorem: every integer vector `r` making all `∑ⱼ aᵢⱼ rⱼ`
integers makes `∑ⱼ bⱼ rⱼ` an integer. -/
def KroneckerRelation {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin n → ℝ) : Prop :=
  ∀ r : Fin n → ℤ, (∀ i, ∃ k : ℤ, ∑ j, a i j * r j = k) → ∃ k : ℤ, ∑ j, b j * r j = k

/-- Morris, Topology Without Tears, Theorem A5.14.8 (TP-623), necessity. If `b` is approximable by
integer combinations of the `aᵢ` modulo integers then every integer relation on the `aᵢ` is integral
on `b`. -/
@[kb "morris2024" "Theorem A5.14.8, p. 605"]
theorem KroneckerApprox.relation {m n : ℕ} {a : Fin m → Fin n → ℝ} {b : Fin n → ℝ}
    (h : KroneckerApprox a b) : KroneckerRelation a b := by
  intro r hr
  choose k hk using hr
  set s : ℝ := ∑ j, b j * r j with hs
  have hC : 0 < ∑ j, |(r j : ℝ)| + 1 := by positivity
  have hmem : s ∈ closure (Set.range ((↑) : ℤ → ℝ)) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨q, p, hqp⟩ := h (δ / (2 * (∑ j, |(r j : ℝ)| + 1))) (by positivity)
    refine ⟨((∑ i, q i * k i - ∑ j, p j * r j : ℤ) : ℝ), ⟨_, rfl⟩, ?_⟩
    have e : ((∑ i, q i * k i - ∑ j, p j * r j : ℤ) : ℝ) - s =
        ∑ j, (r j : ℝ) * (∑ i, (q i : ℝ) * a i j - p j - b j) := by
      have h1 : ∀ j, (r j : ℝ) * (∑ i, (q i : ℝ) * a i j - p j - b j) =
          ∑ i, (q i : ℝ) * (a i j * r j) - p j * r j - b j * r j := by
        intro j
        have : (r j : ℝ) * ∑ i, (q i : ℝ) * a i j = ∑ i, (q i : ℝ) * (a i j * r j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        linear_combination this
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      push_cast
      have h2 : ∀ i, ∑ j, (q i : ℝ) * (a i j * r j) = q i * k i := by
        intro i
        rw [← Finset.mul_sum, hk]
      simp only [h2]
      rw [hs]
    rw [Real.dist_eq, abs_sub_comm, e]
    calc |∑ j, (r j : ℝ) * (∑ i, (q i : ℝ) * a i j - p j - b j)|
        ≤ ∑ j, |(r j : ℝ) * (∑ i, (q i : ℝ) * a i j - p j - b j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |(r j : ℝ)| * (δ / (2 * (∑ j, |(r j : ℝ)| + 1))) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hqp j) (abs_nonneg _)
      _ = (∑ j, |(r j : ℝ)|) * (δ / (2 * (∑ j, |(r j : ℝ)| + 1))) := by rw [Finset.sum_mul]
      _ < δ := by
          have hS : 0 ≤ ∑ j, |(r j : ℝ)| := Finset.sum_nonneg fun j _ => abs_nonneg _
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  rw [(Int.isClosedEmbedding_coe_real.isClosed_range).closure_eq] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨z, hz.symm⟩

/-- Morris, Topology Without Tears, Theorem A5.14.8 (TP-623), sufficiency in dimension `n = 1`. If
every integer relation on the `aᵢ` is integral on `b`, then `b` is approximable by integer combinations
of the `aᵢ` modulo integers. (The case of general `n` needs the annihilator duality `Ω(Ω(G)) = G`
for subgroups of `ℝⁿ`, equivalently that characters of the compact group `𝕋ⁿ / closure G` separate
points; Mathlib has neither.) -/
@[kb "morris2024" "Theorem A5.14.8, p. 605"]
theorem KroneckerRelation.approx_of_dim_one {m : ℕ} {a : Fin m → Fin 1 → ℝ} {b : Fin 1 → ℝ}
    (h : KroneckerRelation a b) : KroneckerApprox a b := by
  let φ : ((Fin m → ℤ) × ℤ) →+ ℝ :=
    { toFun := fun x => ∑ i, (x.1 i : ℝ) * a i 0 - x.2
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
        push_cast
        simp only [add_mul, Finset.sum_add_distrib]
        ring }
  set H : AddSubgroup ℝ := φ.range with hH
  have hmem : ∀ (q : Fin m → ℤ) (p : ℤ), ∑ i, (q i : ℝ) * a i 0 - p ∈ H :=
    fun q p => ⟨(q, p), rfl⟩
  have hdense_to : ∀ ε > 0, (∃ x ∈ H, |x - b 0| < ε) → ∃ (q : Fin m → ℤ) (p : Fin 1 → ℤ),
      ∀ j, |∑ i, (q i : ℝ) * a i j - p j - b j| ≤ ε := by
    rintro ε hε ⟨x, ⟨⟨q, p⟩, rfl⟩, hx⟩
    refine ⟨q, fun _ => p, fun j => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    exact hx.le
  intro ε hε
  rcases (AddSubgroup.dense_or_isCyclic H) with hd | hc
  · apply hdense_to ε hε
    obtain ⟨x, hx, hxH⟩ := Metric.dense_iff.1 hd (b 0) ε hε
    exact ⟨x, hxH, by rwa [Metric.mem_ball, Real.dist_eq] at hx⟩
  · obtain ⟨c, hc⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq _).1 hc
    have hmemc : ∀ x ∈ H, ∃ k : ℤ, x = k * c := by
      intro x hx
      rw [← hc] at hx
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
      exact ⟨k, by rw [← hk]; simp⟩
    have h1H : (1 : ℝ) ∈ H := by simpa using hmem 0 (-1)
    obtain ⟨N, hN⟩ := hmemc _ h1H
    have hak : ∀ i, ∃ k : ℤ, a i 0 = k * c := by
      intro i
      obtain ⟨k, hk⟩ := hmemc _ (hmem (Pi.single i 1) 0)
      refine ⟨k, ?_⟩
      simpa [Pi.single_apply] using hk
    choose k hk using hak
    obtain ⟨t, ht⟩ := h (fun _ => N) (fun i => ⟨k i, by
      simp only [Fin.sum_univ_one]
      rw [hk i]
      linear_combination (-(k i : ℝ)) * hN⟩)
    simp only [Fin.sum_univ_one] at ht
    have hbc : b 0 = t * c := by
      linear_combination (b 0) * hN + c * ht
    have hbH : b 0 ∈ H := by
      rw [← hc]
      exact AddSubgroup.mem_zmultiples_iff.2 ⟨t, by rw [zsmul_eq_mul]; exact hbc.symm⟩
    exact hdense_to ε hε ⟨b 0, hbH, by simpa using hε⟩

theorem irrational_iff_no_integer_relation (θ : ℝ) :
    Irrational θ ↔ ¬ ∃ r h : ℤ, r ≠ 0 ∧ (r : ℝ) * θ = h := by
  constructor
  · rintro hirr ⟨r, h, hr, e⟩
    apply hirr
    refine ⟨(h : ℚ) / r, ?_⟩
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    push_cast
    field_simp
    linarith
  · rintro hn ⟨q, hq⟩
    apply hn
    refine ⟨q.den, q.num, by exact_mod_cast q.den_nz, ?_⟩
    have := congrArg (Rat.cast : ℚ → ℝ) (Rat.mul_den_eq_num q)
    push_cast at this
    rw [← hq, mul_comm]
    exact this

/-- Morris, Topology Without Tears, Corollary A5.14.9 (TP-624), dimension `n = 1`. For a real number
`θ`, every real `x` is approximated within every `ε > 0` by numbers `q θ - p` (`q`, `p` integers) if
and only if there is no relation `r θ = h` with `r`, `h` integers and `r ≠ 0`. -/
@[kb "morris2024" "Corollary A5.14.9, p. 606"]
theorem kronecker_approx_real_iff (θ : ℝ) :
    (∀ x : ℝ, ∀ ε > 0, ∃ q p : ℤ, |(q : ℝ) * θ - p - x| ≤ ε) ↔
      ¬ ∃ r h : ℤ, r ≠ 0 ∧ (r : ℝ) * θ = h := by
  have hd1 := @dense_addSubgroupClosure_pair_iff θ 1
  rw [div_one] at hd1
  rw [← irrational_iff_no_integer_relation, ← hd1]
  have hmem : ∀ y : ℝ, y ∈ (AddSubgroup.closure {θ, (1 : ℝ)}) ↔ ∃ q p : ℤ, (q : ℝ) * θ - p = y := by
    intro y
    rw [AddSubgroup.mem_closure_pair]
    constructor
    · rintro ⟨q, p, rfl⟩
      exact ⟨q, -p, by simp [sub_eq_add_neg]⟩
    · rintro ⟨q, p, rfl⟩
      exact ⟨q, -p, by simp [sub_eq_add_neg]⟩
  constructor
  · intro h
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨q, p, hqp⟩ := h x (r / 2) (by positivity)
    refine ⟨(q : ℝ) * θ - p, ?_, (hmem _).2 ⟨q, p, rfl⟩⟩
    rw [Metric.mem_ball, Real.dist_eq]
    linarith
  · intro hd x ε hε
    obtain ⟨y, hy, hyH⟩ := Metric.dense_iff.1 hd x ε hε
    obtain ⟨q, p, rfl⟩ := (hmem y).1 hyH
    refine ⟨q, p, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hy
    exact hy.le

end Kronecker

end UndergradKB.Topology
