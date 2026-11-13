import UndergradKB.Topology.DualityCompact
import UndergradKB.Topology.ClassicalDuals
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import UndergradKB.Common.Attr

/-!
# Wave 2: Kronecker's theorem and annihilators in `ℝⁿ` (Morris, Appendix 5.14)

Characters of the compact group `Tⁿ` separate a point from a closed subgroup
(`exists_char_trivial_on_ne`); reducing modulo `ℤⁿ` gives the closure criterion in `ℝⁿ` for subgroups
containing `ℤⁿ`, from which Kronecker's theorem (in all dimensions) follows.
-/

open Set Real
open scoped Topology

namespace UndergradKB.Topology

/-! ### The exponential `t ↦ exp (2 π i t)` -/

/-- `t ↦ exp (2 π i t)`, the quotient map `ℝ → ℝ/ℤ = T`. -/
noncomputable def circleE (t : ℝ) : Circle := Circle.exp (2 * π * t)

theorem circleE_add (s t : ℝ) : circleE (s + t) = circleE s * circleE t := by
  unfold circleE; rw [mul_add, Circle.exp_add]

theorem circleE_zero : circleE 0 = 1 := by simp [circleE]

theorem circleE_neg (t : ℝ) : circleE (-t) = (circleE t)⁻¹ := by
  unfold circleE; rw [mul_neg, Circle.exp_neg]

theorem circleE_intCast_mul (k : ℤ) (t : ℝ) : circleE (k * t) = circleE t ^ k := by
  unfold circleE
  rw [show 2 * π * ((k : ℝ) * t) = (k : ℝ) * (2 * π * t) by ring, Circle.exp_intCast_mul]

theorem circleE_eq_one_iff {t : ℝ} : circleE t = 1 ↔ ∃ k : ℤ, t = k := by
  unfold circleE
  rw [Circle.exp_eq_one]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_right_cancel₀ (show (2 * π) ≠ 0 by positivity) ?_⟩
    linarith
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem continuous_circleE : Continuous circleE :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

theorem circleE_surjective : Function.Surjective circleE := by
  intro z
  obtain ⟨s, hs⟩ := Circle.exp_surjective z
  refine ⟨s / (2 * π), ?_⟩
  unfold circleE
  rw [show 2 * π * (s / (2 * π)) = s by field_simp, hs]

theorem isOpenMap_circleE : IsOpenMap circleE := by
  have h1 : IsOpenMap (fun t : ℝ => 2 * π * t) :=
    (Homeomorph.mulLeft₀ (2 * π) (by positivity)).isOpenMap
  exact isLocalHomeomorph_circleExp.isOpenMap.comp h1

theorem prod_circleE {ι : Type*} (s : Finset ι) (c : ι → ℝ) :
    ∏ j ∈ s, circleE (c j) = circleE (∑ j ∈ s, c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleE_zero]
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, circleE_add, ih]

/-- The coordinatewise quotient map `ℝⁿ → Tⁿ`. -/
noncomputable def toTorus {n : ℕ} : (Fin n → ℝ) → (Fin n → Circle) := Pi.map fun _ => circleE

theorem toTorus_apply {n : ℕ} (t : Fin n → ℝ) (j : Fin n) : toTorus t j = circleE (t j) := rfl

theorem toTorus_add {n : ℕ} (s t : Fin n → ℝ) : toTorus (s + t) = toTorus s * toTorus t :=
  funext fun j => circleE_add _ _

theorem toTorus_zero {n : ℕ} : toTorus (0 : Fin n → ℝ) = 1 := funext fun j => circleE_zero

theorem toTorus_neg {n : ℕ} (t : Fin n → ℝ) : toTorus (-t) = (toTorus t)⁻¹ :=
  funext fun j => circleE_neg _

theorem continuous_toTorus {n : ℕ} : Continuous (toTorus (n := n)) :=
  Continuous.piMap fun _ => continuous_circleE

theorem isOpenMap_toTorus {n : ℕ} : IsOpenMap (toTorus (n := n)) :=
  IsOpenMap.piMap (fun _ => isOpenMap_circleE)
    (Filter.Eventually.of_forall fun _ => circleE_surjective)

theorem toTorus_eq_one_iff {n : ℕ} (t : Fin n → ℝ) :
    toTorus t = 1 ↔ ∀ j, ∃ k : ℤ, t j = k := by
  constructor
  · intro h j
    exact circleE_eq_one_iff.1 (congrFun h j)
  · intro h
    funext j
    exact circleE_eq_one_iff.2 (h j)

/-! ### Characters of `Tⁿ` and of `ℝⁿ` -/

/-- Every character of `Tⁿ` is `z ↦ ∏ zⱼ ^ rⱼ` for an integer vector `r`. -/
theorem exists_zpow_form_of_char_circlePow {n : ℕ} (χ : PontryaginDual (Fin n → Circle)) :
    ∃ r : Fin n → ℤ, ∀ z, χ z = ∏ j, z j ^ r j := by
  refine ⟨fun j => circleCharacterExponent
    (PontryaginDual.map (mulSingleHom (G := fun _ : Fin n => Circle) j) χ), fun z => ?_⟩
  have hz : z = ∏ j, Pi.mulSingle j (z j) := (Finset.univ_prod_mulSingle z).symm
  conv_lhs => rw [hz]
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact circleCharacterExponent_spec
    (PontryaginDual.map (mulSingleHom (G := fun _ : Fin n => Circle) j) χ) (z j)

/-- The character `x ↦ exp (2 π i (y | x))` of `ℝⁿ` (written multiplicatively). -/
noncomputable def pairingChar {n : ℕ} (y : Fin n → ℝ) : PontryaginDual (Fin n → Multiplicative ℝ) where
  toFun x := ∏ j, circleE (y j * Multiplicative.toAdd (x j))
  map_one' := by simp [circleE_zero]
  map_mul' x z := by
    simp only [Pi.mul_apply, toAdd_mul, mul_add, circleE_add]
    exact Finset.prod_mul_distrib
  continuous_toFun :=
    continuous_finsetProd _ fun j _ => continuous_circleE.comp
      (continuous_const.mul (continuous_toAdd.comp (continuous_apply j)))

theorem pairingChar_apply_eq_one_iff {n : ℕ} (y x : Fin n → ℝ) :
    pairingChar y (fun j => Multiplicative.ofAdd (x j)) = 1 ↔ ∃ k : ℤ, ∑ j, y j * x j = k := by
  show ∏ j, circleE (y j * x j) = 1 ↔ _
  rw [prod_circleE, circleE_eq_one_iff]

/-- Every character of `ℝⁿ` is a `pairingChar`. -/
theorem exists_pairingChar_eq {n : ℕ} (χ : PontryaginDual (Fin n → Multiplicative ℝ)) :
    ∃ y : Fin n → ℝ, χ = pairingChar y := by
  choose t ht using fun j : Fin n =>
    dual_real_apply (PontryaginDual.map (mulSingleHom (G := fun _ : Fin n => Multiplicative ℝ) j) χ)
  refine ⟨t, PontryaginDual.ext fun x => ?_⟩
  have hz : x = ∏ j, Pi.mulSingle j (x j) := (Finset.univ_prod_mulSingle x).symm
  conv_lhs => rw [hz]
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  have := ht j (Multiplicative.toAdd (x j))
  show _ = circleE (t j * Multiplicative.toAdd (x j))
  have e : circleE (t j * Multiplicative.toAdd (x j)) =
      Circle.exp (2 * π * t j * Multiplicative.toAdd (x j)) := by
    unfold circleE; congr 1; ring
  rw [e]
  exact this

/-- Morris, Topology Without Tears, Proposition A5.14.5 (TP-621). Under the identification of `ℝⁿ` with
its dual group (`y ↦ pairingChar y`, which is onto), the annihilator in the dual of a (not necessarily
closed) subset `G` of `ℝⁿ` consists of the `y` for which `(y | x)` is an integer for every `x ∈ G`. -/
@[kb "morris2024" "Proposition A5.14.5, p. 604"]
theorem annihilator_realPow_iff {n : ℕ} (G : Set (Fin n → ℝ)) :
    ∀ χ : PontryaginDual (Fin n → Multiplicative ℝ),
      (∀ x ∈ G, χ (fun j => Multiplicative.ofAdd (x j)) = 1) ↔
        ∃ y : Fin n → ℝ, χ = pairingChar y ∧ ∀ x ∈ G, ∃ k : ℤ, ∑ j, y j * x j = k := by
  intro χ
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := exists_pairingChar_eq χ
    exact ⟨y, rfl, fun x hx => (pairingChar_apply_eq_one_iff y x).1 (h x hx)⟩
  · rintro ⟨y, rfl, h⟩ x hx
    exact (pairingChar_apply_eq_one_iff y x).2 (h x hx)

/-! ### The closure criterion and Kronecker's theorem -/

/-- A point `x` of `ℝⁿ` for which `(y | x)` is an integer whenever `(y | g)` is an integer for all `g`
in a subgroup `G ⊇ ℤⁿ` lies in the closure of `G`. -/
theorem mem_closure_of_integral_pairing {n : ℕ} (G : AddSubgroup (Fin n → ℝ))
    (hG : ∀ j, (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ G) (x : Fin n → ℝ)
    (h : ∀ y : Fin n → ℝ, (∀ g ∈ G, ∃ k : ℤ, ∑ j, y j * g j = k) → ∃ k : ℤ, ∑ j, y j * x j = k) :
    x ∈ closure (G : Set (Fin n → ℝ)) := by
  classical
  let S : Subgroup (Fin n → Circle) :=
    { carrier := toTorus '' (G : Set (Fin n → ℝ))
      mul_mem' := by
        rintro _ _ ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
        exact ⟨g + g', G.add_mem hg hg', toTorus_add g g'⟩
      one_mem' := ⟨0, G.zero_mem, toTorus_zero⟩
      inv_mem' := by
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨-g, G.neg_mem hg, toTorus_neg g⟩ }
  have hker : toTorus ⁻¹' (toTorus '' (G : Set (Fin n → ℝ))) = G := by
    ext u
    constructor
    · rintro ⟨g, hg, hgu⟩
      have h1 : toTorus (u - g) = 1 := by
        rw [sub_eq_add_neg, toTorus_add, toTorus_neg, ← hgu, mul_inv_cancel]
      choose k hk using (toTorus_eq_one_iff _).1 h1
      have h2 : u - g = ∑ j, k j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
        ext i
        simp [Finset.sum_apply, Pi.single_apply, hk]
      have h3 : u - g ∈ G := by
        rw [h2]
        exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (hG j) _
      simpa using G.add_mem hg h3
    · intro hu
      exact ⟨u, hu, rfl⟩
  have key : toTorus ⁻¹' closure (toTorus '' (G : Set (Fin n → ℝ))) = closure (G : Set (Fin n → ℝ)) := by
    rw [isOpenMap_toTorus.preimage_closure_eq_closure_preimage continuous_toTorus, hker]
  by_contra hx
  have hx' : toTorus x ∉ closure (S : Set (Fin n → Circle)) := by
    intro hm
    apply hx
    rw [← key]
    exact hm
  have hxH : toTorus x ∉ S.topologicalClosure := by
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    exact hx'
  obtain ⟨χ, hχ, hχx⟩ := exists_char_trivial_on_ne S.topologicalClosure
    (Subgroup.isClosed_topologicalClosure S) hxH
  obtain ⟨r, hr⟩ := exists_zpow_form_of_char_circlePow χ
  have hpair : ∀ t : Fin n → ℝ, χ (toTorus t) = circleE (∑ j, (r j : ℝ) * t j) := by
    intro t
    rw [hr, ← prod_circleE]
    refine Finset.prod_congr rfl fun j _ => ?_
    show circleE (t j) ^ r j = circleE (r j * t j)
    rw [circleE_intCast_mul]
  obtain ⟨k, hk⟩ := h (fun j => (r j : ℝ)) (fun g hg => by
    have hgS : toTorus g ∈ S := ⟨g, hg, rfl⟩
    have := hχ (toTorus g) (Subgroup.le_topologicalClosure S hgS)
    rw [hpair, circleE_eq_one_iff] at this
    exact this)
  apply hχx
  rw [hpair, circleE_eq_one_iff]
  exact ⟨k, hk⟩

/-- Morris, Topology Without Tears, Proposition A5.14.7 (TP-622), the easy direction, for any subgroup
`G` of `ℝⁿ`: a point of the closure of `G` has integral pairing with every `y` that pairs integrally with
`G`. -/
@[kb "morris2024" "Proposition A5.14.7, p. 604"]
theorem integral_pairing_of_mem_closure {n : ℕ} (G : AddSubgroup (Fin n → ℝ)) {x : Fin n → ℝ}
    (hx : x ∈ closure (G : Set (Fin n → ℝ))) (y : Fin n → ℝ)
    (hy : ∀ g ∈ G, ∃ k : ℤ, ∑ j, y j * g j = k) : ∃ k : ℤ, ∑ j, y j * x j = k := by
  have hcont : Continuous fun z : Fin n → ℝ => ∑ j, y j * z j := by fun_prop
  have hclosed : IsClosed ((fun z : Fin n → ℝ => ∑ j, y j * z j) ⁻¹' range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isClosed_range.preimage hcont
  have hsub : (G : Set (Fin n → ℝ)) ⊆ (fun z : Fin n → ℝ => ∑ j, y j * z j) ⁻¹' range ((↑) : ℤ → ℝ) := by
    intro g hg
    obtain ⟨k, hk⟩ := hy g hg
    exact ⟨k, hk.symm⟩
  obtain ⟨k, hk⟩ := closure_minimal hsub hclosed hx
  exact ⟨k, hk.symm⟩

/-- Morris, Topology Without Tears, Proposition A5.14.7 (TP-622), for subgroups `G ⊇ ℤⁿ` (the case used
for Kronecker's theorem): `x` lies in the closure of `G` iff `(y | x)` is an integer for every `y` with
`(y | g)` an integer for all `g ∈ G`. -/
@[kb "morris2024" "Proposition A5.14.7, p. 604"]
theorem mem_closure_iff_integral_pairing {n : ℕ} (G : AddSubgroup (Fin n → ℝ))
    (hG : ∀ j, (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ G) (x : Fin n → ℝ) :
    x ∈ closure (G : Set (Fin n → ℝ)) ↔
      ∀ y : Fin n → ℝ, (∀ g ∈ G, ∃ k : ℤ, ∑ j, y j * g j = k) → ∃ k : ℤ, ∑ j, y j * x j = k :=
  ⟨fun hx y hy => integral_pairing_of_mem_closure G hx y hy,
    mem_closure_of_integral_pairing G hG x⟩

/-- Morris, Topology Without Tears, Theorem A5.14.8 (TP-623), sufficiency, all `n` and `m`. If every
integer relation on the `aᵢ` is integral on `b`, then `b` is approximable by integer combinations of the
`aᵢ` modulo integers. -/
@[kb "morris2024" "Theorem A5.14.8, p. 605"]
theorem KroneckerRelation.approx {m n : ℕ} {a : Fin m → Fin n → ℝ} {b : Fin n → ℝ}
    (h : KroneckerRelation a b) : KroneckerApprox a b := by
  classical
  let G : AddSubgroup (Fin n → ℝ) :=
    { carrier := {x | ∃ (q : Fin m → ℤ) (p : Fin n → ℤ), ∀ j, x j = ∑ i, (q i : ℝ) * a i j - p j}
      zero_mem' := ⟨0, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨q, p, hq⟩ ⟨q', p', hq'⟩
        refine ⟨q + q', p + p', fun j => ?_⟩
        simp only [Pi.add_apply, hq j, hq' j, Pi.add_apply, Int.cast_add, add_mul,
          Finset.sum_add_distrib]
        ring
      neg_mem' := by
        rintro _ ⟨q, p, hq⟩
        refine ⟨-q, -p, fun j => ?_⟩
        simp [hq j, Finset.sum_neg_distrib]
        ring }
  have hGe : ∀ j, (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ G := by
    intro j
    refine ⟨0, -Pi.single j 1, fun j' => ?_⟩
    simp [Pi.single_apply]
  have hGa : ∀ i, (fun j => a i j) ∈ G := by
    intro i
    refine ⟨Pi.single i 1, 0, fun j => ?_⟩
    simp [Pi.single_apply]
  have hb : b ∈ closure (G : Set (Fin n → ℝ)) := by
    refine mem_closure_of_integral_pairing G hGe b fun y hy => ?_
    have hint : ∀ j, ∃ k : ℤ, y j = k := by
      intro j
      obtain ⟨k, hk⟩ := hy _ (hGe j)
      refine ⟨k, ?_⟩
      simpa [Pi.single_apply] using hk
    choose r hr using hint
    have hrel : ∀ i, ∃ k : ℤ, ∑ j, a i j * r j = k := by
      intro i
      obtain ⟨k, hk⟩ := hy _ (hGa i)
      refine ⟨k, ?_⟩
      rw [← hk]
      exact Finset.sum_congr rfl fun j _ => by rw [hr j]; ring
    obtain ⟨k, hk⟩ := h r hrel
    refine ⟨k, ?_⟩
    rw [← hk]
    exact Finset.sum_congr rfl fun j _ => by rw [hr j]; ring
  intro ε hε
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.1 hb ε hε
  obtain ⟨q, p, hq⟩ := hg
  refine ⟨q, p, fun j => ?_⟩
  have h1 : dist (b j) (g j) ≤ dist b g := dist_le_pi_dist b g j
  rw [Real.dist_eq] at h1
  have h2 : ∑ i, (q i : ℝ) * a i j - p j - b j = g j - b j := by rw [hq j]
  rw [h2, abs_sub_comm]
  exact h1.trans hdist.le

/-- Morris, Topology Without Tears, Theorem A5.14.8 (TP-623), Kronecker's theorem. For points
`a₁, …, a_m` and `b` of `ℝⁿ`, `b` is approximable by `∑ qᵢ aᵢ − p` (integers `qᵢ`, `pⱼ`) to within every
`ε > 0` iff every integer vector `r` with all `∑ⱼ aᵢⱼ rⱼ` integral has `∑ⱼ bⱼ rⱼ` integral. -/
@[kb "morris2024" "Theorem A5.14.8, p. 605"]
theorem kronecker_approx_iff_relation {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin n → ℝ) :
    KroneckerApprox a b ↔ KroneckerRelation a b :=
  ⟨KroneckerApprox.relation, KroneckerRelation.approx⟩

/-- Morris, Topology Without Tears, Corollary A5.14.9 (TP-624). For reals `θ₁, …, θₙ`: every point
`x ∈ ℝⁿ` is approximable by `q θ − p` (integers `q`, `pⱼ`) to within every `ε > 0` iff there is no relation
`∑ rⱼ θⱼ = h` with integers `rⱼ`, `h`, not all `rⱼ` zero. -/
@[kb "morris2024" "Corollary A5.14.9, p. 606"]
theorem kronecker_approx_iff_no_relation {n : ℕ} (θ : Fin n → ℝ) :
    (∀ x : Fin n → ℝ, ∀ ε > 0, ∃ (q : ℤ) (p : Fin n → ℤ), ∀ j, |(q : ℝ) * θ j - p j - x j| ≤ ε) ↔
      ∀ (r : Fin n → ℤ) (h : ℤ), ∑ j, (r j : ℝ) * θ j = h → ∀ j, r j = 0 := by
  classical
  let a : Fin 1 → Fin n → ℝ := fun _ => θ
  constructor
  · intro hap r h hrel
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ := hcon
    let b : Fin n → ℝ := fun j => if j = k then 1 / (2 * (r k : ℝ)) else 0
    have happ : KroneckerApprox a b := by
      intro ε hε
      obtain ⟨q, p, hqp⟩ := hap b ε hε
      exact ⟨fun _ => q, p, fun j => by simpa [a] using hqp j⟩
    have hrelb := happ.relation r (fun i => ⟨h, by
      rw [← hrel]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _⟩)
    obtain ⟨k', hk'⟩ := hrelb
    have hrk : (r k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hsum : ∑ j, b j * r j = 1 / 2 := by
      rw [Finset.sum_eq_single k]
      · simp [b]; field_simp
      · intro j _ hj; simp [b, hj]
      · intro hk0; exact absurd (Finset.mem_univ k) hk0
    rw [hsum] at hk'
    have : (2 * k' : ℝ) = 1 := by linarith
    have : (2 * k' : ℤ) = 1 := by exact_mod_cast this
    omega
  · intro hno x ε hε
    have hrel : KroneckerRelation a x := by
      intro r hr
      obtain ⟨k, hk⟩ := hr 0
      have hr0 : ∀ j, r j = 0 := hno r k (by
        rw [← hk]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
      exact ⟨0, by simp [hr0]⟩
    obtain ⟨q, p, hqp⟩ := hrel.approx ε hε
    exact ⟨q 0, p, fun j => by simpa [a] using hqp j⟩

end UndergradKB.Topology
