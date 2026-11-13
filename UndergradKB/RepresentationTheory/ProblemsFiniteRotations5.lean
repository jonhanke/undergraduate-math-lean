import UndergradKB.Common.Attr
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Alternating
import UndergradKB.RepresentationTheory.ProblemsFiniteRotations4

/-! # Problem 3.24: identification of the finite subgroups of `SO(3)`

Using the orbit data of the poles we identify the cyclic, dihedral, tetrahedral and octahedral groups.
-/

namespace UndergradKB.RepresentationTheory

open Matrix SO3Rot

namespace FiniteRotations

/-- Orbit data of the poles of `H`, with the connection to the points: the orbits are indexed by `κ`,
`mk` sends a pole to its orbit, and `m` is the order of the stabilizer. -/
theorem pole_data (H : Subgroup SO3) [Fintype H] :
    ∃ (κ : Type) (_ : Fintype κ) (m : κ → ℕ) (mk : poles H → κ),
      (∀ k, 2 ≤ m k ∧ m k ∣ Fintype.card H) ∧
      ∑ k, ((1 : ℚ) - 1 / (m k : ℚ)) = 2 - 2 / (Fintype.card H : ℚ) ∧
      Function.Surjective mk ∧
      (∀ q, m (mk q) = Nat.card (MulAction.stabilizer H (q : Sph))) ∧
      (∀ q q', mk q = mk q' → ∃ h : H, h • (q : Sph) = (q' : Sph)) := by
  classical
  have hfin : Finite (poles H) := (poles_finite H).to_subtype
  haveI : Fintype (poles H) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient H (poles H)) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H (poles H)
  have hclass := MulAction.card_eq_sum_card_group_div_card_stabilizer H (poles H)
  have hn : 0 < Fintype.card H := Fintype.card_pos
  have hsum : ∑ g : H, Fintype.card (MulAction.fixedBy (poles H) g) =
      Fintype.card (poles H) + 2 * (Fintype.card H - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H))]
    have h1 : Fintype.card (MulAction.fixedBy (poles H) (1 : H)) = Fintype.card (poles H) := by
      exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun x ↦ by simp)
    rw [h1]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => 2)]
    · simp [Finset.card_erase_of_mem, mul_comm]
    · intro g hg
      rw [← Nat.card_eq_fintype_card]
      exact card_fixedBy_nontrivial H g (Finset.ne_of_mem_erase hg)
  refine ⟨MulAction.orbitRel.Quotient H (poles H), inferInstance,
    fun ω ↦ Fintype.card (MulAction.stabilizer H ω.out), Quotient.mk'', fun ω ↦ ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h, hh, hfix⟩ := ω.out.2
    rw [Nat.succ_le_iff, Fintype.one_lt_card_iff]
    refine ⟨⟨h, ?_⟩, 1, fun e ↦ hh (congrArg Subtype.val e)⟩
    exact Subtype.ext hfix
  · have := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer H ω.out)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  · have hdiv : ∀ ω : MulAction.orbitRel.Quotient H (poles H),
        Fintype.card (MulAction.stabilizer H ω.out) ∣ Fintype.card H := by
      intro ω
      have := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer H ω.out)
      rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    have hm0 : ∀ ω : MulAction.orbitRel.Quotient H (poles H),
        (Fintype.card (MulAction.stabilizer H ω.out) : ℚ) ≠ 0 := fun ω ↦
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hclassQ : (Fintype.card (poles H) : ℚ) =
        ∑ ω : MulAction.orbitRel.Quotient H (poles H),
          (Fintype.card H : ℚ) / Fintype.card (MulAction.stabilizer H ω.out) := by
      rw [hclass]
      push_cast
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [Nat.cast_div (hdiv ω) (hm0 ω)]
    have hburnQ : (Fintype.card (poles H) : ℚ) + 2 * ((Fintype.card H : ℚ) - 1) =
        Fintype.card (MulAction.orbitRel.Quotient H (poles H)) * Fintype.card H := by
      have := congrArg (Nat.cast : ℕ → ℚ) (hsum.symm.trans hburn)
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one] at this
      simpa using this
    have e1 : ∑ ω : MulAction.orbitRel.Quotient H (poles H),
        ((1 : ℚ) - 1 / (Fintype.card (MulAction.stabilizer H ω.out) : ℚ)) =
        Fintype.card (MulAction.orbitRel.Quotient H (poles H)) -
          ∑ ω : MulAction.orbitRel.Quotient H (poles H), 1 / (Fintype.card (MulAction.stabilizer H ω.out) : ℚ) := by
      simp [Finset.sum_sub_distrib]
    have e2 : (Fintype.card H : ℚ) * ∑ ω : MulAction.orbitRel.Quotient H (poles H),
        1 / (Fintype.card (MulAction.stabilizer H ω.out) : ℚ) = Fintype.card (poles H) := by
      rw [hclassQ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ω _ ↦ by ring
    have hnq : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    show ∑ ω : MulAction.orbitRel.Quotient H (poles H),
        ((1 : ℚ) - 1 / (Fintype.card (MulAction.stabilizer H ω.out) : ℚ)) = _
    rw [e1]
    field_simp
    linear_combination (-1) * hburnQ - e2
  · exact Quotient.mk''_surjective
  · intro q
    have hrel : (Quotient.mk'' q : MulAction.orbitRel.Quotient H (poles H)).out ∈ MulAction.orbit H q := by
      have := Quotient.mk_out (s := MulAction.orbitRel H (poles H)) q
      exact MulAction.orbitRel_apply.mp this
    have horb : MulAction.orbit H (Quotient.mk'' q : MulAction.orbitRel.Quotient H (poles H)).out =
        MulAction.orbit H q := MulAction.orbit_eq_iff.mpr hrel
    set o := (Quotient.mk'' q : MulAction.orbitRel.Quotient H (poles H)).out with ho
    have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H o
    have h2 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H q
    have hpos : 0 < Fintype.card (MulAction.orbit H q) :=
      Fintype.card_pos_iff.mpr ⟨⟨q, MulAction.mem_orbit_self q⟩⟩
    have e : Fintype.card (MulAction.orbit H o) = Fintype.card (MulAction.orbit H q) :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x ↦ by rw [horb])
    have : Fintype.card (MulAction.stabilizer H o) = Fintype.card (MulAction.stabilizer H q) := by
      rw [e] at h1
      exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    show Fintype.card (MulAction.stabilizer H o) = Nat.card (MulAction.stabilizer H (q : Sph))
    rw [this, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun h ↦ by
      simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff])
  · intro q q' h
    have := Quotient.exact h
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp this
    have hv : (q : Sph) = g • (q' : Sph) := (congrArg Subtype.val hg).symm
    exact ⟨g⁻¹, by rw [hv, inv_smul_smul]⟩

/-! ### Recognition of the dihedral group -/

/-- A finite group of order `2 r` with a cyclic subgroup `S` of order `r` such that every element outside `S`
squares to `1` is dihedral. -/
theorem dihedral_of_index_two {G : Type*} [Group G] [Fintype G] (S : Subgroup G) (hcyc : IsCyclic S)
    (r : ℕ) [NeZero r] (hS : Nat.card S = r) (hG : Nat.card G = 2 * r)
    (hinv : ∀ g : G, g ∉ S → g * g = 1) : Nonempty (G ≃* DihedralGroup r) := by
  classical
  obtain ⟨c0, hc0⟩ := hcyc.exists_generator
  set c : G := (c0 : G) with hcdef
  have hord : orderOf c = r := by
    rw [hcdef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hc0, hS]
  have hcS : ∀ i : ℕ, c ^ i ∈ S := fun i ↦ S.pow_mem c0.2 i
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  obtain ⟨g0, hg0S⟩ : ∃ g0 : G, g0 ∉ S := by
    by_contra hcon
    push Not at hcon
    have : S = ⊤ := eq_top_iff.mpr fun x _ ↦ hcon x
    rw [this, Subgroup.card_top] at hS
    omega
  have hg0 : g0 * g0 = 1 := hinv g0 hg0S
  let cp : ZMod r → G := fun i ↦ c ^ i.val
  have cp_add : ∀ i j, cp (i + j) = cp i * cp j := by
    intro i j
    simp only [cp, ZMod.val_add, ← pow_add]
    have := pow_mod_orderOf c (i.val + j.val)
    rwa [hord] at this
  have cp_zero : cp 0 = 1 := by simp [cp]
  have cp_neg : ∀ i, cp (-i) = (cp i)⁻¹ := by
    intro i
    apply eq_inv_of_mul_eq_one_right
    rw [← cp_add, add_neg_cancel, cp_zero]
  have cp_mem : ∀ i, cp i ∈ S := fun i ↦ hcS _
  have hconj : ∀ i, g0 * cp i * g0 = cp (-i) := by
    intro i
    have hnot : g0 * cp i ∉ S := fun h ↦ hg0S (by
      have := S.mul_mem h (S.inv_mem (cp_mem i))
      simpa using this)
    have h1 := hinv _ hnot
    rw [cp_neg]
    apply eq_inv_of_mul_eq_one_left
    calc g0 * cp i * g0 * cp i = (g0 * cp i) * (g0 * cp i) := by simp only [mul_assoc]
      _ = 1 := h1
  have hcomm : ∀ i, cp i * g0 = g0 * cp (-i) := by
    intro i
    calc cp i * g0 = g0 * (g0 * cp i * g0) := by
          calc cp i * g0 = (g0 * g0) * cp i * g0 := by rw [hg0, one_mul]
            _ = g0 * (g0 * cp i * g0) := by simp only [mul_assoc]
      _ = g0 * cp (-i) := by rw [hconj]
  let φ : DihedralGroup r →* G :=
    { toFun := fun x ↦ match x with
        | DihedralGroup.r i => cp i
        | DihedralGroup.sr i => g0 * cp i
      map_one' := by rw [DihedralGroup.one_def]; exact cp_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · simp only [DihedralGroup.r_mul_r]; exact cp_add _ _
        · simp only [DihedralGroup.r_mul_sr]
          calc g0 * cp (j - i) = g0 * (cp (-i) * cp j) := by rw [sub_eq_add_neg, add_comm, cp_add]
            _ = (g0 * cp (-i)) * cp j := (mul_assoc _ _ _).symm
            _ = (cp i * g0) * cp j := by rw [hcomm]
            _ = cp i * (g0 * cp j) := by simp only [mul_assoc]
        · simp only [DihedralGroup.sr_mul_r]
          rw [cp_add, mul_assoc]
        · simp only [DihedralGroup.sr_mul_sr]
          calc cp (j - i) = cp (-i) * cp j := by rw [sub_eq_add_neg, add_comm, cp_add]
            _ = (g0 * cp i * g0) * cp j := by rw [hconj]
            _ = g0 * cp i * (g0 * cp j) := by simp only [mul_assoc] }
  have hinj : Function.Injective φ := by
    have hcpinj : ∀ i j, cp i = cp j → i = j := by
      intro i j h
      have hi : i.val < orderOf c := by rw [hord]; exact ZMod.val_lt i
      have hj : j.val < orderOf c := by rw [hord]; exact ZMod.val_lt j
      exact ZMod.val_injective r (pow_injOn_Iio_orderOf hi hj h)
    rintro (i | i) (j | j) h
    · exact congrArg _ (hcpinj _ _ h)
    · exfalso
      have e : g0 = cp i * (cp j)⁻¹ := by
        have h' : cp i = g0 * cp j := h
        rw [h', mul_inv_cancel_right]
      exact hg0S (e ▸ S.mul_mem (cp_mem i) (S.inv_mem (cp_mem j)))
    · exfalso
      have e : g0 = cp j * (cp i)⁻¹ := by
        have h' : g0 * cp i = cp j := h
        rw [← h', mul_inv_cancel_right]
      exact hg0S (e ▸ S.mul_mem (cp_mem j) (S.inv_mem (cp_mem i)))
    · exact congrArg _ (hcpinj _ _ (mul_left_cancel h))
  have hcard : Fintype.card (DihedralGroup r) = Fintype.card G := by
    rw [DihedralGroup.card, ← Nat.card_eq_fintype_card, hG]
  exact ⟨(MulEquiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)).symm⟩

/-! ### Cyclic stabilizers and the dihedral case -/

/-- The stabilizer in `H` of a unit vector is cyclic. -/
theorem stabilizer_isCyclic (H : Subgroup SO3) [Finite H] (q : Sph) :
    IsCyclic (MulAction.stabilizer H q) := by
  let K : Subgroup SO3 := (MulAction.stabilizer H q).map H.subtype
  let e : MulAction.stabilizer H q ≃* K :=
    Subgroup.equivMapOfInjective _ H.subtype Subtype.val_injective
  haveI : Finite K := Finite.of_equiv _ e.toEquiv
  have hK : IsCyclic K := by
    refine isCyclic_of_fix K q.1 q.2 fun h ↦ ?_
    obtain ⟨x, hx, hxh⟩ := h.2
    have : ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = (((x : H) : SO3) : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [← hxh]; rfl
    rw [this]
    exact congrArg Subtype.val ((MulAction.mem_stabilizer_iff (G := H) (α := Sph)).mp hx)
  exact (MulEquiv.isCyclic e).mpr hK

/-- If the value `r ≠ 2` occurs once in the multiset of the `m k`, there is only one `k` with `m k = r`. -/
theorem eq_of_count_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] (m : κ → ℕ) (r : ℕ)
    (h : (Finset.univ.val.map m).count r = 1) {k k' : κ} (hk : m k = r) (hk' : m k' = r) : k = k' := by
  rw [Multiset.count_map] at h
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
  have h1 : k ∈ Multiset.filter (fun x ↦ r = m x) Finset.univ.val := by simp [hk]
  have h2 : k' ∈ Multiset.filter (fun x ↦ r = m x) Finset.univ.val := by simp [hk']
  rw [ha] at h1 h2
  rw [Multiset.mem_singleton] at h1 h2
  rw [h1, h2]

theorem mul_self_eq_one_of_card_two {G : Type*} [Group G] (T : Subgroup G) (hT : Nat.card T = 2) {g : G}
    (hg : g ∈ T) : g * g = 1 := by
  have := pow_card_eq_one' (G := T) (x := ⟨g, hg⟩)
  rw [hT] at this
  have h2 := congrArg Subtype.val this
  simpa [pow_two] using h2

/-- **The dihedral case.** If the orbit data of the poles of `H` is `{2, 2, r}` with `|H| = 2 r`, then `H` is
dihedral of order `2 r`. -/
theorem dihedral_case (H : Subgroup SO3) [Fintype H] {κ : Type} [Fintype κ] (m : κ → ℕ) (mk : poles H → κ)
    (hsurj : Function.Surjective mk) (hmk : ∀ q, m (mk q) = Nat.card (MulAction.stabilizer H (q : Sph)))
    (hmk2 : ∀ q q', mk q = mk q' → ∃ h : H, h • (q : Sph) = (q' : Sph))
    (r : ℕ) (hr2 : 2 ≤ r) (hn : Fintype.card H = 2 * r) (hM : Finset.univ.val.map m = {2, 2, r}) :
    Nonempty (H ≃* DihedralGroup r) := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  have hrmem : r ∈ Finset.univ.val.map m := by rw [hM]; simp
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hrmem
  obtain ⟨p, hp⟩ := hsurj k
  set S : Subgroup H := MulAction.stabilizer H (p : Sph) with hSdef
  have hS : Nat.card S = r := by rw [← hk, ← hp, hmk p]
  have hG : Nat.card H = 2 * r := by rw [Nat.card_eq_fintype_card]; exact hn
  have hindex : S.index = 2 := by
    have := Subgroup.card_mul_index S
    rw [hS, hG] at this
    have hr0 : 0 < r := by omega
    nlinarith
  haveI : S.Normal := Subgroup.normal_of_index_eq_two hindex
  refine dihedral_of_index_two S (stabilizer_isCyclic H p) r hS hG ?_
  intro g hgS
  have hg1 : g ≠ 1 := fun h ↦ hgS (h ▸ S.one_mem)
  obtain ⟨a, b, hne, hab⟩ := fixed_two (g : SO3) (fun e ↦ hg1 (Subtype.ext e))
  have hga : g • a = a := (hab a).mpr (Or.inl rfl)
  have ha : a ∈ poles H := ⟨g, hg1, hga⟩
  have hgmem : g ∈ MulAction.stabilizer H a := MulAction.mem_stabilizer_iff.mpr hga
  have hmq : m (mk ⟨a, ha⟩) = Nat.card (MulAction.stabilizer H a) := hmk ⟨a, ha⟩
  have hin : m (mk ⟨a, ha⟩) ∈ Finset.univ.val.map m := Multiset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
  rw [hM] at hin
  have hcases : m (mk ⟨a, ha⟩) = 2 ∨ m (mk ⟨a, ha⟩) = r := by simpa using hin
  by_cases hr : r = 2
  · have h2 : Nat.card (MulAction.stabilizer H a) = 2 := by
      rw [← hmq]; rcases hcases with h | h <;> omega
    exact mul_self_eq_one_of_card_two _ h2 hgmem
  · rcases hcases with h | h
    · exact mul_self_eq_one_of_card_two _ (by rw [← hmq]; exact h) hgmem
    · exfalso
      have hcount : (Finset.univ.val.map m).count r = 1 := by
        rw [hM]
        simp [Multiset.count_cons, hr, Ne.symm hr]
      have hkk : mk ⟨a, ha⟩ = mk p := eq_of_count_eq_one m r hcount h (hp ▸ hk)
      obtain ⟨h0, hh0⟩ := hmk2 _ _ hkk
      -- `h0 • a = p`, so `g` conjugated by `h0` lies in the stabilizer `S` of `p`
      have hpa : (p : Sph) = h0 • a := hh0.symm
      have hconj : h0 * g * h0⁻¹ ∈ S := by
        rw [hSdef, MulAction.mem_stabilizer_iff, hpa, ← mul_smul, show h0 * g * h0⁻¹ * h0 = h0 * g by group,
          mul_smul, hga]
      have := (inferInstance : S.Normal).conj_mem _ hconj h0⁻¹
      apply hgS
      simpa [mul_assoc] using this

/-! ### The tetrahedral case -/

open Equiv in
/-- A subgroup of `S₄` of order `12` is `A₄`. -/
theorem eq_alternating_of_card_twelve (K : Subgroup (Perm (Fin 4))) (hK : Nat.card K = 12) :
    K = alternatingGroup (Fin 4) := by
  have hperm : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide
  have hindex : K.index = 2 := by
    have := Subgroup.card_mul_index K
    rw [hK, hperm] at this
    omega
  have hle : alternatingGroup (Fin 4) ≤ K := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      rw [← hσ.orderOf]; exact pow_orderOf_eq_one σ
    have : σ = σ ^ 2 * σ ^ 2 := by
      calc σ = σ * σ ^ 3 := by rw [h3, mul_one]
        _ = σ ^ 2 * σ ^ 2 := by group
    rw [this]
    exact Subgroup.mul_self_mem_of_index_two hindex _
  have hA : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    have := two_mul_nat_card_alternatingGroup (α := Fin 4)
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hK])).symm

/-- The orbit of a unit vector under `H`, as an `H`-stable subset of `Sph`. -/
def orbitSub (H : Subgroup SO3) (q : Sph) : SubMulAction H Sph where
  carrier := MulAction.orbit H q
  smul_mem' := by
    rintro g x ⟨h, rfl⟩
    exact ⟨g * h, mul_smul _ _ _⟩

theorem finite_orbitSub (H : Subgroup SO3) [Finite H] (q : Sph) : Finite (orbitSub H q) :=
  Finite.of_surjective (fun h : H ↦ (⟨h • q, h, rfl⟩ : orbitSub H q))
    (by rintro ⟨x, h, rfl⟩; exact ⟨h, rfl⟩)

theorem card_orbitSub_mul (H : Subgroup SO3) [Fintype H] (q : Sph) :
    Nat.card (orbitSub H q) * Nat.card (MulAction.stabilizer H q) = Nat.card H := by
  classical
  haveI : Finite (orbitSub H q) := finite_orbitSub H q
  haveI : Finite (MulAction.orbit H q) := finite_orbitSub H q
  haveI : Fintype (MulAction.orbit H q) := Fintype.ofFinite _
  have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H q
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this
  exact this

/-- The action of `H` on the orbit of a pole is faithful if the orbit has more than two points. -/
theorem injective_toPermHom_orbitSub (H : Subgroup SO3) [Finite H] (q : Sph)
    (hcard : 2 < Nat.card (orbitSub H q)) : Function.Injective (MulAction.toPermHom H (orbitSub H q)) := by
  classical
  haveI : Finite (orbitSub H q) := finite_orbitSub H q
  haveI : Fintype (orbitSub H q) := Fintype.ofFinite _
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hg1
  obtain ⟨a, b, -, hab⟩ := fixed_two (g : SO3) (fun e ↦ hg1 (Subtype.ext e))
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hcard
  have hfix : ∀ w : orbitSub H q, w.1 = a ∨ w.1 = b := fun w ↦ by
    apply (hab w.1).mp
    have := congrArg (fun σ : Equiv.Perm (orbitSub H q) ↦ σ w) hg
    exact congrArg Subtype.val this
  have hx := hfix x
  have hy := hfix y
  have hz := hfix z
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  all_goals first
    | exact hxy (Subtype.ext (hx.trans hy.symm))
    | exact hxz (Subtype.ext (hx.trans hz.symm))
    | exact hyz (Subtype.ext (hy.trans hz.symm))

/-- **The tetrahedral case.**  A finite subgroup of `SO(3)` of order `12` having a pole with stabilizer of order
`3` is isomorphic to `A₄`. -/
theorem alternating_case (H : Subgroup SO3) [Fintype H] (hn : Fintype.card H = 12) (q : Sph)
    (hs : Nat.card (MulAction.stabilizer H q) = 3) : Nonempty (H ≃* alternatingGroup (Fin 4)) := by
  classical
  haveI : Finite (orbitSub H q) := finite_orbitSub H q
  haveI : Fintype (orbitSub H q) := Fintype.ofFinite _
  have hO : Nat.card (orbitSub H q) = 4 := by
    have := card_orbitSub_mul H q
    have hn' : Nat.card H = 12 := by rw [Nat.card_eq_fintype_card]; exact hn
    rw [hs, hn'] at this
    omega
  have hinj := injective_toPermHom_orbitSub H q (by omega)
  have e : orbitSub H q ≃ Fin 4 := Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hO)
  let ψ : H →* Equiv.Perm (Fin 4) := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H (orbitSub H q))
  have hψ : Function.Injective ψ := e.permCongrHom.injective.comp hinj
  let iso : H ≃* ψ.range := MonoidHom.ofInjective hψ
  have hK : Nat.card ψ.range = 12 := by
    rw [← Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card, hn]
  have hKA : ψ.range = alternatingGroup (Fin 4) := eq_alternating_of_card_twelve _ hK
  exact ⟨iso.trans (MulEquiv.subgroupCongr hKA)⟩

/-! ### The octahedral case -/

/-- The antipodal unit vector. -/
def negS (x : Sph) : Sph := ⟨-x.1, by simpa using x.2⟩

theorem negS_val (x : Sph) : (negS x).1 = -x.1 := rfl

theorem negS_negS (x : Sph) : negS (negS x) = x := Subtype.ext (by simp [negS_val])

theorem negS_ne_self (x : Sph) : negS x ≠ x := by
  intro h
  have h1 : -x.1 = x.1 := congrArg Subtype.val h
  have : x.1 = 0 := by
    funext i
    have := congrFun h1 i
    simp only [Pi.neg_apply] at this
    simp only [Pi.zero_apply]
    linarith
  have h2 := x.2
  rw [this] at h2
  simp at h2

theorem smul_negS (H : Subgroup SO3) (h : H) (x : Sph) : h • negS x = negS (h • x) :=
  Subtype.ext (by
    show ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (-x.1) = -(((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.1)
    rw [Matrix.mulVec_neg])

open Pointwise

/-- The axis `{x, -x}` of a unit vector. -/
def axis (x : Sph) : Set Sph := {x, negS x}

theorem smul_axis (H : Subgroup SO3) (h : H) (x : Sph) : h • axis x = axis (h • x) := by
  simp [axis, Set.smul_set_insert, Set.smul_set_singleton, smul_negS]

theorem axis_eq_iff (x y : Sph) : axis x = axis y ↔ y = x ∨ y = negS x := by
  constructor
  · intro h
    have : y ∈ axis x := by rw [h]; exact Or.inl rfl
    simpa [axis] using this
  · rintro (rfl | rfl)
    · rfl
    · simp [axis, Set.pair_comm, negS_negS]

/-- The orbit of a point of any `H`-set, as an `H`-stable subset. -/
def orbitSubG (H : Subgroup SO3) {X : Type} [MulAction H X] (x : X) : SubMulAction H X where
  carrier := MulAction.orbit H x
  smul_mem' := by
    rintro g y ⟨h, rfl⟩
    exact ⟨g * h, mul_smul _ _ _⟩

/-- A nontrivial element cannot fix three distinct unit vectors. -/
theorem fixes_three (g : SO3) (hg : g ≠ 1) {x y z : Sph} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : g • x = x) (hy : g • y = y) (hz : g • z = z) : False := by
  obtain ⟨a, b, -, hab⟩ := fixed_two g hg
  rcases (hab x).mp hx with h1 | h1 <;> rcases (hab y).mp hy with h2 | h2 <;>
    rcases (hab z).mp hz with h3 | h3
  all_goals first
    | exact hxy (h1.trans h2.symm)
    | exact hxz (h1.trans h3.symm)
    | exact hyz (h2.trans h3.symm)

theorem card_stab_smul (H : Subgroup SO3) (h : H) (x : Sph) :
    Nat.card (MulAction.stabilizer H (h • x)) = Nat.card (MulAction.stabilizer H x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj h).injective

theorem ncard_orbit_eq (H : Subgroup SO3) (x : Sph) :
    Nat.card (orbitSub H x) = (MulAction.orbit H x).ncard := Nat.card_coe_set_eq _

/-- An element of `H` that stabilizes every axis `{h q₀, -h q₀}` and is nontrivial acts as `-1` on the
orbit of `q₀` (when stabilizers in the orbit have order `3` and the orbit has more than two points). -/
theorem kernel_neg (H : Subgroup SO3) [Finite H] (q0 : Sph) (hs3 : Nat.card (MulAction.stabilizer H q0) = 3)
    (hO : 2 < (MulAction.orbit H q0).ncard) (g : H)
    (hP : ∀ h : H, g • axis (h • q0) = axis (h • q0)) (hg : g ≠ 1) :
    ∀ x ∈ MulAction.orbit H q0, g • x = negS x := by
  classical
  have hax : ∀ x ∈ MulAction.orbit H q0, g • x = x ∨ g • x = negS x := by
    rintro x ⟨h, rfl⟩
    have : g • (h • q0) ∈ axis (h • q0) := by
      rw [← hP h]
      exact Set.smul_mem_smul_set (Or.inl rfl)
    simpa [axis] using this
  rintro x hx
  rcases hax x hx with h1 | h1
  · exfalso
    obtain ⟨h, rfl⟩ := hx
    have hcard : Nat.card (MulAction.stabilizer H (h • q0)) = 3 := by rw [card_stab_smul, hs3]
    have hg3 : g ^ 3 = 1 := by
      have := pow_card_eq_one' (G := MulAction.stabilizer H (h • q0)) (x := ⟨g, MulAction.mem_stabilizer_iff.mpr h1⟩)
      rw [hcard] at this
      exact congrArg Subtype.val this
    -- a second point of the orbit
    obtain ⟨x', hx', hne1, hne2⟩ : ∃ x' ∈ MulAction.orbit H q0, x' ≠ h • q0 ∧ x' ≠ negS (h • q0) := by
      by_contra hcon
      push Not at hcon
      have hsub : MulAction.orbit H q0 ⊆ {h • q0, negS (h • q0)} := fun y hy ↦ by
        by_cases e : y = h • q0
        · exact Or.inl e
        · exact Or.inr (hcon y hy e)
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({h • q0, negS (h • q0)} : Set Sph).ncard ≤ 2 :=
        (Set.ncard_insert_le _ _).trans (by simp)
      omega
    rcases hax x' hx' with h2 | h2
    · refine fixes_three (g : SO3) (fun e ↦ hg (Subtype.ext e)) (x := h • q0) (y := negS (h • q0)) (z := x')
        (negS_ne_self _).symm hne1.symm hne2.symm h1 ?_ h2
      show g • negS (h • q0) = negS (h • q0)
      rw [smul_negS, h1]
    · have h3 : g • (g • x') = x' := by rw [h2, smul_negS, h2, negS_negS]
      have : g ^ 3 • x' = g • x' := by
        rw [show g ^ 3 = g * (g * g) by rw [pow_succ, pow_two, mul_assoc], mul_smul, mul_smul, h3]
      rw [hg3, one_smul, h2] at this
      exact negS_ne_self x' this.symm
  · exact h1

/-- Two nontrivial elements that both act as `-1` on the orbit of `q₀` are equal (the orbit has more than two
points and a nontrivial element has only two fixed unit vectors). -/
theorem eq_of_neg_neg (H : Subgroup SO3) [Finite H] (q0 : Sph) (hO : 2 < (MulAction.orbit H q0).ncard)
    (g g' : H) (hg : ∀ x ∈ MulAction.orbit H q0, g • x = negS x)
    (hg' : ∀ x ∈ MulAction.orbit H q0, g' • x = negS x) : g = g' := by
  by_contra hne
  have hne' : g⁻¹ * g' ≠ 1 := fun e ↦ hne (by rw [inv_mul_eq_one] at e; exact e)
  have hfix : ∀ x ∈ MulAction.orbit H q0, (g⁻¹ * g') • x = x := by
    intro x hx
    rw [mul_smul, hg' x hx]
    exact (inv_smul_eq_iff).mpr (hg x hx).symm
  haveI hfinO : Finite (MulAction.orbit H q0) := finite_orbitSub H q0
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := (Set.two_lt_ncard (Set.toFinite _)).mp hO
  exact fixes_three ((g⁻¹ * g' : H) : SO3) (fun e ↦ hne' (Subtype.ext e)) hxy hxz hyz
    (hfix x hx) (hfix y hy) (hfix z hz)

theorem card_orbitSubG_mul (H : Subgroup SO3) [Fintype H] {X : Type} [MulAction H X] (x : X)
    [hf : Finite (orbitSubG H x)] :
    Nat.card (orbitSubG H x) * Nat.card (MulAction.stabilizer H x) = Nat.card H := by
  classical
  haveI : Finite (MulAction.orbit H x) := hf
  haveI : Fintype (MulAction.orbit H x) := Fintype.ofFinite _
  have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H x
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at this
  exact this

/-- **The octahedral case.**  A finite subgroup of `SO(3)` of order `24` with a pole `q₀` whose stabilizer has
order `3`, all poles with stabilizer of order `3` lying in the orbit of `q₀`, and all pole stabilizers of order
`≤ 4`, is isomorphic to `S₄` (via its action on the four axes through the orbit of `q₀`). -/
theorem octahedral_case (H : Subgroup SO3) [Fintype H] (hn : Fintype.card H = 24) (q0 : Sph)
    (hq0 : q0 ∈ poles H) (hs : Nat.card (MulAction.stabilizer H q0) = 3)
    (hU : ∀ x : Sph, x ∈ poles H → Nat.card (MulAction.stabilizer H x) = 3 → x ∈ MulAction.orbit H q0)
    (hB : ∀ x : Sph, x ∈ poles H → Nat.card (MulAction.stabilizer H x) ≤ 4) :
    Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
  classical
  have hn' : Nat.card H = 24 := by rw [Nat.card_eq_fintype_card]; exact hn
  haveI hfinO : Finite (orbitSub H q0) := finite_orbitSub H q0
  have hOcard : Nat.card (orbitSub H q0) = 8 := by
    have := card_orbitSub_mul H q0
    rw [hs, hn'] at this
    omega
  have hO : 2 < (MulAction.orbit H q0).ncard := by
    rw [← ncard_orbit_eq]; omega
  -- the antipode of `q₀` lies in the orbit of `q₀`
  have hnegpole : negS q0 ∈ poles H := by
    obtain ⟨g, hg1, hg⟩ := hq0
    exact ⟨g, hg1, by rw [smul_negS, hg]⟩
  have hstabneg : MulAction.stabilizer H (negS q0) = MulAction.stabilizer H q0 := by
    ext h
    simp only [MulAction.mem_stabilizer_iff, smul_negS]
    constructor
    · intro e
      simpa [negS_negS] using congrArg negS e
    · intro e; rw [e]
  obtain ⟨h0, hh0⟩ := hU _ hnegpole (by rw [hstabneg, hs])
  -- the four axes
  let Ax : SubMulAction H (Set Sph) := orbitSubG H (axis q0)
  haveI hfinAx : Finite Ax :=
    Finite.of_surjective (fun h : H ↦ (⟨h • axis q0, h, rfl⟩ : Ax)) (by rintro ⟨x, h, rfl⟩; exact ⟨h, rfl⟩)
  haveI : Fintype Ax := Fintype.ofFinite _
  let ψ : H →* Equiv.Perm Ax := MulAction.toPermHom H Ax
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    by_contra hg1
    have hP : ∀ h : H, g • axis (h • q0) = axis (h • q0) := by
      intro h
      have := congrArg (fun σ : Equiv.Perm Ax ↦ (σ ⟨h • axis q0, h, rfl⟩ : Set Sph)) hg
      simpa [ψ, MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_axis] using this
    have hPc : ∀ k : H, ∀ g' : H, (∀ h : H, g' • axis (h • q0) = axis (h • q0)) →
        ∀ h : H, (k * g' * k⁻¹) • axis (h • q0) = axis (h • q0) := by
      intro k g' hg' h
      have e : k⁻¹ • axis (h • q0) = axis ((k⁻¹ * h) • q0) := by rw [smul_axis, ← mul_smul]
      calc (k * g' * k⁻¹) • axis (h • q0) = k • (g' • (k⁻¹ • axis (h • q0))) := by simp only [mul_smul]
        _ = k • (g' • axis ((k⁻¹ * h) • q0)) := by rw [e]
        _ = k • axis ((k⁻¹ * h) • q0) := by rw [hg']
        _ = axis (h • q0) := by rw [smul_axis, ← mul_smul]; simp
    have hneg := kernel_neg H q0 hs hO g hP hg1
    have hcentral : ∀ k : H, k * g * k⁻¹ = g := by
      intro k
      have hk1 : k * g * k⁻¹ ≠ 1 := fun e ↦ hg1 (by simpa using e)
      exact eq_of_neg_neg H q0 hO _ _ (kernel_neg H q0 hs hO _ (hPc k g hP) hk1) hneg
    obtain ⟨a, b, -, hab⟩ := fixed_two (g : SO3) (fun e ↦ hg1 (Subtype.ext e))
    have hga : g • a = a := (hab a).mpr (Or.inl rfl)
    have ha : a ∈ poles H := ⟨g, hg1, hga⟩
    have hsub : MulAction.orbit H a ⊆ {a, b} := by
      rintro _ ⟨k, rfl⟩
      have hc : g * k = k * g := by
        have := hcentral k
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      have : g • (k • a) = k • a := by rw [← mul_smul, hc, mul_smul, hga]
      simpa using (hab _).mp this
    haveI : Finite (orbitSub H a) := finite_orbitSub H a
    have h2 : Nat.card (orbitSub H a) ≤ 2 := by
      rw [ncard_orbit_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans (by simp))
    have h24 := card_orbitSub_mul H a
    have h4 := hB a ha
    rw [hn'] at h24
    have hposc : 0 < Nat.card (orbitSub H a) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨a, MulAction.mem_orbit_self a⟩⟩, inferInstance⟩
    nlinarith
  -- counting
  let T := MulAction.stabilizer H (axis q0)
  have hle : MulAction.stabilizer H q0 ≤ T := by
    intro h hh
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    rw [smul_axis, hh]
  have hh0' : h0 • q0 = negS q0 := hh0
  have h0T : h0 ∈ T := by
    rw [MulAction.mem_stabilizer_iff, smul_axis, hh0']
    exact (axis_eq_iff _ _).mpr (Or.inr (negS_negS q0).symm)
  have h0nS : h0 ∉ MulAction.stabilizer H q0 := fun h ↦
    negS_ne_self q0 (hh0'.symm.trans (MulAction.mem_stabilizer_iff.mp h))
  have hdvd : 3 ∣ Nat.card T := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hs] at this
  have hgt : 3 < Nat.card T := by
    have hle' : Nat.card (MulAction.stabilizer H q0) ≤ Nat.card T := Subgroup.card_le_of_le hle
    rw [hs] at hle'
    by_contra hcon
    have : Nat.card T ≤ Nat.card (MulAction.stabilizer H q0) := by omega
    exact h0nS ((Subgroup.eq_of_le_of_card_ge hle this) ▸ h0T)
  have hcardAx := card_orbitSubG_mul H (axis q0)
  rw [hn'] at hcardAx
  have hAxle : Nat.card Ax ≤ 4 := by
    obtain ⟨t, ht⟩ := hdvd
    have : 2 ≤ t := by omega
    have hc : 6 ≤ Nat.card T := by omega
    nlinarith
  have hAxge : 4 ≤ Nat.card Ax := by
    have h1 : Nat.card H ≤ Nat.card (Equiv.Perm Ax) := Nat.card_le_card_of_injective ψ hinj
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm Ax), Fintype.card_perm, hn'] at h1
    by_contra hcon
    have hc : Fintype.card Ax ≤ 3 := by rw [← Nat.card_eq_fintype_card]; omega
    have h2 : (Fintype.card Ax).factorial ≤ (3 : ℕ).factorial := Nat.factorial_le hc
    simp [Nat.factorial] at h2
    omega
  have hAx4 : Nat.card Ax = 4 := le_antisymm hAxle hAxge
  have hAx4' : Fintype.card Ax = 4 := by rw [← Nat.card_eq_fintype_card]; exact hAx4
  have hbij : Function.Bijective ψ := by
    refine (Fintype.bijective_iff_injective_and_card ψ).mpr ⟨hinj, ?_⟩
    rw [Fintype.card_perm, hAx4', hn]
    decide
  let e : Ax ≃ Fin 4 := Fintype.equivFinOfCardEq hAx4'
  exact ⟨(MulEquiv.ofBijective ψ hbij).trans e.permCongrHom⟩

/-! ### Assembling the classification -/

/-- The five possible multisets of stabilizer orders. -/
theorem multiset_classification {κ : Type} [Fintype κ] (m : κ → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (hm : ∀ k, 2 ≤ m k ∧ m k ∣ n) (hsum : ∑ k, ((1 : ℚ) - 1 / (m k : ℚ)) = 2 - 2 / (n : ℚ)) :
    Finset.univ.val.map m = {n, n} ∨ (∃ r, n = 2 * r ∧ Finset.univ.val.map m = {2, 2, r}) ∨
      (n = 12 ∧ Finset.univ.val.map m = {2, 3, 3}) ∨ (n = 24 ∧ Finset.univ.val.map m = {2, 3, 4}) ∨
      (n = 60 ∧ Finset.univ.val.map m = {2, 3, 5}) := by
  classical
  set M : Multiset ℕ := Finset.univ.val.map m with hM
  have hl : (M.sort (· ≤ ·) : Multiset ℕ) = M := Multiset.sort_eq _ _
  have hmem : ∀ x ∈ M.sort (· ≤ ·), x ∈ M := fun x hx ↦ (Multiset.mem_sort _).mp hx
  have hmem' : ∀ x ∈ M, ∃ k, m k = x := fun x hx ↦ by
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.mp hx
    exact ⟨k, rfl⟩
  have h := rotation_orbit_data n hn (M.sort (· ≤ ·)) (Multiset.pairwise_sort _ _)
    (fun x hx ↦ by obtain ⟨k, rfl⟩ := hmem' x (hmem x hx); exact (hm k).1)
    (fun x hx ↦ by obtain ⟨k, rfl⟩ := hmem' x (hmem x hx); exact (hm k).2)
    (by
      rw [← hsum]
      have := congrArg (fun S : Multiset ℕ ↦ (S.map fun x : ℕ ↦ (1 : ℚ) - 1 / (x : ℚ)).sum) hl
      simp only [Multiset.map_coe, Multiset.sum_coe] at this
      rw [this, hM, Multiset.map_map]
      rfl)
  have key : ∀ l : List ℕ, l = M.sort (· ≤ ·) → ((l : Multiset ℕ) = M) := fun l hl' ↦ hl' ▸ hl
  rcases h with h | ⟨r, hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩
  · left; rw [← key _ h.symm]; rfl
  · right; left; exact ⟨r, hr, by rw [← key _ h.symm]; rfl⟩
  · right; right; left; exact ⟨hr, by rw [← key _ h.symm]; rfl⟩
  · right; right; right; left; exact ⟨hr, by rw [← key _ h.symm]; rfl⟩
  · right; right; right; right; exact ⟨hr, by rw [← key _ h.symm]; rfl⟩

/-- **Problem 3.24(a), classification** (up to the octahedral and icosahedral cases).  A finite subgroup of
`SO(3)` of order `≥ 2` is cyclic, dihedral of order `2 r` with `r ≥ 2`, isomorphic to `A₄` or to `S₄`, or has
order `60` (icosahedral; identification with `A₅` is not proved). -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem finite_subgroup_SO3_classification (H : Subgroup SO3) [Fintype H] (hn : 2 ≤ Fintype.card H) :
    IsCyclic H ∨ (∃ r, 2 ≤ r ∧ Nonempty (H ≃* DihedralGroup r)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
        Fintype.card H = 60 := by
  classical
  obtain ⟨κ, hκ, m, mk, hm, hsum, hsurj, hmk, hmk2⟩ := pole_data H
  have hcls := multiset_classification m (Fintype.card H) hn hm hsum
  rcases hcls with h | ⟨r, hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩
  · left
    have hnmem : Fintype.card H ∈ Finset.univ.val.map m := by rw [h]; simp
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hnmem
    obtain ⟨q, hq⟩ := hsurj k
    have hS : Nat.card (MulAction.stabilizer H (q : Sph)) = Fintype.card H := by
      rw [← hmk q, hq, hk]
    have htop : MulAction.stabilizer H (q : Sph) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hS, Nat.card_eq_fintype_card]
    refine isCyclic_of_fix H q.1.1 q.1.2 fun g ↦ ?_
    have : g ∈ MulAction.stabilizer H (q : Sph) := by rw [htop]; trivial
    exact congrArg Subtype.val ((MulAction.mem_stabilizer_iff (G := H) (α := Sph)).mp this)
  · right; left
    have hr2 : 2 ≤ r := by
      have hrmem : r ∈ Finset.univ.val.map m := by rw [h]; simp
      obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hrmem
      rw [← hk]; exact (hm k).1
    exact ⟨r, hr2, dihedral_case H m mk hsurj hmk hmk2 r hr2 hr h⟩
  · right; right; left
    have h3 : 3 ∈ Finset.univ.val.map m := by rw [h]; simp
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp h3
    obtain ⟨q, hq⟩ := hsurj k
    exact alternating_case H hr q.1 (by rw [← hmk q, hq, hk])
  · right; right; right; left
    have h3 : 3 ∈ Finset.univ.val.map m := by rw [h]; simp
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp h3
    obtain ⟨q, hq⟩ := hsurj k
    have hcount : (Finset.univ.val.map m).count 3 = 1 := by rw [h]; simp
    refine octahedral_case H hr q.1 q.2 (by rw [← hmk q, hq, hk]) ?_ ?_
    · intro x hx hx3
      have hkk : mk ⟨x, hx⟩ = mk q :=
        eq_of_count_eq_one m 3 hcount (by rw [hmk]; exact hx3) (by rw [hq, hk])
      obtain ⟨h, hh⟩ := hmk2 _ _ hkk
      refine ⟨h⁻¹, ?_⟩
      show h⁻¹ • (q : Sph) = x
      rw [← hh]
      exact inv_smul_smul h x
    · intro x hx
      have hin : m (mk ⟨x, hx⟩) ∈ Finset.univ.val.map m := Multiset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
      rw [h, hmk] at hin
      have hin2 : Nat.card (MulAction.stabilizer H x) = 2 ∨ Nat.card (MulAction.stabilizer H x) = 3 ∨
          Nat.card (MulAction.stabilizer H x) = 4 := by simpa using hin
      omega
  · right; right; right; right; exact hr

end FiniteRotations

end UndergradKB.RepresentationTheory
