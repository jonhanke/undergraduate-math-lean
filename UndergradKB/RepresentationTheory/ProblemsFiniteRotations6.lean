import UndergradKB.Common.Attr
import Mathlib.GroupTheory.Sylow
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.GroupTheory.SpecificGroups.Alternating
import UndergradKB.RepresentationTheory.ProblemsFiniteRotations5

/-! # Problem 3.24: the icosahedral case

Abstract part: a finite group of order `60` whose nontrivial elements have order `2, 3` or `5`, with `15`
involutions, centralizers of involutions of order `≤ 4`, and no small nontrivial normal subgroup, is isomorphic
to `A₅` via its conjugation action on its five Sylow `2`-subgroups.
-/

namespace UndergradKB.RepresentationTheory

namespace FiniteRotations

open Equiv in
/-- A subgroup of `S₅` of order `60` is `A₅`. -/
theorem eq_alternating_of_card_sixty (K : Subgroup (Perm (Fin 5))) (hK : Nat.card K = 60) :
    K = alternatingGroup (Fin 5) := by
  have hperm : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide
  have hindex : K.index = 2 := by
    have := Subgroup.card_mul_index K
    rw [hK, hperm] at this
    omega
  have hle : alternatingGroup (Fin 5) ≤ K := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      rw [← hσ.orderOf]; exact pow_orderOf_eq_one σ
    have : σ = σ ^ 2 * σ ^ 2 := by
      calc σ = σ * σ ^ 3 := by rw [h3, mul_one]
        _ = σ ^ 2 * σ ^ 2 := by group
    rw [this]
    exact Subgroup.mul_self_mem_of_index_two hindex _
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    have := two_mul_nat_card_alternatingGroup (α := Fin 5)
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hK])).symm

theorem sylow_card_four {G : Type*} [Group G] [Fintype G] (hn : Fintype.card G = 60) (P : Sylow 2 G) :
    Nat.card P = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn' : Nat.card G = 60 := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup
  have h4 : 2 ^ 2 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (by rw [hn']; norm_num)
  have hd : Nat.card P ∣ 60 := hn' ▸ Subgroup.card_subgroup_dvd_card _
  rw [hk] at h4 hd ⊢
  have : k = 2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · interval_cases k <;> omega
    · have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 h
      have := Nat.dvd_trans h8 hd
      omega
  subst this
  norm_num

/-- **Abstract recognition of `A₅`.** -/
theorem a5_of_conditions {G : Type*} [Group G] [Fintype G] (hn : Fintype.card G = 60)
    (G1 : ∀ g : G, g ≠ 1 → orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5)
    (G2 : (Finset.univ.filter fun g : G => orderOf g = 2).card = 15)
    (G3 : ∀ z : G, orderOf z = 2 → Nat.card (Subgroup.centralizer ({z} : Set G)) ≤ 4)
    (G4 : ∀ N : Subgroup G, N.Normal → ∀ x ∈ N,
      (orderOf x = 2 → 16 ≤ Nat.card N) ∧ (orderOf x = 3 → 11 ≤ Nat.card N) ∧
        (orderOf x = 5 → 7 ≤ Nat.card N)) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn' : Nat.card G = 60 := by rw [Nat.card_eq_fintype_card]; exact hn
  haveI : Fintype (Sylow 2 G) := Fintype.ofFinite _
  have hord2 : ∀ (P : Sylow 2 G) (x : G), x ∈ P → x ≠ 1 → orderOf x = 2 := by
    intro P x hx hx1
    have hdvd : orderOf x ∣ 4 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup G))
      rw [sylow_card_four hn P, Subgroup.orderOf_mk] at this
      exact this
    rcases G1 x hx1 with h | h | h <;> rw [h] at hdvd ⊢ <;> first | rfl | (exfalso; omega)
  have hcomm : ∀ (P : Sylow 2 G) (x y : G), x ∈ P → y ∈ P → x * y = y * x := by
    intro P x y hx hy
    have hP : Nat.card (P : Subgroup G) = 2 ^ 2 := by rw [sylow_card_four hn P]; norm_num
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hP).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hex : ∀ z : G, orderOf z = 2 → ∃ P : Sylow 2 G, z ∈ P := by
    intro z hz
    have hp : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hz]; norm_num⟩
    obtain ⟨P, hP⟩ := hp.exists_le_sylow
    exact ⟨P, hP (Subgroup.mem_zpowers z)⟩
  have huniq : ∀ (z : G) (P Q : Sylow 2 G), orderOf z = 2 → z ∈ P → z ∈ Q → P = Q := by
    intro z P Q hz hzP hzQ
    have hle : ∀ R : Sylow 2 G, z ∈ R → (R : Subgroup G) = Subgroup.centralizer {z} := by
      intro R hzR
      have hl : (R : Subgroup G) ≤ Subgroup.centralizer {z} := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hcomm R z x hzR hx
      refine Subgroup.eq_of_le_of_card_ge hl ?_
      rw [sylow_card_four hn R]; exact G3 z hz
    exact Sylow.ext ((hle P hzP).trans (hle Q hzQ).symm)
  let S : Sylow 2 G → Finset G := fun P => Finset.univ.filter fun g => g ∈ P ∧ orderOf g = 2
  have hS3 : ∀ P, (S P).card = 3 := by
    intro P
    have hS : S P = (Finset.univ.filter fun g : G => g ∈ P).erase 1 := by
      ext g
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hg, h2⟩
        exact ⟨fun h ↦ by rw [h, orderOf_one] at h2; omega, hg⟩
      · rintro ⟨h1, hg⟩
        exact ⟨hg, hord2 P g hg h1⟩
    have hc : (Finset.univ.filter fun g : G => g ∈ P).card = 4 := by
      rw [← sylow_card_four hn P, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rfl
    rw [hS, Finset.card_erase_of_mem (by simp [Subgroup.one_mem]), hc]
  have hunion : Finset.univ.filter (fun g : G => orderOf g = 2) = Finset.univ.biUnion S := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, S]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hex g h
      exact ⟨P, hP, h⟩
    · rintro ⟨P, -, h⟩
      exact h
  have hdisj : ∀ P ∈ (Finset.univ : Finset (Sylow 2 G)), ∀ Q ∈ (Finset.univ : Finset (Sylow 2 G)),
      P ≠ Q → Disjoint (S P) (S Q) := by
    intro P _ Q _ hPQ
    rw [Finset.disjoint_left]
    intro g hgP hgQ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hgP hgQ
    exact hPQ (huniq g P Q hgP.2 hgP.1 hgQ.1)
  have hn2 : Fintype.card (Sylow 2 G) = 5 := by
    have h := G2
    rw [hunion, Finset.card_biUnion hdisj] at h
    simp only [hS3, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
    omega
  -- the conjugation action on the Sylow subgroups
  let φ : G →* Equiv.Perm (Sylow 2 G) := MulAction.toPermHom G (Sylow 2 G)
  obtain ⟨P0⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hstab : Nat.card (MulAction.stabilizer G P0) = 12 := by
    haveI : Fintype (MulAction.orbit G P0) := Fintype.ofFinite _
    have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G P0
    have horb : Fintype.card (MulAction.orbit G P0) = 5 := by
      rw [← hn2]
      exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun x ↦
        MulAction.mem_orbit_iff.mpr (MulAction.exists_smul_eq G P0 x))
    rw [horb, hn] at h1
    rw [Nat.card_eq_fintype_card]
    omega
  have hker : Nat.card φ.ker ≤ 12 := by
    have hle : φ.ker ≤ MulAction.stabilizer G P0 := by
      intro g hg
      rw [MulAction.mem_stabilizer_iff]
      have := congrArg (fun σ : Equiv.Perm (Sylow 2 G) ↦ σ P0) (MonoidHom.mem_ker.mp hg)
      simpa [φ] using this
    rw [← hstab]
    exact Subgroup.card_le_of_le hle
  have hbot : φ.ker = ⊥ := by
    by_contra hne
    haveI : φ.ker.Normal := MonoidHom.normal_ker φ
    have hd : Nat.card φ.ker ∣ 60 := hn' ▸ Subgroup.card_subgroup_dvd_card _
    have hgt : 1 < Nat.card φ.ker := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have h2 : ¬ 2 ∣ Nat.card φ.ker := by
      intro h2
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 h2
      have := (G4 φ.ker inferInstance x x.2).1 ((Subgroup.orderOf_coe x).trans hx)
      omega
    have key : ∀ c : ℕ, c ∣ 60 → ¬ 2 ∣ c → 1 < c → c ≤ 12 → c = 3 ∨ c = 5 := by
      intro c h1 h2 h3 h4
      interval_cases c <;> omega
    rcases key _ hd h2 hgt hker with h3 | h3
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 3 (by rw [h3])
      have := (G4 φ.ker inferInstance x x.2).2.1 ((Subgroup.orderOf_coe x).trans hx)
      omega
    · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 5 (by rw [h3])
      have := (G4 φ.ker inferInstance x x.2).2.2 ((Subgroup.orderOf_coe x).trans hx)
      omega
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
  have e : Sylow 2 G ≃ Fin 5 := Fintype.equivFinOfCardEq hn2
  let ψ : G →* Equiv.Perm (Fin 5) := e.permCongrHom.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := e.permCongrHom.injective.comp hinj
  let iso : G ≃* ψ.range := MonoidHom.ofInjective hψ
  have hK : Nat.card ψ.range = 60 := by rw [← Nat.card_congr iso.toEquiv, hn']
  exact ⟨iso.trans (MulEquiv.subgroupCongr (eq_alternating_of_card_sixty _ hK))⟩

/-! ### The geometric input -/

/-- The pole data of an icosahedral group: `|H| = 60`, pole stabilizers have order `2, 3` or `5`, and the poles
with stabilizer of order `2` form one orbit. -/
structure IcoData (H : Subgroup SO3) [Fintype H] : Prop where
  card : Fintype.card H = 60
  stab : ∀ a : Sph, a ∈ poles H → Nat.card (MulAction.stabilizer H a) = 2 ∨
    Nat.card (MulAction.stabilizer H a) = 3 ∨ Nat.card (MulAction.stabilizer H a) = 5
  uniq2 : ∀ a b : Sph, a ∈ poles H → b ∈ poles H → Nat.card (MulAction.stabilizer H a) = 2 →
    Nat.card (MulAction.stabilizer H b) = 2 → b ∈ MulAction.orbit H a
  ex2 : ∃ a : Sph, a ∈ poles H ∧ Nat.card (MulAction.stabilizer H a) = 2

section Ico

variable {H : Subgroup SO3} [Fintype H]

theorem fixed_pair (g : H) (hg : g ≠ 1) :
    ∃ a b : Sph, a ≠ b ∧ (∀ y : Sph, g • y = y ↔ y = a ∨ y = b) ∧ a ∈ poles H ∧ b ∈ poles H := by
  obtain ⟨a, b, hne, hab⟩ := fixed_two (g : SO3) (fun e ↦ hg (Subtype.ext e))
  exact ⟨a, b, hne, hab, ⟨g, hg, (hab a).mpr (Or.inl rfl)⟩, ⟨g, hg, (hab b).mpr (Or.inr rfl)⟩⟩

theorem orderOf_eq_stab (hD : IcoData H) (g : H) (hg : g ≠ 1) (a : Sph) (ha : a ∈ poles H)
    (hga : g • a = a) : orderOf g = Nat.card (MulAction.stabilizer H a) := by
  have hdvd : orderOf g ∣ Nat.card (MulAction.stabilizer H a) := by
    have := orderOf_dvd_natCard (⟨g, MulAction.mem_stabilizer_iff.mpr hga⟩ : MulAction.stabilizer H a)
    rwa [Subgroup.orderOf_mk] at this
  have hprime : (Nat.card (MulAction.stabilizer H a)).Prime := by
    rcases hD.stab a ha with h | h | h <;> rw [h] <;>
      first | exact Nat.prime_two | exact Nat.prime_three | exact Nat.prime_five
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hg
  · exact h

theorem G1_ico (hD : IcoData H) (g : H) (hg : g ≠ 1) : orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  obtain ⟨a, b, hne, hab, ha, hb⟩ := fixed_pair g hg
  rw [orderOf_eq_stab hD g hg a ha ((hab a).mpr (Or.inl rfl))]
  exact hD.stab a ha

theorem inv_fixed (hD : IcoData H) (z : H) (hz : orderOf z = 2) :
    ∃ a b : Sph, a ≠ b ∧ (∀ y : Sph, z • y = y ↔ y = a ∨ y = b) ∧ a ∈ poles H ∧ b ∈ poles H ∧
      Nat.card (MulAction.stabilizer H a) = 2 ∧ Nat.card (MulAction.stabilizer H b) = 2 := by
  have hz1 : z ≠ 1 := fun h ↦ by rw [h, orderOf_one] at hz; omega
  obtain ⟨a, b, hne, hab, ha, hb⟩ := fixed_pair z hz1
  refine ⟨a, b, hne, hab, ha, hb, ?_, ?_⟩
  · rw [← orderOf_eq_stab hD z hz1 a ha ((hab a).mpr (Or.inl rfl)), hz]
  · rw [← orderOf_eq_stab hD z hz1 b hb ((hab b).mpr (Or.inr rfl)), hz]

theorem eq_of_card_two {G : Type*} [Group G] (T : Subgroup G) [Finite T] (hT : Nat.card T = 2) {x y : G}
    (hx : x ∈ T) (hy : y ∈ T) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  by_contra hne
  haveI : Fintype T := Fintype.ofFinite _
  have h2 : Fintype.card T = 2 := by rw [← Nat.card_eq_fintype_card]; exact hT
  have : 2 < Fintype.card T := by
    refine Fintype.two_lt_card_iff.mpr ⟨⟨1, T.one_mem⟩, ⟨x, hx⟩, ⟨y, hy⟩, ?_, ?_, ?_⟩
    · exact fun h ↦ hx1 (congrArg Subtype.val h).symm
    · exact fun h ↦ hy1 (congrArg Subtype.val h).symm
    · exact fun h ↦ hne (congrArg Subtype.val h)
  omega

theorem G3_ico (hD : IcoData H) (z : H) (hz : orderOf z = 2) :
    Nat.card (Subgroup.centralizer ({z} : Set H)) ≤ 4 := by
  classical
  obtain ⟨a, b, hne, hab, ha, hb, hsa, hsb⟩ := inv_fixed hD z hz
  have hza : z • a = a := (hab a).mpr (Or.inl rfl)
  set C := Subgroup.centralizer ({z} : Set H) with hC
  have hsub : MulAction.orbit C a ⊆ {a, b} := by
    rintro _ ⟨c, rfl⟩
    have hc : z * (c : H) = (c : H) * z := Subgroup.mem_centralizer_iff.mp c.2 z rfl
    have : z • ((c : H) • a) = (c : H) • a := by
      rw [← mul_smul, hc, mul_smul, hza]
    exact (hab _).mp this
  haveI : Finite (MulAction.orbit C a) := ((Set.toFinite {a, b}).subset hsub).to_subtype
  haveI : Fintype (MulAction.orbit C a) := Fintype.ofFinite _
  haveI : Fintype C := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer C a) := Fintype.ofFinite _
  have hcard := MulAction.card_orbit_mul_card_stabilizer_eq_card_group C a
  have horb : Fintype.card (MulAction.orbit C a) ≤ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans (by simp))
  haveI : Fintype (MulAction.stabilizer H a) := Fintype.ofFinite _
  have hst : Fintype.card (MulAction.stabilizer C a) ≤ 2 := by
    have hinj : Function.Injective (fun c : MulAction.stabilizer C a ↦
        (⟨(c.1 : H), MulAction.mem_stabilizer_iff.mpr (MulAction.mem_stabilizer_iff.mp c.2)⟩ :
          MulAction.stabilizer H a)) := by
      intro c c' h
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext this)
    have := Fintype.card_le_of_injective _ hinj
    rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer H a), hsa] at this
    exact this
  rw [Nat.card_eq_fintype_card, ← hcard]
  nlinarith

theorem norm_lower (N : Subgroup H) [N.Normal] (x : H) (hx : x ∈ N) (hx1 : x ≠ 1) (a : Sph)
    (hxa : x • a = a) : Nat.card (orbitSub H a) ≤ 2 * (Nat.card N - 1) := by
  classical
  haveI : Finite (orbitSub H a) := finite_orbitSub H a
  haveI : Finite (MulAction.orbit H a) := ‹Finite (orbitSub H a)›
  let O : Finset Sph := (Set.toFinite (MulAction.orbit H a)).toFinset
  have hO : O.card = Nat.card (orbitSub H a) := by
    rw [ncard_orbit_eq, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have hOmem : ∀ b, b ∈ O ↔ b ∈ MulAction.orbit H a := fun b ↦ by simp [O]
  let f : Sph → H := fun b ↦
    if hb : b ∈ MulAction.orbit H a then
      (Classical.choose hb) * x * (Classical.choose hb)⁻¹ else 1
  have hf : ∀ b ∈ O, f b ∈ N ∧ f b ≠ 1 ∧ f b • b = b := by
    intro b hb
    rw [hOmem] at hb
    have hfb : f b = (Classical.choose hb) * x * (Classical.choose hb)⁻¹ := by simp [f, hb]
    have hch : Classical.choose hb • a = b := Classical.choose_spec hb
    set k := Classical.choose hb
    refine ⟨?_, ?_, ?_⟩
    · rw [hfb]; exact (inferInstance : N.Normal).conj_mem x hx k
    · rw [hfb]; intro e; exact hx1 (by simpa using e)
    · rw [hfb, ← hch, ← mul_smul, show k * x * k⁻¹ * k = k * x by group, mul_smul, hxa]
  have hfib : ∀ c ∈ O.image f, (O.filter fun b ↦ f b = c).card ≤ 2 := by
    intro c hc
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a0, b1, -, hab, -, -⟩ := fixed_pair (f b0) (hf b0 hb0).2.1
    have : (O.filter fun b ↦ f b = f b0) ⊆ {a0, b1} := by
      intro b hb
      rw [Finset.mem_filter] at hb
      have := (hf b hb.1).2.2
      rw [hb.2] at this
      simpa using (hab b).mp this
    exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _ |>.trans (by simp))
  have h1 := Finset.card_le_mul_card_image O 2 hfib
  have h2 : (O.image f).card ≤ Nat.card N - 1 := by
    have hsub : O.image f ⊆ (Finset.univ.filter fun g : H ↦ g ∈ N).erase 1 := by
      intro c hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hf b hb).2.1, (hf b hb).1⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_erase_of_mem (by simp [N.one_mem])]
    have : (Finset.univ.filter fun g : H ↦ g ∈ N).card = Nat.card N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    omega
  rw [← hO]
  nlinarith

theorem G4_ico (hD : IcoData H) (N : Subgroup H) [N.Normal] (x : H) (hx : x ∈ N) :
    (orderOf x = 2 → 16 ≤ Nat.card N) ∧ (orderOf x = 3 → 11 ≤ Nat.card N) ∧
      (orderOf x = 5 → 7 ≤ Nat.card N) := by
  have hn' : Nat.card H = 60 := by rw [Nat.card_eq_fintype_card]; exact hD.card
  have key : x ≠ 1 → 60 ≤ orderOf x * (2 * (Nat.card N - 1)) := by
    intro hx1
    obtain ⟨a, b, -, hab, ha, hb⟩ := fixed_pair x hx1
    have hxa : x • a = a := (hab a).mpr (Or.inl rfl)
    have h1 := norm_lower N x hx hx1 a hxa
    have h2 := card_orbitSub_mul H a
    rw [← orderOf_eq_stab hD x hx1 a ha hxa, hn'] at h2
    nlinarith
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := key (fun e ↦ by rw [e, orderOf_one] at h; omega)
    rw [h] at this; omega
  · have := key (fun e ↦ by rw [e, orderOf_one] at h; omega)
    rw [h] at this; omega
  · have := key (fun e ↦ by rw [e, orderOf_one] at h; omega)
    rw [h] at this; omega

theorem G2_ico (hD : IcoData H) : (Finset.univ.filter fun g : H ↦ orderOf g = 2).card = 15 := by
  classical
  obtain ⟨q2, hq2, hs2⟩ := hD.ex2
  have hn' : Nat.card H = 60 := by rw [Nat.card_eq_fintype_card]; exact hD.card
  haveI hf2 : Finite (orbitSub H q2) := finite_orbitSub H q2
  haveI : Finite (MulAction.orbit H q2) := hf2
  let O2 : Finset Sph := (Set.toFinite (MulAction.orbit H q2)).toFinset
  have hO2card : O2.card = 30 := by
    have h := card_orbitSub_mul H q2
    rw [hs2, hn'] at h
    have : O2.card = Nat.card (orbitSub H q2) := by
      rw [ncard_orbit_eq, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    omega
  have hmemO2 : ∀ a : Sph, a ∈ poles H → Nat.card (MulAction.stabilizer H a) = 2 → a ∈ O2 := by
    intro a ha hsa
    simpa [O2] using hD.uniq2 q2 a hq2 ha hs2 hsa
  have hbip := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Finset.univ.filter fun g : H ↦ orderOf g = 2) (t := O2) (fun (z : H) (a : Sph) ↦ z • a = a)
  have hL : ∀ z ∈ (Finset.univ.filter fun g : H ↦ orderOf g = 2),
      (O2.bipartiteAbove (fun (z : H) (a : Sph) ↦ z • a = a) z).card = 2 := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨a, b, hne, hab, ha, hb, hsa, hsb⟩ := inv_fixed hD z hz
    have : O2.bipartiteAbove (fun (z : H) (a : Sph) ↦ z • a = a) z = {a, b} := by
      ext y
      simp only [Finset.mem_bipartiteAbove, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hy⟩
        exact (hab y).mp hy
      · rintro (rfl | rfl)
        · exact ⟨hmemO2 _ ha hsa, (hab _).mpr (Or.inl rfl)⟩
        · exact ⟨hmemO2 _ hb hsb, (hab _).mpr (Or.inr rfl)⟩
    rw [this, Finset.card_pair hne]
  have hR : ∀ a ∈ O2,
      ((Finset.univ.filter fun g : H ↦ orderOf g = 2).bipartiteBelow
        (fun (z : H) (a : Sph) ↦ z • a = a) a).card = 1 := by
    intro a ha
    have ha' : a ∈ MulAction.orbit H q2 := by simpa [O2] using ha
    obtain ⟨h, rfl⟩ := ha'
    have hpole : h • q2 ∈ poles H := SubMulAction.smul_mem (poles H) h hq2
    have hsa : Nat.card (MulAction.stabilizer H (h • q2)) = 2 := by rw [card_stab_smul, hs2]
    haveI : Finite (MulAction.stabilizer H (h • q2)) := inferInstance
    have hnt : 1 < Nat.card (MulAction.stabilizer H (h • q2)) := by omega
    obtain ⟨z0, hz0⟩ : ∃ z0 : MulAction.stabilizer H (h • q2), z0 ≠ 1 := by
      haveI : Fintype (MulAction.stabilizer H (h • q2)) := Fintype.ofFinite _
      haveI : Nontrivial (MulAction.stabilizer H (h • q2)) := Fintype.one_lt_card_iff_nontrivial.mp (by rw [← Nat.card_eq_fintype_card]; exact hnt)
      exact exists_ne 1
    have hz0H : (z0 : H) ≠ 1 := fun e ↦ hz0 (Subtype.ext e)
    have hz0a : (z0 : H) • (h • q2) = h • q2 := MulAction.mem_stabilizer_iff.mp z0.2
    have hord : orderOf (z0 : H) = 2 := by
      rw [orderOf_eq_stab hD z0 hz0H _ hpole hz0a, hsa]
    rw [Finset.card_eq_one]
    refine ⟨z0, ?_⟩
    ext z
    simp only [Finset.mem_bipartiteBelow, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hza⟩
      have hz1 : z ≠ 1 := fun e ↦ by rw [e, orderOf_one] at hz; omega
      exact eq_of_card_two _ hsa (MulAction.mem_stabilizer_iff.mpr hza) z0.2 hz1 hz0H
    · rintro rfl
      exact ⟨hord, hz0a⟩
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at hbip
  simp only [Finset.sum_const, smul_eq_mul, mul_one, hO2card] at hbip
  omega

end Ico

/-- A finite subgroup of `SO(3)` of order `60` is cyclic, dihedral, or isomorphic to `A₅`. -/
theorem classification_sixty (H : Subgroup SO3) [Fintype H] (hn : Fintype.card H = 60) :
    IsCyclic H ∨ (∃ r, 2 ≤ r ∧ Nonempty (H ≃* DihedralGroup r)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  classical
  obtain ⟨κ, hκ, m, mk, hm, hsum, hsurj, hmk, hmk2⟩ := pole_data H
  have hcls := multiset_classification m (Fintype.card H) (by omega) hm hsum
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
  · omega
  · omega
  · right; right
    have hcount2 : (Finset.univ.val.map m).count 2 = 1 := by rw [h]; simp
    have hD : IcoData H := by
      refine ⟨hn, ?_, ?_, ?_⟩
      · intro a ha
        have hin : m (mk ⟨a, ha⟩) ∈ Finset.univ.val.map m :=
          Multiset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
        rw [h, hmk] at hin
        simpa using hin
      · intro a b ha hb hsa hsb
        have hkk : mk ⟨a, ha⟩ = mk ⟨b, hb⟩ :=
          eq_of_count_eq_one m 2 hcount2 (by rw [hmk]; exact hsa) (by rw [hmk]; exact hsb)
        exact hmk2 _ _ hkk
      · have h2 : 2 ∈ Finset.univ.val.map m := by rw [h]; simp
        obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp h2
        obtain ⟨q, hq⟩ := hsurj k
        exact ⟨q.1, q.2, by rw [← hmk q, hq, hk]⟩
    refine a5_of_conditions hn (G1_ico hD) (G2_ico hD) (G3_ico hD) ?_
    intro N hN x hx
    haveI := hN
    exact G4_ico hD N x hx

/-- **Problem 3.24(a).**  Every finite subgroup `H` of `SO(3)` is cyclic, dihedral of order `2 r` with `r ≥ 2`,
or isomorphic to `A₄`, `S₄` or `A₅` (the rotation groups of the tetrahedron, cube and icosahedron). -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem finite_subgroup_SO3_classification_full (H : Subgroup SO3) [Fintype H] :
    IsCyclic H ∨ (∃ r, 2 ≤ r ∧ Nonempty (H ≃* DihedralGroup r)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  by_cases hn : 2 ≤ Fintype.card H
  · rcases finite_subgroup_SO3_classification H hn with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases classification_sixty H h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · left
    have : Fintype.card H = 1 := by
      have := Fintype.card_pos (α := H)
      omega
    haveI : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp this.le
    exact isCyclic_of_subsingleton

end FiniteRotations

end UndergradKB.RepresentationTheory
