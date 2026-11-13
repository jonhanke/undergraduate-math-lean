import UndergradKB.Common.Attr
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex
import UndergradKB.RepresentationTheory.ProblemsFiniteRotations3

/-! # Problem 3.24: finite groups of rotations about an axis are cyclic

A finite subgroup of `SO(3)` all of whose elements fix a unit vector `p` is cyclic: conjugating by a rotation
`R` taking `p` to `e₃`, its elements become rotations `Rz c s` about the `z`-axis, and `Rz c s ↦ c + s i` is an
injective homomorphism to `ℂ`; a finite subgroup of the multiplicative group of a field is cyclic.
-/

namespace UndergradKB.RepresentationTheory

open Matrix SO3Rot

namespace FiniteRotations

theorem isSO3_transpose' {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : IsSO3 M) : IsSO3 Mᵀ :=
  ⟨by simpa using hM.2.1, by simpa using hM.1, by rw [Matrix.det_transpose]; exact hM.2.2⟩

/-- A rotation taking a given unit vector to the `z`-axis. -/
theorem exists_rot_to_e3 (p : Fin 3 → ℝ) (hp : p ⬝ᵥ p = 1) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, IsSO3 R ∧ R *ᵥ p = ![0, 0, 1] := by
  have hn : p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1 := by
    simp [dotProduct, Fin.sum_univ_three] at hp; nlinarith
  obtain ⟨c1, s1, h1, h1x⟩ := exists_cs (p 0) (p 1)
  set x := p 0 with hx
  set y := p 1 with hy
  set z := p 2 with hz
  set t := s1 * x + c1 * y with ht
  have ht2 : t ^ 2 = x ^ 2 + y ^ 2 := by
    rw [ht]
    linear_combination (x ^ 2 + y ^ 2) * h1 - (c1 * x - s1 * y) * h1x
  have hzt : z ^ 2 + t ^ 2 = 1 := by linarith
  refine ⟨Rx z t * Rz c1 s1, ((inRange_Rx z t hzt).mul (inRange_Rz c1 s1 h1)).isSO3, ?_⟩
  funext i
  fin_cases i <;> simp [Rx, Rz, Matrix.mulVec, dotProduct, Fin.sum_univ_three, ← hx, ← hy, ← hz]
  · linear_combination h1x
  · rw [ht]; ring
  · linear_combination hzt - t * ht

/-- The complex number `c + s i` attached to the upper left corner of a matrix. -/
def zOf (B : Matrix (Fin 3) (Fin 3) ℝ) : ℂ := ⟨B 0 0, B 1 0⟩

theorem zOf_Rz (c s : ℝ) : zOf (Rz c s) = ⟨c, s⟩ := by simp [zOf, Rz]

theorem Rz_mul (c s c' s' : ℝ) : Rz c s * Rz c' s' = Rz (c * c' - s * s') (s * c' + c * s') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem zOf_Rz_mul (c s c' s' : ℝ) : zOf (Rz c s * Rz c' s') = zOf (Rz c s) * zOf (Rz c' s') := by
  rw [Rz_mul]
  apply Complex.ext <;> simp [zOf, Rz] <;> ring

theorem conj_fix {R M : Matrix (Fin 3) (Fin 3) ℝ} (hR : IsSO3 R) (hM : IsSO3 M) (p : Fin 3 → ℝ)
    (hRp : R *ᵥ p = ![0, 0, 1]) (hMp : M *ᵥ p = p) : ∃ c s : ℝ, R * M * Rᵀ = Rz c s := by
  have hB : IsSO3 (R * M * Rᵀ) := (hR.mul hM).mul (isSO3_transpose' hR)
  have hRt : Rᵀ *ᵥ ![0, 0, 1] = p := by
    rw [← hRp, Matrix.mulVec_mulVec, hR.2.1, Matrix.one_mulVec]
  have hBe : (R * M * Rᵀ) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    rw [← Matrix.mulVec_mulVec, hRt, ← Matrix.mulVec_mulVec, hMp, hRp]
  have e0 := congrFun hBe 0
  have e1 := congrFun hBe 1
  have e2 := congrFun hBe 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e0 e1 e2
  exact eq_Rz_of_fix hB e0 e1 e2 |>.imp fun c h ↦ h.imp fun s h' ↦ h'.2

theorem conj_mul' {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : Rᵀ * R = 1) (M M' : Matrix (Fin 3) (Fin 3) ℝ) :
    R * (M * M') * Rᵀ = (R * M * Rᵀ) * (R * M' * Rᵀ) := by
  have : (R * M * Rᵀ) * (R * M' * Rᵀ) = R * M * (Rᵀ * R) * M' * Rᵀ := by simp only [Matrix.mul_assoc]
  rw [this, hR, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- **A finite group of rotations about an axis is cyclic.**  If every element of a finite subgroup `H` of
`SO(3)` fixes the unit vector `p`, then `H` is cyclic. -/
theorem isCyclic_of_fix (H : Subgroup SO3) [Finite H] (p : Fin 3 → ℝ) (hp : p ⬝ᵥ p = 1)
    (hfix : ∀ h : H, ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p = p) : IsCyclic H := by
  obtain ⟨R, hR, hRp⟩ := exists_rot_to_e3 p hp
  have hconj : ∀ h : H, ∃ c s : ℝ, R * ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ = Rz c s :=
    fun h ↦ conj_fix hR (isSO3_of_mem h) p hRp (hfix h)
  let f : H →* ℂ :=
    { toFun := fun h ↦ zOf (R * ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ)
      map_one' := by
        have : R * (((1 : H) : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ = 1 := by
          show R * 1 * Rᵀ = 1
          rw [Matrix.mul_one]; exact hR.1
        rw [this]
        apply Complex.ext <;> simp [zOf]
      map_mul' := by
        intro h h'
        obtain ⟨c, s, e⟩ := hconj h
        obtain ⟨c', s', e'⟩ := hconj h'
        have : R * (((h * h' : H) : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ =
            (R * ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ) *
              (R * ((h' : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ) :=
          conj_mul' hR.2.1 _ _
        rw [this, e, e', zOf_Rz_mul] }
  refine isCyclic_of_injective_ringHom f ?_
  intro h h' hh
  obtain ⟨c, s, e⟩ := hconj h
  obtain ⟨c', s', e'⟩ := hconj h'
  have hh' : zOf (R * ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ) =
      zOf (R * ((h' : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ) := hh
  rw [e, e', zOf_Rz, zOf_Rz] at hh'
  have hc : c = c' := congrArg Complex.re hh'
  have hs : s = s' := congrArg Complex.im hh'
  have hee : R * ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ =
      R * ((h' : SO3) : Matrix (Fin 3) (Fin 3) ℝ) * Rᵀ := by rw [e, e', hc, hs]
  have cancel : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, M = Rᵀ * (R * M * Rᵀ) * R := fun M ↦ by
    have : Rᵀ * (R * M * Rᵀ) * R = (Rᵀ * R) * M * (Rᵀ * R) := by simp only [Matrix.mul_assoc]
    rw [this, hR.2.1, Matrix.one_mul, Matrix.mul_one]
  exact Subtype.ext (Subtype.ext (by rw [cancel ((h : SO3) : Matrix (Fin 3) (Fin 3) ℝ), hee, ← cancel]))

/-- The pole counting identity together with the information that an orbit whose stabilizer is all of `H`
consists of a pole fixed by all of `H`. -/
theorem pole_counting_exposed (H : Subgroup SO3) [Fintype H] :
    ∃ (κ : Type) (_ : Fintype κ) (m : κ → ℕ), (∀ k, 2 ≤ m k ∧ m k ∣ Fintype.card H) ∧
      ∑ k, ((1 : ℚ) - 1 / (m k : ℚ)) = 2 - 2 / (Fintype.card H : ℚ) ∧
      (∀ k, m k = Fintype.card H → ∃ p : Sph, p ∈ poles H ∧ ∀ h : H, h • p = p) := by
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
      exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun x ↦ by simp [MulAction.mem_fixedBy])
    rw [h1]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => 2)]
    · simp [Finset.card_erase_of_mem, mul_comm]
    · intro g hg
      rw [← Nat.card_eq_fintype_card]
      exact card_fixedBy_nontrivial H g (Finset.ne_of_mem_erase hg)
  refine ⟨MulAction.orbitRel.Quotient H (poles H), inferInstance,
    fun ω ↦ Fintype.card (MulAction.stabilizer H ω.out), fun ω ↦ ⟨?_, ?_⟩, ?_, ?_⟩
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
  · intro ω hω
    have htop : MulAction.stabilizer H ω.out = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact hω
    refine ⟨(ω.out : Sph), ω.out.2, fun h ↦ ?_⟩
    have : h ∈ MulAction.stabilizer H ω.out := by rw [htop]; trivial
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp this)

/-- **Problem 3.24(a), first consequences.**  A finite subgroup `H` of `SO(3)` of order `n ≥ 2` is cyclic, or
has order `2 r` with `r ≥ 2` (the dihedral case), or has order `12`, `24` or `60` (the tetrahedral, octahedral
and icosahedral cases).  The cyclic case is the one where some orbit of poles has stabilizer all of `H`, i.e.
`H` fixes a pole.  (The identification of the non-cyclic groups is not proved.) -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem finite_subgroup_SO3_cyclic_or (H : Subgroup SO3) [Fintype H] (hn : 2 ≤ Fintype.card H) :
    IsCyclic H ∨ (∃ r, 2 ≤ r ∧ Fintype.card H = 2 * r) ∨ Fintype.card H = 12 ∨ Fintype.card H = 24 ∨
      Fintype.card H = 60 := by
  classical
  obtain ⟨κ, hκ, m, hm, hsum, hext⟩ := pole_counting_exposed H
  set n := Fintype.card H with hndef
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
  rcases h with h | ⟨r, hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩
  · left
    have hnmem : n ∈ M.sort (· ≤ ·) := by rw [h]; simp
    obtain ⟨k, hk⟩ := hmem' n (hmem n hnmem)
    obtain ⟨p, -, hp⟩ := hext k hk
    exact isCyclic_of_fix H p.1 p.2 fun h ↦ congrArg Subtype.val (hp h)
  · right; left
    have hrmem : r ∈ M.sort (· ≤ ·) := by rw [h]; simp
    obtain ⟨k, hk⟩ := hmem' r (hmem r hrmem)
    exact ⟨r, hk ▸ (hm k).1, hr⟩
  · right; right; left; exact hr
  · right; right; right; left; exact hr
  · right; right; right; right; exact hr

/-! ### Finite subgroups of `SU(2)` -/

/-- The group `SU(2)`. -/
abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- The central element `-1` of `SU(2)`. -/
def negOne : SU2 :=
  ⟨-1, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨by simp [Matrix.mem_unitaryGroup_iff], by simp [Matrix.det_neg]⟩⟩

theorem negOne_val : (negOne : Matrix (Fin 2) (Fin 2) ℂ) = -1 := rfl

theorem negOne_ne_one : negOne ≠ 1 := by
  intro h
  have := congrArg (fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  simp [negOne_val] at this
  norm_num at this

/-- The only elements of order dividing `2` in `SU(2)` are `±1`. -/
theorem sq_eq_one_su2 (g : SU2) (hg : g * g = 1) : g = 1 ∨ g = negOne := by
  have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  have hsq : (g : Matrix (Fin 2) (Fin 2) ℂ) * g = 1 := congrArg Subtype.val hg
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  set a := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  have h2 : a * (a + d) = 2 := by linear_combination e00 + hdet
  have hne : a + d ≠ 0 := fun h ↦ by rw [h] at h2; simp at h2
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hne
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hne
  have ha : a * a = 1 := by rw [hb] at e00; linear_combination e00
  have hd : a * d = 1 := by rw [hb, hc] at hdet; linear_combination hdet
  have had : d = a := by
    have : a * (a - d) = 0 := by linear_combination ha - hd
    have ha0 : a ≠ 0 := fun h ↦ by rw [h] at ha; simp at ha
    have := (mul_eq_zero.mp this).resolve_left ha0
    linear_combination -this
  have ha' : (a - 1) * (a + 1) = 0 := by linear_combination ha
  rcases mul_eq_zero.mp ha' with h | h
  · left
    apply Subtype.ext
    have ha1 : a = 1 := by linear_combination h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> first | exact ha1 | exact hb | exact hc | exact had.trans ha1
  · right
    apply Subtype.ext
    have ha1 : a = -1 := by linear_combination h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [negOne_val] <;> first | exact ha1 | exact hb | exact hc | exact had.trans ha1

theorem rotSU2_comp_injective (K : Subgroup SU2) (hneg : negOne ∉ K) :
    Function.Injective (rotSU2.comp K.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have h1 : rotSU2 (x : SU2) = 1 := hx
  rcases (rotSU2_eq_one_iff _).mp h1 with h | h
  · exact (Subgroup.mem_bot).mpr (Subtype.ext (Subtype.ext h))
  · exfalso
    apply hneg
    have : (x : SU2) = negOne := Subtype.ext h
    rw [← this]
    exact x.2

/-- **Problem 3.24(b), odd case.**  A finite subgroup of `SU(2)` of odd order is cyclic.  (Its image in `SO(3)` is
isomorphic to it, since `-1` is the only nontrivial element of the kernel and has even order, and the image has
odd order, so it is cyclic by the classification of the orders of finite subgroups of `SO(3)`.) -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem finite_subgroup_SU2_odd_cyclic (K : Subgroup SU2) [Finite K] (hodd : Odd (Nat.card K)) :
    IsCyclic K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hneg : negOne ∉ K := by
    intro h
    let e : K := ⟨negOne, h⟩
    have he1 : e ≠ 1 := fun h' ↦ negOne_ne_one (congrArg Subtype.val h')
    have he2 : e ^ 2 = 1 := by
      apply Subtype.ext
      rcases (sq_eq_one_su2 negOne (by
        apply Subtype.ext
        simp [negOne_val])) with h'' | h''
      · exact absurd h'' negOne_ne_one
      · show negOne ^ 2 = 1
        rw [pow_two]
        apply Subtype.ext
        simp [negOne_val]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
    have hdvd : orderOf e ∣ Nat.card K := orderOf_dvd_natCard e
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hinj := rotSU2_comp_injective K hneg
  let f : K →* SO3 := rotSU2.comp K.subtype
  let e : K ≃* f.range := MonoidHom.ofInjective hinj
  haveI : Finite f.range := Finite.of_equiv K e.toEquiv
  haveI : Fintype f.range := Fintype.ofFinite _
  have hcard : Fintype.card f.range = Nat.card K := by
    rw [← Nat.card_eq_fintype_card]; exact (Nat.card_congr e.toEquiv.symm)
  by_cases h1 : Nat.card K = 1
  · haveI : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have hpos : 0 < Nat.card K := Nat.card_pos
    have hn : 2 ≤ Fintype.card f.range := by omega
    refine (MulEquiv.isCyclic e).mpr ?_
    rcases finite_subgroup_SO3_cyclic_or f.range hn with h | ⟨r, -, hr⟩ | h | h | h
    · exact h
    · exfalso; rw [hcard] at hr; obtain ⟨k, hk⟩ := hodd; omega
    · exfalso; rw [hcard] at h; obtain ⟨k, hk⟩ := hodd; omega
    · exfalso; rw [hcard] at h; obtain ⟨k, hk⟩ := hodd; omega
    · exfalso; rw [hcard] at h; obtain ⟨k, hk⟩ := hodd; omega

/-- **Problem 3.24(b), even case.**  A finite subgroup `K` of `SU(2)` of even order contains `-1` (the only element
of order `2`) and is the full preimage of its image in `SO(3)` under the double cover `rotSU2`. -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem finite_subgroup_SU2_even (K : Subgroup SU2) [Finite K] (heven : Even (Nat.card K)) :
    negOne ∈ K ∧ K = (K.map rotSU2).comap rotSU2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.mp heven)
  have hx1 : x ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx; omega
  have hx2 : x * x = 1 := by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hx.dvd
  have hneg : negOne ∈ K := by
    rcases sq_eq_one_su2 (x : SU2) (congrArg Subtype.val hx2) with h | h
    · exact absurd (Subtype.ext h) hx1
    · rw [← h]; exact x.2
  refine ⟨hneg, ?_⟩
  rw [Subgroup.comap_map_eq]
  refine (sup_eq_left.mpr ?_).symm
  intro g hg
  rcases (rotSU2_eq_one_iff g).mp hg with h | h
  · have : g = 1 := Subtype.ext h
    rw [this]; exact K.one_mem
  · have : g = negOne := Subtype.ext h
    rw [this]; exact hneg

end FiniteRotations

end UndergradKB.RepresentationTheory
