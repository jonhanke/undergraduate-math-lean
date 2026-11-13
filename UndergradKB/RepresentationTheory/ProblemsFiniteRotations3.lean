import UndergradKB.Common.Attr
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.GroupAction.SubMulAction
import UndergradKB.RepresentationTheory.ProblemsFiniteRotations2

/-! # Problem 3.24: poles of a finite group of rotations

Let `H` be a finite subgroup of `SO(3)`.  A *pole* is a unit vector fixed by some nontrivial element of `H`.
Each nontrivial rotation fixes exactly two unit vectors, so Burnside's lemma applied to the action of `H` on the
set of poles gives the identity `∑_orbits (1 - 1/m_i) = 2 - 2/n`, where `n = |H|` and `m_i` is the order of
the stabilizer of a pole in the `i`-th orbit.
-/

namespace UndergradKB.RepresentationTheory

open Matrix SO3Rot

namespace FiniteRotations

/-- The group `SO(3)`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

theorem isSO3_of_mem (A : SO3) : IsSO3 (A : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h := Matrix.mem_specialOrthogonalGroup_iff.mp A.2
  refine ⟨(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp h.1, (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp h.1, h.2⟩

/-- Unit vectors in `ℝ³`. -/
def Sph : Type := {x : Fin 3 → ℝ // x ⬝ᵥ x = 1}

theorem dot_mulVec_self (A : SO3) (x : Fin 3 → ℝ) :
    ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) ⬝ᵥ ((A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) = x ⬝ᵥ x := by
  have h := (isSO3_of_mem A).2.1
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

instance : MulAction SO3 Sph where
  smul A x := ⟨(A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.1, by rw [dot_mulVec_self]; exact x.2⟩
  one_smul x := Subtype.ext (by simp [HSMul.hSMul, SMul.smul])
  mul_smul A B x := Subtype.ext (by
    simp [HSMul.hSMul, SMul.smul, Matrix.mulVec_mulVec])

theorem smul_val (A : SO3) (x : Sph) : (A • x).1 = (A : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.1 := rfl

/-- A nontrivial rotation fixes exactly two unit vectors. -/
theorem fixed_two (A : SO3) (hA : A ≠ 1) : ∃ p q : Sph, p ≠ q ∧ ∀ y : Sph, A • y = y ↔ y = p ∨ y = q := by
  have hne : (A : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := fun h ↦ hA (Subtype.ext h)
  obtain ⟨v, hv0, hfix⟩ := fixed_axis (isSO3_of_mem A) hne
  have hs : 0 < v ⬝ᵥ v := by
    have h0 : 0 ≤ v ⬝ᵥ v := by
      simp only [dotProduct, Fin.sum_univ_three]
      nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2)]
    exact lt_of_le_of_ne h0 (fun h => hv0 (dotProduct_self_eq_zero.mp h.symm))
  set k : ℝ := 1 / Real.sqrt (v ⬝ᵥ v) with hk
  have hk2 : k ^ 2 * (v ⬝ᵥ v) = 1 := by
    rw [hk, div_pow, Real.sq_sqrt hs.le]
    field_simp
  have hkne : k ≠ 0 := by
    intro h; rw [h] at hk2; simp at hk2
  have hp : (k • v) ⬝ᵥ (k • v) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; linear_combination hk2
  have hq : ((-k) • v) ⬝ᵥ ((-k) • v) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; linear_combination hk2
  refine ⟨⟨k • v, hp⟩, ⟨(-k) • v, hq⟩, ?_, fun y ↦ ?_⟩
  · intro h
    have h' : k • v = (-k) • v := congrArg Subtype.val h
    have : (2 * k) • v = 0 := by rw [two_mul, add_smul]; nth_rewrite 2 [h']; simp
    rcases smul_eq_zero.mp this with h0 | h0
    · exact hkne (by linarith)
    · exact hv0 h0
  · constructor
    · intro hy
      obtain ⟨t, ht⟩ := (hfix y.1).mp (congrArg Subtype.val hy)
      have h1 : t ^ 2 * (v ⬝ᵥ v) = 1 := by
        have := y.2
        rw [ht, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
        linear_combination this
      have h2 : t ^ 2 = k ^ 2 := by
        have : (t ^ 2 - k ^ 2) * (v ⬝ᵥ v) = 0 := by linear_combination h1 - hk2
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · exact absurd h hs.ne'
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
      · left; exact Subtype.ext (by simp [ht, h])
      · right; exact Subtype.ext (by simp [ht, h])
    · rintro (rfl | rfl)
      · exact Subtype.ext ((hfix _).mpr ⟨k, rfl⟩)
      · exact Subtype.ext ((hfix _).mpr ⟨-k, rfl⟩)

section Poles

variable (H : Subgroup SO3)

/-- The poles of `H`: unit vectors fixed by some nontrivial element of `H`; an `H`-stable subset of `Sph`. -/
def poles : SubMulAction H Sph where
  carrier := {p | ∃ h : H, h ≠ 1 ∧ h • p = p}
  smul_mem' := by
    rintro c p ⟨h, hh, hp⟩
    refine ⟨c * h * c⁻¹, fun e ↦ hh (conj_eq_one_iff.mp e), ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hp]

theorem mem_poles {p : Sph} : p ∈ poles H ↔ ∃ h : H, h ≠ 1 ∧ h • p = p := Iff.rfl

theorem poles_finite [Finite H] : (poles H : Set Sph).Finite := by
  have : ∀ h : {h : H // h ≠ 1}, {p : Sph | h.1 • p = p}.Finite := by
    intro h
    obtain ⟨a, b, -, hab⟩ := fixed_two (h.1 : SO3) (fun e ↦ h.2 (Subtype.ext e))
    refine (Set.toFinite ({a, b} : Set Sph)).subset fun y hy ↦ ?_
    exact (hab y).mp hy
  refine (Set.finite_iUnion this).subset fun p hp ↦ ?_
  obtain ⟨h, hh, hp⟩ := hp
  exact Set.mem_iUnion.mpr ⟨⟨h, hh⟩, hp⟩

theorem card_fixedBy_nontrivial [Finite H] (g : H) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (poles H) g) = 2 := by
  obtain ⟨a, b, hne, hab⟩ := fixed_two (g : SO3) (fun e ↦ hg (Subtype.ext e))
  have ha : a ∈ poles H := ⟨g, hg, (hab a).mpr (Or.inl rfl)⟩
  have hb : b ∈ poles H := ⟨g, hg, (hab b).mpr (Or.inr rfl)⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨⟨a, ha⟩, MulAction.mem_fixedBy.mpr (Subtype.ext ((hab a).mpr (Or.inl rfl)))⟩,
    ⟨⟨b, hb⟩, MulAction.mem_fixedBy.mpr (Subtype.ext ((hab b).mpr (Or.inr rfl)))⟩, ?_, ?_⟩
  · intro h
    exact hne (congrArg (fun z => z.1.1) h)
  · ext ⟨⟨y, hy⟩, hfix⟩
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, iff_true]
    rcases (hab y).mp (congrArg Subtype.val (MulAction.mem_fixedBy.mp hfix)) with h | h
    · left; exact Subtype.ext (Subtype.ext h)
    · right; exact Subtype.ext (Subtype.ext h)

end Poles

/-- **The pole counting identity** (Problem 3.24): for a finite subgroup `H` of `SO(3)` of order `n`, the orbits
of poles have stabilizers of orders `m_k ≥ 2` dividing `n`, and `∑_k (1 - 1/m_k) = 2 - 2/n`. -/
theorem pole_counting (H : Subgroup SO3) [Fintype H] :
    ∃ (κ : Type) (_ : Fintype κ) (m : κ → ℕ), (∀ k, 2 ≤ m k ∧ m k ∣ Fintype.card H) ∧
      ∑ k, ((1 : ℚ) - 1 / (m k : ℚ)) = 2 - 2 / (Fintype.card H : ℚ) := by
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
    fun ω ↦ Fintype.card (MulAction.stabilizer H ω.out), fun ω ↦ ⟨?_, ?_⟩, ?_⟩
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


/-- **Problem 3.24(a), orbit data.**  Let `H` be a finite subgroup of `SO(3)` of order `n ≥ 2`.  Then the orbits of
poles of `H` are indexed by a finite type `κ`, with stabilizer orders `m k ≥ 2` dividing `n`, satisfying
`∑ (1 - 1/m k) = 2 - 2/n`, and the multiset of the `m k` is one of: `{n, n}` (cyclic case, two orbits of one
pole each), `{2, 2, r}` with `n = 2 r` (dihedral case), `{2, 3, 3}` with `n = 12` (tetrahedral case),
`{2, 3, 4}` with `n = 24` (octahedral case), `{2, 3, 5}` with `n = 60` (icosahedral case). -/
@[kb "etingof2011" "Problem 3.24, p. 44"]
theorem finite_subgroup_SO3_orbit_data (H : Subgroup SO3) [Fintype H] (hn : 2 ≤ Fintype.card H) :
    ∃ (κ : Type) (_ : Fintype κ) (m : κ → ℕ), (∀ k, 2 ≤ m k ∧ m k ∣ Fintype.card H) ∧
      ∑ k, ((1 : ℚ) - 1 / (m k : ℚ)) = 2 - 2 / (Fintype.card H : ℚ) ∧
      (Finset.univ.val.map m = {Fintype.card H, Fintype.card H} ∨
        (∃ r, Fintype.card H = 2 * r ∧ Finset.univ.val.map m = {2, 2, r}) ∨
        (Fintype.card H = 12 ∧ Finset.univ.val.map m = {2, 3, 3}) ∨
        (Fintype.card H = 24 ∧ Finset.univ.val.map m = {2, 3, 4}) ∨
        (Fintype.card H = 60 ∧ Finset.univ.val.map m = {2, 3, 5})) := by
  classical
  obtain ⟨κ, hκ, m, hm, hsum⟩ := pole_counting H
  refine ⟨κ, hκ, m, hm, hsum, ?_⟩
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
  have key : ∀ l : List ℕ, l = M.sort (· ≤ ·) → ((l : Multiset ℕ) = M) := fun l hl' ↦ hl' ▸ hl
  rcases h with h | ⟨r, hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩ | ⟨hr, h⟩
  · left; rw [← key _ h.symm]; rfl
  · right; left; exact ⟨r, hr, by rw [← key _ h.symm]; rfl⟩
  · right; right; left; exact ⟨hr, by rw [← key _ h.symm]; rfl⟩
  · right; right; right; left; exact ⟨hr, by rw [← key _ h.symm]; rfl⟩
  · right; right; right; right; exact ⟨hr, by rw [← key _ h.symm]; rfl⟩

end FiniteRotations

end UndergradKB.RepresentationTheory
