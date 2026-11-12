import UndergradKB.RepresentationTheory.FrobeniusDivisibility
import UndergradKB.RepresentationTheory.RootsOfUnity
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

/-! # Burnside's theorem (Etingof et al., §4.5 to §4.7)

* Theorem 4.21: if the conjugacy class of `g` has size prime to `dim V` (`V` irreducible complex), then `χ_V(g) = 0`
  or `g` acts on `V` by a scalar. Uses Lemma 4.22 (`eq_or_sum_eq_zero_of_isIntegral_average`) and Proposition 4.17.
* Lemma 4.24 and Theorem 4.23: a conjugacy class of prime-power size `p^k`, `k > 0`, forces a proper nontrivial normal
  subgroup.
* Theorem 4.20 (Burnside): a group of order `p^a q^b` is solvable.
-/

namespace UndergradKB.RepresentationTheory

open Module Polynomial Representation

section Eigen

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem eq_smul_id_of_forall_mem_roots (T : Module.End ℂ V) (m : ℕ) (hm : 0 < m) (hT : T ^ m = 1) (ε : ℂ)
    (h : ∀ μ ∈ T.charpoly.roots, μ = ε) : T = ε • LinearMap.id := by
  have hss : T.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ m - C 1)
    · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).squarefree
    · simp [hT]
  have htop := hss.iSup_eigenspace_eq_top
  have hle : ∀ μ, T.eigenspace μ ≤ T.eigenspace ε := by
    intro μ
    by_cases hμ : T.HasEigenvalue μ
    · rw [h μ ((Polynomial.mem_roots T.charpoly_monic.ne_zero).mpr
        ((Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).mp hμ))]
    · rw [Module.End.hasEigenvalue_iff, not_not] at hμ
      rw [hμ]
      exact bot_le
  have htop' : T.eigenspace ε = ⊤ := top_unique (htop ▸ iSup_le hle)
  ext v
  have hv : v ∈ T.eigenspace ε := htop' ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hv
  simp [hv]

theorem pow_eq_one_of_mem_roots (T : Module.End ℂ V) (m : ℕ) (hT : T ^ m = 1) {μ : ℂ}
    (hμ : μ ∈ T.charpoly.roots) : μ ^ m = 1 := by
  have hroot := (Polynomial.mem_roots T.charpoly_monic.ne_zero).mp hμ
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).mpr hroot).exists_hasEigenvector
  have h1 : (T ^ m) v = μ ^ m • v := hv.pow_apply m
  rw [hT, one_apply_eq_self] at h1
  have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv.2

theorem trace_eq_sum_roots (T : Module.End ℂ V) : LinearMap.trace ℂ V T = T.charpoly.roots.sum :=
  Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)

theorem card_roots_charpoly (T : Module.End ℂ V) : T.charpoly.roots.card = finrank ℂ V := by
  rw [(Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)), LinearMap.charpoly_natDegree]

end Eigen

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ G V) [IsIrreducible ρ]

/-- **Etingof et al., Theorem 4.21**: let `V` be an irreducible complex representation of a finite group and `g` an
element whose conjugacy class has size prime to `dim V`. Then either `χ_V(g) = 0` or `g` acts on `V` by a scalar. -/
@[kb "etingof2011" "Theorem 4.21, p. 52"]
theorem character_eq_zero_or_eq_smul (g : G) (hcop : Nat.Coprime (conjCard g) (finrank ℂ V)) :
    ρ.character g = 0 ∨ ∃ c : ℂ, ρ g = c • LinearMap.id := by
  set T := ρ g with hTdef
  set s := T.charpoly.roots with hsdef
  have hd := finrank_ne_zero' ρ
  have hsum : ρ.character g = s.sum := trace_eq_sum_roots T
  have hcard : s.card = finrank ℂ V := card_roots_charpoly T
  have hm : 0 < orderOf g := orderOf_pos g
  have hTm : T ^ orderOf g = 1 := by rw [hTdef, ← map_pow, pow_orderOf_eq_one, map_one]
  have hroot : ∀ μ ∈ s, μ ^ orderOf g = 1 := fun μ hμ ↦ pow_eq_one_of_mem_roots T _ hTm hμ
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have huv' : (u : ℂ) * conjCard g + v * finrank ℂ V = 1 := by exact_mod_cast huv
  have hint : IsIntegral ℤ (s.sum / s.card) := by
    have : s.sum / s.card = u * ((conjCard g : ℂ) * ρ.character g / finrank ℂ V) + v * ρ.character g := by
      rw [hcard, ← hsum]
      have e : (v : ℂ) * ρ.character g = v * ρ.character g * (finrank ℂ V * (finrank ℂ V : ℂ)⁻¹) := by
        rw [mul_inv_cancel₀ hd, mul_one]
      rw [e, div_eq_mul_inv, div_eq_mul_inv]
      linear_combination (- ρ.character g * (finrank ℂ V : ℂ)⁻¹) * huv'
    rw [this]
    exact (isIntegral_algebraMap.mul (isIntegral_conjCard_mul_character_div ρ g)).add
      (isIntegral_algebraMap.mul (isIntegral_character ρ g))
  -- pass to a family indexed by `Fin s.toList.length`
  let l := s.toList
  have hl : l.length = s.card := Multiset.length_toList s
  have hne : 0 < l.length := by rw [hl, hcard]; exact Nat.pos_of_ne_zero fun h ↦ hd (by rw [h, Nat.cast_zero])
  have : Nonempty (Fin l.length) := ⟨⟨0, hne⟩⟩
  let ε : Fin l.length → ℂ := fun i ↦ l[i]
  have hεsum : ∑ i, ε i = s.sum := by
    rw [← Multiset.sum_toList]
    exact Fin.sum_univ_getElem l
  have hεmem : ∀ i, ε i ∈ s := fun i ↦ Multiset.mem_toList.mp (List.getElem_mem _)
  have hcardι : (Fintype.card (Fin l.length) : ℂ) = s.card := by rw [Fintype.card_fin, hl]
  rcases eq_or_sum_eq_zero_of_isIntegral_average ε (orderOf g) hm (fun i ↦ hroot _ (hεmem i))
      (by rw [hεsum, hcardι]; exact hint) with hall | hzero
  · right
    refine ⟨ε ⟨0, hne⟩, eq_smul_id_of_forall_mem_roots T _ hm hTm _ fun μ hμ ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (Multiset.mem_toList.mpr hμ)
    exact hall ⟨i, hi⟩ _
  · left
    rw [hsum, ← hεsum, hzero]


/-! ### The trivial representation as an irreducible representation -/

section Trivial

universe v

variable (G : Type v) [Group G]

instance : FiniteDimensional ℂ (ULift.{v} ℂ) :=
  Module.Finite.equiv (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm

theorem finrank_ulift_complex : finrank ℂ (ULift.{v} ℂ) = 1 := by
  rw [(ULift.moduleEquiv (R := ℂ) (M := ℂ)).finrank_eq, Module.finrank_self]

instance isIrreducible_trivial : IsIrreducible (Representation.trivial ℂ G (ULift.{v} ℂ)) where
  exists_pair_ne := ⟨⊥, ⊤, fun h ↦ by
    have h' := congrArg Subrepresentation.toSubmodule h
    have : (⟨1⟩ : ULift.{v} ℂ) ∈ (⊥ : Subrepresentation (Representation.trivial ℂ G (ULift.{v} ℂ))) :=
      h ▸ (show (⟨1⟩ : ULift.{v} ℂ) ∈ (⊤ : Submodule ℂ (ULift.{v} ℂ)) from Submodule.mem_top)
    have h0 : (⟨1⟩ : ULift.{v} ℂ) = 0 := (Submodule.mem_bot ℂ).mp this
    exact one_ne_zero (congrArg ULift.down h0)⟩
  eq_bot_or_eq_top W := by
    by_cases h : ∃ x ∈ W, x ≠ 0
    · right
      obtain ⟨x, hx, hx0⟩ := h
      apply Subrepresentation.toSubmodule_injective
      refine eq_top_iff.mpr fun y _ ↦ ?_
      have hxd : x.down ≠ 0 := fun h0 ↦ hx0 (ULift.ext h0)
      have : y = (y.down / x.down) • x := by
        ext; simp [hxd]
      rw [this]
      exact W.toSubmodule.smul_mem _ hx
    · left
      push Not at h
      apply Subrepresentation.toSubmodule_injective
      exact eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot ℂ).mpr (h x hx)

/-- The trivial one-dimensional representation, as an irreducible representation. -/
noncomputable def trivialIrrRep : IrrRep ℂ G where
  V := ULift.{v} ℂ
  ρ := Representation.trivial ℂ G (ULift.{v} ℂ)

theorem character_trivialIrrRep : (trivialIrrRep G).ρ.character = 1 := by
  funext g
  have : Representation.trivial ℂ G (ULift.{v} ℂ) g = LinearMap.id := by ext; simp
  show LinearMap.trace ℂ (ULift.{v} ℂ) (Representation.trivial ℂ G (ULift.{v} ℂ) g) = 1
  rw [this, LinearMap.trace_id, finrank_ulift_complex, Nat.cast_one]

end Trivial


/-! ### Prime-power conjugacy classes -/

section Applications

universe w

variable {G : Type w} [Group G] [Fintype G]

theorem not_isConj_one_of_conjCard_ne_one (g : G) (hg : conjCard g ≠ 1) : ¬ IsConj g 1 := by
  intro h
  rw [isConj_one_left] at h
  subst h
  apply hg
  unfold conjCard
  rw [Finset.card_eq_one]
  exact ⟨1, by ext x; simp⟩

theorem not_isIntegral_inv_prime {p : ℕ} (hp : p.Prime) : ¬ IsIntegral ℤ ((p : ℂ)⁻¹) := by
  intro h
  have hq : algebraMap ℚ ℂ ((p : ℚ)⁻¹) = (p : ℂ)⁻¹ := by simp
  rw [← hq, ← Algebra.ofId_apply, ← AlgHom.coe_restrictScalars' ℤ (Algebra.ofId ℚ ℂ),
    isIntegral_algHom_iff _ (algebraMap ℚ ℂ).injective, IsIntegrallyClosed.isIntegral_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [algebraMap_int_eq, eq_intCast] at hn
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : (n : ℚ) * p = 1 := by rw [hn, inv_mul_cancel₀ hp0]
  have hz : n * (p : ℤ) = 1 := by exact_mod_cast h1
  have hdvd : (p : ℤ) ∣ 1 := ⟨n, by rw [mul_comm]; exact hz.symm⟩
  have : p ∣ 1 := by exact_mod_cast hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Etingof et al., Lemma 4.24**: if the conjugacy class of `g` has `p^k` elements with `k > 0`, some nontrivial
irreducible complex representation has dimension prime to `p` and a character not vanishing at `g`. -/
@[kb "etingof2011" "Lemma 4.24, p. 53"]
theorem exists_irrRep_of_conjCard_eq_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (g : G)
    (hg : conjCard g = p ^ k) :
    ∃ X : IrrRep ℂ G, X.ρ.character ≠ 1 ∧ ¬ p ∣ finrank ℂ X.V ∧ X.ρ.character g ≠ 0 := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  by_contra H
  push Not at H
  have hng : ¬ IsConj g 1 :=
    not_isConj_one_of_conjCard_ne_one g (by rw [hg]; exact (Nat.one_lt_pow hk.ne' hp.one_lt).ne')
  have hcol := sum_irrChars_mul_inv (k := ℂ) g 1
  rw [if_neg hng, inv_one] at hcol
  have htriv : (1 : G → ℂ) ∈ irrChars ℂ G := ⟨trivialIrrRep G, character_trivialIrrRep G⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨1, htriv⟩)] at hcol
  have hterm : ∀ χ ∈ Finset.univ.erase (⟨1, htriv⟩ : irrChars ℂ G),
      ∃ t : ℂ, IsIntegral ℤ t ∧ (χ : G → ℂ) g * (χ : G → ℂ) 1 = p * t := by
    intro χ hχ
    obtain ⟨X, hX'⟩ := χ.2
    have hX : X.ρ.character = (χ : G → ℂ) := hX'
    have hne : X.ρ.character ≠ 1 := by
      intro h
      exact (Finset.mem_erase.mp hχ).1 (Subtype.ext (hX.symm.trans h))
    have h1 : (χ : G → ℂ) 1 = finrank ℂ X.V := by rw [← hX, char_one]
    by_cases hd : p ∣ finrank ℂ X.V
    · obtain ⟨d, hd⟩ := hd
      refine ⟨(χ : G → ℂ) g * d, ?_, ?_⟩
      · rw [← hX]
        exact (isIntegral_character X.ρ g).mul (by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (d : ℤ)))
      · rw [h1, hd]; push_cast; ring
    · refine ⟨0, isIntegral_zero, ?_⟩
      rw [← hX, H X hne hd, zero_mul, mul_zero]
  choose! t ht using hterm
  have hsum : ∑ χ ∈ Finset.univ.erase (⟨1, htriv⟩ : irrChars ℂ G), (χ : G → ℂ) g * (χ : G → ℂ) 1 =
      p * ∑ χ ∈ Finset.univ.erase (⟨1, htriv⟩ : irrChars ℂ G), t χ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ ↦ (ht χ hχ).2
  rw [hsum] at hcol
  simp only [Pi.one_apply, mul_one] at hcol
  have hS : IsIntegral ℤ (∑ χ ∈ Finset.univ.erase (⟨1, htriv⟩ : irrChars ℂ G), t χ) :=
    IsIntegral.sum _ fun χ hχ ↦ (ht χ hχ).1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : ℂ)⁻¹ = -(∑ χ ∈ Finset.univ.erase (⟨1, htriv⟩ : irrChars ℂ G), t χ) := by
    field_simp
    linear_combination hcol
  exact not_isIntegral_inv_prime hp (this ▸ hS.neg)

/-- An irreducible representation on which `G` acts trivially is one-dimensional. -/
theorem finrank_eq_one_of_forall_eq_one (X : IrrRep ℂ G) (htriv : ∀ h, X.ρ h = 1) : finrank ℂ X.V = 1 := by
  have hd := finrank_ne_zero' X.ρ
  have : Nontrivial X.V := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero fun h0 ↦ hd (by rw [h0, Nat.cast_zero]))
  obtain ⟨v, hv⟩ := exists_ne (0 : X.V)
  let W : Subrepresentation X.ρ :=
    ⟨ℂ ∙ v, fun h x hx ↦ by rw [htriv h]; exact hx⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top W with hW | hW
  · have : v ∈ (⊥ : Subrepresentation X.ρ) := hW ▸ Submodule.mem_span_singleton_self v
    exact absurd ((Submodule.mem_bot ℂ).mp this) hv
  · have hW' : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hW
    rw [← finrank_top ℂ X.V, ← hW', finrank_span_singleton hv]

/-- **Etingof et al., Theorem 4.23**: if a conjugacy class of a finite group has `p^k` elements with `p` prime and
`k > 0`, the group has a normal subgroup other than `1` and itself (so it is not simple). -/
@[kb "etingof2011" "Theorem 4.23, p. 53"]
theorem exists_normal_of_conjCard_eq_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (g : G)
    (hg : conjCard g = p ^ k) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  obtain ⟨X, hX1, hXp, hXg⟩ := exists_irrRep_of_conjCard_eq_prime_pow hp hk g hg
  have hcop : Nat.Coprime (conjCard g) (finrank ℂ X.V) := by
    rw [hg]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hXp)
  rcases character_eq_zero_or_eq_smul X.ρ g hcop with h0 | ⟨c, hc⟩
  · exact absurd h0 hXg
  refine ⟨X.ρ.ker, inferInstance, ?_, ?_⟩
  · intro hker
    have hinj : Function.Injective X.ρ := (MonoidHom.ker_eq_bot_iff _).mp hker
    have hcomm : ∀ h : G, h * g = g * h := by
      intro h
      apply hinj
      rw [map_mul, map_mul, hc]
      ext v
      simp
    have h1 : conjCard g = 1 := by
      unfold conjCard
      rw [Finset.card_eq_one]
      refine ⟨g, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hx
        obtain ⟨c', hc'⟩ := isConj_iff.mp hx
        calc x = c'⁻¹ * (c' * x * c'⁻¹) * c' := by group
          _ = g := by rw [hc', hcomm c'⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      · rintro rfl
        exact IsConj.refl _
    rw [hg] at h1
    exact (Nat.one_lt_pow hk.ne' hp.one_lt).ne' h1
  · intro hker
    have htriv : ∀ h, X.ρ h = 1 := fun h ↦ (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top h)
    apply hX1
    have hdim := finrank_eq_one_of_forall_eq_one X htriv
    funext h
    rw [Pi.one_apply, character, htriv h, Module.End.one_eq_id, LinearMap.trace_id, hdim, Nat.cast_one]

end Applications


/-! ### Burnside's theorem -/

section BurnsideThm

universe w

theorem isSolvable_of_normal {G : Type w} [Group G] (N : Subgroup G) [N.Normal] (h1 : Group.IsSolvable N)
    (h2 : Group.IsSolvable (G ⧸ N)) : Group.IsSolvable G :=
  Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem conjCard_eq_index {G : Type w} [Group G] [Fintype G] (g : G) :
    conjCard g = (Subgroup.centralizer {g}).index := by
  have h1 := card_isConj_mul_card_centralizer g
  have h2 := (Subgroup.centralizer {g}).index_mul_card
  have hC : 0 < Nat.card (Subgroup.centralizer {g}) := Nat.card_pos
  have h3 : Nat.card {x // IsConj x g} = conjCard g := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [← h3]
  exact Nat.eq_of_mul_eq_mul_right hC (h1.trans h2.symm)

open scoped Classical in
theorem mem_center_of_conjCard_eq_one {G : Type w} [Group G] [Fintype G] {g : G} (h : conjCard g = 1) :
    g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro x
  have hle := h.le
  unfold conjCard at hle
  have hx : x * g * x⁻¹ = g :=
    Finset.card_le_one.mp hle _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isConj_iff.mpr ⟨x⁻¹, by group⟩⟩) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl g⟩)
  calc x * g = x * g * x⁻¹ * x := by group
    _ = g * x := by rw [hx]

/-- Burnside's theorem in the form used for the induction: a finite group all of whose prime divisors are `p` or
`q` is solvable. -/
theorem isSolvable_of_forall_prime_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ∀ (n : ℕ) (G : Type w) [Group G] [Finite G], Nat.card G = n →
      (∀ r : ℕ, r.Prime → r ∣ Nat.card G → r = p ∨ r = q) → Group.IsSolvable G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hprimes
  have : Fintype G := Fintype.ofFinite G
  have reduce : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≠ ⊤ → Group.IsSolvable G := by
    intro N hN hbot htop
    have hidx := N.index_mul_card
    have hc1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hbot
    have hi1 : 1 < N.index := Subgroup.one_lt_index_of_ne_top htop
    have hNlt : Nat.card N < n := by rw [← hn, ← hidx]; nlinarith
    have hQlt : Nat.card (G ⧸ N) < n := by rw [← Subgroup.index_eq_card, ← hn, ← hidx]; nlinarith
    have h1 : Group.IsSolvable N := ih _ hNlt N rfl fun r hr hrd ↦
      hprimes r hr (dvd_trans hrd (Subgroup.card_subgroup_dvd_card N))
    have h2 : Group.IsSolvable (G ⧸ N) := ih _ hQlt (G ⧸ N) rfl fun r hr hrd ↦
      hprimes r hr (dvd_trans hrd (by rw [← Subgroup.index_eq_card]; exact N.index_dvd_card))
    exact isSolvable_of_normal N h1 h2
  by_cases hqd : q ∣ Nat.card G
  · have : Fact q.Prime := ⟨hq⟩
    let Q : Sylow q G := Classical.arbitrary _
    have hQbot : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card hqd
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot _).mpr hQbot
    have := Q.isPGroup.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Q)
    set g : G := ((z : Q) : G) with hgdef
    have hg1 : g ≠ 1 := by
      intro h
      apply hz
      exact Subtype.ext (Subtype.ext h)
    have hQC : (Q : Subgroup G) ≤ Subgroup.centralizer {g} := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
      exact (congrArg Subtype.val this).symm
    have hdvd : conjCard g ∣ (Q : Subgroup G).index := by
      rw [conjCard_eq_index]; exact Subgroup.index_dvd_of_le hQC
    have hnq : ¬ q ∣ (Q : Subgroup G).index := Q.not_dvd_index
    obtain ⟨k, hk⟩ : ∃ k, conjCard g = p ^ k := by
      refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (conjCard_pos g).ne' fun {r} hr hrd ↦ ?_⟩
      have hrG : r ∣ Nat.card G := dvd_trans hrd (dvd_trans hdvd (Subgroup.index_dvd_card _))
      rcases hprimes r hr hrG with h | h
      · exact h
      · have h' := dvd_trans hrd hdvd
        rw [h] at h'
        exact absurd h' hnq
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero] at hk
      have hcen := mem_center_of_conjCard_eq_one hk
      by_cases hZ : Subgroup.center G = ⊤
      · exact Group.isSolvable_of_comm fun a b ↦
          (Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top b) a)
      · refine reduce (Subgroup.center G) inferInstance (fun h ↦ hg1 ?_) hZ
        rw [h] at hcen
        exact (Subgroup.mem_bot).mp hcen
    · obtain ⟨N, hN, hbot, htop⟩ := exists_normal_of_conjCard_eq_prime_pow hp hkpos g hk
      exact reduce N hN hbot htop
  · have : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p G := IsPGroup.of_card
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrd ↦
        (hprimes r hr hrd).resolve_right fun h ↦ hqd (h ▸ hrd))
    have := hpg.isNilpotent
    infer_instance

/-- **Etingof et al., Theorem 4.20** (Burnside): a group of order `p^a q^b`, with `p` and `q` prime, is solvable. -/
@[kb "etingof2011" "Theorem 4.20, p. 52"]
theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type w} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hG : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  refine isSolvable_of_forall_prime_dvd hp hq _ G rfl fun r hr hrd ↦ ?_
  rw [hG] at hrd
  rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h))

end BurnsideThm

end UndergradKB.RepresentationTheory
