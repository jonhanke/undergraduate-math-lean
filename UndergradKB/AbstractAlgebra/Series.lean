import Mathlib.Order.JordanHolder
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group
import UndergradKB.Common.Attr

/-! # Judson–Beezer, section 13.2: subnormal and composition series, Jordan–Hölder

Mathlib proves Jordan–Hölder for any `JordanHolderLattice` but has no instance for the subgroup
lattice. Here `Subgroup G` becomes a `JordanHolderLattice` (`IsMaximal H K` means `H` is a maximal
normal subgroup of `K`), `isMaxNormalIn_iff_isSimpleGroup` identifies this with "`K / H` is simple",
and `jordan_holder_group` is the book's theorem for subnormal series with simple factors. -/

open scoped Pointwise

namespace UndergradKB.AbstractAlgebra

section Core

variable {G : Type*} [Group G]

/-- `H` is a normal subgroup of the subgroup `K` (so `H ≤ K` and `K` normalizes `H`). -/
def NormalIn (H K : Subgroup G) : Prop := H ≤ K ∧ K ≤ Subgroup.normalizer (H : Set G)

theorem normalIn_iff {H K : Subgroup G} :
    NormalIn H K ↔ H ≤ K ∧ (H.subgroupOf K).Normal :=
  and_congr_right fun h => (Subgroup.normal_subgroupOf_iff_le_normalizer h).symm

theorem normalIn_iff_conj {H K : Subgroup G} :
    NormalIn H K ↔ H ≤ K ∧ ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H :=
  and_congr_right fun _ => Subgroup.le_normalizer_iff

theorem NormalIn.conj_mem {H K : Subgroup G} (h : NormalIn H K) {k : G} (hk : k ∈ K) {a : G}
    (ha : a ∈ H) : k * a * k⁻¹ ∈ H :=
  (normalIn_iff_conj.1 h).2 k hk a ha

theorem conj_mem_sup {A B : Subgroup G} {k : G} (hA : ∀ a ∈ A, k * a * k⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, k * b * k⁻¹ ∈ A ⊔ B) {m : G} (hm : m ∈ A ⊔ B) : k * m * k⁻¹ ∈ A ⊔ B := by
  have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj k).toMonoidHom := sup_le hA hB
  simpa using this hm

/-- `H` is a maximal normal subgroup of `K` (the notion of maximality in the Jordan-Hölder
lattice of subgroups). -/
def IsMaxNormalIn (H K : Subgroup G) : Prop :=
  NormalIn H K ∧ H ≠ K ∧ ∀ L, NormalIn L K → H ≤ L → L = H ∨ L = K

theorem isMaxNormalIn_sup_eq {x y z : Subgroup G} (hx : IsMaxNormalIn x z)
    (hy : IsMaxNormalIn y z) (hne : x ≠ y) : x ⊔ y = z := by
  have hn : NormalIn (x ⊔ y) z := by
    rw [normalIn_iff_conj]
    refine ⟨sup_le hx.1.1 hy.1.1, fun k hk m hm => ?_⟩
    exact conj_mem_sup (fun a ha => Subgroup.mem_sup_left (hx.1.conj_mem hk ha))
      (fun a ha => Subgroup.mem_sup_right (hy.1.conj_mem hk ha)) hm
  rcases hx.2.2 _ hn le_sup_left with h | h
  · exfalso
    have hyx : y ≤ x := le_sup_right.trans h.le
    rcases hy.2.2 x hx.1 hyx with h' | h'
    · exact hne h'
    · exact hx.2.1 h'
  · exact h

theorem isMaxNormalIn_inf {x y : Subgroup G} (_hx : IsMaxNormalIn x (x ⊔ y))
    (hy : IsMaxNormalIn y (x ⊔ y)) : IsMaxNormalIn (x ⊓ y) x := by
  have hxz : x ≤ x ⊔ y := le_sup_left
  have hyz : y ≤ x ⊔ y := le_sup_right
  refine ⟨?_, ?_, ?_⟩
  · rw [normalIn_iff_conj]
    exact ⟨inf_le_left, fun k hk h hh =>
      ⟨x.mul_mem (x.mul_mem hk hh.1) (x.inv_mem hk), hy.1.conj_mem (hxz hk) hh.2⟩⟩
  · intro h
    have hxy : x ≤ y := inf_eq_left.1 h
    have : x ⊔ y = y := sup_eq_right.2 hxy
    exact hy.2.1 this.symm
  · intro L hL hle
    have hLx := hL.1
    have hLz : L ≤ x ⊔ y := hLx.trans hxz
    have hMn : NormalIn (L ⊔ y) (x ⊔ y) := by
      refine ⟨sup_le hLz hyz, sup_le ?_ ?_⟩
      · refine Subgroup.le_normalizer_iff.2 fun k hk m hm => ?_
        exact conj_mem_sup (fun a ha => Subgroup.mem_sup_left (hL.conj_mem hk ha))
          (fun b hb => Subgroup.mem_sup_right (hy.1.conj_mem (hxz hk) hb)) hm
      · refine Subgroup.le_normalizer_iff.2 fun k hk m hm => ?_
        refine conj_mem_sup (fun a ha => ?_) (fun b hb => Subgroup.mem_sup_right (y.mul_mem
          (y.mul_mem hk hb) (y.inv_mem hk))) hm
        have h1 : a⁻¹ * k * a⁻¹⁻¹ ∈ y := hy.1.conj_mem ((x ⊔ y).inv_mem (hLz ha)) hk
        have e : k * a * k⁻¹ = a * ((a⁻¹ * k * a⁻¹⁻¹) * k⁻¹) := by group
        rw [e]
        exact (L ⊔ y).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (y.mul_mem h1 (y.inv_mem hk)))
    rcases hy.2.2 (L ⊔ y) hMn le_sup_right with hM | hM
    · left
      have : L ≤ y := le_sup_left.trans hM.le
      exact le_antisymm (le_inf hLx this) hle
    · right
      refine le_antisymm hLx (fun a ha => ?_)
      have hmem : a ∈ (↑(L ⊔ y) : Set G) := by
        rw [hM]; exact hxz ha
      rw [Subgroup.coe_mul_of_left_le_normalizer_right L y (hLz.trans hy.1.2)] at hmem
      obtain ⟨l, hl, y', hy', rfl⟩ := Set.mem_mul.1 hmem
      have hy'x : y' ∈ x := by
        have := x.mul_mem (x.inv_mem (hLx hl)) ha
        simpa using this
      exact L.mul_mem hl (hle ⟨hy'x, hy'⟩)

/-- The subgroup lattice of a group is a Jordan-Hölder lattice, with `IsMaximal H K` meaning that
`H` is a maximal normal subgroup of `K`. -/
instance : JordanHolderLattice (Subgroup G) where
  IsMaximal := IsMaxNormalIn
  lt_of_isMaximal h := lt_of_le_of_ne h.1.1 h.2.1
  sup_eq_of_isMaximal := isMaxNormalIn_sup_eq
  isMaximal_inf_left_of_isMaximal_sup := isMaxNormalIn_inf

/-- The factor group `K / H`, for `H` normal in `K`. It is defined for all pairs through the normal
core of `H` in `K`, which is `H` itself when `H` is normal in `K`. -/
abbrev Factor (H K : Subgroup G) : Type _ := ↥K ⧸ (H.subgroupOf K).normalCore

/-- When `H` is normal in `K`, `Factor H K` is the ordinary quotient group. -/
noncomputable def factorEquiv (H K : Subgroup G) [hn : (H.subgroupOf K).Normal] :
    Factor H K ≃* ↥K ⧸ H.subgroupOf K :=
  QuotientGroup.quotientMulEquivOfEq (Subgroup.normalCore_eq_self _)

/-- Second isomorphism theorem for the factors: `(x ⊔ y) / x ≅ y / (x ⊓ y)` when `x` is normal in
`x ⊔ y`. -/
theorem factor_second_iso {x y : Subgroup G} (h : NormalIn x (x ⊔ y)) :
    Nonempty (Factor x (x ⊔ y) ≃* Factor (x ⊓ y) y) := by
  have hn : (x.subgroupOf (x ⊔ y)).Normal := (normalIn_iff.1 h).2
  let φ : y →* (↥(x ⊔ y) ⧸ x.subgroupOf (x ⊔ y)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)
  have hφ : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨g, hg⟩ := g
      have hg' : g ∈ (↑(x ⊔ y) : Set G) := hg
      rw [Subgroup.coe_mul_of_right_le_normalizer_left x y (le_sup_right.trans h.2)] at hg'
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg'
      refine ⟨⟨b, hb⟩, ?_⟩
      show QuotientGroup.mk _ = _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have := h.conj_mem ((x ⊔ y).inv_mem ((le_sup_right : y ≤ x ⊔ y) hb)) ha
      simpa [mul_assoc] using this
  have hker : φ.ker = (x ⊓ y).subgroupOf y := by
    ext ⟨u, hu⟩
    simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have : ((x ⊓ y).subgroupOf y).Normal := by
    rw [← hker]; infer_instance
  exact ⟨(factorEquiv x (x ⊔ y)).trans ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (factorEquiv (x ⊓ y) y).symm))⟩

end Core

section Simple

variable {G : Type*} [Group G]

theorem isSimpleGroup_quotient_iff {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal] :
    IsSimpleGroup (Γ ⧸ N) ↔ N ≠ ⊤ ∧ ∀ L : Subgroup Γ, L.Normal → N ≤ L → L = N ∨ L = ⊤ := by
  constructor
  · intro hs
    refine ⟨fun h => ?_, fun L hL hNL => ?_⟩
    · have : Subsingleton (Γ ⧸ N) := by
        subst h; exact QuotientGroup.subsingleton_quotient_top
      exact (not_subsingleton (Γ ⧸ N)) this
    · have hM : (L.map (QuotientGroup.mk' N)).Normal := hL.map _ (QuotientGroup.mk'_surjective N)
      rcases Subgroup.Normal.eq_bot_or_eq_top (L.map (QuotientGroup.mk' N)) with h | h
      · left
        refine le_antisymm ?_ hNL
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
        exact h
      · right
        have := Subgroup.comap_map_eq (QuotientGroup.mk' N) L
        rw [h, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hNL] at this
        exact this.symm
  · rintro ⟨hne, h⟩
    have hnt : Nontrivial (Γ ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      apply hne
      rw [eq_top_iff]
      intro g _
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := ?_ }
    intro M hM
    have hL : (M.comap (QuotientGroup.mk' N)).Normal := hM.comap _
    have hle : N ≤ M.comap (QuotientGroup.mk' N) := by
      intro g hg
      rw [Subgroup.mem_comap]
      have : QuotientGroup.mk' N g = 1 := (QuotientGroup.eq_one_iff g).2 hg
      rw [this]
      exact M.one_mem
    have hmc := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) M
    rcases h _ hL hle with h' | h'
    · left
      rw [← hmc, h', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    · right
      rw [← hmc, h', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

/-- AA-202. `H` is a maximal normal subgroup of `K` exactly when `H` is normal in `K` and the
factor group `K / H` is simple. -/
@[kb "judson2026" "Definition (unnumbered) composition series, p. 181"]
theorem isMaxNormalIn_iff_isSimpleGroup {H K : Subgroup G} :
    IsMaxNormalIn H K ↔ NormalIn H K ∧ IsSimpleGroup (Factor H K) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hn : (H.subgroupOf K).Normal := (normalIn_iff.1 h.1).2
    rw [(factorEquiv H K).isSimpleGroup_congr, isSimpleGroup_quotient_iff]
    refine ⟨?_, fun L hL hNL => ?_⟩
    · intro htop
      exact h.2.1 (le_antisymm h.1.1 (Subgroup.subgroupOf_eq_top.1 htop))
    · set L' : Subgroup G := L.map K.subtype with hL'
      have hLK : L'.subgroupOf K = L := Subgroup.comap_map_eq_self_of_injective K.subtype_injective L
      have hL'K : L' ≤ K := Subgroup.map_subtype_le L
      have hNL' : NormalIn L' K := normalIn_iff.2 ⟨hL'K, by rw [hLK]; exact hL⟩
      have hHL' : H ≤ L' := by
        intro g hg
        refine ⟨⟨g, h.1.1 hg⟩, ?_, rfl⟩
        exact hNL (show (⟨g, h.1.1 hg⟩ : K) ∈ H.subgroupOf K from hg)
      rcases h.2.2 L' hNL' hHL' with e | e
      · left
        rw [← hLK, e]
      · right
        rw [← hLK, e, Subgroup.subgroupOf_self]
  · rintro ⟨hN, hs⟩
    have hn : (H.subgroupOf K).Normal := (normalIn_iff.1 hN).2
    rw [(factorEquiv H K).isSimpleGroup_congr, isSimpleGroup_quotient_iff] at hs
    obtain ⟨hne, hmax⟩ := hs
    refine ⟨hN, ?_, fun L hL hHL => ?_⟩
    · intro e
      apply hne
      rw [Subgroup.subgroupOf_eq_top, e]
    · have hLn : (L.subgroupOf K).Normal := (normalIn_iff.1 hL).2
      have := hmax _ hLn (Subgroup.subgroupOf_mono K hHL)
      rcases this with e | e
      · left
        have := Subgroup.subgroupOf_inj.1 e
        rwa [inf_of_le_left hL.1, inf_of_le_left hN.1] at this
      · right
        exact le_antisymm hL.1 (Subgroup.subgroupOf_eq_top.1 e)

end Simple

section Series

variable {G : Type*} [Group G]

/-- AA-201. A subnormal series of subgroups of `G`: a chain `H₀ ≤ H₁ ≤ ⋯ ≤ Hₙ` with each `Hᵢ`
normal in `Hᵢ₊₁` (its length is `n`). It is a series of the group `G` when `H₀ = ⊥`, `Hₙ = ⊤`. -/
@[kb "judson2026" "Definition (unnumbered) subnormal series, p. 180"]
abbrev SubnormalSeries (G : Type*) [Group G] : Type _ :=
  RelSeries {p : Subgroup G × Subgroup G | NormalIn p.1 p.2}

namespace SubnormalSeries

/-- AA-201. The series starts at the trivial subgroup and ends at `G`. -/
def IsSeriesOfGroup (s : SubnormalSeries G) : Prop := s.head = ⊥ ∧ s.last = ⊤

/-- AA-201. A normal series: every member of the series is normal in `G`. -/
@[kb "judson2026" "Definition (unnumbered) normal series, p. 180"]
def IsNormalSeries (s : SubnormalSeries G) : Prop := ∀ i, (s i).Normal

/-- AA-201. `t` is a refinement of `s`: every member of `s` occurs in `t`. -/
@[kb "judson2026" "Definition (unnumbered) refinement, p. 181"]
def IsRefinedBy (s t : SubnormalSeries G) : Prop := ∀ i, ∃ j, s i = t j

/-- AA-201. Two subnormal series are isomorphic: there is a bijection between their factor
positions matching each factor group `Hᵢ₊₁ / Hᵢ` with an isomorphic one. -/
@[kb "judson2026" "Definition (unnumbered) isomorphic series, p. 181"]
def Isomorphic (s t : SubnormalSeries G) : Prop :=
  ∃ e : Fin s.length ≃ Fin t.length, ∀ i : Fin s.length,
    Nonempty (Factor (s i.castSucc) (s i.succ) ≃* Factor (t (e i).castSucc) (t (e i).succ))

/-- AA-202. A composition series: a subnormal series of `G` all of whose factor groups are
simple. -/
@[kb "judson2026" "Definition (unnumbered) composition series, p. 181"]
def IsCompositionSeries (s : SubnormalSeries G) : Prop :=
  s.IsSeriesOfGroup ∧ ∀ i : Fin s.length, IsSimpleGroup (Factor (s i.castSucc) (s i.succ))

/-- AA-202. A principal series: a normal series of `G` all of whose factor groups are simple. -/
@[kb "judson2026" "Definition (unnumbered) principal series, p. 181"]
def IsPrincipalSeries (s : SubnormalSeries G) : Prop :=
  s.IsSeriesOfGroup ∧ s.IsNormalSeries ∧
    ∀ i : Fin s.length, IsSimpleGroup (Factor (s i.castSucc) (s i.succ))

end SubnormalSeries

/-- A subnormal series with simple factors is a `CompositionSeries` of the Jordan-Hölder lattice
`Subgroup G`. -/
def SubnormalSeries.toCompositionSeries (s : SubnormalSeries G)
    (h : ∀ i : Fin s.length, IsSimpleGroup (Factor (s i.castSucc) (s i.succ))) :
    CompositionSeries (Subgroup G) where
  length := s.length
  toFun := s.toFun
  step i := isMaxNormalIn_iff_isSimpleGroup.2 ⟨s.step i, h i⟩

/-- AA-203. Jordan-Hölder for the subgroup lattice: two composition series of subgroups of `G`
with the same bottom and top have the same factor groups up to isomorphism and order. -/
theorem jordan_holder_subgroups (s t : CompositionSeries (Subgroup G)) (hb : s.head = t.head)
    (ht : s.last = t.last) :
    ∃ e : Fin s.length ≃ Fin t.length, ∀ i : Fin s.length,
      Nonempty (Factor (s i.castSucc) (s i.succ) ≃* Factor (t (e i).castSucc) (t (e i).succ)) := by
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder s t hb ht
  refine ⟨e, fun i => ?_⟩
  exact JordanHolderLattice.Iso.rel (fun p q => Nonempty (Factor p.1 p.2 ≃* Factor q.1 q.2))
    ⟨MulEquiv.refl _⟩ (fun ⟨f⟩ => ⟨f.symm⟩) (fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩)
    (fun {x y} (h : IsMaxNormalIn x (x ⊔ y)) => factor_second_iso h.1) (he i)

/-- AA-203. The Jordan-Hölder theorem for groups: any two composition series of a group `G` are
isomorphic (same factor groups up to isomorphism and permutation). -/
@[kb "judson2026" "Theorem 13.2.8, p. 182"]
theorem jordan_holder_group (s t : SubnormalSeries G) (hs : s.IsCompositionSeries)
    (ht : t.IsCompositionSeries) : s.Isomorphic t := by
  have := jordan_holder_subgroups (s.toCompositionSeries hs.2) (t.toCompositionSeries ht.2)
    (hs.1.1.trans ht.1.1.symm) (hs.1.2.trans ht.1.2.symm)
  exact this

end Series

end UndergradKB.AbstractAlgebra
