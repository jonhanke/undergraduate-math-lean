import UndergradKB.Topology.DualityCompact2
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import UndergradKB.Topology.NSSGroups
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Topology.Bases
import Mathlib.Algebra.Polynomial.Roots
import UndergradKB.Common.Attr

/-!
# The weight of a compact abelian group is the cardinality of its dual (TP-491 (i))

Morris, *Topology Without Tears*, Proposition A5.0.18 (i). The weight `w(X)` of a topological space
(Exercises 9.4 #14 of the book) is the least cardinality of a basis of its topology; Mathlib has no
such notion, so we add the small bridging definition `topWeight`.

For an infinite compact Hausdorff abelian group `G` we prove `w(G) = |Ĝ|`:

* `w(G) ≤ |Ĝ|`: `G` is a closed subgroup of the power `T^Ĝ` of the circle (Corollary A5.10.3), and
  `T^ι` has a basis indexed by the finite subsets of `ι × B₀`, `B₀` a countable basis of `T`;
* `|Ĝ| ≤ |B|` for every basis `B`: fix `ε > 0` with the ball of radius `4ε` about `1` in `T`
  containing no nontrivial subgroup (`T` has no small subgroups). Every character maps some basic
  neighbourhood `W` of `1` into the `ε`-ball; for a fixed `W` there are only finitely many such
  characters (cover `G` by finitely many translates `g⁻¹ W` and the circle by finitely many
  `ε`-balls: two characters with the same pattern of balls at the points `g⁻¹` differ by a character
  with values in the `4ε`-ball, which is trivial). So `|Ĝ| ≤ |B| · ℵ₀ = |B|`, `B` being infinite
  because `G` is an infinite Hausdorff space.
-/

open Topology Set TopologicalSpace Cardinal Metric

set_option linter.unusedSectionVars false

universe u

namespace UndergradKB.Topology

section Weight

variable {X : Type u} [TopologicalSpace X]

/-- Morris, Topology Without Tears, Exercises 9.4 #14: the weight of a topological space, the least
cardinality of a basis of its topology. -/
@[kb "morris2024" "Exercises 9.4 #14, p. 247"]
noncomputable def topWeight (X : Type u) [TopologicalSpace X] : Cardinal.{u} :=
  ⨅ B : {B : Set (Set X) // IsTopologicalBasis B}, #B.1

theorem topWeight_le {B : Set (Set X)} (hB : IsTopologicalBasis B) : topWeight X ≤ #B :=
  ciInf_le' (fun B : {B : Set (Set X) // IsTopologicalBasis B} => #B.1) ⟨B, hB⟩

theorem le_topWeight {c : Cardinal.{u}} (h : ∀ B : Set (Set X), IsTopologicalBasis B → c ≤ #B) :
    c ≤ topWeight X := by
  have : Nonempty {B : Set (Set X) // IsTopologicalBasis B} := ⟨⟨_, isTopologicalBasis_opens⟩⟩
  exact le_ciInf fun B => h B.1 B.2

/-- The weight of a space is at most that of a space it embeds in. -/
theorem topWeight_le_of_isInducing {Y : Type u} [TopologicalSpace Y] {f : X → Y}
    (hf : IsInducing f) : topWeight X ≤ topWeight Y := by
  refine le_topWeight fun B hB => ?_
  exact (topWeight_le (hf.isTopologicalBasis hB)).trans mk_image_le

/-- A power `T^ι` of the circle with `ι` infinite has weight at most `|ι|`. -/
theorem topWeight_pi_circle_le (ι : Type u) [Infinite ι] : topWeight (ι → Circle) ≤ #ι := by
  classical
  obtain ⟨B₀, hB₀c, -, hB₀⟩ := exists_countable_basis Circle
  have hne : B₀.Nonempty := by
    obtain ⟨s, hs, -⟩ := hB₀.exists_subset_of_mem_open (mem_univ (1 : Circle)) isOpen_univ
    exact ⟨s, hs⟩
  let U : Finset (ι × B₀) → Set (ι → Circle) := fun S => {x | ∀ p ∈ S, x p.1 ∈ (p.2 : Set Circle)}
  have hU : IsTopologicalBasis (range U) := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨S, rfl⟩
      have : U S = ⋂ p ∈ S, (fun x : ι → Circle => x p.1) ⁻¹' (p.2 : Set Circle) := by
        ext x
        simp [U]
      rw [this]
      exact isOpen_biInter_finset fun p _ => (hB₀.isOpen p.2.2).preimage (continuous_apply p.1)
    · intro x O hxO hO
      obtain ⟨I, u, hu, hIO⟩ := isOpen_pi_iff.1 hO x hxO
      have hb : ∀ a, a ∈ I → ∃ b ∈ B₀, x a ∈ b ∧ b ⊆ u a := fun a ha =>
        hB₀.exists_subset_of_mem_open (hu a ha).2 (hu a ha).1
      choose! b hb using hb
      let S : Finset (ι × B₀) := I.attach.image fun a => (a.1, ⟨b a.1, (hb a.1 a.2).1⟩)
      refine ⟨U S, ⟨S, rfl⟩, ?_, ?_⟩
      · intro p hp
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
        exact (hb a.1 a.2).2.1
      · intro y hy
        apply hIO
        intro a ha
        have hp : (a, (⟨b a, (hb a ha).1⟩ : B₀)) ∈ S :=
          Finset.mem_image.2 ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩
        exact (hb a ha).2.2 (hy _ hp)
  refine (topWeight_le hU).trans ?_
  refine mk_range_le.trans ?_
  have : Countable B₀ := hB₀c.to_subtype
  obtain ⟨b0, hb0⟩ := hne
  have : Infinite (ι × B₀) :=
    Infinite.of_injective (fun i => (i, (⟨b0, hb0⟩ : B₀))) fun _ _ h => congrArg Prod.fst h
  rw [mk_finset_of_infinite]
  -- `B₀` injects into `ℕ`, hence into `ι`
  obtain ⟨e, he⟩ := Countable.exists_injective_nat B₀
  let j : ι × B₀ → ι × ι := fun p => (p.1, Infinite.natEmbedding ι (e p.2))
  have hj : Function.Injective j := by
    intro p q h
    simp only [j, Prod.mk.injEq] at h
    exact Prod.ext h.1 (he ((Infinite.natEmbedding ι).injective h.2))
  refine (mk_le_of_injective hj).trans ?_
  rw [mk_prod, lift_id, mul_eq_self (aleph0_le_mk ι)]

/-- A finite Hausdorff space has weight equal to its cardinality (it is discrete, and every basis
contains all singletons). -/
theorem topWeight_eq_mk_of_finite [Finite X] [T2Space X] : topWeight X = #X := by
  classical
  apply le_antisymm
  · have hB := isTopologicalBasis_singletons X
    refine (topWeight_le hB).trans ?_
    have : {s : Set X | ∃ x, s = {x}} = range fun x : X => ({x} : Set X) := by
      ext s
      simp [eq_comm]
    rw [this]
    exact mk_range_le
  · refine le_topWeight fun B hB => ?_
    have h : ∀ x : X, ∃ s ∈ B, x ∈ s ∧ s ⊆ {x} := fun x =>
      hB.exists_subset_of_mem_open (mem_singleton x) (isOpen_discrete _)
    choose f hfB hxf hfx using h
    refine mk_le_of_injective (f := fun x => (⟨f x, hfB x⟩ : B)) fun x y hxy => ?_
    have : f x = f y := congrArg Subtype.val hxy
    have hx := hxf x
    rw [this] at hx
    exact hfx y hx

end Weight

/-- A finite abelian group has at most as many characters as elements (Dedekind: the characters
are linearly independent functions `G → ℂ`). -/
theorem card_dual_le_of_finite {G : Type u} [CommGroup G] [TopologicalSpace G] [Finite G] :
    #(PontryaginDual G) ≤ #G := by
  classical
  have := Fintype.ofFinite G
  let φ : PontryaginDual G → (G →* ℂ) := fun χ => Circle.coeHom.comp (χ : G →* Circle)
  have hφ : Function.Injective φ := by
    intro χ ψ h
    ext g
    exact DFunLike.congr_fun h g
  have hli := (linearIndependent_monoidHom G ℂ).comp φ hφ
  have := hli.cardinalMk_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at this
  rwa [Cardinal.mk_fintype G]

section Compact

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G]

/-- The distance of `a b⁻¹` from `1` on the circle is the distance from `a` to `b`. -/
theorem circle_dist_mul_inv_one (a b : Circle) : dist (a * b⁻¹) 1 = dist a b := by
  change dist (((a * b⁻¹ : Circle)) : ℂ) ((1 : Circle) : ℂ) = dist (a : ℂ) (b : ℂ)
  rw [Complex.dist_eq, Complex.dist_eq, Circle.coe_mul, Circle.coe_inv, Circle.coe_one]
  have hb : (b : ℂ) ≠ 0 := Circle.coe_ne_zero b
  have : (a : ℂ) * (b : ℂ)⁻¹ - 1 = ((a : ℂ) - b) * (b : ℂ)⁻¹ := by field_simp
  rw [this, norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one]

/-- The triangle inequality for products on the circle. -/
theorem circle_dist_mul_mul_le (a b c d : Circle) : dist (a * b) (c * d) ≤ dist a c + dist b d := by
  have h1 : dist (a * b) (c * d) = dist ((a * c⁻¹) * (b * d⁻¹)) 1 := by
    rw [circle_dist_mul_inv_one (a * b) (c * d) |>.symm, mul_inv]
    congr 1
    ac_rfl
  have h2 : dist ((a * c⁻¹) * (b * d⁻¹)) (a * c⁻¹) = dist (b * d⁻¹) 1 := by
    rw [← circle_dist_mul_inv_one ((a * c⁻¹) * (b * d⁻¹)) (a * c⁻¹), mul_inv_cancel_comm]
  rw [h1, ← circle_dist_mul_inv_one a c, ← circle_dist_mul_inv_one b d]
  calc dist ((a * c⁻¹) * (b * d⁻¹)) 1
      ≤ dist ((a * c⁻¹) * (b * d⁻¹)) (a * c⁻¹) + dist (a * c⁻¹) 1 := dist_triangle _ _ _
    _ = dist (a * c⁻¹) 1 + dist (b * d⁻¹) 1 := by rw [h2, add_comm]

/-- A character whose values lie in a set containing no nontrivial subgroup of the circle is
trivial. -/
theorem char_eq_one_of_mem {O : Set Circle}
    (hO : ∀ H : Subgroup Circle, (H : Set Circle) ⊆ O → H = ⊥) (χ : PontryaginDual G)
    (h : ∀ g, χ g ∈ O) : χ = 1 := by
  have hr : MonoidHom.range (χ : G →* Circle) = ⊥ := hO _ (by rintro _ ⟨g, rfl⟩; exact h g)
  ext g
  have : χ g ∈ MonoidHom.range (χ : G →* Circle) := ⟨g, rfl⟩
  rw [hr, Subgroup.mem_bot] at this
  rw [this]
  rfl

/-- For a fixed open neighbourhood `W` of `1`, only finitely many characters map `W` into the
`ε`-ball about `1`, when the `4ε`-ball contains no nontrivial subgroup. -/
theorem finite_smallChars {O : Set Circle}
    (hO : ∀ H : Subgroup Circle, (H : Set Circle) ⊆ O → H = ⊥) {ε : ℝ} (hε : 0 < ε)
    (hball : ball (1 : Circle) (4 * ε) ⊆ O) {W : Set G} (hW : IsOpen W) (hW1 : (1 : G) ∈ W) :
    {χ : PontryaginDual G | ∀ w ∈ W, dist (χ w) 1 < ε}.Finite := by
  classical
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates (K := (univ : Set G)) (V := W)
    isCompact_univ (by rw [hW.interior_eq]; exact ⟨1, hW1⟩)
  obtain ⟨N, -, hNf, hN⟩ := finite_cover_balls_of_compact (isCompact_univ : IsCompact (univ : Set Circle)) hε
  have hc : ∀ (χ : PontryaginDual G) (g : t), ∃ c : N, dist (χ (g : G)⁻¹) c < ε := fun χ g => by
    obtain ⟨c, hc, hd⟩ := mem_iUnion₂.1 (hN (mem_univ (χ (g : G)⁻¹)))
    exact ⟨⟨c, hc⟩, hd⟩
  choose p hp using hc
  have : Finite N := hNf.to_subtype
  refine Set.Finite.of_finite_image (f := p) (Set.toFinite _) ?_
  intro χ hχ ψ hψ hpq
  have hclose : ∀ g : t, dist (χ (g : G)⁻¹) (ψ (g : G)⁻¹) < 2 * ε := fun g => by
    have h1 := hp χ g
    have h2 := hp ψ g
    rw [show p χ g = p ψ g from congrFun hpq g] at h1
    calc dist (χ (g : G)⁻¹) (ψ (g : G)⁻¹)
        ≤ dist (χ (g : G)⁻¹) (p ψ g) + dist ((p ψ g : Circle)) (ψ (g : G)⁻¹) := dist_triangle _ _ _
      _ < ε + ε := add_lt_add h1 (by rw [dist_comm]; exact h2)
      _ = 2 * ε := by ring
  have hdiv : χ * ψ⁻¹ = 1 := char_eq_one_of_mem hO _ fun h => by
    obtain ⟨g, hg, hgh⟩ := mem_iUnion₂.1 (ht (mem_univ h))
    have hgh' : g * h ∈ W := hgh
    obtain ⟨w, hwdef⟩ : ∃ w, w = g * h := ⟨_, rfl⟩
    rw [← hwdef] at hgh'
    have hh : h = g⁻¹ * w := by rw [hwdef, inv_mul_cancel_left]
    apply hball
    rw [mem_ball]
    have happ : (χ * ψ⁻¹) h = χ h * (ψ h)⁻¹ := rfl
    rw [happ, circle_dist_mul_inv_one, hh, map_mul, map_mul]
    have hw1 := hχ _ hgh'
    have hw2 := hψ _ hgh'
    have hw : dist (χ w) (ψ w) < 2 * ε := by
      calc dist (χ w) (ψ w) ≤ dist (χ w) 1 + dist 1 (ψ w) :=
            dist_triangle _ _ _
        _ < ε + ε := add_lt_add hw1 (by rw [dist_comm]; exact hw2)
        _ = 2 * ε := by ring
    calc dist (χ g⁻¹ * χ w) (ψ g⁻¹ * ψ w)
        ≤ dist (χ g⁻¹) (ψ g⁻¹) + dist (χ w) (ψ w) := circle_dist_mul_mul_le _ _ _ _
      _ < 2 * ε + 2 * ε := add_lt_add (hclose ⟨g, hg⟩) hw
      _ = 4 * ε := by ring
  exact mul_inv_eq_one.1 hdiv

/-- An infinite compact Hausdorff abelian group has an infinite dual group. -/
theorem infinite_dual_of_infinite [Infinite G] : Infinite (PontryaginDual G) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  set N := Nat.card (PontryaginDual G) with hNdef
  have hN : 0 < N := Nat.card_pos
  let R : Set ℂ := {z | z ^ N = 1}
  have hR : R.Finite := by
    refine (Polynomial.nthRoots N (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => ?_
    have hz' : z ^ N = 1 := hz
    simp [Polynomial.mem_nthRoots hN, hz']
  have : Finite R := hR.to_subtype
  have hpow : ∀ (χ : PontryaginDual G) (g : G) (n : ℕ), (χ ^ n) g = (χ g) ^ n := by
    intro χ g n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl
  have hval : ∀ (χ : PontryaginDual G) (g : G), ((χ g : Circle) : ℂ) ^ N = 1 := by
    intro χ g
    rw [← Circle.coe_pow, ← hpow, pow_card_eq_one']
    rfl
  let f : G → (PontryaginDual G → R) := fun g χ => ⟨(χ g : ℂ), hval χ g⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_contra hne
    obtain ⟨χ, hχ⟩ := characters_separate_points_of_compact hne
    apply hχ
    have := congrArg Subtype.val (congrFun hxy χ)
    exact Circle.coe_inj.1 this
  have : Finite G := Finite.of_injective f hf
  exact not_finite G

/-- `|Ĝ| ≤ |B|` for every basis `B` of an infinite compact Hausdorff abelian group `G`. -/
theorem card_dual_le_of_isTopologicalBasis [Infinite G] {B : Set (Set G)}
    (hB : IsTopologicalBasis B) : #(PontryaginDual G) ≤ #B := by
  classical
  -- `B` is infinite: the complements of points are distinct open sets
  have hBinf : Infinite B := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have hinj : Function.Injective (fun x : G => {s : B | (s : Set G) ⊆ {x}ᶜ}) := by
      intro x y hxy
      have hxy : {s : B | (s : Set G) ⊆ {x}ᶜ} = {s : B | (s : Set G) ⊆ {y}ᶜ} := hxy
      have hx := hB.open_eq_sUnion' (isOpen_compl_singleton (x := x))
      have hy := hB.open_eq_sUnion' (isOpen_compl_singleton (x := y))
      have hxy' : ({x}ᶜ : Set G) = {y}ᶜ := by
        rw [hx, hy]
        congr 1
        ext s
        constructor
        · rintro ⟨hs, hsx⟩
          have : (⟨s, hs⟩ : B) ∈ {s : B | (s : Set G) ⊆ {x}ᶜ} := hsx
          rw [hxy] at this
          exact ⟨hs, this⟩
        · rintro ⟨hs, hsy⟩
          have : (⟨s, hs⟩ : B) ∈ {s : B | (s : Set G) ⊆ {y}ᶜ} := hsy
          rw [← hxy] at this
          exact ⟨hs, this⟩
      rw [compl_inj_iff, Set.singleton_eq_singleton_iff] at hxy'
      exact hxy'
    have : Finite G := Finite.of_injective _ hinj
    exact not_finite G
  obtain ⟨O, hOo, hO1, hO⟩ := isNSS_circle
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hOo 1 hO1
  have hε : 0 < δ / 4 := by positivity
  have hball' : ball (1 : Circle) (4 * (δ / 4)) ⊆ O := by
    rw [show 4 * (δ / 4) = δ by ring]
    exact hball
  let ι := {W : B // (1 : G) ∈ (W : Set G)}
  let S : ι → Set (PontryaginDual G) := fun W => {χ | ∀ w ∈ ((W : B) : Set G), dist (χ w) 1 < δ / 4}
  have hcov : (univ : Set (PontryaginDual G)) ⊆ ⋃ W, S W := by
    intro χ _
    have hc : Continuous fun g : G => χ g := χ.continuous
    have hmem : (fun g : G => χ g) ⁻¹' ball 1 (δ / 4) ∈ 𝓝 (1 : G) :=
      hc.continuousAt.preimage_mem_nhds (by
        show ball 1 (δ / 4) ∈ 𝓝 (χ 1)
        rw [map_one χ]
        exact ball_mem_nhds _ hε)
    obtain ⟨W, hWB, hW1, hWsub⟩ := hB.mem_nhds_iff.1 hmem
    exact mem_iUnion.2 ⟨⟨⟨W, hWB⟩, hW1⟩, fun w hw => hWsub hw⟩
  have hSfin : ∀ W, (S W).Finite := fun W =>
    finite_smallChars hO hε hball' (hB.isOpen (W : B).2) W.2
  calc #(PontryaginDual G) = #(univ : Set (PontryaginDual G)) := mk_univ.symm
    _ ≤ #(⋃ W, S W) := mk_le_mk_of_subset hcov
    _ ≤ #ι * ⨆ W, #(S W) := mk_iUnion_le _
    _ ≤ #B * ℵ₀ := by
        refine mul_le_mul' (mk_subtype_le _) (ciSup_le' fun W => ?_)
        have : Countable (S W) := (hSfin W).countable.to_subtype
        exact mk_le_aleph0
    _ ≤ #B * #B := mul_le_mul' le_rfl (aleph0_le_mk B)
    _ = #B := mul_eq_self (aleph0_le_mk B)

/-- The weight of an infinite compact Hausdorff abelian group equals the cardinality of its dual. -/
theorem topWeight_eq_card_dual_of_infinite [Infinite G] : topWeight G = #(PontryaginDual G) := by
  have := infinite_dual_of_infinite (G := G)
  apply le_antisymm
  · calc topWeight G ≤ topWeight (PontryaginDual G → Circle) :=
          topWeight_le_of_isInducing (isClosedEmbedding_evalChars' (K := G)).isInducing
      _ ≤ #(PontryaginDual G) := topWeight_pi_circle_le _
  · exact le_topWeight fun B hB => card_dual_le_of_isTopologicalBasis hB

/-- Morris, Topology Without Tears, Proposition A5.0.18 (i) (TP-491). The weight of a compact
Hausdorff abelian group `G` (the least cardinality of a basis of its topology) equals the
cardinality of its dual group `Ĝ`. -/
@[kb "morris2024" "Proposition A5.0.18, p. 504"]
theorem topWeight_eq_card_dual : topWeight G = #(PontryaginDual G) := by
  rcases finite_or_infinite G with hG | hG
  · have h1 : #(PontryaginDual G) ≤ #G := card_dual_le_of_finite
    have : Finite (PontryaginDual G) :=
      Cardinal.mk_lt_aleph0_iff.1 (h1.trans_lt (Cardinal.mk_lt_aleph0))
    have h2 : #G ≤ #(PontryaginDual (PontryaginDual G)) :=
      mk_le_of_injective (toDualDual_injective_compact (K := G))
    have h3 : #(PontryaginDual (PontryaginDual G)) ≤ #(PontryaginDual G) := card_dual_le_of_finite
    rw [topWeight_eq_mk_of_finite]
    exact le_antisymm (h2.trans h3) h1
  · exact topWeight_eq_card_dual_of_infinite

end Compact

end UndergradKB.Topology
