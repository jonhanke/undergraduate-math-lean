import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Permutations

/-! # Judson–Beezer, chapter 14: group actions (course layer)

Thin wrappers in the book's terms around Mathlib for orbits and stabilizers, the class equation,
`p`-groups and Burnside's counting theorem. -/

namespace UndergradKB.AbstractAlgebra.Course

section Actions

variable {G X : Type*} [Group G] [MulAction G X]

/-- AA-209. `G` acts on the left cosets `G/H` by `g · xH = gxH`, and this action is transitive. -/
@[kb "judson2026" "Example 14.1.5, p. 187"]
theorem judson_14_1_5 (H : Subgroup G) :
    (∀ g x : G, g • (x : G ⧸ H) = ((g * x : G) : G ⧸ H)) ∧ MulAction.IsPretransitive G (G ⧸ H) :=
  ⟨fun _ _ => rfl, inferInstance⟩

/-- AA-210. `G`-equivalence (`g x = y` for some `g`) is an equivalence relation on a `G`-set. -/
@[kb "judson2026" "Proposition 14.1.6, p. 187"]
theorem judson_14_1_6 : Equivalence (fun x y : X => ∃ g : G, g • x = y) :=
  ⟨fun x => ⟨1, one_smul G x⟩,
    fun ⟨g, h⟩ => ⟨g⁻¹, by rw [← h, inv_smul_smul]⟩,
    fun ⟨g, h⟩ ⟨g', h'⟩ => ⟨g' * g, by rw [mul_smul, h, h']⟩⟩

/-- AA-213. The stabilizer of a point `x` is a subgroup of `G`. -/
@[kb "judson2026" "Proposition 14.1.10, p. 188"]
theorem judson_14_1_10 (x : X) : ∃ K : Subgroup G, ∀ g : G, g ∈ K ↔ g • x = x :=
  ⟨MulAction.stabilizer G x, fun _ => MulAction.mem_stabilizer_iff⟩

/-- AA-214. Orbit-stabilizer: the orbit of `x` has `[G : G_x]` elements; for finite `G`,
`|orbit| · |G_x| = |G|`. -/
@[kb "judson2026" "Theorem 14.1.11, p. 188"]
theorem judson_14_1_11 (x : X) :
    Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index ∧
    (Finite G → Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
      Nat.card G) := by
  have h : Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
    rw [MulAction.index_stabilizer,Nat.card_coe_set_eq]
  exact ⟨h, fun _ => h ▸ Subgroup.index_mul_card _⟩

/-- AA-215. Points in the same orbit have conjugate (hence isomorphic, equinumerous)
stabilizers: `G_{gx} = g G_x g⁻¹`. -/
@[kb "judson2026" "Lemma 14.3.2, p. 191"]
theorem judson_14_3_2 (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = (MulAction.stabilizer G x).map (MulAut.conj g).toMonoidHom ∧
    Nonempty (MulAction.stabilizer G (g • x) ≃* MulAction.stabilizer G x) := by
  refine ⟨MulAction.stabilizer_smul_eq_stabilizer_map_conj g x, ?_⟩
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj g x]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).symm⟩

end Actions

/-- AA-217. Orbit decomposition: for a finite `G`-set `X`, `|X|` is the sum over the orbits
(represented by `ω.out`) of `[G : G_x]`, i.e. of `|G| / |G_x|`. -/
@[kb "judson2026" "Discussion before Example 14.2.1, p. 188"]
theorem judson_14_2_orbit_decomposition {G X : Type*} [Group G] [MulAction G X] [Fintype G]
    [Fintype X] [Fintype (MulAction.orbitRel.Quotient G X)]
    [∀ b : X, Fintype (MulAction.stabilizer G b)] :
    Fintype.card X = ∑ ω : MulAction.orbitRel.Quotient G X,
      Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out) :=
  MulAction.card_eq_sum_card_group_div_card_stabilizer G X

/-- AA-218. Class equation: for a finite group, `|G| = |Z(G)| + Σ |C|` over the nontrivial
conjugacy classes `C`. -/
@[kb "judson2026" "Class equation, p. 189"]
theorem judson_14_2_class_equation (G : Type*) [Group G] [Finite G] :
    Nat.card (Subgroup.center G) + ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier =
      Nat.card G :=
  Group.nat_card_center_add_sum_card_noncenter_eq_card G

/-- AA-218. Each conjugacy class of a finite group has a size dividing the order of the group. -/
@[kb "judson2026" "Class equation, p. 189"]
theorem judson_14_2_class_size_dvd (G : Type*) [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier ∣ Nat.card G := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ConjClasses.card_carrier]
  exact Nat.div_dvd_of_dvd (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card _)

/-- AA-220. A group of order `pⁿ` (`p` prime, `n ≥ 1`) has a nontrivial center. -/
@[kb "judson2026" "Theorem 14.2.4, p. 190"]
theorem judson_14_2_4 {G : Type*} [Group G] {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (h : Nat.card G = p ^ n) : Nontrivial (Subgroup.center G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ hp.ne_zero)
  have hnt : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial, h]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  exact (IsPGroup.of_card h).center_nontrivial

/-- AA-221. A group of order `p²` is abelian. -/
@[kb "judson2026" "Corollary 14.2.5, p. 190"]
theorem judson_14_2_5 {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (h : Nat.card G = p ^ 2) :
    ∀ a b : G, a * b = b * a := by
  have : Fact p.Prime := ⟨hp⟩
  exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq h).is_comm.comm

/-- AA-222. Burnside's counting theorem: the number of orbits is the average over `g ∈ G` of
the number of points fixed by `g`. -/
@[kb "judson2026" "Theorem 14.3.3, p. 191"]
theorem judson_14_3_3 {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] :
    (Nat.card (MulAction.orbitRel.Quotient G X) : ℚ) =
      (Nat.card G : ℚ)⁻¹ * ∑ g : G, (Nat.card (MulAction.fixedBy X g) : ℚ) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  simp only [Nat.card_eq_fintype_card] at *
  have hG : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [eq_inv_mul_iff_mul_eq₀ hG]
  have hk := congrArg (Nat.cast : ℕ → ℚ) key
  push_cast at hk
  linarith

/-- AA-223. A permutation `σ` of a finite set `X` fixes exactly `|Y| ^ c` colorings `f : X → Y`
(under `f ↦ f ∘ σ`), where `c` is the number of cycles of `σ`, fixed points counted as cycles of
length 1. -/
@[kb "judson2026" "Proposition 14.3.5, p. 193"]
theorem judson_14_3_5 {X Y : Type*} [Fintype X] [DecidableEq X] [Finite Y]
    (σ : Equiv.Perm X) :
    Nat.card {f : X → Y // f ∘ σ = f} =
      Nat.card Y ^ (σ.cycleType.card + (Fintype.card X - σ.support.card)) :=
  card_fixed_colorings σ

end UndergradKB.AbstractAlgebra.Course
