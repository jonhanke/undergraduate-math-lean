import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Commutator.Basic
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.FiniteGroups

/-! # Judson–Beezer, chapter 15: the Sylow theorems (course layer)

Thin wrappers in the book's terms around Mathlib for Cauchy's theorem, the three Sylow theorems
and some of their applications. -/

namespace UndergradKB.AbstractAlgebra.Course

open scoped Pointwise

/-- AA-195. Cauchy's theorem: a finite group has an element of order `p` for every prime `p`
dividing its order. -/
@[kb "judson2026" "Theorem 15.1.1, p. 200"]
theorem judson_15_1_1 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact exists_prime_orderOf_dvd_card' p h

/-- AA-196. A finite group is a `p`-group iff its order is a power of `p`. -/
@[kb "judson2026" "Corollary 15.1.2, p. 201"]
theorem judson_15_1_2 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.iff_card

/-- AA-227. First Sylow theorem: if `pʳ` divides `|G|` then `G` has a subgroup of order `pʳ`. -/
@[kb "judson2026" "Theorem 15.1.4, p. 201"]
theorem judson_15_1_4 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (r : ℕ)
    (h : p ^ r ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ^ r := by
  have : Fact p.Prime := ⟨hp⟩
  exact Sylow.exists_subgroup_card_pow_prime p h

/-- AA-228. If an element `x` of `p`-power order normalizes a Sylow `p`-subgroup `P`, then
`x ∈ P`. -/
@[kb "judson2026" "Lemma 15.1.5, p. 202"]
theorem judson_15_1_5 {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (x : G) (n : ℕ)
    (hx : x ^ (p ^ n) = 1) (hN : x ∈ Subgroup.normalizer P) : x ∈ P := by
  have hZ : IsPGroup p (Subgroup.zpowers x) := by
    intro g
    obtain ⟨g, m, rfl⟩ := g
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have h := hZ.inf_normalizer_sylow P
  have hmem : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer P :=
    ⟨Subgroup.mem_zpowers x, hN⟩
  rw [h] at hmem
  exact hmem.2

/-- AA-230. Second Sylow theorem: any two Sylow `p`-subgroups of a finite group are
conjugate. -/
@[kb "judson2026" "Theorem 15.1.7, p. 202"]
theorem judson_15_1_7 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (P Q : Sylow p G) :
    ∃ g : G, (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨g, by rw [← hg, Sylow.coe_subgroup_smul]; rfl⟩

/-- AA-231. Third Sylow theorem: the number of Sylow `p`-subgroups of a finite group is
congruent to `1` modulo `p` and divides `|G|`. -/
@[kb "judson2026" "Theorem 15.1.8, p. 202"]
theorem judson_15_1_8 {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    Nat.card (Sylow p G) ≡ 1 [MOD p] ∧ Nat.card (Sylow p G) ∣ Nat.card G := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨card_sylow_modEq_one p G, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  exact (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)

/-- AA-207. The commutator subgroup `G'` is normal in `G`, and `G/G'` is abelian. -/
@[kb "judson2026" "Theorem 15.2.5, p. 204"]
theorem judson_15_2_5 (G : Type*) [Group G] :
    (commutator G).Normal ∧ ∀ a b : Abelianization G, a * b = b * a :=
  ⟨inferInstance, fun a b => mul_comm a b⟩

/-- AA-233. A group of order `pⁿ` with `n > 1` (`p` prime) is not simple. -/
@[kb "judson2026" "Example 15.2.8, p. 204"]
theorem judson_15_2_8 {G : Type*} [Group G] {p n : ℕ} (hp : p.Prime) (hn : 1 < n)
    (h : Nat.card G = p ^ n) : ¬ IsSimpleGroup G := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [h]; exact pow_ne_zero _ hp.ne_zero)
  intro hs
  have h1 := ((IsPGroup.of_card h).isSimpleGroup_iff_card_eq).mp hs
  rw [h] at h1
  have : p ^ n = p ^ 1 := by rw [pow_one]; exact h1
  exact absurd (Nat.pow_right_injective hp.two_le this) (by omega)

/-- AA-229. The number of `H`-conjugates `h K h⁻¹` (`h ∈ H`) of a subgroup `K` is the index
`[H : N(K) ∩ H]`. -/
@[kb "judson2026" "Lemma 15.1.6, p. 202"]
theorem judson_15_1_6 {G : Type*} [Group G] (H K : Subgroup G) :
    {L : Subgroup G | ∃ h ∈ H, MulAut.conj h • K = L}.ncard
      = (Subgroup.normalizer (K : Set G) ⊓ H).relIndex H :=
  card_conjugates H K

/-- AA-232. If `p < q` are primes, every group of order `p q` has a normal subgroup of order `q`
(so it is not simple). -/
@[kb "judson2026" "Theorem 15.2.2, p. 203"]
theorem judson_15_2_2 {G : Type*} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hG : Nat.card G = p * q) : ∃ N : Subgroup G, N.Normal ∧ Nat.card N = q := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  exact exists_normal_subgroup_card_of_card_eq_mul_primes hpq hG

/-- AA-232. If `p < q` are primes, `|G| = p q` and `q ≢ 1 (mod p)`, then `G` is cyclic. -/
@[kb "judson2026" "Theorem 15.2.2 (cyclic case), p. 203"]
theorem judson_15_2_2_cyclic {G : Type*} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hG : Nat.card G = p * q) (h : ¬ Nat.ModEq p q 1) :
    IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  exact isCyclic_of_card_eq_mul_primes hpq hG h

/-- AA-234. For subgroups `H`, `K`: `|H K| · |H ∩ K| = |H| · |K|`, i.e.
`|H K| = |H||K| / |H ∩ K|`, with `H K` the product set. -/
@[kb "judson2026" "Lemma 15.2.10, p. 205"]
theorem judson_15_2_10 {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G)) * Nat.card (H ⊓ K : Subgroup G) =
      Nat.card H * Nat.card K := by
  classical
  exact card_mul_set_mul_card_inf H K

end UndergradKB.AbstractAlgebra.Course
