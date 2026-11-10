import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import UndergradKB.Common.Attr

/-! # Judson–Beezer, chapter 3: groups (course layer)

Thin wrappers around Mathlib for modular arithmetic, basic examples and properties of groups, and
subgroup tests. -/

namespace UndergradKB.AbstractAlgebra.Course

/-- AA-024. Arithmetic in `ℤ_n` (`ZMod n`): addition and multiplication are commutative and
associative, `0` and `1` are identities, every element has an additive inverse, and multiplication
distributes over addition. -/
@[kb "judson2026" "Proposition 3.1.4, p. 42"]
theorem judson_3_1_4 (n : ℕ) (a b c : ZMod n) :
    (a + b = b + a ∧ a * b = b * a) ∧
    ((a + b) + c = a + (b + c) ∧ (a * b) * c = a * (b * c)) ∧
    (a + 0 = a ∧ a * 1 = a) ∧ (∃ d : ZMod n, a + d = 0) ∧
    a * (b + c) = a * b + a * c :=
  ⟨⟨add_comm a b, mul_comm a b⟩, ⟨add_assoc a b c, mul_assoc a b c⟩, ⟨add_zero a, mul_one a⟩,
    ⟨-a, add_neg_cancel a⟩, mul_add a b c⟩

/-- AA-025. A residue `m` mod `n` has a multiplicative inverse exactly when `gcd(m, n) = 1`. -/
@[kb "judson2026" "Proposition 3.1.4, p. 42"]
theorem judson_3_1_4_inverse (m n : ℕ) :
    (∃ b : ZMod n, (m : ZMod n) * b = 1) ↔ Nat.gcd m n = 1 := by
  rw [← isUnit_iff_exists_inv]
  exact ZMod.isUnit_iff_coprime m n

/-- AA-029. The classes of `ℤ_n` that are units (the elements of `U(n)`) are those coprime to `n`. -/
@[kb "judson2026" "Example 3.2.4, p. 46"]
theorem judson_3_2_4 (m n : ℕ) : IsUnit (m : ZMod n) ↔ Nat.Coprime m n :=
  ZMod.isUnit_iff_coprime m n

/-- AA-030. The symmetries of the triangle, the dihedral group `D₃`, form a nonabelian group of
order 6. -/
@[kb "judson2026" "Example 3.2.6, p. 47"]
theorem judson_3_2_6 :
    Nat.card (DihedralGroup 3) = 6 ∧ ∃ a b : DihedralGroup 3, a * b ≠ b * a := by
  refine ⟨?_, DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

/-- AA-030. The symmetric group `S₃` has order 6 and is nonabelian. -/
@[kb "judson2026" "Example 3.2.6, p. 47"]
theorem judson_3_2_6_perm :
    Nat.card (Equiv.Perm (Fin 3)) = 6 ∧ ∃ a b : Equiv.Perm (Fin 3), a * b ≠ b * a := by
  refine ⟨?_, Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

/-- AA-031. The invertible real `2 × 2` matrices `GL₂(ℝ)` contain the determinant-one matrices as a
subgroup. -/
@[kb "judson2026" "Example 3.3.3, p. 50"]
theorem judson_3_3_3 :
    ∃ H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ),
      ∀ g, g ∈ H ↔ (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  refine ⟨(Matrix.GeneralLinearGroup.det).ker, fun g => ?_⟩
  rw [MonoidHom.mem_ker, Units.ext_iff]
  simp

/-- AA-032. The quaternion group `Q₈` has order 8 and is nonabelian. -/
@[kb "judson2026" "Example 3.2.8, p. 48"]
theorem judson_3_2_8 :
    Nat.card (QuaternionGroup 2) = 8 ∧ ∃ a b : QuaternionGroup 2, a * b ≠ b * a := by
  refine ⟨?_, QuaternionGroup.a 1, QuaternionGroup.xa 0, by decide⟩
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- AA-033. The nonzero elements of a field (for instance `ℝ` or `ℂ`) are exactly its units, which
form a group under multiplication. -/
@[kb "judson2026" "Example 3.2.9, p. 48"]
theorem judson_3_2_9 {F : Type*} [Field F] (x : F) : IsUnit x ↔ x ≠ 0 :=
  isUnit_iff_ne_zero

/-- AA-035. The direct product of groups has the coordinatewise operation. -/
@[kb "judson2026" "Example 3.3.5, p. 51"]
theorem judson_3_3_5 {G H : Type*} [Group G] [Group H] (g₁ g₂ : G) (h₁ h₂ : H) :
    ((g₁, h₁) : G × H) * (g₂, h₂) = (g₁ * g₂, h₁ * h₂) :=
  rfl

section Basic

variable {G : Type*} [Group G]

/-- AA-036. The identity of a group is unique. -/
@[kb "judson2026" "Proposition 3.2.10, p. 48"]
theorem judson_3_2_10 (e e' : G) (he : ∀ g : G, e * g = g ∧ g * e = g)
    (he' : ∀ g : G, e' * g = g ∧ g * e' = g) : e = e' :=
  calc e = e' * e := ((he' e).1).symm
    _ = e' := (he e').2

/-- AA-037. Inverses in a group are unique. -/
@[kb "judson2026" "Proposition 3.2.11, p. 48"]
theorem judson_3_2_11 (g b b' : G) (h : g * b = 1 ∧ b * g = 1) (h' : g * b' = 1 ∧ b' * g = 1) :
    b = b' := by
  rw [← inv_eq_of_mul_eq_one_right h.1, ← inv_eq_of_mul_eq_one_right h'.1]

/-- AA-038. The inverse of a product is the product of inverses in reverse order. -/
@[kb "judson2026" "Proposition 3.2.12, p. 48"]
theorem judson_3_2_12 (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  mul_inv_rev a b

/-- AA-039. The inverse of the inverse of `a` is `a`. -/
@[kb "judson2026" "Proposition 3.2.13, p. 48"]
theorem judson_3_2_13 (a : G) : (a⁻¹)⁻¹ = a :=
  inv_inv a

/-- AA-040. In a group the equations `a x = b` and `x a = b` each have a unique solution. -/
@[kb "judson2026" "Proposition 3.2.14, p. 49"]
theorem judson_3_2_14 (a b : G) : (∃! x : G, a * x = b) ∧ (∃! x : G, x * a = b) :=
  ⟨⟨a⁻¹ * b, by simp, fun y hy => by rw [← hy]; simp⟩,
    ⟨b * a⁻¹, by simp, fun y hy => by rw [← hy]; simp⟩⟩

/-- AA-041. Left and right cancellation hold in a group. -/
@[kb "judson2026" "Proposition 3.2.15, p. 49"]
theorem judson_3_2_15 (a b c : G) : (b * a = c * a → b = c) ∧ (a * b = a * c → b = c) :=
  ⟨fun h => mul_right_cancel h, fun h => mul_left_cancel h⟩

/-- AA-042. Laws of exponents: `g^m g^n = g^(m+n)`, `(g^m)^n = g^(mn)`, and
`(gh)^n = (h⁻¹ g⁻¹)^(-n)`, which is `g^n h^n` when the group is abelian. -/
@[kb "judson2026" "Theorem 3.2.16, p. 49"]
theorem judson_3_2_16 (g h : G) (m n : ℤ) :
    g ^ m * g ^ n = g ^ (m + n) ∧ (g ^ m) ^ n = g ^ (m * n) ∧
    (g * h) ^ n = (h⁻¹ * g⁻¹) ^ (-n) ∧ (Commute g h → (g * h) ^ n = g ^ n * h ^ n) :=
  ⟨(zpow_add g m n).symm, (zpow_mul g m n).symm,
    by rw [← mul_inv_rev, inv_zpow', neg_neg], fun hc => hc.mul_zpow n⟩

/-- AA-044. A subset of a group is a subgroup iff it contains the identity and is closed under
products and inverses. -/
@[kb "judson2026" "Proposition 3.3.7, p. 51"]
theorem judson_3_3_7 (S : Set G) :
    (∃ H : Subgroup G, (H : Set G) = S) ↔
      (1 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ ∀ a ∈ S, a⁻¹ ∈ S) := by
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨H.one_mem, fun a ha b hb => H.mul_mem ha hb, fun a ha => H.inv_mem ha⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := h1, inv_mem' := ?_ }, rfl⟩
    · exact fun {a b} ha hb => h2 a ha b hb
    · exact fun {a} ha => h3 a ha

/-- AA-045. A subset of a group is a subgroup iff it is nonempty and `g h⁻¹` lies in it whenever
`g` and `h` do. -/
@[kb "judson2026" "Proposition 3.3.8, p. 52"]
theorem judson_3_3_8 (S : Set G) :
    (∃ H : Subgroup G, (H : Set G) = S) ↔
      (S.Nonempty ∧ ∀ g ∈ S, ∀ h ∈ S, g * h⁻¹ ∈ S) := by
  constructor
  · rintro ⟨H, rfl⟩
    exact ⟨⟨1, H.one_mem⟩, fun g hg h hh => H.mul_mem hg (H.inv_mem hh)⟩
  · rintro ⟨hne, h⟩
    exact ⟨Subgroup.ofDiv S hne h, rfl⟩

/-- AA-046. The center of a group consists of the elements commuting with every element. -/
@[kb "judson2026" "Exercise 3.5.48, p. 56"]
theorem judson_3_5_48 (g : G) : g ∈ Subgroup.center G ↔ ∀ h : G, h * g = g * h :=
  Subgroup.mem_center_iff

/-- AA-047. The centralizer of a subgroup `H` consists of the elements commuting with every
element of `H`. -/
@[kb "judson2026" "Exercise 3.5.53, p. 56"]
theorem judson_3_5_53 (H : Subgroup G) (g : G) :
    g ∈ Subgroup.centralizer (H : Set G) ↔ ∀ h ∈ H, h * g = g * h :=
  Subgroup.mem_centralizer_iff

end Basic

end UndergradKB.AbstractAlgebra.Course
