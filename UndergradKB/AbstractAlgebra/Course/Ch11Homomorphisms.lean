import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.DirectProducts

/-! # Judson–Beezer, chapter 11: homomorphisms and the isomorphism theorems (course layer)

Thin wrappers in the book's terms around Mathlib for homomorphisms, kernels, the canonical
homomorphism and the first, second and third isomorphism theorems. -/

open scoped Pointwise

namespace UndergradKB.AbstractAlgebra.Course

/-- AA-154. For `g ∈ G` the map `n ↦ gⁿ` is a homomorphism `ℤ → G` whose image is `⟨g⟩`. -/
@[kb "judson2026" "Example 11.1.1, p. 151"]
theorem judson_11_1_1 {G : Type*} [Group G] (g : G) :
    (zpowersHom G g).range = Subgroup.zpowers g :=
  rfl

/-- AA-156. The determinant is a homomorphism `GLₙ → units`, and its kernel is exactly the image
of `SLₙ`. -/
@[kb "judson2026" "Example 11.1.2, p. 151"]
theorem judson_11_1_2 (n : ℕ) (R : Type*) [CommRing R] :
    (∀ A B : Matrix.GeneralLinearGroup (Fin n) R,
      Matrix.GeneralLinearGroup.det (A * B) =
        Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det B) ∧
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) R →*
        Matrix.GeneralLinearGroup (Fin n) R).range =
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin n) R →* Rˣ).ker :=
  ⟨fun A B => map_mul _ A B, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det⟩

/-- AA-158. A homomorphism preserves the identity and inverses, carries subgroups to subgroups,
and pulls subgroups (normal ones to normal ones) back to subgroups. -/
@[kb "judson2026" "Proposition 11.1.4, p. 152"]
theorem judson_11_1_4 {G H : Type*} [Group G] [Group H] (φ : G →* H) :
    φ 1 = 1 ∧ (∀ g, φ g⁻¹ = (φ g)⁻¹) ∧
    (∀ H₁ : Subgroup G, ∃ K : Subgroup H, (K : Set H) = φ '' H₁) ∧
    (∀ H₂ : Subgroup H, ∃ K : Subgroup G, (K : Set G) = φ ⁻¹' H₂) ∧
    (∀ N : Subgroup H, N.Normal → ∃ K : Subgroup G, K.Normal ∧ (K : Set G) = φ ⁻¹' N) :=
  ⟨map_one φ, map_inv φ, fun H₁ => ⟨H₁.map φ, by simp⟩, fun H₂ => ⟨H₂.comap φ, by simp⟩,
    fun N hN => ⟨N.comap φ, hN.comap φ, by simp⟩⟩

/-- AA-159. The kernel of a homomorphism is a normal subgroup of the domain. -/
@[kb "judson2026" "Theorem 11.1.5, p. 153"]
theorem judson_11_1_5 {G H : Type*} [Group G] [Group H] (φ : G →* H) :
    φ.ker.Normal ∧ ∀ g, g ∈ φ.ker ↔ φ g = 1 :=
  ⟨inferInstance, fun _ => MonoidHom.mem_ker⟩

/-- AA-160. For `N` normal, `g ↦ gN` is a surjective homomorphism `G → G/N` with kernel `N`. -/
@[kb "judson2026" "Definition 11.1 (canonical homomorphism), p. 153"]
theorem judson_11_1_canonical_hom {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    Function.Surjective (QuotientGroup.mk' N) ∧ (QuotientGroup.mk' N).ker = N :=
  ⟨QuotientGroup.mk'_surjective N, QuotientGroup.ker_mk' N⟩

/-- AA-161. First isomorphism theorem: for a homomorphism `ψ : G → H` there is a unique
isomorphism `G/ker ψ ≅ ψ(G)` compatible with `ψ` and the quotient map. -/
@[kb "judson2026" "Theorem 11.2.1, p. 153"]
theorem judson_11_2_1 {G H : Type*} [Group G] [Group H] (ψ : G →* H) :
    ∃! η : G ⧸ ψ.ker ≃* ψ.range, ∀ g : G, ((η (g : G ⧸ ψ.ker) : ψ.range) : H) = ψ g := by
  refine ⟨QuotientGroup.quotientKerEquivRange ψ, fun g => rfl, fun η hη => ?_⟩
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    rw [hη g]
    rfl

/-- AA-163. Second isomorphism theorem: for `H ≤ G` and `N` normal in `G`, `HN` is a subgroup,
`H ∩ N` is normal in `H`, and `H/(H ∩ N) ≅ HN/N`. (`H ∩ N` is `N.subgroupOf H`, `HN` is `H ⊔ N`.) -/
@[kb "judson2026" "Theorem 11.2.3, p. 154"]
theorem judson_11_2_3 {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    ((H ⊔ N : Subgroup G) : Set G) = (H : Set G) * (N : Set G) ∧ (N.subgroupOf H).Normal ∧
    Nonempty (H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N)) :=
  ⟨Subgroup.mul_normal H N, inferInstance, ⟨QuotientGroup.quotientInfEquivProdNormalQuotient H N⟩⟩

/-- AA-165. Third isomorphism theorem: for normal subgroups `N ≤ H` of `G`,
`G/H ≅ (G/N)/(H/N)`. -/
@[kb "judson2026" "Theorem 11.2.5, p. 155"]
theorem judson_11_2_5 {G : Type*} [Group G] (N H : Subgroup G) [N.Normal] [H.Normal]
    (h : N ≤ H) : Nonempty (G ⧸ H ≃* (G ⧸ N) ⧸ H.map (QuotientGroup.mk' N)) :=
  ⟨(QuotientGroup.quotientQuotientEquivQuotient N H h).symm⟩

/-- AA-164. Correspondence Theorem 11.2.4: for `N` normal in `G`, the subgroups of `G ⧸ N`
correspond (order isomorphically, `H' ↦ π⁻¹ H'`) to the subgroups of `G` containing `N`, and
normal subgroups correspond to normal subgroups. -/
@[kb "judson2026" "Theorem 11.2.4, p. 155"]
theorem judson_11_2_4 {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (∀ H' : Subgroup (G ⧸ N), ((QuotientGroup.comapMk'OrderIso N H').1).Normal ↔ H'.Normal) ∧
    (∀ H : Subgroup G, N ≤ H → (H.Normal ↔ (H.map (QuotientGroup.mk' N)).Normal)) :=
  UndergradKB.AbstractAlgebra.correspondence_normal N

end UndergradKB.AbstractAlgebra.Course
