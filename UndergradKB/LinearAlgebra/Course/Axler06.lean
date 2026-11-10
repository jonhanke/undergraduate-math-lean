import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Convex.StrictConvexSpace
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 6 (Inner product spaces): course layer

Axler's inner product is linear in the first slot, Mathlib's in the second; the bridge
`axInner u v := inner v u` below is used in statements so that they read as in the book.
-/

namespace UndergradKB.LinearAlgebra.Course

open Module

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Axler's inner product `⟨u, v⟩` (linear in `u`), written with Mathlib's `inner` (linear in the
second slot): `⟨u, v⟩ = inner v u`. -/
def axInner (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) : 𝕜 := inner 𝕜 v u

/-! ## 6A Inner products and norms -/

/-- Axler 6.1: the dot product on `ℝⁿ` is positive definite, linear in the first slot and
symmetric. -/
@[kb "axler2024" "6.1, p. 200", kb "hefferon2020" "One.II.2.3, p. 53"]
theorem axler_6_1 (n : ℕ) :
    (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ x) ∧ (∀ x : Fin n → ℝ, x ⬝ᵥ x = 0 ↔ x = 0) ∧
    (∀ x y z : Fin n → ℝ, (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z) ∧
    (∀ (a : ℝ) (x z : Fin n → ℝ), (a • x) ⬝ᵥ z = a * (x ⬝ᵥ z)) ∧
    (∀ x y : Fin n → ℝ, x ⬝ᵥ y = y ⬝ᵥ x) :=
  ⟨fun x => Finset.sum_nonneg fun i _ => mul_self_nonneg (x i), fun _ => dotProduct_self_eq_zero,
    fun x y z => add_dotProduct x y z, fun a x z => smul_dotProduct a x z,
    fun x y => dotProduct_comm x y⟩

/-- Axler 6.2 and 6.4: the defining properties of an inner product, in Axler's convention. -/
@[kb "axler2024" "6.2, p. 201", kb "axler2024" "6.4, p. 202"]
theorem axler_6_2 (u u' v : E) (a : 𝕜) :
    0 ≤ RCLike.re (axInner 𝕜 v v) ∧ (axInner 𝕜 v v = 0 ↔ v = 0) ∧
    axInner 𝕜 (u + u') v = axInner 𝕜 u v + axInner 𝕜 u' v ∧
    axInner 𝕜 (a • u) v = a * axInner 𝕜 u v ∧
    axInner 𝕜 u v = starRingEnd 𝕜 (axInner 𝕜 v u) := by
  refine ⟨inner_self_nonneg (𝕜 := 𝕜), inner_self_eq_zero, inner_add_right _ _ _, inner_smul_right _ _ _, ?_⟩
  exact (inner_conj_symm (𝕜 := 𝕜) v u).symm

/-- Axler 6.6: basic properties of the inner product. -/
@[kb "axler2024" "6.6, p. 203"]
theorem axler_6_6 (u v v' : E) (a : 𝕜) :
    (axInner 𝕜 (a • u) v = a * axInner 𝕜 u v) ∧ axInner 𝕜 (0 : E) v = 0 ∧ axInner 𝕜 v (0 : E) = 0 ∧
    axInner 𝕜 u (v + v') = axInner 𝕜 u v + axInner 𝕜 u v' ∧
    axInner 𝕜 u (a • v) = starRingEnd 𝕜 a * axInner 𝕜 u v := by
  refine ⟨inner_smul_right _ _ _, inner_zero_right _, inner_zero_left _, inner_add_left _ _ _, ?_⟩
  exact inner_smul_left _ _ _

/-- Axler 6.7: the norm of `v` is the square root of `⟨v, v⟩`. -/
@[kb "axler2024" "6.7, p. 204", kb "hefferon2020" "One.II.2.1, p. 52"]
theorem axler_6_7 (v : E) : ‖v‖ = Real.sqrt (RCLike.re (axInner 𝕜 v v)) :=
  norm_eq_sqrt_re_inner (𝕜 := 𝕜) v

/-- Axler 6.9: `‖v‖ = 0` iff `v = 0`, and `‖λ v‖ = |λ| ‖v‖`. -/
@[kb "axler2024" "6.9, p. 204"]
theorem axler_6_9 (v : E) (a : 𝕜) : (‖v‖ = 0 ↔ v = 0) ∧ ‖a • v‖ = ‖a‖ * ‖v‖ :=
  ⟨norm_eq_zero, norm_smul a v⟩

/-- Axler 6.10: orthogonality is a symmetric condition on the pair `u, v`. -/
@[kb "axler2024" "6.10, p. 205"]
theorem axler_6_10 (u v : E) : axInner 𝕜 u v = 0 ↔ axInner 𝕜 v u = 0 :=
  inner_eq_zero_symm

/-- Axler 6.11: `0` is orthogonal to everything, and is the only vector orthogonal to itself. -/
@[kb "axler2024" "6.11, p. 205"]
theorem axler_6_11 (v : E) :
    axInner 𝕜 (0 : E) v = 0 ∧ axInner 𝕜 v (0 : E) = 0 ∧ (axInner 𝕜 v v = 0 ↔ v = 0) :=
  ⟨inner_zero_right _, inner_zero_left _, inner_self_eq_zero⟩

/-- Axler 6.12 (Pythagorean theorem). -/
@[kb "axler2024" "6.12, p. 205"]
theorem axler_6_12 (u v : E) (h : axInner 𝕜 u v = 0) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 :=
  by simpa [sq] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) u v (inner_eq_zero_symm.1 h)

private theorem cs_aux (x y : E) :
    ‖inner 𝕜 x y‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : 𝕜, y = r • x :=
  (norm_inner_eq_norm_tfae 𝕜 x y).out 1 3

/-- Axler 6.14 (Cauchy-Schwarz), with the equality case. -/
@[kb "axler2024" "6.14, p. 207", kb "hefferon2020" "One.II.2.6, p. 55"]
theorem axler_6_14 (u v : E) :
    ‖axInner 𝕜 u v‖ ≤ ‖u‖ * ‖v‖ ∧
    (‖axInner 𝕜 u v‖ = ‖u‖ * ‖v‖ ↔ (∃ a : 𝕜, u = a • v) ∨ (∃ a : 𝕜, v = a • u)) := by
  refine ⟨by simpa [axInner, mul_comm] using norm_inner_le_norm (𝕜 := 𝕜) v u, ?_⟩
  unfold axInner
  rw [mul_comm ‖u‖]
  constructor
  · intro h
    rcases (cs_aux (𝕜 := 𝕜) v u).1 h with h | ⟨r, hr⟩
    · exact Or.inr ⟨0, by simp [h]⟩
    · exact Or.inl ⟨r, hr⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact (cs_aux (𝕜 := 𝕜) v u).2 (Or.inr ⟨a, ha⟩)
    · have := (cs_aux (𝕜 := 𝕜) u v).2 (Or.inr ⟨a, ha⟩)
      rw [norm_inner_symm, mul_comm] at this
      exact this

/-- Axler 6.17 and 6.20: the triangle inequality, with its equality case (one vector is a
nonnegative real multiple of the other). -/
@[kb "axler2024" "6.17, p. 208", kb "axler2024" "6.20, p. 208",
  kb "hefferon2020" "One.II.2.5, p. 54"]
theorem axler_6_17 (u v : E) :
    ‖u + v‖ ≤ ‖u‖ + ‖v‖ ∧
    (‖u + v‖ = ‖u‖ + ‖v‖ ↔
      (∃ a : ℝ, 0 ≤ a ∧ u = (a : 𝕜) • v) ∨ (∃ a : ℝ, 0 ≤ a ∧ v = (a : 𝕜) • u)) := by
  refine ⟨norm_add_le u v, ?_⟩
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  have key : ∀ (a : ℝ) (x : E), (a : 𝕜) • x = a • x := fun a x =>
    (RCLike.real_smul_eq_coe_smul (K := 𝕜) a x).symm
  simp only [key]
  rw [← sameRay_iff_norm_add]
  constructor
  · rintro (h | h | ⟨r₁, r₂, h₁, h₂, h⟩)
    · exact Or.inl ⟨0, le_rfl, by simp [h]⟩
    · exact Or.inr ⟨0, le_rfl, by simp [h]⟩
    · refine Or.inl ⟨r₂ / r₁, by positivity, ?_⟩
      have : u = r₁⁻¹ • (r₁ • u) := by rw [smul_smul, inv_mul_cancel₀ h₁.ne', one_smul]
      rw [this, h, smul_smul]
      congr 1
      field_simp
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact SameRay.sameRay_nonneg_smul_left v ha
    · exact (SameRay.sameRay_nonneg_smul_left u ha).symm

include 𝕜 in
/-- Axler 6.21 (parallelogram equality). -/
@[kb "axler2024" "6.21, p. 209"]
theorem axler_6_21 (u v : E) : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  simpa [sq] using parallelogram_law_with_norm 𝕜 u v

/-- Axler Exercise 6A.20 (reverse triangle inequality). -/
@[kb "axler2024" "Ex6A.20, p. 211"]
theorem axler_ex6A_20 (u v : E) : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v

/-- Axler Exercise 6A.26 (real polarization). -/
@[kb "axler2024" "Ex6A.26, p. 212"]
theorem axler_ex6A_26 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (u v : F) :
    inner ℝ u v = (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2) / 4 := by
  have := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) u v
  simpa [sq] using this

/-- Axler Exercise 6A.27 (complex polarization; written with Mathlib's `inner`, linear in the
second slot, so the book's `⟨u, v⟩` is `inner v u` here). -/
@[kb "axler2024" "Ex6A.27, p. 212"]
theorem axler_ex6A_27 (u v : E) :
    inner 𝕜 u v = ((‖u + v‖ : 𝕜) ^ 2 - (‖u - v‖ : 𝕜) ^ 2 +
      ((‖u - (RCLike.I : 𝕜) • v‖ : 𝕜) ^ 2 - (‖u + (RCLike.I : 𝕜) • v‖ : 𝕜) ^ 2) * (RCLike.I : 𝕜)) / 4 :=
  inner_eq_sum_norm_sq_div_four u v

/-- Axler Exercise 6A.28 (Jordan-von Neumann): a norm on a real vector space satisfying the
parallelogram equality comes from an inner product. -/
@[kb "axler2024" "Ex6A.28, p. 212"]
theorem axler_ex6A_28 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ∀ x y : F, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    ∃ _ : InnerProductSpace ℝ F, ∀ x : F, ‖x‖ = Real.sqrt (inner ℝ x x) := by
  haveI : InnerProductSpaceable F := ⟨h⟩
  obtain ⟨I⟩ := nonempty_innerProductSpace ℝ F
  exact ⟨I, fun x => norm_eq_sqrt_real_inner x⟩

/-! ## 6B Orthonormal bases -/

/-- Axler 6.22: a list is orthonormal iff each vector has norm one and distinct vectors are
orthogonal. -/
@[kb "axler2024" "6.22, p. 215"]
theorem axler_6_22 {ι : Type*} (e : ι → E) :
    Orthonormal 𝕜 e ↔ (∀ i, ‖e i‖ = 1) ∧ ∀ i j, i ≠ j → axInner 𝕜 (e i) (e j) = 0 := by
  unfold Orthonormal
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j hij => h2 hij.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i j hij => h2 j i (Ne.symm hij)⟩

/-- Axler 6.25 (and Hefferon Three.VI.2.2): orthonormal lists are linearly independent. -/
@[kb "axler2024" "6.25, p. 216", kb "hefferon2020" "Three.VI.2.2, p. 290"]
theorem axler_6_25 {ι : Type*} (e : ι → E) (h : Orthonormal 𝕜 e) : LinearIndependent 𝕜 e :=
  h.linearIndependent

/-- Axler 6.26 (Bessel's inequality). -/
@[kb "axler2024" "6.26, p. 216"]
theorem axler_6_26 {ι : Type*} (e : ι → E) (h : Orthonormal 𝕜 e) (s : Finset ι) (v : E) :
    ∑ i ∈ s, ‖axInner 𝕜 v (e i)‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  Orthonormal.sum_inner_products_le (x := v) h

/-- Axler 6.27: an orthonormal basis is a basis that is an orthonormal list. -/
@[kb "axler2024" "6.27, p. 217"]
theorem axler_6_27 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) :
    Orthonormal 𝕜 b ∧ LinearIndependent 𝕜 b ∧ Submodule.span 𝕜 (Set.range b) = ⊤ :=
  ⟨b.orthonormal, b.orthonormal.linearIndependent, b.toBasis.span_eq⟩

/-- Axler 6.28 (and Hefferon Three.VI.2.3): an orthonormal list of length `dim V` is an
orthonormal basis. -/
@[kb "axler2024" "6.28, p. 217", kb "hefferon2020" "Three.VI.2.3, p. 290"]
theorem axler_6_28 [FiniteDimensional 𝕜 E] (n : ℕ) (e : Fin n → E) (h : Orthonormal 𝕜 e)
    (hn : n = finrank 𝕜 E) : ∃ b : OrthonormalBasis (Fin n) 𝕜 E, ⇑b = e := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · refine ⟨OrthonormalBasis.mk h ?_, OrthonormalBasis.coe_mk _ _⟩
    have : Subsingleton E := Module.finrank_zero_iff.1 hn.symm
    intro x _
    simp [Subsingleton.elim x 0]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    have hc : Fintype.card (Fin n) = finrank 𝕜 E := by simpa using hn
    refine ⟨OrthonormalBasis.mk h ?_, OrthonormalBasis.coe_mk _ _⟩
    rw [← coe_basisOfOrthonormalOfCardEqFinrank h hc]
    exact (basisOfOrthonormalOfCardEqFinrank h hc).span_eq.ge

/-- Axler 6.30 (and Hefferon Three.VI.2.22): expansion, Parseval's identity and the inner product
in terms of an orthonormal basis. -/
@[kb "axler2024" "6.30, p. 218", kb "hefferon2020" "Three.VI.2.22, p. 294"]
theorem axler_6_30 {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (u v : E) :
    v = ∑ i, axInner 𝕜 v (b i) • b i ∧
    ‖v‖ ^ 2 = ∑ i, ‖axInner 𝕜 v (b i)‖ ^ 2 ∧
    axInner 𝕜 u v = ∑ i, axInner 𝕜 u (b i) * starRingEnd 𝕜 (axInner 𝕜 v (b i)) := by
  refine ⟨(b.sum_repr' v).symm, (b.sum_sq_norm_inner_right v).symm, ?_⟩
  rw [axInner, ← b.sum_inner_mul_inner v u]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [axInner, inner_conj_symm]
  exact mul_comm _ _

/-- Axler 6.32 and 6.33 (Gram-Schmidt): from a linearly independent list one gets an orthonormal
list with the same span at every stage. -/
@[kb "axler2024" "6.32, p. 219", kb "axler2024" "6.33, p. 219",
  kb "hefferon2020" "Three.VI.2.7, p. 292"]
theorem axler_6_32 (m : ℕ) (v : Fin m → E) (hv : LinearIndependent 𝕜 v) :
    ∃ e : Fin m → E, Orthonormal 𝕜 e ∧
      ∀ k : Fin m, Submodule.span 𝕜 (e '' Set.Iic k) = Submodule.span 𝕜 (v '' Set.Iic k) :=
  ⟨InnerProductSpace.gramSchmidtNormed 𝕜 v, InnerProductSpace.gramSchmidtNormed_orthonormal hv,
    fun k => by
      rw [InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]⟩

/-- Axler 6.35: every finite-dimensional inner product space has an orthonormal basis. -/
@[kb "axler2024" "6.35, p. 220"]
theorem axler_6_35 [FiniteDimensional 𝕜 E] :
    Nonempty (OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :=
  ⟨stdOrthonormalBasis 𝕜 E⟩

/-- Axler 6.36: an orthonormal list in a finite-dimensional space extends to an orthonormal basis
(here the list is the first `m` vectors of the basis). -/
@[kb "axler2024" "6.36, p. 221"]
theorem axler_6_36 [FiniteDimensional 𝕜 E] (m : ℕ) (e : Fin m → E) (h : Orthonormal 𝕜 e) :
    ∃ (hm : m ≤ finrank 𝕜 E) (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E),
      ∀ i : Fin m, b (Fin.castLE hm i) = e i := by
  have hm : m ≤ finrank 𝕜 E := by
    simpa using h.linearIndependent.fintype_card_le_finrank
  refine ⟨hm, ?_⟩
  classical
  let w : Fin (finrank 𝕜 E) → E := fun j => if hj : j.val < m then e ⟨j.val, hj⟩ else 0
  let s : Set (Fin (finrank 𝕜 E)) := {j | j.val < m}
  have hw : Orthonormal 𝕜 (s.restrict w) := by
    have : s.restrict w = e ∘ fun j : s => (⟨j.1.val, j.2⟩ : Fin m) := by
      ext j; simp [w, Set.restrict, j.2.out]
    rw [this]
    refine h.comp _ ?_
    intro a b hab
    apply Subtype.ext; apply Fin.ext; simpa using congrArg Fin.val hab
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hw
  refine ⟨b, fun i => ?_⟩
  have := hb (Fin.castLE hm i) (by simp [s])
  rw [this]
  simp [w]

/-! ## 6B Linear functionals and the Riesz representation -/

/-- Axler 6.42 (Riesz representation theorem): on a finite-dimensional inner product space every
linear functional is `u ↦ ⟨u, v⟩` for a unique `v`. -/
@[kb "axler2024" "6.42, p. 223"]
theorem axler_6_42 [FiniteDimensional 𝕜 E] (φ : E →ₗ[𝕜] 𝕜) :
    ∃! v : E, ∀ u : E, φ u = axInner 𝕜 u v := by
  haveI := FiniteDimensional.complete 𝕜 E
  let φ' : StrongDual 𝕜 E := LinearMap.toContinuousLinearMap φ
  refine ⟨(InnerProductSpace.toDual 𝕜 E).symm φ', fun u => ?_, fun w hw => ?_⟩
  · have := InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜) (x := u) (y := φ')
    simp only [axInner]
    rw [this]; rfl
  · apply (InnerProductSpace.toDual 𝕜 E).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext u
    simp [InnerProductSpace.toDual_apply_apply, φ', hw u, axInner]

/-- Axler 6.58: `v ↦ ⟨·, v⟩` is a bijection from a finite-dimensional `V` onto its dual,
additive and conjugate-homogeneous. -/
@[kb "axler2024" "6.58, p. 234"]
theorem axler_6_58 [FiniteDimensional 𝕜 E] :
    let Φ : E → (E →ₗ[𝕜] 𝕜) := fun v => (innerₛₗ 𝕜 v)
    Function.Bijective Φ ∧ (∀ v w, Φ (v + w) = Φ v + Φ w) ∧
      ∀ (a : 𝕜) v, Φ (a • v) = starRingEnd 𝕜 a • Φ v := by
  intro Φ
  refine ⟨⟨?_, ?_⟩, fun v w => by simp [Φ], fun a v => by simp [Φ]⟩
  · intro v w h
    have : ∀ u, inner 𝕜 v u = inner 𝕜 w u := fun u => by
      have := LinearMap.congr_fun h u
      simpa [Φ] using this
    exact ext_inner_right 𝕜 this
  · intro φ
    obtain ⟨v, hv, -⟩ := axler_6_42 (𝕜 := 𝕜) φ
    refine ⟨v, ?_⟩
    ext u
    simp [Φ, hv u, axInner]

/-! ## 6C Orthogonal complements and minimization -/

/-- Axler 6.46 (and Hefferon Three.VI.3.4): `v ∈ U^⊥` iff `v` is orthogonal to every vector of `U`. -/
@[kb "axler2024" "6.46, p. 229", kb "hefferon2020" "Three.VI.3.4, p. 298"]
theorem axler_6_46 (U : Submodule 𝕜 E) (v : E) :
    v ∈ Uᗮ ↔ ∀ u ∈ U, axInner 𝕜 u v = 0 := by
  rw [Submodule.mem_orthogonal]
  simp only [axInner]
  constructor
  · intro h u hu; rw [inner_eq_zero_symm]; exact h u hu
  · intro h u hu; rw [inner_eq_zero_symm]; exact h u hu

/-- Axler 6.48 (and Hefferon Topic Voting Exercise 6): basic properties of the orthogonal
complement. -/
@[kb "axler2024" "6.48, p. 229", kb "hefferon2020" "Topic-Voting.Ex6, p. 174"]
theorem axler_6_48 (U W : Submodule 𝕜 E) :
    (⊥ : Submodule 𝕜 E)ᗮ = ⊤ ∧ (⊤ : Submodule 𝕜 E)ᗮ = ⊥ ∧ U ⊓ Uᗮ = ⊥ ∧ (U ≤ W → Wᗮ ≤ Uᗮ) :=
  ⟨Submodule.bot_orthogonal_eq_top, Submodule.top_orthogonal_eq_bot,
    Submodule.inf_orthogonal_eq_bot U, fun h => Submodule.orthogonal_le h⟩

/-- Axler 6.49 (and Hefferon Topic Voting 2, Three.VI.3.7): for a finite-dimensional subspace `U`,
`V = U ⊕ U^⊥`. -/
@[kb "axler2024" "6.49, p. 230", kb "hefferon2020" "Topic-Voting.2, p. 171",
  kb "hefferon2020" "Three.VI.3.7, p. 299"]
theorem axler_6_49 (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] : IsCompl U Uᗮ :=
  Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

/-- Axler 6.51: `dim U^⊥ = dim V - dim U`. -/
@[kb "axler2024" "6.51, p. 231"]
theorem axler_6_51 [FiniteDimensional 𝕜 E] (U : Submodule 𝕜 E) :
    finrank 𝕜 Uᗮ = finrank 𝕜 E - finrank 𝕜 U := by
  have := Submodule.finrank_add_finrank_orthogonal U
  omega

/-- Axler 6.52: `(U^⊥)^⊥ = U` for a finite-dimensional subspace `U`. -/
@[kb "axler2024" "6.52, p. 231"]
theorem axler_6_52 (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] : Uᗮᗮ = U :=
  Submodule.orthogonal_orthogonal U

/-- Axler 6.54: `U^⊥ = {0}` iff `U = V`, for a finite-dimensional subspace `U`. -/
@[kb "axler2024" "6.54, p. 232"]
theorem axler_6_54 (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] : Uᗮ = ⊥ ↔ U = ⊤ :=
  Submodule.orthogonal_eq_bot_iff

/-- Axler 6.55: the orthogonal projection `P_U` sends `u + w` (`u ∈ U`, `w ∈ U^⊥`) to `u`. -/
@[kb "axler2024" "6.55, p. 232"]
theorem axler_6_55 (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] (u w : E) (hu : u ∈ U)
    (hw : w ∈ Uᗮ) : U.starProjection (u + w) = u := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hu
  intro x hx
  have h : inner 𝕜 x w = 0 := hw x hx
  simpa using inner_eq_zero_symm.1 h

/-- Axler 6.56 (and Hefferon Three.VI.1.1): projection onto the line spanned by `u`. -/
@[kb "axler2024" "6.56, p. 232", kb "hefferon2020" "Three.VI.1.1, p. 286"]
theorem axler_6_56 (u v : E) :
    (𝕜 ∙ u).starProjection v = (axInner 𝕜 v u / ((‖u‖ ^ 2 : ℝ) : 𝕜)) • u :=
  Submodule.starProjection_singleton 𝕜 v

/-- Axler 6.57: properties of the orthogonal projection `P_U`. -/
@[kb "axler2024" "6.57, p. 233"]
theorem axler_6_57 (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] (v : E) :
    (∀ u ∈ U, U.starProjection u = u) ∧ (∀ w ∈ Uᗮ, U.starProjection w = 0) ∧
    U.starProjection.range = U ∧ U.starProjection.ker = Uᗮ ∧
    v - U.starProjection v ∈ Uᗮ ∧ U.starProjection (U.starProjection v) = U.starProjection v ∧
    ‖U.starProjection v‖ ≤ ‖v‖ := by
  refine ⟨fun u hu => Submodule.starProjection_eq_self_iff.2 hu,
    fun w hw => (Submodule.starProjection_apply_eq_zero_iff U).2 hw,
    Submodule.range_starProjection U, Submodule.ker_starProjection U,
    Submodule.sub_starProjection_mem_orthogonal v, ?_, Submodule.norm_starProjection_apply_le U v⟩
  exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem U v)

/-- Axler 6.57 (formula): for an orthonormal basis `e` of `U`, `P_U v = ∑ ⟨v, eₖ⟩ eₖ`. -/
theorem axler_6_57_formula (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 U) (v : E) :
    U.starProjection v = ∑ i, axInner 𝕜 v (b i : E) • (b i : E) := by
  rw [b.starProjection_eq_sum_rankOne]
  simp [axInner, InnerProductSpace.rankOne_apply]

/-- Axler 6.61 (and Hefferon Three.VI.1.17, Three.VI.3.14, Topic LineOfBestFit Exercise 9):
`P_U v` is the unique closest point of `U` to `v`. -/
@[kb "axler2024" "6.61, p. 235", kb "hefferon2020" "Three.VI.1.17, p. 289",
  kb "hefferon2020" "Three.VI.3.14, p. 302",
  kb "hefferon2020" "Topic-LineOfBestFit.Ex9, p. 310"]
theorem axler_6_61 (U : Submodule 𝕜 E) [FiniteDimensional 𝕜 U] (v : E) (u : E) (hu : u ∈ U) :
    ‖v - U.starProjection v‖ ≤ ‖v - u‖ ∧
      (‖v - U.starProjection v‖ = ‖v - u‖ ↔ u = U.starProjection v) := by
  have hmem : U.starProjection v - u ∈ U := U.sub_mem (Submodule.starProjection_apply_mem U v) hu
  have horth : axInner 𝕜 (v - U.starProjection v) (U.starProjection v - u) = 0 := by
    have := Submodule.sub_starProjection_mem_orthogonal (K := U) v
    rw [axler_6_46] at this
    exact (axler_6_10 _ _).1 (this _ hmem)
  have key : ‖v - u‖ ^ 2 = ‖v - U.starProjection v‖ ^ 2 + ‖U.starProjection v - u‖ ^ 2 := by
    have := axler_6_12 (𝕜 := 𝕜) _ _ horth
    rwa [sub_add_sub_cancel] at this
  refine ⟨?_, ?_⟩
  · have : ‖v - U.starProjection v‖ ^ 2 ≤ ‖v - u‖ ^ 2 := by
      rw [key]; nlinarith [sq_nonneg ‖U.starProjection v - u‖]
    exact le_of_sq_le_sq this (norm_nonneg _)
  · constructor
    · intro h
      rw [h] at key
      have : ‖U.starProjection v - u‖ ^ 2 = 0 := by linarith
      have h0 : U.starProjection v - u = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
      exact (sub_eq_zero.1 h0).symm
    · intro h
      subst h
      simp

end

end UndergradKB.LinearAlgebra.Course
