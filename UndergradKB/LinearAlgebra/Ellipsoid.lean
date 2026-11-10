import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import UndergradKB.Common.Attr

/-! # Ellipsoids, parallelepipeds, boxes and volume (Axler, section 7F)

Rows LA-446 to LA-454.  The ball is `Metric.ball 0 1`; ellipsoids are defined from an orthonormal
basis and positive semi-axis lengths; parallelepipeds and boxes use the open interval `(0, 1)` as
in the book (for real scalars).  The volume statements use Mathlib's Lebesgue measure `volume` on a
real finite-dimensional inner product space.
-/

set_option linter.unusedSectionVars false

open Module InnerProductSpace
open scoped InnerProductSpace

namespace UndergradKB.LinearAlgebra
namespace Ellipsoid

section Ellipsoids

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- The ellipsoid `E(s₁ f₁, …, s_n f_n)` of Axler 7.96: the vectors `v` with
`∑ |⟨v, f_k⟩|² / s_k² < 1`, for an orthonormal basis `f` and positive numbers `s`. -/
def ellipsoid {ι : Type*} [Fintype ι] (s : ι → ℝ) (f : OrthonormalBasis ι 𝕜 V) : Set V :=
  {v | ∑ i, ‖⟪f i, v⟫_𝕜‖ ^ 2 / s i ^ 2 < 1}

/-- The ellipsoid with all axes of length `1` is the unit ball, for every orthonormal basis. -/
@[kb "axler2024" "7.96, p. 305"]
theorem axler_7_96 {ι : Type*} [Fintype ι] (f : OrthonormalBasis ι 𝕜 V) :
    ellipsoid (fun _ => (1 : ℝ)) f = Metric.ball (0 : V) 1 := by
  ext v
  simp only [ellipsoid, Set.mem_ofPred_eq, one_pow, div_one, f.sum_sq_norm_inner_right,
    mem_ball_zero_iff]
  exact sq_lt_one_iff₀ (norm_nonneg _)

omit [InnerProductSpace 𝕜 V] in
lemma sq_div_mul {a s : ℝ} (hs : 0 < s) : (s * a) ^ 2 / s ^ 2 = a ^ 2 := by
  field_simp

/-- Key computation: a map with `⟨f_i, T v⟩ = s_i ⟨e_i, v⟩` sends the unit ball onto the ellipsoid. -/
lemma image_ball_eq_ellipsoid {ι : Type*} [Fintype ι] (T : V →ₗ[𝕜] V)
    (hT : Function.Surjective T) (e f : OrthonormalBasis ι 𝕜 V) (s : ι → ℝ)
    (hs : ∀ i, 0 < s i) (h : ∀ i v, ⟪f i, T v⟫_𝕜 = (s i : 𝕜) * ⟪e i, v⟫_𝕜) :
    T '' Metric.ball (0 : V) 1 = ellipsoid s f := by
  have key : ∀ v, ∑ i, ‖⟪f i, T v⟫_𝕜‖ ^ 2 / s i ^ 2 = ‖v‖ ^ 2 := by
    intro v
    rw [← e.sum_sq_norm_inner_right v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h, norm_mul, RCLike.norm_ofReal, abs_of_pos (hs i)]
    exact sq_div_mul (hs i)
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [ellipsoid, Set.mem_ofPred_eq, key]
    rw [mem_ball_zero_iff] at hv
    exact (sq_lt_one_iff₀ (norm_nonneg _)).mpr hv
  · intro hw
    obtain ⟨v, rfl⟩ := hT w
    refine ⟨v, ?_, rfl⟩
    simp only [ellipsoid, Set.mem_ofPred_eq, key] at hw
    rw [mem_ball_zero_iff]
    exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hw

variable [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V)

/-- An orthonormal eigenbasis of `T* T`. -/
noncomputable def eb : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

lemma adj_apply_eb (i : Fin (finrank 𝕜 V)) :
    LinearMap.adjoint T (T (eb T i)) = ((T.singularValues i : 𝕜) ^ 2) • eb T i := by
  have := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [eb, this, ← T.sq_singularValues_fin rfl i]
  simp

lemma inner_eb_eb (i j : Fin (finrank 𝕜 V)) :
    ⟪eb T i, eb T j⟫_𝕜 = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (eb T).orthonormal i j

lemma inner_T_eb (i j : Fin (finrank 𝕜 V)) :
    ⟪T (eb T i), T (eb T j)⟫_𝕜 = if i = j then ((T.singularValues i : 𝕜) ^ 2) else 0 := by
  rw [← LinearMap.adjoint_inner_left, adj_apply_eb, inner_smul_left, inner_eb_eb]
  split_ifs <;> simp

/-- For an injective operator there are orthonormal bases `e`, `f` of `V` such that
`⟨f_i, T v⟩ = s_i ⟨e_i, v⟩` and `T e_i = s_i f_i`, with `s_i` the singular values. -/
lemma exists_svd_bases (hT : Function.Injective T) :
    ∃ e f : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V,
      (∀ i v, ⟪f i, T v⟫_𝕜 = (T.singularValues i : 𝕜) * ⟪e i, v⟫_𝕜) ∧
      ∀ i, T (e i) = (T.singularValues i : 𝕜) • f i := by
  classical
  have hpos : ∀ i : Fin (finrank 𝕜 V), 0 < T.singularValues i :=
    fun i => (T.injective_iff_forall_lt_finrank_singularValues_pos.mp hT) i i.2
  have hne : ∀ i : Fin (finrank 𝕜 V), (T.singularValues i : 𝕜) ≠ 0 :=
    fun i => by exact_mod_cast (hpos i).ne'
  let vfam : Fin (finrank 𝕜 V) → V := fun i => ((T.singularValues i : 𝕜)⁻¹) • T (eb T i)
  have hon : Orthonormal 𝕜 vfam := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [vfam]
    rw [inner_smul_left, inner_smul_right, inner_T_eb]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      rw [map_inv₀, RCLike.conj_ofReal]
      field_simp [hne i]
    · simp [hij]
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (s := Set.univ) (by simp) (hon.comp _ Subtype.val_injective)
  have hf' : ∀ i, f i = vfam i := fun i => hf i (Set.mem_univ i)
  refine ⟨eb T, f, ?_, ?_⟩
  · intro i v
    rw [hf', show vfam i = ((T.singularValues i : 𝕜)⁻¹) • T (eb T i) from rfl,
      inner_smul_left, ← LinearMap.adjoint_inner_left, adj_apply_eb, inner_smul_left,
      map_inv₀, RCLike.conj_ofReal, map_pow, RCLike.conj_ofReal]
    field_simp [hne i]
  · intro i
    rw [hf', show vfam i = ((T.singularValues i : 𝕜)⁻¹) • T (eb T i) from rfl, smul_smul,
      mul_inv_cancel₀ (hne i), one_smul]

/-- An invertible operator maps the unit ball onto an ellipsoid whose principal axes come from its
singular value decomposition: there are orthonormal bases `e`, `f` with
`T v = ∑ s_k ⟨v, e_k⟩ f_k` (`s_k` the singular values) and `T(B) = E(s₁ f₁, …, s_n f_n)`. -/
@[kb "axler2024" "7.99, p. 306"]
theorem axler_7_99 (hT : Function.Injective T) :
    ∃ e f : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V,
      (∀ v, T v = ∑ k : Fin (finrank 𝕜 V), (T.singularValues (k : ℕ) : 𝕜) • ⟪e k, v⟫_𝕜 • f k) ∧
      T '' Metric.ball (0 : V) 1 = ellipsoid (fun k : Fin (finrank 𝕜 V) => T.singularValues k) f := by
  obtain ⟨e, f, h1, h2⟩ := exists_svd_bases T hT
  have hpos : ∀ i : Fin (finrank 𝕜 V), 0 < T.singularValues i :=
    fun i => (T.injective_iff_forall_lt_finrank_singularValues_pos.mp hT) i i.2
  refine ⟨e, f, ?_, ?_⟩
  · intro v
    conv_lhs => rw [← f.sum_repr' (T v)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1, smul_smul, mul_comm]
  · exact image_ball_eq_ellipsoid T (LinearMap.surjective_of_injective hT) e f _ hpos h1

omit [FiniteDimensional 𝕜 V] in
/-- The operator stretching by `r_i` along each vector of an orthonormal basis. -/
lemma exists_scaling {ι : Type*} [Fintype ι] (g : OrthonormalBasis ι 𝕜 V) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) :
    ∃ S : V →ₗ[𝕜] V, Function.Injective S ∧ ∀ i v, ⟪g i, S v⟫_𝕜 = (r i : 𝕜) * ⟪g i, v⟫_𝕜 := by
  let S : V →ₗ[𝕜] V := g.toBasis.constr 𝕜 (fun i => (r i : 𝕜) • g i)
  have hSg : ∀ i, S (g i) = (r i : 𝕜) • g i := fun i => by
    have := g.toBasis.constr_basis 𝕜 (fun i => (r i : 𝕜) • g i) i
    simpa [S] using this
  have hSv : ∀ v, S v = ∑ i, (⟪g i, v⟫_𝕜 * (r i : 𝕜)) • g i := by
    intro v
    conv_lhs => rw [← g.sum_repr' v]
    simp only [map_sum, map_smul, hSg, smul_smul]
  have hin : ∀ i v, ⟪g i, S v⟫_𝕜 = (r i : 𝕜) * ⟪g i, v⟫_𝕜 := by
    intro i v
    rw [hSv, g.orthonormal.inner_right_fintype (fun j => ⟪g j, v⟫_𝕜 * (r j : 𝕜)) i, mul_comm]
  refine ⟨S, ?_, hin⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h0 : ∀ i, ⟪g i, v⟫_𝕜 = 0 := by
    intro i
    have := hin i v
    rw [hv, inner_zero_right] at this
    have hri : (r i : 𝕜) ≠ 0 := by exact_mod_cast (hr i).ne'
    exact (mul_eq_zero.mp this.symm).resolve_left hri
  rw [← g.sum_repr' v]
  simp [h0]

/-- An invertible operator maps every ellipsoid onto an ellipsoid. -/
@[kb "axler2024" "7.101, p. 307"]
theorem axler_7_101 (hT : Function.Injective T) {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (g : OrthonormalBasis ι 𝕜 V) :
    ∃ (t : Fin (finrank 𝕜 V) → ℝ) (f : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V),
      (∀ i, 0 < t i) ∧ T '' ellipsoid r g = ellipsoid t f := by
  obtain ⟨S, hSinj, hS⟩ := exists_scaling g r hr
  have hSsurj : Function.Surjective S := LinearMap.surjective_of_injective hSinj
  have hE : S '' Metric.ball (0 : V) 1 = ellipsoid r g :=
    image_ball_eq_ellipsoid S hSsurj g g r hr hS
  have hTS : Function.Injective (T ∘ₗ S) := hT.comp hSinj
  obtain ⟨e, f, -, h2⟩ := axler_7_99 (T ∘ₗ S) hTS
  refine ⟨fun k => (T ∘ₗ S).singularValues k, f, fun i => ?_, ?_⟩
  · exact (((T ∘ₗ S).injective_iff_forall_lt_finrank_singularValues_pos.mp hTS) i i.2)
  · rw [← hE, ← h2, ← Set.image_comp]
    rfl

end Ellipsoids

section Parallelepipeds

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]

/-- The set `P(v₁, …, v_n)` of Axler 7.102: combinations `a₁ v₁ + ⋯ + a_n v_n` with every
coefficient in the open interval `(0, 1)`. -/
def openParallelepiped (v : ι → V) : Set V :=
  {x | ∃ a : ι → ℝ, (∀ i, a i ∈ Set.Ioo (0 : ℝ) 1) ∧ x = ∑ i, a i • v i}

/-- The translate `u + P(v₁, …, v_n)`, a parallelepiped in the sense of Axler 7.102. -/
def parallelepipedAt (u : V) (v : ι → V) : Set V :=
  {x | ∃ a : ι → ℝ, (∀ i, a i ∈ Set.Ioo (0 : ℝ) 1) ∧ x = u + ∑ i, a i • v i}

/-- A parallelepiped is the translate of the open parallelepiped, and the open parallelepiped lies
inside Mathlib's closed `parallelepiped`. -/
@[kb "axler2024" "7.102, p. 307"]
theorem axler_7_102 (u : V) (v : ι → V) :
    parallelepipedAt u v = (fun x => u + x) '' openParallelepiped v ∧
      openParallelepiped v ⊆ parallelepiped v := by
  constructor
  · ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨∑ i, a i • v i, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ⟨fun i => (ha i).1.le, fun i => (ha i).2.le⟩, rfl⟩

/-- A linear map sends the parallelepiped `u + P(v₁, …, v_n)` onto `T u + P(T v₁, …, T v_n)`
(for every linear map, in particular for invertible operators). -/
@[kb "axler2024" "7.104, p. 308"]
theorem axler_7_104 {V' : Type*} [AddCommGroup V'] [Module ℝ V'] (T : V →ₗ[ℝ] V') (u : V)
    (v : ι → V) : T '' parallelepipedAt u v = parallelepipedAt (T u) (fun i => T (v i)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, by simp [map_add, map_sum, map_smul]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨u + ∑ i, a i • v i, ⟨a, ha, rfl⟩, by simp [map_add, map_sum, map_smul]⟩

end Parallelepipeds

section Boxes

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι]

/-- The box `u + P(r₁ e₁, …, r_n e_n)` of Axler 7.105. -/
noncomputable def box (u : V) (r : ι → ℝ) (e : OrthonormalBasis ι ℝ V) : Set V :=
  parallelepipedAt u (fun i => r i • e i)

/-- Coordinate description of a box: `x` lies in `u + P(r₁ e₁, …, r_n e_n)` exactly when each
coordinate `⟨e_i, x - u⟩` lies in `(0, r_i)`. -/
@[kb "axler2024" "7.105, p. 308"]
theorem axler_7_105 (u : V) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (e : OrthonormalBasis ι ℝ V) (x : V) :
    x ∈ box u r e ↔ ∀ i, ⟪e i, x - u⟫_ℝ ∈ Set.Ioo 0 (r i) := by
  constructor
  · rintro ⟨a, ha, rfl⟩ i
    have : ∑ j, (a j • r j • e j) = ∑ j, (a j * r j) • e j :=
      Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    rw [add_sub_cancel_left, this, e.orthonormal.inner_right_fintype (fun j => a j * r j) i]
    exact ⟨mul_pos (ha i).1 (hr i), by nlinarith [(ha i).2, hr i]⟩
  · intro h
    refine ⟨fun i => ⟪e i, x - u⟫_ℝ / r i, fun i => ⟨div_pos (h i).1 (hr i), ?_⟩, ?_⟩
    · rw [div_lt_one (hr i)]; exact (h i).2
    · have h2 : ∑ i, (⟪e i, x - u⟫_ℝ / r i) • (r i • e i) = x - u := by
        conv_rhs => rw [← e.sum_repr' (x - u)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, div_mul_cancel₀ _ (hr i).ne']
      show x = u + ∑ i, (⟪e i, x - u⟫_ℝ / r i) • (r i • e i)
      rw [h2]; abel

/-- An invertible operator on a real inner product space maps boxes to boxes: with a singular value
decomposition `T v = ∑ s_k ⟨v, e_k⟩ f_k`, the box `u + P(r₁ e₁, …, r_n e_n)` goes onto
`T u + P(r₁ s₁ f₁, …, r_n s_n f_n)`, for every `u` and every `r`. -/
@[kb "axler2024" "7.107, p. 309"]
theorem axler_7_107 [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (hT : Function.Injective T) :
    ∃ e f : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V,
      (∀ v, T v = ∑ k : Fin (finrank ℝ V), T.singularValues (k : ℕ) • ⟪e k, v⟫_ℝ • f k) ∧
      ∀ (u : V) (r : Fin (finrank ℝ V) → ℝ),
        T '' box u r e = box (T u) (fun k => r k * T.singularValues (k : ℕ)) f := by
  obtain ⟨e, f, h1, h2⟩ := exists_svd_bases T hT
  simp only [RCLike.ofReal_real_eq_id, id] at h1 h2
  refine ⟨e, f, ?_, ?_⟩
  · intro v
    conv_lhs => rw [← f.sum_repr' (T v)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1]
    exact mul_smul _ _ _
  · intro u r
    rw [box, axler_7_104]
    unfold box
    congr 1
    funext k
    rw [map_smul, h2, smul_smul]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The volume (Lebesgue measure) of the box `u + P(r₁ e₁, …, r_n e_n)` is the product
`r₁ ⋯ r_n` of its side lengths. -/
@[kb "axler2024" "7.108, p. 309"]
theorem axler_7_108 (u : V) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (e : OrthonormalBasis ι ℝ V) :
    MeasureTheory.volume (box u r e) = ENNReal.ofReal (∏ i, r i) := by
  have hset : box u r e = (fun x => x + -u) ⁻¹'
      ((fun x : V => (WithLp.ofLp (e.repr x) : ι → ℝ)) ⁻¹'
        Set.pi Set.univ (fun i => Set.Ioo (0 : ℝ) (r i))) := by
    ext x
    rw [axler_7_105 u r hr e x]
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      OrthonormalBasis.repr_apply_apply, ← sub_eq_add_neg]
  have hmp : MeasureTheory.MeasurePreserving
      (fun x : V => (WithLp.ofLp (e.repr x) : ι → ℝ)) MeasureTheory.volume
      MeasureTheory.volume :=
    (PiLp.volume_preserving_ofLp ι).comp e.measurePreserving_repr
  rw [hset, MeasureTheory.measure_preimage_add_right,
    hmp.measure_preimage (MeasurableSet.univ_pi fun i => measurableSet_Ioo).nullMeasurableSet,
    Real.volume_pi_Ioo, ENNReal.ofReal_prod_of_nonneg (fun i _ => (hr i).le)]
  simp

end Boxes

section Volume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Volume changes by the factor "product of the singular values": for a linear operator `T` on a
real inner product space and any set `Ω`, `volume (T '' Ω) = (∏ singular values of T) * volume Ω`.
(Invertibility is not needed; if `T` is not invertible both sides vanish.) -/
@[kb "axler2024" "7.111, p. 311"]
theorem axler_7_111 (T : V →ₗ[ℝ] V) (Ω : Set V) :
    MeasureTheory.volume (T '' Ω) =
      ENNReal.ofReal (∏ i ∈ Finset.range (finrank ℝ V), T.singularValues i) *
        MeasureTheory.volume Ω := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_eq_prod_singularValues]

end Volume

end Ellipsoid
end UndergradKB.LinearAlgebra
