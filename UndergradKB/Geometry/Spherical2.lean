import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import UndergradKB.Geometry.Spherical
import UndergradKB.Common.Attr

namespace UndergradKB.Geometry

open MeasureTheory Metric Set InnerProductGeometry RealInnerProductSpace
open scoped Pointwise

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The area (surface measure) of a subset of the unit sphere of `ℝ³`: the real value of Mathlib's
`Measure.toSphere` of Lebesgue measure, applied to the part of the set on the sphere. -/
noncomputable def sphArea (S : Set E3) : ℝ :=
  (volume : Measure E3).toSphere.real (Subtype.val ⁻¹' S : Set (sphere (0 : E3) 1))

theorem sphArea_eq_cone {S : Set E3} (hS : MeasurableSet S) :
    sphArea S = 3 * volume.real (Ioo (0 : ℝ) 1 • (S ∩ sphere (0 : E3) 1)) := by
  have hm : MeasurableSet (Subtype.val ⁻¹' S : Set (sphere (0 : E3) 1)) :=
    hS.preimage measurable_subtype_coe
  unfold sphArea
  rw [measureReal_def, Measure.toSphere_apply' _ hm, Subtype.image_preimage_coe, measureReal_def]
  simp [Set.inter_comm]

theorem sphArea_preimage (g : E3 ≃ₗᵢ[ℝ] E3) {S : Set E3} (hS : MeasurableSet S) :
    sphArea (g ⁻¹' S) = sphArea S := by
  have hgS : MeasurableSet (g ⁻¹' S) := g.continuous.measurable hS
  rw [sphArea_eq_cone hgS, sphArea_eq_cone hS]
  congr 1
  have : Ioo (0 : ℝ) 1 • (g ⁻¹' S ∩ sphere (0 : E3) 1) = g ⁻¹' (Ioo (0 : ℝ) 1 • (S ∩ sphere (0 : E3) 1)) := by
    ext x
    simp only [Set.mem_smul, mem_preimage, mem_inter_iff, mem_sphere_iff_norm, sub_zero]
    constructor
    · rintro ⟨t, ht, y, ⟨hy1, hy2⟩, rfl⟩
      exact ⟨t, ht, g y, ⟨hy1, by simpa using hy2⟩, by simp⟩
    · rintro ⟨t, ht, y, ⟨hy1, hy2⟩, hxy⟩
      refine ⟨t, ht, g.symm y, ⟨by simpa using hy1, by simpa using hy2⟩, ?_⟩
      apply g.injective
      simpa using hxy
  rw [this]
  rw [measureReal_def, measureReal_def, (g.measurePreserving).measure_preimage_emb g.toHomeomorph.measurableEmbedding]

theorem sphArea_inter_sphere (S : Set E3) : sphArea (S ∩ sphere (0 : E3) 1) = sphArea S := by
  unfold sphArea
  have : (Subtype.val ⁻¹' (S ∩ sphere (0 : E3) 1) : Set (sphere (0 : E3) 1)) = Subtype.val ⁻¹' S := by
    ext x
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [this]

theorem sphArea_total : sphArea univ = 4 * Real.pi := by
  unfold sphArea
  rw [preimage_univ, Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin, measureReal_def, EuclideanSpace.volume_ball_fin_three]
  have hpi := Real.pi_pos
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by norm_num)]
  push_cast
  ring

theorem sphArea_union {S T : Set E3} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h : sphArea (S ∩ T) = 0) : sphArea (S ∪ T) = sphArea S + sphArea T := by
  unfold sphArea at *
  have := measureReal_union_add_inter (μ := (volume : Measure E3).toSphere)
    (s := (Subtype.val ⁻¹' S : Set (sphere (0 : E3) 1))) (t := Subtype.val ⁻¹' T)
    (hT.preimage measurable_subtype_coe)
  rw [preimage_inter] at h
  rw [preimage_union]
  linarith

theorem sphArea_mono {S T : Set E3} (h : S ⊆ T) : sphArea S ≤ sphArea T := by
  unfold sphArea
  exact measureReal_mono (preimage_mono h)

theorem sphArea_neg {S : Set E3} (hS : MeasurableSet S) : sphArea ((fun x => -x) ⁻¹' S) = sphArea S :=
  sphArea_preimage (LinearIsometryEquiv.neg ℝ) hS

theorem sphArea_of_subset_submodule {S : Set E3} (hS : MeasurableSet S) (W : Submodule ℝ E3) (hW : W ≠ ⊤)
    (h : S ⊆ W) : sphArea S = 0 := by
  rw [sphArea_eq_cone hS]
  have : (volume : Measure E3) (Ioo (0 : ℝ) 1 • (S ∩ sphere (0 : E3) 1)) = 0 := by
    refine measure_mono_null ?_ (Measure.addHaar_submodule volume W hW)
    rintro x hx
    rw [Set.mem_smul] at hx
    obtain ⟨t, ht, y, hy, rfl⟩ := hx
    exact W.smul_mem t (h hy.1)
  simp [measureReal_def, this]

theorem sphArea_plane {n : E3} (hn : n ≠ 0) : sphArea {x | ⟪x, n⟫ = 0} = 0 := by
  refine sphArea_of_subset_submodule ?_ (ℝ ∙ n)ᗮ ?_ ?_
  · exact (isClosed_eq (continuous_id.inner continuous_const) continuous_const).measurableSet
  · intro h
    have : n ∈ (ℝ ∙ n)ᗮ := by rw [h]; trivial
    exact hn (by simpa using (Submodule.mem_orthogonal_singleton_iff_inner_right.mp this))
  · intro x hx
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hx

/-- The `i`-th standard basis vector of `ℝ³`. -/
noncomputable abbrev eb (i : Fin 3) : E3 := EuclideanSpace.single i 1

theorem exists_isometry_of_orthonormal {v0 v1 : E3} (h0 : ‖v0‖ = 1) (h1 : ‖v1‖ = 1) (h01 : ⟪v0, v1⟫ = 0) :
    ∃ g : E3 ≃ₗᵢ[ℝ] E3, g (eb 0) = v0 ∧ g (eb 1) = v1 := by
  let v : Fin 3 → E3 := ![v0, v1, 0]
  let s : Set (Fin 3) := {0, 1}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 0 ∨ i = 1 := by simpa [s] using hi
    have hj' : j = 0 ∨ j = 1 := by simpa [s] using hj
    have n0 : ⟪v0, v0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h0]; norm_num
    have n1 : ⟪v1, v1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [v, n0, n1, h0, h1, h01, real_inner_comm v0 v1]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := E3)
    (ι := Fin 3) (by simp) hv
  refine ⟨(EuclideanSpace.basisFun (Fin 3) ℝ).equiv b (Equiv.refl _), ?_, ?_⟩
  · have := (EuclideanSpace.basisFun (Fin 3) ℝ).equiv_apply_basis b (Equiv.refl _) 0
    simpa [hb 0 (by simp [s]), v] using this
  · have := (EuclideanSpace.basisFun (Fin 3) ℝ).equiv_apply_basis b (Equiv.refl _) 1
    simpa [hb 1 (by simp [s]), v] using this

/-- The closed half-space `{x | 0 ≤ ⟪x, n⟫}` of `ℝ³` (its trace on the sphere is a closed half-sphere). -/
def hs (n : E3) : Set E3 := {x | 0 ≤ ⟪x, n⟫}

theorem measurableSet_hs (n : E3) : MeasurableSet (hs n) :=
  (isClosed_le continuous_const (continuous_id.inner continuous_const)).measurableSet

theorem hs_inter_hs_neg (n : E3) : hs n ∩ hs (-n) = {x | ⟪x, n⟫ = 0} := by
  ext x
  simp only [hs, mem_inter_iff, mem_ofPred_eq, inner_neg_right]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; constructor <;> linarith

theorem sphArea_hs_inter_hs_neg {n : E3} (hn : n ≠ 0) : sphArea (hs n ∩ hs (-n)) = 0 := by
  rw [hs_inter_hs_neg]; exact sphArea_plane hn

theorem sphArea_hs {n : E3} (hn : n ≠ 0) : sphArea (hs n) = 2 * Real.pi := by
  have hu : hs n ∪ hs (-n) = univ := by
    ext x
    simp only [hs, mem_union, mem_ofPred_eq, inner_neg_right, mem_univ, iff_true]
    rcases le_total 0 ⟪x, n⟫ with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hneg : sphArea (hs (-n)) = sphArea (hs n) := by
    have : hs (-n) = (fun x : E3 => -x) ⁻¹' hs n := by
      ext x; simp [hs]
    rw [this]; exact sphArea_neg (measurableSet_hs n)
  have := sphArea_union (measurableSet_hs n) (measurableSet_hs (-n)) (sphArea_hs_inter_hs_neg hn)
  rw [hu, sphArea_total, hneg] at this
  linarith

/-- The unit vector `m t = (-sin t, cos t, 0)` in the horizontal plane. -/
noncomputable def mv (t : ℝ) : E3 := Real.cos t • eb 1 - Real.sin t • eb 0

theorem inner_mv (x : E3) (t : ℝ) : ⟪x, mv t⟫ = Real.cos t * ⟪x, eb 1⟫ - Real.sin t * ⟪x, eb 0⟫ := by
  simp [mv, inner_sub_right, inner_smul_right]

theorem mv_ne_zero (t : ℝ) : mv t ≠ 0 := by
  intro h
  have h1 := inner_mv (eb 1) t
  have h2 := inner_mv (eb 0) t
  rw [h] at h1 h2
  have e10 : ⟪eb 1, eb 0⟫ = 0 := by simp [eb, EuclideanSpace.inner_single_left]
  have e01 : ⟪eb 0, eb 1⟫ = 0 := by simp [eb, EuclideanSpace.inner_single_left]
  have e11 : ⟪eb 1, eb 1⟫ = 1 := by simp [eb, EuclideanSpace.inner_single_left]
  have e00 : ⟪eb 0, eb 0⟫ = 1 := by simp [eb, EuclideanSpace.inner_single_left]
  rw [e10, e11] at h1
  rw [e01, e00] at h2
  rw [inner_zero_right] at h1 h2
  have := Real.sin_sq_add_cos_sq t
  nlinarith

/-- The lune between the half-planes of angles `a ≤ b` about the vertical axis. -/
noncomputable def lune (a b : ℝ) : Set E3 := hs (mv a) ∩ hs (-mv b)

theorem measurableSet_lune (a b : ℝ) : MeasurableSet (lune a b) :=
  (measurableSet_hs _).inter (measurableSet_hs _)

theorem sphArea_hs_inter_iso (g : E3 ≃ₗᵢ[ℝ] E3) (n1 n2 : E3) :
    sphArea (hs (g n1) ∩ hs (g n2)) = sphArea (hs n1 ∩ hs n2) := by
  have : hs (g n1) ∩ hs (g n2) = g.symm ⁻¹' (hs n1 ∩ hs n2) := by
    ext x
    simp only [hs, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    rw [← g.inner_map_map (g.symm x) n1, ← g.inner_map_map (g.symm x) n2]
    simp
  rw [this]
  exact sphArea_preimage _ ((measurableSet_hs _).inter (measurableSet_hs _))

theorem inner_eb_eb (i j : Fin 3) : ⟪eb i, eb j⟫ = if i = j then 1 else 0 := by
  simp [eb, EuclideanSpace.inner_single_left, PiLp.single_apply, eq_comm]

theorem norm_eq_one_of_inner_self {v : E3} (h : ⟪v, v⟫ = 1) : ‖v‖ = 1 := by
  have : ‖v‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, h]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this

/-- A rotation about the vertical axis by the angle `s`. -/
theorem exists_rotation (s : ℝ) :
    ∃ g : E3 ≃ₗᵢ[ℝ] E3, ∀ t, g (mv t) = mv (t + s) := by
  have e00 := inner_eb_eb 0 0
  have e11 := inner_eb_eb 1 1
  have e01 := inner_eb_eb 0 1
  have e10 := inner_eb_eb 1 0
  simp only [ite_true] at e00 e11
  have e01' : ⟪eb 0, eb 1⟫ = 0 := by simpa using e01
  have e10' : ⟪eb 1, eb 0⟫ = 0 := by simpa using e10
  have hsc := Real.sin_sq_add_cos_sq s
  obtain ⟨g, hg0, hg1⟩ := exists_isometry_of_orthonormal
    (v0 := Real.cos s • eb 0 + Real.sin s • eb 1) (v1 := mv s)
    (norm_eq_one_of_inner_self (by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, e00, e11, e01', e10']
      simp; nlinarith))
    (norm_eq_one_of_inner_self (by
      simp only [mv, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, e00, e11, e01', e10']
      simp; nlinarith))
    (by
      simp only [mv, inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, e00, e11, e01', e10']
      simp; ring)
  refine ⟨g, fun t => ?_⟩
  simp only [mv, map_sub, map_smul, hg0, hg1, Real.cos_add, Real.sin_add]
  module

theorem sphArea_lune_shift (a b s : ℝ) : sphArea (lune (a + s) (b + s)) = sphArea (lune a b) := by
  obtain ⟨g, hg⟩ := exists_rotation s
  have : lune (a + s) (b + s) = hs (g (mv a)) ∩ hs (g (-mv b)) := by
    rw [map_neg, hg, hg]; rfl
  unfold lune at *
  rw [this]
  exact sphArea_hs_inter_iso g _ _

theorem lune_union {a b c : ℝ} (hab : a < b) (hbc : b < c) (hca : c - a ≤ Real.pi) :
    lune a c = lune a b ∪ lune b c := by
  have hs1 : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2 : 0 < Real.sin (c - b) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have key : ∀ x : E3, Real.sin (c - a) * ⟪x, mv b⟫ =
      Real.sin (c - b) * ⟪x, mv a⟫ + Real.sin (b - a) * ⟪x, mv c⟫ := by
    intro x
    simp only [inner_mv, Real.sin_sub]
    ring
  ext x
  simp only [lune, hs, mem_inter_iff, mem_ofPred_eq, mem_union, inner_neg_right]
  constructor
  · rintro ⟨h1, h2⟩
    rcases le_total 0 ⟪x, mv b⟫ with h | h
    · exact Or.inr ⟨h, h2⟩
    · exact Or.inl ⟨h1, by linarith⟩
  · rcases eq_or_lt_of_le hca with hc | hc
    · have hcm : mv c = - mv a := by
        have : c = a + Real.pi := by linarith
        simp only [mv, this, Real.cos_add_pi, Real.sin_add_pi]
        module
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by rw [hcm]; simpa using h1⟩
      · refine ⟨?_, h2⟩
        rw [hcm, inner_neg_right] at h2
        linarith
    · have hs3 : 0 < Real.sin (c - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hc
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨h1, ?_⟩
        have := key x
        nlinarith
      · refine ⟨?_, h2⟩
        have := key x
        nlinarith

theorem sphArea_nonneg (S : Set E3) : 0 ≤ sphArea S := measureReal_nonneg

/-- A nonnegative function on `[0, π]` additive on `[0, π]` is linear there. -/
theorem linear_of_additive (F : ℝ → ℝ) (hnn : ∀ x, 0 ≤ F x)
    (hadd : ∀ x y, 0 ≤ x → 0 ≤ y → x + y ≤ Real.pi → F (x + y) = F x + F y) :
    ∀ θ, 0 ≤ θ → θ ≤ Real.pi → F θ = θ * (F Real.pi / Real.pi) := by
  have hpi := Real.pi_pos
  have h0 : F 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl (by linarith)
    simp at this; linarith
  have hmono : ∀ x y, 0 ≤ x → x ≤ y → y ≤ Real.pi → F x ≤ F y := by
    intro x y hx hxy hy
    have := hadd x (y - x) hx (by linarith) (by linarith)
    rw [add_sub_cancel] at this
    linarith [hnn (y - x)]
  have hk : ∀ n : ℕ, 0 < n → ∀ k : ℕ, k ≤ n → F (k * Real.pi / n) = k * F (Real.pi / n) := by
    intro n hn k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hkn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hk' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      have e : ((k + 1 : ℕ) : ℝ) * Real.pi / n = k * Real.pi / n + Real.pi / n := by
        push_cast; ring
      rw [e, hadd _ _ (by positivity) (by positivity), ih (by omega)]
      · push_cast; ring
      · rw [← add_div, div_le_iff₀ hn']
        nlinarith
  have hfull : ∀ n : ℕ, 0 < n → ∀ k : ℕ, k ≤ n → F (k * Real.pi / n) = k * F Real.pi / n := by
    intro n hn k hkn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := hk n hn n le_rfl
    rw [mul_div_cancel_left₀ _ hn'.ne'] at h1
    rw [hk n hn k hkn]
    have : F (Real.pi / n) = F Real.pi / n := by
      field_simp; linarith
    rw [this]; ring
  intro θ hθ hθπ
  set c := F Real.pi / Real.pi with hc
  have hc0 : 0 ≤ c := div_nonneg (hnn _) hpi.le
  have hFpi : F Real.pi = c * Real.pi := by rw [hc]; field_simp
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (c * Real.pi / ε)
    have hnpos : 0 < n := by
      have : (0 : ℝ) ≤ c * Real.pi / ε := by positivity
      exact_mod_cast lt_of_le_of_lt this hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    set k := ⌈(n : ℝ) * θ / Real.pi⌉₊ with hkdef
    have hkn : k ≤ n := by
      rw [hkdef, Nat.ceil_le]
      rw [div_le_iff₀ hpi]; nlinarith
    have hkθ : (n : ℝ) * θ / Real.pi ≤ k := Nat.le_ceil _
    have hkθ' : (k : ℝ) < n * θ / Real.pi + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : θ ≤ k * Real.pi / n := by
      rw [le_div_iff₀ hn']
      rw [div_le_iff₀ hpi] at hkθ
      nlinarith
    have h2 := hmono θ _ hθ h1 (by
      rw [div_le_iff₀ hn']; have : (k : ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith)
    rw [hfull n hnpos k hkn, hFpi] at h2
    have h3 : (k : ℝ) * (c * Real.pi) / n ≤ c * θ + ε := by
      have : (k : ℝ) * (c * Real.pi) / n = c * (k * Real.pi / n) := by ring
      rw [this]
      have h4 : (k : ℝ) * Real.pi / n < θ + Real.pi / n := by
        rw [div_lt_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
        have := mul_lt_mul_of_pos_right hkθ' hpi
        have e : (n : ℝ) * θ / Real.pi * Real.pi = n * θ := by field_simp
        nlinarith
      have h5 : c * (Real.pi / n) ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ hn']
        rw [div_lt_iff₀ hε] at hn
        nlinarith
      nlinarith
    linarith [mul_comm θ c]
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (c * Real.pi / ε)
    have hnpos : 0 < n := by
      have : (0 : ℝ) ≤ c * Real.pi / ε := by positivity
      exact_mod_cast lt_of_le_of_lt this hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
    set k := ⌊(n : ℝ) * θ / Real.pi⌋₊ with hkdef
    have hkθ : (k : ℝ) ≤ n * θ / Real.pi := Nat.floor_le (by positivity)
    have hkθ' : (n : ℝ) * θ / Real.pi < k + 1 := Nat.lt_floor_add_one _
    have hkn : k ≤ n := by
      have : (k : ℝ) ≤ n := by
        refine hkθ.trans ?_
        rw [div_le_iff₀ hpi]; nlinarith
      exact_mod_cast this
    have h1 : k * Real.pi / n ≤ θ := by
      rw [div_le_iff₀ hn']
      rw [le_div_iff₀ hpi] at hkθ
      nlinarith
    have h2 := hmono _ θ (by positivity) h1 hθπ
    rw [hfull n hnpos k hkn, hFpi] at h2
    have h4 : θ < (k : ℝ) * Real.pi / n + Real.pi / n := by
      rw [← add_div, lt_div_iff₀ hn']
      rw [div_lt_iff₀ hpi] at hkθ'
      nlinarith
    have h5 : c * (Real.pi / n) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hn']
      rw [div_lt_iff₀ hε] at hn
      nlinarith
    have : (k : ℝ) * (c * Real.pi) / n = c * (k * Real.pi / n) := by ring
    rw [this] at h2
    nlinarith [mul_comm θ c]

theorem sphArea_lune_zero {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) : sphArea (lune 0 θ) = 2 * θ := by
  have hpi := Real.pi_pos
  have hF0 : sphArea (lune 0 0) = 0 := by
    have : lune 0 0 = {x | ⟪x, mv 0⟫ = 0} := hs_inter_hs_neg _
    rw [this]; exact sphArea_plane (mv_ne_zero 0)
  have hFpi : sphArea (lune 0 Real.pi) = 2 * Real.pi := by
    have : lune 0 Real.pi = hs (mv 0) := by
      have hm : -mv Real.pi = mv 0 := by
        simp only [mv, Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero]; module
      rw [lune, hm, inter_self]
    rw [this]; exact sphArea_hs (mv_ne_zero 0)
  have hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ Real.pi →
      sphArea (lune 0 (x + y)) = sphArea (lune 0 x) + sphArea (lune 0 y) := by
    intro x y hx hy hxy
    rcases eq_or_lt_of_le hx with rfl | hx'
    · simp [hF0]
    rcases eq_or_lt_of_le hy with rfl | hy'
    · simp [hF0]
    have hu := lune_union (a := 0) (b := x) (c := x + y) hx' (by linarith) (by linarith)
    have hnull : sphArea (lune 0 x ∩ lune x (x + y)) = 0 := by
      apply le_antisymm _ (sphArea_nonneg _)
      calc sphArea (lune 0 x ∩ lune x (x + y)) ≤ sphArea {z | ⟪z, mv x⟫ = 0} := by
            apply sphArea_mono
            rintro z ⟨⟨_, h2⟩, ⟨h3, _⟩⟩
            simp only [hs, mem_ofPred_eq, inner_neg_right] at h2 h3 ⊢
            linarith
        _ = 0 := sphArea_plane (mv_ne_zero x)
    rw [hu, sphArea_union (measurableSet_lune _ _) (measurableSet_lune _ _) hnull]
    have := sphArea_lune_shift 0 y x
    rw [zero_add, add_comm y x] at this
    rw [this]
  have := linear_of_additive (fun θ => sphArea (lune 0 θ)) (fun _ => sphArea_nonneg _) hadd θ h0 hπ
  rw [this, hFpi]
  field_simp

theorem hs_smul {n : E3} {c : ℝ} (hc : 0 < c) : hs (c • n) = hs n := by
  ext x
  simp only [hs, mem_ofPred_eq, inner_smul_right]
  exact mul_nonneg_iff_of_pos_left hc

/-- Area of a lune (Petrunin, proof of Lemma 16.1): the intersection of the two half-spheres with poles
`n₁`, `n₂`, where the angle between `n₁` and `n₂` is strictly between `0` and `π`, has area `2(π - angle n₁ n₂)`
(twice the dihedral angle of the lune). -/
theorem sphArea_hs_inter {n1 n2 : E3} (h1 : n1 ≠ 0) (h2 : n2 ≠ 0)
    (hφ0 : 0 < angle n1 n2) (hφπ : angle n1 n2 < Real.pi) :
    sphArea (hs n1 ∩ hs n2) = 2 * (Real.pi - angle n1 n2) := by
  set φ := angle n1 n2 with hφ
  set θ := Real.pi - φ with hθ
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
  have n1pos : 0 < ‖n1‖ := norm_pos_iff.mpr h1
  have n2pos : 0 < ‖n2‖ := norm_pos_iff.mpr h2
  set u1 := (‖n1‖⁻¹) • n1 with hu1
  set u2 := (‖n2‖⁻¹) • n2 with hu2
  have hu1n : ‖u1‖ = 1 := by rw [hu1, norm_smul, norm_inv, norm_norm]; field_simp
  have hu2n : ‖u2‖ = 1 := by rw [hu2, norm_smul, norm_inv, norm_norm]; field_simp
  have hcos : ⟪u1, u2⟫ = Real.cos φ := by
    have := InnerProductGeometry.cos_angle (x := n1) (y := n2)
    rw [← hφ] at this
    rw [this, hu1, hu2, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp
  have hs1 : hs n1 = hs u1 := (hs_smul (inv_pos.mpr n1pos)).symm
  have hs2 : hs n2 = hs u2 := (hs_smul (inv_pos.mpr n2pos)).symm
  clear_value u1 u2
  have hin1 : ⟪u1, u1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu1n]; norm_num
  have hin2 : ⟪u2, u2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu2n]; norm_num
  set v := (Real.sin φ)⁻¹ • (u2 - Real.cos φ • u1) with hv
  have hvu : ⟪v, u1⟫ = 0 := by
    rw [hv, inner_smul_left, inner_sub_left, inner_smul_left, real_inner_comm u1 u2, hcos, hin1]
    simp
  have hvn : ‖v‖ = 1 := by
    apply norm_eq_one_of_inner_self
    rw [hv, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, real_inner_comm u1 u2, hcos, hin1, hin2]
    simp only [RCLike.conj_to_real]
    have := Real.sin_sq_add_cos_sq φ
    field_simp
    nlinarith
  obtain ⟨g, hg0, hg1⟩ := exists_isometry_of_orthonormal hvn hu1n hvu
  have hsθ : Real.sin θ = Real.sin φ := by rw [hθ, Real.sin_pi_sub]
  have hcθ : Real.cos θ = - Real.cos φ := by rw [hθ, Real.cos_pi_sub]
  have e1 : g (mv 0) = u1 := by simp [mv, hg1]
  have e2 : g (-mv θ) = u2 := by
    simp only [mv, map_neg, map_sub, map_smul, hg0, hg1, hsθ, hcθ, hv]
    have : Real.sin φ ≠ 0 := hsφ.ne'
    match_scalars <;> field_simp <;> ring
  rw [hs1, hs2, ← e1, ← e2, sphArea_hs_inter_iso]
  exact sphArea_lune_zero (by rw [hθ]; linarith) (by rw [hθ]; linarith) |>.trans (by rw [hθ])

theorem sphArea_eq_integral {S : Set E3} (hS : MeasurableSet S) :
    sphArea S = ∫ x : sphere (0 : E3) 1, S.indicator (1 : E3 → ℝ) (x : E3) ∂(volume : Measure E3).toSphere := by
  have hm : MeasurableSet (Subtype.val ⁻¹' S : Set (sphere (0 : E3) 1)) :=
    hS.preimage measurable_subtype_coe
  unfold sphArea
  rw [← integral_indicator_one hm]
  congr 1

theorem integrable_indicator_sph {S : Set E3} (hS : MeasurableSet S) :
    Integrable (fun x : sphere (0 : E3) 1 => S.indicator (1 : E3 → ℝ) (x : E3))
      (volume : Measure E3).toSphere := by
  have hm : MeasurableSet (Subtype.val ⁻¹' S : Set (sphere (0 : E3) 1)) :=
    hS.preimage measurable_subtype_coe
  have : (fun x : sphere (0 : E3) 1 => S.indicator (1 : E3 → ℝ) (x : E3)) =
      (Subtype.val ⁻¹' S : Set (sphere (0 : E3) 1)).indicator (fun _ => (1 : ℝ)) := by
    ext x
    by_cases h : (x : E3) ∈ S <;> simp [Set.indicator, h]
  rw [this]
  exact (integrable_const (1 : ℝ)).indicator hm

theorem ae_ne_zero_inner {n : E3} (hn : n ≠ 0) :
    ∀ᵐ x : sphere (0 : E3) 1 ∂(volume : Measure E3).toSphere, ⟪(x : E3), n⟫ ≠ 0 := by
  have h : (volume : Measure E3).toSphere (Subtype.val ⁻¹' {x : E3 | ⟪x, n⟫ = 0}) = 0 := by
    have := sphArea_plane hn
    unfold sphArea at this
    exact (measureReal_eq_zero_iff).mp this
  have := measure_eq_zero_iff_ae_notMem.mp h
  filter_upwards [this] with x hx
  simpa using hx

theorem integral_six {α : Type*} [MeasurableSpace α] {μ : Measure α} {F1 F2 F3 F4 F5 F6 G H K : α → ℝ}
    (i1 : Integrable F1 μ) (i2 : Integrable F2 μ) (i3 : Integrable F3 μ) (i4 : Integrable F4 μ)
    (i5 : Integrable F5 μ) (i6 : Integrable F6 μ) (iG : Integrable G μ) (iH : Integrable H μ)
    (iK : Integrable K μ)
    (h : ∀ᵐ x ∂μ, F1 x + F2 x + F3 x + F4 x + F5 x + F6 x = G x + 2 * H x + 2 * K x) :
    ∫ x, F1 x ∂μ + ∫ x, F2 x ∂μ + ∫ x, F3 x ∂μ + ∫ x, F4 x ∂μ + ∫ x, F5 x ∂μ + ∫ x, F6 x ∂μ
      = ∫ x, G x ∂μ + 2 * ∫ x, H x ∂μ + 2 * ∫ x, K x ∂μ := by
  have e := integral_congr_ae h
  have j2 : Integrable (fun x => F1 x + F2 x) μ := i1.add i2
  have j3 : Integrable (fun x => F1 x + F2 x + F3 x) μ := j2.add i3
  have j4 : Integrable (fun x => F1 x + F2 x + F3 x + F4 x) μ := j3.add i4
  have j5 : Integrable (fun x => F1 x + F2 x + F3 x + F4 x + F5 x) μ := j4.add i5
  have jH : Integrable (fun x => 2 * H x) μ := iH.const_mul 2
  have jK : Integrable (fun x => 2 * K x) μ := iK.const_mul 2
  have jGH : Integrable (fun x => G x + 2 * H x) μ := iG.add jH
  rw [integral_add j5 i6, integral_add j4 i5, integral_add j3 i4, integral_add j2 i3,
    integral_add i1 i2, integral_add jGH jK, integral_add iG jH,
    integral_const_mul, integral_const_mul] at e
  exact e

/-- The counting identity of the six lunes of a triangle (Petrunin, proof of Lemma 16.1). -/
theorem six_lunes {u v w : E3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    sphArea (hs v ∩ hs w) + sphArea (hs (-v) ∩ hs (-w)) + sphArea (hs u ∩ hs w)
      + sphArea (hs (-u) ∩ hs (-w)) + sphArea (hs u ∩ hs v) + sphArea (hs (-u) ∩ hs (-v))
    = 4 * Real.pi + 2 * sphArea (hs u ∩ hs v ∩ hs w) + 2 * sphArea (hs (-u) ∩ hs (-v) ∩ hs (-w)) := by
  have M : ∀ n : E3, MeasurableSet (hs n) := measurableSet_hs
  have m1 := (M v).inter (M w)
  have m2 := (M (-v)).inter (M (-w))
  have m3 := (M u).inter (M w)
  have m4 := (M (-u)).inter (M (-w))
  have m5 := (M u).inter (M v)
  have m6 := (M (-u)).inter (M (-v))
  have m7 := ((M u).inter (M v)).inter (M w)
  have m8 := ((M (-u)).inter (M (-v))).inter (M (-w))
  have hT : 4 * Real.pi = sphArea univ := sphArea_total.symm
  rw [sphArea_eq_integral m1, sphArea_eq_integral m2, sphArea_eq_integral m3, sphArea_eq_integral m4,
    sphArea_eq_integral m5, sphArea_eq_integral m6, sphArea_eq_integral m7, sphArea_eq_integral m8,
    hT, sphArea_eq_integral MeasurableSet.univ]
  have key : ∀ᵐ x : sphere (0 : E3) 1 ∂(volume : Measure E3).toSphere,
      (hs v ∩ hs w).indicator (1 : E3 → ℝ) (x : E3) + (hs (-v) ∩ hs (-w)).indicator (1 : E3 → ℝ) (x : E3)
      + (hs u ∩ hs w).indicator (1 : E3 → ℝ) (x : E3) + (hs (-u) ∩ hs (-w)).indicator (1 : E3 → ℝ) (x : E3)
      + (hs u ∩ hs v).indicator (1 : E3 → ℝ) (x : E3) + (hs (-u) ∩ hs (-v)).indicator (1 : E3 → ℝ) (x : E3)
      = (univ : Set E3).indicator (1 : E3 → ℝ) (x : E3) + 2 * (hs u ∩ hs v ∩ hs w).indicator (1 : E3 → ℝ) (x : E3)
        + 2 * (hs (-u) ∩ hs (-v) ∩ hs (-w)).indicator (1 : E3 → ℝ) (x : E3) := by
    filter_upwards [ae_ne_zero_inner hu, ae_ne_zero_inner hv, ae_ne_zero_inner hw] with x h1 h2 h3
    simp only [hs, inter_def, mem_ofPred_eq, inner_neg_right, Set.indicator, mem_univ, Pi.one_apply]
    rcases lt_or_gt_of_ne h1 with a | a <;> rcases lt_or_gt_of_ne h2 with b | b <;>
      rcases lt_or_gt_of_ne h3 with c | c <;> simp [a.le, b.le, c.le, not_le.mpr a, not_le.mpr b, not_le.mpr c] <;> norm_num
  exact integral_six (integrable_indicator_sph m1) (integrable_indicator_sph m2)
    (integrable_indicator_sph m3) (integrable_indicator_sph m4) (integrable_indicator_sph m5)
    (integrable_indicator_sph m6) (integrable_indicator_sph MeasurableSet.univ)
    (integrable_indicator_sph m7) (integrable_indicator_sph m8) key

/-- The unit normal-direction vector of the plane through `O`, `X`, `Y`, pointing to the side of `Z`:
the component of `Z` orthogonal to the span of `X` and `Y`. -/
noncomputable def sideNormal (X Y Z : E3) : E3 := Z - (Submodule.span ℝ {X, Y}).starProjection Z

theorem sideNormal_formula {A B C : E3} (hA : ‖A‖ = 1) (hb : sphTangent A B ≠ 0) :
    sideNormal A B C = sphTangent A C -
      (⟪sphTangent A C, sphTangent A B⟫ / ⟪sphTangent A B, sphTangent A B⟫) • sphTangent A B := by
  set tB := sphTangent A B with htB
  set tC := sphTangent A C with htC
  have hAA : ⟪A, A⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hA]; norm_num
  have hbpos : ⟪tB, tB⟫ ≠ 0 := by rwa [Ne, inner_self_eq_zero]
  have hBA : ⟪tB, A⟫ = 0 := inner_sphTangent_self hA
  have hCA : ⟪tC, A⟫ = 0 := inner_sphTangent_self hA
  have hAB : ⟪A, tB⟫ = 0 := by rw [real_inner_comm]; exact hBA
  have hAC : ⟪A, tC⟫ = 0 := by rw [real_inner_comm]; exact hCA
  set v := ⟪C, A⟫ • A + (⟪tC, tB⟫ / ⟪tB, tB⟫) • tB with hv
  have hCv : C - v = tC - (⟪tC, tB⟫ / ⟪tB, tB⟫) • tB := by
    rw [hv, htC, sphTangent]; module
  have hB : B = tB + ⟪B, A⟫ • A := by rw [htB, sphTangent]; module
  have hmemA : A ∈ Submodule.span ℝ ({A, B} : Set E3) := Submodule.subset_span (by simp)
  have hmemtB : tB ∈ Submodule.span ℝ ({A, B} : Set E3) := by
    rw [htB, sphTangent]
    exact Submodule.sub_mem _ (Submodule.subset_span (by simp)) (Submodule.smul_mem _ _ hmemA)
  have hvm : v ∈ Submodule.span ℝ ({A, B} : Set E3) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hmemA) (Submodule.smul_mem _ _ hmemtB)
  have hproj : (Submodule.span ℝ ({A, B} : Set E3)).starProjection C = v := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hvm
    intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hw
    have h1 : ⟪C - v, A⟫ = 0 := by
      rw [hCv, inner_sub_left, inner_smul_left, hCA, hBA]; simp
    have h2 : ⟪C - v, B⟫ = 0 := by
      have h3 : ⟪C - v, tB⟫ = 0 := by
        rw [hCv, inner_sub_left, inner_smul_left]
        simp only [RCLike.conj_to_real]
        field_simp
        ring
      have h4 : ⟪C - v, B⟫ = ⟪C - v, tB⟫ + ⟪B, A⟫ * ⟪C - v, A⟫ := by
        conv_lhs => rw [hB]
        rw [inner_add_right, inner_smul_right]
      rw [h4, h3, h1]; ring
    rw [inner_add_right, inner_smul_right, inner_smul_right, h1, h2]; simp
  rw [sideNormal, hproj, hCv]

theorem normals_angle_aux {tB tC : E3} (hD : ⟪tB, tC⟫ ^ 2 < ‖tB‖ ^ 2 * ‖tC‖ ^ 2) :
    (tB - (⟪tB, tC⟫ / ⟪tC, tC⟫) • tC ≠ 0) ∧ (tC - (⟪tC, tB⟫ / ⟪tB, tB⟫) • tB ≠ 0) ∧
    0 < angle tB tC ∧ angle tB tC < Real.pi ∧
    angle (tB - (⟪tB, tC⟫ / ⟪tC, tC⟫) • tC) (tC - (⟪tC, tB⟫ / ⟪tB, tB⟫) • tB) = Real.pi - angle tB tC := by
  set p := ⟪tB, tC⟫ with hp
  set β := ‖tB‖ with hβ
  set γ := ‖tC‖ with hγ
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg _
  have hβγ : 0 < β ^ 2 * γ ^ 2 := lt_of_le_of_lt hp2 hD
  have hβpos : 0 < β := by
    rcases (norm_nonneg tB).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← hβ] at h; rw [← h] at hβγ; simp at hβγ
  have hγpos : 0 < γ := by
    rcases (norm_nonneg tC).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← hγ] at h; rw [← h] at hβγ; simp at hβγ
  have hbb : ⟪tB, tB⟫ = β ^ 2 := real_inner_self_eq_norm_sq tB
  have hcc : ⟪tC, tC⟫ = γ ^ 2 := real_inner_self_eq_norm_sq tC
  have hcb : ⟪tC, tB⟫ = p := real_inner_comm _ _
  rw [hbb, hcc, hcb]
  set D := β ^ 2 * γ ^ 2 - p ^ 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  -- inner products of the normals
  have hnn : ⟪tB - (p / γ ^ 2) • tC, tC - (p / β ^ 2) • tB⟫ = p * (p ^ 2 - β ^ 2 * γ ^ 2) / (β ^ 2 * γ ^ 2) := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      hbb, hcc, hcb, ← hp]
    field_simp
    ring
  have hB2 : ⟪tB - (p / γ ^ 2) • tC, tB - (p / γ ^ 2) • tC⟫ = D / γ ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      hbb, hcc, hcb, ← hp]
    field_simp
    ring
  have hC2 : ⟪tC - (p / β ^ 2) • tB, tC - (p / β ^ 2) • tB⟫ = D / β ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      hbb, hcc, hcb, ← hp]
    field_simp
    ring
  have hnB : tB - (p / γ ^ 2) • tC ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hB2; have : 0 < D / γ ^ 2 := by positivity
    linarith
  have hnC : tC - (p / β ^ 2) • tB ≠ 0 := by
    intro h; rw [h, inner_zero_left] at hC2; have : 0 < D / β ^ 2 := by positivity
    linarith
  have hNB : ‖tB - (p / γ ^ 2) • tC‖ ^ 2 = D / γ ^ 2 := by rw [← real_inner_self_eq_norm_sq, hB2]
  have hNC : ‖tC - (p / β ^ 2) • tB‖ ^ 2 = D / β ^ 2 := by rw [← real_inner_self_eq_norm_sq, hC2]
  have hprod : ‖tB - (p / γ ^ 2) • tC‖ * ‖tC - (p / β ^ 2) • tB‖ = D / (β * γ) := by
    have h1 : (‖tB - (p / γ ^ 2) • tC‖ * ‖tC - (p / β ^ 2) • tB‖) ^ 2 = (D / (β * γ)) ^ 2 := by
      rw [mul_pow, hNB, hNC]; field_simp
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h1
  have hcosα : Real.cos (angle tB tC) = p / (β * γ) := by
    rw [InnerProductGeometry.cos_angle]
  have hlt1 : p / (β * γ) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg (β * γ - p), mul_pos hβpos hγpos]
  have hgt1 : -1 < p / (β * γ) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (β * γ + p), mul_pos hβpos hγpos]
  have hα0 : 0 < angle tB tC := by
    rcases (angle_nonneg tB tC).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, Real.cos_zero] at hcosα; linarith
  have hαπ : angle tB tC < Real.pi := by
    rcases (angle_le_pi tB tC).lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, Real.cos_pi] at hcosα; linarith
  refine ⟨hnB, hnC, hα0, hαπ, ?_⟩
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨by linarith, by linarith⟩
  rw [InnerProductGeometry.cos_angle, hnn, hprod, Real.cos_pi_sub, hcosα]
  have hDne : D ≠ 0 := hDpos.ne'
  have : (β * γ) ≠ 0 := by positivity
  have hD' : p ^ 2 - β ^ 2 * γ ^ 2 = -D := by rw [hDdef]; ring
  rw [hD']
  field_simp

theorem sphAngle_comm (A C B : E3) : sphAngle A C B = sphAngle B C A := angle_comm _ _

theorem sphArea_neg_hs_inter (v w : E3) : sphArea (hs (-v) ∩ hs (-w)) = sphArea (hs v ∩ hs w) := by
  have : hs (-v) ∩ hs (-w) = (fun x : E3 => -x) ⁻¹' (hs v ∩ hs w) := by
    ext x; simp [hs]
  rw [this]; exact sphArea_neg ((measurableSet_hs v).inter (measurableSet_hs w))

theorem sphArea_neg_hs_inter3 (u v w : E3) :
    sphArea (hs (-u) ∩ hs (-v) ∩ hs (-w)) = sphArea (hs u ∩ hs v ∩ hs w) := by
  have : hs (-u) ∩ hs (-v) ∩ hs (-w) = (fun x : E3 => -x) ⁻¹' (hs u ∩ hs v ∩ hs w) := by
    ext x; simp [hs]
  rw [this]
  exact sphArea_neg (((measurableSet_hs u).inter (measurableSet_hs v)).inter (measurableSet_hs w))

/-- Gram inequality for the tangents at a vertex of a nondegenerate spherical triangle. -/
theorem tangent_gram {A B C : E3} (hA : ‖A‖ = 1)
    (hind : ∀ x y z : ℝ, x • A + y • B + z • C = 0 → x = 0 ∧ y = 0 ∧ z = 0) :
    ⟪sphTangent A B, sphTangent A C⟫ ^ 2 < ‖sphTangent A B‖ ^ 2 * ‖sphTangent A C‖ ^ 2 := by
  have hB' : B = sphTangent A B + ⟪B, A⟫ • A := by rw [sphTangent]; module
  have hC' : C = sphTangent A C + ⟪C, A⟫ • A := by rw [sphTangent]; module
  generalize sphTangent A B = tB at *
  generalize sphTangent A C = tC at *
  have hb : tB ≠ 0 := by
    intro h
    have := hind (-⟪B, A⟫) 1 0 (by linear_combination (norm := module) hB' + h)
    simp at this
  have hbpos : 0 < ⟪tB, tB⟫ := real_inner_self_pos.mpr hb
  obtain ⟨w, hw⟩ : ∃ w, w = tC - (⟪tC, tB⟫ / ⟪tB, tB⟫) • tB := ⟨_, rfl⟩
  have hw0 : w ≠ 0 := by
    intro h
    have := hind (-⟪C, A⟫ + (⟪tC, tB⟫ / ⟪tB, tB⟫) * ⟪B, A⟫) (-(⟪tC, tB⟫ / ⟪tB, tB⟫)) 1
      (by linear_combination (norm := module) hC' + (-(⟪tC, tB⟫ / ⟪tB, tB⟫)) • hB' + h - hw)
    simp at this
  have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw0
  have hexp : ⟪w, w⟫ = ⟪tC, tC⟫ - ⟪tC, tB⟫ ^ 2 / ⟪tB, tB⟫ := by
    rw [hw]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm tC tB]
    field_simp
    ring
  rw [hexp, sub_pos, div_lt_iff₀ hbpos] at hww
  rw [← real_inner_self_eq_norm_sq tB, ← real_inner_self_eq_norm_sq tC, ← real_inner_comm tB tC]
  linarith

theorem vertex_normals {X P Q : E3} (hX : ‖X‖ = 1)
    (hind : ∀ x y z : ℝ, x • X + y • P + z • Q = 0 → x = 0 ∧ y = 0 ∧ z = 0) :
    sideNormal X Q P ≠ 0 ∧ sideNormal X P Q ≠ 0 ∧ 0 < sphAngle P X Q ∧ sphAngle P X Q < Real.pi ∧
    angle (sideNormal X Q P) (sideNormal X P Q) = Real.pi - sphAngle P X Q := by
  have hD := tangent_gram hX hind
  have hβ : sphTangent X P ≠ 0 := by
    intro h; rw [h] at hD; simp at hD
  have hγ : sphTangent X Q ≠ 0 := by
    intro h; rw [h] at hD; simp at hD
  rw [sideNormal_formula hX hγ, sideNormal_formula hX hβ]
  have := normals_angle_aux hD
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at *
  simpa [sphAngle, real_inner_self_eq_norm_sq] using this

/-- The closed half-sphere of the unit sphere bounded by the great circle `(XY)ₛ` and containing `Z`
(for `X`, `Y`, `Z` linearly independent): the points of the sphere on the side of `Z` of the plane `OXY`. -/
noncomputable def sphHalfOf (X Y Z : E3) : Set E3 := sphere (0 : E3) 1 ∩ hs (sideNormal X Y Z)

/-- The solid spherical triangle `▲ₛABC` (Petrunin, p. 132): the intersection of the three half-spheres,
the first bounded by `(AB)ₛ` and containing `C`, the second bounded by `(BC)ₛ` and containing `A`, the
third bounded by `(CA)ₛ` and containing `B`. -/
@[kb "petrunin2025" "Definition (solid spherical triangle), p. 132"]
noncomputable def solidSphTriangle (A B C : E3) : Set E3 := sphHalfOf A B C ∩ sphHalfOf B C A ∩ sphHalfOf C A B

/-- The arc `[AB]ₛ` of the great circle through the non-antipodal points `A`, `B` of the unit sphere: the
shorter arc, i.e. the points of the sphere in the cone spanned by `A` and `B`. -/
@[kb "petrunin2025" "Definition (spherical arc), p. 132"]
def sphArc {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A B : V) : Set V :=
  {x | ‖x‖ = 1 ∧ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • A + b • B}

/-- The spherical triangle `△ₛABC` (Petrunin, p. 132): the union of its three sides `[AB]ₛ`, `[BC]ₛ`,
`[CA]ₛ`. Its angles are `sphAngle B A C`, `sphAngle A B C`, `sphAngle A C B` (wave 1). -/
@[kb "petrunin2025" "Definition (spherical triangle), p. 132"]
def sphTriangle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (A B C : V) : Set V :=
  sphArc A B ∪ sphArc B C ∪ sphArc C A

/-- The sides of the triangle lie in the solid spherical triangle. -/
theorem sphTriangle_subset_solid {A B C : E3} (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1) :
    sphTriangle A B C ⊆ solidSphTriangle A B C := by
  have hmem : ∀ X Y Z : E3, sideNormal X Y Z ∈ (Submodule.span ℝ ({X, Y} : Set E3))ᗮ := fun X Y Z =>
    Submodule.sub_starProjection_mem_orthogonal Z
  have h1 : ∀ X Y Z : E3, ⟪X, sideNormal X Y Z⟫ = 0 ∧ ⟪Y, sideNormal X Y Z⟫ = 0 := by
    intro X Y Z
    have := (Submodule.mem_orthogonal _ _).mp (hmem X Y Z)
    exact ⟨this X (Submodule.subset_span (by simp)), this Y (Submodule.subset_span (by simp))⟩
  have h2 : ∀ X Y Z : E3, 0 ≤ ⟪Z, sideNormal X Y Z⟫ := by
    intro X Y Z
    have hp : (Submodule.span ℝ ({X, Y} : Set E3)).starProjection Z ∈ Submodule.span ℝ ({X, Y} : Set E3) :=
      Submodule.starProjection_apply_mem _ _
    have h0 : ⟪(Submodule.span ℝ ({X, Y} : Set E3)).starProjection Z, sideNormal X Y Z⟫ = 0 :=
      (Submodule.mem_orthogonal _ _).mp (hmem X Y Z) _ hp
    have h3 : Z = (Submodule.span ℝ ({X, Y} : Set E3)).starProjection Z + sideNormal X Y Z := by
      simp [sideNormal]
    have h4 : ⟪Z, sideNormal X Y Z⟫ = ⟪sideNormal X Y Z, sideNormal X Y Z⟫ := by
      nth_rewrite 1 [h3]
      rw [inner_add_left, h0, zero_add]
    rw [h4, real_inner_self_eq_norm_sq]
    positivity
  have key : ∀ (P Q n : E3) (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ ⟪P, n⟫ → 0 ≤ ⟪Q, n⟫ →
      0 ≤ ⟪a • P + b • Q, n⟫ := by
    intro P Q n a b ha hb hP hQ
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    positivity
  have hAC := h1 A B C
  have hBA := h1 B C A
  have hCB := h1 C A B
  have all : ∀ n, (n = sideNormal A B C ∨ n = sideNormal B C A ∨ n = sideNormal C A B) →
      0 ≤ ⟪A, n⟫ ∧ 0 ≤ ⟪B, n⟫ ∧ 0 ≤ ⟪C, n⟫ := by
    rintro n (rfl | rfl | rfl)
    · exact ⟨hAC.1.ge, hAC.2.ge, h2 A B C⟩
    · exact ⟨h2 B C A, hBA.1.ge, hBA.2.ge⟩
    · exact ⟨hCB.2.ge, h2 C A B, hCB.1.ge⟩
  have inSolid : ∀ x : E3, ‖x‖ = 1 → (∀ n, (n = sideNormal A B C ∨ n = sideNormal B C A ∨
      n = sideNormal C A B) → 0 ≤ ⟪x, n⟫) → x ∈ solidSphTriangle A B C := by
    intro x hx hn
    exact ⟨⟨⟨by simpa using hx, hn _ (Or.inl rfl)⟩, by simpa using hx, hn _ (Or.inr (Or.inl rfl))⟩,
      by simpa using hx, hn _ (Or.inr (Or.inr rfl))⟩
  rintro x ((⟨hx, a, b, ha, hb, rfl⟩ | ⟨hx, a, b, ha, hb, rfl⟩) | ⟨hx, a, b, ha, hb, rfl⟩)
  · exact inSolid _ hx fun n hn => key _ _ _ a b ha hb (all n hn).1 (all n hn).2.1
  · exact inSolid _ hx fun n hn => key _ _ _ a b ha hb (all n hn).2.1 (all n hn).2.2
  · exact inSolid _ hx fun n hn => key _ _ _ a b ha hb (all n hn).2.2 (all n hn).1

/-- **Girard's theorem** (Petrunin, Lemma 16.1): the area of a (nondegenerate) solid spherical triangle
`▲ₛABC` in the unit sphere of `ℝ³` equals `α + β + γ - π`, where `α`, `β`, `γ` are its angles at `A`, `B`,
`C`. Area is Mathlib's `Measure.toSphere` of Lebesgue measure (total area `4π`). Nondegenerate means `A`, `B`,
`C` linearly independent (this includes: no two vertices antipodal or equal, and the vertices not on one great
circle). -/
@[kb "petrunin2025" "Lemma 16.1, p. 132"]
theorem girard {A B C : E3} (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hind : LinearIndependent ℝ ![A, B, C]) :
    sphArea (solidSphTriangle A B C) =
      sphAngle B A C + sphAngle A B C + sphAngle A C B - Real.pi := by
  have hi : ∀ x y z : ℝ, x • A + y • B + z • C = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    have := Fintype.linearIndependent_iff.mp hind ![x, y, z] (by simpa [Fin.sum_univ_three] using h)
    exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2⟩
  have hiA : ∀ x y z : ℝ, x • A + y • B + z • C = 0 → x = 0 ∧ y = 0 ∧ z = 0 := hi
  have hiB : ∀ x y z : ℝ, x • B + y • C + z • A = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    have := hi z x y (by rw [← h]; abel)
    exact ⟨this.2.1, this.2.2, this.1⟩
  have hiC : ∀ x y z : ℝ, x • C + y • A + z • B = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    have := hi y z x (by rw [← h]; abel)
    exact ⟨this.2.2, this.1, this.2.1⟩
  -- vertex A: planes AB (normal nC) and AC (normal nB)
  obtain ⟨hnB0, hnC0, hα0, hαπ, hαn⟩ := vertex_normals hA (P := B) (Q := C) hiA
  obtain ⟨hnC0', hnA0, hβ0, hβπ, hβn⟩ := vertex_normals hB (P := C) (Q := A) hiB
  obtain ⟨hnA0', hnB0', hγ0, hγπ, hγn⟩ := vertex_normals hC (P := A) (Q := B) hiC
  set nA := sideNormal B C A with hnA
  set nB := sideNormal C A B with hnB
  set nC := sideNormal A B C with hnC
  have pair : ∀ X Y Z : E3, sideNormal X Y Z = sideNormal Y X Z := by
    intro X Y Z; simp only [sideNormal, Set.pair_comm X Y]
  -- identify the normals appearing at each vertex
  have e1 : sideNormal A C B = nB := by rw [hnB, pair]
  have e2 : sideNormal B A C = nC := by rw [hnC, pair]
  have e3 : sideNormal C B A = nA := by rw [hnA, pair]
  rw [e1] at hnB0 hαn
  rw [e2] at hnC0' hβn
  rw [e3] at hnA0' hγn
  -- areas of the three lunes
  have aA : sphArea (hs nB ∩ hs nC) = 2 * sphAngle B A C := by
    rw [sphArea_hs_inter hnB0 hnC0 (by rw [hαn]; linarith) (by rw [hαn]; linarith), hαn]; ring
  have aB : sphArea (hs nA ∩ hs nC) = 2 * sphAngle A B C := by
    rw [inter_comm, sphArea_hs_inter hnC0' hnA0 (by rw [hβn]; linarith) (by rw [hβn]; linarith), hβn,
      sphAngle_comm C B A]; ring
  have aC : sphArea (hs nA ∩ hs nB) = 2 * sphAngle A C B := by
    rw [sphArea_hs_inter hnA0' hnB0' (by rw [hγn]; linarith) (by rw [hγn]; linarith), hγn]; ring
  have six := six_lunes hnA0 hnB0' hnC0
  rw [sphArea_neg_hs_inter, sphArea_neg_hs_inter, sphArea_neg_hs_inter, sphArea_neg_hs_inter3,
    aA, aB, aC] at six
  have hsol : solidSphTriangle A B C = (hs nA ∩ hs nB ∩ hs nC) ∩ sphere (0 : E3) 1 := by
    ext x
    simp only [solidSphTriangle, sphHalfOf, mem_inter_iff]
    tauto
  rw [hsol, sphArea_inter_sphere]
  linarith

section GreatCircles

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The closed half-sphere of the unit sphere with pole `n`: the points `x` with `‖x‖ = 1`, `⟪x, n⟫ ≥ 0`
(Petrunin, p. 131; the half-spheres are the two sides of a great circle). -/
@[kb "petrunin2025" "Definition (half-spheres), p. 131"]
def sphHalf (n : V) : Set V := {x | ‖x‖ = 1 ∧ 0 ≤ ⟪x, n⟫}

/-- The open half-sphere with pole `n`. -/
@[kb "petrunin2025" "Definition (half-spheres), p. 131"]
def sphOpenHalf (n : V) : Set V := {x | ‖x‖ = 1 ∧ 0 < ⟪x, n⟫}

/-- The great circle of the unit sphere cut out by the plane through `O` orthogonal to `n`: the intersection
of the unit sphere with the plane `{x | ⟪x, n⟫ = 0}` through the origin (Petrunin, p. 131). -/
@[kb "petrunin2025" "Definition (great circle), p. 131"]
def sphGreatCircle (n : V) : Set V := {x | ‖x‖ = 1 ∧ ⟪x, n⟫ = 0}

/-- A great circle is the intersection of the unit sphere with a plane (linear subspace) through `O`. -/
theorem sphGreatCircle_eq_inter (n : V) :
    sphGreatCircle n = sphere (0 : V) 1 ∩ ((ℝ ∙ n)ᗮ : Submodule ℝ V) := by
  ext x
  simp [sphGreatCircle, Submodule.mem_orthogonal_singleton_iff_inner_left]

theorem sphHalf_inter_neg (n : V) : sphHalf n ∩ sphHalf (-n) = sphGreatCircle n := by
  ext x
  simp only [sphHalf, sphGreatCircle, mem_inter_iff, mem_ofPred_eq, inner_neg_right]
  constructor
  · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.ge⟩, h1, by linarith⟩

theorem sphHalf_union_neg (n : V) : sphHalf n ∪ sphHalf (-n) = sphere (0 : V) 1 := by
  ext x
  simp only [sphHalf, mem_union, mem_ofPred_eq, inner_neg_right, mem_sphere_iff_norm, sub_zero]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    rcases le_total 0 ⟪x, n⟫ with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, by linarith⟩

theorem sphOpenHalf_eq_diff (n : V) : sphOpenHalf n = sphHalf n \ sphGreatCircle n := by
  ext x
  simp only [sphOpenHalf, sphHalf, sphGreatCircle, mem_diff, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, fun h => h2.ne' h.2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, lt_of_le_of_ne h2 (fun h => h3 ⟨h1, h.symm⟩)⟩

/-- The antipode `-x` of a point of the great circle `sphGreatCircle n` lies on it, and `x ≠ -x`. -/
theorem neg_mem_sphGreatCircle {n x : V} (hx : x ∈ sphGreatCircle n) :
    -x ∈ sphGreatCircle n ∧ -x ≠ x := by
  refine ⟨⟨by simpa using hx.1, by simpa using hx.2⟩, fun h => ?_⟩
  have h0 : x = 0 := by
    have h2 : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [← h]; simp
    simpa using h2
  have := hx.1
  simp [h0] at this

/-- Antipodal points lie in opposite open half-spheres. -/
theorem neg_mem_sphOpenHalf {n x : V} (hx : x ∈ sphOpenHalf n) :
    -x ∈ sphOpenHalf (-n) ∧ -x ∉ sphHalf n := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨⟨by simpa using h1, by simpa using h2⟩, fun h => ?_⟩
  have := h.2
  simp at this
  linarith

/-- The great circle `sphGreatCircle n` is the boundary (in the unit sphere) of the closed half-sphere
`sphHalf n`, hence also of the opposite half-sphere `sphHalf (-n)`. -/
@[kb "petrunin2025" "Definition (great circle bounds half-spheres), p. 131"]
theorem frontier_sphHalf {n : V} (hn : n ≠ 0) :
    frontier (Subtype.val ⁻¹' sphHalf n : Set (sphere (0 : V) 1)) =
      Subtype.val ⁻¹' sphGreatCircle n := by
  have hset : (Subtype.val ⁻¹' sphHalf n : Set (sphere (0 : V) 1)) = {x : sphere (0 : V) 1 | 0 ≤ ⟪(x : V), n⟫} := by
    ext x
    have := mem_sphere_iff_norm.mp x.2
    simp [sphHalf, this]
  have hcont : Continuous fun x : sphere (0 : V) 1 => ⟪(x : V), n⟫ :=
    continuous_subtype_val.inner continuous_const
  have hclosed : IsClosed {x : sphere (0 : V) 1 | 0 ≤ ⟪(x : V), n⟫} :=
    isClosed_le continuous_const hcont
  rw [hset, frontier, hclosed.closure_eq]
  ext x
  have hxn : ‖(x : V)‖ = 1 := by simpa using mem_sphere_iff_norm.mp x.2
  simp only [mem_diff, mem_preimage, mem_ofPred_eq, sphGreatCircle]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hxn, ?_⟩
    by_contra hne
    have hpos : 0 < ⟪(x : V), n⟫ := lt_of_le_of_ne h1 (Ne.symm hne)
    apply h2
    have hopen : IsOpen {y : sphere (0 : V) 1 | 0 < ⟪(y : V), n⟫} := isOpen_lt continuous_const hcont
    have hsub : {y : sphere (0 : V) 1 | 0 < ⟪(y : V), n⟫} ⊆ {y : sphere (0 : V) 1 | 0 ≤ ⟪(y : V), n⟫} :=
      fun y hy => by simp only [mem_ofPred_eq] at hy ⊢; exact hy.le
    exact interior_maximal hsub hopen hpos
  · rintro ⟨_, h0⟩
    refine ⟨h0.ge, fun hint => ?_⟩
    have hnorm : ∀ ε : ℝ, ‖(x : V) - ε • n‖ ^ 2 = 1 + ε ^ 2 * ‖n‖ ^ 2 := by
      intro ε
      rw [norm_sub_sq_real, inner_smul_right, h0, norm_smul, hxn]
      simp [mul_pow]
    have hne : ∀ ε : ℝ, ‖(x : V) - ε • n‖ ≠ 0 := by
      intro ε h
      have := hnorm ε
      rw [h] at this
      nlinarith [sq_nonneg (ε * ‖n‖), sq_nonneg ‖n‖]
    let y : ℝ → V := fun ε => (‖(x : V) - ε • n‖)⁻¹ • ((x : V) - ε • n)
    have hy : ∀ ε, ‖y ε‖ = 1 := fun ε => norm_smul_inv_norm (norm_ne_zero_iff.mp (hne ε))
    have hcy : Continuous y := by
      apply Continuous.smul
      · exact Continuous.inv₀ (by fun_prop : Continuous fun ε : ℝ => ‖(x : V) - ε • n‖) hne
      · fun_prop
    have hlim : Filter.Tendsto y (nhdsWithin 0 (Set.Ioi 0)) (nhds (x : V)) := by
      have := (hcy.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [y, hxn] using this
    let ys : ℝ → sphere (0 : V) 1 := fun ε => ⟨y ε, by simpa using hy ε⟩
    have hlim' : Filter.Tendsto ys (nhdsWithin 0 (Set.Ioi 0)) (nhds x) :=
      tendsto_subtype_rng.mpr hlim
    have hnhds : {z : sphere (0 : V) 1 | 0 ≤ ⟪(z : V), n⟫} ∈ nhds x :=
      Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hint) (fun _ h => h)
    have hev := hlim'.eventually hnhds
    obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    have hin : ⟪y ε, n⟫ < 0 := by
      show ⟪(‖(x : V) - ε • n‖)⁻¹ • ((x : V) - ε • n), n⟫ < 0
      rw [inner_smul_left, inner_sub_left, inner_smul_left, h0, real_inner_self_eq_norm_sq]
      have : 0 < ‖(x : V) - ε • n‖ := lt_of_le_of_ne (norm_nonneg _) (hne ε).symm
      simp only [RCLike.conj_to_real]
      have : 0 < ‖(x : V) - ε • n‖⁻¹ * (ε * ‖n‖ ^ 2) := by positivity
      nlinarith
    exact absurd hε (not_le.mpr hin)

end GreatCircles

section SphereCharacterization

/-- `S` is a circle lying in the plane (linear subspace) `W`: the set of points of `W` at a positive
distance `r` from a point `c ∈ W`. -/
def IsCircleIn (W : Submodule ℝ E3) (S : Set E3) : Prop :=
  ∃ c ∈ W, ∃ r : ℝ, 0 < r ∧ S = {x | x ∈ W ∧ dist x c = r}

/-- **A plane meets a sphere in the empty set, a point or a circle** (Petrunin, Lemma 16.9, the easy
direction "sphere ⟹ every plane meets it in `∅`, a point or a circle"). The plane is any linear subspace
`W` (for instance a plane through the fixed point `O`, here the origin). The converse ("if every plane
through `O` meets `Σ` in `∅`, a point or a circle, and `Σ` has two points, then `Σ` is a sphere") is not
formalized. -/
@[kb "petrunin2025" "Lemma 16.9 (only if), p. 136"]
theorem plane_inter_sphere (c : E3) {R : ℝ} (hR : 0 ≤ R) (W : Submodule ℝ E3) :
    ((W : Set E3) ∩ sphere c R = ∅) ∨ (∃ p, (W : Set E3) ∩ sphere c R = {p}) ∨
      IsCircleIn W ((W : Set E3) ∩ sphere c R) := by
  set P := W.starProjection c with hP
  have hPW : P ∈ W := Submodule.starProjection_apply_mem _ _
  have horth : c - P ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal c
  have key : ∀ x ∈ W, ‖x - c‖ ^ 2 = ‖x - P‖ ^ 2 + ‖c - P‖ ^ 2 := by
    intro x hx
    have h0 : ⟪x - P, c - P⟫ = 0 := (Submodule.mem_orthogonal _ _).mp horth _ (W.sub_mem hx hPW)
    have : x - c = (x - P) - (c - P) := by abel
    rw [this, norm_sub_sq_real, h0]; ring
  set t := R ^ 2 - ‖c - P‖ ^ 2 with ht
  have hmem : ∀ x ∈ W, (x ∈ sphere c R ↔ ‖x - P‖ ^ 2 = t) := by
    intro x hx
    rw [mem_sphere_iff_norm, ht]
    constructor
    · intro h; have := key x hx; rw [h] at this; linarith
    · intro h
      have := key x hx
      have h2 : ‖x - c‖ ^ 2 = R ^ 2 := by linarith
      exact (sq_eq_sq₀ (norm_nonneg _) hR).mp h2
  rcases lt_trichotomy t 0 with h | h | h
  · left
    ext x
    simp only [mem_inter_iff, SetLike.mem_coe, mem_empty_iff_false, iff_false, not_and]
    intro hx hxs
    have := (hmem x hx).mp hxs
    nlinarith [sq_nonneg ‖x - P‖]
  · right; left
    refine ⟨P, ?_⟩
    ext x
    simp only [mem_inter_iff, SetLike.mem_coe, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxs⟩
      have := (hmem x hx).mp hxs
      rw [h] at this
      have : ‖x - P‖ = 0 := by nlinarith [norm_nonneg (x - P)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    · rintro rfl
      refine ⟨hPW, (hmem _ hPW).mpr ?_⟩
      rw [h]; simp
  · right; right
    refine ⟨P, hPW, Real.sqrt t, Real.sqrt_pos.mpr h, ?_⟩
    ext x
    simp only [mem_inter_iff, SetLike.mem_coe, mem_ofPred_eq, dist_eq_norm]
    constructor
    · rintro ⟨hx, hxs⟩
      refine ⟨hx, ?_⟩
      have := (hmem x hx).mp hxs
      rw [← Real.sqrt_sq (norm_nonneg (x - P)), this]
    · rintro ⟨hx, hxs⟩
      refine ⟨hx, (hmem x hx).mpr ?_⟩
      rw [hxs, Real.sq_sqrt h.le]

end SphereCharacterization

section Cones

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The circular cone (Petrunin, p. 136) with tip `T` over the circle with centre `c` and radius `r` lying in
the plane through `c` orthogonal to the unit vector `n`: the union of the segments `[T, x]`, `x` on the circle.
(The book works in `ℝ³`; nothing here needs the dimension. Use with `⟪T - c, n⟫ ≠ 0`, i.e. the tip is not
in the plane of the base.) -/
@[kb "petrunin2025" "Definition (circular cone), p. 136"]
def circularCone (T c n : V) (r : ℝ) : Set V :=
  {y | ∃ x : V, ∃ s : ℝ, ⟪x - c, n⟫ = 0 ∧ ‖x - c‖ = r ∧ 0 ≤ s ∧ s ≤ 1 ∧ y = T + s • (x - T)}

/-- The footpoint of the tip `T` on the plane through `c` orthogonal to the unit vector `n`. -/
def coneFoot (T c n : V) : V := T - ⟪T - c, n⟫ • n

/-- The cone is *right* if the footpoint of the tip on the base plane is the centre of the base circle
(Petrunin, p. 136); otherwise it is *oblique*. -/
@[kb "petrunin2025" "Definition (right and oblique cone), p. 136"]
def IsRightCone (T c n : V) : Prop := coneFoot T c n = c

/-- A plane meets a sphere in a circle: if the plane `{y | ⟪y, m⟫ = d}` is at distance less than `ρ` from the
centre `q` of the sphere of radius `ρ`, the intersection is a circle of positive radius in the plane. -/
theorem plane_inter_sphere_circle {m q : V} (hm : m ≠ 0) {ρ d : ℝ}
    (hρ : |d - ⟪q, m⟫| < ρ * ‖m‖) :
    ∃ (p : V) (ρ' : ℝ), 0 < ρ' ∧ ⟪p, m⟫ = d ∧
      ∀ y : V, (⟪y, m⟫ = d ∧ ‖y - q‖ = ρ) ↔ (⟪y, m⟫ = d ∧ ‖y - p‖ = ρ') := by
  have hmm : 0 < ⟪m, m⟫ := real_inner_self_pos.mpr hm
  have hmn : ‖m‖ ^ 2 = ⟪m, m⟫ := (real_inner_self_eq_norm_sq m).symm
  have hρpos : 0 ≤ ρ := by
    by_contra h
    push_neg at h
    have := abs_nonneg (d - ⟪q, m⟫)
    nlinarith [norm_nonneg m]
  set l := (d - ⟪q, m⟫) / ⟪m, m⟫ with hl
  have hlm : l * ⟪m, m⟫ = d - ⟪q, m⟫ := by rw [hl]; field_simp
  have hnorm : ‖l • m‖ ^ 2 = l ^ 2 * ⟪m, m⟫ := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hmn]
  have hlt : l ^ 2 * ⟪m, m⟫ < ρ ^ 2 := by
    have h1 : (d - ⟪q, m⟫) ^ 2 < (ρ * ‖m‖) ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_lt.mp hρ]) (abs_lt.mp hρ).2
      simpa using this
    have h2 : l ^ 2 * ⟪m, m⟫ = (d - ⟪q, m⟫) ^ 2 / ⟪m, m⟫ := by
      rw [hl]; field_simp
    rw [h2, div_lt_iff₀ hmm]
    nlinarith [mul_pow ρ ‖m‖ 2]
  refine ⟨q + l • m, Real.sqrt (ρ ^ 2 - l ^ 2 * ⟪m, m⟫), Real.sqrt_pos.mpr (by linarith), ?_, ?_⟩
  · rw [inner_add_left, inner_smul_left]; simp only [RCLike.conj_to_real]; linarith
  · intro y
    constructor <;> rintro ⟨hy, h⟩ <;> refine ⟨hy, ?_⟩
    · have key : ‖y - q‖ ^ 2 = ‖y - (q + l • m)‖ ^ 2 + l ^ 2 * ⟪m, m⟫ := by
        have h0 : ⟪y - (q + l • m), l • m⟫ = 0 := by
          rw [inner_smul_right, inner_sub_left, inner_add_left, inner_smul_left]
          simp only [RCLike.conj_to_real]
          have : ⟪y, m⟫ - (⟪q, m⟫ + l * ⟪m, m⟫) = 0 := by linarith
          rw [this]; ring
        have : y - q = (y - (q + l • m)) + l • m := by abel
        rw [this, norm_add_sq_real, h0, hnorm]; ring
      rw [← Real.sqrt_sq (norm_nonneg (y - (q + l • m)))]
      congr 1
      rw [h] at key
      linarith
    · have key : ‖y - q‖ ^ 2 = ‖y - (q + l • m)‖ ^ 2 + l ^ 2 * ⟪m, m⟫ := by
        have h0 : ⟪y - (q + l • m), l • m⟫ = 0 := by
          rw [inner_smul_right, inner_sub_left, inner_add_left, inner_smul_left]
          simp only [RCLike.conj_to_real]
          have : ⟪y, m⟫ - (⟪q, m⟫ + l * ⟪m, m⟫) = 0 := by linarith
          rw [this]; ring
        have : y - q = (y - (q + l • m)) + l • m := by abel
        rw [this, norm_add_sq_real, h0, hnorm]; ring
      have h2 : ‖y - (q + l • m)‖ ^ 2 = ρ ^ 2 - l ^ 2 * ⟪m, m⟫ := by
        rw [h, Real.sq_sqrt (by linarith)]
      rw [← sq_eq_sq₀ (norm_nonneg _) hρpos]
      linarith

/-- **An oblique circular cone has a circular plane section not parallel to the base** (Petrunin,
Exercise 16.11). For the cone with tip `T` over the circle (centre `c`, radius `r > 0`, plane orthogonal to the
unit vector `n`, tip off that plane) which is not right, there is a plane `{y | ⟪y, m⟫ = d}` whose normal `m` is
not parallel to `n` (so it is not parallel to the base) such that the intersection of the plane with the cone
is exactly a circle of positive radius `ρ` about a point `p` of the plane. (The plane meets the cone in the
intersection of the plane with the sphere on the segment from `T` to its footpoint on the base plane as
diameter.) -/
@[kb "petrunin2025" "Exercise 16.11, p. 136"]
theorem circularCone_oblique_section {T c n : V} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 < r)
    (hT : ⟪T - c, n⟫ ≠ 0) (hobl : ¬ IsRightCone T c n) :
    ∃ m : V, m - ⟪m, n⟫ • n ≠ 0 ∧ ∃ (d : ℝ) (p : V) (ρ : ℝ), 0 < ρ ∧ ⟪p, m⟫ = d ∧
      circularCone T c n r ∩ {y | ⟪y, m⟫ = d} = {y | ⟪y, m⟫ = d ∧ ‖y - p‖ = ρ} := by
  obtain ⟨a, ha⟩ : ∃ a, a = c - T := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α, α = ⟪a, n⟫ := ⟨_, rfl⟩
  have hnn : ⟪n, n⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hTc : ⟪T - c, n⟫ = -α := by
    rw [hα, ← inner_neg_left]; congr 1; rw [ha]; abel
  have hα0 : α ≠ 0 := by intro h; apply hT; rw [hTc, h]; simp
  obtain ⟨A, hA⟩ : ∃ A, A = ⟪a, a⟫ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = A - r ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : V, m = (2 * α) • a - κ • n := ⟨_, rfl⟩
  have hmn : ⟪m, n⟫ = 2 * α ^ 2 - κ := by
    rw [hm]; simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, ← hα, hnn]; ring
  have hma : ⟪m, a⟫ = 2 * α * A - κ * α := by
    rw [hm]; simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real, ← hA, real_inner_comm a n, ← hα]
  have hmm : ⟪m, m⟫ = 4 * α ^ 2 * r ^ 2 + κ ^ 2 := by
    rw [hm]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      ← hA, real_inner_comm a n, ← hα, hnn]
    rw [hκ] at *
    nlinarith [hκ]
  have hmpos : 0 < ⟪m, m⟫ := by rw [hmm]; positivity
  have hm0 : m ≠ 0 := fun h => by rw [h] at hmpos; simp at hmpos
  have hnotpar : m - ⟪m, n⟫ • n ≠ 0 := by
    have h1 : m - ⟪m, n⟫ • n = (2 * α) • (a - α • n) := by rw [hmn, hm]; module
    rw [h1]
    refine smul_ne_zero (by positivity) ?_
    intro h
    apply hobl
    have h' : c - T - α • n = 0 := by rw [← ha]; exact h
    unfold IsRightCone coneFoot
    rw [hTc, neg_smul, sub_neg_eq_add]
    linear_combination (norm := module) (-1 : ℝ) • h'
  have key : ∀ y : V, (y ∈ circularCone T c n r ∧ ⟪y, m⟫ = ⟪T, m⟫ + α ^ 3) ↔
      (⟪y, m⟫ = ⟪T, m⟫ + α ^ 3 ∧ ‖y - (T + (α / 2) • n)‖ = |α| / 2) := by
    intro y
    constructor
    · rintro ⟨⟨x, s, h1, h2, hs0, hs1, rfl⟩, hyp⟩
      refine ⟨hyp, ?_⟩
      obtain ⟨e, he⟩ : ∃ e, e = x - c := ⟨_, rfl⟩
      obtain ⟨z, hz⟩ : ∃ z, z = e + a := ⟨_, rfl⟩
      have hxT : x - T = z := by rw [hz, he, ha]; abel
      have he1 : ⟪e, n⟫ = 0 := by rw [he]; exact h1
      have he2 : ⟪e, e⟫ = r ^ 2 := by rw [real_inner_self_eq_norm_sq, he, h2]
      have hn1 : ⟪z, n⟫ = α := by rw [hz, inner_add_left, he1, ← hα]; ring
      have hea : ⟪z, a⟫ = ⟪e, a⟫ + A := by rw [hz, inner_add_left, ← hA]
      have hee : ⟪z, z⟫ = r ^ 2 + 2 * ⟪e, a⟫ + A := by
        rw [hz]; simp only [inner_add_left, inner_add_right, he2, ← hA, real_inner_comm e a]; ring
      have h4 : ⟪z, m⟫ = α * ⟪z, z⟫ := by
        rw [hm]
        simp only [inner_sub_right, inner_smul_right, hn1, hea, hee]
        rw [hκ]; ring
      rw [hxT] at hyp ⊢
      have h3 : ⟪T + s • z, m⟫ = ⟪T, m⟫ + s * ⟪z, m⟫ := by
        rw [inner_add_left, inner_smul_left]; simp
      rw [h3, h4] at hyp
      have hsN : s * ⟪z, z⟫ = α ^ 2 := by
        apply mul_left_cancel₀ hα0
        linear_combination hyp
      have hsq : ‖s • z - (α / 2) • n‖ ^ 2 = α ^ 2 / 4 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
          RCLike.conj_to_real, hn1, hnn, real_inner_comm z n]
        linear_combination s * hsN
      have e1 : T + s • z - (T + (α / 2) • n) = s • z - (α / 2) • n := by abel
      rw [e1]
      exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (by rw [hsq, div_pow, sq_abs]; ring)
    · rintro ⟨hyp, hsph⟩
      obtain ⟨w, hw⟩ : ∃ w, w = y - T := ⟨_, rfl⟩
      have hyw : y = T + w := by rw [hw]; abel
      have hwm : ⟪w, m⟫ = α ^ 3 := by
        have : ⟪y, m⟫ = ⟪T, m⟫ + ⟪w, m⟫ := by rw [hyw, inner_add_left]
        linarith
      have hsq : ‖w - (α / 2) • n‖ ^ 2 = α ^ 2 / 4 := by
        have e1 : y - (T + (α / 2) • n) = w - (α / 2) • n := by rw [hw]; abel
        rw [e1] at hsph
        rw [hsph, div_pow, sq_abs]; ring
      obtain ⟨b, hb⟩ : ∃ b, b = ⟪w, n⟫ := ⟨_, rfl⟩
      have hWW : ⟪w, w⟫ = α * b := by
        have : ‖w - (α / 2) • n‖ ^ 2 = ⟪w, w⟫ - α * b + α ^ 2 / 4 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
            RCLike.conj_to_real, ← hb, hnn, real_inner_comm w n]
          ring
        linarith
      have hw0 : w ≠ 0 := by
        intro h; rw [h] at hwm; simp at hwm; exact hα0 (by simpa using hwm.symm)
      have hWpos : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw0
      have hbα : 0 < b / α := by
        have : b / α = ⟪w, w⟫ / α ^ 2 := by rw [hWW]; field_simp
        rw [this]; positivity
      obtain ⟨s, hs⟩ : ∃ s, s = b / α := ⟨_, rfl⟩
      have hspos : 0 < s := hs ▸ hbα
      have hsb : b = s * α := by rw [hs]; field_simp
      have hWs : ⟪w, w⟫ = α ^ 2 * s := by rw [hWW, hsb]; ring
      have hs1 : s ≤ 1 := by
        have hcs : |b| ≤ ‖w‖ := by
          have := abs_real_inner_le_norm w n
          rwa [hn, mul_one, ← hb] at this
        have hW2 : ⟪w, w⟫ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
        have h1 : α ^ 2 * s ≤ |α| * ‖w‖ := by
          calc α ^ 2 * s = |α * b| := by rw [← hWs, hWW, abs_of_nonneg (by rw [← hWW]; positivity)]
            _ = |α| * |b| := abs_mul _ _
            _ ≤ |α| * ‖w‖ := by gcongr
        have h2 : ‖w‖ ^ 2 = α ^ 2 * s := by rw [← hW2, hWs]
        have hαabs : 0 < |α| := abs_pos.mpr hα0
        have h3 : ‖w‖ ≤ |α| := by
          have : ‖w‖ * ‖w‖ ≤ |α| * ‖w‖ := by nlinarith [sq_abs α]
          exact le_of_mul_le_mul_right this (norm_pos_iff.mpr hw0)
        have : α ^ 2 * s ≤ α ^ 2 := by
          rw [← h2, ← sq_abs α]; nlinarith [norm_nonneg w]
        nlinarith [sq_pos_of_ne_zero hα0]
      have hwa : 2 * α * ⟪w, a⟫ = α ^ 3 + κ * s * α := by
        have : ⟪w, m⟫ = 2 * α * ⟪w, a⟫ - κ * b := by
          rw [hm]; simp only [inner_sub_right, inner_smul_right, ← hb, ← hα]
        rw [hwm, hsb] at this
        linarith
      have hwa' : ⟪w, a⟫ = (α ^ 2 + κ * s) / 2 := by
        apply mul_left_cancel₀ hα0
        linear_combination (1 / 2 : ℝ) * hwa
      have hcone : ‖w - s • a‖ ^ 2 = s ^ 2 * r ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
          RCLike.conj_to_real, real_inner_comm w a, ← hA, hWs, hwa']
        rw [hκ]; ring
      refine ⟨⟨T + s⁻¹ • w, s, ?_, ?_, hspos.le, hs1, ?_⟩, hyp⟩
      · have : T + s⁻¹ • w - c = s⁻¹ • w - a := by rw [ha]; abel
        rw [this, inner_sub_left, inner_smul_left, ← hb, ← hα]
        simp only [RCLike.conj_to_real]
        rw [hsb]; field_simp; ring
      · have : T + s⁻¹ • w - c = s⁻¹ • (w - s • a) := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul, ha]; abel
        rw [this, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hspos]
        have : ‖w - s • a‖ = s * r := by
          rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), hcone]; ring
        rw [this]; field_simp
      · rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]; exact hyw
  have hρ : |(⟪T, m⟫ + α ^ 3) - ⟪T + (α / 2) • n, m⟫| < |α| / 2 * ‖m‖ := by
    have h1 : (⟪T, m⟫ + α ^ 3) - ⟪T + (α / 2) • n, m⟫ = α * κ / 2 := by
      rw [inner_add_left, inner_smul_left, real_inner_comm m n, hmn]
      simp only [RCLike.conj_to_real]; ring
    rw [h1, abs_div, abs_mul]
    have hmnorm : κ ^ 2 < ‖m‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq] at hmm
      rw [hmm]; nlinarith [mul_pos (sq_pos_of_ne_zero hα0) (pow_pos hr 2)]
    have : |κ| < ‖m‖ := abs_lt_of_sq_lt_sq hmnorm (norm_nonneg _)
    have hαabs : 0 < |α| := abs_pos.mpr hα0
    rw [abs_two]
    nlinarith
  obtain ⟨p, ρ', hρ', hp, hiff⟩ := plane_inter_sphere_circle hm0 hρ
  refine ⟨m, hnotpar, ⟪T, m⟫ + α ^ 3, p, ρ', hρ', hp, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq]
  rw [key y]
  have := hiff y
  simp only [add_sub_assoc] at *
  exact this
end Cones

section Stereographic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The derivative of an inversion with nonzero radius preserves (unoriented) angles between vectors. -/
theorem sph_angle_fderiv_inversion {c x : V} {R : ℝ} (hR : R ≠ 0) (hx : x ≠ c) (u v : V) :
    angle (fderiv ℝ (EuclideanGeometry.inversion c R) x u) (fderiv ℝ (EuclideanGeometry.inversion c R) x v) =
      angle u v := by
  rw [EuclideanGeometry.fderiv_inversion]
  have hk : 0 < (R / dist x c) ^ 2 := by
    have : dist x c ≠ 0 := dist_ne_zero.mpr hx
    positivity
  simp only [ContinuousLinearMap.smul_apply, LinearMap.smul_apply]
  rw [angle_smul_left_of_pos _ _ hk, angle_smul_right_of_pos _ _ hk]
  exact (Submodule.reflection (ℝ ∙ (x - c))ᗮ).toLinearIsometry.angle_map u v

/-- Inversion is conformal: if two differentiable curves meet at a point other than the centre, the images
under the inversion across a sphere of nonzero radius have tangent vectors at that point making the same
angle as the original tangent vectors. -/
theorem inversion_curves_angle {c : V} {R : ℝ} (hR : R ≠ 0) {γ δ : ℝ → V} {u v : V}
    (hγ : HasDerivAt γ u 0) (hδ : HasDerivAt δ v 0) (h0 : γ 0 = δ 0) (hne : γ 0 ≠ c) :
    ∃ u' v' : V, HasDerivAt (fun t => EuclideanGeometry.inversion c R (γ t)) u' 0 ∧
      HasDerivAt (fun t => EuclideanGeometry.inversion c R (δ t)) v' 0 ∧ angle u' v' = angle u v := by
  have h1 := (EuclideanGeometry.hasFDerivAt_inversion (c := c) (R := R) hne).comp_hasDerivAt 0 hγ
  have h2 := (EuclideanGeometry.hasFDerivAt_inversion (c := c) (R := R) (h0 ▸ hne)).comp_hasDerivAt 0 hδ
  rw [← h0] at h2
  refine ⟨_, _, h1, h2, ?_⟩
  have := sph_angle_fderiv_inversion (c := c) hR hne u v
  rw [(EuclideanGeometry.hasFDerivAt_inversion (c := c) (R := R) hne).fderiv] at this
  exact this

/-- **Stereographic projection preserves angles** (Petrunin, Exercise 16.6). Let `N` be a unit vector,
`S = -N` the south pole of the unit sphere and `Π` the plane through `O` orthogonal to `N`. The stereographic
projection `ξₛ : Σ → Π` is the restriction of the inversion across the sphere with centre `S` and radius
`√2` (wave 1: `stereographic_eq_inversion`). Consequently, for two curves `γ`, `δ` on the sphere that are
differentiable at a common point `P ≠ S`, the image curves are differentiable, lie in `Π` (tangent vectors
orthogonal to `N`), and their tangent vectors make the same angle as the tangent vectors of `γ` and `δ`.
(By the involutivity of the inversion the same holds for the inverse projection `Π → Σ`, which is covered by
`inversion_curves_angle`.) -/
@[kb "petrunin2025" "Exercise 16.6, p. 136"]
theorem stereographic_preserves_angles {N : V} (hN : ‖N‖ = 1) {γ δ : ℝ → V} {u v : V}
    (hγ : HasDerivAt γ u 0) (hδ : HasDerivAt δ v 0) (h0 : γ 0 = δ 0)
    (hγs : ∀ t, ‖γ t‖ = 1) (hδs : ∀ t, ‖δ t‖ = 1) (hS : γ 0 ≠ -N) :
    ∃ u' v' : V, HasDerivAt (fun t => EuclideanGeometry.inversion (-N) (Real.sqrt 2) (γ t)) u' 0 ∧
      HasDerivAt (fun t => EuclideanGeometry.inversion (-N) (Real.sqrt 2) (δ t)) v' 0 ∧
      ⟪u', N⟫ = 0 ∧ ⟪v', N⟫ = 0 ∧ angle u' v' = angle u v := by
  have hR : Real.sqrt 2 ≠ 0 := by positivity
  obtain ⟨u', v', h1, h2, ha⟩ := inversion_curves_angle (c := -N) hR hγ hδ h0 hS
  refine ⟨u', v', h1, h2, ?_, ?_, ha⟩
  · have hev : ∀ᶠ t in nhds (0 : ℝ), γ t ≠ -N :=
      hγ.continuousAt.eventually_ne hS
    have hd : HasDerivAt (fun t => ⟪EuclideanGeometry.inversion (-N) (Real.sqrt 2) (γ t), N⟫) ⟪u', N⟫ 0 :=
      h1.inner ℝ (hasDerivAt_const 0 N) |>.congr_deriv (by simp)
    have hz : HasDerivAt (fun t => ⟪EuclideanGeometry.inversion (-N) (Real.sqrt 2) (γ t), N⟫) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with t ht
      exact (stereographic_eq_inversion hN).1 (γ t) (hγs t) ht |>.1
    exact hd.unique hz
  · have hS' : δ 0 ≠ -N := h0 ▸ hS
    have hev : ∀ᶠ t in nhds (0 : ℝ), δ t ≠ -N :=
      hδ.continuousAt.eventually_ne hS'
    have hd : HasDerivAt (fun t => ⟪EuclideanGeometry.inversion (-N) (Real.sqrt 2) (δ t), N⟫) ⟪v', N⟫ 0 :=
      h2.inner ℝ (hasDerivAt_const 0 N) |>.congr_deriv (by simp)
    have hz : HasDerivAt (fun t => ⟪EuclideanGeometry.inversion (-N) (Real.sqrt 2) (δ t), N⟫) 0 0 := by
      refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with t ht
      exact (stereographic_eq_inversion hN).1 (δ t) (hδs t) ht |>.1
    exact hd.unique hz

end Stereographic

end UndergradKB.Geometry
