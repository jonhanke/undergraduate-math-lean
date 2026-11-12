import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Connected.PathConnected
import UndergradKB.Common.Attr

/-! # The topologist's sine curve (Morris, Remark 5.2.7)

A connected space need not be path-connected. The book's example is the subspace of the plane made of the graph of
`y = sin (1/x)` for `0 < x ≤ 1` together with the vertical segment `{0} × [-1, 1]`.

The proof is adapted from `Counterexamples/TopologistsSineCurve.lean` of Mathlib (Daniele Bolla, David Loeffler,
Apache 2.0), which treats the graph over all `x > 0`; that file is not part of the Mathlib library, and the book
restricts to `x ≤ 1`, so the argument is redone here for the book's set. -/

open Topology Filter Set Real

namespace UndergradKB.Topology.SineCurve

/-- The graph of `y = sin (1/x)` for `0 < x ≤ 1`. -/
noncomputable def S : Set (ℝ × ℝ) := (fun x ↦ (x, sin x⁻¹)) '' Ioc 0 1

/-- The vertical segment `{(0, y) : -1 ≤ y ≤ 1}`. -/
def Z : Set (ℝ × ℝ) := (fun y ↦ (0, y)) '' Icc (-1) 1

/-- The book's space `X = S ∪ Z` (Morris, Remark 5.2.7). -/
noncomputable def X : Set (ℝ × ℝ) := S ∪ Z

/-- Points `x` tending to `0` at which `sin (1/x)` takes a given value `y`. -/
noncomputable def xSeq (y : ℝ) (k : ℕ) := 1 / (arcsin y + (k + 1) * (2 * π))

lemma xSeq_pos (y : ℝ) (k : ℕ) : 0 < xSeq y k := by
  rw [xSeq, one_div_pos]
  nlinarith [pi_pos, neg_pi_div_two_le_arcsin y]

lemma xSeq_le_one (y : ℝ) (k : ℕ) : xSeq y k ≤ 1 := by
  rw [xSeq, div_le_one (by nlinarith [pi_pos, neg_pi_div_two_le_arcsin y])]
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  nlinarith [two_le_pi, neg_pi_div_two_le_arcsin y]

lemma sin_inv_xSeq {y : ℝ} (hy : y ∈ Icc (-1) 1) (k : ℕ) : sin (xSeq y k)⁻¹ = y := by
  simpa [xSeq, -Nat.cast_add, ← Nat.cast_succ] using sin_arcsin' hy

lemma xSeq_tendsto (y : ℝ) : Tendsto (xSeq y) atTop (𝓝 0) := by
  refine .comp (g := fun k : ℝ ↦ 1 / (arcsin y + (k + 1) * (2 * π))) ?_ tendsto_natCast_atTop_atTop
  simp only [div_eq_mul_inv, show 𝓝 0 = 𝓝 (1 * (0 : ℝ)) by simp]
  refine (tendsto_inv_atTop_zero.comp <| tendsto_atTop_add_const_left _ _ ?_).const_mul _
  exact (tendsto_atTop_add_const_right _ _ tendsto_id).atTop_mul_const (by positivity)

/-- The closure of the graph `S` is the book's space `X`. -/
lemma closure_S : closure S = X := by
  ext ⟨x, y⟩
  simp only [mem_closure_iff_seq_limit, Prod.tendsto_iff]
  constructor
  · rintro ⟨f, hf_mem, hf_lim⟩
    have x_nonneg : 0 ≤ x := by
      refine isClosed_Ici.mem_of_tendsto hf_lim.1 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa [← hy.2] using le_of_lt hy.1.1
    have x_le : x ≤ 1 := by
      refine isClosed_Iic.mem_of_tendsto hf_lim.1 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa [← hy.2] using hy.1.2
    rcases x_nonneg.eq_or_lt with rfl | h
    · right
      simp only [Z, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
      refine isClosed_Icc.mem_of_tendsto hf_lim.2 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa only [Function.comp_apply, ← hy.2] using sin_mem_Icc ..
    · refine .inl ⟨x, ⟨h, x_le⟩, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      have : ContinuousAt (fun x ↦ sin x⁻¹) x :=
        continuous_sin.continuousAt.comp <| continuousAt_inv₀ h.ne'
      refine tendsto_nhds_unique_of_forall (this.tendsto.comp hf_lim.1) hf_lim.2 fun n ↦ ?_
      obtain ⟨y, hy⟩ := hf_mem n
      simp [← hy.2]
  · rintro (hz | ⟨z, hz⟩)
    · exact ⟨_, fun _ ↦ hz, tendsto_const_nhds, tendsto_const_nhds⟩
    · simp only [Prod.mk.injEq] at hz
      rcases hz with ⟨hz, ⟨rfl, rfl⟩⟩
      refine ⟨fun n ↦ (xSeq z n, z), fun n ↦ ⟨_, ⟨xSeq_pos z n, xSeq_le_one z n⟩, ?_⟩,
        xSeq_tendsto z, tendsto_const_nhds⟩
      simpa using sin_inv_xSeq hz n

lemma isClosed_X : IsClosed X := by simpa only [← closure_S] using isClosed_closure

/-- The book's space `X` is connected (it is the closure of the connected graph `S`). -/
theorem isConnected_X : IsConnected X := by
  rw [← closure_S]
  refine (isConnected_Ioc zero_lt_one |>.image _ <| continuousOn_id.prodMk ?_).closure
  intro x hx
  exact (continuous_sin.continuousAt.comp (continuousAt_inv₀ hx.1.ne')).continuousWithinAt

lemma zero_mem_X : (0, 0) ∈ X := by
  refine .inr ⟨0, ⟨?_, ?_⟩, rfl⟩ <;> linarith

/-- The point `(1, sin 1)` of the graph. -/
noncomputable def w : ℝ × ℝ := (1, sin 1⁻¹)

lemma w_mem_X : w ∈ X := .inl ⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩

private lemma norm_ge_abs_snd {a b : ℝ} : |b| ≤ ‖(a, b)‖ := by simp

private lemma exists_unitInterval_gt {t₀ : unitInterval} (ht₀ : t₀ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
  let s₀ := (t₀ : ℝ)
  let s₁ := min (s₀ + δ / 2) 1
  have h_s₀_delta_pos : 0 ≤ s₀ + δ / 2 := add_nonneg t₀.2.1 (by positivity)
  have hs₁ : 0 ≤ s₁ := le_min h_s₀_delta_pos zero_le_one
  have hs₁' : s₁ ≤ 1 := min_le_right ..
  refine ⟨⟨s₁, hs₁, hs₁'⟩, lt_min ((lt_add_iff_pos_right _).mpr (half_pos hδ)) ht₀, ?_⟩
  have h_le : s₁ ≤ s₀ + δ / 2 := min_le_left _ _
  have h_ge : s₀ ≤ s₁ := le_min (by linarith) t₀.2.2
  rw [Subtype.dist_eq, dist_comm, dist_eq, abs_of_nonneg (by linarith)]
  linarith

private lemma mem_S_of_x_pos {p : ℝ × ℝ} (hx : 0 < p.1) (hT : p ∈ X) : p.2 = sin (p.1)⁻¹ := by
  obtain ⟨x, -, hx⟩ : p ∈ S := by
    cases hT with
    | inl hT => trivial
    | inr hZ => obtain ⟨y, ⟨-, rfl⟩⟩ := hZ; exact (lt_irrefl _ hx).elim
  simp [← hx]

lemma exists_mem_Ioc_of_y {y : ℝ} (hy : y ∈ Icc (-1) 1) {a : ℝ} (ha : 0 < a) :
    ∃ x ∈ Ioc 0 a, sin x⁻¹ = y := by
  obtain ⟨N, h_dist⟩ := (Metric.tendsto_nhds.mp (xSeq_tendsto y) (a / 2) (by positivity)).exists
  refine ⟨xSeq y N, ⟨xSeq_pos y N, ?_⟩, sin_inv_xSeq hy _⟩
  rw [dist_eq, sub_zero, abs_of_pos (xSeq_pos _ N)] at h_dist
  linarith

/-- The book's space `X` is not path-connected. -/
theorem not_isPathConnected_X : ¬ IsPathConnected X := by
  intro h_pathConn
  replace h_pathConn := h_pathConn.joinedIn (0, 0) zero_mem_X w w_mem_X
  let p := h_pathConn.somePath
  have xcoord_pathContinuous : Continuous fun t ↦ (p t).1 := continuous_fst.comp p.continuous
  let t₀ : unitInterval := sSup {t | (p t).1 = 0}
  have h_pt₀_x : (p t₀).1 = 0 :=
    (isClosed_singleton.preimage xcoord_pathContinuous).sSup_mem ⟨0, by aesop⟩
  obtain ⟨δ, hδ, ht⟩ : ∃ δ, 0 < δ ∧ ∀ t, dist t t₀ < δ → dist (p t) (p t₀) < 1 :=
    Metric.eventually_nhds_iff.mp <| Metric.tendsto_nhds.mp (p.continuousAt t₀) _ one_pos
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
    refine exists_unitInterval_gt (lt_of_le_of_ne (unitInterval.le_one t₀) fun ht₀' ↦ ?_) hδ
    have w_x_path : (p 1).1 = 1 := by rw [Path.target p, w]
    have x_eq_zero : (p 1).1 = 0 := by rwa [ht₀'] at h_pt₀_x
    linarith
  let a := (p t₁).1
  have ha : 0 < a := by
    obtain ⟨x, hxI, hx_eq⟩ : p t₁ ∈ S := by
      refine (h_pathConn.somePath_mem t₁).elim id fun ⟨y, hy⟩ ↦ ?_
      have : (p t₁).1 = 0 := by simp only [p, ← hy.2]
      exact ((show t₁ ≤ t₀ from le_sSup this).not_gt ht₁.1).elim
    have : a = x := by simp only [a, ← hx_eq]
    rw [this]
    exact hxI.1
  have intervalAZeroSubOfT₀T₁Xcoord : Icc 0 a ⊆ (fun t ↦ (p t).1) '' Icc t₀ t₁ :=
    (isPreconnected_Icc.image _ xcoord_pathContinuous.continuousOn).Icc_subset
      (show 0 ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₀, ⟨le_rfl, ht₁.1.le⟩, ‹_›⟩)
      (show a ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₁, ⟨ht₁.1.le, le_rfl⟩, rfl⟩)
  have exists_close {y : ℝ} (hy : y ∈ Icc (-1) 1) : ∃ t, dist t t₀ < δ ∧ (p t).2 = y := by
    obtain ⟨x, hx, hx'⟩ := exists_mem_Ioc_of_y hy ha
    obtain ⟨t, ht⟩ : ∃ t ∈ Icc t₀ t₁, (p t).1 = x := intervalAZeroSubOfT₀T₁Xcoord ⟨hx.1.le, hx.2⟩
    have hp : (p t).2 = sin (p t).1⁻¹ := mem_S_of_x_pos (ht.2 ▸ hx.1) (h_pathConn.somePath_mem t)
    refine ⟨t, ?_, by rw [← hx', hp, ht.2]⟩
    calc
    dist t t₀ ≤ dist t₁ t₀ := dist_right_le_of_mem_uIcc (Icc_subset_uIcc' ht.1)
    _ = dist t₀ t₁ := by rw [dist_comm]
    _ < δ := ht₁.2
  obtain ⟨x₁, hx₁, h_pathx₁⟩ : ∃ x₁, dist x₁ t₀ < δ ∧ (p x₁).2 = 1 := exists_close (by simp)
  obtain ⟨x₂, hx₂, h_pathx₂⟩ : ∃ x₂, dist x₂ t₀ < δ ∧ (p x₂).2 = -1 := exists_close (by simp)
  have : dist (p x₁) (p x₂) < 2 := by
    refine (dist_triangle_right _ _ (p t₀)).trans_lt ?_
    exact (add_lt_add (ht _ hx₁) (ht _ hx₂)).trans_eq (by norm_num)
  have := norm_ge_abs_snd.trans_lt this
  rw [h_pathx₁, h_pathx₂, abs_of_nonneg (by norm_num)] at this
  linarith

end SineCurve

/-- Morris, Topology Without Tears, Remark 5.2.7 (TP-088). The subspace
`{(x, sin (1/x)) : 0 < x ≤ 1} ∪ {(0, y) : -1 ≤ y ≤ 1}` of the plane is connected but not path-connected; so a
connected space need not be path-connected. -/
@[kb "morris2024" "Remark 5.2.7, p. 119"]
theorem sineCurve_connectedSpace_not_pathConnectedSpace :
    ConnectedSpace SineCurve.X ∧ ¬ PathConnectedSpace SineCurve.X :=
  ⟨isConnected_iff_connectedSpace.mp SineCurve.isConnected_X,
    fun h ↦ SineCurve.not_isPathConnected_X (isPathConnected_iff_pathConnectedSpace.mpr h)⟩

/-- Morris, Topology Without Tears, Remark 5.2.7 (TP-088), in the form: there is a connected topological space that
is not path-connected. -/
@[kb "morris2024" "Remark 5.2.7, p. 119"]
theorem exists_connectedSpace_not_pathConnectedSpace :
    ∃ (T : Type) (_ : TopologicalSpace T), ConnectedSpace T ∧ ¬ PathConnectedSpace T :=
  ⟨SineCurve.X, inferInstance, sineCurve_connectedSpace_not_pathConnectedSpace⟩

end UndergradKB.Topology
