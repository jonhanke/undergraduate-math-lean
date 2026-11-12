import UndergradKB.Geometry.NeutralParallels
import UndergradKB.Common.Attr

/-! # Neutral plane IX: large inradius (Petrunin, Theorem 11.16, (d) ⇒ (e))

For every neutral plane: if there are triangles of arbitrarily large inradius, some nondegenerate triangle has
zero defect.

Suppose no nondegenerate triangle has zero defect. Inside a triangle of inradius `≥ r` with interior point `I`,
one of the three angles at `I` is at least `2π/3` (they add up to `2π`); the foot `F` of the perpendicular from
`I` to the opposite side splits it, giving a right triangle `IFQ` with leg `IF ≥ r` and angle `≥ π/3` at `I`.
Cutting it gives right triangles with angle exactly `π/3` at `I` and any leg `x ≤ r`. **Halving:** the
perpendicular at the midpoint `M` of `[IF]` cuts off a triangle `IMK`, whose mirror image `FMK` sits in the rest,
so the defect of `IFQ` is at least twice the defect of `IMK` (Exercise 11.12). With leg `2ⁿ` the defect is at
least `2ⁿ` times the (positive) defect of the triangle with leg `1`, which exceeds `π` for large `n`: a
contradiction. -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-- In a right triangle `IFQ` (right angle at `F`), the perpendicular to `(IF)` at a point `F'` strictly between
`I` and `F` meets `[IQ]` at a point `Q'` strictly between `I` and `Q`. -/
theorem exists_perp_cut {I F Q F' : P} (hT : IsTriangle I F Q) (hr : N.uangle I F Q = π / 2)
    (hb : IsBetween I F' F) : ∃ Q', IsBetween I Q' Q ∧ Q' ≠ F' ∧ N.uangle I F' Q' = π / 2 := by
  obtain ⟨hIF, hFQ, hQI⟩ := hT
  have hF'I : F' ≠ I := hb.1
  have hF'F : F' ≠ F := hb.2.1
  have hnd : ¬ IsTriangle.Degenerate I F Q :=
    N.not_degenerate_of_uangle_eq_pi_div_two hIF (Ne.symm hFQ) hr
  have hQl : Q ∉ N.line I F := fun h => hnd ((N.degenerate_iff_mem_line hIF).2 h)
  obtain ⟨W, hWd, hWang⟩ := N.exists_angle_eq_pi_div_two (O := F') (A := I) (Ne.symm hF'I) one_pos
  have hWF' : W ≠ F' := by
    intro e
    rw [e, dist_self] at hWd
    exact zero_ne_one hWd
  have hrW : N.uangle I F' W = π / 2 :=
    N.uangle_of_angle_eq_coe (by positivity) (by linarith [Real.pi_pos]) hWang
  have hF'l : F' ∈ N.line I F := N.mem_line_of_isBetween hb
  have hlF'I : N.line F' I = N.line I F := N.line_eq_of_mem hIF hF'l (N.left_mem_line I F) hF'I
  have hlF'F : N.line F' F = N.line I F := N.line_eq_of_mem hIF hF'l (N.right_mem_line I F) hF'F
  have hlFI : N.line F I = N.line I F := N.line_comm F I
  set L := N.line F' W with hL
  have hLl : IsLine L := N.isLine_line (Ne.symm hWF')
  have hIL : I ∉ L := N.not_mem_line_of_perp (Ne.symm hF'I) hWF' hrW
  have hFL : F ∉ L := by
    intro hF
    apply hIL
    rw [hL, ← N.line_eq_of_mem (Ne.symm hWF') (N.left_mem_line F' W) hF hF'F, hlF'F]
    exact N.left_mem_line I F
  -- the two perpendiculars to `(IF)`, at `F'` and at `F`, are disjoint
  have r1 : N.uangle W F' F = π / 2 := by
    have hFm : F ∈ N.line F' I := by rw [hlF'I]; exact N.right_mem_line I F
    have := N.uangle_eq_pi_div_two_of_mem_line (Ne.symm hF'I) hWF' hrW hFm (Ne.symm hF'F)
    exact (N.uangle_comm hWF' (Ne.symm hF'F)).trans this
  have r2 : N.uangle Q F F' = π / 2 := by
    have hF'm : F' ∈ N.line F I := by rw [hlFI]; exact hF'l
    have := N.uangle_eq_pi_div_two_of_mem_line hIF (Ne.symm hFQ) hr hF'm hF'F
    exact (N.uangle_comm (Ne.symm hFQ) hF'F).trans this
  have hdisj : Disjoint L (N.line F Q) :=
    N.disjoint_of_perp_perp hF'F hWF' (Ne.symm hFQ) r1 r2
  have hQL : Q ∉ L := fun h => Set.disjoint_left.1 hdisj h (N.right_mem_line F Q)
  rcases N.pasch hLl hIL hFL hQL ⟨F', N.left_mem_line F' W, hb⟩ with ⟨Z, hZ, hZb⟩ | ⟨Z, hZ, hZb⟩
  · exact absurd (N.mem_line_of_isBetween hZb) (Set.disjoint_left.1 hdisj hZ)
  · have hZF' : Z ≠ F' := by
      intro e
      apply hQl
      have h1 : F' ∈ N.line I Q := by rw [← e]; exact N.mem_line_of_isBetween hZb
      have h2 : N.line I F' = N.line I Q := N.line_eq_of_mem hQI.symm (N.left_mem_line I Q) h1 hF'I.symm
      have h3 : N.line I F' = N.line I F := N.line_eq_of_mem hIF (N.left_mem_line I F) hF'l hF'I.symm
      rw [← h3, h2]
      exact N.right_mem_line I Q
    refine ⟨Z, hZb, hZF', ?_⟩
    have hrW' : N.uangle W F' I = π / 2 := (N.uangle_comm hWF' (Ne.symm hF'I)).trans hrW
    have := N.uangle_eq_pi_div_two_of_mem_line hWF' (Ne.symm hF'I) hrW' hZ hZF'
    exact (N.uangle_comm (Ne.symm hF'I) hZF').trans this

/-- **Halving.** The perpendicular at the midpoint `M` of the leg `[IF]` of a right triangle `IFQ` cuts off a
right triangle `IMK` with the same angle at `I`, and `2·defect(IMK) ≤ defect(IFQ)`. -/
theorem exists_half_right {I F Q : P} (hT : IsTriangle I F Q) (hr : N.uangle I F Q = π / 2) :
    ∃ M K : P, IsTriangle I M K ∧ N.uangle I M K = π / 2 ∧ N.uangle M I K = N.uangle F I Q ∧
      2 * dist I M = dist I F ∧ 2 * N.defect I M K ≤ N.defect I F Q := by
  obtain ⟨hIF, hFQ, hQI⟩ := hT
  have hnd : ¬ IsTriangle.Degenerate I F Q :=
    N.not_degenerate_of_uangle_eq_pi_div_two hIF (Ne.symm hFQ) hr
  obtain ⟨M, hb, hMM⟩ := N.exists_midpoint hIF
  obtain ⟨K, hbK, hKM, hrK⟩ := N.exists_perp_cut ⟨hIF, hFQ, hQI⟩ hr hb
  have hMI : M ≠ I := hb.1
  have hMF : M ≠ F := hb.2.1
  have hKI : K ≠ I := hbK.1
  have hKQ : K ≠ Q := hbK.2.1
  have hFl : F ∉ N.line I Q := by
    intro h
    apply hnd
    obtain ⟨L, hL, h1, h2, h3⟩ := (N.degenerate_iff_mem_line hQI.symm).2 h
    exact ⟨L, hL, h1, h3, h2⟩
  have hKl : K ∉ N.line I F := by
    intro h
    apply hnd
    have h1 : N.line I K = N.line I F := N.line_eq_of_mem hIF (N.left_mem_line I F) h hKI.symm
    have h2 : N.line I K = N.line I Q :=
      N.line_eq_of_mem hQI.symm (N.left_mem_line I Q) (N.mem_line_of_isBetween hbK) hKI.symm
    refine (N.degenerate_iff_mem_line hIF).2 ?_
    rw [← h1, h2]
    exact N.right_mem_line I Q
  have hFK : F ≠ K := fun e => hKl (e ▸ N.right_mem_line I F)
  refine ⟨M, K, ⟨hMI.symm, hKM.symm, hKI⟩, hrK, ?_, ?_, ?_⟩
  · rw [N.uangle_ray_left hIF.symm (N.isBetween_rays hb).1 hMI hKI,
      N.uangle_ray_right hIF.symm hQI (N.isBetween_rays hbK).1 hKI]
  · have := hb.dist_add
    rw [← hMM] at this
    linarith
  · -- the reflection across `(MK)` swaps `I` and `F`
    have hLl : IsLine (N.line M K) := N.isLine_line (Ne.symm hKM)
    have hrK' : N.uangle K M I = π / 2 := (N.uangle_comm hKM hMI.symm).trans hrK
    obtain ⟨hσb, hσd⟩ :=
      N.isBetween_lineRefl_of_perp hLl (N.right_mem_line M K) (N.left_mem_line M K) hKM hMI.symm hrK'
    have hσI : N.lineRefl hLl I = F := by
      rw [← N.pointRefl_eq_of_isBetween hσb hσd, N.pointRefl_eq_of_isBetween hb (by rw [← hMM, dist_comm])]
    have hσM : N.lineRefl hLl M = M := N.lineRefl_fix hLl (N.left_mem_line M K)
    have hσK : N.lineRefl hLl K = K := N.lineRefl_fix hLl (N.right_mem_line M K)
    have hmir := N.defect_isometryEquiv (N.lineRefl hLl) (A := I) (B := M) (C := K) ⟨hMI.symm, hKM.symm, hKI⟩
    rw [hσI, hσM, hσK] at hmir
    have d1 := N.defect_add (A := I) (B := Q) (D := K) (C := F) hbK hFl
    have d2 := N.defect_add (A := I) (B := F) (D := M) (C := K) hb hKl
    have p1 := N.defect_perm1 (A := I) (B := F) (C := Q) ⟨hIF, hFQ, hQI⟩
    have p2 := N.defect_perm1 (A := I) (B := F) (C := K) ⟨hIF, hFK, hKI⟩
    have p3 := N.defect_swap (A := F) (B := M) (C := K) ⟨hMF.symm, hKM.symm, hFK.symm⟩
    have n1 := N.defect_nonneg (A := K) (B := Q) (C := F) ⟨hKQ, hFQ.symm, hFK⟩
    linarith

private theorem sign_coe_of_pos {r : ℝ} (h0 : 0 < r) (h1 : r < π) : ((r : ℝ) : Real.Angle).sign = 1 := by
  have ht : ((r : ℝ) : Real.Angle).toReal = r := Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith, h1.le⟩
  have hne : ((r : ℝ) : Real.Angle) ≠ π := by
    intro e
    rw [e, Real.Angle.toReal_pi] at ht
    linarith
  rw [← Real.Angle.sign_toReal hne, ht, sign_pos h0]

private theorem sign_coe_of_neg {r : ℝ} (h0 : -π < r) (h1 : r < 0) : ((r : ℝ) : Real.Angle).sign = -1 := by
  have ht : ((r : ℝ) : Real.Angle).toReal = r :=
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨h0, by linarith [Real.pi_pos]⟩
  have hne : ((r : ℝ) : Real.Angle) ≠ π := by
    intro e
    rw [e, Real.Angle.toReal_pi] at ht
    linarith [Real.pi_pos]
  rw [← Real.Angle.sign_toReal hne, ht, sign_neg h1]

/-- The crossbar step: in a right triangle `IFQ` with `|∡FIQ| > π/3`, the half-line from `I` at angle `π/3` from
`[IF)` (on the side of `Q`) meets `[FQ]`. -/
private theorem exists_pi_div_three_cut {I F Q : P} (hT : IsTriangle I F Q) (hr : N.uangle I F Q = π / 2)
    (hα : π / 3 < N.uangle F I Q) :
    ∃ Q₁, IsTriangle I F Q₁ ∧ N.uangle I F Q₁ = π / 2 ∧ N.uangle F I Q₁ = π / 3 := by
  obtain ⟨hIF, hFQ, hQI⟩ := hT
  have hFI : F ≠ I := Ne.symm hIF
  have hnd : ¬ IsTriangle.Degenerate I F Q :=
    N.not_degenerate_of_uangle_eq_pi_div_two hIF (Ne.symm hFQ) hr
  have hnd' : ¬ IsTriangle.Degenerate F I Q := fun ⟨L, hL, h1, h2, h3⟩ => hnd ⟨L, hL, h2, h1, h3⟩
  have hlt : N.uangle F I Q < π / 2 := by
    have := N.uangle_add_uangle_lt_pi (A := I) (B := F) (C := Q) ⟨hIF, hFQ, hQI⟩ hnd
    rw [N.uangle_comm hQI hFI] at this
    linarith
  set t := (N.angle F I Q).toReal with ht
  have hut : N.uangle F I Q = |t| := rfl
  have hcoe : N.angle F I Q = ((t : ℝ) : Real.Angle) := (Real.Angle.coe_toReal _).symm
  have hsQ : ∀ φ : ℝ, ∀ X : P, X ≠ I → N.angle F I X = ((φ : ℝ) : Real.Angle) →
      N.angle X I Q = ((t - φ : ℝ) : Real.Angle) := by
    intro φ X hXI hX
    have h := N.axiomIIIb I F X Q hFI hXI hQI
    rw [hX, hcoe] at h
    rw [eq_sub_of_add_eq' h, Real.Angle.coe_sub]
  have finish : ∀ φ : ℝ, |φ| = π / 3 → ∀ X : P, X ≠ I → N.angle F I X = ((φ : ℝ) : Real.Angle) →
      (N.angle F I X).sign = (N.angle F I Q).sign → (N.angle X I Q).sign = (N.angle F I Q).sign →
      ∃ Q₁, IsTriangle I F Q₁ ∧ N.uangle I F Q₁ = π / 2 ∧ N.uangle F I Q₁ = π / 3 := by
    intro φ hφ X hXI hX h₁ h₂
    obtain ⟨Z, hZr, hZb⟩ := N.crossbar ⟨hFI, Ne.symm hQI, Ne.symm hFQ⟩ hnd' hXI h₁ h₂
    have hZI : Z ≠ I := by
      rintro rfl
      exact hnd' hZb.degenerate
    have hZF : Z ≠ F := hZb.1
    refine ⟨Z, ⟨hIF, Ne.symm hZF, hZI⟩, ?_, ?_⟩
    · have hQF : N.uangle Q F I = π / 2 := (N.uangle_comm (Ne.symm hFQ) hIF).trans hr
      have := N.uangle_eq_pi_div_two_of_mem_line (Ne.symm hFQ) hIF hQF (N.mem_line_of_isBetween hZb) hZF
      exact (N.uangle_comm hIF hZF).trans this
    · rw [N.uangle_ray_right hFI hXI hZr hZI, N.uangle_def, hX,
        Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith [abs_le.1 hφ.le, Real.pi_pos, neg_abs_le φ],
          by linarith [le_abs_self φ, Real.pi_pos]⟩]
      exact hφ
  rcases lt_or_gt_of_ne (show t ≠ 0 by
      intro h
      rw [hut, h, abs_zero] at hα
      linarith [Real.pi_pos]) with htn | htp
  · have habs : |t| = -t := abs_of_neg htn
    obtain ⟨X, hXI, hX, -⟩ := N.axiomIIIa I F hFI ((-(π / 3) : ℝ) : Real.Angle)
    have hs := hsQ _ X hXI hX
    have sQ : (N.angle F I Q).sign = -1 := by
      rw [hcoe]
      exact sign_coe_of_neg (by linarith) htn
    refine finish (-(π / 3)) (by rw [abs_neg, abs_of_pos (by positivity)]) X hXI hX ?_ ?_
    · rw [hX, sQ]
      exact sign_coe_of_neg (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    · rw [hs, sQ]
      exact sign_coe_of_neg (by linarith [Real.pi_pos]) (by linarith)
  · have habs : |t| = t := abs_of_pos htp
    obtain ⟨X, hXI, hX, -⟩ := N.axiomIIIa I F hFI (((π / 3) : ℝ) : Real.Angle)
    have hs := hsQ _ X hXI hX
    have sQ : (N.angle F I Q).sign = 1 := by
      rw [hcoe]
      exact sign_coe_of_pos htp (by linarith [Real.pi_pos])
    refine finish (π / 3) (abs_of_pos (by positivity)) X hXI hX ?_ ?_
    · rw [hX, sQ]
      exact sign_coe_of_pos (by positivity) (by linarith [Real.pi_pos])
    · rw [hs, sQ]
      exact sign_coe_of_pos (by linarith) (by linarith [Real.pi_pos])

/-- From a right triangle `IFQ` with `|∡FIQ| ≥ π/3` and leg `IF ≥ x > 0`: a right triangle with angle exactly
`π/3` at `I` and leg exactly `x`. -/
theorem exists_right_pi_div_three {I F Q : P} (hT : IsTriangle I F Q) (hr : N.uangle I F Q = π / 2)
    (hα : π / 3 ≤ N.uangle F I Q) {x : ℝ} (hx : 0 < x) (hxF : x ≤ dist I F) :
    ∃ F' Q', IsTriangle I F' Q' ∧ N.uangle I F' Q' = π / 2 ∧ N.uangle F' I Q' = π / 3 ∧ dist I F' = x := by
  have step1 : ∃ Q₁, IsTriangle I F Q₁ ∧ N.uangle I F Q₁ = π / 2 ∧ N.uangle F I Q₁ = π / 3 := by
    rcases hα.lt_or_eq with hlt | heq
    · exact N.exists_pi_div_three_cut hT hr hlt
    · exact ⟨Q, hT, hr, heq.symm⟩
  obtain ⟨Q₁, ⟨hIF, hFQ₁, hQ₁I⟩, hr₁, ha₁⟩ := step1
  rcases hxF.lt_or_eq with hlt | heq
  · set F' := N.linePt I F x with hF'
    have hd1 : dist I F' = x := by rw [hF', N.dist_left_linePt hIF, abs_of_pos hx]
    have hd2 : dist F' F = dist I F - x := by
      have := N.dist_linePt hIF x (dist I F)
      rw [N.linePt_dist hIF] at this
      rw [hF', this, abs_of_neg (by linarith)]
      ring
    have hF'I : F' ≠ I := by
      intro e
      rw [e, dist_self] at hd1
      linarith
    have hF'F : F' ≠ F := by
      intro e
      rw [e, dist_self] at hd2
      linarith
    have hb : IsBetween I F' F :=
      N.isBetween_of_mem_line hIF (N.linePt_mem_line I F x) hF'I hF'F (by rw [hd1]; exact hlt)
        (by rw [hd2]; linarith)
    obtain ⟨Q', hbQ, hQ'F', hrQ⟩ := N.exists_perp_cut ⟨hIF, hFQ₁, hQ₁I⟩ hr₁ hb
    have hQ'I : Q' ≠ I := hbQ.1
    refine ⟨F', Q', ⟨Ne.symm hF'I, Ne.symm hQ'F', hQ'I⟩, hrQ, ?_, hd1⟩
    rw [N.uangle_ray_left (Ne.symm hIF) (N.isBetween_rays hb).1 hF'I hQ'I,
      N.uangle_ray_right (Ne.symm hIF) hQ₁I (N.isBetween_rays hbQ).1 hQ'I]
    exact ha₁
  · exact ⟨F, Q₁, ⟨hIF, hFQ₁, hQ₁I⟩, hr₁, ha₁, heq.symm⟩

/-- At an interior point `I` of a triangle `ABC` the three angles add up to `2π`, so one of them is at least
`2π/3`. -/
theorem exists_uangle_ge_of_interior {A B C I : P} (h : N.InteriorPoint A B C I) (hA : A ≠ I) (hB : B ≠ I)
    (hC : C ≠ I) :
    2 * π / 3 ≤ N.uangle A I B ∨ 2 * π / 3 ≤ N.uangle B I C ∨ 2 * π / 3 ≤ N.uangle C I A := by
  obtain ⟨h1, h2, h0⟩ := h
  have hsum : N.angle A I B + N.angle B I C + N.angle C I A = 0 := by
    rw [N.axiomIIIb I A B C hA hB hC, N.axiomIIIb I A C A hA hC hA, N.angle_self hA]
  set x := (N.angle A I B).toReal with hx
  set y := (N.angle B I C).toReal with hy
  set z := (N.angle C I A).toReal with hz
  have hc : ((x + y + z : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add, hx, hy, hz, Real.Angle.coe_toReal, Real.Angle.coe_toReal,
      Real.Angle.coe_toReal]
    exact hsum
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.1 hc
  rw [zsmul_eq_mul] at hn
  have nπ : ∀ θ : Real.Angle, θ.sign ≠ 0 → θ ≠ π := fun θ h e => h (by rw [e, Real.Angle.sign_coe_pi])
  have sx : SignType.sign x = (N.angle A I B).sign := Real.Angle.sign_toReal (nπ _ h0)
  have sy : SignType.sign y = (N.angle B I C).sign := Real.Angle.sign_toReal (nπ _ (h1 ▸ h0))
  have sz : SignType.sign z = (N.angle C I A).sign := Real.Angle.sign_toReal (nπ _ (h2 ▸ h1 ▸ h0))
  have bx := Real.Angle.toReal_le_pi (N.angle A I B)
  have by' := Real.Angle.toReal_le_pi (N.angle B I C)
  have bz := Real.Angle.toReal_le_pi (N.angle C I A)
  have cx := Real.Angle.neg_pi_lt_toReal (N.angle A I B)
  have cy := Real.Angle.neg_pi_lt_toReal (N.angle B I C)
  have cz := Real.Angle.neg_pi_lt_toReal (N.angle C I A)
  have hpi := Real.pi_pos
  have key : |x| + |y| + |z| = 2 * π := by
    rcases lt_trichotomy x 0 with hxn | hx0 | hxp
    · have e : (N.angle A I B).sign = -1 := by rw [← sx]; exact sign_neg hxn
      have hyn : y < 0 := sign_eq_neg_one_iff.1 (by rw [sy, ← h1, e])
      have hzn : z < 0 := sign_eq_neg_one_iff.1 (by rw [sz, ← h2, ← h1, e])
      have hn1 : (n : ℝ) < 0 := by nlinarith
      have hn2 : (-2 : ℝ) < n := by nlinarith
      have hn' : n = -1 := by
        have a : n < 0 := by exact_mod_cast hn1
        have b : -2 < n := by exact_mod_cast hn2
        omega
      rw [hn'] at hn
      push_cast at hn
      rw [abs_of_neg hxn, abs_of_neg hyn, abs_of_neg hzn]
      linarith
    · exfalso
      apply h0
      rw [← sx, hx0, sign_zero]
    · have e : (N.angle A I B).sign = 1 := by rw [← sx]; exact sign_pos hxp
      have hyp : 0 < y := sign_eq_one_iff.1 (by rw [sy, ← h1, e])
      have hzp : 0 < z := sign_eq_one_iff.1 (by rw [sz, ← h2, ← h1, e])
      have hn1 : (0 : ℝ) < n := by nlinarith
      have hn2 : (n : ℝ) < 2 := by nlinarith
      have hn' : n = 1 := by
        have a : 0 < n := by exact_mod_cast hn1
        have b : n < 2 := by exact_mod_cast hn2
        omega
      rw [hn'] at hn
      push_cast at hn
      rw [abs_of_pos hxp, abs_of_pos hyp, abs_of_pos hzp]
      linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  have : N.uangle A I B + N.uangle B I C + N.uangle C I A = |x| + |y| + |z| := rfl
  linarith

private theorem big_right_of_side {I P₁ P₂ : P} {r : ℝ} (hr : 0 < r) (h12 : P₁ ≠ P₂)
    (hd : ∀ X ∈ N.line P₁ P₂, r ≤ dist I X) (hge : 2 * π / 3 ≤ N.uangle P₁ I P₂) :
    ∃ F Q, IsTriangle I F Q ∧ N.uangle I F Q = π / 2 ∧ π / 3 ≤ N.uangle F I Q ∧ r ≤ dist I F := by
  have hI : I ∉ N.line P₁ P₂ := fun h => by
    have := hd I h
    rw [dist_self] at this
    linarith
  have hP₁ : P₁ ≠ I := fun e => hI (e ▸ N.left_mem_line P₁ P₂)
  have hP₂ : P₂ ≠ I := fun e => hI (e ▸ N.right_mem_line P₁ P₂)
  obtain ⟨F, hF, hFr⟩ := N.exists_foot (N.isLine_line h12) hI
  have hFI : F ≠ I := fun e => hI (e ▸ hF)
  have hdF := hd F hF
  have hle := N.uangle_le_add (A := P₁) (B := P₂) (X := F) (O := I) hP₁ hP₂ hFI
  by_cases h2 : π / 3 ≤ N.uangle F I P₂
  · have hP₂F : P₂ ≠ F := by
      rintro rfl
      rw [N.uangle_def, N.angle_self hFI, Real.Angle.toReal_zero, abs_zero] at h2
      linarith [Real.pi_pos]
    exact ⟨F, P₂, ⟨Ne.symm hFI, Ne.symm hP₂F, hP₂⟩, hFr P₂ (N.right_mem_line P₁ P₂) hP₂F, h2, hdF⟩
  · have h1 : π / 3 ≤ N.uangle P₁ I F := by
      push Not at h2
      linarith
    have hP₁F : P₁ ≠ F := by
      rintro rfl
      rw [N.uangle_def, N.angle_self hP₁, Real.Angle.toReal_zero, abs_zero] at h1
      linarith [Real.pi_pos]
    refine ⟨F, P₁, ⟨Ne.symm hFI, Ne.symm hP₁F, hP₁⟩, hFr P₁ (N.left_mem_line P₁ P₂) hP₁F, ?_, hdF⟩
    rw [N.uangle_comm hFI hP₁]
    exact h1

/-- A triangle with inradius `≥ r > 0` contains a right triangle with leg `≥ r` and angle `≥ π/3` next to it. -/
theorem exists_big_right {A B C : P} {r : ℝ} (hr : 0 < r) (hT : IsTriangle A B C) (h : N.InradiusGE A B C r) :
    ∃ I F Q, IsTriangle I F Q ∧ N.uangle I F Q = π / 2 ∧ π / 3 ≤ N.uangle F I Q ∧ r ≤ dist I F := by
  obtain ⟨hAB, hBC, hCA⟩ := hT
  obtain ⟨I, hint, hd⟩ := h
  have dAB : ∀ X ∈ N.line A B, r ≤ dist I X :=
    hd _ (N.isLine_line hAB) (Or.inl ⟨N.left_mem_line A B, N.right_mem_line A B⟩)
  have dBC : ∀ X ∈ N.line B C, r ≤ dist I X :=
    hd _ (N.isLine_line hBC) (Or.inr (Or.inl ⟨N.left_mem_line B C, N.right_mem_line B C⟩))
  have dCA : ∀ X ∈ N.line C A, r ≤ dist I X :=
    hd _ (N.isLine_line hCA) (Or.inr (Or.inr ⟨N.left_mem_line C A, N.right_mem_line C A⟩))
  have hAI : A ≠ I := fun e => by
    have := dAB A (N.left_mem_line A B)
    rw [e, dist_self] at this
    linarith
  have hBI : B ≠ I := fun e => by
    have := dBC B (N.left_mem_line B C)
    rw [e, dist_self] at this
    linarith
  have hCI : C ≠ I := fun e => by
    have := dCA C (N.left_mem_line C A)
    rw [e, dist_self] at this
    linarith
  rcases N.exists_uangle_ge_of_interior hint hAI hBI hCI with h | h | h
  · obtain ⟨F, Q, hh⟩ := N.big_right_of_side hr hAB dAB h
    exact ⟨I, F, Q, hh⟩
  · obtain ⟨F, Q, hh⟩ := N.big_right_of_side hr hBC dBC h
    exact ⟨I, F, Q, hh⟩
  · obtain ⟨F, Q, hh⟩ := N.big_right_of_side hr hCA dCA h
    exact ⟨I, F, Q, hh⟩

/-- **Doubling.** Right triangles with angle `π/3` at `I`: the one with leg `2ⁿ·x₀` has at least `2ⁿ` times
the defect of the one with leg `x₀`. -/
theorem defect_ge_of_right {I₀ F₀ Q₀ : P} (h₀ : IsTriangle I₀ F₀ Q₀) (r₀ : N.uangle I₀ F₀ Q₀ = π / 2)
    (a₀ : N.uangle F₀ I₀ Q₀ = π / 3) :
    ∀ n : ℕ, ∀ I F Q : P, IsTriangle I F Q → N.uangle I F Q = π / 2 → N.uangle F I Q = π / 3 →
      dist I F = 2 ^ n * dist I₀ F₀ → 2 ^ n * N.defect I₀ F₀ Q₀ ≤ N.defect I F Q := by
  intro n
  induction n with
  | zero =>
    intro I F Q hT hr ha hd
    have hnd : ¬ IsTriangle.Degenerate I F Q :=
      N.not_degenerate_of_uangle_eq_pi_div_two hT.1 (Ne.symm hT.2.1) hr
    have hc := N.asa h₀ hT hnd (by rw [hd, pow_zero, one_mul]) (by rw [r₀, hr])
      (by rw [N.uangle_comm h₀.2.2 (Ne.symm h₀.1), a₀, N.uangle_comm hT.2.2 (Ne.symm hT.1), ha])
    rw [N.defect_congruent h₀ hc, pow_zero, one_mul]
  | succ n ih =>
    intro I F Q hT hr ha hd
    obtain ⟨M, K, hT', hr', ha', hd', hdef⟩ := N.exists_half_right hT hr
    have := ih I M K hT' hr' (ha'.trans ha) (by rw [pow_succ] at hd; linarith)
    rw [pow_succ]
    linarith

/-- **(d) ⇒ (e).** If there are triangles of arbitrarily large inradius, some nondegenerate triangle has zero
defect. -/
theorem zeroDefectTriangle_of_arbitrarilyLargeInradius (h : N.ArbitrarilyLargeInradius) :
    N.ZeroDefectTriangle := by
  by_contra hne
  have hpos : ∀ A B C : P, IsTriangle A B C → ¬ IsTriangle.Degenerate A B C → 0 < N.defect A B C :=
    fun A B C hT hnd => lt_of_le_of_ne (N.defect_nonneg hT) fun e => hne ⟨A, B, C, hT, hnd, e.symm⟩
  have big : ∀ r : ℝ, 0 < r → ∃ I F Q, IsTriangle I F Q ∧ N.uangle I F Q = π / 2 ∧
      π / 3 ≤ N.uangle F I Q ∧ r ≤ dist I F := fun r hr => by
    obtain ⟨A, B, C, hT, -, hin⟩ := h r
    exact N.exists_big_right hr hT hin
  obtain ⟨I, F, Q, hT, hr, hα, hd⟩ := big 1 one_pos
  obtain ⟨F₀, Q₀, h₀, r₀, a₀, d₀⟩ := N.exists_right_pi_div_three hT hr hα one_pos hd
  have hδ : 0 < N.defect I F₀ Q₀ :=
    hpos _ _ _ h₀ (N.not_degenerate_of_uangle_eq_pi_div_two h₀.1 (Ne.symm h₀.2.1) r₀)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (π / N.defect I F₀ Q₀) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨I', F', Q', hT', hr', hα', hd'⟩ := big (2 ^ n) (by positivity)
  obtain ⟨F₁, Q₁, h₁, r₁, a₁, d₁⟩ := N.exists_right_pi_div_three hT' hr' hα' (by positivity) hd'
  have hge := N.defect_ge_of_right h₀ r₀ a₀ n I' F₁ Q₁ h₁ r₁ a₁ (by rw [d₁, d₀, mul_one])
  have hle : N.defect I' F₁ Q₁ ≤ π := by
    unfold NeutralPlane.defect
    linarith [N.uangle_nonneg I' F₁ Q₁, N.uangle_nonneg F₁ Q₁ I', N.uangle_nonneg Q₁ I' F₁]
  rw [div_lt_iff₀ hδ] at hn
  linarith

/-- **(d) ⇒ `Z`.** -/
theorem allZeroDefect_of_arbitrarilyLargeInradius (h : N.ArbitrarilyLargeInradius) : N.AllZeroDefect :=
  N.allZeroDefect_of_hasRectangle
    (N.hasRectangle_of_zeroDefectTriangle (N.zeroDefectTriangle_of_arbitrarilyLargeInradius h))

end NeutralPlane

end Neutral

end UndergradKB.Geometry
