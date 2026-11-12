import UndergradKB.Geometry.NeutralParallels
import UndergradKB.Common.Attr

/-! # Neutral plane VII: zero defect gives Axiom V (Petrunin, Theorem 11.16, the implication to Axiom V)

Let `Z` be the statement that every triangle has zero defect (`NeutralPlane.AllZeroDefect`). We prove that `Z`
implies Axiom V, for every neutral plane. The tool is the oriented angle: under `Z` the three oriented angles of
every triangle add up to `π` in `Real.Angle` (`angle_add_angle_add_angle_of_allZeroDefect`), so that
configurations are handled by algebra in `Real.Angle` and Axiom IIIb, without case distinctions on the position of
the points.

Plan. Fix a nondegenerate triangle `ABC`, `α = ∡BAC`, `β = ∡ABC`. For `B' ∈ [AB)`, `B' ≠ A`, there is a unique
point `C' ∈ [AC)` with `∡AB'C' = β` (existence by the intermediate value theorem along `[AC)`, using Legendre's
`exists_uangle_lt`; uniqueness by Proposition 2.2). The functions `x ↦ AC'` and `x ↦ B'C'` of `x = AB'` are
additive (the reflection across the midpoint of `[B' C'']` turns a decomposition of a big equiangular triangle into
two smaller ones), positive, hence linear (`eq_mul_of_additive_of_pos`). This is the proportionality (Thales)
theorem; Axiom V follows, the degenerate triangles being handled on a line. -/

namespace UndergradKB.Geometry

open Real

/-- A positive additive function on the positive reals is linear. -/
theorem eq_mul_of_additive_of_pos {f : ℝ → ℝ} (hadd : ∀ x y, 0 < x → 0 < y → f (x + y) = f x + f y)
    (hpos : ∀ x, 0 < x → 0 < f x) {x : ℝ} (hx : 0 < x) : f x = f 1 * x := by
  have hmono : ∀ a b, 0 < a → a < b → f a < f b := by
    intro a b ha hab
    have h1 := hadd a (b - a) ha (by linarith)
    have h2 := hpos (b - a) (by linarith)
    rw [show a + (b - a) = b by ring] at h1
    linarith
  have hnat : ∀ n : ℕ, 0 < n → ∀ y : ℝ, 0 < y → f (n * y) = n * f y := by
    intro n hn y hy
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : ((n + 1 : ℕ) : ℝ) * y = n * y + y := by push_cast; ring
      rw [h1, hadd _ _ (by positivity) hy, ih]
      push_cast; ring
  have hq : ∀ q : ℚ, 0 < q → f (q : ℝ) = q * f 1 := by
    intro q hq
    obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (Rat.num_pos.2 hq).le
    have hp0 : 0 < p := by
      have := Rat.num_pos.2 hq
      rw [hp] at this
      exact_mod_cast this
    have hd : 0 < q.den := q.den_pos
    have hd' : (0 : ℝ) < q.den := by exact_mod_cast hd
    have hqe : (q : ℝ) = p * (1 / (q.den : ℝ)) := by
      rw [Rat.cast_def, hp]; push_cast; ring
    have h1 : f 1 = q.den * f (1 / (q.den : ℝ)) := by
      have := hnat q.den hd (1 / (q.den : ℝ)) (by positivity)
      rwa [mul_one_div_cancel hd'.ne'] at this
    rw [hqe, hnat p hp0 _ (by positivity)]
    have h2 : f (1 / (q.den : ℝ)) = f 1 / q.den := by
      rw [h1]; field_simp
    rw [h2]
    field_simp
  have hc : 0 < f 1 := hpos 1 one_pos
  rcases lt_trichotomy (f x) (f 1 * x) with h | h | h
  · exfalso
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show f x / f 1 < x by rw [div_lt_iff₀ hc]; linarith)
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (div_nonneg (hpos x hx).le hc.le) hq1
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    have := hmono _ _ hq0 hq2
    rw [hq q hq0'] at this
    rw [div_lt_iff₀ hc] at hq1
    nlinarith
  · exact h
  · exfalso
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < f x / f 1 by rw [lt_div_iff₀ hc]; linarith)
    have hq0 : (0 : ℝ) < q := hx.trans hq1
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    have := hmono _ _ hx hq1
    rw [lt_div_iff₀ hc] at hq2
    have h3 := hq q hq0'
    nlinarith

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-- Two angles with the same absolute value and the same nonzero sign coincide. -/
theorem angle_eq_of_abs_eq_of_sign_eq {x y : Real.Angle} (h : |x.toReal| = |y.toReal|)
    (hs : x.sign = y.sign) (h0 : x.sign ≠ 0) : x = y := by
  rcases abs_eq_abs.1 h with e | e
  · exact Real.Angle.toReal_injective e
  · exfalso
    have hxy : x = -y := by
      calc x = ((x.toReal : ℝ) : Real.Angle) := (Real.Angle.coe_toReal x).symm
        _ = ((-y.toReal : ℝ) : Real.Angle) := by rw [e]
        _ = -y := by rw [Real.Angle.coe_neg, Real.Angle.coe_toReal]
    have h1 : x.sign = -y.sign := by rw [hxy, Real.Angle.sign_neg]
    rw [← hs] at h1
    revert h0 h1
    generalize x.sign = t
    revert t
    decide

/-- Under `Z`, the oriented angles of every triangle (three distinct points) add up to `π`. -/
theorem angle_add_angle_add_angle_of_allZeroDefect (h : N.AllZeroDefect) {A B C : P}
    (hT : IsTriangle A B C) : N.angle A B C + N.angle B C A + N.angle C A B = π := by
  have hd := h A B C hT
  unfold NeutralPlane.defect NeutralPlane.uangle at hd
  have hcoe : N.angle A B C + N.angle B C A + N.angle C A B =
      ((((N.angle A B C).toReal + (N.angle B C A).toReal + (N.angle C A B).toReal : ℝ)) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_toReal,
      Real.Angle.coe_toReal]
  by_cases hdeg : IsTriangle.Degenerate A B C
  · have h1 := (N.degenerate_iff_angle hT.1 hT.2.1.symm).1 hdeg
    have h2 := (N.degenerate_iff_angle hT.2.1 hT.2.2.symm).1 (deg_rotate hdeg)
    have h3 := (N.degenerate_iff_angle hT.2.2 hT.1.symm).1 (deg_rotate (deg_rotate hdeg))
    have hp := Real.pi_pos
    rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rcases h3 with e3 | e3 <;>
      first
      | (exfalso; rw [e1, e2, e3] at hd
         simp only [Real.Angle.toReal_zero, Real.Angle.toReal_pi, abs_zero, abs_of_pos hp] at hd
         linarith)
      | (rw [e1, e2, e3]; simp)
  · have hs := N.sign_angle_triangle hT hdeg
    have hne := N.sign_angle_ne_zero hT hdeg
    have hsum : |(N.angle A B C).toReal| + |(N.angle B C A).toReal| + |(N.angle C A B).toReal| = π := by
      linarith
    rcases (by revert hne; generalize (N.angle A B C).sign = t; revert t; decide :
      ∀ t : SignType, t ≠ 0 → t = 1 ∨ t = -1) _ hne with h1 | h1
    · have a1 : 0 ≤ (N.angle A B C).toReal := Real.Angle.toReal_nonneg_iff_sign_nonneg.2 (by rw [h1]; decide)
      have a2 : 0 ≤ (N.angle B C A).toReal :=
        Real.Angle.toReal_nonneg_iff_sign_nonneg.2 (by rw [← hs.1, h1]; decide)
      have a3 : 0 ≤ (N.angle C A B).toReal :=
        Real.Angle.toReal_nonneg_iff_sign_nonneg.2 (by rw [← hs.2, ← hs.1, h1]; decide)
      rw [abs_of_nonneg a1, abs_of_nonneg a2, abs_of_nonneg a3] at hsum
      rw [hcoe, hsum]
    · have a1 : (N.angle A B C).toReal < 0 := Real.Angle.toReal_neg_iff_sign_neg.2 h1
      have a2 : (N.angle B C A).toReal < 0 := Real.Angle.toReal_neg_iff_sign_neg.2 (by rw [← hs.1, h1])
      have a3 : (N.angle C A B).toReal < 0 :=
        Real.Angle.toReal_neg_iff_sign_neg.2 (by rw [← hs.2, ← hs.1, h1])
      rw [abs_of_neg a1, abs_of_neg a2, abs_of_neg a3] at hsum
      have : (N.angle A B C).toReal + (N.angle B C A).toReal + (N.angle C A B).toReal = -π := by linarith
      rw [hcoe, this, Real.Angle.coe_neg, Real.Angle.neg_coe_pi]

/-! ### Small helpers on rays and nondegeneracy -/

theorem deg_swap23 {A B C : P} (h : IsTriangle.Degenerate A B C) : IsTriangle.Degenerate A C B := by
  obtain ⟨L, hL, hA, hB, hC⟩ := h
  exact ⟨L, hL, hA, hC, hB⟩

include N in
/-- Nondegeneracy is transported along an equality of angles. -/
theorem nondeg_of_angle_eq {A O B A' O' B' : P} (hA : A ≠ O) (hB : B ≠ O) (hA' : A' ≠ O') (hB' : B' ≠ O')
    (h : N.angle A' O' B' = N.angle A O B) (hnd : ¬ IsTriangle.Degenerate A O B) :
    ¬ IsTriangle.Degenerate A' O' B' := by
  intro hd
  apply hnd
  rw [N.degenerate_iff_angle hA hB, ← h, ← N.degenerate_iff_angle hA' hB']
  exact hd

/-- The angle at the vertex `A` does not change when the two other points move along their rays. -/
theorem angle_ray_ray {A B C B' C' : P} (hB : B ≠ A) (hC : C ≠ A) (hB' : B' ∈ metricHalfLine A B)
    (hB'A : B' ≠ A) (hC' : C' ∈ metricHalfLine A C) (hC'A : C' ≠ A) :
    N.angle B' A C' = N.angle B A C := by
  rw [N.angle_ray_left hB hB' hB'A hC'A, N.angle_ray_right hB hC hC' hC'A]

include N in
/-- Points on the two rays of a nondegenerate triangle at `A` form a nondegenerate triangle. -/
theorem nondeg_rays {A B C B' C' : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (hB' : B' ∈ metricHalfLine A B) (hB'A : B' ≠ A) (hC' : C' ∈ metricHalfLine A C) (hC'A : C' ≠ A) :
    IsTriangle A B' C' ∧ ¬ IsTriangle.Degenerate A B' C' := by
  have h1 : ¬ IsTriangle.Degenerate B A C := not_degenerate_swap hnd
  have h2 := N.nondeg_of_angle_eq hT.1.symm hT.2.2 hB'A hC'A
    (N.angle_ray_ray hT.1.symm hT.2.2 hB' hB'A hC' hC'A) h1
  have h3 : ¬ IsTriangle.Degenerate A B' C' := not_degenerate_swap h2
  exact ⟨⟨hB'A.symm, N.ne_of_not_degenerate hB'A h2, hC'A⟩, h3⟩

include N in
theorem not_mem_line_of_rays {A B C B' : P} (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C)
    (hB' : B' ∈ metricHalfLine A B) (hB'A : B' ≠ A) : B' ∉ N.line A C := by
  intro hmem
  have hCA : A ≠ C := hT.2.2.symm
  have := (N.nondeg_rays hT hnd hB' hB'A (N.self_mem_metricHalfLine hCA) hT.2.2).2
  exact this (deg_swap23 ((N.degenerate_iff_mem_line hCA).2 hmem))

theorem uangle_sum_of_allZeroDefect (h : N.AllZeroDefect) {A B C : P} (hT : IsTriangle A B C) :
    N.uangle A B C + N.uangle B C A + N.uangle C A B = π := by
  have := h A B C hT
  unfold NeutralPlane.defect at this
  linarith

/-- Uniqueness of the equiangular point (no `Z` needed): if `C₁, C₂ ≠ A` lie on `[AC)`, `B' ∉ (AC)` and
`∡AB'C₁ = ∡AB'C₂`, then `C₁ = C₂`. -/
theorem eq_of_angle_eq_of_mem_ray {A C B' C₁ C₂ : P} (hAC : A ≠ C) (hB' : B' ∉ N.line A C)
    (h₁ : C₁ ∈ metricHalfLine A C) (h₁A : C₁ ≠ A) (h₂ : C₂ ∈ metricHalfLine A C) (h₂A : C₂ ≠ A)
    (he : N.angle A B' C₁ = N.angle A B' C₂) : C₁ = C₂ := by
  have hAB' : A ≠ B' := fun e => hB' (e ▸ N.left_mem_line A C)
  have hC₁L : C₁ ∈ N.line A C := N.metricHalfLine_subset_line hAC h₁
  have hC₂L : C₂ ∈ N.line A C := N.metricHalfLine_subset_line hAC h₂
  have hC₁B : C₁ ≠ B' := fun e => hB' (e ▸ hC₁L)
  obtain ⟨D, hD, -, huniq⟩ := N.axiomIIIa B' A hAB' (N.angle A B' C₁)
  have m₁ : C₁ ∈ metricHalfLine B' D := huniq C₁ hC₁B rfl
  have m₂ : C₂ ∈ metricHalfLine B' D := huniq C₂ (fun e => hB' (e ▸ hC₂L)) he.symm
  have hray : metricHalfLine B' C₁ = metricHalfLine B' D := N.metricHalfLine_eq_of_mem hD.symm m₁ hC₁B
  have m₃ : C₂ ∈ N.line B' C₁ := N.metricHalfLine_subset_line hC₁B.symm (hray ▸ m₂)
  refine N.eq_of_mem_line_of_mem_line (N.isLine_line hAC) (N.isLine_line hC₁B.symm) ?_ hC₁L
    (N.right_mem_line B' C₁) hC₂L m₃
  intro hLM
  exact hB' (hLM ▸ N.left_mem_line B' C₁)

/-- Existence of the equiangular point under `Z`: for a nondegenerate triangle `ABC` and `B' ∈ [AB)`, `B' ≠ A`,
there is `C' ∈ [AC)`, `C' ≠ A`, with `∡AB'C' = ∡ABC`. -/
theorem exists_equiangular (h : N.AllZeroDefect) {A B C : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) {B' : P} (hB' : B' ∈ metricHalfLine A B) (hB'A : B' ≠ A) :
    ∃ C', C' ∈ metricHalfLine A C ∧ C' ≠ A ∧ N.angle A B' C' = N.angle A B C := by
  have hAB : A ≠ B := hT.1
  have hAC : A ≠ C := hT.2.2.symm
  have hB'L : B' ∉ N.line A C := N.not_mem_line_of_rays hT hnd hB' hB'A
  have hAB' : A ≠ B' := hB'A.symm
  -- a far point of the ray at which the angle exceeds `∡ABC`
  have hγ : 0 < N.uangle B C A :=
    N.uangle_pos_of_nondeg hT.2.1 hT.2.2.symm (nondeg_rotate hnd)
  obtain ⟨X₁, hX₁, hX₁A, hX₁lt⟩ := N.exists_uangle_lt hAC.symm hB'L hγ
  obtain ⟨hT₁, hnd₁⟩ := N.nondeg_rays hT hnd hB' hB'A hX₁ hX₁A
  have hsum₁ := N.uangle_sum_of_allZeroDefect h hT₁
  have hsum := N.uangle_sum_of_allZeroDefect h hT
  have hcomm : N.uangle B' X₁ A = N.uangle A X₁ B' := N.uangle_comm hT₁.2.1 hX₁A.symm
  have hang : N.uangle X₁ A B' = N.uangle C A B := by
    rw [N.uangle_def, N.uangle_def, N.angle_ray_ray hAC.symm hAB.symm hX₁ hX₁A hB' hB'A]
  have hgt : N.uangle A B C < N.uangle A B' X₁ := by linarith
  -- the cosine of the angle along the ray
  obtain ⟨s, hs0, hs⟩ : ∃ s, 0 ≤ s ∧ N.linePt A C s = X₁ := by
    rw [N.metricHalfLine_eq_linePt hAC] at hX₁
    exact hX₁
  have hspos : 0 < s := by
    rcases hs0.lt_or_eq with h1 | h1
    · exact h1
    · exfalso; apply hX₁A; rw [← hs, ← h1, N.linePt_zero]
  set f : ℝ → ℝ := fun t => Real.Angle.cos (N.angle A B' (N.linePt A C t)) with hf
  have hray : ∀ t, 0 < t → N.linePt A C t ∈ metricHalfLine A C ∧ N.linePt A C t ≠ A := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [N.metricHalfLine_eq_linePt hAC]; exact ⟨t, ht.le, rfl⟩
    · intro e
      have := N.dist_left_linePt hAC t
      rw [e, dist_self, abs_of_pos ht] at this
      linarith
  have hne : ∀ t, N.linePt A C t ≠ B' := fun t e => hB'L (e ▸ N.linePt_mem_line A C t)
  have hcont : ContinuousOn f (Set.Icc 0 s) := by
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    have hnpi : N.angle A B' (N.linePt A C t) ≠ (π : Real.Angle) := by
      rcases ht.1.lt_or_eq with h1 | h1
      · intro hpi
        obtain ⟨-, hnd2⟩ := N.nondeg_rays hT hnd hB' hB'A (hray t h1).1 (hray t h1).2
        apply hnd2
        rw [N.degenerate_iff_angle hAB' (hne t)]
        exact Or.inr hpi
      · rw [← h1, N.linePt_zero, N.angle_self hAB']
        intro e
        exact Real.Angle.pi_ne_zero e.symm
    have h1 := N.axiomIIIc A B' (N.linePt A C t) hAB' (hne t) hnpi
    have h2 : ContinuousAt (fun t : ℝ => (A, B', N.linePt A C t)) t :=
      (continuous_const.prodMk (continuous_const.prodMk (N.continuous_linePt hAC))).continuousAt
    have h3 := ContinuousAt.comp (g := fun x : P × P × P => N.angle x.1 x.2.1 x.2.2)
      (f := fun t : ℝ => (A, B', N.linePt A C t)) (x := t) h1 h2
    exact Real.Angle.continuous_cos.continuousAt.comp h3
  have hu_cos : ∀ θ : Real.Angle, Real.Angle.cos θ = Real.cos |θ.toReal| := by
    intro θ; rw [Real.cos_abs, Real.Angle.cos_toReal]
  have hcosβ : Real.Angle.cos (N.angle A B C) ∈ Set.Icc (f s) (f 0) := by
    constructor
    · show Real.Angle.cos (N.angle A B' (N.linePt A C s)) ≤ _
      rw [hs, hu_cos, hu_cos]
      exact (Real.cos_lt_cos_of_nonneg_of_le_pi (N.uangle_nonneg A B C) (N.uangle_le_pi A B' X₁) hgt).le
    · show _ ≤ Real.Angle.cos (N.angle A B' (N.linePt A C 0))
      rw [N.linePt_zero, N.angle_self hAB', ← Real.Angle.cos_toReal]
      exact Real.cos_le_one _ |>.trans (by simp)
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hs0 hcont hcosβ
  have hu : N.uangle A B' (N.linePt A C t) = N.uangle A B C := by
    have h1 : Real.cos (N.uangle A B' (N.linePt A C t)) = Real.cos (N.uangle A B C) := by
      rw [N.uangle_def, N.uangle_def, ← hu_cos, ← hu_cos]
      exact hft
    exact Real.injOn_cos ⟨N.uangle_nonneg _ _ _, N.uangle_le_pi _ _ _⟩
      ⟨N.uangle_nonneg _ _ _, N.uangle_le_pi _ _ _⟩ h1
  have htpos : 0 < t := by
    rcases ht.1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      rw [← h1, N.linePt_zero, N.uangle_def, N.angle_self hAB'] at hu
      have h3 := N.uangle_pos_of_nondeg hT.1 hT.2.1.symm hnd
      simp at hu
      linarith
  obtain ⟨hmem, hXA⟩ := hray t htpos
  refine ⟨N.linePt A C t, hmem, hXA, ?_⟩
  obtain ⟨hT₂, hnd₂⟩ := N.nondeg_rays hT hnd hB' hB'A hmem hXA
  have s1 := N.sign_angle_triangle hT₂ hnd₂
  have s2 := N.sign_angle_triangle hT hnd
  have hs3 : N.angle (N.linePt A C t) A B' = N.angle C A B :=
    N.angle_ray_ray hAC.symm hAB.symm hmem hXA hB' hB'A
  have hsign : (N.angle A B' (N.linePt A C t)).sign = (N.angle A B C).sign := by
    rw [s1.1.trans s1.2, hs3, ← s2.2, ← s2.1]
  exact angle_eq_of_abs_eq_of_sign_eq hu hsign (by rw [hsign]; exact N.sign_angle_ne_zero hT hnd)

/-- Oriented angle-side-angle: triangles `ABC`, `A'B'C'` (nondegenerate) with `AB = A'B'`, `∡BAC = ∡B'A'C'` and
`∡ABC = ∡A'B'C'` have `AC = A'C'` and `BC = B'C'`. -/
theorem dist_eq_of_angle_eq_of_angle_eq {A B C A' B' C' : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (hT' : IsTriangle A' B' C') (h₁ : dist A B = dist A' B')
    (h₂ : N.angle B A C = N.angle B' A' C') (h₃ : N.angle A B C = N.angle A' B' C') :
    dist A C = dist A' C' ∧ dist B C = dist B' C' := by
  have hnd' := N.nondeg_of_angle_eq hT.1 hT.2.1.symm hT'.1 hT'.2.1.symm h₃.symm hnd
  have e₂ : N.uangle A B C = N.uangle A' B' C' := by
    rw [N.uangle_def, N.uangle_def, h₃]
  have e₃ : N.uangle C A B = N.uangle C' A' B' := by
    rw [N.uangle_def, N.uangle_def, N.angle_rev hT.2.2 hT.1.symm, N.angle_rev hT'.2.2 hT'.1.symm, h₂]
  have hc := TriangleCongruent.dist_eq (N.asa hT hT' hnd' h₁ e₂ e₃)
  obtain ⟨-, h2, h3⟩ := hc
  refine ⟨?_, h2.symm⟩
  rw [dist_comm A C, dist_comm A' C']
  exact h3.symm

include N in
/-- If `B₁` lies between `A` and `B₂` and `B₁ ∈ [AB)`, then also `B₂ ∈ [AB)`. -/
theorem mem_ray_of_isBetween {A B B₁ B₂ : P} (hAB : A ≠ B) (hB₁ : B₁ ∈ metricHalfLine A B)
    (hB : IsBetween A B₁ B₂) : B₂ ∈ metricHalfLine A B ∧ B₂ ≠ A := by
  refine ⟨?_, hB.ne.symm⟩
  have h1 := (N.metricHalfLine_eq_of_mem hAB hB₁ hB.1)
  rw [← h1]
  exact (N.isBetween_rays hB).2

/-- Under `Z`: the angle `∡AB₁C₂` at the nearer point exceeds `∡ABC` (unsigned), when `∡AB₂C₂ = ∡ABC`; it
equals `∡ABC` plus the (positive) angle of the triangle `B₂C₂B₁` at `C₂`. -/
theorem uangle_eq_add_of_equiangular (h : N.AllZeroDefect) {A B C B₁ B₂ C₂ : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (hB₁ : B₁ ∈ metricHalfLine A B) (hB : IsBetween A B₁ B₂)
    (hC₂ : C₂ ∈ metricHalfLine A C) (hC₂A : C₂ ≠ A) (e₂ : N.angle A B₂ C₂ = N.angle A B C) :
    N.uangle A B₁ C₂ = N.uangle A B C + N.uangle B₂ C₂ B₁ ∧ 0 < N.uangle B₂ C₂ B₁ := by
  obtain ⟨hB₂, hB₂A⟩ := N.mem_ray_of_isBetween hT.1 hB₁ hB
  obtain ⟨hT₂, hnd₂⟩ := N.nondeg_rays hT hnd hB₂ hB₂A hC₂ hC₂A
  have hB₁A : B₁ ≠ A := hB.1
  have hB₂C : B₂ ≠ C₂ := hT₂.2.1
  have hB₁C : B₁ ≠ C₂ := (N.nondeg_rays hT hnd hB₁ hB₁A hC₂ hC₂A).1.2.1
  have hB₁B₂ : B₁ ≠ B₂ := hB.2.1
  have hang : N.angle B₁ B₂ C₂ = N.angle A B C :=
    (N.angle_ray_left hB₂A.symm (N.isBetween_rays hB.symm).1 hB₁B₂ hB₂C.symm).trans e₂
  have hT₃ : IsTriangle B₁ B₂ C₂ := ⟨hB₁B₂, hB₂C, hB₁C.symm⟩
  have hnd₃ := N.nondeg_of_angle_eq hT.1 hT.2.1.symm hB₁B₂ hB₂C.symm hang hnd
  have hsum := N.uangle_sum_of_allZeroDefect h hT₃
  have hX : C₂ ∉ N.line A B₂ := fun hm => hnd₂ ((N.degenerate_iff_mem_line hB₂A.symm).2 hm)
  have hsup := (N.uangle_add_uangle_of_isBetween hB hX).1
  have hu : N.uangle B₁ B₂ C₂ = N.uangle A B C := by rw [N.uangle_def, N.uangle_def, hang]
  have hpos := N.uangle_pos_of_nondeg hB₂C hB₁C (nondeg_rotate hnd₃)
  exact ⟨by linarith, hpos⟩

/-- Monotonicity under `Z`: if `B₁` lies between `A` and `B₂` on `[AB)`, and `C₁, C₂ ∈ [AC)` are the
equiangular points (`∡AB₁C₁ = ∡AB₂C₂ = ∡ABC`), then `C₁` lies between `A` and `C₂`. -/
theorem isBetween_of_equiangular (h : N.AllZeroDefect) {A B C B₁ B₂ C₁ C₂ : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (hB₁ : B₁ ∈ metricHalfLine A B) (hB : IsBetween A B₁ B₂)
    (hC₁ : C₁ ∈ metricHalfLine A C) (hC₁A : C₁ ≠ A) (hC₂ : C₂ ∈ metricHalfLine A C) (hC₂A : C₂ ≠ A)
    (e₁ : N.angle A B₁ C₁ = N.angle A B C) (e₂ : N.angle A B₂ C₂ = N.angle A B C) :
    IsBetween A C₁ C₂ := by
  have hAC : A ≠ C := hT.2.2.symm
  have hB₁A : B₁ ≠ A := hB.1
  obtain ⟨hgt, hpos⟩ := N.uangle_eq_add_of_equiangular h hT hnd hB₁ hB hC₂ hC₂A e₂
  have hβ : N.uangle A B₁ C₁ = N.uangle A B C := by rw [N.uangle_def, N.uangle_def, e₁]
  obtain ⟨-, hnd₁⟩ := N.nondeg_rays hT hnd hB₁ hB₁A hC₁ hC₁A
  have hne : C₁ ≠ C₂ := by
    rintro rfl
    linarith
  have hnot : ¬ IsBetween A C₂ C₁ := by
    intro hb
    have hX : B₁ ∉ N.line A C₁ := fun hm =>
      hnd₁ (deg_swap23 ((N.degenerate_iff_mem_line hC₁A.symm).2 hm))
    have h38 := (N.isBetween_angle_sign_and_uangle hb hX).2.2
    have := N.uangle_nonneg C₂ B₁ C₁
    linarith
  have hC₁C₂ : N.angle C₁ A C₂ = 0 := by
    rw [N.angle_ray_ray hAC.symm hAC.symm hC₁ hC₁A hC₂ hC₂A, N.angle_self hAC.symm]
  rcases (N.isLine_line hAC).isBetween_trichotomy (N.left_mem_line A C)
      (N.metricHalfLine_subset_line hAC hC₁) (N.metricHalfLine_subset_line hAC hC₂) hC₁A.symm hne hC₂A with
    h1 | h1 | h1
  · exfalso
    have := NeutralPlane.IsBetween.angle_eq_pi N h1
    rw [hC₁C₂] at this
    exact Real.Angle.pi_ne_zero this.symm
  · exact h1
  · exact absurd h1 hnot

/-- Additivity under `Z`: with `B₁` between `A` and `B₂` and the equiangular points `C₁, C₂` as above, the
segments `[C₁C₂]` and the third side `[B₂C₂]` split as for a triangle with base `B₁B₂`: if `A₀B₀C₀` is a triangle
with `A₀B₀ = B₁B₂`, `∡B₀A₀C₀ = ∡BAC` and `∡A₀B₀C₀ = ∡ABC`, then `C₁C₂ = A₀C₀` and `B₂C₂ = B₁C₁ + B₀C₀`. -/
theorem dist_add_of_equiangular (h : N.AllZeroDefect) {A B C B₁ B₂ C₁ C₂ A₀ B₀ C₀ : P}
    (hT : IsTriangle A B C) (hnd : ¬ IsTriangle.Degenerate A B C) (hB₁ : B₁ ∈ metricHalfLine A B)
    (hB : IsBetween A B₁ B₂) (hC₁ : C₁ ∈ metricHalfLine A C) (hC₁A : C₁ ≠ A) (hC₂ : C₂ ∈ metricHalfLine A C)
    (hC₂A : C₂ ≠ A) (e₁ : N.angle A B₁ C₁ = N.angle A B C) (e₂ : N.angle A B₂ C₂ = N.angle A B C)
    (hT₀ : IsTriangle A₀ B₀ C₀) (h₀ : dist A₀ B₀ = dist B₁ B₂) (a₀ : N.angle B₀ A₀ C₀ = N.angle B A C)
    (b₀ : N.angle A₀ B₀ C₀ = N.angle A B C) :
    dist C₁ C₂ = dist A₀ C₀ ∧ dist B₂ C₂ = dist B₁ C₁ + dist B₀ C₀ := by
  have h2π : (π : Real.Angle) + π = 0 := Real.Angle.coe_pi_add_coe_pi
  have hAB : A ≠ B := hT.1
  have hAC : A ≠ C := hT.2.2.symm
  have hB₁A : B₁ ≠ A := hB.1
  have hB₁B₂ : B₁ ≠ B₂ := hB.2.1
  obtain ⟨hB₂, hB₂A⟩ := N.mem_ray_of_isBetween hAB hB₁ hB
  have hC12 : IsBetween A C₁ C₂ :=
    N.isBetween_of_equiangular h hT hnd hB₁ hB hC₁ hC₁A hC₂ hC₂A e₁ e₂
  have hC₁C₂ : C₁ ≠ C₂ := hC12.2.1
  obtain ⟨hT₁, hnd₁⟩ := N.nondeg_rays hT hnd hB₁ hB₁A hC₁ hC₁A
  obtain ⟨hT₂, hnd₂⟩ := N.nondeg_rays hT hnd hB₁ hB₁A hC₂ hC₂A
  obtain ⟨hT₃, hnd₃⟩ := N.nondeg_rays hT hnd hB₂ hB₂A hC₂ hC₂A
  have hB₁C₁ : B₁ ≠ C₁ := hT₁.2.1
  have hB₁C₂ : B₁ ≠ C₂ := hT₂.2.1
  have hB₂C₂ : B₂ ≠ C₂ := hT₃.2.1
  have hang : N.angle B₁ B₂ C₂ = N.angle A B C :=
    (N.angle_ray_left hB₂A.symm (N.isBetween_rays hB.symm).1 hB₁B₂ hB₂C₂.symm).trans e₂
  have hT₄ : IsTriangle B₁ B₂ C₂ := ⟨hB₁B₂, hB₂C₂, hB₁C₂.symm⟩
  -- the point reflection across the midpoint of `[B₁C₂]`
  obtain ⟨M, hM, hMd⟩ := N.exists_midpoint hB₁C₂
  have hR1 : N.pointRefl M B₁ = C₂ :=
    N.pointRefl_eq_of_isBetween hM (by rw [dist_comm M B₁]; exact hMd.symm)
  have hR2 : N.pointRefl M C₂ = B₁ :=
    N.pointRefl_eq_of_isBetween hM.symm (by rw [dist_comm M B₁]; exact hMd)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = N.pointRefl M C₁ := ⟨_, rfl⟩
  have hQC₂ : Q ≠ C₂ := fun e =>
    hB₁C₁ ((N.pointRefl M).injective (hQ ▸ e |>.trans hR1.symm)).symm
  have hQB₁ : Q ≠ B₁ := fun e => hC₁C₂ ((N.pointRefl M).injective (hQ ▸ e |>.trans hR2.symm))
  -- the alternate angles
  have hc : N.angle B₂ C₂ B₁ = N.angle C₁ B₁ C₂ := by
    have t2 := N.angle_add_angle_add_angle_of_allZeroDefect h hT₄
    rw [hang] at t2
    have i1 := N.axiomIIIb B₁ C₂ A B₂ hB₁C₂.symm hB₁A.symm hB₁B₂.symm
    have i4 := N.axiomIIIb B₁ A C₁ C₂ hB₁A.symm hB₁C₁.symm hB₁C₂.symm
    have i2 : N.angle A B₁ B₂ = π := NeutralPlane.IsBetween.angle_eq_pi N hB
    have i3 := N.angle_rev (A := C₂) (B := A) (O := B₁) hB₁C₂.symm hB₁A.symm
    linear_combination (norm := abel) t2 + i1 - i2 - i3 - i4 + e₁
  have hd : N.angle B₂ B₁ Q = N.angle B A C := by
    have j1 := N.axiomIIIb B₁ B₂ C₂ Q hB₁B₂.symm hB₁C₂.symm hQB₁
    have j2 := N.axiomIIIb B₁ B₂ A C₂ hB₁B₂.symm hB₁A.symm hB₁C₂.symm
    have jπ : N.angle B₂ B₁ A = π := NeutralPlane.IsBetween.angle_eq_pi N hB.symm
    have j3 := N.angle_pointRefl M (A := B₁) (B := C₂) (C := C₁) hB₁C₂ hC₁C₂
    rw [hR1, hR2, ← hQ] at j3
    have j4 : N.angle B₁ C₂ C₁ = N.angle B₁ C₂ A :=
      N.angle_ray_right hB₁C₂ hC₂A.symm (N.isBetween_rays hC12.symm).1 hC₁C₂
    have j5 := N.angle_add_angle_add_angle_of_allZeroDefect h hT₂
    have j6 : N.angle C₂ A B₁ = N.angle C A B := N.angle_ray_ray hAC.symm hAB.symm hC₂ hC₂A hB₁ hB₁A
    have j7 := N.angle_rev (A := C) (B := B) (O := A) hAC.symm hAB.symm
    linear_combination (norm := abel) -j1 - j2 + jπ + j3 + j4 + j5 - j6 - j7 + h2π
  have hQ0 : N.angle B₂ C₂ Q = 0 := by
    have k1 := N.axiomIIIb C₂ B₂ B₁ Q hB₂C₂ hB₁C₂ hQC₂
    have k2 := N.angle_pointRefl M (A := C₂) (B := B₁) (C := C₁) hB₁C₂.symm hB₁C₁.symm
    rw [hR2, hR1, ← hQ] at k2
    have k3 := N.angle_rev (A := C₂) (B := C₁) (O := B₁) hB₁C₂.symm hB₁C₁.symm
    linear_combination (norm := abel) -k1 + hc + k2 + k3
  have hQray : Q ∈ metricHalfLine C₂ B₂ := N.mem_ray_of_angle_eq_zero hB₂C₂ hQC₂ hQ0
  -- `Q` is strictly between `B₂` and `C₂`
  have hndα : ¬ IsTriangle.Degenerate B A C := not_degenerate_swap hnd
  have hα := (N.degenerate_iff_angle hAB.symm hAC.symm).not.1 hndα
  have hαne0 : N.angle B A C ≠ 0 := fun e => hα (Or.inl e)
  have hndQ : ¬ IsTriangle.Degenerate B₂ B₁ Q :=
    N.nondeg_of_angle_eq hAB.symm hAC.symm hB₁B₂.symm hQB₁ hd hndα
  have hQB₂ : Q ≠ B₂ := by
    intro e
    rw [e, N.angle_self hB₁B₂.symm] at hd
    exact hαne0 hd.symm
  have hgood : IsBetween B₂ Q C₂ := by
    rcases (N.isLine_line hB₂C₂.symm).isBetween_trichotomy (N.left_mem_line C₂ B₂)
        (N.metricHalfLine_subset_line hB₂C₂.symm hQray) (N.right_mem_line C₂ B₂) hQC₂.symm hQB₂
        hB₂C₂ with hb | hb | hb
    · exfalso
      have e1 := NeutralPlane.IsBetween.angle_eq_pi N hb
      have e2 := N.angle_rev (A := Q) (B := B₂) (O := C₂) hQC₂ hB₂C₂
      rw [hQ0, e1] at e2
      simp at e2
      exact Real.Angle.pi_ne_zero (by rw [e2])
    · exact hb.symm
    · exfalso
      have e1 := NeutralPlane.IsBetween.angle_eq_pi N hb
      have b1 := N.axiomIIIb B₂ B₁ C₂ Q hB₁B₂ hB₂C₂.symm hQB₂
      rw [hang, e1] at b1
      have hs1 : (N.angle B₁ B₂ Q).sign = -(N.angle A B C).sign := by
        rw [← b1, Real.Angle.sign_add_pi]
      have hT₅ : IsTriangle B₁ B₂ Q := ⟨hB₁B₂, hQB₂.symm, hQB₁⟩
      have s := N.sign_angle_triangle hT₅ (not_degenerate_swap hndQ)
      have r1 := N.angle_rev (A := Q) (B := B₂) (O := B₁) hQB₁ hB₁B₂.symm
      have r2 := N.angle_rev (A := C) (B := B) (O := A) hAC.symm hAB.symm
      have s2 := N.sign_angle_triangle hT hnd
      have hs2 : (N.angle B₁ B₂ Q).sign = (N.angle A B C).sign := by
        rw [s.1.trans s.2, r1, hd, Real.Angle.sign_neg]
        have : N.angle B A C = -N.angle C A B := by rw [r2, neg_neg]
        rw [this, Real.Angle.sign_neg, neg_neg, ← s2.2, ← s2.1]
      have hne := N.sign_angle_ne_zero hT hnd
      rw [hs2] at hs1
      revert hne hs1
      generalize (N.angle A B C).sign = t
      revert t
      decide
  have hβ' : N.angle B₁ B₂ Q = N.angle A B C :=
    ((N.angle_ray_right hB₁B₂ hB₂C₂.symm (N.isBetween_rays hgood).1 hQB₂).trans hang)
  have hT₅ : IsTriangle B₁ B₂ Q := ⟨hB₁B₂, hQB₂.symm, hQB₁⟩
  have hnd₀ := N.nondeg_of_angle_eq hAB hT.2.1.symm hT₀.1 hT₀.2.1.symm b₀ hnd
  obtain ⟨hAC0, hBC0⟩ := N.dist_eq_of_angle_eq_of_angle_eq hT₀ hnd₀ hT₅ h₀ (a₀.trans hd.symm)
    (b₀.trans hβ'.symm)
  constructor
  · have e := (N.pointRefl M).dist_eq C₁ C₂
    rw [hR2, ← hQ] at e
    rw [hAC0, ← e, dist_comm]
  · have e1 := hgood.dist_add
    have e := (N.pointRefl M).dist_eq C₁ B₁
    rw [hR1, ← hQ] at e
    rw [hBC0, ← e1, e, dist_comm C₁ B₁]
    ring

/-- **Proportionality (Thales) under `Z`.** For a nondegenerate triangle `ABC`, `B' ∈ [AB)`, `C' ∈ [AC)`
(both `≠ A`) with `∡AB'C' = ∡ABC`: `AC'·AB = AC·AB'` and `B'C'·AB = BC·AB'`. -/
theorem dist_mul_eq_of_equiangular (h : N.AllZeroDefect) {A B C B' C' : P} (hT : IsTriangle A B C)
    (hnd : ¬ IsTriangle.Degenerate A B C) (hB' : B' ∈ metricHalfLine A B) (hB'A : B' ≠ A)
    (hC' : C' ∈ metricHalfLine A C) (hC'A : C' ≠ A) (e : N.angle A B' C' = N.angle A B C) :
    dist A C' * dist A B = dist A C * dist A B' ∧ dist B' C' * dist A B = dist B C * dist A B' := by
  have hAB : A ≠ B := hT.1
  have hAC : A ≠ C := hT.2.2.symm
  -- the points of `[AB)` by their distance from `A`
  have hP : ∀ x : ℝ, 0 < x → N.linePt A B x ∈ metricHalfLine A B ∧ N.linePt A B x ≠ A := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [N.metricHalfLine_eq_linePt hAB]; exact ⟨x, hx.le, rfl⟩
    · intro e
      have := N.dist_left_linePt hAB x
      rw [e, dist_self, abs_of_pos hx] at this
      linarith
  have hdP : ∀ x : ℝ, 0 < x → dist A (N.linePt A B x) = x := by
    intro x hx
    rw [N.dist_left_linePt hAB, abs_of_pos hx]
  have hex : ∀ x : ℝ, 0 < x → ∃ Y, Y ∈ metricHalfLine A C ∧ Y ≠ A ∧
      N.angle A (N.linePt A B x) Y = N.angle A B C := fun x hx =>
    N.exists_equiangular h hT hnd (hP x hx).1 (hP x hx).2
  have : Nonempty P := ⟨A⟩
  choose! Cf hCf1 hCf2 hCf3 using hex
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, ∀ x, f x = dist A (Cf x) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ x, g x = dist (N.linePt A B x) (Cf x) := ⟨_, fun _ => rfl⟩
  have hbetween : ∀ x y : ℝ, 0 < x → 0 < y →
      IsBetween A (N.linePt A B x) (N.linePt A B (x + y)) := by
    intro x y hx hy
    refine ⟨(hP x hx).2, ?_, ?_, ?_⟩
    · intro e
      have := N.linePt_injective hAB e
      linarith
    · rw [hdP x hx, hdP (x + y) (by linarith), N.dist_linePt hAB, abs_of_nonpos (by linarith)]
      ring
    · exact ⟨N.line A B, N.isLine_line hAB, N.left_mem_line A B, N.linePt_mem_line A B x,
        N.linePt_mem_line A B (x + y)⟩
  have hkey : ∀ x y : ℝ, 0 < x → 0 < y → f (x + y) = f x + f y ∧ g (x + y) = g x + g y := by
    intro x y hx hy
    have hxy : 0 < x + y := by linarith
    have hB := hbetween x y hx hy
    obtain ⟨-, hnd₀⟩ := N.nondeg_rays hT hnd (hP y hy).1 (hP y hy).2 (hCf1 y hy) (hCf2 y hy)
    obtain ⟨hT₀, -⟩ := N.nondeg_rays hT hnd (hP y hy).1 (hP y hy).2 (hCf1 y hy) (hCf2 y hy)
    have hbt := N.isBetween_of_equiangular h hT hnd (hP x hx).1 hB (hCf1 x hx) (hCf2 x hx)
      (hCf1 _ hxy) (hCf2 _ hxy) (hCf3 x hx) (hCf3 _ hxy)
    obtain ⟨r1, r2⟩ := N.dist_add_of_equiangular h hT hnd (hP x hx).1 hB (hCf1 x hx) (hCf2 x hx)
      (hCf1 _ hxy) (hCf2 _ hxy) (hCf3 x hx) (hCf3 _ hxy) (A₀ := A) (B₀ := N.linePt A B y)
      (C₀ := Cf y) hT₀
      (by rw [hdP y hy, N.dist_linePt hAB, abs_of_nonpos (by linarith)]; ring)
      (N.angle_ray_ray hAB.symm hAC.symm (hP y hy).1 (hP y hy).2 (hCf1 y hy) (hCf2 y hy))
      (hCf3 y hy)
    refine ⟨?_, ?_⟩
    · rw [hf, hf, hf]
      have := hbt.dist_add
      rw [r1] at this
      linarith
    · rw [hg, hg, hg]
      linarith
  have hfpos : ∀ x, 0 < x → 0 < f x := fun x hx => by
    rw [hf]; exact dist_pos.2 (hCf2 x hx).symm
  have hgpos : ∀ x, 0 < x → 0 < g x := fun x hx => by
    rw [hg]
    exact dist_pos.2 (N.nondeg_rays hT hnd (hP x hx).1 (hP x hx).2 (hCf1 x hx) (hCf2 x hx)).1.2.1
  have hflin : ∀ x : ℝ, 0 < x → f x = f 1 * x := fun x hx => eq_mul_of_additive_of_pos (fun a b ha hb => (hkey a b ha hb).1) hfpos hx
  have hglin : ∀ x : ℝ, 0 < x → g x = g 1 * x := fun x hx => eq_mul_of_additive_of_pos (fun a b ha hb => (hkey a b ha hb).2) hgpos hx
  -- identify the given points
  have hdB : 0 < dist A B := dist_pos.2 hAB
  have hdB' : 0 < dist A B' := dist_pos.2 hB'A.symm
  have hB'eq : B' = N.linePt A B (dist A B') := by
    obtain ⟨X, -, hX⟩ := N.existsUnique_mem_metricHalfLine_dist hAB hdB'.le
    have h1 := hX B' ⟨hB', rfl⟩
    have h2 := hX (N.linePt A B (dist A B')) ⟨(hP _ hdB').1, hdP _ hdB'⟩
    exact h1.trans h2.symm
  have hCeq : C = Cf (dist A B) := by
    have hBL : B ∉ N.line A C := N.not_mem_line_of_rays hT hnd (N.self_mem_metricHalfLine hAB) hAB.symm
    refine N.eq_of_angle_eq_of_mem_ray hAC hBL (N.self_mem_metricHalfLine hAC) hAC.symm (hCf1 _ hdB)
      (hCf2 _ hdB) ?_
    have h3 := hCf3 _ hdB
    rw [N.linePt_dist hAB] at h3
    exact h3.symm
  have hC'eq : C' = Cf (dist A B') := by
    refine N.eq_of_angle_eq_of_mem_ray hAC (N.not_mem_line_of_rays hT hnd hB' hB'A) hC' hC'A
      (hCf1 _ hdB') (hCf2 _ hdB') ?_
    have h3 := hCf3 _ hdB'
    rw [← hB'eq] at h3
    rw [h3]
    exact e
  have l1 := hflin _ hdB'
  have l2 := hglin _ hdB'
  have l3 := hflin _ hdB
  have l4 := hglin _ hdB
  rw [hf, ← hC'eq] at l1
  rw [hg, ← hC'eq, ← hB'eq] at l2
  rw [hf, ← hCeq] at l3
  rw [hg, ← hCeq, N.linePt_dist hAB] at l4
  constructor
  · rw [l1, l3]; ring
  · rw [l2, l4]; ring

include N in
/-- Two points of a ray at different distances: the nearer lies between the vertex and the farther. -/
theorem isBetween_of_ray {A O X Y : P} (hAO : A ≠ O) (hX : X ∈ metricHalfLine A O) (hXA : X ≠ A)
    (hY : Y ∈ metricHalfLine A O) (hlt : dist A X < dist A Y) : IsBetween A X Y := by
  have hY' : Y ∈ metricHalfLine A X := by
    rw [N.metricHalfLine_eq_of_mem hAO hX hXA]; exact hY
  have hd := N.dist_of_mem_metricHalfLine hXA.symm hY'
  refine ⟨hXA, ?_, ?_, ?_⟩
  · intro e
    rw [e] at hlt
    exact lt_irrefl _ hlt
  · rw [hd, abs_of_neg (by linarith)]
    ring
  · exact ⟨N.line A O, N.isLine_line hAO, N.left_mem_line A O, N.metricHalfLine_subset_line hAO hX,
      N.metricHalfLine_subset_line hAO hY⟩

include N in
/-- Scaling by `k > 0` from `A` keeps betweenness. -/
theorem isBetween_scale {A B C B' C' : P} {k : ℝ} (hk : 0 < k) (hb : IsBetween A B C)
    (hB' : B' ∈ metricHalfLine A B) (hC' : C' ∈ metricHalfLine A C) (hdB : dist A B' = k * dist A B)
    (hdC : dist A C' = k * dist A C) : IsBetween A B' C' := by
  have hAB : A ≠ B := hb.1.symm
  have hCray : C ∈ metricHalfLine A B := (N.isBetween_rays hb).2
  have hC'' : C' ∈ metricHalfLine A B := by
    rw [← N.metricHalfLine_eq_of_mem hAB hCray hb.ne.symm]; exact hC'
  have hB'A : B' ≠ A := by
    intro e
    rw [e, dist_self] at hdB
    have := mul_pos hk (dist_pos.2 hAB)
    linarith
  exact N.isBetween_of_ray hAB hB' hB'A hC'' (by
    rw [hdB, hdC]; exact mul_lt_mul_of_pos_left hb.dist_lt_left hk)

/-- On a ray from `X` through `Y`: `∡YXZ = 0` and `∡ZXY = 0` when `Y` lies between `X` and `Z`. -/
theorem angle_zero_of_isBetween {X Y Z : P} (hb : IsBetween X Y Z) :
    N.angle Y X Z = 0 ∧ N.angle Z X Y = 0 :=
  ⟨N.angle_eq_zero_of_mem_ray hb.1 (N.isBetween_rays hb).2 hb.ne.symm,
    N.angle_eq_zero_of_mem_ray hb.ne.symm (N.isBetween_rays hb).1 hb.1⟩

/-- Axiom V for degenerate triangles holds in every neutral plane (the points lie on one line). -/
theorem axiomV_degenerate {A B C B' C' : P} {k : ℝ} (hk : 0 < k) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hdeg : IsTriangle.Degenerate A B C) (hB' : B' ∈ metricHalfLine A B) (hC' : C' ∈ metricHalfLine A C)
    (hdB : dist A B' = k * dist A B) (hdC : dist A C' = k * dist A C) :
    dist B' C' = k * dist B C ∧ N.angle A B C = N.angle A B' C' ∧ N.angle A C B = N.angle A C' B' := by
  have hB'A : B' ≠ A := by
    intro e
    rw [e, dist_self] at hdB
    have := mul_pos hk (dist_pos.2 hAB)
    linarith
  have hC'A : C' ≠ A := by
    intro e
    rw [e, dist_self] at hdC
    have := mul_pos hk (dist_pos.2 hAC)
    linarith
  obtain ⟨L, hL, hA, hB, hC⟩ := hdeg
  rcases hL.isBetween_trichotomy hA hB hC hAB hBC hAC.symm with hb | hb | hb
  · -- `A` lies between `B` and `C`
    have hpi : N.angle B' A C' = π := by
      rw [N.angle_ray_ray hAB.symm hAC.symm hB' hB'A hC' hC'A]
      exact NeutralPlane.IsBetween.angle_eq_pi N hb
    have hb' : IsBetween B' A C' := (N.angle_eq_pi_iff hB'A hC'A).1 hpi
    have E1 := hb.dist_add
    have E1' := hb'.dist_add
    rw [dist_comm B A] at E1
    rw [dist_comm B' A] at E1'
    refine ⟨by linear_combination -E1' + hdB + hdC + k * E1, ?_, ?_⟩
    · rw [(N.angle_zero_of_isBetween hb).1, (N.angle_zero_of_isBetween hb').1]
    · rw [(N.angle_zero_of_isBetween hb.symm).1, (N.angle_zero_of_isBetween hb'.symm).1]
  · -- `B` lies between `A` and `C`
    have hb' := N.isBetween_scale hk hb hB' hC' hdB hdC
    have E1 := hb.dist_add
    have E1' := hb'.dist_add
    refine ⟨by linear_combination E1' - hdB + hdC - k * E1, ?_, ?_⟩
    · rw [NeutralPlane.IsBetween.angle_eq_pi N hb, NeutralPlane.IsBetween.angle_eq_pi N hb']
    · rw [(N.angle_zero_of_isBetween hb.symm).2, (N.angle_zero_of_isBetween hb'.symm).2]
  · -- `C` lies between `A` and `B`
    have hb' := N.isBetween_scale hk hb hC' hB' hdC hdB
    have E1 := hb.dist_add
    have E1' := hb'.dist_add
    refine ⟨?_, ?_, ?_⟩
    · rw [dist_comm B' C', dist_comm B C]
      linear_combination E1' + hdB - hdC - k * E1
    · rw [(N.angle_zero_of_isBetween hb.symm).2, (N.angle_zero_of_isBetween hb'.symm).2]
    · rw [NeutralPlane.IsBetween.angle_eq_pi N hb, NeutralPlane.IsBetween.angle_eq_pi N hb']

/-- **Theorem 11.16, `Z` ⇒ Axiom V.** If every triangle of a neutral plane has zero defect, the plane satisfies
Axiom V. -/
@[kb "petrunin2025" "Theorem 11.16, p. 88"]
theorem axiomV_of_allZeroDefect (h : N.AllZeroDefect) : N.AxiomV := by
  intro A B C B' C' k hk hAB hAC hBC hB' hC' hdB hdC
  by_cases hdeg : IsTriangle.Degenerate A B C
  · exact N.axiomV_degenerate hk hAB hAC hBC hdeg hB' hC' hdB hdC
  have hT : IsTriangle A B C := ⟨hAB, hBC, hAC.symm⟩
  have hB'A : B' ≠ A := by
    intro e
    rw [e, dist_self] at hdB
    have := mul_pos hk (dist_pos.2 hAB)
    linarith
  obtain ⟨C'', hC''1, hC''2, hC''3⟩ := N.exists_equiangular h hT hdeg hB' hB'A
  obtain ⟨m1, m2⟩ := N.dist_mul_eq_of_equiangular h hT hdeg hB' hB'A hC''1 hC''2 hC''3
  have hd'' : dist A C'' = k * dist A C := by
    have : dist A C'' * dist A B = k * dist A C * dist A B := by rw [m1, hdB]; ring
    exact mul_right_cancel₀ (dist_pos.2 hAB).ne' this
  have hCeq : C'' = C' := by
    obtain ⟨X, -, hX⟩ := N.existsUnique_mem_metricHalfLine_dist hAC (mul_nonneg hk.le (dist_nonneg (x := A) (y := C)))
    exact (hX C'' ⟨hC''1, hd''⟩).trans (hX C' ⟨hC', hdC⟩).symm
  subst hCeq
  have hC''A := hC''2
  refine ⟨?_, hC''3.symm, ?_⟩
  · have : dist B' C'' * dist A B = k * dist B C * dist A B := by rw [m2, hdB]; ring
    exact mul_right_cancel₀ (dist_pos.2 hAB).ne' this
  · have s1 := N.angle_add_angle_add_angle_of_allZeroDefect h hT
    obtain ⟨hT', -⟩ := N.nondeg_rays hT hdeg hB' hB'A hC''1 hC''A
    have s2 := N.angle_add_angle_add_angle_of_allZeroDefect h hT'
    have r1 := N.angle_rev (A := A) (B := B) (O := C) hAC hBC
    have r2 := N.angle_rev (A := A) (B := B') (O := C'') hC''A.symm hT'.2.1
    have r3 : N.angle C'' A B' = N.angle C A B :=
      N.angle_ray_ray hAC.symm hAB.symm hC''1 hC''A hB' hB'A
    linear_combination (norm := abel) r1 - r2 - s1 + s2 - hC''3 - r3

end NeutralPlane

end Neutral

end UndergradKB.Geometry
