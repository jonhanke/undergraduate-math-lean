import Mathlib.Topology.MetricSpace.HausdorffDistance
import UndergradKB.Geometry.NeutralParallels
import UndergradKB.Common.Attr

/-! # Neutral plane VIII: lines at bounded distance (Petrunin, Theorem 11.16, (c) ⇒ (f))

For every neutral plane: two distinct lines at bounded distance from each other give a rectangle.

* **Divergence.** If `O ∈ m` and `X₁` is the midpoint of `[O X₂]` with `X₁ ∉ m`, then the distance from `X₂` to
  `m` is at least twice the distance from `X₁` to `m` (reflect across `X₁` and apply Exercise 11.11). Hence two
  lines through a common point are never at bounded distance.
* **Convexity.** Along a line `ℓ` disjoint from `m`, the distance to `m` is midpoint-convex (the same reflection
  argument), so if it is bounded it is constant.
* **Rectangle.** If the distance to `m` is constant along `ℓ`, the feet of three points `X`, `M`, `Y` of `ℓ`
  (`M` the midpoint) give Saccheri quadrangles with equal summit angles, and these angles are right. -/

namespace UndergradKB.Geometry

open Real

/-- A real function, midpoint-convex and bounded above, is constant. -/
theorem eq_of_midpoint_convex_of_bddAbove {g : ℝ → ℝ} {C : ℝ}
    (hmid : ∀ t s : ℝ, 2 * g t ≤ g (t - s) + g (t + s)) (hC : ∀ t, g t ≤ C) (a b : ℝ) : g a = g b := by
  have key : ∀ a b : ℝ, g b ≤ g a := by
    intro a b
    by_contra hlt
    push Not at hlt
    set d := g b - g a with hd
    have hd0 : 0 < d := by linarith
    set x : ℕ → ℝ := fun n => a + (n : ℝ) * (b - a) with hx
    have hstep : ∀ n : ℕ, d ≤ g (x (n + 1)) - g (x n) := by
      intro n
      induction n with
      | zero =>
        have e1 : x (0 + 1) = b := by simp [hx]
        have e0 : x 0 = a := by simp [hx]
        rw [e1, e0]
      | succ n ih =>
        have h := hmid (x (n + 1)) (b - a)
        have e1 : x (n + 1) - (b - a) = x n := by simp only [hx]; push_cast; ring
        have e2 : x (n + 1) + (b - a) = x (n + 1 + 1) := by simp only [hx]; push_cast; ring
        rw [e1, e2] at h
        linarith
    have hgrow : ∀ n : ℕ, g a + n * d ≤ g (x n) := by
      intro n
      induction n with
      | zero => simp [hx]
      | succ n ih =>
        have := hstep n
        push_cast
        linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((C - g a) / d)
    have h1 := hgrow n
    have h2 := hC (x n)
    have : C - g a < n * d := by rwa [div_lt_iff₀ hd0] at hn
    linarith
  exact le_antisymm (key b a) (key a b)

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

/-- **Divergence.** If `X₁` is the midpoint of `[O X₂]`, `O ∈ m`, `X₁ ∉ m`, and `F₁`, `F₂` are the feet of `X₁`,
`X₂` on `m`, then `2·X₁F₁ ≤ X₂F₂`. -/
theorem two_mul_dist_foot_le {m : Set P} {O X₁ X₂ F₁ F₂ : P} (hO : O ∈ m) (hX₁ : X₁ ∉ m)
    (hb : IsBetween O X₁ X₂) (hd : dist O X₁ = dist X₁ X₂) (hF₁ : F₁ ∈ m)
    (hF₁r : ∀ Y ∈ m, Y ≠ F₁ → N.uangle X₁ F₁ Y = π / 2) (hF₂ : F₂ ∈ m) :
    2 * dist X₁ F₁ ≤ dist X₂ F₂ := by
  have hXF : X₁ ≠ F₁ := fun e => hX₁ (e ▸ hF₁)
  set s := N.pointRefl X₁ with hs
  set F' := s F₁ with hF'
  have hb' : IsBetween F₁ X₁ F' := N.isBetween_pointReflFun (Ne.symm hXF)
  have hd' : dist X₁ F' = dist X₁ F₁ := N.dist_pointReflFun X₁ F₁
  have hsO : s O = X₂ := N.pointRefl_eq_of_isBetween hb (by rw [← hd, dist_comm])
  have hsX : s X₁ = X₁ := by rw [hs, pointRefl_apply, pointReflFun_self]
  have hFF' : F₁ ≠ F' := hb'.ne
  have hlen : dist F₁ F' = 2 * dist X₁ F₁ := by
    have := hb'.dist_add
    rw [hd', dist_comm F₁ X₁] at this
    linarith
  have hX₁l : X₁ ∈ N.line F₁ F' := N.mem_line_of_isBetween hb'
  have hl : N.line F₁ X₁ = N.line F₁ F' :=
    N.line_eq_of_mem hFF' (N.left_mem_line F₁ F') hX₁l (Ne.symm hXF)
  have key := N.dist_le_of_perp_perp (A := F₁) (B := F') (C := X₂) (D := F₂) hFF' ?_ ?_
  · rw [hlen] at key
    exact key
  · by_cases e : F₂ = F₁
    · exact Or.inl e
    right
    have h1 := hF₁r F₂ hF₂ e
    have hF'l : F' ∈ N.line F₁ X₁ := by rw [hl]; exact N.right_mem_line F₁ F'
    have h2 := N.uangle_eq_pi_div_two_of_mem_line hXF e h1 hF'l (Ne.symm hFF')
    exact (N.uangle_comm e (Ne.symm hFF')).trans h2
  · by_cases e : O = F₁
    · left
      rw [← hsO, e]
    right
    have h1 := hF₁r O hO e
    have h2 := N.uangle_isometryEquiv s hXF e
    rw [hsX, hsO, h1] at h2
    have hX₂F' : X₂ ≠ F' := by
      rw [← hsO, hF']
      exact fun h => e (s.injective h)
    have hF₁l : F₁ ∈ N.line F' X₁ := by
      rw [N.line_eq_of_mem hFF' (N.right_mem_line F₁ F') hX₁l hb'.2.1.symm]
      exact N.left_mem_line F₁ F'
    exact N.uangle_eq_pi_div_two_of_mem_line hb'.2.1 hX₂F' h2 hF₁l hFF'

/-- Points of a line at increasing parameters are in order. -/
theorem isBetween_linePt {A B : P} (h : A ≠ B) {r s t : ℝ} (h1 : r < s) (h2 : s < t) :
    IsBetween (N.linePt A B r) (N.linePt A B s) (N.linePt A B t) := by
  have inj := N.linePt_injective h
  refine ⟨fun e => (ne_of_gt h1) (inj e), fun e => (ne_of_lt h2) (inj e), ?_, ?_⟩
  · rw [N.dist_linePt h, N.dist_linePt h, N.dist_linePt h, abs_of_neg (by linarith),
      abs_of_neg (by linarith), abs_of_neg (by linarith)]
    ring
  · exact ⟨N.line A B, N.isLine_line h, N.linePt_mem_line A B r, N.linePt_mem_line A B s,
      N.linePt_mem_line A B t⟩

/-- The distance from a point to a line is attained at the foot of the perpendicular. -/
theorem infDist_eq_dist_foot {m : Set P} (hm : IsLine m) {X F : P} (hF : F ∈ m)
    (hFr : ∀ Y ∈ m, Y ≠ F → N.uangle X F Y = π / 2) : Metric.infDist X m = dist X F := by
  refine le_antisymm (Metric.infDist_le_dist_of_mem hF) ((Metric.le_infDist ⟨F, hF⟩).2 fun Y hY => ?_)
  by_cases e : Y = F
  · rw [e]
  · exact (N.dist_foot_lt hm hF hY e hFr).le

include N in
/-- **Two lines through a common point are not at bounded distance.** -/
theorem not_bounded_of_mem_of_mem {ℓ m : Set P} (hℓ : IsLine ℓ) (hm : IsLine m) (hne : ℓ ≠ m) {O : P}
    (hOℓ : O ∈ ℓ) (hOm : O ∈ m) (C : ℝ) : ¬ ∀ X ∈ ℓ, ∃ Y ∈ m, dist X Y ≤ C := by
  intro hC
  obtain ⟨X₀, hX₀, hX₀O⟩ := exists_ne_mem hℓ hOℓ
  have hOX : O ≠ X₀ := Ne.symm hX₀O
  have hℓe : ℓ = N.line O X₀ := N.eq_line hℓ hOℓ hX₀ hOX
  have d0 : 0 < dist O X₀ := dist_pos.2 hOX
  set X : ℕ → P := fun n => N.linePt O X₀ (2 ^ n * dist O X₀) with hXdef
  have hXℓ : ∀ n, X n ∈ ℓ := fun n => by rw [hℓe]; exact N.linePt_mem_line O X₀ _
  have hXO : ∀ n, X n ≠ O := fun n e => by
    have := N.dist_left_linePt hOX (2 ^ n * dist O X₀)
    rw [show N.linePt O X₀ (2 ^ n * dist O X₀) = X n from rfl, e, dist_self] at this
    have : 0 < |2 ^ n * dist O X₀| := abs_pos.2 (by positivity)
    linarith
  have hXm : ∀ n, X n ∉ m := fun n hm' =>
    hXO n (N.eq_of_mem_line_of_mem_line hℓ hm hne (hXℓ n) hm' hOℓ hOm)
  have hstep : ∀ n, IsBetween O (X n) (X (n + 1)) ∧ dist O (X n) = dist (X n) (X (n + 1)) := by
    intro n
    have hp : (0 : ℝ) < 2 ^ n * dist O X₀ := by positivity
    have e0 : N.linePt O X₀ 0 = O := N.linePt_zero O X₀
    refine ⟨?_, ?_⟩
    · rw [← e0]
      refine N.isBetween_linePt hOX hp ?_
      rw [pow_succ]
      nlinarith
    · simp only [hXdef]
      rw [N.dist_left_linePt hOX, N.dist_linePt hOX, pow_succ, abs_of_pos hp]
      rw [abs_of_neg (by nlinarith)]
      ring
  -- feet
  have hfoot : ∀ n, ∃ F ∈ m, ∀ Y ∈ m, Y ≠ F → N.uangle (X n) F Y = π / 2 := fun n =>
    N.exists_foot hm (hXm n)
  obtain ⟨F₀, hF₀, hF₀r⟩ := hfoot 0
  have h0 : 0 < dist (X 0) F₀ := dist_pos.2 fun e => hXm 0 (e ▸ hF₀)
  have grow : ∀ n, ∀ F ∈ m, (∀ Y ∈ m, Y ≠ F → N.uangle (X n) F Y = π / 2) →
      2 ^ n * dist (X 0) F₀ ≤ dist (X n) F := by
    intro n
    induction n with
    | zero =>
      intro F hF hFr
      rw [N.foot_unique hm (hXm 0) hF hF₀ hFr hF₀r]
      simp
    | succ n ih =>
      intro F hF _
      obtain ⟨G, hG, hGr⟩ := hfoot n
      have h1 := ih G hG hGr
      have h2 := N.two_mul_dist_foot_le hOm (hXm n) (hstep n).1 (hstep n).2 hG hGr hF
      rw [pow_succ]
      linarith
  have bound : ∀ n, 2 ^ n * dist (X 0) F₀ ≤ C := by
    intro n
    obtain ⟨F, hF, hFr⟩ := hfoot n
    obtain ⟨Y, hY, hXY⟩ := hC (X n) (hXℓ n)
    have := grow n F hF hFr
    have h2 : dist (X n) F ≤ dist (X n) Y := by
      by_cases e : Y = F
      · rw [e]
      · exact (N.dist_foot_lt hm hF hY e hFr).le
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / dist (X 0) F₀) (by norm_num : (1 : ℝ) < 2)
  have := bound n
  rw [div_lt_iff₀ h0] at hn
  linarith

include N in
/-- **Midpoint convexity of the distance to a line.** If `ℓ` misses `m`, `X, Y ∈ ℓ` and `M` is the midpoint of
`[XY]`, then `2·d(M, m) ≤ d(X, m) + d(Y, m)`. -/
theorem two_mul_infDist_le {m : Set P} (hm : IsLine m) {X M Y : P} (hX : X ∉ m) (hY : Y ∉ m) (hM : M ∉ m)
    (hb : IsBetween X M Y) (hd : dist X M = dist M Y) :
    2 * Metric.infDist M m ≤ Metric.infDist X m + Metric.infDist Y m := by
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hm hX
  obtain ⟨G, hG, hGr⟩ := N.exists_foot hm hY
  obtain ⟨H, hH, hHr⟩ := N.exists_foot hm hM
  rw [N.infDist_eq_dist_foot hm hF hFr, N.infDist_eq_dist_foot hm hG hGr, N.infDist_eq_dist_foot hm hH hHr]
  set s := N.pointRefl M with hs
  have hFM : F ≠ M := fun e => hM (e ▸ hF)
  have hsX : s X = Y := N.pointRefl_eq_of_isBetween hb (by rw [← hd, dist_comm])
  have hb' : IsBetween F M (s F) := N.isBetween_pointReflFun hFM
  have hd' : dist M (s F) = dist M F := N.dist_pointReflFun M F
  have hF'm : s F ∉ m := by
    intro hF'
    apply hM
    rw [N.eq_line hm hF hF' hb'.ne]
    exact N.mem_line_of_isBetween hb'
  have key := N.two_mul_dist_foot_le hF hM hb' (by rw [hd', dist_comm]) hH hHr hG
  have h1 : dist (s F) Y = dist F X := by rw [← hsX, s.dist_eq]
  have h2 := dist_triangle (s F) Y G
  rw [h1, dist_comm F X] at h2
  linarith

/-- In a quadrangle `ABCD` with right angles at `A` and `B` and `AD = BC` (a Saccheri quadrangle), the angles at
`D` and `C` are equal (two congruences: SAS, then SSS). -/
theorem saccheri_uangle_eq {A B C D : P} (hAB : A ≠ B) (hAD : A ≠ D) (hBC : B ≠ C) (hDC : D ≠ C)
    (hA : N.uangle D A B = π / 2) (hB : N.uangle A B C = π / 2) (hd : dist A D = dist B C) :
    N.uangle A D C = N.uangle B C D := by
  have hBD : B ≠ D := by
    rintro rfl
    rw [N.uangle_def, N.angle_self (Ne.symm hAB)] at hA
    simp at hA
    linarith [Real.pi_pos]
  have hAC : A ≠ C := by
    rintro rfl
    rw [N.uangle_def, N.angle_self hAB] at hB
    simp at hB
    linarith [Real.pi_pos]
  have h₃ : N.uangle C B A = N.uangle D A B := by
    rw [N.uangle_comm (Ne.symm hBC) hAB, hB, hA]
  have c1 := N.sas (A := A) (B := B) (C := D) (A' := B) (B' := A) (C' := C) hAB hAD hBD (Ne.symm hAB) hBC hAC
    (dist_comm B A) hd.symm h₃
  have e1 := (TriangleCongruent.dist_eq c1).2.1
  have c2 := N.sss (A := A) (B := D) (C := C) (A' := B) (B' := C) (C' := D) ⟨hAD, hDC, Ne.symm hAC⟩
    ⟨hBC, Ne.symm hDC, Ne.symm hBD⟩ hd.symm (dist_comm C D)
    (by rw [dist_comm D B, ← e1, dist_comm])
  exact (TriangleCongruent.uangle_eq N c2 hAD (Ne.symm hDC)).symm

/-- Two points of a line `ℓ` missing `m` have different feet on `m`. -/
private theorem foot_ne {ℓ m : Set P} (hℓ : IsLine ℓ) (hm : IsLine m) (hdisj : ∀ O ∈ ℓ, O ∉ m) {X Y F G : P}
    (hX : X ∈ ℓ) (hY : Y ∈ ℓ) (hXY : X ≠ Y) (hF : F ∈ m) (hFr : ∀ Z ∈ m, Z ≠ F → N.uangle X F Z = π / 2)
    (hG : G ∈ m) (hGr : ∀ Z ∈ m, Z ≠ G → N.uangle Y G Z = π / 2) : F ≠ G := by
  rintro rfl
  obtain ⟨Z, hZ, hZF⟩ := exists_ne_mem hm hF
  have hXF : X ≠ F := fun e => hdisj X hX (e ▸ hF)
  have hYF : Y ≠ F := fun e => hdisj Y hY (e ▸ hF)
  have r1 := (N.uangle_comm hZF hXF).trans (hFr Z hZ hZF)
  have r2 := (N.uangle_comm hZF hYF).trans (hGr Z hZ hZF)
  have hYl : Y ∈ N.line F X := N.mem_line_of_perp hm hZ hF hZF hXF hYF r1 r2
  have hl : N.line X Y = N.line F X := N.line_eq_of_mem (Ne.symm hXF) (N.right_mem_line F X) hYl hXY
  apply hdisj F _ hF
  rw [N.eq_line hℓ hX hY hXY, hl]
  exact N.left_mem_line F X

/-- **(c) ⇒ (f).** Two distinct lines at bounded distance give a rectangle. -/
theorem hasRectangle_of_boundedDistantLines (h : N.BoundedDistantLines) : N.HasRectangle := by
  obtain ⟨ℓ, m, hℓ, hm, hne, C, hC⟩ := h
  by_cases hmeet : ∃ O, O ∈ ℓ ∧ O ∈ m
  · obtain ⟨O, hOℓ, hOm⟩ := hmeet
    exact absurd hC (N.not_bounded_of_mem_of_mem hℓ hm hne hOℓ hOm C)
  push Not at hmeet
  obtain ⟨f, hf, hfr⟩ := hℓ
  have hA : f 0 ∈ ℓ := hfr ▸ ⟨0, rfl⟩
  have hB : f 1 ∈ ℓ := hfr ▸ ⟨1, rfl⟩
  have hAB : f 0 ≠ f 1 := fun e => by
    have := hf.injective e
    norm_num at this
  have hℓ' : IsLine ℓ := ⟨f, hf, hfr⟩
  have hℓe : ℓ = N.line (f 0) (f 1) := N.eq_line hℓ' hA hB hAB
  set p := N.linePt (f 0) (f 1) with hp
  have hpℓ : ∀ t, p t ∉ m := fun t => hmeet _ (by rw [hℓe]; exact N.linePt_mem_line _ _ t)
  -- the distance to `m` along `ℓ` is constant
  set g : ℝ → ℝ := fun t => Metric.infDist (p t) m with hg
  have hmid : ∀ t s : ℝ, 2 * g t ≤ g (t - s) + g (t + s) := by
    intro t s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hb := N.isBetween_linePt hAB (show t + s < t by linarith) (show t < t - s by linarith)
      have hd : dist (p (t + s)) (p t) = dist (p t) (p (t - s)) := by
        simp only [hp]
        rw [N.dist_linePt hAB, N.dist_linePt hAB]
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        ring
      have := N.two_mul_infDist_le hm (hpℓ _) (hpℓ _) (hpℓ _) hb hd
      simp only [hg]
      linarith
    · rw [hs, sub_zero, add_zero]
      linarith
    · have hb := N.isBetween_linePt hAB (show t - s < t by linarith) (show t < t + s by linarith)
      have hd : dist (p (t - s)) (p t) = dist (p t) (p (t + s)) := by
        simp only [hp]
        rw [N.dist_linePt hAB, N.dist_linePt hAB]
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        ring
      exact N.two_mul_infDist_le hm (hpℓ _) (hpℓ _) (hpℓ _) hb hd
  have hbdd : ∀ t, g t ≤ C := by
    intro t
    obtain ⟨Y, hY, hXY⟩ := hC (p t) (by rw [hℓe]; exact N.linePt_mem_line _ _ t)
    exact (Metric.infDist_le_dist_of_mem hY).trans hXY
  have hconst : ∀ t, g t = g 0 := fun t => eq_of_midpoint_convex_of_bddAbove hmid hbdd t 0
  -- three points and their feet
  set X := p 0
  set M := p 1
  set Y := p 2
  have hb : IsBetween X M Y := N.isBetween_linePt hAB (by norm_num) (by norm_num)
  have hXℓ : X ∈ ℓ := by rw [hℓe]; exact N.linePt_mem_line _ _ 0
  have hMℓ : M ∈ ℓ := by rw [hℓe]; exact N.linePt_mem_line _ _ 1
  have hYℓ : Y ∈ ℓ := by rw [hℓe]; exact N.linePt_mem_line _ _ 2
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hm (hpℓ 0)
  obtain ⟨H, hH, hHr⟩ := N.exists_foot hm (hpℓ 1)
  obtain ⟨G, hG, hGr⟩ := N.exists_foot hm (hpℓ 2)
  have dX : dist X F = g 0 := (N.infDist_eq_dist_foot hm hF hFr).symm
  have dM : dist M H = g 0 := by rw [← hconst 1]; exact (N.infDist_eq_dist_foot hm hH hHr).symm
  have dY : dist Y G = g 0 := by rw [← hconst 2]; exact (N.infDist_eq_dist_foot hm hG hGr).symm
  have hXM : X ≠ M := hb.1.symm
  have hMY : M ≠ Y := hb.2.1
  have hXY : X ≠ Y := hb.ne
  have hFH := N.foot_ne hℓ' hm hmeet hXℓ hMℓ hXM hF hFr hH hHr
  have hHG := N.foot_ne hℓ' hm hmeet hMℓ hYℓ hMY hH hHr hG hGr
  have hFG := N.foot_ne hℓ' hm hmeet hXℓ hYℓ hXY hF hFr hG hGr
  have hXF : X ≠ F := fun e => hmeet X hXℓ (e ▸ hF)
  have hMH : M ≠ H := fun e => hmeet M hMℓ (e ▸ hH)
  have hYG : Y ≠ G := fun e => hmeet Y hYℓ (e ▸ hG)
  have hMF : M ≠ F := fun e => hmeet M hMℓ (e ▸ hF)
  have hXH : X ≠ H := fun e => hmeet X hXℓ (e ▸ hH)
  have hMG : M ≠ G := fun e => hmeet M hMℓ (e ▸ hG)
  have hYH : Y ≠ H := fun e => hmeet Y hYℓ (e ▸ hH)
  have hXG : X ≠ G := fun e => hmeet X hXℓ (e ▸ hG)
  have hYF : Y ≠ F := fun e => hmeet Y hYℓ (e ▸ hF)
  -- right angles at the feet
  have rXH : N.uangle X F H = π / 2 := hFr H hH (Ne.symm hFH)
  have rXG : N.uangle X F G = π / 2 := hFr G hG (Ne.symm hFG)
  have rMF : N.uangle F H M = π / 2 := (N.uangle_comm hFH hMH).trans (hHr F hF hFH)
  have rMG : N.uangle M H G = π / 2 := hHr G hG (Ne.symm hHG)
  have rYH : N.uangle H G Y = π / 2 := (N.uangle_comm hHG hYG).trans (hGr H hH hHG)
  have rYF : N.uangle F G Y = π / 2 := (N.uangle_comm hFG hYG).trans (hGr F hF hFG)
  -- the three Saccheri quadrangles
  have s1 := N.saccheri_uangle_eq hFH (Ne.symm hXF) (Ne.symm hMH) hXM rXH rMF
    (by rw [dist_comm F X, dX, dist_comm H M, dM])
  have s2 := N.saccheri_uangle_eq hHG (Ne.symm hMH) (Ne.symm hYG) hMY rMG rYH
    (by rw [dist_comm H M, dM, dist_comm G Y, dY])
  have s3 := N.saccheri_uangle_eq hFG (Ne.symm hXF) (Ne.symm hYG) hXY rXG rYF
    (by rw [dist_comm F X, dX, dist_comm G Y, dY])
  have ray1 : N.uangle F X M = N.uangle F X Y :=
    N.uangle_ray_right (Ne.symm hXF) (Ne.symm hXY) (N.isBetween_rays hb).1 (Ne.symm hXM)
  have ray2 : N.uangle G Y M = N.uangle G Y X :=
    N.uangle_ray_right (Ne.symm hYG) hXY (N.isBetween_rays hb.symm).1 hMY
  have hHl : H ∉ N.line X Y := by
    rw [← N.eq_line hℓ' hXℓ hYℓ hXY]
    exact fun h => hmeet H h hH
  have sup := (N.uangle_add_uangle_of_isBetween hb hHl).1
  have c1 : N.uangle X M H = N.uangle H M X := N.uangle_comm hXM (Ne.symm hMH)
  have hα : N.uangle F X M = π / 2 := by linarith
  have hβ : N.uangle H M X = π / 2 := by linarith
  refine ⟨F, H, M, X, hFH, Ne.symm hMF, Ne.symm hXF, Ne.symm hMH, Ne.symm hXH, hXM.symm, rMF, hβ, ?_, rXH⟩
  exact (N.uangle_comm (Ne.symm hXM) (Ne.symm hXF)).trans hα

/-- **(c) ⇒ `Z`.** -/
theorem allZeroDefect_of_boundedDistantLines (h : N.BoundedDistantLines) : N.AllZeroDefect :=
  N.allZeroDefect_of_hasRectangle (N.hasRectangle_of_boundedDistantLines h)

end NeutralPlane

end Neutral

end UndergradKB.Geometry
