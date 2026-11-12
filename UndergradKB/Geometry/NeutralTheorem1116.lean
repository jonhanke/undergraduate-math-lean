import UndergradKB.Geometry.NeutralSimilarity
import UndergradKB.Geometry.NeutralBounded
import UndergradKB.Geometry.NeutralInradius
import UndergradKB.Common.Attr

/-! # Theorem 11.16 for every neutral plane (Petrunin, Chapter 11, p. 88)

A neutral plane (Axioms I-IV) is Euclidean (satisfies Axiom V) iff one of the conditions (a)-(f) holds. With
`Z` = every triangle has zero defect (`NeutralPlane.AllZeroDefect`), we prove:

* Axiom V ⇒ (e): scaling a triangle by `2` keeps its angles, so the defect of the big triangle equals that of the
  small one, while additivity of the defect (Exercise 11.12) adds two nonnegative defects; one of them must vanish;
* `Z` ⇒ Axiom V (`NeutralSimilarity`);
* (a), (b), (e), (f) ⇔ `Z` (`NeutralParallels`);
* `Z` ⇒ (c): the lines through two opposite sides of a rectangle stay at bounded distance (a quadrangle with three
  right angles is a rectangle under `Z`, by the oriented angle sum); (c) ⇒ (f) in `NeutralBounded`;
* `Z` ⇒ (d): Axiom V scales a triangle together with the distance from an interior point to its sides;
  (d) ⇒ (e) in `NeutralInradius`.

The statement `theorem_11_16` collects the equivalences. -/

namespace UndergradKB.Geometry

open Real

section Neutral

variable {P : Type*} [MetricSpace P] (N : NeutralPlane P)

namespace NeutralPlane

include N in
/-- A point `X` of `[OA)` with `OX = 2·OA` has `A` between `O` and `X`. -/
private theorem isBetween_of_double {O A X : P} (hOA : O ≠ A) (hX : X ∈ metricHalfLine O A)
    (hd : dist O X = 2 * dist O A) : IsBetween O A X := by
  have hpos := dist_pos.2 hOA
  have hAX : dist A X = dist O A := by
    rw [N.dist_of_mem_metricHalfLine hOA hX, hd, abs_of_nonpos (by linarith)]
    ring
  have hOX : O ≠ X := by
    intro e
    rw [← e, dist_self] at hd
    linarith
  have hAl : A ∈ N.line O X := by
    have hXl : X ∈ N.line O A := N.metricHalfLine_subset_line hOA hX
    rw [N.line_eq_of_mem hOA (N.left_mem_line O A) hXl hOX]
    exact N.right_mem_line O A
  refine N.isBetween_of_mem_line hOX hAl hOA.symm ?_ (by rw [hd]; linarith) (by rw [hAX, hd]; linarith)
  intro e
  rw [e, dist_self] at hAX
  linarith

/-- **Axiom V ⇒ (e).** Scale a nondegenerate triangle `ABC` by `2` from `A` to `AB'C'`: the two triangles have
the same angles, hence the same defect, while the big one splits into `ABC`, `CC'B` and `BB'C'` (Exercise 11.12);
the defects are nonnegative, so `BB'C'` has zero defect. -/
theorem zeroDefectTriangle_of_axiomV (h : N.AxiomV) : N.ZeroDefectTriangle := by
  obtain ⟨A, B, C, ⟨hAB, hBC, hCA⟩, hnd⟩ := N.exists_nondegenerate
  have hAC : A ≠ C := hCA.symm
  obtain ⟨B', ⟨hB'r, hB'd⟩, -⟩ :=
    N.existsUnique_mem_metricHalfLine_dist hAB (by positivity : (0 : ℝ) ≤ 2 * dist A B)
  obtain ⟨C', ⟨hC'r, hC'd⟩, -⟩ :=
    N.existsUnique_mem_metricHalfLine_dist hAC (by positivity : (0 : ℝ) ≤ 2 * dist A C)
  obtain ⟨-, h2, h3⟩ := h A B C B' C' 2 two_pos hAB hAC hBC hB'r hC'r hB'd hC'd
  have hbB := N.isBetween_of_double hAB hB'r hB'd
  have hbC := N.isBetween_of_double hAC hC'r hC'd
  have hAB' : A ≠ B' := hbB.ne
  have hAC' : A ≠ C' := hbC.ne
  have hlB : N.line A B' = N.line A B :=
    N.line_eq_of_mem hAB (N.left_mem_line A B) (N.metricHalfLine_subset_line hAB hB'r) hAB'
  have hlC : N.line A C' = N.line A C :=
    N.line_eq_of_mem hAC (N.left_mem_line A C) (N.metricHalfLine_subset_line hAC hC'r) hAC'
  have hCl : C ∉ N.line A B := fun hm => hnd ((N.degenerate_iff_mem_line hAB).2 hm)
  have hBl : B ∉ N.line A C := by
    intro hm
    apply hnd
    obtain ⟨L, hL, h1, h2, h3⟩ := (N.degenerate_iff_mem_line hAC).2 hm
    exact ⟨L, hL, h1, h3, h2⟩
  -- `C' ∉ (AB)` and `B ∉ (AC')`
  have hC'l : C' ∉ N.line A B := by
    intro hm
    apply hCl
    have : N.line A C' = N.line A B := N.line_eq_of_mem hAB (N.left_mem_line A B) hm hAC'
    rw [← this, hlC]
    exact N.right_mem_line A C
  have hB'C' : B' ≠ C' := by
    intro e
    apply hC'l
    rw [← e, ← hlB]
    exact N.right_mem_line A B'
  have hBC' : B ≠ C' := by
    intro e
    apply hC'l
    rw [← e]
    exact N.right_mem_line A B
  have hCB' : C ≠ B' := by
    intro e
    apply hCl
    rw [e, ← hlB]
    exact N.right_mem_line A B'
  -- equal defects
  have hdef : N.defect A B' C' = N.defect A B C := by
    unfold NeutralPlane.defect
    have e1 : N.uangle A B' C' = N.uangle A B C := by rw [N.uangle_def, N.uangle_def, h2]
    have e2 : N.uangle B' C' A = N.uangle B C A := by
      rw [N.uangle_comm hB'C' hAC', N.uangle_comm hBC hAC.symm.symm, N.uangle_def, N.uangle_def, h3]
    have e3 : N.uangle C' A B' = N.uangle C A B := by
      rw [N.uangle_ray_right hAC'.symm hAB.symm hB'r hAB'.symm,
        N.uangle_ray_left hAC.symm hC'r hAC'.symm hAB.symm]
    rw [e1, e2, e3]
  -- decompositions
  have hC'l' : C' ∉ N.line A B' := by rw [hlB]; exact hC'l
  have d1 := N.defect_add hbB hC'l'
  have hBl' : B ∉ N.line A C' := by rw [hlC]; exact hBl
  have d2 := N.defect_add hbC hBl'
  have p1 := N.defect_perm1 (A := A) (B := B) (C := C') ⟨hAB, hBC', hAC'.symm⟩
  have p2 := N.defect_perm1 (A := A) (B := B) (C := C) ⟨hAB, hBC, hCA⟩
  have n1 := N.defect_nonneg (A := C) (B := C') (C := B) ⟨hbC.2.1, hBC'.symm, hBC⟩
  have n2 := N.defect_nonneg (A := B) (B := B') (C := C') ⟨hbB.2.1, hB'C', hBC'.symm⟩
  have hz : N.defect B B' C' = 0 := by linarith
  refine ⟨B, B', C', ⟨hbB.2.1, hB'C', hBC'.symm⟩, ?_, hz⟩
  intro hd
  apply hC'l
  rw [← hlB, ← N.line_eq_of_mem hAB' (N.mem_line_of_isBetween hbB) (N.right_mem_line A B') hbB.2.1]
  exact (N.degenerate_iff_mem_line hbB.2.1).1 hd

/-- `Z` ⇔ Axiom V. -/
theorem allZeroDefect_iff_axiomV : N.AllZeroDefect ↔ N.AxiomV :=
  ⟨N.axiomV_of_allZeroDefect, fun h =>
    N.allZeroDefect_of_hasRectangle (N.hasRectangle_of_zeroDefectTriangle (N.zeroDefectTriangle_of_axiomV h))⟩

/-- A right angle is an angle `θ` with `2θ = π`. -/
private theorem two_nsmul_of_uangle {A O B : P} (h : N.uangle A O B = π / 2) :
    (2 : ℕ) • N.angle A O B = π := by
  rw [N.uangle_def] at h
  apply Real.Angle.two_nsmul_eq_pi_iff.2
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ π / 2)).1 h with e | e
  · left
    rw [← Real.Angle.coe_toReal (N.angle A O B), e]
  · right
    rw [← Real.Angle.coe_toReal (N.angle A O B), e, neg_div]

private theorem uangle_of_two_nsmul {A O B : P} (h : (2 : ℕ) • N.angle A O B = π) :
    N.uangle A O B = π / 2 := by
  rw [N.uangle_def]
  rcases Real.Angle.two_nsmul_eq_pi_iff.1 h with e | e
  · rw [e, Real.Angle.toReal_pi_div_two, abs_of_pos (by positivity)]
  · rw [e, Real.Angle.toReal_neg_pi_div_two, neg_div, abs_neg, abs_of_pos (by positivity)]

/-- Under `Z`, a quadrangle `ABCD` with right angles at `A`, `B` and `D` has a right angle at `C` (the oriented
angles of the two triangles cut off by the diagonal `[BD]` add up to `2π`; no convexity is needed). -/
theorem uangle_eq_pi_div_two_of_three_right (h : N.AllZeroDefect) {A B C D : P} (hAB : A ≠ B) (hBC : B ≠ C)
    (hCD : C ≠ D) (hDA : D ≠ A) (hA : N.uangle D A B = π / 2) (hB : N.uangle A B C = π / 2)
    (hD : N.uangle C D A = π / 2) : N.uangle B C D = π / 2 := by
  have hBD : B ≠ D := by
    intro e
    rw [e, N.uangle_def, N.angle_self hDA] at hA
    simp at hA
    linarith [Real.pi_pos]
  have t1 := N.angle_add_angle_add_angle_of_allZeroDefect h (A := A) (B := B) (C := D) ⟨hAB, hBD, hDA⟩
  have t2 := N.angle_add_angle_add_angle_of_allZeroDefect h (A := C) (B := D) (C := B) ⟨hCD, hBD.symm, hBC⟩
  have iB := N.axiomIIIb B A D C hAB hBD.symm hBC.symm
  have iD := N.axiomIIIb D C B A hCD hBD hDA.symm
  have hsum : N.angle B C D = -(N.angle D A B + N.angle A B C + N.angle C D A) := by
    rw [← iB, ← iD]
    have h2 : (N.angle A B D + N.angle B D A + N.angle D A B) +
        (N.angle C D B + N.angle D B C + N.angle B C D) = 0 := by
      rw [t1, t2]
      exact Real.Angle.coe_pi_add_coe_pi
    rw [eq_neg_iff_add_eq_zero, ← h2]
    abel
  apply N.uangle_of_two_nsmul
  rw [hsum, smul_neg, smul_add, smul_add, N.two_nsmul_of_uangle hA, N.two_nsmul_of_uangle hB,
    N.two_nsmul_of_uangle hD, Real.Angle.coe_pi_add_coe_pi, zero_add, Real.Angle.neg_coe_pi]

/-- **`Z` ⇒ (c).** Let `ℓ` and `m` be perpendicular to `[AD]` at `A` and at `D`. The foot `F` on `m` of a point
`X ≠ A` of `ℓ` makes a quadrangle `DAXF` with right angles at `D`, `A`, `F`, hence a rectangle, so `XF = AD`. -/
theorem boundedDistantLines_of_allZeroDefect (h : N.AllZeroDefect) : N.BoundedDistantLines := by
  obtain ⟨A, B, hAB⟩ := N.axiomI
  obtain ⟨D, hADd, hDang⟩ := N.exists_angle_eq_pi_div_two hAB.symm one_pos
  have hDA : D ≠ A := by
    intro e
    rw [e, dist_self] at hADd
    exact zero_ne_one hADd
  have hrD : N.uangle B A D = π / 2 :=
    N.uangle_of_angle_eq_coe (by positivity) (by linarith [Real.pi_pos]) hDang
  obtain ⟨E, hDEd, hEang⟩ := N.exists_angle_eq_pi_div_two hDA.symm one_pos
  have hED : E ≠ D := by
    intro e
    rw [e, dist_self] at hDEd
    exact zero_ne_one hDEd
  have hrE : N.uangle A D E = π / 2 :=
    N.uangle_of_angle_eq_coe (by positivity) (by linarith [Real.pi_pos]) hEang
  have hrE' : N.uangle E D A = π / 2 := (N.uangle_comm hED hDA.symm).trans hrE
  have hdisj : Disjoint (N.line A B) (N.line D E) :=
    N.disjoint_of_perp_perp hDA.symm hAB.symm hED hrD hrE'
  have hAm : A ∉ N.line D E := Set.disjoint_left.1 hdisj (N.left_mem_line A B)
  have hDl : D ∉ N.line A B := fun hm => Set.disjoint_left.1 hdisj hm (N.left_mem_line D E)
  have hm := N.isLine_line hED.symm
  refine ⟨N.line A B, N.line D E, N.isLine_line hAB, hm, fun e => hAm (e ▸ N.left_mem_line A B),
    dist A D, fun X hX => ?_⟩
  by_cases hXA : X = A
  · exact ⟨D, N.left_mem_line D E, by rw [hXA]⟩
  have hXm : X ∉ N.line D E := Set.disjoint_left.1 hdisj hX
  obtain ⟨F, hF, hFr⟩ := N.exists_foot hm hXm
  refine ⟨F, hF, le_of_eq ?_⟩
  have hDX : D ≠ X := fun e => hDl (e ▸ hX)
  have hFD : F ≠ D := by
    intro e
    have h1 : N.uangle E D X = π / 2 := by
      have := hFr E (N.right_mem_line D E) (by rw [e]; exact hED)
      rw [e] at this
      exact (N.uangle_comm hED (Ne.symm hDX)).trans this
    have hX' : X ∈ N.line D A :=
      N.mem_line_of_perp hm (N.right_mem_line D E) (N.left_mem_line D E) hED hDA.symm
        (Ne.symm hDX) hrE' h1
    have hl : N.line A B ≠ N.line D A := fun e' => hDl (e' ▸ N.left_mem_line D A)
    exact hXA (N.eq_of_mem_line_of_mem_line (N.isLine_line hAB) (N.isLine_line hDA) hl hX hX'
      (N.left_mem_line A B) (N.right_mem_line D A))
  have hXF : X ≠ F := fun e => hXm (e ▸ hF)
  have hAF : A ≠ F := fun e => hAm (e ▸ hF)
  have r1 : N.uangle F D A = π / 2 :=
    N.uangle_eq_pi_div_two_of_mem_line hED hDA.symm hrE' hF hFD
  have r2 : N.uangle D A X = π / 2 := by
    have := N.uangle_eq_pi_div_two_of_mem_line hAB.symm hDA hrD hX hXA
    exact (N.uangle_comm hDA (Ne.symm hXA).symm).trans this
  have r3 : N.uangle X F D = π / 2 := hFr D (N.left_mem_line D E) hFD.symm
  have r4 := N.uangle_eq_pi_div_two_of_three_right h hDA (Ne.symm hXA) hXF hFD r1 r2 r3
  have hR : N.IsRectangle D A X F := ⟨hDA, hDX, hFD.symm, Ne.symm hXA, hAF, hXF, r2, r4, r3, r1⟩
  rw [← (IsRectangle.dist_eq N hR).1, dist_comm]

/-! ### `Z` ⇒ (d) -/

/-- A point `X` of a line through the foot `F` of a perpendicular from `I` is at least as far from `I` as `F`. -/
private theorem dist_ge_of_perp {I F Y X : P} (hIF : I ≠ F) (hYF : Y ≠ F) (hr : N.uangle I F Y = π / 2)
    (hX : X ∈ N.line F Y) : dist I F ≤ dist I X := by
  by_cases hXF : X = F
  · rw [hXF]
  have h1 := N.uangle_eq_pi_div_two_of_mem_line hYF hIF ((N.uangle_comm hYF hIF).trans hr) hX hXF
  exact (N.dist_lt_hypotenuse hIF hXF ((N.uangle_comm hIF hXF).trans h1)).le

include N in
private theorem linePt_ray {O Q : P} (h : O ≠ Q) {t : ℝ} (ht : 0 < t) :
    N.linePt O Q t ∈ metricHalfLine O Q ∧ dist O (N.linePt O Q t) = t ∧ N.linePt O Q t ≠ O := by
  have hd : dist O (N.linePt O Q t) = t := by rw [N.dist_left_linePt h, abs_of_pos ht]
  refine ⟨?_, hd, ?_⟩
  · rw [N.metricHalfLine_eq_linePt h]
    exact ⟨t, ht.le, rfl⟩
  · intro e
    rw [e, dist_self] at hd
    linarith

/-- Under Axiom V, scaling from `I` keeps a right angle at the foot `F`. -/
private theorem scaled_perp (hV : N.AxiomV) {I F Y F' Y' : P} {k : ℝ} (hk : 0 < k) (hIF : I ≠ F) (hIY : I ≠ Y)
    (hY : Y = F ∨ N.uangle I F Y = π / 2) (hF' : F' ∈ metricHalfLine I F) (hdF : dist I F' = k * dist I F)
    (hY' : Y' ∈ metricHalfLine I Y) (hdY : dist I Y' = k * dist I Y) :
    Y' = F' ∨ (Y' ≠ F' ∧ N.uangle I F' Y' = π / 2) := by
  by_cases hFY : Y = F
  · subst hFY
    left
    obtain ⟨Z, -, hZ⟩ :=
      N.existsUnique_mem_metricHalfLine_dist hIF (by positivity : (0 : ℝ) ≤ k * dist I Y)
    rw [hZ Y' ⟨hY', hdY⟩, hZ F' ⟨hF', hdF⟩]
  have hr := hY.resolve_left hFY
  obtain ⟨hd, hang, -⟩ := hV I F Y F' Y' k hk hIF hIY (Ne.symm hFY) hF' hY' hdF hdY
  right
  refine ⟨?_, ?_⟩
  · intro e
    rw [e, dist_self] at hd
    have := mul_pos hk (dist_pos.2 (Ne.symm hFY))
    linarith
  · rw [N.uangle_def, ← hang]
    exact hr

/-- Under Axiom V, scaling the side `[AB]` from `I` by `k` scales the distance from `I` to its line. -/
private theorem side_bound (hV : N.AxiomV) {I A B F A' B' : P} {k : ℝ} (hk : 0 < k) (hIA : I ≠ A)
    (hIB : I ≠ B) (hIF : I ≠ F) (hA : A = F ∨ N.uangle I F A = π / 2) (hB : B = F ∨ N.uangle I F B = π / 2)
    (hA' : A' ∈ metricHalfLine I A) (hdA : dist I A' = k * dist I A)
    (hB' : B' ∈ metricHalfLine I B) (hdB : dist I B' = k * dist I B) (hA'B' : A' ≠ B') :
    ∀ X ∈ N.line A' B', k * dist I F ≤ dist I X := by
  have hpos : 0 < k * dist I F := mul_pos hk (dist_pos.2 hIF)
  obtain ⟨hF'r, hF'd, hF'I⟩ := N.linePt_ray hIF hpos
  set F' := N.linePt I F (k * dist I F)
  have sA := N.scaled_perp hV hk hIF hIA hA hF'r hF'd hA' hdA
  have sB := N.scaled_perp hV hk hIF hIB hB hF'r hF'd hB' hdB
  have hIF' : I ≠ F' := Ne.symm hF'I
  intro X hX
  rw [← hF'd]
  rcases sA with eA | ⟨nA, rA⟩ <;> rcases sB with eB | ⟨nB, rB⟩
  · exact absurd (eA.trans eB.symm) hA'B'
  · rw [eA] at hX
    exact N.dist_ge_of_perp hIF' nB rB hX
  · rw [eB, N.line_comm] at hX
    exact N.dist_ge_of_perp hIF' nA rA hX
  · have hB'm : B' ∈ N.line F' A' :=
      N.mem_line_of_perp (N.isLine_line hF'I) (N.right_mem_line F' I) (N.left_mem_line F' I) hIF' nA nB rA rB
    rw [N.line_eq_of_mem (Ne.symm nA) (N.right_mem_line F' A') hB'm hA'B'] at hX
    exact N.dist_ge_of_perp hIF' nA rA hX

/-- A side `[XY]` seen from `I ∉ (XY)`: some `d > 0` such that, scaled by `k` from `I`, its line stays at
distance `≥ k·d` from `I`. -/
private theorem side_data (hV : N.AxiomV) {I X Y : P} (hX : X ≠ I) (hY : Y ≠ I) (hXY : X ≠ Y)
    (hI : I ∉ N.line X Y) :
    ∃ d : ℝ, 0 < d ∧ ∀ k : ℝ, 0 < k → ∀ X' Y' : P, X' ∈ metricHalfLine I X → dist I X' = k * dist I X →
      Y' ∈ metricHalfLine I Y → dist I Y' = k * dist I Y → X' ≠ Y' → ∀ Z ∈ N.line X' Y', k * d ≤ dist I Z := by
  obtain ⟨F, hF, hFr⟩ := N.exists_foot (N.isLine_line hXY) hI
  have hIF : I ≠ F := fun e => hI (e ▸ hF)
  refine ⟨dist I F, dist_pos.2 hIF, fun k hk X' Y' hX' hdX hY' hdY hX'Y' => ?_⟩
  have hXF : X = F ∨ N.uangle I F X = π / 2 := by
    by_cases e : X = F
    · exact Or.inl e
    · exact Or.inr (hFr X (N.left_mem_line X Y) e)
  have hYF : Y = F ∨ N.uangle I F Y = π / 2 := by
    by_cases e : Y = F
    · exact Or.inl e
    · exact Or.inr (hFr Y (N.right_mem_line X Y) e)
  exact N.side_bound hV hk (Ne.symm hX) (Ne.symm hY) hIF hXF hYF hX' hdX hY' hdY hX'Y'

private theorem not_mem_line_of_angle {X I Y : P} (hX : X ≠ I) (hY : Y ≠ I) (h0 : N.angle X I Y ≠ 0)
    (hπ : N.angle X I Y ≠ π) : X ≠ Y ∧ I ∉ N.line X Y := by
  have hXY : X ≠ Y := by
    rintro rfl
    exact h0 (N.angle_self hX)
  refine ⟨hXY, fun hm => ?_⟩
  obtain ⟨L, hL, h1, h2, h3⟩ := (N.degenerate_iff_mem_line hXY).2 hm
  rcases (N.degenerate_iff_angle hX hY).1 ⟨L, hL, h1, h3, h2⟩ with e | e
  · exact h0 e
  · exact hπ e

private theorem angle_linePt {I Q R : P} (hQ : I ≠ Q) (hR : I ≠ R) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    N.angle (N.linePt I Q t) I (N.linePt I R s) = N.angle Q I R := by
  obtain ⟨h1, -, h3⟩ := N.linePt_ray hQ ht
  obtain ⟨g1, -, g3⟩ := N.linePt_ray hR hs
  rw [N.angle_ray_left (Ne.symm hQ) h1 h3 g3, N.angle_ray_right (Ne.symm hQ) (Ne.symm hR) g1 g3]

/-- **Axiom V ⇒ (d).** Three half-lines from `I` at angles `2π/3`; the points at distance `k` on them form a
triangle containing `I`, and by Axiom V the distance from `I` to its sides grows linearly in `k`. -/
theorem arbitrarilyLargeInradius_of_axiomV (hV : N.AxiomV) : N.ArbitrarilyLargeInradius := by
  obtain ⟨I, A₀, hIA⟩ := N.axiomI
  set θ : Real.Angle := ((2 * π / 3 : ℝ) : Real.Angle) with hθ
  obtain ⟨D, hDI, hD, -⟩ := N.axiomIIIa I A₀ (Ne.symm hIA) θ
  obtain ⟨E, hEI, hE, -⟩ := N.axiomIIIa I A₀ (Ne.symm hIA) (-θ)
  have hθr : θ.toReal = 2 * π / 3 :=
    Real.Angle.toReal_coe_eq_self_iff.2 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hθ0 : θ ≠ 0 := fun e => by
    rw [e, Real.Angle.toReal_zero] at hθr
    linarith [Real.pi_pos]
  have hθπ : θ ≠ π := fun e => by
    rw [e, Real.Angle.toReal_pi] at hθr
    linarith [Real.pi_pos]
  have h3 : θ + θ + θ = 0 := by
    rw [hθ, ← Real.Angle.coe_add, ← Real.Angle.coe_add,
      show 2 * π / 3 + 2 * π / 3 + 2 * π / 3 = 2 * π by ring, Real.Angle.coe_two_pi]
  have hAI : A₀ ≠ I := Ne.symm hIA
  have aDE : N.angle D I E = θ := by
    rw [← N.axiomIIIb I D A₀ E hDI hAI hEI, N.angle_rev hDI hAI, hD, hE]
    calc -θ + -θ = -θ + -θ + (θ + θ + θ) := by rw [h3, add_zero]
      _ = θ := by abel
  have aEA : N.angle E I A₀ = θ := by rw [N.angle_rev hEI hAI, hE, neg_neg]
  have ang : ∀ t s : ℝ, 0 < t → 0 < s →
      N.angle (N.linePt I A₀ t) I (N.linePt I D s) = θ ∧ N.angle (N.linePt I D t) I (N.linePt I E s) = θ ∧
        N.angle (N.linePt I E t) I (N.linePt I A₀ s) = θ := fun t s ht hs =>
    ⟨by rw [N.angle_linePt hIA (Ne.symm hDI) ht hs, hD],
      by rw [N.angle_linePt (Ne.symm hDI) (Ne.symm hEI) ht hs, aDE],
      by rw [N.angle_linePt (Ne.symm hEI) hIA ht hs, aEA]⟩
  have ray : ∀ {Q : P}, I ≠ Q → ∀ t : ℝ, 0 < t →
      N.linePt I Q t ∈ metricHalfLine I (N.linePt I Q 1) ∧ dist I (N.linePt I Q t) = t * dist I (N.linePt I Q 1) ∧
        N.linePt I Q t ≠ I := fun {Q} hQ t ht => by
    obtain ⟨h1, h2, h3⟩ := N.linePt_ray hQ ht
    obtain ⟨g1, g2, g3⟩ := N.linePt_ray hQ one_pos
    refine ⟨?_, by rw [h2, g2, mul_one], h3⟩
    rw [N.metricHalfLine_eq_of_mem hQ g1 g3]
    exact h1
  have nm : ∀ {X Y : P}, X ≠ I → Y ≠ I → N.angle X I Y = θ → X ≠ Y ∧ I ∉ N.line X Y :=
    fun hX hY h => N.not_mem_line_of_angle hX hY (by rw [h]; exact hθ0) (by rw [h]; exact hθπ)
  obtain ⟨-, -, a1I⟩ := N.linePt_ray hIA one_pos
  obtain ⟨-, -, b1I⟩ := N.linePt_ray (Ne.symm hDI) one_pos
  obtain ⟨-, -, c1I⟩ := N.linePt_ray (Ne.symm hEI) one_pos
  obtain ⟨a1, b1, c1⟩ := ang 1 1 one_pos one_pos
  obtain ⟨d1, hd1, H1⟩ := N.side_data hV a1I b1I (nm a1I b1I a1).1 (nm a1I b1I a1).2
  obtain ⟨d2, hd2, H2⟩ := N.side_data hV b1I c1I (nm b1I c1I b1).1 (nm b1I c1I b1).2
  obtain ⟨d3, hd3, H3⟩ := N.side_data hV c1I a1I (nm c1I a1I c1).1 (nm c1I a1I c1).2
  intro r
  set k := |r| / d1 + |r| / d2 + |r| / d3 + 1 with hk
  have hk0 : 0 < k := by positivity
  have b1' : |r| ≤ k * d1 := by
    have : k * d1 = |r| / d1 * d1 + (|r| / d2 + |r| / d3 + 1) * d1 := by rw [hk]; ring
    rw [this, div_mul_cancel₀ _ hd1.ne']
    have : 0 ≤ (|r| / d2 + |r| / d3 + 1) * d1 := by positivity
    linarith
  have b2' : |r| ≤ k * d2 := by
    have : k * d2 = |r| / d2 * d2 + (|r| / d1 + |r| / d3 + 1) * d2 := by rw [hk]; ring
    rw [this, div_mul_cancel₀ _ hd2.ne']
    have : 0 ≤ (|r| / d1 + |r| / d3 + 1) * d2 := by positivity
    linarith
  have b3' : |r| ≤ k * d3 := by
    have : k * d3 = |r| / d3 * d3 + (|r| / d1 + |r| / d2 + 1) * d3 := by rw [hk]; ring
    rw [this, div_mul_cancel₀ _ hd3.ne']
    have : 0 ≤ (|r| / d1 + |r| / d2 + 1) * d3 := by positivity
    linarith
  obtain ⟨ra, da, aI⟩ := ray hIA k hk0
  obtain ⟨rb, db, bI⟩ := ray (Ne.symm hDI) k hk0
  obtain ⟨rc, dc, cI⟩ := ray (Ne.symm hEI) k hk0
  obtain ⟨ab, bc, ca⟩ := ang k k hk0 hk0
  set A := N.linePt I A₀ k
  set B := N.linePt I D k
  set C := N.linePt I E k
  obtain ⟨hAB, hIAB⟩ := nm aI bI ab
  obtain ⟨hBC, hIBC⟩ := nm bI cI bc
  obtain ⟨hCA, hICA⟩ := nm cI aI ca
  have hu : ∀ {X Y : P}, N.angle X I Y = θ → N.uangle X I Y = 2 * π / 3 := fun h => by
    rw [N.uangle_def, h, hθr, abs_of_pos (by positivity)]
  have uab := hu ab
  have ubc := hu bc
  have uca := hu ca
  have uba : N.uangle B I A = 2 * π / 3 := (N.uangle_comm bI aI).trans uab
  have ucb : N.uangle C I B = 2 * π / 3 := (N.uangle_comm cI bI).trans ubc
  have uac : N.uangle A I C = 2 * π / 3 := (N.uangle_comm aI cI).trans uca
  refine ⟨A, B, C, ⟨hAB, hBC, hCA⟩, ?_, I, ?_, ?_⟩
  · rintro ⟨L, hL, hA, hB, hC⟩
    rcases hL.isBetween_trichotomy hA hB hC hAB hBC hCA with h | h | h
    · have := (N.isBetween_angle_sign_and_uangle h hIBC).2.2
      rw [uba, uac, ubc] at this
      linarith [Real.pi_pos]
    · have hI' : I ∉ N.line A C := by rw [N.line_comm]; exact hICA
      have := (N.isBetween_angle_sign_and_uangle h hI').2.2
      rw [uab, ubc, uac] at this
      linarith [Real.pi_pos]
    · have := (N.isBetween_angle_sign_and_uangle h hIAB).2.2
      rw [uac, ucb, uab] at this
      linarith [Real.pi_pos]
  · refine ⟨by rw [ab, bc], by rw [bc, ca], ?_⟩
    rw [ab]
    intro e
    rcases Real.Angle.sign_eq_zero_iff.1 e with e | e
    · exact hθ0 e
    · exact hθπ e
  · intro L hL hcase X hX
    have hr := le_abs_self r
    rcases hcase with ⟨hA, hB⟩ | ⟨hB, hC⟩ | ⟨hC, hA⟩
    · rw [N.eq_line hL hA hB hAB] at hX
      have := H1 k hk0 A B ra da rb db hAB X hX
      linarith
    · rw [N.eq_line hL hB hC hBC] at hX
      have := H2 k hk0 B C rb db rc dc hBC X hX
      linarith
    · rw [N.eq_line hL hC hA hCA] at hX
      have := H3 k hk0 C A rc dc ra da hCA X hX
      linarith

/-- **`Z` ⇒ (d).** -/
theorem arbitrarilyLargeInradius_of_allZeroDefect (h : N.AllZeroDefect) : N.ArbitrarilyLargeInradius :=
  N.arbitrarilyLargeInradius_of_axiomV (N.axiomV_of_allZeroDefect h)

/-- **Theorem 11.16** for every neutral plane: the plane is Euclidean (satisfies Axiom V) iff (a) there is a line
and a point off it with exactly one parallel through the point, iff (b) every nondegenerate triangle can be
circumscribed, iff (c) two distinct lines lie at bounded distance from each other, iff (d) there are triangles of
arbitrarily large inradius, iff (e) some nondegenerate triangle has zero defect, iff (f) there is a rectangle. -/
@[kb "petrunin2025" "Theorem 11.16, p. 88"]
theorem theorem_11_16 :
    (N.AxiomV ↔ N.OnlyOneParallel) ∧ (N.AxiomV ↔ N.AllTrianglesCircumscribable) ∧
      (N.AxiomV ↔ N.BoundedDistantLines) ∧ (N.AxiomV ↔ N.ArbitrarilyLargeInradius) ∧
        (N.AxiomV ↔ N.ZeroDefectTriangle) ∧ (N.AxiomV ↔ N.HasRectangle) := by
  have hZ := N.allZeroDefect_iff_axiomV
  have he : N.ZeroDefectTriangle ↔ N.AllZeroDefect :=
    ⟨fun h => N.allZeroDefect_of_hasRectangle (N.hasRectangle_of_zeroDefectTriangle h),
      N.zeroDefectTriangle_of_allZeroDefect⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hZ]
    exact ⟨N.onlyOneParallel_of_allZeroDefect, fun h => he.1 (N.zeroDefectTriangle_of_onlyOneParallel h)⟩
  · rw [← hZ]
    exact ⟨N.allTrianglesCircumscribable_of_allZeroDefect, fun h =>
      he.1 (N.zeroDefectTriangle_of_onlyOneParallel (N.onlyOneParallel_of_allTrianglesCircumscribable h))⟩
  · rw [← hZ]
    exact ⟨N.boundedDistantLines_of_allZeroDefect, N.allZeroDefect_of_boundedDistantLines⟩
  · rw [← hZ]
    exact ⟨N.arbitrarilyLargeInradius_of_allZeroDefect, N.allZeroDefect_of_arbitrarilyLargeInradius⟩
  · rw [← hZ, he]
  · rw [← hZ]
    exact ⟨fun h => N.hasRectangle_of_zeroDefectTriangle (he.2 h), N.allZeroDefect_of_hasRectangle⟩

/-- **The remark after Theorem 11.16 (p. 88):** every neutral plane satisfies Axiom V or Axiom h-V. -/
@[kb "petrunin2025" "Remark after Theorem 11.16, p. 88"]
theorem axiomV_or_axiomHV : N.AxiomV ∨ N.AxiomHV := by
  by_cases h : N.ZeroDefectTriangle
  · exact Or.inl ((N.theorem_11_16).2.2.2.2.1.2 h)
  · exact Or.inr (N.axiomHV_of_not_zeroDefectTriangle h)

end NeutralPlane

end Neutral

end UndergradKB.Geometry
