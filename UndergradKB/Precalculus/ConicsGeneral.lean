import UndergradKB.Precalculus.ConicsClassify

/-!
# Focus-directrix-eccentricity classification for an arbitrary focus and directrix

Section 11.1 and Theorem 11.12 of Stitz-Zeager: the earlier file treats a focus at the pole and a vertical
directrix. Here the focus is any point `F` and the directrix is any line `a x + b y = c` not through `F`.
The proof translates the focus to the origin, normalises the line to unit normal `(cos φ, sin φ)` and a
negative constant, rotates by `φ`, and applies the special case.
-/

namespace UndergradKB.Precalculus

open Real

/-- The set `S` translated so that the point `(0, 0)` goes to `v`. -/
def transSet (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {P | (P.1 - v.1, P.2 - v.2) ∈ S}

theorem edist2_trans_left (v F P : ℝ × ℝ) :
    edist2 P (F.1 + v.1, F.2 + v.2) = edist2 (P.1 - v.1, P.2 - v.2) F := by
  unfold edist2; dsimp only; congr 1; ring

theorem edist2_trans_zero (F P : ℝ × ℝ) : edist2 P F = edist2 (P.1 - F.1, P.2 - F.2) (0, 0) := by
  unfold edist2; dsimp only; congr 1; ring

theorem transSet_ellipseSet (v F₁ F₂ : ℝ × ℝ) (d : ℝ) :
    transSet v (ellipseSet F₁ F₂ d) = ellipseSet (F₁.1 + v.1, F₁.2 + v.2) (F₂.1 + v.1, F₂.2 + v.2) d := by
  ext P
  simp only [transSet, ellipseSet, Set.mem_ofPred_eq, IsEllipsePt, edist2_trans_left]

theorem transSet_hyperbolaSet (v F₁ F₂ : ℝ × ℝ) (d : ℝ) :
    transSet v (hyperbolaSet F₁ F₂ d) = hyperbolaSet (F₁.1 + v.1, F₁.2 + v.2) (F₂.1 + v.1, F₂.2 + v.2) d := by
  ext P
  simp only [transSet, hyperbolaSet, Set.mem_ofPred_eq, IsHyperbolaPt, edist2_trans_left]

theorem edist2_trans_foci (v F₁ F₂ : ℝ × ℝ) :
    edist2 (F₁.1 + v.1, F₁.2 + v.2) (F₂.1 + v.1, F₂.2 + v.2) = edist2 F₁ F₂ := by
  unfold edist2; dsimp only; congr 1; ring

/-- Moving the focus to the origin moves the constant of the directrix. -/
theorem conicPt_translate (F : ℝ × ℝ) (a b c e : ℝ) (P : ℝ × ℝ) :
    IsConicPt F a b c e P ↔
      IsConicPt (0, 0) a b (c - a * F.1 - b * F.2) e (P.1 - F.1, P.2 - F.2) := by
  unfold IsConicPt distToLine
  rw [edist2_trans_zero F P]
  dsimp only
  have : a * (P.1 - F.1) + b * (P.2 - F.2) - (c - a * F.1 - b * F.2) = a * P.1 + b * P.2 - c := by ring
  rw [this]

/-- A line with nonzero constant has a unit normal `(cos φ, sin φ)` and a negative constant `-d`. -/
theorem conicPt_normalise {a b c : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (hc : c ≠ 0) (e : ℝ) :
    ∃ φ d : ℝ, 0 < d ∧ ∀ P : ℝ × ℝ,
      IsConicPt (0, 0) a b c e P ↔ IsConicPt (0, 0) (cos φ) (sin φ) (-d) e P := by
  set z : ℂ := ⟨a, b⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hab
    have h1 : a = 0 := congrArg Complex.re h
    have h2 : b = 0 := congrArg Complex.im h
    rw [h1, h2]; norm_num
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hρ2 : ‖z‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hx : ‖z‖ * cos (Complex.arg z) = a := Complex.norm_mul_cos_arg z
  have hy : ‖z‖ * sin (Complex.arg z) = b := Complex.norm_mul_sin_arg z
  have hs : √(a ^ 2 + b ^ 2) = ‖z‖ := by rw [← hρ2]; exact Real.sqrt_sq hρ.le
  have key : ∀ (φ k : ℝ), ‖z‖ * cos φ = a → ‖z‖ * sin φ = b → ‖z‖ * k = c →
      ∀ P : ℝ × ℝ, IsConicPt (0, 0) a b c e P ↔ IsConicPt (0, 0) (cos φ) (sin φ) k e P := by
    intro φ k h1 h2 h3 P
    unfold IsConicPt distToLine
    have h4 : cos φ ^ 2 + sin φ ^ 2 = 1 := cos_sq_add_sin_sq φ
    rw [h4, Real.sqrt_one, div_one, hs]
    have : a * P.1 + b * P.2 - c = ‖z‖ * (cos φ * P.1 + sin φ * P.2 - k) := by
      rw [← h1, ← h2, ← h3]; ring
    rw [this, abs_mul, abs_of_pos hρ, mul_div_cancel_left₀ _ hρ.ne']
  have key2 : ∀ (φ k : ℝ), ‖z‖ * cos φ = -a → ‖z‖ * sin φ = -b → ‖z‖ * k = -c →
      ∀ P : ℝ × ℝ, IsConicPt (0, 0) a b c e P ↔ IsConicPt (0, 0) (cos φ) (sin φ) k e P := by
    intro φ k h1 h2 h3 P
    unfold IsConicPt distToLine
    have h4 : cos φ ^ 2 + sin φ ^ 2 = 1 := cos_sq_add_sin_sq φ
    rw [h4, Real.sqrt_one, div_one, hs]
    have : a * P.1 + b * P.2 - c = -(‖z‖ * (cos φ * P.1 + sin φ * P.2 - k)) := by
      have : ‖z‖ * (cos φ * P.1 + sin φ * P.2 - k) = (‖z‖ * cos φ) * P.1 + (‖z‖ * sin φ) * P.2 - ‖z‖ * k := by ring
      rw [this, h1, h2, h3]; ring
    rw [this, abs_neg, abs_mul, abs_of_pos hρ, mul_div_cancel_left₀ _ hρ.ne']
  have hk : c / ‖z‖ ≠ 0 := div_ne_zero hc hρ.ne'
  have hk' : ‖z‖ * (c / ‖z‖) = c := mul_div_cancel₀ _ hρ.ne'
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · refine ⟨Complex.arg z, -(c / ‖z‖), by linarith, ?_⟩
    rw [neg_neg]
    exact key _ _ hx hy hk'
  · refine ⟨Complex.arg z + π, c / ‖z‖, hpos, fun P => ?_⟩
    apply key2
    · rw [cos_add_pi]; linarith
    · rw [sin_add_pi]; linarith
    · linarith

/-- The set of the focus-directrix condition for a unit normal and a negative constant, as a rotation. -/
theorem conicSet_rotSet (φ d e : ℝ) :
    {P | IsConicPt (0, 0) (cos φ) (sin φ) (-d) e P} = rotSet φ {P | IsConicPt (0, 0) 1 0 (-d) e P} := by
  ext P
  exact conicPt_rotate φ (-d) e P

/-- The classification for a focus at the origin and a directrix not through it. -/
theorem conic_origin_type {a b c : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (hc : c ≠ 0) (e : ℝ) :
    (0 < e → e < 1 → ∃ F₁ F₂ : ℝ × ℝ, ∃ a' : ℝ, edist2 F₁ F₂ < 2 * a' ∧
      {P | IsConicPt (0, 0) a b c e P} = ellipseSet F₁ F₂ (2 * a')) ∧
    (1 < e → ∃ F₁ F₂ : ℝ × ℝ, ∃ a' : ℝ, 0 < a' ∧ 2 * a' < edist2 F₁ F₂ ∧
      {P | IsConicPt (0, 0) a b c e P} = hyperbolaSet F₁ F₂ (2 * a')) := by
  obtain ⟨φ, d, hd, hP⟩ := conicPt_normalise hab hc e
  have hset : {P | IsConicPt (0, 0) a b c e P} =
      rotSet φ {P | IsConicPt (0, 0) 1 0 (-d) e P} := by
    rw [← conicSet_rotSet]; ext P; exact hP P
  constructor
  · intro he he1
    obtain ⟨F₁, F₂, a', ha, h⟩ := conic_eccentricity_lt_one_ellipse he he1 hd
    refine ⟨rotPt φ F₁, rotPt φ F₂, a', by rwa [edist2_rotPt], ?_⟩
    rw [hset, h, rotSet_ellipseSet]
  · intro he1
    obtain ⟨F₁, F₂, a', ha, hlt, h⟩ := conic_eccentricity_gt_one_hyperbola he1 hd
    refine ⟨rotPt φ F₁, rotPt φ F₂, a', ha, by rwa [edist2_rotPt], ?_⟩
    rw [hset, h, rotSet_hyperbolaSet]

/-- Definition 11.1 and Theorem 11.12 for any focus and directrix: for a focus `F` not on the directrix
`a x + b y = c` (`a² + b² ≠ 0`), the set of points whose distance to `F` is `e` times their distance to the
directrix is a parabola (Definition 7.3) for `e = 1`, an ellipse (Definition 7.4) for `0 < e < 1`, and a
hyperbola (Definition 7.6) for `e > 1` (PC-257). -/
@[kb "stitzzeager2013" "Definition 11.1, p. 993"]
theorem conic_focus_directrix_type {F : ℝ × ℝ} {a b c : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0)
    (hF : a * F.1 + b * F.2 ≠ c) (e : ℝ) :
    (e = 1 → {P | IsConicPt F a b c e P} = parabolaSet F a b c) ∧
    (0 < e → e < 1 → ∃ F₁ F₂ : ℝ × ℝ, ∃ a' : ℝ, edist2 F₁ F₂ < 2 * a' ∧
      {P | IsConicPt F a b c e P} = ellipseSet F₁ F₂ (2 * a')) ∧
    (1 < e → ∃ F₁ F₂ : ℝ × ℝ, ∃ a' : ℝ, 0 < a' ∧ 2 * a' < edist2 F₁ F₂ ∧
      {P | IsConicPt F a b c e P} = hyperbolaSet F₁ F₂ (2 * a')) := by
  have hc : c - a * F.1 - b * F.2 ≠ 0 := by intro h; apply hF; linarith
  have hset : {P | IsConicPt F a b c e P} =
      transSet F {P | IsConicPt (0, 0) a b (c - a * F.1 - b * F.2) e P} := by
    ext P; exact conicPt_translate F a b c e P
  obtain ⟨h1, h2⟩ := conic_origin_type hab hc e
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    ext P
    exact conic_pt_one_iff_parabola F a b c P
  · intro he he1
    obtain ⟨F₁, F₂, a', ha, h⟩ := h1 he he1
    refine ⟨(F₁.1 + F.1, F₁.2 + F.2), (F₂.1 + F.1, F₂.2 + F.2), a', ?_, ?_⟩
    · rwa [edist2_trans_foci]
    · rw [hset, h, transSet_ellipseSet]
  · intro he1
    obtain ⟨F₁, F₂, a', ha, hlt, h⟩ := h2 he1
    refine ⟨(F₁.1 + F.1, F₁.2 + F.2), (F₂.1 + F.1, F₂.2 + F.2), a', ha, ?_, ?_⟩
    · rwa [edist2_trans_foci]
    · rw [hset, h, transSet_hyperbolaSet]

end UndergradKB.Precalculus
