import UndergradKB.Precalculus.ConicsRotation

/-!
# Classification of the graph of a quadratic equation (Stitz-Zeager, Precalculus, Theorem 11.11)

What is proved: the point set of `A x^2 + B x y + C y^2 + D x + E y + F = 0` (with `A, B, C` not all zero) is
* for `B^2 - 4AC < 0`: empty, a single point, or an ellipse (a circle when the foci coincide);
* for `B^2 - 4AC > 0`: a hyperbola or two intersecting lines;
* for `B^2 - 4AC = 0`: a parabola, empty, one line, or two parallel lines.

This is the discriminant test of Theorem 11.11 as a statement about point sets, with the degenerate cases listed
explicitly; the book's version ("if the graph is a non-degenerate conic, then ...") is `discriminant_test_graph`
below. The proof follows the book: rotate the axes to remove the `xy` term (Theorem 11.10), use the invariance of
`B^2 - 4AC`, complete the squares, and recognise the standard equations of Chapter 7. Also: for a focus at the
pole and directrix `x = -d`, the focus-directrix-eccentricity curve of Definition 11.1 is an ellipse for
`0 < e < 1` and a hyperbola for `e > 1` in the sense of Definitions 7.4 and 7.6; and the graph of the polar
equation `r = ℓ / (1 - e cos(θ - φ))` is a circle, an ellipse, a parabola or a hyperbola according to `e = 0`,
`0 < e < 1`, `e = 1`, `e > 1` (Theorem 11.13, `polar_conic_type`).
-/

namespace UndergradKB.Precalculus

open Real

/-! ### Point sets -/

/-- The graph of `A x^2 + B x y + C y^2 + D x + E y + F = 0`. -/
def conicGraph (A B C D E F : ℝ) : Set (ℝ × ℝ) := {P | quadForm A B C D E F P.1 P.2 = 0}

/-- The line `a x + b y = c`. -/
def lineSet (a b c : ℝ) : Set (ℝ × ℝ) := {P | a * P.1 + b * P.2 = c}

/-- The ellipse with foci `F₁`, `F₂` and distance sum `d` (Definition 7.4). -/
def ellipseSet (F₁ F₂ : ℝ × ℝ) (d : ℝ) : Set (ℝ × ℝ) := {P | IsEllipsePt F₁ F₂ d P}

/-- The hyperbola with foci `F₁`, `F₂` and distance difference `d` (Definition 7.6). -/
def hyperbolaSet (F₁ F₂ : ℝ × ℝ) (d : ℝ) : Set (ℝ × ℝ) := {P | IsHyperbolaPt F₁ F₂ d P}

/-- The parabola with focus `F` and directrix `a x + b y = c` (Definition 7.3). -/
def parabolaSet (F : ℝ × ℝ) (a b c : ℝ) : Set (ℝ × ℝ) := {P | IsParabolaPt F a b c P}

/-! ### Rotations of the plane -/

/-- The point with coordinates `(x', y')` in the axes rotated by `θ`, written in the original axes
(Theorem 11.9). -/
noncomputable def rotPt (θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * cos θ - p.2 * sin θ, p.1 * sin θ + p.2 * cos θ)

theorem rotPt_rotPt_neg (θ : ℝ) (P : ℝ × ℝ) : rotPt θ (rotPt (-θ) P) = P := by
  have h := cos_sq_add_sin_sq θ
  unfold rotPt
  rw [cos_neg, sin_neg]
  ext
  · dsimp only; linear_combination P.1 * h
  · dsimp only; linear_combination P.2 * h

theorem rotPt_neg_rotPt (θ : ℝ) (P : ℝ × ℝ) : rotPt (-θ) (rotPt θ P) = P := by
  have := rotPt_rotPt_neg (-θ) P
  rwa [neg_neg] at this

theorem edist2_rotPt (θ : ℝ) (p q : ℝ × ℝ) : edist2 (rotPt θ p) (rotPt θ q) = edist2 p q := by
  have h := cos_sq_add_sin_sq θ
  unfold edist2 rotPt
  dsimp only
  congr 1
  linear_combination ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) * h

/-- The set `S` described in the axes rotated by `θ`, as a set in the original axes. -/
def rotSet (θ : ℝ) (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {P | rotPt (-θ) P ∈ S}

theorem rotSet_empty (θ : ℝ) : rotSet θ ∅ = ∅ := rfl

theorem rotSet_union (θ : ℝ) (S T : Set (ℝ × ℝ)) :
    rotSet θ (S ∪ T) = rotSet θ S ∪ rotSet θ T := rfl

theorem rotSet_singleton (θ : ℝ) (p : ℝ × ℝ) : rotSet θ {p} = {rotPt θ p} := by
  ext P
  simp only [rotSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h; rw [← h, rotPt_rotPt_neg]
  · intro h; rw [h, rotPt_neg_rotPt]

theorem edist2_rotPt_left (θ : ℝ) (P F : ℝ × ℝ) :
    edist2 P (rotPt θ F) = edist2 (rotPt (-θ) P) F := by
  rw [← edist2_rotPt (-θ), rotPt_neg_rotPt]

theorem rotSet_ellipseSet (θ : ℝ) (F₁ F₂ : ℝ × ℝ) (d : ℝ) :
    rotSet θ (ellipseSet F₁ F₂ d) = ellipseSet (rotPt θ F₁) (rotPt θ F₂) d := by
  ext P
  simp only [rotSet, ellipseSet, Set.mem_ofPred_eq, IsEllipsePt, edist2_rotPt_left]

theorem rotSet_hyperbolaSet (θ : ℝ) (F₁ F₂ : ℝ × ℝ) (d : ℝ) :
    rotSet θ (hyperbolaSet F₁ F₂ d) = hyperbolaSet (rotPt θ F₁) (rotPt θ F₂) d := by
  ext P
  simp only [rotSet, hyperbolaSet, Set.mem_ofPred_eq, IsHyperbolaPt, edist2_rotPt_left]

theorem rotSet_lineSet (θ : ℝ) (a b c : ℝ) :
    rotSet θ (lineSet a b c) = lineSet (rotPt θ (a, b)).1 (rotPt θ (a, b)).2 c := by
  ext P
  simp only [rotSet, lineSet, rotPt, Set.mem_ofPred_eq, cos_neg, sin_neg]
  constructor <;> intro h <;> linear_combination h

theorem rotPt_normSq (θ : ℝ) (a b : ℝ) :
    (rotPt θ (a, b)).1 ^ 2 + (rotPt θ (a, b)).2 ^ 2 = a ^ 2 + b ^ 2 := by
  have h := cos_sq_add_sin_sq θ
  unfold rotPt; dsimp only
  linear_combination (a ^ 2 + b ^ 2) * h

theorem rotPt_cross (θ : ℝ) (a b a' b' : ℝ) :
    (rotPt θ (a, b)).1 * (rotPt θ (a', b')).2 - (rotPt θ (a', b')).1 * (rotPt θ (a, b)).2 =
      a * b' - a' * b := by
  have h := cos_sq_add_sin_sq θ
  unfold rotPt; dsimp only
  linear_combination (a * b' - a' * b) * h

theorem distToLine_rotPt (θ : ℝ) (a b c : ℝ) (P : ℝ × ℝ) :
    distToLine (rotPt θ (a, b)).1 (rotPt θ (a, b)).2 c P = distToLine a b c (rotPt (-θ) P) := by
  unfold distToLine
  rw [rotPt_normSq]
  congr 2
  simp only [rotPt, cos_neg, sin_neg]
  ring

theorem rotSet_parabolaSet (θ : ℝ) (F : ℝ × ℝ) (a b c : ℝ) :
    rotSet θ (parabolaSet F a b c) =
      parabolaSet (rotPt θ F) (rotPt θ (a, b)).1 (rotPt θ (a, b)).2 c := by
  ext P
  simp only [rotSet, parabolaSet, Set.mem_ofPred_eq, IsParabolaPt, edist2_rotPt_left, distToLine_rotPt]

/-- The graph of the general quadratic equation is the graph of the rotated equation (coefficients
`rotA, ..., rotE`), drawn in the axes rotated by `θ` (Theorems 11.9-11.10). -/
theorem conicGraph_eq_rotSet (A B C D E F θ : ℝ) :
    conicGraph A B C D E F =
      rotSet θ (conicGraph (rotA A B C θ) (rotB A B C θ) (rotC A B C θ) (rotD D E θ) (rotE D E θ) F) := by
  ext P
  simp only [conicGraph, rotSet, Set.mem_ofPred_eq]
  have h := quadForm_rotate A B C D E F θ (rotPt (-θ) P).1 (rotPt (-θ) P).2
  have h1 : (rotPt (-θ) P).1 * cos θ - (rotPt (-θ) P).2 * sin θ = P.1 :=
    congrArg Prod.fst (rotPt_rotPt_neg θ P)
  have h2 : (rotPt (-θ) P).1 * sin θ + (rotPt (-θ) P).2 * cos θ = P.2 :=
    congrArg Prod.snd (rotPt_rotPt_neg θ P)
  rw [h1, h2] at h
  rw [h]

/-- Multiplying the equation by `-1` does not change its graph. -/
theorem conicGraph_neg (A B C D E F : ℝ) :
    conicGraph (-A) (-B) (-C) (-D) (-E) (-F) = conicGraph A B C D E F := by
  ext P
  simp only [conicGraph, Set.mem_ofPred_eq, quadForm]
  constructor <;> intro h <;> linear_combination -h

/-! ### Equations without an `xy` term -/

theorem quadForm_complete {A C D E F : ℝ} (hA : A ≠ 0) (hC : C ≠ 0) (x y : ℝ) :
    quadForm A 0 C D E F x y =
      A * (x - centerX A D) ^ 2 + C * (y - centerX C E) ^ 2 - centralRHS A C D E F := by
  unfold quadForm centerX centralRHS; field_simp; ring

/-- Ellipse case without `xy` term, `A, C > 0`, `R > 0`: the graph of `A x^2 + C y^2 + D x + E y + F = 0` is
an ellipse (Equation 7.4). -/
theorem conicGraph_ellipse {A C D E F : ℝ} (hA : 0 < A) (hC : 0 < C) (hR : 0 < centralRHS A C D E F) :
    ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
      conicGraph A 0 C D E F = ellipseSet F₁ F₂ (2 * a) := by
  set R := centralRHS A C D E F with hRdef
  set x0 := centerX A D
  set y0 := centerX C E
  have key : ∀ x y : ℝ, quadForm A 0 C D E F x y = 0 ↔
      (x - x0) ^ 2 / (R / A) + (y - y0) ^ 2 / (R / C) = 1 := by
    intro x y
    rw [quadForm_complete hA.ne' hC.ne', div_add_div _ _ (by positivity) (by positivity),
      div_eq_one_iff_eq (by positivity)]
    constructor <;> intro h <;> field_simp at h ⊢ <;> linarith
  have hRA : 0 < R / A := by positivity
  have hRC : 0 < R / C := by positivity
  rcases le_total (R / C) (R / A) with hle | hle
  · -- horizontal major axis
    set a := √(R / A)
    set b := √(R / C)
    have ha2 : a ^ 2 = R / A := Real.sq_sqrt hRA.le
    have hb2 : b ^ 2 = R / C := Real.sq_sqrt hRC.le
    have ha : 0 < a := Real.sqrt_pos.2 hRA
    set c := √(a ^ 2 - b ^ 2)
    have hc2 : c ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt (by rw [ha2, hb2]; linarith)
    have hc : 0 ≤ c := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.2 hRC
    have hca : c < a := by nlinarith
    refine ⟨(x0 - c, y0), (x0 + c, y0), a, ?_, ?_⟩
    · have : edist2 (x0 - c, y0) (x0 + c, y0) = 2 * c :=
        (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
      rw [this]; linarith
    · ext ⟨x, y⟩
      simp only [conicGraph, ellipseSet, Set.mem_ofPred_eq]
      rw [ellipse_horizontal_equation ha hc hca (by linarith : b ^ 2 = a ^ 2 - c ^ 2), key, ha2, hb2]
  · -- vertical major axis
    set a := √(R / C)
    set b := √(R / A)
    have ha2 : a ^ 2 = R / C := Real.sq_sqrt hRC.le
    have hb2 : b ^ 2 = R / A := Real.sq_sqrt hRA.le
    have ha : 0 < a := Real.sqrt_pos.2 hRC
    set c := √(a ^ 2 - b ^ 2)
    have hc2 : c ^ 2 = a ^ 2 - b ^ 2 := Real.sq_sqrt (by rw [ha2, hb2]; linarith)
    have hc : 0 ≤ c := Real.sqrt_nonneg _
    have hb0 : 0 < b := Real.sqrt_pos.2 hRA
    have hca : c < a := by nlinarith
    refine ⟨(x0, y0 - c), (x0, y0 + c), a, ?_, ?_⟩
    · have : edist2 (x0, y0 - c) (x0, y0 + c) = 2 * c :=
        (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
      rw [this]; linarith
    · ext ⟨x, y⟩
      simp only [conicGraph, ellipseSet, Set.mem_ofPred_eq]
      rw [ellipse_vertical_equation ha hc hca (by linarith : b ^ 2 = a ^ 2 - c ^ 2), key, ha2, hb2]

/-- Ellipse-type equation without `xy` term (`AC > 0`): the graph is empty, one point, or an ellipse. -/
theorem conicGraph_AC_pos {A C D E F : ℝ} (hAC : 0 < A * C) :
    conicGraph A 0 C D E F = ∅ ∨ (∃ p, conicGraph A 0 C D E F = {p}) ∨
      ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
        conicGraph A 0 C D E F = ellipseSet F₁ F₂ (2 * a) := by
  -- reduce to `A > 0`, `C > 0`
  wlog hA : 0 < A generalizing A C D E F
  · have hA' : A < 0 := by
      rcases lt_trichotomy A 0 with h | h | h
      · exact h
      · rw [h, zero_mul] at hAC; exact absurd hAC (lt_irrefl 0)
      · exact absurd h hA
    have := this (A := -A) (C := -C) (D := -D) (E := -E) (F := -F) (by nlinarith) (by linarith)
    rwa [← neg_zero, conicGraph_neg] at this
  have hC : 0 < C := pos_of_mul_pos_right hAC hA.le
  have key := quadForm_complete (D := D) (E := E) (F := F) hA.ne' hC.ne'
  rcases lt_trichotomy (centralRHS A C D E F) 0 with hR | hR | hR
  · left
    ext ⟨x, y⟩
    simp only [conicGraph, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, key]
    have : 0 ≤ A * (x - centerX A D) ^ 2 + C * (y - centerX C E) ^ 2 := by positivity
    linarith
  · right; left
    refine ⟨(centerX A D, centerX C E), ?_⟩
    ext ⟨x, y⟩
    simp only [conicGraph, Set.mem_ofPred_eq, Set.mem_singleton_iff, key, hR, sub_zero, Prod.mk.injEq]
    constructor
    · intro h
      have h1 : A * (x - centerX A D) ^ 2 = 0 := by
        have := mul_nonneg hA.le (sq_nonneg (x - centerX A D))
        have := mul_nonneg hC.le (sq_nonneg (y - centerX C E))
        linarith
      have h2 : C * (y - centerX C E) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.1 h1 with h1 | h1
      · exact absurd h1 hA.ne'
      rcases mul_eq_zero.1 h2 with h2 | h2
      · exact absurd h2 hC.ne'
      exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := x - centerX A D) two_ne_zero],
        by nlinarith [pow_eq_zero_iff (n := 2) (a := y - centerX C E) two_ne_zero]⟩
    · rintro ⟨rfl, rfl⟩; ring
  · right; right
    exact conicGraph_ellipse hA hC hR

/-- Hyperbola case without `xy` term, `A > 0 > C`, `R > 0`: the graph is a hyperbola with horizontal
transverse axis (Equation 7.6). -/
theorem conicGraph_hyperbola_pos {A C D E F : ℝ} (hA : 0 < A) (hC : C < 0)
    (hR : 0 < centralRHS A C D E F) :
    ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
      conicGraph A 0 C D E F = hyperbolaSet F₁ F₂ (2 * a) := by
  set R := centralRHS A C D E F
  set x0 := centerX A D
  set y0 := centerX C E
  have hRA : 0 < R / A := by positivity
  have hRC : 0 < R / -C := div_pos hR (by linarith)
  set a := √(R / A)
  set b := √(R / -C)
  have ha2 : a ^ 2 = R / A := Real.sq_sqrt hRA.le
  have hb2 : b ^ 2 = R / -C := Real.sq_sqrt hRC.le
  have ha : 0 < a := Real.sqrt_pos.2 hRA
  have hb : 0 < b := Real.sqrt_pos.2 hRC
  set c := √(a ^ 2 + b ^ 2)
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hac : a < c := by nlinarith
  refine ⟨(x0 - c, y0), (x0 + c, y0), a, ha, ?_, ?_⟩
  · have : edist2 (x0 - c, y0) (x0 + c, y0) = 2 * c :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
    rw [this]; linarith
  · ext ⟨x, y⟩
    simp only [conicGraph, hyperbolaSet, Set.mem_ofPred_eq]
    rw [hyperbola_horizontal_equation ha hac (by linarith : b ^ 2 = c ^ 2 - a ^ 2), ha2, hb2,
      quadForm_complete hA.ne' hC.ne]
    have hC' : -C ≠ 0 := by linarith
    have hC0 : C ≠ 0 := hC.ne
    have hR0 : R ≠ 0 := hR.ne'
    have hA0 : A ≠ 0 := hA.ne'
    have e : (x - x0) ^ 2 / (R / A) - (y - y0) ^ 2 / (R / -C) =
        (A * (x - x0) ^ 2 + C * (y - y0) ^ 2) / R := by
      field_simp; ring
    rw [e, div_eq_one_iff_eq hR0]
    exact sub_eq_zero

/-- Hyperbola case without `xy` term, `A > 0 > C`, `R < 0`: the graph is a hyperbola with vertical
transverse axis (Equation 7.7). -/
theorem conicGraph_hyperbola_neg {A C D E F : ℝ} (hA : 0 < A) (hC : C < 0)
    (hR : centralRHS A C D E F < 0) :
    ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
      conicGraph A 0 C D E F = hyperbolaSet F₁ F₂ (2 * a) := by
  set R := centralRHS A C D E F
  set x0 := centerX A D
  set y0 := centerX C E
  have hRA : 0 < -R / A := div_pos (by linarith) hA
  have hRC : 0 < R / C := div_pos_of_neg_of_neg hR hC
  set a := √(-R / A)
  set b := √(R / C)
  have ha2 : a ^ 2 = -R / A := Real.sq_sqrt hRA.le
  have hb2 : b ^ 2 = R / C := Real.sq_sqrt hRC.le
  have ha : 0 < a := Real.sqrt_pos.2 hRA
  have hb : 0 < b := Real.sqrt_pos.2 hRC
  set c := √(a ^ 2 + b ^ 2)
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hbc : b < c := by nlinarith
  refine ⟨(x0, y0 - c), (x0, y0 + c), b, hb, ?_, ?_⟩
  · have : edist2 (x0, y0 - c) (x0, y0 + c) = 2 * c :=
      (edist2_eq_iff_sq (by linarith)).2 (by dsimp only; ring)
    rw [this]; linarith
  · ext ⟨x, y⟩
    simp only [conicGraph, hyperbolaSet, Set.mem_ofPred_eq]
    rw [hyperbola_vertical_equation hb hbc (by linarith : a ^ 2 = c ^ 2 - b ^ 2), ha2, hb2,
      quadForm_complete hA.ne' hC.ne]
    have hR' : -R ≠ 0 := by linarith
    have hC0 : C ≠ 0 := hC.ne
    have hR0 : R ≠ 0 := hR.ne
    have hA0 : A ≠ 0 := hA.ne'
    have e : (y - y0) ^ 2 / (R / C) - (x - x0) ^ 2 / (-R / A) =
        (A * (x - x0) ^ 2 + C * (y - y0) ^ 2) / R := by
      field_simp; ring
    rw [e, div_eq_one_iff_eq hR0]
    exact sub_eq_zero

/-- Two intersecting lines without `xy` term: `A > 0 > C`, `R = 0`. -/
theorem conicGraph_crossing_lines {A C D E F : ℝ} (hA : 0 < A) (hC : C < 0)
    (hR : centralRHS A C D E F = 0) :
    ∃ a b c a' b' c' : ℝ, a * b' - a' * b ≠ 0 ∧
      conicGraph A 0 C D E F = lineSet a b c ∪ lineSet a' b' c' := by
  set x0 := centerX A D
  set y0 := centerX C E
  set s := √A
  set t := √(-C)
  have hs2 : s ^ 2 = A := Real.sq_sqrt hA.le
  have ht2 : t ^ 2 = -C := Real.sq_sqrt (by linarith)
  have hs : 0 < s := Real.sqrt_pos.2 hA
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  refine ⟨s, -t, s * x0 - t * y0, s, t, s * x0 + t * y0, ?_, ?_⟩
  · nlinarith
  · ext ⟨x, y⟩
    simp only [conicGraph, lineSet, Set.mem_ofPred_eq, Set.mem_union, quadForm_complete hA.ne' hC.ne, hR,
      sub_zero]
    have e : A * (x - x0) ^ 2 + C * (y - y0) ^ 2 =
        (s * (x - x0) - t * (y - y0)) * (s * (x - x0) + t * (y - y0)) := by
      rw [← hs2]; linear_combination (y - y0) ^ 2 * ht2
    rw [e, mul_eq_zero]
    constructor
    · rintro (h | h)
      · left; linear_combination h
      · right; linear_combination h
    · rintro (h | h)
      · left; linear_combination h
      · right; linear_combination h

/-- Hyperbola-type equation without `xy` term (`AC < 0`): the graph is a hyperbola or two intersecting
lines. -/
theorem conicGraph_AC_neg {A C D E F : ℝ} (hAC : A * C < 0) :
    (∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
        conicGraph A 0 C D E F = hyperbolaSet F₁ F₂ (2 * a)) ∨
      ∃ a b c a' b' c' : ℝ, a * b' - a' * b ≠ 0 ∧
        conicGraph A 0 C D E F = lineSet a b c ∪ lineSet a' b' c' := by
  wlog hA : 0 < A generalizing A C D E F
  · have hA' : A < 0 := by
      rcases lt_trichotomy A 0 with h | h | h
      · exact h
      · rw [h, zero_mul] at hAC; exact absurd hAC (lt_irrefl 0)
      · exact absurd h hA
    have := this (A := -A) (C := -C) (D := -D) (E := -E) (F := -F) (by nlinarith) (by linarith)
    rwa [← neg_zero, conicGraph_neg] at this
  have hC : C < 0 := by
    by_contra h; push Not at h; nlinarith
  rcases lt_trichotomy (centralRHS A C D E F) 0 with hR | hR | hR
  · exact Or.inl (conicGraph_hyperbola_neg hA hC hR)
  · exact Or.inr (conicGraph_crossing_lines hA hC hR)
  · exact Or.inl (conicGraph_hyperbola_pos hA hC hR)

/-- Parabola-type equation `A x^2 + D x + E y + F = 0` (`A ≠ 0`, no `y^2` and no `xy` term): a parabola with
vertical axis if `E ≠ 0`; otherwise empty, one vertical line, or two parallel vertical lines. -/
theorem conicGraph_C_zero {A D E F : ℝ} (hA : A ≠ 0) :
    (∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
        conicGraph A 0 0 D E F = parabolaSet Fc a b c) ∨
      conicGraph A 0 0 D E F = ∅ ∨
      (∃ a b c : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ conicGraph A 0 0 D E F = lineSet a b c) ∨
      ∃ a b c c' : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ c ≠ c' ∧
        conicGraph A 0 0 D E F = lineSet a b c ∪ lineSet a b c' := by
  by_cases hE : E = 0
  · subst hE
    set x0 := centerX A D
    set q := (D ^ 2 / (4 * A) - F) / A
    have key : ∀ x y : ℝ, quadForm A 0 0 D 0 F x y = A * ((x - x0) ^ 2 - q) := by
      intro x y; unfold quadForm; simp only [x0, q, centerX]; field_simp; ring
    have key' : ∀ x y : ℝ, quadForm A 0 0 D 0 F x y = 0 ↔ (x - x0) ^ 2 = q := by
      intro x y; rw [key, mul_eq_zero, sub_eq_zero]; simp [hA]
    rcases lt_trichotomy q 0 with hq | hq | hq
    · right; left
      ext ⟨x, y⟩
      simp only [conicGraph, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, key']
      intro h; nlinarith [sq_nonneg (x - x0)]
    · right; right; left
      refine ⟨1, 0, x0, by norm_num, ?_⟩
      ext ⟨x, y⟩
      simp only [conicGraph, lineSet, Set.mem_ofPred_eq, key', hq, one_mul, zero_mul, add_zero]
      rw [pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    · right; right; right
      set r := √q
      have hr2 : r ^ 2 = q := Real.sq_sqrt hq.le
      have hr : 0 < r := Real.sqrt_pos.2 hq
      refine ⟨1, 0, x0 - r, x0 + r, by norm_num, by linarith, ?_⟩
      ext ⟨x, y⟩
      simp only [conicGraph, lineSet, Set.mem_ofPred_eq, Set.mem_union, key', one_mul, zero_mul,
        add_zero]
      rw [← hr2]
      constructor
      · intro h
        have : (x - x0 + r) * (x - x0 - r) = 0 := by linear_combination h
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      · rintro (h | h) <;> rw [h] <;> ring
  · left
    set p := -E / (4 * A)
    set k := (D ^ 2 / (4 * A) - F) / E
    have hp : p ≠ 0 := div_ne_zero (neg_ne_zero.2 hE) (mul_ne_zero four_ne_zero hA)
    refine ⟨(centerX A D, k + p), 0, 1, k - p, by norm_num, ?_, ?_⟩
    · intro h; apply hp; linarith
    · ext ⟨x, y⟩
      simp only [conicGraph, parabolaSet, Set.mem_ofPred_eq, IsParabolaPt]
      rw [parabola_vertical_equation, conic_parabola_form_vertical hA hE]

/-- Parabola-type equation `C y^2 + D x + E y + F = 0` (`C ≠ 0`): a parabola with horizontal axis if `D ≠ 0`;
otherwise empty, one horizontal line, or two parallel horizontal lines. -/
theorem conicGraph_A_zero {C D E F : ℝ} (hC : C ≠ 0) :
    (∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
        conicGraph 0 0 C D E F = parabolaSet Fc a b c) ∨
      conicGraph 0 0 C D E F = ∅ ∨
      (∃ a b c : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ conicGraph 0 0 C D E F = lineSet a b c) ∨
      ∃ a b c c' : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ c ≠ c' ∧
        conicGraph 0 0 C D E F = lineSet a b c ∪ lineSet a b c' := by
  by_cases hD : D = 0
  · subst hD
    set y0 := centerX C E
    set q := (E ^ 2 / (4 * C) - F) / C
    have key : ∀ x y : ℝ, quadForm 0 0 C 0 E F x y = C * ((y - y0) ^ 2 - q) := by
      intro x y; unfold quadForm; simp only [y0, q, centerX]; field_simp; ring
    have key' : ∀ x y : ℝ, quadForm 0 0 C 0 E F x y = 0 ↔ (y - y0) ^ 2 = q := by
      intro x y; rw [key, mul_eq_zero, sub_eq_zero]; simp [hC]
    rcases lt_trichotomy q 0 with hq | hq | hq
    · right; left
      ext ⟨x, y⟩
      simp only [conicGraph, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, key']
      intro h; nlinarith [sq_nonneg (y - y0)]
    · right; right; left
      refine ⟨0, 1, y0, by norm_num, ?_⟩
      ext ⟨x, y⟩
      simp only [conicGraph, lineSet, Set.mem_ofPred_eq, key', hq, one_mul, zero_mul, zero_add]
      rw [pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    · right; right; right
      set r := √q
      have hr2 : r ^ 2 = q := Real.sq_sqrt hq.le
      have hr : 0 < r := Real.sqrt_pos.2 hq
      refine ⟨0, 1, y0 - r, y0 + r, by norm_num, by linarith, ?_⟩
      ext ⟨x, y⟩
      simp only [conicGraph, lineSet, Set.mem_ofPred_eq, Set.mem_union, key', one_mul, zero_mul,
        zero_add]
      rw [← hr2]
      constructor
      · intro h
        have : (y - y0 + r) * (y - y0 - r) = 0 := by linear_combination h
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      · rintro (h | h) <;> rw [h] <;> ring
  · left
    set p := -D / (4 * C)
    set h0 := (E ^ 2 / (4 * C) - F) / D
    have hp : p ≠ 0 := div_ne_zero (neg_ne_zero.2 hD) (mul_ne_zero four_ne_zero hC)
    refine ⟨(h0 + p, centerX C E), 1, 0, h0 - p, by norm_num, ?_, ?_⟩
    · intro h; apply hp; simp only at h; linarith
    · ext ⟨x, y⟩
      simp only [conicGraph, parabolaSet, Set.mem_ofPred_eq, IsParabolaPt]
      rw [parabola_horizontal_equation, conic_parabola_form_horizontal hC hD]

/-! ### The discriminant test -/

/-- `A + C` is unchanged by a rotation of the axes. -/
theorem rot_trace (A B C θ : ℝ) : rotA A B C θ + rotC A B C θ = A + C := by
  have h := cos_sq_add_sin_sq θ
  unfold rotA rotC
  linear_combination (A + C) * h

/-- Discriminant test (Theorem 11.11), point-set form with the degenerate cases. Let `A, B, C` be not all
zero and let `S` be the graph of `A x^2 + B x y + C y^2 + D x + E y + F = 0`.
* If `B^2 - 4AC < 0`, then `S` is empty, a single point, or an ellipse (foci `F₁`, `F₂`, distance sum
  `2a > |F₁F₂|`; a circle when `F₁ = F₂`).
* If `B^2 - 4AC > 0`, then `S` is a hyperbola (foci `F₁`, `F₂`, distance difference `0 < 2a < |F₁F₂|`) or the
  union of two intersecting lines.
* If `B^2 - 4AC = 0`, then `S` is a parabola (focus not on the directrix), empty, one line, or the union of two
  distinct parallel lines (PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem discriminant_test_classification (A B C D E F : ℝ) (hABC : ¬(A = 0 ∧ B = 0 ∧ C = 0)) :
    (B ^ 2 - 4 * A * C < 0 →
      conicGraph A B C D E F = ∅ ∨ (∃ p, conicGraph A B C D E F = {p}) ∨
        ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
          conicGraph A B C D E F = ellipseSet F₁ F₂ (2 * a)) ∧
    (0 < B ^ 2 - 4 * A * C →
      (∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
          conicGraph A B C D E F = hyperbolaSet F₁ F₂ (2 * a)) ∨
        ∃ a b c a' b' c' : ℝ, a * b' - a' * b ≠ 0 ∧
          conicGraph A B C D E F = lineSet a b c ∪ lineSet a' b' c') ∧
    (B ^ 2 - 4 * A * C = 0 →
      (∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
          conicGraph A B C D E F = parabolaSet Fc a b c) ∨
        conicGraph A B C D E F = ∅ ∨
        (∃ a b c : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ conicGraph A B C D E F = lineSet a b c) ∨
        ∃ a b c c' : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ c ≠ c' ∧
          conicGraph A B C D E F = lineSet a b c ∪ lineSet a b c') := by
  obtain ⟨θ, hθ, hdisc, -, -, -⟩ := discriminant_test A B C
  have hS := conicGraph_eq_rotSet A B C D E F θ
  rw [hθ] at hS
  set A' := rotA A B C θ
  set C' := rotC A B C θ
  set D' := rotD D E θ
  set E' := rotE D E θ
  have htr : A' + C' = A + C := rot_trace A B C θ
  refine ⟨?_, ?_, ?_⟩
  · intro hneg
    have hAC : 0 < A' * C' := by linarith
    rcases conicGraph_AC_pos (D := D') (E := E') (F := F) hAC with h | ⟨p, h⟩ | ⟨F₁, F₂, a, ha, h⟩
    · left; rw [hS, h, rotSet_empty]
    · right; left; exact ⟨rotPt θ p, by rw [hS, h, rotSet_singleton]⟩
    · right; right
      refine ⟨rotPt θ F₁, rotPt θ F₂, a, by rwa [edist2_rotPt], ?_⟩
      rw [hS, h, rotSet_ellipseSet]
  · intro hpos
    have hAC : A' * C' < 0 := by linarith
    rcases conicGraph_AC_neg (D := D') (E := E') (F := F) hAC with ⟨F₁, F₂, a, ha, hlt, h⟩ |
        ⟨a, b, c, a', b', c', hx, h⟩
    · left
      refine ⟨rotPt θ F₁, rotPt θ F₂, a, ha, by rwa [edist2_rotPt], ?_⟩
      rw [hS, h, rotSet_hyperbolaSet]
    · right
      refine ⟨(rotPt θ (a, b)).1, (rotPt θ (a, b)).2, c, (rotPt θ (a', b')).1, (rotPt θ (a', b')).2, c', by rwa [rotPt_cross θ a b a' b'], ?_⟩
      rw [hS, h, rotSet_union, rotSet_lineSet, rotSet_lineSet]
  · intro hzero
    have hAC : A' * C' = 0 := by linarith
    -- the rotated equation keeps a square term
    have hnot : ¬(A' = 0 ∧ C' = 0) := by
      rintro ⟨h1, h2⟩
      apply hABC
      have hsum : A + C = 0 := by rw [← htr, h1, h2, add_zero]
      have hC : C = -A := by linarith
      rw [hC] at hzero
      have hA : A = 0 := by nlinarith [sq_nonneg B, sq_nonneg A]
      have hB : B = 0 := by rw [hA] at hzero; nlinarith [sq_nonneg B]
      exact ⟨hA, hB, by rw [hC, hA, neg_zero]⟩
    have key : ∀ S' : Set (ℝ × ℝ), conicGraph A' 0 C' D' E' F = S' →
        conicGraph A B C D E F = rotSet θ S' := fun S' h => by rw [hS, h]
    have transport :
        ((∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
            conicGraph A' 0 C' D' E' F = parabolaSet Fc a b c) ∨
          conicGraph A' 0 C' D' E' F = ∅ ∨
          (∃ a b c : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ conicGraph A' 0 C' D' E' F = lineSet a b c) ∨
          ∃ a b c c' : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ c ≠ c' ∧
            conicGraph A' 0 C' D' E' F = lineSet a b c ∪ lineSet a b c') →
        ((∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
            conicGraph A B C D E F = parabolaSet Fc a b c) ∨
          conicGraph A B C D E F = ∅ ∨
          (∃ a b c : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ conicGraph A B C D E F = lineSet a b c) ∨
          ∃ a b c c' : ℝ, a ^ 2 + b ^ 2 ≠ 0 ∧ c ≠ c' ∧
            conicGraph A B C D E F = lineSet a b c ∪ lineSet a b c') := by
      rintro (⟨Fc, a, b, c, hab, hF, h⟩ | h | ⟨a, b, c, hab, h⟩ | ⟨a, b, c, c', hab, hc, h⟩)
      · left
        refine ⟨rotPt θ Fc, (rotPt θ (a, b)).1, (rotPt θ (a, b)).2, c, by rwa [rotPt_normSq], ?_, by rw [key _ h, rotSet_parabolaSet]⟩
        intro h'
        apply hF
        have e : (rotPt θ (a, b)).1 * (rotPt θ Fc).1 + (rotPt θ (a, b)).2 * (rotPt θ Fc).2 =
            a * Fc.1 + b * Fc.2 := by
          have := cos_sq_add_sin_sq θ
          simp only [rotPt]; linear_combination (a * Fc.1 + b * Fc.2) * this
        rw [← e, h']
      · right; left; rw [key _ h, rotSet_empty]
      · right; right; left
        exact ⟨(rotPt θ (a, b)).1, (rotPt θ (a, b)).2, c, by rwa [rotPt_normSq], by rw [key _ h, rotSet_lineSet]⟩
      · right; right; right
        exact ⟨(rotPt θ (a, b)).1, (rotPt θ (a, b)).2, c, c', by rwa [rotPt_normSq], hc, by rw [key _ h, rotSet_union, rotSet_lineSet,
          rotSet_lineSet]⟩
    apply transport
    rcases mul_eq_zero.1 hAC with h0 | h0
    · have hC' : C' ≠ 0 := fun h => hnot ⟨h0, h⟩
      rw [h0]
      exact conicGraph_A_zero hC'
    · have hA' : A' ≠ 0 := fun h => hnot ⟨h, h0⟩
      rw [h0]
      exact conicGraph_C_zero hA'

/-- Discriminant test in the book's wording (Theorem 11.11): suppose the graph of
`A x^2 + B x y + C y^2 + D x + E y + F = 0` is a non-degenerate conic, i.e. it is neither empty, nor a single
point, nor a line, nor the union of two lines. Then it is an ellipse (possibly a circle) if `B^2 - 4AC < 0`, a
hyperbola if `B^2 - 4AC > 0`, and a parabola if `B^2 - 4AC = 0` (PC-256). -/
@[kb "stitzzeager2013" "Theorem 11.11, p. 991"]
theorem discriminant_test_graph (A B C D E F : ℝ) (hABC : ¬(A = 0 ∧ B = 0 ∧ C = 0))
    (hne : conicGraph A B C D E F ≠ ∅) (hpt : ∀ p, conicGraph A B C D E F ≠ {p})
    (hline : ∀ a b c a' b' c' : ℝ, conicGraph A B C D E F ≠ lineSet a b c ∪ lineSet a' b' c') :
    (B ^ 2 - 4 * A * C < 0 → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
        conicGraph A B C D E F = ellipseSet F₁ F₂ (2 * a)) ∧
    (0 < B ^ 2 - 4 * A * C → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
        conicGraph A B C D E F = hyperbolaSet F₁ F₂ (2 * a)) ∧
    (B ^ 2 - 4 * A * C = 0 → ∃ (Fc : ℝ × ℝ) (a b c : ℝ), a ^ 2 + b ^ 2 ≠ 0 ∧ a * Fc.1 + b * Fc.2 ≠ c ∧
        conicGraph A B C D E F = parabolaSet Fc a b c) := by
  obtain ⟨h1, h2, h3⟩ := discriminant_test_classification A B C D E F hABC
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases h1 h with h | ⟨p, h⟩ | h
    · exact absurd h hne
    · exact absurd h (hpt p)
    · exact h
  · rcases h2 h with h | ⟨a, b, c, a', b', c', -, h⟩
    · exact h
    · exact absurd h (hline a b c a' b' c')
  · rcases h3 h with h | h | ⟨a, b, c, -, h⟩ | ⟨a, b, c, c', -, -, h⟩
    · exact h
    · exact absurd h hne
    · exact absurd (by rw [h, Set.union_self]) (hline a b c a b c)
    · exact absurd h (hline a b c a b c')

/-! ### Eccentricity and the type of the conic -/

theorem conicPt_standard_iff {e d : ℝ} (he : 0 ≤ e) (P : ℝ × ℝ) :
    IsConicPt (0, 0) 1 0 (-d) e P ↔
      quadForm (1 - e ^ 2) 0 1 (-(2 * e ^ 2 * d)) 0 (-(e ^ 2 * d ^ 2)) P.1 P.2 = 0 := by
  rw [conic_pt_iff (0, 0) he (by norm_num)]
  unfold quadForm
  constructor <;> intro h <;> linear_combination h

/-- With focus at the pole and directrix `x = -d` (`d > 0`), the conic of Definition 11.1 with eccentricity
`0 < e < 1` is an ellipse in the sense of Definition 7.4 (foci `F₁`, `F₂`, distance sum `2a > |F₁F₂|`)
(PC-257). -/
@[kb "stitzzeager2013" "Definition 11.1, p. 993"]
theorem conic_eccentricity_lt_one_ellipse {e d : ℝ} (he : 0 < e) (he1 : e < 1) (hd : 0 < d) :
    ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
      {P | IsConicPt (0, 0) 1 0 (-d) e P} = ellipseSet F₁ F₂ (2 * a) := by
  have hA : 0 < 1 - e ^ 2 := by nlinarith
  have hR : 0 < centralRHS (1 - e ^ 2) 1 (-(2 * e ^ 2 * d)) 0 (-(e ^ 2 * d ^ 2)) := by
    unfold centralRHS
    have : 0 < e ^ 2 * d ^ 2 := by positivity
    have : 0 ≤ (-(2 * e ^ 2 * d)) ^ 2 / (4 * (1 - e ^ 2)) := by positivity
    have e0 : (0 : ℝ) ^ 2 / (4 * 1) = 0 := by norm_num
    rw [e0]; linarith
  obtain ⟨F₁, F₂, a, ha, h⟩ := conicGraph_ellipse hA one_pos hR
  refine ⟨F₁, F₂, a, ha, ?_⟩
  rw [← h]
  ext P
  simp only [conicGraph, Set.mem_ofPred_eq, conicPt_standard_iff he.le]

/-- With focus at the pole and directrix `x = -d` (`d > 0`), the conic of Definition 11.1 with eccentricity
`e > 1` is a hyperbola in the sense of Definition 7.6 (foci `F₁`, `F₂`, distance difference `0 < 2a < |F₁F₂|`)
(PC-257). -/
@[kb "stitzzeager2013" "Definition 11.1, p. 993"]
theorem conic_eccentricity_gt_one_hyperbola {e d : ℝ} (he1 : 1 < e) (hd : 0 < d) :
    ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
      {P | IsConicPt (0, 0) 1 0 (-d) e P} = hyperbolaSet F₁ F₂ (2 * a) := by
  have hA : 1 - e ^ 2 < 0 := by nlinarith
  have hR : centralRHS (1 - e ^ 2) 1 (-(2 * e ^ 2 * d)) 0 (-(e ^ 2 * d ^ 2)) < 0 := by
    unfold centralRHS
    have hne : 1 - e ^ 2 ≠ 0 := hA.ne
    have e1 : (-(2 * e ^ 2 * d)) ^ 2 / (4 * (1 - e ^ 2)) + (0 : ℝ) ^ 2 / (4 * 1) - -(e ^ 2 * d ^ 2) =
        e ^ 2 * d ^ 2 / (1 - e ^ 2) := by
      field_simp; ring
    rw [e1]
    exact div_neg_of_pos_of_neg (by positivity) hA
  -- multiply the equation by `-1` to get `A > 0 > C`
  have hA' : 0 < -(1 - e ^ 2) := by linarith
  have hR' : 0 < centralRHS (-(1 - e ^ 2)) (-1) (-(-(2 * e ^ 2 * d))) (-0) (-(-(e ^ 2 * d ^ 2))) := by
    have : centralRHS (-(1 - e ^ 2)) (-1) (-(-(2 * e ^ 2 * d))) (-0) (-(-(e ^ 2 * d ^ 2))) =
        -centralRHS (1 - e ^ 2) 1 (-(2 * e ^ 2 * d)) 0 (-(e ^ 2 * d ^ 2)) := by
      unfold centralRHS; field_simp; ring
    rw [this]; linarith
  obtain ⟨F₁, F₂, a, ha, hlt, h⟩ := conicGraph_hyperbola_pos hA' (by norm_num) hR'
  refine ⟨F₁, F₂, a, ha, hlt, ?_⟩
  rw [← neg_zero, conicGraph_neg] at h
  rw [← h]
  ext P
  simp only [conicGraph, Set.mem_ofPred_eq, conicPt_standard_iff (by linarith : (0 : ℝ) ≤ e), neg_zero]

/-! ### Polar equations and the type of the conic -/

theorem rotPt_zero (φ : ℝ) : rotPt φ (0, 0) = (0, 0) := by simp [rotPt]

theorem rotPt_one_zero (φ : ℝ) : rotPt φ (1, 0) = (cos φ, sin φ) := by simp [rotPt]

theorem conicPt_rotate (φ c e : ℝ) (P : ℝ × ℝ) :
    IsConicPt (0, 0) (cos φ) (sin φ) c e P ↔ IsConicPt (0, 0) 1 0 c e (rotPt (-φ) P) := by
  have h1 := distToLine_rotPt φ 1 0 c P
  rw [rotPt_one_zero] at h1
  unfold IsConicPt
  dsimp only at h1
  rw [h1, ← rotPt_zero φ, edist2_rotPt_left, rotPt_zero]

/-- The graph of the polar equation `r = ℓ / (1 - e cos(θ - φ))`, over the angles where the denominator is
nonzero. -/
def polarConicGraph (ℓ e φ : ℝ) : Set (ℝ × ℝ) :=
  {P | ∃ θ : ℝ, 1 - e * cos (θ - φ) ≠ 0 ∧
    P = (ℓ / (1 - e * cos (θ - φ)) * cos θ, ℓ / (1 - e * cos (θ - φ)) * sin θ)}

theorem polarConicGraph_eq {ℓ e φ : ℝ} (hℓ : 0 < ℓ) (he : 0 < e) :
    polarConicGraph ℓ e φ = {P | IsConicPt (0, 0) (cos φ) (sin φ) (-(ℓ / e)) e P} := by
  ext ⟨x, y⟩
  simp only [polarConicGraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, h⟩
    rw [h]
    exact (polar_conic_rotated hℓ he.le hθ).2.1 he
  · intro h
    have hP : (x, y) ≠ ((0 : ℝ), (0 : ℝ)) := by
      rintro ⟨⟩
      unfold IsConicPt distToLine at h
      rw [cos_sq_add_sin_sq, Real.sqrt_one, div_one] at h
      have h0 : edist2 (0, 0) (0, 0) = 0 := (edist2_eq_iff_sq le_rfl).2 (by norm_num)
      rw [h0] at h
      simp only [mul_zero, add_zero, zero_sub, neg_neg] at h
      have : 0 < e * |ℓ / e| := by
        have : 0 < ℓ / e := div_pos hℓ he
        rw [abs_of_pos this]; positivity
      linarith
    exact polar_conic_rotated_converse hℓ he x y hP h

/-- Theorem 11.13 with the type of the conic: the graph of `r = ℓ / (1 - e cos(θ - φ))` (`ℓ > 0`) is a circle
of radius `ℓ` about the pole if `e = 0`, an ellipse (Definition 7.4) if `0 < e < 1`, a parabola (Definition 7.3,
focus at the pole, directrix `x cos φ + y sin φ = -ℓ`) if `e = 1`, and a hyperbola (Definition 7.6) if `e > 1`
(PC-259). -/
@[kb "stitzzeager2013" "Theorem 11.13, p. 997"]
theorem polar_conic_type {ℓ φ : ℝ} (hℓ : 0 < ℓ) (e : ℝ) :
    (e = 0 → polarConicGraph ℓ e φ = {P | edist2 P (0, 0) = ℓ}) ∧
    (0 < e → e < 1 → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, edist2 F₁ F₂ < 2 * a ∧
      polarConicGraph ℓ e φ = ellipseSet F₁ F₂ (2 * a)) ∧
    (e = 1 → polarConicGraph ℓ e φ = parabolaSet (0, 0) (cos φ) (sin φ) (-ℓ)) ∧
    (1 < e → ∃ F₁ F₂ : ℝ × ℝ, ∃ a : ℝ, 0 < a ∧ 2 * a < edist2 F₁ F₂ ∧
      polarConicGraph ℓ e φ = hyperbolaSet F₁ F₂ (2 * a)) := by
  have hrot : ∀ {e : ℝ}, 0 < e → polarConicGraph ℓ e φ =
      rotSet φ {P | IsConicPt (0, 0) 1 0 (-(ℓ / e)) e P} := by
    intro e he
    rw [polarConicGraph_eq hℓ he]
    ext P
    simp only [rotSet, Set.mem_ofPred_eq, conicPt_rotate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    ext P
    simp only [polarConicGraph, Set.mem_ofPred_eq, zero_mul, sub_zero, div_one]
    constructor
    · rintro ⟨θ, -, rfl⟩
      have := (polar_conic_rotated (φ := φ) (θ := θ) hℓ le_rfl (by simp)).1 rfl
      simpa using this
    · intro h
      have hP : P ≠ ((0 : ℝ), (0 : ℝ)) := by
        rintro rfl
        have h0 : edist2 (0, 0) (0, 0) = 0 := (edist2_eq_iff_sq le_rfl).2 (by norm_num)
        rw [h0] at h; linarith
      obtain ⟨θ, h1, h2⟩ := polar_rep_of_abs (s := ℓ) (x := P.1) (y := P.2) hP
        (by rw [abs_of_pos hℓ]; exact h.symm)
      exact ⟨θ, one_ne_zero, by rw [h1, h2]⟩
  · intro he he1
    have hd : 0 < ℓ / e := div_pos hℓ he
    obtain ⟨F₁, F₂, a, ha, h⟩ := conic_eccentricity_lt_one_ellipse he he1 hd
    refine ⟨rotPt φ F₁, rotPt φ F₂, a, by rwa [edist2_rotPt], ?_⟩
    rw [hrot he, h, rotSet_ellipseSet]
  · rintro rfl
    rw [polarConicGraph_eq hℓ one_pos, div_one]
    ext P
    simp only [parabolaSet, Set.mem_ofPred_eq, conic_pt_one_iff_parabola]
  · intro he1
    have he : 0 < e := by linarith
    have hd : 0 < ℓ / e := div_pos hℓ he
    obtain ⟨F₁, F₂, a, ha, hlt, h⟩ := conic_eccentricity_gt_one_hyperbola he1 hd
    refine ⟨rotPt φ F₁, rotPt φ F₂, a, ha, by rwa [edist2_rotPt], ?_⟩
    rw [hrot he, h, rotSet_hyperbolaSet]

end UndergradKB.Precalculus
