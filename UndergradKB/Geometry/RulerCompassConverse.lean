import UndergradKB.Geometry.RulerCompass

/-! # Ruler-and-compass constructions: the converse (Petrunin, Theorem 19.8 "if", Exercise 19.7)

Every point with constructible coordinates (in the sense of `IsConstructible`) is obtained from
`(0,0)` and `(1,0)` by the ruler-and-compass steps of `RCConstructible`. -/

namespace UndergradKB.Geometry

open Real

namespace RCConv

abbrev S0 : Set (ℝ × ℝ) := {(0, 0), (1, 0)}

abbrev Pt (P : ℝ × ℝ) : Prop := RCConstructible S0 (.point P)

theorem pt_zero : Pt (0, 0) := .init (by simp)
theorem pt_one : Pt (1, 0) := .init (by simp)

theorem xaxis : RCConstructible S0 (.line (0, 0) (1, 0)) := .line pt_zero pt_one (by simp)

theorem pt_xaxis_circle {c d : ℝ × ℝ} (hc : Pt c) (hd : Pt d) {a : ℝ} (h : OnCircle c d (a, 0)) :
    Pt (a, 0) :=
  RCConstructible.lineCircle xaxis (.circle hc hd) ⟨a, by simp, by simp⟩ h

/-- Apex points of the two equilateral triangles on `PQ`. -/
noncomputable def Ep (P Q : ℝ × ℝ) : ℝ × ℝ :=
  ((P.1 + Q.1) / 2 - √3 / 2 * (Q.2 - P.2), (P.2 + Q.2) / 2 + √3 / 2 * (Q.1 - P.1))

noncomputable def Em (P Q : ℝ × ℝ) : ℝ × ℝ :=
  ((P.1 + Q.1) / 2 + √3 / 2 * (Q.2 - P.2), (P.2 + Q.2) / 2 - √3 / 2 * (Q.1 - P.1))

theorem h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt3_pos : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)

theorem ne_coords {P Q : ℝ × ℝ} (h : P ≠ Q) : 0 < (Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2 := by
  by_contra hc
  apply h
  have h1 : (Q.1 - P.1) ^ 2 = 0 := by nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2 - P.2)]
  have h2 : (Q.2 - P.2) ^ 2 = 0 := by nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2 - P.2)]
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
  exact Prod.ext (by linarith) (by linarith)

theorem pt_apex {P Q : ℝ × ℝ} (hP : Pt P) (hQ : Pt Q) (hPQ : P ≠ Q) : Pt (Ep P Q) ∧ Pt (Em P Q) := by
  have hc1 : RCConstructible S0 (.circle P Q) := .circle hP hQ
  have hc2 : RCConstructible S0 (.circle Q P) := .circle hQ hP
  constructor
  · refine RCConstructible.circleCircle hc1 hc2 hPQ ?_ ?_
    · simp only [OnCircle, Ep]
      linear_combination ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2) / 4 * h3
    · simp only [OnCircle, Ep]
      linear_combination ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2) / 4 * h3
  · refine RCConstructible.circleCircle hc1 hc2 hPQ ?_ ?_
    · simp only [OnCircle, Em]
      linear_combination ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2) / 4 * h3
    · simp only [OnCircle, Em]
      linear_combination ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2) / 4 * h3

theorem apex_ne {P Q : ℝ × ℝ} (hPQ : P ≠ Q) : Ep P Q ≠ Em P Q := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Ep, Em] at h1 h2
  have hD := ne_coords hPQ
  have := sqrt3_pos
  nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2 - P.2), mul_pos this this]

theorem ln_bis {P Q : ℝ × ℝ} (hP : Pt P) (hQ : Pt Q) (hPQ : P ≠ Q) :
    RCConstructible S0 (.line (Ep P Q) (Em P Q)) :=
  .line (pt_apex hP hQ hPQ).1 (pt_apex hP hQ hPQ).2 (apex_ne hPQ)

theorem onLine_bis {P Q X : ℝ × ℝ} (hPQ : P ≠ Q)
    (hX : (X.1 - P.1) ^ 2 + (X.2 - P.2) ^ 2 = (X.1 - Q.1) ^ 2 + (X.2 - Q.2) ^ 2) :
    OnLine (Ep P Q) (Em P Q) X := by
  have hD := ne_coords hPQ
  have hs := sqrt3_pos.ne'
  have hw : (X.1 - (P.1 + Q.1) / 2) * (Q.1 - P.1) + (X.2 - (P.2 + Q.2) / 2) * (Q.2 - P.2) = 0 := by
    linear_combination (1 / 2 : ℝ) * hX
  refine ⟨1 / 2 - (((X.1 - (P.1 + Q.1) / 2) * (-(Q.2 - P.2)) + (X.2 - (P.2 + Q.2) / 2) * (Q.1 - P.1)) /
    ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2)) / √3, ?_, ?_⟩
  · simp only [Ep, Em]
    field_simp
    linear_combination ((Q.1 - P.1) * √3 * 4) * hw
  · simp only [Ep, Em]
    field_simp
    linear_combination ((Q.2 - P.2) * √3 * 4) * hw

theorem pt_mid {P Q : ℝ × ℝ} (hP : Pt P) (hQ : Pt Q) (hPQ : P ≠ Q) :
    Pt ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2) := by
  have hD := ne_coords hPQ
  have hdet : (Q.1 - P.1) * ((Em P Q).2 - (Ep P Q).2) - (Q.2 - P.2) * ((Em P Q).1 - (Ep P Q).1) =
      -(√3 * ((Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2)) := by
    simp only [Ep, Em]; ring
  refine RCConstructible.lineLine (.line hP hQ hPQ) (ln_bis hP hQ hPQ) ?_ ⟨1 / 2, ?_, ?_⟩
    (onLine_bis hPQ ?_)
  · rw [hdet, neg_ne_zero]; exact (mul_pos sqrt3_pos hD).ne'
  · simp only; ring
  · simp only; ring
  · simp only; ring

theorem pt_bis_xaxis {P Q : ℝ × ℝ} (hP : Pt P) (hQ : Pt Q) (hPQ : P ≠ Q) (hv : Q.1 ≠ P.1) {c : ℝ}
    (hc : (c - P.1) ^ 2 + (0 - P.2) ^ 2 = (c - Q.1) ^ 2 + (0 - Q.2) ^ 2) : Pt (c, 0) := by
  have hdet : (((1 : ℝ) - 0) * ((Em P Q).2 - (Ep P Q).2) - (0 - 0) * ((Em P Q).1 - (Ep P Q).1)) =
      -(√3 * (Q.1 - P.1)) := by
    simp only [Ep, Em]; ring
  refine RCConstructible.lineLine (p := (0, 0)) (q := (1, 0)) xaxis (ln_bis hP hQ hPQ) ?_
    ⟨c, by simp, by simp⟩ (onLine_bis hPQ (by simpa using hc))
  simp only
  rw [hdet, neg_ne_zero]
  exact mul_ne_zero sqrt3_pos.ne' (sub_ne_zero.mpr hv)

theorem ax_neg {a : ℝ} (h : Pt (a, 0)) : Pt (-a, 0) :=
  pt_xaxis_circle pt_zero h (by simp [OnCircle])

theorem ax_dbl {m : ℝ} (h : Pt (m, 0)) : Pt (2 * m, 0) :=
  pt_xaxis_circle h pt_zero (by simp [OnCircle]; ring)

theorem ax_mid {a b : ℝ} (ha : Pt (a, 0)) (hb : Pt (b, 0)) (hab : a ≠ b) : Pt ((a + b) / 2, 0) := by
  have := pt_mid ha hb (fun h => hab (congrArg Prod.fst h))
  simpa using this

theorem ax_half {a : ℝ} (ha : Pt (a, 0)) : Pt (a / 2, 0) := by
  by_cases h : a = 0
  · subst h; simpa using pt_zero
  · have := ax_mid pt_zero ha (fun h' => h h'.symm)
    simpa using this

theorem ax_add {a b : ℝ} (ha : Pt (a, 0)) (hb : Pt (b, 0)) : Pt (a + b, 0) := by
  by_cases h : a = b
  · subst h; have := ax_dbl ha; rwa [show 2 * a = a + a by ring] at this
  · have := ax_dbl (ax_mid ha hb h)
    rwa [show 2 * ((a + b) / 2) = a + b by ring] at this

/-- The point `(0, √3)`, giving the `y`-axis. -/
theorem pt_sqrt3 : Pt (0, √3) := by
  have h := (pt_apex (P := (-1, 0)) (Q := (1, 0)) (ax_neg pt_one) pt_one (by simp; norm_num)).1
  have e : Ep ((-1 : ℝ), (0 : ℝ)) (1, 0) = (0, √3) := by
    apply Prod.ext
    · simp [Ep]
    · simp [Ep]; ring
  rwa [e] at h

theorem yaxis : RCConstructible S0 (.line (0, 0) (0, √3)) :=
  .line pt_zero pt_sqrt3 (by simp; exact sqrt3_pos.ne)

theorem pt_yaxis_circle {c d : ℝ × ℝ} (hc : Pt c) (hd : Pt d) {a : ℝ} (h : OnCircle c d (0, a)) :
    Pt (0, a) :=
  RCConstructible.lineCircle yaxis (.circle hc hd) ⟨a / √3, by simp, by simp⟩ h

theorem ax_to_y {a : ℝ} (h : Pt (a, 0)) : Pt (0, a) :=
  pt_yaxis_circle pt_zero h (by simp [OnCircle])

theorem y_to_ax {a : ℝ} (h : Pt (0, a)) : Pt (a, 0) :=
  pt_xaxis_circle pt_zero h (by simp [OnCircle])

theorem ax_sq {s : ℝ} (h : Pt (s, 0)) : Pt (s ^ 2, 0) := by
  have hy := ax_to_y h
  have hm1 := ax_neg pt_one
  have hc := pt_bis_xaxis (P := (-1, 0)) (Q := (0, s)) hm1 hy (by simp) (by simp)
    (c := (s ^ 2 - 1) / 2) (by simp; ring)
  exact pt_xaxis_circle hc hm1 (by simp [OnCircle]; ring)

theorem ax_mul {a b : ℝ} (ha : Pt (a, 0)) (hb : Pt (b, 0)) : Pt (a * b, 0) := by
  have := ax_half (ax_half (ax_add (ax_sq (ax_add ha hb)) (ax_neg (ax_sq (ax_add ha (ax_neg hb))))))
  rwa [show ((a + b) ^ 2 + -(a + -b) ^ 2) / 2 / 2 = a * b by ring] at this

theorem ax_inv {a : ℝ} (ha : Pt (a, 0)) : Pt (a⁻¹, 0) := by
  by_cases h0 : a = 0
  · subst h0; simpa using pt_zero
  have h1 := ax_to_y pt_one
  have hc := pt_bis_xaxis (P := (0, 1)) (Q := (a, 0)) h1 ha (by simp) (by simpa using h0)
    (c := (a ^ 2 - 1) / (2 * a)) (by simp; field_simp; ring)
  have := ax_neg (pt_xaxis_circle hc ha (a := -a⁻¹) (by simp [OnCircle]; field_simp; ring))
  rwa [neg_neg] at this

theorem ax_sqrt {a : ℝ} (ha : Pt (a, 0)) : Pt (√a, 0) := by
  by_cases h : 0 ≤ a
  · have hm1 := ax_neg pt_one
    have hm := ax_mid hm1 ha (by intro e; linarith)
    have hsq : √a ^ 2 = a := Real.sq_sqrt h
    exact y_to_ax (pt_yaxis_circle hm hm1 (by simp only [OnCircle]; linear_combination hsq))
  · rw [Real.sqrt_eq_zero_of_nonpos (by linarith)]; exact pt_zero

theorem ax_nat (n : ℕ) : Pt ((n : ℝ), 0) := by
  induction n with
  | zero => simpa using pt_zero
  | succ n ih => simpa using ax_add ih pt_one

theorem ax_int (n : ℤ) : Pt ((n : ℝ), 0) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using ax_nat m
  · simpa using ax_neg (ax_nat m)

theorem ax_of_constructible {a : ℝ} (h : IsConstructible a) : Pt (a, 0) := by
  induction h with
  | intCast n => exact ax_int n
  | add _ _ ih1 ih2 => exact ax_add ih1 ih2
  | neg _ ih => exact ax_neg ih
  | mul _ _ ih1 ih2 => exact ax_mul ih1 ih2
  | inv _ ih => exact ax_inv ih
  | sqrt _ ih => exact ax_sqrt ih

theorem pt_of_axes {x y : ℝ} (hx : Pt (x, 0)) (hy : Pt (y, 0)) : Pt (x, y) := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h; exact pt_zero
  have hy' := ax_to_y hy
  have hm := pt_mid hx hy' (by intro e; apply h; exact ⟨congrArg Prod.fst e, (congrArg Prod.snd e).symm⟩)
  have hne : ((0 : ℝ), (0 : ℝ)) ≠ (((x, (0 : ℝ)).1 + ((0 : ℝ), y).1) / 2,
      ((x, (0 : ℝ)).2 + ((0 : ℝ), y).2) / 2) := by
    intro e
    apply h
    have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    simp only at h1 h2
    constructor <;> linarith
  exact RCConstructible.lineCircle (.line pt_zero hm hne) (.circle hm pt_zero)
    ⟨2, by simp only; ring, by simp only; ring⟩ (by simp only [OnCircle]; ring)

end RCConv

open RCConv in
/-- **Theorem 19.8** (Petrunin, p. 160), the "if" direction: every point with constructible coordinates
is obtained from `(0,0)` and `(1,0)` by a ruler-and-compass construction. -/
@[kb "petrunin2025" "Theorem 19.8, p. 160"]
theorem rcConstructible_of_isConstructible {x y : ℝ} (hx : IsConstructible x) (hy : IsConstructible y) :
    RCConstructible {(0, 0), (1, 0)} (.point (x, y)) :=
  pt_of_axes (ax_of_constructible hx) (ax_of_constructible hy)

/-- **Theorem 19.8** (Petrunin, p. 160): a point is obtainable from `(0,0)` and `(1,0)` by ruler and compass
if and only if its coordinates are constructible. -/
@[kb "petrunin2025" "Theorem 19.8, p. 160"]
theorem rcConstructible_iff {X : ℝ × ℝ} :
    RCConstructible {(0, 0), (1, 0)} (.point X) ↔ IsConstructiblePoint X := by
  refine ⟨fun h => h.coords ?_, fun h => rcConstructible_of_isConstructible h.1 h.2⟩
  rintro x (rfl | rfl)
  exacts [isConstructiblePoint_zero, isConstructiblePoint_one_zero]

open RCConv in
/-- **Exercise 19.7** (Petrunin, p. 159): from constructed points `(a,0)` and `(b,0)` one constructs
`(a·b, 0)`, `(a/b, 0)` and `(√(a·b), 0)` (for `a, b > 0`; positivity is only needed for the last two to be
meaningful). -/
@[kb "petrunin2025" "Exercise 19.7, p. 159"]
theorem rcConstructible_mul_div_geomMean {a b : ℝ}
    (ha : RCConstructible {(0, 0), (1, 0)} (.point (a, 0)))
    (hb : RCConstructible {(0, 0), (1, 0)} (.point (b, 0))) (_ha0 : 0 < a) (_hb0 : 0 < b) :
    RCConstructible {(0, 0), (1, 0)} (.point (a * b, 0)) ∧
    RCConstructible {(0, 0), (1, 0)} (.point (a / b, 0)) ∧
    RCConstructible {(0, 0), (1, 0)} (.point (√(a * b), 0)) :=
  ⟨ax_mul ha hb, by simpa [div_eq_mul_inv] using ax_mul ha (ax_inv hb), ax_sqrt (ax_mul ha hb)⟩

end UndergradKB.Geometry
