import UndergradKB.Calculus.Vectors

/-! # Calculus: quadric surfaces and cylindrical / spherical coordinates

Points of space are `Fin 3 → ℝ` (coordinates `p 0 = x`, `p 1 = y`, `p 2 = z`). Quadric surfaces are sets of
points; their traces in the planes `z = k` (and the vertical coordinate planes for the paraboloid) are
stated as exact equivalences with the equation of an ellipse with explicit semi-axes. -/

namespace UndergradKB.Calculus

open Matrix

/-- A point `(x, y)` satisfies `x²/a² + y²/b² = m` (`m > 0`) iff it lies on the ellipse
`(x/A)² + (y/B)² = 1` with semi-axes `A = a √m`, `B = b √m`. -/
lemma ellipse_iff {a b m : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hm : 0 < m) (x y : ℝ) :
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = m ↔
      (x / (a * Real.sqrt m)) ^ 2 + (y / (b * Real.sqrt m)) ^ 2 = 1 := by
  have hs : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have : (x / (a * Real.sqrt m)) ^ 2 + (y / (b * Real.sqrt m)) ^ 2 = (x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2) / m := by
    rw [div_pow, div_pow, mul_pow, mul_pow, hs]
    field_simp
  rw [this, div_eq_one_iff_eq hm.ne']

/-- The ellipsoid `x²/a² + y²/b² + z²/c² = 1`. -/
def ellipsoid (a b c : ℝ) : Set (Fin 3 → ℝ) :=
  {p | p 0 ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2 + p 2 ^ 2 / c ^ 2 = 1}

/-- OpenStax Calculus 3:Example 2.56, p. 204 (CA-472): for `|k| < c` the trace of the ellipsoid in the
plane `z = k` is the ellipse `(x/A)² + (y/B)² = 1` with semi-axes `A = a √(1 − k²/c²)`,
`B = b √(1 − k²/c²)`. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (ellipsoid and its traces), p. 204"]
theorem ellipsoid_trace_z {a b c k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : |k| < c)
    (p : Fin 3 → ℝ) :
    (p ∈ ellipsoid a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt (1 - k ^ 2 / c ^ 2))) ^ 2 +
        (p 1 / (b * Real.sqrt (1 - k ^ 2 / c ^ 2))) ^ 2 = 1) := by
  have hk2 : k ^ 2 < c ^ 2 := by nlinarith [abs_lt.1 hk]
  have hm : 0 < 1 - k ^ 2 / c ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]; exact hk2
  simp only [ellipsoid, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h2, (ellipse_iff ha.ne' hb.ne' hm _ _).1 ?_⟩
    rw [h2] at h; linarith
  · rintro ⟨h2, h⟩
    have := (ellipse_iff ha.ne' hb.ne' hm _ _).2 h
    refine ⟨?_, h2⟩
    rw [h2]; linarith

/-- OpenStax Calculus 3:Example 2.56, p. 204 (CA-472): the traces of the ellipsoid in the other two
coordinate planes `x = 0`, `y = 0` are the ellipses `y²/b² + z²/c² = 1`, `x²/a² + z²/c² = 1`. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (ellipsoid and its traces), p. 204"]
theorem ellipsoid_trace_coordinate (a b c : ℝ) (p : Fin 3 → ℝ) :
    ((p ∈ ellipsoid a b c ∧ p 0 = 0) ↔ (p 0 = 0 ∧ p 1 ^ 2 / b ^ 2 + p 2 ^ 2 / c ^ 2 = 1)) ∧
    ((p ∈ ellipsoid a b c ∧ p 1 = 0) ↔ (p 1 = 0 ∧ p 0 ^ 2 / a ^ 2 + p 2 ^ 2 / c ^ 2 = 1)) := by
  simp only [ellipsoid, Set.mem_ofPred_eq]
  constructor
  · constructor
    · rintro ⟨h, h0⟩; rw [h0] at h; exact ⟨h0, by simpa using h⟩
    · rintro ⟨h0, h⟩; rw [h0]; exact ⟨by simpa using h, rfl⟩
  · constructor
    · rintro ⟨h, h0⟩; rw [h0] at h; exact ⟨h0, by simpa using h⟩
    · rintro ⟨h0, h⟩; rw [h0]; exact ⟨by simpa using h, rfl⟩

/-- OpenStax Calculus 3:§2.6 text (ellipsoid), p. 204 (CA-472): with `a = b = c = r > 0` the ellipsoid is
the sphere of radius `r` about the origin. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (ellipsoid and its traces), p. 204"]
theorem ellipsoid_eq_sphere {r : ℝ} (hr : 0 < r) (p : Fin 3 → ℝ) :
    p ∈ ellipsoid r r r ↔ len p = r := by
  simp only [ellipsoid, Set.mem_ofPred_eq]
  have h1 : p 0 ^ 2 / r ^ 2 + p 1 ^ 2 / r ^ 2 + p 2 ^ 2 / r ^ 2 = 1 ↔ p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = r ^ 2 := by
    rw [← add_div, ← add_div, div_eq_one_iff_eq (by positivity)]
  rw [h1]
  unfold len
  rw [dot_expand, Real.sqrt_eq_iff_mul_self_eq (by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2)]) hr.le]
  constructor <;> intro h <;> nlinarith

/-- The elliptic paraboloid `z = x²/a² + y²/b²`. -/
def ellipticParaboloid (a b : ℝ) : Set (Fin 3 → ℝ) :=
  {p | p 2 = p 0 ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2}

/-- OpenStax Calculus 3:Example 2.57, p. 206 (CA-473): for `k > 0` the trace of the elliptic
paraboloid in the plane `z = k` is the ellipse with semi-axes `a √k` and `b √k`. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (elliptic paraboloid), p. 205"]
theorem paraboloid_trace_horizontal {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (p : Fin 3 → ℝ) :
    (p ∈ ellipticParaboloid a b ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt k)) ^ 2 + (p 1 / (b * Real.sqrt k)) ^ 2 = 1) := by
  simp only [ellipticParaboloid, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, h2⟩
    exact ⟨h2, (ellipse_iff ha.ne' hb.ne' hk _ _).1 (by rw [← h, h2])⟩
  · rintro ⟨h2, h⟩
    have := (ellipse_iff ha.ne' hb.ne' hk _ _).2 h
    exact ⟨by rw [h2, this], h2⟩

/-- OpenStax Calculus 3:Example 2.57, p. 206 (CA-473): the trace of the elliptic paraboloid in `z = 0`
is the origin only, and in `z = k < 0` it is empty. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (elliptic paraboloid), p. 205"]
theorem paraboloid_trace_degenerate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Fin 3 → ℝ) :
    ((p ∈ ellipticParaboloid a b ∧ p 2 = 0) ↔ (p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0)) ∧
    (∀ k : ℝ, k < 0 → ¬ (p ∈ ellipticParaboloid a b ∧ p 2 = k)) := by
  simp only [ellipticParaboloid, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨h, h2⟩
      have hx : 0 ≤ p 0 ^ 2 / a ^ 2 := by positivity
      have hy : 0 ≤ p 1 ^ 2 / b ^ 2 := by positivity
      have hx0 : p 0 ^ 2 / a ^ 2 = 0 := by linarith
      have hy0 : p 1 ^ 2 / b ^ 2 = 0 := by linarith
      refine ⟨?_, ?_, h2⟩
      · have := (div_eq_zero_iff.1 hx0).resolve_right (by positivity)
        exact pow_eq_zero_iff two_ne_zero |>.1 this
      · have := (div_eq_zero_iff.1 hy0).resolve_right (by positivity)
        exact pow_eq_zero_iff two_ne_zero |>.1 this
    · rintro ⟨h0, h1, h2⟩
      refine ⟨?_, h2⟩
      rw [h2, h0, h1]; simp
  · rintro k hk ⟨h, h2⟩
    have hx : 0 ≤ p 0 ^ 2 / a ^ 2 := by positivity
    have hy : 0 ≤ p 1 ^ 2 / b ^ 2 := by positivity
    linarith

/-- OpenStax Calculus 3:Example 2.57, p. 206 (CA-473): the traces of the elliptic paraboloid in the
vertical planes `y = k` and `x = k` are the parabolas `z = x²/a² + k²/b²` and `z = k²/a² + y²/b²`. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (elliptic paraboloid), p. 205"]
theorem paraboloid_trace_vertical (a b k : ℝ) (p : Fin 3 → ℝ) :
    ((p ∈ ellipticParaboloid a b ∧ p 1 = k) ↔ (p 1 = k ∧ p 2 = p 0 ^ 2 / a ^ 2 + k ^ 2 / b ^ 2)) ∧
    ((p ∈ ellipticParaboloid a b ∧ p 0 = k) ↔ (p 0 = k ∧ p 2 = k ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2)) := by
  simp only [ellipticParaboloid, Set.mem_ofPred_eq]
  constructor
  · constructor
    · rintro ⟨h, h1⟩; rw [h1] at h; exact ⟨h1, h⟩
    · rintro ⟨h1, h⟩; rw [h1]; exact ⟨h, rfl⟩
  · constructor
    · rintro ⟨h, h1⟩; rw [h1] at h; exact ⟨h1, h⟩
    · rintro ⟨h1, h⟩; rw [h1]; exact ⟨h, rfl⟩

/-- The hyperboloid of one sheet `x²/a² + y²/b² − z²/c² = 1`. -/
def hyperboloidOne (a b c : ℝ) : Set (Fin 3 → ℝ) :=
  {p | p 0 ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2 - p 2 ^ 2 / c ^ 2 = 1}

/-- The hyperboloid of two sheets `z²/c² − x²/a² − y²/b² = 1`. -/
def hyperboloidTwo (a b c : ℝ) : Set (Fin 3 → ℝ) :=
  {p | p 2 ^ 2 / c ^ 2 - p 0 ^ 2 / a ^ 2 - p 1 ^ 2 / b ^ 2 = 1}

/-- The elliptic cone `z²/c² = x²/a² + y²/b²`. -/
def ellipticCone (a b c : ℝ) : Set (Fin 3 → ℝ) :=
  {p | p 2 ^ 2 / c ^ 2 = p 0 ^ 2 / a ^ 2 + p 1 ^ 2 / b ^ 2}

/-- The hyperbolic paraboloid `z = x²/a² − y²/b²`. -/
def hyperbolicParaboloid (a b : ℝ) : Set (Fin 3 → ℝ) :=
  {p | p 2 = p 0 ^ 2 / a ^ 2 - p 1 ^ 2 / b ^ 2}

/-- OpenStax Calculus 3:§2.6 table (standard quadric surfaces), p. 209 (CA-474): the horizontal trace
`z = k` of the hyperboloid of one sheet is, for every `k`, an ellipse with semi-axes
`a √(1 + k²/c²)` and `b √(1 + k²/c²)`. -/
@[kb "openstaxcalculus2016" "3:§2.6 text (hyperboloid of one sheet), p. 207"]
theorem hyperboloidOne_trace {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℝ)
    (p : Fin 3 → ℝ) :
    (p ∈ hyperboloidOne a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt (1 + k ^ 2 / c ^ 2))) ^ 2 +
        (p 1 / (b * Real.sqrt (1 + k ^ 2 / c ^ 2))) ^ 2 = 1) := by
  have hm : 0 < 1 + k ^ 2 / c ^ 2 := by positivity
  simp only [hyperboloidOne, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h2, (ellipse_iff ha.ne' hb.ne' hm _ _).1 ?_⟩
    rw [h2] at h; linarith
  · rintro ⟨h2, h⟩
    have := (ellipse_iff ha.ne' hb.ne' hm _ _).2 h
    refine ⟨?_, h2⟩
    rw [h2]; linarith

/-- OpenStax Calculus 3:§2.6 table (standard quadric surfaces), p. 209 (CA-474): the horizontal trace
`z = k` of the hyperboloid of two sheets is empty for `|k| < c` and, for `|k| > c`, an ellipse with
semi-axes `a √(k²/c² − 1)` and `b √(k²/c² − 1)`. -/
@[kb "openstaxcalculus2016" "3:§2.6 table (standard quadric surfaces, Figures 2.87 and 2.88), p. 209"]
theorem hyperboloidTwo_trace {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℝ)
    (p : Fin 3 → ℝ) :
    (|k| < c → ¬ (p ∈ hyperboloidTwo a b c ∧ p 2 = k)) ∧
    (c < |k| → ((p ∈ hyperboloidTwo a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * Real.sqrt (k ^ 2 / c ^ 2 - 1))) ^ 2 +
        (p 1 / (b * Real.sqrt (k ^ 2 / c ^ 2 - 1))) ^ 2 = 1))) := by
  simp only [hyperboloidTwo, Set.mem_ofPred_eq]
  refine ⟨fun hk ⟨h, h2⟩ => ?_, fun hk => ?_⟩
  · have hk2 : k ^ 2 < c ^ 2 := by nlinarith [abs_lt.1 hk]
    have : k ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact hk2
    have hx : 0 ≤ p 0 ^ 2 / a ^ 2 := by positivity
    have hy : 0 ≤ p 1 ^ 2 / b ^ 2 := by positivity
    rw [h2] at h; linarith
  · have hk2 : c ^ 2 < k ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg k]) hk
      rw [sq_abs] at this; exact this
    have hm : 0 < k ^ 2 / c ^ 2 - 1 := by
      rw [sub_pos, one_lt_div (by positivity)]; exact hk2
    constructor
    · rintro ⟨h, h2⟩
      refine ⟨h2, (ellipse_iff ha.ne' hb.ne' hm _ _).1 ?_⟩
      rw [h2] at h; linarith
    · rintro ⟨h2, h⟩
      have := (ellipse_iff ha.ne' hb.ne' hm _ _).2 h
      refine ⟨?_, h2⟩
      rw [h2]; linarith

/-- OpenStax Calculus 3:§2.6 table (standard quadric surfaces), p. 209 (CA-474): the trace of the
elliptic cone in the plane `z = k ≠ 0` is the ellipse with semi-axes `a |k|/c` and `b |k|/c`
(written with `√(k²/c²) = |k|/c`), and in `z = 0` it is the origin. -/
@[kb "openstaxcalculus2016" "3:§2.6 table (standard quadric surfaces, Figures 2.87 and 2.88), p. 209"]
theorem cone_trace {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (k : ℝ) (hk : k ≠ 0)
    (p : Fin 3 → ℝ) :
    (p ∈ ellipticCone a b c ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / (a * (|k| / c))) ^ 2 + (p 1 / (b * (|k| / c))) ^ 2 = 1) := by
  have hm : 0 < k ^ 2 / c ^ 2 := by positivity
  have hs : Real.sqrt (k ^ 2 / c ^ 2) = |k| / c := by
    rw [Real.sqrt_div (sq_nonneg k), Real.sqrt_sq_eq_abs, Real.sqrt_sq hc.le]
  simp only [ellipticCone, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h2, ?_⟩
    rw [← hs]
    refine (ellipse_iff ha.ne' hb.ne' hm _ _).1 ?_
    rw [h2] at h; linarith
  · rintro ⟨h2, h⟩
    rw [← hs] at h
    have := (ellipse_iff ha.ne' hb.ne' hm _ _).2 h
    refine ⟨?_, h2⟩
    rw [h2]; linarith

/-- OpenStax Calculus 3:§2.6 table (standard quadric surfaces), p. 209 (CA-474): the trace of the
elliptic cone `z²/c² = x²/a² + y²/b²` in `z = 0` is the origin. -/
@[kb "openstaxcalculus2016" "3:§2.6 table (standard quadric surfaces, Figures 2.87 and 2.88), p. 209"]
theorem cone_trace_zero {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Fin 3 → ℝ) :
    (p ∈ ellipticCone a b c ∧ p 2 = 0) ↔ (p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0) := by
  simp only [ellipticCone, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, h2⟩
    rw [h2] at h
    have hx : 0 ≤ p 0 ^ 2 / a ^ 2 := by positivity
    have hy : 0 ≤ p 1 ^ 2 / b ^ 2 := by positivity
    have hx0 : p 0 ^ 2 / a ^ 2 = 0 := by simp at h; linarith
    have hy0 : p 1 ^ 2 / b ^ 2 = 0 := by simp at h; linarith
    refine ⟨?_, ?_, h2⟩
    · exact pow_eq_zero_iff two_ne_zero |>.1 ((div_eq_zero_iff.1 hx0).resolve_right (by positivity))
    · exact pow_eq_zero_iff two_ne_zero |>.1 ((div_eq_zero_iff.1 hy0).resolve_right (by positivity))
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, h0, h1]; simp

/-- OpenStax Calculus 3:§2.6 table (standard quadric surfaces), p. 209 (CA-474): the horizontal trace
`z = k` of the hyperbolic paraboloid `z = x²/a² − y²/b²` is the hyperbola (`k ≠ 0`) or pair of lines
(`k = 0`) `x²/a² − y²/b² = k`, i.e. `(x/a − y/b)(x/a + y/b) = k`. -/
@[kb "openstaxcalculus2016" "3:§2.6 table (standard quadric surfaces, Figures 2.87 and 2.88), p. 209"]
theorem hyperbolicParaboloid_trace (a b k : ℝ) (p : Fin 3 → ℝ) :
    (p ∈ hyperbolicParaboloid a b ∧ p 2 = k) ↔
      (p 2 = k ∧ (p 0 / a - p 1 / b) * (p 0 / a + p 1 / b) = k) := by
  simp only [hyperbolicParaboloid, Set.mem_ofPred_eq]
  have e : (p 0 / a - p 1 / b) * (p 0 / a + p 1 / b) = p 0 ^ 2 / a ^ 2 - p 1 ^ 2 / b ^ 2 := by
    ring
  rw [e]
  constructor
  · rintro ⟨h, h2⟩; exact ⟨h2, by rw [← h, h2]⟩
  · rintro ⟨h2, h⟩; exact ⟨by rw [h2, h], h2⟩

/-! ## Cylindrical and spherical coordinates (CA-476, CA-478) -/

/-- Cartesian point `(r cos θ, r sin θ, z)` with cylindrical coordinates `(r, θ, z)`. -/
noncomputable def cylToCart (r θ z : ℝ) : Fin 3 → ℝ := ![r * Real.cos θ, r * Real.sin θ, z]

/-- Cartesian point with spherical coordinates `(ρ, θ, φ)`. -/
noncomputable def sphToCart (ρ θ φ : ℝ) : Fin 3 → ℝ :=
  ![ρ * Real.sin φ * Real.cos θ, ρ * Real.sin φ * Real.sin θ, ρ * Real.cos φ]

/-- OpenStax Calculus 3:Theorem 2.15, p. 218 (CA-476): `x = r cos θ`, `y = r sin θ`, `z = z`, hence
`r² = x² + y²`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.15, p. 218"]
theorem cylToCart_spec (r θ z : ℝ) :
    (cylToCart r θ z) 0 = r * Real.cos θ ∧ (cylToCart r θ z) 1 = r * Real.sin θ ∧
    (cylToCart r θ z) 2 = z ∧
    (cylToCart r θ z) 0 ^ 2 + (cylToCart r θ z) 1 ^ 2 = r ^ 2 := by
  have := Real.sin_sq_add_cos_sq θ
  refine ⟨by simp [cylToCart], by simp [cylToCart], by simp [cylToCart], ?_⟩
  simp only [cylToCart, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

/-- OpenStax Calculus 3:Theorem 2.15, p. 218 (CA-476), converse: every point `(x, y, z)` has
cylindrical coordinates `r = √(x²+y²)`, `θ = arg(x + iy)`, `z`, with `r² = x² + y²` and, if `x ≠ 0`,
`tan θ = y / x`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.15, p. 218"]
theorem cartesian_to_cylindrical (p : Fin 3 → ℝ) :
    p = cylToCart (Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) (Complex.arg ⟨p 0, p 1⟩) (p 2) ∧
    Real.sqrt (p 0 ^ 2 + p 1 ^ 2) ^ 2 = p 0 ^ 2 + p 1 ^ 2 ∧
    (p 0 ≠ 0 → Real.tan (Complex.arg ⟨p 0, p 1⟩) = p 1 / p 0) := by
  obtain ⟨h0, h1⟩ := plane_vector_components (p 0) (p 1)
  refine ⟨?_, Real.sq_sqrt (by positivity), fun hx => ?_⟩
  · ext i; fin_cases i
    · simpa [cylToCart] using h0
    · simpa [cylToCart] using h1
    · simp [cylToCart]
  · rw [Real.tan_eq_sin_div_cos]
    have hr : Real.sqrt (p 0 ^ 2 + p 1 ^ 2) ≠ 0 := by
      intro h
      rw [h] at h0
      exact hx (by simpa using h0)
    have hc : Real.cos (Complex.arg ⟨p 0, p 1⟩) ≠ 0 := by
      intro h
      rw [h] at h0
      exact hx (by simpa using h0)
    rw [div_eq_div_iff hc hx]
    calc Real.sin (Complex.arg ⟨p 0, p 1⟩) * p 0
        = Real.sin (Complex.arg ⟨p 0, p 1⟩) *
          (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) * Real.cos (Complex.arg ⟨p 0, p 1⟩)) := by rw [← h0]
      _ = (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) * Real.sin (Complex.arg ⟨p 0, p 1⟩)) *
          Real.cos (Complex.arg ⟨p 0, p 1⟩) := by ring
      _ = p 1 * Real.cos (Complex.arg ⟨p 0, p 1⟩) := by rw [← h1]

/-- OpenStax Calculus 3:Theorem 2.16, p. 223 (CA-478): `x = ρ sin φ cos θ`, `y = ρ sin φ sin θ`,
`z = ρ cos φ`, hence `ρ² = x² + y² + z²` (for `ρ ≥ 0`: `ρ` is the distance from the origin), and for
`0 ≤ φ ≤ π` the cylindrical radius is `r = √(x²+y²) = ρ sin φ`. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.16, p. 223"]
theorem sphToCart_spec {ρ φ : ℝ} (hρ : 0 ≤ ρ) (hφ0 : 0 ≤ φ) (hφπ : φ ≤ Real.pi) (θ : ℝ) :
    (sphToCart ρ θ φ) 0 = ρ * Real.sin φ * Real.cos θ ∧
    (sphToCart ρ θ φ) 1 = ρ * Real.sin φ * Real.sin θ ∧
    (sphToCart ρ θ φ) 2 = ρ * Real.cos φ ∧
    ρ ^ 2 = (sphToCart ρ θ φ) 0 ^ 2 + (sphToCart ρ θ φ) 1 ^ 2 + (sphToCart ρ θ φ) 2 ^ 2 ∧
    len (sphToCart ρ θ φ) = ρ ∧
    Real.sqrt ((sphToCart ρ θ φ) 0 ^ 2 + (sphToCart ρ θ φ) 1 ^ 2) = ρ * Real.sin φ ∧
    (sphToCart ρ θ φ) 2 = ρ * Real.cos φ := by
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ
  have hsq : ρ ^ 2 = (sphToCart ρ θ φ) 0 ^ 2 + (sphToCart ρ θ φ) 1 ^ 2 + (sphToCart ρ θ φ) 2 ^ 2 := by
    simp only [sphToCart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have : (ρ * Real.sin φ * Real.cos θ) ^ 2 + (ρ * Real.sin φ * Real.sin θ) ^ 2 =
        ρ ^ 2 * Real.sin φ ^ 2 := by nlinarith
    nlinarith
  refine ⟨by simp [sphToCart], by simp [sphToCart], by simp [sphToCart], hsq, ?_, ?_, by simp [sphToCart]⟩
  · unfold len
    rw [dot_expand]
    have : (sphToCart ρ θ φ) 0 * (sphToCart ρ θ φ) 0 + (sphToCart ρ θ φ) 1 * (sphToCart ρ θ φ) 1 +
        (sphToCart ρ θ φ) 2 * (sphToCart ρ θ φ) 2 = ρ ^ 2 := by rw [hsq]; ring
    rw [this, Real.sqrt_sq hρ]
  · have : (sphToCart ρ θ φ) 0 ^ 2 + (sphToCart ρ θ φ) 1 ^ 2 = (ρ * Real.sin φ) ^ 2 := by
      simp only [sphToCart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      nlinarith
    rw [this, Real.sqrt_sq (mul_nonneg hρ hs)]

/-- OpenStax Calculus 3:Theorem 2.16, p. 223 (CA-478), converse: every point `p` has spherical
coordinates `ρ = ‖p‖ ≥ 0`, `θ = arg(x + iy)`, `φ ∈ [0, π]` (with `ρ² = x² + y² + z²`), i.e. `p` is the
point with those coordinates. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.16, p. 223"]
theorem cartesian_to_spherical (p : Fin 3 → ℝ) :
    ∃ ρ θ φ : ℝ, 0 ≤ ρ ∧ 0 ≤ φ ∧ φ ≤ Real.pi ∧ p = sphToCart ρ θ φ ∧
      ρ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  by_cases hp : p = 0
  · refine ⟨0, 0, 0, le_refl _, le_refl _, Real.pi_pos.le, ?_, ?_⟩
    · rw [hp]; ext i; fin_cases i <;> simp [sphToCart]
    · rw [hp]; simp
  · have hl := len_pos hp
    have hρ2 : len p ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
      rw [len_sq, dot_expand]; ring
    set ρ := len p with hρ
    have hz : |p 2 / ρ| ≤ 1 := by
      rw [abs_div, abs_of_pos hl, div_le_one hl]
      refine abs_le_of_sq_le_sq' ?_ hl.le |> fun h => abs_le.2 h
      nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    obtain ⟨hz1, hz2⟩ := abs_le.1 hz
    refine ⟨ρ, Complex.arg ⟨p 0, p 1⟩, Real.arccos (p 2 / ρ), hl.le, Real.arccos_nonneg _,
      Real.arccos_le_pi _, ?_, hρ2⟩
    have hsin : Real.sin (Real.arccos (p 2 / ρ)) = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) / ρ := by
      rw [Real.sin_arccos]
      have : 1 - (p 2 / ρ) ^ 2 = (p 0 ^ 2 + p 1 ^ 2) / ρ ^ 2 := by
        field_simp; linarith
      rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq hl.le]
    obtain ⟨h0, h1⟩ := plane_vector_components (p 0) (p 1)
    have ex : p 0 = ρ * Real.sin (Real.arccos (p 2 / ρ)) * Real.cos (Complex.arg ⟨p 0, p 1⟩) := by
      rw [hsin]
      calc p 0 = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) * Real.cos (Complex.arg ⟨p 0, p 1⟩) := h0
        _ = _ := by field_simp
    have ey : p 1 = ρ * Real.sin (Real.arccos (p 2 / ρ)) * Real.sin (Complex.arg ⟨p 0, p 1⟩) := by
      rw [hsin]
      calc p 1 = Real.sqrt (p 0 ^ 2 + p 1 ^ 2) * Real.sin (Complex.arg ⟨p 0, p 1⟩) := h1
        _ = _ := by field_simp
    have ez : p 2 = ρ * Real.cos (Real.arccos (p 2 / ρ)) := by
      rw [Real.cos_arccos hz1 hz2]; field_simp
    ext i; fin_cases i
    · simpa [sphToCart] using ex
    · simpa [sphToCart] using ey
    · simpa [sphToCart] using ez

end UndergradKB.Calculus
