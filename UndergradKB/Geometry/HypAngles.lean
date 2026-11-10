import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import UndergradKB.Common.Attr
import UndergradKB.Geometry.HyperbolicDisc2

/-! # H-angles in the conformal disc model (Petrunin, chapters 12 and 13)

The h-angle at `Q` between the h-half-lines toward `P` and `R` is the Euclidean angle between their
tangent half-lines at `Q` (book Definition p. 93).  The h-motion `mobius Q` sends `Q` to the centre,
where h-lines are diameters, and its derivative at `Q` is a positive real number, so the tangent
direction at `Q` of the h-half-line `[QP)_h` is the direction of `mobius Q P`.  Hence
`hoangle P Q R` (signed, in `Real.Angle`) is the argument of `mobius Q R / mobius Q P` and
`hangle P Q R` (unsigned) is the angle between the vectors `mobius Q P`, `mobius Q R` of `ℂ`.

Contents: Definition p. 93 with the tangent theorem and motion invariance, Axioms IIIa, IIIb, IIIc, IV
(Claims 12.16-12.19), asymptotically/ultra parallel h-lines and the angle of parallelism (pp. 103-104). -/

namespace UndergradKB.Geometry

open Real Complex ComplexConjugate Filter Topology

/-! ### Definitions -/

/-- The signed h-angle `∡_h P Q R` at `Q` from the h-half-line `[QP)_h` to `[QR)_h`, as an element
of `Real.Angle`: the argument of `mobius Q R / mobius Q P` (book Definition p. 93, via the tangent
directions at `Q`, see `hcurve_tangent`). -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
noncomputable def hoangle (P Q R : ℂ) : Real.Angle := ((mobius Q R / mobius Q P).arg : Real.Angle)

/-- The unsigned h-angle `∠_h P Q R ∈ [0, π]` at `Q`: the Euclidean angle between the tangent
vectors `mobius Q P` and `mobius Q R` (book Definition p. 93). -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
noncomputable def hangle (P Q R : ℂ) : ℝ :=
  InnerProductGeometry.angle (mobius Q P) (mobius Q R)

/-- The h-half-line `[QP)_h` from `Q` through `P`: the points `z` of the disc with
`mobius Q z` a nonnegative real multiple of `mobius Q P` (the h-lines through `Q` become the
diameters under `mobius Q`). -/
def hray (Q P : ℂ) : Set ℂ := {z | ‖z‖ < 1 ∧ ∃ s : ℝ, 0 ≤ s ∧ mobius Q z = s * mobius Q P}

section Algebra

variable {a Q P R u w : ℂ}

theorem ofReal_one_sub_sq (a : ℂ) : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) = 1 - a * conj a := by
  have e : (‖a‖ : ℂ) ^ 2 = a * conj a := by
    have := Complex.mul_conj a
    rw [Complex.normSq_eq_norm_sq] at this
    rw [this]; push_cast; ring
  push_cast
  rw [e]

theorem mobius_eq_zero_iff (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) : mobius Q P = 0 ↔ P = Q := by
  unfold mobius
  rw [div_eq_zero_iff, sub_eq_zero]
  simp [mobius_den_ne hQ hP]

theorem mobius_ne_zero (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) (h : P ≠ Q) : mobius Q P ≠ 0 :=
  fun h' => h ((mobius_eq_zero_iff hQ hP).mp h')

theorem mobius_neg_zero : mobius (-Q) 0 = Q := by simp [mobius]

theorem mobius_mobius_neg (hQ : ‖Q‖ < 1) (hw : ‖w‖ < 1) : mobius Q (mobius (-Q) w) = w := by
  have := mobius_neg_mobius (a := -Q) (z := w) (by simpa using hQ) hw
  simpa using this

theorem mobius_rot (hu : ‖u‖ = 1) (p q : ℂ) : mobius (u * q) (u * p) = u * mobius q p := by
  have h1 : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
  have h2 : 1 - conj (u * q) * (u * p) = 1 - conj q * p := by
    rw [map_mul]; linear_combination (-(conj q * p)) * h1
  unfold mobius
  rw [h2]; ring

/-- Composition of an h-motion `mobius a` with the pair `(Q, P)`: the vector `mobius (φ Q) (φ P)`
is a unit multiple of `mobius Q P`. -/
theorem mobius_pair (ha : ‖a‖ < 1) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) :
    mobius (mobius a Q) (mobius a P) =
      (conj (1 - conj a * Q) / (1 - conj a * Q)) * mobius Q P := by
  have dP := mobius_den_ne ha hP
  have dQ := mobius_den_ne ha hQ
  have dQP := mobius_den_ne hQ hP
  have hcd : conj (1 - conj a * Q) ≠ 0 := (map_ne_zero _).mpr dQ
  have hk : (1 - a * conj a) ≠ 0 := by
    rw [← ofReal_one_sub_sq]; exact_mod_cast (one_sub_sq_pos ha).ne'
  have e1 : conj (1 - conj a * Q) = 1 - a * conj Q := by simp
  have n1 : 1 - a * conj Q ≠ 0 := by rwa [e1] at hcd
  have n3 : 1 - P * conj a ≠ 0 := by rwa [mul_comm]
  have n4 : 1 - Q * conj a ≠ 0 := by rwa [mul_comm]
  have n5 : 1 - P * conj Q ≠ 0 := by rwa [mul_comm]
  have n2 : 1 - conj Q * a ≠ 0 := by rwa [mul_comm]
  have key : 1 - conj (mobius a Q) * mobius a P =
      ((1 - a * conj a) * (1 - conj Q * P)) / (conj (1 - conj a * Q) * (1 - conj a * P)) := by
    simp only [mobius, map_div₀, map_sub, map_mul, map_one, Complex.conj_conj]
    field_simp
    ring
  have hs := mobius_sub ha hP hQ
  rw [ofReal_one_sub_sq] at hs
  conv_lhs => rw [show mobius (mobius a Q) (mobius a P) =
      (mobius a P - mobius a Q) / (1 - conj (mobius a Q) * mobius a P) from rfl]
  rw [hs, key, show mobius Q P = (P - Q) / (1 - conj Q * P) from rfl, e1]
  field_simp

theorem norm_conj_div (d : ℂ) (hd : d ≠ 0) : ‖conj d / d‖ = 1 := by
  rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hd)]

/-- The pair-vector of the h-motion `z ↦ u * mobius a z` at `Q` is a unit multiple of `mobius Q ·`. -/
theorem mobius_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (hQ : ‖Q‖ < 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ P : ℂ, ‖P‖ < 1 →
      mobius (u * mobius a Q) (u * mobius a P) = c * mobius Q P := by
  refine ⟨u * (conj (1 - conj a * Q) / (1 - conj a * Q)), ?_, fun P hP => ?_⟩
  · rw [norm_mul, hu, norm_conj_div _ (mobius_den_ne ha hQ), one_mul]
  · rw [mobius_rot hu, mobius_pair ha hP hQ, mul_assoc]

end Algebra

/-! ### Row 1: the definition, the tangent theorem, motion invariance -/

section Tangent

variable {Q P : ℂ}

theorem hasDerivAt_mobius_neg_zero (hQ : ‖Q‖ < 1) :
    HasDerivAt (mobius (-Q)) (((1 - ‖Q‖ ^ 2 : ℝ) : ℂ)) 0 := by
  have h1 : HasDerivAt (fun z : ℂ => z - -Q) 1 0 := (hasDerivAt_id (0 : ℂ)).sub_const _
  have h2 : HasDerivAt (fun z : ℂ => 1 - conj (-Q) * z) (-(conj (-Q))) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).const_mul (conj (-Q))).const_sub 1
    simpa using this
  have hd : (1 - conj (-Q) * (0 : ℂ)) ≠ 0 := by simp
  have := h1.div h2 hd
  refine HasDerivAt.congr_deriv this ?_
  rw [ofReal_one_sub_sq]
  simp only [map_neg, mul_zero, sub_zero, neg_neg, zero_sub, one_pow, div_one]
  ring

theorem hasDerivAt_hcurve (hQ : ‖Q‖ < 1) (m : ℂ) :
    HasDerivAt (fun t : ℝ => mobius (-Q) ((t : ℂ) * m)) (((1 - ‖Q‖ ^ 2 : ℝ) : ℂ) * m) 0 := by
  have h1 : HasDerivAt (fun z : ℂ => z * m) m ((0 : ℝ) : ℂ) := by
    simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const m
  have h2 : HasDerivAt (mobius (-Q)) (((1 - ‖Q‖ ^ 2 : ℝ) : ℂ)) ((0 : ℂ) * m) := by
    simpa using hasDerivAt_mobius_neg_zero hQ
  have h3 := h2.scomp ((0 : ℝ) : ℂ) h1
  have h5 : HasDerivAt (fun z : ℂ => mobius (-Q) (z * m)) (((1 - ‖Q‖ ^ 2 : ℝ) : ℂ) * m)
      ((0 : ℝ) : ℂ) := h3.congr_deriv (by simp [mul_comm])
  exact HasDerivAt.comp_ofReal (e := fun z : ℂ => mobius (-Q) (z * m)) h5

/-- The tangent theorem justifying the definition of the h-angle (book Definition p. 93).  For
`P ≠ Q` in the disc, the curve `γ t = mobius (-Q) (t · mobius Q P)` (the h-half-line `[QP)_h`,
a diameter transported by the h-motion) runs from `Q` (`t = 0`) to `P` (`t = 1`), stays in the disc,
`Q γ(t)` has h-length `hdist 0 (t · mobius Q P)`, and its velocity at `Q` is the positive real
multiple `(1 - ‖Q‖²)` of `mobius Q P`. -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
theorem hcurve_tangent (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) :
    (mobius (-Q) (((0 : ℝ) : ℂ) * mobius Q P) = Q) ∧
    (mobius (-Q) (((1 : ℝ) : ℂ) * mobius Q P) = P) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖mobius (-Q) ((t : ℂ) * mobius Q P)‖ < 1 ∧
      hdist Q (mobius (-Q) ((t : ℂ) * mobius Q P)) = hdist 0 ((t : ℂ) * mobius Q P)) ∧
    0 < 1 - ‖Q‖ ^ 2 ∧
    HasDerivAt (fun t : ℝ => mobius (-Q) ((t : ℂ) * mobius Q P))
      (((1 - ‖Q‖ ^ 2 : ℝ) : ℂ) * mobius Q P) 0 := by
  have hm := norm_mobius_lt_one hQ hP
  refine ⟨by simp [mobius_neg_zero], by simpa using mobius_neg_mobius hQ hP,
    fun t h0 h1 => ?_, one_sub_sq_pos hQ, hasDerivAt_hcurve hQ _⟩
  have hw : ‖(t : ℂ) * mobius Q P‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    nlinarith [norm_nonneg (mobius Q P)]
  have hn : ‖(-Q)‖ < 1 := by simpa using hQ
  refine ⟨norm_mobius_lt_one hn hw, ?_⟩
  have hg := norm_mobius_lt_one hn hw
  rw [← hdist_mobius hQ hQ hg, mobius_self hQ, mobius_mobius_neg hQ hw]

end Tangent

section Invariance

variable {a Q P R u : ℂ}

/-- Invariance of the signed h-angle under the h-motions `z ↦ u * mobius a z`. -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
theorem hoangle_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (hR : ‖R‖ < 1) :
    hoangle (u * mobius a P) (u * mobius a Q) (u * mobius a R) = hoangle P Q R := by
  obtain ⟨c, hc, h⟩ := mobius_motion ha hu hQ
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at hc; simp at hc
  unfold hoangle
  rw [h P hP, h R hR, mul_div_mul_left _ _ hc0]

/-- Invariance of the unsigned h-angle under the h-motions `z ↦ u * mobius a z`. -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
theorem hangle_motion (ha : ‖a‖ < 1) (hu : ‖u‖ = 1) (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1)
    (hR : ‖R‖ < 1) :
    hangle (u * mobius a P) (u * mobius a Q) (u * mobius a R) = hangle P Q R := by
  obtain ⟨c, hc, h⟩ := mobius_motion ha hu hQ
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at hc; simp at hc
  unfold hangle
  rw [h P hP, h R hR]
  exact Complex.angle_mul_left hc0 _ _

theorem mobius_conj (Q P : ℂ) : mobius (conj Q) (conj P) = conj (mobius Q P) := by
  simp [mobius]

/-- The reflection `z ↦ conj z` preserves the unsigned h-angle. -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
theorem hangle_conj (P Q R : ℂ) : hangle (conj P) (conj Q) (conj R) = hangle P Q R := by
  unfold hangle
  rw [mobius_conj, mobius_conj]
  exact (Complex.conjLIE.toLinearIsometry).angle_map _ _

/-- The reflection `z ↦ conj z` negates the signed h-angle. -/
@[kb "petrunin2025" "Definition (h-angle), p. 93"]
theorem hoangle_conj (P Q R : ℂ) : hoangle (conj P) (conj Q) (conj R) = -hoangle P Q R := by
  unfold hoangle
  rw [mobius_conj, mobius_conj, ← map_div₀]
  exact Complex.arg_conj_coe_angle _

theorem hangle_eq_abs (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) (hR : ‖R‖ < 1) (hPQ : P ≠ Q) (hRQ : R ≠ Q) :
    hangle P Q R = |(mobius Q P / mobius Q R).arg| :=
  Complex.angle_eq_abs_arg (mobius_ne_zero hQ hP hPQ) (mobius_ne_zero hQ hR hRQ)

end Invariance

/-! ### Row 2: Axiom IIIa (Claim 12.16) -/

section AxiomIIIa

variable {Q P R R' : ℂ}

theorem hray_eq_of_pos {s : ℝ} (hs : 0 < s) (h : mobius Q R' = s * mobius Q R) :
    hray Q R' = hray Q R := by
  ext z
  constructor
  · rintro ⟨hz, t, ht, e⟩
    exact ⟨hz, t * s, mul_nonneg ht hs.le, by rw [e, h]; push_cast; ring⟩
  · rintro ⟨hz, t, ht, e⟩
    refine ⟨hz, t / s, div_nonneg ht hs.le, ?_⟩
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [e, h]; push_cast; field_simp

/-- Claim 12.16, existence (Axiom IIIa): from `Q`, for a point `P ≠ Q` and a signed angle `α`
there is a point `R ≠ Q` with `∡_h P Q R = α`. -/
@[kb "petrunin2025" "Claim 12.16, p. 99"]
theorem hoangle_exists (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) (hPQ : P ≠ Q) (α : Real.Angle) :
    ∃ R : ℂ, ‖R‖ < 1 ∧ R ≠ Q ∧ hoangle P Q R = α := by
  have hm0 := mobius_ne_zero hQ hP hPQ
  have hmpos : 0 < ‖mobius Q P‖ := norm_pos_iff.mpr hm0
  set θ : ℝ := α.toReal with hθ
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hen : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  set w : ℂ := e * mobius Q P / ((2 * ‖mobius Q P‖ : ℝ) : ℂ) with hw
  have hwn : ‖w‖ = 1 / 2 := by
    rw [hw, norm_div, norm_mul, hen, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hw1 : ‖w‖ < 1 := by rw [hwn]; norm_num
  have hw0 : w ≠ 0 := by intro h0; rw [h0] at hwn; simp at hwn
  have hmw : mobius Q (mobius (-Q) w) = w := mobius_mobius_neg hQ hw1
  have hn : ‖(-Q)‖ < 1 := by simpa using hQ
  refine ⟨mobius (-Q) w, norm_mobius_lt_one hn hw1, ?_, ?_⟩
  · intro h
    rw [h, mobius_self hQ] at hmw
    exact hw0 hmw.symm
  · unfold hoangle
    rw [hmw]
    have : w / mobius Q P = (((1 / (2 * ‖mobius Q P‖) : ℝ)) : ℂ) *
        (Complex.cos θ + Complex.sin θ * Complex.I) := by
      rw [hw, he, Complex.exp_mul_I]
      push_cast
      field_simp
    rw [this, Complex.arg_real_mul _ (by positivity),
      Complex.arg_cos_add_sin_mul_I (Real.Angle.toReal_mem_Ioc α)]
    simp [hθ]

/-- Claim 12.16, uniqueness (Axiom IIIa): two points `R, R'` (different from `Q`) forming the same
signed h-angle with `[QP)_h` lie on the same h-half-line from `Q`: their half-lines coincide. -/
@[kb "petrunin2025" "Claim 12.16, p. 99"]
theorem hoangle_unique (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) (hR : ‖R‖ < 1) (hR' : ‖R'‖ < 1)
    (hPQ : P ≠ Q) (hRQ : R ≠ Q) (hRQ' : R' ≠ Q) (h : hoangle P Q R = hoangle P Q R') :
    hray Q R' = hray Q R := by
  have hm0 := mobius_ne_zero hQ hP hPQ
  have h1 := mobius_ne_zero hQ hR hRQ
  have h2 := mobius_ne_zero hQ hR' hRQ'
  unfold hoangle at h
  have hx : (mobius Q R / mobius Q P) ≠ 0 := div_ne_zero h1 hm0
  have hy : (mobius Q R' / mobius Q P) ≠ 0 := div_ne_zero h2 hm0
  have harg : (mobius Q R / mobius Q P).arg = (mobius Q R' / mobius Q P).arg := by
    have e1 := Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨Complex.neg_pi_lt_arg (mobius Q R / mobius Q P), Complex.arg_le_pi _⟩
    have e2 := Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨Complex.neg_pi_lt_arg (mobius Q R' / mobius Q P), Complex.arg_le_pi _⟩
    rw [← e1, ← e2, h]
  have this := (Complex.arg_eq_arg_iff hx hy).mp harg
  have p1 := norm_pos_iff.mpr h1
  have p2 := norm_pos_iff.mpr h2
  have p0 := norm_pos_iff.mpr hm0
  refine hray_eq_of_pos (s := ‖mobius Q R'‖ / ‖mobius Q R‖) (by positivity) ?_
  rw [norm_div, norm_div] at this
  have e2 : ((‖mobius Q R'‖ : ℂ) * mobius Q R) / (‖mobius Q R‖ : ℂ) = mobius Q R' := by
    have hp0 : (‖mobius Q P‖ : ℂ) ≠ 0 := by exact_mod_cast p0.ne'
    have hq0 : (‖mobius Q R‖ : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
    have hm0' : mobius Q P ≠ 0 := hm0
    push_cast at this
    field_simp at this
    field_simp
    exact this
  refine e2.symm.trans ?_
  push_cast; ring

end AxiomIIIa

/-! ### Row 3: Axiom IIIb (Claim 12.17) -/

/-- Claim 12.17 (Axiom IIIb): h-angles add, `∡_h P Q R + ∡_h R Q S = ∡_h P Q S`
(for `P, R, S ≠ Q`). -/
@[kb "petrunin2025" "Claim 12.17, p. 99"]
theorem hoangle_add {P Q R S : ℂ} (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) (hR : ‖R‖ < 1) (hS : ‖S‖ < 1)
    (hPQ : P ≠ Q) (hRQ : R ≠ Q) (hSQ : S ≠ Q) :
    hoangle P Q R + hoangle R Q S = hoangle P Q S := by
  have h1 := mobius_ne_zero hQ hP hPQ
  have h2 := mobius_ne_zero hQ hR hRQ
  have h3 := mobius_ne_zero hQ hS hSQ
  unfold hoangle
  rw [← Complex.arg_mul_coe_angle (div_ne_zero h2 h1) (div_ne_zero h3 h2)]
  congr 2
  field_simp

/-! ### Row 4: Axiom IIIc (Claim 12.18) -/

/-- The non-degenerate configurations `(P, Q, R)`: all in the disc and `P, R ≠ Q`. -/
def HNondeg : Set (ℂ × ℂ × ℂ) :=
  {p | ‖p.1‖ < 1 ∧ ‖p.2.1‖ < 1 ∧ ‖p.2.2‖ < 1 ∧ p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.2.1}

theorem continuousOn_mobius_pair :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.2.2) {p | ‖p.2.1‖ < 1 ∧ ‖p.2.2‖ < 1} := by
  have hc1 : Continuous fun p : ℂ × ℂ × ℂ => p.2.2 - p.2.1 := by fun_prop
  have hc2 : Continuous fun p : ℂ × ℂ × ℂ => 1 - conj p.2.1 * p.2.2 := by fun_prop
  exact hc1.continuousOn.div hc2.continuousOn (fun p hp => mobius_den_ne hp.1 hp.2)

theorem continuousOn_mobius_pair' :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.1) {p | ‖p.2.1‖ < 1 ∧ ‖p.1‖ < 1} := by
  have hc1 : Continuous fun p : ℂ × ℂ × ℂ => p.1 - p.2.1 := by fun_prop
  have hc2 : Continuous fun p : ℂ × ℂ × ℂ => 1 - conj p.2.1 * p.1 := by fun_prop
  exact hc1.continuousOn.div hc2.continuousOn (fun p hp => mobius_den_ne hp.1 hp.2)

/-- Claim 12.18 (Axiom IIIc): the signed h-angle `∡_h P Q R ∈ Real.Angle` depends continuously on
`(P, Q, R)` away from the degenerate configurations `P = Q` or `R = Q`. -/
@[kb "petrunin2025" "Claim 12.18, p. 100"]
theorem continuousOn_hoangle :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => hoangle p.1 p.2.1 p.2.2) HNondeg := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hP := mobius_ne_zero h2 h1 h4
  have hR := mobius_ne_zero h2 h3 h5
  have c1 : ContinuousWithinAt (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.2.2) HNondeg p :=
    (continuousOn_mobius_pair p ⟨h2, h3⟩).mono (fun q hq => ⟨hq.2.1, hq.2.2.1⟩)
  have c2 : ContinuousWithinAt (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.1) HNondeg p :=
    (continuousOn_mobius_pair' p ⟨h2, h1⟩).mono (fun q hq => ⟨hq.2.1, hq.1⟩)
  have c3 : ContinuousWithinAt (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.2.2 / mobius p.2.1 p.1)
      HNondeg p := c1.div c2 hP
  exact (Complex.continuousAt_arg_coe_angle (div_ne_zero hR hP)).comp_continuousWithinAt
    (f := fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.2.2 / mobius p.2.1 p.1) c3

/-- Claim 12.18 (Axiom IIIc), unsigned form: `∠_h P Q R` is continuous in `(P, Q, R)` away from the
degenerate configurations. -/
@[kb "petrunin2025" "Claim 12.18, p. 100"]
theorem continuousOn_hangle :
    ContinuousOn (fun p : ℂ × ℂ × ℂ => hangle p.1 p.2.1 p.2.2) HNondeg := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  have hP := mobius_ne_zero h2 h1 h4
  have hR := mobius_ne_zero h2 h3 h5
  have c1 : ContinuousWithinAt (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.2.2) HNondeg p :=
    (continuousOn_mobius_pair p ⟨h2, h3⟩).mono (fun q hq => ⟨hq.2.1, hq.2.2.1⟩)
  have c2 : ContinuousWithinAt (fun p : ℂ × ℂ × ℂ => mobius p.2.1 p.1) HNondeg p :=
    (continuousOn_mobius_pair' p ⟨h2, h1⟩).mono (fun q hq => ⟨hq.2.1, hq.1⟩)
  have c3 : ContinuousWithinAt
      (fun p : ℂ × ℂ × ℂ => (mobius p.2.1 p.1, mobius p.2.1 p.2.2)) HNondeg p := c2.prodMk c1
  exact (InnerProductGeometry.continuousAt_angle (x := (mobius p.2.1 p.1, mobius p.2.1 p.2.2))
    hP hR).comp_continuousWithinAt
    (f := fun p : ℂ × ℂ × ℂ => (mobius p.2.1 p.1, mobius p.2.1 p.2.2)) c3

/-! ### Row 5: Axiom IV, SAS (Claim 12.19) -/

section SAS

theorem hdist_eq_mobius {Q P : ℂ} (hQ : ‖Q‖ < 1) (hP : ‖P‖ < 1) :
    hdist Q P = hdist 0 (mobius Q P) := by
  rw [← hdist_mobius hQ hQ hP, mobius_self hQ]

theorem norm_eq_of_hdist_zero {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (h : hdist 0 x = hdist 0 y) : ‖x‖ = ‖y‖ := by
  have h1 := (hdist_zero_eq_iff (r := hdist 0 x) hx).mp rfl
  have h2 := (hdist_zero_eq_iff (r := hdist 0 y) hy).mp rfl
  rw [h1, h2, h]

theorem hcosh_unit_mul {v : ℂ} (hv : ‖v‖ = 1) (x y : ℂ) : hcosh (v * x) (v * y) = hcosh x y := by
  unfold hcosh
  rw [← mul_sub, norm_mul, norm_mul, norm_mul, hv]
  simp

theorem hcosh_conj (x y : ℂ) : hcosh (conj x) (conj y) = hcosh x y := by
  unfold hcosh
  rw [← map_sub, Complex.norm_conj, Complex.norm_conj, Complex.norm_conj]

/-- Planar congruence: two pairs of nonzero vectors of `ℂ` with equal lengths and equal angle are
related by a rotation, possibly composed with the reflection `conj`. -/
theorem exists_rot_of_angle_eq {x y x' y' : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hx' : x' ≠ 0)
    (hy' : y' ≠ 0) (hnx : ‖x'‖ = ‖x‖) (hny : ‖y'‖ = ‖y‖)
    (hang : InnerProductGeometry.angle x y = InnerProductGeometry.angle x' y') :
    ∃ v : ℂ, ‖v‖ = 1 ∧ ((v * x = x' ∧ v * y = y') ∨ (v * conj x = x' ∧ v * conj y = y')) := by
  rw [Complex.angle_eq_abs_arg hx hy, Complex.angle_eq_abs_arg hx' hy'] at hang
  have hr : ‖x' / y'‖ = ‖x / y‖ := by rw [norm_div, norm_div, hnx, hny]
  have hxn : (x : ℂ) ≠ 0 := hx
  have hcx : conj x ≠ 0 := by simpa using hx
  have hcy : conj y ≠ 0 := by simpa using hy
  rcases abs_eq_abs.mp hang with h | h
  · -- same orientation
    have hrr : x' / y' = x / y := Complex.ext_norm_arg_iff.mpr ⟨hr, h.symm⟩
    refine ⟨x' / x, ?_, Or.inl ⟨by field_simp, ?_⟩⟩
    · rw [norm_div, hnx, div_self (norm_ne_zero_iff.mpr hx)]
    · rw [div_eq_div_iff hy' hy] at hrr
      field_simp
      linear_combination hrr
  · by_cases hpi : (x / y).arg = π
    · exfalso
      rw [hpi] at h
      linarith [Complex.neg_pi_lt_arg (x' / y')]
    · have hc : x' / y' = conj (x / y) := by
        refine Complex.ext_norm_arg_iff.mpr ⟨by rw [hr, Complex.norm_conj], ?_⟩
        rw [Complex.arg_conj]; simp only [hpi, ↓reduceIte]; linarith
      refine ⟨x' / conj x, ?_, Or.inr ⟨by field_simp, ?_⟩⟩
      · rw [norm_div, hnx, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hx)]
      · rw [map_div₀, div_eq_div_iff hy' hcy] at hc
        field_simp
        linear_combination hc

/-- The h-motion `z ↦ mobius (-Q') (v · mobius Q z)`: moves `Q` to the centre, rotates by `v`, and
moves the centre to `Q'`. -/
noncomputable def hmotion (Q' v Q z : ℂ) : ℂ := mobius (-Q') (v * mobius Q z)

/-- The h-motion `hmotion` composed with the reflection `z ↦ conj z` in the centre. -/
noncomputable def hmotionConj (Q' v Q z : ℂ) : ℂ := mobius (-Q') (v * conj (mobius Q z))

/-- Claim 12.19 (Axiom IV, SAS): let `PQR` and `P'Q'R'` be non-degenerate h-triangles with
`QP_h = Q'P'_h`, `QR_h = Q'R'_h` and equal h-angles at `Q`, `Q'`.  Then `PR_h = P'R'_h`, and the
triangles are congruent: there is an h-motion (a composite of `mobius`-motions, a rotation about the
centre and possibly the reflection `conj`) taking `Q, P, R` to `Q', P', R'`. -/
@[kb "petrunin2025" "Claim 12.19, p. 100"]
theorem hsas {P Q R P' Q' R' : ℂ} (hP : ‖P‖ < 1) (hQ : ‖Q‖ < 1) (hR : ‖R‖ < 1)
    (hP' : ‖P'‖ < 1) (hQ' : ‖Q'‖ < 1) (hR' : ‖R'‖ < 1) (hPQ : P ≠ Q) (hRQ : R ≠ Q)
    (hPQ' : P' ≠ Q') (hRQ' : R' ≠ Q') (h1 : hdist Q P = hdist Q' P') (h2 : hdist Q R = hdist Q' R')
    (h3 : hangle P Q R = hangle P' Q' R') :
    hdist P R = hdist P' R' ∧ ∃ v : ℂ, ‖v‖ = 1 ∧
      ((hmotion Q' v Q Q = Q' ∧ hmotion Q' v Q P = P' ∧ hmotion Q' v Q R = R') ∨
       (hmotionConj Q' v Q Q = Q' ∧ hmotionConj Q' v Q P = P' ∧ hmotionConj Q' v Q R = R')) := by
  have mP := norm_mobius_lt_one hQ hP
  have mR := norm_mobius_lt_one hQ hR
  have mP' := norm_mobius_lt_one hQ' hP'
  have mR' := norm_mobius_lt_one hQ' hR'
  have hn : ‖(-Q')‖ < 1 := by simpa using hQ'
  rw [hdist_eq_mobius hQ hP, hdist_eq_mobius hQ' hP'] at h1
  rw [hdist_eq_mobius hQ hR, hdist_eq_mobius hQ' hR'] at h2
  have n1 := norm_eq_of_hdist_zero mP mP' h1
  have n2 := norm_eq_of_hdist_zero mR mR' h2
  obtain ⟨v, hv, hcase⟩ := exists_rot_of_angle_eq (mobius_ne_zero hQ hP hPQ)
    (mobius_ne_zero hQ hR hRQ) (mobius_ne_zero hQ' hP' hPQ') (mobius_ne_zero hQ' hR' hRQ')
    n1.symm n2.symm h3
  refine ⟨?_, v, hv, ?_⟩
  · rw [← hdist_mobius hQ hP hR, ← hdist_mobius hQ' hP' hR']
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2]; unfold hdist; rw [hcosh_unit_mul hv]
    · rw [← e1, ← e2]; unfold hdist; rw [hcosh_unit_mul hv, hcosh_conj]
  · have g0 : mobius (-Q') 0 = Q' := mobius_neg_zero
    rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      refine ⟨?_, ?_, ?_⟩
      · simp [hmotion, mobius_self hQ, g0]
      · simp only [hmotion]; rw [e1]; simpa using mobius_neg_mobius hQ' hP'
      · simp only [hmotion]; rw [e2]; simpa using mobius_neg_mobius hQ' hR'
    · right
      refine ⟨?_, ?_, ?_⟩
      · simp [hmotionConj, mobius_self hQ, g0]
      · simp only [hmotionConj]; rw [e1]; simpa using mobius_neg_mobius hQ' hP'
      · simp only [hmotionConj]; rw [e2]; simpa using mobius_neg_mobius hQ' hR'

end SAS

/-! ### Row 6: parallels (pp. 103-104) -/

section Parallels

/-- The h-angle at `P` between the h-half-line toward the h-point `Q` and the h-half-line toward the
ideal point `A` (a point of the absolute): the Euclidean angle between the tangent vectors
`mobius P Q` and `mobius P A` (for `‖A‖ = 1`, `mobius P A` is the direction at `P` of the h-ray to
`A`). -/
noncomputable def hangleIdeal (P Q A : ℂ) : ℝ :=
  InnerProductGeometry.angle (mobius P Q) (mobius P A)

/-- Definition p. 103: the h-lines `hline α c` and `hline α' c'` (with `α² < ‖c‖²`, `α'² < ‖c'‖²`)
are asymptotically parallel if they are different and share an ideal point. -/
@[kb "petrunin2025" "Definition (asymptotically parallel), p. 103"]
def AsymParallel (α : ℝ) (c : ℂ) (α' : ℝ) (c' : ℂ) : Prop :=
  α ^ 2 < ‖c‖ ^ 2 ∧ α' ^ 2 < ‖c'‖ ^ 2 ∧ idealPts α c ≠ idealPts α' c' ∧
    (idealPts α c ∩ idealPts α' c').Nonempty

/-- Definition p. 104: two h-lines are ultra parallel if they are disjoint (and so parallel) but not
asymptotically parallel: they have no common point and no common ideal point. -/
@[kb "petrunin2025" "Definition (ultra parallel), p. 104"]
def UltraParallel (α : ℝ) (c : ℂ) (α' : ℝ) (c' : ℂ) : Prop :=
  α ^ 2 < ‖c‖ ^ 2 ∧ α' ^ 2 < ‖c'‖ ^ 2 ∧ Disjoint (hline α c) (hline α' c') ∧
    Disjoint (idealPts α c) (idealPts α' c')

theorem exists_two_idealPts {α : ℝ} {c : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) :
    ∃ A B : ℂ, A ≠ B ∧ A ∈ idealPts α c ∧ B ∈ idealPts α c := by
  have hN : 0 < ‖c‖ ^ 2 := by nlinarith [sq_nonneg α]
  have hc : c ≠ 0 := by rintro rfl; simp at hN
  have hk : 0 < Real.sqrt (‖c‖ ^ 2 - α ^ 2) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨(α + Real.sqrt (‖c‖ ^ 2 - α ^ 2) * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ),
    (α - Real.sqrt (‖c‖ ^ 2 - α ^ 2) * Complex.I) * c / ((‖c‖ ^ 2 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · intro e
    have hNc : ((‖c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [div_left_inj' hNc, mul_left_inj' hc] at e
    have := congrArg Complex.im e
    simp at this
    linarith
  · rw [idealPts_eq h]; simp
  · rw [idealPts_eq h]; simp

/-- Through an ideal point `A` and a point `P` of the disc there passes an h-line: there are
`α, c` with `α² < ‖c‖²`, `P ∈ hline α c` and `A ∈ idealPts α c`. -/
theorem exists_hline_through {A P : ℂ} (hA : ‖A‖ = 1) (hP : ‖P‖ < 1) :
    ∃ (α : ℝ) (c : ℂ), α ^ 2 < ‖c‖ ^ 2 ∧ P ∈ hline α c ∧ A ∈ idealPts α c := by
  have hA2 : A.re ^ 2 + A.im ^ 2 = 1 := by rw [← sq_norm_eq, hA]; norm_num
  have hP2 : P.re ^ 2 + P.im ^ 2 < 1 := by rw [← sq_norm_eq]; nlinarith [norm_nonneg P]
  set qr : ℝ := A.re * P.re + A.im * P.im with hqr
  set qi : ℝ := A.re * P.im - A.im * P.re with hqi
  have hq : qr ^ 2 + qi ^ 2 = P.re ^ 2 + P.im ^ 2 := by
    rw [hqr, hqi]; linear_combination (P.re ^ 2 + P.im ^ 2) * hA2
  set k : ℝ := -((1 - qr) ^ 2 + qi ^ 2) / 2 with hk
  have hpos : 0 < (1 - qr) ^ 2 + qi ^ 2 := by
    by_contra hcon
    push Not at hcon
    have h1 : qr = 1 := by nlinarith [sq_nonneg (1 - qr), sq_nonneg qi]
    have h2 : qi = 0 := by nlinarith [sq_nonneg (1 - qr), sq_nonneg qi]
    rw [h1, h2] at hq
    linarith
  have hk0 : 0 < k ^ 2 := by
    have : k ≠ 0 := by rw [hk]; intro h; linarith
    positivity
  refine ⟨qi, ⟨qi * A.re + k * A.im, qi * A.im - k * A.re⟩, ?_, ⟨hP, ?_⟩, ⟨by simpa using hA, ?_⟩⟩
  · rw [sq_norm_eq]
    simp only
    nlinarith [hA2]
  · rw [re_conj_mul, sq_norm_eq]
    simp only
    have e1 : (qi * A.re + k * A.im) * P.re + (qi * A.im - k * A.re) * P.im = qi * qr - k * qi := by
      rw [hqr, hqi]; ring
    rw [e1, hk]
    linear_combination (-(qi * (P.re ^ 2 + P.im ^ 2))) * hA2 + 0 * hq
  · rw [re_conj_mul]
    simp only
    linear_combination qi * hA2

/-- If an h-line `m` through `P` has two distinct ideal points in common with `ℓ`, then it equals
`ℓ` and so `P ∈ ℓ`. -/
theorem mem_hline_of_two_common {α α' : ℝ} {c c' A B P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2)
    (h' : α' ^ 2 < ‖c'‖ ^ 2) (hAB : A ≠ B) (hA : A ∈ idealPts α c) (hB : B ∈ idealPts α c)
    (hA' : A ∈ idealPts α' c') (hB' : B ∈ idealPts α' c') (hP : P ∈ hline α' c') :
    P ∈ hline α c := by
  rw [hline_eq_of_idealPts h h' hAB hA hB hA' hB']
  exact hP

/-- Definition p. 103 and the claim that follows it: through a point `P` of the disc off the
h-line `ℓ = hline α c` there pass two different h-lines asymptotically parallel to `ℓ`, one through
each ideal point of `ℓ`.  The two lines are different (they have different sets of ideal points).
(That there are no further asymptotically parallel lines through `P` is not formalized.) -/
@[kb "petrunin2025" "Definition (asymptotically parallel), p. 103"]
theorem exists_two_asymParallel {α : ℝ} {c P : ℂ} (h : α ^ 2 < ‖c‖ ^ 2) (hP : ‖P‖ < 1)
    (hPl : P ∉ hline α c) :
    ∃ (α₁ : ℝ) (c₁ : ℂ) (α₂ : ℝ) (c₂ : ℂ), AsymParallel α c α₁ c₁ ∧ AsymParallel α c α₂ c₂ ∧
      P ∈ hline α₁ c₁ ∧ P ∈ hline α₂ c₂ ∧ idealPts α₁ c₁ ≠ idealPts α₂ c₂ := by
  obtain ⟨A, B, hAB, hA, hB⟩ := exists_two_idealPts h
  obtain ⟨α₁, c₁, h1, hP1, hA1⟩ := exists_hline_through hA.1 hP
  obtain ⟨α₂, c₂, h2, hP2, hB2⟩ := exists_hline_through hB.1 hP
  refine ⟨α₁, c₁, α₂, c₂, ⟨h, h1, ?_, A, hA, hA1⟩, ⟨h, h2, ?_, B, hB, hB2⟩, hP1, hP2, ?_⟩
  · intro e
    exact hPl (mem_hline_of_two_common h h1 hAB hA hB hA1 (by rw [← e]; exact hB) hP1)
  · intro e
    exact hPl (mem_hline_of_two_common h h2 hAB hA hB (by rw [← e]; exact hA) hB2 hP2)
  · intro e
    exact hPl (mem_hline_of_two_common h h1 hAB hA hB hA1 (by rw [e]; exact hB2) hP1)

end Parallels

/-! ### The angle of parallelism (Proposition 13.3, centred model) -/

/-- Definition p. 103 / Proposition 13.3 in the centred model.  For `0 < φ < π/2` let `ℓ` be the
h-line `hline (cos φ) 1` (the Euclidean circle with centre `1/cos φ` and radius `tan φ`), with ideal
points `e^{±iφ}`, and let `Q = (1 - sin φ)/cos φ` be the real point of `ℓ` closest to the centre
`P = 0` (the footpoint).  Then `Q ∈ ℓ`, the h-angle at `P` between the h-ray to the footpoint `Q` and
the h-rays to the two ideal points of `ℓ` equals `φ` (so `φ` is the angle of parallelism), and with
`h = PQ_h`, `cos φ = (e^{2h} - 1)/(e^{2h} + 1)` (wave 1's `angle_of_parallelism`).  That `PQ` is
perpendicular to `ℓ` and that `φ` is the smallest angle of a non-crossing ray are not formalized. -/
@[kb "petrunin2025" "Definition (angle of parallelism), p. 103"]
theorem angle_of_parallelism_hangle {φ : ℝ} (h0 : 0 < φ) (h1 : φ < π / 2) :
    let Q : ℂ := (((1 - Real.sin φ) / Real.cos φ : ℝ) : ℂ)
    let A : ℂ := Complex.mk (Real.cos φ) (Real.sin φ)
    Q ∈ hline (Real.cos φ) 1 ∧ A ∈ idealPts (Real.cos φ) 1 ∧ conj A ∈ idealPts (Real.cos φ) 1 ∧
    hangleIdeal 0 Q A = φ ∧ hangleIdeal 0 Q (conj A) = φ ∧
    Real.cos φ = (Real.exp (2 * hdist 0 Q) - 1) / (Real.exp (2 * hdist 0 Q) + 1) := by
  intro Q A
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hsc := Real.sin_sq_add_cos_sq φ
  have hw := angle_of_parallelism h0 h1
  have hQn : ‖Q‖ = (1 - Real.sin φ) / Real.cos φ := by
    have : Real.sin φ < 1 := by nlinarith
    simp only [Q, Complex.norm_real]
    exact Real.norm_of_nonneg (div_nonneg (by linarith) hc.le)
  have hQpos : 0 < (1 - Real.sin φ) / Real.cos φ := by
    have : Real.sin φ < 1 := by nlinarith
    exact div_pos (by linarith) hc
  have hAn : ‖A‖ = 1 := by
    have : ‖A‖ ^ 2 = 1 := by
      rw [sq_norm_eq]; simp only [A]; linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  have hAre : (conj 1 * A).re = Real.cos φ := by simp [A]
  have hAre' : (conj 1 * conj A).re = Real.cos φ := by simp [A]
  have hAarg : A = Complex.cos φ + Complex.sin φ * Complex.I := by
    apply Complex.ext <;> simp [A, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hQ0 : (Q : ℂ) ≠ 0 := by
    intro h; rw [h] at hQn; simp at hQn; linarith
  have hang : InnerProductGeometry.angle (Q : ℂ) A = φ := by
    rw [InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg (by intro h; rw [h] at hAn; simp at hAn) hQ0]
    have : A / Q = ((((1 - Real.sin φ) / Real.cos φ)⁻¹ : ℝ) : ℂ) * A := by
      simp only [Q]; push_cast; ring
    rw [this, Complex.arg_real_mul _ (inv_pos.mpr hQpos), hAarg,
      Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      abs_of_pos h0]
  refine ⟨⟨hw.1, ?_⟩, ⟨hAn, hAre⟩, ⟨by rw [Complex.norm_conj, hAn], hAre'⟩, ?_, ?_, hw.2.2.2.2.2⟩
  · have e : (conj 1 * Q).re = (1 - Real.sin φ) / Real.cos φ := by
      simp only [Q]; rw [map_one, one_mul, Complex.ofReal_re]
    rw [e, hQn, mul_comm]
    have hc' : Real.cos φ ≠ 0 := hc.ne'
    field_simp
    linear_combination hsc
  · unfold hangleIdeal
    simpa [mobius] using hang
  · unfold hangleIdeal
    have : InnerProductGeometry.angle (Q : ℂ) (conj A) = InnerProductGeometry.angle (Q : ℂ) A := by
      have hQc : conj Q = Q := Complex.conj_ofReal _
      have := (Complex.conjLIE.toLinearIsometry).angle_map (Q : ℂ) A
      simpa [hQc] using this
    simpa [mobius] using this.trans hang

end UndergradKB.Geometry
