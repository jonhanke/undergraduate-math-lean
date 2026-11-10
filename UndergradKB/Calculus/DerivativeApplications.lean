import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import UndergradKB.Common.Attr

namespace UndergradKB.Calculus

open Set Filter Topology

/-! ### Critical points and absolute extrema (CA-142, CA-143) -/

/-- OpenStax Calculus 1:§4.3 Definition (critical point) (CA-142). `c` is a critical point of `f` on the
domain `D` when `c` is an interior point of `D` and either `f` is not differentiable at `c` or
`f'(c) = 0`. -/
@[kb "openstaxcalculus2016" "1:§4.3 Definition (critical point), p. 329"]
def IsCriticalPoint1 (f : ℝ → ℝ) (D : Set ℝ) (c : ℝ) : Prop :=
  c ∈ interior D ∧ (¬ DifferentiableAt ℝ f c ∨ deriv f c = 0)

/-- OpenStax Calculus 1:Theorem 4.3 (CA-143). If `f` attains its maximum over `[a,b]` at `x`, then `x` is an
endpoint or a critical point of `f` in `(a,b)`. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.3, p. 332"]
theorem isMaxOn_Icc_endpoint_or_critical {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Icc a b)
    (h : IsMaxOn f (Icc a b) x) : x = a ∨ x = b ∨ IsCriticalPoint1 f (Icc a b) x := by
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr (Or.inl hxb)
  refine Or.inr (Or.inr ?_)
  have hI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  refine ⟨by rw [interior_Icc]; exact hI, ?_⟩
  by_cases hd : DifferentiableAt ℝ f x
  · exact Or.inr (h.isLocalMax (Icc_mem_nhds hI.1 hI.2)).deriv_eq_zero
  · exact Or.inl hd

/-- OpenStax Calculus 1:Theorem 4.3 (CA-143), minimum version. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.3, p. 332"]
theorem isMinOn_Icc_endpoint_or_critical {f : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Icc a b)
    (h : IsMinOn f (Icc a b) x) : x = a ∨ x = b ∨ IsCriticalPoint1 f (Icc a b) x := by
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr (Or.inl hxb)
  refine Or.inr (Or.inr ?_)
  have hI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  refine ⟨by rw [interior_Icc]; exact hI, ?_⟩
  by_cases hd : DifferentiableAt ℝ f x
  · exact Or.inr (h.isLocalMin (Icc_mem_nhds hI.1 hI.2)).deriv_eq_zero
  · exact Or.inl hd

/-- OpenStax Calculus 1:Theorem 4.3 / §4.3 strategy (CA-143). A continuous function on `[a,b]` attains an
absolute maximum and an absolute minimum, each at an endpoint or at a critical point. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.3, p. 332"]
theorem exists_extrema_endpoint_or_critical {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    (∃ x ∈ Icc a b, IsMaxOn f (Icc a b) x ∧ (x = a ∨ x = b ∨ IsCriticalPoint1 f (Icc a b) x)) ∧
    (∃ x ∈ Icc a b, IsMinOn f (Icc a b) x ∧ (x = a ∨ x = b ∨ IsCriticalPoint1 f (Icc a b) x)) := by
  have hc : IsCompact (Icc a b) := isCompact_Icc
  have hne : (Icc a b).Nonempty := nonempty_Icc.mpr hab
  obtain ⟨x, hx, hxm⟩ := hc.exists_isMaxOn hne hf
  obtain ⟨y, hy, hym⟩ := hc.exists_isMinOn hne hf
  exact ⟨⟨x, hx, hxm, isMaxOn_Icc_endpoint_or_critical hx hxm⟩,
    ⟨y, hy, hym, isMinOn_Icc_endpoint_or_critical hy hym⟩⟩

/-! ### First derivative test (CA-149) -/

/-- OpenStax Calculus 1:Theorem 4.9 (CA-149), `+` to `-`: if `f` is continuous at `c`, differentiable on
`(a,b)` except possibly at `c`, with `f' > 0` on `(a,c)` and `f' < 0` on `(c,b)`, then `c` is a local
maximum. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.9, p. 349"]
theorem first_derivative_test_max {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c) (hd : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x)
    (hpos : ∀ x ∈ Ioo a c, 0 < deriv f x) (hneg : ∀ x ∈ Ioo c b, deriv f x < 0) :
    IsLocalMax f c := by
  refine isLocalMax_of_deriv hcont ?_ ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hac hcb), self_mem_nhdsWithin]
      with x hx hne using hd x hx hne
  · filter_upwards [Ioo_mem_nhdsLT hac] with x hx using (hpos x hx).le
  · filter_upwards [Ioo_mem_nhdsGT hcb] with x hx using (hneg x hx).le

/-- OpenStax Calculus 1:Theorem 4.9 (CA-149), `-` to `+`: a local minimum. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.9, p. 349"]
theorem first_derivative_test_min {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c) (hd : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x)
    (hneg : ∀ x ∈ Ioo a c, deriv f x < 0) (hpos : ∀ x ∈ Ioo c b, 0 < deriv f x) :
    IsLocalMin f c := by
  refine isLocalMin_of_deriv hcont ?_ ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hac hcb), self_mem_nhdsWithin]
      with x hx hne using hd x hx hne
  · filter_upwards [Ioo_mem_nhdsLT hac] with x hx using (hneg x hx).le
  · filter_upwards [Ioo_mem_nhdsGT hcb] with x hx using (hpos x hx).le

/-- OpenStax Calculus 1:Theorem 4.9 (CA-149), no sign change (positive): if `f' > 0` on both sides of `c`
(`f` continuous at `c`), then `c` is not a local extremum. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.9, p. 349"]
theorem first_derivative_test_no_change_pos {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c) (hd : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x)
    (hl : ∀ x ∈ Ioo a c, 0 < deriv f x) (hr : ∀ x ∈ Ioo c b, 0 < deriv f x) :
    ¬ IsLocalExtr f c := by
  have hcontOn : ∀ x ∈ Ioo a b, ContinuousAt f x := fun x hx => by
    by_cases hxc : x = c
    · rw [hxc]; exact hcont
    · exact (hd x hx hxc).continuousAt
  have h1 : StrictMonoOn f (Ioc a c) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc a c) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hcontOn x ⟨hx.1, lt_of_le_of_lt hx.2 hcb⟩).continuousWithinAt
    · rw [interior_Ioc] at hx; exact hl x hx
  have h2 : StrictMonoOn f (Ico c b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ico c b) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hcontOn x ⟨lt_of_lt_of_le hac hx.1, hx.2⟩).continuousWithinAt
    · rw [interior_Ico] at hx; exact hr x hx
  rintro (hmin | hmax)
  · have := (hmin.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hac)
    obtain ⟨x, hx1, hx2⟩ := (this : ∀ᶠ x in 𝓝[<] c, _).exists
    exact absurd (h1 ⟨hx2.1, hx2.2.le⟩ ⟨hac, le_rfl⟩ hx2.2) (not_lt.mpr hx1)
  · have := (hmax.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hcb)
    obtain ⟨x, hx1, hx2⟩ := (this : ∀ᶠ x in 𝓝[>] c, _).exists
    exact absurd (h2 ⟨le_rfl, hcb⟩ ⟨hx2.1.le, hx2.2⟩ hx2.1) (not_lt.mpr hx1)

/-- OpenStax Calculus 1:Theorem 4.9 (CA-149), no sign change (negative): if `f' < 0` on both sides of `c`
(`f` continuous at `c`), then `c` is not a local extremum. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.9, p. 349"]
theorem first_derivative_test_no_change_neg {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c) (hd : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x)
    (hl : ∀ x ∈ Ioo a c, deriv f x < 0) (hr : ∀ x ∈ Ioo c b, deriv f x < 0) :
    ¬ IsLocalExtr f c := by
  have hcontOn : ∀ x ∈ Ioo a b, ContinuousAt f x := fun x hx => by
    by_cases hxc : x = c
    · rw [hxc]; exact hcont
    · exact (hd x hx hxc).continuousAt
  have h1 : StrictAntiOn f (Ioc a c) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc a c) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hcontOn x ⟨hx.1, lt_of_le_of_lt hx.2 hcb⟩).continuousWithinAt
    · rw [interior_Ioc] at hx; exact hl x hx
  have h2 : StrictAntiOn f (Ico c b) := by
    refine strictAntiOn_of_deriv_neg (convex_Ico c b) (fun x hx => ?_) (fun x hx => ?_)
    · exact (hcontOn x ⟨lt_of_lt_of_le hac hx.1, hx.2⟩).continuousWithinAt
    · rw [interior_Ico] at hx; exact hr x hx
  rintro (hmin | hmax)
  · have := (hmin.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hcb)
    obtain ⟨x, hx1, hx2⟩ := (this : ∀ᶠ x in 𝓝[>] c, _).exists
    exact absurd (h2 ⟨le_rfl, hcb⟩ ⟨hx2.1.le, hx2.2⟩ hx2.1) (not_lt.mpr hx1)
  · have := (hmax.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hac)
    obtain ⟨x, hx1, hx2⟩ := (this : ∀ᶠ x in 𝓝[<] c, _).exists
    exact absurd (h1 ⟨hx2.1, hx2.2.le⟩ ⟨hac, le_rfl⟩ hx2.2) (not_lt.mpr hx1)

/-! ### Concavity and inflection points (CA-150, CA-152) -/

/-- OpenStax Calculus 1:§4.5 Definition (concave up) (CA-150). `f` is concave up on `I` when it is
differentiable there and its derivative is increasing on `I`. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (concave up, concave down), p. 352"]
def ConcaveUpOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  DifferentiableOn ℝ f I ∧ StrictMonoOn (deriv f) I

/-- OpenStax Calculus 1:§4.5 Definition (concave down) (CA-150). `f` is differentiable on `I` with
decreasing derivative. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (concave up, concave down), p. 352"]
def ConcaveDownOn (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  DifferentiableOn ℝ f I ∧ StrictAntiOn (deriv f) I

/-- OpenStax Calculus 1:§4.5 (CA-150): on an open interval, concave up (book definition) implies strictly
convex in Mathlib's sense. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (concave up, concave down), p. 352"]
theorem ConcaveUpOn.strictConvexOn {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    (h : ConcaveUpOn f I) : StrictConvexOn ℝ I f :=
  StrictMonoOn.strictConvexOn_of_deriv hc h.1.continuousOn (by rw [hI.interior_eq]; exact h.2)

/-- OpenStax Calculus 1:§4.5 (CA-150): on an open interval, concave down implies strictly concave in
Mathlib's sense. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (concave up, concave down), p. 352"]
theorem ConcaveDownOn.strictConcaveOn {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    (h : ConcaveDownOn f I) : StrictConcaveOn ℝ I f :=
  StrictAntiOn.strictConcaveOn_of_deriv hc h.1.continuousOn (by rw [hI.interior_eq]; exact h.2)

/-- OpenStax Calculus 1:§4.5 (CA-150): conversely, a convex function differentiable on `I` has increasing
(non-strictly) derivative. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (concave up, concave down), p. 352"]
theorem ConvexOn.monotoneOn_deriv_of_differentiable {f : ℝ → ℝ} {I : Set ℝ} (hc : ConvexOn ℝ I f)
    (hd : ∀ x ∈ I, DifferentiableAt ℝ f x) : MonotoneOn (deriv f) I :=
  hc.monotoneOn_deriv hd

/-- OpenStax Calculus 1:§4.5 (CA-151): second-derivative criterion, `f'' > 0` on an open interval gives
concave up. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.10, p. 353"]
theorem concaveUpOn_of_deriv2_pos {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    (hf : ∀ x ∈ I, DifferentiableAt ℝ f x) (hf' : ∀ x ∈ I, DifferentiableAt ℝ (deriv f) x)
    (h : ∀ x ∈ I, 0 < deriv (deriv f) x) : ConcaveUpOn f I :=
  ⟨fun x hx => (hf x hx).differentiableWithinAt,
    strictMonoOn_of_deriv_pos hc (fun x hx => (hf' x hx).continuousAt.continuousWithinAt)
      (by rw [hI.interior_eq]; exact h)⟩

/-- OpenStax Calculus 1:§4.5 (CA-151): `f'' < 0` on an open interval gives concave down. -/
@[kb "openstaxcalculus2016" "1:Theorem 4.10, p. 353"]
theorem concaveDownOn_of_deriv2_neg {f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (hc : Convex ℝ I)
    (hf : ∀ x ∈ I, DifferentiableAt ℝ f x) (hf' : ∀ x ∈ I, DifferentiableAt ℝ (deriv f) x)
    (h : ∀ x ∈ I, deriv (deriv f) x < 0) : ConcaveDownOn f I :=
  ⟨fun x hx => (hf x hx).differentiableWithinAt,
    strictAntiOn_of_deriv_neg hc (fun x hx => (hf' x hx).continuousAt.continuousWithinAt)
      (by rw [hI.interior_eq]; exact h)⟩

/-- OpenStax Calculus 1:§4.5 Definition (inflection point) (CA-152). `f` is continuous at `c` and its
concavity changes at `c`: concave up on `(a,c)` and concave down on `(c,b)`, or the reverse. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (inflection point), p. 353"]
def IsInflectionPoint (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ContinuousAt f c ∧ ∃ a b, a < c ∧ c < b ∧
    ((ConcaveUpOn f (Ioo a c) ∧ ConcaveDownOn f (Ioo c b)) ∨
     (ConcaveDownOn f (Ioo a c) ∧ ConcaveUpOn f (Ioo c b)))

/-- OpenStax Calculus 1:§4.5 (CA-152): if `f` is continuous at `c`, twice differentiable on `(a,b)` away
from `c`, and `f''` is positive on `(a,c)` and negative on `(c,b)`, then `c` is an inflection point. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (inflection point), p. 353"]
theorem isInflectionPoint_of_deriv2_sign_change {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c)
    (hf : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ (deriv f) x)
    (hpos : ∀ x ∈ Ioo a c, 0 < deriv (deriv f) x) (hneg : ∀ x ∈ Ioo c b, deriv (deriv f) x < 0) :
    IsInflectionPoint f c := by
  refine ⟨hcont, a, b, hac, hcb, Or.inl ⟨?_, ?_⟩⟩
  · exact concaveUpOn_of_deriv2_pos isOpen_Ioo (convex_Ioo a c)
      (fun x hx => hf x ⟨hx.1, hx.2.trans hcb⟩ hx.2.ne)
      (fun x hx => hf' x ⟨hx.1, hx.2.trans hcb⟩ hx.2.ne) hpos
  · exact concaveDownOn_of_deriv2_neg isOpen_Ioo (convex_Ioo c b)
      (fun x hx => hf x ⟨hac.trans hx.1, hx.2⟩ hx.1.ne')
      (fun x hx => hf' x ⟨hac.trans hx.1, hx.2⟩ hx.1.ne') hneg

/-- OpenStax Calculus 1:§4.5 (CA-152), the other orientation: `f''` negative then positive. -/
@[kb "openstaxcalculus2016" "1:§4.5 Definition (inflection point), p. 353"]
theorem isInflectionPoint_of_deriv2_sign_change' {f : ℝ → ℝ} {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hcont : ContinuousAt f c)
    (hf : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ Ioo a b, x ≠ c → DifferentiableAt ℝ (deriv f) x)
    (hneg : ∀ x ∈ Ioo a c, deriv (deriv f) x < 0) (hpos : ∀ x ∈ Ioo c b, 0 < deriv (deriv f) x) :
    IsInflectionPoint f c := by
  refine ⟨hcont, a, b, hac, hcb, Or.inr ⟨?_, ?_⟩⟩
  · exact concaveDownOn_of_deriv2_neg isOpen_Ioo (convex_Ioo a c)
      (fun x hx => hf x ⟨hx.1, hx.2.trans hcb⟩ hx.2.ne)
      (fun x hx => hf' x ⟨hx.1, hx.2.trans hcb⟩ hx.2.ne) hneg
  · exact concaveUpOn_of_deriv2_pos isOpen_Ioo (convex_Ioo c b)
      (fun x hx => hf x ⟨hac.trans hx.1, hx.2⟩ hx.1.ne')
      (fun x hx => hf' x ⟨hac.trans hx.1, hx.2⟩ hx.1.ne') hpos

end UndergradKB.Calculus
