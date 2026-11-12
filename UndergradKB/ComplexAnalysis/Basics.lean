import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval
import UndergradKB.Common.Attr

/-! # Connectedness, paths, holomorphic functions (rows CX-017, CX-018, CX-026)

* Connected sets in the sense of separated pieces, shown equivalent to Mathlib's `IsPreconnected`;
  regions; the interval example.
* Paths on a compact interval `[a, b]`, simple and closed paths, the unit circle and segments, and
  the comparison with Mathlib's `Path` (parametrised on `[0, 1]`).
* Holomorphy at a point (differentiable on a disc), its equivalence with analyticity,
  and the entire function `z ↦ z ^ 3`. -/

namespace UndergradKB.ComplexAnalysis

open Set Metric Filter Topology

/-! ## Separated sets and connectedness (CX-017) -/

/-- Two sets are separated when they lie in disjoint open sets. -/
def BookSeparated (X Y : Set ℂ) : Prop :=
  ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧ X ⊆ A ∧ Y ⊆ B

/-- Beck Definition 1.4.8 (CX-017): a set is connected if it is not the union of two nonempty
separated sets. -/
def BookConnected (G : Set ℂ) : Prop :=
  ¬ ∃ X Y : Set ℂ, X.Nonempty ∧ Y.Nonempty ∧ BookSeparated X Y ∧ X ∪ Y = G

/-- A region: an open connected set. -/
def IsRegion (G : Set ℂ) : Prop := IsOpen G ∧ IsConnected G

/-- Beck Definition 1.4.8 (CX-017): the book's notion of connectedness agrees with Mathlib's
`IsPreconnected`. -/
@[kb "beck2025" "Definition 1.4.8, p. 23"]
theorem bookConnected_iff_isPreconnected (G : Set ℂ) : BookConnected G ↔ IsPreconnected G := by
  constructor
  · intro hB u v hu hv hsub hxu hyv
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hB
    refine ⟨G ∩ u, G ∩ v, hxu, hyv, ?_, ?_⟩
    · have h1 : Disjoint (closure (G ∩ u)) (G ∩ v) := by
        rw [Set.disjoint_left]
        intro x hx hxv
        obtain ⟨y, hyv', hyu⟩ := mem_closure_iff.mp hx v hv hxv.2
        have : y ∈ G ∩ (u ∩ v) := ⟨hyu.1, hyu.2, hyv'⟩
        rw [hne] at this; exact this
      have h2 : Disjoint (G ∩ u) (closure (G ∩ v)) := by
        rw [Set.disjoint_left]
        intro x hx hxv
        obtain ⟨y, hyu', hyv⟩ := mem_closure_iff.mp hxv u hu hx.2
        have : y ∈ G ∩ (u ∩ v) := ⟨hyv.1, hyu', hyv.2⟩
        rw [hne] at this; exact this
      have := separatedNhds_iff_disjoint.mpr (completely_normal h1 h2)
      obtain ⟨A, B, hA, hB, hXA, hYB, hAB⟩ := this
      exact ⟨A, B, hA, hB, hAB, hXA, hYB⟩
    · rw [← Set.inter_union_distrib_left]
      exact Set.inter_eq_left.mpr hsub
  · rintro hP ⟨X, Y, ⟨x, hx⟩, ⟨y, hy⟩, ⟨A, B, hA, hB, hAB, hXA, hYB⟩, hU⟩
    have hsub : G ⊆ A ∪ B := by
      intro p hp
      rw [← hU] at hp
      rcases hp with hp | hp
      · exact Or.inl (hXA hp)
      · exact Or.inr (hYB hp)
    have hxG : x ∈ G := by rw [← hU]; exact Or.inl hx
    have hyG : y ∈ G := by rw [← hU]; exact Or.inr hy
    obtain ⟨p, _, hpA, hpB⟩ := hP A B hA hB hsub ⟨x, hxG, hXA hx⟩ ⟨y, hyG, hYB hy⟩
    exact Set.disjoint_left.mp hAB hpA hpB

/-- Connected in Mathlib's sense is the book's connectedness plus nonemptiness. -/
theorem isConnected_iff_bookConnected (G : Set ℂ) :
    IsConnected G ↔ G.Nonempty ∧ BookConnected G := by
  rw [bookConnected_iff_isPreconnected]
  exact ⟨fun h => ⟨h.nonempty, h.isPreconnected⟩, fun h => ⟨h.1, h.2⟩⟩

/-- The two intervals `[0, 1)` and `(1, 2]` on the real axis. -/
def intervalLeft : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re ∧ z.re < 1}
/-- See `intervalLeft`. -/
def intervalRight : Set ℂ := {z | z.im = 0 ∧ 1 < z.re ∧ z.re ≤ 2}

/-- Beck Example 1.4.9 (CX-017): `[0, 1)` and `(1, 2]` are separated. -/
@[kb "beck2025" "Example 1.4.9, p. 23"]
theorem intervals_separated : BookSeparated intervalLeft intervalRight := by
  refine ⟨{z | z.re < 1}, {z | 1 < z.re}, isOpen_lt Complex.continuous_re continuous_const,
    isOpen_lt continuous_const Complex.continuous_re, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]; intro z h1 h2; simp only [Set.mem_ofPred_eq] at h1 h2; linarith
  · intro z hz; exact hz.2.2
  · intro z hz; exact hz.2.1

/-- Beck Example 1.4.9 (CX-017): hence `[0, 1) ∪ (1, 2]` is not connected. -/
@[kb "beck2025" "Example 1.4.9, p. 23"]
theorem interval_union_not_connected : ¬ BookConnected (intervalLeft ∪ intervalRight) := by
  intro h
  apply h
  refine ⟨intervalLeft, intervalRight, ⟨0, by simp [intervalLeft]⟩, ⟨2, by simp [intervalRight]⟩,
    intervals_separated, rfl⟩

/-! ## Paths (CX-018) -/

/-- Beck Definition 1.4.11 (CX-018): a path is a continuous map on a compact interval `[a, b]`. -/
@[kb "beck2025" "Definition 1.4.11, p. 23"]
def IsPath (a b : ℝ) (γ : ℝ → ℂ) : Prop := a ≤ b ∧ ContinuousOn γ (Icc a b)

/-- Beck Definition 1.4.14 (CX-018): a path is simple if it is injective, except that the two
endpoints may coincide. -/
@[kb "beck2025" "Definition 1.4.14, p. 25"]
def IsSimplePath (a b : ℝ) (γ : ℝ → ℂ) : Prop :=
  IsPath a b γ ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, γ s = γ t →
    s = t ∨ (s = a ∧ t = b) ∨ (s = b ∧ t = a)

/-- Beck Definition 1.4.14 (CX-018): a path is closed if its endpoints agree. -/
@[kb "beck2025" "Definition 1.4.14, p. 25"]
def IsClosedPath (a b : ℝ) (γ : ℝ → ℂ) : Prop := IsPath a b γ ∧ γ a = γ b

/-- Beck Example 1.4.15 (CX-018): the unit circle `t ↦ e^{it}`, `0 ≤ t ≤ 2π`, is a simple
closed path. -/
@[kb "beck2025" "Example 1.4.15, p. 25"]
theorem unitCircle_simple_closed :
    IsSimplePath 0 (2 * Real.pi) (fun t : ℝ => Complex.exp (t * Complex.I)) ∧
    IsClosedPath 0 (2 * Real.pi) (fun t : ℝ => Complex.exp (t * Complex.I)) := by
  have hpi := Real.pi_pos
  have hpath : IsPath 0 (2 * Real.pi) (fun t : ℝ => Complex.exp (t * Complex.I)) :=
    ⟨by positivity, (by fun_prop : Continuous fun t : ℝ => Complex.exp (t * Complex.I)).continuousOn⟩
  refine ⟨⟨hpath, ?_⟩, hpath, ?_⟩
  · intro s hs t ht hst
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hst
    have him := congrArg Complex.im hn
    simp at him
    -- him : s = t + n * (2π)
    have hs0 := hs.1; have hs1 := hs.2; have ht0 := ht.1; have ht1 := ht.2
    have hn1 : (n : ℝ) ≤ 1 := by
      by_contra h
      have : (2 : ℝ) ≤ n := by
        have : (1 : ℤ) < n := by exact_mod_cast not_le.mp h
        exact_mod_cast this
      nlinarith
    have hn2 : (-1 : ℝ) ≤ n := by
      by_contra h
      have : (n : ℝ) ≤ -2 := by
        have : n < -1 := by exact_mod_cast not_le.mp h
        have : n ≤ -2 := by omega
        exact_mod_cast this
      nlinarith
    have hn1' : n ≤ 1 := by exact_mod_cast hn1
    have hn2' : -1 ≤ n := by exact_mod_cast hn2
    interval_cases n
    · right; left; constructor <;> push_cast at him <;> linarith
    · left; push_cast at him; linarith
    · right; right; constructor <;> push_cast at him <;> linarith
  · show Complex.exp ((0 : ℝ) * Complex.I) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I)
    push_cast
    rw [zero_mul, Complex.exp_zero, Complex.exp_two_pi_mul_I]

/-- Beck Example 1.4.12 (CX-018): a segment `t ↦ p + t (q - p)`, `0 ≤ t ≤ 1`, with `p ≠ q` is a
simple path. -/
@[kb "beck2025" "Example 1.4.12, p. 24"]
theorem segment_simple {p q : ℂ} (hpq : p ≠ q) :
    IsSimplePath 0 1 (fun t : ℝ => p + t * (q - p)) := by
  refine ⟨⟨zero_le_one, (by fun_prop : Continuous fun t : ℝ => p + t * (q - p)).continuousOn⟩, ?_⟩
  intro s _ t _ hst
  left
  have hne : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have : ((s : ℂ)) * (q - p) = (t : ℂ) * (q - p) := by simpa using hst
  have := mul_right_cancel₀ hne this
  exact_mod_cast this

/-- The Mathlib `Path` obtained from a path on `[a, b]` (`a < b`) by affine reparametrisation to
`[0, 1]`. -/
noncomputable def IsPath.toPath {a b : ℝ} {γ : ℝ → ℂ} (h : IsPath a b γ) (hab : a < b) :
    Path (γ a) (γ b) where
  toFun t := γ (a + t * (b - a))
  continuous_toFun := by
    refine h.2.comp_continuous (by fun_prop) (fun t => ?_)
    have h0 := t.2.1; have h1 := t.2.2
    constructor <;> nlinarith [sub_pos.mpr hab]
  source' := by simp
  target' := by simp

/-- Beck Definition 1.4.11 (CX-018): the reparametrised Mathlib `Path` has the same image as the
original path. -/
@[kb "beck2025" "Definition 1.4.11, p. 23"]
theorem IsPath.range_toPath {a b : ℝ} {γ : ℝ → ℂ} (h : IsPath a b γ) (hab : a < b) :
    Set.range (h.toPath hab) = γ '' Icc a b := by
  ext w
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨a + t * (b - a), ?_, rfl⟩
    have h0 := t.2.1; have h1 := t.2.2
    constructor <;> nlinarith [sub_pos.mpr hab]
  · rintro ⟨s, hs, rfl⟩
    have hba : 0 < b - a := sub_pos.mpr hab
    refine ⟨⟨(s - a) / (b - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [hs.1]) hba.le
    · rw [div_le_one hba]; linarith [hs.2]
    · show γ (a + (s - a) / (b - a) * (b - a)) = γ s
      rw [div_mul_cancel₀ _ hba.ne']; congr 1; ring

/-! ## Holomorphic functions (CX-026) -/

/-- Beck Definition 2.2.1 (CX-026): `f` is holomorphic at `z₀` if it is differentiable on an open
disc around `z₀`. -/
@[kb "beck2025" "Definition 2.2.1, p. 36"]
def HolomorphicAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ r > 0, DifferentiableOn ℂ f (ball z₀ r)

/-- Entire: holomorphic at every point. -/
def IsEntire (f : ℂ → ℂ) : Prop := ∀ z, HolomorphicAt f z

/-- Beck Definition 2.2.1 (CX-026): holomorphic at a point is the same as complex analytic there. -/
@[kb "beck2025" "Definition 2.2.1, p. 36"]
theorem holomorphicAt_iff_analyticAt (f : ℂ → ℂ) (z₀ : ℂ) :
    HolomorphicAt f z₀ ↔ AnalyticAt ℂ f z₀ := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt, Metric.eventually_nhds_iff_ball]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun y hy => (h.differentiableAt (isOpen_ball.mem_nhds hy))⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun y hy => (h y hy).differentiableWithinAt⟩

/-- Beck Example 2.2.2 (CX-026): `z ↦ z ^ 3` is entire. -/
@[kb "beck2025" "Example 2.2.2, p. 36"]
theorem cube_isEntire : IsEntire (fun z : ℂ => z ^ 3) := fun _ =>
  ⟨1, one_pos, (differentiable_id.pow 3).differentiableOn⟩

/-- Beck Example 2.2.2 (CX-026): the derivative of `z ↦ z ^ 3` is `3 z ^ 2`. -/
@[kb "beck2025" "Example 2.2.2, p. 36"]
theorem cube_hasDerivAt (z : ℂ) : HasDerivAt (fun z : ℂ => z ^ 3) (3 * z ^ 2) z := by
  simpa using hasDerivAt_pow 3 z

end UndergradKB.ComplexAnalysis
