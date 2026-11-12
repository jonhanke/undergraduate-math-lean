import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Archimedean
import UndergradKB.Common.Attr

/-!
# Iterates, orbits, fixed and periodic points, attracting and repelling fixed points

Morris, *Topology Without Tears* (2024), Appendix 3, Sections A3.1 to A3.5 (`morris2024`).
Fixed points, periodic points and prime periods are Mathlib's `Function.IsFixedPt`,
`Function.IsPeriodicPt` and `Function.minimalPeriod`; the book's notions of orbit, eventually
fixed / periodic point, attracting / repelling / neutral fixed point and `m`-cycle are bridging
definitions (they are missing from Mathlib).
-/

open Function Set Filter
open scoped Topology

namespace UndergradKB.Topology

/-! ### Orbits -/

section Orbits

variable {α : Type*}

/-- The forward orbit `{f^n x | n ≥ 0}` of a seed `x` under a self-map `f`. -/
def forwardOrbit (f : α → α) (x : α) : Set α := Set.range fun n : ℕ => f^[n] x

/-- Morris, Topology Without Tears, Definition A3.1.2 (TP-433). A point lies on the orbit of the seed
`x` exactly when it is some iterate `f^n x`. -/
@[kb "morris2024" "Definition A3.1.2, p. 438"]
theorem mem_forwardOrbit_iff {f : α → α} {x y : α} :
    y ∈ forwardOrbit f x ↔ ∃ n : ℕ, f^[n] x = y := Iff.rfl

/-- Morris, Topology Without Tears, Definition A3.1.2 (TP-433). The seed lies on its own orbit. -/
@[kb "morris2024" "Definition A3.1.2, p. 438"]
theorem self_mem_forwardOrbit (f : α → α) (x : α) : x ∈ forwardOrbit f x := ⟨0, rfl⟩

/-- Morris, Topology Without Tears, Definition A3.1.2 (TP-433). The orbit of `x` is `x` together with
the orbit of `f x`. -/
@[kb "morris2024" "Definition A3.1.2, p. 438"]
theorem forwardOrbit_eq_insert (f : α → α) (x : α) :
    forwardOrbit f x = insert x (forwardOrbit f (f x)) := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, by simp [iterate_succ_apply]⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨n + 1, by simp [iterate_succ_apply]⟩

/-- Morris, Topology Without Tears, Definition A3.1.2 (TP-433). The orbit is carried into itself by `f`. -/
@[kb "morris2024" "Definition A3.1.2, p. 438"]
theorem mapsTo_forwardOrbit (f : α → α) (x : α) : MapsTo f (forwardOrbit f x) (forwardOrbit f x) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n + 1, by simp [iterate_succ_apply']⟩

end Orbits

/-! ### Eventually fixed and eventually periodic points -/

section Eventually

variable {α : Type*}

/-- A point is *eventually fixed* if it is not fixed but some point of its orbit is fixed. -/
def IsEventuallyFixed (f : α → α) (x : α) : Prop :=
  ¬ IsFixedPt f x ∧ ∃ y ∈ forwardOrbit f x, IsFixedPt f y

/-- Morris, Topology Without Tears, Definition A3.2.1 (TP-435). Eventually fixed means: not fixed, and
some iterate is fixed. -/
@[kb "morris2024" "Definition A3.2.1, p. 441"]
theorem isEventuallyFixed_iff {f : α → α} {x : α} :
    IsEventuallyFixed f x ↔ ¬ IsFixedPt f x ∧ ∃ n : ℕ, IsFixedPt f (f^[n] x) := by
  constructor
  · rintro ⟨h, _, ⟨n, rfl⟩, hy⟩
    exact ⟨h, n, hy⟩
  · rintro ⟨h, n, hn⟩
    exact ⟨h, _, ⟨n, rfl⟩, hn⟩

/-- Morris, Topology Without Tears, Definition A3.2.1 (TP-435). Once an eventually fixed orbit has
reached its fixed point, it stays there. -/
@[kb "morris2024" "Definition A3.2.1, p. 441"]
theorem IsEventuallyFixed.exists_forall_iterate_eq {f : α → α} {x : α} (h : IsEventuallyFixed f x) :
    ∃ N : ℕ, ∀ m ≥ N, f^[m] x = f^[N] x := by
  obtain ⟨-, N, hN⟩ := isEventuallyFixed_iff.mp h
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm, iterate_add_apply]
  exact hN.iterate k

/-- A point is *eventually periodic* if it is not periodic but some point of its orbit is periodic. -/
def IsEventuallyPeriodic (f : α → α) (x : α) : Prop :=
  x ∉ periodicPts f ∧ ∃ y ∈ forwardOrbit f x, y ∈ periodicPts f

/-- Morris, Topology Without Tears, Definition A3.2.3 (TP-437). Eventually periodic means: not
periodic, and some iterate is periodic. -/
@[kb "morris2024" "Definition A3.2.3, p. 441"]
theorem isEventuallyPeriodic_iff {f : α → α} {x : α} :
    IsEventuallyPeriodic f x ↔ x ∉ periodicPts f ∧ ∃ n : ℕ, f^[n] x ∈ periodicPts f := by
  constructor
  · rintro ⟨h, _, ⟨n, rfl⟩, hy⟩
    exact ⟨h, n, hy⟩
  · rintro ⟨h, n, hn⟩
    exact ⟨h, _, ⟨n, rfl⟩, hn⟩

/-- Morris, Topology Without Tears, Definition A3.2.3 (TP-437). Every eventually fixed point is
eventually periodic. -/
@[kb "morris2024" "Definition A3.2.3, p. 441"]
theorem IsEventuallyFixed.isEventuallyPeriodic {f : α → α} {x : α} (h : IsEventuallyFixed f x) :
    IsEventuallyPeriodic f x := by
  obtain ⟨hx, n, hn⟩ := isEventuallyFixed_iff.mp h
  refine isEventuallyPeriodic_iff.mpr ⟨?_, n, mk_mem_periodicPts Nat.one_pos hn⟩
  intro hper
  obtain ⟨N, hN, hNx⟩ := mem_periodicPts.mp hper
  apply hx
  have h1 : f^[N * n] x = x := (hNx.mul_const n).eq
  have h2 : f^[N * n] x = f^[n] x := by
    obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [hk, add_mul, one_mul, iterate_add_apply]
    exact (hn.iterate (k * n)).eq
  have h3 : x = f^[n] x := h1.symm.trans h2
  calc f x = f (f^[n] x) := by rw [← h3]
    _ = f^[n] x := hn
    _ = x := h3.symm

end Eventually

/-! ### Attracting, repelling and neutral fixed points -/

section Attracting

/-- A fixed point `a` of `f : ℝ → ℝ` is *attracting* if some open interval around `a` consists of
points whose iterates converge to `a`. -/
def IsAttractingFixedPt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  IsFixedPt f a ∧ ∃ l u : ℝ, l < a ∧ a < u ∧ ∀ x ∈ Ioo l u, Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 a)

/-- A fixed point `a` of `f : ℝ → ℝ` is *repelling* if there is an open interval `I` around `a` such
that every point `x ≠ a` of `I` has some iterate outside `I`. -/
def IsRepellingFixedPt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  IsFixedPt f a ∧ ∃ l u : ℝ, l < a ∧ a < u ∧
    ∀ x ∈ Ioo l u, x ≠ a → ∃ n : ℕ, f^[n] x ∉ Ioo l u

/-- A fixed point is *neutral* if it is neither attracting nor repelling. -/
def IsNeutralFixedPt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  IsFixedPt f a ∧ ¬ IsAttractingFixedPt f a ∧ ¬ IsRepellingFixedPt f a

/-- Morris, Topology Without Tears, Definition A3.3.2 (TP-438). Attracting means: some ball around the
fixed point is attracted to it. -/
@[kb "morris2024" "Definition A3.3.2, p. 443"]
theorem isAttractingFixedPt_iff_ball {f : ℝ → ℝ} {a : ℝ} :
    IsAttractingFixedPt f a ↔ IsFixedPt f a ∧ ∃ δ > 0, ∀ x ∈ Metric.ball a δ,
      Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 a) := by
  constructor
  · rintro ⟨ha, l, u, hl, hu, h⟩
    refine ⟨ha, min (a - l) (u - a), lt_min (by linarith) (by linarith), fun x hx => h x ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    have h1 := min_le_left (a - l) (u - a)
    have h2 := min_le_right (a - l) (u - a)
    constructor <;> linarith [hx.1, hx.2]
  · rintro ⟨ha, δ, hδ, h⟩
    refine ⟨ha, a - δ, a + δ, by linarith, by linarith, fun x hx => h x ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]

/-- Morris, Topology Without Tears, Definition A3.3.3 (TP-439). Repelling means: some ball around the
fixed point has the property that each of its points other than the centre has an iterate outside it. -/
@[kb "morris2024" "Definition A3.3.3, p. 443"]
theorem isRepellingFixedPt_iff_ball {f : ℝ → ℝ} {a : ℝ} :
    IsRepellingFixedPt f a ↔ IsFixedPt f a ∧ ∃ δ > 0, ∀ x ∈ Metric.ball a δ, x ≠ a →
      ∃ n : ℕ, f^[n] x ∉ Metric.ball a δ := by
  have key : ∀ δ : ℝ, Metric.ball a δ = Ioo (a - δ) (a + δ) := fun δ => by
    ext x
    rw [Metric.mem_ball, Real.dist_eq, abs_lt, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  constructor
  · rintro ⟨ha, l, u, hl, hu, h⟩
    refine ⟨ha, min (a - l) (u - a), lt_min (by linarith) (by linarith), fun x hx hxa => ?_⟩
    rw [key] at hx ⊢
    have h1 := min_le_left (a - l) (u - a)
    have h2 := min_le_right (a - l) (u - a)
    have hx' : x ∈ Ioo l u := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨n, hn⟩ := h x hx' hxa
    refine ⟨n, fun hn' => hn ⟨?_, ?_⟩⟩ <;> linarith [hn'.1, hn'.2]
  · rintro ⟨ha, δ, hδ, h⟩
    refine ⟨ha, a - δ, a + δ, by linarith, by linarith, fun x hx hxa => ?_⟩
    rw [← key] at hx
    obtain ⟨n, hn⟩ := h x hx hxa
    rw [key] at hn
    exact ⟨n, hn⟩

/-- Morris, Topology Without Tears, Definition A3.3.5 (TP-440). A fixed point is neutral exactly when
it is neither attracting nor repelling. -/
@[kb "morris2024" "Definition A3.3.5, p. 443"]
theorem isNeutralFixedPt_iff {f : ℝ → ℝ} {a : ℝ} :
    IsNeutralFixedPt f a ↔ IsFixedPt f a ∧ ¬ IsAttractingFixedPt f a ∧ ¬ IsRepellingFixedPt f a :=
  Iff.rfl

end Attracting

/-! ### The derivative test -/

section DerivativeTest

/-- Local estimate used in both parts of the derivative test. -/
private lemma eventually_dist_image_close {f : ℝ → ℝ} {a L : ℝ} (hf : HasDerivAt f L a)
    (ha : f a = a) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ x ∈ Metric.ball a δ, |f x - a - (x - a) * L| ≤ c * |x - a| := by
  have h := (hf.isLittleO).def hc
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := h (Metric.mem_ball.mp hx)
  simpa [ha, Real.norm_eq_abs, mul_comm] using this

/-- Morris, Topology Without Tears, Theorem A3.5.2 (TP-441). If `f a = a` and `f` has derivative `L`
at `a` with `|L| < 1`, then `a` is an attracting fixed point (derivative form). -/
theorem isAttractingFixedPt_of_hasDerivAt {f : ℝ → ℝ} {a L : ℝ} (hf : HasDerivAt f L a)
    (ha : f a = a) (hL : |L| < 1) : IsAttractingFixedPt f a := by
  set k : ℝ := (|L| + 1) / 2 with hk
  have hk0 : 0 ≤ k := by positivity
  have hk1 : k < 1 := by rw [hk]; linarith
  obtain ⟨δ, hδ, hball⟩ := eventually_dist_image_close hf ha (c := (1 - |L|) / 2) (by linarith)
  have step : ∀ x ∈ Metric.ball a δ, dist (f x) a ≤ k * dist x a := by
    intro x hx
    have h := hball x hx
    rw [Real.dist_eq, Real.dist_eq]
    have h1 : |f x - a| ≤ |f x - a - (x - a) * L| + |(x - a) * L| := by
      have := abs_add_le (f x - a - (x - a) * L) ((x - a) * L)
      simpa using this
    rw [abs_mul] at h1
    nlinarith [abs_nonneg (x - a), abs_nonneg L]
  have iter : ∀ x ∈ Metric.ball a δ, ∀ n : ℕ, dist (f^[n] x) a ≤ k ^ n * dist x a := by
    intro x hx n
    induction n with
    | zero => simp
    | succ n ih =>
      have hmem : f^[n] x ∈ Metric.ball a δ := by
        rw [Metric.mem_ball]
        calc dist (f^[n] x) a ≤ k ^ n * dist x a := ih
          _ ≤ 1 * dist x a := by
            gcongr
            exact pow_le_one₀ hk0 hk1.le
          _ < δ := by simpa using Metric.mem_ball.mp hx
      rw [iterate_succ_apply', pow_succ]
      calc dist (f (f^[n] x)) a ≤ k * dist (f^[n] x) a := step _ hmem
        _ ≤ k * (k ^ n * dist x a) := by gcongr
        _ = k ^ n * k * dist x a := by ring
  refine isAttractingFixedPt_iff_ball.mpr ⟨ha, δ, hδ, fun x hx => ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => iter x hx n) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const (dist x a)

/-- Morris, Topology Without Tears, Theorem A3.5.3 (TP-442). If `f a = a` and `f` has derivative `L`
at `a` with `|L| > 1`, then `a` is a repelling fixed point (derivative form). -/
theorem isRepellingFixedPt_of_hasDerivAt {f : ℝ → ℝ} {a L : ℝ} (hf : HasDerivAt f L a)
    (ha : f a = a) (hL : 1 < |L|) : IsRepellingFixedPt f a := by
  set k : ℝ := (|L| + 1) / 2 with hk
  have hk1 : 1 < k := by rw [hk]; linarith
  obtain ⟨δ, hδ, hball⟩ := eventually_dist_image_close hf ha (c := (|L| - 1) / 2) (by linarith)
  have step : ∀ x ∈ Metric.ball a δ, k * dist x a ≤ dist (f x) a := by
    intro x hx
    have h := hball x hx
    rw [Real.dist_eq, Real.dist_eq]
    have h1 : |(x - a) * L| ≤ |f x - a| + |f x - a - (x - a) * L| := by
      calc |(x - a) * L| = |(f x - a) + (-(f x - a - (x - a) * L))| := by congr 1; ring
        _ ≤ |f x - a| + |-(f x - a - (x - a) * L)| := abs_add_le _ _
        _ = |f x - a| + |f x - a - (x - a) * L| := by rw [abs_neg]
    rw [abs_mul] at h1
    nlinarith [abs_nonneg (x - a), abs_nonneg L]
  refine isRepellingFixedPt_iff_ball.mpr ⟨ha, δ, hδ, fun x hx hxa => ?_⟩
  by_contra hcon
  push Not at hcon
  have d0 : 0 < dist x a := dist_pos.mpr hxa
  have iter : ∀ n : ℕ, k ^ n * dist x a ≤ dist (f^[n] x) a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', pow_succ]
      calc k ^ n * k * dist x a = k * (k ^ n * dist x a) := by ring
        _ ≤ k * dist (f^[n] x) a := by gcongr
        _ ≤ dist (f (f^[n] x)) a := step _ (hcon n)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ / dist x a) hk1
  have h1 : δ < k ^ n * dist x a := by
    rwa [div_lt_iff₀ d0] at hn
  have h2 := Metric.mem_ball.mp (hcon n)
  linarith [iter n]

/-- Morris, Topology Without Tears, Theorem A3.5.2 (TP-441). Let `a` be an interior fixed point of an
interval on which `f` is defined (here `f : ℝ → ℝ`; only the germ of `f` at `a` matters). If `f` is
differentiable at `a` and `|f'(a)| < 1`, then `a` is an attracting fixed point. -/
@[kb "morris2024" "Theorem A3.5.2, p. 451"]
theorem isAttractingFixedPt_of_deriv_lt {f : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a)
    (ha : IsFixedPt f a) (hd : |deriv f a| < 1) : IsAttractingFixedPt f a :=
  isAttractingFixedPt_of_hasDerivAt hf.hasDerivAt ha hd

/-- Morris, Topology Without Tears, Theorem A3.5.3 (TP-442). If `f` is differentiable at the fixed
point `a` and `|f'(a)| > 1`, then `a` is a repelling fixed point. -/
@[kb "morris2024" "Theorem A3.5.3, p. 451"]
theorem isRepellingFixedPt_of_one_lt_deriv {f : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a)
    (ha : IsFixedPt f a) (hd : 1 < |deriv f a|) : IsRepellingFixedPt f a :=
  isRepellingFixedPt_of_hasDerivAt hf.hasDerivAt ha hd

end DerivativeTest

/-! ### Cycles and attracting / repelling periodic points -/

section Cycles

variable {α : Type*}

/-- `C` is an *`m`-cycle* of `f` if it is the orbit of a point of prime period `m`. -/
def IsMCycle (f : α → α) (m : ℕ) (C : Set α) : Prop :=
  ∃ x, 0 < m ∧ minimalPeriod f x = m ∧ C = forwardOrbit f x

/-- Morris, Topology Without Tears, Definition A3.5.8 (TP-444). The orbit of a point of prime period
`m` is `{x, f x, ..., f^(m-1) x}`. -/
@[kb "morris2024" "Definition A3.5.8, p. 453"]
theorem forwardOrbit_eq_image_Iio (f : α → α) (x : α) :
    forwardOrbit f x = (fun k : ℕ => f^[k] x) '' Iio (minimalPeriod f x) ∨ x ∉ periodicPts f := by
  by_cases hx : x ∈ periodicPts f
  · left
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n % minimalPeriod f x, Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx),
        iterate_mod_minimalPeriod_eq⟩
    · rintro ⟨k, -, rfl⟩
      exact ⟨k, rfl⟩
  · right; exact hx

/-- Morris, Topology Without Tears, Definition A3.5.8 (TP-444). A cycle of length `m` is the image of
`{0, ..., m-1}` under `k ↦ f^k x`, listed without repetition (hence it has exactly `m` points). -/
@[kb "morris2024" "Definition A3.5.8, p. 453"]
theorem IsMCycle.eq_image_Iio {f : α → α} {m : ℕ} {C : Set α} (h : IsMCycle f m C) :
    ∃ x, C = (fun k : ℕ => f^[k] x) '' Iio m ∧ Set.InjOn (fun k : ℕ => f^[k] x) (Iio m) := by
  obtain ⟨x, hm, hx, rfl⟩ := h
  have hper : x ∈ periodicPts f := by
    rw [← minimalPeriod_pos_iff_mem_periodicPts]; omega
  refine ⟨x, ?_, ?_⟩
  · rcases forwardOrbit_eq_image_Iio f x with h | h
    · rw [h, hx]
    · exact absurd hper h
  · rw [← hx]; exact iterate_injOn_Iio_minimalPeriod

/-- Morris, Topology Without Tears, Definition A3.5.8 (TP-444). An `m`-cycle has exactly `m` points
(Exercises A3.2 #4). -/
@[kb "morris2024" "Definition A3.5.8, p. 453"]
theorem IsMCycle.ncard_eq {f : α → α} {m : ℕ} {C : Set α} (h : IsMCycle f m C) : C.ncard = m := by
  obtain ⟨x, rfl, hinj⟩ := h.eq_image_Iio
  rw [hinj.ncard_image]
  exact Set.ncard_Iio_nat m

end Cycles

section PeriodicAttracting

/-- A periodic point `a` of prime period `m` is *attracting* if it is an attracting fixed point of `f^m`. -/
def IsAttractingPeriodicPt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a ∈ periodicPts f ∧ IsAttractingFixedPt (f^[minimalPeriod f a]) a

/-- A periodic point `a` of prime period `m` is *repelling* if it is a repelling fixed point of `f^m`. -/
def IsRepellingPeriodicPt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  a ∈ periodicPts f ∧ IsRepellingFixedPt (f^[minimalPeriod f a]) a

/-- Morris, Topology Without Tears, Definition A3.5.9 (TP-445). Attracting periodic points of prime
period `m` are exactly the attracting fixed points of `f^m` among points of prime period `m`. -/
@[kb "morris2024" "Definition A3.5.9, p. 453"]
theorem isAttractingPeriodicPt_iff {f : ℝ → ℝ} {a : ℝ} {m : ℕ} (hm : minimalPeriod f a = m)
    (hpos : 0 < m) : IsAttractingPeriodicPt f a ↔ IsAttractingFixedPt (f^[m]) a := by
  have hper : a ∈ periodicPts f := by
    rw [← minimalPeriod_pos_iff_mem_periodicPts]; omega
  unfold IsAttractingPeriodicPt
  rw [hm]
  exact ⟨fun h => h.2, fun h => ⟨hper, h⟩⟩

/-- Morris, Topology Without Tears, Definition A3.5.9 (TP-445). Repelling periodic points of prime
period `m` are exactly the repelling fixed points of `f^m` among points of prime period `m`. -/
@[kb "morris2024" "Definition A3.5.9, p. 453"]
theorem isRepellingPeriodicPt_iff {f : ℝ → ℝ} {a : ℝ} {m : ℕ} (hm : minimalPeriod f a = m)
    (hpos : 0 < m) : IsRepellingPeriodicPt f a ↔ IsRepellingFixedPt (f^[m]) a := by
  have hper : a ∈ periodicPts f := by
    rw [← minimalPeriod_pos_iff_mem_periodicPts]; omega
  unfold IsRepellingPeriodicPt
  rw [hm]
  exact ⟨fun h => h.2, fun h => ⟨hper, h⟩⟩

/-- Morris, Topology Without Tears, Definition A3.5.9 (TP-445). For a fixed point (period 1) the new
notions agree with the old ones. -/
@[kb "morris2024" "Definition A3.5.9, p. 453"]
theorem isAttractingPeriodicPt_iff_of_isFixedPt {f : ℝ → ℝ} {a : ℝ} (ha : IsFixedPt f a) :
    IsAttractingPeriodicPt f a ↔ IsAttractingFixedPt f a := by
  have := isAttractingPeriodicPt_iff (f := f) (m := 1)
    (minimalPeriod_eq_one_iff_isFixedPt.mpr ha) Nat.one_pos
  simpa using this

/-- Morris, Topology Without Tears, Definition A3.5.9 (TP-445). For a fixed point (period 1) the new
notions agree with the old ones. -/
@[kb "morris2024" "Definition A3.5.9, p. 453"]
theorem isRepellingPeriodicPt_iff_of_isFixedPt {f : ℝ → ℝ} {a : ℝ} (ha : IsFixedPt f a) :
    IsRepellingPeriodicPt f a ↔ IsRepellingFixedPt f a := by
  have := isRepellingPeriodicPt_iff (f := f) (m := 1)
    (minimalPeriod_eq_one_iff_isFixedPt.mpr ha) Nat.one_pos
  simpa using this

end PeriodicAttracting

/-! ### The quadratic family `Q_c(x) = x^2 + c`

Morris, Theorems A3.5.6 (first bifurcation theorem) and A3.5.10 (second bifurcation theorem). -/

/-- The quadratic map `Q_c(x) = x^2 + c`. -/
def quadMap (c : ℝ) : ℝ → ℝ := fun x => x ^ 2 + c

/-- `Q_c` has derivative `2 x` at `x`. -/
lemma hasDerivAt_quadMap (c x : ℝ) : HasDerivAt (quadMap c) (2 * x) x := by
  unfold quadMap
  convert (hasDerivAt_pow 2 x).add_const c using 1
  simp

/-- The larger fixed point `a₊ = (1 + √(1 - 4c)) / 2` of `Q_c`. -/
noncomputable def fixedPlus (c : ℝ) : ℝ := (1 + Real.sqrt (1 - 4 * c)) / 2

/-- The smaller fixed point `a₋ = (1 - √(1 - 4c)) / 2` of `Q_c`. -/
noncomputable def fixedMinus (c : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * c)) / 2

/-- Morris, Topology Without Tears, Theorem A3.5.6 (i) (TP-443). For `c > 1/4`, every orbit of `Q_c` tends
to infinity. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem quadMap_tendsto_atTop {c : ℝ} (hc : 1 / 4 < c) (x : ℝ) :
    Tendsto (fun n : ℕ => (quadMap c)^[n] x) atTop atTop := by
  have hδ : 0 < c - 1 / 4 := by linarith
  have hb : ∀ n : ℕ, x + n * (c - 1 / 4) ≤ (quadMap c)^[n] x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have : (quadMap c)^[n] x + (c - 1 / 4) ≤ quadMap c ((quadMap c)^[n] x) := by
        simp only [quadMap]
        nlinarith [sq_nonneg ((quadMap c)^[n] x - 1 / 2)]
      push_cast
      linarith
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (c - 1 / 4)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hδ
  exact tendsto_atTop_mono hb (tendsto_atTop_add_const_left atTop x h1)

/-- Morris, Topology Without Tears, Theorem A3.5.6 (ii) (TP-443). For `c = 1/4`, `1/2` is the only fixed
point of `Q_c`. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem isFixedPt_quadMap_quarter_iff (x : ℝ) : IsFixedPt (quadMap (1 / 4)) x ↔ x = 1 / 2 := by
  unfold IsFixedPt quadMap
  constructor
  · intro h
    nlinarith [sq_nonneg (x - 1 / 2)]
  · rintro rfl; norm_num

/-- Morris, Topology Without Tears, Theorem A3.5.6 (ii) (TP-443). For `c = 1/4`, the fixed point `1/2`
is neutral. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem isNeutralFixedPt_quadMap_quarter : IsNeutralFixedPt (quadMap (1 / 4)) (1 / 2) := by
  have hmono : ∀ y : ℝ, y ≤ quadMap (1 / 4) y := fun y => by
    simp only [quadMap]; nlinarith [sq_nonneg (y - 1 / 2)]
  refine ⟨(isFixedPt_quadMap_quarter_iff _).mpr rfl, ?_, ?_⟩
  · rintro ⟨-, l, u, hl, hu, h⟩
    set x : ℝ := (1 / 2 + u) / 2 with hx
    have hxI : x ∈ Ioo l u := ⟨by linarith, by linarith⟩
    have hge : ∀ n : ℕ, x ≤ (quadMap (1 / 4))^[n] x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [iterate_succ_apply']; exact ih.trans (hmono _)
    have := ge_of_tendsto' (h x hxI) hge
    linarith
  · rintro ⟨-, l, u, hl, hu, h⟩
    set x : ℝ := max l 0 / 2 + 1 / 4 with hx
    have hl0 : max l 0 < 1 / 2 := max_lt hl (by norm_num)
    have hx1 : max l 0 < x := by
      have := le_max_right l 0; have := le_max_left l 0; rw [hx]; linarith
    have hx2 : x < 1 / 2 := by rw [hx]; linarith
    have hx0 : 0 < x := by
      have := le_max_right l 0; rw [hx]; linarith
    have hxl : l < x := lt_of_le_of_lt (le_max_left l 0) hx1
    have hinv : ∀ n : ℕ, x ≤ (quadMap (1 / 4))^[n] x ∧ (quadMap (1 / 4))^[n] x < 1 / 2 := by
      intro n
      induction n with
      | zero => exact ⟨le_rfl, hx2⟩
      | succ n ih =>
        rw [iterate_succ_apply']
        refine ⟨ih.1.trans (hmono _), ?_⟩
        simp only [quadMap]
        have h0 : 0 < (quadMap (1 / 4))^[n] x := lt_of_lt_of_le hx0 ih.1
        nlinarith [ih.2]
    obtain ⟨n, hn⟩ := h x ⟨hxl, by linarith⟩ hx2.ne
    exact hn ⟨by linarith [(hinv n).1], by linarith [(hinv n).2]⟩

/-- The two fixed points of `Q_c` for `c < 1/4`, and nothing else. -/
lemma isFixedPt_quadMap_iff {c : ℝ} (hc : c < 1 / 4) (x : ℝ) :
    IsFixedPt (quadMap c) x ↔ x = fixedPlus c ∨ x = fixedMinus c := by
  have hs : Real.sqrt (1 - 4 * c) ^ 2 = 1 - 4 * c := Real.sq_sqrt (by linarith)
  unfold IsFixedPt quadMap fixedPlus fixedMinus
  constructor
  · intro h
    have h2 : (x - (1 + Real.sqrt (1 - 4 * c)) / 2) * (x - (1 - Real.sqrt (1 - 4 * c)) / 2) = 0 := by
      linear_combination h - (1 / 4) * hs
    rcases mul_eq_zero.mp h2 with h3 | h3
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> linear_combination (1 / 4) * hs

/-- Morris, Topology Without Tears, Theorem A3.5.6 (iii) (TP-443). For `c < 1/4` the fixed points of `Q_c`
are exactly `a₊` and `a₋`, and these are distinct. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem isFixedPt_quadMap_iff_of_lt {c : ℝ} (hc : c < 1 / 4) :
    (∀ x : ℝ, IsFixedPt (quadMap c) x ↔ x = fixedPlus c ∨ x = fixedMinus c) ∧
      fixedPlus c ≠ fixedMinus c := by
  refine ⟨isFixedPt_quadMap_iff hc, ?_⟩
  have : 0 < Real.sqrt (1 - 4 * c) := Real.sqrt_pos.mpr (by linarith)
  unfold fixedPlus fixedMinus
  intro h; linarith

/-- Morris, Topology Without Tears, Theorem A3.5.6 (iii)(a) (TP-443). For `c < 1/4` the fixed point `a₊`
is repelling. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem isRepellingFixedPt_fixedPlus {c : ℝ} (hc : c < 1 / 4) :
    IsRepellingFixedPt (quadMap c) (fixedPlus c) := by
  have hfix := (isFixedPt_quadMap_iff hc _).mpr (Or.inl rfl)
  have hpos : 0 < Real.sqrt (1 - 4 * c) := Real.sqrt_pos.mpr (by linarith)
  refine isRepellingFixedPt_of_hasDerivAt (hasDerivAt_quadMap c _) hfix ?_
  unfold fixedPlus
  rw [abs_of_pos (by linarith)]
  linarith

/-- Morris, Topology Without Tears, Theorem A3.5.6 (iii)(b) (TP-443). For `-3/4 < c < 1/4` the fixed point
`a₋` is attracting. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem isAttractingFixedPt_fixedMinus {c : ℝ} (hc : c < 1 / 4) (hc' : -3 / 4 < c) :
    IsAttractingFixedPt (quadMap c) (fixedMinus c) := by
  have hfix := (isFixedPt_quadMap_iff hc _).mpr (Or.inr rfl)
  have hpos : 0 < Real.sqrt (1 - 4 * c) := Real.sqrt_pos.mpr (by linarith)
  have hlt : Real.sqrt (1 - 4 * c) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  refine isAttractingFixedPt_of_hasDerivAt (hasDerivAt_quadMap c _) hfix ?_
  unfold fixedMinus
  rw [abs_lt]
  constructor <;> linarith

/-- Morris, Topology Without Tears, Theorem A3.5.6 (iii)(c) (TP-443). For `c < -3/4` the fixed point `a₋`
is repelling. -/
@[kb "morris2024" "Theorem A3.5.6, p. 453"]
theorem isRepellingFixedPt_fixedMinus {c : ℝ} (hc : c < -3 / 4) :
    IsRepellingFixedPt (quadMap c) (fixedMinus c) := by
  have hfix := (isFixedPt_quadMap_iff (c := c) (by linarith) _).mpr (Or.inr rfl)
  have hgt : 2 < Real.sqrt (1 - 4 * c) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; linarith
  refine isRepellingFixedPt_of_hasDerivAt (hasDerivAt_quadMap c _) hfix ?_
  unfold fixedMinus
  rw [abs_of_neg (by linarith)]
  linarith

/-- The point `q₊ = (-1 + √(-4c - 3)) / 2` of the 2-cycle of `Q_c` (for `c < -3/4`). -/
noncomputable def cyclePlus (c : ℝ) : ℝ := (-1 + Real.sqrt (-4 * c - 3)) / 2

/-- The point `q₋ = (-1 - √(-4c - 3)) / 2` of the 2-cycle of `Q_c` (for `c < -3/4`). -/
noncomputable def cycleMinus (c : ℝ) : ℝ := (-1 - Real.sqrt (-4 * c - 3)) / 2

private lemma quad_cycle_sq {c : ℝ} (hc : c < -3 / 4) :
    Real.sqrt (-4 * c - 3) ^ 2 = -4 * c - 3 := Real.sq_sqrt (by linarith)

lemma quadMap_cyclePlus {c : ℝ} (hc : c < -3 / 4) : quadMap c (cyclePlus c) = cycleMinus c := by
  have hr := quad_cycle_sq hc
  unfold quadMap cyclePlus cycleMinus
  linear_combination (1 / 4) * hr

lemma quadMap_cycleMinus {c : ℝ} (hc : c < -3 / 4) : quadMap c (cycleMinus c) = cyclePlus c := by
  have hr := quad_cycle_sq hc
  unfold quadMap cyclePlus cycleMinus
  linear_combination (1 / 4) * hr

lemma cyclePlus_ne_cycleMinus {c : ℝ} (hc : c < -3 / 4) : cyclePlus c ≠ cycleMinus c := by
  have : 0 < Real.sqrt (-4 * c - 3) := Real.sqrt_pos.mpr (by linarith)
  unfold cyclePlus cycleMinus
  intro h; linarith

private lemma isPeriodicPt_two_cyclePlus {c : ℝ} (hc : c < -3 / 4) :
    IsPeriodicPt (quadMap c) 2 (cyclePlus c) := by
  show quadMap c (quadMap c (cyclePlus c)) = cyclePlus c
  rw [quadMap_cyclePlus hc, quadMap_cycleMinus hc]

lemma minimalPeriod_cyclePlus {c : ℝ} (hc : c < -3 / 4) :
    minimalPeriod (quadMap c) (cyclePlus c) = 2 := by
  refine minimalPeriod_eq_prime (p := 2) (isPeriodicPt_two_cyclePlus hc) ?_
  intro h
  have : quadMap c (cyclePlus c) = cyclePlus c := h
  rw [quadMap_cyclePlus hc] at this
  exact cyclePlus_ne_cycleMinus hc this.symm

lemma minimalPeriod_cycleMinus {c : ℝ} (hc : c < -3 / 4) :
    minimalPeriod (quadMap c) (cycleMinus c) = 2 := by
  have h := minimalPeriod_apply (f := quadMap c) (x := cyclePlus c)
    (mk_mem_periodicPts (n := 2) (by norm_num) (isPeriodicPt_two_cyclePlus hc))
  rw [quadMap_cyclePlus hc, minimalPeriod_cyclePlus hc] at h
  exact h

/-- Morris, Topology Without Tears, Theorem A3.5.10 (a) (TP-446). For `-3/4 ≤ c`, `Q_c` has no point
of prime period `2`. -/
@[kb "morris2024" "Theorem A3.5.10, p. 454"]
theorem quadMap_minimalPeriod_ne_two {c : ℝ} (hc : -3 / 4 ≤ c) (x : ℝ) :
    minimalPeriod (quadMap c) x ≠ 2 := by
  intro h
  have hper : IsPeriodicPt (quadMap c) 2 x := by
    rw [← h]; exact isPeriodicPt_minimalPeriod _ _
  have hnf : ¬ IsFixedPt (quadMap c) x := by
    intro hf
    have := minimalPeriod_eq_one_iff_isFixedPt.mpr hf
    omega
  have h2 : quadMap c (quadMap c x) = x := hper
  simp only [IsFixedPt, quadMap] at hnf h2
  have hfac : (x ^ 2 - x + c) * (x ^ 2 + x + c + 1) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp hfac with h3 | h3
  · exact hnf (by linarith)
  · have h4 : (x + 1 / 2) ^ 2 = -(c + 3 / 4) := by linear_combination h3
    have h5 : x = -1 / 2 := by
      have h6 : (x + 1 / 2) ^ 2 = 0 := by nlinarith [sq_nonneg (x + 1 / 2)]
      have := (pow_eq_zero_iff (two_ne_zero)).mp h6
      linarith
    apply hnf
    have hc' : c = -3 / 4 := by rw [h5] at h3; linarith
    rw [h5, hc']; norm_num

/-- Morris, Topology Without Tears, Theorem A3.5.10 (a) (TP-446). For `-3/4 ≤ c < 1/4`, `Q_c` has no
`2`-cycle. -/
@[kb "morris2024" "Theorem A3.5.10, p. 454"]
theorem not_isMCycle_two_quadMap {c : ℝ} (hc : -3 / 4 ≤ c) (C : Set ℝ) :
    ¬ IsMCycle (quadMap c) 2 C := by
  rintro ⟨x, -, hx, -⟩
  exact quadMap_minimalPeriod_ne_two hc x hx

private lemma quad_cycle_orbit {c : ℝ} (hc : c < -3 / 4) :
    IsMCycle (quadMap c) 2 {cycleMinus c, cyclePlus c} := by
  refine ⟨cyclePlus c, by norm_num, minimalPeriod_cyclePlus hc, ?_⟩
  rcases forwardOrbit_eq_image_Iio (quadMap c) (cyclePlus c) with h | h
  · rw [h, minimalPeriod_cyclePlus hc]
    have hI : (Iio 2 : Set ℕ) = {0, 1} := by ext k; simp; omega
    rw [hI, image_pair]
    simp [quadMap_cyclePlus hc, Set.pair_comm]
  · exact absurd (mk_mem_periodicPts (n := 2) (by norm_num) (isPeriodicPt_two_cyclePlus hc)) h

private lemma hasDerivAt_quadMap_iterate_two (c q : ℝ) :
    HasDerivAt ((quadMap c)^[2]) (2 * quadMap c q * (2 * q)) q := by
  have h := (hasDerivAt_quadMap c (quadMap c q)).comp q (hasDerivAt_quadMap c q)
  have e : (quadMap c)^[2] = quadMap c ∘ quadMap c := by
    funext x; rfl
  rw [e]
  exact h

private lemma quad_cycle_deriv {c : ℝ} (hc : c < -3 / 4) :
    2 * quadMap c (cyclePlus c) * (2 * cyclePlus c) = 4 * (c + 1) ∧
    2 * quadMap c (cycleMinus c) * (2 * cycleMinus c) = 4 * (c + 1) := by
  have hr := quad_cycle_sq hc
  rw [quadMap_cyclePlus hc, quadMap_cycleMinus hc]
  unfold cyclePlus cycleMinus
  constructor <;> linear_combination (-1) * hr

private lemma isFixedPt_iterate_two {c : ℝ} (hc : c < -3 / 4) :
    IsFixedPt ((quadMap c)^[2]) (cyclePlus c) ∧ IsFixedPt ((quadMap c)^[2]) (cycleMinus c) := by
  constructor
  · exact isPeriodicPt_two_cyclePlus hc
  · show quadMap c (quadMap c (cycleMinus c)) = cycleMinus c
    rw [quadMap_cycleMinus hc, quadMap_cyclePlus hc]

/-- Morris, Topology Without Tears, Theorem A3.5.10 (b) (TP-446). For `-5/4 < c < -3/4`, `Q_c` has the
`2`-cycle `{q₋, q₊}`, and both its points are attracting periodic points. -/
@[kb "morris2024" "Theorem A3.5.10, p. 454"]
theorem quadMap_attracting_two_cycle {c : ℝ} (h1 : -5 / 4 < c) (h2 : c < -3 / 4) :
    IsMCycle (quadMap c) 2 {cycleMinus c, cyclePlus c} ∧
      IsAttractingPeriodicPt (quadMap c) (cycleMinus c) ∧
      IsAttractingPeriodicPt (quadMap c) (cyclePlus c) := by
  have hd := quad_cycle_deriv h2
  have hf := isFixedPt_iterate_two h2
  have hlt : |4 * (c + 1)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  refine ⟨quad_cycle_orbit h2, ?_, ?_⟩
  · rw [isAttractingPeriodicPt_iff (minimalPeriod_cycleMinus h2) (by norm_num)]
    refine isAttractingFixedPt_of_hasDerivAt (hasDerivAt_quadMap_iterate_two c _) hf.2 ?_
    rw [hd.2]; exact hlt
  · rw [isAttractingPeriodicPt_iff (minimalPeriod_cyclePlus h2) (by norm_num)]
    refine isAttractingFixedPt_of_hasDerivAt (hasDerivAt_quadMap_iterate_two c _) hf.1 ?_
    rw [hd.1]; exact hlt

/-- Morris, Topology Without Tears, Theorem A3.5.10 (c) (TP-446). For `c < -5/4`, `Q_c` has the
`2`-cycle `{q₋, q₊}`, and both its points are repelling periodic points. -/
@[kb "morris2024" "Theorem A3.5.10, p. 454"]
theorem quadMap_repelling_two_cycle {c : ℝ} (h1 : c < -5 / 4) :
    IsMCycle (quadMap c) 2 {cycleMinus c, cyclePlus c} ∧
      IsRepellingPeriodicPt (quadMap c) (cycleMinus c) ∧
      IsRepellingPeriodicPt (quadMap c) (cyclePlus c) := by
  have h2 : c < -3 / 4 := by linarith
  have hd := quad_cycle_deriv h2
  have hf := isFixedPt_iterate_two h2
  have hlt : 1 < |4 * (c + 1)| := by
    rw [abs_of_neg (by linarith)]; linarith
  refine ⟨quad_cycle_orbit h2, ?_, ?_⟩
  · rw [isRepellingPeriodicPt_iff (minimalPeriod_cycleMinus h2) (by norm_num)]
    refine isRepellingFixedPt_of_hasDerivAt (hasDerivAt_quadMap_iterate_two c _) hf.2 ?_
    rw [hd.2]; exact hlt
  · rw [isRepellingPeriodicPt_iff (minimalPeriod_cyclePlus h2) (by norm_num)]
    refine isRepellingFixedPt_of_hasDerivAt (hasDerivAt_quadMap_iterate_two c _) hf.1 ?_
    rw [hd.1]; exact hlt

end UndergradKB.Topology
