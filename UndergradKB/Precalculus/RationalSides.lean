import UndergradKB.Precalculus.Rational

/-! # Behaviour on the two sides of a vertical asymptote (Stitz-Zeager, §4.2)

Theorem 4.1 (`hole_or_vertical_asymptote`) says that `x = c` is a vertical asymptote of a reduced rational function
`p(x)/q(x)` when `q(c) = 0`. The opening of §4.2 (p. 332) explains that a rational function can change sign at a
vertical asymptote without crossing the x-axis, and the worked graphs of §4.2 read off on which side the graph goes
up and on which it goes down. This file makes that precise: if `c` is a zero of multiplicity `m` of the denominator,
`q(x) = (x - c)^m q₁(x)` with `q₁(c) ≠ 0`, and `p(c) ≠ 0`, then as `x → c⁺` the function tends to `∞` or `-∞` by the
sign of `p(c)/q₁(c)`, and as `x → c⁻` by the sign of `(-1)^m p(c)/q₁(c)`. So the graph goes the same way on both
sides exactly when `m` is even, the analogue for asymptotes of the multiplicity rule for zeros (Theorem 3.3).
-/

namespace UndergradKB.Precalculus

open Filter Topology Polynomial Set

/-- From the left, `1 / (c - x)^m → ∞` as `x → c⁻` (for `m ≠ 0`). -/
theorem tendsto_inv_pow_sub_left {c : ℝ} {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun x => ((c - x) ^ m)⁻¹) (𝓝[<] c) atTop := by
  have hsub : Tendsto (fun x => c - x) (𝓝[<] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x => c - x) (𝓝 c) (𝓝 (c - c)) := tendsto_const_nhds.sub tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Iio.mp hx)
  have h1 : Tendsto (fun x => (c - x)⁻¹) (𝓝[<] c) atTop := tendsto_inv_nhdsGT_zero.comp hsub
  refine ((tendsto_pow_atTop hm).comp h1).congr' (Eventually.of_forall fun x => ?_)
  simp [inv_pow]

/-- From the right, `1 / (x - c)^m → ∞` as `x → c⁺` (for `m ≠ 0`). -/
theorem tendsto_inv_pow_sub_right {c : ℝ} {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun x => ((x - c) ^ m)⁻¹) (𝓝[>] c) atTop := by
  have hsub : Tendsto (fun x => x - c) (𝓝[>] c) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x => x - c) (𝓝 c) (𝓝 (c - c)) := tendsto_id.sub tendsto_const_nhds
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Ioi.mp hx)
  have h1 : Tendsto (fun x => (x - c)⁻¹) (𝓝[>] c) atTop := tendsto_inv_nhdsGT_zero.comp hsub
  refine ((tendsto_pow_atTop hm).comp h1).congr' (Eventually.of_forall fun x => ?_)
  simp [inv_pow]

/-- §4.2 (p. 332), behaviour of a rational function on the two sides of a vertical asymptote: let the denominator
be `q(x) = (x - c)^m q₁(x)` with `m ≥ 1` and `q₁(c) ≠ 0`, and let `p(c) ≠ 0` (so `x = c` is a vertical asymptote
of `r(x) = p(x)/q(x)` by Theorem 4.1; the hypothesis is implicit below in `k ≠ 0`). Put `k = p(c)/q₁(c)`. As `x → c⁺`, `r(x) → ∞` if `k > 0` and
`r(x) → -∞` if `k < 0`; as `x → c⁻`, `r(x) → ∞` if `(-1)^m k > 0` and `r(x) → -∞` if `(-1)^m k < 0`. -/
@[kb "stitzzeager2013" "§4.2 (behaviour at a vertical asymptote), p. 332"]
theorem vertical_asymptote_sides {p q₁ : ℝ[X]} {c : ℝ} {m : ℕ} (hm : m ≠ 0) (hq₁ : q₁.eval c ≠ 0) :
    let r := fun x => p.eval x / ((X - C c) ^ m * q₁).eval x
    let k := p.eval c / q₁.eval c
    (0 < k → Tendsto r (𝓝[>] c) atTop) ∧ (k < 0 → Tendsto r (𝓝[>] c) atBot) ∧
      (0 < (-1) ^ m * k → Tendsto r (𝓝[<] c) atTop) ∧ (((-1) ^ m * k < 0 → Tendsto r (𝓝[<] c) atBot)) := by
  intro r k
  have hlim : Tendsto (fun x => p.eval x / q₁.eval x) (𝓝 c) (𝓝 k) :=
    (p.continuous.continuousAt.div q₁.continuous.continuousAt hq₁).tendsto
  have hR : (fun x => p.eval x / q₁.eval x * ((x - c) ^ m)⁻¹) = r := by
    funext x
    simp only [r, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    ring
  have hL : (fun x => (-1) ^ m * (p.eval x / q₁.eval x) * ((c - x) ^ m)⁻¹) = r := by
    funext x
    simp only [r, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    have : (x - c) ^ m = (-1) ^ m * (c - x) ^ m := by rw [← mul_pow]; ring
    rw [this]
    have h1 : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
    have h2 : (((-1 : ℝ) ^ m))⁻¹ = (-1) ^ m := inv_eq_of_mul_eq_one_left h1
    simp only [div_eq_mul_inv, mul_inv, h2]; ring
  have hlimR := hlim.mono_left (nhdsWithin_le_nhds (s := Ioi c))
  have hlimL := (hlim.const_mul ((-1 : ℝ) ^ m)).mono_left (nhdsWithin_le_nhds (s := Iio c))
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [← hR]; exact hlimR.pos_mul_atTop hk (tendsto_inv_pow_sub_right hm)
  · rw [← hR]; exact hlimR.neg_mul_atTop hk (tendsto_inv_pow_sub_right hm)
  · rw [← hL]; exact hlimL.pos_mul_atTop hk (tendsto_inv_pow_sub_left hm)
  · rw [← hL]; exact hlimL.neg_mul_atTop hk (tendsto_inv_pow_sub_left hm)

/-- §4.2 (p. 332), parity form: in the situation of `vertical_asymptote_sides`, if the multiplicity `m` is even the
graph goes the same way (both up or both down) on the two sides of `x = c`; if `m` is odd it goes up on one side and
down on the other, so the function changes sign at the asymptote without its graph crossing the x-axis. -/
@[kb "stitzzeager2013" "§4.2 (behaviour at a vertical asymptote), p. 332"]
theorem vertical_asymptote_sides_parity {p q₁ : ℝ[X]} {c : ℝ} {m : ℕ} (hm : m ≠ 0) (hq₁ : q₁.eval c ≠ 0)
    (hp : p.eval c ≠ 0) :
    let r := fun x => p.eval x / ((X - C c) ^ m * q₁).eval x
    (Even m → (Tendsto r (𝓝[<] c) atTop ∧ Tendsto r (𝓝[>] c) atTop) ∨
      (Tendsto r (𝓝[<] c) atBot ∧ Tendsto r (𝓝[>] c) atBot)) ∧
    (Odd m → (Tendsto r (𝓝[<] c) atBot ∧ Tendsto r (𝓝[>] c) atTop) ∨
      (Tendsto r (𝓝[<] c) atTop ∧ Tendsto r (𝓝[>] c) atBot)) := by
  intro r
  obtain ⟨h1, h2, h3, h4⟩ := vertical_asymptote_sides (p := p) hm hq₁
  have hk : p.eval c / q₁.eval c ≠ 0 := div_ne_zero hp hq₁
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · rw [he.neg_one_pow, one_mul] at h3 h4
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · exact Or.inr ⟨h4 hneg, h2 hneg⟩
    · exact Or.inl ⟨h3 hpos, h1 hpos⟩
  · rw [ho.neg_one_pow, neg_one_mul, neg_pos, neg_lt_zero] at *
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · exact Or.inr ⟨h3 hneg, h2 hneg⟩
    · exact Or.inl ⟨h4 hpos, h1 hpos⟩

/-- §4.2 (p. 332) for a rational function in lowest terms: if `p` and `q` have no common zero, `q(c) = 0` and `m` is
the multiplicity of `c` as a zero of `q`, then from the right `p(x)/q(x)` tends to `∞` or `-∞`, and from the left it
tends to the same infinity when `m` is even and to the opposite one when `m` is odd. -/
@[kb "stitzzeager2013" "§4.2 (behaviour at a vertical asymptote), p. 332"]
theorem vertical_asymptote_sides_reduced {p q : ℝ[X]} (hq : q ≠ 0)
    (hpq : ∀ x, ¬ (p.eval x = 0 ∧ q.eval x = 0)) {c : ℝ} (hqc : q.eval c = 0) :
    let r := fun x => p.eval x / q.eval x
    (Even (q.rootMultiplicity c) → (Tendsto r (𝓝[<] c) atTop ∧ Tendsto r (𝓝[>] c) atTop) ∨
      (Tendsto r (𝓝[<] c) atBot ∧ Tendsto r (𝓝[>] c) atBot)) ∧
    (Odd (q.rootMultiplicity c) → (Tendsto r (𝓝[<] c) atBot ∧ Tendsto r (𝓝[>] c) atTop) ∨
      (Tendsto r (𝓝[<] c) atTop ∧ Tendsto r (𝓝[>] c) atBot)) := by
  intro r
  set m := q.rootMultiplicity c
  set q₁ := q /ₘ (X - C c) ^ m
  have hfac : (X - C c) ^ m * q₁ = q := pow_mul_divByMonic_rootMultiplicity_eq q c
  have hq₁ : q₁.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hq
  have hm : m ≠ 0 := by
    intro h0
    apply hq₁
    have : q₁ = q := by simpa [h0] using hfac
    rw [this, hqc]
  have hp : p.eval c ≠ 0 := fun h => hpq c ⟨h, hqc⟩
  have := vertical_asymptote_sides_parity hm hq₁ hp
  simp only [hfac] at this
  exact this

/-- Function form of `vertical_asymptote_sides`, for the worked examples: if near `c` (with `x ≠ c`) the function
is `f(x) = g(x)/(x - c)^m` with `m ≥ 1` and `g` continuous at `c`, then from the right `f` tends to `∞` or `-∞` by
the sign of `g(c)`, and from the left by the sign of `(-1)^m g(c)`. -/
theorem tendsto_sides_of_eq_div_pow {f g : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : m ≠ 0) (hg : ContinuousAt g c)
    (hf : ∀ᶠ x in 𝓝[≠] c, f x = g x / (x - c) ^ m) :
    (0 < g c → Tendsto f (𝓝[>] c) atTop) ∧ (g c < 0 → Tendsto f (𝓝[>] c) atBot) ∧
      (0 < (-1) ^ m * g c → Tendsto f (𝓝[<] c) atTop) ∧ ((-1) ^ m * g c < 0 → Tendsto f (𝓝[<] c) atBot) := by
  have hR : ∀ᶠ x in 𝓝[>] c, g x * ((x - c) ^ m)⁻¹ = f x :=
    (hf.filter_mono (nhdsWithin_mono c fun x (hx : x ∈ Ioi c) => (ne_of_gt (mem_Ioi.mp hx) : x ≠ c))).mono
      fun x hx => by rw [hx, div_eq_mul_inv]
  have h1 : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  have h2 : (((-1 : ℝ) ^ m))⁻¹ = (-1) ^ m := inv_eq_of_mul_eq_one_left h1
  have hL : ∀ᶠ x in 𝓝[<] c, (-1) ^ m * g x * ((c - x) ^ m)⁻¹ = f x :=
    (hf.filter_mono (nhdsWithin_mono c fun x (hx : x ∈ Iio c) => (ne_of_lt (mem_Iio.mp hx) : x ≠ c))).mono
      fun x hx => by
        rw [hx, show (x - c) ^ m = (-1) ^ m * (c - x) ^ m by rw [← mul_pow]; ring]
        simp only [div_eq_mul_inv, mul_inv, h2]; ring
  have hlimR := hg.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi c))
  have hlimL := (hg.tendsto.const_mul ((-1 : ℝ) ^ m)).mono_left (nhdsWithin_le_nhds (s := Iio c))
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · exact (hlimR.pos_mul_atTop hk (tendsto_inv_pow_sub_right hm)).congr' hR
  · exact (hlimR.neg_mul_atTop hk (tendsto_inv_pow_sub_right hm)).congr' hR
  · exact (hlimL.pos_mul_atTop hk (tendsto_inv_pow_sub_left hm)).congr' hL
  · exact (hlimL.neg_mul_atTop hk (tendsto_inv_pow_sub_left hm)).congr' hL

end UndergradKB.Precalculus
