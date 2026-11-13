import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import UndergradKB.DifferentialEquations.BesselSeries
import UndergradKB.DifferentialEquations.SecondOrderLinear
import UndergradKB.Common.Attr

/-! # Bessel function of the second kind, order 0 (Lebl, *Notes on Diffy Qs*, §7.3.3, Example 7.3.4)

For `x > 0` let `J_0 = besselJR 0` and
`y₂(x) = J_0(x) log x + ∑_{k ≥ 1} c_k x^(2k)` with `c_k = (-1)^(k+1) H_k / (4^k (k!)²)` (`H_k` the harmonic
number).  We prove that `y₂` solves Bessel's equation of order 0 on `x > 0`, tends to `-∞` at `0⁺`, that
`J_0, y₂` are independent, and that every solution on `(0, ∞)` is `A J_0 + B y₂`.  The same is transported to
the book's `Y_0 = (2/π)(y₂ + (γ - log 2) J_0)`, and to `x² y'' + x y' + λ² x² y = 0` (Example 7.3.4).
-/

namespace UndergradKB.DifferentialEquations

open Filter Topology

/-- Harmonic numbers `H_k = ∑_{i<k} 1/(i+1)` as reals. -/
noncomputable def harmR (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1)

lemma harmR_nonneg (k : ℕ) : 0 ≤ harmR k := Finset.sum_nonneg (fun i _ => by positivity)

lemma harmR_le (k : ℕ) : harmR k ≤ k := by
  calc harmR k ≤ ∑ _i ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    _ = k := by simp

lemma harmR_succ (k : ℕ) : harmR (k + 1) = harmR k + 1 / ((k : ℝ) + 1) :=
  Finset.sum_range_succ _ _

/-- The coefficients `c_k = (-1)^(k+1) H_k / (4^k (k!)²)` of the series part of `y₂`
(`c_0 = 0`), written as `-H_k · bcoef 0 k`. -/
noncomputable def besselYcoef (k : ℕ) : ℝ := - harmR k * bcoef 0 k

lemma besselYcoef_eq (k : ℕ) :
    besselYcoef k = (-1) ^ (k + 1) * harmR k / (4 ^ k * ((k.factorial : ℝ)) ^ 2) := by
  unfold besselYcoef bcoef
  have g : Real.Gamma ((k : ℝ) + 0 + 1) = (k.factorial : ℝ) := by
    rw [add_zero]; exact Real.Gamma_nat_eq_factorial k
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [g, pow_succ]
  field_simp

lemma besselYcoef_hsum : ∀ r : ℝ, 0 < r → Summable fun n => |besselYcoef n| * r ^ n := by
  intro r hr
  have := summable_n (bcoef_hsum 0 (hp_of_nonneg (le_refl (0 : ℝ)))) hr
  refine this.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  unfold besselYcoef
  rw [abs_mul, abs_neg, abs_of_nonneg (harmR_nonneg n)]
  have h := harmR_le n
  calc harmR n * |bcoef 0 n| * r ^ n ≤ (n : ℝ) * |bcoef 0 n| * r ^ n := by gcongr
    _ = _ := by ring

lemma besselYcoef_rec (n : ℕ) :
    besselYcoef (n + 1) * (4 * ((n : ℝ) + 1) ^ 2) + besselYcoef n = bcoef 1 n := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  have h1 := bcoef_rec 0 hp0 n
  have h2 := bcoef_succ_shift 0 hp0 n
  rw [zero_add] at h2
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have e : bcoef 0 (n + 1) = - bcoef 0 n / (4 * ((n : ℝ) + 1) ^ 2) := by
    field_simp
    linear_combination h1
  unfold besselYcoef
  rw [harmR_succ, h2, e]
  field_simp
  ring

lemma evS_tendsto_gen {b : ℕ → ℝ} (hsum : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n) :
    Tendsto (evS b) (𝓝 0) (𝓝 (b 0)) := by
  have hc : ContinuousAt (evS b) 0 := (hasDerivAt_evS hsum 0).continuousAt
  have h0 : evS b 0 = b 0 := by
    unfold evS
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow (by omega : 2 * n ≠ 0)]
  rw [← h0]
  exact hc.tendsto

/-- The series identity for the inhomogeneous recurrence `4 (n+1)² b_{n+1} + b_n = d_n`:
`x S'' + S' + x S = x ∑ d_n x^(2n)`. -/
lemma evS_ode_inhom {b d : ℕ → ℝ}
    (hrec : ∀ n : ℕ, b (n + 1) * (4 * ((n : ℝ) + 1) ^ 2) + b n = d n)
    (hsb : ∀ r : ℝ, 0 < r → Summable fun n => |b n| * r ^ n)
    (hsd : ∀ r : ℝ, 0 < r → Summable fun n => |d n| * r ^ n) (x : ℝ) :
    x * evS2 b x + evS1 b x + x * evS b x = x * evS d x := by
  have hR : 1 ≤ |x| + 1 := by linarith [abs_nonneg x]
  have s0 := summable0 hsb (abs_lt_R x) hR
  have s1 := summable1 hsb (abs_lt_R x) hR
  have s2 := summable2 hsb (abs_lt_R x) hR
  have sd := summable0 hsd (abs_lt_R x) hR
  set A : ℕ → ℝ := fun n =>
    x * (b n * (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ) * x ^ (2 * n - 1 - 1)))) +
      (b n * (((2 * n : ℕ) : ℝ) * x ^ (2 * n - 1))) with hA
  have sA : Summable A := (s2.mul_left x).add s1
  have e1 : x * evS2 b x + evS1 b x = ∑' n, A n := by
    unfold evS2 evS1
    rw [← tsum_mul_left, ← Summable.tsum_add (s2.mul_left x) s1]
  have hA0 : A 0 = 0 := by simp [hA]
  have su : Summable fun n : ℕ => d n * x ^ (2 * n + 1) :=
    (sd.mul_left x).congr (fun n => by rw [pow_succ]; ring)
  have sv : Summable fun n : ℕ => b n * x ^ (2 * n + 1) :=
    (s0.mul_left x).congr (fun n => by rw [pow_succ]; ring)
  have hAs : ∀ n : ℕ, A (n + 1) = d n * x ^ (2 * n + 1) - b n * x ^ (2 * n + 1) := by
    intro n
    have e2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e3 : 2 * n + 1 - 1 = 2 * n := by omega
    simp only [hA, e2, e3]
    push_cast
    have := hrec n
    have hp : x ^ (2 * n + 1) = x ^ (2 * n) * x := pow_succ _ _
    rw [hp]
    linear_combination (x ^ (2 * n) * x) * this
  have e4 : ∑' n, A n = ∑' n : ℕ, (d n * x ^ (2 * n + 1) - b n * x ^ (2 * n + 1)) := by
    rw [sA.tsum_eq_zero_add, hA0, zero_add]
    exact tsum_congr hAs
  have ed : x * evS d x = ∑' n : ℕ, d n * x ^ (2 * n + 1) := by
    unfold evS
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by rw [pow_succ]; ring)
  have eb : x * evS b x = ∑' n : ℕ, b n * x ^ (2 * n + 1) := by
    unfold evS
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by rw [pow_succ]; ring)
  rw [e1, e4, Summable.tsum_sub su sv]
  linarith [ed, eb]

/-- The second solution `y₂(x) = J_0(x) log x + ∑ c_k x^(2k)` of Bessel's equation of order 0, `x > 0`. -/
noncomputable def besselY2 (x : ℝ) : ℝ := besselJR 0 x * Real.log x + evS besselYcoef x

/-- Explicit first derivative of `besselY2` on `x > 0`. -/
noncomputable def besselY2d (x : ℝ) : ℝ :=
  besselJ1 0 x * Real.log x + besselJR 0 x / x + evS1 besselYcoef x

/-- Explicit second derivative of `besselY2` on `x > 0`. -/
noncomputable def besselY2dd (x : ℝ) : ℝ :=
  besselJ2 0 x * Real.log x + besselJ1 0 x / x + (besselJ1 0 x / x - besselJR 0 x / x ^ 2) +
    evS2 besselYcoef x

lemma hasDerivAt_besselY2 {x : ℝ} (hx : 0 < x) : HasDerivAt besselY2 (besselY2d x) x := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  have h := ((hasDerivAt_besselJR 0 hp0 hx).mul (Real.hasDerivAt_log hx.ne')).add
    (hasDerivAt_evS besselYcoef_hsum x)
  refine h.congr_deriv ?_
  unfold besselY2d
  ring

lemma hasDerivAt_besselY2d {x : ℝ} (hx : 0 < x) : HasDerivAt besselY2d (besselY2dd x) x := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  have h := (((hasDerivAt_besselJ1 0 hp0 hx).mul (Real.hasDerivAt_log hx.ne')).add
    ((hasDerivAt_besselJR 0 hp0 hx).div (hasDerivAt_id' x) hx.ne')).add
    (hasDerivAt_evS1 besselYcoef_hsum x)
  refine h.congr_deriv ?_
  unfold besselY2dd
  have hx0 := hx.ne'
  field_simp

lemma besselJ1_zero_eq {x : ℝ} (hx : 0 < x) : besselJ1 0 x = - besselJR 1 x := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  rw [← (hasDerivAt_besselJR 0 hp0 hx).deriv]
  exact deriv_besselJR_zero hx

lemma besselY2_ode {x : ℝ} (hx : 0 < x) :
    x ^ 2 * besselY2dd x + x * besselY2d x + x ^ 2 * besselY2 x = 0 := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  have hJ := besselJ2_ode 0 hp0 hx
  have hJ1 := besselJ1_zero_eq hx
  have hS := evS_ode_inhom besselYcoef_rec besselYcoef_hsum
    (bcoef_hsum 1 (hp_of_nonneg (zero_le_one' ℝ))) x
  have hJ1' : besselJR 1 x = x / 2 * evS (bcoef 1) x := by
    rw [besselJR_eq 1 x hx, Real.rpow_one]
  have hx0 := hx.ne'
  have key : x ^ 2 * besselY2dd x + x * besselY2d x + x ^ 2 * besselY2 x =
      Real.log x * (x ^ 2 * besselJ2 0 x + x * besselJ1 0 x + (x ^ 2 - 0 ^ 2) * besselJR 0 x) +
        x * (x * evS2 besselYcoef x + evS1 besselYcoef x + x * evS besselYcoef x) +
        2 * x * besselJ1 0 x := by
    unfold besselY2dd besselY2d besselY2
    field_simp
    ring
  rw [key, hJ, hS, hJ1, hJ1']
  ring

lemma solves_of_hasDeriv {f f1 f2 : ℝ → ℝ}
    (h1 : ∀ x, 0 < x → HasDerivAt f (f1 x) x) (h2 : ∀ x, 0 < x → HasDerivAt f1 (f2 x) x)
    (h3 : ∀ x, 0 < x → x ^ 2 * f2 x + x * f1 x + x ^ 2 * f x = 0) :
    SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) f := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have hd : deriv f =ᶠ[𝓝 x] f1 := by
    filter_upwards [Ioi_mem_nhds hx'] with y hy using (h1 y hy).deriv
  have hdd : HasDerivAt (deriv f) (f2 x) x := (h2 x hx').congr_of_eventuallyEq hd
  refine ⟨(h1 x hx').differentiableAt, hdd.differentiableAt, ?_⟩
  rw [hdd.deriv, (h1 x hx').deriv]
  have h := h3 x hx'
  have e : f2 x + 1 / x * f1 x + 1 * f x = (x ^ 2 * f2 x + x * f1 x + x ^ 2 * f x) / x ^ 2 := by
    field_simp
  simp only [Pi.zero_apply]
  rw [e, h, zero_div]

lemma besselJ_solves : SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) (besselJR 0) := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  exact solves_of_hasDeriv (fun x hx => hasDerivAt_besselJR 0 hp0 hx)
    (fun x hx => hasDerivAt_besselJ1 0 hp0 hx)
    (fun x hx => by have := besselJ2_ode 0 hp0 hx; linear_combination this)

lemma besselY2_solves : SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) besselY2 :=
  solves_of_hasDeriv (fun _ hx => hasDerivAt_besselY2 hx) (fun _ hx => hasDerivAt_besselY2d hx)
    (fun _ hx => besselY2_ode hx)

lemma besselJR_zero_tendsto : Tendsto (besselJR 0) (𝓝[>] 0) (𝓝 1) := by
  have hp0 := hp_of_nonneg (le_refl (0 : ℝ))
  have h := (evS_tendsto_gen (bcoef_hsum 0 hp0)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have e : bcoef 0 0 = 1 := by simp [bcoef]
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [besselJR_eq 0 x hx, Real.rpow_zero, one_mul]

lemma evS_Y_tendsto : Tendsto (evS besselYcoef) (𝓝[>] 0) (𝓝 0) := by
  have h := (evS_tendsto_gen besselYcoef_hsum).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have e : besselYcoef 0 = 0 := by simp [besselYcoef, harmR]
  rwa [e] at h

/-- `y₂(x) → -∞` as `x → 0⁺`. -/
theorem besselY2_tendsto_atBot : Tendsto besselY2 (𝓝[>] 0) atBot := by
  have h1 : Tendsto (fun x => Real.log x * besselJR 0 x) (𝓝[>] 0) atBot :=
    Real.tendsto_log_nhdsGT_zero.atBot_mul_pos one_pos besselJR_zero_tendsto
  have h2 := h1.atBot_add evS_Y_tendsto
  exact h2.congr (fun x => by unfold besselY2; ring)

lemma linIndep_of {f g : ℝ → ℝ} (h : ∀ a b : ℝ, (∀ x : ℝ, 0 < x → a * f x + b * g x = 0) → a = 0 ∧ b = 0) :
    LinearIndependent ℝ ![fun t : Set.Ioi (0 : ℝ) => f t, fun t : Set.Ioi (0 : ℝ) => g t] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : ∀ x : ℝ, 0 < x → c 0 * f x + c 1 * g x = 0 := by
    intro x hx
    have := congrFun hc ⟨x, hx⟩
    simpa [Fin.sum_univ_two] using this
  have := h _ _ h0
  fin_cases i
  · exact this.1
  · exact this.2

lemma besselJ_Y2_indep (a b : ℝ) (h : ∀ x : ℝ, 0 < x → a * besselJR 0 x + b * besselY2 x = 0) :
    a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), besselY2 x = (-(a / b)) * besselJR 0 x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have := h x hx
      field_simp
      linarith
    have ht : Tendsto besselY2 (𝓝[>] 0) (𝓝 ((-(a / b)) * 1)) :=
      (besselJR_zero_tendsto.const_mul (-(a / b))).congr' (hev.mono fun x hx => hx.symm)
    exact not_tendsto_nhds_of_tendsto_atBot besselY2_tendsto_atBot _ ht
  subst hb
  refine ⟨?_, rfl⟩
  have ht : Tendsto (fun x => a * besselJR 0 x) (𝓝[>] 0) (𝓝 (a * 1)) :=
    besselJR_zero_tendsto.const_mul a
  have ht0 : Tendsto (fun x => a * besselJR 0 x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have := h x hx
      simpa using this.symm)
  have := tendsto_nhds_unique ht ht0
  linarith

/-- Every solution on `(0, ∞)` of Bessel's equation of order 0 is `A J_0 + B y₂`. -/
theorem besselY2_general {y : ℝ → ℝ}
    (hy : SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) y) :
    ∃ A B : ℝ, ∀ x : ℝ, 0 < x → y x = A * besselJR 0 x + B * besselY2 x := by
  obtain ⟨C₁, C₂, h⟩ := lin2_general_solution Set.ordConnected_Ioi
    (continuousOn_const.div continuousOn_id (fun x hx => (Set.mem_Ioi.mp hx).ne'))
    continuousOn_const besselJ_solves besselY2_solves
    (linIndep_of besselJ_Y2_indep) Set.nonempty_Ioi hy
  exact ⟨C₁, C₂, fun x hx => h x hx⟩

/-! ## The book's `Y_0` -/

/-- Bridging definition of Lebl's `Y_0` on `x > 0`: `Y_0 = (2/π)(y₂ + (γ - log 2) J_0)` with `γ` Euler's
constant.  The book defines `Y_n` as a limit of combinations of `J_p, J_{-p}` as `p → n`; this is the standard
explicit formula for `n = 0`, and the limit characterization is not proved here. -/
noncomputable def besselY0 (x : ℝ) : ℝ :=
  2 / Real.pi * (besselY2 x + (Real.eulerMascheroniConstant - Real.log 2) * besselJR 0 x)

lemma besselY0_eq :
    besselY0 = fun x => (2 / Real.pi * (Real.eulerMascheroniConstant - Real.log 2)) * besselJR 0 x +
      (2 / Real.pi) * besselY2 x := by
  funext x; unfold besselY0; ring

lemma besselY0_solves : SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) besselY0 := by
  rw [besselY0_eq]
  have := lin2_superposition (isOpen_Ioi (a := (0 : ℝ))) besselJ_solves besselY2_solves
    (2 / Real.pi * (Real.eulerMascheroniConstant - Real.log 2)) (2 / Real.pi)
  exact this

theorem besselY0_tendsto_atBot : Tendsto besselY0 (𝓝[>] 0) atBot := by
  have h1 := besselY2_tendsto_atBot.atBot_add
    ((besselJR_zero_tendsto.const_mul (Real.eulerMascheroniConstant - Real.log 2)))
  exact (h1.const_mul_atBot (by positivity : (0 : ℝ) < 2 / Real.pi))

lemma besselJ_Y0_indep (a b : ℝ) (h : ∀ x : ℝ, 0 < x → a * besselJR 0 x + b * besselY0 x = 0) :
    a = 0 ∧ b = 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have := besselJ_Y2_indep (a + b * (2 / Real.pi * (Real.eulerMascheroniConstant - Real.log 2)))
    (b * (2 / Real.pi)) (fun x hx => by
      have := h x hx
      unfold besselY0 at this
      linear_combination this)
  have hb : b = 0 := by
    have h2 := this.2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 (by positivity)
  subst hb
  refine ⟨by simpa using this.1, rfl⟩

/-- DE-214 (§7.3.3 Bessel function of the second kind, p. 349), order 0.  On `x > 0` the function `Y_0` solves
Bessel's equation `x² y'' + x y' + x² y = 0`, `Y_0(x) → -∞` as `x → 0⁺`, and every twice differentiable
solution on `(0, ∞)` is `A J_0 + B Y_0`.  Only `n = 0` is treated, with `Y_0` given by the explicit formula
`besselY0` (the limit definition of `Y_n` from `J_p, J_{-p}` is not proved). -/
@[kb "lebldiffyqs2026" "§7.3.3 Bessel function of the second kind, p. 349"]
theorem besselY0_second_kind :
    (∀ x : ℝ, 0 < x → x ^ 2 * deriv (deriv besselY0) x + x * deriv besselY0 x + x ^ 2 * besselY0 x = 0) ∧
    Tendsto besselY0 (𝓝[>] 0) atBot ∧
    (∀ y : ℝ → ℝ, SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) y →
      ∃ A B : ℝ, ∀ x : ℝ, 0 < x → y x = A * besselJR 0 x + B * besselY0 x) := by
  refine ⟨?_, besselY0_tendsto_atBot, ?_⟩
  · intro x hx
    obtain ⟨-, -, e⟩ := besselY0_solves x hx
    have hx0 : x ≠ 0 := hx.ne'
    have : x ^ 2 * deriv (deriv besselY0) x + x * deriv besselY0 x + x ^ 2 * besselY0 x =
        x ^ 2 * (deriv (deriv besselY0) x + 1 / x * deriv besselY0 x + 1 * besselY0 x) := by
      field_simp
    rw [this]
    simp only [Pi.zero_apply] at e
    rw [e, mul_zero]
  · intro y hy
    obtain ⟨C₁, C₂, h⟩ := lin2_general_solution Set.ordConnected_Ioi
      (continuousOn_const.div continuousOn_id (fun x hx => (Set.mem_Ioi.mp hx).ne'))
      continuousOn_const besselJ_solves besselY0_solves
      (linIndep_of besselJ_Y0_indep) Set.nonempty_Ioi hy
    exact ⟨C₁, C₂, fun x hx => h x hx⟩

/-! ## Example 7.3.4: the equation `x² y'' + x y' + λ² x² y = 0` -/

/-- `y` is a (twice differentiable) solution of `x² y'' + x y' + λ² x² y = 0` on `x > 0`. -/
def BesselZeroSol (l : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → DifferentiableAt ℝ y x ∧ DifferentiableAt ℝ (deriv y) x ∧
    x ^ 2 * deriv (deriv y) x + x * deriv y x + l ^ 2 * x ^ 2 * y x = 0

lemma bessel_zero_sol_iff (l : ℝ) (y : ℝ → ℝ) :
    SolvesLin2 (fun x => 1 / x) (fun _ => l ^ 2) 0 (Set.Ioi 0) y ↔ BesselZeroSol l y := by
  unfold SolvesLin2 BesselZeroSol
  simp only [Set.mem_Ioi, Pi.zero_apply]
  refine forall_congr' fun x => forall_congr' fun hx => and_congr Iff.rfl (and_congr Iff.rfl ?_)
  have hx0 : x ≠ 0 := hx.ne'
  have e : x ^ 2 * deriv (deriv y) x + x * deriv y x + l ^ 2 * x ^ 2 * y x =
      x ^ 2 * (deriv (deriv y) x + 1 / x * deriv y x + l ^ 2 * y x) := by
    field_simp
  rw [e]
  have : x ^ 2 ≠ 0 := by positivity
  simp [this]

lemma solves_rescale {f : ℝ → ℝ} (l : ℝ) (hl : 0 < l)
    (hf : SolvesLin2 (fun x => 1 / x) (fun _ => 1) 0 (Set.Ioi 0) f) :
    SolvesLin2 (fun x => 1 / x) (fun _ => l ^ 2) 0 (Set.Ioi 0) (fun x => f (l * x)) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have hlx : l * x ∈ Set.Ioi (0 : ℝ) := mul_pos hl hx'
  have hcomp : ∀ u : ℝ, 0 < u → HasDerivAt (fun x => f (l * x)) (l * deriv f (l * u)) u := by
    intro u hu
    have := (hf (l * u) (mul_pos hl hu)).1.hasDerivAt.comp u ((hasDerivAt_id' u).const_mul l)
    exact this.congr_deriv (by ring)
  have hd : deriv (fun x => f (l * x)) =ᶠ[𝓝 x] fun u => l * deriv f (l * u) := by
    filter_upwards [Ioi_mem_nhds hx'] with u hu using (hcomp u hu).deriv
  have hdd : HasDerivAt (deriv fun x => f (l * x)) (l * (l * deriv (deriv f) (l * x))) x := by
    have := ((hf (l * x) hlx).2.1.hasDerivAt.comp x ((hasDerivAt_id' x).const_mul l)).const_mul l
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq hd
  refine ⟨(hcomp x hx').differentiableAt, hdd.differentiableAt, ?_⟩
  rw [hdd.deriv, (hcomp x hx').deriv]
  obtain ⟨-, -, e⟩ := hf (l * x) hlx
  simp only [Pi.zero_apply] at e ⊢
  have hx0 : x ≠ 0 := hx'.ne'
  have hl0 : l ≠ 0 := hl.ne'
  have key : l * (l * deriv (deriv f) (l * x)) + 1 / x * (l * deriv f (l * x)) + l ^ 2 * f (l * x) =
      l ^ 2 * (deriv (deriv f) (l * x) + 1 / (l * x) * deriv f (l * x) + 1 * f (l * x)) := by
    field_simp
  rw [key, e, mul_zero]

/-- DE-216 (Example 7.3.4, p. 349), `λ > 0`: `x ↦ J_0(λx)` and `x ↦ Y_0(λx)` solve
`x² y'' + x y' + λ² x² y = 0` on `x > 0` (the rescaling `t = λx` of Bessel's equation of order 0), and every
twice differentiable solution on `(0, ∞)` is `A J_0(λx) + B Y_0(λx)`. -/
@[kb "lebldiffyqs2026" "Example 7.3.4, p. 349"]
theorem bessel_lambda_general (l : ℝ) (hl : 0 < l) :
    BesselZeroSol l (fun x => besselJR 0 (l * x)) ∧ BesselZeroSol l (fun x => besselY0 (l * x)) ∧
    (∀ y : ℝ → ℝ, BesselZeroSol l y →
      ∃ A B : ℝ, ∀ x : ℝ, 0 < x → y x = A * besselJR 0 (l * x) + B * besselY0 (l * x)) := by
  have hJ := solves_rescale l hl besselJ_solves
  have hY := solves_rescale l hl besselY0_solves
  refine ⟨(bessel_zero_sol_iff _ _).mp hJ, (bessel_zero_sol_iff _ _).mp hY, ?_⟩
  intro y hy
  have hli : LinearIndependent ℝ ![fun t : Set.Ioi (0 : ℝ) => besselJR 0 (l * t),
      fun t : Set.Ioi (0 : ℝ) => besselY0 (l * t)] := by
    refine linIndep_of (f := fun x => besselJR 0 (l * x)) (g := fun x => besselY0 (l * x))
      (fun a b h => besselJ_Y0_indep a b (fun s hs => ?_))
    have := h (s / l) (div_pos hs hl)
    have e : l * (s / l) = s := by field_simp
    simpa only [e] using this
  obtain ⟨C₁, C₂, h⟩ := lin2_general_solution Set.ordConnected_Ioi
    (continuousOn_const.div continuousOn_id (fun x hx => (Set.mem_Ioi.mp hx).ne'))
    continuousOn_const hJ hY hli Set.nonempty_Ioi ((bessel_zero_sol_iff _ _).mpr hy)
  exact ⟨C₁, C₂, fun x hx => h x hx⟩

end UndergradKB.DifferentialEquations
