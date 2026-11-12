import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import UndergradKB.Common.Attr

/-!
# Exponential and logarithmic functions (Stitz-Zeager, §6.1-6.3)

Properties of `x ↦ b ^ x` and `logb b` for a base `b > 0`, `b ≠ 1`, stated for Mathlib's
`Real.rpow` and `Real.logb`.
-/

namespace UndergradKB.Precalculus

open Filter Topology Set Real
open scoped ContDiff

lemma exp_base_eq_exp_mul {b : ℝ} (hb : 0 < b) : (fun x : ℝ => b ^ x) = fun x => exp (x * log b) := by
  funext x; rw [rpow_def_of_pos hb]; ring_nf

lemma exp_base_tendsto_nhdsGT {l : Filter ℝ} {g : ℝ → ℝ}
    (h : Tendsto g l (𝓝 0)) (hpos : ∀ x, 0 < g x) : Tendsto g l (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall hpos⟩

/-- Theorem 6.1, general part: for `b > 0`, `b ≠ 1`, the function `x ↦ b ^ x` has range
`(0, ∞)`, takes the value `1` at `0`, is one-to-one, continuous and smooth (PC-093). -/
@[kb "stitzzeager2013" "Theorem 6.1, p. 431"]
theorem exp_fun_basic {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) :
    Set.range (fun x : ℝ => b ^ x) = Ioi 0 ∧ b ^ (0 : ℝ) = 1 ∧
    Function.Injective (fun x : ℝ => b ^ x) ∧ Continuous (fun x : ℝ => b ^ x) ∧
    ContDiff ℝ ∞ (fun x : ℝ => b ^ x) := by
  refine ⟨?_, rpow_zero b, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩; exact rpow_pos_of_pos hb x
    · intro hy; exact ⟨logb b y, rpow_logb hb hb1 hy⟩
  · intro u w h
    have := congrArg (logb b) h
    simpa [logb_rpow hb hb1] using this
  · exact continuous_const.rpow continuous_id (fun _ => Or.inl hb.ne')
  · rw [exp_base_eq_exp_mul hb]
    exact Real.contDiff_exp.comp (contDiff_id.mul contDiff_const)

/-- Theorem 6.1, case `b > 1`: `x ↦ b ^ x` is increasing, tends to `0` from above as
`x → -∞` (so `y = 0` is a horizontal asymptote) and to `∞` as `x → ∞` (PC-093). -/
@[kb "stitzzeager2013" "Theorem 6.1, p. 431"]
theorem exp_fun_base_gt_one {b : ℝ} (hb : 1 < b) :
    StrictMono (fun x : ℝ => b ^ x) ∧
    Tendsto (fun x : ℝ => b ^ x) atBot (𝓝[>] 0) ∧
    Tendsto (fun x : ℝ => b ^ x) atTop atTop := by
  have hb0 : 0 < b := by linarith
  have hl : 0 < log b := log_pos hb
  rw [exp_base_eq_exp_mul hb0]
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    exact exp_lt_exp.2 (mul_lt_mul_of_pos_right hxy hl)
  · refine exp_base_tendsto_nhdsGT ?_ (fun x => exp_pos _)
    exact tendsto_exp_atBot.comp (tendsto_id.atBot_mul_const hl)
  · exact tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hl)

/-- Theorem 6.1, case `0 < b < 1`: `x ↦ b ^ x` is decreasing, tends to `∞` as `x → -∞` and to
`0` from above as `x → ∞` (PC-093). -/
@[kb "stitzzeager2013" "Theorem 6.1, p. 431"]
theorem exp_fun_base_lt_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1) :
    StrictAnti (fun x : ℝ => b ^ x) ∧
    Tendsto (fun x : ℝ => b ^ x) atBot atTop ∧
    Tendsto (fun x : ℝ => b ^ x) atTop (𝓝[>] 0) := by
  have hl : log b < 0 := log_neg hb0 hb
  rw [exp_base_eq_exp_mul hb0]
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    exact exp_lt_exp.2 (mul_lt_mul_of_neg_right hxy hl)
  · exact tendsto_exp_atTop.comp (tendsto_id.atBot_mul_const_of_neg hl)
  · refine exp_base_tendsto_nhdsGT ?_ (fun x => exp_pos _)
    exact tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg hl)

/-- Theorem 6.2, general part: for `b > 0`, `b ≠ 1`, `logb b` maps `(0, ∞)` onto `ℝ`, sends `1`
to `0`, is one-to-one, continuous and smooth on `(0, ∞)`, satisfies `b ^ a = c ↔ logb b c = a`
for `c > 0`, and the two inverse identities (PC-096). -/
@[kb "stitzzeager2013" "Theorem 6.2, p. 435"]
theorem log_fun_basic {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) :
    logb b '' Ioi 0 = univ ∧ logb b 1 = 0 ∧ InjOn (logb b) (Ioi 0) ∧
    ContinuousOn (logb b) (Ioi 0) ∧ ContDiffOn ℝ ∞ (logb b) (Ioi 0) ∧
    (∀ a c : ℝ, 0 < c → (b ^ a = c ↔ logb b c = a)) ∧
    (∀ x : ℝ, logb b (b ^ x) = x) ∧ (∀ x : ℝ, 0 < x → b ^ (logb b x) = x) := by
  have hsub : Ioi (0 : ℝ) ⊆ {0}ᶜ := fun x hx => ne_of_gt hx
  refine ⟨?_, logb_one, ?_, ?_, ?_, ?_, fun x => logb_rpow hb hb1,
    fun x hx => rpow_logb hb hb1 hx⟩
  · ext y
    simp only [mem_image, mem_univ, iff_true]
    exact ⟨b ^ y, rpow_pos_of_pos hb y, logb_rpow hb hb1⟩
  · intro x hx y hy h
    have := congrArg (fun t => b ^ t) h
    simpa [rpow_logb hb hb1 (mem_Ioi.1 hx), rpow_logb hb hb1 (mem_Ioi.1 hy)] using this
  · have : ContinuousOn log (Ioi 0) := Real.continuousOn_log.mono hsub
    exact this.div_const _
  · exact (Real.contDiffOn_log.mono hsub).div_const _
  · intro a c hc
    rw [logb_eq_iff_rpow_eq hb hb1 hc]

/-- Theorem 6.2, case `b > 1`: `logb b` is increasing on `(0, ∞)`, tends to `-∞` as `x → 0⁺`
(vertical asymptote `x = 0`) and to `∞` as `x → ∞` (PC-096). -/
@[kb "stitzzeager2013" "Theorem 6.2, p. 435"]
theorem log_fun_base_gt_one {b : ℝ} (hb : 1 < b) :
    StrictMonoOn (logb b) (Ioi 0) ∧ Tendsto (logb b) (𝓝[>] 0) atBot ∧
    Tendsto (logb b) atTop atTop := by
  refine ⟨?_, tendsto_logb_nhdsGT_zero hb, tendsto_logb_atTop hb⟩
  intro x hx y hy hxy
  exact (logb_lt_logb_iff hb hx hy).2 hxy

/-- Theorem 6.2, case `0 < b < 1`: `logb b` is decreasing on `(0, ∞)`, tends to `∞` as
`x → 0⁺` and to `-∞` as `x → ∞` (PC-096). -/
@[kb "stitzzeager2013" "Theorem 6.2, p. 435"]
theorem log_fun_base_lt_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1) :
    StrictAntiOn (logb b) (Ioi 0) ∧ Tendsto (logb b) (𝓝[>] 0) atTop ∧
    Tendsto (logb b) atTop atBot := by
  refine ⟨?_, tendsto_logb_nhdsGT_zero_of_base_lt_one hb0 hb, ?_⟩
  · intro x hx y hy hxy
    exact (logb_lt_logb_iff_of_base_lt_one hb0 hb hy hx).2 hxy
  · have hl : log b < 0 := log_neg hb0 hb
    exact tendsto_log_atTop.atTop_mul_const_of_neg (inv_lt_zero.2 hl)

/-- Theorem 6.4 (exponential part): for `b > 0`, `b ≠ 1`, `b ^ u = b ^ w ↔ u = w` (PC-098). -/
@[kb "stitzzeager2013" "Theorem 6.4, p. 449"]
theorem rpow_eq_rpow_iff_exponent {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (u w : ℝ) :
    b ^ u = b ^ w ↔ u = w := by
  constructor
  · intro h
    have := congrArg (logb b) h
    simpa [logb_rpow hb hb1] using this
  · rintro rfl; rfl

/-- Theorem 6.4 (logarithmic part): for `b > 0`, `b ≠ 1`, `u, w > 0`,
`logb b u = logb b w ↔ u = w` (PC-098). -/
@[kb "stitzzeager2013" "Theorem 6.4, p. 449"]
theorem logb_eq_logb_iff {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    logb b u = logb b w ↔ u = w := by
  constructor
  · intro h
    have := congrArg (fun t => b ^ t) h
    simpa [rpow_logb hb hb1 hu, rpow_logb hb hb1 hw] using this
  · rintro rfl; rfl

/-- Theorem 6.7, first change-of-base formula: `a ^ x = b ^ (x * logb b a)` for `a, b > 0`,
`b ≠ 1` (the book also assumes `a ≠ 1`, which is not needed) (PC-101). -/
@[kb "stitzzeager2013" "Theorem 6.7, p. 454"]
theorem rpow_change_of_base {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) (x : ℝ) :
    a ^ x = b ^ (x * logb b a) := by
  rw [mul_comm, rpow_mul hb.le, rpow_logb hb hb1 ha]

/-- Theorem 6.7, second change-of-base formula: `logb a x = logb b x / logb b a` for
`a, b > 0`, `a, b ≠ 1`, `x > 0` (PC-101). -/
@[kb "stitzzeager2013" "Theorem 6.7, p. 454"]
theorem logb_change_of_base {a b : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hb : 0 < b) (hb1 : b ≠ 1)
    (x : ℝ) : logb a x = logb b x / logb b a := by
  have hla : log a ≠ 0 := fun h => by
    rcases Real.log_eq_zero.1 h with h | h | h <;> [linarith; exact ha1 h; linarith]
  have hlb : log b ≠ 0 := fun h => by
    rcases Real.log_eq_zero.1 h with h | h | h <;> [linarith; exact hb1 h; linarith]
  simp only [logb]
  field_simp

end UndergradKB.Precalculus
