import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic
import UndergradKB.Common.Attr
import UndergradKB.Probability.Branching
import UndergradKB.Probability.ExamplesBranching

/-!
# Probability: the Keyfitz data and the geometric branching model (Grinstead–Snell, Examples 10.9, 10.12, 10.13)
-/

open Finset Filter Set
open scoped Topology

namespace UndergradKB.Probability

namespace Keyfitz

variable {p : ℕ → ℝ}

/-- Numerators (over `10000`) of Table 10.2. -/
def num : ℕ → ℕ
  | 0 => 2092 | 1 => 2584 | 2 => 2360 | 3 => 1593 | 4 => 828 | 5 => 357
  | 6 => 133 | 7 => 42 | 8 => 11 | 9 => 2 | _ => 0

/-- Table 10.2 normalized by its sum `1.0002` (the printed values do not sum to `1`). -/
noncomputable def law (k : ℕ) : ℝ := (num k : ℝ) / 10002

theorem law_nonzero_range (k : ℕ) (hk : k ∉ range 11) : law k = 0 := by
  have : 11 ≤ k := by simpa using hk
  have : num k = 0 := by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [num] at this ⊢
  simp [law, this]

theorem isOffspring_law : IsOffspring law where
  nonneg k := by unfold law; positivity
  hasSum := by
    have : HasSum law (∑ k ∈ range 11, law k) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => law_nonzero_range k hk)
    convert this using 1
    simp [sum_range_succ, law, num]
    norm_num

theorem gf_law (z : ℝ) : offspringGF law z = ∑ k ∈ range 11, law k * z ^ k := by
  unfold offspringGF
  exact tsum_eq_sum (fun k hk => by simp [law_nonzero_range k hk])

theorem hasSum_mean_law : HasSum (fun k : ℕ => (k : ℝ) * law k) (∑ k ∈ range 11, (k : ℝ) * law k) :=
  hasSum_sum_of_ne_finset_zero (fun k hk => by simp [law_nonzero_range k hk])

/-- A root `r < 1` of `h z = z` forces `h a ≤ a` for `r < a ≤ 1` (convexity of `h`). -/
theorem gf_le_of_root (hp : IsOffspring p) {r a : ℝ} (hr0 : 0 ≤ r) (hra : r < a) (ha1 : a ≤ 1)
    (hroot : offspringGF p r = r) : offspringGF p a ≤ a := by
  have hr1 : r < 1 := hra.trans_le ha1
  have h1r : 0 < 1 - r := by linarith
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr0, hr1.le⟩
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨hr0.trans hra.le, ha1⟩
  set s := (1 - a) / (1 - r) with hs
  set t := (a - r) / (1 - r) with ht
  have hs0 : 0 ≤ s := div_nonneg (by linarith) h1r.le
  have ht0 : 0 ≤ t := div_nonneg (by linarith) h1r.le
  have hst : s + t = 1 := by rw [hs, ht, ← add_div, div_eq_one_iff_eq h1r.ne']; ring
  have hsr : s * r + t * 1 = a := by rw [hs, ht]; field_simp; ring
  have hconv : ∀ k : ℕ, a ^ k ≤ s * r ^ k + t := fun k => by
    have := (convexOn_pow k).2 (show r ∈ Set.Ici (0 : ℝ) from hr0) (show (1 : ℝ) ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.2 zero_le_one)
      hs0 ht0 hst
    simp only [smul_eq_mul, mul_one, one_pow] at this
    rwa [show s * r + t = a by simpa using hsr] at this
  have h1 : HasSum (fun k => p k * a ^ k) (offspringGF p a) := (Branching.summable_term hp haI).hasSum
  have h2 : HasSum (fun k => p k * (s * r ^ k + t)) (s * offspringGF p r + t) := by
    have := ((Branching.summable_term hp hrI).hasSum.mul_left s).add (hp.hasSum.mul_right t)
    convert this using 1
    · funext k; ring
    · rw [offspringGF, one_mul]
  have := hasSum_le (fun k => mul_le_mul_of_nonneg_left (hconv k) (hp.nonneg k)) h1 h2
  rw [hroot] at this
  calc offspringGF p a ≤ s * r + t := this
    _ = a := by simpa using hsr

/-- If `h a > a` for some `a ∈ [0,1]` then `a < d`. -/
theorem lt_extinction (hp : IsOffspring p) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (h : a < offspringGF p a) : a < extinctionProb p := by
  obtain ⟨_, _, ⟨hmem, hfix⟩, _⟩ := extinction_smallest_root hp
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · linarith [gf_le_of_root hp hmem.1 hlt ha.2 hfix]
  · rw [heq] at hfix; linarith

/-- If `h b < b` for some `b ∈ [0,1]` then `d < b`. -/
theorem extinction_lt (hp : IsOffspring p) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (h : offspringGF p b < b) : extinctionProb p < b := by
  obtain ⟨_, _, _, hleast⟩ := extinction_smallest_root hp
  have hg : ContinuousOn (fun x => offspringGF p x - x) (Icc 0 b) :=
    ((Branching.gf_continuousOn hp).mono (Icc_subset_Icc le_rfl hb.2)).sub continuousOn_id
  have h0 : (0 : ℝ) ∈ Icc (offspringGF p b - b) (offspringGF p 0 - 0) := by
    refine ⟨by linarith, ?_⟩
    rw [Branching.gf_zero]; simpa using hp.nonneg 0
  obtain ⟨r, hrI, hr⟩ := intermediate_value_Icc' hb.1 hg h0
  have hrI' : r ∈ Icc (0 : ℝ) 1 := ⟨hrI.1, hrI.2.trans hb.2⟩
  have := hleast ⟨hrI', by simp only at hr; linarith⟩
  have hrb : r ≠ b := by rintro rfl; simp only at hr; linarith
  exact lt_of_le_of_lt this (lt_of_le_of_ne hrI.2 hrb)

end Keyfitz

open Keyfitz in
/-- Grinstead–Snell Example 10.9 (PR-210). Table 10.2 (Keyfitz's offspring law of Japanese women, ages
45-49 in 1960). Erratum: the printed probabilities `.2092, .2584, .2360, .1593, .0828, .0357, .0133, .0042,
.0011, .0002, .0000` sum to `1.0002`, not `1`; we use the table divided by its sum as the offspring law.
Its mean is `1.8374...` (the book's 1.837, rounded; the unnormalized mean would be `1.8378`), so the
extinction probability is `< 1`; the smallest root `d` of `h z = z` satisfies `.3242 < d < .3243`
(true value `.324202...`; the unnormalized table has root `.324326...`; both round to the book's `.324`). -/
@[kb "grinsteadsnell2006" "Example 10.9, p. 390"]
theorem keyfitz_extinction :
    IsOffspring law ∧ (1.8374 < ∑' k : ℕ, (k : ℝ) * law k ∧ ∑' k : ℕ, (k : ℝ) * law k < 1.8375) ∧
      extinctionProb law < 1 ∧ 0.3242 < extinctionProb law ∧ extinctionProb law < 0.3243 := by
  have hp := isOffspring_law
  have hmean : ∑' k : ℕ, (k : ℝ) * law k = ∑ k ∈ range 11, (k : ℝ) * law k := hasSum_mean_law.tsum_eq
  have hmv : 1.8374 < ∑ k ∈ range 11, (k : ℝ) * law k ∧ ∑ k ∈ range 11, (k : ℝ) * law k < 1.8375 := by
    simp only [sum_range_succ, law, num]; norm_num
  refine ⟨hp, ⟨hmean ▸ hmv.1, hmean ▸ hmv.2⟩, ?_, ?_, ?_⟩
  · refine extinction_prob_lt_one hp ?_
    rintro ⟨_, h⟩
    rw [hmean] at h; linarith [hmv.1]
  · refine lt_extinction hp ⟨by norm_num, by norm_num⟩ ?_
    rw [gf_law]; simp only [sum_range_succ, law, num]; norm_num
  · refine extinction_lt hp ⟨by norm_num, by norm_num⟩ ?_
    rw [gf_law]; simp only [sum_range_succ, law, num]; norm_num

namespace KeyfitzGeom

/-- The linear fractional map `z ↦ (d M (z-1) - (z-d)) / (M (z-1) - (z-d))`; for `M = m^n` it is the
generating function of `Z_n` for the geometric offspring law with mean `m` and extinction probability `d`. -/
noncomputable def lf (d M z : ℝ) : ℝ := (d * M * (z - 1) - (z - d)) / (M * (z - 1) - (z - d))

/-- The book's law of `Z_n` for the geometric model: `P(Z_n = 0) = d (M-1)/(M-d)` and
`P(Z_n = j) = M ((1-d)/(M-d))^2 ((M-1)/(M-d))^(j-1)` for `j ≥ 1`, where `M = m^n`. -/
noncomputable def lawN (d M : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then d * (M - 1) / (M - d) else M * ((1 - d) / (M - d)) ^ 2 * ((M - 1) / (M - d)) ^ (j - 1)

theorem denom_ne (d M z : ℝ) (hd : d < 1) (hM : 1 ≤ M) (hz : z ≤ 1) :
    M * (z - 1) - (z - d) ≠ 0 := by
  nlinarith

theorem lawN_eq_geom (d M : ℝ) (hd1 : d < 1) (hM : 1 ≤ M) (j : ℕ) :
    lawN d M j = geomOffspring (M * ((1 - d) / (M - d)) ^ 2) ((M - 1) / (M - d)) j := by
  have hMd : M - d ≠ 0 := by intro h; linarith
  unfold lawN geomOffspring
  split_ifs with hj
  · have : 1 - (M - 1) / (M - d) = (1 - d) / (M - d) := by field_simp; ring
    rw [this]
    have h1d : 1 - d ≠ 0 := by intro h; linarith
    field_simp
    ring
  · rfl

theorem geom_form (d M z : ℝ) (hd1 : d < 1) (hM : 1 ≤ M) (hz : z ≤ 1) :
    1 - (M * ((1 - d) / (M - d)) ^ 2) / (1 - (M - 1) / (M - d)) +
        (M * ((1 - d) / (M - d)) ^ 2) * z / (1 - (M - 1) / (M - d) * z) = lf d M z := by
  have hMd : M - d ≠ 0 := by intro h; linarith
  have h1d : 1 - d ≠ 0 := by intro h; linarith
  have hD := denom_ne d M z hd1 hM hz
  have h2 : 1 - (M - 1) / (M - d) = (1 - d) / (M - d) := by field_simp; ring
  have h3 : (M - d) - (M - 1) * z ≠ 0 := by intro h; apply hD; nlinarith
  have h4 : 1 - (M - 1) / (M - d) * z = ((M - d) - (M - 1) * z) / (M - d) := by field_simp
  rw [h2, h4]
  unfold lf
  rw [show M * (z - 1) - (z - d) = -((M - d) - (M - 1) * z) by ring]
  generalize hu : (M - d) - (M - 1) * z = u at *
  have hu0 : u ≠ 0 := h3
  field_simp
  rw [← hu]
  ring


theorem lf_comp (d m M z : ℝ) (hd1 : d < 1) (hM : 1 ≤ M) (hm : 1 ≤ m) (hz : z ≤ 1) :
    lf d m (lf d M z) = lf d (m * M) z := by
  have hD := denom_ne d M z hd1 hM hz
  have hD2 := denom_ne d (m * M) z hd1 (by nlinarith) hz
  have h1d : d - 1 ≠ 0 := by intro h; linarith
  have hx : ∀ N D : ℝ, D ≠ 0 → d * m * (N / D - 1) - (N / D - d) = (d * m * (N - D) - (N - d * D)) / D :=
    fun N D hD => by field_simp
  have hy : ∀ N D : ℝ, D ≠ 0 → m * (N / D - 1) - (N / D - d) = (m * (N - D) - (N - d * D)) / D :=
    fun N D hD => by field_simp
  have hY : m * ((d * M * (z - 1) - (z - d)) - (M * (z - 1) - (z - d))) -
      ((d * M * (z - 1) - (z - d)) - d * (M * (z - 1) - (z - d))) =
      (d - 1) * (m * M * (z - 1) - (z - d)) := by ring
  unfold lf
  rw [hx _ _ hD, hy _ _ hD, div_div_div_cancel_right₀ hD, hY]
  rw [div_eq_div_iff (mul_ne_zero h1d hD2) hD2]
  ring

theorem lf_gf {b c m d : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c) (hc1 : c < 1)
    (hm : 1 < b / (1 - c) ^ 2) (hmdef : m = b / (1 - c) ^ 2) (hddef : d = (1 - b - c) / (c * (1 - c))) :
    c = (m - 1) / (m - d) ∧ b = m * ((1 - d) / (m - d)) ^ 2 := by
  have h1c : 0 < 1 - c := by linarith
  have hb2 : (1 - c) ^ 2 < b := by
    rw [lt_div_iff₀ (by positivity)] at hm; linarith
  have h1c' : 1 - c ≠ 0 := h1c.ne'
  have hc : c ≠ 0 := hc0.ne'
  have hmd : m - d = (b - (1 - c) ^ 2) / (c * (1 - c) ^ 2) := by
    rw [hmdef, hddef]; field_simp; ring
  have hm1 : m - 1 = (b - (1 - c) ^ 2) / (1 - c) ^ 2 := by
    rw [hmdef]; field_simp
  have hpos : b - (1 - c) ^ 2 ≠ 0 := by linarith
  have hc : c ≠ 0 := hc0.ne'
  have h1c' : 1 - c ≠ 0 := h1c.ne'
  have h1d : 1 - d = (b - (1 - c) ^ 2) / (c * (1 - c)) := by
    rw [hddef]; field_simp; ring
  constructor
  · rw [hmd, hm1]; field_simp
  · rw [hmd, h1d, hmdef]; field_simp


theorem iterate_mem {p : ℕ → ℝ} (hp : IsOffspring p) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    (offspringGF p)^[n] z ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨Branching.gf_nonneg hp ih, Branching.gf_le_one hp ih⟩

theorem iterate_eq_lf {b c m d : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c) (hc1 : c < 1)
    (hm : 1 < b / (1 - c) ^ 2) (hmdef : m = b / (1 - c) ^ 2) (hddef : d = (1 - b - c) / (c * (1 - c)))
    (n : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (offspringGF (geomOffspring b c))^[n] z = lf d (m ^ n) z := by
  have hp := GeomBranching.isOffspring hb hbc hc0 hc1
  have hd1 : d < 1 := by
    rw [hddef]; exact (geomOffspring_d_lt_one_iff hc0 hc1).2 hm
  have hm1 : 1 ≤ m := by rw [hmdef]; exact hm.le
  obtain ⟨hcm, hbm⟩ := lf_gf hb hbc hc0 hc1 hm hmdef hddef
  induction n with
  | zero =>
    have h1d : d - 1 ≠ 0 := by intro h; linarith
    simp only [Function.iterate_zero, id, pow_zero, lf]
    rw [eq_div_iff (by intro h; apply h1d; linarith)]
    ring
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', ← lf_comp d m (m ^ n) z hd1 (one_le_pow₀ hm1) hm1 hz.2]
    have hw := iterate_mem hp hz n
    rw [ih] at hw
    rw [GeomBranching.gf_eq hc0.le hc1 hw]
    have := geom_form d m (lf d (m ^ n) z) hd1 hm1 hw.2
    rw [← hcm, ← hbm] at this
    exact this

theorem lawN_nonneg {d M : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (hM : 1 ≤ M) (j : ℕ) : 0 ≤ lawN d M j := by
  have h1 : 0 < M - d := by linarith
  have h2 : 0 ≤ M - 1 := by linarith
  unfold lawN
  split_ifs
  · positivity
  · positivity

theorem hasSum_lawN {d M : ℝ} (hd1 : d < 1) (hM : 1 ≤ M) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    HasSum (fun j : ℕ => lawN d M j * z ^ j) (lf d M z) := by
  have hC0 : 0 ≤ (M - 1) / (M - d) := div_nonneg (by linarith) (by linarith)
  have hC1 : (M - 1) / (M - d) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have := GeomBranching.hasSum_gf (b := M * ((1 - d) / (M - d)) ^ 2) hC0 hC1 hz
  rw [geom_form d M z hd1 hM hz.2] at this
  simpa only [lawN_eq_geom d M hd1 hM] using this

end KeyfitzGeom

open KeyfitzGeom

/-- Grinstead–Snell Example 10.12 (PR-211), solving for the parameters. For the geometric offspring law
`p_k = b c^(k-1)` with mean `m = b/(1-c)^2 > 1` and extinction probability `d = (1-b-c)/(c(1-c))`
(Example 10.11), `c = (m-1)/(m-d)` and `b = m ((1-d)/(m-d))^2`. -/
@[kb "grinsteadsnell2006" "Example 10.12, p. 393"]
theorem geom_fit_parameters {b c m d : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c) (hc1 : c < 1)
    (hm : 1 < b / (1 - c) ^ 2) (hmdef : m = b / (1 - c) ^ 2) (hddef : d = (1 - b - c) / (c * (1 - c))) :
    c = (m - 1) / (m - d) ∧ b = m * ((1 - d) / (m - d)) ^ 2 :=
  lf_gf hb hbc hc0 hc1 hm hmdef hddef

/-- Grinstead–Snell Example 10.12 (PR-211), the numbers. With the Keyfitz values `m = 1.837`, `d = .324`,
the parameters `c = (m-1)/(m-d)` and `b = m((1-d)/(m-d))^2` satisfy `.5532 < c < .5533` and
`.3667 < b < .3668` (the book prints `b = .3666`, which is a rounding slip: `b = .36671...`; with the
book's rounded `c = .5533` one gets `b`-values consistent with Table 10.3), and `(1-c)^2 < b < 1-c`, as
required. Moreover this `(b, c)` really gives a geometric law with mean `1.837` and extinction probability
`.324`. -/
@[kb "grinsteadsnell2006" "Example 10.12, p. 393"]
theorem geom_fit_keyfitz :
    let m : ℝ := 1.837
    let d : ℝ := 0.324
    let c : ℝ := (m - 1) / (m - d)
    let b : ℝ := m * ((1 - d) / (m - d)) ^ 2
    (0.5532 < c ∧ c < 0.5533) ∧ (0.3667 < b ∧ b < 0.3668) ∧ ((1 - c) ^ 2 < b ∧ b < 1 - c) ∧
      IsOffspring (geomOffspring b c) ∧ b / (1 - c) ^ 2 = m ∧ (1 - b - c) / (c * (1 - c)) = d ∧
      extinctionProb (geomOffspring b c) = d := by
  intro m d c b
  have hc : 0.5532 < c ∧ c < 0.5533 := by simp only [c, m, d]; norm_num
  have hb : 0.3667 < b ∧ b < 0.3668 := by simp only [b, m, d]; norm_num
  have hmv : b / (1 - c) ^ 2 = m := by simp only [b, c, m, d]; norm_num
  have hdv : (1 - b - c) / (c * (1 - c)) = d := by simp only [b, c, m, d]; norm_num
  have hm1 : 1 < m := by simp only [m]; norm_num
  clear_value b c m d
  have hbc : b ≤ 1 - c := by linarith [hc.1, hc.2, hb.1, hb.2]
  have hlt : (1 - c) ^ 2 < b := by nlinarith [hc.1, hc.2, hb.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hc0 : 0 < c := by linarith [hc.1]
  have hc1 : c < 1 := by linarith [hc.2]
  refine ⟨hc, hb, ⟨hlt, by linarith [hbc]⟩, GeomBranching.isOffspring hb0 hbc hc0 hc1, hmv, hdv, ?_⟩
  have := (geomOffspring_extinction hb0 hbc hc0 hc1).2 (by rw [hmv]; exact hm1)
  rw [this.1, hdv]

/-- Grinstead–Snell Example 10.12 (PR-211), Table 10.3. With the book's rounded parameters `b = .3666`,
`c = .5533`, the geometric column of Table 10.3 for `p_1, ..., p_10` is reproduced to four places
(`.3666, .2028, .1122, .0621, .0344, .0190, .0105, .0058, .0032, .0018`), while
`p_0 = 1 - b/(1-c)` is `.1793` (the book prints `.1816`, an erratum: with it the table would sum to `1`
before the positive tail `k > 10` is added). -/
@[kb "grinsteadsnell2006" "Example 10.12, p. 393"]
theorem geom_fit_table :
    (0.1793 < geomOffspring 0.3666 0.5533 0 ∧ geomOffspring 0.3666 0.5533 0 < 0.1794) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ 10 →
      |geomOffspring 0.3666 0.5533 k - ([0.3666, 0.2028, 0.1122, 0.0621, 0.0344, 0.0190, 0.0105, 0.0058,
        0.0032, 0.0018] : List ℝ).getD (k - 1) 0| ≤ 0.00005 := by
  refine ⟨by simp only [geomOffspring]; norm_num, fun k hk1 hk2 => ?_⟩
  interval_cases k <;> simp only [geomOffspring] <;> norm_num [abs_le]


namespace KeyfitzGeom

theorem local_limit {d : ℝ} (hd1 : d < 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun M : ℝ => M * lawN d M ⌊t * M⌋₊) atTop (𝓝 ((1 - d) ^ 2 * Real.exp (-(t * (1 - d))))) := by
  have hpos : ∀ᶠ M : ℝ in atTop, 0 < M - d ∧ 0 < M ∧ 1 ≤ t * M ∧ 1 < M := by
    filter_upwards [eventually_gt_atTop (max (max d 0) 1), eventually_ge_atTop (1 / t)] with M h1 h2
    have h3 : d < M := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) h1
    have h4 : 0 < M := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) h1
    have h5 : 1 < M := lt_of_le_of_lt (le_max_right _ _) h1
    refine ⟨by linarith, h4, ?_, h5⟩
    rw [div_le_iff₀ ht] at h2; linarith
  -- M / (M - d) → 1
  have hq : Tendsto (fun M : ℝ => M / (M - d)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun M : ℝ => (1 - d / M)⁻¹) atTop (𝓝 ((1 - 0)⁻¹)) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)).inv₀ (by norm_num)
    norm_num at h0
    refine h0.congr' ?_
    filter_upwards [hpos] with M hM
    obtain ⟨h1, h2, _, _⟩ := hM
    field_simp
  have hA : Tendsto (fun M : ℝ => M * ((1 - d) / (M - d))) atTop (𝓝 (1 - d)) := by
    have := hq.const_mul (1 - d)
    simp only [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hpos] with M hM
    obtain ⟨h1, h2, _, _⟩ := hM
    field_simp
  -- M * log r → -(1-d), where r = (M-1)/(M-d) = 1 + g M
  have hlog : Tendsto (fun M : ℝ => M * Real.log (1 + (-(1 - d) / (M - d)))) atTop (𝓝 (-(1 - d))) := by
    refine Real.tendsto_mul_log_one_add_of_tendsto ?_
    have := hq.const_mul (-(1 - d))
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hpos] with M hM
    obtain ⟨h1, h2, _, _⟩ := hM
    field_simp
  -- k / M → t, k = ⌊tM⌋₊ - 1
  have hk : Tendsto (fun M : ℝ => ((⌊t * M⌋₊ : ℝ) - 1) / M) atTop (𝓝 t) := by
    have hlow : Tendsto (fun M : ℝ => t - 2 / M) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop tendsto_id)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hpos] with M hM
      obtain ⟨_, h2, _, _⟩ := hM
      have := Nat.lt_floor_add_one (t * M)
      rw [le_div_iff₀ h2, sub_mul, div_mul_cancel₀ _ h2.ne']
      linarith
    · filter_upwards [hpos] with M hM
      obtain ⟨_, h2, _, _⟩ := hM
      have := Nat.floor_le (mul_nonneg ht.le h2.le)
      rw [div_le_iff₀ h2]
      linarith
  have hexp : Tendsto (fun M : ℝ => Real.exp (((⌊t * M⌋₊ : ℝ) - 1) * Real.log (1 + (-(1 - d) / (M - d)))))
      atTop (𝓝 (Real.exp (t * (-(1 - d))))) := by
    refine (Real.continuous_exp.tendsto _).comp ?_
    refine (hk.mul hlog).congr' ?_
    filter_upwards [hpos] with M hM
    obtain ⟨_, h2, _, _⟩ := hM
    field_simp
  have hfin := (hA.pow 2).mul hexp
  rw [show -(t * (1 - d)) = t * (-(1 - d)) by ring]
  refine hfin.congr' ?_
  filter_upwards [hpos] with M hM
  obtain ⟨h1, h2, h3, h4⟩ := hM
  have hfl : 1 ≤ ⌊t * M⌋₊ := Nat.le_floor (by simpa using h3)
  have hr : 0 < 1 + (-(1 - d) / (M - d)) := by
    have : 1 + (-(1 - d) / (M - d)) = (M - 1) / (M - d) := by field_simp; ring
    rw [this]
    exact div_pos (by linarith) h1
  obtain ⟨k, hk⟩ : ∃ k, ⌊t * M⌋₊ = k + 1 := ⟨⌊t * M⌋₊ - 1, by omega⟩
  have hrr : 1 + (-(1 - d) / (M - d)) = (M - 1) / (M - d) := by field_simp; ring
  have hexp' : Real.exp (((⌊t * M⌋₊ : ℝ) - 1) * Real.log (1 + (-(1 - d) / (M - d)))) =
      ((M - 1) / (M - d)) ^ k := by
    rw [hk, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.exp_nat_mul, Real.exp_log hr, hrr]
  rw [hexp', hk]
  simp only [lawN, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  ring

end KeyfitzGeom

open KeyfitzGeom

/-- Grinstead–Snell Example 10.13 (PR-212), the law of `Z_n`. Erratum: the book writes "`m < 1`", but the
formulas need `m > 1` (for `m ≤ 1` one has `d = 1` and `m^n → 0` or `= 1`, and the extinction formulas
degenerate). For the geometric offspring law `p_k = b c^(k-1)` with `m = b/(1-c)^2 > 1` and
`d = (1-b-c)/(c(1-c))`, put `M = m^n`. The `n`-th iterate `h_n` of the offspring generating function (the
generating function of `Z_n`) is the linear fractional map `(d M (z-1) - (z-d))/(M (z-1) - (z-d))` on `[0,1]`
(so `(h_n(z)-d)/(h_n(z)-1) = m^(-n) (z-d)/(z-1)`), and it is the generating function of the law
`P(Z_n = 0) = d (M-1)/(M-d)`, `P(Z_n = j) = M ((1-d)/(M-d))^2 ((M-1)/(M-d))^(j-1)` (`j ≥ 1`), a probability
law on `ℕ`; also `P(Z_n = 0) = d_n`, the extinction probability by generation `n`. -/
@[kb "grinsteadsnell2006" "Example 10.13, p. 395"]
theorem geom_generation_law {b c m d : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c) (hc1 : c < 1)
    (hm : 1 < b / (1 - c) ^ 2) (hmdef : m = b / (1 - c) ^ 2) (hddef : d = (1 - b - c) / (c * (1 - c)))
    (n : ℕ) :
    (∀ z ∈ Icc (0 : ℝ) 1, (offspringGF (geomOffspring b c))^[n] z =
        (d * m ^ n * (z - 1) - (z - d)) / (m ^ n * (z - 1) - (z - d))) ∧
      IsOffspring (lawN d (m ^ n)) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, HasSum (fun j : ℕ => lawN d (m ^ n) j * z ^ j)
        ((offspringGF (geomOffspring b c))^[n] z)) ∧
      extinctProb (geomOffspring b c) n = d * (m ^ n - 1) / (m ^ n - d) := by
  have hp := GeomBranching.isOffspring hb hbc hc0 hc1
  have hd1 : d < 1 := by rw [hddef]; exact (geomOffspring_d_lt_one_iff hc0 hc1).2 hm
  have h1c : 0 < 1 - c := by linarith
  have hd0 : 0 ≤ d := by
    rw [hddef]; exact div_nonneg (by linarith) (mul_nonneg hc0.le h1c.le)
  have hm1 : 1 ≤ m := by rw [hmdef]; exact hm.le
  have hM : 1 ≤ m ^ n := one_le_pow₀ hm1
  have hit := fun z (hz : z ∈ Icc (0 : ℝ) 1) => iterate_eq_lf hb hbc hc0 hc1 hm hmdef hddef n hz
  have hsum : ∀ z ∈ Icc (0 : ℝ) 1, HasSum (fun j : ℕ => lawN d (m ^ n) j * z ^ j)
      ((offspringGF (geomOffspring b c))^[n] z) := fun z hz => by
    rw [hit z hz]; exact hasSum_lawN hd1 hM hz
  refine ⟨fun z hz => hit z hz, ⟨lawN_nonneg hd0 hd1 hM, ?_⟩, hsum, ?_⟩
  · have h1 := hsum 1 ⟨zero_le_one, le_rfl⟩
    rw [Function.iterate_fixed (Branching.gf_one hp)] at h1
    simpa using h1
  · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have : extinctProb (geomOffspring b c) n = lf d (m ^ n) 0 := hit 0 h0
    rw [this]
    have hMd : m ^ n - d ≠ 0 := by intro h; linarith
    unfold lf
    rw [div_eq_div_iff (by intro h; apply hMd; linarith) hMd]
    ring

/-- Grinstead–Snell Example 10.13 (PR-212), `P(Z_n = 0) → d`. In the setting of `geom_generation_law`,
`P(Z_n = 0) = d (m^n-1)/(m^n-d)` converges to the extinction probability `d = (1-b-c)/(c(1-c))`. -/
@[kb "grinsteadsnell2006" "Example 10.13, p. 395"]
theorem geom_generation_zero_tendsto {b c m d : ℝ} (hb : 0 < b) (hbc : b ≤ 1 - c) (hc0 : 0 < c)
    (hc1 : c < 1) (hm : 1 < b / (1 - c) ^ 2) (hmdef : m = b / (1 - c) ^ 2)
    (hddef : d = (1 - b - c) / (c * (1 - c))) :
    Tendsto (fun n : ℕ => lawN d (m ^ n) 0) atTop (𝓝 d) := by
  have hp := GeomBranching.isOffspring hb hbc hc0 hc1
  have hdv := ((geomOffspring_extinction hb hbc hc0 hc1).2 (by exact hm)).1
  obtain ⟨_, hlim, _⟩ := extinction_smallest_root hp
  rw [hdv, ← hddef] at hlim
  refine hlim.congr fun n => ?_
  have := (geom_generation_law hb hbc hc0 hc1 hm hmdef hddef n).2.2.2
  rw [this]; simp [lawN]

/-- Grinstead–Snell Example 10.13 (PR-212), the local limit. In the setting of `geom_generation_law`
(`m > 1`; the book's "`m < 1`" is an erratum), for every `t > 0` and `j_n = ⌊t m^n⌋`,
`m^n P(Z_n = j_n) → (1-d)^2 e^{-t(1-d)}`, where `P(Z_n = j)` is the book's law `lawN d (m^n) j`
(identified with the law of `Z_n` by `geom_generation_law`). -/
@[kb "grinsteadsnell2006" "Example 10.13, p. 395"]
theorem geom_generation_local_limit {b c m d : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hm : 1 < b / (1 - c) ^ 2) (hmdef : m = b / (1 - c) ^ 2)
    (hddef : d = (1 - b - c) / (c * (1 - c))) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => m ^ n * lawN d (m ^ n) ⌊t * m ^ n⌋₊) atTop
      (𝓝 ((1 - d) ^ 2 * Real.exp (-(t * (1 - d))))) := by
  have hd1 : d < 1 := by rw [hddef]; exact (geomOffspring_d_lt_one_iff hc0 hc1).2 hm
  have hm' : 1 < m := by rw [hmdef]; exact hm
  exact (local_limit hd1 ht).comp (tendsto_pow_atTop_atTop_of_one_lt hm')

end UndergradKB.Probability
