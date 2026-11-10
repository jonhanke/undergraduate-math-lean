import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import UndergradKB.Common.Attr

/-! # Calculus: Riemann sums and numerical integration

OpenStax Calculus 1:§5.1-5.2 and 2:§3.6: the regular partition, left/right/midpoint/tagged sums, convergence of
Riemann sums of continuous functions, monotone upper and lower sums, closed forms of power sums, and the midpoint and
trapezoidal error bounds (the trapezoidal sum is Mathlib's `trapezoidal_integral`). -/

namespace UndergradKB.Calculus

open Set Finset intervalIntegral MeasureTheory Filter Topology

/-- OpenStax Calculus 1:§5.1 (CA-181). Point `i` of the regular partition of `[a,b]` into `n` equal pieces: `a + i (b-a)/n`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (partition, regular partition), p. 450"]
noncomputable def regularPartition (a b : ℝ) (n i : ℕ) : ℝ := a + i * ((b - a) / n)

/-- OpenStax Calculus 1:§5.1 (CA-182). Left-endpoint sum `L_n`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (left-endpoint approximation), p. 450"]
noncomputable def leftSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((b - a) / n) * ∑ i ∈ range n, f (regularPartition a b n i)

/-- OpenStax Calculus 1:§5.1 (CA-182). Right-endpoint sum `R_n`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (right-endpoint approximation), p. 451"]
noncomputable def rightSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((b - a) / n) * ∑ i ∈ range n, f (regularPartition a b n (i + 1))

/-- OpenStax Calculus 2:§3.6 (CA-234). Midpoint sum `M_n`: `f` at the midpoints of the `n` equal subintervals, times the width. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.3, p. 285"]
noncomputable def midSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  ((b - a) / n) * ∑ i ∈ range n, f (a + (i + 1 / 2) * ((b - a) / n))

/-- OpenStax Calculus 1:§5.1 (CA-183). Riemann sum on the regular partition with tags `c i`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (Riemann sum), p. 456"]
noncomputable def taggedSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (c : ℕ → ℝ) : ℝ :=
  ((b - a) / n) * ∑ i ∈ range n, f (c i)

theorem regularPartition_zero (a b : ℝ) (n : ℕ) : regularPartition a b n 0 = a := by
  simp [regularPartition]

theorem regularPartition_last (a b : ℝ) {n : ℕ} (hn : 0 < n) : regularPartition a b n n = b := by
  have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [regularPartition]; field_simp; ring

theorem regularPartition_succ_sub (a b : ℝ) (n i : ℕ) :
    regularPartition a b n (i + 1) - regularPartition a b n i = (b - a) / n := by
  simp [regularPartition]; ring

theorem regularPartition_mem {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 0 < n) {i : ℕ} (hi : i ≤ n) :
    regularPartition a b n i ∈ Icc a b := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hi' : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hd : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  constructor
  · simp only [regularPartition]
    have : 0 ≤ (i:ℝ) * ((b - a) / n) := by positivity
    linarith
  · have : (i:ℝ) * ((b - a) / n) ≤ n * ((b - a) / n) :=
      mul_le_mul_of_nonneg_right hi' hd
    have h2 : (n:ℝ) * ((b - a) / n) = b - a := by field_simp
    simp only [regularPartition]; linarith

theorem regularPartition_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Monotone (regularPartition a b n) := by
  intro i j hij
  have : (i:ℝ) ≤ j := by exact_mod_cast hij
  have h0 : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  simp only [regularPartition]; nlinarith

theorem integrableOn_part {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    {n : ℕ} (hn : 0 < n) (i : ℕ) (hi : i < n) :
    IntervalIntegrable f volume (regularPartition a b n i) (regularPartition a b n (i + 1)) := by
  refine hf.mono_set ?_
  rw [uIcc_of_le (regularPartition_mono hab n (Nat.le_succ i)), uIcc_of_le hab]
  exact Icc_subset_Icc (regularPartition_mem hab hn hi.le).1 (regularPartition_mem hab hn hi).2

theorem integral_eq_sum_part {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    {n : ℕ} (hn : 0 < n) :
    ∫ x in a..b, f x = ∑ i ∈ range n, ∫ x in regularPartition a b n i..regularPartition a b n (i + 1), f x := by
  have := sum_integral_adjacent_intervals (f := f) (μ := volume) (a := regularPartition a b n) (n := n)
    (fun k hk => integrableOn_part hab hf hn k hk)
  rw [this, regularPartition_zero, regularPartition_last a b hn]

/-- Quantitative form of the Riemann-sum convergence (CA-183, CA-186): if `f` varies by at most `ε` on pieces of width `(b-a)/n`, every tagged sum is within `(b-a) ε` of the integral. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (definite integral), p. 464"]
theorem taggedSum_error_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| ≤ (b - a) / n → |f x - f y| ≤ ε)
    {c : ℕ → ℝ}
    (hc : ∀ i < n, c i ∈ Icc (regularPartition a b n i) (regularPartition a b n (i + 1))) :
    |taggedSum f a b n c - ∫ x in a..b, f x| ≤ (b - a) * ε := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  have hfi : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hf.integrableOn_Icc
  rw [integral_eq_sum_part hab hfi hn, taggedSum, mul_sum, ← sum_sub_distrib]
  have key : ∀ i ∈ range n, |(b - a) / n * f (c i) -
      ∫ x in regularPartition a b n i..regularPartition a b n (i + 1), f x| ≤ (b - a) / n * ε := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hle := regularPartition_mono hab n (Nat.le_succ i)
    have hI := integrableOn_part hab hfi hn i hi
    have e1 : (b - a) / n * f (c i) =
        ∫ x in regularPartition a b n i..regularPartition a b n (i + 1), f (c i) := by
      rw [intervalIntegral.integral_const, regularPartition_succ_sub]; simp
    rw [e1, ← integral_sub intervalIntegrable_const hI]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := regularPartition a b n i)
      (b := regularPartition a b n (i + 1)) (C := ε) (f := fun x => f (c i) - f x) (by
        intro x hx
        rw [uIoc_of_le hle] at hx
        have hci := hc i hi
        have hmi := regularPartition_mem hab hn hi.le
        have hmi1 := regularPartition_mem hab hn (Nat.succ_le_of_lt hi)
        have := hε (c i) ⟨hmi.1.trans hci.1, hci.2.trans hmi1.2⟩ x
          ⟨hmi.1.trans hx.1.le, hx.2.trans hmi1.2⟩ (by
            have h1 := regularPartition_succ_sub a b n i
            rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2, hci.1, hci.2])
        simpa [Real.norm_eq_abs] using this)
    rw [regularPartition_succ_sub, abs_of_nonneg hd] at this
    simp only [Real.norm_eq_abs] at this
    linarith
  calc _ ≤ ∑ i ∈ range n, |(b - a) / n * f (c i) -
        ∫ x in regularPartition a b n i..regularPartition a b n (i + 1), f x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, (b - a) / n * ε := sum_le_sum key
    _ = (b - a) * ε := by simp; field_simp

/-- OpenStax Calculus 1:§5.2 (CA-184, CA-186). Every sequence of Riemann sums of a continuous `f` on regular partitions with `n` pieces tends to `∫_a^b f`. -/
@[kb "openstaxcalculus2016" "1:§5.2 Definition (definite integral), p. 464"]
theorem tendsto_taggedSum {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (c : ℕ → ℕ → ℝ)
    (hc : ∀ n, ∀ i < n, c n i ∈ Icc (regularPartition a b n i) (regularPartition a b n (i + 1))) :
    Tendsto (fun n => taggedSum f a b n (c n)) atTop (𝓝 (∫ x in a..b, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := (isCompact_Icc.uniformContinuousOn_of_continuous hf)
  rw [Metric.uniformContinuousOn_iff_le] at huc
  have hε' : 0 < ε / (2 * (b - a + 1)) := by
    have : 0 < b - a + 1 := by linarith
    positivity
  obtain ⟨δ, hδ, hδ'⟩ := huc _ hε'
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnN : (N:ℝ) < n := by exact_mod_cast (by omega : N < n)
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  have hlt : (b - a) / n ≤ δ := by
    rw [div_le_iff₀ hn']
    have := (div_lt_iff₀ hδ).1 hN
    nlinarith
  have := taggedSum_error_le hab hf hn0 (ε := ε / (2 * (b - a + 1))) (fun x hx y hy hxy => by
    simpa [Real.dist_eq] using hδ' x hx y hy (by simpa [Real.dist_eq] using hxy.trans hlt)) (hc n)
  rw [Real.dist_eq]
  refine this.trans_lt ?_
  have h1 : 0 < b - a + 1 := by linarith
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

theorem leftSum_eq_taggedSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    leftSum f a b n = taggedSum f a b n (regularPartition a b n) := rfl

theorem rightSum_eq_taggedSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    rightSum f a b n = taggedSum f a b n (fun i => regularPartition a b n (i + 1)) := rfl

theorem midSum_eq_taggedSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    midSum f a b n = taggedSum f a b n (fun i => a + (i + 1 / 2) * ((b - a) / n)) := rfl

/-- OpenStax Calculus 1:§5.1 (CA-184). `L_n → ∫_a^b f` for continuous `f`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (area under a curve), p. 456"]
theorem tendsto_leftSum {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => leftSum f a b n) atTop (𝓝 (∫ x in a..b, f x)) := by
  refine tendsto_taggedSum hab hf (fun n => regularPartition a b n) ?_
  intro n i hi
  have := regularPartition_mono hab n (Nat.le_succ i)
  exact ⟨le_rfl, this⟩

/-- OpenStax Calculus 1:§5.1 (CA-184). `R_n → ∫_a^b f` for continuous `f`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (area under a curve), p. 456"]
theorem tendsto_rightSum {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => rightSum f a b n) atTop (𝓝 (∫ x in a..b, f x)) := by
  refine tendsto_taggedSum hab hf (fun n i => regularPartition a b n (i + 1)) ?_
  intro n i hi
  have := regularPartition_mono hab n (Nat.le_succ i)
  exact ⟨this, le_rfl⟩

/-- OpenStax Calculus 2:Theorem 3.3 (CA-234). `M_n → ∫_a^b f` for continuous `f`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.3, p. 285"]
theorem tendsto_midSum {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => midSum f a b n) atTop (𝓝 (∫ x in a..b, f x)) := by
  refine tendsto_taggedSum hab hf (fun n i => a + (i + 1 / 2) * ((b - a) / n)) ?_
  intro n i hi
  have h := regularPartition_succ_sub a b n i
  have hd : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  simp only [regularPartition] at h ⊢
  constructor <;> nlinarith

/-- OpenStax Calculus 2:§3.6 (CA-235). `T_n = (L_n + R_n)/2`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.4, p. 287"]
theorem trapezoidal_integral_eq_avg (f : ℝ → ℝ) (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    trapezoidal_integral f n a b = (leftSum f a b n + rightSum f a b n) / 2 := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := sum_trapezoidal_integral_adjacent_intervals (f := f) (a := a) (h := (b - a) / n) hn
  have hb : a + n * ((b - a) / n) = b := by field_simp; ring
  rw [hb] at h
  rw [← h, leftSum, rightSum, ← mul_add, ← sum_add_distrib, mul_sum, Finset.sum_div]
  refine sum_congr rfl fun i _ => ?_
  simp only [trapezoidal_integral_one, regularPartition]
  push_cast; ring

/-- OpenStax Calculus 2:Theorem 3.4 (CA-235). The trapezoidal sums (Mathlib's `trapezoidal_integral`) tend to `∫_a^b f` for continuous `f`. -/
@[kb "openstaxcalculus2016" "2:Theorem 3.4, p. 287"]
theorem tendsto_trapezoid {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n => trapezoidal_integral f n a b) atTop (𝓝 (∫ x in a..b, f x)) := by
  have := ((tendsto_leftSum hab hf).add (tendsto_rightSum hab hf)).div_const 2
  rw [show ((∫ x in a..b, f x) + ∫ x in a..b, f x) / 2 = ∫ x in a..b, f x by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (trapezoidal_integral_eq_avg f a b hn).symm


/-- OpenStax Calculus 1:§5.1 (CA-185). For increasing `f`, `L_n` is a lower sum: `L_n ≤ ∫`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (upper sum, lower sum), p. 457"]
theorem leftSum_le_integral_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) {n : ℕ} (hn : 0 < n) :
    leftSum f a b n ≤ ∫ x in a..b, f x := by
  have hfi : IntervalIntegrable f volume a b := by
    exact MonotoneOn.intervalIntegrable (a := a) (b := b) (by rwa [uIcc_of_le hab])
  rw [integral_eq_sum_part hab hfi hn, leftSum, mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hle := regularPartition_mono hab n (Nat.le_succ i)
  have hmi := regularPartition_mem hab hn hi.le
  have hmi1 := regularPartition_mem hab hn (Nat.succ_le_of_lt hi)
  have h := intervalIntegral.integral_mono_on hle (intervalIntegrable_const (c := f (regularPartition a b n i)))
    (integrableOn_part hab hfi hn i hi) (fun x hx => hf hmi (⟨hmi.1.trans hx.1, hx.2.trans hmi1.2⟩) hx.1)
  rw [intervalIntegral.integral_const, regularPartition_succ_sub] at h
  simpa using h

/-- OpenStax Calculus 1:§5.1 (CA-185). For increasing `f`, `R_n` is an upper sum: `∫ ≤ R_n`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (upper sum, lower sum), p. 457"]
theorem integral_le_rightSum_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) {n : ℕ} (hn : 0 < n) :
    ∫ x in a..b, f x ≤ rightSum f a b n := by
  have hfi : IntervalIntegrable f volume a b := by
    exact MonotoneOn.intervalIntegrable (a := a) (b := b) (by rwa [uIcc_of_le hab])
  rw [integral_eq_sum_part hab hfi hn, rightSum, mul_sum]
  refine sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hle := regularPartition_mono hab n (Nat.le_succ i)
  have hmi := regularPartition_mem hab hn hi.le
  have hmi1 := regularPartition_mem hab hn (Nat.succ_le_of_lt hi)
  have h := intervalIntegral.integral_mono_on hle (integrableOn_part hab hfi hn i hi)
    (intervalIntegrable_const (c := f (regularPartition a b n (i + 1))))
    (fun x hx => hf (⟨hmi.1.trans hx.1, hx.2.trans hmi1.2⟩) hmi1 hx.2)
  rw [intervalIntegral.integral_const, regularPartition_succ_sub] at h
  simpa using h

theorem leftSum_neg (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    leftSum (fun x => -f x) a b n = -leftSum f a b n := by
  simp [leftSum, Finset.sum_neg_distrib]

theorem rightSum_neg (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    rightSum (fun x => -f x) a b n = -rightSum f a b n := by
  simp [rightSum, Finset.sum_neg_distrib]

/-- OpenStax Calculus 1:§5.1 (CA-185). For decreasing `f`, `R_n` is a lower sum. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (upper sum, lower sum), p. 457"]
theorem rightSum_le_integral_of_antitoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) {n : ℕ} (hn : 0 < n) :
    rightSum f a b n ≤ ∫ x in a..b, f x := by
  have := integral_le_rightSum_of_monotoneOn (f := fun x => -f x) hab hf.neg hn
  rw [rightSum_neg, intervalIntegral.integral_neg] at this
  linarith

/-- OpenStax Calculus 1:§5.1 (CA-185). For decreasing `f`, `L_n` is an upper sum. -/
@[kb "openstaxcalculus2016" "1:§5.1 Definition (upper sum, lower sum), p. 457"]
theorem integral_le_leftSum_of_antitoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) {n : ℕ} (hn : 0 < n) :
    ∫ x in a..b, f x ≤ leftSum f a b n := by
  have := leftSum_le_integral_of_monotoneOn (f := fun x => -f x) hab hf.neg hn
  rw [leftSum_neg, intervalIntegral.integral_neg] at this
  linarith

/-- OpenStax Calculus 1:§5.1 (CA-180). `1 + ... + n = n(n+1)/2`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (sums and powers of integers), p. 448"]
theorem sum_Icc_id (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, (i : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- OpenStax Calculus 1:§5.1 (CA-180). `1² + ... + n² = n(n+1)(2n+1)/6`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (sums and powers of integers), p. 448"]
theorem sum_Icc_sq (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- OpenStax Calculus 1:§5.1 (CA-180). `1³ + ... + n³ = (n(n+1)/2)²`. -/
@[kb "openstaxcalculus2016" "1:§5.1 Rule (sums and powers of integers), p. 448"]
theorem sum_Icc_cube (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, (i : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- A function with a global derivative `φ'` vanishing at `0`, with `|φ' t| ≤ C t^k` on `[0,T]`,
satisfies `|φ t| ≤ C/(k+1) t^(k+1)` there. -/
theorem abs_le_of_abs_deriv_le {φ φ' : ℝ → ℝ} {T C : ℝ} {k : ℕ}
    (h : ∀ x, HasDerivAt φ (φ' x) x) (h0 : φ 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, |φ' t| ≤ C * t ^ k) :
    ∀ t ∈ Icc 0 T, |φ t| ≤ C / (k + 1) * t ^ (k + 1) := by
  intro t ht
  have hB (x : ℝ) : HasDerivAt (fun y : ℝ ↦ C / (k + 1) * y ^ (k + 1)) (C * x ^ k) x := by
    have := (hasDerivAt_pow (k + 1) x).const_mul (C / (k + 1))
    convert this using 1
    push_cast
    field_simp
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ) (a := 0) (b := t)
    (fun x _ => (h x).continuousAt.continuousWithinAt)
    (fun x _ => (h x).hasDerivWithinAt) (by simp [h0]) hB
    (fun x hx => by simpa [Real.norm_eq_abs] using hb x ⟨hx.1, hx.2.le.trans ht.2⟩) (x := t) ⟨ht.1, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-- Mean value inequality for a globally differentiable function. -/
theorem abs_sub_le_of_abs_deriv_le {g g' : ℝ → ℝ} {u v M : ℝ} (hg : ∀ x, HasDerivAt g (g' x) x)
    (hb : ∀ x ∈ Icc u v, |g' x| ≤ M) {x y : ℝ} (hx : x ∈ Icc u v) (hy : y ∈ Icc u v) :
    |g y - g x| ≤ M * |y - x| := by
  have := (convex_Icc u v).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by simpa [Real.norm_eq_abs] using hb x hx) hx hy
  simpa [Real.norm_eq_abs] using this

theorem hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) {k : ℕ} (hk : k < n)
    (x : ℝ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have := ((hf.differentiable_iteratedDeriv k (by exact_mod_cast hk)).differentiableAt (x := x)).hasDerivAt
  rwa [← iteratedDeriv_succ] at this

theorem hasDerivAt_integral_primitive {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun u => ∫ y in (0:ℝ)..u, f y) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hasDerivAt_shift_add {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (c t : ℝ) :
    HasDerivAt (fun t => g (c + t)) (g' (c + t)) t := by
  exact ((hg (c + t)).comp t ((hasDerivAt_id t).const_add c)).congr_deriv (by simp)

theorem hasDerivAt_shift_sub {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (c t : ℝ) :
    HasDerivAt (fun t => g (c - t)) (-g' (c - t)) t := by
  exact ((hg (c - t)).comp t ((hasDerivAt_id t).const_sub c)).congr_deriv (by simp)

theorem sum_panel_error_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {n : ℕ} (hn : 0 < n) (s : ℕ → ℝ) {B : ℝ}
    (h : ∀ i < n, |s i - ∫ x in regularPartition a b n i..regularPartition a b n (i + 1), f x| ≤ B) :
    |∑ i ∈ range n, s i - ∫ x in a..b, f x| ≤ n * B := by
  have hfi : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]; exact hf.integrableOn_Icc
  rw [integral_eq_sum_part hab hfi hn, ← sum_sub_distrib]
  calc _ ≤ ∑ i ∈ range n, |s i - ∫ x in regularPartition a b n i..regularPartition a b n (i + 1), f x| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, B := sum_le_sum fun i hi => h i (Finset.mem_range.1 hi)
    _ = n * B := by simp

/-- One-panel midpoint error. -/
theorem midpoint_panel_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {c h M : ℝ} (hh : 0 ≤ h)
    (hM : ∀ x ∈ Icc (c - h) (c + h), |iteratedDeriv 2 f x| ≤ M) :
    |(∫ x in c - h..c + h, f x) - 2 * h * f c| ≤ M * h ^ 3 / 3 := by
  have hc : Continuous f := hf.continuous
  have f0 : ∀ x, HasDerivAt f (iteratedDeriv 1 f x) x := by
    intro x
    have := hasDerivAt_iteratedDeriv (n := 2) hf (k := 0) (by norm_num) x
    rwa [iteratedDeriv_zero] at this
  have f1 : ∀ x, HasDerivAt (iteratedDeriv 1 f) (iteratedDeriv 2 f x) x :=
    hasDerivAt_iteratedDeriv (n := 2) hf (k := 1) (by norm_num)
  set F : ℝ → ℝ := fun u => ∫ y in (0:ℝ)..u, f y with hFdef
  have hF : ∀ x, HasDerivAt F (f x) x := hasDerivAt_integral_primitive hc
  have hψ : ∀ t, HasDerivAt (fun t => f (c + t) + f (c - t) - 2 * f c)
      (iteratedDeriv 1 f (c + t) - iteratedDeriv 1 f (c - t)) t := by
    intro t
    have := ((hasDerivAt_shift_add f0 c t).add (hasDerivAt_shift_sub f0 c t)).sub_const (2 * f c)
    exact this.congr_deriv (by ring)
  have hφ : ∀ t, HasDerivAt (fun t => F (c + t) - F (c - t) - 2 * t * f c)
      (f (c + t) + f (c - t) - 2 * f c) t := by
    intro t
    have := ((hasDerivAt_shift_add hF c t).sub (hasDerivAt_shift_sub hF c t)).sub
      (((hasDerivAt_id t).const_mul 2).mul_const (f c))
    exact this.congr_deriv (by ring)
  have b2 : ∀ t ∈ Icc 0 h, |iteratedDeriv 1 f (c + t) - iteratedDeriv 1 f (c - t)| ≤ 2 * M * t ^ 1 := by
    intro t ht
    have := abs_sub_le_of_abs_deriv_le f1 hM (x := c - t) (y := c + t)
      ⟨by linarith [ht.2], by linarith [ht.1]⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e : |c + t - (c - t)| = 2 * t := by rw [abs_of_nonneg (by linarith [ht.1])]; ring
    rw [e] at this
    calc _ ≤ M * (2 * t) := this
      _ = 2 * M * t ^ 1 := by ring
  have b1 := abs_le_of_abs_deriv_le hψ (by simp; ring) b2
  have b1' : ∀ t ∈ Icc 0 h, |f (c + t) + f (c - t) - 2 * f c| ≤ M * t ^ 2 := by
    intro t ht
    have := b1 t ht
    norm_num at this
    simpa [pow_two] using this
  have b0 := abs_le_of_abs_deriv_le hφ (by simp) b1' h ⟨hh, le_rfl⟩
  have hint : ∫ x in c - h..c + h, f x = F (c + h) - F (c - h) :=
    integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hc.intervalIntegrable _ _)
  rw [hint]
  norm_num at b0
  calc _ ≤ M / 3 * h ^ 3 := by simpa using b0
    _ = _ := by ring


/-- OpenStax Calculus 2:Theorem 3.5 (CA-237). If `|f''| ≤ M` on `[a,b]`, the midpoint error is at most `M (b-a)³ / (24 n²)`. (`f` is `C²` on all of `ℝ`.) -/
@[kb "openstaxcalculus2016" "2:Theorem 3.5, p. 289"]
theorem midpoint_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ} (hab : a ≤ b) {n : ℕ}
    (hn : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ M) :
    |midSum f a b n - ∫ x in a..b, f x| ≤ M * (b - a) ^ 3 / (24 * n ^ 2) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 ≤ (b - a) / n := by have := sub_nonneg.2 hab; positivity
  have key := sum_panel_error_le hab hf.continuous.continuousOn hn
    (fun i => (b - a) / n * f (a + (i + 1 / 2) * ((b - a) / n))) (B := M * (((b - a) / n) / 2) ^ 3 / 3) (by
      intro i hi
      have hmi := regularPartition_mem hab hn hi.le
      have hmi1 := regularPartition_mem hab hn (Nat.succ_le_of_lt hi)
      have e1 : regularPartition a b n i = (a + (i + 1 / 2) * ((b - a) / n)) - ((b - a) / n) / 2 := by
        simp only [regularPartition]; ring
      have e2 : regularPartition a b n (i + 1) = (a + (i + 1 / 2) * ((b - a) / n)) + ((b - a) / n) / 2 := by
        simp only [regularPartition]; push_cast; ring
      rw [e1, e2]
      have := midpoint_panel_error_le hf (c := a + (i + 1 / 2) * ((b - a) / n)) (h := ((b - a) / n) / 2)
        (M := M) (by positivity) (fun x hx => hM x ⟨by rw [e1] at hmi; exact hmi.1.trans hx.1,
          by rw [e2] at hmi1; exact hx.2.trans hmi1.2⟩)
      rw [abs_sub_comm]
      refine le_trans (le_of_eq ?_) this
      congr 2; ring)
  have e : midSum f a b n = ∑ i ∈ range n, (b - a) / n * f (a + (i + 1 / 2) * ((b - a) / n)) := by
    rw [midSum, mul_sum]
  rw [e]
  refine key.trans (le_of_eq ?_)
  field_simp
  ring


/-- OpenStax Calculus 2:Theorem 3.5 (CA-237). If `|f''| ≤ M` on `[a,b]`, the trapezoidal error is at most `M (b-a)³ / (12 n²)`; book form of Mathlib's `trapezoidal_error_le_of_c2`. (`f` is `C²` on all of `ℝ`.) -/
@[kb "openstaxcalculus2016" "2:Theorem 3.5, p. 289"]
theorem trapezoid_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ} (hab : a ≤ b) {n : ℕ}
    (hn : 0 < n) (hM : ∀ x ∈ Icc a b, |iteratedDeriv 2 f x| ≤ M) :
    |trapezoidal_integral f n a b - ∫ x in a..b, f x| ≤ M * (b - a) ^ 3 / (12 * n ^ 2) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  have hU : UniqueDiffOn ℝ (uIcc a b) := uniqueDiffOn_uIcc hlt.ne
  have := trapezoidal_error_le_of_c2 (f := f) (a := a) (b := b) hf.contDiffOn (ζ := M) (by
    intro x
    by_cases hx : x ∈ uIcc a b
    · rw [iteratedDerivWithin_eq_iteratedDeriv hU hf.contDiffAt hx]
      exact hM x (by simpa [uIcc_of_le hab] using hx)
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
        (by rwa [Set.uIcc, isClosed_Icc.closure_eq]), abs_zero]
      exact hM0) hn
  rw [abs_of_pos (sub_pos.2 hlt)] at this
  unfold trapezoidal_error at this
  rwa [mul_comm M] 

end UndergradKB.Calculus
