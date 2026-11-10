import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import UndergradKB.Common.Attr
import UndergradKB.Trigonometry.PolarCurves

/-! # Rose curves and the Archimedes spiral (OpenStax §10.4)

The plane is `ℂ` and `polarPoint r θ` is the point with polar coordinates `(r, θ)` (see `PolarCurves`).

* `roseCos a n`, `roseSin a n`: the rose curves `r = a cos nθ`, `r = a sin nθ` (`n ≥ 1` a natural number);
* `roseCos_petal_length`, `roseSin_petal_length`: every point of the curve lies within `|a|` of the pole and the
  distance `|a|` is attained, so the petals have length `|a|`;
* `roseCosTips a n`, `roseSinTips a n`: the points of the curve at maximal distance `|a|` from the pole. A petal
  is counted by its tip, the farthest point of the petal, so the number of petals is the number of tips;
* `roseCos_petal_count`, `roseSin_petal_count`: for `a ≠ 0` there are `n` petals if `n` is odd and `2n` petals
  if `n` is even;
* `archimedesSpiral`: the spiral `r = θ`, `θ ≥ 0`; `archimedesSpiral_norm`, `archimedesSpiral_turn` (the distance
  from the pole is `θ`, so one turn adds `2π`) and `archimedesSpiral_no_symmetry`.
-/

namespace UndergradKB.Trigonometry

open Complex ComplexConjugate Set

lemma polarPoint_eq_mul_exp (r θ : ℝ) : polarPoint r θ = r * exp (θ * I) := by
  rw [polarPoint, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

lemma norm_polarPoint (r θ : ℝ) : ‖polarPoint r θ‖ = |r| := by
  rw [polarPoint_eq_mul_exp, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

lemma polarPoint_add (r θ α : ℝ) : polarPoint r (θ + α) = exp (α * I) * polarPoint r θ := by
  rw [polarPoint_eq_mul_exp, polarPoint_eq_mul_exp, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- The rose `r = a cos nθ`. -/
def roseCos (a : ℝ) (n : ℕ) : Set ℂ := polarGraph (fun r θ => r = a * Real.cos (n * θ))

/-- The rose `r = a sin nθ`. -/
def roseSin (a : ℝ) (n : ℕ) : Set ℂ := polarGraph (fun r θ => r = a * Real.sin (n * θ))

/-- The petal tips of `r = a cos nθ`: the points of the curve at the maximal distance `|a|` from the pole.
A petal is counted by its tip, the farthest point of the petal. -/
def roseCosTips (a : ℝ) (n : ℕ) : Set ℂ := {z ∈ roseCos a n | ‖z‖ = |a|}

/-- The petal tips of `r = a sin nθ` (points of the curve at distance `|a|` from the pole). -/
def roseSinTips (a : ℝ) (n : ℕ) : Set ℂ := {z ∈ roseSin a n | ‖z‖ = |a|}

/-- **Petal length of `r = a cos nθ`**: every point of the curve is within `|a|` of the pole, and the distance
`|a|` is attained. (TR-142) -/
@[kb "openstaxalgtrig2e" "§10.4 Rose curves, p. 937"]
theorem roseCos_petal_length (a : ℝ) (n : ℕ) :
    (∀ z ∈ roseCos a n, ‖z‖ ≤ |a|) ∧ ∃ z ∈ roseCos a n, ‖z‖ = |a| := by
  refine ⟨?_, polarPoint a 0, ⟨a, 0, by simp, rfl⟩, by rw [norm_polarPoint]⟩
  rintro _ ⟨r, θ, rfl, rfl⟩
  rw [norm_polarPoint, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- **Petal length of `r = a sin nθ`** (`n ≥ 1`): every point of the curve is within `|a|` of the pole, and the
distance `|a|` is attained (at `θ = π/(2n)`). (TR-142) -/
@[kb "openstaxalgtrig2e" "§10.4 Rose curves, p. 937"]
theorem roseSin_petal_length (a : ℝ) {n : ℕ} (hn : 0 < n) :
    (∀ z ∈ roseSin a n, ‖z‖ ≤ |a|) ∧ ∃ z ∈ roseSin a n, ‖z‖ = |a| := by
  refine ⟨?_, polarPoint a (Real.pi / (2 * n)), ⟨a, Real.pi / (2 * n), ?_, rfl⟩,
    by rw [norm_polarPoint]⟩
  · rintro _ ⟨r, θ, rfl, rfl⟩
    rw [norm_polarPoint, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : (n : ℝ) * (Real.pi / (2 * n)) = Real.pi / 2 := by field_simp
    show a = a * Real.sin (n * (Real.pi / (2 * n)))
    rw [this, Real.sin_pi_div_two, mul_one]

/-! ### Counting the petals -/

/-- `exp (i π (n+1)/n)`; the tips of `r = a cos nθ` are `a` times its integer powers. -/
noncomputable def roseRoot (n : ℕ) : ℂ := exp (((n : ℂ) + 1) * (Real.pi : ℂ) / n * I)

lemma sin_eq_zero_of_abs_cos (x : ℝ) (h : |Real.cos x| = 1) : Real.sin x = 0 := by
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.cos x ^ 2 = 1 := by rw [← sq_abs, h]; norm_num
  have h3 : Real.sin x ^ 2 = 0 := by linarith
  exact (pow_eq_zero_iff (two_ne_zero)).1 h3

lemma abs_cos_of_sin_eq_zero (x : ℝ) (h : Real.sin x = 0) : |Real.cos x| = 1 := by
  have h1 := Real.sin_sq_add_cos_sq x
  rw [h] at h1
  have h2 : Real.cos x ^ 2 = 1 ^ 2 := by linarith
  simpa using (sq_eq_sq_iff_abs_eq_abs _ _).1 h2

lemma polar_tip (a : ℝ) {n : ℕ} (hn : 0 < n) (k : ℤ) :
    polarPoint (a * Real.cos (n * (k * Real.pi / n))) (k * Real.pi / n) = a * roseRoot n ^ k := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn'' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h : (n : ℝ) * (k * Real.pi / n) = k * Real.pi := by field_simp
  have hc : ((Real.cos (k * Real.pi) : ℝ) : ℂ) = exp (((k * Real.pi : ℝ) : ℂ) * I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.sin_int_mul_pi]
    simp
  rw [h, polarPoint_eq_mul_exp, roseRoot, ← Complex.exp_int_mul, Complex.ofReal_mul, hc,
    mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp

lemma mem_roseCosTips_iff {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 0 < n) (z : ℂ) :
    z ∈ roseCosTips a n ↔ ∃ k : ℤ, z = a * roseRoot n ^ k := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · rintro ⟨⟨r, θ, hr, rfl⟩, hnorm⟩
    rw [norm_polarPoint, hr, abs_mul] at hnorm
    have hcos : |Real.cos (n * θ)| = 1 := by
      have : |a| ≠ 0 := abs_ne_zero.2 ha
      exact (mul_eq_left₀ this).1 hnorm
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 (sin_eq_zero_of_abs_cos _ hcos)
    have hθ : θ = k * Real.pi / n := by field_simp; linarith
    subst hθ
    exact ⟨k, by rw [hr]; exact (polar_tip a hn k).symm ▸ rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨_, k * Real.pi / n, rfl, (polar_tip a hn k).symm⟩, ?_⟩
    rw [← polar_tip a hn k, norm_polarPoint, abs_mul]
    have h : (n : ℝ) * (k * Real.pi / n) = k * Real.pi := by field_simp
    rw [h, abs_cos_of_sin_eq_zero _ (Real.sin_int_mul_pi k), mul_one]

lemma ncard_range_zpow {ω : ℂ} {N : ℕ} (h : IsPrimitiveRoot ω N) (hN : 0 < N) :
    (Set.range fun k : ℤ => ω ^ k).ncard = N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hset : (Set.range fun k : ℤ => ω ^ k) = (fun j : ℕ => ω ^ j) '' Set.Iio N := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      have h0 : 0 ≤ k % (N : ℤ) := Int.emod_nonneg _ hN'.ne'
      have h1 := Int.emod_lt_of_pos k hN'
      refine ⟨(k % N).toNat, ?_, ?_⟩
      · simp only [mem_Iio]; omega
      · have hd : (N : ℤ) ∣ k - k % N := ⟨k / N, by have := Int.emod_add_mul_ediv k N; linarith⟩
        have h2 := (h.zpow_eq_one_iff_dvd _).2 hd
        rw [zpow_sub₀ (h.ne_zero hN.ne')] at h2
        have h3 := (div_eq_one_iff_eq (zpow_ne_zero _ (h.ne_zero hN.ne'))).1 h2
        simp only
        rw [← zpow_natCast, Int.toNat_of_nonneg h0, h3]
    · rintro ⟨j, -, rfl⟩
      exact ⟨j, by simp⟩
  have hinj : Set.InjOn (fun j : ℕ => ω ^ j) (Set.Iio N) := fun i hi j hj hij =>
    h.pow_inj hi hj hij
  rw [hset, hinj.ncard_image, ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

lemma coprime_succ_double (m : ℕ) : Nat.Coprime (m + 1) (2 * m + 1) := by
  have h1 := Nat.gcd_dvd_left (m + 1) (2 * m + 1)
  have h2 := Nat.gcd_dvd_right (m + 1) (2 * m + 1)
  have h3 := Nat.dvd_sub (Dvd.dvd.mul_left h1 2) h2
  have : 2 * (m + 1) - (2 * m + 1) = 1 := by omega
  rw [this] at h3
  exact Nat.dvd_one.1 h3

lemma roseRoot_primitive {n : ℕ} (hn : 0 < n) :
    IsPrimitiveRoot (roseRoot n) (if Odd n then n else 2 * n) := by
  by_cases ho : Odd n
  · simp only [ho, ↓reduceIte]
    obtain ⟨m, rfl⟩ := ho
    have := Complex.isPrimitiveRoot_exp_of_coprime (m + 1) (2 * m + 1) (by omega)
      (coprime_succ_double m)
    convert this using 1
    rw [roseRoot]
    congr 1
    have : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast at this ⊢
    field_simp
    ring
  · simp only [ho, ↓reduceIte]
    have he : Even n := Nat.not_odd_iff_even.1 ho
    obtain ⟨m, hm⟩ := he
    have hc : Nat.Coprime (n + 1) (2 * n) := by
      refine Nat.Coprime.mul_right ?_ (by simp)
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    have := Complex.isPrimitiveRoot_exp_of_coprime (n + 1) (2 * n) (by omega) hc
    convert this using 1
    rw [roseRoot]
    congr 1
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp

/-- **Number of petals of `r = a cos nθ`**: for `a ≠ 0` and `n ≥ 1`, the curve has `n` petals if `n` is odd and
`2n` petals if `n` is even; a petal is counted by its tip. (TR-143) -/
@[kb "openstaxalgtrig2e" "§10.4 Rose curves, p. 937"]
theorem roseCos_petal_count {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 0 < n) :
    (roseCosTips a n).ncard = if Odd n then n else 2 * n := by
  have hset : roseCosTips a n =
      (fun w : ℂ => (a : ℂ) * w) '' Set.range (fun k : ℤ => roseRoot n ^ k) := by
    ext z
    rw [mem_roseCosTips_iff ha hn]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨_, ⟨k, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩; exact ⟨k, rfl⟩
  have hpos : 0 < (if Odd n then n else 2 * n) := by split_ifs <;> omega
  rw [hset, Set.ncard_image_of_injective _ (mul_right_injective₀ (Complex.ofReal_ne_zero.2 ha)),
    ncard_range_zpow (roseRoot_primitive hn) hpos]

/-- The rotation by `π/(2n)`. -/
noncomputable def roseShift (n : ℕ) : ℂ := exp (((Real.pi / (2 * n) : ℝ) : ℂ) * I)

lemma norm_roseShift (n : ℕ) : ‖roseShift n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma roseSin_eq_image (a : ℝ) {n : ℕ} (hn : 0 < n) :
    roseSin a n = (fun w : ℂ => roseShift n * w) '' roseCos a n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  ext z
  constructor
  · rintro ⟨r, θ, hr, rfl⟩
    refine ⟨polarPoint r (θ - Real.pi / (2 * n)), ⟨r, θ - Real.pi / (2 * n), ?_, rfl⟩, ?_⟩
    · have : (n : ℝ) * (θ - Real.pi / (2 * n)) = n * θ - Real.pi / 2 := by field_simp
      show r = a * Real.cos (n * (θ - Real.pi / (2 * n)))
      rw [this, Real.cos_sub_pi_div_two]; exact hr
    · have := polarPoint_add r (θ - Real.pi / (2 * n)) (Real.pi / (2 * n))
      rw [sub_add_cancel] at this
      exact this.symm
  · rintro ⟨_, ⟨r, θ, hr, rfl⟩, rfl⟩
    refine ⟨r, θ + Real.pi / (2 * n), ?_, (polarPoint_add r θ _).symm⟩
    have : (n : ℝ) * (θ + Real.pi / (2 * n)) = n * θ + Real.pi / 2 := by field_simp
    show r = a * Real.sin (n * (θ + Real.pi / (2 * n)))
    rw [this, Real.sin_add_pi_div_two]; exact hr

lemma roseSinTips_eq_image (a : ℝ) {n : ℕ} (hn : 0 < n) :
    roseSinTips a n = (fun w : ℂ => roseShift n * w) '' roseCosTips a n := by
  ext z
  constructor
  · rintro ⟨hz, hnorm⟩
    rw [roseSin_eq_image a hn] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    simpa only [norm_mul, norm_roseShift, one_mul] using hnorm
  · rintro ⟨w, ⟨hw, hnorm⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [roseSin_eq_image a hn]; exact ⟨w, hw, rfl⟩
    · rw [norm_mul, norm_roseShift, one_mul, hnorm]

/-- **Number of petals of `r = a sin nθ`**: for `a ≠ 0` and `n ≥ 1`, the curve has `n` petals if `n` is odd and
`2n` petals if `n` is even (it is the cosine rose rotated by `π/(2n)`). (TR-143) -/
@[kb "openstaxalgtrig2e" "§10.4 Rose curves, p. 937"]
theorem roseSin_petal_count {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : 0 < n) :
    (roseSinTips a n).ncard = if Odd n then n else 2 * n := by
  have hu : roseShift n ≠ 0 := Complex.exp_ne_zero _
  rw [roseSinTips_eq_image a hn, Set.ncard_image_of_injective _ (mul_right_injective₀ hu),
    roseCos_petal_count ha hn]

/-! ### The Archimedes spiral -/

/-- The Archimedes spiral `r = θ`, `θ ≥ 0`. -/
def archimedesSpiral : Set ℂ := {z | ∃ θ : ℝ, 0 ≤ θ ∧ z = polarPoint θ θ}

/-- **Archimedes spiral, distance from the pole**: the point of the spiral at angle `θ ≥ 0` is at distance `θ`
from the pole, and one more turn (`θ ↦ θ + 2π`) increases the distance by exactly `2π`. (TR-144) -/
@[kb "openstaxalgtrig2e" "§10.4 Archimedes' spiral, p. 939"]
theorem archimedesSpiral_norm {θ : ℝ} (h : 0 ≤ θ) : ‖polarPoint θ θ‖ = θ := by
  rw [norm_polarPoint, abs_of_nonneg h]

/-- One turn of the Archimedes spiral adds `2π` to the distance from the pole. (TR-144) -/
@[kb "openstaxalgtrig2e" "§10.4 Archimedes' spiral, p. 939"]
theorem archimedesSpiral_turn {θ : ℝ} (h : 0 ≤ θ) :
    ‖polarPoint (θ + 2 * Real.pi) (θ + 2 * Real.pi)‖ = ‖polarPoint θ θ‖ + 2 * Real.pi := by
  rw [archimedesSpiral_norm (by positivity), archimedesSpiral_norm h]

lemma eq_of_mem_archimedesSpiral {w : ℂ} (hw : w ∈ archimedesSpiral) :
    w = polarPoint ‖w‖ ‖w‖ := by
  obtain ⟨θ, h, rfl⟩ := hw
  rw [archimedesSpiral_norm h]

/-- **The Archimedes spiral has none of the three symmetries**: it is not closed under conjugation (polar
axis), under `z ↦ -conj z` (the line `θ = π/2`), nor under `z ↦ -z` (the pole). (TR-144) -/
@[kb "openstaxalgtrig2e" "§10.4 Archimedes' spiral, p. 939"]
theorem archimedesSpiral_no_symmetry :
    ¬ (∀ z ∈ archimedesSpiral, conj z ∈ archimedesSpiral) ∧
      ¬ (∀ z ∈ archimedesSpiral, -conj z ∈ archimedesSpiral) ∧
      ¬ (∀ z ∈ archimedesSpiral, -z ∈ archimedesSpiral) := by
  have hpi := Real.pi_pos
  have hz0 : polarPoint (Real.pi / 2) (Real.pi / 2) ∈ archimedesSpiral := ⟨_, by positivity, rfl⟩
  have hz1 : polarPoint Real.pi Real.pi ∈ archimedesSpiral := ⟨_, hpi.le, rfl⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := eq_of_mem_archimedesSpiral (h _ hz0)
    rw [Complex.norm_conj, archimedesSpiral_norm (by positivity), conj_polarPoint] at this
    have := congrArg Complex.im this
    rw [polarPoint_im, polarPoint_im, Real.sin_neg, Real.sin_pi_div_two] at this
    linarith
  · have := eq_of_mem_archimedesSpiral (h _ hz1)
    rw [norm_neg, Complex.norm_conj, archimedesSpiral_norm hpi.le, conj_polarPoint,
      neg_polarPoint] at this
    have := congrArg Complex.re this
    rw [polarPoint_re, polarPoint_re, Real.cos_neg, Real.cos_pi] at this
    linarith
  · have := eq_of_mem_archimedesSpiral (h _ hz0)
    rw [norm_neg, archimedesSpiral_norm (by positivity), neg_polarPoint] at this
    have := congrArg Complex.im this
    rw [polarPoint_im, polarPoint_im, Real.sin_pi_div_two] at this
    linarith

end UndergradKB.Trigonometry
