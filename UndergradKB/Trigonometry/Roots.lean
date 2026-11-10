import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import UndergradKB.Common.Attr

/-! # Roots of a complex number in polar form (Corral §6.3; OpenStax §10.5)

The `n` distinct `n`-th roots of `z = r (cos θ + i sin θ)` with `r > 0` are
`r^(1/n) (cos((θ + 2πk)/n) + i sin((θ + 2πk)/n))`, `k = 0, …, n-1`. They all have modulus `r^(1/n)` and
consecutive ones differ by the rotation through `2π/n`, so they sit equally spaced on a circle.
-/

namespace UndergradKB.Trigonometry

open Real

/-- The `k`-th candidate `n`-th root `r^(1/n) cis ((θ + 2πk)/n)` of `r cis θ`. (TR-191) -/
noncomputable def nthRootPolar (n : ℕ) (r θ : ℝ) (k : ℕ) : ℂ :=
  (r ^ (1 / n : ℝ) : ℝ) * (Real.cos ((θ + 2 * π * k) / n) + Real.sin ((θ + 2 * π * k) / n) * Complex.I)

private lemma cis_eq (s : ℝ) :
    ((Real.cos s : ℝ) : ℂ) + (Real.sin s : ℝ) * Complex.I = Complex.exp (s * Complex.I) := by
  rw [Complex.exp_mul_I]; push_cast; ring

private lemma nthRootPolar_eq (n : ℕ) (r θ : ℝ) (k : ℕ) :
    nthRootPolar n r θ k =
      ((r ^ (1 / n : ℝ) : ℝ) : ℂ) * Complex.exp ((((θ + 2 * π * k) / n : ℝ) : ℂ) * Complex.I) := by
  unfold nthRootPolar
  rw [cis_eq]

private lemma rpow_pow {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) : (r ^ (1 / n : ℝ)) ^ n = r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  have : (n : ℝ) ≠ 0 := by positivity
  rw [one_div, inv_mul_cancel₀ this, Real.rpow_one]

/-- **Every `k` gives an `n`-th root**: `(r^(1/n) cis((θ + 2πk)/n))ⁿ = r cis θ`. (TR-191) -/
theorem nthRootPolar_pow {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) (k : ℕ) :
    (nthRootPolar n r θ k) ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I) := by
  rw [nthRootPolar_eq, mul_pow, ← Complex.ofReal_pow, rpow_pow hn hr, ← Complex.exp_nat_mul,
    cis_eq θ]
  congr 1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (n : ℂ) * ((((θ + 2 * π * k) / n : ℝ) : ℂ) * Complex.I) =
      θ * Complex.I + k * (2 * π * Complex.I) := by
    push_cast
    field_simp
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- **The `n` roots are distinct**. (TR-191) -/
theorem nthRootPolar_injOn {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    Set.InjOn (nthRootPolar n r θ) (Finset.range n : Set ℕ) := by
  intro j hj k hk h
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  rw [nthRootPolar_eq, nthRootPolar_eq] at h
  have hρ : ((r ^ (1 / n : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hr _).ne'
  have h2 := mul_left_cancel₀ hρ h
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h2
  have hnr : (n : ℝ) ≠ 0 := by positivity
  have h3 : (((θ + 2 * π * j) / n - (θ + 2 * π * k) / n - 2 * π * m : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast at hm ⊢
    linear_combination hm
  have h4 := (mul_eq_zero.1 h3).resolve_right Complex.I_ne_zero
  have h5 : (θ + 2 * π * j) / n - (θ + 2 * π * k) / n - 2 * π * m = 0 := by exact_mod_cast h4
  have h6 : ((j : ℤ) - k : ℝ) = m * n := by
    field_simp at h5
    push_cast
    nlinarith [pi_pos]
  have h7 : (j : ℤ) - k = m * n := by exact_mod_cast h6
  have hn1 : (0 : ℤ) < n := by exact_mod_cast hn
  have hj' : (j : ℤ) < n := by exact_mod_cast hj
  have hk' : (k : ℤ) < n := by exact_mod_cast hk
  have : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst this
  have : (j : ℤ) = k := by linarith
  exact_mod_cast this

/-- **The `n`-th roots of `r cis θ`** (`r > 0`, `n > 0`) are exactly the `n` numbers
`r^(1/n) cis((θ + 2πk)/n)`, `k = 0, …, n-1`. (TR-191) -/
@[kb "corraltrig" "Box §6.3 (6.8), p. 152"]
theorem nthRoots_eq_image {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    {z : ℂ | z ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I)} =
      ↑((Finset.range n).image (nthRootPolar n r θ)) := by
  set T : ℂ := (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I) with hT
  have hsub : (Finset.range n).image (nthRootPolar n r θ) ⊆ (Polynomial.nthRoots n T).toFinset := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact nthRootPolar_pow hn hr θ k
  have hcard : (Polynomial.nthRoots n T).toFinset.card ≤
      ((Finset.range n).image (nthRootPolar n r θ)).card := by
    rw [Finset.card_image_of_injOn (nthRootPolar_injOn hn hr θ), Finset.card_range]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n T)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  ext z
  have : z ∈ (Finset.range n).image (nthRootPolar n r θ) ↔ z ^ n = T := by
    rw [heq, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  simpa using this.symm

/-- The OpenStax §10.5 statement of the same fact. (TR-191) -/
@[kb "openstaxalgtrig2e" "§10.5 (nth root theorem), p. 952"]
theorem nthRoots_eq_image' {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    {z : ℂ | z ^ n = (r : ℂ) * ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I)} =
      ↑((Finset.range n).image (nthRootPolar n r θ)) :=
  nthRoots_eq_image hn hr θ

/-- All the `n`-th roots lie on the circle of radius `r^(1/n)`. (TR-192) -/
theorem norm_nthRootPolar (n : ℕ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (k : ℕ) :
    ‖nthRootPolar n r θ k‖ = r ^ (1 / n : ℝ) := by
  rw [nthRootPolar_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]

/-- Consecutive roots differ by the rotation through `2π/n`, so the roots are equally spaced. (TR-192) -/
@[kb "corraltrig" "Box §6.3, p. 153"]
theorem nthRootPolar_succ {n : ℕ} (hn : 0 < n) (r θ : ℝ) (k : ℕ) :
    nthRootPolar n r θ (k + 1) =
      nthRootPolar n r θ k *
        ((Real.cos (2 * π / n) : ℝ) + (Real.sin (2 * π / n) : ℝ) * Complex.I) := by
  rw [nthRootPolar_eq, nthRootPolar_eq, cis_eq, mul_assoc (_ : ℂ), ← Complex.exp_add]
  congr 2
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp
  ring

end UndergradKB.Trigonometry
