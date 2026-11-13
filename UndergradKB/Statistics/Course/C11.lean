import UndergradKB.Statistics.ChiSquared
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.Pearson
import UndergradKB.Statistics.IndependenceTest
import UndergradKB.Statistics.Homogeneity
import UndergradKB.Statistics.DistributionLimits
import UndergradKB.Common.Attr

/-!
# Course layer, chapter 11 (OpenStax *Introductory Statistics 2e*): the chi-square distribution
-/

namespace UndergradKB.Statistics.Course.C11

open MeasureTheory ProbabilityTheory UndergradKB.Statistics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- OpenStax Introductory Statistics 2e §11.1 (ST-096). If `Z₁, …, Z_k` are independent standard
normal variables (`k ≥ 1`), then `Z₁² + ⋯ + Z_k²` has the chi-square distribution with `k` degrees of
freedom. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem chi_square_is_sum_of_squared_standard_normals {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {Z : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (hZ : ∀ i ∈ s, HasLaw (Z i) (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ ∑ i ∈ s, Z i ω ^ 2) (chiSquared s.card) P :=
  hasLaw_sum_sq_chiSquared hs hmeas hind hZ

/-- OpenStax Introductory Statistics 2e §11.1 (ST-096). The chi-square distribution with `k > 0`
degrees of freedom has mean `k`. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem chi_square_mean {k : ℝ} (hk : 0 < k) : ∫ x, x ∂(chiSquared k) = k :=
  integral_id_chiSquared hk

/-- OpenStax Introductory Statistics 2e §11.1 (ST-096). The chi-square distribution with `k > 0`
degrees of freedom has variance `2k` (standard deviation `√(2k)`). -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem chi_square_variance {k : ℝ} (hk : 0 < k) : variance id (chiSquared k) = 2 * k :=
  variance_id_chiSquared hk

/-- OpenStax Introductory Statistics 2e §11.2 (ST-097). Goodness of fit: for independent
observations falling in category `i` of `k ≥ 2` categories with probability `pᵢ > 0`, the statistic
`∑ (O - E)²/E` (observed counts `O`, expected counts `E = n pᵢ`) is approximately chi-square with
`k - 1` degrees of freedom: it converges in distribution to that law as `n → ∞`. -/
@[kb "openstaxintrostats2e" "§11.2, p. 576"]
theorem goodness_of_fit_statistic_approx_chi_square {k : ℕ} {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {p : Fin k → ℝ} (hk : 2 ≤ k) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) {C : ℕ → Ω → Fin k} (hmeas : ∀ m, Measurable (C m)) (hind : iIndepFun C P)
    (hident : ∀ m, IdentDistrib (C m) (C 0) P P) (hprob : ∀ i, P.real {ω | C 0 ω = i} = p i)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared ((k : ℝ) - 1)) P') :
    TendstoInDistribution (pearsonStatistic p C) Filter.atTop W (fun _ ↦ P) P' :=
  tendstoInDistribution_pearsonStatistic hk hp hsum hmeas hind hident hprob hW

/-- OpenStax Introductory Statistics 2e §11.3 (ST-098). Test of independence: for independent
individuals classified in an `r × c` table (`r, c ≥ 2`), under the hypothesis that the row and column
variables are independent with positive marginal probabilities `a_i`, `b_j`, the statistic
`∑ (O - E)²/E` with expected counts `E = (row total)(column total)/(grand total)` is approximately
chi-square with `(r - 1)(c - 1)` degrees of freedom: it converges in distribution to that law. -/
@[kb "openstaxintrostats2e" "§11.3, p. 585"]
theorem independence_test_statistic_approx_chi_square {r c : ℕ} {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c) {a : Fin r → ℝ}
    {b : Fin c → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hasum : ∑ i, a i = 1)
    (hbsum : ∑ j, b j = 1) {C : ℕ → Ω → Fin r × Fin c} (hmeas : ∀ m, Measurable (C m))
    (hind : iIndepFun C P) (hident : ∀ m, IdentDistrib (C m) (C 0) P P)
    (hprob : ∀ i j, P.real {ω | C 0 ω = (i, j)} = a i * b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (independenceStatistic C) Filter.atTop W (fun _ ↦ P) P' :=
  tendstoInDistribution_independenceStatistic hr hc ha hb hasum hbsum hmeas hind hident hprob hW

/-- OpenStax Introductory Statistics 2e §11.4 (ST-099). Test of homogeneity: independent samples from
`r ≥ 2` populations with sizes `sᵢ n` in a fixed ratio, each individual in one of `c ≥ 2` categories;
if every population has the same category probabilities `b_j > 0`, the statistic `∑ (O - E)²/E` with
`E = (row total)(column total)/(grand total)` is approximately chi-square with `(r - 1)(c - 1)`
degrees of freedom: it converges in distribution to that law. -/
@[kb "openstaxintrostats2e" "§11.4, p. 589"]
theorem homogeneity_test_statistic_approx_chi_square {r c : ℕ} {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] (hr : 2 ≤ r) (hc : 2 ≤ c) {sz : Fin r → ℕ}
    (hsz : ∀ i, 0 < sz i) {b : Fin c → ℝ} (hb : ∀ j, 0 < b j) (hbsum : ∑ j, b j = 1)
    {Y : Fin r → ℕ → Ω → Fin c} (hmeas : ∀ i m, Measurable (Y i m))
    (hind : iIndepFun (fun x : Fin r × ℕ ↦ Y x.1 x.2) P)
    (hident : ∀ i m, IdentDistrib (Y i m) (Y i 0) P P) (hprob : ∀ i j, P.real {ω | Y i 0 ω = j} = b j)
    {W : Ω' → ℝ} (hW : HasLaw W (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) P') :
    TendstoInDistribution (homogeneityStatistic Y sz) Filter.atTop W (fun _ ↦ P) P' :=
  tendstoInDistribution_homogeneityStatistic hr hc hsz hb hbsum hmeas hind hident hprob hW

/-- OpenStax Introductory Statistics 2e §11.6 (ST-101). Test of a single variance: for a normal
sample of size `n ≥ 2` with standard deviation `σ`, `(n - 1) s² / σ²` has the chi-square distribution
with `n - 1` degrees of freedom. -/
@[kb "openstaxintrostats2e" "§11.6, p. 593"]
theorem single_variance_test_statistic_law {n : ℕ} {X : Fin n → Ω → ℝ} {μ σ : ℝ} (hn : 2 ≤ n)
    (hσ : 0 < σ) (hX : IsNormalSample X μ σ P) :
    HasLaw (fun ω ↦ ((n : ℝ) - 1) * (sampleVariance fun i ↦ X i ω) / σ ^ 2) (chiSquared ((n : ℝ) - 1)) P :=
  hasLaw_sampleVariance_chiSquared hn hσ hX

/-- OpenStax Introductory Statistics 2e §11.1 (ST-096). For large degrees of freedom the chi-square
distribution is approximately normal: for independent standard normal variables `Z₀, Z₁, …`, each
sum `Z₀² + ⋯ + Z_{k-1}²` (`k ≥ 1`) has the chi-square law with `k` degrees of freedom, and the
standardised sums `(∑_{i<k} Zᵢ² - k)/√(2k)` converge in distribution to a standard normal variable
as `k → ∞`. -/
@[kb "openstaxintrostats2e" "§11.1, p. 575"]
theorem chi_square_approx_normal_for_large_degrees_of_freedom {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : ℕ → Ω → ℝ} {W : Ω' → ℝ}
    (hW : HasLaw W (gaussianReal 0 1) P') (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P) :
    (∀ k : ℕ, 0 < k → HasLaw (fun ω ↦ ∑ i ∈ Finset.range k, Z i ω ^ 2) (chiSquared k) P) ∧
    TendstoInDistribution
      (fun (k : ℕ) ω ↦ (∑ i ∈ Finset.range k, Z i ω ^ 2 - k) / √(2 * k)) Filter.atTop W
      (fun _ ↦ P) P' :=
  chiSquared_approx_normal hW hmeas hind hZ

end UndergradKB.Statistics.Course.C11
