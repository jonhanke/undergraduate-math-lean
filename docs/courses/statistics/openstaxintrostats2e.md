# Course outline: OpenStax Introductory Statistics 2e (statistics)

Generated from [`docs/coverage/statistics/checklist.md`](../../coverage/statistics/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build Statistics` builds this topic.

118 items in 13 chapters; 94 with a Lean name (79.7%).

## Chapter 1

3 items; 1 with a Lean name; 1 proved proved here; 2 not a result.


#### Section 1.2

- **§1.2**, p.21 [ST-001]: A simple random sample of size n from a population is chosen so that every subset of size n is equally likely. — *proved proved here* — `UndergradKB.Statistics.srsLaw`, `UndergradKB.Statistics.srsLaw_inclusion_prob`

#### Section 1.3

- **§1.3**, p.37 [ST-003]: Levels of measurement (nominal, ordinal, interval, ratio) classify what arithmetic is meaningful on data. — *not a result* — –

#### Section 1.4

- **§1.4**, p.45 [ST-004]: Explanatory and response variables, treatments, lurking variables, randomization and blinding in experimental design. — *not a result* — –

## Chapter 2

14 items; 10 with a Lean name; 8 proved proved here; 1 in Mathlib; 1 partly; 4 not a result.


#### Section 2.2

- **§2.2**, p.86 [ST-005]: Relative frequency is frequency divided by the sample size, and relative frequencies sum to one; cumulative relative frequency is the running total. — *proved proved here* — `UndergradKB.Statistics.sum_relativeFrequency_eq_one`
- **§2.2**, p.86 [ST-018]: Histograms, frequency polygons, time series and stem-and-leaf displays. — *not a result* — –

#### Section 2.3

- **§2.3**, p.97 [ST-009]: The k-th percentile is a data value with about k percent of the data at or below it; quartiles Q1, Q2, Q3 are the 25th, 50th, 75th percentiles; the interquartile range is Q3 minus Q1. — *proved proved here* — `UndergradKB.Statistics.exists_percentile`, `UndergradKB.Statistics.existsUnique_percentile`

#### Section 2.4

- **§2.4**, p.105 [ST-010]: Five-number summary and box plot: minimum, Q1, median, Q3, maximum; a value is a suspected outlier if it lies more than 1.5 IQR below Q1 or above Q3. — *not a result* — –

#### Section 2.5

- **§2.5**, p.109 [ST-006]: The mean of data x_1..x_n is the sum divided by n; for tabulated data it is the sum of f*x over the sum of f. — *proved proved here* — `UndergradKB.Statistics.mean_eq_sum_value_mul_frequency`
- **§2.5**, p.109 [ST-007]: The median is the middle value of ordered data (average of the two middle values when n is even); the mode is the most frequent value. — *proved proved here* — `UndergradKB.Statistics.sortedData`, `UndergradKB.Statistics.median`, `UndergradKB.Statistics.half_le_card_le_median`, `UndergradKB.Statistics.half_le_card_ge_median`
- **§2.5**, p.109 [ST-008]: Mean of grouped data is approximated by sum of f times the interval midpoint over the sum of f. — *not a result* — –

#### Section 2.6

- **§2.6**, p.115 [ST-011]: In a right-skewed distribution the mean exceeds the median, which exceeds the mode, in a left-skewed one the order reverses, and in a symmetric one they agree. — *proved proved here* — `UndergradKB.Statistics.integral_eq_of_map_reflect`

#### Section 2.7

- **§2.7**, p.118 [ST-012]: Sample standard deviation s is the square root of the sum of squared deviations divided by n-1; population standard deviation sigma divides by N; variance is the square. — *proved proved here* — `UndergradKB.Statistics.sampleVariance`, `UndergradKB.Statistics.sampleVariance_nonneg`, `UndergradKB.Statistics.populationVariance_eq`
- **§2.7**, p.118 [ST-013]: Standard deviation is zero exactly when all data values are equal, and is nonnegative. — *proved proved here* — `UndergradKB.Statistics.sampleStdDev_eq_zero_iff`
- **§2.7**, p.118 [ST-014]: z-score: z = (x - mean)/standard deviation counts the number of standard deviations x lies from the mean. — *proved proved here* — `UndergradKB.Statistics.zScore`, `UndergradKB.Statistics.mean_zScore`, `UndergradKB.Statistics.sampleVariance_zScore`
- **§2.7**, p.118 [ST-015]: Chebyshev's inequality: at least 1 - 1/k^2 of any data set lies within k standard deviations of the mean (k > 1). — *in Mathlib* — `UndergradKB.Statistics.Course.C2.chebyshev_inequality`, `UndergradKB.Statistics.chebyshev_data`, `UndergradKB.Statistics.chebyshev_data_within`, `ProbabilityTheory.meas_ge_le_variance_div_sq`
- **§2.7**, p.118 [ST-016]: Empirical rule: for roughly bell-shaped data about 68, 95 and 99.7 percent lie within 1, 2, 3 standard deviations of the mean. — *partly* — `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.gaussianReal_apply_eq_integral`
- **§2.7**, p.118 [ST-017]: For grouped data the standard deviation is approximated using interval midpoints weighted by frequency. — *not a result* — –

## Chapter 3

15 items; 13 with a Lean name; 2 proved proved here; 8 in Mathlib; 3 partly; 2 not a result.


#### Section 3.1

- **§3.1**, p.179 [ST-019]: A sample space is the set of all outcomes; an event is a subset; with equally likely outcomes P(A) is the number of outcomes in A over the number in the sample space. — *partly* — `UndergradKB.Statistics.Course.C3.equally_likely_probability`, `MeasureTheory.IsProbabilityMeasure`, `MeasureTheory.Measure.uniformOfFinset`
- **§3.1**, p.179 [ST-020]: Probabilities lie between 0 and 1, the whole sample space has probability 1 and the empty event 0. — *in Mathlib* — `UndergradKB.Statistics.Course.C3.probability_bounds`, `MeasureTheory.prob_le_one`, `MeasureTheory.measure_empty`
- **§3.1**, p.179 [ST-021]: Complement rule: P(A') = 1 - P(A). — *in Mathlib* — `UndergradKB.Statistics.Course.C3.complement_rule`, `MeasureTheory.prob_compl_eq_one_sub`

#### Section 3.2

- **§3.2**, p.183 [ST-023]: Mutually exclusive events cannot occur together, so P(A and B) = 0 and P(A or B) = P(A) + P(B). — *in Mathlib* — `UndergradKB.Statistics.Course.C3.mutually_exclusive_rule`, `MeasureTheory.measure_union`, `Disjoint`
- **§3.2**, p.183 [ST-026]: Events A and B are independent if P(A \| B) = P(A), equivalently P(B \| A) = P(B), equivalently P(A and B) = P(A) P(B). — *in Mathlib* — `UndergradKB.Statistics.Course.C3.independent_iff_product`, `UndergradKB.Statistics.Course.C3.conditional_eq_of_independent`, `ProbabilityTheory.IndepSet`, `ProbabilityTheory.indepSet_iff_measure_inter_eq_mul`
- **§3.2**, p.183 [ST-027]: Two mutually exclusive events of positive probability are never independent. — *proved proved here* — `UndergradKB.Statistics.not_indepSet_of_disjoint`
- **§3.2**, p.183 [ST-029]: Drawing with replacement gives independent draws, drawing without replacement gives dependent draws. — *not a result* — –

#### Section 3.3

- **§3.3**, p.190 [ST-022]: Addition rule: P(A or B) = P(A) + P(B) - P(A and B). — *in Mathlib* — `UndergradKB.Statistics.Course.C3.addition_rule`, `MeasureTheory.measure_union_add_inter`
- **§3.3**, p.190 [ST-024]: Conditional probability: P(A \| B) = P(A and B) / P(B) when P(B) > 0. — *in Mathlib* — `UndergradKB.Statistics.Course.C3.conditional_probability_def`, `ProbabilityTheory.cond`, `ProbabilityTheory.cond_apply`
- **§3.3**, p.190 [ST-025]: Multiplication rule: P(A and B) = P(B \| A) P(A). — *in Mathlib* — `UndergradKB.Statistics.Course.C3.multiplication_rule`, `ProbabilityTheory.cond_mul_eq_inter`
- **§3.3**, p.190 [ST-028]: Independence of A and B implies independence of A and the complement of B (and of the two complements). — *proved proved here* — `UndergradKB.Statistics.indepSet_compl_right_of_indepSet`, `UndergradKB.Statistics.indepSet_compl_compl_of_indepSet`

#### Section 3.4

- **§3.4**, p.194 [ST-030]: Contingency tables give joint, marginal and conditional probabilities by dividing cell counts by totals. — *not a result* — –

#### Section 3.5

- **§3.5**, p.200 [ST-031]: Tree diagrams: the probability of a path is the product of the branch probabilities (multiplication rule), and the probability of an event is the sum over the paths leading to it. — *partly* — `UndergradKB.Statistics.Course.C3.total_probability_two_branches`, `ProbabilityTheory.cond_mul_eq_inter`, `MeasureTheory.measure_inter_add_diff`
- **§3.5**, p.200 [ST-032]: Reversing a conditional probability by the definition: P(A \| B) = P(B \| A) P(A) / P(B) (Bayes' rule, worked from tree and contingency table). — *in Mathlib* — `UndergradKB.Statistics.Course.C3.reverse_conditional`, `ProbabilityTheory.cond_eq_inv_mul_cond_mul`
- **§3.5**, p.200 [ST-033]: Venn diagram identities: P(A and B') = P(A) - P(A and B) and De Morgan type relations among events. — *partly* — `UndergradKB.Statistics.Course.C3.prob_inter_compl`, `MeasureTheory.measure_diff`, `Set.compl_union`

## Chapter 4

16 items; 16 with a Lean name; 5 proved proved here; 10 in Mathlib; 1 partly.


#### Section 4.1

- **§4.1**, p.239 [ST-034]: A discrete probability distribution assigns each value x a probability P(x) with 0 <= P(x) <= 1 and the probabilities summing to 1. — *in Mathlib* — `UndergradKB.Statistics.Course.C4.discrete_distribution_sums_to_one`, `PMF.tsum_coe`, `MeasureTheory.Measure.count`

#### Section 4.2

- **§4.2**, p.241 [ST-002]: Law of large numbers: the average of independent identically distributed trials converges to the expected value as the number of trials grows. — *in Mathlib* — `UndergradKB.Statistics.Course.C4.law_of_large_numbers`, `ProbabilityTheory.strong_law_ae`
- **§4.2**, p.241 [ST-035]: Expected value of a discrete random variable is mu = sum of x P(x). — *in Mathlib* — `UndergradKB.Statistics.Course.C4.expected_value_discrete`, `MeasureTheory.integral`, `PMF.integral_eq_tsum`
- **§4.2**, p.241 [ST-036]: Standard deviation of a discrete random variable: sigma = sqrt(sum of (x - mu)^2 P(x)). — *in Mathlib* — `UndergradKB.Statistics.Course.C4.variance_is_expected_squared_deviation`, `ProbabilityTheory.variance`, `ProbabilityTheory.variance_eq_integral`
- **§4.2**, p.241 [ST-037]: Expected value of a game: the long-run average gain per play equals the sum of gain times probability (a fair game has expectation 0). — *partly* — `ProbabilityTheory.strong_law_ae`

#### Section 4.3

- **§4.3**, p.248 [ST-038]: A Bernoulli trial has two outcomes, success with probability p and failure q = 1 - p; trials are independent. — *in Mathlib* — `UndergradKB.Statistics.Course.C4.bernoulli_success_probability`, `ProbabilityTheory.bernoulliMeasure`
- **§4.3**, p.248 [ST-039]: Binomial distribution: the number of successes in n independent Bernoulli(p) trials has P(X = x) = C(n,x) p^x q^(n-x). — *in Mathlib* — `UndergradKB.Statistics.Course.C4.binomial_probability`, `ProbabilityTheory.binomial`, `ProbabilityTheory.binomial_singleton`, `ProbabilityTheory.binomial_real_singleton`
- **§4.3**, p.248 [ST-040]: The binomial distribution has mean np and standard deviation sqrt(npq). — *proved proved here* — `UndergradKB.Statistics.variance_binomial`, `UndergradKB.Statistics.variance_of_hasLaw_binomial`, `ProbabilityTheory.integral_of_hasLaw_binomial`

#### Section 4.4

- **§4.4**, p.253 [ST-041]: Geometric distribution: the number of trials until the first success has P(X = x) = q^(x-1) p; the failures-before-first-success version is q^x p. — *in Mathlib* — `UndergradKB.Statistics.Course.C4.geometric_probability`, `UndergradKB.Statistics.Course.C4.geometric_probabilities_sum_to_one`, `ProbabilityTheory.geometricMeasure`, `ProbabilityTheory.geometricMeasure_singleton`
- **§4.4**, p.253 [ST-042]: The geometric distribution (trials version) has mean 1/p and standard deviation sqrt((1-p)/p^2); the failures version has mean (1-p)/p. — *proved proved here* — `UndergradKB.Statistics.integral_geometricMeasure_id`, `UndergradKB.Statistics.integral_geometricMeasure_trials`, `UndergradKB.Statistics.variance_geometricMeasure`, `UndergradKB.Statistics.variance_geometricMeasure_trials`

#### Section 4.5

- **§4.5**, p.258 [ST-043]: Hypergeometric distribution: choosing n items without replacement from A successes and B failures gives P(X = x) = C(A,x) C(B,n-x) / C(A+B,n). — *proved proved here* — `UndergradKB.Statistics.hypergeometricPMF`, `UndergradKB.Statistics.sum_hypergeometricPMF`
- **§4.5**, p.258 [ST-044]: The hypergeometric distribution has mean nA/(A+B) and the binomial with p = A/(A+B) approximates it when the population is large. — *proved proved here* — `UndergradKB.Statistics.sum_mul_hypergeometricPMF`
- **Example 4.20**, p.258 [ST-041]: Geometric distribution: the number of trials until the first success has P(X = x) = q^(x-1) p; the failures-before-first-success version is q^x p. — *in Mathlib* — `UndergradKB.Statistics.Course.C4.geometric_probability`, `UndergradKB.Statistics.Course.C4.geometric_probabilities_sum_to_one`, `ProbabilityTheory.geometricMeasure`, `ProbabilityTheory.geometricMeasure_singleton`

#### Section 4.6

- **§4.6**, p.261 [ST-045]: Poisson distribution: P(X = x) = e^(-mu) mu^x / x!, with mean mu and standard deviation sqrt(mu). — *proved proved here* — `UndergradKB.Statistics.integral_poissonMeasure_id`, `UndergradKB.Statistics.variance_poissonMeasure`
- **§4.6**, p.261 [ST-046]: The Poisson distribution approximates the binomial when n is large and p is small, with mu = np. — *in Mathlib* — `UndergradKB.Statistics.Course.C4.poisson_approximates_binomial`, `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`
- **§4.6**, p.261 [ST-047]: A sum of independent Poisson random variables is Poisson with the summed parameter (implicit when intervals are added). — *in Mathlib* — `UndergradKB.Statistics.Course.C4.poisson_sum`, `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`, `ProbabilityTheory.IndepFun.hasLaw_add_poissonMeasure`

## Chapter 5

10 items; 10 with a Lean name; 6 proved proved here; 4 in Mathlib.


#### Section 5.1

- **§5.1**, p.303 [ST-048]: A continuous random variable has a density with total area 1; probabilities are areas under the density and P(X = x) = 0 for each single x. — *in Mathlib* — `UndergradKB.Statistics.Course.C5.prob_single_value_eq_zero`, `UndergradKB.Statistics.Course.C5.density_total_area`, `MeasureTheory.HasPDF`, `MeasureTheory.pdf`
- **§5.1**, p.303 [ST-049]: The cumulative distribution function F(x) = P(X <= x) is nondecreasing with limits 0 and 1. — *in Mathlib* — `UndergradKB.Statistics.Course.C5.cdf_monotone_with_limits`, `ProbabilityTheory.cdf`, `ProbabilityTheory.monotone_cdf`, `ProbabilityTheory.tendsto_cdf_atBot`

#### Section 5.2

- **§5.2**, p.306 [ST-050]: Uniform distribution on [a,b]: density 1/(b-a); P(c < X < d) = (d-c)/(b-a). — *in Mathlib* — `UndergradKB.Statistics.Course.C5.uniform_interval_probability`, `MeasureTheory.pdf.IsUniform`, `MeasureTheory.pdf.IsUniform.pdf_eq`
- **§5.2**, p.306 [ST-051]: The uniform distribution on [a,b] has mean (a+b)/2 and standard deviation (b-a)/sqrt(12). — *proved proved here* — `UndergradKB.Statistics.uniform_mean`, `UndergradKB.Statistics.uniform_variance`
- **§5.2**, p.306 [ST-052]: Conditional probability for a uniform variable: P(X > c \| X > b) is the ratio of the lengths of the remaining intervals. — *proved proved here* — `UndergradKB.Statistics.uniform_cond_Ioi`

#### Section 5.3

- **§5.3**, p.313 [ST-053]: Exponential distribution with rate m: density m e^(-mx) for x >= 0, mean = standard deviation = 1/m. — *proved proved here* — `UndergradKB.Statistics.Course.C5.exponential_density_total_area`, `UndergradKB.Statistics.integral_expMeasure_id`, `UndergradKB.Statistics.variance_expMeasure`, `UndergradKB.Statistics.sqrt_variance_expMeasure`
- **§5.3**, p.313 [ST-054]: Exponential cumulative distribution function: P(X <= x) = 1 - e^(-mx), so P(X > x) = e^(-mx). — *in Mathlib* — `UndergradKB.Statistics.Course.C5.exponential_cdf`, `ProbabilityTheory.cdf_expMeasure_eq`
- **§5.3**, p.313 [ST-055]: Memoryless property of the exponential distribution: P(X > x + k \| X > x) = P(X > k). — *proved proved here* — `UndergradKB.Statistics.expMeasure_memoryless`, `UndergradKB.Statistics.expMeasure_memoryless_of_hasLaw`
- **§5.3**, p.313 [ST-056]: If events occur at Poisson rate m, the waiting time between events is exponential with mean 1/m (Poisson-exponential relation). — *proved proved here* — `UndergradKB.Statistics.hasLaw_expMeasure_of_poisson_counts`
- **§5.3**, p.313 [ST-057]: The k-th percentile of the exponential distribution is k_p = ln(1 - p)/(-m). — *proved proved here* — `UndergradKB.Statistics.expMeasure_percentile`

## Chapter 6

5 items; 5 with a Lean name; 3 in Mathlib; 2 partly.


#### Section 6.1

- **§6.1**, p.347 [ST-058]: The normal distribution N(mu, sigma) has a bell-shaped density symmetric about mu, with mean mu and standard deviation sigma; N(0,1) is the standard normal. — *in Mathlib* — `UndergradKB.Statistics.Course.C6.normal_mean_variance`, `UndergradKB.Statistics.Course.C6.normal_density_shift`, `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.gaussianPDFReal`
- **§6.1**, p.347 [ST-059]: Standardization: if X ~ N(mu, sigma) then Z = (X - mu)/sigma ~ N(0,1), and conversely X = mu + sigma Z. — *in Mathlib* — `UndergradKB.Statistics.Course.C6.standardization`, `UndergradKB.Statistics.Course.C6.normal_of_standard`, `ProbabilityTheory.gaussianReal_sub_const`, `ProbabilityTheory.gaussianReal_div_const`
- **§6.1**, p.347 [ST-060]: Empirical rule for the normal distribution: P(\|X - mu\| < k sigma) is about 0.68, 0.95, 0.997 for k = 1, 2, 3. — *partly* — `ProbabilityTheory.gaussianReal_apply_eq_integral`

#### Section 6.2

- **§6.2**, p.351 [ST-061]: Normal probabilities and percentiles are computed from the standard normal cumulative distribution function and its inverse (z-tables). — *partly* — `ProbabilityTheory.cdf`, `ProbabilityTheory.gaussianReal`
- **§6.2**, p.351 [ST-062]: Linear transformations: if X has mean mu and standard deviation sigma then aX + b has mean a mu + b and standard deviation \|a\| sigma (used when converting units). — *in Mathlib* — `UndergradKB.Statistics.Course.C6.linear_transformation_mean_variance`, `UndergradKB.Statistics.mean_affine`, `UndergradKB.Statistics.sampleStdDev_affine`, `ProbabilityTheory.variance_smul`

## Chapter 7

8 items; 7 with a Lean name; 3 proved proved here; 4 in Mathlib; 1 not a result.


#### Section 7.1

- **§7.1**, p.378 [ST-063]: The sampling distribution of a statistic is the probability distribution of the statistic over all simple random samples of size n; the standard error is its standard deviation. — *proved proved here* — `UndergradKB.Statistics.srsLaw`, `UndergradKB.Statistics.integral_srsLaw_sampleMean`
- **§7.1**, p.378 [ST-064]: Mean of the sample mean: E[X-bar] = mu, and standard error sigma/sqrt(n) for independent identically distributed observations. — *in Mathlib* — `UndergradKB.Statistics.Course.C7.expected_sample_mean`, `UndergradKB.Statistics.Course.C7.variance_sample_mean`, `UndergradKB.Statistics.Course.C7.standard_error_sample_mean`, `ProbabilityTheory.IndepFun.variance_sum`
- **§7.1**, p.378 [ST-065]: Central limit theorem for sample means: for large n the sample mean of n independent observations from any population with mean mu and standard deviation sigma is approximately N(mu, sigma/sqrt(n)). — *in Mathlib* — `UndergradKB.Statistics.Course.C7.central_limit_theorem_mean`, `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`
- **§7.1**, p.378 [ST-066]: If the population is normal N(mu, sigma), the sample mean of n observations is exactly N(mu, sigma/sqrt(n)) for every n. — *proved proved here* — `UndergradKB.Statistics.hasLaw_sampleMean_normal`
- **§7.1**, p.378 [ST-068]: Law of large numbers: as n grows the sample mean approaches the population mean. — *in Mathlib* — `UndergradKB.Statistics.Course.C7.sample_mean_tendsto_population_mean`, `ProbabilityTheory.strong_law_ae`

#### Section 7.2

- **§7.2**, p.381 [ST-067]: Central limit theorem for sums: the sum of n independent observations is approximately N(n mu, sqrt(n) sigma). — *in Mathlib* — `UndergradKB.Statistics.Course.C7.central_limit_theorem_sum`, `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`

#### Section 7.3

- **§7.3**, p.384 [ST-069]: Normal approximation to the binomial with continuity correction 0.5: P(X <= k) is about the normal cdf at k + 0.5. — *proved proved here* — `UndergradKB.Statistics.tendstoInDistribution_binomial_count`
- **§7.3**, p.384 [ST-070]: Sums and means of sample size n at least about 30 may be treated as normal (rule of thumb for the central limit theorem). — *not a result* — –

## Chapter 8

10 items; 7 with a Lean name; 7 proved proved here; 3 not a result.


#### Section 8.1

- **§8.1**, p.418 [ST-071]: With known sigma and a normal population, the interval x-bar +- z_(alpha/2) sigma/sqrt(n) covers mu with probability 1 - alpha (confidence level 1 - alpha). — *proved proved here* — `UndergradKB.Statistics.zInterval_coverage`, `UndergradKB.Statistics.zInterval_confidence_level`
- **§8.1**, p.418 [ST-072]: Margin of error (error bound) EBM = z_(alpha/2) sigma/sqrt(n); the interval is x-bar - EBM to x-bar + EBM. — *not a result* — –
- **§8.1**, p.418 [ST-073]: Required sample size for a given error bound: n = z^2 sigma^2 / EBM^2 (rounded up). — *proved proved here* — `UndergradKB.Statistics.margin_le_of_sampleSize`
- **§8.1**, p.418 [ST-074]: Interpretation of a confidence level: in repeated sampling a proportion 1 - alpha of the intervals contains the parameter. — *not a result* — –

#### Section 8.2

- **§8.2**, p.427 [ST-075]: Student t: for a normal population, (x-bar - mu)/(s/sqrt(n)) has the Student t distribution with n-1 degrees of freedom. — *proved proved here* — `UndergradKB.Statistics.studentT`, `UndergradKB.Statistics.hasLaw_studentT`, `UndergradKB.Statistics.hasLaw_tStatistic`, `UndergradKB.Statistics.indepFun_sampleMean_sampleVariance`
- **§8.2**, p.427 [ST-076]: The Student t distribution is symmetric, bell-shaped, heavier-tailed than the normal and tends to N(0,1) as the degrees of freedom grow. — *proved proved here* — `UndergradKB.Statistics.studentTPDFReal_neg`, `UndergradKB.Statistics.studentTPDFReal_le_of_abs_le`, `UndergradKB.Statistics.tendsto_studentTPDFReal_gaussianPDFReal`
- **§8.2**, p.427 [ST-077]: Confidence interval for a mean with unknown sigma: x-bar +- t_(alpha/2, n-1) s/sqrt(n). — *proved proved here* — `UndergradKB.Statistics.tInterval_coverage`

#### Section 8.3

- **§8.3**, p.431 [ST-078]: For a proportion, p' = x/n is approximately N(p, sqrt(pq/n)) when np and nq are large, giving the interval p' +- z_(alpha/2) sqrt(p'q'/n). — *proved proved here* — `UndergradKB.Statistics.tendstoInDistribution_sampleProportion`
- **§8.3**, p.431 [ST-079]: Sample size for estimating a proportion to within EBP: n = z^2 p'q' / EBP^2 (use p' = 0.5 if unknown). — *proved proved here* — `UndergradKB.Statistics.proportion_margin_le_of_sampleSize`, `UndergradKB.Statistics.proportion_margin_le_of_conservative`
- **§8.3**, p.431 [ST-080]: Rule of thumb: the normal approximation for a proportion is acceptable when np' and nq' are both at least 5. — *not a result* — –

## Chapter 9

9 items; 7 with a Lean name; 7 proved proved here; 2 not a result.


#### Section 9.1

- **§9.1**, p.473 [ST-081]: A hypothesis test compares a null hypothesis H0 (an equality) with an alternative Ha (a strict inequality); tests are left, right or two-tailed according to Ha. — *not a result* — –

#### Section 9.2

- **§9.2**, p.475 [ST-082]: Type I error (rejecting a true H0) has probability alpha, the level of significance; Type II error (keeping a false H0) has probability beta; power is 1 - beta. — *proved proved here* — `UndergradKB.Statistics.zTest_typeI_error`, `UndergradKB.Statistics.tTest_typeI_error`
- **§9.2**, p.475 [ST-083]: For a fixed sample size, decreasing alpha increases beta; increasing the sample size reduces both. — *proved proved here* — `UndergradKB.Statistics.zTestPower`, `UndergradKB.Statistics.zTest_power_eq`, `UndergradKB.Statistics.zTestPower_strictAnti_critical`, `UndergradKB.Statistics.zTestPower_lt_of_smaller_level`

#### Section 9.3

- **§9.3**, p.477 [ST-084]: Under H0 with known sigma (or large n), the test statistic z = (x-bar - mu0)/(sigma/sqrt(n)) is approximately standard normal (test of a mean, normal case). — *proved proved here* — `UndergradKB.Statistics.Course.C7.central_limit_theorem_mean`, `UndergradKB.Statistics.hasLaw_zStatistic`
- **§9.3**, p.477 [ST-085]: Under H0 with unknown sigma and a normal population, t = (x-bar - mu0)/(s/sqrt(n)) has the Student t distribution with n-1 degrees of freedom. — *proved proved here* — `UndergradKB.Statistics.hasLaw_tStatistic`
- **§9.3**, p.477 [ST-086]: Test of a proportion: under H0 the statistic z = (p' - p0)/sqrt(p0 q0/n) is approximately standard normal when np0 and nq0 are at least 5. — *proved proved here* — `UndergradKB.Statistics.tendstoInDistribution_sampleProportion`

#### Section 9.4

- **§9.4**, p.478 [ST-087]: The p-value is the probability, assuming H0, of a result at least as extreme as the observed statistic; reject H0 when p-value < alpha. — *proved proved here* — `UndergradKB.Statistics.zPValue`, `UndergradKB.Statistics.zPValue_lt_iff`, `UndergradKB.Statistics.zPValue_prob_lt`

#### Section 9.5

- **§9.5**, p.480 [ST-088]: Decision rule and conclusion in words: reject H0 when the p-value is below alpha, otherwise do not reject; never 'accept' H0. — *not a result* — –
- **§9.5**, p.480 [ST-089]: Testing at level alpha two-sidedly is equivalent to checking whether mu0 lies in the (1 - alpha) confidence interval (duality). — *proved proved here* — `UndergradKB.Statistics.zTest_accepts_iff_mem_interval`, `UndergradKB.Statistics.tTest_accepts_iff_mem_interval`

## Chapter 10

6 items; 4 with a Lean name; 3 proved proved here; 1 partly; 1 not formalized; 1 not a result.


#### Section 10.1

- **§10.1**, p.523 [ST-090]: Two independent sample means with unknown standard deviations: t = ((x1-bar - x2-bar) - (mu1 - mu2))/sqrt(s1^2/n1 + s2^2/n2) is approximately Student t with Satterthwaite degrees of freedom. — *not formalized* — –
- **§10.1**, p.523 [ST-091]: The difference of independent sample means has mean mu1 - mu2 and standard deviation sqrt(sigma1^2/n1 + sigma2^2/n2) (and is normal when both populations are normal). — *proved proved here* — `UndergradKB.Statistics.hasLaw_diffMeans`

#### Section 10.2

- **§10.2**, p.531 [ST-092]: Two independent means with known standard deviations: z = ((x1-bar - x2-bar) - (mu1 - mu2))/sqrt(sigma1^2/n1 + sigma2^2/n2) is standard normal for normal populations. — *proved proved here* — `UndergradKB.Statistics.hasLaw_twoSampleZ`

#### Section 10.3

- **§10.3**, p.534 [ST-093]: Two proportions: the difference p'_A - p'_B is approximately normal with mean p_A - p_B and standard deviation sqrt(p_A q_A/n_A + p_B q_B/n_B); under H0 use the pooled proportion p_c. — *partly* — `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`, `ProbabilityTheory.IndepFun.variance_add`

#### Section 10.4

- **§10.4**, p.538 [ST-094]: Matched (paired) samples: test the mean of the paired differences with t = (d-bar - mu_d)/(s_d/sqrt(n)), Student t with n-1 degrees of freedom. — *proved proved here* — `UndergradKB.Statistics.hasLaw_pairedTStatistic`

#### Section 10.5

- **§10.5**, p.543 [ST-095]: Choice of the right two-sample procedure (independent vs matched, means vs proportions, known vs unknown sigma). — *not a result* — –

## Chapter 11

6 items; 2 with a Lean name; 2 proved proved here; 3 not formalized; 1 not a result.


#### Section 11.1

- **§11.1**, p.575 [ST-096]: The chi-square distribution with k degrees of freedom is right-skewed, has mean k, standard deviation sqrt(2k) and approaches the normal as k grows; it is the law of a sum of k squared independent standard normals. — *proved proved here* — `UndergradKB.Statistics.chiSquared`, `UndergradKB.Statistics.hasLaw_sq_chiSquared_one`, `UndergradKB.Statistics.hasLaw_sum_sq_chiSquared`, `UndergradKB.Statistics.hasLaw_sum_chiSquared`

#### Section 11.2

- **§11.2**, p.576 [ST-097]: Goodness of fit: the statistic sum of (O - E)^2/E over k categories is approximately chi-square with k - 1 degrees of freedom under H0 (Pearson). — *not formalized* — –

#### Section 11.3

- **§11.3**, p.585 [ST-098]: Test of independence in an r by c table: expected count = (row total)(column total)/grand total, degrees of freedom (r-1)(c-1). — *not formalized* — –

#### Section 11.4

- **§11.4**, p.589 [ST-099]: Test for homogeneity of several populations uses the same chi-square statistic and degrees of freedom as the test of independence. — *not formalized* — –

#### Section 11.5

- **§11.5**, p.593 [ST-100]: Conditions for the chi-square approximation: every expected count at least 5; the tests are right-tailed. — *not a result* — –

#### Section 11.6

- **§11.6**, p.593 [ST-101]: Test of a single variance: for a normal population (n-1)s^2/sigma0^2 has the chi-square distribution with n-1 degrees of freedom under H0. — *proved proved here* — `UndergradKB.Statistics.hasLaw_sampleVariance_chiSquared`

## Chapter 12

11 items; 8 with a Lean name; 8 proved proved here; 3 not a result.


#### Section 12.1

- **§12.1**, p.628 [ST-102]: A line y = a + bx has intercept a and slope b; the slope is the change in y per unit change in x. — *not a result* — –

#### Section 12.3

- **§12.3**, p.634 [ST-103]: Least-squares line: the line y-hat = a + bx minimizing the sum of squared residuals (SSE) has b = sum((x - x-bar)(y - y-bar))/sum((x - x-bar)^2) and a = y-bar - b x-bar. — *proved proved here* — `UndergradKB.Statistics.slope`, `UndergradKB.Statistics.intercept`, `UndergradKB.Statistics.sse`, `UndergradKB.Statistics.sse_intercept_slope_le`
- **§12.3**, p.634 [ST-104]: The least-squares line passes through the point of means (x-bar, y-bar); the residuals sum to zero. — *proved proved here* — `UndergradKB.Statistics.intercept_add_slope_mul_mean`, `UndergradKB.Statistics.sum_residual_eq_zero`
- **§12.3**, p.634 [ST-105]: The slope also equals r s_y / s_x, where r is the sample correlation coefficient and s_x, s_y are sample standard deviations. — *proved proved here* — `UndergradKB.Statistics.slope_eq_correlation_mul`
- **§12.3**, p.634 [ST-106]: Correlation coefficient r = sum((x - x-bar)(y - y-bar))/sqrt(sum((x - x-bar)^2) sum((y - y-bar)^2)) satisfies -1 <= r <= 1. — *proved proved here* — `UndergradKB.Statistics.correlation`, `UndergradKB.Statistics.correlation_mem_Icc`
- **§12.3**, p.634 [ST-107]: r = 1 or -1 exactly when all points lie on a line with positive or negative slope; r = 0 means no linear relationship. — *proved proved here* — `UndergradKB.Statistics.correlation_eq_one_iff`, `UndergradKB.Statistics.correlation_eq_neg_one_iff`, `UndergradKB.Statistics.abs_correlation_eq_one_iff`
- **§12.3**, p.634 [ST-108]: Coefficient of determination r^2 is the fraction of the variation of y explained by the regression line. — *proved proved here* — `UndergradKB.Statistics.sumSqDev_eq_ssr_add_sse`, `UndergradKB.Statistics.correlation_sq_eq_ssr_div`

#### Section 12.4

- **§12.4**, p.642 [ST-109]: Test for the significance of r: under H0 (rho = 0, bivariate normal) t = r sqrt(n-2)/sqrt(1 - r^2) has the Student t distribution with n - 2 degrees of freedom. — *proved proved here* — `UndergradKB.Statistics.hasLaw_correlation_tStatistic`

#### Section 12.5

- **§12.5**, p.646 [ST-110]: Prediction: y-hat = a + bx estimates y at x; the standard error of the estimate is s = sqrt(SSE/(n-2)). — *proved proved here* — `UndergradKB.Statistics.stdErrorEstimate`, `UndergradKB.Statistics.stdErrorEstimate_eq`
- **§12.5**, p.646 [ST-111]: Extrapolation outside the observed range of x is unreliable, interpolation inside it is safer. — *not a result* — –

#### Section 12.6

- **§12.6**, p.647 [ST-112]: Outlier rule for regression: a point whose residual exceeds 2s in absolute value is a potential outlier; influential points change the line strongly when removed. — *not a result* — –

## Chapter 13

5 items; 4 with a Lean name; 4 proved proved here; 1 not a result.


#### Section 13.1

- **§13.1**, p.690 [ST-113]: One-way analysis of variance compares k population means under normality, independence and equal variances. — *not a result* — –

#### Section 13.2

- **§13.2**, p.691 [ST-114]: Sum of squares decomposition: SS_total = SS_between + SS_within, with SS_between = sum n_j (x_j-bar - x-bar)^2 and mean squares MS = SS/df, df_between = k-1, df_within = n-k. — *proved proved here* — `UndergradKB.Statistics.sumSqDev_eq_ssBetween_add_ssWithin`, `UndergradKB.Statistics.msBetween`, `UndergradKB.Statistics.msWithin`, `UndergradKB.Statistics.fStatistic`
- **§13.2**, p.691 [ST-115]: Under H0 (equal means) the ratio F = MS_between/MS_within has the F distribution with k - 1 and n - k degrees of freedom; reject for large F. — *proved proved here* — `UndergradKB.Statistics.hasLaw_fStatistic`

#### Section 13.3

- **§13.3**, p.695 [ST-116]: The F distribution with (d1, d2) degrees of freedom is right-skewed, nonnegative, has mean about 1 for large d2, and is the law of a ratio of two independent scaled chi-square variables. — *proved proved here* — `UndergradKB.Statistics.fDistribution`, `UndergradKB.Statistics.hasLaw_fDistribution`, `UndergradKB.Statistics.fDistribution_Iic_zero`

#### Section 13.4

- **§13.4**, p.701 [ST-117]: Test of two variances: for independent normal samples (s1^2/sigma1^2)/(s2^2/sigma2^2) has the F distribution with n1-1 and n2-1 degrees of freedom; under H0 use s1^2/s2^2. — *proved proved here* — `UndergradKB.Statistics.hasLaw_varianceRatio`, `UndergradKB.Statistics.hasLaw_inv_fDistribution`
