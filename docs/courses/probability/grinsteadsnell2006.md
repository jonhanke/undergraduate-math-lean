# Course outline: Grinstead–Snell (probability)

Generated from [`docs/coverage/probability/checklist.md`](../../coverage/probability/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build Probability` builds this topic.

218 items in 12 chapters; 217 with a Lean name (99.5%).

## Chapter 1

11 items; 11 with a Lean name; 4 proved proved here; 7 in Mathlib.

- **Definition 1.1**, p.26 [PR-001]: A random variable records the outcome of a chance experiment, the sample space is the set of outcomes, and it is discrete if finite or countable. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_1_1`, `MeasureTheory.IsProbabilityMeasure`, `Measurable`
- **Definition 1.2**, p.27 [PR-002]: A distribution function on a finite sample space assigns nonnegative weights m(w) summing to 1, and P(E) is the sum of m over E. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_1_2`, `PMF.toMeasure`, `PMF.toOuterMeasure_apply`, `PMF.toMeasure_apply_finset`

#### Section 1.2

- **§1.2 probability of an event**, p.27 [PR-002]: A distribution function on a finite sample space assigns nonnegative weights m(w) summing to 1, and P(E) is the sum of m over E. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_1_2`, `PMF.toMeasure`, `PMF.toOuterMeasure_apply`, `PMF.toMeasure_apply_finset`
- **Theorem 1.1**, p.30 [PR-003]: Probabilities of events are nonnegative, P(Omega)=1, monotone in the event, and P of a complement is 1-P. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_1_1`, `MeasureTheory.measure_mono`, `MeasureTheory.prob_compl_eq_one_sub`, `MeasureTheory.prob_le_one`
- **Theorem 1.2**, p.31 [PR-004]: For pairwise disjoint events the probability of the union is the sum of the probabilities. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_1_2`, `MeasureTheory.measure_biUnion_finset`, `MeasureTheory.measure_union`
- **Theorem 1.3**, p.31 [PR-005]: If A_1..A_n partition the sample space then P(E) is the sum of P(E and A_i); in particular P(A)=P(A and B)+P(A and not B). — *proved proved here* — `UndergradKB.Probability.measure_eq_sum_inter_partition`, `UndergradKB.Probability.measure_eq_inter_add_inter_compl`
- **Corollary 1.1**, p.32 [PR-005]: If A_1..A_n partition the sample space then P(E) is the sum of P(E and A_i); in particular P(A)=P(A and B)+P(A and not B). — *proved proved here* — `UndergradKB.Probability.measure_eq_sum_inter_partition`, `UndergradKB.Probability.measure_eq_inter_add_inter_compl`
- **Theorem 1.4**, p.32 [PR-006]: Probability of a union of two events: P(A or B)=P(A)+P(B)-P(A and B). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_1_4`, `MeasureTheory.measure_union_add_inter`
- **Definition 1.3**, p.33 [PR-007]: The uniform distribution on an n-element sample space gives each outcome probability 1/n. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_1_3`, `PMF.uniformOfFintype`, `MeasureTheory.Measure.uniformOfFinset`, `ProbabilityTheory.uniformOn`
- **Definition 1.4**, p.36 [PR-008]: Odds in favour of an event with probability p are r:s where r/s=p/(1-p), and p=r/(r+s). — *proved proved here* — `UndergradKB.Probability.prob_eq_of_odds`
- **Example 1.13**, p.37 [PR-009]: A coin tossed until the first head: the first head occurs at toss n with probability 2^-n, and these probabilities sum to 1. — *proved proved here* — `UndergradKB.Probability.firstHead_real_singleton`, `UndergradKB.Probability.firstHead_hasSum`

## Chapter 2

17 items; 17 with a Lean name; 9 proved proved here; 8 in Mathlib.

- **Example 2.1**, p.49 [PR-014]: A spinner or a uniform random point of [0,1] is modelled by Lebesgue measure on [0,1) with density 1; every single point has probability 0. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_2_7`, `MeasureTheory.pdf.IsUniform`, `MeasureTheory.pdf.IsUniform.pdf_eq`
- **Example 2.3**, p.52 [PR-016]: Buffon's needle: a needle of length equal to the line spacing crosses a line with probability 2/pi. — *proved proved here* — `UndergradKB.Probability.buffon_crossing_prob`
- **Example 2.4**, p.54 [PR-089]: The sum of two independent uniform [0,1] variables has the triangular density; the sum of n has the piecewise polynomial density. — *proved proved here* — `UndergradKB.Probability.lintegral_unitDensity_conv`, `UndergradKB.Probability.integral_indicator_Icc_conv`, `UndergradKB.Probability.map_add_uniform`
- **Example 2.7**, p.63 [PR-014]: A spinner or a uniform random point of [0,1] is modelled by Lebesgue measure on [0,1) with density 1; every single point has probability 0. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_2_7`, `MeasureTheory.pdf.IsUniform`, `MeasureTheory.pdf.IsUniform.pdf_eq`

#### Section 2.2

- **§2.2 density function**, p.64 [PR-011]: A density function of a continuous random variable is a function f with P(a<=X<=b)=integral of f from a to b. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_2_1`, `MeasureTheory.pdf`, `MeasureTheory.HasPDF`, `MeasureTheory.map_eq_withDensity_pdf`
- **Example 2.8**, p.64 [PR-015]: A dart hitting a unit disk uniformly: the probability of landing within distance r of the centre is r^2, so the distance has density 2r. — *proved proved here* — `UndergradKB.Probability.measureReal_norm_le_of_uniform_disk`, `UndergradKB.Probability.measureReal_norm_le_eq_integral_of_uniform_disk`
- **Example 2.9**, p.65 [PR-015]: A dart hitting a unit disk uniformly: the probability of landing within distance r of the centre is r^2, so the distance has density 2r. — *proved proved here* — `UndergradKB.Probability.measureReal_norm_le_of_uniform_disk`, `UndergradKB.Probability.measureReal_norm_le_eq_integral_of_uniform_disk`
- **Definition 2.1**, p.67 [PR-011]: A density function of a continuous random variable is a function f with P(a<=X<=b)=integral of f from a to b. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_2_1`, `MeasureTheory.pdf`, `MeasureTheory.HasPDF`, `MeasureTheory.map_eq_withDensity_pdf`
- **Example 2.10**, p.67 [PR-014]: A spinner or a uniform random point of [0,1] is modelled by Lebesgue measure on [0,1) with density 1; every single point has probability 0. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_2_7`, `MeasureTheory.pdf.IsUniform`, `MeasureTheory.pdf.IsUniform.pdf_eq`
- **Example 2.11**, p.67 [PR-015]: A dart hitting a unit disk uniformly: the probability of landing within distance r of the centre is r^2, so the distance has density 2r. — *proved proved here* — `UndergradKB.Probability.measureReal_norm_le_of_uniform_disk`, `UndergradKB.Probability.measureReal_norm_le_eq_integral_of_uniform_disk`
- **Theorem 2.1**, p.69 [PR-013]: If X has density f then F(x) is the integral of f up to x, and F'(x)=f(x) where f is continuous. — *proved proved here* — `UndergradKB.Probability.cdf_withDensity_eq_integral`, `UndergradKB.Probability.hasDerivAt_cdf_withDensity`
- **Definition 2.2**, p.69 [PR-012]: The cumulative distribution function of X is F(x)=P(X<=x). — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_2_2`, `ProbabilityTheory.cdf`, `ProbabilityTheory.cdf_eq_real`
- **§2.2 cumulative distribution function**, p.69 [PR-012]: The cumulative distribution function of X is F(x)=P(X<=x). — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_2_2`, `ProbabilityTheory.cdf`, `ProbabilityTheory.cdf_eq_real`
- **Example 2.14**, p.71 [PR-089]: The sum of two independent uniform [0,1] variables has the triangular density; the sum of n has the piecewise polynomial density. — *proved proved here* — `UndergradKB.Probability.lintegral_unitDensity_conv`, `UndergradKB.Probability.integral_indicator_Icc_conv`, `UndergradKB.Probability.map_add_uniform`
- **Example 2.15**, p.72 [PR-015]: A dart hitting a unit disk uniformly: the probability of landing within distance r of the centre is r^2, so the distance has density 2r. — *proved proved here* — `UndergradKB.Probability.measureReal_norm_le_of_uniform_disk`, `UndergradKB.Probability.measureReal_norm_le_eq_integral_of_uniform_disk`
- **Example 2.17**, p.74 [PR-017]: The exponential density lambda e^(-lambda x) on x>=0 integrates to 1, has cdf 1-e^(-lambda x), and models waiting times between random events. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_2_17`, `ProbabilityTheory.expMeasure`, `ProbabilityTheory.exponentialPDFReal`, `ProbabilityTheory.lintegral_exponentialPDF_eq_one`
- **Example 2.18**, p.77 [PR-010]: Infinitely many tosses of a fair coin have a sample space of 0-1 sequences, which is uncountable, and a probability measure exists on it. — *proved proved here* — `UndergradKB.Probability.infinite_fair_coin_tosses`

## Chapter 3

25 items; 25 with a Lean name; 9 proved proved here; 16 in Mathlib.

- **Example 3.3**, p.85 [PR-024]: Birthday problem: with 23 people the probability that two share a birthday exceeds 1/2. — *proved proved here* — `UndergradKB.Probability.birthday_distinct_lt_half`, `UndergradKB.Probability.birthday_shared_gt_half`
- **Definition 3.1**, p.87 [PR-019]: A permutation of a finite set is a bijection of it onto itself; a k-permutation is an ordered listing of k elements. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_3_1`, `Equiv.Perm`, `Function.Embedding`
- **Theorem 3.1**, p.88 [PR-020]: A set of n elements has n! permutations and n(n-1)...(n-k+1) k-permutations; 0!=1. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_1`, `UndergradKB.Probability.Course.gs_theorem_3_2`, `Fintype.card_perm`, `Nat.card_perm`

#### Section 3.1

- **§3.1 factorials**, p.88 [PR-020]: A set of n elements has n! permutations and n(n-1)...(n-k+1) k-permutations; 0!=1. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_1`, `UndergradKB.Probability.Course.gs_theorem_3_2`, `Fintype.card_perm`, `Nat.card_perm`
- **Definition 3.2**, p.88 [PR-019]: A permutation of a finite set is a bijection of it onto itself; a k-permutation is an ordered listing of k elements. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_3_1`, `Equiv.Perm`, `Function.Embedding`
- **Theorem 3.2**, p.88 [PR-020]: A set of n elements has n! permutations and n(n-1)...(n-k+1) k-permutations; 0!=1. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_1`, `UndergradKB.Probability.Course.gs_theorem_3_2`, `Fintype.card_perm`, `Nat.card_perm`
- **Definition 3.3**, p.89 [PR-021]: Sequences a_n and b_n are asymptotically equal (a_n ~ b_n) if a_n/b_n tends to 1. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_3_3`, `Asymptotics.IsEquivalent`
- **Theorem 3.3**, p.89 [PR-022]: Stirling's formula: n! is asymptotically equal to sqrt(2 pi n) (n/e)^n. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_3`, `Stirling.tendsto_stirlingSeq_sqrt_pi`
- **Definition 3.4**, p.91 [PR-023]: A record of a permutation is a position whose value exceeds all earlier values; snowfall-record model. — *proved proved here* — `UndergradKB.Probability.IsRecord`

#### Section 3.2

- **§3.2 binomial coefficients**, p.101 [PR-026]: C(n,j)=n!/(j!(n-j)!), the number of j-element subsets of an n-element set; it is 0 for j<0 or j>n. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_5`, `Nat.choose_eq_factorial_div_factorial`, `Nat.choose_eq_descFactorial_div_factorial`, `Finset.card_powersetCard`
- **Theorem 3.4**, p.101 [PR-025]: Pascal's recursion: C(n,j)=C(n-1,j)+C(n-1,j-1). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_4`, `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`
- **Theorem 3.5**, p.102 [PR-026]: C(n,j)=n!/(j!(n-j)!), the number of j-element subsets of an n-element set; it is 0 for j<0 or j>n. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_5`, `Nat.choose_eq_factorial_div_factorial`, `Nat.choose_eq_descFactorial_div_factorial`, `Finset.card_powersetCard`
- **Definition 3.5**, p.104 [PR-027]: A Bernoulli trials process is a sequence of n independent experiments each with two outcomes and the same success probability p. — *proved proved here* — `UndergradKB.Probability.hasLaw_sum_bernoulli`
- **Theorem 3.6**, p.106 [PR-028]: In n Bernoulli trials the probability of exactly j successes is C(n,j) p^j q^(n-j). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_6`, `ProbabilityTheory.binomial_real_singleton`, `ProbabilityTheory.map_ncard_setBernoulli_real_singleton`
- **§3.2 binomial distribution**, p.107 [PR-029]: The binomial distribution b(n,p,k) is the law of the number of successes in n Bernoulli trials. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_3_6`, `ProbabilityTheory.binomial`, `PMF.binomial`, `PMF.binomial_apply`
- **Definition 3.6**, p.107 [PR-029]: The binomial distribution b(n,p,k) is the law of the number of successes in n Bernoulli trials. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_3_6`, `ProbabilityTheory.binomial`, `PMF.binomial`, `PMF.binomial_apply`
- **Corollary 3.1**, p.111 [PR-030]: Binomial theorem (a+b)^n = sum C(n,j) a^j b^(n-j); row sums of Pascal's triangle are 2^n and alternating sums are 0. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_7`, `UndergradKB.Probability.Course.gs_corollary_3_1`, `add_pow`, `Nat.sum_range_choose`
- **Theorem 3.7**, p.111 [PR-030]: Binomial theorem (a+b)^n = sum C(n,j) a^j b^(n-j); row sums of Pascal's triangle are 2^n and alternating sums are 0. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_3_7`, `UndergradKB.Probability.Course.gs_corollary_3_1`, `add_pow`, `Nat.sum_range_choose`
- **Theorem 3.8**, p.112 [PR-031]: Inclusion-exclusion for probabilities: P of a union of n events is the alternating sum of the probabilities of intersections. — *proved proved here* — `UndergradKB.Probability.real_biUnion_eq_sum_inter`
- **Example 3.12**, p.113 [PR-032]: Hat-check problem: the probability that a random permutation of n objects has no fixed point tends to 1/e. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_3_12`, `card_derangements_eq_numDerangements`, `numDerangements_sum`, `numDerangements_tendsto_inv_e`
- **Theorem 3.9**, p.130 [PR-033]: An a-shuffle followed by a b-shuffle induces the same distribution on orderings as an ab-shuffle (bijection of pairs of shuffles with ab-shuffles). — *proved proved here* — `UndergradKB.Probability.exists_shuffle_pair_equiv`, `UndergradKB.Probability.card_shuffle_pairs_eq`
- **Theorem 3.10**, p.133 [PR-033]: An a-shuffle followed by a b-shuffle induces the same distribution on orderings as an ab-shuffle (bijection of pairs of shuffles with ab-shuffles). — *proved proved here* — `UndergradKB.Probability.exists_shuffle_pair_equiv`, `UndergradKB.Probability.card_shuffle_pairs_eq`
- **Theorem 3.11**, p.134 [PR-034]: An ordering with r rising sequences arises from C(n+a-r, n) cut-interleaving pairs of an a-shuffle. — *proved proved here* — `UndergradKB.Probability.card_shuffles_eq_choose`

#### Section 3.3

- **§3.3 Eulerian number**, p.135 [PR-035]: Identity a^n = sum over r of C(n+a-r, n) A(n,r), where A(n,r) are Eulerian numbers (orderings with r rising sequences). — *proved proved here* — `UndergradKB.Probability.pow_eq_sum_choose_mul_eulerian`
- **Theorem 3.12**, p.135 [PR-035]: Identity a^n = sum over r of C(n+a-r, n) A(n,r), where A(n,r) are Eulerian numbers (orderings with r rising sequences). — *proved proved here* — `UndergradKB.Probability.pow_eq_sum_choose_mul_eulerian`

## Chapter 4

19 items; 19 with a Lean name; 8 proved proved here; 11 in Mathlib.


#### Section 4.1

- **§4.1 conditional probability**, p.143 [PR-036]: Conditional probability: P(F\|E)=P(E and F)/P(E) when P(E)>0, so P(.\|E) is again a probability measure. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_4_1_conditional_probability`, `ProbabilityTheory.cond`, `ProbabilityTheory.cond_apply`, `ProbabilityTheory.cond_isProbabilityMeasure`
- **§4.1 product rule**, p.143 [PR-037]: Product rule: P(E and F)=P(E) P(F\|E); tree diagrams multiply conditional probabilities along a path. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_4_1_product_rule`, `ProbabilityTheory.cond_mul_eq_inter`, `ProbabilityTheory.cond_cond_eq_cond_inter`
- **Definition 4.1**, p.147 [PR-040]: Events E,F are independent if P(E\|F)=P(E) (and symmetrically) or one has probability 0; equivalently P(E and F)=P(E)P(F). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_4_1`, `ProbabilityTheory.IndepSet`, `ProbabilityTheory.indepSet_iff_measure_inter_eq_mul`
- **Theorem 4.1**, p.148 [PR-040]: Events E,F are independent if P(E\|F)=P(E) (and symmetrically) or one has probability 0; equivalently P(E and F)=P(E)P(F). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_4_1`, `ProbabilityTheory.IndepSet`, `ProbabilityTheory.indepSet_iff_measure_inter_eq_mul`
- **Definition 4.2**, p.149 [PR-041]: Events A_1..A_n are mutually independent if every sub-family has intersection probability equal to the product. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_4_2`, `ProbabilityTheory.iIndepSet`, `ProbabilityTheory.iIndepSet_iff_meas_biInter`
- **Definition 4.3**, p.150 [PR-042]: The joint random variable (X_1..X_n) has outcomes the n-tuples; its distribution is the joint distribution and the distributions of the X_i are the marginals. — *proved proved here* — `UndergradKB.Probability.joint_and_marginal_laws`, `UndergradKB.Probability.joint_and_marginal_laws_pair`
- **§4.1 joint and marginal distributions**, p.151 [PR-042]: The joint random variable (X_1..X_n) has outcomes the n-tuples; its distribution is the joint distribution and the distributions of the X_i are the marginals. — *proved proved here* — `UndergradKB.Probability.joint_and_marginal_laws`, `UndergradKB.Probability.joint_and_marginal_laws_pair`
- **Definition 4.4**, p.151 [PR-043]: Random variables X_1..X_n are mutually independent if P(X_1=r_1,...,X_n=r_n) is the product of the P(X_i=r_i). — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_4_4`, `ProbabilityTheory.iIndepFun`, `ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul`
- **Definition 4.5**, p.152 [PR-044]: An independent trials process is a sequence of mutually independent random variables with the same distribution. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_4_5`, `ProbabilityTheory.iIndepFun`, `ProbabilityTheory.IdentDistrib`
- **§4.1 total probability**, p.154 [PR-038]: Law of total probability: for a partition E_1..E_n, P(F)=sum P(F\|E_i) P(E_i). — *proved proved here* — `UndergradKB.Probability.measure_eq_sum_cond_mul`, `UndergradKB.Probability.real_eq_sum_cond_mul`
- **§4.1 Bayes' formula**, p.154 [PR-039]: Bayes' formula: P(H_i\|E)=P(E\|H_i)P(H_i) divided by the sum of P(E\|H_j)P(H_j) over a partition. — *proved proved here* — `UndergradKB.Probability.real_cond_eq_bayes`

#### Section 4.2

- **§4.2 conditional probability, continuous case**, p.170 [PR-036]: Conditional probability: P(F\|E)=P(E and F)/P(E) when P(E)>0, so P(.\|E) is again a probability measure. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_4_1_conditional_probability`, `ProbabilityTheory.cond`, `ProbabilityTheory.cond_apply`, `ProbabilityTheory.cond_isProbabilityMeasure`
- **Example 4.20**, p.171 [PR-018]: The exponential waiting time is memoryless: P(T>r+s \| T>r)=P(T>s). — *proved proved here* — `UndergradKB.Probability.expMeasure_memoryless`
- **Theorem 4.2**, p.173 [PR-047]: Continuous random variables are independent iff the joint density is the product of the marginal densities. — *proved proved here* — `UndergradKB.Probability.indepFun_iff_joint_density`
- **Definition 4.6**, p.173 [PR-045]: The joint cumulative distribution function F(x_1..x_n)=P(X_1<=x_1,...,X_n<=x_n) and joint density. — *proved proved here* — `UndergradKB.Probability.jointLaw_eq_of_jointCdf_eq`
- **Definition 4.7**, p.173 [PR-046]: Continuous random variables are mutually independent iff the joint cdf is the product of the individual cdfs. — *proved proved here* — `UndergradKB.Probability.indepFun_iff_cdf_mul`
- **Theorem 4.3**, p.175 [PR-048]: Continuous functions of independent random variables, each applied to one variable, are independent. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_4_3`, `ProbabilityTheory.iIndepFun.comp`, `ProbabilityTheory.IndepFun.comp`

#### Section 4.3

- **§4.3 beta density**, p.176 [PR-049]: The beta density x^(a-1)(1-x)^(b-1)/B(a,b) on [0,1] (posterior for an unknown success probability). — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_4_3_beta_density`, `ProbabilityTheory.betaMeasure`
- **Definition 4.8**, p.176 [PR-044]: An independent trials process is a sequence of mutually independent random variables with the same distribution. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_4_5`, `ProbabilityTheory.iIndepFun`, `ProbabilityTheory.IdentDistrib`

## Chapter 5

25 items; 25 with a Lean name; 15 proved proved here; 10 in Mathlib.


#### Section 5.1

- **§5.1 uniform distribution**, p.191 [PR-007]: The uniform distribution on an n-element sample space gives each outcome probability 1/n. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_1_3`, `PMF.uniformOfFintype`, `MeasureTheory.Measure.uniformOfFinset`, `ProbabilityTheory.uniformOn`
- **§5.1 geometric distribution**, p.193 [PR-050]: Geometric distribution: the first success in Bernoulli trials occurs at trial j with probability q^(j-1) p. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_1_geometric_distribution`, `ProbabilityTheory.geometricMeasure`, `ProbabilityTheory.geometricMeasure_singleton`
- **§5.1 memoryless property**, p.194 [PR-051]: The geometric distribution is memoryless: P(T>r+s \| T>r)=P(T>s). — *proved proved here* — `UndergradKB.Probability.trialsLaw_memoryless`
- **§5.1 negative binomial distribution**, p.195 [PR-052]: Negative binomial: the number of trials to obtain k successes has probability C(x-1,k-1) p^k q^(x-k). — *proved proved here* — `UndergradKB.Probability.hasSum_negBinomMass`, `UndergradKB.Probability.hasSum_negBinomMass_trial`
- **Example 5.2**, p.195 [PR-052]: Negative binomial: the number of trials to obtain k successes has probability C(x-1,k-1) p^k q^(x-k). — *proved proved here* — `UndergradKB.Probability.hasSum_negBinomMass`, `UndergradKB.Probability.hasSum_negBinomMass_trial`
- **§5.1 Poisson distribution**, p.197 [PR-053]: Poisson distribution with mean lambda: P(X=j)=e^(-lambda) lambda^j/j!. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_1_poisson_distribution`, `ProbabilityTheory.poissonMeasure`, `ProbabilityTheory.poissonMeasure_singleton`, `ProbabilityTheory.hasSum_one_poissonMeasure`
- **§5.1 Poisson approximation to the binomial**, p.197 [PR-054]: Poisson approximation: if n p_n tends to lambda then C(n,k) p_n^k (1-p_n)^(n-k) tends to e^(-lambda) lambda^k/k!. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_1_poisson_approximation`, `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`
- **Example 5.3**, p.197 [PR-054]: Poisson approximation: if n p_n tends to lambda then C(n,k) p_n^k (1-p_n)^(n-k) tends to e^(-lambda) lambda^k/k!. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_1_poisson_approximation`, `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`
- **Example 5.4**, p.199 [PR-053]: Poisson distribution with mean lambda: P(X=j)=e^(-lambda) lambda^j/j!. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_1_poisson_distribution`, `ProbabilityTheory.poissonMeasure`, `ProbabilityTheory.poissonMeasure_singleton`, `ProbabilityTheory.hasSum_one_poissonMeasure`
- **Example 5.5**, p.199 [PR-053]: Poisson distribution with mean lambda: P(X=j)=e^(-lambda) lambda^j/j!. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_1_poisson_distribution`, `ProbabilityTheory.poissonMeasure`, `ProbabilityTheory.poissonMeasure_singleton`, `ProbabilityTheory.hasSum_one_poissonMeasure`
- **§5.1 hypergeometric distribution**, p.201 [PR-055]: Hypergeometric distribution: drawing without replacement, P(X=k)=C(a,k)C(b,n-k)/C(a+b,n). — *proved proved here* — `UndergradKB.Probability.sum_hyperMass`, `UndergradKB.Probability.hyperMass_mean`

#### Section 5.2

- **§5.2 exponential density**, p.213 [PR-017]: The exponential density lambda e^(-lambda x) on x>=0 integrates to 1, has cdf 1-e^(-lambda x), and models waiting times between random events. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_2_17`, `ProbabilityTheory.expMeasure`, `ProbabilityTheory.exponentialPDFReal`, `ProbabilityTheory.lintegral_exponentialPDF_eq_one`
- **§5.2 gamma density**, p.213 [PR-056]: The gamma density generalises the exponential density (shape parameter n, rate lambda) and integrates to 1. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_2_gamma_density`, `ProbabilityTheory.gammaMeasure`, `ProbabilityTheory.gammaPDFReal`, `ProbabilityTheory.isProbabilityMeasure_gammaMeasure`
- **Theorem 5.1**, p.218 [PR-062]: If phi is strictly increasing, Y=phi(X) has cdf F_Y(y)=F_X(phi^-1(y)) and density f_X(phi^-1(y)) times the derivative of phi^-1. — *proved proved here* — `UndergradKB.Probability.cdf_map_strictMono`, `UndergradKB.Probability.measure_comp_le_strictMono`, `UndergradKB.Probability.map_withDensity_strictMono`
- **Corollary 5.1**, p.218 [PR-062]: If phi is strictly increasing, Y=phi(X) has cdf F_Y(y)=F_X(phi^-1(y)) and density f_X(phi^-1(y)) times the derivative of phi^-1. — *proved proved here* — `UndergradKB.Probability.cdf_map_strictMono`, `UndergradKB.Probability.measure_comp_le_strictMono`, `UndergradKB.Probability.map_withDensity_strictMono`
- **§5.2 normal density**, p.220 [PR-057]: The normal density with parameters mu, sigma is e^(-(x-mu)^2/(2 sigma^2))/(sigma sqrt(2 pi)); standard normal has mu=0, sigma=1. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_5_2_normal_density`, `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.gaussianPDFReal`, `ProbabilityTheory.gaussianPDFReal_def`
- **Corollary 5.2**, p.220 [PR-063]: Inverse transform sampling: if U is uniform on [0,1] and F is a strictly increasing cdf then F^-1(U) has cdf F. — *proved proved here* — `UndergradKB.Probability.measure_inverse_transform_le`, `UndergradKB.Probability.cdf_inverse_transform`
- **§5.2 standardized normal**, p.221 [PR-058]: If Z is standard normal then X=sigma Z+mu is normal with parameters mu, sigma, and the standardized version of X is (X-mu)/sigma. — *proved proved here* — `UndergradKB.Probability.hasLaw_gaussian_affine`, `UndergradKB.Probability.hasLaw_gaussian_standardize`
- **§5.2 standardized version**, p.222 [PR-058]: If Z is standard normal then X=sigma Z+mu is normal with parameters mu, sigma, and the standardized version of X is (X-mu)/sigma. — *proved proved here* — `UndergradKB.Probability.hasLaw_gaussian_affine`, `UndergradKB.Probability.hasLaw_gaussian_standardize`
- **§5.2 Maxwell density**, p.223 [PR-059]: Maxwell and Rayleigh densities: laws of the length of a normal vector in 3 and 2 dimensions. — *proved proved here* — `UndergradKB.Probability.measureReal_sqrt_sq_add_sq_le`, `UndergradKB.Probability.measureReal_sqrt_sum_sq_le`
- **§5.2 Rayleigh density**, p.223 [PR-059]: Maxwell and Rayleigh densities: laws of the length of a normal vector in 3 and 2 dimensions. — *proved proved here* — `UndergradKB.Probability.measureReal_sqrt_sq_add_sq_le`, `UndergradKB.Probability.measureReal_sqrt_sum_sq_le`
- **Example 5.9**, p.223 [PR-059]: Maxwell and Rayleigh densities: laws of the length of a normal vector in 3 and 2 dimensions. — *proved proved here* — `UndergradKB.Probability.measureReal_sqrt_sq_add_sq_le`, `UndergradKB.Probability.measureReal_sqrt_sum_sq_le`
- **§5.2 chi-squared density**, p.225 [PR-060]: Chi-squared density with n degrees of freedom: law of the sum of squares of n independent standard normals (a gamma density). — *proved proved here* — `UndergradKB.Probability.map_sq_gaussianReal_eq_gammaMeasure`, `UndergradKB.Probability.hasLaw_sq_gammaMeasure`, `UndergradKB.Probability.map_add_gammaMeasure`, `UndergradKB.Probability.hasLaw_sum_sq_gammaMeasure`
- **§5.2 Cauchy density**, p.226 [PR-061]: The Cauchy density a/(pi(a^2+x^2)); the tangent of a uniform angle has a Cauchy law (mirror and wall experiment). — *proved proved here* — `UndergradKB.Probability.measureReal_tan_le_of_uniform`, `UndergradKB.Probability.map_tan_of_uniform`
- **Example 5.11**, p.226 [PR-061]: The Cauchy density a/(pi(a^2+x^2)); the tangent of a uniform angle has a Cauchy law (mirror and wall experiment). — *proved proved here* — `UndergradKB.Probability.measureReal_tan_le_of_uniform`, `UndergradKB.Probability.map_tan_of_uniform`

## Chapter 6

38 items; 38 with a Lean name; 17 proved proved here; 21 in Mathlib.


#### Section 6.2

- **§6.2 standard deviation**, p.223 [PR-071]: The variance V(X)=E((X-mu)^2); the standard deviation is its square root. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_3`, `ProbabilityTheory.variance`, `ProbabilityTheory.variance_eq_integral`
- **Definition 6.1**, p.234 [PR-064]: The expected value of a discrete random variable is the sum of x m(x), provided the sum converges absolutely. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_1`, `MeasureTheory.integral`, `MeasureTheory.integral_fintype`, `MeasureTheory.integral_countable`

#### Section 6.1

- **§6.1 expected value**, p.234 [PR-064]: The expected value of a discrete random variable is the sum of x m(x), provided the sum converges absolutely. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_1`, `MeasureTheory.integral`, `MeasureTheory.integral_fintype`, `MeasureTheory.integral_countable`
- **Example 6.4**, p.236 [PR-079]: A geometrically distributed T has E(T)=1/p and V(T)=q/p^2. — *proved proved here* — `UndergradKB.Probability.trialsLaw_mean`, `UndergradKB.Probability.trialsLaw_variance_integral`, `UndergradKB.Probability.geometric_expectation`, `UndergradKB.Probability.geometric_variance`
- **Theorem 6.1**, p.238 [PR-065]: E(phi(X)) is the sum of phi(x) m(x) (discrete); for density f it is the integral of phi(x) f(x) dx. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_1`, `UndergradKB.Probability.Course.gs_theorem_6_11`, `MeasureTheory.integral_map`
- **Theorem 6.2**, p.239 [PR-067]: Expectation is linear: E(X+Y)=E(X)+E(Y) and E(cX)=c E(X) (no independence needed). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_2`, `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul`, `MeasureTheory.integral_smul`
- **Example 6.8**, p.240 [PR-085]: The expected number of fixed points of a random permutation is 1 for every n (linearity of expectation on indicators). — *proved proved here* — `UndergradKB.Probability.sum_fixedPoints_card`, `UndergradKB.Probability.average_fixedPoints_card`
- **Theorem 6.3**, p.241 [PR-068]: The number of successes in n Bernoulli trials has expected value np. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_3`, `ProbabilityTheory.integral_of_hasLaw_binomial`, `ProbabilityTheory.integral_binomial`
- **Theorem 6.4**, p.241 [PR-069]: For independent random variables E(XY)=E(X)E(Y). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_4`, `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`, `ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral`
- **Example 6.11**, p.242 [PR-084]: The expected number of records in a random permutation of n values is 1+1/2+...+1/n. — *proved proved here* — `UndergradKB.Probability.sum_records_card`, `UndergradKB.Probability.average_records_card`
- **Definition 6.2**, p.247 [PR-070]: Conditional expectation of X given an event F is the sum of x_j P(X=x_j\|F); and E(X) is the sum of E(X\|F_j) P(F_j) over a partition. — *proved proved here* — `UndergradKB.Probability.integral_eq_sum_condExpEvent`
- **Theorem 6.5**, p.247 [PR-070]: Conditional expectation of X given an event F is the sum of x_j P(X=x_j\|F); and E(X) is the sum of E(X\|F_j) P(F_j) over a partition. — *proved proved here* — `UndergradKB.Probability.integral_eq_sum_condExpEvent`
- **Example 6.15**, p.249 [PR-086]: In a fair heads-or-tails game the fortune S_n has E(S_n)=0 and V(S_n)=n. — *proved proved here* — `UndergradKB.Probability.fair_game_mean_variance`
- **Definition 6.3**, p.265 [PR-071]: The variance V(X)=E((X-mu)^2); the standard deviation is its square root. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_3`, `ProbabilityTheory.variance`, `ProbabilityTheory.variance_eq_integral`
- **Theorem 6.6**, p.266 [PR-072]: V(X)=E(X^2)-E(X)^2. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_6`, `ProbabilityTheory.variance_eq_sub`
- **Theorem 6.7**, p.267 [PR-073]: V(cX)=c^2 V(X) and V(X+c)=V(X). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_7`, `ProbabilityTheory.variance_const_mul`, `ProbabilityTheory.variance_smul`, `ProbabilityTheory.variance_add_const`
- **Theorem 6.8**, p.267 [PR-074]: For independent X,Y the variance adds: V(X+Y)=V(X)+V(Y). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_8`, `ProbabilityTheory.IndepFun.variance_fun_add`, `ProbabilityTheory.variance_add`
- **Theorem 6.9**, p.268 [PR-075]: For an independent trials process, S_n has mean n mu and variance n sigma^2, and the average A_n=S_n/n has mean mu and variance sigma^2/n. — *proved proved here* — `UndergradKB.Probability.sum_mean_variance`, `UndergradKB.Probability.average_mean_variance`
- **Example 6.19**, p.270 [PR-079]: A geometrically distributed T has E(T)=1/p and V(T)=q/p^2. — *proved proved here* — `UndergradKB.Probability.trialsLaw_mean`, `UndergradKB.Probability.trialsLaw_variance_integral`, `UndergradKB.Probability.geometric_expectation`, `UndergradKB.Probability.geometric_variance`

#### Section 6.2

- **§6.2 standardized random variable**, p.272 [PR-077]: The standardized random variable X*=(X-mu)/sigma has mean 0 and variance 1. — *proved proved here* — `UndergradKB.Probability.integral_standardize`, `UndergradKB.Probability.variance_standardize`

#### Section 6.1

- **§6.1 expected value, continuous**, p.276 [PR-066]: The expected value of a continuous random variable with density f is the integral of x f(x) dx, when the integral of \|x\| f(x) converges. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_4`, `MeasureTheory.integral`
- **Definition 6.4**, p.276 [PR-066]: The expected value of a continuous random variable with density f is the integral of x f(x) dx, when the integral of \|x\| f(x) converges. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_4`, `MeasureTheory.integral`
- **Theorem 6.10**, p.277 [PR-067]: Expectation is linear: E(X+Y)=E(X)+E(Y) and E(cX)=c E(X) (no independence needed). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_2`, `MeasureTheory.integral_add`, `MeasureTheory.integral_const_mul`, `MeasureTheory.integral_smul`
- **Example 6.20**, p.277 [PR-080]: A uniform random variable on [0,1] has mean 1/2 and variance 1/12. — *proved proved here* — `UndergradKB.Probability.integral_uniform_Icc`, `UndergradKB.Probability.variance_uniform_Icc`, `UndergradKB.Probability.integral_of_isUniform_Icc`, `UndergradKB.Probability.variance_of_isUniform_Icc`
- **Theorem 6.11**, p.278 [PR-065]: E(phi(X)) is the sum of phi(x) m(x) (discrete); for density f it is the integral of phi(x) f(x) dx. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_1`, `UndergradKB.Probability.Course.gs_theorem_6_11`, `MeasureTheory.integral_map`
- **Theorem 6.12**, p.278 [PR-069]: For independent random variables E(XY)=E(X)E(Y). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_4`, `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`, `ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral`
- **Definition 6.5**, p.279 [PR-071]: The variance V(X)=E((X-mu)^2); the standard deviation is its square root. — *in Mathlib* — `UndergradKB.Probability.Course.gs_definition_6_3`, `ProbabilityTheory.variance`, `ProbabilityTheory.variance_eq_integral`
- **Theorem 6.13**, p.280 [PR-076]: For a density f the variance is the integral of (x-mu)^2 f(x) dx. — *proved proved here* — `UndergradKB.Probability.variance_eq_integral_pdf`
- **Theorem 6.14**, p.280 [PR-073]: V(cX)=c^2 V(X) and V(X+c)=V(X). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_7`, `ProbabilityTheory.variance_const_mul`, `ProbabilityTheory.variance_smul`, `ProbabilityTheory.variance_add_const`
- **Theorem 6.15**, p.280 [PR-072]: V(X)=E(X^2)-E(X)^2. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_6`, `ProbabilityTheory.variance_eq_sub`
- **Theorem 6.16**, p.280 [PR-074]: For independent X,Y the variance adds: V(X+Y)=V(X)+V(Y). — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_6_8`, `ProbabilityTheory.IndepFun.variance_fun_add`, `ProbabilityTheory.variance_add`
- **Example 6.25**, p.280 [PR-080]: A uniform random variable on [0,1] has mean 1/2 and variance 1/12. — *proved proved here* — `UndergradKB.Probability.integral_uniform_Icc`, `UndergradKB.Probability.variance_uniform_Icc`, `UndergradKB.Probability.integral_of_isUniform_Icc`, `UndergradKB.Probability.variance_of_isUniform_Icc`
- **Example 6.26**, p.281 [PR-081]: An exponential random variable with parameter lambda has mean 1/lambda and variance 1/lambda^2. — *proved proved here* — `UndergradKB.Probability.integral_expMeasure`, `UndergradKB.Probability.variance_expMeasure`
- **Example 6.27**, p.281 [PR-082]: A standard normal variable has mean 0 and variance 1; normal(mu, sigma) has mean mu and variance sigma^2. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_6_27`, `ProbabilityTheory.integral_id_gaussianReal`, `ProbabilityTheory.variance_id_gaussianReal`
- **Example 6.28**, p.282 [PR-083]: The Cauchy density has no expected value, since the integral of \|x\| f(x) diverges. — *proved proved here* — `UndergradKB.Probability.not_integrable_cauchyMeasure`
- **Corollary 6.1**, p.283 [PR-075]: For an independent trials process, S_n has mean n mu and variance n sigma^2, and the average A_n=S_n/n has mean mu and variance sigma^2/n. — *proved proved here* — `UndergradKB.Probability.sum_mean_variance`, `UndergradKB.Probability.average_mean_variance`

#### Section 6.3

- **§6.3 covariance**, p.289 [PR-078]: Covariance cov(X,Y)=E((X-mu_X)(Y-mu_Y)) (and correlation rho=cov/(sigma_X sigma_Y)); independent variables are uncorrelated. — *proved proved here* — `UndergradKB.Probability.IndepFun.correlation_eq_zero`, `UndergradKB.Probability.abs_correlation_le_one`
- **§6.3 correlation**, p.289 [PR-078]: Covariance cov(X,Y)=E((X-mu_X)(Y-mu_Y)) (and correlation rho=cov/(sigma_X sigma_Y)); independent variables are uncorrelated. — *proved proved here* — `UndergradKB.Probability.IndepFun.correlation_eq_zero`, `UndergradKB.Probability.abs_correlation_le_one`

## Chapter 7

10 items; 10 with a Lean name; 9 proved proved here; 1 in Mathlib.

- **Definition 7.1**, p.294 [PR-087]: The convolution of integer-valued distributions is (m1*m2)(j)=sum_k m1(k) m2(j-k), and for independent X,Y the sum X+Y has distribution m1*m2. — *proved proved here* — `UndergradKB.Probability.measure_add_eq_tsum_int`

#### Section 7.1

- **§7.1 distribution of a sum**, p.295 [PR-087]: The convolution of integer-valued distributions is (m1*m2)(j)=sum_k m1(k) m2(j-k), and for independent X,Y the sum X+Y has distribution m1*m2. — *proved proved here* — `UndergradKB.Probability.measure_add_eq_tsum_int`
- **Theorem 7.1**, p.299 [PR-088]: For independent X,Y with densities f,g the sum has density (f*g)(z)=integral of f(z-y) g(y) dy. — *proved proved here* — `UndergradKB.Probability.map_add_eq_withDensity_convolution`
- **Definition 7.2**, p.299 [PR-088]: For independent X,Y with densities f,g the sum has density (f*g)(z)=integral of f(z-y) g(y) dy. — *proved proved here* — `UndergradKB.Probability.map_add_eq_withDensity_convolution`
- **Example 7.3**, p.300 [PR-089]: The sum of two independent uniform [0,1] variables has the triangular density; the sum of n has the piecewise polynomial density. — *proved proved here* — `UndergradKB.Probability.lintegral_unitDensity_conv`, `UndergradKB.Probability.integral_indicator_Icc_conv`, `UndergradKB.Probability.map_add_uniform`
- **Example 7.4**, p.300 [PR-090]: The sum of two independent exponential variables with rate lambda has the gamma density lambda^2 x e^(-lambda x). — *proved proved here* — `UndergradKB.Probability.lintegral_gammaPDF_one_conv`, `UndergradKB.Probability.map_add_expMeasure`
- **Example 7.5**, p.302 [PR-091]: The sum of independent normal variables is normal with means and variances added. — *in Mathlib* — `UndergradKB.Probability.Course.gs_example_7_5`, `ProbabilityTheory.gaussianReal_conv_gaussianReal`, `ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun`
- **Example 7.6**, p.302 [PR-092]: The average of n independent standard Cauchy variables is again Cauchy. — *proved proved here* — `UndergradKB.Probability.cauchy_sum_two`, `UndergradKB.Probability.cauchy_average_two`, `UndergradKB.Probability.cauchy_average`
- **Example 7.7**, p.303 [PR-060]: Chi-squared density with n degrees of freedom: law of the sum of squares of n independent standard normals (a gamma density). — *proved proved here* — `UndergradKB.Probability.map_sq_gaussianReal_eq_gammaMeasure`, `UndergradKB.Probability.hasLaw_sq_gammaMeasure`, `UndergradKB.Probability.map_add_gammaMeasure`, `UndergradKB.Probability.hasLaw_sum_sq_gammaMeasure`
- **Example 7.9**, p.307 [PR-089]: The sum of two independent uniform [0,1] variables has the triangular density; the sum of n has the piecewise polynomial density. — *proved proved here* — `UndergradKB.Probability.lintegral_unitDensity_conv`, `UndergradKB.Probability.integral_indicator_Icc_conv`, `UndergradKB.Probability.map_add_uniform`

## Chapter 8

5 items; 5 with a Lean name; 3 proved proved here; 2 in Mathlib.

- **Theorem 8.1**, p.313 [PR-094]: Chebyshev inequality: P(\|X-mu\|>=eps) <= V(X)/eps^2, for discrete or continuous X with finite variance. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_8_1`, `UndergradKB.Probability.Course.gs_theorem_8_3`, `ProbabilityTheory.meas_ge_le_variance_div_sq`, `ProbabilityTheory.meas_ge_le_evariance_div_sq`
- **Theorem 8.2**, p.315 [PR-095]: Law of large numbers: for an independent trials process with finite mean mu and variance, P(\|S_n/n-mu\|>=eps) tends to 0 for every eps>0. — *proved proved here* — `UndergradKB.Probability.weak_law_chebyshev_bound`, `UndergradKB.Probability.weak_law_of_large_numbers`
- **Theorem 8.3**, p.324 [PR-094]: Chebyshev inequality: P(\|X-mu\|>=eps) <= V(X)/eps^2, for discrete or continuous X with finite variance. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_8_1`, `UndergradKB.Probability.Course.gs_theorem_8_3`, `ProbabilityTheory.meas_ge_le_variance_div_sq`, `ProbabilityTheory.meas_ge_le_evariance_div_sq`
- **Theorem 8.4**, p.324 [PR-095]: Law of large numbers: for an independent trials process with finite mean mu and variance, P(\|S_n/n-mu\|>=eps) tends to 0 for every eps>0. — *proved proved here* — `UndergradKB.Probability.weak_law_chebyshev_bound`, `UndergradKB.Probability.weak_law_of_large_numbers`
- **Example 8.8**, p.328 [PR-092]: The average of n independent standard Cauchy variables is again Cauchy. — *proved proved here* — `UndergradKB.Probability.cauchy_sum_two`, `UndergradKB.Probability.cauchy_average_two`, `UndergradKB.Probability.cauchy_average`

## Chapter 9

7 items; 7 with a Lean name; 5 proved proved here; 2 in Mathlib.

- **Definition 9.1**, p.334 [PR-096]: The standardized sum S_n* = (S_n-np)/sqrt(npq) has mean 0 and variance 1. — *proved proved here* — `UndergradKB.Probability.integral_standardize_sum`, `UndergradKB.Probability.variance_standardize_sum`
- **Theorem 9.1**, p.336 [PR-097]: Local limit theorem for the binomial: sqrt(npq) b(n,p,np+x sqrt(npq)) tends to the standard normal density. — *proved proved here* — `UndergradKB.Probability.local_limit_binomial`, `UndergradKB.Probability.local_limit_binomial_nearest`
- **Theorem 9.2**, p.338 [PR-098]: Central limit theorem for Bernoulli trials: P(a<=S_n*<=b) tends to the integral of the standard normal density from a to b. — *proved proved here* — `UndergradKB.Probability.clt_bernoulli_interval`
- **Theorem 9.3**, p.350 [PR-099]: Local limit theorem: for iid lattice variables with span 1, P(S_n=j) is asymptotic to the normal density term phi(x_j)/(sigma sqrt n). — *proved proved here* — `UndergradKB.Probability.local_limit_lattice`, `UndergradKB.Probability.local_limit_lattice_ratio`
- **Theorem 9.4**, p.351 [PR-100]: Central limit theorem: for iid variables with mean mu and variance sigma^2 the standardized sum (S_n-n mu)/(sigma sqrt n) converges in distribution to the standard normal. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_9_4`, `UndergradKB.Probability.Course.gs_theorem_9_6`, `UndergradKB.Probability.clt_iid_interval`, `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`
- **Theorem 9.5**, p.353 [PR-101]: Central limit theorem for independent, not identically distributed bounded discrete variables with variances s_n^2 growing. — *proved proved here* — `UndergradKB.Probability.clt_bounded`, `UndergradKB.Probability.clt_bounded_interval`
- **Theorem 9.6**, p.365 [PR-100]: Central limit theorem: for iid variables with mean mu and variance sigma^2 the standardized sum (S_n-n mu)/(sigma sqrt n) converges in distribution to the standard normal. — *in Mathlib* — `UndergradKB.Probability.Course.gs_theorem_9_4`, `UndergradKB.Probability.Course.gs_theorem_9_6`, `UndergradKB.Probability.clt_iid_interval`, `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`

## Chapter 10

17 items; 17 with a Lean name; 13 proved proved here; 4 in Mathlib.


#### Section 10.1

- **§10.1 moment generating function**, p.374 [PR-102]: The moment generating function g(t)=E(e^(tX)); its derivatives at 0 give the moments E(X^k). — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_10_1_moment_generating_function`, `ProbabilityTheory.mgf`, `ProbabilityTheory.iteratedDeriv_mgf_zero`, `ProbabilityTheory.moment`
- **Example 10.1**, p.375 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`
- **Example 10.2**, p.375 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`
- **Example 10.3**, p.375 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`
- **Theorem 10.1**, p.376 [PR-103]: For a discrete variable with finite range, the generating function g determines the distribution p and conversely. — *proved proved here* — `UndergradKB.Probability.eq_of_genFun_eq`
- **Example 10.4**, p.376 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`

#### Section 10.2

- **§10.2 generating function of a sum**, p.378 [PR-104]: The generating function of an independent sum is the product of the generating functions. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_10_2_generating_function_of_a_sum`, `ProbabilityTheory.IndepFun.mgf_add`, `ProbabilityTheory.iIndepFun.mgf_sum`
- **Example 10.5**, p.379 [PR-093]: The sum of independent binomial (same p) variables is binomial; the sum of independent geometric variables is negative binomial. — *proved proved here* — `UndergradKB.Probability.binomial_mass_convolution`, `UndergradKB.Probability.hasLaw_add_binomial`
- **Example 10.6**, p.380 [PR-093]: The sum of independent binomial (same p) variables is binomial; the sum of independent geometric variables is negative binomial. — *proved proved here* — `UndergradKB.Probability.binomial_mass_convolution`, `UndergradKB.Probability.hasLaw_add_binomial`
- **Theorem 10.2**, p.388 [PR-106]: Branching process: the probability of eventual extinction is the smallest root of z=h(z); it is 1 if the mean offspring is at most 1 and less than 1 otherwise. — *proved proved here* — `UndergradKB.Probability.extinction_smallest_root`, `UndergradKB.Probability.extinction_prob_eq_one`, `UndergradKB.Probability.extinction_prob_lt_one`

#### Section 10.3

- **§10.3 moments**, p.401 [PR-102]: The moment generating function g(t)=E(e^(tX)); its derivatives at 0 give the moments E(X^k). — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_10_1_moment_generating_function`, `ProbabilityTheory.mgf`, `ProbabilityTheory.iteratedDeriv_mgf_zero`, `ProbabilityTheory.moment`
- **Example 10.15**, p.402 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`
- **Example 10.16**, p.403 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`
- **Example 10.17**, p.403 [PR-105]: Moment generating functions of standard laws: uniform, binomial (pe^t+q)^n, geometric, Poisson e^(lambda(e^t-1)), exponential, normal e^(mu t+sigma^2 t^2/2). — *proved proved here* — `UndergradKB.Probability.mgf_uniform_unit`, `UndergradKB.Probability.mgf_exponential`, `UndergradKB.Probability.mgf_normal`, `UndergradKB.Probability.mgf_uniform_discrete`
- **Theorem 10.3**, p.404 [PR-107]: For a bounded continuous variable the series sum mu_k t^k/k! converges to g(t). — *proved proved here* — `UndergradKB.Probability.hasSum_moments_mgf`
- **§10.3 characteristic function**, p.405 [PR-109]: The characteristic function k_X(tau)=E(e^(i tau X)) is defined for every random variable. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_10_3_characteristic_function`, `MeasureTheory.charFun`
- **Theorem 10.4**, p.405 [PR-108]: For a bounded variable the moment generating function determines the density. — *proved proved here* — `UndergradKB.Probability.map_eq_of_mgf_eq_of_bounded`

## Chapter 11

32 items; 31 with a Lean name; 30 proved proved here; 1 in Mathlib; 1 not formalized.


#### Section 11.1

- **§11.1 Markov chain and transition matrix**, p.413 [PR-110]: A Markov chain has states s_1..s_r and transition probabilities p_ij forming a stochastic matrix, with the next state depending only on the present one. — *proved proved here* — `UndergradKB.Probability.pathProb_snoc`, `UndergradKB.Probability.sum_pathProb`
- **Theorem 11.1**, p.415 [PR-111]: The (i,j) entry of P^n is the probability of moving from s_i to s_j in n steps; the distribution after n steps is u P^n. — *proved proved here* — `UndergradKB.Probability.markov_dist_after_n_steps`, `UndergradKB.Probability.markov_nstep_prob`, `UndergradKB.Probability.markov_dist_after_n_steps_prob`
- **Theorem 11.2**, p.417 [PR-111]: The (i,j) entry of P^n is the probability of moving from s_i to s_j in n steps; the distribution after n steps is u P^n. — *proved proved here* — `UndergradKB.Probability.markov_dist_after_n_steps`, `UndergradKB.Probability.markov_nstep_prob`, `UndergradKB.Probability.markov_dist_after_n_steps_prob`
- **Definition 11.1**, p.424 [PR-112]: Absorbing state (p_ii=1), absorbing chain, transient state. — *proved proved here* — `UndergradKB.Probability.IsAbsorbingState`, `UndergradKB.Probability.IsAbsorbingChain`, `UndergradKB.Probability.Transient`
- **Definition 11.2**, p.424 [PR-112]: Absorbing state (p_ii=1), absorbing chain, transient state. — *proved proved here* — `UndergradKB.Probability.IsAbsorbingState`, `UndergradKB.Probability.IsAbsorbingChain`, `UndergradKB.Probability.Transient`
- **Theorem 11.3**, p.425 [PR-113]: In an absorbing chain absorption occurs with probability 1 (Q^n tends to 0). — *proved proved here* — `UndergradKB.Probability.absorbQ_pow_tendsto_zero`, `UndergradKB.Probability.absorption_certain`
- **Theorem 11.4**, p.426 [PR-114]: For an absorbing chain N=(I-Q)^-1=I+Q+Q^2+... gives expected numbers of visits; expected absorption times are t=Nc and absorption probabilities are B=NR. — *proved proved here* — `UndergradKB.Probability.fundamentalMatrix_spec`, `UndergradKB.Probability.hasSum_visits`, `UndergradKB.Probability.hasSum_absorption_time`, `UndergradKB.Probability.absorption_prob_tendsto`
- **Definition 11.3**, p.427 [PR-114]: For an absorbing chain N=(I-Q)^-1=I+Q+Q^2+... gives expected numbers of visits; expected absorption times are t=Nc and absorption probabilities are B=NR. — *proved proved here* — `UndergradKB.Probability.fundamentalMatrix_spec`, `UndergradKB.Probability.hasSum_visits`, `UndergradKB.Probability.hasSum_absorption_time`, `UndergradKB.Probability.absorption_prob_tendsto`
- **Theorem 11.5**, p.427 [PR-114]: For an absorbing chain N=(I-Q)^-1=I+Q+Q^2+... gives expected numbers of visits; expected absorption times are t=Nc and absorption probabilities are B=NR. — *proved proved here* — `UndergradKB.Probability.fundamentalMatrix_spec`, `UndergradKB.Probability.hasSum_visits`, `UndergradKB.Probability.hasSum_absorption_time`, `UndergradKB.Probability.absorption_prob_tendsto`
- **Theorem 11.6**, p.428 [PR-114]: For an absorbing chain N=(I-Q)^-1=I+Q+Q^2+... gives expected numbers of visits; expected absorption times are t=Nc and absorption probabilities are B=NR. — *proved proved here* — `UndergradKB.Probability.fundamentalMatrix_spec`, `UndergradKB.Probability.hasSum_visits`, `UndergradKB.Probability.hasSum_absorption_time`, `UndergradKB.Probability.absorption_prob_tendsto`

#### Section 11.2

- **§11.2 harmonic function**, p.436 [PR-123]: A function f with Pf=f is harmonic for P; harmonic functions solve gambler's ruin type absorption problems. — *proved proved here* — `UndergradKB.Probability.harmonic_eq_absorption`
- **Definition 11.4**, p.441 [PR-115]: A chain is ergodic (irreducible) if every state can be reached from every state, and regular if some power of P has all entries positive. — *proved proved here* — `UndergradKB.Probability.IsErgodicChain`, `UndergradKB.Probability.IsRegularChain`, `UndergradKB.Probability.isErgodicChain_iff`, `UndergradKB.Probability.IsRegularChain.isErgodicChain`
- **Definition 11.5**, p.441 [PR-115]: A chain is ergodic (irreducible) if every state can be reached from every state, and regular if some power of P has all entries positive. — *proved proved here* — `UndergradKB.Probability.IsErgodicChain`, `UndergradKB.Probability.IsRegularChain`, `UndergradKB.Probability.isErgodicChain_iff`, `UndergradKB.Probability.IsRegularChain.isErgodicChain`
- **Theorem 11.7**, p.442 [PR-117]: For a regular chain P^n converges to a matrix W with equal rows w, a strictly positive probability vector; w is the unique fixed probability vector and v P^n tends to w. — *proved proved here* — `UndergradKB.Probability.osc_mulVec_le_of_entries_ge`, `UndergradKB.Probability.regular_pow_tendsto`, `UndergradKB.Probability.regular_fixed_vector`, `UndergradKB.Probability.regular_distribution_tendsto`
- **Definition 11.6**, p.443 [PR-116]: A row vector w with wP=w is a fixed row vector; a column vector with Px=x is a fixed column vector. — *proved proved here* — `UndergradKB.Probability.IsFixedRow`, `UndergradKB.Probability.IsFixedColumn`
- **Theorem 11.8**, p.443 [PR-117]: For a regular chain P^n converges to a matrix W with equal rows w, a strictly positive probability vector; w is the unique fixed probability vector and v P^n tends to w. — *proved proved here* — `UndergradKB.Probability.osc_mulVec_le_of_entries_ge`, `UndergradKB.Probability.regular_pow_tendsto`, `UndergradKB.Probability.regular_fixed_vector`, `UndergradKB.Probability.regular_distribution_tendsto`
- **Theorem 11.9**, p.445 [PR-117]: For a regular chain P^n converges to a matrix W with equal rows w, a strictly positive probability vector; w is the unique fixed probability vector and v P^n tends to w. — *proved proved here* — `UndergradKB.Probability.osc_mulVec_le_of_entries_ge`, `UndergradKB.Probability.regular_pow_tendsto`, `UndergradKB.Probability.regular_fixed_vector`, `UndergradKB.Probability.regular_distribution_tendsto`
- **Theorem 11.10**, p.446 [PR-118]: An ergodic chain has a unique strictly positive fixed probability vector w and the Cesaro averages of P^n converge to W. — *proved proved here* — `UndergradKB.Probability.ergodic_fixed_vector`, `UndergradKB.Probability.ergodic_cesaro_tendsto`
- **Theorem 11.11**, p.446 [PR-118]: An ergodic chain has a unique strictly positive fixed probability vector w and the Cesaro averages of P^n converge to W. — *proved proved here* — `UndergradKB.Probability.ergodic_fixed_vector`, `UndergradKB.Probability.ergodic_cesaro_tendsto`
- **Theorem 11.12**, p.447 [PR-119]: Law of large numbers for ergodic chains: the proportion of time spent in state s_j converges in probability to w_j. — *proved proved here* — `UndergradKB.Probability.markov_lln`
- **Lemma 11.1**, p.456 [PR-117]: For a regular chain P^n converges to a matrix W with equal rows w, a strictly positive probability vector; w is the unique fixed probability vector and v P^n tends to w. — *proved proved here* — `UndergradKB.Probability.osc_mulVec_le_of_entries_ge`, `UndergradKB.Probability.regular_pow_tendsto`, `UndergradKB.Probability.regular_fixed_vector`, `UndergradKB.Probability.regular_distribution_tendsto`
- **Theorem 11.13**, p.456 [PR-117]: For a regular chain P^n converges to a matrix W with equal rows w, a strictly positive probability vector; w is the unique fixed probability vector and v P^n tends to w. — *proved proved here* — `UndergradKB.Probability.osc_mulVec_le_of_entries_ge`, `UndergradKB.Probability.regular_pow_tendsto`, `UndergradKB.Probability.regular_fixed_vector`, `UndergradKB.Probability.regular_distribution_tendsto`
- **Theorem 11.14**, p.458 [PR-117]: For a regular chain P^n converges to a matrix W with equal rows w, a strictly positive probability vector; w is the unique fixed probability vector and v P^n tends to w. — *proved proved here* — `UndergradKB.Probability.osc_mulVec_le_of_entries_ge`, `UndergradKB.Probability.regular_pow_tendsto`, `UndergradKB.Probability.regular_fixed_vector`, `UndergradKB.Probability.regular_distribution_tendsto`
- **Definition 11.7**, p.461 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`
- **Definition 11.8**, p.462 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`
- **Theorem 11.15**, p.463 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`
- **Corollary 11.1**, p.464 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`
- **Proposition 11.1**, p.465 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`
- **Lemma 11.2**, p.466 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`
- **Theorem 11.16**, p.467 [PR-120]: Mean first passage time m_ij and mean recurrence time r_i; r_i=1/w_i, the fixed vector is positive, and M is computed from the fundamental matrix Z=(I-P+W)^-1 by m_ij=(z_jj-z_ij)/w_j. — *proved proved here* — `UndergradKB.Probability.meanFirstPassage`, `UndergradKB.Probability.meanRecurrence`, `UndergradKB.Probability.hasSum_notYetHit`, `UndergradKB.Probability.meanFirstPassage_eq`

#### Section 11.5

- **§11.5 reversible chain**, p.471 [PR-122]: A chain is reversible if w_i p_ij = w_j p_ji for the fixed vector w. — *in Mathlib* — `UndergradKB.Probability.Course.gs_section_11_5_reversible_chain`, `ProbabilityTheory.Kernel.IsReversible`, `ProbabilityTheory.Kernel.IsReversible.invariant`
- **Theorem 11.17**, p.472 [PR-121]: Central limit theorem for ergodic Markov chains: the number of visits to a state is asymptotically normal. — *not formalized* — –

## Chapter 12

12 items; 12 with a Lean name; 12 proved proved here.

- **Definition 12.1**, p.479 [PR-124]: A random walk is the sequence of partial sums S_n=X_1+...+X_n of iid random variables (in R^m). — *proved proved here* — `UndergradKB.Probability.randomWalk_succ`
- **Theorem 12.1**, p.481 [PR-125]: For the simple symmetric walk the probability of being at the origin at time 2m is C(2m,m) 2^(-2m), and 0 at odd times. — *proved proved here* — `UndergradKB.Probability.u_even`, `UndergradKB.Probability.u_odd`
- **Theorem 12.2**, p.481 [PR-126]: First returns: u_2n = sum f_2k u_(2n-2k); and the first return to 0 at time 2m has probability u_2m/(2m-1). — *proved proved here* — `UndergradKB.Probability.u_renewal`, `UndergradKB.Probability.f_even`
- **Theorem 12.3**, p.482 [PR-126]: First returns: u_2n = sum f_2k u_(2n-2k); and the first return to 0 at time 2m has probability u_2m/(2m-1). — *proved proved here* — `UndergradKB.Probability.u_renewal`, `UndergradKB.Probability.f_even`
- **Example 12.1**, p.483 [PR-127]: Eventual return to the origin has probability 1 in dimensions 1 and 2 (recurrent) and less than 1 in dimension at least 3; the expected number of equalizations in 2m steps. — *proved proved here* — `UndergradKB.Probability.Polya.u_renewal`, `UndergradKB.Probability.Polya.hasSum_f_of_hasSum_u`, `UndergradKB.Probability.Polya.hasSum_f_of_not_summable_u`, `UndergradKB.Probability.Polya.tsum_f_eq_one_iff`
- **Example 12.2**, p.484 [PR-127]: Eventual return to the origin has probability 1 in dimensions 1 and 2 (recurrent) and less than 1 in dimension at least 3; the expected number of equalizations in 2m steps. — *proved proved here* — `UndergradKB.Probability.Polya.u_renewal`, `UndergradKB.Probability.Polya.hasSum_f_of_hasSum_u`, `UndergradKB.Probability.Polya.hasSum_f_of_not_summable_u`, `UndergradKB.Probability.Polya.tsum_f_eq_one_iff`
- **Example 12.3**, p.487 [PR-127]: Eventual return to the origin has probability 1 in dimensions 1 and 2 (recurrent) and less than 1 in dimension at least 3; the expected number of equalizations in 2m steps. — *proved proved here* — `UndergradKB.Probability.Polya.u_renewal`, `UndergradKB.Probability.Polya.hasSum_f_of_hasSum_u`, `UndergradKB.Probability.Polya.hasSum_f_of_not_summable_u`, `UndergradKB.Probability.Polya.tsum_f_eq_one_iff`

#### Section 12.2

- **§12.2 gambler's ruin**, p.494 [PR-128]: A fair game (martingale) keeps conditional expected fortune equal to the present fortune; de Moivre's gambler's ruin argument. — *proved proved here* — `UndergradKB.Probability.gamblersRuin_fair_exists`, `UndergradKB.Probability.gamblersRuin_fair_unique`, `UndergradKB.Probability.gamblersRuin_unfair_exists`, `UndergradKB.Probability.gamblersRuin_unfair_unique`
- **§12.2 martingale**, p.498 [PR-128]: A fair game (martingale) keeps conditional expected fortune equal to the present fortune; de Moivre's gambler's ruin argument. — *proved proved here* — `UndergradKB.Probability.gamblersRuin_fair_exists`, `UndergradKB.Probability.gamblersRuin_fair_unique`, `UndergradKB.Probability.gamblersRuin_unfair_exists`, `UndergradKB.Probability.gamblersRuin_unfair_unique`
- **Theorem 12.4**, p.502 [PR-129]: Arc sine laws: the time in the lead, the last time of the maximum, and in general the fraction of time a symmetric walk is positive have the arc sine distribution (discrete and continuous versions). — *proved proved here* — `UndergradKB.Probability.firstAtEnd_prob`, `UndergradKB.Probability.leadCount_prob`, `UndergradKB.Probability.leadCount_cdf_tendsto`, `UndergradKB.Probability.firstAtEnd_cdf_tendsto`
- **Theorem 12.5**, p.503 [PR-129]: Arc sine laws: the time in the lead, the last time of the maximum, and in general the fraction of time a symmetric walk is positive have the arc sine distribution (discrete and continuous versions). — *proved proved here* — `UndergradKB.Probability.firstAtEnd_prob`, `UndergradKB.Probability.leadCount_prob`, `UndergradKB.Probability.leadCount_cdf_tendsto`, `UndergradKB.Probability.firstAtEnd_cdf_tendsto`
- **Theorem 12.6**, p.504 [PR-129]: Arc sine laws: the time in the lead, the last time of the maximum, and in general the fraction of time a symmetric walk is positive have the arc sine distribution (discrete and continuous versions). — *proved proved here* — `UndergradKB.Probability.firstAtEnd_prob`, `UndergradKB.Probability.leadCount_prob`, `UndergradKB.Probability.leadCount_cdf_tendsto`, `UndergradKB.Probability.firstAtEnd_cdf_tendsto`
