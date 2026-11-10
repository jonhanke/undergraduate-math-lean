# Course outline: A=B (combinatorics)

Generated from [`docs/coverage/combinatorics/checklist.md`](../../coverage/combinatorics/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build Combinatorics` builds this topic.

251 items in 10 chapters; 214 with a Lean name (85.3%).

## (unplaced)

1 items; 0 with a Lean name; 1 not formalized.

- **text p.15**, p.15 [CO-540]: Goedel: any consistent axiom system has true statements it cannot prove (incompleteness); cited as background. — *not formalized* — –

## Chapter 1

25 items; 21 with a Lean name; 10 proved proved here; 9 in Mathlib; 2 partly; 4 not formalized.


#### Section 1.1

- **Thm 1.1.1**, p.16 [CO-541]: Richardson: for expressions built from rationals, pi, ln 2, x with +, *, composition, sin, exp, \|.\|, the predicate "E = 0" is recursively undecidable. — *not formalized* — –
- **text p.16**, p.16 [CO-542]: No algorithm decides solvability of Diophantine equations over the integers (Hilbert's tenth problem, Matiyasevich 1970). — *partly* — `Dioph.pow_dioph`
- **def p.18 canonical form**, p.18 [CO-543]: Canonical form: a one-to-one description c(A) of the objects of a class, so A = B iff c(A) = c(B). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsCanonicalForm`, `UndergradKB.Combinatorics.AeqB.IsCanonicalForm.eq_iff`
- **def p.18 normal form**, p.18 [CO-544]: Normal form: a representation (maybe non-unique) in an additive group such that a representation of 0 is recognizable, so A = B reduces to A - B = 0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.NormalForm`, `UndergradKB.Combinatorics.AeqB.NormalForm.val_eq_iff`

#### Section 1.3

- **Eq 1.3.1**, p.19 [CO-345]: ((a+b)/2)^2 - ab = ((a-b)/2)^2, which gives the AM-GM inequality for two numbers. — *proved proved here* — `UndergradKB.Combinatorics.sq_avg_sub_mul_eq_sq_half_diff`, `UndergradKB.Combinatorics.mul_le_sq_avg`, `UndergradKB.Combinatorics.sqrt_mul_le_avg`
- **Eq 1.3.2**, p.19 [CO-346]: Euler's four-square identity: product of two sums of four squares is again a sum of four squares via an explicit bilinear formula. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.eq_1_3_2`, `euler_four_squares`, `Nat.euler_four_squares`
- **text p.19**, p.19 [CO-527]: Every rational number has a unique reduced form a/b with gcd(a,b)=1 and b>0 (canonical form of Q); equal rationals are decided by comparing it. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p19_rat_reduced`, `Rat.num_div_den`
- **text p.19**, p.19 [CO-528]: A polynomial in several variables has a canonical form as a finite coefficient array sum a_ij x^i y^j; equality of polynomials is coefficientwise. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p19_mvpoly_ext`, `MvPolynomial.ext`

#### Section 1.4

- **Thm 1.4.1**, p.20 [CO-068]: Sum of the first n cubes equals (n(n+1)/2)^2. — *proved proved here* — `UndergradKB.Combinatorics.sum_cubes`
- **Thm 1.4.2**, p.20 [CO-348]: The three angle bisectors of a triangle are concurrent (incenter). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.angle_bisectors_concurrent`
- **text p.20 2D Cauchy-Schwarz**, p.20 [CO-347]: Lagrange identity: (sum a_i^2)(sum b_i^2) - (sum a_i b_i)^2 = sum_{i<j} (a_i b_j - a_j b_i)^2; the n=2 case gives 2D Cauchy-Schwarz. — *proved proved here* — `UndergradKB.Combinatorics.lagrange_identity`
- **text p.20-21**, p.20 [CO-529]: A polynomial of degree at most L in n is determined by its values at L+1 distinct points, so the value vector is a canonical form (basis of "proof by example"). — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p20_poly_eval`, `Polynomial.eq_of_degree_le_of_eval_finset_eq`
- **text p.21**, p.21 [CO-069]: sum_{i=1}^n q(i) = p(n) holds for all n iff p(n)-p(n-1)=q(n) and p(0)=0. — *proved proved here* — `UndergradKB.Combinatorics.sum_eq_iff_telescoping`

#### Section 1.5

- **Ex 1.5.1**, p.22 [CO-532]: arcsin x + arcsin y = arcsin(x sqrt(1-y^2) + y sqrt(1-x^2)) (equivalent to sin addition), proved by differentiating in x. — *proved proved here* — `UndergradKB.Combinatorics.arcsin_add_arcsin`
- **text p.22**, p.22 [CO-530]: cos x = (e^{ix}+e^{-ix})/2 and sin x = (e^{ix}-e^{-ix})/(2i), reducing rational trig identities to polynomial identities in e^{ix}. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p22_cos_sin_exp`, `Complex.two_cos`
- **text p.22**, p.22 [CO-531]: Addition formula sin(a+b)=sin a cos b + cos a sin b (and double-angle cos 2x identities) as routine trig identities. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p22_trig`, `Real.sin_add`, `Complex.sin_add`, `Complex.cos_two_mul`
- **text p.23**, p.23 [CO-231]: Explicit (Binet) formula for Fibonacci numbers f_n=(phi^n-psi^n)/sqrt5, requested by exercises. — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_9_9_5_binet`, `Real.coe_fib_eq`
- **text p.23**, p.23 [CO-232]: Cassini's identity F_{n+1}F_{n-1} - F_n^2 = (-1)^n. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p23_cassini`, `Int.fib_succ_mul_fib_pred_sub_fib_sq`
- **text p.23**, p.23 [CO-349]: (sum a_i)^2 = sum a_i^2 + 2 sum_{i<j} a_i a_j, i.e. p_1^2 = p_2 + 2 e_2. — *proved proved here* — `UndergradKB.Combinatorics.sq_sum_eq_sum_sq_add_two_mul`
- **text p.23**, p.23 [CO-531]: Addition formula sin(a+b)=sin a cos b + cos a sin b (and double-angle cos 2x identities) as routine trig identities. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p22_trig`, `Real.sin_add`, `Complex.sin_add`, `Complex.cos_two_mul`

#### Section 1.7

- **Eq 1.7.1**, p.24 [CO-347]: Lagrange identity: (sum a_i^2)(sum b_i^2) - (sum a_i b_i)^2 = sum_{i<j} (a_i b_j - a_j b_i)^2; the n=2 case gives 2D Cauchy-Schwarz. — *proved proved here* — `UndergradKB.Combinatorics.lagrange_identity`
- **text p.24**, p.24 [CO-350]: An identity among elementary/power-sum symmetric functions holds for all n iff it holds for n equal to the largest index appearing, so such identities are routine. — *partly* — `MvPolynomial.esymmAlgEquiv`
- **def p.25 sn cn dn**, p.25 [CO-533]: Jacobi's elliptic function sn is the inverse of F(z)=integral_0^z dx / sqrt((1-x^2)(1-k^2x^2)); cn, dn defined from it; theta functions give rapidly convergent series. — *not formalized* — –

#### Section 1.8

- **Eq 1.8.4**, p.26 [CO-534]: Addition formula sn(u+v) = (sn u cn v dn v + sn v cn u dn u)/(1-k^2 sn^2 u sn^2 v), equivalent to an algebraic addition law for F, provable by differentiation. — *not formalized* — –
- **Eq 1.8.5**, p.26 [CO-534]: Addition formula sn(u+v) = (sn u cn v dn v + sn v cn u dn u)/(1-k^2 sn^2 u sn^2 v), equivalent to an algebraic addition law for F, provable by differentiation. — *not formalized* — –

## Chapter 2

19 items; 17 with a Lean name; 11 proved proved here; 6 in Mathlib; 2 not formalized.


#### Section 2.1

- **Ex 2.1.1**, p.31 [CO-535]: e(x+y)=e(x)e(y) for the series e(x)=sum x^n/n!, proved by showing e(x+y)e(-x)e(-y) has zero derivative and equals 1 at 0. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.ex_2_1_1`, `Complex.exp_add`, `Real.exp_add`, `NormedSpace.exp_add`
- **text p.31**, p.31 [CO-233]: f(n)=sum_k C(n,k)^3 satisfies 8(n+1)^2 f(n)+(7n^2+21n+16) f(n+1)-(n+2)^2 f(n+2)=0, and f has no simple closed form (proved later as Thm 8.8.1). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.franel_recurrence`
- **text p.32**, p.32 [CO-025]: Sum of mu(k) over divisors k of n is 1 if n=1 and 0 otherwise. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p32_moebius_sum`, `ArithmeticFunction.moebius_mul_coe_zeta`
- **text p.32**, p.32 [CO-209]: Euler product: product over primes of (1-p^-s)^-1 = sum n^-s for Re s > 1. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p32_euler_product`, `riemannZeta_eulerProduct`
- **text p.32**, p.32 [CO-210]: Rogers-Ramanujan: sum_m x^{m^2}/((1-x)...(1-x^m)) = product over m of 1/((1-x^{5m+1})(1-x^{5m+4})). — *not formalized* — –
- **text p.32**, p.32 [CO-351]: det(gcd(i,j))_{i,j<=n} = phi(1) phi(2) ... phi(n) (Smith's determinant). — *proved proved here* — `UndergradKB.Combinatorics.det_gcdMatrix`

#### Section 2.2

- **Eq 2.2.1**, p.33 [CO-032]: Sum over i of C(n,i)^2 equals C(2n,n). — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_2_20`, `Nat.sum_range_choose_sq`
- **Eq 2.2.2**, p.33 [CO-043]: Sum over i+j+k=n of C(i+j,i)C(j+k,j)C(k+i,k) equals sum_{0<=j<=n} C(2j,j). — *not formalized* — –
- **Eq 2.2.3**, p.33 [CO-211]: exp(sum_{m>=1} m^{m-1} t^m/m!) = 1 + sum_{n>=1} (n+1)^{n-1} t^n/n! (tree-function identity). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.exp_treeSeries`
- **Eq 2.2.4**, p.33 [CO-044]: sum_s (-1)^s C(2m,s)^3 = (-1)^m (3m)!/(m!)^3 (Dixon-type alternating cube sum). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.alternating_choose_cube`

#### Section 2.3

- **Eq 2.3.1**, p.34 [CO-032]: Sum over i of C(n,i)^2 equals C(2n,n). — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_2_20`, `Nat.sum_range_choose_sq`
- **text p.34**, p.34 [CO-386]: To prove sum_k summand(n,k)=answer(n): find a recurrence for the sum, check answer satisfies it, check enough initial values (Zeilberger 1982 principle). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.zeilberger_principle`
- **Ex 2.3.1**, p.36 [CO-029]: Sum over i of C(n,i) equals 2^n (count bit strings by number of zeros). — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_2_17`, `Nat.sum_range_choose`
- **text p.36 WZ proof algorithm**, p.36 [CO-439]: Standardized WZ proof algorithm: divide by rhs to get sum_k F(n,k)=1, take certificate R(n,k), set G=RF, verify F(n+1,k)-F(n,k)=G(n,k+1)-G(n,k), sum over k, check n=0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.wz_proof`
- **text p.36**, p.36 [CO-440]: If F,G satisfy F(n+1,k)-F(n,k)=G(n,k+1)-G(n,k) and F(n,.) has finite support in k, then sum_k F(n,k) is independent of n. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.WZEq.finsum_const`
- **def p.37 routinely verifiable**, p.37 [CO-441]: A "routinely verifiable" identity: after cancelling exponentials and rewriting binomials as factorial quotients, it reduces to a polynomial identity checkable mechanically. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.recurrence_of_ratio_identity`, `UndergradKB.Combinatorics.AeqB.recurrence_iff_ratio_identity`
- **Ex 2.3.2**, p.38 [CO-442]: The sum over k of F(n,k)=(n-i)!(n-j)!(i-1)!(j-1)!/((n-1)!(k-1)!(n-i-j+k)!(i-k)!(j-k)!) equals 1, with certificate R(n,k)=(k-1)/n. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.mon_cert`
- **def p.45 hypergeometric series/term**, p.45 [CO-353]: Hypergeometric term/series: t_0=1 and t_{k+1}/t_k=P(k)/Q(k) is a rational function of k; geometric series are the constant-ratio case. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsHypergeometricSeries`, `UndergradKB.Combinatorics.AeqB.isHypergeometricSeries_pFqTerm`
- **text p.90 Step 2.1-2.2**, p.90 [CO-402]: Step 2 of Gosper: compute S=nonneg integer zeros of Res_n(f(n),g(n+h)); successively cancel gcds s_j of p_{j-1}(n) and q_{j-1}(n+h_j) to get a,b and c as a product of shifted s_i — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosperStage`, `UndergradKB.Combinatorics.AeqB.gosperShiftGcd`, `UndergradKB.Combinatorics.AeqB.gosperStep2C`, `UndergradKB.Combinatorics.AeqB.gosper_step2_spec`

## Chapter 3

30 items; 22 with a Lean name; 15 proved proved here; 5 in Mathlib; 10 not formalized.


#### Section 3.2

- **Eq 3.2.1**, p.46 [CO-354]: The series pFq[a1..ap; b1..bq; x] has term ratio (k+a1)...(k+ap)x/((k+b1)...(k+bq)(k+1)), i.e. sum (a1)_k...(ap)_k x^k/((b1)_k...(bq)_k k!); upper/lower parameters; e^x = 0F0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.pFqTerm`, `UndergradKB.Combinatorics.AeqB.pFqTerm_succ_mul`, `UndergradKB.Combinatorics.AeqB.isHypergeometricSeries_pFqTerm`, `UndergradKB.Combinatorics.AeqB.pFqTerm_zero_zero`
- **def p.46 pFq**, p.46 [CO-354]: The series pFq[a1..ap; b1..bq; x] has term ratio (k+a1)...(k+ap)x/((k+b1)...(k+bq)(k+1)), i.e. sum (a1)_k...(ap)_k x^k/((b1)_k...(bq)_k k!); upper/lower parameters; e^x = 0F0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.pFqTerm`, `UndergradKB.Combinatorics.AeqB.pFqTerm_succ_mul`, `UndergradKB.Combinatorics.AeqB.isHypergeometricSeries_pFqTerm`, `UndergradKB.Combinatorics.AeqB.pFqTerm_zero_zero`
- **text p.47 lookup algorithm**, p.47 [CO-355]: Hypergeometric series lookup algorithm: shift index to start at nonzero term, normalize t_0=1, factor term ratio, and read off p,q,a_i,b_j,x. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.eq_pFqTerm_of_term_ratio`, `UndergradKB.Combinatorics.AeqB.eq_pFqTerm_of_factored_ratio`, `UndergradKB.Combinatorics.AeqB.eq_pFqTerm_of_factored_ratio_insert`, `UndergradKB.Combinatorics.AeqB.lookup_shift_normalize`

#### Section 3.3

- **Ex 3.3.3**, p.48 [CO-356]: Generalized falling factorial [x,d]_n = prod_{j<n}(x-jd), and sum_k C(n,k)[x,d]_k[y,d]_{n-k} = 2F1(-n,-x/d; y/d-n+1; 1) times its leading term. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gff`, `UndergradKB.Combinatorics.AeqB.gff_add`, `UndergradKB.Combinatorics.AeqB.gff_binomial_eq_pFq`
- **def p.48 [x,d]_n**, p.48 [CO-356]: Generalized falling factorial [x,d]_n = prod_{j<n}(x-jd), and sum_k C(n,k)[x,d]_k[y,d]_{n-k} = 2F1(-n,-x/d; y/d-n+1; 1) times its leading term. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gff`, `UndergradKB.Combinatorics.AeqB.gff_add`, `UndergradKB.Combinatorics.AeqB.gff_binomial_eq_pFq`
- **Ex 3.3.5**, p.49 [CO-357]: Bessel function J_p(x) = (x/2)^p/p! * 0F1(-; p+1; -x^2/4), so it is hypergeometric. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.ex_3_3_5`, `besselJ_def`
- **Eq 3.3.2**, p.50 [CO-354]: The series pFq[a1..ap; b1..bq; x] has term ratio (k+a1)...(k+ap)x/((k+b1)...(k+bq)(k+1)), i.e. sum (a1)_k...(ap)_k x^k/((b1)_k...(bq)_k k!); upper/lower parameters; e^x = 0F0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.pFqTerm`, `UndergradKB.Combinatorics.AeqB.pFqTerm_succ_mul`, `UndergradKB.Combinatorics.AeqB.isHypergeometricSeries_pFqTerm`, `UndergradKB.Combinatorics.AeqB.pFqTerm_zero_zero`
- **def p.50 rising factorial**, p.50 [CO-358]: Rising factorial (a)_n = a(a+1)...(a+n-1), (a)_0=1. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.def_p50_rising_factorial`, `ascPochhammer`, `Nat.ascFactorial`
- **text p.50**, p.50 [CO-359]: pFq is well defined if no lower parameter is a nonpositive integer, and terminates when an upper parameter is a nonpositive integer. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.LowerOK`, `UndergradKB.Combinatorics.AeqB.pFqTerm_eq_zero_of_neg_nat`, `UndergradKB.Combinatorics.AeqB.tsum_pFqTerm_eq_sum_of_neg_nat`
- **text p.53**, p.53 [CO-360]: Gamma(n+1)=n!=(1)_n and (a)_n = Gamma(n+a)/Gamma(a). — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.text_p53_gamma_pochhammer`, `Complex.Gamma_nat_eq_factorial`, `Complex.Gamma_add_nat_div_Gamma_eq`
- **text p.53 (I) Gauss 2F1**, p.53 [CO-361]: Gauss: 2F1(a,b;c;1) = Gamma(c-a-b)Gamma(c)/(Gamma(c-a)Gamma(c-b)) if b is a nonpositive integer or Re(c-a-b)>0. — *not formalized* — `UndergradKB.Combinatorics.AeqB.gauss_two_one_neg_nat`
- **text p.53 (II) Kummer 2F1**, p.53 [CO-362]: Kummer: for a-b+c=1, 2F1(a,b;c;-1) = Gamma(b/2+1)Gamma(b-a+1)/(Gamma(b+1)Gamma(b/2-a+1)); cosine form for negative integer b. — *not formalized* — `UndergradKB.Combinatorics.AeqB.kummer_terminating`, `UndergradKB.Combinatorics.AeqB.kummer_terminating_odd`, `UndergradKB.Combinatorics.AeqB.kummer_terminating_even`
- **def p.53 gamma function**, p.53 [CO-536]: Gamma(z) = integral_0^infty t^{z-1} e^{-t} dt for Re z>0, extended by analytic continuation; extends factorial. — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.def_p53_gamma`, `Complex.Gamma`, `Real.Gamma`, `Complex.Gamma_nat_eq_factorial`

#### Section 3.5

- **Eq 3.5.1**, p.54 [CO-537]: Euler reflection formula Gamma(z)Gamma(1-z)=pi/sin(pi z). — *in Mathlib* — `UndergradKB.Combinatorics.Course.AeqB.eq_3_5_1`, `Complex.Gamma_mul_Gamma_one_sub`, `Real.Gamma_mul_Gamma_one_sub`
- **text p.54 (III) Saalschuetz**, p.54 [CO-363]: Saalschuetz: if d+e=a+b+c+1 and c is a negative integer, 3F2(a,b,c;d,e;1)=(d-a)_\|c\|(d-b)_\|c\|/((d)_\|c\|(d-a-b)_\|c\|). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.saalschutz_three_f_two`
- **text p.54 (IV) Dixon**, p.54 [CO-364]: Dixon: sum_k (-1)^k C(a+b,a+k)C(a+c,c+k)C(b+c,b+k) = (a+b+c)!/(a!b!c!), and the well-poised 3F2 form with d=a-b+1, e=a-c+1. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dixon`
- **text p.54 (V) Clausen 4F3**, p.54 [CO-365]: Clausen-type 4F3 summation under d nonpositive integer, a+b+c-d=1/2, e=a+b+1/2, a+f=d+1=b+g, giving a product of rising factorials. — *not formalized* — –
- **text p.54 (VI) Dougall 7F6**, p.54 [CO-366]: Dougall's terminating well-poised 7F6 summation (balanced, a6=1+a1/2, a7=-n) as a product of rising factorials. — *not formalized* — –

#### Section 3.6

- **Ex 3.6.1**, p.55 [CO-045]: sum_k (-1)^k C(2n,k)^2 = (-1)^n C(2n,n), found as 2F1(-2n,-2n;1;-1) via Kummer. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.alt_sum_choose_sq`
- **text p.55 well-poised 3F2**, p.55 [CO-364]: Dixon: sum_k (-1)^k C(a+b,a+k)C(a+c,c+k)C(b+c,b+k) = (a+b+c)!/(a!b!c!), and the well-poised 3F2 form with d=a-b+1, e=a-c+1. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dixon`
- **text p.55 1F0**, p.55 [CO-367]: 1F0[a;-;z] = (1-z)^{-a}. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.oneFZero_nat_mul_one_sub_X_pow`, `UndergradKB.Combinatorics.AeqB.hasSum_pFqTerm_one_zero`
- **text p.55 2F1 at 1/2**, p.55 [CO-368]: 2F1(a,1-a;b;1/2) = Gamma(b/2)Gamma(b/2+1/2)/(Gamma((a+b)/2)Gamma((1+b-a)/2)) (Bailey-type; unnamed in book). — *not formalized* — –
- **text p.55 3F2 (-2n,b,c)**, p.55 [CO-369]: 3F2(-2n,b,c;1-b-2n,1-c-2n;1) = (1)_2n (b)_n (c)_n (b+c)_2n / ((1)_n (b)_2n (c)_2n (b+c)_n). — *not formalized* — –
- **text p.55 3F2 (a,b,-n)**, p.55 [CO-370]: 3F2(a,b,-n;1+a-b,1+a+n;1) = (1+a)_n (1+a/2-b)_n/((1+a/2)_n (1+a-b)_n). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities3b.threeFTwo_a_b_neg_n`
- **text p.55 3F2 ((1+a+b)/2,2c)**, p.55 [CO-371]: 3F2(a,b,c;(1+a+b)/2,2c;1) equals a gamma-quotient (Watson-type; unnamed in book). — *not formalized* — –
- **text p.55 3F2 (a,1-a,c)**, p.55 [CO-372]: 3F2(a,1-a,c;d,1+2c-d;1) equals a gamma/factorial quotient (Whipple-type; unnamed in book). — *not formalized* — –
- **Ex 3.6.2**, p.56 [CO-046]: sum_k (-1)^k C(2n,k)C(2k,k)C(4n-2k,2n-k) = C(2n,n)^2 (a special case of Dixon, needing a gamma-limit argument). — *not formalized* — –
- **Eq 3.6.3**, p.58 [CO-046]: sum_k (-1)^k C(2n,k)C(2k,k)C(4n-2k,2n-k) = C(2n,n)^2 (a special case of Dixon, needing a gamma-limit argument). — *not formalized* — –
- **text p.60**, p.60 [CO-373]: Euler transformation 2F1(a,b;c;z)=(1-z)^{c-a-b} 2F1(c-a,c-b;c;z). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.euler_transformation`
- **text p.96 Step 3.1-3.2**, p.96 [CO-410]: Step 3 of Gosper: compute candidate degrees D (at most two), take d=max D in N, solve for a polynomial x of degree <=d by undetermined coefficients — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosperDegreeSet`, `UndergradKB.Combinatorics.AeqB.gosperDegreeBound`, `UndergradKB.Combinatorics.AeqB.natDegree_mem_gosperDegreeSet`, `UndergradKB.Combinatorics.AeqB.natDegree_le_gosperDegreeBound`

## Chapter 4

20 items; 19 with a Lean name; 17 proved proved here; 1 in Mathlib; 2 not formalized.


#### Section 4.1

- **Ex 4.1.1**, p.65 [CO-047]: sum_k k*C(n,k) = n*2^(n-1), derived by Sister Celine's method — *proved proved here* — `UndergradKB.Combinatorics.AeqB.sum_mul_choose`
- **text p.67**, p.67 [CO-387]: A recurrence for the summand with coefficients free of k, summed over all integers k (finite support), gives a recurrence for the sum f(n)=sum_k F(n,k) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.sum_recurrence`
- **def p.68 doubly hypergeometric**, p.68 [CO-374]: F(n,k) is doubly hypergeometric if both F(n+1,k)/F(n,k) and F(n,k+1)/F(n,k) are rational functions of n and k — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsDoublyHypergeometric`

#### Section 4.3

- **Ex 4.3.1**, p.69 [CO-032]: Sum over i of C(n,i)^2 equals C(2n,n). — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_2_20`, `Nat.sum_range_choose_sq`
- **def p.69 algorithm (steps 1-5, eq 4.3.1)**, p.69 [CO-388]: Sister Celine's method: assume a k-free recurrence sum a_{ij}(n)F(n-j,k-i)=0 with trial orders I,J, divide by F, clear denominators, equate powers of k to zero and solve the linear system, enlarging I,J on failure — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Celine.eval_shift_mul_deltaVal`, `UndergradKB.Combinatorics.AeqB.Celine.celine_sound`, `UndergradKB.Combinatorics.AeqB.Celine.celineMap_ker_ne_bot`
- **Ex 4.3.2**, p.71 [CO-234]: Laguerre polynomials L_n(x)=sum (-1)^k C(n,k) x^k/k! satisfy n L_n+(x+1-2n)L_{n-1}+(n-1)L_{n-2}=0 — *proved proved here* — `UndergradKB.Combinatorics.AeqB.laguerre_recurrence`, `UndergradKB.Combinatorics.AeqB.laguerre_recurrence'`
- **text p.72**, p.72 [CO-387]: A recurrence for the summand with coefficients free of k, summed over all integers k (finite support), gives a recurrence for the sum f(n)=sum_k F(n,k) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.sum_recurrence`
- **Ex 4.3.3**, p.73 [CO-048]: Reed-Dawson identity: sum_k C(n,k)C(2k,k)(-2)^(n-k) is 0 for odd n and C(n,n/2) for even n, from n f(n)=4(n-1)f(n-2) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.reed_dawson`

#### Section 4.4

- **def p.74 proper hypergeometric term (eq 4.4.1)**, p.74 [CO-375]: Proper hypergeometric term: P(n,k) times a ratio of products of factorials of integer-linear forms in n,k with fixed integer coefficients, times x^k — *proved proved here* — `UndergradKB.Combinatorics.AeqB.ProperHypergeometricData.eval`
- **Thm 4.4.1**, p.75 [CO-389]: Fundamental Theorem: every proper hypergeometric term satisfies a nontrivial k-free recurrence with polynomial coefficients, of explicit orders (I*,J*) given by sums of \|b_s\|,\|v_s\| and deg P; this guarantees Sister Celine's method terminates — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Celine.celineMap_ker_ne_bot`, `UndergradKB.Combinatorics.AeqB.Celine.exists_kfree_recurrence`, `UndergradKB.Combinatorics.AeqB.Celine.fundamental_theorem`
- **text p.76 eq 4.4.4**, p.76 [CO-390]: Shift ratio of a factorial of a linear form: F(n-j,k-i)/F(n,k) for F=(an+bk+c)! is a reciprocal falling factorial polynomial or a rising factorial polynomial depending on the sign of aj+bi (eq 4.4.4/4.4.5) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Celine.eval_shift_mul_deltaVal`, `UndergradKB.Combinatorics.AeqB.shift_factorial_of_nonneg`, `UndergradKB.Combinatorics.AeqB.shift_factorial_of_neg`
- **text p.79-80**, p.79 [CO-391]: An identity sum_k F(n,k)=1 is proved by checking finitely many n up to a computable n0 (order of recurrence plus largest nonnegative root of the leading coefficient plus max coefficient degree) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.eq_of_polynomial_recurrence`, `UndergradKB.Combinatorics.AeqB.eq_of_backward_recurrence`, `UndergradKB.Combinatorics.AeqB.exists_finite_check_bound`
- **text p.80**, p.80 [CO-392]: Yen: for q-identities the leading coefficient of the recurrence cannot vanish, so a finite check suffices (Chu-Vandermonde needs 2358 values) — *not formalized* — –

#### Section 4.5

- **Thm 4.5.1**, p.81 [CO-393]: Multivariate Fundamental Theorem: proper hypergeometric terms in r summation variables satisfy a nontrivial k-free recurrence with explicit order bound J* — *not formalized* — `UndergradKB.Combinatorics.AeqB.CelineMulti.exists_kfree_recurrence_multi`
- **Thm 4.5.2**, p.81 [CO-394]: q-version of the Fundamental Theorem: a q-hypergeometric term satisfies a k-free recurrence of order at most sum b_s^2 + sum v_s^2 + 2\|c\| — *proved proved here* — `UndergradKB.Combinatorics.AeqB.QFundamental.q_fundamental_theorem`
- **text p.81 eq 4.5.5-4.5.6**, p.81 [CO-376]: q-proper hypergeometric term: product of q-Pochhammer-type factors Q(m,c)=prod(1-c q^i) in numerator/denominator, times a quadratic power of q and xi^k — *proved proved here* — `UndergradKB.Combinatorics.AeqB.QAnalogue.QProperData.eval`
- **def p.84 Gosper-summable**, p.84 [CO-395]: A hypergeometric term t_n is Gosper-summable if some hypergeometric z_n satisfies z_{n+1}-z_n=t_n, so the partial sum is a hypergeometric term plus a constant — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsGosperSummable`
- **def p.85 hypergeometric term**, p.85 [CO-353]: Hypergeometric term/series: t_0=1 and t_{k+1}/t_k=P(k)/Q(k) is a rational function of k; geometric series are the constant-ratio case. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsHypergeometricSeries`, `UndergradKB.Combinatorics.AeqB.isHypergeometricSeries_pFqTerm`
- **text p.85**, p.85 [CO-396]: Writing z_n=y(n)t_n turns z_{n+1}-z_n=t_n into r(n)y(n+1)-y(n)=1 with y rational, where r=t_{n+1}/t_n (eq 5.2.2) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosper_reduction_iff`, `UndergradKB.Combinatorics.AeqB.isGosperSummable_iff`
- **text p.85-86**, p.85 [CO-397]: Gosper's form: r(n)=a(n)c(n+1)/(b(n)c(n)) with gcd(a(n),b(n+h))=1 for all h in N; then y=b(n-1)x(n)/c(n) with a(n)x(n+1)-b(n-1)x(n)=c(n) (eq 5.2.3-5.2.6) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosper_form_equiv`

## Chapter 5

21 items; 21 with a Lean name; 20 proved proved here; 1 not formalized.


#### Section 5.2

- **Thm 5.2.1**, p.86 [CO-398]: Any rational solution x(n) of a(n)x(n+1)-b(n-1)x(n)=c(n) is a polynomial when gcd(a(n),b(n+h))=1 for all h in N — *proved proved here* — `UndergradKB.Combinatorics.AeqB.natDegree_eq_zero_of_gosper_eq`, `UndergradKB.Combinatorics.AeqB.dvd_of_gosper_eq`, `UndergradKB.Combinatorics.AeqB.gosper_rational_solution_is_polynomial`
- **text p.87**, p.87 [CO-399]: Hypergeometric solutions of z_{n+1}-z_n=t_n correspond exactly to nonzero polynomial solutions x of (5.2.6) via z_n=b(n-1)x(n)t_n/c(n) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.isGosperSummable_iff_polynomial_solution`
- **text p.87 algorithm outline**, p.87 [CO-400]: Gosper's algorithm: form r=t_{n+1}/t_n, factor r as in Gosper's form, find a nonzero polynomial solution x, return b(n-1)x(n)t_n/c(n) or report partial sum not Gosper-summable — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosperOutput`, `UndergradKB.Combinatorics.AeqB.gosperTerm_correct`, `UndergradKB.Combinatorics.AeqB.gosperOutput_spec`, `UndergradKB.Combinatorics.AeqB.gosper_algorithm`
- **text p.89**, p.89 [CO-401]: R(h)=Res_n(f(n),g(n+h)) vanishes at alpha iff gcd(f(n),g(n+alpha)) is nonconstant; so violating shifts are the nonneg integer roots of R; integer roots found by divisors of the constant term (over Q) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.resultant_shift_eq_zero_iff`, `UndergradKB.Combinatorics.AeqB.forall_isCoprime_shift_iff`

#### Section 5.3

- **Prop 5.3.1**, p.91 [CO-403]: In Step 2, gcd(p_i(n),q_j(n+h))=1 for k<=i,j<=N and h<h_{k+1}; in particular gcd(a(n),b(n+h))=1 for all h in N — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosperStage_coprime`, `UndergradKB.Combinatorics.AeqB.gosper_prop_5_3_1`
- **Thm 5.3.1**, p.92 [CO-404]: Every nonzero rational function r over a char-0 field factors as a c(n+1)/(b c(n)) with b,c monic and gcd(a,b(n+h))=1 for all h, gcd(a,c)=1, gcd(b,c(n+1))=1; Step 2 constructs it — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosper_step2_coprime`, `UndergradKB.Combinatorics.AeqB.exists_gosper_form`
- **Lem 5.3.1**, p.92 [CO-405]: If two Gosper-type factorizations of the same rational function satisfy gcd conditions (one in canonical shape), then c(n) divides C(n) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dvd_of_gosper_forms_eq`
- **Cor 5.3.1**, p.93 [CO-406]: The canonical factorization of r(n) from Thm 5.3.1 is unique — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosper_form_unique`
- **Cor 5.3.2**, p.93 [CO-407]: Among all triples satisfying (5.2.3)-(5.2.4), the Step 2 output has c(n) of least degree (smallest linear system) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gosper_step2_form`, `UndergradKB.Combinatorics.AeqB.gosper_c_dvd_of_triple`, `UndergradKB.Combinatorics.AeqB.gosper_step2_c_minimal`
- **text p.94 eq 5.3.8**, p.94 [CO-408]: Alternative to resultants: find irreducible factors u of f and v of g with v(n)=u(n-h); the only possible shift is h=(A-B)/d from the subleading coefficients — *proved proved here* — `UndergradKB.Combinatorics.AeqB.shift_subleading`, `UndergradKB.Combinatorics.AeqB.shift_eq_of_subleading`, `UndergradKB.Combinatorics.AeqB.shift_unique`
- **text p.94-95 cases 1,2a,2b**, p.94 [CO-409]: Possible degrees of a polynomial solution x of (5.2.6): deg c - max(deg a,deg b) if leading terms do not cancel; else deg c - deg a +1 or (B-A)/lc(a) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.natDegree_solution_case1`, `UndergradKB.Combinatorics.AeqB.coeff_gosper_lhs_case2`, `UndergradKB.Combinatorics.AeqB.natDegree_solution_case2`

#### Section 5.5

- **Ex 5.5.1**, p.96 [CO-411]: The partial sum of k! is not a hypergeometric term plus a constant (k! is not Gosper-summable) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.not_isGosperSummable_factorial`
- **text p.99 eq 5.5.2**, p.99 [CO-049]: Iterated sum identity: s-fold repeated partial sums of C(2n1,n1)/4^n1 equal C(2n+2s,2s)C(2n,n)/(C(n+s,s)4^n), proved by induction using Gosper — *proved proved here* — `UndergradKB.Combinatorics.AeqB.iterCentral_eq`

#### Section 5.6

- **Def 5.6.1**, p.102 [CO-412]: Two hypergeometric terms are similar (s ~ t) if their ratio is a rational function of n; this is an equivalence relation — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsSimilar`, `UndergradKB.Combinatorics.AeqB.isSimilar_equivalence`
- **Prop 5.6.1**, p.102 [CO-413]: For non-constant hypergeometric s_n, the difference s_{n+1}-s_n is a hypergeometric term similar to s_n — *proved proved here* — `UndergradKB.Combinatorics.AeqB.isHypergeometric_sub_succ`
- **Prop 5.6.2**, p.102 [CO-414]: For hypergeometric s,t with s+t nonzero, s+t is hypergeometric iff s ~ t — *proved proved here* — `UndergradKB.Combinatorics.AeqB.isHypergeometric_add_iff`
- **Thm 5.6.1**, p.103 [CO-415]: If a sum of hypergeometric terms is zero, two of the terms are similar — *proved proved here* — `UndergradKB.Combinatorics.AeqB.exists_similar_of_sum_eq_zero`
- **Thm 5.6.2**, p.103 [CO-417]: Decision of rationality: with canonical factorizations of r and of B/A, t_n is rational iff A is monic and a=b=1 — *proved proved here* — `UndergradKB.Combinatorics.AeqB.isRational_iff_canonical_forms`
- **Prop 5.6.3**, p.103 [CO-416]: Any sum of a fixed number of hypergeometric terms can be rewritten as a sum of pairwise dissimilar ones — *proved proved here* — `UndergradKB.Combinatorics.AeqB.exists_dissimilar_sum`
- **Thm 5.6.3**, p.104 [CO-418]: If Gosper's algorithm fails on t_n, the partial sum is not expressible as any fixed-length linear combination of hypergeometric terms — *proved proved here* — `UndergradKB.Combinatorics.AeqB.not_closed_form_of_not_isGosperSummable`, `UndergradKB.Combinatorics.AeqB.gosper_failure_no_closed_form`
- **text p.105 algorithm**, p.105 [CO-419]: Extended Gosper algorithm: write a sum of hypergeometric terms as pairwise dissimilar terms u^(j), apply Gosper to each, keep partial sums of failures — *not formalized* — `UndergradKB.Combinatorics.AeqB.extended_gosper`

## Chapter 6

22 items; 21 with a Lean name; 18 proved proved here; 2 in Mathlib; 2 not formalized.


#### Section 6.1

- **text p.112 (6.1.3)**, p.112 [CO-420]: A telescoped recurrence for a summand F(n,k) is an identity sum_{j=0}^J a_j(n) F(n+j,k) = G(n,k+1)-G(n,k) with polynomial a_j and G/F rational in n,k. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Zeilberger.IsTelescopedRecurrence`
- **text p.112**, p.112 [CO-029]: Sum over i of C(n,i) equals 2^n (count bit strings by number of zeros). — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_2_17`, `Nat.sum_range_choose`
- **text p.113 (6.1.4)**, p.113 [CO-421]: Summing a telescoped recurrence over all k (G of compact support) gives the k-free recurrence sum_j a_j(n) f(n+j)=0 for f(n)=sum_k F(n,k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.finsum_recurrence`
- **text p.113**, p.113 [CO-422]: If the sum recurrence has order J=1, then f(n+1)/f(n)=-a_0/a_1 is rational and f is a hypergeometric term given by a product f(0)*prod(-a_0(j)/a_1(j)); constant coefficients case is solved by the characteristic equation. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.order_one_solution`, `UndergradKB.Combinatorics.AeqB.isHypergeometric_of_order_one`
- **Ex 6.1.1**, p.114 [CO-423]: For f(n)=sum_{0<=k<=n/3} 2^k n/(n-k) binom(n-k,2k) (Monthly problem 10424) one gets f(n)=2^{n-1}+cos(n pi/2) for n>=2, from the order-3 constant-coefficient recurrence (N^2+1)(N-2)f=0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.MonthlySum.Fsum`, `UndergradKB.Combinatorics.AeqB.MonthlySum.fSum`, `UndergradKB.Combinatorics.AeqB.MonthlySum.fSum_formula`, `UndergradKB.Combinatorics.AeqB.MonthlySum.fSum_formula_cos`

#### Section 6.2

- **Thm 6.2.1**, p.115 [CO-424]: Every proper hypergeometric term F(n,k) satisfies a nontrivial telescoped recurrence with G/F rational (existence of creative telescoping, obtained from the two-variable recurrence of the Fundamental Theorem and a minimal-degree-in-K argument). — *not formalized* — `UndergradKB.Combinatorics.AeqB.Zeilberger.isTelescopedRecurrence_of_two_variable`, `UndergradKB.Combinatorics.AeqB.Zeilberger.exists_nontrivial_telescoped`

#### Section 6.3

- **text p.116-119 (6.3.1)-(6.3.12)**, p.116 [CO-425]: Zeilberger's algorithm (creative telescoping): for a fixed order J, form t_k=sum a_j F(n+j,k), reduce to a Gosper-type problem p2(k)b(k+1)-p3(k-1)b(k)=p(k) with the a_j unknown, solve the linear system for a_j and polynomial b, else increase J; output the telescoped recurrence and G. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Zeilberger.tSeq_ratio`, `UndergradKB.Combinatorics.AeqB.Zeilberger.zeilberger_sound`
- **text p.118-119 (6.3.10)-(6.3.12)**, p.118 [CO-426]: With the term ratio of t_k written in Gosper canonical form p(k+1)p2(k)/(p(k)p3(k)) (p=p0*p1), t_k is indefinitely summable iff p2(k)b(k+1)-p3(k-1)b(k)=p(k) has a polynomial solution b; then G=p3(k-1)b(k)t_k/p(k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Zeilberger.gosper_step`, `UndergradKB.Combinatorics.AeqB.Zeilberger.zeilberger_sound`
- **text p.118 (after 6.3.11)**, p.118 [CO-427]: The coefficients p2,p3 and the polynomial degree bound do not depend on the unknown a_j and the right-hand side p(k) is linear in them, so finding a_j and b is a linear-algebra problem in Delta+J+2 unknowns. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Zeilberger.zeilbergerSystem`, `UndergradKB.Combinatorics.AeqB.Zeilberger.zeilbergerSystem_eq_zero_iff`

#### Section 6.4

- **Ex 6.4.1**, p.119 [CO-032]: Sum over i of C(n,i)^2 equals C(2n,n). — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_2_20`, `Nat.sum_range_choose_sq`
- **Ex 6.4.2**, p.120 [CO-377]: sum_k (-1)^k binom(n,k)/binom(x+k,k) = x/(x+n), via telescoped recurrence with R=k(x+k)/(n+1-k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.kummer_sum`
- **Ex 6.4.3**, p.121 [CO-378]: sum_k (-1)^k binom(n+1,k) binom(2n-2k+1,n) = 1 for n>=0 (WZ-type recurrence (N-1)F=G(k+1)-G(k)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.alt_sum_choose_choose`
- **Ex 6.4.4**, p.121 [CO-044]: sum_s (-1)^s C(2m,s)^3 = (-1)^m (3m)!/(m!)^3 (Dixon-type alternating cube sum). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.alternating_choose_cube`
- **text p.122**, p.122 [CO-428]: Continuous analogue of creative telescoping: for proper F(n,y) one finds a recurrence for integral F(n,y)dy, and a differential equation for integral F(x,y)dy; implemented as AZd, AZc. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Continuous.integral_recurrence`, `UndergradKB.Combinatorics.AeqB.Continuous.integral_telescoping_recurrence`, `UndergradKB.Combinatorics.AeqB.Continuous.integral_telescoping_ode`

#### Section 6.5

- **text p.123 (6.5.1)**, p.123 [CO-379]: sum_k binom(n,2k) binom(2k,k) 4^{-k} = 2^{-(n-1)} binom(2n-1,n-1) for n>=1 (recurrence (2n+1)f(n)=(n+1)f(n+1), G=(n-2k)n!/((n-2k)! k!^2 4^k)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.sum_choose_two_mul_centralBinom_div`
- **text p.123**, p.123 [CO-545]: Recurrences produced by creative telescoping or Sister Celine are self-certifying: dividing by F and cancelling factorials reduces correctness to a polynomial/rational identity check. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.recurrence_of_ratio_identity`, `UndergradKB.Combinatorics.AeqB.recurrence_iff_ratio_identity`
- **Ex 6.5.1**, p.124 [CO-048]: Reed-Dawson identity: sum_k C(n,k)C(2k,k)(-2)^(n-k) is 0 for odd n and C(n,n/2) for even n, from n f(n)=4(n-1)f(n-2) — *proved proved here* — `UndergradKB.Combinatorics.AeqB.reed_dawson`
- **Ex 6.5.2**, p.125 [CO-380]: sum_k binom(n+k,2k) binom(2k,k) (-1)^k/(k+1) equals 1 for n=0 and 0 for n>=1 (first order recurrence). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.sum_choose_centralBinom_alt_div`
- **Ex 6.5.3**, p.125 [CO-381]: The determinant det(binom(i+j-x,2i-j)) (i,j<n) of Mills-Robbins-Rumsey is a polynomial in x all of whose roots are integers or half-integers; it is proved by Andrews' triangularizing matrix E_n whose product M_n E_n has entries given by hypergeometric sums, each certified by Zeilberger's algorithm. — *not formalized* — –
- **text p.126 (6.5.4)**, p.126 [CO-429]: q-analogue of Zeilberger's algorithm: for F(n,k) with ratios rational in q^n,q^k it finds Omega(N,n)F=G(n,k+1)-G(n,k) with G=RF, R rational in q^n,q^k (program qzeil). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.QAnalogue.q_zeilberger_sound`, `UndergradKB.Combinatorics.AeqB.QAnalogue.certificate_eq_ratio_mul`
- **text p.126**, p.126 [CO-430]: Paule's symmetrization: an unrestricted sum over k of f(n,k) equals the sum of (f(n,k)+f(n,-k))/2 since the odd part sums to zero, and the symmetrized summand can have much lower recurrence order. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities2.finsum_symmetrize`, `UndergradKB.Combinatorics.AeqB.Identities2.sum_range_symmetrize`
- **text p.127 (6.5.5)-(6.5.7)**, p.127 [CO-382]: Finite Rogers-Ramanujan-type identity (6.5.5) in symmetrized form (6.5.6) is certified by an order-2 operator A(N)=(1-q^n)-(1+q-q^n+q^{2n-1})N^{-1}+qN^{-2} with explicit certificates R_L,R_R (order 5 for the unsymmetrized form). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.RogersRamanujan.paule_left`, `UndergradKB.Combinatorics.AeqB.RogersRamanujan.paule_right`

## Chapter 7

31 items; 27 with a Lean name; 25 proved proved here; 1 partly; 5 not formalized.


#### Section 7.1

- **Ex 7.1.1**, p.132 [CO-444]: The WZ certificate for sum_k binom(n,k)^2/binom(2n,n)=1 is R(n,k)=-k^2(3n-2k+3)/(2(2n+1)(n-k+1)^2). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.central_cert`
- **text p.132 (7.1.2)**, p.132 [CO-443]: A WZ pair is a pair (F,G) of hypergeometric terms with F(n+1,k)-F(n,k)=G(n,k+1)-G(n,k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.WZEq`, `UndergradKB.Combinatorics.AeqB.IsWZPair`
- **text p.133-134**, p.133 [CO-445]: Finding a WZ certificate: normalize the summand to F with sum 1, feed F(n+1,k)-F(n,k) to Gosper's algorithm; if Gosper succeeds the result G is the WZ mate and R=G/F is the certificate, and if Gosper fails the method fails (no theorem guarantees existence; there are true identities lacking a mate). — *not formalized* — `UndergradKB.Combinatorics.AeqB.wz_certificate_via_gosper`
- **Thm 7.1.1**, p.134 [CO-446]: If (F,G) is a WZ pair and G(n,k)->0 as k->+-infinity for each n>=0, then sum_k F(n,k) is independent of n (constant). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.WZEq.tsum_const`
- **Thm 7.1.1**, p.134 [CO-447]: Companion identity: if also F(n,k)->f_k as n->infinity and sum_{n<=N} G(n,-L)->0, then sum_{n>=0} G(n,k) = sum_{j<=k-1}(f_j-F(0,j)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.WZEq.companion`
- **text p.134**, p.134 [CO-448]: Proof from a certificate R(n,k): normalize F=f/r(n), set G=R F, check F(n+1,k)-F(n,k)=G(n,k+1)-G(n,k) as a rational-function identity after dividing by factorials, then check the identity for a single n. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.wz_eq_of_ratio_identity`, `UndergradKB.Combinatorics.AeqB.wz_eq_iff_ratio_identity`, `UndergradKB.Combinatorics.AeqB.wzEq_of_ratio_identity`
- **text p.136 (I)**, p.136 [CO-449]: Gauss's 2F1(1) identity is certified by R(n,k)=(k+1)(k+c)/(n(n+1-c)) for the stated factorial summand. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.gauss_cert`
- **text p.136 (II)**, p.136 [CO-450]: Kummer's 2F1(-1) identity is certified by an explicit rational R(n,k) (denominator 2(2n-k+c+1)(2n-k+c)(2n-k+2)(2n-k+1)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.kummer_cert`
- **text p.136 (III)**, p.136 [CO-451]: Saalschutz's 3F2 identity is certified by R(n,k)=k(c+k-1)(a+b-c+k-n)/((b-c-n)(c-a+n)(1-k+n)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.saal_cert`
- **text p.136-137 (IV)**, p.136 [CO-452]: Dixon's identity sum (-1)^k binom(n+b,n+k)binom(n+c,c+k)binom(b+c,b+k) = (n+b+c)!/(n!b!c!) is certified by R=(k+b)(k+c)/(2(k-n-1)(n+b+c+1)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dixon_cert`
- **text p.137 (V)**, p.137 [CO-453]: Clausen's 4F3 identity (summand phi(k)phi(n-k)psi(n)) is certified by an explicit rational function R(n,k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.clausen_cert`, `UndergradKB.Combinatorics.AeqB.clausen_cert_int`
- **text p.137 (VI)**, p.137 [CO-454]: Dougall's 7F6 identity is certified by an explicit rational R(n,k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dougall_wz`

#### Section 7.3

- **Ex 7.3.1**, p.138 [CO-455]: Companion of sum binom(n,k)^2 = binom(2n,n): sum_{n>=0} (3n-2k+1)/(2n+1) * binom(n,k)^2/binom(2n,n) = 2 for k>=0 (new identity). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Companions.companion_sum_choose_sq`
- **Ex 7.3.2**, p.139 [CO-456]: The companion of the identity sum_k (n-i)!(n-j)!(i-1)!(j-1)!/((n-1)!(k-1)!(n-i-j+k)!(i-k)!(j-k)!)=1 (cert R=(k-1)/n) is Gauss's 2F1(1) identity; the same summand also sums to 1 over i. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities3d.gauss_companion`
- **Ex 7.3.3**, p.140 [CO-457]: The companion of the full Saalschutz identity expresses a nonterminating 3F2(1) as a partial sum of Gauss's 2F1(1) series (valid for c>a+b, integer k>0). — *not formalized* — –
- **Ex 7.3.4**, p.140 [CO-050]: Vandermonde sum_k binom(a,k)binom(n,k)=binom(n+a,a) has WZ certificate R=k^2/((k-1-n)(1+a+n)) and companion sum_{n>=0} binom(n,k)/binom(n+a+1,n) = (a+1)/((k+1)binom(a,k+1)) for integer a>k>=0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.vand_cert`, `UndergradKB.Combinatorics.AeqB.Companions.vandermonde_companion`, `UndergradKB.Combinatorics.AeqB.vandermonde_sum`
- **text p.141-142 (7.3.6)**, p.141 [CO-458]: Dual identities: replacing a numerator factorial (an+bk+c)! by (-1)^{an+bk}/(-1-an-bk-c)! in both F and its mate G keeps a WZ pair (the factor ratio is period-1 by the gamma reflection formula). — *partly* — `Complex.Gamma_mul_Gamma_one_sub`, `Real.Gamma_mul_Gamma_one_sub`
- **Ex 7.3.5**, p.142 [CO-460]: Dual of the sum-of-squares identity: sum_k (3k-2n) binom(n,k) binom(2k,k) = 0 for n>=0, obtained via the dual pair F'=(-3k+2n)/2 binom(n,k)binom(2k,k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.sum_dual_squares`
- **text p.142 (7.3.7)**, p.142 [CO-459]: The map (F(n,k),G(n,k)) -> (G(-k-1,-n),F(-k,-n-1)) sends WZ pairs to WZ pairs. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.WZEq.dual`
- **text p.143-144 (7.3.8)**, p.143 [CO-462]: For a WZ pair with support of F containing [0,n], the restricted sum has an n-free-summand form: sum_{k=0}^n F(n,k) = F(0,0)+sum_{j=1}^n (F(j,j)+G(j-1,j)); this gives O(N) table-making and asymptotics. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.restricted_sum_formula`
- **text p.143**, p.143 [CO-461]: Dual of sum binom(n,k)=2^n is sum (-1)^k binom(n+k,k) 2^{n-k}=1; Saalschutz is self-dual; a dual of Dixon is a special case of Saalschutz; a dual of Vandermonde is a special case of Gauss 2F1 (sum (-1)^k binom(n+k,k)binom(n,k)... = binom(b,n)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities2.dual_sum_choose`, `UndergradKB.Combinatorics.AeqB.Identities2.dual_vandermonde`
- **Ex 7.3.6**, p.144 [CO-463]: With F=binom(3n,k)/8^n: 8^{-n} sum_{k<=n} binom(3n,k) = 1 + (2/3) sum_{j=1}^n (2-j-5j^2)/((3j-1)(3j-2)) 8^{-j} binom(3j,j); consequently the sum is asymptotic to twice its last term. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.partial_choose_three`, `UndergradKB.Combinatorics.AeqB.PartialSumAsymptotic.partial_sum_ratio_tendsto`, `UndergradKB.Combinatorics.AeqB.PartialSumAsymptotic.partial_sum_isEquivalent`
- **text p.145 (Gessel approach 2)**, p.145 [CO-464]: A WZ function is a summand F(a,b,c,...,k) with sum_k F=1 and a WZ mate G; free parameters may be shifted by multiples of the running variable n, so all parameters are on an equal footing. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsWZFunction`, `UndergradKB.Combinatorics.AeqB.IsWZFunction.shift_param`
- **text p.145 (Gessel approach 3-5)**, p.145 [CO-465]: If (F,G) is a WZ pair then so is (G(k,n),F(k,n)); also F(n+alpha,k+beta), F(-n,k) and F(n,-k) are WZ functions; shifts can be chosen to make the transposed sum terminate. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.WZEq.transpose`, `UndergradKB.Combinatorics.AeqB.WZEq.shift`, `UndergradKB.Combinatorics.AeqB.WZEq.neg_left`, `UndergradKB.Combinatorics.AeqB.WZEq.neg_right`
- **text p.145-146**, p.145 [CO-466]: Gessel's algorithm for new terminating hypergeometric identities: take a WZ function with free parameters, substitute parameters affine in n, find the mate by Gosper, transpose and shift so the sum terminates, evaluate the constant at one n. — *not formalized* — –

#### Section 7.4

- **text p.146 (7.4.1)**, p.146 [CO-467]: Starting from Dixon's WZ function with a->a+n, b->b-n one derives the new identity that a certain terminating 5F4(1) equals 0 (eq 7.4.1). — *not formalized* — –
- **text p.147**, p.147 [CO-468]: Three further Gessel identities (a 3F2 with ratio of Pochhammers (c+2/3)_n(1/3)_n/((1-c)_n(4/3)_n), a second 3F2 with (1/3-b)_n/(1/3+b)_n, and a 4F3 equal to (5/2)_n(11/6)_n/((3/2)_n(7/2)_n) up to a constant) are certified by explicit R(n,k). — *not formalized* — –

#### Section 7.5

- **Ex 7.5.1**, p.148 [CO-469]: The identity sum_k 2^{k+1}(k+1)(2n-k-2)! n!/((n-k-1)!(2n)!)=1 has certificate R=k/(2(k-n-1)) and mate G=-n!/(2^{n+1}(k-1)!(n-k+1)!). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.half_mate`, `UndergradKB.Combinatorics.AeqB.half_mate_eq`, `UndergradKB.Combinatorics.AeqB.two_cert`
- **Ex 7.5.2**, p.148 [CO-470]: Companion of sum_k k binom(n+1,k)binom(x,k)/((n+1)binom(n+x,n+1))=1: sum_{n>=0} n!(n+1)!/((n-k+2)!(x+n+1)!) = (k-2)!/(binom(x,k)(x-1)!) for k>=2, x>k, a nonterminating case of Gauss 2F1. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities2.companion_binomial`, `UndergradKB.Combinatorics.AeqB.Identities2.companion_factorial`
- **text p.149-150 (7.5.2)**, p.149 [CO-471]: A WZ pair is exactly the order-1 case of creative telescoping: program ct returning (N-1,R) means Omega=N-1 so (N-1)F=G(k+1)-G(k) with G=RF; WZ mates are obtained from ct after normalizing the sum to 1. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Zeilberger.wzEq_iff_isTelescopedRecurrence`
- **Ex 7.5.3**, p.149 [CO-444]: The WZ certificate for sum_k binom(n,k)^2/binom(2n,n)=1 is R(n,k)=-k^2(3n-2k+3)/(2(2n+1)(n-k+1)^2). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.central_cert`

## Chapter 8

46 items; 40 with a Lean name; 32 proved proved here; 1 in Mathlib; 11 not formalized; 2 not a result.


#### Section 8.1

- **Def 8.1.1**, p.151 [CO-475]: A function of n has closed form if it equals a linear combination of a fixed number (independent of all parameters) of hypergeometric terms. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsClosedForm`
- **text p.151**, p.151 [CO-476]: Decision procedure for closed form of a definite sum over k of a proper hypergeometric summand: find a recurrence by creative telescoping, find all hypergeometric solutions with Hyper, match enough initial values. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.closedForm_dissimilar_solutions`
- **Ex 8.1.1**, p.152 [CO-051]: Sum over k of C(tk+r,k) C(tn-tk+s,n-k) r/(tk+r) equals C(tn+r+s,n) (Rothe-Hagen type convolution quoted from Concrete Mathematics); t=3,r=1,s=0 gives a sum that is a single hypergeometric term although creative telescoping first returns an order-2 recurrence. — *not formalized* — –
- **text p.152**, p.152 [CO-477]: Conjecture: for every d there are integers t,r,s such that creative telescoping applied to the sum in (8.1.1) yields recurrence order at least d, even though the sum satisfies a first-order one. — *not a result* — –
- **Prop 8.1.1**, p.153 [CO-431]: For F hypergeometric in n and k with hypergeometric sum f(n), creative telescoping returns a first-order recurrence for f exactly when the WZ method proves sum_k F = f. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Prop811.CTFirstOrder`, `UndergradKB.Combinatorics.AeqB.Prop811.WZProves`, `UndergradKB.Combinatorics.AeqB.Prop811.ctFirstOrder_iff_wzProves`
- **text p.153-154**, p.153 [CO-476]: Decision procedure for closed form of a definite sum over k of a proper hypergeometric summand: find a recurrence by creative telescoping, find all hypergeometric solutions with Hyper, match enough initial values. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.closedForm_dissimilar_solutions`

#### Section 8.2

- **Ex 8.2.1**, p.155 [CO-479]: In the full sequence ring K^N a first-order equation with sequence or polynomial coefficients can have solution space of dimension 0, k, or infinity, motivating the almost-everywhere quotient. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.not_finite_firstOrderSol_even_odd`, `UndergradKB.Combinatorics.AeqB.firstOrderSol_even_neg_one`, `UndergradKB.Combinatorics.AeqB.finrank_exSol`
- **Ex 8.2.2**, p.155 [CO-479]: In the full sequence ring K^N a first-order equation with sequence or polynomial coefficients can have solution space of dimension 0, k, or infinity, motivating the almost-everywhere quotient. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.not_finite_firstOrderSol_even_odd`, `UndergradKB.Combinatorics.AeqB.firstOrderSol_even_neg_one`, `UndergradKB.Combinatorics.AeqB.finrank_exSol`
- **def p.155 (linear recurrence operator)**, p.155 [CO-478]: Shift operator N on sequences over K, linear recurrence operators sum a_k N^k with sequence coefficients, order r when a_r and a_0 nonzero, Ker L, homogeneous vs inhomogeneous equations Ly=f. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.SeqOp.shiftN`, `UndergradKB.Combinatorics.AeqB.SeqOp.recOp`, `UndergradKB.Combinatorics.AeqB.SeqOp.HasOrder`, `UndergradKB.Combinatorics.AeqB.SeqOp.mem_ker_recOp`
- **def p.156 (S(K))**, p.156 [CO-480]: S(K) is the ring of sequences modulo the ideal of eventually-zero sequences (equality almost everywhere); the shift N descends to an automorphism. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.SeqRing`, `UndergradKB.Combinatorics.AeqB.SeqRing.shift`
- **text p.156**, p.156 [CO-481]: In S(K) a sequence is a unit iff it is eventually nonzero; a nonzero non-unit is exactly a zero divisor (infinitely many zero and nonzero terms). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.SeqRing.isUnit_coe_iff`, `UndergradKB.Combinatorics.AeqB.SeqRing.nonzero_not_isUnit_iff`, `UndergradKB.Combinatorics.AeqB.SeqRing.isZeroDivisor_iff_not_isUnit`
- **Thm 8.2.1**, p.157 [CO-482]: If L is a recurrence operator of order r on S(K) with leading and trailing coefficients units then dim Ker L = r. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.finrank_kerOp`
- **Def 8.2.1**, p.158 [CO-383]: A nonzero sequence is hypergeometric over K if p Nx + q x = 0 for nonzero polynomial sequences p,q, equivalently x(n+1)/x(n) is rational; geometric when the ratio is constant. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsHypergeometric`, `UndergradKB.Combinatorics.AeqB.isHypergeometric_iff`, `UndergradKB.Combinatorics.AeqB.isHypergeometric_iff_ratio`
- **Def 8.2.1**, p.158 [CO-483]: Polynomial and rational sequences over K are those equal almost everywhere to p(n) or r(n); every polynomial sequence is rational and every nonzero rational sequence is a unit. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.SeqRing.IsPolynomialSeq`, `UndergradKB.Combinatorics.AeqB.SeqRing.IsRationalSeq`, `UndergradKB.Combinatorics.AeqB.SeqRing.IsPolynomialSeq.isRationalSeq`, `UndergradKB.Combinatorics.AeqB.SeqRing.IsRationalSeq.isUnit`
- **Prop 8.2.1**, p.158 [CO-484]: If Ny = ay in S(K) with y nonzero then both y and a are units. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.SeqRing.isUnit_of_shift_eq`
- **Cor 8.2.1**, p.158 [CO-485]: Every hypergeometric sequence in S(K) is a unit. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.SeqRing.IsHypergeometric.isUnit`

#### Section 8.3

- **Prop 8.3.1**, p.160 [CO-486]: For L = sum p_i N^i with q_j = sum_i C(i,j) p_i and b = max(deg q_j - j), any polynomial solution of Ly=f has degree at most max(deg f - b, -b-1, largest nonnegative integer root of the degree polynomial alpha). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.degree_cases`, `UndergradKB.Combinatorics.AeqB.natDegree_le_of_applyOp_eq`, `UndergradKB.Combinatorics.AeqB.natDegree_le_book_bound`
- **text p.160 (Algorithm Poly)**, p.160 [CO-487]: Algorithm Poly: compute q_j, the degree bound d, then find all polynomial solutions of degree at most d by undetermined coefficients. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.poly_complete`

#### Section 8.4

- **Thm 8.4.1**, p.162 [CO-489]: If y is a nonzero solution with rational ratio S = z a c(n+1)/(b c(n)) in canonical form, then sum alpha_i z^i = 0, a divides p_0, b divides p_d(n-d+1), and c solves the auxiliary recurrence (8.4.6). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyper_necessary`
- **Thm 8.4.1**, p.162 [CO-490]: Hyper finds a hypergeometric solution when one exists and proves that none exists when it returns 0 (a finite candidate search). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyper_candidate_sound`, `UndergradKB.Combinatorics.AeqB.hyper_candidate_complete`, `UndergradKB.Combinatorics.AeqB.hyper_exists_iff`
- **text p.162 (Algorithm Hyper)**, p.162 [CO-488]: Algorithm Hyper: loop over monic factors a of p_0 and b of p_d(n-d+1) and nonzero roots z of the leading-coefficient polynomial, solve the auxiliary recurrence for polynomial c with Poly, and return y with y(n+1)/y(n) = z a c(n+1)/(b c(n)). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyper_exists_iff`, `UndergradKB.Combinatorics.AeqB.hyper_candidates_finite`
- **text p.162 (second-order derivation)**, p.162 [CO-490]: Hyper finds a hypergeometric solution when one exists and proves that none exists when it returns 0 (a finite candidate search). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyper_candidate_sound`, `UndergradKB.Combinatorics.AeqB.hyper_candidate_complete`, `UndergradKB.Combinatorics.AeqB.hyper_exists_iff`
- **text p.163**, p.163 [CO-491]: Conversely, any z, a, b and polynomial c solving the auxiliary recurrence give a ratio S whose solution y satisfies the original recurrence (soundness of Hyper). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyper_sound`
- **Ex 8.4.2**, p.164 [CO-493]: The sum of C(n,k) C(n+k,k) over k satisfies a second-order recurrence with polynomial coefficients that has no hypergeometric solution, so the sum is not a hypergeometric term. — *not formalized* — `UndergradKB.Combinatorics.AeqB.Companions.delannoySum_rec`, `UndergradKB.Combinatorics.AeqB.Companions.aperySum_rec`
- **text p.164**, p.164 [CO-492]: Worst-case time of Hyper is exponential in the degrees of the coefficients when there is no hypergeometric solution; speedups by ordering degree differences d(a,b). — *not formalized* — –
- **Ex 8.4.3**, p.165 [CO-494]: The number of permutations with all cycles of length at most r (r at least 2), e.g. involutions with y(n)=y(n-1)+(n-1)y(n-2), satisfies a recurrence with no hypergeometric solution; so involution counts are P-recursive but not hypergeometric, and order-d recurrences without hypergeometric solutions exist for each d>=2. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.not_hypergeometric_involution_rec`, `UndergradKB.Combinatorics.AeqB.Involutions.involutionNumber_rec`
- **text p.166**, p.166 [CO-495]: qHyper: q-analogue of Hyper finding all q-hypergeometric solutions of q-difference equations with rational coefficients (Abramov, Paule, Petkovsek). — *not formalized* — –

#### Section 8.6

- **Ex 8.6.1**, p.167 [CO-191]: Derangement numbers satisfy d_n=(n-1)(d_{n-1}+d_{n-2}) and d_n=n d_{n-1}+(-1)^n. — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_7_22_rec`, `UndergradKB.Combinatorics.Course.KellerTrotter.ex_7_22_alt`, `numDerangements_add_two`, `numDerangements_succ`
- **text p.167**, p.167 [CO-496]: A d'Alembertian sequence is an iterated indefinite sum of hypergeometric terms, equivalently annihilated by a product of first-order operators with rational coefficients; these sequences form a ring. — *not formalized* — `UndergradKB.Combinatorics.AeqB.IsDAlembertian.exists_chain`, `UndergradKB.Combinatorics.AeqB.IsDAlembertian.exists_firstOrder_product`
- **text p.167**, p.167 [CO-497]: To find all closed-form (d'Alembertian) solutions: find one hypergeometric solution with Hyper, reduce the order, solve recursively, and use Gosper's algorithm to close up antidifferences. — *not formalized* — `UndergradKB.Combinatorics.AeqB.RecOp.reduction_of_order`, `UndergradKB.Combinatorics.AeqB.RecOp.act_hyper_mul`

#### Section 8.7

- **Prop 8.7.1**, p.168 [CO-498]: For a recurrence operator L and hypergeometric term h with Lh nonzero, Lh is a hypergeometric term similar to h (a rational multiple of h). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.RecOp.isHypergeometric_act`
- **Thm 8.7.1**, p.169 [CO-499]: If L kills a sum of pairwise dissimilar hypergeometric terms then L kills each term separately. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.RecOp.act_eq_zero_of_sum_dissimilar`
- **Cor 8.7.1**, p.169 [CO-500]: The solutions of Ly=0 lying in the linear hull of hypergeometric terms have a basis consisting of hypergeometric terms, so the recursive algorithm of Sec 8.6 finds all closed-form solutions. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyperHull`, `UndergradKB.Combinatorics.AeqB.kernel_inter_hull_basis`
- **text p.169**, p.169 [CO-026]: The derangement number is the nearest integer to n!/e, a nice formula though not a closed form in the hypergeometric sense. — *proved proved here* — `UndergradKB.Combinatorics.abs_numDerangements_sub_factorial_div_e_lt`
- **text p.169**, p.169 [CO-500]: The solutions of Ly=0 lying in the linear hull of hypergeometric terms have a basis consisting of hypergeometric terms, so the recursive algorithm of Sec 8.6 finds all closed-form solutions. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.hyperHull`, `UndergradKB.Combinatorics.AeqB.kernel_inter_hull_basis`
- **text p.169-170**, p.169 [CO-501]: Conjecture (folklore): for p at least 3 the sum of p-th powers of C(n,k) has no closed form; status of partial binomial sums h(p,r) is open. — *not a result* — –

#### Section 8.8

- **Thm 8.8.1**, p.170 [CO-502]: The sum of cubes of C(n,k), derangement numbers, central trinomial coefficients, involution numbers, and the sum of the first third of C(3n,k) are not sums of a fixed number of hypergeometric terms. — *not formalized* — –

#### Section 8.9

- **Prop 8.9.1**, p.171 [CO-503]: Representation of an element of the linear hull of hypergeometric terms as a sum of pairwise dissimilar hypergeometric terms is unique up to order. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dissimilar_repr_unique`, `UndergradKB.Combinatorics.AeqB.dissimilar_repr_unique_fin`
- **text p.171-172**, p.171 [CO-504]: Algorithm for Ly=f over the hypergeometric linear hull: split f into dissimilar terms, solve L_j r_j = 1 for rational r_j (Abramov's rational-solution algorithm), add a Hyper basis of Ker L. — *not formalized* — `UndergradKB.Combinatorics.AeqB.RecOp.act_mul_eq_conjOp`, `UndergradKB.Combinatorics.AeqB.RecOp.act_mul_eq_self_iff`, `UndergradKB.Combinatorics.AeqB.RecOp.act_sum_particular`
- **text p.172**, p.172 [CO-505]: Recurrence operators multiply by the commutation rule N p(n) = p(n+1) N, i.e. (a(n)N^r)(b(n)N^s) = a(n)b(n+r)N^{r+s}; they form a noncommutative ring (Laurent operators with N invertible in Ch.9). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.RecOp.term_mul_term`, `UndergradKB.Combinatorics.AeqB.RecOp.N_mul_C`, `UndergradKB.Combinatorics.AeqB.RecOp.act_mul`, `UndergradKB.Combinatorics.AeqB.RecOp.act_N_act_C`
- **text p.172**, p.172 [CO-506]: For recurrence operators with rational coefficients and L2 nonzero there are Q,R with L1 = Q L2 + R and ord R < ord L2 (right division with remainder). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.skew_right_division`, `UndergradKB.Combinatorics.AeqB.ratfunc_right_division`
- **text p.172**, p.172 [CO-507]: Right-Euclidean algorithm computes greatest common right divisors (and least common left multiples) of recurrence operators. — *not formalized* — `UndergradKB.Combinatorics.AeqB.skew_gcrd`, `UndergradKB.Combinatorics.AeqB.ratfunc_gcrd`
- **text p.173**, p.173 [CO-508]: The minimal-order annihilating operator of a sequence right-divides every annihilating operator. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities3c.minimal_annihilator_dvd`
- **text p.173**, p.173 [CO-509]: If Ly=0 then L = L1 L2 with L2 the minimal operator of y, and hypergeometric solutions of Ly=0 correspond one-to-one to monic first-order right factors of L. — *not formalized* — `UndergradKB.Combinatorics.AeqB.RecOp.solution_of_right_factor`, `UndergradKB.Combinatorics.AeqB.RecOp.hyper_solution_of_right_factor`
- **def p.173 (adjoint operator)**, p.173 [CO-510]: The adjoint of L = sum p_k(n) N^k (order d) is L* = sum p_{d-k}(n+k) N^k. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.RecOp.adjoint`
- **text p.173-174**, p.173 [CO-511]: L** = N^d L N^{-d} and (LM)* = (N^d M* N^{-d}) L*, so left first-order factors of L correspond to right first-order factors of L*, and operators of order 2 and 3 factor completely using Hyper. — *not formalized* — `UndergradKB.Combinatorics.AeqB.RecOp.adjoint_adjoint_mul`

## Chapter 9

36 items; 26 with a Lean name; 22 proved proved here; 2 in Mathlib; 11 not formalized; 1 not a result.


#### Section 9.2

- **text p.183 (eq 9.2.3)**, p.183 [CO-505]: Recurrence operators multiply by the commutation rule N p(n) = p(n+1) N, i.e. (a(n)N^r)(b(n)N^s) = a(n)b(n+r)N^{r+s}; they form a noncommutative ring (Laurent operators with N invertible in Ch.9). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.RecOp.term_mul_term`, `UndergradKB.Combinatorics.AeqB.RecOp.N_mul_C`, `UndergradKB.Combinatorics.AeqB.RecOp.act_mul`, `UndergradKB.Combinatorics.AeqB.RecOp.act_N_act_C`
- **Def 9.2.1**, p.184 [CO-513]: A sequence is P-recursive (holonomic) if it satisfies a linear recurrence with polynomial coefficients. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsPRecursive`, `UndergradKB.Combinatorics.AeqB.IsHypergeometric.isPRecursive`
- **text p.184**, p.184 [CO-512]: The operators annihilating a given sequence form a left ideal of the operator ring; every nowhere-zero sequence is annihilated by the first-order operator N - x(n+1)/x(n), so polynomial coefficients are needed for a meaningful theory. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities3c.annihilatorIdeal`, `UndergradKB.Combinatorics.AeqB.Identities3c.nowhere_zero_first_order`
- **text p.185**, p.185 [CO-514]: Algorithm findrec: guess a recurrence of given order and degree for the beginning of a sequence by linear algebra (EKHAD, cf. gfun). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.findrecMap`, `UndergradKB.Combinatorics.AeqB.mem_ker_findrecMap_iff`, `UndergradKB.Combinatorics.AeqB.coeffs_mem_ker_findrecMap`, `UndergradKB.Combinatorics.AeqB.recOp_coeffs_mem_ker_findrecMap`
- **Def 9.2.2**, p.186 [CO-383]: A nonzero sequence is hypergeometric over K if p Nx + q x = 0 for nonzero polynomial sequences p,q, equivalently x(n+1)/x(n) is rational; geometric when the ratio is constant. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.IsHypergeometric`, `UndergradKB.Combinatorics.AeqB.isHypergeometric_iff`, `UndergradKB.Combinatorics.AeqB.isHypergeometric_iff_ratio`
- **def p.186 (multinomial coefficient)**, p.186 [CO-034]: Multinomial coefficient n!/(k1!...kr!) counts ways to color an n-set with k_i elements of color i. — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.def_p54_multinomial`, `Nat.multinomial`, `Nat.multinomial_spec`

#### Section 9.3

- **text p.187-188 (eq 9.3.1-9.3.3)**, p.187 [CO-515]: Operators with polynomial coefficients in n,k,N,K form the noncommutative algebra with relations NK=KN, Nn=(n+1)N, Kk=(k+1)K and others commuting; operators annihilating F combine as A P + B Q. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.recOpAlgebra`, `UndergradKB.Combinatorics.AeqB.Holonomic.relations`
- **text p.187-188**, p.187 [CO-432]: If S(N,n)F = (K-1)G and F,G vanish at plus or minus infinity, then summing over k shows a(n) = sum_k F(n,k) satisfies S(N,n)a = 0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.tsum_recurrence`
- **text p.187-189**, p.187 [CO-433]: Elimination: from operators P,Q annihilating a holonomic F, eliminate k (mod K-1) to get a k-free operator S and certificate G=CF, proving S a = 0; holonomicity guarantees success. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.elimination`
- **text p.189**, p.189 [CO-432]: If S(N,n)F = (K-1)G and F,G vanish at plus or minus infinity, then summing over k shows a(n) = sum_k F(n,k) satisfies S(N,n)a = 0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.tsum_recurrence`
- **def p.189 (Modified elimination problem)**, p.189 [CO-434]: Given P,Q find A,B,C with S = AP + BQ + (K-1)C free of K and k, left multiples allowed for P,Q and right multiples for K-1 (Almkvist's observation). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.modified_elimination`
- **text p.190-191 (Chu-Vandermonde)**, p.190 [CO-052]: Sum over k of C(n,k) C(b,k) equals C(n+b,b), derived and proved by elimination. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Companions.sum_choose_mul_choose`
- **text p.192 (Dixon's identity)**, p.192 [CO-364]: Dixon: sum_k (-1)^k C(a+b,a+k)C(a+c,c+k)C(b+c,b+k) = (a+b+c)!/(a!b!c!), and the well-poised 3F2 form with d=a-b+1, e=a-c+1. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.dixon`
- **def p.193 (discrete holonomic function)**, p.193 [CO-516]: A discrete multivariate function is holonomic if it satisfies as many independent polynomial-coefficient linear recurrences as possible without vanishing, in particular one in each variable. — *not formalized* — –
- **text p.193**, p.193 [CO-517]: Stafford's theorem: every holonomic function is described by just two generating linear recurrence equations. — *not formalized* — –
- **text p.193**, p.193 [CO-518]: Summing a holonomic function over any subset of its variables (or summing and integrating, for mixed discrete-continuous holonomic functions) gives a holonomic function of the remaining variables. — *not formalized* — –
- **text p.194-195**, p.194 [CO-203]: The generating function of p_n is the product over m>=1 of 1/(1-x^m). — *proved proved here* — `UndergradKB.Combinatorics.Recurrence.hasProd_partition_card`
- **text p.194**, p.194 [CO-212]: Rooted labeled trees counted by n^(n-1) have EGF T(x) with T = x e^T, a transcendental equation, and this sequence is not P-recursive. — *not formalized* — `UndergradKB.Combinatorics.AeqB.treeSeries_eq_X_mul_exp`
- **text p.194**, p.194 [CO-518]: Summing a holonomic function over any subset of its variables (or summing and integrating, for mixed discrete-continuous holonomic functions) gives a holonomic function of the remaining variables. — *not formalized* — –
- **text p.195**, p.195 [CO-213]: Bell numbers have EGF exp(e^x - 1) and satisfy B_{n+1} = sum C(n,k) B_k, an indefinite-order recurrence; the sequence is not P-recursive. — *not formalized* — `UndergradKB.Combinatorics.AeqB.bellSeries_eq_exp_exp_sub_one`, `UndergradKB.Combinatorics.bellNumber`, `UndergradKB.Combinatorics.bellNumber_succ`
- **def p.196 (q-hypergeometric, bi-basic)**, p.196 [CO-384]: A sequence is q-hypergeometric if a(k+1)/a(k) is rational in (q^k,q); bi-basic (p,q)-hypergeometric if the ratio is rational in (p,q,p^k,q^k). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.QAnalogue.IsQHypergeometric`, `UndergradKB.Combinatorics.AeqB.QAnalogue.IsBiBasicHypergeometric`
- **text p.198**, p.198 [CO-435]: If F(n,k) = -F(n,n+alpha-k) for an integer alpha then the sum over k of F vanishes. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.finsum_eq_zero_of_reflect`
- **text p.198**, p.198 [CO-436]: Creative anti-symmetrizing: for antisymmetric F it suffices that P F - (G(k+1)-G(k)) be antisymmetric rather than zero, possibly giving lower-order recurrences; idea not yet implemented. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.antisymmetrizing`
- **text p.198**, p.198 [CO-437]: Fundamental theorem of algorithmic proof theory (cited): for every proper hypergeometric multi-variable term F there are an operator P(N,n) and certificates G_i with P F = sum of forward differences of G_i. — *not formalized* — –
- **text p.198-199**, p.198 [CO-438]: For symmetric multisum summands it suffices that the symmetrization of P F - sum Delta_i G_i vanishes, giving r! P(sum F) = 0. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.symmetrizer_multisum`
- **text p.199**, p.199 [CO-519]: P-Di functions satisfy polynomial-coefficient equations in x, the doubling operator T f(x)=f(2x) and shift E; the operator ring has relations T x = 2xT, E x = xE + E, ET = TE^2, and P-Di functions form an algebra. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.pdi_relations`
- **text p.199-200**, p.199 [CO-520]: For Di-holonomic F(x,y), eliminating y and using that integrals are invariant under y -> y+1 and scale by 1/2 under y -> 2y shows the integral of F over y is P-Di. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Holonomic.integral_annihilated`

#### Section 9.11

- **text p.200 (eq 9.11.1, 9.11.2)**, p.200 [CO-053]: Abel-type identity: sum over k of C(n,k) (k+r)^(k-1) (s-k)^(n-k) = (r+s)^n / r, with special case sum C(n,k)(k+1)^(k-1)(n-k+1)^(n-k) = (n+2)^n; summand not holonomic but handled by elimination. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities2.abel_identity`, `UndergradKB.Combinatorics.AeqB.Identities2.abel_special`
- **text p.200**, p.200 [CO-033]: (x+y)^n equals the sum over i of C(n,i) x^(n-i) y^i. — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.thm_2_30`, `add_pow`, `Commute.add_pow`
- **text p.200**, p.200 [CO-495]: qHyper: q-analogue of Hyper finding all q-hypergeometric solutions of q-difference equations with rational coefficients (Abramov, Paule, Petkovsek). — *not formalized* — –
- **text p.201 (eq 9.11.3)**, p.201 [CO-054]: Euler's identity: sum over k of (-1)^k C(n,k) (x-k)^n = n!, proved here by elimination and induction on n. — *proved proved here* — `UndergradKB.Combinatorics.AeqB.euler_identity`
- **text p.202**, p.202 [CO-538]: Anglesio's identity: integral from 0 to infinity of e^(-ax)(1-e^(-x))^n / x^r dx = (-1)^r/(r-1)! sum_k (-1)^k C(n,k)(a+k)^(r-1) log(a+k), proved by checking a system of difference-differential equations plus initial conditions (semi-holonomic). — *not formalized* — –
- **text p.203**, p.203 [CO-352]: Cauchy identity: prod over i,j of 1/(1 - x_i y_j) = sum over partitions lambda of s_lambda(x) s_lambda(y). — *not formalized* — –
- **text p.203**, p.203 [CO-385]: Pfaff-Saalschutz: C(a+b,a+k) C(a+c,c+k) C(b+c,b+k) = sum over n of (a+b+c-n)!/((a-n)!(b-n)!(c-n)!(n+k)!(n-k)!), stated as a binomial-product identity found by elimination (Exercise 9.14.3). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.Identities3.pfaff_saalschutz`
- **text p.203-204**, p.203 [CO-539]: Mehler's formula: sum H_n(x)H_n(y) t^n / n! = (1-4t^2)^(-1/2) exp(y^2 - (y-2xt)^2/(1-4t^2)) for Hermite polynomials, with Foata's combinatorial proof and an automatable derivation. — *not formalized* — –
- **text p.205-208**, p.205 [CO-546]: Appendix A documents Maple (EKHAD ct, zeil, celine, findrec, AZ programs) and Mathematica (Gosper, Hyper, WZ) implementations of the algorithms, e.g. ct returns an operator and certificate with ope F = G(k+1)-G(k). — *not a result* — –
