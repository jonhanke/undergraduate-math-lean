# Course outline: Stitz-Zeager (precalculus)

Generated from [`docs/coverage/precalculus/checklist.md`](../../coverage/precalculus/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build Precalculus` builds this topic.

329 items in 11 chapters; 318 with a Lean name (96.7%).

## Chapter 1

34 items; 24 with a Lean name; 17 proved proved here; 7 in Mathlib; 10 not a result.

- **Definition 1.1 p.13**, p.13 [PC-001]: A set is a collection of elements with well-defined membership. — *not a result* — –

#### Section 1.1

- **§1.1 p.15**, p.15 [PC-002]: Interval notation: $[a,b]$, $(a,b)$, $[a,b)$, $(-\infty,b]$, $(a,\infty)$ describe order-convex sets of reals. — *in Mathlib* — `UndergradKB.Precalculus.Course.box_1_1_interval_notation`, `UndergradKB.Precalculus.Course.box_1_1_interval_notation_half_open`, `Set.Icc`, `Set.Ioo`
- **Definition 1.2 p.16**, p.16 [PC-003]: Intersection $A\cap B$ consists of $x$ in both; union $A\cup B$ of $x$ in at least one. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_1_2_mem_inter_union`, `Set.mem_inter_iff`, `Set.mem_union`
- **Definition 1.3 p.21**, p.21 [PC-004]: Points $(a,b)$ and $(c,d)$ are symmetric about x-axis, y-axis, origin iff $(c,d)=(a,-b),(-a,b),(-a,-b)$ respectively. — *proved proved here* — `UndergradKB.Precalculus.PtSymmX`, `UndergradKB.Precalculus.PtSymmY`, `UndergradKB.Precalculus.PtSymmO`, `UndergradKB.Precalculus.pt_symm_coordinates`
- **Equation 1.1 p.23**, p.23 [PC-005]: Distance formula: $d(P,Q)=\sqrt{(x_1-x_0)^2+(y_1-y_0)^2}$. — *proved proved here* — `UndergradKB.Precalculus.plane_dist_formula`
- **Example 1.1.7 p.25**, p.25 [PC-007]: The line $y=x$ bisects the segment joining $(a,b)$ and $(b,a)$ (midpoint $((a+b)/2,(a+b)/2)$). — *proved proved here* — `UndergradKB.Precalculus.plane_diagonal_bisects`
- **Equation 1.2 p.25**, p.25 [PC-006]: Midpoint formula: $M=((x_0+x_1)/2,(y_0+y_1)/2)$. — *proved proved here* — `UndergradKB.Precalculus.plane_midpoint_formula`, `UndergradKB.Precalculus.plane_midpoint_equidistant`
- **Definition 1.4 p.32**, p.32 [PC-008]: A relation is a set of points in the plane. — *not a result* — –

#### Section 1.2

- **§1.2 p.35**, p.35 [PC-009]: The graph of $x=a$ is a vertical line and of $y=b$ a horizontal line. — *proved proved here* — `UndergradKB.Precalculus.graph_vertical_horizontal_line`
- **§1.2 p.35**, p.35 [PC-010]: Fundamental Graphing Principle: a point is on the graph of an equation iff its coordinates satisfy it. — *not a result* — –
- **§1.2 p.37**, p.37 [PC-011]: Intercepts: x-intercepts are graph points on the x-axis (set $y=0$), y-intercepts on the y-axis (set $x=0$). — *not a result* — –
- **Definition 1.5 p.37**, p.37 [PC-011]: Intercepts: x-intercepts are graph points on the x-axis (set $y=0$), y-intercepts on the y-axis (set $x=0$). — *not a result* — –
- **§1.2 p.38**, p.38 [PC-012]: Symmetry test: substituting $(-x,y)$, $(x,-y)$, $(-x,-y)$ and obtaining an equivalent equation shows symmetry about y-axis, x-axis, origin. — *proved proved here* — `UndergradKB.Precalculus.SymmetricX`, `UndergradKB.Precalculus.SymmetricY`, `UndergradKB.Precalculus.SymmetricO`, `UndergradKB.Precalculus.symmetry_test`
- **Theorem 1.1 p.55**, p.55 [PC-014]: Vertical Line Test: a set of points is a function graph iff no vertical line meets it twice. — *proved proved here* — `UndergradKB.Precalculus.vertical_line_test`
- **Definition 1.6 p.55**, p.55 [PC-013]: A relation defines $y$ as a function of $x$ when each $x$-coordinate has exactly one $y$-coordinate. — *not a result* — –
- **Definition 1.7 p.57**, p.57 [PC-015]: Domain of a function is the set of $x$-coordinates, range the set of $y$-coordinates of its graph. — *proved proved here* — `UndergradKB.Precalculus.relDomain`, `UndergradKB.Precalculus.relRange`, `UndergradKB.Precalculus.relDomain_relRange_graphOn`

#### Section 1.4

- **§1.4 p.74**, p.74 [PC-016]: Piecewise-defined function: different formulas on different parts of the domain. — *not a result* — –
- **§1.4 p.79**, p.79 [PC-017]: Greatest integer function $\lfloor x\rfloor$ is the largest integer $k\le x$. — *in Mathlib* — `UndergradKB.Precalculus.Course.box_1_4_greatest_integer`, `Int.floor_le`, `Int.le_floor`, `Int.lt_floor_add_one`

#### Section 1.5

- **§1.5 p.88**, p.88 [PC-018]: Function arithmetic: $(f\pm g)(x)=f(x)\pm g(x)$, $(fg)(x)=f(x)g(x)$, $(f/g)(x)=f(x)/g(x)$, on the common domain with $g(x)\ne0$. — *proved proved here* — `UndergradKB.Precalculus.function_arith_graph`
- **Definition 1.8 p.91**, p.91 [PC-019]: Difference quotient of $f$ is $(f(x+h)-f(x))/h$. — *proved proved here* — `UndergradKB.Precalculus.diffQuot`, `UndergradKB.Precalculus.diffQuot_eq_slope`
- **§1.5 p.94**, p.94 [PC-020]: Cost, revenue ($R=xp$), average cost, profit ($P=R-C$) functions; $C(0)$ is the fixed cost. — *not a result* — –

#### Section 1.6

- **§1.6 p.105**, p.105 [PC-021]: Graph of $y=f(x)$ is the set of points $(x,f(x))$. — *in Mathlib* — `UndergradKB.Precalculus.Course.box_1_6_graph_of_function`, `Set.graphOn`
- **§1.6 p.107**, p.107 [PC-023]: Graph symmetric about y-axis iff $f(-x)=f(x)$; about origin iff $f(-x)=-f(x)$; these define even and odd functions. — *in Mathlib* — `UndergradKB.Precalculus.Course.box_1_6_even_odd`, `Function.Even`, `Function.Odd`, `Function.Even.eq`
- **§1.6 p.107**, p.107 [PC-024]: Only the zero function is both even and odd. — *in Mathlib* — `UndergradKB.Precalculus.Course.box_1_6_even_and_odd_zero`, `Function.zero_of_even_and_odd`
- **Definition 1.9 p.107**, p.107 [PC-022]: Zeros of $f$ are solutions to $f(x)=0$, i.e. x-intercepts of the graph. — *not a result* — –
- **Definition 1.10 p.113**, p.113 [PC-025]: A function on an interval $I$ is increasing/decreasing if $f(a)<f(b)$ resp. $f(a)>f(b)$ for $a<b$ in $I$, and constant if $f(a)=f(b)$. — *proved proved here* — `UndergradKB.Precalculus.ConstantOn`, `UndergradKB.Precalculus.increasing_decreasing_constant_on`
- **Definition 1.11 p.114**, p.114 [PC-026]: Local max/min at $a$: $f(a)\ge f(x)$ (resp. $\le$) on an open interval around $a$; absolute max/min: over the whole domain. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_1_11_local_extrema`, `UndergradKB.Precalculus.Course.def_1_11_absolute_extrema`, `IsLocalMax`, `IsLocalMin`
- **Theorem 1.2 p.133**, p.133 [PC-027]: Vertical shifts: $y=f(x)\pm k$ shifts the graph up/down $k$ units. — *proved proved here* — `UndergradKB.Precalculus.graph_vertical_shift`
- **Theorem 1.3 p.135**, p.135 [PC-028]: Horizontal shifts: $y=f(x+h)$ shifts left $h$, $y=f(x-h)$ right $h$. — *proved proved here* — `UndergradKB.Precalculus.graph_horizontal_shift`
- **Theorem 1.4 p.138**, p.138 [PC-029]: Reflections: $y=-f(x)$ reflects across the x-axis, $y=f(-x)$ across the y-axis. — *proved proved here* — `UndergradKB.Precalculus.graph_reflections`

#### Section 1.7

- **§1.7 p.141**, p.141 [PC-033]: Nonrigid transformations change shape (scalings), unlike shifts and reflections. — *not a result* — –
- **Theorem 1.5 p.142**, p.142 [PC-030]: Vertical scaling: $y=af(x)$ ($a>0$) multiplies $y$-coordinates by $a$. — *proved proved here* — `UndergradKB.Precalculus.graph_vertical_scale`
- **Theorem 1.6 p.144**, p.144 [PC-031]: Horizontal scaling: $y=f(bx)$ ($b>0$) divides $x$-coordinates by $b$. — *proved proved here* — `UndergradKB.Precalculus.graph_horizontal_scale`
- **Theorem 1.7 p.147**, p.147 [PC-032]: General transformation $g(x)=Af(Bx+H)+K$ in the order shift, horizontal scale, vertical scale, shift. — *proved proved here* — `UndergradKB.Precalculus.graph_general_transformation`, `UndergradKB.Precalculus.transformation_steps_comp`

## Chapter 2

16 items; 16 with a Lean name; 9 proved proved here; 7 in Mathlib.

- **Equation 2.1 p.163**, p.163 [PC-034]: Slope of the line through two points with distinct x-coordinates is the quotient of the y-difference by the x-difference — *proved proved here* — `UndergradKB.Precalculus.mem_line_iff_slope`
- **Equation 2.2 p.167**, p.167 [PC-035]: Point-slope form $y-y_0=m(x-x_0)$ of the line through a point with given slope — *proved proved here* — `UndergradKB.Precalculus.mem_line_point_slope`
- **Equation 2.3 p.167**, p.167 [PC-036]: Slope-intercept form $y=mx+b$; its y-intercept is $(0,b)$ — *proved proved here* — `UndergradKB.Precalculus.point_slope_iff_slope_intercept`, `UndergradKB.Precalculus.mem_line_slope_intercept`
- **Definition 2.1 p.168**, p.168 [PC-037]: Linear function $f(x)=mx+b$ with $m\ne 0$, domain all reals — *proved proved here* — `UndergradKB.Precalculus.graph_linear_function`, `UndergradKB.Precalculus.line_eq_graph_linear_function`
- **Definition 2.2 p.168**, p.168 [PC-038]: Constant function $f(x)=b$ with domain all reals — *in Mathlib* — `UndergradKB.Precalculus.Course.def_2_2_constant_function`
- **Definition 2.3 p.172**, p.172 [PC-039]: Average rate of change of $f$ over $[a,b]$ is $(f(b)-f(a))/(b-a)$, the slope of the secant line — *in Mathlib* — `UndergradKB.Precalculus.Course.def_2_3_average_rate_of_change`, `slope`, `slope_def_field`
- **Theorem 2.1 p.185**, p.185 [PC-041]: Product, power, quotient rules and equality properties of absolute value ($\|x\|=0$ iff $x=0$, $\|x\|=c$ iff $x=\pm c$) — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_2_1_abs_mul_pow_div`, `UndergradKB.Precalculus.Course.thm_2_1_abs_equality`, `abs_mul`, `abs_pow`
- **Definition 2.4 p.185**, p.185 [PC-040]: Absolute value: $\|x\|=-x$ for $x<0$ and $\|x\|=x$ for $x\ge0$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_2_4_abs_piecewise`, `abs_of_nonneg`, `abs_of_neg`
- **Definition 2.5 p.200**, p.200 [PC-043]: Quadratic function $f(x)=ax^2+bx+c$ with $a\ne0$, domain all reals — *proved proved here* — `UndergradKB.Precalculus.quadratic_standard_form`
- **Theorem 2.2 p.202**, p.202 [PC-045]: Vertex of $y=a(x-h)^2+k$ is $(h,k)$ — *proved proved here* — `UndergradKB.Precalculus.vertex_standard_form`
- **Definition 2.6 p.202**, p.202 [PC-044]: General form $ax^2+bx+c$ and standard form $a(x-h)^2+k$ of a quadratic function — *proved proved here* — `UndergradKB.Precalculus.quadratic_standard_form`, `UndergradKB.Precalculus.quadratic_standard_form_unique`
- **Equation 2.4 p.206**, p.206 [PC-046]: Vertex of $y=ax^2+bx+c$ is $(-b/2a, f(-b/2a))$; completed-square form $a(x+b/2a)^2+(4ac-b^2)/4a$ — *proved proved here* — `UndergradKB.Precalculus.vertex_general_form`, `UndergradKB.Precalculus.quadratic_standard_form`
- **Equation 2.5 p.206**, p.206 [PC-047]: Quadratic formula: roots of $ax^2+bx+c=0$ are $(-b\pm\sqrt{b^2-4ac})/2a$ — *in Mathlib* — `UndergradKB.Precalculus.Course.eq_2_5_quadratic_formula`, `quadratic_eq_zero_iff`, `quadratic_eq_zero_iff_discrim_eq_sq`
- **Theorem 2.3 p.207**, p.207 [PC-049]: Discriminant trichotomy: no real root if negative, one if zero, two if positive — *proved proved here* — `UndergradKB.Precalculus.discriminant_trichotomy`
- **Definition 2.7 p.207**, p.207 [PC-048]: Discriminant of $ax^2+bx+c$ is $b^2-4ac$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_2_7_discriminant`, `discrim`
- **Theorem 2.4 p.223**, p.223 [PC-042]: Inequalities $\|x\|<c$, $\|x\|\le c$, $\|x\|>c$, $\|x\|\ge c$ rewritten as double or split inequalities — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_2_4_abs_inequalities`

## Chapter 3

22 items; 22 with a Lean name; 9 proved proved here; 13 in Mathlib.

- **Definition 3.1 p.247**, p.247 [PC-050]: Polynomial function $a_nx^n+\dots+a_0$ with real coefficients — *in Mathlib* — `UndergradKB.Precalculus.Course.def_3_1_polynomial_function`, `Polynomial`, `Polynomial.eval`
- **Definition 3.2 p.248**, p.248 [PC-051]: Degree, leading term, leading coefficient, constant term of a polynomial; nonzero constants have degree 0, zero has none — *in Mathlib* — `UndergradKB.Precalculus.Course.def_3_2_leading_coeff`, `UndergradKB.Precalculus.Course.def_3_2_constant_term`, `UndergradKB.Precalculus.Course.def_3_2_degree_constants`, `Polynomial.degree`
- **Theorem 3.1 p.253**, p.253 [PC-052]: Intermediate Value Theorem (zero version) for a continuous function with sign change — *proved proved here* — `UndergradKB.Precalculus.poly_zero_of_sign_change`
- **Theorem 3.2 p.255**, p.255 [PC-053]: End behavior of a polynomial matches that of its leading term $a_nx^n$ — *proved proved here* — `UndergradKB.Precalculus.poly_end_behavior_atTop`, `UndergradKB.Precalculus.poly_end_behavior_atBot`, `UndergradKB.Precalculus.poly_tendsto_atBot_cases`
- **Definition 3.3 p.256**, p.256 [PC-054]: Zero of multiplicity $m$: $(x-c)^m$ divides $f$ but $(x-c)^{m+1}$ does not — *in Mathlib* — `UndergradKB.Precalculus.Course.def_3_3_zero_multiplicity`, `Polynomial.rootMultiplicity`, `Polynomial.le_rootMultiplicity_iff`
- **Theorem 3.3 p.257**, p.257 [PC-055]: Role of multiplicity: graph touches the axis at even multiplicity and crosses at odd — *proved proved here* — `UndergradKB.Precalculus.poly_no_sign_change_even_multiplicity`, `UndergradKB.Precalculus.poly_sign_change_odd_multiplicity`, `UndergradKB.Precalculus.poly_factor_root_multiplicity`
- **Theorem 3.4 p.270**, p.270 [PC-056]: Polynomial division: unique quotient and remainder with remainder zero or of smaller degree than divisor — *proved proved here* — `UndergradKB.Precalculus.poly_division_algorithm_unique`
- **Theorem 3.5 p.270**, p.270 [PC-057]: Remainder Theorem: remainder of $p$ on division by $x-c$ is $p(c)$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_5_remainder_theorem`, `Polynomial.modByMonic_X_sub_C_eq_C_eval`
- **Theorem 3.6 p.270**, p.270 [PC-058]: Factor Theorem: $c$ is a zero of $p$ iff $x-c$ divides $p$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_6_factor_theorem`, `Polynomial.dvd_iff_isRoot`, `Polynomial.mul_divByMonic_eq_iff_isRoot`
- **Theorem 3.7 p.276**, p.276 [PC-059]: A polynomial of degree $n\ge1$ has at most $n$ real zeros counting multiplicity — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_7_at_most_n_zeros`, `Polynomial.card_roots'`
- **Theorem 3.8 p.281**, p.281 [PC-060]: Cauchy's bound: all real zeros lie in $[-(M+1),M+1]$ where $M$ is the largest $\|a_i\|/\|a_n\|$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_8_cauchy_bound`, `Polynomial.cauchyBound`, `Polynomial.IsRoot.norm_lt_cauchyBound`
- **Theorem 3.9 p.281**, p.281 [PC-061]: Rational Zeros Theorem: a rational zero $p/q$ of an integer polynomial has $p$ dividing the constant term and $q$ the leading coefficient — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_9_rational_zeros`, `num_dvd_of_is_root`, `den_dvd_of_is_root`
- **Theorem 3.10 p.285**, p.285 [PC-062]: Descartes' Rule of Signs: positive (and via $f(-x)$ negative) zero counts are the sign variations number minus an even number — *proved proved here* — `UndergradKB.Precalculus.descartes_rule_of_signs`, `UndergradKB.Precalculus.descartes_rule_of_signs_neg`, `UndergradKB.Precalculus.signVariations_mod_two`, `UndergradKB.Precalculus.descartes_rule_of_signs_bounds`
- **Theorem 3.11 p.286**, p.286 [PC-063]: Upper and lower bounds on real zeros from sign pattern in the synthetic division tableau — *proved proved here* — `UndergradKB.Precalculus.poly_upper_bound_synthetic_division`, `UndergradKB.Precalculus.poly_lower_bound_synthetic_division`
- **Definition 3.4 p.299**, p.299 [PC-064]: Imaginary unit with $i^2=-1$ and $\sqrt{-c}=i\sqrt c$ for $c\ge0$ — *proved proved here* — `UndergradKB.Precalculus.imaginary_unit_sq_and_sqrt_neg`
- **Definition 3.5 p.299**, p.299 [PC-065]: Complex number $a+bi$ with real $a,b$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_3_5_complex_number`, `Complex`

#### Section 3.4

- **§3.4 p.300**, p.300 [PC-066]: Complex conjugate of $a+bi$ is $a-bi$ — *in Mathlib* — `UndergradKB.Precalculus.Course.box_3_4_complex_conjugate`, `RCLike.conj_re`, `RCLike.conj_im`
- **Theorem 3.12 p.301**, p.301 [PC-067]: Properties of conjugation: involutive, additive, multiplicative, commutes with powers, fixed exactly by reals — *proved proved here* — `UndergradKB.Precalculus.complex_conj_properties`
- **Theorem 3.13 p.302**, p.302 [PC-068]: Fundamental Theorem of Algebra: a complex polynomial of degree at least 1 has a complex zero — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_13_fundamental_theorem_of_algebra`, `Complex.exists_root`, `Complex.isAlgClosed`
- **Theorem 3.14 p.302**, p.302 [PC-069]: Complex Factorization Theorem: degree $n$ polynomial has $n$ complex zeros with multiplicity and factors as $a\prod(x-z_i)^{m_i}$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_14_complex_factorization`, `Polynomial.Splits.eq_prod_roots`, `Polynomial.Splits.natDegree_eq_card_roots`
- **Theorem 3.15 p.303**, p.303 [PC-070]: Conjugate Pairs Theorem: nonreal zeros of a real polynomial come in conjugate pairs — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_3_15_conjugate_pairs`, `Polynomial.aeval_conj`
- **Theorem 3.16 p.304**, p.304 [PC-071]: Real Factorization Theorem: real polynomial is a product of linear factors and irreducible quadratics — *proved proved here* — `UndergradKB.Precalculus.real_polynomial_factorization`

## Chapter 4

8 items; 8 with a Lean name; 7 proved proved here; 1 in Mathlib.

- **Definition 4.1 p.313**, p.313 [PC-072]: A rational function is a quotient $p(x)/q(x)$ of two polynomial functions; every polynomial is one (take $q=1$). — *proved proved here* — `UndergradKB.Precalculus.IsRationalFunction`, `UndergradKB.Precalculus.isRationalFunction_polynomial`, `UndergradKB.Precalculus.IsRationalFunction.mul`
- **Definition 4.2 p.316**, p.316 [PC-073]: The line $x=c$ is a vertical asymptote of $y=f(x)$ if $f(x)\to\pm\infty$ as $x\to c^-$ or $x\to c^+$. — *proved proved here* — `UndergradKB.Precalculus.IsVerticalAsymptote`, `UndergradKB.Precalculus.isVerticalAsymptote_inv`
- **Definition 4.3 p.316**, p.316 [PC-074]: The line $y=c$ is a horizontal asymptote of $y=f(x)$ if $f(x)\to c$ as $x\to-\infty$ or $x\to\infty$. — *proved proved here* — `UndergradKB.Precalculus.IsHorizontalAsymptote`, `UndergradKB.Precalculus.isHorizontalAsymptote_iff_sub`, `UndergradKB.Precalculus.isHorizontalAsymptote_inv`
- **Theorem 4.1 p.318**, p.318 [PC-075]: For $r=p/q$ in lowest terms and $c$ outside the domain: if $q(c)\ne0$ the graph has a hole at $(c,p(c)/q(c))$ (impossible in lowest terms), if $q(c)=0$ then $x=c$ is a vertical asymptote. — *proved proved here* — `UndergradKB.Precalculus.hole_or_vertical_asymptote`, `UndergradKB.Precalculus.eventually_eval_ne_zero`, `UndergradKB.Precalculus.tendsto_div_of_eval_eq_zero_right`
- **Theorem 4.2 p.320**, p.320 [PC-076]: For $r=p/q$ with leading coefficients $a,b$: equal degrees give $y=a/b$, $\deg p<\deg q$ gives $y=0$, $\deg p>\deg q$ gives no horizontal asymptote. — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_4_2_horizontal_asymptote_equal_degree`, `UndergradKB.Precalculus.Course.thm_4_2_horizontal_asymptote_numerator_smaller`, `UndergradKB.Precalculus.Course.thm_4_2_no_horizontal_asymptote_numerator_larger`, `UndergradKB.Precalculus.horizontal_asymptote_rational`
- **Definition 4.4 p.323**, p.323 [PC-077]: The line $y=mx+b$ with $m\ne0$ is a slant asymptote of $f$ if $f(x)\to mx+b$ as $x\to\pm\infty$ (equivalently $f(x)-(mx+b)\to0$). — *proved proved here* — `UndergradKB.Precalculus.IsSlantAsymptote`, `UndergradKB.Precalculus.isSlantAsymptote_iff`
- **Theorem 4.3 p.324**, p.324 [PC-078]: If $\deg p=\deg q+1$, the graph of $p/q$ has the slant asymptote $y=L(x)$, where $L$ is the quotient of $p$ by $q$. — *proved proved here* — `UndergradKB.Precalculus.slant_asymptote_rational`, `UndergradKB.Precalculus.isSlantAsymptote_rational`
- **Definition 4.5 p.362**, p.362 [PC-079]: Direct, inverse and joint variation: $y=kx$, $y=k/x$, $z=kxy$ with constant of proportionality $k$. — *proved proved here* — `UndergradKB.Precalculus.VariesDirectly`, `UndergradKB.Precalculus.VariesInversely`, `UndergradKB.Precalculus.VariesJointly`, `UndergradKB.Precalculus.constant_of_proportionality`

## Chapter 5

12 items; 12 with a Lean name; 8 proved proved here; 4 in Mathlib.

- **Definition 5.1 p.372**, p.372 [PC-080]: The composite $(g\circ f)(x)=g(f(x))$, defined where $x\in\mathrm{dom}f$ and $f(x)\in\mathrm{dom}g$. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_5_1_composition`, `Function.dcomp_eq_comp`
- **Theorem 5.1 p.379**, p.379 [PC-081]: Composition is associative, and the identity function is a two-sided unit for composition. — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_5_1_composition_assoc_id`, `Function.comp_assoc`
- **Definition 5.2 p.391**, p.391 [PC-082]: $f$ and $g$ are inverses if $g(f(x))=x$ on $\mathrm{dom}f$ and $f(g(x))=x$ on $\mathrm{dom}g$; then they are called invertible. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_5_2_inverse_functions`, `Function.bijective_iff_has_inverse`
- **Theorem 5.2 p.391**, p.391 [PC-083]: For inverses $f,g$: range of $f$ is the domain of $g$ and vice versa; $f(a)=b\iff g(b)=a$; $(a,b)\in$ graph $f\iff(b,a)\in$ graph $g$. — *proved proved here* — `UndergradKB.Precalculus.InverseOn`, `UndergradKB.Precalculus.inverse_properties`
- **Theorem 5.3 p.392**, p.392 [PC-084]: An invertible function has exactly one inverse, and the graph of $f^{-1}$ is the reflection of the graph of $f$ across $y=x$. — *proved proved here* — `UndergradKB.Precalculus.inverse_unique_and_graph_reflection`
- **Definition 5.3 p.393**, p.393 [PC-085]: $f$ is one-to-one if $f(c)=f(d)$ implies $c=d$ (distinct inputs give distinct outputs). — *in Mathlib* — `UndergradKB.Precalculus.Course.def_5_3_one_to_one`
- **Theorem 5.4 p.393**, p.393 [PC-086]: Horizontal Line Test: $f$ is one-to-one iff no horizontal line meets its graph more than once. — *proved proved here* — `UndergradKB.Precalculus.horizontal_line_test`
- **Theorem 5.5 p.394**, p.394 [PC-087]: For a function $f$: invertible $\iff$ one-to-one $\iff$ graph passes the Horizontal Line Test. — *proved proved here* — `UndergradKB.Precalculus.invertible_iff_injective`
- **Definition 5.4 p.409**, p.409 [PC-088]: Principal $n$-th root $\sqrt[n]{x}$: the unique real $r$ with $r^n=x$ (and $r\ge0$ if $n$ even, $x\ge0$ then). — *proved proved here* — `UndergradKB.Precalculus.principalRoot`, `UndergradKB.Precalculus.principalRoot_eq_iff_odd`, `UndergradKB.Precalculus.principalRoot_eq_iff_nonneg`
- **Definition 5.5 p.410**, p.410 [PC-091]: Rational exponents: $x^{1/n}=\sqrt[n]x$ and $x^{m/n}=(\sqrt[n]x)^m=\sqrt[n]{x^m}$ where defined. — *proved proved here* — `UndergradKB.Precalculus.rpow_one_div_eq_principalRoot`, `UndergradKB.Precalculus.rpow_intCast_div_eq_principalRoot_zpow`, `UndergradKB.Precalculus.rpow_natCast_div_eq_principalRoot_pow`
- **Theorem 5.6 p.410**, p.410 [PC-089]: For $\sqrt[n]{x},\sqrt[n]{y}$ real: $\sqrt[n]{xy}=\sqrt[n]x\sqrt[n]y$, $\sqrt[n]{x/y}=\sqrt[n]x/\sqrt[n]y$, and $\sqrt[n]{x^m}=(\sqrt[n]x)^m$. — *proved proved here* — `UndergradKB.Precalculus.principalRoot_mul`, `UndergradKB.Precalculus.principalRoot_div`, `UndergradKB.Precalculus.principalRoot_pow_nat`
- **Theorem 5.6 p.410**, p.410 [PC-090]: $\sqrt[n]{x^n}=x$ for odd $n$ and $\|x\|$ for even $n$. — *proved proved here* — `UndergradKB.Precalculus.principalRoot_pow_self_odd`, `UndergradKB.Precalculus.principalRoot_pow_self_even`

## Chapter 6

19 items; 19 with a Lean name; 13 proved proved here; 6 in Mathlib.

- **Definition 6.1 p.430**, p.430 [PC-092]: Base $b$ exponential function $f(x)=b^x$, $b>0$, $b\ne1$. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_6_1_exponential_function`, `Real.rpow`, `Real.rpow_def_of_pos`
- **Theorem 6.1 p.431**, p.431 [PC-093]: Properties of $b^x$: domain $\mathbb R$, range $(0,\infty)$, $(0,1)$ on graph, $y=0$ asymptote, one-to-one, continuous, increasing if $b>1$, decreasing if $0<b<1$, with the limits at $\pm\infty$. — *proved proved here* — `UndergradKB.Precalculus.exp_fun_basic`, `UndergradKB.Precalculus.exp_fun_base_gt_one`, `UndergradKB.Precalculus.exp_fun_base_lt_one`
- **Definition 6.2 p.434**, p.434 [PC-094]: The base-$b$ logarithm $\log_b$ is the inverse of $b^x$. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_6_2_logarithm_inverse`, `Real.logb`, `Real.logb_rpow`, `Real.rpow_logb`
- **Definition 6.3 p.434**, p.434 [PC-095]: Common logarithm $\log=\log_{10}$ and natural logarithm $\ln=\log_e$. — *in Mathlib* — `UndergradKB.Precalculus.Course.def_6_3_common_and_natural_log`, `Real.log`, `Real.logb`
- **Theorem 6.2 p.435**, p.435 [PC-096]: Properties of $\log_b$: domain $(0,\infty)$, range $\mathbb R$, $(1,0)$ on graph, $x=0$ vertical asymptote, one-to-one, increasing/decreasing by base, $b^a=c\iff\log_bc=a$, $\log_b(b^x)=x$, $b^{\log_bx}=x$. — *proved proved here* — `UndergradKB.Precalculus.log_fun_basic`, `UndergradKB.Precalculus.log_fun_base_gt_one`, `UndergradKB.Precalculus.log_fun_base_lt_one`
- **Theorem 6.3 p.449**, p.449 [PC-097]: Inverse properties: $b^a=c\iff\log_bc=a$; $\log_b(b^x)=x$ for all $x$; $b^{\log_bx}=x$ for $x>0$. — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_6_3_log_exp_inverse_properties`, `Real.logb_eq_iff_rpow_eq`, `Real.logb_rpow`, `Real.rpow_logb`
- **Theorem 6.4 p.449**, p.449 [PC-098]: One-to-one properties: $b^u=b^w\iff u=w$ and $\log_bu=\log_bw\iff u=w$ for $u,w>0$. — *proved proved here* — `UndergradKB.Precalculus.rpow_eq_rpow_iff_exponent`, `UndergradKB.Precalculus.logb_eq_logb_iff`
- **Theorem 6.5 p.449**, p.449 [PC-099]: Exponent laws for real exponents: $b^{u+w}=b^ub^w$, $b^{u-w}=b^u/b^w$, $(b^u)^w=b^{uw}$. — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_6_5_exponent_laws`, `Real.rpow_add`, `Real.rpow_sub`, `Real.rpow_mul`
- **Theorem 6.6 p.450**, p.450 [PC-100]: Log laws: $\log_b(uw)=\log_bu+\log_bw$, $\log_b(u/w)=\log_bu-\log_bw$, $\log_b(u^w)=w\log_bu$ for $u,w>0$. — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_6_6_log_laws`, `Real.logb_mul`, `Real.logb_div`, `Real.logb_rpow_eq_mul_logb_of_pos`
- **Theorem 6.7 p.454**, p.454 [PC-101]: Change of base: $a^x=b^{x\log_ba}$ and $\log_ax=\log_bx/\log_ba$. — *proved proved here* — `UndergradKB.Precalculus.rpow_change_of_base`, `UndergradKB.Precalculus.logb_change_of_base`
- **Equation 6.1 p.481**, p.481 [PC-102]: Simple interest: $I=Prt$, so the balance is $A=P(1+rt)$. — *proved proved here* — `UndergradKB.Precalculus.simpleBalance`, `UndergradKB.Precalculus.growth_simple_interest`
- **Equation 6.2 p.482**, p.482 [PC-103]: Compound interest: $A(t)=P(1+r/n)^{nt}$. — *proved proved here* — `UndergradKB.Precalculus.compoundBalance`, `UndergradKB.Precalculus.growth_compound_interest`
- **Theorem 6.8 p.483**, p.483 [PC-104]: $\$1$ at 100% interest compounded continuously gives $\$e$ after a year, i.e. $(1+1/n)^n\to e$. — *proved proved here* — `UndergradKB.Precalculus.growth_one_plus_inv_pow_tendsto_e`
- **Equation 6.3 p.484**, p.484 [PC-105]: Continuously compounded interest: $A(t)=Pe^{rt}$. — *proved proved here* — `UndergradKB.Precalculus.growth_continuous_compounding`
- **Equation 6.4 p.484**, p.484 [PC-106]: Uninhibited growth: $N(t)=N_0e^{kt}$ with $k>0$, rate of change equal to $kN$. — *proved proved here* — `UndergradKB.Precalculus.expModel`, `UndergradKB.Precalculus.growth_exp_model_deriv`
- **Equation 6.5 p.485**, p.485 [PC-107]: Radioactive decay: $A(t)=A_0e^{kt}$ with $k<0$. — *proved proved here* — `UndergradKB.Precalculus.growth_decay_model`
- **Equation 6.6 p.486**, p.486 [PC-108]: Newton's law of cooling: $T(t)=T_a+(T_0-T_a)e^{-kt}$, $k>0$. — *proved proved here* — `UndergradKB.Precalculus.coolingModel`, `UndergradKB.Precalculus.growth_newton_cooling`
- **Equation 6.7 p.487**, p.487 [PC-109]: Logistic growth: $N(t)=L/(1+Ce^{-kLt})$ with $C=L/N_0-1$. — *proved proved here* — `UndergradKB.Precalculus.logisticPop`, `UndergradKB.Precalculus.growth_logistic`

#### Section 6.5

- **§6.5 p.489**, p.489 [PC-110]: An inflection point (point of diminishing returns) is where a growth curve switches concavity (logistic curve). — *proved proved here* — `UndergradKB.Precalculus.logisticRate`, `UndergradKB.Precalculus.logisticSecond`, `UndergradKB.Precalculus.growth_logistic_inflection`

## Chapter 7

20 items; 20 with a Lean name; 20 proved proved here.

- **Definition 7.1 p.510**, p.510 [PC-111]: A circle with center $(h,k)$ and radius $r>0$ is the set of points at distance $r$ from the center; equivalently $(x-h)^2+(y-k)^2=r^2$ — *proved proved here* — `UndergradKB.Precalculus.edist2`, `UndergradKB.Precalculus.circle_mem_iff_equation`
- **Equation 7.1 p.510**, p.510 [PC-111]: A circle with center $(h,k)$ and radius $r>0$ is the set of points at distance $r$ from the center; equivalently $(x-h)^2+(y-k)^2=r^2$ — *proved proved here* — `UndergradKB.Precalculus.edist2`, `UndergradKB.Precalculus.circle_mem_iff_equation`

#### Section 7.2

- **Example 7.2.4 p.512**, p.512 [PC-113]: A circle with given diameter endpoints has the midpoint as center and half the distance between them as radius — *proved proved here* — `UndergradKB.Precalculus.circle_diameter_endpoints`
- **Definition 7.2 p.513**, p.513 [PC-114]: The unit circle is the circle of radius 1 at the origin, equation $x^2+y^2=1$ — *proved proved here* — `UndergradKB.Precalculus.unit_circle_mem_iff`, `UndergradKB.Precalculus.unit_circle_cos_sin`
- **Definition 7.3 p.517**, p.517 [PC-115]: A parabola is the set of points equidistant from a focus $F$ and a directrix line $D$ not containing $F$ — *proved proved here* — `UndergradKB.Precalculus.distToLine`, `UndergradKB.Precalculus.IsParabolaPt`, `UndergradKB.Precalculus.parabola_pt_iff`

#### Section 7.3

- **§7.3 p.517**, p.517 [PC-116]: Vertical parabola with vertex $(h,k)$ and directed focal distance $p$: $(x-h)^2=4p(y-k)$, opening up if $p>0$ and down if $p<0$ (derived from $x^2=4py$) — *proved proved here* — `UndergradKB.Precalculus.parabola_vertical_equation`
- **Equation 7.2 p.518**, p.518 [PC-116]: Vertical parabola with vertex $(h,k)$ and directed focal distance $p$: $(x-h)^2=4p(y-k)$, opening up if $p>0$ and down if $p<0$ (derived from $x^2=4py$) — *proved proved here* — `UndergradKB.Precalculus.parabola_vertical_equation`
- **§7.3 p.519**, p.519 [PC-118]: The latus rectum (chord through focus parallel to directrix) of a parabola has length $\lvert 4p\rvert$ (the focal diameter) — *proved proved here* — `UndergradKB.Precalculus.parabola_latus_rectum`
- **Equation 7.3 p.520**, p.520 [PC-117]: Horizontal parabola: $(y-k)^2=4p(x-h)$, opening right if $p>0$ and left if $p<0$ — *proved proved here* — `UndergradKB.Precalculus.parabola_horizontal_equation`
- **§7.3 p.523**, p.523 [PC-119]: Reflective property: rays parallel to the axis reflect through the focus of a parabola — *proved proved here* — `UndergradKB.Precalculus.parabola_reflective_property`, `UndergradKB.Precalculus.reflectDir`, `UndergradKB.Precalculus.parabola_tangent_slope`
- **Definition 7.4 p.528**, p.528 [PC-120]: An ellipse is the set of points whose distances to two distinct foci sum to a constant $d$ (center, major/minor axis, vertices defined) — *proved proved here* — `UndergradKB.Precalculus.IsEllipsePt`, `UndergradKB.Precalculus.ellipse_symm_center`

#### Section 7.4

- **§7.4 p.530**, p.530 [PC-121]: For the ellipse with foci $(\pm c,0)$ and vertices $(\pm a,0)$: $d=2a$ and $b^2=a^2-c^2$ — *proved proved here* — `UndergradKB.Precalculus.ellipse_vertex_sum`
- **Equation 7.4 p.531**, p.531 [PC-122]: Standard ellipse equation $\frac{(x-h)^2}{a^2}+\frac{(y-k)^2}{b^2}=1$, with focal distance $c=\sqrt{\lvert a^2-b^2\rvert}$ — *proved proved here* — `UndergradKB.Precalculus.ellipse_horizontal_equation`, `UndergradKB.Precalculus.ellipse_vertical_equation`, `UndergradKB.Precalculus.ellipse_focal_distance`
- **Equation 7.5 p.531**, p.531 [PC-112]: Alternate circle equation $\frac{(x-h)^2}{r^2}+\frac{(y-k)^2}{r^2}=1$ — *proved proved here* — `UndergradKB.Precalculus.circle_alt_equation`
- **Definition 7.5 p.534**, p.534 [PC-123]: Eccentricity of an ellipse is $e=$ (center-to-focus)/(center-to-vertex), and $0<e<1$ — *proved proved here* — `UndergradKB.Precalculus.ellipseEccentricity`, `UndergradKB.Precalculus.ellipse_eccentricity_bounds`
- **Definition 7.6 p.543**, p.543 [PC-124]: A hyperbola is the set of points where the absolute difference of distances to two distinct foci is a constant $d$ (center, transverse axis, vertices, branches) — *proved proved here* — `UndergradKB.Precalculus.IsHyperbolaPt`, `UndergradKB.Precalculus.hyperbola_symm_center`

#### Section 7.5

- **§7.5 p.545**, p.545 [PC-125]: For foci $(\pm c,0)$ and vertices $(\pm a,0)$: $d=2a$ and $c^2=a^2+b^2$ — *proved proved here* — `UndergradKB.Precalculus.hyperbola_vertex_difference`
- **§7.5 p.546**, p.546 [PC-127]: The asymptotes of the horizontal hyperbola centered at $(h,k)$ are $y-k=\pm\frac{b}{a}(x-h)$ — *proved proved here* — `UndergradKB.Precalculus.hyperbola_asymptotes`
- **Equation 7.6 p.546**, p.546 [PC-126]: Standard hyperbola equations: horizontal $\frac{(x-h)^2}{a^2}-\frac{(y-k)^2}{b^2}=1$, vertical $\frac{(y-k)^2}{b^2}-\frac{(x-h)^2}{a^2}=1$ — *proved proved here* — `UndergradKB.Precalculus.hyperbola_horizontal_equation`, `UndergradKB.Precalculus.hyperbola_vertical_equation`
- **Equation 7.7 p.546**, p.546 [PC-126]: Standard hyperbola equations: horizontal $\frac{(x-h)^2}{a^2}-\frac{(y-k)^2}{b^2}=1$, vertical $\frac{(y-k)^2}{b^2}-\frac{(x-h)^2}{a^2}=1$ — *proved proved here* — `UndergradKB.Precalculus.hyperbola_horizontal_equation`, `UndergradKB.Precalculus.hyperbola_vertical_equation`

## Chapter 8

39 items; 39 with a Lean name; 17 proved proved here; 22 in Mathlib.

- **Definition 8.1 p.561**, p.561 [PC-128]: A linear equation in two variables is $a_1x+a_2y=c$ with $a_1,a_2$ not both zero — *proved proved here* — `UndergradKB.Precalculus.lin2Solutions`, `UndergradKB.Precalculus.lin2_solutions_line`

#### Section 8.1

- **§8.1 p.565**, p.565 [PC-129]: Terminology: a system is consistent or inconsistent; a consistent system is dependent (free variables) or independent; consistent independent systems have exactly one solution — *proved proved here* — `UndergradKB.Precalculus.solutionSet`, `UndergradKB.Precalculus.IsConsistent`, `UndergradKB.Precalculus.IsInconsistent`, `UndergradKB.Precalculus.IsIndependent`
- **Definition 8.2 p.566**, p.566 [PC-130]: A linear equation in $n$ variables is $a_1x_1+\dots+a_nx_n=c$ with some $a_i\neq0$ — *proved proved here* — `UndergradKB.Precalculus.linEqSolutions`, `UndergradKB.Precalculus.lin_eq_solutions_solve`, `UndergradKB.Precalculus.lin2_mem_iff_linEq`
- **Theorem 8.1 p.567**, p.567 [PC-131]: Swapping equations, scaling an equation by a nonzero number, and adding a multiple of one equation to another give equivalent systems — *proved proved here* — `UndergradKB.Precalculus.system_moves_equivalent`, `UndergradKB.Precalculus.solutionSet_swap`, `UndergradKB.Precalculus.solutionSet_scale`, `UndergradKB.Precalculus.solutionSet_add_multiple`
- **Definition 8.3 p.568**, p.568 [PC-132]: Definition of a system in triangular form (increasing variable indices, leading coefficients 1, strictly increasing leading variables, constant equations at the bottom) — *proved proved here* — `UndergradKB.Precalculus.IsTriangularSystem`, `UndergradKB.Precalculus.isTriangularSystem_iff`

#### Section 8.2

- **§8.2 p.579**, p.579 [PC-138]: A matrix is a rectangular array of reals with entries $a_{ij}$ (row $i$, column $j$) — *in Mathlib* — `UndergradKB.Precalculus.Course.box_8_2_matrix_entries`, `Matrix`
- **Theorem 8.2 p.580**, p.580 [PC-133]: Elementary row operations on an augmented matrix give an equivalent system — *proved proved here* — `UndergradKB.Precalculus.augmented_row_ops_equivalent`, `UndergradKB.Precalculus.solutionSet_unit_mul`
- **§8.2 p.580**, p.580 [PC-136]: Augmented matrix of a system (coefficient matrix with the constants column appended) — *proved proved here* — `UndergradKB.Precalculus.augmented`, `UndergradKB.Precalculus.coeffPart`, `UndergradKB.Precalculus.constPart`, `UndergradKB.Precalculus.augSolutions`
- **Definition 8.4 p.581**, p.581 [PC-134]: Row echelon form: leading entries are 1, strictly move right going down, zero rows at the bottom — *proved proved here* — `UndergradKB.Precalculus.IsRowEchelonForm`, `UndergradKB.Precalculus.isRowEchelonForm_iff`
- **Definition 8.5 p.582**, p.582 [PC-135]: Reduced row echelon form: row echelon form with leading 1s the only nonzero entries in their columns — *proved proved here* — `UndergradKB.Precalculus.rref_square_no_zero_row`, `UndergradKB.Precalculus.rref_isRowEchelonForm`
- **§8.2 p.583**, p.583 [PC-137]: Gauss-Jordan elimination: row-reduction to reduced row echelon form — *proved proved here* — `UndergradKB.Precalculus.gauss_jordan`, `UndergradKB.Precalculus.exists_unit_mul_isReducedRowEchelon`
- **Definition 8.6 p.590**, p.590 [PC-139]: Two matrices are equal iff they have the same size and equal corresponding entries — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_6_matrix_equality`, `Matrix.ext_iff`
- **Definition 8.7 p.590**, p.590 [PC-140]: Matrix sum is entrywise — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_7_matrix_sum`, `Matrix.add_apply`
- **Theorem 8.3 p.591**, p.591 [PC-141]: Addition properties: commutative, associative, zero matrix is identity, each $A$ has unique additive inverse $-A$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_3_add_comm`, `UndergradKB.Precalculus.Course.thm_8_3_add_assoc`, `UndergradKB.Precalculus.Course.thm_8_3_zero_add`, `UndergradKB.Precalculus.Course.thm_8_3_additive_inverse`
- **Definition 8.8 p.592**, p.592 [PC-142]: Scalar multiplication $kA=[ka_{ij}]$; subtraction $A-B=A+(-B)$ is entrywise — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_8_scalar_mul_sub`, `Matrix.smul_apply`, `Matrix.sub_apply`
- **Theorem 8.4 p.593**, p.593 [PC-143]: Scalar multiplication properties: $(kr)A=k(rA)$, $1A=A$, $-A=(-1)A$, both distributive laws, and $kA=0$ iff $k=0$ or $A=0$ — *proved proved here* — `UndergradKB.Precalculus.matrix_smul_laws`
- **Definition 8.9 p.596**, p.596 [PC-144]: Product of a row and a column $R_i\cdot C_j=\sum_k a_{ik}b_{kj}$; matrix product $AB=[R_i\cdot C_j]$ for $A$ $m\times n$, $B$ $n\times r$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_10_matrix_product`, `Matrix.mul_apply`
- **Definition 8.10 p.596**, p.596 [PC-144]: Product of a row and a column $R_i\cdot C_j=\sum_k a_{ik}b_{kj}$; matrix product $AB=[R_i\cdot C_j]$ for $A$ $m\times n$, $B$ $n\times r$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_10_matrix_product`, `Matrix.mul_apply`
- **Theorem 8.5 p.597**, p.597 [PC-145]: Properties of matrix multiplication: associativity, $k(AB)=(kA)B=A(kB)$, identity $I_mA=AI_n=A$, distributivity over addition; identity matrix (1 on main diagonal) and square matrix — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_5_mul_assoc`, `UndergradKB.Precalculus.Course.thm_8_5_smul_mul`, `UndergradKB.Precalculus.Course.thm_8_5_identity`, `UndergradKB.Precalculus.Course.thm_8_5_distributive`

#### Section 8.3

- **§8.3 p.605**, p.605 [PC-146]: Upper triangular (zeros below the diagonal) and lower triangular (zeros above) square matrices — *in Mathlib* — `UndergradKB.Precalculus.Course.box_8_3_upper_triangular`, `UndergradKB.Precalculus.Course.box_8_3_lower_triangular`, `Matrix.IsUpperTriangular`
- **Theorem 8.6 p.614**, p.614 [PC-148]: The inverse of an invertible matrix is unique — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_6_inverse_unique`, `Matrix.inv_eq_left_inv`, `Matrix.inv_eq_right_inv`
- **Theorem 8.6 p.614**, p.614 [PC-149]: $A$ is invertible iff $AX=B$ has a unique solution for every $B$ — *proved proved here* — `UndergradKB.Precalculus.invertible_iff_unique_solution`
- **Definition 8.11 p.614**, p.614 [PC-147]: An $n\times n$ matrix $A$ is invertible if some $A^{-1}$ satisfies $A^{-1}A=AA^{-1}=I_n$ — *proved proved here* — `UndergradKB.Precalculus.IsInvertibleMatrix`, `UndergradKB.Precalculus.isInvertibleMatrix_iff`
- **Definition 8.12 p.626**, p.626 [PC-150]: $A_{ij}$ is $A$ with row $i$ and column $j$ deleted — *proved proved here* — `UndergradKB.Precalculus.deleteRowCol`, `UndergradKB.Precalculus.deleteRowCol_apply`
- **Definition 8.13 p.626**, p.626 [PC-151]: Determinant defined recursively: $\det[a]=a$, and $\det A=\sum_j(-1)^{1+j}a_{1j}\det A_{1j}$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_13_det_first_row`, `UndergradKB.Precalculus.Course.def_8_13_det_one_by_one`, `Matrix.det_succ_row_zero`, `Matrix.det_eq_elem_of_card_eq_one`
- **Equation 8.1 p.627**, p.627 [PC-152]: $\det\begin{pmatrix}a&b\\c&d\end{pmatrix}=ad-bc$ — *in Mathlib* — `UndergradKB.Precalculus.Course.eq_8_1_det_two_by_two`, `Matrix.det_fin_two`
- **Theorem 8.7 p.628**, p.628 [PC-154]: Determinant can be expanded along any row — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_7_expand_along_row`, `Matrix.det_succ_row`, `Matrix.det_succ_column`
- **Theorem 8.7 p.628**, p.628 [PC-155]: Row operations: swapping two rows negates $\det$; scaling a row by $c$ multiplies $\det$ by $c$; adding a multiple of another row leaves $\det$ unchanged — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_7_swap_rows`, `UndergradKB.Precalculus.Course.thm_8_7_scale_row`, `UndergradKB.Precalculus.Course.thm_8_7_add_multiple_of_row`, `Matrix.det_permute'`
- **Theorem 8.7 p.628**, p.628 [PC-156]: A matrix with two identical rows or a zero row has $\det=0$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_7_equal_rows`, `UndergradKB.Precalculus.Course.thm_8_7_zero_row`, `Matrix.det_zero_of_row_eq`, `Matrix.det_eq_zero_of_row_eq_zero`
- **Theorem 8.7 p.628**, p.628 [PC-157]: The determinant of a triangular matrix is the product of its diagonal entries — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_7_det_upper_triangular`, `UndergradKB.Precalculus.Course.thm_8_7_det_lower_triangular`, `Matrix.det_of_isUpperTriangular`, `Matrix.det_of_isLowerTriangular`
- **Theorem 8.7 p.628**, p.628 [PC-158]: $\det(AB)=\det A\det B$ and $\det(A^n)=(\det A)^n$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_7_det_mul`, `UndergradKB.Precalculus.Course.thm_8_7_det_pow`, `Matrix.det_mul`, `Matrix.det_pow`
- **Theorem 8.7 p.628**, p.628 [PC-159]: $A$ is invertible iff $\det A\ne0$, and then $\det A^{-1}=1/\det A$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_7_invertible_iff_det_ne_zero`, `UndergradKB.Precalculus.Course.thm_8_7_det_inverse`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.det_nonsing_inv`
- **Definition 8.14 p.628**, p.628 [PC-153]: Minor $M_{ij}=\det A_{ij}$ and cofactor $C_{ij}=(-1)^{i+j}M_{ij}$ — *proved proved here* — `UndergradKB.Precalculus.minor'`, `UndergradKB.Precalculus.cofactor`, `UndergradKB.Precalculus.det_eq_sum_cofactor`
- **Theorem 8.8 p.631**, p.631 [PC-160]: Cramer's rule: if $\det A\ne0$ then $x_j=\det(A_j)/\det A$ where $A_j$ has column $j$ replaced by the constants — *proved proved here* — `UndergradKB.Precalculus.cramers_rule`
- **Equation 8.2 p.634**, p.634 [PC-163]: $\begin{pmatrix}a&b\\c&d\end{pmatrix}^{-1}=\frac{1}{ad-bc}\begin{pmatrix}d&-b\\-c&a\end{pmatrix}$ — *in Mathlib* — `UndergradKB.Precalculus.Course.eq_8_2_inverse_two_by_two`, `Matrix.adjugate_fin_two`, `Matrix.inv_def`
- **Theorem 8.9 p.634**, p.634 [PC-162]: $A^{-1}=\frac{1}{\det A}\operatorname{adj}(A)$ for invertible $A$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_9_inverse_via_adjoint`, `Matrix.inv_def`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`
- **Definition 8.15 p.634**, p.634 [PC-161]: Adjoint (adjugate) of $A$ is the transpose of the cofactor matrix — *in Mathlib* — `UndergradKB.Precalculus.Course.def_8_15_adjoint_entries`, `Matrix.adjugate`
- **Theorem 8.10 p.642**, p.642 [PC-164]: Partial fraction form: for proper reduced $N/D$, each linear factor $(ax+b)^m$ contributes $\sum_{i\le m}A_i/(ax+b)^i$ and each irreducible quadratic $(ax^2+bx+c)^m$ contributes $\sum_{i\le m}(B_ix+C_i)/(ax^2+bx+c)^i$ — *proved proved here* — `UndergradKB.Precalculus.partial_fractions_proper`, `UndergradKB.Precalculus.partial_fraction_numerator_shape`
- **Theorem 8.11 p.643**, p.643 [PC-165]: If two polynomials agree for all $x$ in an open interval then they have the same coefficients — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_8_11_polynomial_identity`, `Polynomial.eq_of_infinite_eval_eq`, `Polynomial.funext`

## Chapter 9

22 items; 21 with a Lean name; 7 proved proved here; 14 in Mathlib; 1 not a result.

- **Definition 9.1 p.664**, p.664 [PC-166]: A sequence is a function on the natural numbers; its value at n is the nth term — *not a result* — –
- **Definition 9.2 p.666**, p.666 [PC-167]: A sequence is arithmetic if consecutive terms differ by a fixed d, geometric if each term is a fixed r times the previous — *proved proved here* — `UndergradKB.Precalculus.IsArithmeticSeq`, `UndergradKB.Precalculus.IsGeometricSeq`, `UndergradKB.Precalculus.seq_arith_geom_recurrence`
- **Equation 9.1 p.668**, p.668 [PC-168]: An arithmetic sequence with first term a, difference d has nth term a+(n-1)d; a geometric one with ratio r has nth term $ar^{n-1}$ — *proved proved here* — `UndergradKB.Precalculus.seq_arith_nth_term`, `UndergradKB.Precalculus.seq_geom_nth_term`

#### Section 9.1

- **Example 9.1.3 p.668**, p.668 [PC-168]: An arithmetic sequence with first term a, difference d has nth term a+(n-1)d; a geometric one with ratio r has nth term $ar^{n-1}$ — *proved proved here* — `UndergradKB.Precalculus.seq_arith_nth_term`, `UndergradKB.Precalculus.seq_geom_nth_term`
- **Definition 9.3 p.673**, p.673 [PC-169]: Summation notation: the sum from index m to p of a sequence is the sum of its terms $a_m$ through $a_p$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_9_3_summation`, `Finset.Icc`
- **Theorem 9.1 p.676**, p.676 [PC-170]: Summation is linear (sum of sums, constant factor out), splits at an interior index, and the index can be shifted — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_9_1_sum_add`, `UndergradKB.Precalculus.Course.thm_9_1_sum_sub`, `UndergradKB.Precalculus.Course.thm_9_1_sum_const_mul`, `UndergradKB.Precalculus.Course.thm_9_1_sum_split`
- **Equation 9.2 p.678**, p.678 [PC-171]: Sum of the first n terms of an arithmetic sequence is $n(a_1+a_n)/2=\frac n2(2a+(n-1)d)$ — *proved proved here* — `UndergradKB.Precalculus.seq_arith_sum_formula`, `UndergradKB.Precalculus.seq_arith_sum_first_last`
- **Equation 9.2 p.678 (consequence)**, p.678 [PC-172]: $1+2+\dots+n=n(n+1)/2$ — *in Mathlib* — `UndergradKB.Precalculus.Course.eq_9_2_sum_first_n`, `Finset.sum_range_id_mul_two`, `Finset.sum_range_id`
- **Equation 9.2 p.678**, p.678 [PC-173]: Sum of the first n terms of a geometric sequence is $a\frac{1-r^n}{1-r}$ for $r\ne1$ and $na$ for r=1 — *in Mathlib* — `UndergradKB.Precalculus.Course.eq_9_2_geometric_sum`, `UndergradKB.Precalculus.Course.eq_9_2_geometric_sum_ratio_one`, `geom_sum_eq`, `Finset.mul_sum`
- **Equation 9.3 p.679**, p.679 [PC-174]: Future value of an ordinary annuity with payment P, rate i per period, k periods is $P((1+i)^k-1)/i$ — *proved proved here* — `UndergradKB.Precalculus.seq_annuity_balance`

#### Section 9.2

- **Example 9.2.2 p.680**, p.680 [PC-174]: Future value of an ordinary annuity with payment P, rate i per period, k periods is $P((1+i)^k-1)/i$ — *proved proved here* — `UndergradKB.Precalculus.seq_annuity_balance`
- **Theorem 9.2 p.681**, p.681 [PC-175]: Geometric series with abs(r)<1 sums to $a/(1-r)$; for abs(r) at least 1 the series does not converge — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_9_2_geometric_series_converges`, `UndergradKB.Precalculus.Course.thm_9_2_geometric_series_diverges`, `tsum_geometric_of_abs_lt_one`, `hasSum_geometric_of_abs_lt_one`

#### Section 9.3

- **§9.3 p.685**, p.685 [PC-176]: Principle of mathematical induction: if P(1) and P(k) implies P(k+1), then P(n) for all natural n — *in Mathlib* — `UndergradKB.Precalculus.Course.box_9_3_induction`, `Nat.le_induction`
- **Example 9.3.1 p.686**, p.686 [PC-177]: The conjugate of $z^n$ is the nth power of the conjugate of z (proved by induction) — *in Mathlib* — `UndergradKB.Precalculus.Course.ex_9_3_1_conj_pow`, `map_pow`
- **Example 9.3.1 p.686**, p.686 [PC-178]: Replacing one row of a square matrix by c times that row multiplies the determinant by c — *in Mathlib* — `UndergradKB.Precalculus.Course.ex_9_3_1_det_scaled_row`, `Matrix.det_updateRow_smul`
- **Definition 9.4 p.693**, p.693 [PC-179]: Factorial: 0!=1 and n!=n(n-1)! — *in Mathlib* — `UndergradKB.Precalculus.Course.def_9_4_factorial`, `Nat.factorial`, `Nat.factorial_zero`, `Nat.factorial_succ`

#### Section 9.4

- **Example 9.4.1 p.693**, p.693 [PC-180]: $n!>3^n$ for all $n\ge7$ — *proved proved here* — `UndergradKB.Precalculus.seq_three_pow_lt_factorial`
- **§9.4 p.694**, p.694 [PC-181]: For every x>0, $x^n/n!\to0$ as n grows (remark, no proof in book) — *in Mathlib* — `UndergradKB.Precalculus.Course.box_9_4_pow_div_factorial_tendsto`, `FloorSemiring.tendsto_pow_div_factorial_atTop`
- **Theorem 9.3 p.695**, p.695 [PC-184]: Pascal rule: $\binom n{j-1}+\binom nj=\binom{n+1}j$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_9_3_pascal`, `Nat.choose_succ_succ`
- **§9.4 p.695**, p.695 [PC-183]: $\binom nj$ counts the ways to select j items from n when order is ignored — *in Mathlib* — `UndergradKB.Precalculus.Course.box_9_4_choose_counts_subsets`, `Finset.card_powersetCard`
- **Definition 9.5 p.695**, p.695 [PC-182]: Binomial coefficient: $\binom nj=\frac{n!}{j!(n-j)!}$ for $0\le j\le n$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_9_5_choose_factorial`, `Nat.choose`, `Nat.choose_eq_factorial_div_factorial`, `Nat.choose_mul_factorial_mul_factorial`
- **Theorem 9.4 p.696**, p.696 [PC-185]: Binomial theorem: $(a+b)^n=\sum_{j=0}^n\binom nj a^{n-j}b^j$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_9_4_binomial`, `add_pow`, `Commute.add_pow`

## Chapter 10

71 items; 71 with a Lean name; 57 proved proved here; 14 in Mathlib.


#### Section 10.1

- **§10.1 p.705**, p.705 [PC-186]: An angle is formed by two rays sharing an initial point, the vertex — *proved proved here* — `UndergradKB.Trigonometry.angle_eq_of_mem_ray`
- **§10.1 p.706**, p.706 [PC-187]: Angles are acute (below 90), right, obtuse (90 to 180), straight; two angles are supplementary or complementary when they sum to 180 or 90 degrees — *proved proved here* — `UndergradKB.Trigonometry.angle_kind_unique`, `UndergradKB.Trigonometry.angle_kind_cases`, `UndergradKB.Trigonometry.angle_kinds_exclusive`, `UndergradKB.Trigonometry.two_angles_acute`
- **§10.1 p.707**, p.707 [PC-188]: One degree is 60 minutes and one minute is 60 seconds — *proved proved here* — `UndergradKB.Trigonometry.dmsToDeg_minute_second`, `UndergradKB.Trigonometry.degToRad_dmsToDeg`
- **§10.1 p.708**, p.708 [PC-187]: Angles are acute (below 90), right, obtuse (90 to 180), straight; two angles are supplementary or complementary when they sum to 180 or 90 degrees — *proved proved here* — `UndergradKB.Trigonometry.angle_kind_unique`, `UndergradKB.Trigonometry.angle_kind_cases`, `UndergradKB.Trigonometry.angle_kinds_exclusive`, `UndergradKB.Trigonometry.two_angles_acute`
- **§10.1 p.710**, p.710 [PC-189]: Counterclockwise rotation is positive, clockwise negative; an angle is in standard position when vertex is the origin and initial side the positive x-axis — *proved proved here* — `UndergradKB.Trigonometry.standardPosition`
- **§10.1 p.710**, p.710 [PC-190]: Angle in standard position is a quadrant angle when its terminal side is in a quadrant, quadrantal when on an axis — *proved proved here* — `UndergradKB.Trigonometry.existsUnique_quadrant`, `UndergradKB.Trigonometry.not_inQuadrant_of_axis`, `UndergradKB.Trigonometry.isQuadrantal_iff`
- **§10.1 p.710**, p.710 [PC-191]: Angles in standard position are coterminal iff they differ by a multiple of 360 degrees (2 pi radians) — *proved proved here* — `UndergradKB.Trigonometry.sin_cos_add_int_mul_two_pi`, `UndergradKB.Trigonometry.existsUnique_coterminal_Ico`, `UndergradKB.Trigonometry.existsUnique_coterminal_Ico_deg`
- **Definition 10.1 p.712**, p.712 [PC-192]: $\pi$ is the ratio of circumference to diameter of a circle, so circumference over radius is $2\pi$ — *proved proved here* — `UndergradKB.Trigonometry.circumference`
- **§10.1 p.713**, p.713 [PC-193]: Radian measure of a central angle is arc length over radius; one revolution is 2 pi radians; arc length is $s=r\theta$ — *proved proved here* — `UndergradKB.Trigonometry.radian_eq_arc_div_radius`, `UndergradKB.Trigonometry.arc_length`, `UndergradKB.Trigonometry.arc_length'`
- **§10.1 p.714**, p.714 [PC-191]: Angles in standard position are coterminal iff they differ by a multiple of 360 degrees (2 pi radians) — *proved proved here* — `UndergradKB.Trigonometry.sin_cos_add_int_mul_two_pi`, `UndergradKB.Trigonometry.existsUnique_coterminal_Ico`, `UndergradKB.Trigonometry.existsUnique_coterminal_Ico_deg`
- **Equation 10.1 p.716**, p.716 [PC-194]: Degrees times $\pi/180$ gives radians; radians times $180/\pi$ gives degrees — *proved proved here* — `UndergradKB.Trigonometry.degToRad_spec`, `UndergradKB.Trigonometry.degToRad_iff`, `UndergradKB.Trigonometry.degToRad`, `UndergradKB.Trigonometry.radToDeg`
- **§10.1 p.716**, p.716 [PC-195]: Wrapping the real line around the unit circle identifies each real t with the oriented arc of length t from (1,0) — *proved proved here* — `UndergradKB.Trigonometry.unitCircle_arc_point`
- **Equation 10.2 p.719**, p.719 [PC-196]: Circular motion at constant angular velocity: linear velocity is $v=r\omega$ (average velocity is s/t, average angular velocity is theta/t) — *proved proved here* — `UndergradKB.Trigonometry.linear_speed`, `UndergradKB.Trigonometry.avgLinearSpeed_uniform_circular`, `UndergradKB.Trigonometry.avgAngularSpeed_uniform_circular`
- **§10.1 p.720**, p.720 [PC-197]: Ordinary frequency is cycles per unit time, angular frequency is $\omega=2\pi f$, period is $T=1/f$ — *proved proved here* — `UndergradKB.Precalculus.angularFrequency`, `UndergradKB.Precalculus.periodOfFrequency`, `UndergradKB.Precalculus.frequency_period_periodic`

#### Section 10.2

- **§10.2 p.729**, p.729 [PC-198]: Cosine of an angle is the x-coordinate and sine the y-coordinate of the point where its terminal side meets the unit circle — *proved proved here* — `UndergradKB.Precalculus.Course.box_10_2_unit_circle_point`, `UndergradKB.Trigonometry.unitCircle_arc_point`
- **Example 10.2.1 p.729**, p.729 [PC-201]: Exact cos and sin at 0, 30, 45, 60, 90 degrees and (by reference angles) all multiples of 30 and 45 degrees — *proved proved here* — `UndergradKB.Trigonometry.six_functions_special_values`, `UndergradKB.Trigonometry.sin_cos_second_quadrant`, `UndergradKB.Trigonometry.sin_cos_third_quadrant`, `UndergradKB.Trigonometry.sin_cos_fourth_quadrant`
- **Theorem 10.1 p.732**, p.732 [PC-199]: Pythagorean identity $\cos^2\theta+\sin^2\theta=1$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_1_pythagorean`, `Real.sin_sq_add_cos_sq`, `Real.cos_sq_add_sin_sq`
- **Example 10.2.2 p.732**, p.732 [PC-199]: Pythagorean identity $\cos^2\theta+\sin^2\theta=1$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_1_pythagorean`, `Real.sin_sq_add_cos_sq`, `Real.cos_sq_add_sin_sq`
- **§10.2 p.733**, p.733 [PC-200]: Reference angle is the acute angle to the x-axis; cos and sin of an angle equal those of its reference angle up to a quadrant-determined sign — *proved proved here* — `UndergradKB.Trigonometry.refAngle`, `UndergradKB.Trigonometry.abs_sin_cos_eq_refAngle`
- **Theorem 10.2 p.734**, p.734 [PC-200]: Reference angle is the acute angle to the x-axis; cos and sin of an angle equal those of its reference angle up to a quadrant-determined sign — *proved proved here* — `UndergradKB.Trigonometry.refAngle`, `UndergradKB.Trigonometry.abs_sin_cos_eq_refAngle`
- **§10.2 p.734**, p.734 [PC-201]: Exact cos and sin at 0, 30, 45, 60, 90 degrees and (by reference angles) all multiples of 30 and 45 degrees — *proved proved here* — `UndergradKB.Trigonometry.six_functions_special_values`, `UndergradKB.Trigonometry.sin_cos_second_quadrant`, `UndergradKB.Trigonometry.sin_cos_third_quadrant`, `UndergradKB.Trigonometry.sin_cos_fourth_quadrant`
- **§10.2 p.736**, p.736 [PC-201]: Exact cos and sin at 0, 30, 45, 60, 90 degrees and (by reference angles) all multiples of 30 and 45 degrees — *proved proved here* — `UndergradKB.Trigonometry.six_functions_special_values`, `UndergradKB.Trigonometry.sin_cos_second_quadrant`, `UndergradKB.Trigonometry.sin_cos_third_quadrant`, `UndergradKB.Trigonometry.sin_cos_fourth_quadrant`
- **Theorem 10.3 p.742**, p.742 [PC-202]: A point (x,y) on the terminal side at distance r satisfies $x=r\cos\theta$, $y=r\sin\theta$, hence $\cos\theta=x/r$, $\sin\theta=y/r$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_3_trig_of_point`, `UndergradKB.Trigonometry.trig_of_point`, `UndergradKB.Trigonometry.trig_of_point_arg`
- **Example 10.2.6 p.743**, p.743 [PC-202]: A point (x,y) on the terminal side at distance r satisfies $x=r\cos\theta$, $y=r\sin\theta$, hence $\cos\theta=x/r$, $\sin\theta=y/r$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_3_trig_of_point`, `UndergradKB.Trigonometry.trig_of_point`, `UndergradKB.Trigonometry.trig_of_point_arg`
- **Example 10.2.7 p.744**, p.744 [PC-203]: An object moving on a circle of radius r with constant angular velocity omega from (r,0) is at $(r\cos\omega t, r\sin\omega t)$ — *proved proved here* — `UndergradKB.Precalculus.circularMotion`, `UndergradKB.Precalculus.circular_motion_on_circle`
- **Equation 10.3 p.744**, p.744 [PC-203]: An object moving on a circle of radius r with constant angular velocity omega from (r,0) is at $(r\cos\omega t, r\sin\omega t)$ — *proved proved here* — `UndergradKB.Precalculus.circularMotion`, `UndergradKB.Precalculus.circular_motion_on_circle`
- **Theorem 10.4 p.745**, p.745 [PC-204]: In a right triangle with acute angle theta, $\cos\theta$ is adjacent over hypotenuse and $\sin\theta$ is opposite over hypotenuse — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_4_cos_right_triangle`, `UndergradKB.Precalculus.Course.thm_10_4_sin_right_triangle`, `EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two`, `EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two`
- **Theorem 10.5 p.747**, p.747 [PC-205]: Cosine and sine are defined on all reals (angle in radians) with range $[-1,1]$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_5_range_cos_sin`, `Real.range_sin`, `Real.range_cos`, `Real.abs_sin_le_one`
- **Definition 10.2 p.756**, p.756 [PC-206]: The six circular functions are x, y, 1/x, 1/y, y/x, x/y for the point (x,y) on the unit circle (when defined) — *proved proved here* — `UndergradKB.Precalculus.Course.def_10_2_circular_functions`, `UndergradKB.Trigonometry.trig_of_point`, `UndergradKB.Trigonometry.trig_of_point_arg`

#### Section 10.3

- **§10.3 p.757**, p.757 [PC-207]: Geometric meaning: tan is the height on the tangent line x=1 and sec the length of the secant segment cut off — *proved proved here* — `UndergradKB.Precalculus.secant`, `UndergradKB.Precalculus.cosecant`, `UndergradKB.Precalculus.tan_sec_on_line_x_eq_one`
- **Theorem 10.6 p.757**, p.757 [PC-208]: Reciprocal and quotient identities: sec=1/cos, csc=1/sin, tan=sin/cos, cot=cos/sin (undefined when the denominator is 0) — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_6_quotient_identities`, `UndergradKB.Precalculus.Course.thm_10_6_reciprocal_identities`, `UndergradKB.Trigonometry.sec_eq_one_div_cos`, `UndergradKB.Trigonometry.csc_eq_one_div_sin`
- **§10.3 p.759**, p.759 [PC-209]: Table of tan and cot at 0, 30, 45, 60, 90 degrees — *proved proved here* — `UndergradKB.Trigonometry.six_functions_special_values`, `UndergradKB.Trigonometry.six_functions_quadrantal`
- **Theorem 10.7 p.759**, p.759 [PC-210]: Every circular function of an angle equals, up to sign, that of its reference angle — *proved proved here* — `UndergradKB.Trigonometry.abs_sin_cos_eq_refAngle`
- **Theorem 10.8 p.761**, p.761 [PC-211]: Pythagorean identities: $\cos^2+\sin^2=1$, $1+\tan^2=\sec^2$, $1+\cot^2=\csc^2$ and rearranged forms — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_8_one_add_tan_sq`, `UndergradKB.Precalculus.Course.thm_10_8_one_add_cot_sq`, `UndergradKB.Trigonometry.one_add_tan_sq_eq_sec_sq`, `UndergradKB.Trigonometry.cot_sq_add_one_eq_csc_sq`
- **§10.3 p.763**, p.763 [PC-212]: Pythagorean conjugates: products such as $(1-\cos)(1+\cos)=\sin^2$, $(\sec-\tan)(\sec+\tan)=1$, $(\csc-\cot)(\csc+\cot)=1$ — *proved proved here* — `UndergradKB.Precalculus.pythagorean_conjugates`
- **Theorem 10.9 p.764**, p.764 [PC-213]: For a point (x,y) at distance r: $\sec=r/x$, $\csc=r/y$, $\tan=y/x$, $\cot=x/y$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_9_functions_of_point`, `UndergradKB.Trigonometry.trig_of_point`, `UndergradKB.Trigonometry.trig_of_point_arg`
- **Example 10.3.4 p.765**, p.765 [PC-213]: For a point (x,y) at distance r: $\sec=r/x$, $\csc=r/y$, $\tan=y/x$, $\cot=x/y$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_9_functions_of_point`, `UndergradKB.Trigonometry.trig_of_point`, `UndergradKB.Trigonometry.trig_of_point_arg`
- **Theorem 10.10 p.765**, p.765 [PC-214]: In a right triangle, tan is opposite/adjacent, sec is hypotenuse/adjacent, csc is hypotenuse/opposite, cot is adjacent/opposite — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_10_tan_right_triangle`, `UndergradKB.Trigonometry.csc_angle_of_angle_eq_pi_div_two`, `UndergradKB.Trigonometry.sec_angle_of_angle_eq_pi_div_two`, `UndergradKB.Trigonometry.cot_angle_of_angle_eq_pi_div_two`
- **Theorem 10.11 p.769**, p.769 [PC-215]: Domains and ranges: cos, sin on all reals with range [-1,1]; tan, cot range all reals; sec, csc range abs at least 1; domains omit zeros of cos or sin — *proved proved here* — `UndergradKB.Trigonometry.one_le_abs_sec`, `UndergradKB.Trigonometry.one_le_abs_csc`, `UndergradKB.Trigonometry.sec_eq_zero_iff`, `UndergradKB.Trigonometry.csc_eq_zero_iff`
- **Theorem 10.12 p.782**, p.782 [PC-216]: Even/odd identities: cos and sec are even; sin, tan, csc, cot are odd — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_12_even_odd`, `UndergradKB.Trigonometry.sec_neg`, `UndergradKB.Trigonometry.csc_neg`, `UndergradKB.Trigonometry.cot_neg`
- **Theorem 10.13 p.783**, p.783 [PC-217]: $\cos(\alpha\pm\beta)=\cos\alpha\cos\beta\mp\sin\alpha\sin\beta$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_13_cos_sum_diff`, `Real.cos_add`, `Real.cos_sub`

#### Section 10.4

- **Example 10.4.1 p.784**, p.784 [PC-218]: Cofunction identities: $\cos(\pi/2-\theta)=\sin\theta$, $\sin(\pi/2-\theta)=\cos\theta$, and tan/cot, sec/csc likewise — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_14_cofunction`, `UndergradKB.Trigonometry.sec_pi_div_two_sub`, `UndergradKB.Trigonometry.csc_pi_div_two_sub`, `UndergradKB.Trigonometry.cot_pi_div_two_sub`
- **Theorem 10.14 p.785**, p.785 [PC-218]: Cofunction identities: $\cos(\pi/2-\theta)=\sin\theta$, $\sin(\pi/2-\theta)=\cos\theta$, and tan/cot, sec/csc likewise — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_14_cofunction`, `UndergradKB.Trigonometry.sec_pi_div_two_sub`, `UndergradKB.Trigonometry.csc_pi_div_two_sub`, `UndergradKB.Trigonometry.cot_pi_div_two_sub`
- **Theorem 10.15 p.785**, p.785 [PC-219]: $\sin(\alpha\pm\beta)=\sin\alpha\cos\beta\pm\cos\alpha\sin\beta$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_15_sin_sum_diff`, `Real.sin_add`, `Real.sin_sub`
- **Example 10.4.2 p.786**, p.786 [PC-220]: Combined sum/difference identities including $\tan(\alpha\pm\beta)=\frac{\tan\alpha\pm\tan\beta}{1\mp\tan\alpha\tan\beta}$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_16_tan_sum_diff`, `Real.cos_add`, `Real.sin_add`, `Real.tan_add`
- **Theorem 10.16 p.787**, p.787 [PC-220]: Combined sum/difference identities including $\tan(\alpha\pm\beta)=\frac{\tan\alpha\pm\tan\beta}{1\mp\tan\alpha\tan\beta}$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_16_tan_sum_diff`, `Real.cos_add`, `Real.sin_add`, `Real.tan_add`
- **Example 10.4.3 p.788**, p.788 [PC-226]: Example: $\cos3\theta=4\cos^3\theta-3\cos\theta$, and $\sin2\theta=2\tan\theta/(1+\tan^2\theta)$ — *proved proved here* — `UndergradKB.Precalculus.cos_three_and_sin_two_tan`
- **Theorem 10.17 p.788**, p.788 [PC-221]: Double angle: $\sin2\theta=2\sin\theta\cos\theta$, three forms of $\cos2\theta$, $\tan2\theta=2\tan\theta/(1-\tan^2\theta)$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_17_double_angle`, `UndergradKB.Precalculus.Course.thm_10_17_tan_double_angle`, `Real.sin_two_mul`, `Real.cos_two_mul`
- **Theorem 10.18 p.790**, p.790 [PC-222]: Power reduction: $\cos^2\theta=(1+\cos2\theta)/2$, $\sin^2\theta=(1-\cos2\theta)/2$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_18_power_reduction`, `Real.cos_sq`, `Real.sin_sq_eq_half_sub`
- **Example 10.4.5 p.791**, p.791 [PC-223]: Half angle formulas for cos, sin, tan of theta/2 with sign by quadrant; also $\tan(\theta/2)=\sin\theta/(1+\cos\theta)$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_19_half_angle`, `UndergradKB.Precalculus.Course.ex_10_4_5_tan_half_angle`, `UndergradKB.Trigonometry.tan_sq_half`, `UndergradKB.Trigonometry.tan_half_eq_sin_div_one_add_cos`
- **Theorem 10.19 p.791**, p.791 [PC-223]: Half angle formulas for cos, sin, tan of theta/2 with sign by quadrant; also $\tan(\theta/2)=\sin\theta/(1+\cos\theta)$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_19_half_angle`, `UndergradKB.Precalculus.Course.ex_10_4_5_tan_half_angle`, `UndergradKB.Trigonometry.tan_sq_half`, `UndergradKB.Trigonometry.tan_half_eq_sin_div_one_add_cos`
- **Theorem 10.20 p.792**, p.792 [PC-224]: Product to sum: $\cos\alpha\cos\beta=\frac12[\cos(\alpha-\beta)+\cos(\alpha+\beta)]$ and two more — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_20_product_to_sum`, `Real.two_mul_cos_mul_cos`, `Real.two_mul_sin_mul_sin`, `Real.two_mul_sin_mul_cos`
- **Theorem 10.21 p.793**, p.793 [PC-225]: Sum to product: $\cos\alpha+\cos\beta=2\cos\frac{\alpha+\beta}2\cos\frac{\alpha-\beta}2$ and three more — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_21_sum_to_product`, `Real.cos_add_cos`, `Real.cos_sub_cos`, `Real.sin_add_sin`
- **Definition 10.3 p.802**, p.802 [PC-227]: A function is periodic if f(t+c)=f(t) for some c; the period is the smallest positive such c — *proved proved here* — `UndergradKB.Trigonometry.isLeast_period_sin`, `Function.Periodic`
- **Theorem 10.22 p.803**, p.803 [PC-228]: cos and sin: domain all reals, range [-1,1], continuous, cos even and sin odd, period $2\pi$ — *proved proved here* — `UndergradKB.Trigonometry.isLeast_period_sin`, `UndergradKB.Trigonometry.isLeast_period_cos`, `Real.range_sin`, `Real.range_cos`

#### Section 10.5

- **§10.5 p.804**, p.804 [PC-229]: The sine graph is the cosine graph shifted right by pi/2: $\sin x=\cos(x-\pi/2)$ — *in Mathlib* — `UndergradKB.Precalculus.Course.box_10_5_sin_eq_shifted_cos`, `Real.cos_sub_pi_div_two`
- **Theorem 10.23 p.807**, p.807 [PC-230]: For omega>0, $A\cos(\omega x+\phi)+B$ and $A\sin(\omega x+\phi)+B$ have period $2\pi/\omega$, amplitude abs(A), phase shift $-\phi/\omega$, vertical shift B — *proved proved here* — `UndergradKB.Trigonometry.amplitude_sinusoid`, `UndergradKB.Trigonometry.isLeast_period_sin_mul`, `UndergradKB.Trigonometry.sinusoid_phase_shift`, `UndergradKB.Trigonometry.range_sinusoid`
- **Example 10.5.3 p.810**, p.810 [PC-231]: $a\cos\omega x+b\sin\omega x$ is a single sinusoid with amplitude $\sqrt{a^2+b^2}$ — *proved proved here* — `UndergradKB.Trigonometry.exists_amplitude_phase`, `UndergradKB.Trigonometry.exists_mul_sin_add_mul_cos_eq`
- **Theorem 10.24 p.814**, p.814 [PC-232]: sec and csc: domain without zeros of cos (sin), range abs at least 1, continuous on domain, sec even, csc odd, period $2\pi$ — *proved proved here* — `UndergradKB.Trigonometry.one_le_abs_sec`, `UndergradKB.Trigonometry.one_le_abs_csc`, `UndergradKB.Trigonometry.isLeast_period_sec`, `UndergradKB.Trigonometry.isLeast_period_csc`
- **Theorem 10.25 p.818**, p.818 [PC-233]: tan and cot: domains omit poles, range all reals, continuous on domain, odd, period $\pi$ — *proved proved here* — `UndergradKB.Trigonometry.isLeast_period_tan`, `UndergradKB.Trigonometry.isLeast_period_cot`, `UndergradKB.Trigonometry.cot_neg`, `Real.tan_periodic`
- **Theorem 10.26 p.832**, p.832 [PC-234]: arccos has domain [-1,1], range [0,pi], and $\cos\arccos x=x$, $\arccos\cos x=x$ on [0,pi]; arcsin has domain [-1,1], range [-pi/2,pi/2], inverse relations on those intervals, and is odd — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_10_26_arcsin_range`, `UndergradKB.Precalculus.Course.thm_10_26_arccos_range`, `UndergradKB.Precalculus.Course.thm_10_26_sin_arcsin_cos_arccos`, `UndergradKB.Precalculus.Course.thm_10_26_arcsin_sin_arccos_cos`

#### Section 10.6

- **Example 10.6.1 p.833**, p.833 [PC-238]: Composites such as tan(arccos x)=sqrt(1-x^2)/x, cos(2 arcsin x)=1-2x^2, tan(2 arctan x)=2x/(1-x^2), tan(arcsec x), cos(arccsc 4x) with the domains of validity — *proved proved here* — `UndergradKB.Precalculus.tan_arcsecCF`, `UndergradKB.Precalculus.cos_arccscCF`, `UndergradKB.Precalculus.cos_arccscCF_four_mul`, `UndergradKB.Precalculus.inverse_trig_composites`
- **Theorem 10.27 p.836**, p.836 [PC-235]: arctan has domain R, range (-pi/2,pi/2), limits at plus and minus infinity, tan(arctan x)=x, arctan(tan x)=x on (-pi/2,pi/2), odd, and arctan x = arccot(1/x) for x>0; arccot has range (0,pi) with the analogous properties — *proved proved here* — `UndergradKB.Precalculus.Course.thm_10_27_arctan`, `UndergradKB.Precalculus.Course.thm_10_27_arctan_limits`, `UndergradKB.Trigonometry.arccot_spec`, `UndergradKB.Trigonometry.cot_arccot`
- **Example 10.6.2 p.837**, p.837 [PC-238]: Composites such as tan(arccos x)=sqrt(1-x^2)/x, cos(2 arcsin x)=1-2x^2, tan(2 arctan x)=2x/(1-x^2), tan(arcsec x), cos(arccsc 4x) with the domains of validity — *proved proved here* — `UndergradKB.Precalculus.tan_arcsecCF`, `UndergradKB.Precalculus.cos_arccscCF`, `UndergradKB.Precalculus.cos_arccscCF_four_mul`, `UndergradKB.Precalculus.inverse_trig_composites`
- **Example 10.6.3 p.840**, p.840 [PC-238]: Composites such as tan(arccos x)=sqrt(1-x^2)/x, cos(2 arcsin x)=1-2x^2, tan(2 arctan x)=2x/(1-x^2), tan(arcsec x), cos(arccsc 4x) with the domains of validity — *proved proved here* — `UndergradKB.Precalculus.tan_arcsecCF`, `UndergradKB.Precalculus.cos_arccscCF`, `UndergradKB.Precalculus.cos_arccscCF_four_mul`, `UndergradKB.Precalculus.inverse_trig_composites`
- **Theorem 10.28 p.840**, p.840 [PC-236]: Trigonometry-friendly arcsec/arccsc: domain abs(x) at least 1, arcsec range [0,pi] without pi/2, arccsc range [-pi/2,pi/2] without 0, arcsec x = arccos(1/x), arccsc x = arcsin(1/x), inverse relations — *proved proved here* — `UndergradKB.Trigonometry.arcsec_spec`, `UndergradKB.Trigonometry.arccsc_spec`, `UndergradKB.Trigonometry.arcsec`, `UndergradKB.Trigonometry.arccsc`
- **Example 10.6.4 p.843**, p.843 [PC-238]: Composites such as tan(arccos x)=sqrt(1-x^2)/x, cos(2 arcsin x)=1-2x^2, tan(2 arctan x)=2x/(1-x^2), tan(arcsec x), cos(arccsc 4x) with the domains of validity — *proved proved here* — `UndergradKB.Precalculus.tan_arcsecCF`, `UndergradKB.Precalculus.cos_arccscCF`, `UndergradKB.Precalculus.cos_arccscCF_four_mul`, `UndergradKB.Precalculus.inverse_trig_composites`
- **Theorem 10.29 p.843**, p.843 [PC-237]: Calculus-friendly arcsec/arccsc with ranges [0,pi/2) union [pi,3pi/2) and (0,pi/2] union (pi,3pi/2], their inverse relations, and arcsec x = arccos(1/x) for x at least 1 only — *proved proved here* — `UndergradKB.Precalculus.arcsecCF`, `UndergradKB.Precalculus.arccscCF`, `UndergradKB.Precalculus.arcsecCF_properties`, `UndergradKB.Precalculus.arccscCF_properties`
- **Example 10.6.5 p.845**, p.845 [PC-239]: arccot x = arctan(1/x) for x>0 and pi+arctan(1/x) for x<0 (arccot 0 = pi/2) — *proved proved here* — `UndergradKB.Precalculus.arccotR`, `UndergradKB.Precalculus.arccotR_properties`
- **Example 10.6.7 p.850**, p.850 [PC-240]: All angles with sin theta = c (abs c at most 1) are arcsin c + 2 pi k or pi - arcsin c + 2 pi k; similarly cos and tan via arccos, arctan — *proved proved here* — `UndergradKB.Trigonometry.sin_eq_iff`, `UndergradKB.Trigonometry.cos_eq_iff`, `UndergradKB.Trigonometry.tan_eq_iff`

#### Section 10.7

- **§10.7 p.869**, p.869 [PC-241]: Solving basic equations: cos u = c or sin u = c solve on [0,2pi) then add multiples of 2pi, none if abs c>1; sec, csc via cos, sin; tan u = c add multiples of pi; cot u = 0 gives pi/2 + pi k — *proved proved here* — `UndergradKB.Trigonometry.periodic_solutions`, `UndergradKB.Trigonometry.sin_eq_iff`, `UndergradKB.Trigonometry.cos_eq_iff`, `UndergradKB.Trigonometry.tan_eq_iff`

## Chapter 11

66 items; 66 with a Lean name; 39 proved proved here; 27 in Mathlib.

- **Theorem 11.1 p.899**, p.899 [PC-242]: Undamped spring-mass motion with mass $m$, constant $k$, start $x_0$, velocity $v_0$ is $x(t)=A\sin(\omega t+\varphi)$ with $\omega=\sqrt{k/m}$, $A=\sqrt{x_0^2+(v_0/\omega)^2}$, $A\sin\varphi=x_0$, $A\omega\cos\varphi=v_0$ — *proved proved here* — `UndergradKB.Precalculus.springMotion`, `UndergradKB.Precalculus.spring_mass_solution`
- **Theorem 11.2 p.909**, p.909 [PC-243]: Law of Sines: $\sin\alpha/a=\sin\beta/b=\sin\gamma/c$ in a triangle — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_2_law_of_sines`, `EuclideanGeometry.law_sin`, `EuclideanGeometry.sin_angle_div_dist_eq_sin_angle_div_dist`, `EuclideanGeometry.dist_eq_dist_mul_sin_angle_div_sin_angle`
- **Theorem 11.3 p.913**, p.913 [PC-244]: Ambiguous (SSA) case: with $h=c\sin\alpha$, no triangle if $a<h$, one right triangle if $a=h$, two if $h<a<c$, one if $a\ge c$ — *proved proved here* — `UndergradKB.Trigonometry.ncard_ssaSolutions`, `UndergradKB.Trigonometry.ssaSolutions`, `UndergradKB.Trigonometry.ssaSolutions_acute_two`, `UndergradKB.Trigonometry.dist_mem_ssaSolutions`

#### Section 11.2

- **Example 11.2.4 p.915**, p.915 [PC-245]: Triangle area is $\tfrac12 bc\sin\alpha=\tfrac12 ac\sin\beta=\tfrac12 ab\sin\gamma$ — *proved proved here* — `UndergradKB.Trigonometry.area_eq_mul_mul_sin_div_two`, `UndergradKB.Trigonometry.area_eq_half_mul_sin_included`, `UndergradKB.Trigonometry.area`
- **Theorem 11.4 p.915**, p.915 [PC-245]: Triangle area is $\tfrac12 bc\sin\alpha=\tfrac12 ac\sin\beta=\tfrac12 ab\sin\gamma$ — *proved proved here* — `UndergradKB.Trigonometry.area_eq_mul_mul_sin_div_two`, `UndergradKB.Trigonometry.area_eq_half_mul_sin_included`, `UndergradKB.Trigonometry.area`
- **Theorem 11.5 p.922**, p.922 [PC-246]: Law of Cosines: $a^2=b^2+c^2-2bc\cos\alpha$ and cyclic versions, equivalently $\cos\alpha=(b^2+c^2-a^2)/(2bc)$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_5_law_of_cosines`, `EuclideanGeometry.law_cos`, `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`, `InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle`
- **Theorem 11.6 p.926**, p.926 [PC-247]: Heron's formula: area $=\sqrt{s(s-a)(s-b)(s-c)}$, $s$ the semiperimeter — *proved proved here* — `UndergradKB.Trigonometry.heron`, `UndergradKB.Trigonometry.heron_openstax`

#### Section 11.3

- **Example 11.3.3 p.927**, p.927 [PC-247]: Heron's formula: area $=\sqrt{s(s-a)(s-b)(s-c)}$, $s$ the semiperimeter — *proved proved here* — `UndergradKB.Trigonometry.heron`, `UndergradKB.Trigonometry.heron_openstax`

#### Section 11.4

- **§11.4 p.931**, p.931 [PC-248]: Polar coordinates $(r,\theta)$: directed distance from a pole and angle from the polar axis; negative $r$ means the opposite direction — *proved proved here* — `UndergradKB.Trigonometry.polarPoint_add_int_mul_two_pi`, `UndergradKB.Trigonometry.polarPoint_eq_iff`, `UndergradKB.Trigonometry.polarPoint_neg_eq_add_pi`
- **§11.4 p.935**, p.935 [PC-249]: Two polar pairs with nonzero $r$ give the same point iff $(r',\theta')=(r,\theta+2\pi k)$ or $(-r,\theta+(2k+1)\pi)$; $(0,\theta)$ is the pole — *proved proved here* — `UndergradKB.Trigonometry.polarPoint_eq_iff`, `UndergradKB.Trigonometry.polarPoint_add_int_mul_two_pi`, `UndergradKB.Trigonometry.polarPoint_neg_eq_add_pi`
- **Theorem 11.7 p.936**, p.936 [PC-250]: Polar to rectangular: $x=r\cos\theta$, $y=r\sin\theta$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_7_polar_to_rectangular`, `UndergradKB.Precalculus.Course.thm_11_7_polar_to_rectangular_complex`, `polarCoord_symm_apply`, `Complex.norm_mul_cos_arg`
- **Theorem 11.7 p.936**, p.936 [PC-251]: Rectangular to polar: $x^2+y^2=r^2$ and $\tan\theta=y/x$ for $x\ne0$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_7_rectangular_to_polar`, `UndergradKB.Trigonometry.polarPoint_sq_add_sq`, `UndergradKB.Trigonometry.tan_eq_im_div_re`
- **Theorem 11.8 p.952**, p.952 [PC-252]: The polar graph $r=a$ ($a\ne0$) is the circle of radius $\lvert a\rvert$ about the origin; $\theta=\alpha$ is the line through the origin at angle $\alpha$ — *proved proved here* — `UndergradKB.Precalculus.polarPoint`, `UndergradKB.Precalculus.polarGraphRadius`, `UndergradKB.Precalculus.polarGraphAngle`, `UndergradKB.Precalculus.polar_graph_circle_and_line`

#### Section 11.5

- **Example 11.5.3 p.963**, p.963 [PC-253]: Recipe for intersections of polar graphs: check the pole, then solve with $\theta+2\pi k$ substituted in one equation and with $(-r,\theta+(2k+1)\pi)$ substituted in one equation — *proved proved here* — `UndergradKB.Precalculus.polar_point_same_names`
- **§11.5 p.967**, p.967 [PC-253]: Recipe for intersections of polar graphs: check the pole, then solve with $\theta+2\pi k$ substituted in one equation and with $(-r,\theta+(2k+1)\pi)$ substituted in one equation — *proved proved here* — `UndergradKB.Precalculus.polar_point_same_names`
- **Theorem 11.9 p.986**, p.986 [PC-254]: Rotating axes counterclockwise by $\theta$: $x=x'\cos\theta-y'\sin\theta$, $y=x'\sin\theta+y'\cos\theta$ and the inverse system — *proved proved here* — `UndergradKB.Precalculus.rotation_coordinates`, `UndergradKB.Precalculus.rotation_preserves_norm_sq`
- **Theorem 11.10 p.989**, p.989 [PC-255]: $Ax^2+Bxy+Cy^2+Dx+Ey+F=0$ with $B\ne0$ loses its $x'y'$ term after rotating by $\theta$ with $\cot 2\theta=(A-C)/B$ — *proved proved here* — `UndergradKB.Precalculus.quadForm_rotate`, `UndergradKB.Precalculus.rotB_eq`, `UndergradKB.Precalculus.rotB_eq_zero_of_cot`, `UndergradKB.Precalculus.exists_rotation_eliminating_xy`
- **Theorem 11.11 p.991**, p.991 [PC-256]: Discriminant test: for a non-degenerate conic, $B^2-4AC>0$ hyperbola, $=0$ parabola, $<0$ ellipse or circle — *proved proved here* — `UndergradKB.Precalculus.discriminant_test`, `UndergradKB.Precalculus.discriminant_rotation_invariant`, `UndergradKB.Precalculus.conic_central_form`, `UndergradKB.Precalculus.conic_central_signs`
- **Definition 11.1 p.993**, p.993 [PC-257]: Conic section (focus-directrix-eccentricity): points whose distance to focus $F$ is $e$ times the distance to line $L$ — *proved proved here* — `UndergradKB.Precalculus.IsConicPt`, `UndergradKB.Precalculus.conic_pt_iff`, `UndergradKB.Precalculus.conic_pt_one_iff_parabola`
- **Theorem 11.12 p.995**, p.995 [PC-258]: Polar equations $r=ed/(1\pm e\cos\theta)$ and $r=ed/(1\pm e\sin\theta)$ are conics with directrix $x=\mp d$, $x=d$, $y=\mp d$, $y=d$ and focus at the pole — *proved proved here* — `UndergradKB.Precalculus.polar_conic_cos_minus`, `UndergradKB.Precalculus.polar_conic_cos_plus`, `UndergradKB.Precalculus.polar_conic_sin_minus`, `UndergradKB.Precalculus.polar_conic_sin_plus`
- **Theorem 11.13 p.997**, p.997 [PC-259]: The graph of $r=\ell/(1-e\cos(\theta-\varphi))$ is a conic with eccentricity $e$ and focus at the pole (circle of radius $\ell$ if $e=0$) — *proved proved here* — `UndergradKB.Precalculus.polar_conic_rotated`, `UndergradKB.Precalculus.polar_conic_rotated_converse`
- **Definition 11.2 p.1003**, p.1003 [PC-260]: Modulus $\lvert z\rvert$ is the polar radius of $(\mathrm{Re}\,z,\mathrm{Im}\,z)$; arguments are its polar angles; $\mathrm{Arg}\,z\in(-\pi,\pi]$ is the principal one — *proved proved here* — `UndergradKB.Precalculus.complexArgs`, `UndergradKB.Precalculus.complex_modulus_arguments`
- **Theorem 11.14 p.1005**, p.1005 [PC-261]: Modulus properties: distance to 0, $\lvert z\rvert\ge0$ with equality iff $z=0$, $\sqrt{(\mathrm{Re}\,z)^2+(\mathrm{Im}\,z)^2}$, and $\lvert zw\rvert=\lvert z\rvert\lvert w\rvert$, $\lvert z^n\rvert=\lvert z\rvert^n$, $\lvert z/w\rvert=\lvert z\rvert/\lvert w\rvert$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_14_modulus`, `Complex.norm_def`, `norm_nonneg`, `norm_eq_zero`
- **Definition 11.3 p.1007**, p.1007 [PC-263]: Polar form of $z$: $\lvert z\rvert\,\mathrm{cis}\,\theta=\lvert z\rvert(\cos\theta+i\sin\theta)$ for an argument $\theta$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_3_polar_form`, `Complex.norm_mul_cos_add_sin_mul_I`, `Complex.norm_mul_exp_arg_mul_I`
- **Theorem 11.15 p.1007**, p.1007 [PC-262]: Arguments: $\tan\theta=\mathrm{Im}\,z/\mathrm{Re}\,z$ if $\mathrm{Re}\,z\ne0$; if $\mathrm{Re}\,z=0$ the arguments are $\pi/2+2\pi k$ (Im>0) or $-\pi/2+2\pi k$ (Im<0); all reals for $z=0$ — *proved proved here* — `UndergradKB.Precalculus.complex_arguments_cases`
- **Theorem 11.16 p.1009**, p.1009 [PC-264]: Product in polar form: $zw=\lvert z\rvert\lvert w\rvert\,\mathrm{cis}(\alpha+\beta)$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_16_product_polar`, `UndergradKB.Trigonometry.cis_mul_cis`, `UndergradKB.Trigonometry.cis_mul_cis'`
- **Theorem 11.16 p.1009**, p.1009 [PC-265]: De Moivre: $z^n=\lvert z\rvert^n\,\mathrm{cis}(n\theta)$ for natural $n$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_16_de_moivre`, `UndergradKB.Trigonometry.de_moivre`, `UndergradKB.Trigonometry.de_moivre_nat`
- **Theorem 11.16 p.1009**, p.1009 [PC-266]: Quotient in polar form: $z/w=(\lvert z\rvert/\lvert w\rvert)\,\mathrm{cis}(\alpha-\beta)$ for $w\ne0$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_16_quotient_polar`, `UndergradKB.Trigonometry.cis_div_cis`, `UndergradKB.Trigonometry.cis_div_cis'`

#### Section 11.7

- **Example 11.7.3 p.1011**, p.1011 [PC-264]: Product in polar form: $zw=\lvert z\rvert\lvert w\rvert\,\mathrm{cis}(\alpha+\beta)$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_16_product_polar`, `UndergradKB.Trigonometry.cis_mul_cis`, `UndergradKB.Trigonometry.cis_mul_cis'`
- **Definition 11.4 p.1012**, p.1012 [PC-267]: An $n$th root of $z$ is any $w$ with $w^n=z$ (no principal choice) — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_4_nth_root`, `Polynomial.nthRoots`, `Polynomial.mem_nthRoots`
- **Theorem 11.17 p.1013**, p.1013 [PC-268]: A nonzero $z=r\,\mathrm{cis}\,\theta$ has exactly $n$ distinct $n$th roots $\sqrt[n]{r}\,\mathrm{cis}(\theta/n+2\pi k/n)$, $k=0..n-1$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_17_explicit_roots`, `UndergradKB.Precalculus.Course.thm_11_17_number_of_roots`, `UndergradKB.Trigonometry.nthRoots_eq_image`, `UndergradKB.Trigonometry.nthRootPolar`
- **Example 11.7.4 p.1014**, p.1014 [PC-268]: A nonzero $z=r\,\mathrm{cis}\,\theta$ has exactly $n$ distinct $n$th roots $\sqrt[n]{r}\,\mathrm{cis}(\theta/n+2\pi k/n)$, $k=0..n-1$ — *proved proved here* — `UndergradKB.Precalculus.Course.thm_11_17_explicit_roots`, `UndergradKB.Precalculus.Course.thm_11_17_number_of_roots`, `UndergradKB.Trigonometry.nthRoots_eq_image`, `UndergradKB.Trigonometry.nthRootPolar`
- **§11.7 p.1018**, p.1018 [PC-269]: The $n$th roots of unity are the $n$ solutions of $z^n=1$ (the $n$th roots of 1) — *in Mathlib* — `UndergradKB.Precalculus.Course.box_11_7_roots_of_unity`, `rootsOfUnity`, `Complex.mem_rootsOfUnity`, `Complex.card_rootsOfUnity`
- **Definition 11.5 p.1025**, p.1025 [PC-270]: Component form of the vector from $P(x_0,y_0)$ to $Q(x_1,y_1)$ is $\langle x_1-x_0,y_1-y_0\rangle$; vectors are equal iff components are — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_5_component_form`
- **Definition 11.6 p.1026**, p.1026 [PC-271]: Vector sum is componentwise: $\langle v_1,v_2\rangle+\langle w_1,w_2\rangle=\langle v_1+w_1,v_2+w_2\rangle$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_6_vector_sum`
- **Theorem 11.18 p.1027**, p.1027 [PC-272]: Vector addition is commutative and associative, $\vec0$ is an identity, $\vec v+(-\vec v)=\vec0$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_18_vector_addition`, `add_comm`, `add_assoc`, `add_zero`
- **Definition 11.7 p.1029**, p.1029 [PC-273]: Scalar multiple: $k\langle v_1,v_2\rangle=\langle kv_1,kv_2\rangle$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_7_scalar_multiple`
- **Theorem 11.19 p.1030**, p.1030 [PC-274]: Scalar multiplication: $(kr)\vec v=k(r\vec v)$, $1\vec v=\vec v$, $-\vec v=(-1)\vec v$, $(k+r)\vec v=k\vec v+r\vec v$, $k(\vec v+\vec w)=k\vec v+k\vec w$, $0\vec v=\vec 0$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_19_scalar_multiplication`, `mul_smul`, `one_smul`, `neg_one_smul`
- **Definition 11.8 p.1032**, p.1032 [PC-275]: Magnitude $\lVert\vec v\rVert=\sqrt{v_1^2+v_2^2}$ and direction $\hat v=\langle\cos\theta,\sin\theta\rangle$ for $(r,\theta)$ polar of $(v_1,v_2)$; $\vec v=\lVert\vec v\rVert\langle\cos\theta,\sin\theta\rangle$ — *proved proved here* — `UndergradKB.Precalculus.dotProd2`, `UndergradKB.Precalculus.vecMag`, `UndergradKB.Precalculus.vector_magnitude_direction`
- **Theorem 11.20 p.1032**, p.1032 [PC-276]: $\lVert\vec v\rVert\ge0$ with equality iff $\vec v=\vec0$; $\lVert k\vec v\rVert=\lvert k\rvert\lVert\vec v\rVert$; $\vec v=\lVert\vec v\rVert\hat v$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_20_magnitude`, `norm_nonneg`, `norm_eq_zero`, `norm_smul`

#### Section 11.8

- **Example 11.8.4 p.1033**, p.1033 [PC-275]: Magnitude $\lVert\vec v\rVert=\sqrt{v_1^2+v_2^2}$ and direction $\hat v=\langle\cos\theta,\sin\theta\rangle$ for $(r,\theta)$ polar of $(v_1,v_2)$; $\vec v=\lVert\vec v\rVert\langle\cos\theta,\sin\theta\rangle$ — *proved proved here* — `UndergradKB.Precalculus.dotProd2`, `UndergradKB.Precalculus.vecMag`, `UndergradKB.Precalculus.vector_magnitude_direction`
- **Example 11.8.5 p.1034**, p.1034 [PC-277]: A unit vector is one of norm 1; normalizing $\vec v/\lVert\vec v\rVert$ gives a unit vector — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_9_unit_vector`, `norm_smul_inv_norm`, `NormedSpace.normalize`
- **Definition 11.9 p.1035**, p.1035 [PC-277]: A unit vector is one of norm 1; normalizing $\vec v/\lVert\vec v\rVert$ gives a unit vector — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_9_unit_vector`, `norm_smul_inv_norm`, `NormedSpace.normalize`
- **Definition 11.10 p.1036**, p.1036 [PC-278]: Principal unit vectors $\hat\imath=\langle1,0\rangle$ and $\hat\jmath=\langle0,1\rangle$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_10_principal_unit_vectors`, `EuclideanSpace.single`
- **Theorem 11.21 p.1036**, p.1036 [PC-279]: Principal decomposition: $\vec v=v_1\hat\imath+v_2\hat\jmath$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_21_principal_decomposition`, `OrthonormalBasis.sum_repr`, `EuclideanSpace.basisFun`
- **Example 11.8.6 p.1037**, p.1037 [PC-279]: Principal decomposition: $\vec v=v_1\hat\imath+v_2\hat\jmath$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_21_principal_decomposition`, `OrthonormalBasis.sum_repr`, `EuclideanSpace.basisFun`
- **Definition 11.11 p.1046**, p.1046 [PC-280]: Dot product $\langle v_1,v_2\rangle\cdot\langle w_1,w_2\rangle=v_1w_1+v_2w_2$ — *in Mathlib* — `UndergradKB.Precalculus.Course.def_11_11_dot_product`, `EuclideanSpace.inner_eq_star_dotProduct`, `PiLp.inner_apply`
- **Theorem 11.22 p.1046**, p.1046 [PC-281]: Dot product is commutative, distributive over sum, $(k\vec v)\cdot\vec w=k(\vec v\cdot\vec w)$, $\vec v\cdot\vec v=\lVert\vec v\rVert^2$, $\vec0\cdot\vec v=0$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_22_dot_product_properties`, `real_inner_comm`, `inner_add_right`, `inner_add_left`

#### Section 11.9

- **Example 11.9.1 p.1047**, p.1047 [PC-282]: $\lVert\vec v-\vec w\rVert^2=\lVert\vec v\rVert^2-2\,\vec v\cdot\vec w+\lVert\vec w\rVert^2$ — *in Mathlib* — `UndergradKB.Precalculus.Course.ex_11_9_1_norm_sub_sq`, `norm_sub_sq_real`
- **Theorem 11.23 p.1047**, p.1047 [PC-283]: $\vec v\cdot\vec w=\lVert\vec v\rVert\lVert\vec w\rVert\cos\theta$ for nonzero vectors with angle $\theta$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_23_dot_product_angle`, `InnerProductGeometry.cos_angle_mul_norm_mul_norm`
- **Example 11.9.2 p.1048**, p.1048 [PC-284]: Angle between nonzero vectors is $\arccos\big(\vec v\cdot\vec w/(\lVert\vec v\rVert\lVert\vec w\rVert)\big)=\arccos(\hat v\cdot\hat w)$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_24_angle_between_vectors`, `InnerProductGeometry.angle`
- **Theorem 11.24 p.1048**, p.1048 [PC-284]: Angle between nonzero vectors is $\arccos\big(\vec v\cdot\vec w/(\lVert\vec v\rVert\lVert\vec w\rVert)\big)=\arccos(\hat v\cdot\hat w)$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_24_angle_between_vectors`, `InnerProductGeometry.angle`
- **Example 11.9.3 p.1049**, p.1049 [PC-286]: Lines $y=m_1x+b_1$, $y=m_2x+b_2$ are perpendicular iff $m_1m_2=-1$ — *proved proved here* — `UndergradKB.Precalculus.perpendicular_slopes_iff`
- **Theorem 11.25 p.1049**, p.1049 [PC-285]: For nonzero vectors, $\vec v\perp\vec w$ iff $\vec v\cdot\vec w=0$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_25_orthogonal_iff_dot_zero`, `InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two`
- **Example 11.9.4 p.1051**, p.1051 [PC-288]: $\mathrm{proj}_{\vec w}\vec v=\dfrac{\vec v\cdot\vec w}{\lVert\vec w\rVert^2}\vec w$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_26_projection`, `Submodule.starProjection_singleton`
- **Definition 11.12 p.1051**, p.1051 [PC-287]: Orthogonal projection of $\vec v$ onto $\vec w$ is $(\vec v\cdot\hat w)\hat w$ — *proved proved here* — `UndergradKB.Precalculus.vecProj`, `UndergradKB.Precalculus.vecProj_eq_unit_form`
- **Theorem 11.26 p.1051**, p.1051 [PC-288]: $\mathrm{proj}_{\vec w}\vec v=\dfrac{\vec v\cdot\vec w}{\lVert\vec w\rVert^2}\vec w$ — *in Mathlib* — `UndergradKB.Precalculus.Course.thm_11_26_projection`, `Submodule.starProjection_singleton`
- **Theorem 11.27 p.1052**, p.1052 [PC-289]: Every $\vec v$ splits uniquely as $\vec p+\vec q$ with $\vec p$ a multiple of $\vec w\ne0$ and $\vec q\cdot\vec w=0$ — *proved proved here* — `UndergradKB.Precalculus.vector_decomposition_unique`
- **Example 11.9.5 p.1054**, p.1054 [PC-290]: Work of a constant force $\vec F$ along $\overrightarrow{PQ}$ is $W=\vec F\cdot\overrightarrow{PQ}=\lVert\vec F\rVert\lVert\overrightarrow{PQ}\rVert\cos\theta$ — *proved proved here* — `UndergradKB.Precalculus.workDone`, `UndergradKB.Precalculus.work_eq_norm_mul_norm_mul_cos`
- **Theorem 11.28 p.1054**, p.1054 [PC-290]: Work of a constant force $\vec F$ along $\overrightarrow{PQ}$ is $W=\vec F\cdot\overrightarrow{PQ}=\lVert\vec F\rVert\lVert\overrightarrow{PQ}\rVert\cos\theta$ — *proved proved here* — `UndergradKB.Precalculus.workDone`, `UndergradKB.Precalculus.work_eq_norm_mul_norm_mul_cos`

#### Section 11.10

- **§11.10 p.1060**, p.1060 [PC-291]: A curve is parametrized by $x=f(t)$, $y=g(t)$, the parameter $t$ giving an orientation; $x=r\cos\omega t$, $y=r\sin\omega t$ traces a circle counterclockwise for $\omega>0$ — *proved proved here* — `UndergradKB.Precalculus.circleParam`, `UndergradKB.Precalculus.circle_param_counterclockwise`
- **§11.10 p.1065**, p.1065 [PC-292]: Standard parametrizations: graph $y=f(x)$ by $x=t,y=f(t)$; $x=g(y)$ by $x=g(t),y=t$; segment $P\to Q$ by $P+t(Q-P)$, $0\le t\le1$; ellipse $x=h+a\cos t,\ y=k+b\sin t$ — *proved proved here* — `UndergradKB.Precalculus.standard_parametrizations`
- **Example 11.10.3 p.1065**, p.1065 [PC-292]: Standard parametrizations: graph $y=f(x)$ by $x=t,y=f(t)$; $x=g(y)$ by $x=g(t),y=t$; segment $P\to Q$ by $P+t(Q-P)$, $0\le t\le1$; ellipse $x=h+a\cos t,\ y=k+b\sin t$ — *proved proved here* — `UndergradKB.Precalculus.standard_parametrizations`
- **§11.10 p.1066**, p.1066 [PC-293]: Replacing $t$ by $-t$ reverses orientation; replacing $t$ by $t-c$ shifts the parameter start by $c$ — *proved proved here* — `UndergradKB.Precalculus.reparametrization_reverse_shift`
- **Example 11.10.4 p.1067**, p.1067 [PC-293]: Replacing $t$ by $-t$ reverses orientation; replacing $t$ by $t-c$ shifts the parameter start by $c$ — *proved proved here* — `UndergradKB.Precalculus.reparametrization_reverse_shift`
- **Example 11.10.5 p.1069**, p.1069 [PC-294]: Cycloid of a circle of radius $r$ rolling on the $x$-axis: $x=r(t-\sin t)$, $y=r(1-\cos t)$ — *proved proved here* — `UndergradKB.Precalculus.cycloid`, `UndergradKB.Precalculus.cycloid_on_rolling_circle`
