# ReasBook: what this library takes from it, and how it was checked

The real analysis topic follows J. Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I* (version 6.3,
2026). Much of that book is already formalized in **ReasBook** ([optpku/ReasBook](https://github.com/optpku/ReasBook),
Apache License 2.0; the formalization of Lebl's book there is by Zichen Wang and Zaiwen Wen, following version 6.2,
whose numbering agrees with version 6.3 in the chapters used). This library does not redo that work. Each row of the
real analysis map ([`docs/books/lebl2026.md`](books/lebl2026.md)) is one of three kinds besides the Mathlib rows:

* **proved here**: proved in this library, by our own code (for example the Riemann rearrangement theorem for the
  alternating harmonic series, the two forms of the fundamental theorem of calculus for the Darboux integral, and the
  agreement of the Darboux integral with Mathlib's interval integral);
* **ported from ReasBook** (trust level A): the Darboux sums and the Riemann integral of Lebl's sections 5.1 and 5.2,
  copied from ReasBook at commit `35bcb693144a4cb67108bac1793b5ffbfea0acd9` into
  `UndergradKB/RealAnalysis/Darboux*.lean` and adapted (specific Mathlib imports, our namespace, repairs for the Lean
  and Mathlib versions of this library). Each file's header names the original file and lines; `NOTICE` lists them.
  This library's build, its axiom check and `lake comparator` see this code like any other;
* **cited from ReasBook** (trust level B): proved in ReasBook at the same commit and cited by declaration name, not
  built here (ReasBook is pinned to Lean v4.30.0 and an older Mathlib). For every cited name we checked, at that
  commit, that the declaration exists and its module builds, that it depends only on the axioms `propext`,
  `Classical.choice` and `Quot.sound` (no `sorry`), and that Lean's kernel checker (`leanchecker`) replays its module.
  The independent kernels (NanoDa, con-ron) were not run on ReasBook.

The names cited from ReasBook (141 distinct names, module paths relative to the ReasBook library
`IntroductiontoRealAnalysisVolumeI_JiriLebl_2025`):

| name | module | builds | axioms | replay | note |
|---|---|---|---|---|---|
| ImproperIntegralAtTop | Chap05.section05 | yes | standard three | pass | cited by RA-295 |
| ImproperIntegralAtTopConverges | Chap05.section05 | yes | standard three | pass | cited by RA-295 |
| ImproperIntegralOpenInterval | Chap05.section05 | yes | standard three | pass | cited by RA-300 |
| ImproperIntegralRealLine | Chap05.section05 | yes | standard three | pass | cited by RA-300 |
| ImproperIntegralRight | Chap05.section05 | yes | standard three | pass | cited by RA-295 |
| ImproperIntegralRightConverges | Chap05.section05 | yes | standard three | pass | cited by RA-295 |
| IntervalPartition | Chap05.section01 | yes | standard three | pass | cited by RA-258 |
| IntervalPartition.IsRefinement | Chap05.section01 | yes | standard three | pass | cited by RA-262 |
| RiemannIntegrableOn | Chap05.section01 | yes | standard three | pass | cited by RA-265 |
| SeriesAbsolutelyConvergent | Chap02.section05 | yes | standard three | pass | cited by RA-140 |
| SeriesCauchy | Chap02.section05 | yes | standard three | pass | cited by RA-131 |
| SeriesConditionallyConvergent | Chap02.section05 | yes | standard three | pass | cited by RA-140 |
| abs_convergentSequence | Chap02.section02 | yes | standard three | pass | cited by RA-105 |
| alternatingZeroOne_subsequences_converge | Chap02.section01 | yes | standard three | pass | cited by RA-096 |
| alternating_harmonic_conditional | Chap02.section06 | yes | standard three | pass | cited by RA-143 |
| alternating_signs_diverges | Chap02.section01 | yes | standard three | pass | cited by RA-085 |
| book_clusterPoint_atBot | Chap03.section05 | yes | standard three | pass | cited by RA-211 |
| book_clusterPoint_atTop | Chap03.section05 | yes | standard three | pass | cited by RA-211 |
| book_clusterPoint_atTop_iff_not_bddAbove | Chap03.section05 | yes | standard three | pass | cited by RA-211 |
| book_lipschitzOn_sqrt_Ici_one | Chap03.section04 | yes | standard three | pass | cited by RA-210 |
| cauchy_product_conditional_diverges | Chap02.section06 | yes | standard three | pass | cited by RA-155 |
| clusterPoint_iff_of_local_agree | Chap03.section01 | yes | standard three | pass | cited by RA-177 |
| complex_not_linearOrderedField | Chap01.section01 | yes | standard three | pass | cited by RA-049 |
| continuousAt_complex_iff_real_im | Chap07.section05 | yes | standard three | pass | cited by RA-413 |
| converges_iff_convergent_subsequences_converge | Chap02.section03 | yes | standard three | pass | cited by RA-119 |
| converges_of_abs_sub_le_converging_to_zero | Chap02.section02 | yes | standard three | pass | cited by RA-106 |
| darbouxIntegral_add | Chap05.section02_part2 | yes | standard three | pass | cited by RA-270 |
| darbouxIntegral_add_le_add | Chap05.section02_part3 | yes | standard three | pass | cited by RA-274 |
| decimalBounds | Chap01.section05 | yes | standard three | pass | cited by RA-076 |
| decimalBoundsStrict | Chap01.section05 | yes | standard three | pass | cited by RA-076 |
| decimalBoundsStrict_digits_unique | Chap01.section05 | yes | standard three | pass | cited by RA-078 |
| decimalBounds_value_unique | Chap01.section05 | yes | standard three | pass | cited by RA-077 |
| decimalPrefix | Chap01.section05 | yes | standard three | pass | cited by RA-076 |
| decimalWithIncreasingZeroBlocks_bounds | Chap01.section05 | yes | standard three | pass | cited by RA-081 |
| decimal_expansion_properties | Chap01.section05 | yes | standard three | pass | cited by RA-077, RA-078 |
| deriv_oscillatorySquared_at_zero | Chap04.section02 | yes | standard three | pass | cited by RA-245 |
| deriv_oscillatorySquared_not_continuous_at_zero | Chap04.section02 | yes | standard three | pass | cited by RA-245 |
| deriv_oscillatorySquared_sign_changes | Chap04.section02 | yes | standard three | pass | cited by RA-245 |
| deriv_powerSeries_eq_series | Chap06.section02 | yes | standard three | pass | cited by RA-328 |
| differentiable_oscillatorySquared | Chap04.section02 | yes | standard three | pass | cited by RA-245 |
| dirichletFunction_lower_integral | Chap05.section01 | yes | standard three | pass | cited by RA-261 |
| dirichletFunction_upper_integral | Chap05.section01 | yes | standard three | pass | cited by RA-261 |
| discreteMetric_closed_and_bounded | Chap07.section04 | yes | standard three | pass | cited by RA-403 |
| discreteMetric_complete | Chap07.section04 | yes | standard three | pass | cited by RA-403 |
| discreteMetric_lebesgue_covering | Chap07.section04 | yes | standard three | pass | cited by RA-405 |
| evenNaturals_sameCardinality_nat | Chap00.section03_part5 | yes | standard three | pass | cited by RA-032 |
| example6_2_1_limit_not_continuous | Chap06.section02 | yes | standard three | pass | cited by RA-317 |
| example6_2_3_integral_limit_ne_limit_integral | Chap06.section02 | yes | standard three | pass | cited by RA-319 |
| example6_2_6_dirichlet_not_riemann_integrable | Chap06.section02 | yes | standard three | pass | cited by RA-321 |
| example6_2_7_limit_unbounded | Chap06.section02 | yes | standard three | pass | cited by RA-322 |
| example6_2_8_deriv_not_tendsto_at_pi | Chap06.section02 | yes | standard three | pass | cited by RA-323 |
| example6_2_8_uniform_tendsto_zero | Chap06.section02 | yes | standard three | pass | cited by RA-323 |
| example6_2_9_deriv_not_uniform | Chap06.section02 | yes | standard three | pass | cited by RA-324 |
| example6_2_9_limit_not_differentiable | Chap06.section02 | yes | standard three | pass | cited by RA-324 |
| example_3_2_10 | Chap03.section02 | yes | standard three | pass | cited by RA-188 |
| example_3_2_11 | Chap03.section02 | yes | standard three | pass | cited by RA-189 |
| example_3_3_12 | Chap03.section03 | yes | standard three | pass | cited by RA-199 |
| example_3_6_5 | Chap03.section06 | yes | standard three | pass | cited by RA-221 |
| example_3_6_7 | Chap03.section06 | yes | standard three | pass | cited by RA-224 |
| exists_digits_decimalBoundsStrict | Chap01.section05 | yes | standard three | pass | cited by RA-078 |
| exists_nonconvergent_sin_nat_mul | Chap06.section01 | yes | standard three | pass | cited by RA-308 |
| exists_sup_decimalBounds | Chap01.section05 | yes | standard three | pass | cited by RA-077 |
| harmonic_partial_sums_unbounded | Chap02.section01 | yes | standard three | pass | cited by RA-090 |
| harmonic_power_series_behavior | Chap02.section06 | yes | standard three | pass | cited by RA-158 |
| improperIntegral_comparison | Chap05.section05 | yes | standard three | pass | cited by RA-299 |
| improperIntegral_iterated_limits_symm | Chap05.section05 | yes | standard three | pass | cited by RA-301 |
| improperIntegral_nonneg_sup_and_seq | Chap05.section05 | yes | standard three | pass | cited by RA-298 |
| improperIntegral_sign_diverges_but_symmetric_zero | Chap05.section05 | yes | standard three | pass | cited by RA-302 |
| improperIntegral_sinc_conditional | Chap05.section05 | yes | standard three | pass | cited by RA-303 |
| improperIntegral_tail_convergence | Chap05.section05 | yes | standard three | pass | cited by RA-297 |
| improperIntegral_tail_value | Chap05.section05 | yes | standard three | pass | cited by RA-297 |
| inf_nat_inv_eq_zero | Chap01.section02 | yes | standard three | pass | cited by RA-058 |
| infimum_exists_of_bddBelow | Chap01.section01 | yes | standard three | pass | cited by RA-050 |
| integral_powerSeries_eq_series | Chap06.section02 | yes | standard three | pass | cited by RA-327 |
| intervalIntegral_continuous_on_rectangle | Chap07.section05 | yes | standard three | pass | cited by RA-421 |
| irrational_decimalWithIncreasingZeroBlocks | Chap01.section05 | yes | standard three | pass | cited by RA-081 |
| limitWithin_abs | Chap03.section01 | yes | standard three | pass | cited by RA-175 |
| limitWithin_iff_of_local_agree | Chap03.section01 | yes | standard three | pass | cited by RA-178 |
| limitWithin_imp_of_local_agree | Chap03.section01 | yes | standard three | pass | cited by RA-178 |
| limit_abs_of_convergent | Chap02.section02 | yes | standard three | pass | cited by RA-105 |
| limit_mul_sin_inv | Chap03.section01 | yes | standard three | pass | cited by RA-169 |
| limsup_liminf_subsequence_bounds | Chap02.section03 | yes | standard three | pass | cited by RA-118 |
| lowerDarbouxIntegral | Chap05.section01 | yes | standard three | pass | cited by RA-260 |
| lowerDarbouxSum | Chap05.section01 | yes | standard three | pass | cited by RA-258 |
| lower_upper_integral_bounds | Chap05.section01 | yes | standard three | pass | cited by RA-264 |
| lower_upper_sum_bounds | Chap05.section01 | yes | standard three | pass | cited by RA-259 |
| lower_upper_sum_refinement | Chap05.section01 | yes | standard three | pass | cited by RA-263 |
| metricClusterPoint_iff_mem_closure_diff | Chap07.section05 | yes | standard three | pass | cited by RA-426 |
| metric_picard_existence_uniqueness | Chap07.section06 | yes | standard three | pass | cited by RA-433 |
| no_solution_dirichlet_ode | Chap06.section03 | yes | standard three | pass | cited by RA-333 |
| not_book_lipschitzOn_sqrt_Ici_zero | Chap03.section04 | yes | standard three | pass | cited by RA-210 |
| not_uniformContinuous_inv_on_Ioo | Chap03.section04 | yes | standard three | pass | cited by RA-203 |
| not_uniformContinuous_sq | Chap03.section04 | yes | standard three | pass | cited by RA-202 |
| not_uniformConverges_pow_even_on_unit_interval | Chap06.section01 | yes | standard three | pass | cited by RA-311 |
| nth_root_sequence_converges_to_one | Chap02.section02 | yes | standard three | pass | cited by RA-112 |
| oscillatorySquared | Chap04.section02 | yes | standard three | pass | cited by RA-245 |
| pointwiseConverges_pow_even | Chap06.section01 | yes | standard three | pass | cited by RA-307 |
| popcorn_continuous_at_irrational | Chap03.section02 | yes | standard three | pass | cited by RA-190 |
| popcorn_discontinuous_at_rational | Chap03.section02 | yes | standard three | pass | cited by RA-190 |
| power_series_algebra | Chap02.section06 | yes | standard three | pass | cited by RA-163 |
| power_series_nn_pow_diverges | Chap02.section06 | yes | standard three | pass | cited by RA-159 |
| power_series_real_radius | Chap02.section06 | yes | standard three | pass | cited by RA-160 |
| proposition_3_6_6 | Chap03.section06 | yes | standard three | pass | cited by RA-223 |
| quadratic_ode_example | Chap06.section03 | yes | standard three | pass | cited by RA-331 |
| ratPairRel_equivalence | Chap00.section03_part4 | yes | standard three | pass | cited by RA-023 |
| rat_sq_lt_two_has_no_sup | Chap01.section01 | yes | standard three | pass | cited by RA-044 |
| ratio_test_for_sequences | Chap02.section02 | yes | standard three | pass | cited by RA-109, RA-110 |
| rational_decimal_digits_eventually_periodic | Chap01.section05 | yes | standard three | pass | cited by RA-080 |
| rational_sq_eq_two_absurd | Chap01.section01 | yes | standard three | pass | cited by RA-044 |
| real_le_zero_of_le_pos | Chap01.section02 | yes | standard three | pass | cited by RA-052 |
| removableDiscontinuityExample_continuous_on_complement | Chap03.section02 | yes | standard three | pass | cited by RA-191 |
| removableDiscontinuityExample_limit | Chap03.section02 | yes | standard three | pass | cited by RA-191 |
| removableDiscontinuityExample_not_continuous_at_zero | Chap03.section02 | yes | standard three | pass | cited by RA-191 |
| removableDiscontinuityExample_restrict_singleton | Chap03.section02 | yes | standard three | pass | cited by RA-191 |
| riemannIntegrableFunctions | Chap05.section01 | yes | standard three | pass | cited by RA-265 |
| riemannIntegrableOn_of_finite_discontinuities | Chap05.section02_part4 | yes | standard three | pass | cited by RA-278 |
| riemannIntegrable_of_upper_lower_gap | Chap05.section01 | yes | standard three | pass | cited by RA-268 |
| riemannIntegral | Chap05.section01 | yes | standard three | pass | cited by RA-265 |
| riemannIntegral_bounds | Chap05.section01 | yes | standard three | pass | cited by RA-266 |
| riemannIntegral_eq_of_eq_off_finite | Chap05.section02_part6 | yes | standard three | pass | cited by RA-279 |
| riemannIntegral_tendsto_of_nested_intervals | Chap05.section02_part4 | yes | standard three | pass | cited by RA-277 |
| root_test_abs_converges | Chap02.section06 | yes | standard three | pass | cited by RA-148 |
| root_test_diverges | Chap02.section06 | yes | standard three | pass | cited by RA-148 |
| second_derivative_test | Chap04.section03 | yes | standard three | pass | cited by RA-252 |
| sequenceTail | Chap02.section01 | yes | standard three | pass | cited by RA-092 |
| series_cauchy_iff_tail_norm_small | Chap02.section05 | yes | standard three | pass | cited by RA-132 |
| sin_inv_no_limit | Chap03.section01 | yes | standard three | pass | cited by RA-169 |
| sinc | Chap05.section05 | yes | standard three | pass | cited by RA-303 |
| sqrt_abs_ode_nonunique | Chap06.section03 | yes | standard three | pass | cited by RA-332 |
| sqrt_not_Lipschitz_on_Icc | Chap07.section05 | yes | standard three | pass | cited by RA-424 |
| sqrt_uniformContinuous_on_Icc | Chap07.section05 | yes | standard three | pass | cited by RA-424 |
| subsequence_converging_to_limsup_liminf | Chap02.section03 | yes | standard three | pass | cited by RA-116 |
| sup_le_inf_of_forall_le | Chap01.section02 | yes | standard three | pass | cited by RA-060 |
| uniformContinuousOn_Ioo_iff_limits_extend | Chap03.section04 | yes | standard three | pass | cited by RA-206 |
| uniformContinuous_sq_on_Icc | Chap03.section04 | yes | standard three | pass | cited by RA-202 |
| uniformContinuous_sqrt_Ici_zero | Chap03.section04 | yes | standard three | pass | cited by RA-210 |
| uniformConverges_iff_uniformNormOn_tendsto_zero | Chap06.section01 | yes | standard three | pass | cited by RA-313 |
| uniformConverges_nat_mul_add_sin_div_nat | Chap06.section01 | yes | standard three | pass | cited by RA-314 |
| uniformConverges_pow_even_on_subinterval | Chap06.section01 | yes | standard three | pass | cited by RA-311 |
| upperDarbouxIntegral | Chap05.section01 | yes | standard three | pass | cited by RA-260 |
| upperDarbouxSum | Chap05.section01 | yes | standard three | pass | cited by RA-258 |
