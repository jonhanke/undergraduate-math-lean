# Course outline: Hammack (foundations)

Generated from [`docs/coverage/foundations/checklist.md`](../../coverage/foundations/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build Foundations` builds this topic.

360 items in 14 chapters; 324 with a Lean name (90.0%).

## Chapter 1

39 items; 33 with a Lean name; 17 proved proved here; 16 in Mathlib; 6 not a result.


#### Section 1.1

- **Def §1.1**, p.15 [FO-001]: A set is a collection of elements; membership relation; sets are finite or infinite — *proved proved here* — `UndergradKB.Foundations.set_membership_finite_infinite`
- **Def §1.1**, p.15 [FO-002]: Two sets are equal iff they have the same elements (order and repetition irrelevant) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_set_ext`, `Set.ext`
- **Def §1.1**, p.16 [FO-004]: Standard number-system sets N, Z, Q, R and conventions (Hammack N starts at 1, Levin N starts at 0) — *not a result* — –
- **Def §1.1**, p.16 [FO-005]: Cardinality of a finite set is its number of elements; the empty set is the only set of cardinality 0 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_card_eq_zero`, `Finset.card`, `Set.ncard`
- **Def §1.1**, p.16 [FO-006]: The empty set has no elements; the empty set differs from the set containing the empty set — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_empty_ne_singleton_empty`, `Set.singleton_ne_empty`, `Set.eq_empty_iff_forall_notMem`
- **Def §1.1**, p.17 [FO-003]: Set-builder notation {expr : rule} describes a set by a membership condition — *not a result* — –
- **Example 1.1**, p.17 [FO-003]: Set-builder notation {expr : rule} describes a set by a membership condition — *not a result* — –
- **Def §1.1**, p.18 [FO-004]: Standard number-system sets N, Z, Q, R and conventions (Hammack N starts at 1, Levin N starts at 0) — *not a result* — –
- **Example 1.2**, p.18 [FO-364]: The set {7a + 3b : a, b integers} equals all of Z. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_1_2_seven_three_integers`
- **Def §1.1**, p.19 [FO-007]: Interval notation: closed, open, half-open and infinite intervals of R — *proved proved here* — `UndergradKB.Foundations.interval_notation`
- **Def 1.1**, p.20 [FO-008]: An ordered pair (x,y) is a list of two things; (a,b)=(c,d) iff componentwise equal — *proved proved here* — `UndergradKB.Foundations.ordered_pair_eq_iff`
- **Def 1.2**, p.20 [FO-009]: Cartesian product A x B = set of pairs (a,b) with a in A, b in B — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_2_mem_prod`, `Set.prod`, `Set.mem_prod`
- **Fact 1.1**, p.21 [FO-010]: Fact 1.1: for finite sets, \\|A x B\\| = \\|A\\| \\|B\\| — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_1_card_prod`, `Finset.card_product`, `Set.ncard_prod`, `Fintype.card_prod`
- **Example 1.3**, p.21 [FO-443]: The set of outcomes of two rolls of a six-sided die has 36 elements. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_1_3_dice_pairs`

#### Section 1.2

- **Def §1.2**, p.22 [FO-011]: Cartesian products of n sets and Cartesian powers A^n (n-tuples) — *proved proved here* — `UndergradKB.Foundations.cartesian_power`
- **Example 1.4**, p.23 [FO-011]: Cartesian products of n sets and Cartesian powers A^n (n-tuples) — *proved proved here* — `UndergradKB.Foundations.cartesian_power`
- **Fact 1.2**, p.24 [FO-014]: Fact 1.2: the empty set is a subset of every set — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_2_empty_subset`, `Set.empty_subset`
- **Def 1.3**, p.24 [FO-012]: A is a subset of B iff every element of A is in B; A is a subset of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_3_subset`, `Set.Subset`, `Set.subset_def`, `Set.Subset.refl`
- **Example 1.5**, p.24 [FO-012]: A is a subset of B iff every element of A is in B; A is a subset of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_3_subset`, `Set.Subset`, `Set.subset_def`, `Set.Subset.refl`
- **Fact 1.3**, p.25 [FO-015]: Fact 1.3 and Fact 1.4: a finite set with n elements has 2^n subsets, i.e. \\|P(A)\\| = 2^\\|A\\| — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_4_card_powerset`, `Finset.card_powerset`, `Set.ncard_powerset`
- **Fact 1.4**, p.27 [FO-015]: Fact 1.3 and Fact 1.4: a finite set with n elements has 2^n subsets, i.e. \\|P(A)\\| = 2^\\|A\\| — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_4_card_powerset`, `Finset.card_powerset`, `Set.ncard_powerset`
- **Def 1.4**, p.27 [FO-016]: Power set P(A) is the set of all subsets of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_4_mem_powerset`, `Set.powerset`, `Set.mem_powerset_iff`
- **Example 1.7**, p.28 [FO-444]: The power set of {0,1,3} is the list of its eight subsets. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_1_7_powerset_three`, `UndergradKB.Foundations.Course.hammack_ex_1_7_powerset_two`, `UndergradKB.Foundations.Course.hammack_ex_1_7_powerset_small`, `UndergradKB.Foundations.Course.hammack_ex_1_7_card_powerset`
- **Def 1.5**, p.30 [FO-017]: Union, intersection and difference of two sets — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_5_union_inter_diff`, `Set.union`, `Set.inter`, `Set.diff`
- **Def 1.5**, p.30 [FO-018]: Union and intersection are commutative; difference is not — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_5_comm`, `Set.union_comm`, `Set.inter_comm`
- **Example 1.8**, p.30 [FO-445]: Union, intersection, differences and symmetric difference of {a..e} and {d,e,f}. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_1_8_set_operations`, `UndergradKB.Foundations.Course.hammack_ex_1_8_with_numbers`, `UndergradKB.Foundations.Course.hammack_ex_1_8_products`
- **Def 1.6**, p.32 [FO-021]: Universal set U and complement of A defined as U - A — *proved proved here* — `UndergradKB.Foundations.complement_in_universe`

#### Section 1.7

- **Def §1.7**, p.34 [FO-023]: Venn diagrams as informal pictures of set operations — *not a result* — –
- **Sec 1.7**, p.35 [FO-019]: Union and intersection are associative, so parentheses may be dropped in iterated unions or intersections — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_7_assoc`, `Set.union_assoc`, `Set.inter_assoc`
- **Sec 1.7**, p.36 [FO-020]: Mixed union and intersection need parentheses: (A∪B)∩C and A∪(B∩C) differ in general — *not a result* — –
- **Def 1.7**, p.37 [FO-024]: Union and intersection of finitely many indexed sets A_1,...,A_n (sigma-style notation) — *proved proved here* — `UndergradKB.Foundations.mem_finite_indexed_union_inter`
- **Example 1.12**, p.37 [FO-446]: Indexed union of {0,2,5},{1,2,5},{2,5,7} is {0,1,2,5,7} and the intersection is {2,5}. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_1_12_indexed_union_inter`
- **Def 1.8**, p.38 [FO-025]: Union and intersection of an arbitrary family A_alpha, alpha in an index set I (I nonempty) — *proved proved here* — `UndergradKB.Foundations.mem_indexed_union_inter`
- **Example 1.13**, p.38 [FO-447]: For A_i={-i,0,i}, the union over i>=1 is Z and the intersection is {0}. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_1_13_union_inter_integers`
- **Fact 1.5**, p.42 [FO-027]: Fact 1.5, Division algorithm: for integers a, b with b > 0 there are unique integers q, r with a = qb + r and 0 <= r < b (proved from well-ordering) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_5_division_algorithm`, `Int.ediv_emod_unique''`
- **Sec 1.9**, p.42 [FO-026]: Well-ordering principle: every nonempty subset of {b, b+1, ...} has a least element (false for positive rationals/reals) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_9_well_ordering`, `Nat.find`, `Nat.find_spec`, `Nat.find_min`
- **Sec 1.9**, p.43 [FO-028]: Every natural number can be viewed as a set: 0 = empty set, n = {0,...,n-1} — *proved proved here* — `UndergradKB.Foundations.mem_vonNeumann`
- **Sec 1.10**, p.44 [FO-029]: Russell's paradox: the set of all sets not containing themselves is contradictory — *proved proved here* — `UndergradKB.Foundations.russell_paradox`, `UndergradKB.Foundations.russell_paradox_zfset`
- **Sec 1.10**, p.44 [FO-030]: Axiom of foundation: no nonempty set X is such that every element x meets X; in particular no set is a member of itself — *proved proved here* — `UndergradKB.Foundations.foundation`

## Chapter 2

42 items; 25 with a Lean name; 16 proved proved here; 9 in Mathlib; 17 not a result.


#### Section 2.1

- **Def §2.1**, p.47 [FO-031]: A statement is a sentence that is definitely true or definitely false — *not a result* — –
- **Def §2.1**, p.48 [FO-032]: Open sentence (predicate): a sentence whose truth depends on free variables — *not a result* — –

#### Section 2.2

- **Def §2.2**, p.51 [FO-034]: Definitions of conjunction, disjunction (inclusive or) and negation with their truth tables — *not a result* — –
- **Def §2.2**, p.52 [FO-034]: Definitions of conjunction, disjunction (inclusive or) and negation with their truth tables — *not a result* — –
- **Def §2.2**, p.53 [FO-034]: Definitions of conjunction, disjunction (inclusive or) and negation with their truth tables — *not a result* — –

#### Section 2.3

- **Def §2.3**, p.54 [FO-035]: Implication P => Q (hypothesis, conclusion) is false only when P is true and Q is false — *not a result* — –
- **Sec 2.3**, p.56 [FO-037]: Equivalent wordings of implication and biconditional: only if, sufficient, necessary, whenever, provided that — *not a result* — –
- **Sec 2.3**, p.57 [FO-037]: Equivalent wordings of implication and biconditional: only if, sufficient, necessary, whenever, provided that — *not a result* — –

#### Section 2.4

- **Def §2.4**, p.58 [FO-036]: Biconditional P <=> Q is true iff P and Q have the same truth value; read "if and only if" — *not a result* — –
- **Def §2.4**, p.58 [FO-038]: Converse of P => Q is Q => P; inverse is not-P => not-Q; contrapositive is not-Q => not-P — *not a result* — –
- **Def §2.4**, p.58 [FO-041]: P <=> Q is equivalent to (P => Q) and (Q => P), and to (P and Q) or (not P and not Q) — *proved proved here* — `UndergradKB.Foundations.iff_iff_imp_and_imp_and_or`
- **Def §2.4**, p.59 [FO-036]: Biconditional P <=> Q is true iff P and Q have the same truth value; read "if and only if" — *not a result* — –
- **Sec 2.4**, p.59 [FO-037]: Equivalent wordings of implication and biconditional: only if, sufficient, necessary, whenever, provided that — *not a result* — –
- **Fact 2.1**, p.63 [FO-045]: De Morgan's laws: not(P and Q) = (not P) or (not Q); not(P or Q) = (not P) and (not Q) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_2_1_de_morgan`, `not_and_or`
- **Sec 2.6**, p.63 [FO-041]: P <=> Q is equivalent to (P => Q) and (Q => P), and to (P and Q) or (not P and not Q) — *proved proved here* — `UndergradKB.Foundations.iff_iff_imp_and_imp_and_or`

#### Section 2.6

- **Def §2.6**, p.63 [FO-042]: Logical equivalence: statements with identical truth tables — *not a result* — –
- **Eq (2.1)**, p.64 [FO-044]: Contrapositive law: P => Q is equivalent to (not Q) => (not P) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_1_contrapositive`, `not_imp_not`, `mt`, `Function.mtr`
- **Eq (2.2)**, p.64 [FO-045]: De Morgan's laws: not(P and Q) = (not P) or (not Q); not(P or Q) = (not P) and (not Q) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_2_1_de_morgan`, `not_and_or`
- **Eq (2.3)**, p.64 [FO-046]: Commutative laws for and, or — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_3_comm`
- **Eq (2.4)**, p.64 [FO-047]: Distributive laws: P and (Q or R) = (P and Q) or (P and R); P or (Q and R) = (P or Q) and (P or R) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_4_distrib`
- **Eq (2.5)**, p.64 [FO-048]: Associative laws for and, or — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_5_assoc`
- **Def 2.1**, p.65 [FO-051]: Quantifiers: universal "for all" and existential "there exists", with their truth conditions and the terms universally/existentially quantified statement — *not a result* — –
- **Example 2.5**, p.66 [FO-528]: Four translated statements (non-odd integers are even, a non-even integer exists, real cube roots exist, rational products are rational) are true — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_5_true_translations`
- **Example 2.6**, p.66 [FO-529]: Four translated statements (all integers even, n^2=2, every real a square, sqrt(ab) rational) are false — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_6_false_translations`
- **Sec 2.7**, p.66 [FO-051]: Quantifiers: universal "for all" and existential "there exists", with their truth conditions and the terms universally/existentially quantified statement — *not a result* — –
- **Example 2.7**, p.67 [FO-052]: Order of quantifiers matters: forall x exists y does not imply exists y forall x, but exists y forall x implies forall x exists y — *proved proved here* — `UndergradKB.Foundations.forall_exists_of_exists_forall`, `UndergradKB.Foundations.cube_root_quantifier_order`, `UndergradKB.Foundations.lt_quantifier_order`
- **Sec 2.8**, p.68 [FO-056]: Implicit universal quantifier: an unquantified open conditional P(x) => Q(x) is read as forall x (P(x) => Q(x)) — *not a result* — –
- **Def 2.2**, p.69 [FO-056]: Implicit universal quantifier: an unquantified open conditional P(x) => Q(x) is read as forall x (P(x) => Q(x)) — *not a result* — –
- **Example 2.8**, p.69 [FO-530]: Mean Value Theorem as a conditional statement — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_8_mean_value`
- **Fact 2.2**, p.70 [FO-055]: Fact 2.2: forall x in X, Q(x) means the same as (x in X) => Q(x); "Every P-thing is a Q-thing" is forall x (P(x) => Q(x)) — *proved proved here* — `UndergradKB.Foundations.bounded_quantifiers`
- **Example 2.9**, p.70 [FO-531]: Goldbach's set X of even integers above 2 equals range of 2k+4; Goldbach holds for 4..20 — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_9_goldbach_setup`
- **Eq (2.8)**, p.72 [FO-054]: Negating quantified statements: not forall = exists not; not exists = forall not — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_8_negate_quantifiers`, `not_exists`, `not_forall₂`
- **Eq (2.9)**, p.72 [FO-054]: Negating quantified statements: not forall = exists not; not exists = forall not — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_8_negate_quantifiers`, `not_exists`, `not_forall₂`
- **Example 2.10**, p.72 [FO-532]: De Morgan: not (P or Q) iff not P and not Q — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_10_not_or`
- **Example 2.11**, p.72 [FO-533]: Not both x,y odd iff x even or y even — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_11_not_both_odd`
- **Eq (2.10)**, p.73 [FO-050]: Negation of an implication: not(P => Q) is equivalent to P and not Q — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_10_not_imp`, `not_and_not_right`
- **Example 2.12**, p.73 [FO-534]: Negation of "every real square is nonnegative" and its truth — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_12_neg_square_nonneg`
- **Example 2.13**, p.73 [FO-535]: Negation of "every real has a cube root" is some x with y^3 != x for all y; it is false — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_13_neg_cube_root`
- **Example 2.14**, p.74 [FO-536]: Negation of "if a odd then a^2 odd" is a odd and a^2 not odd; original true — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_14_neg_odd_square`
- **Example 2.15**, p.74 [FO-537]: Negation of "for all x, x odd implies x^2 odd" and its truth — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_2_15_neg_odd_square_forall`
- **Sec 2.11**, p.75 [FO-058]: Rules of inference: modus ponens, modus tollens, elimination (disjunctive syllogism); and-introduction, and-elimination, or-introduction — *proved proved here* — `UndergradKB.Foundations.rules_of_inference`
- **Sec 2.11**, p.76 [FO-058]: Rules of inference: modus ponens, modus tollens, elimination (disjunctive syllogism); and-introduction, and-elimination, or-introduction — *proved proved here* — `UndergradKB.Foundations.rules_of_inference`

## Chapter 3

54 items; 53 with a Lean name; 24 proved proved here; 29 in Mathlib; 1 not a result.


#### Section 3.1

- **Def §3.1**, p.77 [FO-213]: A list is an ordered finite sequence of entries (repetition allowed, order matters, length = number of entries, equal iff same entries in same positions); the empty list has length 0; a list of symbols without punctuation is a string. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_1_list_ext`, `UndergradKB.Foundations.Course.hammack_s3_1_list_length_zero`, `List`
- **Fact 3.1**, p.81 [FO-214]: Multiplication (product) principle: if a list/outcome is built in n steps with a_i choices at step i (number of choices independent of earlier choices), the total is a_1 a_2 ... a_n; for two sets, the size of a product set is the product of sizes. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_1_card_prod`, `UndergradKB.Foundations.Course.hammack_fact_3_1_card_pi`, `Finset.card_product`, `Fintype.card_prod`
- **Example 3.1**, p.81 [FO-496]: License plates of three letters and four digits number 26^3*10^4. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_1_license_plates`
- **Example 3.2**, p.81 [FO-497]: A drink order with 3, 3 and 2 options has 18 outcomes. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_2_latte_choices`
- **Ex 3.3**, p.82 [FO-217]: The number of length-n lists with entries from a k-element set, repetition allowed, is k^n; equivalently the number of functions from an n-set to a k-set is k^n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_3_card_fun`, `Fintype.card_fun`, `Fintype.card_pi`
- **Ex 3.3**, p.82 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **Example 3.4**, p.84 [FO-498]: Repetition-free 5-lists from A..G with first entry B/C/D and last entry a vowel number 360. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_4_restricted_lists`
- **Fact 3.2**, p.86 [FO-215]: Addition (sum) principle: for pairwise disjoint finite sets the cardinality of the union is the sum of the cardinalities; for two sets the condition is disjointness. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_2_card_union`, `UndergradKB.Foundations.Course.hammack_fact_3_2_card_biUnion`, `Finset.card_union_eq_card_add_card`, `Finset.card_disjUnion`
- **Example 3.5**, p.86 [FO-499]: Repetition-free 4-lists from A..G containing an E number 480. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_5_lists_with_E`
- **Example 3.6**, p.87 [FO-500]: Even five-digit numbers with no zero digit and exactly one 6 number 10240. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_6_even_numbers_one_six`
- **Fact 3.3**, p.88 [FO-216]: Subtraction (complement) principle: if X is a subset of a finite U then the cardinality of U minus X is card U minus card X (count the complement). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_3_card_sdiff`, `Finset.card_sdiff_of_subset`, `Finset.card_compl`, `Finset.card_add_card_compl`
- **Example 3.7**, p.88 [FO-501]: 4-lists from A..G (repetition allowed) with at least one E number 7^4-6^4. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_7_lists_at_least_one_E`
- **Def 3.1**, p.90 [FO-226]: Definition of factorial: n! is the number of non-repetitive length-n lists from n symbols, 0! = 1, 1! = 1, n! = n (n-1)! = n(n-1)...1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_3_1_factorial`, `Nat.factorial`, `Nat.factorial_zero`, `Nat.factorial_succ`
- **Eq 3.1**, p.91 [FO-226]: Definition of factorial: n! is the number of non-repetitive length-n lists from n symbols, 0! = 1, 1! = 1, n! = n (n-1)! = n(n-1)...1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_3_1_factorial`, `Nat.factorial`, `Nat.factorial_zero`, `Nat.factorial_succ`
- **Example 3.8**, p.91 [FO-394]: Repetition-free lists of length 7 from 7 letters number 7! = 5040. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_8_injective_lists`, `UndergradKB.Foundations.Course.hammack_ex_3_8_repeated_lists`

#### Section 3.4

- **text §3.4**, p.92 [FO-227]: A permutation of a set X is a non-repetitive list using every element of X (equivalently, bijection X to X); an n-element set has n! permutations. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_4_card_perm`, `Fintype.card_perm`, `Fintype.card_equiv`, `List.length_permutations`
- **text §3.4**, p.93 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **Fact 3.4**, p.95 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **Example 3.9**, p.95 [FO-395]: First-second-third rankings among 10 runners: P(10,3) = 720. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_9_rankings`
- **Example 3.10**, p.95 [FO-396]: Five-card lineups all red or all clubs: P(26,5) + P(13,5) = 8048040. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_10_red_or_clubs`
- **Def 3.2**, p.97 [FO-224]: Binomial coefficient: C(n,k) is the number of k-element subsets of an n-element set (0 when k<0 or k>n); also the entry in row n, column k of Pascal's triangle; read "n choose k". — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_3_2_card_powersetCard`, `Nat.choose`, `Finset.card_powersetCard`, `Nat.choose_eq_zero_of_lt`

#### Section 3.5

- **text §3.5**, p.98 [FO-229]: P(n,k) = C(n,k) k!: choose the k-subset, then arrange it (equivalently C(n,k) = P(n,k)/k!). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_5_descFactorial_eq_choose_mul`, `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.choose_eq_descFactorial_div_factorial`
- **text §3.5**, p.98 [FO-233]: Boundary values C(n,0) = C(n,n) = 1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_5_choose_boundary`, `Nat.choose_zero_right`, `Nat.choose_self`
- **Fact 3.5**, p.99 [FO-225]: Closed formula: C(n,k) = n!/(k!(n-k)!) for 0 <= k <= n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_5_choose_formula`, `Nat.choose_eq_factorial_div_factorial`, `Nat.choose_mul_factorial_mul_factorial`
- **Example 3.11**, p.99 [FO-397]: The set {1..9} has 126 four-element subsets. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_11_four_subsets`
- **Example 3.12**, p.99 [FO-398]: 60 five-element subsets of {1..9} have exactly two even elements. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_12_two_even`
- **Example 3.13**, p.99 [FO-399]: C(52,5) = 2598960 five-card hands. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_13_five_card_hands`
- **Example 3.14**, p.100 [FO-400]: Hands with two clubs and three hearts: C(13,2) C(13,3) = 22308. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_14_clubs_hearts`
- **Example 3.15**, p.100 [FO-401]: Lottery: C(36,6) = 1947792 tickets. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_15_lottery`
- **Example 3.16**, p.100 [FO-402]: 64 binary strings of length 7 have an odd number of 1's. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_16_odd_weight`
- **Eq 3.3**, p.102 [FO-231]: Pascal's rule C(n+1,k) = C(n,k-1) + C(n,k) (1 <= k <= n); every Pascal-triangle entry is the sum of the two above it, with 1s on the boundary; triangle rows are numbered from 0. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_3_pascal`, `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`
- **Eq 3.4**, p.103 [FO-232]: Symmetry: C(n,k) = C(n,n-k) for 0 <= k <= n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_4_choose_symm`, `Nat.choose_symm`

#### Section 3.6

- **text §3.6**, p.103 [FO-231]: Pascal's rule C(n+1,k) = C(n,k-1) + C(n,k) (1 <= k <= n); every Pascal-triangle entry is the sum of the two above it, with 1s on the boundary; triangle rows are numbered from 0. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_3_pascal`, `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`
- **Thm 3.1**, p.104 [FO-234]: Binomial theorem: (x+y)^n = sum over k of C(n,k) x^k y^(n-k) for n >= 0 (coefficients are Pascal's row n). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_3_1_binomial`, `add_pow`, `Commute.add_pow`
- **Fact 3.6**, p.105 [FO-239]: Inclusion-exclusion for two sets: for finite A, B, card(A union B) = card A + card B - card(A inter B). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_6_inclusion_exclusion`, `Finset.card_union_add_card_inter`
- **Example 3.17**, p.105 [FO-403]: Three-card hands all red or all face: C(26,3)+C(12,3)-C(6,3) = 2800. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_17_red_or_face`
- **Eq 3.5**, p.106 [FO-240]: Inclusion-exclusion for three sets: card(A union B union C) = sum of single cards - sum of pairwise intersections + triple intersection. — *proved proved here* — `UndergradKB.Foundations.hammack_eq_3_5_inclusion_exclusion_three`, `UndergradKB.Foundations.hammack_eq_3_5_inclusion_exclusion_three_int`
- **Example 3.18**, p.106 [FO-404]: Complement of Example 3.17: C(52,3) - 2800 = 19300. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_18_complement`

#### Section 3.8

- **text §3.8**, p.108 [FO-242]: A multiset is a collection where elements may repeat and order does not matter; its cardinality counts repeats, and the multiplicity of an element is the number of times it appears (sets are multisets with multiplicity 1). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_8_multiset`, `Multiset`, `Multiset.card`, `Multiset.count`
- **Fact 3.7**, p.110 [FO-243]: Stars and bars: the number of k-element multisets from an n-element set is C(k+n-1,k) = C(k+n-1,n-1) (encode as k stars and n-1 bars); equivalently weakly increasing lists / non-decreasing functions of bounded range. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_7_multisets`, `Sym.card_sym_eq_choose`, `Sym.card_sym_eq_multichoose`, `Nat.multichoose_eq`
- **Ex 3.19**, p.111 [FO-243]: Stars and bars: the number of k-element multisets from an n-element set is C(k+n-1,k) = C(k+n-1,n-1) (encode as k stars and n-1 bars); equivalently weakly increasing lists / non-decreasing functions of bounded range. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_7_multisets`, `Sym.card_sym_eq_choose`, `Sym.card_sym_eq_multichoose`, `Nat.multichoose_eq`
- **Ex 3.20**, p.112 [FO-244]: The number of non-negative integer solutions of x_1 + ... + x_n = k is C(k+n-1,n-1) (distributing k identical objects to n kids). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_20_nonneg_solutions`, `Finset.card_finsuppAntidiag_nat_eq_choose`
- **Ex 3.21**, p.112 [FO-243]: Stars and bars: the number of k-element multisets from an n-element set is C(k+n-1,k) = C(k+n-1,n-1) (encode as k stars and n-1 bars); equivalently weakly increasing lists / non-decreasing functions of bounded range. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_7_multisets`, `Sym.card_sym_eq_choose`, `Sym.card_sym_eq_multichoose`, `Nat.multichoose_eq`
- **Fact 3.8**, p.114 [FO-246]: Permutations of a multiset with n elements and multiplicities p_1..p_k number n!/(p_1! ... p_k!) (multinomial); same count for words with given letter multiplicities. — *proved proved here* — `UndergradKB.Combinatorics.card_arrangements`, `UndergradKB.Combinatorics.card_words_with_multiplicities`
- **Example 3.22**, p.114 [FO-405]: Permutations of a multiset with multiplicities 1,4,4,2 (MISSISSIPPI): 34650. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_22_mississippi`
- **Example 3.23**, p.114 [FO-406]: Permutations of the multiset with multiplicities 4,2,1,2: 3780. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_23_coin_multiset`
- **Fact 3.9**, p.116 [FO-247]: Division (strong pigeonhole) principle: n objects in k boxes give a box with at least ceil(n/k) objects and a box with at most floor(n/k). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_9_pigeonhole_strong`, `Fintype.exists_lt_card_fiber_of_mul_lt_card`, `Fintype.exists_le_card_fiber_of_mul_le_card`, `Fintype.exists_card_fiber_lt_of_card_lt_mul`
- **Fact 3.10**, p.116 [FO-248]: Pigeonhole principle: n objects in k boxes; if n > k some box has two objects, if n < k some box is empty. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_10_pigeonhole`, `UndergradKB.Foundations.Course.hammack_fact_3_10_empty_box`, `Fintype.exists_ne_map_eq_of_card_lt`, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
- **Example 3.24**, p.117 [FO-502]: Any six distinct integers from 0..9 contain two summing to 9. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_24_six_integers_sum_nine`, `UndergradKB.Foundations.Course.hammack_ex_3_24_five_integers_no_pair`
- **Example 3.25**, p.118 [FO-503]: Among 49 gumballs of four colours some colour occurs at least 13 times. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_25_forty_nine_gumballs`, `UndergradKB.Foundations.Course.hammack_ex_3_25_forty_eight_not_enough`
- **Example 3.26**, p.119 [FO-504]: Nine points each placed in one of four regions: some three share a region (pigeonhole step). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_3_26_nine_points_four_regions`

#### Section 3.10

- **text §3.10**, p.120 [FO-238]: Combinatorial proof: prove an identity by counting one set in two ways (method). — *not a result* — –
- **Ex 3.27**, p.120 [FO-232]: Symmetry: C(n,k) = C(n,n-k) for 0 <= k <= n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_4_choose_symm`, `Nat.choose_symm`
- **Ex 3.28**, p.121 [FO-236]: Sum of squares: C(n,0)^2 + ... + C(n,n)^2 = C(2n,n). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_28_sum_choose_sq`, `Nat.sum_range_choose_sq`

## Chapter 4

16 items; 15 with a Lean name; 4 proved proved here; 11 in Mathlib; 1 not a result.

- **Definition 4.1**, p.127 [FO-100]: Definitions of even (n = 2a) and odd (n = 2a+1) integers — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_1_even_odd`, `Even`, `Odd`, `even_iff_two_dvd`
- **Definition 4.2**, p.127 [FO-100]: Definitions of even (n = 2a) and odd (n = 2a+1) integers — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_1_even_odd`, `Even`, `Odd`, `even_iff_two_dvd`
- **Definition 4.3**, p.127 [FO-101]: Two integers have the same parity if both even or both odd, else opposite parity — *proved proved here* — `UndergradKB.Foundations.SameParity`, `UndergradKB.Foundations.OppositeParity`, `UndergradKB.Foundations.sameParity_iff_even_sub`, `UndergradKB.Foundations.oppositeParity_iff_odd_sub`
- **Definition 4.4**, p.128 [FO-105]: Definition of divisibility a ∣ b (b = ac); divisor, multiple; 0 and 1 facts (x ∣ 0, x ∣ x, 1 ∣ n) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_4_dvd`, `dvd_zero`, `dvd_refl`
- **Definition 4.5**, p.128 [FO-108]: Prime = exactly two positive divisors; composite = more than two; 1 is neither — *proved proved here* — `UndergradKB.Foundations.Composite`, `UndergradKB.Foundations.prime_iff_card_divisors_eq_two`, `UndergradKB.Foundations.composite_iff_two_lt_card_divisors`, `UndergradKB.Foundations.one_neither_prime_nor_composite`
- **Definition 4.6**, p.128 [FO-110]: Definitions of gcd (largest common divisor, not both zero) and lcm (smallest positive common multiple) — *proved proved here* — `UndergradKB.Foundations.gcd_isGreatest_common_divisor`, `UndergradKB.Foundations.lcm_isLeast_positive_common_multiple`
- **Fact 4.1**, p.129 [FO-107]: The integers are closed under +, − and × — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_4_1_int_closed`, `Int.instCommRing`

#### Section 4.2

- **Prop §4.2 @129 (stated, accepted without proof; unnumbered)**, p.129 [FO-112]: Division algorithm: existence and uniqueness of q, r with a = qb + r, 0 ≤ r < b — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_2_division_algorithm`, `Int.ediv_emod_unique''`
- **Prop §4.2 @129 (accepted without proof; revisited in §10.3)**, p.129 [FO-113]: Fundamental theorem of arithmetic: unique prime factorization of n > 1 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_2_fta`, `Nat.primeFactorsList_unique`, `Nat.prod_primeFactorsList`, `UniqueFactorizationMonoid.factors_unique`

#### Section 4.3

- **Outline §4.3**, p.130 [FO-138]: Direct proof: to show P ⇒ Q assume P, deduce Q (fix an arbitrary element for universal statements) — *not a result* — –
- **Prop §4.3**, p.131 [FO-104]: n is even iff n^2 is even (equivalently n odd iff n^2 odd) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_even_iff_sq_even`, `Int.even_pow'`, `Int.even_pow`, `Int.odd_mul`
- **Prop §4.3**, p.133 [FO-106]: Divisibility is transitive: a ∣ b and b ∣ c imply a ∣ c — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_dvd_trans`, `dvd_trans`
- **Prop §4.3**, p.134 [FO-111]: lcm(ca, cb) = c · lcm(a, b) for naturals — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_lcm_mul_left`, `lcm_mul_left`
- **Prop §4.3**, p.134 [FO-116]: For positive x, y: x ≤ y implies √x ≤ √y — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_sqrt_mono`, `Real.sqrt_le_sqrt`
- **Prop §4.3**, p.135 [FO-117]: AM-GM for two variables: 2√(xy) ≤ x + y for positive reals — *proved proved here* — `UndergradKB.Foundations.two_mul_sqrt_mul_le_add`

#### Section 4.5

- **Prop §4.5**, p.137 [FO-102]: Integers of opposite parity have odd sum (and in general parity of a sum) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_5_opposite_parity_odd_sum`, `Int.odd_add`, `Int.even_add`

## Chapter 5

7 items; 7 with a Lean name; 2 proved proved here; 5 in Mathlib.


#### Section 5.1

- **Outline §5.1**, p.141 [FO-139]: Contrapositive: P ⇒ Q is equivalent to ∼Q ⇒ ∼P; so prove the latter — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_o5_1_contrapositive`, `not_imp_not`, `mt`
- **Definition 5.1**, p.143 [FO-118]: Definition of congruence mod n (Hammack: n ∣ a−b; Levin: same remainder) with notation a ≡ b (mod n) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_5_1_modEq_iff_dvd`, `Int.ModEq`, `Int.modEq_iff_dvd`
- **Example 5.1**, p.143 [FO-483]: Sample congruences 9=1, 6=10, 14!=8 (mod 4), 20=4 (mod 8), 17=-4 (mod 3). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_5_1_sample_congruences`, `UndergradKB.Foundations.Course.hammack_ex_5_1_divisibility_form`, `UndergradKB.Foundations.Course.hammack_ex_5_1_remainders`

#### Section 5.2

- **Prop §5.2 @143 (same remainder; converse left to exercise 32)**, p.143 [FO-119]: a ≡ b (mod n) iff same remainder iff n ∣ a−b iff a = b + kn — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s5_2_modEq_equiv`, `Int.modEq_iff_dvd`, `Int.modEq_iff_add_fac`, `Int.ModEq`
- **Prop §5.2 @144 (ac ≡ bc)**, p.144 [FO-121]: Congruence respects addition, subtraction, multiplication (a≡b, c≡d give a±c ≡ b±d, ac ≡ bd); special case ac ≡ bc — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s5_2_modEq_arith`, `Int.ModEq.add`, `Int.ModEq.sub`, `Int.ModEq.mul`
- **Prop §5.2 @144 (squares)**, p.144 [FO-122]: Congruence respects powers: a ≡ b implies a^p ≡ b^p (e.g. a^2 ≡ b^2) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s5_2_modEq_pow`, `Int.ModEq.pow`
- **Prop §6 intro**, p.149 [FO-132]: No integers a, b with a^2 − 4b = 2 (equivalently x^2 = 4y+2 has no integer solution) — *proved proved here* — `UndergradKB.Foundations.no_int_sq_sub_four_mul_eq_two`

## Chapter 6

8 items; 8 with a Lean name; 2 proved proved here; 6 in Mathlib.


#### Section 6.1

- **Outline §6.1**, p.150 [FO-140]: Proof by contradiction: to show P assume ∼P and derive a contradiction (P ⇔ (∼P ⇒ C ∧ ∼C)); for P ⇒ Q assume P and ∼Q — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_o6_1_contradiction`, `Classical.by_contradiction`, `imp_iff_not_or`
- **Definition 6.1**, p.151 [FO-130]: Definition of rational (a/b, a, b integers) and irrational real number — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_6_1_irrational_iff`, `Irrational`, `irrational_iff_ne_rational`
- **Prop §6.1**, p.151 [FO-131]: √2 is irrational — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s6_1_sqrt_two_irrational`, `irrational_sqrt_two`, `Nat.Prime.irrational_sqrt`, `irrational_sqrt_natCast_iff`
- **Prop §6.1**, p.152 [FO-133]: There are infinitely many primes (Euclid) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s6_1_infinitely_many_primes`, `Nat.exists_infinite_primes`, `Nat.not_bddAbove_setOfPred_prime`

#### Section 6.2

- **Prop §6.2**, p.153 [FO-104]: n is even iff n^2 is even (equivalently n odd iff n^2 odd) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_even_iff_sq_even`, `Int.even_pow'`, `Int.even_pow`, `Int.odd_mul`
- **Outline §6.2**, p.153 [FO-140]: Proof by contradiction: to show P assume ∼P and derive a contradiction (P ⇔ (∼P ⇒ C ∧ ∼C)); for P ⇒ Q assume P and ∼Q — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_o6_1_contradiction`, `Classical.by_contradiction`, `imp_iff_not_or`
- **Prop §6.2**, p.154 [FO-135]: No integer a ≥ 2 divides both b and b+1 (consecutive integers are coprime) — *proved proved here* — `UndergradKB.Foundations.not_dvd_both_consecutive`

#### Section 6.3

- **Prop §6.3**, p.154 [FO-134]: Every nonzero rational number is a product of two irrational numbers — *proved proved here* — `UndergradKB.Foundations.rat_eq_mul_irrationals`

## Chapter 7

10 items; 7 with a Lean name; 2 proved proved here; 5 in Mathlib; 3 not a result.


#### Section 7.1

- **Outline §7.1**, p.159 [FO-141]: Proving "P iff Q": prove both P ⇒ Q and its converse — *not a result* — –
- **Prop §7.1**, p.160 [FO-104]: n is even iff n^2 is even (equivalently n odd iff n^2 odd) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_even_iff_sq_even`, `Int.even_pow'`, `Int.even_pow`, `Int.odd_mul`
- **Prop §7.1**, p.160 [FO-124]: a ≡ b (mod 6) iff a ≡ b (mod 2) and a ≡ b (mod 3) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s7_1_modEq_six`, `Int.modEq_and_modEq_iff_modEq_mul`

#### Section 7.2

- **Prop §7.2**, p.161 [FO-142]: To prove n statements equivalent it suffices to prove a cycle of n implications — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s7_2_cycle_tfae`, `List.tfae_of_cycle`

#### Section 7.3

- **Prop §7.3 @163 (there exists an even prime, witness 2)**, p.163 [FO-109]: A prime is 2 or odd (the only even prime is 2) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s7_3_even_prime`, `Nat.Prime.eq_two_or_odd'`, `Nat.Prime.even_iff`
- **Prop §7.3**, p.163 [FO-143]: Existence statements (exhibit a witness) and existence-and-uniqueness proofs; constructive vs non-constructive — *not a result* — –
- **Proposition 7.1**, p.164 [FO-114]: Bezout: for a, b ∈ ℕ there are integers k, l with gcd(a,b) = ak + bl — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_prop_7_1_bezout`, `Nat.gcd_eq_gcd_ab`, `Int.gcd_eq_gcd_ab`, `EuclideanDomain.gcd_eq_gcd_ab`
- **Prop §7.3**, p.165 [FO-115]: The integers ax + by are exactly the multiples of gcd(a,b) (existence and uniqueness of such a d) — *proved proved here* — `UndergradKB.Foundations.existsUnique_multiples_eq_combinations`

#### Section 7.4

- **Prop §7.4**, p.166 [FO-136]: There exist irrational x, y with x^y rational (non-constructive via √2^√2; constructive via √2, log_2 9, which uses log_2 9 irrational) — *proved proved here* — `UndergradKB.Foundations.exists_irrational_rpow_rational`, `UndergradKB.Foundations.irrational_logb_two_nine`, `UndergradKB.Foundations.sqrt_two_rpow_logb_two_nine`
- **Prop §7.4**, p.166 [FO-143]: Existence statements (exhibit a witness) and existence-and-uniqueness proofs; constructive vs non-constructive — *not a result* — –

## Chapter 8

25 items; 24 with a Lean name; 11 proved proved here; 13 in Mathlib; 1 not a result.


#### Section 8.1

- **Prop §8.1**, p.170 [FO-150]: How to show a ∈ {x : P(x)} and a ∈ {x ∈ S : P(x)} (unfold the set-builder condition) — *not a result* — –
- **Example 8.1**, p.170 [FO-484]: 7,14,21,28,35 lie in {x in N : 7 \| x} and 8 does not. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_1_multiples_of_seven`
- **Example 8.2**, p.170 [FO-485]: {4,13,45}, {1,2,3}, {10,854,3} have three elements; {1,2,3,4} does not. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_2_three_element_sets`

#### Section 8.2

- **Prop §8.2 @171 (restates Definition 1.3)**, p.171 [FO-145]: Definition of subset A ⊆ B (and proper subset) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_2_subset_def`, `Set.Subset`
- **Example 8.3**, p.171 [FO-551]: Pairs (8,23),(100,75),(102,77) lie in the mod-5 congruence set, (6,10) does not, (4n+3,9n-2) always does — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_3_congruence_pairs`
- **Example 8.4**, p.171 [FO-486]: -22, -1, 5 lie in {3x^3+2 : x in Z}; 0 and 12 do not. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_4_three_cubed_plus_two`
- **Example 8.5**, p.172 [FO-386]: Integers divisible by 18 are a subset of integers divisible by 6. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_5_dvd_18_subset_dvd_6`
- **Example 8.6**, p.172 [FO-387]: Integers divisible by both 2 and 9 are divisible by 6. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_6_dvd_2_inter_dvd_9`
- **Example 8.7**, p.172 [FO-388]: Pairs congruent mod 6 are congruent mod 3. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_8_7_modeq_six_subset_three`
- **Prop §8.2 @173 (listed among "obvious" facts)**, p.173 [FO-146]: Subset is transitive: A ⊆ B and B ⊆ C imply A ⊆ C — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_2_subset_trans`, `Set.Subset.trans`
- **Prop §8.2**, p.173 [FO-147]: Basic subset facts: A∩B ⊆ A, A ⊆ A∪B, A−B ⊆ A, X ⊆ A implies X ⊆ A∪B — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_2_basic_subsets`, `Set.inter_subset_left`, `Set.subset_union_left`, `Set.sdiff_subset`
- **Example 8.8**, p.173 [FO-151]: P(A) ∪ P(B) ⊆ P(A ∪ B) — *proved proved here* — `UndergradKB.Foundations.powerset_union_subset`, `UndergradKB.Foundations.powerset_union_ne`

#### Section 8.3

- **Prop §8.3**, p.174 [FO-149]: Set equality: A = B iff A ⊆ B and B ⊆ A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_3_set_eq_iff`, `Set.Subset.antisymm`, `Set.ext`
- **Example 8.9**, p.174 [FO-152]: P(A) ⊆ P(B) implies A ⊆ B — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_8_9_powerset_subset`, `Set.powerset_mono`
- **Example 8.10**, p.174 [FO-156]: If a ∣ n, b ∣ n with a, b coprime then ab ∣ n (used for {n : 35 ∣ n} = {n : 5 ∣ n} ∩ {n : 7 ∣ n}) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_8_10_coprime_dvd`, `IsCoprime.mul_dvd`
- **Example 8.11**, p.175 [FO-153]: If C ≠ ∅ and A×C = B×C then A = B — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_8_11_prod_cancel`, `Set.prod_eq_iff_eq`
- **Example 8.12**, p.175 [FO-154]: A × (B ∩ C) = (A×B) ∩ (A×C) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_8_12_prod_inter`, `Set.prod_inter`
- **Example 8.13**, p.176 [FO-154]: A × (B ∩ C) = (A×B) ∩ (A×C) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_8_12_prod_inter`, `Set.prod_inter`
- **Definition 8.1**, p.177 [FO-157]: Definition of perfect number (sum of proper divisors equals n; equivalently divisors sum to 2n) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_8_1_perfect`, `Nat.Perfect`, `Nat.perfect_iff_sum_properDivisors`, `Nat.perfect_iff_sum_divisors_eq_two_mul`
- **Prop §8.3**, p.177 [FO-155]: Laws for sets: De Morgan, distributive of ∩ over ∪ and ∪ over ∩, and × over ∪ (stated, proved in exercises) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_3_set_laws`, `Set.compl_inter`, `Set.compl_union`, `Set.inter_union_distrib_left`

#### Section 8.4

- **Eq (8.1) §8.4 @179 (unnumbered; recalled from calculus / ch. 7 exercise)**, p.179 [FO-158]: Geometric sum: sum_{k=0}^{n} r^k = (r^{n+1} − 1)/(r − 1), in particular sum 2^k = 2^{n+1} − 1 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_8_1_geom_sum`, `geom_sum_eq`
- **Theorem 8.1**, p.179 [FO-159]: Euclid: if 2^n − 1 is prime then 2^{n−1}(2^n − 1) is perfect — *proved proved here* — `UndergradKB.Foundations.euclid_perfect`
- **Theorem 8.2**, p.181 [FO-160]: Euler: every even perfect number has the form 2^{n−1}(2^n − 1) with 2^n − 1 prime — *proved proved here* — `UndergradKB.Foundations.euler_even_perfect`
- **Prop §8.4 @182 (term; n prime is Ch. 5 Exercise 25)**, p.182 [FO-161]: Mersenne primes: primes of the form 2^n − 1 (and then n is prime) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_4_mersenne_prime_exponent`, `mersenne`, `Nat.Prime.of_mersenne`
- **Prop §9 intro**, p.186 [FO-144]: Disproof: to disprove P prove ∼P; negation of ∀ is ∃∼, of ∃ is ∀∼, of P⇒Q is P ∧ ∼Q; counterexample — *proved proved here* — `UndergradKB.Foundations.negation_rules`

## Chapter 9

7 items; 7 with a Lean name; 7 proved proved here.


#### Section 9.1

- **Prop §9.1**, p.187 [FO-144]: Disproof: to disprove P prove ∼P; negation of ∀ is ∃∼, of ∃ is ∀∼, of P⇒Q is P ∧ ∼Q; counterexample — *proved proved here* — `UndergradKB.Foundations.negation_rules`
- **Example 9.1**, p.187 [FO-389]: Not every integer n gives a prime n^2 - n + 11 (n = 11 fails). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_9_1_not_always_prime`
- **Example 9.2**, p.188 [FO-365]: A - (B cap C) = (A - B) cap (A - C) fails for sets of naturals. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_9_2_set_diff_counterexample`

#### Section 9.2

- **Prop §9.2**, p.188 [FO-144]: Disproof: to disprove P prove ∼P; negation of ∀ is ∃∼, of ∃ is ∀∼, of P⇒Q is P ∧ ∼Q; counterexample — *proved proved here* — `UndergradKB.Foundations.negation_rules`
- **Example 9.3**, p.188 [FO-137]: There is no real x with x^4 < x < x^2 — *proved proved here* — `UndergradKB.Foundations.no_real_x4_lt_x_lt_x2`
- **Example 9.4**, p.189 [FO-390]: Three distinct integers above 1 exist with x^y = y^z (2, 16, 4). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_9_4_exists_pow_triple`
- **Example 9.5**, p.190 [FO-137]: There is no real x with x^4 < x < x^2 — *proved proved here* — `UndergradKB.Foundations.no_real_x4_lt_x_lt_x2`

## Chapter 10

29 items; 28 with a Lean name; 6 proved proved here; 22 in Mathlib; 1 not a result.


#### Section 10.1

- **Outline §10.1**, p.194 [FO-171]: Principle of mathematical induction: a base case plus the step P(k) implies P(k+1) proves P(n) for all n from the base on — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_induction`, `Nat.le_induction`
- **Def §10.1**, p.194 [FO-172]: Terminology: basis step, inductive step, inductive hypothesis — *not a result* — –
- **Prop §10.1**, p.194 [FO-178]: The sum of the first n odd numbers is n^2 — *proved proved here* — `UndergradKB.Foundations.hammack_s10_1_sum_odds`
- **Prop §10.1**, p.195 [FO-173]: Induction may start at any base case (S_0, S_m, n >= 5), not only at 1 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_induction_any_base`, `Nat.le_induction`
- **Prop §10.1**, p.195 [FO-174]: To prove a statement for all integers by induction one needs a base case and steps in both directions (P(k) implies P(k+1) and P(k-1)) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_int_induction`, `Int.induction_on`
- **Prop §10.1**, p.195 [FO-183]: 5 divides n^5 - n for every non-negative integer n — *proved proved here* — `UndergradKB.Foundations.five_dvd_pow_five_sub`
- **Prop §10.1**, p.196 [FO-180]: Sum_{i=0}^n i * i! = (n+1)! - 1 — *proved proved here* — `UndergradKB.Foundations.hammack_s10_1_sum_mul_factorial`
- **Prop §10.1**, p.198 [FO-181]: Bernoulli's inequality: (1+x)^n >= 1 + nx for x > -1 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_bernoulli`, `one_add_mul_le_pow`
- **Prop 10.1**, p.198 [FO-182]: If a prime p divides a product a_1 ... a_n (n >= 2) then p divides some a_i — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_prime_dvd_prod`, `Prime.exists_mem_finset_dvd`, `Prime.exists_mem_multiset_dvd`

#### Section 10.2

- **Outline §10.2**, p.199 [FO-175]: Strong induction: P(1..k) all true implies P(k+1), plus base cases, proves P(n) for all n; also equivalent in power to ordinary induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_strong_induction`, `Nat.strong_induction_on`, `Nat.case_strong_induction_on`
- **Prop §10.2**, p.199 [FO-185]: Every postage of 8 cents or more can be made from 3-cent and 5-cent stamps — *proved proved here* — `UndergradKB.Foundations.hammack_s10_2_stamps`
- **Def §10.2**, p.201 [FO-186]: Definitions: cycle in a graph and tree (connected graph with no cycles) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_iff`, `SimpleGraph.Walk.IsCycle`, `SimpleGraph.IsAcyclic`, `SimpleGraph.IsTree`
- **Def §10.2**, p.201 [FO-310]: A (simple) graph is a pair of a vertex set and a set of 2-element subsets of it (edges) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_edge_two_vertices`, `SimpleGraph`
- **Def §10.2 @201 (assumed throughout, informal)**, p.201 [FO-314]: Connected graph: a path (walk) between any two vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_connected_iff`, `SimpleGraph.Connected`, `SimpleGraph.Preconnected`, `SimpleGraph.Reachable`
- **Def §10.2 @201 (informal: distinct edges forming a closed route)**, p.201 [FO-324]: Cycle: closed path with no other repeated vertex — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_cycle_def`, `SimpleGraph.Walk.IsCycle`, `SimpleGraph.Walk.IsCircuit`
- **Def §10.2**, p.201 [FO-326]: Tree = connected graph with no cycles; forest = graph with no cycles; leaves are degree-1 vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_def`, `SimpleGraph.IsTree`, `SimpleGraph.IsAcyclic`
- **Prop §10.2**, p.202 [FO-187]: A tree with n vertices has n - 1 edges (strong induction, remove an edge) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_edges`, `SimpleGraph.IsTree.card_edgeFinset`
- **Prop §10.2**, p.202 [FO-330]: A tree with v vertices has v-1 edges (and conversely connected plus v-1 edges gives a tree) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_iff_card_edges`, `SimpleGraph.IsTree.card_edgeFinset`, `SimpleGraph.IsTree.ncard_edgeSet_add_one`, `SimpleGraph.isTree_iff_connected_and_card`

#### Section 10.3

- **Outline §10.3**, p.203 [FO-177]: Proof by smallest counterexample (well-ordering): if some S_n fails, there is a least failing index k, with S_{k-1} true — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_3_smallest_counterexample`, `Nat.find`, `Nat.find_spec`, `Nat.find_min`
- **Prop §10.3**, p.203 [FO-184]: x - 1 divides x^n - 1 (instances 4 \\| 5^n - 1 and 5 \\| 6^n - 1) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_3_sub_one_dvd_pow`, `UndergradKB.Foundations.Course.hammack_s10_3_four_dvd_five_pow`, `sub_one_dvd_pow_sub_one`, `sub_dvd_pow_sub_pow`
- **Thm 10.1**, p.204 [FO-188]: Fundamental theorem of arithmetic, existence: every integer n > 1 is a product of primes — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_10_1_exists_prime_factorization`, `Nat.prod_primeFactorsList`, `Nat.prime_of_mem_primeFactorsList`, `UniqueFactorizationMonoid.exists_prime_factors`
- **Thm 10.1**, p.204 [FO-189]: Fundamental theorem of arithmetic, uniqueness: two prime factorizations of n agree up to order — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_10_1_unique_prime_factorization`, `Nat.primeFactorsList_unique`, `UniqueFactorizationMonoid.factors_unique`

#### Section 10.5

- **Def §10.5**, p.205 [FO-190]: Definition of the Fibonacci sequence F_1 = F_2 = 1, F_n = F_{n-1} + F_{n-2} — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_5_fibonacci`, `Nat.fib`, `Nat.fib_add_two`
- **Eq (10.1) §10.5**, p.206 [FO-192]: F_{n+1}/F_n tends to (1+sqrt 5)/2 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_10_1_fib_ratio_limit`, `tendsto_fib_succ_div_fib_atTop`
- **Prop §10.5**, p.206 [FO-191]: F_{n+1}^2 - F_{n+1} F_n - F_n^2 = (-1)^n — *proved proved here* — `UndergradKB.Foundations.hammack_s10_5_fib_identity`
- **Def §10.5**, p.207 [FO-193]: The golden ratio Phi = (1+sqrt 5)/2 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_5_golden_ratio`, `Real.goldenRatio`
- **Exercise 1 §10 (unnumbered, @207)**, p.207 [FO-179]: Triangular numbers: 1+2+...+n = n(n+1)/2 (equivalently T_n = C(n+1,2)), proved by reverse-and-add and by induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_triangular`, `Finset.sum_range_id_mul_two`, `Finset.sum_range_id`
- **Exercise 2 §10 (unnumbered, @207)**, p.207 [FO-205]: Sum of squares: 1^2+...+n^2 = n(n+1)(2n+1)/6 (squares on an n by n chessboard) — *proved proved here* — `UndergradKB.Foundations.hammack_ex_s10_sum_squares`
- **Exercise 30 §10 (unnumbered, @209)**, p.209 [FO-194]: Binet's formula: F_n = (phi^n - psi^n)/sqrt 5 — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_9_9_5_binet`, `UndergradKB.Foundations.Course.hammack_ex_s10_30_binet`, `Real.coe_fib_eq`

## Chapter 11

27 items; 27 with a Lean name; 16 proved proved here; 11 in Mathlib.

- **Def 11.1**, p.214 [FO-062]: A (binary) relation on A, or from A to B, is a subset of A x A (resp. A x B) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_1_relation_is_subset`, `SetRel`
- **Example 11.1**, p.214 [FO-457]: The ten listed pairs on {1,2,3,4} form the relation >=, and (3,4) is not in it. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_1_geq_relation`
- **Example 11.2**, p.214 [FO-458]: The eight listed pairs on {1,2,3,4} form the relation same parity. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_2_same_parity`
- **Example 11.3**, p.214 [FO-459]: The intersection of >= and same parity on {1,2,3,4} is six listed pairs. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_3_intersection`
- **Example 11.4**, p.215 [FO-460]: An arbitrary subset of B x B is a relation; alphabetical order on four letters is six pairs. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_4_arbitrary_relation`
- **Example 11.5**, p.215 [FO-461]: {(x,y) in Z x Z : x-y positive} is the relation > on Z. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_5_greater_than_on_int`
- **Example 11.6**, p.215 [FO-462]: {(x,x) : x real} is the relation = on R. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_6_equality_relation`
- **Def 11.2**, p.217 [FO-063]: Reflexive, symmetric, transitive properties of a relation (Levin adds irreflexive and antisymmetric in running text) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_2_refl_symm_trans`, `IsTrans`, `SetRel.IsSymm`
- **Example 11.7**, p.218 [FO-371]: The concrete relation on {b,c,d,e} is not reflexive but is symmetric and transitive. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_7_relation_properties`

#### Section 11.2

- **Prop §11.2 @220 (Example 11.8)**, p.220 [FO-064]: Congruence mod n is reflexive, symmetric and transitive on Z (Levin: the mod-2 case, "difference is even") — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s11_2_modEq_equivalence`, `Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans`
- **Def 11.3**, p.222 [FO-065]: Definition of equivalence relation (reflexive, symmetric, transitive) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_3_equivalence`, `Equivalence`, `Setoid`, `IsEquiv`
- **Def 11.4**, p.223 [FO-066]: Equivalence class of a under an equivalence relation: [a] = set of x related to a — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_4_class_mem`, `Setoid.classes`, `Setoid.mem_classes`
- **Example 11.9**, p.223 [FO-463]: Equality on {-1,1,2,3,4} has five singleton classes. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_9_equality_classes`
- **Example 11.10**, p.223 [FO-464]: Same parity on {-1,1,2,3,4} has exactly the classes {2,4} and {-1,1,3}. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_10_parity_classes`
- **Example 11.11**, p.223 [FO-544]: R4 of Figure 11.2 is an equivalence with classes {-1},{1,3},{2,4} — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_11_R4_classes`
- **Example 11.12**, p.224 [FO-465]: Same degree is an equivalence relation on real polynomials; the class of 3x^2+2 is the degree-2 polynomials. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_12_same_degree`
- **Example 11.13**, p.224 [FO-466]: Classes of congruence mod 3: [0] is the multiples of 3, [1] and [2] by remainder. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_13_classes_mod_three`, `UndergradKB.Foundations.Course.hammack_ex_11_13_class_names`
- **Thm 11.1**, p.227 [FO-068]: For an equivalence relation, [a] = [b] iff aRb — *proved proved here* — `UndergradKB.Foundations.eqvClass_eq_iff`, `UndergradKB.Foundations.relClass_eq_iff`
- **Thm 11.2**, p.228 [FO-070]: The equivalence classes of an equivalence relation on A form a partition of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_11_2_classes_partition`, `Setoid.isPartition_classes`, `Setoid.classes_eqv_classes`
- **Def 11.5**, p.228 [FO-069]: Definition of partition of a set (nonempty blocks, cover, pairwise disjoint) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_5_partition`, `Setoid.IsPartition`
- **Example 11.14**, p.228 [FO-467]: Five listed families of subsets of a 4-element set are partitions. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_14_partitions_of_four`
- **Example 11.15**, p.228 [FO-545]: Classes of R1..R4 of Figure 11.2 form partitions of A with the listed blocks — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_15_classes_partition`
- **Example 11.16**, p.228 [FO-468]: The classes of congruence mod 3 are the three remainder sets and form a partition of Z. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_11_16_mod_three_partition`

#### Section 11.4

- **Prop §11.4**, p.229 [FO-071]: Conversely a partition defines an equivalence relation ("same block"), and the two constructions are mutually inverse — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s11_4_partition_equivalence`, `Setoid.mkClasses`, `Setoid.classes_mkClasses`, `Setoid.mkClasses_classes`
- **Def 11.6**, p.231 [FO-072]: Definition of the integers mod n: the n classes [0],...,[n-1] of congruence mod n, with [a]+[b]=[a+b] and [a][b]=[ab] — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_6_zmod`, `ZMod`, `ZMod.commRing`, `ZMod.card`

#### Section 11.5

- **Prop §11.5**, p.232 [FO-073]: Addition and multiplication on Z_n are well defined (independent of representatives) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s11_5_modEq_add_mul`, `Int.ModEq.add`, `Int.ModEq.mul`, `ZMod.intCast_eq_intCast_iff`
- **Def 11.7**, p.233 [FO-062]: A (binary) relation on A, or from A to B, is a subset of A x A (resp. A x B) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_1_relation_is_subset`, `SetRel`

## Chapter 12

36 items; 35 with a Lean name; 15 proved proved here; 20 in Mathlib; 1 not a result.

- **Def 12.1**, p.236 [FO-078]: A function f : A -> B assigns to each element of A exactly one element of B (Hammack: a relation from A to B in which each x has a unique y; f(x) is the image of x) — *not a result* — –
- **Example 12.1**, p.236 [FO-469]: {(n,\|n\|+2)} in Z x N is the graph of a function containing (1,3) and (-3,5). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_1_abs_plus_two_graph`
- **Def 12.2**, p.237 [FO-079]: Domain, codomain and range of a function; range is a subset of the codomain — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_2_range`, `Set.range`, `Set.mem_range`
- **Example 12.2**, p.237 [FO-470]: {(p,0),(q,1),(r,2),(s,2)} is a function A to B with range all of B. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_2_small_function`
- **Def 12.3**, p.239 [FO-080]: Two functions are equal iff they agree at every point of the domain — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_3_function_ext`, `funext`, `funext_iff`
- **Example 12.3**, p.239 [FO-372]: The range of (m,n) -> 6m - 9n on Z x Z is the multiples of 3. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_3_range_multiples_of_three`
- **Def 12.4**, p.240 [FO-081]: Injective (one-to-one): distinct inputs have distinct outputs — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_injective`
- **Def 12.4**, p.240 [FO-082]: Surjective (onto): every element of the codomain is an output — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_surjective`
- **Def 12.4**, p.240 [FO-083]: Bijective = injective and surjective — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_bijective`, `Function.Bijective`
- **Example 12.4**, p.243 [FO-373]: x -> 1/x + 1 on nonzero reals is injective but not surjective onto R. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_4_injective_not_surjective`
- **Example 12.5**, p.243 [FO-374]: x -> 1/x + 1 is a bijection from nonzero reals onto reals other than 1. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_5_bijective`
- **Example 12.6**, p.243 [FO-375]: (m,n) -> (m+n, m+2n) is a bijection of Z x Z. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_6_bijective`
- **Example 12.7**, p.243 [FO-376]: (m,n) -> m/(\|n\|+1) into Q is not injective but surjective. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_7_not_injective_surjective`

#### Section 12.3

- **Prop §12.3**, p.245 [FO-084]: Pigeonhole principle (function version): if \\|A\\|>\\|B\\| a function A->B is not injective; if \\|A\\|<\\|B\\| it is not surjective — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s12_3_pigeonhole`, `Fintype.exists_ne_map_eq_of_card_lt`, `Function.Embedding.isEmpty_of_card_lt`, `Fintype.card_le_of_surjective`
- **Prop §12.3**, p.246 [FO-085]: Any 10 integers in [1,100] have two different subsets with equal sum (pigeonhole application) — *proved proved here* — `UndergradKB.Foundations.exists_subsets_eq_sum`
- **Def 12.5**, p.247 [FO-086]: Composition g∘f of f : A->B and g : B->C — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_5_comp`
- **Example 12.8**, p.248 [FO-377]: The composition g o f of two small finite functions is (a,3),(b,1),(c,3). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_8_composition`
- **Example 12.9**, p.248 [FO-546]: f: A->B, g: C->B with B != C and B not subset of C, so g after f undefined — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_9_composition_undefined`
- **Example 12.10**, p.248 [FO-378]: g o f = x^2+x+1, f o g = x^2+3x+2 and they differ (composition is not commutative). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_10_composition_not_commutative`
- **Thm 12.1**, p.249 [FO-087]: Function composition is associative — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_1_comp_assoc`, `Function.comp_assoc`
- **Thm 12.2**, p.249 [FO-088]: Composites of injective (resp. surjective) functions are injective (resp. surjective) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_2_comp`, `Function.Bijective.comp`
- **Def 12.6**, p.250 [FO-089]: Identity function i_A is bijective — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_6_id_bijective`, `id`, `Function.bijective_id`
- **Def 12.7**, p.251 [FO-076]: Inverse relation R^{-1} = {(y,x) : (x,y) in R} — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_7_inverse_relation`, `SetRel.inv`
- **Thm 12.3**, p.252 [FO-090]: f : A->B is bijective iff the inverse relation f^{-1} is a function B->A — *proved proved here* — `UndergradKB.Foundations.bijective_iff_inverseRelation_function`
- **Def 12.8**, p.252 [FO-091]: Inverse function f^{-1} of a bijection, with f^{-1}∘f = i_A and f∘f^{-1} = i_B — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_8_inverse`, `Equiv.ofBijective`, `Function.leftInverse_surjInv`, `Function.rightInverse_surjInv`
- **Example 12.11**, p.252 [FO-379]: x -> x^3 + 1 on R is bijective: every y has a unique real preimage. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_11_cube_plus_one_bijective`
- **Example 12.12**, p.253 [FO-380]: The inverse of (m,n) -> (m+n, m+2n) is (m,n) -> (2m-n, n-m) (left and right inverse). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_12_inverse`
- **Def 12.9**, p.254 [FO-092]: Image f(X) and preimage (inverse image) f^{-1}(Y) of subsets under a function — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_9_image_preimage`, `Set.image`, `Set.preimage`
- **Example 12.13**, p.254 [FO-381]: Image and preimage computations for an 8-element function (preimage of {4}, image, empty preimage of 9). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_12_13_image_preimage`
- **Example 12.14**, p.254 [FO-095]: X ⊆ f^{-1}(f(X)), with proper inclusion in general — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_3`, `Set.subset_preimage_image`, `Set.preimage_image_eq`
- **Thm 12.4(1)**, p.255 [FO-093]: f(W ∩ X) ⊆ f(W) ∩ f(X) (equality can fail) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_1`, `Set.image_inter_subset`
- **Thm 12.4(2)**, p.255 [FO-094]: f(W ∪ X) = f(W) ∪ f(X) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_2`, `Set.image_union`
- **Thm 12.4(3)**, p.255 [FO-095]: X ⊆ f^{-1}(f(X)), with proper inclusion in general — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_3`, `Set.subset_preimage_image`, `Set.preimage_image_eq`
- **Thm 12.4(4)**, p.255 [FO-096]: f^{-1}(Y ∪ Z) = f^{-1}(Y) ∪ f^{-1}(Z) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_4`, `Set.preimage_union`
- **Thm 12.4(5)**, p.255 [FO-097]: f^{-1}(Y ∩ Z) = f^{-1}(Y) ∩ f^{-1}(Z) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_5`, `Set.preimage_inter`
- **Thm 12.4(6)**, p.255 [FO-098]: f(f^{-1}(Y)) ⊆ Y, with equality for surjective f — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_12_4_6`, `Set.image_preimage_subset`, `Set.image_preimage_eq`

## Chapter 13

35 items; 31 with a Lean name; 12 proved proved here; 19 in Mathlib; 4 not a result.

- **Theorem 13.1**, p.257 [FO-259]: Triangle inequality for reals: $\lvert x-y\rvert \le \lvert x-z\rvert+\lvert z-y\rvert$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_1_triangle`, `dist_triangle`

#### Section 13.1

- **Eq (13.1)-(13.3) §13.1**, p.257 [FO-260]: Consequences of the triangle inequality: $\lvert x+y\rvert\le\lvert x\rvert+\lvert y\rvert$ and $\lvert x\rvert-\lvert y\rvert\le\lvert x+y\rvert$ (and $\lvert x-y\rvert\le\lvert x\rvert+\lvert y\rvert$) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s13_1_triangle_consequences`
- **Definition 13.1**, p.258 [FO-261]: Informal definition of limit (f(x) arbitrarily close to L for x sufficiently close to c) — *not a result* — –
- **Definition 13.2**, p.259 [FO-262]: Epsilon-delta definition of $\lim_{x\to c}f(x)=L$ (with $0<\lvert x-c\rvert<\delta$, f defined on a punctured neighbourhood) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_13_2_limit_eps_delta`, `Metric.tendsto_nhdsWithin_nhds`, `Filter.Tendsto`
- **Example 13.1**, p.260 [FO-415]: Epsilon-delta: lim_{x->2} (3x+4) = 10. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_13_1_limit_linear`
- **Example 13.2**, p.260 [FO-416]: Epsilon-delta: lim_{x->2} 5x^2 = 20. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_13_2_limit_quadratic`

#### Section 13.3

- **§13.3 @261 (unnumbered)**, p.261 [FO-263]: A limit "does not exist" when no real L satisfies the definition (negation; also two different limits cannot both hold) — *not a result* — –
- **Example 13.3**, p.261 [FO-264]: Example: $f(x)=x/2+\lvert x-2\rvert/(x-2)+2$ has no limit at 2 (one-sided values differ by more than 2) — *proved proved here* — `UndergradKB.Foundations.hammack_ex_13_3_no_limit`
- **Example 13.4**, p.262 [FO-265]: $\lim_{x\to0}\sin(1/x)$ does not exist — *proved proved here* — `UndergradKB.Foundations.hammack_ex_13_4_sin_inv_no_limit`
- **Example 13.5**, p.262 [FO-266]: $\lim_{x\to0}x\sin(1/x)=0$ — *proved proved here* — `UndergradKB.Foundations.hammack_ex_13_5_x_sin_inv`
- **Theorem 13.2**, p.263 [FO-267]: Constant function rule: $\lim_{x\to c}a=a$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_2_limit_const`, `tendsto_const_nhds`
- **Theorem 13.3**, p.263 [FO-268]: Identity function rule: $\lim_{x\to c}x=c$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_3_limit_id`, `tendsto_id`
- **Theorem 13.4**, p.264 [FO-269]: Constant multiple rule: $\lim a f(x)=a\lim f(x)$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_4_limit_const_mul`, `Filter.Tendsto.const_mul`
- **Theorem 13.5**, p.264 [FO-270]: Sum rule for limits — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_5_limit_add`
- **Theorem 13.6**, p.264 [FO-271]: Difference rule for limits — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_6_limit_sub`
- **Theorem 13.7**, p.265 [FO-272]: Multiplication rule for limits — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_7_limit_mul`, `Filter.Tendsto.mul`
- **Theorem 13.8**, p.265 [FO-273]: Division rule for limits (denominator limit nonzero) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_8_limit_div`, `Filter.Tendsto.div`
- **Example 13.6**, p.267 [FO-417]: lim_{x->1} (1/x - 1)/(1 - x) = 1 (punctured neighbourhood). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_13_6_rational_limit`
- **Definition 13.3**, p.268 [FO-274]: Definition of continuity at c: $\lim_{x\to c}f(x)=f(c)$ (three conditions); continuous = continuous at every point of the domain — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_13_3_continuousAt_eps_delta`, `ContinuousAt`, `Continuous`, `Metric.continuousAt_iff`

#### Section 13.5

- **§13.5 @269 (unnumbered)**, p.269 [FO-276]: Derivative as a limit of difference quotients: $f'(c)=\lim_{x\to c}\frac{f(x)-f(c)}{x-c}$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s13_5_deriv_as_limit`, `hasDerivAt_iff_tendsto_slope`
- **Theorem 13.9**, p.269 [FO-275]: Composition rule: if $g\to L$ at c and f continuous at L then $f\circ g\to f(L)$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_9_limit_comp`, `ContinuousAt.tendsto`, `Filter.Tendsto.comp`
- **Theorem 13.10**, p.269 [FO-277]: Differentiable at c implies continuous at c — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_10_differentiable_continuous`, `DifferentiableAt.continuousAt`, `HasDerivAt.continuousAt`

#### Section 13.6

- **§13.6 @270 (unnumbered)**, p.270 [FO-280]: Horizontal asymptote: line $y=L$ where $\lim_{x\to\pm\infty}f=L$ — *not a result* — –
- **Definition 13.4**, p.271 [FO-278]: Definition of limits at $\pm\infty$ ($x>N\Rightarrow\lvert f(x)-L\rvert<\varepsilon$; $x<N$ for $-\infty$) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_13_4_limit_atTop`, `UndergradKB.Foundations.Course.hammack_def_13_4_limit_atBot`, `Metric.tendsto_atTop`, `Metric.tendsto_atTop'`
- **Example 13.7**, p.271 [FO-281]: $\lim_{x\to\infty}\sin(x)/x=0$ — *proved proved here* — `UndergradKB.Foundations.hammack_ex_13_7_sin_div_x`
- **§13.6 @272 (unnumbered)**, p.272 [FO-279]: Infinite limits at infinity: $\lim_{x\to\infty}f=\pm\infty$ means eventually exceeds (resp. below) any bound — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s13_6_limit_atTop_infinite`, `Filter.tendsto_atTop_atTop`

#### Section 13.7

- **§13.7 @273 (unnumbered)**, p.273 [FO-282]: Sequences: infinite list $a_1,a_2,\dots$, general term, a sequence as a function $\mathbb N\to\mathbb R$ — *not a result* — –
- **Definition 13.5**, p.274 [FO-283]: Definition: sequence converges to L ($\forall\varepsilon\exists N\,n>N\Rightarrow\lvert a_n-L\rvert<\varepsilon$); otherwise diverges — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_13_5_seq_converges`, `Metric.tendsto_atTop'`, `Filter.Tendsto`
- **Example 13.8**, p.274 [FO-418]: The sequence 1 - 1/n converges to 1 (epsilon-N form). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_13_8_one_minus_inv`
- **Example 13.9**, p.275 [FO-419]: The sequence (-1)^(n+1)(n+1)/n has no limit. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_13_9_alternating_diverges`
- **Definition 13.6**, p.276 [FO-284]: Divergence to $\pm\infty$ of a sequence — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_13_6_seq_diverges_to_infinity`, `Filter.tendsto_atTop_atTop`
- **Definition 13.7**, p.278 [FO-285]: Definition: infinite series converges to S iff sequence of partial sums converges to S — *proved proved here* — `UndergradKB.Foundations.SeriesConvergesTo`, `UndergradKB.Foundations.seriesConvergesTo_of_hasSum`
- **Example 13.10**, p.278 [FO-286]: $\sum_{k\ge1}1/2^k=1$ — *proved proved here* — `UndergradKB.Foundations.hammack_ex_13_10_geometric_half`
- **Corollary 13.1**, p.279 [FO-288]: Divergence test: if $a_n$ diverges or tends to a nonzero limit, then $\sum a_k$ diverges — *proved proved here* — `UndergradKB.Foundations.hammack_thm_13_11_terms_tendsto_zero`, `UndergradKB.Foundations.hammack_cor_13_1_divergence_test`
- **Theorem 13.11**, p.279 [FO-287]: If $\sum a_k$ converges then $a_n\to0$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_13_11_series_terms_tendsto_zero`

## Chapter 14

25 items; 24 with a Lean name; 6 proved proved here; 17 in Mathlib; 1 not formalized; 1 not a result.

- **Definition 14.1**, p.281 [FO-289]: Same cardinality: $\lvert A\rvert=\lvert B\rvert$ iff there is a bijection $A\to B$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_14_1_card_eq_iff`, `Cardinal.eq`, `Cardinal.mk_congr`, `Equiv`

#### Section 14.1

- **§14.1 @282 (unnumbered)**, p.282 [FO-290]: Terminology: bijection, injection, surjection — *not a result* — –
- **Example 14.1**, p.282 [FO-420]: Negation is a bijection from {0..5} onto {-5..0}. — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_14_1_negation_bijection`
- **Example 14.2**, p.282 [FO-291]: There is a bijection $\mathbb N\to\mathbb Z$, so $\lvert\mathbb N\rvert=\lvert\mathbb Z\rvert$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_1_nat_int`, `Equiv.intEquivNat`, `Cardinal.mk_int`, `Cardinal.mk_nat`
- **Theorem 14.1**, p.283 [FO-291]: There is a bijection $\mathbb N\to\mathbb Z$, so $\lvert\mathbb N\rvert=\lvert\mathbb Z\rvert$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_1_nat_int`, `Equiv.intEquivNat`, `Cardinal.mk_int`, `Cardinal.mk_nat`
- **Theorem 14.2**, p.284 [FO-292]: No surjection (hence bijection) $\mathbb N\to\mathbb R$; $\lvert\mathbb N\rvert\ne\lvert\mathbb R\rvert$ (Cantor's diagonal argument) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_2_nat_not_real`, `Cardinal.not_countable_real`, `Cardinal.aleph0_lt_continuum`, `Cardinal.mk_real`
- **§14.1 @285 (unnumbered)**, p.285 [FO-294]: Equal cardinality is an equivalence relation (reflexive, symmetric, transitive) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s14_1_card_eq_equivalence`, `Equiv.refl`, `Equiv.symm`, `Equiv.trans`
- **Example 14.3**, p.285 [FO-293]: $\lvert(0,\infty)\rvert=\lvert(0,1)\rvert=\lvert\mathbb R\rvert$ (all intervals have the cardinality of $\mathbb R$) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_14_3_interval_cards`, `Cardinal.mk_Ioi_real`, `Cardinal.mk_Ioo_real`, `Cardinal.mk_real`
- **Example 14.4**, p.285 [FO-293]: $\lvert(0,\infty)\rvert=\lvert(0,1)\rvert=\lvert\mathbb R\rvert$ (all intervals have the cardinality of $\mathbb R$) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_14_3_interval_cards`, `Cardinal.mk_Ioi_real`, `Cardinal.mk_Ioo_real`, `Cardinal.mk_real`
- **Definition 14.2**, p.287 [FO-295]: Definitions: countably infinite ($\lvert\mathbb N\rvert=\lvert A\rvert$), countable (finite or countably infinite), uncountable — *proved proved here* — `UndergradKB.Foundations.hammack_def_14_2_countably_infinite_iff`, `UndergradKB.Foundations.hammack_def_14_2_countable_iff`, `UndergradKB.Foundations.hammack_def_14_2_uncountable_iff`
- **Definition 14.3**, p.287 [FO-296]: Definition: $\aleph_0=\lvert\mathbb N\rvert$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_14_3_aleph0`, `Cardinal.aleph0`, `Cardinal.mk_nat`
- **Example 14.5**, p.287 [FO-421]: The even integers have cardinality aleph_0 (via n -> 2n from Z). — *proved proved here* — `UndergradKB.Foundations.Course.hammack_ex_14_5_even_integers_countable`
- **Theorem 14.3**, p.288 [FO-297]: A set is countably infinite iff its elements can be listed in an infinite list $a_1,a_2,\dots$ — *proved proved here* — `UndergradKB.Foundations.hammack_thm_14_3_list`, `UndergradKB.Foundations.hammack_thm_14_3_list_with_repeats`
- **Theorem 14.4**, p.288 [FO-298]: $\mathbb Q$ is countably infinite — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_4_rat_countably_infinite`, `Cardinal.mkRat`
- **Theorem 14.5**, p.290 [FO-299]: Product of two countably infinite sets is countably infinite — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_5_prod_countably_infinite`, `Set.Countable.prod`, `Cardinal.mk_prod`
- **Corollary 14.1**, p.291 [FO-300]: Finite product of $n\ge2$ countably infinite sets is countably infinite — *proved proved here* — `UndergradKB.Foundations.hammack_cor_14_1_finite_product`
- **Theorem 14.6**, p.291 [FO-301]: Union of two countably infinite sets is countably infinite — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_6_union_countably_infinite`, `Set.Countable.union`, `Set.countable_union`
- **Definition 14.4**, p.293 [FO-302]: Order on cardinalities: $\lvert A\rvert\le\lvert B\rvert$ iff injection $A\to B$; $<$ iff injection but no bijection — *proved proved here* — `UndergradKB.Foundations.hammack_def_14_4_lt_iff`, `UndergradKB.Foundations.hammack_def_14_4_le_iff`
- **Theorem 14.7**, p.293 [FO-303]: Cantor's theorem: $\lvert A\rvert<\lvert\mathcal P(A)\rvert$ for every set A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_7_cantor`, `Cardinal.cantor`, `Cardinal.mk_set`, `Function.cantor_surjective`
- **Theorem 14.8**, p.294 [FO-304]: An infinite subset of a countably infinite set is countably infinite — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_8_infinite_subset`, `Set.Countable.mono`, `Cardinal.mk_eq_aleph0`
- **Theorem 14.9**, p.295 [FO-305]: A set containing an uncountable subset is uncountable — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_9_superset_uncountable`, `Set.Countable.mono`
- **Theorem 14.10**, p.298 [FO-306]: Cantor-Bernstein-Schroeder: injections $A\to B$ and $B\to A$ give a bijection — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_10_cantor_bernstein`, `Function.Embedding.schroeder_bernstein`, `Function.Embedding.antisymm`
- **Example 14.6**, p.300 [FO-307]: $[0,1)$ and $(0,1)$ have equal cardinality — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_14_6_Ico_Ioo`, `Cardinal.mk_Ico_real`, `Cardinal.mk_Ioo_real`
- **Theorem 14.11**, p.300 [FO-308]: $\lvert\mathbb R\rvert=\lvert\mathcal P(\mathbb N)\rvert$ — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_14_11_real_powerset_nat`, `Cardinal.mk_real`, `Cardinal.mk_set_nat`, `Cardinal.two_power_aleph0`

#### Section 14.4

- **§14.4 @301 (unnumbered)**, p.301 [FO-309]: Continuum hypothesis (no cardinality strictly between $\aleph_0$ and $\lvert\mathbb R\rvert$) and its independence (Godel, Cohen) — *not formalized* — `UndergradKB.Foundations.continuumHypothesis_iff`
