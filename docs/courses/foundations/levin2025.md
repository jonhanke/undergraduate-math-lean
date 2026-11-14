# Course outline: Levin (foundations)

Generated from [`docs/coverage/foundations/checklist.md`](../../coverage/foundations/checklist.md); do not edit by hand.
Items are in the book's order. Statements are our own paraphrases, not book text. Cite the Lean name; `lake build Foundations` builds this topic.

447 items in 7 chapters; 409 with a Lean name (91.5%).

## Chapter 0

7 items; 3 with a Lean name; 2 proved proved here; 1 in Mathlib; 4 not a result.


#### Section 0.2

- **Sec 0.2.2**, p.25 [FO-001]: A set is a collection of elements; membership relation; sets are finite or infinite — *proved proved here* — `UndergradKB.Foundations.set_membership_finite_infinite`
- **Sec 0.2.2**, p.26 [FO-002]: Two sets are equal iff they have the same elements (order and repetition irrelevant) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_set_ext`, `Set.ext`
- **Sec 0.2.2**, p.26 [FO-003]: Set-builder notation {expr : rule} describes a set by a membership condition — *not a result* — –
- **Sec 0.2.2**, p.26 [FO-004]: Standard number-system sets N, Z, Q, R and conventions (Hammack N starts at 1, Levin N starts at 0) — *not a result* — –
- **Sec 0.2.3**, p.26 [FO-061]: Overview of discrete structures: functions (rule, closed vs recursive formula, graph as set of pairs), sequences, relations as sets of pairs, graphs — *not a result* — –
- **Example 0.2.3**, p.27 [FO-061]: Overview of discrete structures: functions (rule, closed vs recursive formula, graph as set of pairs), sequences, relations as sets of pairs, graphs — *not a result* — –
- **Sec 0.2.4**, p.28 [FO-008]: An ordered pair (x,y) is a list of two things; (a,b)=(c,d) iff componentwise equal — *proved proved here* — `UndergradKB.Foundations.ordered_pair_eq_iff`

## Chapter 1

83 items; 64 with a Lean name; 36 proved proved here; 28 in Mathlib; 19 not a result.


#### Section 1.1

- **Def 1.1.3**, p.34 [FO-057]: Argument, premises, conclusion; valid, sound argument; proof as sound argument — *not a result* — –
- **Def 1.1.6**, p.36 [FO-031]: A statement is a sentence that is definitely true or definitely false — *not a result* — –
- **Sec 1.1.2**, p.37 [FO-033]: Atomic versus molecular statements; propositional variables — *not a result* — –
- **Sec 1.1.2**, p.39 [FO-033]: Atomic versus molecular statements; propositional variables — *not a result* — –
- **Def 1.1.8**, p.39 [FO-034]: Definitions of conjunction, disjunction (inclusive or) and negation with their truth tables — *not a result* — –
- **Def 1.1.8**, p.39 [FO-036]: Biconditional P <=> Q is true iff P and Q have the same truth value; read "if and only if" — *not a result* — –
- **Def 1.1.9**, p.39 [FO-034]: Definitions of conjunction, disjunction (inclusive or) and negation with their truth tables — *not a result* — –
- **Example 1.1.11**, p.40 [FO-448]: Truth values of compound statements about 17, 18, 19 being prime. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_1_11_connectives_primes`
- **Sec 1.1.3**, p.42 [FO-032]: Open sentence (predicate): a sentence whose truth depends on free variables — *not a result* — –
- **Def 1.1.13**, p.43 [FO-051]: Quantifiers: universal "for all" and existential "there exists", with their truth conditions and the terms universally/existentially quantified statement — *not a result* — –
- **Sec 1.1.3**, p.44 [FO-055]: Fact 2.2: forall x in X, Q(x) means the same as (x in X) => Q(x); "Every P-thing is a Q-thing" is forall x (P(x) => Q(x)) — *proved proved here* — `UndergradKB.Foundations.bounded_quantifiers`
- **Def 1.1.15**, p.45 [FO-056]: Implicit universal quantifier: an unquantified open conditional P(x) => Q(x) is read as forall x (P(x) => Q(x)) — *not a result* — –

#### Section 1.2

- **Def 1.2.2**, p.51 [FO-035]: Implication P => Q (hypothesis, conclusion) is false only when P is true and Q is false — *not a result* — –
- **Example 1.2.5**, p.53 [FO-449]: Implications with false hypothesis or true conclusion are true. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_5_vacuous_implications`
- **Def 1.2.7**, p.55 [FO-038]: Converse of P => Q is Q => P; inverse is not-P => not-Q; contrapositive is not-Q => not-P — *not a result* — –
- **Example 1.2.8**, p.55 [FO-538]: contrapositive equivalent to implication, inverse to converse, converse not equivalent — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_8_converse_contrapositive_inverse`
- **Note 1.2.9**, p.56 [FO-039]: Converse, contrapositive and inverse of a quantified implication are formed ignoring the outside quantifier — *not a result* — –
- **Example 1.2.10**, p.56 [FO-450]: Any nine cards from a deck contain three of the same suit. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_10_nine_cards_three_suit`
- **Example 1.2.11**, p.57 [FO-539]: from P->Q: Q follows from P, not-P from not-Q; nothing from Q or not-P — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_11_conclusions`
- **Sec 1.2.3**, p.58 [FO-041]: P <=> Q is equivalent to (P => Q) and (Q => P), and to (P and Q) or (not P and not Q) — *proved proved here* — `UndergradKB.Foundations.iff_iff_imp_and_imp_and_or`
- **Example 1.2.12**, p.58 [FO-540]: biconditional is conjunction of if-part and only-if-part — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_12_if_only_if`
- **Example 1.2.13**, p.58 [FO-541]: rephrasings of an implication: contrapositive, not-P or Q — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_13_rephrasings`
- **Def 1.2.14**, p.59 [FO-037]: Equivalent wordings of implication and biconditional: only if, sufficient, necessary, whenever, provided that — *not a result* — –
- **Example 1.2.15**, p.59 [FO-542]: spade implies black, black does not imply spade — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_2_15_spade_black`

#### Section 1.3

- **Example 1.3.3**, p.66 [FO-543]: truth table of not-P or Q and equivalence with P->Q — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_3_3_truth_table_not_or`
- **Example 1.3.4**, p.67 [FO-451]: (P -> Q) or (Q -> R) is a tautology. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_3_4_tautology`
- **Sec 1.3.2**, p.68 [FO-043]: Tautology / law of logic: a statement true for all truth assignments (resp. in all interpretations) — *not a result* — –
- **Def 1.3.5**, p.68 [FO-042]: Logical equivalence: statements with identical truth tables — *not a result* — –
- **Theorem 1.3.6**, p.68 [FO-044]: Contrapositive law: P => Q is equivalent to (not Q) => (not P) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_1_contrapositive`, `not_imp_not`, `mt`, `Function.mtr`
- **Example 1.3.7**, p.69 [FO-452]: not (P or Q) is equivalent to not P and not Q. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_3_7_not_or`
- **Theorem 1.3.8**, p.69 [FO-045]: De Morgan's laws: not(P and Q) = (not P) or (not Q); not(P or Q) = (not P) and (not Q) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_2_1_de_morgan`, `not_and_or`
- **Sec 1.3.3**, p.70 [FO-040]: P => Q is logically equivalent to (not P) or Q — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s1_3_3_imp_iff_not_or`, `imp_iff_not_or`
- **Sec 1.3.3**, p.70 [FO-049]: Double negation: not not P is equivalent to P — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s1_3_3_double_negation`, `not_not`
- **Example 1.3.9**, p.70 [FO-453]: not (P -> Q) is equivalent to P and not Q. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_3_9_not_implies`
- **Theorem 1.3.10**, p.71 [FO-050]: Negation of an implication: not(P => Q) is equivalent to P and not Q — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_10_not_imp`, `not_and_not_right`
- **Example 1.3.11**, p.71 [FO-366]: (P or Q) -> R implies (P->R) or (Q->R) but they are not logically equivalent. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_3_11_not_equivalent`
- **Sec 1.3.4**, p.72 [FO-054]: Negating quantified statements: not forall = exists not; not exists = forall not — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_2_8_negate_quantifiers`, `not_exists`, `not_forall₂`
- **Example 1.3.12**, p.73 [FO-454]: No smallest integer is equivalent to: for every x there is y < x. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_3_12_no_smallest`
- **Example 1.3.13**, p.73 [FO-053]: forall x P(x) or forall x Q(x) implies forall x (P(x) or Q(x)), but not conversely — *proved proved here* — `UndergradKB.Foundations.forall_or_of_or_forall`, `UndergradKB.Foundations.even_or_odd_not_distrib`
- **Sec 1.3.4**, p.74 [FO-043]: Tautology / law of logic: a statement true for all truth assignments (resp. in all interpretations) — *not a result* — –
- **Example 1.3.14**, p.74 [FO-052]: Order of quantifiers matters: forall x exists y does not imply exists y forall x, but exists y forall x implies forall x exists y — *proved proved here* — `UndergradKB.Foundations.forall_exists_of_exists_forall`, `UndergradKB.Foundations.cube_root_quantifier_order`, `UndergradKB.Foundations.lt_quantifier_order`
- **Sec 1.3.5**, p.75 [FO-058]: Rules of inference: modus ponens, modus tollens, elimination (disjunctive syllogism); and-introduction, and-elimination, or-introduction — *proved proved here* — `UndergradKB.Foundations.rules_of_inference`
- **Example 1.3.15**, p.75 [FO-059]: Validity of a deduction rule checked by truth table: (P=>Q, not P=>Q therefore Q); (P=>R, Q=>R, P or Q therefore R) is valid but (P=>R, Q=>R, R therefore P or Q) is not — *proved proved here* — `UndergradKB.Foundations.deduction_cases`, `UndergradKB.Foundations.deduction_or_elim`, `UndergradKB.Foundations.deduction_converse_or_invalid`
- **Example 1.3.16**, p.76 [FO-059]: Validity of a deduction rule checked by truth table: (P=>Q, not P=>Q therefore Q); (P=>R, Q=>R, P or Q therefore R) is valid but (P=>R, Q=>R, R therefore P or Q) is not — *proved proved here* — `UndergradKB.Foundations.deduction_cases`, `UndergradKB.Foundations.deduction_or_elim`, `UndergradKB.Foundations.deduction_converse_or_invalid`
- **Sec 1.3.5**, p.77 [FO-060]: If everything has property P then something has it (forall x P(x) therefore exists x P(x)), valid when the domain is nonempty — *proved proved here* — `UndergradKB.Foundations.exists_of_forall`, `UndergradKB.Foundations.forall_not_imp_exists_of_isEmpty`

#### Section 1.4

- **Proposition 1.4.4**, p.85 [FO-552]: in a mini sudoku solution each digit appears once per row, column, box, four times total — *proved proved here* — `UndergradKB.Foundations.Course.levin_prop_1_4_4_sudoku_solution_digits`
- **Sec 1.4.2**, p.86 [FO-138]: Direct proof: to show P ⇒ Q assume P, deduce Q (fix an arbitrary element for universal statements) — *not a result* — –
- **Example 1.4.6**, p.86 [FO-553]: in the given mini sudoku, a 2 at r1c1 forces a 2 at r4c4 — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_4_6_sudoku_two_corners`
- **Example 1.4.7**, p.87 [FO-564]: a valid-or-not mini sudoku with exactly three empty squares and a solution is solvable (unique solution) — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_4_7_three_empty_solvable`
- **Ex 1.4.8**, p.88 [FO-100]: Definitions of even (n = 2a) and odd (n = 2a+1) integers — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_1_even_odd`, `Even`, `Odd`, `even_iff_two_dvd`
- **Ex 1.4.8**, p.88 [FO-104]: n is even iff n^2 is even (equivalently n odd iff n^2 odd) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_even_iff_sq_even`, `Int.even_pow'`, `Int.even_pow`, `Int.odd_mul`
- **Ex 1.4.9**, p.88 [FO-106]: Divisibility is transitive: a ∣ b and b ∣ c imply a ∣ c — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_dvd_trans`, `dvd_trans`
- **Sec 1.4.3**, p.89 [FO-139]: Contrapositive: P ⇒ Q is equivalent to ∼Q ⇒ ∼P; so prove the latter — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_o5_1_contrapositive`, `not_imp_not`, `mt`
- **Example 1.4.10**, p.89 [FO-554]: a solvable mini sudoku puzzle is valid — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_4_10_sudoku_solvable_valid`
- **Ex 1.4.11 @90 (definitions stated inline in the examples)**, p.90 [FO-100]: Definitions of even (n = 2a) and odd (n = 2a+1) integers — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_1_even_odd`, `Even`, `Odd`, `even_iff_two_dvd`
- **Ex 1.4.11**, p.90 [FO-104]: n is even iff n^2 is even (equivalently n odd iff n^2 odd) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_3_even_iff_sq_even`, `Int.even_pow'`, `Int.even_pow`, `Int.odd_mul`
- **Ex 1.4.12**, p.90 [FO-103]: If a+b is odd then a is odd or b is odd (contrapositive: two evens sum to even) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_1_4_12_odd_sum_odd_summand`, `Int.odd_add`, `Int.even_add`
- **Sec 1.4.4**, p.91 [FO-140]: Proof by contradiction: to show P assume ∼P and derive a contradiction (P ⇔ (∼P ⇒ C ∧ ∼C)); for P ⇒ Q assume P and ∼Q — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_o6_1_contradiction`, `Classical.by_contradiction`, `imp_iff_not_or`
- **Ex 1.4.13 @91 (prime defined inline)**, p.91 [FO-108]: Prime = exactly two positive divisors; composite = more than two; 1 is neither — *proved proved here* — `UndergradKB.Foundations.Composite`, `UndergradKB.Foundations.prime_iff_card_divisors_eq_two`, `UndergradKB.Foundations.composite_iff_two_lt_card_divisors`, `UndergradKB.Foundations.one_neither_prime_nor_composite`
- **Ex 1.4.13**, p.91 [FO-109]: A prime is 2 or odd (the only even prime is 2) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s7_3_even_prime`, `Nat.Prime.eq_two_or_odd'`, `Nat.Prime.even_iff`
- **Example 1.4.14**, p.92 [FO-565]: every solution of the given mini sudoku has a 3 in the top-right corner — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_4_14_sudoku_top_right_three`
- **Ex 1.4.15 @92 (uses the negation of an existence statement)**, p.92 [FO-144]: Disproof: to disprove P prove ∼P; negation of ∀ is ∃∼, of ∃ is ∀∼, of P⇒Q is P ∧ ∼Q; counterexample — *proved proved here* — `UndergradKB.Foundations.negation_rules`
- **Ex 1.4.16**, p.93 [FO-131]: √2 is irrational — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s6_1_sqrt_two_irrational`, `irrational_sqrt_two`, `Nat.Prime.irrational_sqrt`, `irrational_sqrt_natCast_iff`
- **Ex 1.4.17**, p.93 [FO-132]: No integers a, b with a^2 − 4b = 2 (equivalently x^2 = 4y+2 has no integer solution) — *proved proved here* — `UndergradKB.Foundations.no_int_sq_sub_four_mul_eq_two`
- **Sec 1.4.5**, p.94 [FO-140]: Proof by contradiction: to show P assume ∼P and derive a contradiction (P ⇔ (∼P ⇒ C ∧ ∼C)); for P ⇒ Q assume P and ∼Q — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_o6_1_contradiction`, `Classical.by_contradiction`, `imp_iff_not_or`
- **Example 1.4.18**, p.94 [FO-162]: Pigeonhole principle: more than n pigeons in n holes forces a hole with two — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_1_4_18_pigeonhole`, `Fintype.exists_ne_map_eq_of_card_lt`, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`

#### Section 1.5

- **Definition 1.5.2**, p.105 [FO-145]: Definition of subset A ⊆ B (and proper subset) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_2_subset_def`, `Set.Subset`
- **Example 1.5.3**, p.105 [FO-487]: {x < 5} properly contains {x^2 < 10} in the naturals. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_5_3_proper_subset`
- **Proposition 1.5.4**, p.106 [FO-146]: Subset is transitive: A ⊆ B and B ⊆ C imply A ⊆ C — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s8_2_subset_trans`, `Set.Subset.trans`
- **Example 1.5.5 @106 (the iff is left as an exercise)**, p.106 [FO-148]: A ⊆ B implies A∪B ⊆ B (and A ⊆ B iff A∪B = B) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_1_5_5_union_subset`, `Set.union_subset_iff`, `Set.union_eq_right`
- **Definition 1.5.6**, p.107 [FO-163]: Definition of injective function — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_1_5_6_injective`
- **Example 1.5.7**, p.107 [FO-488]: Of two functions on {1,2,3}, one is injective and the other is not. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_5_7_injective`
- **Proposition 1.5.8**, p.108 [FO-164]: If f : A → B with finite A, B and ∣A∣ > ∣B∣ then f is not injective — *in Mathlib* — `UndergradKB.Foundations.Course.levin_prop_1_5_8_not_injective`, `Fintype.exists_ne_map_eq_of_card_lt`, `Fintype.card_le_of_injective`
- **Corollary 1.5.9**, p.108 [FO-489]: Among 25 students and 12 birth months two share a month. — *proved proved here* — `UndergradKB.Foundations.Course.levin_cor_1_5_9_birth_months`
- **Definition 1.5.10**, p.108 [FO-165]: Image of a set under a function: f(A) = {f(a) : a ∈ A} — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_1_5_10_image`, `Set.image`
- **Example 1.5.11**, p.108 [FO-490]: The image of {1,2,3} under doubling is {2,4,6}. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_5_11_image_doubling`
- **Proposition 1.5.12**, p.109 [FO-166]: If A ⊆ B then f(A) ⊆ f(B) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_prop_1_5_12_image_mono`, `Set.image_mono`
- **Definition 1.5.13**, p.110 [FO-168]: Definition of a transitive relation — *proved proved here* — `UndergradKB.Foundations.transitive_iff`
- **Definition 1.5.16**, p.111 [FO-169]: Degree of a vertex: number of edges containing it — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_1_5_16_degree`, `SimpleGraph.degree`
- **Example 1.5.17**, p.111 [FO-491]: Degrees 3,2,2,1 in the graph on {1,2,3,4} with four edges; sum is twice the edge count. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_1_5_17_degrees`
- **Proposition 1.5.18**, p.112 [FO-170]: In any graph the number of odd-degree vertices is even (consequence of the Handshake Lemma 2.1.9) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_prop_1_5_18_even_odd_vertices`, `SimpleGraph.even_card_odd_degree_vertices`, `SimpleGraph.sum_degrees_eq_twice_card_edges`
- **Def §1.5.7 @115 (practice problem 9)**, p.115 [FO-167]: Inverse image of a set under a function: f^{-1}(B) = {x : f(x) ∈ B} — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_1_5_7_preimage`, `Set.preimage`
- **Sec 1.4 (Additional Exercises 1) -** [FO-143]: Existence statements (exhibit a witness) and existence-and-uniqueness proofs; constructive vs non-constructive — *not a result* — –

## Chapter 2

112 items; 108 with a Lean name; 39 proved proved here; 62 in Mathlib; 9 not formalized; 2 not a result.


#### Section 2.1

- **Intro §2.1**, p.120 [FO-311]: Multigraph: loops and parallel edges allowed — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_multigraph_loop`, `UndergradKB.Combinatorics.Multigraph`, `Graph`
- **Intro §2.1**, p.121 [FO-318]: Degree sequence: degrees listed in non-increasing order — *proved proved here* — `UndergradKB.Foundations.levin_s2_1_degreeSequence_length`, `UndergradKB.Foundations.levin_s2_1_degreeSequence_sorted`, `UndergradKB.Foundations.levin_s2_1_degreeSequence_sum`, `UndergradKB.Foundations.levin_s2_1_degreeSequence_mem`
- **Intro §2.1**, p.122 [FO-324]: Cycle: closed path with no other repeated vertex — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_cycle_def`, `SimpleGraph.Walk.IsCycle`, `SimpleGraph.Walk.IsCircuit`
- **Intro §2.1**, p.122 [FO-326]: Tree = connected graph with no cycles; forest = graph with no cycles; leaves are degree-1 vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_def`, `SimpleGraph.IsTree`, `SimpleGraph.IsAcyclic`
- **Intro §2.1**, p.122 [FO-349]: Chromatic number: least number of colours in a proper vertex colouring — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_chromatic_le_iff`, `SimpleGraph.chromaticNumber`
- **Def 2.1.2**, p.122 [FO-310]: A (simple) graph is a pair of a vertex set and a set of 2-element subsets of it (edges) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_edge_two_vertices`, `SimpleGraph`
- **Example 2.1.3**, p.123 [FO-560]: two three-vertex graphs with different edge sets are not equal — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_1_3_graphs_not_equal`
- **Example 2.1.4**, p.124 [FO-561]: triangles on abc and uvw are unequal but related by a renaming bijection — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_1_4_equal_vs_isomorphic`
- **Def 2.1.5**, p.124 [FO-312]: Graph isomorphism: a bijection of vertex sets preserving adjacency in both directions; isomorphic graphs — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_2_1_5_iso_adj`, `SimpleGraph.Iso`
- **Example 2.1.6**, p.125 [FO-562]: two 4-vertex graphs unequal, cyclic shift not an isomorphism, another map is — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_1_6_equal_or_isomorphic`
- **Def 2.1.7**, p.126 [FO-313]: Subgraph and induced subgraph — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_2_1_7_induce_adj`, `SimpleGraph.Subgraph`, `SimpleGraph.Subgraph.IsInduced`, `SimpleGraph.induce`
- **Text §2.1**, p.127 [FO-314]: Connected graph: a path (walk) between any two vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_connected_iff`, `SimpleGraph.Connected`, `SimpleGraph.Preconnected`, `SimpleGraph.Reachable`
- **Text §2.1 @127-128**, p.127 [FO-315]: Complete graph K_n: every pair adjacent; unique up to isomorphism — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_complete_adj`, `completeGraph`, `SimpleGraph.top_adj`
- **Example 2.1.8**, p.127 [FO-566]: G2 induced subgraph of G1, G3 subgraph but not induced, G4 not a subgraph — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_1_8_subgraphs`
- **Text §2.1**, p.128 [FO-316]: K_n has n(n-1)/2 = C(n,2) edges — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_complete_edges`, `SimpleGraph.card_edgeFinset_top_eq_card_choose_two`
- **Text §2.1**, p.128 [FO-317]: Degree of a vertex = number of incident edges — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_degree_incident_edges`, `SimpleGraph.degree`
- **Lemma 2.1.9**, p.128 [FO-319]: Handshake Lemma: sum of degrees = twice the number of edges — *in Mathlib* — `UndergradKB.Foundations.Course.levin_lem_2_1_9_handshake`, `SimpleGraph.sum_degrees_eq_twice_card_edges`
- **Example 2.1.10**, p.128 [FO-422]: A graph with degree sequence (4,4,3,3,3,2,1) has 10 edges. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_1_10_edges_from_degrees`
- **Text**, p.128 [FO-318]: Degree sequence: degrees listed in non-increasing order — *proved proved here* — `UndergradKB.Foundations.levin_s2_1_degreeSequence_length`, `UndergradKB.Foundations.levin_s2_1_degreeSequence_sorted`, `UndergradKB.Foundations.levin_s2_1_degreeSequence_sum`, `UndergradKB.Foundations.levin_s2_1_degreeSequence_mem`
- **Text §2.1**, p.129 [FO-321]: Bipartite graph; complete bipartite graph K_{m,n} — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_bipartite_iff_partition`, `UndergradKB.Foundations.Course.levin_s2_1_complete_bipartite_adj`, `SimpleGraph.IsBipartite`, `SimpleGraph.IsBipartiteWith`
- **Text §2.1 @129-130**, p.129 [FO-322]: Named graphs: cycle C_n and path P_n — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_cycle_graph_adj`, `UndergradKB.Foundations.Course.levin_s2_1_path_graph_adj`, `cycleGraph`, `pathGraph`
- **Example 2.1.11**, p.129 [FO-423]: No graph on 9 vertices is regular of degree 7. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_1_11_no_regular_nine_seven`
- **Prop 2.1.12**, p.129 [FO-320]: The number of odd-degree vertices is even — *in Mathlib* — `UndergradKB.Foundations.Course.levin_prop_2_1_12_even_odd_vertices`, `SimpleGraph.even_card_odd_degree_vertices`
- **Glossary §2.1**, p.130 [FO-311]: Multigraph: loops and parallel edges allowed — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_multigraph_loop`, `UndergradKB.Combinatorics.Multigraph`, `Graph`
- **Glossary**, p.130 [FO-321]: Bipartite graph; complete bipartite graph K_{m,n} — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_bipartite_iff_partition`, `UndergradKB.Foundations.Course.levin_s2_1_complete_bipartite_adj`, `SimpleGraph.IsBipartite`, `SimpleGraph.IsBipartiteWith`
- **Glossary**, p.130 [FO-324]: Cycle: closed path with no other repeated vertex — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_cycle_def`, `SimpleGraph.Walk.IsCycle`, `SimpleGraph.Walk.IsCircuit`
- **Glossary §2.1**, p.131 [FO-323]: Walk, trail (no repeated edge), path (no repeated vertex) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_trail_path`, `SimpleGraph.Walk`, `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`
- **Glossary**, p.131 [FO-314]: Connected graph: a path (walk) between any two vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_connected_iff`, `SimpleGraph.Connected`, `SimpleGraph.Preconnected`, `SimpleGraph.Reachable`
- **Glossary**, p.131 [FO-326]: Tree = connected graph with no cycles; forest = graph with no cycles; leaves are degree-1 vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_def`, `SimpleGraph.IsTree`, `SimpleGraph.IsAcyclic`
- **Glossary**, p.131 [FO-337]: Planar graph (drawable in the plane without crossings) and its faces — *not formalized* — `UndergradKB.Foundations.FaceData`, `UndergradKB.Foundations.StraightLineDrawing`, `UndergradKB.Foundations.IsStraightLinePlanar`, `UndergradKB.Foundations.StraightLineDrawing.comap`
- **Glossary**, p.131 [FO-345]: Euler trail (walk using each edge exactly once) and Euler circuit (closed Euler trail) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_4_euler_trail`, `UndergradKB.Foundations.Course.levin_s2_4_euler_circuit`, `SimpleGraph.Walk.IsEulerian`, `SimpleGraph.Walk.IsCircuit`
- **Exercise 2.1.5.11 @134 (unnumbered definition)**, p.134 [FO-325]: Neighbourhood N(v) of a vertex (and closed N[v]) — *proved proved here* — `UndergradKB.Foundations.levin_ex_2_1_5_11_mem_closedNeighborSet`, `UndergradKB.Foundations.levin_ex_2_1_5_11_neighborSet_eq_diff`, `UndergradKB.Foundations.levin_ex_2_1_5_11_card_closedNeighborSet`

#### Section 2.2

- **Def 2.2.2**, p.137 [FO-326]: Tree = connected graph with no cycles; forest = graph with no cycles; leaves are degree-1 vertices — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_def`, `SimpleGraph.IsTree`, `SimpleGraph.IsAcyclic`
- **Prop 2.2.3**, p.139 [FO-327]: A graph is a tree iff between any two distinct vertices there is a unique path — *in Mathlib* — `UndergradKB.Foundations.Course.levin_prop_2_2_3_tree_unique_path`, `SimpleGraph.isTree_iff_existsUnique_path`, `SimpleGraph.IsTree.existsUnique_path`
- **Cor 2.2.4**, p.140 [FO-328]: A graph is a forest iff any two vertices are joined by at most one path — *in Mathlib* — `UndergradKB.Foundations.Course.levin_cor_2_2_4_forest_unique_path`, `SimpleGraph.isAcyclic_iff_subsingleton_path`
- **Prop 2.2.5**, p.140 [FO-329]: A tree with at least two vertices has at least two leaves — *in Mathlib* — `UndergradKB.Foundations.Course.levin_prop_2_2_5_tree_two_leaves`, `SimpleGraph.IsTree.exists_ne_and_degree_eq_one`
- **Prop 2.2.6**, p.141 [FO-330]: A tree with v vertices has v-1 edges (and conversely connected plus v-1 edges gives a tree) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_tree_iff_card_edges`, `SimpleGraph.IsTree.card_edgeFinset`, `SimpleGraph.IsTree.ncard_edgeSet_add_one`, `SimpleGraph.isTree_iff_connected_and_card`
- **Def 2.2.7**, p.142 [FO-331]: Spanning tree of a connected graph: a subgraph that is a tree on all vertices — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_2_2_7_spanning_le`, `SimpleGraph.IsTree`
- **Thm 2.2.8**, p.142 [FO-332]: Every connected graph has a spanning tree — *in Mathlib* — `UndergradKB.Foundations.Course.levin_thm_2_2_8_spanning_tree`, `SimpleGraph.Connected.exists_isTree_le`
- **Example 2.2.9**, p.142 [FO-567]: the 7-vertex graph has two different spanning trees — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_2_9_two_spanning_trees`
- **Text §2.2**, p.143 [FO-333]: Minimum spanning tree of a weighted graph (Prim, Kruskal algorithms mentioned in a footnote) — *proved proved here* — `UndergradKB.Combinatorics.SpanningTree.IsMinSpanningTree`, `UndergradKB.Combinatorics.SpanningTree.exists_isMinSpanningTree`
- **Text §2.2 @143-144**, p.143 [FO-334]: Rooted-tree terminology: root, parent, child, ancestor, descendant, sibling — *not a result* — –
- **Example 2.2.10**, p.144 [FO-568]: the figure is a tree; children, descendants and siblings relative to roots f and a — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_2_10_rooted_tree`
- **Example 2.2.11**, p.144 [FO-336]: Every tree (indeed every forest) is bipartite, equivalently 2-colourable — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_2_2_11_forest_bipartite`, `UndergradKB.Foundations.Course.levin_ex_2_2_11_tree_two_colorable`, `SimpleGraph.IsTree.isBipartite`, `SimpleGraph.IsAcyclic.isBipartite`
- **Text §2.2**, p.145 [FO-335]: Breadth-first and depth-first search — *not a result* — –

#### Section 2.3

- **Intro §2.3 @149-150**, p.149 [FO-337]: Planar graph (drawable in the plane without crossings) and its faces — *not formalized* — `UndergradKB.Foundations.FaceData`, `UndergradKB.Foundations.StraightLineDrawing`, `UndergradKB.Foundations.IsStraightLinePlanar`, `UndergradKB.Foundations.StraightLineDrawing.comap`
- **Unnumbered boxed §2.3**, p.151 [FO-338]: Euler's formula: v - e + f = 2 for a connected planar graph — *not formalized* — `UndergradKB.Foundations.FaceData.euler`
- **Thm 2.3.3**, p.153 [FO-339]: K_5 is not planar — *not formalized* — `UndergradKB.Foundations.PlaneDrawing.edges_le_three_mul_sub_six`, `UndergradKB.Foundations.not_planeDrawing_K5`, `UndergradKB.Foundations.FaceData.euler`, `UndergradKB.Foundations.not_planeFaceData_K5`
- **Text §2.3**, p.154 [FO-341]: Girth: length of a shortest cycle — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_3_girth_top_iff_acyclic`, `UndergradKB.Foundations.Course.levin_s2_3_girth_le_cycle`, `SimpleGraph.girth`, `SimpleGraph.egirth`
- **Text §2.3**, p.154 [FO-342]: For a planar graph with girth g, g*f <= 2e — *not formalized* — `UndergradKB.Foundations.PlaneDrawing.girth_edge_bound`, `UndergradKB.Foundations.PlaneDrawing.girth_edge_bound_div`, `UndergradKB.Foundations.PlaneFaceData.girth_edge_bound`
- **Thm 2.3.4**, p.154 [FO-340]: K_{3,3} is not planar — *not formalized* — `UndergradKB.Foundations.not_planeDrawing_K33`, `UndergradKB.Foundations.FaceData.euler`, `UndergradKB.Foundations.not_planeFaceData_K33`, `UndergradKB.Foundations.not_straightLineDrawing_K33`
- **Text §2.3**, p.155 [FO-343]: Euler's formula holds for convex polyhedra (via planar projection) — *not formalized* — –
- **Example 2.3.6**, p.155 [FO-526]: No polyhedron with three triangles and six pentagons; none with five added heptagons either. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_3_6_no_polyhedra`
- **Thm 2.3.7**, p.156 [FO-344]: There are exactly five regular polyhedra (Platonic solids) — *not formalized* — `UndergradKB.Foundations.levin_thm_2_3_7_platonic_pairs`, `UndergradKB.Foundations.levin_thm_2_3_7_platonic_counts`

#### Section 2.4

- **Text §2.4**, p.161 [FO-323]: Walk, trail (no repeated edge), path (no repeated vertex) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_1_trail_path`, `SimpleGraph.Walk`, `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`
- **Text §2.4**, p.161 [FO-345]: Euler trail (walk using each edge exactly once) and Euler circuit (closed Euler trail) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_4_euler_trail`, `UndergradKB.Foundations.Course.levin_s2_4_euler_circuit`, `SimpleGraph.Walk.IsEulerian`, `SimpleGraph.Walk.IsCircuit`
- **Unnumbered boxed §2.4**, p.164 [FO-346]: Euler's theorem: connected graph has an Euler circuit iff all degrees are even; Euler trail iff at most two odd-degree vertices — *proved proved here* — `UndergradKB.Combinatorics.Euler.isEulerianGraph_iff`, `UndergradKB.Combinatorics.Euler.hasEulerianTrail_iff`, `SimpleGraph.Walk.IsEulerian.even_degree_iff`, `SimpleGraph.Walk.IsEulerian.card_odd_degree`
- **Text §2.4**, p.164 [FO-347]: Hamilton path and Hamilton cycle: visit each vertex exactly once (NP-complete to decide, remark) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_4_hamilton_path`, `UndergradKB.Foundations.Course.levin_s2_4_hamilton_cycle`, `SimpleGraph.Walk.IsHamiltonian`, `SimpleGraph.Walk.IsHamiltonianCycle`
- **Example 2.4.2**, p.165 [FO-569]: Petersen graph has a Hamilton path; K5 with pendant vertices has none — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_4_2_hamilton_paths`

#### Section 2.5

- **Text §2.5**, p.171 [FO-348]: Vertex colouring; proper colouring (adjacent vertices differ) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_proper_coloring`, `UndergradKB.Foundations.Course.levin_s2_5_colorable_iff`, `SimpleGraph.Coloring`, `SimpleGraph.Colorable`
- **Text §2.5**, p.171 [FO-349]: Chromatic number: least number of colours in a proper vertex colouring — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_chromatic_le_iff`, `SimpleGraph.chromaticNumber`
- **Example 2.5.3**, p.173 [FO-350]: chi(K_n) = n; complete bipartite and every bipartite graph with an edge has chi = 2 — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_chromatic_complete`, `UndergradKB.Foundations.Course.levin_ex_2_5_3_bipartite_chromatic_two`, `UndergradKB.Foundations.Course.levin_ex_2_5_3_complete_bipartite_chromatic`, `SimpleGraph.chromaticNumber_top`
- **Example 2.5.3**, p.173 [FO-424]: The complete graph K6 has chromatic number 6. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_5_3_k6_chromatic_number`
- **Text §2.5**, p.174 [FO-350]: chi(K_n) = n; complete bipartite and every bipartite graph with an edge has chi = 2 — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_chromatic_complete`, `UndergradKB.Foundations.Course.levin_ex_2_5_3_bipartite_chromatic_two`, `UndergradKB.Foundations.Course.levin_ex_2_5_3_complete_bipartite_chromatic`, `SimpleGraph.chromaticNumber_top`
- **Thm 2.5.4**, p.174 [FO-352]: Four Color Theorem: every planar graph has chi <= 4 — *not formalized* — –
- **Example 2.5.5**, p.175 [FO-570]: radio interference graph is 5-colorable, not 4-colorable, chromatic number 5 — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_5_5_radio_frequencies`
- **Text §2.5**, p.176 [FO-351]: Trivial bounds: 1 <= chi(G) <= / V / — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_chromatic_bounds`, `SimpleGraph.chromaticNumber_le_card`, `SimpleGraph.Colorable.chromaticNumber_pos`
- **Text §2.5**, p.176 [FO-353]: Clique and clique number — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_5_nclique_iff`, `SimpleGraph.IsClique`, `SimpleGraph.IsNClique`, `SimpleGraph.cliqueNum`
- **Text §2.5**, p.176 [FO-355]: Perfect graph (chi equals clique number) — *proved proved here* — `IsPerfect`
- **Text §2.5**, p.176 [FO-356]: chi(G) <= Delta(G) + 1 — *proved proved here* — `UndergradKB.Combinatorics.chromaticNumber_le_maxDegree_add_one`, `UndergradKB.Combinatorics.colorable_of_degree_le`
- **Thm 2.5.6**, p.176 [FO-354]: chi(G) >= clique number of G — *in Mathlib* — `UndergradKB.Foundations.Course.levin_thm_2_5_6_clique_le_chromatic`, `SimpleGraph.cliqueNum_le_chromaticNumber`, `SimpleGraph.IsClique.card_le_chromaticNumber`
- **Text §2.5**, p.177 [FO-358]: Edge colouring and chromatic index chi'(G); chi'(G) >= Delta(G) — *proved proved here* — `UndergradKB.Foundations.levin_s2_5_maxDegree_le_of_edgeColorable`, `UndergradKB.Foundations.levin_s2_5_maxDegree_le_chromaticIndex`
- **Thm 2.5.7**, p.177 [FO-357]: Brooks' theorem: chi(G) <= Delta(G) unless G is complete or an odd cycle — *proved proved here* — `UndergradKB.Combinatorics.brooks`, `UndergradKB.Combinatorics.brooks_of_not_complete_succ`, `UndergradKB.Combinatorics.chromaticNumber_le_of_brooks`, `UndergradKB.Combinatorics.brooks_two`
- **Example 2.5.8**, p.177 [FO-527]: K6 has a proper edge colouring with 5 colours and none with 4. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_5_8_k6_chromatic_index`
- **Text §2.5**, p.178 [FO-360]: Class 1 / class 2 graphs; bipartite graphs are class 1 (Konig); planar graphs with Delta >= 7 class 1 (history remarks) — *proved proved here* — `UndergradKB.Foundations.IsClassOne`, `UndergradKB.Foundations.IsClassTwo`, `UndergradKB.Foundations.levin_s2_5_class_one_or_two`, `UndergradKB.Foundations.levin_s2_5_bipartite_class_one`
- **Thm 2.5.9**, p.178 [FO-359]: Vizing's theorem: chi'(G) is Delta(G) or Delta(G)+1 — *proved proved here* — `UndergradKB.Foundations.levin_thm_2_5_9_vizing`, `UndergradKB.Foundations.EdgeColoring.edgeColorable_maxDegree_add_one`, `UndergradKB.Foundations.maxDegree_le_chromaticIndex_le`

#### Section 2.6

- **Def 2.6.3**, p.186 [FO-062]: A (binary) relation on A, or from A to B, is a subset of A x A (resp. A x B) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_1_relation_is_subset`, `SetRel`
- **Example 2.6.5**, p.187 [FO-074]: A partial order is a reflexive, antisymmetric, transitive relation (e.g. subset, "is a multiple of") — *in Mathlib* — `UndergradKB.Foundations.Course.levin_rem_2_6_15_partial_order`, `IsPartialOrder`, `PartialOrder`
- **Example 2.6.5**, p.187 [FO-547]: 'is a multiple of' on 1..6 is the listed 14 pairs, has loops, not symmetric — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_5_multiple_of_relation`
- **D057**, p.187 [FO-548]: (6,2) is in the multiple-of relation, (6,4) is not — *proved proved here* — `UndergradKB.Foundations.Course.levin_d057_multiple_of_membership`
- **Def 2.6.6**, p.188 [FO-076]: Inverse relation R^{-1} = {(y,x) : (x,y) in R} — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_7_inverse_relation`, `SetRel.inv`
- **Def 2.6.7**, p.188 [FO-077]: Composition of relations S∘R (apply R, then S) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_2_6_7_comp`, `SetRel.comp`
- **Example 2.6.8**, p.189 [FO-077]: Composition of relations S∘R (apply R, then S) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_2_6_7_comp`, `SetRel.comp`
- **Example 2.6.8**, p.189 [FO-471]: Composition of "is taking" with "is taught by" is the listed ten pairs. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_8_composition`
- **Example 2.6.9**, p.189 [FO-472]: T inverse composed with T relates students sharing a class; only Dirk-Bob and Dirk-Eva fail. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_9_common_class`
- **Def 2.6.10**, p.190 [FO-063]: Reflexive, symmetric, transitive properties of a relation (Levin adds irreflexive and antisymmetric in running text) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_2_refl_symm_trans`, `IsTrans`, `SetRel.IsSymm`
- **Text §2.6.3**, p.191 [FO-063]: Reflexive, symmetric, transitive properties of a relation (Levin adds irreflexive and antisymmetric in running text) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_2_refl_symm_trans`, `IsTrans`, `SetRel.IsSymm`
- **Example 2.6.11**, p.191 [FO-473]: Reflexivity of <=, within-3, divisibility; sums-to-zero is not reflexive. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_11_reflexive`
- **Example 2.6.12**, p.191 [FO-474]: Within-3 and sums-to-zero are symmetric; <= and divisibility are not. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_12_symmetric`
- **Text §2.6.3**, p.192 [FO-075]: A relation is symmetric iff it equals its inverse — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_6_3_symmetric_iff_inv_eq`, `SetRel.inv_eq_self_iff`
- **Example 2.6.13**, p.192 [FO-475]: <= and divisibility are transitive; within-3 and sums-to-zero are not. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_13_transitive`
- **Def 2.6.14**, p.193 [FO-065]: Definition of equivalence relation (reflexive, symmetric, transitive) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_3_equivalence`, `Equivalence`, `Setoid`, `IsEquiv`
- **Remark 2.6.15**, p.193 [FO-074]: A partial order is a reflexive, antisymmetric, transitive relation (e.g. subset, "is a multiple of") — *in Mathlib* — `UndergradKB.Foundations.Course.levin_rem_2_6_15_partial_order`, `IsPartialOrder`, `PartialOrder`
- **Example 2.6.16**, p.193 [FO-064]: Congruence mod n is reflexive, symmetric and transitive on Z (Levin: the mod-2 case, "difference is even") — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s11_2_modEq_equivalence`, `Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans`
- **Example 2.6.17**, p.194 [FO-476]: Having the same degree sequence is an equivalence relation on graphs. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_17_same_degree_sequence`
- **Def 2.6.18**, p.194 [FO-066]: Equivalence class of a under an equivalence relation: [a] = set of x related to a — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_4_class_mem`, `Setoid.classes`, `Setoid.mem_classes`
- **Def 2.6.18**, p.194 [FO-067]: Relation class [a] = {b : (a,b) in R} for an arbitrary (not necessarily equivalence) relation — *proved proved here* — `UndergradKB.Foundations.mem_relClass`
- **Example 2.6.19**, p.194 [FO-067]: Relation class [a] = {b : (a,b) in R} for an arbitrary (not necessarily equivalence) relation — *proved proved here* — `UndergradKB.Foundations.mem_relClass`
- **Example 2.6.19**, p.194 [FO-477]: Relation classes of "is a multiple of" on {1..6}. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_19_multiple_classes`
- **Example 2.6.20**, p.195 [FO-478]: Congruence mod 2 on the integers has exactly two classes, odd and even. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_20_mod_two_classes`
- **Def 2.6.21**, p.196 [FO-069]: Definition of partition of a set (nonempty blocks, cover, pairwise disjoint) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_5_partition`, `Setoid.IsPartition`
- **Example 2.6.22**, p.196 [FO-069]: Definition of partition of a set (nonempty blocks, cover, pairwise disjoint) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_11_5_partition`, `Setoid.IsPartition`
- **Example 2.6.22**, p.196 [FO-479]: Four explicit partitions of {1,...,5}. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_6_22_partitions`
- **Example 2.6.23**, p.196 [FO-071]: Conversely a partition defines an equivalence relation ("same block"), and the two constructions are mutually inverse — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s11_4_partition_equivalence`, `Setoid.mkClasses`, `Setoid.classes_mkClasses`, `Setoid.mkClasses_classes`
- **Thm 2.6.24 @197 (first part)**, p.197 [FO-070]: The equivalence classes of an equivalence relation on A form a partition of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_11_2_classes_partition`, `Setoid.isPartition_classes`, `Setoid.classes_eqv_classes`
- **Thm 2.6.24 @197 (second and third parts)**, p.197 [FO-071]: Conversely a partition defines an equivalence relation ("same block"), and the two constructions are mutually inverse — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s11_4_partition_equivalence`, `Setoid.mkClasses`, `Setoid.classes_mkClasses`, `Setoid.mkClasses_classes`

#### Section 2.7

- **Text §2.7**, p.201 [FO-361]: Matching in a bipartite graph (of A: each vertex of A in exactly one edge, no vertex of B in two); perfect matching — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s2_7_matching_def`, `UndergradKB.Foundations.Course.levin_s2_7_perfect_matching_def`, `SimpleGraph.Subgraph.IsMatching`, `SimpleGraph.Subgraph.IsPerfectMatching`
- **Matching Condition §2.7**, p.202 [FO-362]: Hall's Marriage Theorem: a bipartite graph has a matching of A iff / N(S) / >= / S / for all S subset of A (necessity of the matching condition is the easy half) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_thm_2_7_2_hall`, `UndergradKB.Foundations.Course.levin_thm_2_7_2_hall_family`, `Finset.all_card_le_biUnion_card_iff_exists_injective`, `Fintype.all_card_le_rel_image_card_iff_exists_injective`
- **Thm 2.7.2**, p.202 [FO-362]: Hall's Marriage Theorem: a bipartite graph has a matching of A iff / N(S) / >= / S / for all S subset of A (necessity of the matching condition is the easy half) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_thm_2_7_2_hall`, `UndergradKB.Foundations.Course.levin_thm_2_7_2_hall_family`, `Finset.all_card_le_biUnion_card_iff_exists_injective`, `Fintype.all_card_le_rel_image_card_iff_exists_injective`
- **Example 2.7.3**, p.203 [FO-563]: 52 cards in 13 piles of 4: one card per pile can be chosen with each value once (via Hall) — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_2_7_3_card_piles`
- **Exercise 2.7.3 @204 (definition in exercise)**, p.204 [FO-363]: Alternating path and augmenting path for a partial matching — *proved proved here* — `UndergradKB.Foundations.levin_ex_2_7_3_augmenting_odd_length`

#### Section 2.2

- **Exercise 2.2.7.9** [FO-336]: Every tree (indeed every forest) is bipartite, equivalently 2-colourable — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_2_2_11_forest_bipartite`, `UndergradKB.Foundations.Course.levin_ex_2_2_11_tree_two_colorable`, `SimpleGraph.IsTree.isBipartite`, `SimpleGraph.IsAcyclic.isBipartite`

## Chapter 3

101 items; 100 with a Lean name; 54 proved proved here; 46 in Mathlib; 1 not a result.


#### Section 3.1

- **text §3.1.1**, p.215 [FO-231]: Pascal's rule C(n+1,k) = C(n,k-1) + C(n,k) (1 <= k <= n); every Pascal-triangle entry is the sum of the two above it, with 1s on the boundary; triangle rows are numbered from 0. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_3_pascal`, `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`
- **text §3.1.2**, p.215 [FO-223]: A lattice path is a shortest path between lattice points (steps right/up); the number of lattice paths from (0,0) to (m,n) is C(m+n,m), obtained from the Pascal recursion (paths end with a right step or an up step). — *proved proved here* — `UndergradKB.Combinatorics.IsLatticePath`, `UndergradKB.Combinatorics.ncard_latticePaths`, `UndergradKB.Combinatorics.ncard_latticePaths'`
- **Ex 3.1.3**, p.217 [FO-223]: A lattice path is a shortest path between lattice points (steps right/up); the number of lattice paths from (0,0) to (m,n) is C(m+n,m), obtained from the Pascal recursion (paths end with a right step or an up step). — *proved proved here* — `UndergradKB.Combinatorics.IsLatticePath`, `UndergradKB.Combinatorics.ncard_latticePaths`, `UndergradKB.Combinatorics.ncard_latticePaths'`
- **text §3.1.3**, p.218 [FO-222]: The number of n-bit strings of weight k is C(n,k) (so is the number of lattice paths and of k-subsets; Pascal recursion for B_k^n by last bit). — *proved proved here* — `UndergradKB.Combinatorics.card_bitStrings_with_ones`
- **Def 3.1.4**, p.218 [FO-221]: Definition of n-bit string, its length n, its weight (number of 1s) and the set B_k^n of n-bit strings of weight k. — *proved proved here* — `UndergradKB.Foundations.BitString`, `UndergradKB.Foundations.levin_def_3_1_4_bitstring_count`
- **text §3.1.4**, p.219 [FO-219]: Subsets of {1..n} correspond bijectively to n-bit strings (bit i = 1 iff i is in the subset); k-element subsets correspond to strings of weight k. — *proved proved here* — `UndergradKB.Combinatorics.subsetEquivBits_card`, `UndergradKB.Combinatorics.card_bitStrings`
- **Ex 3.1.5**, p.219 [FO-222]: The number of n-bit strings of weight k is C(n,k) (so is the number of lattice paths and of k-subsets; Pascal recursion for B_k^n by last bit). — *proved proved here* — `UndergradKB.Combinatorics.card_bitStrings_with_ones`
- **Ex 3.1.6**, p.219 [FO-219]: Subsets of {1..n} correspond bijectively to n-bit strings (bit i = 1 iff i is in the subset); k-element subsets correspond to strings of weight k. — *proved proved here* — `UndergradKB.Combinatorics.subsetEquivBits_card`, `UndergradKB.Combinatorics.card_bitStrings`
- **text §3.1.4 "Counting Subsets"**, p.220 [FO-224]: Binomial coefficient: C(n,k) is the number of k-element subsets of an n-element set (0 when k<0 or k>n); also the entry in row n, column k of Pascal's triangle; read "n choose k". — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_3_2_card_powersetCard`, `Nat.choose`, `Finset.card_powersetCard`, `Nat.choose_eq_zero_of_lt`
- **Remark 3.1.7**, p.220 [FO-220]: A bijection between two finite sets shows they have the same cardinality (basic counting technique). — *in Mathlib* — `UndergradKB.Foundations.Course.levin_rem_3_1_7_card_bijection`, `Fintype.card_congr`, `Finset.card_equiv`
- **Ex 3.1.8**, p.220 [FO-224]: Binomial coefficient: C(n,k) is the number of k-element subsets of an n-element set (0 when k<0 or k>n); also the entry in row n, column k of Pascal's triangle; read "n choose k". — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_3_2_card_powersetCard`, `Nat.choose`, `Finset.card_powersetCard`, `Nat.choose_eq_zero_of_lt`
- **Thm 3.1.10**, p.222 [FO-234]: Binomial theorem: (x+y)^n = sum over k of C(n,k) x^k y^(n-k) for n >= 0 (coefficients are Pascal's row n). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_3_1_binomial`, `add_pow`, `Commute.add_pow`
- **Example 3.1.11**, p.222 [FO-407]: Binomial expansion of (x+y)^5 from Pascal's triangle. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_1_11_binomial_expansion`

#### Section 3.2

- **Principle 3.2.3**, p.227 [FO-215]: Addition (sum) principle: for pairwise disjoint finite sets the cardinality of the union is the sum of the cardinalities; for two sets the condition is disjointness. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_2_card_union`, `UndergradKB.Foundations.Course.hammack_fact_3_2_card_biUnion`, `Finset.card_union_eq_card_add_card`, `Finset.card_disjUnion`
- **Example 3.2.4**, p.228 [FO-505]: 52 two-letter words start with A or B. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_4_words_start_a_or_b`
- **Example 3.2.5**, p.228 [FO-506]: 98 ten-bit strings of weight 6 start with 11 or 00. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_5_weight_six_prefix`
- **Ex 3.2.6**, p.229 [FO-216]: Subtraction (complement) principle: if X is a subset of a finite U then the cardinality of U minus X is card U minus card X (count the complement). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_3_card_sdiff`, `Finset.card_sdiff_of_subset`, `Finset.card_compl`, `Finset.card_add_card_compl`
- **Example 3.2.7**, p.229 [FO-507]: 130 two-letter words start with a vowel (sum principle). — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_7_vowel_words_sum`
- **Principle 3.2.8**, p.229 [FO-214]: Multiplication (product) principle: if a list/outcome is built in n steps with a_i choices at step i (number of choices independent of earlier choices), the total is a_1 a_2 ... a_n; for two sets, the size of a product set is the product of sizes. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_1_card_prod`, `UndergradKB.Foundations.Course.hammack_fact_3_1_card_pi`, `Finset.card_product`, `Fintype.card_prod`
- **Example 3.2.9**, p.230 [FO-508]: 130 two-letter words start with a vowel (product principle). — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_9_vowel_words_product`
- **Example 3.2.10**, p.231 [FO-509]: 330 * 84 = 27720 lattice paths from (0,0) to (10,10) through (4,7). — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_10_paths_through_point`
- **Example 3.2.11**, p.231 [FO-510]: 26^3 * 10^3 license plates. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_11_license_plates`
- **Ex 3.2.12**, p.232 [FO-217]: The number of length-n lists with entries from a k-element set, repetition allowed, is k^n; equivalently the number of functions from an n-set to a k-set is k^n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_3_card_fun`, `Fintype.card_fun`, `Fintype.card_pi`
- **Ex 3.2.13**, p.233 [FO-218]: A set with n elements has 2^n subsets (yes/no for each element), equivalently there are 2^n bit strings of length n. — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_3_2_13_card_powerset`, `Finset.card_powerset`
- **Ex 3.2.14**, p.233 [FO-217]: The number of length-n lists with entries from a k-element set, repetition allowed, is k^n; equivalently the number of functions from an n-set to a k-set is k^n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_3_card_fun`, `Fintype.card_fun`, `Fintype.card_pi`
- **Example 3.2.15**, p.234 [FO-511]: 6720 lattice paths from (0,0) to (9,9) through (2,6) or (6,2). — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_15_paths_through_either`
- **Example 3.2.16**, p.235 [FO-408]: 13 two-digit numbers with digits in {1..5} have even digit sum. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_2_16_even_digit_sum`

#### Section 3.3

- **Principle 3.3.2**, p.239 [FO-215]: Addition (sum) principle: for pairwise disjoint finite sets the cardinality of the union is the sum of the cardinalities; for two sets the condition is disjointness. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_2_card_union`, `UndergradKB.Foundations.Course.hammack_fact_3_2_card_biUnion`, `Finset.card_union_eq_card_add_card`, `Finset.card_disjUnion`
- **Example 3.3.3**, p.240 [FO-512]: Twelve 7-bit strings of weight 4 start with 11 or end with 00. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_3_3_start_or_end`
- **Example 3.3.4**, p.241 [FO-513]: Inclusion-exclusion: 15 students failed at least one subject. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_3_4_failed_subjects`
- **Thm 3.3.5**, p.243 [FO-239]: Inclusion-exclusion for two sets: for finite A, B, card(A union B) = card A + card B - card(A inter B). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_6_inclusion_exclusion`, `Finset.card_union_add_card_inter`
- **Example 3.3.6**, p.243 [FO-514]: Same count as 3.3.3 via 10 + 5 - 3 = 12. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_3_6_union_formula`
- **Thm 3.3.7**, p.243 [FO-240]: Inclusion-exclusion for three sets: card(A union B union C) = sum of single cards - sum of pairwise intersections + triple intersection. — *proved proved here* — `UndergradKB.Foundations.hammack_eq_3_5_inclusion_exclusion_three`, `UndergradKB.Foundations.hammack_eq_3_5_inclusion_exclusion_three_int`
- **text §3.3.3**, p.244 [FO-241]: Principle of Inclusion/Exclusion for any number of sets: alternating sum of cardinalities of all intersections of j of the sets (add, subtract, add back, ...). — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s3_3_3_inclusion_exclusion`, `Finset.inclusion_exclusion_card_biUnion`, `Finset.inclusion_exclusion_card_inf_compl`
- **Example 3.3.8**, p.244 [FO-409]: 36 numbers in {1..50} are multiples of 2, 3, or 5. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_3_8_multiples_2_3_5`
- **Ex 3.3.9**, p.245 [FO-217]: The number of length-n lists with entries from a k-element set, repetition allowed, is k^n; equivalently the number of functions from an n-set to a k-set is k^n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_3_card_fun`, `Fintype.card_fun`, `Fintype.card_pi`
- **Ex 3.3.9**, p.245 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **Example 3.3.10**, p.246 [FO-515]: Choices for second letter vary: 4 after w, 26 after a. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_3_10_varying_choices`

#### Section 3.4

- **text §3.4.2**, p.252 [FO-226]: Definition of factorial: n! is the number of non-repetitive length-n lists from n symbols, 0! = 1, 1! = 1, n! = n (n-1)! = n(n-1)...1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_3_1_factorial`, `Nat.factorial`, `Nat.factorial_zero`, `Nat.factorial_succ`
- **Example 3.4.2**, p.252 [FO-410]: Six distinct letters have 6! = 720 arrangements. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_4_2_six_letter_arrangements`
- **Thm 3.4.3**, p.252 [FO-227]: A permutation of a set X is a non-repetitive list using every element of X (equivalently, bijection X to X); an n-element set has n! permutations. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_4_card_perm`, `Fintype.card_perm`, `Fintype.card_equiv`, `List.length_permutations`
- **Ex 3.4.4**, p.253 [FO-227]: A permutation of a set X is a non-repetitive list using every element of X (equivalently, bijection X to X); an n-element set has n! permutations. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_4_card_perm`, `Fintype.card_perm`, `Fintype.card_equiv`, `List.length_permutations`
- **Example 3.4.5**, p.253 [FO-411]: 840 four-letter words from a..g without repeated letters. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_4_5_four_letter_words`
- **Def 3.4.6**, p.254 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **Thm 3.4.7**, p.254 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **Ex 3.4.8**, p.254 [FO-228]: k-permutations: the number P(n,k) of non-repetitive length-k lists from an n-set (= injective functions from a k-set to an n-set) is n(n-1)...(n-k+1), which is n!/(n-k)! for k <= n and 0 for k > n; P(n,n)=n!, P(n,0)=1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_4_card_embedding`, `UndergradKB.Foundations.Course.hammack_fact_3_4_descFactorial_div`, `Fintype.card_embedding_eq`, `Nat.descFactorial`
- **text §3.4.3**, p.255 [FO-229]: P(n,k) = C(n,k) k!: choose the k-subset, then arrange it (equivalently C(n,k) = P(n,k)/k!). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_5_descFactorial_eq_choose_mul`, `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.choose_eq_descFactorial_div_factorial`
- **Ex 3.4.9**, p.255 [FO-229]: P(n,k) = C(n,k) k!: choose the k-subset, then arrange it (equivalently C(n,k) = P(n,k)/k!). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_5_descFactorial_eq_choose_mul`, `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.choose_eq_descFactorial_div_factorial`
- **Thm 3.4.10**, p.256 [FO-225]: Closed formula: C(n,k) = n!/(k!(n-k)!) for 0 <= k <= n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_5_choose_formula`, `Nat.choose_eq_factorial_div_factorial`, `Nat.choose_mul_factorial_mul_factorial`
- **Ex 3.4.11**, p.256 [FO-229]: P(n,k) = C(n,k) k!: choose the k-subset, then arrange it (equivalently C(n,k) = P(n,k)/k!). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_5_descFactorial_eq_choose_mul`, `Nat.descFactorial_eq_factorial_mul_choose`, `Nat.choose_eq_descFactorial_div_factorial`
- **text §3.4.4**, p.259 [FO-230]: Quotient principle: if a finite set is partitioned into classes all of the same size m, then the number of classes is (cardinality of the set)/m. — *proved proved here* — `UndergradKB.Foundations.levin_s3_4_4_quotient_principle`
- **Ex 3.4.13**, p.260 [FO-230]: Quotient principle: if a finite set is partitioned into classes all of the same size m, then the number of classes is (cardinality of the set)/m. — *proved proved here* — `UndergradKB.Foundations.levin_s3_4_4_quotient_principle`

#### Section 3.5

- **Def 3.5.2**, p.265 [FO-242]: A multiset is a collection where elements may repeat and order does not matter; its cardinality counts repeats, and the multiplicity of an element is the number of times it appears (sets are multisets with multiplicity 1). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_8_multiset`, `Multiset`, `Multiset.card`, `Multiset.count`
- **text §3.5.2**, p.267 [FO-244]: The number of non-negative integer solutions of x_1 + ... + x_n = k is C(k+n-1,n-1) (distributing k identical objects to n kids). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_20_nonneg_solutions`, `Finset.card_finsuppAntidiag_nat_eq_choose`
- **Example 3.5.3**, p.268 [FO-557]: jelly bean multisets correspond to flavor-count strings summing to 10 — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_5_3_jelly_beans`
- **Example 3.5.4**, p.268 [FO-558]: book distributions on 5 shelves as count strings summing to 12 and multisets — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_5_4_books_on_shelves`
- **text §3.5.3**, p.269 [FO-243]: Stars and bars: the number of k-element multisets from an n-element set is C(k+n-1,k) = C(k+n-1,n-1) (encode as k stars and n-1 bars); equivalently weakly increasing lists / non-decreasing functions of bounded range. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_7_multisets`, `Sym.card_sym_eq_choose`, `Sym.card_sym_eq_multichoose`, `Nat.multichoose_eq`
- **text §3.5.3**, p.270 [FO-245]: Distributions/solutions with lower bounds: first give each variable its minimum; with all x_i >= 1 the count is C(k-1,n-1); with x_i >= a_i it is C(n + (k - sum a_i) - 1, n-1). — *proved proved here* — `UndergradKB.Combinatorics.card_lowerBoundedSolutions`, `UndergradKB.Combinatorics.card_solutions_pos`, `UndergradKB.Combinatorics.card_positiveCompositions`
- **Ex 3.5.5**, p.270 [FO-243]: Stars and bars: the number of k-element multisets from an n-element set is C(k+n-1,k) = C(k+n-1,n-1) (encode as k stars and n-1 bars); equivalently weakly increasing lists / non-decreasing functions of bounded range. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_7_multisets`, `Sym.card_sym_eq_choose`, `Sym.card_sym_eq_multichoose`, `Nat.multichoose_eq`
- **Ex 3.5.6**, p.271 [FO-243]: Stars and bars: the number of k-element multisets from an n-element set is C(k+n-1,k) = C(k+n-1,n-1) (encode as k stars and n-1 bars); equivalently weakly increasing lists / non-decreasing functions of bounded range. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_3_7_multisets`, `Sym.card_sym_eq_choose`, `Sym.card_sym_eq_multichoose`, `Nat.multichoose_eq`
- **Ex 3.5.7(1)**, p.271 [FO-244]: The number of non-negative integer solutions of x_1 + ... + x_n = k is C(k+n-1,n-1) (distributing k identical objects to n kids). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_20_nonneg_solutions`, `Finset.card_finsuppAntidiag_nat_eq_choose`
- **Ex 3.5.7(2)(3)**, p.271 [FO-245]: Distributions/solutions with lower bounds: first give each variable its minimum; with all x_i >= 1 the count is C(k-1,n-1); with x_i >= a_i it is C(n + (k - sum a_i) - 1, n-1). — *proved proved here* — `UndergradKB.Combinatorics.card_lowerBoundedSolutions`, `UndergradKB.Combinatorics.card_solutions_pos`, `UndergradKB.Combinatorics.card_positiveCompositions`

#### Section 3.6

- **text §3.6**, p.276 [FO-238]: Combinatorial proof: prove an identity by counting one set in two ways (method). — *not a result* — –
- **Ex 3.6.2**, p.279 [FO-231]: Pascal's rule C(n+1,k) = C(n,k-1) + C(n,k) (1 <= k <= n); every Pascal-triangle entry is the sum of the two above it, with 1s on the boundary; triangle rows are numbered from 0. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_3_pascal`, `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`
- **Ex 3.6.3**, p.280 [FO-233]: Boundary values C(n,0) = C(n,n) = 1. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s3_5_choose_boundary`, `Nat.choose_zero_right`, `Nat.choose_self`
- **Ex 3.6.4**, p.280 [FO-231]: Pascal's rule C(n+1,k) = C(n,k-1) + C(n,k) (1 <= k <= n); every Pascal-triangle entry is the sum of the two above it, with 1s on the boundary; triangle rows are numbered from 0. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_3_pascal`, `Nat.choose_succ_succ`, `Nat.choose_succ_succ'`
- **Ex 3.6.5**, p.281 [FO-232]: Symmetry: C(n,k) = C(n,n-k) for 0 <= k <= n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_eq_3_4_choose_symm`, `Nat.choose_symm`
- **Ex 3.6.6**, p.281 [FO-235]: Row sum: C(n,0) + C(n,1) + ... + C(n,n) = 2^n. — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_3_6_6_row_sum`, `Nat.sum_range_choose`
- **text §3.6.3**, p.283 [FO-246]: Permutations of a multiset with n elements and multiplicities p_1..p_k number n!/(p_1! ... p_k!) (multinomial); same count for words with given letter multiplicities. — *proved proved here* — `UndergradKB.Combinatorics.card_arrangements`, `UndergradKB.Combinatorics.card_words_with_multiplicities`
- **Ex 3.6.7**, p.284 [FO-237]: 1(n) + 2(n-1) + 3(n-2) + ... + n(1) = C(n+2,3) (combinatorial proof by the middle element of a 3-subset). — *proved proved here* — `UndergradKB.Foundations.levin_ex_3_6_7_weighted_sum`
- **Ex 3.6.8**, p.285 [FO-236]: Sum of squares: C(n,0)^2 + ... + C(n,n)^2 = C(2n,n). — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_28_sum_choose_sq`, `Nat.sum_range_choose_sq`

#### Section 3.7

- **text §3.7.2**, p.295 [FO-253]: Random experiment, sample space (finite set of outcomes), uniform probability distribution (each outcome has probability 1/size); an event is a subset of the sample space. — *proved proved here* — `UndergradKB.Foundations.levin_s3_7_2_uniform_probability`
- **Note 3.7.2**, p.295 [FO-253]: Random experiment, sample space (finite set of outcomes), uniform probability distribution (each outcome has probability 1/size); an event is a subset of the sample space. — *proved proved here* — `UndergradKB.Foundations.levin_s3_7_2_uniform_probability`
- **Example 3.7.3**, p.296 [FO-516]: Probability of two heads with two coins is 1/4. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_3_two_heads`
- **Def 3.7.4**, p.296 [FO-254]: Probability of an event E in a finite uniform sample space S is card E / card S. — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_3_7_4_uniform_probability`, `ProbabilityTheory.uniformOn_apply_finset`
- **Example 3.7.5**, p.296 [FO-517]: Probability of an even die roll is 1/2. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_5_even_roll`
- **Example 3.7.6**, p.297 [FO-518]: Four of a kind: 2598960 hands, 624 favourable; combination and permutation ratios agree. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_6_four_of_a_kind`
- **Thm 3.7.7**, p.298 [FO-255]: Complement rule: P(complement of E) = 1 - P(E). — *in Mathlib* — `UndergradKB.Foundations.Course.levin_thm_3_7_7_complement`, `MeasureTheory.prob_compl_eq_one_sub`
- **Example 3.7.8**, p.298 [FO-519]: 1023 of 1024 ten-flip sequences contain a head. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_8_at_least_one_head`
- **Example 3.7.9**, p.299 [FO-520]: At least one 6 in four rolls has probability 671/1296 > 1/2; double 6 in 24 rolls is below 1/2. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_9_de_mere`
- **Thm 3.7.10**, p.300 [FO-256]: Union rule: P(A or B) = P(A) + P(B) for disjoint events, and P(A union B) = P(A) + P(B) - P(A inter B) in general. — *in Mathlib* — `UndergradKB.Foundations.Course.levin_thm_3_7_10_union_disjoint`, `UndergradKB.Foundations.Course.levin_thm_3_7_10_union_add_inter`, `MeasureTheory.measure_union`, `MeasureTheory.measure_union_add_inter`
- **Example 3.7.11**, p.300 [FO-521]: Even or less than 3 on a die: 4 outcomes via 3 + 2 - 1. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_11_even_or_small`
- **Example 3.7.12**, p.300 [FO-522]: Even die roll and a head has probability 1/4. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_12_die_and_coin`
- **Def 3.7.13**, p.301 [FO-257]: Events A and B are independent if P(A inter B) = P(A) P(B). — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_3_7_13_independent`, `ProbabilityTheory.IndepSet`, `ProbabilityTheory.indepSet_iff_measure_inter_eq_mul`
- **Example 3.7.14**, p.302 [FO-523]: On a 12-sided die: multiples of 3 and 4 independent, 3 and <7 independent, 4 and <7 not. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_14_independence`
- **Def 3.7.15**, p.303 [FO-258]: Conditional probability: P(A given B) = P(A inter B)/P(B) (= card(A inter B)/card B in the uniform case). — *in Mathlib* — `UndergradKB.Foundations.Course.levin_def_3_7_15_conditional`, `ProbabilityTheory.cond`, `ProbabilityTheory.cond_apply`
- **Example 3.7.16**, p.304 [FO-524]: Probability of sum 7 given at least one 4 on two dice is 2/11. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_16_sum_given_four`
- **Example 3.7.17**, p.304 [FO-525]: Two cards: P(second face \| first red) = 3/13 and P(first red \| second face) = 1/2. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_7_17_red_face`

#### Section 3.8

- **Example 3.8.2**, p.312 [FO-412]: 11 cookies to 3 kids with at most 4 each: 3 ways. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_8_2_cookies_at_most_four`
- **Example 3.8.3**, p.313 [FO-413]: 10 cookies to 4 kids with at most 2 each: 0 ways. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_8_3_cookies_at_most_two`
- **Example 3.8.4**, p.314 [FO-414]: 15 solutions of x1+...+x5 = 13 with each xi between 0 and 3. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_8_4_bounded_solutions`
- **text §3.8.3**, p.315 [FO-251]: A derangement of {1..n} is a permutation with no fixed point (3 elements: 2 derangements; 4 elements: 9). — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s3_8_3_derangements`, `derangements`, `numDerangements`
- **Ex 3.8.6**, p.315 [FO-252]: The number of derangements of n elements is n! - C(n,1)(n-1)! + C(n,2)(n-2)! - ... + (-1)^n C(n,n) 0! (inclusion-exclusion; hat-check problem). — *proved proved here* — `UndergradKB.Combinatorics.card_derangements_sum`
- **Ex 3.8.7**, p.316 [FO-252]: The number of derangements of n elements is n! - C(n,1)(n-1)! + C(n,2)(n-2)! - ... + (-1)^n C(n,n) 0! (inclusion-exclusion; hat-check problem). — *proved proved here* — `UndergradKB.Combinatorics.card_derangements_sum`
- **Example 3.8.9**, p.317 [FO-559]: 5^3 functions, 60 injective Fin 3 -> Fin 5, 5^8 functions Fin 8 -> Fin 5 — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_3_8_9_gifts_as_functions`
- **Ex 3.8.10**, p.318 [FO-249]: The number of surjections from an n-set onto an m-set is the sum over k of (-1)^k C(m,k)(m-k)^n (inclusion-exclusion on the missed codomain elements); equals 2^n - 2 for m=2. — *proved proved here* — `UndergradKB.Combinatorics.card_surjections`
- **Ex 3.8.11**, p.318 [FO-249]: The number of surjections from an n-set onto an m-set is the sum over k of (-1)^k C(m,k)(m-k)^n (inclusion-exclusion on the missed codomain elements); equals 2^n - 2 for m=2. — *proved proved here* — `UndergradKB.Combinatorics.card_surjections`
- **Ex 3.8.12**, p.320 [FO-249]: The number of surjections from an n-set onto an m-set is the sum over k of (-1)^k C(m,k)(m-k)^n (inclusion-exclusion on the missed codomain elements); equals 2^n - 2 for m=2. — *proved proved here* — `UndergradKB.Combinatorics.card_surjections`
- **text §3.8.4**, p.321 [FO-250]: Identity n^n - C(n,1)(n-1)^n + C(n,2)(n-2)^n - ... = n! (surjections from an n-set to itself are bijections). — *proved proved here* — `UndergradKB.Combinatorics.AeqB.euler_identity`
- **Ex 3.8.13**, p.321 [FO-217]: The number of length-n lists with entries from a k-element set, repetition allowed, is k^n; equivalently the number of functions from an n-set to a k-set is k^n. — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_ex_3_3_card_fun`, `Fintype.card_fun`, `Fintype.card_pi`
- **Ex 3.8.14**, p.322 [FO-218]: A set with n elements has 2^n subsets (yes/no for each element), equivalently there are 2^n bit strings of length n. — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_3_2_13_card_powerset`, `Finset.card_powerset`

## Chapter 4

57 items; 55 with a Lean name; 31 proved proved here; 24 in Mathlib; 2 not a result.


#### Section 4.1

- **Example 4.1.3**, p.333 [FO-555]: next terms of triangular, power of 2 and Fibonacci sequences — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_1_3_next_terms`
- **Def 4.1.4**, p.334 [FO-195]: Definition: closed formula for a sequence — *not a result* — –
- **Def 4.1.5**, p.334 [FO-196]: Definition: recursive definition (recurrence relation plus initial conditions); a sequence satisfying the recurrence and initial terms is determined — *proved proved here* — `UndergradKB.Foundations.levin_def_4_1_5_recurrence_determines`, `UndergradKB.Foundations.levin_def_4_1_5_two_term_determines`
- **Example 4.1.6**, p.335 [FO-194]: Binet's formula: F_n = (phi^n - psi^n)/sqrt 5 — *in Mathlib* — `UndergradKB.Combinatorics.Course.KellerTrotter.ex_9_9_5_binet`, `UndergradKB.Foundations.Course.hammack_ex_s10_30_binet`, `Real.coe_fib_eq`
- **Example 4.1.7**, p.335 [FO-391]: Rice-grain recurrence a(n+1)=2a(n)+1, a(1)=1 gives a(n)=2^n-1, a(30)=2^30-1. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_1_7_rice_grains`
- **Example 4.1.8**, p.336 [FO-196]: Definition: recursive definition (recurrence relation plus initial conditions); a sequence satisfying the recurrence and initial terms is determined — *proved proved here* — `UndergradKB.Foundations.levin_def_4_1_5_recurrence_determines`, `UndergradKB.Foundations.levin_def_4_1_5_two_term_determines`
- **Common Sequences**, p.337 [FO-179]: Triangular numbers: 1+2+...+n = n(n+1)/2 (equivalently T_n = C(n+1,2)), proved by reverse-and-add and by induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_triangular`, `Finset.sum_range_id_mul_two`, `Finset.sum_range_id`
- **Common Sequences**, p.337 [FO-190]: Definition of the Fibonacci sequence F_1 = F_2 = 1, F_n = F_{n-1} + F_{n-2} — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_5_fibonacci`, `Nat.fib`, `Nat.fib_add_two`
- **Example 4.1.9**, p.338 [FO-556]: closed formulas reproduce the eight listed sequences — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_1_9_closed_formulas`, `UndergradKB.Foundations.Course.levin_ex_4_1_9_sequence_identities`
- **Example 4.1.10**, p.340 [FO-197]: Sequence of partial sums and sequence of differences; a_{n+1} = a_n + d_n so the sequence is the partial sums of its differences — *proved proved here* — `UndergradKB.Foundations.levin_s4_1_3_differences_partial_sums`
- **Differences §4.1.3**, p.341 [FO-197]: Sequence of partial sums and sequence of differences; a_{n+1} = a_n + d_n so the sequence is the partial sums of its differences — *proved proved here* — `UndergradKB.Foundations.levin_s4_1_3_differences_partial_sums`
- **Example 4.1.12**, p.342 [FO-492]: Recurrence a_n = 3a_{n-1}+2, a_0 = 1 gives 1,5,17,53,161,485. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_1_12_recurrence_terms`
- **Arithmetic Sequences**, p.349 [FO-199]: Arithmetic sequences: constant difference d gives a_n = a + dn (and a_n = a + (n-1)d if indexed from 1) — *proved proved here* — `UndergradKB.Foundations.levin_s4_2_arithmetic_closed_form`

#### Section 4.2

- **Telescoping §4.2.2**, p.350 [FO-198]: Telescoping: sum of (a_{i+1} - a_i) over i < n equals a_n - a_0 — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s4_2_2_telescoping`
- **Example 4.2.2**, p.350 [FO-199]: Arithmetic sequences: constant difference d gives a_n = a + dn (and a_n = a + (n-1)d if indexed from 1) — *proved proved here* — `UndergradKB.Foundations.levin_s4_2_arithmetic_closed_form`
- **Example 4.2.3**, p.351 [FO-200]: Geometric sequences: constant ratio r gives a_n = a r^n — *proved proved here* — `UndergradKB.Foundations.levin_s4_2_geometric_closed_form`
- **Geometric Sequences**, p.351 [FO-200]: Geometric sequences: constant ratio r gives a_n = a r^n — *proved proved here* — `UndergradKB.Foundations.levin_s4_2_geometric_closed_form`
- **Def (D081)**, p.351 [FO-200]: Geometric sequences: constant ratio r gives a_n = a r^n — *proved proved here* — `UndergradKB.Foundations.levin_s4_2_geometric_closed_form`
- **Triangular numbers §4.2.4 @352-353**, p.352 [FO-179]: Triangular numbers: 1+2+...+n = n(n+1)/2 (equivalently T_n = C(n+1,2)), proved by reverse-and-add and by induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_triangular`, `Finset.sum_range_id_mul_two`, `Finset.sum_range_id`
- **Remark 4.2.4**, p.352 [FO-199]: Arithmetic sequences: constant difference d gives a_n = a + dn (and a_n = a + (n-1)d if indexed from 1) — *proved proved here* — `UndergradKB.Foundations.levin_s4_2_arithmetic_closed_form`

#### Section 4.3

- **Reverse and add §4.3.2**, p.360 [FO-179]: Triangular numbers: 1+2+...+n = n(n+1)/2 (equivalently T_n = C(n+1,2)), proved by reverse-and-add and by induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_triangular`, `Finset.sum_range_id_mul_two`, `Finset.sum_range_id`
- **Reverse and Add §4.3.2**, p.360 [FO-201]: Sum of a finite arithmetic sequence by reverse and add: (first + last) * (number of terms) / 2 — *proved proved here* — `UndergradKB.Foundations.levin_s4_3_2_arithmetic_sum`
- **Example 4.3.2**, p.360 [FO-201]: Sum of a finite arithmetic sequence by reverse and add: (first + last) * (number of terms) / 2 — *proved proved here* — `UndergradKB.Foundations.levin_s4_3_2_arithmetic_sum`
- **Example 4.3.3**, p.361 [FO-493]: 6 + 10 + ... + (4n-2) = (n-1)(4n+4)/2. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_3_3_arithmetic_sum`
- **Example 4.3.4**, p.361 [FO-392]: a(0)=2, a(n)=a(n-1)+3n-2 gives 2a(n) = 4 + 3n^2 - n. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_3_4_partial_sums_closed_form`
- **Def §4.3.3**, p.363 [FO-202]: Definition: Delta^k-constant sequence (k-th differences constant) — *proved proved here* — `UndergradKB.Foundations.IsDeltaConstant`, `UndergradKB.Foundations.levin_s4_3_3_delta_constant`, `UndergradKB.Foundations.isDeltaConstant_iff_iterate_succ_eq_zero`
- **Example 4.3.5**, p.363 [FO-202]: Definition: Delta^k-constant sequence (k-th differences constant) — *proved proved here* — `UndergradKB.Foundations.IsDeltaConstant`, `UndergradKB.Foundations.levin_s4_3_3_delta_constant`, `UndergradKB.Foundations.isDeltaConstant_iff_iterate_succ_eq_zero`
- **Theorem 4.3.6**, p.364 [FO-203]: Polynomial Fitting: a sequence has a degree-k polynomial closed formula iff it is Delta^k-constant — *proved proved here* — `UndergradKB.Foundations.polynomial_fitting_le`, `UndergradKB.Foundations.polynomial_fitting`
- **Example 4.3.7**, p.364 [FO-204]: A degree-n polynomial is determined by n+1 values, so n+1 terms can always be fitted (Warning: fitting alone does not identify the sequence) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_warning_4_3_11_poly_determined`, `Polynomial.eq_of_degrees_lt_of_eval_finset_eq`, `Lagrange.interpolate`, `Lagrange.degree_interpolate_lt`
- **Example 4.3.8**, p.365 [FO-205]: Sum of squares: 1^2+...+n^2 = n(n+1)(2n+1)/6 (squares on an n by n chessboard) — *proved proved here* — `UndergradKB.Foundations.hammack_ex_s10_sum_squares`
- **Example 4.3.9**, p.365 [FO-494]: a_n = (3/2)n^2 - n/2 + 2 matches 2,3,7,14,24,37 and the recurrence. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_3_9_fitted_formula`
- **Example 4.3.10**, p.366 [FO-495]: 0,7,50,183,484,1055 is a degree 4 polynomial with constant fourth difference 24. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_3_10_degree_four`
- **Warning 4.3.11**, p.367 [FO-204]: A degree-n polynomial is determined by n+1 values, so n+1 terms can always be fitted (Warning: fitting alone does not identify the sequence) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_warning_4_3_11_poly_determined`, `Polynomial.eq_of_degrees_lt_of_eval_finset_eq`, `Lagrange.interpolate`, `Lagrange.degree_interpolate_lt`

#### Section 4.4

- **Section 4.4.1**, p.373 [FO-190]: Definition of the Fibonacci sequence F_1 = F_2 = 1, F_n = F_{n-1} + F_{n-2} — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_5_fibonacci`, `Nat.fib`, `Nat.fib_add_two`
- **Multiply, Shift, Subtract §4.4.2**, p.375 [FO-206]: Sum of a finite geometric sequence by multiply, shift, subtract: sum_{i<n} x^i = (x^n - 1)/(x - 1) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_4_4_2_geom_sum`, `UndergradKB.Foundations.Course.levin_s4_4_2_geom_sum_mul`, `geom_sum_mul`, `geom_sum_eq`
- **Example 4.4.2**, p.375 [FO-206]: Sum of a finite geometric sequence by multiply, shift, subtract: sum_{i<n} x^i = (x^n - 1)/(x - 1) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_4_4_2_geom_sum`, `UndergradKB.Foundations.Course.levin_s4_4_2_geom_sum_mul`, `geom_sum_mul`, `geom_sum_eq`
- **Example 4.4.3**, p.375 [FO-206]: Sum of a finite geometric sequence by multiply, shift, subtract: sum_{i<n} x^i = (x^n - 1)/(x - 1) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_4_4_2_geom_sum`, `UndergradKB.Foundations.Course.levin_s4_4_2_geom_sum_mul`, `geom_sum_mul`, `geom_sum_eq`
- **Example 4.4.4**, p.376 [FO-393]: The repeating decimal 0.4646... (geometric series, ratio 0.01) sums to 46/99. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_4_4_4_repeating_decimal`
- **Example 4.4.5**, p.377 [FO-209]: Characteristic root technique, distinct roots: solutions of a_n + alpha a_{n-1} + beta a_{n-2} = 0 are a r_1^n + b r_2^n, constants fixed by initial values — *proved proved here* — `UndergradKB.Combinatorics.Recurrence.solutions_distinct_roots`
- **Def (D085)**, p.377 [FO-207]: Characteristic polynomial and characteristic roots of a linear recurrence; r^n is a solution iff r is a characteristic root — *in Mathlib* — `UndergradKB.Foundations.Course.levin_char_roots_geom_solution_iff`, `LinearRecurrence.charPoly`, `LinearRecurrence.geom_sol_iff_root_charPoly`
- **Characteristic Roots**, p.377 [FO-207]: Characteristic polynomial and characteristic roots of a linear recurrence; r^n is a solution iff r is a characteristic root — *in Mathlib* — `UndergradKB.Foundations.Course.levin_char_roots_geom_solution_iff`, `LinearRecurrence.charPoly`, `LinearRecurrence.geom_sol_iff_root_charPoly`
- **Characteristic Roots**, p.377 [FO-209]: Characteristic root technique, distinct roots: solutions of a_n + alpha a_{n-1} + beta a_{n-2} = 0 are a r_1^n + b r_2^n, constants fixed by initial values — *proved proved here* — `UndergradKB.Combinatorics.Recurrence.solutions_distinct_roots`
- **Text §4.4.3**, p.378 [FO-193]: The golden ratio Phi = (1+sqrt 5)/2 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_5_golden_ratio`, `Real.goldenRatio`
- **Example 4.4.6**, p.378 [FO-210]: Characteristic root technique, repeated root: solutions are a r^n + b n r^n — *proved proved here* — `UndergradKB.Combinatorics.Recurrence.solutions_repeated_root`
- **Repeated Roots**, p.378 [FO-210]: Characteristic root technique, repeated root: solutions are a r^n + b n r^n — *proved proved here* — `UndergradKB.Combinatorics.Recurrence.solutions_repeated_root`
- **Def (D086)**, p.379 [FO-208]: Definition: linear homogeneous recurrence relation with constant coefficients — *in Mathlib* — `UndergradKB.Foundations.Course.levin_d086_linear_recurrence_solution`, `LinearRecurrence`, `LinearRecurrence.IsSolution`

#### Section 4.5

- **Induction Proof Structure §4.5.3**, p.385 [FO-171]: Principle of mathematical induction: a base case plus the step P(k) implies P(k+1) proves P(n) for all n from the base on — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_induction`, `Nat.le_induction`
- **Example 4.5.2**, p.386 [FO-179]: Triangular numbers: 1+2+...+n = n(n+1)/2 (equivalently T_n = C(n+1,2)), proved by reverse-and-add and by induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_triangular`, `Finset.sum_range_id_mul_two`, `Finset.sum_range_id`
- **Def §4.5.3**, p.386 [FO-172]: Terminology: basis step, inductive step, inductive hypothesis — *not a result* — –
- **Induction Proof Structure §4.5.3**, p.386 [FO-173]: Induction may start at any base case (S_0, S_m, n >= 5), not only at 1 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_1_induction_any_base`, `Nat.le_induction`
- **Example 4.5.3**, p.387 [FO-184]: x - 1 divides x^n - 1 (instances 4 \\| 5^n - 1 and 5 \\| 6^n - 1) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_3_sub_one_dvd_pow`, `UndergradKB.Foundations.Course.hammack_s10_3_four_dvd_five_pow`, `sub_one_dvd_pow_sub_one`, `sub_dvd_pow_sub_pow`
- **Example 4.5.4**, p.388 [FO-212]: n^2 < 2^n for all integers n >= 5 — *proved proved here* — `UndergradKB.Foundations.levin_ex_4_5_4_sq_lt_two_pow`

#### Section 4.6

- **Example 4.6.2**, p.397 [FO-176]: Two-step induction: P(k) and P(k-1) together give P(k+1), with two base cases (used for second-order recurrences) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_4_6_2_two_step_induction`, `Nat.twoStepInduction`, `Nat.stepInduction`
- **Strong Induction Proof Structure §4.6.2**, p.399 [FO-175]: Strong induction: P(1..k) all true implies P(k+1), plus base cases, proves P(n) for all n; also equivalent in power to ordinary induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_strong_induction`, `Nat.strong_induction_on`, `Nat.case_strong_induction_on`
- **Proposition 4.6.3**, p.400 [FO-211]: An n-square rectangular chocolate bar needs exactly n - 1 breaks to reduce to single squares (strong induction) — *proved proved here* — `UndergradKB.Foundations.levin_prop_4_6_3_chocolate`
- **Example 4.6.4**, p.400 [FO-188]: Fundamental theorem of arithmetic, existence: every integer n > 1 is a product of primes — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_thm_10_1_exists_prime_factorization`, `Nat.prod_primeFactorsList`, `Nat.prime_of_mem_primeFactorsList`, `UniqueFactorizationMonoid.exists_prime_factors`
- **Text §4.6.2**, p.401 [FO-175]: Strong induction: P(1..k) all true implies P(k+1), plus base cases, proves P(n) for all n; also equivalent in power to ordinary induction — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s10_2_strong_induction`, `Nat.strong_induction_on`, `Nat.case_strong_induction_on`

## Chapter 5

49 items; 41 with a Lean name; 18 proved proved here; 23 in Mathlib; 8 not a result.

- **Sec 5.1**, p.409 [FO-001]: A set is a collection of elements; membership relation; sets are finite or infinite — *proved proved here* — `UndergradKB.Foundations.set_membership_finite_infinite`
- **Sec 5.1**, p.409 [FO-002]: Two sets are equal iff they have the same elements (order and repetition irrelevant) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_set_ext`, `Set.ext`

#### Section 5.1

- **Sec 5.1.1**, p.410 [FO-003]: Set-builder notation {expr : rule} describes a set by a membership condition — *not a result* — –
- **Sec 5.1.1**, p.410 [FO-006]: The empty set has no elements; the empty set differs from the set containing the empty set — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_empty_ne_singleton_empty`, `Set.singleton_ne_empty`, `Set.eq_empty_iff_forall_notMem`
- **Sec 5.1.1**, p.412 [FO-004]: Standard number-system sets N, Z, Q, R and conventions (Hammack N starts at 1, Levin N starts at 0) — *not a result* — –
- **Sec 5.1.1**, p.412 [FO-013]: Proper subset: A subset of B and A different from B — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s5_1_2_proper_subset`, `Set.ssubset_def`
- **Sec 5.1.2**, p.413 [FO-012]: A is a subset of B iff every element of A is in B; A is a subset of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_3_subset`, `Set.Subset`, `Set.subset_def`, `Set.Subset.refl`
- **Sec 5.1.2**, p.413 [FO-013]: Proper subset: A subset of B and A different from B — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s5_1_2_proper_subset`, `Set.ssubset_def`
- **Example 5.1.4**, p.413 [FO-455]: True subset/membership statements for A={1..6}, B={2,4,6}, C={1,2,3}. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_1_4_subset_statements`
- **Sec 5.1.2**, p.414 [FO-005]: Cardinality of a finite set is its number of elements; the empty set is the only set of cardinality 0 — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s1_1_card_eq_zero`, `Finset.card`, `Set.ncard`
- **Sec 5.1.2**, p.414 [FO-014]: Fact 1.2: the empty set is a subset of every set — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_2_empty_subset`, `Set.empty_subset`
- **Sec 5.1.2**, p.414 [FO-016]: Power set P(A) is the set of all subsets of A — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_4_mem_powerset`, `Set.powerset`, `Set.mem_powerset_iff`
- **Example 5.1.5**, p.414 [FO-367]: The power set of {1,2,3} is the eight listed subsets. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_1_5_powerset_three`
- **Sec 5.1.3**, p.415 [FO-017]: Union, intersection and difference of two sets — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_5_union_inter_diff`, `Set.union`, `Set.inter`, `Set.diff`
- **Example 5.1.6**, p.415 [FO-015]: Fact 1.3 and Fact 1.4: a finite set with n elements has 2^n subsets, i.e. \\|P(A)\\| = 2^\\|A\\| — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_4_card_powerset`, `Finset.card_powerset`, `Set.ncard_powerset`
- **Example 5.1.6**, p.415 [FO-368]: {23..38} has 16 elements and a 3-element set has a power set of size 8. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_1_6_cardinalities`
- **Sec 5.1.3**, p.416 [FO-021]: Universal set U and complement of A defined as U - A — *proved proved here* — `UndergradKB.Foundations.complement_in_universe`
- **Sec 5.1.3**, p.416 [FO-022]: A \\ B equals A intersected with the complement of B — *in Mathlib* — `UndergradKB.Foundations.Course.levin_s5_1_3_diff_eq_inter_compl`, `Set.sdiff_eq_compl_inter`, `sdiff_eq`
- **Example 5.1.7**, p.416 [FO-369]: Union, intersection and difference computations for A={1..6}, B={2,4,6}, C={1,2,3}, D={7,8,9}. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_1_7_set_operations`
- **Sec 5.1.3**, p.417 [FO-009]: Cartesian product A x B = set of pairs (a,b) with a in A, b in B — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_1_2_mem_prod`, `Set.prod`, `Set.mem_prod`
- **Sec 5.1.3**, p.417 [FO-011]: Cartesian products of n sets and Cartesian powers A^n (n-tuples) — *proved proved here* — `UndergradKB.Foundations.cartesian_power`
- **Example 5.1.8**, p.417 [FO-456]: Adding 4 to {1,2,3} and removing 2 give new sets; original unchanged. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_1_8_add_remove`
- **Example 5.1.9**, p.417 [FO-010]: Fact 1.1: for finite sets, \\|A x B\\| = \\|A\\| \\|B\\| — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_fact_1_1_card_prod`, `Finset.card_product`, `Set.ncard_prod`, `Fintype.card_prod`
- **Example 5.1.9**, p.417 [FO-370]: {1,2} x {3,4,5} is the six listed pairs and {3,4,5}^2 has 9 elements. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_1_9_cartesian_product`
- **Sec 5.1.4**, p.418 [FO-023]: Venn diagrams as informal pictures of set operations — *not a result* — –

#### Section 5.2

- **Text §5.2**, p.423 [FO-078]: A function f : A -> B assigns to each element of A exactly one element of B (Hammack: a relation from A to B in which each x has a unique y; f(x) is the image of x) — *not a result* — –
- **Text §5.2**, p.423 [FO-079]: Domain, codomain and range of a function; range is a subset of the codomain — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_2_range`, `Set.range`, `Set.mem_range`
- **Example 5.2.1**, p.423 [FO-078]: A function f : A -> B assigns to each element of A exactly one element of B (Hammack: a relation from A to B in which each x has a unique y; f(x) is the image of x) — *not a result* — –
- **Example 5.2.1**, p.423 [FO-480]: Range of tripling is multiples of 3; range of g is {a,c}; table function is 3x. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_1_function_ranges`
- **Example 5.2.3**, p.426 [FO-549]: f and g diagrams are functions, h is not (no output at 1, two at 2) — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_3_which_are_functions`
- **Example 5.2.4**, p.427 [FO-099]: Recursive definition of a function on N (initial condition plus recurrence) — *not a result* — –
- **Example 5.2.4**, p.427 [FO-481]: For f(0)=0, f(n+1)=f(n)+2n+1 one gets f(6)=36. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_4_recursive_value`
- **Box §5.2.1**, p.428 [FO-099]: Recursive definition of a function on N (initial condition plus recurrence) — *not a result* — –
- **Example 5.2.5**, p.428 [FO-099]: Recursive definition of a function on N (initial condition plus recurrence) — *not a result* — –
- **Example 5.2.5**, p.428 [FO-550]: recursive definitions determine 3*2^n, 7+2n and n! — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_5_recursive_definitions`
- **Text §5.2.2**, p.429 [FO-082]: Surjective (onto): every element of the codomain is an output — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_surjective`
- **Example 5.2.6**, p.429 [FO-382]: n -> 3n on Z is not surjective; its range is the multiples of 3. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_6_triple_not_surjective`
- **Text §5.2.2**, p.430 [FO-081]: Injective (one-to-one): distinct inputs have distinct outputs — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_injective`
- **Example 5.2.7**, p.430 [FO-383]: n -> 3n on Z is injective. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_7_triple_injective`
- **Box §5.2.2**, p.431 [FO-081]: Injective (one-to-one): distinct inputs have distinct outputs — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_injective`
- **Box §5.2.2**, p.431 [FO-082]: Surjective (onto): every element of the codomain is an output — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_surjective`
- **Text §5.2.2**, p.431 [FO-083]: Bijective = injective and surjective — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_4_bijective`, `Function.Bijective`
- **Text §5.2.3**, p.431 [FO-092]: Image f(X) and preimage (inverse image) f^{-1}(Y) of subsets under a function — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_9_image_preimage`, `Set.image`, `Set.preimage`
- **Example 5.2.8**, p.432 [FO-092]: Image f(X) and preimage (inverse image) f^{-1}(Y) of subsets under a function — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_9_image_preimage`, `Set.image`, `Set.preimage`
- **Example 5.2.8**, p.432 [FO-384]: Image and preimage computations for a 6-element function into {a,b,c,d}. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_8_image_preimage`
- **Example 5.2.9**, p.432 [FO-092]: Image f(X) and preimage (inverse image) f^{-1}(Y) of subsets under a function — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_9_image_preimage`, `Set.image`, `Set.preimage`
- **Example 5.2.9**, p.432 [FO-385]: For g(n)=n^2+1 on Z: g(1)=2, g[{1}]={2}, preimages of {1},{2},{3} are {0},{-1,1},empty. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_9_square_plus_one`
- **Summary §5.2**, p.433 [FO-079]: Domain, codomain and range of a function; range is a subset of the codomain — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_12_2_range`, `Set.range`, `Set.mem_range`
- **Example 5.2.10**, p.433 [FO-482]: Unique function on {1..5} with preimage of 7 of size 5 is constantly 7. — *proved proved here* — `UndergradKB.Foundations.Course.levin_ex_5_2_10_preimage_size`

## Chapter 6

38 items; 38 with a Lean name; 22 proved proved here; 16 in Mathlib.

- **Sec 6.1**, p.441 [FO-425]: The generating series of a sequence a_0, a_1, ... is the power series sum a_n x^n; the sequence is read off its coefficients (starting at a_0) and the series determines the sequence — *in Mathlib* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_1_coeff`, `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_genSeries_injective`, `PowerSeries.mk`, `PowerSeries.coeff_mk`

#### Section 6.1

- **Example 6.1.1**, p.441 [FO-425]: The generating series of a sequence a_0, a_1, ... is the power series sum a_n x^n; the sequence is read off its coefficients (starting at a_0) and the series determines the sequence — *in Mathlib* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_1_coeff`, `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_genSeries_injective`, `PowerSeries.mk`, `PowerSeries.coeff_mk`
- **Sec 6.1**, p.442 [FO-442]: e^x is the generating function of 1, 1, 1/2, 1/6, ..., 1/n!, ... — *in Mathlib* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_exp`, `PowerSeries.exp`, `PowerSeries.coeff_exp`
- **Sec 6.1.1**, p.443 [FO-426]: The generating function for 1, 1, 1, ... is 1/(1-x) — *in Mathlib* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_ones`, `PowerSeries.mk_one_mul_one_sub_eq_one`
- **Sec 6.1.1**, p.443 [FO-427]: Substituting c x for x: 1/(1 - c x) generates 1, c, c^2, ... (1/(1+x) generates 1, -1, 1, ...; 1/(1-3x) generates powers of 3) — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_geometric`, `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_alternating`
- **Sec 6.1.1**, p.443 [FO-428]: Generating functions add termwise and respect constant multiples (2/(1-x) generates 2, 2, 2, ...; 1/(1-x) + 1/(1-3x) generates 3^n + 1) — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_add_smul`, `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_pow_three_add_one`
- **Sec 6.1.1**, p.444 [FO-429]: Multiplying a generating function by x shifts the sequence right, putting a 0 in front — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_shift`
- **Sec 6.1.1**, p.444 [FO-430]: Substituting x^2: 1/(1-x^2) generates 1, 0, 1, 0, ..., x/(1-x^2) generates 0, 1, 0, 1, ..., and their sum is 1/(1-x) — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_even_odd`
- **Sec 6.1.1**, p.444 [FO-431]: Differentiating 1/(1-x) gives 1/(1-x)^2, which generates 1, 2, 3, 4, ... — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_derivative`, `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_naturals`
- **Sec 6.1.1**, p.444 [FO-432]: 1/(1-x)^3 generates the triangular numbers 1, 3, 6, 10, ... — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_1_triangular`
- **Sec 6.1.2**, p.445 [FO-433]: Differencing: if A generates a_0, a_1, ... then (1-x)A generates a_0, a_1 - a_0, a_2 - a_1, ... — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_2_differencing`
- **Example 6.1.2**, p.445 [FO-434]: The odd numbers 1, 3, 5, ... have generating function (1+x)/(1-x)^2 — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_2_odds`
- **Sec 6.1.2**, p.446 [FO-436]: A sequence with a_n = p a_(n-1) + q a_(n-2) has (1 - p x - q x^2) A = a_0 + (a_1 - p a_0) x — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_2_recurrence`
- **Example 6.1.3**, p.446 [FO-435]: The squares 1, 4, 9, 16, ... (a_0 = 1) have generating function (1+x)/(1-x)^3 — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_3_squares`
- **Example 6.1.4**, p.446 [FO-437]: The sequence a_n = 3a_(n-1) - 2a_(n-2), a_0 = 1, a_1 = 3 (1, 3, 7, 15, ...) has generating function 1/(1 - 3x + 2x^2) — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_4_recurrence_gf`
- **Sec 6.1.3**, p.447 [FO-438]: Multiplying generating functions convolves the sequences: the n-th coefficient of AB is a_0 b_n + a_1 b_(n-1) + ... + a_n b_0 — *in Mathlib* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_3_mul`, `PowerSeries.coeff_mul`
- **Sec 6.1.3**, p.447 [FO-440]: Multiplying a generating function by 1/(1-x) gives the generating function of the partial sums — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_s6_1_3_partial_sums`
- **Example 6.1.5**, p.447 [FO-439]: Multiplying 1, 2, 3, ... by 1, 2, 4, 8, ... gives 1, 4, 11, 26, 57, ... (n-th term 2^(n+2) - n - 3), generated by 1/((1-x)^2 (1-2x)) — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_5_product`
- **Example 6.1.6**, p.448 [FO-441]: Solving a_n = 3a_(n-1) - 2a_(n-2), a_0 = 1, a_1 = 3 by generating functions and partial fractions gives a_n = 2^(n+1) - 1 — *proved proved here* — `UndergradKB.Foundations.GeneratingFunctions.levin_ex_6_1_6_solve`

#### Section 6.2

- **Box §6.2.1**, p.453 [FO-105]: Definition of divisibility a ∣ b (b = ac); divisor, multiple; 0 and 1 facts (x ∣ 0, x ∣ x, 1 ∣ n) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_4_dvd`, `dvd_zero`, `dvd_refl`
- **Ex 6.2.1**, p.453 [FO-105]: Definition of divisibility a ∣ b (b = ac); divisor, multiple; 0 and 1 facts (x ∣ 0, x ∣ x, 1 ∣ n) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_4_4_dvd`, `dvd_zero`, `dvd_refl`
- **Box §6.2.1**, p.455 [FO-112]: Division algorithm: existence and uniqueness of q, r with a = qb + r, 0 ≤ r < b — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s4_2_division_algorithm`, `Int.ediv_emod_unique''`
- **Box §6.2.2**, p.455 [FO-125]: Remainder classes modulo b: exactly b classes, partitioning ℤ — *proved proved here* — `UndergradKB.Foundations.exists_unique_remainder`, `UndergradKB.Foundations.remainderClass`, `UndergradKB.Foundations.remainderClasses_partition`
- **Ex 6.2.2**, p.455 [FO-125]: Remainder classes modulo b: exactly b classes, partitioning ℤ — *proved proved here* — `UndergradKB.Foundations.exists_unique_remainder`, `UndergradKB.Foundations.remainderClass`, `UndergradKB.Foundations.remainderClasses_partition`
- **Box §6.2.2**, p.456 [FO-118]: Definition of congruence mod n (Hammack: n ∣ a−b; Levin: same remainder) with notation a ≡ b (mod n) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_def_5_1_modEq_iff_dvd`, `Int.ModEq`, `Int.modEq_iff_dvd`
- **Box §6.2.2 @457 (Congruence and Divisibility; Congruence and Equality)**, p.457 [FO-119]: a ≡ b (mod n) iff same remainder iff n ∣ a−b iff a = b + kn — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s5_2_modEq_equiv`, `Int.modEq_iff_dvd`, `Int.modEq_iff_add_fac`, `Int.ModEq`
- **Box §6.2.3**, p.457 [FO-120]: Congruence mod n is reflexive, symmetric and transitive (an equivalence relation) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_box_6_2_3_modEq_equivalence`, `Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans`
- **Box §6.2.3**, p.458 [FO-121]: Congruence respects addition, subtraction, multiplication (a≡b, c≡d give a±c ≡ b±d, ac ≡ bd); special case ac ≡ bc — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s5_2_modEq_arith`, `Int.ModEq.add`, `Int.ModEq.sub`, `Int.ModEq.mul`
- **Ex 6.2.3**, p.459 [FO-126]: Every natural number is congruent to its digit sum mod 9 (and mod 3), giving the divisibility test — *in Mathlib* — `UndergradKB.Foundations.Course.levin_ex_6_2_3_digit_sum`, `Nat.modEq_nine_digits_sum`, `Nat.nine_dvd_iff`, `Nat.modEq_three_digits_sum`
- **Ex 6.2.4 @459 (uses the power rule stated in the text)**, p.459 [FO-122]: Congruence respects powers: a ≡ b implies a^p ≡ b^p (e.g. a^2 ≡ b^2) — *in Mathlib* — `UndergradKB.Foundations.Course.hammack_s5_2_modEq_pow`, `Int.ModEq.pow`
- **Box §6.2.3**, p.460 [FO-123]: Cancellation: ad ≡ bd (mod n) implies a ≡ b (mod n/gcd(d,n)) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_box_6_2_3_cancel`, `Int.ModEq.cancel_right_div_gcd`
- **Box §6.2.4 @460 (gcd described informally as largest common factor)**, p.460 [FO-110]: Definitions of gcd (largest common divisor, not both zero) and lcm (smallest positive common multiple) — *proved proved here* — `UndergradKB.Foundations.gcd_isGreatest_common_divisor`, `UndergradKB.Foundations.lcm_isLeast_positive_common_multiple`
- **Ex 6.2.5**, p.460 [FO-123]: Cancellation: ad ≡ bd (mod n) implies a ≡ b (mod n/gcd(d,n)) — *in Mathlib* — `UndergradKB.Foundations.Course.levin_box_6_2_3_cancel`, `Int.ModEq.cancel_right_div_gcd`
- **Ex 6.2.6**, p.461 [FO-127]: Linear congruences: if gcd(a,n) does not divide b then ax ≡ b (mod n) has no solution; otherwise solved by dividing out gcd — *proved proved here* — `UndergradKB.Foundations.exists_linear_congruence_iff`, `UndergradKB.Foundations.no_solution_linear_congruence`
- **Box §6.2.4**, p.463 [FO-127]: Linear congruences: if gcd(a,n) does not divide b then ax ≡ b (mod n) has no solution; otherwise solved by dividing out gcd — *proved proved here* — `UndergradKB.Foundations.exists_linear_congruence_iff`, `UndergradKB.Foundations.no_solution_linear_congruence`
- **Box §6.2.5**, p.463 [FO-128]: Linear Diophantine equation ax+by=c: definition, solvable iff gcd(a,b) ∣ c, solving via congruences — *proved proved here* — `UndergradKB.Foundations.exists_linear_diophantine_iff`, `UndergradKB.Foundations.linear_diophantine_solutions`
- **Box §6.2.5 @463 (remark)**, p.463 [FO-129]: Matiyasevich: no general algorithm decides solvability of Diophantine equations (mentioned) — *proved proved here* — `UndergradKB.Foundations.levin_s6_2_5_hilbert_tenth`, `UndergradKB.Foundations.hilbert_tenth_nat`, `UndergradKB.Foundations.re_dioph`, `UndergradKB.Foundations.dprm`
- **Ex 6.2.7**, p.465 [FO-128]: Linear Diophantine equation ax+by=c: definition, solvable iff gcd(a,b) ∣ c, solving via congruences — *proved proved here* — `UndergradKB.Foundations.exists_linear_diophantine_iff`, `UndergradKB.Foundations.linear_diophantine_solutions`
