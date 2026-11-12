# Undergraduate mathematics in Lean 4

[![Lean build](https://github.com/jonhanke/undergraduate-math-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/undergraduate-math-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24119531.svg)](https://doi.org/10.5281/zenodo.24119531)

A Lean 4 library (built on Mathlib) that formalizes eighteen openly available undergraduate textbooks in fourteen
topics, item by item: **linear algebra** (Axler; Hefferon), **abstract algebra** (Judson–Beezer), **combinatorics**
(Keller–Trotter; Petkovšek–Wilf–Zeilberger, *A=B*), **calculus** (OpenStax, Volumes 1–3), **trigonometry** (Corral;
OpenStax *Algebra and Trigonometry*), **geometry** (Petrunin), **precalculus** (Stitz–Zeager), **statistics**
(OpenStax *Introductory Statistics*), **probability** (Grinstead–Snell), **proofs, logic and sets** (Hammack, *Book of
Proof*; Levin, *Discrete Mathematics*), **differential equations** (Lebl, *Notes on Diffy Qs*), **complex analysis**
(Beck–Marchesi–Pixton–Sabalka), **representation theory** (Etingof et al.) and **topology** (Morris, *Topology Without
Tears*). The Lean library is called `UndergradKB`; the repository is undergraduate-math-lean.

- **Book maps**: for each book, a table from every numbered item (theorem, proposition, lemma, corollary, example,
  exercise, definition) to the Lean declaration that formalizes it and its status: [docs/books/](docs/books/).
  They are generated from one master checklist per topic, [docs/coverage/&lt;topic&gt;/checklist.md](docs/coverage/),
  whose notes say what Mathlib has and what this library adds.
- **Course outlines**: for each book, its chapters in order with, for every item, a one-line statement and the
  Lean names a course can cite: [docs/courses/](docs/courses/README.md).
- **Literature statements**: each result from a book is a Lean declaration tagged `@[kb "<source key>" "<locator>"]`,
  with the keys of [`references.bib`](references.bib).
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the repository are the
  deliberate ones in the `Challenge_<Topic>.lean` files, which state the headline results without proofs. The CI
  workflow checks the import rules, builds the library, checks that the headline theorems depend only on the
  standard axioms `propext`, `Classical.choice` and `Quot.sound` ([scripts/check_axioms/](scripts/check_axioms/)),
  checks that every Lean name of the book maps exists ([scripts/check_map_names/](scripts/check_map_names/)), and
  runs `lake comparator` once per topic to check the proved statements against the `Challenge_<Topic>.lean` files.
- **Modular**: one Lean library per topic. A topic imports specific Mathlib modules and never another topic; no
  file imports all of Mathlib ([scripts/check_modularity.py](scripts/check_modularity.py)). `lake build Geometry`
  builds one topic.
- **Course layer**: for the central results Mathlib already proves, a theorem of this library states the result in
  the book's terms and proves it from Mathlib, so every central item of every book has a Lean name a course can cite.

## What's new in 0.2.0

- **Eight new topics, nine new books**: precalculus (Stitz–Zeager), statistics (OpenStax *Introductory Statistics*),
  probability (Grinstead–Snell), proofs, logic and sets (Hammack; Levin), differential equations (Lebl), complex
  analysis (Beck–Marchesi–Pixton–Sabalka), representation theory (Etingof et al.) and topology (Morris), each with
  its master checklist, book maps and course outlines.
- **More in the six topics of 0.1.0**: new work in calculus (Green's, Stokes's and the divergence theorems on glued
  regions, winding numbers), combinatorics (graph theory, the Lovász local lemma, the hypergeometric summation
  theorems of Gauss, Dougall and Dixon, more of *A=B*'s algorithms), abstract algebra and geometry (the neutral
  plane: Petrunin's theorems are now derived from the axioms of a neutral plane, not only checked in its models).
- **76 headline theorems** (29 in 0.1.0), with one `Challenge_<Topic>.lean` / `Solution_<Topic>.lean`
  pair and one `lake comparator` check per topic; new highlights below are marked *(new)*.

## The topics

| topic | books | items of the books | Lean modules | lines of Lean | headline theorems |
|---|---|---|---|---|---|
| Linear algebra | 2 | 817 | 54 | 16,005 | 3 |
| Abstract algebra | 1 | 518 | 51 | 11,448 | 9 |
| Combinatorics | 2 | 670 | 213 | 56,002 | 15 |
| Calculus | 1 | 1327 | 98 | 30,434 | 2 |
| Trigonometry | 2 | 375 | 42 | 7,458 | 4 |
| Geometry | 1 | 354 | 81 | 44,037 | 9 |
| Precalculus | 1 | 329 | 29 | 6,528 | 2 |
| Statistics | 1 | 118 | 26 | 4,861 | 5 |
| Probability | 1 | 218 | 42 | 11,565 | 11 |
| Proofs, logic and sets | 2 | 599 | 39 | 4,373 | 0 |
| Differential equations | 1 | 415 | 27 | 7,899 | 3 |
| Complex analysis | 1 | 265 | 32 | 7,782 | 2 |
| Representation theory | 1 | 271 | 113 | 38,550 | 2 |
| Topology | 1 | 814 | 68 | 19,014 | 9 |
| **total** | 18 | 7090 | 915 | 265,956 | 76 |

*Items*: the item entries of the books in their maps. *Lean modules* and *lines* count the files under
`UndergradKB/<Topic>/` and the topic's root file. *Headline theorems*: the theorems of `Challenge_<Topic>.lean`
(the topic *proofs, logic and sets* has none: every result it proves is in Mathlib or its Archive, or is an
exercise).

## The books

| topic | book | licence | items | rows | proved here | in Mathlib | partly in Mathlib | not formalized | not a result | items with a Lean name | course outline |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Linear algebra | [S. Axler, *Linear Algebra Done Right*, 4th ed., Springer, 2024 (open access)](docs/books/axler2024.md) | CC BY-NC 4.0 | 465 | 436 | 142 | 294 | 0 | 0 | 0 | 464 (99.8%) | [outline](docs/courses/linear-algebra/axler2024.md) |
| Linear algebra | [J. Hefferon, *Linear Algebra*, 4th ed., 2020](docs/books/hefferon2020.md) | GNU FDL or CC BY-SA 3.0 US, at the reader's choice | 352 | 296 | 121 | 173 | 0 | 0 | 2 | 351 (99.7%) | [outline](docs/courses/linear-algebra/hefferon2020.md) |
| Abstract algebra | [T. W. Judson and R. A. Beezer, *Abstract Algebra: Theory and Applications*, 2026 edition](docs/books/judson2026.md) | GNU FDL 1.2 or later | 518 | 445 | 148 | 295 | 0 | 2 | 0 | 517 (99.8%) | [outline](docs/courses/abstract-algebra/judson2026.md) |
| Combinatorics | [M. T. Keller and W. T. Trotter, *Applied Combinatorics*, 2017 edition](docs/books/kellertrotter2017.md) | CC BY-SA 4.0 | 419 | 329 | 185 | 130 | 0 | 11 | 3 | 404 (96.4%) | [outline](docs/courses/combinatorics/kellertrotter2017.md) |
| Combinatorics | [M. Petkovšek, H. S. Wilf and D. Zeilberger, *A=B*, A K Peters, 1996](docs/books/petkovsekwilfzeilberger1996.md) | © 1996 A K Peters | 251 | 224 | 177 | 21 | 1 | 22 | 3 | 231 (92.0%) | [outline](docs/courses/combinatorics/petkovsekwilfzeilberger1996.md) |
| Calculus | [G. Strang, E. Herman et al., *Calculus*, Volumes 1–3, OpenStax, 2016](docs/books/openstax-calculus.md) | CC BY-NC-SA 4.0 | 1327 | 690 | 351 | 272 | 0 | 0 | 67 | 1233 (92.9%) | [outline](docs/courses/calculus/openstax-calculus.md) |
| Trigonometry | [M. Corral, *Trigonometry*](docs/books/corraltrig.md) | GNU FDL 1.3 or later | 170 | 156 | 88 | 64 | 0 | 0 | 4 | 164 (96.5%) | [outline](docs/courses/trigonometry/corraltrig.md) |
| Trigonometry | [J. Abramson et al., *Algebra and Trigonometry*, 2nd ed., OpenStax](docs/books/openstaxalgtrig2e.md) | CC BY-NC-SA 4.0 | 205 | 129 | 81 | 43 | 0 | 0 | 5 | 198 (96.6%) | [outline](docs/courses/trigonometry/openstaxalgtrig2e.md) |
| Geometry | [A. Petrunin, *Euclidean Plane and its Relatives: a minimalist introduction*, 3rd ed. (arXiv:1302.1630v25, 2025)](docs/books/petrunin2025.md) | CC BY-SA 4.0 | 354 | 352 | 228 | 100 | 0 | 6 | 18 | 342 (96.6%) | [outline](docs/courses/geometry/petrunin2025.md) |
| Precalculus | [C. Stitz and J. Zeager, *Precalculus*, corrected edition, 2013](docs/books/stitzzeager2013.md) | CC BY-NC-SA 3.0 | 329 | 294 | 176 | 108 | 0 | 0 | 10 | 318 (96.7%) | [outline](docs/courses/precalculus/stitzzeager2013.md) |
| Statistics | [B. Illowsky, S. Dean et al., *Introductory Statistics*, 2nd ed., OpenStax, 2023](docs/books/openstaxintrostats2e.md) | CC BY-NC-SA 4.0 | 118 | 117 | 56 | 29 | 8 | 4 | 20 | 94 (79.7%) | [outline](docs/courses/statistics/openstaxintrostats2e.md) |
| Probability | [C. M. Grinstead and J. L. Snell, *Introduction to Probability*, 2nd ed., American Mathematical Society (version of 4 July 2006)](docs/books/grinsteadsnell2006.md) | GNU FDL | 218 | 129 | 77 | 51 | 0 | 1 | 0 | 217 (99.5%) | [outline](docs/courses/probability/grinsteadsnell2006.md) |
| Proofs, logic and sets | [R. Hammack, *Book of Proof*, 3rd ed. (edition 3.4), 2018](docs/books/hammack2018.md) | CC BY-NC-ND 4.0 | 276 | 240 | 50 | 163 | 0 | 1 | 26 | 240 (87.0%) | [outline](docs/courses/foundations/hammack2018.md) |
| Proofs, logic and sets | [O. Levin, *Discrete Mathematics: An Open Introduction*, 4th ed.](docs/books/levin2025.md) | CC BY-NC-SA 4.0 | 323 | 232 | 54 | 140 | 0 | 11 | 27 | 280 (86.7%) | [outline](docs/courses/foundations/levin2025.md) |
| Differential equations | [J. Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11, 2026](docs/books/lebldiffyqs2026.md) | CC BY-NC-SA 4.0 or CC BY-SA 4.0, at the reader's choice | 415 | 260 | 128 | 50 | 25 | 44 | 13 | 341 (82.2%) | [outline](docs/courses/differential-equations/lebldiffyqs2026.md) |
| Complex analysis | [M. Beck, G. Marchesi, D. Pixton and L. Sabalka, *A First Course in Complex Analysis*, edition 1.6, 2025](docs/books/beck2025.md) | CC BY 4.0 | 265 | 161 | 50 | 89 | 11 | 4 | 7 | 251 (94.7%) | [outline](docs/courses/complex-analysis/beck2025.md) |
| Representation theory | [P. Etingof, O. Golberg, S. Hensel, T. Liu, A. Schwendner, D. Vaintrob and E. Yudovina, *Introduction to Representation Theory*, American Mathematical Society, 2011 (arXiv:0901.0827v5)](docs/books/etingof2011.md) | arXiv non-exclusive distribution licence | 271 | 266 | 186 | 73 | 0 | 7 | 0 | 270 (99.6%) | [outline](docs/courses/representation-theory/etingof2011.md) |
| Topology | [S. A. Morris, *Topology Without Tears*, version of 6 August 2024](docs/books/morris2024.md) | © S. A. Morris, free download from the author | 814 | 703 | 228 | 384 | 23 | 64 | 4 | 730 (89.7%) | [outline](docs/courses/topology/morris2024.md) |

*Items*: the item entries of the book in its map. The other counts are checklist rows (one row per result; a
result stated in two books of a topic is one row, counted in both). *Proved here*: proved in this library with only
the standard axioms. *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration, and
for central results a course-layer theorem of this library. *Partly in Mathlib*: only part of the item is
formalized. *Not formalized*: a gap (see each checklist). *Not a result*: a definition, notation or remark.
*Items with a Lean name*: items whose line in the course outline cites a Lean declaration that exists.

**Licences of the books.** The books are cited, never copied: this repository holds item numbers, page numbers,
Lean statements and one-line paraphrases of our own, and none of the books' text. Axler: CC BY-NC 4.0
(open access, Springer). Hefferon: GNU FDL or CC BY-SA 3.0 US. Judson–Beezer: GNU FDL 1.2 or later.
Keller–Trotter: CC BY-SA 4.0. OpenStax *Calculus*, *Algebra and Trigonometry* and *Introductory Statistics*: CC
BY-NC-SA 4.0. Corral: GNU FDL 1.3 or later. Petrunin: CC BY-SA 4.0. Stitz–Zeager: CC BY-NC-SA 3.0. Grinstead–Snell:
GNU FDL. Hammack: CC BY-NC-ND 4.0. Levin: CC BY-NC-SA 4.0. Lebl, *Notes on Diffy Qs*: CC BY-NC-SA 4.0 or CC BY-SA
4.0. Beck–Marchesi–Pixton–Sabalka: CC BY 4.0. *A=B*: © 1996 A K Peters, made freely available by its authors with
the publisher's consent. Etingof et al. (arXiv non-exclusive distribution licence) and Morris (© the author, free
download from the author): these three books are cited only. We thank the authors for making their books openly
available.

## Highlights

Every result listed here is a headline theorem of a `Challenge_<Topic>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in neither
Mathlib nor [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (main, 2026-11-07), read statement by statement;
related results of those libraries are cited next to each headline in the challenge files. The statements have
**not yet been reviewed by a human** (see Provenance).

**Linear algebra** ([`Challenge_LinearAlgebra.lean`](Challenge_LinearAlgebra.lean))

- **The Jordan normal form:** over an algebraically closed field, every operator on a finite-dimensional space has a
  basis in which its matrix is block diagonal with Jordan blocks (`jordan_normal_form`, Axler 8.46), and two similar
  Jordan matrices have the same blocks up to order (`jordan_form_unique`, Hefferon Five.IV.2.9). Related: Mathlib has
  the Jordan–Chevalley decomposition; Tau Ceti has Jordan-chain bases and the Jordan partition of nilpotent maps.
- **Schur's triangularization:** every operator on a finite-dimensional complex inner product space has an
  upper-triangular matrix in some orthonormal basis (`schur_triangularization`, Axler 6.38).

**Abstract algebra** ([`Challenge_AbstractAlgebra.lean`](Challenge_AbstractAlgebra.lean))

- **$`\pi`$ is transcendental** (`transcendental_pi`; used in Judson–Beezer § 21.3). Related: Mathlib has the
  analytic part of the Lindemann–Weierstrass theorem; Tau Ceti proves the Lindemann–Weierstrass theorem, which implies
  this, but does not state it. The proof here is self-contained over Mathlib.
- **Constructible numbers:** a real number is constructible with straightedge and compass if and only if it lies in
  a tower of square-root extensions of $`\mathbb Q`$ (`constructible_iff_sqrt_tower`, Theorem 21.3.7); hence **the
  three classical problems are impossible**: $`\sqrt[3]2`$, $`\cos(\pi/9)`$ and $`\sqrt\pi`$ are not constructible
  (`not_constructible_cbrt_two`, `not_constructible_cos_pi_div_nine`, `not_constructible_sqrt_pi`).
- **An explicit quintic not solvable by radicals:** $`x^5 - 6x^3 - 27x - 3`$ (`quintic_not_solvable_by_radicals`,
  Example 23.3.7). Related: Mathlib proves that solvability by radicals implies a solvable Galois group, without an
  explicit polynomial.
- *(new)* **The crystallographic restriction:** a linear map of finite order of the plane preserving a lattice has
  order 1, 2, 3, 4 or 6 (`crystallographic_restriction`, Theorem 12.2.9); **the finite subgroups of $`O(2)`$ are
  cyclic or dihedral** (`finite_subgroup_orthogonal_two`, Theorem 12.2.4); **the BCH bound** for cyclic codes
  (`bch_bound`, Theorem 22.2.8).

**Combinatorics** ([`Challenge_Combinatorics.lean`](Challenge_Combinatorics.lean))

- **Dilworth's theorem:** a finite poset is a union of as many chains as the size of its largest antichain, and no
  fewer (`dilworth`, Keller–Trotter Theorem 6.17).
- **Brooks's theorem:** a connected graph of maximum degree at most $`k \ge 3`$ that is not complete is
  $`k`$-colourable (`brooks`).
- **Cayley's formula:** there are $`n^{n-2}`$ labelled trees on $`n`$ vertices (`cayley_formula`, Theorem 5.39).
- **Stable matchings:** a stable matching always exists, and the proposal algorithm of Gale and Shapley finds one
  (`stable_matching_exists`, `gale_shapley_correct`).
- **The Gale–Ryser theorem:** a 0–1 matrix with given row and column sums exists if and only if the conjugate of the
  row sums dominates the column sums (`gale_ryser`, Theorem 16.12).
- **A=B's algorithms, as theorems:** Gosper's algorithm decides whether a hypergeometric term has a hypergeometric
  antidifference and returns it (`gosper_algorithm`); Sister Celine's fundamental theorem: every proper hypergeometric
  term satisfies a nontrivial recurrence free of the summation variable (`sister_celine`, A=B Theorem 4.4.1);
  Petkovšek's algorithm Hyper is complete: a linear recurrence with polynomial coefficients has a hypergeometric
  solution if and only if its finite candidate set contains one (`hyper_complete`, A=B Theorem 8.4.1). These are
  mathematical decision and correctness theorems (the outputs are chosen classically), not executable programs.
- *(new)* **Euler's theorem:** a finite graph has an Euler circuit if and only if it is connected and all degrees are
  even (`euler_circuit_iff`, Theorem 5.13; Mathlib has only the "only if"). **Dirac's theorem:** minimum degree at
  least $`n/2`$ gives a Hamiltonian cycle (`dirac`, Theorem 5.18). **The Lovász local lemma** (`lovasz_local_lemma`,
  Lemma 16.14).
- *(new)* **Hypergeometric summation theorems** of *A=B*'s list: Gauss's $`{}_2F_1(a,b;c;1)`$, Dougall's
  $`{}_7F_6`$ and Dixon's $`{}_3F_2`$ (`gauss_hypergeometric_sum`, `dougall_sum`, `dixon_sum`).

**Calculus** ([`Challenge_Calculus.lean`](Challenge_Calculus.lean))

- **Riemann's rearrangement theorem:** a conditionally convergent real series can be rearranged to converge to any
  real number (`riemann_rearrangement`, OpenStax Volume 2, § 5.5).
- **The error bound of Simpson's rule:** $`|S_n - \int_a^b f| \le M(b-a)^5/(180 n^4)`$ when $`|f^{(4)}| \le M`$
  (`simpson_error_bound`, Volume 2, § 3.6).

**Trigonometry** ([`Challenge_Trigonometry.lean`](Challenge_Trigonometry.lean))

- **Heron's formula** for the area of a triangle in any Euclidean affine space (`heron`, Corral § 2.4).
- **The law of tangents** $`\frac{a-b}{a+b} = \frac{\tan\frac{A-B}{2}}{\tan\frac{A+B}{2}}`$ (`law_of_tangents`,
  Corral Theorem 2.3).
- **The fixed point of the cosine:** $`\cos x = x`$ has exactly one real solution, in $`[0.72, 0.76]`$
  (`cos_eq_self_existsUnique`), and iterating the cosine from any start converges to it (`tendsto_iterate_cos`)
  (Corral § 6.2).

**Geometry** ([`Challenge_Geometry.lean`](Challenge_Geometry.lean))

- **The Gauss–Wantzel theorem:** the regular $`n`$-gon is constructible with ruler and compass if and only if
  $`\varphi(n)`$ is a power of 2 (`gauss_wantzel`, Petrunin Theorem 19.6).
- **The Wallace–Bolyai–Gerwien theorem:** two polygonal sets of the plane with the same positive area are
  equidecomposable (`wallace_bolyai_gerwien`, Chapter 20).
- **The Poncelet–Steiner theorem:** a ruler and one circle with its centre construct the same points as ruler and
  compass (`poncelet_steiner`, Chapter 19).
- **Desargues's theorem** (with its converse) and **Pappus's theorem** in the real projective plane (`desargues`,
  `pappus`).
- *(new)* **The fundamental theorems of affine and of projective geometry** for the real plane
  (`fundamental_affine`, Theorem 14.12; `fundamental_projective`, Theorem 15.2).
- *(new)* **Neutral geometry from the axioms:** in any plane satisfying Petrunin's Axioms I to IV, the parallel axiom
  is equivalent to each of six classical conditions (`neutral_plane_parallel_axiom`, Theorem 11.16), and the angle
  sum of a triangle is at most $`\pi`$ (`saccheri_legendre`, Theorem 11.10).

**Precalculus** *(new)* ([`Challenge_Precalculus.lean`](Challenge_Precalculus.lean))

- **Descartes' rule of signs** in full: the number of sign changes of the coefficients equals the number of positive
  zeros plus an even number, and likewise for negative zeros (`descartes_rule_of_signs`,
  `descartes_rule_of_signs_neg`, Stitz–Zeager Theorem 3.10). Related: Mathlib has the inequality only.

**Statistics** *(new)* ([`Challenge_Statistics.lean`](Challenge_Statistics.lean))

- **The sampling distributions of the normal-theory tests:** for a sample of independent normal observations, the
  sample mean and sample variance are independent and $`(n-1)s^2/\sigma^2`$ is chi-square with $`n-1`$ degrees of
  freedom (`indepFun_sampleMean_sampleVariance`, `hasLaw_sampleVariance_chiSquared`); the t statistic has the
  Student t law (`hasLaw_tStatistic`); the F statistic of one-way analysis of variance has the F law
  (`hasLaw_fStatistic`); and the t statistic of the correlation coefficient has the Student t law, given the
  predictors (`hasLaw_correlation_tStatistic`). Related: Tau Ceti has the chi-square, Student t and F laws, but no
  statement about samples; Mathlib has none of these laws.

**Probability** *(new)* ([`Challenge_Probability.lean`](Challenge_Probability.lean))

- **Finite Markov chains:** the powers of a regular transition matrix converge to a matrix with equal positive rows
  (`regular_pow_tendsto`, Grinstead–Snell Theorem 11.7); for ergodic chains the averages converge
  (`ergodic_cesaro_tendsto`); absorbing chains are absorbed with probability one, with expected absorption times
  and absorption probabilities given by the fundamental matrix (`absorption_certain`, `hasSum_absorption_time`,
  `absorption_prob_tendsto`, Theorems 11.3–11.6).
- **Pólya's theorem:** the simple random walk returns to its start with probability one on $`\mathbb Z^2`$ and with
  probability less than one on $`\mathbb Z^3`$ (`polya_two`, `polya_three`). Related: Tau Ceti has dimension one.
- **The arc sine law** for the time a fair coin game spends in the lead (`arcsine_law_lead`, Theorem 12.4).
- **Riffle shuffles:** an $`a`$-shuffle followed by a $`b`$-shuffle is an $`ab`$-shuffle, and an ordering with
  $`r`$ rising sequences arises from $`\binom{n+a-r}{n}`$ of the $`a`$-shuffles (`riffle_shuffle_composition`,
  `card_riffle_shuffles`, Theorems 3.10, 3.11).
- **The local limit theorem** for sums of independent integer-valued variables (`local_limit_theorem`,
  Theorem 9.3).

**Differential equations** *(new)* ([`Challenge_DifferentialEquations.lean`](Challenge_DifferentialEquations.lean))

- **Uniqueness of the Laplace transform** (Lerch's theorem, `laplace_unique`, Lebl Theorem 6.1.3).
- **The general solution of a linear equation of order $`n`$:** $`n`$ independent solutions span all solutions
  (`linN_general_solution`, Theorem 2.3.3).
- **The general solution of the wave equation:** $`y = F(x + at) + G(x - at)`$ (`wave_general_solution`, § 4.8).

**Complex analysis** *(new)* ([`Challenge_ComplexAnalysis.lean`](Challenge_ComplexAnalysis.lean))

- **The Casorati–Weierstrass theorem** (`casorati_weierstrass`, Beck et al. Theorem 9.1.9).
- **The reciprocity law for Dedekind sums** (`dedekind_sum_reciprocity`, § 10.4).

**Representation theory** *(new)* ([`Challenge_RepresentationTheory.lean`](Challenge_RepresentationTheory.lean))

- **Frobenius's factorization of the group determinant** into irreducible factors, one per irreducible
  representation, with multiplicity its dimension (`groupDeterminant_factorization`, Etingof et al. Theorem 4.7).
- **Dixmier's lemma:** endomorphisms of an irreducible representation of countable dimension are scalars
  (`dixmier_lemma`, Problem 1.23).

**Topology** *(new)* ([`Challenge_Topology.lean`](Challenge_Topology.lean))

- **The period three theorem:** a continuous map of the line with a point of period 3 has points of every period
  (`period_three`, Morris Theorem A3.6.2).
- **Peano's curve:** a continuous map of $`[0,1]`$ onto $`[0,1]^n`$ (`peano_curve`, Theorem 9.5.9).
- **The Banach–Mazur theorem:** every separable normed space embeds isometrically in $`C([0,1])`$ (`banach_mazur`).
- **Closed subgroups of $`\mathbb R^n`$** are $`\mathbb R^p \times \mathbb Z^q`$, their quotients
  $`\mathbb R^c \times \mathbb T^d`$, and closed subgroups of tori are a torus times a finite group
  (`closed_subgroup_equiv`, `quotient_closed_subgroup_equiv`, `closed_subgroup_torus_equiv`).
- **The Wallman compactification**, and it is the Stone–Čech compactification exactly for normal spaces
  (`wallman_compactification`, `normalSpace_iff_wallman_eq_stoneCech`).
- **Pontryagin–van Kampen duality** for $`\mathbb R^a \times \mathbb T^b \times \mathbb Z^c`$
  (`pontryagin_duality_real_circle_int`).

**Main statements.** To check what is claimed, read the thirteen files `Challenge_<Topic>.lean`: they state the
results above (76 theorems), with a docstring for each and a list of the library definitions the
statements use; every proof there is a deliberate `sorry`. The matching `Solution_<Topic>.lean` files prove the same
statements by appeal to the library theorems, and `lake comparator`, configured per topic by
`comparator/<Topic>.json` (the topics are listed in [`comparator.json`](comparator.json)), checks that each proved
statement is exactly the one in the challenge file and uses only the standard axioms. The check is run one topic at
a time: each needs only the files of its topic. [`formalization.yaml`](formalization.yaml) records the scope,
sources, divergences, provenance and review status in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Also proved here, not headlines because Mathlib or Tau Ceti has them:** the singular value and polar
decompositions, the pseudoinverse and the complex spectral theorem (Tau Ceti); the Schwarz–Pick lemma and the area
of a hyperbolic triangle as its angle defect (Tau Ceti); Green's theorem on parametrized and glued regions, Stokes's
theorem on parametrized surfaces and the divergence theorem on images of boxes (Tau Ceti and Mathlib have more
general forms); Kepler's orbit equation (Tau Ceti); the theorems of Sylow, Lagrange and Jordan–Hölder, max-flow
min-cut, Hall's and Menger's theorems (Mathlib or Tau Ceti); the residue theorem, the argument principle, Rouché's
theorem and Laurent series (Tau Ceti); Burnside's $`p^aq^b`$ theorem, Frobenius reciprocity, Gabriel's theorem and
Schur–Weyl duality (Tau Ceti); the prime number theorem (Tau Ceti, as a case of the theorem for arithmetic
progressions); Euclid's and Euler's theorems on perfect numbers (Mathlib's Archive, from which our proof is adapted).

**Not formalized, or formalized only in part**, among others: Zeilberger's algorithm and the WZ method are
formalized as the soundness of supplied certificates (no existence or completeness theorem); the classification of
the 17 wallpaper groups; Sharkovskii's theorem beyond small periods; Brouwer's fixed point theorem (only the
reduction to the no-retraction theorem); Vizing's theorem (only the easy bounds); the non-planarity of $`K_5`$ and
$`K_{3,3}`$ (only from an assumed Euler formula); Sturm–Liouville expansions, the method of Frobenius and the
convergence of Fourier series. The *not formalized* rows of each checklist list the gaps.

## Layout

```
Challenge_<Topic>.lean  the headline statements of one topic (proofs: deliberate sorry); <Topic> = LinearAlgebra,
                        AbstractAlgebra, Combinatorics, Calculus, Trigonometry, Geometry, Precalculus, Statistics,
                        Probability, DifferentialEquations, ComplexAnalysis, RepresentationTheory, Topology
Solution_<Topic>.lean   the same statements, proved from the library
comparator.json         the topics, each with its lake comparator configuration comparator/<Topic>.json
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/books/             the book maps (one per book)
docs/courses/           the course outlines (one per book)
docs/coverage/          the master checklist of each topic (one row per result, with notes)
UndergradKB/
  Common/               the @[kb] citation attribute (imported by every topic)
  LinearAlgebra/        Axler and Hefferon      (Course/: course-layer theorems in the books' terms)
  AbstractAlgebra/      Judson-Beezer
  Combinatorics/        Keller-Trotter (Counting, Graph, Order, Flow, Polya, Probability, Recurrence) and A=B (AeqB)
  Calculus/             OpenStax Calculus, Volumes 1-3
  Trigonometry/         Corral and OpenStax Algebra and Trigonometry
  Geometry/             Petrunin
  Precalculus/          Stitz-Zeager
  Statistics/           OpenStax Introductory Statistics
  Probability/          Grinstead-Snell
  Foundations/          proofs, logic and sets: Hammack and Levin
  DifferentialEquations/  Lebl, Notes on Diffy Qs
  ComplexAnalysis/      Beck-Marchesi-Pixton-Sabalka
  RepresentationTheory/ Etingof et al.
  Topology/             Morris
references.bib          bibliography; the keys used by @[kb]
scripts/check_modularity.py     the import rules (run in CI)
scripts/check_axioms/<Topic>.lean     prints the axioms of the headline theorems of one topic (run in CI)
scripts/check_map_names/<Topic>.lean  checks that the Lean names of one topic's maps exist (run in CI)
scripts/verify-comparator.sh    runs lake comparator for one topic with the toolchain's kernels (run in CI)
.github/workflows/build.yml     the CI workflow (import rules, build, axioms, map names, one comparator check per topic)
```

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake build Calculus      # or one topic
lake env lean scripts/check_axioms/Geometry.lean   # axioms of the geometry headline theorems
./scripts/verify-comparator.sh Geometry            # Solution_Geometry against Challenge_Geometry
                                                   # (Linux; needs bubblewrap); likewise the other topics
```

Mathlib comes prebuilt from its cache; this library is built from source (917 Lean files, about 266,000 lines; no file
imports all of Mathlib, so only the Mathlib modules it needs are loaded). On 8 cores (2026-11-12), with Mathlib's
cache in place, `lake build` took about 16.5 minutes, with at most 7.6 GB of memory in use and a largest single Lean
process of 7.0 GB. Each `lake comparator` check (one topic: build, export, and the Lean, NanoDa and con-ron kernels)
took 1 to 7 minutes, with at most 3.6 GB in use and a largest single process of 4.0 GB (`leanexport`).

## Provenance

UndergradKB was written by AI, with Claude Code (Anthropic): by Claude Opus 5.5 and Claude Sonnet 5.5, in November
2026. Jonathan Hanke designed and directed it: he chose the books, the topics, the conventions and the release. The
proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms. The
76 headline statements of this release in the `Challenge_<Topic>.lean` files, and the definitions they use, have
**not yet been reviewed** by a human; that review is planned for a later release. `lake comparator` checks that each
`Solution_<Topic>.lean` proves exactly the statements of its `Challenge_<Topic>.lean`. The rest of the library (its
other definitions and results, the book maps, the course outlines and the paraphrases in them) has not been reviewed
by a human; as with any AI-written formalization, treat it as untrustworthy until checked against the literature.
Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24119531](https://doi.org/10.5281/zenodo.24119531) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.2.0](https://github.com/jonhanke/undergraduate-math-lean/releases/tag/v0.2.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:ZENODO-DOI-v0.2.0](https://doi.org/ZENODO-DOI-v0.2.0): eight new topics (precalculus, statistics, probability, proofs, logic and sets, differential equations, complex analysis, representation theory, topology) with the maps and course outlines of their nine books, new work in the six topics of 0.1.0, and 76 headline statements in thirteen topics.
- **[v0.1.0](https://github.com/jonhanke/undergraduate-math-lean/releases/tag/v0.1.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`), archived on Zenodo as [doi:10.5281/zenodo.24119532](https://doi.org/10.5281/zenodo.24119532): the first release: the six topics, the maps and course outlines
  of the nine books, and the 29 headline statements above.

## License

Apache License 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The textbooks are their authors' works under their
own licences (above); this repository contains none of their text, and three Lean files contain code adapted from
Mathlib and the PrimeNumberTheoremAnd project under the Apache License 2.0 (see NOTICE).
