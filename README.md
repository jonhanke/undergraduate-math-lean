# Undergraduate mathematics in Lean 4

[![Lean build](https://github.com/jonhanke/undergraduate-math-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/undergraduate-math-lean/actions/workflows/build.yml)

A Lean 4 library (built on Mathlib) that formalizes nine openly available undergraduate textbooks in six topics, item
by item: **linear algebra** (Axler; Hefferon), **abstract algebra** (Judson–Beezer), **combinatorics**
(Keller–Trotter; Petkovšek–Wilf–Zeilberger, *A=B*), **calculus** (OpenStax, Volumes 1–3), **trigonometry** (Corral;
OpenStax *Algebra and Trigonometry*) and **geometry** (Petrunin). The Lean library is called `UndergradKB`; the
repository is undergraduate-math-lean.

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

## The books

| topic | book | licence | items | rows | proved here | in Mathlib | partly in Mathlib | not formalized | not a result | items with a Lean name | course outline |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Linear algebra | [S. Axler, *Linear Algebra Done Right*, 4th ed., Springer, 2024 (open access)](docs/books/axler2024.md) | CC BY-NC 4.0 | 465 | 436 | 142 | 294 | 0 | 0 | 0 | 464 (99.8%) | [outline](docs/courses/linear-algebra/axler2024.md) |
| Linear algebra | [J. Hefferon, *Linear Algebra*, 4th ed., 2020](docs/books/hefferon2020.md) | GNU FDL or CC BY-SA 3.0 US, at the reader's choice | 352 | 296 | 121 | 173 | 0 | 0 | 2 | 351 (99.7%) | [outline](docs/courses/linear-algebra/hefferon2020.md) |
| Abstract algebra | [T. W. Judson and R. A. Beezer, *Abstract Algebra: Theory and Applications*, 2026 edition](docs/books/judson2026.md) | GNU FDL 1.2 or later | 518 | 445 | 148 | 295 | 0 | 2 | 0 | 517 (99.8%) | [outline](docs/courses/abstract-algebra/judson2026.md) |
| Combinatorics | [M. T. Keller and W. T. Trotter, *Applied Combinatorics*, 2017 edition](docs/books/kellertrotter2017.md) | CC BY-SA 4.0 | 419 | 329 | 177 | 130 | 1 | 18 | 3 | 400 (95.5%) | [outline](docs/courses/combinatorics/kellertrotter2017.md) |
| Combinatorics | [M. Petkovšek, H. S. Wilf and D. Zeilberger, *A=B*, A K Peters, 1996](docs/books/petkovsekwilfzeilberger1996.md) | © 1996 A K Peters | 251 | 224 | 152 | 21 | 3 | 45 | 3 | 214 (85.3%) | [outline](docs/courses/combinatorics/petkovsekwilfzeilberger1996.md) |
| Calculus | [G. Strang, E. Herman et al., *Calculus*, Volumes 1–3, OpenStax, 2016](docs/books/openstax-calculus.md) | CC BY-NC-SA 4.0 | 1327 | 690 | 351 | 272 | 0 | 0 | 67 | 1233 (92.9%) | [outline](docs/courses/calculus/openstax-calculus.md) |
| Trigonometry | [M. Corral, *Trigonometry*](docs/books/corraltrig.md) | GNU FDL 1.3 or later | 170 | 156 | 88 | 64 | 0 | 0 | 4 | 164 (96.5%) | [outline](docs/courses/trigonometry/corraltrig.md) |
| Trigonometry | [J. Abramson et al., *Algebra and Trigonometry*, 2nd ed., OpenStax](docs/books/openstaxalgtrig2e.md) | CC BY-NC-SA 4.0 | 205 | 129 | 81 | 43 | 0 | 0 | 5 | 198 (96.6%) | [outline](docs/courses/trigonometry/openstaxalgtrig2e.md) |
| Geometry | [A. Petrunin, *Euclidean Plane and its Relatives: a minimalist introduction*, 3rd ed. (arXiv:1302.1630v25, 2025)](docs/books/petrunin2025.md) | CC BY-SA 4.0 | 354 | 352 | 213 | 102 | 3 | 16 | 18 | 339 (95.8%) | [outline](docs/courses/geometry/petrunin2025.md) |

*Items*: the item entries of the book in its map. The other counts are checklist rows (one row per result; a
result stated in two books of a topic is one row, counted in both). *Proved here*: proved in this library with only
the standard axioms. *In Mathlib*: Mathlib (a dependency) has the result; the map names the Mathlib declaration, and
for central results a course-layer theorem of this library. *Partly in Mathlib*: only part of the item is
formalized. *Not formalized*: a gap (see each checklist). *Not a result*: a definition, notation or remark.
*Items with a Lean name*: items whose line in the course outline cites a Lean declaration that exists.

**Licences of the books.** The books are cited, never copied: this repository holds item numbers, page numbers,
Lean statements and one-line paraphrases of our own, and none of the books' text. Axler: CC BY-NC 4.0
(open access, Springer). Hefferon: GNU FDL or CC BY-SA 3.0 US. Judson–Beezer: GNU FDL 1.2 or later.
Keller–Trotter: CC BY-SA 4.0. OpenStax *Calculus* and *Algebra and Trigonometry*: CC BY-NC-SA 4.0. Corral: GNU FDL
1.3 or later. Petrunin: CC BY-SA 4.0. *A=B*: © 1996 A K Peters, made freely available by its authors with the
publisher's consent; it is cited only. We thank the authors for making their books openly available.

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

**Main statements.** To check what is claimed, read the six files `Challenge_<Topic>.lean`: they state the results
above (29 theorems), with a docstring for each and a list of the library definitions the statements use; every proof
there is a deliberate `sorry`. The matching `Solution_<Topic>.lean` files prove the same statements by appeal to the
library theorems, and `lake comparator`, configured per topic by `comparator/<Topic>.json` (the topics are listed in
[`comparator.json`](comparator.json)), checks that each proved statement is exactly the one in the challenge file and
uses only the standard axioms. The check is run one topic at a time: each needs only the files of its topic.
[`formalization.yaml`](formalization.yaml) records the scope, sources, divergences, provenance and review status in
the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Also proved here, not headlines because Mathlib or Tau Ceti has them:** the singular value and polar
decompositions, the pseudoinverse and the complex spectral theorem (Tau Ceti); the Schwarz–Pick lemma and the area
of a hyperbolic triangle as its angle defect (Tau Ceti); Green's theorem on parametrized regions, Stokes's theorem on
parametrized surfaces and the divergence theorem on images of boxes (Tau Ceti and Mathlib have more general forms);
Kepler's orbit equation (Tau Ceti); the theorems of Sylow, Lagrange and Jordan–Hölder, max-flow min-cut, Hall's and
Menger's theorems (Mathlib or Tau Ceti).

**Not formalized, or formalized only in part**, among others: the neutral-plane theorems of Petrunin are checked in
the Euclidean and hyperbolic models, not derived from the axioms; Zeilberger's algorithm and the WZ method are
formalized as the soundness of supplied certificates (no existence or completeness theorem); the classification of
the 17 wallpaper groups. The *not formalized* rows of each checklist list the gaps.

## Layout

```
Challenge_<Topic>.lean  the headline statements of one topic (proofs: deliberate sorry); <Topic> = LinearAlgebra,
                        AbstractAlgebra, Combinatorics, Calculus, Trigonometry, Geometry
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

Mathlib comes prebuilt from its cache; this library is built from source (447 modules, about 132,000 lines; no file
imports all of Mathlib, so only the Mathlib modules it needs are loaded). On 8 cores and 31 GB (2026-11-10), with
Mathlib's cache in place, `lake build` took about 8 minutes, with at most 7.2 GB of memory in use and a largest
single Lean process of 4.5 GB. Each `lake comparator` check (one topic: build, export, and the Lean, NanoDa and
con-ron kernels) took 2 to 6.5 minutes, with at most 2.3 GB in use and a largest single process of 3.7 GB
(`leanexport`).

## Provenance

UndergradKB was written by AI, with Claude Code (Anthropic): by Claude Opus 5.5 and Claude Sonnet 5.5, in November
2026. Jonathan Hanke designed and directed it: he chose the books, the topics, the conventions and the release. The
proofs are checked by the Lean kernel, and CI checks that the headline theorems use only the standard axioms. The
29 headline statements of this release in the `Challenge_<Topic>.lean` files, and the definitions they use, have
**not yet been reviewed** by a human; that review is planned for a later release. `lake comparator` checks that each
`Solution_<Topic>.lean` proves exactly the statements of its `Challenge_<Topic>.lean`. The rest of the library (its
other definitions and results, the book maps, the course outlines and the paraphrases in them) has not been reviewed
by a human; as with any AI-written formalization, treat it as untrustworthy until checked against the literature.
Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop.

- **v0.1.0** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`): the first release: the six topics, the maps and course outlines
  of the nine books, and the 29 headline statements above.

## License

Apache License 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The textbooks are their authors' works under their
own licences (above); this repository contains none of their text.
