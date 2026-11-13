# Undergraduate courses: outlines

Generated from the master checklists (`docs/coverage/<topic>/checklist.md`); never edit by hand.

One outline per book: the book's chapters in order, one line per item (item number, a one-line statement in our own words, status, and the Lean names a course can cite). *Items with a Lean name* counts items whose line shows at least one Lean name that was found in the repository or Mathlib sources; *of results* leaves out the items classified *not a result* (definitions, notation, remarks).

| topic | book | chapters | items | items with a Lean name | % | % of results | outline | checklist |
|---|---|---|---|---|---|---|---|---|
| Abstract algebra | judson2026 | 23 | 518 | 517 | 99.8% | 99.8% | [judson2026](abstract-algebra/judson2026.md) | [checklist](../coverage/abstract-algebra/checklist.md) |
| Calculus | OpenStax Calculus | 20 | 1327 | 1233 | 92.9% | 100.0% | [openstax-calculus](calculus/openstax-calculus.md) | [checklist](../coverage/calculus/checklist.md) |
| Combinatorics | Keller–Trotter | 17 | 419 | 404 | 96.4% | 97.1% | [kellertrotter2017](combinatorics/kellertrotter2017.md) | [checklist](../coverage/combinatorics/checklist.md) |
| Combinatorics | A=B | 10 | 251 | 231 | 92.0% | 93.1% | [petkovsekwilfzeilberger1996](combinatorics/petkovsekwilfzeilberger1996.md) | [checklist](../coverage/combinatorics/checklist.md) |
| Complex analysis | Beck 2025 | 10 | 265 | 261 | 98.5% | 100.0% | [beck2025](complex-analysis/beck2025.md) | [checklist](../coverage/complex-analysis/checklist.md) |
| Differential equations | Lebl, Notes on Diffy Qs | 9 | 415 | 384 | 92.5% | 97.2% | [lebldiffyqs2026](differential-equations/lebldiffyqs2026.md) | [checklist](../coverage/differential-equations/checklist.md) |
| Foundations | Hammack | 14 | 346 | 310 | 89.6% | 100.0% | [hammack2018](foundations/hammack2018.md) | [checklist](../coverage/foundations/checklist.md) |
| Foundations | Levin | 7 | 418 | 379 | 90.7% | 99.2% | [levin2025](foundations/levin2025.md) | [checklist](../coverage/foundations/checklist.md) |
| Geometry | Petrunin2025 | 20 | 354 | 342 | 96.6% | 100.0% | [petrunin2025](geometry/petrunin2025.md) | [checklist](../coverage/geometry/checklist.md) |
| Linear algebra | axler2024 | 9 | 465 | 464 | 99.8% | 99.8% | [axler2024](linear-algebra/axler2024.md) | [checklist](../coverage/linear-algebra/checklist.md) |
| Linear algebra | hefferon2020 | 20 | 352 | 351 | 99.7% | 100.0% | [hefferon2020](linear-algebra/hefferon2020.md) | [checklist](../coverage/linear-algebra/checklist.md) |
| Precalculus | Stitz-Zeager | 11 | 332 | 321 | 96.7% | 100.0% | [stitzzeager2013](precalculus/stitzzeager2013.md) | [checklist](../coverage/precalculus/checklist.md) |
| Probability | Grinstead–Snell | 12 | 277 | 277 | 100.0% | 100.0% | [grinsteadsnell2006](probability/grinsteadsnell2006.md) | [checklist](../coverage/probability/checklist.md) |
| Real analysis | Lebl, Basic Analysis I v6.3 | 8 | 451 | 348 | 77.2% | 77.3% | [lebl2026](real-analysis/lebl2026.md) | [checklist](../coverage/real-analysis/checklist.md) |
| Representation theory | etingof2011 | 7 | 305 | 305 | 100.0% | 100.0% | [etingof2011](representation-theory/etingof2011.md) | [checklist](../coverage/representation-theory/checklist.md) |
| Statistics | OpenStax Introductory Statistics 2e | 13 | 118 | 103 | 87.3% | 100.0% | [openstaxintrostats2e](statistics/openstaxintrostats2e.md) | [checklist](../coverage/statistics/checklist.md) |
| Topology | Morris | 12 | 814 | 789 | 96.9% | 97.4% | [morris2024](topology/morris2024.md) | [checklist](../coverage/topology/checklist.md) |
| Trigonometry | Corral | 6 | 170 | 164 | 96.5% | 100.0% | [corraltrig](trigonometry/corraltrig.md) | [checklist](../coverage/trigonometry/checklist.md) |
| Trigonometry | OpenStax | 4 | 205 | 198 | 96.6% | 100.0% | [openstaxalgtrig2e](trigonometry/openstaxalgtrig2e.md) | [checklist](../coverage/trigonometry/checklist.md) |

## How to use this for a course

- Pick the outline of the book your course follows and read it chapter by chapter; the counts at the top of each chapter say how much of it is available in Lean.
- Cite the Lean name shown on the item's line. A name containing `Course` is a course-layer theorem stated in the book's terms; other `UndergradKB` names are theorems proved in this repository; the rest are Mathlib names.
- `lake build <Topic>` builds one topic (for example `lake build LinearAlgebra`); topics never import each other, so a build touches only that topic.
- Statements in these documents are our paraphrases of the results, not the book's wording; the Lean statement is the authority. An item marked *partly* is only partly covered; read the note in the checklist row (the `[id]` after the item number) before using it.
- Items marked *not formalized* are the gaps; items marked *not a result* are definitions, notation or remarks and have no theorem to cite.
