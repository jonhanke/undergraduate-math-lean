# Undergraduate courses: outlines

Generated from the master checklists (`docs/coverage/<topic>/checklist.md`); never edit by hand.

One outline per book: the book's chapters in order, one line per item (item number, a one-line statement in our own words, status, and the Lean names a course can cite). *Items with a Lean name* counts items whose line shows at least one Lean name that was found in the repository or Mathlib sources; *of results* leaves out the items classified *not a result* (definitions, notation, remarks).

| topic | book | chapters | items | items with a Lean name | % | % of results | outline | checklist |
|---|---|---|---|---|---|---|---|---|
| Abstract algebra | judson2026 | 23 | 518 | 517 | 99.8% | 99.8% | [judson2026](abstract-algebra/judson2026.md) | [checklist](../coverage/abstract-algebra/checklist.md) |
| Calculus | OpenStax Calculus | 20 | 1327 | 1233 | 92.9% | 100.0% | [openstax-calculus](calculus/openstax-calculus.md) | [checklist](../coverage/calculus/checklist.md) |
| Combinatorics | Keller–Trotter | 17 | 419 | 400 | 95.5% | 96.2% | [kellertrotter2017](combinatorics/kellertrotter2017.md) | [checklist](../coverage/combinatorics/checklist.md) |
| Combinatorics | A=B | 10 | 251 | 214 | 85.3% | 86.3% | [petkovsekwilfzeilberger1996](combinatorics/petkovsekwilfzeilberger1996.md) | [checklist](../coverage/combinatorics/checklist.md) |
| Geometry | Petrunin2025 | 20 | 354 | 339 | 95.8% | 99.1% | [petrunin2025](geometry/petrunin2025.md) | [checklist](../coverage/geometry/checklist.md) |
| Linear algebra | axler2024 | 9 | 465 | 464 | 99.8% | 99.8% | [axler2024](linear-algebra/axler2024.md) | [checklist](../coverage/linear-algebra/checklist.md) |
| Linear algebra | hefferon2020 | 20 | 352 | 351 | 99.7% | 100.0% | [hefferon2020](linear-algebra/hefferon2020.md) | [checklist](../coverage/linear-algebra/checklist.md) |
| Trigonometry | Corral | 6 | 170 | 164 | 96.5% | 100.0% | [corraltrig](trigonometry/corraltrig.md) | [checklist](../coverage/trigonometry/checklist.md) |
| Trigonometry | OpenStax | 4 | 205 | 198 | 96.6% | 100.0% | [openstaxalgtrig2e](trigonometry/openstaxalgtrig2e.md) | [checklist](../coverage/trigonometry/checklist.md) |

## How to use this for a course

- Pick the outline of the book your course follows and read it chapter by chapter; the counts at the top of each chapter say how much of it is available in Lean.
- Cite the Lean name shown on the item's line. A name containing `Course` is a course-layer theorem stated in the book's terms; other `UndergradKB` names are theorems proved in this repository; the rest are Mathlib names.
- `lake build <Topic>` builds one topic (for example `lake build LinearAlgebra`); topics never import each other, so a build touches only that topic.
- Statements in these documents are our paraphrases of the results, not the book's wording; the Lean statement is the authority. An item marked *partly* is only partly covered; read the note in the checklist row (the `[id]` after the item number) before using it.
- Items marked *not formalized* are the gaps; items marked *not a result* are definitions, notation or remarks and have no theorem to cite.
