import UndergradKB.RepresentationTheory.A5InducedCore
import UndergradKB.RepresentationTheory.ProblemsA5InducedZ2
import UndergradKB.RepresentationTheory.ProblemsA5InducedZ3
import UndergradKB.RepresentationTheory.ProblemsA5InducedZ5
import UndergradKB.RepresentationTheory.ProblemsA5InducedV4
import UndergradKB.RepresentationTheory.ProblemsA5InducedA4

/-! # Problem 4.34: representations of `A5` induced from subgroups

For the subgroups `Z2`, `Z3`, `Z5`, `Z2 × Z2` and `A4` of `A5 = alternatingGroup (Fin 5)` and each irreducible
character of the subgroup, we decompose the induced representation (Mathlib's `coind`, `Ind` in
`Induced.lean`) into irreducible characters of `A5`.  The statements are about the character of
`Ind H ρ` for any complex representation `ρ` of `H` with the given character; by
`nonempty_equiv_iff_character_eq_of_charZero` this is the isomorphism class of the induced representation.

The work is split into `A5InducedCore.lean` and one module per subgroup (`ProblemsA5InducedZ2.lean`,
`ProblemsA5InducedZ3.lean`, `ProblemsA5InducedZ5.lean`, `ProblemsA5InducedV4.lean`, `ProblemsA5InducedA4.lean`);
this file only gathers them.
-/
