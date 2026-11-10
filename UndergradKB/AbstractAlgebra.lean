import UndergradKB.Common.Attr
import UndergradKB.AbstractAlgebra.Alternating
import UndergradKB.AbstractAlgebra.Boolean
import UndergradKB.AbstractAlgebra.Codes
import UndergradKB.AbstractAlgebra.Codes2
import UndergradKB.AbstractAlgebra.Constructible
import UndergradKB.AbstractAlgebra.Course.Ch01Preliminaries
import UndergradKB.AbstractAlgebra.Course.Ch02Integers
import UndergradKB.AbstractAlgebra.Course.Ch03Groups
import UndergradKB.AbstractAlgebra.Course.Ch04CyclicGroups
import UndergradKB.AbstractAlgebra.Course.Ch05Permutations
import UndergradKB.AbstractAlgebra.Course.Ch06Cosets
import UndergradKB.AbstractAlgebra.Course.Ch07Cryptography
import UndergradKB.AbstractAlgebra.Course.Ch08Codes
import UndergradKB.AbstractAlgebra.Course.Ch09Isomorphisms
import UndergradKB.AbstractAlgebra.Course.Ch10NormalSubgroups
import UndergradKB.AbstractAlgebra.Course.Ch11Homomorphisms
import UndergradKB.AbstractAlgebra.Course.Ch12MatrixGroups
import UndergradKB.AbstractAlgebra.Course.Ch13AbelianGroups
import UndergradKB.AbstractAlgebra.Course.Ch14GroupActions
import UndergradKB.AbstractAlgebra.Course.Ch15Sylow
import UndergradKB.AbstractAlgebra.Course.Ch16Rings
import UndergradKB.AbstractAlgebra.Course.Ch17Polynomials
import UndergradKB.AbstractAlgebra.Course.Ch18IntegralDomains
import UndergradKB.AbstractAlgebra.Course.Ch19Lattices
import UndergradKB.AbstractAlgebra.Course.Ch20VectorSpaces
import UndergradKB.AbstractAlgebra.Course.Ch21Fields
import UndergradKB.AbstractAlgebra.Course.Ch22FiniteFields
import UndergradKB.AbstractAlgebra.Course.Ch23Galois
import UndergradKB.AbstractAlgebra.Cryptography
import UndergradKB.AbstractAlgebra.Cube
import UndergradKB.AbstractAlgebra.CyclicCodes
import UndergradKB.AbstractAlgebra.DihedralPolygon
import UndergradKB.AbstractAlgebra.DirectProducts
import UndergradKB.AbstractAlgebra.Domains
import UndergradKB.AbstractAlgebra.Extensions
import UndergradKB.AbstractAlgebra.FiniteFields
import UndergradKB.AbstractAlgebra.FiniteGroups
import UndergradKB.AbstractAlgebra.FiniteSymmetry
import UndergradKB.AbstractAlgebra.Galois
import UndergradKB.AbstractAlgebra.Groups
import UndergradKB.AbstractAlgebra.Integers
import UndergradKB.AbstractAlgebra.MatrixGroups
import UndergradKB.AbstractAlgebra.MatrixGroups2
import UndergradKB.AbstractAlgebra.Permutations
import UndergradKB.AbstractAlgebra.PiTranscendental
import UndergradKB.AbstractAlgebra.Polynomials
import UndergradKB.AbstractAlgebra.RadicalTowers
import UndergradKB.AbstractAlgebra.Rings
import UndergradKB.AbstractAlgebra.Series
import UndergradKB.AbstractAlgebra.Wallpaper

/-! # Abstract algebra (Judson–Beezer)

Root of the topic: imports every file of the topic. Topic files import specific Mathlib modules (never all of
`Mathlib`) and `UndergradKB.Common`, never another topic (docs/ARCHITECTURE.md). Proofs of results that Mathlib
lacks are in `UndergradKB/AbstractAlgebra/*.lean`; the course layer (book-named statements of results Mathlib has)
is in `UndergradKB/AbstractAlgebra/Course/`. -/
