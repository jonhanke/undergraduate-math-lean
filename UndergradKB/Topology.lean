import UndergradKB.Topology.BanachEmbedding
import UndergradKB.Topology.BanachMazur
import UndergradKB.Topology.Basics
import UndergradKB.Topology.Brouwer
import UndergradKB.Topology.Characters
import UndergradKB.Topology.ClassicalDuals
import UndergradKB.Topology.ClosedSubgroupsRn
import UndergradKB.Topology.ClosedSubgroupsRn2
import UndergradKB.Topology.Compactness
import UndergradKB.Topology.Completeness
import UndergradKB.Topology.ConesSpheres
import UndergradKB.Topology.CountableProducts
import UndergradKB.Topology.Course.AppendixA1
import UndergradKB.Topology.Course.AppendixA3A4
import UndergradKB.Topology.Course.AppendixA5
import UndergradKB.Topology.Course.AppendixA6
import UndergradKB.Topology.Course.Chapter01
import UndergradKB.Topology.Course.Chapter02
import UndergradKB.Topology.Course.Chapter03
import UndergradKB.Topology.Course.Chapter04
import UndergradKB.Topology.Course.Chapter05
import UndergradKB.Topology.Course.Chapter06Complete
import UndergradKB.Topology.Course.Chapter06Metric
import UndergradKB.Topology.Course.Chapter07
import UndergradKB.Topology.Course.Chapter08
import UndergradKB.Topology.Course.Chapter09
import UndergradKB.Topology.Course.Chapter10
import UndergradKB.Topology.Course.Chapter10StoneCech
import UndergradKB.Topology.Course.Chapter11
import UndergradKB.Topology.Course.Chapter12
import UndergradKB.Topology.Course.Extras
import UndergradKB.Topology.CubeEmbedding
import UndergradKB.Topology.CubeMaps
import UndergradKB.Topology.DensityCharacter
import UndergradKB.Topology.DiscreteDuals
import UndergradKB.Topology.Dynamics
import UndergradKB.Topology.DynamicsChaos
import UndergradKB.Topology.Extension
import UndergradKB.Topology.FilterFacts
import UndergradKB.Topology.FiniteIntersection
import UndergradKB.Topology.FunctionSpaces
import UndergradKB.Topology.GroupStructure
import UndergradKB.Topology.GroupsExtra
import UndergradKB.Topology.GroupsMore
import UndergradKB.Topology.GroupsMore2
import UndergradKB.Topology.HausdorffCovers
import UndergradKB.Topology.Homeomorphisms
import UndergradKB.Topology.IdentityComponent
import UndergradKB.Topology.InfiniteSets
import UndergradKB.Topology.KleiberPervin
import UndergradKB.Topology.MetricBasics
import UndergradKB.Topology.NSSGroups
import UndergradKB.Topology.Nets
import UndergradKB.Topology.Peano
import UndergradKB.Topology.PeriodThree
import UndergradKB.Topology.PolynomialBump
import UndergradKB.Topology.ProductsQuotients
import UndergradKB.Topology.Sharkovskii
import UndergradKB.Topology.SharkovskiiConverse
import UndergradKB.Topology.SineCurve
import UndergradKB.Topology.StoneCech
import UndergradKB.Topology.StoneCechCard
import UndergradKB.Topology.StoneWeierstrass
import UndergradKB.Topology.SubgroupsOfR
import UndergradKB.Topology.TopGroups
import UndergradKB.Topology.Wallman
import UndergradKB.Topology.Weierstrass
import UndergradKB.Common

/-! # Point-set topology
Topic root. Import every file of the topic here; a topic imports Mathlib modules
and `UndergradKB.Common` only (docs/ARCHITECTURE.md). Coverage: docs/coverage/topology/. Book: Morris, *Topology
Without Tears* (`morris2024`). Proved results in `UndergradKB/Topology/*.lean`, course layer (thin wrappers of
Mathlib results in the book's terms, by chapter) in `UndergradKB/Topology/Course/`. The import list is generated
(one import per file of the topic). -/
