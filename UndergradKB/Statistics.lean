import UndergradKB.Common
import UndergradKB.Statistics.Data
import UndergradKB.Statistics.Descriptive
import UndergradKB.Statistics.Regression
import UndergradKB.Statistics.Anova
import UndergradKB.Statistics.Discrete
import UndergradKB.Statistics.Continuous
import UndergradKB.Statistics.MGF
import UndergradKB.Statistics.ChiSquared
import UndergradKB.Statistics.StudentT
import UndergradKB.Statistics.FDistribution
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.CorrelationTest
import UndergradKB.Statistics.Inference
import UndergradKB.Statistics.AnovaTest
import UndergradKB.Statistics.PValue
import UndergradKB.Statistics.Sampling
import UndergradKB.Statistics.Limits
import UndergradKB.Statistics.Waiting
import UndergradKB.Statistics.Percentile
import UndergradKB.Statistics.Rules
import UndergradKB.Statistics.NormalCdf
import UndergradKB.Statistics.EmpiricalRule
import UndergradKB.Statistics.Pearson
import UndergradKB.Statistics.Welch
import UndergradKB.Statistics.TwoProportions
import UndergradKB.Statistics.TableProjection
import UndergradKB.Statistics.IndependenceTest
import UndergradKB.Statistics.HomogeneityCLT
import UndergradKB.Statistics.Homogeneity
import UndergradKB.Statistics.TwoSample
import UndergradKB.Statistics.CriticalValues
import UndergradKB.Statistics.Remarks
import UndergradKB.Statistics.DistributionLimits
import UndergradKB.Statistics.SampleMoments
import UndergradKB.Statistics.Course.C1
import UndergradKB.Statistics.Course.C2
import UndergradKB.Statistics.Course.C3
import UndergradKB.Statistics.Course.C4
import UndergradKB.Statistics.Course.C5
import UndergradKB.Statistics.Course.C6
import UndergradKB.Statistics.Course.C6Cdf
import UndergradKB.Statistics.Course.C7
import UndergradKB.Statistics.Course.C8
import UndergradKB.Statistics.Course.C9
import UndergradKB.Statistics.Course.C10
import UndergradKB.Statistics.Course.C11
import UndergradKB.Statistics.Course.C12
import UndergradKB.Statistics.Course.C13

/-! # Statistics
Topic root. Import every file of the topic here; a topic imports Mathlib modules
and `UndergradKB.Common` only (docs/ARCHITECTURE.md). Coverage: docs/coverage/.

Book: OpenStax *Introductory Statistics 2e* (`openstaxintrostats2e`). Headlines: the chi-square law
(`ChiSquared`), the Student t and F laws (`StudentT`, `FDistribution`), the sampling distributions of a normal
sample (`NormalSample`), least squares and correlation (`Regression`); course layer in `Course/`. -/
