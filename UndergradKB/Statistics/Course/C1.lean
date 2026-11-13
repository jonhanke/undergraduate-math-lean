import UndergradKB.Statistics.Sampling
import UndergradKB.Common.Attr

/-!
# Course layer, chapter 1 (OpenStax *Introductory Statistics 2e*): sampling
-/

namespace UndergradKB.Statistics.Course.C1

open MeasureTheory UndergradKB.Statistics

/-- OpenStax Introductory Statistics 2e §1.2 (ST-001). A simple random sample of size `n` from a
population of `N` members is chosen so that every subset of size `n` is equally likely: its law is
the uniform law on the `n`-subsets. -/
@[kb "openstaxintrostats2e" "§1.2, p. 21"]
noncomputable def simple_random_sample_law (N n : ℕ) : Measure (Finset (Fin N)) :=
  srsLaw N n

/-- OpenStax Introductory Statistics 2e §1.2 (ST-001). In a simple random sample of size `n` from a
population of `N` members, each member is included with probability `n / N`. -/
@[kb "openstaxintrostats2e" "§1.2, p. 21"]
theorem simple_random_sample_inclusion_probability {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N)
    (i : Fin N) : (simple_random_sample_law N n).real {S | i ∈ S} = n / N :=
  srsLaw_inclusion_prob hn hnN i

end UndergradKB.Statistics.Course.C1
