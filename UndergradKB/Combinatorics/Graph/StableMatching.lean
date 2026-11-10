import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import UndergradKB.Common.Attr

/-!
# The Stable Matching Theorem (Gale–Shapley)

Keller–Trotter, Section 16.4.  There are `n` males and `n` females, each with a strict
preference order.  A bijection `M ≃ F` is *stable* if no male `b` and female `g'` both prefer each
other to their partners.  The proposal (deferred acceptance) algorithm is modelled in its
one-rejection-at-a-time form: the state records, for each male, the set of females that have
rejected him; he proposes to his best non-rejecting female; whenever a female has two suitors she
rejects the one she likes less.  The algorithm stops when no female has two suitors.
-/

namespace UndergradKB.Combinatorics.StableMatching

open Classical Function

noncomputable section

variable {M F : Type*}

/-- Strict preferences of every male over the females and of every female over the males,
given by injective rankings into `ℕ` (a larger rank is preferred, as in the book). -/
structure PrefProfile (M F : Type*) where
  rankM : M → F → ℕ
  rankF : F → M → ℕ
  rankM_inj : ∀ m, Injective (rankM m)
  rankF_inj : ∀ g, Injective (rankF g)

variable (P : PrefProfile M F)

/-- CO-308. A perfect matching `σ : M ≃ F` is stable if there is no male `b` and female `g'`
with `b` preferring `g'` to his partner and `g'` preferring `b` to her partner. -/
@[kb "kellertrotter2017" "Definition (unnumbered) stable matching, p. 345"]
def IsStable (σ : M ≃ F) : Prop :=
  ¬ ∃ (b : M) (g' : F), P.rankM b (σ b) < P.rankM b g' ∧ P.rankF g' (σ.symm g') < P.rankF g' b

/-- State of the algorithm: for each male, the set of females who have rejected him. -/
abbrev State (M F : Type*) := M → Finset F

/-- `g` is the current proposal of `m`: the best female (for `m`) who has not rejected him. -/
def IsProp (R : State M F) (m : M) (g : F) : Prop :=
  g ∉ R m ∧ ∀ g', g' ∉ R m → P.rankM m g' ≤ P.rankM m g

/-- One rejection: `g` has two suitors `m` and `m'`, prefers `m'`, and rejects `m`. -/
def Step (R R' : State M F) : Prop :=
  ∃ (m m' : M) (g : F), IsProp P R m g ∧ IsProp P R m' g ∧ P.rankF g m < P.rankF g m' ∧
    R' = update R m (insert g (R m))

/-- Invariant: whoever rejected `m` currently has a better suitor. -/
def Inv (R : State M F) : Prop :=
  ∀ m g, g ∈ R m → ∃ m', IsProp P R m' g ∧ P.rankF g m < P.rankF g m'

variable {P}

theorem IsProp.unique {R : State M F} {m : M} {g g' : F} (h : IsProp P R m g)
    (h' : IsProp P R m g') : g = g' :=
  P.rankM_inj m (le_antisymm (h'.2 g h.1) (h.2 g' h'.1))

theorem isProp_update_ne {R : State M F} {m m3 : M} {v : Finset F} {g : F} (h : m3 ≠ m) :
    IsProp P (update R m v) m3 g ↔ IsProp P R m3 g := by
  simp [IsProp, Function.update_of_ne h]

theorem Step.subset {R R' : State M F} (h : Step P R R') (m : M) : R m ⊆ R' m := by
  obtain ⟨m0, m', g, -, -, -, rfl⟩ := h
  by_cases hm : m = m0
  · subst hm; simp [Finset.subset_insert]
  · simp [Function.update_of_ne hm]

/-- The measure decreasing along the algorithm: the number of remaining (non-rejecting) options. -/
def meas [Fintype M] [Fintype F] (R : State M F) : ℕ := ∑ m, (R m)ᶜ.card

theorem Step.meas_lt [Fintype M] [Fintype F] {R R' : State M F} (h : Step P R R') : meas R' < meas R := by
  obtain ⟨m0, m', g, hp, -, -, rfl⟩ := h
  apply Finset.sum_lt_sum
  · intro m _
    by_cases hm : m = m0
    · subst hm; simp only [update_self]
      exact Finset.card_le_card (Finset.compl_subset_compl.2 (Finset.subset_insert _ _))
    · simp [Function.update_of_ne hm]
  · refine ⟨m0, Finset.mem_univ _, ?_⟩
    simp only [update_self]
    exact Finset.card_lt_card (Finset.compl_ssubset_compl.2 (Finset.ssubset_insert hp.1))

theorem Inv.step {R R' : State M F} (hR : Inv P R) (h : Step P R R') : Inv P R' := by
  obtain ⟨m0, m', g, hp, hp', hlt, rfl⟩ := h
  have hne : m' ≠ m0 := fun e => by subst e; exact lt_irrefl _ hlt
  intro m2 g2 hg2
  by_cases hm : m2 = m0
  · subst hm
    simp only [update_self, Finset.mem_insert] at hg2
    rcases hg2 with rfl | hg2
    · exact ⟨m', (isProp_update_ne hne).2 hp', hlt⟩
    · obtain ⟨m3, h3, h3lt⟩ := hR _ _ hg2
      by_cases h30 : m3 = m2
      · subst h30
        have := h3.unique hp
        subst this
        exact ⟨m', (isProp_update_ne hne).2 hp', h3lt.trans hlt⟩
      · exact ⟨m3, (isProp_update_ne h30).2 h3, h3lt⟩
  · simp only [Function.update_of_ne hm] at hg2
    obtain ⟨m3, h3, h3lt⟩ := hR _ _ hg2
    by_cases h30 : m3 = m0
    · subst h30
      have := h3.unique hp
      subst this
      exact ⟨m', (isProp_update_ne hne).2 hp', h3lt.trans hlt⟩
    · exact ⟨m3, (isProp_update_ne h30).2 h3, h3lt⟩

theorem inv_empty : Inv P (fun _ : M => (∅ : Finset F)) := by
  intro m g hg; simp at hg

/-- Under the invariant (and equal numbers) every male still has a proposal. -/
theorem Inv.exists_prop [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) {R : State M F}
    (hR : Inv P R) (m : M) : ∃ g, IsProp P R m g := by
  by_cases hm : (R m)ᶜ.Nonempty
  · obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image (R m)ᶜ (P.rankM m) hm
    exact ⟨g, by simpa using hg, fun g' hg' => hmax g' (by simpa using hg')⟩
  · exfalso
    have hall : ∀ g, g ∈ R m := by
      intro g; by_contra hg
      exact hm ⟨g, by simpa using hg⟩
    have key : ∀ g, ∃ m', m' ≠ m ∧ IsProp P R m' g := by
      intro g
      obtain ⟨m', h1, -⟩ := hR m g (hall g)
      exact ⟨m', fun e => by subst e; exact h1.1 (hall g), h1⟩
    choose f hf1 hf2 using key
    have hinj : Injective (fun g => (⟨f g, hf1 g⟩ : {m' // m' ≠ m})) := by
      intro g1 g2 e
      have e' : f g1 = f g2 := congrArg Subtype.val e
      exact (hf2 g1).unique (e' ▸ hf2 g2)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at this
    have hpos : 0 < Fintype.card M := Fintype.card_pos_iff.2 ⟨m⟩
    omega

variable (P) in
/-- CO-286. The proposal algorithm: from a state, perform rejections until no female has two
suitors (the choice of which rejection to perform next is arbitrary, via `Classical.choose`). -/
@[kb "kellertrotter2017" "text, p. 345"]
def run [Fintype M] [Fintype F] (R : State M F) : State M F :=
  if h : ∃ R', Step P R R' then run (Classical.choose h) else R
termination_by meas R
decreasing_by exact (Classical.choose_spec h).meas_lt

theorem run_spec [Fintype M] [Fintype F] (R : State M F) (hR : Inv P R) :
    Inv P (run P R) ∧ ¬ ∃ R', Step P (run P R) R' := by
  rw [run]
  split_ifs with h
  · exact run_spec _ (hR.step (Classical.choose_spec h))
  · exact ⟨hR, h⟩
termination_by meas R
decreasing_by exact (Classical.choose_spec h).meas_lt

/-- If no step is possible, two distinct males never propose to the same female. -/
theorem terminal_inj {R : State M F} (hT : ¬ ∃ R', Step P R R') {m m' : M} {g : F}
    (h : IsProp P R m g) (h' : IsProp P R m' g) : m = m' := by
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne (P.rankF_inj g e)) with hl | hl
  · exact hT ⟨_, m, m', g, h, h', hl, rfl⟩
  · exact hT ⟨_, m', m, g, h', h, hl, rfl⟩

/-- A terminal state with the invariant yields a stable perfect matching consisting of the
final proposals. -/
theorem exists_stable_of_terminal [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F)
    {R : State M F} (hR : Inv P R) (hT : ¬ ∃ R', Step P R R') :
    ∃ σ : M ≃ F, IsStable P σ ∧ ∀ m, IsProp P R m (σ m) := by
  choose p hp using hR.exists_prop hcard
  have hinj : Injective p := fun m m' e => terminal_inj hT (hp m) (e ▸ hp m')
  have hbij : Bijective p := (Fintype.bijective_iff_injective_and_card p).2 ⟨hinj, hcard⟩
  refine ⟨Equiv.ofBijective p hbij, ?_, hp⟩
  rintro ⟨b, g', h1, h2⟩
  have hmem : g' ∈ R b := by
    by_contra hg
    exact absurd ((hp b).2 g' hg) (not_le.2 h1)
  obtain ⟨m', hm', hlt⟩ := hR b g' hmem
  have : (Equiv.ofBijective p hbij).symm g' = m' := by
    rw [Equiv.symm_apply_eq]
    exact ((hp m').unique hm').symm
  rw [this] at h2
  exact absurd hlt (not_lt.2 h2.le)

/-- CO-309. The Stable Matching Theorem: for any strict preferences of `n` males and `n` females
there is a stable perfect matching. -/
@[kb "kellertrotter2017" "Stable Matching Theorem (unnumbered), p. 345"]
theorem exists_stable [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, IsStable P σ := by
  obtain ⟨hI, hT⟩ := run_spec (P := P) _ inv_empty
  obtain ⟨σ, hσ, -⟩ := exists_stable_of_terminal hcard hI hT
  exact ⟨σ, hσ⟩

/-- CO-287 (correctness). The algorithm started from the empty rejection state halts with a
stable perfect matching, whose partners are the final proposals. -/
@[kb "kellertrotter2017" "text, p. 346"]
theorem run_correct [Fintype M] [Fintype F] (hcard : Fintype.card M = Fintype.card F) :
    ∃ σ : M ≃ F, IsStable P σ ∧ (∀ m, IsProp P (run P fun _ => ∅) m (σ m)) ∧
      ¬ ∃ R', Step P (run P fun _ => ∅) R' := by
  obtain ⟨hI, hT⟩ := run_spec (P := P) _ inv_empty
  obtain ⟨σ, hσ, h⟩ := exists_stable_of_terminal hcard hI hT
  exact ⟨σ, hσ, h, hT⟩

/-- CO-287 (termination). Each step strictly decreases the number of remaining options, so
at most `n * n` rejections occur. -/
@[kb "kellertrotter2017" "text, p. 346"]
theorem step_meas_lt [Fintype M] [Fintype F] {R R' : State M F} (h : Step P R R') : meas R' < meas R := h.meas_lt

/-- CO-287 (males only worsen): a male's proposal moves down his list along a step. -/
@[kb "kellertrotter2017" "text, p. 346"]
theorem step_male_down {R R' : State M F} (h : Step P R R') {m : M} {g g' : F}
    (hg : IsProp P R m g) (hg' : IsProp P R' m g') : P.rankM m g' ≤ P.rankM m g :=
  hg.2 g' (fun hmem => hg'.1 (h.subset m hmem))

/-- CO-287 (females only improve): the best-held suitor of a female is never replaced by a worse
one along a step, i.e. a suitor at least as good still proposes to her. -/
@[kb "kellertrotter2017" "text, p. 346"]
theorem step_female_up {R R' : State M F} (h : Step P R R') {m0 : M} {g : F}
    (hg : IsProp P R m0 g) : ∃ m1, IsProp P R' m1 g ∧ P.rankF g m0 ≤ P.rankF g m1 := by
  obtain ⟨m, m', g1, hp, hp', hlt, rfl⟩ := h
  have hne : m' ≠ m := fun e => by subst e; exact lt_irrefl _ hlt
  by_cases h0 : m0 = m
  · subst h0
    have := hg.unique hp
    subst this
    exact ⟨m', (isProp_update_ne hne).2 hp', hlt.le⟩
  · exact ⟨m0, (isProp_update_ne h0).2 hg, le_rfl⟩

end

end UndergradKB.Combinatorics.StableMatching
