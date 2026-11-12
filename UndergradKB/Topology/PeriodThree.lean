import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import UndergradKB.Common.Attr

/-!
# The Period Three Theorem

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.2 and Exercises A3.6 (`morris2024`):
a continuous self-map of the real line with a point of prime period 3 has points of every prime period.

The proof follows the book's Exercises A3.6 #2 to #4: a fixed point lemma (Proposition A), the lemma that a
compact interval covered by the image of another contains a subinterval mapping exactly onto it
(Proposition B), a chain lemma for sequences of intervals, and finally the choice of the itinerary
`I₁, I₀, I₁, ..., I₁` for the two intervals spanned by the 3-cycle. Prime periods are
`Function.minimalPeriod`.
-/

open Function Set

namespace UndergradKB.Topology

/-! ### Intervals and the intermediate value theorem -/

/-- Morris, Topology Without Tears, Exercises A3.6 #2, Proposition A. If a continuous function `g` maps
`[a, b]` onto a set containing `[a, b]`, then it has a fixed point in `[a, b]`. -/
@[kb "morris2024" "Exercises A3.6, p. 459"]
theorem exists_fixedPt_of_subset_image {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b)
    (h : Icc a b ⊆ g '' Icc a b) : ∃ x ∈ Icc a b, g x = x := by
  obtain ⟨p, hp, hgp⟩ := h (left_mem_Icc.mpr hab)
  obtain ⟨q, hq, hgq⟩ := h (right_mem_Icc.mpr hab)
  have hφ : ContinuousOn (fun x => g x - x) (uIcc p q) := (hg.sub continuous_id).continuousOn
  have h0 : (0 : ℝ) ∈ uIcc (g p - p) (g q - q) := by
    rw [mem_uIcc]
    left
    constructor
    · have := hp.1; have := hp.2; simp only [hgp]; linarith [hp.1]
    · simp only [hgq]; linarith [hq.2]
  obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hφ h0
  exact ⟨x, uIcc_subset_Icc hp hq hx, by simp only at hx0; linarith⟩

/-- Core of Proposition B (Exercises A3.6 #3), the case where the preimage of the lower value lies to the left
of the preimage of the upper value. -/
private lemma exists_subinterval_aux {g : ℝ → ℝ} (hg : Continuous g) {u v c d : ℝ} (huv : u ≤ v)
    (hcd : c ≤ d) (hu : g u = c) (hv : g v = d) :
    ∃ s t, u ≤ s ∧ s ≤ t ∧ t ≤ v ∧ g '' Icc s t = Icc c d := by
  rcases hcd.eq_or_lt with rfl | hlt
  · refine ⟨u, u, le_rfl, le_rfl, huv, ?_⟩
    simp [hu]
  -- the last point `s` of `[u, v]` with `g s ≤ c`
  have hSc : IsCompact (Icc u v ∩ g ⁻¹' Iic c) :=
    isCompact_Icc.inter_right (isClosed_Iic.preimage hg)
  obtain ⟨s, ⟨hsIcc, hsc⟩, hsmax⟩ := hSc.exists_isGreatest ⟨u, ⟨le_rfl, huv⟩, by simp [hu]⟩
  have hsmax' : ∀ x ∈ Icc u v, g x ≤ c → x ≤ s := fun x hx hxc => hsmax ⟨hx, hxc⟩
  have hgs : g s = c := by
    have hcI : c ∈ Icc (g s) (g v) := ⟨hsc, by rw [hv]; exact hlt.le⟩
    obtain ⟨x, hx, hxc⟩ := intermediate_value_Icc hsIcc.2 hg.continuousOn hcI
    have : x ≤ s := hsmax' x ⟨hsIcc.1.trans hx.1, hx.2⟩ hxc.le
    have : x = s := le_antisymm this hx.1
    rw [← this]; exact hxc
  -- the first point `t` of `[s, v]` with `g t ≥ d`
  have hTc : IsCompact (Icc s v ∩ g ⁻¹' Ici d) :=
    isCompact_Icc.inter_right (isClosed_Ici.preimage hg)
  obtain ⟨t, ⟨htIcc, htd⟩, htmin⟩ := hTc.exists_isLeast ⟨v, ⟨hsIcc.2, le_rfl⟩, by simp [hv]⟩
  have htmin' : ∀ x ∈ Icc s v, d ≤ g x → t ≤ x := fun x hx hxd => htmin ⟨hx, hxd⟩
  have hgt : g t = d := by
    have hdI : d ∈ Icc (g s) (g t) := ⟨by rw [hgs]; exact hlt.le, htd⟩
    obtain ⟨x, hx, hxd⟩ := intermediate_value_Icc htIcc.1 hg.continuousOn hdI
    have : t ≤ x := htmin' x ⟨hx.1, hx.2.trans htIcc.2⟩ hxd.ge
    have : x = t := le_antisymm hx.2 this
    rw [← this]; exact hxd
  refine ⟨s, t, hsIcc.1, htIcc.1, htIcc.2, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    constructor
    · by_contra hlt'
      push Not at hlt'
      have : x ≤ s := hsmax' x ⟨hsIcc.1.trans hx.1, hx.2.trans htIcc.2⟩ hlt'.le
      have : x = s := le_antisymm this hx.1
      rw [this, hgs] at hlt'; exact lt_irrefl _ hlt'
    · by_contra hlt'
      push Not at hlt'
      have : t ≤ x := htmin' x ⟨hx.1, hx.2.trans htIcc.2⟩ hlt'.le
      have : x = t := le_antisymm hx.2 this
      rw [this, hgt] at hlt'; exact lt_irrefl _ hlt'
  · have := intermediate_value_Icc htIcc.1 hg.continuousOn (a := s) (b := t)
    rw [hgs, hgt] at this
    exact this

/-- Morris, Topology Without Tears, Exercises A3.6 #3, Proposition B. If a continuous function `g` maps
`[a, b]` onto a set containing `[c, d]` (`c ≤ d`), then some subinterval `[s, t]` of `[a, b]` is mapped
exactly onto `[c, d]`. -/
@[kb "morris2024" "Exercises A3.6, p. 459"]
theorem exists_subinterval_image_eq {g : ℝ → ℝ} (hg : Continuous g) {a b c d : ℝ} (hcd : c ≤ d)
    (h : Icc c d ⊆ g '' Icc a b) :
    ∃ s t, a ≤ s ∧ s ≤ t ∧ t ≤ b ∧ g '' Icc s t = Icc c d := by
  obtain ⟨u, hu, hgu⟩ := h (left_mem_Icc.mpr hcd)
  obtain ⟨v, hv, hgv⟩ := h (right_mem_Icc.mpr hcd)
  rcases le_total u v with huv | hvu
  · obtain ⟨s, t, h1, h2, h3, h4⟩ := exists_subinterval_aux hg huv hcd hgu hgv
    exact ⟨s, t, hu.1.trans h1, h2, h3.trans hv.2, h4⟩
  · have hg' : Continuous fun x => -g x := hg.neg
    obtain ⟨s, t, h1, h2, h3, h4⟩ := exists_subinterval_aux hg' hvu (neg_le_neg hcd)
      (by simp [hgv]) (by simp [hgu])
    refine ⟨s, t, hv.1.trans h1, h2, h3.trans hu.2, ?_⟩
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have : -g x ∈ Icc (-d) (-c) := by rw [← h4]; exact ⟨x, hx, rfl⟩
      constructor <;> linarith [this.1, this.2]
    · intro y hy
      have : -y ∈ (fun x => -g x) '' Icc s t := by
        rw [h4]; constructor <;> linarith [hy.1, hy.2]
      obtain ⟨x, hx, hxy⟩ := this
      exact ⟨x, hx, by simp only at hxy; linarith⟩

/-- The image of an interval whose endpoints go to the endpoints of `[lo, hi]` contains `[lo, hi]`. -/
private lemma Icc_subset_image_of_endpoints {f : ℝ → ℝ} (hf : Continuous f) {x y lo hi : ℝ}
    (hxy : x ≤ y) (h : (f x = lo ∧ f y = hi) ∨ (f x = hi ∧ f y = lo)) : Icc lo hi ⊆ f '' Icc x y := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := intermediate_value_Icc hxy hf.continuousOn
    rwa [h1, h2] at this
  · have := intermediate_value_Icc' hxy hf.continuousOn
    rwa [h1, h2] at this

/-! ### Chains of intervals -/

/-- Chain lemma: if `J (i+1) ⊆ f (J i)` for compact intervals `J i = [l i, r i]`, there is a subinterval `K` of
`J 0` with `f^i (K) ⊆ J i` for `i ≤ n` and `f^n (K) = J n`. -/
private lemma exists_interval_chain {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ∀ (l r : ℕ → ℝ), (∀ i, l i ≤ r i) →
      (∀ i, Icc (l (i + 1)) (r (i + 1)) ⊆ f '' Icc (l i) (r i)) →
      ∃ s t, l 0 ≤ s ∧ s ≤ t ∧ t ≤ r 0 ∧ (∀ i ≤ n, f^[i] '' Icc s t ⊆ Icc (l i) (r i)) ∧
        f^[n] '' Icc s t = Icc (l n) (r n) := by
  induction n with
  | zero =>
    intro l r hlr _
    refine ⟨l 0, r 0, le_rfl, hlr 0, le_rfl, ?_, by simp⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simp
  | succ n ih =>
    intro l r hlr hcov
    obtain ⟨s', t', h1, h2, h3, h4, h5⟩ := ih (fun i => l (i + 1)) (fun i => r (i + 1))
      (fun i => hlr _) (fun i => hcov (i + 1))
    obtain ⟨s, t, g1, g2, g3, g4⟩ := exists_subinterval_image_eq hf h2
      ((Icc_subset_Icc h1 h3).trans (hcov 0))
    refine ⟨s, t, g1, g2, g3, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        rw [iterate_zero, Set.image_id]
        exact Icc_subset_Icc g1 g3
      | succ j =>
        rw [iterate_succ, Set.image_comp, g4]
        exact h4 j (by omega)
    · rw [iterate_succ, Set.image_comp, g4]
      exact h5

/-- A periodic point following an itinerary of intervals: if `J (i+1) ⊆ f (J i)` for the intervals
`J i = [l i, r i]` and `J 0 ⊆ J n`, then `f^n` has a fixed point `x` with `f^i x ∈ J i` for `i ≤ n`. -/
private lemma exists_periodic_itinerary {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (l r : ℕ → ℝ)
    (hlr : ∀ i, l i ≤ r i) (hcov : ∀ i, Icc (l (i + 1)) (r (i + 1)) ⊆ f '' Icc (l i) (r i))
    (hn : Icc (l 0) (r 0) ⊆ Icc (l n) (r n)) :
    ∃ x, f^[n] x = x ∧ ∀ i ≤ n, f^[i] x ∈ Icc (l i) (r i) := by
  obtain ⟨s, t, h1, h2, h3, h4, h5⟩ := exists_interval_chain hf n l r hlr hcov
  have hsub : Icc s t ⊆ f^[n] '' Icc s t := by
    rw [h5]; exact (Icc_subset_Icc h1 h3).trans hn
  obtain ⟨x, hx, hfx⟩ := exists_fixedPt_of_subset_image (hf.iterate n) h2 hsub
  exact ⟨x, hfx, fun i hi => h4 i hi ⟨x, hx, rfl⟩⟩

/-! ### The two intervals of a 3-cycle -/

/-- The itinerary lemma for two closed intervals `I₀ = [a₀, b₀]`, `I₁ = [a₁, b₁]` meeting in the single point
`b`, with `I₀ ⊆ f (I₁)`, `I₁ ⊆ f (I₀)`, `I₁ ⊆ f (I₁)`, where `b` has prime period `3` and `f² b ∉ I₁`:
`f` has points of every prime period. -/
private lemma exists_minimalPeriod_of_intervals {f : ℝ → ℝ} (hf : Continuous f)
    {a₀ b₀ a₁ b₁ b : ℝ} (h₀ : a₀ ≤ b₀) (h₁ : a₁ ≤ b₁)
    (hA : Icc a₀ b₀ ⊆ f '' Icc a₁ b₁) (hB : Icc a₁ b₁ ⊆ f '' Icc a₀ b₀)
    (hC : Icc a₁ b₁ ⊆ f '' Icc a₁ b₁)
    (hinter : ∀ x, x ∈ Icc a₀ b₀ → x ∈ Icc a₁ b₁ → x = b)
    (hfb : f (f b) ∉ Icc a₁ b₁) (hper : minimalPeriod f b = 3) :
    ∀ n : ℕ, 0 < n → ∃ x, minimalPeriod f x = n := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    obtain ⟨x, -, hx⟩ := exists_fixedPt_of_subset_image hf h₁ hC
    exact ⟨x, minimalPeriod_eq_one_iff_isFixedPt.mpr hx⟩
  -- the itinerary `I₁, I₀, I₁, I₁, ...`
  let l : ℕ → ℝ := fun i => if i = 1 then a₀ else a₁
  let r : ℕ → ℝ := fun i => if i = 1 then b₀ else b₁
  have hlr : ∀ i, l i ≤ r i := by
    intro i; by_cases hi : i = 1 <;> simp [l, r, hi, h₀, h₁]
  have hcov : ∀ i, Icc (l (i + 1)) (r (i + 1)) ⊆ f '' Icc (l i) (r i) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0; simpa [l, r] using hA
    · by_cases hi1 : i = 1
      · subst hi1; simpa [l, r] using hB
      · have e1 : i + 1 ≠ 1 := by omega
        simpa [l, r, hi0, hi1, e1] using hC
  have hnn : n ≠ 1 := by omega
  obtain ⟨x, hxn, hxi⟩ := exists_periodic_itinerary hf (n := n) l r hlr hcov (by
    simp [l, r, hnn])
  have hI0 : f x ∈ Icc a₀ b₀ := by simpa [l, r] using hxi 1 (by omega)
  have hI1 : ∀ i, 2 ≤ i → i ≤ n → f^[i] x ∈ Icc a₁ b₁ := by
    intro i h2 hi
    have := hxi i hi
    have e : i ≠ 1 := by omega
    simpa [l, r, e] using this
  refine ⟨x, ?_⟩
  have hpernx : IsPeriodicPt f n x := hxn
  have hmpos : 0 < minimalPeriod f x := hpernx.minimalPeriod_pos hn
  have hdvd : minimalPeriod f x ∣ n := hpernx.minimalPeriod_dvd
  by_contra hne
  have hlt : minimalPeriod f x < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne
  set m := minimalPeriod f x with hm
  have hmx : f^[m] x = x := iterate_minimalPeriod
  have hfx : f^[m + 1] x = f x := by rw [iterate_succ_apply', hmx]
  have hfxI1 : f x ∈ Icc a₁ b₁ := by
    rw [← hfx]; exact hI1 (m + 1) (by omega) (by omega)
  have hfxb : f x = b := hinter _ hI0 hfxI1
  have hbper : f^[m] b = b := by
    rw [← hfxb, ← iterate_succ_apply, hfx]
  have h3m : 3 ∣ m := by
    rw [← hper]; exact (show IsPeriodicPt f m b from hbper).minimalPeriod_dvd
  have h3n : 3 ≤ n := by
    have := Nat.le_of_dvd hmpos h3m
    omega
  have : f^[3] x ∈ Icc a₁ b₁ := hI1 3 (by omega) h3n
  apply hfb
  have e3 : f^[3] x = f (f b) := by
    rw [iterate_succ_apply, hfxb]; rfl
  rwa [← e3]

private lemma case_orient_a {f : ℝ → ℝ} (hf : Continuous f) {p q r : ℝ} (hpq : p < q) (hqr : q < r)
    (h1 : f p = q) (h2 : f q = r) (h3 : f r = p) (hq : minimalPeriod f q = 3) :
    ∀ n : ℕ, 0 < n → ∃ x, minimalPeriod f x = n := by
  have hr : Icc p r ⊆ f '' Icc q r :=
    Icc_subset_image_of_endpoints hf hqr.le (Or.inr ⟨h2, h3⟩)
  refine exists_minimalPeriod_of_intervals hf (a₀ := p) (b₀ := q) (a₁ := q) (b₁ := r) (b := q)
    hpq.le hqr.le ?_ ?_ ?_ ?_ ?_ hq
  · exact (Icc_subset_Icc le_rfl hqr.le).trans hr
  · exact Icc_subset_image_of_endpoints hf hpq.le (Or.inl ⟨h1, h2⟩)
  · exact (Icc_subset_Icc hpq.le le_rfl).trans hr
  · intro x hx1 hx2; exact le_antisymm hx1.2 hx2.1
  · rw [h2, h3]; intro h; exact absurd h.1 (not_le.mpr hpq)

private lemma case_orient_b {f : ℝ → ℝ} (hf : Continuous f) {p q r : ℝ} (hpq : p < q) (hqr : q < r)
    (h1 : f p = r) (h2 : f r = q) (h3 : f q = p) (hq : minimalPeriod f q = 3) :
    ∀ n : ℕ, 0 < n → ∃ x, minimalPeriod f x = n := by
  have hr : Icc p r ⊆ f '' Icc p q :=
    Icc_subset_image_of_endpoints hf hpq.le (Or.inr ⟨h1, h3⟩)
  refine exists_minimalPeriod_of_intervals hf (a₀ := q) (b₀ := r) (a₁ := p) (b₁ := q) (b := q)
    hqr.le hpq.le ?_ ?_ ?_ ?_ ?_ hq
  · exact (Icc_subset_Icc hpq.le le_rfl).trans hr
  · exact Icc_subset_image_of_endpoints hf hqr.le (Or.inl ⟨h3, h2⟩)
  · exact (Icc_subset_Icc le_rfl hqr.le).trans hr
  · intro x hx1 hx2; exact le_antisymm hx2.2 hx1.1
  · rw [h3, h1]; intro h; exact absurd h.2 (not_le.mpr hqr)

/-- A 3-cycle `x → y → z → x` of distinct reals, each of prime period 3, forces every prime period: the
six possible orderings reduce to the two orientations treated above. -/
private lemma three_cycle {f : ℝ → ℝ} (hf : Continuous f) {x y z : ℝ} (hxy : f x = y) (hyz : f y = z)
    (hzx : f z = x) (hne1 : x ≠ y) (hne2 : y ≠ z) (hne3 : x ≠ z) (mx : minimalPeriod f x = 3)
    (my : minimalPeriod f y = 3) (mz : minimalPeriod f z = 3) :
    ∀ n : ℕ, 0 < n → ∃ w, minimalPeriod f w = n := by
  rcases lt_or_gt_of_ne hne1 with h1 | h1 <;> rcases lt_or_gt_of_ne hne2 with h2 | h2 <;>
    rcases lt_or_gt_of_ne hne3 with h4 | h4 <;>
    first
    | (exfalso; linarith)
    | exact case_orient_a hf (p := x) (q := y) (r := z) (by linarith) (by linarith) hxy hyz hzx my
    | exact case_orient_b hf (p := x) (q := z) (r := y) (by linarith) (by linarith) hxy hyz hzx mz
    | exact case_orient_b hf (p := y) (q := x) (r := z) (by linarith) (by linarith) hyz hzx hxy mx
    | exact case_orient_a hf (p := y) (q := z) (r := x) (by linarith) (by linarith) hyz hzx hxy mz
    | exact case_orient_a hf (p := z) (q := x) (r := y) (by linarith) (by linarith) hzx hxy hyz mx
    | exact case_orient_b hf (p := z) (q := y) (r := x) (by linarith) (by linarith) hzx hxy hyz my

/-- Morris, Topology Without Tears, Theorem A3.6.2 (TP-447). The Period Three Theorem: a continuous
`f : ℝ → ℝ` with a point of prime period 3 has, for every `n ≥ 1`, a point of prime period `n`. -/
@[kb "morris2024" "Theorem A3.6.2, p. 456"]
theorem exists_minimalPeriod_eq_of_minimalPeriod_three {f : ℝ → ℝ} (hf : Continuous f)
    (h3 : ∃ a, minimalPeriod f a = 3) : ∀ n : ℕ, 0 < n → ∃ x, minimalPeriod f x = n := by
  obtain ⟨a, ha⟩ := h3
  have hper : a ∈ periodicPts f := by
    rw [← minimalPeriod_pos_iff_mem_periodicPts]; omega
  have my : minimalPeriod f (f a) = 3 := by rw [minimalPeriod_apply hper, ha]
  have hpy : f a ∈ periodicPts f := by
    rw [← minimalPeriod_pos_iff_mem_periodicPts]; omega
  have mz : minimalPeriod f (f (f a)) = 3 := by rw [minimalPeriod_apply hpy, my]
  have hfz : f (f (f a)) = a := by
    have := isPeriodicPt_minimalPeriod f a
    rw [ha] at this
    exact this
  have hinj := iterate_injOn_Iio_minimalPeriod (f := f) (x := a)
  rw [ha] at hinj
  have hxy : a ≠ f a := fun h => by
    have := hinj (show 0 ∈ Iio 3 by simp) (show 1 ∈ Iio 3 by simp) (by simpa using h)
    omega
  have hyz : f a ≠ f (f a) := fun h => by
    have := hinj (show 1 ∈ Iio 3 by simp) (show 2 ∈ Iio 3 by simp) (by exact h)
    omega
  have hxz : a ≠ f (f a) := fun h => by
    have := hinj (show 0 ∈ Iio 3 by simp) (show 2 ∈ Iio 3 by simp) (by simpa using h)
    omega
  exact three_cycle hf rfl rfl hfz hxy hyz hxz ha my mz

end UndergradKB.Topology

