import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import UndergradKB.Topology.Sharkovskii
import UndergradKB.Common.Attr

/-!
# The converse of Sharkovskii's theorem: the cases `n = 1`, `n = 2`, `n = 3`

Morris, *Topology Without Tears* (2024), Theorem A3.6.6 (`morris2024`).  `SharkovskiiLT l n` means
that `n` comes after `l`, i.e. `l` precedes `n`.  Here we construct, for `n ∈ {1, 2, 3}`, a continuous
`f : ℝ → ℝ` with a point of prime period `n` and no point of prime period `l` for any `l` preceding `n`.
-/

open Function Set

namespace UndergradKB.Topology

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), case `n = 1`: the identity has a fixed
point and no point of prime period `l` for `l` preceding `1`. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii_one :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = 1) ∧
      ∀ l, 0 < l → SharkovskiiLT l 1 → ¬ ∃ x, minimalPeriod f x = l := by
  refine ⟨id, continuous_id, ⟨0, by simp⟩, ?_⟩
  rintro l hl h ⟨x, hx⟩
  have : l = 1 := by simpa using hx.symm
  subst this
  exact SharkovskiiLT.irrefl 1 h

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), case `n = 2`: `x ↦ -x` has a point of
prime period `2` and no point of prime period `l` for `l` preceding `2`. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii_two :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = 2) ∧
      ∀ l, 0 < l → SharkovskiiLT l 2 → ¬ ∃ x, minimalPeriod f x = l := by
  have hper : ∀ x : ℝ, IsPeriodicPt (fun y : ℝ => -y) 2 x := fun x => by
    show (fun y : ℝ => -y)^[2] x = x
    simp
  refine ⟨fun y => -y, continuous_neg, ⟨1, ?_⟩, ?_⟩
  · refine Function.minimalPeriod_eq_prime (hper 1) ?_
    show -(1 : ℝ) ≠ 1
    norm_num
  · rintro l hl h ⟨x, hx⟩
    have hd : minimalPeriod (fun y : ℝ => -y) x ∣ 2 := (hper x).minimalPeriod_dvd
    rw [hx] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with rfl | rfl
    · exact not_sharkovskiiLT_one 2 h
    · exact SharkovskiiLT.irrefl 2 h

/-- No positive integer precedes `3` in the Sharkovskii order. -/
theorem not_sharkovskiiLT_three {l : ℕ} (hl : 0 < l) : ¬ SharkovskiiLT l 3 := by
  intro h
  have e : 2 ^ l.factorization 2 * (l / 2 ^ l.factorization 2) = l :=
    Nat.ordProj_mul_ordCompl_eq_self l 2
  have hodd : ¬ 2 ∣ l / 2 ^ l.factorization 2 := Nat.not_dvd_ordCompl Nat.prime_two hl.ne'
  have h3 : (3 : ℕ).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  unfold SharkovskiiLT sharkovskiiAux at h
  rw [h3] at h
  simp only [pow_zero, Nat.div_one] at h
  generalize l.factorization 2 = a at *
  generalize l / 2 ^ a = m at *
  omega

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), case `n = 3`: `x ↦ min (x+1) (7-2x)`
has the cycle `1 → 2 → 3 → 1`, and nothing precedes `3`. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii_three :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = 3) ∧
      ∀ l, 0 < l → SharkovskiiLT l 3 → ¬ ∃ x, minimalPeriod f x = l := by
  refine ⟨fun x => min (x + 1) (7 - 2 * x), by fun_prop, ⟨1, ?_⟩, fun l hl h _ =>
    not_sharkovskiiLT_three hl h⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Function.minimalPeriod_eq_prime (f := fun x : ℝ => min (x + 1) (7 - 2 * x)) (p := 3) ?_ ?_
  · show (fun x : ℝ => min (x + 1) (7 - 2 * x))^[3] 1 = 1
    norm_num [Function.iterate_succ]
  · show min ((1 : ℝ) + 1) (7 - 2 * 1) ≠ 1
    norm_num

/-! ### The doubling construction and the case `n = 2^k` -/

section Doubling

/-- The doubled map: with `L = 2 (b - a)`, the interval `J₁ = [a, b]` is sent to `J₂ = [a+L, b+L]` by
translation, `J₂` is sent back to `J₁` by `f (· - L)`, the gap is bridged linearly, and the map is
constant beyond the two ends.  Then `dbl f a b` restricted twice to `J₁` is `f`. -/
noncomputable def dbl (f : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℝ :=
  if x ≤ b then max x a + 2 * (b - a)
  else if x ≤ a + 2 * (b - a) then
    (b + 2 * (b - a)) + (f a - (b + 2 * (b - a))) * (x - b) / (b - a)
  else f (min x (b + 2 * (b - a)) - 2 * (b - a))

variable {f : ℝ → ℝ} {a b x : ℝ}

theorem dbl_J1 (hax : a ≤ x) (hxb : x ≤ b) : dbl f a b x = x + 2 * (b - a) := by
  rw [dbl, if_pos hxb, max_eq_left hax]

theorem dbl_J2 (hab : a < b) (hx1 : a + 2 * (b - a) ≤ x) (hx2 : x ≤ b + 2 * (b - a)) :
    dbl f a b x = f (x - 2 * (b - a)) := by
  have hbx : ¬ x ≤ b := by intro h; linarith
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  rw [dbl, if_neg hbx]
  by_cases h : x ≤ a + 2 * (b - a)
  · have hx : x = a + 2 * (b - a) := le_antisymm h hx1
    rw [if_pos h, hx]
    have e1 : a + 2 * (b - a) - b = b - a := by ring
    have e2 : a + 2 * (b - a) - 2 * (b - a) = a := by ring
    rw [e1, e2, mul_div_cancel_right₀ _ hba]
    ring
  · rw [if_neg h, min_eq_left hx2]

theorem continuous_dbl (hf : Continuous f) (hab : a < b) : Continuous (dbl f a b) := by
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  unfold dbl
  refine Continuous.if_le (f := fun x : ℝ => x) (g := fun _ => b) ?_ ?_ continuous_id
    continuous_const ?_
  · fun_prop
  · refine Continuous.if_le (f := fun x : ℝ => x) (g := fun _ => a + 2 * (b - a)) ?_ ?_
      continuous_id continuous_const ?_
    · fun_prop
    · exact hf.comp (by fun_prop)
    · intro x hx
      subst hx
      have e1 : a + 2 * (b - a) - 2 * (b - a) = a := by ring
      rw [min_eq_left (by linarith), e1]
      have e2 : a + 2 * (b - a) - b = b - a := by ring
      rw [e2, mul_div_cancel_right₀ _ hba]
      ring
  · intro x hx
    subst hx
    simp only [if_pos (show x ≤ a + 2 * (x - a) by linarith)]
    rw [max_eq_left hab.le]
    ring

theorem dbl_mem_Icc (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b)) (x : ℝ) :
    dbl f a b x ∈ Icc a (b + 2 * (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hfa := hM (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
  unfold dbl
  split_ifs with h1 h2
  · constructor
    · linarith [le_max_right x a]
    · linarith [max_le h1 hab.le]
  · push Not at h1
    have ht0 : 0 ≤ (x - b) / (b - a) := div_nonneg (by linarith) hba.le
    have ht1 : (x - b) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith)
    rw [mul_div_assoc]
    set t := (x - b) / (b - a)
    have hc : 0 ≤ b + 2 * (b - a) - f a := by linarith [hfa.2]
    constructor
    · nlinarith [mul_nonneg hc (sub_nonneg.mpr ht1), hfa.1]
    · nlinarith [mul_nonneg hc ht0]
  · push Not at h2
    have hy1 : a + 2 * (b - a) ≤ min x (b + 2 * (b - a)) :=
      le_min h2.le (by linarith)
    have hy2 : min x (b + 2 * (b - a)) - 2 * (b - a) ≤ b := by
      linarith [min_le_right x (b + 2 * (b - a))]
    have := hM (show min x (b + 2 * (b - a)) - 2 * (b - a) ∈ Icc a b from
      ⟨by linarith, hy2⟩)
    exact ⟨this.1, by linarith [this.2]⟩

theorem dbl_gap (h1 : b < x) (h2 : x ≤ a + 2 * (b - a)) :
    dbl f a b x = (b + 2 * (b - a)) + (f a - (b + 2 * (b - a))) * (x - b) / (b - a) := by
  rw [dbl, if_neg (not_le.mpr h1), if_pos h2]

theorem iterate_dbl_two (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b)) (hx : x ∈ Icc a b) :
    (dbl f a b)^[2] x = f x := by
  show dbl f a b (dbl f a b x) = f x
  rw [dbl_J1 hx.1 hx.2, dbl_J2 hab (by linarith [hx.1]) (by linarith [hx.2])]
  congr 1
  ring

theorem iterate_dbl_even (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b)) (n : ℕ) :
    ∀ x ∈ Icc a b, (dbl f a b)^[2 * n] x = f^[n] x := by
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply,
      iterate_dbl_two hab hM hx, ih _ (hM hx), Function.iterate_succ_apply]

theorem iterate_dbl_odd (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b)) (n : ℕ)
    (hx : x ∈ Icc a b) : (dbl f a b)^[2 * n + 1] x = f^[n] x + 2 * (b - a) := by
  have hn := hM.iterate n hx
  rw [Function.iterate_succ_apply', iterate_dbl_even hab hM n x hx, dbl_J1 hn.1 hn.2]

theorem dbl_periodic_J1 (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b)) (hx : x ∈ Icc a b)
    {m : ℕ} (h : IsPeriodicPt (dbl f a b) m x) : ∃ q, m = 2 * q ∧ f^[q] x = x := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' m
  · refine ⟨q, hq, ?_⟩
    have := h.eq
    rw [hq, iterate_dbl_even hab hM q x hx] at this
    exact this
  · exfalso
    have := h.eq
    rw [hq, iterate_dbl_odd hab hM q hx] at this
    have h2 := (hM.iterate q hx).1
    linarith [hx.2]

theorem minimalPeriod_dbl_J1 (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b)) (hx : x ∈ Icc a b)
    (hr : 0 < minimalPeriod f x) : minimalPeriod (dbl f a b) x = 2 * minimalPeriod f x := by
  have h1 : IsPeriodicPt (dbl f a b) (2 * minimalPeriod f x) x := by
    show (dbl f a b)^[2 * minimalPeriod f x] x = x
    rw [iterate_dbl_even hab hM _ x hx]
    exact isPeriodicPt_minimalPeriod f x
  have hm_pos : 0 < minimalPeriod (dbl f a b) x := h1.minimalPeriod_pos (by omega)
  obtain ⟨q, hq, hfq⟩ := dbl_periodic_J1 hab hM hx (isPeriodicPt_minimalPeriod (dbl f a b) x)
  have hqpos : 0 < q := by omega
  have d1 : minimalPeriod f x ∣ q := (show IsPeriodicPt f q x from hfq).minimalPeriod_dvd
  have d2 : 2 * q ∣ 2 * minimalPeriod f x := hq ▸ h1.minimalPeriod_dvd
  have d3 : q ∣ minimalPeriod f x := Nat.dvd_of_mul_dvd_mul_left (by norm_num) d2
  rw [hq, Nat.dvd_antisymm d3 d1]

/-- A periodic point in the gap of the doubled map has period dividing `2`. -/
theorem minimalPeriod_dbl_dvd_two_of_gap (hab : a < b) (hM : MapsTo f (Icc a b) (Icc a b))
    (hx : b < x ∧ x < a + 2 * (b - a)) (hp : 0 < minimalPeriod (dbl f a b) x) :
    minimalPeriod (dbl f a b) x ∣ 2 := by
  set g := dbl f a b with hg
  have hba : 0 < b - a := sub_pos.mpr hab
  have hper : IsPeriodicPt g (minimalPeriod g x) x := isPeriodicPt_minimalPeriod g x
  set m := minimalPeriod g x with hm
  have hT : ∀ y, (y ∈ Icc a b ∨ y ∈ Icc (a + 2 * (b - a)) (b + 2 * (b - a))) →
      (g y ∈ Icc a b ∨ g y ∈ Icc (a + 2 * (b - a)) (b + 2 * (b - a))) := by
    rintro y (hy | hy)
    · right
      rw [hg, dbl_J1 hy.1 hy.2]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · left
      rw [hg, dbl_J2 hab hy.1 hy.2]
      exact hM (show y - 2 * (b - a) ∈ Icc a b from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hTit : ∀ j y, (y ∈ Icc a b ∨ y ∈ Icc (a + 2 * (b - a)) (b + 2 * (b - a))) →
      (g^[j] y ∈ Icc a b ∨ g^[j] y ∈ Icc (a + 2 * (b - a)) (b + 2 * (b - a))) := by
    intro j
    induction j with
    | zero => intro y hy; exact hy
    | succ j ih => intro y hy; rw [Function.iterate_succ_apply]; exact ih _ (hT y hy)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have horb : ∀ j, b < g^[j] x ∧ g^[j] x < a + 2 * (b - a) := by
    intro j
    by_contra hcon
    have hj : j ≠ 0 := by
      rintro rfl
      exact hcon hx
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hrange : g^[j' + 1] x ∈ Icc a (b + 2 * (b - a)) := by
      rw [Function.iterate_succ_apply']
      exact dbl_mem_Icc hab hM _
    have hyT : g^[j' + 1] x ∈ Icc a b ∨
        g^[j' + 1] x ∈ Icc (a + 2 * (b - a)) (b + 2 * (b - a)) := by
      by_cases h1 : g^[j' + 1] x ≤ b
      · exact Or.inl ⟨hrange.1, h1⟩
      · right
        have : a + 2 * (b - a) ≤ g^[j' + 1] x := by
          by_contra h2
          exact hcon ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩
        exact ⟨this, hrange.2⟩
    have h3 := hTit (m' * (j' + 1)) _ hyT
    have h4 : g^[m' * (j' + 1)] (g^[j' + 1] x) = x := by
      rw [← Function.iterate_add_apply]
      have : m' * (j' + 1) + (j' + 1) = m * (j' + 1) := by rw [hm']; ring
      rw [this]
      exact (hper.mul_const (j' + 1)).eq
    rw [h4] at h3
    rcases h3 with h3 | h3 <;> linarith [h3.1, h3.2, hx.1, hx.2]
  have hc : f a - (b + 2 * (b - a)) < 0 := by linarith [(hM (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)).2]
  have hanti : ∀ y z, (b < y ∧ y < a + 2 * (b - a)) → (b < z ∧ z < a + 2 * (b - a)) → y < z →
      g z < g y := by
    intro y z hy hz hyz
    rw [hg, dbl_gap hz.1 hz.2.le, dbl_gap hy.1 hy.2.le]
    have : (f a - (b + 2 * (b - a))) * (z - b) / (b - a) <
        (f a - (b + 2 * (b - a))) * (y - b) / (b - a) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_neg_left (by linarith) hc) hba
    linarith
  have e1 : ∀ i, g^[2 * (i + 1)] x = g (g (g^[2 * i] x)) := by
    intro i
    rw [show 2 * (i + 1) = 2 + 2 * i by ring, Function.iterate_add_apply]
    rfl
  have hper2 : g^[2 * m] x = x := by
    rw [mul_comm]
    exact (hper.mul_const 2).eq
  have hG : g (g x) = x := by
    by_contra hne
    have hq : ∀ j, b < g (g^[j] x) ∧ g (g^[j] x) < a + 2 * (b - a) := fun j => by
      rw [← Function.iterate_succ_apply' g j x]
      exact horb _
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdesc : ∀ j, g^[2 * (j + 1)] x < g^[2 * j] x := by
        intro j
        induction j with
        | zero => exact hlt
        | succ j ih =>
          have s1 : g (g^[2 * j] x) < g (g^[2 * (j + 1)] x) :=
            hanti _ _ (horb (2 * (j + 1))) (horb (2 * j)) ih
          have s2 : g (g (g^[2 * (j + 1)] x)) < g (g (g^[2 * j] x)) :=
            hanti _ _ (hq (2 * j)) (hq (2 * (j + 1))) s1
          calc g^[2 * (j + 1 + 1)] x = g (g (g^[2 * (j + 1)] x)) := e1 (j + 1)
            _ < g (g (g^[2 * j] x)) := s2
            _ = g^[2 * (j + 1)] x := (e1 j).symm
      have hs := strictAnti_nat_of_succ_lt (f := fun j => g^[2 * j] x) hdesc
      have h' : g^[2 * m] x < x := hs (show 0 < m by omega)
      rw [hper2] at h'
      exact lt_irrefl _ h'
    · have hasc : ∀ j, g^[2 * j] x < g^[2 * (j + 1)] x := by
        intro j
        induction j with
        | zero => exact hgt
        | succ j ih =>
          have s1 : g (g^[2 * (j + 1)] x) < g (g^[2 * j] x) :=
            hanti _ _ (horb (2 * j)) (horb (2 * (j + 1))) ih
          have s2 : g (g (g^[2 * j] x)) < g (g (g^[2 * (j + 1)] x)) :=
            hanti _ _ (hq (2 * (j + 1))) (hq (2 * j)) s1
          calc g^[2 * (j + 1)] x = g (g (g^[2 * j] x)) := e1 j
            _ < g (g (g^[2 * (j + 1)] x)) := s2
            _ = g^[2 * (j + 1 + 1)] x := (e1 (j + 1)).symm
      have hs := strictMono_nat_of_lt_succ (f := fun j => g^[2 * j] x) hasc
      have h' : x < g^[2 * m] x := hs (show 0 < m by omega)
      rw [hper2] at h'
      exact lt_irrefl _ h'
  exact (show IsPeriodicPt g 2 x from hG).minimalPeriod_dvd

/-- The invariant carried through the doubling: a continuous map with an invariant compact interval
`[a, b]` containing all its periodic points, with a point of prime period `2^k` and all periodic
points of prime period `2^j`, `j ≤ k`. -/
def DblData (k : ℕ) : Prop :=
  ∃ (f : ℝ → ℝ) (a b : ℝ), Continuous f ∧ a < b ∧ MapsTo f (Icc a b) (Icc a b) ∧
    (∃ x ∈ Icc a b, minimalPeriod f x = 2 ^ k) ∧
    ∀ x, 0 < minimalPeriod f x → x ∈ Icc a b ∧ ∃ j ≤ k, minimalPeriod f x = 2 ^ j

theorem dblData_zero : DblData 0 := by
  have hrange : ∀ y : ℝ, max 0 (min y 1) ∈ Icc (0 : ℝ) 1 := fun y =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hfix : ∀ y ∈ Icc (0 : ℝ) 1, max 0 (min y 1) = y := fun y hy => by
    rw [min_eq_left hy.2, max_eq_right hy.1]
  refine ⟨fun x => max 0 (min x 1), 0, 1, by fun_prop, zero_lt_one, fun y _ => hrange y,
    ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
  · simpa using (Function.minimalPeriod_eq_one_iff_isFixedPt (f := fun x : ℝ => max 0 (min x 1))
      (x := 0)).mpr (hfix 0 ⟨le_rfl, zero_le_one⟩)
  · intro x hpos
    obtain ⟨m', hm'⟩ : ∃ m', minimalPeriod (fun x : ℝ => max 0 (min x 1)) x = m' + 1 :=
      ⟨minimalPeriod (fun x : ℝ => max 0 (min x 1)) x - 1, by omega⟩
    have hx : x = max 0 (min ((fun x : ℝ => max 0 (min x 1))^[m'] x) 1) := by
      have := (isPeriodicPt_minimalPeriod (fun x : ℝ => max 0 (min x 1)) x).eq
      rw [hm', Function.iterate_succ_apply'] at this
      exact this.symm
    have hxI : x ∈ Icc (0 : ℝ) 1 := hx ▸ hrange _
    refine ⟨hxI, 0, le_rfl, ?_⟩
    simpa using (Function.minimalPeriod_eq_one_iff_isFixedPt (f := fun x : ℝ => max 0 (min x 1))
      (x := x)).mpr (hfix x hxI)

theorem dblData_succ {k : ℕ} (h : DblData k) : DblData (k + 1) := by
  obtain ⟨f, a, b, hf, hab, hM, ⟨x0, hx0, hx0p⟩, hper⟩ := h
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨dbl f a b, a, b + 2 * (b - a), continuous_dbl hf hab, by linarith, ?_, ?_, ?_⟩
  · intro y _
    exact dbl_mem_Icc hab hM y
  · refine ⟨x0, ⟨hx0.1, by linarith [hx0.2]⟩, ?_⟩
    rw [minimalPeriod_dbl_J1 hab hM hx0 (by rw [hx0p]; positivity), hx0p, pow_succ]
    ring
  · intro x hpos
    obtain ⟨m', hm'⟩ : ∃ m', minimalPeriod (dbl f a b) x = m' + 1 :=
      ⟨minimalPeriod (dbl f a b) x - 1, by omega⟩
    have hxI : x ∈ Icc a (b + 2 * (b - a)) := by
      have := (isPeriodicPt_minimalPeriod (dbl f a b) x).eq
      rw [hm', Function.iterate_succ_apply'] at this
      rw [← this]
      exact dbl_mem_Icc hab hM _
    refine ⟨hxI, ?_⟩
    have key : ∀ y ∈ Icc a b, 0 < minimalPeriod (dbl f a b) y →
        ∃ j ≤ k + 1, minimalPeriod (dbl f a b) y = 2 ^ j := by
      intro y hy hp
      obtain ⟨q, hq, hfq⟩ := dbl_periodic_J1 hab hM hy (isPeriodicPt_minimalPeriod (dbl f a b) y)
      have hqpos : 0 < q := by omega
      have hfpos : 0 < minimalPeriod f y :=
        (show IsPeriodicPt f q y from hfq).minimalPeriod_pos hqpos
      obtain ⟨_, j, hj, hjeq⟩ := hper y hfpos
      exact ⟨j + 1, by omega, by rw [minimalPeriod_dbl_J1 hab hM hy hfpos, hjeq, pow_succ]; ring⟩
    by_cases h1 : x ≤ b
    · exact key x ⟨hxI.1, h1⟩ hpos
    · by_cases h2 : a + 2 * (b - a) ≤ x
      · have hy : dbl f a b x ∈ Icc a b := by
          rw [dbl_J2 hab h2 hxI.2]
          exact hM (show x - 2 * (b - a) ∈ Icc a b from ⟨by linarith, by linarith [hxI.2]⟩)
        have hper_x : x ∈ periodicPts (dbl f a b) :=
          Function.minimalPeriod_pos_iff_mem_periodicPts.mp hpos
        have e := Function.minimalPeriod_apply hper_x
        rw [← e] at hpos ⊢
        exact key _ hy hpos
      · have hd := minimalPeriod_dbl_dvd_two_of_gap hab hM ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩ hpos
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
        · exact ⟨0, by omega, by simpa using h⟩
        · exact ⟨1, by omega, by simpa using h⟩

/-- A more flexible invariant: `S` bounds the set of prime periods, `n` is attained. -/
def DblDataS (S : Set ℕ) (n : ℕ) : Prop :=
  ∃ (f : ℝ → ℝ) (a b : ℝ), Continuous f ∧ a < b ∧ MapsTo f (Icc a b) (Icc a b) ∧
    (∃ x ∈ Icc a b, minimalPeriod f x = n) ∧
    ∀ x, 0 < minimalPeriod f x → x ∈ Icc a b ∧ minimalPeriod f x ∈ S

/-- The set of periods allowed after one doubling. -/
def dblSet (S : Set ℕ) : Set ℕ := {1, 2} ∪ (fun r => 2 * r) '' S

theorem dblDataS_double {S : Set ℕ} {n : ℕ} (hn : 0 < n) (h : DblDataS S n) :
    DblDataS (dblSet S) (2 * n) := by
  obtain ⟨f, a, b, hf, hab, hM, ⟨x0, hx0, hx0p⟩, hper⟩ := h
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨dbl f a b, a, b + 2 * (b - a), continuous_dbl hf hab, by linarith, ?_, ?_, ?_⟩
  · intro y _
    exact dbl_mem_Icc hab hM y
  · refine ⟨x0, ⟨hx0.1, by linarith [hx0.2]⟩, ?_⟩
    rw [minimalPeriod_dbl_J1 hab hM hx0 (by rw [hx0p]; exact hn), hx0p]
  · intro x hpos
    obtain ⟨m', hm'⟩ : ∃ m', minimalPeriod (dbl f a b) x = m' + 1 :=
      ⟨minimalPeriod (dbl f a b) x - 1, by omega⟩
    have hxI : x ∈ Icc a (b + 2 * (b - a)) := by
      have := (isPeriodicPt_minimalPeriod (dbl f a b) x).eq
      rw [hm', Function.iterate_succ_apply'] at this
      rw [← this]
      exact dbl_mem_Icc hab hM _
    refine ⟨hxI, ?_⟩
    have key : ∀ y ∈ Icc a b, 0 < minimalPeriod (dbl f a b) y →
        minimalPeriod (dbl f a b) y ∈ dblSet S := by
      intro y hy hp
      obtain ⟨q, hq, hfq⟩ := dbl_periodic_J1 hab hM hy (isPeriodicPt_minimalPeriod (dbl f a b) y)
      have hqpos : 0 < q := by omega
      have hfpos : 0 < minimalPeriod f y :=
        (show IsPeriodicPt f q y from hfq).minimalPeriod_pos hqpos
      obtain ⟨_, hS⟩ := hper y hfpos
      exact Or.inr ⟨_, hS, (minimalPeriod_dbl_J1 hab hM hy hfpos).symm⟩
    by_cases h1 : x ≤ b
    · exact key x ⟨hxI.1, h1⟩ hpos
    · by_cases h2 : a + 2 * (b - a) ≤ x
      · have hy : dbl f a b x ∈ Icc a b := by
          rw [dbl_J2 hab h2 hxI.2]
          exact hM (show x - 2 * (b - a) ∈ Icc a b from ⟨by linarith, by linarith [hxI.2]⟩)
        have hper_x : x ∈ periodicPts (dbl f a b) :=
          Function.minimalPeriod_pos_iff_mem_periodicPts.mp hpos
        have e := Function.minimalPeriod_apply hper_x
        rw [← e] at hpos ⊢
        exact key _ hy hpos
      · have hd := minimalPeriod_dbl_dvd_two_of_gap hab hM ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩ hpos
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inl (by simp [h])

theorem dblDataS_iterate {S : Set ℕ} {n : ℕ} (hn : 0 < n) (h : DblDataS S n) (k : ℕ) :
    DblDataS (dblSet^[k] S) (2 ^ k * n) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := dblDataS_double (by positivity) ih
    rwa [show 2 ^ (k + 1) * n = 2 * (2 ^ k * n) by ring]

theorem mem_dblSet_iterate {S : Set ℕ} (k : ℕ) {l : ℕ} (hl : l ∈ dblSet^[k] S) :
    (∃ j ≤ k, l = 2 ^ j) ∨ ∃ s ∈ S, l = 2 ^ k * s := by
  induction k generalizing l with
  | zero => exact Or.inr ⟨l, by simpa using hl, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at hl
    rcases hl with hl | ⟨r, hr, rfl⟩
    · rcases hl with rfl | rfl
      · exact Or.inl ⟨0, by omega, by simp⟩
      · exact Or.inl ⟨1, by omega, by simp⟩
    · rcases ih hr with ⟨j, hj, rfl⟩ | ⟨s, hs, rfl⟩
      · exact Or.inl ⟨j + 1, by omega, by ring⟩
      · exact Or.inr ⟨s, hs, by ring⟩

end Doubling

/-- The map `x ↦ min (y+1) (7-2y)` with `y` clamped to `[1,3]`: the cycle `1 → 2 → 3 → 1`. -/
noncomputable def clampThree (x : ℝ) : ℝ :=
  min (max 1 (min x 3) + 1) (7 - 2 * max 1 (min x 3))

theorem dblDataS_clampThree : DblDataS Set.univ 3 := by
  have hc : ∀ y : ℝ, max 1 (min y 3) ∈ Icc (1 : ℝ) 3 := fun y =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hrange : ∀ y : ℝ, clampThree y ∈ Icc (1 : ℝ) 3 := fun y => by
    have h := hc y
    unfold clampThree
    constructor
    · exact le_min (by linarith [h.1]) (by linarith [h.2])
    · rcases le_total (max 1 (min y 3)) 2 with h2 | h2
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by linarith)
  have hfix : ∀ y ∈ Icc (1 : ℝ) 3, max 1 (min y 3) = y := fun y hy => by
    rw [min_eq_left hy.2, max_eq_right hy.1]
  have hval : ∀ y ∈ Icc (1 : ℝ) 3, clampThree y = min (y + 1) (7 - 2 * y) := fun y hy => by
    unfold clampThree
    rw [hfix y hy]
  have hcont : Continuous clampThree := by unfold clampThree; fun_prop
  refine ⟨clampThree, 1, 3, hcont, by norm_num, fun y _ => hrange y, ⟨1, ⟨le_rfl, by norm_num⟩, ?_⟩,
    fun x hpos => ⟨?_, trivial⟩⟩
  · have e1 : clampThree 1 = 2 := by rw [hval 1 ⟨le_rfl, by norm_num⟩]; norm_num
    have e2 : clampThree 2 = 3 := by rw [hval 2 ⟨by norm_num, by norm_num⟩]; norm_num
    have e3 : clampThree 3 = 1 := by rw [hval 3 ⟨by norm_num, le_rfl⟩]; norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine Function.minimalPeriod_eq_prime (f := clampThree) (p := 3) ?_ ?_
    · show clampThree^[3] 1 = 1
      simp [Function.iterate_succ, e1, e2, e3]
    · show clampThree 1 ≠ 1
      rw [e1]; norm_num
  · obtain ⟨m', hm'⟩ : ∃ m', minimalPeriod clampThree x = m' + 1 :=
      ⟨minimalPeriod clampThree x - 1, by omega⟩
    have := (isPeriodicPt_minimalPeriod clampThree x).eq
    rw [hm', Function.iterate_succ_apply'] at this
    rw [← this]
    exact hrange _

theorem not_sharkovskiiLT_two_pow {j k : ℕ} (h : j ≤ k) : ¬ SharkovskiiLT (2 ^ j) (2 ^ k) := by
  have hj : (2 ^ j).factorization 2 = j := by
    simp [Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two]
  have hk : (2 ^ k).factorization 2 = k := by
    simp [Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two]
  unfold SharkovskiiLT sharkovskiiAux
  rw [hj, hk, Nat.div_self (by positivity), Nat.div_self (by positivity)]
  omega

theorem factorization_two_pow_mul_odd (a t : ℕ) (ht : ¬ 2 ∣ t) (ht0 : t ≠ 0) :
    (2 ^ a * t).factorization 2 = a ∧ (2 ^ a * t) / 2 ^ a = t := by
  refine ⟨?_, Nat.mul_div_cancel_left _ (by positivity)⟩
  rw [Nat.factorization_mul (by positivity) ht0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd ht]
  simp [Nat.factorization_pow, Nat.Prime.factorization_self Nat.prime_two]

theorem not_sharkovskiiLT_pow_two_pow_mul_three {j k : ℕ} : ¬ SharkovskiiLT (2 ^ j) (2 ^ k * 3) := by
  have h1 := factorization_two_pow_mul_odd j 1 (by norm_num) one_ne_zero
  have h2 := factorization_two_pow_mul_odd k 3 (by norm_num) (by norm_num)
  rw [mul_one] at h1
  unfold SharkovskiiLT sharkovskiiAux
  rw [h1.1, h1.2, h2.1, h2.2]
  omega

theorem not_sharkovskiiLT_mul_two_pow_mul_three {k s : ℕ} (hs : s ≠ 0) :
    ¬ SharkovskiiLT (2 ^ k * s) (2 ^ k * 3) := by
  obtain ⟨c, t, ht, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hs
  have h1 := factorization_two_pow_mul_odd (k + c) t (by simpa [Nat.odd_iff] using ht.not_two_dvd_nat)
    (by rintro rfl; simp at ht)
  have h2 := factorization_two_pow_mul_odd k 3 (by norm_num) (by norm_num)
  have e : 2 ^ k * (2 ^ c * t) = 2 ^ (k + c) * t := by ring
  rw [e]
  have hodd : ¬ 2 ∣ t := ht.not_two_dvd_nat
  unfold SharkovskiiLT sharkovskiiAux
  rw [h1.1, h1.2, h2.1, h2.2]
  omega

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), case `n = 2^k · 3`: obtained by doubling
the period-three map `k` times; its prime periods are the powers of two up to `2^k` and the multiples
of `2^k`. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii_two_pow_mul_three (k : ℕ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = 2 ^ k * 3) ∧
      ∀ l, 0 < l → SharkovskiiLT l (2 ^ k * 3) → ¬ ∃ x, minimalPeriod f x = l := by
  obtain ⟨f, a, b, hf, -, -, ⟨x0, -, hx0⟩, hper⟩ :=
    dblDataS_iterate (by norm_num) dblDataS_clampThree k
  refine ⟨f, hf, ⟨x0, hx0⟩, ?_⟩
  rintro l hl h ⟨x, hx⟩
  obtain ⟨-, hS⟩ := hper x (hx ▸ hl)
  rw [hx] at hS
  rcases mem_dblSet_iterate k hS with ⟨j, hj, rfl⟩ | ⟨s, -, rfl⟩
  · exact not_sharkovskiiLT_pow_two_pow_mul_three h
  · exact not_sharkovskiiLT_mul_two_pow_mul_three (by rintro rfl; simp at hl) h

/-- Morris, Topology Without Tears, Theorem A3.6.6 (TP-449), case `n = 2^k`: there is a continuous
`f : ℝ → ℝ` with a point of prime period `2^k` and no point of prime period `l` for any `l`
preceding `2^k` (its prime periods are exactly `1, 2, 4, …, 2^k`), built by iterating the doubling
construction. -/
@[kb "morris2024" "Theorem A3.6.6, p. 458"]
theorem converse_sharkovskii_two_pow (k : ℕ) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∃ x, minimalPeriod f x = 2 ^ k) ∧
      ∀ l, 0 < l → SharkovskiiLT l (2 ^ k) → ¬ ∃ x, minimalPeriod f x = l := by
  have hall : ∀ k, DblData k := fun k => Nat.rec dblData_zero (fun k ih => dblData_succ ih) k
  obtain ⟨f, a, b, hf, -, -, ⟨x0, -, hx0⟩, hper⟩ := hall k
  refine ⟨f, hf, ⟨x0, hx0⟩, ?_⟩
  rintro l hl h ⟨x, hx⟩
  obtain ⟨-, j, hj, hjeq⟩ := hper x (hx ▸ hl)
  rw [← hx, hjeq] at h
  exact not_sharkovskiiLT_two_pow hj h

end UndergradKB.Topology
