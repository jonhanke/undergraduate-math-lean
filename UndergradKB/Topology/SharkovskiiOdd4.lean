import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import UndergradKB.Topology.Sharkovskii
import UndergradKB.Topology.SharkovskiiConverse
import UndergradKB.Topology.SharkovskiiOdd
import UndergradKB.Topology.SharkovskiiOdd2
import UndergradKB.Topology.SharkovskiiOdd3
import UndergradKB.Common.Attr

/-!
# Sharkovskii's theorem for odd periods: the Štefan lemma

Morris, *Topology Without Tears* (2024), Appendix 3, Theorem A3.6.4 (`morris2024`).  If a continuous
`f : ℝ → ℝ` has a point of prime period `m`, `m ≥ 3` odd, and no point of odd prime period `l` with
`3 ≤ l < m`, then `f` has a point of prime period `k` for every `k` which is `1`, even, or larger than `m`.
The proof lists the cycle in increasing order, builds the Markov graph of the gaps between consecutive points,
shows (`SharkovskiiOdd`, `SharkovskiiOdd2`, `SharkovskiiOdd3`) that it is a Hamiltonian chain closed up by a
last gap which covers all the gaps of even index, and follows loops of gaps (an interval-covering fixed point
argument).
-/

open Function Set

namespace UndergradKB.Topology

namespace SortedOrbit

variable {f : ℝ → ℝ} {m : ℕ} (S : SortedOrbit f m)

/-- A loop of gaps of length `k` gives a point following it, of prime period `k` unless it is a cycle point. -/
theorem exists_loop_point (hf : Continuous f) {k : ℕ} {J : ℕ → ℕ} (hk : 0 < k)
    (hlt : ∀ i, J i + 1 < m) (hcov : ∀ i, S.Cov (J i) (J (i + 1)))
    (hper : ∀ i, J (i + k) = J i) (hprim : ∀ p, 0 < p → p < k → ∃ i, J (i + p) ≠ J i) :
    ∃ y, f^[k] y = y ∧ (minimalPeriod f y = k ∨ ∃ r, r < m ∧ S.q r = y) ∧
      ∀ i, f^[i] y ∈ Icc (S.q (J i)) (S.q (J i + 1)) := by
  obtain ⟨y, hy, hit⟩ := S.exists_periodic_gap_loop hf hk hper (fun i => ⟨hlt i, hlt (i + 1), hcov i⟩)
  refine ⟨y, hy, ?_, hit⟩
  by_cases hex : minimalPeriod f y = k
  · exact Or.inl hex
  · exact Or.inr (S.mem_cycle_of_not_exact hk hprim hlt hy hit hex)

end SortedOrbit

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), the Štefan lemma: if `m ≥ 3` is odd and `f` has a
point of prime period `m` but none of odd prime period `l` with `3 ≤ l < m`, then `f` has a point of prime
period `k` for every `k` which is `1`, even, or larger than `m`. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem stefan_periods {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} {m : ℕ} (hx : minimalPeriod f x = m)
    (hm : 3 ≤ m) (hodd : m % 2 = 1)
    (hmin : ∀ l, 3 ≤ l → l < m → Odd l → ¬ ∃ y, minimalPeriod f y = l) {k : ℕ} (hk : 0 < k)
    (hkk : m < k ∨ k % 2 = 0 ∨ k = 1) : ∃ y, minimalPeriod f y = k := by
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨p, hp⟩ := exists_isFixedPt_of_two_le_minimalPeriod hf hx (by omega)
    exact ⟨p, minimalPeriod_eq_one_iff_isFixedPt.mpr hp⟩
  obtain ⟨S⟩ := exists_sortedOrbit hx (by omega)
  obtain ⟨t, ht1, ht2, ht3, htl⟩ := S.exists_loop_gap hf hm
  obtain ⟨v, hv0, hvinj, hvlt, hvsurj, hvstep, hvcl, hvshort, hvC5⟩ :=
    S.exists_chain hf hm hodd hmin ht1 ht2 ht3 htl
  let G : GapData m :=
    { π := S.π
      v := v
      hm := hm
      π_lt := S.π_lt
      pi_pi_ne := fun i hi => S.pi_pi_ne hm hi
      v_inj := hvinj
      v_lt := hvlt
      hout := by
        intro j g hj hg h1 h2
        have hvj := hvlt j hj
        have hcov : S.Cov (v j) g := S.cov_of_between hf (by omega) (by omega) h1 h2
        obtain ⟨i, hi, hig⟩ := hvsurj g hg
        subst hig
        refine ⟨⟨i, hvshort j i hj hi hcov, rfl⟩, fun h => ?_⟩
        rw [h] at hcov
        exact hvC5 j hj hcov
      t2 := by rw [hv0]; exact ht2
      t3 := by rw [hv0]; exact ht3 }
  have hGs := G.start
  obtain ⟨x0, hx0def⟩ : ∃ x0 : ℕ, x0 = if S.π (v 0) = v 0 + 1 then v 0 else v 0 + 1 := ⟨_, rfl⟩
  have hv0m := hvlt 0 (by omega)
  have hx0m : x0 < m := by
    rw [hx0def]; split_ifs <;> omega
  have hper0 := S.per x0 hx0m
  let D : SpiralData m :=
    { toGapData := G
      X := fun i => S.π^[i] x0
      X_succ := fun i => by simp only [iterate_succ_apply']; rfl
      X_lt := fun i => (S.iter (k := i) hx0m).1
      X_inj := by
        intro i j hi hj h
        have h1 := (S.iter (k := i) hx0m).2
        have h2 := (S.iter (k := j) hx0m).2
        have h3 : f^[i] (S.q x0) = f^[j] (S.q x0) := by
          rw [h1, h2]
          exact congrArg S.q h
        have hinj := iterate_injOn_Iio_minimalPeriod (f := f) (x := S.q x0)
        rw [hper0] at hinj
        exact hinj (show i ∈ Iio m from hi) (show j ∈ Iio m from hj) h3
      X_m := S.pi_iter_m hx0m
      X_start := by
        by_cases h1 : S.π (v 0) = v 0 + 1
        · left
          refine ⟨?_, h1⟩
          show S.π^[0] x0 = v 0
          rw [iterate_zero, id_eq, hx0def]
          simp [h1]
        · right
          rcases hGs with h | h
          · exact absurd h h1
          · refine ⟨?_, h⟩
            show S.π^[0] x0 = v 0 + 1
            rw [iterate_zero, id_eq, hx0def]
            simp [h1] }
  have hZe : ∀ e, e % 2 = 0 → e + 3 ≤ m → S.Cov (v (m - 2)) (v e) := by
    intro e he1 he2
    rcases Nat.eq_zero_or_pos e with rfl | hepos
    · exact hvcl
    · have h2 : 2 ≤ e := by omega
      obtain ⟨h1, h2'⟩ := D.final hodd h2 he1 he2
      have := hvlt (m - 2) (by omega)
      have := hvlt e (by omega)
      exact S.cov_of_between hf (by omega) (by omega) h1 h2'
  have hinjy : ∀ y, minimalPeriod f y = m → ∀ i j, i < m → j < m → f^[i] y = f^[j] y → i = j := by
    intro y hy i j hi hj h
    have hinj := iterate_injOn_Iio_minimalPeriod (f := f) (x := y)
    rw [hy] at hinj
    exact hinj (show i ∈ Iio m from hi) (show j ∈ Iio m from hj) h
  rcases Nat.lt_or_ge m k with hmk | hkm
  · -- `k > m`: loop through the first gap `k - m + 2` times, then along the chain
    obtain ⟨r, hr⟩ : ∃ r, r = k - (m - 2) := ⟨_, rfl⟩
    have hr3 : 3 ≤ r := by omega
    obtain ⟨Jf, hJf1, hJf2⟩ : ∃ Jf : ℕ → ℕ, (∀ c, c < r → Jf c = v 0) ∧
        (∀ c, r ≤ c → Jf c = v (c - r + 1)) :=
      ⟨fun c => if c < r then v 0 else v (c - r + 1), fun c hc => by simp [hc],
        fun c hc => by simp [not_lt.mpr hc]⟩
    have hlt : ∀ i, Jf (i % k) + 1 < m := by
      intro i
      have hc := Nat.mod_lt i hk
      by_cases h : i % k < r
      · rw [hJf1 _ h]; omega
      · rw [hJf2 _ (by omega)]
        have := hvlt (i % k - r + 1) (by omega)
        omega
    have hcov : ∀ i, S.Cov (Jf (i % k)) (Jf ((i + 1) % k)) := by
      intro i
      have hc := Nat.mod_lt i hk
      rcases nat_mod_succ_cases i k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        by_cases hc1 : i % k + 1 < r
        · rw [hJf1 _ (by omega), hJf1 _ hc1, hv0]
          exact htl
        · by_cases hc2 : i % k < r
          · rw [hJf1 _ hc2, hJf2 _ (by omega), show i % k + 1 - r + 1 = 0 + 1 by omega]
            exact hvstep 0 (by omega)
          · rw [hJf2 _ (by omega), hJf2 _ (by omega),
              show i % k + 1 - r + 1 = i % k - r + 1 + 1 by omega]
            exact hvstep _ (by omega)
      · rw [h2, hJf2 _ (by omega), hJf1 0 (by omega), show i % k - r + 1 = m - 2 by omega]
        exact hvcl
    have hprim : ∀ p, 0 < p → p < k → ∃ i, Jf ((i + p) % k) ≠ Jf (i % k) := by
      intro p hp hpk
      refine ⟨k - 1, ?_⟩
      have e1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
      have e2 : (k - 1 + p) % k = p - 1 := by
        have : k - 1 + p - k = p - 1 := by omega
        rw [Nat.mod_eq_sub_mod (by omega), this, Nat.mod_eq_of_lt (by omega)]
      rw [e1, e2, hJf2 (k - 1) (by omega), show k - 1 - r + 1 = m - 2 by omega]
      intro h
      by_cases hp1 : p - 1 < r
      · rw [hJf1 _ hp1] at h
        have := hvinj 0 (m - 2) (by omega) (by omega) h
        omega
      · rw [hJf2 _ (by omega)] at h
        have := hvinj (p - 1 - r + 1) (m - 2) (by omega) (by omega) h
        omega
    obtain ⟨y, hy, hcyc, hit⟩ := S.exists_loop_point hf (J := fun i => Jf (i % k)) hk hlt hcov
      (fun i => by simp only [Nat.add_mod_right]) hprim
    rcases hcyc with h | ⟨r', hr', hrq⟩
    · exact ⟨y, h⟩
    · exfalso
      have hy' : minimalPeriod f y = m := by rw [← hrq]; exact S.per r' hr'
      have hJ : ∀ c, c < 3 → Jf (c % k) = v 0 := by
        intro c hc
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hJf1 c (by omega)
      have hv0m' : v 0 + 1 < m := by omega
      have hpos : ∀ i, i < 3 → v 0 ≤ S.π^[i] r' ∧ S.π^[i] r' ≤ v 0 + 1 := by
        intro i hi
        have h1 : f^[i] y ∈ Icc (S.q (Jf (i % k))) (S.q (Jf (i % k) + 1)) := hit i
        rw [hJ i hi, ← hrq, (S.iter (k := i) hr').2] at h1
        obtain ⟨hl, hu⟩ := h1
        have hs := (S.iter (k := i) hr').1
        constructor
        · by_contra hc
          push Not at hc
          exact absurd hl (not_le.mpr ((S.q_lt_iff hs (by omega)).mpr hc))
        · by_contra hc
          push Not at hc
          exact absurd hu (not_le.mpr ((S.q_lt_iff hv0m' hs).mpr hc))
      have hdist : ∀ i j, i < 3 → j < 3 → S.π^[i] r' = S.π^[j] r' → i = j := by
        intro i j hi hj h
        have h1 := (S.iter (k := i) hr').2
        have h2 := (S.iter (k := j) hr').2
        apply hinjy y hy' i j (by omega) (by omega)
        rw [← hrq, h1, h2, h]
      have a0 := hpos 0 (by omega)
      have a1 := hpos 1 (by omega)
      have a2 := hpos 2 (by omega)
      have d01 : S.π^[0] r' ≠ S.π^[1] r' := fun h => by
        have := hdist 0 1 (by omega) (by omega) h; omega
      have d02 : S.π^[0] r' ≠ S.π^[2] r' := fun h => by
        have := hdist 0 2 (by omega) (by omega) h; omega
      have d12 : S.π^[1] r' ≠ S.π^[2] r' := fun h => by
        have := hdist 1 2 (by omega) (by omega) h; omega
      omega
  · -- `k < m` even: loop along the end of the chain
    have hke : k % 2 = 0 := by omega
    have hkm' : k < m := by omega
    obtain ⟨e, he⟩ : ∃ e, e = m - 1 - k := ⟨_, rfl⟩
    have he2 : e % 2 = 0 := by omega
    have hek : e + k = m - 1 := by omega
    have hlt : ∀ i, v (e + i % k) + 1 < m := by
      intro i
      have hc := Nat.mod_lt i hk
      have := hvlt (e + i % k) (by omega)
      omega
    have hcov : ∀ i, S.Cov (v (e + i % k)) (v (e + (i + 1) % k)) := by
      intro i
      have hc := Nat.mod_lt i hk
      rcases nat_mod_succ_cases i k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, show e + (i % k + 1) = e + i % k + 1 by omega]
        exact hvstep _ (by omega)
      · rw [h2, show e + i % k = m - 2 by omega, Nat.add_zero]
        exact hZe e he2 (by omega)
    have hprim : ∀ p, 0 < p → p < k → ∃ i, v (e + (i + p) % k) ≠ v (e + i % k) := by
      intro p hp hpk
      refine ⟨0, ?_⟩
      rw [Nat.zero_add, Nat.zero_mod, Nat.mod_eq_of_lt hpk]
      intro h
      have := hvinj _ _ (by omega) (by omega) h
      omega
    obtain ⟨y, hy, hcyc, hit⟩ := S.exists_loop_point hf (J := fun i => v (e + i % k)) hk hlt hcov
      (fun i => by simp only [Nat.add_mod_right]) hprim
    rcases hcyc with h | ⟨r', hr', hrq⟩
    · exact ⟨y, h⟩
    · exfalso
      have := (show IsPeriodicPt f k y from hy).minimalPeriod_dvd
      rw [← hrq, S.per r' hr'] at this
      have := Nat.le_of_dvd hk this
      omega

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), the Štefan step: a point of odd prime period `m ≥ 3` gives points of prime period `k` for every `k` which is `1`, even, or
larger than `m` (choose the smallest odd period `≥ 3` and apply the Štefan lemma). -/
theorem exists_minimalPeriod_of_odd_period {f : ℝ → ℝ} (hf : Continuous f) {m : ℕ} (hm : 3 ≤ m)
    (hodd : m % 2 = 1) (hper : ∃ x, minimalPeriod f x = m) {k : ℕ} (hk : 0 < k)
    (hkk : m < k ∨ k % 2 = 0 ∨ k = 1) : ∃ y, minimalPeriod f y = k := by
  classical
  have hex : ∃ l, 3 ≤ l ∧ l % 2 = 1 ∧ ∃ y, minimalPeriod f y = l := ⟨m, hm, hodd, hper⟩
  obtain ⟨⟨h3, hodd', x, hx⟩, hle⟩ : (3 ≤ Nat.find hex ∧ Nat.find hex % 2 = 1 ∧
      ∃ y, minimalPeriod f y = Nat.find hex) ∧ Nat.find hex ≤ m :=
    ⟨Nat.find_spec hex, Nat.find_min' hex ⟨hm, hodd, hper⟩⟩
  refine stefan_periods hf hx h3 hodd' ?_ hk (by omega)
  intro l hl3 hlm hlodd hy
  exact Nat.find_min hex hlm ⟨hl3, Nat.odd_iff.mp hlodd, hy⟩

private lemma period_of_iterate_two {f : ℝ → ℝ} {y : ℝ} {n : ℕ}
    (h : minimalPeriod (f^[2]) y = n) :
    (minimalPeriod f y = n ∧ n % 2 = 1) ∨ minimalPeriod f y = 2 * n := by
  rw [minimalPeriod_iterate_eq_div_gcd two_ne_zero] at h
  rcases Nat.even_or_odd (minimalPeriod f y) with he | ho
  · have h2 : (2 : ℕ) ∣ minimalPeriod f y := even_iff_two_dvd.mp he
    rw [Nat.gcd_eq_right h2] at h
    right
    omega
  · have hodd : minimalPeriod f y % 2 = 1 := Nat.odd_iff.mp ho
    have hg : Nat.gcd (minimalPeriod f y) 2 = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right (minimalPeriod f y) 2) with h1 | h1
      · exact h1
      · exfalso
        have := Nat.gcd_dvd_left (minimalPeriod f y) 2
        rw [h1] at this
        omega
    rw [hg, Nat.div_one] at h
    left
    exact ⟨h, by omega⟩

private lemma sharkovskiiLT_iff_aux {a m b l : ℕ} (hm : m % 2 = 1) (hl : l % 2 = 1) :
    SharkovskiiLT (2 ^ a * m) (2 ^ b * l) ↔ sharkovskiiAux a m b l := by
  have h1 := factorization_two_pow_mul_odd a m (by omega) (by omega)
  have h2 := factorization_two_pow_mul_odd b l (by omega) (by omega)
  unfold SharkovskiiLT
  rw [h1.1, h1.2, h2.1, h2.2]

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), the case `n = m` odd, `m ≥ 3`. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem sharkovskii_odd_core {f : ℝ → ℝ} (hf : Continuous f) {m : ℕ} (hm3 : 3 ≤ m)
    (hodd : m % 2 = 1) (hper : ∃ x, minimalPeriod f x = m) {k : ℕ} (hk : 0 < k)
    (hlt : SharkovskiiLT m k) : ∃ y, minimalPeriod f y = k := by
  obtain ⟨b, l, hl, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
  have hl' : l % 2 = 1 := Nat.odd_iff.mp hl
  have hlt' := (sharkovskiiLT_iff_aux (a := 0) (b := b) hodd hl').mp (by rwa [pow_zero, one_mul])
  refine exists_minimalPeriod_of_odd_period hf hm3 hodd hper hk ?_
  unfold sharkovskiiAux at hlt'
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases Nat.eq_or_lt_of_le (show 1 ≤ l by omega) with h1 | h1
    · right; right; subst h1; simp
    · left; simp only [pow_zero, one_mul]; omega
  · right; left
    have : 2 ∣ 2 ^ b * l := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) l
    omega

/-- The case `n = 2^a · m` of Sharkovskii's theorem, `m ≥ 3` odd, by induction on `a` through `f ↦ f²`. -/
theorem sharkovskii_odd_mul_two_pow : ∀ (a : ℕ) {f : ℝ → ℝ}, Continuous f → ∀ {m : ℕ}, 3 ≤ m →
    m % 2 = 1 → (∃ x, minimalPeriod f x = 2 ^ a * m) → ∀ {k : ℕ}, 0 < k →
    SharkovskiiLT (2 ^ a * m) k → ∃ y, minimalPeriod f y = k := by
  intro a
  induction a with
  | zero =>
    intro f hf m hm3 hodd hper k hk hlt
    rw [pow_zero, one_mul] at hper hlt
    exact sharkovskii_odd_core hf hm3 hodd hper hk hlt
  | succ a ih =>
    intro f hf m hm3 hodd hper k hk hlt
    obtain ⟨x, hx⟩ := hper
    have hg : Continuous (f^[2]) := hf.iterate 2
    have hxg : minimalPeriod (f^[2]) x = 2 ^ a * m := by
      rw [minimalPeriod_iterate_eq_div_gcd two_ne_zero, hx, show 2 ^ (a + 1) * m = 2 * (2 ^ a * m) by ring]
      have : Nat.gcd (2 * (2 ^ a * m)) 2 = 2 := Nat.gcd_eq_right (Dvd.intro _ rfl)
      rw [this]
      omega
    have h2 : 2 ≤ 2 ^ (a + 1) * m := by
      have := Nat.one_le_two_pow (n := a)
      rw [pow_succ]
      nlinarith
    obtain ⟨b, l, hl, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
    have hl' : l % 2 = 1 := Nat.odd_iff.mp hl
    have hlt' := (sharkovskiiLT_iff_aux hodd hl').mp hlt
    unfold sharkovskiiAux at hlt'
    by_cases hl1 : l = 1
    · subst hl1
      rw [mul_one]
      rcases Nat.lt_or_ge b 2 with hb | hb
      · rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
        · obtain ⟨p, hp⟩ := exists_isFixedPt_of_two_le_minimalPeriod hf hx h2
          exact ⟨p, by simpa using minimalPeriod_eq_one_iff_isFixedPt.mpr hp⟩
        · obtain ⟨y, hy⟩ := exists_minimalPeriod_two_of_two_le_minimalPeriod hf hx h2
          exact ⟨y, by simpa using hy⟩
      · have hlt2 : SharkovskiiLT (2 ^ a * m) (2 ^ (b - 1) * 1) :=
          (sharkovskiiLT_iff_aux hodd (by norm_num)).mpr (by unfold sharkovskiiAux; omega)
        obtain ⟨y, hy⟩ := ih hg hm3 hodd ⟨x, hxg⟩ (Nat.pos_of_ne_zero (by positivity)) hlt2
        rw [mul_one] at hy
        refine ⟨y, ?_⟩
        have := minimalPeriod_eq_two_pow_succ_of_iterate_two (f := f) (by omega) hy
        rwa [show b - 1 + 1 = b by omega] at this
    · have hl3 : 3 ≤ l := by omega
      have hb1 : 1 ≤ b := by omega
      have hlt2 : SharkovskiiLT (2 ^ a * m) (2 ^ (b - 1) * l) :=
        (sharkovskiiLT_iff_aux hodd hl').mpr (by unfold sharkovskiiAux; omega)
      obtain ⟨y, hy⟩ := ih hg hm3 hodd ⟨x, hxg⟩ (by positivity) hlt2
      rcases period_of_iterate_two hy with ⟨hp, hpodd⟩ | hp
      · -- the point has odd period `2^(b-1) * l` for `f`, so `b = 1`; use the case `a = 0`
        have hb1' : b - 1 = 0 := by
          by_contra hne
          have : 2 ∣ 2 ^ (b - 1) * l := Dvd.dvd.mul_right (dvd_pow_self 2 hne) l
          omega
        rw [hb1', pow_zero, one_mul] at hp
        refine sharkovskii_odd_core hf hl3 hl' ⟨y, hp⟩ hk ?_
        have hb : b = 1 := by omega
        subst hb
        have := (sharkovskiiLT_iff_aux (a := 0) (b := 1) hl' hl').mpr (by unfold sharkovskiiAux; omega)
        rwa [pow_zero, one_mul] at this
      · refine ⟨y, ?_⟩
        rw [hp]
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]
        ring

/-- Morris, Topology Without Tears, Theorem A3.6.4 (TP-448), Sharkovskii's Theorem: if a continuous
`f : ℝ → ℝ` has a point of prime period `n` and `k` comes after `n` in Sharkovskii's ordering
`3 ▹ 5 ▹ 7 ▹ ... ▹ 2·3 ▹ 2·5 ▹ ... ▹ 2² ▹ 2 ▹ 1`, then `f` has a point of prime period `k`. -/
@[kb "morris2024" "Theorem A3.6.4, p. 458"]
theorem sharkovskii_theorem {f : ℝ → ℝ} (hf : Continuous f) {n : ℕ} (hn : 0 < n)
    (hper : ∃ x, minimalPeriod f x = n) {k : ℕ} (hk : 0 < k) (hlt : SharkovskiiLT n k) :
    ∃ y, minimalPeriod f y = k := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hm' : m % 2 = 1 := Nat.odd_iff.mp hm
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hper hlt
    exact sharkovskii_of_period_two_pow hf hper hk hlt
  · exact sharkovskii_odd_mul_two_pow a hf (by omega) hm' hper hk hlt

end UndergradKB.Topology
