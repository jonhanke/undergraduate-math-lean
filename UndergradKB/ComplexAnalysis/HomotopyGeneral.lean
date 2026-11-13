import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import UndergradKB.ComplexAnalysis.PiecewisePath
import UndergradKB.ComplexAnalysis.Homotopy
import UndergradKB.ComplexAnalysis.CauchyDisc

/-!
# Cauchy's theorem for continuous homotopies (rows CX-067, CX-068)

Beck et al., *A First Course in Complex Analysis*, Theorem 4.3.4 in full generality: if `f` is
holomorphic on the open set `G` and the piecewise smooth closed paths `γ₀, γ₁` (parametrised on
`[0, 1]`) are `G`-homotopic through a merely continuous homotopy `h`, then `∫_{γ₀} f = ∫_{γ₁} f`.
The book proves only the case of a `C²` homotopy (`cauchy_theorem_C2_homotopy`); here the full
statement is proved by the standard subdivision argument with local primitives:

* the compact image `h([0,1]²)` has an `ε`-neighbourhood inside `G`, and by uniform continuity there
  is `n` such that `h` maps each grid square `[j/n, (j+1)/n] × [k/n, (k+1)/n]` into the disc of
  radius `ε` about the image of its corner; on that disc `f` has a primitive `F j k`;
* two primitives on overlapping discs differ by a constant on the (convex) intersection;
* the row sums `R k σ = Σ_j (F j k (h ((j+1)/n) σ) - F j k (h (j/n) σ))` do not change from the
  bottom to the top of a row (telescoping, using that the paths are closed) nor from one row to the
  next (shared corners), and the bottom and top rows give the two path integrals.

Consequences: Corollary 4.3.8 (contractible closed paths have zero integrals).
-/

open Set Metric Filter Topology MeasureTheory

namespace UndergradKB.ComplexAnalysis

variable {f : ℂ → ℂ}

/-- Two primitives of `f` on two open discs change by the same amount between two points of the
intersection of the discs. -/
lemma primitive_sub_eq {F₁ F₂ : ℂ → ℂ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (h₁ : ∀ z ∈ ball c₁ r₁, HasDerivAt F₁ (f z) z) (h₂ : ∀ z ∈ ball c₂ r₂, HasDerivAt F₂ (f z) z)
    {z w : ℂ} (hz₁ : z ∈ ball c₁ r₁) (hz₂ : z ∈ ball c₂ r₂) (hw₁ : w ∈ ball c₁ r₁)
    (hw₂ : w ∈ ball c₂ r₂) :
    F₁ z - F₁ w = F₂ z - F₂ w := by
  have hU : IsOpen (ball c₁ r₁ ∩ ball c₂ r₂) := isOpen_ball.inter isOpen_ball
  have hd : ∀ x ∈ ball c₁ r₁ ∩ ball c₂ r₂, HasDerivAt (fun x => F₁ x - F₂ x) 0 x := fun x hx => by
    have := (h₁ x hx.1).sub (h₂ x hx.2)
    rwa [sub_self] at this
  have := hU.is_const_of_deriv_eq_zero
    ((convex_ball c₁ r₁).inter (convex_ball c₂ r₂)).isPreconnected
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hd x hx).deriv)
    (⟨hz₁, hz₂⟩ : z ∈ ball c₁ r₁ ∩ ball c₂ r₂) (⟨hw₁, hw₂⟩ : w ∈ ball c₁ r₁ ∩ ball c₂ r₂)
  linear_combination this

/-- Cyclic telescoping: if consecutive terms match and the last matches the first, the sum of the
differences vanishes. -/
lemma sum_telescope_cyclic (m : ℕ) (D : ℕ → ℕ → ℂ)
    (h : ∀ j, j + 1 < m + 1 → D j (j + 1) = D (j + 1) (j + 1)) (hc : D m (m + 1) = D 0 0) :
    ∑ j ∈ Finset.range (m + 1), (D j (j + 1) - D j j) = 0 := by
  have key : ∀ i, i ≤ m →
      ∑ j ∈ Finset.range (i + 1), (D j (j + 1) - D j j) = D i (i + 1) - D 0 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [Finset.sum_range_succ, ih (by omega), h i (by omega)]
      ring
  rw [key m le_rfl, hc, sub_self]

/-- The grid of a continuous map on the unit square into an open set. -/
lemma exists_grid {G : Set ℂ} (hG : IsOpen G) {h : ℝ → ℝ → ℂ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => h p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, h t s ∈ G) :
    ∃ ε > 0, ∃ m : ℕ,
      (∀ j k : ℕ, j < m + 1 → k < m + 1 →
        ball (h ((j : ℝ) / (m + 1)) ((k : ℝ) / (m + 1))) ε ⊆ G) ∧
      (∀ j k : ℕ, j < m + 1 → k < m + 1 →
        ∀ t ∈ Icc ((j : ℝ) / (m + 1)) (((j : ℝ) + 1) / (m + 1)),
        ∀ s ∈ Icc ((k : ℝ) / (m + 1)) (((k : ℝ) + 1) / (m + 1)),
          h t s ∈ ball (h ((j : ℝ) / (m + 1)) ((k : ℝ) / (m + 1))) ε) := by
  set K := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨ε, hε, hth⟩ := (hK.image_of_continuousOn hc).exists_thickening_subset_open hG
    (by rintro _ ⟨p, hp, rfl⟩; exact hmem _ hp.1 _ hp.2)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hc)
    ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcorner : ∀ j : ℕ, j < m + 1 → (j : ℝ) / (m + 1) ∈ Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, (div_le_one hN).2 ?_⟩
    have : (j : ℝ) < m + 1 := by exact_mod_cast hj
    linarith
  refine ⟨ε, hε, m, fun j k hj hk => ?_, fun j k hj hk t ht s hs => ?_⟩
  · exact (ball_subset_thickening (mem_image_of_mem (fun p : ℝ × ℝ => h p.1 p.2)
      (show ((j : ℝ) / (m + 1), (k : ℝ) / (m + 1)) ∈ K from ⟨hcorner j hj, hcorner k hk⟩)) ε).trans hth
  · have hj' : (j : ℝ) + 1 ≤ m + 1 := by exact_mod_cast hj
    have hk' : (k : ℝ) + 1 ≤ m + 1 := by exact_mod_cast hk
    have hup : ∀ i : ℝ, i + 1 ≤ m + 1 → (i + 1) / (m + 1) ≤ 1 := fun i hi => (div_le_one hN).2 hi
    have htK : t ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (by positivity) ht.1, ht.2.trans (hup _ hj')⟩
    have hsK : s ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (by positivity) hs.1, hs.2.trans (hup _ hk')⟩
    have hstep : ∀ (i x : ℝ), x ∈ Icc (i / (m + 1)) ((i + 1) / (m + 1)) →
        |x - i / (m + 1)| < δ := by
      intro i x hx
      have e : (i + 1) / (m + 1) = i / (m + 1) + 1 / (m + 1) := by ring
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, e ▸ hx.2, hm]
    have hd : dist ((t, s) : ℝ × ℝ) ((j : ℝ) / (m + 1), (k : ℝ) / (m + 1)) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (hstep _ _ ht) (hstep _ _ hs)
    have := hU (t, s) ⟨htK, hsK⟩ _ ⟨hcorner j hj, hcorner k hk⟩ hd
    exact this

/-- The integral along a piecewise smooth path on `[0, 1]` is the sum of the increments of local
primitives along a subdivision into `m + 1` equal pieces. -/
lemma pathIntegral_eq_sum_increments {γ : ℝ → ℂ} (hγ : IsPiecewiseSmooth γ 0 1) (m : ℕ)
    (F : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (hF : ∀ j < m + 1, ∀ z ∈ U j, HasDerivAt (F j) (f z) z)
    (hfU : ∀ j < m + 1, ContinuousOn f (U j))
    (hsub : ∀ j < m + 1, ∀ t ∈ Icc ((j : ℝ) / (m + 1)) (((j : ℝ) + 1) / (m + 1)), γ t ∈ U j)
    (hf : ContinuousOn f (γ '' Icc 0 1)) :
    pathIntegral f γ 0 1 = ∑ j ∈ Finset.range (m + 1),
      (F j (γ (((j : ℝ) + 1) / (m + 1))) - F j (γ ((j : ℝ) / (m + 1)))) := by
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set a : ℕ → ℝ := fun j => (j : ℝ) / (m + 1) with ha
  have ha0 : a 0 = 0 := by simp [a]
  have ham : a (m + 1) = 1 := by simp only [a]; push_cast; exact div_self hN.ne'
  have hsucc : ∀ j : ℕ, a (j + 1) = ((j : ℝ) + 1) / (m + 1) := by intro j; simp [a]
  have hle : ∀ j : ℕ, a j ≤ a (j + 1) := fun j => by
    rw [hsucc]; exact div_le_div_of_nonneg_right (by linarith) hN.le
  have hin : ∀ j < m + 1, 0 ≤ a j ∧ a (j + 1) ≤ 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [hsucc]
    have : (j : ℝ) + 1 ≤ m + 1 := by exact_mod_cast hj
    exact (div_le_one hN).2 this
  have hint := hγ.intervalIntegrable_integrand zero_le_one hf
  have hpiece : ∀ j < m + 1,
      IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume (a j) (a (j + 1)) := by
    intro j hj
    refine hint.mono_set ?_
    rw [uIcc_of_le (hle j), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (hin j hj).1 (hin j hj).2
  unfold pathIntegral
  have hs := intervalIntegral.sum_integral_adjacent_intervals hpiece
  rw [ha0, ham] at hs
  rw [← hs]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < m + 1 := Finset.mem_range.1 hj
  have := pathIntegral_eq_sub_of_isPiecewiseSmooth (f := f) (F := F j) (U := U j)
    (hγ.mono (hin j hj').1 (hin j hj').2) (hle j)
    (fun t ht => hsub j hj' t (by rw [← hsucc]; exact ht)) (hF j hj') (hfU j hj')
  unfold pathIntegral at this
  rw [this, hsucc]

/-- Beck Theorem 4.3.4 (CX-067), Cauchy's theorem: if `f` is holomorphic on the open set `G` and the
piecewise smooth closed paths `γ₀, γ₁` on `[0, 1]` are `G`-homotopic (Definition 4.3.1, a continuous
homotopy), then `∫_{γ₀} f = ∫_{γ₁} f`. -/
@[kb "beck2025" "Theorem 4.3.4, p. 78"]
theorem cauchy_theorem_homotopy {G : Set ℂ} (hG : IsOpen G) (hf : DifferentiableOn ℂ f G)
    {γ₀ γ₁ : ℝ → ℂ} (hγ₀ : IsPiecewiseSmooth γ₀ 0 1) (hγ₁ : IsPiecewiseSmooth γ₁ 0 1)
    (hh : IsGHomotopic G γ₀ γ₁) :
    pathIntegral f γ₀ 0 1 = pathIntegral f γ₁ 0 1 := by
  obtain ⟨h, hc, hmem, h0, h1, hcl⟩ := hh
  obtain ⟨ε, hε, m, hB, hQ⟩ := exists_grid hG hc hmem
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (m : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hNdef] at hB hQ
  have hN : (0 : ℝ) < N := by rw [hNdef]; positivity
  have hex : ∀ j k : ℕ, ∃ F : ℂ → ℂ, j < m + 1 → k < m + 1 →
      ∀ z ∈ ball (h ((j : ℝ) / N) ((k : ℝ) / N)) ε, HasDerivAt F (f z) z := by
    intro j k
    by_cases hjk : j < m + 1 ∧ k < m + 1
    · obtain ⟨F, hF⟩ := exists_antiderivative_ball (hf.mono (hB j k hjk.1 hjk.2))
      exact ⟨F, fun _ _ => hF⟩
    · exact ⟨0, fun hj hk => absurd ⟨hj, hk⟩ hjk⟩
  choose F hF using hex
  -- the grid points
  have lo : ∀ i : ℕ, (i : ℝ) / N ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := fun i =>
    ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hN.le⟩
  have hi : ∀ i : ℕ, ((i : ℝ) + 1) / N ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := fun i =>
    ⟨div_le_div_of_nonneg_right (by linarith) hN.le, le_rfl⟩
  have cast1 : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := fun i => by push_cast; ring
  -- row sums
  let R : ℕ → ℝ → ℂ := fun k σ => ∑ j ∈ Finset.range (m + 1),
    (F j k (h (((j : ℝ) + 1) / N) σ) - F j k (h ((j : ℝ) / N) σ))
  -- the closing condition on grid levels
  have hclose : ∀ l : ℕ, l ≤ m + 1 → h ((((m : ℕ) : ℝ) + 1) / N) ((l : ℝ) / N) = h 0 ((l : ℝ) / N) := by
    intro l hl
    have h1N : (((m : ℕ) : ℝ) + 1) / N = 1 := by rw [← hNdef]; exact div_self hN.ne'
    rw [h1N]
    refine (hcl _ ⟨by positivity, (div_le_one hN).2 (by rw [hNdef]; exact_mod_cast hl)⟩).symm
  -- Claim A: within a row
  have hA : ∀ k < m + 1, R k ((k : ℝ) / N) = R k (((k : ℝ) + 1) / N) := by
    intro k hk
    let D : ℕ → ℕ → ℂ := fun j i =>
      F j k (h ((i : ℝ) / N) ((k : ℝ) / N)) - F j k (h ((i : ℝ) / N) (((k : ℝ) + 1) / N))
    have hD := sum_telescope_cyclic m D (fun j hj => ?_) ?_
    · have e : R k ((k : ℝ) / N) - R k (((k : ℝ) + 1) / N) =
          ∑ j ∈ Finset.range (m + 1), (D j (j + 1) - D j j) := by
        simp only [R, D, ← Finset.sum_sub_distrib, cast1]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      linear_combination e + hD
    · -- consecutive columns share the right edge
      simp only [D, cast1]
      have hj0 : j < m + 1 := by omega
      have m1 := hQ j k hj0 hk _ (hi j) _ (lo k)
      have m2 := hQ j k hj0 hk _ (hi j) _ (hi k)
      have m3 := hQ (j + 1) k hj hk _ (lo (j + 1)) _ (lo k)
      have m4 := hQ (j + 1) k hj hk _ (lo (j + 1)) _ (hi k)
      rw [cast1] at m3 m4
      exact primitive_sub_eq (hF j k hj0 hk) (hF (j + 1) k hj hk) m1 (by rw [cast1]; exact m3) m2
        (by rw [cast1]; exact m4)
    · -- the last column matches the first, since the paths are closed
      simp only [D]
      have hc1 := hclose k hk.le
      have hc2 := hclose (k + 1) hk
      rw [cast1] at hc2
      rw [cast1, hc1, hc2]
      have m1 := hQ m k (Nat.lt_succ_self m) hk _ (hi m) _ (lo k)
      have m2 := hQ m k (Nat.lt_succ_self m) hk _ (hi m) _ (hi k)
      have m3 := hQ 0 k (Nat.succ_pos m) hk _ (lo 0) _ (lo k)
      have m4 := hQ 0 k (Nat.succ_pos m) hk _ (lo 0) _ (hi k)
      have hF0 := hF 0 k (Nat.succ_pos m) hk
      rw [hc1] at m1
      rw [hc2] at m2
      simp only [Nat.cast_zero, zero_div] at m3 m4 hF0 ⊢
      exact primitive_sub_eq (hF m k (Nat.lt_succ_self m) hk) hF0 m1 m3 m2 m4
  -- Claim B: between rows
  have hBr : ∀ k, k + 1 < m + 1 → R k (((k : ℝ) + 1) / N) = R (k + 1) (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    have hk0 : k < m + 1 := by omega
    simp only [R, cast1]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < m + 1 := Finset.mem_range.1 hj
    have m1 := hQ j k hj' hk0 _ (hi j) _ (hi k)
    have m2 := hQ j k hj' hk0 _ (lo j) _ (hi k)
    have m3 := hQ j (k + 1) hj' hk _ (hi j) _ (lo (k + 1))
    have m4 := hQ j (k + 1) hj' hk _ (lo j) _ (lo (k + 1))
    have hF' := hF j (k + 1) hj' hk
    rw [cast1] at m3 m4 hF'
    exact primitive_sub_eq (hF j k hj' hk0) hF' m1 m3 m2 m4
  -- chain the rows
  have hchain : ∀ k, k < m + 1 → R k ((k : ℝ) / N) = R 0 0 := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.cast_zero, zero_div]
    | succ k ih =>
      intro hk
      rw [← hBr k hk, ← hA k (by omega), ih (by omega)]
  -- the bottom and the top rows are the path integrals
  subst hNdef
  have hfc : ContinuousOn f G := hf.continuousOn
  have himg0 : ContinuousOn f (γ₀ '' Icc 0 1) :=
    hfc.mono (by rintro _ ⟨t, ht, rfl⟩; rw [← h0 t ht]; exact hmem t ht 0 ⟨le_rfl, zero_le_one⟩)
  have himg1 : ContinuousOn f (γ₁ '' Icc 0 1) :=
    hfc.mono (by rintro _ ⟨t, ht, rfl⟩; rw [← h1 t ht]; exact hmem t ht 1 ⟨zero_le_one, le_rfl⟩)
  have hIcc : ∀ j < m + 1, ∀ t ∈ Icc ((j : ℝ) / ((m : ℝ) + 1)) (((j : ℝ) + 1) / ((m : ℝ) + 1)), t ∈ Icc (0 : ℝ) 1 := by
    intro j hj t ht
    refine ⟨le_trans (by positivity) ht.1, ht.2.trans ((div_le_one hN).2 ?_)⟩
    exact_mod_cast hj
  have hbot : pathIntegral f γ₀ 0 1 = R 0 0 := by
    rw [pathIntegral_eq_sum_increments hγ₀ m (fun j => F j 0)
      (fun j => ball (h ((j : ℝ) / ((m : ℝ) + 1)) 0) ε)
      (fun j hj => by simpa using hF j 0 hj (Nat.succ_pos m))
      (fun j hj => hfc.mono (by simpa using hB j 0 hj (Nat.succ_pos m)))
      (fun j hj t ht => by
        rw [← h0 t (hIcc j hj t ht)]
        simpa using hQ j 0 hj (Nat.succ_pos m) t ht 0 (by simpa using lo 0)) himg0]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.1 hj
    rw [← h0 _ (hIcc j hj' _ (hi j)), ← h0 _ (hIcc j hj' _ (lo j))]
  have htop : pathIntegral f γ₁ 0 1 = R m (((m : ℝ) + 1) / ((m : ℝ) + 1)) := by
    rw [pathIntegral_eq_sum_increments hγ₁ m (fun j => F j m)
      (fun j => ball (h ((j : ℝ) / ((m : ℝ) + 1)) ((m : ℝ) / ((m : ℝ) + 1))) ε)
      (fun j hj => hF j m hj (Nat.lt_succ_self m))
      (fun j hj => hfc.mono (hB j m hj (Nat.lt_succ_self m)))
      (fun j hj t ht => by
        rw [← h1 t (hIcc j hj t ht)]
        have := hQ j m hj (Nat.lt_succ_self m) t ht 1 ⟨?_, ?_⟩
        · exact this
        · exact (div_le_one hN).2 (by linarith)
        · exact (le_div_iff₀ hN).2 (by linarith)) himg1]
    have h1N : ((m : ℝ) + 1) / ((m : ℝ) + 1) = 1 := div_self hN.ne'
    rw [h1N]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.1 hj
    rw [← h1 _ (hIcc j hj' _ (hi j)), ← h1 _ (hIcc j hj' _ (lo j))]
  rw [hbot, htop, ← hA m (Nat.lt_succ_self m), hchain m (Nat.lt_succ_self m)]

/-- Beck Corollary 4.3.8 (CX-068): if `f` is holomorphic on the open set `G` and the piecewise smooth
closed path `γ` on `[0, 1]` is `G`-contractible (`G`-homotopic to a constant path), then
`∫_γ f = 0`. -/
@[kb "beck2025" "Corollary 4.3.8, p. 80"]
theorem pathIntegral_eq_zero_of_contractible {G : Set ℂ} (hG : IsOpen G)
    (hf : DifferentiableOn ℂ f G) {γ : ℝ → ℂ} (hγ : IsPiecewiseSmooth γ 0 1) {c : ℂ}
    (hh : IsGHomotopic G γ (fun _ => c)) : pathIntegral f γ 0 1 = 0 := by
  rw [cauchy_theorem_homotopy hG hf hγ (isPiecewiseSmooth_const c 0 1) hh, pathIntegral_const_path]

end UndergradKB.ComplexAnalysis
