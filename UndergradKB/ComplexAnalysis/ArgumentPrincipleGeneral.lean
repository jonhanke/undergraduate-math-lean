import UndergradKB.ComplexAnalysis.ArgumentPrinciple
import UndergradKB.ComplexAnalysis.ResidueGeneral
import UndergradKB.ComplexAnalysis.PiecewisePath
import UndergradKB.ComplexAnalysis.PathIntegralMore

/-!
# The argument principle and Rouché's theorem for simple closed paths (rows CX-144, CX-145)

Beck et al., *A First Course in Complex Analysis*, Theorems 9.3.2 and 9.3.3, for a positively
oriented simple closed piecewise smooth path `γ` with `γ ∼_G 0` in a region `G`.

* `argument_principle` (Theorem 9.3.2): if `f` is analytic and nonzero on `G` outside a finite set
  `S`, where it is meromorphic (not identically zero), and `γ` avoids `S`, then
  `(2πi)⁻¹ ∫_γ f'/f` is the sum of the orders of `f` at the points of `S` inside `γ`. It follows from
  the residue theorem (Theorem 9.2.2) and `residue_logDeriv`.
* `isBounded_insideOf`, `closure_insideOf_subset`: the inside of a path is bounded and its closure
  lies in the inside together with the path.
* `argument_principle_zeroCountInside` (Theorem 9.3.2 without poles): for `f` analytic on a region
  `G`, nonzero on `γ`, `(2πi)⁻¹ ∫_γ f'/f` is the number of zeros inside `γ`, counted with
  multiplicity.
* `rouche` (Theorem 9.3.3): if `|g| < |f|` on `γ`, then `f + g` and `f` have the same number of zeros
  inside `γ`, counted with multiplicity.
-/

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

namespace UndergradKB.ComplexAnalysis

open Classical in
/-- Beck Theorem 9.3.2 (CX-144), **the argument principle**, for a positively oriented simple closed
path: let `f` be analytic and nonzero at every point of the open set `G` outside the finite set `S`,
meromorphic (not identically zero) at the points of `S`, and `γ` a positively oriented simple closed
piecewise smooth path avoiding `S` that is `G`-contractible. Then `(2πi)⁻¹ ∫_γ f'/f` is the sum of
the orders of `f` at the points of `S` inside `γ`: the number of zeros minus the number of poles
inside `γ`, counted with multiplicity. -/
@[kb "beck2025" "Theorem 9.3.2, p. 158"]
theorem argument_principle {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) {S : Finset ℂ}
    (hf : ∀ z ∈ G \ (S : Set ℂ), AnalyticAt ℂ f z) (hf0 : ∀ z ∈ G \ (S : Set ℂ), f z ≠ 0)
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hord : ∀ s ∈ S, meromorphicOrderAt f s ≠ ⊤)
    {γ : ℝ → ℂ} (hγ : IsPositivelyOrientedSimpleClosed γ)
    (hγS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ S) {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) :
    (2 * π * I)⁻¹ * pathIntegral (fun z => deriv f z / f z) γ 0 1 =
      ∑ s ∈ S.filter (· ∈ insideOf γ), ((meromorphicOrderAt f s).untop₀ : ℂ) := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (G \ (S : Set ℂ)) :=
    fun z hz => ((hf z hz).deriv.differentiableAt.div (hf z hz).differentiableAt
      (hf0 z hz)).differentiableWithinAt
  rw [residue_theorem hG hd hγ hγS hc, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]
  refine Finset.sum_congr rfl fun s hs => residue_logDeriv (hmero s (Finset.mem_filter.1 hs).1) ?_
  exact (WithTop.coe_untop₀_of_ne_top (hord s (Finset.mem_filter.1 hs).1)).symm

/-! ### Topology of the inside of a path -/

/-- The inside of a path is bounded. -/
theorem isBounded_insideOf {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) :
    Bornology.IsBounded (insideOf γ) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (isCompact_pathImage hγ).isBounded
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨max M 0, fun z hz => ?_⟩
  by_contra hzn
  rw [mem_closedBall, dist_zero_right, not_le] at hzn
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (le_max_right _ _) hzn
  set ray : ℝ → ℂ := fun t => (t : ℂ) * z with hray
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖ray t‖ = t * ‖z‖ := fun t ht => by
    simp only [ray, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hconn : IsPreconnected (ray '' Ici 1) :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hsub : ray '' Ici 1 ⊆ (pathImage γ)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hmem
    have h1 := hM _ hmem
    have ht1 : (1 : ℝ) ≤ t := ht
    rw [hnorm t (le_trans zero_le_one ht1)] at h1
    have : ‖z‖ ≤ t * ‖z‖ := le_mul_of_one_le_left hzpos.le ht1
    linarith [le_max_left M 0]
  have hw1 : z ∈ ray '' Ici 1 := ⟨1, mem_Ici.2 le_rfl, by simp [ray]⟩
  have hin := hconn.subset_connectedComponentIn hw1 hsub
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hz.2
  have hCz : ‖z‖ ≤ C := hC z (mem_connectedComponentIn hz.1)
  have hC0 : 0 ≤ C / ‖z‖ := div_nonneg (hzpos.le.trans hCz) hzpos.le
  have h2 := hC _ (hin ⟨C / ‖z‖ + 1, mem_Ici.2 (by linarith), rfl⟩)
  rw [hnorm _ (by linarith)] at h2
  have : (C / ‖z‖ + 1) * ‖z‖ = C + ‖z‖ := by field_simp
  rw [this] at h2
  linarith

/-- The closure of the inside of a path lies in the inside together with the path. -/
theorem closure_insideOf_subset {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) :
    closure (insideOf γ) ⊆ insideOf γ ∪ pathImage γ := by
  intro x hx
  by_cases hxp : x ∈ pathImage γ
  · exact Or.inr hxp
  refine Or.inl ⟨hxp, ?_⟩
  have hS : IsOpen (pathImage γ)ᶜ := (isCompact_pathImage hγ).isClosed.isOpen_compl
  obtain ⟨y, hyC, hyin⟩ := mem_closure_iff.1 hx _ hS.connectedComponentIn
    (mem_connectedComponentIn hxp)
  rw [connectedComponentIn_eq hyC]
  exact hyin.2

/-! ### Counting zeros inside a path -/

/-- The number of zeros, counted with multiplicity, of `f` inside the path `γ`. -/
noncomputable def zeroCountInside (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℕ :=
  ∑ᶠ z ∈ insideOf γ, analyticOrderNatAt f z

open Classical in
/-- Beck Theorem 9.3.2 (CX-144) without poles: for `f` analytic on a region `G`, nonzero on the
positively oriented simple closed path `γ`, which is `G`-contractible, `(2πi)⁻¹ ∫_γ f'/f` is the
number of zeros of `f` inside `γ`, counted with multiplicity. -/
@[kb "beck2025" "Theorem 9.3.2, p. 158"]
theorem argument_principle_zeroCountInside {f : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G)
    (hGc : IsPreconnected G) (hf : ∀ z ∈ G, AnalyticAt ℂ f z) {γ : ℝ → ℂ}
    (hγ : IsPositivelyOrientedSimpleClosed γ) (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) ≠ 0)
    {c : ℂ} (hc : IsGHomotopic G γ (fun _ => c)) :
    (2 * π * I)⁻¹ * pathIntegral (fun z => deriv f z / f z) γ 0 1 = zeroCountInside f γ := by
  have himgG : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G := hc.mem_left
  have hinG := hγ.inside_subset_of_contractible hG hc
  set K : Set ℂ := closure (insideOf γ) with hK
  have hKb : IsCompact K := (isBounded_insideOf hγ.smooth.continuousOn).isCompact_closure
  have hKG : K ⊆ G := fun x hx => by
    rcases closure_insideOf_subset hγ.smooth.continuousOn hx with h | ⟨t, ht, rfl⟩
    · exact hinG h
    · exact himgG t ht
  have hord : ∀ z ∈ G, analyticOrderAt f z ≠ ⊤ := by
    intro z hz htop
    have h0 : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.1 htop
    have hall := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf hGc hz h0
    exact hf0 0 ⟨le_rfl, zero_le_one⟩ (hall (himgG 0 ⟨le_rfl, zero_le_one⟩))
  have hiso : ∀ z ∈ G, ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    intro z hz
    rcases (hf z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.2 h) (hord z hz)
    · exact h
  have hfin : {z | z ∈ K ∧ f z = 0}.Finite := by
    have hcont : ContinuousOn f K := fun z hz => (hf z (hKG hz)).continuousAt.continuousWithinAt
    have hcl : IsClosed {z | z ∈ K ∧ f z = 0} :=
      hcont.preimage_isClosed_of_isClosed hKb.isClosed isClosed_singleton
    refine (hKb.of_isClosed_subset hcl fun z hz => hz.1).finite ?_
    rw [isDiscrete_iff_nhdsNE]
    intro z hz
    rw [← disjoint_iff, disjoint_principal_right]
    filter_upwards [hiso z (hKG hz.1)] with w hw hw' using hw hw'.2
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, ∀ z, z ∈ S ↔ z ∈ K ∧ f z = 0 :=
    ⟨hfin.toFinset, fun z => hfin.mem_toFinset⟩
  -- an open set containing the closure of the inside, where the only zeros are those in `S`
  set U : Set ℂ := {z | z ∈ G ∧ (f z ≠ 0 ∨ z ∈ K)} with hU
  have hUo : IsOpen U := by
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    filter_upwards [hG.mem_nhds hz.1, eventually_nhdsWithin_iff.1 (hiso z hz.1)] with w hwG hw
    refine ⟨hwG, ?_⟩
    rcases eq_or_ne w z with rfl | hwz
    · exact hz.2
    · exact Or.inl (hw hwz)
  have hKU : K ⊆ U := fun z hz => ⟨hKG hz, Or.inr hz⟩
  have himgU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := fun t ht => ⟨himgG t ht, Or.inl (hf0 t ht)⟩
  obtain ⟨c', hc'⟩ := (hγ.contractible_iff_inside_subset hUo himgU).2 (subset_closure.trans hKU)
  have hSK : ∀ s ∈ S, s ∈ K := fun s hs => ((hS s).1 hs).1
  have e := argument_principle hUo (f := f) (S := S)
    (fun z hz => hf z hz.1.1)
    (fun z hz h0 => by
      rcases hz.1.2 with h | h
      · exact h h0
      · exact hz.2 (Finset.mem_coe.2 ((hS z).2 ⟨h, h0⟩)))
    (fun s hs => (hf s (hKG (hSK s hs))).meromorphicAt)
    (fun s hs => by
      rw [(hf s (hKG (hSK s hs))).meromorphicOrderAt_eq]
      intro h
      exact hord s (hKG (hSK s hs)) (by simpa using h))
    hγ (fun t ht h => hf0 t ht ((hS _).1 h).2) hc'
  rw [e]
  have hsupp : insideOf γ ∩ Function.support (fun z => analyticOrderNatAt f z) =
      ↑(S.filter (· ∈ insideOf γ)) ∩ Function.support (fun z => analyticOrderNatAt f z) := by
    ext z
    simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
    constructor
    · rintro ⟨hz, hne⟩
      refine ⟨Finset.mem_filter.2 ⟨(hS z).2 ⟨subset_closure hz, ?_⟩, hz⟩, hne⟩
      by_contra h0
      exact hne (by simp [analyticOrderNatAt,
        (hf z (hKG (subset_closure hz))).analyticOrderAt_eq_zero.2 h0])
    · rintro ⟨hz, hne⟩
      exact ⟨(Finset.mem_filter.1 hz).2, hne⟩
  unfold zeroCountInside
  rw [finsum_mem_eq_sum_of_inter_support_eq _ hsupp, Nat.cast_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs1 := hKG (hSK s (Finset.mem_filter.1 hs).1)
  rw [(hf s hs1).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt (hord s hs1)]
  simp

/-- Beck Theorem 9.3.3 (CX-145), **Rouché's theorem**, for a positively oriented simple closed path:
if `f` and `g` are analytic on a region `G`, `|g| < |f|` on `γ`, and `γ` is `G`-contractible, then
`f + g` and `f` have the same number of zeros inside `γ`, counted with multiplicity. -/
@[kb "beck2025" "Theorem 9.3.3, p. 159"]
theorem rouche {f g : ℂ → ℂ} {G : Set ℂ} (hG : IsOpen G) (hGc : IsPreconnected G)
    (hf : ∀ z ∈ G, AnalyticAt ℂ f z) (hg : ∀ z ∈ G, AnalyticAt ℂ g z) {γ : ℝ → ℂ}
    (hγ : IsPositivelyOrientedSimpleClosed γ)
    (hlt : ∀ t ∈ Icc (0 : ℝ) 1, ‖g (γ t)‖ < ‖f (γ t)‖) {c : ℂ}
    (hc : IsGHomotopic G γ (fun _ => c)) :
    zeroCountInside (fun z => f z + g z) γ = zeroCountInside f γ := by
  have himgG : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ G := hc.mem_left
  have hf0 : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) ≠ 0 := fun t ht h => by
    have := hlt t ht; rw [h, norm_zero] at this; exact absurd this (not_lt.2 (norm_nonneg _))
  have hfg : ∀ z ∈ G, AnalyticAt ℂ (fun z => f z + g z) z := fun z hz => (hf z hz).add (hg z hz)
  have hfg0 : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) + g (γ t) ≠ 0 := fun t ht h => by
    have := hlt t ht
    rw [add_eq_zero_iff_eq_neg.1 h, norm_neg] at this; exact lt_irrefl _ this
  have hint : ∀ F : ℂ → ℂ, (∀ z ∈ G, AnalyticAt ℂ F z) → (∀ t ∈ Icc (0 : ℝ) 1, F (γ t) ≠ 0) →
      IntervalIntegrable (fun t => (deriv F (γ t) / F (γ t)) * deriv γ t) volume 0 1 := by
    intro F hF hF0
    refine hγ.smooth.intervalIntegrable_integrand zero_le_one (f := fun z => deriv F z / F z) ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ((hF _ (himgG t ht)).deriv.continuousAt.div (hF _ (himgG t ht)).continuousAt
      (hF0 t ht)).continuousWithinAt
  have hslit : ∀ t ∈ Icc (0 : ℝ) 1, (f (γ t) + g (γ t)) / f (γ t) ∈ slitPlane := by
    intro t ht
    have hfz := hf0 t ht
    rw [mem_slitPlane_iff]; left
    have h1 : (f (γ t) + g (γ t)) / f (γ t) = 1 + g (γ t) / f (γ t) := by field_simp
    have h2 : ‖g (γ t) / f (γ t)‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 hfz)]; exact hlt t ht
    rw [h1, add_re, one_re]
    linarith [neg_abs_le (g (γ t) / f (γ t)).re, abs_re_le_norm (g (γ t) / f (γ t))]
  have key : pathIntegral (fun z => deriv (fun z => f z + g z) z / (f z + g z)) γ 0 1 =
      pathIntegral (fun z => deriv f z / f z) γ 0 1 := by
    have hsub := pathIntegral_sub (γ := γ) (a := 0) (b := 1)
      (f := fun z => deriv (fun z => f z + g z) z / (f z + g z))
      (g := fun z => deriv f z / f z) (hint _ hfg hfg0) (hint _ hf hf0)
    rw [← sub_eq_zero, ← hsub]
    refine pathIntegral_eq_zero_of_closed_of_isPiecewiseSmooth
      (U := {z | z ∈ G ∧ f z ≠ 0 ∧ (f z + g z) / f z ∈ slitPlane})
      (F := fun z => log ((f z + g z) / f z)) hγ.smooth zero_le_one
      (fun t ht => ⟨himgG t ht, hf0 t ht, hslit t ht⟩) ?_ ?_ hγ.closed
    · rintro z ⟨hzG, hfz, hsl⟩
      have hfgz : f z + g z ≠ 0 := fun h => slitPlane_ne_zero hsl (by rw [h, zero_div])
      have hh : HasDerivAt (fun z => (f z + g z) / f z)
          ((deriv (fun z => f z + g z) z * f z - (f z + g z) * deriv f z) / f z ^ 2) z :=
        (hfg z hzG).differentiableAt.hasDerivAt.div (hf z hzG).differentiableAt.hasDerivAt hfz
      refine (hh.clog hsl).congr_deriv ?_
      field_simp
    · rintro z ⟨hzG, hfz, hsl⟩
      have hfgz : f z + g z ≠ 0 := fun h => slitPlane_ne_zero hsl (by rw [h, zero_div])
      exact (((hfg z hzG).deriv.continuousAt.div (hfg z hzG).continuousAt hfgz).sub
        ((hf z hzG).deriv.continuousAt.div (hf z hzG).continuousAt hfz)).continuousWithinAt
  have e1 := argument_principle_zeroCountInside hG hGc hfg hγ hfg0 hc
  have e2 := argument_principle_zeroCountInside hG hGc hf hγ hf0 hc
  rw [key, e2] at e1
  exact_mod_cast e1.symm

end UndergradKB.ComplexAnalysis
