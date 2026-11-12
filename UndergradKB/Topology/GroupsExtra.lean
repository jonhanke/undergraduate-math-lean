import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr

/-!
# Extra results on topological groups (Morris, Appendix 5)

Countable abelian groups as quotients of `ℕ →₀ ℤ`, the Pontryagin dual of a binary product, extension
of local homomorphisms from a ball in a real normed space, and closed non-discrete subgroups of
`ℝⁿ` contain a line.
-/

namespace UndergradKB.Topology

open Set

/-! ### Restricted products of copies of `ℤ` (TP-592) -/

/-- Morris, Topology Without Tears, Corollary A5.11.9 (TP-592). Every countable abelian group is the
image of a surjective homomorphism from the restricted direct product `ℕ →₀ ℤ` of countably many
copies of `ℤ`. -/
@[kb "morris2024" "Corollary A5.11.9, p. 578"]
theorem exists_surjective_finsupp_int_addMonoidHom (G : Type*) [AddCommGroup G] [Countable G] :
    ∃ φ : (ℕ →₀ ℤ) →+ G, Function.Surjective φ := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  refine ⟨Finsupp.liftAddHom (fun n => zmultiplesHom G (e n)), fun g => ?_⟩
  obtain ⟨n, rfl⟩ := he g
  exact ⟨Finsupp.single n 1, by simp⟩

/-- Morris, Topology Without Tears, Corollary A5.11.9 (TP-592). Every countable abelian group is
isomorphic to a quotient group of `ℕ →₀ ℤ` (a countable restricted direct product of copies of `ℤ`). -/
@[kb "morris2024" "Corollary A5.11.9, p. 578"]
theorem exists_addEquiv_quotient_finsupp_int (G : Type*) [AddCommGroup G] [Countable G] :
    ∃ K : AddSubgroup (ℕ →₀ ℤ), Nonempty (((ℕ →₀ ℤ) ⧸ K) ≃+ G) := by
  obtain ⟨φ, hφ⟩ := exists_surjective_finsupp_int_addMonoidHom G
  exact ⟨φ.ker, ⟨QuotientAddGroup.quotientKerEquivOfSurjective φ hφ⟩⟩

/-! ### Dual of a product (TP-573) -/

open ContinuousMonoidHom

/-- Morris, Topology Without Tears, Theorem A5.9.1 (TP-573), case of two factors. The Pontryagin dual
of `A × B` is topologically isomorphic to the product of the duals (written multiplicatively as in
Mathlib; holds for any topological monoids, in particular for LCA groups). -/
@[kb "morris2024" "Theorem A5.9.1, p. 566"]
noncomputable def pontryaginDualProdEquiv (A B : Type*) [CommGroup A] [CommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] :
    PontryaginDual (A × B) ≃ₜ* (PontryaginDual A × PontryaginDual B) where
  toFun ψ := (PontryaginDual.map (ContinuousMonoidHom.inl A B) ψ,
    PontryaginDual.map (ContinuousMonoidHom.inr A B) ψ)
  invFun p := PontryaginDual.map (ContinuousMonoidHom.fst A B) p.1 *
    PontryaginDual.map (ContinuousMonoidHom.snd A B) p.2
  left_inv ψ := by
    refine PontryaginDual.ext fun x => ?_
    show ψ (x.1, 1) * ψ (1, x.2) = ψ x
    rw [← map_mul]
    simp
  right_inv p := by
    refine Prod.ext (PontryaginDual.ext fun x => ?_) (PontryaginDual.ext fun x => ?_)
    · show p.1 x * p.2 (1 : B) = p.1 x
      simp
    · show p.1 (1 : A) * p.2 x = p.2 x
      simp
  map_mul' ψ φ := by
    refine Prod.ext ?_ ?_ <;> rfl
  continuous_toFun :=
    ((PontryaginDual.map (ContinuousMonoidHom.inl A B)).continuous.prodMk
      (PontryaginDual.map (ContinuousMonoidHom.inr A B)).continuous)
  continuous_invFun :=
    (((PontryaginDual.map (ContinuousMonoidHom.fst A B)).continuous.comp continuous_fst).mul
      ((PontryaginDual.map (ContinuousMonoidHom.snd A B)).continuous.comp continuous_snd))

/-! ### Local homomorphisms on a ball (TP-553) -/

section LocalHom

open Metric

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup G]

/-- Hypothesis of a local homomorphism on the ball of radius `r` around `0`. -/
def IsLocalAddHom (r : ℝ) (f : E → G) : Prop :=
  ∀ x ∈ ball (0 : E) r, ∀ y ∈ ball (0 : E) r, x + y ∈ ball (0 : E) r → f (x + y) = f x + f y

variable {r : ℝ} {f : E → G}

theorem IsLocalAddHom.map_zero (hr : 0 < r) (h : IsLocalAddHom r f) : f 0 = 0 := by
  have h0 : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
  have := h 0 h0 0 h0 (by simpa using h0)
  simpa using this

theorem IsLocalAddHom.map_nsmul (hr : 0 < r) (h : IsLocalAddHom r f) (z : E) :
    ∀ j : ℕ, (j : ℝ) * ‖z‖ < r → f (j • z) = j • f z := by
  intro j
  induction j with
  | zero => intro _; simpa using h.map_zero hr
  | succ j ih =>
    intro hj
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    push_cast at hj
    have hj' : (j : ℝ) * ‖z‖ < r := by nlinarith
    have hz : z ∈ ball (0 : E) r := by
      rw [mem_ball_zero_iff]; nlinarith
    have hjz : j • z ∈ ball (0 : E) r := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt norm_nsmul_le hj'
    have hsum : j • z + z ∈ ball (0 : E) r := by
      rw [← succ_nsmul, mem_ball_zero_iff]
      exact lt_of_le_of_lt norm_nsmul_le (by push_cast; linarith)
    rw [succ_nsmul, h _ hjz _ hz hsum, ih hj', succ_nsmul]

theorem IsLocalAddHom.map_eq_nsmul_inv (hr : 0 < r) (h : IsLocalAddHom r f) {y : E}
    (hy : y ∈ ball (0 : E) r) {m : ℕ} (hm : 0 < m) :
    f y = m • f ((m : ℝ)⁻¹ • y) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hnorm : (m : ℝ) * ‖(m : ℝ)⁻¹ • y‖ = ‖y‖ := by
    rw [norm_smul, norm_inv, Real.norm_natCast, ← mul_assoc, mul_inv_cancel₀ hm'.ne', one_mul]
  have := h.map_nsmul hr ((m : ℝ)⁻¹ • y) m (by rw [hnorm]; exact mem_ball_zero_iff.1 hy)
  have e : m • ((m : ℝ)⁻¹ • y) = y := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hm'.ne', one_smul]
  rwa [e] at this

/-- A natural number `k` is admissible for `x` if `‖x‖ < k r`. -/
def admissible (r : ℝ) (k : ℕ) (x : E) : Prop := 0 < k ∧ ‖x‖ < k * r

theorem admissible.inv_mem {k : ℕ} {x : E} (hr : 0 < r) (hk : admissible r k x) :
    (k : ℝ)⁻¹ • x ∈ ball (0 : E) r := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk.1
  rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_natCast, inv_mul_lt_iff₀ hk']
  exact hk.2

theorem exists_admissible (hr : 0 < r) (s : ℝ) : ∃ k : ℕ, 0 < k ∧ s < k * r := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max s 0 / r)
  have h1 : max s 0 < k * r := by rwa [div_lt_iff₀ hr] at hk
  refine ⟨k, ?_, lt_of_le_of_lt (le_max_left _ _) h1⟩
  have : (0 : ℝ) < k * r := lt_of_le_of_lt (le_max_right _ _) h1
  have : (0 : ℝ) < k := by
    by_contra hc
    push_neg at hc
    nlinarith
  exact_mod_cast this

theorem IsLocalAddHom.nsmul_scale (hr : 0 < r) (h : IsLocalAddHom r f) {k : ℕ} {x : E}
    (hk : admissible r k x) {m : ℕ} (hm : 0 < m) :
    k • f ((k : ℝ)⁻¹ • x) = (k * m) • f (((k * m : ℕ) : ℝ)⁻¹ • x) := by
  have := h.map_eq_nsmul_inv hr (hk.inv_mem hr) hm
  rw [this, ← mul_smul]
  congr 2
  rw [smul_smul, Nat.cast_mul, mul_inv, mul_comm]

theorem IsLocalAddHom.scale_unique (hr : 0 < r) (h : IsLocalAddHom r f) {k k' : ℕ} {x : E}
    (hk : admissible r k x) (hk' : admissible r k' x) :
    k • f ((k : ℝ)⁻¹ • x) = k' • f ((k' : ℝ)⁻¹ • x) := by
  rw [h.nsmul_scale hr hk hk'.1, h.nsmul_scale hr hk' hk.1, mul_comm k k']

/-- Morris, Topology Without Tears, Lemma A5.5.24 (TP-553), for a ball neighbourhood. A local
homomorphism `f` (additive whenever the arguments and their sum lie in the ball `B(0,r)` of a real
normed space `E`), continuous on the ball, extends to a continuous homomorphism `E →+ G`, `G` an
abelian topological group. -/
@[kb "morris2024" "Lemma A5.5.24, p. 548"]
theorem IsLocalAddHom.exists_extension [TopologicalSpace G] [IsTopologicalAddGroup G]
    (hr : 0 < r) (h : IsLocalAddHom r f) (hc : ContinuousOn f (ball (0 : E) r)) :
    ∃ F : E →+ G, Continuous F ∧ ∀ x ∈ ball (0 : E) r, F x = f x := by
  classical
  have hex : ∀ x : E, ∃ k : ℕ, admissible r k x := fun x => exists_admissible hr ‖x‖
  let F0 : E → G := fun x => (Classical.choose (hex x)) • f (((Classical.choose (hex x) : ℕ) : ℝ)⁻¹ • x)
  have hF0 : ∀ x (k : ℕ), admissible r k x → F0 x = k • f ((k : ℝ)⁻¹ • x) :=
    fun x k hk => h.scale_unique hr (Classical.choose_spec (hex x)) hk
  have hadd : ∀ x y, F0 (x + y) = F0 x + F0 y := by
    intro x y
    obtain ⟨k, hk0, hk⟩ := exists_admissible hr (‖x‖ + ‖y‖)
    have hkx : admissible r k x := ⟨hk0, lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) hk⟩
    have hky : admissible r k y := ⟨hk0, lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) hk⟩
    have hkxy : admissible r k (x + y) := ⟨hk0, lt_of_le_of_lt (norm_add_le _ _) hk⟩
    rw [hF0 _ _ hkxy, hF0 _ _ hkx, hF0 _ _ hky, smul_add, h _ (hkx.inv_mem hr) _ (hky.inv_mem hr)
      (by rw [← smul_add]; exact hkxy.inv_mem hr), nsmul_add]
  have hzero : F0 0 = 0 := by
    have := hadd 0 0
    simpa using this
  let F : E →+ G := AddMonoidHom.mk' F0 hadd
  have hagree : ∀ x ∈ ball (0 : E) r, F x = f x := by
    intro x hx
    have hk : admissible r 1 x := ⟨one_pos, by simpa using mem_ball_zero_iff.1 hx⟩
    show F0 x = f x
    rw [hF0 x 1 hk]; simp
  refine ⟨F, ?_, hagree⟩
  apply continuous_of_continuousAt_zero
  have h0 : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
  have hcf : ContinuousAt f 0 := hc.continuousAt (isOpen_ball.mem_nhds h0)
  refine hcf.congr ?_
  filter_upwards [isOpen_ball.mem_nhds h0] with x hx using (hagree x hx).symm

end LocalHom

/-! ### Closed non-discrete subgroups of `ℝⁿ` (TP-546) -/

section Line

open Filter Metric
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Morris, Topology Without Tears, Proposition A5.5.11 (TP-546), in a finite-dimensional (proper)
real normed space, with non-discreteness phrased as the existence of non-zero elements of the
subgroup of arbitrarily small norm. A closed subgroup with this property contains a line through
`0`. -/
theorem exists_line_of_closed_of_small_elements (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    (hnd : ∀ ε > 0, ∃ h ∈ H, h ≠ 0 ∧ ‖h‖ < ε) : ∃ a : E, a ≠ 0 ∧ ∀ t : ℝ, t • a ∈ H := by
  choose h hmem hne hlt using fun n : ℕ => hnd (1 / ((n : ℝ) + 1)) (by positivity)
  have hpos : ∀ n, 0 < ‖h n‖ := fun n => norm_pos_iff.2 (hne n)
  let m : ℕ → ℕ := fun n => ⌊1 / ‖h n‖⌋₊
  have hm_le : ∀ n, (m n : ℝ) * ‖h n‖ ≤ 1 := by
    intro n
    have := Nat.floor_le (show 0 ≤ 1 / ‖h n‖ by have := hpos n; positivity)
    rw [le_div_iff₀ (hpos n)] at this
    exact this
  have hm_gt : ∀ n, 1 < ((m n : ℝ) + 1) * ‖h n‖ := by
    intro n
    have := Nat.lt_floor_add_one (1 / ‖h n‖)
    rw [div_lt_iff₀ (hpos n)] at this
    exact this
  let p : ℕ → E := fun n => (m n : ℝ) • h n
  have hp_mem : ∀ n, p n ∈ H := by
    intro n
    have := H.nsmul_mem (hmem n) (m n)
    rwa [← Nat.cast_smul_eq_nsmul ℝ] at this
  have hp_norm : ∀ n, ‖p n‖ = (m n : ℝ) * ‖h n‖ := by
    intro n
    simp only [p, norm_smul, Real.norm_natCast]
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : E)) (r := 1))
    (x := p) (fun n => by simpa [hp_norm] using hm_le n)
  have hh : Tendsto (fun k => ‖h (φ k)‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => 1 / (((φ k : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hlt (φ k)).le) h1
  have ha : a ≠ 0 := by
    intro ha0
    have hn : Tendsto (fun k => ‖p (φ k)‖) atTop (𝓝 ‖a‖) := hlim.norm
    have hge : (1 / 2 : ℝ) ≤ ‖a‖ := by
      refine ge_of_tendsto hn (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
      have h1 : (1 : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hk.trans (hφ.id_le k)
      have h2 : 1 / ((φ k : ℝ) + 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have h3 := hlt (φ k)
      have h4 := hm_gt (φ k)
      rw [hp_norm]
      nlinarith
    rw [ha0, norm_zero] at hge
    norm_num at hge
  refine ⟨a, ha, fun t => ?_⟩
  let q : ℕ → E := fun n => ((⌊t * m n⌋ : ℤ) : ℝ) • h n
  have hq_mem : ∀ n, q n ∈ H := by
    intro n
    have := H.zsmul_mem (hmem n) ⌊t * m n⌋
    rwa [← Int.cast_smul_eq_zsmul ℝ] at this
  have hdiff : ∀ n, ‖q n - t • p n‖ ≤ ‖h n‖ := by
    intro n
    have e : q n - t • p n = (((⌊t * m n⌋ : ℤ) : ℝ) - t * m n) • h n := by
      simp only [q, p, sub_smul, smul_smul]
    rw [e, norm_smul]
    have h1 := Int.floor_le (t * m n)
    have h2 := Int.lt_floor_add_one (t * m n)
    have : ‖((⌊t * m n⌋ : ℤ) : ℝ) - t * m n‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ ≤ 1 * ‖h n‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖h n‖ := one_mul _
  have hd : Tendsto (fun k => q (φ k) - t • p (φ k)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => hdiff (φ k)) hh
  have htp : Tendsto (fun k => t • p (φ k)) atTop (𝓝 (t • a)) := hlim.const_smul t
  have hsum := hd.add htp
  simp only [sub_add_cancel, zero_add] at hsum
  exact hH.mem_of_tendsto hsum (Eventually.of_forall fun k => hq_mem (φ k))

/-- Morris, Topology Without Tears, Proposition A5.5.11 (TP-546). Every non-discrete closed subgroup
of a finite-dimensional real normed space (in particular of `ℝⁿ`) contains a line through `0`. -/
@[kb "morris2024" "Proposition A5.5.11, p. 543"]
theorem exists_line_of_closed_not_discrete (H : AddSubgroup E) (hH : IsClosed (H : Set E))
    (hnd : ¬ DiscreteTopology H) : ∃ a : E, a ≠ 0 ∧ ∀ t : ℝ, t • a ∈ H := by
  apply exists_line_of_closed_of_small_elements H hH
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hbig⟩ := hcon
  apply hnd
  apply discreteTopology_of_isOpen_singleton_zero
  have : ({0} : Set H) = Subtype.val ⁻¹' ball (0 : E) ε := by
    ext x
    simp only [mem_singleton_iff, mem_preimage, mem_ball_zero_iff]
    constructor
    · rintro rfl; simpa using hε
    · intro hx
      by_contra hne
      have : (x : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      exact absurd hx (not_lt.2 (hbig x x.2 this))
  rw [this]
  exact isOpen_ball.preimage continuous_subtype_val

/-- Morris, Topology Without Tears, Proposition A5.5.11 (TP-546), for `ℝⁿ` as Euclidean space. -/
@[kb "morris2024" "Proposition A5.5.11, p. 543"]
theorem exists_line_of_closed_not_discrete_euclidean (n : ℕ)
    (H : AddSubgroup (EuclideanSpace ℝ (Fin n))) (hH : IsClosed (H : Set (EuclideanSpace ℝ (Fin n))))
    (hnd : ¬ DiscreteTopology H) : ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧ ∀ t : ℝ, t • a ∈ H :=
  exists_line_of_closed_not_discrete H hH hnd

end Line

end UndergradKB.Topology
