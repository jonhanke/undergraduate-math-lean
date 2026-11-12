import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import UndergradKB.Common.Attr

/-!
# Groups with no small subgroups

Morris, *Topology Without Tears*, Definition A5.0.27: a topological group is an NSS-group if some
neighbourhood of the identity contains no non-trivial subgroup.
-/

open Set Topology

namespace UndergradKB.Topology

/-- Morris, Topology Without Tears, Definition A5.0.27 (TP-499).  A topological group has no
small subgroups (is an NSS-group) if some open set containing `1` contains no non-trivial
subgroup. -/
@[kb "morris2024" "Definition A5.0.27, p. 510"]
def IsNSS (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ H : Subgroup G, (H : Set G) ⊆ O → H = ⊥

/-- Additive version of `IsNSS`. -/
@[kb "morris2024" "Definition A5.0.27, p. 510"]
def IsAddNSS (G : Type*) [AddGroup G] [TopologicalSpace G] : Prop :=
  ∃ O : Set G, IsOpen O ∧ (0 : G) ∈ O ∧ ∀ H : AddSubgroup G, (H : Set G) ⊆ O → H = ⊥

/-- Morris, Topology Without Tears, Definition A5.0.27 (TP-499).  Every discrete group is an
NSS-group (take `O = {1}`). -/
@[kb "morris2024" "Definition A5.0.27, p. 510"]
theorem isNSS_of_discreteTopology (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    IsNSS G := by
  refine ⟨{1}, isOpen_discrete _, rfl, fun H hH => ?_⟩
  rw [eq_bot_iff]
  intro x hx
  exact hH hx

/-- Morris, Topology Without Tears, Definition A5.0.27 (TP-499).  The additive group `ℝ` is an
NSS-group. -/
@[kb "morris2024" "Definition A5.0.27, p. 510"]
theorem isAddNSS_real : IsAddNSS ℝ := by
  refine ⟨Ioo (-1) 1, isOpen_Ioo, by norm_num, fun H hH => ?_⟩
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hpos : 0 < |x| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / |x|)
  have hmem : n • x ∈ H := H.nsmul_mem hx n
  have h1 := hH hmem
  rw [nsmul_eq_mul] at h1
  have h2 : 1 ≤ n * |x| := by
    have := (div_le_iff₀ hpos).mp hn
    linarith
  have h3 : |(n : ℝ) * x| < 1 := abs_lt.mpr ⟨h1.1, h1.2⟩
  rw [abs_mul, Nat.abs_cast] at h3
  linarith

/-- Morris, Topology Without Tears, Definition A5.0.27 (TP-499).  The circle group is an
NSS-group: the open right half-plane contains no non-trivial subgroup. -/
@[kb "morris2024" "Definition A5.0.27, p. 510"]
theorem isNSS_circle : IsNSS Circle := by
  refine ⟨{z | 0 < (z : ℂ).re}, isOpen_lt continuous_const
    (Complex.continuous_re.comp (continuous_subtype_val (p := fun z : ℂ => z ∈ Submonoid.unitSphere ℂ))),
    by simp, fun H hH => ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  by_contra hne
  have hz1 : ‖(z : ℂ)‖ = 1 := by simp
  have hexp : (z : ℂ) = Complex.exp (Complex.arg z * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
    rw [hz1] at this
    simpa using this.symm
  have hθ : Complex.arg z ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    rw [hexp, h0]
    simp
  set θ := Complex.arg (z : ℂ) with hθdef
  have ha : 0 < |θ| := abs_pos.mpr hθ
  have hapi : |θ| ≤ Real.pi := abs_le.mpr ⟨(Complex.arg_mem_Ioc _).1.le, (Complex.arg_mem_Ioc _).2⟩
  have hex : ∃ n : ℕ, Real.pi / 2 ≤ n * |θ| := by
    obtain ⟨n, hn⟩ := exists_nat_ge (Real.pi / 2 / |θ|)
    exact ⟨n, (div_le_iff₀ ha).mp hn⟩
  classical
  let n := Nat.find hex
  have hn : Real.pi / 2 ≤ n * |θ| := Nat.find_spec hex
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hn
      simp at hn
      linarith [Real.pi_pos]
    · exact h
  have hup : n * |θ| ≤ Real.pi + Real.pi / 2 := by
    by_cases h1 : n = 1
    · rw [h1]; simp; linarith [Real.pi_pos]
    · have hmin : ¬ (Real.pi / 2 ≤ ((n - 1 : ℕ) : ℝ) * |θ|) :=
        Nat.find_min hex (by omega)
      have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub hnpos]; simp
      rw [hcast] at hmin
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      have h4 : |θ| ≤ (n - 1) * |θ| := by nlinarith
      nlinarith [Real.pi_pos]
  have hcos : Real.cos (n * |θ|) ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hn hup
  have hpow : ((z ^ n : Circle) : ℂ) = Complex.exp (((n * θ : ℝ) : ℂ) * Complex.I) := by
    rw [Circle.coe_pow, hexp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hre : ((z ^ n : Circle) : ℂ).re = Real.cos (n * |θ|) := by
    rw [hpow, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs (n * θ), abs_mul, Nat.abs_cast]
  have := hH (H.pow_mem hz n)
  simp only [Set.mem_ofPred_eq] at this
  rw [hre] at this
  linarith

/-- Morris, Topology Without Tears, Definition A5.0.27 (TP-499).  An infinite product of nontrivial
groups with the product topology is not an NSS-group; in particular `(ℤ/2)^ℕ` (with `ℤ/2`
discrete) is not NSS. -/
@[kb "morris2024" "Definition A5.0.27, p. 510"]
theorem not_isAddNSS_pi {ι : Type*} [Infinite ι] (A : ι → Type*) [∀ i, AddGroup (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, Nontrivial (A i)] : ¬ IsAddNSS (∀ i, A i) := by
  classical
  rintro ⟨O, hO, h0, hsub⟩
  obtain ⟨I, u, hu, hIO⟩ := isOpen_pi_iff.mp hO 0 h0
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
  let H : AddSubgroup (∀ i, A i) :=
    { carrier := {x | ∀ i ∈ I, x i = 0}
      zero_mem' := fun i _ => rfl
      add_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
      neg_mem' := fun {x} hx i hi => by simp [hx i hi] }
  have hHO : (H : Set (∀ i, A i)) ⊆ O := by
    intro x hx
    apply hIO
    intro i hi
    show x i ∈ u i
    rw [hx i hi]
    exact (hu i hi).2
  have := hsub H hHO
  obtain ⟨a, ha⟩ := exists_ne (0 : A j)
  have hmem : (Pi.single j a : ∀ i, A i) ∈ H := by
    intro i hi
    have : i ≠ j := fun h => hj (h ▸ hi)
    simp [this]
  rw [this] at hmem
  have h2 : (Pi.single j a : ∀ i, A i) = 0 := hmem
  have := congrFun h2 j
  simp at this
  exact ha this

end UndergradKB.Topology
