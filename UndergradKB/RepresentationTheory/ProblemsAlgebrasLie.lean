import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.CharP.Basic
import Mathlib.Analysis.Complex.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.WeylAlgebra
import UndergradKB.RepresentationTheory.QWeylAlgebra

/-! # Problems on the Weyl algebras, a two-dimensional Lie algebra and `p`-groups (Etingof et al.)

* `weyl_no_finite_rep` (Problem 1.26(a), first question): over a field of characteristic zero, a
  finite-dimensional representation of the Weyl algebra is zero (trace argument).  The question about
  two-sided ideals is not formalized.
* `weyl_pow_central` (Problem 1.26(b), partial): in characteristic `p`, `x^p` and `y^p` are central
  (they commute with both generators, hence with everything).  The determination of the full centre and the
  classification of irreducibles in part (c) are not formalized.
* `qweyl_finite_rep` and `qweyl_exists_finite_rep` (Problem 1.27(b)): the `q`-Weyl algebra has a nonzero
  finite-dimensional representation exactly when `q` is a root of unity.  Note that the repository's
  `QWeylAlgebra` uses the relation `y x = q x y` (the book writes `x y = q y x`), which replaces `q` by
  `q⁻¹` and does not affect the root-of-unity condition.
* `aff1_irrep_dim_one` and `aff1_irrep_of_finrank_one` (Problem 1.57, characteristic zero): for the
  two-dimensional Lie algebra `[X, Y] = Y`, treated as in the sl(2) files by a pair of operators, every
  finite-dimensional irreducible representation over an algebraically closed field of characteristic zero
  is one-dimensional with `Y = 0` (`X` is then an arbitrary scalar).  The positive-characteristic part is
  not formalized.
* `irreducible_pgroup_trivial` (Problem 3.4): for a group of order `p^n` and a field of characteristic
  `p`, every irreducible representation (Mathlib's `Representation.IsIrreducible`) is one-dimensional with
  trivial action.
-/

namespace UndergradKB.RepresentationTheory

/-! ### Problem 1.26 -/

section Weyl

/-- **Etingof et al., Problem 1.26(a)**: in characteristic zero the Weyl algebra has no nonzero
finite-dimensional representation. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem weyl_no_finite_rep {k : Type*} [Field k] [CharZero k] {V : Type*} [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ : WeylAlgebra k →ₐ[k] Module.End k V) : Subsingleton V := by
  have h := congrArg ρ (weylY_mul_weylX (k := k))
  rw [map_add, map_mul, map_mul, map_one] at h
  have h2 := congrArg (LinearMap.trace k V) h
  have c := LinearMap.trace_mul_comm k (ρ (weylY k)) (ρ (weylX k))
  rw [map_add, LinearMap.trace_one] at h2
  have h3 : ((Module.finrank k V : ℕ) : k) = 0 := by
    rw [c] at h2
    have := h2
    linear_combination -this
  have h4 : Module.finrank k V = 0 := by exact_mod_cast h3
  exact Module.finrank_zero_iff.mp h4

/-- Commutation rule `x yⁿ = yⁿ x - n yⁿ⁻¹` in any ring with `y x = x y + 1`. -/
theorem x_mul_y_pow {A : Type*} [Ring A] (x y : A) (h : y * x = x * y + 1) (n : ℕ) :
    x * y ^ n = y ^ n * x - n • y ^ (n - 1) := by
  have h' : (-x) * y = y * (-x) + 1 := by
    rw [neg_mul, mul_neg, h]; abel
  have := y_mul_x_pow y (-x) h' n
  rw [neg_mul, mul_neg] at this
  rw [← neg_inj, this]
  abel

/-- **Etingof et al., Problem 1.26(b) (partial)**: in characteristic `p`, `x^p` and `y^p` are central
in the Weyl algebra. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem weyl_pow_central {k : Type*} [Field k] {p : ℕ} [CharP k p] [Fact p.Prime] :
    Commute (weylX k ^ p) (weylY k) ∧ Commute (weylY k ^ p) (weylX k) := by
  have hp : ∀ z : WeylAlgebra k, p • z = 0 := by
    intro z
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have h := weylY_mul_weylX (k := k)
  constructor
  · have := y_mul_x_pow (weylX k) (weylY k) h p
    rw [hp, add_zero] at this
    exact this.symm
  · have := x_mul_y_pow (weylX k) (weylY k) h p
    rw [hp, sub_zero] at this
    exact this.symm

end Weyl

/-! ### Problem 1.27 -/

section QWeyl

/-- **Etingof et al., Problem 1.27(b)**: if the `q`-Weyl algebra over `ℂ` has a nonzero
finite-dimensional representation, then `q` is a root of unity (determinant argument). -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_finite_rep {q : ℂˣ} {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [Nontrivial V] (ρ : QWeylAlgebra ℂ q →ₐ[ℂ] Module.End ℂ V) : IsOfFinOrder q := by
  have h := congrArg ρ (qWeylY_mul_qWeylX (k := ℂ) (q := q))
  rw [map_mul, map_smul, map_mul] at h
  have h1 := congrArg LinearMap.det h
  rw [map_mul, LinearMap.det_smul, map_mul] at h1
  have hx : LinearMap.det (ρ (qWeylX ℂ q)) ≠ 0 := by
    have := congrArg (fun f => LinearMap.det (ρ f)) (qWeylX_mul_qWeylXinv (k := ℂ) (q := q))
    simp only [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hy : LinearMap.det (ρ (qWeylY ℂ q)) ≠ 0 := by
    have := congrArg (fun f => LinearMap.det (ρ f)) (qWeylY_mul_qWeylYinv (k := ℂ) (q := q))
    simp only [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have e : (((q : ℂ)) ^ Module.finrank ℂ V - 1) *
      (LinearMap.det (ρ (qWeylY ℂ q)) * LinearMap.det (ρ (qWeylX ℂ q))) = 0 := by
    rw [mul_comm (LinearMap.det (ρ (qWeylX ℂ q)))] at h1
    linear_combination (-1 : ℂ) * h1
  rcases mul_eq_zero.1 e with h2 | h2
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hpos, Units.ext ?_⟩
    simpa [sub_eq_zero] using h2
  · exact absurd h2 (mul_ne_zero hy hx)

/-- The diagonal operator `f ↦ (u i * f i)` on `ZMod n → ℂ`. -/
def qwClock {n : ℕ} (u : ZMod n → ℂˣ) : Module.End ℂ (ZMod n → ℂ) where
  toFun f := fun i => (u i : ℂ) * f i
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp [mul_left_comm]

/-- The cyclic shift `f ↦ (i ↦ f (i + s))` on `ZMod n → ℂ`. -/
def qwShift {n : ℕ} (s : ZMod n) : Module.End ℂ (ZMod n → ℂ) where
  toFun f := fun i => f (i + s)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

/-- **Etingof et al., Problem 1.27(b), converse**: if `q` is a root of unity, the `q`-Weyl algebra has a
representation on a nonzero finite-dimensional space `ℂⁿ` (`n` the order of `q`), given by the clock and
shift matrices. -/
@[kb "etingof2011" "Problem 1.27, p. 13"]
theorem qweyl_exists_finite_rep {q : ℂˣ} (hq : IsOfFinOrder q) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (QWeylAlgebra ℂ q →ₐ[ℂ] Module.End ℂ (ZMod n → ℂ)) := by
  have : NeZero (orderOf q) := ⟨hq.orderOf_pos.ne'⟩
  refine ⟨orderOf q, hq.orderOf_pos, ?_⟩
  have hshift : ∀ i : ZMod (orderOf q), q ^ (i + 1).val = q * q ^ i.val := by
    intro i
    rw [ZMod.val_add, pow_mod_orderOf, pow_add, ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one,
      mul_comm]
  have hshift' : ∀ i : ZMod (orderOf q), (q : ℂ) ^ (i + 1).val = q * (q : ℂ) ^ i.val := by
    intro i
    have := congrArg Units.val (hshift i)
    simpa using this
  have r : IsQWeylRel q (qwClock fun i : ZMod (orderOf q) => q ^ i.val)
      (qwClock fun i : ZMod (orderOf q) => (q ^ i.val)⁻¹) (qwShift 1) (qwShift (-1)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine LinearMap.ext fun f => funext fun i => ?_; simp [qwClock]
    · refine LinearMap.ext fun f => funext fun i => ?_; simp [qwClock]
    · refine LinearMap.ext fun f => funext fun i => ?_; simp [qwShift]
    · refine LinearMap.ext fun f => funext fun i => ?_; simp [qwShift]
    · refine LinearMap.ext fun f => funext fun i => ?_
      simp [qwClock, qwShift, hshift', mul_assoc]
  exact ⟨qWeylLift r⟩

end QWeyl

/-! ### Problem 1.57 -/

section Aff1

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **Etingof et al., Problem 1.57 (characteristic zero)**: let `X, Y` be operators on a nonzero
finite-dimensional space over an algebraically closed field of characteristic zero with `[X, Y] = Y`, such
that the only subspaces invariant under both are `0` and the whole space (an irreducible representation of
the two-dimensional nonabelian Lie algebra).  Then the space is one-dimensional and `Y = 0`. -/
@[kb "etingof2011" "Problem 1.57, p. 22"]
theorem aff1_irrep_dim_one [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] [Nontrivial V]
    (X Y : Module.End k V) (h : X * Y - Y * X = Y)
    (hirr : ∀ W : Submodule k V, W.map X ≤ W → W.map Y ≤ W → W = ⊥ ∨ W = ⊤) :
    Module.finrank k V = 1 ∧ Y = 0 := by
  classical
  have hXY : ∀ z, X (Y z) = Y (X z) + Y z := by
    intro z
    have := LinearMap.congr_fun h z
    simp only [LinearMap.sub_apply, mul_apply_eq_comp] at this
    rw [add_comm]
    exact eq_add_of_sub_eq this
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue X
  obtain ⟨w, hw⟩ := ha.exists_hasEigenvector
  have hXw : X w = a • w := hw.apply_eq_smul
  have hj : ∀ j : ℕ, X ((Y ^ j) w) = (a + j) • (Y ^ j) w := by
    intro j
    induction j with
    | zero => simpa using hXw
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, hXY, ih, map_smul]
      push_cast
      module
  have hex : ∃ j, (Y ^ j) w = 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun j : ℕ => a + (j : k)) := fun i j hij => by
      simpa using hij
    have hmem : ∀ j : ℕ, (fun j : ℕ => a + (j : k)) j ∈ {μ | X.HasEigenvalue μ} := fun j =>
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 (hj j), hcon j⟩
    exact Set.infinite_of_injective_forall_mem hinj hmem X.finite_hasEigenvalue
  have hj0 : (Y ^ Nat.find hex) w = 0 := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hj0
    exact hw.2 (by simpa using hj0)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hu : (Y ^ m) w ≠ 0 := Nat.find_min hex (by omega)
  have hYu : Y ((Y ^ m) w) = 0 := by
    rw [hm, pow_succ', mul_apply_eq_comp] at hj0
    exact hj0
  set u := (Y ^ m) w with hu_def
  have hXu : X u = (a + m) • u := hj m
  have hsp : ∀ v ∈ Submodule.span k {u}, ∃ c : k, v = c • u := fun v hv =>
    (Submodule.mem_span_singleton.1 hv).imp fun c hc => hc.symm
  have hXW : (Submodule.span k {u}).map X ≤ Submodule.span k {u} := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.singleton_subset_iff]
    show X u ∈ Submodule.span k {u}
    rw [hXu]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hYW : (Submodule.span k {u}).map Y ≤ Submodule.span k {u} := by
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.singleton_subset_iff]
    show Y u ∈ Submodule.span k {u}
    rw [hYu]
    exact Submodule.zero_mem _
  rcases hirr _ hXW hYW with h0 | h0
  · exact absurd (Submodule.span_singleton_eq_bot.1 h0) hu
  · refine ⟨?_, ?_⟩
    · have := finrank_span_singleton (K := k) hu
      rwa [h0, finrank_top] at this
    · ext v
      have hv : v ∈ Submodule.span k {u} := by rw [h0]; trivial
      obtain ⟨c, rfl⟩ := hsp v hv
      simp [hYu]

/-- Converse direction of Problem 1.57: on a one-dimensional space the only subspaces are `0` and the
whole space, so every one-dimensional representation (with `X` any scalar and `Y = 0`) is irreducible. -/
@[kb "etingof2011" "Problem 1.57, p. 22"]
theorem aff1_irrep_of_finrank_one (hdim : Module.finrank k V = 1) (W : Submodule k V) :
    W = ⊥ ∨ W = ⊤ := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hdim
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    have hpos : 0 < Module.finrank k W := by
      have : Module.finrank k W ≠ 0 := fun h0 => hW (Submodule.finrank_eq_zero.1 h0)
      omega
    have := Submodule.finrank_le W
    exact Submodule.eq_top_of_finrank_eq (by omega)

end Aff1

/-! ### Problem 3.4 -/

section PGroup

open MulAction

/-- A `p`-group acting additively on a `p`-torsion abelian group fixes a nonzero vector if it moves a
nonzero vector at all: the finite subgroup generated by an orbit has `p`-power order. -/
theorem pgroup_fixed_vector {p : ℕ} [hp : Fact p.Prime] {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V] (hG : IsPGroup p G) (f : G → V →+ V)
    (hmul : ∀ g h x, f (g * h) x = f g (f h x)) (hone : ∀ x, f 1 x = x) (v : V) (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ g, f g w = w := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let S : Set V := Set.range fun g : G => f g v
  have hS : S.Finite := Set.finite_range _
  obtain ⟨M, hMdef⟩ : ∃ M : Submodule (ZMod p) V, M = Submodule.span (ZMod p) S := ⟨_, rfl⟩
  have : Module.Finite (ZMod p) {x : V // x ∈ M} := by
    rw [hMdef]
    exact Module.Finite.span_of_finite (ZMod p) hS
  have : Finite {x : V // x ∈ M} := Module.finite_of_finite (ZMod p)
  have hM : ∀ g : G, ∀ m ∈ M, f g m ∈ M := by
    intro g m hm
    let F : V →ₗ[ZMod p] V := AddMonoidHom.toZModLinearMap p (f g)
    have hF : M.map F ≤ M := by
      rw [hMdef, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [F, AddMonoidHom.toZModLinearMap, hmul]⟩
    exact hF ⟨m, hm, rfl⟩
  let : MulAction G {x : V // x ∈ M} :=
    { smul := fun g m => ⟨f g m, hM g m m.2⟩
      one_smul := fun m => Subtype.ext (hone m)
      mul_smul := fun g h m => Subtype.ext (hmul g h m) }
  have hv' : v ∈ M := hMdef ▸ Submodule.subset_span ⟨1, hone v⟩
  have : Nontrivial {x : V // x ∈ M} :=
    ⟨⟨⟨v, hv'⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hmod := hG.card_modEq_card_fixedPoints {x : V // x ∈ M}
  have hdvd : p ∣ Nat.card {x : V // x ∈ M} := by
    have := Fintype.ofFinite {x : V // x ∈ M}
    have hpos : 0 < Module.finrank (ZMod p) {x : V // x ∈ M} := Module.finrank_pos
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    exact dvd_pow_self p hpos.ne'
  have hdvd2 : p ∣ Nat.card (MulAction.fixedPoints G {x : V // x ∈ M}) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  have h0fix : (0 : {x : V // x ∈ M}) ∈ MulAction.fixedPoints G {x : V // x ∈ M} := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (map_zero (f g))
  have hpos2 : 0 < Nat.card (MulAction.fixedPoints G {x : V // x ∈ M}) :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, h0fix⟩⟩, inferInstance⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints G {x : V // x ∈ M}) :=
    lt_of_lt_of_le hp.out.one_lt (Nat.le_of_dvd hpos2 hdvd2)
  have : Nontrivial (MulAction.fixedPoints G {x : V // x ∈ M}) :=
    Finite.one_lt_card_iff_nontrivial.1 hgt
  obtain ⟨y, hy⟩ := exists_ne (⟨0, h0fix⟩ : MulAction.fixedPoints G {x : V // x ∈ M})
  refine ⟨((y : {x : V // x ∈ M}) : V), ?_, ?_⟩
  · intro h0
    exact hy (Subtype.ext (Subtype.ext h0))
  · intro g
    exact congrArg Subtype.val (y.2 g)

/-- **Etingof et al., Problem 3.4**: if `G` has order `p^n` and `k` has characteristic `p`, then every
irreducible representation of `G` over `k` is one-dimensional with trivial action. -/
@[kb "etingof2011" "Problem 3.4, p. 34"]
theorem irreducible_pgroup_trivial {p n : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k] [CharP k p]
    {G : Type*} [Group G] (hG : Nat.card G = p ^ n) {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V = 1 ∧ ∀ g, ρ g = 1 := by
  have hpG : IsPGroup p G := IsPGroup.of_card hG
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero n hp.out.ne_zero)
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.ext
      ext v
      exact ⟨fun _ => trivial, fun _ => by
        change v ∈ (⊥ : Submodule k V)
        simp [hcon v]⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let : Module (ZMod p) V := AddCommGroup.zmodModule (n := p) (fun x => by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul])
  have key : ∃ w : V, w ≠ 0 ∧ ∀ g, ρ g w = w :=
    pgroup_fixed_vector hpG
      (fun g => (ρ g).toAddMonoidHom) (fun g h x => by simp) (fun x => by simp) v hv
  obtain ⟨w, hw0, hw⟩ := key
  let S' : Subrepresentation ρ :=
    ⟨Submodule.span k {w}, fun g u hu => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
      rw [map_smul, hw g]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S' with h | h
  · exfalso
    have : S'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hw0 (Submodule.span_singleton_eq_bot.1 this)
  · have htop : Submodule.span k {w} = ⊤ := congrArg Subrepresentation.toSubmodule h
    refine ⟨?_, fun g => ?_⟩
    · have := finrank_span_singleton (K := k) hw0
      rwa [htop, finrank_top] at this
    · ext x
      have hx : x ∈ Submodule.span k {w} := by rw [htop]; trivial
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      simp [hw g]

end PGroup

end UndergradKB.RepresentationTheory
