import UndergradKB.RepresentationTheory.Sl2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Order.WellFounded
import Mathlib.Algebra.DirectSum.Module
import UndergradKB.Common.Attr

/-! # Complete reducibility of finite-dimensional sl(2)-modules (Etingof et al., Theorem 1.1 and
Problem 1.55)

Over an algebraically closed field `k` of characteristic zero, let `h e f` be operators on a
finite-dimensional space `V` with the relations of `sl₂` (`IsSl2Rel`).  An invariant subspace
(`IsInv`) is one stable under `h`, `e`, `f`.

* `IsSl2Rel.exists_pow_eq_zero`: `e` (and, by the symmetry `IsSl2Rel.symm`, `f`) is nilpotent; `e`
  shifts the generalized eigenspaces of `h` by `2`.
* `IsSl2Rel.e_pow_f_pow`: for `x` with `e x = 0`, `eᵐ fᵐ x = m! · h (h - 1) ⋯ (h - m + 1) x`
  (from the commutation `e fᵐ⁺¹ = fᵐ⁺¹ e + (m + 1) fᵐ (h - m)`).
* `IsSl2Rel.eq_cyc_of_isInv`: the cyclic module `span {fⁱ v}` of a primitive vector `v` has no
  invariant subspaces other than `⊥` and itself.
* `IsSl2Rel.exists_prim_not_mem`: if `M < P` are invariant and `M` is a sum of lowest-weight cyclic
  modules, then `P` contains a primitive vector outside `M` (the core of the argument; it replaces
  the Casimir generalized-eigenspace route of the book by an elementary polynomial-in-`h` argument).
* `IsSl2Rel.complete_reducibility_aux`: induction on the dimension of the invariant subspace.
* `IsSl2Rel.complete_reducibility`: every invariant subspace has an invariant complement.
* `IsSl2Rel.exists_internal_irreducible`: `V` is an internal direct sum of invariant subspaces that
  are irreducible representations.
-/

namespace UndergradKB.RepresentationTheory.Sl2

open Module

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {h e f : Module.End k V}

namespace IsSl2Rel

lemma pow_succ_apply (g : Module.End k V) (m : ℕ) (x : V) : (g ^ (m + 1)) x = g ((g ^ m) x) := by
  rw [pow_succ', mul_apply_eq_comp]

lemma pow_succ_apply' (g : Module.End k V) (m : ℕ) (x : V) : (g ^ (m + 1)) x = (g ^ m) (g x) := by
  rw [pow_succ, mul_apply_eq_comp]

/-- `h` acting on `fᵐ x`. -/
lemma h_f_pow (r : IsSl2Rel k h e f) (m : ℕ) (x : V) :
    h ((f ^ m) x) = (f ^ m) (h x) - ((2 * m : k)) • (f ^ m) x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ_apply, r.hf_apply, ih, map_sub, map_smul, pow_succ_apply]
    push_cast
    module

/-- The key commutation `e fᵐ⁺¹ x = fᵐ⁺¹ e x + (m + 1) fᵐ (h - m) x`. -/
lemma e_f_pow_succ (r : IsSl2Rel k h e f) (m : ℕ) (x : V) :
    e ((f ^ (m + 1)) x) = (f ^ (m + 1)) (e x) + ((m : k) + 1) • (f ^ m) (h x - (m : k) • x) := by
  induction m with
  | zero => simp [r.ef_apply]
  | succ m ih =>
    rw [pow_succ_apply f (m + 1), r.ef_apply, ih, map_add, map_smul, r.h_f_pow]
    simp only [pow_succ_apply f m, pow_succ_apply f (m + 1), map_sub, map_smul]
    push_cast
    module

section Nilp

variable [FiniteDimensional k V] [IsAlgClosed k] [CharZero k]

omit [FiniteDimensional k V] [IsAlgClosed k] [CharZero k] in
lemma maxGen_e (r : IsSl2Rel k h e f) {c : k} {x : V} (hx : x ∈ h.maxGenEigenspace c) :
    e x ∈ h.maxGenEigenspace (c + 2) := by
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  refine ⟨m, ?_⟩
  have step : ∀ z : V, (h - (c + 2) • (1 : Module.End k V)) (e z) =
      e ((h - c • (1 : Module.End k V)) z) := by
    intro z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, map_sub, map_smul]
    rw [r.he_apply]
    module
  have key : ∀ (m : ℕ) (y : V), ((h - (c + 2) • (1 : Module.End k V)) ^ m) (e y) =
      e (((h - c • (1 : Module.End k V)) ^ m) y) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ_apply, ih, step, ← pow_succ_apply]
  rw [key, hm, map_zero]

omit [FiniteDimensional k V] [IsAlgClosed k] in
lemma e_pow_mem (r : IsSl2Rel k h e f) {c : k} {x : V} (hx : x ∈ h.maxGenEigenspace c) (j : ℕ) :
    (e ^ j) x ∈ h.maxGenEigenspace (c + 2 * j) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have := r.maxGen_e ih
    rw [pow_succ_apply]
    convert this using 2
    push_cast
    ring

omit [IsAlgClosed k] in
lemma exists_pow_eq_zero_of_mem (r : IsSl2Rel k h e f) {c : k} {x : V}
    (hx : x ∈ h.maxGenEigenspace c) : ∃ m, (e ^ m) x = 0 := by
  by_contra hcon
  replace hcon : ∀ m, (e ^ m) x ≠ 0 := fun m hm => hcon ⟨m, hm⟩
  have hev : ∀ j : ℕ, h.HasEigenvalue (c + 2 * j) := by
    intro j
    have hm := r.e_pow_mem hx j
    rw [Module.End.mem_maxGenEigenspace] at hm
    have hw : (e ^ j) x ≠ 0 := hcon j
    set w := (e ^ j) x with hwdef
    set A : Module.End k V := h - (c + 2 * j) • (1 : Module.End k V) with hA
    have hex : ∃ m, (A ^ m) w = 0 := hm
    classical
    let m0 := Nat.find hex
    have hm0 : (A ^ m0) w = 0 := Nat.find_spec hex
    have hm0pos : m0 ≠ 0 := by
      intro h0
      rw [h0] at hm0
      simp at hm0
      exact hw hm0
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero hm0pos
    have hnot : (A ^ p) w ≠ 0 := Nat.find_min hex (by omega)
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hnot⟩
    rw [Module.End.mem_eigenspace_iff]
    have : A ((A ^ p) w) = 0 := by rw [← pow_succ_apply, ← Nat.succ_eq_add_one, ← hp]; exact hm0
    simp only [hA, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self] at this
    exact sub_eq_zero.mp this
  have hinj : Function.Injective (fun j : ℕ => c + 2 * (j : k)) := by
    intro a b hab
    simp only [add_right_inj] at hab
    have := mul_left_cancel₀ (two_ne_zero : (2 : k) ≠ 0) hab
    exact_mod_cast this
  exact Set.infinite_of_injective_forall_mem hinj hev (h.finite_hasEigenvalue)

lemma exists_pow_eq_zero (r : IsSl2Rel k h e f) : ∃ N : ℕ, e ^ N = 0 := by
  have hall : ∀ x : V, ∃ m, (e ^ m) x = 0 := by
    intro x
    have hx : x ∈ (⊤ : Submodule k V) := trivial
    rw [← Module.End.iSup_maxGenEigenspace_eq_top h] at hx
    refine Submodule.iSup_induction _ (motive := fun x => ∃ m, (e ^ m) x = 0) hx
      (fun c y hy => r.exists_pow_eq_zero_of_mem hy) ⟨0, by simp⟩ ?_
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    have h1 : (e ^ (m + n)) x = 0 := by
      rw [add_comm, pow_add, mul_apply_eq_comp, hm, map_zero]
    have h2 : (e ^ (m + n)) y = 0 := by
      rw [pow_add, mul_apply_eq_comp, hn, map_zero]
    rw [map_add, h1, h2, add_zero]
  let b := Module.finBasis k V
  choose m hm using fun i => hall (b i)
  refine ⟨Finset.univ.sup m, b.ext fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) (Finset.mem_univ i))
  rw [hd, add_comm, pow_add, mul_apply_eq_comp, hm i, map_zero]
  simp

end Nilp

end IsSl2Rel

open Polynomial

/-- The falling-factorial-type polynomial `X (X - 1) ⋯ (X - m + 1)`. -/
noncomputable def fallPoly (k : Type*) [Field k] (m : ℕ) : k[X] :=
  ∏ j ∈ Finset.range m, (X - C (j : k))

lemma fallPoly_succ (k : Type*) [Field k] (m : ℕ) :
    fallPoly k (m + 1) = fallPoly k m * (X - C (m : k)) := by
  simp only [fallPoly, Finset.prod_range_succ]

lemma aeval_mem_of_stable(g : Module.End k V) {W : Submodule k V} (hW : ∀ x ∈ W, g x ∈ W)
    (p : k[X]) {x : V} (hx : x ∈ W) : aeval g p x ∈ W := by
  have hpow : ∀ (n : ℕ) (y : V), y ∈ W → (g ^ n) y ∈ W := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; rw [IsSl2Rel.pow_succ_apply]; exact hW _ (ih y hy)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact W.add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial, mul_apply_eq_comp, Module.algebraMap_end_apply]
    exact W.smul_mem _ (hpow n x hx)

lemma aeval_X_sub_C_apply (g : Module.End k V) (c : k) (x : V) :
    aeval g (X - C c) x = g x - c • x := by
  simp [Module.algebraMap_end_apply]

lemma aeval_mul_apply (g : Module.End k V) (p q : k[X]) (x : V) :
    aeval g (p * q) x = aeval g p (aeval g q x) := by
  rw [map_mul, mul_apply_eq_comp]

namespace IsSl2Rel

lemma e_h_apply (r : IsSl2Rel k h e f) (x : V) (hx : e x = 0) : e (h x) = 0 := by
  have := r.he_apply x
  rw [hx, map_zero, smul_zero, add_zero] at this
  exact this.symm

/-- For `x` killed by `e`, `eᵐ fᵐ x = m! (h)(h - 1)⋯(h - m + 1) x`. -/
lemma e_pow_f_pow (r : IsSl2Rel k h e f) (m : ℕ) :
    ∀ x : V, e x = 0 → (e ^ m) ((f ^ m) x) = (m.factorial : k) • aeval h (fallPoly k m) x := by
  induction m with
  | zero => intro x _; simp [fallPoly]
  | succ m ih =>
    intro x hx
    have hx' : e (h x - (m : k) • x) = 0 := by rw [map_sub, map_smul, hx, r.e_h_apply x hx]; simp
    rw [pow_succ_apply', r.e_f_pow_succ, hx, map_zero, zero_add, map_smul, ih _ hx',
      smul_smul, fallPoly_succ, aeval_mul_apply,
      aeval_X_sub_C_apply, Nat.factorial_succ]
    push_cast
    ring_nf

end IsSl2Rel

/-- A subspace stable under all three operators `h`, `e`, `f` (a subrepresentation). -/
def IsInv (h e f : Module.End k V) (W : Submodule k V) : Prop :=
  (∀ x ∈ W, h x ∈ W) ∧ (∀ x ∈ W, e x ∈ W) ∧ (∀ x ∈ W, f x ∈ W)

namespace IsInv

variable {W U : Submodule k V}

lemma bot : IsInv h e f (⊥ : Submodule k V) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro x hx
    rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _

lemma top : IsInv h e f (⊤ : Submodule k V) := ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

lemma inf (hW : IsInv h e f W) (hU : IsInv h e f U) : IsInv h e f (W ⊓ U) :=
  ⟨fun x hx => ⟨hW.1 x hx.1, hU.1 x hx.2⟩, fun x hx => ⟨hW.2.1 x hx.1, hU.2.1 x hx.2⟩,
    fun x hx => ⟨hW.2.2 x hx.1, hU.2.2 x hx.2⟩⟩

lemma sup (hW : IsInv h e f W) (hU : IsInv h e f U) : IsInv h e f (W ⊔ U) := by
  have key : ∀ T : Module.End k V, (∀ x ∈ W, T x ∈ W) → (∀ x ∈ U, T x ∈ U) →
      ∀ x ∈ W ⊔ U, T x ∈ W ⊔ U := by
    intro T h1 h2 x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (h1 y hy) (h2 z hz)
  exact ⟨key h hW.1 hU.1, key e hW.2.1 hU.2.1, key f hW.2.2 hU.2.2⟩

lemma symm (hW : IsInv h e f W) : IsInv (-h) f e W :=
  ⟨fun x hx => by rw [LinearMap.neg_apply]; exact W.neg_mem (hW.1 x hx), hW.2.2, hW.2.1⟩

lemma pow_e (hW : IsInv h e f W) (j : ℕ) : ∀ x ∈ W, (e ^ j) x ∈ W := by
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih => intro x hx; rw [IsSl2Rel.pow_succ_apply]; exact hW.2.1 _ (ih x hx)

lemma pow_f (hW : IsInv h e f W) (j : ℕ) : ∀ x ∈ W, (f ^ j) x ∈ W := by
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih => intro x hx; rw [IsSl2Rel.pow_succ_apply]; exact hW.2.2 _ (ih x hx)

end IsInv

/-- The subspace spanned by the vectors `fⁱ v`. -/
def cyc (f : Module.End k V) (v : V) : Submodule k V :=
  Submodule.span k (Set.range fun i : ℕ => (f ^ i) v)

lemma pow_mem_cyc (f : Module.End k V) (v : V) (i : ℕ) : (f ^ i) v ∈ cyc f v :=
  Submodule.subset_span ⟨i, rfl⟩

namespace IsSl2Rel

lemma isInv_cyc (r : IsSl2Rel k h e f) {v : V} {μ : k} (hv : IsPrimitive h e v μ) :
    IsInv h e f (cyc f v) := by
  have key : ∀ T : Module.End k V, (∀ i : ℕ, T ((f ^ i) v) ∈ cyc f v) →
      ∀ x ∈ cyc f v, T x ∈ cyc f v := by
    intro T hT x hx
    have : cyc f v ≤ (cyc f v).comap T :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hT i)
    exact this hx
  refine ⟨key h fun i => ?_, key e fun i => ?_, key f fun i => ?_⟩
  · rw [r.h_pow_f hv]; exact Submodule.smul_mem _ _ (pow_mem_cyc f v i)
  · cases i with
    | zero => simp [hv.e_apply]
    | succ j => rw [r.e_pow_f_succ hv]; exact Submodule.smul_mem _ _ (pow_mem_cyc f v j)
  · rw [← pow_succ_apply]; exact pow_mem_cyc f v _

section Cyc

variable [FiniteDimensional k V] [CharZero k]

omit [FiniteDimensional k V] [CharZero k] in
lemma e_pow_f_pow_prim (r : IsSl2Rel k h e f) {v : V} {μ : k} (hv : IsPrimitive h e v μ) (i : ℕ) :
    (e ^ i) ((f ^ i) v) = ((i.factorial : k) * (fallPoly k i).eval μ) • v := by
  rw [r.e_pow_f_pow i v hv.e_apply, Module.End.aeval_apply_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hv.h_apply, hv.ne_zero⟩, smul_smul]

omit [FiniteDimensional k V] [CharZero k] in
lemma e_pow_f_pow_lt (r : IsSl2Rel k h e f) {v : V} {μ : k} (hv : IsPrimitive h e v μ) {i d : ℕ}
    (hi : i < d) : (e ^ d) ((f ^ i) v) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have : i + t + 1 = (t + 1) + i := by omega
  rw [this, pow_add, mul_apply_eq_comp, r.e_pow_f_pow_prim hv, map_smul, pow_succ_apply',
    hv.e_apply, map_zero, smul_zero]

omit [FiniteDimensional k V] [CharZero k] in
lemma pow_apply_mem {W : Submodule k V} (g : Module.End k V) (hW : ∀ x ∈ W, g x ∈ W) (j : ℕ) :
    ∀ x ∈ W, (g ^ j) x ∈ W := by
  induction j with
  | zero => intro x hx; simpa using hx
  | succ j ih => intro x hx; rw [pow_succ_apply]; exact hW _ (ih x hx)

omit [FiniteDimensional k V] in
lemma claim_aux (r : IsSl2Rel k h e f) {v : V} {μ : k} (hv : IsPrimitive h e v μ) {n : ℕ}
    (hn : μ = n) {U : Submodule k V} (hU : ∀ x ∈ U, e x ∈ U) :
    ∀ d : ℕ, d ≤ n + 1 → ∀ w ∈ Submodule.span k ((fun i : ℕ => (f ^ i) v) '' Set.Iio d),
      w ∈ U → w ≠ 0 → v ∈ U := by
  intro d
  induction d with
  | zero =>
    intro _ w hw _ hne
    have : Set.Iio (0 : ℕ) = ∅ := by ext; simp
    rw [this, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hw
    exact absurd hw hne
  | succ d ih =>
    intro hd w hw hwU hne
    have hI : Set.Iio (d + 1) = insert d (Set.Iio d) := by
      ext x; simp only [Set.mem_Iio, Set.mem_insert_iff]; omega
    rw [hI, Set.image_insert_eq, Submodule.mem_span_insert] at hw
    obtain ⟨c, w', hw', rfl⟩ := hw
    have h1 : (e ^ d) w' = 0 := by
      refine Submodule.span_induction (p := fun x _ => (e ^ d) x = 0) ?_ ?_ ?_ ?_ hw'
      · rintro _ ⟨i, hi, rfl⟩
        exact r.e_pow_f_pow_lt hv hi
      · simp
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro a x _ hx; rw [map_smul, hx, smul_zero]
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, zero_add] at hwU hne
      exact ih (by omega) w' hw' hwU hne
    · have hκ : ((d.factorial : k) * (fallPoly k d).eval μ) ≠ 0 := by
        refine mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d) ?_
        rw [hn]
        simp only [fallPoly, eval_prod, eval_sub, eval_X, eval_C]
        refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
        have : n ≠ j := by simp at hj; omega
        exact_mod_cast this
      have h2 : (e ^ d) (c • (f ^ d) v + w') = (c * ((d.factorial : k) * (fallPoly k d).eval μ)) • v := by
        rw [map_add, map_smul, r.e_pow_f_pow_prim hv, h1, add_zero, smul_smul]
      have hmem := pow_apply_mem e hU d _ hwU
      rw [h2] at hmem
      have := Submodule.smul_mem U (c * ((d.factorial : k) * (fallPoly k d).eval μ))⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hκ), one_smul] at this

lemma v_mem_of_le_cyc (r : IsSl2Rel k h e f) {v : V} {μ : k} (hv : IsPrimitive h e v μ)
    {U : Submodule k V} (hU : ∀ x ∈ U, e x ∈ U) (hle : U ≤ cyc f v) (hne : U ≠ ⊥) : v ∈ U := by
  obtain ⟨n, hn⟩ := r.exists_nat_weight hv
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine r.claim_aux hv hn hU (n + 1) le_rfl u ?_ huU hu0
  have this : u ∈ Submodule.span k (Set.range fun i : ℕ => (f ^ i) v) := hle huU
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨i, rfl⟩
  by_cases hi : i < n + 1
  · exact Submodule.subset_span ⟨i, hi, rfl⟩
  · show (f ^ i) v ∈ Submodule.span k _
    rw [r.f_pow_eq_zero_of_lt hv hn (by omega)]
    exact zero_mem _

/-- A nonzero invariant subspace of the cyclic module generated by a primitive vector is the whole
cyclic module: the cyclic module is irreducible. -/
lemma eq_cyc_of_isInv (r : IsSl2Rel k h e f) {v : V} {μ : k} (hv : IsPrimitive h e v μ)
    {U : Submodule k V} (hU : IsInv h e f U) (hle : U ≤ cyc f v) (hne : U ≠ ⊥) : U = cyc f v := by
  refine le_antisymm hle (Submodule.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  exact hU.pow_f i v (r.v_mem_of_le_cyc hv hU.2.1 hle hne)

end Cyc

end IsSl2Rel

section Quot

variable {W : Type*} [AddCommGroup W] [Module k W] {h e f : Module.End k W}

/-- The relations of `sl₂` restrict to an invariant subspace. -/
lemma IsSl2Rel.restrict (r : IsSl2Rel k h e f) {P : Submodule k W} (hP : IsInv h e f P) :
    IsSl2Rel k (h.restrict hP.1) (e.restrict hP.2.1) (f.restrict hP.2.2) where
  ef := LinearMap.ext fun x => Subtype.ext (by
    have := congrArg (fun T => T (x : W)) r.ef
    simpa using this)
  he := LinearMap.ext fun x => Subtype.ext (by
    have := congrArg (fun T => T (x : W)) r.he
    simpa using this)
  hf := LinearMap.ext fun x => Subtype.ext (by
    have := congrArg (fun T => T (x : W)) r.hf
    simpa using this)

/-- The relations of `sl₂` pass to the quotient by an invariant subspace. -/
lemma IsSl2Rel.quotient (r : IsSl2Rel k h e f) {N : Submodule k W} (hN : IsInv h e f N) :
    IsSl2Rel k (N.mapQ N h (fun x hx => hN.1 x hx)) (N.mapQ N e (fun x hx => hN.2.1 x hx))
      (N.mapQ N f (fun x hx => hN.2.2 x hx)) where
  ef := LinearMap.ext fun q => by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      have := congrArg (fun T => Submodule.Quotient.mk (p := N) (T x)) r.ef
      simpa using this
  he := LinearMap.ext fun q => by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      have := congrArg (fun T => Submodule.Quotient.mk (p := N) (T x)) r.he
      simpa using this
  hf := LinearMap.ext fun q => by
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      have := congrArg (fun T => Submodule.Quotient.mk (p := N) (T x)) r.hf
      simpa using this

end Quot

namespace IsSl2Rel

/-- Given invariant subspaces `M < P`, there is a vector of `P` outside `M` which is, modulo `M`,
killed by `e` and an `h`-eigenvector of natural weight (a lift of a primitive vector of `P / M`). -/
lemma exists_lift [FiniteDimensional k V] [CharZero k] [IsAlgClosed k] (r : IsSl2Rel k h e f)
    {P M : Submodule k V} (hP : IsInv h e f P) (hM : IsInv h e f M) (hMP : M < P) :
    ∃ x ∈ P, x ∉ M ∧ ∃ n : ℕ, e x ∈ M ∧ h x - (n : k) • x ∈ M := by
  set M' : Submodule k P := M.comap P.subtype with hM'
  have hM'inv : IsInv (h.restrict hP.1) (e.restrict hP.2.1) (f.restrict hP.2.2) M' :=
    ⟨fun x hx => hM.1 x hx, fun x hx => hM.2.1 x hx, fun x hx => hM.2.2 x hx⟩
  have rQ := (r.restrict hP).quotient hM'inv
  have hne : M' ≠ ⊤ := by
    intro htop
    refine hMP.not_ge (fun x hx => ?_)
    have : (⟨x, hx⟩ : P) ∈ M' := htop ▸ Submodule.mem_top
    exact this
  have : Nontrivial (P ⧸ M') := Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨q, μ, hq⟩ := rQ.exists_primitive
  obtain ⟨n, rfl⟩ := rQ.exists_nat_weight hq
  obtain ⟨⟨x, hxP⟩, rfl⟩ := Submodule.Quotient.mk_surjective M' q
  refine ⟨x, hxP, ?_, n, ?_, ?_⟩
  · intro hxM
    apply hq.ne_zero
    rw [Submodule.Quotient.mk_eq_zero]
    exact hxM
  · have := hq.e_apply
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · have := hq.h_apply
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at this
    exact this

/-- From a lift `x₁` of a would-be primitive vector with `e x₁ = 0`, adjust by a polynomial in `h`
(using that `f` is nilpotent, so `h` is semisimple on `ker e` with weights in a finite set) to an
honest primitive vector of weight `n` still outside `M`. -/
lemma exists_primitive_of_ker [FiniteDimensional k V] [CharZero k] [IsAlgClosed k]
    (r : IsSl2Rel k h e f) {P M : Submodule k V} (hP : IsInv h e f P) (hM : IsInv h e f M)
    {x₁ : V} (hxP : x₁ ∈ P) (hxM : x₁ ∉ M) (hex : e x₁ = 0) {n : ℕ}
    (hh : h x₁ - (n : k) • x₁ ∈ M) : ∃ x' ∈ P, x' ∉ M ∧ IsPrimitive h e x' (n : k) := by
  classical
  obtain ⟨N', hN'⟩ := r.symm.exists_pow_eq_zero
  set F := fallPoly k N' with hF
  have hFx : aeval h F x₁ = 0 := by
    have := r.e_pow_f_pow N' x₁ hex
    rw [hN', LinearMap.zero_apply, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)
  set Φ : k[X] := ∏ j ∈ (Finset.range N').erase n, (X - C (j : k)) with hΦ
  have hΦ0 : Φ.eval (n : k) ≠ 0 := by
    simp only [hΦ, eval_prod, eval_sub, eval_X, eval_C]
    refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
    have : n ≠ j := fun h' => (Finset.ne_of_mem_erase hj) h'.symm
    exact_mod_cast this
  have hkey : aeval h ((X - C (n : k)) * Φ) x₁ = 0 := by
    by_cases hn : n ∈ Finset.range N'
    · have : (X - C (n : k)) * Φ = F :=
        Finset.mul_prod_erase (Finset.range N') (fun j => (X - C (j : k))) hn
      rw [this, hFx]
    · have hE : (Finset.range N').erase n = Finset.range N' := Finset.erase_eq_of_notMem hn
      have hΦF : Φ = F := by simp only [hΦ, hF, fallPoly, hE]
      rw [hΦF, aeval_mul_apply, hFx, map_zero]
  set q : k[X] := C (Φ.eval (n : k))⁻¹ * Φ with hq
  set x' : V := aeval h q x₁ with hx'
  have hx'eq : x' = (Φ.eval (n : k))⁻¹ • aeval h Φ x₁ := by
    simp [hx', hq, Module.algebraMap_end_apply]
  have hw : h (aeval h Φ x₁) = (n : k) • aeval h Φ x₁ := by
    rw [aeval_mul_apply, aeval_X_sub_C_apply] at hkey
    exact sub_eq_zero.mp hkey
  have hhx' : h x' = (n : k) • x' := by
    rw [hx'eq, map_smul, hw, smul_comm]
  have hK : e x' = 0 :=
    LinearMap.mem_ker.mp (aeval_mem_of_stable h (W := LinearMap.ker e)
      (fun x hx => r.e_h_apply x hx) q (LinearMap.mem_ker.mpr hex))
  have hq1 : q.eval (n : k) = 1 := by
    simp only [hq, eval_mul, eval_C]
    exact inv_mul_cancel₀ hΦ0
  obtain ⟨s, hs⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := (n : k)) (p := q)
  rw [hq1, mul_comm] at hs
  have hdiff : aeval h (q - C 1) x₁ = x' - x₁ := by
    simp [hx']
  have hxx' : x' - x₁ ∈ M := by
    rw [← hdiff, hs, aeval_mul_apply, aeval_X_sub_C_apply]
    exact aeval_mem_of_stable h hM.1 s hh
  have hx'M : x' ∉ M := fun hmem => hxM (by simpa using M.sub_mem hmem hxx')
  have hx'P : x' ∈ P := aeval_mem_of_stable h hP.1 q hxP
  exact ⟨x', hx'P, hx'M, ⟨fun h0 => hx'M (h0 ▸ M.zero_mem), hhx', hK⟩⟩

end IsSl2Rel

/-- `P` is spanned by the vectors `fⁱ v`, where `v` ranges over primitive vectors lying in `P`. -/
def SpannedByPrim (h e f : Module.End k V) (P : Submodule k V) : Prop :=
  P ≤ Submodule.span k {y | ∃ (v : V) (μ : k) (i : ℕ), v ∈ P ∧ IsPrimitive h e v μ ∧
    y = (f ^ i) v}

namespace IsSl2Rel

/-- If a subspace `M` is spanned by lowest-weight cyclic modules, then a vector `e x ∈ M` for which
`x` has weight `n` modulo `M` already lies in `e M`: lowest-weight vectors have non-positive weight,
so the weight `n + 2` of `e x` cannot occur among them. -/
lemma e_mem_map_e [FiniteDimensional k V] [CharZero k] [IsAlgClosed k] (r : IsSl2Rel k h e f)
    {M : Submodule k V} (hM : IsInv h e f M) (hSC : SpannedByPrim (-h) f e M) {x : V} {n : ℕ}
    (hex : e x ∈ M) (hh : h x - (n : k) • x ∈ M) : e x ∈ M.map e := by
  classical
  obtain ⟨N, hN⟩ := r.exists_pow_eq_zero
  set G : k[X] := (fallPoly k N).comp (-X) with hG
  have hGeq : aeval h G = aeval (-h) (fallPoly k N) := by
    rw [hG, aeval_comp]
    simp
  have hGl : ∀ (l : V) (μ : k), IsPrimitive (-h) f l μ → aeval h G l = 0 := by
    intro l μ hl
    have := r.symm.e_pow_f_pow N l hl.e_apply
    rw [hN, LinearMap.zero_apply, map_zero] at this
    rw [hGeq]
    exact (smul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero _)
  have hsub : M ≤ M.map e ⊔ LinearMap.ker (aeval h G) := by
    refine hSC.trans (Submodule.span_le.mpr ?_)
    rintro y ⟨l, μ, i, hlM, hl, rfl⟩
    cases i with
    | zero => exact Submodule.mem_sup_right (LinearMap.mem_ker.mpr (by simpa using hGl l μ hl))
    | succ j => exact Submodule.mem_sup_left ⟨(e ^ j) l, hM.pow_e j l hlM, (pow_succ_apply e j l).symm⟩
  obtain ⟨u, hu, l, hl, hul⟩ := Submodule.mem_sup.mp (hsub hex)
  set c : k := (n : k) + 2 with hc
  have hstab : ∀ y ∈ M.map e, h y ∈ M.map e := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨h y + (2 : k) • y, M.add_mem (hM.1 y hy) (M.smul_mem _ hy), by
      rw [map_add, map_smul, r.he_apply]⟩
  have hrel : h (e x) - c • e x ∈ M.map e :=
    ⟨h x - (n : k) • x, hh, by rw [map_sub, map_smul, r.he_apply, hc]; module⟩
  obtain ⟨A, hA⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := G)
  rw [mul_comm, sub_eq_iff_eq_add] at hA
  have hGc : G.eval c ≠ 0 := by
    simp only [hG, eval_comp, eval_neg, eval_X, fallPoly, eval_prod, eval_sub, eval_C]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    intro h0
    have : ((n + 2 + j : ℕ) : k) = 0 := by
      push_cast
      rw [hc] at h0
      linear_combination -h0
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  have h1 : aeval h G (e x) = aeval h A (h (e x) - c • e x) + (G.eval c) • e x := by
    conv_lhs => rw [hA]
    rw [map_add, LinearMap.add_apply, aeval_mul_apply, aeval_X_sub_C_apply, aeval_C,
      Module.algebraMap_end_apply]
  have h2 : aeval h G (e x) = aeval h G u := by
    rw [← hul, map_add, LinearMap.mem_ker.mp hl, add_zero]
  have h3 : (G.eval c) • e x ∈ M.map e := by
    have : (G.eval c) • e x = aeval h G u - aeval h A (h (e x) - c • e x) := by
      rw [← h2, h1]; abel
    rw [this]
    exact (M.map e).sub_mem (aeval_mem_of_stable h hstab G hu)
      (aeval_mem_of_stable h hstab A hrel)
  have := (M.map e).smul_mem (G.eval c)⁻¹ h3
  rwa [smul_smul, inv_mul_cancel₀ hGc, one_smul] at this

/-- The key extension step: if `M < P` are invariant, `M` is spanned by lowest-weight cyclic modules
(i.e. `SpannedByPrim (-h) f e M`), then `P` contains a primitive vector outside `M`. -/
lemma exists_prim_not_mem [FiniteDimensional k V] [CharZero k] [IsAlgClosed k]
    (r : IsSl2Rel k h e f) {P M : Submodule k V} (hP : IsInv h e f P) (hM : IsInv h e f M)
    (hMP : M < P) (hSC : SpannedByPrim (-h) f e M) :
    ∃ x' ∈ P, x' ∉ M ∧ ∃ n : ℕ, IsPrimitive h e x' (n : k) := by
  obtain ⟨x, hxP, hxM, n, hex, hh⟩ := r.exists_lift hP hM hMP
  obtain ⟨y, hyM, hy⟩ := r.e_mem_map_e hM hSC hex hh
  have hx₁ : e (x - y) = 0 := by rw [map_sub, hy, sub_self]
  have hxP1 : x - y ∈ P := P.sub_mem hxP (hMP.le hyM)
  have hxM1 : x - y ∉ M := fun hm => hxM (by simpa using M.add_mem hm hyM)
  have hh1 : h (x - y) - (n : k) • (x - y) ∈ M := by
    have : h (x - y) - (n : k) • (x - y) = (h x - (n : k) • x) - (h y - (n : k) • y) := by
      rw [map_sub, smul_sub]; abel
    rw [this]
    exact M.sub_mem hh (M.sub_mem (hM.1 y hyM) (M.smul_mem _ hyM))
  obtain ⟨x', hx'P, hx'M, hx'⟩ := r.exists_primitive_of_ker hP hM hxP1 hxM1 hx₁ hh1
  exact ⟨x', hx'P, hx'M, n, hx'⟩

/-- The cyclic module of a primitive vector `x' ∈ P \ M` is a complement of `M` in `P` when `M` is a
maximal proper invariant subspace of `P`. -/
lemma cyc_complement [FiniteDimensional k V] [CharZero k] (r : IsSl2Rel k h e f)
    {P M : Submodule k V} (hP : IsInv h e f P) (hM : IsInv h e f M) (hMP : M ≤ P)
    (hco : ∀ U, IsInv h e f U → M ≤ U → U ≤ P → U = M ∨ U = P) {x : V} {μ : k}
    (hxP : x ∈ P) (hxM : x ∉ M) (hx : IsPrimitive h e x μ) :
    IsInv h e f (cyc f x) ∧ cyc f x ≤ P ∧ cyc f x ⊓ M = ⊥ ∧ cyc f x ⊔ M = P := by
  have hL := r.isInv_cyc hx
  have hLP : cyc f x ≤ P := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hP.pow_f i x hxP)
  have hxL : x ∈ cyc f x := by simpa using pow_mem_cyc f x 0
  refine ⟨hL, hLP, ?_, ?_⟩
  · by_contra hne
    have := r.eq_cyc_of_isInv hx (hL.inf hM) inf_le_left hne
    exact hxM (by
      have hx2 : x ∈ cyc f x ⊓ M := by rw [this]; exact hxL
      exact hx2.2)
  · rcases hco _ (hL.sup hM) le_sup_right (sup_le hLP hMP) with h1 | h1
    · exact absurd (h1 ▸ (le_sup_left : cyc f x ≤ cyc f x ⊔ M) hxL) hxM
    · exact h1

end IsSl2Rel

/-- Every invariant subspace of `P` has an invariant complement inside `P`. -/
def HasComplements (h e f : Module.End k V) (P : Submodule k V) : Prop :=
  ∀ W : Submodule k V, IsInv h e f W → W ≤ P →
    ∃ W' : Submodule k V, IsInv h e f W' ∧ W' ≤ P ∧ W ⊓ W' = ⊥ ∧ W ⊔ W' = P

lemma exists_coatom [FiniteDimensional k V] {P W : Submodule k V} (hW : IsInv h e f W)
    (hWP : W < P) :
    ∃ M : Submodule k V, IsInv h e f M ∧ W ≤ M ∧ M < P ∧
      ∀ U, IsInv h e f U → M ≤ U → U ≤ P → U = M ∨ U = P := by
  obtain ⟨M, ⟨hMinv, hWM, hMP⟩, hmax⟩ := (wellFounded_gt (α := Submodule k V)).has_min
    {U | IsInv h e f U ∧ W ≤ U ∧ U < P} ⟨W, hW, le_rfl, hWP⟩
  refine ⟨M, hMinv, hWM, hMP, fun U hU hMU hUP => ?_⟩
  by_cases hUP' : U = P
  · exact Or.inr hUP'
  · left
    by_contra hne
    exact hmax U ⟨hU, hWM.trans hMU, lt_of_le_of_ne hUP hUP'⟩ (lt_of_le_of_ne hMU (Ne.symm hne))

namespace IsSl2Rel

/-- Inductive core of complete reducibility: every invariant subspace `P` has complements for all its
invariant subspaces, and is spanned by cyclic modules of primitive vectors. -/
theorem complete_reducibility_aux [FiniteDimensional k V] [CharZero k] [IsAlgClosed k] :
    ∀ (d : ℕ) (h e f : Module.End k V), IsSl2Rel k h e f → ∀ P : Submodule k V,
      IsInv h e f P → Module.finrank k P = d → HasComplements h e f P ∧ SpannedByPrim h e f P := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro h e f r P hP hd
  by_cases hbot : P = ⊥
  · subst hbot
    refine ⟨fun W _ hW => ⟨⊥, IsInv.bot, le_rfl, ?_, ?_⟩, bot_le⟩
    · rw [le_bot_iff.mp hW]; simp
    · rw [le_bot_iff.mp hW]; simp
  have step : ∀ M : Submodule k V, IsInv h e f M → M < P →
      (∀ U, IsInv h e f U → M ≤ U → U ≤ P → U = M ∨ U = P) →
      HasComplements h e f M ∧ SpannedByPrim h e f M ∧
        ∃ L : Submodule k V, IsInv h e f L ∧ L ≤ P ∧ L ⊓ M = ⊥ ∧ L ⊔ M = P ∧
          ∃ x ∈ P, ∃ μ : k, IsPrimitive h e x μ ∧ L = cyc f x := by
    intro M hM hMP hco
    have hlt : Module.finrank k M < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hMP
    obtain ⟨hc, hs⟩ := ih _ hlt h e f r M hM rfl
    obtain ⟨-, hs'⟩ := ih _ hlt (-h) f e r.symm M hM.symm rfl
    obtain ⟨x, hxP, hxM, n, hx⟩ := r.exists_prim_not_mem hP hM hMP hs'
    obtain ⟨hL, hLP, hLM, hLs⟩ := r.cyc_complement hP hM hMP.le hco hxP hxM hx
    exact ⟨hc, hs, cyc f x, hL, hLP, hLM, hLs, x, hxP, n, hx, rfl⟩
  refine ⟨fun W hW hWP => ?_, ?_⟩
  · rcases hWP.eq_or_lt with rfl | hlt
    · exact ⟨⊥, IsInv.bot, bot_le, inf_bot_eq _, sup_bot_eq _⟩
    · obtain ⟨M, hM, hWM, hMP, hco⟩ := exists_coatom hW hlt
      obtain ⟨hc, -, L, hL, hLP, hLM, hLsup, -⟩ := step M hM hMP hco
      obtain ⟨W'', hW'', hW''M, hinf, hsup⟩ := hc W hW hWM
      refine ⟨W'' ⊔ L, hW''.sup hL, sup_le (hW''M.trans hMP.le) hLP, ?_, ?_⟩
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxW, hxs⟩ := Submodule.mem_inf.mp hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hxs
        have hbM : b ∈ M := by
          have := M.sub_mem (hWM hxW) (hW''M ha)
          simpa using this
        have hb0 : b = 0 := by
          have : b ∈ L ⊓ M := ⟨hb, hbM⟩
          rw [hLM] at this
          exact (Submodule.mem_bot k).mp this
        subst hb0
        rw [add_zero] at hxW ⊢
        have : a ∈ W ⊓ W'' := ⟨hxW, ha⟩
        rw [hinf] at this
        exact this
      · rw [← sup_assoc, hsup, sup_comm, hLsup]
  · obtain ⟨M, hM, -, hMP, hco⟩ := exists_coatom (IsInv.bot (h := h) (e := e) (f := f))
      (bot_lt_iff_ne_bot.mpr hbot)
    obtain ⟨-, hs, L, hL, hLP, hLM, hLsup, x, hxP, μ, hx, rfl⟩ := step M hM hMP hco
    refine le_trans (le_of_eq hLsup.symm)
      (sup_le (Submodule.span_le.mpr ?_) (hs.trans (Submodule.span_mono ?_)))
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨x, μ, i, hxP, hx, rfl⟩
    · rintro y ⟨v, μ', i, hv, hp, hy⟩
      exact ⟨v, μ', i, hMP.le hv, hp, hy⟩

end IsSl2Rel

/-- An irreducible invariant subspace: nonzero, invariant, with no invariant subspaces other than
`⊥` and itself. -/
def IsIrreducibleSub (h e f : Module.End k V) (S : Submodule k V) : Prop :=
  IsInv h e f S ∧ S ≠ ⊥ ∧ ∀ U : Submodule k V, IsInv h e f U → U ≤ S → U = ⊥ ∨ U = S

/-- An irreducible invariant subspace is an irreducible representation for the restricted
operators. -/
lemma IsIrreducibleSub.isIrreducibleRep {S : Submodule k V} (hS : IsIrreducibleSub h e f S) :
    IsIrreducibleRep (h.restrict hS.1.1) (e.restrict hS.1.2.1) (f.restrict hS.1.2.2) where
  nontrivial := Submodule.nontrivial_iff_ne_bot.mpr hS.2.1
  eq_bot_or_top W hh he hf := by
    have hU : IsInv h e f (W.map S.subtype) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro _ ⟨w, hw, rfl⟩; exact ⟨_, hh w hw, rfl⟩
      · rintro _ ⟨w, hw, rfl⟩; exact ⟨_, he w hw, rfl⟩
      · rintro _ ⟨w, hw, rfl⟩; exact ⟨_, hf w hw, rfl⟩
    rcases hS.2.2 _ hU (by rintro _ ⟨w, -, rfl⟩; exact w.2) with h0 | h1
    · left
      apply Submodule.map_injective_of_injective S.injective_subtype
      rw [h0, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective S.injective_subtype
      rw [h1, Submodule.map_subtype_top]

lemma exists_irreducibleSub [FiniteDimensional k V] {P : Submodule k V} (hP : IsInv h e f P)
    (hne : P ≠ ⊥) : ∃ S ≤ P, IsIrreducibleSub h e f S := by
  obtain ⟨S, ⟨hSinv, hSP, hSne⟩, hmin⟩ := (wellFounded_lt (α := Submodule k V)).has_min
    {U | IsInv h e f U ∧ U ≤ P ∧ U ≠ ⊥} ⟨P, hP, le_rfl, hne⟩
  refine ⟨S, hSP, hSinv, hSne, fun U hU hUS => ?_⟩
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  · right
    by_contra hUS'
    exact hmin U ⟨hU, hUS.trans hSP, hU0⟩ (lt_of_le_of_ne hUS hUS')

namespace IsSl2Rel

variable [FiniteDimensional k V] [CharZero k] [IsAlgClosed k]

/-- Complete reducibility, for subspaces: every invariant subspace `W` of an invariant subspace `P`
has an invariant complement inside `P`. -/
theorem hasComplements (r : IsSl2Rel k h e f) {P : Submodule k V} (hP : IsInv h e f P) :
    HasComplements h e f P :=
  (complete_reducibility_aux _ h e f r P hP rfl).1

/-- An invariant subspace is a direct sum of irreducible invariant subspaces. -/
theorem exists_family (r : IsSl2Rel k h e f) :
    ∀ (d : ℕ) (P : Submodule k V), IsInv h e f P → Module.finrank k P = d →
      ∃ (ι : Type) (_ : Fintype ι) (S : ι → Submodule k V),
        (∀ i, IsIrreducibleSub h e f (S i) ∧ S i ≤ P) ∧ iSupIndep S ∧ ⨆ i, S i = P := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hP hd
  by_cases hbot : P = ⊥
  · subst hbot
    refine ⟨Empty, inferInstance, fun i => i.elim, ?_⟩
    exact ⟨fun i => i.elim, fun i => i.elim, by simp⟩
  obtain ⟨S, hSP, hS⟩ := exists_irreducibleSub hP hbot
  obtain ⟨Q, hQ, hQP, hSQ, hSsup⟩ := r.hasComplements hP S hS.1 hSP
  have hQlt : Q < P := by
    refine lt_of_le_of_ne hQP fun hQ => hS.2.1 ?_
    rw [hQ, inf_eq_left.mpr hSP] at hSQ
    exact hSQ
  have hlt : Module.finrank k Q < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hQlt
  obtain ⟨ι', _, S', hfam, hind, hsup⟩ := ih _ hlt Q hQ rfl
  have hdisj : Disjoint S Q := disjoint_iff.mpr hSQ
  have hle : ∀ i, S' i ≤ Q := fun i => (hfam i).2
  refine ⟨Option ι', inferInstance, fun o => Option.elim o S S', ?_, ?_, ?_⟩
  · intro o
    cases o with
    | none => exact ⟨hS, hSP⟩
    | some i => exact ⟨(hfam i).1, (hle i).trans hQP⟩
  · intro o
    cases o with
    | none =>
      refine hdisj.mono_right (iSup₂_le fun j hj => ?_)
      cases j with
      | none => exact absurd rfl hj
      | some j' => exact hle j'
    | some i0 =>
      rw [Submodule.disjoint_def]
      intro x hx hx2
      have hsub : (⨆ (j : Option ι') (_ : j ≠ some i0), Option.elim j S S') ≤
          S ⊔ ⨆ (j' : ι') (_ : j' ≠ i0), S' j' := by
        refine iSup₂_le fun j hj => ?_
        cases j with
        | none => exact le_sup_left
        | some j' =>
          exact le_sup_of_le_right (le_iSup₂_of_le j' (fun h' => hj (by rw [h'])) le_rfl)
      obtain ⟨s, hs, rr, hr, hsr⟩ := Submodule.mem_sup.mp (hsub hx2)
      have hrQ : rr ∈ Q := by
        have : (⨆ (j' : ι') (_ : j' ≠ i0), S' j') ≤ Q := iSup₂_le fun j _ => hle j
        exact this hr
      have hxQ : x ∈ Q := hle i0 hx
      have hsQ : s ∈ Q := by
        have : s = x - rr := by rw [← hsr]; abel
        rw [this]; exact Q.sub_mem hxQ hrQ
      have hs0 : s = 0 := Submodule.disjoint_def.mp hdisj s hs hsQ
      rw [hs0, zero_add] at hsr
      subst hsr
      exact Submodule.disjoint_def.mp (hind i0) _ hx hr
  · rw [iSup_option]
    show S ⊔ ⨆ i, S' i = P
    rw [hsup, hSsup]

/-- Complete reducibility of finite-dimensional `sl₂`-modules (Problem 1.55(g)-(k)): over an
algebraically closed field of characteristic zero, every invariant subspace `W` of a
finite-dimensional space `V` carrying operators `h e f` with the relations of `sl₂` has an invariant
complement. -/
@[kb "etingof2011" "Problem 1.55(g)-(k), p. 21"]
theorem complete_reducibility (r : IsSl2Rel k h e f) {W : Submodule k V} (hW : IsInv h e f W) :
    ∃ W' : Submodule k V, IsInv h e f W' ∧ IsCompl W W' := by
  obtain ⟨W', hW', -, hinf, hsup⟩ := r.hasComplements IsInv.top W hW le_top
  exact ⟨W', hW', IsCompl.of_eq hinf hsup⟩

/-- Theorem 1.1, complete reducibility part: over an algebraically closed field of characteristic
zero, a finite-dimensional representation of the relations of `sl₂` is the internal direct sum of
finitely many invariant subspaces, each of which is an irreducible representation for the restricted
operators.  (Together with `irreducible_classification` these are all of the form `k^(n+1)`.) -/
@[kb "etingof2011" "Theorem 1.1, p. 5"]
theorem exists_internal_irreducible (r : IsSl2Rel k h e f) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : ι → Submodule k V)
      (hS : ∀ i, IsInv h e f (S i)),
      (∀ i, IsIrreducibleRep (h.restrict (hS i).1) (e.restrict (hS i).2.1)
        (f.restrict (hS i).2.2)) ∧ DirectSum.IsInternal S := by
  obtain ⟨ι, hι, S, hfam, hind, hsup⟩ := r.exists_family _ ⊤ IsInv.top rfl
  refine ⟨ι, hι, Classical.decEq ι, S, fun i => (hfam i).1.1, fun i => (hfam i).1.isIrreducibleRep, ?_⟩
  let _ := Classical.decEq ι
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top S).mpr ⟨hind, hsup⟩

end IsSl2Rel

end UndergradKB.RepresentationTheory.Sl2
