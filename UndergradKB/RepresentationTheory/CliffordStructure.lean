import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Algebra.Algebra.Subalgebra.Pi
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Ring.Fin
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.CliffordSemisimple

/-! # Structure of Clifford algebras (Etingof et al., Problem 2.25 (i))

For a nondegenerate quadratic form `Q` on a complex vector space `V` of dimension `n`
(Mathlib's `CliffordAlgebra Q`), we prove:

* `finrank_cliffordAlgebra`: the dimension is `2 ^ n`;
* `Anti.basis`: for pairwise anticommuting involutions `g i` generating an algebra of dimension
  `2 ^ n`, the ordered products over subsets form a basis (spanning is shown by sorting, then the
  dimension count gives independence);
* `Anti.center_le_span`: the centre is spanned by `1`, and by `1` and the product of all
  generators when `n` is odd (this uses the sign rule for commuting a generator past an ordered
  product); the full product is a non-scalar central element for odd `n`;
* `exists_pi_matrix_of_center`: a finite dimensional semisimple complex algebra is a product of
  `k` matrix algebras with `k` at most the size of a spanning set of the centre (and at least two
  if a non-scalar central element exists);
* `nonempty_algEquiv_matrix_cliffordAlgebra`: for `n = 2 m` the Clifford algebra is the algebra of
  complex `2 ^ m × 2 ^ m` matrices;
* `nonempty_algEquiv_prod_matrix_cliffordAlgebra`: for `n = 2 m + 1` it is a product of two copies
  of that matrix algebra (equal sizes by the elementary fact that `2 ^ (2 m + 1)` is a sum of two
  squares only as `(2 ^ m) ^ 2 + (2 ^ m) ^ 2`, see `sq_add_sq_eq_two_pow`).
-/

namespace UndergradKB.RepresentationTheory

namespace CliffordStructure

section Generic

variable {A : Type*} [Ring A] {n : ℕ}

/-- Ordered product of the elements `g a`, `a` running through a list. -/
def prodList (g : Fin n → A) (l : List (Fin n)) : A := (l.map g).prod

@[simp] theorem prodList_nil (g : Fin n → A) : prodList g [] = 1 := rfl

@[simp] theorem prodList_cons (g : Fin n → A) (a : Fin n) (l : List (Fin n)) :
    prodList g (a :: l) = g a * prodList g l := by simp [prodList]

theorem prodList_append (g : Fin n → A) (l l' : List (Fin n)) :
    prodList g (l ++ l') = prodList g l * prodList g l' := by simp [prodList]

/-- The product of `g a` over the elements of a finite set, in increasing order. -/
def sortedProd (g : Fin n → A) (S : Finset (Fin n)) : A := prodList g S.sort

@[simp] theorem sortedProd_empty (g : Fin n → A) : sortedProd g ∅ = 1 := by
  simp [sortedProd]

/-- The family `g` consists of involutions which pairwise anticommute. -/
structure Anti (g : Fin n → A) : Prop where
  sq : ∀ i, g i * g i = 1
  anti : ∀ i j, i ≠ j → g i * g j = -(g j * g i)

variable [Algebra ℂ A] {g : Fin n → A}

theorem Anti.mul_prodList (h : Anti g) (j : Fin n) (l : List (Fin n)) :
    g j * prodList g l =
      ((-1 : ℂ) ^ (l.filter (fun a => a ≠ j)).length) • (prodList g l * g j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases haj : a = j
    · subst haj
      simp only [prodList_cons, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false]
      have h1 : g a * prodList g l * g a = ((-1 : ℂ) ^ (l.filter (fun x => x ≠ a)).length) •
          prodList g l := by
        rw [ih, smul_mul_assoc, mul_assoc, h.sq, mul_one]
      rw [h1, ← mul_assoc, h.sq, one_mul, smul_smul, ← mul_pow]
      simp
    · simp only [prodList_cons, List.filter_cons, ne_eq, haj, not_false_eq_true, decide_true,
        ite_true, List.length_cons]
      rw [← mul_assoc, h.anti j a (Ne.symm haj), neg_mul, mul_assoc, ih, mul_smul_comm,
        pow_succ]
      simp [mul_assoc, mul_comm]

theorem Anti.prodList_perm (h : Anti g) {l l' : List (Fin n)} (hp : l.Perm l') :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ prodList g l = ε • prodList g l' := by
  induction hp with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨ε, hε, he⟩ := ih
    exact ⟨ε, hε, by simp [he]⟩
  | swap x y l =>
    by_cases hxy : x = y
    · subst hxy; exact ⟨1, Or.inl rfl, by simp⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      simp only [prodList_cons]
      rw [← mul_assoc, h.anti y x (Ne.symm hxy), neg_mul, ← mul_assoc]
      simp
  | trans _ _ ih1 ih2 =>
    obtain ⟨ε, hε, he⟩ := ih1
    obtain ⟨δ, hδ, hd⟩ := ih2
    refine ⟨ε * δ, ?_, by rw [he, hd, smul_smul]⟩
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp

/-- The span of the ordered products over subsets. -/
def sortedSpan (g : Fin n → A) : Submodule ℂ A := Submodule.span ℂ (Set.range (sortedProd g))

theorem Anti.prodList_mem_of_nodup (h : Anti g) {l : List (Fin n)} (hl : l.Nodup) :
    prodList g l ∈ sortedSpan g := by
  have hp : l.Perm l.toFinset.sort := by
    rw [List.perm_ext_iff_of_nodup hl (Finset.sort_nodup _ _)]
    intro a
    simp [Finset.mem_sort]
  obtain ⟨ε, -, he⟩ := h.prodList_perm hp
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l.toFinset, rfl⟩)

theorem Anti.mul_prodList_mem (h : Anti g) (j : Fin n) {l : List (Fin n)} (hl : l.Nodup) :
    g j * prodList g l ∈ sortedSpan g := by
  by_cases hj : j ∈ l
  · obtain ⟨ε, -, he⟩ := h.prodList_perm (List.perm_cons_erase hj)
    rw [he, prodList_cons, mul_smul_comm, ← mul_assoc, h.sq, one_mul]
    exact Submodule.smul_mem _ _ (h.prodList_mem_of_nodup (hl.erase j))
  · have := h.prodList_mem_of_nodup (List.nodup_cons.2 ⟨hj, hl⟩)
    simpa using this

theorem Anti.mul_mem_sortedSpan (h : Anti g) (j : Fin n) {x : A} (hx : x ∈ sortedSpan g) :
    g j * x ∈ sortedSpan g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, rfl⟩ := hy
    exact h.mul_prodList_mem j (Finset.sort_nodup _ _)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem Anti.prodList_mem (h : Anti g) (l : List (Fin n)) : prodList g l ∈ sortedSpan g := by
  induction l with
  | nil =>
    rw [prodList_nil, ← sortedProd_empty g]
    exact Submodule.subset_span ⟨∅, rfl⟩
  | cons a l ih => rw [prodList_cons]; exact h.mul_mem_sortedSpan a ih

theorem Anti.top_le_sortedSpan (h : Anti g) (hgen : Algebra.adjoin ℂ (Set.range g) = ⊤) :
    ⊤ ≤ sortedSpan g := by
  let R : Submonoid A :=
    { carrier := Set.range (prodList g)
      one_mem' := ⟨[], rfl⟩
      mul_mem' := by
        rintro _ _ ⟨l, rfl⟩ ⟨l', rfl⟩
        exact ⟨l ++ l', prodList_append g l l'⟩ }
  have hcl : Submonoid.closure (Set.range g) ≤ R := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨[i], by simp⟩
  rw [← Algebra.top_toSubmodule, ← hgen, Algebra.adjoin_eq_span]
  refine Submodule.span_le.2 (fun x hx => ?_)
  obtain ⟨l, rfl⟩ := hcl hx
  exact h.prodList_mem l

/-- The ordered products over subsets form a basis, when the dimension is `2 ^ n`. -/
noncomputable def Anti.basis (h : Anti g) (hgen : Algebra.adjoin ℂ (Set.range g) = ⊤)
    (hdim : Module.finrank ℂ A = 2 ^ n) : Module.Basis (Finset (Fin n)) ℂ A :=
  basisOfTopLeSpanOfCardEqFinrank (sortedProd g) (h.top_le_sortedSpan hgen)
    (by simp [hdim])

theorem Anti.basis_apply (h : Anti g) (hgen : Algebra.adjoin ℂ (Set.range g) = ⊤)
    (hdim : Module.finrank ℂ A = 2 ^ n) (S : Finset (Fin n)) :
    h.basis hgen hdim S = sortedProd g S := by
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank (sortedProd g) _ _) S

theorem Anti.mul_sortedProd (h : Anti g) (j : Fin n) (S : Finset (Fin n)) :
    g j * sortedProd g S =
      ((-1 : ℂ) ^ (S.erase j).card) • (sortedProd g S * g j) := by
  rw [sortedProd, h.mul_prodList]
  congr 3
  rw [← Finset.filter_ne' S j, ← List.toFinset_card_of_nodup
    ((Finset.sort_nodup _ _).filter _), List.toFinset_filter]
  simp [Finset.sort_toFinset]

theorem Anti.center_coeff (h : Anti g) (b : Module.Basis (Finset (Fin n)) ℂ A)
    (hb : ∀ S, b S = sortedProd g S) {x : A} (hx : ∀ j, g j * x = x * g j)
    (S : Finset (Fin n)) (hS : b.repr x S ≠ 0) : S = ∅ ∨ (S = Finset.univ ∧ Odd n) := by
  classical
  have hxsum : x = ∑ T, b.repr x T • b T := (b.sum_repr x).symm
  have key : ∀ j T, b.repr x T * ((-1 : ℂ) ^ (T.erase j).card - 1) = 0 := by
    intro j T
    have e1 : g j * x = ∑ T, (b.repr x T * (-1 : ℂ) ^ (T.erase j).card) • (b T * g j) := by
      conv_lhs => rw [hxsum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [mul_smul_comm, hb, h.mul_sortedProd, smul_smul]
    have e2 : x * g j = ∑ T, b.repr x T • (b T * g j) := by
      conv_lhs => rw [hxsum]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun T _ => by rw [smul_mul_assoc])
    have e3 : (∑ T, (b.repr x T * ((-1 : ℂ) ^ (T.erase j).card - 1)) • b T) * g j = 0 := by
      rw [Finset.sum_mul]
      have : ∑ T, ((b.repr x T * ((-1 : ℂ) ^ (T.erase j).card - 1)) • b T) * g j =
          ∑ T, (b.repr x T * (-1 : ℂ) ^ (T.erase j).card) • (b T * g j) -
            ∑ T, b.repr x T • (b T * g j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [smul_mul_assoc, mul_sub, mul_one, sub_smul]
      rw [this, ← e1, ← e2, hx j, sub_self]
    have e4 : ∑ T, (b.repr x T * ((-1 : ℂ) ^ (T.erase j).card - 1)) • b T = 0 := by
      have := congrArg (fun y => y * g j) e3
      simpa [mul_assoc, h.sq] using this
    have := congrArg (fun y => b.repr y T) e4
    simp only [b.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this
  have hev : ∀ j, Even (S.erase j).card := by
    intro j
    have := (mul_eq_zero.1 (key j S)).resolve_left hS
    exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 (sub_eq_zero.1 this)
  by_cases hS0 : S = ∅
  · exact Or.inl hS0
  · right
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS0
    have hi' := hev i
    rw [Finset.card_erase_of_mem hi] at hi'
    have hpos := Finset.card_pos.2 ⟨i, hi⟩
    have hSuniv : S = Finset.univ := by
      refine Finset.eq_univ_of_forall (fun j => ?_)
      by_contra hj
      have := hev j
      rw [Finset.erase_eq_of_notMem hj] at this
      rw [Nat.even_iff] at this hi'
      omega
    refine ⟨hSuniv, ?_⟩
    have hcard : S.card = n := by rw [hSuniv]; simp
    rw [hcard, Nat.even_iff] at hi'
    rw [hcard] at hpos
    rw [Nat.odd_iff]
    omega

theorem Anti.sortedProd_univ_mem_center (h : Anti g)
    (hgen : Algebra.adjoin ℂ (Set.range g) = ⊤) (hn : Odd n) :
    sortedProd g Finset.univ ∈ Subalgebra.center ℂ A := by
  have hj : ∀ j, g j * sortedProd g Finset.univ = sortedProd g Finset.univ * g j := by
    intro j
    rw [h.mul_sortedProd, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Fintype.card_fin]
    have : Even (n - 1) := by
      rw [Nat.even_iff]
      have := Nat.odd_iff.1 hn
      omega
    rw [this.neg_one_pow, one_smul]
  have hle : ⊤ ≤ Subalgebra.centralizer ℂ ({sortedProd g Finset.univ} : Set A) := by
    rw [← hgen, Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (hj j).symm
  rw [Subalgebra.mem_center_iff]
  intro y
  have := ((Subalgebra.mem_centralizer_iff ℂ).1 (hle (Algebra.mem_top (x := y)))) _ rfl
  exact this.symm

theorem Anti.center_le_span (h : Anti g) (hgen : Algebra.adjoin ℂ (Set.range g) = ⊤)
    (hdim : Module.finrank ℂ A = 2 ^ n) {x : A} (hx : x ∈ Subalgebra.center ℂ A) :
    x ∈ Submodule.span ℂ ({1, sortedProd g Finset.univ} : Set A) ∧
      (¬ Odd n → x ∈ Submodule.span ℂ ({1} : Set A)) := by
  classical
  have hall := h.center_coeff (h.basis hgen hdim) (h.basis_apply hgen hdim)
    (fun j => Subalgebra.mem_center_iff.1 hx (g j))
  rw [← (h.basis hgen hdim).sum_repr x]
  refine ⟨Submodule.sum_mem _ fun T _ => ?_, fun hn => Submodule.sum_mem _ fun T _ => ?_⟩
  · by_cases hT : (h.basis hgen hdim).repr x T = 0
    · simp [hT]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rcases hall T hT with rfl | ⟨rfl, -⟩
      · simp [h.basis_apply]
      · simp [h.basis_apply]
  · by_cases hT : (h.basis hgen hdim).repr x T = 0
    · simp [hT]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      rcases hall T hT with rfl | ⟨rfl, hodd⟩
      · simp [h.basis_apply]
      · exact absurd hodd hn

theorem Anti.sortedProd_univ_not_scalar (h : Anti g) (hgen : Algebra.adjoin ℂ (Set.range g) = ⊤)
    (hdim : Module.finrank ℂ A = 2 ^ n) (hn : Odd n) (c : ℂ) :
    sortedProd g Finset.univ ≠ algebraMap ℂ A c := by
  intro hc
  have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    rw [← Finset.nonempty_iff_ne_empty]
    obtain ⟨k, hk⟩ := hn
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have := congrArg ((h.basis hgen hdim).repr · Finset.univ) hc
  rw [Algebra.algebraMap_eq_smul_one, ← sortedProd_empty g, ← h.basis_apply hgen hdim,
    ← h.basis_apply hgen hdim] at this
  simp [hne] at this

end Generic

section Wedderburn

variable {A : Type*} [Ring A] [Algebra ℂ A] [IsSemisimpleRing A] [FiniteDimensional ℂ A]

/-- A finite dimensional semisimple complex algebra is a product of `k` matrix algebras, where
`k` is at most the number of vectors spanning the centre, and at least `2` if the centre contains
a non-scalar element. -/
theorem exists_pi_matrix_of_center {N : ℕ} (hdim : Module.finrank ℂ A = N) (hN : 0 < N)
    (s : Finset A) (hs : ∀ x ∈ Subalgebra.center ℂ A, x ∈ Submodule.span ℂ (s : Set A)) :
    ∃ (k : ℕ) (d : Fin k → ℕ), (∀ i, 0 < d i) ∧
      Nonempty (A ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ∧ ∑ i, d i ^ 2 = N ∧
      1 ≤ k ∧ k ≤ s.card ∧
      ((∃ z ∈ Subalgebra.center ℂ A, ∀ c : ℂ, z ≠ algebraMap ℂ A c) → 2 ≤ k) := by
  classical
  obtain ⟨k, d, hd, ⟨E⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A
  have hd' : ∀ i, 0 < d i := fun i => Nat.pos_of_ne_zero (hd i).out
  have : ∀ i, Nonempty (Fin (d i)) := fun i => ⟨⟨0, hd' i⟩⟩
  have hsum : ∑ i, d i ^ 2 = N := by
    rw [← hdim, E.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [Module.finrank_matrix, sq]
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hsum; omega
    · exact hk
  have hcen : ∀ i, E.symm (Pi.single i 1) ∈ Subalgebra.center ℂ A := by
    intro i
    rw [Subalgebra.mem_center_iff]
    intro y
    apply E.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hli : LinearIndependent ℂ (fun i : Fin k => (E.symm (Pi.single i 1) : A)) := by
    have : LinearIndependent ℂ
        (fun i : Fin k => (Pi.single i 1 : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
      rw [linearIndependent_iff']
      intro t c ht i hi
      have h2 := congrFun ht i
      rw [Finset.sum_apply, Finset.sum_eq_single i] at h2
      · simpa using h2
      · intro j _ hji
        simp [Pi.single_eq_of_ne (Ne.symm hji)]
      · intro h; exact absurd hi h
    exact this.map' E.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  have hle := linearIndependent_le_span' _ hli (s : Set A) (by
    rintro _ ⟨i, rfl⟩
    exact hs _ (hcen i))
  simp only [Cardinal.mk_fintype, Fintype.card_fin] at hle
  have hle' : k ≤ s.card := by
    have h1 : k ≤ Fintype.card (↥(s : Set A)) := by exact_mod_cast hle
    simpa using h1
  refine ⟨k, d, hd', ⟨E⟩, hsum, hk1, hle', ?_⟩
  rintro ⟨z, hz, hnz⟩
  by_contra hk
  obtain rfl : k = 1 := by omega
  have hEz : ∀ y, y * E z = E z * y := by
    intro y
    have := Subalgebra.mem_center_iff.1 hz (E.symm y)
    simpa using congrArg E this
  have hM : E z 0 ∈ Set.center (Matrix (Fin (d 0)) (Fin (d 0)) ℂ) := by
    rw [Semigroup.mem_center_iff]
    intro N
    have := congrFun (hEz (Pi.single 0 N)) 0
    simpa using this
  rw [Matrix.center_eq_range] at hM
  obtain ⟨c, hc⟩ := hM
  apply hnz c
  apply E.injective
  rw [AlgEquiv.commutes]
  funext i
  rw [Subsingleton.elim i 0]
  rw [Pi.algebraMap_apply, ← hc]
  simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]

end Wedderburn

section Arith

theorem sq_add_sq_eq_two_pow (m : ℕ) : ∀ x y : ℕ, x ^ 2 + y ^ 2 = 2 ^ (2 * m + 1) →
    x = 2 ^ m ∧ y = 2 ^ m := by
  induction m with
  | zero =>
    intro x y h
    simp at h
    have hx : x ≤ 1 := by nlinarith
    have hy : y ≤ 1 := by nlinarith
    interval_cases x <;> interval_cases y <;> simp_all
  | succ m ih =>
    intro x y h
    have h4 : (2 : ℕ) ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) := by ring
    rw [h4] at h
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' x <;> obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' y
    · have h' : a ^ 2 + b ^ 2 = 2 ^ (2 * m + 1) := by nlinarith
      obtain ⟨ha, hb⟩ := ih a b h'
      subst ha hb
      constructor <;> ring
    · exfalso
      have e1 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      have e2 : (2 * b + 1) ^ 2 = 4 * (b ^ 2 + b) + 1 := by ring
      omega
    · exfalso
      have e1 : (2 * a + 1) ^ 2 = 4 * (a ^ 2 + a) + 1 := by ring
      have e2 : (2 * b) ^ 2 = 4 * b ^ 2 := by ring
      omega
    · exfalso
      have e1 : (2 * a + 1) ^ 2 = 4 * (a ^ 2 + a) + 1 := by ring
      have e2 : (2 * b + 1) ^ 2 = 4 * (b ^ 2 + b) + 1 := by ring
      omega

end Arith

section Clifford

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The Clifford algebra of a quadratic form on a complex space of dimension `n` has dimension
`2 ^ n` (it is linearly equivalent to the exterior algebra). -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem finrank_cliffordAlgebra (Q : QuadraticForm ℂ V) :
    Module.finrank ℂ (CliffordAlgebra Q) = 2 ^ Module.finrank ℂ V := by
  have : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  rw [(CliffordAlgebra.equivExterior Q).finrank_eq,
    Module.finrank_eq_card_basis ((Module.finBasis ℂ V).ExteriorAlgebra)]
  simp

/-- A nondegenerate quadratic form on a complex space has an orthonormal basis. -/
theorem exists_orthonormal (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate) :
    ∃ w : Fin (Module.finrank ℂ V) → V, (∀ i, Q (w i) = 1) ∧
      (∀ i j, i ≠ j → QuadraticMap.polar Q (w i) (w j) = 0) ∧
      Submodule.span ℂ (Set.range w) = ⊤ := by
  classical
  have : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  have hsep : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).2 hQ).1
  obtain ⟨e⟩ := Q.equivalent_weightedSumSquares_of_isAlgClosed hsep
  let w : Fin (Module.finrank ℂ V) → V := fun i => e.symm (Pi.single i 1)
  have hQw : ∀ i, Q (w i) = 1 := by
    intro i
    have := e.symm.map_app (Pi.single i (1 : ℂ))
    simp [w, QuadraticMap.weightedSumSquares_apply, Pi.single_apply]
  refine ⟨w, hQw, ?_, ?_⟩
  · intro i j hij
    have h2 := hQw i
    have h3 := hQw j
    have h4 : Q (w i + w j) = 2 := by
      have : w i + w j = e.symm (Pi.single i (1 : ℂ) + Pi.single j 1) := by simp [w]
      rw [this, e.symm.map_app]
      simp only [QuadraticMap.weightedSumSquares_apply, Pi.single_apply, Pi.add_apply,
        Pi.one_apply, smul_eq_mul, one_mul]
      have hs : ∀ x : Fin (Module.finrank ℂ V),
          ((if x = i then (1 : ℂ) else 0) + if x = j then 1 else 0) *
            ((if x = i then (1 : ℂ) else 0) + if x = j then 1 else 0) =
          (if x = i then (1 : ℂ) else 0) + if x = j then 1 else 0 := by
        intro x
        by_cases hxi : x = i
        · have : x ≠ j := fun h => hij (hxi.symm.trans h)
          simp [hxi, hij]
        · by_cases hxj : x = j
          · simp [hxj, hij.symm]
          · simp [hxi, hxj]
      rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_add_distrib]
      simp
      norm_num
    simp only [QuadraticMap.polar, h4, h2, h3]
    norm_num
  · have hb := ((Pi.basisFun ℂ (Fin (Module.finrank ℂ V))).map e.symm.toLinearEquiv).span_eq
    rw [Module.Basis.coe_map] at hb
    convert hb using 2
    ext x
    simp [w]

/-- The generators `ι (w i)` attached to an orthonormal basis are pairwise anticommuting
involutions generating the Clifford algebra. -/
theorem exists_anti (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate) :
    ∃ g : Fin (Module.finrank ℂ V) → CliffordAlgebra Q, Anti g ∧
      Algebra.adjoin ℂ (Set.range g) = ⊤ := by
  obtain ⟨w, hQw, hpol, hspan⟩ := exists_orthonormal Q hQ
  refine ⟨fun i => ι Q (w i), ⟨fun i => by rw [ι_sq_scalar, hQw i, map_one], ?_⟩, ?_⟩
  · intro i j hij
    have := ι_mul_ι_add_swap (Q := Q) (w i) (w j)
    rw [hpol i j hij, map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  · rw [eq_top_iff, ← adjoin_range_ι, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span ℂ (Set.range w) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | zero => rw [SetLike.mem_coe, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [SetLike.mem_coe, map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [SetLike.mem_coe, map_smul]; exact Subalgebra.smul_mem _ hx a

/-- The Clifford algebra of a nondegenerate form is a product of matrix algebras: one factor if the
dimension `n` is even, two factors if `n` is odd; the squares of the sizes add up to `2 ^ n`. -/
theorem exists_pi_matrix_cliffordAlgebra (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate) :
    ∃ (k : ℕ) (d : Fin k → ℕ), (∀ i, 0 < d i) ∧
      Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ∧
      ∑ i, d i ^ 2 = 2 ^ Module.finrank ℂ V ∧
      (¬ Odd (Module.finrank ℂ V) → k = 1) ∧ (Odd (Module.finrank ℂ V) → k = 2) := by
  classical
  have : IsSemisimpleRing (CliffordAlgebra Q) :=
    CliffordSemisimple.isSemisimpleRing_cliffordAlgebra Q hQ
  obtain ⟨g, hg, hgen⟩ := exists_anti Q hQ
  have hdim := finrank_cliffordAlgebra Q
  have hpos : 0 < 2 ^ Module.finrank ℂ V := by positivity
  have : FiniteDimensional ℂ (CliffordAlgebra Q) :=
    Module.finite_of_finrank_pos (by rw [hdim]; exact hpos)
  by_cases hn : Odd (Module.finrank ℂ V)
  · obtain ⟨k, d, hd, hE, hsum, hk1, hk2, hk3⟩ := exists_pi_matrix_of_center hdim hpos
      {1, sortedProd g Finset.univ} (fun x hx => by
        simpa using (hg.center_le_span hgen hdim hx).1)
    have hk2' : k ≤ 2 := hk2.trans Finset.card_le_two
    have hk3' := hk3 ⟨_, hg.sortedProd_univ_mem_center hgen hn,
      hg.sortedProd_univ_not_scalar hgen hdim hn⟩
    exact ⟨k, d, hd, hE, hsum, fun h => absurd hn h, fun _ => by omega⟩
  · obtain ⟨k, d, hd, hE, hsum, hk1, hk2, -⟩ := exists_pi_matrix_of_center hdim hpos
      {1} (fun x hx => by simpa using (hg.center_le_span hgen hdim hx).2 hn)
    have hk2' : k ≤ 1 := by simpa using hk2
    exact ⟨k, d, hd, hE, hsum, fun _ => by omega, fun h => absurd h hn⟩

/-- **Etingof Problem 2.25 (i), even dimension.** If `dim V = 2 m` and `Q` is nondegenerate, the
Clifford algebra is isomorphic to the algebra of `2 ^ m × 2 ^ m` complex matrices. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem nonempty_algEquiv_matrix_cliffordAlgebra (Q : QuadraticForm ℂ V) (hQ : Q.Nondegenerate)
    (m : ℕ) (hm : Module.finrank ℂ V = 2 * m) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) := by
  obtain ⟨k, d, hd, ⟨E⟩, hsum, hk, -⟩ := exists_pi_matrix_cliffordAlgebra Q hQ
  have hev : ¬ Odd (Module.finrank ℂ V) := by
    rw [hm, Nat.not_odd_iff_even]; exact even_two_mul m
  obtain rfl : k = 1 := hk hev
  rw [Fin.sum_univ_one, hm, pow_mul'] at hsum
  have hd0 : d 0 = 2 ^ m := by
    have h2 : (d 0) ^ 2 = (2 ^ m) ^ 2 := hsum
    exact (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) two_ne_zero).1 h2
  have hdi : ∀ i : Fin 1, d i = 2 ^ m := fun i => by rw [Subsingleton.elim i 0]; exact hd0
  exact ⟨E.trans ((AlgEquiv.piCongrRight fun i =>
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hdi i))).trans (AlgEquiv.funUnique ℂ (Fin 1) _))⟩

/-- **Etingof Problem 2.25 (i), odd dimension.** If `dim V = 2 m + 1` and `Q` is nondegenerate,
the Clifford algebra is isomorphic to a product of two copies of the algebra of
`2 ^ m × 2 ^ m` complex matrices. -/
@[kb "etingof2011" "Problem 2.25, p. 31"]
theorem nonempty_algEquiv_prod_matrix_cliffordAlgebra (Q : QuadraticForm ℂ V)
    (hQ : Q.Nondegenerate) (m : ℕ) (hm : Module.finrank ℂ V = 2 * m + 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ]
      Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ × Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) := by
  obtain ⟨k, d, hd, ⟨E⟩, hsum, -, hk⟩ := exists_pi_matrix_cliffordAlgebra Q hQ
  have hodd : Odd (Module.finrank ℂ V) := ⟨m, by omega⟩
  obtain rfl : k = 2 := hk hodd
  rw [Fin.sum_univ_two, hm] at hsum
  obtain ⟨h0, h1⟩ := sq_add_sq_eq_two_pow m _ _ hsum
  have hdi : ∀ i : Fin 2, d i = 2 ^ m := fun i => by fin_cases i <;> assumption
  let F : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₐ[ℂ]
      Π _ : Fin 2, Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
    AlgEquiv.piCongrRight fun i => Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hdi i))
  let P : (Π _ : Fin 2, Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) ≃ₐ[ℂ]
      Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ × Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo fun _ => Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
      (fun r => rfl)
  exact ⟨E.trans (F.trans P)⟩

end Clifford

end CliffordStructure

end UndergradKB.RepresentationTheory
