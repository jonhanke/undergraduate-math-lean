import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Basic.Complex.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Module.Submodule.Range
import UndergradKB.Common.Attr

/-! # Young symmetrizers and the idempotent lemma (Etingof et al., §4.12-4.13)

* A tableau for a Young diagram `μ` is a bijection `YoungTableau μ := μ ≃ Fin μ.card` between the boxes and the
  numbers `0, …, n-1` (Mathlib already provides the passage between partitions of `n` and Young diagrams with `n`
  boxes: `YoungDiagram.ofPartition`, `YoungDiagram.equivPartition`).
* `rowSubgroup T` / `colSubgroup T`: the permutations of `Fin n` preserving every row / column of `T`.
* `rowSum`, `colSum`, `youngSymmetrizer`: the elements `a`, `b`, `c = a b` of the group algebra `ℂ[S_n]`.
* **Lemma 4.43** (`homIdealSpanEquiv`): for an idempotent `e` of an algebra `A` and an `A`-module `M`,
  `Hom_A(A e, M) ≃ e M`.
-/

universe u v

namespace UndergradKB.RepresentationTheory

open scoped BigOperators

/-! ### Tableaux and row and column subgroups -/

/-- A tableau of shape `μ`: a bijection between the boxes of `μ` and `Fin μ.card` (the numbers filling them). -/
@[kb "etingof2011" "Definition 4.35, p. 58"]
abbrev YoungTableau (μ : YoungDiagram) := μ ≃ Fin μ.card

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The row index of the box containing the number `i`. -/
def rowOf (T : YoungTableau μ) (i : Fin μ.card) : ℕ := (T.symm i : ℕ × ℕ).1

/-- The column index of the box containing the number `i`. -/
def colOf (T : YoungTableau μ) (i : Fin μ.card) : ℕ := (T.symm i : ℕ × ℕ).2

lemma eq_of_rowOf_colOf (T : YoungTableau μ) {i j : Fin μ.card} (hr : T.rowOf i = T.rowOf j)
    (hc : T.colOf i = T.colOf j) : i = j := by
  have : T.symm i = T.symm j := Subtype.ext (Prod.ext hr hc)
  exact T.symm.injective this

end YoungTableau

/-- The permutations of `α` preserving the fibres of a function `f : α → β`. -/
def fiberSubgroup {α β : Type*} (f : α → β) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ i, f (g i) = f i}
  one_mem' := fun _ => rfl
  mul_mem' := fun {g h} hg hh i => by
    show f (g (h i)) = f i
    rw [hg, hh]
  inv_mem' := fun {g} hg i => by
    have := hg (g⁻¹ i)
    rw [show g (g⁻¹ i) = i from g.apply_symm_apply i] at this
    exact this.symm

lemma mem_fiberSubgroup {α β : Type*} (f : α → β) (g : Equiv.Perm α) :
    g ∈ fiberSubgroup f ↔ ∀ i, f (g i) = f i := Iff.rfl

/-- The row subgroup `P_T` of `S_n`: permutations sending each number to a number in the same row. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
def rowSubgroup {μ : YoungDiagram} (T : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup T.rowOf

/-- The column subgroup `Q_T` of `S_n`: permutations sending each number to a number in the same column. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
def colSubgroup {μ : YoungDiagram} (T : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) :=
  fiberSubgroup T.colOf

/-- The row and column subgroups of a tableau meet trivially. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
lemma rowSubgroup_inf_colSubgroup {μ : YoungDiagram} (T : YoungTableau μ) :
    rowSubgroup T ⊓ colSubgroup T = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext i
  exact congrArg Fin.val (T.eq_of_rowOf_colOf (hg.1 i) (hg.2 i))

/-! ### Young symmetrizers -/

section Symmetrizers

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- The weighted sum `∑_{g ∈ H} χ(g) g` in the group algebra `ℂ[G]`, for a subgroup `H` and a
character `χ : G →* ℂ`. -/
noncomputable def twistedSum (H : Subgroup G) (χ : G →* ℂ) : MonoidAlgebra ℂ G :=
  ∑ g : H, χ g • MonoidAlgebra.single (g : G) 1

open scoped Classical in
lemma single_mul_twistedSum (H : Subgroup G) (χ : G →* ℂ) {h : G} (hh : h ∈ H) :
    MonoidAlgebra.single h 1 * twistedSum H χ = χ h⁻¹ • twistedSum H χ := by
  unfold twistedSum
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H)) _ _ (fun g => ?_)
  rw [mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul, smul_smul]
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

open scoped Classical in
lemma twistedSum_mul_single (H : Subgroup G) (χ : G →* ℂ) {h : G} (hh : h ∈ H) :
    twistedSum H χ * MonoidAlgebra.single h 1 = χ h⁻¹ • twistedSum H χ := by
  unfold twistedSum
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : H)) _ _ (fun g => ?_)
  rw [smul_mul_assoc, MonoidAlgebra.single_mul_single, one_mul, smul_smul]
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul]
  rw [mul_comm (χ h⁻¹), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

open scoped Classical in
/-- `(∑_{g∈H} χ(g) g)^2 = |H| ∑_{g∈H} χ(g) g`. -/
lemma twistedSum_mul_self (H : Subgroup G) (χ : G →* ℂ) :
    twistedSum H χ * twistedSum H χ = (Fintype.card H : ℂ) • twistedSum H χ := by
  change (∑ g : H, χ g • MonoidAlgebra.single (g : G) 1) * twistedSum H χ = _
  rw [Finset.sum_mul]
  have : ∀ g : H, (χ g • MonoidAlgebra.single (g : G) 1) * twistedSum H χ = twistedSum H χ := by
    intro g
    rw [smul_mul_assoc, single_mul_twistedSum H χ g.2, smul_smul, ← map_mul, mul_inv_cancel,
      map_one, one_smul]
  rw [Finset.sum_congr rfl (fun g _ => this g)]
  rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/-- The sign character `S_n → ℂ`. -/
noncomputable def signChar (α : Type*) [DecidableEq α] [Fintype α] : Equiv.Perm α →* ℂ :=
  (Int.castRingHom ℂ : ℤ →* ℂ).comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

end Symmetrizers

/-- `a_T = ∑_{g ∈ P_T} g` in `ℂ[S_n]`. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
noncomputable def rowSum {μ : YoungDiagram} (T : YoungTableau μ) : MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)) :=
  twistedSum (rowSubgroup T) 1

/-- `b_T = ∑_{g ∈ Q_T} sign(g) g` in `ℂ[S_n]`. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
noncomputable def colSum {μ : YoungDiagram} (T : YoungTableau μ) : MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)) :=
  twistedSum (colSubgroup T) (signChar _)

/-- The Young symmetrizer `c_T = a_T b_T`. -/
@[kb "etingof2011" "§4.12 (within Definition 4.35), p. 58"]
noncomputable def youngSymmetrizer {μ : YoungDiagram} (T : YoungTableau μ) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)) :=
  rowSum T * colSum T

open scoped Classical in
lemma rowSum_mul_self {μ : YoungDiagram} (T : YoungTableau μ) :
    rowSum T * rowSum T = (Nat.card (rowSubgroup T) : ℂ) • rowSum T := by
  rw [Nat.card_eq_fintype_card]
  exact twistedSum_mul_self _ _

open scoped Classical in
lemma colSum_mul_self {μ : YoungDiagram} (T : YoungTableau μ) :
    colSum T * colSum T = (Nat.card (colSubgroup T) : ℂ) • colSum T := by
  rw [Nat.card_eq_fintype_card]
  exact twistedSum_mul_self _ _

/-! ### Easy half of Lemma 4.40

The scalar in Lemma 4.40 is computed on group elements `g`.  If `g = p q` with `p ∈ P_T`, `q ∈ Q_T`, then
`a g b = sign(q) c`; if some `t ∈ P_T` has `g⁻¹ t g ∈ Q_T` of sign `-1`, then `a g b = 0`.  What is missing for the
full lemma is the combinatorial Lemma 4.39 (every `g ∉ P_T Q_T` admits such a `t`). -/

open scoped Classical in
lemma rowSum_mul_single_mul_colSum_of_mul {μ : YoungDiagram} (T : YoungTableau μ)
    {p q : Equiv.Perm (Fin μ.card)} (hp : p ∈ rowSubgroup T) (hq : q ∈ colSubgroup T) :
    rowSum T * MonoidAlgebra.single (p * q) 1 * colSum T = signChar _ q⁻¹ • youngSymmetrizer T := by
  have h1 : (MonoidAlgebra.single (p * q) 1 : MonoidAlgebra ℂ _) =
      MonoidAlgebra.single p 1 * MonoidAlgebra.single q 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have ea : rowSum T * MonoidAlgebra.single p 1 = rowSum T := by
    have := twistedSum_mul_single (rowSubgroup T) 1 hp
    simpa [rowSum] using this
  have eb : MonoidAlgebra.single q 1 * colSum T = signChar _ q⁻¹ • colSum T :=
    single_mul_twistedSum (colSubgroup T) (signChar _) hq
  have e2 : rowSum T * (MonoidAlgebra.single p 1 * MonoidAlgebra.single q 1) * colSum T =
      (rowSum T * MonoidAlgebra.single p 1) * (MonoidAlgebra.single q 1 * colSum T) := by
    simp only [mul_assoc]
  rw [h1, e2, ea, eb, mul_smul_comm]
  rfl

open scoped Classical in
lemma rowSum_mul_single_mul_colSum_of_transposition {μ : YoungDiagram} (T : YoungTableau μ)
    {t g : Equiv.Perm (Fin μ.card)} (ht : t ∈ rowSubgroup T) (hu : g⁻¹ * t * g ∈ colSubgroup T)
    (hneg : signChar _ (g⁻¹ * t * g)⁻¹ = -1) :
    rowSum T * MonoidAlgebra.single g 1 * colSum T = 0 := by
  set X : MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card)) := rowSum T * MonoidAlgebra.single g 1 * colSum T
  have h1 : X = -X := by
    have e1 : rowSum T = rowSum T * MonoidAlgebra.single t 1 := by
      rw [rowSum, twistedSum_mul_single _ _ ht]; simp
    have e2 : MonoidAlgebra.single t 1 * MonoidAlgebra.single g 1 =
        (MonoidAlgebra.single g 1 : MonoidAlgebra ℂ _) * MonoidAlgebra.single (g⁻¹ * t * g) 1 := by
      simp only [MonoidAlgebra.single_mul_single, mul_one]
      congr 1
      simp [mul_assoc]
    have e3 := single_mul_twistedSum (colSubgroup T) (signChar _) hu
    calc X = (rowSum T * MonoidAlgebra.single t 1) * MonoidAlgebra.single g 1 * colSum T := by
          rw [← e1]
      _ = rowSum T * (MonoidAlgebra.single g 1 * MonoidAlgebra.single (g⁻¹ * t * g) 1) * colSum T := by
          rw [mul_assoc (rowSum T), e2]
      _ = rowSum T * MonoidAlgebra.single g 1 * (MonoidAlgebra.single (g⁻¹ * t * g) 1 * colSum T) := by
          simp only [mul_assoc]
      _ = -X := by
          rw [colSum, e3, hneg]
          simp [X, colSum]
  have h2 : (2 : ℂ) • X = 0 := by
    rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel X
  rcases smul_eq_zero.1 h2 with h | h
  · norm_num at h
  · exact h

/-! ### Lemma 4.43: Hom from a left ideal generated by an idempotent -/

section Idempotent

variable {k : Type u} {A : Type v} {M : Type*} [CommSemiring k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The subspace `e M` of an `A`-module `M`. -/
def idemSubmodule (k : Type u) {A : Type v} (M : Type*) [CommSemiring k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] (e : A) : Submodule k M :=
  LinearMap.range (DistribSMul.toLinearMap k M e)

lemma mem_idemSubmodule {e : A} (he : IsIdempotentElem e) {m : M} :
    m ∈ idemSubmodule k M e ↔ e • m = m := by
  constructor
  · rintro ⟨m', rfl⟩
    simp only [DistribSMul.toLinearMap_apply]
    rw [← mul_smul, he.eq]
  · intro h
    exact ⟨m, h⟩

lemma idem_smul_apply {e : A} (he : IsIdempotentElem e) (φ : Ideal.span {e} →ₗ[A] M) :
    e • φ ⟨e, Ideal.subset_span rfl⟩ = φ ⟨e, Ideal.subset_span rfl⟩ := by
  have : (⟨e, Ideal.subset_span rfl⟩ : Ideal.span {e}) = e • (⟨e, Ideal.subset_span rfl⟩ : Ideal.span {e}) :=
    Subtype.ext (by simp [he.eq])
  conv_rhs => rw [this]
  exact (φ.map_smul e _).symm

/-- **Lemma 4.43.** For an idempotent `e` of an algebra `A` and an `A`-module `M`, the space of `A`-module maps
from the left ideal `A e` to `M` is isomorphic to `e M` (via evaluation at `e`). -/
@[kb "etingof2011" "Lemma 4.43, p. 60"]
noncomputable def homIdealSpanEquiv {e : A} (he : IsIdempotentElem e) :
    (Ideal.span {e} →ₗ[A] M) ≃ₗ[k] idemSubmodule k M e where
  toFun φ := ⟨φ ⟨e, Ideal.subset_span rfl⟩, by
    rw [mem_idemSubmodule he]
    exact idem_smul_apply he φ⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl
  invFun m := (LinearMap.toSpanSingleton A M (m : M)).comp (Submodule.subtype _)
  left_inv φ := by
    ext x
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 x.2
    have hx : x = a • (⟨e, Ideal.subset_span rfl⟩ : Ideal.span {e}) := Subtype.ext (by simp [ha])
    show (x : A) • φ ⟨e, Ideal.subset_span rfl⟩ = φ x
    rw [hx, map_smul]
    show (a * e) • φ ⟨e, Ideal.subset_span rfl⟩ = _
    rw [mul_smul, idem_smul_apply he]
  right_inv m := by
    apply Subtype.ext
    have := (mem_idemSubmodule he).1 m.2
    simpa using this

end Idempotent

end UndergradKB.RepresentationTheory
