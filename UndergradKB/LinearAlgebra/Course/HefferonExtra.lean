import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Order.Setoid.Partition
import Mathlib.Algebra.Group.Conj
import UndergradKB.Common.Attr

/-! # Hefferon: additional course-layer wrappers (chapters One, Three, Five, Appendix, Topics) -/

namespace UndergradKB.LinearAlgebra.Course

open Matrix

/-! ## Chapter One -/

section One

variable {R : Type*} {m n : ℕ}

/-- A matrix is in echelon form iff each leading entry lies strictly right of the leading entry in
every higher row and zero rows sit at the bottom. -/
@[kb "hefferon2020" "One.I.1.10, p. 16"]
theorem hefferon_One_I_1_10 [Zero R] (A : Matrix (Fin m) (Fin n) R) :
    A.IsRowEchelon ↔
      (∀ i₁ i₂ c₁ c₂, i₁ < i₂ → A.IsLeadingEntry i₁ c₁ → A.IsLeadingEntry i₂ c₂ → c₁ < c₂) ∧
      (∀ i₁ i₂, i₁ < i₂ → A i₁ = 0 → A i₂ = 0) := by
  constructor
  · intro he
    refine ⟨fun i₁ i₂ c₁ c₂ hi h₁ h₂ => ?_, fun i₁ i₂ hi h0 => he.row_eq_zero_of_lt hi h0⟩
    by_contra hc
    rw [not_lt] at hc
    exact h₂.2 (he hi fun j hj => h₁.1 j (lt_of_lt_of_le hj hc))
  · rintro ⟨h1, h2⟩ i₁ i₂ hi j₂ hj
    by_contra hne
    have h2ne : A i₂ ≠ 0 := fun h => hne (by simpa using congrFun h j₂)
    have h1ne : A i₁ ≠ 0 := fun h => h2ne (h2 i₁ i₂ hi h)
    obtain ⟨c₂, hc₂⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.1 h2ne
    obtain ⟨c₁, hc₁⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.1 h1ne
    have hle : c₂ ≤ j₂ := by
      by_contra h
      exact hne (hc₂.1 j₂ (not_le.1 h))
    exact hc₁.2 (hj c₁ (lt_of_lt_of_le (h1 i₁ i₂ c₁ c₂ hi hc₁ hc₂) hle))

/-- Reduced echelon form: echelon, leading entries equal to 1, and a leading entry is the only
nonzero entry in its column. -/
@[kb "hefferon2020" "One.III.1.3, p. 61"]
theorem hefferon_One_III_1_3 [Zero R] [One R] (A : Matrix (Fin m) (Fin n) R) :
    A.IsReducedRowEchelon ↔
      A.IsRowEchelon ∧ (∀ i c, A.IsLeadingEntry i c → A i c = 1) ∧
      (∀ i₁ i₂ c, A.IsLeadingEntry i₂ c → i₁ ≠ i₂ → A i₁ c = 0) := by
  constructor
  · intro h
    exact ⟨h.isRowEchelon, fun i c hc => h.eq_one hc,
      fun i₁ i₂ c hc hne => h.eq_zero_of_ne_of_isLeadingEntry hne hc⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun i c hc => h2 i c hc, fun i₁ i₂ c hlt hc => h3 i₁ i₂ c hc (ne_of_lt hlt)⟩

/-- Every solution of `A x = b` is a particular solution plus a solution of the homogeneous
system, and conversely. -/
@[kb "hefferon2020" "One.I.3.7, p. 38"]
theorem hefferon_One_I_3_7 [Ring R] {n' : Type*} [Fintype n'] (A : Matrix (Fin m) n' R)
    (b : Fin m → R) (p : n' → R) (hp : A *ᵥ p = b) :
    {x | A *ᵥ x = b} = {x | ∃ h, A *ᵥ h = 0 ∧ x = p + h} := by
  ext x
  constructor
  · intro hx
    exact ⟨x - p, by rw [Matrix.mulVec_sub, hx, hp, sub_self], by abel⟩
  · rintro ⟨h, hh, rfl⟩
    simp [Matrix.mulVec_add, hp, hh]

end One

/-! ## Appendix -/

section Appendix

variable {α β γ : Type*}

/-- A function has a right inverse iff it is onto. -/
@[kb "hefferon2020" "Appendix.2, p. 503"]
theorem hefferon_Appendix_2 (f : α → β) :
    Function.Surjective f ↔ ∃ g : β → α, Function.RightInverse g f :=
  Function.surjective_iff_hasRightInverse

/-- A function is a correspondence iff it has a two-sided inverse. -/
@[kb "hefferon2020" "Appendix.3, p. 504"]
theorem hefferon_Appendix_3 (f : α → β) :
    Function.Bijective f ↔ ∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse

/-- The two-sided inverse of a function is unique. -/
@[kb "hefferon2020" "Appendix.3, p. 504"]
theorem hefferon_Appendix_3_unique {f : α → β} {g g' : β → α}
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g' f) : g = g' :=
  h₁.eq_rightInverse h₂

/-- A composition of correspondences is a correspondence. -/
@[kb "hefferon2020" "Appendix.3, p. 504"]
theorem hefferon_Appendix_3_comp {f : α → β} {g : β → γ} (hf : Function.Bijective f)
    (hg : Function.Bijective g) : Function.Bijective (g ∘ f) :=
  hg.comp hf

/-- An equivalence relation yields a partition into its classes, every partition arises this
way, and the two constructions are mutually inverse. -/
@[kb "hefferon2020" "Appendix.4, p. 505"]
theorem hefferon_Appendix_4 :
    (∀ r : Setoid α, Setoid.IsPartition r.classes) ∧
    (∀ (c : Set (Set α)) (hc : Setoid.IsPartition c), (Setoid.mkClasses c hc.2).classes = c) ∧
    (∀ r : Setoid α, Setoid.mkClasses r.classes Setoid.classes_eqv_classes = r) :=
  ⟨Setoid.isPartition_classes, Setoid.classes_mkClasses, Setoid.mkClasses_classes⟩

end Appendix

/-! ## Chapter Three -/

section Three

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An automorphism is a linear isomorphism of a space with itself: a linear self-map is one
iff it is bijective. -/
@[kb "hefferon2020" "Three.I.1.7, p. 187"]
theorem hefferon_Three_I_1_7 (f : V →ₗ[K] V) :
    (∃ e : V ≃ₗ[K] V, ⇑e = f) ↔ Function.Bijective f :=
  ⟨fun ⟨e, he⟩ => he ▸ e.bijective, fun h => ⟨LinearEquiv.ofBijective f h, rfl⟩⟩

/-- The inverse of an isomorphism is linear (so again an isomorphism). -/
@[kb "hefferon2020" "Three.I.2.1, p. 193"]
theorem hefferon_Three_I_2_1 (e : V ≃ₗ[K] W) : ∃ h : W ≃ₗ[K] V, ⇑h = e.symm :=
  ⟨e.symm, rfl⟩

/-- A two-sided inverse function of a linear map is automatically linear. -/
@[kb "hefferon2020" "Three.I.2.1, p. 193"]
theorem hefferon_Three_I_2_1_inverse (f : V →ₗ[K] W) (g : W → V)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    ∃ h : W →ₗ[K] V, ⇑h = g :=
  ⟨LinearMap.inverse f g h₁ h₂, rfl⟩

/-- The coordinate map with respect to a basis is an isomorphism `V ≅ K^n`. -/
@[kb "hefferon2020" "Three.I.2.5, p. 195"]
theorem hefferon_Three_I_2_5 {n : ℕ} (B : Module.Basis (Fin n) K V) :
    ∃ e : V ≃ₗ[K] (Fin n → K), ∀ v i, e v i = B.repr v i :=
  ⟨B.equivFun, fun _ _ => rfl⟩

/-- A finite-dimensional space is isomorphic to `K^n` for exactly one `n` (its dimension). -/
@[kb "hefferon2020" "Three.I.2.8, p. 197"]
theorem hefferon_Three_I_2_8 [FiniteDimensional K V] :
    ∃ n : ℕ, Nonempty (V ≃ₗ[K] (Fin n → K)) ∧
      ∀ k : ℕ, Nonempty (V ≃ₗ[K] (Fin k → K)) → k = n := by
  refine ⟨Module.finrank K V, ⟨(Module.finBasis K V).equivFun⟩, fun k ⟨e⟩ => ?_⟩
  simpa using e.finrank_eq.symm

end Three

section Matrices

variable {R : Type*} {n m l : Type*}

/-- The main diagonal of a square matrix consists of the entries `A i i`. -/
@[kb "hefferon2020" "Three.IV.3.8, p. 257"]
theorem hefferon_Three_IV_3_8 (A : Matrix n n R) (i : n) : A.diag i = A i i := rfl

/-- The identity matrix is a two-sided identity for matrix multiplication. -/
@[kb "hefferon2020" "Three.IV.3.10, p. 257"]
theorem hefferon_Three_IV_3_10 [NonAssocSemiring R] [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n R) : (1 : Matrix m m R) * A = A ∧ A * (1 : Matrix n n R) = A :=
  ⟨Matrix.one_mul A, Matrix.mul_one A⟩

/-- A matrix is diagonal iff all its off-diagonal entries vanish. -/
@[kb "hefferon2020" "Three.IV.3.12, p. 258"]
theorem hefferon_Three_IV_3_12 [Zero R] (A : Matrix n n R) :
    A.IsDiag ↔ ∀ i j, i ≠ j → A i j = 0 :=
  Iff.rfl

/-- Left multiplication by a diagonal matrix scales rows, right multiplication scales columns. -/
@[kb "hefferon2020" "Three.IV.3.13, p. 258"]
theorem hefferon_Three_IV_3_13 [NonUnitalNonAssocSemiring R] [Fintype m] [DecidableEq m]
    [DecidableEq n] [Fintype n] (d : m → R) (e : n → R) (M : Matrix m n R) (i : m) (j : n) :
    (Matrix.diagonal d * M) i j = d i * M i j ∧ (M * Matrix.diagonal e) i j = M i j * e j :=
  ⟨Matrix.diagonal_mul d M i j, Matrix.mul_diagonal e M i j⟩

/-- The permutation matrix of `σ` has a single `1` in each row `i` (at column `σ i`) and
zeros elsewhere. -/
@[kb "hefferon2020" "Three.IV.3.14, p. 258"]
theorem hefferon_Three_IV_3_14 [Zero R] [One R] [DecidableEq n] (σ : Equiv.Perm n) (i j : n) :
    σ.permMatrix R i j = if σ i = j then 1 else 0 := by
  simp [PEquiv.toMatrix_apply]

/-- Multiplying on the left by a permutation matrix permutes rows; on the right permutes
columns. -/
@[kb "hefferon2020" "Three.IV.3.15, p. 259"]
theorem hefferon_Three_IV_3_15 [NonAssocSemiring R] [Fintype n] [DecidableEq n]
    (σ : Equiv.Perm n) (A : Matrix n m R) (B : Matrix m n R) :
    σ.permMatrix R * A = A.submatrix σ id ∧ B * σ.permMatrix R = B.submatrix id σ.symm :=
  ⟨PEquiv.toMatrix_toPEquiv_mul σ A, PEquiv.mul_toMatrix_toPEquiv B σ⟩

/-- Left multiplication by an elementary reduction matrix performs the row operation: scaling. -/
@[kb "hefferon2020" "Three.IV.3.20, p. 260"]
theorem hefferon_Three_IV_3_20_scale [CommRing R] [Fintype m] [DecidableEq m] (i : m) (c : R)
    (A : Matrix m n R) : Matrix.rowScale i c * A = A.updateRow i (c • A i) := by
  rw [Matrix.rowScale_mul]; rfl

/-- Left multiplication by an elementary reduction matrix performs the row operation: swapping. -/
@[kb "hefferon2020" "Three.IV.3.20, p. 260"]
theorem hefferon_Three_IV_3_20_swap [CommRing R] [Fintype m] [DecidableEq m] (i j : m)
    (A : Matrix m n R) : Matrix.swap R i j * A = A.submatrix (Equiv.swap i j) id := by
  ext a b
  by_cases ha : a = i
  · subst ha; simp
  by_cases hb : a = j
  · subst hb; simp
  simp [Matrix.swap_mul_of_ne ha hb, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Left multiplication by an elementary reduction matrix performs the row operation:
adding a multiple of one row to another. -/
@[kb "hefferon2020" "Three.IV.3.20, p. 260"]
theorem hefferon_Three_IV_3_20_add [CommRing R] [Fintype m] [DecidableEq m] (i j : m) (c : R)
    (A : Matrix m n R) : Matrix.transvection i j c * A = A.updateRow i (A i + c • A j) := by
  ext a b
  by_cases ha : a = i
  · subst ha; simp
  · simp [Matrix.transvection_mul_apply_of_ne _ _ _ _ ha, ha]

/-- If a matrix has a left inverse and a right inverse, they coincide. -/
@[kb "hefferon2020" "Three.IV.4.2, p. 265"]
theorem hefferon_Three_IV_4_2 [Semiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (B C : Matrix n m R) (hB : B * A = 1) (hC : A * C = 1) : B = C := by
  calc B = B * (A * C) := by rw [hC, Matrix.mul_one]
    _ = (B * A) * C := (Matrix.mul_assoc _ _ _).symm
    _ = C := by rw [hB, Matrix.one_mul]

end Matrices

section Three2

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix is invertible iff it is nonsingular (only the zero vector is sent to zero). -/
@[kb "hefferon2020" "Three.IV.4.3, p. 266"]
theorem hefferon_Three_IV_4_3 (A : Matrix n n K) :
    IsUnit A ↔ ∀ x : n → K, A *ᵥ x = 0 → x = 0 := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  constructor
  · intro h x hx
    exact h (hx.trans (Matrix.mulVec_zero A).symm)
  · intro h x y hxy
    have : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    exact sub_eq_zero.1 (h _ this)

end Three2

section ChangeBasis

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n m : Type*} [Fintype n]
  [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The change of basis matrix from `B` to `D` has `D`-coordinates of the `B`-vectors as columns,
and is the matrix of the identity map. -/
@[kb "hefferon2020" "Three.V.1.1, p. 272"]
theorem hefferon_Three_V_1_1 (B : Module.Basis n K V) (D : Module.Basis m K V) :
    (∀ i j, D.toMatrix B i j = D.repr (B j) i) ∧
      LinearMap.toMatrix B D LinearMap.id = D.toMatrix B :=
  ⟨fun _ _ => Module.Basis.toMatrix_apply D B _ _, LinearMap.toMatrix_id_eq_basis_toMatrix B D⟩

end ChangeBasis

/-! ## Topic: Geometry of Linear Maps, and Chapter Five -/

section Topics

/-- A linear map sends the line through `p` and `q` onto the line through the images (a point
if the images coincide). -/
@[kb "hefferon2020" "Topic-Geometry.2, p. 314"]
theorem hefferon_Topic_Geometry_2 {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (f : V →ₗ[ℝ] W) (p q : V) :
    f '' (affineSpan ℝ {p, q} : Set V) = (affineSpan ℝ {f p, f q} : Set W) := by
  have h := AffineSubspace.map_span f.toAffineMap {p, q}
  have h2 : (f.toAffineMap '' {p, q} : Set W) = {f p, f q} := by
    simp
  rw [h2] at h
  have := congrArg (fun S : AffineSubspace ℝ W => (S : Set W)) h
  simpa [AffineSubspace.coe_map] using this

/-- Similarity of square matrices is an equivalence relation. -/
@[kb "hefferon2020" "Five.II.1.15, p. 414"]
theorem hefferon_Five_II_1_15 {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] :
    Equivalence (IsConj : Matrix n n K → Matrix n n K → Prop) :=
  ⟨fun _ => IsConj.refl _, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end Topics

end UndergradKB.LinearAlgebra.Course
