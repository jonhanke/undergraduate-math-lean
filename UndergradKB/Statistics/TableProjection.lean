import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import UndergradKB.Common.Attr
import UndergradKB.Statistics.NormalSample
import UndergradKB.Statistics.ChiSquared
import UndergradKB.Statistics.Pearson

/-!
# The double projection of a Gaussian table

For an `r × c` table `Z` of independent standard normal entries and unit vectors `α ∈ ℝʳ`, `β ∈ ℝᶜ`, the
matrix `(I - ααᵀ) Z (I - ββᵀ)` has squared Frobenius norm with the chi-square law with `(r - 1)(c - 1)` degrees
of freedom (`hasLaw_tableProj_chiSquared`).  This is the engine behind the chi-square test of independence.

Proof: rotate by the tensor basis `Aᵢ' ⊗ Bⱼ'`, where `A` and `B` are orthonormal bases containing `α` and `β`.
The rotated coordinates are again independent standard normal (`iIndepFun_rotateι`), and in these coordinates
the double projection simply deletes the row `i₀` and the column `j₀`.
-/

namespace UndergradKB.Statistics

open MeasureTheory ProbabilityTheory Real Set Finset

/-! ### Rotation over an arbitrary finite index type -/

section RotationGeneral

variable {ι : Type*} [Fintype ι]

/-- The coordinates of a vector in an orthonormal basis of `ℝ^ι`, for an arbitrary finite index type. -/
noncomputable def rotateι (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (x : ι → ℝ) : ι → ℝ :=
  fun j ↦ ∑ i, b j i * x i

/-- The coordinate map `rotateι b` is the basis representation, read on plain functions. -/
lemma rotateι_eq (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (x : ι → ℝ) :
    rotateι b x = WithLp.ofLp (b.repr (WithLp.toLp 2 x)) := by
  ext j
  simp [rotateι, OrthonormalBasis.repr_apply_apply, PiLp.inner_apply, mul_comm]

/-- The coordinate map `rotateι b` is measurable. -/
@[fun_prop]
lemma measurable_rotateι (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    Measurable (rotateι b) := by
  unfold rotateι; fun_prop

/-- Changing to any orthonormal basis preserves the product of standard normal laws on `ℝ^ι`. -/
lemma map_rotateι_pi (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (rotateι b) =
      Measure.pi fun _ : ι ↦ gaussianReal 0 1 := by
  have hf : rotateι b = WithLp.ofLp ∘ b.repr ∘ WithLp.toLp 2 := funext (rotateι_eq b)
  have h1 : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) := by fun_prop
  have h2 : Measurable (b.repr : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    b.repr.continuous.measurable
  have h3 : Measurable (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ)) := by fun_prop
  rw [hf, ← Measure.map_map h3 (h2.comp h1), ← Measure.map_map h2 h1, map_pi_eq_stdGaussian,
    stdGaussian_map b.repr, ← map_pi_eq_stdGaussian, Measure.map_map h3 h1]
  exact Measure.map_id

/-- The sum of squares of the coordinates in an orthonormal basis equals the sum of squares of the vector. -/
lemma sum_sq_rotateι (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (x : ι → ℝ) :
    ∑ j, rotateι b x j ^ 2 = ∑ i, x i ^ 2 := by
  have h := b.repr.norm_map (WithLp.toLp 2 x)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq] at h
  rw [rotateι_eq]
  simpa using h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Independent standard normal variables indexed by a finite type stay independent standard normal after
taking coordinates in an orthonormal basis. -/
theorem iIndepFun_rotateι [DecidableEq ι] [IsProbabilityMeasure P] {Z : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (Z i))
    (hind : iIndepFun Z P) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    iIndepFun (fun j ω ↦ rotateι b (fun i ↦ Z i ω) j) P ∧
      ∀ j, HasLaw (fun ω ↦ rotateι b (fun i ↦ Z i ω) j) (gaussianReal 0 1) P := by
  have hZm : Measurable fun ω i ↦ Z i ω := Measurable.of_eval hmeas
  have hZv : P.map (fun ω i ↦ Z i ω) = Measure.pi fun _ : ι ↦ gaussianReal 0 1 := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hmeas i).aemeasurable).1 hind]
    congr
    funext i
    exact (hZ i).map_eq
  have hWv : P.map (fun ω ↦ rotateι b (fun i ↦ Z i ω)) = Measure.pi fun _ : ι ↦ gaussianReal 0 1 := by
    rw [← map_rotateι_pi b, ← hZv, Measure.map_map (measurable_rotateι b) hZm]
    rfl
  have hWj : ∀ j, HasLaw (fun ω ↦ rotateι b (fun i ↦ Z i ω) j) (gaussianReal 0 1) P := by
    intro j
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω ↦ rotateι b (fun i ↦ Z i ω) j) =
        Function.eval j ∘ fun ω ↦ rotateι b (fun i ↦ Z i ω) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (by fun_prop), hWv, Measure.pi_map_eval]
    simp
  refine ⟨(iIndepFun_iff_map_fun_eq_pi_map fun j ↦ (hWj j).aemeasurable).2 ?_, hWj⟩
  rw [hWv]
  congr
  funext j
  exact (hWj j).map_eq.symm

end RotationGeneral

/-! ### The tensor basis -/

section Tensor

variable {r c : ℕ}

/-- The inner product of two basis vectors of an orthonormal basis, written as a sum of products. -/
lemma sum_basis_mul_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (i j : ι) :
    ∑ x, A i x * A j x = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.1 A.orthonormal i j
  simpa [PiLp.inner_apply, mul_comm] using h

/-- The product vectors `(i, j) ↦ A i' i * B j' j` indexed by pairs `(i', j')`. -/
noncomputable def tensorFamily (A : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)))
    (B : OrthonormalBasis (Fin c) ℝ (EuclideanSpace ℝ (Fin c))) (p : Fin r × Fin c) :
    EuclideanSpace ℝ (Fin r × Fin c) :=
  WithLp.toLp 2 fun q ↦ A p.1 q.1 * B p.2 q.2

/-- The tensor family of two orthonormal bases is orthonormal. -/
lemma orthonormal_tensorFamily (A : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)))
    (B : OrthonormalBasis (Fin c) ℝ (EuclideanSpace ℝ (Fin c))) :
    Orthonormal ℝ (tensorFamily A B) := by
  rw [orthonormal_iff_ite]
  intro p q
  have key : inner ℝ (tensorFamily A B p) (tensorFamily A B q) =
      (∑ i, A p.1 i * A q.1 i) * ∑ j, B p.2 j * B q.2 j := by
    simp only [tensorFamily, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [key, sum_basis_mul_basis, sum_basis_mul_basis]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

/-- Two orthonormal bases of `ℝʳ` and `ℝᶜ` give an orthonormal basis of `ℝ^(r × c)` of product vectors. -/
lemma exists_tensorBasis (A : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)))
    (B : OrthonormalBasis (Fin c) ℝ (EuclideanSpace ℝ (Fin c))) (hr : 0 < r) (hc : 0 < c) :
    ∃ T : OrthonormalBasis (Fin r × Fin c) ℝ (EuclideanSpace ℝ (Fin r × Fin c)),
      ∀ p, T p = tensorFamily A B p := by
  have : Nonempty (Fin r × Fin c) := ⟨(⟨0, hr⟩, ⟨0, hc⟩)⟩
  have hon := orthonormal_tensorFamily A B
  let bs := basisOfOrthonormalOfCardEqFinrank hon (by simp)
  have hbs : (bs : Fin r × Fin c → EuclideanSpace ℝ (Fin r × Fin c)) = tensorFamily A B :=
    coe_basisOfOrthonormalOfCardEqFinrank hon _
  refine ⟨bs.toOrthonormalBasis (by rw [hbs]; exact hon), fun p ↦ ?_⟩
  rw [Module.Basis.coe_toOrthonormalBasis, hbs]

end Tensor

/-! ### The double projection -/

/-- The double projection of a table `z` (rows orthogonal to `α`, columns orthogonal to `β`). -/
noncomputable def tableProj {r c : ℕ} (α : Fin r → ℝ) (β : Fin c → ℝ) (z : Fin r × Fin c → ℝ) (i : Fin r)
    (j : Fin c) : ℝ :=
  z (i, j) - β j * ∑ l, β l * z (i, l) - α i * ∑ k, α k * z (k, j) +
    α i * β j * ∑ k, ∑ l, α k * β l * z (k, l)

section Coordinates

variable {r c : ℕ}

/-- The coordinate of a table in the tensor basis: `∑ᵢ ∑ⱼ Aᵢ'ᵢ Bⱼ'ⱼ z(i, j)`. -/
noncomputable def tableCoord (A : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)))
    (B : OrthonormalBasis (Fin c) ℝ (EuclideanSpace ℝ (Fin c))) (z : Fin r × Fin c → ℝ) (i' : Fin r)
    (j' : Fin c) : ℝ :=
  ∑ i, ∑ j, A i' i * B j' j * z (i, j)

/-- The tensor-basis coordinate of a table, as `rotateι` of the tensor basis. -/
lemma rotateι_tensor {T : OrthonormalBasis (Fin r × Fin c) ℝ (EuclideanSpace ℝ (Fin r × Fin c))}
    {A : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))}
    {B : OrthonormalBasis (Fin c) ℝ (EuclideanSpace ℝ (Fin c))} (hT : ∀ p, T p = tensorFamily A B p)
    (y : Fin r × Fin c → ℝ) (p : Fin r × Fin c) :
    rotateι T y p = ∑ i, ∑ j, A p.1 i * B p.2 j * y (i, j) := by
  simp only [rotateι, hT, tensorFamily, Fintype.sum_prod_type]

/-- In the tensor basis the double projection of a table has coordinates
`z̃(i',j') - b z̃(i',j₀) - a z̃(i₀,j') + a b z̃(i₀,j₀)`, where `a = ⟨Aᵢ', α⟩` and `b = ⟨Bⱼ', β⟩`. -/
lemma tableCoord_tableProj {i₀ : Fin r} {j₀ : Fin c}
    {A : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))}
    {B : OrthonormalBasis (Fin c) ℝ (EuclideanSpace ℝ (Fin c))} {α : Fin r → ℝ} {β : Fin c → ℝ}
    (hA : ∀ i, A i₀ i = α i) (hB : ∀ j, B j₀ j = β j) (z : Fin r × Fin c → ℝ) (i' : Fin r) (j' : Fin c) :
    tableCoord A B (fun q ↦ tableProj α β z q.1 q.2) i' j' =
      tableCoord A B z i' j' - (∑ j, B j' j * β j) * tableCoord A B z i' j₀ -
        (∑ i, A i' i * α i) * tableCoord A B z i₀ j' +
        (∑ i, A i' i * α i) * (∑ j, B j' j * β j) * tableCoord A B z i₀ j₀ := by
  set a := ∑ i, A i' i * α i with ha
  set b := ∑ j, B j' j * β j with hb
  have c1 : tableCoord A B z i' j₀ = ∑ i, ∑ j, A i' i * β j * z (i, j) := by
    simp only [tableCoord, hB]
  have c2 : tableCoord A B z i₀ j' = ∑ i, ∑ j, α i * B j' j * z (i, j) := by
    simp only [tableCoord, hA]
  have c3 : tableCoord A B z i₀ j₀ = ∑ k, ∑ l, α k * β l * z (k, l) := by
    simp only [tableCoord, hA, hB]
  have e1 : ∑ i, ∑ j, A i' i * B j' j * (β j * ∑ l, β l * z (i, l)) =
      b * ∑ i, ∑ j, A i' i * β j * z (i, j) := by
    calc ∑ i, ∑ j, A i' i * B j' j * (β j * ∑ l, β l * z (i, l))
        = ∑ i, ∑ j, (B j' j * β j) * (A i' i * ∑ l, β l * z (i, l)) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ i, b * (A i' i * ∑ l, β l * z (i, l)) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.sum_mul]
      _ = b * ∑ i, ∑ j, A i' i * β j * z (i, j) := by
          rw [← Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
  have e2 : ∑ i, ∑ j, A i' i * B j' j * (α i * ∑ k, α k * z (k, j)) =
      a * ∑ i, ∑ j, α i * B j' j * z (i, j) := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, A i' i * B j' j * (α i * ∑ k, α k * z (k, j))
        = ∑ j, ∑ i, (A i' i * α i) * (B j' j * ∑ k, α k * z (k, j)) :=
          Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
      _ = ∑ j, a * (B j' j * ∑ k, α k * z (k, j)) :=
          Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.sum_mul]
      _ = a * ∑ j, ∑ i, α i * B j' j * z (i, j) := by
          rw [← Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ = a * ∑ i, ∑ j, α i * B j' j * z (i, j) := by rw [Finset.sum_comm]
  have e3 : ∑ i, ∑ j, A i' i * B j' j * (α i * β j * ∑ k, ∑ l, α k * β l * z (k, l)) =
      a * b * ∑ k, ∑ l, α k * β l * z (k, l) := by
    set K := ∑ k, ∑ l, α k * β l * z (k, l)
    calc ∑ i, ∑ j, A i' i * B j' j * (α i * β j * K)
        = ∑ i, ∑ j, (A i' i * α i) * ((B j' j * β j) * K) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ i, (A i' i * α i) * (b * K) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = a * b * K := by rw [← Finset.sum_mul]; ring
  rw [c1, c2, c3, ← e1, ← e2, ← e3]
  simp only [tableCoord, tableProj, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The inner products `a = ⟨Aᵢ', Aᵢ₀⟩` of an orthonormal basis, as `0` or `1`. -/
lemma sum_basis_mul_eq {n : ℕ} (A : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i₀ i' : Fin n)
    {α : Fin n → ℝ} (hA : ∀ i, A i₀ i = α i) :
    ∑ i, A i' i * α i = if i' = i₀ then 1 else 0 := by
  simp only [← hA]
  exact sum_basis_mul_basis A i' i₀

end Coordinates

/-! ### The chi-square law of the double projection -/

/-- **The double projection of a Gaussian table is chi-square.** If `Z` is an `r × c` table of independent
standard normal entries (`r, c ≥ 2`) and `α ∈ ℝʳ`, `β ∈ ℝᶜ` are unit vectors, then the squared Frobenius norm of
the double projection `(I - ααᵀ) Z (I - ββᵀ)` has the chi-square law with `(r - 1)(c - 1)` degrees of freedom. -/
theorem hasLaw_tableProj_chiSquared {r c : ℕ} (hr : 2 ≤ r) (hc : 2 ≤ c) (α : Fin r → ℝ) (β : Fin c → ℝ)
    (hα : ∑ i, α i ^ 2 = 1) (hβ : ∑ j, β j ^ 2 = 1) :
    HasLaw (fun z : Fin r × Fin c → ℝ ↦ ∑ i, ∑ j, tableProj α β z i j ^ 2)
      (chiSquared (((r : ℝ) - 1) * ((c : ℝ) - 1))) (Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1) := by
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  set j₀ : Fin c := ⟨0, by omega⟩ with hj₀
  have hnα : ‖(WithLp.toLp 2 α : EuclideanSpace ℝ (Fin r))‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq]
    simpa using hα
  have hnβ : ‖(WithLp.toLp 2 β : EuclideanSpace ℝ (Fin c))‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq]
    simpa using hβ
  obtain ⟨A, hA'⟩ := exists_orthonormalBasis_eq i₀ _ hnα
  obtain ⟨B, hB'⟩ := exists_orthonormalBasis_eq j₀ _ hnβ
  have hA : ∀ i, A i₀ i = α i := fun i ↦ by rw [hA']
  have hB : ∀ j, B j₀ j = β j := fun j ↦ by rw [hB']
  obtain ⟨T, hT⟩ := exists_tensorBasis A B (by omega) (by omega)
  -- the rotated coordinates are independent standard normal
  set P : Measure (Fin r × Fin c → ℝ) := Measure.pi fun _ : Fin r × Fin c ↦ gaussianReal 0 1 with hP
  have hZm : ∀ p, Measurable fun z : Fin r × Fin c → ℝ ↦ z p := fun p ↦ measurable_pi_apply p
  have hZind : iIndepFun (fun p (z : Fin r × Fin c → ℝ) ↦ z p) P :=
    iIndepFun_pi (X := fun _ x ↦ x) fun _ ↦ aemeasurable_id
  have hZlaw : ∀ p, HasLaw (fun z : Fin r × Fin c → ℝ ↦ z p) (gaussianReal 0 1) P :=
    fun p ↦ ⟨(hZm p).aemeasurable, (measurePreserving_eval _ p).map_eq⟩
  obtain ⟨hWind, hWlaw⟩ := iIndepFun_rotateι hZm hZind hZlaw T
  set S : Finset (Fin r × Fin c) := (univ.erase i₀) ×ˢ (univ.erase j₀) with hS
  have hne : S.Nonempty :=
    ⟨(⟨1, by omega⟩, ⟨1, by omega⟩), by simp [hS, hi₀, hj₀, Fin.ext_iff]⟩
  have hchi := hasLaw_sum_sq_chiSquared hne (Z := fun p z ↦ rotateι T z p)
    (fun p ↦ by fun_prop) hWind fun p _ ↦ hWlaw p
  have hcard : (S.card : ℝ) = ((r : ℝ) - 1) * ((c : ℝ) - 1) := by
    rw [hS, Finset.card_product, card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_univ _),
      card_univ, card_univ, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul, Nat.cast_sub (by omega),
      Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcard] at hchi
  convert hchi using 1
  funext z
  -- Parseval in the tensor basis
  have hpars := sum_sq_rotateι T (fun q ↦ tableProj α β z q.1 q.2)
  have hL : ∑ i, ∑ j, tableProj α β z i j ^ 2 = ∑ q : Fin r × Fin c, tableProj α β z q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type fun q : Fin r × Fin c ↦ tableProj α β z q.1 q.2 ^ 2).symm
  have hc : ∀ i' j', tableCoord A B z i' j' = rotateι T z (i', j') := fun i' j' ↦
    (rotateι_tensor hT z (i', j')).symm
  have hcoord : ∀ p, rotateι T (fun q ↦ tableProj α β z q.1 q.2) p =
      if p ∈ S then rotateι T z p else 0 := by
    intro p
    have h1 : rotateι T (fun q ↦ tableProj α β z q.1 q.2) p =
        tableCoord A B (fun q ↦ tableProj α β z q.1 q.2) p.1 p.2 := by
      rw [rotateι_tensor hT]
      rfl
    have h3 := tableCoord_tableProj hA hB z p.1 p.2
    rw [sum_basis_mul_eq A i₀ p.1 hA, sum_basis_mul_eq B j₀ p.2 hB, hc, hc, hc, hc] at h3
    rw [h1, h3]
    by_cases h1 : p.1 = i₀ <;> by_cases h2 : p.2 = j₀
    · have : p = (i₀, j₀) := Prod.ext h1 h2
      subst this
      simp [hS]
    · simp [hS, h1, h2]
    · simp [hS, h1, h2]
    · simp [hS, h1, h2]
  rw [hL, ← hpars]
  rw [← Finset.sum_subset (Finset.subset_univ S) (f := fun p ↦ rotateι T (fun q ↦ tableProj α β z q.1 q.2) p ^ 2)
    (fun p _ hp ↦ by simp [hcoord p, hp])]
  exact Finset.sum_congr rfl fun p hp ↦ by simp [hcoord p, hp]

end UndergradKB.Statistics
