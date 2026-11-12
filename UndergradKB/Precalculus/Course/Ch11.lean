import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Basic.Real.Basic
import UndergradKB.Common.Attr

/-!
# Course layer, Chapter 11 (applications of trigonometry)

Thin theorems in the book's terms: law of sines and cosines, polar coordinates, complex numbers in
polar form, roots, and plane vectors (as pairs of reals and as `EuclideanSpace ℝ (Fin 2)`).
-/

namespace UndergradKB.Precalculus.Course

open Complex EuclideanGeometry InnerProductGeometry

private theorem cis_eq_exp_aux (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I = Complex.exp (θ * I) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- Law of Sines: in triangle `ABC` with `a = |BC|`, `b = |CA|`, `c = |AB|` and angles `α`, `β`,
`γ` at `A`, `B`, `C`, we have `sin β / b = sin α / a`, and cyclically `sin γ / c = sin β / b`
(PC-243). -/
@[kb "stitzzeager2013" "Theorem 11.2, p. 909"]
theorem thm_11_2_law_of_sines (A B C : EuclideanSpace ℝ (Fin 2)) (hBC : B ≠ C) (hCA : C ≠ A)
    (hAB : A ≠ B) :
    Real.sin (∠ A B C) / dist C A = Real.sin (∠ C A B) / dist B C ∧
      Real.sin (∠ B C A) / dist A B = Real.sin (∠ A B C) / dist C A := by
  refine ⟨EuclideanGeometry.sin_angle_div_dist_eq_sin_angle_div_dist hBC hCA, ?_⟩
  exact EuclideanGeometry.sin_angle_div_dist_eq_sin_angle_div_dist hCA hAB

/-- Law of Cosines: `b² = a² + c² - 2ac cos β`, written for the triangle `ABC` with the angle at
`B`: `|AC|² = |AB|² + |CB|² - 2 |AB| |CB| cos ∠ABC` (PC-246). -/
@[kb "stitzzeager2013" "Theorem 11.5, p. 922"]
theorem thm_11_5_law_of_cosines (A B C : EuclideanSpace ℝ (Fin 2)) :
    dist A C ^ 2 = dist A B ^ 2 + dist C B ^ 2 - 2 * dist A B * dist C B * Real.cos (∠ A B C) :=
  by rw [sq, sq, sq]; exact EuclideanGeometry.law_cos A B C

/-- Polar to rectangular: a point with polar coordinates `(r, θ)` has rectangular coordinates
`(r cos θ, r sin θ)` (PC-250). -/
@[kb "stitzzeager2013" "Theorem 11.7, p. 936"]
theorem thm_11_7_polar_to_rectangular (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = r * (Real.cos θ + Real.sin θ * I) :=
  Complex.polarCoord_symm_apply (r, θ)

/-- Polar to rectangular for a complex number with modulus `‖z‖` and principal argument:
`Re z = ‖z‖ cos (arg z)` and `Im z = ‖z‖ sin (arg z)` (PC-250). -/
@[kb "stitzzeager2013" "Theorem 11.7, p. 936"]
theorem thm_11_7_polar_to_rectangular_complex (z : ℂ) :
    z.re = ‖z‖ * Real.cos (Complex.arg z) ∧ z.im = ‖z‖ * Real.sin (Complex.arg z) :=
  ⟨(Complex.norm_mul_cos_arg z).symm, (Complex.norm_mul_sin_arg z).symm⟩

/-- Rectangular to polar: `x² + y² = r²`, and `tan θ = y / x` for the principal argument
(PC-251). -/
@[kb "stitzzeager2013" "Theorem 11.7, p. 936"]
theorem thm_11_7_rectangular_to_polar (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 ∧ Real.tan (Complex.arg z) = z.im / z.re := by
  refine ⟨?_, Complex.tan_arg z⟩
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Modulus: `|z|` is nonnegative, zero exactly at `0`, equals `√(Re² + Im²)`, and is
multiplicative on products, powers and quotients (PC-261). -/
@[kb "stitzzeager2013" "Theorem 11.14, p. 1005"]
theorem thm_11_14_modulus (z w : ℂ) (n : ℕ) :
    0 ≤ ‖z‖ ∧ (‖z‖ = 0 ↔ z = 0) ∧ ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) ∧ ‖z * w‖ = ‖z‖ * ‖w‖ ∧
      ‖z ^ n‖ = ‖z‖ ^ n ∧ ‖z / w‖ = ‖z‖ / ‖w‖ := by
  refine ⟨norm_nonneg z, norm_eq_zero, ?_, Complex.norm_mul z w, Complex.norm_pow z n,
    Complex.norm_div z w⟩
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  ring

/-- Polar form: `z = |z| (cos θ + i sin θ)` for the principal argument `θ` of `z` (PC-263). -/
@[kb "stitzzeager2013" "Definition 11.3, p. 1007"]
theorem def_11_3_polar_form (z : ℂ) :
    z = ‖z‖ * (Real.cos (Complex.arg z) + Real.sin (Complex.arg z) * I) := by
  rw [cis_eq_exp_aux, Complex.norm_mul_exp_arg_mul_I]

/-- Product in polar form: multiply the moduli and add the arguments (PC-264). -/
@[kb "stitzzeager2013" "Theorem 11.16, p. 1009"]
theorem thm_11_16_product_polar (r s α β : ℝ) :
    ((r : ℂ) * (Real.cos α + Real.sin α * I)) * ((s : ℂ) * (Real.cos β + Real.sin β * I)) =
      ((r * s : ℝ) : ℂ) * (Real.cos (α + β) + Real.sin (α + β) * I) := by
  rw [cis_eq_exp_aux, cis_eq_exp_aux, cis_eq_exp_aux, Complex.ofReal_add, add_mul,
    Complex.exp_add, Complex.ofReal_mul]
  ring

/-- De Moivre's Theorem: `(r (cos θ + i sin θ))ⁿ = rⁿ (cos nθ + i sin nθ)` (PC-265). -/
@[kb "stitzzeager2013" "Theorem 11.16, p. 1009"]
theorem thm_11_16_de_moivre (r θ : ℝ) (n : ℕ) :
    ((r : ℂ) * (Real.cos θ + Real.sin θ * I)) ^ n =
      ((r ^ n : ℝ) : ℂ) * (Real.cos (n * θ) + Real.sin (n * θ) * I) := by
  rw [mul_pow, Complex.ofReal_pow, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_cos,
    Complex.ofReal_sin, Complex.cos_add_sin_mul_I_pow]
  push_cast
  rfl

/-- Quotient in polar form: divide the moduli and subtract the arguments, for `s ≠ 0`
(PC-266). -/
@[kb "stitzzeager2013" "Theorem 11.16, p. 1009"]
theorem thm_11_16_quotient_polar (r s α β : ℝ) (hs : s ≠ 0) :
    ((r : ℂ) * (Real.cos α + Real.sin α * I)) / ((s : ℂ) * (Real.cos β + Real.sin β * I)) =
      ((r / s : ℝ) : ℂ) * (Real.cos (α - β) + Real.sin (α - β) * I) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  rw [cis_eq_exp_aux, cis_eq_exp_aux, cis_eq_exp_aux, Complex.ofReal_sub, sub_mul,
    Complex.exp_sub, Complex.ofReal_div]
  have := Complex.exp_ne_zero (β * I)
  field_simp

/-- An `n`th root of `z` is any `w` with `wⁿ = z` (PC-267). -/
@[kb "stitzzeager2013" "Definition 11.4, p. 1012"]
theorem def_11_4_nth_root (n : ℕ) (hn : 0 < n) (z w : ℂ) :
    w ∈ Polynomial.nthRoots n z ↔ w ^ n = z :=
  Polynomial.mem_nthRoots hn

/-- The explicit `n`th roots of `z`: for each integer `k`, the number
`‖z‖^(1/n) (cos φ + i sin φ)` with `φ = (arg z + 2πk) / n` has `n`th power `z` (PC-268). -/
@[kb "stitzzeager2013" "Theorem 11.17, p. 1013"]
theorem thm_11_17_explicit_roots (z : ℂ) (n : ℕ) (hn : n ≠ 0) (k : ℤ) :
    (((‖z‖ ^ (1 / (n : ℝ)) : ℝ) : ℂ) *
      (Real.cos ((Complex.arg z + 2 * Real.pi * k) / n) +
        Real.sin ((Complex.arg z + 2 * Real.pi * k) / n) * I)) ^ n = z := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnφ : (n : ℝ) * ((Complex.arg z + 2 * Real.pi * k) / n) =
      Complex.arg z + k * (2 * Real.pi) := by
    field_simp
  rw [thm_11_16_de_moivre, hnφ, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z), one_div, inv_mul_cancel₀ hn',
    Real.rpow_one]
  exact (def_11_3_polar_form z).symm

/-- A nonzero complex number has exactly `n` distinct `n`th roots (PC-268). -/
@[kb "stitzzeager2013" "Theorem 11.17, p. 1013"]
theorem thm_11_17_number_of_roots (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    Multiset.card (Polynomial.nthRoots n z) = n ∧ (Polynomial.nthRoots n z).Nodup := by
  have hprim := Complex.isPrimitiveRoot_exp n hn
  refine ⟨?_, hprim.nthRoots_nodup hz⟩
  have h : ∃ α : ℂ, α ^ n = z := ⟨_, thm_11_17_explicit_roots z n hn 0⟩
  rw [hprim.card_nthRoots]
  simp only [eq_true h, ite_true]

/-- The `n`th roots of unity are the `n` solutions of `zⁿ = 1`; there are exactly `n` of them
(PC-269). -/
@[kb "stitzzeager2013" "§11.7, p. 1018"]
theorem box_11_7_roots_of_unity (n : ℕ) (hn : n ≠ 0) :
    Nat.card (rootsOfUnity n ℂ) = n ∧ IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / n)) n := by
  have : NeZero n := ⟨hn⟩
  exact ⟨Complex.card_rootsOfUnity n, Complex.isPrimitiveRoot_exp n hn⟩

/-- The vector from `P(x₀, y₀)` to `Q(x₁, y₁)` has components `⟨x₁ - x₀, y₁ - y₀⟩`, and two
vectors are equal iff their components are (PC-270). -/
@[kb "stitzzeager2013" "Definition 11.5, p. 1025"]
theorem def_11_5_component_form (P Q v w : ℝ × ℝ) :
    Q -ᵥ P = (Q.1 - P.1, Q.2 - P.2) ∧ (v = w ↔ v.1 = w.1 ∧ v.2 = w.2) :=
  ⟨rfl, Prod.ext_iff⟩

/-- Vector sum is componentwise (PC-271). -/
@[kb "stitzzeager2013" "Definition 11.6, p. 1026"]
theorem def_11_6_vector_sum (v₁ v₂ w₁ w₂ : ℝ) :
    ((v₁, v₂) + (w₁, w₂) : ℝ × ℝ) = (v₁ + w₁, v₂ + w₂) :=
  rfl

/-- Properties of vector addition: commutative, associative, `0` is an identity, and `v + (-v) = 0`
(PC-272). -/
@[kb "stitzzeager2013" "Theorem 11.18, p. 1027"]
theorem thm_11_18_vector_addition (u v w : ℝ × ℝ) :
    u + v = v + u ∧ (u + v) + w = u + (v + w) ∧ v + 0 = v ∧ 0 + v = v ∧ v + -v = 0 :=
  ⟨add_comm u v, add_assoc u v w, add_zero v, zero_add v, add_neg_cancel v⟩

/-- Scalar multiple is componentwise (PC-273). -/
@[kb "stitzzeager2013" "Definition 11.7, p. 1029"]
theorem def_11_7_scalar_multiple (k v₁ v₂ : ℝ) : k • ((v₁, v₂) : ℝ × ℝ) = (k * v₁, k * v₂) :=
  rfl

/-- Properties of scalar multiplication of vectors (PC-274). -/
@[kb "stitzzeager2013" "Theorem 11.19, p. 1030"]
theorem thm_11_19_scalar_multiplication (k r : ℝ) (v w : ℝ × ℝ) :
    (k * r) • v = k • r • v ∧ (1 : ℝ) • v = v ∧ -v = (-1 : ℝ) • v ∧
      (k + r) • v = k • v + r • v ∧ k • (v + w) = k • v + k • w ∧ (0 : ℝ) • v = 0 :=
  ⟨mul_smul k r v, one_smul ℝ v, (neg_one_smul ℝ v).symm, add_smul k r v, smul_add k v w,
    zero_smul ℝ v⟩

/-- The magnitude `‖v‖` is nonnegative, vanishes only at the zero vector, and scales by `|k|`;
every vector is its magnitude times its direction (PC-276). -/
@[kb "stitzzeager2013" "Theorem 11.20, p. 1032"]
theorem thm_11_20_magnitude (v : EuclideanSpace ℝ (Fin 2)) (k : ℝ) :
    0 ≤ ‖v‖ ∧ (‖v‖ = 0 ↔ v = 0) ∧ ‖k • v‖ = |k| * ‖v‖ ∧ ‖v‖ • NormedSpace.normalize v = v :=
  ⟨norm_nonneg v, norm_eq_zero, by rw [norm_smul, Real.norm_eq_abs],
    NormedSpace.norm_smul_normalize v⟩

/-- Normalizing a nonzero vector gives a unit vector (PC-277). -/
@[kb "stitzzeager2013" "Definition 11.9, p. 1035"]
theorem def_11_9_unit_vector (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) :
    ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 :=
  norm_smul_inv_norm hv

/-- The principal unit vectors `î = ⟨1, 0⟩` and `ĵ = ⟨0, 1⟩` (PC-278). -/
@[kb "stitzzeager2013" "Definition 11.10, p. 1036"]
theorem def_11_10_principal_unit_vectors :
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 0 = 1 ∧ EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 1 = 0) ∧
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ) 0 = 0 ∧ EuclideanSpace.single (1 : Fin 2) (1 : ℝ) 1 = 1) ∧
      ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ = 1 ∧ ‖EuclideanSpace.single (1 : Fin 2) (1 : ℝ)‖ = 1 := by
  simp

/-- Principal decomposition: `v = v₁ î + v₂ ĵ` (PC-279). -/
@[kb "stitzzeager2013" "Theorem 11.21, p. 1036"]
theorem thm_11_21_principal_decomposition (v : EuclideanSpace ℝ (Fin 2)) :
    v = v 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      v 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

/-- Dot product in components: `⟨v₁, v₂⟩ · ⟨w₁, w₂⟩ = v₁ w₁ + v₂ w₂` (PC-280). -/
@[kb "stitzzeager2013" "Definition 11.11, p. 1046"]
theorem def_11_11_dot_product (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Properties of the dot product (PC-281). -/
@[kb "stitzzeager2013" "Theorem 11.22, p. 1046"]
theorem thm_11_22_dot_product_properties (u v w : EuclideanSpace ℝ (Fin 2)) (k : ℝ) :
    inner ℝ v w = inner ℝ w v ∧ inner ℝ u (v + w) = inner ℝ u v + inner ℝ u w ∧
      inner ℝ (k • v) w = k * inner ℝ v w ∧ inner ℝ v v = ‖v‖ ^ 2 ∧ inner ℝ (0 : EuclideanSpace ℝ (Fin 2)) v = 0 :=
  ⟨real_inner_comm w v, inner_add_right u v w, real_inner_smul_left v w k,
    real_inner_self_eq_norm_sq v, inner_zero_left v⟩

/-- `‖v - w‖² = ‖v‖² - 2 v·w + ‖w‖²` (PC-282). -/
@[kb "stitzzeager2013" "Example 11.9.1, p. 1047"]
theorem ex_11_9_1_norm_sub_sq (v w : EuclideanSpace ℝ (Fin 2)) :
    ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 :=
  norm_sub_sq_real v w

/-- The dot product in terms of the angle: `v·w = ‖v‖‖w‖ cos θ` (PC-283). -/
@[kb "stitzzeager2013" "Theorem 11.23, p. 1047"]
theorem thm_11_23_dot_product_angle (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = ‖v‖ * ‖w‖ * Real.cos (InnerProductGeometry.angle v w) := by
  rw [mul_comm, InnerProductGeometry.cos_angle_mul_norm_mul_norm]

/-- The angle between nonzero vectors is `arccos (v·w / (‖v‖‖w‖))` (PC-284). -/
@[kb "stitzzeager2013" "Theorem 11.24, p. 1048"]
theorem thm_11_24_angle_between_vectors (v w : EuclideanSpace ℝ (Fin 2)) :
    InnerProductGeometry.angle v w = Real.arccos (inner ℝ v w / (‖v‖ * ‖w‖)) :=
  rfl

/-- Two vectors are orthogonal iff their dot product is zero, i.e. iff the angle between them is
`π / 2` (PC-285). -/
@[kb "stitzzeager2013" "Theorem 11.25, p. 1049"]
theorem thm_11_25_orthogonal_iff_dot_zero (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = 0 ↔ InnerProductGeometry.angle v w = Real.pi / 2 :=
  InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two v w

/-- Projection of `v` onto `w`: `proj_w v = (v·w / ‖w‖²) w` (PC-288). -/
@[kb "stitzzeager2013" "Theorem 11.26, p. 1051"]
theorem thm_11_26_projection (v w : EuclideanSpace ℝ (Fin 2)) :
    (Submodule.span ℝ {w}).starProjection v = (inner ℝ w v / ‖w‖ ^ 2) • w := by
  rw [Submodule.starProjection_singleton]
  simp

end UndergradKB.Precalculus.Course
