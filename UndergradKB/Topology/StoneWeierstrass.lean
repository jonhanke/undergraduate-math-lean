import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Fourier.AddCircle
import UndergradKB.Common.Attr

/-!
# The Stone-Weierstrass theorem (Morris, Topology Without Tears, section 12.2)

Converse direction (a dense set separates points), the book's notions of algebra and Banach algebra,
the lattice lemma, the real and complex Stone-Weierstrass theorems in the book's form (closed
subalgebras containing a nonzero constant), and trigonometric polynomials.
-/

namespace UndergradKB.Topology

open Set

section Converse

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] {𝕜 : Type*} [RCLike 𝕜]

/-- Morris, Topology Without Tears, Proposition 12.2.3 (TP-345). If `S` is dense in `C(X, F)` for
the sup metric (`X` compact Hausdorff, `F = ℝ` or `ℂ`, here any `RCLike` field), then `S` separates
the points of `X`. -/
@[kb "morris2024" "Proposition 12.2.3, p. 376"]
theorem separatesPoints_of_dense (S : Set C(X, 𝕜)) (hS : Dense S) :
    Set.SeparatesPoints ((fun f : C(X, 𝕜) => (f : X → 𝕜)) '' S) := by
  intro a b hab
  by_contra hcon
  push Not at hcon
  obtain ⟨f, hfa, hfb, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := a)) (isClosed_singleton (x := b)) (disjoint_singleton.2 hab)
  let g : C(X, 𝕜) := ⟨fun x => ((f x : ℝ) : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩
  obtain ⟨φ, hφS, hφ⟩ := hS.exists_dist_lt g (show (0 : ℝ) < 1 / 3 by norm_num)
  have h1 := (ContinuousMap.dist_apply_le_dist (f := g) (g := φ) a).trans_lt hφ
  have h2 := (ContinuousMap.dist_apply_le_dist (f := g) (g := φ) b).trans_lt hφ
  have hφab : φ a = φ b := hcon _ ⟨φ, hφS, rfl⟩
  have hga : g a = 0 := by simp [g, show f a = 0 from hfa rfl]
  have hgb : g b = 1 := by simp [g, show f b = 1 from hfb rfl]
  rw [hga] at h1
  rw [hgb] at h2
  have : dist (0 : 𝕜) 1 < 2 / 3 := by
    calc dist (0 : 𝕜) 1 ≤ dist 0 (φ a) + dist (φ a) 1 := dist_triangle _ _ _
      _ = dist 0 (φ a) + dist 1 (φ b) := by rw [hφab, dist_comm (φ b) 1]
      _ < 1 / 3 + 1 / 3 := add_lt_add h1 h2
      _ = 2 / 3 := by norm_num
  rw [dist_zero_left, norm_one] at this
  linarith

end Converse

section Algebras

/-- Bridging notion for Morris, Topology Without Tears, Definition 12.2.4: a multiplication on the
vector space `A` over `F` satisfying the three laws of the book (distributivity on both sides and
`(αx)(βy) = (αβ)(xy)`); associativity and a unit are not required. -/
structure IsAlgebraMul (F A : Type*) [Semiring F] [AddCommMonoid A] [Module F A] [Mul A] :
    Prop where
  add_mul : ∀ x y z : A, (x + y) * z = x * z + y * z
  mul_add : ∀ x y z : A, x * (y + z) = x * y + x * z
  smul_mul_smul : ∀ (α β : F) (x y : A), (α • x) * (β • y) = (α * β) • (x * y)

/-- Morris, Topology Without Tears, Definition 12.2.4 (TP-346). A multiplication satisfying the book's
laws is the same thing as a bilinear map `A × A → A`. -/
@[kb "morris2024" "Definition 12.2.4, p. 377"]
theorem isAlgebraMul_iff_exists_bilinear (F A : Type*) [CommSemiring F] [AddCommMonoid A]
    [Module F A] [Mul A] :
    IsAlgebraMul F A ↔ ∃ B : A →ₗ[F] A →ₗ[F] A, ∀ x y, B x y = x * y := by
  constructor
  · intro h
    refine ⟨LinearMap.mk₂ F (· * ·) h.add_mul ?_ h.mul_add ?_, fun x y => rfl⟩
    · intro c x y
      simpa using h.smul_mul_smul c 1 x y
    · intro c x y
      simpa using h.smul_mul_smul 1 c x y
  · rintro ⟨B, hB⟩
    refine ⟨fun x y z => ?_, fun x y z => ?_, fun α β x y => ?_⟩
    · rw [← hB, ← hB, ← hB, map_add, LinearMap.add_apply]
    · rw [← hB, ← hB, ← hB, map_add]
    · rw [← hB, ← hB]
      simp only [map_smul, LinearMap.smul_apply, smul_smul]
      rw [mul_comm]

/-- Every non-unital non-associative `F`-algebra in Mathlib's sense has a multiplication satisfying
the book's laws. -/
theorem isAlgebraMul_of_nonUnitalNonAssoc (F A : Type*) [CommSemiring F]
    [NonUnitalNonAssocSemiring A] [Module F A] [IsScalarTower F A A] [SMulCommClass F A A] :
    IsAlgebraMul F A where
  add_mul := add_mul
  mul_add := mul_add
  smul_mul_smul α β x y := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Bridging notion for Morris, Topology Without Tears, Definition 12.2.9: a Banach algebra over
`𝕜` is a normed algebra whose norm is complete. -/
def IsBanachAlgebra (𝕜 A : Type*) [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] : Prop :=
  CompleteSpace A

/-- Morris, Topology Without Tears, Definition 12.2.9 (TP-353). A Banach algebra is exactly a
complete normed algebra; the continuous functions on a compact space form one. -/
@[kb "morris2024" "Definition 12.2.9, p. 378"]
theorem isBanachAlgebra_iff (𝕜 A : Type*) [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] :
    IsBanachAlgebra 𝕜 A ↔ CompleteSpace A := Iff.rfl

/-- The algebra `C(X, 𝕜)` of continuous functions on a compact space is a Banach algebra. -/
theorem isBanachAlgebra_continuousMap (X 𝕜 : Type*) [TopologicalSpace X] [CompactSpace X]
    [RCLike 𝕜] : IsBanachAlgebra 𝕜 C(X, 𝕜) :=
  inferInstanceAs (CompleteSpace C(X, 𝕜))

end Algebras

section Lattice

variable {X : Type*} [TopologicalSpace X]

/-- Morris, Topology Without Tears, Lemma 12.2.18 (TP-363). For `f, g ∈ C(X, ℝ)`: `|f|` is
continuous, `f ∧ g = ½(f + g - |f - g|)`, `f ∨ g = ½(f + g + |f - g|)`, and a vector subspace
closed under absolute value is a sublattice. -/
@[kb "morris2024" "Lemma 12.2.18, p. 382"]
theorem continuousMap_abs_lattice :
    (∀ f : C(X, ℝ), Continuous fun x => |f x|) ∧
      (∀ f g : C(X, ℝ), f ⊓ g = (2⁻¹ : ℝ) • (f + g - |f - g|)) ∧
      (∀ f g : C(X, ℝ), f ⊔ g = (2⁻¹ : ℝ) • (f + g + |f - g|)) ∧
      ∀ A : Submodule ℝ C(X, ℝ), (∀ f ∈ A, |f| ∈ A) →
        ∀ f ∈ A, ∀ g ∈ A, f ⊓ g ∈ A ∧ f ⊔ g ∈ A := by
  have hinf : ∀ f g : C(X, ℝ), f ⊓ g = (2⁻¹ : ℝ) • (f + g - |f - g|) := by
    intro f g
    rw [inf_eq_half_smul_add_sub_abs_sub' ℝ, abs_sub_comm]
  have hsup : ∀ f g : C(X, ℝ), f ⊔ g = (2⁻¹ : ℝ) • (f + g + |f - g|) := by
    intro f g
    rw [sup_eq_half_smul_add_add_abs_sub' ℝ, abs_sub_comm]
  refine ⟨fun f => f.continuous.abs, hinf, hsup, fun A hA f hf g hg => ?_⟩
  have habs : |f - g| ∈ A := hA _ (A.sub_mem hf hg)
  refine ⟨?_, ?_⟩
  · rw [hinf]
    exact A.smul_mem _ (A.sub_mem (A.add_mem hf hg) habs)
  · rw [hsup]
    exact A.smul_mem _ (A.add_mem (A.add_mem hf hg) habs)

end Lattice

section StoneWeierstrass

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

omit [CompactSpace X] [T2Space X] in
/-- A non-unital subalgebra of `C(X, 𝕜)` containing a nonzero constant contains the constant `1`. -/
theorem one_mem_of_const_mem {𝕜 : Type*} [RCLike 𝕜] {A : NonUnitalSubalgebra 𝕜 C(X, 𝕜)} {c : 𝕜}
    (hc0 : c ≠ 0) (hc : ContinuousMap.const X c ∈ A) : (1 : C(X, 𝕜)) ∈ A := by
  have h2 : c⁻¹ • ContinuousMap.const X c = (1 : C(X, 𝕜)) := by
    ext x
    simp [hc0]
  rw [← h2]
  exact A.smul_mem c⁻¹ hc

/-- Morris, Topology Without Tears, Theorem 12.2.20 (TP-365), the real Stone-Weierstrass theorem. A
closed subalgebra of `C(X, ℝ)` (`X` compact Hausdorff) containing a nonzero constant function is all
of `C(X, ℝ)` if and only if it separates the points of `X`. -/
@[kb "morris2024" "Theorem 12.2.20, p. 383"]
theorem nonUnitalSubalgebra_eq_top_iff_real (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (hA : IsClosed (A : Set C(X, ℝ))) (hc : ∃ c : ℝ, c ≠ 0 ∧ ContinuousMap.const X c ∈ A) :
    A = ⊤ ↔ Set.SeparatesPoints ((fun f : C(X, ℝ) => (f : X → ℝ)) '' (A : Set C(X, ℝ))) := by
  constructor
  · rintro rfl
    apply separatesPoints_of_dense
    simp
  · intro hsep
    obtain ⟨c, hc0, hc⟩ := hc
    let B : Subalgebra ℝ C(X, ℝ) := A.toSubalgebra (one_mem_of_const_mem hc0 hc)
    have hB : B.SeparatesPoints := hsep
    have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints B hB
    rw [eq_top_iff]
    intro f _
    have hf : f ∈ B.topologicalClosure := by rw [htop]; trivial
    have hA' : IsClosed (B : Set C(X, ℝ)) := hA
    rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, hA'.closure_eq] at hf
    exact hf

/-- Morris, Topology Without Tears, Theorem 12.2.22 (TP-366), the complex Stone-Weierstrass theorem.
A closed subalgebra of `C(X, ℂ)` (`X` compact Hausdorff) containing a nonzero constant function is
all of `C(X, ℂ)` if and only if it is closed under complex conjugation and separates the points of
`X`. -/
@[kb "morris2024" "Theorem 12.2.22, p. 384"]
theorem nonUnitalSubalgebra_eq_top_iff_complex (A : NonUnitalSubalgebra ℂ C(X, ℂ))
    (hA : IsClosed (A : Set C(X, ℂ))) (hc : ∃ c : ℂ, c ≠ 0 ∧ ContinuousMap.const X c ∈ A) :
    A = ⊤ ↔ ((∀ f ∈ A, star f ∈ A) ∧
      Set.SeparatesPoints ((fun f : C(X, ℂ) => (f : X → ℂ)) '' (A : Set C(X, ℂ)))) := by
  constructor
  · rintro rfl
    refine ⟨fun f _ => trivial, ?_⟩
    apply separatesPoints_of_dense
    simp
  · rintro ⟨hstar, hsep⟩
    obtain ⟨c, hc0, hc⟩ := hc
    let B : StarSubalgebra ℂ C(X, ℂ) :=
      ⟨A.toSubalgebra (one_mem_of_const_mem hc0 hc), fun {f} hf => hstar f hf⟩
    have hB : B.SeparatesPoints := hsep
    have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hB
    rw [eq_top_iff]
    intro f _
    have hf : f ∈ B.topologicalClosure := by rw [htop]; trivial
    have hA' : IsClosed (B : Set C(X, ℂ)) := hA
    rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, hA'.closure_eq] at hf
    exact hf

end StoneWeierstrass

section Trig

open Finset
open scoped Real

local instance : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The real trigonometric polynomial `a₀ + ∑_{n=1}^N (aₙ cos(nx) + bₙ sin(nx))`. -/
noncomputable def realTrigPoly (N : ℕ) (a b : ℕ → ℝ) (x : ℝ) : ℝ :=
  a 0 + ∑ n ∈ Icc 1 N, (a n * Real.cos (n * x) + b n * Real.sin (n * x))

/-- The complex trigonometric polynomial `a₀ + ∑_{n=1}^N (aₙ cos(nx) + i bₙ sin(nx))`. -/
noncomputable def complexTrigPoly (N : ℕ) (a b : ℕ → ℂ) (x : ℝ) : ℂ :=
  a 0 + ∑ n ∈ Icc 1 N,
    (a n * Complex.cos (n * x) + Complex.I * b n * Complex.sin (n * x))

/-- Morris, Topology Without Tears, Definition 12.2.25 (TP-368). `f : ℝ → ℝ` is a real trigonometric
polynomial of degree `N` if `f = a₀ + ∑ aₙ cos(nx) + bₙ sin(nx)` with `a_N ≠ 0` or `b_N ≠ 0`. -/
def IsRealTrigPoly (N : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, (a N ≠ 0 ∨ b N ≠ 0) ∧ f = realTrigPoly N a b

/-- Morris, Topology Without Tears, Definition 12.2.26 (TP-369). `f : ℝ → ℂ` is a complex
trigonometric polynomial of degree `N` if `f = a₀ + ∑ aₙ cos(nx) + i bₙ sin(nx)` with complex
coefficients and `a_N ≠ 0` or `b_N ≠ 0`. -/
def IsComplexTrigPoly (N : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ a b : ℕ → ℂ, (a N ≠ 0 ∨ b N ≠ 0) ∧ f = complexTrigPoly N a b

/-- Morris, Topology Without Tears, Definition 12.2.25 and Remark 12.2.27 (TP-368). Real
trigonometric polynomials are `2π`-periodic. -/
@[kb "morris2024" "Definition 12.2.25, p. 385"]
theorem realTrigPoly_periodic (N : ℕ) (a b : ℕ → ℝ) : Function.Periodic (realTrigPoly N a b) (2 * π) := by
  intro x
  have h : ∀ n ∈ Finset.Icc 1 N, a n * Real.cos (n * (x + 2 * π)) + b n * Real.sin (n * (x + 2 * π)) =
      a n * Real.cos (n * x) + b n * Real.sin (n * x) := by
    intro n _
    have : (n : ℝ) * (x + 2 * π) = n * x + n * (2 * π) := by ring
    rw [this, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  unfold realTrigPoly
  rw [Finset.sum_congr rfl h]

/-- Morris, Topology Without Tears, Definition 12.2.26 and Remark 12.2.27 (TP-369). Complex
trigonometric polynomials are `2π`-periodic. -/
@[kb "morris2024" "Definition 12.2.26, p. 386"]
theorem complexTrigPoly_periodic (N : ℕ) (a b : ℕ → ℂ) :
    Function.Periodic (complexTrigPoly N a b) (2 * π) := by
  intro x
  have h : ∀ n ∈ Finset.Icc 1 N, a n * Complex.cos (n * ((x + 2 * π : ℝ) : ℂ)) +
      Complex.I * b n * Complex.sin (n * ((x + 2 * π : ℝ) : ℂ)) =
      a n * Complex.cos (n * (x : ℂ)) + Complex.I * b n * Complex.sin (n * (x : ℂ)) := by
    intro n _
    have : (n : ℂ) * ((x + 2 * π : ℝ) : ℂ) = n * x + n * (2 * π) := by push_cast; ring
    rw [this, Complex.cos_add_nat_mul_two_pi, Complex.sin_add_nat_mul_two_pi]
  unfold complexTrigPoly
  rw [Finset.sum_congr rfl h]

/-- The complex trigonometric polynomials, as continuous functions on the circle `ℝ / 2πℤ` (a
function of `x ∈ ℝ` satisfying `f (x + 2π) = f x` is a function on the circle, Remark 12.2.29);
polynomials of every degree, including constants (a polynomial with vanishing top coefficients is
one of lower degree). -/
def complexTrigPolynomials : Set C(AddCircle (2 * π), ℂ) :=
  {g | ∃ (N : ℕ) (a b : ℕ → ℂ), ∀ x : ℝ, g (x : AddCircle (2 * π)) = complexTrigPoly N a b x}

/-- The real trigonometric polynomials, as continuous real functions on the circle `ℝ / 2πℤ`. -/
def realTrigPolynomials : Set C(AddCircle (2 * π), ℝ) :=
  {g | ∃ (N : ℕ) (a b : ℕ → ℝ), ∀ x : ℝ, g (x : AddCircle (2 * π)) = realTrigPoly N a b x}

theorem complexTrigPoly_pad {N M : ℕ} (h : N ≤ M) (a b : ℕ → ℂ) (x : ℝ) :
    complexTrigPoly N a b x = complexTrigPoly M (fun n => if n ≤ N then a n else 0)
      (fun n => if n ≤ N then b n else 0) x := by
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc_right h
  have hzero : ∀ n ∈ Finset.Icc 1 M, n ∉ Finset.Icc 1 N →
      ((if n ≤ N then a n else 0) * Complex.cos (n * x) +
        Complex.I * (if n ≤ N then b n else 0) * Complex.sin (n * x)) = 0 := by
    intro n hn hn'
    have : ¬ n ≤ N := fun h' => hn' (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, h'⟩)
    simp [this]
  have key := (Finset.sum_subset hsub hzero).symm
  unfold complexTrigPoly
  simp only [Nat.zero_le, ite_true]
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have : n ≤ N := (Finset.mem_Icc.1 hn).2
  simp [this]

theorem complexTrigPoly_add (N : ℕ) (a b a' b' : ℕ → ℂ) (x : ℝ) :
    complexTrigPoly N a b x + complexTrigPoly N a' b' x =
      complexTrigPoly N (a + a') (b + b') x := by
  simp only [complexTrigPoly, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem complexTrigPoly_smul (N : ℕ) (c : ℂ) (a b : ℕ → ℂ) (x : ℝ) :
    c * complexTrigPoly N a b x = complexTrigPoly N (c • a) (c • b) x := by
  simp only [complexTrigPoly, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem add_mem_complexTrigPolynomials {g₁ g₂ : C(AddCircle (2 * π), ℂ)}
    (h₁ : g₁ ∈ complexTrigPolynomials) (h₂ : g₂ ∈ complexTrigPolynomials) :
    g₁ + g₂ ∈ complexTrigPolynomials := by
  obtain ⟨N₁, a₁, b₁, e₁⟩ := h₁
  obtain ⟨N₂, a₂, b₂, e₂⟩ := h₂
  refine ⟨max N₁ N₂, (fun n => if n ≤ N₁ then a₁ n else 0) + (fun n => if n ≤ N₂ then a₂ n else 0),
    (fun n => if n ≤ N₁ then b₁ n else 0) + (fun n => if n ≤ N₂ then b₂ n else 0), fun x => ?_⟩
  rw [ContinuousMap.add_apply, e₁, e₂, complexTrigPoly_pad (le_max_left N₁ N₂),
    complexTrigPoly_pad (le_max_right N₁ N₂), complexTrigPoly_add]

theorem smul_mem_complexTrigPolynomials (c : ℂ) {g : C(AddCircle (2 * π), ℂ)}
    (h : g ∈ complexTrigPolynomials) : c • g ∈ complexTrigPolynomials := by
  obtain ⟨N, a, b, e⟩ := h
  exact ⟨N, c • a, c • b, fun x => by
    rw [ContinuousMap.smul_apply, smul_eq_mul, e, complexTrigPoly_smul]⟩

theorem zero_mem_complexTrigPolynomials : (0 : C(AddCircle (2 * π), ℂ)) ∈ complexTrigPolynomials :=
  ⟨0, 0, 0, fun x => by simp [complexTrigPoly]⟩

theorem exp_eq_complexTrigPoly (k : ℕ) (s : ℂ) (hs : s = 1 ∨ s = -1) (x : ℝ) :
    Complex.exp (Complex.I * (s * k) * x) =
      complexTrigPoly k (fun m => if m = k then 1 else 0) (fun m => if m = k then s else 0) x := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [complexTrigPoly]
  · have hsum : ∑ n ∈ Finset.Icc 1 k,
        ((if n = k then (1 : ℂ) else 0) * Complex.cos (n * x) +
          Complex.I * (if n = k then s else 0) * Complex.sin (n * x)) =
        Complex.cos (k * x) + Complex.I * s * Complex.sin (k * x) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro n _ hn
        simp [hn]
      · intro hk'
        exact absurd (Finset.mem_Icc.2 ⟨hk, le_rfl⟩) hk'
    unfold complexTrigPoly
    rw [hsum]
    simp only [hk.ne, ↓reduceIte, zero_add]
    have : Complex.I * (s * k) * x = (s * k * x) * Complex.I := by ring
    rw [this, Complex.exp_mul_I]
    rcases hs with rfl | rfl
    · simp [mul_comm]
    · simp [Complex.cos_neg, Complex.sin_neg, mul_comm]

theorem fourier_mem_complexTrigPolynomials (n : ℤ) :
    (fourier (T := 2 * π) n) ∈ complexTrigPolynomials := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hf : ∀ x : ℝ, fourier (T := 2 * π) n (x : AddCircle (2 * π)) =
      Complex.exp (Complex.I * n * x) := by
    intro x
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · refine ⟨k, fun m => if m = k then 1 else 0, fun m => if m = k then 1 else 0, fun x => ?_⟩
    rw [hf, ← exp_eq_complexTrigPoly k 1 (Or.inl rfl)]
    simp
  · refine ⟨k, fun m => if m = k then 1 else 0, fun m => if m = k then -1 else 0, fun x => ?_⟩
    rw [hf, ← exp_eq_complexTrigPoly k (-1) (Or.inr rfl)]
    simp

/-- The complex trigonometric polynomials are dense in `C(T, ℂ)` for the circle `T = ℝ / 2πℤ`. -/
theorem dense_complexTrigPolynomials : Dense complexTrigPolynomials := by
  have hspan := span_fourier_closure_eq_top (T := 2 * π)
  have hd : Dense ((Submodule.span ℂ (Set.range (fourier (T := 2 * π))) :
      Submodule ℂ C(AddCircle (2 * π), ℂ)) : Set C(AddCircle (2 * π), ℂ)) := by
    rw [dense_iff_closure_eq]
    have := congr_arg
      (fun s : Submodule ℂ C(AddCircle (2 * π), ℂ) => (s : Set C(AddCircle (2 * π), ℂ))) hspan
    simpa [Submodule.topologicalClosure_coe] using this
  refine hd.mono ?_
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    exact fourier_mem_complexTrigPolynomials n
  | zero => exact zero_mem_complexTrigPolynomials
  | add g₁ g₂ _ _ h₁ h₂ => exact add_mem_complexTrigPolynomials h₁ h₂
  | smul c g _ h => exact smul_mem_complexTrigPolynomials c h

theorem complexTrigPoly_re (N : ℕ) (a b : ℕ → ℂ) (x : ℝ) :
    (complexTrigPoly N a b x).re =
      realTrigPoly N (fun n => (a n).re) (fun n => -(b n).im) x := by
  have hc : ∀ n : ℕ, Complex.cos ((n : ℂ) * (x : ℂ)) = ((Real.cos (n * x) : ℝ) : ℂ) := by
    intro n
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_cos]
  have hs : ∀ n : ℕ, Complex.sin ((n : ℂ) * (x : ℂ)) = ((Real.sin (n * x) : ℝ) : ℂ) := by
    intro n
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_sin]
  unfold complexTrigPoly realTrigPoly
  simp only [Complex.add_re, Complex.re_sum, hc, hs, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- Morris, Topology Without Tears, Corollary 12.2.30 (TP-370), complex case. The complex
trigonometric polynomials are dense in `C(T, ℂ)`. -/
@[kb "morris2024" "Corollary 12.2.30, p. 386"]
theorem dense_complexTrigPolynomials' : Dense complexTrigPolynomials :=
  dense_complexTrigPolynomials

/-- Morris, Topology Without Tears, Corollary 12.2.30 (TP-370), real case. The real trigonometric
polynomials are dense in `C(T, ℝ)`. -/
@[kb "morris2024" "Corollary 12.2.30, p. 386"]
theorem dense_realTrigPolynomials : Dense realTrigPolynomials := by
  rw [Metric.dense_iff]
  intro g ε hε
  let gC : C(AddCircle (2 * π), ℂ) :=
    ⟨fun y => ((g y : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  obtain ⟨h, hhT, hdist⟩ := dense_complexTrigPolynomials.exists_dist_lt gC hε
  obtain ⟨N, a, b, e⟩ := hhT
  let g' : C(AddCircle (2 * π), ℝ) := ⟨fun y => (h y).re, Complex.continuous_re.comp h.continuous⟩
  refine ⟨g', ?_, N, fun n => (a n).re, fun n => -(b n).im, fun x => ?_⟩
  · rw [Metric.mem_ball, ContinuousMap.dist_lt_iff hε]
    intro y
    calc dist (g' y) (g y) = |(h y).re - g y| := by simp [g', Real.dist_eq]
      _ = |((gC y) - h y).re| := by simp [gC, abs_sub_comm]
      _ ≤ ‖gC y - h y‖ := Complex.abs_re_le_norm _
      _ = dist (gC y) (h y) := (dist_eq_norm _ _).symm
      _ < ε := lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist y) hdist
  · show (h (x : AddCircle (2 * π))).re = _
    rw [e, complexTrigPoly_re]

end Trig

end UndergradKB.Topology
