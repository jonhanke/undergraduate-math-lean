import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RepresentationTheory.Subrepresentation
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.WeylShiftIso

/-! # Homogeneous parts of a polynomial representation (Etingof et al., Theorem 4.66)

Let `ρ` be a finite-dimensional representation of `GL_N(ℂ)` whose coefficient functions are polynomials in the
matrix entries (`IsPolynomialRep`).  The scalar matrices `z • 1` act by an operator polynomial in `z`:
`ρ (z • 1) = ∑ zⁿ Eₙ` (`IsPolynomialRep.exists_scalar_expansion`).  Comparing coefficients
(`eq_zero_of_forall_sum_pow_smul`) shows that the `Eₙ` are pairwise orthogonal idempotents with sum `1`, commuting
with the action, preserving every subrepresentation, and that `GL_N(ℂ)` acts on the image of `Eₙ` by a homogeneous
polynomial representation of degree `n` (`ScalarExpansion.isHomog_coeff`).

Main results:
* `IsPolynomialRep.exists_isCompl`: complete reducibility of finite-dimensional polynomial representations, from
  the homogeneous case `IsHomogPolyRep.exists_isCompl`.
* `IsPolynomialRep.exists_isHomogPolyRep_of_irreducible`: an irreducible polynomial representation is homogeneous.
-/

namespace UndergradKB.RepresentationTheory

open MvPolynomial

section Scalar

variable {N : ℕ}

/-- The scalar matrix `z • 1` as an element of `GL_N(ℂ)`. -/
noncomputable def scalarGL (N : ℕ) (z : ℂ) (hz : z ≠ 0) : GL (Fin N) ℂ :=
  Units.map (algebraMap ℂ (Matrix (Fin N) (Fin N) ℂ)).toMonoidHom (Units.mk0 z hz)

theorem coe_scalarGL (z : ℂ) (hz : z ≠ 0) :
    (scalarGL N z hz : Matrix (Fin N) (Fin N) ℂ) = z • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  simp [scalarGL, Algebra.algebraMap_eq_smul_one]

theorem scalarGL_one : scalarGL N 1 one_ne_zero = 1 := by
  apply Units.ext
  simp [coe_scalarGL]

theorem scalarGL_mul (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    scalarGL N (z * w) (mul_ne_zero hz hw) = scalarGL N z hz * scalarGL N w hw := by
  apply Units.ext
  simp [coe_scalarGL, smul_smul, mul_comm]

theorem scalarGL_mul_comm (z : ℂ) (hz : z ≠ 0) (g : GL (Fin N) ℂ) :
    scalarGL N z hz * g = g * scalarGL N z hz := by
  apply Units.ext
  simp [coe_scalarGL]

theorem glEntries_scalarGL_mul (z : ℂ) (hz : z ≠ 0) (g : GL (Fin N) ℂ) :
    glEntries N ℂ (scalarGL N z hz * g) = z • glEntries N ℂ g := by
  funext p
  simp [glEntries, coe_scalarGL]

end Scalar

section Unique

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Comparing coefficients: if `∑_{n < D} zⁿ • cₙ = 0` for every nonzero complex `z`, all `cₙ` vanish. -/
theorem eq_zero_of_forall_sum_pow_smul (D : ℕ) (c : ℕ → M)
    (h : ∀ z : ℂ, z ≠ 0 → ∑ n ∈ Finset.range D, z ^ n • c n = 0) {n : ℕ} (hn : n < D) : c n = 0 := by
  classical
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (c n)).1 fun φ => ?_
  let p : Polynomial ℂ := ∑ m ∈ Finset.range D, Polynomial.C (φ (c m)) * Polynomial.X ^ m
  have hroot : ∀ z : ℂ, z ≠ 0 → p.IsRoot z := by
    intro z hz
    have := congrArg φ (h z hz)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [p, Polynomial.IsRoot, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← this]
    exact Finset.sum_congr rfl fun m _ => mul_comm (φ (c m)) (z ^ m)
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact Set.Infinite.mono (fun z hz => hroot z hz) (Set.finite_singleton (0 : ℂ)).infinite_compl
  have := congrArg (fun q => Polynomial.coeff q n) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
  simpa [Finset.sum_ite_eq, Finset.mem_range.2 hn] using this

theorem eq_of_forall_sum_pow_smul (D : ℕ) (a c : ℕ → M)
    (h : ∀ z : ℂ, z ≠ 0 → ∑ n ∈ Finset.range D, z ^ n • a n = ∑ n ∈ Finset.range D, z ^ n • c n)
    {n : ℕ} (hn : n < D) : a n = c n := by
  have := eq_zero_of_forall_sum_pow_smul D (fun m => a m - c m)
    (fun z hz => by simp [smul_sub, Finset.sum_sub_distrib, h z hz]) hn
  exact sub_eq_zero.1 this

end Unique

section Expansion

variable {N : ℕ}

/-- Scaling the argument of a homogeneous polynomial of degree `d` by `c` scales the value by `cᵈ`. -/
theorem isHomogeneous_eval_smul {σ : Type*} {F : MvPolynomial σ ℂ} {d : ℕ} (hF : F.IsHomogeneous d) (c : ℂ)
    (p : σ → ℂ) : eval (c • p) F = c ^ d * eval p F := by
  simp only [eval_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hF.degree_eq_sum_deg_support hx, mul_left_comm]

/-- A polynomial function on `GL_N(ℂ)` is a sum of homogeneous ones, scaling like `zⁿ` under `g ↦ z g`. -/
theorem exists_homog_expansion {f : GL (Fin N) ℂ → ℂ} (hf : f ∈ polyFunctions N ℂ) :
    ∃ (D : ℕ) (h : ℕ → GL (Fin N) ℂ → ℂ), (∀ n, h n ∈ homogFunctions N n) ∧
      ∀ D', D ≤ D' → ∀ g z (hz : z ≠ 0),
        f (scalarGL N z hz * g) = ∑ n ∈ Finset.range D', z ^ n * h n g := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P.totalDegree + 1, fun n g => eval (glEntries N ℂ g) (homogeneousComponent n P),
    fun n => ⟨_, homogeneousComponent_isHomogeneous n P, fun g => rfl⟩, fun D' hD' g z hz => ?_⟩
  have hsum : ∑ n ∈ Finset.range D', homogeneousComponent n P = P := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 hD') fun n hn hn' => ?_).symm.trans
      (sum_homogeneousComponent P)
    apply homogeneousComponent_eq_zero
    simp only [Finset.mem_range] at hn hn'
    omega
  rw [hP, glEntries_scalarGL_mul]
  conv_lhs => rw [← hsum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => isHomogeneous_eval_smul (homogeneousComponent_isHomogeneous n P) z _

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {ρ : Representation ℂ (GL (Fin N) ℂ) W}

/-- The scalar matrices act on a polynomial representation by an operator polynomial `∑ zⁿ Eₙ`. -/
structure ScalarExpansion (ρ : Representation ℂ (GL (Fin N) ℂ) W) where
  /-- A bound on the degrees. -/
  D : ℕ
  /-- The coefficient operators. -/
  E : ℕ → Module.End ℂ W
  E_eq_zero : ∀ n, D ≤ n → E n = 0
  expand : ∀ z (hz : z ≠ 0), ρ (scalarGL N z hz) = ∑ n ∈ Finset.range D, z ^ n • E n

theorem IsPolynomialRep.exists_scalar_expansion (hρ : IsPolynomialRep (k := ℂ) ρ) :
    Nonempty (ScalarExpansion ρ) := by
  classical
  let b := Module.finBasis ℂ W
  have hf : ∀ i j, (fun g => b.coord i (ρ g (b j))) ∈ polyFunctions N ℂ := fun i j => hρ (b j) (b.coord i)
  choose D h _ hexp using fun i j => exists_homog_expansion (hf i j)
  let D' := ∑ i, ∑ j, D i j
  have hDle : ∀ i j, D i j ≤ D' := fun i j =>
    (Finset.single_le_sum (f := fun j => D i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, D i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  refine ⟨⟨D', fun n => if n < D' then Matrix.toLin b b (Matrix.of fun i j => h i j n 1) else 0,
    fun n hn => if_neg (not_lt.2 hn), fun z hz => ?_⟩⟩
  rw [Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_range.1 hn)]]
  apply (LinearMap.toMatrix b b).injective
  simp only [map_sum, map_smul, LinearMap.toMatrix_toLin]
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.sum_apply]
  have := hexp i j D' (hDle i j) 1 z hz
  simp only [mul_one, Module.Basis.coord_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

namespace ScalarExpansion

variable (S : ScalarExpansion ρ)

theorem sum_E : ∑ n ∈ Finset.range S.D, S.E n = 1 := by
  have := S.expand 1 one_ne_zero
  rw [scalarGL_one, map_one] at this
  simpa using this.symm

theorem sum_E_apply (w : W) : ∑ n ∈ Finset.range S.D, S.E n w = w := by
  calc ∑ n ∈ Finset.range S.D, S.E n w = (∑ n ∈ Finset.range S.D, S.E n) w := (LinearMap.sum_apply _ _ _).symm
    _ = w := by rw [S.sum_E]; rfl

theorem E_mul_E (a b : ℕ) : S.E a * S.E b = if a = b then S.E a else 0 := by
  by_cases ha : a < S.D
  swap
  · rw [S.E_eq_zero a (not_lt.1 ha)]; simp
  by_cases hb : b < S.D
  swap
  · rw [S.E_eq_zero b (not_lt.1 hb), if_neg (by omega)]; simp
  -- coefficient of `z^a` in `ρ(zw) = ρ(z) ρ(w)`
  have h1 : ∀ w : ℂ, w ≠ 0 → w ^ a • S.E a = ∑ m ∈ Finset.range S.D, w ^ m • (S.E a * S.E m) := by
    intro w hw
    refine eq_of_forall_sum_pow_smul S.D (fun n => w ^ n • S.E n)
      (fun n => ∑ m ∈ Finset.range S.D, w ^ m • (S.E n * S.E m)) (fun z hz => ?_) ha
    have e := congrArg ρ (scalarGL_mul (N := N) z w hz hw)
    rw [map_mul, S.expand, S.expand, S.expand] at e
    rw [Finset.sum_mul] at e
    simp only [smul_mul_assoc, Finset.mul_sum, mul_smul_comm] at e
    simp only [Finset.smul_sum, smul_smul, mul_pow] at e ⊢
    rw [e]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm (w ^ m)]
  have h2 := eq_of_forall_sum_pow_smul S.D (fun m => if m = a then S.E a else 0)
    (fun m => S.E a * S.E m) (fun w hw => by
      rw [← h1 w hw]
      simp [Finset.sum_ite_eq', Finset.mem_range.2 ha]) hb
  rw [← h2]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab, if_neg (Ne.symm hab)]

theorem E_E_apply (a b : ℕ) (w : W) : S.E a (S.E b w) = if a = b then S.E a w else 0 := by
  have := LinearMap.congr_fun (S.E_mul_E a b) w
  rw [Module.End.mul_apply] at this
  rw [this]
  split_ifs <;> rfl

theorem E_idem (n : ℕ) (w : W) : S.E n (S.E n w) = S.E n w := by
  rw [S.E_E_apply, if_pos rfl]

theorem comm (g : GL (Fin N) ℂ) (n : ℕ) : ρ g * S.E n = S.E n * ρ g := by
  by_cases hn : n < S.D
  swap
  · rw [S.E_eq_zero n (not_lt.1 hn)]; simp
  refine eq_of_forall_sum_pow_smul S.D (fun n => ρ g * S.E n) (fun n => S.E n * ρ g) (fun z hz => ?_) hn
  have e : ρ g * ρ (scalarGL N z hz) = ρ (scalarGL N z hz) * ρ g := by
    rw [← map_mul, ← map_mul, scalarGL_mul_comm]
  rw [S.expand, Finset.mul_sum, Finset.sum_mul] at e
  simpa [mul_smul_comm, smul_mul_assoc] using e

theorem comm_apply (g : GL (Fin N) ℂ) (n : ℕ) (w : W) : ρ g (S.E n w) = S.E n (ρ g w) :=
  LinearMap.congr_fun (S.comm g n) w

/-- The coefficient operators preserve every subrepresentation. -/
theorem E_mem {U : Submodule ℂ W} (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) (n : ℕ) {w : W} (hw : w ∈ U) :
    S.E n w ∈ U := by
  by_cases hn : n < S.D
  swap
  · rw [S.E_eq_zero n (not_lt.1 hn)]; exact U.zero_mem
  have := eq_zero_of_forall_sum_pow_smul S.D (fun n => U.mkQ (S.E n w)) (fun z hz => ?_) hn
  · exact (Submodule.Quotient.mk_eq_zero U).1 this
  have e := hU (scalarGL N z hz) w hw
  rw [S.expand] at e
  simp only [LinearMap.sum_apply, LinearMap.smul_apply] at e
  have e' := (Submodule.Quotient.mk_eq_zero U).2 e
  rw [← Submodule.mkQ_apply, map_sum] at e'
  simpa only [map_smul] using e'

/-- `ρ (z • 1)` acts on the image of `Eₙ` as multiplication by `zⁿ`. -/
theorem scalar_apply_of_E {n : ℕ} {w : W} (hw : S.E n w = w) (z : ℂ) (hz : z ≠ 0) :
    ρ (scalarGL N z hz) w = z ^ n • w := by
  by_cases hn : n < S.D
  swap
  · rw [S.E_eq_zero n (not_lt.1 hn)] at hw
    rw [← hw]; simp
  have key : ∀ m, (z ^ m • S.E m) w = if m = n then z ^ n • w else 0 := by
    intro m
    rw [LinearMap.smul_apply]
    have := S.E_E_apply m n w
    rw [hw] at this
    rw [this]
    split_ifs with h
    · subst h; rw [hw]
    · rw [smul_zero]
  rw [S.expand, LinearMap.sum_apply, Finset.sum_congr rfl fun m _ => key m]
  simp [Finset.mem_range.2 hn]

variable (hρ : IsPolynomialRep (k := ℂ) ρ)
include hρ

/-- On the image of `Eₙ` every coefficient function is a homogeneous polynomial of degree `n`. -/
theorem isHomog_coeff {n : ℕ} {w : W} (hw : S.E n w = w) (φ : Module.Dual ℂ W) :
    (fun g => φ (ρ g w)) ∈ homogFunctions N n := by
  obtain ⟨D, h, hh, hexp⟩ := exists_homog_expansion (hρ w φ)
  let D' := max D (n + 1)
  have hn : n < D' := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  have key : ∀ g, h n g = φ (ρ g w) := by
    intro g
    refine (eq_of_forall_sum_pow_smul D' (fun m => h m g) (fun m => if m = n then φ (ρ g w) else 0)
      (fun z hz => ?_) hn).trans (if_pos rfl)
    have e := hexp D' (le_max_left _ _) g z hz
    simp only [smul_eq_mul] at e ⊢
    rw [← e]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range.2 hn, if_true]
    rw [scalarGL_mul_comm, map_mul, Module.End.mul_apply, S.scalar_apply_of_E hw z hz, map_smul,
      map_smul, smul_eq_mul]
  have : (fun g => φ (ρ g w)) = h n := funext fun g => (key g).symm
  rw [this]
  exact hh n

end ScalarExpansion

end Expansion

section Reducible

variable {N : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {ρ : Representation ℂ (GL (Fin N) ℂ) W}

namespace ScalarExpansion

variable (S : ScalarExpansion ρ)

/-- The image of `Eₙ`, a subrepresentation. -/
def part (n : ℕ) : Subrepresentation ρ where
  toSubmodule := LinearMap.range (S.E n)
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, rfl⟩
    exact ⟨ρ g v, (S.comm_apply g n v).symm⟩

theorem mem_part_iff (n : ℕ) (w : W) : w ∈ (S.part n).toSubmodule ↔ S.E n w = w := by
  constructor
  · rintro ⟨v, rfl⟩
    exact S.E_idem n v
  · intro h
    exact ⟨w, h⟩

variable (hρ : IsPolynomialRep (k := ℂ) ρ)
include hρ

/-- `GL_N(ℂ)` acts on the image of `Eₙ` by a homogeneous polynomial representation of degree `n`. -/
theorem isHomogPolyRep_part (n : ℕ) : IsHomogPolyRep n (S.part n).toRepresentation := by
  rw [isHomogPolyRep_iff]
  intro w φ
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have hw : S.E n w = w := (S.mem_part_iff n w).1 w.2
  have := S.isHomog_coeff hρ hw ψ
  convert this using 1
  funext g
  rw [← hψ]
  rfl

theorem exists_complement_part (n : ℕ) {U : Submodule ℂ W} (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) :
    ∃ C : Submodule ℂ W, C ≤ (S.part n).toSubmodule ∧ (∀ g, ∀ w ∈ C, ρ g w ∈ C) ∧
      (∀ x ∈ (S.part n).toSubmodule, ∃ u ∈ U, ∃ c ∈ C, x = u + c) ∧ (∀ x ∈ U, x ∈ C → x = 0) := by
  let P := (S.part n).toSubmodule
  let Un : Submodule ℂ P := U.comap P.subtype
  have hUn : ∀ g, ∀ w ∈ Un, (S.part n).toRepresentation g w ∈ Un := fun g w hw => hU g w hw
  obtain ⟨C', hC', hc⟩ := IsHomogPolyRep.exists_isCompl (S.isHomogPolyRep_part hρ n) Un hUn
  refine ⟨C'.map P.subtype, Submodule.map_subtype_le _ _, ?_, ?_, ?_⟩
  · rintro g _ ⟨c, hc, rfl⟩
    exact ⟨_, hC' g c hc, rfl⟩
  · intro x hx
    have : (⟨x, hx⟩ : P) ∈ Un ⊔ C' := by rw [hc.codisjoint.eq_top]; trivial
    obtain ⟨y, hy, c, hcm, hyc⟩ := Submodule.mem_sup.1 this
    refine ⟨y, hy, c, ⟨c, hcm, rfl⟩, ?_⟩
    have := congrArg Subtype.val hyc
    simpa using this.symm
  · rintro x hx ⟨c, hcm, rfl⟩
    have : c ∈ Un := hx
    have h0 := (Submodule.disjoint_def.1 hc.disjoint) c this hcm
    simp [h0]

end ScalarExpansion

/-- **Etingof et al., Theorem 4.66 (i), complete reducibility for polynomial representations.**  Every
subrepresentation of a finite-dimensional representation of `GL_N(ℂ)` whose coefficient functions are polynomials in
the matrix entries has an invariant complement. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem IsPolynomialRep.exists_isCompl (hρ : IsPolynomialRep (k := ℂ) ρ) (U : Submodule ℂ W)
    (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) :
    ∃ U' : Submodule ℂ W, (∀ g, ∀ w ∈ U', ρ g w ∈ U') ∧ IsCompl U U' := by
  classical
  obtain ⟨S⟩ := hρ.exists_scalar_expansion
  choose C hCle hCinv hCspan hCdisj using fun n => S.exists_complement_part hρ n hU
  let U' : Submodule ℂ W := ⨅ n, (C n).comap (S.E n)
  have hmem : ∀ x, x ∈ U' ↔ ∀ n, S.E n x ∈ C n := fun x => by simp [U']
  refine ⟨U', fun g w hw => ?_, ⟨?_, ?_⟩⟩
  · rw [hmem] at hw ⊢
    intro n
    rw [← S.comm_apply]
    exact hCinv n g _ (hw n)
  · rw [Submodule.disjoint_def]
    intro x hxU hxU'
    rw [hmem] at hxU'
    rw [← S.sum_E_apply x]
    exact Finset.sum_eq_zero fun n _ => hCdisj n _ (S.E_mem hU n hxU) (hxU' n)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hpart : ∀ n, S.E n x ∈ (S.part n).toSubmodule := fun n => ⟨x, rfl⟩
    choose u hu c hc hx using fun n => hCspan n _ (hpart n)
    have hcE : ∀ m n, S.E m (c n) = if m = n then c n else 0 := by
      intro m n
      have := (S.mem_part_iff n (c n)).1 (hCle n (hc n))
      rw [← this, S.E_E_apply, this]
      split_ifs with h
      · subst h; exact this
      · rfl
    refine Submodule.mem_sup.2 ⟨∑ n ∈ Finset.range S.D, u n, U.sum_mem fun n _ => hu n,
      ∑ n ∈ Finset.range S.D, c n, ?_, ?_⟩
    · rw [hmem]
      intro m
      rw [map_sum]
      simp only [hcE, Finset.sum_ite_eq]
      split_ifs
      · exact hc m
      · exact (C m).zero_mem
    · rw [← Finset.sum_add_distrib, ← S.sum_E_apply x]
      exact Finset.sum_congr rfl fun n _ => (hx n).symm

/-- An irreducible polynomial representation of `GL_N(ℂ)` is homogeneous of some degree. -/
theorem IsPolynomialRep.exists_isHomogPolyRep_of_irreducible (hρ : IsPolynomialRep (k := ℂ) ρ)
    [Nontrivial W] (hirr : ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, ρ g w ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ n, IsHomogPolyRep n ρ := by
  classical
  obtain ⟨S⟩ := hρ.exists_scalar_expansion
  have hex : ∃ n, S.E n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := S.sum_E
    simp only [hcon, Finset.sum_const_zero] at this
    exact zero_ne_one this
  obtain ⟨n, hn⟩ := hex
  have htop : (S.part n).toSubmodule = ⊤ := by
    rcases hirr _ (S.part n).apply_mem_toSubmodule with h | h
    · exfalso
      apply hn
      refine LinearMap.ext fun w => ?_
      have : S.E n w ∈ (S.part n).toSubmodule := ⟨w, rfl⟩
      rw [h] at this
      simpa using this
    · exact h
  refine ⟨n, ?_⟩
  rw [isHomogPolyRep_iff]
  intro w φ
  have hw : S.E n w = w := (S.mem_part_iff n w).1 (by rw [htop]; trivial)
  exact S.isHomog_coeff hρ hw φ

end Reducible

end UndergradKB.RepresentationTheory
