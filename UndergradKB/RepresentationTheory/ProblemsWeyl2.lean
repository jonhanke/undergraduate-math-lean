import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Trace
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.WeylAlgebra

/-! # Problem 1.26(b): `p`-dimensional irreducible representations of the Weyl algebra

In characteristic `p`, for `a, b ∈ k` the space `V = k[t]_{< p}` of polynomials of degree `< p`
carries a representation of the Weyl algebra: `x` acts by multiplication by `t` reduced modulo
`t^p - a`, and `y` acts by `d/dt + b`.  It is irreducible of dimension `p`.
-/

namespace UndergradKB.RepresentationTheory

open Polynomial Module

section

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- `x` on `k[t]`: multiplication by `t`, reduced by subtracting the multiple of `t^p - a` that
cancels the coefficient of `t^p`. -/
noncomputable def weylXp (a : k) : k[X] →ₗ[k] k[X] :=
  LinearMap.mulLeft k (X : k[X]) - (lcoeff k (p - 1)).smulRight (X ^ p - C a)

omit [Fact p.Prime] [CharP k p] in
/-- `y` on `k[t]`: `d/dt + b`. -/
noncomputable def weylYp (b : k) : k[X] →ₗ[k] k[X] :=
  derivative (R := k) + b • LinearMap.id

variable {p}

theorem weylXp_apply (a : k) (f : k[X]) :
    weylXp p a f = X * f - f.coeff (p - 1) • (X ^ p - C a) := rfl

omit [Fact p.Prime] [CharP k p] in
theorem weylYp_apply (b : k) (f : k[X]) : weylYp b f = derivative f + b • f := rfl

theorem derivative_weylPoly (a : k) : derivative (X ^ p - C a : k[X]) = 0 := by
  rw [derivative_sub, derivative_X_pow, derivative_C]
  simp [CharP.cast_eq_zero]

theorem coeff_derivative_pred (f : k[X]) : (derivative f).coeff (p - 1) = 0 := by
  have hp := (Fact.out : p.Prime).pos
  rw [coeff_derivative, Nat.sub_add_cancel hp]
  have : ((p - 1 : ℕ) : k) + 1 = 0 := by
    have : ((p - 1 : ℕ) : k) + 1 = (p : k) := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hp]
    rw [this, CharP.cast_eq_zero]
  rw [this, mul_zero]

theorem derivative_X_pow_p : derivative (X ^ p : k[X]) = 0 := by
  rw [derivative_X_pow]; simp [CharP.cast_eq_zero]

theorem weylYp_weylXp (a b : k) (f : k[X]) :
    weylYp b (weylXp p a f) = weylXp p a (weylYp b f) + f := by
  simp only [weylXp_apply, weylYp_apply]
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_smul, derivative_X_pow_p, derivative_C,
    coeff_add, coeff_derivative_pred, coeff_smul, smul_eq_mul, zero_add]
  simp only [smul_eq_C_mul, map_mul, map_zero]
  ring

theorem weylXp_mem (a : k) {f : k[X]} (hf : f ∈ degreeLT k p) : weylXp p a f ∈ degreeLT k p := by
  have hp := (Fact.out : p.Prime).pos
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hf ⊢
  intro n hn
  rw [weylXp_apply]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [coeff_sub, coeff_X_mul, coeff_smul]
  rcases Nat.lt_or_ge n' p with h' | h'
  · have hn : n' + 1 = p := by omega
    have hn' : n' = p - 1 := by omega
    rw [hn, hn']
    simp [coeff_X_pow, coeff_C, show p ≠ 0 by omega]
  · rw [hf n' h']
    simp [coeff_X_pow, coeff_C, show n' + 1 ≠ p by omega]

theorem weylYp_mem (b : k) {f : k[X]} (hf : f ∈ degreeLT k p) : weylYp b f ∈ degreeLT k p := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hf ⊢
  intro n hn
  rw [weylYp_apply, coeff_add, coeff_derivative, coeff_smul, hf n hn, hf (n + 1) (by omega)]
  simp

/-- The space of polynomials of degree `< p`, the underlying space of the representation. -/
abbrev WeylPSpace (k : Type*) [Field k] (p : ℕ) : Type _ := degreeLT k p

/-- `x` acting on `k[t]_{<p}`. -/
noncomputable def weylXV (a : k) : WeylPSpace k p →ₗ[k] WeylPSpace k p :=
  (weylXp p a).restrict fun _ hf => weylXp_mem a hf

/-- `y` acting on `k[t]_{<p}`. -/
noncomputable def weylYV (b : k) : WeylPSpace k p →ₗ[k] WeylPSpace k p :=
  (weylYp b).restrict fun _ hf => weylYp_mem b hf

theorem weylYV_mul_weylXV (a b : k) :
    (weylYV b : Module.End k (WeylPSpace k p)) * weylXV a =
      weylXV a * weylYV b + 1 := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  show weylYp b (weylXp p a f.1) = weylXp p a (weylYp b f.1) + f.1
  exact weylYp_weylXp a b f.1

/-- The `p`-dimensional representation of the Weyl algebra on `k[t]_{<p}`:
`x ↦ t` (reduced mod `t^p - a`), `y ↦ d/dt + b`. -/
noncomputable def weylRepP (a b : k) : WeylAlgebra k →ₐ[k] Module.End k (WeylPSpace k p) :=
  weylLift (weylXV a) (weylYV b) (weylYV_mul_weylXV a b)

theorem weylRepP_x (a b : k) : weylRepP (p := p) a b (weylX k) = weylXV a :=
  weylLift_x _ _ _

theorem weylRepP_y (a b : k) : weylRepP (p := p) a b (weylY k) = weylYV b :=
  weylLift_y _ _ _

/-- The representation has dimension `p`. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem finrank_weylPSpace : finrank k (WeylPSpace k p) = p := by
  rw [(degreeLTEquiv k p).finrank_eq]
  simp

theorem weylXV_X_pow (a : k) (i : ℕ) (hi : i + 1 < p) (hmem : X ^ i ∈ degreeLT k p)
    (hmem' : X ^ (i + 1) ∈ degreeLT k p) :
    weylXV a ⟨X ^ i, hmem⟩ = ⟨X ^ (i + 1), hmem'⟩ := by
  refine Subtype.ext ?_
  show weylXp p a (X ^ i) = X ^ (i + 1)
  rw [weylXp_apply, coeff_X_pow, if_neg (by omega)]
  simp [pow_succ']

/-- Problem 1.26(b): in characteristic `p`, for all `a, b ∈ k`, the `p`-dimensional representation
`weylRepP a b` of the Weyl algebra (`x ↦ t` mod `t^p - a`, `y ↦ d/dt + b` on polynomials of degree
`< p`) is irreducible: its only invariant subspaces are `0` and everything. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem weylRepP_irreducible (a b : k) (W : Submodule k (WeylPSpace k p))
    (hW : ∀ z : WeylAlgebra k, ∀ w ∈ W, weylRepP (p := p) a b z w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hp := (Fact.out : p.Prime).pos
  have hx : ∀ w ∈ W, weylXV a w ∈ W := fun w hw => by
    simpa [weylRepP_x] using hW (weylX k) w hw
  have hy : ∀ w ∈ W, weylYV b w ∈ W := fun w hw => by
    simpa [weylRepP_y] using hW (weylY k) w hw
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hbot
  -- derivative stays in W
  have hder : ∀ w ∈ W, ∃ w2 ∈ W, w2.1 = derivative w.1 := fun w hw =>
    ⟨weylYV b w - b • w, W.sub_mem (hy w hw) (W.smul_mem b hw), by
      show weylYp b w.1 - b • w.1 = _
      rw [weylYp_apply]; abel⟩
  -- reach a nonzero constant
  have key : ∀ d : ℕ, ∀ w ∈ W, w.1 ≠ 0 → w.1.natDegree = d →
      ∃ w0 ∈ W, w0.1 ≠ 0 ∧ w0.1.natDegree = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro w hw hw0 hd
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · exact ⟨w, hw, hw0, hd⟩
      · obtain ⟨w2, hw2W, hw2⟩ := hder w hw
        have hdlt : d < p := by
          have := mem_degreeLT.1 w.2
          rw [← hd]
          exact (natDegree_lt_iff_degree_lt hw0).2 this
        have hne : w2.1 ≠ 0 := by
          intro h0
          have hc : (derivative w.1).coeff (d - 1) = 0 := by rw [← hw2, h0]; simp
          rw [coeff_derivative, Nat.sub_add_cancel hdpos] at hc
          have h1 : w.1.coeff d ≠ 0 := by
            rw [← hd]; exact mt leadingCoeff_eq_zero.1 hw0
          have h2 : ((d - 1 : ℕ) : k) + 1 ≠ 0 := by
            have : ((d - 1 : ℕ) : k) + 1 = (d : k) := by
              rw [← Nat.cast_add_one, Nat.sub_add_cancel hdpos]
            rw [this]
            intro h
            have := (CharP.cast_eq_zero_iff k p d).1 h
            exact absurd (Nat.le_of_dvd hdpos this) (by omega)
          exact (mul_ne_zero h1 h2) hc
        have hlt : w2.1.natDegree < d := by
          rw [hw2, ← hd]
          exact natDegree_derivative_lt (by omega)
        exact ih _ hlt w2 hw2W hne rfl
  obtain ⟨w0, hw0W, hw00, hw0d⟩ := key _ w hwW (fun h => hw0 (Subtype.ext h)) rfl
  obtain ⟨c, hc⟩ : ∃ c, w0.1 = C c := ⟨_, eq_C_of_natDegree_eq_zero hw0d⟩
  have hc0 : c ≠ 0 := by
    intro h; apply hw00; rw [hc, h]; simp
  have h1mem : (1 : k[X]) ∈ degreeLT k p := by
    rw [mem_degreeLT, degree_one]; exact_mod_cast hp
  have hone : (⟨1, h1mem⟩ : WeylPSpace k p) ∈ W := by
    have := W.smul_mem c⁻¹ hw0W
    have e : c⁻¹ • w0 = ⟨1, h1mem⟩ := Subtype.ext (by
      show c⁻¹ • w0.1 = 1
      rw [hc]
      simp [smul_eq_C_mul, ← C_mul, inv_mul_cancel₀ hc0])
    rwa [e] at this
  have hpow : ∀ i (hi : i < p), (⟨X ^ i, by
      rw [mem_degreeLT]; exact (degree_X_pow_le i).trans_lt (by exact_mod_cast hi)⟩ :
        WeylPSpace k p) ∈ W := by
    intro i
    induction i with
    | zero => intro _; simpa using hone
    | succ i ih =>
      intro hi
      have := hx _ (ih (by omega))
      rwa [weylXV_X_pow a i hi] at this
  rw [eq_top_iff]
  intro f _
  have hf := mem_degreeLT.1 f.2
  have hnd : f.1.natDegree < p := by
    rcases eq_or_ne f.1 0 with h | h
    · rw [h]; simpa using hp
    · exact (natDegree_lt_iff_degree_lt h).2 hf
  have hsum : f.1 = ∑ i ∈ Finset.range p, f.1.coeff i • X ^ i := by
    conv_lhs => rw [as_sum_range' f.1 p hnd]
    simp [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
  have : f = ∑ i ∈ Finset.range p, if h : i < p then f.1.coeff i • (⟨X ^ i, by
      rw [mem_degreeLT]; exact (degree_X_pow_le i).trans_lt (by exact_mod_cast h)⟩ :
        WeylPSpace k p) else 0 := by
    refine Subtype.ext ?_
    conv_lhs => rw [hsum]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [dif_pos (Finset.mem_range.1 hi)]
    rfl
  rw [this]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [dif_pos (Finset.mem_range.1 hi)]
  exact W.smul_mem _ (hpow i (Finset.mem_range.1 hi))

end

section Classification

variable {k : Type*} [Field k] [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- Schur-type lemma: an endomorphism commuting with `X` and `Y` acts as a scalar when `V` has no
proper nonzero subspace stable under `X` and `Y`. -/
theorem exists_scalar_of_commute (X Y T : Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ w ∈ W, X w ∈ W) → (∀ w ∈ W, Y w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX : T * X = X * T) (hY : T * Y = Y * T) : ∃ μ : k, T = μ • (1 : Module.End k V) := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  have hne : T.eigenspace μ ≠ ⊥ := hμ
  have hinv : ∀ S : Module.End k V, T * S = S * T → ∀ w ∈ T.eigenspace μ, S w ∈ T.eigenspace μ := by
    intro S hS w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    have := congrArg (fun F => F w) hS
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_smul]
  have htop := (hirr _ (hinv X hX) (hinv Y hY)).resolve_left hne
  refine ⟨μ, LinearMap.ext fun w => ?_⟩
  have : w ∈ T.eigenspace μ := by rw [htop]; trivial
  simpa [Module.End.mem_eigenspace_iff] using this

/-- Abstract form of the dimension count: if `Y X = X Y + 1` on a finite-dimensional space over an
algebraically closed field of characteristic `p`, with `Y^j X = X Y^j + j Y^(j-1)`, and no
proper nonzero subspace is stable under `X` and `Y`, then the dimension is `p`. -/
theorem finrank_eq_of_irreducible {p : ℕ} [Fact p.Prime] [CharP k p] (X Y : Module.End k V)
    (hYX : Y * X = X * Y + 1)
    (hpow : ∀ j : ℕ, Y ^ j * X = X * Y ^ j + j • Y ^ (j - 1))
    (hirr : ∀ W : Submodule k V, (∀ w ∈ W, X w ∈ W) → (∀ w ∈ W, Y w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank k V = p := by
  have hp := (Fact.out : p.Prime).pos
  -- lower bound by the trace
  have hdvd : p ∣ Module.finrank k V := by
    have h1 : LinearMap.trace k V (Y * X - X * Y) = Module.finrank k V := by
      have : Y * X - X * Y = 1 := by rw [hYX]; abel
      rw [this, LinearMap.trace_one]
    rw [map_sub, LinearMap.trace_mul_comm, sub_self] at h1
    exact (CharP.cast_eq_zero_iff k p _).1 h1.symm
  have hpos : 0 < Module.finrank k V := Module.finrank_pos
  have hge : p ≤ Module.finrank k V := Nat.le_of_dvd hpos hdvd
  -- `Y^p` is a scalar
  have hYp : ∃ μ : k, Y ^ p = μ • (1 : Module.End k V) := by
    refine exists_scalar_of_commute X Y (Y ^ p) hirr ?_ ?_
    · rw [hpow, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul, add_zero]
    · exact (Commute.self_pow Y p).eq.symm
  obtain ⟨μ, hμ⟩ := hYp
  -- upper bound via an eigenvector of `X`
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue X
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hXv : X v = α • v := Module.End.mem_eigenspace_iff.1 hv.1
  set W : Submodule k V := Submodule.span k (Set.range fun j : ℕ => (Y ^ j) v) with hW
  have hXY : ∀ j : ℕ, X ((Y ^ j) v) = α • (Y ^ j) v - j • (Y ^ (j - 1)) v := by
    intro j
    have h := congrArg (fun F => F v) (hpow j)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, hXv, map_smul] at h
    rw [h]; abel
  have hgen : ∀ j : ℕ, (Y ^ j) v ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hXW : ∀ w ∈ W, X w ∈ W := by
    have : W ≤ W.comap X := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show X ((Y ^ j) v) ∈ W
      rw [hXY]
      exact W.sub_mem (W.smul_mem _ (hgen j)) (nsmul_mem (hgen _) _)
    exact fun w hw => this hw
  have hYW : ∀ w ∈ W, Y w ∈ W := by
    have : W ≤ W.comap Y := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Y ((Y ^ j) v) ∈ W
      have : Y ((Y ^ j) v) = (Y ^ (j + 1)) v := by rw [pow_succ']; rfl
      rw [this]; exact hgen _
    exact fun w hw => this hw
  have hWtop : W = ⊤ := by
    refine (hirr W hXW hYW).resolve_left fun h => hv.2 ?_
    have := hgen 0
    rw [h] at this
    simpa using this
  set U : Submodule k V := Submodule.span k (Set.range fun j : Fin p => (Y ^ (j : ℕ)) v) with hU
  have hYpv : (Y ^ p) v = μ • v := by rw [hμ]; simp
  have hmemU : ∀ j : ℕ, (Y ^ j) v ∈ U := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      by_cases hj : j < p
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · have e : (Y ^ j) v = μ • (Y ^ (j - p)) v := by
          conv_lhs => rw [show j = (j - p) + p by omega, pow_add, Module.End.mul_apply, hYpv,
            map_smul]
        rw [e]
        exact U.smul_mem _ (ih _ (by omega))
  have hUtop : U = ⊤ := by
    rw [eq_top_iff, ← hWtop]
    exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hmemU j)
  have hle : Module.finrank k V ≤ p := by
    have := finrank_range_le_card (R := k) (fun j : Fin p => (Y ^ (j : ℕ)) v)
    unfold Set.finrank at this
    rw [← hU, hUtop, finrank_top] at this
    simpa using this
  exact le_antisymm hle hge

/-- `yʲ x = x yʲ + j yʲ⁻¹` from `y x = x y + 1` in any ring. -/
theorem y_pow_mul_x_of_rel {A : Type*} [Ring A] (x y : A) (h : y * x = x * y + 1) (j : ℕ) :
    y ^ j * x = x * y ^ j + j • y ^ (j - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rcases j with _ | j
    · simp [h]
    · rw [pow_succ, mul_assoc, h, mul_add, ← mul_assoc, ih]
      simp only [Nat.add_sub_cancel, add_mul, smul_mul_assoc, mul_one, mul_assoc,
        ← pow_succ, add_smul, one_smul]
      abel

/-- Problem 1.26(b), classification: over an algebraically closed field of characteristic `p`,
every irreducible finite-dimensional representation of the Weyl algebra (no proper nonzero
invariant subspace) has dimension exactly `p`. -/
@[kb "etingof2011" "Problem 1.26, p. 12"]
theorem weyl_irrep_finrank {p : ℕ} [Fact p.Prime] [CharP k p]
    (ρ : WeylAlgebra k →ₐ[k] Module.End k V)
    (hirr : ∀ W : Submodule k V, (∀ z : WeylAlgebra k, ∀ w ∈ W, ρ z w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank k V = p := by
  have hrel : ρ (weylY k) * ρ (weylX k) = ρ (weylX k) * ρ (weylY k) + 1 := by
    rw [← map_mul, ← map_mul, ← map_one ρ, ← map_add, weylY_mul_weylX]
  refine finrank_eq_of_irreducible (ρ (weylX k)) (ρ (weylY k)) hrel
    (y_pow_mul_x_of_rel _ _ hrel) ?_
  intro W hx hy
  refine hirr W fun z => ?_
  have hpowW : ∀ F : Module.End k V, (∀ w ∈ W, F w ∈ W) → ∀ n : ℕ, ∀ w ∈ W, (F ^ n) w ∈ W := by
    intro F hF n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih => intro w hw; rw [pow_succ', Module.End.mul_apply]; exact hF _ (ih w hw)
  let S : Submodule k (WeylAlgebra k) :=
    { carrier := {z | ∀ w ∈ W, ρ z w ∈ W}
      add_mem' := fun ha hb w hw => by simpa using W.add_mem (ha w hw) (hb w hw)
      zero_mem' := fun w hw => by simp
      smul_mem' := fun c z hz w hw => by simpa using W.smul_mem c (hz w hw) }
  have hle : (⊤ : Submodule k (WeylAlgebra k)) ≤ S := by
    rw [← weyl_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩ w hw
    show ρ (weylX k ^ i * weylY k ^ j) w ∈ W
    rw [map_mul, map_pow, map_pow, Module.End.mul_apply]
    exact hpowW _ hx i _ (hpowW _ hy j w hw)
  exact fun w hw => hle (Submodule.mem_top (x := z)) w hw

end Classification

end UndergradKB.RepresentationTheory
