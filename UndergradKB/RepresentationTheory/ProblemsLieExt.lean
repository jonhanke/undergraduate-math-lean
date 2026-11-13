import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.GroupTheory.QuotientGroup.Basic
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.Extensions

/-! # Problems 1.57 (positive characteristic) and 2.22(a) (Etingof et al.)

* `aff1_irrep_char_p`, `aff1_lie_theorem_fails` (Problem 1.57, characteristic `p`): over a field of
  characteristic `p` the operators `X = diag(0, 1, ..., p-1)` and the cyclic shift `Y` on `k^p` satisfy
  `[X, Y] = Y` and are irreducible, so Lie's theorem fails.  The classification of all irreducibles
  (dimension `1` or `p`) is not formalized.
* `ext_charRep_ne`, `ext_charRep_eq` (Problem 2.22(a)): `Ext^1` between one-dimensional
  representations of `k[x_1, ..., x_n]`, in the cocycle model of `Extensions.lean` (where `V` is the
  sub and `W` the quotient): it is trivial for `a ≠ b` and `k^n` for `a = b`.
-/

namespace UndergradKB.RepresentationTheory

/-! ### Problem 1.57, characteristic `p` -/

section Aff1CharP

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- The scalar `i ∈ ZMod p` viewed in `k`. -/
noncomputable abbrev zc (i : ZMod p) : k := ZMod.castHom (dvd_refl p) k i

/-- `X = diag(0, 1, ..., p-1)` on `k^(ZMod p)`. -/
noncomputable def aff1XModP : Module.End k (ZMod p → k) :=
  Algebra.lmul k (ZMod p → k) (fun i => zc p k i)

/-- The cyclic shift `e_j ↦ e_{j+1}`. -/
noncomputable def aff1YModP : Module.End k (ZMod p → k) :=
  LinearMap.funLeft k k (fun i : ZMod p => i - 1)

variable {p k}

theorem aff1XModP_apply (f : ZMod p → k) (i : ZMod p) : aff1XModP p k f i = zc p k i * f i := by
  simp [aff1XModP]

theorem aff1YModP_apply (f : ZMod p → k) (i : ZMod p) : aff1YModP p k f i = f (i - 1) := by
  simp [aff1YModP]

theorem aff1_comm : aff1XModP p k * aff1YModP p k - aff1YModP p k * aff1XModP p k = aff1YModP p k := by
  refine LinearMap.ext fun f => funext fun i => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, aff1XModP_apply, aff1YModP_apply,
    map_sub, map_one]
  ring

theorem aff1YModP_single (j : ZMod p) :
    aff1YModP p k (Pi.single j 1) = Pi.single (j + 1) 1 := by
  funext i
  rw [aff1YModP_apply]
  simp only [Pi.single_apply, sub_eq_iff_eq_add]

theorem aeval_aff1XModP_apply (q : Polynomial k) (f : ZMod p → k) (m : ZMod p) :
    Polynomial.aeval (aff1XModP p k) q f m = q.eval (zc p k m) * f m := by
  have h1 : Polynomial.aeval (aff1XModP p k) q =
      Algebra.lmul k (ZMod p → k) (Polynomial.aeval (fun i => zc p k i) q) := by
    unfold aff1XModP
    exact Polynomial.aeval_algHom_apply _ _ _
  have h2 := Polynomial.aeval_algHom_apply (Pi.evalAlgHom k (fun _ : ZMod p => k) m)
    (fun i => zc p k i) q
  simp only [Pi.evalAlgHom_apply] at h2
  rw [h1]
  simp [h2, Polynomial.coe_aeval_eq_eval]

theorem aeval_aff1XModP_mem (W : Submodule k (ZMod p → k)) (hX : ∀ w ∈ W, aff1XModP p k w ∈ W)
    (q : Polynomial k) {w : ZMod p → k} (hw : w ∈ W) : Polynomial.aeval (aff1XModP p k) q w ∈ W := by
  have hpow : ∀ n : ℕ, ∀ w ∈ W, ((aff1XModP p k) ^ n) w ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hX w hw)
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact add_mem hp hq
  | monomial n r =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply]
    simpa using W.smul_mem r (hpow n w hw)

/-- Irreducibility of the shift/diagonal pair in characteristic `p`. -/
theorem aff1_char_p_irreducible (W : Submodule k (ZMod p → k)) (hX : W.map (aff1XModP p k) ≤ W)
    (hY : W.map (aff1YModP p k) ≤ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hX' : ∀ w ∈ W, aff1XModP p k w ∈ W := fun w hw => hX ⟨w, hw, rfl⟩
  have hY' : ∀ w ∈ W, aff1YModP p k w ∈ W := fun w hw => hY ⟨w, hw, rfl⟩
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  set q : Polynomial k := ∏ i ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (zc p k i)) with hq
  have hv := aeval_aff1XModP_mem W hX' q hwW
  have hqj : q.eval (zc p k j) ≠ 0 := by
    rw [hq, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    intro h
    exact hij.symm ((ZMod.castHom (dvd_refl p) k).injective (sub_eq_zero.mp h))
  have hvv : Polynomial.aeval (aff1XModP p k) q w = (q.eval (zc p k j) * w j) • Pi.single j (1 : k) := by
    funext m
    rw [aeval_aff1XModP_apply]
    by_cases hm : m = j
    · subst hm; simp
    · have : q.eval (zc p k m) = 0 := by
        rw [hq, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩) (by simp)
      simp [hm]
      exact Or.inl this
  have hej : (Pi.single j (1 : k) : ZMod p → k) ∈ W := by
    have hr : (q.eval (zc p k j) * w j) ≠ 0 := mul_ne_zero hqj hj
    have := W.smul_mem (q.eval (zc p k j) * w j)⁻¹ hv
    rw [hvv, smul_smul, inv_mul_cancel₀ hr, one_smul] at this
    exact this
  have hall : ∀ n : ℕ, (Pi.single (j + n) (1 : k) : ZMod p → k) ∈ W := by
    intro n
    induction n with
    | zero => simpa using hej
    | succ n ih =>
      have := hY' _ ih
      rw [aff1YModP_single] at this
      simpa [add_assoc] using this
  have hi : ∀ i : ZMod p, (Pi.single i (1 : k) : ZMod p → k) ∈ W := by
    intro i
    have := hall (i - j).val
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
  rw [eq_top_iff, ← (Pi.basisFun k (ZMod p)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simpa [Pi.basisFun_apply] using hi i

variable (p k)

/-- **Etingof et al., Problem 1.57 (characteristic `p`)**: over a field of characteristic `p`, the
operators `X = diag(0, ..., p-1)` and the cyclic shift `Y` on `k^p` satisfy `[X, Y] = Y`, have no common
invariant subspaces other than `0` and `k^p`, `Y ≠ 0`, and the dimension is `p > 1`. -/
@[kb "etingof2011" "Problem 1.57, p. 22"]
theorem aff1_irrep_char_p :
    ∃ X Y : Module.End k (ZMod p → k), X * Y - Y * X = Y ∧
      (∀ W : Submodule k (ZMod p → k), W.map X ≤ W → W.map Y ≤ W → W = ⊥ ∨ W = ⊤) ∧
      Module.finrank k (ZMod p → k) = p ∧ 1 < p ∧ Y ≠ 0 := by
  refine ⟨aff1XModP p k, aff1YModP p k, aff1_comm, aff1_char_p_irreducible, ?_,
    (Fact.out : p.Prime).one_lt, ?_⟩
  · simp [Module.finrank_fintype_fun_eq_card]
  · intro h
    have := congrArg (fun T : Module.End k (ZMod p → k) => T (Pi.single 0 1) 1) h
    simp only [aff1YModP_apply, LinearMap.zero_apply, Pi.zero_apply] at this
    simp at this

/-- **Lie's theorem fails in positive characteristic** (Problem 1.57): it is false that every
irreducible pair `X, Y` with `[X, Y] = Y` on `k^p` is one-dimensional. -/
@[kb "etingof2011" "Problem 1.57, p. 22"]
theorem aff1_lie_theorem_fails :
    ¬ ∀ X Y : Module.End k (ZMod p → k), X * Y - Y * X = Y →
      (∀ W : Submodule k (ZMod p → k), W.map X ≤ W → W.map Y ≤ W → W = ⊥ ∨ W = ⊤) →
      Module.finrank k (ZMod p → k) = 1 := by
  intro h
  obtain ⟨X, Y, h1, h2, h3, h4, -⟩ := aff1_irrep_char_p p k
  have := h X Y h1 h2
  omega

end Aff1CharP

/-! ### Problem 2.22(a) -/

section Ext22

open Extensions

section Generic

variable {k A V W : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρV : A →ₐ[k] Module.End k V} {ρW : A →ₐ[k] Module.End k W}

theorem isCocycle_sub {c c' : A →ₗ[k] (W →ₗ[k] V)} (hc : IsCocycle ρV ρW c)
    (hc' : IsCocycle ρV ρW c') : IsCocycle ρV ρW (c - c') := by
  intro a b
  refine LinearMap.ext fun w => ?_
  have h1 := LinearMap.congr_fun (hc a b) w
  have h2 := LinearMap.congr_fun (hc' a b) w
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub] at h1 h2 ⊢
  rw [h1, h2]
  abel

/-- If every cocycle is a coboundary then `ExtOne` is trivial. -/
theorem subsingleton_extOne (h : ∀ c, IsCocycle ρV ρW c → c ∈ coboundaries ρV ρW) :
    Subsingleton (ExtOne ρV ρW) := by
  refine ⟨fun x y => ?_⟩
  induction x using QuotientAddGroup.induction_on with | _ x => ?_
  induction y using QuotientAddGroup.induction_on with | _ y => ?_
  rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
  have := (coboundaries ρV ρW).add_mem ((coboundaries ρV ρW).neg_mem (h x.1 x.2)) (h y.1 y.2)
  simpa using this

/-- If there are no nonzero coboundaries and the cocycles are linearly equivalent to `M`, then `ExtOne ≃+ M`. -/
theorem nonempty_extOne_equiv (hb : coboundaries ρV ρW = ⊥) {M : Type*} [AddCommGroup M] [Module k M]
    (e : cocycles ρV ρW ≃ₗ[k] M) : Nonempty (ExtOne ρV ρW ≃+ M) := by
  refine ⟨(QuotientAddGroup.quotientAddEquivOfEq ?_).trans
    ((QuotientAddGroup.quotientBot).trans e.toAddEquiv)⟩
  rw [hb]
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  rw [AddSubgroup.mem_comap] at hx
  exact Subtype.ext (by simpa using hx)

end Generic

variable {n : ℕ} {k : Type*} [Field k]

/-- The one-dimensional representation `V_a` of `k[x_1, ..., x_n]` with `x_i` acting by `a_i`. -/
noncomputable def charRep (a : Fin n → k) : MvPolynomial (Fin n) k →ₐ[k] Module.End k k :=
  (Algebra.lsmul k k k).comp (MvPolynomial.aeval a)

theorem charRep_apply (a : Fin n → k) (f : MvPolynomial (Fin n) k) (v : k) :
    charRep a f v = MvPolynomial.aeval a f * v := by
  simp [charRep]

variable {a b : Fin n → k} {c : MvPolynomial (Fin n) k →ₗ[k] (k →ₗ[k] k)}

theorem charRep_cocycle_val (hc : IsCocycle (charRep a) (charRep b) c) (f g : MvPolynomial (Fin n) k) :
    c (f * g) 1 = MvPolynomial.aeval a f * c g 1 + c f 1 * MvPolynomial.aeval b g := by
  have h := LinearMap.congr_fun (hc f g) 1
  simp only [LinearMap.add_apply, LinearMap.comp_apply, charRep_apply, mul_one] at h
  have h2 : c f (MvPolynomial.aeval b g) = MvPolynomial.aeval b g * c f 1 := by
    simpa using (c f).map_smul (MvPolynomial.aeval b g) 1
  rw [h, h2, mul_comm (MvPolynomial.aeval b g)]

theorem charRep_cocycle_apply (f : MvPolynomial (Fin n) k) (w : k) : c f w = w * c f 1 := by
  simpa using (c f).map_smul w 1

theorem charRep_cocycle_eq_zero (hc : IsCocycle (charRep a) (charRep b) c)
    (h : ∀ i, c (MvPolynomial.X i) 1 = 0) : c = 0 := by
  have h1 : c 1 1 = 0 := by simp [hc.map_one]
  have key : ∀ f, c f 1 = 0 := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.C_eq_smul_one, map_smul, LinearMap.smul_apply, h1, smul_zero]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [charRep_cocycle_val hc, hp, h]; simp
  refine LinearMap.ext fun f => LinearMap.ext fun w => ?_
  rw [charRep_cocycle_apply, key]; simp

theorem charRep_cocycle_rel (hc : IsCocycle (charRep a) (charRep b) c) (i j : Fin n) :
    (a i - b i) * c (MvPolynomial.X j) 1 = (a j - b j) * c (MvPolynomial.X i) 1 := by
  have h1 := charRep_cocycle_val hc (MvPolynomial.X i) (MvPolynomial.X j)
  have h2 := charRep_cocycle_val hc (MvPolynomial.X j) (MvPolynomial.X i)
  rw [mul_comm] at h2
  rw [h1] at h2
  simp only [MvPolynomial.aeval_X] at h2
  linear_combination h2

/-- For `a ≠ b`, every cocycle is a coboundary. -/
theorem charRep_cocycle_mem_coboundaries_of_ne (hab : a ≠ b)
    (hc : IsCocycle (charRep a) (charRep b) c) : c ∈ coboundaries (charRep a) (charRep b) := by
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ b i := by
    by_contra h; push Not at h; exact hab (funext h)
  have hne : a i0 - b i0 ≠ 0 := sub_ne_zero.mpr hi0
  set t : k := c (MvPolynomial.X i0) 1 / (a i0 - b i0) with ht
  let f : k →ₗ[k] k := t • LinearMap.id
  have hcob : coboundaryMap (charRep a) (charRep b) f ∈ coboundaries (charRep a) (charRep b) :=
    ⟨f, rfl⟩
  have hcobc := coboundaries_le_cocycles (charRep a) (charRep b) hcob
  have hval : ∀ i, coboundaryMap (charRep a) (charRep b) f (MvPolynomial.X i) 1 =
      (a i - b i) * t := by
    intro i
    simp [coboundaryMap, charRep_apply, f]
    ring
  have hd : c - coboundaryMap (charRep a) (charRep b) f ∈ cocycles (charRep a) (charRep b) :=
    isCocycle_sub hc hcobc
  have hrel : ∀ j, (c - coboundaryMap (charRep a) (charRep b) f) (MvPolynomial.X j) 1 = 0 := by
    intro j
    have h0 : (c - coboundaryMap (charRep a) (charRep b) f) (MvPolynomial.X i0) 1 = 0 := by
      simp only [LinearMap.sub_apply, hval]
      rw [ht]; field_simp; ring
    have := charRep_cocycle_rel (c := c - coboundaryMap (charRep a) (charRep b) f) hd i0 j
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hne
  have := charRep_cocycle_eq_zero hd hrel
  have hcc : c = coboundaryMap (charRep a) (charRep b) f := by
    refine LinearMap.ext fun g => LinearMap.ext fun w => ?_
    have h := LinearMap.congr_fun (LinearMap.congr_fun this g) w
    simpa [sub_eq_zero] using h
  rw [hcc]; exact hcob

/-- **Etingof et al., Problem 2.22(a), case `a ≠ b`**: `Ext^1(V_b, V_a)` (in the cocycle model, with `V_a`
the sub and `V_b` the quotient) vanishes. -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem ext_charRep_ne (hab : a ≠ b) : Subsingleton (ExtOne (charRep a) (charRep b)) := by
  exact subsingleton_extOne fun c hc => charRep_cocycle_mem_coboundaries_of_ne hab hc

/-- For `a = b` there are no nonzero coboundaries. -/
theorem coboundaries_charRep_self (a : Fin n → k) :
    coboundaries (charRep a) (charRep a) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro _ ⟨f, rfl⟩
  refine LinearMap.ext fun g => LinearMap.ext fun w => ?_
  simp only [coboundaryLin, coboundaryMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    LinearMap.comp_apply, charRep_apply, LinearMap.zero_apply]
  have := f.map_smul (MvPolynomial.aeval a g) w
  simp only [smul_eq_mul] at this
  rw [this]; ring

/-- The value-at-generators map on cocycles. -/
noncomputable def cocycleVals (a b : Fin n → k) :
    cocycles (charRep a) (charRep b) →ₗ[k] (Fin n → k) where
  toFun c i := c.1 (MvPolynomial.X i) 1
  map_add' c d := by funext i; simp
  map_smul' r c := by funext i; simp

/-- For `a = b` the cocycles are linearly equivalent to `k^n` (values on the generators). -/
noncomputable def cocycleEquivSelf (a : Fin n → k) :
    cocycles (charRep a) (charRep a) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofBijective (cocycleVals a a) (by
    classical
    constructor
    · intro c d hcd
      apply Subtype.ext
      have h0 := charRep_cocycle_eq_zero (isCocycle_sub c.2 d.2) fun i => by
        have := congr_fun hcd i
        simp only [cocycleVals, LinearMap.coe_mk, AddHom.coe_mk] at this
        simp [this]
      exact sub_eq_zero.mp h0
    · intro d
      let D : MvPolynomial (Fin n) k →ₗ[k] k :=
        ∑ i, d i • ((MvPolynomial.aeval a).toLinearMap ∘ₗ
          (MvPolynomial.pderiv i : Derivation k _ _).toLinearMap)
      have hD : ∀ f, D f = ∑ i, d i * MvPolynomial.aeval a (MvPolynomial.pderiv i f) := by
        intro f; simp [D]
      let c : MvPolynomial (Fin n) k →ₗ[k] (k →ₗ[k] k) := D.smulRight LinearMap.id
      have hc : IsCocycle (charRep a) (charRep a) c := by
        intro f g
        refine LinearMap.ext fun w => ?_
        simp only [c, LinearMap.smulRight_apply, LinearMap.add_apply, LinearMap.comp_apply,
          charRep_apply, LinearMap.id_apply, LinearMap.smul_apply, smul_eq_mul, hD,
          Derivation.leibniz, map_add, map_mul]
        simp only [smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      refine ⟨⟨c, hc⟩, ?_⟩
      funext j
      simp [cocycleVals, c, hD, MvPolynomial.pderiv_X, Pi.single_apply])

/-- **Etingof et al., Problem 2.22(a), case `a = b`**: the coboundaries vanish and the cocycles (hence
`Ext^1(V_a, V_a)`) are `n`-dimensional: `Ext^1` is additively isomorphic to `k^n`. -/
@[kb "etingof2011" "Problem 2.22, p. 30"]
theorem ext_charRep_eq (a : Fin n → k) :
    Nonempty (ExtOne (charRep a) (charRep a) ≃+ (Fin n → k)) := by
  exact nonempty_extOne_equiv (coboundaries_charRep_self a) (cocycleEquivSelf a)

/-- For `a = b` the cocycle space has dimension `n`. -/
theorem finrank_cocycles_charRep_self (a : Fin n → k) :
    Module.finrank k (cocycles (charRep a) (charRep a)) = n := by
  rw [(cocycleEquivSelf a).finrank_eq]; simp

end Ext22

end UndergradKB.RepresentationTheory
