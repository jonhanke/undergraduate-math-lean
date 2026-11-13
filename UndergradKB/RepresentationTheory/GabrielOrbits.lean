import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import UndergradKB.RepresentationTheory.GabrielConverseDefs
import UndergradKB.Common.Attr

/-! # Finitely many orbits cannot fill `Rep(d)` when `q(d) ≤ 0` (Etingof et al., Problem 5.4(a))

Let `d` be a nonzero dimension vector with `q(d) = ∑ d_i² - ∑_{arrows} d_i d_j ≤ 0`, i.e. the space `Rep(d)` of
tuples of matrices has dimension `N ≥ D = ∑ d_i² = dim ∏ GL(d_i)`. Over an infinite field we show that `Rep(d)` is
not a finite union of orbits of `∏ GL(d_i)` (`exists_not_equiv`). This replaces the book's appeal to dimensions of
algebraic varieties (Problem 5.2) by a transcendence degree count:

* fix a position `w₀` (an entry of one of the matrices `g_v`, `d_v > 0`) and let `R` be the polynomial ring in the
  `D - 1` other entries; the generic matrices `Gen_i` have entry `1` at `w₀`; in the localization `L = R[1/Δ]`,
  `Δ = ∏ det Gen_i`, the coordinates `φ` of `Gen_j x_a Gen_i⁻¹` are `N` elements of a ring of transcendence degree
  `D - 1 < N`, hence algebraically dependent: some nonzero polynomial `P` has `P(φ) = 0`;
* every point `g · x` of the orbit with `g_{w₀} ≠ 0` is a specialisation of `φ` (scale `g` so that its `w₀` entry is
  `1`, then evaluate `L → k`), so `P` vanishes there;
* multiplying over all `x` of the finite family and all positions `w₀` gives a nonzero polynomial vanishing on every
  orbit; over an infinite field it has a non-root.
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open scoped Classical
open MvPolynomial Cardinal

noncomputable section

universe u a

variable {k : Type u} [Field k] {n : ℕ} [Q : Quiver.{a} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

section Coordinates

variable (d : Fin n → ℕ)

/-- Index of the entries of a tuple of square matrices `g_i` of sizes `d_i`. -/
abbrev GVar := Σ i : Fin n, Fin (d i) × Fin (d i)

/-- Index of the coordinates of `Rep(d)`: an arrow `e : i → j` and an entry of the `d_j × d_i` matrix. -/
abbrev Crd := Σ i : Fin n, Σ j : Fin n, (i ⟶ j) × Fin (d j) × Fin (d i)

variable {d}

/-- The coordinates of a tuple of matrices. -/
def crdVal (x : MatRep k d) : Crd d → k := fun c => x c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2

/-- The tuple of matrices with given coordinates. -/
def ofCrd (f : Crd d → k) : MatRep k d := fun i j e r c => f ⟨i, j, e, r, c⟩

theorem crdVal_ofCrd (f : Crd d → k) : crdVal (ofCrd f) = f := by
  funext c; rfl

theorem card_GVar : Fintype.card (GVar d) = ∑ i, d i ^ 2 := by
  simp [GVar, Fintype.card_sigma, sq]

theorem card_Crd : Fintype.card (Crd d) = ∑ i, ∑ j, Fintype.card (i ⟶ j) * d j * d i := by
  simp [Crd, Fintype.card_sigma, Fintype.card_prod, mul_assoc]

end Coordinates

/-! ### The generic orbit map at a normalisation `w₀` -/

section Generic

variable (k) {d : Fin n → ℕ} (w₀ : GVar d)

/-- The polynomial ring in the entries other than `w₀`. -/
abbrev RingR := MvPolynomial {w : GVar d // w ≠ w₀} k

/-- The generic entry at `w`: the variable, or `1` at `w₀`. -/
def genEntry (w : GVar d) : RingR k w₀ := if h : w = w₀ then 1 else X ⟨w, h⟩

/-- The generic matrices. -/
def gen (i : Fin n) : Matrix (Fin (d i)) (Fin (d i)) (RingR k w₀) :=
  fun r c => genEntry k w₀ ⟨i, r, c⟩

/-- The product of the determinants of the generic matrices. -/
def genDet : RingR k w₀ := ∏ i, (gen k w₀ i).det

/-- The localization `R[1/Δ]`. -/
abbrev RingL := Localization.Away (genDet k w₀)

/-- The generic matrices over the localization. -/
def genL (i : Fin n) : Matrix (Fin (d i)) (Fin (d i)) (RingL k w₀) :=
  (gen k w₀ i).map (algebraMap _ _)

theorem isUnit_det_genL (i : Fin n) : IsUnit (genL k w₀ i).det := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := RingL k w₀) (genDet k w₀)
  have h' : IsUnit (∏ i, algebraMap (RingR k w₀) (RingL k w₀) (gen k w₀ i).det) := by
    rw [← map_prod]; exact h
  rw [IsUnit.prod_iff] at h'
  have := h' i (Finset.mem_univ _)
  rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this

/-- The generic orbit point `Gen_j x_a Gen_i⁻¹`, coordinatewise. -/
def genPoint (x : MatRep k d) : Crd d → RingL k w₀ := fun c =>
  (genL k w₀ c.2.1 * (x c.1 c.2.1 c.2.2.1).map (algebraMap k (RingL k w₀)) * (genL k w₀ c.1)⁻¹) c.2.2.2.1 c.2.2.2.2

/-- Transcendence degree count: if `q(d) ≤ 0` then the coordinates of the generic orbit point are algebraically
dependent (assuming the localization is a domain, i.e. `Δ ≠ 0`). -/
theorem not_algebraicIndependent_genPoint (hq : titsForm (fun i => (d i : ℤ)) ≤ 0) (hΔ : genDet k w₀ ≠ 0)
    (x : MatRep k d) : ¬ AlgebraicIndependent k (genPoint k w₀ x) := by
  intro hind
  have hle := hind.lift_cardinalMk_le_trdeg
  have hM : Submonoid.powers (genDet k w₀) ≤ nonZeroDivisors (RingR k w₀) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hΔ
  haveI : IsDomain (RingL k w₀) := IsLocalization.isDomain_localization hM
  haveI : FaithfulSMul (RingR k w₀) (RingL k w₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hM)
  haveI : Algebra.IsAlgebraic (RingR k w₀) (RingL k w₀) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers (genDet k w₀))
  have htr := trdeg_add_eq k (RingR k w₀) (A := RingL k w₀)
  rw [trdeg_eq_zero (R := RingR k w₀) (A := RingL k w₀), add_zero, MvPolynomial.trdeg_of_isDomain] at htr
  rw [← htr] at hle
  simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, Nat.cast_le] at hle
  -- `#{w ≠ w₀} = D - 1` and `#Crd = N ≥ D`
  have hcard : Fintype.card {w : GVar d // w ≠ w₀} + 1 = ∑ i, d i ^ 2 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← card_GVar]
    have : 0 < Fintype.card (GVar d) := Fintype.card_pos_iff.2 ⟨w₀⟩
    omega
  have hN := card_Crd (Q := Q) (d := d)
  unfold titsForm at hq
  have hq' : (∑ i, d i ^ 2 : ℤ) ≤ ∑ i, ∑ j, (Fintype.card (i ⟶ j) * d j * d i : ℕ) := by
    push_cast
    have e : ∑ i, ∑ j, (Fintype.card (i ⟶ j) : ℤ) * d i * d j =
        ∑ i, ∑ j, (Fintype.card (i ⟶ j) : ℤ) * d j * d i :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    linarith
  have : ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, Fintype.card (i ⟶ j) * d j * d i := by exact_mod_cast hq'
  omega

/-- The evaluation of the generic matrices at a tuple `g'` with entry `1` at `w₀`. -/
def evalAt (g' : GVar d → k) : RingR k w₀ →+* k := MvPolynomial.eval fun w => g' w.1

theorem evalAt_gen (g' : GVar d → k) (h1 : g' w₀ = 1) (i : Fin n) :
    (gen k w₀ i).map (evalAt k w₀ g') = fun r c => g' ⟨i, r, c⟩ := by
  ext r c
  simp only [Matrix.map_apply, gen, genEntry, evalAt]
  split_ifs with h
  · rw [map_one, ← h1, h]
  · simp

end Generic

/-! ### Vanishing on orbits -/

section Vanishing

variable {d : Fin n → ℕ}

/-- For one orbit and one normalisation position `w₀`, a nonzero polynomial on `Rep(d)` vanishing at every orbit point
`y` (with `y_a g_i = g_j x_a`) for which the `w₀` entry of `g` is nonzero. -/
theorem exists_poly_vanishing (hq : titsForm (fun i => (d i : ℤ)) ≤ 0) (w₀ : GVar d) (x : MatRep k d) :
    ∃ P : MvPolynomial (Crd d) k, P ≠ 0 ∧ ∀ (y : MatRep k d) (g : ∀ i, Matrix (Fin (d i)) (Fin (d i)) k),
      (∀ i, IsUnit (g i)) → (∀ i j (e : i ⟶ j), y i j e * g i = g j * x i j e) →
      g w₀.1 w₀.2.1 w₀.2.2 ≠ 0 → eval (crdVal y) P = 0 := by
  by_cases hΔ : genDet k w₀ = 0
  · -- no admissible `g` at all
    refine ⟨1, one_ne_zero, fun y g hg hy hw => ?_⟩
    exfalso
    set c := g w₀.1 w₀.2.1 w₀.2.2
    let g' : GVar d → k := fun w => c⁻¹ * g w.1 w.2.1 w.2.2
    have h1 : g' w₀ = 1 := by simp [g', c, inv_mul_cancel₀ hw]
    have hev := congrArg (evalAt k w₀ g') hΔ
    rw [show genDet k w₀ = ∏ i, (gen k w₀ i).det from rfl, map_prod, map_zero] at hev
    have : ∀ i, (evalAt k w₀ g') (gen k w₀ i).det ≠ 0 := by
      intro i
      rw [RingHom.map_det, RingHom.mapMatrix_apply, evalAt_gen k w₀ g' h1]
      have hgi : (fun r c' => g' ⟨i, r, c'⟩ : Matrix (Fin (d i)) (Fin (d i)) k) = c⁻¹ • g i := by
        ext r c'; simp [g']
      rw [hgi, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hw)) ((Matrix.isUnit_iff_isUnit_det _).1 (hg i)).ne_zero
    exact (Finset.prod_ne_zero_iff.2 fun i _ => this i) hev
  · obtain ⟨P, hP⟩ : ∃ P : MvPolynomial (Crd d) k, P ≠ 0 ∧ aeval (genPoint k w₀ x) P = 0 := by
      have h := not_algebraicIndependent_genPoint k w₀ hq hΔ x
      rw [algebraicIndependent_iff] at h
      push Not at h
      obtain ⟨P, h1, h2⟩ := h
      exact ⟨P, h2, h1⟩
    refine ⟨P, hP.1, fun y g hg hy hw => ?_⟩
    set c := g w₀.1 w₀.2.1 w₀.2.2
    let g' : GVar d → k := fun w => c⁻¹ * g w.1 w.2.1 w.2.2
    have h1 : g' w₀ = 1 := by simp [g', c, inv_mul_cancel₀ hw]
    let G' : ∀ i, Matrix (Fin (d i)) (Fin (d i)) k := fun i r c' => g' ⟨i, r, c'⟩
    have hG' : ∀ i, G' i = c⁻¹ • g i := fun i => by ext r c'; simp [G', g']
    have hGu : ∀ i, IsUnit (G' i) := fun i => by
      rw [hG', Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
      exact (IsUnit.mk0 _ (pow_ne_zero _ (inv_ne_zero hw))).mul ((Matrix.isUnit_iff_isUnit_det _).1 (hg i))
    -- the evaluation `L → k`
    have hunit : IsUnit (evalAt k w₀ g' (genDet k w₀)) := by
      rw [show genDet k w₀ = ∏ i, (gen k w₀ i).det from rfl, map_prod, IsUnit.prod_iff]
      intro i _
      rw [RingHom.map_det, RingHom.mapMatrix_apply, evalAt_gen k w₀ g' h1]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (hGu i)
    let ψ : RingL k w₀ →+* k := IsLocalization.Away.lift (genDet k w₀) hunit
    have hψ : ∀ r, ψ (algebraMap _ _ r) = evalAt k w₀ g' r :=
      IsLocalization.Away.lift_eq (genDet k w₀) hunit
    have hψk : ψ.comp (algebraMap k (RingL k w₀)) = RingHom.id k := by
      ext t
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [IsScalarTower.algebraMap_apply k (RingR k w₀), hψ]
      simp [evalAt]
    have hψgen : ∀ i, (genL k w₀ i).map ψ = G' i := fun i => by
      rw [genL, Matrix.map_map]
      have : (ψ ∘ algebraMap (RingR k w₀) (RingL k w₀)) = evalAt k w₀ g' := funext hψ
      rw [this, evalAt_gen k w₀ g' h1]
    have hψinv : ∀ i, ((genL k w₀ i)⁻¹).map ψ * G' i = 1 := fun i => by
      rw [← hψgen, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_det_genL k w₀ i), Matrix.map_one _ ψ.map_zero
        ψ.map_one]
    have hy' : ∀ i j (e : i ⟶ j), y i j e * G' i = G' j * x i j e := fun i j e => by
      rw [hG', hG', Matrix.mul_smul, Matrix.smul_mul, hy]
    have hψpt : ∀ cr, ψ (genPoint k w₀ x cr) = crdVal y cr := by
      rintro ⟨i, j, e, r, c'⟩
      simp only [genPoint, crdVal]
      have hmap : ((genL k w₀ j * (x i j e).map (algebraMap k (RingL k w₀)) * (genL k w₀ i)⁻¹).map ψ) =
          y i j e := by
        rw [Matrix.map_mul, Matrix.map_mul, hψgen, Matrix.map_map]
        have hx : ((x i j e).map (ψ ∘ algebraMap k (RingL k w₀))) = x i j e := by
          have : (ψ ∘ algebraMap k (RingL k w₀)) = id := by
            funext t; exact congrArg (fun f : k →+* k => f t) hψk
          rw [this, Matrix.map_id]
        rw [hx]
        -- `y = G'_j x G'_i⁻¹`
        have hinv : G' i * ((genL k w₀ i)⁻¹).map ψ = 1 :=
          mul_eq_one_comm.1 (hψinv i)
        calc G' j * x i j e * ((genL k w₀ i)⁻¹).map ψ
            = y i j e * G' i * ((genL k w₀ i)⁻¹).map ψ := by rw [hy']
          _ = y i j e := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
      exact congrFun (congrFun hmap r) c'
    have := congrArg ψ hP.2
    rw [map_zero, map_aeval, hψk] at this
    rw [← this]
    simp only [eval, coe_eval₂Hom]
    congr 1
    funext cr
    exact (hψpt cr).symm

/-- **Etingof et al., Problem 5.4(a)** (orbit count): over an infinite field, if `d ≠ 0` and `q(d) ≤ 0`, then
`Rep(d)` is not covered by finitely many orbits of `∏ GL(d_i)`. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem exists_not_equiv [Infinite k] (hd : d ≠ 0) (hq : titsForm (fun i => (d i : ℤ)) ≤ 0) {m : ℕ}
    (xs : Fin m → MatRep k d) : ∃ y : MatRep k d, ∀ t, ¬ MatRep.Equiv (xs t) y := by
  choose P hP0 hPv using fun (p : Fin m × GVar d) => exists_poly_vanishing (k := k) hq p.2 (xs p.1)
  set Ptot := ∏ p : Fin m × GVar d, P p with hPtot
  have hne : Ptot ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hP0 p
  obtain ⟨z, hz⟩ : ∃ z : Crd d → k, eval z Ptot ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (MvPolynomial.funext fun z => by rw [h z, map_zero])
  refine ⟨ofCrd z, fun t ⟨g, hg, hy⟩ => hz ?_⟩
  -- some entry of some `g_v` with `d_v > 0` is nonzero
  obtain ⟨v, hv⟩ : ∃ v, d v ≠ 0 := by
    by_contra h; push Not at h; exact hd (funext h)
  obtain ⟨r, c, hrc⟩ : ∃ r c, g v r c ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : g v = 0 := by ext r c; exact h r c
    have hu := hg v
    rw [h0] at hu
    haveI : Nonempty (Fin (d v)) := ⟨⟨0, Nat.pos_of_ne_zero hv⟩⟩
    exact not_isUnit_zero hu
  have := hPv (t, ⟨v, r, c⟩) (ofCrd z) g hg hy hrc
  rw [crdVal_ofCrd] at this
  rw [hPtot, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (t, ⟨v, r, c⟩)) this

end Vanishing

end

end UndergradKB.RepresentationTheory.Gabriel
