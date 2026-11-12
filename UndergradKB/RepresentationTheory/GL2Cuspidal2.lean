import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.FiniteAbelian.Duality
import UndergradKB.RepresentationTheory.GL2Cuspidal
import UndergradKB.Common.Attr

/-! # The count of irreducible representations of `GL_2(F_q)` (Etingof et al., §4.24.4 conclusion)

Continuation of `GL2Cuspidal`.  Throughout `h` is an irreducible monic quadratic `x² - t x + n` over the finite
field `F` and `K = torus h` is the nonsplit torus.

* The torus `K` is cyclic (`isCyclic_torus`), being a finite subgroup of the multiplicative group of the field
  `F[x]/(x² - t x + n)`.
* There are exactly `q - 1` characters `ν` of `K` with `ν^q = ν` (`card_nuPow_fixed`) and so `q² - q` with
  `ν^q ≠ ν` (`card_nuPow_ne`).
* Values of the cuspidal character `W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν` on elliptic, parabolic and hyperbolic
  elements (`cuspChar_torus`, `cuspChar_upper`, `cuspChar_diag`), and `cusp ν = cusp ν'` exactly when
  `ν' ∈ {ν, ν^q}` (`cusp_eq_iff`); hence there are `q(q-1)/2` cuspidal characters (`ncard_cuspSet`).
* The four families (the characters `μ ∘ det`, the characters of `W_μ`, the irreducible principal series, the
  cuspidal ones) consist of irreducible characters, are pairwise disjoint with `q - 1`, `q - 1`, `(q-1)(q-2)/2`,
  `q(q-1)/2` members, and since `q² - 1` is the number of conjugacy classes they exhaust all irreducible
  characters (`irrChars_GL2_eq`, `card_irrChars_GL2`).
-/

universe u

namespace UndergradKB.RepresentationTheory.GL2

open Matrix Representation Module ComplexConjugate Polynomial

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

section CyclicTorus

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- The monic quadratic `x² - t x + n`. -/
noncomputable def quadPoly (t n : F) : F[X] := X ^ 2 - C t * X + C n

lemma quadPoly_irreducible (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) : Irreducible (quadPoly t n) := by
  have hdeg : (quadPoly t n).natDegree = 2 := by
    unfold quadPoly; compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun x hx => ?_
  apply h x
  simpa [quadPoly, IsRoot] using hx

lemma torus_entries' (z : torus h) :
    ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = -(((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 * n) ∧
    ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 + ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 * t := by
  obtain ⟨a, b, -, hz⟩ := torus_entries h z.2
  rw [hz]; simp

lemma root_sq (t n : F) : (AdjoinRoot.root (quadPoly t n)) ^ 2 =
    AdjoinRoot.of (quadPoly t n) t * AdjoinRoot.root (quadPoly t n) - AdjoinRoot.of (quadPoly t n) n := by
  have h0 : AdjoinRoot.mk (quadPoly t n) (X ^ 2 - C t * X + C n) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h0
  linear_combination h0

/-- The embedding of the nonsplit torus into the field `F[x]/(x² - t x + n)`, `a + b C ↦ a + b x`. -/
noncomputable def torusToAdj : torus h →* AdjoinRoot (quadPoly t n) where
  toFun z := AdjoinRoot.of _ (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) +
    AdjoinRoot.of _ (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) * AdjoinRoot.root _
  map_one' := by simp
  map_mul' z w := by
    obtain ⟨hz01, hz11⟩ := torus_entries' h z
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hz01, hz11,
      map_add, map_mul, map_neg]
    linear_combination (-(AdjoinRoot.of (quadPoly t n) (((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) *
      AdjoinRoot.of (quadPoly t n) (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0))) * root_sq t n

lemma torusToAdj_injective : Function.Injective (torusToAdj h : torus h →* AdjoinRoot (quadPoly t n)) := by
  intro z w hzw
  have hmk : ∀ a b : F, AdjoinRoot.of (quadPoly t n) a + AdjoinRoot.of (quadPoly t n) b * AdjoinRoot.root _ =
      AdjoinRoot.mk (quadPoly t n) (C a + C b * X) := by
    intro a b
    simp [AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  simp only [torusToAdj, MonoidHom.coe_mk, OneHom.coe_mk, hmk] at hzw
  rw [AdjoinRoot.mk_eq_mk] at hzw
  have hdeg : (C (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) +
      C (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) * X -
      (C (((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) +
      C (((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) * X)).natDegree < (quadPoly t n).natDegree := by
    have h2 : (quadPoly t n).natDegree = 2 := by unfold quadPoly; compute_degree!
    rw [h2]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
    have : ∀ a b : F, (C a + C b * X).natDegree ≤ 1 := fun a b => by compute_degree
    have h3 := this (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0)
    have h4 := this (((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) (((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0)
    omega
  have h0 := eq_zero_of_dvd_of_natDegree_lt hzw hdeg
  have e : C (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 - ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0) +
      C (((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 - ((w : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) * X = 0 := by
    rw [← h0]; simp only [C_sub]; ring
  have c0 := congrArg (fun p : F[X] => p.coeff 0) e
  have c1 := congrArg (fun p : F[X] => p.coeff 1) e
  simp at c0 c1
  have e00 := sub_eq_zero.1 c0
  have e10 := sub_eq_zero.1 c1
  obtain ⟨hz01, hz11⟩ := torus_entries' h z
  obtain ⟨hw01, hw11⟩ := torus_entries' h w
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact e00
  · simp only [Fin.zero_eta, Fin.mk_one]; rw [hz01, hw01, e10]
  · exact e10
  · simp only [Fin.mk_one]; rw [hz11, hw11, e00, e10]

/-- **The nonsplit torus is cyclic** (it is a finite subgroup of the unit group of the field `F_{q²}`). -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem isCyclic_torus : IsCyclic (torus h) := by
  have : Fact (Irreducible (quadPoly t n)) := ⟨quadPoly_irreducible h⟩
  exact isCyclic_of_injective_ringHom (torusToAdj h) (torusToAdj_injective h)

end CyclicTorus

/-! ### Counting the characters `ν` with `ν^q = ν` -/

section CharCount

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- The nonsplit torus as a commutative group. -/
noncomputable abbrev torusCommGroup : CommGroup (torus h) :=
  { (inferInstance : Group (torus h)) with mul_comm := fun z w => Subtype.ext (torus_comm h z.2 w.2) }

lemma card_torus_dvd : Nat.card F - 1 ∣ Nat.card (torus h) := by
  rw [card_torus]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  refine ⟨Nat.card F + 1, ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by omega⟩
  rw [hr]
  simp only [Nat.add_sub_cancel]
  rw [show (r + 1) ^ 2 - 1 = r * (r + 2) by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]; ring]

lemma nuPow_eq_self_iff_pow (ν : torus h →* ℂˣ) :
    nuPow h ν = ν ↔ ν ^ (Nat.card F - 1) = 1 := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  constructor
  · intro hν
    refine MonoidHom.ext fun z => ?_
    have := congrArg (fun μ : torus h →* ℂˣ => μ z) hν
    simp only [nuPow_apply] at this
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have e : ν z ^ Nat.card F = ν z ^ (Nat.card F - 1) * ν z := by
      rw [← pow_succ]; congr 1; omega
    rw [e] at this
    exact mul_eq_right.1 this
  · intro hν
    refine MonoidHom.ext fun z => ?_
    have := congrArg (fun μ : torus h →* ℂˣ => μ z) hν
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at this
    rw [nuPow_apply]
    calc ν z ^ Nat.card F = ν z ^ (Nat.card F - 1) * ν z := by
          rw [← pow_succ]; congr 1; omega
      _ = ν z := by rw [this, one_mul]

/-- **Etingof et al., §4.24.4 conclusion**: the number of characters `ν` of the nonsplit torus with `ν^q = ν`
is `q - 1` (the torus is cyclic of order `q² - 1`). -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem card_nuPow_fixed : Nat.card {ν : torus h →* ℂˣ // nuPow h ν = ν} = Nat.card F - 1 := by
  letI := torusCommGroup h
  have hcyc : IsCyclic (torus h) := isCyclic_torus h
  have e := (IsCyclic.monoidHom_equiv_self (torus h) ℂ).some
  haveI : IsCyclic (torus h →* ℂˣ) := isCyclic_of_surjective e.symm e.symm.surjective
  have hN : Nat.card (torus h →* ℂˣ) = Nat.card (torus h) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (torus h) ℂ
  have hker := IsCyclic.card_powMonoidHom_ker (G := torus h →* ℂˣ) (Nat.card F - 1)
  rw [hN, Nat.gcd_eq_right (card_torus_dvd h)] at hker
  rw [← hker]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun ν => ?_)
  rw [nuPow_eq_self_iff_pow, MonoidHom.mem_ker]
  rfl

/-- The number of characters `ν` of the nonsplit torus with `ν^q ≠ ν` is `q² - q`. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem card_nuPow_ne : Nat.card {ν : torus h →* ℂˣ // nuPow h ν ≠ ν} = Nat.card F ^ 2 - Nat.card F := by
  letI := torusCommGroup h
  have hN : Nat.card (torus h →* ℂˣ) = Nat.card (torus h) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (torus h) ℂ
  have hfin : Finite (torus h →* ℂˣ) := Nat.finite_of_card_ne_zero (by rw [hN]; exact Nat.card_pos.ne')
  classical
  haveI := Fintype.ofFinite (torus h →* ℂˣ)
  have h2 := card_nuPow_fixed h
  have h1 := Fintype.card_subtype_compl (fun ν : torus h →* ℂˣ => nuPow h ν = ν)
  simp only [← Nat.card_eq_fintype_card] at h1
  rw [h2, hN, card_torus] at h1
  refine h1.trans ?_
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 1 := ⟨Nat.card F - 1, by omega⟩
  rw [hr]
  simp only [Nat.add_sub_cancel]
  rw [show (r + 1) ^ 2 - 1 = r * (r + 2) by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]; ring]
  rw [show (r + 1) ^ 2 - (r + 1) = r * (r + 1) by
    rw [Nat.sub_eq_iff_eq_add (by nlinarith)]; ring]
  exact Nat.sub_eq_of_eq_add (by ring)

end CharCount

/-! ### Values of the cuspidal characters and when two coincide -/

section Values

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- The inclusion of the scalars `F^×` into the nonsplit torus. -/
noncomputable def scalT : Fˣ →* torus h where
  toFun c := ⟨scal c, diag_mem_torus h c⟩
  map_one' := Subtype.ext scal_one
  map_mul' c d := Subtype.ext (scal_mul_scal c d)

/-- The restriction `α` of a character `ν` of the nonsplit torus to the scalars `F^×`. -/
noncomputable def resScal (ν : torus h →* ℂˣ) : Fˣ →* ℂˣ := ν.comp (scalT h)

lemma resScal_apply (ν : torus h →* ℂˣ) (c : Fˣ) :
    ν ⟨scal c, diag_mem_torus h c⟩ = resScal h ν c := rfl

/-- The cuspidal character attached to a character `ν` of the nonsplit torus (with `α` its restriction to the
scalars): the character of `W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν`. -/
noncomputable def cusp (ν : torus h →* ℂˣ) : GL (Fin 2) F → ℂ := cuspChar h (resScal h ν) ν

/-- Value of the cuspidal character on an elliptic (non-scalar) element of the nonsplit torus. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem cuspChar_torus (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ) {z : GL (Fin 2) F} (hz : z ∈ torus h)
    (hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    cuspChar h α ν z = -((ν ⟨z, hz⟩ : ℂ) + (ν (sigmaT h ⟨z, hz⟩) : ℂ)) := by
  rw [cuspChar_eq, phiV_noroot α, character_torusInd_torus h ν hz hz10]
  · ring
  · intro l hl
    exact hz10 (torus_val10_of_root h hz l hl)

/-- Value of the cuspidal character on a parabolic element. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem cuspChar_upper (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ) (x : Fˣ) :
    cuspChar h α ν (upperUnit x 1) = -(α x : ℂ) := by
  rw [cuspChar_eq, phiV_upper, character_torusInd_upper]; ring

/-- Value of the cuspidal character on a hyperbolic element. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem cuspChar_diag (α : Fˣ →* ℂˣ) (ν : torus h →* ℂˣ) {x y : Fˣ} (hxy : x ≠ y) :
    cuspChar h α ν (diagUnit x y) = 0 := by
  rw [cuspChar_eq, phiV_diag α hxy, character_torusInd_diag h ν hxy]; ring

lemma resScal_nuPow (ν : torus h →* ℂˣ) : resScal h (nuPow h ν) = resScal h ν := by
  refine MonoidHom.ext fun c => ?_
  show nuPow h ν (scalT h c) = ν (scalT h c)
  rw [← comp_sigmaT_eq_nuPow]
  exact congrArg ν (sigmaT_scal h c)

lemma nuPow_nuPow (ν : torus h →* ℂˣ) : nuPow h (nuPow h ν) = ν := by
  rw [← comp_sigmaT_eq_nuPow, ← comp_sigmaT_eq_nuPow]
  refine MonoidHom.ext fun z => ?_
  show ν (sigmaT h (sigmaT h z)) = ν z
  congr 1
  exact Subtype.ext (adjG_adjG _)

/-- The cuspidal characters of `ν` and of `ν^q` coincide. -/
theorem cusp_nuPow (ν : torus h →* ℂˣ) : cusp h (nuPow h ν) = cusp h ν := by
  funext g
  rw [cusp, cusp, cuspChar_eq, cuspChar_eq, resScal_nuPow, ← comp_sigmaT_eq_nuPow,
    character_torusInd_comp_sigma, char_adjG]

/-- Dedekind independence of characters, in the form needed: if `ν + ν' = μ + μ'` as functions and `μ ≠ μ'`,
then `μ` is `ν` or `ν'`. -/
lemma eq_or_eq_of_add_eq {K : Type*} [Monoid K] (a b c d : K →* ℂˣ) (hcd : c ≠ d)
    (hsum : ∀ z, (a z : ℂ) + b z = c z + d z) : c = a ∨ c = b := by
  classical
  have hLI : LinearIndependent ℂ (fun ν : K →* ℂˣ => fun z : K => (ν z : ℂ)) := by
    have := (linearIndependent_monoidHom K ℂ).comp (fun ν : K →* ℂˣ => (Units.coeHom ℂ).comp ν)
      (fun ν ν' hh => MonoidHom.ext fun z => Units.ext (DFunLike.congr_fun hh z))
    exact this
  have hl := linearIndependent_iff.1 hLI
    (Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single c 1 - Finsupp.single d 1) (by
      simp only [map_add, map_sub, Finsupp.linearCombination_single, one_smul]
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
      linear_combination hsum z)
  have hc := DFunLike.congr_fun hl c
  by_contra hne
  push Not at hne
  simp [hne.1.symm, hne.2.symm, hcd] at hc

lemma cast_card_sub_one_ne_zero : ((Nat.card F : ℂ) - 1) ≠ 0 := by
  rw [← cast_pred]
  have : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card]
  exact Nat.cast_ne_zero.2 (by omega)

/-- **Etingof et al., §4.24.4 conclusion**: for `ν^q ≠ ν` and `ν'^q ≠ ν'`, the cuspidal characters of `ν` and
`ν'` coincide exactly when `ν'` is `ν` or `ν^q`. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem cusp_eq_iff {ν ν' : torus h →* ℂˣ} (hν : nuPow h ν ≠ ν) (hν' : nuPow h ν' ≠ ν') :
    cusp h ν = cusp h ν' ↔ ν' = ν ∨ ν' = nuPow h ν := by
  constructor
  · intro hc
    have hres : resScal h ν = resScal h ν' := by
      refine MonoidHom.ext fun c => Units.ext ?_
      have e := congrFun hc (scal c)
      rw [cusp, cusp, cuspChar_scal h _ ν (fun c => rfl), cuspChar_scal h _ ν' (fun c => rfl)] at e
      exact mul_left_cancel₀ (cast_card_sub_one_ne_zero (F := F)) e
    have hsum : ∀ z : torus h, (ν z : ℂ) + ν (sigmaT h z) = ν' z + ν' (sigmaT h z) := by
      intro z
      by_cases hz10 : ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      · obtain ⟨c, hcz⟩ := torus_scal_of_val10 h z.2 hz10
        have hz : z = scalT h c := Subtype.ext hcz
        have e1 : sigmaT h z = z := by rw [hz]; exact sigmaT_scal h c
        rw [e1, hz]
        have := congrArg (fun α : Fˣ →* ℂˣ => (α c : ℂ)) hres
        simp only [resScal, MonoidHom.comp_apply] at this
        rw [this]
      · have e := congrFun hc z
        rw [cusp, cusp, cuspChar_torus h _ ν z.2 hz10, cuspChar_torus h _ ν' z.2 hz10] at e
        linear_combination -e
    have hne : ν'.comp (sigmaT h) ≠ ν' := by rw [comp_sigmaT_eq_nuPow]; exact hν'
    rcases eq_or_eq_of_add_eq ν (ν.comp (sigmaT h)) ν' (ν'.comp (sigmaT h)) hne.symm hsum with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1, comp_sigmaT_eq_nuPow])
  · rintro (rfl | rfl)
    · rfl
    · exact (cusp_nuPow h ν).symm

end Values

/-! ### Counting the cuspidal characters -/

section CuspCount

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

/-- If every fibre of `f` over the image of `s` has two points, then `s` has twice as many points as its image. -/
lemma card_eq_two_mul_card_image {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, (s.filter fun a' => f a' = f a).card = 2) : s.card = 2 * (s.image f).card := by
  rw [Finset.card_eq_sum_card_image f s,
    Finset.sum_congr rfl (g := fun _ => 2) (fun b hb => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
      exact hf a ha),
    Finset.sum_const, smul_eq_mul, mul_comm]

lemma finite_torusChars : Finite (torus h →* ℂˣ) := by
  letI := torusCommGroup h
  exact Nat.finite_of_card_ne_zero (by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]; exact Nat.card_pos.ne')

/-- The set of cuspidal characters `cusp ν` with `ν^q ≠ ν`. -/
def cuspSet : Set (GL (Fin 2) F → ℂ) := {ζ | ∃ ν : torus h →* ℂˣ, nuPow h ν ≠ ν ∧ cusp h ν = ζ}

/-- **Etingof et al., §4.24.4 conclusion**: the cuspidal characters `cusp ν` with `ν^q ≠ ν` are pairwise
distinct for distinct pairs `{ν, ν^q}`; there are `q(q-1)/2` of them (stated as `2 * #cuspSet = q² - q`). -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem ncard_cuspSet : 2 * (cuspSet h).ncard = Nat.card F ^ 2 - Nat.card F := by
  classical
  haveI := finite_torusChars h
  haveI := Fintype.ofFinite (torus h →* ℂˣ)
  set S : Finset (torus h →* ℂˣ) := Finset.univ.filter (fun ν => nuPow h ν ≠ ν) with hSdef
  have hS : S.card = Nat.card F ^ 2 - Nat.card F := by
    rw [← card_nuPow_ne h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : cuspSet h = ↑(S.image (cusp h)) := by
    ext ζ; simp [cuspSet, S]
  rw [hset, Set.ncard_coe_finset, ← hS]
  refine (card_eq_two_mul_card_image S (cusp h) ?_).symm
  intro a ha
  have ha' : nuPow h a ≠ a := (Finset.mem_filter.1 ha).2
  have hfib : S.filter (fun a' => cusp h a' = cusp h a) = {a, nuPow h a} := by
    ext a'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, S, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, he⟩
      exact (cusp_eq_iff h ha' hne).1 he.symm
    · rintro (rfl | rfl)
      · exact ⟨ha', rfl⟩
      · exact ⟨by rw [nuPow_nuPow]; exact ha'.symm, cusp_nuPow h a⟩
  rw [hfib, Finset.card_pair ha'.symm]

end CuspCount

/-! ### The other irreducible characters -/

section Others

open scoped ComplexOrder

/-- The character of the principal series representation `V_{λ₁,λ₂}`. -/
noncomputable abbrev psChar (l₁ l₂ : Fˣ →* ℂˣ) : GL (Fin 2) F → ℂ :=
  (principalSeries (F := F) l₁ l₂).character

/-- The character of the `q`-dimensional representation `W_μ`, the complement of the line `C_μ` in
`V_{μ,μ}`: `χ_{V_{μ,μ}} - μ ∘ det`. -/
noncomputable def wChar (μ : Fˣ →* ℂˣ) : GL (Fin 2) F → ℂ := fun g => psChar μ μ g - detCharC μ g

lemma psChar_one (l₁ l₂ : Fˣ →* ℂˣ) : psChar (F := F) l₁ l₂ 1 = ((Nat.card F + 1 : ℕ) : ℂ) := by
  have h1 := (principalSeries (F := F) l₁ l₂).char_one
  rw [finrank_principalSeries] at h1
  exact h1

lemma detCharC_one (μ : Fˣ →* ℂˣ) : detCharC (F := F) μ 1 = 1 := by simp [detCharC]

lemma detCharC_upper (μ : Fˣ →* ℂˣ) : detCharC (F := F) μ (upperUnit 1 1) = 1 := by
  have : GeneralLinearGroup.det (upperUnit (1 : Fˣ) 1 : GL (Fin 2) F) = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, det_upper]; simp
  simp [detCharC, this]

lemma psChar_upper (l₁ l₂ : Fˣ →* ℂˣ) : psChar (F := F) l₁ l₂ (upperUnit 1 1) = 1 := by
  exact (character_principalSeries_upper (F := F) l₁ l₂ 1).trans (by simp)

lemma wChar_one (μ : Fˣ →* ℂˣ) : wChar (F := F) μ 1 = (Nat.card F : ℂ) := by
  rw [wChar, psChar_one, detCharC_one]; push_cast; ring

lemma wChar_upper (μ : Fˣ →* ℂˣ) : wChar (F := F) μ (upperUnit 1 1) = 0 := by
  rw [wChar, psChar_upper, detCharC_upper]; ring

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

lemma cusp_one (ν : torus h →* ℂˣ) : cusp h ν 1 = (Nat.card F : ℂ) - 1 :=
  cuspChar_one h _ ν (fun _ => rfl)

lemma cusp_upper (ν : torus h →* ℂˣ) : cusp h ν (upperUnit 1 1) = -1 := by
  rw [cusp, cuspChar_upper]; simp

lemma two_ne_zero_complex : (2 : ℂ) ≠ 0 := two_ne_zero

lemma mem_irrChars_of_herm {ζ : GL (Fin 2) F → ℂ} (hv : ζ ∈ virtualChars ℂ (GL (Fin 2) F))
    (h1 : hermitianPairing ζ ζ = 1) (hpos : 0 < ζ 1) : ζ ∈ irrChars ℂ (GL (Fin 2) F) :=
  mem_irrChars_of_pairing_eq_one hv (by rw [pairing_eq_hermitianPairing hv]; exact h1) hpos

/-- The one-dimensional character `μ ∘ det` is an irreducible character. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem detCharC_mem_irrChars (μ : Fˣ →* ℂˣ) : detCharC (F := F) μ ∈ irrChars ℂ (GL (Fin 2) F) := by
  refine mem_irrChars_of_herm ?_ (hermitianPairing_detCharC μ) ?_
  · have : detCharC μ = (lineRep' ((Units.coeHom ℂ).comp (μ.comp GeneralLinearGroup.det) :
        GL (Fin 2) F →* ℂ)).character := by
      funext g; rw [character_lineRep']; rfl
    rw [this]; exact S4Table.character_mem_virtualChars _
  · rw [detCharC_one]; exact zero_lt_one

/-- The principal series character `χ_{V_{λ₁,λ₂}}` with `λ₁ ≠ λ₂` is an irreducible character. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem psChar_mem_irrChars {l₁ l₂ : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) :
    psChar (F := F) l₁ l₂ ∈ irrChars ℂ (GL (Fin 2) F) := by
  refine mem_irrChars_of_herm (S4Table.character_mem_virtualChars _)
    (hermitianPairing_principalSeries_self hne) ?_
  rw [psChar_one]; exact Nat.cast_pos.2 (Nat.succ_pos _)

lemma hermitianPairing_wChar (μ : Fˣ →* ℂˣ) : hermitianPairing (wChar (F := F) μ) (wChar μ) = 1 := by
  have hP : psChar μ μ = wChar μ + detCharC (F := F) μ := by funext g; simp [wChar]
  have h2 : hermitianPairing (psChar (F := F) μ μ) (psChar μ μ) = 2 :=
    hermitianPairing_principalSeries_diag (F := F) μ
  have h1 : hermitianPairing (psChar (F := F) μ μ) (detCharC μ) = 1 :=
    hermitianPairing_principalSeries_detCharC (F := F) μ
  have h1' : hermitianPairing (detCharC (F := F) μ) (psChar μ μ) = 1 := by
    rw [hermitianPairing_conj, h1, map_one]
  have hψ := hermitianPairing_detCharC (F := F) μ
  rw [hP] at h2 h1 h1'
  rw [hermitianPairing_add_left, hermitianPairing_add_right, hermitianPairing_add_right] at h2
  rw [hermitianPairing_add_left] at h1
  rw [hermitianPairing_add_right] at h1'
  linear_combination h2 - h1 - h1' + hψ

/-- The character of the `q`-dimensional representation `W_μ` is an irreducible character. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem wChar_mem_irrChars (μ : Fˣ →* ℂˣ) : wChar (F := F) μ ∈ irrChars ℂ (GL (Fin 2) F) := by
  refine mem_irrChars_of_herm ?_ (hermitianPairing_wChar μ) ?_
  · have : wChar μ = psChar μ μ - detCharC μ := rfl
    rw [this]
    exact Submodule.sub_mem _ (S4Table.character_mem_virtualChars _) (by
      have : detCharC μ = (lineRep' ((Units.coeHom ℂ).comp (μ.comp GeneralLinearGroup.det) :
          GL (Fin 2) F →* ℂ)).character := by
        funext g; rw [character_lineRep']; rfl
      rw [this]; exact S4Table.character_mem_virtualChars _)
  · rw [wChar_one]
    have : 1 < Fintype.card F := Fintype.one_lt_card
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_pos.2 (by omega)

/-- The cuspidal character is an irreducible character when `ν^q ≠ ν`. -/
theorem cusp_mem_irrChars {ν : torus h →* ℂˣ} (hν : nuPow h ν ≠ ν) :
    cusp h ν ∈ irrChars ℂ (GL (Fin 2) F) :=
  cuspChar_mem_irrChars h _ ν (fun c => rfl) (by rw [comp_sigmaT_eq_nuPow]; exact hν)

lemma hermitianPairing_detCharC_ne {μ μ' : Fˣ →* ℂˣ} (hne : μ ≠ μ') :
    hermitianPairing (detCharC (F := F) μ) (detCharC μ') = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, μ u ≠ μ' u := by
    by_contra hall; push Not at hall; exact hne (MonoidHom.ext hall)
  obtain ⟨t0, ht0⟩ := GeneralLinearGroup.det_surjective (n := Fin 2) (R := F) u
  have hc1 : (μ u : ℂ) * conj (μ' u : ℂ) ≠ 1 := by
    intro h1; apply hu; apply Units.ext
    calc (μ u : ℂ) = (μ u : ℂ) * (conj (μ' u : ℂ) * (μ' u : ℂ)) := by
          rw [mul_comm (conj _), conj_hom_mul_self, mul_one]
      _ = (μ' u : ℂ) := by rw [← mul_assoc, h1, one_mul]
  unfold hermitianPairing
  rw [sum_eq_zero_of_mul_left t0 _ hc1 ?_, mul_zero]
  intro g
  simp only [detCharC, map_mul, ht0, Units.val_mul]
  ring

lemma wChar_injective : Function.Injective (wChar (F := F)) := by
  intro μ μ' hE
  by_contra hne
  have hP : psChar μ μ = wChar μ + detCharC (F := F) μ := by funext g; simp [wChar]
  have hP' : psChar μ' μ' = wChar μ + detCharC (F := F) μ' := by
    rw [hE]; funext g; simp [wChar]
  have hPP : hermitianPairing (psChar (F := F) μ μ) (psChar μ μ) = 2 :=
    hermitianPairing_principalSeries_diag μ
  have hPD : hermitianPairing (psChar (F := F) μ μ) (detCharC μ) = 1 :=
    hermitianPairing_principalSeries_detCharC μ
  have hDP : hermitianPairing (detCharC (F := F) μ) (psChar μ μ) = 1 := by
    rw [hermitianPairing_conj, hPD, map_one]
  have hP'D' : hermitianPairing (psChar (F := F) μ' μ') (detCharC μ') = 1 :=
    hermitianPairing_principalSeries_detCharC μ'
  have hD'D' := hermitianPairing_detCharC (F := F) μ'
  have hDD' := hermitianPairing_detCharC_ne (F := F) hne
  have hP'P : hermitianPairing (psChar (F := F) μ' μ') (psChar μ μ) = 0 :=
    hermitianPairing_principalSeries_eq_zero (fun h' => hne h'.1.symm) (fun h' => hne h'.1.symm)
  have e1 : hermitianPairing (wChar μ) (detCharC μ') = 0 := by
    have := congrArg (fun f => hermitianPairing f (detCharC μ')) hP'
    simp only [hermitianPairing_add_left] at this
    linear_combination hP'D' - this - hD'D'
  have e2 : hermitianPairing (psChar (F := F) μ μ) (detCharC μ') = 0 := by
    have := congrArg (fun f => hermitianPairing f (detCharC μ')) hP
    simp only [hermitianPairing_add_left] at this
    linear_combination this + e1 + hDD'
  have e3 : hermitianPairing (wChar μ) (psChar μ μ) = 1 := by
    have := congrArg (fun f => hermitianPairing f (psChar μ μ)) hP
    simp only [hermitianPairing_add_left] at this
    linear_combination hPP - this - hDP
  have e5 : hermitianPairing (detCharC (F := F) μ') (psChar μ μ) = 0 := by
    rw [hermitianPairing_conj, e2, map_zero]
  have e4 := congrArg (fun f => hermitianPairing f (psChar μ μ)) hP'
  simp only [hermitianPairing_add_left] at e4
  have : (1 : ℂ) = 0 := by linear_combination -e3 + hP'P - e5 - e4
  exact one_ne_zero this

lemma detCharC_injective : Function.Injective (detCharC (F := F)) := by
  intro μ μ' hE
  refine detChar_injective (F := F) (MonoidHom.ext fun g => Units.ext ?_)
  exact congrFun hE g

theorem psChar_eq_iff {l₁ l₂ l₁' l₂' : Fˣ →* ℂˣ} (hne : l₁ ≠ l₂) (hne' : l₁' ≠ l₂') :
    psChar (F := F) l₁ l₂ = psChar l₁' l₂' ↔ (l₁ = l₁' ∧ l₂ = l₂') ∨ (l₁ = l₂' ∧ l₂ = l₁') := by
  rw [← nonempty_equiv_principalSeries_iff (F := F) hne hne']
  constructor
  · intro hc
    by_contra hN
    rw [nonempty_equiv_principalSeries_iff hne hne'] at hN
    push Not at hN
    have h0 : hermitianPairing (psChar (F := F) l₁ l₂) (psChar l₁' l₂') = 0 :=
      hermitianPairing_principalSeries_eq_zero (fun h' => hN.1 h'.1 h'.2) (fun h' => hN.2 h'.1 h'.2)
    rw [← hc, hermitianPairing_principalSeries_self hne] at h0
    exact one_ne_zero h0
  · rintro ⟨e⟩
    exact Representation.char_iso e

end Others

/-! ### The complete list of irreducible characters -/

section Total

open scoped ComplexOrder

/-- The characters `μ ∘ det` of the one-dimensional representations. -/
noncomputable def detSet : Set (GL (Fin 2) F → ℂ) := Set.range (detCharC (F := F))

/-- The characters of the `q`-dimensional representations `W_μ`. -/
noncomputable def wSet : Set (GL (Fin 2) F → ℂ) := Set.range (wChar (F := F))

/-- The characters of the irreducible principal series representations `V_{λ₁,λ₂}`, `λ₁ ≠ λ₂`. -/
def psSet : Set (GL (Fin 2) F → ℂ) := {ζ | ∃ l₁ l₂ : Fˣ →* ℂˣ, l₁ ≠ l₂ ∧ psChar l₁ l₂ = ζ}

lemma card_homs_units : Nat.card (Fˣ →* ℂˣ) = Nat.card F - 1 := by
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_units]

lemma two_le_card : 2 ≤ Nat.card F := by
  have : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card]; omega

lemma ncard_detSet : (detSet (F := F)).ncard = Nat.card F - 1 := by
  rw [detSet, ← Nat.card_coe_set_eq, Nat.card_range_of_injective detCharC_injective, card_homs_units]

lemma ncard_wSet : (wSet (F := F)).ncard = Nat.card F - 1 := by
  rw [wSet, ← Nat.card_coe_set_eq, Nat.card_range_of_injective wChar_injective, card_homs_units]

/-- There are `(q-1)(q-2)/2` irreducible principal series characters (stated as
`2 * #psSet = (q-1)(q-2)`). -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem ncard_psSet : 2 * (psSet (F := F)).ncard = (Nat.card F - 1) * (Nat.card F - 2) := by
  classical
  haveI : Finite (Fˣ →* ℂˣ) := Nat.finite_of_card_ne_zero (by
    have := two_le_card (F := F)
    rw [card_homs_units]; omega)
  haveI := Fintype.ofFinite (Fˣ →* ℂˣ)
  set S : Finset ((Fˣ →* ℂˣ) × (Fˣ →* ℂˣ)) := (Finset.univ : Finset (Fˣ →* ℂˣ)).offDiag with hSdef
  have hS : S.card = (Nat.card F - 1) * (Nat.card F - 2) := by
    rw [hSdef, Finset.offDiag_card, Finset.card_univ, ← Nat.card_eq_fintype_card, card_homs_units]
    obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 2 := ⟨Nat.card F - 2, by have := two_le_card (F := F); omega⟩
    rw [hr]
    simp only [Nat.add_sub_cancel, show r + 2 - 1 = r + 1 by omega]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hset : psSet (F := F) = ↑(S.image (fun p => psChar (F := F) p.1 p.2)) := by
    ext ζ
    constructor
    · rintro ⟨l₁, l₂, hne, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(l₁, l₂), by simp [hSdef, hne], rfl⟩)
    · intro hζ
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hζ)
      exact ⟨p.1, p.2, (Finset.mem_offDiag.1 hp).2.2, rfl⟩
  rw [hset, Set.ncard_coe_finset, ← hS]
  refine (card_eq_two_mul_card_image S _ ?_).symm
  intro p hp
  have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
  have hfib : S.filter (fun p' => psChar (F := F) p'.1 p'.2 = psChar p.1 p.2) = {p, p.swap} := by
    ext p'
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hSdef, Finset.mem_offDiag,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp', he⟩
      rcases (psChar_eq_iff hp' hpne).1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl (Prod.ext e1 e2)
      · exact Or.inr (Prod.ext e1 e2)
    · rintro (rfl | rfl)
      · exact ⟨hpne, rfl⟩
      · exact ⟨hpne.symm, (psChar_eq_iff hpne.symm hpne).2 (Or.inr ⟨rfl, rfl⟩)⟩
  rw [hfib, Finset.card_pair]
  intro e
  exact hpne (congrArg Prod.fst e)

variable {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0)

lemma cast_card_ne_zero : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'

lemma disjoint_det_w : Disjoint (detSet (F := F)) (wSet (F := F)) := by
  refine Set.disjoint_left.2 ?_
  rintro ζ ⟨μ, rfl⟩ ⟨μ', hE⟩
  have := congrFun hE (upperUnit 1 1)
  rw [wChar_upper, detCharC_upper] at this
  exact zero_ne_one this

lemma disjoint_det_ps : Disjoint (detSet (F := F)) (psSet (F := F)) := by
  refine Set.disjoint_left.2 ?_
  rintro ζ ⟨μ, rfl⟩ ⟨l₁, l₂, -, hE⟩
  have := congrFun hE 1
  rw [psChar_one, detCharC_one] at this
  push_cast at this
  exact cast_card_ne_zero (F := F) (by linear_combination this)

lemma disjoint_det_cusp : Disjoint (detSet (F := F)) (cuspSet h) := by
  refine Set.disjoint_left.2 ?_
  rintro ζ ⟨μ, rfl⟩ ⟨ν, -, hE⟩
  have := congrFun hE (upperUnit 1 1)
  rw [cusp_upper, detCharC_upper] at this
  exact two_ne_zero_complex (by linear_combination -this)

lemma disjoint_w_ps : Disjoint (wSet (F := F)) (psSet (F := F)) := by
  refine Set.disjoint_left.2 ?_
  rintro ζ ⟨μ, rfl⟩ ⟨l₁, l₂, -, hE⟩
  have := congrFun hE 1
  rw [psChar_one, wChar_one] at this
  push_cast at this
  exact one_ne_zero (by linear_combination this)

lemma disjoint_w_cusp : Disjoint (wSet (F := F)) (cuspSet h) := by
  refine Set.disjoint_left.2 ?_
  rintro ζ ⟨μ, rfl⟩ ⟨ν, -, hE⟩
  have := congrFun hE 1
  rw [cusp_one h, wChar_one] at this
  exact one_ne_zero (by linear_combination -this)

lemma disjoint_ps_cusp : Disjoint (psSet (F := F)) (cuspSet h) := by
  refine Set.disjoint_left.2 ?_
  rintro ζ ⟨l₁, l₂, -, rfl⟩ ⟨ν, -, hE⟩
  have := congrFun hE 1
  rw [cusp_one h, psChar_one] at this
  push_cast at this
  exact two_ne_zero_complex (by linear_combination -this)

/-- **Etingof et al., §4.24.4 conclusion (p. 75)**: all irreducible characters of `GL_2(F_q)`.  The irreducible
characters are exactly: the `q - 1` one-dimensional characters `μ ∘ det`; the `q - 1` characters of the
`q`-dimensional representations `W_μ`; the characters of the `(q-1)(q-2)/2` irreducible principal series
`V_{λ₁,λ₂}` with `λ₁ ≠ λ₂` (unordered pairs); and the characters of the `q(q-1)/2` cuspidal representations
`W₁ ⊗ V_{α,1} - V_{α,1} - Y_ν` attached to the pairs `{ν, ν^q}` with `ν^q ≠ ν`.  Here `h` is an irreducible
quadratic over `F`, which exists for every finite field. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem irrChars_GL2_eq :
    irrChars ℂ (GL (Fin 2) F) = ((detSet ∪ wSet) ∪ psSet) ∪ cuspSet h := by
  have hsub : ((detSet (F := F) ∪ wSet) ∪ psSet) ∪ cuspSet h ⊆ irrChars ℂ (GL (Fin 2) F) := by
    rintro ζ (((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨l₁, l₂, hne, rfl⟩) | ⟨ν, hν, rfl⟩)
    · exact detCharC_mem_irrChars μ
    · exact wChar_mem_irrChars μ
    · exact psChar_mem_irrChars hne
    · exact cusp_mem_irrChars h hν
  have hfin : (irrChars ℂ (GL (Fin 2) F)).Finite := irrChars_finite
  have fD : (detSet (F := F)).Finite := hfin.subset (fun ζ hζ => hsub (Or.inl (Or.inl (Or.inl hζ))))
  have fW : (wSet (F := F)).Finite := hfin.subset (fun ζ hζ => hsub (Or.inl (Or.inl (Or.inr hζ))))
  have fP : (psSet (F := F)).Finite := hfin.subset (fun ζ hζ => hsub (Or.inl (Or.inr hζ)))
  have fC : (cuspSet h).Finite := hfin.subset (fun ζ hζ => hsub (Or.inr hζ))
  have d1 : Disjoint (detSet (F := F) ∪ wSet) psSet :=
    Set.disjoint_union_left.2 ⟨disjoint_det_ps, disjoint_w_ps⟩
  have d2 : Disjoint ((detSet (F := F) ∪ wSet) ∪ psSet) (cuspSet h) :=
    Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨disjoint_det_cusp h, disjoint_w_cusp h⟩,
      disjoint_ps_cusp h⟩
  have hcard : (((detSet (F := F) ∪ wSet) ∪ psSet) ∪ cuspSet h).ncard = Nat.card F ^ 2 - 1 := by
    rw [Set.ncard_union_eq d2 (fD.union fW |>.union fP) fC, Set.ncard_union_eq d1 (fD.union fW) fP,
      Set.ncard_union_eq disjoint_det_w fD fW]
    have e1 := ncard_detSet (F := F)
    have e2 := ncard_wSet (F := F)
    have e3 := ncard_psSet (F := F)
    have e4 := ncard_cuspSet h
    obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 2 := ⟨Nat.card F - 2, by have := two_le_card (F := F); omega⟩
    rw [hr] at e1 e2 e3 e4 ⊢
    simp only [show r + 2 - 1 = r + 1 by omega, show r + 2 - 2 = r by omega] at e1 e2 e3
    have f1 : (r + 2) ^ 2 - (r + 2) = (r + 2) * (r + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    have f2 : (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) := Nat.sub_eq_of_eq_add (by ring)
    rw [f1] at e4
    rw [f2]
    nlinarith [e1, e2, e3, e4]
  symm
  apply Set.eq_of_subset_of_ncard_le hsub _ hfin
  rw [hcard, ← Nat.card_coe_set_eq, card_irrChars (k := ℂ), nat_card_conjClasses]

/-- **Etingof et al., §4.24.4 conclusion (p. 75)**: `GL_2(F_q)` has exactly `q² - 1` irreducible
representations up to isomorphism (the number of its conjugacy classes), counted as distinct irreducible
characters, and they are the `q - 1` characters `μ ∘ det`, the `q - 1` characters of `W_μ`, the
`(q-1)(q-2)/2` principal series characters and the `q(q-1)/2` cuspidal characters
(`2 * #psSet = (q-1)(q-2)`, `2 * #cuspSet = q² - q`). -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem card_irrChars_GL2 :
    Nat.card (irrChars ℂ (GL (Fin 2) F)) = Nat.card F ^ 2 - 1 := by
  rw [card_irrChars (k := ℂ), nat_card_conjClasses]

/-- Every finite field has an irreducible monic quadratic (there are `q(q-1)/2` elliptic classes in `GL_2`). -/
theorem exists_irreducible_quadratic : ∃ t n : F, ∀ x : F, x ^ 2 - t * x + n ≠ 0 := by
  have hq := two_le_card (F := F)
  have hpos : 0 < (ellipticClasses F).ncard := by
    rw [ncard_ellipticClasses]
    exact Nat.div_pos (by nlinarith [Nat.mul_le_mul hq (show 1 ≤ Nat.card F - 1 by omega)]) (by norm_num)
  obtain ⟨c, t, n, h, -⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
  exact ⟨t, n, h⟩

/-- **Etingof et al., §4.24.4 conclusion (p. 75)**, with no auxiliary hypothesis: for every finite field the
irreducible characters of `GL_2(F_q)` are exactly the four families of `irrChars_GL2_eq`, for a suitable
irreducible quadratic `x² - t x + n`. -/
@[kb "etingof2011" "§4.24.4 conclusion, p. 75"]
theorem exists_irrChars_GL2_eq : ∃ (t n : F) (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0),
    irrChars ℂ (GL (Fin 2) F) = ((detSet ∪ wSet) ∪ psSet) ∪ cuspSet h := by
  obtain ⟨t, n, h⟩ := exists_irreducible_quadratic (F := F)
  exact ⟨t, n, h, irrChars_GL2_eq h⟩

end Total

end UndergradKB.RepresentationTheory.GL2
