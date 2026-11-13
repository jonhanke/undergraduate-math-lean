import Mathlib.RepresentationTheory.Irreducible
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialRepsDecomp

/-! # Irreducible rational representations of `GL_N(ℂ)` (Etingof et al., Definition 4.65, Theorem 4.66)

For a Young diagram `ν` with at most `N` rows and an integer `a`, `glIrrep ν a = L_ν ⊗ det^a` is the book's `L_λ`
with highest weight `λ_j = ν_j + a` (`highestWeight`), a non-increasing sequence of `N` integers.

* `exists_equiv_swRepGL_of_isHomogPolyRep`: an irreducible homogeneous polynomial representation of degree `m` is
  isomorphic to some `L_ν`, `ν ⊢ m` with at most `N` rows (density theorem over the Schur algebra).
* `glIrrep_equiv_iff`: `L_ν ⊗ det^a ≅ L_μ ⊗ det^b` iff the highest weights agree (characters at diagonal matrices
  and injectivity of Schur polynomials; the converse through the classification).
* `IsRationalRep.exists_equiv_glIrrep`: every irreducible finite-dimensional rational representation is isomorphic
  to some `glIrrep ν a`.
* `IsRationalRep.exists_isCompl`: complete reducibility of finite-dimensional rational representations.

Irreducibility is stated with invariant subspaces (`IsIrredRep`), equivalent to Mathlib's
`Representation.IsIrreducible` (`isIrreducible_iff_isIrredRep`).  Representation spaces in the classification
statements live in `Type` (the universe of the Schur-Weyl multiplicity spaces).
-/

namespace UndergradKB.RepresentationTheory

open scoped TensorProduct

section Irred

variable {G : Type*} [Monoid G] {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Irreducibility in terms of invariant subspaces: `W ≠ 0` and the only invariant subspaces are `0` and `W`. -/
def IsIrredRep (ρ : Representation ℂ G W) : Prop :=
  Nontrivial W ∧ ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, ρ g w ∈ U) → U = ⊥ ∨ U = ⊤

theorem isIrreducible_iff_isIrredRep (ρ : Representation ℂ G W) : ρ.IsIrreducible ↔ IsIrredRep ρ := by
  constructor
  · intro h
    refine ⟨?_, fun U hU => ?_⟩
    · by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      show (⊥ : Submodule ℂ W) = ⊤
      ext x
      simp [Subsingleton.elim x 0]
    · rcases h.eq_bot_or_eq_top ⟨U, fun g v hv => hU g v hv⟩ with h1 | h1
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  · rintro ⟨hn, hU⟩
    exact
      { exists_pair_ne := ⟨⊥, ⊤, fun h => by
          have h' : (⊥ : Submodule ℂ W) = ⊤ := congrArg Subrepresentation.toSubmodule h
          exact bot_ne_top h'⟩
        eq_bot_or_eq_top := fun σ => (hU σ.toSubmodule σ.apply_mem_toSubmodule).imp
          (fun h => Subrepresentation.toSubmodule_injective h)
          (fun h => Subrepresentation.toSubmodule_injective h) }

theorem equiv_apply_rep {ρ : Representation ℂ G W} {σ : Representation ℂ G W'} (e : Representation.Equiv ρ σ)
    (g : G) (w : W) : e.toLinearEquiv (ρ g w) = σ g (e.toLinearEquiv w) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) w

theorem IsIrredRep.of_equiv {ρ : Representation ℂ G W} {σ : Representation ℂ G W'}
    (e : Representation.Equiv ρ σ) (h : IsIrredRep ρ) : IsIrredRep σ := by
  obtain ⟨hn, hU⟩ := h
  refine ⟨e.toLinearEquiv.toEquiv.symm.nontrivial, fun U hU' => ?_⟩
  have hc : ∀ g, ∀ w ∈ U.comap e.toLinearEquiv.toLinearMap, ρ g w ∈ U.comap e.toLinearEquiv.toLinearMap := by
    intro g w hw
    simp only [Submodule.mem_comap] at hw ⊢
    show e.toLinearEquiv (ρ g w) ∈ U
    rw [equiv_apply_rep]
    exact hU' g _ hw
  have hsurj : Function.Surjective e.toLinearEquiv.toLinearMap := e.toLinearEquiv.surjective
  rcases hU _ hc with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective hsurj U, h, Submodule.map_bot]
  · right
    rw [← Submodule.map_comap_eq_of_surjective hsurj U, h, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

theorem trace_eq_of_repEquiv [FiniteDimensional ℂ W] [FiniteDimensional ℂ W'] {ρ : Representation ℂ G W}
    {σ : Representation ℂ G W'} (e : Representation.Equiv ρ σ) (g : G) :
    LinearMap.trace ℂ W (ρ g) = LinearMap.trace ℂ W' (σ g) := by
  have h : e.toLinearEquiv.conj (ρ g) = σ g := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply]
    calc e.toLinearEquiv (ρ g (e.toLinearEquiv.symm x))
        = σ g (e.toLinearEquiv (e.toLinearEquiv.symm x)) := equiv_apply_rep e g _
      _ = σ g x := by rw [LinearEquiv.apply_symm_apply]
  rw [← LinearMap.trace_conj' (ρ g) e.toLinearEquiv, h]

end Irred

section DetTwist

variable {N : ℕ} {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- The value `det(g)^a`. -/
noncomputable abbrev detVal (g : GL (Fin N) ℂ) (a : ℤ) : ℂ := ((Matrix.GeneralLinearGroup.det g ^ a : ℂˣ) : ℂ)

theorem detVal_ne_zero (g : GL (Fin N) ℂ) (a : ℤ) : detVal g a ≠ 0 := Units.ne_zero _

theorem rid_tprod_detRep (ρ : Representation ℂ (GL (Fin N) ℂ) W) (a : ℤ) (g : GL (Fin N) ℂ) (x : W ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ W ((ρ.tprod (detRep N ℂ a)) g x) = detVal g a • ρ g (TensorProduct.rid ℂ W x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul w c => simp [Representation.tprod_apply, detRep, smul_smul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- Twisting by a power of the determinant preserves irreducibility. -/
theorem IsIrredRep.tprod_detRep {ρ : Representation ℂ (GL (Fin N) ℂ) W} (h : IsIrredRep ρ) (a : ℤ) :
    IsIrredRep (ρ.tprod (detRep N ℂ a)) := by
  obtain ⟨hn, hU⟩ := h
  let e := TensorProduct.rid ℂ W
  refine ⟨e.toEquiv.nontrivial, fun U hUs => ?_⟩
  have h1 : ∀ g, ∀ v ∈ U.map e.toLinearMap, ρ g v ∈ U.map e.toLinearMap := by
    rintro g _ ⟨u, hu, rfl⟩
    refine ⟨(detVal g a)⁻¹ • (ρ.tprod (detRep N ℂ a)) g u, U.smul_mem _ (hUs g u hu), ?_⟩
    simp only [LinearEquiv.coe_coe, map_smul, e, rid_tprod_detRep, smul_smul,
      inv_mul_cancel₀ (detVal_ne_zero g a), one_smul]
  have hinj : Function.Injective e.toLinearMap := e.injective
  rcases hU _ h1 with h | h
  · left
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_bot]
  · right
    apply Submodule.map_injective_of_injective hinj
    rw [h, Submodule.map_top]
    exact (LinearMap.range_eq_top.2 e.surjective).symm

end DetTwist

section DetEquiv

variable {N : ℕ} {W W' : Type*} [AddCommMonoid W] [Module ℂ W] [AddCommMonoid W'] [Module ℂ W']

omit [AddCommMonoid W'] [Module ℂ W'] in
theorem equiv_apply_rep' {G : Type*} [Monoid G] {W W' : Type*} [AddCommMonoid W] [Module ℂ W] [AddCommMonoid W']
    [Module ℂ W'] {ρ : Representation ℂ G W} {σ : Representation ℂ G W'} (e : Representation.Equiv ρ σ)
    (g : G) (w : W) : e.toLinearEquiv (ρ g w) = σ g (e.toLinearEquiv w) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) w

/-- An isomorphism `ρ ≅ σ` gives `ρ ⊗ det^a ≅ σ ⊗ det^a`. -/
noncomputable def equivTprodDetRep {ρ : Representation ℂ (GL (Fin N) ℂ) W} {σ : Representation ℂ (GL (Fin N) ℂ) W'}
    (e : Representation.Equiv ρ σ) (a : ℤ) :
    Representation.Equiv (ρ.tprod (detRep N ℂ a)) (σ.tprod (detRep N ℂ a)) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl ℂ ℂ)) fun g =>
    TensorProduct.ext' fun w c => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.tprod_apply, TensorProduct.map_tmul,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      rw [equiv_apply_rep']

/-- `(ρ ⊗ det^a) ⊗ det^b ≅ ρ ⊗ det^c` for `a + b = c`. -/
noncomputable def detRepMergeEquiv (ρ : Representation ℂ (GL (Fin N) ℂ) W) (a b c : ℤ) (h : a + b = c) :
    Representation.Equiv ((ρ.tprod (detRep N ℂ a)).tprod (detRep N ℂ b)) (ρ.tprod (detRep N ℂ c)) :=
  Representation.Equiv.mk ((TensorProduct.assoc ℂ W ℂ ℂ).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ W) (TensorProduct.lid ℂ ℂ))) fun g =>
    TensorProduct.ext_threefold fun w x y => by
      subst h
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.tprod_apply, TensorProduct.map_tmul,
        LinearEquiv.trans_apply, TensorProduct.assoc_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        TensorProduct.lid_tmul]
      congr 1
      simp [detRep, zpow_add, smul_eq_mul]
      ring

/-- `ρ ⊗ det^0 ≅ ρ`. -/
noncomputable def detRepZeroEquiv (ρ : Representation ℂ (GL (Fin N) ℂ) W) :
    Representation.Equiv (ρ.tprod (detRep N ℂ 0)) ρ :=
  Representation.Equiv.mk (TensorProduct.rid ℂ W) fun g =>
    TensorProduct.ext' fun w c => by
      simp [Representation.tprod_apply, detRep]

end DetEquiv

section Homog

variable {N : ℕ}

open Classical in
/-- The family of simple modules over the Schur algebra used in the density argument: `d` and the `L_ν` with at
most `N` rows. -/
noncomputable def idxWith {m : ℕ} (d : PolyRepData N m) :
    Option {ν : DiagramsOfSize m // ν.1.colLen 0 ≤ N} → PolyRepData N m
  | none => d
  | some ν => lData ν.1

/-- The density argument: a simple homogeneous polynomial representation of degree `m` is isomorphic to some
`L_ν`. -/
theorem PolyRepData.exists_equiv_lData {m : ℕ} (d : PolyRepData N m) (hd : d.GLSimple) :
    ∃ ν : DiagramsOfSize m, ν.1.colLen 0 ≤ N ∧ Nonempty (Representation.Equiv d.ρ (swRepGL N m ν)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hsimple : ∀ i, IsSimpleModule (schurCommutant N m) (idxWith d i).Mod := by
    rintro (_ | ⟨ν, hν⟩)
    · exact hd.isSimpleModule
    · exact (glSimple_lData ν hν).isSimpleModule
  have hV : ∀ i j, i ≠ j →
      IsEmpty ((idxWith d i).Mod ≃ₗ[schurCommutant N m] (idxWith d j).Mod) := by
    rintro (_ | ⟨ν, hν⟩) (_ | ⟨ν', hν'⟩) hij
    · exact absurd rfl hij
    · refine ⟨fun e => ?_⟩
      exact (hcon ν' hν').false (PolyRepData.repEquivOfEquiv (d := d) (d' := lData ν') e)
    · refine ⟨fun e => ?_⟩
      exact (hcon ν hν).false (PolyRepData.repEquivOfEquiv (d := d) (d' := lData ν) e.symm)
    · refine ⟨fun e => hij ?_⟩
      have : ν = ν' := eq_of_weylValue_eq ν ν' hν hν' fun x hx => by
        rw [← trace_swRepGL_diagonal ν x hx, ← trace_swRepGL_diagonal ν' x hx]
        exact PolyRepData.trace_eq_of_equiv e (diagGL N x hx)
      subst this
      rfl
  have := hsimple
  let g : ∀ i, Module.End ℂ (idxWith d i).Mod := fun i =>
    match i with
    | none => LinearMap.id
    | some _ => 0
  obtain ⟨b, hb⟩ := density_pi_surjective (k := ℂ) (A := schurCommutant N m)
    (V := fun i => (idxWith d i).Mod) hV g
  have hb0 : b = 0 := by
    refine eq_zero_of_alg_eq_zero b fun ν hν => ?_
    have := congrFun hb (some ⟨ν, hν⟩)
    exact this
  have h1 := congrFun hb none
  have hnt : Nontrivial d.Mod := hd.1
  obtain ⟨w, hw⟩ := exists_ne (0 : d.Mod)
  have h2 := LinearMap.congr_fun h1 w
  subst hb0
  apply hw
  have h3 : (0 : schurCommutant N m) • w = 0 := zero_smul _ _
  have h4 : (g none) w = w := rfl
  exact ((h3.symm.trans h2).trans h4).symm

/-- **Etingof et al., Theorem 4.66 (i), constituents, homogeneous case.**  An irreducible finite-dimensional
representation of `GL_N(ℂ)` whose coefficients are homogeneous polynomials of degree `m` is isomorphic to `L_ν`
for a diagram `ν` with `m` boxes and at most `N` rows. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem exists_equiv_swRepGL_of_isHomogPolyRep {m : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsHomogPolyRep m ρ)
    (hirr : IsIrredRep ρ) :
    ∃ ν : DiagramsOfSize m, ν.1.colLen 0 ≤ N ∧ Nonempty (Representation.Equiv ρ (swRepGL N m ν)) :=
  PolyRepData.exists_equiv_lData ⟨W, ρ, hρ⟩ hirr

end Homog

section Weights

variable {N : ℕ}

/-- The book's `L_λ`: `L_ν ⊗ det^a`, of highest weight `λ_j = ν_j + a`. -/
noncomputable abbrev glIrrep {n : ℕ} (ν : DiagramsOfSize n) (a : ℤ) :
    Representation ℂ (GL (Fin N) ℂ)
      ((spechtModule ν →ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))] tensorPowerModule (Fin N → ℂ) n) ⊗[ℂ] ℂ) :=
  (swRepGL N n ν).tprod (detRep N ℂ a)

/-- The highest weight `(ν_1 + a, …, ν_N + a)` of `L_ν ⊗ det^a`. -/
def highestWeight {n : ℕ} (N : ℕ) (ν : DiagramsOfSize n) (a : ℤ) : Fin N → ℤ := fun j => (ν.1.rowLen j : ℤ) + a

theorem highestWeight_antitone {n : ℕ} (ν : DiagramsOfSize n) (a : ℤ) : Antitone (highestWeight N ν a) := by
  intro i j hij
  simp only [highestWeight, add_le_add_iff_right, Nat.cast_le]
  exact ν.1.rowLen_anti i j hij

theorem isRationalRep_glIrrep {n : ℕ} (ν : DiagramsOfSize n) (a : ℤ) :
    IsRationalRep (glIrrep (N := N) ν a) :=
  (isPolynomialRep_swRepGL N n ν).isRationalRep.tprod (isRationalRep_detRep a)

theorem isIrredRep_swRepGL {n : ℕ} (ν : DiagramsOfSize n) (hν : ν.1.colLen 0 ≤ N) :
    IsIrredRep (swRepGL N n ν) :=
  glSimple_lData ν hν

theorem isIrredRep_glIrrep {n : ℕ} (ν : DiagramsOfSize n) (hν : ν.1.colLen 0 ≤ N) (a : ℤ) :
    IsIrredRep (glIrrep (N := N) ν a) :=
  (isIrredRep_swRepGL ν hν).tprod_detRep a

theorem trace_glIrrep_diag {n : ℕ} (ν : DiagramsOfSize n) (a : ℤ) (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    LinearMap.trace ℂ _ (glIrrep (N := N) ν a (diagGL N x hx)) = (∏ i, x i) ^ a * weylValue ν x := by
  show LinearMap.trace ℂ _ (TensorProduct.map (swRepGL N n ν (diagGL N x hx))
    (detRep N ℂ a (diagGL N x hx))) = _
  rw [LinearMap.trace_tensorProduct', trace_swRepGL_diagonal]
  have : detRep N ℂ a (diagGL N x hx) = (∏ i, x i) ^ a • LinearMap.id := by
    ext
    simp [detRep, diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]
  rw [this, map_smul, LinearMap.trace_id]
  simp [mul_comm]

theorem schurPoly_add_const {R : Type*} [CommRing R] [IsDomain R] (lam : Fin N → ℕ) (p : ℕ) :
    (schurPoly (fun j => lam j + p) : MvPolynomial (Fin N) R) =
      (∏ i : Fin N, MvPolynomial.X i) ^ p * schurPoly lam := by
  induction p with
  | zero => simp
  | succ p ih =>
    have := schurPoly_add_one (R := R) (fun j => lam j + p)
    simp only [← add_assoc] at this ⊢
    rw [this, ih, pow_succ]
    ring

/-- A polynomial vanishing at every point with nonzero coordinates is zero. -/
theorem mvPolynomial_eq_zero_of_torus {P : MvPolynomial (Fin N) ℂ}
    (h : ∀ x : Fin N → ℂ, (∀ i, x i ≠ 0) → MvPolynomial.eval x P = 0) : P = 0 := by
  have hP : (∏ i : Fin N, MvPolynomial.X i : MvPolynomial (Fin N) ℂ) * P = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : ∀ i, x i ≠ 0
    · simp [h x hx]
    · push Not at hx
      obtain ⟨i, hi⟩ := hx
      simp [Finset.prod_eq_zero (Finset.mem_univ i) hi]
  have hne : (∏ i : Fin N, MvPolynomial.X i : MvPolynomial (Fin N) ℂ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => MvPolynomial.X_ne_zero i
  exact (mul_eq_zero.1 hP).resolve_left hne

/-- Equal characters on the diagonal torus force equal highest weights. -/
theorem highestWeight_eq_of_trace {n m : ℕ} (ν : DiagramsOfSize n) (μ : DiagramsOfSize m)
    (hν : ν.1.colLen 0 ≤ N) (hμ : μ.1.colLen 0 ≤ N) (a b : ℤ)
    (h : ∀ x : Fin N → ℂ, (∀ i, x i ≠ 0) → (∏ i, x i) ^ a * weylValue ν x = (∏ i, x i) ^ b * weylValue μ x) :
    highestWeight N ν a = highestWeight N μ b := by
  -- shift both exponents to natural numbers
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = a + (|a| + |b|) := ⟨(a + (|a| + |b|)).toNat, by
    rw [Int.toNat_of_nonneg]; have := le_abs_self (-a); have := abs_nonneg b; rw [abs_neg] at *; linarith⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = b + (|a| + |b|) := ⟨(b + (|a| + |b|)).toNat, by
    rw [Int.toNat_of_nonneg]; have := le_abs_self (-b); have := abs_nonneg a; rw [abs_neg] at *; linarith⟩
  have key : (schurPoly (fun j : Fin N => ν.1.rowLen j + p) : MvPolynomial (Fin N) ℂ) =
      schurPoly (fun j : Fin N => μ.1.rowLen j + q) := by
    rw [schurPoly_add_const, schurPoly_add_const, ← sub_eq_zero]
    apply mvPolynomial_eq_zero_of_torus
    intro x hx
    have hx0 : (∏ i, x i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx i
    have e := h x hx
    simp only [weylValue, hν, hμ, if_true] at e
    have e2 := congrArg (fun t => (∏ i, x i) ^ (|a| + |b|) * t) e
    rw [← mul_assoc, ← mul_assoc, ← zpow_add₀ hx0, ← zpow_add₀ hx0, add_comm (|a| + |b|) a,
      add_comm (|a| + |b|) b, ← hp, ← hq, zpow_natCast, zpow_natCast] at e2
    simp [map_prod, e2]
  have hanti : ∀ (κ : YoungDiagram) (r : ℕ), Antitone (fun j : Fin N => κ.rowLen j + r) :=
    fun κ r i j hij => Nat.add_le_add_right (κ.rowLen_anti i j hij) r
  have := schurPoly_injective (hanti ν.1 p) (hanti μ.1 q) key
  funext j
  have hj := congrFun this j
  simp only [highestWeight]
  have : (ν.1.rowLen j : ℤ) + p = μ.1.rowLen j + q := by exact_mod_cast hj
  rw [hp, hq] at this
  linarith

end Weights

section Rational

variable {N : ℕ}

/-- Isomorphic `L_ν ⊗ det^a` have the same highest weight. -/
theorem highestWeight_eq_of_equiv {n m : ℕ} (ν : DiagramsOfSize n) (μ : DiagramsOfSize m)
    (hν : ν.1.colLen 0 ≤ N) (hμ : μ.1.colLen 0 ≤ N) (a b : ℤ)
    (e : Representation.Equiv (glIrrep (N := N) ν a) (glIrrep (N := N) μ b)) :
    highestWeight N ν a = highestWeight N μ b :=
  highestWeight_eq_of_trace ν μ hν hμ a b fun x hx => by
    rw [← trace_glIrrep_diag, ← trace_glIrrep_diag]
    exact trace_eq_of_repEquiv e (diagGL N x hx)

/-- Shifting into the polynomial range: `L_ν ⊗ det^a ≅ L_κ ⊗ det^(-K)` with `κ = ν + a + K`. -/
theorem exists_shift_equiv {n : ℕ} (ν : DiagramsOfSize n) (hν : ν.1.colLen 0 ≤ N) (a : ℤ) (K p : ℕ)
    (hp : a + K = p) :
    ∃ (m : ℕ) (κ : DiagramsOfSize m), κ.1.colLen 0 ≤ N ∧ highestWeight N κ 0 = highestWeight N ν p ∧
      Nonempty (Representation.Equiv (glIrrep (N := N) ν a) (glIrrep (N := N) κ (-K))) := by
  have hpol : IsPolynomialRep (k := ℂ) (glIrrep (N := N) ν p) :=
    (isPolynomialRep_swRepGL N n ν).tprod (isPolynomialRep_detRep p)
  have hirr := isIrredRep_glIrrep (N := N) ν hν p
  have := hirr.1
  obtain ⟨d, hd⟩ := hpol.exists_isHomogPolyRep_of_irreducible hirr.2
  obtain ⟨κ, hκ, ⟨e⟩⟩ := exists_equiv_swRepGL_of_isHomogPolyRep hd hirr
  refine ⟨d, κ, hκ, ?_, ⟨?_⟩⟩
  · exact (highestWeight_eq_of_equiv ν κ hν hκ p 0 (e.trans (detRepZeroEquiv _).symm)).symm
  · have e5 := detRepMergeEquiv (swRepGL N n ν) a K p hp
    have e3 := equivTprodDetRep e5 (-(K : ℤ))
    have e4 := equivTprodDetRep e (-(K : ℤ))
    have e6 := (detRepMergeEquiv (glIrrep (N := N) ν a) K (-K) 0 (by simp)).symm
    exact (detRepZeroEquiv _).symm.trans (e6.trans (e3.trans e4))

/-- **Etingof et al., Definition 4.65 and Theorem 4.66 (i): the `L_λ` are pairwise non-isomorphic.**
`L_ν ⊗ det^a ≅ L_μ ⊗ det^b` (diagrams with at most `N` rows) iff they have the same highest weight
`λ_j = ν_j + a = μ_j + b`. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem glIrrep_equiv_iff {n m : ℕ} (ν : DiagramsOfSize n) (μ : DiagramsOfSize m)
    (hν : ν.1.colLen 0 ≤ N) (hμ : μ.1.colLen 0 ≤ N) (a b : ℤ) :
    Nonempty (Representation.Equiv (glIrrep (N := N) ν a) (glIrrep (N := N) μ b)) ↔
      highestWeight N ν a = highestWeight N μ b := by
  constructor
  · rintro ⟨e⟩
    exact highestWeight_eq_of_equiv ν μ hν hμ a b e
  · intro h
    let K : ℕ := (|a| + |b|).toNat
    have hK : (K : ℤ) = |a| + |b| := Int.toNat_of_nonneg (by positivity)
    obtain ⟨p, hp⟩ : ∃ p : ℕ, a + K = p := ⟨(a + K).toNat, (Int.toNat_of_nonneg (by
      rw [hK]; have := neg_abs_le a; have := abs_nonneg b; linarith)).symm⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, b + K = q := ⟨(b + K).toNat, (Int.toNat_of_nonneg (by
      rw [hK]; have := neg_abs_le b; have := abs_nonneg a; linarith)).symm⟩
    obtain ⟨m1, κ, hκ, hwκ, ⟨e1⟩⟩ := exists_shift_equiv ν hν a K p hp
    obtain ⟨m2, κ', hκ', hwκ', ⟨e2⟩⟩ := exists_shift_equiv μ hμ b K q hq
    have hrow : ∀ j : Fin N, κ.1.rowLen j = κ'.1.rowLen j := by
      intro j
      have h1 := congrFun hwκ j
      have h2 := congrFun hwκ' j
      have h3 := congrFun h j
      simp only [highestWeight] at h1 h2 h3
      have : (κ.1.rowLen j : ℤ) = κ'.1.rowLen j := by rw [← hp, ← hq] at *; linarith
      exact_mod_cast this
    have hm : m1 = m2 := by
      rw [← sum_rowLen_eq κ hκ, ← sum_rowLen_eq κ' hκ']
      exact Finset.sum_congr rfl fun j _ => hrow j
    subst hm
    have : κ = κ' := eq_of_rowLen_eq hκ hκ' hrow
    subst this
    exact ⟨e1.trans e2.symm⟩

/-- **Etingof et al., Definition 4.65: every non-increasing sequence of `N` integers is a highest weight.** -/
@[kb "etingof2011" "Definition 4.65, p. 67"]
theorem exists_highestWeight_eq (lam : Fin N → ℤ) (hlam : Antitone lam) :
    ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧ highestWeight N ν a = lam := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨0, ⟨⊥, by simp⟩, 0, ?_, funext fun j => j.elim0⟩
    by_contra hcon
    push Not at hcon
    exact absurd (YoungDiagram.mem_iff_lt_colLen.2 hcon) (by simp)
  let a : ℤ := lam ⟨N - 1, by omega⟩
  have hge : ∀ j, a ≤ lam j := fun j =>
    hlam (Fin.le_iff_val_le_val.2 (by show (j : ℕ) ≤ N - 1; omega))
  let r : Fin N → ℕ := fun j => (lam j - a).toNat
  have hr : Antitone r := fun i j hij => by
    simp only [r]
    have := hlam hij
    omega
  let ν0 : YoungDiagram := YoungDiagram.ofRowLens (List.ofFn r) (List.sortedGE_ofFn_iff.2 hr)
  have hrow : ∀ j : Fin N, ν0.rowLen j = r j := by
    intro j
    have := YoungDiagram.rowLen_ofRowLens (w := List.ofFn r) (hw := List.sortedGE_ofFn_iff.2 hr)
      ⟨j, by simp⟩
    simpa using this
  have hcol : ν0.colLen 0 ≤ N := by
    by_contra hcon
    push Not at hcon
    have hmem : (N, 0) ∈ ν0 := YoungDiagram.mem_iff_lt_colLen.2 hcon
    obtain ⟨h1, _⟩ := YoungDiagram.mem_ofRowLens.1 hmem
    simp at h1
  refine ⟨ν0.card, ⟨ν0, rfl⟩, a, hcol, funext fun j => ?_⟩
  simp only [highestWeight, hrow, r]
  have := hge j
  omega

/-- **Etingof et al., Theorem 4.66 (i), constituents.**  Every irreducible finite-dimensional rational
representation of `GL_N(ℂ)` (coefficients polynomial in the entries and `1 / det`) is isomorphic to some
`L_λ = L_ν ⊗ det^a`, with `ν` a diagram with at most `N` rows. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem IsRationalRep.exists_equiv_glIrrep {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) (hirr : IsIrredRep ρ) :
    ∃ (n : ℕ) (ν : DiagramsOfSize n) (a : ℤ), ν.1.colLen 0 ≤ N ∧
      Nonempty (Representation.Equiv ρ (glIrrep (N := N) ν a)) := by
  obtain ⟨c, hc⟩ := hρ.exists_polynomial_tprod_detRep
  have hirr' := hirr.tprod_detRep (c : ℤ)
  have := hirr'.1
  obtain ⟨n, hn⟩ := hc.exists_isHomogPolyRep_of_irreducible hirr'.2
  obtain ⟨ν, hν, ⟨e⟩⟩ := exists_equiv_swRepGL_of_isHomogPolyRep hn hirr'
  exact ⟨n, ν, -c, hν, ⟨(detRepZeroEquiv ρ).symm.trans
    ((detRepMergeEquiv ρ c (-c) 0 (by simp)).symm.trans (equivTprodDetRep e (-c)))⟩⟩

/-- **Etingof et al., Theorem 4.66 (i), complete reducibility.**  Every subrepresentation of a finite-dimensional
rational representation of `GL_N(ℂ)` has an invariant complement. -/
@[kb "etingof2011" "Theorem 4.66, p. 67"]
theorem IsRationalRep.exists_isCompl {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ (GL (Fin N) ℂ) W} (hρ : IsRationalRep ρ) (U : Submodule ℂ W)
    (hU : ∀ g, ∀ w ∈ U, ρ g w ∈ U) : ∃ U' : Submodule ℂ W, (∀ g, ∀ w ∈ U', ρ g w ∈ U') ∧ IsCompl U U' := by
  obtain ⟨c, hc⟩ := hρ.exists_polynomial_tprod_detRep
  let e := TensorProduct.rid ℂ W
  have hform := rid_tprod_detRep ρ (c : ℤ)
  let U₁ : Submodule ℂ (W ⊗[ℂ] ℂ) := U.comap e.toLinearMap
  have hU₁ : ∀ g, ∀ x ∈ U₁, (ρ.tprod (detRep N ℂ c)) g x ∈ U₁ := by
    intro g x hx
    simp only [U₁, Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [hform]
    exact U.smul_mem _ (hU g _ hx)
  obtain ⟨C₁, hC₁, hc₁⟩ := hc.exists_isCompl U₁ hU₁
  refine ⟨C₁.map e.toLinearMap, ?_, ?_⟩
  · rintro g _ ⟨x, hx, rfl⟩
    refine ⟨(detVal g c)⁻¹ • (ρ.tprod (detRep N ℂ c)) g x, C₁.smul_mem _ (hC₁ g x hx), ?_⟩
    simp only [LinearEquiv.coe_coe, map_smul, e, hform, smul_smul, inv_mul_cancel₀ (detVal_ne_zero g _),
      one_smul]
  · have := (Submodule.orderIsoMapComap e).isCompl_iff.1 hc₁
    simp only [Submodule.orderIsoMapComap_apply] at this
    rwa [Submodule.map_comap_eq_of_surjective e.surjective] at this

end Rational

end UndergradKB.RepresentationTheory
