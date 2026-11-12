import Mathlib.Data.Sym.Card
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.GL2
import UndergradKB.RepresentationTheory.CharactersChapter4

/-!
# Counting the conjugacy classes of `GL_2(F_q)`

Etingof et al., §4.24.1 (table): the conjugacy classes of `GL_2(F_q)` are of four kinds, scalar,
parabolic, hyperbolic and elliptic, with `q - 1`, `q - 1`, `(q-1)(q-2)/2` and `q(q-1)/2` classes
respectively, hence `q² - 1` classes in total.  The class sizes were proved in `GL2.lean` and
`CharactersChapter4.lean`; here the classes are enumerated.  No hypothesis on the characteristic is
needed.

The key step: two non-scalar matrices in `GL_2(F)` with the same trace and determinant are
conjugate (both are conjugate to the companion matrix of the characteristic polynomial).
-/

namespace UndergradKB.RepresentationTheory.GL2

open Matrix

universe u

variable {F : Type u} [Field F]

/-- The companion matrix `[[0, -n], [1, t]]` as an element of `GL_2(F)`. -/
noncomputable def compan (t : F) (n : Fˣ) : GL (Fin 2) F :=
  GeneralLinearGroup.mk'' !![0, -(n : F); 1, t] (by simp [Matrix.det_fin_two])

/-- A matrix of `GL_2` is non-scalar. -/
def NonScalar (g : GL (Fin 2) F) : Prop :=
  ¬ ((g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1)

lemma isConj_trace {g h : GL (Fin 2) F} (hgh : IsConj g h) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = Matrix.trace (h : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hgh
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

lemma isConj_det {g h : GL (Fin 2) F} (hgh : IsConj g h) :
    (g : Matrix (Fin 2) (Fin 2) F).det = (h : Matrix (Fin 2) (Fin 2) F).det := by
  have := isConj_iff_eq.1 ((GeneralLinearGroup.det (n := Fin 2) (R := F)).map_isConj hgh)
  have h2 := congrArg (fun u : Fˣ => (u : F)) this
  simpa [GeneralLinearGroup.val_det_apply] using h2

lemma coe_trace_compan (t : F) (n : Fˣ) :
    Matrix.trace (compan t n : Matrix (Fin 2) (Fin 2) F) = t := by
  simp [compan, Matrix.trace_fin_two]

lemma coe_det_compan (t : F) (n : Fˣ) :
    (compan t n : Matrix (Fin 2) (Fin 2) F).det = n := by
  simp [compan, Matrix.det_fin_two]

/-- Over any field some vector `v` among `e₀, e₁, e₀ + e₁` has `v, g v` independent unless `g` is scalar. -/
lemma exists_cyclic {g : GL (Fin 2) F} (hg : NonScalar g) :
    ∃ v0 v1 : F, v0 * ((g : Matrix (Fin 2) (Fin 2) F) 1 0 * v0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 * v1) -
      v1 * ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * v0 + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * v1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hg
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  refine ⟨by linear_combination h1, by linear_combination -h2, ?_⟩
  linear_combination -h3 + h1 + h2

/-- A non-scalar element of `GL_2(F)` is conjugate to the companion matrix of its characteristic
polynomial. -/
lemma isConj_compan {g : GL (Fin 2) F} (hg : NonScalar g) :
    IsConj g (compan (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)) (GeneralLinearGroup.det g)) := by
  obtain ⟨v0, v1, hv⟩ := exists_cyclic hg
  set A : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hA
  let P : GL (Fin 2) F := GeneralLinearGroup.mk''
    !![v0, A 0 0 * v0 + A 0 1 * v1; v1, A 1 0 * v0 + A 1 1 * v1]
    (by
      rw [Matrix.det_fin_two_of]
      exact isUnit_iff_ne_zero.mpr (by intro h; apply hv; linear_combination h))
  have key : g * P = P * compan (Matrix.trace A) (GeneralLinearGroup.det g) := by
    apply Units.ext
    ext i j
    simp only [Units.val_mul, compan, P, coe_mk'']
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
        GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, ← hA] <;> ring
  rw [isConj_iff]
  refine ⟨P⁻¹, ?_⟩
  rw [inv_inv, mul_assoc]
  exact inv_mul_eq_iff_eq_mul.2 key

/-- Two non-scalar elements of `GL_2(F)` with equal trace and determinant are conjugate. -/
lemma isConj_of_trace_det {g h : GL (Fin 2) F} (hg : NonScalar g) (hh : NonScalar h)
    (ht : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = Matrix.trace (h : Matrix (Fin 2) (Fin 2) F))
    (hd : (g : Matrix (Fin 2) (Fin 2) F).det = (h : Matrix (Fin 2) (Fin 2) F).det) : IsConj g h := by
  have hd' : GeneralLinearGroup.det g = GeneralLinearGroup.det h :=
    Units.ext (by simpa [GeneralLinearGroup.val_det_apply] using hd)
  have h1 := isConj_compan hg
  have h2 := isConj_compan hh
  rw [ht, hd'] at h1
  exact h1.trans h2.symm

/-! ### Invariants of the standard representatives -/

lemma nonScalar_upper (x : Fˣ) : NonScalar (upperUnit x 1 : GL (Fin 2) F) := by
  simp [NonScalar, upperUnit]

lemma nonScalar_diag {x y : Fˣ} (h : x ≠ y) : NonScalar (diagUnit x y : GL (Fin 2) F) := by
  simp [NonScalar, diagUnit, Units.val_inj, h]

lemma trace_upper (x : Fˣ) :
    Matrix.trace (upperUnit x 1 : GL (Fin 2) F).1 = (x : F) + x := by
  simp [upperUnit, Matrix.trace_fin_two]

lemma det_upper (x : Fˣ) : (upperUnit x 1 : GL (Fin 2) F).1.det = (x : F) * x := by
  simp [upperUnit, Matrix.det_fin_two]

lemma trace_diag (x y : Fˣ) :
    Matrix.trace (diagUnit x y : GL (Fin 2) F).1 = (x : F) + y := by
  simp [diagUnit, Matrix.trace_fin_two]

lemma det_diag (x y : Fˣ) : (diagUnit x y : GL (Fin 2) F).1.det = (x : F) * y := by
  simp [diagUnit, Matrix.det_fin_two]

lemma nonScalar_elliptic {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    NonScalar (ellipticElt h : GL (Fin 2) F) := by
  simp [NonScalar, ellipticElt, ellUnit]

lemma trace_elliptic {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    Matrix.trace (ellipticElt h : GL (Fin 2) F).1 = t := by
  simp [ellipticElt, ellUnit, Matrix.trace_fin_two]

lemma det_elliptic {t n : F} (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0) :
    (ellipticElt h : GL (Fin 2) F).1.det = n := by
  simp [ellipticElt, ellUnit, Matrix.det_fin_two]

/-! ### The four kinds of classes -/

variable (F) in
/-- The conjugacy classes of scalar matrices `x • 1` in `GL_2(F)`. -/
noncomputable def scalarClasses : Set (ConjClasses (GL (Fin 2) F)) :=
  Set.range fun c : Fˣ => ConjClasses.mk (diagUnit c c)

variable (F) in
/-- The parabolic classes: those of `[[x, 1], [0, x]]`. -/
noncomputable def parabolicClasses : Set (ConjClasses (GL (Fin 2) F)) :=
  Set.range fun x : Fˣ => ConjClasses.mk (upperUnit x 1)

variable (F) in
/-- The hyperbolic classes: those of `diag(x, y)` with `x ≠ y`. -/
noncomputable def hyperbolicClasses : Set (ConjClasses (GL (Fin 2) F)) :=
  {c | ∃ x y : Fˣ, x ≠ y ∧ c = ConjClasses.mk (diagUnit x y)}

variable (F) in
/-- The elliptic classes: those of the companion matrix of a monic quadratic without roots in `F`. -/
noncomputable def ellipticClasses : Set (ConjClasses (GL (Fin 2) F)) :=
  {c | ∃ (t n : F) (h : ∀ x : F, x ^ 2 - t * x + n ≠ 0), c = ConjClasses.mk (ellipticElt h)}

lemma ncard_carrier_mk (g : GL (Fin 2) F) :
    (ConjClasses.mk g).carrier.ncard = (conjugatesOf g).ncard := by
  congr 1

lemma diag_scalar_inj :
    Function.Injective fun c : Fˣ => ConjClasses.mk (diagUnit c c : GL (Fin 2) F) := by
  intro c d h
  have hc : IsConj (diagUnit c c : GL (Fin 2) F) (diagUnit d d) := ConjClasses.mk_eq_mk_iff_isConj.1 h
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 (ncard_conjugatesOf_scalar (F := F) c)
  have h1 : (diagUnit d d : GL (Fin 2) F) ∈ conjugatesOf (diagUnit c c) := hc
  have h2 : (diagUnit c c : GL (Fin 2) F) ∈ conjugatesOf (diagUnit c c) := mem_conjugatesOf_self
  rw [ha] at h1 h2
  have := (Set.mem_singleton_iff.1 h1).trans (Set.mem_singleton_iff.1 h2).symm
  exact (congrArg Prod.fst (diagUnit_injective (a₁ := (d, d)) (a₂ := (c, c)) this)).symm

lemma upper_inj :
    Function.Injective fun x : Fˣ => ConjClasses.mk (upperUnit x 1 : GL (Fin 2) F) := by
  intro x y h
  have hc : IsConj (upperUnit x 1 : GL (Fin 2) F) (upperUnit y 1) := ConjClasses.mk_eq_mk_iff_isConj.1 h
  have ht := isConj_trace hc
  have hd := isConj_det hc
  rw [trace_upper, trace_upper] at ht
  rw [det_upper, det_upper] at hd
  apply Units.ext
  have hab : ((x : F) - y) * ((x : F) + y) = 0 := by linear_combination hd
  rcases mul_eq_zero.1 hab with h0 | h0
  · linear_combination h0
  · have h4 : ((x : F) + x) * 2 = 0 := by linear_combination ht + 2 * h0
    have h5 : (x : F) + x = 0 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact h
      · linear_combination (x : F) * h
    linear_combination h5 - h0

/-- The permutation matrix `[[0, 1], [1, 0]]`. -/
noncomputable def swapElt : GL (Fin 2) F :=
  GeneralLinearGroup.mk'' !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

lemma isConj_diag_swap (x y : Fˣ) : IsConj (diagUnit x y : GL (Fin 2) F) (diagUnit y x) := by
  rw [isConj_iff]
  refine ⟨swapElt, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  ext i j
  simp only [Units.val_mul, swapElt, diagUnit, coe_mk'']
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The class of `diag(x, y)`, as a function of the unordered pair `{x, y}`. -/
noncomputable def hypClass : Sym2 Fˣ → ConjClasses (GL (Fin 2) F) :=
  Sym2.lift ⟨fun x y => ConjClasses.mk (diagUnit x y),
    fun x y => ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_diag_swap x y)⟩

lemma pair_cases {R : Type*} [CommRing R] [IsDomain R] {x y x' y' : R} (hs : x + y = x' + y')
    (hp : x * y = x' * y') : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have h : (x - x') * (x - y') = 0 := by linear_combination x * hs - hp
  rcases mul_eq_zero.1 h with h0 | h0
  · left
    exact ⟨by linear_combination h0, by linear_combination hs - h0⟩
  · right
    exact ⟨by linear_combination h0, by linear_combination hs - h0⟩

lemma hypClass_injective : Function.Injective (hypClass : Sym2 Fˣ → ConjClasses (GL (Fin 2) F)) := by
  intro s s'
  induction s using Sym2.ind with | _ x y =>
  induction s' using Sym2.ind with | _ x' y' =>
  intro h
  have h' : ConjClasses.mk (diagUnit x y : GL (Fin 2) F) = ConjClasses.mk (diagUnit x' y') := h
  have hc := ConjClasses.mk_eq_mk_iff_isConj.1 h'
  have ht := isConj_trace hc
  have hd := isConj_det hc
  rw [trace_diag, trace_diag] at ht
  rw [det_diag, det_diag] at hd
  rcases pair_cases ht hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Units.ext h1, Units.ext h2]
  · rw [Units.ext h1, Units.ext h2, Sym2.eq_swap]

lemma hyperbolicClasses_eq :
    hyperbolicClasses F = (hypClass : Sym2 Fˣ → ConjClasses (GL (Fin 2) F)) '' {s | ¬ s.IsDiag} := by
  ext c
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact ⟨s(x, y), by simpa using hxy, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    induction s using Sym2.ind with | _ x y =>
    exact ⟨x, y, by simpa using hs, rfl⟩

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

lemma sq_sub_choose (q : ℕ) : q * q - (q + 1).choose 2 = q.choose 2 := by
  rcases q with _ | r
  · simp
  · have h1 : (r + 1 + 1).choose 2 = (r + 1).choose 1 + (r + 1).choose 2 :=
      Nat.choose_succ_succ' (r + 1) 1
    have h2 := two_mul_choose_two (r + 1)
    rw [Nat.choose_one_right] at h1
    simp only [Nat.add_sub_cancel] at h2
    have h3 : (r + 1) * (r + 1) = (r + 1 + (r + 1).choose 2) + (r + 1).choose 2 := by
      nlinarith [h2]
    rw [h1]
    omega

/-- The number of hyperbolic classes, in binomial form. -/
lemma ncard_hyperbolicClasses_choose [Finite F] :
    (hyperbolicClasses F).ncard = (Nat.card F - 1).choose 2 := by
  classical
  have := Fintype.ofFinite F
  rw [hyperbolicClasses_eq, Set.ncard_image_of_injective _ hypClass_injective,
    ← Nat.card_coe_set_eq]
  calc Nat.card ↥{s : Sym2 Fˣ | ¬ s.IsDiag} = Nat.card {s : Sym2 Fˣ // ¬ s.IsDiag} := rfl
    _ = Fintype.card {s : Sym2 Fˣ // ¬ s.IsDiag} := Nat.card_eq_fintype_card
    _ = (Fintype.card Fˣ).choose 2 := Sym2.card_subtype_not_diag
    _ = (Nat.card F - 1).choose 2 := by rw [← Nat.card_eq_fintype_card, Nat.card_units]

/-- The pairs `(t, n)` such that `x² - t x + n` has no root in `F`. -/
abbrev IrredPairs (F : Type u) [Field F] : Type u :=
  {p : F × F // ∀ x : F, x ^ 2 - p.1 * x + p.2 ≠ 0}

/-- The class of the companion matrix of an irreducible quadratic. -/
noncomputable def ellClass (p : IrredPairs F) : ConjClasses (GL (Fin 2) F) :=
  ConjClasses.mk (ellipticElt (t := p.1.1) (n := p.1.2) p.2)

lemma ellClass_injective : Function.Injective (ellClass : IrredPairs F → _) := by
  intro p q h
  have hc := ConjClasses.mk_eq_mk_iff_isConj.1 h
  have ht := isConj_trace hc
  have hd := isConj_det hc
  rw [trace_elliptic, trace_elliptic] at ht
  rw [det_elliptic, det_elliptic] at hd
  exact Subtype.ext (Prod.ext ht hd)

lemma ellipticClasses_eq : ellipticClasses F = Set.range (ellClass : IrredPairs F → _) := by
  ext c
  constructor
  · rintro ⟨t, n, h, rfl⟩
    exact ⟨⟨(t, n), h⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.1.1, p.1.2, p.2, rfl⟩

/-- The pair `(x + y, x y)` as a function of the unordered pair `{x, y}`. -/
def redPair : Sym2 F → F × F :=
  Sym2.lift ⟨fun x y => (x + y, x * y), fun x y => by simp [add_comm, mul_comm]⟩

lemma redPair_injective : Function.Injective (redPair : Sym2 F → F × F) := by
  intro s s'
  induction s using Sym2.ind with | _ x y =>
  induction s' using Sym2.ind with | _ x' y' =>
  intro h
  have h1 : x + y = x' + y' := congrArg Prod.fst h
  have h2 : x * y = x' * y' := congrArg Prod.snd h
  rcases pair_cases h1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, Sym2.eq_swap]

lemma irredPairs_eq :
    {p : F × F | ∀ x : F, x ^ 2 - p.1 * x + p.2 ≠ 0} = (Set.range (redPair : Sym2 F → F × F))ᶜ := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range]
  constructor
  · rintro h ⟨s, hs⟩
    induction s using Sym2.ind with | _ x y =>
    apply h x
    rw [← hs]
    simp only [redPair, Sym2.lift_mk]
    ring
  · intro h x hx
    apply h
    refine ⟨s(x, p.1 - x), ?_⟩
    simp only [redPair, Sym2.lift_mk]
    refine Prod.ext (by simp) ?_
    simp only
    linear_combination -hx

/-- The number of elliptic classes, in binomial form. -/
lemma ncard_ellipticClasses_choose [Finite F] :
    (ellipticClasses F).ncard = (Nat.card F).choose 2 := by
  classical
  have := Fintype.ofFinite F
  rw [ellipticClasses_eq, ← Nat.card_coe_set_eq, Nat.card_range_of_injective ellClass_injective]
  have h1 : Nat.card (IrredPairs F) = ({p : F × F | ∀ x : F, x ^ 2 - p.1 * x + p.2 ≠ 0}).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h1, irredPairs_eq, Set.ncard_compl, ← Nat.card_coe_set_eq,
    Nat.card_range_of_injective redPair_injective, Nat.card_prod, Nat.card_eq_fintype_card (α := Sym2 F),
    Sym2.card, ← Nat.card_eq_fintype_card]
  exact sq_sub_choose _

/-- **Etingof et al., §4.24.1 (table)**: `GL_2(F_q)` has `q - 1` conjugacy classes of scalar matrices. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_scalarClasses [Finite F] : (scalarClasses F).ncard = Nat.card F - 1 := by
  rw [← Nat.card_coe_set_eq, scalarClasses, Nat.card_range_of_injective diag_scalar_inj,
    Nat.card_units]

/-- **Etingof et al., §4.24.1 (table)**: `GL_2(F_q)` has `q - 1` parabolic conjugacy classes. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_parabolicClasses [Finite F] : (parabolicClasses F).ncard = Nat.card F - 1 := by
  rw [← Nat.card_coe_set_eq, parabolicClasses, Nat.card_range_of_injective upper_inj,
    Nat.card_units]

/-- **Etingof et al., §4.24.1 (table)**: `GL_2(F_q)` has `(q-1)(q-2)/2` hyperbolic conjugacy classes. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_hyperbolicClasses [Finite F] :
    (hyperbolicClasses F).ncard = (Nat.card F - 1) * (Nat.card F - 2) / 2 := by
  rw [ncard_hyperbolicClasses_choose, Nat.choose_two_right]
  have : Nat.card F - 1 - 1 = Nat.card F - 2 := by omega
  rw [this]

/-- **Etingof et al., §4.24.1 (table)**: `GL_2(F_q)` has `q(q-1)/2` elliptic conjugacy classes. -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem ncard_ellipticClasses [Finite F] :
    (ellipticClasses F).ncard = Nat.card F * (Nat.card F - 1) / 2 := by
  rw [ncard_ellipticClasses_choose, Nat.choose_two_right]

/-! ### Every class is of one of the four kinds -/

/-- Every conjugacy class of `GL_2(F)` is scalar, parabolic, hyperbolic or elliptic. -/
lemma conjClass_cover (c : ConjClasses (GL (Fin 2) F)) :
    c ∈ scalarClasses F ∨ c ∈ parabolicClasses F ∨ c ∈ hyperbolicClasses F ∨
      c ∈ ellipticClasses F := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have hn : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det g).ne_zero
  by_cases hg : NonScalar g
  · obtain ⟨t, ht⟩ : ∃ t, Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = t := ⟨_, rfl⟩
    obtain ⟨n, hnn⟩ : ∃ n, (g : Matrix (Fin 2) (Fin 2) F).det = n := ⟨_, rfl⟩
    by_cases hirr : ∀ x : F, x ^ 2 - t * x + n ≠ 0
    · right; right; right
      refine ⟨t, n, hirr, (ConjClasses.mk_eq_mk_iff_isConj.2
        (isConj_of_trace_det hg (nonScalar_elliptic hirr) ?_ ?_))⟩
      · rw [ht, trace_elliptic]
      · rw [hnn, det_elliptic]
    · push Not at hirr
      obtain ⟨x, hx⟩ := hirr
      have hxy : n = x * (t - x) := by linear_combination hx
      have hx0 : x ≠ 0 := by
        intro h0; apply hn; rw [hnn, hxy, h0]; ring
      have hy0 : t - x ≠ 0 := by
        intro h0; apply hn; rw [hnn, hxy, h0]; ring
      by_cases hxe : x = t - x
      · right; left
        refine ⟨Units.mk0 x hx0, (ConjClasses.mk_eq_mk_iff_isConj.2
          (isConj_of_trace_det hg (nonScalar_upper (Units.mk0 x hx0)) ?_ ?_)).symm⟩
        · rw [trace_upper, ht]; simp only [Units.val_mk0]; linear_combination (-1 : F) * hxe
        · rw [det_upper, hnn]; simp only [Units.val_mk0]; linear_combination hxy - x * hxe
      · right; right; left
        have hne : Units.mk0 x hx0 ≠ Units.mk0 (t - x) hy0 := fun h =>
          hxe (by simpa using congrArg Units.val h)
        refine ⟨Units.mk0 x hx0, Units.mk0 (t - x) hy0, hne, (ConjClasses.mk_eq_mk_iff_isConj.2
          (isConj_of_trace_det hg (nonScalar_diag hne) ?_ ?_))⟩
        · rw [trace_diag, ht]; simp only [Units.val_mk0]; ring
        · rw [det_diag, hnn]; simp only [Units.val_mk0]; exact hxy
  · left
    unfold NonScalar at hg
    obtain ⟨h10, h01, h00⟩ := not_not.1 hg
    have h0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0; apply hn
      simp [Matrix.det_fin_two, h10, h01, ← h00, h0]
    refine ⟨Units.mk0 _ h0, ?_⟩
    have : (diagUnit (Units.mk0 _ h0) (Units.mk0 _ h0) : GL (Fin 2) F) = g := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagUnit, h10, h01, h00]
    simp only [this]

lemma carrier_ncard_eq_of_mem_scalar {c : ConjClasses (GL (Fin 2) F)} (hc : c ∈ scalarClasses F) :
    c.carrier.ncard = 1 := by
  obtain ⟨x, rfl⟩ := hc
  rw [ncard_carrier_mk]
  exact ncard_conjugatesOf_scalar x

lemma carrier_ncard_eq_of_mem_parabolic [Finite F] {c : ConjClasses (GL (Fin 2) F)}
    (hc : c ∈ parabolicClasses F) : c.carrier.ncard = Nat.card F ^ 2 - 1 := by
  obtain ⟨x, rfl⟩ := hc
  rw [ncard_carrier_mk]
  exact ncard_conjugatesOf_parabolic x

lemma carrier_ncard_eq_of_mem_hyperbolic [Finite F] {c : ConjClasses (GL (Fin 2) F)}
    (hc : c ∈ hyperbolicClasses F) : c.carrier.ncard = Nat.card F ^ 2 + Nat.card F := by
  obtain ⟨x, y, hxy, rfl⟩ := hc
  rw [ncard_carrier_mk]
  exact ncard_conjugatesOf_hyperbolic hxy

lemma carrier_ncard_eq_of_mem_elliptic [Finite F] {c : ConjClasses (GL (Fin 2) F)}
    (hc : c ∈ ellipticClasses F) : c.carrier.ncard = Nat.card F ^ 2 - Nat.card F := by
  obtain ⟨t, n, h, rfl⟩ := hc
  rw [ncard_carrier_mk]
  exact ncard_conjugatesOf_elliptic h

lemma disjoint_of_sizes {A B : Set (ConjClasses (GL (Fin 2) F))} {a b : ℕ}
    (hA : ∀ c ∈ A, c.carrier.ncard = a) (hB : ∀ c ∈ B, c.carrier.ncard = b) (hab : a ≠ b) :
    Disjoint A B :=
  Set.disjoint_left.2 fun c hcA hcB => hab ((hA c hcA).symm.trans (hB c hcB))

/-- **Etingof et al., §4.24.1 (table)**: `GL_2(F_q)` has `q² - 1` conjugacy classes in total
(scalar, parabolic, hyperbolic and elliptic classes are pairwise distinct since their sizes
`1`, `q² - 1`, `q² + q`, `q² - q` are). -/
@[kb "etingof2011" "§4.24.1 table, p. 69"]
theorem nat_card_conjClasses [Finite F] :
    Nat.card (ConjClasses (GL (Fin 2) F)) = Nat.card F ^ 2 - 1 := by
  have hq : 2 ≤ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hs : 4 ≤ Nat.card F ^ 2 ∧ 2 * Nat.card F ≤ Nat.card F ^ 2 :=
    ⟨by nlinarith, by nlinarith⟩
  have dSP : Disjoint (scalarClasses F) (parabolicClasses F) :=
    disjoint_of_sizes (fun c hc => carrier_ncard_eq_of_mem_scalar hc)
      (fun c hc => carrier_ncard_eq_of_mem_parabolic hc) (by omega)
  have dSH : Disjoint (scalarClasses F) (hyperbolicClasses F) :=
    disjoint_of_sizes (fun c hc => carrier_ncard_eq_of_mem_scalar hc)
      (fun c hc => carrier_ncard_eq_of_mem_hyperbolic hc) (by omega)
  have dSE : Disjoint (scalarClasses F) (ellipticClasses F) :=
    disjoint_of_sizes (fun c hc => carrier_ncard_eq_of_mem_scalar hc)
      (fun c hc => carrier_ncard_eq_of_mem_elliptic hc) (by omega)
  have dPH : Disjoint (parabolicClasses F) (hyperbolicClasses F) :=
    disjoint_of_sizes (fun c hc => carrier_ncard_eq_of_mem_parabolic hc)
      (fun c hc => carrier_ncard_eq_of_mem_hyperbolic hc) (by omega)
  have dPE : Disjoint (parabolicClasses F) (ellipticClasses F) :=
    disjoint_of_sizes (fun c hc => carrier_ncard_eq_of_mem_parabolic hc)
      (fun c hc => carrier_ncard_eq_of_mem_elliptic hc) (by omega)
  have dHE : Disjoint (hyperbolicClasses F) (ellipticClasses F) :=
    disjoint_of_sizes (fun c hc => carrier_ncard_eq_of_mem_hyperbolic hc)
      (fun c hc => carrier_ncard_eq_of_mem_elliptic hc) (by omega)
  have hcov : (Set.univ : Set (ConjClasses (GL (Fin 2) F))) =
      ((scalarClasses F ∪ parabolicClasses F) ∪ hyperbolicClasses F) ∪ ellipticClasses F := by
    ext c
    simp only [Set.mem_univ, Set.mem_union, true_iff]
    rcases conjClass_cover c with h | h | h | h <;> simp [h]
  have d1 : Disjoint (scalarClasses F ∪ parabolicClasses F) (hyperbolicClasses F) :=
    Set.disjoint_union_left.2 ⟨dSH, dPH⟩
  have d2 : Disjoint ((scalarClasses F ∪ parabolicClasses F) ∪ hyperbolicClasses F)
      (ellipticClasses F) :=
    Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨dSE, dPE⟩, dHE⟩
  rw [← Set.ncard_univ, hcov, Set.ncard_union_eq d2, Set.ncard_union_eq d1,
    Set.ncard_union_eq dSP, ncard_scalarClasses, ncard_parabolicClasses,
    ncard_hyperbolicClasses_choose, ncard_ellipticClasses_choose]
  obtain ⟨r, hr⟩ : ∃ r, Nat.card F = r + 2 := ⟨Nat.card F - 2, by omega⟩
  rw [hr]
  have h1 : (r + 2).choose 2 = (r + 1).choose 1 + (r + 1).choose 2 :=
    Nat.choose_succ_succ' (r + 1) 1
  have h2 := two_mul_choose_two (r + 1)
  rw [Nat.choose_one_right] at h1
  simp only [Nat.add_sub_cancel] at h2
  have e : r + 2 - 1 = r + 1 := by omega
  rw [e, h1]
  symm
  apply Nat.sub_eq_of_eq_add
  nlinarith [h2]

end UndergradKB.RepresentationTheory.GL2
