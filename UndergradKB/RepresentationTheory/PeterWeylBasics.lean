import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import UndergradKB.Common.Attr
import UndergradKB.RepresentationTheory.PolynomialRepsSum

/-! # Translation-invariant spaces of rational functions on `GL_N(ℂ)` (for Etingof et al., Theorem 4.66 (ii))

Preparation for the Peter-Weyl theorem for `GL_N(ℂ)`.

* `ratFunctions_mul_left`, `ratFunctions_mul_right`: the algebra `R` of rational functions (polynomials in the matrix
  entries and `1 / det`) is stable under left and right translations.
* `homogRatSpace d m`: the functions `Q(x) / det(x)^m`, `Q` homogeneous of degree `d`; a finite-dimensional subspace
  of `R`, stable under right translations (`homogRatSpace_rightTr`), and `R` is the sum of these subspaces
  (`mem_sum_homogRatSpace`).
* `exists_dual_eq_sum_eval`: on a finite-dimensional space of functions every linear functional is a combination of
  finitely many point evaluations.
* `rightRegRep`, `isRationalRep_rightRegRep`: right translation on a finite-dimensional right-invariant subspace of
  `R` is a rational representation.
-/

namespace UndergradKB.RepresentationTheory

open MvPolynomial

variable {N : ℕ}

section Translation

/-- Right translation of a function on `GL_N(ℂ)`: `(rightTr h φ)(x) = φ(x h)`. -/
def rightTr (h : GL (Fin N) ℂ) (φ : GL (Fin N) ℂ → ℂ) : GL (Fin N) ℂ → ℂ := fun x => φ (x * h)

theorem invDetPow_mem (m : ℕ) :
    (fun h : GL (Fin N) ℂ => 1 / (h : Matrix (Fin N) (Fin N) ℂ).det ^ m) ∈ ratFunctions N ℂ :=
  (mem_ratFunctions_iff _).2 ⟨1, m, fun g => by simp⟩

theorem glEntries_mul_left_mem (x : GL (Fin N) ℂ) (p : Fin N × Fin N) :
    (fun h : GL (Fin N) ℂ => glEntries N ℂ (x * h) p) ∈ ratFunctions N ℂ := by
  apply polyFunctions_le_ratFunctions
  refine ⟨∑ l, C ((x : Matrix (Fin N) (Fin N) ℂ) p.1 l) * X (l, p.2), fun h => ?_⟩
  simp [glEntries, Matrix.mul_apply]

theorem glEntries_mul_right_mem (x : GL (Fin N) ℂ) (p : Fin N × Fin N) :
    (fun h : GL (Fin N) ℂ => glEntries N ℂ (h * x) p) ∈ ratFunctions N ℂ := by
  apply polyFunctions_le_ratFunctions
  refine ⟨∑ l, C ((x : Matrix (Fin N) (Fin N) ℂ) l p.2) * X (p.1, l), fun h => ?_⟩
  simp [glEntries, Matrix.mul_apply, mul_comm]

/-- Left translation preserves rational functions. -/
theorem ratFunctions_mul_left (x : GL (Fin N) ℂ) {ψ : GL (Fin N) ℂ → ℂ} (hψ : ψ ∈ ratFunctions N ℂ) :
    (fun h => ψ (x * h)) ∈ ratFunctions N ℂ := by
  obtain ⟨P, m, hP⟩ := (mem_ratFunctions_iff ψ).1 hψ
  have h1 := eval_mem_subalgebra (ratFunctions N ℂ) (fun p h => glEntries N ℂ (x * h) p)
    (glEntries_mul_left_mem x) P
  have h2 := (ratFunctions N ℂ).mul_mem h1 (invDetPow_mem m)
  have h3 := (ratFunctions N ℂ).smul_mem h2 (1 / (x : Matrix (Fin N) (Fin N) ℂ).det ^ m)
  convert h3 using 1
  funext h
  have hx := det_ne_zero' x
  have hh := det_ne_zero' h
  simp only [hP, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Units.val_mul, Matrix.det_mul]
  field_simp
  ring

/-- Right translation preserves rational functions. -/
theorem ratFunctions_mul_right (x : GL (Fin N) ℂ) {ψ : GL (Fin N) ℂ → ℂ} (hψ : ψ ∈ ratFunctions N ℂ) :
    (fun h => ψ (h * x)) ∈ ratFunctions N ℂ := by
  obtain ⟨P, m, hP⟩ := (mem_ratFunctions_iff ψ).1 hψ
  have h1 := eval_mem_subalgebra (ratFunctions N ℂ) (fun p h => glEntries N ℂ (h * x) p)
    (glEntries_mul_right_mem x) P
  have h2 := (ratFunctions N ℂ).mul_mem h1 (invDetPow_mem m)
  have h3 := (ratFunctions N ℂ).smul_mem h2 (1 / (x : Matrix (Fin N) (Fin N) ℂ).det ^ m)
  convert h3 using 1
  funext h
  have hx := det_ne_zero' x
  have hh := det_ne_zero' h
  simp only [hP, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Units.val_mul, Matrix.det_mul]
  field_simp
  ring

end Translation

section Homog

variable (N) in
/-- `Q ↦ (x ↦ Q(x) / det(x)^m)`. -/
noncomputable def ratEval (m : ℕ) : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] (GL (Fin N) ℂ → ℂ) where
  toFun Q x := eval (glEntries N ℂ x) Q / (x : Matrix (Fin N) (Fin N) ℂ).det ^ m
  map_add' Q Q' := by funext x; simp [add_div]
  map_smul' c Q := by funext x; simp [mul_div_assoc]

variable (N) in
/-- The functions `Q(x) / det(x)^m` with `Q` homogeneous of degree `d`. -/
noncomputable def homogRatSpace (d m : ℕ) : Submodule ℂ (GL (Fin N) ℂ → ℂ) :=
  (homogeneousSubmodule (Fin N × Fin N) ℂ d).map (ratEval N m)

instance (d m : ℕ) : FiniteDimensional ℂ (homogRatSpace N d m) := by
  have hle : homogeneousSubmodule (Fin N × Fin N) ℂ d ≤ restrictTotalDegree (Fin N × Fin N) ℂ d := by
    intro Q hQ
    rw [mem_restrictTotalDegree]
    exact (mem_homogeneousSubmodule d Q).1 hQ |>.totalDegree_le
  have : FiniteDimensional ℂ (homogeneousSubmodule (Fin N × Fin N) ℂ d) :=
    Submodule.finiteDimensional_of_le hle
  exact Module.Finite.map _ _

theorem homogRatSpace_le (d m : ℕ) : homogRatSpace N d m ≤ (ratFunctions N ℂ).toSubmodule := by
  rintro _ ⟨Q, _, rfl⟩
  exact (mem_ratFunctions_iff _).2 ⟨Q, m, fun g => rfl⟩

/-- The linear substitution `Q(x) ↦ Q(x h)`. -/
noncomputable def substRight (h : GL (Fin N) ℂ) : Fin N × Fin N → MvPolynomial (Fin N × Fin N) ℂ :=
  fun p => ∑ l, C ((h : Matrix (Fin N) (Fin N) ℂ) l p.2) * X (p.1, l)

theorem eval_aeval_substRight (h x : GL (Fin N) ℂ) (Q : MvPolynomial (Fin N × Fin N) ℂ) :
    eval (glEntries N ℂ x) (aeval (substRight h) Q) = eval (glEntries N ℂ (x * h)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, hp]
    congr 1
    simp [substRight, glEntries, Matrix.mul_apply, mul_comm]

theorem homogRatSpace_rightTr (d m : ℕ) (h : GL (Fin N) ℂ) {φ : GL (Fin N) ℂ → ℂ}
    (hφ : φ ∈ homogRatSpace N d m) : rightTr h φ ∈ homogRatSpace N d m := by
  obtain ⟨Q, hQ, rfl⟩ := hφ
  have hQ' : (aeval (substRight h) Q).IsHomogeneous d := by
    have := ((mem_homogeneousSubmodule d Q).1 hQ).aeval (substRight h) (n := 1) fun p =>
      IsHomogeneous.sum _ _ _ fun l _ => by
        simpa using isHomogeneous_C_mul_X ((h : Matrix (Fin N) (Fin N) ℂ) l p.2) (p.1, l)
    simpa using this
  refine ⟨(1 / (h : Matrix (Fin N) (Fin N) ℂ).det ^ m) • aeval (substRight h) Q,
    Submodule.smul_mem _ _ ((mem_homogeneousSubmodule d _).2 hQ'), ?_⟩
  funext x
  have hx := det_ne_zero' x
  have hh := det_ne_zero' h
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, ratEval, LinearMap.coe_mk, AddHom.coe_mk, rightTr,
    eval_aeval_substRight, Units.val_mul, Matrix.det_mul]
  field_simp
  ring

/-- Every rational function is a finite sum of elements of the spaces `homogRatSpace d m`. -/
theorem mem_sum_homogRatSpace {φ : GL (Fin N) ℂ → ℂ} (hφ : φ ∈ ratFunctions N ℂ) :
    ∃ (m D : ℕ), φ ∈ ⨆ d ∈ Finset.range D, homogRatSpace N d m := by
  obtain ⟨P, m, hP⟩ := (mem_ratFunctions_iff φ).1 hφ
  refine ⟨m, P.totalDegree + 1, ?_⟩
  have : φ = ∑ d ∈ Finset.range (P.totalDegree + 1), ratEval N m (homogeneousComponent d P) := by
    rw [← map_sum, sum_homogeneousComponent]
    funext x
    exact hP x
  rw [this]
  refine Submodule.sum_mem _ fun d hd => ?_
  exact (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd
    ⟨_, (mem_homogeneousSubmodule d _).2 (homogeneousComponent_isHomogeneous d P), rfl⟩))

end Homog

section Evaluation

variable {X : Type*}

/-- On a finite-dimensional space of functions, finitely many points detect zero. -/
theorem exists_finset_eq_zero (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ Y] :
    ∃ s : Finset X, ∀ y ∈ Y, (∀ x ∈ s, y x = 0) → y = 0 := by
  classical
  let K : Finset X → Submodule ℂ Y := fun s =>
    { carrier := {y | ∀ x ∈ s, (y : X → ℂ) x = 0}
      add_mem' := fun ha hb x hx => by simp [ha x hx, hb x hx]
      zero_mem' := fun x _ => rfl
      smul_mem' := fun c y hy x hx => by simp [hy x hx] }
  have hex : ∃ d, ∃ s, Module.finrank ℂ (K s) = d := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  refine ⟨s, fun y hy hys => ?_⟩
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, y x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hlt : K (insert x s) < K s := by
    refine lt_of_le_of_ne (fun z hz x' hx' => hz x' (Finset.mem_insert_of_mem hx')) fun h => ?_
    have hmem : (⟨y, hy⟩ : Y) ∈ K s := hys
    rw [← h] at hmem
    exact hx (hmem x (Finset.mem_insert_self x s))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Nat.find_min' hex ⟨insert x s, rfl⟩
  omega

/-- On a finite-dimensional space of functions, every linear functional is a combination of finitely many point
evaluations. -/
theorem exists_dual_eq_sum_eval (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ Y] (ℓ : Module.Dual ℂ Y) :
    ∃ (s : Finset X) (c : X → ℂ), ∀ y : Y, ℓ y = ∑ x ∈ s, c x * (y : X → ℂ) x := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_eq_zero Y
  let r : Y →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun y x => (y : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    intro y y' h
    apply Subtype.ext
    have := hs (y - y' : Y) (Y.sub_mem y.2 y'.2) fun x hx => by
      have := congrFun h ⟨x, hx⟩
      simp only [r, LinearMap.coe_mk, AddHom.coe_mk] at this
      simp [this]
    exact sub_eq_zero.1 this
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective r (LinearMap.ker_eq_bot.mpr hr)
  refine ⟨s, fun x => if hx : x ∈ s then (ℓ ∘ₗ l) (Pi.single ⟨x, hx⟩ 1) else 0, fun y => ?_⟩
  have e1 : ℓ y = (ℓ ∘ₗ l) (r y) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply l r, hl, LinearMap.id_apply]
  rw [e1, LinearMap.pi_apply_eq_sum_univ (ℓ ∘ₗ l) (r y)]
  rw [← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [dif_pos x.2, smul_eq_mul, r, LinearMap.coe_mk, AddHom.coe_mk]
  rw [mul_comm]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

end Evaluation

section RightRegular

variable (Y : Submodule ℂ (GL (Fin N) ℂ → ℂ)) (hY : ∀ h, ∀ φ ∈ Y, rightTr h φ ∈ Y)

/-- Right translation on a right-invariant space of functions on `GL_N(ℂ)`. -/
noncomputable def rightRegRep : Representation ℂ (GL (Fin N) ℂ) Y where
  toFun h :=
    { toFun := fun φ => ⟨rightTr h φ, hY h φ φ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ x
    show (φ : GL (Fin N) ℂ → ℂ) (x * 1) = _
    rw [mul_one]
    rfl
  map_mul' g h := by
    ext φ x
    show (φ : GL (Fin N) ℂ → ℂ) (x * (g * h)) = (φ : GL (Fin N) ℂ → ℂ) (x * g * h)
    rw [mul_assoc]

theorem rightRegRep_apply (h : GL (Fin N) ℂ) (φ : Y) (x : GL (Fin N) ℂ) :
    (rightRegRep Y hY h φ : GL (Fin N) ℂ → ℂ) x = (φ : GL (Fin N) ℂ → ℂ) (x * h) := rfl

/-- Right translation on a finite-dimensional right-invariant space of rational functions is a rational
representation. -/
theorem isRationalRep_rightRegRep [FiniteDimensional ℂ Y] (hYR : Y ≤ (ratFunctions N ℂ).toSubmodule) :
    IsRationalRep (rightRegRep Y hY) := by
  intro ψ ℓ
  obtain ⟨s, c, hc⟩ := exists_dual_eq_sum_eval Y ℓ
  have : (fun h => ℓ (rightRegRep Y hY h ψ)) = ∑ x ∈ s, c x • fun h => (ψ : GL (Fin N) ℂ → ℂ) (x * h) := by
    funext h
    rw [hc]
    simp [rightRegRep_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun x _ => Subalgebra.smul_mem _ (ratFunctions_mul_left x (hYR ψ.2)) _

end RightRegular

end UndergradKB.RepresentationTheory
