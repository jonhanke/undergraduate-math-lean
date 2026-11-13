import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import UndergradKB.RepresentationTheory.SymmetricGroup
import UndergradKB.RepresentationTheory.SymmetricGroupSpecht
import UndergradKB.RepresentationTheory.SpechtModules
import UndergradKB.Common.Attr

/-! # Problem 4.68: the reversed Young symmetrizer (Etingof et al., §4.23)

Let `a = a_λ` (row sum) and `b = b_λ` (signed column sum) in `ℂ[S_n]`.

* `anti_inv` : the linear anti-automorphism `g ↦ g⁻¹` of a group algebra (auxiliary).
* `span_colSum_mul_rowSum_linearEquiv` (Problem 4.68 (a)): the left ideal `ℂ[S_n] b a` is isomorphic, as a
  `ℂ[S_n]`-module, to `V_λ = ℂ[S_n] a b`.  The isomorphism is built from right multiplication by `a` and by
  `b` (the inverse after rescaling by the nonzero scalar `c² = s c`).

Differences from the book: the statement is the existence of a module isomorphism (`Nonempty`), for any filling
`T : λ ≃ Fin n`.  To see that `(b a)² = s (b a)` for the same `s` as for `a b` we use the anti-automorphism
`g ↦ g⁻¹`, which fixes `a` and `b`.
-/

namespace UndergradKB.RepresentationTheory

open scoped Classical

/-! ### The anti-automorphism `g ↦ g⁻¹` -/

section AntiInv

variable {G : Type*} [Group G]

/-- The algebra homomorphism `ℂ[G] → ℂ[G]ᵐᵒᵖ` sending `g` to `g⁻¹`. -/
noncomputable def invAlgHom (G : Type*) [Group G] :
    MonoidAlgebra ℂ G →ₐ[ℂ] (MonoidAlgebra ℂ G)ᵐᵒᵖ :=
  MonoidAlgebra.lift ℂ (MonoidAlgebra ℂ G)ᵐᵒᵖ G
    { toFun := fun g => MulOpposite.op (MonoidAlgebra.single g⁻¹ 1)
      map_one' := by simp; rfl
      map_mul' := fun g h => by
        rw [mul_inv_rev, ← MulOpposite.op_mul, MonoidAlgebra.single_mul_single, mul_one] }

/-- The linear anti-automorphism `g ↦ g⁻¹` of `ℂ[G]`. -/
noncomputable def antiInv (x : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  (invAlgHom G x).unop

lemma antiInv_mul (x y : MonoidAlgebra ℂ G) : antiInv (x * y) = antiInv y * antiInv x := by
  simp [antiInv, map_mul]

lemma antiInv_add (x y : MonoidAlgebra ℂ G) : antiInv (x + y) = antiInv x + antiInv y := by
  simp [antiInv, map_add]

lemma antiInv_smul (r : ℂ) (x : MonoidAlgebra ℂ G) : antiInv (r • x) = r • antiInv x := by
  simp [antiInv, map_smul]

lemma antiInv_single (g : G) (r : ℂ) :
    antiInv (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  simp [antiInv, invAlgHom, MonoidAlgebra.lift_single]

lemma antiInv_sum {ι : Type*} (s : Finset ι) (f : ι → MonoidAlgebra ℂ G) :
    antiInv (∑ i ∈ s, f i) = ∑ i ∈ s, antiInv (f i) := by
  simp [antiInv, map_sum]

variable [Fintype G]

/-- A twisted sum over a subgroup by an inversion-symmetric character is fixed by `antiInv`. -/
lemma antiInv_twistedSum (H : Subgroup G) (χ : G →* ℂ) (hχ : ∀ g, χ g⁻¹ = χ g) :
    antiInv (twistedSum H χ) = twistedSum H χ := by
  unfold twistedSum
  rw [antiInv_sum]
  refine Fintype.sum_equiv (Equiv.inv H) _ _ (fun g => ?_)
  rw [antiInv_smul, antiInv_single]
  show _ = χ ((g : G)⁻¹) • _
  rw [hχ]
  rfl

end AntiInv

lemma signChar_inv {α : Type*} [DecidableEq α] [Fintype α] (g : Equiv.Perm α) :
    signChar α g⁻¹ = signChar α g := by
  simp [signChar]

section PartA

variable {mu : YoungDiagram}

lemma antiInv_rowSum (T : YoungTableau mu) : antiInv (rowSum T) = rowSum T :=
  antiInv_twistedSum _ _ (fun g => by simp)

lemma antiInv_colSum (T : YoungTableau mu) : antiInv (colSum T) = colSum T :=
  antiInv_twistedSum _ _ (fun g => signChar_inv g)

lemma antiInv_youngSymmetrizer (T : YoungTableau mu) :
    antiInv (youngSymmetrizer T) = colSum T * rowSum T := by
  rw [youngSymmetrizer, antiInv_mul, antiInv_rowSum, antiInv_colSum]

/-- The scalar `s ≠ 0` with `c² = s c` and, for the reversed symmetrizer, `(b a)² = s (b a)`. -/
lemma exists_scalar_youngSymmetrizer (T : YoungTableau mu) :
    ∃ s : ℂ, s ≠ 0 ∧ youngSymmetrizer T * youngSymmetrizer T = s • youngSymmetrizer T ∧
      (colSum T * rowSum T) * (colSum T * rowSum T) = s • (colSum T * rowSum T) := by
  obtain ⟨hdim, hk⟩ := youngSymmetrizer_mul_self T
  refine ⟨_, div_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.2 hdim), hk, ?_⟩
  have := congrArg antiInv hk
  rwa [antiInv_mul, antiInv_smul, antiInv_youngSymmetrizer] at this

end PartA

/-! ### Right multiplication between left ideals -/

section RightMul

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Right multiplication by `u`, rescaled by `r`, as an `A`-linear map between left ideals, given that `u`
carries `I` into `J`. -/
noncomputable def rightMulIdeal (I J : Ideal A) (u : A) (r : ℂ) (h : ∀ v ∈ I, v * u ∈ J) :
    I →ₗ[A] J where
  toFun v := ⟨r • (v.1 * u), Submodule.smul_of_tower_mem _ r (h _ v.2)⟩
  map_add' x y := by
    apply Subtype.ext
    simp [add_mul, smul_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [mul_assoc]

lemma rightMulIdeal_apply (I J : Ideal A) (u : A) (r : ℂ) (h : ∀ v ∈ I, v * u ∈ J) (v : I) :
    (rightMulIdeal I J u r h v : A) = r • (v.1 * u) := rfl

end RightMul

section PartA2

variable {mu : YoungDiagram}

/-- **Problem 4.68 (a).** The left ideal `ℂ[S_n] b_T a_T` is isomorphic to the Specht module
`V = ℂ[S_n] a_T b_T`, as a module over the group algebra. -/
@[kb "etingof2011" "Problem 4.68, p. 68"]
theorem span_colSum_mul_rowSum_linearEquiv (T : YoungTableau mu) :
    Nonempty (Ideal.span {youngSymmetrizer T} ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))]
      Ideal.span {colSum T * rowSum T}) := by
  obtain ⟨s, hs0, hc, he⟩ := exists_scalar_youngSymmetrizer T
  have hf : ∀ v ∈ Ideal.span {youngSymmetrizer T}, v * (rowSum T) ∈ Ideal.span {(colSum T) * (rowSum T)} := by
    intro v hv
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hv
    exact Ideal.mem_span_singleton'.2 ⟨z * (rowSum T), by simp [youngSymmetrizer, mul_assoc]⟩
  have hg : ∀ v ∈ Ideal.span {(colSum T) * (rowSum T)}, v * (colSum T) ∈ Ideal.span {youngSymmetrizer T} := by
    intro v hv
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hv
    exact Ideal.mem_span_singleton'.2 ⟨z * (colSum T), by simp [youngSymmetrizer, mul_assoc]⟩
  refine ⟨LinearEquiv.ofLinearMap (rightMulIdeal _ _ (rowSum T) 1 hf) (rightMulIdeal _ _ (colSum T) s⁻¹ hg) ?_ ?_⟩
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 w.2
    simp only [LinearMap.comp_apply, rightMulIdeal_apply, LinearMap.id_apply]
    have key : (w : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))) * (colSum T) * (rowSum T) = s • (w : _) := by
      rw [← hz]
      calc z * ((colSum T) * (rowSum T)) * (colSum T) * (rowSum T) = z * (((colSum T) * (rowSum T)) * ((colSum T) * (rowSum T))) := by simp only [mul_assoc]
        _ = s • (z * ((colSum T) * (rowSum T))) := by rw [he, mul_smul_comm]
    rw [smul_mul_assoc, key, one_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · apply LinearMap.ext
    intro w
    apply Subtype.ext
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 w.2
    simp only [LinearMap.comp_apply, rightMulIdeal_apply, LinearMap.id_apply]
    have key : (w : MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card))) * (rowSum T) * (colSum T) = s • (w : _) := by
      rw [← hz]
      calc z * youngSymmetrizer T * (rowSum T) * (colSum T)
          = z * (youngSymmetrizer T * youngSymmetrizer T) := by
            simp only [youngSymmetrizer, mul_assoc]
        _ = s • (z * youngSymmetrizer T) := by rw [hc, mul_smul_comm]
    rw [one_smul, key, smul_smul, inv_mul_cancel₀ hs0, one_smul]

/-! ### The version for an arbitrary filling `T : λ ≃ Fin n` -/

theorem span_colSumN_mul_rowSumN_linearEquiv {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) :
    Nonempty (Ideal.span {youngSymmetrizerN T} ≃ₗ[MonoidAlgebra ℂ (Equiv.Perm (Fin n))]
      Ideal.span {colSumN T * rowSumN T}) := by
  have hn := card_eq_of_equiv T
  subst hn
  exact span_colSum_mul_rowSum_linearEquiv T

/-! ### The sign twist -/

section Twist

variable {G : Type*} [Group G]

/-- The algebra endomorphism `g ↦ χ(g) g` of `ℂ[G]`, for a character `χ : G →* ℂ`. -/
noncomputable def twistAlgHom (χ : G →* ℂ) : MonoidAlgebra ℂ G →ₐ[ℂ] MonoidAlgebra ℂ G :=
  MonoidAlgebra.lift ℂ (MonoidAlgebra ℂ G) G
    { toFun := fun g => χ g • MonoidAlgebra.single g 1
      map_one' := by simp; rfl
      map_mul' := fun g h => by
        rw [map_mul, smul_mul_smul_comm, MonoidAlgebra.single_mul_single, mul_one] }

lemma twistAlgHom_single (χ : G →* ℂ) (g : G) :
    twistAlgHom χ (MonoidAlgebra.single g 1) = χ g • MonoidAlgebra.single g 1 := by
  simp [twistAlgHom, MonoidAlgebra.lift_single]

/-- The twist is equivariant up to the character: `φ(g x) = χ(g) g φ(x)`. -/
lemma twistAlgHom_single_mul (χ : G →* ℂ) (g : G) (x : MonoidAlgebra ℂ G) :
    twistAlgHom χ (MonoidAlgebra.single g 1 * x) =
      χ g • (MonoidAlgebra.single g 1 * twistAlgHom χ x) := by
  rw [map_mul, twistAlgHom_single, smul_mul_assoc]

/-- If `χ² = 1` the twist is an involution. -/
lemma twistAlgHom_twistAlgHom (χ : G →* ℂ) (hχ : ∀ g, χ g * χ g = 1) (x : MonoidAlgebra ℂ G) :
    twistAlgHom χ (twistAlgHom χ x) = x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single g r =>
    have h1 : (MonoidAlgebra.single g r : MonoidAlgebra ℂ G) = r • MonoidAlgebra.single g 1 := by
      rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_smul, map_smul, twistAlgHom_single, map_smul, twistAlgHom_single, smul_smul,
      smul_smul, mul_assoc, hχ, mul_one]

/-- `φ(ℂ[G] a) = ℂ[G] φ(a)`: membership in a principal left ideal is preserved by the twist. -/
lemma twistAlgHom_mem_span (χ : G →* ℂ) (hχ : ∀ g, χ g * χ g = 1) (x y : MonoidAlgebra ℂ G) :
    twistAlgHom χ y ∈ Ideal.span {twistAlgHom χ x} ↔ y ∈ Ideal.span {x} := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
    refine Ideal.mem_span_singleton'.2 ⟨twistAlgHom χ z, ?_⟩
    have := congrArg (twistAlgHom χ) hz
    rwa [map_mul, twistAlgHom_twistAlgHom χ hχ, twistAlgHom_twistAlgHom χ hχ] at this
  · intro h
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 h
    exact Ideal.mem_span_singleton'.2 ⟨twistAlgHom χ z, by rw [map_mul]⟩

variable [Fintype G]

lemma twistAlgHom_twistedSum (H : Subgroup G) (ψ χ : G →* ℂ) :
    twistAlgHom χ (twistedSum H ψ) = ∑ g : H, (ψ g * χ g) • MonoidAlgebra.single (g : G) 1 := by
  unfold twistedSum
  rw [map_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [map_smul, twistAlgHom_single, smul_smul]

end Twist

lemma signChar_mul_self {α : Type*} [DecidableEq α] [Fintype α] (g : Equiv.Perm α) :
    signChar α g * signChar α g = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [signChar, h]

/-! ### The transposed filling and Problem 4.68 (b) -/

/-- The filling of the conjugate diagram `λ*` obtained by transposing the boxes of a filling `T` of `λ`
(rows of `T'` are the columns of `T`). -/
def transposeTableau {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) : la.transpose ≃ Fin n :=
  (Equiv.mk (fun x : la.transpose => (⟨x.1.swap, YoungDiagram.mem_transpose.1 x.2⟩ : la))
    (fun y : la => (⟨y.1.swap, YoungDiagram.mem_transpose.2 (by simp [y.2])⟩ : la.transpose))
    (fun x => by ext <;> rfl) (fun y => by ext <;> rfl)).trans T

section TwistSymmetrizers

variable {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n)

lemma twist_rowSumN :
    twistAlgHom (signChar (Fin n)) (rowSumN T) = colSumN (transposeTableau T) := by
  unfold rowSumN colSumN
  rw [twistAlgHom_twistedSum]
  unfold twistedSum
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp

lemma twist_colSumN :
    twistAlgHom (signChar (Fin n)) (colSumN T) = rowSumN (transposeTableau T) := by
  unfold rowSumN colSumN
  rw [twistAlgHom_twistedSum]
  unfold twistedSum
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [signChar_mul_self]
  rfl

lemma twist_youngSymmetrizerN :
    twistAlgHom (signChar (Fin n)) (youngSymmetrizerN T) =
      colSumN (transposeTableau T) * rowSumN (transposeTableau T) := by
  rw [youngSymmetrizerN, map_mul, twist_rowSumN, twist_colSumN]

end TwistSymmetrizers

/-- **Problem 4.68 (b).** If `T'` is the transposed filling of the conjugate diagram `λ*`, there is a linear
isomorphism `e : V_λ → V_{λ*}` of the left ideals `ℂ[S_n] c_T` and `ℂ[S_n] c_{T'}` with
`e (g v) = sign(g) g e(v)`, i.e. `V_λ ⊗ sign ≅ V_{λ*}` as representations of `S_n` (equivalently
`V_{λ*} ⊗ sign ≅ V_λ`).  It is the composite of the sign twist `φ` (which sends `ℂ[S_n] c_T` onto
`ℂ[S_n] φ(c_T) = ℂ[S_n] b_{T'} a_{T'}`) with the isomorphism of part (a). -/
@[kb "etingof2011" "Problem 4.68, p. 68"]
theorem exists_linearEquiv_sign_twist {la : YoungDiagram} {n : ℕ} (T : la ≃ Fin n) :
    ∃ e : Ideal.span {youngSymmetrizerN T} ≃ₗ[ℂ] Ideal.span {youngSymmetrizerN (transposeTableau T)},
      ∀ (g : Equiv.Perm (Fin n)) v,
        e ((MonoidAlgebra.single g 1 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) • v) =
          signChar (Fin n) g • ((MonoidAlgebra.single g 1 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) • e v) := by
  set φ := twistAlgHom (signChar (Fin n)) with hφ
  set d := colSumN (transposeTableau T) * rowSumN (transposeTableau T) with hd
  have hφd : φ (youngSymmetrizerN T) = d := twist_youngSymmetrizerN T
  have hχ : ∀ g : Equiv.Perm (Fin n), signChar (Fin n) g * signChar (Fin n) g = 1 := signChar_mul_self
  have F1 : ∀ y ∈ Ideal.span {youngSymmetrizerN T}, φ y ∈ Ideal.span {d} := fun y hy => by
    rw [← hφd]
    exact (twistAlgHom_mem_span _ hχ _ _).2 hy
  have F2 : ∀ w ∈ Ideal.span {d}, φ w ∈ Ideal.span {youngSymmetrizerN T} := fun w hw =>
    (twistAlgHom_mem_span _ hχ (youngSymmetrizerN T) (φ w)).1
      (by rw [hφ, twistAlgHom_twistAlgHom _ hχ]; rw [← hφd] at hw; exact hw)
  let e1 : Ideal.span {youngSymmetrizerN T} ≃ₗ[ℂ] Ideal.span {d} :=
    { toFun := fun v => ⟨φ v.1, F1 _ v.2⟩
      invFun := fun w => ⟨φ w.1, F2 _ w.2⟩
      map_add' := fun x y => Subtype.ext (map_add φ _ _)
      map_smul' := fun r x => Subtype.ext (map_smul φ r x.1)
      left_inv := fun v => Subtype.ext (twistAlgHom_twistAlgHom _ hχ _)
      right_inv := fun w => Subtype.ext (twistAlgHom_twistAlgHom _ hχ _) }
  obtain ⟨e2⟩ := span_colSumN_mul_rowSumN_linearEquiv (transposeTableau T)
  refine ⟨e1.trans (e2.symm.restrictScalars ℂ), fun g v => ?_⟩
  have h1 : e1 ((MonoidAlgebra.single g 1 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) • v) =
      signChar (Fin n) g • ((MonoidAlgebra.single g 1 : MonoidAlgebra ℂ (Equiv.Perm (Fin n))) • e1 v) :=
    Subtype.ext (twistAlgHom_single_mul _ g v.1)
  simp only [LinearEquiv.trans_apply, h1]
  rw [map_smul, LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply, map_smul]

end PartA2

end UndergradKB.RepresentationTheory
