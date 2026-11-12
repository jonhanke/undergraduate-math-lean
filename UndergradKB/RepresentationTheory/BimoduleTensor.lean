import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Algebra.Opposite
import UndergradKB.Common.Attr

/-! # Tensor products of bimodules over noncommutative algebras (Etingof et al., Exercise after Problem 1.49)

Mathlib's `TensorProduct` requires a commutative base ring, so the tensor product `M ⊗_B N` of a right
`B`-module `M` and a left `B`-module `N` over a possibly noncommutative ring `B` is not available.
This file supplies the missing bridging definition.

Setting.  `k` is a commutative ring, `B` a ring.  A right `B`-module is a module over `Bᵐᵒᵖ`
(Mathlib's `MulOpposite`), with `m • b` written `MulOpposite.op b • m`.  Both `M` and `N` are also
`k`-modules.  We define `BalTensor k B M N` as the quotient of `M ⊗[k] N` by the `k`-span of the
elements `(op b • m) ⊗ n - m ⊗ (b • n)`.  Its universal property (`BalTensor.lift`) says that
`k`-bilinear maps that are balanced over `B` factor uniquely through it.

Results.
* If `S` acts on the left of `M` and `T` on the right of `N` (commuting with the `B`-actions and with
  `k`), then `S` and `T` act on `BalTensor k B M N` and the two actions commute; with `S = A`,
  `T = Cᵐᵒᵖ` this makes `M ⊗_B N` an `(A, C)`-bimodule.
* Associativity `(M ⊗_B N) ⊗_C P ≃ M ⊗_B (N ⊗_C P)`, a `k`-linear equivalence compatible with the
  outer left and right actions.
* The Hom-tensor adjunction between `C`-linear maps `M ⊗_B N → P` and `B`-linear maps
  `M → Hom_C(N, P)`.
-/

namespace UndergradKB.RepresentationTheory

open TensorProduct MulOpposite

section Defs

variable (k B M N : Type*) [CommRing k] [Ring B] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module Bᵐᵒᵖ M] [Module B N]

/-- The `k`-submodule of `M ⊗[k] N` spanned by the elements `(m b) ⊗ n - m ⊗ (b n)`, which a tensor
product over `B` must kill. -/
def balancer : Submodule k (M ⊗[k] N) :=
  Submodule.span k
    {x | ∃ (b : B) (m : M) (n : N), x = ((op b • m) ⊗ₜ[k] n) - m ⊗ₜ[k] (b • n)}

/-- **Etingof et al., Exercise after Problem 1.49** (bridging definition): the tensor product
`M ⊗_B N` of a right `B`-module `M` and a left `B`-module `N` over a possibly noncommutative ring,
as a quotient of `M ⊗[k] N`. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
def BalTensor : Type _ := (M ⊗[k] N) ⧸ balancer k B M N

instance : AddCommGroup (BalTensor k B M N) :=
  inferInstanceAs (AddCommGroup ((M ⊗[k] N) ⧸ balancer k B M N))

instance : Module k (BalTensor k B M N) :=
  inferInstanceAs (Module k ((M ⊗[k] N) ⧸ balancer k B M N))

end Defs

namespace BalTensor

section Basic

variable {k B M N : Type*} [CommRing k] [Ring B] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module Bᵐᵒᵖ M] [Module B N]

/-- The canonical `k`-bilinear map `M × N → M ⊗_B N`. -/
def tmul (k B : Type*) {M N : Type*} [CommRing k] [Ring B] [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N] [Module Bᵐᵒᵖ M] [Module B N] :
    M →ₗ[k] N →ₗ[k] BalTensor k B M N :=
  (TensorProduct.mk k M N).compr₂ (balancer k B M N).mkQ

/-- The defining balancing relation `(m b) ⊗ n = m ⊗ (b n)`. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
theorem tmul_balance (b : B) (m : M) (n : N) :
    tmul k B (op b • m) n = tmul k B m (b • n) := by
  have h : ((op b • m) ⊗ₜ[k] n) - m ⊗ₜ[k] (b • n) ∈ balancer k B M N :=
    Submodule.subset_span ⟨b, m, n, rfl⟩
  have h2 := (Submodule.Quotient.mk_eq_zero (balancer k B M N)).2 h
  rw [Submodule.Quotient.mk_sub] at h2
  exact sub_eq_zero.1 h2

theorem tmul_balance' (b : Bᵐᵒᵖ) (m : M) (n : N) :
    tmul k B (b • m) n = tmul k B m (b.unop • n) := by
  simpa using tmul_balance (k := k) (B := B) b.unop m n

/-- The universal property: a `k`-bilinear map balanced over `B` induces a linear map on the tensor
product over `B`. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
def lift {P : Type*} [AddCommGroup P] [Module k P] (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (b : B) (m : M) (n : N), f (op b • m) n = f m (b • n)) :
    BalTensor k B M N →ₗ[k] P :=
  (balancer k B M N).liftQ (TensorProduct.lift f) (by
    rw [balancer, Submodule.span_le]
    rintro _ ⟨b, m, n, rfl⟩
    simp [hf])

@[simp]
theorem lift_tmul {P : Type*} [AddCommGroup P] [Module k P] (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (b : B) (m : M) (n : N), f (op b • m) n = f m (b • n)) (m : M) (n : N) :
    lift f hf (tmul k B m n) = f m n := rfl

theorem induction_on {C : BalTensor k B M N → Prop} (x : BalTensor k B M N)
    (ht : ∀ m n, C (tmul k B m n)) (hadd : ∀ x y, C x → C y → C (x + y)) : C x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (balancer k B M N) x
  exact TensorProduct.inductionOn (motive := fun z => C (Submodule.Quotient.mk z)) z ht
    (fun x y hx hy => hadd (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) hx hy)

theorem hom_ext {R : Type*} [AddCommGroup R] [Module k R] {f g : BalTensor k B M N →ₗ[k] R}
    (h : ∀ m n, f (tmul k B m n) = g (tmul k B m n)) : f = g :=
  LinearMap.ext fun x =>
    induction_on (C := fun x => f x = g x) x h (fun x y hx hy => by simp [hx, hy])

end Basic

section Actions

variable {k B M N : Type*} [CommRing k] [Ring B] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module Bᵐᵒᵖ M] [Module B N]

variable (k B M N) in
/-- Left action of `s` on `M ⊗_B N`, through the action on `M`. -/
def leftAct (S : Type*) [Semiring S] [Module S M] [SMulCommClass S Bᵐᵒᵖ M] [SMulCommClass S k M]
    (s : S) : BalTensor k B M N →ₗ[k] BalTensor k B M N :=
  lift ((tmul k B).comp (DistribSMul.toLinearMap k M s)) (by
    intro b m n
    show tmul k B (s • op b • m) n = tmul k B (s • m) (b • n)
    rw [smul_comm s (op b) m, tmul_balance])

variable (k B M N) in
/-- Right action of `t` on `M ⊗_B N`, through the action on `N`. -/
def rightAct (T : Type*) [Semiring T] [Module T N] [SMulCommClass B T N] [SMulCommClass T k N]
    (t : T) : BalTensor k B M N →ₗ[k] BalTensor k B M N :=
  lift ((tmul k B).compl₂ (DistribSMul.toLinearMap k N t)) (by
    intro b m n
    show tmul k B (op b • m) (t • n) = tmul k B m (t • b • n)
    rw [← smul_comm b t n, tmul_balance])

variable {S : Type*} [Semiring S] [Module S M] [SMulCommClass S Bᵐᵒᵖ M] [SMulCommClass S k M]
variable {T : Type*} [Semiring T] [Module T N] [SMulCommClass B T N] [SMulCommClass T k N]

@[simp]
theorem leftAct_tmul (s : S) (m : M) (n : N) :
    leftAct k B M N S s (tmul k B m n) = tmul k B (s • m) n := rfl

@[simp]
theorem rightAct_tmul (t : T) (m : M) (n : N) :
    rightAct k B M N T t (tmul k B m n) = tmul k B m (t • n) := rfl

variable (S) in
/-- The left action of `S` as a ring homomorphism to the `k`-endomorphisms. -/
def leftHom : S →+* Module.End k (BalTensor k B M N) where
  toFun := leftAct k B M N S
  map_one' := hom_ext fun m n => by simp
  map_mul' s t := hom_ext fun m n => by simp [mul_smul]
  map_zero' := hom_ext fun m n => by simp
  map_add' s t := hom_ext fun m n => by simp [add_smul]

variable (T) in
/-- The right action of `T` as a ring homomorphism to the `k`-endomorphisms (opposite order is
absorbed because `T` is taken to be a left module of `N`, as with `T = Cᵐᵒᵖ`). -/
def rightHom : T →+* Module.End k (BalTensor k B M N) where
  toFun := rightAct k B M N T
  map_one' := hom_ext fun m n => by simp
  map_mul' s t := hom_ext fun m n => by simp [mul_smul]
  map_zero' := hom_ext fun m n => by simp
  map_add' s t := hom_ext fun m n => by simp [add_smul]

/-- `S` acts on the left of `M ⊗_B N`.  (Low priority so that the `k`-module structure is the
quotient one.) -/
instance (priority := low) leftModule : Module S (BalTensor k B M N) :=
  Module.compHom (BalTensor k B M N) (leftHom (k := k) (B := B) (M := M) (N := N) S)

/-- `T` acts on `M ⊗_B N` through its action on `N`. -/
instance (priority := low) rightModule : Module T (BalTensor k B M N) :=
  Module.compHom (BalTensor k B M N) (rightHom (k := k) (B := B) (M := M) (N := N) T)

theorem smul_def_left (s : S) (x : BalTensor k B M N) : s • x = leftAct k B M N S s x := rfl

theorem smul_def_right (t : T) (x : BalTensor k B M N) : t • x = rightAct k B M N T t x := rfl

@[simp]
theorem smul_tmul_left (s : S) (m : M) (n : N) :
    s • tmul k B m n = tmul k B (s • m) n := rfl

@[simp]
theorem smul_tmul_right (t : T) (m : M) (n : N) :
    t • tmul k B m n = tmul k B m (t • n) := rfl

instance : SMulCommClass S k (BalTensor k B M N) :=
  ⟨fun s c x => (leftAct k B M N S s).map_smul c x⟩

instance : SMulCommClass k S (BalTensor k B M N) :=
  (inferInstance : SMulCommClass S k (BalTensor k B M N)).symm

instance : SMulCommClass T k (BalTensor k B M N) :=
  ⟨fun t c x => (rightAct k B M N T t).map_smul c x⟩

instance : SMulCommClass k T (BalTensor k B M N) :=
  (inferInstance : SMulCommClass T k (BalTensor k B M N)).symm

/-- The left action (through `M`) and the right action (through `N`) on `M ⊗_B N` commute.  With
`M` an `(A, B)`-bimodule and `N` a `(B, C)`-bimodule (`S = A`, `T = Cᵐᵒᵖ`), this makes `M ⊗_B N` an
`(A, C)`-bimodule. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
instance : SMulCommClass S T (BalTensor k B M N) :=
  ⟨fun s t x => induction_on (C := fun x => s • t • x = t • s • x) x (fun m n => by simp)
    (fun x y hx hy => by simp [hx, hy])⟩

instance : SMulCommClass T S (BalTensor k B M N) :=
  (inferInstance : SMulCommClass S T (BalTensor k B M N)).symm

end Actions

section Assoc

variable {k : Type*} [CommRing k] {B C : Type*} [Ring B] [Ring C]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module Bᵐᵒᵖ M] [Module B N] [Module Cᵐᵒᵖ N] [Module C P]
  [SMulCommClass B Cᵐᵒᵖ N] [SMulCommClass B k N] [SMulCommClass Cᵐᵒᵖ k N]

variable (k B C M N P) in
/-- Forward map of associativity, on the level of balanced bilinear data:
`m ↦ n ↦ p ↦ m ⊗ (n ⊗ p)`. -/
def assocFwdBilin :
    M →ₗ[k] N →ₗ[k] (P →ₗ[k] BalTensor k B M (BalTensor k C N P)) :=
  LinearMap.mk₂ k (fun m n => (tmul k B m).comp (tmul k C n))
    (fun m₁ m₂ n => LinearMap.ext fun p => by simp)
    (fun c m n => LinearMap.ext fun p => by simp)
    (fun m n₁ n₂ => LinearMap.ext fun p => by simp)
    (fun c m n => LinearMap.ext fun p => by simp)

variable (k B C M N P) in
/-- Forward map of associativity on `(M ⊗_B N) ⊗[k] P`-data, `(m ⊗ n) ↦ p ↦ m ⊗ (n ⊗ p)`. -/
def assocFwdAux :
    BalTensor k B M N →ₗ[k] (P →ₗ[k] BalTensor k B M (BalTensor k C N P)) :=
  lift (assocFwdBilin k B C M N P) (by
    intro b m n
    refine LinearMap.ext fun p => ?_
    show tmul k B (op b • m) (tmul k C n p) = tmul k B m (tmul k C (b • n) p)
    rw [tmul_balance, smul_tmul_left])

omit [SMulCommClass Cᵐᵒᵖ k N] in
@[simp]
theorem assocFwdAux_tmul (m : M) (n : N) (p : P) :
    assocFwdAux k B C M N P (tmul k B m n) p = tmul k B m (tmul k C n p) := rfl

variable (k B C M N P) in
/-- The forward map `(M ⊗_B N) ⊗_C P → M ⊗_B (N ⊗_C P)`. -/
def assocFwd :
    BalTensor k C (BalTensor k B M N) P →ₗ[k] BalTensor k B M (BalTensor k C N P) :=
  lift (assocFwdAux k B C M N P) (by
    intro c q p
    refine induction_on
      (C := fun q => assocFwdAux k B C M N P (op c • q) p = assocFwdAux k B C M N P q (c • p)) q
      (fun m n => ?_) (fun x y hx hy => by simp [smul_add, hx, hy])
    rw [smul_tmul_right]
    show tmul k B m (tmul k C (op c • n) p) = tmul k B m (tmul k C n (c • p))
    rw [tmul_balance])

@[simp]
theorem assocFwd_tmul (m : M) (n : N) (p : P) :
    assocFwd k B C M N P (tmul k C (tmul k B m n) p) = tmul k B m (tmul k C n p) := rfl

variable (k B C M N P) in
/-- Auxiliary map for the inverse of associativity: fix `m` and send `n ⊗ p ↦ (m ⊗ n) ⊗ p`. -/
def assocBwdInner (m : M) :
    BalTensor k C N P →ₗ[k] BalTensor k C (BalTensor k B M N) P :=
  lift ((tmul k C).comp (tmul k B m)) (by
    intro c n p
    show tmul k C (tmul k B m (op c • n)) p = tmul k C (tmul k B m n) (c • p)
    rw [← smul_tmul_right (op c) m n]
    exact tmul_balance c (tmul k B m n) p)

omit [SMulCommClass B k N] in
@[simp]
theorem assocBwdInner_tmul (m : M) (n : N) (p : P) :
    assocBwdInner k B C M N P m (tmul k C n p) = tmul k C (tmul k B m n) p := rfl

variable (k B C M N P) in
/-- The inverse of associativity on bilinear data. -/
def assocBwdBilin :
    M →ₗ[k] BalTensor k C N P →ₗ[k] BalTensor k C (BalTensor k B M N) P :=
  LinearMap.mk₂ k (fun m x => assocBwdInner k B C M N P m x)
    (fun m₁ m₂ x => induction_on (C := fun x => assocBwdInner k B C M N P (m₁ + m₂) x =
        assocBwdInner k B C M N P m₁ x + assocBwdInner k B C M N P m₂ x) x
      (fun n p => by simp) (fun x y hx hy => by simp [hx, hy, add_add_add_comm]))
    (fun c m x => induction_on (C := fun x => assocBwdInner k B C M N P (c • m) x =
        c • assocBwdInner k B C M N P m x) x
      (fun n p => by simp) (fun x y hx hy => by simp [hx, hy]))
    (fun m x y => map_add _ x y)
    (fun c m x => map_smul _ c x)

variable (k B C M N P) in
/-- The inverse map `M ⊗_B (N ⊗_C P) → (M ⊗_B N) ⊗_C P`. -/
def assocBwd :
    BalTensor k B M (BalTensor k C N P) →ₗ[k] BalTensor k C (BalTensor k B M N) P :=
  lift (assocBwdBilin k B C M N P) (by
    intro b m x
    refine induction_on (C := fun x => assocBwdBilin k B C M N P (op b • m) x =
      assocBwdBilin k B C M N P m (b • x)) x (fun n p => ?_)
      (fun x y hx hy => by simp [smul_add, hx, hy])
    rw [smul_tmul_left]
    show tmul k C (tmul k B (op b • m) n) p = tmul k C (tmul k B m (b • n)) p
    rw [tmul_balance])

@[simp]
theorem assocBwd_tmul (m : M) (n : N) (p : P) :
    assocBwd k B C M N P (tmul k B m (tmul k C n p)) = tmul k C (tmul k B m n) p := rfl

variable (k B C M N P) in
/-- **Etingof et al., Exercise after Problem 1.49**: associativity of the tensor product over
noncommutative rings, `(M ⊗_B N) ⊗_C P ≃ M ⊗_B (N ⊗_C P)`, as `k`-modules. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
def assocEquiv :
    BalTensor k C (BalTensor k B M N) P ≃ₗ[k] BalTensor k B M (BalTensor k C N P) :=
  LinearEquiv.ofLinearMap (assocFwd k B C M N P) (assocBwd k B C M N P)
    (hom_ext fun m x => induction_on (C := fun x =>
        assocFwd k B C M N P (assocBwd k B C M N P (tmul k B m x)) = tmul k B m x) x
      (fun n p => by simp) (fun x y hx hy => by simp only [map_add, hx, hy]))
    (hom_ext fun q p => induction_on (C := fun q =>
        assocBwd k B C M N P (assocFwd k B C M N P (tmul k C q p)) = tmul k C q p) q
      (fun m n => by simp) (fun x y hx hy => by simp only [map_add, LinearMap.add_apply, hx, hy]))

@[simp]
theorem assocEquiv_tmul (m : M) (n : N) (p : P) :
    assocEquiv k B C M N P (tmul k C (tmul k B m n) p) = tmul k B m (tmul k C n p) := rfl

/-- Associativity is compatible with the outer left action (an algebra `A` acting on `M`). -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
theorem assocEquiv_smul_left {A : Type*} [Semiring A] [Module A M] [SMulCommClass A Bᵐᵒᵖ M]
    [SMulCommClass A k M] (a : A) (x : BalTensor k C (BalTensor k B M N) P) :
    assocEquiv k B C M N P (a • x) = a • assocEquiv k B C M N P x := by
  refine induction_on (C := fun x => assocEquiv k B C M N P (a • x) =
    a • assocEquiv k B C M N P x) x (fun q p => ?_)
    (fun x y hx hy => by simp only [smul_add, map_add, hx, hy])
  rw [smul_tmul_left]
  refine induction_on (C := fun q => assocEquiv k B C M N P (tmul k C (a • q) p) =
    a • assocEquiv k B C M N P (tmul k C q p)) q (fun m n => ?_)
    (fun x y hx hy => by simp only [smul_add, map_add, LinearMap.add_apply, hx, hy])
  simp

/-- Associativity is compatible with the outer right action (an algebra acting on `P` on the
right, commuting with the `C`-action). -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
theorem assocEquiv_smul_right {D : Type*} [Semiring D] [Module D P] [SMulCommClass C D P]
    [SMulCommClass D k P] (d : D) (x : BalTensor k C (BalTensor k B M N) P) :
    assocEquiv k B C M N P (d • x) = d • assocEquiv k B C M N P x := by
  refine induction_on (C := fun x => assocEquiv k B C M N P (d • x) =
    d • assocEquiv k B C M N P x) x (fun q p => ?_)
    (fun x y hx hy => by simp only [smul_add, map_add, hx, hy])
  rw [smul_tmul_right]
  refine induction_on (C := fun q => assocEquiv k B C M N P (tmul k C q (d • p)) =
    d • assocEquiv k B C M N P (tmul k C q p)) q (fun m n => ?_)
    (fun x y hx hy => by simp only [smul_add, map_add, LinearMap.add_apply, hx, hy])
  simp

end Assoc

end BalTensor

section HomRight

variable (B C N P : Type*) [Ring B] [Ring C] [AddCommGroup N] [AddCommGroup P]
  [Module B N] [Module Cᵐᵒᵖ N] [Module Cᵐᵒᵖ P] [SMulCommClass B Cᵐᵒᵖ N]

/-- The module `Hom_C(N, P)` of `C`-linear maps from a `(B, C)`-bimodule `N` to a right
`C`-module `P` (that is, `Cᵐᵒᵖ`-linear maps), a type synonym carrying its right `B`-module
structure `(f b)(n) = f (b n)`, i.e. a `Bᵐᵒᵖ`-module structure. -/
def HomRight : Type _ := N →ₗ[Cᵐᵒᵖ] P

instance : AddCommGroup (HomRight C N P) := inferInstanceAs (AddCommGroup (N →ₗ[Cᵐᵒᵖ] P))

instance : FunLike (HomRight C N P) N P := inferInstanceAs (FunLike (N →ₗ[Cᵐᵒᵖ] P) N P)

variable {B C N P}

/-- View an element of `HomRight` as a `C`-linear map. -/
def HomRight.toLinearMap (f : HomRight C N P) : N →ₗ[Cᵐᵒᵖ] P := f

/-- Regard a `C`-linear map as an element of `HomRight`. -/
def HomRight.ofLinearMap (f : N →ₗ[Cᵐᵒᵖ] P) : HomRight C N P := f

@[ext]
theorem HomRight.ext {f g : HomRight C N P} (h : ∀ n, f n = g n) : f = g :=
  LinearMap.ext h

@[simp]
theorem HomRight.add_apply (f g : HomRight C N P) (n : N) : (f + g) n = f n + g n := rfl

@[simp]
theorem HomRight.zero_apply (n : N) : (0 : HomRight C N P) n = 0 := rfl

instance : Module Bᵐᵒᵖ (HomRight C N P) where
  smul b f := HomRight.ofLinearMap
    (f.toLinearMap ∘ₗ DistribSMul.toLinearMap Cᵐᵒᵖ N b.unop)
  one_smul f := HomRight.ext fun n => by
    show f ((1 : Bᵐᵒᵖ).unop • n) = f n
    simp
  mul_smul a b f := HomRight.ext fun n => by
    show f ((a * b).unop • n) = f (b.unop • a.unop • n)
    simp [mul_smul]
  smul_zero b := HomRight.ext fun n => rfl
  smul_add b f g := HomRight.ext fun n => rfl
  add_smul a b f := HomRight.ext fun n => by
    show f ((a + b).unop • n) = f (a.unop • n) + f (b.unop • n)
    rw [MulOpposite.unop_add, add_smul]
    exact f.toLinearMap.map_add _ _
  zero_smul f := HomRight.ext fun n => by
    show f ((0 : Bᵐᵒᵖ).unop • n) = 0
    rw [MulOpposite.unop_zero, zero_smul]
    exact f.toLinearMap.map_zero

@[simp]
theorem HomRight.smul_apply (b : Bᵐᵒᵖ) (f : HomRight C N P) (n : N) :
    (b • f) n = f (b.unop • n) := rfl

variable (k : Type*) [CommRing k] [Module k P] [SMulCommClass Cᵐᵒᵖ k P]

instance : Module k (HomRight C N P) := inferInstanceAs (Module k (N →ₗ[Cᵐᵒᵖ] P))

@[simp]
theorem HomRight.smul_apply' (c : k) (f : HomRight C N P) (n : N) : (c • f) n = c • f n := rfl

instance : SMulCommClass Bᵐᵒᵖ k (HomRight C N P) :=
  ⟨fun b c f => HomRight.ext fun n => by simp⟩

end HomRight

section Adjunction

variable {k : Type*} [CommRing k] {B C : Type*} [Ring B] [Ring C] [Algebra k B] [Algebra k C]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]
  [Module Bᵐᵒᵖ M] [Module B N] [Module Cᵐᵒᵖ N] [Module Cᵐᵒᵖ P]
  [SMulCommClass B Cᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ M] [IsScalarTower k B N]
  [IsScalarTower k Cᵐᵒᵖ N] [IsScalarTower k Cᵐᵒᵖ P]

instance : IsScalarTower k Bᵐᵒᵖ (HomRight C N P) :=
  ⟨fun c b f => HomRight.ext fun n => by
    show f ((c • b).unop • n) = c • f (b.unop • n)
    rw [MulOpposite.unop_smul, smul_assoc]
    exact (f.toLinearMap.map_smul_of_tower c (b.unop • n))⟩

namespace BalTensor

/-- The map sending a `C`-linear map `M ⊗_B N → P` to the `B`-linear map
`m ↦ (n ↦ f (m ⊗ n))`. -/
def homTensorTo (f : BalTensor k B M N →ₗ[Cᵐᵒᵖ] P) : M →ₗ[Bᵐᵒᵖ] HomRight C N P where
  toFun m := HomRight.ofLinearMap
    { toFun := fun n => f (tmul k B m n)
      map_add' := fun n₁ n₂ => by simp
      map_smul' := fun c n => by
        simp only [RingHom.id_apply]
        rw [← smul_tmul_right, map_smul] }
  map_add' m₁ m₂ := HomRight.ext fun n => by
    show f (tmul k B (m₁ + m₂) n) = f (tmul k B m₁ n) + f (tmul k B m₂ n)
    simp
  map_smul' b m := HomRight.ext fun n => by
    show f (tmul k B (b • m) n) = f (tmul k B m (b.unop • n))
    rw [tmul_balance']

/-- The `k`-bilinear, `B`-balanced data attached to a `B`-linear map `M → Hom_C(N, P)`. -/
def homTensorBilin (φ : M →ₗ[Bᵐᵒᵖ] HomRight C N P) : M →ₗ[k] N →ₗ[k] P :=
  LinearMap.mk₂ k (fun m n => φ m n)
    (fun m₁ m₂ n => by rw [map_add]; rfl)
    (fun c m n => by rw [LinearMap.map_smul_of_tower]; rfl)
    (fun m n₁ n₂ => map_add (φ m).toLinearMap n₁ n₂)
    (fun c m n => (φ m).toLinearMap.map_smul_of_tower c n)

/-- The `k`-linear map `M ⊗_B N → P` induced by a `B`-linear map `M → Hom_C(N, P)`. -/
def homTensorLift (φ : M →ₗ[Bᵐᵒᵖ] HomRight C N P) : BalTensor k B M N →ₗ[k] P :=
  lift (homTensorBilin φ) (fun b m n => by
    show φ (op b • m) n = φ m (b • n)
    rw [map_smul]
    rfl)

@[simp]
theorem homTensorLift_tmul (φ : M →ₗ[Bᵐᵒᵖ] HomRight C N P) (m : M) (n : N) :
    homTensorLift (k := k) φ (tmul k B m n) = φ m n := rfl

/-- The inverse map: a `B`-linear map `M → Hom_C(N, P)` induces a `C`-linear map
`M ⊗_B N → P`. -/
def homTensorInv (φ : M →ₗ[Bᵐᵒᵖ] HomRight C N P) : BalTensor k B M N →ₗ[Cᵐᵒᵖ] P where
  toFun := homTensorLift (k := k) φ
  map_add' := map_add _
  map_smul' c x := by
    refine induction_on (C := fun x => homTensorLift (k := k) φ (c • x) = c • homTensorLift φ x)
      x (fun m n => ?_) (fun x y hx hy => ?_)
    · rw [smul_tmul_right]
      exact (φ m).toLinearMap.map_smul c n
    · rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable (k B C M N P) in
/-- **Etingof et al., Exercise after Problem 1.49** (Hom-tensor adjunction): for a right `B`-module
`M`, a `(B, C)`-bimodule `N` and a right `C`-module `P`, the `C`-linear maps `M ⊗_B N → P`
correspond `k`-linearly to the `B`-linear maps `M → Hom_C(N, P)`, where `Hom_C(N, P)` is a right
`B`-module via `(f b)(n) = f (b n)`. -/
@[kb "etingof2011" "Exercise after Problem 1.49, p. 18"]
def homTensorEquiv :
    (BalTensor k B M N →ₗ[Cᵐᵒᵖ] P) ≃ₗ[k] (M →ₗ[Bᵐᵒᵖ] HomRight C N P) where
  toFun := homTensorTo
  map_add' f g := LinearMap.ext fun m => HomRight.ext fun n => rfl
  map_smul' c f := LinearMap.ext fun m => HomRight.ext fun n => rfl
  invFun := homTensorInv
  left_inv f := LinearMap.ext fun x =>
    induction_on (C := fun x => homTensorInv (k := k) (homTensorTo f) x = f x) x
      (fun m n => rfl) (fun x y hx hy => by rw [map_add, map_add, hx, hy])
  right_inv φ := LinearMap.ext fun m => HomRight.ext fun n => rfl

end BalTensor

end Adjunction

end UndergradKB.RepresentationTheory

