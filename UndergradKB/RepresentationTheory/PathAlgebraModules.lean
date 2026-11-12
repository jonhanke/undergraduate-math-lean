import UndergradKB.RepresentationTheory.PathAlgebra
import UndergradKB.RepresentationTheory.Quiver
import UndergradKB.Common.Attr

/-! # Quiver representations and path algebra modules (Etingof et al., §1.8)

For a finite quiver `Q` and a field `k`, representations of `Q` correspond to modules over the path
algebra `PathAlgebra k Q`.

Convention.  In `PathAlgebra.lean` the product `p * q` is the path "first `p`, then `q`".  A representation
sends an arrow `i → j` to a map `V_i → V_j`, so the arrow acts on the *right* (it composes like
`m ↦ m · a`).  We therefore work with left modules over the opposite algebra `(PathAlgebra k Q)ᵐᵒᵖ`,
which is the same thing as right modules over `PathAlgebra k Q`.

* `QRep.Total V`: the direct sum (here the finite product) `⨁ V_i`, with its `k`-module structure and
  the action of the path algebra: the trivial path `e_i` acts as the projection onto `V_i`, a path acts by
  the composite of its arrow maps (`Total.smul_pathElem`).
* `QRep.ofModule k Q M`: the representation attached to a module `M`, with `V_i = e_i M` (`corner`) and the
  arrow maps given by the action of the arrows (`arrowMap`).
* `QRep.ofModule_total_isomorphic`: the representation of the module of `V` is isomorphic to `V`.
* `moduleEquivTotal`: a module `M` is isomorphic, as a module over the path algebra, to the module of its
  representation.
-/

set_option linter.unusedSectionVars false

universe u₁ u₂ v w

namespace UndergradKB.RepresentationTheory

open _root_.Quiver

variable {k : Type u₁} [Field k] {Q : Type u₂} [_root_.Quiver.{v + 1} Q] [DecidableEq Q] [Fintype Q]

namespace QRep

/-- The linear map attached to a path: the composite of the arrow maps. -/
def pathMap (V : QRep k Q) : ∀ {i j : Q}, Path i j → (V.obj i →ₗ[k] V.obj j)
  | _, _, .nil => LinearMap.id
  | _, _, .cons p h => (V.map h).comp (pathMap V p)

theorem pathMap_nil (V : QRep k Q) (i : Q) :
    pathMap V (Path.nil : Path i i) = LinearMap.id := by simp [pathMap]

theorem pathMap_comp (V : QRep k Q) {i j l : Q} (p : Path i j) (q : Path j l) :
    pathMap V (p.comp q) = (pathMap V q).comp (pathMap V p) := by
  induction q with
  | nil => simp [pathMap, Path.comp_nil]
  | cons q h ih =>
    rw [Path.comp_cons]
    simp [pathMap, ih, LinearMap.comp_assoc]

theorem pathMap_toPath (V : QRep k Q) {i j : Q} (h : i ⟶ j) :
    pathMap V h.toPath = V.map h := by
  simp [pathMap, Quiver.Hom.toPath]

/-- The direct sum `⨁ V_i` of the spaces of a representation (a finite product, since `Q` is finite). -/
def Total (V : QRep k Q) : Type _ := ∀ i, V.obj i

namespace Total

variable (V : QRep k Q)

instance : AddCommGroup (Total V) := inferInstanceAs (AddCommGroup (∀ i, V.obj i))
instance : Module k (Total V) := inferInstanceAs (Module k (∀ i, V.obj i))

/-- Projection onto the `i`-th summand. -/
def pr (i : Q) : Total V →ₗ[k] V.obj i := LinearMap.proj i

/-- Inclusion of the `i`-th summand. -/
def inc (i : Q) : V.obj i →ₗ[k] Total V := LinearMap.single k (fun i => V.obj i) i

variable {V}

@[simp] theorem pr_inc_self (i : Q) (u : V.obj i) : pr V i (inc V i u) = u := by
  exact Pi.single_eq_same i u

theorem pr_inc_ne {i j : Q} (h : j ≠ i) (u : V.obj i) : pr V j (inc V i u) = 0 := by
  exact Pi.single_eq_of_ne h u

theorem sum_inc_pr (v : Total V) : ∑ i, inc V i (pr V i v) = v := by
  exact LinearMap.sum_single_apply (φ := fun i => V.obj i) v

variable (V)

/-- The operator by which a path `p : i → j` acts: project to `V_i`, apply the composite of the arrow
maps, and include into `V_j`. -/
def pathAct (p : AnyPath Q) : Total V →ₗ[k] Total V :=
  (inc V p.2.1).comp ((pathMap V p.2.2).comp (pr V p.1))

variable {V}

theorem pathAct_mk {i j : Q} (P : Path i j) (v : Total V) :
    pathAct V ⟨i, j, P⟩ v = inc V j (pathMap V P (pr V i v)) := rfl

theorem pathAct_comp (p q : AnyPath Q) :
    (pathAct V q).comp (pathAct V p) = (concatPath p q).elim 0 (pathAct V) := by
  obtain ⟨i, j, P⟩ := p
  obtain ⟨j', l, R⟩ := q
  by_cases h : j = j'
  · subst h
    rw [concatPath_eq_some]
    refine LinearMap.ext fun v => ?_
    simp [pathAct_mk, pathMap_comp]
  · rw [concatPath_eq_none _ _ h]
    refine LinearMap.ext fun v => ?_
    simp [pathAct_mk, pr_inc_ne (Ne.symm h)]

variable (V)

/-- The linear extension of the path operators to the whole path algebra. -/
noncomputable def rho : PathAlgebra k Q →ₗ[k] Module.End k (Total V) :=
  pathAlgebraBasis.constr k (pathAct V)

theorem pathAlgebraBasis_apply (p : AnyPath Q) :
    (pathAlgebraBasis : Module.Basis (AnyPath Q) k (PathAlgebra k Q)) p = pathElem p := by
  simp [pathAlgebraBasis]

theorem rho_pathElem (p : AnyPath Q) : rho V (pathElem p) = pathAct V p := by
  rw [← pathAlgebraBasis_apply (k := k), rho, Module.Basis.constr_basis]

variable {V}

theorem rho_pathElem_mul (p q : AnyPath Q) :
    rho V (pathElem p * pathElem q) = rho V (pathElem q) * rho V (pathElem p) := by
  rw [pathElem_mul, rho_pathElem, rho_pathElem]
  have := pathAct_comp (V := V) p q
  show _ = (pathAct V q).comp (pathAct V p)
  rw [this]
  cases concatPath p q <;> simp [rho_pathElem]

theorem rho_mul (a b : PathAlgebra k Q) : rho V (a * b) = rho V b * rho V a := by
  have h1 : ∀ (p : AnyPath Q) (b : PathAlgebra k Q),
      rho V (pathElem p * b) = rho V b * rho V (pathElem p) := by
    intro p b
    have e : (rho V).comp (LinearMap.mulLeft k (pathElem p)) =
        (LinearMap.mulRight k (rho V (pathElem p))).comp (rho V) :=
      pathAlgebraBasis.ext fun q => by
        rw [pathAlgebraBasis_apply]
        exact rho_pathElem_mul p q
    exact LinearMap.congr_fun e b
  have e : (rho V).comp (LinearMap.mulRight k b) =
      (LinearMap.mulLeft k (rho V b)).comp (rho V) :=
    pathAlgebraBasis.ext fun p => by
      rw [pathAlgebraBasis_apply]
      exact h1 p b
  exact LinearMap.congr_fun e a

theorem rho_one : rho V (1 : PathAlgebra k Q) = 1 := by
  rw [pathElem_one, map_sum]
  refine LinearMap.ext fun v => ?_
  simp only [rho_pathElem, LinearMap.sum_apply, one_apply_eq_self]
  have : ∀ i, pathAct V (trivialPath i) v = inc V i (pr V i v) := fun i => by
    simp [pathAct_mk, trivialPath, pathMap_nil]
  simp only [this, sum_inc_pr]

variable (V)

/-- The action of the opposite of the path algebra on `⨁ V_i`, as a ring homomorphism. -/
noncomputable def actHom : (PathAlgebra k Q)ᵐᵒᵖ →+* Module.End k (Total V) where
  toFun a := rho V a.unop
  map_one' := rho_one
  map_mul' a b := by simp [rho_mul]
  map_zero' := by simp
  map_add' a b := by simp

/-- The module structure on `⨁ V_i` over the path algebra (acting on the right, i.e. through the opposite
algebra): paths act by composing the arrow maps and the trivial path `e_i` acts as the projection onto
`V_i`. -/
@[kb "etingof2011" "§1.8, p. 14"]
noncomputable instance instModuleOp : Module (PathAlgebra k Q)ᵐᵒᵖ (Total V) :=
  Module.compHom (Total V) (actHom V)

variable {V}

theorem smul_def (a : (PathAlgebra k Q)ᵐᵒᵖ) (v : Total V) : a • v = rho V a.unop v := rfl

/-- A path acts by the composite of its arrow maps (from the source summand to the target summand). -/
@[kb "etingof2011" "§1.8, p. 14"]
theorem smul_pathElem (p : AnyPath Q) (v : Total V) :
    MulOpposite.op (pathElem p : PathAlgebra k Q) • v = pathAct V p v := by
  rw [smul_def, MulOpposite.unop_op, rho_pathElem]

instance : IsScalarTower k (PathAlgebra k Q)ᵐᵒᵖ (Total V) where
  smul_assoc c a v := by
    rw [smul_def, smul_def, MulOpposite.unop_smul, map_smul, LinearMap.smul_apply]

end Total

end QRep

/-! ### From a module to a representation -/

section ModuleSide

/-- The trivial path `e_i` as an element of the path algebra. -/
noncomputable def idem (k : Type u₁) [Field k] (i : Q) : PathAlgebra k Q := pathElem (trivialPath i)

/-- The arrow `h : i → j` as an element of the path algebra. -/
noncomputable def arrowElem (k : Type u₁) [Field k] {i j : Q} (h : i ⟶ j) : PathAlgebra k Q :=
  pathElem ⟨i, j, h.toPath⟩

variable (k)

theorem idem_mul_idem (i : Q) : idem k i * idem k i = (idem k i : PathAlgebra k Q) := by
  unfold idem trivialPath
  rw [pathElem_mul, concatPath_eq_some]
  simp [Path.comp_nil]

theorem idem_mul_idem_ne {i j : Q} (h : i ≠ j) : idem k i * idem k j = (0 : PathAlgebra k Q) := by
  unfold idem trivialPath
  rw [pathElem_mul, concatPath_eq_none _ _ h]
  rfl

theorem idem_mul_pathElem {s t : Q} (P : Path s t) :
    idem k s * pathElem ⟨s, t, P⟩ = (pathElem ⟨s, t, P⟩ : PathAlgebra k Q) := by
  unfold idem trivialPath
  rw [pathElem_mul, concatPath_eq_some]
  simp [Path.nil_comp]

theorem pathElem_mul_idem {s t : Q} (P : Path s t) :
    pathElem ⟨s, t, P⟩ * idem k t = (pathElem ⟨s, t, P⟩ : PathAlgebra k Q) := by
  unfold idem trivialPath
  rw [pathElem_mul, concatPath_eq_some]
  simp [Path.comp_nil]

theorem pathElem_mul_idem_ne {s t t' : Q} (P : Path s t) (h : t ≠ t') :
    pathElem ⟨s, t, P⟩ * idem k t' = (0 : PathAlgebra k Q) := by
  unfold idem trivialPath
  rw [pathElem_mul, concatPath_eq_none _ _ h]
  rfl

theorem pathElem_cons {s t t' : Q} (P : Path s t) (h : t ⟶ t') :
    pathElem ⟨s, t', P.cons h⟩ = (pathElem ⟨s, t, P⟩ * arrowElem k h : PathAlgebra k Q) := by
  unfold arrowElem
  rw [pathElem_mul, concatPath_eq_some]
  simp [Quiver.Hom.toPath, Path.comp_cons, Path.comp_nil]

theorem sum_idem : ∑ i : Q, idem k i = (1 : PathAlgebra k Q) := (pathElem_one).symm

variable {k}

variable {M : Type w} [AddCommGroup M] [Module k M] [Module (PathAlgebra k Q)ᵐᵒᵖ M]
  [IsScalarTower k (PathAlgebra k Q)ᵐᵒᵖ M]

/-- The action of an element of the path algebra on a module `M` (through the opposite algebra), as a
`k`-linear map. -/
noncomputable def modAct (M : Type w) [AddCommGroup M] [Module k M] [Module (PathAlgebra k Q)ᵐᵒᵖ M]
    [IsScalarTower k (PathAlgebra k Q)ᵐᵒᵖ M] (a : PathAlgebra k Q) : M →ₗ[k] M where
  toFun m := MulOpposite.op a • m
  map_add' := smul_add _
  map_smul' c m := by
    have : SMulCommClass k (PathAlgebra k Q)ᵐᵒᵖ M := IsScalarTower.to_smulCommClass
    exact (smul_comm c (MulOpposite.op a) m).symm

theorem modAct_apply (a : PathAlgebra k Q) (m : M) : modAct M a m = MulOpposite.op a • m := rfl

theorem modAct_modAct (a b : PathAlgebra k Q) (m : M) :
    modAct M a (modAct M b m) = modAct M (b * a) m := by
  simp only [modAct_apply, ← mul_smul, MulOpposite.op_mul]

theorem modAct_zero (m : M) : modAct M (0 : PathAlgebra k Q) m = 0 := by
  simp [modAct_apply]

theorem sum_modAct_idem (m : M) : ∑ i : Q, modAct M (idem k i) m = m := by
  have h : (1 : (PathAlgebra k Q)ᵐᵒᵖ) = ∑ i : Q, MulOpposite.op (idem k i) := by
    rw [← MulOpposite.op_one, ← sum_idem k, Finset.op_sum]
  calc ∑ i : Q, modAct M (idem k i) m = (∑ i : Q, MulOpposite.op (idem k i)) • m := by
        rw [Finset.sum_smul]; rfl
    _ = m := by rw [← h, one_smul]

variable (k M)

/-- The space `e_i M`, the image of the idempotent `e_i`. -/
noncomputable abbrev corner (i : Q) : Submodule k M := LinearMap.range (modAct M (idem k i))

variable {k M}

theorem mem_corner_iff {i : Q} {m : M} : m ∈ corner k M i ↔ modAct M (idem k i) m = m := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [modAct_modAct, idem_mul_idem]
  · intro h
    exact ⟨m, h⟩

theorem modAct_mem_corner {j : Q} {a : PathAlgebra k Q} (ha : a * idem k j = a) (m : M) :
    modAct M a m ∈ corner k M j := by
  refine mem_corner_iff.2 ?_
  rw [modAct_modAct, ha]

variable (k Q M)

/-- The map `e_i M → e_j M` given by the action of an arrow `h : i → j`. -/
noncomputable def arrowMap {i j : Q} (h : i ⟶ j) : corner k M i →ₗ[k] corner k M j :=
  LinearMap.codRestrict (corner k M j) ((modAct M (arrowElem k h)).comp (corner k M i).subtype)
    (fun x => modAct_mem_corner (pathElem_mul_idem k h.toPath) x.1)

/-- The representation attached to a module `M` over (the opposite of) the path algebra: the space at the
vertex `i` is `e_i M` and an arrow acts by the action of the corresponding element of the path algebra. -/
@[kb "etingof2011" "§1.8, p. 14"]
noncomputable def QRep.ofModule : QRep k Q where
  obj i := corner k M i
  map h := arrowMap k Q M h

variable {k Q M}

/-- The underlying element of `M` of an element of the space `e_i M` of the representation. -/
abbrev objVal {i : Q} (x : (QRep.ofModule k Q M).obj i) : M := Subtype.val x

end ModuleSide

/-! ### The representation of the module of a representation is the representation -/

section FromRep

variable (k) (V : QRep k Q)

theorem modAct_total (a : PathAlgebra k Q) (v : QRep.Total V) :
    modAct (QRep.Total V) a v = QRep.Total.rho V a v := rfl

theorem modAct_idem_total (i : Q) (v : QRep.Total V) :
    modAct (QRep.Total V) (idem k i) v = QRep.Total.inc V i (QRep.Total.pr V i v) := by
  rw [modAct_total, idem, QRep.Total.rho_pathElem]
  simp [QRep.Total.pathAct_mk, trivialPath, QRep.pathMap_nil]

theorem modAct_arrow_total {i j : Q} (h : i ⟶ j) (v : QRep.Total V) :
    modAct (QRep.Total V) (arrowElem k h) v =
      QRep.Total.inc V j (V.map h (QRep.Total.pr V i v)) := by
  rw [modAct_total, arrowElem, QRep.Total.rho_pathElem, QRep.Total.pathAct_mk, QRep.pathMap_toPath]

/-- The component maps `e_i (⨁ V) → V_i`, the projections. -/
noncomputable def ofModuleTotalHom : QRep.Hom (QRep.ofModule k Q (QRep.Total V)) V where
  app i := (QRep.Total.pr V i).comp (corner k (QRep.Total V) i).subtype
  comm {i j} h := LinearMap.ext fun x => by
    show QRep.Total.pr V j (modAct (QRep.Total V) (arrowElem k h) x.1) =
      V.map h (QRep.Total.pr V i x.1)
    rw [modAct_arrow_total, QRep.Total.pr_inc_self]

/-- The component maps `V_i → e_i (⨁ V)`, the inclusions. -/
noncomputable def totalOfModuleHom : QRep.Hom V (QRep.ofModule k Q (QRep.Total V)) where
  app i := LinearMap.codRestrict (corner k (QRep.Total V) i) (QRep.Total.inc V i)
    (fun u => mem_corner_iff.2 (by rw [modAct_idem_total, QRep.Total.pr_inc_self]))
  comm {i j} h := LinearMap.ext fun u => Subtype.ext (by
    show QRep.Total.inc V j (V.map h u) = modAct (QRep.Total V) (arrowElem k h) (QRep.Total.inc V i u)
    rw [modAct_arrow_total, QRep.Total.pr_inc_self])

/-- **Path algebra modules, first round trip.** Starting from a representation `V`, forming the module
`⨁ V_i` over the path algebra and then taking the representation `e_i M`, we recover `V` up to
isomorphism (the isomorphism is the projection onto `V_i` at each vertex). -/
@[kb "etingof2011" "§1.8, p. 14"]
theorem QRep.ofModule_total_isomorphic : QRep.Isomorphic (QRep.ofModule k Q (QRep.Total V)) V :=
  ⟨ofModuleTotalHom k V, totalOfModuleHom k V,
    QRep.Hom.ext fun i => LinearMap.ext fun u => QRep.Total.pr_inc_self i u,
    QRep.Hom.ext fun i => LinearMap.ext fun x => Subtype.ext (by
      have := mem_corner_iff.1 x.2
      rw [modAct_idem_total] at this
      exact this)⟩

end FromRep

/-! ### A module is the module of its representation -/

section FromModule

variable (k Q) (M : Type w) [AddCommGroup M] [Module k M] [Module (PathAlgebra k Q)ᵐᵒᵖ M]
  [IsScalarTower k (PathAlgebra k Q)ᵐᵒᵖ M]

/-- The decomposition map `M → ⨁ e_i M`, `m ↦ (e_i m)`. -/
noncomputable def toTotal : M →ₗ[k] QRep.Total (QRep.ofModule k Q M) :=
  LinearMap.pi fun i => LinearMap.rangeRestrict (modAct M (idem k i))

variable {k Q M}

theorem toTotal_apply_val (m : M) (i : Q) :
    objVal (toTotal k Q M m i : (QRep.ofModule k Q M).obj i) = modAct M (idem k i) m := rfl

theorem pathMap_ofModule {s t : Q} (P : Path s t) (x : (QRep.ofModule k Q M).obj s) :
    objVal (QRep.pathMap (QRep.ofModule k Q M) P x) =
      modAct M (pathElem (k := k) ⟨s, t, P⟩) (objVal x) := by
  induction P with
  | nil =>
    have e : QRep.pathMap (QRep.ofModule k Q M) (Path.nil : Path s s) x = x := by
      simp [QRep.pathMap]
    exact (congrArg objVal e).trans (mem_corner_iff.1 x.2).symm
  | @cons b c P h ih =>
    have e : QRep.pathMap (QRep.ofModule k Q M) (P.cons h) x =
        (QRep.ofModule k Q M).map h (QRep.pathMap (QRep.ofModule k Q M) P x) := by
      simp [QRep.pathMap]
    refine (congrArg objVal e).trans ?_
    show modAct M (arrowElem k h) (objVal (QRep.pathMap (QRep.ofModule k Q M) P x)) = _
    rw [ih, modAct_modAct, ← pathElem_cons k P h]

theorem toTotal_modAct_pathElem (p : AnyPath Q) (m : M) :
    toTotal k Q M (modAct M (pathElem (k := k) p) m) =
      QRep.Total.pathAct (QRep.ofModule k Q M) p (toTotal k Q M m) := by
  obtain ⟨s, t, P⟩ := p
  funext i
  rcases eq_or_ne i t with rfl | hi
  · have h2 : QRep.Total.pathAct (QRep.ofModule k Q M) ⟨s, i, P⟩ (toTotal k Q M m) i =
        QRep.pathMap (QRep.ofModule k Q M) P (toTotal k Q M m s) := Pi.single_eq_same i _
    refine Subtype.ext ?_
    refine ((toTotal_apply_val _ i).trans ?_).trans (congrArg objVal h2).symm
    refine Eq.trans ?_ (pathMap_ofModule P _).symm
    refine Eq.trans ?_ (congrArg (modAct M (pathElem (k := k) ⟨s, i, P⟩)) (toTotal_apply_val m s)).symm
    rw [modAct_modAct, modAct_modAct, pathElem_mul_idem, idem_mul_pathElem]
  · have h2 : QRep.Total.pathAct (QRep.ofModule k Q M) ⟨s, t, P⟩ (toTotal k Q M m) i = 0 :=
      Pi.single_eq_of_ne hi _
    refine Subtype.ext ?_
    refine ((toTotal_apply_val _ i).trans ?_).trans (congrArg objVal h2).symm
    rw [modAct_modAct, pathElem_mul_idem_ne k P (Ne.symm hi), modAct_zero]
    rfl

/-- The linear map `a ↦ a m`. -/
noncomputable def modActLin (m : M) : PathAlgebra k Q →ₗ[k] M where
  toFun a := modAct M a m
  map_add' a b := by simp [modAct_apply, add_smul]
  map_smul' c a := by
    show MulOpposite.op (c • a) • m = c • (MulOpposite.op a • m)
    rw [MulOpposite.op_smul, smul_assoc]

theorem toTotal_smul (a : PathAlgebra k Q) (m : M) :
    toTotal k Q M (modAct M a m) = QRep.Total.rho (QRep.ofModule k Q M) a (toTotal k Q M m) := by
  let f₁ : PathAlgebra k Q →ₗ[k] QRep.Total (QRep.ofModule k Q M) := (toTotal k Q M).comp (modActLin m)
  let f₂ : PathAlgebra k Q →ₗ[k] QRep.Total (QRep.ofModule k Q M) :=
    { toFun := fun a => QRep.Total.rho (QRep.ofModule k Q M) a (toTotal k Q M m)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have e : f₁ = f₂ := pathAlgebraBasis.ext fun p => by
    show toTotal k Q M (modAct M ((pathAlgebraBasis : Module.Basis (AnyPath Q) k (PathAlgebra k Q)) p) m)
      = QRep.Total.rho (QRep.ofModule k Q M)
        ((pathAlgebraBasis : Module.Basis (AnyPath Q) k (PathAlgebra k Q)) p) (toTotal k Q M m)
    rw [QRep.Total.pathAlgebraBasis_apply, QRep.Total.rho_pathElem, toTotal_modAct_pathElem]
  exact LinearMap.congr_fun e a

theorem toTotal_injective : Function.Injective (toTotal k Q M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  have h : ∀ i, modAct M (idem k i) m = 0 := fun i => by
    have := congrArg (fun w : QRep.Total (QRep.ofModule k Q M) => objVal (w i)) hm
    exact this
  rw [← sum_modAct_idem (k := k) (Q := Q) m]
  exact Finset.sum_eq_zero fun i _ => h i

theorem toTotal_surjective : Function.Surjective (toTotal k Q M) := by
  intro w
  refine ⟨∑ j, objVal (w j), ?_⟩
  funext i
  have key : modAct M (idem k i) (∑ j, objVal (w j)) = objVal (w i) := by
    rw [map_sum, Finset.sum_eq_single i]
    · exact mem_corner_iff.1 (w i).2
    · intro j _ hj
      have hw : modAct M (idem k j) (objVal (w j)) = objVal (w j) := mem_corner_iff.1 (w j).2
      generalize objVal (w j) = y at hw ⊢
      calc modAct M (idem k i) y = modAct M (idem k i) (modAct M (idem k j) y) := by rw [hw]
        _ = 0 := by rw [modAct_modAct, idem_mul_idem_ne k hj, modAct_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  exact Subtype.ext key

/-- **Path algebra modules, second round trip.** A module `M` over the path algebra (acting through the
opposite algebra) is isomorphic, as a module, to the direct sum of the spaces `e_i M` of its representation
with the action of `QRep.Total` (so `M` is recovered from its representation). -/
@[kb "etingof2011" "§1.8, p. 14"]
noncomputable def moduleEquivTotal :
    M ≃ₗ[(PathAlgebra k Q)ᵐᵒᵖ] QRep.Total (QRep.ofModule k Q M) :=
  LinearEquiv.ofBijective
    { toFun := toTotal k Q M
      map_add' := map_add _
      map_smul' := fun r m => by
        have hr : r = MulOpposite.op r.unop := rfl
        rw [RingHom.id_apply, QRep.Total.smul_def]
        have := toTotal_smul (k := k) r.unop m
        rw [hr]
        exact this }
    ⟨toTotal_injective, toTotal_surjective⟩

theorem moduleEquivTotal_apply (m : M) : moduleEquivTotal m = toTotal k Q M m := rfl

end FromModule

end UndergradKB.RepresentationTheory
