import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.Artinian.Module
import UndergradKB.Common.Attr

/-! # Problem 5.39: representations of the cyclic quiver with two vertices

A representation is a pair of linear maps `A : V → W`, `B : W → V`.  We define decompositions,
indecomposability and isomorphism, the families `E_{n,λ}`, `E_{n,∞}`, `H_n`, `K_n`, and prove that
they are indecomposable and pairwise non-isomorphic.
-/

namespace UndergradKB.RepresentationTheory

open Module

section Basic

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- `(V₁, W₁) ⊕ (V₂, W₂)` is a decomposition of the representation `(A, B)` into two
subrepresentations. -/
def CQDecomp (A : V →ₗ[k] W) (B : W →ₗ[k] V) (V₁ V₂ : Submodule k V) (W₁ W₂ : Submodule k W) :
    Prop :=
  IsCompl V₁ V₂ ∧ IsCompl W₁ W₂ ∧ (∀ v ∈ V₁, A v ∈ W₁) ∧ (∀ v ∈ V₂, A v ∈ W₂) ∧
    (∀ w ∈ W₁, B w ∈ V₁) ∧ (∀ w ∈ W₂, B w ∈ V₂)

/-- The representation `(A, B)` is indecomposable: nonzero and not a direct sum of two nonzero
subrepresentations. -/
def CQIndec (A : V →ₗ[k] W) (B : W →ₗ[k] V) : Prop :=
  (Nontrivial V ∨ Nontrivial W) ∧
    ∀ (V₁ V₂ : Submodule k V) (W₁ W₂ : Submodule k W), CQDecomp A B V₁ V₂ W₁ W₂ →
      (V₁ = ⊥ ∧ W₁ = ⊥) ∨ (V₂ = ⊥ ∧ W₂ = ⊥)

theorem CQIndec.swap {A : V →ₗ[k] W} {B : W →ₗ[k] V} (h : CQIndec A B) : CQIndec B A := by
  refine ⟨h.1.symm, fun W₁ W₂ V₁ V₂ hd => ?_⟩
  obtain ⟨c1, c2, i1, i2, j1, j2⟩ := hd
  rcases h.2 V₁ V₂ W₁ W₂ ⟨c2, c1, j1, j2, i1, i2⟩ with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨b, a⟩
  · exact Or.inr ⟨b, a⟩

/-- Criterion: if `B` is injective, `B ∘ A` is nilpotent and `ker A` lies in a line, then `(A, B)` is
indecomposable (given it is nonzero). -/
theorem cq_indec_of_ker (A : V →ₗ[k] W) (B : W →ₗ[k] V) (hne : Nontrivial V ∨ Nontrivial W)
    (hnil : ∃ N : ℕ, (B ∘ₗ A) ^ N = (0 : Module.End k V))
    (hB : ∀ w, B w = 0 → w = 0) (e : V) (hA : ∀ x, A x = 0 → ∃ c : k, x = c • e) :
    CQIndec A B := by
  obtain ⟨N, hN⟩ := hnil
  refine ⟨hne, fun V₁ V₂ W₁ W₂ hd => ?_⟩
  obtain ⟨c1, c2, hA1, hA2, hB1, hB2⟩ := hd
  -- a nonzero invariant pair contains a nonzero kernel element of `A`
  have key : ∀ (V' : Submodule k V) (W' : Submodule k W), (∀ v ∈ V', A v ∈ W') →
      (∀ w ∈ W', B w ∈ V') → (V' ≠ ⊥ ∨ W' ≠ ⊥) → ∃ x ∈ V', x ≠ 0 ∧ A x = 0 := by
    intro V' W' hA' hB' hne'
    have hV' : V' ≠ ⊥ := by
      rcases hne' with h | h
      · exact h
      · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff W').1 h
        refine (Submodule.ne_bot_iff V').2 ⟨B y, hB' y hy, fun h0 => hy0 (hB y h0)⟩
    by_contra hcon
    push Not at hcon
    apply hV'
    rw [Submodule.eq_bot_iff]
    have hinv : ∀ j : ℕ, ∀ x ∈ V', ((B ∘ₗ A) ^ j) x ∈ V' := by
      intro j
      induction j with
      | zero => intro x hx; simpa using hx
      | succ j ih =>
        intro x hx
        rw [pow_succ', Module.End.mul_apply]
        exact hB' _ (hA' _ (ih x hx))
    have hz : ∀ j : ℕ, ∀ x ∈ V', ((B ∘ₗ A) ^ j) x = 0 → x = 0 := by
      intro j
      induction j with
      | zero => intro x _ h; simpa using h
      | succ j ih =>
        intro x hx h
        rw [pow_succ', Module.End.mul_apply] at h
        have hzz := hinv j x hx
        have h1 : A (((B ∘ₗ A) ^ j) x) = 0 := hB _ h
        by_cases h2 : ((B ∘ₗ A) ^ j) x = 0
        · exact ih x hx h2
        · exact absurd h1 (hcon _ hzz h2)
    intro x hx
    exact hz N x hx (by rw [hN]; rfl)
  by_cases h1 : V₁ = ⊥ ∧ W₁ = ⊥
  · exact Or.inl h1
  by_cases h2 : V₂ = ⊥ ∧ W₂ = ⊥
  · exact Or.inr h2
  exfalso
  have p1 : V₁ ≠ ⊥ ∨ W₁ ≠ ⊥ := by
    by_contra h; push Not at h; exact h1 h
  have p2 : V₂ ≠ ⊥ ∨ W₂ ≠ ⊥ := by
    by_contra h; push Not at h; exact h2 h
  obtain ⟨x1, hx1, hx10, hAx1⟩ := key V₁ W₁ hA1 hB1 p1
  obtain ⟨x2, hx2, hx20, hAx2⟩ := key V₂ W₂ hA2 hB2 p2
  obtain ⟨a1, ha1⟩ := hA x1 hAx1
  obtain ⟨a2, ha2⟩ := hA x2 hAx2
  have ha10 : a1 ≠ 0 := by rintro rfl; apply hx10; rw [ha1, zero_smul]
  have ha20 : a2 ≠ 0 := by rintro rfl; apply hx20; rw [ha2, zero_smul]
  have he1 : e ∈ V₁ := by
    have := V₁.smul_mem a1⁻¹ hx1
    rwa [ha1, smul_smul, inv_mul_cancel₀ ha10, one_smul] at this
  have he2 : e ∈ V₂ := by
    have := V₂.smul_mem a2⁻¹ hx2
    rwa [ha2, smul_smul, inv_mul_cancel₀ ha20, one_smul] at this
  have he0 : e = 0 := Submodule.disjoint_def.1 c1.disjoint e he1 he2
  apply hx10
  rw [ha1, he0, smul_zero]

/-- Shifting by a scalar does not change decomposability when `B = id`. -/
theorem cq_indec_shift (N : V →ₗ[k] V) (c : k) (h : CQIndec N LinearMap.id) :
    CQIndec (c • LinearMap.id + N) LinearMap.id := by
  refine ⟨h.1, fun V₁ V₂ W₁ W₂ hd => h.2 V₁ V₂ W₁ W₂ ?_⟩
  obtain ⟨c1, c2, hA1, hA2, hB1, hB2⟩ := hd
  have hle : ∀ (X₁ X₂ Y₁ Y₂ : Submodule k V), IsCompl X₁ X₂ → IsCompl Y₁ Y₂ →
      (∀ w ∈ Y₁, w ∈ X₁) → (∀ w ∈ Y₂, w ∈ X₂) → ∀ x ∈ X₁, x ∈ Y₁ := by
    intro X₁ X₂ Y₁ Y₂ cx cy h1 h2 x hx
    have hx' : x ∈ Y₁ ⊔ Y₂ := by rw [cy.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
    have hbx : b ∈ X₁ := by
      have : b = x - a := by rw [← hab]; abel
      rw [this]; exact X₁.sub_mem hx (h1 a ha)
    have : b = 0 := Submodule.disjoint_def.1 cx.disjoint b hbx (h2 b hb)
    rw [this, add_zero] at hab
    rw [← hab]; exact ha
  have hB1' : ∀ w ∈ W₁, w ∈ V₁ := fun w hw => by simpa using hB1 w hw
  have hB2' : ∀ w ∈ W₂, w ∈ V₂ := fun w hw => by simpa using hB2 w hw
  have e1 := hle V₁ V₂ W₁ W₂ c1 c2 hB1' hB2'
  have e2 := hle V₂ V₁ W₂ W₁ c1.symm c2.symm hB2' hB1'
  refine ⟨c1, c2, fun v hv => ?_, fun v hv => ?_, hB1, hB2⟩
  · have h1 := hA1 v hv
    have h2 : c • v ∈ W₁ := W₁.smul_mem c (e1 v hv)
    have : N v = ((c • LinearMap.id + N : V →ₗ[k] V) v) - c • v := by simp
    rw [this]; exact W₁.sub_mem h1 h2
  · have h1 := hA2 v hv
    have h2 : c • v ∈ W₂ := W₂.smul_mem c (e2 v hv)
    have : N v = ((c • LinearMap.id + N : V →ₗ[k] V) v) - c • v := by simp
    rw [this]; exact W₂.sub_mem h1 h2

end Basic

section Shifts

variable {k : Type*} [Field k]

/-- `(N f) j = f (j + 1)` (and `0` at the last index). -/
def shiftDown (n : ℕ) : (Fin n → k) →ₗ[k] (Fin n → k) where
  toFun f j := if h : j.val + 1 < n then f ⟨j.val + 1, h⟩ else 0
  map_add' f g := by funext j; by_cases h : j.val + 1 < n <;> simp [h]
  map_smul' c f := by funext j; by_cases h : j.val + 1 < n <;> simp [h]

/-- `(S f) j = f (j - 1)` (and `0` at index `0`). -/
def shiftUp (n : ℕ) : (Fin n → k) →ₗ[k] (Fin n → k) where
  toFun f j := if h : 0 < j.val then f ⟨j.val - 1, by omega⟩ else 0
  map_add' f g := by funext j; by_cases h : 0 < j.val <;> simp [h]
  map_smul' c f := by funext j; by_cases h : 0 < j.val <;> simp [h]

theorem shiftDown_pow_apply (n t : ℕ) (f : Fin n → k) (j : Fin n) :
    ((shiftDown n : Module.End k (Fin n → k)) ^ t) f j =
      if h : j.val + t < n then f ⟨j.val + t, h⟩ else 0 := by
  induction t generalizing f j with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply]
    show (if h : j.val + 1 < n then (((shiftDown n : Module.End k (Fin n → k)) ^ t) f) ⟨j.val + 1, h⟩
      else 0) = _
    by_cases h : j.val + 1 < n
    · rw [dif_pos h, ih]
      simp only [Fin.val_mk]
      by_cases h2 : j.val + 1 + t < n
      · rw [dif_pos h2, dif_pos (by omega)]
        congr 2; omega
      · rw [dif_neg h2, dif_neg (by omega)]
    · rw [dif_neg h, dif_neg (by omega)]

theorem shiftDown_nilpotent (n : ℕ) : (shiftDown n : Module.End k (Fin n → k)) ^ n = 0 := by
  refine LinearMap.ext fun f => funext fun j => ?_
  rw [shiftDown_pow_apply, dif_neg (by omega)]; rfl

theorem shiftUp_pow_apply (n t : ℕ) (f : Fin n → k) (j : Fin n) :
    ((shiftUp n : Module.End k (Fin n → k)) ^ t) f j =
      if h : t ≤ j.val then f ⟨j.val - t, by omega⟩ else 0 := by
  induction t generalizing f j with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply]
    show (if h : 0 < j.val then (((shiftUp n : Module.End k (Fin n → k)) ^ t) f) ⟨j.val - 1, by omega⟩
      else 0) = _
    by_cases h : 0 < j.val
    · rw [dif_pos h, ih]
      simp only [Fin.val_mk]
      by_cases h2 : t ≤ j.val - 1
      · rw [dif_pos h2, dif_pos (by omega)]
        congr 2; omega
      · rw [dif_neg h2, dif_neg (by omega)]
    · rw [dif_neg h, dif_neg (by omega)]

theorem shiftUp_nilpotent (n : ℕ) : (shiftUp n : Module.End k (Fin n → k)) ^ n = 0 := by
  refine LinearMap.ext fun f => funext fun j => ?_
  rw [shiftUp_pow_apply, dif_neg (by omega)]; rfl

theorem shiftDown_ker {m : ℕ} (f : Fin (m + 1) → k) (h : shiftDown (m + 1) f = 0) :
    f = f 0 • (Pi.single (0 : Fin (m + 1)) (1 : k)) := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hi (Fin.ext h0))
    have := congrFun h ⟨i.val - 1, by omega⟩
    simp only [shiftDown, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [dif_pos (by simp; omega)] at this
    have e : (⟨i.val - 1 + 1, by omega⟩ : Fin (m + 1)) = i := Fin.ext (by simp; omega)
    rw [e] at this
    simp [this, Pi.single_apply, hi]

/-- `truncA m` drops the last coordinate. -/
def truncA (m : ℕ) : (Fin (m + 1) → k) →ₗ[k] (Fin m → k) :=
  LinearMap.funLeft k k (Fin.castSucc : Fin m → Fin (m + 1))

/-- `shiftB m` shifts coordinates up by one (new first coordinate `0`). -/
def shiftB (m : ℕ) : (Fin m → k) →ₗ[k] (Fin (m + 1) → k) where
  toFun g j := if h : 0 < j.val then g ⟨j.val - 1, by omega⟩ else 0
  map_add' f g := by
    funext j
    by_cases h : 0 < j.val
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' c f := by
    funext j
    by_cases h : 0 < j.val
    · simp only [Pi.smul_apply, dif_pos h, RingHom.id_apply]
    · simp only [Pi.smul_apply, dif_neg h, RingHom.id_apply, smul_zero]

theorem truncA_ker {m : ℕ} (f : Fin (m + 1) → k) (h : truncA m f = 0) :
    f = f (Fin.last m) • (Pi.single (Fin.last m) (1 : k)) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · have := congrFun h i
    simp only [truncA, LinearMap.funLeft_apply, Pi.zero_apply] at this
    simp [this, Pi.single_apply, Fin.castSucc_ne_last]

theorem shiftB_inj {m : ℕ} (g : Fin m → k) (h : shiftB m g = 0) : g = 0 := by
  funext j
  have := congrFun h j.succ
  simpa [shiftB] using this

theorem shiftB_comp_truncA (m : ℕ) :
    (shiftB m ∘ₗ truncA m : Module.End k (Fin (m + 1) → k)) = shiftUp (m + 1) := by
  refine LinearMap.ext fun f => funext fun j => ?_
  by_cases h : 0 < j.val <;> simp [shiftB, truncA, shiftUp, h]

end Shifts

section Families

universe u

/-- A (finite-dimensional) representation of the cyclic quiver with two vertices. -/
structure CQRep (k : Type u) [Field k] where
  V : Type u
  W : Type u
  [instV : AddCommGroup V]
  [modV : Module k V]
  [instW : AddCommGroup W]
  [modW : Module k W]
  A : V →ₗ[k] W
  B : W →ₗ[k] V

attribute [instance] CQRep.instV CQRep.modV CQRep.instW CQRep.modW

variable {k : Type u} [Field k]

/-- The representation with the roles of the two vertices exchanged. -/
abbrev CQRep.swap (R : CQRep k) : CQRep k := ⟨R.W, R.V, R.B, R.A⟩

/-- `R` is indecomposable. -/
def CQRep.Indec (R : CQRep k) : Prop := CQIndec R.A R.B

/-- An isomorphism of representations: linear equivalences commuting with `A` and `B`. -/
structure CQIso (R R' : CQRep k) where
  e : R.V ≃ₗ[k] R'.V
  f : R.W ≃ₗ[k] R'.W
  hA : ∀ v, f (R.A v) = R'.A (e v)
  hB : ∀ w, e (R.B w) = R'.B (f w)

/-- `E_{m+1,λ}`: `V = W = k^{m+1}`, `A = J(λ)`, `B = 1`. -/
abbrev cqE (m : ℕ) (c : k) : CQRep k :=
  ⟨Fin (m + 1) → k, Fin (m + 1) → k, c • LinearMap.id + shiftDown (m + 1), LinearMap.id⟩

/-- `E_{m+1,∞}`: `A = 1`, `B = J(0)`. -/
abbrev cqEinf (m : ℕ) : CQRep k :=
  ⟨Fin (m + 1) → k, Fin (m + 1) → k, LinearMap.id, shiftDown (m + 1)⟩

/-- `H_{m+1}`: `V = k^{m+1}`, `W = k^m`, `A v_i = w_i`, `A v_{m+1} = 0`, `B w_i = v_{i+1}`. -/
abbrev cqH (m : ℕ) : CQRep k := ⟨Fin (m + 1) → k, Fin m → k, truncA m, shiftB m⟩

/-- `K_{m+1}`: the swap of `H_{m+1}`. -/
abbrev cqK (m : ℕ) : CQRep k := (cqH m).swap

theorem cqIndec_shiftDown (m : ℕ) :
    CQIndec (shiftDown (m + 1) : (Fin (m + 1) → k) →ₗ[k] (Fin (m + 1) → k)) LinearMap.id := by
  refine cq_indec_of_ker _ _ (Or.inl inferInstance) ⟨m + 1, ?_⟩ (fun w h => h)
    (Pi.single (0 : Fin (m + 1)) (1 : k)) (fun x hx => ⟨x 0, shiftDown_ker x hx⟩)
  simpa using shiftDown_nilpotent (k := k) (m + 1)

/-- Problem 5.39(a): `E_{n,λ}` is indecomposable. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem cqE_indec (m : ℕ) (c : k) : (cqE m c).Indec :=
  cq_indec_shift _ c (cqIndec_shiftDown m)

/-- Problem 5.39(a): `E_{n,∞}` is indecomposable. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem cqEinf_indec (m : ℕ) : (cqEinf (k := k) m).Indec :=
  (cqIndec_shiftDown m).swap

/-- Problem 5.39(a): `H_n` is indecomposable. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem cqH_indec (m : ℕ) : (cqH (k := k) m).Indec := by
  refine cq_indec_of_ker (cqH (k := k) m).A (cqH (k := k) m).B
    (Or.inl (inferInstanceAs (Nontrivial (Fin (m + 1) → k)))) ⟨m + 1, ?_⟩ shiftB_inj
    (Pi.single (Fin.last m) (1 : k)) (fun x hx => ⟨x (Fin.last m), truncA_ker x hx⟩)
  show ((shiftB m ∘ₗ truncA m : Module.End k (Fin (m + 1) → k)) ^ (m + 1)) = 0
  rw [shiftB_comp_truncA]; exact shiftUp_nilpotent (m + 1)

/-- Problem 5.39(a): `K_n` is indecomposable. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem cqK_indec (m : ℕ) : (cqK (k := k) m).Indec := (cqH_indec m).swap

/-! ### Non-isomorphism -/

namespace CQIso

variable {R R' : CQRep k}

theorem finrank_V (φ : CQIso R R') : finrank k R.V = finrank k R'.V := φ.e.finrank_eq

theorem finrank_W (φ : CQIso R R') : finrank k R.W = finrank k R'.W := φ.f.finrank_eq

theorem injA (φ : CQIso R R') (h : Function.Injective R.A) : Function.Injective R'.A := by
  intro x y hxy
  apply φ.e.symm.injective
  apply h
  apply φ.f.injective
  rw [φ.hA, φ.hA]
  simpa using hxy

theorem eig (φ : CQIso R R') {c : k} (h : ∃ v : R.V, v ≠ 0 ∧ R.B (R.A v) = c • v) :
    ∃ v : R'.V, v ≠ 0 ∧ R'.B (R'.A v) = c • v := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨φ.e v, fun h0 => hv0 (φ.e.injective (by rw [h0, map_zero])), ?_⟩
  rw [← φ.hA, ← φ.hB, hv, map_smul]

end CQIso

theorem nilp_eigen {X : Type*} [AddCommGroup X] [Module k X] (N : Module.End k X) (t : ℕ)
    (hN : N ^ t = 0) (a : k) (ha : a ≠ 0) (v : X) (hv : N v = a • v) : v = 0 := by
  have : ∀ j : ℕ, (N ^ j) v = a ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have h := this t
  rw [hN] at h
  have h2 : a ^ t • v = 0 := by rw [← h]; rfl
  exact (smul_eq_zero.1 h2).resolve_left (pow_ne_zero _ ha)

def CQIso.symm {R R' : CQRep k} (φ : CQIso R R') : CQIso R' R where
  e := φ.e.symm
  f := φ.f.symm
  hA w := by
    apply φ.f.injective
    rw [LinearEquiv.apply_symm_apply, φ.hA, LinearEquiv.apply_symm_apply]
  hB w := by
    apply φ.e.injective
    rw [LinearEquiv.apply_symm_apply, φ.hB, LinearEquiv.apply_symm_apply]

theorem shiftDown_single_zero (m : ℕ) :
    shiftDown (m + 1) (Pi.single (0 : Fin (m + 1)) (1 : k)) = 0 := by
  funext j
  simp [shiftDown]

theorem cqE_eig_self (m : ℕ) (c : k) :
    ∃ v : (cqE m c).V, v ≠ 0 ∧ (cqE m c).B ((cqE m c).A v) = c • v := by
  refine ⟨(Pi.single (0 : Fin (m + 1)) (1 : k) : Fin (m + 1) → k), ?_, ?_⟩
  · intro h
    have h1 : (Pi.single (0 : Fin (m + 1)) (1 : k) : Fin (m + 1) → k) 0 =
        (0 : Fin (m + 1) → k) 0 := congrFun h 0
    simp at h1
  · show (c • LinearMap.id + shiftDown (m + 1) : (Fin (m + 1) → k) →ₗ[k] _)
      (Pi.single (0 : Fin (m + 1)) (1 : k)) = _
    rw [LinearMap.add_apply, shiftDown_single_zero, add_zero]
    rfl

theorem cqE_eig (m : ℕ) (c c' : k)
    (h : ∃ v : (cqE m c).V, v ≠ 0 ∧ (cqE m c).B ((cqE m c).A v) = c' • v) : c' = c := by
  by_contra hne
  obtain ⟨v, hv0, hv⟩ := h
  apply hv0
  refine nilp_eigen (shiftDown (m + 1)) (m + 1) (shiftDown_nilpotent _) (c' - c)
    (sub_ne_zero.2 hne) (v : Fin (m + 1) → k) ?_
  have : c • (v : Fin (m + 1) → k) + shiftDown (m + 1) v = c' • (v : Fin (m + 1) → k) := hv
  rw [_root_.sub_smul, ← this]; abel

theorem cqEinf_eig (m : ℕ) (c' : k)
    (h : ∃ v : (cqEinf (k := k) m).V, v ≠ 0 ∧
      (cqEinf m).B ((cqEinf m).A v) = c' • v) : c' = 0 := by
  by_contra hne
  obtain ⟨v, hv0, hv⟩ := h
  exact hv0 (nilp_eigen (shiftDown (m + 1)) (m + 1) (shiftDown_nilpotent _) c' hne
    (v : Fin (m + 1) → k) hv)

theorem cqE_zero_not_injA (m : ℕ) : ¬ Function.Injective (cqE (k := k) m 0).A := by
  intro h
  have h1 : (cqE (k := k) m 0).A (Pi.single (0 : Fin (m + 1)) (1 : k) : Fin (m + 1) → k) =
      (cqE (k := k) m 0).A 0 := by
    show (((0 : k) • LinearMap.id + shiftDown (m + 1) : (Fin (m + 1) → k) →ₗ[k] _))
      (Pi.single (0 : Fin (m + 1)) (1 : k)) = _
    rw [LinearMap.add_apply, shiftDown_single_zero, add_zero]
    simp
  have h2 : (Pi.single (0 : Fin (m + 1)) (1 : k) : Fin (m + 1) → k) 0 =
      (0 : Fin (m + 1) → k) 0 := congrFun (h h1) 0
  simp at h2

theorem E_Einf_false (m m' : ℕ) (c : k) (φ : CQIso (cqE m c) (cqEinf m')) : False := by
  have hV := φ.finrank_V
  simp only [Module.finrank_fin_fun] at hV
  have hm : m = m' := by omega
  subst hm
  by_cases hc : c = 0
  · subst hc
    exact cqE_zero_not_injA m (φ.symm.injA (show Function.Injective
      (LinearMap.id : (Fin (m + 1) → k) →ₗ[k] _) from fun x y h => h))
  · have := cqEinf_eig m c (φ.eig (cqE_eig_self m c))
    exact hc this

/-- The parameters of the four families of Problem 5.39. -/
inductive CQParam (k : Type u) [Field k]
  | E (m : ℕ) (c : k)
  | Einf (m : ℕ)
  | H (m : ℕ)
  | K (m : ℕ)

/-- The representation attached to a parameter (the index is shifted: `m + 1` is the paper's `n`). -/
abbrev CQParam.rep : CQParam k → CQRep k
  | .E m c => cqE m c
  | .Einf m => cqEinf m
  | .H m => cqH m
  | .K m => cqK m

/-- Problem 5.39(a): the representations `E_{n,λ}`, `E_{n,∞}`, `H_n`, `K_n` are indecomposable. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem CQParam.rep_indec (p : CQParam k) : p.rep.Indec := by
  cases p
  · exact cqE_indec _ _
  · exact cqEinf_indec _
  · exact cqH_indec _
  · exact cqK_indec _

/-- Problem 5.39(a): the representations `E_{n,λ}`, `E_{n,∞}`, `H_n`, `K_n` are pairwise
non-isomorphic. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem CQParam.rep_noniso (p q : CQParam k) (φ : CQIso p.rep q.rep) : p = q := by
  have hV := φ.finrank_V
  have hW := φ.finrank_W
  rcases p with ⟨m, c⟩ | m | m | m <;> rcases q with ⟨m', c'⟩ | m' | m' | m' <;>
    simp only [CQParam.rep, cqE, cqEinf, cqH, cqK, CQRep.swap, Module.finrank_fin_fun] at hV hW <;>
    try omega
  · have hm : m = m' := by omega
    subst hm
    have := cqE_eig m c' c (φ.eig (cqE_eig_self m c))
    rw [this]
  · exact (E_Einf_false m m' c φ).elim
  · exact (E_Einf_false m' m c' φ.symm).elim
  · have hm : m = m' := by omega
    rw [hm]
  · have hm : m = m' := by omega
    rw [hm]
  · have hm : m = m' := by omega
    rw [hm]

end Families

section Fitting

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem cq_comp_pow (A : V →ₗ[k] W) (B : W →ₗ[k] V) (n : ℕ) :
    A ∘ₗ ((B ∘ₗ A) ^ n : Module.End k V) = ((A ∘ₗ B) ^ n : Module.End k W) ∘ₗ A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, LinearMap.comp_assoc]
    rfl

/-- Problem 5.39(b) (Fitting decomposition): for a finite-dimensional representation `(A, B)` there
is `N ≥ 1` such that `(ker (BA)^N, ker (AB)^N) ⊕ (range (BA)^N, range (AB)^N)` is a decomposition
into a subrepresentation on which `BA` and `AB` are nilpotent and one on which `A` and `B` are
bijective.  In particular, if `AB` is not nilpotent then the second summand is nonzero. -/
@[kb "etingof2011" "Problem 5.39, p. 96"]
theorem cq_fitting [FiniteDimensional k V] [FiniteDimensional k W]
    (A : V →ₗ[k] W) (B : W →ₗ[k] V) :
    ∃ N : ℕ, 0 < N ∧
      CQDecomp A B (LinearMap.ker ((B ∘ₗ A) ^ N : Module.End k V))
        (LinearMap.range ((B ∘ₗ A) ^ N : Module.End k V))
        (LinearMap.ker ((A ∘ₗ B) ^ N : Module.End k W))
        (LinearMap.range ((A ∘ₗ B) ^ N : Module.End k W)) ∧
      (∀ v ∈ LinearMap.range ((B ∘ₗ A) ^ N : Module.End k V), A v = 0 → v = 0) ∧
      (∀ w ∈ LinearMap.range ((A ∘ₗ B) ^ N : Module.End k W), B w = 0 → w = 0) ∧
      (∀ w ∈ LinearMap.range ((A ∘ₗ B) ^ N : Module.End k W),
        ∃ v ∈ LinearMap.range ((B ∘ₗ A) ^ N : Module.End k V), A v = w) ∧
      (∀ v ∈ LinearMap.range ((B ∘ₗ A) ^ N : Module.End k V),
        ∃ w ∈ LinearMap.range ((A ∘ₗ B) ^ N : Module.End k W), B w = v) := by
  set T : Module.End k V := B ∘ₗ A with hT
  set S : Module.End k W := A ∘ₗ B with hS
  have h1 := T.eventually_isCompl_ker_pow_range_pow
  have h2 := S.eventually_isCompl_ker_pow_range_pow
  have h3 := T.eventually_iInf_range_pow_eq
  have h4 := S.eventually_iInf_range_pow_eq
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (h3.and h4)))
  set N := max N0 1 with hN
  have hN1 : 0 < N := by omega
  have hNN0 : N0 ≤ N := le_max_left _ _
  have c1 := (hN0 N hNN0).1
  have c2 := (hN0 N hNN0).2.1
  have stabT : ∀ m, N ≤ m → LinearMap.range (T ^ m) = LinearMap.range (T ^ N) := fun m hm => by
    rw [← (hN0 m (hNN0.trans hm)).2.2.1, (hN0 N hNN0).2.2.1]
  have stabS : ∀ m, N ≤ m → LinearMap.range (S ^ m) = LinearMap.range (S ^ N) := fun m hm => by
    rw [← (hN0 m (hNN0.trans hm)).2.2.2, (hN0 N hNN0).2.2.2]
  have eAT : ∀ n v, A ((T ^ n) v) = (S ^ n) (A v) := fun n v =>
    congrArg (fun F => F v) (cq_comp_pow A B n)
  have eBS : ∀ n w, B ((S ^ n) w) = (T ^ n) (B w) := fun n w =>
    congrArg (fun F => F w) (cq_comp_pow B A n)
  refine ⟨N, hN1, ⟨c1, c2, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← eAT, hv, map_zero]
  · rintro _ ⟨u, rfl⟩
    exact ⟨A u, by rw [eAT]⟩
  · intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← eBS, hw, map_zero]
  · rintro _ ⟨u, rfl⟩
    exact ⟨B u, by rw [eBS]⟩
  · intro v hv hAv
    have hTv : (T ^ N) v = 0 := by
      have e : T ^ N = T ^ (N - 1) * T := by rw [← pow_succ, Nat.sub_add_cancel hN1]
      rw [e, Module.End.mul_apply]
      have : T v = 0 := by simp [hT, hAv]
      rw [this, map_zero]
    exact Submodule.disjoint_def.1 c1.disjoint v hTv hv
  · intro w hw hBw
    have hSw : (S ^ N) w = 0 := by
      have e : S ^ N = S ^ (N - 1) * S := by rw [← pow_succ, Nat.sub_add_cancel hN1]
      rw [e, Module.End.mul_apply]
      have : S w = 0 := by simp [hS, hBw]
      rw [this, map_zero]
    exact Submodule.disjoint_def.1 c2.disjoint w hSw hw
  · intro w hw
    have hw' : w ∈ LinearMap.range (S ^ (2 * N)) := by
      rw [stabS (2 * N) (by omega)]; exact hw
    obtain ⟨u, rfl⟩ := hw'
    refine ⟨B ((S ^ (2 * N - 1)) u), ?_, ?_⟩
    · rw [eBS]
      have : (T ^ (2 * N - 1)) (B u) ∈ LinearMap.range (T ^ (2 * N - 1)) :=
        LinearMap.mem_range_self _ _
      rwa [stabT (2 * N - 1) (by omega)] at this
    · have e : S ^ (2 * N) = S * S ^ (2 * N - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e, Module.End.mul_apply]
      rfl
  · intro v hv
    have hv' : v ∈ LinearMap.range (T ^ (2 * N)) := by
      rw [stabT (2 * N) (by omega)]; exact hv
    obtain ⟨u, rfl⟩ := hv'
    refine ⟨A ((T ^ (2 * N - 1)) u), ?_, ?_⟩
    · rw [eAT]
      have : (S ^ (2 * N - 1)) (A u) ∈ LinearMap.range (S ^ (2 * N - 1)) :=
        LinearMap.mem_range_self _ _
      rwa [stabS (2 * N - 1) (by omega)] at this
    · have e : T ^ (2 * N) = T * T ^ (2 * N - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e, Module.End.mul_apply]
      rfl

end Fitting

end UndergradKB.RepresentationTheory
