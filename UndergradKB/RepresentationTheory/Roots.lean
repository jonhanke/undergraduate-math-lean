import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import UndergradKB.Common.Attr

/-! # Roots of a graph and reflections (Etingof et al., §5.6-5.7)

For a finite simple graph `G` on `Fin n` (with decidable adjacency):

* `cartanMatrix G = 2 Id - adjacency matrix` and the symmetric bilinear form `form G` on `ℤⁿ` (Definition 5.11);
  `cartanMatrix_pathGraph` identifies the Cartan matrix of the path graph with Mathlib's `CartanMatrix.A`.
* `form_self_even`: `B(x, x)` is even on integer vectors, for any (loopless) graph (Lemma 5.12).
* `PosDefinite G` says the real matrix is positive definite, and `IsDynkin G` adds connectedness (Problem 5.3
  definition); positive definiteness gives `B(x, x) ≥ 2` for nonzero integer `x`.
* Roots are integer vectors with `B(x, x) = 2` (`IsRoot`); finitely many for a positive definite form
  (`roots_finite`, Remark 5.14); simple roots `simpleRoot i` (Definition 5.15); positive / negative roots
  (Definition 5.17); every root of a positive definite graph is positive or negative (`isRoot_sign`,
  Lemma 5.16, Remark 5.18), by the book's argument.
* Reflections `reflect G α` (built on `Module.reflection`) in a root `α` (Definition 5.20), their properties
  (Remark 5.21), simple reflections, the Coxeter element (Definition 5.32) and the Weyl group, which is finite
  for a positive definite form.
* Example 5.19: for the path graph with `n` vertices (type `A_n`, `N = n + 1`), the vectors `e_a - e_b`
  (`a < b ≤ n`) are the interval vectors `intervalRoot n a b`; these are positive roots and there are
  `N (N - 1) / 2` of them.
-/

namespace UndergradKB.RepresentationTheory.Roots

open Matrix

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- The Cartan matrix of a graph: twice the identity minus the adjacency matrix. -/
@[kb "etingof2011" "Definition 5.11, p. 87"]
def cartanMatrix : Matrix (Fin n) (Fin n) ℤ := (2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) - G.adjMatrix ℤ

theorem cartanMatrix_apply (i j : Fin n) :
    cartanMatrix G i j = (if i = j then 2 else 0) - (if G.Adj i j then 1 else 0) := by
  simp only [cartanMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp

theorem cartanMatrix_diag (i : Fin n) : cartanMatrix G i i = 2 := by
  simp [cartanMatrix_apply]

theorem cartanMatrix_symm (i j : Fin n) : cartanMatrix G i j = cartanMatrix G j i := by
  simp only [cartanMatrix_apply]
  have : G.Adj i j ↔ G.Adj j i := G.adj_comm i j
  simp [eq_comm, this]

theorem cartanMatrix_offDiag_nonpos {i j : Fin n} (h : i ≠ j) : cartanMatrix G i j ≤ 0 := by
  rw [cartanMatrix_apply]
  simp only [h, ite_false]
  split_ifs <;> simp

/-- The symmetric bilinear form `B(x, y) = xᵀ A y` on `ℤⁿ` attached to the Cartan matrix of the graph. -/
@[kb "etingof2011" "Definition 5.11, p. 87"]
def form (x y : Fin n → ℤ) : ℤ := x ⬝ᵥ (cartanMatrix G *ᵥ y)

theorem form_eq_sum (x y : Fin n → ℤ) :
    form G x y = ∑ i, ∑ j, x i * cartanMatrix G i j * y j := by
  simp only [form, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_comm (x y : Fin n → ℤ) : form G x y = form G y x := by
  rw [form_eq_sum, form_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [cartanMatrix_symm]; ring

theorem form_add_left (x x' y : Fin n → ℤ) : form G (x + x') y = form G x y + form G x' y := by
  simp [form, add_dotProduct]

theorem form_add_right (x y y' : Fin n → ℤ) : form G x (y + y') = form G x y + form G x y' := by
  simp [form, dotProduct_add, mulVec_add]

theorem form_sub_left (x x' y : Fin n → ℤ) : form G (x - x') y = form G x y - form G x' y := by
  simp [form, sub_dotProduct]

theorem form_sub_right (x y y' : Fin n → ℤ) : form G x (y - y') = form G x y - form G x y' := by
  simp [form, dotProduct_sub, mulVec_sub]

theorem form_smul_left (c : ℤ) (x y : Fin n → ℤ) : form G (c • x) y = c * form G x y := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_smul_right (c : ℤ) (x y : Fin n → ℤ) : form G x (c • y) = c * form G x y := by
  simp only [form, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_neg_left (x y : Fin n → ℤ) : form G (-x) y = - form G x y := by
  simp [form]

theorem form_neg_right (x y : Fin n → ℤ) : form G x (-y) = - form G x y := by
  simp [form, mulVec_neg]

theorem form_single_single (i j : Fin n) : form G (Pi.single i 1) (Pi.single j 1) = cartanMatrix G i j := by
  simp [form_eq_sum, Pi.single_apply]

/-- A symmetric integer array with zero diagonal has even total sum (each off-diagonal entry occurs twice). -/
theorem even_sum_symm {n : ℕ} (g : Fin n → Fin n → ℤ) (hs : ∀ i j, g i j = g j i)
    (hd : ∀ i, g i i = 0) : Even (∑ i, ∑ j, g i j) := by
  have h1 : ∀ i j, g i j = (if i < j then g i j else 0) + (if j < i then g j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp [hd]
    · simp [h, h.not_gt, hs i j]
  have h2 : ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j else 0) +
      ∑ i, ∑ j, (if j < i then g j i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => h1 i j
  rw [h2, Finset.sum_comm (f := fun i j => if j < i then g j i else 0)]
  exact ⟨_, rfl⟩

/-- `B(x, x)` is even for every integer vector `x` (the graph is loopless, so this holds for every graph). -/
@[kb "etingof2011" "Lemma 5.12, p. 87"]
theorem form_self_even (x : Fin n → ℤ) : Even (form G x x) := by
  rw [form_eq_sum]
  have hf : ∀ i j : Fin n, x i * cartanMatrix G i j * x j =
      (if i = j then 2 * (x i * x i) else 0) -
        (if G.Adj i j then x i * x j else 0) := by
    intro i j
    rw [cartanMatrix_apply]
    split_ifs with h1 h2 h2
    · subst h1; exact absurd h2 (G.loopless.irrefl _)
    · subst h1; ring
    · ring
    · ring
  simp only [hf, Finset.sum_sub_distrib]
  refine Even.sub ?_ ?_
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact ⟨∑ i, x i * x i, by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring⟩
  · refine even_sum_symm _ ?_ ?_
    · intro i j
      simp only [G.adj_comm i j]
      split_ifs <;> ring
    · intro i; simp

/-- The Cartan matrix of the graph, viewed as a real matrix, is positive definite. -/
@[kb "etingof2011" "Lemma 5.12, p. 87"]
def PosDefinite : Prop := ((cartanMatrix G).map (Int.cast : ℤ → ℝ)).PosDef

theorem form_cast (x y : Fin n → ℤ) :
    ((form G x y : ℤ) : ℝ) =
      (fun i => (x i : ℝ)) ⬝ᵥ (((cartanMatrix G).map (Int.cast : ℤ → ℝ)) *ᵥ fun i => (y i : ℝ)) := by
  simp [form, dotProduct, mulVec]

theorem PosDefinite.form_pos {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h : PosDefinite G)
    {x : Fin n → ℤ} (hx : x ≠ 0) : 0 < form G x x := by
  have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 h).2 hx'
  have h2 : ((0 : ℤ) : ℝ) < ((form G x x : ℤ) : ℝ) := by
    rw [form_cast]; simpa using this
  exact_mod_cast h2

theorem PosDefinite.two_le {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h : PosDefinite G)
    {x : Fin n → ℤ} (hx : x ≠ 0) : 2 ≤ form G x x := by
  obtain ⟨k, hk⟩ := form_self_even G x
  have := h.form_pos hx
  omega

/-- A Dynkin diagram: a connected graph whose form is positive definite (the definition of Problem 5.3). -/
@[kb "etingof2011" "Problem 5.3, p. 78"]
def IsDynkin : Prop := G.Connected ∧ PosDefinite G

/-- A root: an integer vector `x` with `B(x, x) = 2`. For a positive definite form these are the shortest
nonzero integer vectors, since `B(x, x)` is even and positive. -/
@[kb "etingof2011" "Definition 5.13, p. 87"]
def IsRoot (x : Fin n → ℤ) : Prop := form G x x = 2

/-- The simple root `α_i`: the `i`-th standard basis vector. -/
@[kb "etingof2011" "Definition 5.15, p. 87"]
def simpleRoot (i : Fin n) : Fin n → ℤ := Pi.single i 1

theorem isRoot_simpleRoot (i : Fin n) : IsRoot G (simpleRoot i) := by
  simp [IsRoot, simpleRoot, form_single_single, cartanMatrix_diag]

/-- A positive root: a root all of whose coordinates are nonnegative. -/
@[kb "etingof2011" "Definition 5.17, p. 88"]
def IsPositiveRoot (x : Fin n → ℤ) : Prop := IsRoot G x ∧ ∀ i, 0 ≤ x i
/-- A negative root: a root all of whose coordinates are nonpositive. -/
@[kb "etingof2011" "Definition 5.17, p. 88"]
def IsNegativeRoot (x : Fin n → ℤ) : Prop := IsRoot G x ∧ ∀ i, x i ≤ 0

theorem IsRoot.ne_zero {x : Fin n → ℤ} (h : IsRoot G x) : x ≠ 0 := by
  rintro rfl
  simp [IsRoot, form] at h

/-- For a positive definite form there are only finitely many roots. -/
@[kb "etingof2011" "Remark 5.14, p. 87"]
theorem roots_finite (h : PosDefinite G) : {x : Fin n → ℤ | IsRoot G x}.Finite := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have : Subsingleton (Fin n → ℤ) := inferInstance
    have : Finite (Fin n → ℤ) := Finite.of_subsingleton
    exact Set.toFinite _
  set M : Matrix (Fin n) (Fin n) ℝ := (cartanMatrix G).map (Int.cast : ℤ → ℝ) with hM
  let Q : (Fin n → ℝ) → ℝ := fun v => v ⬝ᵥ (M *ᵥ v)
  have hQc : Continuous Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  have hcomp : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
    obtain ⟨i⟩ := hn
    exact ⟨Pi.single i 1, by simp [Pi.norm_single]⟩
  obtain ⟨v0, hv0, hmin⟩ := hcomp.exists_isMinOn hne hQc.continuousOn
  have hv0ne : v0 ≠ 0 := by
    rintro rfl; simp at hv0
  have hm : 0 < Q v0 := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.1 h).2 hv0ne
    simpa [Q] using this
  -- lower bound
  have hlow : ∀ v : Fin n → ℝ, Q v0 * ‖v‖ ^ 2 ≤ Q v := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp [Q]
    · have hr : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hs : (‖v‖⁻¹ • v) ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
        simp [norm_smul, hr.ne']
      have h1 := hmin hs
      simp only [Set.mem_ofPred_eq] at h1
      have h2 : Q (‖v‖⁻¹ • v) = (‖v‖⁻¹) ^ 2 * Q v := by
        simp only [Q, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]; ring
      rw [h2] at h1
      have h3 : Q v0 * ‖v‖ ^ 2 ≤ (‖v‖⁻¹) ^ 2 * Q v * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h4 : (‖v‖⁻¹) ^ 2 * Q v * ‖v‖ ^ 2 = Q v := by
        field_simp
      linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / Q v0)
  refine (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-(N : ℤ)) N) fun _ => Set.finite_Icc _ _).subset ?_
  intro x hx
  have hx2 : ((form G x x : ℤ) : ℝ) = 2 := by
    have : form G x x = 2 := hx
    rw [this]; norm_num
  have hQx : Q (fun i => (x i : ℝ)) = 2 := by
    simp only [Q, M]; rw [← form_cast]; exact hx2
  have hb := hlow (fun i => (x i : ℝ))
  rw [hQx] at hb
  have hbound : ∀ i, |x i| ≤ N := by
    intro i
    have h1 : |(x i : ℝ)| ≤ ‖fun i => (x i : ℝ)‖ := by
      simpa using norm_le_pi_norm (fun i => (x i : ℝ)) i
    have h2 : |(x i : ℝ)| ^ 2 ≤ N := by
      have h3 : ‖fun i => (x i : ℝ)‖ ^ 2 ≤ 2 / Q v0 := by
        rw [le_div_iff₀ hm]; linarith
      have h5 : |(x i : ℝ)| ^ 2 ≤ ‖fun i => (x i : ℝ)‖ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      linarith
    have h7 : ((|x i| : ℤ) : ℝ) ^ 2 ≤ N := by simpa using h2
    have h8 : |x i| ^ 2 ≤ (N : ℤ) := by exact_mod_cast h7
    have h9 : |x i| ≤ |x i| ^ 2 := by nlinarith [abs_nonneg (x i), Int.abs_eq_natAbs (x i)]
    exact h9.trans h8 |>.trans (by exact_mod_cast le_refl N)
  intro i _
  exact abs_le.1 (hbound i)

/-- Every root of a positive definite graph has all coordinates nonnegative or all nonpositive. The proof splits
the root into its positive and negative parts, whose form is at least `2` each unless one vanishes. -/
@[kb "etingof2011" "Lemma 5.16, p. 87"]
theorem isRoot_sign (h : PosDefinite G) {x : Fin n → ℤ} (hx : IsRoot G x) :
    (∀ i, 0 ≤ x i) ∨ (∀ i, x i ≤ 0) := by
  set p : Fin n → ℤ := fun i => max (x i) 0 with hp
  set q : Fin n → ℤ := fun i => max (- x i) 0 with hq
  have hxpq : x = p - q := by
    funext i
    simp only [hp, hq, Pi.sub_apply]
    rcases le_total 0 (x i) with h0 | h0
    · simp [h0]
    · simp [h0]
  have hpq : form G p q ≤ 0 := by
    rw [form_eq_sum]
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp only [hp, hq]
      rcases le_total 0 (x i) with h0 | h0
      · simp [h0]
      · simp [h0]
    · have h1 := cartanMatrix_offDiag_nonpos G hij
      have h2 : 0 ≤ p i := le_max_right _ _
      have h3 : 0 ≤ q j := le_max_right _ _
      have := mul_nonneg h2 (neg_nonneg.2 h1)
      nlinarith [mul_nonneg this h3]
  have hsum : form G x x = form G p p + form G q q - 2 * form G p q := by
    rw [hxpq, form_sub_left, form_sub_right, form_sub_right, form_comm G q p]
    ring
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
  have hp0 : p ≠ 0 := by
    intro h0
    have := congrFun h0 j
    simp only [hp, Pi.zero_apply] at this
    omega
  have hq0 : q ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp only [hq, Pi.zero_apply] at this
    omega
  have := h.two_le hp0
  have := h.two_le hq0
  unfold IsRoot at hx
  omega

/-- The linear form `v ↦ B(v, α)`. -/
def formDual (α : Fin n → ℤ) : Module.Dual ℤ (Fin n → ℤ) where
  toFun v := form G v α
  map_add' u v := form_add_left G u v α
  map_smul' c v := by simpa using form_smul_left G c v α

theorem formDual_apply (α v : Fin n → ℤ) : formDual G α v = form G v α := rfl

/-- The reflection `s_α(v) = v - B(v, α) α` in a root `α` (here for an arbitrary root, not only a positive one),
built from `Module.reflection`. -/
@[kb "etingof2011" "Definition 5.20, p. 89"]
def reflect (α : Fin n → ℤ) (hα : IsRoot G α) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  Module.reflection (f := formDual G α) (x := α) hα

theorem reflect_apply (α : Fin n → ℤ) (hα : IsRoot G α) (v : Fin n → ℤ) :
    reflect G α hα v = v - form G v α • α :=
  Module.reflection_apply _ _

theorem reflect_self (α : Fin n → ℤ) (hα : IsRoot G α) : reflect G α hα α = -α :=
  Module.reflection_apply_self _

/-- `s_α` fixes the vectors `B`-orthogonal to `α` (and sends `α` to `-α` by `reflect_self`): it is the
orthogonal reflection in the hyperplane `α^⊥`. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem reflect_of_form_eq_zero (α : Fin n → ℤ) (hα : IsRoot G α) {v : Fin n → ℤ}
    (hv : form G v α = 0) : reflect G α hα v = v := by
  simp [reflect_apply, hv]

/-- The reflection `s_α` preserves the form `B`. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem form_reflect (α : Fin n → ℤ) (hα : IsRoot G α) (u v : Fin n → ℤ) :
    form G (reflect G α hα u) (reflect G α hα v) = form G u v := by
  have h2 : form G α α = 2 := hα
  simp only [reflect_apply, form_sub_left, form_sub_right, form_smul_left, form_smul_right,
    form_comm G α v, h2]
  ring

theorem isRoot_reflect {α : Fin n → ℤ} (hα : IsRoot G α) {x : Fin n → ℤ} (hx : IsRoot G x) :
    IsRoot G (reflect G α hα x) := by
  show form G _ _ = 2
  rw [form_reflect]; exact hx

/-- The reflection `s_α` is an involution. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem reflect_involutive (α : Fin n → ℤ) (hα : IsRoot G α) :
    Function.Involutive (reflect G α hα) :=
  Module.involutive_reflection _

theorem reflect_reflect (α : Fin n → ℤ) (hα : IsRoot G α) (v : Fin n → ℤ) :
    reflect G α hα (reflect G α hα v) = v := reflect_involutive G α hα v

/-- A reflection in a root permutes the set of roots. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem bijOn_reflect_roots (α : Fin n → ℤ) (hα : IsRoot G α) :
    Set.BijOn (reflect G α hα) {x | IsRoot G x} {x | IsRoot G x} :=
  Module.bijOn_reflection_of_mapsTo _ (fun _ hx => isRoot_reflect G hα hx)

/-- The simple reflection `s_i`, the reflection in the simple root `α_i`. -/
@[kb "etingof2011" "Definition 5.20, p. 89"]
def simpleReflection (i : Fin n) : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) :=
  reflect G (simpleRoot i) (isRoot_simpleRoot G i)

theorem simpleReflection_apply (i : Fin n) (v : Fin n → ℤ) :
    simpleReflection G i v = v - form G v (simpleRoot i) • simpleRoot i :=
  reflect_apply G _ _ v

/-- The Coxeter element `c = s_0 s_1 ⋯ s_{n-1}` for the vertex labelling by `Fin n` (product in the group of
linear automorphisms of `ℤⁿ`, so `s_{n-1}` is applied first). -/
@[kb "etingof2011" "Definition 5.32, p. 93"]
def coxeterElement : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ) := (List.ofFn (simpleReflection G)).prod

/-- The Weyl group of the graph: the subgroup of linear automorphisms of `ℤⁿ` generated by the simple reflections. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
def weylGroup : Subgroup ((Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) :=
  Subgroup.closure (Set.range (simpleReflection G))

theorem mapsTo_roots_of_mem_weylGroup {w : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)} (hw : w ∈ weylGroup G) :
    (∀ x, IsRoot G x → IsRoot G (w x)) ∧ (∀ x, IsRoot G x → IsRoot G (w.symm x)) := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    refine ⟨fun x hx => isRoot_reflect G (isRoot_simpleRoot G i) hx, fun x hx => ?_⟩
    have : (simpleReflection G i).symm = simpleReflection G i :=
      LinearEquiv.ext fun v => by
        rw [LinearEquiv.symm_apply_eq]
        exact (reflect_involutive G (simpleRoot i) (isRoot_simpleRoot G i) v).symm
    rw [this]; exact isRoot_reflect G (isRoot_simpleRoot G i) hx
  | one => exact ⟨fun x hx => hx, fun x hx => hx⟩
  | mul a b _ _ ha hb => exact ⟨fun x hx => ha.1 _ (hb.1 x hx), fun x hx => hb.2 _ (ha.2 x hx)⟩
  | inv a _ ha => exact ⟨ha.2, ha.1⟩

/-- For a positive definite form the Weyl group is finite: it acts faithfully on the finite set of roots. -/
@[kb "etingof2011" "Remark 5.21, p. 89"]
theorem weylGroup_finite (h : PosDefinite G) : Finite (weylGroup G) := by
  have hR : Finite {x : Fin n → ℤ | IsRoot G x} := (roots_finite G h).to_subtype
  let f : weylGroup G → ({x : Fin n → ℤ | IsRoot G x} → {x : Fin n → ℤ | IsRoot G x}) :=
    fun w x => ⟨w.1 x.1, (mapsTo_roots_of_mem_weylGroup G w.2).1 x.1 x.2⟩
  refine Finite.of_injective f fun w w' hww => ?_
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℤ (Fin n)).ext
  intro i
  have := congrFun hww ⟨simpleRoot i, isRoot_simpleRoot G i⟩
  simpa [f, Subtype.ext_iff, simpleRoot] using this

theorem form_single_right (x : Fin n → ℤ) (j : Fin n) :
    form G x (Pi.single j 1) = ∑ i, x i * cartanMatrix G i j := by
  rw [form_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [hk]
  · simp

/-! ### Example 5.19 -/

/-- The Cartan matrix of the path graph is Mathlib's Cartan matrix of type `A`. -/
@[kb "etingof2011" "Definition 5.11, p. 87"]
theorem cartanMatrix_pathGraph (n : ℕ) : cartanMatrix (SimpleGraph.pathGraph n) = CartanMatrix.A n := by
  ext i j
  rw [cartanMatrix_apply, CartanMatrix.A]
  by_cases h : i = j
  · subst h; simp
  · by_cases h2 : i.val + 1 = j.val ∨ j.val + 1 = i.val <;>
      simp [h, h2, SimpleGraph.pathGraph_adj]

/-- The vector `α_a + ⋯ + α_{b-1}` (the root `e_a - e_b` of `A_n` in simple-root coordinates). -/
@[kb "etingof2011" "Example 5.19, p. 88"]
def intervalRoot (n a b : ℕ) : Fin n → ℤ := fun k => if a ≤ k.val ∧ k.val < b then 1 else 0

theorem form_intervalRoot_simple (n a b : ℕ) (hab : a < b) (hb : b < n) :
    form (SimpleGraph.pathGraph n) (intervalRoot n a b) (simpleRoot ⟨b, hb⟩) = -1 := by
  rw [simpleRoot, form_single_right, Finset.sum_eq_single ⟨b - 1, by omega⟩]
  · simp [intervalRoot, cartanMatrix_pathGraph, CartanMatrix.A, Fin.ext_iff]
    omega
  · intro i _ hi
    by_cases h : a ≤ i.val ∧ i.val < b
    · have h1 : i.val ≠ b := by omega
      have h2 : ¬ (i.val + 1 = b) := fun h3 => hi (Fin.ext (by simp; omega))
      have h3 : ¬ (b + 1 = i.val) := by omega
      simp [intervalRoot, cartanMatrix_pathGraph, CartanMatrix.A, Fin.ext_iff, h1, h2, h3]
    · simp [intervalRoot, h]
  · simp

theorem intervalRoot_succ (n a b : ℕ) (hab : a < b) (hb : b < n) :
    intervalRoot n a (b + 1) =
      reflect (SimpleGraph.pathGraph n) (simpleRoot ⟨b, hb⟩) (isRoot_simpleRoot _ _)
        (intervalRoot n a b) := by
  rw [reflect_apply, form_intervalRoot_simple n a b hab hb]
  funext k
  simp only [intervalRoot, simpleRoot, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Fin.ext_iff]
  by_cases h : k.val = b
  · simp [h]; omega
  · simp [h]; omega

/-- The vectors `e_a - e_b` with `a < b ≤ n` are roots of the path graph. -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem isRoot_intervalRoot (n a b : ℕ) (hab : a < b) (hb : b ≤ n) :
    IsRoot (SimpleGraph.pathGraph n) (intervalRoot n a b) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have : intervalRoot n a (a + 1) = simpleRoot ⟨a, by omega⟩ := by
      funext k
      simp only [intervalRoot, simpleRoot, Pi.single_apply, Fin.ext_iff]
      by_cases h : k.val = a <;> simp [h]; omega
    rw [this]; exact isRoot_simpleRoot _ _
  | succ b hab ih =>
    rw [intervalRoot_succ n a b hab (by omega)]
    exact isRoot_reflect _ _ (ih (by omega))

theorem intervalRoot_nonneg (n a b : ℕ) (k : Fin n) : 0 ≤ intervalRoot n a b k := by
  unfold intervalRoot; split_ifs <;> omega

theorem intervalRoot_injective (n a b a' b' : ℕ) (hab : a < b) (hb : b ≤ n) (hab' : a' < b')
    (hb' : b' ≤ n) (h : intervalRoot n a b = intervalRoot n a' b') : a = a' ∧ b = b' := by
  have key : ∀ k : ℕ, (hk : k < n) → ((a ≤ k ∧ k < b) ↔ (a' ≤ k ∧ k < b')) := by
    intro k hk
    have := congrFun h ⟨k, hk⟩
    simp only [intervalRoot] at this
    by_cases h1 : a ≤ k ∧ k < b <;> by_cases h2 : a' ≤ k ∧ k < b'
    · exact iff_of_true h1 h2
    · simp [h1, h2] at this
    · simp [h1, h2] at this
    · exact iff_of_false h1 h2
  have h1 := key a (by omega)
  have h2 := key a' (by omega)
  have h3 := key (b - 1) (by omega)
  have h4 := key (b' - 1) (by omega)
  omega

/-- The path graph on `n` vertices (type `A_n`, `N = n + 1`) has at least `N (N - 1) / 2` positive roots,
namely the vectors `e_a - e_b`, `a < b`. (The book states that these are all of them; only this half is
formalized.) -/
@[kb "etingof2011" "Example 5.19, p. 88"]
theorem exists_positive_roots_A (n : ℕ) :
    ∃ T : Finset (Fin n → ℤ), T.card = (n + 1) * n / 2 ∧
      ∀ x ∈ T, IsPositiveRoot (SimpleGraph.pathGraph n) x := by
  classical
  let S : Finset (Σ _ : ℕ, ℕ) := (Finset.range (n + 1)).sigma (fun b => Finset.range b)
  have hS : S.card = (n + 1) * n / 2 := by
    simp only [S, Finset.card_sigma, Finset.card_range]
    exact Finset.sum_range_id (n + 1)
  refine ⟨S.image (fun p => intervalRoot n p.2 p.1), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hS]
    rintro ⟨b, a⟩ hp ⟨b', a'⟩ hp' h
    simp only [S, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio] at hp hp'
    have := intervalRoot_injective n a b a' b' hp.2 (by omega) hp'.2 (by omega) h
    obtain ⟨rfl, rfl⟩ := this
    rfl
  · intro x hx
    obtain ⟨⟨b, a⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [S, Finset.mem_sigma, Finset.mem_range] at hp
    exact ⟨isRoot_intervalRoot n a b hp.2 (by omega), intervalRoot_nonneg n a b⟩

/-- Every root of a positive definite graph is positive or negative. -/
@[kb "etingof2011" "Remark 5.18, p. 88"]
theorem isRoot_pos_or_neg {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (h : PosDefinite G)
    {x : Fin n → ℤ} (hx : IsRoot G x) : IsPositiveRoot G x ∨ IsNegativeRoot G x :=
  (isRoot_sign G h hx).imp (fun h => ⟨hx, h⟩) (fun h => ⟨hx, h⟩)

end UndergradKB.RepresentationTheory.Roots
