import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Rat
import UndergradKB.RepresentationTheory.GabrielConverseDefs
import UndergradKB.RepresentationTheory.DynkinForms
import UndergradKB.Common.Attr

/-! # Positivity of the Tits form forces a Dynkin diagram (Etingof et al., Problem 5.4(b), (c))

Let `Q` be a quiver on `Fin n` whose Tits form `q(x) = ∑ x_i² - ∑_{i → j} x_i x_j` is positive on the nonzero
natural vectors.

* `isDynkin_of_titsForm_pos`: if the underlying graph is connected, then `Q` has no loops, at most one arrow between
  two vertices, and the underlying graph is a Dynkin diagram.
* `isOrientation_of_card_le`: without loops and with at most one arrow between two vertices, `Q` is an orientation
  of its underlying graph.

The key analytic step is `posDefinite_of_form_pos`: if the integral form of a graph is positive on all nonzero
integer vectors, its real Cartan matrix is positive definite (positive semidefinite by density of the rational
vectors, and nondegenerate because a rational kernel vector would be an integer vector of form value zero).
-/

namespace UndergradKB.RepresentationTheory.Gabriel

open scoped Classical
open Roots QRep
open Matrix

noncomputable section

universe a

/-! ### From integer positivity to positive definiteness -/

section Pos

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem form_abs_le (x : Fin n → ℤ) : form G (fun i => |x i|) (fun i => |x i|) ≤ form G x x := by
  rw [form_eq_sum, form_eq_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : i = j
  · subst h
    have := abs_mul_abs_self (x i)
    rw [cartanMatrix_diag]
    linarith
  · have hc := cartanMatrix_offDiag_nonpos G h
    have h1 : x i * x j ≤ |x i| * |x j| := by
      rw [← abs_mul]; exact le_abs_self _
    have := mul_le_mul_of_nonpos_left h1 hc
    linarith

theorem form_pos_of_natPos
    (h : ∀ d : Fin n → ℕ, d ≠ 0 → 0 < form G (fun i => (d i : ℤ)) (fun i => (d i : ℤ)))
    {x : Fin n → ℤ} (hx : x ≠ 0) : 0 < form G x x := by
  have hd : (fun i => (x i).natAbs) ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  have := h _ hd
  refine lt_of_lt_of_le ?_ (form_abs_le x)
  simpa [Int.natCast_natAbs] using this

theorem posSemidef_of_form_pos (h : ∀ x : Fin n → ℤ, x ≠ 0 → 0 < form G x x) :
    (cartanReal G).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨cartanReal_isHermitian G, fun x => ?_⟩
  simp only [star_trivial]
  have hd : DenseRange (fun v : Fin n → ℚ => fun i => (v i : ℝ)) :=
    DenseRange.piMap (f := fun _ => ((↑) : ℚ → ℝ)) (fun _ => Rat.denseRange_cast)
  refine hd.induction_on x ?_ ?_
  · refine isClosed_le continuous_const ?_
    unfold dotProduct mulVec
    fun_prop
  · intro v
    set N : ℕ := ∏ i, (v i).den with hNdef
    have hN : 0 < N := Finset.prod_pos fun i _ => (v i).den_pos
    have hz : ∀ i, ∃ z : ℤ, (N : ℚ) * v i = z := by
      intro i
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i => (v i).den) (Finset.mem_univ i)
      refine ⟨m * (v i).num, ?_⟩
      have hm' : N = (v i).den * m := hm
      have h2 : (N : ℚ) = (v i).den * m := by exact_mod_cast hm'
      have h3 := Rat.mul_den_eq_num (v i)
      rw [h2]
      push_cast
      rw [← h3]
      ring
    choose z hz using hz
    have hzN : (fun i => (z i : ℝ)) = (N : ℝ) • (fun i => (v i : ℝ)) := by
      funext i
      have := congrArg (Rat.cast : ℚ → ℝ) (hz i)
      push_cast at this
      simp [← this]
    have hq : 0 ≤ (fun i => (z i : ℝ)) ⬝ᵥ (cartanReal G *ᵥ fun i => (z i : ℝ)) := by
      rw [← form_cast G z z]
      have : 0 ≤ form G z z := by
        by_cases hz0 : z = 0
        · subst hz0; simp [form]
        · exact (h z hz0).le
      exact_mod_cast this
    rw [hzN, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hq
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_pos_of_neg (mul_pos hNpos hNpos) hneg
    nlinarith

/-- If the integral form of a graph is positive on every nonzero integer vector, its real Cartan matrix is positive
definite. -/
theorem posDefinite_of_form_pos (h : ∀ x : Fin n → ℤ, x ≠ 0 → 0 < form G x x) : PosDefinite G := by
  have hs := posSemidef_of_form_pos h
  refine (hs.posDef_iff_det_ne_zero).2 ?_
  intro hdet
  have hz : (cartanMatrix G).det = 0 := by
    have h1 : ((cartanMatrix G).det : ℝ) = 0 := by
      rw [show ((cartanMatrix G).det : ℝ) = (Int.castRingHom ℝ) (cartanMatrix G).det from rfl,
        RingHom.map_det]
      exact hdet
    exact_mod_cast h1
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hz
  have := h v hv0
  rw [form, hv] at this
  simp at this

end Pos

/-! ### The Tits form of a quiver without loops and multiple edges -/

section Tits

variable {n : ℕ} [Q : Quiver.{a} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

theorem card_add_card_eq (hl : ∀ i : Fin n, IsEmpty (i ⟶ i))
    (h1 : ∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) (i j : Fin n) :
    ((Fintype.card (i ⟶ j) : ℤ) + Fintype.card (j ⟶ i)) = if (underlyingGraph Q).Adj i j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    have := hl i
    rw [if_neg (SimpleGraph.irrefl _)]
    simp
  · have hadj : (underlyingGraph Q).Adj i j ↔ (Nonempty (i ⟶ j) ∨ Nonempty (j ⟶ i)) :=
      ⟨fun h => h.2, fun h => ⟨hij, h⟩⟩
    have hle := h1 i j
    by_cases hA : (underlyingGraph Q).Adj i j
    · rw [if_pos hA]
      rcases hadj.1 hA with he | he
      · have := Fintype.card_pos_iff.2 he
        omega
      · have := Fintype.card_pos_iff.2 he
        omega
    · rw [if_neg hA]
      have h2 : ¬ Nonempty (i ⟶ j) := fun h => hA (hadj.2 (Or.inl h))
      have h3 : ¬ Nonempty (j ⟶ i) := fun h => hA (hadj.2 (Or.inr h))
      have c1 : Fintype.card (i ⟶ j) = 0 := Fintype.card_eq_zero_iff.2 (not_nonempty_iff.1 h2)
      have c2 : Fintype.card (j ⟶ i) = 0 := Fintype.card_eq_zero_iff.2 (not_nonempty_iff.1 h3)
      simp [c1, c2]

theorem two_mul_titsForm (hl : ∀ i : Fin n, IsEmpty (i ⟶ i))
    (h1 : ∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) (x : Fin n → ℤ) :
    2 * titsForm x = form (underlyingGraph Q) x x := by
  have e : ∑ i, ∑ j, (Fintype.card (i ⟶ j) : ℤ) * x i * x j =
      ∑ i, ∑ j, (Fintype.card (j ⟶ i) : ℤ) * x i * x j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hterm : ∀ i j, x i * cartanMatrix (underlyingGraph Q) i j * x j =
      (if i = j then 2 * (x i * x i) else 0) -
        ((Fintype.card (i ⟶ j) : ℤ) * x i * x j + (Fintype.card (j ⟶ i) : ℤ) * x i * x j) := by
    intro i j
    have hc := card_add_card_eq hl h1 i j
    rw [cartanMatrix_apply, ← hc]
    split_ifs with h
    · subst h; ring
    · ring
  have hB : ∑ i, 2 * (x i * x i) = 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [form_eq_sum]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold titsForm
  linarith

theorem form_pos_of_titsForm_pos (hl : ∀ i : Fin n, IsEmpty (i ⟶ i))
    (h1 : ∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1)
    (h : ∀ d : Fin n → ℕ, d ≠ 0 → 0 < titsForm (fun i => (d i : ℤ))) :
    ∀ x : Fin n → ℤ, x ≠ 0 → 0 < form (underlyingGraph Q) x x := by
  intro x hx
  refine form_pos_of_natPos (G := underlyingGraph Q) (fun d hd => ?_) hx
  have := h d hd
  have h2 := two_mul_titsForm hl h1 (fun i => (d i : ℤ))
  omega

/-- The Tits form of the basis vector `e_i`. -/
theorem titsForm_single (i : Fin n) :
    titsForm (fun l => if l = i then (1 : ℤ) else 0) = 1 - (Fintype.card (i ⟶ i) : ℤ) := by
  unfold titsForm
  simp [apply_ite]

/-- The Tits form of `e_i + e_j` for `i ≠ j`. -/
theorem titsForm_pair (i j : Fin n) (hij : i ≠ j) :
    titsForm (fun l => (if l = i then (1 : ℤ) else 0) + (if l = j then 1 else 0)) =
      2 - (Fintype.card (i ⟶ i) : ℤ) - Fintype.card (i ⟶ j) - Fintype.card (j ⟶ i) -
        Fintype.card (j ⟶ j) := by
  unfold titsForm
  have h1 : ∀ l, ((if l = i then (1 : ℤ) else 0) + (if l = j then 1 else 0)) ^ 2 =
      (if l = i then 1 else 0) + (if l = j then 1 else 0) := by
    intro l
    by_cases hi : l = i
    · have : l ≠ j := fun h => hij (hi.symm.trans h)
      simp [hi, hij]
    · by_cases hj : l = j
      · simp [hj, hij.symm]
      · simp [hi, hj]
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end Tits

variable {n : ℕ} [Q : Quiver.{a} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

/-- **Etingof et al., Problem 5.4(b), (c)**: if the Tits form is positive on the nonzero natural vectors and the
underlying graph is connected, then there are no loops, at most one arrow between two vertices, and the underlying
graph is a Dynkin diagram. -/
@[kb "etingof2011" "Problem 5.4, p. 80"]
theorem isDynkin_of_titsForm_pos (hc : (underlyingGraph Q).Connected)
    (h : ∀ d : Fin n → ℕ, d ≠ 0 → 0 < titsForm (fun i => (d i : ℤ))) :
    (∀ i : Fin n, IsEmpty (i ⟶ i)) ∧ (∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) ∧
      IsDynkin (underlyingGraph Q) := by
  have hl : ∀ i : Fin n, IsEmpty (i ⟶ i) := by
    intro i
    have h0 := h (fun l => if l = i then 1 else 0) (by
      intro h0
      have := congrFun h0 i
      simp at this)
    have h2 : titsForm (fun l => ((if l = i then 1 else 0 : ℕ) : ℤ)) =
        titsForm (fun l => if l = i then (1 : ℤ) else 0) := by
      congr 1
      funext l
      split_ifs <;> simp
    rw [h2, titsForm_single] at h0
    rw [← Fintype.card_eq_zero_iff]
    omega
  have h1 : ∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have := hl i
      simp
    · have h0 := h (fun l => (if l = i then 1 else 0) + (if l = j then 1 else 0)) (by
        intro h0
        have := congrFun h0 i
        simp [hij] at this)
      have h2 : titsForm (fun l => (((if l = i then 1 else 0) + (if l = j then 1 else 0) : ℕ) : ℤ)) =
          titsForm (fun l => (if l = i then (1 : ℤ) else 0) + (if l = j then 1 else 0)) := by
        congr 1
        funext l
        push_cast
        rfl
      rw [h2, titsForm_pair i j hij] at h0
      have := hl i
      have := hl j
      simp only [Fintype.card_eq_zero, Nat.cast_zero] at h0
      omega
  exact ⟨hl, h1, hc, posDefinite_of_form_pos (form_pos_of_titsForm_pos hl h1 h)⟩

/-- Without loops and with at most one arrow between two vertices, a quiver is an orientation of its underlying
graph. -/
theorem isOrientation_of_card_le (hl : ∀ i : Fin n, IsEmpty (i ⟶ i))
    (h1 : ∀ i j : Fin n, Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i) ≤ 1) :
    IsOrientation (underlyingGraph Q) Q where
  sub x y := by
    have := h1 x y
    exact Fintype.card_le_one_iff_subsingleton.1 (by omega)
  adj x y := by
    rintro ⟨e⟩
    refine ⟨?_, Or.inl ⟨e⟩⟩
    rintro rfl
    exact (hl x).false e
  adj' x y hxy := by
    rcases hxy.2 with he | he
    · exact Or.inl he
    · exact Or.inr he
  asymm x y := by
    rintro ⟨e⟩ ⟨e'⟩
    have := h1 x y
    have h2 := Fintype.card_pos_iff.2 ⟨e⟩
    have h3 := Fintype.card_pos_iff.2 ⟨e'⟩
    omega

end

end UndergradKB.RepresentationTheory.Gabriel
