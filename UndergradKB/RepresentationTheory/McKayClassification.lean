import UndergradKB.RepresentationTheory.McKayAffine
import UndergradKB.RepresentationTheory.AffineClassification
import UndergradKB.Common.Attr

/-! # The McKay graph is one of the affine diagrams (Etingof et al., Problem 5.5(c))

For a finite subgroup `G ≠ 1` of `SU(2)`, `McKayAffine.lean` shows that the McKay matrix `R` is symmetric with
natural entries, zero diagonal, connected, and that `2 I - R` is positive semidefinite but not definite. Here we
identify the graph using the classification of affine Dynkin diagrams (`classification_affine`):

* `mckayR_le_two`: off-diagonal multiplicities are at most `2` (the form at `e_i + e_j` is `4 - 2 r_ij`);
* `eq_or_eq_of_mckayR_eq_two`: a double edge `r_ij = 2` forces the form to vanish at `e_i + e_j`, so `i` and `j`
  are the only vertices: the graph is `Ã_1` (two vertices joined by two edges);
* otherwise all multiplicities are `0` or `1`, the McKay graph is a simple graph with the same matrix `2 I - R`,
  hence an affine Dynkin diagram, hence (`mckay_affine_classification`) a cycle `Ã_k`, `D̃_k`, `Ẽ_6`, `Ẽ_7` or
  `Ẽ_8`.
-/

namespace UndergradKB.RepresentationTheory

open Representation Module Matrix Roots

open scoped Classical

set_option linter.unusedSectionVars false

variable (G : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [Fintype G] [Invertible (Nat.card G : ℂ)]

theorem exists_natCast_mckayR (i j : irrChars ℂ G) : ∃ n : ℕ, mckayR G i j = n := by
  obtain ⟨n, hn⟩ := exists_natCast_mckay (natRep G) i j
  exact ⟨n, by simp [mckayR, hn]⟩

theorem mckayR_self (hG : G ≠ ⊥) (i : irrChars ℂ G) : mckayR G i i = 0 := by
  simp [mckayR, mckay_natRep_self_eq_zero_of_ne_bot G hG i]

theorem form_single_add_single {i j : irrChars ℂ G} (hij : i ≠ j) :
    (Pi.single i 1 + Pi.single j 1 : irrChars ℂ G → ℝ) ⬝ᵥ
        (mckayCartan G *ᵥ (Pi.single i 1 + Pi.single j 1)) =
      4 - mckayR G i i - mckayR G j j - mckayR G i j - mckayR G j i := by
  rw [add_dotProduct, single_dotProduct, single_dotProduct, mckayCartan_mulVec_apply,
    mckayCartan_mulVec_apply]
  simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, hij, Ne.symm hij]
  ring

/-- **Etingof et al., Problem 5.5(c)**: the McKay graph has at most two edges between two vertices. -/
theorem mckayR_le_two (hG : G ≠ ⊥) {i j : irrChars ℂ G} (hij : i ≠ j) : mckayR G i j ≤ 2 := by
  have h := mckayCartan_form_nonneg G (Pi.single i 1 + Pi.single j 1)
  rw [form_single_add_single G hij, mckayR_self G hG, mckayR_self G hG, mckayR_symm G j i] at h
  linarith

/-- A double edge `r_ij = 2` leaves no room for further vertices. -/
theorem eq_or_eq_of_mckayR_eq_two (hG : G ≠ ⊥) {i j : irrChars ℂ G} (hij : i ≠ j) (h2 : mckayR G i j = 2)
    (k : irrChars ℂ G) : k = i ∨ k = j := by
  have h := form_single_add_single G hij
  rw [mckayR_self G hG, mckayR_self G hG, mckayR_symm G j i, h2] at h
  obtain ⟨c, hc⟩ := mckayCartan_form_eq_zero G (by rw [h]; norm_num)
  by_contra hk
  push Not at hk
  have hk0 := congrFun hc k
  simp [hk.1, hk.2] at hk0
  have hd := (dimVec_pos G k).ne'
  have hc0 : c = 0 := by
    rcases hk0 with h | h
    · exact h
    · exact absurd h hd
  have hi := congrFun hc i
  simp [hij, hc0] at hi

/-- In the simply laced case, the McKay graph as a simple graph on `Fin N`. -/
noncomputable def mckaySimpleGraph {N : ℕ} (e : irrChars ℂ G ≃ Fin N) (hG : G ≠ ⊥) : SimpleGraph (Fin N) where
  Adj a b := mckayR G (e.symm a) (e.symm b) = 1
  symm := ⟨fun a b h => by rw [mckayR_symm]; exact h⟩
  loopless := ⟨fun a h => by rw [mckayR_self G hG] at h; norm_num at h⟩

theorem cartanReal_mckaySimpleGraph {N : ℕ} (e : irrChars ℂ G ≃ Fin N) (hG : G ≠ ⊥)
    (h01 : ∀ i j, mckayR G i j = 0 ∨ mckayR G i j = 1) :
    cartanReal (mckaySimpleGraph G e hG) = (mckayCartan G).submatrix e.symm e.symm := by
  ext a b
  show ((cartanMatrix _ a b : ℤ) : ℝ) = _
  rw [cartanMatrix_apply]
  simp only [Matrix.submatrix_apply, mckayCartan,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, e.symm.injective.eq_iff, mckaySimpleGraph]
  by_cases hab : a = b
  · subst hab
    simp [mckayR_self G hG]
  · simp only [hab, if_false]
    rcases h01 (e.symm a) (e.symm b) with h | h <;> simp [h]

theorem mckaySimpleGraph_connected {N : ℕ} (e : irrChars ℂ G ≃ Fin N) (hG : G ≠ ⊥)
    (h01 : ∀ i j, mckayR G i j = 0 ∨ mckayR G i j = 1) : (mckaySimpleGraph G e hG).Connected := by
  have hne : Nonempty (Fin N) := ⟨e trivIrrChar⟩
  refine ⟨fun a b => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have h := mckay_natRep_connected G (e.symm a) (e.symm b)
  have h' := Relation.ReflTransGen.lift (p := (mckaySimpleGraph G e hG).Adj) e (fun x y hxy => ?_) _ _ h
  · simpa [Function.onFun] using h'
  · show mckayR G (e.symm (e x)) (e.symm (e y)) = 1
    simp only [Equiv.symm_apply_apply]
    rcases h01 x y with h0 | h1
    · exact absurd (by rw [mckay_eq_re, h0]; simp) hxy
    · exact h1

/-- **Etingof et al., Problem 5.5(c)**: for a finite subgroup `G ≠ 1` of `SU(2)`, the McKay graph of the natural
2-dimensional representation is an affine Dynkin diagram from the book's list: either two vertices joined by a
double edge (`Ã_1`; then these are all the irreducible representations), or all multiplicities are `0` or `1` and
the graph (transported to `Fin N` along a numbering `e` of the irreducible characters) is isomorphic to a cycle
`Ã_k`, to `D̃_k`, or to `Ẽ_6`, `Ẽ_7`, `Ẽ_8`. -/
@[kb "etingof2011" "Problem 5.5, p. 80"]
theorem mckay_affine_classification (hG : G ≠ ⊥) :
    (∃ i j : irrChars ℂ G, i ≠ j ∧ mckay (natRep G) i j = 2 ∧ ∀ k, k = i ∨ k = j) ∨
    ∃ (N : ℕ) (e : irrChars ℂ G ≃ Fin N) (M : SimpleGraph (Fin N)),
      (∀ i j, mckay (natRep G) i j = 0 ∨ mckay (natRep G) i j = 1) ∧
      (∀ i j, M.Adj (e i) (e j) ↔ mckay (natRep G) i j = 1) ∧
      ((∃ k, Nonempty (affineCycle k ≃g M)) ∨ (∃ k, Nonempty (affineD k ≃g M)) ∨
        Nonempty (affineE6 ≃g M) ∨ Nonempty (affineE7 ≃g M) ∨
        Nonempty (graphOfCartan (CartanMatrix.E 9) ≃g M)) := by
  by_cases h2 : ∃ i j : irrChars ℂ G, i ≠ j ∧ mckayR G i j = 2
  · obtain ⟨i, j, hij, h⟩ := h2
    left
    refine ⟨i, j, hij, by rw [mckay_eq_re, h]; norm_num, eq_or_eq_of_mckayR_eq_two G hG hij h⟩
  right
  push Not at h2
  have h01 : ∀ i j, mckayR G i j = 0 ∨ mckayR G i j = 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij; left; exact mckayR_self G hG i
    obtain ⟨n, hn⟩ := exists_natCast_mckayR G i j
    have hle := mckayR_le_two G hG hij
    have hne := h2 i j hij
    rw [hn] at hle hne
    have : n ≤ 2 := by exact_mod_cast hle
    have : n ≠ 2 := fun h => hne (by rw [h]; norm_num)
    rw [hn]
    interval_cases n <;> simp_all
  let e := Fintype.equivFin (irrChars ℂ G)
  set M := mckaySimpleGraph G e hG with hM
  refine ⟨_, e, M, fun i j => ?_, fun i j => ?_, ?_⟩
  · rcases h01 i j with h | h
    · left; rw [mckay_eq_re, h]; simp
    · right; rw [mckay_eq_re, h]; simp
  · show mckayR G (e.symm (e i)) (e.symm (e j)) = 1 ↔ _
    simp only [Equiv.symm_apply_apply, mckay_eq_re]
    constructor
    · intro h; rw [h]; simp
    · intro h; exact_mod_cast h
  · have hc := mckaySimpleGraph_connected G e hG h01
    have hC := cartanReal_mckaySimpleGraph G e hG h01
    refine classification_affine M ⟨hc, ?_, fun hpd => ?_⟩
    · show (cartanReal M).PosSemidef
      rw [hC, posSemidef_submatrix_equiv]
      exact mckayCartan_posSemidef G
    · have hpd' : (cartanReal M).PosDef := hpd
      rw [hC] at hpd'
      have := hpd'.submatrix (e := e) e.injective
      simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at this
      exact mckayCartan_not_posDef G this

end UndergradKB.RepresentationTheory
