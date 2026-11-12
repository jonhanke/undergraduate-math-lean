import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Perm
import UndergradKB.RepresentationTheory.FrobeniusDefs
import UndergradKB.RepresentationTheory.CharacterTables
import UndergradKB.Common.Attr

/-! # Counting invariant colourings (steps towards the Frobenius character formula, Etingof et al., §4.16)

For a permutation `g` of `Fin n`, the coefficient of `x^α` in `cyclePoly n N g` is the number of colourings
`f : Fin n → Fin N` with `f ∘ g = f` and content `α`.  Consequences proved here:

* the coefficient is unchanged under `g ↦ g⁻¹` and under permuting the exponents (`coeff_cyclePoly_inv`,
  `coeff_cyclePoly_comp`);
* the orthogonality count `∑_g [x^α] P_g [x^β] P_g = n! · contingency α β`, by Burnside's lemma applied to the
  action of `S_n` on pairs of colourings, whose orbits correspond to contingency tables
  (`sum_coeff_cyclePoly_mul`);
* every coefficient function `g ↦ [x^d] P_g` is a virtual character of `S_n` (`coeffChar_mem_virtualChars`),
  being the permutation character on colourings of content `d`.
-/

namespace UndergradKB.RepresentationTheory

open Finset
open scoped Classical

/-! ### The coefficient counts invariant colourings -/

/-- The coefficient of `x^α` in `cyclePoly n N g` counts the `g`-invariant colourings of `Fin n` with `N` colours
having `α j` points of colour `j`. -/
theorem coeff_cyclePoly_eq_card' (n N : ℕ) (g : Equiv.Perm (Fin n)) (α : Fin N → ℕ) :
    (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) =
      ((univ.filter fun f : Fin n → Fin N =>
        f ∘ g = f ∧ ∀ j, colourContent f j = α j).card : ℂ) := by
  have h3 : cyclePoly n N g = ∏ q : CycleClasses g, MvPolynomial.psum (Fin N) ℂ (classSize g q) := by
    unfold cyclePoly
    rw [prod_classSize_eq g (fun m => MvPolynomial.psum (Fin N) ℂ m), Fintype.card_fin]
  rw [h3, coeff_prod_psum_classSize]
  convert rfl
  rfl

lemma colourContent_eq {n N : ℕ} (f : Fin n → Fin N) (j : Fin N) :
    colourContent f j = (univ.filter fun a => f a = j).card := by
  unfold colourContent
  convert rfl

/-- The coefficient of `x^α` in `cyclePoly n N g` counts the `g`-invariant colourings of `Fin n` with `N` colours
having `α j` points of colour `j`. -/
theorem coeff_cyclePoly_eq_card (n N : ℕ) (g : Equiv.Perm (Fin n)) (α : Fin N → ℕ) :
    (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) =
      ((univ.filter fun f : Fin n → Fin N =>
        f ∘ g = f ∧ ∀ j, (univ.filter fun a => f a = j).card = α j).card : ℂ) := by
  rw [coeff_cyclePoly_eq_card']
  simp only [colourContent_eq]

/-- Replacing `g` by its inverse does not change the coefficients of `cyclePoly`. -/
theorem coeff_cyclePoly_inv (n N : ℕ) (g : Equiv.Perm (Fin n)) (α : Fin N → ℕ) :
    (cyclePoly n N g⁻¹).coeff (Finsupp.equivFunOnFinite.symm α) =
      (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) := by
  rw [coeff_cyclePoly_eq_card', coeff_cyclePoly_eq_card']
  congr 2
  ext f
  simp only [mem_filter, mem_univ, true_and]
  have : f ∘ ⇑g⁻¹ = f ↔ f ∘ ⇑g = f := by
    constructor
    · intro h
      funext a
      have := congrFun h (g a)
      simpa using this.symm
    · intro h
      funext a
      have := congrFun h (g⁻¹ a)
      simpa using this.symm
  rw [this]

lemma colourContent_perm_comp {n N : ℕ} (π : Equiv.Perm (Fin N)) (f : Fin n → Fin N) (i : Fin N) :
    colourContent (π ∘ f) i = colourContent f (π.symm i) := by
  unfold colourContent
  congr 1
  ext a
  simp [Equiv.eq_symm_apply]

/-- Permuting the exponents by a permutation of the variables does not change the coefficients. -/
theorem coeff_cyclePoly_comp (n N : ℕ) (g : Equiv.Perm (Fin n)) (α : Fin N → ℕ)
    (π : Equiv.Perm (Fin N)) :
    (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm (α ∘ π)) =
      (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) := by
  rw [coeff_cyclePoly_eq_card', coeff_cyclePoly_eq_card']
  congr 1
  refine Nat.cast_inj.2 (Finset.card_nbij' (fun f => π ∘ f) (fun f => π.symm ∘ f) ?_ ?_ ?_ ?_)
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
    refine ⟨?_, fun j => ?_⟩
    · funext a
      have := congrFun hf.1 a
      simp only [Function.comp_apply] at this ⊢
      rw [this]
    · rw [colourContent_perm_comp, hf.2]
      simp
  · intro f hf
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
    refine ⟨?_, fun j => ?_⟩
    · funext a
      have := congrFun hf.1 a
      simp only [Function.comp_apply] at this ⊢
      rw [this]
    · rw [colourContent_perm_comp, hf.2]
      simp
  · intro f _
    funext a
    simp
  · intro f _
    funext a
    simp

/-! ### Colourings of a fixed content as an `S_n`-set -/

/-- The colourings `Fin n → Fin N` of content `c`. -/
noncomputable abbrev ColX (n N : ℕ) (c : Fin N → ℕ) : Type :=
  {f : Fin n → Fin N // ∀ j, colourContent f j = c j}

/-- `S_n` acts on the colourings of content `c` by precomposition with the inverse. -/
noncomputable instance (n N : ℕ) (c : Fin N → ℕ) : MulAction (Equiv.Perm (Fin n)) (ColX n N c) where
  smul g f := ⟨f.1 ∘ ⇑g⁻¹, fun j => by rw [colourContent_comp_perm]; exact f.2 j⟩
  one_smul f := by apply Subtype.ext; funext a; simp [HSMul.hSMul, SMul.smul]
  mul_smul g h f := by apply Subtype.ext; funext a; simp [HSMul.hSMul, SMul.smul, mul_inv_rev]

lemma ColX.smul_val {n N : ℕ} {c : Fin N → ℕ} (g : Equiv.Perm (Fin n)) (f : ColX n N c) :
    (g • f).1 = f.1 ∘ ⇑g⁻¹ := rfl

lemma ColX.smul_eq_iff {n N : ℕ} {c : Fin N → ℕ} (g : Equiv.Perm (Fin n)) (f : ColX n N c) :
    g • f = f ↔ f.1 ∘ ⇑g = f.1 := by
  rw [Subtype.ext_iff, ColX.smul_val]
  constructor
  · intro h
    funext a
    have := congrFun h (g a)
    simpa using this.symm
  · intro h
    funext a
    have := congrFun h (g⁻¹ a)
    simpa using this.symm

/-- The number of fixed points of `g` on the colourings of content `c`. -/
noncomputable def fixCard {n N : ℕ} (g : Equiv.Perm (Fin n)) (c : Fin N → ℕ) : ℕ :=
  (univ.filter fun x : ColX n N c => g • x = x).card

lemma fixCard_eq {n N : ℕ} (g : Equiv.Perm (Fin n)) (c : Fin N → ℕ) :
    fixCard g c = (univ.filter fun f : Fin n → Fin N =>
        f ∘ g = f ∧ ∀ j, colourContent f j = c j).card := by
  unfold fixCard
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨(ColX.smul_eq_iff g x).1 hx, x.2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    exact ⟨⟨f, hf.2⟩, by simpa using (ColX.smul_eq_iff g ⟨f, hf.2⟩).2 hf.1, rfl⟩

lemma natCard_fixedBy {n N : ℕ} (g : Equiv.Perm (Fin n)) (c : Fin N → ℕ) :
    Nat.card (MulAction.fixedBy (ColX n N c) g) = fixCard g c := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-! ### The permutation character -/

/-- Every coefficient function `g ↦ [x^d] cyclePoly n N g` is a virtual character of `S_n`: it is the character
of the permutation representation on the colourings of content `d`. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem coeffChar_mem_virtualChars (n N : ℕ) (d : Fin N →₀ ℕ) :
    (fun g : Equiv.Perm (Fin n) => (cyclePoly n N g).coeff d) ∈
      virtualChars ℂ (Equiv.Perm (Fin n)) := by
  have h := S4Table.character_mem_virtualChars
    (Representation.ofMulAction ℂ (Equiv.Perm (Fin n)) (ColX n N ⇑d))
  convert h using 1
  funext g
  have h1 : (cyclePoly n N g).coeff d = (fixCard g ⇑d : ℂ) := by
    have := coeff_cyclePoly_eq_card' n N g ⇑d
    rw [fixCard_eq]
    simpa using this
  rw [h1, Representation.character, LinearMap.trace_eq_matrix_trace ℂ
    (MonoidAlgebra.basis (ColX n N ⇑d) ℂ)]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Representation.ofMulAction_single,
    MonoidAlgebra.basis, Finsupp.single_apply, fixCard]

/-! ### The orthogonality count via Burnside's lemma -/

/-- The contingency table of a pair of colourings: entry `(i, j)` counts the points of colour `i` for the first
colouring and colour `j` for the second. -/
noncomputable def table {n N : ℕ} (f₁ f₂ : Fin n → Fin N) (i j : Fin N) : ℕ :=
  (univ.filter fun a => f₁ a = i ∧ f₂ a = j).card

lemma sum_table_right {n N : ℕ} (f₁ f₂ : Fin n → Fin N) (i : Fin N) :
    ∑ j, table f₁ f₂ i j = colourContent f₁ i := by
  unfold colourContent table
  rw [Finset.card_eq_sum_card_fiberwise (f := f₂) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  ext a
  simp

lemma sum_table_left {n N : ℕ} (f₁ f₂ : Fin n → Fin N) (j : Fin N) :
    ∑ i, table f₁ f₂ i j = colourContent f₂ j := by
  unfold colourContent table
  rw [Finset.card_eq_sum_card_fiberwise (f := f₁) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  ext a
  simp [and_comm]

lemma table_comp_perm {n N : ℕ} (f₁ f₂ : Fin n → Fin N) (σ : Equiv.Perm (Fin n)) (i j : Fin N) :
    table (f₁ ∘ σ) (f₂ ∘ σ) i j = table f₁ f₂ i j := by
  unfold table
  refine Finset.card_equiv σ (fun a => ?_)
  simp

lemma table_le {n N : ℕ} (f₁ f₂ : Fin n → Fin N) (i j : Fin N) :
    table f₁ f₂ i j ≤ colourContent f₁ i := by
  rw [← sum_table_right]
  exact Finset.single_le_sum (f := fun j => table f₁ f₂ i j) (fun _ _ => Nat.zero_le _) (mem_univ j)

/-- The table of a pair of colourings of contents `α`, `β`. -/
noncomputable def tableOf {n N : ℕ} {α β : Fin N → ℕ} (p : ColX n N α × ColX n N β) :
    Fin N → Fin N → ℕ := fun i j => table p.1.1 p.2.1 i j

lemma tableOf_smul {n N : ℕ} {α β : Fin N → ℕ} (g : Equiv.Perm (Fin n)) (p : ColX n N α × ColX n N β) :
    tableOf (g • p) = tableOf p := by
  funext i j
  exact table_comp_perm p.1.1 p.2.1 g⁻¹ i j

lemma exists_smul_eq_of_tableOf_eq {n N : ℕ} {α β : Fin N → ℕ} (p q : ColX n N α × ColX n N β)
    (h : tableOf p = tableOf q) : ∃ g : Equiv.Perm (Fin n), g • p = q := by
  have h' : ∀ x : Fin N × Fin N, colourContent (fun a => (p.1.1 a, p.2.1 a)) x =
      colourContent (fun a => (q.1.1 a, q.2.1 a)) x := by
    rintro ⟨i, j⟩
    have := congrFun (congrFun h i) j
    unfold tableOf table at this
    unfold colourContent
    simpa [Prod.ext_iff] using this
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq h'
  refine ⟨σ, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · funext a
    have h1 := (Prod.ext_iff.1 (congrFun hσ (σ⁻¹ a))).1
    simp at h1
    show p.1.1 (σ⁻¹ a) = q.1.1 a
    exact h1.symm
  · funext a
    have h1 := (Prod.ext_iff.1 (congrFun hσ (σ⁻¹ a))).2
    simp at h1
    show p.2.1 (σ⁻¹ a) = q.2.1 a
    exact h1.symm

lemma exists_table {n N : ℕ} (M : Fin N → Fin N → ℕ) (hM : ∑ i, ∑ j, M i j = n) :
    ∃ f₁ f₂ : Fin n → Fin N, ∀ i j, table f₁ f₂ i j = M i j := by
  let σ := Σ q : Fin N × Fin N, Fin (M q.1 q.2)
  have hc : Fintype.card (Fin n) = Fintype.card σ := by
    simp only [σ, Fintype.card_sigma, Fintype.card_fin, Fintype.sum_prod_type]
    exact hM.symm
  let e : Fin n ≃ σ := Fintype.equivOfCardEq hc
  refine ⟨fun a => (e a).1.1, fun a => (e a).1.2, fun i j => ?_⟩
  unfold table
  have h1 : (univ.filter fun a => (e a).1.1 = i ∧ (e a).1.2 = j).card =
      (univ.filter fun s : σ => s.1 = (i, j)).card := by
    refine Finset.card_equiv e (fun a => ?_)
    simp [Prod.ext_iff]
  rw [h1, ← Fintype.card_subtype, Fintype.card_congr (Equiv.sigmaSubtype (β := fun q : Fin N × Fin N =>
    Fin (M q.1 q.2)) (i, j)), Fintype.card_fin]

lemma card_orbits {n N : ℕ} (α β : Fin N → ℕ) (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (ColX n N α × ColX n N β))) =
      contingency α β := by
  let Φ : Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (ColX n N α × ColX n N β)) →
      (Fin N → Fin N → ℕ) :=
    Quotient.lift tableOf (fun p q hpq => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hpq)
      rw [← hg, tableOf_smul])
  have hinj : Function.Injective Φ := by
    intro a b
    induction a using Quotient.inductionOn with | _ p => ?_
    induction b using Quotient.inductionOn with | _ q => ?_
    intro h
    obtain ⟨g, hg⟩ := exists_smul_eq_of_tableOf_eq p q h
    apply Quotient.sound
    refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨g⁻¹, ?_⟩)
    rw [← hg, inv_smul_smul]
  have hrange : Set.range Φ = ↑((Fintype.piFinset fun _ : Fin N => Fintype.piFinset fun _ : Fin N =>
      Finset.range (∑ i, α i + 1)).filter
        fun M : Fin N → Fin N → ℕ => (∀ i, ∑ j, M i j = α i) ∧ ∀ j, ∑ i, M i j = β j) := by
    ext M
    simp only [Set.mem_range, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      induction a using Quotient.inductionOn with | _ p => ?_
      show (∀ i j, tableOf p i j < _) ∧ _
      refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
      · have h1 : tableOf p i j ≤ α i := by
          have := table_le p.1.1 p.2.1 i j
          rwa [p.1.2 i] at this
        have h2 : α i ≤ ∑ i, α i :=
          Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (mem_univ i)
        omega
      · exact (sum_table_right p.1.1 p.2.1 i).trans (p.1.2 i)
      · exact (sum_table_left p.1.1 p.2.1 j).trans (p.2.2 j)
    · rintro ⟨-, h1, h2⟩
      obtain ⟨f₁, f₂, hf⟩ := exists_table M (by simp only [h1]; exact hα)
      have c1 : ∀ i, colourContent f₁ i = α i := fun i => by
        rw [← sum_table_right f₁ f₂]; simp only [hf]; exact h1 i
      have c2 : ∀ j, colourContent f₂ j = β j := fun j => by
        rw [← sum_table_left f₁ f₂]; simp only [hf]; exact h2 j
      refine ⟨Quotient.mk _ (⟨f₁, c1⟩, ⟨f₂, c2⟩), ?_⟩
      funext i j
      exact hf i j
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.ofInjective Φ hinj), hrange,
    Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rfl

lemma natCard_fixedBy_prod {n N : ℕ} (g : Equiv.Perm (Fin n)) (α β : Fin N → ℕ) :
    Nat.card (MulAction.fixedBy (ColX n N α × ColX n N β) g) = fixCard g α * fixCard g β := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (univ.filter fun x : ColX n N α × ColX n N β => x ∈ MulAction.fixedBy _ g) =
      (univ.filter fun x : ColX n N α => g • x = x) ×ˢ (univ.filter fun y : ColX n N β => g • y = y) := by
    ext ⟨x, y⟩
    simp [MulAction.mem_fixedBy, Prod.ext_iff]
  rw [this, Finset.card_product]
  rfl

lemma coeff_eq_fixCard (n N : ℕ) (g : Equiv.Perm (Fin n)) (α : Fin N → ℕ) :
    (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) = (fixCard g α : ℂ) := by
  rw [coeff_cyclePoly_eq_card', fixCard_eq]

/-- Orthogonality count: if `α` and `β` both sum to `n`, then
`∑_g [x^α] P_g · [x^β] P_g = n! · (number of contingency tables with row sums α and column sums β)`.  The
left side counts pairs of colourings fixed by `g`; Burnside's lemma turns it into `n!` times the number of orbits
of `S_n` on pairs, and the orbits are the contingency tables. -/
@[kb "etingof2011" "Theorem 4.47, p. 61"]
theorem sum_coeff_cyclePoly_mul (n N : ℕ) (α β : Fin N → ℕ) (hα : ∑ i, α i = n) (hβ : ∑ i, β i = n) :
    ∑ g : Equiv.Perm (Fin n), (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm α) *
        (cyclePoly n N g).coeff (Finsupp.equivFunOnFinite.symm β) =
      (n.factorial : ℂ) * contingency α β := by
  have hB : ∑ g : Equiv.Perm (Fin n), Fintype.card (MulAction.fixedBy (ColX n N α × ColX n N β) g) =
      Fintype.card (Quotient (MulAction.orbitRel (Equiv.Perm (Fin n)) (ColX n N α × ColX n N β))) *
        Fintype.card (Equiv.Perm (Fin n)) :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
  have hterm : ∀ g : Equiv.Perm (Fin n),
      Fintype.card (MulAction.fixedBy (ColX n N α × ColX n N β) g) = fixCard g α * fixCard g β := fun g => by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_fixedBy_prod g α β
  simp only [hterm, card_orbits α β hα hβ, Fintype.card_perm, Fintype.card_fin] at hB
  have hC := congrArg (fun m : ℕ => (m : ℂ)) hB
  simp only [Nat.cast_sum, Nat.cast_mul] at hC
  simp only [coeff_eq_fixCard]
  rw [hC, mul_comm]

end UndergradKB.RepresentationTheory
