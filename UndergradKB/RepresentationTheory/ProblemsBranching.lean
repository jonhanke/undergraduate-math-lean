import UndergradKB.RepresentationTheory.FrobeniusTheorem
import UndergradKB.RepresentationTheory.Artin
import UndergradKB.Common.Attr

/-! # Problem 4.50: branching rules for the symmetric groups (Etingof et al.)

The restriction of the Specht module `V_μ` from `S_{m+1}` to `S_m` is the direct sum of the `V_λ` over the diagrams
`λ` obtained from `μ` by removing one box (`restrict_spechtChar`, on the level of characters).  The proof uses
the Frobenius character formula: for `σ ∈ S_m` the permutation `extPerm σ ∈ S_{m+1}` has one more fixed point, so
`cyclePoly` gains the factor `p₁ = x₁ + ⋯ + x_N` (`cyclePoly_extPerm`), and `[x^{μ+ρ}] (Δ p₁ P) =
∑_k [x^{μ+ρ-e_k}] (Δ P)`, where only the terms with `μ - e_k` a diagram survive (`frobChar_extPerm`).
-/

namespace UndergradKB.RepresentationTheory

open Finset
open scoped Classical

namespace Branching

variable {m N : ℕ}

/-- The embedding `S_m ⊂ S_{m+1}`: `σ` acts on `1, …, m` and fixes `0`. -/
noncomputable def extPerm (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, σ)

@[simp] theorem extPerm_zero (σ : Equiv.Perm (Fin m)) : extPerm σ 0 = 0 := by
  simp [extPerm, Equiv.Perm.decomposeFin_symm_apply_zero]

@[simp] theorem extPerm_succ (σ : Equiv.Perm (Fin m)) (i : Fin m) : extPerm σ i.succ = (σ i).succ := by
  simp [extPerm, Equiv.Perm.decomposeFin_symm_apply_succ]

theorem card_content_succ {N : ℕ} (f : Fin (m + 1) → Fin N) (j : Fin N) :
    (univ.filter fun a => f a = j).card =
      (if f 0 = j then 1 else 0) + (univ.filter fun a : Fin m => f a.succ = j).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]

/-- The number of invariant colourings of `Fin (m+1)` of content `α` with `f 0 = k`. -/
theorem card_fiber (σ : Equiv.Perm (Fin m)) (α : Fin N → ℕ) (k : Fin N) :
    (((univ : Finset (Fin (m + 1) → Fin N)).filter fun f =>
        f ∘ extPerm σ = f ∧ ∀ j, (univ.filter fun a => f a = j).card = α j).filter
        fun f => f 0 = k).card =
      if 1 ≤ α k then
        (univ.filter fun t : Fin m → Fin N => t ∘ σ = t ∧
          ∀ j, (univ.filter fun a => t a = j).card = α j - if k = j then 1 else 0).card
      else 0 := by
  split_ifs with hk
  · refine Finset.card_nbij' (fun f => fun a => f a.succ) (fun t => Fin.cons k t) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hf ⊢
      obtain ⟨⟨hinv, hcont⟩, h0⟩ := hf
      refine ⟨?_, fun j => ?_⟩
      · funext a
        have := congrFun hinv a.succ
        simpa using this
      · have h1 := hcont j
        rw [card_content_succ, h0] at h1
        by_cases hjk : k = j
        · subst hjk; simp at h1 ⊢; omega
        · simp [hjk] at h1 ⊢; omega
    · intro t ht
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ht ⊢
      obtain ⟨hinv, hcont⟩ := ht
      refine ⟨⟨?_, fun j => ?_⟩, by simp⟩
      · funext a
        refine Fin.cases ?_ (fun i => ?_) a
        · simp
        · simpa using congrFun hinv i
      · rw [card_content_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have h2 := hcont j
        by_cases hjk : k = j
        · subst hjk; simp at h2 ⊢; omega
        · simp [hjk] at h2 ⊢; omega
    · intro f hf
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hf
      funext a
      refine Fin.cases ?_ (fun i => ?_) a
      · simp [hf.2]
      · simp
    · intro t _
      funext a
      rfl
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨⟨_, hcont⟩, h0⟩ := hf
    have h1 := hcont k
    rw [card_content_succ, h0] at h1
    simp at h1
    omega

/-- A fixed point contributes a factor `p₁ = x₁ + ⋯ + x_N` to `cyclePoly`. -/
theorem cyclePoly_extPerm (σ : Equiv.Perm (Fin m)) :
    cyclePoly (m + 1) N (extPerm σ) = (∑ k, MvPolynomial.X k) * cyclePoly m N σ := by
  ext d
  rw [Finset.sum_mul, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_X_mul']
  have h1 := coeff_cyclePoly_eq_card (m + 1) N (extPerm σ) ⇑d
  rw [Finsupp.equivFunOnFinite_symm_coe] at h1
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := fun f : Fin (m + 1) → Fin N => f 0)
    (t := (univ : Finset (Fin N))) (fun _ _ => mem_univ _), Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [card_fiber]
  by_cases hk : 1 ≤ d k
  · have hks : k ∈ d.support := Finsupp.mem_support_iff.mpr (by omega)
    rw [if_pos hk, if_pos hks]
    have h2 := coeff_cyclePoly_eq_card m N σ ⇑(d - (Finsupp.single k 1 : Fin N →₀ ℕ))
    rw [Finsupp.equivFunOnFinite_symm_coe] at h2
    rw [h2]
    congr 3
    ext t
    simp [Finsupp.single_apply]
  · have hks : k ∉ d.support := by
      rw [Finsupp.mem_support_iff]; omega
    rw [if_neg hk, if_neg hks]
    simp

open FrobeniusDet

theorem coeff_delta_mul (σ : Equiv.Perm (Fin m)) (γ : Fin N →₀ ℕ) :
    (vandermondeDelta ℂ N * cyclePoly m N σ).coeff γ =
      ∑ τ : Equiv.Perm (Fin N), ((Equiv.Perm.sign τ : ℤ) : ℂ) *
        (if deltaExp τ ≤ γ then (cyclePoly m N σ).coeff (γ - deltaExp τ) else 0) := by
  rw [vandermondeDelta_eq_sum, Finset.sum_mul, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [smul_mul_assoc, Units.smul_def, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial_mul',
    zsmul_eq_mul]
  split_ifs <;> simp

/-- **Antisymmetry**: `Δ · P` has vanishing coefficient at any exponent with two equal entries. -/
theorem coeff_delta_mul_eq_zero (σ : Equiv.Perm (Fin m)) (γ : Fin N →₀ ℕ) (i j : Fin N) (hij : i ≠ j)
    (hγ : γ i = γ j) : (vandermondeDelta ℂ N * cyclePoly m N σ).coeff γ = 0 := by
  have hsym : ∀ k, γ (Equiv.swap i j k) = γ k := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [hγ]
    by_cases hkj : k = j
    · subst hkj; simp [hγ]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  set F : Equiv.Perm (Fin N) → ℂ := fun τ => ((Equiv.Perm.sign τ : ℤ) : ℂ) *
    (if deltaExp τ ≤ γ then (cyclePoly m N σ).coeff (γ - deltaExp τ) else 0) with hF
  have hS : (vandermondeDelta ℂ N * cyclePoly m N σ).coeff γ = ∑ τ, F τ := coeff_delta_mul σ γ
  have hdelta : ∀ (τ : Equiv.Perm (Fin N)) (k : Fin N),
      deltaExp (Equiv.swap i j * τ) k = deltaExp τ (Equiv.swap i j k) := by
    intro τ k
    rw [deltaExp_apply, deltaExp_apply]
    simp [Equiv.Perm.mul_def, Equiv.symm_swap]
  have hF2 : ∀ τ, F (Equiv.swap i j * τ) = - F τ := by
    intro τ
    have hle : deltaExp (Equiv.swap i j * τ) ≤ γ ↔ deltaExp τ ≤ γ := by
      simp only [Finsupp.le_def, hdelta]
      constructor
      · intro h k
        have := h (Equiv.swap i j k)
        simpa [hsym] using this
      · intro h k
        have := h (Equiv.swap i j k)
        rwa [hsym] at this
    have hco : (cyclePoly m N σ).coeff (γ - deltaExp (Equiv.swap i j * τ)) =
        (cyclePoly m N σ).coeff (γ - deltaExp τ) := by
      have h1 := coeff_cyclePoly_comp m N σ ⇑(γ - deltaExp τ) (Equiv.swap i j)
      rw [Finsupp.equivFunOnFinite_symm_coe] at h1
      rw [← h1]
      congr 1
      ext k
      simp [hdelta, hsym]
    simp only [hF]
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    by_cases hle' : deltaExp τ ≤ γ
    · rw [if_pos (hle.2 hle'), if_pos hle', hco]
      simp
    · rw [if_neg (fun h => hle' (hle.1 h)), if_neg hle']
      simp
  have hneg : ∑ τ, F τ = - ∑ τ, F τ := by
    calc ∑ τ, F τ = ∑ τ, F (Equiv.swap i j * τ) :=
          (Equiv.sum_comp (Equiv.mulLeft (Equiv.swap i j)) F).symm
      _ = - ∑ τ, F τ := by simp [hF2]
  rw [hS]
  linear_combination (1 / 2 : ℂ) * hneg

/-- Row `k` of `lam` has a removable box: it is nonempty and strictly longer than the next row. -/
def Removable (lam : Fin N → ℕ) (k : Fin N) : Prop :=
  1 ≤ lam k ∧ ∀ h : k.val + 1 < N, lam ⟨k.val + 1, h⟩ < lam k

theorem shiftExp_apply' (lam : Fin N → ℕ) (k : Fin N) : shiftExp lam k = lam k + (N - (k.val + 1)) := by
  simp [shiftExp, rhoExp, Fin.val_rev]

/-- **The key step**: adding a fixed point to a permutation turns `θ_λ` into the sum of the `θ_{λ - e_k}` over
the rows `k` with a removable box. -/
theorem frobChar_extPerm (lam : Fin N → ℕ) (hl : Antitone lam) (σ : Equiv.Perm (Fin m)) :
    frobChar (m + 1) N lam (extPerm σ) =
      ∑ k : Fin N, if Removable lam k then frobChar m N (Function.update lam k (lam k - 1)) σ else 0 := by
  unfold frobChar
  rw [cyclePoly_extPerm, mul_left_comm, Finset.sum_mul, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_X_mul']
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsk := shiftExp_apply' lam k
  by_cases hrem : Removable lam k
  · obtain ⟨h1, h2⟩ := hrem
    have hsupp : k ∈ (shiftExp lam).support := by
      rw [Finsupp.mem_support_iff, hsk]; omega
    rw [if_pos hsupp, if_pos ⟨h1, h2⟩]
    congr 2
    ext j
    by_cases hjk : j = k
    · subst hjk
      simp [Finsupp.single_apply, shiftExp_apply']
      omega
    · simp [Finsupp.single_apply, shiftExp_apply', Function.update_of_ne hjk, Ne.symm hjk]
  · rw [if_neg hrem]
    by_cases hsupp : k ∈ (shiftExp lam).support
    · rw [if_pos hsupp]
      have hs1 : 1 ≤ shiftExp lam k := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hsupp)
      have hkN := k.isLt
      obtain ⟨h, hj⟩ : ∃ h : k.val + 1 < N, shiftExp lam ⟨k.val + 1, h⟩ + 1 = shiftExp lam k := by
        by_cases h1 : 1 ≤ lam k
        · have : ¬ ∀ h : k.val + 1 < N, lam ⟨k.val + 1, h⟩ < lam k := fun h' => hrem ⟨h1, h'⟩
          push Not at this
          obtain ⟨h, hge⟩ := this
          have hle : lam ⟨k.val + 1, h⟩ ≤ lam k := hl (by simp [Fin.le_def])
          refine ⟨h, ?_⟩
          have e : ((⟨k.val + 1, h⟩ : Fin N) : ℕ) = k.val + 1 := rfl
          rw [hsk, shiftExp_apply']
          omega
        · have h0 : lam k = 0 := by omega
          rw [hsk, h0] at hs1
          have hk1 : k.val + 1 < N := by omega
          refine ⟨hk1, ?_⟩
          have hle : lam ⟨k.val + 1, hk1⟩ ≤ lam k := hl (by simp [Fin.le_def])
          have e : ((⟨k.val + 1, hk1⟩ : Fin N) : ℕ) = k.val + 1 := rfl
          rw [hsk, shiftExp_apply']
          omega
      have hne' : (⟨k.val + 1, h⟩ : Fin N) ≠ k := fun e => by
        have := congrArg Fin.val e
        simp at this
      apply coeff_delta_mul_eq_zero σ _ k ⟨k.val + 1, h⟩ hne'.symm
      simp [Finsupp.tsub_apply, Finsupp.single_apply, hne']
      omega
    · rw [if_neg hsupp]

/-! ### Removing a corner of a Young diagram -/

/-- `c` is a corner (a removable box) of the diagram `μ`. -/
def IsCorner (μ : YoungDiagram) (c : ℕ × ℕ) : Prop :=
  c ∈ μ ∧ (c.1 + 1, c.2) ∉ μ ∧ (c.1, c.2 + 1) ∉ μ

/-- The diagram obtained from `μ` by removing the corner `c`. -/
def removeCorner (μ : YoungDiagram) (c : ℕ × ℕ) (hc : IsCorner μ c) : YoungDiagram where
  cells := μ.cells.erase c
  isLowerSet := by
    intro p q hqp hp
    simp only [Finset.mem_coe, Finset.mem_erase, YoungDiagram.mem_cells] at hp ⊢
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    obtain ⟨h1, h2⟩ := Prod.mk_le_mk.mp hqp
    refine ⟨?_, μ.up_left_mem h1 h2 hp.2⟩
    intro hqc
    have e1 : q1 = c.1 := congrArg Prod.fst hqc
    have e2 : q2 = c.2 := congrArg Prod.snd hqc
    have hc21 := hc.2.1
    have hc22 := hc.2.2
    rw [← e1, ← e2] at hc21 hc22
    by_cases g1 : q1 + 1 ≤ p1
    · exact hc21 (μ.up_left_mem g1 h2 hp.2)
    · by_cases g2 : q2 + 1 ≤ p2
      · exact hc22 (μ.up_left_mem h1 g2 hp.2)
      · exact hp.1 (by rw [← hqc]; simp only [Prod.mk.injEq]; omega)

theorem mem_removeCorner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : IsCorner μ c) (x : ℕ × ℕ) :
    x ∈ removeCorner μ c hc ↔ x ∈ μ ∧ x ≠ c := by
  show x ∈ μ.cells.erase c ↔ _
  rw [Finset.mem_erase, YoungDiagram.mem_cells, and_comm]

theorem card_removeCorner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : IsCorner μ c) :
    (removeCorner μ c hc).card = μ.card - 1 :=
  Finset.card_erase_of_mem hc.1

theorem rowLen_corner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : IsCorner μ c) : μ.rowLen c.1 = c.2 + 1 := by
  have h1 := YoungDiagram.mem_iff_lt_rowLen.mp hc.1
  have h2 : ¬ c.2 + 1 < μ.rowLen c.1 := fun h =>
    hc.2.2 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
  omega

theorem rowLen_removeCorner {μ : YoungDiagram} {c : ℕ × ℕ} (hc : IsCorner μ c) (r : ℕ) :
    (removeCorner μ c hc).rowLen r = if r = c.1 then c.2 else μ.rowLen r := by
  have hrc := rowLen_corner hc
  have hmem : ∀ r j, (r, j) ∈ removeCorner μ c hc ↔ j < (removeCorner μ c hc).rowLen r :=
    fun r j => YoungDiagram.mem_iff_lt_rowLen
  have hmem' : ∀ r j, (r, j) ∈ removeCorner μ c hc ↔ j < μ.rowLen r ∧ (r, j) ≠ c := fun r j => by
    rw [mem_removeCorner, YoungDiagram.mem_iff_lt_rowLen]
  by_cases hr : r = c.1
  · rw [if_pos hr]
    subst hr
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have := (hmem _ _).mpr hlt
      rw [hmem'] at this
      exact this.2 rfl
    · by_cases h0 : c.2 = 0
      · omega
      · have : (c.1, c.2 - 1) ∈ removeCorner μ c hc := by
          rw [hmem']
          refine ⟨by omega, fun h => ?_⟩
          have := congrArg Prod.snd h
          simp at this
          omega
        have := (hmem _ _).mp this
        omega
  · rw [if_neg hr]
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have := (hmem _ _).mpr hlt
      rw [hmem'] at this
      omega
    · by_cases h0 : μ.rowLen r = 0
      · omega
      · have : (r, μ.rowLen r - 1) ∈ removeCorner μ c hc := by
          rw [hmem']
          exact ⟨by omega, fun h => hr (congrArg Prod.fst h)⟩
        have := (hmem _ _).mp this
        omega

theorem colLen_removeCorner_le {μ : YoungDiagram} {c : ℕ × ℕ} (hc : IsCorner μ c) :
    (removeCorner μ c hc).colLen 0 ≤ μ.colLen 0 := by
  by_contra hlt
  push Not at hlt
  have h : (μ.colLen 0, 0) ∈ removeCorner μ c hc := YoungDiagram.mem_iff_lt_colLen.mpr hlt
  rw [mem_removeCorner] at h
  exact absurd (YoungDiagram.mem_iff_lt_colLen.mp h.1) (lt_irrefl _)

/-- The diagram with `m` boxes obtained from `μ` (with `m + 1` boxes) by removing the corner `c`. -/
noncomputable def removeCornerDiag (μ : DiagramsOfSize (m + 1)) (c : ℕ × ℕ) (hc : IsCorner μ.1 c) :
    DiagramsOfSize m :=
  ⟨removeCorner μ.1 c hc, by rw [card_removeCorner hc, μ.2]; rfl⟩

noncomputable instance (μ : YoungDiagram) : Fintype {c : ℕ × ℕ // IsCorner μ c} :=
  Fintype.subtype (μ.cells.filter (IsCorner μ)) (fun c => by
    simp only [Finset.mem_filter, YoungDiagram.mem_cells]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩)

theorem rowLen_eq_zero_of_le {μ : YoungDiagram} {i : ℕ} (h : μ.colLen 0 ≤ i) : μ.rowLen i = 0 := by
  by_contra hne
  have : (i, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
  have := YoungDiagram.mem_iff_lt_colLen.mp this
  omega

theorem restrict_spechtChar_aux (μ : DiagramsOfSize (m + 1)) (hN : μ.1.colLen 0 ≤ N)
    (σ : Equiv.Perm (Fin m)) :
    (spechtChar (m + 1) μ).1 (extPerm σ) =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c}, (spechtChar m (removeCornerDiag μ c.1 c.2)).1 σ := by
  set lam : Fin N → ℕ := fun j => μ.1.rowLen j with hlam
  have hl : Antitone lam := fun i j hij => μ.1.rowLen_anti i j hij
  have hLHS : (spechtChar (m + 1) μ).1 (extPerm σ) = frobChar (m + 1) N lam (extPerm σ) :=
    congrFun (frobenius_character_formula μ hN) (extPerm σ)
  rw [hLHS, frobChar_extPerm lam hl σ, ← Finset.sum_filter]
  -- reindex over the corners
  have hcorner : ∀ k : Fin N, Removable lam k → IsCorner μ.1 (k.val, μ.1.rowLen k - 1) := by
    intro k hk
    obtain ⟨h1, h2⟩ := hk
    have h1' : 1 ≤ μ.1.rowLen k := h1
    refine ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by simp; omega), ?_, ?_⟩
    · rw [YoungDiagram.mem_iff_lt_rowLen]
      by_cases hk1 : k.val + 1 < N
      · have := h2 hk1
        simp only [hlam] at this
        simp only
        omega
      · have := rowLen_eq_zero_of_le (μ := μ.1) (i := k.val + 1) (by omega)
        simp only
        omega
    · rw [YoungDiagram.mem_iff_lt_rowLen]
      simp only
      omega
  refine Finset.sum_bij (fun k hk => ⟨(k.val, μ.1.rowLen k - 1), hcorner k (Finset.mem_filter.mp hk).2⟩)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k _ k' _ h
    have := congrArg (fun x : {c : ℕ × ℕ // IsCorner μ.1 c} => x.1.1) h
    exact Fin.ext this
  · rintro ⟨c, hc⟩ _
    have hrow := rowLen_corner hc
    have hc1 : c.1 < N := by
      have h0 : (c.1, 0) ∈ μ.1 := μ.1.up_left_mem le_rfl (Nat.zero_le _) hc.1
      have := YoungDiagram.mem_iff_lt_colLen.mp h0
      omega
    refine ⟨⟨c.1, hc1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · show 1 ≤ μ.1.rowLen c.1
      omega
    · intro h
      have : ¬ c.2 < μ.1.rowLen (c.1 + 1) := fun h' => hc.2.1 (YoungDiagram.mem_iff_lt_rowLen.mpr h')
      show μ.1.rowLen (c.1 + 1) < μ.1.rowLen c.1
      omega
    · apply Subtype.ext
      show (c.1, μ.1.rowLen c.1 - 1) = c
      rw [hrow]
      ext <;> simp
  · intro k hk
    have hkr := (Finset.mem_filter.mp hk).2
    have hc := hcorner k hkr
    simp only
    have hres := congrFun (frobenius_character_formula (removeCornerDiag μ _ hc)
      (le_trans (colLen_removeCorner_le hc) hN)) σ
    rw [hres]
    congr 1
    funext j
    show _ = (removeCorner μ.1 _ hc).rowLen j
    rw [rowLen_removeCorner hc]
    by_cases hjk : j = k
    · subst hjk; simp [hlam]
    · have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
      simp [hjk, this, hlam]

/-- **Etingof et al., Problem 4.50(a)** (character level): the character of the Specht module `V_μ` restricted to
`S_m ⊂ S_{m+1}` is the sum of the characters of `V_λ` over the diagrams `λ` obtained from `μ` by removing one box
(one for each corner of `μ`). -/
@[kb "etingof2011" "Problem 4.50, p. 63"]
theorem restrict_spechtChar (μ : DiagramsOfSize (m + 1)) (σ : Equiv.Perm (Fin m)) :
    (spechtChar (m + 1) μ).1 (extPerm σ) =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c}, (spechtChar m (removeCornerDiag μ c.1 c.2)).1 σ :=
  restrict_spechtChar_aux μ le_rfl σ

/-! ### Induction, by Frobenius reciprocity -/

/-- The embedding `S_m → S_{m+1}` as a group homomorphism. -/
noncomputable def extHom (m : ℕ) : Equiv.Perm (Fin m) →* Equiv.Perm (Fin (m + 1)) where
  toFun := extPerm
  map_one' := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_mul' σ τ := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem extHom_injective (m : ℕ) : Function.Injective (extHom m) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have := congrArg (fun p : Equiv.Perm (Fin (m + 1)) => p i.succ) h
  simpa [extHom] using this

/-- The subgroup `S_m ⊂ S_{m+1}`. -/
noncomputable def extSubgroup (m : ℕ) : Subgroup (Equiv.Perm (Fin (m + 1))) := (extHom m).range

/-- `S_m ≅ extSubgroup m`. -/
noncomputable def extIso (m : ℕ) : Equiv.Perm (Fin m) ≃* extSubgroup m :=
  MonoidHom.ofInjective (extHom_injective m)

theorem coe_extIso (σ : Equiv.Perm (Fin m)) : ((extIso m σ : extSubgroup m) : Equiv.Perm (Fin (m + 1))) =
    extPerm σ := rfl

/-- The class function of `S_{m+1}` induced from the character of the Specht module `V_λ` of `S_m`. -/
noncomputable def indSpecht (la : DiagramsOfSize m) : Equiv.Perm (Fin (m + 1)) → ℂ :=
  indClassFun (extSubgroup m) fun h => (spechtChar m la).1 ((extIso m).symm h)

/-- Frobenius reciprocity for the induced Specht character. -/
theorem pairing_indSpecht (la : DiagramsOfSize m) {φ : Equiv.Perm (Fin (m + 1)) → ℂ}
    (hφ : φ ∈ classFunctions ℂ (Equiv.Perm (Fin (m + 1)))) :
    pairing (indSpecht la) φ = pairing (spechtChar m la).1 (fun σ => φ (extPerm σ)) := by
  haveI : Fintype (extSubgroup m) := Fintype.ofFinite _
  unfold indSpecht
  rw [pairing_indClassFun _ _ hφ, pairing_apply, pairing_apply]
  have hcard : Nat.card (extSubgroup m) = Nat.card (Equiv.Perm (Fin m)) :=
    Nat.card_congr (extIso m).symm.toEquiv
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv (extIso m).symm.toEquiv _ _ (fun h => ?_)
  have hh : (h : Equiv.Perm (Fin (m + 1))) = extPerm ((extIso m).symm h) := by
    conv_lhs => rw [← (extIso m).apply_symm_apply h]
    rfl
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, Subgroup.coe_inv]
  rw [hh]
  have hinv : (extPerm ((extIso m).symm h))⁻¹ = extPerm ((extIso m).symm h)⁻¹ := by
    have := (extHom m).map_inv ((extIso m).symm h)
    exact this.symm
  rw [hinv]

theorem spechtChar_eq_iff {n : ℕ} (a b : DiagramsOfSize n) : (spechtChar n a).1 = (spechtChar n b).1 ↔ a = b :=
  ⟨fun h => (spechtChar_bijective n).1 (Subtype.ext h), fun h => by rw [h]⟩

/-- **Etingof et al., Problem 4.50(b)**, multiplicity form: the multiplicity of `V_μ` in the induced
representation `Ind_{S_m}^{S_{m+1}} V_λ` is the number of corners of `μ` whose removal gives `λ`. -/
@[kb "etingof2011" "Problem 4.50, p. 63"]
theorem pairing_indSpecht_spechtChar (la : DiagramsOfSize m) (μ : DiagramsOfSize (m + 1)) :
    pairing (indSpecht la) (spechtChar (m + 1) μ).1 =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c}, if removeCornerDiag μ c.1 c.2 = la then (1 : ℂ) else 0 := by
  rw [pairing_indSpecht la (mem_classFunctions_of_mem_irrChars _)]
  have hfun : (fun σ : Equiv.Perm (Fin m) => (spechtChar (m + 1) μ).1 (extPerm σ)) =
      ∑ c : {c : ℕ × ℕ // IsCorner μ.1 c}, (spechtChar m (removeCornerDiag μ c.1 c.2)).1 := by
    funext σ
    rw [restrict_spechtChar, Finset.sum_apply]
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pairing_irrChars (spechtChar m la).2 (spechtChar m _).2]
  by_cases h : removeCornerDiag μ c.1 c.2 = la
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h ((spechtChar_eq_iff _ _).mp h'.symm))]

theorem removeCorner_injective {μ : YoungDiagram} {c c' : ℕ × ℕ} (hc : IsCorner μ c) (hc' : IsCorner μ c')
    (h : removeCorner μ c hc = removeCorner μ c' hc') : c = c' := by
  by_contra hne
  have h1 : c ∈ removeCorner μ c' hc' := (mem_removeCorner hc' c).mpr ⟨hc.1, hne⟩
  rw [← h, mem_removeCorner] at h1
  exact h1.2 rfl

/-- **Etingof et al., Problem 4.50(b)**: the multiplicity of `V_μ` in `Ind_{S_m}^{S_{m+1}} V_λ` is `1` if `λ` is
obtained from `μ` by removing a box, and `0` otherwise. -/
@[kb "etingof2011" "Problem 4.50, p. 63"]
theorem pairing_indSpecht_spechtChar_eq (la : DiagramsOfSize m) (μ : DiagramsOfSize (m + 1)) :
    pairing (indSpecht la) (spechtChar (m + 1) μ).1 =
      if ∃ (c : ℕ × ℕ) (hc : IsCorner μ.1 c), removeCorner μ.1 c hc = la.1 then (1 : ℂ) else 0 := by
  rw [pairing_indSpecht_spechtChar, Finset.sum_boole]
  by_cases hex : ∃ (c : ℕ × ℕ) (hc : IsCorner μ.1 c), removeCorner μ.1 c hc = la.1
  · rw [if_pos hex]
    obtain ⟨c0, hc0, h0⟩ := hex
    have : (Finset.univ.filter fun c : {c : ℕ × ℕ // IsCorner μ.1 c} =>
        removeCornerDiag μ c.1 c.2 = la) = {⟨c0, hc0⟩} := by
      ext ⟨c, hc⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Subtype.mk.injEq]
      constructor
      · intro h
        exact removeCorner_injective hc hc0 ((congrArg Subtype.val h).trans h0.symm)
      · rintro rfl
        exact Subtype.ext h0
    rw [this]
    simp
  · rw [if_neg hex]
    have : (Finset.univ.filter fun c : {c : ℕ × ℕ // IsCorner μ.1 c} =>
        removeCornerDiag μ c.1 c.2 = la) = ∅ := by
      ext ⟨c, hc⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      exact hex ⟨c, hc, congrArg Subtype.val h⟩
    rw [this]
    simp

/-- **Etingof et al., Problem 4.50(b)** (character level): the class function induced from the character of `V_λ`
is the sum of the characters of the `V_μ` over the diagrams `μ` obtained from `λ` by adding one box. -/
@[kb "etingof2011" "Problem 4.50, p. 63"]
theorem induce_spechtChar [Fintype (DiagramsOfSize (m + 1))] (la : DiagramsOfSize m) :
    indSpecht la = ∑ μ : DiagramsOfSize (m + 1),
      (if ∃ (c : ℕ × ℕ) (hc : IsCorner μ.1 c), removeCorner μ.1 c hc = la.1 then (1 : ℂ) else 0) •
        (spechtChar (m + 1) μ).1 := by
  have hcl : indSpecht la ∈ classFunctions ℂ (Equiv.Perm (Fin (m + 1))) :=
    indClassFun_mem _ _
  rw [eq_sum_pairing_smul hcl]
  refine (Fintype.sum_equiv (Equiv.ofBijective (spechtChar (m + 1)) (spechtChar_bijective _)) _ _ ?_).symm
  intro μ
  show _ • (spechtChar (m + 1) μ).1 = pairing (indSpecht la) (spechtChar (m + 1) μ).1 •
    (spechtChar (m + 1) μ).1
  rw [pairing_indSpecht_spechtChar_eq]

end Branching

end UndergradKB.RepresentationTheory
