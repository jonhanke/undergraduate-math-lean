import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Fintype.Sort
import UndergradKB.Common.Attr

/-! # Strings, Jordan bases and Jordan form

Axler 8.44-8.46, Hefferon Five.III.2 and Five.IV.2.
-/

open Module Set Submodule

namespace UndergradKB.LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The family `(j, i) ↦ N^j (v i)` of a collection of strings. -/
def strFam (N : Module.End K V) {ι : Type*} (m : ι → ℕ) (v : ι → V) :
    (Σ i, Fin (m i + 1)) → V := fun x => (N ^ (x.2 : ℕ)) (v x.1)

section chain

variable (N : Module.End K V)

lemma pow_apply_eq_zero_of_ge {u : V} {m : ℕ} (hz : (N ^ (m + 1)) u = 0) {n : ℕ}
    (hn : m + 1 ≤ n) : (N ^ n) u = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, pow_add, mul_apply_eq_comp, hz, map_zero]

/-- Key computation: if a combination of the string `u, N u, ..., N^m u` is killed by `φ ∘ N^k`
for all `k ≤ m`, all its coefficients vanish. -/
lemma chain_coeff_zero {u : V} {m : ℕ} (hz : (N ^ (m + 1)) u = 0) (φ : Module.Dual K V)
    (hφ : φ ((N ^ m) u) ≠ 0) (c : Fin (m + 1) → K)
    (h : ∀ k : ℕ, k ≤ m → φ ((N ^ k) (∑ j, c j • (N ^ (j : ℕ)) u)) = 0) : c = 0 := by
  have key : ∀ d : ℕ, d ≤ m + 1 → ∀ i : Fin (m + 1), (i : ℕ) < d → c i = 0 := by
    intro d
    induction d with
    | zero => intro _ i hi; omega
    | succ d ih =>
      intro hd i hi
      have hdm : d < m + 1 := hd
      have hprev := ih (by omega)
      have h1 := h (m - d) (by omega)
      rw [map_sum, map_sum, Finset.sum_eq_single (⟨d, hdm⟩ : Fin (m + 1))] at h1
      · simp only [map_smul, ← mul_apply_eq_comp, ← pow_add, smul_eq_mul] at h1
        have : m - d + d = m := by omega
        rw [this] at h1
        have hcd : c ⟨d, hdm⟩ = 0 := by
          rcases mul_eq_zero.mp h1 with h2 | h2
          · exact h2
          · exact absurd h2 hφ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact hprev i hlt
        · have : i = ⟨d, hdm⟩ := Fin.ext heq
          rw [this]; exact hcd
      · intro b _ hb
        rcases lt_or_gt_of_ne (fun e => hb (Fin.ext e)) with hlt | hgt
        · have := hprev b hlt
          simp [this]
        · have hz' : (N ^ (m - d + (b : ℕ))) u = 0 :=
            pow_apply_eq_zero_of_ge N hz (by simp only at hgt; omega)
          simp [map_smul, ← mul_apply_eq_comp, ← pow_add, hz']
      · intro hn; exact absurd (Finset.mem_univ _) hn
  funext i
  exact key (m + 1) le_rfl i i.2

lemma exists_dual_apply_ne_zero {x : V} (hx : x ≠ 0) : ∃ φ : Module.Dual K V, φ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hx ((Module.forall_dual_apply_eq_zero_iff (R := K) x).mp hcon)

/-- Axler 8A.2 in the form with `m + 1` vectors. -/
lemma chain_linearIndependent {u : V} {m : ℕ} (hne : (N ^ m) u ≠ 0) (hz : (N ^ (m + 1)) u = 0) :
    LinearIndependent K (fun j : Fin (m + 1) => (N ^ (j : ℕ)) u) := by
  obtain ⟨φ, hφ⟩ := exists_dual_apply_ne_zero (K := K) hne
  rw [Fintype.linearIndependent_iff]
  intro c hc
  intro i
  exact congrFun (chain_coeff_zero N hz φ hφ c (by intro k _; rw [hc]; simp)) i

end chain

section strings

variable [FiniteDimensional K V] (N : Module.End K V)

/-- `W` is spanned by a collection of `N`-strings, i.e. by a family `N^j (v i)`, `j ≤ m i`, that is
linearly independent with `N^(m i + 1) (v i) = 0`. -/
def HasStrings (W : Submodule K V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (v : ι → V), (∀ i, v i ∈ W) ∧
    (∀ i, (N ^ (m i + 1)) (v i) = 0) ∧ LinearIndependent K (strFam N m v) ∧
    span K (range (strFam N m v)) = W

/-- Lengths for the strings of `Option ι`. -/
def optM {ι : Type} (m0 : ℕ) (m : ι → ℕ) : Option ι → ℕ
  | none => m0
  | some i => m i

/-- Generators for the strings of `Option ι`. -/
def optV {ι : Type} (u : V) (v : ι → V) : Option ι → V
  | none => u
  | some i => v i

/-- Splitting the sigma type over `Option ι`. -/
def optEquiv {ι : Type} (m0 : ℕ) (m : ι → ℕ) :
    (Σ i : Option ι, Fin (optM m0 m i + 1)) ≃ Fin (m0 + 1) ⊕ Σ i : ι, Fin (m i + 1) where
  toFun x := match x with
    | ⟨none, j⟩ => Sum.inl j
    | ⟨some i, j⟩ => Sum.inr ⟨i, j⟩
  invFun := Sum.elim (fun j => ⟨none, j⟩) (fun x => ⟨some x.1, x.2⟩)
  left_inv := by rintro ⟨_ | i, j⟩ <;> rfl
  right_inv := by rintro (j | ⟨i, j⟩) <;> rfl

omit [FiniteDimensional K V] in
lemma strFam_option {ι : Type} (m0 : ℕ) (m : ι → ℕ) (u : V) (v : ι → V) :
    strFam N (optM m0 m) (optV u v) =
      Sum.elim (fun j : Fin (m0 + 1) => (N ^ (j : ℕ)) u) (strFam N m v) ∘ optEquiv m0 m := by
  funext ⟨o, j⟩
  cases o <;> rfl

omit [FiniteDimensional K V] in
lemma hasStrings_bot : HasStrings N (⊥ : Submodule K V) := by
  refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, by simp, by simp, ?_, ?_⟩
  · exact linearIndependent_empty_type
  · simp

omit [FiniteDimensional K V] in
lemma pow_apply_mem {W : Submodule K V} (hW : ∀ x ∈ W, N x ∈ W) (k : ℕ) :
    ∀ x ∈ W, (N ^ k) x ∈ W := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; rw [pow_succ', mul_apply_eq_comp]; exact hW _ (ih x hx)

/-- Axler's induction (8.45): an operator that is nilpotent on an invariant subspace `W`
has `W` spanned by strings. -/
theorem hasStrings_of_nilpotent_on :
    ∀ (n : ℕ) (W : Submodule K V), finrank K W = n → (∀ x ∈ W, N x ∈ W) →
      (∃ k, ∀ x ∈ W, (N ^ k) x = 0) → HasStrings N W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hW hnil
  classical
  by_cases hbot : W = ⊥
  · rw [hbot]; exact hasStrings_bot N
  obtain ⟨n0, hn0, hmin⟩ : ∃ n0, (∀ x ∈ W, (N ^ n0) x = 0) ∧
      ∀ k < n0, ¬ ∀ x ∈ W, (N ^ k) x = 0 :=
    ⟨Nat.find hnil, Nat.find_spec hnil, fun k hk => Nat.find_min hnil hk⟩
  have hn0pos : 0 < n0 := by
    by_contra h0
    have h00 : n0 = 0 := by omega
    apply hbot
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := hn0 x hx
    rw [h00] at this
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, n0 = m + 1 := ⟨n0 - 1, by omega⟩
  obtain ⟨u, hu, hune⟩ : ∃ u ∈ W, (N ^ m) u ≠ 0 := by
    have := hmin m (by omega)
    push Not at this
    exact this
  have hz : (N ^ (m + 1)) u = 0 := hm ▸ hn0 u hu
  set cf : Fin (m + 1) → V := fun j => (N ^ (j : ℕ)) u with hcf
  have hcfli : LinearIndependent K cf := chain_linearIndependent N hune hz
  set U : Submodule K V := span K (range cf) with hUdef
  have hU_le : U ≤ W := by
    rw [hUdef, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact pow_apply_mem N hW j u hu
  obtain ⟨φ, hφ⟩ := exists_dual_apply_ne_zero (K := K) hune
  let S : V →ₗ[K] (Fin (m + 1) → K) := LinearMap.pi (fun k => φ ∘ₗ (N ^ (k : ℕ)))
  have hS : ∀ x k, S x k = φ ((N ^ (k : ℕ)) x) := fun _ _ => rfl
  set W' : Submodule K V := W ⊓ LinearMap.ker S with hW'def
  have hW'inv : ∀ x ∈ W', N x ∈ W' := by
    intro x hx
    have hxW : x ∈ W := hx.1
    have hxk : S x = 0 := LinearMap.mem_ker.mp hx.2
    refine ⟨hW x hxW, LinearMap.mem_ker.mpr ?_⟩
    funext k
    rw [hS, ← mul_apply_eq_comp, ← pow_succ]
    by_cases hk : (k : ℕ) < m
    · have := congrFun hxk ⟨k + 1, by omega⟩
      rw [hS] at this
      simpa using this
    · have hkm : (k : ℕ) = m := by omega
      rw [hkm]
      have := hn0 x hxW
      rw [hm] at this
      rw [this]; simp
  have hdisj : Disjoint U W' := by
    rw [Submodule.disjoint_def]
    intro x hxU hxW'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hxU
    have hc : c = 0 := by
      apply chain_coeff_zero N hz φ hφ c
      intro k hk
      have := congrFun (LinearMap.mem_ker.mp hxW'.2) ⟨k, by omega⟩
      rw [hS] at this
      simpa using this
    simp [hc]
  have hdim : finrank K W ≤ finrank K U + finrank K W' := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (S.domRestrict W)
    have h2 : finrank K (LinearMap.range (S.domRestrict W)) ≤ m + 1 := by
      refine (Submodule.finrank_le _).trans ?_
      simp
    have h3 : (LinearMap.ker (S.domRestrict W)).map W.subtype = W' := by
      ext x
      constructor
      · rintro ⟨⟨y, hyW⟩, hy, rfl⟩
        exact ⟨hyW, hy⟩
      · rintro ⟨hxW, hxk⟩
        exact ⟨⟨x, hxW⟩, hxk, rfl⟩
    have h4 : finrank K U = m + 1 := by
      rw [hUdef, finrank_span_eq_card hcfli]; simp
    have h5 := Submodule.finrank_map_subtype_eq W (LinearMap.ker (S.domRestrict W))
    rw [h3] at h5
    omega
  have hsup : finrank K ↥(U ⊔ W') = finrank K U + finrank K W' := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U W'
    rw [disjoint_iff.mp hdisj] at this
    simpa using this
  have hUW : U ⊔ W' = W := by
    apply Submodule.eq_of_le_of_finrank_le (sup_le hU_le inf_le_left)
    exact hdim.trans hsup.ge
  have hU1 : finrank K U = m + 1 := by
    rw [hUdef, finrank_span_eq_card hcfli]; simp
  have hlt : finrank K W' < n := by
    have h1 : finrank K ↥(U ⊔ W') = n := by rw [hUW]; exact hWn
    have h2 : finrank K ↥W' < finrank K ↥(U ⊔ W') := by rw [hsup, hU1]; omega
    exact lt_of_lt_of_eq h2 h1
  obtain ⟨ι, _, m', v', hvW', hz', hli', hsp'⟩ :=
    ih _ hlt W' rfl hW'inv ⟨n0, fun x hx => hn0 x hx.1⟩
  refine ⟨Option ι, inferInstance, optM m m', optV u v', ?_, ?_, ?_, ?_⟩
  · intro o
    cases o with
    | none => exact hu
    | some i => exact (hvW' i).1
  · intro o
    cases o with
    | none => exact hz
    | some i => exact hz' i
  · rw [strFam_option, linearIndependent_equiv]
    refine LinearIndependent.sum_type hcfli hli' ?_
    rw [hsp']
    exact hdisj
  · rw [strFam_option, Function.Surjective.range_comp (optEquiv m m').surjective,
      Set.Sum.elim_range, Submodule.span_union, hsp']
    exact hUW

/-- Reindexing the strings by `Fin k`. -/
theorem hasStrings_fin {N : Module.End K V} {W : Submodule K V} (h : HasStrings N W) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (v : Fin k → V), (∀ i, v i ∈ W) ∧
      (∀ i, (N ^ (m i + 1)) (v i) = 0) ∧ LinearIndependent K (strFam N m v) ∧
      span K (range (strFam N m v)) = W := by
  obtain ⟨ι, _, m, v, hvW, hz, hli, hsp⟩ := h
  let e := Fintype.equivFin ι
  let g : (Σ a : Fin (Fintype.card ι), Fin (m (e.symm a) + 1)) ≃ Σ a : ι, Fin (m a + 1) :=
    Equiv.sigmaCongrLeft (β := fun a => Fin (m a + 1)) e.symm
  have hfam : strFam N (m ∘ e.symm) (v ∘ e.symm) = strFam N m v ∘ g := rfl
  refine ⟨Fintype.card ι, m ∘ e.symm, v ∘ e.symm, fun i => hvW _, fun i => hz _, ?_, ?_⟩
  · rw [hfam, linearIndependent_equiv]; exact hli
  · rw [hfam, Function.Surjective.range_comp g.surjective]; exact hsp

/-- A nilpotent operator has a basis made of strings `v_i, N v_i, ..., N^(m_i) v_i`
(the data of Axler Exercise 8C.9). -/
theorem exists_string_basis {N : Module.End K V} (hN : ∃ k, N ^ k = 0) :
    ∃ (k : ℕ) (m : Fin k → ℕ) (v : Fin k → V) (b : Module.Basis (Σ i : Fin k, Fin (m i + 1)) K V),
      (∀ x, b x = (N ^ (x.2 : ℕ)) (v x.1)) ∧ ∀ i, (N ^ (m i + 1)) (v i) = 0 := by
  obtain ⟨k, hk⟩ := hN
  have h := hasStrings_of_nilpotent_on N _ (⊤ : Submodule K V) rfl (fun _ _ => trivial)
    ⟨k, fun x _ => by rw [hk]; rfl⟩
  obtain ⟨k, m, v, -, hz, hli, hsp⟩ := hasStrings_fin h
  refine ⟨k, m, v, Module.Basis.mk hli (by rw [hsp]), fun x => ?_, hz⟩
  rw [Module.Basis.coe_mk]; rfl

end strings

section jordanMatrix

variable {p : ℕ} {n : Fin p → ℕ}

/-- The Jordan block of Axler 8.44: size `n`, constant `a` on the diagonal, `1` directly above it,
zeros elsewhere. -/
def jordanBlock (a : K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r c => if r = c then a else if (r : ℕ) + 1 = c then 1 else 0

/-- Axler Definition 8.44: a basis, indexed by the concatenation of `p` blocks of sizes
`n 0, ..., n (p-1)`, in which `T` has block diagonal matrix with Jordan blocks (eigenvalue `lam i`
on block `i`). -/
def IsJordanBasis (T : Module.End K V) (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V) : Prop :=
  ∃ lam : Fin p → K, LinearMap.toMatrix b b T =
    Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i))

lemma jordan_entry (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V) (lam : Fin p → K)
    (i : Fin p) (r : Fin (n i)) (k : Fin p) (s : Fin (n k)) :
    (b.repr (lam i • b ⟨i, r⟩ +
      (if h : 0 < (r : ℕ) then b ⟨i, ⟨r - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.2⟩⟩ else 0)))
        ⟨k, s⟩ =
    Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i)) ⟨k, s⟩ ⟨i, r⟩ := by
  by_cases hk : k = i
  · subst hk
    rw [Matrix.blockDiagonal'_apply_eq]
    by_cases hr : 0 < (r : ℕ)
    · simp only [hr, dite_true, map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.single_apply, jordanBlock, Matrix.of_apply, Sigma.mk.injEq,
        heq_eq_eq, true_and, smul_eq_mul]
      simp only [Fin.ext_iff, Fin.val_mk]
      by_cases h1 : (r : ℕ) = s
      · have h2 : ¬ ((r : ℕ) - 1 = s) := by omega
        have h3 : (s : ℕ) = r := h1.symm
        rw [if_pos h1, if_neg h2, if_pos h3]; simp
      · have h3 : ¬ (s : ℕ) = r := fun e => h1 e.symm
        by_cases h2 : (r : ℕ) - 1 = s
        · have h4 : (s : ℕ) + 1 = r := by omega
          simp [h1, h2, h3, h4]
        · have h4 : ¬ (s : ℕ) + 1 = r := by omega
          simp [h1, h2, h3, h4]
    · simp only [hr, dite_false, add_zero, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, jordanBlock, Matrix.of_apply, Sigma.mk.injEq, heq_eq_eq, true_and,
        smul_eq_mul]
      simp only [Fin.ext_iff]
      by_cases h1 : (r : ℕ) = s
      · rw [if_pos h1, if_pos h1.symm]; simp
      · have h3 : ¬ (s : ℕ) = r := fun e => h1 e.symm
        have h4 : ¬ (s : ℕ) + 1 = r := by omega
        simp [h1, h3, h4]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hk]
    have h1 : (⟨k, s⟩ : Σ i : Fin p, Fin (n i)) ≠ ⟨i, r⟩ := fun e => hk (by cases e; rfl)
    by_cases hr : 0 < (r : ℕ)
    · have h2 : (⟨k, s⟩ : Σ i : Fin p, Fin (n i)) ≠ ⟨i, ⟨r - 1, by omega⟩⟩ :=
        fun e => hk (by cases e; rfl)
      simp [hr, Module.Basis.repr_self, Finsupp.single_apply, h1, h2]
    · simp [hr, Module.Basis.repr_self, Finsupp.single_apply, h1]

/-- The matrix of `T` is block diagonal with Jordan blocks iff `T` acts on the basis by the
Jordan chain equations. -/
lemma toMatrix_jordan_iff (T : Module.End K V) (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V)
    (lam : Fin p → K) :
    LinearMap.toMatrix b b T = Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (n i)) ↔
    ∀ (i : Fin p) (r : Fin (n i)), T (b ⟨i, r⟩) = lam i • b ⟨i, r⟩ +
      (if h : 0 < (r : ℕ) then b ⟨i, ⟨r - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.2⟩⟩
        else 0) := by
  constructor
  · intro h i r
    apply b.repr.injective
    ext ⟨k, s⟩
    have := congrFun (congrFun h ⟨k, s⟩) ⟨i, r⟩
    rw [LinearMap.toMatrix_apply] at this
    rw [this, jordan_entry]
  · intro h
    ext ⟨k, s⟩ ⟨i, r⟩
    rw [LinearMap.toMatrix_apply, h, jordan_entry]

end jordanMatrix

section jordanBasis

/-- If a basis consists of the strings of `T - lam i` generated by `v i`, then reversing each string
gives a basis in which `T` has the block diagonal Jordan matrix (proof of Axler 8.45 and 8.46,
last step). -/
lemma exists_jordan_of_strings (T : Module.End K V) {p : ℕ} (lam : Fin p → K) (m : Fin p → ℕ)
    (v : Fin p → V) (b0 : Module.Basis (Σ i : Fin p, Fin (m i + 1)) K V)
    (hb0 : ∀ x, b0 x = ((T - lam x.1 • 1) ^ (x.2 : ℕ)) (v x.1))
    (hz : ∀ i, ((T - lam i • 1) ^ (m i + 1)) (v i) = 0) :
    ∃ b : Module.Basis (Σ i : Fin p, Fin (m i + 1)) K V,
      LinearMap.toMatrix b b T =
        Matrix.blockDiagonal' (fun i => jordanBlock (lam i) (m i + 1)) := by
  let e : (Σ i : Fin p, Fin (m i + 1)) ≃ (Σ i : Fin p, Fin (m i + 1)) :=
    Equiv.sigmaCongrRight (fun i => Fin.revPerm)
  refine ⟨b0.reindex e, ?_⟩
  rw [toMatrix_jordan_iff (n := fun i => m i + 1)]
  intro i r
  have hb : ∀ i r, b0.reindex e ⟨i, r⟩ = b0 ⟨i, Fin.rev r⟩ := by
    intro i r; rw [Module.Basis.reindex_apply]; rfl
  have hT : ∀ y, T y = lam i • y + (T - lam i • 1) y := by
    intro y; simp
  have hstep : ∀ j : ℕ, (T - lam i • 1) (((T - lam i • 1) ^ j) (v i)) =
      ((T - lam i • 1) ^ (j + 1)) (v i) := by
    intro j; rw [pow_succ', mul_apply_eq_comp]
  rw [hb, hb0, hT, hstep]
  by_cases hr : 0 < (r : ℕ)
  · rw [dif_pos hr, hb, hb0]
    have : ((Fin.rev r : Fin (m i + 1)) : ℕ) + 1 =
        ((Fin.rev (⟨(r : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) r.2⟩ : Fin (m i + 1)) :
          Fin (m i + 1)) : ℕ) := by
      simp only [Fin.val_rev]; have := r.2; omega
    simp only [this]
  · rw [dif_neg hr, add_zero]
    have : ((Fin.rev r : Fin (m i + 1)) : ℕ) + 1 = m i + 1 := by
      simp only [Fin.val_rev]; omega
    rw [this, hz i]
    simp

/-- Axler 8.45: every nilpotent operator has a Jordan basis (all eigenvalues zero), and this
basis is the reversed list of strings. -/
@[kb "axler2024" "8.45, p. 340"]
theorem axler_8_45 [FiniteDimensional K V] {T : Module.End K V} (hT : IsNilpotent T) :
    ∃ (p : ℕ) (m : Fin p → ℕ) (b : Module.Basis (Σ i : Fin p, Fin (m i + 1)) K V),
      LinearMap.toMatrix b b T =
        Matrix.blockDiagonal' (fun i => jordanBlock (0 : K) (m i + 1)) := by
  obtain ⟨k, hk⟩ := hT
  obtain ⟨p, m, v, b0, hb0, hz⟩ := exists_string_basis ⟨k, hk⟩
  exact ⟨p, m, (exists_jordan_of_strings T (fun _ => (0 : K)) m v b0
    (by simpa using hb0) (by simpa using hz)).choose,
    (exists_jordan_of_strings T (fun _ => (0 : K)) m v b0
    (by simpa using hb0) (by simpa using hz)).choose_spec⟩

end jordanBasis

section general

/-- Reindex a basis of strings over a finite index type by `Fin p`. -/
lemma exists_fin_of_fintype (T : Module.End K V) {ι : Type*} [Fintype ι] (lam : ι → K)
    (m : ι → ℕ) (v : ι → V) (B : Module.Basis (Σ i : ι, Fin (m i + 1)) K V)
    (hB : ∀ x, B x = ((T - lam x.1 • 1) ^ (x.2 : ℕ)) (v x.1))
    (hz : ∀ i, ((T - lam i • 1) ^ (m i + 1)) (v i) = 0) :
    ∃ (p : ℕ) (lam' : Fin p → K) (m' : Fin p → ℕ) (v' : Fin p → V)
      (b0 : Module.Basis (Σ i : Fin p, Fin (m' i + 1)) K V),
      (∀ x, b0 x = ((T - lam' x.1 • 1) ^ (x.2 : ℕ)) (v' x.1)) ∧
      ∀ i, ((T - lam' i • 1) ^ (m' i + 1)) (v' i) = 0 := by
  let e := Fintype.equivFin ι
  let g : (Σ a : Fin (Fintype.card ι), Fin (m (e.symm a) + 1)) ≃ Σ a : ι, Fin (m a + 1) :=
    Equiv.sigmaCongrLeft (β := fun a => Fin (m a + 1)) e.symm
  refine ⟨Fintype.card ι, lam ∘ e.symm, m ∘ e.symm, v ∘ e.symm, B.reindex g.symm, ?_, ?_⟩
  · intro x
    rw [Module.Basis.reindex_apply]
    exact hB (g x)
  · intro i; exact hz _

variable [IsAlgClosed K] [FiniteDimensional K V]

private lemma maxGenEigenspace_eq_bot_of_not (T : Module.End K V) {μ : K} (h : ¬ T.HasEigenvalue μ) :
    T.maxGenEigenspace μ = ⊥ := by
  rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq,
    Polynomial.rootMultiplicity_eq_zero]
  rwa [Module.End.hasEigenvalue_iff_isRoot_charpoly] at h

/-- Strings for all the generalized eigenspaces of an operator on a complex space: the proof of
Axler 8.46 up to reversing the strings. -/
theorem exists_jordan_strings (T : Module.End K V) :
    ∃ (p : ℕ) (lam : Fin p → K) (m : Fin p → ℕ) (v : Fin p → V)
      (b0 : Module.Basis (Σ i : Fin p, Fin (m i + 1)) K V),
      (∀ x, b0 x = ((T - lam x.1 • 1) ^ (x.2 : ℕ)) (v x.1)) ∧
      ∀ i, ((T - lam i • 1) ^ (m i + 1)) (v i) = 0 := by
  classical
  let G : T.Eigenvalues → Submodule K V := fun μ => T.maxGenEigenspace μ.1
  have hinv : ∀ μ : T.Eigenvalues, ∀ x ∈ G μ, (T - μ.1 • 1) x ∈ G μ := by
    intro μ x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
    rw [← mul_apply_eq_comp, ← pow_succ, pow_succ', mul_apply_eq_comp, hk, map_zero]
  have hnil : ∀ μ : T.Eigenvalues, ∃ k, ∀ x ∈ G μ, ((T - μ.1 • (1 : Module.End K V)) ^ k) x = 0 := by
    intro μ
    refine ⟨finrank K V, fun x hx => ?_⟩
    have hx' : x ∈ T.maxGenEigenspace μ.1 := hx
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at hx'
    simpa [Module.End.genEigenspace_nat] using hx'
  have hS := fun μ : T.Eigenvalues =>
    hasStrings_of_nilpotent_on (T - μ.1 • 1) _ (G μ) rfl (hinv μ) (hnil μ)
  choose ι _ m v hvW hz hli hsp using hS
  have hmem : ∀ μ x, strFam (T - μ.1 • 1) (m μ) (v μ) x ∈ G μ :=
    fun μ x => pow_apply_mem _ (hinv μ) _ _ (hvW μ x.1)
  have hbasis : ∀ μ : T.Eigenvalues, ∃ b : Module.Basis (Σ i : ι μ, Fin (m μ i + 1)) K (G μ),
      ∀ x, (b x : V) = strFam (T - μ.1 • 1) (m μ) (v μ) x := by
    intro μ
    let f' : (Σ i : ι μ, Fin (m μ i + 1)) → G μ := fun x => ⟨_, hmem μ x⟩
    have hli' : LinearIndependent K f' := LinearIndependent.of_comp (G μ).subtype (hli μ)
    have h1 : (span K (range f')).map (G μ).subtype = span K (range (strFam (T - μ.1 • 1) (m μ) (v μ))) := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    have hsp' : ⊤ ≤ span K (range f') := by
      intro y _
      have : y.1 ∈ (span K (range f')).map (G μ).subtype := by
        rw [h1, hsp]; exact y.2
      obtain ⟨z, hz, hzy⟩ := this
      rwa [← Subtype.ext hzy]
    exact ⟨Module.Basis.mk hli' hsp', fun x => by rw [Module.Basis.coe_mk]⟩
  choose bμ hbμ using hbasis
  have hind : iSupIndep G := T.independent_maxGenEigenspace.comp Subtype.val_injective
  have htop : iSup G = ⊤ := by
    have := Module.End.iSup_maxGenEigenspace_eq_top T
    rw [eq_top_iff, ← this]
    refine iSup_le fun μ => ?_
    by_cases hμ : T.HasEigenvalue μ
    · exact le_iSup G ⟨μ, hμ⟩
    · rw [maxGenEigenspace_eq_bot_of_not T hμ]; exact bot_le
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let B := hint.collectedBasis bμ
  have hB : ∀ a, B a = strFam (T - a.1.1 • 1) (m a.1) (v a.1) a.2 := by
    intro a
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact hbμ a.1 a.2
  let B' : Module.Basis (Σ q : (Σ μ : T.Eigenvalues, ι μ), Fin (m q.1 q.2 + 1)) K V :=
    B.reindex (Equiv.sigmaAssoc (fun μ (i : ι μ) => Fin (m μ i + 1))).symm
  refine exists_fin_of_fintype T (ι := Σ μ : T.Eigenvalues, ι μ)
    (fun q : (Σ μ : T.Eigenvalues, ι μ) => (q.1.1 : K))
    (fun q : (Σ μ : T.Eigenvalues, ι μ) => m q.1 q.2)
    (fun q : (Σ μ : T.Eigenvalues, ι μ) => v q.1 q.2) B' ?_ ?_
  · intro x
    rw [Module.Basis.reindex_apply]
    exact hB _
  · intro q
    exact hz q.1 q.2

/-- Axler 8.46 (Jordan form): over an algebraically closed field (in particular `ℂ`) every
operator has a Jordan basis. -/
@[kb "axler2024" "8.46, p. 342"]
theorem axler_8_46 (T : Module.End K V) :
    ∃ (p : ℕ) (n : Fin p → ℕ) (b : Module.Basis (Σ i : Fin p, Fin (n i)) K V),
      IsJordanBasis T b := by
  obtain ⟨p, lam, m, v, b0, hb0, hz⟩ := exists_jordan_strings T
  obtain ⟨b, hb⟩ := exists_jordan_of_strings T lam m v b0 hb0 hz
  exact ⟨p, fun i => m i + 1, b, lam, hb⟩

end general

section stringBasis

/-- Hefferon Definition Five.III.2.11: a basis that is the concatenation of the `N`-strings
`v i, N (v i), ..., N^(m i) (v i)` with `N^(m i + 1) (v i) = 0` (each string has length `m i + 1`). -/
def IsStringBasis (N : Module.End K V) {k : ℕ} {m : Fin k → ℕ} (v : Fin k → V)
    (b : Module.Basis (Σ i : Fin k, Fin (m i + 1)) K V) : Prop :=
  (∀ x, b x = (N ^ (x.2 : ℕ)) (v x.1)) ∧ ∀ i, (N ^ (m i + 1)) (v i) = 0

lemma IsStringBasis.pow_eq_zero_iff {N : Module.End K V} {k : ℕ} {m : Fin k → ℕ} {v : Fin k → V}
    {b : Module.Basis (Σ i : Fin k, Fin (m i + 1)) K V} (h : IsStringBasis N v b) (n : ℕ) :
    N ^ n = 0 ↔ ∀ i, m i + 1 ≤ n := by
  constructor
  · intro hn i
    by_contra hlt
    push Not at hlt
    have hx := h.1 ⟨i, ⟨n, hlt⟩⟩
    have : b ⟨i, ⟨n, hlt⟩⟩ = 0 := by rw [hx]; simp [hn]
    exact b.ne_zero _ this
  · intro hn
    apply b.ext
    rintro ⟨i, j⟩
    rw [h.1]
    have h0 : (N ^ n) (v i) = 0 := pow_apply_eq_zero_of_ge N (h.2 i) (hn i)
    simp only [LinearMap.zero_apply]
    rw [← mul_apply_eq_comp, (Commute.pow_pow_self N n j).eq, mul_apply_eq_comp, h0, map_zero]

/-- Hefferon Lemma Five.III.2.15: if the space has a string basis for `N`, the index of nilpotency of
`N` (least `n` with `N^n = 0`) is the length of the longest string. -/
@[kb "hefferon2020" "Five.III.2.15, p. 442"]
theorem hefferon_Five_III_2_15 {N : Module.End K V} {k : ℕ} {m : Fin k → ℕ} {v : Fin k → V}
    {b : Module.Basis (Σ i : Fin k, Fin (m i + 1)) K V} (h : IsStringBasis N v b) :
    IsLeast {n : ℕ | N ^ n = 0} (Finset.univ.sup fun i => m i + 1) := by
  refine ⟨?_, fun n hn => ?_⟩
  · show N ^ _ = 0
    rw [h.pow_eq_zero_iff]
    exact fun i => Finset.le_sup (f := fun i => m i + 1) (Finset.mem_univ i)
  · have := (h.pow_eq_zero_iff n).mp hn
    exact Finset.sup_le fun i _ => this i

end stringBasis

section chainHeadline

/-- Axler Exercise 8A.2: if `T^(m-1) v ≠ 0` but `T^m v = 0` then `v, T v, ..., T^(m-1) v` are
linearly independent. -/
@[kb "axler2024" "8A.2, p. 324"]
theorem axler_8A_2 (T : Module.End K V) {m : ℕ} {v : V} (h1 : (T ^ (m - 1)) v ≠ 0)
    (h2 : (T ^ m) v = 0) : LinearIndependent K (fun j : Fin m => (T ^ (j : ℕ)) v) := by
  cases m with
  | zero => exact absurd (by simpa using h2) (by simpa using h1)
  | succ m => exact chain_linearIndependent T (by simpa using h1) h2

/-- Hefferon Definition Five.IV.2.6: the `n × n` Jordan block of Hefferon's convention, with
`a` on the diagonal and `1` directly below it (the transpose of Axler's block). -/
def jordanBlockLower (a : K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r c => if r = c then a else if (c : ℕ) + 1 = r then 1 else 0

lemma jordanBlockLower_eq_transpose (a : K) (n : ℕ) :
    jordanBlockLower a n = (jordanBlock a n).transpose := by
  ext r c
  simp only [jordanBlockLower, jordanBlock, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : r = c
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Hefferon Definition Five.IV.2.6: in a basis `b` of an `n`-dimensional space the matrix of `T` is
the Jordan block `jordanBlockLower lam n` iff the basis is a Jordan chain: `T b_j = lam b_j + b_{j+1}`
and the last vector is an eigenvector. -/
@[kb "hefferon2020" "Five.IV.2.6, p. 462"]
theorem hefferon_Five_IV_2_6 (T : Module.End K V) {n : ℕ} (b : Module.Basis (Fin n) K V) (lam : K) :
    LinearMap.toMatrix b b T = jordanBlockLower lam n ↔
      ∀ j : Fin n, T (b j) = lam • b j + (if h : (j : ℕ) + 1 < n then b ⟨j + 1, h⟩ else 0) := by
  have entry : ∀ (j r : Fin n),
      b.repr (lam • b j + (if h : (j : ℕ) + 1 < n then b ⟨j + 1, h⟩ else 0)) r =
        jordanBlockLower lam n r j := by
    intro j r
    by_cases h : (j : ℕ) + 1 < n
    · simp only [h, dite_true, map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.single_apply, jordanBlockLower, Matrix.of_apply, smul_eq_mul,
        Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · simp only [h, dite_false, add_zero, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, jordanBlockLower, Matrix.of_apply, smul_eq_mul, Fin.ext_iff]
      split_ifs <;> first | omega | simp
  constructor
  · intro h j
    apply b.repr.injective
    ext r
    rw [← LinearMap.toMatrix_apply, h, entry]
  · intro h
    ext r j
    rw [LinearMap.toMatrix_apply, h, entry]

end chainHeadline

section axler818

variable [FiniteDimensional K V]

/-- A strictly upper triangular matrix gives a nilpotent operator (`T^n = 0`). -/
lemma pow_eq_zero_of_strictUpper {n : ℕ} (T : Module.End K V) (b : Module.Basis (Fin n) K V)
    (h : ∀ i j, j ≤ i → LinearMap.toMatrix b b T i j = 0) : T ^ n = 0 := by
  let U : ℕ → Submodule K V := fun c => span K (b '' {i | (i : ℕ) < c})
  have hstep : ∀ i : Fin n, T (b i) ∈ span K (b '' {l | l < i}) := by
    intro i
    rw [← b.sum_repr (T (b i))]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : l < i
    · exact Submodule.smul_mem _ _ (subset_span ⟨l, hl, rfl⟩)
    · have h0 := h l i (not_lt.mp hl)
      rw [LinearMap.toMatrix_apply] at h0
      rw [h0, zero_smul]; exact zero_mem _
  have hU : ∀ c, ∀ x ∈ U (c + 1), T x ∈ U c := by
    intro c
    have : U (c + 1) ≤ (U c).comap T := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      show T (b i) ∈ U c
      refine Submodule.span_mono (image_mono fun l hl => ?_) (hstep i)
      exact lt_of_lt_of_le (Fin.lt_def.mp hl) (Nat.lt_succ_iff.mp hi)
    exact fun x hx => this hx
  have hpow : ∀ c, ∀ x ∈ U c, (T ^ c) x = 0 := by
    intro c
    induction c with
    | zero =>
      intro x hx
      have : x = 0 := by simpa [U] using hx
      simp [this]
    | succ c ih =>
      intro x hx
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (hU c x hx)
  apply b.ext
  intro i
  rw [LinearMap.zero_apply]
  exact hpow n _ (subset_span ⟨i, i.2, rfl⟩)

/-- A nilpotent operator has a basis in which its matrix is strictly upper triangular. -/
lemma exists_strictUpper_of_isNilpotent {T : Module.End K V} (hT : IsNilpotent T) :
    ∃ b : Module.Basis (Fin (finrank K V)) K V,
      ∀ i j, j ≤ i → LinearMap.toMatrix b b T i j = 0 := by
  obtain ⟨p, m, b, hb⟩ := axler_8_45 hT
  let b1 : Module.Basis (Lex (Σ i : Fin p, Fin (m i + 1))) K V := b.reindex toLex
  have hcard : Fintype.card (Lex (Σ i : Fin p, Fin (m i + 1))) = finrank K V :=
    (Module.finrank_eq_card_basis b1).symm
  let e : Fin (finrank K V) ≃o (Lex (Σ i : Fin p, Fin (m i + 1))) := monoEquivOfFin _ hcard
  refine ⟨b1.reindex e.symm.toEquiv, fun i j hji => ?_⟩
  have key : ∀ x y : (Σ i : Fin p, Fin (m i + 1)), toLex y ≤ toLex x →
      (Matrix.blockDiagonal' (fun i => jordanBlock (0 : K) (m i + 1))) x y = 0 := by
    rintro ⟨k, s⟩ ⟨i, r⟩ hle
    rw [Sigma.Lex.le_def] at hle
    rcases hle with hlt | ⟨heq, hle⟩
    · exact Matrix.blockDiagonal'_apply_ne _ _ _ (ne_of_gt hlt)
    · have hik : i = k := heq
      subst hik
      rw [Matrix.blockDiagonal'_apply_eq]
      have hrs : (r : ℕ) ≤ s := hle
      simp only [jordanBlock, Matrix.of_apply]
      by_cases h1 : s = r
      · simp [h1]
      · have h2 : ¬ (s : ℕ) + 1 = r := by omega
        simp [h1, h2]
  rw [LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply]
  have := key (ofLex (e i)) (ofLex (e j)) (by simpa using e.monotone hji)
  rw [← hb] at this
  rw [LinearMap.toMatrix_apply] at this
  simpa [b1, Module.Basis.reindex_apply] using this

/-- Axler 8.18: `T` is nilpotent iff its minimal polynomial is a power of `z` iff some basis gives a
strictly upper triangular matrix (all entries on and below the diagonal vanish). -/
@[kb "axler2024" "8.18, p. 323"]
theorem axler_8_18 (T : Module.End K V) :
    List.TFAE [IsNilpotent T, ∃ m : ℕ, minpoly K T = Polynomial.X ^ m,
      ∃ b : Module.Basis (Fin (finrank K V)) K V,
        ∀ i j, j ≤ i → LinearMap.toMatrix b b T i j = 0] := by
  tfae_have 1 → 2 := by
    rintro ⟨k, hk⟩
    have hdvd : minpoly K T ∣ Polynomial.X ^ k :=
      minpoly.dvd K T (by simp [hk])
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X k).mp hdvd
    exact ⟨i, Polynomial.eq_of_monic_of_associated (minpoly.monic (Algebra.IsIntegral.isIntegral T))
      (Polynomial.monic_X_pow i) hi⟩
  tfae_have 2 → 1 := by
    rintro ⟨m, hm⟩
    have := minpoly.aeval K T
    rw [hm] at this
    exact ⟨m, by simpa using this⟩
  tfae_have 1 → 3 := exists_strictUpper_of_isNilpotent
  tfae_have 3 → 1 := by
    rintro ⟨b, hb⟩
    exact ⟨finrank K V, pow_eq_zero_of_strictUpper T b hb⟩
  tfae_finish

end axler818

section matrixForm

/-- Hefferon Theorem Five.III.2.17 (existence part; Axler's superdiagonal convention): every
nilpotent `n × n` matrix is similar to a block diagonal matrix of Jordan blocks with eigenvalue `0`
(after reindexing the concatenated blocks by `Fin n`). -/
@[kb "hefferon2020" "Five.III.2.17, p. 445"]
theorem hefferon_Five_III_2_17 {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : IsNilpotent A) :
    ∃ (p : ℕ) (m : Fin p → ℕ) (e : (Σ i : Fin p, Fin (m i + 1)) ≃ Fin n)
      (P : (Matrix (Fin n) (Fin n) K)ˣ),
      A = (P : Matrix (Fin n) (Fin n) K) *
        Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m i + 1)) *
        ((P⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) := by
  classical
  let T : Module.End K (Fin n → K) := Matrix.toLin' A
  have hT : IsNilpotent T := hA.map (Matrix.toLinAlgEquiv' (R := K) (n := Fin n))
  obtain ⟨p, m, b, hb⟩ := axler_8_45 hT
  have hcard : Fintype.card (Σ i : Fin p, Fin (m i + 1)) = n := by
    rw [← Module.finrank_eq_card_basis b]; simp
  let e : (Σ i : Fin p, Fin (m i + 1)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin n) K (Fin n → K) := b.reindex e
  have hred : LinearMap.toMatrix b' b' T =
      Matrix.reindex e e (Matrix.blockDiagonal' fun i => jordanBlock (0 : K) (m i + 1)) := by
    rw [← hb]
    ext i j
    simp [b', LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
      Module.Basis.reindex_apply]
  let e0 := Pi.basisFun K (Fin n)
  let P0 : Matrix (Fin n) (Fin n) K := e0.toMatrix b'
  let Q0 : Matrix (Fin n) (Fin n) K := b'.toMatrix e0
  have hPQ : P0 * Q0 = 1 := Module.Basis.toMatrix_mul_toMatrix_flip e0 b'
  have hQP : Q0 * P0 = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b' e0
  refine ⟨p, m, e, ⟨P0, Q0, hPQ, hQP⟩, ?_⟩
  have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (c := e0) (c' := b')
    (b := e0) (b' := b') (f := T)
  rw [hred] at this
  simp only [Units.val_mk, Units.inv_mk]
  rw [show P0 = e0.toMatrix b' from rfl, show Q0 = b'.toMatrix e0 from rfl, this]
  simp [e0, T, LinearMap.toMatrix_eq_toMatrix']

end matrixForm

section blockTriangular

variable [IsAlgClosed K] [FiniteDimensional K V]

open Classical in
lemma isInternal_maxGenEigenspace' (T : Module.End K V) :
    DirectSum.IsInternal (fun μ : T.Eigenvalues => T.maxGenEigenspace μ.1) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact T.independent_maxGenEigenspace.comp Subtype.val_injective
  · have := Module.End.iSup_maxGenEigenspace_eq_top T
    rw [eq_top_iff, ← this]
    refine iSup_le fun μ => ?_
    by_cases hμ : T.HasEigenvalue μ
    · exact le_iSup (fun μ : T.Eigenvalues => T.maxGenEigenspace μ.1) ⟨μ, hμ⟩
    · rw [maxGenEigenspace_eq_bot_of_not T hμ]; exact bot_le

open Classical in
/-- Axler 8.37: over `ℂ` there is a basis of `V` (the concatenation of bases of the generalized
eigenspaces `G(λ_k, T)`, of dimensions `d_k`) in which `T` has block diagonal matrix with blocks
`A_k` of size `d_k × d_k`, upper triangular with constant diagonal `λ_k`. -/
@[kb "axler2024" "8.37, p. 333"]
theorem axler_8_37 (T : Module.End K V) :
    ∃ (b : Module.Basis (Σ μ : T.Eigenvalues, Fin (finrank K (T.maxGenEigenspace μ.1))) K V)
      (A : ∀ μ : T.Eigenvalues, Matrix (Fin (finrank K (T.maxGenEigenspace μ.1)))
        (Fin (finrank K (T.maxGenEigenspace μ.1))) K),
      LinearMap.toMatrix b b T = Matrix.blockDiagonal' A ∧
      ∀ μ : T.Eigenvalues, (∀ i j, j < i → A μ i j = 0) ∧ ∀ i, A μ i i = μ.1 := by
  classical
  have hT : ∀ μ : T.Eigenvalues, ∀ x ∈ T.maxGenEigenspace μ.1, T x ∈ T.maxGenEigenspace μ.1 := by
    intro μ x hx
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
    refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨k, ?_⟩
    have hc : Commute T ((T - μ.1 • (1 : Module.End K V)) ^ k) :=
      ((Commute.refl T).sub_right ((Commute.one_right T).smul_right μ.1)).pow_right k
    rw [← mul_apply_eq_comp, ← hc.eq, mul_apply_eq_comp, hk, map_zero]
  have hN : ∀ μ : T.Eigenvalues, ∀ x ∈ T.maxGenEigenspace μ.1,
      (T - μ.1 • (1 : Module.End K V)) x ∈ T.maxGenEigenspace μ.1 := by
    intro μ x hx
    have := (T.maxGenEigenspace μ.1).sub_mem (hT μ x hx) ((T.maxGenEigenspace μ.1).smul_mem μ.1 hx)
    simpa using this
  let Tμ : ∀ μ : T.Eigenvalues, Module.End K (T.maxGenEigenspace μ.1) := fun μ => T.restrict (hT μ)
  let Nμ : ∀ μ : T.Eigenvalues, Module.End K (T.maxGenEigenspace μ.1) :=
    fun μ => (T - μ.1 • (1 : Module.End K V)).restrict (hN μ)
  have hnil : ∀ μ, IsNilpotent (Nμ μ) := by
    intro μ
    have hpow : ∀ (k : ℕ) (y : T.maxGenEigenspace μ.1),
        (((Nμ μ ^ k) y : T.maxGenEigenspace μ.1) : V) = ((T - μ.1 • (1 : Module.End K V)) ^ k) y := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_apply_eq_comp, ← ih y]
        rfl
    refine ⟨finrank K V, ?_⟩
    ext y
    rw [LinearMap.zero_apply]
    rw [hpow]
    have hy : (y : V) ∈ T.genEigenspace μ.1 (finrank K V) := by
      rw [← Module.End.maxGenEigenspace_eq_genEigenspace_finrank]; exact y.2
    simpa [Module.End.genEigenspace_nat] using hy
  have hbasis : ∀ μ : T.Eigenvalues, ∃ c : Module.Basis (Fin (finrank K (T.maxGenEigenspace μ.1)))
      K (T.maxGenEigenspace μ.1), ∀ i j, j ≤ i → LinearMap.toMatrix c c (Nμ μ) i j = 0 :=
    fun μ => exists_strictUpper_of_isNilpotent (hnil μ)
  choose c hc using hbasis
  have hint := isInternal_maxGenEigenspace' T
  refine ⟨hint.collectedBasis c, fun μ => LinearMap.toMatrix (c μ) (c μ) (Tμ μ), ?_, ?_⟩
  · ext ⟨μ, i⟩ ⟨ν, j⟩
    rw [LinearMap.toMatrix_apply, DirectSum.IsInternal.collectedBasis_coe]
    have hmem : T ((c ν j : T.maxGenEigenspace ν.1) : V) ∈ T.maxGenEigenspace ν.1 :=
      hT ν _ (c ν j).2
    by_cases hμν : μ = ν
    · subst hμν
      rw [Matrix.blockDiagonal'_apply_eq, LinearMap.toMatrix_apply,
        DirectSum.IsInternal.collectedBasis_repr_of_mem hint c hmem]
      rfl
    · rw [DirectSum.IsInternal.collectedBasis_repr_of_mem_ne hint c (Ne.symm hμν) hmem,
        Matrix.blockDiagonal'_apply_ne _ _ _ hμν]
  · intro μ
    have hTN : Tμ μ = Nμ μ + μ.1 • 1 := by
      ext y
      simp [Tμ, Nμ]
    have hA : LinearMap.toMatrix (c μ) (c μ) (Tμ μ) =
        LinearMap.toMatrix (c μ) (c μ) (Nμ μ) + μ.1 • 1 := by
      rw [hTN, map_add, map_smul, LinearMap.toMatrix_one]
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · beta_reduce
      rw [hA, Matrix.add_apply, hc μ i j hji.le, Matrix.smul_apply,
        Matrix.one_apply_ne (ne_of_gt hji)]
      simp
    · beta_reduce
      rw [hA, Matrix.add_apply, hc μ i i le_rfl, Matrix.smul_apply, Matrix.one_apply_eq]
      simp

end blockTriangular

end UndergradKB.LinearAlgebra
