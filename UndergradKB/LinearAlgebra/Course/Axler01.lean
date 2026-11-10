import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DFinsupp
import UndergradKB.Common.Attr

/-!
# Axler, Chapter 1 (vector spaces): book-named wrappers of Mathlib results

Each theorem restates an item of Axler's *Linear Algebra Done Right* (4th ed.), Chapter 1, in the
book's terms, and is proved by the Mathlib declarations named in the proof.
Definition rows without a natural defining property are not given a declaration.
-/

namespace UndergradKB.LinearAlgebra.Course

open UndergradKB

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ## 1A Rn and Cn -/

/-- Axler 1.1: every complex number is `a + b i` with real `a`, `b`, and `i² = -1`. -/
@[kb "axler2024" "1.1, p. 20", kb "hefferon2020" "Five.I.1.cx, p. 410"]
theorem axler_1_1 : (∀ z : ℂ, ∃ a b : ℝ, z = a + b * Complex.I) ∧ Complex.I ^ 2 = -1 :=
  ⟨fun z => ⟨z.re, z.im, (Complex.re_add_im z).symm⟩, Complex.I_sq⟩

/-- Axler 1.3: the arithmetic laws of the complex numbers. -/
@[kb "axler2024" "1.3, p. 21", kb "hefferon2020" "Five.I.2.arith, p. 410"]
theorem axler_1_3 :
    (∀ a b : ℂ, a + b = b + a) ∧ (∀ a b : ℂ, a * b = b * a) ∧
    (∀ a b c : ℂ, a + b + c = a + (b + c)) ∧ (∀ a b c : ℂ, a * b * c = a * (b * c)) ∧
    (∀ a : ℂ, a + 0 = a) ∧ (∀ a : ℂ, a * 1 = a) ∧
    (∀ a : ℂ, ∃ b : ℂ, a + b = 0) ∧ (∀ a : ℂ, a ≠ 0 → ∃ b : ℂ, a * b = 1) ∧
    (∀ a b c : ℂ, a * (b + c) = a * b + a * c) :=
  ⟨add_comm, mul_comm, add_assoc, mul_assoc, add_zero, mul_one,
    fun a => ⟨-a, add_neg_cancel a⟩, fun a ha => ⟨a⁻¹, mul_inv_cancel₀ ha⟩, mul_add⟩

/-- Axler 1.5: subtraction, reciprocal and division on the complex numbers. -/
@[kb "axler2024" "1.5, p. 22"]
theorem axler_1_5 :
    (∀ α β : ℂ, β - α = β + -α) ∧ (∀ α : ℂ, α ≠ 0 → α * (1 / α) = 1) ∧
    (∀ α β : ℂ, β / α = β * (1 / α)) :=
  ⟨fun _ _ => sub_eq_add_neg _ _, fun α hα => by simp [hα], fun _ _ => by simp [div_eq_mul_inv]⟩

/-- Axler 1.13: addition in `Fⁿ` is coordinatewise. -/
@[kb "axler2024" "1.13, p. 24", kb "hefferon2020" "One.I.2.10, p. 27"]
theorem axler_1_13 {n : ℕ} (x y : Fin n → K) : x + y = fun k => x k + y k := rfl

/-- Axler 1.14: addition in `Fⁿ` is commutative. -/
@[kb "axler2024" "1.14, p. 25"]
theorem axler_1_14 {n : ℕ} (x y : Fin n → K) : x + y = y + x := add_comm x y

/-- Axler 1.17: the additive inverse in `Fⁿ` negates each coordinate. -/
@[kb "axler2024" "1.17, p. 27"]
theorem axler_1_17 {n : ℕ} (x : Fin n → K) : x + (fun k => -x k) = 0 ∧ -x = fun k => -x k :=
  ⟨by ext k; simp, rfl⟩

/-- Axler 1.18: scalar multiplication in `Fⁿ` multiplies each coordinate. -/
@[kb "axler2024" "1.18, p. 27", kb "hefferon2020" "One.I.2.11, p. 27"]
theorem axler_1_18 {n : ℕ} (c : K) (x : Fin n → K) : c • x = fun k => c * x k := rfl

/-! ## 1B Definition of vector space -/

/-- Axler 1.19, 1.20, 1.21: the vector-space axioms hold in a `Module` over a field. -/
@[kb "axler2024" "1.19, p. 30", kb "axler2024" "1.20, p. 30",
  kb "axler2024" "1.21, p. 30", kb "hefferon2020" "Two.I.1.1, p. 94"]
theorem axler_1_19 :
    (∀ u v : V, u + v = v + u) ∧ (∀ u v w : V, (u + v) + w = u + (v + w)) ∧
    (∀ a b : K, ∀ v : V, (a * b) • v = a • b • v) ∧ (∀ v : V, v + 0 = v) ∧
    (∀ v : V, ∃ w : V, v + w = 0) ∧ (∀ v : V, (1 : K) • v = v) ∧
    (∀ (a : K) (u v : V), a • (u + v) = a • u + a • v) ∧
    (∀ (a b : K) (v : V), (a + b) • v = a • v + b • v) :=
  ⟨add_comm, add_assoc, mul_smul, add_zero, fun v => ⟨-v, add_neg_cancel v⟩, one_smul K,
    smul_add, add_smul⟩

/-- Axler 1.23: `F^∞`, the sequences of elements of `F`, has termwise operations. -/
@[kb "axler2024" "1.23, p. 31", kb "hefferon2020" "Two.I.1.10, p. 99"]
theorem axler_1_23 :
    (∀ (x y : ℕ → K) (n : ℕ), (x + y) n = x n + y n) ∧
    (∀ (c : K) (x : ℕ → K) (n : ℕ), (c • x) n = c * x n) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Axler 1.25: for any set `S`, the functions `S → F` have pointwise operations. -/
@[kb "axler2024" "1.25, p. 32", kb "hefferon2020" "Two.I.1.12, p. 100"]
theorem axler_1_25 {S : Type*} :
    (∀ (f g : S → K) (s : S), (f + g) s = f s + g s) ∧
    (∀ (c : K) (f : S → K) (s : S), (c • f) s = c * f s) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Axler 1.26: a vector space has a unique additive identity. -/
@[kb "axler2024" "1.26, p. 32"]
theorem axler_1_26 (e : V) (h : ∀ v : V, v + e = v) : e = 0 := by
  simpa using h 0

/-- Axler 1.27: every vector has a unique additive inverse. -/
@[kb "axler2024" "1.27, p. 33"]
theorem axler_1_27 (v w w' : V) (h : v + w = 0) (h' : v + w' = 0) : w = w' :=
  (neg_eq_of_add_eq_zero_right h).symm.trans (neg_eq_of_add_eq_zero_right h')

/-- Axler 1.30: `0 • v = 0`. -/
@[kb "axler2024" "1.30, p. 33", kb "hefferon2020" "Two.I.1.16, p. 102"]
theorem axler_1_30 (v : V) : (0 : K) • v = 0 := zero_smul K v

/-- Axler 1.31: `a • 0 = 0`. -/
@[kb "axler2024" "1.31, p. 34"]
theorem axler_1_31 (a : K) : a • (0 : V) = 0 := smul_zero a

/-- Axler 1.32: `(-1) • v = -v`. -/
@[kb "axler2024" "1.32, p. 34"]
theorem axler_1_32 (v : V) : (-1 : K) • v = -v := neg_one_smul K v

/-! ## 1C Subspaces -/

/-- Axler 1.34: a subset is a subspace iff it contains 0 and is closed under addition and scalar
multiplication. -/
@[kb "axler2024" "1.34, p. 36"]
theorem axler_1_34 (U : Set V) :
    (∃ S : Submodule K V, (S : Set V) = U) ↔
      (0 ∈ U ∧ (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) ∧ (∀ (c : K), ∀ v ∈ U, c • v ∈ U)) := by
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨S.zero_mem, fun u hu v hv => S.add_mem hu hv, fun c v hv => S.smul_mem c hv⟩
  · rintro ⟨h0, ha, hs⟩
    exact ⟨{ carrier := U, zero_mem' := h0, add_mem' := fun {a b} h1 h2 => ha a h1 b h2,
             smul_mem' := fun c v hv => hs c v hv }, rfl⟩

/-- Axler 1.36 (binary case): membership in `U + W` means `u + w` with `u ∈ U`, `w ∈ W`. -/
@[kb "axler2024" "1.36, p. 37", kb "hefferon2020" "Two.III.4.1, p. 154"]
theorem axler_1_36 (U W : Submodule K V) (v : V) :
    v ∈ U ⊔ W ↔ ∃ u ∈ U, ∃ w ∈ W, u + w = v :=
  Submodule.mem_sup

/-- Axler 1.36 (finitely many summands): membership in `V₁ + ⋯ + Vₘ` means a sum `v₁ + ⋯ + vₘ`
with `vₖ ∈ Vₖ`. -/
theorem axler_1_36_finite {ι : Type*} [Fintype ι] (U : ι → Submodule K V) (v : V) :
    v ∈ ⨆ i, U i ↔ ∃ f : ι → V, (∀ i, f i ∈ U i) ∧ ∑ i, f i = v := by
  classical
  constructor
  · intro hv
    refine Submodule.iSup_induction U (motive := fun x =>
      ∃ f : ι → V, (∀ i, f i ∈ U i) ∧ ∑ i, f i = x) hv ?_ ?_ ?_
    · intro i x hx
      refine ⟨Pi.single i x, fun j => ?_, by simp⟩
      by_cases h : j = i
      · subst h; simpa using hx
      · simp [h]
    · exact ⟨0, fun i => (U i).zero_mem, by simp⟩
    · rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, fun i => (U i).add_mem (hf i) (hg i), by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨f, hf, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (hf i)

/-- Axler 1.40: the sum of subspaces is the smallest subspace containing all of them. -/
@[kb "axler2024" "1.40, p. 39"]
theorem axler_1_40 {ι : Type*} (U : ι → Submodule K V) :
    IsLeast {W : Submodule K V | ∀ i, U i ≤ W} (⨆ i, U i) :=
  ⟨fun i => le_iSup U i, fun _ h => iSup_le h⟩

/-- Axler 1.41: the sum `V₁ + ⋯ + Vₘ` is direct (the subspaces are independent) iff every element of
the sum has exactly one expression as a sum of vectors from the summands. -/
@[kb "axler2024" "1.41, p. 39", kb "hefferon2020" "Two.III.4.10, p. 158"]
theorem axler_1_41 {ι : Type*} [Fintype ι] [DecidableEq ι] (U : ι → Submodule K V) :
    iSupIndep U ↔
      ∀ v : V, v ∈ ⨆ i, U i → ∃! f : (i : ι) → U i, ∑ i, (f i : V) = v := by
  classical
  have key : ∀ d : Π₀ i, U i, DFinsupp.lsum ℕ (fun i => (U i).subtype) d = ∑ i, (d i : V) := by
    intro d
    rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
      DFinsupp.sum_eq_sum_fintype _ (by simp)]
    simp
  have hD : ∀ (g : (i : ι) → U i) (i : ι), (DFinsupp.equivFunOnFintype.symm g) i = g i :=
    fun g i => congrFun (DFinsupp.equivFunOnFintype.apply_symm_apply g) i
  rw [iSupIndep_iff_dfinsupp_lsum_injective]
  constructor
  · intro inj v hv
    obtain ⟨f, hf, hs⟩ := (axler_1_36_finite U v).mp hv
    refine ⟨fun i => ⟨f i, hf i⟩, hs, fun g' hg' => ?_⟩
    have := @inj (DFinsupp.equivFunOnFintype.symm g')
      (DFinsupp.equivFunOnFintype.symm fun i => ⟨f i, hf i⟩) (by
        rw [key, key]; simp only [hD]; exact hg'.trans hs.symm)
    funext i
    have h2 := congrArg (fun d => d i) this
    simp only [hD] at h2
    exact h2
  · intro h d1 d2 h12
    have hv : (DFinsupp.lsum ℕ (fun i => (U i).subtype) d1) ∈ ⨆ i, U i := by
      rw [key]
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (d1 i).2
    obtain ⟨g, _, hg⟩ := h _ hv
    have e1 := hg (fun i => d1 i) (key d1).symm
    have e2 := hg (fun i => d2 i) ((key d2).symm.trans h12.symm)
    refine DFinsupp.ext fun i => ?_
    exact congrFun (e1.trans e2.symm) i

/-- Axler 1.46: `U + W` is direct (unique decompositions) iff `U ∩ W = {0}`. -/
@[kb "axler2024" "1.46, p. 41"]
theorem axler_1_46 (U W : Submodule K V) :
    (∀ v ∈ U ⊔ W, ∃! p : U × W, (p.1 : V) + p.2 = v) ↔ U ⊓ W = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h0 : (0 : V) ∈ U ⊔ W := Submodule.zero_mem _
    obtain ⟨p, _, hp⟩ := h 0 h0
    have h1 := hp ⟨⟨x, hx.1⟩, ⟨-x, W.neg_mem hx.2⟩⟩ (by simp)
    have h2 := hp (0, 0) (by simp)
    have := (h1.trans h2.symm)
    simpa using congrArg (fun q : U × W => (q.1 : V)) this
  · intro h v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl, ?_⟩
    rintro ⟨⟨u', hu'⟩, ⟨w', hw'⟩⟩ (he : u' + w' = u + w)
    have hmem : u' - u ∈ U ⊓ W := by
      refine ⟨U.sub_mem hu' hu, ?_⟩
      have : u' - u = w - w' := by
        rw [sub_eq_sub_iff_add_eq_add]; rw [add_comm w, he]
      rw [this]; exact W.sub_mem hw hw'
    rw [h] at hmem
    have h1 : u' = u := sub_eq_zero.mp hmem
    have h2 : w' = w := by simpa [h1] using he
    subst h1; subst h2; rfl

/-- Axler 1.46 and Hefferon Two.III.4.15: a space is the direct sum of two subspaces iff they are
complementary (sum is everything, intersection trivial). -/
@[kb "hefferon2020" "Two.III.4.15, p. 158"]
theorem axler_1_46_isCompl (U W : Submodule K V) :
    DirectSum.IsInternal (fun b : Bool => cond b U W) ↔ IsCompl U W :=
  DirectSum.isInternal_submodule_iff_isCompl (fun b : Bool => cond b U W)
    (i := true) (j := false) (by decide) (by ext b; cases b <;> simp)

end UndergradKB.LinearAlgebra.Course
