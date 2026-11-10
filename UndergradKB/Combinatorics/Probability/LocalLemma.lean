import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import UndergradKB.Combinatorics.Probability.Discrete
import UndergradKB.Common.Attr

/-!
# The Lovász Local Lemma (Keller–Trotter, Section 16.7)

Events are `Finset Ω` in a finite probability space `μ : FinProbSpace Ω`, indexed by a type `ι`
(the book's family `F`).  For a finite set `S` of indices, `noneOf E S` is the event that none of
the `E j`, `j ∈ S`, occurs (the book's product of complements).
-/

open Finset

namespace UndergradKB.Combinatorics.Probability

open FinProbSpace

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [DecidableEq ι]

/-- The event that none of the events `E j`, `j ∈ S`, occurs (an empty intersection is `univ`). -/
def noneOf (E : ι → Finset Ω) (S : Finset ι) : Finset Ω := S.inf fun j => (E j)ᶜ

omit [DecidableEq ι] in
lemma mem_noneOf {E : ι → Finset Ω} {S : Finset ι} {ω : Ω} :
    ω ∈ noneOf E S ↔ ∀ j ∈ S, ω ∉ E j := by
  simp [noneOf, Finset.mem_inf]

omit [DecidableEq ι] in
lemma noneOf_empty (E : ι → Finset Ω) : noneOf E ∅ = univ := by
  ext; simp [mem_noneOf]

lemma noneOf_union (E : ι → Finset Ω) (S T : Finset ι) :
    noneOf E (S ∪ T) = noneOf E S ∩ noneOf E T := by
  ext ω
  simp only [mem_noneOf, mem_union, mem_inter]
  constructor
  · intro h; exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨h1, h2⟩ j (hj | hj)
    exacts [h1 j hj, h2 j hj]

lemma noneOf_insert (E : ι → Finset Ω) (j : ι) (S : Finset ι) :
    noneOf E (insert j S) = noneOf E S \ E j := by
  ext ω
  simp only [mem_noneOf, mem_insert, mem_sdiff]
  constructor
  · intro h; exact ⟨fun k hk => h k (Or.inr hk), h j (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩ k (rfl | hk)
    exacts [h2, h1 k hk]

omit [DecidableEq ι] in
lemma noneOf_anti (E : ι → Finset Ω) {S T : Finset ι} (h : S ⊆ T) : noneOf E T ⊆ noneOf E S := by
  intro ω hω
  rw [mem_noneOf] at hω ⊢
  exact fun j hj => hω j (h hj)

variable (μ : FinProbSpace Ω)

lemma prob_noneOf_insert (E : ι → Finset Ω) (j : ι) (S : Finset ι) :
    μ.prob (noneOf E (insert j S)) = μ.prob (noneOf E S) - μ.prob (E j ∩ noneOf E S) := by
  have h := sum_inter_add_sum_sdiff (noneOf E S) (E j) μ.p
  rw [noneOf_insert, prob, prob, prob, inter_comm]
  linarith

/-- The hypothesis of the Local Lemma on the family `E` and the neighbourhoods `N`: each `E i` is
independent of any event built from complements `E j` with `j` outside `N i` (and `j ≠ i`), in
the book's sense `P(E | ∏ F) = P(E)`, written multiplicatively. -/
def LLLIndep (E : ι → Finset Ω) (N : ι → Finset ι) : Prop :=
  ∀ (i : ι) (S : Finset ι), i ∉ S → Disjoint S (N i) →
    μ.prob (E i ∩ noneOf E S) = μ.prob (E i) * μ.prob (noneOf E S)

variable {μ} {E : ι → Finset Ω} {N : ι → Finset ι} {x : ι → ℝ}

/-- Chain estimate: if the conditional bound holds on all index sets of size `< m`, then
`P(none of S₁ ∪ T) ≥ ∏_{S₁} (1 - x) P(none of T)` whenever `|S₁ ∪ T| ≤ m`. -/
private lemma chain (hx1 : ∀ i, x i < 1)
    (m : ℕ)
    (hB : ∀ S : Finset ι, S.card < m → ∀ i, i ∉ S →
      μ.prob (E i ∩ noneOf E S) ≤ x i * μ.prob (noneOf E S))
    (T : Finset ι) (S₁ : Finset ι) :
    Disjoint S₁ T → (S₁ ∪ T).card ≤ m →
      (∏ j ∈ S₁, (1 - x j)) * μ.prob (noneOf E T) ≤ μ.prob (noneOf E (S₁ ∪ T)) := by
  induction S₁ using Finset.induction_on with
  | empty => intro _ _; simp
  | insert j S₁ hj ih =>
    intro hdisj hcard
    have hjT : j ∉ T := fun h => (disjoint_left.mp hdisj (mem_insert_self _ _)) h
    have hdisj' : Disjoint S₁ T := hdisj.mono_left (subset_insert _ _)
    have hjU : j ∉ S₁ ∪ T := by simp [hj, hjT]
    rw [insert_union] at hcard ⊢
    rw [card_insert_of_notMem hjU] at hcard
    have hlt : (S₁ ∪ T).card < m := by omega
    have h1 := hB _ hlt j hjU
    have h2 := ih hdisj' (by omega)
    rw [prob_noneOf_insert, prod_insert hj]
    have h3 : 0 ≤ 1 - x j := by linarith [hx1 j]
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]

variable (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
  (hP : ∀ i, μ.prob (E i) ≤ x i * ∏ j ∈ N i, (1 - x j))
include hx0 hx1 hP

/-- The inductive claim of the book's proof: `P(E | none of S) ≤ x(E)`, multiplicatively. -/
private lemma cond_bound (hind : LLLIndep μ E N) (S : Finset ι) :
    ∀ i, i ∉ S → μ.prob (E i ∩ noneOf E S) ≤ x i * μ.prob (noneOf E S) := by
  suffices H : ∀ m (S : Finset ι), S.card = m → ∀ i, i ∉ S →
      μ.prob (E i ∩ noneOf E S) ≤ x i * μ.prob (noneOf E S) from H _ S rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S hm i hi
  have hB : ∀ S' : Finset ι, S'.card < m → ∀ i, i ∉ S' →
      μ.prob (E i ∩ noneOf E S') ≤ x i * μ.prob (noneOf E S') :=
    fun S' h => ih _ h S' rfl
  set S₁ := S ∩ N i with hS₁
  set S₂ := S \ N i with hS₂
  have hS : S₁ ∪ S₂ = S := by
    rw [hS₁, hS₂]; ext ω; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hdis : Disjoint S₁ S₂ := by
    rw [hS₁, hS₂]; rw [disjoint_left]; intro ω h1 h2; simp only [mem_inter, mem_sdiff] at h1 h2; tauto
  have hiS₂ : i ∉ S₂ := fun h => hi (sdiff_subset h)
  have hdN : Disjoint S₂ (N i) := sdiff_disjoint
  have hch := chain hx1 m hB S₂ S₁ hdis (by rw [hS, hm])
  rw [hS] at hch
  have hsub : S₂ ⊆ S := sdiff_subset
  have hprod : ∏ j ∈ N i, (1 - x j) ≤ ∏ j ∈ S₁, (1 - x j) :=
    prod_le_prod_of_subset_of_le_one₀ inter_subset_right
      (fun j _ => by linarith [hx1 j]) (fun j _ _ => by linarith [hx0 j])
  have hnn : 0 ≤ μ.prob (noneOf E S₂) := μ.prob_nonneg _
  calc μ.prob (E i ∩ noneOf E S)
      ≤ μ.prob (E i ∩ noneOf E S₂) :=
        μ.prob_mono (inter_subset_inter subset_rfl (noneOf_anti E hsub))
    _ = μ.prob (E i) * μ.prob (noneOf E S₂) := hind i S₂ hiS₂ hdN
    _ ≤ (x i * ∏ j ∈ N i, (1 - x j)) * μ.prob (noneOf E S₂) :=
        mul_le_mul_of_nonneg_right (hP i) hnn
    _ ≤ (x i * ∏ j ∈ S₁, (1 - x j)) * μ.prob (noneOf E S₂) := by
        gcongr
        exact (hx0 i).le
    _ = x i * ((∏ j ∈ S₁, (1 - x j)) * μ.prob (noneOf E S₂)) := by ring
    _ ≤ x i * μ.prob (noneOf E S) := mul_le_mul_of_nonneg_left hch (hx0 i).le

/-- CO-255. Lovász Local Lemma, asymmetric form (Lemma 16.14): if `E i` is independent of the
complements `E j` for `j` outside `N i`, and `P(E i) ≤ x i ∏_{j ∈ N i} (1 - x j)` with
`0 < x i < 1`, then for every finite set `S` of indices
`P(no `E j`, `j ∈ S`, occurs) ≥ ∏_{j ∈ S} (1 - x j)`. -/
@[kb "kellertrotter2017" "Lemma 16.14, p. 350"]
theorem lovasz_local_lemma (hind : LLLIndep μ E N) (S : Finset ι) :
    ∏ j ∈ S, (1 - x j) ≤ μ.prob (noneOf E S) := by
  have hB := cond_bound hx0 hx1 hP hind
  have := chain hx1 (S.card + 1) (fun S' h i hi => hB S' i hi) ∅ S
    (disjoint_empty_right _) (by simp)
  simpa [noneOf_empty, prob_univ] using this

/-- CO-255 (the "in particular"): with positive probability none of the events occurs. -/
@[kb "kellertrotter2017" "Lemma 16.14, p. 350"]
theorem lovasz_local_lemma_pos (hind : LLLIndep μ E N) (S : Finset ι) :
    0 < μ.prob (noneOf E S) :=
  lt_of_lt_of_le (prod_pos fun j _ => by linarith [hx1 j])
    (lovasz_local_lemma hx0 hx1 hP hind S)

omit hx0 hx1 hP

/-- `e⁻¹ ≤ (1 - 1/(d+1))^d`. -/
lemma inv_exp_le_pow (d : ℕ) : (Real.exp 1)⁻¹ ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
    exact (inv_le_one_iff₀.mpr (Or.inr (Real.one_le_exp zero_le_one)))
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by
    calc (1 + 1 / (d : ℝ)) ^ d ≤ (Real.exp (1 / d)) ^ d := by
          gcongr
          linarith [Real.add_one_le_exp (1 / (d : ℝ))]
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h2 : (1 - 1 / ((d : ℝ) + 1)) ^ d * (1 + 1 / (d : ℝ)) ^ d = 1 := by
    rw [← mul_pow]
    have : (1 - 1 / ((d : ℝ) + 1)) * (1 + 1 / (d : ℝ)) = 1 := by
      field_simp; ring
    rw [this, one_pow]
  have h3 : 0 ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
  nlinarith [mul_le_mul_of_nonneg_left h1 h3]

/-- CO-256. Lovász Local Lemma, symmetric form (Lemma 16.15): if every `P(E i) ≤ p`, every
neighbourhood has at most `d ≥ 1` elements and `e p (d+1) ≤ 1` (the book assumes `< 1`, which
implies this), then `P(no `E j`, `j ∈ S`, occurs) ≥ (1 - 1/(d+1))^|S| > 0`. -/
@[kb "kellertrotter2017" "Lemma 16.15, p. 352"]
theorem lovasz_local_lemma_symmetric (hind : LLLIndep μ E N) (p : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hp : ∀ i, μ.prob (E i) ≤ p) (hN : ∀ i, (N i).card ≤ d)
    (he : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) (S : Finset ι) :
    (1 - 1 / ((d : ℝ) + 1)) ^ S.card ≤ μ.prob (noneOf E S) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < 1 / ((d : ℝ) + 1) := by positivity
  have hx1 : 1 / ((d : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hP : ∀ i, μ.prob (E i) ≤ (fun _ => 1 / ((d : ℝ) + 1)) i *
      ∏ j ∈ N i, (1 - (fun _ => 1 / ((d : ℝ) + 1)) j) := by
    intro i
    simp only [prod_const]
    have h1 : (1 - 1 / ((d : ℝ) + 1)) ^ d ≤ (1 - 1 / ((d : ℝ) + 1)) ^ (N i).card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (hN i)
    have h2 : p ≤ 1 / ((d : ℝ) + 1) * (Real.exp 1)⁻¹ := by
      rw [show 1 / ((d : ℝ) + 1) * (Real.exp 1)⁻¹ = 1 / (Real.exp 1 * ((d : ℝ) + 1)) by
        field_simp, le_div_iff₀ (by positivity)]
      linarith
    calc μ.prob (E i) ≤ p := hp i
      _ ≤ 1 / ((d : ℝ) + 1) * (Real.exp 1)⁻¹ := h2
      _ ≤ 1 / ((d : ℝ) + 1) * (1 - 1 / ((d : ℝ) + 1)) ^ d :=
          mul_le_mul_of_nonneg_left (inv_exp_le_pow d) hx0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hx0.le
  have := lovasz_local_lemma (x := fun _ => 1 / ((d : ℝ) + 1)) (fun _ => hx0) (fun _ => hx1) hP hind S
  simpa using this

/-- CO-256 (positivity). Under the hypotheses of the symmetric Local Lemma, with positive
probability no event occurs. -/
@[kb "kellertrotter2017" "Lemma 16.15, p. 352"]
theorem lovasz_local_lemma_symmetric_pos (hind : LLLIndep μ E N) (p : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hp : ∀ i, μ.prob (E i) ≤ p) (hN : ∀ i, (N i).card ≤ d)
    (he : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) (S : Finset ι) :
    0 < μ.prob (noneOf E S) := by
  refine lt_of_lt_of_le (pow_pos ?_ _) (lovasz_local_lemma_symmetric hind p d hd hp hN he S)
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [sub_pos, div_lt_one (by positivity)]
  linarith

/-- CO-257. The `4pd` variant of the symmetric Local Lemma (text, p. 352): if every `P(E i) ≤ p`,
every neighbourhood has at most `d ≥ 1` elements and `4 p d ≤ 1`, then
`P(no `E j`, `j ∈ S`, occurs) ≥ (1 - 1/(2d))^|S| > 0`. -/
@[kb "kellertrotter2017" "text, p. 352"]
theorem lovasz_local_lemma_four_pd (hind : LLLIndep μ E N) (p : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hp : ∀ i, μ.prob (E i) ≤ p) (hN : ∀ i, (N i).card ≤ d)
    (he : 4 * p * d ≤ 1) (S : Finset ι) :
    0 < (1 - 1 / (2 * (d : ℝ))) ^ S.card ∧
      (1 - 1 / (2 * (d : ℝ))) ^ S.card ≤ μ.prob (noneOf E S) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < 1 / (2 * (d : ℝ)) := by positivity
  have hx1 : 1 / (2 * (d : ℝ)) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hP : ∀ i, μ.prob (E i) ≤ (fun _ => 1 / (2 * (d : ℝ))) i *
      ∏ j ∈ N i, (1 - (fun _ => 1 / (2 * (d : ℝ))) j) := by
    intro i
    simp only [prod_const]
    have h1 : (1 - 1 / (2 * (d : ℝ))) ^ d ≤ (1 - 1 / (2 * (d : ℝ))) ^ (N i).card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (hN i)
    have hb := one_add_mul_le_pow (a := -(1 / (2 * (d : ℝ)))) (by linarith) d
    have hdx : (d : ℝ) * -(1 / (2 * (d : ℝ))) = -(1 / 2) := by field_simp
    rw [hdx, ← sub_eq_add_neg (1 : ℝ) (1 / (2 * (d : ℝ)))] at hb
    have h2 : p ≤ 1 / (2 * (d : ℝ)) * (1 / 2) := by
      rw [show 1 / (2 * (d : ℝ)) * (1 / 2) = 1 / (4 * d) by field_simp; ring,
        le_div_iff₀ (by positivity)]
      linarith
    calc μ.prob (E i) ≤ p := hp i
      _ ≤ 1 / (2 * (d : ℝ)) * (1 / 2) := h2
      _ ≤ 1 / (2 * (d : ℝ)) * (1 - 1 / (2 * (d : ℝ))) ^ d :=
          mul_le_mul_of_nonneg_left (by linarith) hx0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hx0.le
  have h := lovasz_local_lemma (x := fun _ => 1 / (2 * (d : ℝ))) (fun _ => hx0) (fun _ => hx1) hP hind S
  simp only [prod_const] at h
  exact ⟨pow_pos (by linarith) _, h⟩

end UndergradKB.Combinatorics.Probability
