import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import UndergradKB.Common.Attr
import UndergradKB.Probability.RandomWalk
import UndergradKB.Probability.ArcSine

/-! # Probability: the first maximum of a symmetric random walk (Grinstead–Snell, Theorem 12.6)

Let `X_0, X_1, ...` be independent real random variables with a common law `μ` that is continuous (no atoms)
and symmetric (`-X` has the law of `X`), and `S_k = X_0 + ⋯ + X_{k-1}`. The index `K_n` of the first maximum of
`S_0, ..., S_n` is the unique `k ≤ n` with `S_j < S_k` for `j < k` and `S_j ≤ S_k` for `k < j ≤ n`.

Theorem 12.6: `P(K_n < nα) → (2/π) arcsin √α`. The book states it without proof (citing Feller). We prove the
exact law `P(K_n = k) = u_{2k} u_{2n-2k}` (the discrete arc sine law of the simple walk, `u_{2k} = C(2k,k)/4^k`)
and deduce the limit from the arc sine limit of `ArcSine.lean`. The proof avoids Sparre Andersen's combinatorial
lemma:

* `{K_n = k}` is the intersection of an event of `X_0..X_{k-1}` (`S_j < S_k`, `j < k`) and an independent event of
  `X_k..X_{n-1}` (`S_j - S_k ≤ 0`, `k < j ≤ n`);
* reversing the first block (exchangeability) gives probability `q_k = P(S_1 > 0, ..., S_k > 0)` to the first,
  and the second has probability `P(S_1 ≤ 0, ..., S_{n-k} ≤ 0) = q_{n-k}` (continuity: ties have probability `0`;
  symmetry: change the signs);
* since `K_n` takes exactly one value, `Σ_{k=0}^n q_k q_{n-k} = 1` for every `n`, with `q_0 = 1`; this recursion
  has the unique solution `q_k = C(2k,k)/4^k`, which satisfies it by `c_conv`. -/

open MeasureTheory ProbabilityTheory Finset Filter Topology Real
open scoped ENNReal

namespace UndergradKB.Probability

namespace FirstMax

/-! ## Partial sums on vectors -/

/-- `Σ_{i < j} x_i` for a vector `x : Fin m → ℝ`. -/
def psum {m : ℕ} (x : Fin m → ℝ) (j : ℕ) : ℝ := ∑ i : Fin m, if (i : ℕ) < j then x i else 0

theorem measurable_psum (m j : ℕ) : Measurable fun x : Fin m → ℝ => psum x j := by
  unfold psum
  refine Finset.measurable_sum _ fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · simp only [h, ite_true]; exact measurable_pi_apply i
  · simp only [h, ite_false]; exact measurable_const

theorem psum_eq {m : ℕ} (g : ℕ → ℝ) {j : ℕ} (hj : j ≤ m) :
    psum (fun i : Fin m => g i) j = ∑ i ∈ range j, g i := by
  unfold psum
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then g i else 0) m, ← sum_filter]
  congr 1
  ext i; simp only [mem_filter, mem_range]; omega

/-- Vectors whose partial sums `Σ_{i<j} x_i`, `1 ≤ j ≤ m`, are all positive. -/
def posSet (m : ℕ) : Set (Fin m → ℝ) := {x | ∀ j, 1 ≤ j → j ≤ m → 0 < psum x j}

/-- Vectors whose partial sums `Σ_{i<j} x_i`, `1 ≤ j ≤ m`, are all `≤ 0`. -/
def nonposSet (m : ℕ) : Set (Fin m → ℝ) := {x | ∀ j, 1 ≤ j → j ≤ m → psum x j ≤ 0}

theorem measurableSet_posSet (m : ℕ) : MeasurableSet (posSet m) := by
  have : posSet m = ⋂ j, ⋂ (_ : 1 ≤ j), ⋂ (_ : j ≤ m), {x | 0 < psum x j} := by
    ext x; simp [posSet]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (measurable_psum m j)

theorem measurableSet_nonposSet (m : ℕ) : MeasurableSet (nonposSet m) := by
  have : nonposSet m = ⋂ j, ⋂ (_ : 1 ≤ j), ⋂ (_ : j ≤ m), {x | psum x j ≤ 0} := by
    ext x; simp [nonposSet]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_psum m j) measurable_const

/-! ## The walk -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The partial sum `S_k = X_0 + ⋯ + X_{k-1}`. -/
def S (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range k, X i ω

theorem measurable_S {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (k : ℕ) : Measurable (S X k) :=
  Finset.measurable_sum _ fun i _ => hX i

/-- `k` is the index of the first maximum of `S_0, ..., S_n`. -/
def IsFirstMax (X : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : Prop :=
  k ≤ n ∧ (∀ j < k, S X j ω < S X k ω) ∧ ∀ j, k < j → j ≤ n → S X j ω ≤ S X k ω

theorem exists_isFirstMax (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ∃ k, IsFirstMax X n k ω := by
  classical
  obtain ⟨j0, hj0, hmax⟩ := exists_max_image (range (n + 1)) (fun j => S X j ω) ⟨0, by simp⟩
  have hex : ∃ k, k ≤ n ∧ S X k ω = S X j0 ω := ⟨j0, Nat.lt_succ_iff.1 (mem_range.1 hj0), rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun j hj => ?_, fun j _ hjn => ?_⟩
  · have hjn : j ≤ n := hj.le.trans (Nat.find_spec hex).1
    have hle : S X j ω ≤ S X j0 ω := hmax j (mem_range.2 (Nat.lt_succ_of_le hjn))
    have hne : S X j ω ≠ S X j0 ω := fun h => Nat.find_min hex hj ⟨hjn, h⟩
    rw [(Nat.find_spec hex).2]
    exact lt_of_le_of_ne hle hne
  · rw [(Nat.find_spec hex).2]
    exact hmax j (mem_range.2 (Nat.lt_succ_of_le hjn))

theorem isFirstMax_unique {X : ℕ → Ω → ℝ} {n k k' : ℕ} {ω : Ω} (h : IsFirstMax X n k ω)
    (h' : IsFirstMax X n k' ω) : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h.2.2 k' hlt h'.1) (not_le.2 (h'.2.1 k hlt))
  · exact absurd (h'.2.2 k hlt h.1) (not_le.2 (h.2.1 k' hlt))

/-- `K_n`, the index of the first maximum of `S_0, ..., S_n`. -/
noncomputable def firstMaxIndex (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ := by
  classical exact Nat.find (exists_isFirstMax X n ω)

theorem firstMaxIndex_eq_iff (X : ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    firstMaxIndex X n ω = k ↔ IsFirstMax X n k ω := by
  classical
  have hs : IsFirstMax X n (firstMaxIndex X n ω) ω := by
    unfold firstMaxIndex; convert Nat.find_spec (exists_isFirstMax X n ω)
  exact ⟨fun h => h ▸ hs, fun h => isFirstMax_unique hs h⟩

theorem firstMaxIndex_le (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : firstMaxIndex X n ω ≤ n :=
  ((firstMaxIndex_eq_iff X n _ ω).1 rfl).1

/-! ## Events of the walk as events of vectors -/

/-- Reversing the first block: `Σ_{i<j} X_{k-1-i} = S_k - S_{k-j}`. -/
theorem sum_reflect (X : ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) :
    ∀ j, j ≤ k → ∑ i ∈ range j, X (k - 1 - i) ω = S X k ω - S X (k - j) ω := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [sum_range_succ, ih (by omega)]
    have e : k - j = (k - (j + 1)) + 1 := by omega
    have e2 : k - 1 - j = k - (j + 1) := by omega
    simp only [S]
    rw [e, sum_range_succ, e2]
    ring

theorem prefix_eq (X : ℕ → Ω → ℝ) (k : ℕ) :
    {ω | (fun i : Fin k => X (k - 1 - i) ω) ∈ posSet k} = {ω | ∀ j < k, S X j ω < S X k ω} := by
  ext ω
  simp only [Set.mem_setOf_eq, posSet]
  constructor
  · intro h j hj
    have := h (k - j) (by omega) (by omega)
    rw [psum_eq (fun i => X (k - 1 - i) ω) (by omega), sum_reflect X ω k _ (by omega)] at this
    rw [show k - (k - j) = j by omega] at this
    linarith
  · intro h j hj1 hjk
    rw [psum_eq (fun i => X (k - 1 - i) ω) hjk, sum_reflect X ω k _ hjk]
    have := h (k - j) (by omega)
    linarith

theorem suffix_eq (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) :
    {ω | (fun i : Fin (n - k) => X (k + i) ω) ∈ nonposSet (n - k)} =
      {ω | ∀ j, k < j → j ≤ n → S X j ω ≤ S X k ω} := by
  ext ω
  simp only [Set.mem_setOf_eq, nonposSet]
  have key : ∀ j, j ≤ n - k → psum (fun i : Fin (n - k) => X (k + i) ω) j = S X (k + j) ω - S X k ω := by
    intro j hj
    rw [psum_eq (fun i => X (k + i) ω) hj, S, S, sum_range_add]
    ring
  constructor
  · intro h j hkj hjn
    have := h (j - k) (by omega) (by omega)
    rw [key _ (by omega), show k + (j - k) = j by omega] at this
    linarith
  · intro h j hj1 hjn
    rw [key _ hjn]
    have := h (k + j) (by omega) (by omega)
    linarith

theorem pos_eq (X : ℕ → Ω → ℝ) (m : ℕ) :
    {ω | (fun i : Fin m => X i ω) ∈ posSet m} = {ω | ∀ j, 1 ≤ j → j ≤ m → 0 < S X j ω} := by
  ext ω
  simp only [Set.mem_setOf_eq, posSet]
  refine forall_congr' fun j => imp_congr_right fun _ => forall_congr' fun hj => ?_
  rw [psum_eq (fun i => X i ω) hj]; rfl

theorem neg_eq (X : ℕ → Ω → ℝ) (m : ℕ) :
    {ω | (fun i : Fin m => -X i ω) ∈ posSet m} = {ω | ∀ j, 1 ≤ j → j ≤ m → S X j ω < 0} := by
  ext ω
  simp only [Set.mem_setOf_eq, posSet]
  refine forall_congr' fun j => imp_congr_right fun _ => forall_congr' fun hj => ?_
  rw [psum_eq (fun i => -X i ω) hj, sum_neg_distrib, S]
  constructor <;> intro h <;> linarith

theorem nonpos_eq (X : ℕ → Ω → ℝ) (m : ℕ) :
    {ω | (fun i : Fin m => X i ω) ∈ nonposSet m} = {ω | ∀ j, 1 ≤ j → j ≤ m → S X j ω ≤ 0} := by
  ext ω
  simp only [Set.mem_setOf_eq, nonposSet]
  refine forall_congr' fun j => imp_congr_right fun _ => forall_congr' fun hj => ?_
  rw [psum_eq (fun i => X i ω) hj]; rfl

/-! ## Probabilities -/

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Two independent families of `m` random variables with the same marginal laws have the same joint law. -/
theorem prob_eq_of_iid {m : ℕ} (Y Z : Fin m → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hZ : ∀ i, Measurable (Z i))
    (hiY : iIndepFun Y P) (hiZ : iIndepFun Z P) (hlaw : ∀ i, P.map (Y i) = P.map (Z i))
    {C : Set (Fin m → ℝ)} (hC : MeasurableSet C) :
    P {ω | (fun i => Y i ω) ∈ C} = P {ω | (fun i => Z i ω) ∈ C} := by
  have h1 := (iIndepFun_iff_map_fun_eq_pi_map fun i => (hY i).aemeasurable).1 hiY
  have h2 := (iIndepFun_iff_map_fun_eq_pi_map fun i => (hZ i).aemeasurable).1 hiZ
  have e1 : P {ω | (fun i => Y i ω) ∈ C} = P.map (fun ω i => Y i ω) C :=
    (Measure.map_apply (measurable_pi_iff.2 hY) hC).symm
  have e2 : P {ω | (fun i => Z i ω) ∈ C} = P.map (fun ω i => Z i ω) C :=
    (Measure.map_apply (measurable_pi_iff.2 hZ) hC).symm
  rw [e1, e2, h1, h2]
  simp_rw [hlaw]

variable {X : ℕ → Ω → ℝ} {μ : Measure ℝ}

/-- `q_m = P(S_1 > 0, ..., S_m > 0)`. -/
def q (P : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℕ) : ℝ≥0∞ := P {ω | ∀ j, 1 ≤ j → j ≤ m → 0 < S X j ω}

theorem prefix_prob (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (k : ℕ) : P {ω | ∀ j < k, S X j ω < S X k ω} = q P X k := by
  rw [← prefix_eq, q, ← pos_eq]
  have hinj : Function.Injective fun i : Fin k => k - 1 - (i : ℕ) := by
    intro a b h; ext; simp only at h; omega
  exact prob_eq_of_iid (fun i : Fin k => X (k - 1 - i)) (fun i : Fin k => X i) (fun i => hX _) (fun i => hX _)
    (hind.precomp hinj) (hind.precomp Fin.val_injective) (fun i => by rw [hlaw, hlaw])
    (measurableSet_posSet k)

theorem suffix_prob (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    {n k : ℕ} (hk : k ≤ n) :
    P {ω | ∀ j, k < j → j ≤ n → S X j ω ≤ S X k ω} = P {ω | ∀ j, 1 ≤ j → j ≤ n - k → S X j ω ≤ 0} := by
  rw [← suffix_eq X hk, ← nonpos_eq]
  have hinj : Function.Injective fun i : Fin (n - k) => k + (i : ℕ) := by
    intro a b h; ext; simp only at h; omega
  exact prob_eq_of_iid (fun i : Fin (n - k) => X (k + i)) (fun i : Fin (n - k) => X i) (fun i => hX _)
    (fun i => hX _) (hind.precomp hinj) (hind.precomp Fin.val_injective) (fun i => by rw [hlaw, hlaw])
    (measurableSet_nonposSet _)

/-- Ties have probability zero: `P(S_j = 0) = 0` for `j ≥ 1` when the common law has no atoms. -/
theorem prob_S_eq_zero (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (hcont : ∀ x, μ {x} = 0) {j : ℕ} (hj : 1 ≤ j) : P {ω | S X j ω = 0} = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hSm : (∑ i ∈ range m, X i) = S X m := by funext ω; simp [S, Finset.sum_apply]
  have hindep : IndepFun (S X m) (X m) P := by
    rw [← hSm]; exact hind.indepFun_finsetSum_of_notMem hX (by simp)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map (measurable_S hX m).aemeasurable
    (hX m).aemeasurable).1 hindep
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 = 0} :=
    measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const
  have e : {ω | S X (m + 1) ω = 0} = (fun ω => (S X m ω, X m ω)) ⁻¹' {p : ℝ × ℝ | p.1 + p.2 = 0} := by
    ext ω; simp [S, sum_range_succ]
  rw [e, ← Measure.map_apply ((measurable_S hX m).prodMk (hX m)) hset, hprod,
    Measure.prod_apply hset]
  have : ∀ a : ℝ, Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 + p.2 = 0} = {-a} := by
    intro a; ext b; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor <;> intro h <;> linarith
  simp_rw [this, hlaw, hcont]
  simp

/-- `P(S_1 ≤ 0, ..., S_m ≤ 0) = q_m` for a continuous symmetric law. -/
theorem nonpos_prob (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (hcont : ∀ x, μ {x} = 0) (hsymm : μ.map (fun x => -x) = μ) (m : ℕ) :
    P {ω | ∀ j, 1 ≤ j → j ≤ m → S X j ω ≤ 0} = q P X m := by
  have hnz : ∀ᵐ ω ∂P, ∀ j, 1 ≤ j → S X j ω ≠ 0 := by
    rw [ae_all_iff]; intro j
    by_cases hj : 1 ≤ j
    · have h0 := prob_S_eq_zero hX hind hlaw hcont hj
      rw [← compl_compl {ω | S X j ω = 0}] at h0
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω _
      simpa using hω
    · exact Eventually.of_forall fun ω h => absurd h hj
  have h1 : P {ω | ∀ j, 1 ≤ j → j ≤ m → S X j ω ≤ 0} = P {ω | ∀ j, 1 ≤ j → j ≤ m → S X j ω < 0} := by
    refine measure_congr ?_
    filter_upwards [hnz] with ω hω
    change (∀ j, 1 ≤ j → j ≤ m → S X j ω ≤ 0) = (∀ j, 1 ≤ j → j ≤ m → S X j ω < 0)
    apply propext
    constructor
    · intro h j hj hjm; exact lt_of_le_of_ne (h j hj hjm) (hω j hj)
    · intro h j hj hjm; exact (h j hj hjm).le
  rw [h1, ← neg_eq, q, ← pos_eq]
  refine prob_eq_of_iid (fun i : Fin m => fun ω => -X i ω) (fun i : Fin m => X i) (fun i => (hX _).neg)
    (fun i => hX _) ?_ (hind.precomp Fin.val_injective) (fun i => ?_) (measurableSet_posSet m)
  · exact (hind.precomp Fin.val_injective).comp (fun _ x => -x) (fun _ => measurable_neg)
  · have : (fun ω => -X i ω) = (fun x => -x) ∘ X i := rfl
    rw [this, ← Measure.map_map measurable_neg (hX _), hlaw]
    exact hsymm

theorem firstMax_set_eq (X : ℕ → Ω → ℝ) {n k : ℕ} (hk : k ≤ n) :
    {ω | IsFirstMax X n k ω} =
      {ω | ∀ j < k, S X j ω < S X k ω} ∩ {ω | ∀ j, k < j → j ≤ n → S X j ω ≤ S X k ω} := by
  ext ω; simp [IsFirstMax, hk]

/-- `P(K_n = k) = q_k q_{n-k}`. -/
theorem firstMax_prob_q (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (hcont : ∀ x, μ {x} = 0) (hsymm : μ.map (fun x => -x) = μ) {n k : ℕ} (hk : k ≤ n) :
    P {ω | IsFirstMax X n k ω} = q P X k * q P X (n - k) := by
  rw [firstMax_set_eq X hk, ← prefix_prob hX hind hlaw k, ← nonpos_prob hX hind hlaw hcont hsymm (n - k),
    ← suffix_prob hX hind hlaw hk, ← prefix_eq, ← suffix_eq X hk]
  -- independence of the two blocks
  have hST : Disjoint (range k) (Ico k n) := by
    rw [Finset.disjoint_left]; intro a ha hb; simp only [mem_range, mem_Ico] at ha hb; omega
  have hI := hind.indepFun_finset (range k) (Ico k n) hST hX
  have hφ : Measurable fun v : (range k) → ℝ => fun i : Fin k =>
      v ⟨k - 1 - i, mem_range.2 (by omega)⟩ :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hψ : Measurable fun v : (Ico k n) → ℝ => fun i : Fin (n - k) =>
      v ⟨k + i, mem_Ico.2 ⟨by omega, by omega⟩⟩ :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  exact (hI.comp hφ hψ).measure_inter_preimage_eq_mul _ _ (measurableSet_posSet k)
    (measurableSet_nonposSet (n - k))

theorem measurableSet_isFirstMax (hX : ∀ i, Measurable (X i)) (n k : ℕ) :
    MeasurableSet {ω | IsFirstMax X n k ω} := by
  by_cases hk : k ≤ n
  · rw [firstMax_set_eq X hk]
    refine MeasurableSet.inter ?_ ?_
    · have : {ω | ∀ j < k, S X j ω < S X k ω} = ⋂ j, ⋂ (_ : j < k), {ω | S X j ω < S X k ω} := by
        ext; simp
      rw [this]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_lt (measurable_S hX j) (measurable_S hX k)
    · have : {ω | ∀ j, k < j → j ≤ n → S X j ω ≤ S X k ω} =
          ⋂ j, ⋂ (_ : k < j), ⋂ (_ : j ≤ n), {ω | S X j ω ≤ S X k ω} := by
        ext; simp
      rw [this]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
        measurableSet_le (measurable_S hX j) (measurable_S hX k)
  · have : {ω | IsFirstMax X n k ω} = ∅ := by ext ω; simp [IsFirstMax, hk]
    rw [this]; exact MeasurableSet.empty

/-- The events `{K_n = k}`, `k ≤ n`, partition the sample space. -/
theorem sum_firstMax_prob (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    ∑ k ∈ range (n + 1), P {ω | IsFirstMax X n k ω} = 1 := by
  rw [← measure_biUnion_finset]
  · have : (⋃ k ∈ range (n + 1), {ω | IsFirstMax X n k ω}) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, mem_range, Set.mem_univ, iff_true]
      obtain ⟨k, hk⟩ := exists_isFirstMax X n ω
      exact ⟨k, Nat.lt_succ_of_le hk.1, hk⟩
    rw [this, measure_univ]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro ω ha hb
    exact hab (isFirstMax_unique ha hb)
  · exact fun k _ => measurableSet_isFirstMax hX n k

/-! ## Solving the convolution equation -/

/-- A sequence with `a_0 = 1` and `Σ_{k=0}^n a_k a_{n-k} = 1` for all `n` is determined by these equations. -/
theorem conv_unique (a b : ℕ → ℝ) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ n, ∑ k ∈ range (n + 1), a k * a (n - k) = 1) (hb : ∀ n, ∑ k ∈ range (n + 1), b k * b (n - k) = 1) :
    ∀ n, a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [ha0, hb0]
    · have hA := ha (m + 1)
      have hB := hb (m + 1)
      rw [sum_range_succ, sum_range_succ'] at hA hB
      have hmid : ∑ k ∈ range m, a (k + 1) * a (m + 1 - (k + 1)) =
          ∑ k ∈ range m, b (k + 1) * b (m + 1 - (k + 1)) := by
        refine sum_congr rfl fun k hk => ?_
        have hk' := mem_range.1 hk
        rw [ih (k + 1) (by omega), ih (m + 1 - (k + 1)) (by omega)]
      simp only [Nat.sub_zero, Nat.sub_self] at hA hB
      rw [ha0] at hA; rw [hb0] at hB
      linarith

theorem q_zero : q P X 0 = 1 := by
  have : {ω : Ω | ∀ j, 1 ≤ j → j ≤ 0 → 0 < S X j ω} = Set.univ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro j h1 h2; omega
  rw [q, this, measure_univ]

/-- `q_k = u_{2k} = C(2k,k)/4^k`. -/
theorem q_eq_c (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (hcont : ∀ x, μ {x} = 0) (hsymm : μ.map (fun x => -x) = μ) (k : ℕ) :
    (q P X k).toReal = ((c k : ℚ) : ℝ) := by
  refine conv_unique (fun k => (q P X k).toReal) (fun k => ((c k : ℚ) : ℝ)) ?_ ?_ ?_ ?_ k
  · simp [q_zero]
  · simp [c_zero]
  · intro n
    have h := congrArg ENNReal.toReal (sum_firstMax_prob (P := P) hX n)
    rw [ENNReal.toReal_sum (fun k _ => measure_ne_top _ _), ENNReal.toReal_one] at h
    rw [← h]
    refine sum_congr rfl fun k hk => ?_
    rw [firstMax_prob_q hX hind hlaw hcont hsymm (Nat.lt_succ_iff.1 (mem_range.1 hk)),
      ENNReal.toReal_mul]
  · intro n
    have := congrArg (Rat.cast : ℚ → ℝ) (c_conv n)
    push_cast at this
    exact this

end FirstMax

open FirstMax

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ} {μ : Measure ℝ}

/-- Grinstead–Snell Theorem 12.6 (PR-129), exact law. For independent steps with a common continuous
symmetric law, the index `K_n` of the first maximum of `S_0, ..., S_n` has the discrete arc sine law
`P(K_n = k) = u_{2k} u_{2n-2k}`, the same as for the simple walk (`u_{2k} = C(2k,k)/4^k`). -/
@[kb "grinsteadsnell2006" "Theorem 12.6, p. 504"]
theorem firstMaxIndex_prob (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (hcont : ∀ x, μ {x} = 0) (hsymm : μ.map (fun x => -x) = μ) {n k : ℕ} (hk : k ≤ n) :
    (P {ω | firstMaxIndex X n ω = k}).toReal = (u (2 * k) : ℝ) * (u (2 * (n - k)) : ℝ) := by
  simp_rw [firstMaxIndex_eq_iff]
  rw [firstMax_prob_q hX hind hlaw hcont hsymm hk, ENNReal.toReal_mul, q_eq_c hX hind hlaw hcont hsymm,
    q_eq_c hX hind hlaw hcont hsymm, u_two_mul, u_two_mul]

theorem c_le_inv_sqrt (k : ℕ) : ((c k : ℚ) : ℝ) ≤ 1 / √(2 * (k : ℝ) + 1) := by
  have h := cR_sq_bound k
  have h0 := cR_nonneg k
  have hp : 0 < 2 * (k : ℝ) + 1 := by positivity
  rw [le_div_iff₀ (Real.sqrt_pos.2 hp)]
  have hs : √(2 * (k : ℝ) + 1) ^ 2 = 2 * (k : ℝ) + 1 := Real.sq_sqrt hp.le
  nlinarith [Real.sqrt_nonneg (2 * (k : ℝ) + 1), sq_nonneg (((c k : ℚ) : ℝ) * √(2 * (k : ℝ) + 1) - 1)]

theorem c_le_one (k : ℕ) : ((c k : ℚ) : ℝ) ≤ 1 := by
  refine (c_le_inv_sqrt k).trans ?_
  rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
  exact Real.one_le_sqrt.2 (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

/-- Grinstead–Snell Theorem 12.6 (PR-129). For independent steps with a common continuous symmetric law
and `0 < α < 1`, the probability that the first maximum of `S_0, ..., S_n` occurs before time `nα` tends to
`(2/π) arcsin √α`. -/
@[kb "grinsteadsnell2006" "Theorem 12.6, p. 504"]
theorem firstMaxIndex_tendsto (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = μ) (hcont : ∀ x, μ {x} = 0) (hsymm : μ.map (fun x => -x) = μ)
    (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    Tendsto (fun n : ℕ => (P {ω | (firstMaxIndex X n ω : ℝ) < n * α}).toReal) atTop
      (𝓝 ((2 / π) * Real.arcsin (√α))) := by
  have hmeas : ∀ n k, MeasurableSet {ω | firstMaxIndex X n ω = k} := fun n k => by
    simp_rw [firstMaxIndex_eq_iff]; exact measurableSet_isFirstMax hX n k
  -- `P(K_n < nα) = Σ_{k ≤ ⌊αn⌋} p_k - e_n` with `0 ≤ e_n ≤ c_{⌊αn⌋}`
  set w : ℕ → ℕ → ℝ := fun n k => ((c k : ℚ) : ℝ) * ((c (n - k) : ℚ) : ℝ) with hw
  have hprob : ∀ n k, k ≤ n → (P {ω | firstMaxIndex X n ω = k}).toReal = w n k := by
    intro n k hk
    rw [firstMaxIndex_prob hX hind hlaw hcont hsymm hk, u_two_mul, u_two_mul]
  -- `P(K_n < nα)` as a finite sum of the weights
  set T : ℕ → Finset ℕ := fun n => (range (n + 1)).filter fun k => (k : ℝ) < n * α with hT
  set R : ℕ → Finset ℕ := fun n => range (⌊α * n⌋₊ + 1) with hR
  have hG : ∀ n, (P {ω | (firstMaxIndex X n ω : ℝ) < n * α}).toReal = ∑ k ∈ T n, w n k := by
    intro n
    have hset : {ω | (firstMaxIndex X n ω : ℝ) < n * α} = ⋃ k ∈ T n, {ω | firstMaxIndex X n ω = k} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, hT, mem_filter, mem_range, exists_prop]
      constructor
      · intro h
        exact ⟨_, ⟨Nat.lt_succ_of_le (firstMaxIndex_le X n ω), h⟩, rfl⟩
      · rintro ⟨k, ⟨_, hk⟩, rfl⟩; exact hk
    rw [hset, measure_biUnion_finset _ fun k _ => hmeas n k, ENNReal.toReal_sum fun k _ => measure_ne_top _ _]
    · refine sum_congr rfl fun k hk => ?_
      simp only [hT, mem_filter, mem_range] at hk
      exact hprob n k (Nat.lt_succ_iff.1 hk.1)
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro ω ha hb
      exact hab ((Set.mem_setOf_eq ▸ ha).symm.trans hb)
  have hfloor_le : ∀ n : ℕ, ⌊α * n⌋₊ ≤ n := by
    intro n
    have : α * (n : ℝ) ≤ n := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact_mod_cast (Nat.floor_le (by positivity)).trans this
  have hsub : ∀ n, T n ⊆ R n := by
    intro n k hk
    simp only [hT, hR, mem_filter, mem_range] at hk ⊢
    exact Nat.lt_succ_of_le (Nat.le_floor (by rw [mul_comm]; exact hk.2.le))
  have hw0 : ∀ n k, 0 ≤ w n k := fun n k => mul_nonneg (cR_nonneg k) (cR_nonneg _)
  have hdiff : ∀ n, 0 ≤ (∑ k ∈ R n, w n k) - ∑ k ∈ T n, w n k ∧
      (∑ k ∈ R n, w n k) - ∑ k ∈ T n, w n k ≤ 1 / √(2 * (⌊α * n⌋₊ : ℝ) + 1) := by
    intro n
    rw [← sum_sdiff_eq_sub (hsub n)]
    refine ⟨sum_nonneg fun k _ => hw0 n k, ?_⟩
    have hsd : R n \ T n ⊆ {⌊α * n⌋₊} := by
      intro k hk
      rw [Finset.mem_sdiff] at hk
      simp only [hT, hR, mem_filter, mem_range, not_and, not_lt] at hk
      have h1 : k ≤ ⌊α * n⌋₊ := Nat.lt_succ_iff.1 hk.1
      have h2 : (n : ℝ) * α ≤ k := hk.2 (Nat.lt_succ_of_le (h1.trans (hfloor_le n)))
      have h3 : ⌊α * n⌋₊ ≤ k := Nat.floor_le_of_le (by rw [mul_comm]; exact h2)
      simp only [mem_singleton]; omega
    refine (sum_le_sum_of_subset_of_nonneg hsd fun k _ _ => hw0 n k).trans ?_
    rw [sum_singleton]
    exact (mul_le_of_le_one_right (cR_nonneg _) (c_le_one _)).trans (c_le_inv_sqrt _)
  have hinv : Tendsto (fun k : ℕ => 1 / √(2 * (k : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / (2 * (k : ℝ) + 1)) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      exact one_div_le_one_div_of_le (by positivity) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [Real.sqrt_div' 1 (by positivity : (0 : ℝ) ≤ 2 * k + 1), Real.sqrt_one]
  have hfl : Tendsto (fun n : ℕ => ⌊α * n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop h0)
  have hE : Tendsto (fun n : ℕ => (∑ k ∈ R n, w n k) - ∑ k ∈ T n, w n k) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hdiff n).1) (fun n => (hdiff n).2) (hinv.comp hfl)
  have hF : Tendsto (fun n : ℕ => ∑ k ∈ R n, w n k) atTop (𝓝 ((2 / π) * Real.arcsin (√α))) :=
    arcsine_sum_tendsto α h0 h1
  have := hF.sub hE
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  rw [hG]
  ring

end UndergradKB.Probability
