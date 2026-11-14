import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Real
import UndergradKB.Common.Attr

/-! # Compact locally connected metric spaces are uniformly locally path connected

This file prepares the Hahn-Mazurkiewicz theorem (Morris, *Topology Without Tears*, Theorem 9.5.12,
row TP-235). The key fact is the theorem of Mazurkiewicz, Moore and Menger in its uniform form: in a
compact, locally connected metric space, for every `ε > 0` there is `δ > 0` such that any two points
at distance less than `δ` are joined by a path staying within `ε` of the first point.

Proof (classical, by nested chains):
* uniform local connectedness: nearby points lie in a common connected set of small diameter
  (Lebesgue number lemma applied to the connected components of small balls);
* a connected set contains a `δ`-chain between any two of its points;
* a link `(p, q)` of stage `n` (with `dist p q < δₙ`) is refined into a `δₙ₊₁`-chain inside a connected
  set of radius `εₙ = ε₀ / 2ⁿ` around `p`; the stage-`m` "walk" `walk n m p q t` follows the refinements
  for `m` levels, reading the parameter `t ∈ [0,1]` in a mixed radix given by the chain lengths;
* the walks converge (geometric bound), the limit is continuous because at depth `m` every parameter
  has a neighbourhood mapped within `4 εₘ` of its value (glued from finitely many sub-intervals).
-/

open Set Filter Topology Metric

namespace UndergradKB.Topology
namespace HMPaths

variable {X : Type*} [MetricSpace X]

/-! ### Chains in connected sets -/

/-- `z` is a `δ`-chain of length `k ≥ 1` inside `s` from `x` to `y`. -/
def IsChain (s : Set X) (δ : ℝ) (x y : X) (k : ℕ) (z : ℕ → X) : Prop :=
  1 ≤ k ∧ z 0 = x ∧ z k = y ∧ (∀ i ≤ k, z i ∈ s) ∧ ∀ i < k, dist (z i) (z (i + 1)) < δ

/-- In a preconnected set any two points are joined by a `δ`-chain inside the set. -/
theorem exists_chain {s : Set X} (hs : IsPreconnected s) {δ : ℝ} (hδ : 0 < δ) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) : ∃ k z, IsChain s δ x y k z := by
  refine hs.induction₂ (fun a b => ∃ k z, IsChain s δ a b k z) ?_ ?_ ?_ hx hy
  · intro a ha
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hδ)]
      with b hbs hbb
    refine ⟨1, fun i => if i = 0 then a else b, le_rfl, by simp, by simp, ?_, ?_⟩
    · intro i hi
      by_cases h : i = 0 <;> simp [h, ha, hbs]
    · intro i hi
      have : i = 0 := by omega
      subst this
      simpa [dist_comm] using hbb
  · rintro a b c - - - ⟨k, z, hk1, hz0, hzk, hzs, hzd⟩ ⟨k', z', hk1', hz0', hzk', hzs', hzd'⟩
    refine ⟨k + k', fun i => if i ≤ k then z i else z' (i - k), by omega, by simp [hz0], ?_, ?_, ?_⟩
    · simp only
      simp only [show ¬ k + k' ≤ k by omega, ↓reduceIte]
      simpa using hzk'
    · intro i hi
      simp only
      split_ifs with h
      · exact hzs i h
      · exact hzs' _ (by omega)
    · intro i hi
      have key : ∀ j, k ≤ j → (if j ≤ k then z j else z' (j - k)) = z' (j - k) := by
        intro j hj
        split_ifs with h
        · have : j = k := le_antisymm h hj
          subst this
          simp [hzk, hz0']
        · rfl
      dsimp only
      by_cases h : i < k
      · simp only [show i ≤ k by omega, show i + 1 ≤ k by omega, ↓reduceIte]
        exact hzd i h
      · rw [key i (by omega), key (i + 1) (by omega)]
        have := hzd' (i - k) (by omega)
        rwa [show i - k + 1 = i + 1 - k by omega] at this
  · rintro a b - - ⟨k, z, hk1, hz0, hzk, hzs, hzd⟩
    refine ⟨k, fun i => z (k - i), hk1, by simp [hzk], by simp [hz0], ?_, ?_⟩
    · intro i hi
      exact hzs _ (by omega)
    · intro i hi
      have := hzd (k - (i + 1)) (by omega)
      rw [show k - (i + 1) + 1 = k - i by omega, dist_comm] at this
      exact this

/-! ### Uniform local connectedness -/

/-- In a compact locally connected metric space, nearby points lie in a common preconnected set
contained in a small closed ball around the first point. -/
theorem exists_preconnected_of_dist_lt [CompactSpace X] [LocallyConnectedSpace X] {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ p q : X, dist p q < δ →
      ∃ C : Set X, IsPreconnected C ∧ p ∈ C ∧ q ∈ C ∧ C ⊆ closedBall p ε := by
  let c : X → Set X := fun x => connectedComponentIn (ball x (ε / 2)) x
  have hco : ∀ x, IsOpen (c x) := fun x => isOpen_ball.connectedComponentIn
  have hcov : (univ : Set X) ⊆ ⋃ x, c x := fun x _ =>
    mem_iUnion.2 ⟨x, mem_connectedComponentIn (mem_ball_self (by positivity))⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hco hcov
  refine ⟨δ, hδ, fun p q hpq => ?_⟩
  obtain ⟨i, hi⟩ := hleb p (mem_univ p)
  refine ⟨c i, isPreconnected_connectedComponentIn, hi (mem_ball_self hδ),
    hi (by rw [mem_ball, dist_comm]; exact hpq), ?_⟩
  intro z hz
  have hzi : z ∈ ball i (ε / 2) := connectedComponentIn_subset _ _ hz
  have hpi : p ∈ ball i (ε / 2) := connectedComponentIn_subset _ _ (hi (mem_ball_self hδ))
  rw [mem_ball] at hzi hpi
  rw [mem_closedBall]
  calc dist z p ≤ dist z i + dist p i := dist_triangle_right _ _ _
    _ ≤ ε := by linarith

/-! ### The recursive walk -/

/-- Index of the sub-interval of `[0,1]` (cut into `k` equal parts) containing `t`. -/
noncomputable def idx (k : ℕ) (t : ℝ) : ℕ := min (⌊t * k⌋₊) (k - 1)

/-- Local parameter of `t` inside its sub-interval. -/
noncomputable def loc (k : ℕ) (t : ℝ) : ℝ := t * k - idx k t

theorem idx_lt {k : ℕ} (hk : 1 ≤ k) (t : ℝ) : idx k t < k := by
  unfold idx; omega

theorem idx_zero (k : ℕ) : idx k 0 = 0 := by simp [idx]

theorem loc_zero (k : ℕ) : loc k 0 = 0 := by simp [loc, idx]

theorem idx_one {k : ℕ} (hk : 1 ≤ k) : idx k 1 = k - 1 := by
  simp only [idx, one_mul, Nat.floor_natCast]; omega

theorem loc_one {k : ℕ} (hk : 1 ≤ k) : loc k 1 = 1 := by
  rw [loc, idx_one hk, Nat.cast_sub hk]; simp

/-- The point `t ∈ [0,1]` lies in the closed sub-interval number `idx k t`. -/
theorem mem_Icc_idx {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (idx k t : ℝ) ≤ t * k ∧ t * k ≤ idx k t + 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h0 : 0 ≤ t * k := mul_nonneg ht.1 (by linarith)
  by_cases h : ⌊t * k⌋₊ ≤ k - 1
  · have he : idx k t = ⌊t * k⌋₊ := by simp [idx, h]
    rw [he]
    exact ⟨Nat.floor_le h0, (Nat.lt_floor_add_one _).le⟩
  · have he : idx k t = k - 1 := by simp [idx]; omega
    have hge : (k : ℝ) ≤ t * k := by
      have : k ≤ ⌊t * k⌋₊ := by omega
      exact (Nat.le_floor_iff h0).1 this
    have htk : t * k ≤ k := by nlinarith [ht.2]
    rw [he, Nat.cast_sub hk]
    constructor <;> push_cast <;> linarith

theorem loc_mem {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    loc k t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := mem_Icc_idx hk ht
  rw [loc]; constructor <;> linarith

section Walk

variable (len : ℕ → X → X → ℕ) (pt : ℕ → X → X → ℕ → X)

/-- The stage-`m` walk along the refinements, starting at stage `n` with the link `(p, q)`. -/
noncomputable def walk : ℕ → ℕ → X → X → ℝ → X
  | _, 0, p, _, _ => p
  | n, m + 1, p, q, t =>
      walk (n + 1) m (pt n p q (idx (len n p q) t)) (pt n p q (idx (len n p q) t + 1))
        (loc (len n p q) t)

variable {len pt}

omit [MetricSpace X] in
theorem walk_succ (n m : ℕ) (p q : X) (t : ℝ) :
    walk len pt n (m + 1) p q t = walk len pt (n + 1) m (pt n p q (idx (len n p q) t))
      (pt n p q (idx (len n p q) t + 1)) (loc (len n p q) t) := rfl

omit [MetricSpace X] in
theorem walk_zero_param (h0 : ∀ n p q, pt n p q 0 = p) (n m : ℕ) (p q : X) :
    walk len pt n m p q 0 = p := by
  induction m generalizing n p q with
  | zero => rfl
  | succ m ih => rw [walk_succ, idx_zero, loc_zero, ih, h0]

/-- Standing hypotheses on the chain data, for a sequence of radii `eps` and of link bounds `del`. -/
structure Good (eps del : ℕ → ℝ) (len : ℕ → X → X → ℕ) (pt : ℕ → X → X → ℕ → X) : Prop where
  len_pos : ∀ n p q, 1 ≤ len n p q
  pt_zero : ∀ n p q, pt n p q 0 = p
  pt_last : ∀ n p q, dist p q < del n → pt n p q (len n p q) = q
  pt_near : ∀ n p q i, dist p q < del n → i ≤ len n p q → dist p (pt n p q i) ≤ eps n
  pt_step : ∀ n p q i, dist p q < del n → i < len n p q →
    dist (pt n p q i) (pt n p q (i + 1)) < del (n + 1)
  eps_succ : ∀ n, eps (n + 1) = eps n / 2
  del_le : ∀ n, del n ≤ eps n

variable {eps del : ℕ → ℝ} (hG : Good eps del len pt)
include hG

theorem walk_mem (n m : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) :
    dist p (walk len pt n m p q t) ≤ 2 * eps n := by
  induction m generalizing n p q t with
  | zero =>
    have : 0 ≤ eps n := le_trans dist_nonneg (hG.pt_near n p q 0 hpq (Nat.zero_le _))
    simp [walk]; linarith
  | succ m ih =>
    rw [walk_succ]
    have hi := idx_lt (hG.len_pos n p q) t
    have h1 := hG.pt_near n p q _ hpq hi.le
    have h2 := ih (n + 1) _ _ (hG.pt_step n p q _ hpq hi) (loc (len n p q) t)
    rw [hG.eps_succ] at h2
    calc _ ≤ _ := dist_triangle _ (pt n p q (idx (len n p q) t)) _
      _ ≤ 2 * eps n := by linarith

theorem walk_dist_succ (n m : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) :
    dist (walk len pt n m p q t) (walk len pt n (m + 1) p q t) ≤ eps n / 2 ^ m := by
  induction m generalizing n p q t with
  | zero =>
    rw [walk_succ]
    simp only [walk, pow_zero, div_one]
    exact hG.pt_near n p q _ hpq (idx_lt (hG.len_pos n p q) t).le
  | succ m ih =>
    rw [walk_succ, walk_succ (m := m + 1)]
    have hi := idx_lt (hG.len_pos n p q) t
    have := ih (n + 1) _ _ (hG.pt_step n p q _ hpq hi) (loc (len n p q) t)
    rw [hG.eps_succ, ← walk_succ] at this
    refine this.trans_eq ?_
    rw [pow_succ]
    ring

theorem walk_one_dist (n m : ℕ) (p q : X) (hpq : dist p q < del n) :
    dist (walk len pt n m p q 1) q ≤ eps n / 2 ^ m := by
  induction m generalizing n p q with
  | zero => simpa [walk] using (hpq.le.trans (hG.del_le n))
  | succ m ih =>
    have hk := hG.len_pos n p q
    rw [walk_succ, idx_one hk, loc_one hk]
    have hlt : len n p q - 1 < len n p q := by omega
    have := ih (n + 1) _ _ (hG.pt_step n p q _ hpq hlt)
    rw [show len n p q - 1 + 1 = len n p q by omega, hG.pt_last n p q hpq, hG.eps_succ] at this
    rw [show len n p q - 1 + 1 = len n p q by omega, hG.pt_last n p q hpq]
    refine this.trans_eq ?_
    rw [pow_succ]
    ring

/-! ### The limit path -/

variable [CompleteSpace X]

omit [CompleteSpace X] in
theorem walk_cauchy (n : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) :
    CauchySeq fun m => walk len pt n m p q t := by
  refine cauchySeq_of_le_geometric_two (C := 2 * eps n) fun m => ?_
  have := walk_dist_succ hG n m p q hpq t
  convert this using 1
  ring

variable [Nonempty X]

omit hG in
variable (len pt) in
/-- The limit of the walks. -/
noncomputable def lim (n : ℕ) (p q : X) (t : ℝ) : X :=
  limUnder atTop fun m => walk len pt n m p q t

theorem tendsto_walk (n : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) :
    Tendsto (fun m => walk len pt n m p q t) atTop (𝓝 (lim len pt n p q t)) :=
  (walk_cauchy hG n p q hpq t).tendsto_limUnder

theorem lim_zero (n : ℕ) (p q : X) (hpq : dist p q < del n) :
    lim len pt n p q 0 = p := by
  have := tendsto_walk hG n p q hpq 0
  simp only [walk_zero_param hG.pt_zero] at this
  exact (tendsto_nhds_unique tendsto_const_nhds this).symm

theorem lim_one (n : ℕ) (p q : X) (hpq : dist p q < del n) :
    lim len pt n p q 1 = q := by
  have h1 := tendsto_walk hG n p q hpq 1
  have h2 : Tendsto (fun m => walk len pt n m p q 1) atTop (𝓝 q) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun m => walk_one_dist hG n m p q hpq) ?_
    have : Tendsto (fun m : ℕ => eps n * (1 / 2) ^ m) atTop (𝓝 (eps n * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    simpa [div_eq_mul_inv] using this
  exact tendsto_nhds_unique h1 h2

theorem lim_mem (n : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) :
    dist p (lim len pt n p q t) ≤ 2 * eps n := by
  have h := tendsto_walk hG n p q hpq t
  have hc : IsClosed (closedBall p (2 * eps n)) := isClosed_closedBall
  have := hc.mem_of_tendsto h (Eventually.of_forall fun m => by
    rw [mem_closedBall, dist_comm]; exact walk_mem hG n m p q hpq t)
  rwa [mem_closedBall, dist_comm] at this

theorem lim_rec (n : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) :
    lim len pt n p q t = lim len pt (n + 1)
      (pt n p q (idx (len n p q) t)) (pt n p q (idx (len n p q) t + 1)) (loc (len n p q) t) := by
  have hi := idx_lt (hG.len_pos n p q) t
  have h1 := tendsto_walk hG n p q hpq t
  have h2 := tendsto_walk hG (n + 1) _ _ (hG.pt_step n p q _ hpq hi) (loc (len n p q) t)
  rw [← tendsto_add_atTop_iff_nat 1] at h1
  exact tendsto_nhds_unique h1 h2

/-- On the closed `i`-th sub-interval the limit is the sub-limit of the `i`-th link, in the
local parameter `t * k - i`. -/
theorem lim_eq_on_piece (n : ℕ) (p q : X) (hpq : dist p q < del n) {i : ℕ}
    (hi : i < len n p q) {t : ℝ} (ht1 : (i : ℝ) ≤ t * len n p q)
    (ht2 : t * len n p q ≤ i + 1) :
    lim len pt n p q t = lim len pt (n + 1) (pt n p q i)
      (pt n p q (i + 1)) (t * len n p q - i) := by
  have hk := hG.len_pos n p q
  have h0 : 0 ≤ t * len n p q := le_trans (Nat.cast_nonneg _) ht1
  rw [lim_rec hG n p q hpq t]
  by_cases hfl : t * len n p q < i + 1
  · have hfe : ⌊t * len n p q⌋₊ = i := (Nat.floor_eq_iff h0).2 ⟨ht1, hfl⟩
    have he : idx (len n p q) t = i := by simp only [idx, hfe]; omega
    rw [loc, he]
  · have heq : t * len n p q = i + 1 := le_antisymm ht2 (not_lt.1 hfl)
    have hstep := hG.pt_step n p q i hpq hi
    rw [heq, show (i : ℝ) + 1 - i = 1 by ring, lim_one hG _ _ _ hstep]
    have hfe : ⌊t * len n p q⌋₊ = i + 1 := by
      rw [heq]; exact_mod_cast Nat.floor_natCast (R := ℝ) (i + 1)
    by_cases hlast : i + 1 ≤ len n p q - 1
    · have he : idx (len n p q) t = i + 1 := by simp only [idx, hfe]; omega
      have hl : loc (len n p q) t = 0 := by rw [loc, he, heq]; push_cast; ring
      rw [he, hl, lim_zero hG _ _ _ (hG.pt_step n p q _ hpq (by omega))]
    · have he : idx (len n p q) t = i := by simp only [idx, hfe]; omega
      have hl : loc (len n p q) t = 1 := by rw [loc, he, heq]; ring
      rw [he, hl, lim_one hG _ _ _ hstep]

/-- Oscillation bound at depth `m`: every parameter has a neighbourhood in `[0,1]` mapped within
`4 εₙ₊ₘ` of its value. -/
theorem lim_osc (m n : ℕ) (p q : X) (hpq : dist p q < del n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t,
      dist (lim len pt n p q s) (lim len pt n p q t) ≤
        4 * eps (n + m) := by
  induction m generalizing n p q t with
  | zero =>
    refine Eventually.of_forall fun s => ?_
    have h1 := lim_mem hG n p q hpq s
    have h2 := lim_mem hG n p q hpq t
    calc _ ≤ _ := dist_triangle_left _ _ p
      _ ≤ 4 * eps (n + 0) := by simp only [add_zero]; linarith
  | succ m ih =>
    set k := len n p q with hkdef
    have hk := hG.len_pos n p q
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    -- the pieces
    have piece : ∀ i ∈ Finset.range k, ∀ᶠ s in 𝓝 t,
        s ∈ Icc (0 : ℝ) 1 → (i : ℝ) ≤ s * k → s * k ≤ i + 1 →
          dist (lim len pt n p q s) (lim len pt n p q t) ≤
            4 * eps (n + (m + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hti : (i : ℝ) ≤ t * k ∧ t * k ≤ i + 1
      · -- `t` is in the piece: pull back the induction hypothesis along `s ↦ s * k - i`
        have hloc : t * k - i ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hti.1], by linarith [hti.2]⟩
        have hstep := hG.pt_step n p q i hpq hi
        have IH := ih (n + 1) _ _ hstep (t * k - i) hloc
        have hcont : Tendsto (fun s : ℝ => s * k - i) (𝓝[{s | (i : ℝ) ≤ s * k ∧ s * k ≤ i + 1}] t)
            (𝓝[Icc (0 : ℝ) 1] (t * k - i)) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
          · exact ((continuous_id.mul continuous_const).sub continuous_const).continuousAt.tendsto.mono_left
              nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with s hs
            exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have := hcont.eventually IH
        rw [eventually_nhdsWithin_iff] at this
        filter_upwards [this] with s hs hs01 hs1 hs2
        have e1 := lim_eq_on_piece hG n p q hpq hi hs1 hs2
        have e2 := lim_eq_on_piece hG n p q hpq hi hti.1 hti.2
        rw [e1, e2, show n + (m + 1) = n + 1 + m by ring]
        exact hs ⟨hs1, hs2⟩
      · -- `t` is outside the closed piece: eventually no point of the piece
        have hcl : IsClosed {s : ℝ | (i : ℝ) ≤ s * k ∧ s * k ≤ i + 1} :=
          (isClosed_le continuous_const (continuous_id.mul continuous_const)).inter
            (isClosed_le (continuous_id.mul continuous_const) continuous_const)
        filter_upwards [hcl.isOpen_compl.mem_nhds hti] with s hs _ h1 h2
        exact absurd ⟨h1, h2⟩ hs
    rw [← Filter.eventually_all_finset] at piece
    rw [eventually_nhdsWithin_iff]
    filter_upwards [piece] with s hs hs01
    have hmem := mem_Icc_idx hk hs01
    exact hs _ (Finset.mem_range.2 (idx_lt hk s)) hs01 hmem.1 hmem.2

theorem continuousOn_lim (n : ℕ) (p q : X) (hpq : dist p q < del n) :
    ContinuousOn (lim len pt n p q) (Icc (0 : ℝ) 1) := by
  intro t ht
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro r hr
  -- `eps (n + m) = eps n / 2 ^ m` tends to zero
  have heps : ∀ m, eps (n + m) = eps n / 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [← add_assoc, hG.eps_succ, ih, pow_succ]; field_simp
  have htend : Tendsto (fun m : ℕ => 4 * (eps n * (1 / 2) ^ m)) atTop (𝓝 (4 * (eps n * 0))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _).const_mul _
  simp only [mul_zero] at htend
  obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds hr)).exists
  filter_upwards [lim_osc hG m n p q hpq t ht] with s hs
  refine lt_of_le_of_lt hs ?_
  rw [heps m]
  convert hm using 2
  rw [div_eq_mul_inv, one_div, inv_pow]

end Walk

/-! ### The uniform path lemma -/

/-- **Uniform local path connectedness** (Mazurkiewicz-Moore-Menger, uniform form).  In a compact
locally connected metric space, for every `ε > 0` there is `δ > 0` such that two points at distance
less than `δ` are joined by a path that stays within `ε` of the first point. -/
theorem exists_path_of_dist_lt [CompactSpace X] [LocallyConnectedSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ → ∃ γ : Path x y, ∀ t, dist x (γ t) ≤ ε := by
  set eps : ℕ → ℝ := fun n => ε / 2 / 2 ^ n with heps
  have heps_pos : ∀ n, 0 < eps n := fun n => by positivity
  have hU : ∀ n, ∃ δ > 0, δ ≤ eps n ∧ ∀ p q : X, dist p q < δ →
      ∃ C : Set X, IsPreconnected C ∧ p ∈ C ∧ q ∈ C ∧ C ⊆ closedBall p (eps n) := by
    intro n
    obtain ⟨δ, hδ, h⟩ := exists_preconnected_of_dist_lt (X := X) (heps_pos n)
    exact ⟨min δ (eps n), lt_min hδ (heps_pos n), min_le_right _ _,
      fun p q hpq => h p q (lt_of_lt_of_le hpq (min_le_left _ _))⟩
  choose del hdel hdel_le hC using hU
  have hch : ∀ n (p q : X), ∃ k : ℕ, ∃ z : ℕ → X, 1 ≤ k ∧ z 0 = p ∧
      (dist p q < del n → IsChain (closedBall p (eps n)) (del (n + 1)) p q k z) := by
    intro n p q
    by_cases h : dist p q < del n
    · obtain ⟨C, hCc, hpC, hqC, hCsub⟩ := hC n p q h
      obtain ⟨k, z, hz⟩ := exists_chain hCc (hdel (n + 1)) hpC hqC
      refine ⟨k, z, hz.1, hz.2.1, fun _ => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := hz
      exact ⟨h1, h2, h3, fun i hi => hCsub (h4 i hi), h5⟩
    · exact ⟨1, fun _ => p, le_rfl, rfl, fun h' => absurd h' h⟩
  choose len pt hlen hpt0 hchain using hch
  have hG : Good eps del len pt :=
    { len_pos := hlen
      pt_zero := hpt0
      pt_last := fun n p q h => (hchain n p q h).2.2.1
      pt_near := fun n p q i h hi => by
        have := (hchain n p q h).2.2.2.1 i hi
        rw [mem_closedBall, dist_comm] at this
        exact this
      pt_step := fun n p q i h hi => (hchain n p q h).2.2.2.2 i hi
      eps_succ := fun n => by simp only [heps, pow_succ]; field_simp
      del_le := hdel_le }
  have : CompleteSpace X := complete_of_compact
  refine ⟨del 0, hdel 0, fun x y hxy => ?_⟩
  have : Nonempty X := ⟨x⟩
  have hc := continuousOn_lim hG 0 x y hxy
  refine ⟨{ toFun := fun t => lim len pt 0 x y t
            continuous_toFun := hc.comp_continuous continuous_subtype_val (fun t => t.2)
            source' := lim_zero hG 0 x y hxy
            target' := lim_one hG 0 x y hxy }, fun t => ?_⟩
  have := lim_mem hG 0 x y hxy t
  simp only [heps, pow_zero, div_one] at this
  simp only [Path.coe_mk_mk]
  linarith

/-- A compact locally connected metric space is locally path connected. -/
theorem locallyPathConnectedSpace_of_compact_locallyConnected [CompactSpace X]
    [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨r, hr, hru⟩ := Metric.isOpen_iff.1 hu x hxu
  obtain ⟨δ, hδ, hpath⟩ := exists_path_of_dist_lt (X := X) (half_pos hr)
  refine Filter.mem_of_superset (ball_mem_nhds x hδ) fun y hy => ?_
  rw [mem_ball, dist_comm] at hy
  obtain ⟨γ, hγ⟩ := hpath x y hy
  exact ⟨γ, fun t => hru (by rw [mem_ball, dist_comm]; linarith [hγ t])⟩

end HMPaths
end UndergradKB.Topology
