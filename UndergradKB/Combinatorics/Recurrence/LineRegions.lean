import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Data.Set.Card
import UndergradKB.Common.Attr

/-!
# Regions cut out of the plane by lines: sign cells and the counting step

The plane is `ℝ × ℝ`. A line is the set of points `(x, y)` with `a x + b y = c`, where `(a, b)` is not
the zero vector. For a finite family of lines, every point off all the lines has a sign vector
(on which side of each line it lies). We prove, for any finite family of lines:

* the set of points with a given sign vector (a "cell") is open and convex;
* the connected components of the complement of the lines correspond exactly to the sign vectors that
  occur, so the number of regions is the number of realizable sign vectors;
* adding one line to a family increases the number of realizable sign vectors by the number of
  sign vectors realized by points of the new line lying off the old lines.

The counting for lines in general position is in `LineRegions2`.
-/

namespace UndergradKB.Combinatorics.Recurrence.LineRegions

open Set

/-- A line in the plane `ℝ × ℝ`: the set `a x + b y = c`, with `(a, b) ≠ (0, 0)`. -/
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nz : a ≠ 0 ∨ b ≠ 0

namespace Line

/-- The affine function whose zero set is the line. -/
def f (ℓ : Line) (p : ℝ × ℝ) : ℝ := ℓ.a * p.1 + ℓ.b * p.2 - ℓ.c

/-- The points of the line. -/
def pts (ℓ : Line) : Set (ℝ × ℝ) := {p | ℓ.a * p.1 + ℓ.b * p.2 = ℓ.c}

lemma mem_pts {ℓ : Line} {p : ℝ × ℝ} : p ∈ ℓ.pts ↔ ℓ.f p = 0 := by
  simp [pts, f, sub_eq_zero]

lemma continuous_f (ℓ : Line) : Continuous ℓ.f := by unfold f; fun_prop

lemma f_comb (ℓ : Line) (x y : ℝ × ℝ) (s t : ℝ) (h : s + t = 1) :
    ℓ.f (s • x + t • y) = s * ℓ.f x + t * ℓ.f y := by
  simp only [f, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination ℓ.c * h

lemma sq_pos (ℓ : Line) : 0 < ℓ.a * ℓ.a + ℓ.b * ℓ.b := by
  rcases ℓ.nz with h | h
  · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg ℓ.b]
  · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg ℓ.a]

lemma f_add_smul (ℓ : Line) (p w : ℝ × ℝ) (ε : ℝ) :
    ℓ.f (p + ε • w) = ℓ.f p + ε * (ℓ.a * w.1 + ℓ.b * w.2) := by
  simp only [f, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

end Line

/-- Strict sign condition: `Sg true x` is `0 < x`, `Sg false x` is `x < 0`. -/
def Sg : Bool → ℝ → Prop
  | true, x => 0 < x
  | false, x => x < 0

lemma Sg_iff (b : Bool) (x : ℝ) : Sg b x ↔ x ≠ 0 ∧ decide (0 < x) = b := by
  cases b
  · simp only [Sg, decide_eq_false_iff_not, not_lt]
    exact ⟨fun h => ⟨h.ne, h.le⟩, fun h => lt_of_le_of_ne h.2 h.1⟩
  · simp only [Sg, decide_eq_true_eq]
    exact ⟨fun h => ⟨h.ne', h⟩, fun h => h.2⟩

lemma isOpen_Sg (b : Bool) : IsOpen {x : ℝ | Sg b x} := by
  cases b
  · exact isOpen_Iio
  · exact isOpen_Ioi

noncomputable section

variable {n : ℕ}

/-- Sign vector of a point with respect to a family of lines. -/
def signVec (L : Fin n → Line) (p : ℝ × ℝ) : Fin n → Bool := fun i => decide (0 < (L i).f p)

/-- Points off all the lines. -/
def Off (L : Fin n → Line) : Set (ℝ × ℝ) := {p | ∀ i, (L i).f p ≠ 0}

/-- The cell of a sign vector. -/
def Cell (L : Fin n → Line) (σ : Fin n → Bool) : Set (ℝ × ℝ) := {p | ∀ i, Sg (σ i) ((L i).f p)}

/-- The sign vectors realized by points off the lines. -/
def Real (L : Fin n → Line) : Set (Fin n → Bool) := signVec L '' Off L

lemma mem_Cell {L : Fin n → Line} {σ : Fin n → Bool} {p : ℝ × ℝ} :
    p ∈ Cell L σ ↔ p ∈ Off L ∧ signVec L p = σ := by
  simp only [Cell, Off, signVec, mem_ofPred_eq, Sg_iff, funext_iff]
  exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i, h.2 i⟩⟩

lemma isOpen_Cell (L : Fin n → Line) (σ : Fin n → Bool) : IsOpen (Cell L σ) := by
  have : Cell L σ = ⋂ i, (L i).f ⁻¹' {x | Sg (σ i) x} := by ext; simp [Cell]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_Sg _).preimage (L i).continuous_f

lemma pos_comb {s t u v : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hu : 0 < u)
    (hv : 0 < v) : 0 < s * u + t * v := by
  rcases hs.lt_or_eq with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos h hu) (mul_nonneg ht hv.le)
  · have : t = 1 := by linarith
    subst this; rw [← h]; simpa using hv

lemma convex_Cell (L : Fin n → Line) (σ : Fin n → Bool) : Convex ℝ (Cell L σ) := by
  intro x hx y hy s t hs ht hst i
  have hxi := hx i
  have hyi := hy i
  rw [(L i).f_comb _ _ _ _ hst]
  revert hxi hyi
  cases σ i
  · intro h1 h2
    have := pos_comb hs ht hst (neg_pos.2 h1) (neg_pos.2 h2)
    simp only [Sg]; linarith
  · intro h1 h2
    exact pos_comb hs ht hst h1 h2

/-- The sign vector map on the complement of the lines. -/
def phi (L : Fin n → Line) : Off L → (Fin n → Bool) := fun q => signVec L q.1

lemma continuous_phi (L : Fin n → Line) : Continuous (phi L) := by
  rw [continuous_discrete_rng]
  intro σ
  have : phi L ⁻¹' {σ} = Subtype.val ⁻¹' Cell L σ := by
    ext q
    simp only [mem_preimage, mem_singleton_iff, mem_Cell]
    exact ⟨fun h => ⟨q.2, h⟩, fun h => h.2⟩
  rw [this]
  exact (isOpen_Cell L σ).preimage continuous_subtype_val

lemma comp_eq_of_phi_eq (L : Fin n → Line) (x y : Off L) (h : phi L x = phi L y) :
    (x : ConnectedComponents (Off L)) = y := by
  rw [ConnectedComponents.coe_eq_coe']
  have hsub : Cell L (phi L y) ⊆ Off L := fun p hp => (mem_Cell.1 hp).1
  have hp : IsPreconnected (Subtype.val ⁻¹' Cell L (phi L y) : Set (Off L)) := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hsub]
    exact (convex_Cell L _).isPreconnected
  have hy : y ∈ (Subtype.val ⁻¹' Cell L (phi L y) : Set (Off L)) :=
    mem_Cell.2 ⟨y.2, rfl⟩
  have hx : x ∈ (Subtype.val ⁻¹' Cell L (phi L y) : Set (Off L)) :=
    mem_Cell.2 ⟨x.2, h⟩
  exact hp.subset_connectedComponent hy hx

/-- The connected components of the complement of the lines are in bijection with the realizable
sign vectors. -/
theorem nat_card_components (L : Fin n → Line) :
    Nat.card (ConnectedComponents (Off L)) = (Real L).ncard := by
  let g := (continuous_phi L).connectedComponentsLift
  have hg : Function.Injective g := by
    intro u v h
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe v
    simp only [g, Continuous.connectedComponentsLift_apply_coe] at h
    exact comp_eq_of_phi_eq L x y h
  have hr : Set.range g = Real L := by
    ext σ
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
      exact ⟨x.1, x.2, by simp [g, phi]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨((⟨p, hp⟩ : Off L) : ConnectedComponents (Off L)), by simp [g, phi]⟩
  rw [Nat.card_congr (Equiv.ofInjective g hg), hr, Nat.card_coe_set_eq]

/-! ### Adding one line -/

/-- Old sign vectors realized with the new line's value positive. -/
def TS (ℓ : Line) (M : Fin n → Line) : Set (Fin n → Bool) :=
  {τ | ∃ p ∈ Off M, 0 < ℓ.f p ∧ signVec M p = τ}

/-- Old sign vectors realized with the new line's value negative. -/
def FS (ℓ : Line) (M : Fin n → Line) : Set (Fin n → Bool) :=
  {τ | ∃ p ∈ Off M, ℓ.f p < 0 ∧ signVec M p = τ}

/-- Sign vectors realized by points of `ℓ` off the lines `M`. -/
def OnLine (ℓ : Line) (M : Fin n → Line) : Set (Fin n → Bool) :=
  signVec M '' (Off M ∩ ℓ.pts)

lemma perturb (M : Fin n → Line) (p : ℝ × ℝ) (hp : p ∈ Off M) (w : ℝ × ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ p + ε • w ∈ Cell M (signVec M p) := by
  have hp' : p ∈ Cell M (signVec M p) := mem_Cell.2 ⟨hp, rfl⟩
  have hc : Continuous fun ε : ℝ => p + ε • w := by fun_prop
  have h : ∀ᶠ ε in nhds (0 : ℝ), p + ε • w ∈ Cell M (signVec M p) :=
    ((isOpen_Cell M _).preimage hc).mem_nhds (by simpa using hp')
  have h2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
      p + ε • w ∈ Cell M (signVec M p) ∧ ε ∈ Ioi (0 : ℝ) :=
    (h.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ε, h1, h2⟩ := h2.exists
  exact ⟨ε, h2, h1⟩

lemma TS_union_FS (ℓ : Line) (M : Fin n → Line) : TS ℓ M ∪ FS ℓ M = Real M := by
  ext τ
  constructor
  · rintro (⟨p, hp, _, rfl⟩ | ⟨p, hp, _, rfl⟩) <;> exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    rcases lt_trichotomy (ℓ.f p) 0 with h | h | h
    · exact Or.inr ⟨p, hp, h, rfl⟩
    · obtain ⟨ε, hε, hc⟩ := perturb M p hp (ℓ.a, ℓ.b)
      refine Or.inl ⟨p + ε • (ℓ.a, ℓ.b), (mem_Cell.1 hc).1, ?_, (mem_Cell.1 hc).2⟩
      rw [ℓ.f_add_smul, h]
      have := ℓ.sq_pos
      simp only [zero_add]
      exact mul_pos hε this
    · exact Or.inl ⟨p, hp, h, rfl⟩

lemma TS_inter_FS (ℓ : Line) (M : Fin n → Line) : TS ℓ M ∩ FS ℓ M = OnLine ℓ M := by
  ext τ
  constructor
  · rintro ⟨⟨p, hp, hfp, rfl⟩, ⟨q, hq, hfq, hqs⟩⟩
    have hp' : p ∈ Cell M (signVec M p) := mem_Cell.2 ⟨hp, rfl⟩
    have hq' : q ∈ Cell M (signVec M p) := mem_Cell.2 ⟨hq, hqs⟩
    have hD : 0 < ℓ.f p - ℓ.f q := by linarith
    have hr := convex_Cell M (signVec M p) hp' hq'
      (a := -ℓ.f q / (ℓ.f p - ℓ.f q)) (b := ℓ.f p / (ℓ.f p - ℓ.f q))
      (div_nonneg (by linarith) hD.le) (div_nonneg hfp.le hD.le)
      (by field_simp; ring)
    have hf : ℓ.f ((-ℓ.f q / (ℓ.f p - ℓ.f q)) • p + (ℓ.f p / (ℓ.f p - ℓ.f q)) • q) = 0 := by
      rw [ℓ.f_comb _ _ _ _ (by field_simp; ring)]
      field_simp; ring
    exact ⟨_, ⟨(mem_Cell.1 hr).1, Line.mem_pts.2 hf⟩, (mem_Cell.1 hr).2⟩
  · rintro ⟨r, ⟨hr, hl⟩, rfl⟩
    have hl' := Line.mem_pts.1 hl
    constructor
    · obtain ⟨ε, hε, hc⟩ := perturb M r hr (ℓ.a, ℓ.b)
      refine ⟨r + ε • (ℓ.a, ℓ.b), (mem_Cell.1 hc).1, ?_, (mem_Cell.1 hc).2⟩
      rw [ℓ.f_add_smul, hl']
      have := ℓ.sq_pos
      simp only [zero_add]
      exact mul_pos hε this
    · obtain ⟨ε, hε, hc⟩ := perturb M r hr (-ℓ.a, -ℓ.b)
      refine ⟨r + ε • (-ℓ.a, -ℓ.b), (mem_Cell.1 hc).1, ?_, (mem_Cell.1 hc).2⟩
      rw [ℓ.f_add_smul, hl']
      have := ℓ.sq_pos
      simp only [zero_add]
      nlinarith

/-- Prepend a sign. -/
def consB (b : Bool) (τ : Fin n → Bool) : Fin (n + 1) → Bool := Fin.cons b τ

lemma consB_injective (b : Bool) : Function.Injective (consB (n := n) b) := by
  intro x y h
  funext i
  have := congrFun h i.succ
  simpa [consB] using this

lemma signVec_cons (ℓ : Line) (M : Fin n → Line) (p : ℝ × ℝ) :
    signVec (Fin.cons ℓ M : Fin (n + 1) → Line) p =
      consB (decide (0 < ℓ.f p)) (signVec M p) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [signVec, consB]

lemma Off_cons (ℓ : Line) (M : Fin n → Line) (p : ℝ × ℝ) :
    p ∈ Off (Fin.cons ℓ M : Fin (n + 1) → Line) ↔ ℓ.f p ≠ 0 ∧ p ∈ Off M := by
  simp [Off, Fin.forall_fin_succ]

lemma Real_cons (ℓ : Line) (M : Fin n → Line) :
    Real (Fin.cons ℓ M : Fin (n + 1) → Line) = consB true '' TS ℓ M ∪ consB false '' FS ℓ M := by
  ext σ
  obtain ⟨b, τ, rfl⟩ : ∃ b τ, σ = consB b τ :=
    ⟨σ 0, Fin.tail σ, (Fin.cons_self_tail σ).symm⟩
  have key : ∀ b' τ', consB b' τ' = consB b τ ↔ b' = b ∧ τ' = τ := by
    intro b' τ'
    simp [consB, Fin.cons_injective2.eq_iff]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [Off_cons] at hp
    rw [signVec_cons, key] at h
    obtain ⟨h1, h2⟩ := h
    rcases hp with ⟨h0, hM⟩
    rcases lt_or_gt_of_ne h0 with hn | hn
    · have : b = false := by rw [← h1]; simp [not_lt.2 hn.le]
      subst this
      exact Or.inr ⟨τ, ⟨p, hM, hn, h2⟩, rfl⟩
    · have : b = true := by rw [← h1]; simp [hn]
      subst this
      exact Or.inl ⟨τ, ⟨p, hM, hn, h2⟩, rfl⟩
  · rintro (⟨τ', ⟨p, hM, hn, h2⟩, h⟩ | ⟨τ', ⟨p, hM, hn, h2⟩, h⟩)
    · rw [key] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨p, (Off_cons _ _ _).2 ⟨hn.ne', hM⟩, ?_⟩
      rw [signVec_cons, h2]; simp [hn]
    · rw [key] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨p, (Off_cons _ _ _).2 ⟨hn.ne, hM⟩, ?_⟩
      rw [signVec_cons, h2]; simp [not_lt.2 hn.le]

/-- Adding a line adds the number of old sign vectors that are realized on the new line. -/
theorem ncard_Real_cons (ℓ : Line) (M : Fin n → Line) :
    (Real (Fin.cons ℓ M : Fin (n + 1) → Line)).ncard =
      (Real M).ncard + (OnLine ℓ M).ncard := by
  have hd : Disjoint (consB true '' TS ℓ M) (consB false '' FS ℓ M) := by
    rw [Set.disjoint_left]
    rintro σ ⟨τ, _, rfl⟩ ⟨τ', _, h⟩
    have := congrFun h 0
    simp [consB] at this
  rw [Real_cons, Set.ncard_union_eq hd, Set.ncard_image_of_injective _ (consB_injective _),
    Set.ncard_image_of_injective _ (consB_injective _), ← TS_union_FS, ← TS_inter_FS,
    ← Set.ncard_union_add_ncard_inter (TS ℓ M) (FS ℓ M)]

end

end UndergradKB.Combinatorics.Recurrence.LineRegions
