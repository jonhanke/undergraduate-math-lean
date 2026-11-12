import UndergradKB.Combinatorics.Recurrence.LineRegions
import Mathlib.Data.Finset.Max

/-!
# Lines in general position cut the plane into `1 + n (n + 1) / 2` regions

The plane is `ℝ × ℝ` and a line is the set `a x + b y = c` with `(a, b) ≠ (0, 0)`
(see `LineRegions`). A family of lines is in general position when no two are parallel and no three
pass through one point. We prove that `n` lines in general position cut the plane into
`1 + n (n + 1) / 2` regions, where the regions are the connected components of the complement of the
union of the lines, and that adding a line to `n` lines in general position adds `n + 1` regions.

The proof counts realizable sign vectors (see `LineRegions`): a new line meets the old
lines in `n` distinct points, which cut it into `n + 1` pieces, and these pieces give exactly the
old cells that the new line splits in two.
-/

namespace UndergradKB.Combinatorics.Recurrence.LineRegions

open Set

noncomputable section

/-! ### Cutting the real line by `n` points -/

lemma exists_between_lt (s : Finset ℝ) (a : ℝ) (h : ∀ x ∈ s, x < a) :
    ∃ t, (∀ x ∈ s, x < t) ∧ t < a := by
  by_cases hs : s.Nonempty
  · have hm := h _ (s.max'_mem hs)
    refine ⟨(s.max' hs + a) / 2, fun x hx => ?_, by linarith⟩
    have := s.le_max' x hx
    linarith
  · exact ⟨a - 1, fun x hx => absurd ⟨x, hx⟩ hs, by linarith⟩

lemma exists_count (T : Finset ℝ) : ∀ k ≤ T.card, ∃ t, t ∉ T ∧ (T.filter (· < t)).card = k := by
  induction T using Finset.induction_on_max with
  | empty =>
    intro k hk
    simp only [Finset.card_empty, nonpos_iff_eq_zero] at hk
    subst hk
    exact ⟨0, by simp, by simp⟩
  | insert a s hlt ih =>
    intro k hk
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    rw [Finset.card_insert_of_notMem ha] at hk
    rcases Nat.lt_or_ge k s.card with h | h
    · obtain ⟨t, ht, hc⟩ := ih k h.le
      have hta : t < a := by
        by_contra hge
        push_neg at hge
        have : s.filter (· < t) = s :=
          Finset.filter_true_of_mem (fun x hx => lt_of_lt_of_le (hlt x hx) hge)
        rw [this] at hc
        omega
      refine ⟨t, ?_, ?_⟩
      · simp [Finset.mem_insert, ht, hta.ne]
      · rw [Finset.filter_insert, if_neg (not_lt.2 hta.le)]; exact hc
    · rcases (by omega : k = s.card ∨ k = s.card + 1) with h | h
      · obtain ⟨t, h1, h2⟩ := exists_between_lt s a hlt
        refine ⟨t, ?_, ?_⟩
        · simp only [Finset.mem_insert, not_or]
          exact ⟨h2.ne, fun hx => lt_irrefl _ (h1 t hx)⟩
        · rw [Finset.filter_insert, if_neg (not_lt.2 h2.le),
            Finset.filter_true_of_mem (fun x hx => h1 x hx), h]
      · refine ⟨a + 1, ?_, ?_⟩
        · simp only [Finset.mem_insert, not_or]
          exact ⟨by linarith, fun hx => by have := hlt _ hx; linarith⟩
        · rw [Finset.filter_true_of_mem, Finset.card_insert_of_notMem ha, h]
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · linarith
          · have := hlt _ hx; linarith

/-- `n` distinct points cut the real line into `n + 1` pieces: counted as the number of distinct
"which points lie to the left" vectors realized off the points. -/
lemma count_1d {n : ℕ} (τ : Fin n → ℝ) (hτ : Function.Injective τ) :
    ((fun (t : ℝ) (i : Fin n) => decide (τ i < t)) '' {t | ∀ i, t ≠ τ i}).ncard = n + 1 := by
  set w : ℝ → Fin n → Bool := fun t i => decide (τ i < t) with hw
  let cnt : (Fin n → Bool) → ℕ := fun v => (Finset.univ.filter fun i => v i = true).card
  have aux : ∀ t t' : ℝ, t ≤ t' → cnt (w t) = cnt (w t') → w t = w t' := by
    intro t t' htt h
    have hsub : (Finset.univ.filter fun i => w t i = true) ⊆
        (Finset.univ.filter fun i => w t' i = true) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hw, decide_eq_true_eq] at hi ⊢
      exact lt_of_lt_of_le hi htt
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)
    funext i
    rw [Bool.eq_iff_iff]
    have := Finset.ext_iff.1 heq i
    simpa using this
  have hinj : Set.InjOn cnt (w '' {t | ∀ i, t ≠ τ i}) := by
    rintro _ ⟨t, _, rfl⟩ _ ⟨t', _, rfl⟩ h
    rcases le_total t t' with h1 | h1
    · exact aux t t' h1 h
    · exact (aux t' t h1 h.symm).symm
  have himg : cnt '' (w '' {t | ∀ i, t ≠ τ i}) = ↑(Finset.range (n + 1)) := by
    ext k
    constructor
    · rintro ⟨_, ⟨t, _, rfl⟩, rfl⟩
      have : cnt (w t) ≤ n := by
        have := Finset.card_le_univ (Finset.univ.filter fun i : Fin n => w t i = true)
        simpa using this
      simp only [Finset.coe_range, mem_Iio]
      omega
    · intro hk
      simp only [Finset.coe_range, mem_Iio] at hk
      have hT : (Finset.univ.image τ).card = n := by
        rw [Finset.card_image_of_injective _ hτ]; simp
      obtain ⟨t, ht, hc⟩ := exists_count (Finset.univ.image τ) k (by omega)
      refine ⟨w t, ⟨t, fun i hi => ht (by simp [hi]), rfl⟩, ?_⟩
      have : (Finset.univ.filter fun i => w t i = true).image τ =
          (Finset.univ.image τ).filter (· < t) := by
        ext x
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hw,
          decide_eq_true_eq]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
        · rintro ⟨⟨i, rfl⟩, hi⟩; exact ⟨i, hi, rfl⟩
      show (Finset.univ.filter fun i => w t i = true).card = k
      rw [← Finset.card_image_of_injective _ hτ, this, hc]
  rw [← hinj.ncard_image, himg, Set.ncard_coe_finset, Finset.card_range]

/-! ### General position and the count on the new line -/

/-- General position: no two lines are parallel and no three lines have a common point. -/
structure GeneralPosition {n : ℕ} (L : Fin n → Line) : Prop where
  nonpar : ∀ i j, i ≠ j → (L i).a * (L j).b - (L j).a * (L i).b ≠ 0
  nothree : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    ∀ p, ¬ (p ∈ (L i).pts ∧ p ∈ (L j).pts ∧ p ∈ (L k).pts)

lemma ncard_OnLine {n : ℕ} (ℓ : Line) (M : Fin n → Line)
    (hpar : ∀ i, ℓ.a * (M i).b - (M i).a * ℓ.b ≠ 0)
    (hconc : ∀ i j, i ≠ j → ∀ p, ¬ (p ∈ ℓ.pts ∧ p ∈ (M i).pts ∧ p ∈ (M j).pts)) :
    (OnLine ℓ M).ncard = n + 1 := by
  have hD := ℓ.sq_pos
  set D := ℓ.a * ℓ.a + ℓ.b * ℓ.b with hDdef
  set x0 := ℓ.a * ℓ.c / D with hx0
  set y0 := ℓ.b * ℓ.c / D with hy0
  have hp0 : ℓ.a * x0 + ℓ.b * y0 = ℓ.c := by
    rw [hx0, hy0]; field_simp; rw [hDdef]; ring
  let P : ℝ → ℝ × ℝ := fun t => (x0 - ℓ.b * t, y0 + ℓ.a * t)
  have hPl : ∀ t, P t ∈ ℓ.pts := by
    intro t; simp only [Line.pts, mem_ofPred_eq, P]; linear_combination hp0
  have hPf : ∀ i t, (M i).f (P t) = (M i).f (x0, y0) +
      t * (ℓ.a * (M i).b - (M i).a * ℓ.b) := by
    intro i t; simp only [Line.f, P]; ring
  have hPall : ∀ q ∈ ℓ.pts, ∃ t, q = P t := by
    intro q hq
    have hq' : ℓ.a * q.1 + ℓ.b * q.2 = ℓ.c := hq
    refine ⟨(-ℓ.b * (q.1 - x0) + ℓ.a * (q.2 - y0)) / D, ?_⟩
    have ht : D * ((-ℓ.b * (q.1 - x0) + ℓ.a * (q.2 - y0)) / D) =
        -ℓ.b * (q.1 - x0) + ℓ.a * (q.2 - y0) := mul_div_cancel₀ _ hD.ne'
    generalize (-ℓ.b * (q.1 - x0) + ℓ.a * (q.2 - y0)) / D = t at ht
    refine Prod.ext ?_ ?_
    · apply mul_left_cancel₀ hD.ne'
      simp only [P]
      linear_combination ℓ.b * ht + ℓ.a * hq' - ℓ.a * hp0
    · apply mul_left_cancel₀ hD.ne'
      simp only [P]
      linear_combination (-ℓ.a) * ht + ℓ.b * hq' - ℓ.b * hp0
  let τ : Fin n → ℝ := fun i => -(M i).f (x0, y0) / (ℓ.a * (M i).b - (M i).a * ℓ.b)
  have hroot : ∀ i t, (M i).f (P t) = 0 ↔ t = τ i := by
    intro i t
    rw [hPf, show τ i = -(M i).f (x0, y0) / (ℓ.a * (M i).b - (M i).a * ℓ.b) from rfl,
      eq_div_iff (hpar i)]
    constructor <;> intro h <;> linarith
  have hτinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    apply hconc i j hne (P (τ i))
    refine ⟨hPl _, Line.mem_pts.2 ((hroot i _).2 rfl), Line.mem_pts.2 ((hroot j _).2 hij)⟩
  -- the points of the line off the old lines
  have hset : Off M ∩ ℓ.pts = P '' {t | ∀ i, t ≠ τ i} := by
    ext q
    constructor
    · rintro ⟨hq, hl⟩
      obtain ⟨t, rfl⟩ := hPall q hl
      exact ⟨t, fun i hti => hq i ((hroot i t).2 hti), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨fun i hi => ht i ((hroot i t).1 hi), hPl t⟩
  -- the sign vector along the line
  let o : Fin n → Bool := fun i => decide (0 < ℓ.a * (M i).b - (M i).a * ℓ.b)
  let F : (Fin n → Bool) → (Fin n → Bool) := fun v i => (o i == v i)
  have hF : Function.Injective F := by
    intro v v' h
    funext i
    have := congrFun h i
    simp only [F] at this
    revert this
    cases o i <;> cases v i <;> cases v' i <;> simp
  have hsign : ∀ t ∈ {t : ℝ | ∀ i, t ≠ τ i},
      signVec M (P t) = F (fun i => decide (τ i < t)) := by
    intro t ht
    funext i
    simp only [signVec, F, o]
    have hβ := hpar i
    have hα : (M i).f (x0, y0) = -τ i * (ℓ.a * (M i).b - (M i).a * ℓ.b) := by
      simp only [τ]; field_simp
    have e : (M i).f (P t) = (ℓ.a * (M i).b - (M i).a * ℓ.b) * (t - τ i) := by
      rw [hPf, hα]; ring
    rw [e]
    have hti : t ≠ τ i := ht i
    rcases lt_or_gt_of_ne hβ with hb | hb <;> rcases lt_or_gt_of_ne hti with h | h
    · have p1 := mul_pos_of_neg_of_neg hb (sub_neg.2 h)
      simp [p1, not_lt.2 hb.le, not_lt.2 h.le]
    · have p1 := mul_neg_of_neg_of_pos hb (sub_pos.2 h)
      simp [not_lt.2 p1.le, not_lt.2 hb.le, h]
    · have p1 := mul_neg_of_pos_of_neg hb (sub_neg.2 h)
      simp [not_lt.2 p1.le, hb, not_lt.2 h.le]
    · have p1 := mul_pos hb (sub_pos.2 h)
      simp [p1, hb, h]
  have : OnLine ℓ M = F '' ((fun (t : ℝ) (i : Fin n) => decide (τ i < t)) ''
      {t | ∀ i, t ≠ τ i}) := by
    rw [OnLine, hset, Set.image_image, Set.image_image]
    exact Set.image_congr (fun t ht => hsign t ht)
  rw [this, Set.ncard_image_of_injective _ hF]
  exact count_1d τ hτinj

/-! ### The count -/

lemma ncard_Real_succ {n : ℕ} (L : Fin (n + 1) → Line) (gp : GeneralPosition L) :
    (Real L).ncard = (Real (fun i => L i.succ)).ncard + (n + 1) := by
  have hL : (Fin.cons (L 0) (fun i => L i.succ) : Fin (n + 1) → Line) = L := Fin.cons_self_tail L
  have h := ncard_Real_cons (L 0) (fun i => L i.succ)
  rw [hL] at h
  rw [h, ncard_OnLine]
  · intro i
    simpa using gp.nonpar 0 i.succ (Fin.succ_ne_zero i).symm
  · intro i j hij p hp
    exact gp.nothree 0 i.succ j.succ (Fin.succ_ne_zero i).symm (fun h => hij (Fin.succ_injective _ h))
      (Fin.succ_ne_zero j).symm p hp

lemma GeneralPosition.tail {n : ℕ} {L : Fin (n + 1) → Line} (gp : GeneralPosition L) :
    GeneralPosition (fun i => L i.succ) :=
  ⟨fun i j h => gp.nonpar i.succ j.succ (fun h' => h (Fin.succ_injective _ h')),
   fun i j k hij hjk hik => gp.nothree i.succ j.succ k.succ (fun h' => hij (Fin.succ_injective _ h'))
     (fun h' => hjk (Fin.succ_injective _ h')) (fun h' => hik (Fin.succ_injective _ h'))⟩

/-- The number of realizable sign vectors of `n` lines in general position. -/
theorem ncard_Real {n : ℕ} (L : Fin n → Line) (gp : GeneralPosition L) :
    (Real L).ncard = 1 + n * (n + 1) / 2 := by
  induction n with
  | zero =>
    have : Real L = Set.univ := by
      ext σ
      exact ⟨fun _ => trivial, fun _ => ⟨(0, 0), fun i => i.elim0, Subsingleton.elim _ _⟩⟩
    rw [this, Set.ncard_univ]
    simp
  | succ n ih =>
    rw [ncard_Real_succ L gp, ih _ gp.tail]
    have : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    omega

lemma Off_eq (n : ℕ) (L : Fin n → Line) : Off L = (⋃ i, (L i).pts)ᶜ := by
  ext p
  simp [Off, Line.mem_pts]

/-- CO-214, CO-220. `n` lines in general position cut the plane `ℝ × ℝ` into `1 + n (n + 1) / 2`
regions. A line is the set `{p | a p.1 + b p.2 = c}` with `(a, b) ≠ (0, 0)`; general position means
that no two lines are parallel and no three have a common point; the regions are the connected
components of the complement of the union of the lines. -/
@[kb "kellertrotter2017" "text p.210 lines and regions; Example 1.12 p.36; Example 3.3 p.67; Example 9.16 p.220"]
theorem lines_regions_card {n : ℕ} (L : Fin n → Line) (gp : GeneralPosition L) :
    Nat.card (ConnectedComponents (↥((⋃ i, (L i).pts)ᶜ))) = 1 + n * (n + 1) / 2 := by
  rw [← Off_eq, nat_card_components, ncard_Real L gp]

/-- CO-214, CO-220 (recurrence form). Adding one more line to `n` lines in general position adds
`n + 1` regions: the new line is cut by the old ones into `n + 1` pieces, each splitting a region
in two. -/
@[kb "kellertrotter2017" "text p.210 lines and regions; Example 3.3 p.67"]
theorem lines_regions_succ {n : ℕ} (L : Fin (n + 1) → Line) (gp : GeneralPosition L) :
    Nat.card (ConnectedComponents (↥((⋃ i, (L i).pts)ᶜ))) =
      Nat.card (ConnectedComponents (↥((⋃ i : Fin n, (L i.succ).pts)ᶜ))) + (n + 1) := by
  rw [← Off_eq, ← Off_eq, nat_card_components, nat_card_components, ncard_Real_succ L gp]

end

end UndergradKB.Combinatorics.Recurrence.LineRegions
