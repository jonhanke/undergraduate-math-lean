import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import UndergradKB.Common.Attr
import UndergradKB.Geometry.Constructions2

/-! # The Poncelet-Steiner theorem (Petrunin, Section 19F, p. 164): the hard inclusion

A ruler together with one given circle (and its centre) constructs everything ruler and compass do
(`rgConstructible_iff_rcConstructible`). Strategy, in the frame `O = (0,0)`, `P = (1,0)` (`Setup`): the set `T`
of ruler-reachable points is closed under line-line and line-circle intersections (`LLC`, `GC`). Using only
line-line closure, a base segment with its midpoint, an external point and a point of the median give an
auxiliary parallel (`step1_std`) and then the parallel through every point (`par_std`, `par_std_full`,
`par_base`); diameters of the given circle have midpoint `O`, so parallels to every line thru `O`
(`Setup.par_O`) and then to every line (`Setup.gen_par`, via the parallelogram midpoint) are available. This
simulates the parallel tool, hence Exercise 14.7 (`rp_add_sub_mul_div`): the abscissae `K` of the points on the
axis form a field (`Setup.K`); the point `(0,1)` (`Setup.hJ`), the grid, the projections give `T ⊆ K × K`
and `K × K ⊆ T`; the horizontal chord thru `(0, (1-a)/(1+a))` gives square roots (`Setup.sqrt_mem`).
Then `RCConstructible.coordsK` and the frame transfer of Mohr-Mascheroni finish. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace UndergradKB.Geometry

open RCConv

namespace PS

/-- A set of points closed under intersecting two non-parallel lines thru its points. -/
def LLC (T : Set (ℝ × ℝ)) : Prop :=
  ∀ p q p' q' x : ℝ × ℝ, p ∈ T → q ∈ T → p' ∈ T → q' ∈ T →
    (q.1 - p.1) * (q'.2 - p'.2) - (q.2 - p.2) * (q'.1 - p'.1) ≠ 0 →
    OnLine p q x → OnLine p' q' x → x ∈ T

/-- The parallel construction in the standard frame: base segment `(0,0),(1,0)` with midpoint, an auxiliary
parallel `y = h` with two points, and a point `C` at height `c ∉ {0, h, 2h}`. -/
theorem par_std {T : Set (ℝ × ℝ)} (hT : LLC T) {d1 d1' h c1 c : ℝ} (hA : ((0 : ℝ), (0 : ℝ)) ∈ T)
    (hB : ((1 : ℝ), (0 : ℝ)) ∈ T) (hM : ((1 / 2 : ℝ), (0 : ℝ)) ∈ T) (hD : (d1, h) ∈ T) (hD' : (d1', h) ∈ T)
    (hd : d1 ≠ d1') (hh : h ≠ 0) (hC : (c1, c) ∈ T) (hc0 : c ≠ 0) (hch : c ≠ h) (hc2 : c ≠ 2 * h) :
    (c1 - 1 + c / h, c) ∈ T := by
  have hc2' : 2 * h - c ≠ 0 := fun e => hc2 (by linarith)
  have hc2'' : h * 2 - c ≠ 0 := fun e => hc2 (by linarith)
  have hc2''' : -c + h * 2 ≠ 0 := fun e => hc2 (by linarith)
  have hd' : d1' - d1 ≠ 0 := fun e => hd (by linarith)
  have hW : (1 + h / c * (c1 - 1), h) ∈ T := by
    refine hT (1, 0) (c1, c) (d1, h) (d1', h) _ hB hC hD hD' ?_ ⟨h / c, ?_, ?_⟩
      ⟨(1 + h / c * (c1 - 1) - d1) / (d1' - d1), ?_, ?_⟩
    · simp only <;> intro e; apply mul_ne_zero hc0 hd'; linarith
    · simp only <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> ring
  have hZ : (h / (2 * h - c) * c1, h / (2 * h - c) * c) ∈ T := by
    refine hT (0, 0) (c1, c) (1 + h / c * (c1 - 1), h) (1 / 2, 0) _ hA hC hW hM ?_
      ⟨h / (2 * h - c), ?_, ?_⟩ ⟨(2 * h - 2 * c) / (2 * h - c), ?_, ?_⟩
    · simp only
      have : (c1 - 0) * (0 - h) - (c - 0) * (1 / 2 - (1 + h / c * (c1 - 1))) = (c - 2 * h) / 2 := by
        field_simp <;> ring
      rw [this]; exact div_ne_zero (sub_ne_zero.mpr hc2) two_ne_zero
    · simp only <;> ring
    · simp only <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
  refine hT (1, 0) (h / (2 * h - c) * c1, h / (2 * h - c) * c) (0, 0) (1 + h / c * (c1 - 1), h) _ hB hZ hA hW ?_
    ⟨(2 * h - c) / h, ?_, ?_⟩ ⟨c / h, ?_, ?_⟩
  · simp only
    have : (h / (2 * h - c) * c1 - 1) * (h - 0) - (h / (2 * h - c) * c - 0) * (1 + h / c * (c1 - 1) - 0) =
        -h ^ 2 / (2 * h - c) := by
      field_simp <;> ring
    rw [this]; exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hh)) hc2'
  · simp only <;> field_simp <;> ring
  · simp only <;> field_simp <;> ring
  · simp only <;> field_simp <;> ring
  · simp only <;> field_simp <;> ring

/-- Pulling a line-closed set back along a similarity `unframe A B` keeps it line-closed. -/
theorem LLC.pull {T : Set (ℝ × ℝ)} (hT : LLC T) {A B : ℝ × ℝ} (hAB : A ≠ B) :
    LLC {y | unframe A B y ∈ T} := by
  have hN := (ne_coords hAB).ne'
  intro p q p' q' x hp hq hp' hq' hdet hx hx'
  have onl : ∀ {p q x : ℝ × ℝ}, OnLine p q x → OnLine (unframe A B p) (unframe A B q) (unframe A B x) := by
    rintro p q x ⟨t, h1, h2⟩
    refine ⟨t, ?_, ?_⟩ <;> simp only [unframe, h1, h2] <;> ring
  refine hT _ _ _ _ _ hp hq hp' hq' ?_ (onl hx) (onl hx')
  have : ((unframe A B q).1 - (unframe A B p).1) * ((unframe A B q').2 - (unframe A B p').2) -
      ((unframe A B q).2 - (unframe A B p).2) * ((unframe A B q').1 - (unframe A B p').1) =
      ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) *
      ((q.1 - p.1) * (q'.2 - p'.2) - (q.2 - p.2) * (q'.1 - p'.1)) := by
    simp only [unframe]; ring
  rw [this]; exact mul_ne_zero hN hdet

/-- The first step: from the base `(0,0),(1,0)` with midpoint, an external point `X` and a point `Z` of the
line `XM` (`Z = M + ζ (X - M)`, `ζ ∉ {0, 1, -1}`) one constructs the two ends `U`, `V` of a parallel to the base
at height `t x₂`, and the midpoint of `UV`. -/
theorem step1_std {T : Set (ℝ × ℝ)} (hT : LLC T) {x1 x2 ζ t : ℝ} (hA : ((0 : ℝ), (0 : ℝ)) ∈ T)
    (hB : ((1 : ℝ), (0 : ℝ)) ∈ T) (hM : ((1 / 2 : ℝ), (0 : ℝ)) ∈ T) (hX : (x1, x2) ∈ T) (hx2 : x2 ≠ 0)
    (hZ : (1 / 2 + ζ * (x1 - 1 / 2), ζ * x2) ∈ T) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ -1)
    (ht : t = 2 * ζ / (1 + ζ)) :
    (1 + t * (x1 - 1), t * x2) ∈ T ∧ (t * x1, t * x2) ∈ T ∧ (1 / 2 + t * (x1 - 1 / 2), t * x2) ∈ T := by
  have h1 : 1 + ζ ≠ 0 := fun e => hζ2 (by linarith)
  have h1' : ζ - 1 ≠ 0 := fun e => hζ1 (by linarith)
  subst ht
  have hU : (1 + 2 * ζ / (1 + ζ) * (x1 - 1), 2 * ζ / (1 + ζ) * x2) ∈ T := by
    refine hT (0, 0) (1 / 2 + ζ * (x1 - 1 / 2), ζ * x2) (1, 0) (x1, x2) _ hA hZ hB hX ?_
      ⟨2 / (1 + ζ), ?_, ?_⟩ ⟨2 * ζ / (1 + ζ), ?_, ?_⟩
    · simp only
      have : (1 / 2 + ζ * (x1 - 1 / 2) - 0) * (x2 - 0) - (ζ * x2 - 0) * (x1 - 1) = x2 * (1 + ζ) / 2 := by ring
      rw [this]; exact div_ne_zero (mul_ne_zero hx2 h1) two_ne_zero
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
  have hV : (2 * ζ / (1 + ζ) * x1, 2 * ζ / (1 + ζ) * x2) ∈ T := by
    refine hT (1, 0) (1 / 2 + ζ * (x1 - 1 / 2), ζ * x2) (0, 0) (x1, x2) _ hB hZ hA hX ?_
      ⟨2 / (1 + ζ), ?_, ?_⟩ ⟨2 * ζ / (1 + ζ), ?_, ?_⟩
    · simp only
      have : (1 / 2 + ζ * (x1 - 1 / 2) - 1) * (x2 - 0) - (ζ * x2 - 0) * (x1 - 0) = -(x2 * (1 + ζ) / 2) := by ring
      rw [this]; exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hx2 h1) two_ne_zero)
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
    · simp only <;> field_simp <;> ring
  refine ⟨hU, hV, ?_⟩
  refine hT (1 / 2, 0) (x1, x2) _ _ _ hM hX hV hU ?_ ⟨2 * ζ / (1 + ζ), ?_, ?_⟩ ⟨1 / 2, ?_, ?_⟩
  · simp only
    have : (x1 - 1 / 2) * (2 * ζ / (1 + ζ) * x2 - 2 * ζ / (1 + ζ) * x2) -
        (x2 - 0) * (1 + 2 * ζ / (1 + ζ) * (x1 - 1) - 2 * ζ / (1 + ζ) * x1) = -(x2 * (1 - ζ) / (1 + ζ)) := by
      field_simp <;> ring
    rw [this]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero hx2 (fun e => hζ1 (by linarith))) h1)
  · simp only <;> ring
  · simp only <;> ring
  · simp only <;> ring
  · simp only <;> ring

/-- The parallel construction for an arbitrary base `A B` with midpoint `M` (reduction to `par_std` by the
frame of `A, B`): `D, D'` span the auxiliary parallel; `C` is not on the base, nor on the auxiliary parallel,
nor on the parallel at twice its distance. -/
theorem par_gen {T : Set (ℝ × ℝ)} (hT : LLC T) {A B M D D' C : ℝ × ℝ} (hAB : A ≠ B) (hA : A ∈ T)
    (hB : B ∈ T) (hM : M ∈ T) (hMe : M = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) (hD : D ∈ T) (hD' : D' ∈ T)
    (hDD : (frame A B D).1 ≠ (frame A B D').1) (hh : (frame A B D').2 = (frame A B D).2)
    (hh0 : (frame A B D).2 ≠ 0) (hC : C ∈ T) (hc0 : (frame A B C).2 ≠ 0)
    (hch : (frame A B C).2 ≠ (frame A B D).2) (hc2 : (frame A B C).2 ≠ 2 * (frame A B D).2) :
    ∃ d ∈ T, d ≠ C ∧ (frame A B d).2 = (frame A B C).2 := by
  have hT' := hT.pull hAB
  have fm : ∀ {p : ℝ × ℝ}, p ∈ T → frame A B p ∈ {y | unframe A B y ∈ T} := fun {p} hp => by
    show unframe A B (frame A B p) ∈ T
    rw [unframe_frame hAB]; exact hp
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (0, 0) ∈ T
    have : unframe A B (0, 0) = A := by ext <;> simp [unframe]
    rw [this]; exact hA
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (1, 0) ∈ T
    have : unframe A B (1, 0) = B := by ext <;> simp [unframe]
    rw [this]; exact hB
  have hm : ((1 / 2 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (1 / 2, 0) ∈ T
    have : unframe A B (1 / 2, 0) = M := by rw [hMe]; ext <;> simp [unframe] <;> ring
    rw [this]; exact hM
  have hD'' : ((frame A B D').1, (frame A B D).2) ∈ {y | unframe A B y ∈ T} := by
    rw [← hh]; exact fm hD'
  have key := par_std (d1 := (frame A B D).1) (d1' := (frame A B D').1) (h := (frame A B D).2)
    (c1 := (frame A B C).1) (c := (frame A B C).2) hT' h0 h1 hm (fm hD) hD'' hDD hh0 (fm hC) hc0 hch hc2
  refine ⟨unframe A B ((frame A B C).1 - 1 + (frame A B C).2 / (frame A B D).2, (frame A B C).2), key, ?_, ?_⟩
  · intro h
    have := congrArg (frame A B) h
    rw [frame_unframe hAB] at this
    have h1 := congrArg Prod.fst this
    simp only at h1
    have : (frame A B C).2 / (frame A B D).2 = 1 := by linarith
    rw [div_eq_one_iff_eq hh0] at this
    exact hch this
  · rw [frame_unframe hAB]

/-- The complete parallel construction in the standard frame: from the base `(0,0),(1,0)` with midpoint,
an external point `X` and a point `Z` of `XM`, for every point `C` of the set there is another point of the set
at the same height. -/
theorem par_std_full {T : Set (ℝ × ℝ)} (hT : LLC T) {x1 x2 ζ c1 c : ℝ} (hA : ((0 : ℝ), (0 : ℝ)) ∈ T)
    (hB : ((1 : ℝ), (0 : ℝ)) ∈ T) (hM : ((1 / 2 : ℝ), (0 : ℝ)) ∈ T) (hX : (x1, x2) ∈ T) (hx2 : x2 ≠ 0)
    (hZ : (1 / 2 + ζ * (x1 - 1 / 2), ζ * x2) ∈ T) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (hζ2 : ζ ≠ -1)
    (hC : (c1, c) ∈ T) : ∃ d ∈ T, d ≠ (c1, c) ∧ d.2 = c := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * ζ / (1 + ζ) := ⟨_, rfl⟩
  have h1 : 1 + ζ ≠ 0 := fun e => hζ2 (by linarith)
  have ht' : t * (1 + ζ) = 2 * ζ := by rw [ht]; field_simp
  have ht0 : t ≠ 0 := by
    intro e; rw [e] at ht'; apply hζ0; linarith
  have ht1 : t - 1 ≠ 0 := by
    intro e; have : t = 1 := by linarith
    rw [this] at ht'; apply hζ1; linarith
  obtain ⟨hU, hV, hM2⟩ := step1_std hT hA hB hM hX hx2 hZ hζ0 hζ1 hζ2 ht
  have hh : t * x2 ≠ 0 := mul_ne_zero ht0 hx2
  have hUV : (1 + t * (x1 - 1), t * x2) ≠ (t * x1, t * x2) := by
    intro e; have := congrArg Prod.fst e; simp only at this; apply ht1; linarith
  by_cases hc0 : c = 0
  · subst hc0
    by_cases hc1 : c1 = 0
    · subst hc1
      exact ⟨(1, 0), hB, by simp, rfl⟩
    · exact ⟨(0, 0), hA, fun e => hc1 (by simpa using (congrArg Prod.fst e).symm), rfl⟩
  by_cases hch : c = t * x2
  · subst hch
    by_cases hUC : (1 + t * (x1 - 1), t * x2) = (c1, t * x2)
    · exact ⟨_, hV, fun e => hUV (hUC.trans e.symm), rfl⟩
    · exact ⟨_, hU, hUC, rfl⟩
  by_cases hc2 : c = 2 * (t * x2)
  · -- swap the roles of the two parallels
    have hVU : (1 + t * (x1 - 1), t * x2) ≠ (t * x1, t * x2) := hUV
    have hd : t * x1 - (1 + t * (x1 - 1)) = t - 1 := by ring
    have f1 : ∀ p : ℝ × ℝ, (frame (1 + t * (x1 - 1), t * x2) (t * x1, t * x2) p).2 =
        (p.2 - t * x2) / (t - 1) := by
      intro p
      simp only [frame]
      rw [show t * x1 - (1 + t * (x1 - 1)) = t - 1 by ring]
      field_simp; ring
    have f2 : ∀ p : ℝ × ℝ, (frame (1 + t * (x1 - 1), t * x2) (t * x1, t * x2) p).1 =
        (p.1 - (1 + t * (x1 - 1))) / (t - 1) := by
      intro p
      simp only [frame]
      rw [show t * x1 - (1 + t * (x1 - 1)) = t - 1 by ring]
      field_simp; ring
    obtain ⟨d, hdT, hdC, hd2⟩ := par_gen hT hVU hU hV hM2 (by ext <;> simp <;> ring) hA hB
      (D := (0, 0)) (D' := (1, 0)) (C := (c1, c))
      (by rw [f2, f2]; intro e; have := (div_left_inj' ht1).mp e; simp only at this; linarith)
      (by simp only [f1]) (by rw [f1]; exact div_ne_zero (by simpa using hh) ht1)
      hC (by rw [f1]; exact div_ne_zero (sub_ne_zero.mpr hch) ht1)
      (by
        rw [f1, f1]; intro e; have := (div_left_inj' ht1).mp e; simp only at this; apply hc0; linarith)
      (by
        rw [f1, f1]; intro e
        rw [← mul_div_assoc, div_left_inj' ht1] at e
        simp only at e; apply hh; rw [hc2] at e; linarith)
    refine ⟨d, hdT, hdC, ?_⟩
    rw [f1, f1] at hd2
    have := (div_left_inj' ht1).mp hd2
    linarith
  · have hd1 : 1 + t * (x1 - 1) ≠ t * x1 := fun e => hUV (by rw [e])
    have key := par_std hT hA hB hM hU hV hd1 hh hC hc0 hch hc2
    refine ⟨_, key, ?_, rfl⟩
    intro e
    have h1 := congrArg Prod.fst e
    simp only at h1
    have : c / (t * x2) = 1 := by linarith
    rw [div_eq_one_iff_eq hh] at this
    exact hch this

/-- **The parallel tool from a base with midpoint** (general position): for a base `A ≠ B` of the set with
midpoint `M` in the set, an external point `X` and a point `Z = M + ζ (X - M)`, `ζ ∉ {0, 1, -1}`, of the set
on the line `XM`, every point `C` of the set has another point `d` of the set on the parallel to `AB` thru `C`
(expressed by the equality of the heights in the frame of `A, B`). -/
theorem par_from_base {T : Set (ℝ × ℝ)} (hT : LLC T) {A B M X Z C : ℝ × ℝ} {ζ : ℝ} (hAB : A ≠ B)
    (hA : A ∈ T) (hB : B ∈ T) (hM : M ∈ T) (hMe : M = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) (hX : X ∈ T)
    (hXo : (frame A B X).2 ≠ 0) (hZ : Z ∈ T)
    (hZe : Z = (M.1 + ζ * (X.1 - M.1), M.2 + ζ * (X.2 - M.2))) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ≠ -1) (hC : C ∈ T) : ∃ d ∈ T, d ≠ C ∧ (frame A B d).2 = (frame A B C).2 := by
  have hN := (ne_coords hAB).ne'
  have hT' := hT.pull hAB
  have fm : ∀ {p : ℝ × ℝ}, p ∈ T → frame A B p ∈ {y | unframe A B y ∈ T} := fun {p} hp => by
    show unframe A B (frame A B p) ∈ T
    rw [unframe_frame hAB]; exact hp
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (0, 0) ∈ T
    have : unframe A B (0, 0) = A := by ext <;> simp [unframe]
    rw [this]; exact hA
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (1, 0) ∈ T
    have : unframe A B (1, 0) = B := by ext <;> simp [unframe]
    rw [this]; exact hB
  have hm : ((1 / 2 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (1 / 2, 0) ∈ T
    have : unframe A B (1 / 2, 0) = M := by rw [hMe]; ext <;> simp [unframe] <;> ring
    rw [this]; exact hM
  have hZ' : (1 / 2 + ζ * ((frame A B X).1 - 1 / 2), ζ * (frame A B X).2) ∈ {y | unframe A B y ∈ T} := by
    have : frame A B Z = (1 / 2 + ζ * ((frame A B X).1 - 1 / 2), ζ * (frame A B X).2) := by
      rw [hZe, hMe]
      ext <;> simp only [frame] <;> field_simp <;> ring
    rw [← this]; exact fm hZ
  obtain ⟨d, hdT, hdC, hd2⟩ := par_std_full (x1 := (frame A B X).1) (x2 := (frame A B X).2) (ζ := ζ)
    (c1 := (frame A B C).1) (c := (frame A B C).2) hT' h0 h1 hm (fm hX) hXo hZ' hζ0 hζ1 hζ2 (fm hC)
  refine ⟨unframe A B d, hdT, ?_, ?_⟩
  · intro h
    apply hdC
    have := congrArg (frame A B) h
    rw [frame_unframe hAB] at this
    exact this
  · rw [frame_unframe hAB]; exact hd2

theorem frame_snd (A B p : ℝ × ℝ) :
    (frame A B p).2 = ((B.1 - A.1) * (p.2 - A.2) - (B.2 - A.2) * (p.1 - A.1)) /
      ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2) := by
  simp only [frame]; ring

/-- The parallel tool from a base with midpoint, in terms of cross products. -/
theorem par_base {T : Set (ℝ × ℝ)} (hT : LLC T) {A B M X Z C : ℝ × ℝ} {ζ : ℝ} (hAB : A ≠ B)
    (hA : A ∈ T) (hB : B ∈ T) (hM : M ∈ T) (hMe : M = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) (hX : X ∈ T)
    (hXo : (B.1 - A.1) * (X.2 - A.2) - (B.2 - A.2) * (X.1 - A.1) ≠ 0) (hZ : Z ∈ T)
    (hZe : Z = (M.1 + ζ * (X.1 - M.1), M.2 + ζ * (X.2 - M.2))) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ≠ -1) (hC : C ∈ T) :
    ∃ d ∈ T, d ≠ C ∧ (B.1 - A.1) * (d.2 - C.2) - (B.2 - A.2) * (d.1 - C.1) = 0 := by
  have hN := (ne_coords hAB).ne'
  obtain ⟨d, hd, hdC, h2⟩ := par_from_base hT hAB hA hB hM hMe hX
    (by rw [frame_snd]; exact div_ne_zero hXo hN) hZ hZe hζ0 hζ1 hζ2 hC
  refine ⟨d, hd, hdC, ?_⟩
  rw [frame_snd, frame_snd] at h2
  have := (div_left_inj' hN).mp h2
  linarith

/-- The first step in general position (the ends of the auxiliary parallel). -/
theorem step1_gen {T : Set (ℝ × ℝ)} (hT : LLC T) {A B M X Z : ℝ × ℝ} {ζ t : ℝ} (hAB : A ≠ B)
    (hA : A ∈ T) (hB : B ∈ T) (hM : M ∈ T) (hMe : M = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) (hX : X ∈ T)
    (hXo : (frame A B X).2 ≠ 0) (hZ : Z ∈ T)
    (hZe : Z = (M.1 + ζ * (X.1 - M.1), M.2 + ζ * (X.2 - M.2))) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ≠ -1) (ht : t = 2 * ζ / (1 + ζ)) :
    unframe A B (1 + t * ((frame A B X).1 - 1), t * (frame A B X).2) ∈ T ∧
      unframe A B (t * (frame A B X).1, t * (frame A B X).2) ∈ T := by
  have hN := (ne_coords hAB).ne'
  have hT' := hT.pull hAB
  have fm : ∀ {p : ℝ × ℝ}, p ∈ T → frame A B p ∈ {y | unframe A B y ∈ T} := fun {p} hp => by
    show unframe A B (frame A B p) ∈ T
    rw [unframe_frame hAB]; exact hp
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (0, 0) ∈ T
    have : unframe A B (0, 0) = A := by ext <;> simp [unframe]
    rw [this]; exact hA
  have h1 : ((1 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (1, 0) ∈ T
    have : unframe A B (1, 0) = B := by ext <;> simp [unframe]
    rw [this]; exact hB
  have hm : ((1 / 2 : ℝ), (0 : ℝ)) ∈ {y | unframe A B y ∈ T} := by
    show unframe A B (1 / 2, 0) ∈ T
    have : unframe A B (1 / 2, 0) = M := by rw [hMe]; ext <;> simp [unframe] <;> ring
    rw [this]; exact hM
  have hZ' : (1 / 2 + ζ * ((frame A B X).1 - 1 / 2), ζ * (frame A B X).2) ∈ {y | unframe A B y ∈ T} := by
    have : frame A B Z = (1 / 2 + ζ * ((frame A B X).1 - 1 / 2), ζ * (frame A B X).2) := by
      rw [hZe, hMe]
      ext <;> simp only [frame] <;> field_simp <;> ring
    rw [← this]; exact fm hZ
  obtain ⟨hU, hV, -⟩ := step1_std hT' h0 h1 hm (fm hX) hXo hZ' hζ0 hζ1 hζ2 ht
  exact ⟨hU, hV⟩

/-! ### The given circle -/

/-- A set of points closed under the intersection of a line thru two of its points with the unit circle. -/
def GC (T : Set (ℝ × ℝ)) : Prop :=
  ∀ p q x : ℝ × ℝ, p ∈ T → q ∈ T → p ≠ q → OnLine p q x → x.1 ^ 2 + x.2 ^ 2 = 1 → x ∈ T

/-- The data of the hard half of the Poncelet-Steiner theorem in the frame `O = (0,0)`, `P = (1,0)`: a set `T`
of points closed under line-line and line-circle intersections, containing `O`, `P`, and a point `E` off the
line `OP` and off the circle. -/
structure Setup (T : Set (ℝ × ℝ)) (E : ℝ × ℝ) : Prop where
  ll : LLC T
  gc : GC T
  hO : ((0 : ℝ), (0 : ℝ)) ∈ T
  hP : ((1 : ℝ), (0 : ℝ)) ∈ T
  hE : E ∈ T
  hE2 : E.2 ≠ 0
  hE1 : E.1 ^ 2 + E.2 ^ 2 ≠ 1

theorem exists_scale {a : ℝ × ℝ} (ha : a.1 ^ 2 + a.2 ^ 2 ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ s ^ 2 * (a.1 ^ 2 + a.2 ^ 2) = 1 := by
  have hpos : 0 < a.1 ^ 2 + a.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm ha)
  refine ⟨1 / √(a.1 ^ 2 + a.2 ^ 2), by positivity, ?_⟩
  rw [div_pow, Real.sq_sqrt hpos.le]; field_simp

variable {T : Set (ℝ × ℝ)} {E : ℝ × ℝ}

theorem Setup.circ_mem (h : Setup T E) {a : ℝ × ℝ} (ha : a ∈ T) (ha0 : a.1 ^ 2 + a.2 ^ 2 ≠ 0) {s : ℝ}
    (hs : s ^ 2 * (a.1 ^ 2 + a.2 ^ 2) = 1) : (s * a.1, s * a.2) ∈ T := by
  refine h.gc (0, 0) a _ h.hO ha ?_ ⟨s, ?_, ?_⟩ ?_
  · intro e; apply ha0; rw [← e]; simp
  · simp
  · simp
  · simp only; linear_combination hs

/-- Cross product. -/
def crs (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

theorem Setup.diam_par_X (h : Setup T E) {w X : ℝ × ℝ} (hw : w ∈ T) (hw1 : w.1 ^ 2 + w.2 ^ 2 = 1)
    (hX : X ∈ T) (hXo : crs w X ≠ 0) (hX1 : X.1 ^ 2 + X.2 ^ 2 ≠ 1) {C : ℝ × ℝ} (hC : C ∈ T) :
    ∃ d ∈ T, d ≠ C ∧ crs w (d - C) = 0 := by
  have hw0 : w.1 ^ 2 + w.2 ^ 2 ≠ 0 := by rw [hw1]; exact one_ne_zero
  have hX0 : X.1 ^ 2 + X.2 ^ 2 ≠ 0 := by
    intro e
    apply hXo
    have h1 : X.1 = 0 := by nlinarith [sq_nonneg X.1, sq_nonneg X.2]
    have h2 : X.2 = 0 := by nlinarith [sq_nonneg X.1, sq_nonneg X.2]
    simp [crs, h1, h2]
  obtain ⟨s, hs0, hs⟩ := exists_scale hX0
  have hmw : (-1 * w.1, -1 * w.2) ∈ T := h.circ_mem hw hw0 (s := -1) (by rw [hw1]; norm_num)
  have hZ := h.circ_mem hX hX0 hs
  have hAB : ((-1 * w.1, -1 * w.2) : ℝ × ℝ) ≠ w := by
    intro e
    have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    simp only at h1 h2
    have : w.1 = 0 := by linarith
    have : w.2 = 0 := by linarith
    apply hw0; simp [*]
  obtain ⟨d, hd, hdC, hd2⟩ := par_base h.ll (A := (-1 * w.1, -1 * w.2)) (B := w) (M := (0, 0)) (X := X)
    (Z := (s * X.1, s * X.2)) (C := C) (ζ := s) hAB hmw hw h.hO (by ext <;> simp) hX
    (by
      simp only
      intro e; apply hXo; unfold crs; linear_combination e / 2)
    hZ (by ext <;> simp) hs0.ne'
    (by
      intro e
      rw [e] at hs
      apply hX1; linear_combination hs)
    (by intro e; linarith) hC
  refine ⟨d, hd, hdC, ?_⟩
  unfold crs
  simp only [Prod.fst_sub, Prod.snd_sub]
  simp only at hd2
  linear_combination hd2 / 2

theorem Setup.exists_X (h : Setup T E) {w : ℝ × ℝ} (hw1 : w.1 ^ 2 + w.2 ^ 2 = 1) :
    ∃ X ∈ T, crs w X ≠ 0 ∧ X.1 ^ 2 + X.2 ^ 2 ≠ 1 := by
  by_cases hc : crs w E = 0
  swap
  · exact ⟨E, h.hE, hc, h.hE1⟩
  have he2 := h.hE2
  have e0 : E.1 ^ 2 + E.2 ^ 2 ≠ 0 := by
    have := sq_pos_of_ne_zero he2; positivity
  obtain ⟨ζ, hζ0, hζ⟩ := exists_scale e0
  have hZ := h.circ_mem h.hE e0 hζ
  have hζ1 : ζ ≠ 1 := by
    intro e; rw [e] at hζ; apply h.hE1; linarith
  have hζ2 : ζ ≠ -1 := by intro e; linarith
  have hA : ((-1 : ℝ), (0 : ℝ)) ∈ T := by
    have := h.circ_mem h.hP (a := (1, 0)) (by norm_num) (s := -1) (by norm_num)
    simpa using this
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 * ζ / (1 + ζ) := ⟨_, rfl⟩
  have h1 : 1 + ζ ≠ 0 := fun e => hζ2 (by linarith)
  have ht' : t * (1 + ζ) = 2 * ζ := by rw [ht]; field_simp
  have hfr : (frame (-1, 0) (1, 0) E).2 = E.2 / 2 := by
    rw [frame_snd]; norm_num; ring
  obtain ⟨hU, -⟩ := step1_gen h.ll (A := (-1, 0)) (B := (1, 0)) (M := (0, 0)) (X := E)
    (Z := (ζ * E.1, ζ * E.2)) (ζ := ζ) (t := t) (by intro e; have := congrArg Prod.fst e; norm_num at this) hA h.hP h.hO (by ext <;> simp) h.hE
    (by rw [hfr]; exact div_ne_zero he2 two_ne_zero) hZ (by ext <;> simp) hζ0.ne' hζ1 hζ2 ht
  have eU : unframe (-1, 0) (1, 0) (1 + t * ((frame (-1, 0) (1, 0) E).1 - 1), t * (frame (-1, 0) (1, 0) E).2)
      = (1 + t * (E.1 - 1), t * E.2) := by
    ext <;> simp [unframe, frame] <;> ring
  rw [eU] at hU
  refine ⟨_, hU, ?_, ?_⟩
  · have hw2 : w.2 ≠ 0 := by
      intro e
      unfold crs at hc
      rw [e] at hc hw1
      have : w.1 = 0 := by
        have : w.1 * E.2 = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exact absurd h' he2
      rw [this] at hw1; norm_num at hw1
    have ht1 : 1 - t ≠ 0 := by
      intro e; have : t = 1 := by linarith
      rw [this] at ht'; apply hζ1; linarith
    unfold crs at hc ⊢
    simp only
    intro e
    apply mul_ne_zero hw2 ht1
    linear_combination -e + t * hc
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / ζ := ⟨_, rfl⟩
    have hrζ : r * ζ = 1 := by rw [hr]; field_simp
    have hr0 : 0 < r := by rw [hr]; positivity
    have hr2 : r ^ 2 = E.1 ^ 2 + E.2 ^ 2 := by
      have : (r * ζ) ^ 2 * (E.1 ^ 2 + E.2 ^ 2) = r ^ 2 := by linear_combination (r ^ 2) * hζ
      rw [hrζ] at this; linarith
    have hrt : t * (r + 1) = 2 := by linear_combination r * ht' - (t - 2) * hrζ
    have hre : 0 < r + E.1 := by
      have : E.1 ^ 2 < r ^ 2 := by have := sq_pos_of_ne_zero he2; linarith
      nlinarith
    have hr1 : r - 1 ≠ 0 := by
      intro e; have : r = 1 := by linarith
      apply h.hE1; rw [← hr2, this]; norm_num
    have ht0 : t ≠ 0 := by intro e; rw [e] at hrt; norm_num at hrt
    simp only
    intro e
    have key : ((1 + t * (E.1 - 1)) ^ 2 + (t * E.2) ^ 2 - 1) * (r + 1) = 2 * t * (r - 1) * (r + E.1) := by
      linear_combination (-(r + 1) * t ^ 2) * hr2 + (t * (r ^ 2 - 2 * E.1 + 1)) * hrt
    rw [e, sub_self, zero_mul] at key
    have : 2 * t * (r - 1) * (r + E.1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ht0) hr1) hre.ne'
    exact this key.symm

theorem Setup.diam_par (h : Setup T E) {w : ℝ × ℝ} (hw : w ∈ T) (hw1 : w.1 ^ 2 + w.2 ^ 2 = 1)
    {C : ℝ × ℝ} (hC : C ∈ T) : ∃ d ∈ T, d ≠ C ∧ crs w (d - C) = 0 := by
  obtain ⟨X, hX, hXo, hX1⟩ := h.exists_X hw1
  exact h.diam_par_X hw hw1 hX hXo hX1 hC

/-- Parallels to a line thru `O` and a point of the set. -/
theorem Setup.par_O (h : Setup T E) {a : ℝ × ℝ} (ha : a ∈ T) (ha0 : a ≠ (0, 0)) {C : ℝ × ℝ} (hC : C ∈ T) :
    ∃ d ∈ T, d ≠ C ∧ crs a (d - C) = 0 := by
  have hn : a.1 ^ 2 + a.2 ^ 2 ≠ 0 := by
    intro e
    apply ha0
    have h1 : a.1 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
    have h2 : a.2 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
    exact Prod.ext h1 h2
  obtain ⟨s, hs0, hs⟩ := exists_scale hn
  have hw := h.circ_mem ha hn hs
  obtain ⟨d, hd, hdC, hd2⟩ := h.diam_par hw (by simp only; linear_combination hs) hC
  refine ⟨d, hd, hdC, ?_⟩
  unfold crs at hd2 ⊢
  simp only [Prod.fst_sub, Prod.snd_sub] at hd2 ⊢
  have : s * (a.1 * (d.2 - C.2) - a.2 * (d.1 - C.1)) = 0 := by linear_combination hd2
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hs0.ne'
  · exact h'

theorem smul_of_crs {a v : ℝ × ℝ} (ha : a ≠ (0, 0)) (h : crs a v = 0) :
    ∃ κ : ℝ, v.1 = κ * a.1 ∧ v.2 = κ * a.2 := by
  have hn : a.1 ^ 2 + a.2 ^ 2 ≠ 0 := by
    intro e
    apply ha
    have h1 : a.1 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
    have h2 : a.2 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2]
    exact Prod.ext h1 h2
  unfold crs at h
  refine ⟨(v.1 * a.1 + v.2 * a.2) / (a.1 ^ 2 + a.2 ^ 2), ?_, ?_⟩
  · field_simp; linear_combination (-a.2) * h
  · field_simp; linear_combination a.1 * h

theorem crs_trans {a b v : ℝ × ℝ} (ha : a ≠ (0, 0)) (hab : crs a b = 0) (hav : crs a v = 0) :
    crs (b - a) v = 0 := by
  unfold crs at *
  simp only [Prod.fst_sub, Prod.snd_sub]
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := fun h2 => ha (Prod.ext h1 h2)
    have : a.2 * ((b.1 - a.1) * v.2 - (b.2 - a.2) * v.1) = 0 := by
      linear_combination (b.2 - a.2) * hav - v.2 * hab
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h2
    · exact h'
  · have : a.1 * ((b.1 - a.1) * v.2 - (b.2 - a.2) * v.1) = 0 := by
      linear_combination (b.1 - a.1) * hav - v.1 * hab
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h1
    · exact h'

theorem Setup.gen_par (h : Setup T E) {a b : ℝ × ℝ} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) {C : ℝ × ℝ}
    (hC : C ∈ T) : ∃ d ∈ T, d ≠ C ∧ crs (b - a) (d - C) = 0 := by
  by_cases hc : crs a b = 0
  · by_cases ha0 : a = (0, 0)
    · have hb0 : b ≠ (0, 0) := by rw [← ha0]; exact hab.symm
      obtain ⟨d, hd, hdC, hd2⟩ := h.par_O hb hb0 hC
      refine ⟨d, hd, hdC, ?_⟩
      rw [ha0, show b - (0, 0) = b by ext <;> simp]; exact hd2
    · obtain ⟨d, hd, hdC, hd2⟩ := h.par_O ha ha0 hC
      exact ⟨d, hd, hdC, crs_trans ha0 hc hd2⟩
  · have ha0 : a ≠ (0, 0) := by
      intro e; apply hc; rw [e]; simp [crs]
    have hb0 : b ≠ (0, 0) := by
      intro e; apply hc; rw [e]; simp [crs]
    obtain ⟨d1, hd1, hd1b, hd1c⟩ := h.par_O ha ha0 hb
    obtain ⟨d2, hd2, hd2a, hd2c⟩ := h.par_O hb hb0 ha
    obtain ⟨k1, hk11, hk12⟩ := smul_of_crs ha0 hd1c
    obtain ⟨k2, hk21, hk22⟩ := smul_of_crs hb0 hd2c
    simp only [Prod.fst_sub, Prod.snd_sub] at hk11 hk12 hk21 hk22
    have hk1 : k1 ≠ 0 := by
      intro e; apply hd1b; rw [e] at hk11 hk12
      exact Prod.ext (by linarith) (by linarith)
    have hk2 : k2 ≠ 0 := by
      intro e; apply hd2a; rw [e] at hk21 hk22
      exact Prod.ext (by linarith) (by linarith)
    have hs : (a.1 + b.1, a.2 + b.2) ∈ T := by
      refine h.ll b d1 a d2 _ hb hd1 ha hd2 ?_ ⟨1 / k1, ?_, ?_⟩ ⟨1 / k2, ?_, ?_⟩
      · have : (d1.1 - b.1) * (d2.2 - a.2) - (d1.2 - b.2) * (d2.1 - a.1) = k1 * k2 * crs a b := by
          rw [hk11, hk12, hk21, hk22]; unfold crs; ring
        rw [this]; exact mul_ne_zero (mul_ne_zero hk1 hk2) hc
      · simp only; field_simp; linarith
      · simp only; field_simp; linarith
      · simp only; field_simp; linarith
      · simp only; field_simp; linarith
    have hM : ((a.1 + b.1) / 2, (a.2 + b.2) / 2) ∈ T := by
      refine h.ll (0, 0) (a.1 + b.1, a.2 + b.2) a b _ h.hO hs ha hb ?_ ⟨1 / 2, ?_, ?_⟩ ⟨1 / 2, ?_, ?_⟩
      · have : (a.1 + b.1 - 0) * (b.2 - a.2) - (a.2 + b.2 - 0) * (b.1 - a.1) = 2 * crs a b := by
          unfold crs; ring
        rw [this]; exact mul_ne_zero two_ne_zero hc
      all_goals (simp only; ring)
    have hs0 : (a.1 + b.1) ^ 2 + (a.2 + b.2) ^ 2 ≠ 0 := by
      intro e
      apply hc
      have h1 : a.1 + b.1 = 0 := by nlinarith [sq_nonneg (a.1 + b.1), sq_nonneg (a.2 + b.2)]
      have h2 : a.2 + b.2 = 0 := by nlinarith [sq_nonneg (a.1 + b.1), sq_nonneg (a.2 + b.2)]
      unfold crs
      have : b.1 = -a.1 := by linarith
      have : b.2 = -a.2 := by linarith
      simp [*]; ring
    obtain ⟨σ, hσ0, hσ⟩ := exists_scale (a := (a.1 + b.1, a.2 + b.2)) hs0
    have hZ := h.circ_mem hs (a := (a.1 + b.1, a.2 + b.2)) hs0 (s := -σ) (by simp only at hσ ⊢; linear_combination hσ)
    obtain ⟨d, hd, hdC, hd2⟩ := par_base h.ll (A := a) (B := b) (M := ((a.1 + b.1) / 2, (a.2 + b.2) / 2))
      (X := (0, 0)) (Z := (-σ * (a.1 + b.1), -σ * (a.2 + b.2))) (C := C) (ζ := 1 + 2 * σ) hab ha hb hM rfl h.hO
      (by simp only; intro e; apply hc; unfold crs; linear_combination e) hZ
      (by ext <;> simp only <;> ring) (by linarith) (by linarith) (by linarith) hC
    refine ⟨d, hd, hdC, ?_⟩
    unfold crs
    simp only [Prod.fst_sub, Prod.snd_sub]
    exact hd2

/-! ### Simulating the parallel tool -/

theorem crs_par_trans {u v w : ℝ × ℝ} (hu : u ≠ (0, 0)) (h1 : crs u v = 0) (h2 : crs u w = 0) : crs v w = 0 := by
  obtain ⟨k, hk1, hk2⟩ := smul_of_crs hu h1
  obtain ⟨k', hk1', hk2'⟩ := smul_of_crs hu h2
  unfold crs; rw [hk1, hk2, hk1', hk2']; ring

/-- A line `pq` of the parallel-tool constructions is a line spanned by two points of `T`. -/
def TL (T : Set (ℝ × ℝ)) (p q : ℝ × ℝ) : Prop :=
  p ≠ q ∧ ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ crs (b - a) (q - p) = 0 ∧ crs (b - a) (p - a) = 0

theorem ne_zero_of_ne {a b : ℝ × ℝ} (h : a ≠ b) : b - a ≠ (0, 0) := by
  intro e; apply h
  have h1 := congrArg Prod.fst e
  have h2 := congrArg Prod.snd e
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
  exact Prod.ext (by linarith) (by linarith)

theorem Setup.rp_sim (h : Setup T E) {S' : Set (ℝ × ℝ)} (hS' : ∀ s ∈ S', s ∈ T) {o : RCObj}
    (ho : RPConstructible S' o) :
    (match o with
      | .point x => x ∈ T
      | .line p q => TL T p q
      | .circle _ _ => True) := by
  induction ho with
  | init hx => exact hS' _ hx
  | @line p q hp hq hpq ihp ihq =>
    refine ⟨hpq, p, ihp, q, ihq, hpq, ?_, ?_⟩ <;> unfold crs <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring
  | @parallel c p q hc hl hpq ihc ihl =>
    obtain ⟨-, a, ha, b, hb, hab, h1, h2⟩ := ihl
    obtain ⟨d, hd, hdc, hd2⟩ := h.gen_par ha hb hab ihc
    have hne : (c + (q - p)) ≠ c := by
      intro e
      apply hpq
      have h1 := congrArg Prod.fst e
      have h2 := congrArg Prod.snd e
      simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at h1 h2
      exact (Prod.ext (by linarith) (by linarith)).symm
    refine ⟨hne.symm, c, ihc, d, hd, hdc.symm, ?_, ?_⟩
    · have := crs_par_trans (ne_zero_of_ne hab) hd2 h1
      simpa using this
    · unfold crs; simp
  | @lineLine p q p' q' x hl hl' hdet hx hx' ih ih' =>
    obtain ⟨-, a, ha, b, hb, hab, h1, h2⟩ := ih
    obtain ⟨-, a', ha', b', hb', hab', h1', h2'⟩ := ih'
    have hq : q - p ≠ (0, 0) := by
      intro e
      apply hdet
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      simp only [Prod.fst_sub, Prod.snd_sub] at e1 e2
      rw [e1, e2]; ring
    have hq' : q' - p' ≠ (0, 0) := by
      intro e
      apply hdet
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      simp only [Prod.fst_sub, Prod.snd_sub] at e1 e2
      rw [e1, e2]; ring
    obtain ⟨k, hk1, hk2⟩ := smul_of_crs (ne_zero_of_ne hab) h1
    obtain ⟨k', hk1', hk2'⟩ := smul_of_crs (ne_zero_of_ne hab') h1'
    obtain ⟨m, hm1, hm2⟩ := smul_of_crs (ne_zero_of_ne hab) h2
    obtain ⟨m', hm1', hm2'⟩ := smul_of_crs (ne_zero_of_ne hab') h2'
    simp only [Prod.fst_sub, Prod.snd_sub] at hk1 hk2 hk1' hk2' hm1 hm2 hm1' hm2'
    obtain ⟨t, ht1, ht2⟩ := hx
    obtain ⟨t', ht1', ht2'⟩ := hx'
    have hdet' : (b.1 - a.1) * (b'.2 - a'.2) - (b.2 - a.2) * (b'.1 - a'.1) ≠ 0 := by
      intro e
      apply hdet
      rw [hk1, hk2, hk1', hk2']
      linear_combination (k * k') * e
    refine h.ll a b a' b' x ha hb ha' hb' hdet' ⟨m + t * k, ?_, ?_⟩ ⟨m' + t' * k', ?_, ?_⟩
    · linear_combination ht1 + hm1 + t * hk1
    · linear_combination ht2 + hm2 + t * hk2
    · linear_combination ht1' + hm1' + t' * hk1'
    · linear_combination ht2' + hm2' + t' * hk2'

theorem Setup.axis_arith (h : Setup T E) {a b : ℝ} (ha : (a, (0 : ℝ)) ∈ T) (hb : (b, (0 : ℝ)) ∈ T) :
    (a + b, (0 : ℝ)) ∈ T ∧ (a - b, (0 : ℝ)) ∈ T ∧ (a * b, (0 : ℝ)) ∈ T ∧ (b ≠ 0 → (a / b, (0 : ℝ)) ∈ T) := by
  set S' : Set (ℝ × ℝ) := {(0, 0), (1, 0), (a, 0), (b, 0), E} with hS'def
  have hS' : ∀ s ∈ S', s ∈ T := by
    rintro s (rfl | rfl | rfl | rfl | rfl)
    · exact h.hO
    · exact h.hP
    · exact ha
    · exact hb
    · exact h.hE
  obtain ⟨h1, h2, h3, h4⟩ := rp_add_sub_mul_div (S := S') (a := a) (b := b) (e := E) h.hE2
    (by simp [hS'def]) (by simp [hS'def]) (by simp [hS'def]) (by simp [hS'def]) (by simp [hS'def])
  exact ⟨h.rp_sim hS' h1, h.rp_sim hS' h2, h.rp_sim hS' h3, fun hb0 => h.rp_sim hS' (h4 hb0)⟩

/-- The abscissae of the points of `T` on the `x`-axis form a subfield of `ℝ`. -/
def Setup.K (h : Setup T E) : Subfield ℝ where
  carrier := {a | (a, (0 : ℝ)) ∈ T}
  mul_mem' {a b} ha hb := (h.axis_arith ha hb).2.2.1
  one_mem' := h.hP
  add_mem' {a b} ha hb := (h.axis_arith ha hb).1
  zero_mem' := h.hO
  neg_mem' {a} ha := by
    have := (h.axis_arith (a := 0) (b := a) h.hO ha).2.1
    simpa using this
  inv_mem' {a} ha := by
    by_cases h0 : a = 0
    · subst h0; simpa using h.hO
    · have := (h.axis_arith (a := 1) (b := a) h.hP ha).2.2.2 h0
      simpa using this

theorem Setup.mem_K (h : Setup T E) {a : ℝ} : a ∈ h.K ↔ (a, (0 : ℝ)) ∈ T := Iff.rfl

/-! ### The perpendicular axis and the grid -/

theorem Setup.hmP (h : Setup T E) : ((-1 : ℝ), (0 : ℝ)) ∈ T := by
  have := h.circ_mem h.hP (a := (1, 0)) (by norm_num) (s := -1) (by norm_num)
  simpa using this

/-- Horizontal parallel: through every point of `T` there is a second point of `T` at the same height. -/
theorem Setup.horiz (h : Setup T E) {C : ℝ × ℝ} (hC : C ∈ T) :
    ∃ d ∈ T, d.2 = C.2 ∧ d.1 ≠ C.1 := by
  obtain ⟨d, hd, hdC, hd2⟩ := h.gen_par h.hO h.hP (by intro e; have := congrArg Prod.fst e; norm_num at this) hC
  unfold crs at hd2
  simp only [Prod.fst_sub, Prod.snd_sub] at hd2
  have h2 : d.2 = C.2 := by linarith
  refine ⟨d, hd, h2, fun e => hdC (Prod.ext e h2)⟩

theorem Setup.exists_unit_pt (h : Setup T E) : ∃ u ∈ T, u.1 ^ 2 + u.2 ^ 2 = 1 ∧ u.2 ≠ 0 := by
  have he2 := h.hE2
  have e0 : E.1 ^ 2 + E.2 ^ 2 ≠ 0 := by
    have := sq_pos_of_ne_zero he2; positivity
  obtain ⟨s, hs0, hs⟩ := exists_scale e0
  refine ⟨_, h.circ_mem h.hE e0 hs, ?_, ?_⟩
  · simp only; linear_combination hs
  · exact mul_ne_zero hs0.ne' he2

/-- The point `(0,1)`. -/
theorem Setup.hJ (h : Setup T E) : ((0 : ℝ), (1 : ℝ)) ∈ T := by
  obtain ⟨u, hu, hu1, hu2⟩ := h.exists_unit_pt
  have hu1' : u.1 + 1 ≠ 0 := by
    intro e
    have : u.1 = -1 := by linarith
    rw [this] at hu1
    apply hu2
    nlinarith [sq_nonneg u.2]
  have hu' : ((-u.1, u.2) : ℝ × ℝ) ∈ T := by
    obtain ⟨d, hd, hd2, hd1⟩ := h.horiz hu
    by_cases hu0 : u.1 = 0
    · have : ((-u.1, u.2) : ℝ × ℝ) = u := by ext <;> simp [hu0]
      rw [this]; exact hu
    · refine h.gc u d _ hu hd (fun e => hd1 (by rw [← e])) ⟨-2 * u.1 / (d.1 - u.1), ?_, ?_⟩ ?_
      · have : d.1 - u.1 ≠ 0 := sub_ne_zero.mpr hd1
        simp only; field_simp; ring
      · simp only; rw [hd2]; ring
      · simp only; linear_combination hu1
  have hX : ((0 : ℝ), u.2 / (1 + u.1)) ∈ T := by
    have h1 : 1 + u.1 ≠ 0 := by rw [add_comm]; exact hu1'
    refine h.ll (-1, 0) u (1, 0) (-u.1, u.2) _ h.hmP hu h.hP hu' ?_ ⟨1 / (1 + u.1), ?_, ?_⟩
      ⟨1 / (1 + u.1), ?_, ?_⟩
    · simp only
      have : (u.1 - -1) * (u.2 - 0) - (u.2 - 0) * (-u.1 - 1) = 2 * u.2 * (u.1 + 1) := by ring
      rw [this]; exact mul_ne_zero (mul_ne_zero two_ne_zero hu2) hu1'
    · simp only; field_simp; ring
    · simp only; field_simp  <;> ring
    · simp only; field_simp; ring
    · simp only; field_simp  <;> ring
  have h1 : 1 + u.1 ≠ 0 := by rw [add_comm]; exact hu1'
  refine h.gc (0, 0) (0, u.2 / (1 + u.1)) _ h.hO hX ?_ ⟨(1 + u.1) / u.2, ?_, ?_⟩ ?_
  · intro e; have := congrArg Prod.snd e; simp only at this
    exact div_ne_zero hu2 h1 this.symm
  · simp
  · simp only; field_simp  <;> ring
  · simp

/-- Vertical parallel. -/
theorem Setup.vert (h : Setup T E) {C : ℝ × ℝ} (hC : C ∈ T) :
    ∃ d ∈ T, d.1 = C.1 ∧ d.2 ≠ C.2 := by
  obtain ⟨d, hd, hdC, hd2⟩ := h.gen_par h.hO h.hJ (by intro e; have := congrArg Prod.snd e; norm_num at this) hC
  unfold crs at hd2
  simp only [Prod.fst_sub, Prod.snd_sub] at hd2
  have h2 : d.1 = C.1 := by linarith
  refine ⟨d, hd, h2, fun e => hdC (Prod.ext h2 e)⟩

theorem Setup.proj_x (h : Setup T E) {c1 c2 : ℝ} (hC : (c1, c2) ∈ T) : (c1, (0 : ℝ)) ∈ T := by
  obtain ⟨d, hd, hd1, hd2⟩ := h.vert hC
  simp only at hd1 hd2
  have hd2' : d.2 - c2 ≠ 0 := sub_ne_zero.mpr hd2
  refine h.ll (c1, c2) d (0, 0) (1, 0) _ hC hd h.hO h.hP ?_ ⟨-c2 / (d.2 - c2), ?_, ?_⟩ ⟨c1, ?_, ?_⟩
  · simp only; rw [hd1]; intro e; apply hd2'; linarith
  · simp only; rw [hd1]; ring
  · simp only; field_simp; ring
  · simp only; ring
  · simp only; ring

theorem Setup.proj_y (h : Setup T E) {c1 c2 : ℝ} (hC : (c1, c2) ∈ T) : ((0 : ℝ), c2) ∈ T := by
  obtain ⟨d, hd, hd2, hd1⟩ := h.horiz hC
  simp only at hd1 hd2
  have hd1' : d.1 - c1 ≠ 0 := sub_ne_zero.mpr hd1
  refine h.ll (c1, c2) d (0, 0) (0, 1) _ hC hd h.hO h.hJ ?_ ⟨-c1 / (d.1 - c1), ?_, ?_⟩ ⟨c2, ?_, ?_⟩
  · simp only; rw [hd2]; intro e; apply hd1'; linarith
  · simp only; field_simp; ring
  · simp only; rw [hd2]; ring
  · simp only; ring
  · simp only; ring

theorem Setup.y_to_x (h : Setup T E) {b : ℝ} (hB : ((0 : ℝ), b) ∈ T) : (b, (0 : ℝ)) ∈ T := by
  obtain ⟨d, hd, hdC, hd2⟩ := h.gen_par h.hJ h.hP (by intro e; have := congrArg Prod.fst e; norm_num at this) hB
  unfold crs at hd2
  simp only [Prod.fst_sub, Prod.snd_sub] at hd2
  have e : d.2 = b - d.1 := by linarith
  have hd1 : d.1 ≠ 0 := by
    intro e'; apply hdC; exact Prod.ext e' (by rw [e, e']; ring)
  refine h.ll (0, b) d (0, 0) (1, 0) _ hB hd h.hO h.hP ?_ ⟨b / d.1, ?_, ?_⟩ ⟨b, ?_, ?_⟩
  · simp only; rw [e]; intro e2; apply hd1; linarith
  · simp only; field_simp; ring
  · simp only; rw [e]; field_simp; ring
  · simp only; ring
  · simp only; ring

theorem Setup.x_to_y (h : Setup T E) {b : ℝ} (hB : (b, (0 : ℝ)) ∈ T) : ((0 : ℝ), b) ∈ T := by
  obtain ⟨d, hd, hdC, hd2⟩ := h.gen_par h.hJ h.hP (by intro e; have := congrArg Prod.fst e; norm_num at this) hB
  unfold crs at hd2
  simp only [Prod.fst_sub, Prod.snd_sub] at hd2
  have e : d.2 = b - d.1 := by linarith
  have hd1 : d.1 - b ≠ 0 := by
    intro e'; apply hdC; exact Prod.ext (by linarith) (by rw [e]; linarith)
  refine h.ll (b, 0) d (0, 0) (0, 1) _ hB hd h.hO h.hJ ?_ ⟨-b / (d.1 - b), ?_, ?_⟩ ⟨b, ?_, ?_⟩
  · simp only; intro e2; apply hd1; linarith
  · simp only; field_simp; ring
  · simp only; rw [e]; field_simp; ring
  · simp only; ring
  · simp only; ring

theorem Setup.proj_K (h : Setup T E) {c : ℝ × ℝ} (hc : c ∈ T) : c.1 ∈ h.K ∧ c.2 ∈ h.K := by
  obtain ⟨c1, c2⟩ := c
  exact ⟨h.proj_x hc, h.y_to_x (h.proj_y hc)⟩

theorem Setup.mem_of_K (h : Setup T E) {a b : ℝ} (ha : a ∈ h.K) (hb : b ∈ h.K) : (a, b) ∈ T := by
  have hB : ((0 : ℝ), b) ∈ T := h.x_to_y hb
  obtain ⟨d, hd, hd1, hd2⟩ := h.vert (C := (a, 0)) ha
  obtain ⟨d', hd', hd2', hd1'⟩ := h.horiz (C := (0, b)) hB
  simp only at hd1 hd2 hd2' hd1'
  refine h.ll (a, 0) d (0, b) d' _ ha hd hB hd' ?_ ⟨b / d.2, ?_, ?_⟩ ⟨a / d'.1, ?_, ?_⟩
  · simp only; rw [hd1, hd2']
    have : (a - a) * (b - b) - (d.2 - 0) * (d'.1 - 0) = -(d.2 * d'.1) := by ring
    rw [this]; exact neg_ne_zero.mpr (mul_ne_zero hd2 hd1')
  · simp only; rw [hd1]; ring
  · simp only; field_simp <;> ring
  · simp only; field_simp <;> ring
  · simp only; rw [hd2']; ring

/-- Square roots: the subfield `K` is closed under square roots. -/
theorem Setup.sqrt_mem (h : Setup T E) {a : ℝ} (ha : a ∈ h.K) : √a ∈ h.K := by
  by_cases ha0 : 0 < a
  swap
  · rw [Real.sqrt_eq_zero_of_nonpos (not_lt.mp ha0)]; exact h.K.zero_mem
  have h1 : (1 + a) ≠ 0 := by positivity
  have hc : (1 - a) / (1 + a) ∈ h.K := h.K.div_mem (h.K.sub_mem h.K.one_mem ha) (h.K.add_mem h.K.one_mem ha)
  have hC : ((0 : ℝ), (1 - a) / (1 + a)) ∈ T := h.x_to_y hc
  obtain ⟨d, hd, hd2, hd1⟩ := h.horiz hC
  simp only at hd1 hd2
  have hsq : √a ^ 2 = a := Real.sq_sqrt ha0.le
  have hx : (2 * √a / (1 + a), (1 - a) / (1 + a)) ∈ T := by
    refine h.gc (0, (1 - a) / (1 + a)) d _ hC hd (fun e => hd1 (by rw [← e])) ⟨2 * √a / (1 + a) / d.1, ?_, ?_⟩ ?_
    · simp only; field_simp <;> ring
    · simp only; rw [hd2]; ring
    · simp only
      field_simp
      linear_combination (4 : ℝ) * hsq
  have := (h.proj_K hx).1
  simp only at this
  have h2 : √a = 2 * √a / (1 + a) * (1 + a) / 2 := by field_simp
  rw [h2]
  exact h.K.div_mem (h.K.mul_mem this (h.K.add_mem h.K.one_mem ha)) (K_two h.K)

/-- **The core of the hard half of the Poncelet-Steiner theorem** (in the frame `O = (0,0)`, `P = (1,0)`): there
is a subfield of `ℝ`, closed under square roots, containing all coordinates of the points of `T`, such that
all of its coordinate points are in `T`. -/
theorem Setup.core (h : Setup T E) : ∃ K : Subfield ℝ, (∀ a ∈ K, √a ∈ K) ∧ (∀ x ∈ T, x.1 ∈ K ∧ x.2 ∈ K) ∧
    ∀ a ∈ K, ∀ b ∈ K, (a, b) ∈ T :=
  ⟨h.K, fun _ ha => h.sqrt_mem ha, fun _ hx => h.proj_K hx, fun _ ha _ hb => h.mem_of_K ha hb⟩

/-! ### The theorem -/

/-- The points constructible by the ruler and the given circle are closed under line-line intersections. -/
theorem rg_llc (O P : ℝ × ℝ) (S : Set (ℝ × ℝ)) : LLC {x | RGConstructible O P S (.point x)} := by
  intro p q p' q' x hp hq hp' hq' hdet hx hx'
  have hpq : p ≠ q := by
    intro e; subst e; apply hdet; ring
  have hpq' : p' ≠ q' := by
    intro e; subst e; apply hdet; ring
  exact RGConstructible.lineLine (RGConstructible.line hp hq hpq) (RGConstructible.line hp' hq' hpq')
    hdet hx hx'

end PS

open PS in
/-- **Poncelet-Steiner theorem** (Petrunin, p. 164), the hard inclusion: a ruler together with one given circle
(centre `O`, passing thru `P`) constructs every point that ruler and compass construct. The initial set `S`
contains `O`, `P` and a point `E` that is off the line `OP`; the hypothesis `hEcirc` (`E` is not on the given
circle) is needed: if `E` lies on the circle, the ruler constructs only `O` and the four vertices of the
rectangle `P E (-P) (-E)`, so the statement fails. In the book's wording (the circle and its centre are
given, arbitrary choices of points allowed) this assumption is absorbed in the free choice of points. -/
@[kb "petrunin2025" "Poncelet-Steiner theorem, p. 164"]
theorem rgConstructible_iff_rcConstructible {O P : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hO : O ∈ S) (hP : P ∈ S)
    {E : ℝ × ℝ} (hE : E ∈ S)
    (hEoff : (P.1 - O.1) * (E.2 - O.2) - (P.2 - O.2) * (E.1 - O.1) ≠ 0)
    (hEcirc : (E.1 - O.1) ^ 2 + (E.2 - O.2) ^ 2 ≠ (P.1 - O.1) ^ 2 + (P.2 - O.2) ^ 2) (x : ℝ × ℝ) :
    RGConstructible O P S (.point x) ↔ RCConstructible S (.point x) := by
  refine ⟨RGConstructible.rc hO hP, fun hx => ?_⟩
  have hOP : O ≠ P := by
    intro e; apply hEoff; rw [e]; ring
  have hN := (ne_coords hOP).ne'
  let TR : Set (ℝ × ℝ) := {x | RGConstructible O P S (.point x)}
  let T : Set (ℝ × ℝ) := {y | unframe O P y ∈ TR}
  have hmemT : ∀ y, y ∈ T ↔ RGConstructible O P S (.point (unframe O P y)) := fun y => Iff.rfl
  have onl : ∀ {p q x : ℝ × ℝ}, OnLine p q x → OnLine (unframe O P p) (unframe O P q) (unframe O P x) := by
    rintro p q x ⟨t, h1, h2⟩
    refine ⟨t, ?_, ?_⟩ <;> simp only [unframe, h1, h2] <;> ring
  have uinj : ∀ {p q : ℝ × ℝ}, p ≠ q → unframe O P p ≠ unframe O P q := by
    intro p q hpq e
    apply hpq
    have := congrArg (frame O P) e
    rwa [frame_unframe hOP, frame_unframe hOP] at this
  have hS : Setup T (frame O P E) := by
    refine ⟨(rg_llc O P S).pull hOP, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p q x hp hq hpq hx hx1
      refine RGConstructible.lineCircle (RGConstructible.line hp hq (uinj hpq)) (onl hx) ?_
      unfold OnCircle
      simp only [unframe]
      linear_combination ((P.1 - O.1) ^ 2 + (P.2 - O.2) ^ 2) * hx1
    · show RGConstructible O P S (.point (unframe O P (0, 0)))
      have : unframe O P (0, 0) = O := by ext <;> simp [unframe]
      rw [this]; exact .init hO
    · show RGConstructible O P S (.point (unframe O P (1, 0)))
      have : unframe O P (1, 0) = P := by ext <;> simp [unframe]
      rw [this]; exact .init hP
    · show RGConstructible O P S (.point (unframe O P (frame O P E)))
      rw [unframe_frame hOP]; exact .init hE
    · rw [frame_snd]; exact div_ne_zero hEoff hN
    · have := frame_dist hOP E O
      have h0 : frame O P O = (0, 0) := by ext <;> simp [frame]
      rw [h0] at this
      simp only [sub_zero] at this
      rw [this]
      intro e
      apply hEcirc
      rw [div_eq_one_iff_eq hN] at e
      linarith
  obtain ⟨K, hsq, hcoords, hmem⟩ := hS.core
  have hsq' : ∀ a ∈ K, √a ∈ K := hsq
  have hS' : ∀ y ∈ frame O P '' S, y.1 ∈ K ∧ y.2 ∈ K := by
    rintro _ ⟨s, hs, rfl⟩
    apply hcoords
    show RGConstructible O P S (.point (unframe O P (frame O P s)))
    rw [unframe_frame hOP]; exact .init hs
  have hxK := RCConstructible.coordsK K hsq' hS' (frame_transfer hOP hx)
  have := hmem _ hxK.1 _ hxK.2
  have h2 : RGConstructible O P S (.point (unframe O P ((frame O P x).1, (frame O P x).2))) := this
  rwa [show ((frame O P x).1, (frame O P x).2) = frame O P x from rfl, unframe_frame hOP] at h2

end UndergradKB.Geometry
