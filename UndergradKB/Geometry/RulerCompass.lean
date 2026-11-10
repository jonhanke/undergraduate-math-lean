import UndergradKB.Geometry.Constructible

/-! # Ruler-and-compass constructions (Petrunin, chapter 19)

The book's informal setting (Section 19C, pp. 158-159): the initial configuration is a finite set of points; a
line is given by two distinct constructed points on it, a circle by its constructed centre and a constructed
point on it; new points are the intersection points of two distinct lines, of a line and a circle, or of two
distinct circles. We model the plane by coordinates `ℝ × ℝ` and define the constructed points, lines and
circles inductively (`RCConstructible`).

Main results:
* `RCConstructible.coords` (Theorem 19.8, the direction used for impossibility proofs): if every initial point
  has constructible coordinates, so has every constructed point;
* geometric impossibility of doubling the cube: from `(0,0)` and `(1,0)` no two constructed points are at
  distance `∛2`;
* geometric impossibility of trisecting the angle `π/3`: from `(0,0)`, `(1,0)` and `(1/2, √3/2)` no constructed
  point `X ≠ (0,0)` makes the angle `π/9` with the positive `x`-axis. -/

namespace UndergradKB.Geometry

open Real

/-- The objects of a ruler-and-compass construction in coordinates: points, the line through `p` and `q`, and
the circle with centre `c` passing thru `d`. -/
inductive RCObj
  | point (x : ℝ × ℝ)
  | line (p q : ℝ × ℝ)
  | circle (c d : ℝ × ℝ)

/-- `x` lies on the line through `p` and `q`. -/
def OnLine (p q x : ℝ × ℝ) : Prop := ∃ t : ℝ, x.1 = p.1 + t * (q.1 - p.1) ∧ x.2 = p.2 + t * (q.2 - p.2)

/-- `x` lies on the circle with centre `c` passing thru `d`. -/
def OnCircle (c d x : ℝ × ℝ) : Prop :=
  (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = (d.1 - c.1) ^ 2 + (d.2 - c.2) ^ 2

/-- Ruler-and-compass constructions from an initial set of points `S` (Petrunin, Sections 19A and 19C).
Two lines are intersected only when they are not parallel (two distinct intersecting lines), two circles only
when their centres differ (two distinct circles), so each step produces finitely many points. -/
inductive RCConstructible (S : Set (ℝ × ℝ)) : RCObj → Prop
  | init {x : ℝ × ℝ} : x ∈ S → RCConstructible S (.point x)
  | line {p q : ℝ × ℝ} : RCConstructible S (.point p) → RCConstructible S (.point q) → p ≠ q →
      RCConstructible S (.line p q)
  | circle {c d : ℝ × ℝ} : RCConstructible S (.point c) → RCConstructible S (.point d) →
      RCConstructible S (.circle c d)
  | lineLine {p q p' q' x : ℝ × ℝ} : RCConstructible S (.line p q) → RCConstructible S (.line p' q') →
      (q.1 - p.1) * (q'.2 - p'.2) - (q.2 - p.2) * (q'.1 - p'.1) ≠ 0 →
      OnLine p q x → OnLine p' q' x → RCConstructible S (.point x)
  | lineCircle {p q c d x : ℝ × ℝ} : RCConstructible S (.line p q) → RCConstructible S (.circle c d) →
      OnLine p q x → OnCircle c d x → RCConstructible S (.point x)
  | circleCircle {c d c' d' x : ℝ × ℝ} : RCConstructible S (.circle c d) →
      RCConstructible S (.circle c' d') → c ≠ c' → OnCircle c d x → OnCircle c' d' x →
      RCConstructible S (.point x)

/-- A point with constructible coordinates. -/
def IsConstructiblePoint (x : ℝ × ℝ) : Prop := IsConstructible x.1 ∧ IsConstructible x.2

/-- Parameter of the intersection of two non-parallel lines with constructible data. -/
theorem isConstructible_lineLine {p1 p2 v1 v2 p1' p2' v1' v2' t s : ℝ}
    (hp1 : IsConstructible p1) (hp2 : IsConstructible p2) (hv1 : IsConstructible v1)
    (hv2 : IsConstructible v2) (hp1' : IsConstructible p1') (hp2' : IsConstructible p2')
    (hv1' : IsConstructible v1') (hv2' : IsConstructible v2') (hdet : v1 * v2' - v2 * v1' ≠ 0)
    (h1 : p1 + t * v1 = p1' + s * v1') (h2 : p2 + t * v2 = p2' + s * v2') : IsConstructible t := by
  have ht : t = ((p1' - p1) * v2' - (p2' - p2) * v1') / (v1 * v2' - v2 * v1') := by
    rw [eq_div_iff hdet]
    linear_combination v2' * h1 - v1' * h2
  rw [ht]
  exact (((hp1'.sub hp1).mul hv2').sub ((hp2'.sub hp2).mul hv1')).div ((hv1.mul hv2').sub (hv2.mul hv1'))

/-- Parameter of an intersection of a line and a circle with constructible data (a quadratic equation). -/
theorem isConstructible_lineCircle {p1 p2 v1 v2 c1 c2 R t : ℝ}
    (hp1 : IsConstructible p1) (hp2 : IsConstructible p2) (hv1 : IsConstructible v1)
    (hv2 : IsConstructible v2) (hc1 : IsConstructible c1) (hc2 : IsConstructible c2)
    (hR : IsConstructible R) (hv : v1 ≠ 0 ∨ v2 ≠ 0)
    (h : (p1 + t * v1 - c1) ^ 2 + (p2 + t * v2 - c2) ^ 2 = R) : IsConstructible t := by
  set a := v1 ^ 2 + v2 ^ 2 with ha
  set b := 2 * (v1 * (p1 - c1) + v2 * (p2 - c2)) with hb
  set e := (p1 - c1) ^ 2 + (p2 - c2) ^ 2 - R with he
  have hapos : 0 < a := by
    rcases hv with hv | hv
    · have := sq_pos_of_ne_zero hv; positivity
    · have := sq_pos_of_ne_zero hv; positivity
  have key : (2 * a * t + b) ^ 2 = b ^ 2 - 4 * a * e := by
    rw [ha, hb, he]; linear_combination (4 * (v1 ^ 2 + v2 ^ 2)) * h
  have hA : IsConstructible a := by
    rw [ha]; simpa [sq] using (hv1.mul hv1).add (hv2.mul hv2)
  have hB : IsConstructible b := by
    rw [hb]
    have := (hv1.mul (hp1.sub hc1)).add (hv2.mul (hp2.sub hc2))
    exact (by exact_mod_cast IsConstructible.intCast 2 : IsConstructible 2).mul this
  have hE : IsConstructible e := by
    rw [he]
    have := ((hp1.sub hc1).mul (hp1.sub hc1)).add ((hp2.sub hc2).mul (hp2.sub hc2))
    simpa [sq] using this.sub hR
  have hD : IsConstructible (Real.sqrt (b ^ 2 - 4 * a * e)) := by
    refine IsConstructible.sqrt ?_
    have := (hB.mul hB).sub (((by exact_mod_cast IsConstructible.intCast 4 :
      IsConstructible 4).mul hA).mul hE)
    simpa [sq] using this
  have hsq : Real.sqrt (b ^ 2 - 4 * a * e) = |2 * a * t + b| := by
    rw [← key, Real.sqrt_sq_eq_abs]
  have h2a : IsConstructible (2 * a) := (by exact_mod_cast IsConstructible.intCast 2 :
    IsConstructible 2).mul hA
  rcases abs_choice (2 * a * t + b) with habs | habs
  · have ht : t = (Real.sqrt (b ^ 2 - 4 * a * e) - b) / (2 * a) := by
      rw [hsq, habs]; field_simp; ring
    rw [ht]; exact (hD.sub hB).div h2a
  · have ht : t = (-Real.sqrt (b ^ 2 - 4 * a * e) - b) / (2 * a) := by
      rw [hsq, habs]; field_simp; ring
    rw [ht]; exact (hD.neg.sub hB).div h2a

/-- A point of the line `p + t v` (constructible data, `v ≠ 0`) on a circle with constructible centre and
constructible squared radius has constructible coordinates. -/
theorem isConstructiblePoint_of_line_circle {p1 p2 v1 v2 c1 c2 R t : ℝ}
    (hp1 : IsConstructible p1) (hp2 : IsConstructible p2) (hv1 : IsConstructible v1)
    (hv2 : IsConstructible v2) (hc1 : IsConstructible c1) (hc2 : IsConstructible c2)
    (hR : IsConstructible R) (hv : v1 ≠ 0 ∨ v2 ≠ 0)
    (h : (p1 + t * v1 - c1) ^ 2 + (p2 + t * v2 - c2) ^ 2 = R) :
    IsConstructiblePoint (p1 + t * v1, p2 + t * v2) := by
  have ht := isConstructible_lineCircle hp1 hp2 hv1 hv2 hc1 hc2 hR hv h
  exact ⟨hp1.add (ht.mul hv1), hp2.add (ht.mul hv2)⟩

/-- **Theorem 19.8** (Petrunin, p. 160), the direction used for impossibility proofs: if every point of the
initial configuration has constructible coordinates, then every point obtained by a ruler-and-compass
construction has constructible coordinates. -/
@[kb "petrunin2025" "Theorem 19.8, p. 160"]
theorem RCConstructible.coords {S : Set (ℝ × ℝ)} (hS : ∀ x ∈ S, IsConstructiblePoint x) {x : ℝ × ℝ}
    (hx : RCConstructible S (.point x)) : IsConstructiblePoint x := by
  -- the invariant of all constructed objects
  let good : RCObj → Prop
    | .point x => IsConstructiblePoint x
    | .line p q => IsConstructiblePoint p ∧ IsConstructiblePoint q ∧ p ≠ q
    | .circle c d => IsConstructiblePoint c ∧ IsConstructiblePoint d
  suffices ∀ o, RCConstructible S o → good o from this _ hx
  intro o ho
  induction ho with
  | init hx => exact hS _ hx
  | line _ _ hpq ihp ihq => exact ⟨ihp, ihq, hpq⟩
  | circle _ _ ihc ihd => exact ⟨ihc, ihd⟩
  | @lineLine p q p' q' x _ _ hdet hx hx' ih ih' =>
    obtain ⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩, -⟩ := ih
    obtain ⟨⟨hp1', hp2'⟩, ⟨hq1', hq2'⟩, -⟩ := ih'
    obtain ⟨t, ht1, ht2⟩ := hx
    obtain ⟨s, hs1, hs2⟩ := hx'
    have htc := isConstructible_lineLine hp1 hp2 (hq1.sub hp1) (hq2.sub hp2) hp1' hp2' (hq1'.sub hp1')
      (hq2'.sub hp2') hdet (ht1.symm.trans hs1) (ht2.symm.trans hs2)
    refine ⟨?_, ?_⟩
    · rw [ht1]; exact hp1.add (htc.mul (hq1.sub hp1))
    · rw [ht2]; exact hp2.add (htc.mul (hq2.sub hp2))
  | @lineCircle p q c d x _ _ hx hxc ih ih' =>
    obtain ⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩, hpq⟩ := ih
    obtain ⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩ := ih'
    obtain ⟨t, ht1, ht2⟩ := hx
    have hv : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hpq (Prod.ext (by linarith [hcon.1]) (by linarith [hcon.2]))
    have hR := (((hd1.sub hc1).mul (hd1.sub hc1)).add ((hd2.sub hc2).mul (hd2.sub hc2)))
    have hcirc : (p.1 + t * (q.1 - p.1) - c.1) ^ 2 + (p.2 + t * (q.2 - p.2) - c.2) ^ 2 =
        (d.1 - c.1) * (d.1 - c.1) + (d.2 - c.2) * (d.2 - c.2) := by
      rw [← ht1, ← ht2, hxc]; ring
    have := isConstructiblePoint_of_line_circle hp1 hp2 (hq1.sub hp1) (hq2.sub hp2) hc1 hc2 hR hv hcirc
    rw [show x = (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2)) from Prod.ext ht1 ht2]
    exact this
  | @circleCircle c d c' d' x _ _ hcc hx hx' ih ih' =>
    obtain ⟨⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩ := ih
    obtain ⟨⟨hc1', hc2'⟩, ⟨hd1', hd2'⟩⟩ := ih'
    -- reduce to a line and a circle: the radical axis, written as `c + λ w + t w⊥`
    set w1 := c'.1 - c.1
    set w2 := c'.2 - c.2
    set R := (d.1 - c.1) * (d.1 - c.1) + (d.2 - c.2) * (d.2 - c.2) with hRdef
    set R' := (d'.1 - c'.1) * (d'.1 - c'.1) + (d'.2 - c'.2) * (d'.2 - c'.2) with hR'def
    have hw : w1 ≠ 0 ∨ w2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hcc (Prod.ext (by linarith [hcon.1]) (by linarith [hcon.2]))
    have hW : 0 < w1 ^ 2 + w2 ^ 2 := by
      rcases hw with hw | hw
      · have := sq_pos_of_ne_zero hw; positivity
      · have := sq_pos_of_ne_zero hw; positivity
    have hw1 : IsConstructible w1 := hc1'.sub hc1
    have hw2 : IsConstructible w2 := hc2'.sub hc2
    have hR : IsConstructible R := ((hd1.sub hc1).mul (hd1.sub hc1)).add ((hd2.sub hc2).mul (hd2.sub hc2))
    have hR' : IsConstructible R' :=
      ((hd1'.sub hc1').mul (hd1'.sub hc1')).add ((hd2'.sub hc2').mul (hd2'.sub hc2'))
    have hWc : IsConstructible (w1 * w1 + w2 * w2) := (hw1.mul hw1).add (hw2.mul hw2)
    set lam := (R - R' + (w1 * w1 + w2 * w2)) / (2 * (w1 * w1 + w2 * w2)) with hlam
    have hlamc : IsConstructible lam :=
      ((hR.sub hR').add hWc).div ((by exact_mod_cast IsConstructible.intCast 2 :
        IsConstructible 2).mul hWc)
    set t := ((x.1 - c.1) * (-w2) + (x.2 - c.2) * w1) / (w1 ^ 2 + w2 ^ 2) with ht
    have hx1 : OnCircle c d x := hx
    have hx2 : OnCircle c' d' x := hx'
    unfold OnCircle at hx1 hx2
    -- the component of `x - c` along `w`
    have hdot : (x.1 - c.1) * w1 + (x.2 - c.2) * w2 = (R - R' + (w1 * w1 + w2 * w2)) / 2 := by
      rw [hRdef, hR'def]
      have e1 : x.1 - c'.1 = (x.1 - c.1) - w1 := by ring
      have e2 : x.2 - c'.2 = (x.2 - c.2) - w2 := by ring
      rw [e1, e2] at hx2
      linear_combination (1 / 2 : ℝ) * hx1 - (1 / 2 : ℝ) * hx2
    have hdecomp1 : x.1 = (c.1 + lam * w1) + t * (-w2) := by
      rw [hlam, ht]; field_simp
      linear_combination (w1 * 2) * hdot
    have hdecomp2 : x.2 = (c.2 + lam * w2) + t * w1 := by
      rw [hlam, ht]; field_simp
      linear_combination (w2 * 2) * hdot
    have hcirc : ((c.1 + lam * w1) + t * (-w2) - c.1) ^ 2 + ((c.2 + lam * w2) + t * w1 - c.2) ^ 2 = R := by
      rw [← hdecomp1, ← hdecomp2, hx1, hRdef]; ring
    have hv : -w2 ≠ 0 ∨ w1 ≠ 0 := by
      rcases hw with hw | hw
      · exact Or.inr hw
      · exact Or.inl (neg_ne_zero.mpr hw)
    have := isConstructiblePoint_of_line_circle (hc1.add (hlamc.mul hw1)) (hc2.add (hlamc.mul hw2))
      hw2.neg hw1 hc1 hc2 hR hv hcirc
    rw [show x = ((c.1 + lam * w1) + t * (-w2), (c.2 + lam * w2) + t * w1) from
      Prod.ext hdecomp1 hdecomp2]
    exact this

theorem isConstructiblePoint_zero : IsConstructiblePoint (0, 0) :=
  ⟨by exact_mod_cast IsConstructible.intCast 0, by exact_mod_cast IsConstructible.intCast 0⟩

theorem isConstructiblePoint_one_zero : IsConstructiblePoint (1, 0) :=
  ⟨by exact_mod_cast IsConstructible.intCast 1, by exact_mod_cast IsConstructible.intCast 0⟩

/-- The Euclidean length of a segment with constructible endpoints is constructible. -/
theorem isConstructible_length {X Y : ℝ × ℝ} (hX : IsConstructiblePoint X) (hY : IsConstructiblePoint Y) :
    IsConstructible (Real.sqrt ((X.1 - Y.1) ^ 2 + (X.2 - Y.2) ^ 2)) := by
  have := ((hX.1.sub hY.1).mul (hX.1.sub hY.1)).add ((hX.2.sub hY.2).mul (hX.2.sub hY.2))
  exact IsConstructible.sqrt (by simpa [sq] using this)

/-- **Doubling the cube is impossible** (Petrunin, Section 19B, p. 157-158): starting from the segment between
`(0,0)` and `(1,0)` (of length 1), no ruler-and-compass construction produces two points at distance `∛2`. -/
@[kb "petrunin2025" "Section 19B, doubling the cube, pp. 157-158"]
theorem not_rcConstructible_cube_doubling {X Y : ℝ × ℝ}
    (hX : RCConstructible {(0, 0), (1, 0)} (.point X)) (hY : RCConstructible {(0, 0), (1, 0)} (.point Y)) :
    Real.sqrt ((X.1 - Y.1) ^ 2 + (X.2 - Y.2) ^ 2) ^ 3 ≠ 2 := by
  have hS : ∀ x ∈ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), IsConstructiblePoint x := by
    rintro x (rfl | rfl)
    exacts [isConstructiblePoint_zero, isConstructiblePoint_one_zero]
  intro h
  exact not_isConstructible_cbrt_two h (isConstructible_length (hX.coords hS) (hY.coords hS))

/-- **Trisecting the angle `π/3` is impossible** (Petrunin, Section 19B, p. 158): starting from `O = (0,0)`,
`A = (1,0)` and `B = (1/2, √3/2)` (so that `∠AOB = π/3`), no ruler-and-compass construction produces a point
`X ≠ O` on the half-line from `O` making the angle `π/9` with `[OA)`. -/
@[kb "petrunin2025" "Section 19B, angle trisection, p. 158"]
theorem not_rcConstructible_trisection {X : ℝ × ℝ}
    (hX : RCConstructible {(0, 0), (1, 0), (1 / 2, Real.sqrt 3 / 2)} (.point X)) {r : ℝ} (hr : 0 < r) :
    X ≠ (r * Real.cos (π / 9), r * Real.sin (π / 9)) := by
  have hS : ∀ x ∈ ({(0, 0), (1, 0), (1 / 2, Real.sqrt 3 / 2)} : Set (ℝ × ℝ)), IsConstructiblePoint x := by
    rintro x (rfl | rfl | rfl)
    · exact isConstructiblePoint_zero
    · exact isConstructiblePoint_one_zero
    · have h2 : IsConstructible 2 := by exact_mod_cast IsConstructible.intCast 2
      have h3 : IsConstructible 3 := by exact_mod_cast IsConstructible.intCast 3
      refine ⟨?_, (h3.sqrt).div h2⟩
      have := (IsConstructible.intCast 1).div h2
      simpa using this
  rintro rfl
  have hc := hX.coords hS
  have hlen := isConstructible_length hc isConstructiblePoint_zero
  have hr' : Real.sqrt ((r * Real.cos (π / 9) - 0) ^ 2 + (r * Real.sin (π / 9) - 0) ^ 2) = r := by
    rw [show (r * Real.cos (π / 9) - 0) ^ 2 + (r * Real.sin (π / 9) - 0) ^ 2 =
        r ^ 2 * (Real.sin (π / 9) ^ 2 + Real.cos (π / 9) ^ 2) by ring, Real.sin_sq_add_cos_sq, mul_one,
      Real.sqrt_sq hr.le]
  simp only at hlen
  rw [hr'] at hlen
  apply not_isConstructible_cos_pi_div_nine
  have := hc.1.div hlen
  simp only at this
  rwa [mul_div_cancel_left₀ _ hr.ne'] at this

/-- **The regular 9-gon cannot be constructed** (Petrunin, Gauss-Wantzel theorem 19.6, the example `n = 9`,
p. 158): starting from the centre `O = (0,0)` and a vertex `A₁ = (1,0)`, no ruler-and-compass construction
produces the next vertex `A₂ = (cos (2π/9), sin (2π/9))` (nor its mirror image). -/
@[kb "petrunin2025" "Theorem 19.6 (case n = 9), p. 158"]
theorem not_rcConstructible_nonagon {X : ℝ × ℝ} (hX : RCConstructible {(0, 0), (1, 0)} (.point X)) :
    X.1 ≠ Real.cos (2 * π / 9) := by
  have hS : ∀ x ∈ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)), IsConstructiblePoint x := by
    rintro x (rfl | rfl)
    exacts [isConstructiblePoint_zero, isConstructiblePoint_one_zero]
  intro h
  exact not_isConstructible_cos_two_pi_div_nine (h ▸ (hX.coords hS).1)

end UndergradKB.Geometry
