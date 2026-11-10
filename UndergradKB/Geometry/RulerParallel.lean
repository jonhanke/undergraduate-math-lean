import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import UndergradKB.Common.Attr
import UndergradKB.Geometry.RulerCompass

/-! # Constructions with a ruler and a parallel tool (Petrunin, Section 14B)

We reuse the objects `RCObj` and the incidence `OnLine` of `RulerCompass.lean`. The constructions with a ruler
and a parallel tool (the tool draws a line thru a given point parallel to a given line) from an initial set `S`
of points are the inductive family `RPConstructible S`: lines thru two constructed points, the parallel line
thru a constructed point to a constructed line, and the intersection point of two non-parallel constructed
lines.

* `RPConstructible.fixed`, `not_rp_perpendicular` (Exercise 14.9): an affine map (in particular the shear
  `(x, y) ↦ (x + y, y)`) that fixes all initial points fixes every constructed point; hence from points on the
  `x`-axis no point off the axis and no line perpendicular to the axis can be constructed.
* `rp_add_sub_mul_div` (Exercise 14.7): from `0`, `1`, `a`, `b` on the axis and one auxiliary point off the
  axis one constructs `a + b`, `a - b`, `a b`, `a / b`.
-/

namespace UndergradKB.Geometry

/-- Constructions with a ruler and a parallel tool (Petrunin, Section 14B). -/
inductive RPConstructible (S : Set (ℝ × ℝ)) : RCObj → Prop
  | init {x : ℝ × ℝ} : x ∈ S → RPConstructible S (.point x)
  | line {p q : ℝ × ℝ} : RPConstructible S (.point p) → RPConstructible S (.point q) → p ≠ q →
      RPConstructible S (.line p q)
  | parallel {c p q : ℝ × ℝ} : RPConstructible S (.point c) → RPConstructible S (.line p q) → p ≠ q →
      RPConstructible S (.line c (c + (q - p)))
  | lineLine {p q p' q' x : ℝ × ℝ} : RPConstructible S (.line p q) → RPConstructible S (.line p' q') →
      (q.1 - p.1) * (q'.2 - p'.2) - (q.2 - p.2) * (q'.1 - p'.1) ≠ 0 →
      OnLine p q x → OnLine p' q' x → RPConstructible S (.point x)

/-- An affine map fixing the point `p` and `q` fixes every point of the line `pq`. -/
theorem affine_fixed_on_line (f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ)) {p q x : ℝ × ℝ} (hp : f p = p) (hq : f q = q)
    (hx : OnLine p q x) : f x = x := by
  obtain ⟨t, h1, h2⟩ := hx
  have hx : x = t • (q -ᵥ p) +ᵥ p := Prod.ext (by simp [h1, add_comm]) (by simp [h2, add_comm])
  have hl : f.linear (q -ᵥ p) = q -ᵥ p := by rw [f.linear_apply_vsub, hp, hq]
  rw [hx, f.map_vadd, map_smul, hl, hp]

/-- An affine map fixing the vector `q - p` and `c` fixes `c + (q - p)`. -/
theorem affine_fixed_add (f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ)) {c p q : ℝ × ℝ} (hc : f c = c) (hp : f p = p)
    (hq : f q = q) : f (c + (q - p)) = c + (q - p) := by
  have hl : f.linear (q - p) = q - p := by
    rw [← vsub_eq_sub, f.linear_apply_vsub, hp, hq]
  have := f.map_vadd c (q - p)
  rw [vadd_eq_add, add_comm] at this
  rw [this, hl, hc, vadd_eq_add, add_comm]

/-- **Constructions commute with affine maps** (Petrunin, Exercise 14.1 and the discussion in Section 14B):
if an affine map `f` of `ℝ²` fixes every initial point, it fixes every constructed point, and both defining
points of every constructed line. (A line fixed in this sense is fixed pointwise.) -/
theorem RPConstructible.fixed {S : Set (ℝ × ℝ)} (f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ)) (hS : ∀ s ∈ S, f s = s)
    {o : RCObj} (ho : RPConstructible S o) :
    (match o with
      | .point x => f x = x
      | .line p q => f p = p ∧ f q = q ∧ p ≠ q
      | .circle _ _ => True) := by
  induction ho with
  | init hx => exact hS _ hx
  | line _ _ hpq ihp ihq => exact ⟨ihp, ihq, hpq⟩
  | @parallel c p q _ _ hpq ihc ihl =>
    obtain ⟨hp, hq, -⟩ := ihl
    refine ⟨ihc, affine_fixed_add f ihc hp hq, ?_⟩
    intro h
    have : q - p = 0 := by simpa using h.symm
    exact hpq (sub_eq_zero.mp this).symm
  | lineLine _ _ _ hx hx' ih ih' =>
    obtain ⟨hp, hq, -⟩ := ih
    exact affine_fixed_on_line f hp hq hx

/-- The shear `(x, y) ↦ (x + y, y)` as an affine map (Petrunin, Exercise 14.3(a) with `k = 1`). -/
def shearMap : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  ((LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ)).toAffineMap

theorem shearMap_apply (p : ℝ × ℝ) : shearMap p = (p.1 + p.2, p.2) := rfl

theorem shearMap_fixed_iff (p : ℝ × ℝ) : shearMap p = p ↔ p.2 = 0 := by
  rw [shearMap_apply]
  constructor
  · intro h
    have := congrArg Prod.fst h
    simp at this
    exact this
  · intro h
    ext <;> simp [h]

/-- **Constructions from points of the `x`-axis stay on the axis** (Petrunin, Exercise 14.9): the shear
`(x, y) ↦ (x + y, y)` fixes every point of the axis, hence (by `RPConstructible.fixed`) every constructed point;
the fixed points of the shear are exactly the points of the axis. So a ruler-and-parallel-tool construction
from points of the axis constructs only points of the axis, and only the lines `pq` with `p`, `q` on the axis
and `p ≠ q`. -/
theorem rp_constructible_on_axis {S : Set (ℝ × ℝ)} (hS : ∀ s ∈ S, s.2 = 0) {o : RCObj}
    (ho : RPConstructible S o) :
    (match o with
      | .point x => x.2 = 0
      | .line p q => p.2 = 0 ∧ q.2 = 0 ∧ p ≠ q
      | .circle _ _ => True) := by
  have h := RPConstructible.fixed shearMap (fun s hs => (shearMap_fixed_iff s).mpr (hS s hs)) ho
  cases o with
  | point x => exact (shearMap_fixed_iff x).mp h
  | line p q => exact ⟨(shearMap_fixed_iff p).mp h.1, (shearMap_fixed_iff q).mp h.2.1, h.2.2⟩
  | circle c d => trivial

/-- **One cannot construct a perpendicular with a ruler and a parallel tool** (Petrunin, Exercise 14.9, p. 116).
Let `S` be a set of initial points on the `x`-axis (for instance `(0,0)` and `(1,0)`). Then every constructible
line `pq` lies on the axis (so is not perpendicular to it: `p.1 ≠ q.1`), and no point off the axis, e.g. `(0, t)`
with `t ≠ 0`, is constructible; in particular the perpendicular to the axis at `(0,0)` is not constructible. -/
@[kb "petrunin2025" "Exercise 14.9, p. 116"]
theorem not_rp_perpendicular {S : Set (ℝ × ℝ)} (hS : ∀ s ∈ S, s.2 = 0) :
    (∀ p q : ℝ × ℝ, RPConstructible S (.line p q) → p.2 = 0 ∧ q.2 = 0 ∧ p.1 ≠ q.1) ∧
    (∀ t : ℝ, t ≠ 0 → ¬ RPConstructible S (.point (0, t))) ∧
    (∀ t : ℝ, t ≠ 0 → ¬ RPConstructible S (.line (0, 0) (0, t))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q h
    obtain ⟨hp, hq, hpq⟩ := rp_constructible_on_axis hS h
    refine ⟨hp, hq, fun h1 => hpq (Prod.ext h1 (by rw [hp, hq]))⟩
  · intro t ht h
    exact ht (rp_constructible_on_axis hS h)
  · intro t ht h
    exact ht (rp_constructible_on_axis hS h).2.1

/-! ### Exercise 14.7: arithmetic with a ruler and a parallel tool -/

section Arithmetic

variable {S : Set (ℝ × ℝ)}

/-- The basic step of the constructions below: the intersection of the line thru `c₁` parallel to `p₁q₁` and
the line thru `c₂` parallel to `p₂q₂` (which are not parallel to each other) is constructible. -/
theorem RPConstructible.inter_par {c₁ p₁ q₁ c₂ p₂ q₂ x : ℝ × ℝ}
    (hc₁ : RPConstructible S (.point c₁)) (hp₁ : RPConstructible S (.point p₁))
    (hq₁ : RPConstructible S (.point q₁)) (hc₂ : RPConstructible S (.point c₂))
    (hp₂ : RPConstructible S (.point p₂)) (hq₂ : RPConstructible S (.point q₂)) (h₁ : p₁ ≠ q₁)
    (h₂ : p₂ ≠ q₂)
    (hdet : (q₁.1 - p₁.1) * (q₂.2 - p₂.2) - (q₁.2 - p₁.2) * (q₂.1 - p₂.1) ≠ 0)
    (hx₁ : ∃ t : ℝ, x.1 = c₁.1 + t * (q₁.1 - p₁.1) ∧ x.2 = c₁.2 + t * (q₁.2 - p₁.2))
    (hx₂ : ∃ t : ℝ, x.1 = c₂.1 + t * (q₂.1 - p₂.1) ∧ x.2 = c₂.2 + t * (q₂.2 - p₂.2)) :
    RPConstructible S (.point x) := by
  have L₁ := RPConstructible.parallel hc₁ (RPConstructible.line hp₁ hq₁ h₁) h₁
  have L₂ := RPConstructible.parallel hc₂ (RPConstructible.line hp₂ hq₂ h₂) h₂
  refine RPConstructible.lineLine L₁ L₂ ?_ ?_ ?_
  · simpa using hdet
  · obtain ⟨t, h1, h2⟩ := hx₁
    exact ⟨t, by simpa using h1, by simpa using h2⟩
  · obtain ⟨t, h1, h2⟩ := hx₂
    exact ⟨t, by simpa using h1, by simpa using h2⟩

/-- **Arithmetic with a ruler and a parallel tool** (Petrunin, Exercise 14.7, p. 115). Suppose the points
`(0,0)`, `(1,0)`, `(a,0)`, `(b,0)` and one auxiliary point `e` off the `x`-axis (a free choice of the
construction; without it nothing off the axis, hence nothing new, can be constructed by Exercise 14.9) are
given. Then `(a + b, 0)`, `(a - b, 0)`, `(a b, 0)` and, for `b ≠ 0`, `(a / b, 0)` are constructible. -/
@[kb "petrunin2025" "Exercise 14.7, p. 115"]
theorem rp_add_sub_mul_div {a b : ℝ} {e : ℝ × ℝ} (he : e.2 ≠ 0) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (h1 : ((1 : ℝ), (0 : ℝ)) ∈ S) (ha : (a, (0 : ℝ)) ∈ S) (hb : (b, (0 : ℝ)) ∈ S) (hE : e ∈ S) :
    RPConstructible S (.point (a + b, 0)) ∧ RPConstructible S (.point (a - b, 0)) ∧
      RPConstructible S (.point (a * b, 0)) ∧
      (b ≠ 0 → RPConstructible S (.point (a / b, 0))) := by
  have hO : RPConstructible S (.point ((0 : ℝ), (0 : ℝ))) := .init h0
  have hI : RPConstructible S (.point ((1 : ℝ), (0 : ℝ))) := .init h1
  have hA : RPConstructible S (.point (a, (0 : ℝ))) := .init ha
  have hB : RPConstructible S (.point (b, (0 : ℝ))) := .init hb
  have hEp : RPConstructible S (.point e) := .init hE
  obtain ⟨e1, e2⟩ := e
  simp only at he
  have hOI : ((0 : ℝ), (0 : ℝ)) ≠ ((1 : ℝ), (0 : ℝ)) := by simp
  have hOE : ((0 : ℝ), (0 : ℝ)) ≠ (e1, e2) := by intro h; exact he (congrArg Prod.snd h).symm
  have hIE : ((1 : ℝ), (0 : ℝ)) ≠ (e1, e2) := by simp [he.symm]
  have hBE : (b, (0 : ℝ)) ≠ (e1, e2) := by simp [he.symm]
  have hAE : (a, (0 : ℝ)) ≠ (e1, e2) := by simp [he.symm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- a + b
    have hF : RPConstructible S (.point (a + e1, e2)) :=
      RPConstructible.inter_par hEp hO hI hA hO hEp hOI hOE (by simpa using he)
        ⟨a, by simp [add_comm], by simp⟩ ⟨1, by simp, by simp⟩
    exact RPConstructible.inter_par hO hO hI hF hB hEp hOI hBE (by simpa using he)
      ⟨a + b, by simp, by simp⟩ ⟨-1, by simp, by simp⟩
  · -- a - b
    have hG : RPConstructible S (.point (e1 + b, e2)) :=
      RPConstructible.inter_par hEp hO hI hB hO hEp hOI hOE (by simpa using he)
        ⟨b, by simp [add_comm], by simp⟩ ⟨1, by simp [add_comm], by simp⟩
    have hGA : ((e1 + b, e2) : ℝ × ℝ) ≠ (a, 0) := by simp [he]
    exact RPConstructible.inter_par hO hO hI hEp hG hA hOI hGA.symm.symm (by simpa using he)
      ⟨a - b, by simp, by simp⟩ ⟨1, by simp; ring, by simp⟩
  · -- a * b
    have hU : RPConstructible S (.point (b * e1, b * e2)) :=
      RPConstructible.inter_par hO hO hEp hB hI hEp hOE hIE (by simp; ring_nf; simpa using he)
        ⟨b, by simp, by simp⟩ ⟨b, by simp; ring, by simp⟩
    exact RPConstructible.inter_par hO hO hI hU hEp hA hOI hAE.symm (by simpa using he)
      ⟨a * b, by simp, by simp⟩ ⟨b, by simp; ring, by simp⟩
  · intro hb0
    have hV : RPConstructible S (.point (a / b * e1, a / b * e2)) :=
      RPConstructible.inter_par hO hO hEp hA hB hEp hOE hBE (by simp; ring_nf; simpa [hb0] using he)
        ⟨a / b, by simp, by simp⟩ ⟨a / b, by simp; field_simp; ring, by simp⟩
    exact RPConstructible.inter_par hO hO hI hV hEp hI hOI hIE.symm (by simpa using he)
      ⟨a / b, by simp, by simp⟩ ⟨a / b, by simp; ring, by simp⟩

end Arithmetic

end UndergradKB.Geometry
