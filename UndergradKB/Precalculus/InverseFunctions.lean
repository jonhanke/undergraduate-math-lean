import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Function
import UndergradKB.Common.Attr

/-!
# Inverse functions (Stitz–Zeager, Chapter 5)

`f` has domain `D` and range `R`; `g` has domain `R` and range `D`. Graphs are
`Set.graphOn f D`.
-/

namespace UndergradKB.Precalculus

open UndergradKB

/-- `g` is the inverse of `f`, where `f` is considered on the domain `D` and `g` on the domain `R`:
`f` sends `D` into `R` and `g` undoes it, and `g` sends `R` into `D` and `f` undoes it. -/
def InverseOn (f g : ℝ → ℝ) (D R : Set ℝ) : Prop :=
  (∀ x ∈ D, f x ∈ R ∧ g (f x) = x) ∧ (∀ y ∈ R, g y ∈ D ∧ f (g y) = y)

/-- Properties of inverse functions: ranges and domains swap, `f a = b ↔ g b = a`, and
`(a, b)` is on the graph of `f` iff `(b, a)` is on the graph of `g` (PC-083). -/
@[kb "stitzzeager2013" "Theorem 5.2, p. 391"]
theorem inverse_properties {f g : ℝ → ℝ} {D R : Set ℝ} (h : InverseOn f g D R) :
    f '' D = R ∧ g '' R = D ∧
    (∀ a ∈ D, ∀ b ∈ R, f a = b ↔ g b = a) ∧
    (∀ a b : ℝ, (a, b) ∈ Set.graphOn f D ↔ (b, a) ∈ Set.graphOn g R) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (h1 x hx).1
    · intro hy; exact ⟨g y, (h2 y hy).1, (h2 y hy).2⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (h2 y hy).1
    · intro hx; exact ⟨f x, (h1 x hx).1, (h1 x hx).2⟩
  · intro a ha b hb
    constructor
    · rintro rfl; exact (h1 a ha).2
    · rintro rfl; exact (h2 b hb).2
  · intro a b
    simp only [Set.mem_graphOn]
    constructor
    · rintro ⟨ha, rfl⟩; exact ⟨(h1 a ha).1, (h1 a ha).2⟩
    · rintro ⟨hb, rfl⟩; exact ⟨(h2 b hb).1, (h2 b hb).2⟩

/-- Uniqueness of the inverse, and the graph of the inverse is the reflection of the graph of `f`
across the line `y = x` (the image under swapping coordinates) (PC-084). -/
@[kb "stitzzeager2013" "Theorem 5.3, p. 392"]
theorem inverse_unique_and_graph_reflection {f g g' : ℝ → ℝ} {D R : Set ℝ}
    (h : InverseOn f g D R) (h' : InverseOn f g' D R) :
    Set.EqOn g g' R ∧ Set.graphOn g R = Prod.swap '' Set.graphOn f D := by
  constructor
  · intro y hy
    obtain ⟨hgD, hgf⟩ := h.2 y hy
    obtain ⟨hgD', hgf'⟩ := h'.2 y hy
    calc g y = g' (f (g y)) := ((h'.1 _ hgD).2).symm
      _ = g' y := by rw [hgf]
  · ext ⟨b, a⟩
    have := (inverse_properties h).2.2.2 a b
    simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · intro hm
      exact ⟨a, b, this.2 hm, rfl, rfl⟩
    · rintro ⟨a', b', hm, rfl, rfl⟩
      exact this.1 hm

/-- Horizontal Line Test: `f` is one-to-one on `D` iff each horizontal line meets the graph of `f`
in at most one point (PC-086). -/
@[kb "stitzzeager2013" "Theorem 5.4, p. 393"]
theorem horizontal_line_test (f : ℝ → ℝ) (D : Set ℝ) :
    Set.InjOn f D ↔ ∀ b : ℝ, (Set.graphOn f D ∩ {p | p.2 = b}).Subsingleton := by
  constructor
  · intro hinj b p ⟨hp, hpb⟩ q ⟨hq, hqb⟩
    rw [Set.mem_graphOn] at hp hq
    have hpb' : p.2 = b := hpb
    have hqb' : q.2 = b := hqb
    have : p.1 = q.1 := hinj hp.1 hq.1 (by rw [hp.2, hq.2, hpb', hqb'])
    ext
    · exact this
    · rw [hpb', hqb']
  · intro h x hx y hy hxy
    have := h (f y) (show ((x, f x) : ℝ × ℝ) ∈ Set.graphOn f D ∩ {p | p.2 = f y} from
      ⟨Set.mem_graphOn.2 ⟨hx, rfl⟩, hxy⟩)
      (show ((y, f y) : ℝ × ℝ) ∈ Set.graphOn f D ∩ {p | p.2 = f y} from
      ⟨Set.mem_graphOn.2 ⟨hy, rfl⟩, rfl⟩)
    exact congrArg Prod.fst this

/-- Equivalent conditions for invertibility: `f` has an inverse (from its range `f '' D` back to
`D`) iff it is one-to-one on `D` iff its graph passes the Horizontal Line Test (PC-087). -/
@[kb "stitzzeager2013" "Theorem 5.5, p. 394"]
theorem invertible_iff_injective (f : ℝ → ℝ) (D : Set ℝ) :
    ((∃ g : ℝ → ℝ, InverseOn f g D (f '' D)) ↔ Set.InjOn f D) ∧
    (Set.InjOn f D ↔ ∀ b : ℝ, (Set.graphOn f D ∩ {p | p.2 = b}).Subsingleton) := by
  refine ⟨⟨?_, ?_⟩, horizontal_line_test f D⟩
  · rintro ⟨g, h1, h2⟩ x hx y hy hxy
    calc x = g (f x) := ((h1 x hx).2).symm
      _ = g (f y) := by rw [hxy]
      _ = y := (h1 y hy).2
  · intro hinj
    refine ⟨Function.invFunOn f D, fun x hx => ⟨⟨x, hx, rfl⟩, hinj.leftInvOn_invFunOn hx⟩,
      fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩⟩

end UndergradKB.Precalculus
