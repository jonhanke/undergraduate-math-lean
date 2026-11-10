import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
import UndergradKB.Geometry.RulerParallel
import UndergradKB.Common.Attr

/-! # Classical problems and one impossibility (Petrunin, Exercise 14.9, Section 19 A)

* Exercise 14.9, general form: from initial points lying on an arbitrary line `ℓ = (ab)` of `ℝ²`
  one cannot construct, with ruler and parallel tool, any line perpendicular to `ℓ` (nor any point
  off `ℓ`). Wave 1 had the case `ℓ` = the `x`-axis (`not_rp_perpendicular`).
* Problem 19.1 (Brahmagupta), existence: a convex quadrangle inscribed in a circle with prescribed
  sides.
* Problem 19.2 (Apollonius), existence: a circle tangent to three pairwise exterior circles. -/

namespace UndergradKB.Geometry

/-! ### Exercise 14.9, general line -/

section Perp

/-- The shear along the line `(ab)`: `x ↦ x + det(b - a, x - a) · (b - a)`. -/
noncomputable def shearAlong (a b : ℝ × ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) where
  toFun x := x + ((b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)) • (b - a)
  linear :=
    { toFun := fun v => v + ((b.1 - a.1) * v.2 - (b.2 - a.2) * v.1) • (b - a)
      map_add' := fun v w => by ext <;> simp <;> ring
      map_smul' := fun r v => by ext <;> simp <;> ring }
  map_vadd' p v := by ext <;> simp <;> ring

theorem shearAlong_apply (a b x : ℝ × ℝ) :
    shearAlong a b x = x + ((b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)) • (b - a) := rfl

theorem onLine_iff_det {a b x : ℝ × ℝ} (hab : a ≠ b) :
    OnLine a b x ↔ (b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1) = 0 := by
  constructor
  · rintro ⟨t, h1, h2⟩
    rw [h1, h2]; ring
  · intro h
    by_cases h1 : b.1 - a.1 = 0
    · have h2 : b.2 - a.2 ≠ 0 := by
        intro h2; apply hab; ext <;> linarith
      refine ⟨(x.2 - a.2) / (b.2 - a.2), ?_, ?_⟩
      · rw [h1] at h
        have : x.1 - a.1 = 0 := by
          rcases mul_eq_zero.mp (by linarith : (b.2 - a.2) * (x.1 - a.1) = 0) with h3 | h3
          · exact absurd h3 h2
          · exact h3
        rw [h1]; linarith
      · field_simp; ring
    · refine ⟨(x.1 - a.1) / (b.1 - a.1), ?_, ?_⟩
      · field_simp; ring
      · field_simp; linarith

theorem shearAlong_fixed_iff {a b : ℝ × ℝ} (hab : a ≠ b) (x : ℝ × ℝ) :
    shearAlong a b x = x ↔ OnLine a b x := by
  rw [onLine_iff_det hab, shearAlong_apply]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul] at h1 h2
    by_contra hne
    apply hab
    have e1 : (b.1 - a.1) * ((b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)) = 0 := by
      linarith
    have e2 : (b.2 - a.2) * ((b.1 - a.1) * (x.2 - a.2) - (b.2 - a.2) * (x.1 - a.1)) = 0 := by
      linarith
    have f1 := (mul_eq_zero.mp e1).resolve_right hne
    have f2 := (mul_eq_zero.mp e2).resolve_right hne
    ext <;> linarith
  · intro h
    rw [h, zero_smul, add_zero]

/-- **Exercise 14.9, general form** (Petrunin, p. 116): let the given line be `ℓ = (ab)` with
`a ≠ b`, and let `S` be any set of initial points on `ℓ` (a ruler-and-parallel-tool construction
starting from the data "the line `ℓ`" can only use points of `ℓ`). Then every constructible
line `pq` coincides with `ℓ` (both `p`, `q` lie on `ℓ`), so it is not perpendicular to `ℓ`
(its direction `q - p` has nonzero inner product with `b - a`), and no point off `ℓ` is
constructible; in particular there is no constructible perpendicular to `ℓ`. The hypothesis
cannot be weakened to initial points off `ℓ` (then a perpendicular can be available). -/
@[kb "petrunin2025" "Exercise 14.9, p. 116"]
theorem not_rp_perpendicular_general {a b : ℝ × ℝ} (hab : a ≠ b) {S : Set (ℝ × ℝ)}
    (hS : ∀ s ∈ S, OnLine a b s) :
    (∀ p q : ℝ × ℝ, RPConstructible S (.line p q) →
      OnLine a b p ∧ OnLine a b q ∧ p ≠ q ∧ (q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2) ≠ 0) ∧
    (∀ x : ℝ × ℝ, ¬ OnLine a b x → ¬ RPConstructible S (.point x)) := by
  have hfix := fun {o : RCObj} (ho : RPConstructible S o) =>
    RPConstructible.fixed (shearAlong a b) (fun s hs => (shearAlong_fixed_iff hab s).mpr (hS s hs)) ho
  refine ⟨fun p q h => ?_, fun x hx h => hx ((shearAlong_fixed_iff hab x).mp (hfix h))⟩
  obtain ⟨hp, hq, hpq⟩ := hfix h
  have hp' := (shearAlong_fixed_iff hab p).mp hp
  have hq' := (shearAlong_fixed_iff hab q).mp hq
  refine ⟨hp', hq', hpq, ?_⟩
  obtain ⟨t, h1, h2⟩ := hp'
  obtain ⟨s, k1, k2⟩ := hq'
  have hd : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
    intro h0
    apply hab
    have e1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have e2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    ext <;> linarith
  have hts : s - t ≠ 0 := by
    intro h0
    apply hpq
    have : s = t := by linarith
    subst this
    ext <;> linarith
  have : (q.1 - p.1) * (b.1 - a.1) + (q.2 - p.2) * (b.2 - a.2) =
      (s - t) * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    rw [k1, k2, h1, h2]; ring
  rw [this]
  exact mul_ne_zero hts hd

end Perp

/-! ### Problem 19.1 (Brahmagupta): existence of an inscribed quadrangle with given sides -/

section Brahmagupta

open EuclideanGeometry

theorem dist2 (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : EuclideanSpace ℝ (Fin 2)) !₂[x2, y2] =
      √((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem pos_of_mul_pos_aux {u v : ℝ} (h : 0 < u * v) (hv : 0 < v) : 0 < u := by
  by_contra hu
  push_neg at hu
  nlinarith [mul_nonneg (neg_nonneg.mpr hu) hv.le]

/-- Algebraic core: the diagonal `x` of the quadrangle satisfies
`x² (ab + cd) = cd(a²+b²) + ab(c²+d²)`; the vertices `A = (0,0)`, `B = (p,h)`, `C = (x,0)`,
`D = (q,-k)` then have the required sides and `h(d² - qx) + k(a² - px) = 0` (cyclicity). -/
theorem brahma_params {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a < b + c + d) (h2 : b < a + c + d) (h3 : c < a + b + d) (h4 : d < a + b + c) :
    ∃ x p h q k : ℝ, 0 < x ∧ 0 < h ∧ 0 < k ∧ p ^ 2 + h ^ 2 = a ^ 2 ∧ (p - x) ^ 2 + h ^ 2 = b ^ 2 ∧
      (q - x) ^ 2 + k ^ 2 = c ^ 2 ∧ q ^ 2 + k ^ 2 = d ^ 2 ∧
      h * (d ^ 2 - q * x) + k * (a ^ 2 - p * x) = 0 := by
  have hab : 0 < a * b + c * d := by positivity
  set Nn : ℝ := c * d * (a ^ 2 + b ^ 2) + a * b * (c ^ 2 + d ^ 2) with hNn
  have hNpos : 0 < Nn := by positivity
  set T : ℝ := Nn / (a * b + c * d) with hTdef
  have hTpos : 0 < T := by positivity
  have hT : T * (a * b + c * d) = Nn := by rw [hTdef]; field_simp
  have i1 : T < (a + b) ^ 2 := by
    have key : ((a + b) ^ 2 - T) * (a * b + c * d) = a * b * ((a + b - c + d) * (a + b + c - d)) := by
      linear_combination (-1) * hT
    have : 0 < ((a + b) ^ 2 - T) * (a * b + c * d) := by
      rw [key]; apply mul_pos (by positivity); apply mul_pos <;> linarith
    linarith [pos_of_mul_pos_aux this hab]
  have i2 : (a - b) ^ 2 < T := by
    have key : (T - (a - b) ^ 2) * (a * b + c * d) = a * b * ((c + d - a + b) * (c + d + a - b)) := by
      linear_combination hT
    have : 0 < (T - (a - b) ^ 2) * (a * b + c * d) := by
      rw [key]; apply mul_pos (by positivity); apply mul_pos <;> linarith
    linarith [pos_of_mul_pos_aux this hab]
  have i3 : T < (c + d) ^ 2 := by
    have key : ((c + d) ^ 2 - T) * (a * b + c * d) = c * d * ((c + d - a + b) * (c + d + a - b)) := by
      linear_combination (-1) * hT
    have : 0 < ((c + d) ^ 2 - T) * (a * b + c * d) := by
      rw [key]; apply mul_pos (by positivity); apply mul_pos <;> linarith
    linarith [pos_of_mul_pos_aux this hab]
  have i4 : (c - d) ^ 2 < T := by
    have key : (T - (c - d) ^ 2) * (a * b + c * d) = c * d * ((a + b - c + d) * (a + b + c - d)) := by
      linear_combination hT
    have : 0 < (T - (c - d) ^ 2) * (a * b + c * d) := by
      rw [key]; apply mul_pos (by positivity); apply mul_pos <;> linarith
    linarith [pos_of_mul_pos_aux this hab]
  obtain ⟨x, hx, hxT⟩ : ∃ x : ℝ, 0 < x ∧ x ^ 2 = T :=
    ⟨√T, Real.sqrt_pos.2 hTpos, Real.sq_sqrt hTpos.le⟩
  have hx2 : x ^ 2 * (a * b + c * d) = Nn := by rw [hxT]; exact hT
  have hxN : x ^ 2 = Nn / (a * b + c * d) := hxT.trans hTdef
  set p : ℝ := (a ^ 2 - b ^ 2 + x ^ 2) / (2 * x) with hp
  set q : ℝ := (d ^ 2 - c ^ 2 + x ^ 2) / (2 * x) with hq
  have hpx : p * x = (a ^ 2 - b ^ 2 + x ^ 2) / 2 := by rw [hp]; field_simp
  have hqx : q * x = (d ^ 2 - c ^ 2 + x ^ 2) / 2 := by rw [hq]; field_simp
  have hap : a ^ 2 - p ^ 2 = ((a + b) ^ 2 - x ^ 2) * (x ^ 2 - (a - b) ^ 2) / (4 * x ^ 2) := by
    rw [hp]; field_simp; ring
  have hdq : d ^ 2 - q ^ 2 = ((c + d) ^ 2 - x ^ 2) * (x ^ 2 - (c - d) ^ 2) / (4 * x ^ 2) := by
    rw [hq]; field_simp; ring
  have hapos : 0 < a ^ 2 - p ^ 2 := by
    rw [hap]; apply div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  have hdpos : 0 < d ^ 2 - q ^ 2 := by
    rw [hdq]; apply div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  set h : ℝ := √(a ^ 2 - p ^ 2) with hh
  set k : ℝ := √(d ^ 2 - q ^ 2) with hk
  have hhpos : 0 < h := Real.sqrt_pos.2 hapos
  have hkpos : 0 < k := Real.sqrt_pos.2 hdpos
  have hh2 : h ^ 2 = a ^ 2 - p ^ 2 := Real.sq_sqrt hapos.le
  have hk2 : k ^ 2 = d ^ 2 - q ^ 2 := Real.sq_sqrt hdpos.le
  have hkab : k * (a * b) = c * d * h := by
    have hsq : (k * (a * b)) ^ 2 = (c * d * h) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hk2, hh2, hdq, hap, hxN]
      field_simp
      ring
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  refine ⟨x, p, h, q, k, hx, hhpos, hkpos, by linarith, ?_, ?_, by linarith, ?_⟩
  · linear_combination hh2 - 2 * hpx
  · linear_combination hk2 - 2 * hqx
  · have : a * b * (h * (d ^ 2 - q * x) + k * (a ^ 2 - p * x)) = 0 := by
      have e1 : d ^ 2 - q * x = (c ^ 2 + d ^ 2 - x ^ 2) / 2 := by rw [hqx]; ring
      have e2 : a ^ 2 - p * x = (a ^ 2 + b ^ 2 - x ^ 2) / 2 := by rw [hpx]; ring
      rw [e1, e2]
      linear_combination (a ^ 2 + b ^ 2 - x ^ 2) / 2 * hkab - h / 2 * hx2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by positivity)
    · exact h0

theorem sqrt_eq_of_sq {S a : ℝ} (ha : 0 ≤ a) (h : S = a ^ 2) : √S = a := by
  rw [h, Real.sqrt_sq ha]

theorem brahma_geom {a b c d x p h q k : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k)
    (e1 : p ^ 2 + h ^ 2 = a ^ 2) (e2 : (p - x) ^ 2 + h ^ 2 = b ^ 2)
    (e3 : (q - x) ^ 2 + k ^ 2 = c ^ 2) (e4 : q ^ 2 + k ^ 2 = d ^ 2)
    (hcyc : h * (d ^ 2 - q * x) + k * (a ^ 2 - p * x) = 0) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    ∃ A B C D M : EuclideanSpace ℝ (Fin 2), dist A B = a ∧ dist B C = b ∧ dist C D = c ∧
      dist D A = d ∧ Cospherical ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Sbtw ℝ A M C ∧ Sbtw ℝ B M D := by
  set e : ℝ := (a ^ 2 - p * x) / (2 * h) with he
  have he2 : 2 * h * e = a ^ 2 - p * x := by rw [he]; field_simp
  set R : ℝ := √((x / 2) ^ 2 + e ^ 2) with hR
  set O : EuclideanSpace ℝ (Fin 2) := !₂[x / 2, e] with hO
  have dA : dist (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) O = R := by
    rw [hO, dist2, hR]; congr 1; ring
  have dB : dist (!₂[p, h] : EuclideanSpace ℝ (Fin 2)) O = R := by
    rw [hO, dist2, hR]; congr 1; linear_combination e1 - he2
  have dC : dist (!₂[x, 0] : EuclideanSpace ℝ (Fin 2)) O = R := by
    rw [hO, dist2, hR]; congr 1; ring
  have dD : dist (!₂[q, -k] : EuclideanSpace ℝ (Fin 2)) O = R := by
    rw [hO, dist2, hR]; congr 1
    have : h * ((q - x / 2) ^ 2 + (-k - e) ^ 2 - ((x / 2) ^ 2 + e ^ 2)) = 0 := by
      linear_combination hcyc + h * e4 + k * he2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hh.ne'
    · linarith
  set m : ℝ := (p * k + q * h) / (h + k) with hm
  have hBMD : Sbtw ℝ (!₂[p, h] : EuclideanSpace ℝ (Fin 2)) !₂[m, 0] !₂[q, -k] := by
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    refine ⟨⟨h / (h + k), ⟨by positivity, ?_⟩, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply, hm]
        field_simp
        ring
      · simp [AffineMap.lineMap_apply]
        field_simp
        ring
    · intro hBD
      have := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 1) hBD
      simp at this
      linarith
  have hin := hBMD.dist_lt_max_dist O
  rw [dB, dD, max_self] at hin
  have hin2 : (m - x / 2) ^ 2 + (0 - e) ^ 2 < (x / 2) ^ 2 + e ^ 2 := by
    rw [hO, dist2, hR] at hin
    exact (Real.sqrt_lt_sqrt_iff (by positivity)).mp hin
  have hm0 : 0 < m := by nlinarith
  have hmx : m < x := by nlinarith
  have hAMC : Sbtw ℝ (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[m, 0] !₂[x, 0] := by
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    refine ⟨⟨m / x, ⟨by positivity, ?_⟩, ?_⟩, ?_⟩
    · rw [div_lt_one hx]; exact hmx
    · ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply]
        field_simp
      · simp [AffineMap.lineMap_apply]
    · intro hAC
      have := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 0) hAC
      simp at this
      linarith
  refine ⟨!₂[0, 0], !₂[p, h], !₂[x, 0], !₂[q, -k], !₂[m, 0], ?_, ?_, ?_, ?_, ⟨O, R, ?_⟩, hAMC, hBMD⟩
  · rw [dist2]; exact sqrt_eq_of_sq ha.le (by linear_combination e1)
  · rw [dist2]; exact sqrt_eq_of_sq hb.le (by linear_combination e2)
  · rw [dist2]; exact sqrt_eq_of_sq hc.le (by linear_combination e3)
  · rw [dist2]; exact sqrt_eq_of_sq hd.le (by linear_combination e4)
  · intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl | rfl | rfl
    exacts [dA, dB, dC, dD]

/-- **Problem of Brahmagupta, existence form** (Petrunin, Problem 19.1, p. 157): for positive
`a, b, c, d`, each less than the sum of the other three, there is a convex quadrangle `ABCD` in the
Euclidean plane, inscribed in a circle, with sides `AB = a`, `BC = b`, `CD = c`, `DA = d`. Convexity
is expressed by the diagonals crossing at a point `M` strictly inside both. (The condition on the
lengths is also necessary, by the triangle inequality, so this characterizes the possible side
lengths; the construction is by the diagonal `AC` with
`AC² = (ac + bd)(ad + bc)/(ab + cd)`.) -/
@[kb "petrunin2025" "Problem 19.1, p. 157"]
theorem brahmagupta_exists {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a < b + c + d) (h2 : b < a + c + d) (h3 : c < a + b + d) (h4 : d < a + b + c) :
    ∃ A B C D M : EuclideanSpace ℝ (Fin 2), dist A B = a ∧ dist B C = b ∧ dist C D = c ∧
      dist D A = d ∧ Cospherical ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin 2))) ∧
      Sbtw ℝ A M C ∧ Sbtw ℝ B M D := by
  obtain ⟨x, p, h, q, k, hx, hh, hk, e1, e2, e3, e4, hcyc⟩ :=
    brahma_params ha hb hc hd h1 h2 h3 h4
  exact brahma_geom hx hh hk e1 e2 e3 e4 hcyc ha hb hc hd

end Brahmagupta

/-! ### Problem 19.2 (Apollonius): existence of a circle tangent to three exterior circles

A circle `(X, ρ)` with a signed radius `σ` (`ρ = |σ|`) is tangent to the circle `(O_i, r_i)` iff
`|X - O_i| = |σ - t_i|` for `t_i = ± r_i`. Writing `X = O₁ + (x, y)` and `z = σ - r₁`, the three
equations become `x² + y² = z²` plus two *linear* equations in `(x, y, z)`, i.e. a point of the light
cone of the Lorentz form `x² + y² - z²` on a line; this line meets the cone as soon as its Gram
determinant `det` is nonzero (the discriminant is then a positive multiple of
`|O₂O₃|² - (t₂ - t₃)²`), and `det` is nonzero for at least one of the four sign patterns. -/

section Apollonius

/-- The Lorentz-signature Gram determinant of `(d₂₁, d₂₂, s₂)`, `(d₃₁, d₃₂, s₃)`. -/
def lorentzDet (d21 d22 d31 d32 s2 s3 : ℝ) : ℝ :=
  (d21 ^ 2 + d22 ^ 2 - s2 ^ 2) * (d31 ^ 2 + d32 ^ 2 - s3 ^ 2) -
    (d21 * d31 + d22 * d32 - s2 * s3) ^ 2

theorem lorentz_exists {u1 u2 u3 v1 v2 v3 m n g1 g2 g12 : ℝ}
    (hg1 : g1 = u1 ^ 2 + u2 ^ 2 - u3 ^ 2) (hg2 : g2 = v1 ^ 2 + v2 ^ 2 - v3 ^ 2)
    (hg12 : g12 = u1 * v1 + u2 * v2 - u3 * v3)
    (hdet : g1 * g2 - g12 ^ 2 ≠ 0) (hQ : 0 ≤ g2 * m ^ 2 - 2 * g12 * m * n + g1 * n ^ 2) :
    ∃ x y z : ℝ, x * u1 + y * u2 - z * u3 = m ∧ x * v1 + y * v2 - z * v3 = n ∧
      x ^ 2 + y ^ 2 = z ^ 2 := by
  have hc2 : (√(g2 * m ^ 2 - 2 * g12 * m * n + g1 * n ^ 2)) ^ 2 =
      g2 * m ^ 2 - 2 * g12 * m * n + g1 * n ^ 2 := Real.sq_sqrt hQ
  obtain ⟨det, hdetdef⟩ : ∃ det, det = g1 * g2 - g12 ^ 2 := ⟨_, rfl⟩
  rw [← hdetdef] at hdet
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = g2 * m ^ 2 - 2 * g12 * m * n + g1 * n ^ 2 := ⟨_, rfl⟩
  rw [← hQdef] at hc2 hQ
  obtain ⟨a, ha⟩ : ∃ a, a = (g2 * m - g12 * n) / det := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (g1 * n - g12 * m) / det := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = √Q / det := ⟨_, rfl⟩
  have hab1 : a * g1 + b * g12 = m := by
    rw [ha, hb]; field_simp; rw [hdetdef]; ring
  have hab2 : a * g12 + b * g2 = n := by
    rw [ha, hb]; field_simp; rw [hdetdef]; ring
  have hcc : c ^ 2 * det ^ 2 = Q := by
    rw [hc, div_pow, hc2]; field_simp
  have h5 : (a * m + b * n) * det = Q := by
    rw [ha, hb, hQdef]; field_simp; ring
  have h6 : a * m + b * n - c ^ 2 * det = 0 := by
    have : (a * m + b * n - c ^ 2 * det) * det = 0 := by linear_combination h5 - hcc
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hdet
  have I1 : (u2 * v3 - u3 * v2) * u1 + (u3 * v1 - u1 * v3) * u2 + (u1 * v2 - u2 * v1) * u3 = 0 := by
    ring
  have I2 : (u2 * v3 - u3 * v2) * v1 + (u3 * v1 - u1 * v3) * v2 + (u1 * v2 - u2 * v1) * v3 = 0 := by
    ring
  have I3 : (u2 * v3 - u3 * v2) ^ 2 + (u3 * v1 - u1 * v3) ^ 2 - (u1 * v2 - u2 * v1) ^ 2 = -det := by
    rw [hdetdef, hg1, hg2, hg12]; ring
  subst hg1 hg2 hg12
  refine ⟨a * u1 + b * v1 + c * (u2 * v3 - u3 * v2), a * u2 + b * v2 + c * (u3 * v1 - u1 * v3),
    a * u3 + b * v3 - c * (u1 * v2 - u2 * v1), ?_, ?_, ?_⟩
  · linear_combination hab1 + c * I1
  · linear_combination hab2 + c * I2
  · linear_combination a * hab1 + b * hab2 + 2 * c * a * I1 + 2 * c * b * I2 + c ^ 2 * I3 + h6

theorem apollonius_pattern {d21 d22 d31 d32 r1 r2 r3 t2 t3 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hr3 : 0 < r3) (h12 : (r1 + r2) ^ 2 < d21 ^ 2 + d22 ^ 2) (h13 : (r1 + r3) ^ 2 < d31 ^ 2 + d32 ^ 2)
    (h23 : (r2 + r3) ^ 2 < (d21 - d31) ^ 2 + (d22 - d32) ^ 2) (ht2 : -r2 ≤ t2 ∧ t2 ≤ r2)
    (ht3 : -r3 ≤ t3 ∧ t3 ≤ r3) (hdet : lorentzDet d21 d22 d31 d32 (t2 - r1) (t3 - r1) ≠ 0) :
    ∃ x y σ : ℝ, x ^ 2 + y ^ 2 = (σ - r1) ^ 2 ∧ (x - d21) ^ 2 + (y - d22) ^ 2 = (σ - t2) ^ 2 ∧
      (x - d31) ^ 2 + (y - d32) ^ 2 = (σ - t3) ^ 2 := by
  obtain ⟨ht2a, ht2b⟩ := ht2
  obtain ⟨ht3a, ht3b⟩ := ht3
  have hs2 : (t2 - r1) ^ 2 < d21 ^ 2 + d22 ^ 2 := by
    refine lt_of_le_of_lt ?_ h12
    nlinarith
  have hs3 : (t3 - r1) ^ 2 < d31 ^ 2 + d32 ^ 2 := by
    refine lt_of_le_of_lt ?_ h13
    nlinarith
  have hs23 : (t2 - t3) ^ 2 < (d21 - d31) ^ 2 + (d22 - d32) ^ 2 := by
    refine lt_of_le_of_lt ?_ h23
    nlinarith
  obtain ⟨x, y, z, e1, e2, e3⟩ := lorentz_exists
    (u1 := d21) (u2 := d22) (u3 := t2 - r1) (v1 := d31) (v2 := d32) (v3 := t3 - r1)
    (m := (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) / 2) (n := (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) / 2)
    (g1 := d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) (g2 := d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2)
    (g12 := d21 * d31 + d22 * d32 - (t2 - r1) * (t3 - r1)) rfl rfl rfl hdet (by
      have hm : 0 < d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2 := by linarith
      have hn : 0 < d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2 := by linarith
      have hk : 0 < (d21 - d31) ^ 2 + (d22 - d32) ^ 2 - (t2 - t3) ^ 2 := by linarith
      have : (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) * ((d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) / 2) ^ 2 -
          2 * (d21 * d31 + d22 * d32 - (t2 - r1) * (t3 - r1)) *
            ((d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) / 2) * ((d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) / 2) +
          (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) * ((d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) / 2) ^ 2 =
          (d21 ^ 2 + d22 ^ 2 - (t2 - r1) ^ 2) * (d31 ^ 2 + d32 ^ 2 - (t3 - r1) ^ 2) *
            ((d21 - d31) ^ 2 + (d22 - d32) ^ 2 - (t2 - t3) ^ 2) / 4 := by ring
      rw [this]
      positivity)
  refine ⟨x, y, z + r1, by linear_combination e3, ?_, ?_⟩
  · linear_combination e3 - 2 * e1
  · linear_combination e3 - 2 * e2

theorem exists_pattern {d21 d22 d31 d32 r1 r2 r3 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) (hr3 : 0 < r3)
    (h13 : (r1 + r3) ^ 2 < d31 ^ 2 + d32 ^ 2) :
    ∃ t2 t3 : ℝ, (t2 = r2 ∨ t2 = -r2) ∧ (t3 = r3 ∨ t3 = -r3) ∧
      lorentzDet d21 d22 d31 d32 (t2 - r1) (t3 - r1) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hpp := hcon r2 r3 (Or.inl rfl) (Or.inl rfl)
  have hmp := hcon (-r2) r3 (Or.inr rfl) (Or.inl rfl)
  have hpm := hcon r2 (-r3) (Or.inl rfl) (Or.inr rfl)
  have hmm := hcon (-r2) (-r3) (Or.inr rfl) (Or.inr rfl)
  simp only [lorentzDet] at hpp hmp hpm hmm
  have k1 : r2 * (r1 * (d31 ^ 2 + d32 ^ 2) + (r3 - r1) * (d21 * d31 + d22 * d32)) = 0 := by
    linear_combination (1 / 4) * (hpp - hmp)
  have k2 : r2 * (r1 * (d31 ^ 2 + d32 ^ 2) + (-r3 - r1) * (d21 * d31 + d22 * d32)) = 0 := by
    linear_combination (1 / 4) * (hpm - hmm)
  have k1' := (mul_eq_zero.mp k1).resolve_left hr2.ne'
  have k2' := (mul_eq_zero.mp k2).resolve_left hr2.ne'
  have hC : d21 * d31 + d22 * d32 = 0 := by
    have : r3 * (d21 * d31 + d22 * d32) = 0 := by linear_combination (1 / 2) * (k1' - k2')
    exact (mul_eq_zero.mp this).resolve_left hr3.ne'
  rw [hC] at k1'
  have hB : 0 < d31 ^ 2 + d32 ^ 2 := by nlinarith [sq_nonneg (r1 + r3), mul_pos hr1 hr3]
  nlinarith [mul_pos hr1 hB]

theorem apollonius_core {d21 d22 d31 d32 r1 r2 r3 : ℝ} (hr1 : 0 < r1) (hr2 : 0 < r2) (hr3 : 0 < r3)
    (h12 : (r1 + r2) ^ 2 < d21 ^ 2 + d22 ^ 2) (h13 : (r1 + r3) ^ 2 < d31 ^ 2 + d32 ^ 2)
    (h23 : (r2 + r3) ^ 2 < (d21 - d31) ^ 2 + (d22 - d32) ^ 2) :
    ∃ x y σ t2 t3 : ℝ, (t2 = r2 ∨ t2 = -r2) ∧ (t3 = r3 ∨ t3 = -r3) ∧
      x ^ 2 + y ^ 2 = (σ - r1) ^ 2 ∧ (x - d21) ^ 2 + (y - d22) ^ 2 = (σ - t2) ^ 2 ∧
      (x - d31) ^ 2 + (y - d32) ^ 2 = (σ - t3) ^ 2 := by
  obtain ⟨t2, t3, h2, h3, hdet⟩ := exists_pattern (d21 := d21) (d22 := d22) hr1 hr2 hr3 h13
  have b2 : -r2 ≤ t2 ∧ t2 ≤ r2 := by rcases h2 with rfl | rfl <;> constructor <;> linarith
  have b3 : -r3 ≤ t3 ∧ t3 ≤ r3 := by rcases h3 with rfl | rfl <;> constructor <;> linarith
  obtain ⟨x, y, σ, e1, e2, e3⟩ := apollonius_pattern hr1 hr2 hr3 h12 h13 h23 b2 b3 hdet
  exact ⟨x, y, σ, t2, t3, h2, h3, e1, e2, e3⟩

/-- Two circles are tangent (Petrunin: distinct circles with exactly one common point) iff they
are distinct and the distance between the centres is the sum (external tangency) or the absolute
difference (internal tangency) of the radii. -/
def CirclesTangent {P : Type*} [MetricSpace P] (Γ Ω : EuclideanGeometry.Sphere P) : Prop :=
  Γ ≠ Ω ∧ (dist Γ.center Ω.center = Γ.radius + Ω.radius ∨
    dist Γ.center Ω.center = |Γ.radius - Ω.radius|)

theorem dist_coords (P Q : EuclideanSpace ℝ (Fin 2)) :
    dist P Q = √((P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_sq_coords (P Q : EuclideanSpace ℝ (Fin 2)) :
    dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [dist_coords, Real.sq_sqrt (by positivity)]

theorem tangent_abs {σ t r : ℝ} (hr : 0 < r) (ht : t = r ∨ t = -r) :
    |σ - t| = |σ| + r ∨ |σ - t| = |(|σ| - r)| := by
  rcases ht with rfl | rfl <;> rcases le_total 0 σ with h | h
  · right; rw [abs_of_nonneg h]
  · left
    rw [abs_of_nonpos h, abs_of_nonpos (by linarith : σ - t ≤ 0)]; ring
  · left
    rw [sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ σ + r), abs_of_nonneg h]
  · right
    rw [sub_neg_eq_add, abs_of_nonpos h, show -σ - r = -(σ + r) by ring, abs_neg]

theorem abs_of_pm {t r : ℝ} (hr : 0 < r) (ht : t = r ∨ t = -r) : |t| = r := by
  rcases ht with rfl | rfl
  · exact abs_of_pos hr
  · rw [abs_neg, abs_of_pos hr]

/-- **Problem of Apollonius, existence form** (Petrunin, Problem 19.2, p. 157), in the Euclidean
plane `ℝ²`. Covered configuration: three circles `(O_i, r_i)` that are *pairwise exterior*
(`r_i + r_j < |O_i O_j|`, so no two meet and none lies inside another); the centres may be collinear
and the radii arbitrary. Conclusion: there is a circle `Γ` of positive radius tangent (externally
or internally) to all three. The construction itself (ruler and compass) is not formalized. -/
@[kb "petrunin2025" "Problem 19.2, p. 157"]
theorem apollonius_exists (O₁ O₂ O₃ : EuclideanSpace ℝ (Fin 2)) {r₁ r₂ r₃ : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) (h12 : r₁ + r₂ < dist O₁ O₂) (h13 : r₁ + r₃ < dist O₁ O₃)
    (h23 : r₂ + r₃ < dist O₂ O₃) :
    ∃ Γ : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)), 0 < Γ.radius ∧
      CirclesTangent Γ ⟨O₁, r₁⟩ ∧ CirclesTangent Γ ⟨O₂, r₂⟩ ∧ CirclesTangent Γ ⟨O₃, r₃⟩ := by
  have s12 : (r₁ + r₂) ^ 2 < (O₂ 0 - O₁ 0) ^ 2 + (O₂ 1 - O₁ 1) ^ 2 := by
    have := pow_lt_pow_left₀ h12 (by positivity) (two_ne_zero)
    rw [dist_sq_coords] at this; nlinarith
  have s13 : (r₁ + r₃) ^ 2 < (O₃ 0 - O₁ 0) ^ 2 + (O₃ 1 - O₁ 1) ^ 2 := by
    have := pow_lt_pow_left₀ h13 (by positivity) (two_ne_zero)
    rw [dist_sq_coords] at this; nlinarith
  have s23 : (r₂ + r₃) ^ 2 <
      ((O₂ 0 - O₁ 0) - (O₃ 0 - O₁ 0)) ^ 2 + ((O₂ 1 - O₁ 1) - (O₃ 1 - O₁ 1)) ^ 2 := by
    have := pow_lt_pow_left₀ h23 (by positivity) (two_ne_zero)
    rw [dist_sq_coords] at this; nlinarith
  obtain ⟨x, y, σ, t2, t3, h2, h3, e1, e2, e3⟩ := apollonius_core hr₁ hr₂ hr₃ s12 s13 s23
  set X : EuclideanSpace ℝ (Fin 2) := !₂[O₁ 0 + x, O₁ 1 + y] with hX
  have hX0 : X 0 = O₁ 0 + x := by simp [hX]
  have hX1 : X 1 = O₁ 1 + y := by simp [hX]
  have d1 : dist X O₁ = |σ - r₁| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e1
  have d2 : dist X O₂ = |σ - t2| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e2
  have d3 : dist X O₃ = |σ - t3| := by
    rw [dist_coords, hX0, hX1, ← Real.sqrt_sq_eq_abs]; congr 1; linear_combination e3
  have a1 : |t2| = r₂ := abs_of_pm hr₂ h2
  have a2 : |t3| = r₃ := abs_of_pm hr₃ h3
  have hσ : σ ≠ 0 := by
    intro h0
    have := dist_triangle O₁ X O₂
    rw [dist_comm O₁ X, d1, d2, h0, zero_sub, abs_neg, abs_of_pos hr₁, zero_sub, abs_neg, a1] at this
    linarith
  have hpos : 0 < |σ| := abs_pos.mpr hσ
  have ine : ∀ (O : EuclideanSpace ℝ (Fin 2)) (t r : ℝ), dist X O = |σ - t| → |t| = r → dist X O ≤ |σ| + r :=
    fun O t r hd ht => by
      rw [hd, ← ht]; exact abs_sub σ t
  refine ⟨⟨X, |σ|⟩, hpos, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have hc : X = O₁ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₁ := congrArg EuclideanGeometry.Sphere.radius h
    have := ine O₂ t2 r₂ d2 a1
    rw [hc, hr] at this
    linarith
  · exact (tangent_abs hr₁ (Or.inl rfl) |>.imp (fun h => d1.trans h) (fun h => d1.trans h))
  · intro h
    have hc : X = O₂ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₂ := congrArg EuclideanGeometry.Sphere.radius h
    have := ine O₁ r₁ r₁ (by rw [d1]) (abs_of_pos hr₁)
    rw [hc, hr, dist_comm] at this
    linarith
  · exact (tangent_abs hr₂ h2 |>.imp (fun h => d2.trans h) (fun h => d2.trans h))
  · intro h
    have hc : X = O₃ := congrArg EuclideanGeometry.Sphere.center h
    have hr : |σ| = r₃ := congrArg EuclideanGeometry.Sphere.radius h
    have := ine O₁ r₁ r₁ (by rw [d1]) (abs_of_pos hr₁)
    rw [hc, hr, dist_comm] at this
    linarith
  · exact (tangent_abs hr₃ h3 |>.imp (fun h => d3.trans h) (fun h => d3.trans h))

end Apollonius

end UndergradKB.Geometry
