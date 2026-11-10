import UndergradKB.Calculus.Vectors

/-! # Calculus: lines and planes in space, and distances

Lines `line P v = {P + t v}`, planes in point-normal form `plane n P₀ = {x | n · (x − P₀) = 0}` and in general
form `{x | n · x + d = 0}`. Distances are stated as minima (`IsLeast`) of the Euclidean length `len` over the
points of the objects, so that the book's closed formulas are proved to be the distances. -/

namespace UndergradKB.Calculus

open Matrix

/-- The line through `P` with direction vector `v`: all points `P + t v`. -/
def line (P v : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := {x | ∃ t : ℝ, x = P + t • v}

/-- The plane through `P₀` with normal vector `n` (point-normal form): all `x` with `n · (x − P₀) = 0`. -/
def plane (n P₀ : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := {x | n ⬝ᵥ (x - P₀) = 0}

/-- The plane `n · x + d = 0` in general form. -/
def planeGen (n : Fin 3 → ℝ) (d : ℝ) : Set (Fin 3 → ℝ) := {x | n ⬝ᵥ x + d = 0}

/-! ## Lines (CA-460) and planes (CA-464, CA-434) -/

/-- OpenStax Calculus 3:Theorem 2.11, p. 179 (CA-460): the point `x` lies on the line through `P`
with direction `v` iff the parametric equations `x_i = P_i + t v_i` hold for one `t`; and, when all
direction numbers are nonzero, iff the symmetric equations hold. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.11, p. 179"]
theorem line_forms (P v x : Fin 3 → ℝ) :
    (x ∈ line P v ↔ ∃ t : ℝ, x 0 = P 0 + t * v 0 ∧ x 1 = P 1 + t * v 1 ∧ x 2 = P 2 + t * v 2) ∧
    (v 0 ≠ 0 → v 1 ≠ 0 → v 2 ≠ 0 →
      (x ∈ line P v ↔ (x 0 - P 0) / v 0 = (x 1 - P 1) / v 1 ∧ (x 1 - P 1) / v 1 = (x 2 - P 2) / v 2)) := by
  have par : x ∈ line P v ↔ ∃ t : ℝ, x 0 = P 0 + t * v 0 ∧ x 1 = P 1 + t * v 1 ∧ x 2 = P 2 + t * v 2 := by
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp, by simp, by simp⟩
    · rintro ⟨t, h0, h1, h2⟩
      refine ⟨t, ?_⟩
      ext i; fin_cases i <;> simp [h0, h1, h2]
  refine ⟨par, fun h0 h1 h2 => ?_⟩
  rw [par]
  constructor
  · rintro ⟨t, e0, e1, e2⟩
    rw [e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> field_simp <;> ring
  · rintro ⟨e1, e2⟩
    refine ⟨(x 0 - P 0) / v 0, ?_, ?_, ?_⟩
    · field_simp; ring
    · rw [e1]; field_simp; ring
    · rw [e1, e2]; field_simp; ring

/-- OpenStax Calculus 3:Eq 2.17, 2.18, p. 186 (CA-464): the point-normal form
`n · (x − P₀) = 0`, the scalar form `a(x−x₀)+b(y−y₀)+c(z−z₀) = 0` and the general form
`ax + by + cz + d = 0` with `d = −n · P₀` define the same set. -/
@[kb "openstaxcalculus2016" "3:§2.5 Definition (vector and scalar equation of a plane, Eq 2.17, 2.18), p. 186"]
theorem plane_forms (n P₀ : Fin 3 → ℝ) :
    plane n P₀ = {x | n 0 * (x 0 - P₀ 0) + n 1 * (x 1 - P₀ 1) + n 2 * (x 2 - P₀ 2) = 0} ∧
    plane n P₀ = planeGen n (-(n ⬝ᵥ P₀)) ∧
    planeGen n (-(n ⬝ᵥ P₀)) =
      {x | n 0 * x 0 + n 1 * x 1 + n 2 * x 2 + (-(n 0 * P₀ 0 + n 1 * P₀ 1 + n 2 * P₀ 2)) = 0} := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;>
    simp [plane, planeGen, dot_expand, sub_eq_add_neg, mul_add]
  constructor <;> intro h <;> linarith

/-- OpenStax Calculus 3:Eq 2.18, p. 186 (CA-464), converse: every plane `n · x + d = 0` with
`n ≠ 0` is the plane through some point `P₀` with normal `n`. -/
@[kb "openstaxcalculus2016" "3:§2.5 Definition (vector and scalar equation of a plane, Eq 2.17, 2.18), p. 186"]
theorem planeGen_eq_plane {n : Fin 3 → ℝ} (hn : n ≠ 0) (d : ℝ) :
    ∃ P₀, planeGen n d = plane n P₀ := by
  have hne : n ⬝ᵥ n ≠ 0 := fun h => hn (dotProduct_self_eq_zero.1 h)
  refine ⟨(-d / (n ⬝ᵥ n)) • n, ?_⟩
  ext x
  simp only [planeGen, plane, Set.mem_ofPred_eq, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  field_simp
  constructor <;> intro h <;> linarith

/-- OpenStax Calculus 3:§2.2 Rule (equations of planes parallel to coordinate planes), p. 124
(CA-434): the plane through `P₀` with normal `k` (resp. `j`, `i`) is `z = z₀` (resp. `y = y₀`, `x = x₀`);
in particular the coordinate planes are `z = 0`, `y = 0`, `x = 0`. -/
@[kb "openstaxcalculus2016" "3:§2.2 Rule: Equations of Planes Parallel to Coordinate Planes, p. 124"]
theorem plane_parallel_coordinate (P₀ : Fin 3 → ℝ) :
    plane ek P₀ = {x | x 2 = P₀ 2} ∧ plane ej P₀ = {x | x 1 = P₀ 1} ∧
      plane ei P₀ = {x | x 0 = P₀ 0} ∧
      plane ek 0 = {x | x 2 = 0} ∧ plane ej 0 = {x | x 1 = 0} ∧ plane ei 0 = {x | x 0 = 0} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext x <;>
    simp [plane, ei, ej, ek, dotProduct, Fin.sum_univ_three, sub_eq_zero]

/-! ## Distance identities -/

lemma len_sub_smul_sq (w v : Fin 3 → ℝ) (t : ℝ) :
    (len (w - t • v) * len v) ^ 2 = len (w ⨯₃ v) ^ 2 + (w ⬝ᵥ v - t * (v ⬝ᵥ v)) ^ 2 := by
  rw [mul_pow, len_sq, len_sq, len_sq]
  simp only [dot_expand, cross_0, cross_1, cross_2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma abs_dot_le_len (n y : Fin 3 → ℝ) : |n ⬝ᵥ y| ≤ len n * len y := by
  have h := lagrange n y
  have h0 : 0 ≤ (n ⨯₃ y) ⬝ᵥ (n ⨯₃ y) := dot_self_nonneg _
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (by have := len_nonneg n; have := len_nonneg y; positivity)
    two_ne_zero).1 ?_
  rw [sq_abs, mul_pow, len_sq, len_sq]
  nlinarith

/-- OpenStax Calculus 3:Theorem 2.12, p. 181 (CA-462): the distance from `Q` to the line through `P`
with direction `v ≠ 0` is `‖PQ × v‖ / ‖v‖`; precisely, this number is the minimum (attained) of the
distances from `Q` to the points `P + t v` of the line. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.12, p. 181"]
theorem distance_point_line (P Q v : Fin 3 → ℝ) (hv : v ≠ 0) :
    IsLeast {r | ∃ t : ℝ, r = len (Q - (P + t • v))} (len ((Q - P) ⨯₃ v) / len v) := by
  have hl := len_pos hv
  have hvv : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.1 h)
  constructor
  · refine ⟨(Q - P) ⬝ᵥ v / (v ⬝ᵥ v), ?_⟩
    have e : Q - (P + ((Q - P) ⬝ᵥ v / (v ⬝ᵥ v)) • v) = (Q - P) - ((Q - P) ⬝ᵥ v / (v ⬝ᵥ v)) • v := by
      abel
    rw [e]
    have h := len_sub_smul_sq (Q - P) v ((Q - P) ⬝ᵥ v / (v ⬝ᵥ v))
    have h2 : (Q - P) ⬝ᵥ v - (Q - P) ⬝ᵥ v / (v ⬝ᵥ v) * (v ⬝ᵥ v) = 0 := by field_simp; ring
    rw [h2] at h
    rw [div_eq_iff hl.ne']
    refine (sq_eq_sq₀ (len_nonneg _) (mul_nonneg (len_nonneg _) hl.le)).1 ?_
    rw [h]; ring
  · rintro r ⟨t, rfl⟩
    have e : Q - (P + t • v) = (Q - P) - t • v := by abel
    rw [e, div_le_iff₀ hl]
    have h := len_sub_smul_sq (Q - P) v t
    refine (pow_le_pow_iff_left₀ (len_nonneg _)
      (by have := len_nonneg ((Q - P) - t • v); positivity) two_ne_zero).1 ?_
    rw [h]; nlinarith [sq_nonneg ((Q - P) ⬝ᵥ v - t * (v ⬝ᵥ v))]

/-- OpenStax Calculus 3:Theorem 2.13, p. 188 (CA-465): the distance from `Q = (x₀, y₀, z₀)` to the
plane `a x + b y + c z + d = 0` (normal `n = (a, b, c) ≠ 0`) is `|n · Q + d| / ‖n‖`, i.e.
`|a x₀ + b y₀ + c z₀ + d| / √(a²+b²+c²)`; precisely the minimum (attained) of the distances from `Q`
to the points of the plane. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.13, p. 188"]
theorem distance_point_plane (n : Fin 3 → ℝ) (d : ℝ) (Q : Fin 3 → ℝ) (hn : n ≠ 0) :
    IsLeast {r | ∃ x ∈ planeGen n d, r = len (Q - x)} (|n ⬝ᵥ Q + d| / len n) := by
  have hl := len_pos hn
  have hne : n ⬝ᵥ n ≠ 0 := fun h => hn (dotProduct_self_eq_zero.1 h)
  constructor
  · refine ⟨Q - ((n ⬝ᵥ Q + d) / (n ⬝ᵥ n)) • n, ?_, ?_⟩
    · simp only [planeGen, Set.mem_ofPred_eq, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      field_simp; ring
    · rw [sub_sub_cancel, len_smul, ← len_sq, abs_div, abs_of_pos (by positivity : 0 < len n ^ 2)]
      field_simp
  · rintro r ⟨x, hx, rfl⟩
    have h : n ⬝ᵥ (Q - x) = n ⬝ᵥ Q + d := by
      simp only [planeGen, Set.mem_ofPred_eq] at hx
      rw [dotProduct_sub]; linarith
    rw [div_le_iff₀ hl, ← h, mul_comm]
    exact abs_dot_le_len n (Q - x)

/-- OpenStax Calculus 3:Theorem 2.13, p. 188 (CA-465), point-normal form: the distance from `P` to
the plane through `Q` with normal `n` is `|n · QP| / ‖n‖`, again as an attained minimum. -/
@[kb "openstaxcalculus2016" "3:Theorem 2.13, p. 188"]
theorem distance_point_plane_pointNormal (n Q P : Fin 3 → ℝ) (hn : n ≠ 0) :
    IsLeast {r | ∃ x ∈ plane n Q, r = len (P - x)} (|n ⬝ᵥ (P - Q)| / len n) := by
  have h := distance_point_plane n (-(n ⬝ᵥ Q)) P hn
  have e : plane n Q = planeGen n (-(n ⬝ᵥ Q)) := (plane_forms n Q).2.1
  have e2 : n ⬝ᵥ (P - Q) = n ⬝ᵥ P + -(n ⬝ᵥ Q) := by rw [dotProduct_sub]; ring
  rw [e, e2]; exact h

/-- OpenStax Calculus 3:Theorem 2.14, p. 191 (CA-465): the distance between the parallel planes
`n · x + d₁ = 0` and `n · x + d₂ = 0` is `|d₁ − d₂| / ‖n‖`, as an attained minimum over pairs of
points (so it does not depend on the points chosen). -/
@[kb "openstaxcalculus2016" "3:Theorem 2.14, p. 191"]
theorem distance_parallel_planes (n : Fin 3 → ℝ) (d₁ d₂ : ℝ) (hn : n ≠ 0) :
    IsLeast {r | ∃ x ∈ planeGen n d₁, ∃ y ∈ planeGen n d₂, r = len (x - y)}
      (|d₁ - d₂| / len n) := by
  have hl := len_pos hn
  have hne : n ⬝ᵥ n ≠ 0 := fun h => hn (dotProduct_self_eq_zero.1 h)
  constructor
  · refine ⟨(-d₂ / (n ⬝ᵥ n)) • n + ((d₂ - d₁) / (n ⬝ᵥ n)) • n, ?_, (-d₂ / (n ⬝ᵥ n)) • n, ?_, ?_⟩
    · simp only [planeGen, Set.mem_ofPred_eq, dotProduct_add, dotProduct_smul, smul_eq_mul]
      field_simp; ring
    · simp only [planeGen, Set.mem_ofPred_eq, dotProduct_smul, smul_eq_mul]
      field_simp; ring
    · rw [add_sub_cancel_left, len_smul, ← len_sq, abs_div, abs_of_pos (by positivity : 0 < len n ^ 2),
        abs_sub_comm]
      field_simp
  · rintro r ⟨x, hx, y, hy, rfl⟩
    have h : n ⬝ᵥ (x - y) = d₂ - d₁ := by
      simp only [planeGen, Set.mem_ofPred_eq] at hx hy
      rw [dotProduct_sub]; linarith
    have h' : |d₁ - d₂| = |n ⬝ᵥ (x - y)| := by rw [h, abs_sub_comm]
    rw [div_le_iff₀ hl, h', mul_comm]
    exact abs_dot_le_len n (x - y)

/-- Cramer's rule in `ℝ³` for the basis `a, b, a × b`. -/
lemma cramer_cross (a b w : Fin 3 → ℝ) :
    ((a ⨯₃ b) ⬝ᵥ (a ⨯₃ b)) • w =
      (w ⬝ᵥ (b ⨯₃ (a ⨯₃ b))) • a + (w ⬝ᵥ ((a ⨯₃ b) ⨯₃ a)) • b + (w ⬝ᵥ (a ⨯₃ b)) • (a ⨯₃ b) := by
  ext i; fin_cases i <;>
  · simp only [dot_expand, cross_0, cross_1, cross_2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    ring

/-- OpenStax Calculus 3:Student Project (distance between two skew lines), p. 192 (CA-468): for the
lines through `P` and `Q` with non-parallel directions `a`, `b` (`a × b ≠ 0`), the distance is
`|(a × b) · PQ| / ‖a × b‖`, precisely the attained minimum of the distances between points of the two
lines. -/
@[kb "openstaxcalculus2016" "3:§2.5 Student Project (distance between two skew lines), p. 192"]
theorem distance_skew_lines (P Q a b : Fin 3 → ℝ) (hab : a ⨯₃ b ≠ 0) :
    IsLeast {r | ∃ s t : ℝ, r = len ((P + s • a) - (Q + t • b))}
      (|(a ⨯₃ b) ⬝ᵥ (Q - P)| / len (a ⨯₃ b)) := by
  set c := a ⨯₃ b with hc
  have hl := len_pos hab
  have hcc : c ⬝ᵥ c ≠ 0 := fun h => hab (dotProduct_self_eq_zero.1 h)
  have hca : c ⬝ᵥ a = 0 := by rw [hc]; exact dot_self_cross a b |> fun h => by rw [dotProduct_comm]; exact h
  have hcb : c ⬝ᵥ b = 0 := by rw [hc, dotProduct_comm]; exact dot_cross_self a b
  constructor
  · -- attaining pair
    set w := P - Q with hw
    have hcr := cramer_cross a b w
    rw [← hc] at hcr
    set α := (w ⬝ᵥ (b ⨯₃ c)) / (c ⬝ᵥ c)
    set β := (w ⬝ᵥ (c ⨯₃ a)) / (c ⬝ᵥ c)
    set γ := (w ⬝ᵥ c) / (c ⬝ᵥ c)
    have hw' : w = α • a + β • b + γ • c := by
      have := congrArg (fun z => (c ⬝ᵥ c)⁻¹ • z) hcr
      simp only [smul_smul, inv_mul_cancel₀ hcc, one_smul, smul_add] at this
      rw [this]; simp only [α, β, γ, div_eq_inv_mul]
    refine ⟨-α, β, ?_⟩
    have e : (P + (-α) • a) - (Q + β • b) = γ • c := by
      have : (P + (-α) • a) - (Q + β • b) = w - α • a - β • b := by
        rw [hw]; module
      rw [this, hw']; module
    rw [e, len_smul, hc]
    simp only [γ, ← hc]
    rw [← len_sq, abs_div, abs_of_pos (by positivity : 0 < len c ^ 2)]
    have : |w ⬝ᵥ c| = |c ⬝ᵥ (Q - P)| := by
      rw [dotProduct_comm, hw, ← abs_neg, ← dotProduct_neg, neg_sub]
    rw [this]; field_simp
  · rintro r ⟨s, t, rfl⟩
    have h : c ⬝ᵥ ((P + s • a) - (Q + t • b)) = -(c ⬝ᵥ (Q - P)) := by
      have : (P + s • a) - (Q + t • b) = -(Q - P) + s • a - t • b := by module
      rw [this, dotProduct_sub, dotProduct_add, dotProduct_neg, dotProduct_smul, dotProduct_smul, hca, hcb]
      simp
    rw [div_le_iff₀ hl, ← abs_neg, ← h, mul_comm]
    exact abs_dot_le_len c _

end UndergradKB.Calculus
