import UndergradKB.Calculus.LinesPlanes

/-! # Calculus: relative position of lines and of planes; angle between planes

Classification of two lines of space (equal, parallel and distinct, intersecting in one point, skew), of two
planes (parallel or meeting in a line), and the angle between two planes. -/

namespace UndergradKB.Calculus

open Matrix

/-- Two direction vectors are parallel: one is a scalar multiple of the other. -/
def Par (a b : Fin 3 → ℝ) : Prop := ∃ c : ℝ, a = c • b

lemma len_zero : len (0 : Fin 3 → ℝ) = 0 := len_eq_zero.2 rfl

/-- For `b ≠ 0`, `a × b = 0` exactly when `a` is a scalar multiple of `b`. -/
lemma cross_eq_zero_iff_par {a b : Fin 3 → ℝ} (hb : b ≠ 0) : a ⨯₃ b = 0 ↔ Par a b := by
  constructor
  · intro h
    have hl := len_pos hb
    have hbb : b ⬝ᵥ b ≠ 0 := fun h0 => hb (dotProduct_self_eq_zero.1 h0)
    refine ⟨(a ⬝ᵥ b) / (b ⬝ᵥ b), ?_⟩
    have h1 := len_sub_smul_sq a b ((a ⬝ᵥ b) / (b ⬝ᵥ b))
    have h2 : a ⬝ᵥ b - (a ⬝ᵥ b) / (b ⬝ᵥ b) * (b ⬝ᵥ b) = 0 := by field_simp; ring
    have h3 : (len (a - ((a ⬝ᵥ b) / (b ⬝ᵥ b)) • b) * len b) ^ 2 = 0 := by
      rw [h1, h, h2, len_zero]; norm_num
    have h4 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact sub_eq_zero.1 (len_eq_zero.1 h5)
    · exact absurd h5 hl.ne'
  · rintro ⟨c, rfl⟩
    simp [map_smul, cross_self]

/-- Lines of the classification: equal. -/
def LinesEqual (P a Q b : Fin 3 → ℝ) : Prop := line P a = line Q b
/-- Lines of the classification: parallel directions and no common point (so distinct). -/
def LinesParallelDistinct (P a Q b : Fin 3 → ℝ) : Prop :=
  Par a b ∧ Disjoint (line P a) (line Q b)
/-- Lines of the classification: non-parallel directions meeting in exactly one point. -/
def LinesIntersecting (P a Q b : Fin 3 → ℝ) : Prop :=
  ¬ Par a b ∧ ∃! x, x ∈ line P a ∧ x ∈ line Q b
/-- Skew lines: non-parallel directions and no common point. -/
def LinesSkew (P a Q b : Fin 3 → ℝ) : Prop :=
  ¬ Par a b ∧ Disjoint (line P a) (line Q b)

lemma mem_line_iff (P v x : Fin 3 → ℝ) : x ∈ line P v ↔ ∃ t : ℝ, x = P + t • v := Iff.rfl

lemma meet_unique {P Q a b : Fin 3 → ℝ} (hab : a ⨯₃ b ≠ 0) {x y : Fin 3 → ℝ}
    (hx : x ∈ line P a ∧ x ∈ line Q b) (hy : y ∈ line P a ∧ y ∈ line Q b) : x = y := by
  obtain ⟨⟨s1, h1⟩, ⟨t1, h1'⟩⟩ := hx
  obtain ⟨⟨s2, h2⟩, ⟨t2, h2'⟩⟩ := hy
  have e : (s1 - s2) • a = (t1 - t2) • b := by
    have : P + s1 • a = Q + t1 • b := h1.symm.trans h1'
    have this2 : P + s2 • a = Q + t2 • b := h2.symm.trans h2'
    rw [sub_smul, sub_smul]
    linear_combination (exp := 1) this - this2
  have e2 : ((s1 - s2) • a) ⨯₃ b = ((t1 - t2) • b) ⨯₃ b := by rw [e]
  simp only [map_smul, LinearMap.smul_apply, cross_self, smul_zero] at e2
  have : s1 - s2 = 0 := by
    rcases smul_eq_zero.1 e2 with h | h
    · exact h
    · exact absurd h hab
  have : s1 = s2 := sub_eq_zero.1 this
  rw [h1, h2, this]

lemma meet_imp_det {P Q a b x : Fin 3 → ℝ} (hx : x ∈ line P a ∧ x ∈ line Q b) :
    (a ⨯₃ b) ⬝ᵥ (Q - P) = 0 := by
  obtain ⟨⟨s, h1⟩, ⟨t, h1'⟩⟩ := hx
  have e : Q - P = s • a - t • b := by
    have : P + s • a = Q + t • b := h1.symm.trans h1'
    linear_combination (exp := 1) -this
  rw [e, dotProduct_sub, dotProduct_smul, dotProduct_smul]
  have h1 : (a ⨯₃ b) ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact dot_self_cross a b
  have h2 : (a ⨯₃ b) ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact dot_cross_self a b
  rw [h1, h2]; simp

lemma meet_of_det {P Q a b : Fin 3 → ℝ} (hab : a ⨯₃ b ≠ 0) (h : (a ⨯₃ b) ⬝ᵥ (Q - P) = 0) :
    ∃ x, x ∈ line P a ∧ x ∈ line Q b := by
  have hD : (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) ≠ 0 := fun h0 => hab (dotProduct_self_eq_zero.1 h0)
  have hcr := cramer_cross a b (Q - P)
  have hz : (Q - P) ⬝ᵥ (a ⨯₃ b) = 0 := by rw [dotProduct_comm]; exact h
  rw [hz, zero_smul, add_zero] at hcr
  set D := (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b)
  set A := (Q - P) ⬝ᵥ (b ⨯₃ (a ⨯₃ b))
  set B := (Q - P) ⬝ᵥ ((a ⨯₃ b) ⨯₃ a)
  have hw : Q - P = (D⁻¹ * A) • a + (D⁻¹ * B) • b := by
    have h1 := congrArg (fun z => D⁻¹ • z) hcr
    simp only [smul_smul, inv_mul_cancel₀ hD, one_smul, smul_add] at h1
    rw [h1]
  refine ⟨P + (D⁻¹ * A) • a, ⟨_, rfl⟩, ⟨-(D⁻¹ * B), ?_⟩⟩
  rw [neg_smul]
  linear_combination (exp := 1) -hw

lemma line_eq_of_meet_par {P Q a b : Fin 3 → ℝ} {k : ℝ} (hk : k ≠ 0) (hak : a = k • b)
    (hm : ∃ x, x ∈ line P a ∧ x ∈ line Q b) : line P a = line Q b := by
  obtain ⟨x, ⟨s, h1⟩, ⟨t, h1'⟩⟩ := hm
  have hP : P = Q + t • b - s • a := by
    have : P + s • a = Q + t • b := h1.symm.trans h1'
    rw [← this]; abel
  subst hak
  ext y
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨t - s * k + r * k, ?_⟩
    rw [hP]; module
  · rintro ⟨u, rfl⟩
    refine ⟨(u - t) / k + s, ?_⟩
    rw [hP]
    match_scalars
    · ring
    · field_simp
      ring

/-- OpenStax Calculus 3:§2.5 text (skew lines and relationships between lines), p. 182 (CA-463):
two lines of space with nonzero directions are always in exactly one of four relations: equal;
parallel directions and no common point; non-parallel directions meeting in exactly one point; skew
(non-parallel directions and no common point). -/
@[kb "openstaxcalculus2016" "3:§2.5 text (skew lines and relationships between lines), p. 182"]
theorem lines_classification (P Q a b : Fin 3 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinesEqual P a Q b ∨ LinesParallelDistinct P a Q b ∨ LinesIntersecting P a Q b ∨
      LinesSkew P a Q b := by
  by_cases hpar : Par a b
  · by_cases hm : ∃ x, x ∈ line P a ∧ x ∈ line Q b
    · obtain ⟨k, hk⟩ := hpar
      have hk0 : k ≠ 0 := by rintro rfl; exact ha (by simpa using hk)
      exact Or.inl (line_eq_of_meet_par hk0 hk hm)
    · refine Or.inr (Or.inl ⟨hpar, Set.disjoint_left.2 fun x hx hx' => hm ⟨x, hx, hx'⟩⟩)
  · have hab : a ⨯₃ b ≠ 0 := fun h => hpar ((cross_eq_zero_iff_par hb).1 h)
    by_cases hm : ∃ x, x ∈ line P a ∧ x ∈ line Q b
    · obtain ⟨x, hx⟩ := hm
      exact Or.inr (Or.inr (Or.inl ⟨hpar, x, hx, fun y hy => (meet_unique hab hy hx)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hpar, Set.disjoint_left.2 fun x hx hx' => hm ⟨x, hx, hx'⟩⟩))

/-- OpenStax Calculus 3:§2.5 text (skew lines), p. 182 (CA-463): the four relations are pairwise
exclusive (for nonzero directions). -/
@[kb "openstaxcalculus2016" "3:§2.5 text (skew lines and relationships between lines), p. 182"]
theorem lines_classification_exclusive (P Q a b : Fin 3 → ℝ) :
    ¬ (LinesEqual P a Q b ∧ LinesParallelDistinct P a Q b) ∧
    ¬ (LinesEqual P a Q b ∧ LinesIntersecting P a Q b) ∧
    ¬ (LinesEqual P a Q b ∧ LinesSkew P a Q b) ∧
    ¬ (LinesParallelDistinct P a Q b ∧ LinesIntersecting P a Q b) ∧
    ¬ (LinesParallelDistinct P a Q b ∧ LinesSkew P a Q b) ∧
    ¬ (LinesIntersecting P a Q b ∧ LinesSkew P a Q b) := by
  have heq : LinesEqual P a Q b → Par a b ∧ ¬ Disjoint (line P a) (line Q b) := by
    intro h
    have hP : P ∈ line Q b := h ▸ ⟨0, by simp⟩
    have hPa : P + a ∈ line Q b := h ▸ ⟨1, by simp⟩
    refine ⟨?_, fun hd => Set.disjoint_left.1 hd ⟨0, by simp⟩ hP⟩
    obtain ⟨s, hs⟩ := hP
    obtain ⟨t, ht⟩ := hPa
    refine ⟨t - s, ?_⟩
    have : a = (Q + t • b) - (Q + s • b) := by rw [← ht, ← hs]; abel
    rw [this]; module
  refine ⟨fun ⟨h, h2⟩ => (heq h).2 h2.2, fun ⟨h, h3⟩ => h3.1 (heq h).1,
    fun ⟨h, h4⟩ => h4.1 (heq h).1, fun ⟨h2, h3⟩ => h3.1 h2.1, fun ⟨h2, h4⟩ => h4.1 h2.1,
    fun ⟨h3, h4⟩ => ?_⟩
  obtain ⟨x, hx, _⟩ := h3.2
  exact Set.disjoint_left.1 h4.2 hx.1 hx.2

lemma par_imp_cross_zero {a b : Fin 3 → ℝ} (h : Par a b) : a ⨯₃ b = 0 := by
  obtain ⟨c, rfl⟩ := h
  simp [map_smul, cross_self]

/-- OpenStax Calculus 3:§2.5 text (skew lines), p. 182 (CA-463): with nonzero direction `b`, the
lines through `P` (direction `a`) and `Q` (direction `b`) are skew exactly when the triple product
`(a × b) · PQ` is nonzero. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (skew lines and relationships between lines), p. 182"]
theorem lines_skew_iff (P Q a b : Fin 3 → ℝ) (hb : b ≠ 0) :
    LinesSkew P a Q b ↔ (a ⨯₃ b) ⬝ᵥ (Q - P) ≠ 0 := by
  constructor
  · rintro ⟨hp, hd⟩ h0
    have hab : a ⨯₃ b ≠ 0 := fun h => hp ((cross_eq_zero_iff_par hb).1 h)
    obtain ⟨x, hx, hx'⟩ := meet_of_det hab h0
    exact Set.disjoint_left.1 hd hx hx'
  · intro hne
    have hab : a ⨯₃ b ≠ 0 := fun h => hne (by rw [h]; simp)
    refine ⟨fun hp => hab (par_imp_cross_zero hp), Set.disjoint_left.2 fun x hx hx' => hne ?_⟩
    exact meet_imp_det ⟨hx, hx'⟩

lemma recip_cross (a b z : Fin 3 → ℝ) :
    ((a ⨯₃ b) ⬝ᵥ (a ⨯₃ b)) • z =
      (z ⬝ᵥ a) • (b ⨯₃ (a ⨯₃ b)) + (z ⬝ᵥ b) • ((a ⨯₃ b) ⨯₃ a) + (z ⬝ᵥ (a ⨯₃ b)) • (a ⨯₃ b) := by
  ext i; fin_cases i <;>
  · simp only [dot_expand, cross_0, cross_1, cross_2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    ring

lemma pf1 (a b : Fin 3 → ℝ) : a ⬝ᵥ (b ⨯₃ (a ⨯₃ b)) = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) := by
  simp only [dot_expand, cross_0, cross_1, cross_2]; ring

lemma pf2 (a b : Fin 3 → ℝ) : a ⬝ᵥ ((a ⨯₃ b) ⨯₃ a) = 0 := dot_cross_self _ _

lemma pf3 (a b : Fin 3 → ℝ) : b ⬝ᵥ (b ⨯₃ (a ⨯₃ b)) = 0 := dot_self_cross _ _

lemma pf4 (a b : Fin 3 → ℝ) : b ⬝ᵥ ((a ⨯₃ b) ⨯₃ a) = (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) := by
  simp only [dot_expand, cross_0, cross_1, cross_2]; ring

/-- OpenStax Calculus 3:§2.5 text (parallel and intersecting planes), p. 189 (CA-466): two distinct
planes `n₁ · x + d₁ = 0`, `n₂ · x + d₂ = 0` (nonzero normals) either have parallel normals and no
common point, or non-parallel normals and meet in a line with direction `n₁ × n₂`. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (parallel and intersecting planes), p. 189"]
theorem planes_parallel_or_line (n₁ n₂ : Fin 3 → ℝ) (d₁ d₂ : ℝ) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0)
    (hne : planeGen n₁ d₁ ≠ planeGen n₂ d₂) :
    (Par n₁ n₂ ∧ Disjoint (planeGen n₁ d₁) (planeGen n₂ d₂)) ∨
    (¬ Par n₁ n₂ ∧ n₁ ⨯₃ n₂ ≠ 0 ∧
      ∃ P, planeGen n₁ d₁ ∩ planeGen n₂ d₂ = line P (n₁ ⨯₃ n₂)) := by
  by_cases hp : Par n₁ n₂
  · left
    refine ⟨hp, Set.disjoint_left.2 fun x hx hx' => hne ?_⟩
    obtain ⟨k, hk⟩ := hp
    have hk0 : k ≠ 0 := by rintro rfl; exact h₁ (by simpa using hk)
    simp only [planeGen, Set.mem_ofPred_eq] at hx hx'
    rw [hk, smul_dotProduct, smul_eq_mul] at hx
    have hd : d₁ = k * d₂ := by linear_combination hx - k * hx'
    ext y
    simp only [planeGen, Set.mem_ofPred_eq, hk, smul_dotProduct, smul_eq_mul, hd]
    constructor
    · intro h
      have : k * (n₂ ⬝ᵥ y + d₂) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hk0
    · intro h
      rw [← mul_add, h, mul_zero]
  · right
    have hc : n₁ ⨯₃ n₂ ≠ 0 := fun h => hp ((cross_eq_zero_iff_par h₂).1 h)
    have hD : (n₁ ⨯₃ n₂) ⬝ᵥ (n₁ ⨯₃ n₂) ≠ 0 := fun h => hc (dotProduct_self_eq_zero.1 h)
    refine ⟨hp, hc, ?_⟩
    set D := (n₁ ⨯₃ n₂) ⬝ᵥ (n₁ ⨯₃ n₂) with hDdef
    refine ⟨(D⁻¹ * -d₁) • (n₂ ⨯₃ (n₁ ⨯₃ n₂)) + (D⁻¹ * -d₂) • ((n₁ ⨯₃ n₂) ⨯₃ n₁), ?_⟩
    have hP1 : n₁ ⬝ᵥ ((D⁻¹ * -d₁) • (n₂ ⨯₃ (n₁ ⨯₃ n₂)) + (D⁻¹ * -d₂) • ((n₁ ⨯₃ n₂) ⨯₃ n₁)) = -d₁ := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, pf1, pf2, smul_eq_mul, smul_eq_mul]
      field_simp; ring
    have hP2 : n₂ ⬝ᵥ ((D⁻¹ * -d₁) • (n₂ ⨯₃ (n₁ ⨯₃ n₂)) + (D⁻¹ * -d₂) • ((n₁ ⨯₃ n₂) ⨯₃ n₁)) = -d₂ := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, pf3, pf4, smul_eq_mul, smul_eq_mul]
      field_simp; ring
    set P := (D⁻¹ * -d₁) • (n₂ ⨯₃ (n₁ ⨯₃ n₂)) + (D⁻¹ * -d₂) • ((n₁ ⨯₃ n₂) ⨯₃ n₁) with hPdef
    have c1 : n₁ ⬝ᵥ (n₁ ⨯₃ n₂) = 0 := dot_self_cross _ _
    have c2 : n₂ ⬝ᵥ (n₁ ⨯₃ n₂) = 0 := dot_cross_self _ _
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      simp only [planeGen, Set.mem_ofPred_eq] at hx1 hx2
      have z1 : (x - P) ⬝ᵥ n₁ = 0 := by rw [dotProduct_comm, dotProduct_sub, hP1]; linarith
      have z2 : (x - P) ⬝ᵥ n₂ = 0 := by rw [dotProduct_comm, dotProduct_sub, hP2]; linarith
      have hr := recip_cross n₁ n₂ (x - P)
      rw [z1, z2, zero_smul, zero_smul, zero_add, zero_add] at hr
      refine ⟨D⁻¹ * ((x - P) ⬝ᵥ (n₁ ⨯₃ n₂)), ?_⟩
      rw [← hDdef] at hr
      have h1 := congrArg (fun z => D⁻¹ • z) hr
      simp only [smul_smul, inv_mul_cancel₀ hD, one_smul] at h1
      rw [← h1]; abel
    · rintro ⟨t, rfl⟩
      constructor
      · simp only [planeGen, Set.mem_ofPred_eq]
        rw [dotProduct_add, dotProduct_smul, hP1, c1]; simp
      · simp only [planeGen, Set.mem_ofPred_eq]
        rw [dotProduct_add, dotProduct_smul, hP2, c2]; simp

/-- The angle `θ ∈ [0, π/2]` between two planes with normals `n₁`, `n₂`:
`cos θ = |n₁ · n₂| / (‖n₁‖‖n₂‖)`. -/
noncomputable def planeAngle (n₁ n₂ : Fin 3 → ℝ) : ℝ :=
  Real.arccos (|n₁ ⬝ᵥ n₂| / (len n₁ * len n₂))

/-- OpenStax Calculus 3:§2.5 text (angle between two planes), p. 190 (CA-467): for nonzero normals the
angle between the planes satisfies `cos θ = |n₁ · n₂| / (‖n₁‖‖n₂‖)`, lies in `[0, π/2]`, and is the
smaller of the two angles `φ`, `π − φ` between the normals; the planes are parallel (`θ = 0`) iff the
normals are parallel, and orthogonal (`θ = π/2`) iff the normals are orthogonal. -/
@[kb "openstaxcalculus2016" "3:§2.5 text (angle between two planes), p. 190"]
theorem planeAngle_spec {n₁ n₂ : Fin 3 → ℝ} (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) :
    Real.cos (planeAngle n₁ n₂) = |n₁ ⬝ᵥ n₂| / (len n₁ * len n₂) ∧
    0 ≤ planeAngle n₁ n₂ ∧ planeAngle n₁ n₂ ≤ Real.pi / 2 ∧
    planeAngle n₁ n₂ = min (vangle n₁ n₂) (Real.pi - vangle n₁ n₂) ∧
    (planeAngle n₁ n₂ = 0 ↔ Par n₁ n₂) ∧
    (planeAngle n₁ n₂ = Real.pi / 2 ↔ n₁ ⬝ᵥ n₂ = 0) := by
  have hl1 := len_pos h₁
  have hl2 := len_pos h₂
  have hp : 0 < len n₁ * len n₂ := mul_pos hl1 hl2
  have hle : |n₁ ⬝ᵥ n₂| / (len n₁ * len n₂) ≤ 1 := by
    rw [div_le_one hp]; exact abs_dot_le_len _ _
  have h0 : 0 ≤ |n₁ ⬝ᵥ n₂| / (len n₁ * len n₂) := by positivity
  have hw := work_eq n₁ n₂
  have hφ0 : 0 ≤ vangle n₁ n₂ := InnerProductGeometry.angle_nonneg _ _
  have hφπ : vangle n₁ n₂ ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
  have habs : |n₁ ⬝ᵥ n₂| / (len n₁ * len n₂) = |Real.cos (vangle n₁ n₂)| := by
    rw [hw, abs_mul, abs_of_pos hp, mul_div_cancel_left₀ _ hp.ne']
  refine ⟨Real.cos_arccos (by linarith) hle, Real.arccos_nonneg _,
    Real.arccos_le_pi_div_two.2 h0, ?_, ?_, ?_⟩
  · unfold planeAngle
    rw [habs]
    rcases le_or_gt 0 (Real.cos (vangle n₁ n₂)) with hc | hc
    · rw [abs_of_nonneg hc, Real.arccos_cos hφ0 hφπ]
      have : vangle n₁ n₂ ≤ Real.pi / 2 := by
        by_contra hgt
        have hgt := not_le.1 hgt
        have := Real.cos_neg_of_pi_div_two_lt_of_lt hgt (by linarith [Real.pi_pos])
        linarith
      rw [min_eq_left (by linarith)]
    · rw [abs_of_neg hc, ← Real.cos_pi_sub, Real.arccos_cos (by linarith) (by linarith)]
      have : Real.pi / 2 < vangle n₁ n₂ := by
        by_contra hle'
        have hle' := not_lt.1 hle'
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hle'
        linarith
      rw [min_eq_right (by linarith)]
  · unfold planeAngle
    rw [Real.arccos_eq_zero, ← cross_eq_zero_iff_par h₂, ← len_eq_zero]
    have hl := (parallelogram_area n₁ n₂).2
    rw [le_div_iff₀ hp, one_mul]
    constructor
    · intro h
      have h2 : (len n₁ * len n₂) ^ 2 ≤ |n₁ ⬝ᵥ n₂| ^ 2 := pow_le_pow_left₀ hp.le h 2
      rw [sq_abs] at h2
      have h3 : len (n₁ ⨯₃ n₂) ^ 2 = 0 :=
        le_antisymm (by nlinarith [sq_nonneg (len (n₁ ⨯₃ n₂))]) (sq_nonneg _)
      exact (pow_eq_zero_iff two_ne_zero).1 h3
    · intro h
      have h3 : len (n₁ ⨯₃ n₂) ^ 2 = 0 := by rw [h]; norm_num
      have : (len n₁ * len n₂) ^ 2 = |n₁ ⬝ᵥ n₂| ^ 2 := by
        rw [sq_abs]; nlinarith
      exact ((sq_eq_sq₀ hp.le (abs_nonneg _)).1 this).le
  · unfold planeAngle
    rw [Real.arccos_eq_pi_div_two, div_eq_zero_iff, abs_eq_zero]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h hp.ne'
    · exact fun h => Or.inl h

end UndergradKB.Calculus
