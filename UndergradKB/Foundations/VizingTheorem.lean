import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import UndergradKB.Foundations.Kempe
import UndergradKB.Foundations.Vizing

/-!
# Foundations: Vizing's theorem and König's edge-colouring theorem

Levin, Theorem 2.5.9 (Vizing): the chromatic index of a (finite simple) graph is `Δ` or `Δ + 1`; the graphs
with `χ' = Δ` are class 1, the others class 2, and bipartite graphs are class 1 (König). Levin states these without
proof; we follow the classical fan argument.

*Vizing.* Colour the edges one at a time with `Δ + 1` colours, so every vertex misses a colour. To colour `x y₀`,
build a maximal fan `y₀, y₁, …, y_k` at `x` (`x y_i` coloured with a colour missing at `y_{i-1}`), let `α` be
missing at `x` and `β` at `y_k`. If `β` is missing at `x`, rotate the fan and use `β`. Otherwise `β` sits on an
edge `x y_l` of the fan, `β` is missing at `y_{l-1}`, and in the Kempe graph of `α, β` the three vertices
`x, y_{l-1}, y_k` have degree at most one, so they are not all in one component. Exchanging `α, β` on the component
of `y_{l-1}` (if it misses `x`) or of `y_k` (otherwise) makes `α` missing at the end of a shorter or the whole fan;
rotate and use `α`.

*König.* With `Δ` colours and `x y` uncoloured, `x` misses some `α` and `y` some `β`. If neither colour can be used
directly, the Kempe chain of `x` for `α, β` does not reach `y`: a path from `x` to `y` in the Kempe graph alternates
colours, starts with `β` and ends with `α`, so has even length, and closing it with the edge `y x` gives an odd closed
walk in a bipartite graph. Exchanging the colours on that chain frees `β` at `x`.
-/

namespace UndergradKB.Foundations

open SimpleGraph

namespace EdgeColoring

variable {V κ : Type*} {G : SimpleGraph V}

/-- Exchanging `a, b` on a Kempe chain that avoids `x` keeps a fan at `x` whose edge colours avoid `b`, when `a` is
missing at `x`. -/
theorem FanChain.kempeSwap [DecidableEq κ] {c : Sym2 V → Option κ} {a b : κ}
    {v₀ x y : V} {l : List V} (hfan : FanChain G c x y l) (ha : Missing G c x a)
    (hxK : ¬ (kempeGraph (G := G) c a b).Reachable v₀ x) (hb : ∀ w ∈ l, c s(x, w) ≠ some b) :
    FanChain G (EdgeColoring.kempeSwap G c a b v₀) x y l := by
  refine hfan.imp (fun w _ => kempeSwap_of_not_mem hxK) ?_
  intro w hw d hd e he
  have hda : d ≠ a := by rintro rfl; exact ha (hfan.adj w hw) hd
  have hdb : d ≠ b := by rintro rfl; exact hb w hw hd
  exact (kempeSwap_eq_some_of_ne hda hdb e).1 he

/-- **Vizing's recolouring step.** If every vertex misses some colour, an uncoloured edge can be coloured while every
coloured edge stays coloured. -/
theorem vizing_step [Fintype V] [DecidableEq V] [DecidableEq κ] {c : Sym2 V → Option κ}
    (hc : IsProperPartial G c) (hmiss : ∀ v, ∃ a, Missing G c v a) {x y₀ : V} (hxy : G.Adj x y₀)
    (hnone : c s(x, y₀) = none) :
    ∃ c' : Sym2 V → Option κ, IsProperPartial G c' ∧ (∀ e, c e ≠ none → c' e ≠ none) ∧ c' s(x, y₀) ≠ none := by
  classical
  obtain ⟨α, hα⟩ := hmiss x
  suffices H : ∀ n (l : List V), FanChain G c x y₀ l → (y₀ :: l).Nodup → l.length + n = Fintype.card V →
      ∃ c' : Sym2 V → Option κ, IsProperPartial G c' ∧ (∀ e, c e ≠ none → c' e ≠ none) ∧
        c' s(x, y₀) ≠ none from
    H (Fintype.card V) [] trivial (List.nodup_singleton _) (by simp)
  intro n
  induction n with
  | zero =>
    intro l _ hnd hlen
    have := hnd.length_le_card
    simp only [List.length_cons] at this
    omega
  | succ n ih =>
    intro l hfan hnd hlen
    obtain ⟨β, hβ⟩ := hmiss (fanLast y₀ l)
    by_cases hβx : Missing G c x β
    · exact exists_extend_of_fan l y₀ c hc hxy hnone hfan hnd β hβx hβ
    obtain ⟨z, hxz, hz⟩ : ∃ z, G.Adj x z ∧ c s(x, z) = some β := by
      by_contra hcon
      exact hβx fun w hw h => hcon ⟨w, hw, h⟩
    by_cases hzl : z ∈ y₀ :: l
    swap
    · -- extend the fan by `z`
      refine ih (l ++ [z]) ?_ ?_ (by simp; omega)
      · rw [FanChain.append_iff]
        exact ⟨hfan, hxz, ⟨β, hz, hβ⟩, trivial⟩
      · rw [← List.cons_append, List.nodup_append]
        refine ⟨hnd, List.nodup_singleton _, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst hb; subst hab; exact hzl ha
    have hz₀ : z ≠ y₀ := by rintro rfl; rw [hnone] at hz; simp at hz
    have hzl' : z ∈ l := (List.mem_cons.1 hzl).resolve_left hz₀
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hzl'
    obtain ⟨hfanA, -, ⟨d, hd, hpd⟩, hfanB⟩ := (FanChain.append_iff y₀ A (z :: B)).1 hfan
    have hdβ : d = β := Option.some_injective _ (hd.symm.trans hz)
    rw [hdβ] at hpd
    set p := fanLast y₀ A with hp
    set y := fanLast y₀ (A ++ z :: B) with hy
    have hylast : y = fanLast z B := by rw [hy, fanLast_append]; rfl
    have hyz : y ≠ z := by
      intro h
      rw [h] at hβ
      exact hβ hxz.symm (by rw [Sym2.eq_swap]; exact hz)
    have hB : B ≠ [] := by rintro rfl; exact hyz hylast
    have hyB : y ∈ B := hylast ▸ fanLast_mem_of_ne_nil z hB
    have hpA : p ∈ y₀ :: A := fanLast_mem y₀ A
    have hnd' : ((y₀ :: A) ++ (z :: B)).Nodup := by simpa using hnd
    obtain ⟨hndA, hndB, hdisj⟩ := List.nodup_append.1 hnd'
    have hpy : p ≠ y := hdisj p hpA y (List.mem_cons_of_mem _ hyB)
    have hzA : z ∉ y₀ :: A := fun h => hdisj z h z (List.mem_cons_self ..) rfl
    have hzB : z ∉ B := (List.nodup_cons.1 hndB).1
    have hadjA : ∀ w ∈ y₀ :: A, G.Adj x w := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hxy
      · exact hfanA.adj w hw
    have hxp : x ≠ p := G.ne_of_adj (hadjA p hpA)
    have hxy' : x ≠ y := G.ne_of_adj (hfanB.adj y hyB)
    -- edges of the fan other than `x z` do not carry `β`
    have hbA : ∀ w ∈ A, c s(x, w) ≠ some β := by
      intro w hw h
      exact hzA (hc.ne_of_ne (hfanA.adj w hw) hxz h hz ▸ List.mem_cons_of_mem _ hw)
    have hbB : ∀ w ∈ B, c s(x, w) ≠ some β := by
      intro w hw h
      exact hzB (hc.ne_of_ne (hfanB.adj w hw) hxz h hz ▸ hw)
    -- the Kempe graph of `α, β`
    set H := kempeGraph (G := G) c α β with hH
    have h2 : ∀ v, H.degree v ≤ 2 := fun v => kempeGraph_degree_le_two hc v
    have hdx : H.degree x ≤ 1 := kempeGraph_degree_le_one_left hc hα
    have hdp : H.degree p ≤ 1 := kempeGraph_degree_le_one hc hpd
    have hdy : H.degree y ≤ 1 := kempeGraph_degree_le_one hc hβ
    have hnoneSwap : ∀ v₀, EdgeColoring.kempeSwap G c α β v₀ s(x, y₀) = none := fun v₀ =>
      (kempeSwap_eq_none_iff _).2 hnone
    have hmonoSwap : ∀ v₀ e, c e ≠ none → EdgeColoring.kempeSwap G c α β v₀ e ≠ none :=
      fun v₀ e he h => he ((kempeSwap_eq_none_iff e).1 h)
    by_cases hxpR : H.Reachable x p
    · -- case B: exchange on the chain of `y`, which avoids `x` and `p`
      have hxyR : ¬ H.Reachable x y := fun h => not_three_ends H h2 hxp hxy' hpy hdx hdp hdy hxpR h
      have hxK : ¬ H.Reachable y x := fun h => hxyR h.symm
      have hpK : ¬ H.Reachable y p := fun h => hxyR (hxpR.trans h.symm)
      set c' := EdgeColoring.kempeSwap G c α β y
      have hfan' : FanChain G c' x y₀ (A ++ z :: B) := by
        rw [FanChain.append_iff]
        refine ⟨hfanA.kempeSwap hα hxK hbA, hxz, ⟨β, ?_, ?_⟩, hfanB.kempeSwap hα hxK hbB⟩
        · exact (kempeSwap_of_not_mem hxK).trans hz
        · exact missing_kempeSwap_of_not_mem hpK hpd
      have hαy : Missing G c' y α := by
        have := missing_kempeSwap_of_mem (G := G) (a := α) (b := β) (Reachable.refl y) hβ
        rwa [Equiv.swap_apply_right] at this
      obtain ⟨c'', hc'', hmono, hxy''⟩ := exists_extend_of_fan (A ++ z :: B) y₀ c' hc.kempeSwap hxy
        (hnoneSwap y) hfan' hnd α (missing_kempeSwap_of_not_mem hxK hα) hαy
      exact ⟨c'', hc'', fun e he => hmono e (hmonoSwap y e he), hxy''⟩
    · -- case A: exchange on the chain of `p`, which avoids `x`
      have hxK : ¬ H.Reachable p x := fun h => hxpR h.symm
      set c' := EdgeColoring.kempeSwap G c α β p
      have hαp : Missing G c' p α := by
        have := missing_kempeSwap_of_mem (G := G) (a := α) (b := β) (Reachable.refl p) hpd
        rwa [Equiv.swap_apply_right] at this
      obtain ⟨c'', hc'', hmono, hxy''⟩ := exists_extend_of_fan A y₀ c' hc.kempeSwap hxy
        (hnoneSwap p) (hfanA.kempeSwap hα hxK hbA) hndA α (missing_kempeSwap_of_not_mem hxK hα) hαp
      exact ⟨c'', hc'', fun e he => hmono e (hmonoSwap p e he), hxy''⟩

/-- Colouring the edges one at a time: if every uncoloured edge can be coloured while keeping the coloured ones,
some proper colouring colours every edge. -/
theorem exists_total_of_step [DecidableEq V] [Fintype G.edgeSet]
    (P : (Sym2 V → Option κ) → Prop) (hP : P (fun _ => none))
    (hstep : ∀ c, P c → ∀ x y, G.Adj x y → c s(x, y) = none →
      ∃ c', P c' ∧ (∀ e, c e ≠ none → c' e ≠ none) ∧ c' s(x, y) ≠ none) :
    ∃ c, P c ∧ ∀ e ∈ G.edgeSet, c e ≠ none := by
  classical
  suffices h : ∀ S : Finset (Sym2 V), ∃ c, P c ∧ ∀ e ∈ S, e ∈ G.edgeSet → c e ≠ none by
    obtain ⟨c, hc, hS⟩ := h G.edgeFinset
    exact ⟨c, hc, fun e he => hS e (by simpa using he) he⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨_, hP, by simp⟩
  | insert e S _ ih =>
    obtain ⟨c, hc, hS⟩ := ih
    by_cases he : e ∈ G.edgeSet ∧ c e = none
    · obtain ⟨heG, hce⟩ := he
      induction e using Sym2.ind with
      | _ x y =>
      obtain ⟨c', hc', hmono, hxy⟩ := hstep c hc x y heG hce
      refine ⟨c', hc', fun e' he' he'G => ?_⟩
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact hxy
      · exact hmono e' (hS e' he' he'G)
    · refine ⟨c, hc, fun e' he' he'G => ?_⟩
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact fun h => he ⟨he'G, h⟩
      · exact hS e' he' he'G

/-- A proper partial colouring with colours in `Fin n` that colours every edge is a proper edge colouring. -/
theorem edgeColorable_of_total {n : ℕ} {c : Sym2 V → Option (Fin n)} (hc : IsProperPartial G c)
    (htot : ∀ e ∈ G.edgeSet, c e ≠ none) : EdgeColorable G n := by
  refine ⟨fun e => (c e.1).get (Option.isSome_iff_ne_none.2 (htot e.1 e.2)), ?_⟩
  intro e e' hne ⟨v, hv, hv'⟩ heq
  dsimp only at heq
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hv
  obtain ⟨w', hw'⟩ := Sym2.mem_iff_exists.1 hv'
  have hadj : G.Adj v w := by have := e.2; rw [hw] at this; exact this
  have hadj' : G.Adj v w' := by have := e'.2; rw [hw'] at this; exact this
  have hww : w ≠ w' := by
    rintro rfl
    exact hne (Subtype.ext (hw.trans hw'.symm))
  have h1 : c s(v, w) = some ((c e.1).get (Option.isSome_iff_ne_none.2 (htot e.1 e.2))) := by
    rw [Option.some_get, hw]
  have h2 : c s(v, w') = some ((c e.1).get (Option.isSome_iff_ne_none.2 (htot e.1 e.2))) := by
    rw [heq, Option.some_get, hw']
  exact hc hadj hadj' hww _ h1 h2

/-- With `Δ + 1` colours (or more) every finite graph has a proper edge colouring. -/
theorem edgeColorable_maxDegree_add_one [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    EdgeColorable G (G.maxDegree + 1) := by
  classical
  obtain ⟨c, hc, htot⟩ := exists_total_of_step (G := G) (κ := Fin (G.maxDegree + 1))
    (IsProperPartial G) isProperPartial_none (by
      intro c hc x y hxy hnone
      refine vizing_step hc (fun v => exists_missing c v ?_) hxy hnone
      rw [Fintype.card_fin]
      exact Nat.lt_succ_of_le (G.degree_le_maxDegree v))
  exact edgeColorable_of_total hc htot

/-! ### König: bipartite graphs -/

/-- Colours alternate along a path of a Kempe graph: if the edge `u' u` before the path has colour `d` (one of the
two colours, `d'` the other), the last edge into the end of the path has colour `d` after an even number of steps
and `d'` after an odd number. -/
theorem kempe_path_alternates {c : Sym2 V → Option κ} (hc : IsProperPartial G c) {a b : κ} :
    ∀ {u v : V} (q : (kempeGraph (G := G) c a b).Walk u v), q.IsPath → ∀ (u' : V) (d d' : κ),
      (d = a ∧ d' = b ∨ d = b ∧ d' = a) → (kempeGraph (G := G) c a b).Adj u' u → u' ∉ q.support →
      c s(u', u) = some d →
      ∃ v', (kempeGraph (G := G) c a b).Adj v' v ∧ c s(v', v) = some (if Even q.length then d else d') := by
  intro u v q
  induction q with
  | nil =>
    intro _ u' d d' _ hadj _ hcol
    exact ⟨u', hadj, by simpa using hcol⟩
  | @cons u w v h q ih =>
    intro hq u' d d' hdd hadj hu' hcol
    rw [Walk.cons_isPath_iff] at hq
    rw [Walk.support_cons, List.mem_cons, not_or] at hu'
    have hw : w ∈ q.support := q.start_mem_support
    have hu'w : u' ≠ w := fun h => hu'.2 (h ▸ hw)
    have hcol' : c s(u, w) = some d' := by
      have hcu : c s(u, u') = some d := by rw [Sym2.eq_swap]; exact hcol
      rcases h.2 with h1 | h1 <;> rcases hdd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hc.ne_of_ne hadj.1.symm h.1 hcu h1) hu'w
      · exact h1
      · exact h1
      · exact absurd (hc.ne_of_ne hadj.1.symm h.1 hcu h1) hu'w
    obtain ⟨v', hv', hcv⟩ := ih hq.1 u d' d (by tauto) h hq.2 hcol'
    refine ⟨v', hv', ?_⟩
    rw [hcv, Walk.length_cons]
    by_cases he : Even q.length
    · have : ¬ Even (q.length + 1) := by rw [Nat.even_add_one]; exact not_not.2 he
      simp [he, this]
    · have : Even (q.length + 1) := by rw [Nat.even_add_one]; exact he
      simp [he, this]

/-- König's recolouring step: in a bipartite graph, an uncoloured edge can be coloured with `Δ` colours. -/
theorem konig_step [Fintype V] [DecidableEq V] [DecidableEq κ] [Fintype κ] (hG : G.IsBipartite)
    [DecidableRel G.Adj] (hκ : G.maxDegree ≤ Fintype.card κ) {c : Sym2 V → Option κ}
    (hc : IsProperPartial G c) {x y : V} (hxy : G.Adj x y) (hnone : c s(x, y) = none) :
    ∃ c' : Sym2 V → Option κ, IsProperPartial G c' ∧ (∀ e, c e ≠ none → c' e ≠ none) ∧ c' s(x, y) ≠ none := by
  classical
  have hmono_update : ∀ (c₀ : Sym2 V → Option κ) (g : κ) e, c₀ e ≠ none →
      Function.update c₀ s(x, y) (some g) e ≠ none := by
    intro c₀ g e he
    rw [Function.update_apply]; split_ifs <;> simp_all
  obtain ⟨α, hα⟩ := exists_missing_of_none c x hxy hnone ((G.degree_le_maxDegree x).trans hκ)
  obtain ⟨β, hβ⟩ := exists_missing_of_none c y hxy.symm (by rw [Sym2.eq_swap]; exact hnone)
    ((G.degree_le_maxDegree y).trans hκ)
  by_cases hyα : Missing G c y α
  · exact ⟨_, hc.update hα hyα, fun e he => hmono_update c α e he, by simp⟩
  by_cases hxβ : Missing G c x β
  · exact ⟨_, hc.update hxβ hβ, fun e he => hmono_update c β e he, by simp⟩
  set H := kempeGraph (G := G) c α β with hH
  -- the Kempe chain of `x` does not reach `y`
  have hxyR : ¬ H.Reachable x y := by
    rintro ⟨p⟩
    have hq := p.bypass_isPath
    generalize p.bypass = q at hq
    cases q with
    | nil => exact G.ne_of_adj hxy rfl
    | @cons _ w _ h q =>
      rw [Walk.cons_isPath_iff] at hq
      have hxw : c s(x, w) = some β := h.2.resolve_left (hα h.1)
      obtain ⟨v', hv', hcv⟩ := kempe_path_alternates hc q hq.1 x β α (Or.inr ⟨rfl, rfl⟩) h hq.2 hxw
      have hodd : ¬ Even q.length := by
        intro he
        simp only [he, ↓reduceIte] at hcv
        exact hβ hv'.1.symm (by rw [Sym2.eq_swap]; exact hcv)
      -- close the path with the edge `y x`: an odd closed walk
      have hle : H ≤ G := fun _ _ h => h.1
      have := (two_colorable_iff_forall_loop_even.1 hG) x
        (((Walk.cons h q).mapLe hle).concat hxy.symm)
      rw [Walk.length_concat, Walk.length_mapLe, Walk.length_cons] at this
      exact hodd (by
        rcases this with ⟨k, hk⟩
        rcases Nat.even_or_odd q.length with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact ⟨m, hm⟩
        · omega)
  set c' := EdgeColoring.kempeSwap G c α β x
  have hxβ' : Missing G c' x β := by
    have := missing_kempeSwap_of_mem (G := G) (a := α) (b := β) (Reachable.refl x) hα
    rwa [Equiv.swap_apply_left] at this
  have hyβ' : Missing G c' y β := missing_kempeSwap_of_not_mem hxyR hβ
  refine ⟨Function.update c' s(x, y) (some β), hc.kempeSwap.update hxβ' hyβ', ?_, by simp⟩
  intro e he
  exact hmono_update c' β e (fun h => he ((kempeSwap_eq_none_iff e).1 h))

/-- A finite bipartite graph has a proper edge colouring with `Δ` colours. -/
theorem edgeColorable_maxDegree_of_isBipartite [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsBipartite) : EdgeColorable G G.maxDegree := by
  classical
  obtain ⟨c, hc, htot⟩ := exists_total_of_step (G := G) (κ := Fin G.maxDegree)
    (IsProperPartial G) isProperPartial_none (by
      intro c hc x y hxy hnone
      exact konig_step hG (by rw [Fintype.card_fin]) hc hxy hnone)
  exact edgeColorable_of_total hc htot

end EdgeColoring

/-! ### Headline statements in Levin's terms -/

/-- `χ'(G) ≤ n` as soon as `G` has a proper edge colouring with `n` colours. -/
theorem chromaticIndex_le_of_edgeColorable {V : Type*} (G : SimpleGraph V) {n : ℕ} (h : EdgeColorable G n) :
    chromaticIndex G ≤ n :=
  iInf_le_of_le ⟨n, h⟩ le_rfl

/-- FO-359. **Vizing's theorem** (Levin Thm 2.5.9): the chromatic index of a finite graph is `Δ(G)` or
`Δ(G) + 1`. -/
@[kb "levin2025" "Thm 2.5.9, p. 178"]
theorem levin_thm_2_5_9_vizing {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticIndex G = G.maxDegree ∨ chromaticIndex G = G.maxDegree + 1 := by
  have hlo := levin_s2_5_maxDegree_le_chromaticIndex G
  have hhi : chromaticIndex G ≤ ((G.maxDegree + 1 : ℕ) : ℕ∞) :=
    chromaticIndex_le_of_edgeColorable G (EdgeColoring.edgeColorable_maxDegree_add_one G)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, chromaticIndex G = m :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hhi) |>.imp fun _ h => h.symm
  rw [hm] at hlo hhi ⊢
  norm_cast at hlo hhi ⊢
  omega

/-- FO-360. A graph is *class 1* when its chromatic index equals its maximum degree. -/
def IsClassOne {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  chromaticIndex G = G.maxDegree

/-- FO-360. A graph is *class 2* when its chromatic index is its maximum degree plus one. -/
def IsClassTwo {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  chromaticIndex G = G.maxDegree + 1

/-- FO-360. By Vizing's theorem every finite graph is of class 1 or of class 2, and not both. -/
@[kb "levin2025" "Text §2.5, p. 178"]
theorem levin_s2_5_class_one_or_two {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (IsClassOne G ∨ IsClassTwo G) ∧ ¬ (IsClassOne G ∧ IsClassTwo G) := by
  refine ⟨levin_thm_2_5_9_vizing G, fun ⟨h1, h2⟩ => ?_⟩
  unfold IsClassOne at h1
  unfold IsClassTwo at h2
  rw [h1] at h2
  norm_cast at h2
  omega

/-- FO-360. **König's edge-colouring theorem** (quoted in Levin §2.5): a finite bipartite graph is of class 1,
`χ'(G) = Δ(G)`. -/
@[kb "levin2025" "Text §2.5, p. 178"]
theorem levin_s2_5_bipartite_class_one {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsBipartite) : IsClassOne G :=
  le_antisymm
    (chromaticIndex_le_of_edgeColorable G (EdgeColoring.edgeColorable_maxDegree_of_isBipartite G hG))
    (levin_s2_5_maxDegree_le_chromaticIndex G)

end UndergradKB.Foundations
