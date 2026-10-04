import CurveComplexGenusTwo.Topology.FiniteArcPositionActual.SourceFiniteArcPositionFullAssemblyCandidate
import CurveComplexGenusTwo.CWHurewicz.SingularNullhomotopyHeaders
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Subpath
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.CWHurewicz.SmallSingularChainsLocal

namespace CurveComplexGenusTwo.SourceTopology

/-- A serial relation on a nonempty finite set contains a vertex-simple directed cycle. -/
theorem finite_serial_relation_simple_cycle
    {V : Type*} [Fintype V] [Nonempty V] (R : V → V → Prop)
    (hR : ∀ v, ∃ w, R v w) :
    ∃ (n : ℕ) (hn : 0 < n) (z : Fin (n + 1) → V),
      z 0 = z (Fin.last n) ∧
      (∀ k : Fin n, R (z k.castSucc) (z k.succ)) ∧
      Function.Injective (fun k : Fin n => z k.castSucc) := by
  classical
  let f : V → V := fun v => Classical.choose (hR v)
  have hf (v : V) : R v (f v) := Classical.choose_spec (hR v)
  have shift {i j : ℕ} (hij : i ≤ j) (v : V) :
      f^[j - i] (f^[i] v) = f^[j] v := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]
  have hp : ∃ n : ℕ, 0 < n ∧ ∃ v : V, f^[n] v = v := by
    let v : V := Classical.choice inferInstance
    let q : Fin (Fintype.card V + 1) → V := fun i => f^[i.val] v
    obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt q (by simp)
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hij | hji
    · refine ⟨j.val - i.val, by omega, f^[i.val] v, ?_⟩
      rw [shift (Nat.le_of_lt hij)]
      exact heq.symm
    · refine ⟨i.val - j.val, by omega, f^[j.val] v, ?_⟩
      rw [shift (Nat.le_of_lt hji)]
      exact heq
  let n := Nat.find hp
  obtain ⟨hn, v, hv⟩ := Nat.find_spec hp
  let z : Fin (n + 1) → V := fun i => f^[i.val] v
  refine ⟨n, hn, z, ?_, ?_, ?_⟩
  · simpa [z] using hv.symm
  · intro k
    change R (f^[k.val] v) (f^[k.val + 1] v)
    rw [Function.iterate_succ_apply']
    exact hf _
  · intro i j heq
    by_contra hne
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hcycle {a b : Fin n} (hab : a.val < b.val)
        (he : f^[a.val] v = f^[b.val] v) : False := by
      have hsmall : 0 < b.val - a.val ∧
          ∃ w : V, f^[b.val - a.val] w = w := by
        refine ⟨by omega, f^[a.val] v, ?_⟩
        rw [shift (Nat.le_of_lt hab)]
        exact he.symm
      have hminimal := Nat.find_min' hp hsmall
      have hb := b.isLt
      change n ≤ b.val - a.val at hminimal
      omega
    rcases lt_or_gt_of_ne hval with hij | hji
    · exact hcycle hij heq
    · exact hcycle hji heq.symm

/-- Positive flow entering a vertex of a balanced finite graph has a positive outgoing edge. -/
theorem balanced_positive_edge_successor
    {V E : Type*} [DecidableEq V] [Fintype E] (src dst : E → V) (c : E → ℕ)
    (hbal : ∀ v, (∑ e, if src e = v then c e else 0) =
      ∑ e, if dst e = v then c e else 0)
    (e : E) (he : 0 < c e) :
    ∃ e' : E, src e' = dst e ∧ 0 < c e' := by
  classical
  have hle : c e ≤ ∑ e', if dst e' = dst e then c e' else 0 := by
    simpa using (Finset.single_le_sum
      (fun e' (_ : e' ∈ Finset.univ) => Nat.zero_le (if dst e' = dst e then c e' else 0))
      (Finset.mem_univ e))
  have hout : 0 < ∑ e', if src e' = dst e then c e' else 0 := by
    rw [hbal]
    exact lt_of_lt_of_le he hle
  obtain ⟨e', _, hpos⟩ := Finset.sum_pos_iff.mp hout
  by_cases hsrc : src e' = dst e
  · exact ⟨e', hsrc, by simpa [hsrc] using hpos⟩
  · simp [hsrc] at hpos

/-- Every nonzero balanced natural flow contains a simple cycle of positive edges. -/
theorem balanced_flow_contains_simple_cycle
    {V E : Type*} [DecidableEq V] [Fintype V] [Fintype E] (src dst : E → V) (c : E → ℕ)
    (hbal : ∀ v, (∑ e, if src e = v then c e else 0) =
      ∑ e, if dst e = v then c e else 0)
    (hpos : ∃ e, 0 < c e) :
    ∃ (n : ℕ) (hn : 0 < n) (z : Fin (n + 1) → V) (edges : Fin n → E),
      z 0 = z (Fin.last n) ∧
      Function.Injective (fun k : Fin n => z k.castSucc) ∧
      (∀ k, src (edges k) = z k.castSucc ∧ dst (edges k) = z k.succ ∧
        0 < c (edges k)) ∧ Function.Injective edges := by
  classical
  let A := {v : V // ∃ e, src e = v ∧ 0 < c e}
  have hA : Nonempty A := by
    obtain ⟨e, he⟩ := hpos
    exact ⟨⟨src e, e, rfl, he⟩⟩
  letI : Nonempty A := hA
  let R : A → A → Prop := fun v w => ∃ e, src e = v.val ∧ dst e = w.val ∧ 0 < c e
  have hR (v : A) : ∃ w, R v w := by
    obtain ⟨e, hsrc, he⟩ := v.property
    obtain ⟨e', hnext, hpos'⟩ := balanced_positive_edge_successor src dst c hbal e he
    refine ⟨⟨dst e, e', hnext, hpos'⟩, e, hsrc, rfl, he⟩
  obtain ⟨n, hn, z, hz, hedges, hinj⟩ := finite_serial_relation_simple_cycle R hR
  choose edges hsrc hdst hpositive using hedges
  refine ⟨n, hn, fun k => (z k).val, edges, congrArg Subtype.val hz, ?_, ?_, ?_⟩
  · intro i j hij
    exact hinj (Subtype.ext hij)
  · exact fun k => ⟨hsrc k, hdst k, hpositive k⟩
  · intro i j hij
    apply hinj
    apply Subtype.ext
    rw [← hsrc i, ← hsrc j, hij]

/-- The incidence multiplicities of a closed finite edge sequence are balanced. -/
theorem closed_edge_sequence_balanced
    {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
    (src dst : E → V) (n : ℕ) (z : Fin (n + 1) → V) (edges : Fin n → E)
    (hz : z 0 = z (Fin.last n))
    (hs : ∀ k, src (edges k) = z k.castSucc)
    (ht : ∀ k, dst (edges k) = z k.succ) :
    ∀ v, (∑ e, if src e = v then (∑ k, if edges k = e then 1 else 0) else 0) =
      ∑ e, if dst e = v then (∑ k, if edges k = e then 1 else 0) else (0 : ℕ) := by
  classical
  intro v
  have distribute (r : E → V) :
      (∑ e, if r e = v then (∑ k, if edges k = e then 1 else 0) else 0) =
      ∑ k, if r (edges k) = v then 1 else (0 : ℕ) := by
    have hd (e : E) :
        (if r e = v then (∑ k, if edges k = e then 1 else 0) else (0 : ℕ)) =
        ∑ k : Fin n, if r e = v then (if edges k = e then 1 else 0) else 0 := by
      by_cases hr : r e = v <;> simp [hr]
    simp_rw [hd]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    have (e : E) :
        (if r e = v then (if edges k = e then 1 else 0) else 0 : ℕ) =
        (if e = edges k then (if r (edges k) = v then 1 else 0) else 0) := by
      by_cases he : e = edges k
      · subst e; simp
      · simp [he, Ne.symm he]
    simp_rw [this]
    simp
  rw [distribute src, distribute dst]
  simp_rw [hs, ht]
  have h₁ := Fin.sum_univ_castSucc (fun k => if z k = v then 1 else (0 : ℕ))
  have h₂ := Fin.sum_univ_succ (fun k => if z k = v then 1 else (0 : ℕ))
  rw [← hz] at h₁
  omega

/-- Subtracting an actual balanced subflow leaves a balanced, strictly smaller flow. -/
theorem balanced_subflow_remainder
    {V E : Type*} [DecidableEq V] [Fintype E] (src dst : E → V)
    (c d : E → ℕ) (hle : ∀ e, d e ≤ c e)
    (hc : ∀ v, (∑ e, if src e = v then c e else 0) =
      ∑ e, if dst e = v then c e else 0)
    (hd : ∀ v, (∑ e, if src e = v then d e else 0) =
      ∑ e, if dst e = v then d e else 0)
    (hpos : ∃ e, 0 < d e) :
    (∀ v, (∑ e, if src e = v then c e - d e else 0) =
      ∑ e, if dst e = v then c e - d e else 0) ∧
    (∑ e : E, (c e - d e)) < ∑ e : E, c e := by
  classical
  have hsplit (e : E) : c e = d e + (c e - d e) := by
    have := hle e
    omega
  have hsplitSum (r : E → V) (v : V) :
      (∑ e, if r e = v then c e else 0) =
      (∑ e, if r e = v then d e else 0) +
      ∑ e, if r e = v then c e - d e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hr : r e = v
    · simpa only [hr, ite_true] using hsplit e
    · simp only [hr, ite_false, zero_add]
  constructor
  · intro v
    have hh := hc v
    rw [hsplitSum src v, hsplitSum dst v, hd v] at hh
    exact Nat.add_left_cancel hh
  · have htotal : (∑ e : E, c e) = (∑ e : E, d e) + ∑ e : E, (c e - d e) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun e _ => hsplit e)
    have hpositive : 0 < ∑ e, d e := by
      obtain ⟨e, he⟩ := hpos
      exact lt_of_lt_of_le he (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e))
    omega

/-- A finite oriented vertex-simple cycle, with its actual edge labels. -/
structure FiniteDirectedSimpleCycle {V E : Type*} (src dst : E → V) where
  length : ℕ
  positive_length : 0 < length
  vertices : Fin (length + 1) → V
  edges : Fin length → E
  closed : vertices 0 = vertices (Fin.last length)
  sources : ∀ k, src (edges k) = vertices k.castSucc
  targets : ∀ k, dst (edges k) = vertices k.succ
  simple : Function.Injective (fun k : Fin length => vertices k.castSucc)
  edge_injective : Function.Injective edges

noncomputable def FiniteDirectedSimpleCycle.multiplicity
    {V E : Type*} {src dst : E → V} (C : FiniteDirectedSimpleCycle src dst)
    (e : E) : ℕ := by
  classical
  exact ∑ k, if C.edges k = e then 1 else 0

theorem FiniteDirectedSimpleCycle.multiplicity_le_flow
    {V E : Type*} {src dst : E → V} (C : FiniteDirectedSimpleCycle src dst)
    (c : E → ℕ) (hpos : ∀ k, 0 < c (C.edges k)) :
    ∀ e, C.multiplicity e ≤ c e := by
  classical
  intro e
  by_cases hex : ∃ k, C.edges k = e
  · obtain ⟨k, hk⟩ := hex
    have hm : C.multiplicity e = 1 := by
      unfold multiplicity
      rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro j _ hj
        have hne : C.edges j ≠ e := by
          intro h
          exact hj (C.edge_injective (h.trans hk.symm))
        simp [hne]
      · simp
    rw [hm]
    have := hpos k
    rw [hk] at this
    omega
  · have he : ∀ k, C.edges k ≠ e := by simpa using hex
    simp [multiplicity, he]

/-- Balanced nonnegative integer edge multiplicities resolve into a finite list of
actual simple directed cycles. This is the finite algorithm used after arc cutting. -/
theorem balanced_flow_finite_cycle_resolution
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (src dst : E → V) (c : E → ℕ)
    (hbal : ∀ v, (∑ e, if src e = v then c e else 0) =
      ∑ e, if dst e = v then c e else 0) :
    ∃ L : List (FiniteDirectedSimpleCycle src dst),
      ∀ e, c e = (L.map (fun C => C.multiplicity e)).sum := by
  classical
  generalize hm : (∑ e, c e) = m
  induction m using Nat.strong_induction_on generalizing c with
  | h m ih =>
    by_cases hpos : ∃ e, 0 < c e
    · obtain ⟨n, hn, z, edges, hz, hsimp, he, hinj⟩ :=
        balanced_flow_contains_simple_cycle src dst c hbal hpos
      let C : FiniteDirectedSimpleCycle src dst :=
        ⟨n, hn, z, edges, hz, fun k => (he k).1,
          fun k => (he k).2.1, hsimp, hinj⟩
      have hle : ∀ e, C.multiplicity e ≤ c e :=
        C.multiplicity_le_flow c (fun k => (he k).2.2)
      have hd : ∀ v, (∑ e, if src e = v then C.multiplicity e else 0) =
          ∑ e, if dst e = v then C.multiplicity e else 0 :=
        closed_edge_sequence_balanced src dst n z edges hz C.sources C.targets
      have hdpos : ∃ e, 0 < C.multiplicity e := by
        let k : Fin n := ⟨0, hn⟩
        refine ⟨edges k, ?_⟩
        have hh : 1 ≤ C.multiplicity (edges k) := by
          unfold FiniteDirectedSimpleCycle.multiplicity
          simpa [C] using (Finset.single_le_sum
            (fun j (_ : j ∈ Finset.univ) => Nat.zero_le
              (if edges j = edges k then 1 else 0)) (Finset.mem_univ k))
        omega
      obtain ⟨hrbal, hrlt⟩ := balanced_subflow_remainder src dst c
        C.multiplicity hle hbal hd hdpos
      obtain ⟨L, hL⟩ := ih (∑ e : E, (c e - C.multiplicity e))
        (by simpa [hm] using hrlt) (fun e => c e - C.multiplicity e) hrbal rfl
      refine ⟨C :: L, fun e => ?_⟩
      simp only [List.map_cons, List.sum_cons]
      rw [← hL e]
      exact (Nat.add_sub_of_le (hle e)).symm
    · refine ⟨[], fun e => ?_⟩
      have he : c e = 0 := by
        have := not_exists.mp hpos e
        omega
      simpa using he

/-- Replace each signed edge multiplicity by the nonnegative multiplicities of
its two actual orientations. -/
def signedFlowSource {V E : Type*} (src dst : E → V) (e : E × Bool) : V :=
  if e.2 then src e.1 else dst e.1

def signedFlowTarget {V E : Type*} (src dst : E → V) (e : E × Bool) : V :=
  if e.2 then dst e.1 else src e.1

def signedFlowWeight {E : Type*} (c : E → ℤ) (e : E × Bool) : ℕ :=
  if e.2 then (c e.1).toNat else (-c e.1).toNat

/-- Actual signed incidence balance becomes nonnegative oriented incidence
balance, without an extra geometric or homological premise. -/
theorem signed_flow_orientations_balanced
    {V E : Type*} [DecidableEq V] [Fintype E]
    (src dst : E → V) (c : E → ℤ)
    (hbal : ∀ v, (∑ e, if src e = v then c e else 0) =
      ∑ e, if dst e = v then c e else 0) :
    ∀ v, (∑ e : E × Bool, if signedFlowSource src dst e = v then signedFlowWeight c e else 0) =
      ∑ e : E × Bool, if signedFlowTarget src dst e = v then signedFlowWeight c e else 0 := by
  classical
  intro v
  let plus (r : E → V) := ∑ e, if r e = v then (c e).toNat else 0
  let minus (r : E → V) := ∑ e, if r e = v then (-c e).toNat else 0
  have hout : (∑ e : E × Bool, if signedFlowSource src dst e = v then signedFlowWeight c e else 0) =
      plus src + minus dst := by
    simp [signedFlowSource, signedFlowWeight, Fintype.sum_prod_type,
      Fintype.univ_bool, plus, minus, Finset.sum_add_distrib, add_comm]
  have hin : (∑ e : E × Bool, if signedFlowTarget src dst e = v then signedFlowWeight c e else 0) =
      plus dst + minus src := by
    simp [signedFlowTarget, signedFlowWeight, Fintype.sum_prod_type,
      Fintype.univ_bool, plus, minus, Finset.sum_add_distrib, add_comm]
  have hsplit (r : E → V) : (∑ e, if r e = v then c e else 0) =
      (plus r : ℤ) - (minus r : ℤ) := by
    simp only [plus, minus, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : r e = v
    · simp only [he, ite_true]
      omega
    · simp [he]
  rw [hout, hin]
  have hh := hbal v
  rw [hsplit src, hsplit dst] at hh
  have hsum : ((plus src + minus dst : ℕ) : ℤ) =
      ((plus dst + minus src : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast hsum

/-- Every signed balanced finite edge flow resolves into actual simple cycles
of oriented edges, with exact integer coefficients on the original edges. -/
theorem signed_flow_finite_cycle_resolution
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (src dst : E → V) (c : E → ℤ)
    (hbal : ∀ v, (∑ e, if src e = v then c e else 0) =
      ∑ e, if dst e = v then c e else 0) :
    ∃ L : List (FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)),
      (∀ e : E × Bool, signedFlowWeight c e = (L.map (fun C => C.multiplicity e)).sum) ∧
      ∀ e, c e = (L.map (fun C => (C.multiplicity (e,true) : ℤ) -
        (C.multiplicity (e,false) : ℤ))).sum := by
  classical
  obtain ⟨L,hL⟩ := balanced_flow_finite_cycle_resolution
    (signedFlowSource src dst) (signedFlowTarget src dst) (signedFlowWeight c)
    (signed_flow_orientations_balanced src dst c hbal)
  refine ⟨L,hL, fun e => ?_⟩
  have hsum : (L.map (fun C => (C.multiplicity (e,true) : ℤ) -
      (C.multiplicity (e,false) : ℤ))).sum =
      (((L.map (fun C => C.multiplicity (e,true))).sum : ℕ) : ℤ) -
      (((L.map (fun C => C.multiplicity (e,false))).sum : ℕ) : ℤ) := by
    clear hL
    induction L with
    | nil => simp
    | cons C L ih =>
      simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
      ring
  rw [hsum, ← hL, ← hL]
  simp only [signedFlowWeight, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false]
  omega

/-- Positive signed flow never uses both orientations of one actual edge. -/
theorem signed_flow_positive_orientation_unique
    {E : Type*} (c : E → ℤ) (e : E) :
    ¬ (0 < signedFlowWeight c (e,true) ∧ 0 < signedFlowWeight c (e,false)) := by
  simp only [signedFlowWeight, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false]
  omega

theorem resolved_cycle_edges_positive
    {V E : Type*} {src dst : E → V} (c : E → ℕ)
    (L : List (FiniteDirectedSimpleCycle src dst))
    (hL : ∀ e, c e = (L.map (fun C => C.multiplicity e)).sum)
    (C : FiniteDirectedSimpleCycle src dst) (hC : C ∈ L) (k : Fin C.length) :
    0 < c (C.edges k) := by
  classical
  have hcount : 1 ≤ C.multiplicity (C.edges k) := by
    unfold FiniteDirectedSimpleCycle.multiplicity
    simpa using (Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => Nat.zero_le
        (if C.edges j = C.edges k then 1 else 0)) (Finset.mem_univ k))
  have hsum : C.multiplicity (C.edges k) ≤
      (L.map (fun D => D.multiplicity (C.edges k))).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨C,hC,rfl⟩)
  rw [← hL] at hsum
  omega

/-- A resolved positive signed cycle never repeats an unoriented actual edge. -/
theorem resolved_signed_cycle_raw_edges_injective
    {V E : Type*} (src dst : E → V) (c : E → ℤ)
    (L : List (FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)))
    (hL : ∀ e, signedFlowWeight c e = (L.map (fun C => C.multiplicity e)).sum)
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst))
    (hC : C ∈ L) : Function.Injective (fun k => (C.edges k).1) := by
  intro i j hij
  change (C.edges i).1 = (C.edges j).1 at hij
  by_cases hb : (C.edges i).2 = (C.edges j).2
  · exact C.edge_injective (Prod.ext hij hb)
  · have hi := resolved_cycle_edges_positive (signedFlowWeight c) L hL C hC i
    have hj := resolved_cycle_edges_positive (signedFlowWeight c) L hL C hC j
    dsimp [signedFlowWeight] at hi hj
    rw [hij] at hi
    cases hbi : (C.edges i).2 <;> cases hbj : (C.edges j).2 <;>
      simp_all <;> omega

theorem simple_cycle_length_two_le_of_no_self_edges
    {V E : Type*} {src dst : E → V} (C : FiniteDirectedSimpleCycle src dst)
    (hne : ∀ e, src e ≠ dst e) : 2 ≤ C.length := by
  by_contra hn
  have hp := C.positive_length
  have hlen : C.length = 1 := by omega
  let k : Fin C.length := ⟨0,hp⟩
  have hs : k.castSucc = 0 := by apply Fin.ext; rfl
  have ht : k.succ = Fin.last C.length := by apply Fin.ext; simp [k,hlen]
  apply hne (C.edges k)
  rw [C.sources, C.targets, hs, ht]
  exact C.closed

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

/-- Concatenation preserves embeddedness when two embedded arcs meet only at
 their common endpoint. -/
theorem embedded_arcs_concat_injective
    {S : Type*} [TopologicalSpace S] {a b c : S}
    (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t : unitInterval, p s = q t → s = 1 ∧ t = 0) :
    Function.Injective (p.trans q) := by
  intro s t he
  rw [Path.trans_apply, Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · have hh := congrArg Subtype.val (hp he)
    apply Subtype.ext
    dsimp at hh
    linarith
  · have hh := (hcross _ _ he).2
    have hv := congrArg Subtype.val hh
    dsimp at hv
    have htt : (1 : ℝ) / 2 < t := lt_of_not_ge ht
    linarith
  · have hh := (hcross _ _ he.symm).2
    have hv := congrArg Subtype.val hh
    dsimp at hv
    have hss : (1 : ℝ) / 2 < s := lt_of_not_ge hs
    linarith
  · have hh := congrArg Subtype.val (hq he)
    apply Subtype.ext
    dsimp at hh
    linarith

/-- Closing an embedded arc by another arc meeting it only at its two endpoints
produces a loop with precisely the endpoint identification. -/
theorem embedded_arcs_closing_loop_collision
    {S : Type*} [TopologicalSpace S] {a b : S}
    (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t : unitInterval, p s = q t →
      (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) :
    ∀ s t : unitInterval, (p.trans q) s = (p.trans q) t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  intro s t he
  rw [Path.trans_apply, Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · left
    have hh := congrArg Subtype.val (hp he)
    apply Subtype.ext
    dsimp at hh
    linarith
  · rcases hcross _ _ he with ⟨_, hh⟩ | ⟨hh, hh'⟩
    · have hv := congrArg Subtype.val hh
      dsimp at hv
      have htt : (1 : ℝ) / 2 < t := lt_of_not_ge ht
      linarith
    · right; left
      constructor
      · apply Subtype.ext
        have hv := congrArg Subtype.val hh
        dsimp at hv ⊢
        linarith
      · apply Subtype.ext
        have hv := congrArg Subtype.val hh'
        dsimp at hv ⊢
        linarith
  · rcases hcross _ _ he.symm with ⟨_, hh⟩ | ⟨hh, hh'⟩
    · have hv := congrArg Subtype.val hh
      dsimp at hv
      have hss : (1 : ℝ) / 2 < s := lt_of_not_ge hs
      linarith
    · right; right
      constructor
      · apply Subtype.ext
        have hv := congrArg Subtype.val hh'
        dsimp at hv ⊢
        linarith
      · apply Subtype.ext
        have hv := congrArg Subtype.val hh
        dsimp at hv ⊢
        linarith
  · left
    have hh := congrArg Subtype.val (hq he)
    apply Subtype.ext
    dsimp at hh
    linarith

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Set Topology

/-- Endpoint-only collision of an actual interval loop yields an actual embedded
Circle. The loop is not assumed nullhomotopic or essential. -/
theorem simple_loop_gives_embedded_curve
    {X : Type} [TopologicalSpace X] [T2Space X]
    (x : X) (l : Path x x)
    (hcoll : ∀ s t : CurveComplex.Interval, l s = l t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l := by
  let r := AddCircle.EndpointIdent (1 : ℝ) 0
  let j : Icc (0 : ℝ) (0 + 1) → CurveComplex.Interval := fun t => ⟨t.val, by simpa using t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
    rintro a b ⟨⟩
    simpa [j] using l.source.trans l.target.symm
  let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
  have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
  have hLi : Function.Injective L := by
    intro a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro hab
        rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · apply congrArg (Quot.mk r)
          exact Subtype.ext (congrArg (fun t : CurveComplex.Interval => t.val) he)
        · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) ha)
          have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) hb)
          subst a; subst b
          exact Quot.sound AddCircle.EndpointIdent.mk
        · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) ha)
          have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : CurveComplex.Interval => t.val) hb)
          subst a; subst b
          exact (Quot.sound AddCircle.EndpointIdent.mk).symm
  let e : Circle ≃ₜ Quot r :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      (AddCircle.homeoIccQuot (1 : ℝ) 0)
  let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
  refine ⟨c, ?_⟩
  change range (L ∘ e) = range l
  rw [e.surjective.range_comp]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.inductionOn with | h t =>
      exact ⟨j t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Quot.mk r ⟨t.val, by simpa using t.property⟩, rfl⟩

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.simple_loop_gives_embedded_curve

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

theorem embedded_arcs_closing_loop_gives_curve
    {S : Type} [TopologicalSpace S] [T2Space S] {a b : S}
    (p : Path a b) (q : Path b a)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t : unitInterval, p s = q t →
      (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) :
    ∃ c : Curve S, c.image = Set.range p ∪ Set.range q := by
  obtain ⟨c, hc⟩ := simple_loop_gives_embedded_curve a (p.trans q)
    (embedded_arcs_closing_loop_collision p q hp hq hcross)
  exact ⟨c, hc.trans (Path.trans_range p q)⟩

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

/-- Nonempty concatenation omits the initial constant segment of `Path.concat`,
which would destroy embeddedness. -/
noncomputable def nonemptyGraphPath {S : Type*} [TopologicalSpace S] :
    (n : ℕ) → (z : Fin (n + 2) → S) →
    ((k : Fin (n + 1)) → Path (z k.castSucc) (z k.succ)) →
    Path (z 0) (z (Fin.last (n + 1)))
  | 0, z, E => E 0
  | n + 1, z, E =>
      (nonemptyGraphPath n (z ∘ Fin.castSucc) (fun k => E k.castSucc)).trans
        (E (Fin.last (n + 1)))

/-- Every point of a nonempty finite concatenation lies on an actual constituent arc. -/
theorem nonemptyGraphPath_point_on_arc
    {S : Type*} [TopologicalSpace S] (n : ℕ) (z : Fin (n + 2) → S)
    (E : (k : Fin (n + 1)) → Path (z k.castSucc) (z k.succ))
    (t : unitInterval) :
    ∃ (k : Fin (n + 1)) (u : unitInterval), nonemptyGraphPath n z E t = E k u := by
  induction n generalizing t with
  | zero => exact ⟨0, t, rfl⟩
  | succ n ih =>
    have ht : nonemptyGraphPath (n+1) z E t ∈
        Set.range (nonemptyGraphPath n (z ∘ Fin.castSucc) (fun k => E k.castSucc)) ∪
          Set.range (E (Fin.last (n + 1))) := by
      rw [← Path.trans_range]
      exact ⟨t, rfl⟩
    rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
    · obtain ⟨k, v, hv⟩ := ih (z ∘ Fin.castSucc) (fun k => E k.castSucc) u
      exact ⟨k.castSucc, v, hu.symm.trans hv⟩
    · exact ⟨Fin.last (n+1), u, hu.symm⟩

/-- A finite chain of embedded arcs with distinct vertices and endpoint-only
intersections is itself an embedded arc. -/
theorem nonemptyGraphPath_injective
    {S : Type*} [TopologicalSpace S] (n : ℕ) (z : Fin (n + 2) → S)
    (E : (k : Fin (n + 1)) → Path (z k.castSucc) (z k.succ))
    (hz : Function.Injective z) (hE : ∀ k, Function.Injective (E k))
    (hc : ∀ i j, i ≠ j → ∀ s t : unitInterval,
      E i s = E j t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) :
    Function.Injective (nonemptyGraphPath n z E) := by
  induction n with
  | zero => exact hE 0
  | succ n ih =>
    let P := nonemptyGraphPath n (z ∘ Fin.castSucc) (fun k => E k.castSucc)
    have hP : Function.Injective P :=
      ih (z ∘ Fin.castSucc) (fun k => E k.castSucc)
        (hz.comp (Fin.castSucc_injective _)) (fun k => hE k.castSucc)
        (fun i j hij => hc i.castSucc j.castSucc
          (fun h => hij (Fin.castSucc_injective _ h)))
    apply embedded_arcs_concat_injective P (E (Fin.last (n+1))) hP (hE _)
    intro s t he
    obtain ⟨i, u, hu⟩ := nonemptyGraphPath_point_on_arc n (z ∘ Fin.castSucc)
      (fun k => E k.castSucc) s
    have hex : E i.castSucc u = E (Fin.last (n+1)) t := hu.symm.trans he
    obtain ⟨hui, hti⟩ := hc i.castSucc (Fin.last (n+1)) (by
      intro h
      have hh := congrArg Fin.val h
      have hi := i.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      omega) u t hex
    have ht : t = 0 := by
      rcases hti with ht | ht
      · exact ht
      · rcases hui with hu | hu
        · have hh := hz (by simpa [hu, ht] using hex)
          have hv := congrArg Fin.val hh
          have hi := i.isLt
          simp at hv
          omega
        · have hh := hz (by simpa [hu, ht] using hex)
          have hv := congrArg Fin.val hh
          have hi := i.isLt
          simp at hv
          omega
    refine ⟨?_, ht⟩
    apply hP
    rw [Path.target]
    simpa [ht, P] using he

/-- Every constituent arc lies in the actual nonempty concatenation. -/
theorem nonemptyGraphPath_arc_in_range
    {S : Type*} [TopologicalSpace S] (n : ℕ) (z : Fin (n + 2) → S)
    (E : (k : Fin (n + 1)) → Path (z k.castSucc) (z k.succ))
    (k : Fin (n+1)) (u : unitInterval) :
    E k u ∈ Set.range (nonemptyGraphPath n z E) := by
  induction n with
  | zero =>
    have hk : k = 0 := by apply Fin.ext; omega
    subst k
    exact ⟨u, rfl⟩
  | succ n ih =>
    change E k u ∈ Set.range
      ((nonemptyGraphPath n (z ∘ Fin.castSucc) (fun j => E j.castSucc)).trans
        (E (Fin.last (n+1))))
    rw [Path.trans_range]
    refine Fin.lastCases ?_ (fun j => ?_) k
    · exact Or.inr ⟨u, rfl⟩
    · exact Or.inl (ih (z ∘ Fin.castSucc) (fun j => E j.castSucc) j)

/-- An actual vertex-simple finite cycle of embedded arcs with endpoint-only
intersections yields an actual embedded circle containing every constituent arc. -/
theorem simple_finite_graph_cycle_gives_curve
    {S : Type} [TopologicalSpace S] [T2Space S]
    (n : ℕ) (z : Fin (n+3) → S)
    (E : (k : Fin (n+2)) → Path (z k.castSucc) (z k.succ))
    (hz : z 0 = z (Fin.last (n+2)))
    (hv : Function.Injective (fun k : Fin (n+2) => z k.castSucc))
    (hE : ∀ k, Function.Injective (E k))
    (hc : ∀ i j, i ≠ j → ∀ s t : unitInterval,
      E i s = E j t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) :
    ∃ c : Curve S, ∀ k u, E k u ∈ c.image := by
  let P := nonemptyGraphPath n (z ∘ Fin.castSucc) (fun k => E k.castSucc)
  let Q : Path (z (Fin.last (n+1)).castSucc) (z 0) :=
    (E (Fin.last (n+1))).cast rfl hz
  have hP : Function.Injective P :=
    nonemptyGraphPath_injective n (z ∘ Fin.castSucc) (fun k => E k.castSucc)
      hv (fun k => hE k.castSucc)
      (fun i j hij => hc i.castSucc j.castSucc
        (fun h => hij (Fin.castSucc_injective _ h)))
  have hQ : Function.Injective Q := by
    simpa only [Q, Path.cast_coe] using hE (Fin.last (n+1))
  have hcross : ∀ s t : unitInterval, P s = Q t →
      (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) := by
    intro s t he
    obtain ⟨i, u, hu⟩ := nonemptyGraphPath_point_on_arc n (z ∘ Fin.castSucc)
      (fun k => E k.castSucc) s
    have hex : E i.castSucc u = E (Fin.last (n+1)) t := hu.symm.trans he
    obtain ⟨_, hti⟩ := hc i.castSucc (Fin.last (n+1)) (by
      intro h
      have hh := congrArg Fin.val h
      have hi := i.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      omega) u t hex
    rcases hti with ht | ht
    · left
      refine ⟨hP ?_, ht⟩
      rw [Path.target]
      simpa [ht, Q] using he
    · right
      refine ⟨hP ?_, ht⟩
      rw [Path.source]
      simpa [ht, Q, ← hz] using he
  obtain ⟨c, hcurve⟩ := embedded_arcs_closing_loop_gives_curve P Q hP hQ hcross
  refine ⟨c, fun k u => ?_⟩
  rw [hcurve]
  refine Fin.lastCases ?_ (fun i => ?_) k
  · exact Or.inr ⟨u, rfl⟩
  · exact Or.inl (nonemptyGraphPath_arc_in_range n (z ∘ Fin.castSucc)
      (fun k => E k.castSucc) i u)

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

noncomputable def signedGraphPath
    {S V E : Type*} [TopologicalSpace S] (src dst : E → V) (v : V → S)
    (p : (e : E) → Path (v (src e)) (v (dst e))) :
    (e : E × Bool) → Path (v (signedFlowSource src dst e))
      (v (signedFlowTarget src dst e))
  | (e,true) => p e
  | (e,false) => (p e).symm

theorem signedGraphPath_injective
    {S V E : Type*} [TopologicalSpace S] (src dst : E → V) (v : V → S)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (hp : ∀ e, Function.Injective (p e)) (e : E × Bool) :
    Function.Injective (signedGraphPath src dst v p e) := by
  rcases e with ⟨e,b⟩
  cases b
  · intro s t he
    have hh : unitInterval.symm s = unitInterval.symm t := hp e he
    exact unitInterval.symm_involutive.injective hh
  · exact hp e

theorem signedGraphPath_endpoint_intersection
    {S V E : Type*} [TopologicalSpace S] (src dst : E → V) (v : V → S)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (hc : ∀ e f, e ≠ f → ∀ s t : unitInterval,
      p e s = p f t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))
    (e f : E × Bool) (hne : e.1 ≠ f.1) (s t : unitInterval)
    (he : signedGraphPath src dst v p e s = signedGraphPath src dst v p f t) :
    (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
  rcases e with ⟨e,b⟩
  rcases f with ⟨f,d⟩
  cases b <;> cases d
  · have hh := hc e f hne (unitInterval.symm s) (unitInterval.symm t) he
    simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using hh
  · have hh := hc e f hne (unitInterval.symm s) t he
    simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using hh
  · have hh := hc e f hne s (unitInterval.symm t) he
    simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using hh
  · exact hc e f hne s t he

theorem simple_finite_graph_cycle_gives_curve_of_length_two_le
    {S : Type} [TopologicalSpace S] [T2Space S]
    (n : ℕ) (hn : 2 ≤ n) (z : Fin (n+1) → S)
    (E : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (hz : z 0 = z (Fin.last n))
    (hv : Function.Injective (fun k : Fin n => z k.castSucc))
    (hE : ∀ k, Function.Injective (E k))
    (hc : ∀ i j, i ≠ j → ∀ s t : unitInterval,
      E i s = E j t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) :
    ∃ c : Curve S, ∀ k u, E k u ∈ c.image := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n => exact simple_finite_graph_cycle_gives_curve n z E hz hv hE hc

/-- The actual signed-flow resolution produces an embedded source circle for
every resolved cycle, containing its actual oriented graph-edge paths. -/
theorem resolved_signed_graph_cycle_gives_actual_curve
    {S : Type} [TopologicalSpace S] [T2Space S] {V E : Type*}
    (src dst : E → V) (v : V → S) (hv : Function.Injective v)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (hp : ∀ e, Function.Injective (p e)) (hne : ∀ e, src e ≠ dst e)
    (hc : ∀ e f, e ≠ f → ∀ s t : unitInterval,
      p e s = p f t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))
    (c : E → ℤ)
    (L : List (FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)))
    (hL : ∀ e, signedFlowWeight c e = (L.map (fun C => C.multiplicity e)).sum)
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst))
    (hC : C ∈ L) :
    ∃ curve : Curve S, ∀ k u, signedGraphPath src dst v p (C.edges k) u ∈ curve.image := by
  have hl : 2 ≤ C.length := simple_cycle_length_two_le_of_no_self_edges C (by
    rintro ⟨e,b⟩
    cases b
    · exact (hne e).symm
    · exact hne e)
  let z := v ∘ C.vertices
  let P (k : Fin C.length) : Path (z k.castSucc) (z k.succ) :=
    (signedGraphPath src dst v p (C.edges k)).cast
      (congrArg v (C.sources k).symm) (congrArg v (C.targets k).symm)
  have hPi (k : Fin C.length) : Function.Injective (P k) := by
    simpa only [P, Path.cast_coe] using signedGraphPath_injective src dst v p hp (C.edges k)
  have hraw := resolved_signed_cycle_raw_edges_injective src dst c L hL C hC
  have hPc : ∀ i j, i ≠ j → ∀ s t : unitInterval,
      P i s = P j t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
    intro i j hij s t he
    exact signedGraphPath_endpoint_intersection src dst v p hc (C.edges i) (C.edges j)
      (fun h => hij (hraw h)) s t he
  obtain ⟨curve,hcurve⟩ := simple_finite_graph_cycle_gives_curve_of_length_two_le
    C.length hl z P (congrArg v C.closed) (hv.comp C.simple) hPi hPc
  exact ⟨curve,hcurve⟩

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology.PathChains
open CurveComplex CurveComplexGenusTwo.CWHurewicz CategoryTheory Convexity
open scoped Simplicial

noncomputable def weightedTime (n : ℕ) (times : Fin (n+1) → unitInterval) :
    C(StdSimplex ℝ (Fin (n+1)), unitInterval) := {
  toFun := fun z => ⟨∑ i, z.weights i * (times i : ℝ), by
    constructor
    · exact Finset.sum_nonneg (fun i _ => mul_nonneg (z.weights_nonneg i) (times i).property.1)
    · calc
        ∑ i, z.weights i * (times i : ℝ) ≤ ∑ i, z.weights i * 1 :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (times i).property.2 (z.weights_nonneg i))
        _ = 1 := by
          have hz := z.total
          rw [Finsupp.sum_fintype] at hz <;> simp_all⟩
  continuous_toFun := (show Continuous (fun z : StdSimplex ℝ (Fin (n+1)) =>
    ∑ i, z.weights i * (times i : ℝ)) from by fun_prop).subtype_mk _ }

noncomputable def edgeSimplex {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).symm
    (f.comp (weightedTime 1 ![a,b]))

noncomputable def triangleSimplex {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b c : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋2⦌)).symm
    (f.comp (weightedTime 2 ![a,b,c]))

private theorem triangle_face0 {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b c : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 0 (triangleSimplex f a b c) = edgeSimplex f b c := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change f (weightedTime 2 ![a,b,c] (z.map (0 : Fin 3).succAbove)) =
    f (weightedTime 1 ![b,c] z)
  apply congrArg f
  apply Subtype.ext
  simp [weightedTime, StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_fintype, Fin.sum_univ_two, Fin.sum_univ_three]

private theorem triangle_face1 {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b c : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 1 (triangleSimplex f a b c) = edgeSimplex f a c := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change f (weightedTime 2 ![a,b,c] (z.map (1 : Fin 3).succAbove)) =
    f (weightedTime 1 ![a,c] z)
  apply congrArg f
  apply Subtype.ext
  simp [weightedTime, StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_fintype, Fin.sum_univ_two, Fin.sum_univ_three]

private theorem triangle_face2 {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b c : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 2 (triangleSimplex f a b c) = edgeSimplex f a b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change f (weightedTime 2 ![a,b,c] (z.map (2 : Fin 3).succAbove)) =
    f (weightedTime 1 ![a,b] z)
  apply congrArg f
  apply Subtype.ext
  have hs : (2 : Fin 3).succAbove (1 : Fin 2) = (1 : Fin 3) := by decide
  simp [weightedTime, StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_fintype, Fin.sum_univ_two, Fin.sum_univ_three, hs]

theorem triangle_boundary {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b c : unitInterval) :
    singularBoundaryFinsupp (TopCat.of S) 1 (Finsupp.single (triangleSimplex f a b c) 1) =
      Finsupp.single (edgeSimplex f b c) 1 - Finsupp.single (edgeSimplex f a c) 1 +
        Finsupp.single (edgeSimplex f a b) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, triangle_face0, triangle_face1, triangle_face2]
  abel

noncomputable def splitCorrection {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (t : ℕ → unitInterval) (N : ℕ) :
    (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ :=
  (∑ i ∈ Finset.range N, Finsupp.single (triangleSimplex f (t 0) (t i) (t (i+1))) 1) -
    Finsupp.single (triangleSimplex f (t 0) (t 0) (t 0)) 1

private theorem splitCorrection_succ {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (t : ℕ → unitInterval) (N : ℕ) :
    splitCorrection f t (N+1) = splitCorrection f t N +
      Finsupp.single (triangleSimplex f (t 0) (t N) (t (N+1))) 1 := by
  simp only [splitCorrection, Finset.sum_range_succ]
  abel

/-- An actual finite path subdivision has an explicit finite singular 2-chain
correction, including the degenerate first triangle. No homology premise. -/
theorem splitCorrection_boundary {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (t : ℕ → unitInterval) (N : ℕ) :
    singularBoundaryFinsupp (TopCat.of S) 1 (splitCorrection f t N) =
      (∑ i ∈ Finset.range N, Finsupp.single (edgeSimplex f (t i) (t (i+1))) 1) -
        Finsupp.single (edgeSimplex f (t 0) (t N)) 1 := by
  induction N with
  | zero =>
    simp only [splitCorrection, Finset.range_zero, Finset.sum_empty, zero_sub,
      map_neg, triangle_boundary]
    abel
  | succ N ih =>
    rw [splitCorrection_succ, map_add, ih, triangle_boundary, Finset.sum_range_succ]
    abel

/-- Reversing an actual oriented path edge differs by an explicit boundary. -/
theorem reverse_edge_boundary {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b : unitInterval) :
    singularBoundaryFinsupp (TopCat.of S) 1
      (Finsupp.single (triangleSimplex f a b a) 1 +
        Finsupp.single (triangleSimplex f a a a) 1) =
      Finsupp.single (edgeSimplex f a b) 1 + Finsupp.single (edgeSimplex f b a) 1 := by
  rw [map_add, triangle_boundary, triangle_boundary]
  abel

end CurveComplexGenusTwo.SourceTopology.PathChains


namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial

/-- Injective actual maps give injective maps on finite singular chains. -/
theorem singularFinsuppPush_injective_of_injective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (singularFinsuppPush (TopCat.ofHom f) n) := by
  have hi : Function.Injective
      ((TopCat.toSSet.map (TopCat.ofHom f)).app (.op ⦋n⦌)) := by
    intro a b hab
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).injective
    ext z
    apply hf
    exact congrArg (fun t => TopCat.toSSetObjEquiv (TopCat.of Y) (.op ⦋n⦌) t z) hab
  intro a b hab
  ext x
  have h := congrArg (fun t => t
    (((TopCat.toSSet.map (TopCat.ofHom f)).app (.op ⦋n⦌)) x)) hab
  simpa [singularFinsuppPush, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_apply_of_injective hi] using h

/-- A singular simplex whose actual image is contained in an embedded circle
has an actual continuous lift to that circle. -/
theorem singular_simplex_lifts_to_curve
    {S : Type} [TopologicalSpace S] (c : Curve S) (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of S)) _⦋n⦌)
    (ha : ∀ z, TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋n⦌) a z ∈ c.image) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋n⦌,
      ((TopCat.toSSet.map (TopCat.ofHom
        (⟨c.map,c.embedded.continuous⟩ : C(Circle,S)))).app (.op ⦋n⦌)) b = a := by
  classical
  let A := TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋n⦌) a
  have he (z) : ∃ t, c.map t = A z := ha z
  let l := fun z => Classical.choose (he z)
  have hl : (c.map ∘ l) = A := funext (fun z => Classical.choose_spec (he z))
  have hcont : Continuous l := c.embedded.continuous_iff.mpr (by
    rw [hl]
    exact A.continuous)
  refine ⟨(TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋n⦌)).symm ⟨l,hcont⟩, ?_⟩
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋n⦌)).injective
  ext z
  exact Classical.choose_spec (he z)

/-- An actual finite singular cycle carried by an embedded source circle is
exactly the pushforward of an actual finite singular cycle of that circle. -/
theorem singular_cycle_carried_by_curve_lifts
    {S : Type} [TopologicalSpace S] (c : Curve S)
    (chain : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌ →₀ ℤ)
    (hchain : singularBoundaryFinsupp (TopCat.of S) 0 chain = 0)
    (hcarry : ∀ a ∈ chain.support, ∀ z,
      TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a z ∈ c.image) :
    ∃ cycle : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ,
      cycle ∈ absoluteSingularCycles (TopCat.of Circle) 1 ∧
      singularFinsuppPush (TopCat.ofHom
        (⟨c.map,c.embedded.continuous⟩ : C(Circle,S))) 1 cycle = chain := by
  classical
  let f : C(Circle,S) := ⟨c.map,c.embedded.continuous⟩
  let push := ((TopCat.toSSet.map (TopCat.ofHom f)).app (.op ⦋1⦌))
  have hlift (a) (ha : a ∈ chain.support) : ∃ b, push b = a :=
    singular_simplex_lifts_to_curve c 1 a (hcarry a ha)
  let l := fun a => if ha : a ∈ chain.support then Classical.choose (hlift a ha)
    else (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm
      (ContinuousMap.const _ (1 : Circle))
  let cycle := Finsupp.mapDomain l chain
  have heq : singularFinsuppPush (TopCat.ofHom f) 1 cycle = chain := by
    change Finsupp.mapDomain push (Finsupp.mapDomain l chain) = chain
    rw [← Finsupp.mapDomain_comp]
    calc
      Finsupp.mapDomain (push ∘ l) chain = Finsupp.mapDomain id chain :=
        Finsupp.mapDomain_congr (fun a ha => by
          dsimp [l]
          rw [dif_pos ha]
          exact Classical.choose_spec (hlift a ha))
      _ = chain := Finsupp.mapDomain_id
  refine ⟨cycle, ?_, heq⟩
  have hzero : singularBoundaryFinsupp (TopCat.of Circle) 0 cycle = 0 := by
    apply singularFinsuppPush_injective_of_injective f c.embedded.injective 0
    rw [← singularFinsuppPush_boundary, heq, hchain, map_zero]
  change singularBoundaryFinsupp (TopCat.of Circle) 0 cycle = 0
  exact hzero

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology.PathChains
open CurveComplex CurveComplexGenusTwo.CWHurewicz CategoryTheory Convexity
open scoped Simplicial

noncomputable def vertexSimplex {S : Type} [TopologicalSpace S] (x : S) :
    (TopCat.toSSet.obj (TopCat.of S)) _⦋0⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋0⦌)).symm (ContinuousMap.const _ x)

private theorem edge_face0 {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 0 (edgeSimplex f a b) = vertexSimplex (f b) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋0⦌)).injective
  ext z
  change f (weightedTime 1 ![a,b] (z.map (0 : Fin 2).succAbove)) = f b
  have hz : z.weights 0 = 1 := by
    have h := z.total
    rw [Finsupp.sum_fintype] at h <;> simpa using h
  apply congrArg f
  apply Subtype.ext
  simp [weightedTime, StdSimplex.weights_map,Finsupp.mapDomain,
    Finsupp.sum_fintype,Fin.sum_univ_two,Fin.sum_univ_one,hz]

private theorem edge_face1 {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b : unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 1 (edgeSimplex f a b) = vertexSimplex (f a) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋0⦌)).injective
  ext z
  change f (weightedTime 1 ![a,b] (z.map (1 : Fin 2).succAbove)) = f a
  have hz : z.weights 0 = 1 := by
    have h := z.total
    rw [Finsupp.sum_fintype] at h <;> simpa using h
  apply congrArg f
  apply Subtype.ext
  have hh : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := by decide
  simp [weightedTime, StdSimplex.weights_map,Finsupp.mapDomain,
    Finsupp.sum_fintype,Fin.sum_univ_two,Fin.sum_univ_one,hz,hh]

theorem edgeSimplex_boundary {S : Type} [TopologicalSpace S]
    (f : C(unitInterval,S)) (a b : unitInterval) :
    singularBoundaryFinsupp (TopCat.of S) 0 (Finsupp.single (edgeSimplex f a b) 1) =
      Finsupp.single (vertexSimplex (f b)) 1 - Finsupp.single (vertexSimplex (f a)) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_two,edge_face0,edge_face1]
  abel

theorem actual_closed_path_sequence_cycle
    {S : Type} [TopologicalSpace S] (n : ℕ) (z : Fin (n+1) → S)
    (p : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (hz : z 0 = z (Fin.last n)) :
    singularBoundaryFinsupp (TopCat.of S) 0
      (∑ k, Finsupp.single (edgeSimplex (p k).toContinuousMap 0 1) 1) = 0 := by
  rw [map_sum]
  simp only [edgeSimplex_boundary,Path.target,Path.source]
  rw [Finset.sum_sub_distrib]
  change (∑ k, Finsupp.single (vertexSimplex ((p k) 1)) (1 : ℤ)) -
    (∑ k, Finsupp.single (vertexSimplex ((p k) 0)) (1 : ℤ)) = 0
  simp only [Path.target, Path.source]
  have h₁ := Fin.sum_univ_castSucc (fun k => Finsupp.single (vertexSimplex (z k)) (1 : ℤ))
  have h₂ := Fin.sum_univ_succ (fun k => Finsupp.single (vertexSimplex (z k)) (1 : ℤ))
  rw [← hz] at h₁
  have h₂' := h₂.trans (add_comm _ _)
  have he := add_right_cancel (h₁.symm.trans h₂')
  rw [he, sub_self]

/-- The actual edge chain of a closed graph cycle carried by an actual embedded
circle is exactly a pushed finite singular Circle cycle. -/
theorem actual_closed_path_sequence_lifts_to_circle_cycle
    {S : Type} [TopologicalSpace S] (n : ℕ) (z : Fin (n+1) → S)
    (p : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (hz : z 0 = z (Fin.last n)) (c : Curve S)
    (hc : ∀ k u, p k u ∈ c.image) :
    ∃ cycle : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ,
      cycle ∈ absoluteSingularCycles (TopCat.of Circle) 1 ∧
      singularFinsuppPush (TopCat.ofHom
        (⟨c.map,c.embedded.continuous⟩ : C(Circle,S))) 1 cycle =
          ∑ k, Finsupp.single (edgeSimplex (p k).toContinuousMap 0 1) 1 := by
  classical
  let chain := ∑ k, Finsupp.single (edgeSimplex (p k).toContinuousMap 0 1) (1 : ℤ)
  apply singular_cycle_carried_by_curve_lifts c chain
    (actual_closed_path_sequence_cycle n z p hz)
  intro a ha x
  have hex : ∃ k, edgeSimplex (p k).toContinuousMap 0 1 = a := by
    by_contra hn
    have hne : ∀ k, edgeSimplex (p k).toContinuousMap 0 1 ≠ a := by simpa using hn
    have he0 : chain a = 0 := by
      simp [chain,Finsupp.sum_apply,Finsupp.single_apply,hne]
    exact Finsupp.mem_support_iff.mp ha he0
  obtain ⟨k,hk⟩ := hex
  rw [← hk]
  change (p k).toContinuousMap (weightedTime 1 ![0,1] x) ∈ c.image
  exact hc k _

theorem edgeSimplex_path_symm
    {S : Type} [TopologicalSpace S] {a b : S} (p : Path a b) :
    edgeSimplex p.symm.toContinuousMap 0 1 = edgeSimplex p.toContinuousMap 1 0 := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change p (unitInterval.symm (weightedTime 1 ![0,1] z)) =
    p (weightedTime 1 ![1,0] z)
  apply congrArg p
  apply Subtype.ext
  have htotal : z.weights 0 + z.weights 1 = 1 := by
    have ht := z.total
    rw [Finsupp.sum_fintype] at ht <;> simpa [Fin.sum_univ_two] using ht
  dsimp [weightedTime]
  simp only [Fin.sum_univ_two]
  norm_num
  linarith [htotal]

end CurveComplexGenusTwo.SourceTopology.PathChains

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz
open PathChains
open scoped Simplicial

/-- Every actual resolved signed graph cycle is represented exactly by an
actual finite singular cycle pushed from its constructed embedded Circle. -/
theorem resolved_signed_graph_cycle_is_pushed_circle_cycle
    {S : Type} [TopologicalSpace S] [T2Space S] {V E : Type*}
    (src dst : E → V) (v : V → S) (hv : Function.Injective v)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (hp : ∀ e, Function.Injective (p e)) (hne : ∀ e, src e ≠ dst e)
    (hc : ∀ e f, e ≠ f → ∀ s t : unitInterval,
      p e s = p f t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))
    (c : E → ℤ)
    (L : List (FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)))
    (hL : ∀ e, signedFlowWeight c e = (L.map (fun C => C.multiplicity e)).sum)
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst))
    (hC : C ∈ L) :
    ∃ (curve : Curve S)
      (cycle : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ),
      cycle ∈ absoluteSingularCycles (TopCat.of Circle) 1 ∧
      singularFinsuppPush (TopCat.ofHom
        (⟨curve.map,curve.embedded.continuous⟩ : C(Circle,S))) 1 cycle =
          ∑ k, Finsupp.single (edgeSimplex
            (signedGraphPath src dst v p (C.edges k)).toContinuousMap 0 1) 1 := by
  obtain ⟨curve,hcurve⟩ := resolved_signed_graph_cycle_gives_actual_curve
    src dst v hv p hp hne hc c L hL C hC
  let z := v ∘ C.vertices
  let P (k : Fin C.length) : Path (z k.castSucc) (z k.succ) :=
    (signedGraphPath src dst v p (C.edges k)).cast
      (congrArg v (C.sources k).symm) (congrArg v (C.targets k).symm)
  obtain ⟨cycle,hcycle,hpush⟩ := actual_closed_path_sequence_lifts_to_circle_cycle
    C.length z P (congrArg v C.closed) curve hcurve
  exact ⟨curve,cycle,hcycle,hpush⟩

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz
open PathChains
open scoped Simplicial

theorem cycle_multiplicity_value_sum
    {V E A : Type*} [Fintype E] [AddCommGroup A] {src dst : E → V}
    (C : FiniteDirectedSimpleCycle src dst) (f : E → A) :
    (∑ e, C.multiplicity e • f e) = ∑ k, f (C.edges k) := by
  classical
  have hdist (e : E) : C.multiplicity e • f e =
      ∑ k, if C.edges k = e then f e else 0 := by
    unfold FiniteDirectedSimpleCycle.multiplicity
    rw [← Finset.sum_nsmul_assoc]
    apply Finset.sum_congr rfl
    intro k _
    by_cases he : C.edges k = e <;> simp [he]
  simp_rw [hdist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hh (e : E) : (if C.edges k = e then f e else 0) =
      if e = C.edges k then f (C.edges k) else 0 := by
    by_cases he : e = C.edges k
    · subst e; simp
    · simp [he,Ne.symm he]
  simp_rw [hh]
  simp

noncomputable def rawSignedCycleValue
    {V E A : Type*} [AddCommGroup A] (src dst : E → V) (f : E → A)
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)) : A :=
  ∑ k, if (C.edges k).2 then f (C.edges k).1 else -f (C.edges k).1

theorem rawSignedCycleValue_coefficients
    {V E A : Type*} [Fintype E] [AddCommGroup A] (src dst : E → V) (f : E → A)
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)) :
    rawSignedCycleValue src dst f C =
      ∑ e, ((C.multiplicity (e,true) : ℤ) - (C.multiplicity (e,false) : ℤ)) • f e := by
  classical
  calc
    _ = ∑ e : E × Bool, C.multiplicity e • (if e.2 then f e.1 else -f e.1) :=
      (cycle_multiplicity_value_sum C (fun e => if e.2 then f e.1 else -f e.1)).symm
    _ = _ := by
      simp [Fintype.sum_prod_type,Fintype.univ_bool,sub_smul,natCast_zsmul,
        smul_neg,sub_eq_add_neg,add_smul,neg_smul]

noncomputable def cycleReversalCorrection
    {S : Type} [TopologicalSpace S] {V E : Type*} (src dst : E → V) (v : V → S)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)) :
    (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ :=
  ∑ k, if (C.edges k).2 then 0 else
    Finsupp.single (triangleSimplex (p (C.edges k).1).toContinuousMap 0 1 0) 1 +
      Finsupp.single (triangleSimplex (p (C.edges k).1).toContinuousMap 0 0 0) 1

/-- Every reversed cycle edge contributes its explicit reversal triangle pair;
the complete cycle correction realizes the signed/oriented chain difference. -/
theorem cycleReversalCorrection_boundary
    {S : Type} [TopologicalSpace S] {V E : Type*} (src dst : E → V) (v : V → S)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (C : FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)) :
    singularBoundaryFinsupp (TopCat.of S) 1 (cycleReversalCorrection src dst v p C) =
      (∑ k, Finsupp.single (edgeSimplex
        (signedGraphPath src dst v p (C.edges k)).toContinuousMap 0 1) 1) -
      rawSignedCycleValue src dst
        (fun e => Finsupp.single (edgeSimplex (p e).toContinuousMap 0 1) 1) C := by
  classical
  unfold cycleReversalCorrection rawSignedCycleValue
  rw [map_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  generalize he : C.edges k = e
  rcases e with ⟨e,b⟩
  cases b
  · simp only [Bool.false_eq_true,ite_false,signedGraphPath]
    rw [reverse_edge_boundary,edgeSimplex_path_symm]
    abel
  · simp [signedGraphPath]

theorem resolved_signed_raw_values_sum
    {V E A : Type*} [Fintype E] [AddCommGroup A]
    (src dst : E → V) (f : E → A) (c : E → ℤ)
    (L : List (FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)))
    (hcoef : ∀ e, c e = (L.map (fun C => (C.multiplicity (e,true) : ℤ) -
      (C.multiplicity (e,false) : ℤ))).sum) :
    (L.map (rawSignedCycleValue src dst f)).sum = ∑ e, c e • f e := by
  classical
  have hh : ∀ K : List (FiniteDirectedSimpleCycle (signedFlowSource src dst) (signedFlowTarget src dst)),
      (K.map (rawSignedCycleValue src dst f)).sum =
      ∑ e, (K.map (fun C => (C.multiplicity (e,true) : ℤ) -
        (C.multiplicity (e,false) : ℤ))).sum • f e := by
    intro K
    induction K with
    | nil => simp
    | cons C K ih =>
      simp only [List.map_cons,List.sum_cons]
      simp_rw [add_smul]
      rw [Finset.sum_add_distrib,rawSignedCycleValue_coefficients,ih]
  rw [hh]
  simp_rw [← hcoef]

/-- A balanced actual finite embedded graph cycle resolves into actual embedded
Circle cycles, with an explicit actual finite singular 2-chain correction.
This consumes actual arcs and their incidence balance, not a circle-resolution
certificate. -/
theorem actual_finite_embedded_graph_cycle_resolves
    {S : Type} [TopologicalSpace S] [T2Space S] {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V]
    (src dst : E → V) (v : V → S) (hv : Function.Injective v)
    (p : (e : E) → Path (v (src e)) (v (dst e)))
    (hp : ∀ e, Function.Injective (p e)) (hne : ∀ e, src e ≠ dst e)
    (hc : ∀ e f, e ≠ f → ∀ s t : unitInterval,
      p e s = p f t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1))
    (c : E → ℤ)
    (hbal : ∀ w, (∑ e, if src e = w then c e else 0) =
      ∑ e, if dst e = w then c e else 0) :
    ∃ (n : ℕ) (curves : Fin n → Curve S)
      (cycles : Fin n → ((TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ)),
      (∀ i, cycles i ∈ absoluteSingularCycles (TopCat.of Circle) 1) ∧
      ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of S) 1 B =
          (∑ e, c e • Finsupp.single (edgeSimplex (p e).toContinuousMap 0 1) 1) -
          ∑ i, singularFinsuppPush
            (TopCat.ofHom (⟨(curves i).map,(curves i).embedded.continuous⟩ : C(Circle,S)))
            1 (cycles i) := by
  classical
  obtain ⟨L,hL,hcoef⟩ := signed_flow_finite_cycle_resolution src dst c hbal
  let C (i : Fin L.length) := L[i.val]
  have hC (i : Fin L.length) : C i ∈ L := List.getElem_mem i.isLt
  have hcircle (i : Fin L.length) := resolved_signed_graph_cycle_is_pushed_circle_cycle
    src dst v hv p hp hne hc c L hL (C i) (hC i)
  choose curves cycles hcycles hpush using hcircle
  let f (e : E) := Finsupp.single (edgeSimplex (p e).toContinuousMap 0 1) (1 : ℤ)
  have hraw : (∑ i : Fin L.length, rawSignedCycleValue src dst f (C i)) =
      ∑ e, c e • f e := by
    calc
      _ = (L.map (rawSignedCycleValue src dst f)).sum := by
        simpa only [C] using Fin.sum_univ_fun_getElem L (rawSignedCycleValue src dst f)
      _ = _ := resolved_signed_raw_values_sum src dst f c L hcoef
  refine ⟨L.length,curves,cycles,hcycles,
    -(∑ i : Fin L.length, cycleReversalCorrection src dst v p (C i)), ?_⟩
  rw [map_neg,map_sum]
  simp_rw [cycleReversalCorrection_boundary,← hpush]
  rw [Finset.sum_sub_distrib,hraw]
  abel

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology.SquareChains
open CurveComplex CurveComplexGenusTwo.CWHurewicz CategoryTheory Convexity
open CurveComplexGenusTwo.SourceTopology.PathChains
open scoped Simplicial

noncomputable def squareSimplex {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (n : ℕ)
    (V : Fin (n+1) → unitInterval × unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋n⦌)).symm {
    toFun := fun z => H (weightedTime n (fun i => (V i).1) z,
      weightedTime n (fun i => (V i).2) z)
    continuous_toFun := H.continuous.comp
      ((weightedTime n (fun i => (V i).1)).continuous.prodMk
        (weightedTime n (fun i => (V i).2)).continuous) }

noncomputable def squareEdge {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b : unitInterval × unitInterval) :=
  squareSimplex H 1 ![a,b]
noncomputable def squareTriangle {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b c : unitInterval × unitInterval) :=
  squareSimplex H 2 ![a,b,c]

private theorem square_face0 {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b c : unitInterval × unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 0 (squareTriangle H a b c) = squareEdge H b c := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change H (weightedTime 2 (fun k => (![a,b,c] k).1) (z.map (0 : Fin 3).succAbove),
    weightedTime 2 (fun k => (![a,b,c] k).2) (z.map (0 : Fin 3).succAbove)) =
    H (weightedTime 1 (fun k => (![b,c] k).1) z,
      weightedTime 1 (fun k => (![b,c] k).2) z)
  apply congrArg H
  apply Prod.ext <;> apply Subtype.ext
  all_goals simp [weightedTime, StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_fintype, Fin.sum_univ_two, Fin.sum_univ_three]

private theorem square_face1 {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b c : unitInterval × unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 1 (squareTriangle H a b c) = squareEdge H a c := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change H (weightedTime 2 (fun k => (![a,b,c] k).1) (z.map (1 : Fin 3).succAbove),
    weightedTime 2 (fun k => (![a,b,c] k).2) (z.map (1 : Fin 3).succAbove)) =
    H (weightedTime 1 (fun k => (![a,c] k).1) z,
      weightedTime 1 (fun k => (![a,c] k).2) z)
  apply congrArg H
  apply Prod.ext <;> apply Subtype.ext
  all_goals simp [weightedTime, StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_fintype, Fin.sum_univ_two, Fin.sum_univ_three]

private theorem square_face2 {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b c : unitInterval × unitInterval) :
    (TopCat.toSSet.obj (TopCat.of S)).δ 2 (squareTriangle H a b c) = squareEdge H a b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change H (weightedTime 2 (fun k => (![a,b,c] k).1) (z.map (2 : Fin 3).succAbove),
    weightedTime 2 (fun k => (![a,b,c] k).2) (z.map (2 : Fin 3).succAbove)) =
    H (weightedTime 1 (fun k => (![a,b] k).1) z,
      weightedTime 1 (fun k => (![a,b] k).2) z)
  apply congrArg H
  apply Prod.ext <;> apply Subtype.ext
  all_goals have hh : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  all_goals simp [weightedTime, StdSimplex.weights_map, Finsupp.mapDomain,
    Finsupp.sum_fintype, Fin.sum_univ_two, Fin.sum_univ_three, hh]

theorem squareTriangle_boundary {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b c : unitInterval × unitInterval) :
    singularBoundaryFinsupp (TopCat.of S) 1 (Finsupp.single (squareTriangle H a b c) 1) =
      Finsupp.single (squareEdge H b c) 1 - Finsupp.single (squareEdge H a c) 1 +
        Finsupp.single (squareEdge H a b) 1 := by
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, square_face0, square_face1, square_face2]
  abel

private theorem weightedTime_constant (n : ℕ) (t : unitInterval)
    (z : StdSimplex ℝ (Fin (n+1))) : weightedTime n (fun _ => t) z = t := by
  apply Subtype.ext
  change (∑ i, z.weights i * (t : ℝ)) = t
  rw [← Finset.sum_mul]
  have hz := z.total
  rw [Finsupp.sum_fintype] at hz <;> simp_all

private theorem weightedTime_pair_constant (t : unitInterval)
    (z : StdSimplex ℝ (Fin 2)) : weightedTime 1 ![t,t] z = t := by
  have h : (![t,t] : Fin 2 → unitInterval) = fun _ => t := by
    funext i; fin_cases i <;> rfl
  rw [h]
  exact weightedTime_constant 1 t z

private theorem squareEdge_eval {S : Type} [TopologicalSpace S]
    (H : C(unitInterval × unitInterval,S)) (a b : unitInterval × unitInterval)
    (z : StdSimplex ℝ (Fin 2)) :
    TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) (squareEdge H a b) z =
      H (weightedTime 1 ![a.1,b.1] z, weightedTime 1 ![a.2,b.2] z) := by
  change H (weightedTime 1 (fun i => (![a,b] i).1) z,
    weightedTime 1 (fun i => (![a,b] i).2) z) = _
  congr 2 <;> (funext i; fin_cases i <;> rfl)

/-- An actual endpoint-fixed path homotopy has an explicit finite singular
2-chain realizing the difference of its two actual path edges. -/
theorem path_homotopy_edge_difference_fills
    {S : Type} [TopologicalSpace S] {a b : S}
    (p q : Path a b) (hpq : Path.Homotopic p q) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B =
        Finsupp.single (edgeSimplex q.toContinuousMap 0 1) 1 -
          Finsupp.single (edgeSimplex p.toContinuousMap 0 1) 1 := by
  obtain ⟨H⟩ := hpq
  let F : C(unitInterval × unitInterval,S) := H.toHomotopy.toContinuousMap
  let A : unitInterval × unitInterval := (0,0)
  let B : unitInterval × unitInterval := (1,0)
  let C : unitInterval × unitInterval := (1,1)
  let D : unitInterval × unitInterval := (0,1)
  have hAB : squareEdge F A B = squareEdge F A A := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    rw [squareEdge_eval, squareEdge_eval]
    simp only [A, B, Prod.fst, Prod.snd, weightedTime_pair_constant]
    exact (H.source _).trans (H.source _).symm
  have hCD : squareEdge F C D = squareEdge F C C := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    rw [squareEdge_eval, squareEdge_eval]
    simp only [C, D, Prod.fst, Prod.snd, weightedTime_pair_constant]
    exact (H.target _).trans (H.target _).symm
  have hBC : squareEdge F B C = edgeSimplex q.toContinuousMap 0 1 := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    rw [squareEdge_eval]
    simp only [B, C, Prod.fst, Prod.snd, weightedTime_pair_constant]
    change H (1, weightedTime 1 ![0,1] z) = q (weightedTime 1 ![0,1] z)
    exact H.apply_one _
  have hAD : squareEdge F A D = edgeSimplex p.toContinuousMap 0 1 := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    rw [squareEdge_eval]
    simp only [A, D, Prod.fst, Prod.snd, weightedTime_pair_constant]
    change H (0, weightedTime 1 ![0,1] z) = p (weightedTime 1 ![0,1] z)
    exact H.apply_zero _
  refine ⟨Finsupp.single (squareTriangle F A B C) 1 +
    Finsupp.single (squareTriangle F A C D) 1 -
    Finsupp.single (squareTriangle F A A A) 1 -
    Finsupp.single (squareTriangle F C C C) 1, ?_⟩
  rw [map_sub, map_sub, map_add]
  simp only [squareTriangle_boundary, hAB, hCD, hBC, hAD]
  abel

end CurveComplexGenusTwo.SourceTopology.SquareChains

namespace CurveComplexGenusTwo.SourceTopology.PathChains
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz Convexity
open scoped Simplicial

/-- The actual interval path associated to a singular 1-simplex using the
canonical standard-simplex/interval homeomorphism. -/
noncomputable def singularSimplexPath {S : Type} [TopologicalSpace S]
    (a : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌) :
    Path ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 0))
      ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 1)) where
  toFun t := TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a (StdSimplex.homeomorphI.symm t)
  continuous_toFun := (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a).continuous.comp
    StdSimplex.homeomorphI.symm.continuous
  source' := by
    congr 1
    apply StdSimplex.homeomorphI.injective
    simp
  target' := by
    congr 1
    apply StdSimplex.homeomorphI.injective
    simp

/-- The original singular simplex equals its actual canonical path edge,
not merely its homology class. -/
theorem singularSimplexPath_edge_eq {S : Type} [TopologicalSpace S]
    (a : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌) :
    edgeSimplex (singularSimplexPath a).toContinuousMap 0 1 = a := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a)
    (StdSimplex.homeomorphI.symm (weightedTime 1 ![0,1] z)) = _
  apply congrArg (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a)
  apply StdSimplex.homeomorphI.injective
  rw [StdSimplex.homeomorphI.apply_symm_apply]
  apply Subtype.ext
  change ((weightedTime 1 ![0,1] z) : ℝ) = z.weights 1
  simp [weightedTime,Fin.sum_univ_two]

theorem singular_simplex_path_homotopy_correction
    {S : Type} [TopologicalSpace S]
    (a : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌)
    (q : Path ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 0))
      ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 1)))
    (hq : Path.Homotopic (singularSimplexPath a) q) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B =
        Finsupp.single (edgeSimplex q.toContinuousMap 0 1) 1 - Finsupp.single a 1 := by
  obtain ⟨B,hB⟩ := SquareChains.path_homotopy_edge_difference_fills (singularSimplexPath a) q hq
  rw [singularSimplexPath_edge_eq] at hB
  exact ⟨B,hB⟩

end CurveComplexGenusTwo.SourceTopology.PathChains

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Topology Set CategoryTheory CurveComplexGenusTwo.CWHurewicz
open PathChains Convexity
open scoped Simplicial

/-- An actual loop carried by a convex chart ball is endpoint-fixed homotopic
to the actual constant loop. -/
theorem chart_ball_loop_homotopic_refl
    {S : Type} [TopologicalSpace S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
    (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball center r ⊆ e.target)
    {a : S} (q : Path a a)
    (hq : ∀ t, q t ∈ e.source ∧ e (q t) ∈ Metric.ball center r) :
    Path.Homotopic q (Path.refl a) := by
  have ha : a ∈ e.source ∧ e a ∈ Metric.ball center r := by simpa using hq 0
  let B := Metric.ball center r
  let Q : Path (⟨e a,ha.2⟩ : B) (⟨e a,ha.2⟩ : B) := {
    toFun := fun t => ⟨e (q t),(hq t).2⟩
    continuous_toFun := (e.continuousOn.comp_continuous q.continuous
      (fun t => (hq t).1)).subtype_mk _
    source' := by apply Subtype.ext; simp
    target' := by apply Subtype.ext; simp }
  let inverse : C(B,S) := ⟨fun x => e.symm x,
    e.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => hball x.property)⟩
  have hea : a = inverse ⟨e a,ha.2⟩ := (e.left_inv ha.1).symm
  letI : ContractibleSpace B := Metric.contractibleSpace_ball hr
  have H := Path.Homotopic.pathCast
    ((SimplyConnectedSpace.paths_homotopic Q (Path.refl _)).map inverse) hea hea
  have hQ : (Q.map inverse.continuous).cast hea hea = q := by
    ext t
    exact e.left_inv (hq t).1
  have hR : ((Path.refl (⟨e a,ha.2⟩ : B)).map inverse.continuous).cast hea hea = Path.refl a := by
    ext t
    exact e.left_inv ha.1
  rwa [hQ,hR] at H

/-- An actual singular1simplex with equal endpoints carried by one convex
chart ball has an actual finite singular2filling in the source surface. -/
theorem chart_small_closed_singular_simplex_fills
    {S : Type} [TopologicalSpace S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
    (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball center r ⊆ e.target)
    (a : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌)
    (hends : ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 0)) =
      ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 1)))
    (ha : ∀ z, TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a z ∈ e.source ∧
      e (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a z) ∈ Metric.ball center r) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B = Finsupp.single a 1 := by
  let x := (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) a) (.single 0)
  let q : Path x x := (singularSimplexPath a).cast rfl hends
  have hq : Path.Homotopic q (Path.refl x) := chart_ball_loop_homotopic_refl
    e center r hr hball q (fun t => ha (StdSimplex.homeomorphI.symm t))
  obtain ⟨B,hB⟩ := SquareChains.path_homotopy_edge_difference_fills q (Path.refl x) hq
  have he : edgeSimplex q.toContinuousMap 0 1 = a := singularSimplexPath_edge_eq a
  rw [he] at hB
  let f : C(unitInterval,S) := ContinuousMap.const _ x
  have hconst : edgeSimplex (Path.refl x).toContinuousMap 0 1 = edgeSimplex f 0 0 := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    rfl
  refine ⟨Finsupp.single (triangleSimplex f 0 0 0) 1 - B, ?_⟩
  rw [map_sub,triangle_boundary,hB,hconst]
  abel

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex.BranchedDoubleCover

/-- Consecutive distinct cut times of an injective source arc give genuine
injective graph-edge paths, with distinct actual endpoint images. -/
theorem actual_cut_subpath_injective
    {S : Type} [TopologicalSpace S] {x y : S} (p : Path x y)
    (hp : Function.Injective p) (a b : unitInterval) (hab : a < b) :
    Function.Injective (actualSubpath p a b) ∧ p a ≠ p b := by
  constructor
  · intro s t heq
    have he := congrArg (fun u : unitInterval => (u : ℝ)) (hp heq)
    change (1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ) =
      (1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ) at he
    have hlt : (a : ℝ) < (b : ℝ) := hab
    apply Subtype.ext
    nlinarith
  · exact fun he => hab.ne (hp he)

/-- Interior parameters of an actual cut subpath stay strictly between its
original cut times. -/
theorem actual_cut_subpath_interior_parameter
    (a b u : unitInterval) (hab : a < b) (hu0 : 0 < u) (hu1 : u < 1) :
    a < intervalAffine a b u ∧ intervalAffine a b u < b := by
  have hab' : (a : ℝ) < (b : ℝ) := hab
  have hu0' : (0 : ℝ) < (u : ℝ) := hu0
  have hu1' : (u : ℝ) < 1 := hu1
  change (a : ℝ) < (1-(u:ℝ))*(a:ℝ)+(u:ℝ)*(b:ℝ) ∧
    (1-(u:ℝ))*(a:ℝ)+(u:ℝ)*(b:ℝ) < (b:ℝ)
  constructor <;> nlinarith [mul_pos hu0' (sub_pos.mpr hab'),
    mul_pos (sub_pos.mpr hu1') (sub_pos.mpr hab')]

end CurveComplexGenusTwo.SourceTopology


namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex.BranchedDoubleCover

private theorem intervalAffine_bounds (a b u : unitInterval) (hab : a ≤ b) :
    a ≤ intervalAffine a b u ∧ intervalAffine a b u ≤ b := by
  have ha : (a : ℝ) ≤ b := hab
  have hu0 := u.property.1
  have hu1 := u.property.2
  change (a : ℝ) ≤ (1-(u:ℝ))*(a:ℝ)+(u:ℝ)*(b:ℝ) ∧
    (1-(u:ℝ))*(a:ℝ)+(u:ℝ)*(b:ℝ) ≤ (b:ℝ)
  constructor <;> nlinarith [mul_nonneg hu0 (sub_nonneg.mpr ha),
    mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr ha)]

/-- Distinct consecutive cut edges of one embedded arc can meet only at their
own endpoints. -/
theorem same_arc_cut_edges_endpoint_intersection
    {S : Type} [TopologicalSpace S] {a b : S} (p : Path a b)
    (hp : Function.Injective p) (n : ℕ) (t : Fin (n+1) → unitInterval)
    (ht : StrictMono t) (i j : Fin n) (hij : i ≠ j)
    (s u : unitInterval)
    (he : actualSubpath p (t i.castSucc) (t i.succ) s =
      actualSubpath p (t j.castSucc) (t j.succ) u) :
    (s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1) := by
  have eq : intervalAffine (t i.castSucc) (t i.succ) s =
      intervalAffine (t j.castSucc) (t j.succ) u := hp he
  have habi : t i.castSucc < t i.succ := ht (by simp)
  have habj : t j.castSucc < t j.succ := ht (by simp)
  have bdi := intervalAffine_bounds _ _ s habi.le
  have bdj := intervalAffine_bounds _ _ u habj.le
  have single {i j : Fin n} (hij : i ≠ j) {s u : unitInterval}
      (eq : intervalAffine (t i.castSucc) (t i.succ) s =
        intervalAffine (t j.castSucc) (t j.succ) u) : s = 0 ∨ s = 1 := by
    by_contra hend
    have hs0 : s ≠ 0 := fun h => hend (Or.inl h)
    have hs1 : s ≠ 1 := fun h => hend (Or.inr h)
    have hs0' : (0 : unitInterval) < s :=
      lt_of_le_of_ne (show (0 : unitInterval) ≤ s from s.property.1) hs0.symm
    have hs1' : s < (1 : unitInterval) :=
      lt_of_le_of_ne (show s ≤ (1 : unitInterval) from s.property.2) hs1
    have hinside := actual_cut_subpath_interior_parameter (t i.castSucc) (t i.succ) s
      (ht (by simp)) hs0' hs1'
    have bd := intervalAffine_bounds (t j.castSucc) (t j.succ) u (ht (by simp)).le
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hstep : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        omega
      have hsep := ht.monotone hstep
      rw [eq] at hinside
      exact (not_lt_of_ge (le_trans hsep bd.1)) hinside.2
    · have hstep : j.succ ≤ i.castSucc := by
        change j.val + 1 ≤ i.val
        omega
      have hsep := ht.monotone hstep
      rw [eq] at hinside
      exact (not_lt_of_ge (le_trans bd.2 hsep)) hinside.1
  exact ⟨single hij eq, single hij.symm eq.symm⟩

/-- The actual finite-position contact cuts produce graph edges whose pairwise
intersections occur only at their endpoints. -/
theorem contact_cut_graph_edges_endpoint_intersection
    {S : Type} [TopologicalSpace S] (m : ℕ) (a b : Fin m → S)
    (p : (i : Fin m) → Path (a i) (b i))
    (hp : ∀ i, Function.Injective (p i)) (n : Fin m → ℕ)
    (t : (i : Fin m) → Fin (n i + 1) → unitInterval)
    (ht : ∀ i, StrictMono (t i))
    (havoid : ∀ i (k : Fin (n i)) (u : unitInterval),
      t i k.castSucc < u → u < t i k.succ →
      ∀ j, i ≠ j → p i u ∉ Set.range (p j))
    (e f : Σ i : Fin m, Fin (n i)) (hne : e ≠ f)
    (s u : unitInterval)
    (he : actualSubpath (p e.1) (t e.1 e.2.castSucc) (t e.1 e.2.succ) s =
      actualSubpath (p f.1) (t f.1 f.2.castSucc) (t f.1 f.2.succ) u) :
    (s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1) := by
  rcases e with ⟨i,k⟩
  rcases f with ⟨j,l⟩
  by_cases hij : i = j
  · subst j
    exact same_arc_cut_edges_endpoint_intersection (p i) (hp i) (n i) (t i) (ht i)
      k l (fun h => hne (by cases h; rfl)) s u he
  · have single (i j : Fin m) (hij : i ≠ j) (k : Fin (n i)) (l : Fin (n j))
        (s u : unitInterval)
        (he : actualSubpath (p i) (t i k.castSucc) (t i k.succ) s =
          actualSubpath (p j) (t j l.castSucc) (t j l.succ) u) : s = 0 ∨ s = 1 := by
      by_contra hend
      have hs0 : s ≠ 0 := fun h => hend (Or.inl h)
      have hs1 : s ≠ 1 := fun h => hend (Or.inr h)
      have hs0' : (0 : unitInterval) < s :=
        lt_of_le_of_ne (show (0 : unitInterval) ≤ s from s.property.1) hs0.symm
      have hs1' : s < (1 : unitInterval) :=
        lt_of_le_of_ne (show s ≤ (1 : unitInterval) from s.property.2) hs1
      have hi := actual_cut_subpath_interior_parameter (t i k.castSucc) (t i k.succ) s
        (ht i (by simp)) hs0' hs1'
      exact havoid i k _ hi.1 hi.2 j hij
        ⟨intervalAffine (t j l.castSucc) (t j l.succ) u, he.symm⟩
    exact ⟨single i j hij k l s u he, single j i (Ne.symm hij) l k u s he.symm⟩

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology.PathChains
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz Convexity
open CurveComplex.BranchedDoubleCover
open scoped Simplicial

/-- Actual affine subpaths agree exactly with their singular path-edge bases. -/
theorem actualSubpath_edgeSimplex_eq
    {S : Type} [TopologicalSpace S] {x y : S} (p : Path x y) (a b : unitInterval) :
    edgeSimplex (actualSubpath p a b).toContinuousMap 0 1 = edgeSimplex p.toContinuousMap a b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
  ext z
  change p (intervalAffine a b (weightedTime 1 ![0,1] z)) =
    p (weightedTime 1 ![a,b] z)
  apply congrArg p
  apply Subtype.ext
  have htotal : z.weights 0 + z.weights 1 = 1 := by
    have ht := z.total
    rw [Finsupp.sum_fintype] at ht <;> simpa [Fin.sum_univ_two] using ht
  dsimp [intervalAffine,weightedTime]
  simp only [Fin.sum_univ_two]
  norm_num
  left
  linarith

/-- An actual finite ordered path cutting has a finite singular2correction to
its actual constituent cut-edge paths. -/
theorem finite_actual_path_cut_correction
    {S : Type} [TopologicalSpace S] {x y : S} (p : Path x y)
    (n : ℕ) (t : Fin (n+1) → unitInterval)
    (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B =
        (∑ k : Fin n, Finsupp.single (edgeSimplex
          (actualSubpath p (t k.castSucc) (t k.succ)).toContinuousMap 0 1) 1) -
        Finsupp.single (edgeSimplex p.toContinuousMap 0 1) 1 := by
  classical
  let T : ℕ → unitInterval := fun k => if hk : k < n+1 then t ⟨k,hk⟩ else 1
  have T0 : T 0 = 0 := by simpa [T] using ht0
  have Tn : T n = 1 := by
    dsimp [T]
    rw [dif_pos (by omega)]
    convert ht1 using 1
    congr 1
  refine ⟨splitCorrection p.toContinuousMap T n, ?_⟩
  rw [splitCorrection_boundary,T0,Tn]
  apply congrArg (fun c => c - Finsupp.single (edgeSimplex p.toContinuousMap 0 1) 1)
  calc
    (∑ i ∈ Finset.range n, Finsupp.single
        (edgeSimplex p.toContinuousMap (T i) (T (i+1))) 1) =
        ∑ k : Fin n, Finsupp.single
          (edgeSimplex p.toContinuousMap (T k.val) (T (k.val+1))) 1 :=
      (Fin.sum_univ_eq_sum_range (fun i => Finsupp.single
        (edgeSimplex p.toContinuousMap (T i) (T (i+1))) (1 : ℤ)) n).symm
    _ = ∑ k : Fin n, Finsupp.single (edgeSimplex
        (actualSubpath p (t k.castSucc) (t k.succ)).toContinuousMap 0 1) 1 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [actualSubpath_edgeSimplex_eq]
      have hk := k.isLt
      simp only [T,dif_pos (show k.val < n+1 by omega),
        dif_pos (show k.val+1 < n+1 by omega)]
      congr 3 <;> apply Fin.ext <;> rfl

end CurveComplexGenusTwo.SourceTopology.PathChains

namespace CurveComplexGenusTwo.SourceTopology.PathChains
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz Convexity
open scoped Simplicial

theorem vertexSimplex_injective {S : Type} [TopologicalSpace S] :
    Function.Injective (vertexSimplex (S := S)) := by
  intro x y h
  exact congrArg (fun a => TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋0⦌) a (.single 0)) h

/-- Boundary-zero of the actual weighted graph edge chain gives literal signed
incidence balance at every actual graph vertex. -/
theorem actual_graph_edge_chain_incidence_balance
    {S : Type} [TopologicalSpace S] {V E : Type*} [Fintype E] [DecidableEq V]
    (src dst : E → V) (v : V → S) (hv : Function.Injective v)
    (p : (e : E) → Path (v (src e)) (v (dst e))) (c : E → ℤ)
    (hcycle : singularBoundaryFinsupp (TopCat.of S) 0
      (∑ e, c e • Finsupp.single (edgeSimplex (p e).toContinuousMap 0 1) 1) = 0) :
    ∀ w, (∑ e, if src e = w then c e else 0) =
      ∑ e, if dst e = w then c e else 0 := by
  classical
  have hd (e : E) : singularBoundaryFinsupp (TopCat.of S) 0
      (Finsupp.single (edgeSimplex (p e).toContinuousMap 0 1) 1) =
      Finsupp.single (vertexSimplex (v (dst e))) 1 -
        Finsupp.single (vertexSimplex (v (src e))) 1 := by
    have h := edgeSimplex_boundary (p e).toContinuousMap 0 1
    change _ = Finsupp.single (vertexSimplex ((p e) 1)) 1 -
      Finsupp.single (vertexSimplex ((p e) 0)) 1 at h
    simpa only [Path.target,Path.source] using h
  rw [map_sum] at hcycle
  simp_rw [map_smul,hd] at hcycle
  intro w
  have hp (a : V) : vertexSimplex (v a) = vertexSimplex (v w) ↔ a = w :=
    (vertexSimplex_injective.comp hv).eq_iff
  have hp' (a : V) : vertexSimplex (v w) = vertexSimplex (v a) ↔ a = w := by
    rw [eq_comm,hp]
  have hz := congrArg (fun a => a (vertexSimplex (v w))) hcycle
  simp only [Finsupp.finsetSum_apply,Finsupp.smul_apply,Pi.smul_apply,smul_eq_mul,
    Finsupp.sub_apply,Finsupp.single_apply,hp,hp',Finsupp.zero_apply] at hz
  have he (e : E) : c e * ((if dst e = w then 1 else 0) - (if src e = w then 1 else 0)) =
      (if dst e = w then c e else 0) - (if src e = w then c e else 0) := by
    split_ifs <;> ring
  simp_rw [he] at hz
  rw [Finset.sum_sub_distrib] at hz
  exact (sub_eq_zero.mp hz).symm

end CurveComplexGenusTwo.SourceTopology.PathChains

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Topology Set

/-- A genuine source path in one convex-ball chart can be straightened relative
endpoints; distinct endpoints give an embedded arc in the original surface. -/
theorem chart_ball_path_straightening
    {S : Type} [TopologicalSpace S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)))
    (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball center r ⊆ e.target)
    {a b : S} (q : Path a b)
    (hq : ∀ t, q t ∈ e.source ∧ e (q t) ∈ Metric.ball center r) :
    ∃ p : Path a b, Path.Homotopic q p ∧
      (a ≠ b → Function.Injective p) ∧
      ∀ t, p t ∈ e.source ∧ e (p t) ∈ Metric.ball center r := by
  have ha : a ∈ e.source ∧ e a ∈ Metric.ball center r := by simpa using hq 0
  have hb : b ∈ e.source ∧ e b ∈ Metric.ball center r := by simpa using hq 1
  let B := Metric.ball center r
  let Q : Path (⟨e a, ha.2⟩ : B) (⟨e b, hb.2⟩ : B) := {
    toFun := fun t => ⟨e (q t), (hq t).2⟩
    continuous_toFun := (e.continuousOn.comp_continuous q.continuous
      (fun t => (hq t).1)).subtype_mk _
    source' := by apply Subtype.ext; simp
    target' := by apply Subtype.ext; simp }
  let line := Path.segment (e a) (e b)
  have hline (t : unitInterval) : line t ∈ B := by
    apply (convex_ball center r).segment_subset ha.2 hb.2
    rw [← Path.range_segment]
    exact ⟨t, rfl⟩
  let L : Path (⟨e a, ha.2⟩ : B) (⟨e b, hb.2⟩ : B) := {
    toFun := fun t => ⟨line t, hline t⟩
    continuous_toFun := line.continuous.subtype_mk _
    source' := by apply Subtype.ext; exact line.source
    target' := by apply Subtype.ext; exact line.target }
  let inverse : C(B,S) := ⟨fun x => e.symm x,
    e.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => hball x.property)⟩
  have hea : a = inverse ⟨e a,ha.2⟩ := (e.left_inv ha.1).symm
  have heb : b = inverse ⟨e b,hb.2⟩ := (e.left_inv hb.1).symm
  let p : Path a b := (L.map inverse.continuous).cast hea heb
  letI : ContractibleSpace B := Metric.contractibleSpace_ball hr
  have H := Path.Homotopic.pathCast
    ((SimplyConnectedSpace.paths_homotopic Q L).map inverse) hea heb
  have hQ : (Q.map inverse.continuous).cast hea heb = q := by
    ext t
    exact e.left_inv (hq t).1
  refine ⟨p, ?_, ?_, ?_⟩
  · rwa [hQ] at H
  · intro hne s t hst
    have hcoord : line s = line t :=
      e.symm.injOn (hball (hline s)) (hball (hline t)) hst
    apply Path.segment_injective_of_ne (show e a ≠ e b from
      fun heq => hne (e.injOn ha.1 hb.1 heq))
    exact hcoord
  · intro t
    exact ⟨e.map_target (hball (hline t)), by
      change e (e.symm (line t)) ∈ B
      rw [e.right_inv (hball (hline t))]
      exact hline t⟩

end CurveComplexGenusTwo.SourceTopology


namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Set

/-- A finite-position family of actual injective arcs has a finite ordered cut
set containing every crossing and both endpoints. Consecutive open pieces of
one arc then avoid every other entire arc. -/
theorem finite_position_arc_contact_subdivision
    {S : Type} [TopologicalSpace S]
    (m : ℕ) (a b : Fin m → S) (p : (i : Fin m) → Path (a i) (b i))
    (hp : ∀ i, Function.Injective (p i))
    (hposition : ∀ i j, i ≠ j → (Set.range (p i) ∩ Set.range (p j)).Finite)
    (i : Fin m) :
    ∃ (n : ℕ) (t : Fin (n+1) → unitInterval), StrictMono t ∧
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      (∀ j, i ≠ j → ∀ u v, p i u = p j v → ∃ k, t k = u) ∧
      ∀ (k : Fin n) (u : unitInterval), t k.castSucc < u → u < t k.succ →
        ∀ j, i ≠ j → p i u ∉ Set.range (p j) := by
  classical
  let C : Set unitInterval := {u | ∃ j, i ≠ j ∧ p i u ∈ Set.range (p j)}
  have hfinite : C.Finite := by
    have single (j : Fin m) : {u : unitInterval | i ≠ j ∧ p i u ∈ Set.range (p j)}.Finite := by
      by_cases hij : i = j
      · simp [hij]
      · have hf := Set.Finite.preimage (hp i).injOn (hposition i j hij)
        have he : (p i) ⁻¹' (Set.range (p i) ∩ Set.range (p j)) =
            {u : unitInterval | i ≠ j ∧ p i u ∈ Set.range (p j)} := by
          ext u
          simp [hij, Set.mem_range_self]
        rwa [he] at hf
    have hf := Set.finite_iUnion single
    apply hf.subset
    intro u hu
    obtain ⟨j,hij,hup⟩ := hu
    exact Set.mem_iUnion.mpr ⟨j,hij,hup⟩
  let T := insert (0 : unitInterval) (insert 1 hfinite.toFinset)
  have hzero : (0 : unitInterval) ∈ T := by simp [T]
  have hone : (1 : unitInterval) ∈ T := by simp [T]
  have hcard : 0 < T.card := Finset.card_pos.mpr ⟨0,hzero⟩
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let e := T.orderIsoOfFin hn
  let t : Fin (n+1) → unitInterval := fun k => e k
  have hmono : StrictMono t := e.strictMono
  have ht0 : t 0 = 0 := by
    have hmin : t 0 ≤ 0 := by
      let j := e.symm ⟨0,hzero⟩
      have hh := e.monotone (Fin.zero_le j)
      change t 0 ≤ (e j : unitInterval) at hh
      simpa [j] using hh
    exact le_antisymm hmin (unitInterval.nonneg _)
  have ht1 : t (Fin.last n) = 1 := by
    have hmax : 1 ≤ t (Fin.last n) := by
      let j := e.symm ⟨1,hone⟩
      have hh := e.monotone (Fin.le_last j)
      change (e j : unitInterval) ≤ t (Fin.last n) at hh
      simpa [j] using hh
    exact le_antisymm (unitInterval.le_one _) hmax
  have hcontacts (j : Fin m) (hij : i ≠ j) (u v : unitInterval)
      (heq : p i u = p j v) : ∃ k, t k = u := by
    have hu : u ∈ C := ⟨j,hij,v,heq.symm⟩
    have huT : u ∈ T := by simp only [T,Finset.mem_insert]; exact Or.inr (Or.inr (hfinite.mem_toFinset.mpr hu))
    obtain ⟨k,hk⟩ := e.surjective ⟨u,huT⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  refine ⟨n,t,hmono,ht0,ht1,hcontacts,?_⟩
  intro k u hleft hright j hij hmem
  obtain ⟨v,hv⟩ := hmem
  obtain ⟨l,hl⟩ := hcontacts j hij u v hv.symm
  by_cases hle : l ≤ k.castSucc
  · have hh := hmono.monotone hle
    rw [hl] at hh
    exact (not_le_of_gt hleft) hh
  · have hge : k.succ ≤ l := by
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ] at hle ⊢
      omega
    have hh := hmono.monotone hge
    rw [hl] at hh
    exact (not_le_of_gt hright) hh

end CurveComplexGenusTwo.SourceTopology


namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz Topology Convexity
open scoped Simplicial

noncomputable local instance (n : ℕ) : MetricSpace (StdSimplex ℝ (Fin (n + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).comapMetricSpace
    (fun t => (t.weights : Fin (n + 1) → ℝ))

private theorem uniform_cover_scale {X : Type} [TopologicalSpace X]
    {J : Type} (U : J → Set X) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, x ∈ U j) (n : ℕ)
    (fs : List C(StdSimplex ℝ (Fin (n+1)), X)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ fs, ∀ x : StdSimplex ℝ (Fin (n+1)),
      ∃ j, f '' Metric.ball x δ ⊆ U j := by
  have single (f : C(StdSimplex ℝ (Fin (n+1)), X)) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : StdSimplex ℝ (Fin (n+1)),
        ∃ j, f '' Metric.ball x δ ⊆ U j := by
    let c : J → Set (StdSimplex ℝ (Fin (n+1))) := fun j => f ⁻¹' U j
    have hopen : ∀ j, IsOpen (c j) := fun j => (hU j).preimage f.continuous
    have hc : Set.univ ⊆ ⋃ j, c j := by
      intro x _
      obtain ⟨j, hj⟩ := hcover (f x)
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hc
    refine ⟨δ, hδ, fun x => ?_⟩
    obtain ⟨j, hj⟩ := hballs x (Set.mem_univ x)
    exact ⟨j, Set.image_subset_iff.mpr hj⟩
  induction fs with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons f fs ih =>
    obtain ⟨δf, hδf, hf⟩ := single f
    obtain ⟨δs, hδs, hs⟩ := ih
    refine ⟨min δf δs, lt_min hδf hδs, ?_⟩
    intro g hg x
    rcases List.mem_cons.mp hg with rfl | hg
    · obtain ⟨j,hj⟩ := hf x
      exact ⟨j, (Set.image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hj⟩
    · obtain ⟨j,hj⟩ := hs g hg x
      exact ⟨j, (Set.image_mono (Metric.ball_subset_ball (min_le_right _ _))).trans hj⟩

private theorem subdivision_subordinate_to_open_cover
    (X : TopCat) {J : Type} (U : J → Set X) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ x, ∃ j, x ∈ U j) (n : ℕ)
    (chain : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ) :
    ∃ k : ℕ, ∀ y ∈ (singularBarycentricIterate X n k chain).support,
      ∃ j, Set.range (TopCat.toSSetObjEquiv X (.op ⦋n⦌) y) ⊆ U j := by
  classical
  let fs := chain.support.toList.map (fun x => TopCat.toSSetObjEquiv X (.op ⦋n⦌) x)
  obtain ⟨δ,hδ,hscale⟩ := uniform_cover_scale U hU hcover n fs
  obtain ⟨k,hk⟩ := barycentricFlagIterate_eventually_small n δ hδ
  have hiter (j : ℕ) : singularBarycentricIterateList X n j chain =
      singularBarycentricIterate X n j chain := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [singularBarycentricIterateList,
        singularBarycentricIterate_succ, ih]
  refine ⟨k, ?_⟩
  intro y hy
  rw [← hiter k] at hy
  obtain ⟨x,hx,ss,hlen,rfl⟩ := singularBarycentricIterateList_support X n k chain y hy
  have hfx : TopCat.toSSetObjEquiv X (.op ⦋n⦌) x ∈ fs :=
    List.mem_map.mpr ⟨x, by simpa using hx, rfl⟩
  let t : StdSimplex ℝ (Fin (n+1)) := .single 0
  obtain ⟨j,hj⟩ := hscale _ hfx (barycentricFlagIterate n ss t)
  refine ⟨j, ?_⟩
  rintro z ⟨u,rfl⟩
  rw [singularFlagIterate_eval]
  apply hj
  refine ⟨barycentricFlagIterate n ss u, ?_, rfl⟩
  exact Metric.mem_ball.mpr (hk ss hlen u t)

theorem finite_type_sum_dite {A B : Type*} [Fintype A] [AddCommMonoid B]
    {p : A → Prop} [DecidablePred p]
    (f : ∀ a, p a → B) (g : ∀ a, ¬p a → B) :
    (∑ a, dite (p a) (f a) (g a)) =
      (∑ a : {a // p a}, f a a.property) + ∑ a : {a // ¬p a}, g a a.property := by
  simp only [Finset.sum_dite]
  congr 1
  · exact (Equiv.subtypeEquivRight (by simp)).sum_comp
      (fun a : {a // p a} => f a a.property)
  · exact (Equiv.subtypeEquivRight (by simp)).sum_comp
      (fun a : {a // ¬p a} => g a a.property)

-- Exact approved source target; no new decomposition assumption is present.
theorem source_singular_one_cycle_straightening
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (chain : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌ →₀ ℤ)
    (hchain : singularBoundaryFinsupp (TopCat.of S) 0 chain = 0) :
    ∃ (n : ℕ) (curves : Fin n → Curve S)
      (cycles : Fin n → ((TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ)),
      (∀ i, cycles i ∈ absoluteSingularCycles (TopCat.of Circle) 1) ∧
      ∃ b₀ : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of S) 1 b₀ = chain -
          ∑ i, singularFinsuppPush
            (TopCat.ofHom ⟨(curves i).map, (curves i).embedded.continuous⟩) 1 (cycles i) := by
  classical
  obtain ⟨hsurface⟩ := hS.2.1
  letI : ClosedSurface S := hsurface
  let P := EuclideanSpace ℝ (Fin 2)
  let E (p : S) := chartAt P p
  have hballs (p : S) : ∃ r : ℝ, 0 < r ∧ Metric.ball (E p p) r ⊆ (E p).target :=
    Metric.isOpen_iff.mp (E p).open_target (E p p)
      ((E p).map_source (mem_chart_source P p))
  choose r hr hrtarget using hballs
  let U (p : S) : Set S := (E p).source ∩ (E p) ⁻¹' Metric.ball (E p p) (r p)
  have hU (p : S) : IsOpen (U p) :=
    (E p).continuousOn.isOpen_inter_preimage (E p).open_source Metric.isOpen_ball
  have hcover (x : S) : ∃ p, x ∈ U p := by
    exact ⟨x, mem_chart_source P x, Metric.mem_ball_self (hr x)⟩
  obtain ⟨k,hsmall⟩ := subdivision_subordinate_to_open_cover
    (TopCat.of S) U hU hcover 1 chain
  let small := singularBarycentricIterate (TopCat.of S) 1 k chain
  have hsmallCycle : singularBoundaryFinsupp (TopCat.of S) 0 small = 0 := by
    rw [singularBarycentricIterate_boundary, hchain, map_zero]
  let h := singularCarrierHomotopyIterate (TopCat.of S) 1 k chain
  have hhom : singularBoundaryFinsupp (TopCat.of S) 1 h = small - chain := by
    have hh := singularCarrierHomotopyIterate_boundary_succ (TopCat.of S) 0 k chain
    rw [hchain, map_zero, add_zero] at hh
    exact hh
  have hedge (edge : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌)
      (hedge : edge ∈ small.support) :
      ∃ p : Path
          ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge) (.single 0))
          ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge) (.single 1)),
        Path.Homotopic
          (PathChains.singularSimplexPath edge) p ∧
        (((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge) (.single 0)) ≠
          ((TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge) (.single 1)) →
          Function.Injective p) := by
    obtain ⟨v,hv⟩ := hsmall edge hedge
    let f := TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge
    let q := PathChains.singularSimplexPath edge
    have hq (t : unitInterval) : q t ∈ (E v).source ∧
        E v (q t) ∈ Metric.ball (E v v) (r v) :=
      hv ⟨StdSimplex.homeomorphI.symm t, rfl⟩
    obtain ⟨p,hp,hinj,hrange⟩ := chart_ball_path_straightening
      (E v) (E v v) (r v) (hr v) (hrtarget v) q hq
    exact ⟨p,hp,hinj⟩
  let Edge := {edge : ↑small.support //
    (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge.val) (.single 0) ≠
      (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge.val) (.single 1)}
  let F (edge : Edge) := TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge.val.val
  have hchoose (edge : Edge) : ∃ p : Path (F edge (.single 0)) (F edge (.single 1)),
      Path.Homotopic
        (PathChains.singularSimplexPath edge.val.val) p ∧ Function.Injective p := by
    obtain ⟨p,hp,hinj⟩ := hedge edge.val.val edge.val.property
    exact ⟨p,hp,hinj edge.property⟩
  choose edgePath hEdgePathHom hEdgePathInj using hchoose
  let M := Fintype.card Edge
  let enum : Fin M → Edge := (Fintype.equivFin Edge).symm
  let endpointsA (i : Fin M) := F (enum i) (.single 0)
  let endpointsB (i : Fin M) := F (enum i) (.single 1)
  let paths (i : Fin M) : Path (endpointsA i) (endpointsB i) := edgePath (enum i)
  have hends (i : Fin M) : endpointsA i ≠ endpointsB i := (enum i).property
  have hpaths (i : Fin M) : Function.Injective (paths i) := hEdgePathInj (enum i)
  -- Verified original finite-position source theorem imported from frozen release
  -- in this package until the independent finite-position owner's proof closes.
  obtain ⟨positioned,hpositionHom,hpositionInj,hpositionFinite⟩ :=
    source_finite_embedded_arcs_finite_position S g hg hS M
      endpointsA endpointsB paths hends hpaths
  have cutData (i : Fin M) := finite_position_arc_contact_subdivision
    M endpointsA endpointsB positioned hpositionInj hpositionFinite i
  choose subdivisions cuts hcutsStrict hcutsZero hcutsOne hcutsContacts hcutsAvoid using cutData
  -- Remaining genuine geometry: replace this chart-small finite cycle by
  -- a finite embedded graph, resolve its integer cycle into embedded circles,
  -- and produce the correction 2-chain. hsmall gives actual convex-ball charts.
  have hgraph : ∃ (n : ℕ) (curves : Fin n → Curve S)
      (cycles : Fin n → ((TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ)),
      (∀ i, cycles i ∈ absoluteSingularCycles (TopCat.of Circle) 1) ∧
      ∃ b : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of S) 1 b = small -
          ∑ i, singularFinsuppPush
            (TopCat.ofHom ⟨(curves i).map, (curves i).embedded.continuous⟩) 1 (cycles i) := by
    let Pieces := Σ i : Fin M, Fin (subdivisions i)
    let rawSource (e : Pieces) := positioned e.1 (cuts e.1 e.2.castSucc)
    let rawTarget (e : Pieces) := positioned e.1 (cuts e.1 e.2.succ)
    let Z : Set S := Set.range rawSource ∪ Set.range rawTarget
    have hZ : Z.Finite := (Set.finite_range rawSource).union (Set.finite_range rawTarget)
    let V := Z
    letI : Fintype V := hZ.fintype
    let src (e : Pieces) : V := ⟨rawSource e,Or.inl ⟨e,rfl⟩⟩
    let dst (e : Pieces) : V := ⟨rawTarget e,Or.inr ⟨e,rfl⟩⟩
    let v : V → S := Subtype.val
    let arcs (e : Pieces) : Path (v (src e)) (v (dst e)) :=
      CurveComplex.BranchedDoubleCover.actualSubpath (positioned e.1)
        (cuts e.1 e.2.castSucc) (cuts e.1 e.2.succ)
    let coeff (e : Pieces) : ℤ := small (enum e.1).val.val
    have hlt (e : Pieces) : cuts e.1 e.2.castSucc < cuts e.1 e.2.succ :=
      hcutsStrict e.1 (by simp)
    have hinj (e : Pieces) : Function.Injective (arcs e) :=
      (actual_cut_subpath_injective (positioned e.1) (hpositionInj e.1) _ _ (hlt e)).1
    have hne (e : Pieces) : src e ≠ dst e := by
      intro he
      exact (actual_cut_subpath_injective (positioned e.1) (hpositionInj e.1) _ _
        (hlt e)).2 (congrArg Subtype.val he)
    have hcross : ∀ e f, e ≠ f → ∀ s t : unitInterval,
        arcs e s = arcs f t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) :=
      contact_cut_graph_edges_endpoint_intersection M endpointsA endpointsB positioned
        hpositionInj subdivisions cuts hcutsStrict hcutsAvoid
    let graphChain := ∑ e : Pieces, coeff e •
      Finsupp.single (PathChains.edgeSimplex (arcs e).toContinuousMap 0 1) (1 : ℤ)
    have hcutApprox : ∃ correction :
        (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
        singularBoundaryFinsupp (TopCat.of S) 1 correction = small - graphChain := by
      let cutSum (i : Fin M) := ∑ k : Fin (subdivisions i),
        Finsupp.single (PathChains.edgeSimplex
          (CurveComplex.BranchedDoubleCover.actualSubpath (positioned i)
            (cuts i k.castSucc) (cuts i k.succ)).toContinuousMap 0 1) (1 : ℤ)
      have hgood (edge : Edge) : ∃ B :
          (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of S) 1 B = Finsupp.single edge.val.val 1 -
            cutSum ((Fintype.equivFin Edge) edge) := by
        let i := (Fintype.equivFin Edge) edge
        have hen : enum i = edge := (Fintype.equivFin Edge).symm_apply_apply edge
        have H := (hEdgePathHom (enum i)).trans (hpositionHom i)
        obtain ⟨B,hB⟩ := PathChains.singular_simplex_path_homotopy_correction
          (enum i).val.val (positioned i) H
        obtain ⟨Bcut,hBcut⟩ := PathChains.finite_actual_path_cut_correction
          (positioned i) (subdivisions i) (cuts i) (hcutsZero i) (hcutsOne i)
        refine ⟨-(B+Bcut),?_⟩
        rw [map_neg,map_add,hB,hBcut]
        change -(Finsupp.single (PathChains.edgeSimplex (positioned i).toContinuousMap 0 1) 1 -
          Finsupp.single (enum i).val.val 1 +
          (cutSum i - Finsupp.single (PathChains.edgeSimplex (positioned i).toContinuousMap 0 1) 1)) =
          Finsupp.single edge.val.val 1 - cutSum i
        rw [hen]
        abel
      let Good (edge : ↑small.support) :=
        (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge.val) (.single 0) ≠
          (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌) edge.val) (.single 1)
      let slot (edge : ↑small.support) := if he : Good edge then
        cutSum ((Fintype.equivFin Edge) ⟨edge,he⟩) else 0
      have hall (edge : ↑small.support) : ∃ B :
          (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of S) 1 B = Finsupp.single edge.val 1 - slot edge := by
        by_cases he : Good edge
        · simpa only [slot,dif_pos he] using hgood ⟨edge,he⟩
        · obtain ⟨w,hw⟩ := hsmall edge.val edge.property
          obtain ⟨B,hB⟩ := chart_small_closed_singular_simplex_fills
            (E w) (E w w) (r w) (hr w) (hrtarget w) edge.val
            (not_ne_iff.mp he) (fun z => hw ⟨z,rfl⟩)
          exact ⟨B,by simpa only [slot,dif_neg he,sub_zero] using hB⟩
      choose correction hcorrection using hall
      have hrep : (∑ edge : ↑small.support, small edge.val • Finsupp.single edge.val (1 : ℤ)) = small := by
        simp only [Finsupp.smul_single,smul_eq_mul,mul_one]
        exact (Finset.sum_coe_sort small.support (fun a => Finsupp.single a (small a))).trans
          (Finsupp.sum_single small)
      have hslots : (∑ edge : ↑small.support, small edge.val • slot edge) = graphChain := by
        have hd (edge : ↑small.support) : small edge.val • slot edge =
            if he : Good edge then small edge.val •
              cutSum ((Fintype.equivFin Edge) ⟨edge,he⟩) else 0 := by
          by_cases he : Good edge <;> simp [slot,he]
        simp_rw [hd]
        rw [finite_type_sum_dite]
        simp only [Finset.sum_const_zero,add_zero]
        change (∑ edge : Edge, small edge.val.val • cutSum ((Fintype.equivFin Edge) edge)) = graphChain
        calc
          _ = ∑ i : Fin M, small (enum i).val.val • cutSum i :=
            Fintype.sum_equiv (Fintype.equivFin Edge) _ _ (fun edge => by simp [enum])
          _ = graphChain := by
            dsimp [graphChain,coeff,arcs,Pieces]
            rw [Fintype.sum_sigma]
            simp only [cutSum,Finset.smul_sum]
      refine ⟨∑ edge : ↑small.support, small edge.val • correction edge,?_⟩
      rw [map_sum]
      simp_rw [map_smul,hcorrection,smul_sub]
      rw [Finset.sum_sub_distrib,hrep,hslots]
    obtain ⟨correction,hcorrection⟩ := hcutApprox
    have hgraphCycle : singularBoundaryFinsupp (TopCat.of S) 0 graphChain = 0 := by
      have hh := singularBoundaryFinsupp_comp_zero (TopCat.of S) 0 correction
      rw [hcorrection,map_sub,hsmallCycle] at hh
      simpa only [zero_sub,neg_eq_zero] using hh
    have hbal := PathChains.actual_graph_edge_chain_incidence_balance src dst v
      Subtype.val_injective arcs coeff hgraphCycle
    obtain ⟨n,curves,cycles,hcycles,B,hB⟩ := actual_finite_embedded_graph_cycle_resolves
      src dst v Subtype.val_injective arcs hinj hne hcross coeff hbal
    refine ⟨n,curves,cycles,hcycles,correction+B,?_⟩
    rw [map_add,hcorrection,hB]
    change small - graphChain + (graphChain - _) = _
    abel
  obtain ⟨n,curves,cycles,hcycles,b,hb⟩ := hgraph
  refine ⟨n,curves,cycles,hcycles,b-h, ?_⟩
  rw [map_sub,hb,hhom]
  abel

end CurveComplexGenusTwo.SourceTopology

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex Topology CategoryTheory
open CurveComplexGenusTwo.CWHurewicz

/-- An actual disk bounded by an embedded source circle gives a nullhomotopy
of its actual parametrization, without fixing a boundary parametrization. -/
theorem boundsDisc_curveMap_nullhomotopic
    {S : Type} [TopologicalSpace S] (c : Curve S) (hc : BoundsDisc c) :
    (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic := by
  classical
  obtain ⟨f, hf, hboundary⟩ := hc
  let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hpre (t : Circle) : ∃ x : B, f x = c.map t := by
    have ht : c.map t ∈ c.image := ⟨t, rfl⟩
    rw [← hboundary] at ht
    obtain ⟨x, hx, hfx⟩ := ht
    exact ⟨x, hfx⟩
  let lift : Circle → B := fun t => Classical.choose (hpre t)
  have heq : (f : B → S) ∘ lift = c.map :=
    funext (fun t => Classical.choose_spec (hpre t))
  have hcont : Continuous lift := hf.continuous_iff.mpr (by
    rw [heq]
    exact c.embedded.continuous)
  let l : C(Circle, B) := ⟨lift, hcont⟩
  letI : ContractibleSpace B := Metric.contractibleSpace_closedBall (by norm_num)
  have hnull := (id_nullhomotopic B).comp_right f |>.comp_left l
  have hm : (f.comp (ContinuousMap.id B)).comp l =
      (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)) := by
    ext t
    exact Classical.choose_spec (hpre t)
  rwa [hm] at hnull

open scoped Simplicial

/-- Every actual singular circle cycle mapped by a disk-bounding source curve
has an actual finite singular filling in the original surface. -/
theorem boundsDisc_singularCircleCycle_fills
    {S : Type} [TopologicalSpace S] (c : Curve S) (hc : BoundsDisc c)
    (z : (TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ)
    (hz : z ∈ absoluteSingularCycles (TopCat.of Circle) 1) :
    ∃ b : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 b =
        singularFinsuppPush (TopCat.ofHom ⟨c.map, c.embedded.continuous⟩) 1 z := by
  obtain ⟨y, ⟨H⟩⟩ := boundsDisc_curveMap_nullhomotopic c hc
  exact CurveComplex.WeightedFlowScratch.singularFinsupp_cycle_fills_of_nullhomotopy
    (TopCat.ofHom ⟨c.map, c.embedded.continuous⟩) y H 1 (by omega) z hz

end CurveComplexGenusTwo.SourceTopology


namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial

-- Exact approved endpoint; the finite singular-cycle surface surgery remains open.
theorem source_essential_curve_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) :
    ∃ c : Curve S, Essential c := by
  classical
  obtain ⟨hsurface⟩ := hS.2.1
  letI : ClosedSurface S := hsurface
  obtain ⟨e⟩ := hS.2.2.2
  let u : Fin (2 * g) → ℤ := fun _ => 1
  have hnonzero : e.inv u ≠ 0 := by
    intro hz
    have hu : u = 0 := by
      calc
        u = e.hom (e.inv u) := (e.toLinearEquiv.apply_symm_apply u).symm
        _ = 0 := by rw [hz, map_zero]
    have hi := congrFun hu (⟨0, by omega⟩ : Fin (2 * g))
    norm_num [u] at hi
  by_contra hessential
  have hdisks (c : Curve S) : BoundsDisc c := by
    by_contra hn
    exact hessential ⟨c, hn⟩
  let r := singularHomologyRepresentation (TopCat.of S) 1
  have hnonzeroF : r.inv (e.inv u) ≠ 0 := by
    intro hz
    apply hnonzero
    have hi : r.hom (r.inv (e.inv u)) = e.inv u :=
      r.toLinearEquiv.apply_symm_apply (e.inv u)
    rw [hz] at hi
    change r.hom.hom 0 = e.inv u at hi
    rw [map_zero] at hi
    exact hi.symm
  let C := mvAmbientComplex (TopCat.of S)
  have hπ : Function.Surjective (C.homologyπ 1) :=
    (ModuleCat.epi_iff_surjective (C.homologyπ 1)).mp inferInstance
  obtain ⟨z, hz⟩ := hπ (r.inv (e.inv u))
  let chain : (TopCat.toSSet.obj (TopCat.of S)) _⦋1⦌ →₀ ℤ := C.iCycles 1 z
  have hchainCycle : singularBoundaryFinsupp (TopCat.of S) 0 chain = 0 := by
    have hi := congrArg (fun f => f z) (C.iCycles_d 1 0)
    change singularBoundaryFinsupp (TopCat.of S) 0 chain = 0 at hi
    exact hi
  have hfill : ∃ b : C.X 2, C.d 2 1 b = C.iCycles 1 z := by
    -- Exact outstanding surface geometry: straighten the finite cycle into a
    -- finite sum of embedded circle cycles, with an actual singular homotopy chain.
    have hstraight : ∃ (n : ℕ) (curves : Fin n → Curve S)
        (cycles : Fin n → ((TopCat.toSSet.obj (TopCat.of Circle)) _⦋1⦌ →₀ ℤ)),
        (∀ i, cycles i ∈ absoluteSingularCycles (TopCat.of Circle) 1) ∧
        ∃ b₀ : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
          singularBoundaryFinsupp (TopCat.of S) 1 b₀ = chain -
            ∑ i, singularFinsuppPush
              (TopCat.ofHom ⟨(curves i).map, (curves i).embedded.continuous⟩) 1 (cycles i) := by
      exact source_singular_one_cycle_straightening S g hg hS chain hchainCycle
    obtain ⟨n, curves, cycles, hcycles, b₀, hb₀⟩ := hstraight
    have hcircles (i : Fin n) := boundsDisc_singularCircleCycle_fills
      (curves i) (hdisks (curves i)) (cycles i) (hcycles i)
    choose fillings hfillings using hcircles
    refine ⟨b₀ + ∑ i, fillings i, ?_⟩
    change singularBoundaryFinsupp (TopCat.of S) 1 (b₀ + ∑ i, fillings i) = chain
    rw [map_add, map_sum, hb₀]
    simp_rw [hfillings]
    exact sub_add_cancel _ _
  obtain ⟨b, hb⟩ := hfill
  apply hnonzeroF
  apply (ModuleCat.mono_iff_injective (C.homologyι 1)).mp inferInstance
  rw [← hz]
  change C.homologyι 1 (C.homologyπ 1 z) = (C.homologyι 1).hom 0
  rw [map_zero]
  have hident := congrArg (fun f => f z) (C.homology_π_ι 1)
  change C.homologyι 1 (C.homologyπ 1 z) = C.pOpcycles 1 (C.iCycles 1 z) at hident
  rw [hident, ← hb]
  have hzero := congrArg (fun f => f b) (C.d_pOpcycles 2 1)
  change C.pOpcycles 1 (C.d 2 1 b) = 0 at hzero
  exact hzero

end CurveComplexGenusTwo.SourceTopology
