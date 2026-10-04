import Schoenflies.Graph.Walk
import Mathlib
import Schoenflies.GeneralCrosscut
import Schoenflies.Concatenate
import Schoenflies.Subarc
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import Schoenflies.JordanClosed
import Schoenflies.Endgame
import Schoenflies.Graph.CycleJordan
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Path
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChartSelection
import CurveComplexGenusTwo.Topology.IntersectionParity.TwoCrossingsActual
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates




namespace CurveComplex.LocalSurgery
/-- Realize an actual walk while retaining an edge constraint supplied by each
actual adjacency, such as containment of every drawn edge in a closed cap. -/
theorem actual_simple_graph_walk_to_labeled_graph_with_edge_constraint
    {V E X : Type*} (G : SimpleGraph V) (H : Graph X E) (f : V → X)
    (R : E → Prop) (hvertex : ∀ v, f v ∈ H.vertexSet)
    (hlink : ∀ {v w}, G.Adj v w → ∃ e, H.IsLink e (f v) (f w) ∧ R e)
    {v w : V} (p : G.Walk v w) :
    ∃ W, H.IsWalk (f v) W (f w) ∧ ∀ e ∈ W, R e := by
  induction p with
  | nil => exact ⟨[],Graph.IsWalk.nil (hvertex _),by simp⟩
  | cons hadj p ih =>
    obtain ⟨e,he,hR⟩ := hlink hadj
    obtain ⟨W,hW,hconstraint⟩ := ih
    refine ⟨e :: W,Graph.IsWalk.cons he hW,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hR
    · exact hconstraint q hq
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
/-- Join a real cap walk to the visited part of a real returning path, then
shorten the joined walk while retaining every edge's cap constraint. -/
theorem actual_drawn_cap_path_join_at_visited_vertex
    {X E : Type*} (H : Graph X E) (R : E → Prop)
    {r y a b : X} {U W : List E}
    (hU : H.IsWalk r U y) (hW : H.IsPath a W b)
    (hy : y ∈ H.walkVertices a W)
    (hRU : ∀ e ∈ U, R e) (hRW : ∀ e ∈ W, R e) :
    ∃ P, H.IsPath r P b ∧ ∀ e ∈ P, R e := by
  obtain ⟨T,hT,hTW⟩ := hW.from_visited hy
  obtain ⟨P,hP,hPsub⟩ := (hU.append hT.isWalk).contains_path
  refine ⟨P,hP,?_⟩
  intro e he
  rcases List.mem_append.mp (hPsub he) with heU | heT
  · exact hRU e heU
  · exact hRW e (hTW heT)
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
open Set Topology Schoenflies unitInterval
/-- An actual extra boundary event splits the selected cut arc and produces
its proper prefix and a new complementary boundary arc. Both arcs are constructed. -/
theorem actual_boundary_cut_pair_split_at_interior_event
    {C A B : Set Plane} {a b z : Plane} (hcut : IsCutPair C a b A B)
    (hzA : z ∈ A) (hza : z ≠ a) (hzb : z ≠ b) :
    ∃ R T S U : Set Plane, IsCutPair C z a R T ∧ IsCutPair C z b S U ∧
      R ⊆ A ∧ S ⊆ A ∧ R ∪ S = A ∧ b ∉ R ∧ a ∉ S := by
  obtain ⟨f,hfc,hfi,hfA,hf0,hf1⟩ := hcut.fst
  obtain ⟨t,htI,hft⟩ := (hfA.symm ▸ hzA : z ∈ f '' I)
  have ht0 : 0 < t := by
    by_contra h
    have he : t = 0 := le_antisymm (le_of_not_gt h) htI.1
    rw [he,hf0] at hft
    exact hza hft.symm
  have ht1 : t < 1 := by
    by_contra h
    have he : t = 1 := le_antisymm htI.2 (le_of_not_gt h)
    rw [he,hf1] at hft
    exact hzb hft.symm
  let R := f '' Icc 0 t
  let S := f '' Icc t 1
  have hR : IsArcBetween R z a := by
    have h := isArcBetween_subarc_of_injOn_I hfc hfi htI zero_mem_I (ne_of_gt ht0)
    simpa only [uIcc_of_ge ht0.le,hft,hf0] using h
  have hS : IsArcBetween S z b := by
    have h := isArcBetween_subarc_of_injOn_I hfc hfi htI one_mem_I (ne_of_lt ht1)
    simpa only [uIcc_of_le ht1.le,hft,hf1] using h
  have hRsub : R ⊆ A := by
    rintro x ⟨r,hr,he⟩
    exact hfA ▸ ⟨r,⟨hr.1,hr.2.trans htI.2⟩,he⟩
  have hSsub : S ⊆ A := by
    rintro x ⟨r,hr,he⟩
    exact hfA ▸ ⟨r,⟨htI.1.trans hr.1,hr.2⟩,he⟩
  have hbR : b ∉ R := by
    rintro ⟨r,hr,he⟩
    have hrI : r ∈ I := ⟨hr.1,hr.2.trans htI.2⟩
    have hr1 : r = 1 := hfi hrI one_mem_I (he.trans hf1.symm)
    rw [hr1] at hr
    exact (not_le_of_gt ht1) hr.2
  have haS : a ∉ S := by
    rintro ⟨r,hr,he⟩
    have hrI : r ∈ I := ⟨htI.1.trans hr.1,hr.2⟩
    have hr0 : r = 0 := hfi hrI zero_mem_I (he.trans hf0.symm)
    rw [hr0] at hr
    exact (not_le_of_gt ht0) hr.1
  have hsplit : R ∪ S = A := by
    dsimp [R,S]
    rw [←image_union,Icc_union_Icc_eq_Icc ht0.le ht1.le]
    exact hfA
  have hRS : R ∩ S = {z} := by
    ext x
    constructor
    · rintro ⟨⟨r,hr,hfr⟩,⟨s,hs,hfs⟩⟩
      have hrI : r ∈ I := ⟨hr.1,hr.2.trans htI.2⟩
      have hsI : s ∈ I := ⟨htI.1.trans hs.1,hs.2⟩
      have hrs : r = s := hfi hrI hsI (hfr.trans hfs.symm)
      have hrt : r = t := le_antisymm hr.2 (hrs ▸ hs.1)
      rw [hrt,hft] at hfr
      exact hfr.symm
    · intro hx
      have he : x = z := hx
      subst x
      exact ⟨⟨t,⟨htI.1,le_rfl⟩,hft⟩,⟨t,⟨le_rfl,htI.2⟩,hft⟩⟩
  have hRB : R ∩ B = {a} := by
    ext x
    constructor
    · rintro ⟨hxR,hxB⟩
      have hx : x ∈ ({a,b} : Set Plane) := hcut.inter_eq ▸ ⟨hRsub hxR,hxB⟩
      rcases (by simpa using hx : x = a ∨ x = b) with hxa | hxb
      · exact hxa
      · exact False.elim (hbR (hxb ▸ hxR))
    · intro hx
      have he : x = a := hx
      subst x
      exact ⟨hR.right_mem,hcut.snd.left_mem⟩
  have hSB : S ∩ B = {b} := by
    ext x
    constructor
    · rintro ⟨hxS,hxB⟩
      have hx : x ∈ ({a,b} : Set Plane) := hcut.inter_eq ▸ ⟨hSsub hxS,hxB⟩
      rcases (by simpa using hx : x = a ∨ x = b) with hxa | hxb
      · exact False.elim (haS (hxa ▸ hxS))
      · exact hxb
    · intro hx
      have he : x = b := hx
      subst x
      exact ⟨hS.right_mem,hcut.snd.right_mem⟩
  have hT : IsArcBetween (S ∪ B) z a := hS.concatenate hcut.snd.reverse (by
    intro x hxS hxB
    exact (show x ∈ ({b} : Set Plane) from hSB ▸ ⟨hxS,hxB⟩))
  have hU : IsArcBetween (R ∪ B) z b := hR.concatenate hcut.snd (by
    intro x hxR hxB
    exact (show x ∈ ({a} : Set Plane) from hRB ▸ ⟨hxR,hxB⟩))
  have hFirst : IsCutPair C z a R (S ∪ B) := by
    refine ⟨hR,hT,?_,?_⟩
    · rw [←union_assoc,hsplit,hcut.union_eq]
    · rw [inter_union_distrib_left,hRS,hRB]
      ext x
      simp [or_comm]
  have hSecond : IsCutPair C z b S (R ∪ B) := by
    refine ⟨hS,hU,?_,?_⟩
    · rw [←union_assoc,union_comm S R,hsplit,hcut.union_eq]
    · rw [inter_union_distrib_left,inter_comm S R,hRS,hSB]
      ext x
      simp [or_comm]
  exact ⟨R,S ∪ B,S,R ∪ B,hFirst,hSecond,hRsub,hSsub,hsplit,hbR,haS⟩
/-- Two actual interior events determine a real smaller boundary cut pair,
whose selected arc lies in the old one and avoids both old endpoints. -/
theorem actual_boundary_cut_pair_between_interior_events
    {C A B : Set Plane} {a b z y : Plane} (hcut : IsCutPair C a b A B)
    (hzA : z ∈ A) (hyA : y ∈ A) (hzy : z ≠ y)
    (hza : z ≠ a) (hzb : z ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    ∃ R T, IsCutPair C z y R T ∧ R ⊆ A ∧ a ∉ R ∧ b ∉ R := by
  obtain ⟨R,T,S,U,hR,hS,hRA,hSA,hunion,hbR,haS⟩ :=
    actual_boundary_cut_pair_split_at_interior_event hcut hzA hza hzb
  have reverseEndpoints {Q D : Set Plane} (h : IsCutPair C y z Q D) :
      IsCutPair C z y Q D := by
    refine ⟨h.fst.reverse,h.snd.reverse,h.union_eq,?_⟩
    rw [h.inter_eq]
    ext x
    simp [or_comm]
  by_cases hyR : y ∈ R
  · obtain ⟨Q,D,L,M,hQ,hL,hQR,hLR,hunion',haQ,hzL⟩ :=
      actual_boundary_cut_pair_split_at_interior_event hR hyR hzy.symm hya
    refine ⟨Q,D,reverseEndpoints hQ,hQR.trans hRA,haQ,?_⟩
    exact fun hb => hbR (hQR hb)
  · have hyS : y ∈ S := (hunion.symm ▸ hyA : y ∈ R ∪ S).resolve_left hyR
    obtain ⟨Q,D,L,M,hQ,hL,hQS,hLS,hunion',hbQ,hzL⟩ :=
      actual_boundary_cut_pair_split_at_interior_event hS hyS hzy.symm hyb
    refine ⟨Q,D,reverseEndpoints hQ,hQS.trans hSA,?_,hbQ⟩
    exact fun ha => haS (hQS ha)
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
attribute [local instance] Classical.propDecidable
/-- A returning boundary subarc between actual interior events decreases the
finite old event count when it excludes both old endpoints. -/
theorem actual_interior_boundary_subarc_event_count_strict_decrease
    {X : Type*} [DecidableEq X] (E : Finset X) (A R : Set X) (a b z y : X)
    (hzE : z ∈ E) (hzA : z ∈ A) (hza : z ≠ a) (hzb : z ≠ b)
    (hRA : R ⊆ A) (haR : a ∉ R) (hbR : b ∉ R) :
    (E.filter (fun x => x ∈ R ∧ x ≠ z ∧ x ≠ y)).card <
      (E.filter (fun x => x ∈ A ∧ x ≠ a ∧ x ≠ b)).card := by
  have hsub : E.filter (fun x => x ∈ R ∧ x ≠ z ∧ x ≠ y) ⊆
      E.filter (fun x => x ∈ A ∧ x ≠ a ∧ x ≠ b) := by
    intro x hx
    obtain ⟨hxE,hxR,hxz,hxy⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxE,hRA hxR,?_,?_⟩
    · intro hxa
      exact haR (hxa ▸ hxR)
    · intro hxb
      exact hbR (hxb ▸ hxR)
  have hzOld : z ∈ E.filter (fun x => x ∈ A ∧ x ≠ a ∧ x ≠ b) :=
    Finset.mem_filter.mpr ⟨hzE,hzA,hza,hzb⟩
  have hzNew : z ∉ E.filter (fun x => x ∈ R ∧ x ≠ z ∧ x ≠ y) := by
    intro hz
    exact (Finset.mem_filter.mp hz).2.2.1 rfl
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_subset_ne).mpr ⟨hsub,fun he => hzNew (he.symm ▸ hzOld)⟩
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
open Set Topology Schoenflies
theorem actual_boundary_subarc_returning_cap_nested_general_endpoints
    {C A P R Q : Set Plane} {a b z y : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hAC : A ⊆ C) (hPi : P \ {a,b} ⊆ inside C)
    (hR : IsArcBetween R z y) (hRA : R ⊆ A) (hQ : IsArcBetween Q z y)
    (hQi : Q \ {z,y} ⊆ inside C)
    (hQold : Q ⊆ (A ∪ P) ∪ inside (A ∪ P)) :
    IsJordanCurve (R ∪ Q) ∧
      ((R ∪ Q) ∪ inside (R ∪ Q)) ⊆ (A ∪ P) ∪ inside (A ∪ P) := by
  have hOld : IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro x hxA hxP
    by_contra hbad
    have hxne : x ∉ ({a,b} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hPi ⟨hxP,hxne⟩) (hAC hxA)
  have hNew : IsJordanCurve (R ∪ Q) := by
    apply isJordanCurve_union hR hQ
    intro x hxR hxQ
    by_contra hbad
    have hxne : x ∉ ({z,y} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hQi ⟨hxQ,hxne⟩) (hAC (hRA hxR))
  have hboundary : R ∪ Q ⊆ inside (A ∪ P) ∪ (A ∪ P) := by
    intro x hx
    rcases hx with hxR | hxQ
    · exact Or.inr (Or.inl (hRA hxR))
    · exact (hQold hxQ).elim Or.inr Or.inl
  have hinside := CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
    (jordan_curve_theorem hOld) (jordan_curve_theorem hNew) hboundary
  refine ⟨hNew,?_⟩
  intro x hx
  rcases hx with hxB | hxIn
  · exact (hboundary hxB).elim Or.inr Or.inl
  · exact Or.inr (hinside hxIn)

end CurveComplex.LocalSurgery


namespace CurveComplex.LocalSurgery
/-- Recover the actual simple path from an injectively drawn labeled graph,
retaining exactly its visited vertices. -/
theorem actual_labeled_graph_path_to_simple_graph_with_vertices
    {V E X : Type*} (G : SimpleGraph V) (H : Graph X E) (f : V → X)
    (hf : Function.Injective f) (hvertex : H.vertexSet ⊆ Set.range f)
    (hlink : ∀ {v w e}, H.IsLink e (f v) (f w) → G.Adj v w)
    {x y : X} {W : List E} (hW : H.IsPath x W y) :
    ∀ v w, f v = x → f w = y → ∃ p : G.Walk v w,
      p.IsPath ∧ H.walkVertices x W = f '' {u | u ∈ p.support} := by
  induction hW with
  | @nil x hx =>
    intro v w hv hw
    have he : v = w := hf (hv.trans hw.symm)
    subst w
    refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
    subst x
    simp [Graph.walkVertices_nil]
  | @cons x z y e W he hW hnew ih =>
    intro v w hv hw
    obtain ⟨k,hk⟩ := hvertex he.right_mem
    obtain ⟨p,hp,hverts⟩ := ih k w hk hw
    have ha : G.Adj v k := hlink (hv.symm ▸ hk.symm ▸ he)
    have hfresh : v ∉ p.support := by
      intro hm
      apply hnew
      rw [hverts]
      exact ⟨v,hm,hv⟩
    refine ⟨SimpleGraph.Walk.cons ha p,
      (SimpleGraph.Walk.cons_isPath_iff ha p).mpr ⟨hp,hfresh⟩, ?_⟩
    ext q
    constructor
    · intro hq
      rcases Graph.mem_walkVertices_cons he hq with hq | hq
      · exact ⟨v,by simp,hv.trans hq.symm⟩
      · rw [hverts] at hq
        obtain ⟨r,hr,heq⟩ := hq
        exact ⟨r,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hr,heq⟩
    · rintro ⟨r,hr,rfl⟩
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hr
      rcases hr with rfl | hr
      · rw [hv]
        exact Graph.mem_walkVertices_self
      · apply Graph.mem_walkVertices_cons_of_mem he
        rw [hverts]
        exact ⟨r,hr,rfl⟩
end CurveComplex.LocalSurgery



open Set Topology Schoenflies Filter
namespace CurveComplex.LocalSurgery
theorem actual_crosscut_closed_cap_partition
    {C P R₁ R₂ : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C)
    (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b R₁ R₂)
    (hPi : P \ {a, b} ⊆ inside C) :
    (((R₁ ∪ P) ∪ inside (R₁ ∪ P)) ∪
      ((R₂ ∪ P) ∪ inside (R₂ ∪ P)) = C ∪ inside C) ∧
    (((R₁ ∪ P) ∪ inside (R₁ ∪ P)) ∩
      ((R₂ ∪ P) ∪ inside (R₂ ∪ P)) = P) := by
  have hclass := general_crosscut_arbitrary_of_endpoints hC hP hcut hPi
  have hside₁ : inside (R₁ ∪ P) ⊆ inside C \ P := by
    intro x hx
    rw [hclass.1]
    exact Or.inl hx
  have hside₂ : inside (R₂ ∪ P) ⊆ inside C \ P := by
    intro x hx
    rw [hclass.1]
    exact Or.inr hx
  have hPclosed : P ⊆ C ∪ inside C := by
    intro x hx
    by_cases he : x ∈ ({a,b} : Set Plane)
    · rcases (by simpa using he : x=a ∨ x=b) with rfl | rfl
      · exact Or.inl (hcut.fst_subset hcut.fst.left_mem)
      · exact Or.inl (hcut.fst_subset hcut.fst.right_mem)
    · exact Or.inr (hPi ⟨hx,he⟩)
  constructor
  · ext x
    constructor
    · intro hx
      have hx' : x ∈ C ∪ inside C := by
        rcases hx with ((hR₁ | hP₁) | hi₁) | ((hR₂ | hP₂) | hi₂)
        · exact Or.inl (hcut.fst_subset hR₁)
        · exact hPclosed hP₁
        · exact Or.inr (hside₁ hi₁).1
        · exact Or.inl (hcut.snd_subset hR₂)
        · exact hPclosed hP₂
        · exact Or.inr (hside₂ hi₂).1
      exact hx'
    · intro hx
      have hx' : x ∈ C ∪ inside C :=
        hx
      rcases hx' with hxC | hxin
      · have hxb : x ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
        rcases hxb with hR₁ | hR₂
        · exact Or.inl (Or.inl (Or.inl hR₁))
        · exact Or.inr (Or.inl (Or.inl hR₂))
      · by_cases hxP : x ∈ P
        · exact Or.inl (Or.inl (Or.inr hxP))
        · have hinside : x ∈ inside (R₁ ∪ P) ∪ inside (R₂ ∪ P) := by
            rw [← hclass.1]
            exact ⟨hxin, hxP⟩
          rcases hinside with hi₁ | hi₂
          · exact Or.inl (Or.inr hi₁)
          · exact Or.inr (Or.inr hi₂)
  · ext x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      rcases hx₁ with (hR₁ | hP₁) | hi₁
      · rcases hx₂ with (hR₂ | hP₂) | hi₂
        · have hxEnds : x ∈ ({a, b} : Set Plane) :=
            hcut.inter_eq ▸ ⟨hR₁, hR₂⟩
          rcases (by simpa using hxEnds : x = a ∨ x = b) with rfl | rfl
          · exact hP.left_mem
          · exact hP.right_mem
        · exact hP₂
        · exact False.elim (inside_subset_compl (hside₂ hi₂).1 (hcut.fst_subset hR₁))
      · exact hP₁
      · rcases hx₂ with (hR₂ | hP₂) | hi₂
        · exact False.elim (inside_subset_compl (hside₁ hi₁).1 (hcut.snd_subset hR₂))
        · exact hP₂
        · exact False.elim (Set.disjoint_left.1 hclass.2.1 hi₁ hi₂)
    · intro hxP
      exact ⟨Or.inl (Or.inr hxP), Or.inl (Or.inr hxP)⟩


/-- At an interior point of one actual boundary arc, the complementary closed
cap is absent in an open neighborhood. The cap and neighborhood are produced
from the crosscut, rather than supplied as an inside-side certificate. -/
theorem actual_crosscut_boundary_cap_neighborhood
    {C P R₁ R₂ : Set Plane} {a b z : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b R₁ R₂) (hPi : P \ {a,b} ⊆ inside C)
    (hz : z ∈ R₁) (hne : z ∉ ({a,b} : Set Plane)) :
    ∃ U : Set Plane, IsOpen U ∧ z ∈ U ∧
      U ∩ (C ∪ inside C) ⊆ (R₁ ∪ P) ∪ inside (R₁ ∪ P) := by
  have hzC : z ∈ C := hcut.fst_subset hz
  have hzP : z ∉ P := by
    intro hzP
    exact inside_subset_compl (hPi ⟨hzP,hne⟩) hzC
  have hJ₂ : IsJordanCurve (R₂ ∪ P) := by
    apply isJordanCurve_union hcut.snd hP
    intro x hx₂ hxP
    by_contra hbad
    have hxne : x ∉ ({a,b} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hPi ⟨hxP,hxne⟩) (hcut.snd_subset hx₂)
  have hclass := general_crosscut_arbitrary_of_endpoints hC hP hcut hPi
  have hside₂ : inside (R₂ ∪ P) ⊆ inside C \ P := by
    intro x hx
    rw [hclass.1]
    exact Or.inr hx
  have hzOther : z ∉ (R₂ ∪ P) ∪ inside (R₂ ∪ P) := by
    rintro ((hz₂ | hzP') | hzi)
    · exact hne (hcut.inter_eq ▸ ⟨hz,hz₂⟩)
    · exact hzP hzP'
    · exact inside_subset_compl (hside₂ hzi).1 hzC
  let U : Set Plane := ((R₂ ∪ P) ∪ inside (R₂ ∪ P))ᶜ
  refine ⟨U,(isClosed_union_inside (jordan_curve_theorem hJ₂)).isOpen_compl,hzOther,?_⟩
  rintro x ⟨hxU,hxClosed⟩
  have hcover := (actual_crosscut_closed_cap_partition hC hP hcut hPi).1
  rw [←hcover] at hxClosed
  exact hxClosed.resolve_right hxU

/-- Every actual continuous path in the closed Jordan domain starting at such
a boundary point lies in the selected cap for a neighborhood of its start. -/
theorem actual_crosscut_boundary_path_initially_in_cap
    {C P R₁ R₂ : Set Plane} {a b z w : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b R₁ R₂) (hPi : P \ {a,b} ⊆ inside C)
    (hz : z ∈ R₁) (hne : z ∉ ({a,b} : Set Plane))
    (q : Path z w) (hq : Set.range q ⊆ C ∪ inside C) :
    ∀ᶠ t in 𝓝 (0 : unitInterval), q t ∈ (R₁ ∪ P) ∪ inside (R₁ ∪ P) := by
  obtain ⟨U,hU,hzU,hsub⟩ := actual_crosscut_boundary_cap_neighborhood hC hP hcut hPi hz hne
  have htend : Tendsto q (𝓝 (0 : unitInterval)) (𝓝 z) := by
    simpa using q.continuous.tendsto (0 : unitInterval)
  have hnear : ∀ᶠ t in 𝓝 (0 : unitInterval), q t ∈ U := htend.eventually (hU.mem_nhds hzU)
  filter_upwards [hnear] with t ht
  exact hsub ⟨ht,hq ⟨t,rfl⟩⟩

end CurveComplex.LocalSurgery

open Set Topology Schoenflies
namespace CurveComplex.LocalSurgery
/-- A genuine arc whose interior avoids a Jordan boundary and actually meets
the inside has its full closed image in the closed cap. -/
theorem actual_arc_closed_cap_containment_of_interior_hit
    {C A : Set Plane} {p q : Plane} (hC : IsJordanCurve C) (hA : IsArcBetween A p q)
    (hdisjoint : Disjoint (A \ {p,q}) C)
    (hhit : ((A \ {p,q}) ∩ inside C).Nonempty) : A ⊆ C ∪ inside C := by
  have hs := jordan_curve_theorem hC
  have hcover : A \ {p,q} ⊆ inside C ∪ outside C := by
    rw [inside_union_outside]
    exact fun x hx => Set.disjoint_left.mp hdisjoint hx
  have hin : A \ {p,q} ⊆ inside C :=
    hA.isPreconnected_diff.subset_left_of_subset_union hs.isOpen_inside hs.isOpen_outside
      disjoint_inside_outside hcover hhit
  have hclosed : IsClosed (C ∪ inside C) := isClosed_union_inside hs
  have hclosure : closure (A \ {p,q}) ⊆ C ∪ inside C :=
    hclosed.closure_subset_iff.mpr (fun x hx => Or.inr (hin hx))
  intro x hx
  by_cases hp : x = p
  · exact hp ▸ hclosure hA.left_mem_closure_diff
  by_cases hq : x = q
  · exact hq ▸ hclosure hA.right_mem_closure_diff
  exact hclosure (subset_closure ⟨hx,by simpa [hp,hq]⟩)

/-- An actual endpoint in the open cap supplies the interior hit automatically. -/
theorem actual_arc_closed_cap_containment_of_endpoint_inside
    {C A : Set Plane} {p q : Plane} (hC : IsJordanCurve C) (hA : IsArcBetween A p q)
    (hdisjoint : Disjoint (A \ {p,q}) C) (hp : p ∈ inside C) : A ⊆ C ∪ inside C := by
  have hs := jordan_curve_theorem hC
  obtain ⟨z,hzin,hzA⟩ := mem_closure_iff.mp hA.left_mem_closure_diff (inside C) hs.isOpen_inside hp
  exact actual_arc_closed_cap_containment_of_interior_hit hC hA hdisjoint ⟨z,hzA,hzin⟩
end CurveComplex.LocalSurgery
open Set Topology Schoenflies
namespace CurveComplex.LocalSurgery
/-- A genuine zero edge starting at an extra boundary event stays in the
selected closed cap. The inside hit is constructed from endpoint closure and
the actual crosscut neighborhood; it is not a supplied side certificate. -/
theorem actual_crosscut_boundary_arc_stays_in_selected_cap
    {C P R₁ R₂ Q : Set Plane} {a b z w : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b R₁ R₂) (hPi : P \ {a,b} ⊆ inside C)
    (hQ : IsArcBetween Q z w) (hz : z ∈ R₁) (hne : z ∉ ({a,b} : Set Plane))
    (hQi : Q \ {z,w} ⊆ inside C) (hQP : Disjoint (Q \ {z,w}) P) :
    Q ⊆ (R₁ ∪ P) ∪ inside (R₁ ∪ P) := by
  have hJ : IsJordanCurve (R₁ ∪ P) := by
    apply isJordanCurve_union hcut.fst hP
    intro x hx₁ hxP
    by_contra hbad
    have hxne : x ∉ ({a,b} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hPi ⟨hxP,hxne⟩) (hcut.fst_subset hx₁)
  have hdisjoint : Disjoint (Q \ {z,w}) (R₁ ∪ P) := by
    rw [Set.disjoint_left]
    intro x hxQ hxJ
    rcases hxJ with hx₁ | hxP
    · exact inside_subset_compl (hQi hxQ) (hcut.fst_subset hx₁)
    · exact Set.disjoint_left.mp hQP hxQ hxP
  obtain ⟨U,hU,hzU,hsub⟩ := actual_crosscut_boundary_cap_neighborhood hC hP hcut hPi hz hne
  obtain ⟨t,htU,htQ⟩ := mem_closure_iff.mp hQ.left_mem_closure_diff U hU hzU
  have htCap : t ∈ (R₁ ∪ P) ∪ inside (R₁ ∪ P) := hsub ⟨htU,Or.inr (hQi htQ)⟩
  have htIn : t ∈ inside (R₁ ∪ P) :=
    htCap.resolve_left (Set.disjoint_left.mp hdisjoint htQ)
  exact actual_arc_closed_cap_containment_of_interior_hit hJ hQ hdisjoint ⟨t,htQ,htIn⟩
/-- A new actual returning arc contained in the old closed cap, joined to a
proper original boundary subarc, produces a Jordan cap inside the old one. -/
theorem actual_boundary_subarc_returning_cap_nested
    {C A P R Q : Set Plane} {a b z : Plane}
    (hC : IsJordanCurve C) (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hAC : A ⊆ C) (hPi : P \ {a,b} ⊆ inside C)
    (hR : IsArcBetween R z a) (hRA : R ⊆ A) (hQ : IsArcBetween Q z a)
    (hQi : Q \ {z,a} ⊆ inside C)
    (hQold : Q ⊆ (A ∪ P) ∪ inside (A ∪ P)) :
    IsJordanCurve (R ∪ Q) ∧
      ((R ∪ Q) ∪ inside (R ∪ Q)) ⊆ (A ∪ P) ∪ inside (A ∪ P) := by
  have hOld : IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro x hxA hxP
    by_contra hbad
    have hxne : x ∉ ({a,b} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hPi ⟨hxP,hxne⟩) (hAC hxA)
  have hNew : IsJordanCurve (R ∪ Q) := by
    apply isJordanCurve_union hR hQ
    intro x hxR hxQ
    by_contra hbad
    have hxne : x ∉ ({z,a} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hQi ⟨hxQ,hxne⟩) (hAC (hRA hxR))
  have hboundary : R ∪ Q ⊆ inside (A ∪ P) ∪ (A ∪ P) := by
    intro x hx
    rcases hx with hxR | hxQ
    · exact Or.inr (Or.inl (hRA hxR))
    · exact (hQold hxQ).elim Or.inr Or.inl
  have hinside := CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
    (jordan_curve_theorem hOld) (jordan_curve_theorem hNew) hboundary
  refine ⟨hNew,?_⟩
  intro x hx
  rcases hx with hxB | hxIn
  · exact (hboundary hxB).elim Or.inr Or.inl
  · exact Or.inr (hinside hxIn)

end CurveComplex.LocalSurgery

open Set Topology Schoenflies Metric
namespace CurveComplex.LocalSurgery
/-- A Jordan cap contained in the actual closed annulus has strictly annular
interior. This excludes both original cylinder boundaries at interior vertices. -/
theorem actual_annular_jordan_cap_interior_strict_bounds
    {C : Set Plane} (hC : IsJordanCurve C)
    (hbound : ∀ z ∈ C ∪ inside C, 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2)
    {x : Plane} (hx : x ∈ inside C) : 1 < ‖x‖ ∧ ‖x‖ < 2 := by
  have hs := jordan_curve_theorem hC
  have hupper : inside C ⊆ closedBall (0 : Plane) 2 := by
    intro z hz
    simpa only [mem_closedBall,dist_zero_right] using (hbound z (Or.inr hz)).2
  have hupperOpen : inside C ⊆ interior (closedBall (0 : Plane) 2) :=
    hs.isOpen_inside.subset_interior_iff.mpr hupper
  rw [interior_closedBall (0 : Plane) (by norm_num : (2 : ℝ) ≠ 0)] at hupperOpen
  have hlow : inside C ⊆ (ball (0 : Plane) 1)ᶜ := by
    intro z hz hzb
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hzb
    exact (not_lt_of_ge (hbound z (Or.inr hz)).1) hn
  have hlowOpen : inside C ⊆ interior (ball (0 : Plane) 1)ᶜ :=
    hs.isOpen_inside.subset_interior_iff.mpr hlow
  rw [interior_compl,closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)] at hlowOpen
  constructor
  · have hn : ¬ ‖x‖ ≤ 1 := by
      simpa only [Set.mem_compl_iff,mem_closedBall,dist_zero_right] using hlowOpen hx
    exact lt_of_not_ge hn
  · simpa only [mem_ball,dist_zero_right] using hupperOpen hx
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
/-- The handshaking lemma produces another odd vertex in the actual component,
then an actual simple path to it. Useful for following edges inside a selected cap. -/
theorem actual_odd_vertex_has_distinct_path_partner
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (hx : Odd (G.degree x)) :
    ∃ y, y ≠ x ∧ Odd (G.degree y) ∧ ∃ p : G.Walk x y, p.IsPath := by
  classical
  have hpartner : ∃ y, y ≠ x ∧ Odd (G.degree y) ∧ G.Reachable x y := by
    by_contra hn
    let c := G.connectedComponentMk x
    let H := G.induce c.supp
    let xC : c.supp := ⟨x,rfl⟩
    have hdegree (v : c.supp) : H.degree v = G.degree v.val := by
      apply SimpleGraph.degree_induce_of_neighborSet_subset
      intro w hw
      change G.connectedComponentMk w = c
      exact (SimpleGraph.ConnectedComponent.sound hw.reachable).symm.trans v.property
    have hunique (v : c.supp) (hv : Odd (H.degree v)) : v = xC := by
      apply Subtype.ext
      by_contra hne
      rw [hdegree] at hv
      have hr : G.Reachable x v.val := SimpleGraph.ConnectedComponent.eq.mp v.property.symm
      exact hn ⟨v.val,hne,hv,hr⟩
    have hsingle : Finset.univ.filter (fun v : c.supp => Odd (H.degree v)) = {xC} := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · exact hunique v
      · rintro rfl
        rw [hdegree]
        exact hx
    have heven := H.even_card_odd_degree_vertices
    rw [hsingle,Finset.card_singleton] at heven
    norm_num at heven
  obtain ⟨y,hy,hodd,hreach⟩ := hpartner
  obtain ⟨p,hp⟩ := hreach.exists_isPath
  exact ⟨y,hy,hodd,p,hp⟩
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
attribute [local instance] Classical.propDecidable
/-- Replacing the selected original boundary arc by its proper prefix ending
at an extra event strictly decreases the actual finite interior event count. -/
theorem actual_boundary_subarc_event_count_strict_decrease
    {X : Type*} [DecidableEq X] (E : Finset X) (A R : Set X) (a b z : X)
    (hzE : z ∈ E) (hzA : z ∈ A) (hza : z ≠ a) (hzb : z ≠ b)
    (hRA : R ⊆ A) (hbR : b ∉ R) :
    (E.filter (fun x => x ∈ R ∧ x ≠ z ∧ x ≠ a)).card <
      (E.filter (fun x => x ∈ A ∧ x ≠ a ∧ x ≠ b)).card := by
  have hsub : E.filter (fun x => x ∈ R ∧ x ≠ z ∧ x ≠ a) ⊆
      E.filter (fun x => x ∈ A ∧ x ≠ a ∧ x ≠ b) := by
    intro x hx
    obtain ⟨hxE,hxR,hxz,hxa⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hxE,hRA hxR,hxa,?_⟩
    intro hxb
    exact hbR (hxb ▸ hxR)
  have hzOld : z ∈ E.filter (fun x => x ∈ A ∧ x ≠ a ∧ x ≠ b) :=
    Finset.mem_filter.mpr ⟨hzE,hzA,hza,hzb⟩
  have hzNew : z ∉ E.filter (fun x => x ∈ R ∧ x ≠ z ∧ x ≠ a) := by
    intro hz
    exact (Finset.mem_filter.mp hz).2.2.1 rfl
  apply Finset.card_lt_card
  exact (Finset.ssubset_iff_subset_ne).mpr ⟨hsub,fun he => hzNew (he.symm ▸ hzOld)⟩
end CurveComplex.LocalSurgery





open Set Topology
namespace CurveComplex.LocalSurgery

def actualCylinderAnnulus : C(unitInterval × Circle,ℂ) where
  toFun p := ((1+p.1.val : ℝ) : ℂ) * (p.2 : ℂ)
  continuous_toFun := by fun_prop

lemma actualCylinderAnnulus_norm (p : unitInterval × Circle) :
    ‖actualCylinderAnnulus p‖ = 1+p.1.val := by
  change ‖((1+p.1.val : ℝ) : ℂ) * (p.2 : ℂ)‖ = _
  rw [norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith [p.1.property.1] : 0 ≤ 1+p.1.val)]

theorem actualCylinderAnnulus_injective : Function.Injective actualCylinderAnnulus := by
  rintro ⟨t,z⟩ ⟨u,w⟩ he
  have hnorm := congrArg norm he
  rw [actualCylinderAnnulus_norm,actualCylinderAnnulus_norm] at hnorm
  have htu : t = u := Subtype.ext (by linarith)
  subst u
  apply Prod.ext
  · rfl
  apply Circle.ext
  change ((1+t.val : ℝ) : ℂ) * (z : ℂ) = ((1+t.val : ℝ) : ℂ) * (w : ℂ) at he
  have hn : ((1+t.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [t.property.1] : (1+t.val : ℝ) ≠ 0)
  exact mul_left_cancel₀ hn he

theorem actualCylinderAnnulus_embedding : Topology.IsEmbedding actualCylinderAnnulus :=
  (actualCylinderAnnulus.continuous.isClosedEmbedding actualCylinderAnnulus_injective).isEmbedding

noncomputable def actualCylinderPlane : C(unitInterval × Circle,ℝ × ℝ) :=
  ⟨Complex.equivRealProdCLM ∘ actualCylinderAnnulus,
    Complex.equivRealProdCLM.continuous.comp actualCylinderAnnulus.continuous⟩

theorem actualCylinderPlane_embedding : Topology.IsEmbedding actualCylinderPlane :=
  Complex.equivRealProdCLM.toHomeomorph.isEmbedding.comp actualCylinderAnnulus_embedding


noncomputable def actualCylinderReverse : (unitInterval × Circle) ≃ₜ (unitInterval × Circle) :=
  unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl Circle)

noncomputable def actualOuterCylinderAnnulus : C(unitInterval × Circle,ℂ) :=
  actualCylinderAnnulus.comp ⟨actualCylinderReverse,actualCylinderReverse.continuous⟩

lemma actualOuterCylinderAnnulus_norm (p : unitInterval × Circle) :
    ‖actualOuterCylinderAnnulus p‖ = 2-p.1.val := by
  change ‖actualCylinderAnnulus (actualCylinderReverse p)‖ = _
  rw [actualCylinderAnnulus_norm]
  change 1+(1-p.1.val) = 2-p.1.val
  ring

theorem actualOuterCylinderAnnulus_embedding : Topology.IsEmbedding actualOuterCylinderAnnulus :=
  actualCylinderAnnulus_embedding.comp actualCylinderReverse.isEmbedding

noncomputable def actualOuterCylinderPlane : C(unitInterval × Circle,ℝ × ℝ) :=
  ⟨Complex.equivRealProdCLM ∘ actualOuterCylinderAnnulus,
    Complex.equivRealProdCLM.continuous.comp actualOuterCylinderAnnulus.continuous⟩

theorem actualOuterCylinderPlane_embedding : Topology.IsEmbedding actualOuterCylinderPlane :=
  Complex.equivRealProdCLM.toHomeomorph.isEmbedding.comp actualOuterCylinderAnnulus_embedding

lemma actualOuterCylinderAnnulus_closed_bounds (p : unitInterval × Circle) :
    1 ≤ ‖actualOuterCylinderAnnulus p‖ ∧ ‖actualOuterCylinderAnnulus p‖ ≤ 2 := by
  rw [actualOuterCylinderAnnulus_norm]
  constructor <;> linarith [p.1.property.1,p.1.property.2]

lemma actualOuterCylinderAnnulus_open_bounds (p : unitInterval × Circle)
    (hp : p.1 ∈ Set.Ioo (0 : unitInterval) 1) :
    1 < ‖actualOuterCylinderAnnulus p‖ ∧ ‖actualOuterCylinderAnnulus p‖ < 2 := by
  rw [actualOuterCylinderAnnulus_norm]
  have h0 : 0 < p.1.val := hp.1
  have h1 : p.1.val < 1 := hp.2
  constructor <;> linarith

theorem actualCylinderAnnulus_range :
    Set.range actualCylinderAnnulus = {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    change 1 ≤ ‖actualCylinderAnnulus p‖ ∧ ‖actualCylinderAnnulus p‖ ≤ 2
    rw [actualCylinderAnnulus_norm]
    constructor <;> linarith [p.1.property.1,p.1.property.2]
  · intro hz
    have hn : ‖z‖ ≠ 0 := by linarith [hz.1]
    have hnC : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    let t : unitInterval := ⟨‖z‖-1,by constructor <;> linarith [hz.1,hz.2]⟩
    let w : Circle := ⟨z / ((‖z‖ : ℝ) : ℂ),by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z)]
      exact div_self hn⟩
    refine ⟨(t,w),?_⟩
    change (((1+(‖z‖-1) : ℝ) : ℂ) * (z / ((‖z‖ : ℝ) : ℂ))) = z
    have hscalar : (1+(‖z‖-1) : ℝ) = ‖z‖ := by ring
    rw [hscalar]
    exact mul_div_cancel₀ z hnC

theorem actualOuterCylinderAnnulus_range :
    Set.range actualOuterCylinderAnnulus = {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
  rw [← actualCylinderAnnulus_range]
  change Set.range (actualCylinderAnnulus ∘ actualCylinderReverse) = _
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨actualCylinderReverse p,rfl⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨q,hq⟩ := actualCylinderReverse.surjective p
    exact ⟨q,congrArg actualCylinderAnnulus hq⟩


noncomputable def actualComplexSchoenflies : ℂ ≃L[ℝ] Schoenflies.Plane :=
  Complex.equivRealProdCLM.trans ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm)

lemma actualComplexSchoenflies_norm (z : ℂ) : ‖actualComplexSchoenflies z‖ = ‖z‖ := by
  have h0 : actualComplexSchoenflies z 0 = z.re := rfl
  have h1 : actualComplexSchoenflies z 1 = z.im := rfl
  have hs : ‖actualComplexSchoenflies z‖^2 = ‖z‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,Complex.sq_norm]
    simp [Fin.sum_univ_two,h0,h1,Complex.normSq_apply,pow_two]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

noncomputable def actualOuterCylinderSchoenflies : C(unitInterval × Circle,Schoenflies.Plane) :=
  ⟨actualComplexSchoenflies ∘ actualOuterCylinderAnnulus,
    actualComplexSchoenflies.continuous.comp actualOuterCylinderAnnulus.continuous⟩

theorem actualOuterCylinderSchoenflies_embedding : Topology.IsEmbedding actualOuterCylinderSchoenflies :=
  actualComplexSchoenflies.toHomeomorph.isEmbedding.comp actualOuterCylinderAnnulus_embedding

lemma actualOuterCylinderSchoenflies_norm (p : unitInterval × Circle) :
    ‖actualOuterCylinderSchoenflies p‖ = 2-p.1.val := by
  change ‖actualComplexSchoenflies (actualOuterCylinderAnnulus p)‖ = _
  rw [actualComplexSchoenflies_norm,actualOuterCylinderAnnulus_norm]

theorem actualOuterCylinderSchoenflies_range :
    Set.range actualOuterCylinderSchoenflies =
      {z : Schoenflies.Plane | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
  ext z
  constructor
  · rintro ⟨p,rfl⟩
    change 1 ≤ ‖actualOuterCylinderSchoenflies p‖ ∧ ‖actualOuterCylinderSchoenflies p‖ ≤ 2
    rw [actualOuterCylinderSchoenflies_norm]
    constructor <;> linarith [p.1.property.1,p.1.property.2]
  · intro hz
    have hnorm : ‖actualComplexSchoenflies.symm z‖ = ‖z‖ := by
      rw [← actualComplexSchoenflies_norm,actualComplexSchoenflies.apply_symm_apply]
    have hr : actualComplexSchoenflies.symm z ∈ Set.range actualOuterCylinderAnnulus := by
      rw [actualOuterCylinderAnnulus_range]
      change 1 ≤ ‖actualComplexSchoenflies.symm z‖ ∧ ‖actualComplexSchoenflies.symm z‖ ≤ 2
      rwa [hnorm]
    obtain ⟨p,hp⟩ := hr
    refine ⟨p,?_⟩
    change actualComplexSchoenflies (actualOuterCylinderAnnulus p) = z
    rw [hp,actualComplexSchoenflies.apply_symm_apply]

noncomputable def actualCylinderBottomCircle : C(Circle,Schoenflies.Plane) :=
  ⟨fun z => actualOuterCylinderSchoenflies (0,z),by fun_prop⟩

theorem actualCylinderBottomCircle_embedding : Topology.IsEmbedding actualCylinderBottomCircle := by
  apply (actualCylinderBottomCircle.continuous.isClosedEmbedding ?_).isEmbedding
  intro z w he
  have hp : ((0 : unitInterval),z) = (0,w) := actualOuterCylinderSchoenflies_embedding.injective he
  exact congrArg Prod.snd hp

theorem actualCylinderBottomCircle_jordan :
    Schoenflies.IsJordanCurve (Set.range actualCylinderBottomCircle) :=
  CurveComplex.isJordanCurve_range_of_isEmbedding_circle actualCylinderBottomCircle
    actualCylinderBottomCircle_embedding

theorem actualCylinderBottomCircle_range :
    Set.range actualCylinderBottomCircle = Metric.sphere (0 : Schoenflies.Plane) 2 := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    rw [Metric.mem_sphere,dist_zero_right]
    change ‖actualOuterCylinderSchoenflies (0,w)‖ = 2
    rw [actualOuterCylinderSchoenflies_norm]
    norm_num
  · intro hz
    have hnorm : ‖z‖ = 2 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz
    have hr : z ∈ Set.range actualOuterCylinderSchoenflies := by
      rw [actualOuterCylinderSchoenflies_range]
      change 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2
      rw [hnorm]
      norm_num
    obtain ⟨⟨t,w⟩,hp⟩ := hr
    have ht : t = 0 := by
      apply Subtype.ext
      have h := congrArg norm hp
      rw [actualOuterCylinderSchoenflies_norm,hnorm] at h
      change 2-t.val = 2 at h
      change t.val = 0
      linarith
    subst t
    exact ⟨w,hp⟩


theorem actualCylinderBottomCircle_inside :
    Schoenflies.inside (Set.range actualCylinderBottomCircle) =
      Metric.ball (0 : Schoenflies.Plane) 2 := by
  have hJ := actualCylinderBottomCircle_jordan
  rw [actualCylinderBottomCircle_range] at hJ ⊢
  have hsub : Metric.ball (0 : Schoenflies.Plane) 2 ⊆
      (Metric.sphere (0 : Schoenflies.Plane) 2)ᶜ := by
    intro x hx hs
    exact (ne_of_lt (Metric.mem_ball.mp hx)) (Metric.mem_sphere.mp hs)
  have hfr : frontier (Metric.ball (0 : Schoenflies.Plane) 2) ∩
      (Metric.sphere (0 : Schoenflies.Plane) 2)ᶜ = ∅ := by
    rw [frontier_ball (0 : Schoenflies.Plane) (by norm_num : (2 : ℝ) ≠ 0)]
    exact Set.inter_compl_self _
  have hzero : (0 : Schoenflies.Plane) ∈ Metric.ball (0 : Schoenflies.Plane) 2 := by
    simp
  have hcomp := Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
    Metric.isOpen_ball (convex_ball (0 : Schoenflies.Plane) 2).isPreconnected hsub hfr hzero
  have hinside : (0 : Schoenflies.Plane) ∈
      Schoenflies.inside (Metric.sphere (0 : Schoenflies.Plane) 2) := by
    refine ⟨hsub hzero,?_⟩
    rw [hcomp]
    exact Metric.isBounded_ball
  exact ((Schoenflies.jordan_curve_theorem hJ).connectedComponentIn_eq_inside hinside).symm.trans hcomp

open Schoenflies


/-- A genuine crosscut produces a closed Jordan cap avoiding any connected
hole contained in the cut domain. The two sides are produced by the actual
arbitrary-crosscut theorem, rather than supplied as a region certificate. -/
theorem actual_crosscut_cap_avoiding_connected_hole
    {C P A₁ A₂ H : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b A₁ A₂)
    (hPi : P \ {a,b} ⊆ inside C)
    (hH : IsPreconnected H) (hHi : H ⊆ inside C \ P) :
    ∃ A : Set Plane, (A = A₁ ∨ A = A₂) ∧ IsArcBetween A a b ∧
      IsJordanCurve (A ∪ P) ∧
      Disjoint ((A ∪ P) ∪ inside (A ∪ P)) H := by
  have hJ (A : Set Plane) (hA : IsArcBetween A a b) (hAC : A ⊆ C) :
      IsJordanCurve (A ∪ P) := by
    apply isJordanCurve_union hA hP
    intro x hxA hxP
    by_contra hbad
    have hnot : x ∉ ({a,b} : Set Plane) := by simpa using hbad
    exact inside_subset_compl (hPi ⟨hxP,hnot⟩) (hAC hxA)
  have hJ₁ := hJ A₁ hcut.fst hcut.fst_subset
  have hJ₂ := hJ A₂ hcut.snd hcut.snd_subset
  have hs₁ := jordan_curve_theorem hJ₁
  have hs₂ := jordan_curve_theorem hJ₂
  have hclass := general_crosscut_arbitrary_of_endpoints hC hP hcut hPi
  have hcover : H ⊆ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
    rw [← hclass.1]
    exact hHi
  rcases hH.subset_or_subset hs₁.isOpen_inside hs₂.isOpen_inside hclass.2.1 hcover with h₁ | h₂
  · refine ⟨A₂,Or.inr rfl,hcut.snd,hJ₂,?_⟩
    rw [Set.disjoint_left]
    intro x hx hxH
    rcases hx with (hxA | hxP) | hxi
    · exact inside_subset_compl (hHi hxH).1 (hcut.snd_subset hxA)
    · exact (hHi hxH).2 hxP
    · exact Set.disjoint_left.mp hclass.2.1 (h₁ hxH) hxi
  · refine ⟨A₁,Or.inl rfl,hcut.fst,hJ₁,?_⟩
    rw [Set.disjoint_left]
    intro x hx hxH
    rcases hx with (hxA | hxP) | hxi
    · exact inside_subset_compl (hHi hxH).1 (hcut.fst_subset hxA)
    · exact (hHi hxH).2 hxP
    · exact Set.disjoint_left.mp hclass.2.1 hxi (h₂ hxH)


/-- Produce the boundary cut as well as the Jordan cap from the genuine
crosscut and connected hole; no chosen cut pair or cap is an input. -/
theorem actual_crosscut_cap_produced
    {C P H : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPi : P \ {a,b} ⊆ inside C)
    (hH : IsPreconnected H) (hHi : H ⊆ inside C \ P) :
    ∃ A : Set Plane, IsArcBetween A a b ∧ A ⊆ C ∧
      IsJordanCurve (A ∪ P) ∧
      Disjoint ((A ∪ P) ∪ inside (A ∪ P)) H := by
  obtain ⟨A₁,A₂,hcut⟩ := exists_isCutPair hC ha hb hP.ne
  obtain ⟨A,hA,hArc,hJordan,hDisjoint⟩ :=
    actual_crosscut_cap_avoiding_connected_hole hC hP hcut hPi hH hHi
  refine ⟨A,hArc,?_,hJordan,hDisjoint⟩
  rcases hA with rfl | rfl
  · exact hcut.fst_subset
  · exact hcut.snd_subset


theorem actual_crosscut_cap_produced_with_carrier_bound
    {C P H : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (ha : a ∈ C) (hb : b ∈ C)
    (hPi : P \ {a,b} ⊆ inside C)
    (hH : IsPreconnected H) (hHi : H ⊆ inside C \ P) :
    ∃ A : Set Plane, IsArcBetween A a b ∧ A ⊆ C ∧
      IsJordanCurve (A ∪ P) ∧
      Disjoint ((A ∪ P) ∪ inside (A ∪ P)) H ∧
      ((A ∪ P) ∪ inside (A ∪ P)) ⊆ inside C ∪ C := by
  obtain ⟨A,hA,hAC,hJ,hDisjoint⟩ :=
    actual_crosscut_cap_produced hC hP ha hb hPi hH hHi
  have hPclosed : P ⊆ inside C ∪ C := by
    intro x hx
    by_cases he : x ∈ ({a,b} : Set Plane)
    · rcases (by simpa using he : x = a ∨ x = b) with rfl | rfl
      · exact Or.inr ha
      · exact Or.inr hb
    · exact Or.inl (hPi ⟨hx,he⟩)
  have hboundary : A ∪ P ⊆ inside C ∪ C := by
    intro x hx
    rcases hx with hxA | hxP
    · exact Or.inr (hAC hxA)
    · exact hPclosed hxP
  have hinside := CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
    (jordan_curve_theorem hC) (jordan_curve_theorem hJ) hboundary
  refine ⟨A,hA,hAC,hJ,hDisjoint,?_⟩
  intro x hx
  rcases hx with hxB | hxi
  · exact hboundary hxB
  · exact Or.inl (hinside hxi)


theorem actual_embedded_path_isArcBetween
    {x y : Schoenflies.Plane} (p : Path x y) (hp : Topology.IsEmbedding p) :
    Schoenflies.IsArcBetween (Set.range p) x y := by
  refine ⟨p.extend,p.continuous_extend.continuousOn,?_,?_,p.extend_zero,p.extend_one⟩
  · intro t ht u hu he
    rw [Path.extend_apply p ht,Path.extend_apply p hu] at he
    exact congrArg Subtype.val (hp.injective he)
  · ext z
    constructor
    · rintro ⟨t,ht,he⟩
      exact ⟨⟨t,ht⟩,(Path.extend_apply p ht).symm.trans he⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t.val,t.property,Path.extend_apply p t.property⟩

/-- An actual embedded cylinder crosscut from the original boundary to itself
produces an annular Jordan cap. No cap, hole-side choice, or cut-pair
certificate is supplied. -/
theorem actual_proper_cylinder_arc_produces_annular_cap
    {x y : unitInterval × Circle} (p : Path x y)
    (hp : Topology.IsEmbedding p) (hx : x.1 = 0) (hy : y.1 = 0)
    (hi : ∀ t ∈ Set.Ioo (0 : unitInterval) 1, 0 < (p t).1) :
    ∃ A : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween A (actualOuterCylinderSchoenflies x) (actualOuterCylinderSchoenflies y) ∧
      A ⊆ Set.range actualCylinderBottomCircle ∧
      Schoenflies.IsJordanCurve (A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p)) ∧
      ((A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p)) ∪
        Schoenflies.inside (A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p))) ⊆
          Set.range actualOuterCylinderSchoenflies := by
  let γ : Path (actualOuterCylinderSchoenflies x) (actualOuterCylinderSchoenflies y) :=
    p.map actualOuterCylinderSchoenflies.continuous
  have hγ : Topology.IsEmbedding γ := actualOuterCylinderSchoenflies_embedding.comp hp
  have hArc := actual_embedded_path_isArcBetween γ hγ
  have hleft : actualOuterCylinderSchoenflies x ∈ Set.range actualCylinderBottomCircle := by
    refine ⟨x.2,?_⟩
    apply congrArg actualOuterCylinderSchoenflies
    exact Prod.ext hx.symm rfl
  have hright : actualOuterCylinderSchoenflies y ∈ Set.range actualCylinderBottomCircle := by
    refine ⟨y.2,?_⟩
    apply congrArg actualOuterCylinderSchoenflies
    exact Prod.ext hy.symm rfl
  have hPi : Set.range γ \ {actualOuterCylinderSchoenflies x,actualOuterCylinderSchoenflies y} ⊆
      Schoenflies.inside (Set.range actualCylinderBottomCircle) := by
    rintro z ⟨⟨t,rfl⟩,hnot⟩
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      exact hnot (by simp)
    have ht1 : t ≠ 1 := by
      intro he
      subst t
      exact hnot (by simp)
    have htI : t ∈ Set.Ioo (0 : unitInterval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩
    rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right]
    change ‖actualOuterCylinderSchoenflies (p t)‖ < 2
    rw [actualOuterCylinderSchoenflies_norm]
    have hpos : 0 < (p t).1.val := hi t htI
    linarith
  have hHole : Metric.ball (0 : Schoenflies.Plane) 1 ⊆
      Schoenflies.inside (Set.range actualCylinderBottomCircle) \ Set.range γ := by
    intro z hz
    have hnorm : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    constructor
    · rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right]
      linarith
    · rintro ⟨t,he⟩
      have hbounds : 1 ≤ ‖actualOuterCylinderSchoenflies (p t)‖ := by
        rw [actualOuterCylinderSchoenflies_norm]
        linarith [(p t).1.property.2]
      change actualOuterCylinderSchoenflies (p t) = z at he
      rw [he] at hbounds
      linarith
  obtain ⟨A,hA,hAC,hJ,hDisjoint,hBound⟩ := actual_crosscut_cap_produced_with_carrier_bound
    actualCylinderBottomCircle_jordan hArc hleft hright hPi
    (convex_ball (0 : Schoenflies.Plane) 1).isPreconnected hHole
  refine ⟨A,hA,hAC,hJ,?_⟩
  intro z hz
  rw [actualOuterCylinderSchoenflies_range]
  change 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2
  constructor
  · apply le_of_not_gt
    intro hlt
    have hzHole : z ∈ Metric.ball (0 : Schoenflies.Plane) 1 := by
      simpa only [Metric.mem_ball,dist_zero_right] using hlt
    exact Set.disjoint_left.mp hDisjoint hz hzHole
  · rcases hBound hz with hzi | hzC
    · rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right] at hzi
      exact hzi.le
    · rw [actualCylinderBottomCircle_range,Metric.mem_sphere,dist_zero_right] at hzC
      exact hzC.le



theorem actual_closed_jordan_region_contractible
    {C : Set Plane} (hC : IsJordanCurve C) : ContractibleSpace ↥(C ∪ inside C) := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
  have himage : F '' C = modelCurve := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have he := hF ⟨x,hx⟩
      rw [he]
      exact (e ⟨x,hx⟩).property
    · intro hy
      obtain ⟨x,hx⟩ := e.surjective ⟨y,hy⟩
      refine ⟨x.val,x.property,?_⟩
      calc
        F x.val = (e x).val := hF x
        _ = y := congrArg Subtype.val hx
  have hclosed : F '' (C ∪ inside C) = Plane.closedSquare 0 1 := by
    rw [Set.image_union,CurveComplex.jordan_inside_homeomorph_image,himage]
    exact modelCurve_union_inside
  let E : ↥(C ∪ inside C) ≃ₜ ↥(Plane.closedSquare 0 1) :=
    (Homeomorph.image F (C ∪ inside C)).trans (Homeomorph.setCongr hclosed)
  have hnon : (Plane.closedSquare (0 : Plane) 1).Nonempty := by
    refine ⟨0,?_⟩
    exact mem_closedSquare_zero_one.mpr (by norm_num [Plane.supNorm])
  exact E.contractibleSpace_iff.mpr ((Plane.convex_closedSquare 0 1).contractibleSpace hnon)

theorem actual_closed_jordan_region_paths_homotopic
    {C : Set Plane} (hC : IsJordanCurve C)
    {x y : ↥(C ∪ inside C)} (p q : Path x y) : p.Homotopic q := by
  letI := actual_closed_jordan_region_contractible hC
  exact SimplyConnectedSpace.paths_homotopic p q


/-- The actual annular cap gives an embedded original-boundary arc homotopic
relative endpoints to the supplied proper embedded cylinder arc. -/
theorem actual_proper_cylinder_arc_homotopic_to_boundary
    {x y : unitInterval × Circle} (p : Path x y)
    (hp : Topology.IsEmbedding p) (hx : x.1 = 0) (hy : y.1 = 0)
    (hi : ∀ t ∈ Set.Ioo (0 : unitInterval) 1, 0 < (p t).1) :
    ∃ q : Path x y, Topology.IsEmbedding q ∧
      Set.range q ⊆ {z : unitInterval × Circle | z.1 = 0} ∧ p.Homotopic q := by
  obtain ⟨A,hA,hAC,hJ,hR⟩ := actual_proper_cylinder_arc_produces_annular_cap p hp hx hy hi
  let γ : Path (actualOuterCylinderSchoenflies x) (actualOuterCylinderSchoenflies y) :=
    p.map actualOuterCylinderSchoenflies.continuous
  let D : Set Schoenflies.Plane := (A ∪ Set.range γ) ∪ Schoenflies.inside (A ∪ Set.range γ)
  let rx : D := ⟨actualOuterCylinderSchoenflies x,Or.inl (Or.inr ⟨0,γ.source⟩)⟩
  let ry : D := ⟨actualOuterCylinderSchoenflies y,Or.inl (Or.inr ⟨1,γ.target⟩)⟩
  rcases hA with ⟨f,hfc,hfi,himage,hf0,hf1⟩
  have hAt (t : unitInterval) : f t.val ∈ A := himage ▸ (Set.mem_image_of_mem f t.property)
  let pD : Path rx ry := {
    toFun := fun t => ⟨γ t,Or.inl (Or.inr ⟨t,rfl⟩)⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := by apply Subtype.ext; exact γ.source
    target' := by apply Subtype.ext; exact γ.target }
  let qD : Path rx ry := {
    toFun := fun t => ⟨f t.val,Or.inl (Or.inl (hAt t))⟩
    continuous_toFun := (continuousOn_iff_continuous_restrict.mp hfc).subtype_mk _
    source' := by apply Subtype.ext; exact hf0
    target' := by apply Subtype.ext; exact hf1 }
  let E := actualOuterCylinderSchoenflies_embedding.toHomeomorph
  let back : C(D,unitInterval × Circle) :=
    ⟨fun z => E.symm ⟨z.val,hR z.property⟩,
      E.symm.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hback (z : D) : actualOuterCylinderSchoenflies (back z) = z.val :=
    congrArg Subtype.val (E.apply_symm_apply ⟨z.val,hR z.property⟩)
  have hbackinj : Function.Injective back := by
    intro z w he
    apply Subtype.ext
    exact (hback z).symm.trans ((congrArg actualOuterCylinderSchoenflies he).trans (hback w))
  have hrx : back rx = x := actualOuterCylinderSchoenflies_embedding.injective (hback rx)
  have hry : back ry = y := actualOuterCylinderSchoenflies_embedding.injective (hback ry)
  let q : Path x y := (qD.map back.continuous).cast hrx.symm hry.symm
  have hq : Topology.IsEmbedding q := by
    apply (q.continuous.isClosedEmbedding ?_).isEmbedding
    intro s t he
    have heD : qD s = qD t := hbackinj he
    have heF := congrArg Subtype.val heD
    exact Subtype.ext (hfi s.property t.property heF)
  have hboundary : Set.range q ⊆ {z : unitInterval × Circle | z.1 = 0} := by
    rintro z ⟨t,rfl⟩
    change (back (qD t)).1 = 0
    obtain ⟨w,hw⟩ := hAC (hAt t)
    have he : actualOuterCylinderSchoenflies (back (qD t)) =
        actualOuterCylinderSchoenflies (0,w) := (hback (qD t)).trans hw.symm
    exact congrArg Prod.fst (actualOuterCylinderSchoenflies_embedding.injective he)
  have H := (actual_closed_jordan_region_paths_homotopic hJ pD qD).map back
  have H' := H.pathCast hrx.symm hry.symm
  have hpeq : (pD.map back.continuous).cast hrx.symm hry.symm = p := by
    exact DFunLike.ext _ _ (fun t =>
      actualOuterCylinderSchoenflies_embedding.injective (hback (pD t)))
  change ((pD.map back.continuous).cast hrx.symm hry.symm).Homotopic q at H'
  rw [hpeq] at H'
  exact ⟨q,hq,hboundary,H'⟩

/-- The actual cap producer realizes the returning cylinder arc on the surface,
including the fixed-endpoint homotopy. Clean boundary interior remains separate. -/
theorem actual_proper_cylinder_returning_surface_paths
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (a b : Curve S) (F : C(unitInterval × Circle,S)) (z : Circle)
    (hbottom : ∀ w : Circle, F (0,w) = a.map (z*w))
    {x y : unitInterval × Circle} (p : Path x y) (hp : Topology.IsEmbedding p)
    (hx : x.1 = 0) (hy : y.1 = 0)
    (hi : ∀ t ∈ Set.Ioo (0 : unitInterval) 1, 0 < (p t).1)
    (htrace : Set.range (F ∘ p) ⊆ b.image) :
    F x ≠ F y ∧ F x ∈ a.image ∩ b.image ∧ F y ∈ a.image ∩ b.image ∧
      ∃ f g : Path (F x) (F y), Topology.IsEmbedding f ∧
        Set.range f ⊆ a.image ∧ Set.range g ⊆ b.image ∧ f.Homotopic g := by
  obtain ⟨q,hq,hqb,hpq⟩ := actual_proper_cylinder_arc_homotopic_to_boundary p hp hx hy hi
  have bottomInjective {r s : unitInterval × Circle} (hr : r.1 = 0) (hs : s.1 = 0)
      (h : F r = F s) : r = s := by
    have hre : r = (0,r.2) := Prod.ext hr rfl
    have hse : s = (0,s.2) := Prod.ext hs rfl
    rw [hre,hse,hbottom,hbottom] at h
    exact Prod.ext (hr.trans hs.symm) (mul_left_cancel (a.embedded.injective h))
  have hneq : F x ≠ F y := by
    intro he
    have hxy := bottomInjective hx hy he
    have ht : (0 : unitInterval) = 1 := hp.injective (by simpa using hxy)
    have hv := congrArg Subtype.val ht
    norm_num at hv
  have hxa : F x ∈ a.image := by
    rw [show x = (0,x.2) from Prod.ext hx rfl,hbottom]
    exact ⟨z*x.2,rfl⟩
  have hya : F y ∈ a.image := by
    rw [show y = (0,y.2) from Prod.ext hy rfl,hbottom]
    exact ⟨z*y.2,rfl⟩
  have hxb : F x ∈ b.image := htrace ⟨0,by simp⟩
  have hyb : F y ∈ b.image := htrace ⟨1,by simp⟩
  let f := q.map F.continuous
  let g := p.map F.continuous
  have hqtime (t : unitInterval) : (q t).1 = 0 := hqb ⟨t,rfl⟩
  have hf : Topology.IsEmbedding f := by
    have hinj : Function.Injective f := by
      intro t u he
      exact hq.injective (bottomInjective (hqtime t) (hqtime u) he)
    exact (f.continuous.isClosedEmbedding hinj).isEmbedding
  refine ⟨hneq,⟨hxa,hxb⟩,⟨hya,hyb⟩,f,g,hf,?_,?_,?_⟩
  · rintro w ⟨t,rfl⟩
    change F (q t) ∈ a.image
    rw [show q t = (0,(q t).2) from Prod.ext (hqtime t) rfl,hbottom]
    exact ⟨z*(q t).2,rfl⟩
  · exact htrace
  · exact (hpq.map F).symm

/-- Lift a genuine planar graph arc in the actual closed annulus to an embedded
cylinder Path, preserving its exact geometric image. -/
theorem actual_annular_arc_lifts_to_embedded_cylinder_path
    {A : Set Schoenflies.Plane} {x y : unitInterval × Circle}
    (hA : Schoenflies.IsArcBetween A (actualOuterCylinderSchoenflies x)
      (actualOuterCylinderSchoenflies y))
    (hAnn : A ⊆ Set.range actualOuterCylinderSchoenflies) :
    ∃ p : Path x y, Topology.IsEmbedding p ∧
      actualOuterCylinderSchoenflies '' Set.range p = A := by
  obtain ⟨γ,hγc,hγi,hγA,hγ0,hγ1⟩ := hA
  let R := Set.range actualOuterCylinderSchoenflies
  let rx : R := ⟨actualOuterCylinderSchoenflies x,⟨x,rfl⟩⟩
  let ry : R := ⟨actualOuterCylinderSchoenflies y,⟨y,rfl⟩⟩
  have hγR (t : unitInterval) : γ t.val ∈ R :=
    hAnn (hγA ▸ ⟨t.val,t.property,rfl⟩)
  let r : Path rx ry := {
    toFun := fun t => ⟨γ t.val,hγR t⟩
    continuous_toFun := (continuousOn_iff_continuous_restrict.mp hγc).subtype_mk _
    source' := by apply Subtype.ext; exact hγ0
    target' := by apply Subtype.ext; exact hγ1 }
  let E := actualOuterCylinderSchoenflies_embedding.toHomeomorph
  have hback (z : R) : actualOuterCylinderSchoenflies (E.symm z) = z.val :=
    congrArg Subtype.val (E.apply_symm_apply z)
  have hrx : E.symm rx = x := actualOuterCylinderSchoenflies_embedding.injective (hback rx)
  have hry : E.symm ry = y := actualOuterCylinderSchoenflies_embedding.injective (hback ry)
  let p : Path x y := (r.map E.symm.continuous).cast hrx.symm hry.symm
  have hp : Topology.IsEmbedding p := by
    apply (p.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    have hr : r t = r u := E.symm.injective he
    have hγ : γ t.val = γ u.val := congrArg Subtype.val hr
    exact Subtype.ext (hγi t.property u.property hγ)
  have hpoint (t : unitInterval) : actualOuterCylinderSchoenflies (p t) = γ t.val := hback (r t)
  refine ⟨p,hp,?_⟩
  ext z
  constructor
  · rintro ⟨w,⟨t,rfl⟩,rfl⟩
    rw [hpoint]
    exact hγA ▸ ⟨t.val,t.property,rfl⟩
  · intro hz
    have hzγ : z ∈ γ '' Set.Icc (0 : ℝ) 1 := hγA.symm ▸ hz
    obtain ⟨t,ht,he⟩ := hzγ
    exact ⟨p ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,(hpoint ⟨t,ht⟩).trans he⟩

end CurveComplex.LocalSurgery

open Set
namespace CurveComplex.LocalSurgery
noncomputable section
def actualThreeSegmentStart (j : Fin 3) : ℝ :=
  if j=0 then 0 else if j=1 then 1/3 else 2/3
def actualThreeSegmentEnd (j : Fin 3) : ℝ :=
  if j=0 then 1/3 else if j=1 then 2/3 else 1
theorem actualThreeSegment_order (j : Fin 3) :
    actualThreeSegmentStart j < actualThreeSegmentEnd j := by
  fin_cases j <;> norm_num [actualThreeSegmentStart,actualThreeSegmentEnd]
theorem actualThreeSegment_distinct_intersection (j k : Fin 3) (hjk : j ≠ k)
    (s : ℝ) (hs : s ∈ Icc (actualThreeSegmentStart j) (actualThreeSegmentEnd j))
    (ht : s ∈ Icc (actualThreeSegmentStart k) (actualThreeSegmentEnd k)) :
    (s = actualThreeSegmentStart j ∨ s = actualThreeSegmentEnd j) ∧
      (s = actualThreeSegmentStart k ∨ s = actualThreeSegmentEnd k) := by
  fin_cases j <;> fin_cases k
  all_goals norm_num [actualThreeSegmentStart,actualThreeSegmentEnd] at *
  all_goals first
    | (exfalso; linarith [hs.1,hs.2,ht.1,ht.2])
    | (constructor <;> first
      | (left; linarith [hs.1,hs.2,ht.1,ht.2])
      | (right; linarith [hs.1,hs.2,ht.1,ht.2]))
theorem actualThreeSegment_breakpoint_is_endpoint (j : Fin 3) (s : ℝ)
    (hs : s ∈ Icc (actualThreeSegmentStart j) (actualThreeSegmentEnd j))
    (hb : s = 0 ∨ s = 1/3 ∨ s = 2/3 ∨ s = 1) :
    s = actualThreeSegmentStart j ∨ s = actualThreeSegmentEnd j := by
  fin_cases j
  all_goals rcases hb with rfl | rfl | rfl | rfl
  all_goals norm_num [actualThreeSegmentStart,actualThreeSegmentEnd] at *
end
end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
/-- A label-preserving passage from the actual simple graph to the graph whose
edge labels carry geometric drawings. This does not supply any parity or drawing. -/
theorem actual_simple_graph_walk_to_labeled_graph
    {V E X : Type*} (G : SimpleGraph V) (H : Graph X E) (f : V → X)
    (hvertex : ∀ v, f v ∈ H.vertexSet)
    (hlink : ∀ {v w}, G.Adj v w → ∃ e, H.IsLink e (f v) (f w))
    {v w : V} (p : G.Walk v w) : ∃ W, H.IsWalk (f v) W (f w) := by
  induction p with
  | nil => exact ⟨[],Graph.IsWalk.nil (hvertex _)⟩
  | cons hadj p ih =>
    obtain ⟨e,he⟩ := hlink hadj
    obtain ⟨W,hW⟩ := ih
    exact ⟨e :: W,Graph.IsWalk.cons he hW⟩
/-- The geometric graph translation visits exactly the positions of the
original walk's support. No additional graph vertices appear. -/
theorem actual_simple_graph_walk_to_labeled_graph_with_vertices
    {V E X : Type*} (G : SimpleGraph V) (H : Graph X E) (f : V → X)
    (hvertex : ∀ v, f v ∈ H.vertexSet)
    (hlink : ∀ {v w}, G.Adj v w → ∃ e, H.IsLink e (f v) (f w))
    {v w : V} (p : G.Walk v w) :
    ∃ W, H.IsWalk (f v) W (f w) ∧
      H.walkVertices (f v) W = f '' {u | u ∈ p.support} := by
  induction p with
  | nil =>
    refine ⟨[],Graph.IsWalk.nil (hvertex _),?_⟩
    simp [Graph.walkVertices_nil]
  | @cons v u w hadj p ih =>
    obtain ⟨e,he⟩ := hlink hadj
    obtain ⟨W,hW,hverts⟩ := ih
    refine ⟨e :: W,Graph.IsWalk.cons he hW,?_⟩
    ext x
    constructor
    · intro hx
      rcases Graph.mem_walkVertices_cons he hx with rfl | htail
      · exact ⟨v,by simp,rfl⟩
      · rw [hverts] at htail
        obtain ⟨r,hr,heq⟩ := htail
        exact ⟨r,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hr,heq⟩
    · rintro ⟨r,hr,rfl⟩
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Graph.mem_walkVertices_self
      · apply Graph.mem_walkVertices_cons_of_mem he
        rw [hverts]
        exact ⟨r,hr,rfl⟩

/-- An injective vertex realization preserves a simple path and its exact
visited vertex set in the labeled geometric graph. -/
theorem actual_simple_graph_path_to_labeled_graph_with_vertices
    {V E X : Type*} (G : SimpleGraph V) (H : Graph X E) (f : V → X)
    (hf : Function.Injective f) (hvertex : ∀ v, f v ∈ H.vertexSet)
    (hlink : ∀ {v w}, G.Adj v w → ∃ e, H.IsLink e (f v) (f w))
    {v w : V} (p : G.Walk v w) (hp : p.IsPath) :
    ∃ W, H.IsPath (f v) W (f w) ∧
      H.walkVertices (f v) W = f '' {u | u ∈ p.support} := by
  revert hp
  induction p with
  | nil =>
    intro hp
    refine ⟨[],Graph.IsPath.nil (hvertex _),?_⟩
    simp [Graph.walkVertices_nil]
  | @cons v u w hadj p ih =>
    intro hp
    obtain ⟨hpp,hfresh⟩ := (SimpleGraph.Walk.cons_isPath_iff hadj p).mp hp
    obtain ⟨e,he⟩ := hlink hadj
    obtain ⟨W,hW,hverts⟩ := ih hpp
    have hnew : f v ∉ H.walkVertices (f u) W := by
      intro hv
      rw [hverts] at hv
      obtain ⟨r,hr,heq⟩ := hv
      exact hfresh (hf heq ▸ hr)
    refine ⟨e :: W,Graph.IsPath.cons he hW hnew,?_⟩
    ext x
    constructor
    · intro hx
      rcases Graph.mem_walkVertices_cons he hx with rfl | htail
      · exact ⟨v,by simp,rfl⟩
      · rw [hverts] at htail
        obtain ⟨r,hr,heq⟩ := htail
        exact ⟨r,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hr,heq⟩
    · rintro ⟨r,hr,rfl⟩
      simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Graph.mem_walkVertices_self
      · apply Graph.mem_walkVertices_cons_of_mem he
        rw [hverts]
        exact ⟨r,hr,rfl⟩

end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
/-- A degree-one vertex on an actual simple path must be one of its endpoints. -/
theorem actual_degree_one_path_support_is_endpoint
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {v w z : V} (p : G.Walk v w) (hp : p.IsPath)
    (hz : z ∈ p.support) (hdegree : G.degree z = 1) : z = v ∨ z = w := by
  by_contra hbad
  have hzv : z ≠ v := fun h => hbad (Or.inl h)
  have hzw : z ≠ w := fun h => hbad (Or.inr h)
  obtain ⟨n,hnz,hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he] at hnz
    exact hzv (by simpa using hnz.symm)
  have hnlt : n < p.length := by
    by_contra h
    have he : n = p.length := by omega
    rw [he,SimpleGraph.Walk.getVert_length] at hnz
    exact hzw hnz.symm
  have hprev : G.Adj z (p.getVert (n-1)) := by
    have h := (p.adj_getVert_succ (i := n-1) (by omega)).symm
    have he : n-1+1 = n := by omega
    rwa [he,hnz] at h
  have hnext : G.Adj z (p.getVert (n+1)) := by
    simpa only [hnz] using p.adj_getVert_succ hnlt
  have hne : p.getVert (n-1) ≠ p.getVert (n+1) := by
    intro h
    have he := hp.getVert_injOn (show n-1 ≤ p.length by omega)
      (show n+1 ≤ p.length by omega) h
    omega
  have hnon : (G.neighborFinset z).Nontrivial :=
    ⟨p.getVert (n-1),(G.mem_neighborFinset z _).mpr hprev,
      p.getVert (n+1),(G.mem_neighborFinset z _).mpr hnext,hne⟩
  have htwo : 2 ≤ G.degree z := hnon.two_le_card
  omega
end CurveComplex.LocalSurgery


open Set Topology
namespace CurveComplex.LocalSurgery

theorem actual_embedded_affine_subarc
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (γ : C(unitInterval,X)) (hγ : Topology.IsEmbedding γ)
    (r s : unitInterval) (hrs : r < s) :
    ∃ p : Path (γ r) (γ s), Topology.IsEmbedding p ∧
      Set.range p ⊆ γ '' Set.Icc r s ∧
      p '' Set.Ioo (0 : unitInterval) 1 ⊆ γ '' Set.Ioo r s := by
  let d : Path r s := {
    toFun := fun t => ⟨(1-t.val)*r.val+t.val*s.val,by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) r.property.1)
          (mul_nonneg t.property.1 s.property.1)
      · nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,s.property.1,s.property.2]⟩
    continuous_toFun := by fun_prop
    source' := by apply Subtype.ext; simp
    target' := by apply Subtype.ext; simp }
  have hd : Function.Injective d := by
    intro t u he
    have hv := congrArg Subtype.val he
    change (1-t.val)*r.val+t.val*s.val = (1-u.val)*r.val+u.val*s.val at hv
    have hs : r.val < s.val := hrs
    apply Subtype.ext
    nlinarith
  let p := d.map γ.continuous
  refine ⟨p,?_,?_,?_⟩
  · exact (p.continuous.isClosedEmbedding (hγ.injective.comp hd)).isEmbedding
  · rintro x ⟨t,rfl⟩
    refine ⟨d t,?_,rfl⟩
    have hs : r.val < s.val := hrs
    change r.val ≤ (1-t.val)*r.val+t.val*s.val ∧
      (1-t.val)*r.val+t.val*s.val ≤ s.val
    constructor <;> nlinarith [t.property.1,t.property.2]
  · rintro x ⟨t,ht,rfl⟩
    refine ⟨d t,?_,rfl⟩
    have hs : r.val < s.val := hrs
    have ht0 : 0 < t.val := ht.1
    have ht1 : t.val < 1 := ht.2
    change r.val < (1-t.val)*r.val+t.val*s.val ∧
      (1-t.val)*r.val+t.val*s.val < s.val
    constructor <;> nlinarith

end CurveComplex.LocalSurgery


open Set Topology

set_option pp.proofs false
set_option maxHeartbeats 4000000

namespace CurveComplex.LocalSurgery
/-- Genuine original transverse crossings change the side in every actual
centered axis chart. No endpoint-incidence parity or side certificate is assumed. -/
theorem actual_transverse_axis_signs_flip
    {S : Type*} [TopologicalSpace S] {a b : Curve S}
    (u : unitInterval) (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1)
    (γ : C(unitInterval, S)) (hγ : Set.InjOn γ (Set.Ioo 0 1))
    (hγimage : Set.range γ ⊆ b.image) (hcross : CrossesAt a b (γ u))
    (C : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : γ u ∈ C.source) (hCzero : C (γ u) = (0,0))
    (hCa : ∀ x ∈ C.source, x ∈ a.image ↔ (C x).1 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v w : unitInterval,
      (u : ℝ) - δ < v → v < u → u < w → (w : ℝ) < u + δ →
      (C (γ v)).1 ≠ 0 ∧ (C (γ w)).1 ≠ 0 ∧
      ((0 < (C (γ v)).1) ↔ ¬ (0 < (C (γ w)).1)) := by
  classical
  obtain ⟨U, V, hpU, k, hU, hV, kzero, kaxes⟩ := hcross
  let K := crossingPartialChart U V hU hV ⟨γ u, hpU⟩ k
  have hKs : K.source = U := by simp [K, crossingPartialChart]
  have hKval (x : S) (hx : x ∈ U) : K x = (k ⟨x, hx⟩ : ℝ × ℝ) := by
    change crossingPartialChart U V hU hV ⟨γ u, hpU⟩ k x = _
    simp only [crossingPartialChart, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    change (k (((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨γ u, hpU⟩⟩).symm x) : ℝ × ℝ) = (k ⟨x, hx⟩ : ℝ × ℝ)
    have hinv := ((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨γ u, hpU⟩⟩).left_inv (show (⟨x, hx⟩ : U) ∈ Set.univ from trivial)
    change ((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨γ u, hpU⟩⟩).symm x = ⟨x, hx⟩ at hinv
    rw [hinv]
  have hKzero : K (γ u) = (0, 0) := (hKval _ hpU).trans kzero
  have hKa (x : S) (hx : x ∈ K.source) : x ∈ a.image ↔ (K x).1 = 0 := by
    rw [hKval x (hKs ▸ hx)]
    exact (kaxes x (hKs ▸ hx)).1
  have hKb (x : S) (hx : x ∈ K.source) : x ∈ b.image ↔ (K x).2 = 0 := by
    rw [hKval x (hKs ▸ hx)]
    exact (kaxes x (hKs ▸ hx)).2
  have hpA : γ u ∈ a.image := (hKa _ (hKs.symm ▸ hpU)).mpr (by rw [hKzero])
  let T := K.symm.trans C
  have hTsource : (0, 0) ∈ T.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · change (0, 0) ∈ K.target
      exact hKzero ▸ K.map_source (hKs.symm ▸ hpU)
    · change K.symm (0, 0) ∈ C.source
      rw [← hKzero, K.left_inv (hKs.symm ▸ hpU)]
      exact hpC
  have hTzero : T (0, 0) = (0, 0) := by
    change C (K.symm (0, 0)) = (0, 0)
    rw [← hKzero, K.left_inv (hKs.symm ▸ hpU)]
    exact hCzero.trans hKzero.symm
  have hTaxis (x : ℝ × ℝ) (hx : x ∈ T.source) : x.1 = 0 ↔ (T x).1 = 0 := by
    rw [OpenPartialHomeomorph.trans_source] at hx
    have hKinv : K (K.symm x) = x := K.right_inv hx.1
    have hxKs : K.symm x ∈ K.source := K.symm.map_source hx.1
    have haxisK := hKa (K.symm x) hxKs
    rw [hKinv] at haxisK
    exact haxisK.symm.trans (hCa (K.symm x) hx.2)
  obtain ⟨r, hr, hrT, ε, hrelative⟩ :=
    local_axis_transition_side_constant T hTsource hTzero hTaxis
  let realγ := realIntervalPath γ
  have hγreal (v : unitInterval) : realγ (v : ℝ) = γ v := by
    change γ (Set.projIcc 0 1 (by norm_num) (v : ℝ)) = γ v
    rw [Set.projIcc_of_mem _ v.property]
  let Ω := C.source ∩ (K.source ∩ K ⁻¹' Metric.ball (0, 0) r)
  have hΩopen : IsOpen Ω := C.open_source.inter
    (K.isOpen_inter_preimage Metric.isOpen_ball)
  have hpΩ : γ u ∈ Ω := ⟨hpC, hKs.symm ▸ hpU, by
    change K (γ u) ∈ Metric.ball (0, 0) r
    rw [hKzero]
    exact Metric.mem_ball_self hr⟩
  obtain ⟨d, hd, hdΩ⟩ := Metric.mem_nhds_iff.mp
    (realγ.continuous.continuousAt.preimage_mem_nhds
      (hΩopen.mem_nhds (hγreal u ▸ hpΩ)))
  let δ := min d (min (u : ℝ) (1 - (u : ℝ))) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min hd (lt_min hu.1 (sub_pos.mpr hu.2))) (by norm_num)
  have hδd : δ < d := by dsimp [δ]; linarith [min_le_left d (min (u : ℝ) (1 - (u : ℝ)))]
  have hδu : δ < (u : ℝ) := by
    dsimp [δ]
    linarith [min_le_right d (min (u : ℝ) (1 - (u : ℝ))),
      min_le_left (u : ℝ) (1 - (u : ℝ))]
  have hδone : δ < 1 - (u : ℝ) := by
    dsimp [δ]
    linarith [min_le_right d (min (u : ℝ) (1 - (u : ℝ))),
      min_le_right (u : ℝ) (1 - (u : ℝ))]
  let J := Set.Icc ((u : ℝ) - δ) ((u : ℝ) + δ)
  have hJI : J ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.Icc_subset_Ioo (by linarith) (by linarith)
  have hJΩ (v : ℝ) (hv : v ∈ J) : realγ v ∈ Ω := by
    apply hdΩ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hv.1, hv.2]
  let normal : ℝ → ℝ := fun v => (K (realγ v)).1
  have hncont : ContinuousOn normal J := continuous_fst.comp_continuousOn
    (K.continuousOn.comp realγ.continuous.continuousOn (fun v hv => (hJΩ v hv).2.1))
  have hnzero : normal (u : ℝ) = 0 := by
    dsimp only [normal]
    rw [hγreal, hKzero]
  have hninj : Set.InjOn normal J := by
    intro v hv w hw heq
    have hvI := hJI hv
    have hwI := hJI hw
    let vI : unitInterval := ⟨v, hvI.1.le, hvI.2.le⟩
    let wI : unitInterval := ⟨w, hwI.1.le, hwI.2.le⟩
    have hvb : realγ v ∈ b.image := by
      rw [hγreal vI]
      exact hγimage ⟨vI, rfl⟩
    have hwb : realγ w ∈ b.image := by
      rw [hγreal wI]
      exact hγimage ⟨wI, rfl⟩
    have hvzero := (hKb _ (hJΩ v hv).2.1).mp hvb
    have hwzero := (hKb _ (hJΩ w hw).2.1).mp hwb
    have hcoords : K (realγ v) = K (realγ w) :=
      Prod.ext heq (hvzero.trans hwzero.symm)
    have hsame := K.injOn (hJΩ v hv).2.1 (hJΩ w hw).2.1 hcoords
    rw [hγreal vI, hγreal wI] at hsame
    exact congrArg Subtype.val (hγ hvI hwI hsame)
  have hmono := hncont.strictMonoOn_of_injOn_Icc'
    (show (u : ℝ) - δ ≤ (u : ℝ) + δ by linarith) hninj
  refine ⟨δ,hδ,?_⟩
  intro v w hvlo hvu huw hwhi
  have hvJ : (v : ℝ) ∈ J := ⟨hvlo.le, by exact le_trans hvu.le (by linarith)⟩
  have hwJ : (w : ℝ) ∈ J := ⟨by exact le_trans (by linarith) huw.le, hwhi.le⟩
  have huJ : (u : ℝ) ∈ J := ⟨by linarith, by linarith⟩
  have hsigns : (0 < normal (v : ℝ) ∧ normal (w : ℝ) < 0) ∨
      (normal (v : ℝ) < 0 ∧ 0 < normal (w : ℝ)) := by
    rcases hmono with hm | hm
    · right
      constructor
      · simpa only [hnzero] using hm hvJ huJ hvu
      · simpa only [hnzero] using hm huJ hwJ huw
    · left
      constructor
      · simpa only [hnzero] using hm hvJ huJ hvu
      · simpa only [hnzero] using hm huJ hwJ huw
  have hnv : normal (v : ℝ) ≠ 0 := by
    rcases hsigns with h | h
    · exact ne_of_gt h.1
    · exact ne_of_lt h.1
  have hnw : normal (w : ℝ) ≠ 0 := by
    rcases hsigns with h | h
    · exact ne_of_lt h.2
    · exact ne_of_gt h.2
  have pointAxis (x : unitInterval) (hxJ : (x : ℝ) ∈ J)
      (hx0 : normal (x : ℝ) ≠ 0) :
      (C (γ x)).1 ≠ 0 ∧
      (if 0 < (C (γ x)).1 then (1 : ZMod 2) else 0) =
        (if 0 < normal (x : ℝ) then (1 : ZMod 2) else 0) + ε := by
    have hxΩ := hγreal x ▸ hJΩ (x : ℝ) hxJ
    have hrel := hrelative (K (γ x)) hxΩ.2.2 (by
      simpa only [normal, hγreal] using hx0)
    have hTval : T (K (γ x)) = C (γ x) := by
      change C (K.symm (K (γ x))) = C (γ x)
      rw [K.left_inv hxΩ.2.1]
    rw [hTval] at hrel
    constructor
    · intro hz
      have ha := (hCa _ hxΩ.1).mpr hz
      have hK := (hKa _ hxΩ.2.1).mp ha
      exact hx0 (by simpa only [normal, hγreal] using hK)
    · simpa only [normal, hγreal] using hrel
  obtain ⟨hcv,hvlabel⟩ := pointAxis v hvJ hnv
  obtain ⟨hcw,hwlabel⟩ := pointAxis w hwJ hnw
  have hdiff : (if 0 < (C (γ v)).1 then (1 : ZMod 2) else 0) ≠
      (if 0 < (C (γ w)).1 then (1 : ZMod 2) else 0) := by
    intro he
    have hh := add_right_cancel (hvlabel.symm.trans (he.trans hwlabel))
    rcases hsigns with ⟨hvp,hwn⟩ | ⟨hvn,hwp⟩
    · simp [hvp,not_lt.mpr hwn.le] at hh
    · simp [not_lt.mpr hvn.le,hwp] at hh
  refine ⟨hcv,hcw,?_⟩
  by_cases hvp : 0 < (C (γ v)).1
  · by_cases hwp : 0 < (C (γ w)).1
    · exact False.elim (hdiff (by simp only [if_pos hvp,if_pos hwp]))
    · simp only [hvp,hwp,not_false_eq_true]
  · by_cases hwp : 0 < (C (γ w)).1
    · simp only [hvp,hwp,not_true_eq_false]
    · exact False.elim (hdiff (by simp only [if_neg hvp,if_neg hwp]))
/-- The sign change holds in the actual cell chart even when its origin is
not the crossing: translate the target chart, preserving its normal coordinate. -/
theorem actual_transverse_uncentered_axis_signs_flip
    {S : Type*} [TopologicalSpace S] {a b : Curve S}
    (u : unitInterval) (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1)
    (γ : C(unitInterval, S)) (hγ : Set.InjOn γ (Set.Ioo 0 1))
    (hγimage : Set.range γ ⊆ b.image) (hcross : CrossesAt a b (γ u))
    (C : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : γ u ∈ C.source)
    (hCa : ∀ x ∈ C.source, x ∈ a.image ↔ (C x).1 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v w : unitInterval,
      (u : ℝ) - δ < v → v < u → u < w → (w : ℝ) < u + δ →
      (C (γ v)).1 ≠ 0 ∧ (C (γ w)).1 ≠ 0 ∧
      ((0 < (C (γ v)).1) ↔ ¬ (0 < (C (γ w)).1)) := by
  have hmem : γ u ∈ a.image := by
    obtain ⟨U,V,hp,k,hU,hV,hzero,haxes⟩ := hcross
    apply (haxes (γ u) hp).1.mpr
    exact congrArg Prod.fst hzero
  have hnzero : (C (γ u)).1 = 0 := (hCa _ hpC).mp hmem
  let D : OpenPartialHomeomorph S (ℝ × ℝ) :=
    C.trans (Homeomorph.addRight (-C (γ u))).toOpenPartialHomeomorph
  have hsource : D.source = C.source := by
    ext x
    simp only [D,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
  have hfirst (x : S) : (D x).1 = (C x).1 := by
    change (C x).1 + (-(C (γ u))).1 = (C x).1
    change (C x).1 + -(C (γ u)).1 = (C x).1
    rw [hnzero]
    simp
  have hDzero : D (γ u) = (0,0) := by
    change C (γ u) + -C (γ u) = (0,0)
    exact add_neg_cancel _
  have hDa (x : S) (hx : x ∈ D.source) : x ∈ a.image ↔ (D x).1 = 0 := by
    rw [hfirst]
    exact hCa x (hsource ▸ hx)
  obtain ⟨δ,hδ,hflip⟩ := actual_transverse_axis_signs_flip u hu γ hγ hγimage hcross
    D (hsource.symm ▸ hpC) hDzero hDa
  refine ⟨δ,hδ,?_⟩
  intro v w hvlo hvu huw hwhi
  simpa only [hfirst] using hflip v w hvlo hvu huw hwhi
private lemma extraction_noZeroIntervalSign (g : C(Interval,ℝ)) (x y s : Interval)
    (hxs : x < s) (hsy : s < y) (hs : g s < 0)
    (hn : ∀ t, x < t → t < y → g t ≠ 0) :
    ∀ t ∈ Set.Icc x y, g t ≤ 0 := by
  intro t ht
  by_contra hgt
  have htpos : 0 < g t := lt_of_not_ge hgt
  rcases le_total s t with hst | hts
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hst g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have hzt : z < t := lt_of_le_of_ne hz.2 (by
      intro he; rw [he] at hgz; linarith)
    exact hn z (hxs.trans_le hz.1) (hzt.trans_le ht.2) hgz
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc' hts g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have htz : t < z := lt_of_le_of_ne hz.1 (by
      intro he; rw [← he] at hgz; linarith)
    exact hn z (ht.1.trans_lt htz) (hz.2.trans_lt hsy) hgz
private lemma extraction_interval_sign_constant (g : C(Interval,ℝ))
    (x y s t : Interval) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
    (hn : ∀ z, x < z → z < y → g z ≠ 0) :
    g s < 0 ↔ g t < 0 := by
  constructor
  · intro h
    exact lt_of_le_of_ne (extraction_noZeroIntervalSign g x y s hs.1 hs.2 h hn t
      ⟨ht.1.le,ht.2.le⟩) (hn t ht.1 ht.2)
  · intro h
    exact lt_of_le_of_ne (extraction_noZeroIntervalSign g x y t ht.1 ht.2 h hn s
      ⟨hs.1.le,hs.2.le⟩) (hn s hs.1 hs.2)
/-- Actual original transverse crossing plus the constructed zero-free mesh
intervals forces exactly one neighboring cone sector to be negative. -/
theorem actual_transverse_adjacent_intervals_have_opposite_signs
    {S : Type*} [TopologicalSpace S] {a b : Curve S}
    (u : unitInterval) (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1)
    (γ : C(unitInterval, S)) (hγ : Set.InjOn γ (Set.Ioo 0 1))
    (hγimage : Set.range γ ⊆ b.image) (hcross : CrossesAt a b (γ u))
    (C : OpenPartialHomeomorph S (ℝ × ℝ)) (hpC : γ u ∈ C.source)
    (hCa : ∀ x ∈ C.source, x ∈ a.image ↔ (C x).1 = 0)
    (g : C(Interval,ℝ)) (c : ℝ) (hc : c ≠ 0)
    (hg : ∀ t, g t = (C (γ t)).1 / c)
    (x y sl sr : Interval) (hxu : x < u) (huy : u < y)
    (hsl : sl ∈ Set.Ioo x u) (hsr : sr ∈ Set.Ioo u y)
    (hleft : ∀ z, x < z → z < u → g z ≠ 0)
    (hright : ∀ z, u < z → z < y → g z ≠ 0) :
    g sl < 0 ↔ ¬ g sr < 0 := by
  obtain ⟨δ,hδ,hflip⟩ := actual_transverse_uncentered_axis_signs_flip
    u hu γ hγ hγimage hcross C hpC hCa
  have hlo : max (x : ℝ) ((u : ℝ)-δ/2) < (u : ℝ) :=
    max_lt (show (x : ℝ) < (u : ℝ) from hxu) (by linarith)
  obtain ⟨v,hv0,hv1⟩ := exists_between hlo
  have hvI : v ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact x.property.1.trans (le_max_left _ _ |>.trans hv0.le)
    · exact hv1.le.trans u.property.2
  let vI : Interval := ⟨v,hvI⟩
  have hhi : (u : ℝ) < min (y : ℝ) ((u : ℝ)+δ/2) :=
    lt_min (show (u : ℝ) < (y : ℝ) from huy) (by linarith)
  obtain ⟨w,hw0,hw1⟩ := exists_between hhi
  have hwI : w ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact u.property.1.trans hw0.le
    · exact hw1.le.trans ((min_le_left _ _).trans y.property.2)
  let wI : Interval := ⟨w,hwI⟩
  have hvnear : (u : ℝ)-δ < vI := by
    change (u : ℝ)-δ < v
    have hh := (le_max_right _ _).trans_lt hv0
    linarith
  have hwnear : (wI : ℝ) < (u : ℝ)+δ := by
    change w < (u : ℝ)+δ
    have hh := hw1.trans_le (min_le_right _ _)
    linarith
  obtain ⟨hnv,hnw,hpos⟩ := hflip vI wI hvnear hv1 hw0 hwnear
  have hsample : g vI < 0 ↔ ¬ g wI < 0 := by
    rw [hg vI,hg wI]
    by_cases hvp : 0 < (C (γ vI)).1
    · have hwn : (C (γ wI)).1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt (hpos.mp hvp)) hnw
      rcases lt_or_gt_of_ne hc with hcn | hcp
      · have hgv : (C (γ vI)).1 / c < 0 := div_neg_of_pos_of_neg hvp hcn
        have hgw : 0 < (C (γ wI)).1 / c := div_pos_of_neg_of_neg hwn hcn
        simp only [hgv,not_lt.mpr hgw.le,not_false_eq_true]
      · have hgv : 0 < (C (γ vI)).1 / c := div_pos hvp hcp
        have hgw : (C (γ wI)).1 / c < 0 := div_neg_of_neg_of_pos hwn hcp
        simp only [not_lt.mpr hgv.le,hgw,not_true_eq_false]
    · have hvn : (C (γ vI)).1 < 0 := lt_of_le_of_ne (le_of_not_gt hvp) hnv
      have hwp : 0 < (C (γ wI)).1 := by
        by_contra hn
        exact hvp (hpos.mpr hn)
      rcases lt_or_gt_of_ne hc with hcn | hcp
      · have hgv : 0 < (C (γ vI)).1 / c := div_pos_of_neg_of_neg hvn hcn
        have hgw : (C (γ wI)).1 / c < 0 := div_neg_of_pos_of_neg hwp hcn
        simp only [not_lt.mpr hgv.le,hgw,not_true_eq_false]
      · have hgv : (C (γ vI)).1 / c < 0 := div_neg_of_neg_of_pos hvn hcp
        have hgw : 0 < (C (γ wI)).1 / c := div_pos hwp hcp
        simp only [hgv,not_lt.mpr hgw.le,not_false_eq_true]
  have hvleft : vI ∈ Set.Ioo x u := by
    constructor
    · change (x : ℝ) < v
      exact (le_max_left _ _).trans_lt hv0
    · exact hv1
  have hwright : wI ∈ Set.Ioo u y := by
    constructor
    · exact hw0
    · change w < (y : ℝ)
      exact hw1.trans_le (min_le_left _ _)
  have hl := extraction_interval_sign_constant g x u vI sl hvleft hsl hleft
  have hr := extraction_interval_sign_constant g u y wI sr hwright hsr hright
  exact hl.symm.trans (hsample.trans (not_congr hr))

/-- The actual unchanged boundary edges have embedded interiors and genuine
original crossing charts. Their affine parameter formula constructs the data. -/
theorem actual_original_boundary_subarc_geometry
    {S : Type*} [TopologicalSpace S] (a b : Curve S)
    (ht : Transverse a b) (z : Circle) (x y : Interval) (hxy : x < y)
    (γ : C(Interval,S))
    (hformula : ∀ t : Interval, ∃ r : Interval,
      r.val = (1-t.val)*x.val+t.val*y.val ∧
      γ t = intervalCurveLoopFrom a z r) :
    Set.range γ ⊆ a.image ∧ Set.InjOn γ (Set.Ioo (0 : Interval) 1) ∧
      ∀ u : Interval, γ u ∈ b.image → CrossesAt b a (γ u) := by
  have himage : Set.range γ ⊆ a.image := by
    rintro q ⟨t,rfl⟩
    obtain ⟨r,hr,hγ⟩ := hformula t
    rw [hγ]
    exact ⟨intervalCircleParameterFrom z r,rfl⟩
  refine ⟨himage,?_,?_⟩
  · intro t ht u hu htu
    obtain ⟨r,hr,hγr⟩ := hformula t
    obtain ⟨s,hs,hγs⟩ := hformula u
    have hrI : 0 < (r : ℝ) ∧ (r : ℝ) < 1 := by
      have hxyR : x.val < y.val := hxy
      have ht0 : 0 < t.val := ht.1
      have ht1 : t.val < 1 := ht.2
      rw [hr]
      constructor <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
    have hsI : 0 < (s : ℝ) ∧ (s : ℝ) < 1 := by
      have hxyR : x.val < y.val := hxy
      have hu0 : 0 < u.val := hu.1
      have hu1 : u.val < 1 := hu.2
      rw [hs]
      constructor <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
    rw [hγr,hγs] at htu
    have hcircle := a.embedded.injective htu
    change z * Circle.exp (2*Real.pi*r.val) =
      z * Circle.exp (2*Real.pi*s.val) at hcircle
    have hexp := mul_left_cancel hcircle
    have hangle := Circle.exp_injOn_Ico (a := 0) (b := 2*Real.pi) (by simp)
      (show 2*Real.pi*r.val ∈ Set.Ico 0 (2*Real.pi) from
        ⟨mul_nonneg (by positivity) hrI.1.le,by nlinarith [Real.pi_pos]⟩)
      (show 2*Real.pi*s.val ∈ Set.Ico 0 (2*Real.pi) from
        ⟨mul_nonneg (by positivity) hsI.1.le,by nlinarith [Real.pi_pos]⟩) hexp
    have hrs : r.val = s.val := by nlinarith [Real.pi_pos]
    apply Subtype.ext
    rw [hr,hs] at hrs
    have hxyR : x.val < y.val := hxy
    nlinarith
  · intro u hu
    exact (transverse_symm_of_chart ht).2 (γ u) ⟨hu,himage ⟨u,rfl⟩⟩
/-- Two actual charts straightening the same curve preserve whether a pair
of nearby off-curve points is on the same side. The chart transition produces
this equivalence; no orientation or endpoint-parity certificate is supplied. -/
theorem actual_shared_axis_charts_same_side
    {S : Type*} [TopologicalSpace S] (b : Curve S) (p : S)
    (hp : p ∈ b.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : p ∈ C.source) (hpD : p ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ b.image ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ b.image ↔ (D x).1 = 0) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ C.source ∩ D.source ∧
      ∀ x ∈ U, ∀ y ∈ U, x ∉ b.image → y ∉ b.image →
        (((C x).1 < 0 ↔ (C y).1 < 0) ↔
          ((D x).1 < 0 ↔ (D y).1 < 0)) := by
  classical
  have hCp : (C p).1 = 0 := (hC p hpC).mp hp
  have hDp : (D p).1 = 0 := (hD p hpD).mp hp
  let P := C.trans (Homeomorph.addRight (-C p)).toOpenPartialHomeomorph
  let Q := D.trans (Homeomorph.addRight (-D p)).toOpenPartialHomeomorph
  have hPs : P.source = C.source := by
    ext x
    simp only [P,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  have hQs : Q.source = D.source := by
    ext x
    simp only [Q,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  have hPf (x : S) : (P x).1 = (C x).1 := by
    change (C x).1 + -(C p).1 = (C x).1
    rw [hCp]
    simp
  have hQf (x : S) : (Q x).1 = (D x).1 := by
    change (D x).1 + -(D p).1 = (D x).1
    rw [hDp]
    simp
  have hPp : P p = (0,0) := by
    change C p + -C p = (0,0)
    exact add_neg_cancel _
  have hQp : Q p = (0,0) := by
    change D p + -D p = (0,0)
    exact add_neg_cancel _
  have hpP : p ∈ P.source := hPs.symm ▸ hpC
  have hpQ : p ∈ Q.source := hQs.symm ▸ hpD
  let T := P.symm.trans Q
  have hTs : (0,0) ∈ T.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hPp ▸ P.map_source hpP,?_⟩
    change P.symm (0,0) ∈ Q.source
    rw [←hPp,P.left_inv hpP]
    exact hpQ
  have hT0 : T (0,0) = (0,0) := by
    change Q (P.symm (0,0)) = (0,0)
    rw [←hPp,P.left_inv hpP]
    exact hQp.trans hPp.symm
  have hTa (z : ℝ × ℝ) (hz : z ∈ T.source) : z.1 = 0 ↔ (T z).1 = 0 := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hPinv := P.right_inv hz.1
    have hPaxis : P.symm z ∈ b.image ↔ z.1 = 0 := by
      have hh := hC (P.symm z) (hPs ▸ P.symm.map_source hz.1)
      rw [←hPf (P.symm z),hPinv] at hh
      exact hh
    have hQaxis : P.symm z ∈ b.image ↔ (Q (P.symm z)).1 = 0 := by
      rw [hQf]
      exact hD (P.symm z) (hQs ▸ hz.2)
    exact hPaxis.symm.trans hQaxis
  obtain ⟨r,hr,hball,ε,hrelative⟩ :=
    local_axis_transition_side_constant T hTs hT0 hTa
  let U := Q.source ∩ (P.source ∩ P ⁻¹' Metric.ball (0,0) r)
  have hUopen : IsOpen U := Q.open_source.inter
    (P.isOpen_inter_preimage Metric.isOpen_ball)
  have hpU : p ∈ U := ⟨hpQ,hpP,by
    change P p ∈ Metric.ball (0,0) r
    rw [hPp]
    exact Metric.mem_ball_self hr⟩
  have hsub : U ⊆ C.source ∩ D.source := fun _ hx => ⟨hPs ▸ hx.2.1,hQs ▸ hx.1⟩
  have hlabel (x : S) (hx : x ∈ U) (hxb : x ∉ b.image) :
      (if 0 < (D x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (C x).1 then (1 : ZMod 2) else 0) + ε := by
    have hn : (P x).1 ≠ 0 := by
      rw [hPf]
      exact fun hh => hxb ((hC x (hPs ▸ hx.2.1)).mpr hh)
    have hh := hrelative (P x) hx.2.2 hn
    have htrans : T (P x) = Q x := by
      change Q (P.symm (P x)) = Q x
      rw [P.left_inv hx.2.1]
    simpa only [htrans,hPf,hQf] using hh
  refine ⟨U,hUopen,hpU,hsub,?_⟩
  intro x hx y hy hxb hyb
  have hxnC : (C x).1 ≠ 0 := fun hh => hxb ((hC x (hsub hx).1).mpr hh)
  have hynC : (C y).1 ≠ 0 := fun hh => hyb ((hC y (hsub hy).1).mpr hh)
  have hxnD : (D x).1 ≠ 0 := fun hh => hxb ((hD x (hsub hx).2).mpr hh)
  have hynD : (D y).1 ≠ 0 := fun hh => hyb ((hD y (hsub hy).2).mpr hh)
  have hlabels :
      ((if 0 < (D x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (D y).1 then (1 : ZMod 2) else 0)) ↔
      ((if 0 < (C x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (C y).1 then (1 : ZMod 2) else 0)) := by
    rw [hlabel x hx hxb,hlabel y hy hyb]
    exact add_right_cancel_iff
  by_cases hcx : 0 < (C x).1 <;> by_cases hcy : 0 < (C y).1 <;>
    by_cases hdx : 0 < (D x).1 <;> by_cases hdy : 0 < (D y).1
  all_goals simp only [hcx,hcy,hdx,hdy,ite_true,ite_false] at hlabels
  all_goals have hcnegx : (C x).1 < 0 ↔ ¬0 < (C x).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnC⟩
  all_goals have hcnegy : (C y).1 < 0 ↔ ¬0 < (C y).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynC⟩
  all_goals have hdnegx : (D x).1 < 0 ↔ ¬0 < (D x).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnD⟩
  all_goals have hdnegy : (D y).1 < 0 ↔ ¬0 < (D y).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynD⟩
  all_goals rw [hcnegx,hcnegy,hdnegx,hdnegy]
  all_goals simp_all

/-- Normalizing one actual axis coordinate by its nonzero cone-center height
preserves whether two off-axis samples have the same sign. -/
lemma normalized_axis_same_sign (x y c : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hc : c ≠ 0) : ((x/c < 0 ↔ y/c < 0) ↔ (x < 0 ↔ y < 0)) := by
  rcases lt_or_gt_of_ne hc with hcn | hcp
  · have hcp : ¬0 < c := not_lt_of_ge hcn.le
    simp only [div_neg_iff,hcn,hcp,and_true,and_false,or_false]
    have hxs : 0 < x ↔ ¬x < 0 :=
      ⟨fun h => not_lt_of_ge h.le,
        fun h => lt_of_le_of_ne (le_of_not_gt h) hx.symm⟩
    have hys : 0 < y ↔ ¬y < 0 :=
      ⟨fun h => not_lt_of_ge h.le,
        fun h => lt_of_le_of_ne (le_of_not_gt h) hy.symm⟩
    rw [hxs,hys]
    tauto
  · have hcn : ¬c < 0 := not_lt_of_ge hcp.le
    simp only [div_neg_iff,hcn,hcp,and_true,and_false,false_or]

private lemma shared_noZeroIntervalSign (g : C(Interval,ℝ)) (x y s : Interval)
    (hxs : x < s) (hsy : s < y) (hs : g s < 0)
    (hn : ∀ t, x < t → t < y → g t ≠ 0) :
    ∀ t ∈ Set.Icc x y, g t ≤ 0 := by
  intro t ht
  by_contra hgt
  have htpos : 0 < g t := lt_of_not_ge hgt
  rcases le_total s t with hst | hts
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hst g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have hzt : z < t := lt_of_le_of_ne hz.2 (by
      intro he; rw [he] at hgz; linarith)
    exact hn z (hxs.trans_le hz.1) (hzt.trans_le ht.2) hgz
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc' hts g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have htz : t < z := lt_of_le_of_ne hz.1 (by
      intro he; rw [← he] at hgz; linarith)
    exact hn z (ht.1.trans_lt htz) (hz.2.trans_lt hsy) hgz
private lemma shared_interval_sign_constant (g : C(Interval,ℝ))
    (x y s t : Interval) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
    (hn : ∀ z, x < z → z < y → g z ≠ 0) :
    g s < 0 ↔ g t < 0 := by
  constructor
  · intro h
    exact lt_of_le_of_ne (shared_noZeroIntervalSign g x y s hs.1 hs.2 h hn t
      ⟨ht.1.le,ht.2.le⟩) (hn t ht.1 ht.2)
  · intro h
    exact lt_of_le_of_ne (shared_noZeroIntervalSign g x y t ht.1 ht.2 h hn s
      ⟨hs.1.le,hs.2.le⟩) (hn s hs.1 hs.2)
/-- The actual common trace of two chart-contained faces has the same
sector-incidence parity in both actual axis charts, even at a tangency. -/
theorem actual_shared_axis_trace_same_sector_sign
    {S : Type*} [TopologicalSpace S] (b : Curve S)
    (γ : C(Interval,S)) (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
    (hroot : γ u ∈ b.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : γ u ∈ C.source) (hpD : γ u ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ b.image ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ b.image ↔ (D x).1 = 0)
    (g h : C(Interval,ℝ)) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : ∀ t, g t = (C (γ t)).1/c) (hh : ∀ t, h t = (D (γ t)).1/d)
    (x y sl sr X Y sL sR : Interval)
    (hxu : x < u) (huy : u < y) (hXu : X < u) (huY : u < Y)
    (hsl : sl ∈ Set.Ioo x u) (hsr : sr ∈ Set.Ioo u y)
    (hsL : sL ∈ Set.Ioo X u) (hsR : sR ∈ Set.Ioo u Y)
    (hgl : ∀ t, x < t → t < u → g t ≠ 0)
    (hgr : ∀ t, u < t → t < y → g t ≠ 0)
    (hhl : ∀ t, X < t → t < u → h t ≠ 0)
    (hhr : ∀ t, u < t → t < Y → h t ≠ 0) :
    ((g sl < 0 ↔ g sr < 0) ↔ (h sL < 0 ↔ h sR < 0)) := by
  obtain ⟨U,hUopen,hpU,hUcharts,hside⟩ :=
    actual_shared_axis_charts_same_side b (γ u) hroot C D hpC hpD hC hD
  let realγ := realIntervalPath γ
  have hreal (t : Interval) : realγ t.val = γ t := by
    change γ (Set.projIcc 0 1 (by norm_num) t.val) = γ t
    rw [Set.projIcc_of_mem _ t.property]
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp
    (realγ.continuous.continuousAt.preimage_mem_nhds
      (hUopen.mem_nhds (hreal u ▸ hpU)))
  have hlo : max (max x.val X.val) (u.val-δ/2) < u.val := by
    apply max_lt
    · exact max_lt (show x.val < u.val from hxu) (show X.val < u.val from hXu)
    · linarith
  obtain ⟨v,hv0,hv1⟩ := exists_between hlo
  have hvx : x.val < v := (le_max_left x.val X.val).trans
    (le_max_left _ _) |>.trans_lt hv0
  have hvX : X.val < v := (le_max_right x.val X.val).trans
    (le_max_left _ _) |>.trans_lt hv0
  let vI : Interval := ⟨v,⟨x.property.1.trans hvx.le,hv1.le.trans u.property.2⟩⟩
  have hhi : u.val < min (min y.val Y.val) (u.val+δ/2) := by
    apply lt_min
    · exact lt_min (show u.val < y.val from huy) (show u.val < Y.val from huY)
    · linarith
  obtain ⟨w,hw0,hw1⟩ := exists_between hhi
  have hwy : w < y.val := hw1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hwY : w < Y.val := hw1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  let wI : Interval := ⟨w,⟨u.property.1.trans hw0.le,hwy.le.trans y.property.2⟩⟩
  have hvU : γ vI ∈ U := by
    rw [←hreal vI]
    apply hδU
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    have hl := (le_max_right _ _).trans_lt hv0
    constructor <;> change _ < _ <;> linarith
  have hwU : γ wI ∈ U := by
    rw [←hreal wI]
    apply hδU
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    have hh' := hw1.trans_le (min_le_right _ _)
    constructor <;> change _ < _ <;> linarith
  have hgv : g vI ≠ 0 := hgl vI hvx hv1
  have hgw : g wI ≠ 0 := hgr wI hw0 hwy
  have hhv : h vI ≠ 0 := hhl vI hvX hv1
  have hhw : h wI ≠ 0 := hhr wI hw0 hwY
  have hCv : (C (γ vI)).1 ≠ 0 := by
    intro he
    apply hgv
    rw [hg vI,he,zero_div]
  have hCw : (C (γ wI)).1 ≠ 0 := by
    intro he
    apply hgw
    rw [hg wI,he,zero_div]
  have hDv : (D (γ vI)).1 ≠ 0 := by
    intro he
    apply hhv
    rw [hh vI,he,zero_div]
  have hDw : (D (γ wI)).1 ≠ 0 := by
    intro he
    apply hhw
    rw [hh wI,he,zero_div]
  have hvb : γ vI ∉ b.image := fun he => hCv ((hC _ (hUcharts hvU).1).mp he)
  have hwb : γ wI ∉ b.image := fun he => hCw ((hC _ (hUcharts hwU).1).mp he)
  have hsamples : ((g vI < 0 ↔ g wI < 0) ↔ (h vI < 0 ↔ h wI < 0)) := by
    rw [hg vI,hg wI,hh vI,hh wI]
    exact (normalized_axis_same_sign _ _ c hCv hCw hc).trans
      ((hside _ hvU _ hwU hvb hwb).trans
        (normalized_axis_same_sign _ _ d hDv hDw hd).symm)
  have hl := shared_interval_sign_constant g x u sl vI hsl ⟨hvx,hv1⟩ hgl
  have hr := shared_interval_sign_constant g u y sr wI hsr ⟨hw0,hwy⟩ hgr
  have hL := shared_interval_sign_constant h X u sL vI hsL ⟨hvX,hv1⟩ hhl
  have hR := shared_interval_sign_constant h u Y sR wI hsR ⟨hw0,hwY⟩ hhr
  rwa [←hl,←hr,←hL,←hR] at hsamples

/-- Exact parity of the two concrete negative-sector contributions. -/
lemma negative_sector_indicator_odd_iff (x y : ℝ) :
    Odd ((if x < 0 then 1 else 0) + (if y < 0 then 1 else 0) : ℕ) ↔
      ¬(x < 0 ↔ y < 0) := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  all_goals simp only [hx,hy,ite_true,ite_false]
  all_goals norm_num

theorem actual_shared_axis_trace_sector_incidence_parity
    {S : Type*} [TopologicalSpace S] (b : Curve S)
    (γ : C(Interval,S)) (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
    (hroot : γ u ∈ b.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : γ u ∈ C.source) (hpD : γ u ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ b.image ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ b.image ↔ (D x).1 = 0)
    (g h : C(Interval,ℝ)) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : ∀ t, g t = (C (γ t)).1/c) (hh : ∀ t, h t = (D (γ t)).1/d)
    (x y sl sr X Y sL sR : Interval)
    (hxu : x < u) (huy : u < y) (hXu : X < u) (huY : u < Y)
    (hsl : sl ∈ Set.Ioo x u) (hsr : sr ∈ Set.Ioo u y)
    (hsL : sL ∈ Set.Ioo X u) (hsR : sR ∈ Set.Ioo u Y)
    (hgl : ∀ t, x < t → t < u → g t ≠ 0)
    (hgr : ∀ t, u < t → t < y → g t ≠ 0)
    (hhl : ∀ t, X < t → t < u → h t ≠ 0)
    (hhr : ∀ t, u < t → t < Y → h t ≠ 0) :
    (Odd ((if g sl < 0 then 1 else 0) + (if g sr < 0 then 1 else 0) : ℕ) ↔
      Odd ((if h sL < 0 then 1 else 0) + (if h sR < 0 then 1 else 0) : ℕ)) := by
  have hs := actual_shared_axis_trace_same_sector_sign b γ u hu hroot C D hpC hpD hC hD
    g h c d hc hd hg hh x y sl sr X Y sL sR hxu huy hXu huY hsl hsr hsL hsR
    hgl hgr hhl hhr
  rw [negative_sector_indicator_odd_iff,negative_sector_indicator_odd_iff]
  exact not_congr hs



lemma mesh_brackets (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
    (hend : mesh (Fin.last (m+1)) = 1) (t : Interval) (ht : t < 1) :
    ∃ j : Fin (m+1), mesh j.castSucc ≤ t ∧ t < mesh j.succ := by
  classical
  let P : Finset (Fin (m+2)) := Finset.univ.filter (fun i => mesh i ≤ t)
  have hP : P.Nonempty := ⟨0, by simp [P, hstart]⟩
  let i := P.max' hP
  have hi : mesh i ≤ t := (Finset.mem_filter.mp (P.max'_mem hP)).2
  have hilast : i ≠ Fin.last (m+1) := by
    intro he
    rw [he, hend] at hi
    exact (not_le_of_gt ht) hi
  obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hilast
  refine ⟨j, hj ▸ hi, ?_⟩
  by_contra hn
  have hsucc : j.succ ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_of_not_gt hn
  have hle := P.le_max' j.succ hsucc
  change j.succ ≤ i at hle
  rw [← hj] at hle
  have hval : j.val + 1 ≤ j.val := hle
  omega
lemma mesh_zero_internal (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
    (hend : mesh (Fin.last (m+1)) = 1) (g : Interval → ℝ)
    (hg0 : g 0 ≠ 0) (hg1 : g 1 ≠ 0)
    (hgap : ∀ (j : Fin (m+1)) (t : Interval),
      mesh j.castSucc < t → t < mesh j.succ → g t ≠ 0)
    (t : Interval) (ht : g t = 0) :
    ∃ i : Fin (m+2), mesh i = t ∧ i ≠ 0 ∧ i ≠ Fin.last (m+1) := by
  have ht0 : t ≠ 0 := by intro he; exact hg0 (he ▸ ht)
  have ht1 : t < 1 := lt_of_le_of_ne t.property.2 (by
    intro he
    apply hg1
    exact he ▸ ht)
  obtain ⟨j,hlo,hhi⟩ := mesh_brackets m mesh hmono hstart hend t ht1
  have he : mesh j.castSucc = t := by
    by_contra hn
    exact hgap j t (lt_of_le_of_ne hlo hn) hhi ht
  refine ⟨j.castSucc,he,?_,?_⟩
  · intro hi
    rw [hi,hstart] at he
    exact ht0 he.symm
  · exact Fin.castSucc_ne_last j
lemma mesh_zero_adjacent (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
    (hend : mesh (Fin.last (m+1)) = 1) (g : Interval → ℝ)
    (hg0 : g 0 ≠ 0) (hg1 : g 1 ≠ 0)
    (hgap : ∀ (j : Fin (m+1)) (t : Interval),
      mesh j.castSucc < t → t < mesh j.succ → g t ≠ 0)
    (t : Interval) (ht : g t = 0) :
    ∃ l r : Fin (m+1), mesh l.succ = t ∧ mesh r.castSucc = t ∧
      l.val+1 = r.val ∧
      (∀ j : Fin (m+1), mesh j.succ = t ↔ j = l) ∧
      (∀ j : Fin (m+1), mesh j.castSucc = t ↔ j = r) := by
  obtain ⟨i,hi,hi0,hi1⟩ := mesh_zero_internal m mesh hmono hstart hend g hg0 hg1 hgap t ht
  obtain ⟨l,hl⟩ := Fin.exists_succ_eq.mpr hi0
  obtain ⟨r,hr⟩ := Fin.exists_castSucc_eq.mpr hi1
  refine ⟨l,r,hl ▸ hi,hr ▸ hi,?_,?_,?_⟩
  · have he := congrArg Fin.val (hl.trans hr.symm)
    exact he
  · intro j
    constructor
    · intro hj
      apply Fin.succ_injective
      apply hmono.injective
      exact hj.trans (hl ▸ hi).symm
    · rintro rfl
      exact hl ▸ hi
  · intro j
    constructor
    · intro hj
      apply Fin.castSucc_injective
      apply hmono.injective
      exact hj.trans (hr ▸ hi).symm
    · rintro rfl
      exact hr ▸ hi

/-- The exact adjacent mesh-incidence census at a zero, without transversality.
The two contributions are computed from the actual negative sectors. -/
lemma actual_mesh_zero_incidence_card (m : ℕ) (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
    (hend : mesh (Fin.last (m+1)) = 1)
    (intervalMidpoint : Interval → Interval → Interval) (g : Interval → ℝ)
    (hg0 : g 0 ≠ 0) (hg1 : g 1 ≠ 0)
    (hgap : ∀ (j : Fin (m+1)) (t : Interval),
      mesh j.castSucc < t → t < mesh j.succ → g t ≠ 0)
    (t : Interval) (ht : g t = 0) :
    ∃ l r : Fin (m+1), mesh l.succ = t ∧ mesh r.castSucc = t ∧
      l.val+1 = r.val ∧
      (Finset.univ.filter (fun j : Fin (m+1) =>
        g (intervalMidpoint (mesh j.castSucc) (mesh j.succ)) < 0 ∧
          mesh j.succ = t)).card +
      (Finset.univ.filter (fun j : Fin (m+1) =>
        g (intervalMidpoint (mesh j.castSucc) (mesh j.succ)) < 0 ∧
          mesh j.castSucc = t)).card =
        (if g (intervalMidpoint (mesh l.castSucc) (mesh l.succ)) < 0 then 1 else 0) +
        (if g (intervalMidpoint (mesh r.castSucc) (mesh r.succ)) < 0 then 1 else 0) := by
  classical
  obtain ⟨l,r,hl,hr,hlr,hlu,hru⟩ :=
    mesh_zero_adjacent m mesh hmono hstart hend g hg0 hg1 hgap t ht
  let P (j : Fin (m+1)) := g (intervalMidpoint (mesh j.castSucc) (mesh j.succ)) < 0
  have hL : Finset.univ.filter (fun j : Fin (m+1) => P j ∧ mesh j.succ = t) =
      if P l then {l} else ∅ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hlu j]
    by_cases hj : j = l
    · subst j
      by_cases hn : P l <;> simp [hn]
    · by_cases hn : P l <;> simp [hn,hj]
  have hR : Finset.univ.filter (fun j : Fin (m+1) => P j ∧ mesh j.castSucc = t) =
      if P r then {r} else ∅ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hru j]
    by_cases hj : j = r
    · subst j
      by_cases hn : P r <;> simp [hn]
    · by_cases hn : P r <;> simp [hn,hj]
  refine ⟨l,r,hl,hr,hlr,?_⟩
  change (Finset.univ.filter (fun j => P j ∧ mesh j.succ = t)).card +
    (Finset.univ.filter (fun j => P j ∧ mesh j.castSucc = t)).card =
    (if P l then 1 else 0) + (if P r then 1 else 0)
  rw [hL,hR]
  by_cases hn : P l <;> by_cases hp : P r <;> simp [hn,hp]



noncomputable def actualMeshMidpoint (x y : Interval) : Interval :=
  ⟨(x.val+y.val)/2,by constructor <;> linarith [x.property.1,x.property.2,y.property.1,y.property.2]⟩

lemma actualMeshMidpoint_between (x y : Interval) (hxy : x < y) :
    x < actualMeshMidpoint x y ∧ actualMeshMidpoint x y < y := by
  have hxy' : x.val < y.val := hxy
  constructor
  · change x.val < (x.val+y.val)/2
    linarith
  · change (x.val+y.val)/2 < y.val
    linarith

/-- Complete two-face mesh-index incidence parity from the actual common trace
and actual straightening charts. No parity/side certificate is an input. -/
theorem actual_shared_mesh_root_incidence_parity
    {S : Type*} [TopologicalSpace S] (b : Curve S)
    (γ : C(Interval,S)) (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
    (hroot : γ u ∈ b.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : γ u ∈ C.source) (hpD : γ u ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ b.image ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ b.image ↔ (D x).1 = 0)
    (g h : C(Interval,ℝ)) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hg : ∀ t, g t = (C (γ t)).1/c) (hh : ∀ t, h t = (D (γ t)).1/d)
    (m M : ℕ) (mesh : Fin (m+2) → Interval) (Mesh : Fin (M+2) → Interval)
    (hmono : StrictMono mesh) (Hmono : StrictMono Mesh)
    (hstart : mesh 0 = 0) (Hstart : Mesh 0 = 0)
    (hend : mesh (Fin.last (m+1)) = 1) (Hend : Mesh (Fin.last (M+1)) = 1)
    (hg0 : g 0 ≠ 0) (hg1 : g 1 ≠ 0) (hh0 : h 0 ≠ 0) (hh1 : h 1 ≠ 0)
    (hgap : ∀ (j : Fin (m+1)) (t : Interval),
      mesh j.castSucc < t → t < mesh j.succ → g t ≠ 0)
    (Hgap : ∀ (j : Fin (M+1)) (t : Interval),
      Mesh j.castSucc < t → t < Mesh j.succ → h t ≠ 0) :
    (Odd ((Finset.univ.filter (fun j : Fin (m+1) =>
      g (actualMeshMidpoint (mesh j.castSucc) (mesh j.succ)) < 0 ∧ mesh j.succ = u)).card +
      (Finset.univ.filter (fun j : Fin (m+1) =>
      g (actualMeshMidpoint (mesh j.castSucc) (mesh j.succ)) < 0 ∧ mesh j.castSucc = u)).card) ↔
    Odd ((Finset.univ.filter (fun j : Fin (M+1) =>
      h (actualMeshMidpoint (Mesh j.castSucc) (Mesh j.succ)) < 0 ∧ Mesh j.succ = u)).card +
      (Finset.univ.filter (fun j : Fin (M+1) =>
      h (actualMeshMidpoint (Mesh j.castSucc) (Mesh j.succ)) < 0 ∧ Mesh j.castSucc = u)).card)) := by
  classical
  have hgu : g u = 0 := by rw [hg u,(hC _ hpC).mp hroot,zero_div]
  have hhu : h u = 0 := by rw [hh u,(hD _ hpD).mp hroot,zero_div]
  obtain ⟨l,r,hl,hr,hlr,hcard⟩ := actual_mesh_zero_incidence_card m mesh hmono hstart hend
    actualMeshMidpoint g hg0 hg1 hgap u hgu
  obtain ⟨L,R,hL,hR,hLR,Hcard⟩ := actual_mesh_zero_incidence_card M Mesh Hmono Hstart Hend
    actualMeshMidpoint h hh0 hh1 Hgap u hhu
  have hxu : mesh l.castSucc < u := hl ▸ hmono (by change l.val < l.val+1; omega)
  have huy : u < mesh r.succ := hr ▸ hmono (by change r.val < r.val+1; omega)
  have hXu : Mesh L.castSucc < u := hL ▸ Hmono (by change L.val < L.val+1; omega)
  have huY : u < Mesh R.succ := hR ▸ Hmono (by change R.val < R.val+1; omega)
  have hsl := actualMeshMidpoint_between (mesh l.castSucc) u hxu
  have hsr := actualMeshMidpoint_between u (mesh r.succ) huy
  have hsL := actualMeshMidpoint_between (Mesh L.castSucc) u hXu
  have hsR := actualMeshMidpoint_between u (Mesh R.succ) huY
  have hgl : ∀ t, mesh l.castSucc < t → t < u → g t ≠ 0 := by
    intro t ht0 ht1
    apply hgap l t ht0
    rwa [hl]
  have hgr : ∀ t, u < t → t < mesh r.succ → g t ≠ 0 := by
    intro t ht0 ht1
    apply hgap r t _ ht1
    rwa [hr]
  have hhl : ∀ t, Mesh L.castSucc < t → t < u → h t ≠ 0 := by
    intro t ht0 ht1
    apply Hgap L t ht0
    rwa [hL]
  have hhr : ∀ t, u < t → t < Mesh R.succ → h t ≠ 0 := by
    intro t ht0 ht1
    apply Hgap R t _ ht1
    rwa [hR]
  rw [hcard,Hcard]
  have hactual := actual_shared_axis_trace_sector_incidence_parity b γ u hu hroot
    C D hpC hpD hC hD g h c d hc hd hg hh
    (mesh l.castSucc) (mesh r.succ)
    (actualMeshMidpoint (mesh l.castSucc) u) (actualMeshMidpoint u (mesh r.succ))
    (Mesh L.castSucc) (Mesh R.succ)
    (actualMeshMidpoint (Mesh L.castSucc) u) (actualMeshMidpoint u (Mesh R.succ))
    hxu huy hXu huY hsl hsr hsL hsR hgl hgr hhl hhr
  simpa only [hl,hr,hL,hR] using hactual


lemma actual_interval_exp_off_one (u v : Interval) (hu : u ≠ 1) (hv : v ≠ 1)
    (he : Circle.exp (2*Real.pi*u.val) = Circle.exp (2*Real.pi*v.val)) : u = v := by
  have hmem (t : Interval) (ht : t ≠ 1) :
      2*Real.pi*t.val ∈ Set.Ico (0 : ℝ) (2*Real.pi) := by
    have hlt : t.val < 1 := lt_of_le_of_ne t.property.2 (by
      intro h
      apply ht
      exact Subtype.ext h)
    constructor
    · exact mul_nonneg (by positivity : 0 ≤ 2*Real.pi) t.property.1
    · have hh := mul_lt_mul_of_pos_left hlt (by positivity : 0 < 2*Real.pi)
      simpa only [mul_one] using hh
  have hh := Circle.exp_injOn_Ico (by simp : 2*Real.pi-0 ≤ 2*Real.pi)
    (hmem u hu) (hmem v hv) he
  apply Subtype.ext
  exact mul_left_cancel₀ (by positivity : (2*Real.pi : ℝ) ≠ 0) hh

/-- The actual cylinder quotient has a unique square representative away from
its seam. This computes the fiber, without an assumed quotient certificate. -/
theorem actual_cylinder_interior_phase_fiber_unique (q r : Interval × Interval)
    (hr : r.2 ∈ Set.Ioo (0 : Interval) 1)
    (he : (q.1,Circle.exp (2*Real.pi*q.2.val)) =
      (r.1,Circle.exp (2*Real.pi*r.2.val))) : q = r := by
  have hangle := congrArg Prod.snd he
  have hq1 : q.2 ≠ 1 := by
    intro hq
    have hzero : r.2 = 0 := actual_interval_exp_off_one r.2 0
      (ne_of_lt hr.2) (by norm_num) (by simpa [hq] using hangle.symm)
    exact (ne_of_gt hr.1) hzero
  have htime : q.1 = r.1 := congrArg (fun z : Interval × Circle => z.1) he
  exact Prod.ext htime
    (actual_interval_exp_off_one q.2 r.2 hq1 (ne_of_lt hr.2) hangle)

/-- The exact seam fiber consists of the two actual square boundary copies. -/
theorem actual_cylinder_seam_phase_fiber (u : Interval) :
    Circle.exp (2*Real.pi*u.val) = 1 ↔ u = 0 ∨ u = 1 := by
  constructor
  · intro he
    by_cases hu : u = 1
    · exact Or.inr hu
    · left
      exact actual_interval_exp_off_one u 0 hu (by norm_num) (by simpa using he)
  · rintro (rfl | rfl) <;> simp

/-- Complete exact point fiber of the concrete parameter-cylinder projection. -/
theorem actual_cylinder_projection_fiber (q r : Interval × Interval) :
    (q.1,Circle.exp (2*Real.pi*q.2.val)) = (r.1,Circle.exp (2*Real.pi*r.2.val)) ↔
      q.1 = r.1 ∧ (q.2 = r.2 ∨ q.2 = 0 ∧ r.2 = 1 ∨ q.2 = 1 ∧ r.2 = 0) := by
  constructor
  · intro he
    have ht := congrArg Prod.fst he
    have ha := congrArg Prod.snd he
    refine ⟨ht,?_⟩
    by_cases hq : q.2 = 1
    · have hr : r.2 = 0 ∨ r.2 = 1 := actual_cylinder_seam_phase_fiber r.2 |>.mp
        (by simpa [hq] using ha.symm)
      rcases hr with hr | hr
      · exact Or.inr (Or.inr ⟨hq,hr⟩)
      · exact Or.inl (hq.trans hr.symm)
    · by_cases hr : r.2 = 1
      · have hq0 : q.2 = 0 := by
          rcases (actual_cylinder_seam_phase_fiber q.2).mp (by simpa [hr] using ha) with hz | hz
          · exact hz
          · exact False.elim (hq hz)
        exact Or.inr (Or.inl ⟨hq0,hr⟩)
      · exact Or.inl (actual_interval_exp_off_one q.2 r.2 hq hr ha)
  · rintro ⟨ht,ha⟩
    apply Prod.ext
    · exact ht
    · rcases ha with ha | ⟨hq,hr⟩ | ⟨hq,hr⟩
      · rw [ha]
      · simp [hq,hr]
      · simp [hq,hr]


/-- A returning component of a genuinely regularized count-decreasing homotopy
selects an embedded original subarc homotopic relative endpoints into the fixed
curve. The regularization and returning component are conclusions to construct,
not hypotheses supplied by the caller. -/
theorem actual_proper_cylinder_arc_produces_annular_cap_with_cut_pair
    {x y : unitInterval × Circle} (p : Path x y)
    (hp : Topology.IsEmbedding p) (hx : x.1 = 0) (hy : y.1 = 0)
    (hi : ∀ t ∈ Set.Ioo (0 : unitInterval) 1, 0 < (p t).1) :
    ∃ A : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween A (actualOuterCylinderSchoenflies x) (actualOuterCylinderSchoenflies y) ∧
      A ⊆ Set.range actualCylinderBottomCircle ∧
      Schoenflies.IsJordanCurve (A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p)) ∧
      ((A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p)) ∪
        Schoenflies.inside (A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p))) ⊆
          Set.range actualOuterCylinderSchoenflies ∧
      ∃ B : Set Schoenflies.Plane, Schoenflies.IsCutPair (Set.range actualCylinderBottomCircle)
        (actualOuterCylinderSchoenflies x) (actualOuterCylinderSchoenflies y) A B := by
  let γ : Path (actualOuterCylinderSchoenflies x) (actualOuterCylinderSchoenflies y) :=
    p.map actualOuterCylinderSchoenflies.continuous
  have hγ : Topology.IsEmbedding γ := actualOuterCylinderSchoenflies_embedding.comp hp
  have hArc := actual_embedded_path_isArcBetween γ hγ
  have hleft : actualOuterCylinderSchoenflies x ∈ Set.range actualCylinderBottomCircle := by
    refine ⟨x.2,?_⟩
    apply congrArg actualOuterCylinderSchoenflies
    exact Prod.ext hx.symm rfl
  have hright : actualOuterCylinderSchoenflies y ∈ Set.range actualCylinderBottomCircle := by
    refine ⟨y.2,?_⟩
    apply congrArg actualOuterCylinderSchoenflies
    exact Prod.ext hy.symm rfl
  have hPi : Set.range γ \ {actualOuterCylinderSchoenflies x,actualOuterCylinderSchoenflies y} ⊆
      Schoenflies.inside (Set.range actualCylinderBottomCircle) := by
    rintro z ⟨⟨t,rfl⟩,hnot⟩
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      exact hnot (by simp)
    have ht1 : t ≠ 1 := by
      intro he
      subst t
      exact hnot (by simp)
    have htI : t ∈ Set.Ioo (0 : unitInterval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩
    rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right]
    change ‖actualOuterCylinderSchoenflies (p t)‖ < 2
    rw [actualOuterCylinderSchoenflies_norm]
    have hpos : 0 < (p t).1.val := hi t htI
    linarith
  have hHole : Metric.ball (0 : Schoenflies.Plane) 1 ⊆
      Schoenflies.inside (Set.range actualCylinderBottomCircle) \ Set.range γ := by
    intro z hz
    have hnorm : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    constructor
    · rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right]
      linarith
    · rintro ⟨t,he⟩
      have hbounds : 1 ≤ ‖actualOuterCylinderSchoenflies (p t)‖ := by
        rw [actualOuterCylinderSchoenflies_norm]
        linarith [(p t).1.property.2]
      change actualOuterCylinderSchoenflies (p t) = z at he
      rw [he] at hbounds
      linarith
  obtain ⟨A₁,A₂,hcut⟩ := Schoenflies.exists_isCutPair actualCylinderBottomCircle_jordan
    hleft hright hArc.ne
  obtain ⟨A,hChoice,hA,hJ,hDisjoint⟩ := actual_crosscut_cap_avoiding_connected_hole
    actualCylinderBottomCircle_jordan hArc hcut hPi
    (convex_ball (0 : Schoenflies.Plane) 1).isPreconnected hHole
  have hAC : A ⊆ Set.range actualCylinderBottomCircle := by
    rcases hChoice with rfl | rfl
    · exact hcut.fst_subset
    · exact hcut.snd_subset
  have hγClosed : Set.range γ ⊆ Schoenflies.inside (Set.range actualCylinderBottomCircle) ∪
      Set.range actualCylinderBottomCircle := by
    intro z hz
    by_cases he : z ∈ ({actualOuterCylinderSchoenflies x,actualOuterCylinderSchoenflies y} : Set Schoenflies.Plane)
    · rcases (by simpa using he : z = actualOuterCylinderSchoenflies x ∨ z = actualOuterCylinderSchoenflies y) with rfl | rfl
      · exact Or.inr hleft
      · exact Or.inr hright
    · exact Or.inl (hPi ⟨hz,he⟩)
  have hBoundary : A ∪ Set.range γ ⊆ Schoenflies.inside (Set.range actualCylinderBottomCircle) ∪
      Set.range actualCylinderBottomCircle := by
    intro z hz
    rcases hz with hzA | hzP
    · exact Or.inr (hAC hzA)
    · exact hγClosed hzP
  have hInside := CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
    (Schoenflies.jordan_curve_theorem actualCylinderBottomCircle_jordan)
    (Schoenflies.jordan_curve_theorem hJ) hBoundary
  have hBound : (A ∪ Set.range γ) ∪ Schoenflies.inside (A ∪ Set.range γ) ⊆
      Schoenflies.inside (Set.range actualCylinderBottomCircle) ∪ Set.range actualCylinderBottomCircle := by
    intro z hz
    rcases hz with hzB | hzIn
    · exact hBoundary hzB
    · exact Or.inl (hInside hzIn)
  refine ⟨A,hA,hAC,hJ,?_,?_⟩
  · intro z hz
    rw [actualOuterCylinderSchoenflies_range]
    change 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2
    constructor
    · apply le_of_not_gt
      intro hlt
      have hzHole : z ∈ Metric.ball (0 : Schoenflies.Plane) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hlt
      exact Set.disjoint_left.mp hDisjoint hz hzHole
    · rcases hBound hz with hzi | hzC
      · rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right] at hzi
        exact hzi.le
      · rw [actualCylinderBottomCircle_range,Metric.mem_sphere,dist_zero_right] at hzC
        exact hzC.le
  · rcases hChoice with rfl | rfl
    · exact ⟨A₂,hcut⟩
    · exact ⟨A₁,hcut.symm⟩


attribute [local instance] Classical.propDecidable
/-- Construct a real smaller cut arc for any distinct new returning boundary
endpoint, and prove strict decrease of the actual finite event count. -/
theorem actual_boundary_cut_pair_with_strict_event_decrease
    {V : Type*} [DecidableEq V] (E : Finset V) (f : V → Plane)
    (hf : Function.Injective f) {C A B : Set Plane} (a b z y : V)
    (hcut : IsCutPair C (f a) (f b) A B)
    (hzE : z ∈ E) (hzA : f z ∈ A) (hza : z ≠ a) (hzb : z ≠ b)
    (hyA : f y ∈ A) (hyz : y ≠ z) :
    ∃ R T, IsCutPair C (f z) (f y) R T ∧ R ⊆ A ∧
      (E.filter (fun x => f x ∈ R ∧ x ≠ z ∧ x ≠ y)).card <
        (E.filter (fun x => f x ∈ A ∧ x ≠ a ∧ x ≠ b)).card := by
  have hzfa : f z ≠ f a := fun h => hza (hf h)
  have hzfb : f z ≠ f b := fun h => hzb (hf h)
  by_cases hya : y = a
  · subst y
    obtain ⟨R,T,S,U,hR,hS,hRA,hSA,hunion,hbR,haS⟩ :=
      actual_boundary_cut_pair_split_at_interior_event hcut hzA hzfa hzfb
    refine ⟨R,T,hR,hRA,?_⟩
    exact actual_boundary_subarc_event_count_strict_decrease E (f ⁻¹' A) (f ⁻¹' R)
      a b z hzE hzA hza hzb (fun x hx => hRA hx) hbR
  · by_cases hyb : y = b
    · subst y
      have hrev : IsCutPair C (f b) (f a) A B := by
        refine ⟨hcut.fst.reverse,hcut.snd.reverse,hcut.union_eq,?_⟩
        rw [hcut.inter_eq]
        ext x
        simp [or_comm]
      obtain ⟨R,T,S,U,hR,hS,hRA,hSA,hunion,haR,hbS⟩ :=
        actual_boundary_cut_pair_split_at_interior_event hrev hzA hzfb hzfa
      refine ⟨R,T,hR,hRA,?_⟩
      have hcount := actual_boundary_subarc_event_count_strict_decrease E (f ⁻¹' A) (f ⁻¹' R)
        b a z hzE hzA hzb hza (fun x hx => hRA hx) haR
      simpa only [Set.mem_preimage,and_comm,and_left_comm,and_assoc] using hcount
    · obtain ⟨R,T,hR,hRA,haR,hbR⟩ := actual_boundary_cut_pair_between_interior_events
        hcut hzA hyA (fun h => hyz (hf h).symm) hzfa hzfb
        (fun h => hya (hf h)) (fun h => hyb (hf h))
      refine ⟨R,T,hR,hRA,?_⟩
      exact actual_interior_boundary_subarc_event_count_strict_decrease E (f ⁻¹' A) (f ⁻¹' R)
        a b z y hzE hzA hza hzb (fun x hx => hRA hx) haR hbR

/-- Real fixed-endpoint homotopy inside a supplied actual Jordan cap, using
its proved contractibility and the actual annular inverse. -/
theorem actual_cylinder_paths_homotopic_in_jordan_cap
    {J : Set Schoenflies.Plane} (hJ : Schoenflies.IsJordanCurve J)
    (hR : (J ∪ Schoenflies.inside J) ⊆ Set.range actualOuterCylinderSchoenflies)
    {x y : unitInterval × Circle} (p q : Path x y)
    (hp : Set.range (actualOuterCylinderSchoenflies ∘ p) ⊆ J ∪ Schoenflies.inside J)
    (hq : Set.range (actualOuterCylinderSchoenflies ∘ q) ⊆ J ∪ Schoenflies.inside J) :
    p.Homotopic q := by
  let D : Set Schoenflies.Plane := J ∪ Schoenflies.inside J
  have hpt (t : unitInterval) : actualOuterCylinderSchoenflies (p t) ∈ D := hp ⟨t,rfl⟩
  have hqt (t : unitInterval) : actualOuterCylinderSchoenflies (q t) ∈ D := hq ⟨t,rfl⟩
  let rx : D := ⟨actualOuterCylinderSchoenflies x,by simpa using hpt 0⟩
  let ry : D := ⟨actualOuterCylinderSchoenflies y,by simpa using hpt 1⟩
  let pD : Path rx ry := {
    toFun := fun t => ⟨actualOuterCylinderSchoenflies (p t),hpt t⟩
    continuous_toFun := (actualOuterCylinderSchoenflies.continuous.comp p.continuous).subtype_mk _
    source' := by apply Subtype.ext; simp [rx]
    target' := by apply Subtype.ext; simp [ry] }
  let qD : Path rx ry := {
    toFun := fun t => ⟨actualOuterCylinderSchoenflies (q t),hqt t⟩
    continuous_toFun := (actualOuterCylinderSchoenflies.continuous.comp q.continuous).subtype_mk _
    source' := by apply Subtype.ext; simp [rx]
    target' := by apply Subtype.ext; simp [ry] }
  let E := actualOuterCylinderSchoenflies_embedding.toHomeomorph
  let back : C(D,unitInterval × Circle) :=
    ⟨fun z => E.symm ⟨z.val,hR z.property⟩,
      E.symm.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hback (z : D) : actualOuterCylinderSchoenflies (back z) = z.val :=
    congrArg Subtype.val (E.apply_symm_apply ⟨z.val,hR z.property⟩)
  have hrx : back rx = x := actualOuterCylinderSchoenflies_embedding.injective (hback rx)
  have hry : back ry = y := actualOuterCylinderSchoenflies_embedding.injective (hback ry)
  have H := (actual_closed_jordan_region_paths_homotopic hJ pD qD).map back
  have H' := H.pathCast hrx.symm hry.symm
  have hpeq : (pD.map back.continuous).cast hrx.symm hry.symm = p := by
    exact DFunLike.ext _ _ (fun t =>
      actualOuterCylinderSchoenflies_embedding.injective (hback (pD t)))
  have hqeq : (qD.map back.continuous).cast hrx.symm hry.symm = q := by
    exact DFunLike.ext _ _ (fun t =>
      actualOuterCylinderSchoenflies_embedding.injective (hback (qD t)))
  rw [hpeq,hqeq] at H'
  exact H'
/-- Lift the actual selected boundary side of a Jordan cap and retain its
exact image, so a subsequently proved event exclusion applies to this path. -/
theorem actual_selected_cap_boundary_path_with_homotopy
    {x y : unitInterval × Circle} (p : Path x y) {A : Set Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A (actualOuterCylinderSchoenflies x)
      (actualOuterCylinderSchoenflies y))
    (hAC : A ⊆ Set.range actualCylinderBottomCircle)
    (hJ : Schoenflies.IsJordanCurve (A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p)))
    (hBound : ((A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p)) ∪
        Schoenflies.inside (A ∪ Set.range (actualOuterCylinderSchoenflies ∘ p))) ⊆
          Set.range actualOuterCylinderSchoenflies) :
    ∃ q : Path x y, Topology.IsEmbedding q ∧
      (∀ t, (q t).1 = 0) ∧ actualOuterCylinderSchoenflies '' Set.range q = A ∧
      p.Homotopic q := by
  have hAnn : A ⊆ Set.range actualOuterCylinderSchoenflies :=
    fun z hz => hBound (Or.inl (Or.inl hz))
  obtain ⟨q,hq,himage⟩ := actual_annular_arc_lifts_to_embedded_cylinder_path hA hAnn
  have hqA (t : unitInterval) : actualOuterCylinderSchoenflies (q t) ∈ A := by
    rw [←himage]
    exact ⟨q t,⟨t,rfl⟩,rfl⟩
  have hbottom (t : unitInterval) : (q t).1 = 0 := by
    obtain ⟨z,hz⟩ := hAC (hqA t)
    have he : q t = (0,z) := actualOuterCylinderSchoenflies_embedding.injective hz.symm
    exact congrArg Prod.fst he
  refine ⟨q,hq,hbottom,himage,?_⟩
  apply actual_cylinder_paths_homotopic_in_jordan_cap hJ hBound p q
  · intro z hz
    exact Or.inl (Or.inr hz)
  · rintro z ⟨t,rfl⟩
    exact Or.inl (Or.inl (hqA t))

theorem count_decreasing_isotopy_has_returning_subarc
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b a' : EssentialCurve S) (ht : Transverse a.val b.val)
    (haa' : AmbientIsotopy.Rel a.val.image a'.val.image)
    (ht' : Transverse a'.val b.val)
    (hcount : ht'.1.toFinset.card < ht.1.toFinset.card) :
    ∃ u v : S, u ≠ v ∧ u ∈ a.val.image ∩ b.val.image ∧
      v ∈ a.val.image ∩ b.val.image ∧
      ∃ f g : Path u v,
        Topology.IsEmbedding f ∧ Set.range f ⊆ a.val.image ∧
        Set.range g ⊆ b.val.image ∧
        f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.val.imageᶜ ∧
        f.Homotopic g := by
  classical
  obtain ⟨H,hH⟩ := haa'
  have hless : ht'.1.toFinset.card < ht.1.toFinset.card := hcount
  obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = e := (funext he).symm
  let A : Set Circle := {z | a.val.map z ∈ b.val.image}
  let E : Set Circle := {z | H.finalMap (a.val.map z) ∈ b.val.image}
  have hA : A.Finite := (ht.1.preimage a.val.embedded.injective.injOn).subset
    (fun z hz => ⟨⟨z,rfl⟩,hz⟩)
  have hE : E.Finite := by
    have hinj : Function.Injective (H.finalMap ∘ a.val.map) := by
      rw [hfinal]; exact e.injective.comp a.val.embedded.injective
    apply (ht'.1.preimage hinj.injOn).subset
    intro z hz
    refine ⟨?_,hz⟩
    rw [← hH]
    exact ⟨a.val.map z,⟨z,rfl⟩,rfl⟩
  letI : Infinite (Set.Ioo (0 : ℝ) Real.pi) := Set.Ioo.infinite Real.pi_pos
  letI : Infinite Circle := Infinite.of_injective
    (fun t : Set.Ioo (0 : ℝ) Real.pi => Circle.exp t.val) (by
      intro t u heq
      apply Subtype.ext
      exact Circle.exp_injOn_Icc (by linarith [Real.pi_pos] : Real.pi-(0:ℝ) < 2*Real.pi)
        ⟨t.property.1.le,t.property.2.le⟩ ⟨u.property.1.le,u.property.2.le⟩ heq)
  obtain ⟨z₀,hz₀⟩ := (hA.union hE).exists_notMem
  have hzStart : a.val.map z₀ ∉ b.val.image ∧ H.finalMap (a.val.map z₀) ∉ b.val.image := by
    simpa only [Set.mem_union,Set.mem_setOf_eq,not_or,A,E] using hz₀
  let F : C(Interval × Interval,S) :=
    ⟨fun z => H.map (z.1,a.val.map (z₀ * Circle.exp (2*Real.pi*z.2.val))),
      H.map.continuous.comp (continuous_fst.prodMk
        (a.val.embedded.continuous.comp (continuous_const.mul
          (Circle.exp.continuous.comp (by fun_prop)))))⟩
  have endpointEventCount (c : Curve S) (htc : Transverse c b.val)
      (hz : c.map z₀ ∉ b.val.image) :
      ∃ h : ((intervalCurveLoopFrom c z₀) ⁻¹' (b.val.image ∩ c.image)).Finite,
        h.toFinset.card = htc.1.toFinset.card := by
    have hbc := transverse_symm_of_chart htc
    let γ := intervalCurveLoopFrom c z₀
    let events := γ ⁻¹' (b.val.image ∩ c.image)
    have hends : γ 0 = c.map z₀ ∧ γ 1 = c.map z₀ := by
      simp [γ, intervalCurveLoopFrom, intervalCircleParameterFrom,
        intervalCircleParameter]
    have heventInterior (u : unitInterval) (hu : u ∈ events) :
        0 < (u : ℝ) ∧ (u : ℝ) < 1 := by
      have huimage : γ u ∈ b.val.image := hu.1
      constructor
      · by_contra h
        have heq : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) u.property.1)
        rw [heq, hends.1] at huimage
        exact hz huimage
      · by_contra h
        have heq : u = 1 := Subtype.ext (le_antisymm u.property.2 (le_of_not_gt h))
        rw [heq, hends.2] at huimage
        exact hz huimage
    have hγinj : Set.InjOn γ events := by
      intro u hu v hv heq
      have huI := heventInterior u hu
      have hvI := heventInterior v hv
      have hcircle := c.embedded.injective heq
      change z₀ * Circle.exp (2 * Real.pi * (u : ℝ)) =
        z₀ * Circle.exp (2 * Real.pi * (v : ℝ)) at hcircle
      have hexp := mul_left_cancel hcircle
      have hangle := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
        (by simp)
        (show 2 * Real.pi * (u : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
          ⟨mul_nonneg (by positivity) huI.1.le, by nlinarith [Real.pi_pos]⟩)
        (show 2 * Real.pi * (v : ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
          ⟨mul_nonneg (by positivity) hvI.1.le, by nlinarith [Real.pi_pos]⟩) hexp
      apply Subtype.ext
      nlinarith [Real.pi_pos]
    have hfiniteEvents : events.Finite := hbc.1.preimage hγinj
    have hexpRange : Circle.exp '' Set.Icc 0 (2 * Real.pi) = Set.univ := by
      simpa only [zero_add, Circle.exp_surjective.range_eq] using
        Circle.periodic_exp.image_Icc Real.two_pi_pos (0 : ℝ)
    have hparameterSurj : Function.Surjective (intervalCircleParameterFrom z₀) := by
      intro v
      have hv : z₀⁻¹ * v ∈ Circle.exp '' Set.Icc 0 (2 * Real.pi) := by
        rw [hexpRange]
        trivial
      obtain ⟨θ, hθI, hθ⟩ := hv
      let u : unitInterval := ⟨θ / (2 * Real.pi),
        ⟨div_nonneg hθI.1 Real.two_pi_pos.le,
          (div_le_one Real.two_pi_pos).mpr hθI.2⟩⟩
      refine ⟨u, ?_⟩
      change z₀ * Circle.exp (2 * Real.pi * (θ / (2 * Real.pi))) = v
      have hscale : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by
        field_simp
      rw [hscale, hθ]
      simp
    have hγrange : Set.range γ = c.image := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨intervalCircleParameterFrom z₀ u, rfl⟩
      · rintro ⟨v, rfl⟩
        obtain ⟨u, hu⟩ := hparameterSurj v
        exact ⟨u, by change c.map (intervalCircleParameterFrom z₀ u) = c.map v; rw [hu]⟩
    have hγbij : Set.BijOn γ events (b.val.image ∩ c.image) := by
      refine ⟨fun _ hu => hu, hγinj, ?_⟩
      intro x hx
      have hxrange : x ∈ Set.range γ := by rw [hγrange]; exact hx.2
      obtain ⟨u, hu⟩ := hxrange
      refine ⟨u, ?_, hu⟩
      change γ u ∈ b.val.image ∩ c.image
      rw [hu]
      exact hx
    refine ⟨hfiniteEvents,?_⟩
    rw [← Set.ncard_eq_toFinset_card _ hfiniteEvents,
      ← Set.ncard_eq_toFinset_card _ htc.1]
    exact hγbij.ncard_eq.trans (by rw [Set.inter_comm])
  obtain ⟨hzeroEvents,hzeroCount⟩ := endpointEventCount a.val ht hzStart.1
  let endCurve : Curve S := ⟨e ∘ a.val.map,e.isEmbedding.comp a.val.embedded⟩
  have hendImage : endCurve.image = a'.val.image := by
    change Set.range (e ∘ a.val.map) = a'.val.image
    rw [Set.range_comp,← hfinal]; exact hH
  have htEnd : Transverse endCurve b.val := by
    simpa only [Transverse,CrossesAt,hendImage] using ht'
  have hendStart : endCurve.map z₀ ∉ b.val.image := by
    change e (a.val.map z₀) ∉ b.val.image
    rw [← hfinal]; exact hzStart.2
  obtain ⟨honeEvents,honeCount⟩ := endpointEventCount endCurve htEnd hendStart
  have hendpointCounts : honeEvents.toFinset.card < hzeroEvents.toFinset.card := by
    rw [honeCount,hzeroCount]
    have hset : htEnd.1.toFinset = ht'.1.toFinset := by
      ext x; simp only [Set.Finite.mem_toFinset,Set.mem_inter_iff,hendImage]
    rw [hset]; exact hless
  -- A finite embedded graph may have even-valence interior branches. Component
  -- parity, not an assumed one-manifold classification, suffices for returning
  -- endpoint cancellation AFTER the graph and its actual component labels exist.
  have componentParityForcesReturningPair {X L : Type} [DecidableEq X]
      (B T : Finset X) (component : X → L)
      (heven : ∀ c, Even ((B ∪ T).filter (fun x => component x = c)).card)
      (hcount : T.card < B.card) :
      ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ component x = component y := by
    classical
    by_contra hno
    have hsame (x y : X) (hx : x ∈ B) (hy : y ∈ B)
        (hxy : component x = component y) : x = y := by
      by_contra hne
      exact hno ⟨x,hx,y,hy,hne,hxy⟩
    have hpartner (x : X) (hx : x ∈ B) : ∃ y ∈ T, component y = component x := by
      by_contra h
      have hfilter : (B ∪ T).filter (fun y => component y = component x) = {x} := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_singleton]
        constructor
        · rintro ⟨hy,hc⟩
          rcases hy with hyB | hyT
          · exact hsame y x hyB hx hc
          · exact False.elim (h ⟨y,hyT,hc⟩)
        · intro hy
          subst y
          exact ⟨Or.inl hx,rfl⟩
      have hodd := heven (component x)
      rw [hfilter,Finset.card_singleton] at hodd
      norm_num at hodd
    let partner : X → X := fun x => if hx : x ∈ B then (hpartner x hx).choose else x
    have hmaps : Set.MapsTo partner (B : Set X) (T : Set X) := by
      intro x hx
      change x ∈ B at hx
      change partner x ∈ T
      simpa only [partner,dif_pos hx] using (hpartner x hx).choose_spec.1
    have hcomponent (x : X) (hx : x ∈ B) : component (partner x) = component x := by
      simpa only [partner,dif_pos hx] using (hpartner x hx).choose_spec.2
    have hinj : Set.InjOn partner (B : Set X) := by
      intro x hx y hy hxy
      apply hsame x y hx hy
      exact (hcomponent x hx).symm.trans ((congrArg component hxy).trans (hcomponent y hy))
    exact hcount.not_ge (Finset.card_le_card_of_injOn partner hmaps hinj)
  have graphComponentBoundaryParity {V : Type} [Fintype V] (G : SimpleGraph V)
      (B T : Finset V) (hodd : ∀ v, Odd (G.degree v) ↔ v ∈ B ∪ T) :
      ∀ c, Even ((B ∪ T).filter (fun v => G.connectedComponentMk v = c)).card := by
    classical
    intro c
    let H := G.induce c.supp
    have hdegree (v : c.supp) : H.degree v = G.degree v.val := by
      apply SimpleGraph.degree_induce_of_neighborSet_subset
      intro w hw
      change G.connectedComponentMk w = c
      exact (SimpleGraph.ConnectedComponent.sound hw.reachable).symm.trans
        v.property
    have hmap : (Finset.univ.filter (fun v : c.supp => Odd (H.degree v))).image Subtype.val =
        (B ∪ T).filter (fun v => G.connectedComponentMk v = c) := by
      ext v
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
        hdegree,hodd]
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨hw,w.property⟩
      · rintro ⟨hv,hc⟩
        exact ⟨⟨v,hc⟩,hv,rfl⟩
    rw [← hmap,Finset.card_image_of_injective _ Subtype.val_injective]
    exact H.even_card_odd_degree_vertices
  have graphReturnsToBottom {V : Type} [Fintype V] (G : SimpleGraph V)
      (B T : Finset V) (hodd : ∀ v, Odd (G.degree v) ↔ v ∈ B ∪ T)
      (hcount : T.card < B.card) :
      ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧ ∃ p : G.Walk x y, p.IsPath := by
    classical
    obtain ⟨x,hx,y,hy,hne,hcomp⟩ := componentParityForcesReturningPair B T
      G.connectedComponentMk (graphComponentBoundaryParity G B T hodd) hcount
    have hr : G.Reachable x y := (SimpleGraph.ConnectedComponent.eq.mp hcomp)
    obtain ⟨p,hp⟩ := hr.exists_isPath
    exact ⟨x,hx,y,hy,hne,p,hp⟩
  let C := selectedAxisChart b.val
  let D := cutAtlasDomain b.val
  have hchart (p : b.val.image) : p.val ∈ (C p).source ∧ C p p.val = (0, 0) ∧
      ∀ x ∈ (C p).source, x ∈ b.val.image ↔ (C p x).1 = 0 := by
    let H := embedded_curve_has_local_axis_chart b.val p p.property
    let U := H.choose
    let V := H.choose_spec.choose
    let hp := H.choose_spec.choose_spec.choose
    let h := H.choose_spec.choose_spec.choose_spec.choose
    let spec := H.choose_spec.choose_spec.choose_spec.choose_spec
    have hCs : (C p).source = U := by simp [C, selectedAxisChart, H, U, V, hp, h, crossingPartialChart]
    have hval (x : S) (hx : x ∈ U) : C p x = (h ⟨x, hx⟩ : ℝ × ℝ) := by
      change crossingPartialChart U V spec.1 spec.2.1 ⟨p, hp⟩ h x = _
      simp only [crossingPartialChart, OpenPartialHomeomorph.trans_apply,
        Homeomorph.toOpenPartialHomeomorph_apply]
      change (h (((⟨U, spec.1⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
        ⟨⟨p, hp⟩⟩).symm x) : ℝ × ℝ) = (h ⟨x, hx⟩ : ℝ × ℝ)
      have hinv := ((⟨U, spec.1⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
        ⟨⟨p, hp⟩⟩).left_inv (show (⟨x, hx⟩ : U) ∈ Set.univ from trivial)
      change ((⟨U, spec.1⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
        ⟨⟨p, hp⟩⟩).symm x = ⟨x, hx⟩ at hinv
      rw [hinv]
    refine ⟨hCs.symm ▸ hp, (hval p hp).trans spec.2.2.1, ?_⟩
    intro x hx
    rw [hval x (hCs ▸ hx)]
    have hxU : x ∈ U := hCs ▸ hx
    exact spec.2.2.2 x hxU
  have hclosed : IsClosed b.val.image := by
    simpa [Curve.image, Set.image_univ] using (isCompact_univ.image b.val.embedded.continuous).isClosed
  have hDopen : ∀ i, IsOpen (D i) := by
    intro i
    cases i with
    | none => exact hclosed.isOpen_compl
    | some p => exact (C p).open_source
  have hDmem : ∀ x, x ∈ D (cutAtlasIndexAt b.val x) := by
    intro x
    by_cases hx : x ∈ b.val.image
    · simpa [cutAtlasIndexAt, D, cutAtlasDomain, hx, C] using (hchart ⟨x, hx⟩).1
    · simpa [cutAtlasIndexAt, D, cutAtlasDomain, hx] using hx
  have convexChartAt (p : S) :
      ∃ e : OpenPartialHomeomorph S (ℝ × ℝ), p ∈ e.source ∧ Convex ℝ e.target ∧
        (Disjoint e.source b.val.image ∨
          ∀ x ∈ e.source, x ∈ b.val.image ↔ (e x).1 = 0) := by
    by_cases hp : p ∈ b.val.image
    · let E := C ⟨p,hp⟩
      have hpE : p ∈ E.source := (hchart ⟨p,hp⟩).1
      have hpEt : E p ∈ E.target := E.map_source hpE
      obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp E.open_target (E p) hpEt
      let e := (E.symm.restrOpen (Metric.ball (E p) r) Metric.isOpen_ball).symm
      have hsource : e.source = E.source ∩ E ⁻¹' Metric.ball (E p) r := rfl
      have htarget : e.target = Metric.ball (E p) r := by
        change E.target ∩ Metric.ball (E p) r = Metric.ball (E p) r
        exact Set.inter_eq_right.mpr hball
      refine ⟨e,hsource.symm ▸ ⟨hpE,Metric.mem_ball_self hr⟩,?_,Or.inr ?_⟩
      · rw [htarget]; exact convex_ball _ _
      · intro x hx
        have hxE := (hsource ▸ hx).1
        exact (hchart ⟨p,hp⟩).2.2 x hxE
    · let L : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
        ((EuclideanSpace.equiv (Fin 2) ℝ).trans
          (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
      let E := (chartAt (EuclideanSpace ℝ (Fin 2)) p).trans L.toOpenPartialHomeomorph
      have hpE : p ∈ E.source := by
        change p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' Set.univ
        exact ⟨mem_chart_source _ p,Set.mem_univ _⟩
      let W := E.target ∩ E.symm ⁻¹' b.val.imageᶜ
      have hW : IsOpen W := E.isOpen_inter_preimage_symm hclosed.isOpen_compl
      have hpW : E p ∈ W := ⟨E.map_source hpE,by change E.symm (E p) ∉ b.val.image; rwa [E.left_inv hpE]⟩
      obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW (E p) hpW
      let e := (E.symm.restrOpen (Metric.ball (E p) r) Metric.isOpen_ball).symm
      have hsource : e.source = E.source ∩ E ⁻¹' Metric.ball (E p) r := rfl
      have htarget : e.target = Metric.ball (E p) r := by
        change E.target ∩ Metric.ball (E p) r = Metric.ball (E p) r
        exact Set.inter_eq_right.mpr (fun x hx => (hball hx).1)
      refine ⟨e,hsource.symm ▸ ⟨hpE,Metric.mem_ball_self hr⟩,?_,Or.inl ?_⟩
      · rw [htarget]; exact convex_ball _ _
      · apply Set.disjoint_left.mpr
        intro x hx hxb
        have hxE := hsource ▸ hx
        have hno := (hball hxE.2).2
        change E.symm (E x) ∉ b.val.image at hno
        rw [E.left_inv hxE.1] at hno
        exact hno hxb
  choose convexChart hconvexPoint hconvexTarget hconvexAxis using convexChartAt
  -- A vertex perturbation must lie in ALL incident chart neighborhoods.
  -- Local axis charts make the complement dense; compactness is not used as
  -- a substitute for transversality or trace regularity.
  have offComparisonInOpen (U : Set S) (hU : IsOpen U) (p : S) (hp : p ∈ U) :
      ∃ x ∈ U, x ∉ b.val.image := by
    by_cases hpb : p ∈ b.val.image
    · let E := convexChart p
      have hpE : p ∈ E.source := hconvexPoint p
      have haxis : ∀ x ∈ E.source, x ∈ b.val.image ↔ (E x).1 = 0 := by
        rcases hconvexAxis p with hd | ha
        · exact False.elim ((Set.disjoint_left.mp hd) hpE hpb)
        · exact ha
      have hcenter : (E p).1 = 0 := (haxis p hpE).mp hpb
      have hW : IsOpen (E '' (E.source ∩ U)) := E.isOpen_image_source_inter hU
      obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW (E p) ⟨p,⟨hpE,hp⟩,rfl⟩
      let y : ℝ × ℝ := (r/2,(E p).2)
      have hy : y ∈ Metric.ball (E p) r := by
        rw [Metric.mem_ball,Prod.dist_eq]
        change max (dist (r/2) (E p).1) (dist (E p).2 (E p).2) < r
        rw [hcenter,dist_self,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
        exact max_lt (by linarith) hr
      obtain ⟨x,hx,he⟩ := hball hy
      refine ⟨x,hx.2,?_⟩
      intro hxb
      have hz := (haxis x hx.1).mp hxb
      rw [he] at hz
      change r/2 = 0 at hz
      linarith
    · exact ⟨p,hp,hpb⟩
  have simultaneousVertexPerturbation {I : Type} [Finite I]
      (U : I → Set S) (hU : ∀ i, IsOpen (U i)) (p : S) (hp : ∀ i, p ∈ U i) :
      ∃ x : S, x ∉ b.val.image ∧ ∀ i, x ∈ U i := by
    obtain ⟨x,hx,hxb⟩ := offComparisonInOpen (⋂ i, U i)
      (isOpen_iInter_of_finite hU) p (Set.mem_iInter.mpr hp)
    exact ⟨x,hxb,Set.mem_iInter.mp hx⟩
  have finiteGrid {I : Type} (U : I → Set S) (hU : ∀ i, IsOpen (U i))
      (hcov : ∀ z : Interval × Interval, ∃ i, F z ∈ U i) :
      ∃ n : ℕ, 0 < n ∧ ∃ chart : Fin n × Fin n → I,
        ∀ k : Fin n × Fin n, ∀ z : Interval × Interval,
          (k.1.val : ℝ)/n ≤ z.1.val → z.1.val ≤ (k.1.val+1 : ℝ)/n →
          (k.2.val : ℝ)/n ≤ z.2.val → z.2.val ≤ (k.2.val+1 : ℝ)/n →
          F z ∈ U (chart k) := by
    let V : I → Set (Interval × Interval) := fun i => F ⁻¹' U i
    have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage F.continuous
    have hcover : (Set.univ : Set (Interval × Interval)) ⊆ ⋃ i, V i := by
      intro z _; obtain ⟨i,hi⟩ := hcov z; exact Set.mem_iUnion.mpr ⟨i,hi⟩
    obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcover
    obtain ⟨n,hn,hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let anchor : Fin n → Interval := fun k => ⟨(k.val : ℝ)/n,by
      constructor
      · positivity
      · apply (div_le_one hnR).mpr
        exact le_of_lt (by exact_mod_cast k.isLt)⟩
    have hanchor (k : Fin n × Fin n) : ∃ i,
        Metric.ball (anchor k.1,anchor k.2) δ ⊆ V i := hball _ (Set.mem_univ _)
    choose chart hchart using hanchor
    refine ⟨n,hn,chart,?_⟩
    intro k z ht0 ht1 hs0 hs1
    apply hchart k
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    have hcoord (i : Fin n) (t : Interval)
        (hlo : (i.val : ℝ)/n ≤ t.val) (hhi : t.val ≤ (i.val+1 : ℝ)/n) :
        dist t (anchor i) < δ := by
      rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
      have heq : (i.val+1 : ℝ)/n = (i.val : ℝ)/n+(n : ℝ)⁻¹ := by rw [add_div,one_div]
      rw [heq] at hhi
      linarith
    exact ⟨hcoord k.1 z.1 ht0 ht1,hcoord k.2 z.2 hs0 hs1⟩
  have haloFiniteGrid {I : Type} (U : I → Set S) (hU : ∀ i, IsOpen (U i))
      (hcov : ∀ z : Interval × Interval, ∃ i, F z ∈ U i) :
      ∃ n : ℕ, 0 < n ∧ ∃ chart : Fin (n+1) × Fin (n+1) → I,
        ∀ k : Fin (n+1) × Fin (n+1), ∀ z : Interval × Interval,
          (k.1.val-1 : ℝ)/n ≤ z.1.val → z.1.val ≤ (k.1.val+1 : ℝ)/n →
          (k.2.val-1 : ℝ)/n ≤ z.2.val → z.2.val ≤ (k.2.val+1 : ℝ)/n →
          F z ∈ U (chart k) := by
    let V : I → Set (Interval × Interval) := fun i => F ⁻¹' U i
    have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage F.continuous
    have hcover : (Set.univ : Set (Interval × Interval)) ⊆ ⋃ i, V i := by
      intro z _; obtain ⟨i,hi⟩ := hcov z; exact Set.mem_iUnion.mpr ⟨i,hi⟩
    obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcover
    obtain ⟨n,hn,hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let anchor : Fin (n+1) → Interval := fun k => ⟨(k.val : ℝ)/n,by
      constructor
      · positivity
      · apply (div_le_one hnR).mpr
        exact_mod_cast (Nat.lt_succ_iff.mp k.isLt)⟩
    have hanchor (k : Fin (n+1) × Fin (n+1)) : ∃ i,
        Metric.ball (anchor k.1,anchor k.2) δ ⊆ V i := hball _ (Set.mem_univ _)
    choose chart hchart using hanchor
    refine ⟨n,hn,chart,?_⟩
    intro k z ht0 ht1 hs0 hs1
    apply hchart k
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    have hcoord (i : Fin (n+1)) (t : Interval)
        (hlo : (i.val-1 : ℝ)/n ≤ t.val) (hhi : t.val ≤ (i.val+1 : ℝ)/n) :
        dist t (anchor i) < δ := by
      rw [Subtype.dist_eq,Real.dist_eq,abs_lt]
      change -δ < t.val-(i.val : ℝ)/n ∧ t.val-(i.val : ℝ)/n < δ
      rw [sub_div,one_div] at hlo
      rw [add_div,one_div] at hhi
      constructor <;> linarith
    exact ⟨hcoord k.1 z.1 ht0 ht1,hcoord k.2 z.2 hs0 hs1⟩
  let chartDomain : S → Set S := fun p => (convexChart p).source
  have hDomainOpen : ∀ p, IsOpen (chartDomain p) := fun p => (convexChart p).open_source
  have hgridCover : ∀ z : Interval × Interval, ∃ i, F z ∈ chartDomain i :=
    fun z => ⟨F z,hconvexPoint (F z)⟩
  obtain ⟨n,hn,chart,hgrid⟩ := haloFiniteGrid chartDomain hDomainOpen hgridCover
  -- A uniform rational mesh can hit original endpoint events. Select one
  -- shared phase outside a finite forbidden set instead of moving the original
  -- horizontal boundary traces.
  have endpointAvoidingPhase (events : Set Interval) (hf : events.Finite)
      (m : ℕ) (hm : 0 < m) :
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        ∀ k : Fin m, ∀ t : Interval,
          t.val = (k.val+θ)/m → t ∉ events := by
    let forbidden : Set ℝ := ⋃ k : Fin m,
      (fun t : Interval => (m : ℝ)*t.val-k.val) '' events
    have hforbidden : forbidden.Finite := Set.finite_iUnion (fun k => hf.image _)
    obtain ⟨θ,hθ,havoid⟩ := (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).exists_notMem_finite hforbidden
    refine ⟨θ,hθ.1,hθ.2,?_⟩
    intro k t ht hevent
    apply havoid
    apply Set.mem_iUnion.mpr
    refine ⟨k,t,hevent,?_⟩
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    change (m : ℝ)*t.val-k.val = θ
    rw [ht]
    field_simp
    <;> ring
  obtain ⟨phase,hphase0,hphase1,hphaseAvoid⟩ := endpointAvoidingPhase
    ((intervalCurveLoopFrom a.val z₀) ⁻¹' (b.val.image ∩ a.val.image) ∪
      (intervalCurveLoopFrom endCurve z₀) ⁻¹' (b.val.image ∩ endCurve.image))
    (hzeroEvents.union honeEvents) n hn
  let phasePoint : Fin n → Interval := fun k =>
    ⟨(k.val+phase)/n,by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      constructor
      · exact (div_pos (by positivity) hnR).le
      · apply (div_le_one hnR).mpr
        have hkR : (k.val : ℝ)+1 ≤ n := by exact_mod_cast k.isLt
        linarith⟩
  have phasePointStrict (i j : Fin n) (hij : i < j) : phasePoint i < phasePoint j := by
    change (i.val+phase)/(n : ℝ) < (j.val+phase)/(n : ℝ)
    apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hn)).mpr
    have hijR : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith
  have phasePointEndpoints (k : Fin n) :
      (intervalCurveLoopFrom a.val z₀) (phasePoint k) ∉ b.val.image ∧
      (intervalCurveLoopFrom endCurve z₀) (phasePoint k) ∉ b.val.image := by
    have hav := hphaseAvoid k (phasePoint k) rfl
    constructor
    · intro hb
      exact hav (Or.inl ⟨hb,⟨intervalCircleParameterFrom z₀ (phasePoint k),rfl⟩⟩)
    · intro hb
      exact hav (Or.inr ⟨hb,⟨intervalCircleParameterFrom z₀ (phasePoint k),rfl⟩⟩)
  let phaseGrid : Fin (n+2) → Interval := fun i =>
    if h0 : i.val = 0 then 0 else
    if h1 : i.val = n+1 then 1 else
      phasePoint ⟨i.val-1,by omega⟩
  have phaseGridBounds (i : Fin (n+2)) :
      (i.val-1 : ℝ)/n ≤ (phaseGrid i).val ∧
      (phaseGrid i).val ≤ (i.val : ℝ)/n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases h0 : i.val = 0
    · have heq : phaseGrid i = 0 := by simp only [phaseGrid,dif_pos h0]
      rw [heq]
      change (i.val-1 : ℝ)/n ≤ 0 ∧ 0 ≤ (i.val : ℝ)/n
      rw [h0,Nat.cast_zero]
      norm_num
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hnR.le
    · by_cases h1 : i.val = n+1
      · have heq : phaseGrid i = 1 := by simp only [phaseGrid,dif_neg h0,dif_pos h1]
        rw [heq]
        change (i.val-1 : ℝ)/n ≤ 1 ∧ 1 ≤ (i.val : ℝ)/n
        have hiR : (i.val : ℝ) = (n : ℝ)+1 := by exact_mod_cast h1
        rw [hiR]
        constructor
        · rw [add_sub_cancel_right,div_self hnR.ne']
        · apply (le_div_iff₀ hnR).mpr
          linarith
      · simp only [phaseGrid,h0,dif_neg,h1]
        change (i.val-1 : ℝ)/n ≤ (((i.val-1 : ℕ) : ℝ)+phase)/n ∧
          (((i.val-1 : ℕ) : ℝ)+phase)/n ≤ (i.val : ℝ)/n
        have hiR : ((i.val-1 : ℕ) : ℝ) = (i.val : ℝ)-1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ i.val),Nat.cast_one]
        rw [hiR]
        constructor
        · exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith)
        · exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith)
  have phaseGridStrict : StrictMono phaseGrid := by
    intro i j hij
    have hijN : i.val < j.val := hij
    have hiLast : i.val ≠ n+1 := by omega
    have hjZero : j.val ≠ 0 := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    by_cases hiZero : i.val = 0
    · have hi : phaseGrid i = 0 := by simp only [phaseGrid,dif_pos hiZero]
      rw [hi]
      by_cases hjLast : j.val = n+1
      · have hj : phaseGrid j = 1 := by simp only [phaseGrid,dif_neg hjZero,dif_pos hjLast]
        rw [hj]
        change (0 : ℝ) < 1
        norm_num
      · simp only [phaseGrid,dif_neg hjZero,dif_neg hjLast]
        change (0 : ℝ) < (((j.val-1 : ℕ) : ℝ)+phase)/n
        positivity
    · by_cases hjLast : j.val = n+1
      · have hj : phaseGrid j = 1 := by simp only [phaseGrid,dif_neg hjZero,dif_pos hjLast]
        rw [hj]
        simp only [phaseGrid,dif_neg hiZero,dif_neg hiLast]
        change (((i.val-1 : ℕ) : ℝ)+phase)/n < 1
        apply (div_lt_one hnR).mpr
        have hiN : i.val-1+1 ≤ n := by omega
        have hiR : ((i.val-1 : ℕ) : ℝ)+1 ≤ n := by exact_mod_cast hiN
        linarith
      · simp only [phaseGrid,dif_neg hiZero,dif_neg hiLast,dif_neg hjZero,dif_neg hjLast]
        apply phasePointStrict
        change i.val-1 < j.val-1
        omega
  have orderedMeshCovers {m : ℕ} (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (hzero : mesh 0 = 0) (hone : mesh (Fin.last (m+1)) = 1) :
      ∀ t : Interval, ∃ k : Fin (m+1), mesh k.castSucc ≤ t ∧ t ≤ mesh k.succ := by
    classical
    intro t
    let A : Finset (Fin (m+2)) := Finset.univ.filter (fun i => mesh i ≤ t)
    have h0 : (0 : Fin (m+2)) ∈ A := by
      simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,hzero]
      exact t.property.1
    have hne : A.Nonempty := ⟨0,h0⟩
    let i := A.max' hne
    have hi : i ∈ A := Finset.max'_mem A hne
    have hiT : mesh i ≤ t := (Finset.mem_filter.mp hi).2
    by_cases hilast : i = Fin.last (m+1)
    · have ht1 : t = 1 := by
        apply Subtype.ext
        have hge : (1 : ℝ) ≤ t.val := by
          have hgeI : (1 : Interval) ≤ t := by simpa only [hilast,hone] using hiT
          change ((1 : Interval) : ℝ) ≤ t.val at hgeI
          norm_num at hgeI
          exact hgeI
        exact le_antisymm t.property.2 hge
      refine ⟨Fin.last m,?_,?_⟩
      · rw [ht1,← hone]
        apply hmono.monotone
        change m ≤ m+1
        omega
      · have hlast : (Fin.last m).succ = Fin.last (m+1) := by apply Fin.ext; rfl
        rw [hlast,hone,ht1]
    · have hiN : i.val < m+1 := by
        have hn := i.isLt
        have hneN : i.val ≠ m+1 := by intro h; apply hilast; apply Fin.ext; exact h
        omega
      let k : Fin (m+1) := ⟨i.val,hiN⟩
      have hik : k.castSucc = i := by apply Fin.ext; rfl
      refine ⟨k,hik.symm ▸ hiT,?_⟩
      by_contra hbad
      have hsT : mesh k.succ ≤ t := le_of_lt (lt_of_not_ge hbad)
      have hsA : k.succ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsT⟩
      have hsmax : k.succ ≤ i := Finset.le_max' A _ hsA
      have hsN : k.val+1 ≤ i.val := hsmax
      change i.val+1 ≤ i.val at hsN
      omega
  have phaseGridCovers (t : Interval) : ∃ k : Fin (n+1),
      phaseGrid k.castSucc ≤ t ∧ t ≤ phaseGrid k.succ :=
    orderedMeshCovers phaseGrid phaseGridStrict (by simp [phaseGrid]) (by simp [phaseGrid]) t
  have phaseGridCellCover (k : Fin (n+1) × Fin (n+1)) (z : Interval × Interval)
      (ht0 : phaseGrid k.1.castSucc ≤ z.1) (ht1 : z.1 ≤ phaseGrid k.1.succ)
      (hs0 : phaseGrid k.2.castSucc ≤ z.2) (hs1 : z.2 ≤ phaseGrid k.2.succ) :
      F z ∈ chartDomain (chart k) := by
    apply hgrid k z
    · exact (phaseGridBounds k.1.castSucc).1.trans ht0
    · have ht1R : z.1.val ≤ (phaseGrid k.1.succ).val := ht1
      have h := ht1R.trans (phaseGridBounds k.1.succ).2
      simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one] using h
    · exact (phaseGridBounds k.2.castSucc).1.trans hs0
    · have hs1R : z.2.val ≤ (phaseGrid k.2.succ).val := hs1
      have h := hs1R.trans (phaseGridBounds k.2.succ).2
      simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one] using h
  let cellDomain : Fin (n+1) × Fin (n+1) → Set (Interval × Interval) :=
    fun k => {z | phaseGrid k.1.castSucc ≤ z.1 ∧ z.1 ≤ phaseGrid k.1.succ ∧
      phaseGrid k.2.castSucc ≤ z.2 ∧ z.2 ≤ phaseGrid k.2.succ}
  have hcellClosed (k : Fin (n+1) × Fin (n+1)) : IsClosed (cellDomain k) :=
    (isClosed_le (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (by fun_prop) (by fun_prop)).inter
        ((isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))))
  have hcellCover (z : Interval × Interval) : ∃ k, z ∈ cellDomain k := by
    obtain ⟨i,hi0,hi1⟩ := phaseGridCovers z.1
    obtain ⟨j,hj0,hj1⟩ := phaseGridCovers z.2
    exact ⟨(i,j),hi0,hi1,hj0,hj1⟩
  have hcellOriginalChart (k : Fin (n+1) × Fin (n+1)) (z : Interval × Interval)
      (hz : z ∈ cellDomain k) : F z ∈ chartDomain (chart k) :=
    phaseGridCellCover k z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  have phaseStep (k : Fin (n+1)) : (phaseGrid k.castSucc).val < (phaseGrid k.succ).val :=
    phaseGridStrict (by change k.val < k.val+1; omega)
  let localCoordinate : Fin (n+1) → C(Interval,Interval) := fun k =>
    ⟨fun t => ⟨max 0 (min 1 ((t.val-(phaseGrid k.castSucc).val)/
        ((phaseGrid k.succ).val-(phaseGrid k.castSucc).val))),
      ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩⟩,by fun_prop⟩
  have localCoordinateOnCell (k : Fin (n+1)) (t : Interval)
      (ht0 : phaseGrid k.castSucc ≤ t) (ht1 : t ≤ phaseGrid k.succ) :
      (localCoordinate k t).val = (t.val-(phaseGrid k.castSucc).val)/
        ((phaseGrid k.succ).val-(phaseGrid k.castSucc).val) := by
    have hgap : 0 < (phaseGrid k.succ).val-(phaseGrid k.castSucc).val := sub_pos.mpr (phaseStep k)
    have ht0R : (phaseGrid k.castSucc).val ≤ t.val := ht0
    have ht1R : t.val ≤ (phaseGrid k.succ).val := ht1
    have h0 : 0 ≤ (t.val-(phaseGrid k.castSucc).val)/
        ((phaseGrid k.succ).val-(phaseGrid k.castSucc).val) :=
      div_nonneg (sub_nonneg.mpr ht0R) hgap.le
    have h1 : (t.val-(phaseGrid k.castSucc).val)/
        ((phaseGrid k.succ).val-(phaseGrid k.castSucc).val) ≤ 1 :=
      (div_le_one hgap).mpr (by linarith)
    exact (congrArg (max 0) (min_eq_right h1)).trans (max_eq_right h0)
  have localCoordinateLeft (k : Fin (n+1)) : localCoordinate k (phaseGrid k.castSucc) = 0 := by
    apply Subtype.ext
    simp [localCoordinate]
  have localCoordinateRight (k : Fin (n+1)) : localCoordinate k (phaseGrid k.succ) = 1 := by
    apply Subtype.ext
    have hgap : (phaseGrid k.succ).val-(phaseGrid k.castSucc).val ≠ 0 :=
      ne_of_gt (sub_pos.mpr (phaseStep k))
    simp [localCoordinate,hgap]
  let cellCoordinates : Fin (n+1) × Fin (n+1) → C(Interval × Interval,Interval × Interval) :=
    fun k => ⟨fun z => (localCoordinate k.1 z.1,localCoordinate k.2 z.2),
      ((localCoordinate k.1).continuous.comp continuous_fst).prodMk
        ((localCoordinate k.2).continuous.comp continuous_snd)⟩
  have phaseGridOriginalEndpoints (i : Fin (n+2)) :
      (intervalCurveLoopFrom a.val z₀) (phaseGrid i) ∉ b.val.image ∧
      (intervalCurveLoopFrom endCurve z₀) (phaseGrid i) ∉ b.val.image := by
    by_cases h0 : i.val = 0
    · have hi : phaseGrid i = 0 := by simp only [phaseGrid,dif_pos h0]
      rw [hi]
      simpa [intervalCurveLoopFrom,intervalCircleParameterFrom,intervalCircleParameter]
        using And.intro hzStart.1 hendStart
    · by_cases h1 : i.val = n+1
      · have hi : phaseGrid i = 1 := by simp only [phaseGrid,dif_neg h0,dif_pos h1]
        rw [hi]
        simpa [intervalCurveLoopFrom,intervalCircleParameterFrom,intervalCircleParameter]
          using And.intro hzStart.1 hendStart
      · simpa only [phaseGrid,dif_neg h0,dif_neg h1] using
          phasePointEndpoints ⟨i.val-1,by omega⟩
  have Fzero (u : Interval) : F (0,u) = intervalCurveLoopFrom a.val z₀ u := by
    change H.map (0,a.val.map (z₀ * Circle.exp (2*Real.pi*u.val))) = _
    change H.map (0,a.val.map (z₀ * Circle.exp (2*Real.pi*u.val))) =
      a.val.map (z₀ * Circle.exp (2*Real.pi*u.val))
    rw [show (0 : Interval) = ⟨0,by norm_num⟩ from Subtype.ext (by norm_num)]
    exact H.at_zero _
  have Fone (u : Interval) : F (1,u) = intervalCurveLoopFrom endCurve z₀ u := by
    change H.finalMap (a.val.map (z₀ * Circle.exp (2*Real.pi*u.val))) = _
    rw [hfinal]
    rfl
  let gridVertex : Fin (n+2) × Fin (n+2) → Interval × Interval :=
    fun v => (phaseGrid v.1,phaseGrid v.2)
  let incident : (Fin (n+1) × Fin (n+1)) → (Fin (n+2) × Fin (n+2)) → Prop :=
    fun k v => phaseGrid k.1.castSucc ≤ phaseGrid v.1 ∧
      phaseGrid v.1 ≤ phaseGrid k.1.succ ∧
      phaseGrid k.2.castSucc ≤ phaseGrid v.2 ∧
      phaseGrid v.2 ≤ phaseGrid k.2.succ
  have originalVertexCharts (v : Fin (n+2) × Fin (n+2)) :
      ∀ k, incident k v → F (gridVertex v) ∈ chartDomain (chart k) := by
    intro k hk
    exact phaseGridCellCover k (gridVertex v) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
  have boundaryVertexOff (v : Fin (n+2) × Fin (n+2))
      (hv : v.1.val = 0 ∨ v.1.val = n+1) : F (gridVertex v) ∉ b.val.image := by
    rcases hv with h0 | h1
    · have hphase : phaseGrid v.1 = 0 := by simp only [phaseGrid,dif_pos h0]
      change F (phaseGrid v.1,phaseGrid v.2) ∉ _
      rw [hphase,Fzero]
      exact (phaseGridOriginalEndpoints v.2).1
    · have h0 : v.1.val ≠ 0 := by omega
      have hphase : phaseGrid v.1 = 1 := by simp only [phaseGrid,dif_neg h0,dif_pos h1]
      change F (phaseGrid v.1,phaseGrid v.2) ∉ _
      rw [hphase,Fone]
      exact (phaseGridOriginalEndpoints v.2).2
  have convexChartWithinOpen (U : Set S) (hU : IsOpen U) (p : S) (hp : p ∈ U) :
      ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), p ∈ E.source ∧
        Convex ℝ E.target ∧ E.source ⊆ U ∧
        (Disjoint E.source b.val.image ∨ ∀ x ∈ E.source,
          x ∈ b.val.image ↔ (E x).1 = 0) := by
    let L := convexChart p
    have hpL : p ∈ L.source := hconvexPoint p
    let W := L.target ∩ L.symm ⁻¹' U
    have hW : IsOpen W := L.isOpen_inter_preimage_symm hU
    have hpW : L p ∈ W := ⟨L.map_source hpL,by change L.symm (L p) ∈ U; rwa [L.left_inv hpL]⟩
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW (L p) hpW
    let E := (L.symm.restrOpen (Metric.ball (L p) r) Metric.isOpen_ball).symm
    have hsource : E.source = L.source ∩ L ⁻¹' Metric.ball (L p) r := rfl
    have htarget : E.target = Metric.ball (L p) r := by
      change L.target ∩ Metric.ball (L p) r = Metric.ball (L p) r
      exact Set.inter_eq_right.mpr (fun x hx => (hball hx).1)
    refine ⟨E,hsource.symm ▸ ⟨hpL,Metric.mem_ball_self hr⟩,?_,?_,?_⟩
    · rw [htarget]
      exact convex_ball _ _
    · intro x hx
      have hxL := hsource ▸ hx
      have hxu := (hball hxL.2).2
      change L.symm (L x) ∈ U at hxu
      rwa [L.left_inv hxL.1] at hxu
    · rcases hconvexAxis p with hd | ha
      · left
        apply Set.disjoint_left.mpr
        intro x hx hxb
        exact (Set.disjoint_left.mp hd) (hsource ▸ hx).1 hxb
      · right
        intro x hx
        change x ∈ b.val.image ↔ (L x).1 = 0
        exact ha x (hsource ▸ hx).1
  -- Choose jointly by ORIGINAL surface value. In particular, the two copies
  -- of each periodic-seam vertex get the same perturbed value, and the choice
  -- remains in chart neighborhoods from BOTH copies of that vertex.
  have vertexByOriginalValue (p : S) :
      ∃ x : S, x ∉ b.val.image ∧
        (∀ v k, F (gridVertex v) = p → incident k v → x ∈ chartDomain (chart k)) ∧
        ((∃ v, (v.1.val = 0 ∨ v.1.val = n+1) ∧ F (gridVertex v) = p) → x = p) ∧
        ∃ γ : Path p x, ∀ v k, F (gridVertex v) = p → incident k v →
          ∀ t, γ t ∈ chartDomain (chart k) := by
    by_cases hp : ∃ v, (v.1.val = 0 ∨ v.1.val = n+1) ∧ F (gridVertex v) = p
    · obtain ⟨v,hv,he⟩ := hp
      refine ⟨p,he ▸ boundaryVertexOff v hv,?_,fun _ => rfl,Path.refl p,?_⟩
      · intro w k hw hk
        exact hw ▸ originalVertexCharts w k hk
      · intro w k hw hk t
        exact hw ▸ originalVertexCharts w k hk
    · let I := {w : (Fin (n+2) × Fin (n+2)) × (Fin (n+1) × Fin (n+1)) //
        F (gridVertex w.1) = p ∧ incident w.2 w.1}
      let U : Set S := ⋂ w : I, chartDomain (chart w.val.2)
      have hU : IsOpen U := isOpen_iInter_of_finite (fun w => hDomainOpen (chart w.val.2))
      have hpU : p ∈ U := Set.mem_iInter.mpr (fun w =>
        Eq.mp (congrArg (fun x => x ∈ chartDomain (chart w.val.2)) w.property.1)
          (originalVertexCharts w.val.1 w.val.2 w.property.2))
      obtain ⟨E,hpE,hconvex,hsub,haxisE⟩ := convexChartWithinOpen U hU p hpU
      obtain ⟨x,hxE,hxb⟩ := offComparisonInOpen E.source E.open_source p hpE
      have hpath : IsPathConnected E.source := by
        rw [← E.symm_image_target_eq_source]
        exact (hconvex.isPathConnected ⟨E p,E.map_source hpE⟩).image' E.continuousOn_symm
      obtain ⟨γ,hγ⟩ := hpath.joinedIn p hpE x hxE
      refine ⟨x,hxb,?_,fun h => False.elim (hp h),γ,?_⟩
      · intro v k he hk
        exact (Set.mem_iInter.mp (hsub hxE)) ⟨(v,k),he,hk⟩
      · intro v k he hk t
        exact (Set.mem_iInter.mp (hsub (hγ t))) ⟨(v,k),he,hk⟩
  choose vertexValue hvalueOff hvalueCharts hvalueBoundary hvalueConnector using vertexByOriginalValue
  let perturbedVertex : Fin (n+2) × Fin (n+2) → S := fun v => vertexValue (F (gridVertex v))
  have hvertexOff (v) : perturbedVertex v ∉ b.val.image := hvalueOff _
  have hvertexCharts (v) (k) (hk : incident k v) :
      perturbedVertex v ∈ chartDomain (chart k) := hvalueCharts _ v k rfl hk
  have hvertexBoundary (v) (hv : v.1.val = 0 ∨ v.1.val = n+1) :
      perturbedVertex v = F (gridVertex v) := hvalueBoundary _ ⟨v,hv,rfl⟩
  have hvertexConnector (v : Fin (n+2) × Fin (n+2)) :
      ∃ γ : Path (F (gridVertex v)) (perturbedVertex v),
        ∀ k, incident k v → ∀ t, γ t ∈ chartDomain (chart k) := by
    obtain ⟨γ,hγ⟩ := hvalueConnector (F (gridVertex v))
    exact ⟨γ,fun k hk t => hγ v k rfl hk t⟩
  have Fseam (t : Interval) : F (t,0) = F (t,1) := by
    simp [F]
  have hvertexSeam (i : Fin (n+2)) :
      perturbedVertex (i,0) = perturbedVertex (i,Fin.last (n+1)) := by
    have h0 : phaseGrid 0 = 0 := by simp [phaseGrid]
    have h1 : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
    change vertexValue (F (phaseGrid i,phaseGrid 0)) =
      vertexValue (F (phaseGrid i,phaseGrid (Fin.last (n+1))))
    rw [h0,h1,Fseam]
  -- The actual vertex system now has both incident-chart compatibility and
  -- exact periodic-seam equality. Shared edge homotopies and component topology
  -- remain explicit obligations.
  have finitePathTrans {Y : Type} [TopologicalSpace Y]
      (B : Set Y) {x y z : Y} (p : Path x y) (q : Path y z)
      (hp : (p ⁻¹' B).Finite) (hq : (q ⁻¹' B).Finite) :
      ((p.trans q) ⁻¹' B).Finite := by
    let E0 : Set ℝ := (fun t : Interval => t.val) '' (p ⁻¹' B)
    let E1 : Set ℝ := (fun t : Interval => t.val) '' (q ⁻¹' B)
    let f0 : Interval → ℝ := fun t => 2*t.val
    let f1 : Interval → ℝ := fun t => 2*t.val-1
    have hi0 : Function.Injective f0 := by
      intro t u h
      apply Subtype.ext
      change 2*t.val = 2*u.val at h
      linarith
    have hi1 : Function.Injective f1 := by
      intro t u h
      apply Subtype.ext
      change 2*t.val-1 = 2*u.val-1 at h
      linarith
    have h0 : (f0 ⁻¹' E0).Finite := (hp.image _).preimage hi0.injOn
    have h1 : (f1 ⁻¹' E1).Finite := (hq.image _).preimage hi1.injOn
    apply (h0.union h1).subset
    intro t ht
    change (p.trans q) t ∈ B at ht
    by_cases h : t.val ≤ 1/2
    · left
      simp only [Path.trans_apply,dif_pos h] at ht
      exact ⟨⟨2*t.val,by constructor <;> linarith [t.property.1]⟩,ht,rfl⟩
    · right
      simp only [Path.trans_apply,dif_neg h] at ht
      exact ⟨⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩,ht,rfl⟩
  have embeddedPathTrans {Y : Type} [TopologicalSpace Y] [T2Space Y]
      {x y z : Y} (p : Path x y) (q : Path y z)
      (hp : Topology.IsEmbedding p) (hq : Topology.IsEmbedding q)
      (hinter : Set.range p ∩ Set.range q = {y}) :
      Topology.IsEmbedding (p.trans q) := by
    apply ((p.trans q).continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    simp only [Path.trans_apply] at he
    split_ifs at he with ht hu
    · have hv := congrArg Subtype.val (hp.injective he)
      apply Subtype.ext
      change 2*t.val = 2*u.val at hv
      linarith
    · let t0 : Interval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
      let u1 : Interval := ⟨2*u.val-1,by constructor <;> linarith [u.property.2]⟩
      change p t0 = q u1 at he
      have hpy : p t0 = y := by
        have hm : p t0 ∈ Set.range p ∩ Set.range q := ⟨⟨t0,rfl⟩,⟨u1,he.symm⟩⟩
        rw [hinter] at hm
        exact Set.mem_singleton_iff.mp hm
      have hqu : q u1 = y := he.symm.trans hpy
      have ht0 := congrArg Subtype.val (hp.injective (hpy.trans p.target.symm))
      have hu1 := congrArg Subtype.val (hq.injective (hqu.trans q.source.symm))
      apply Subtype.ext
      change 2*t.val = 1 at ht0
      change 2*u.val-1 = 0 at hu1
      linarith
    · let t1 : Interval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
      let u0 : Interval := ⟨2*u.val,by constructor <;> linarith [u.property.1]⟩
      change q t1 = p u0 at he
      have hpu : p u0 = y := by
        have hm : p u0 ∈ Set.range p ∩ Set.range q := ⟨⟨u0,rfl⟩,⟨t1,he⟩⟩
        rw [hinter] at hm
        exact Set.mem_singleton_iff.mp hm
      have hqt : q t1 = y := he.trans hpu
      have ht1 := congrArg Subtype.val (hq.injective (hqt.trans q.source.symm))
      have hu0 := congrArg Subtype.val (hp.injective (hpu.trans p.target.symm))
      apply Subtype.ext
      change 2*t.val-1 = 0 at ht1
      change 2*u.val = 1 at hu0
      linarith
    · have hv := congrArg Subtype.val (hq.injective he)
      apply Subtype.ext
      change 2*t.val-1 = 2*u.val-1 at hv
      linarith
  have convexSegmentFinite (V : Set (ℝ × ℝ)) (hV : Convex ℝ V) (x y : V)
      (hend : x.val.1 ≠ 0 ∨ y.val.1 ≠ 0) :
      ∃ p : Path x y, ({t : Interval | (p t).val.1 = 0}).Finite := by
    let p : Path x y := {
      toFun := fun t => ⟨(1-t.val) • x.val+t.val • y.val,
        hV x.property y.property (by linarith [t.property.2]) t.property.1 (by ring)⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
    refine ⟨p,?_⟩
    by_cases heq : x.val.1 = y.val.1
    · apply Set.Finite.subset Set.finite_empty
      intro t ht
      change (1-t.val)*x.val.1+t.val*y.val.1 = 0 at ht
      rw [← heq] at ht
      have hz : x.val.1 = 0 := by nlinarith only [ht]
      rcases hend with hx | hy
      · exact False.elim (hx hz)
      · exact False.elim (hy (heq ▸ hz))
    · apply Set.Subsingleton.finite
      intro t ht u hu
      change (1-t.val)*x.val.1+t.val*y.val.1 = 0 at ht
      change (1-u.val)*x.val.1+u.val*y.val.1 = 0 at hu
      apply Subtype.ext
      have hz : (t.val-u.val)*(y.val.1-x.val.1) = 0 := by nlinarith only [ht,hu]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact sub_eq_zero.mp hz
      · exact False.elim (heq (sub_eq_zero.mp hz).symm)
  have localChartRegularization (E : OpenPartialHomeomorph S (ℝ × ℝ))
      (hV : Convex ℝ E.target)
      (haxis : Disjoint E.source b.val.image ∨
        ∀ x ∈ E.source, x ∈ b.val.image ↔ (E x).1 = 0)
      {x y : S} (g : Path x y) (hg : Set.range g ⊆ E.source) :
      ∃ p : Path x y, Set.range p ⊆ E.source ∧ p.Homotopic g ∧
        (p ⁻¹' b.val.image).Finite := by
    have hx : x ∈ E.source := g.source ▸ hg ⟨0,rfl⟩
    have hy : y ∈ E.source := g.target ▸ hg ⟨1,rfl⟩
    rcases haxis with hdis | haxis
    · refine ⟨g,hg,Path.Homotopic.refl g,?_⟩
      apply Set.Finite.subset Set.finite_empty
      intro t ht
      exact False.elim ((Set.disjoint_left.mp hdis) (hg ⟨t,rfl⟩) ht)
    · obtain ⟨w,hw,hwB⟩ := offComparisonInOpen E.source E.open_source x hx
      let xs : E.source := ⟨x,hx⟩
      let ys : E.source := ⟨y,hy⟩
      let ws : E.source := ⟨w,hw⟩
      let H := E.toHomeomorphSourceTarget
      have hwcoord : (H ws).val.1 ≠ 0 := by
        intro hz
        apply hwB
        exact (haxis w hw).mpr hz
      obtain ⟨c0,hc0⟩ := convexSegmentFinite E.target hV (H xs) (H ws) (Or.inr hwcoord)
      obtain ⟨c1,hc1⟩ := convexSegmentFinite E.target hV (H ws) (H ys) (Or.inl hwcoord)
      let c := c0.trans c1
      have hc : (c ⁻¹' {z : E.target | z.val.1 = 0}).Finite :=
        finitePathTrans {z : E.target | z.val.1 = 0} c0 c1 hc0 hc1
      let r : Path xs ys := ((c.map H.symm.continuous).cast
        (H.symm_apply_apply xs).symm (H.symm_apply_apply ys).symm)
      let p : Path x y := r.map continuous_subtype_val
      have hprange : Set.range p ⊆ E.source := by
        rintro z ⟨t,rfl⟩
        exact (r t).property
      let gs : Path xs ys := {
        toFun := fun t => ⟨g t,hg ⟨t,rfl⟩⟩
        continuous_toFun := g.continuous.subtype_mk _
        source' := by apply Subtype.ext; exact g.source
        target' := by apply Subtype.ext; exact g.target }
      have hgs : gs.map continuous_subtype_val = g := by ext t; rfl
      letI : ContractibleSpace E.target := hV.contractibleSpace ⟨H xs,(H xs).property⟩
      letI : ContractibleSpace E.source := H.contractibleSpace_iff.mpr inferInstance
      have hhom : p.Homotopic g := by
        rw [← hgs]
        exact (SimplyConnectedSpace.paths_homotopic r gs).map ⟨Subtype.val,continuous_subtype_val⟩
      refine ⟨p,hprange,hhom,hc.subset ?_⟩
      intro t ht
      change (c t).val.1 = 0
      have hz := (haxis (p t) (hprange ⟨t,rfl⟩)).mp ht
      have heq : E (p t) = (c t).val := by
        change (H (H.symm (c t))).val = (c t).val
        rw [H.apply_symm_apply]
      rwa [heq] at hz
  -- Regularize a WHOLE shared edge inside every incident chart neighborhood.
  -- Local subpaths are replaced within adapted convex charts subordinate to U;
  -- the concatenation is homotopic to the original edge relative endpoints.
  have regularizePathInOpen (U : Set S) (hU : IsOpen U)
      {x y : S} (g : Path x y) (hg : Set.range g ⊆ U)
      (hxB : x ∉ b.val.image) :
      ∃ p : Path x y, Set.range p ⊆ U ∧ p.Homotopic g ∧
        (p ⁻¹' b.val.image).Finite := by
    have hpoint (t : Interval) :
        ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), g t ∈ E.source ∧
          Convex ℝ E.target ∧ E.source ⊆ U ∧
          (Disjoint E.source b.val.image ∨
            ∀ z ∈ E.source, z ∈ b.val.image ↔ (E z).1 = 0) :=
      convexChartWithinOpen U hU (g t) (hg ⟨t,rfl⟩)
    choose atlas hatlasPoint hatlasConvex hatlasU hatlasAxis using hpoint
    let W : Interval → Set Interval := fun t => g ⁻¹' (atlas t).source
    have hW : ∀ t, IsOpen (W t) := fun t => (atlas t).open_source.preimage g.continuous
    have hcover : (Set.univ : Set Interval) ⊆ ⋃ t, W t := by
      intro t _
      exact Set.mem_iUnion.mpr ⟨t,hatlasPoint t⟩
    obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hcover
    obtain ⟨m,hm,hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    let mesh : ℕ → Interval := fun k => ⟨min ((k : ℝ)/m) 1,
      ⟨le_min (by positivity) (by norm_num),min_le_right _ _⟩⟩
    have meshValue (k : ℕ) (hk : k ≤ m) : (mesh k).val = (k : ℝ)/m := by
      apply min_eq_left
      apply (div_le_one hmR).mpr
      exact_mod_cast hk
    have hmesh0 : mesh 0 = 0 := by apply Subtype.ext; simp [mesh]
    have hmesh1 : mesh m = 1 := by apply Subtype.ext; rw [meshValue m le_rfl,div_self hmR.ne']; rfl
    have segment (k : ℕ) (hk : k < m) :
        ∃ p : Path (g (mesh k)) (g (mesh (k+1))), Set.range p ⊆ U ∧
          (p ⁻¹' b.val.image).Finite ∧
          ∃ d : Path (mesh k) (mesh (k+1)), p.Homotopic (d.map g.continuous) := by
      obtain ⟨t,ht⟩ := hball (mesh k) (Set.mem_univ _)
      let d : Path (mesh k) (mesh (k+1)) := {
        toFun := fun r => ⟨(1-r.val)*(mesh k).val+r.val*(mesh (k+1)).val,by
          constructor
          · exact add_nonneg (mul_nonneg (sub_nonneg.mpr r.property.2) (mesh k).property.1)
              (mul_nonneg r.property.1 (mesh (k+1)).property.1)
          · nlinarith [r.property.1,r.property.2,(mesh k).property.2,(mesh (k+1)).property.2]⟩
        continuous_toFun := by fun_prop
        source' := by apply Subtype.ext; simp
        target' := by apply Subtype.ext; simp }
      have hd : Set.range (d.map g.continuous) ⊆ (atlas t).source := by
        rintro z ⟨r,rfl⟩
        apply ht
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_lt]
        change -δ < (1-r.val)*(mesh k).val+r.val*(mesh (k+1)).val-(mesh k).val ∧
          (1-r.val)*(mesh k).val+r.val*(mesh (k+1)).val-(mesh k).val < δ
        rw [meshValue k hk.le,meshValue (k+1) (by omega)]
        have hstep : ((k+1 : ℕ) : ℝ)/m = (k : ℝ)/m+(m : ℝ)⁻¹ := by
          rw [Nat.cast_add,Nat.cast_one,add_div,one_div]
        rw [hstep]
        have hmeshpos : (0 : ℝ) < (m : ℝ)⁻¹ := inv_pos.mpr hmR
        constructor <;> nlinarith [r.property.1,r.property.2]
      obtain ⟨p,hp,hhom,hfin⟩ := localChartRegularization (atlas t) (hatlasConvex t)
        (hatlasAxis t) (d.map g.continuous) hd
      exact ⟨p,hp.trans (hatlasU t),hfin,d,hhom⟩
    have chain (j : ℕ) (hj : j ≤ m) :
        ∃ p : Path (g (mesh 0)) (g (mesh j)), Set.range p ⊆ U ∧
          (p ⁻¹' b.val.image).Finite ∧
          ∃ d : Path (mesh 0) (mesh j), p.Homotopic (d.map g.continuous) := by
      induction j with
      | zero =>
        refine ⟨Path.refl (g (mesh 0)),?_,?_,Path.refl (mesh 0),?_⟩
        · rintro z ⟨t,rfl⟩
          exact hg ⟨mesh 0,rfl⟩
        · apply Set.Finite.subset Set.finite_empty
          intro t ht
          apply hxB
          change g (mesh 0) ∈ b.val.image at ht
          rwa [hmesh0,g.source] at ht
        · exact Path.Homotopic.refl _
      | succ j ih =>
        obtain ⟨p,hp,hpfin,d,hpd⟩ := ih (by omega)
        obtain ⟨q,hq,hqfin,e,hqe⟩ := segment j (by omega)
        refine ⟨p.trans q,?_,finitePathTrans b.val.image p q hpfin hqfin,d.trans e,?_⟩
        · rw [Path.trans_range]
          exact Set.union_subset hp hq
        · rw [Path.map_trans]
          exact hpd.hcomp hqe
    obtain ⟨p,hp,hpfin,d,hpd⟩ := chain m le_rfl
    let idpath : Path (0 : Interval) 1 := {
      toFun := id
      continuous_toFun := continuous_id
      source' := rfl
      target' := rfl }
    let d0 : Path (mesh 0) (mesh m) := idpath.cast hmesh0 hmesh1
    letI : ContractibleSpace Interval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    have hdom : d.Homotopic d0 := SimplyConnectedSpace.paths_homotopic d d0
    have hstart : x = g (mesh 0) := ((congrArg g hmesh0).trans g.source).symm
    have hfinish : y = g (mesh m) := ((congrArg g hmesh1).trans g.target).symm
    let p0 : Path x y := p.cast hstart hfinish
    have heq : (d0.map g.continuous).cast hstart hfinish = g := by ext t; rfl
    have hhom : p0.Homotopic g := by
      rw [← heq]
      exact (hpd.trans (hdom.map g.toContinuousMap)).pathCast hstart hfinish
    exact ⟨p0,hp,hhom,hpfin⟩
  have sharedEdgeCandidate (v w : Fin (n+2) × Fin (n+2)) :
      ∃ (left : Path (F (gridVertex v)) (perturbedVertex v))
        (right : Path (F (gridVertex w)) (perturbedVertex w))
        (original : Path (F (gridVertex v)) (F (gridVertex w)))
        (p : Path (perturbedVertex v) (perturbedVertex w)),
        (∀ k, incident k v ∧ incident k w → Set.range p ⊆ chartDomain (chart k)) ∧
        (p ⁻¹' b.val.image).Finite ∧
        p.Homotopic ((left.symm.trans original).trans right) := by
    obtain ⟨left,hleft⟩ := hvertexConnector v
    obtain ⟨right,hright⟩ := hvertexConnector w
    let d : Path (gridVertex v) (gridVertex w) := {
      toFun := fun t =>
        (⟨(1-t.val)*(phaseGrid v.1).val+t.val*(phaseGrid w.1).val,by
          constructor
          · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (phaseGrid v.1).property.1)
              (mul_nonneg t.property.1 (phaseGrid w.1).property.1)
          · nlinarith [t.property.1,t.property.2,(phaseGrid v.1).property.2,(phaseGrid w.1).property.2]⟩,
         ⟨(1-t.val)*(phaseGrid v.2).val+t.val*(phaseGrid w.2).val,by
          constructor
          · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (phaseGrid v.2).property.1)
              (mul_nonneg t.property.1 (phaseGrid w.2).property.1)
          · nlinarith [t.property.1,t.property.2,(phaseGrid v.2).property.2,(phaseGrid w.2).property.2]⟩)
      continuous_toFun := by fun_prop
      source' := by apply Prod.ext <;> apply Subtype.ext <;> simp [gridVertex]
      target' := by apply Prod.ext <;> apply Subtype.ext <;> simp [gridVertex] }
    let original := d.map F.continuous
    let I := {k : Fin (n+1) × Fin (n+1) // incident k v ∧ incident k w}
    let U : Set S := ⋂ k : I, chartDomain (chart k.val)
    have hU : IsOpen U := isOpen_iInter_of_finite (fun k => hDomainOpen (chart k.val))
    have hleftU : Set.range left ⊆ U := by
      rintro z ⟨t,rfl⟩
      exact Set.mem_iInter.mpr (fun k => hleft k.val k.property.1 t)
    have hrightU : Set.range right ⊆ U := by
      rintro z ⟨t,rfl⟩
      exact Set.mem_iInter.mpr (fun k => hright k.val k.property.2 t)
    have horiginalU : Set.range original ⊆ U := by
      rintro z ⟨t,rfl⟩
      apply Set.mem_iInter.mpr
      intro k
      apply phaseGridCellCover k.val (d t)
      · have h0 : (phaseGrid k.val.1.castSucc).val ≤ (phaseGrid v.1).val := k.property.1.1
        have h1 : (phaseGrid k.val.1.castSucc).val ≤ (phaseGrid w.1).val := k.property.2.1
        change (phaseGrid k.val.1.castSucc).val ≤
          (1-t.val)*(phaseGrid v.1).val+t.val*(phaseGrid w.1).val
        nlinarith [t.property.1,t.property.2]
      · have h0 : (phaseGrid v.1).val ≤ (phaseGrid k.val.1.succ).val := k.property.1.2.1
        have h1 : (phaseGrid w.1).val ≤ (phaseGrid k.val.1.succ).val := k.property.2.2.1
        change (1-t.val)*(phaseGrid v.1).val+t.val*(phaseGrid w.1).val ≤ (phaseGrid k.val.1.succ).val
        nlinarith [t.property.1,t.property.2]
      · have h0 : (phaseGrid k.val.2.castSucc).val ≤ (phaseGrid v.2).val := k.property.1.2.2.1
        have h1 : (phaseGrid k.val.2.castSucc).val ≤ (phaseGrid w.2).val := k.property.2.2.2.1
        change (phaseGrid k.val.2.castSucc).val ≤
          (1-t.val)*(phaseGrid v.2).val+t.val*(phaseGrid w.2).val
        nlinarith [t.property.1,t.property.2]
      · have h0 : (phaseGrid v.2).val ≤ (phaseGrid k.val.2.succ).val := k.property.1.2.2.2
        have h1 : (phaseGrid w.2).val ≤ (phaseGrid k.val.2.succ).val := k.property.2.2.2.2
        change (1-t.val)*(phaseGrid v.2).val+t.val*(phaseGrid w.2).val ≤ (phaseGrid k.val.2.succ).val
        nlinarith [t.property.1,t.property.2]
    let prepared := (left.symm.trans original).trans right
    have hpreparedU : Set.range prepared ⊆ U := by
      rw [Path.trans_range,Path.trans_range,Path.symm_range]
      exact Set.union_subset (Set.union_subset hleftU horiginalU) hrightU
    obtain ⟨p,hp,hhom,hfin⟩ := regularizePathInOpen U hU prepared hpreparedU (hvertexOff v)
    refine ⟨left,right,original,p,?_,hfin,hhom⟩
    intro k hk z hz
    exact (Set.mem_iInter.mp (hp hz)) ⟨k,hk⟩
  -- The periodic seam is chosen once, with support in BOTH copies of its
  -- incident cell charts. It is not obtained by two unrelated edge choices.
  have sharedSeamEdgeCandidate (i : Fin (n+1)) :
      ∃ p : Path (perturbedVertex (i.castSucc,0)) (perturbedVertex (i.succ,0)),
        (∀ t, p t ∈ chartDomain (chart (i,0)) ∧
          p t ∈ chartDomain (chart (i,Fin.last n))) ∧
        (p ⁻¹' b.val.image).Finite := by
    let v : Fin (n+2) × Fin (n+2) := (i.castSucc,0)
    let w : Fin (n+2) × Fin (n+2) := (i.succ,0)
    let v' : Fin (n+2) × Fin (n+2) := (i.castSucc,Fin.last (n+1))
    let w' : Fin (n+2) × Fin (n+2) := (i.succ,Fin.last (n+1))
    have hv : incident (i,0) v := by
      change phaseGrid i.castSucc ≤ phaseGrid i.castSucc ∧
        phaseGrid i.castSucc ≤ phaseGrid i.succ ∧
        phaseGrid 0 ≤ phaseGrid 0 ∧ phaseGrid 0 ≤ phaseGrid (Fin.succ 0)
      exact ⟨le_rfl,(phaseStep i).le,le_rfl,(phaseGridStrict (by change (0 : ℕ) < 0+1; omega)).le⟩
    have hw : incident (i,0) w := by
      change phaseGrid i.castSucc ≤ phaseGrid i.succ ∧
        phaseGrid i.succ ≤ phaseGrid i.succ ∧
        phaseGrid 0 ≤ phaseGrid 0 ∧ phaseGrid 0 ≤ phaseGrid (Fin.succ 0)
      exact ⟨(phaseStep i).le,le_rfl,le_rfl,(phaseGridStrict (by change (0 : ℕ) < 0+1; omega)).le⟩
    have hv' : incident (i,Fin.last n) v' := by
      change phaseGrid i.castSucc ≤ phaseGrid i.castSucc ∧
        phaseGrid i.castSucc ≤ phaseGrid i.succ ∧
        phaseGrid (Fin.last n).castSucc ≤ phaseGrid (Fin.last (n+1)) ∧
        phaseGrid (Fin.last (n+1)) ≤ phaseGrid (Fin.last n).succ
      have he : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
      exact ⟨le_rfl,(phaseStep i).le,he ▸ (phaseStep (Fin.last n)).le,by rw [he]⟩
    have hw' : incident (i,Fin.last n) w' := by
      change phaseGrid i.castSucc ≤ phaseGrid i.succ ∧
        phaseGrid i.succ ≤ phaseGrid i.succ ∧
        phaseGrid (Fin.last n).castSucc ≤ phaseGrid (Fin.last (n+1)) ∧
        phaseGrid (Fin.last (n+1)) ≤ phaseGrid (Fin.last n).succ
      have he : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
      exact ⟨(phaseStep i).le,le_rfl,he ▸ (phaseStep (Fin.last n)).le,by rw [he]⟩
    have hseam (j : Fin (n+2)) :
        F (gridVertex (j,Fin.last (n+1))) = F (gridVertex (j,0)) := by
      change F (phaseGrid j,phaseGrid (Fin.last (n+1))) = F (phaseGrid j,phaseGrid 0)
      have h0 : phaseGrid 0 = 0 := by simp [phaseGrid]
      have h1 : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
      rw [h0,h1]; exact (Fseam _).symm
    obtain ⟨l,hl⟩ := hvalueConnector (F (gridVertex v))
    obtain ⟨r,hr⟩ := hvalueConnector (F (gridVertex w))
    let U := chartDomain (chart (i,0)) ∩ chartDomain (chart (i,Fin.last n))
    have hU : IsOpen U := (hDomainOpen _).inter (hDomainOpen _)
    have hlU : Set.range l ⊆ U := by
      rintro x ⟨t,rfl⟩
      exact ⟨hl v (i,0) rfl hv t,hl v' (i,Fin.last n) (hseam _) hv' t⟩
    have hrU : Set.range r ⊆ U := by
      rintro x ⟨t,rfl⟩
      exact ⟨hr w (i,0) rfl hw t,hr w' (i,Fin.last n) (hseam _) hw' t⟩
    let d : Path (gridVertex v) (gridVertex w) := {
      toFun := fun t =>
        (⟨(1-t.val)*(phaseGrid i.castSucc).val+t.val*(phaseGrid i.succ).val,by
          constructor
          · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2)
              (phaseGrid i.castSucc).property.1) (mul_nonneg t.property.1
              (phaseGrid i.succ).property.1)
          · nlinarith [(phaseGrid i.castSucc).property.1,(phaseGrid i.castSucc).property.2,
              (phaseGrid i.succ).property.1,(phaseGrid i.succ).property.2,t.property.1,t.property.2]⟩,0)
      continuous_toFun := by fun_prop
      source' := by apply Prod.ext <;> apply Subtype.ext <;> simp [gridVertex,v,phaseGrid]
      target' := by apply Prod.ext <;> apply Subtype.ext <;> simp [gridVertex,w,phaseGrid] }
    let original := d.map F.continuous
    have horiginalU : Set.range original ⊆ U := by
      rintro x ⟨t,rfl⟩
      have h0 : phaseGrid i.castSucc ≤ (d t).1 := by
        change (phaseGrid i.castSucc).val ≤
          (1-t.val)*(phaseGrid i.castSucc).val+t.val*(phaseGrid i.succ).val
        nlinarith [(phaseStep i).le,t.property.1]
      have h1 : (d t).1 ≤ phaseGrid i.succ := by
        change (1-t.val)*(phaseGrid i.castSucc).val+t.val*(phaseGrid i.succ).val ≤
          (phaseGrid i.succ).val
        nlinarith [(phaseStep i).le,t.property.2]
      constructor
      · apply phaseGridCellCover (i,0) (d t) h0 h1
        · change phaseGrid 0 ≤ (0 : Interval); simp [phaseGrid]
        · exact (phaseGrid (Fin.succ 0)).property.1
      · change F ((d t).1,0) ∈ chartDomain (chart (i,Fin.last n))
        rw [Fseam]
        apply phaseGridCellCover (i,Fin.last n) ((d t).1,1) h0 h1
        · exact (phaseGrid (Fin.last n).castSucc).property.2
        · have he : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
          simp [he,phaseGrid]
    let prepared := (l.symm.trans original).trans r
    have hpU : Set.range prepared ⊆ U := by
      rw [Path.trans_range,Path.trans_range,Path.symm_range]
      exact Set.union_subset (Set.union_subset hlU horiginalU) hrU
    obtain ⟨p,hp,hhom,hfin⟩ := regularizePathInOpen U hU prepared hpU (hvertexOff v)
    exact ⟨p,fun t => hp ⟨t,rfl⟩,hfin⟩
  have convexEdgeReplacement (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
      (g : C(Interval,V)) (h0 : (g 0).val.1 ≠ 0) (h1 : (g 1).val.1 ≠ 0) :
      ∃ p : C(Interval,V), g.HomotopicRel p {0,1} ∧
        ({t : Interval | (p t).val.1 = 0}).Finite := by
    let p : C(Interval,V) := ⟨fun t => ⟨(1-t.val) • (g 0).val+t.val • (g 1).val,
      hV (g 0).property (g 1).property (by linarith [t.property.2]) t.property.1 (by ring)⟩,
      by fun_prop⟩
    have hp0 : p 0 = g 0 := by apply Subtype.ext; simp [p]
    have hp1 : p 1 = g 1 := by apply Subtype.ext; simp [p]
    let G : g.HomotopyRel p {0,1} := {
      toHomotopy := {
        toFun := fun z => ⟨(1-z.1.val) • (g z.2).val+z.1.val • (p z.2).val,
          hV (g z.2).property (p z.2).property (by linarith [z.1.property.2])
            z.1.property.1 (by ring)⟩
        continuous_toFun := by fun_prop
        map_zero_left := by intro t; apply Subtype.ext; simp
        map_one_left := by intro t; apply Subtype.ext; simp }
      prop' := by
        intro t u hu
        rcases Set.mem_insert_iff.mp hu with hu | hu
        · subst u; apply Subtype.ext; change (1-t.val) • (g 0).val+t.val • (p 0).val = _
          rw [hp0]; ext <;> simp <;> ring
        · have hu' : u = 1 := Set.mem_singleton_iff.mp hu
          subst u; apply Subtype.ext; change (1-t.val) • (g 1).val+t.val • (p 1).val = _
          rw [hp1]; ext <;> simp <;> ring }
    refine ⟨p,⟨G⟩,?_⟩
    by_cases heq : (g 0).val.1 = (g 1).val.1
    · apply Set.Finite.subset Set.finite_empty
      intro t ht
      change (1-t.val)*(g 0).val.1+t.val*(g 1).val.1 = 0 at ht
      rw [← heq] at ht
      have hz : (g 0).val.1 = 0 := by nlinarith only [ht]
      exact False.elim (h0 hz)
    · apply Set.Subsingleton.finite
      intro t ht u hu
      change (1-t.val)*(g 0).val.1+t.val*(g 1).val.1 = 0 at ht
      change (1-u.val)*(g 0).val.1+u.val*(g 1).val.1 = 0 at hu
      apply Subtype.ext
      have hz : (t.val-u.val)*((g 1).val.1-(g 0).val.1) = 0 := by nlinarith only [ht,hu]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact sub_eq_zero.mp hz
      · exact False.elim (heq (sub_eq_zero.mp hz).symm)
  have convexConeFill (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
      (f : C(Circle,V)) (v : V) :
      ∃ (q : C(unitInterval × Circle,{z : ℂ // ‖z‖ ≤ 1}))
        (G : C({z : ℂ // ‖z‖ ≤ 1},V)), Function.Surjective q ∧
        (∀ a, (q a).val = (1-a.1.val) • (a.2 : ℂ)) ∧
        ∀ a, (G (q a)).val = (1-a.1.val) • (f a.2).val+a.1.val • v.val := by
    have hradial : ∃ q : C(unitInterval × Circle, {z : ℂ // ‖z‖ ≤ 1}),
        Function.Surjective q ∧
        (∀ a b, q a = q b → a = b ∨ a.1 = 1 ∧ b.1 = 1) ∧
        (∀ a : unitInterval × Circle, (q a : ℂ) = (1-a.1.val) • (a.2 : ℂ)) := by
      let q : C(unitInterval × Circle, {z : ℂ // ‖z‖ ≤ 1}) :=
        ⟨fun a => ⟨(1 - (a.1 : ℝ)) • (a.2 : ℂ), by
          rw [norm_smul, Circle.norm_coe a.2, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
          linarith [a.1.property.1]⟩,
          by fun_prop⟩
      have hnorm (a : unitInterval × Circle) : ‖(q a : ℂ)‖ = 1 - (a.1 : ℝ) := by
        change ‖(1 - (a.1 : ℝ)) • (a.2 : ℂ)‖ = _
        rw [norm_smul, Circle.norm_coe a.2, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
      refine ⟨q, ?_, ?_, ?_⟩
      · intro z
        by_cases hz : (z : ℂ) = 0
        · refine ⟨(1, ⟨1, by simp⟩), ?_⟩
          apply Subtype.ext
          simp [q, hz]
        · have hn : ‖(z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
          let u : Circle := ⟨‖(z : ℂ)‖⁻¹ • (z : ℂ), by
            change dist (‖(z : ℂ)‖⁻¹ • (z : ℂ)) 0 = 1
            rw [dist_zero_right]
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
            exact inv_mul_cancel₀ hn⟩
          refine ⟨(⟨1 - ‖(z : ℂ)‖, by constructor <;> linarith only [z.property, norm_nonneg (z : ℂ)]⟩, u), ?_⟩
          apply Subtype.ext
          change (1 - (1 - ‖(z : ℂ)‖)) • (‖(z : ℂ)‖⁻¹ • (z : ℂ)) = (z : ℂ)
          rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ hn, one_smul]
      · intro a b hab
        have ht : a.1 = b.1 := by
          apply Subtype.ext
          have h := congrArg (fun z : {z : ℂ // ‖z‖ ≤ 1} => ‖(z : ℂ)‖) hab
          rw [hnorm, hnorm] at h
          linarith
        by_cases ha : a.1 = 1
        · exact Or.inr ⟨ha, ht.symm.trans ha⟩
        · left
          apply Prod.ext ht
          apply Subtype.ext
          have h := congrArg (fun z : {z : ℂ // ‖z‖ ≤ 1} => (z : ℂ)) hab
          change (1 - (a.1 : ℝ)) • (a.2 : ℂ) = (1 - (b.1 : ℝ)) • (b.2 : ℂ) at h
          rw [← ht] at h
          have hn : 1 - (a.1 : ℝ) ≠ 0 := by
            intro he
            apply ha
            apply Subtype.ext
            change (a.1 : ℝ) = 1
            linarith
          exact (smul_right_injective _ hn) h
      · intro a
        rfl
    obtain ⟨q,hsurj,hfiber,hqformula⟩ := hradial
    let K : C(unitInterval × Circle,V) :=
      ⟨fun a => ⟨(1-a.1.val) • (f a.2).val+a.1.val • v.val,
        hV (f a.2).property v.property (by linarith [a.1.property.2]) a.1.property.1 (by ring)⟩,
        by fun_prop⟩
    have hrespect (a b : unitInterval × Circle) (hab : q a = q b) : K a = K b := by
      rcases hfiber a b hab with hab | ⟨ha,hb⟩
      · rw [hab]
      · apply Subtype.ext
        simp [K,ha,hb]
    let G : {z : ℂ // ‖z‖ ≤ 1} → V := fun z => K (Function.surjInv hsurj z)
    have hGq (a : unitInterval × Circle) : G (q a) = K a :=
      hrespect _ _ (Function.surjInv_eq hsurj (q a))
    have hquot := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
    have hGc : Continuous G := hquot.continuous_iff.mpr (by
      have heq : G ∘ q = K := funext hGq
      rw [heq]; exact K.continuous)
    refine ⟨q,⟨G,hGc⟩,hsurj,hqformula,?_⟩
    intro a
    exact congrArg Subtype.val (hGq a)
  have squareCoordinateBounds (z : {z : ℝ × ℝ // ‖z‖ ≤ 1}) :
      (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
    simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using z.property
  let squareCoordinates : {z : ℝ × ℝ // ‖z‖ ≤ 1} ≃ₜ Interval × Interval := {
    toFun := fun z =>
      (⟨(z.val.1+1)/2,by constructor <;> linarith [(squareCoordinateBounds z).1.1,(squareCoordinateBounds z).1.2]⟩,
       ⟨(z.val.2+1)/2,by constructor <;> linarith [(squareCoordinateBounds z).2.1,(squareCoordinateBounds z).2.2]⟩)
    invFun := fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
      simp only [Prod.norm_mk,Real.norm_eq_abs,max_le_iff,abs_le]
      constructor <;> constructor <;> linarith only [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩
    left_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> change 2*((_+1)/2)-1 = _ <;> ring
    right_inv := by intro z; apply Prod.ext <;> apply Subtype.ext <;> change ((2*_-1)+1)/2 = _ <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  -- The product norm on R² is the max norm, so this quotient cone fills an
  -- actual SQUARE cell. No unproved disk-to-square homeomorphism is assumed.
  have squareConeFill (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
      (f : C({z : ℝ × ℝ // ‖z‖ = 1},V)) (v : V) :
      ∃ (q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1},{z : ℝ × ℝ // ‖z‖ ≤ 1}))
        (G : C({z : ℝ × ℝ // ‖z‖ ≤ 1},V)), Function.Surjective q ∧
        (∀ a, (q a).val = (1-a.1.val) • (a.2 : ℝ × ℝ)) ∧
        ∀ a, (G (q a)).val = (1-a.1.val) • (f a.2).val+a.1.val • v.val := by
    have hQ : IsCompact {z : ℝ × ℝ | ‖z‖ ≤ 1} := by
      convert (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)) using 1
      ext z
      simp only [Set.mem_ofPred_eq,Set.mem_prod,Set.mem_Icc,Prod.norm_def,
        Real.norm_eq_abs,max_le_iff,abs_le]
    have hB : IsClosed {z : ℝ × ℝ | ‖z‖ = 1} :=
      isClosed_eq (continuous_fst.norm.max continuous_snd.norm) continuous_const
    letI : CompactSpace {z : ℝ × ℝ // ‖z‖ ≤ 1} := isCompact_iff_compactSpace.mp hQ
    letI : CompactSpace {z : ℝ × ℝ // ‖z‖ = 1} :=
      isCompact_iff_compactSpace.mp (hQ.of_isClosed_subset hB (fun z hz => hz.le))
    have hradial : ∃ q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, {z : ℝ × ℝ // ‖z‖ ≤ 1}),
        Function.Surjective q ∧
        (∀ a b, q a = q b → a = b ∨ a.1 = 1 ∧ b.1 = 1) ∧
        (∀ a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, (q a : ℝ × ℝ) = (1-a.1.val) • (a.2 : ℝ × ℝ)) := by
      let q : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}, {z : ℝ × ℝ // ‖z‖ ≤ 1}) :=
        ⟨fun a => ⟨(1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ), by
          rw [norm_smul, a.2.property, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
          linarith [a.1.property.1]⟩,
          by fun_prop⟩
      have hnorm (a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) : ‖(q a : ℝ × ℝ)‖ = 1 - (a.1 : ℝ) := by
        change ‖(1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ)‖ = _
        rw [norm_smul, a.2.property, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr a.1.property.2)]
      refine ⟨q, ?_, ?_, ?_⟩
      · intro z
        by_cases hz : (z : ℝ × ℝ) = 0
        · refine ⟨(1, ⟨(1,0), by simp⟩), ?_⟩
          apply Subtype.ext
          simp [q, hz]
        · have hn : ‖(z : ℝ × ℝ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
          let u : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨‖(z : ℝ × ℝ)‖⁻¹ • (z : ℝ × ℝ), by
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
            exact inv_mul_cancel₀ hn⟩
          refine ⟨(⟨1 - ‖(z : ℝ × ℝ)‖, by constructor <;> linarith only [z.property, norm_nonneg (z : ℝ × ℝ)]⟩, u), ?_⟩
          apply Subtype.ext
          change (1 - (1 - ‖(z : ℝ × ℝ)‖)) • (‖(z : ℝ × ℝ)‖⁻¹ • (z : ℝ × ℝ)) = (z : ℝ × ℝ)
          rw [sub_sub_cancel, smul_smul, mul_inv_cancel₀ hn, one_smul]
      · intro a b hab
        have ht : a.1 = b.1 := by
          apply Subtype.ext
          have h := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ ≤ 1} => ‖(z : ℝ × ℝ)‖) hab
          rw [hnorm, hnorm] at h
          linarith
        by_cases ha : a.1 = 1
        · exact Or.inr ⟨ha, ht.symm.trans ha⟩
        · left
          apply Prod.ext ht
          apply Subtype.ext
          have h := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ ≤ 1} => (z : ℝ × ℝ)) hab
          change (1 - (a.1 : ℝ)) • (a.2 : ℝ × ℝ) = (1 - (b.1 : ℝ)) • (b.2 : ℝ × ℝ) at h
          rw [← ht] at h
          have hn : 1 - (a.1 : ℝ) ≠ 0 := by
            intro he
            apply ha
            apply Subtype.ext
            change (a.1 : ℝ) = 1
            linarith
          exact (smul_right_injective _ hn) h
      · intro a
        rfl
    obtain ⟨q,hsurj,hfiber,hqformula⟩ := hradial
    let K : C(unitInterval × {z : ℝ × ℝ // ‖z‖ = 1},V) :=
      ⟨fun a => ⟨(1-a.1.val) • (f a.2).val+a.1.val • v.val,
        hV (f a.2).property v.property (by linarith [a.1.property.2]) a.1.property.1 (by ring)⟩,
        by fun_prop⟩
    have hrespect (a b : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) (hab : q a = q b) : K a = K b := by
      rcases hfiber a b hab with hab | ⟨ha,hb⟩
      · rw [hab]
      · apply Subtype.ext
        simp [K,ha,hb]
    let G : {z : ℝ × ℝ // ‖z‖ ≤ 1} → V := fun z => K (Function.surjInv hsurj z)
    have hGq (a : unitInterval × {z : ℝ × ℝ // ‖z‖ = 1}) : G (q a) = K a :=
      hrespect _ _ (Function.surjInv_eq hsurj (q a))
    have hquot := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
    have hGc : Continuous G := hquot.continuous_iff.mpr (by
      have heq : G ∘ q = K := funext hGq
      rw [heq]; exact K.continuous)
    refine ⟨q,⟨G,hGc⟩,hsurj,hqformula,?_⟩
    intro a
    exact congrArg Subtype.val (hGq a)
  have normalizedSquareConeFill (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
      (f : C({z : ℝ × ℝ // ‖z‖ = 1},V)) (v : V) :
      ∃ G : C(Interval × Interval,V),
        ∀ r : Interval, ∀ z : {z : ℝ × ℝ // ‖z‖ = 1},
          ∃ q : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q.val = (1-r.val) • z.val ∧
            (G (squareCoordinates q)).val = (1-r.val) • (f z).val+r.val • v.val := by
    obtain ⟨q,G,hq,hformula,hfill⟩ := squareConeFill V hV f v
    let G0 : C(Interval × Interval,V) := G.comp ⟨squareCoordinates.symm,squareCoordinates.symm.continuous⟩
    refine ⟨G0,?_⟩
    intro r z
    refine ⟨q (r,z),hformula (r,z),?_⟩
    change (G (squareCoordinates.symm (squareCoordinates (q (r,z))))).val = _
    rw [squareCoordinates.symm_apply_apply]
    exact hfill (r,z)
  have finiteClosedGlue {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {I : Type} [Finite I]
      (C : I → Set X) (hC : ∀ i, IsClosed (C i))
      (hcover : ∀ x, ∃ i, x ∈ C i) (f : I → C(X,Y))
      (hagree : ∀ i j x, x ∈ C i → x ∈ C j → f i x = f j x) :
      ∃ G : C(X,Y), ∀ i x, x ∈ C i → G x = f i x := by
    classical
    choose index hindex using hcover
    let G : X → Y := fun x => f (index x) x
    have hG (i : I) (x : X) (hx : x ∈ C i) : G x = f i x :=
      hagree (index x) i x (hindex x) hx
    have hGc : Continuous G := continuous_iff_isClosed.mpr (by
      intro D hD
      have heq : G ⁻¹' D = ⋃ i, C i ∩ (f i) ⁻¹' D := by
        ext x
        constructor
        · intro hx
          exact Set.mem_iUnion.mpr ⟨index x,hindex x,hx⟩
        · intro hx
          obtain ⟨i,hxi,hfix⟩ := Set.mem_iUnion.mp hx
          change G x ∈ D
          rw [hG i x hxi]
          exact hfix
      rw [heq]
      exact isClosed_iUnion_of_finite (fun i => (hC i).inter (hD.preimage (f i).continuous)))
    exact ⟨⟨G,hGc⟩,hG⟩
  have fourSideBoundary {Y : Type} [TopologicalSpace Y] {bl br tl tr : Y}
      (bottom : Path bl br) (right : Path br tr) (top : Path tl tr) (left : Path bl tl) :
      ∃ f : C({z : ℝ × ℝ // ‖z‖ = 1},Y),
        ∀ z, (z.val.2 = -1 → f z = bottom ((squareCoordinates ⟨z.val,z.property.le⟩).1)) ∧
          (z.val.1 = 1 → f z = right ((squareCoordinates ⟨z.val,z.property.le⟩).2)) ∧
          (z.val.2 = 1 → f z = top ((squareCoordinates ⟨z.val,z.property.le⟩).1)) ∧
          (z.val.1 = -1 → f z = left ((squareCoordinates ⟨z.val,z.property.le⟩).2)) := by
    let B := {z : ℝ × ℝ // ‖z‖ = 1}
    let bc : C(B,Interval × Interval) :=
      ⟨fun z => squareCoordinates ⟨z.val,z.property.le⟩,by fun_prop⟩
    let xc : C(B,Interval) := ⟨fun z => (bc z).1,continuous_fst.comp bc.continuous⟩
    let yc : C(B,Interval) := ⟨fun z => (bc z).2,continuous_snd.comp bc.continuous⟩
    have xzero (z : B) (hz : z.val.1 = -1) : xc z = 0 := by
      apply Subtype.ext
      change (z.val.1+1)/2 = 0
      rw [hz]
      norm_num
    have xone (z : B) (hz : z.val.1 = 1) : xc z = 1 := by
      apply Subtype.ext
      change (z.val.1+1)/2 = 1
      rw [hz]
      norm_num
    have yzero (z : B) (hz : z.val.2 = -1) : yc z = 0 := by
      apply Subtype.ext
      change (z.val.2+1)/2 = 0
      rw [hz]
      norm_num
    have yone (z : B) (hz : z.val.2 = 1) : yc z = 1 := by
      apply Subtype.ext
      change (z.val.2+1)/2 = 1
      rw [hz]
      norm_num
    let D : Fin 4 → Set B := fun i =>
      if i.val = 0 then {z | z.val.2 = -1} else
      if i.val = 1 then {z | z.val.1 = 1} else
      if i.val = 2 then {z | z.val.2 = 1} else {z | z.val.1 = -1}
    let edges : Fin 4 → C(B,Y) := fun i =>
      if i.val = 0 then bottom.toContinuousMap.comp xc else
      if i.val = 1 then right.toContinuousMap.comp yc else
      if i.val = 2 then top.toContinuousMap.comp xc else left.toContinuousMap.comp yc
    have hD : ∀ i, IsClosed (D i) := by
      intro i
      fin_cases i <;> simp only [D] <;>
        exact isClosed_eq (by fun_prop) continuous_const
    have hcover : ∀ z : B, ∃ i, z ∈ D i := by
      intro z
      have hn : max |z.val.1| |z.val.2| = 1 := by
        simpa only [Prod.norm_def,Real.norm_eq_abs] using z.property
      have hpair : |z.val.1| = 1 ∨ |z.val.2| = 1 := by
        by_cases hx : |z.val.1| = 1
        · exact Or.inl hx
        · right
          by_contra hy
          have hxlt : |z.val.1| < 1 := lt_of_le_of_ne ((le_max_left _ _).trans hn.le) hx
          have hylt : |z.val.2| < 1 := lt_of_le_of_ne ((le_max_right _ _).trans hn.le) hy
          have hmax := max_lt hxlt hylt
          rw [hn] at hmax
          exact lt_irrefl _ hmax
      rcases hpair with hx | hy
      · by_cases hx0 : 0 ≤ z.val.1
        · refine ⟨1,?_⟩
          change z.val.1 = 1
          rwa [abs_of_nonneg hx0] at hx
        · refine ⟨3,?_⟩
          change z.val.1 = -1
          rw [abs_of_neg (lt_of_not_ge hx0)] at hx
          linarith
      · by_cases hy0 : 0 ≤ z.val.2
        · refine ⟨2,?_⟩
          change z.val.2 = 1
          rwa [abs_of_nonneg hy0] at hy
        · refine ⟨0,?_⟩
          change z.val.2 = -1
          rw [abs_of_neg (lt_of_not_ge hy0)] at hy
          linarith
    have hagree : ∀ i j z, z ∈ D i → z ∈ D j → edges i z = edges j z := by
      intro i j z hi hj
      fin_cases i <;> fin_cases j <;> simp [D,edges,ContinuousMap.comp_apply] at hi hj ⊢
      all_goals first
        | rfl
        | (exfalso; linarith)
        | (simp_all only [xzero,xone,yzero,yone,Path.source,Path.target])
    obtain ⟨f,hf⟩ := finiteClosedGlue D hD hcover edges hagree
    refine ⟨f,?_⟩
    intro z
    exact ⟨fun hz => hf 0 z hz,fun hz => hf 1 z hz,fun hz => hf 2 z hz,fun hz => hf 3 z hz⟩
  have convexSquareFill (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
      {bl br tl tr : V} (bottom : Path bl br) (right : Path br tr)
      (top : Path tl tr) (left : Path bl tl) (v : V) :
      ∃ (G : C(Interval × Interval,V)) (f : C({z : ℝ × ℝ // ‖z‖ = 1},V)),
        (∀ t : Interval,
        G (t,0) = bottom t ∧ G (1,t) = right t ∧
        G (t,1) = top t ∧ G (0,t) = left t) ∧
        ∀ r : Interval, ∀ z : {z : ℝ × ℝ // ‖z‖ = 1},
          ∃ q : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q.val = (1-r.val) • z.val ∧
            (G (squareCoordinates q)).val = (1-r.val) • (f z).val+r.val • v.val := by
    obtain ⟨f,hf⟩ := fourSideBoundary bottom right top left
    obtain ⟨G,hG⟩ := normalizedSquareConeFill V hV f v
    have hboundary (z : {z : ℝ × ℝ // ‖z‖ = 1}) :
        G (squareCoordinates ⟨z.val,z.property.le⟩) = f z := by
      obtain ⟨q,hq,hfill⟩ := hG 0 z
      have heq : q = ⟨z.val,z.property.le⟩ := Subtype.ext (by simpa using hq)
      rw [heq] at hfill
      apply Subtype.ext
      simpa using hfill
    refine ⟨G,f,?_,hG⟩
    intro t
    have hnorm (u : ℝ) (hu : -1 ≤ u ∧ u ≤ 1) :
        ‖((u,-1) : ℝ × ℝ)‖ = 1 ∧ ‖((1,u) : ℝ × ℝ)‖ = 1 ∧
        ‖((u,1) : ℝ × ℝ)‖ = 1 ∧ ‖((-1,u) : ℝ × ℝ)‖ = 1 := by
      have habs : |u| ≤ 1 := abs_le.mpr hu
      simp only [Prod.norm_mk,Real.norm_eq_abs,abs_neg,abs_one]
      exact ⟨max_eq_right habs,max_eq_left habs,max_eq_right habs,max_eq_left habs⟩
    have ht : -1 ≤ 2*t.val-1 ∧ 2*t.val-1 ≤ 1 := by
      constructor <;> linarith [t.property.1,t.property.2]
    let zb : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨(2*t.val-1,-1),(hnorm _ ht).1⟩
    let zr : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨(1,2*t.val-1),(hnorm _ ht).2.1⟩
    let zt : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨(2*t.val-1,1),(hnorm _ ht).2.2.1⟩
    let zl : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨(-1,2*t.val-1),(hnorm _ ht).2.2.2⟩
    have hb : squareCoordinates ⟨zb.val,zb.property.le⟩ = (t,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · change ((2*t.val-1)+1)/2 = t.val; ring
      · change ((-1 : ℝ)+1)/2 = 0; norm_num
    have hr : squareCoordinates ⟨zr.val,zr.property.le⟩ = (1,t) := by
      apply Prod.ext <;> apply Subtype.ext
      · change ((1 : ℝ)+1)/2 = 1; norm_num
      · change ((2*t.val-1)+1)/2 = t.val; ring
    have htt : squareCoordinates ⟨zt.val,zt.property.le⟩ = (t,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · change ((2*t.val-1)+1)/2 = t.val; ring
      · change ((1 : ℝ)+1)/2 = 1; norm_num
    have hl : squareCoordinates ⟨zl.val,zl.property.le⟩ = (0,t) := by
      apply Prod.ext <;> apply Subtype.ext
      · change ((-1 : ℝ)+1)/2 = 0; norm_num
      · change ((2*t.val-1)+1)/2 = t.val; ring
    constructor
    · calc G (t,0) = f zb := by rw [← hb]; exact hboundary zb
           _ = bottom t := by have h := (hf zb).1 rfl; rwa [hb] at h
    constructor
    · calc G (1,t) = f zr := by rw [← hr]; exact hboundary zr
           _ = right t := by have h := (hf zr).2.1 rfl; rwa [hr] at h
    constructor
    · calc G (t,1) = f zt := by rw [← htt]; exact hboundary zt
           _ = top t := by have h := (hf zt).2.2.1 rfl; rwa [htt] at h
    · calc G (0,t) = f zl := by rw [← hl]; exact hboundary zl
           _ = left t := by have h := (hf zl).2.2.2 rfl; rwa [hl] at h
  have coneZeroArc (c : ℝ) (hc : 0 < c) (g : C(Interval,ℝ))
      (hg : ∀ t, g t ≤ 0) (h0 : g 0 = 0) (h1 : g 1 = 0)
      (hneg : ∀ t ∈ Set.Ioo (0 : Interval) 1, g t < 0) :
      ∃ q : C(Interval,Interval × Interval), Topology.IsEmbedding q ∧
        q 0 = (1,0) ∧ q 1 = (1,1) ∧
        (∀ t, (1-(q t).1.val)*c+(q t).1.val*g t = 0) ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1, (q t).1 ∈ Set.Ioo (0 : Interval) 1) ∧
        (∀ t (r : Interval), (1-r.val)*c+r.val*g t = 0 → r = (q t).1) := by
    have hden (t : Interval) : 0 < c-g t := by linarith [hg t]
    let radius : C(Interval,Interval) :=
      ⟨fun t => ⟨c/(c-g t),⟨(div_pos hc (hden t)).le,
        (div_le_one (hden t)).mpr (by linarith [hg t])⟩⟩,
        (continuous_const.div (continuous_const.sub g.continuous)
          (fun t => (hden t).ne')).subtype_mk _⟩
    let q : C(Interval,Interval × Interval) :=
      ⟨fun t => (radius t,t),radius.continuous.prodMk continuous_id⟩
    have hqinj : Function.Injective q := fun t u h => congrArg Prod.snd h
    refine ⟨q,(q.continuous.isClosedEmbedding hqinj).isEmbedding,?_,?_,?_,?_,?_⟩
    · apply Prod.ext
      · apply Subtype.ext; simp [q,radius,h0,hc.ne']
      · rfl
    · apply Prod.ext
      · apply Subtype.ext; simp [q,radius,h1,hc.ne']
      · rfl
    · intro t
      change (1-c/(c-g t))*c+(c/(c-g t))*g t = 0
      field_simp [(hden t).ne']
      <;> ring
    · intro t ht
      change 0 < c/(c-g t) ∧ c/(c-g t) < 1
      exact ⟨div_pos hc (hden t),(div_lt_one (hden t)).mpr (by linarith [hneg t ht])⟩
    · intro t r hr
      apply Subtype.ext
      change r.val = c/(c-g t)
      apply (eq_div_iff (hden t).ne').mpr
      nlinarith
  have surfaceSquareFill (E : OpenPartialHomeomorph S (ℝ × ℝ))
      (hV : Convex ℝ E.target) {bl br tl tr : S}
      (bottom : Path bl br) (right : Path br tr)
      (top : Path tl tr) (left : Path bl tl)
      (hb : Set.range bottom ⊆ E.source) (hr : Set.range right ⊆ E.source)
      (htop : Set.range top ⊆ E.source) (hl : Set.range left ⊆ E.source)
      (v : E.target) :
      ∃ (G : C(Interval × Interval,S))
        (f : C({z : ℝ × ℝ // ‖z‖ = 1},E.target)),
        (∀ z, G z ∈ E.source) ∧
        (∀ t, G (t,0) = bottom t ∧ G (1,t) = right t ∧
          G (t,1) = top t ∧ G (0,t) = left t) ∧
        ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖ = 1}),
          ∃ q : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q.val = (1-r.val) • z.val ∧
            E (G (squareCoordinates q)) =
              (1-r.val) • (f z).val+r.val • v.val := by
    let H := E.toHomeomorphSourceTarget
    have chartPath {x y : S} (p : Path x y) (hp : Set.range p ⊆ E.source) :
        ∃ q : Path (H ⟨x,p.source ▸ hp ⟨0,rfl⟩⟩)
          (H ⟨y,p.target ▸ hp ⟨1,rfl⟩⟩), ∀ t, (q t).val = E (p t) := by
      let ps : Path (⟨x,p.source ▸ hp ⟨0,rfl⟩⟩ : E.source)
          (⟨y,p.target ▸ hp ⟨1,rfl⟩⟩ : E.source) := {
        toFun := fun t => ⟨p t,hp ⟨t,rfl⟩⟩
        continuous_toFun := p.continuous.subtype_mk _
        source' := by apply Subtype.ext; exact p.source
        target' := by apply Subtype.ext; exact p.target }
      exact ⟨ps.map H.continuous,fun _ => rfl⟩
    obtain ⟨b0,hb0⟩ := chartPath bottom hb
    obtain ⟨r0,hr0⟩ := chartPath right hr
    obtain ⟨t0,ht0⟩ := chartPath top htop
    obtain ⟨l0,hl0⟩ := chartPath left hl
    obtain ⟨G0,f,hfaces,hcone⟩ := convexSquareFill E.target hV b0 r0 t0 l0 v
    let G : C(Interval × Interval,S) :=
      ⟨fun z => (H.symm (G0 z)).val,
        continuous_subtype_val.comp (H.symm.continuous.comp G0.continuous)⟩
    have hchart (z : Interval × Interval) : E (G z) = (G0 z).val := by
      change (H (H.symm (G0 z))).val = (G0 z).val
      rw [H.apply_symm_apply]
    refine ⟨G,f,fun z => (H.symm (G0 z)).property,?_,?_⟩
    · intro t
      have heq {z : Interval × Interval} {p : S} (hp : p ∈ E.source)
          (hc : (G0 z).val = E p) : G z = p := by
        have hh : H ⟨G z,(H.symm (G0 z)).property⟩ = H ⟨p,hp⟩ := by
          apply Subtype.ext
          exact (hchart z).trans hc
        exact congrArg Subtype.val (H.injective hh)
      refine ⟨heq (hb ⟨t,rfl⟩) ?_,heq (hr ⟨t,rfl⟩) ?_,
        heq (htop ⟨t,rfl⟩) ?_,heq (hl ⟨t,rfl⟩) ?_⟩
      · rw [(hfaces t).1]; exact hb0 t
      · rw [(hfaces t).2.1]; exact hr0 t
      · rw [(hfaces t).2.2.1]; exact ht0 t
      · rw [(hfaces t).2.2.2]; exact hl0 t
    · intro r z
      obtain ⟨q,hq,hval⟩ := hcone r z
      exact ⟨q,hq,(hchart _).trans hval⟩
  have endpointTraceFinite :
      ((fun t : Interval => F (0,t)) ⁻¹' b.val.image).Finite ∧
      ((fun t : Interval => F (1,t)) ⁻¹' b.val.image).Finite := by
    constructor
    · apply hzeroEvents.subset
      intro t htB
      change intervalCurveLoopFrom a.val z₀ t ∈ b.val.image ∩ a.val.image
      exact ⟨(Fzero t) ▸ htB,⟨z₀ * Circle.exp (2*Real.pi*t.val),rfl⟩⟩
    · apply honeEvents.subset
      intro t htB
      change intervalCurveLoopFrom endCurve z₀ t ∈ b.val.image ∩ endCurve.image
      exact ⟨(Fone t) ▸ htB,⟨z₀ * Circle.exp (2*Real.pi*t.val),rfl⟩⟩
  have finiteOriginalSubpath {x y : Interval} (hxy : x < y)
      (γ : C(Interval,S)) (hγ : (γ ⁻¹' b.val.image).Finite) :
      ∃ p : Path (γ x) (γ y), (p ⁻¹' b.val.image).Finite ∧
        ∀ t : Interval, ∃ s : Interval,
          s.val = (1-t.val)*x.val+t.val*y.val ∧ p t = γ s := by
    let d : Path x y := {
      toFun := fun t => ⟨(1-t.val)*x.val+t.val*y.val,by
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property.1)
            (mul_nonneg t.property.1 y.property.1)
        · nlinarith only [t.property.1,t.property.2,x.property.1,x.property.2,y.property.1,y.property.2]⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
    have hinj : Function.Injective d := by
      intro t u he
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      change (1-t.val)*x.val+t.val*y.val = (1-u.val)*x.val+u.val*y.val at hh
      have hlt : x.val < y.val := hxy
      nlinarith
    have hfin : (d ⁻¹' (γ ⁻¹' b.val.image)).Finite := hγ.preimage hinj.injOn
    exact ⟨d.map γ.continuous,hfin,fun t => ⟨d t,rfl,rfl⟩⟩
  have exactOriginalBoundaryEdges (i : Fin (n+1)) :
      (∃ p : Path (F (0,phaseGrid i.castSucc)) (F (0,phaseGrid i.succ)),
        (p ⁻¹' b.val.image).Finite ∧ ∀ t : Interval, ∃ s : Interval,
          s.val = (1-t.val)*(phaseGrid i.castSucc).val+t.val*(phaseGrid i.succ).val ∧
          p t = F (0,s)) ∧
      (∃ p : Path (F (1,phaseGrid i.castSucc)) (F (1,phaseGrid i.succ)),
        (p ⁻¹' b.val.image).Finite ∧ ∀ t : Interval, ∃ s : Interval,
          s.val = (1-t.val)*(phaseGrid i.castSucc).val+t.val*(phaseGrid i.succ).val ∧
          p t = F (1,s)) := by
    exact ⟨finiteOriginalSubpath (phaseStep i)
      ⟨fun t => F (0,t),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      endpointTraceFinite.1,
      finiteOriginalSubpath (phaseStep i)
      ⟨fun t => F (1,t),F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      endpointTraceFinite.2⟩
  have meshOverlap (i j : Fin (n+1)) (t : Interval)
      (hi0 : phaseGrid i.castSucc ≤ t) (hi1 : t ≤ phaseGrid i.succ)
      (hj0 : phaseGrid j.castSucc ≤ t) (hj1 : t ≤ phaseGrid j.succ)
      (hij : i < j) : i.succ = j.castSucc ∧ t = phaseGrid i.succ := by
    have hle : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
    have hm : phaseGrid i.succ ≤ phaseGrid j.castSucc := phaseGridStrict.monotone hle
    have ht : t = phaseGrid i.succ := le_antisymm hi1 (hm.trans hj0)
    have he : phaseGrid i.succ = phaseGrid j.castSucc :=
      le_antisymm hm (hj0.trans hi1)
    exact ⟨phaseGridStrict.injective he,ht⟩
  have localCoordinateOverlap (i j : Fin (n+1)) (t : Interval)
      (hi0 : phaseGrid i.castSucc ≤ t) (hi1 : t ≤ phaseGrid i.succ)
      (hj0 : phaseGrid j.castSucc ≤ t) (hj1 : t ≤ phaseGrid j.succ)
      (hij : i < j) : localCoordinate i t = 1 ∧ localCoordinate j t = 0 := by
    obtain ⟨he,ht⟩ := meshOverlap i j t hi0 hi1 hj0 hj1 hij
    constructor
    · rw [ht]; exact localCoordinateRight i
    · rw [ht,he]; exact localCoordinateLeft j
  have coherentCellGlue {Y : Type} [TopologicalSpace Y]
      (g : Fin (n+1) × Fin (n+1) → C(Interval × Interval,Y))
      (hvertical : ∀ (i j : Fin (n+1)) (s : Interval),
        i.val+1 = j.val → ∀ k : Fin (n+1), g (i,k) (1,s) = g (j,k) (0,s))
      (hhorizontal : ∀ (i j : Fin (n+1)) (t : Interval),
        i.val+1 = j.val → ∀ k : Fin (n+1), g (k,i) (t,1) = g (k,j) (t,0)) :
      ∃ G : C(Interval × Interval,Y), ∀ k z, z ∈ cellDomain k →
        G z = g k (cellCoordinates k z) := by
    have agreement (i j : Fin (n+1) × Fin (n+1)) (z : Interval × Interval)
        (hi : z ∈ cellDomain i) (hj : z ∈ cellDomain j) :
        g i (cellCoordinates i z) = g j (cellCoordinates j z) := by
      have alongFirst (p q r : Fin (n+1))
          (hp0 : phaseGrid p.castSucc ≤ z.1) (hp1 : z.1 ≤ phaseGrid p.succ)
          (hq0 : phaseGrid q.castSucc ≤ z.1) (hq1 : z.1 ≤ phaseGrid q.succ) :
          g (p,r) (localCoordinate p z.1,localCoordinate r z.2) =
          g (q,r) (localCoordinate q z.1,localCoordinate r z.2) := by
        rcases lt_trichotomy p q with hpq | hpq | hqp
        · obtain ⟨he,_⟩ := meshOverlap p q z.1 hp0 hp1 hq0 hq1 hpq
          obtain ⟨hpc,hqc⟩ := localCoordinateOverlap p q z.1 hp0 hp1 hq0 hq1 hpq
          rw [hpc,hqc]
          exact hvertical p q _ (congrArg Fin.val he) r
        · rw [hpq]
        · obtain ⟨he,_⟩ := meshOverlap q p z.1 hq0 hq1 hp0 hp1 hqp
          obtain ⟨hqc,hpc⟩ := localCoordinateOverlap q p z.1 hq0 hq1 hp0 hp1 hqp
          rw [hpc,hqc]
          exact (hvertical q p _ (congrArg Fin.val he) r).symm
      have alongSecond (p q r : Fin (n+1))
          (hp0 : phaseGrid p.castSucc ≤ z.2) (hp1 : z.2 ≤ phaseGrid p.succ)
          (hq0 : phaseGrid q.castSucc ≤ z.2) (hq1 : z.2 ≤ phaseGrid q.succ) :
          g (r,p) (localCoordinate r z.1,localCoordinate p z.2) =
          g (r,q) (localCoordinate r z.1,localCoordinate q z.2) := by
        rcases lt_trichotomy p q with hpq | hpq | hqp
        · obtain ⟨he,_⟩ := meshOverlap p q z.2 hp0 hp1 hq0 hq1 hpq
          obtain ⟨hpc,hqc⟩ := localCoordinateOverlap p q z.2 hp0 hp1 hq0 hq1 hpq
          rw [hpc,hqc]
          exact hhorizontal p q _ (congrArg Fin.val he) r
        · rw [hpq]
        · obtain ⟨he,_⟩ := meshOverlap q p z.2 hq0 hq1 hp0 hp1 hqp
          obtain ⟨hqc,hpc⟩ := localCoordinateOverlap q p z.2 hq0 hq1 hp0 hp1 hqp
          rw [hpc,hqc]
          exact (hhorizontal q p _ (congrArg Fin.val he) r).symm
      exact (alongFirst i.1 j.1 i.2 hi.1 hi.2.1 hj.1 hj.2.1).trans
        (alongSecond i.2 j.2 j.1 hi.2.2.1 hi.2.2.2 hj.2.2.1 hj.2.2.2)
    exact finiteClosedGlue cellDomain hcellClosed hcellCover
      (fun k => (g k).comp (cellCoordinates k)) agreement
  have meshFillFromEdges
      (he : ∀ (i : Fin (n+1)) (j : Fin (n+2)),
        Path (perturbedVertex (i.castSucc,j)) (perturbedVertex (i.succ,j)))
      (ve : ∀ (i : Fin (n+2)) (j : Fin (n+1)),
        Path (perturbedVertex (i,j.castSucc)) (perturbedVertex (i,j.succ)))
      (hedges : ∀ k : Fin (n+1) × Fin (n+1),
        Set.range (he k.1 k.2.castSucc) ⊆ chartDomain (chart k) ∧
        Set.range (ve k.1.succ k.2) ⊆ chartDomain (chart k) ∧
        Set.range (he k.1 k.2.succ) ⊆ chartDomain (chart k) ∧
        Set.range (ve k.1.castSucc k.2) ⊆ chartDomain (chart k))
      (center : ∀ k : Fin (n+1) × Fin (n+1), (convexChart (chart k)).target) :
      ∃ (G : C(Interval × Interval,S))
        (cells : Fin (n+1) × Fin (n+1) → C(Interval × Interval,S))
        (boundaries : ∀ k : Fin (n+1) × Fin (n+1),
          C({z : ℝ × ℝ // ‖z‖ = 1},(convexChart (chart k)).target)),
        (∀ k z, z ∈ cellDomain k → G z = cells k (cellCoordinates k z)) ∧
        (∀ k z, cells k z ∈ chartDomain (chart k)) ∧
        (∀ k t, cells k (t,0) = he k.1 k.2.castSucc t ∧
          cells k (1,t) = ve k.1.succ k.2 t ∧
          cells k (t,1) = he k.1 k.2.succ t ∧
          cells k (0,t) = ve k.1.castSucc k.2 t) ∧
        ∀ k (r : Interval) (z : {z : ℝ × ℝ // ‖z‖ = 1}),
          ∃ q : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q.val = (1-r.val) • z.val ∧
            convexChart (chart k) (cells k (squareCoordinates q)) =
              (1-r.val) • (boundaries k z).val+r.val • (center k).val := by
    have localFill (k : Fin (n+1) × Fin (n+1)) :=
      surfaceSquareFill (convexChart (chart k)) (hconvexTarget (chart k))
        (he k.1 k.2.castSucc) (ve k.1.succ k.2) (he k.1 k.2.succ) (ve k.1.castSucc k.2)
        (hedges k).1 (hedges k).2.1 (hedges k).2.2.1 (hedges k).2.2.2 (center k)
    choose cells boundaries hrange hfaces hcone using localFill
    have vertical (i j : Fin (n+1)) (s : Interval) (hij : i.val+1 = j.val)
        (k : Fin (n+1)) : cells (i,k) (1,s) = cells (j,k) (0,s) := by
      have heq : i.succ = j.castSucc := by apply Fin.ext; exact hij
      rw [(hfaces (i,k) s).2.1,(hfaces (j,k) s).2.2.2,heq]
    have horizontal (i j : Fin (n+1)) (t : Interval) (hij : i.val+1 = j.val)
        (k : Fin (n+1)) : cells (k,i) (t,1) = cells (k,j) (t,0) := by
      have heq : i.succ = j.castSucc := by apply Fin.ext; exact hij
      rw [(hfaces (k,i) t).2.2.1,(hfaces (k,j) t).1,heq]
    obtain ⟨G,hG⟩ := coherentCellGlue cells vertical horizontal
    exact ⟨G,cells,boundaries,hG,hrange,hfaces,hcone⟩
  have originalBoundaryEdge (i : Fin (n+2)) (hi : i.val = 0 ∨ i.val = n+1)
      (j : Fin (n+1)) :
      ∃ p : Path (perturbedVertex (i,j.castSucc)) (perturbedVertex (i,j.succ)),
        (p ⁻¹' b.val.image).Finite ∧
        (∀ k, incident k (i,j.castSucc) ∧ incident k (i,j.succ) →
          Set.range p ⊆ chartDomain (chart k)) ∧
        ∀ t : Interval, ∃ u : Interval,
          u.val = (1-t.val)*(phaseGrid j.castSucc).val+t.val*(phaseGrid j.succ).val ∧
          p t = F (phaseGrid i,u) := by
    let γ : C(Interval,S) := ⟨fun t => F (phaseGrid i,t),
      F.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hf : (γ ⁻¹' b.val.image).Finite := by
      rcases hi with hi | hi
      · have he : phaseGrid i = 0 := by simp only [phaseGrid,dif_pos hi]
        simpa only [γ,ContinuousMap.coe_mk,he] using endpointTraceFinite.1
      · have hiz : i.val ≠ 0 := by omega
        have he : phaseGrid i = 1 := by simp only [phaseGrid,dif_neg hiz,dif_pos hi]
        simpa only [γ,ContinuousMap.coe_mk,he] using endpointTraceFinite.2
    obtain ⟨q,hq,hformula⟩ := finiteOriginalSubpath (phaseStep j) γ hf
    have hsource : perturbedVertex (i,j.castSucc) = γ (phaseGrid j.castSucc) :=
      hvertexBoundary _ hi
    have htarget : perturbedVertex (i,j.succ) = γ (phaseGrid j.succ) :=
      hvertexBoundary _ hi
    let p := q.cast hsource htarget
    refine ⟨p,hq,?_,hformula⟩
    intro k hk x hx
    obtain ⟨t,rfl⟩ := hx
    obtain ⟨u,hu,hqu⟩ := hformula t
    change q t ∈ chartDomain (chart k)
    rw [hqu]
    apply phaseGridCellCover k (phaseGrid i,u) hk.1.1 hk.1.2.1
    · have h0 : (phaseGrid k.2.castSucc).val ≤ (phaseGrid j.castSucc).val := hk.1.2.2.1
      have h1 : (phaseGrid k.2.castSucc).val ≤ (phaseGrid j.succ).val := hk.2.2.2.1
      change (phaseGrid k.2.castSucc).val ≤ u.val
      rw [hu]
      nlinarith [t.property.1,t.property.2]
    · have h0 : (phaseGrid j.castSucc).val ≤ (phaseGrid k.2.succ).val := hk.1.2.2.2
      have h1 : (phaseGrid j.succ).val ≤ (phaseGrid k.2.succ).val := hk.2.2.2.2
      change u.val ≤ (phaseGrid k.2.succ).val
      rw [hu]
      nlinarith [t.property.1,t.property.2]
  -- These choices are actual paths for this trace and this perturbed grid.
  -- Each ordinary mesh edge is selected once, shared by its incident cells.
  choose edgeLeft edgeRight edgeOriginal edgePath edgeSupport edgeFinite edgeHomotopy
    using sharedEdgeCandidate
  let ordinaryTimeEdge (i : Fin (n+1)) (j : Fin (n+2)) :=
    edgePath (i.castSucc,j) (i.succ,j)
  let ordinarySpaceEdge (i : Fin (n+2)) (j : Fin (n+1)) :=
    edgePath (i,j.castSucc) (i,j.succ)
  have gridCorners (k : Fin (n+1) × Fin (n+1)) :
      incident k (k.1.castSucc,k.2.castSucc) ∧
      incident k (k.1.succ,k.2.castSucc) ∧
      incident k (k.1.castSucc,k.2.succ) ∧
      incident k (k.1.succ,k.2.succ) := by
    have h1 : phaseGrid k.1.castSucc ≤ phaseGrid k.1.succ := (phaseStep k.1).le
    have h2 : phaseGrid k.2.castSucc ≤ phaseGrid k.2.succ := (phaseStep k.2).le
    exact ⟨⟨le_rfl,h1,le_rfl,h2⟩,⟨h1,le_rfl,le_rfl,h2⟩,
      ⟨le_rfl,h1,h2,le_rfl⟩,⟨h1,le_rfl,h2,le_rfl⟩⟩
  have ordinaryEdgeSupport (k : Fin (n+1) × Fin (n+1)) :
      Set.range (ordinaryTimeEdge k.1 k.2.castSucc) ⊆ chartDomain (chart k) ∧
      Set.range (ordinarySpaceEdge k.1.succ k.2) ⊆ chartDomain (chart k) ∧
      Set.range (ordinaryTimeEdge k.1 k.2.succ) ⊆ chartDomain (chart k) ∧
      Set.range (ordinarySpaceEdge k.1.castSucc k.2) ⊆ chartDomain (chart k) := by
    have h := gridCorners k
    exact ⟨edgeSupport _ _ k ⟨h.1,h.2.1⟩,
      edgeSupport _ _ k ⟨h.2.1,h.2.2.2⟩,
      edgeSupport _ _ k ⟨h.2.2.1,h.2.2.2⟩,
      edgeSupport _ _ k ⟨h.1,h.2.2.1⟩⟩
  have actualCellCenter (k : Fin (n+1) × Fin (n+1)) :
      ∃ p ∈ chartDomain (chart k), p ∉ b.val.image :=
    offComparisonInOpen _ (hDomainOpen _) _ (hconvexPoint _)
  choose centerPoint centerInChart centerOffComparison using actualCellCenter
  let cellCenter (k : Fin (n+1) × Fin (n+1)) : (convexChart (chart k)).target :=
    ⟨convexChart (chart k) (centerPoint k),
      (convexChart (chart k)).map_source (centerInChart k)⟩
  have cellCenterAxisNonzero (k : Fin (n+1) × Fin (n+1))
      (haxis : ∀ x ∈ chartDomain (chart k),
        x ∈ b.val.image ↔ (convexChart (chart k) x).1 = 0) :
      (cellCenter k).val.1 ≠ 0 := by
    intro hz
    exact centerOffComparison k ((haxis _ (centerInChart k)).mpr hz)
  obtain ⟨ordinaryFilledTrace,ordinaryCells,ordinaryBoundaries,
    ordinaryFilledOnCells,ordinaryCellRange,ordinaryCellFaces,ordinaryCellCone⟩ :=
      meshFillFromEdges ordinaryTimeEdge ordinarySpaceEdge ordinaryEdgeSupport cellCenter
  have ordinaryTimeEdgeFinite (i : Fin (n+1)) (j : Fin (n+2)) :
      (ordinaryTimeEdge i j ⁻¹' b.val.image).Finite := edgeFinite _ _
  have ordinarySpaceEdgeFinite (i : Fin (n+2)) (j : Fin (n+1)) :
      (ordinarySpaceEdge i j ⁻¹' b.val.image).Finite := edgeFinite _ _
  let actualSpaceEdge (i : Fin (n+2)) (j : Fin (n+1)) :=
    if hi : i.val = 0 ∨ i.val = n+1 then (originalBoundaryEdge i hi j).choose
    else ordinarySpaceEdge i j
  have actualSpaceEdgeFinite (i : Fin (n+2)) (j : Fin (n+1)) :
      (actualSpaceEdge i j ⁻¹' b.val.image).Finite := by
    by_cases hi : i.val = 0 ∨ i.val = n+1
    · simpa only [actualSpaceEdge,dif_pos hi] using (originalBoundaryEdge i hi j).choose_spec.1
    · simpa only [actualSpaceEdge,dif_neg hi] using ordinarySpaceEdgeFinite i j
  have actualSpaceEdgeSupport (i : Fin (n+2)) (j : Fin (n+1))
      (k : Fin (n+1) × Fin (n+1))
      (hk : incident k (i,j.castSucc) ∧ incident k (i,j.succ)) :
      Set.range (actualSpaceEdge i j) ⊆ chartDomain (chart k) := by
    by_cases hi : i.val = 0 ∨ i.val = n+1
    · simpa only [actualSpaceEdge,dif_pos hi] using
        (originalBoundaryEdge i hi j).choose_spec.2.1 k hk
    · simpa only [actualSpaceEdge,dif_neg hi,ordinarySpaceEdge] using
        edgeSupport (i,j.castSucc) (i,j.succ) k hk
  have actualBoundarySpaceEdge (i : Fin (n+2)) (hi : i.val = 0 ∨ i.val = n+1)
      (j : Fin (n+1)) (t : Interval) : ∃ u : Interval,
      u.val = (1-t.val)*(phaseGrid j.castSucc).val+t.val*(phaseGrid j.succ).val ∧
      actualSpaceEdge i j t = F (phaseGrid i,u) := by
    simpa only [actualSpaceEdge,dif_pos hi] using
      (originalBoundaryEdge i hi j).choose_spec.2.2 t
  have actualEdgeSupport (k : Fin (n+1) × Fin (n+1)) :
      Set.range (ordinaryTimeEdge k.1 k.2.castSucc) ⊆ chartDomain (chart k) ∧
      Set.range (actualSpaceEdge k.1.succ k.2) ⊆ chartDomain (chart k) ∧
      Set.range (ordinaryTimeEdge k.1 k.2.succ) ⊆ chartDomain (chart k) ∧
      Set.range (actualSpaceEdge k.1.castSucc k.2) ⊆ chartDomain (chart k) :=
    ⟨(ordinaryEdgeSupport k).1,
      actualSpaceEdgeSupport _ _ k ⟨(gridCorners k).2.1,(gridCorners k).2.2.2⟩,
      (ordinaryEdgeSupport k).2.2.1,
      actualSpaceEdgeSupport _ _ k ⟨(gridCorners k).1,(gridCorners k).2.2.1⟩⟩
  obtain ⟨boundaryFilledTrace,boundaryCells,boundaryCellLoops,
    boundaryFilledOnCells,boundaryCellRange,boundaryCellFaces,boundaryCellCone⟩ :=
      meshFillFromEdges ordinaryTimeEdge actualSpaceEdge actualEdgeSupport cellCenter
  choose seamEdge seamSupport seamFinite using sharedSeamEdgeCandidate
  have timeIncidentCell (i : Fin (n+1)) (j : Fin (n+2))
      (k : Fin (n+1) × Fin (n+1))
      (hk : incident k (i.castSucc,j) ∧ incident k (i.succ,j)) : k.1 = i := by
    have h0 := phaseGridStrict.le_iff_le.mp hk.1.1
    have h1 := phaseGridStrict.le_iff_le.mp hk.2.2.1
    apply Fin.ext
    change k.1.val ≤ i.val at h0
    change i.val+1 ≤ k.1.val+1 at h1
    omega
  have actualSeamChoice (i : Fin (n+1)) (j : Fin (n+2))
      (hj : j = 0 ∨ j = Fin.last (n+1)) :
      ∃ p : Path (perturbedVertex (i.castSucc,j)) (perturbedVertex (i.succ,j)),
        (p ⁻¹' b.val.image).Finite ∧
        (∀ k, incident k (i.castSucc,j) ∧ incident k (i.succ,j) →
          Set.range p ⊆ chartDomain (chart k)) ∧
        ∀ t, p t = seamEdge i t := by
    rcases hj with hj | hj
    · subst j
      refine ⟨seamEdge i,seamFinite i,?_,fun _ => rfl⟩
      intro k hk x hx
      have hk1 : k.1 = i := timeIncidentCell i 0 k hk
      have hk2 : k.2 = 0 := by
        have h := phaseGridStrict.le_iff_le.mp hk.1.2.2.1
        apply Fin.ext
        change k.2.val ≤ 0 at h
        change k.2.val = 0
        omega
      obtain ⟨t,rfl⟩ := hx
      have he : k = (i,0) := Prod.ext hk1 hk2
      rw [he]; exact (seamSupport i t).1
    · subst j
      let p := (seamEdge i).cast (hvertexSeam i.castSucc).symm (hvertexSeam i.succ).symm
      refine ⟨p,seamFinite i,?_,fun _ => rfl⟩
      intro k hk x hx
      have hk1 : k.1 = i := timeIncidentCell i _ k hk
      have hk2 : k.2 = Fin.last n := by
        have h := phaseGridStrict.le_iff_le.mp hk.1.2.2.2
        apply Fin.ext
        change n+1 ≤ k.2.val+1 at h
        have hlt := k.2.isLt
        change k.2.val = n
        omega
      obtain ⟨t,rfl⟩ := hx
      have he : k = (i,Fin.last n) := Prod.ext hk1 hk2
      rw [he]; exact (seamSupport i t).2
  let actualTimeEdge (i : Fin (n+1)) (j : Fin (n+2)) :=
    if hj : j = 0 ∨ j = Fin.last (n+1) then (actualSeamChoice i j hj).choose
    else ordinaryTimeEdge i j
  have actualTimeEdgeFinite (i : Fin (n+1)) (j : Fin (n+2)) :
      (actualTimeEdge i j ⁻¹' b.val.image).Finite := by
    by_cases hj : j = 0 ∨ j = Fin.last (n+1)
    · simpa only [actualTimeEdge,dif_pos hj] using (actualSeamChoice i j hj).choose_spec.1
    · simpa only [actualTimeEdge,dif_neg hj] using ordinaryTimeEdgeFinite i j
  have actualTimeEdgeSupport (i : Fin (n+1)) (j : Fin (n+2))
      (k : Fin (n+1) × Fin (n+1))
      (hk : incident k (i.castSucc,j) ∧ incident k (i.succ,j)) :
      Set.range (actualTimeEdge i j) ⊆ chartDomain (chart k) := by
    by_cases hj : j = 0 ∨ j = Fin.last (n+1)
    · simpa only [actualTimeEdge,dif_pos hj] using
        (actualSeamChoice i j hj).choose_spec.2.1 k hk
    · simpa only [actualTimeEdge,dif_neg hj,ordinaryTimeEdge] using
        edgeSupport (i.castSucc,j) (i.succ,j) k hk
  have actualTimeEdgeSeam (i : Fin (n+1)) (t : Interval) :
      actualTimeEdge i 0 t = actualTimeEdge i (Fin.last (n+1)) t := by
    have h0 : (0 : Fin (n+2)) = 0 ∨ (0 : Fin (n+2)) = Fin.last (n+1) := Or.inl rfl
    have h1 : Fin.last (n+1) = (0 : Fin (n+2)) ∨ Fin.last (n+1) = Fin.last (n+1) := Or.inr rfl
    simp only [actualTimeEdge,dif_pos h0,dif_pos h1]
    exact ((actualSeamChoice i 0 h0).choose_spec.2.2 t).trans
      ((actualSeamChoice i (Fin.last (n+1)) h1).choose_spec.2.2 t).symm
  have coherentActualEdges (k : Fin (n+1) × Fin (n+1)) :
      Set.range (actualTimeEdge k.1 k.2.castSucc) ⊆ chartDomain (chart k) ∧
      Set.range (actualSpaceEdge k.1.succ k.2) ⊆ chartDomain (chart k) ∧
      Set.range (actualTimeEdge k.1 k.2.succ) ⊆ chartDomain (chart k) ∧
      Set.range (actualSpaceEdge k.1.castSucc k.2) ⊆ chartDomain (chart k) :=
    ⟨actualTimeEdgeSupport _ _ k ⟨(gridCorners k).1,(gridCorners k).2.1⟩,
      actualSpaceEdgeSupport _ _ k ⟨(gridCorners k).2.1,(gridCorners k).2.2.2⟩,
      actualTimeEdgeSupport _ _ k ⟨(gridCorners k).2.2.1,(gridCorners k).2.2.2⟩,
      actualSpaceEdgeSupport _ _ k ⟨(gridCorners k).1,(gridCorners k).2.2.1⟩⟩
  obtain ⟨regularizedTrace,regularizedCells,regularizedCellLoops,
    regularizedOnCells,regularizedCellRange,regularizedCellFaces,regularizedCellCone⟩ :=
      meshFillFromEdges actualTimeEdge actualSpaceEdge coherentActualEdges cellCenter
  have localCoordinateAffine (j : Fin (n+1)) (t : Interval)
      (h0 : phaseGrid j.castSucc ≤ t) (h1 : t ≤ phaseGrid j.succ) :
      (1-(localCoordinate j t).val)*(phaseGrid j.castSucc).val+
        (localCoordinate j t).val*(phaseGrid j.succ).val = t.val := by
    rw [localCoordinateOnCell j t h0 h1]
    have hgap : (phaseGrid j.succ).val-(phaseGrid j.castSucc).val ≠ 0 :=
      ne_of_gt (sub_pos.mpr (phaseStep j))
    field_simp [hgap]
    <;> ring
  have coordinateZero : localCoordinate 0 0 = 0 := by
    have h0 : phaseGrid (0 : Fin (n+2)) = 0 := by simp [phaseGrid]
    simpa only [show (0 : Fin (n+1)).castSucc = 0 from rfl,h0] using localCoordinateLeft 0
  have lastSucc : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
  have coordinateOne : localCoordinate (Fin.last n) 1 = 1 := by
    have h1 : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
    simpa only [lastSucc,h1] using localCoordinateRight (Fin.last n)
  have regularizedSeam (t : Interval) : regularizedTrace (t,0) = regularizedTrace (t,1) := by
    obtain ⟨i,hi0,hi1⟩ := phaseGridCovers t
    have hb : (t,0) ∈ cellDomain (i,0) := by
      refine ⟨hi0,hi1,?_,?_⟩
      · change phaseGrid (0 : Fin (n+2)) ≤ 0; simp [phaseGrid]
      · exact (phaseGrid (Fin.succ 0)).property.1
    have ht : (t,1) ∈ cellDomain (i,Fin.last n) := by
      refine ⟨hi0,hi1,(phaseGrid (Fin.last n).castSucc).property.2,?_⟩
      change (1 : Interval) ≤ phaseGrid (Fin.last n).succ
      simp [lastSucc,phaseGrid]
    rw [regularizedOnCells (i,0) (t,0) hb,regularizedOnCells (i,Fin.last n) (t,1) ht]
    change regularizedCells (i,0) (localCoordinate i t,localCoordinate 0 0) =
      regularizedCells (i,Fin.last n) (localCoordinate i t,localCoordinate (Fin.last n) 1)
    rw [coordinateZero,coordinateOne,(regularizedCellFaces (i,0) _).1,
      (regularizedCellFaces (i,Fin.last n) _).2.2.1,lastSucc]
    exact actualTimeEdgeSeam i _
  have regularizedOriginalBoundary (t : Interval) :
      regularizedTrace (0,t) = F (0,t) ∧ regularizedTrace (1,t) = F (1,t) := by
    obtain ⟨j,hj0,hj1⟩ := phaseGridCovers t
    have hleft : (0,t) ∈ cellDomain (0,j) := by
      refine ⟨?_,(phaseGrid (Fin.succ 0)).property.1,hj0,hj1⟩
      change phaseGrid (0 : Fin (n+2)) ≤ 0; simp [phaseGrid]
    have hright : (1,t) ∈ cellDomain (Fin.last n,j) := by
      refine ⟨(phaseGrid (Fin.last n).castSucc).property.2,?_,hj0,hj1⟩
      change (1 : Interval) ≤ phaseGrid (Fin.last n).succ
      simp [lastSucc,phaseGrid]
    have hparam {i : Fin (n+2)} (hi : i.val = 0 ∨ i.val = n+1) :
        actualSpaceEdge i j (localCoordinate j t) = F (phaseGrid i,t) := by
      obtain ⟨u,hu,hp⟩ := actualBoundarySpaceEdge i hi j (localCoordinate j t)
      have hut : u = t := Subtype.ext (hu.trans (localCoordinateAffine j t hj0 hj1))
      simpa only [hut] using hp
    constructor
    · rw [regularizedOnCells (0,j) (0,t) hleft]
      change regularizedCells (0,j) (localCoordinate 0 0,localCoordinate j t) = F (0,t)
      rw [coordinateZero,(regularizedCellFaces (0,j) _).2.2.2]
      have he : (0 : Fin (n+1)).castSucc = (0 : Fin (n+2)) := by apply Fin.ext; simp
      rw [he]
      have h := hparam (i := 0) (Or.inl rfl)
      have h0 : phaseGrid (0 : Fin (n+2)) = 0 := by simp [phaseGrid]
      simpa only [h0] using h
    · rw [regularizedOnCells (Fin.last n,j) (1,t) hright]
      change regularizedCells (Fin.last n,j) (localCoordinate (Fin.last n) 1,localCoordinate j t) = F (1,t)
      rw [coordinateOne,(regularizedCellFaces (Fin.last n,j) _).2.1,lastSucc]
      have h := hparam (i := Fin.last (n+1)) (Or.inr rfl)
      simpa [phaseGrid] using h
  let cellSkeletonEvents (k : Fin (n+1) × Fin (n+1)) : Set (Interval × Interval) :=
    {z | (z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1) ∧ regularizedCells k z ∈ b.val.image}
  have cellSkeletonFinite (k : Fin (n+1) × Fin (n+1)) : (cellSkeletonEvents k).Finite := by
    have firstFixed (r : Interval) (p : C(Interval,S)) (hp : (p ⁻¹' b.val.image).Finite)
        (hface : ∀ t, regularizedCells k (r,t) = p t) :
        ({z : Interval × Interval | z.1 = r ∧ regularizedCells k z ∈ b.val.image}).Finite := by
      apply Set.Finite.of_injOn (f := Prod.snd) (t := p ⁻¹' b.val.image) _ _ hp
      · rintro z ⟨hz,hb⟩
        change p z.2 ∈ b.val.image
        rw [← hface z.2,← hz]
        exact hb
      · intro z hz w hw he
        exact Prod.ext (hz.1.trans hw.1.symm) he
    have secondFixed (r : Interval) (p : C(Interval,S)) (hp : (p ⁻¹' b.val.image).Finite)
        (hface : ∀ t, regularizedCells k (t,r) = p t) :
        ({z : Interval × Interval | z.2 = r ∧ regularizedCells k z ∈ b.val.image}).Finite := by
      apply Set.Finite.of_injOn (f := Prod.fst) (t := p ⁻¹' b.val.image) _ _ hp
      · rintro z ⟨hz,hb⟩
        change p z.1 ∈ b.val.image
        rw [← hface z.1,← hz]
        exact hb
      · intro z hz w hw he
        exact Prod.ext he (hz.1.trans hw.1.symm)
    have hl := firstFixed 0 (actualSpaceEdge k.1.castSucc k.2).toContinuousMap
      (actualSpaceEdgeFinite _ _) (fun t => (regularizedCellFaces k t).2.2.2)
    have hr := firstFixed 1 (actualSpaceEdge k.1.succ k.2).toContinuousMap
      (actualSpaceEdgeFinite _ _) (fun t => (regularizedCellFaces k t).2.1)
    have hb := secondFixed 0 (actualTimeEdge k.1 k.2.castSucc).toContinuousMap
      (actualTimeEdgeFinite _ _) (fun t => (regularizedCellFaces k t).1)
    have ht := secondFixed 1 (actualTimeEdge k.1 k.2.succ).toContinuousMap
      (actualTimeEdgeFinite _ _) (fun t => (regularizedCellFaces k t).2.2.1)
    apply (((hl.union hr).union hb).union ht).subset
    rintro z ⟨hz,hB⟩
    rcases hz with hz | hz | hz | hz
    · exact Or.inl (Or.inl (Or.inl ⟨hz,hB⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hz,hB⟩))
    · exact Or.inl (Or.inr ⟨hz,hB⟩)
    · exact Or.inr ⟨hz,hB⟩
  have regularizedBoundaryEventSets :
      ((fun t : Interval => regularizedTrace (0,t)) ⁻¹' b.val.image) =
        ((intervalCurveLoopFrom a.val z₀) ⁻¹' (b.val.image ∩ a.val.image)) ∧
      ((fun t : Interval => regularizedTrace (1,t)) ⁻¹' b.val.image) =
        ((intervalCurveLoopFrom endCurve z₀) ⁻¹' (b.val.image ∩ endCurve.image)) := by
    constructor
    · ext t
      simp only [Set.mem_preimage,(regularizedOriginalBoundary t).1,Fzero]
      constructor
      · intro htB
        exact ⟨htB,⟨z₀ * Circle.exp (2*Real.pi*t.val),rfl⟩⟩
      · exact fun h => h.1
    · ext t
      simp only [Set.mem_preimage,(regularizedOriginalBoundary t).2,Fone]
      constructor
      · intro htB
        exact ⟨htB,⟨z₀ * Circle.exp (2*Real.pi*t.val),rfl⟩⟩
      · exact fun h => h.1
  have regularizedBoundaryFinite :
      ((fun t : Interval => regularizedTrace (0,t)) ⁻¹' b.val.image).Finite ∧
      ((fun t : Interval => regularizedTrace (1,t)) ⁻¹' b.val.image).Finite := by
    rw [regularizedBoundaryEventSets.1,regularizedBoundaryEventSets.2]
    exact ⟨hzeroEvents,honeEvents⟩
  have regularizedBoundaryCountDecrease :
      ((fun t : Interval => regularizedTrace (1,t)) ⁻¹' b.val.image).ncard <
        ((fun t : Interval => regularizedTrace (0,t)) ⁻¹' b.val.image).ncard := by
    rw [regularizedBoundaryEventSets.1,regularizedBoundaryEventSets.2,
      Set.ncard_eq_toFinset_card _ honeEvents,Set.ncard_eq_toFinset_card _ hzeroEvents]
    exact hendpointCounts
  let cellBoundaryEvents (k : Fin (n+1) × Fin (n+1)) :
      Set {z : ℝ × ℝ // ‖z‖ = 1} :=
    {z | regularizedCells k (squareCoordinates ⟨z.val,z.property.le⟩) ∈ b.val.image}
  have cellBoundaryFinite (k : Fin (n+1) × Fin (n+1)) : (cellBoundaryEvents k).Finite := by
    let f : {z : ℝ × ℝ // ‖z‖ = 1} → Interval × Interval :=
      fun z => squareCoordinates ⟨z.val,z.property.le⟩
    apply Set.Finite.of_injOn (f := f) (t := cellSkeletonEvents k) _ _ (cellSkeletonFinite k)
    · intro z hz
      have hn : max |z.val.1| |z.val.2| = 1 := by
        simpa only [Prod.norm_def,Real.norm_eq_abs] using z.property
      have hp : |z.val.1| = 1 ∨ |z.val.2| = 1 := by
        by_cases hx : |z.val.1| = 1
        · exact Or.inl hx
        · right
          by_contra hy
          have hxlt : |z.val.1| < 1 := lt_of_le_of_ne ((le_max_left _ _).trans hn.le) hx
          have hylt : |z.val.2| < 1 := lt_of_le_of_ne ((le_max_right _ _).trans hn.le) hy
          have hh := max_lt hxlt hylt
          rw [hn] at hh
          exact lt_irrefl _ hh
      refine ⟨?_,hz⟩
      rcases hp with hx | hy
      · by_cases hpos : 0 ≤ z.val.1
        · right; left
          apply Subtype.ext
          change (z.val.1+1)/2 = 1
          rw [abs_of_nonneg hpos] at hx
          linarith
        · left
          apply Subtype.ext
          change (z.val.1+1)/2 = 0
          rw [abs_of_neg (lt_of_not_ge hpos)] at hx
          linarith
      · by_cases hpos : 0 ≤ z.val.2
        · right; right; right
          apply Subtype.ext
          change (z.val.2+1)/2 = 1
          rw [abs_of_nonneg hpos] at hy
          linarith
        · right; right; left
          apply Subtype.ext
          change (z.val.2+1)/2 = 0
          rw [abs_of_neg (lt_of_not_ge hpos)] at hy
          linarith
    · intro z hz w hw he
      have hh := squareCoordinates.injective he
      exact Subtype.ext (congrArg (fun a : {z : ℝ × ℝ // ‖z‖ ≤ 1} => a.val) hh)
  have actualCellBoundaryFormula (k : Fin (n+1) × Fin (n+1))
      (z : {z : ℝ × ℝ // ‖z‖ = 1}) :
      convexChart (chart k) (regularizedCells k (squareCoordinates ⟨z.val,z.property.le⟩)) =
        (regularizedCellLoops k z).val := by
    obtain ⟨u,hu,hv⟩ := regularizedCellCone k 0 z
    have he : u = ⟨z.val,z.property.le⟩ := by
      apply Subtype.ext
      simpa using hu
    rw [he] at hv
    simpa using hv
  have actualCellBoundaryAxisZeros (k : Fin (n+1) × Fin (n+1))
      (haxis : ∀ x ∈ chartDomain (chart k),
        x ∈ b.val.image ↔ (convexChart (chart k) x).1 = 0) :
      {z : {z : ℝ × ℝ // ‖z‖ = 1} | (regularizedCellLoops k z).val.1 = 0}.Finite := by
    apply (cellBoundaryFinite k).subset
    intro z hz
    apply (haxis _ (regularizedCellRange k _)).mpr
    rw [actualCellBoundaryFormula]
    exact hz
  have actualConeZeroRadial (k : Fin (n+1) × Fin (n+1))
      (haxis : ∀ x ∈ chartDomain (chart k),
        x ∈ b.val.image ↔ (convexChart (chart k) x).1 = 0) :
      let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k z).val.1 / (cellCenter k).val.1 ≤ 0}
      ∃ q : C(N,Interval × Interval), Function.Injective q ∧
        (∀ z, regularizedCells k (q z) ∈ b.val.image) ∧
        ∀ z, ∃ u : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q z = squareCoordinates u ∧
          u.val = (1 / (1-(regularizedCellLoops k z.val).val.1 /
            (cellCenter k).val.1)) • z.val.val := by
    dsimp only
    let c := (cellCenter k).val.1
    have hc : c ≠ 0 := cellCenterAxisNonzero k haxis
    let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
      (regularizedCellLoops k z).val.1 / c ≤ 0}
    let h : C(N,ℝ) := ⟨fun z => (regularizedCellLoops k z.val).val.1 / c,by fun_prop⟩
    have hnonpos (z : N) : h z ≤ 0 := z.property
    have hden (z : N) : 0 < 1-h z := by linarith [hnonpos z]
    let radius : C(N,Interval) :=
      ⟨fun z => ⟨1/(1-h z),⟨(one_div_pos.mpr (hden z)).le,
        (div_le_one (hden z)).mpr (by linarith [hnonpos z])⟩⟩,
        (continuous_const.div (continuous_const.sub h.continuous)
          (fun z => (hden z).ne')).subtype_mk _⟩
    have hrpos (z : N) : 0 < (radius z).val := one_div_pos.mpr (hden z)
    let radial : C(N,{z : ℝ × ℝ // ‖z‖ ≤ 1}) :=
      ⟨fun z => ⟨(radius z).val • z.val.val,by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hrpos z),z.val.property,mul_one]
        exact (radius z).property.2⟩,by fun_prop⟩
    let q : C(N,Interval × Interval) :=
      ⟨fun z => squareCoordinates (radial z),squareCoordinates.continuous.comp radial.continuous⟩
    have hradnorm (z : N) : ‖(radial z).val‖ = (radius z).val := by
      change ‖(radius z).val • z.val.val‖ = (radius z).val
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hrpos z),z.val.property,mul_one]
    have hinj : Function.Injective q := by
      intro z w he
      have hu : radial z = radial w := squareCoordinates.injective he
      have hr : (radius z).val = (radius w).val := by
        rw [← hradnorm z,← hradnorm w,hu]
      apply Subtype.ext
      apply Subtype.ext
      have heq := congrArg Subtype.val hu
      change (radius z).val • z.val.val = (radius w).val • w.val.val at heq
      rw [← hr] at heq
      exact smul_right_injective (ℝ × ℝ) (ne_of_gt (hrpos z)) heq
    refine ⟨q,hinj,?_,fun z => ⟨radial z,rfl,rfl⟩⟩
    intro z
    let r : Interval := ⟨1-(radius z).val,by constructor <;> linarith [(radius z).property.1,(radius z).property.2]⟩
    obtain ⟨u,hu,hval⟩ := regularizedCellCone k r z.val
    have he : u = radial z := by
      apply Subtype.ext
      rw [hu]
      change (1-(1-(radius z).val)) • z.val.val = (radius z).val • z.val.val
      congr 1
      ring
    rw [he] at hval
    apply (haxis _ (regularizedCellRange k (q z))).mpr
    have hfirst := congrArg Prod.fst hval
    change (convexChart (chart k) (regularizedCells k (q z))).1 =
      (1-r.val)*(regularizedCellLoops k z.val).val.1+r.val*c at hfirst
    have hrval : 1-r.val = (radius z).val := by change 1-(1-(radius z).val) = (radius z).val; ring
    rw [hrval] at hfirst
    rw [hfirst]
    change (1/(1-(regularizedCellLoops k z.val).val.1/c))*
      (regularizedCellLoops k z.val).val.1+
      (1-1/(1-(regularizedCellLoops k z.val).val.1/c))*c = 0
    have hd : 1-(regularizedCellLoops k z.val).val.1/c ≠ 0 := (hden z).ne'
    have hsub : c-(regularizedCellLoops k z.val).val.1 ≠ 0 := by
      intro he
      have heq := sub_eq_zero.mp he
      rw [← heq,div_self hc,sub_self] at hd
      exact hd rfl
    field_simp [hc,hd,hsub]
    <;> ring
  have actualCellZeroSet (k : Fin (n+1) × Fin (n+1))
      (haxis : ∀ x ∈ chartDomain (chart k),
        x ∈ b.val.image ↔ (convexChart (chart k) x).1 = 0) :
      let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k z).val.1 / (cellCenter k).val.1 ≤ 0}
      ∃ q : C(N,Interval × Interval), Function.Injective q ∧
        Set.range q = {x | regularizedCells k x ∈ b.val.image} := by
    dsimp only
    obtain ⟨q,hqi,hqb,hqformula⟩ := actualConeZeroRadial k haxis
    refine ⟨q,hqi,?_⟩
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact hqb z
    · intro hx
      let u := squareCoordinates.symm x
      let c := (cellCenter k).val.1
      have hc : c ≠ 0 := cellCenterAxisNonzero k haxis
      have hxu : x = squareCoordinates u := (squareCoordinates.apply_symm_apply x).symm
      have hu0 : u.val ≠ 0 := by
        intro hu0
        let z0 : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨(1,0),by norm_num [Prod.norm_def]⟩
        obtain ⟨v,hv,hformula⟩ := regularizedCellCone k 1 z0
        have hvu : v = u := by apply Subtype.ext; simpa [hu0] using hv
        rw [hvu] at hformula
        have hz := (haxis _ (regularizedCellRange k x)).mp hx
        rw [hxu] at hz
        have hf : convexChart (chart k) (regularizedCells k (squareCoordinates u)) = cellCenter k := by
          simpa using hformula
        rw [hf] at hz
        exact hc hz
      have hn : 0 < ‖u.val‖ := norm_pos_iff.mpr hu0
      let z : {z : ℝ × ℝ // ‖z‖ = 1} :=
        ⟨‖u.val‖⁻¹ • u.val,by
          rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']⟩
      let r : Interval := ⟨1-‖u.val‖,by constructor <;> linarith [u.property]⟩
      obtain ⟨v,hv,hformula⟩ := regularizedCellCone k r z
      have hvu : v = u := by
        apply Subtype.ext
        rw [hv]
        change (1-(1-‖u.val‖)) • (‖u.val‖⁻¹ • u.val) = u.val
        have he : 1-(1-‖u.val‖) = ‖u.val‖ := by ring
        rw [he,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
      rw [hvu] at hformula
      have hz := (haxis _ (regularizedCellRange k x)).mp hx
      rw [hxu] at hz
      have hfirst := congrArg Prod.fst hformula
      change (convexChart (chart k) (regularizedCells k (squareCoordinates u))).1 =
        (1-r.val)*(regularizedCellLoops k z).val.1+r.val*c at hfirst
      rw [hz] at hfirst
      have hr : 1-r.val = ‖u.val‖ := by change 1-(1-‖u.val‖) = ‖u.val‖; ring
      rw [hr] at hfirst
      have heq : ‖u.val‖*((regularizedCellLoops k z).val.1/c)+(1-‖u.val‖) = 0 := by
        apply (mul_right_cancel₀ hc)
        field_simp [hc]
        nlinarith [hfirst]
      have hneg : (regularizedCellLoops k z).val.1/c ≤ 0 := by
        by_contra hh
        have hhpos : 0 < (regularizedCellLoops k z).val.1/c := lt_of_not_ge hh
        have hprod := mul_pos hn hhpos
        linarith [u.property]
      let zn := (⟨z,hneg⟩ : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k z).val.1/(cellCenter k).val.1 ≤ 0})
      obtain ⟨w,hw,hwrad⟩ := hqformula zn
      have hd : 0 < 1-(regularizedCellLoops k z).val.1/c := by linarith
      have hrad : 1/(1-(regularizedCellLoops k z).val.1/c) = ‖u.val‖ := by
        apply (div_eq_iff hd.ne').mpr
        nlinarith [heq]
      have hwu : w = u := by
        apply Subtype.ext
        rw [hwrad]
        change (1/(1-(regularizedCellLoops k z).val.1/c)) • (‖u.val‖⁻¹ • u.val) = u.val
        rw [hrad,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
      exact ⟨zn,hw.trans ((congrArg squareCoordinates hwu).trans hxu.symm)⟩
  have unitSquareBoundaryCompact : CompactSpace {z : ℝ × ℝ // ‖z‖ = 1} := by
    have hQ : IsCompact {z : ℝ × ℝ | ‖z‖ ≤ 1} := by
      convert (isCompact_Icc.prod isCompact_Icc :
        IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)) using 1
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_prod,Set.mem_Icc,Prod.norm_def,
        Real.norm_eq_abs,max_le_iff,abs_le]
    have hB : IsClosed {z : ℝ × ℝ | ‖z‖ = 1} :=
      isClosed_eq (continuous_fst.norm.max continuous_snd.norm) continuous_const
    exact isCompact_iff_compactSpace.mp
      (hQ.of_isClosed_subset hB (fun z hz => hz.le))
  have actualCellGeometry (k : Fin (n+1) × Fin (n+1)) :
      (∀ x, regularizedCells k x ∉ b.val.image) ∨
      (let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k z).val.1 / (cellCenter k).val.1 ≤ 0}
       ∃ q : C(N,Interval × Interval), Topology.IsEmbedding q ∧
         Set.range q = {x | regularizedCells k x ∈ b.val.image}) := by
    rcases hconvexAxis (chart k) with hdis | haxis
    · left
      intro x hx
      exact Set.disjoint_left.mp hdis (regularizedCellRange k x) hx
    · right
      obtain ⟨q,hqi,hqrange⟩ := actualCellZeroSet k haxis
      letI := unitSquareBoundaryCompact
      have hN : IsClosed {z : {z : ℝ × ℝ // ‖z‖ = 1} |
          (regularizedCellLoops k z).val.1 / (cellCenter k).val.1 ≤ 0} :=
        isClosed_le (by fun_prop) continuous_const
      letI := isCompact_iff_compactSpace.mp hN.isCompact
      exact ⟨q,(q.continuous.isClosedEmbedding hqi).isEmbedding,hqrange⟩
  have finiteZeroMesh (g : C(Interval,ℝ)) (hf : (g ⁻¹' {0}).Finite) :
      ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,
        StrictMono mesh ∧ mesh 0 = 0 ∧ mesh (Fin.last (m+1)) = 1 ∧
        ∀ (i : Fin (m+1)) (t : Interval),
          mesh i.castSucc < t → t < mesh i.succ → g t ≠ 0 := by
    let P : Finset Interval := hf.toFinset ∪ {0,1}
    have h0 : (0 : Interval) ∈ P := Finset.mem_union_right _ (by simp)
    have h1 : (1 : Interval) ∈ P := Finset.mem_union_right _ (by simp)
    have hcard : 2 ≤ P.card := by
      have hsub : ({0,1} : Finset Interval) ⊆ P := Finset.subset_union_right
      have hc := Finset.card_le_card hsub
      norm_num at hc
      exact hc
    let m := P.card-2
    have hm : P.card = m+2 := by dsimp [m]; omega
    let e := P.orderEmbOfFin hm
    have hmono : StrictMono e := e.strictMono
    have hz : e 0 = 0 := by
      have hr : (0 : Interval) ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact h0
      obtain ⟨j,hj⟩ := hr
      exact le_antisymm (hj ▸ hmono.monotone (Fin.zero_le j)) (e 0).property.1
    have ho : e (Fin.last (m+1)) = 1 := by
      have hr : (1 : Interval) ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact h1
      obtain ⟨j,hj⟩ := hr
      exact le_antisymm (e _).property.2 (hj ▸ hmono.monotone (Fin.le_last j))
    refine ⟨m,e,hmono,hz,ho,?_⟩
    intro i t ht0 ht1 hgt
    have htP : t ∈ P := Finset.mem_union_left _ (hf.mem_toFinset.mpr hgt)
    have hr : t ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact htP
    obtain ⟨j,hj⟩ := hr
    have hj0 := hmono.lt_iff_lt.mp (hj ▸ ht0)
    have hj1 := hmono.lt_iff_lt.mp (hj ▸ ht1)
    change i.val < j.val at hj0
    change j.val < i.val+1 at hj1
    omega
  let boundaryFaceRaw : Fin 4 → Interval → ℝ × ℝ := fun i t =>
    if i.val = 0 then (2*t.val-1,-1) else if i.val = 1 then (1,2*t.val-1)
    else if i.val = 2 then (2*t.val-1,1) else (-1,2*t.val-1)
  have faceRawNorm (i : Fin 4) (t : Interval) : ‖boundaryFaceRaw i t‖ = 1 := by
    have ha : |2*t.val-1| ≤ 1 := abs_le.mpr (by constructor <;> linarith [t.property.1,t.property.2])
    fin_cases i <;> simp [boundaryFaceRaw,Prod.norm_def,Real.norm_eq_abs,
      max_eq_left ha,max_eq_right ha]
  let boundaryFace : Fin 4 → C(Interval,{z : ℝ × ℝ // ‖z‖ = 1}) := fun i =>
    ⟨fun t => ⟨boundaryFaceRaw i t,faceRawNorm i t⟩,by
      fin_cases i <;> simp [boundaryFaceRaw] <;> fun_prop⟩
  have actualCornerAdjacentFaces :
      boundaryFace (0 : Fin 4) (0 : Interval) = boundaryFace 3 0 ∧
      boundaryFace (0 : Fin 4) (1 : Interval) = boundaryFace 1 0 ∧
      boundaryFace (2 : Fin 4) (0 : Interval) = boundaryFace 3 1 ∧
      boundaryFace (2 : Fin 4) (1 : Interval) = boundaryFace 1 1 := by
    repeat' constructor
    all_goals apply Subtype.ext
    all_goals norm_num [boundaryFace,boundaryFaceRaw]
  have actualCornerFaceClassification (j : Fin 4) (t : Interval) :
      (boundaryFace j t = boundaryFace 0 0 ↔ j = 0 ∧ t = 0 ∨ j = 3 ∧ t = 0) ∧
      (boundaryFace j t = boundaryFace 0 1 ↔ j = 0 ∧ t = 1 ∨ j = 1 ∧ t = 0) ∧
      (boundaryFace j t = boundaryFace 2 0 ↔ j = 2 ∧ t = 0 ∨ j = 3 ∧ t = 1) ∧
      (boundaryFace j t = boundaryFace 2 1 ↔ j = 2 ∧ t = 1 ∨ j = 1 ∧ t = 1) := by
    have ht0 : t.val = 0 ↔ t = 0 := by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; rw [h]; rfl
    have ht1 : t.val = 1 ↔ t = 1 := by
      constructor
      · intro h; exact Subtype.ext h
      · intro h; rw [h]; rfl
    have boundaryEq (i j : Fin 4) (u v : Interval) :
        boundaryFace i u = boundaryFace j v ↔ boundaryFaceRaw i u = boundaryFaceRaw j v := by
      exact Subtype.ext_iff
    have linear0 : 2*t.val-1 = -1 ↔ t = 0 := by
      constructor
      · intro h; apply Subtype.ext; change t.val = 0; linarith
      · intro h; rw [h]; norm_num
    have linear1 : 2*t.val-1 = 1 ↔ t = 1 := by
      constructor
      · intro h; apply Subtype.ext; change t.val = 1; linarith
      · intro h; rw [h]; norm_num
    refine ⟨?_,?_,?_,?_⟩
    all_goals fin_cases j
    all_goals simp only [boundaryEq,boundaryFaceRaw]
    all_goals norm_num
    all_goals simpa only [linear0,linear1]
  have boundaryFaceInjective (i : Fin 4) : Function.Injective (boundaryFace i) := by
    intro t u he
    have hh := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val) he
    apply Subtype.ext
    fin_cases i
    all_goals simp only [boundaryFace,boundaryFaceRaw,ContinuousMap.coe_mk] at hh
    all_goals first | (have h := congrArg Prod.fst hh; change 2*t.val-1 = 2*u.val-1 at h; linarith)
                    | (have h := congrArg Prod.snd hh; change 2*t.val-1 = 2*u.val-1 at h; linarith)
  have actualFaceZeroMeshes (k : Fin (n+1) × Fin (n+1))
      (haxis : ∀ x ∈ chartDomain (chart k),
        x ∈ b.val.image ↔ (convexChart (chart k) x).1 = 0) (i : Fin 4) :
      ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,
        StrictMono mesh ∧ mesh 0 = 0 ∧ mesh (Fin.last (m+1)) = 1 ∧
        ∀ (j : Fin (m+1)) (t : Interval),
          mesh j.castSucc < t → t < mesh j.succ →
          (regularizedCellLoops k (boundaryFace i t)).val.1 ≠ 0 := by
    let g : C(Interval,ℝ) :=
      ⟨fun t => (regularizedCellLoops k (boundaryFace i t)).val.1,by fun_prop⟩
    have hf0 : (boundaryFace i ⁻¹'
        {z : {z : ℝ × ℝ // ‖z‖ = 1} | (regularizedCellLoops k z).val.1 = 0}).Finite :=
      (actualCellBoundaryAxisZeros k haxis).preimage (boundaryFaceInjective i).injOn
    have hf : (g ⁻¹' {0}).Finite := hf0
    exact finiteZeroMesh g hf
  have boundaryFaceInteriorUnique (i j : Fin 4) (t u : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (he : boundaryFace i t = boundaryFace j u) : i = j := by
    have hf := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val.1) he
    have hs := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val.2) he
    have ht0 : 0 < t.val := ht.1
    have ht1 : t.val < 1 := ht.2
    have hu0 : 0 < u.val := hu.1
    have hu1 : u.val < 1 := hu.2
    fin_cases i <;> fin_cases j
    all_goals first | rfl |
      (simp [boundaryFace,boundaryFaceRaw] at hf hs; exfalso; linarith)
  have boundaryFaceOpenUnique (i j : Fin 4) (t u : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (he : boundaryFace i t = boundaryFace j u) : i = j := by
    have hf := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val.1) he
    have hs := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val.2) he
    have ht0 : 0 < t.val := ht.1
    have ht1 : t.val < 1 := ht.2
    fin_cases i <;> fin_cases j
    all_goals first | rfl |
      (simp [boundaryFace,boundaryFaceRaw] at hf hs; exfalso;
        first | exact (ne_of_gt ht.1) hf | exact (ne_of_gt ht.1) hs |
          exact (ne_of_lt ht.2) hf | exact (ne_of_lt ht.2) hs | linarith)
  have noZeroIntervalSign (g : C(Interval,ℝ)) (x y s : Interval)
      (hxs : x < s) (hsy : s < y) (hs : g s < 0)
      (hn : ∀ t, x < t → t < y → g t ≠ 0) :
      ∀ t ∈ Set.Icc x y, g t ≤ 0 := by
    intro t ht
    by_contra hgt
    have htpos : 0 < g t := lt_of_not_ge hgt
    rcases le_total s t with hst | hts
    · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hst g.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
      have hzt : z < t := lt_of_le_of_ne hz.2 (by
        intro he; rw [he] at hgz; linarith)
      exact hn z (hxs.trans_le hz.1) (hzt.trans_le ht.2) hgz
    · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc' hts g.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
      have htz : t < z := lt_of_le_of_ne hz.1 (by
        intro he; rw [← he] at hgz; linarith)
      exact hn z (ht.1.trans_lt htz) (hz.2.trans_lt hsy) hgz
  have noZeroIntervalEndpointSign (g : C(Interval,ℝ)) (x y mid : Interval)
      (hx : x < mid) (hy : mid < y)
      (hn : ∀ t, x < t → t < y → g t ≠ 0) :
      (g x ≠ 0 → (g mid < 0 ↔ g x < 0)) ∧
      (g y ≠ 0 → (g mid < 0 ↔ g y < 0)) := by
    constructor
    · intro hx0
      constructor
      · intro hm
        exact lt_of_le_of_ne (noZeroIntervalSign g x y mid hx hy hm hn x
          ⟨le_rfl,(hx.trans hy).le⟩) hx0
      · intro hneg
        by_contra hh
        have hp : 0 < g mid := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm (hn mid hx hy))
        obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hx.le g.continuous.continuousOn
          (show (0 : ℝ) ∈ Set.Icc (g x) (g mid) from ⟨hneg.le,hp.le⟩)
        have hzx : x < z := lt_of_le_of_ne hz.1 (by
          intro he; rw [← he] at hgz; exact (ne_of_lt hneg) hgz)
        exact hn z hzx (hz.2.trans_lt hy) hgz
    · intro hy0
      constructor
      · intro hm
        exact lt_of_le_of_ne (noZeroIntervalSign g x y mid hx hy hm hn y
          ⟨(hx.trans hy).le,le_rfl⟩) hy0
      · intro hneg
        by_contra hh
        have hp : 0 < g mid := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm (hn mid hx hy))
        obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc' hy.le g.continuous.continuousOn
          (show (0 : ℝ) ∈ Set.Icc (g y) (g mid) from ⟨hneg.le,hp.le⟩)
        have hzy : z < y := lt_of_le_of_ne hz.2 (by
          intro he; rw [he] at hgz; exact (ne_of_lt hneg) hgz)
        exact hn z (hx.trans_le hz.1) hzy hgz
  let intervalMidpoint (x y : Interval) : Interval := ⟨(x.val+y.val)/2,by
    constructor <;> linarith only [x.property.1,x.property.2,y.property.1,y.property.2]⟩
  have actualNegativeFaceEdges (k : Fin (n+1) × Fin (n+1))
      (haxis : ∀ x ∈ chartDomain (chart k),
        x ∈ b.val.image ↔ (convexChart (chart k) x).1 = 0) (i : Fin 4) :
      let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k z).val.1 / (cellCenter k).val.1 ≤ 0}
      ∃ (m : ℕ) (mesh : Fin (m+2) → Interval) (q : C(N,Interval × Interval)),
        StrictMono mesh ∧ mesh 0 = 0 ∧ mesh (Fin.last (m+1)) = 1 ∧
        (∀ (j : Fin (m+1)) (t : Interval), mesh j.castSucc < t → t < mesh j.succ →
          (regularizedCellLoops k (boundaryFace i t)).val.1 ≠ 0) ∧
        (∀ z : N, (regularizedCellLoops k z.val).val.1 = 0 →
          q z = squareCoordinates ⟨z.val.val,z.val.property.le⟩) ∧
        (∀ z : N, ∃ u : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q z = squareCoordinates u ∧
          u.val = (1/(1-(regularizedCellLoops k z.val).val.1 /
            (cellCenter k).val.1)) • z.val.val) ∧
        ∀ j : Fin (m+1),
          (regularizedCellLoops k (boundaryFace i
            (intervalMidpoint (mesh j.castSucc) (mesh j.succ)))).val.1 /
            (cellCenter k).val.1 < 0 →
          ∃ p : C(Interval,Interval × Interval), Topology.IsEmbedding p ∧
            (∀ t, regularizedCells k (p t) ∈ b.val.image) ∧
            (∀ t, ∃ (r : Interval) (z : N),
              r.val = (1-t.val)*(mesh j.castSucc).val+t.val*(mesh j.succ).val ∧
              z.val = boundaryFace i r ∧ p t = q z ∧
              (t ∈ Set.Ioo (0 : Interval) 1 →
                (regularizedCellLoops k z.val).val.1 / (cellCenter k).val.1 < 0)) ∧
            ∃ zl zr : N, zl.val = boundaryFace i (mesh j.castSucc) ∧
              zr.val = boundaryFace i (mesh j.succ) ∧ p 0 = q zl ∧ p 1 = q zr := by
    dsimp only
    obtain ⟨m,mesh,hm,hzero,hone,hno⟩ := actualFaceZeroMeshes k haxis i
    obtain ⟨q,hqi,hqb,hqformula⟩ := actualConeZeroRadial k haxis
    let c := (cellCenter k).val.1
    have hc : c ≠ 0 := cellCenterAxisNonzero k haxis
    let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
      (regularizedCellLoops k z).val.1/c ≤ 0}
    have hfix (z : N) (hz : (regularizedCellLoops k z.val).val.1 = 0) :
        q z = squareCoordinates ⟨z.val.val,z.val.property.le⟩ := by
      obtain ⟨w,hw,hwrad⟩ := hqformula z
      have he : w = ⟨z.val.val,z.val.property.le⟩ := by
        apply Subtype.ext
        simpa [hz] using hwrad
      exact hw.trans (congrArg squareCoordinates he)
    let g : C(Interval,ℝ) :=
      ⟨fun t => (regularizedCellLoops k (boundaryFace i t)).val.1/c,by fun_prop⟩
    refine ⟨m,mesh,q,hm,hzero,hone,hno,hfix,hqformula,?_⟩
    intro j hneg
    let x := mesh j.castSucc
    let y := mesh j.succ
    have hxy : x < y := hm (by change j.val < j.val+1; omega)
    let s := intervalMidpoint x y
    have hxs : x < s := by change x.val < (x.val+y.val)/2; have hh : x.val < y.val := hxy; linarith only [hh]
    have hsy : s < y := by change (x.val+y.val)/2 < y.val; have hh : x.val < y.val := hxy; linarith only [hh]
    have hn : ∀ t, x < t → t < y → g t ≠ 0 := by
      intro t ht0 ht1
      exact div_ne_zero (hno j t ht0 ht1) hc
    have hsign : ∀ t ∈ Set.Icc x y, g t ≤ 0 := noZeroIntervalSign g x y s hxs hsy hneg hn
    let d : Path x y := {
      toFun := fun t => ⟨(1-t.val)*x.val+t.val*y.val,by
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property.1)
            (mul_nonneg t.property.1 y.property.1)
        · nlinarith only [x.property.1,x.property.2,y.property.1,y.property.2,t.property.1,t.property.2]⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
    have hd (t : Interval) : d t ∈ Set.Icc x y := by
      change x.val ≤ (1-t.val)*x.val+t.val*y.val ∧
        (1-t.val)*x.val+t.val*y.val ≤ y.val
      have hh : x.val < y.val := hxy
      constructor <;> nlinarith only [hh,t.property.1,t.property.2]
    have hdi : Function.Injective d := by
      intro t u he
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      change (1-t.val)*x.val+t.val*y.val = (1-u.val)*x.val+u.val*y.val at hh
      have hlt : x.val < y.val := hxy
      nlinarith
    let f : C(Interval,N) := ⟨fun t => ⟨boundaryFace i (d t),hsign _ (hd t)⟩,by fun_prop⟩
    have hfi : Function.Injective f := by
      intro t u he
      exact hdi (boundaryFaceInjective i (congrArg Subtype.val he))
    let p : C(Interval,Interval × Interval) := q.comp f
    refine ⟨p,(p.continuous.isClosedEmbedding (hqi.comp hfi)).isEmbedding,
      fun t => hqb (f t),?_,f 0,f 1,?_,?_,rfl,rfl⟩
    · intro t
      refine ⟨d t,f t,rfl,rfl,rfl,?_⟩
      intro ht
      have hdt0 : x < d t := by
        change x.val < (1-t.val)*x.val+t.val*y.val
        have hh : x.val < y.val := hxy
        have ht0 : 0 < t.val := ht.1
        nlinarith only [hh,ht0]
      have hdt1 : d t < y := by
        change (1-t.val)*x.val+t.val*y.val < y.val
        have hh : x.val < y.val := hxy
        have ht1 : t.val < 1 := ht.2
        nlinarith only [hh,ht1]
      exact lt_of_le_of_ne (hsign _ (hd t)) (hn _ hdt0 hdt1)
    · change boundaryFace i (d 0) = boundaryFace i x
      rw [d.source]
    · change boundaryFace i (d 1) = boundaryFace i y
      rw [d.target]
  let activeCells := {k : Fin (n+1) × Fin (n+1) |
    ¬ Disjoint (chartDomain (chart k)) b.val.image}
  have activeCellAxis (k : activeCells) : ∀ x ∈ chartDomain (chart k.val),
      x ∈ b.val.image ↔ (convexChart (chart k.val) x).1 = 0 := by
    rcases hconvexAxis (chart k.val) with hdis | haxis
    · exact False.elim (k.property hdis)
    · exact haxis
  have activeFaceConstruction (p : activeCells × Fin 4) :=
    actualNegativeFaceEdges p.1.val (activeCellAxis p.1) p.2
  choose activeFaceSize activeFaceMesh activeFaceRadial activeFaceMono
    activeFaceStart activeFaceEnd activeFaceNoInteriorZero activeFaceBoundaryFix activeFaceRadialFormula
    activeFaceEdges using activeFaceConstruction
  let actualFaceHeight (p : activeCells × Fin 4) : C(Interval,ℝ) :=
    ⟨fun t => (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 /
      (cellCenter p.1.val).val.1,by fun_prop⟩
  have actualCellCornersOff (k : Fin (n+1) × Fin (n+1)) :
      regularizedCells k (0,0) ∉ b.val.image ∧
      regularizedCells k (1,0) ∉ b.val.image ∧
      regularizedCells k (0,1) ∉ b.val.image ∧
      regularizedCells k (1,1) ∉ b.val.image := by
    constructor
    · rw [(regularizedCellFaces k 0).1,(actualTimeEdge k.1 k.2.castSucc).source]
      exact hvertexOff _
    constructor
    · rw [(regularizedCellFaces k 1).1,(actualTimeEdge k.1 k.2.castSucc).target]
      exact hvertexOff _
    constructor
    · rw [(regularizedCellFaces k 0).2.2.1,(actualTimeEdge k.1 k.2.succ).source]
      exact hvertexOff _
    · rw [(regularizedCellFaces k 1).2.2.1,(actualTimeEdge k.1 k.2.succ).target]
      exact hvertexOff _
  have actualFaceEndpointsNonzero (p : activeCells × Fin 4) :
      actualFaceHeight p 0 ≠ 0 ∧ actualFaceHeight p 1 ≠ 0 := by
    have endpointOff (i : Fin 4) (t : Interval) (ht : t = 0 ∨ t = 1) :
        regularizedCells p.1.val (squareCoordinates
          ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩) ∉ b.val.image := by
      obtain ⟨h00,h10,h01,h11⟩ := actualCellCornersOff p.1.val
      rcases ht with rfl | rfl
      all_goals fin_cases i
      all_goals first |
        simpa [squareCoordinates,boundaryFace,boundaryFaceRaw] using h00 |
        simpa [squareCoordinates,boundaryFace,boundaryFaceRaw] using h10 |
        simpa [squareCoordinates,boundaryFace,boundaryFaceRaw] using h01 |
        simpa [squareCoordinates,boundaryFace,boundaryFaceRaw] using h11
    have heightNonzero (t : Interval) (ht : t = 0 ∨ t = 1) :
        (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 ≠ 0 := by
      intro hzero
      apply endpointOff p.2 t ht
      apply (activeCellAxis p.1 _ (regularizedCellRange p.1.val (squareCoordinates
        ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩))).mpr
      rw [actualCellBoundaryFormula]
      exact hzero
    exact ⟨div_ne_zero (heightNonzero 0 (Or.inl rfl))
        (cellCenterAxisNonzero p.1.val (activeCellAxis p.1)),
      div_ne_zero (heightNonzero 1 (Or.inr rfl))
        (cellCenterAxisNonzero p.1.val (activeCellAxis p.1))⟩
  have actualFaceIntervalNoZero (p : activeCells × Fin 4)
      (j : Fin (activeFaceSize p+1)) (t : Interval)
      (hleft : activeFaceMesh p j.castSucc < t) (hright : t < activeFaceMesh p j.succ) :
      actualFaceHeight p t ≠ 0 := by
    exact div_ne_zero (activeFaceNoInteriorZero p j t hleft hright)
      (cellCenterAxisNonzero p.1.val (activeCellAxis p.1))
  have actualFaceInteriorConstantSign (p : activeCells × Fin 4)
      (j : Fin (activeFaceSize p+1)) :
      actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
        (activeFaceMesh p j.succ)) < 0 ↔
      ∀ t ∈ Set.Ioo (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ),
        actualFaceHeight p t < 0 := by
    let x := activeFaceMesh p j.castSucc
    let y := activeFaceMesh p j.succ
    let mid := intervalMidpoint x y
    have hxy : x < y := activeFaceMono p (by change j.val < j.val+1; omega)
    have hx : x < mid := by
      change x.val < (x.val+y.val)/2
      have hh : x.val < y.val := hxy
      linarith
    have hy : mid < y := by
      change (x.val+y.val)/2 < y.val
      have hh : x.val < y.val := hxy
      linarith
    constructor
    · intro hmid t ht
      have hle := noZeroIntervalSign (actualFaceHeight p) x y mid hx hy hmid
        (fun r hr0 hr1 => actualFaceIntervalNoZero p j r hr0 hr1) t ⟨ht.1.le,ht.2.le⟩
      exact lt_of_le_of_ne hle (actualFaceIntervalNoZero p j t ht.1 ht.2)
    · intro h
      exact h mid ⟨hx,hy⟩
  have actualFaceNegativeClosedInterval (p : activeCells × Fin 4)
      (j : Fin (activeFaceSize p+1))
      (hneg : actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
        (activeFaceMesh p j.succ)) < 0) :
      ∀ t ∈ Set.Icc (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ),
        actualFaceHeight p t ≤ 0 := by
    let x := activeFaceMesh p j.castSucc
    let y := activeFaceMesh p j.succ
    have hxy : x.val < y.val := activeFaceMono p (by change j.val < j.val+1; omega)
    have hx : x < intervalMidpoint x y := by change x.val < (x.val+y.val)/2; linarith
    have hy : intervalMidpoint x y < y := by change (x.val+y.val)/2 < y.val; linarith
    exact noZeroIntervalSign (actualFaceHeight p) x y (intervalMidpoint x y) hx hy hneg
      (fun r hr0 hr1 => actualFaceIntervalNoZero p j r hr0 hr1)
  have mesh_brackets (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
      (hend : mesh (Fin.last (m+1)) = 1) (t : Interval) (ht : t < 1) :
      ∃ j : Fin (m+1), mesh j.castSucc ≤ t ∧ t < mesh j.succ := by
    classical
    let P : Finset (Fin (m+2)) := Finset.univ.filter (fun i => mesh i ≤ t)
    have hP : P.Nonempty := ⟨0, by simp [P, hstart]⟩
    let i := P.max' hP
    have hi : mesh i ≤ t := (Finset.mem_filter.mp (P.max'_mem hP)).2
    have hilast : i ≠ Fin.last (m+1) := by
      intro he
      rw [he, hend] at hi
      exact (not_le_of_gt ht) hi
    obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hilast
    refine ⟨j, hj ▸ hi, ?_⟩
    by_contra hn
    have hsucc : j.succ ∈ P := by
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_of_not_gt hn
    have hle := P.le_max' j.succ hsucc
    change j.succ ≤ i at hle
    rw [← hj] at hle
    have hval : j.val + 1 ≤ j.val := hle
    omega
  have mesh_zero_internal (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
      (hend : mesh (Fin.last (m+1)) = 1) (g : Interval → ℝ)
      (hg0 : g 0 ≠ 0) (hg1 : g 1 ≠ 0)
      (hgap : ∀ (j : Fin (m+1)) (t : Interval),
        mesh j.castSucc < t → t < mesh j.succ → g t ≠ 0)
      (t : Interval) (ht : g t = 0) :
      ∃ i : Fin (m+2), mesh i = t ∧ i ≠ 0 ∧ i ≠ Fin.last (m+1) := by
    have ht0 : t ≠ 0 := by intro he; exact hg0 (he ▸ ht)
    have ht1 : t < 1 := lt_of_le_of_ne t.property.2 (by
      intro he
      apply hg1
      exact he ▸ ht)
    obtain ⟨j,hlo,hhi⟩ := mesh_brackets m mesh hmono hstart hend t ht1
    have he : mesh j.castSucc = t := by
      by_contra hn
      exact hgap j t (lt_of_le_of_ne hlo hn) hhi ht
    refine ⟨j.castSucc,he,?_,?_⟩
    · intro hi
      rw [hi,hstart] at he
      exact ht0 he.symm
    · exact Fin.castSucc_ne_last j
  have mesh_zero_adjacent (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (hstart : mesh 0 = 0)
      (hend : mesh (Fin.last (m+1)) = 1) (g : Interval → ℝ)
      (hg0 : g 0 ≠ 0) (hg1 : g 1 ≠ 0)
      (hgap : ∀ (j : Fin (m+1)) (t : Interval),
        mesh j.castSucc < t → t < mesh j.succ → g t ≠ 0)
      (t : Interval) (ht : g t = 0) :
      ∃ l r : Fin (m+1), mesh l.succ = t ∧ mesh r.castSucc = t ∧
        l.val+1 = r.val ∧
        (∀ j : Fin (m+1), mesh j.succ = t ↔ j = l) ∧
        (∀ j : Fin (m+1), mesh j.castSucc = t ↔ j = r) := by
    obtain ⟨i,hi,hi0,hi1⟩ := mesh_zero_internal m mesh hmono hstart hend g hg0 hg1 hgap t ht
    obtain ⟨l,hl⟩ := Fin.exists_succ_eq.mpr hi0
    obtain ⟨r,hr⟩ := Fin.exists_castSucc_eq.mpr hi1
    refine ⟨l,r,hl ▸ hi,hr ▸ hi,?_,?_,?_⟩
    · have he := congrArg Fin.val (hl.trans hr.symm)
      exact he
    · intro j
      constructor
      · intro hj
        apply Fin.succ_injective
        apply hmono.injective
        exact hj.trans (hl ▸ hi).symm
      · rintro rfl
        exact hl ▸ hi
    · intro j
      constructor
      · intro hj
        apply Fin.castSucc_injective
        apply hmono.injective
        exact hj.trans (hr ▸ hi).symm
      · rintro rfl
        exact hr ▸ hi
  have actualFaceZeroIsInternalMesh (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0) :
      ∃ i : Fin (activeFaceSize p+2), activeFaceMesh p i = t ∧
        i ≠ 0 ∧ i ≠ Fin.last (activeFaceSize p+1) := by
    exact mesh_zero_internal (activeFaceSize p) (activeFaceMesh p)
      (activeFaceMono p) (activeFaceStart p) (activeFaceEnd p)
      (actualFaceHeight p) (actualFaceEndpointsNonzero p).1
      (actualFaceEndpointsNonzero p).2
      (fun j r hr0 hr1 => actualFaceIntervalNoZero p j r hr0 hr1) t ht
  have actualFaceEndpointGerms (p : activeCells × Fin 4)
      (j : Fin (activeFaceSize p+1)) :
      (actualFaceHeight p (activeFaceMesh p j.castSucc) ≠ 0 →
        (actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ↔
          actualFaceHeight p (activeFaceMesh p j.castSucc) < 0)) ∧
      (actualFaceHeight p (activeFaceMesh p j.succ) ≠ 0 →
        (actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ↔
          actualFaceHeight p (activeFaceMesh p j.succ) < 0)) := by
    let x := activeFaceMesh p j.castSucc
    let y := activeFaceMesh p j.succ
    have hxy : x.val < y.val := activeFaceMono p (by change j.val < j.val+1; omega)
    have hx : x < intervalMidpoint x y := by change x.val < (x.val+y.val)/2; linarith
    have hy : intervalMidpoint x y < y := by change (x.val+y.val)/2 < y.val; linarith
    exact noZeroIntervalEndpointSign (actualFaceHeight p) x y (intervalMidpoint x y) hx hy
      (fun r hr0 hr1 => actualFaceIntervalNoZero p j r hr0 hr1)
  -- All four selected radial maps in a cell are the same map.  The face
  -- choice affects only the finite subdivision, never the cone geometry.
  let actualFaceIncidenceCount (p : activeCells × Fin 4) (u : Interval) : ℕ :=
    (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
      actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0 ∧
      activeFaceMesh p j.succ = u)).card +
    (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
      actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0 ∧
      activeFaceMesh p j.castSucc = u)).card
  have actualTimeAdjacentFaceIncidencesEven (k l : activeCells)
      (htime : k.val.1.succ = l.val.1.castSucc) (hphase : k.val.2 = l.val.2)
      (u : Interval) (hroot : actualFaceHeight (k,1) u = 0) :
      Even (actualFaceIncidenceCount (k,1) u + actualFaceIncidenceCount (l,3) u) := by
    let γ : C(Interval,S) := (actualSpaceEdge k.val.1.succ k.val.2).toContinuousMap
    have hcoordk (q : Interval) : squareCoordinates
        ⟨(boundaryFace 1 q).val,(boundaryFace 1 q).property.le⟩ = (1,q) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hcoordl (q : Interval) : squareCoordinates
        ⟨(boundaryFace 3 q).val,(boundaryFace 3 q).property.le⟩ = (0,q) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have htracek (q : Interval) : γ q = regularizedCells k.val
        (squareCoordinates ⟨(boundaryFace 1 q).val,(boundaryFace 1 q).property.le⟩) := by
      rw [hcoordk,(regularizedCellFaces k.val q).2.1]
      rfl
    have htracel (q : Interval) : γ q = regularizedCells l.val
        (squareCoordinates ⟨(boundaryFace 3 q).val,(boundaryFace 3 q).property.le⟩) := by
      rw [hcoordl,(regularizedCellFaces l.val q).2.2.2]
      change actualSpaceEdge k.val.1.succ k.val.2 q = actualSpaceEdge l.val.1.castSucc l.val.2 q
      rw [htime,hphase]
    have hpC : γ u ∈ chartDomain (chart k.val) := by
      rw [htracek u]
      exact regularizedCellRange k.val _
    have hpD : γ u ∈ chartDomain (chart l.val) := by
      rw [htracel u]
      exact regularizedCellRange l.val _
    have hn : (regularizedCellLoops k.val (boundaryFace 1 u)).val.1 = 0 :=
      (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hb : γ u ∈ b.val.image := by
      apply (activeCellAxis k _ hpC).mpr
      rw [htracek u,actualCellBoundaryFormula]
      exact hn
    have hu0 : u ≠ 0 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,1)).1 (he ▸ hroot)
    have hu1 : u ≠ 1 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,1)).2 (he ▸ hroot)
    have huI : u ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne u.property.1 hu0.symm,lt_of_le_of_ne u.property.2 hu1⟩
    have hnormalK (q : Interval) : actualFaceHeight (k,1) q =
        (convexChart (chart k.val) (γ q)).1 / (cellCenter k.val).val.1 := by
      change (regularizedCellLoops k.val (boundaryFace 1 q)).val.1 /
        (cellCenter k.val).val.1 = _
      rw [htracek q,actualCellBoundaryFormula]
    have hnormalL (q : Interval) : actualFaceHeight (l,3) q =
        (convexChart (chart l.val) (γ q)).1 / (cellCenter l.val).val.1 := by
      change (regularizedCellLoops l.val (boundaryFace 3 q)).val.1 /
        (cellCenter l.val).val.1 = _
      rw [htracel q,actualCellBoundaryFormula]
    have hactual := actual_shared_mesh_root_incidence_parity b.val γ u huI hb
      (convexChart (chart k.val)) (convexChart (chart l.val)) hpC hpD
      (activeCellAxis k) (activeCellAxis l)
      (actualFaceHeight (k,1)) (actualFaceHeight (l,3))
      (cellCenter k.val).val.1 (cellCenter l.val).val.1
      (cellCenterAxisNonzero k.val (activeCellAxis k))
      (cellCenterAxisNonzero l.val (activeCellAxis l)) hnormalK hnormalL
      (activeFaceSize (k,1)) (activeFaceSize (l,3))
      (activeFaceMesh (k,1)) (activeFaceMesh (l,3))
      (activeFaceMono (k,1)) (activeFaceMono (l,3))
      (activeFaceStart (k,1)) (activeFaceStart (l,3))
      (activeFaceEnd (k,1)) (activeFaceEnd (l,3))
      (actualFaceEndpointsNonzero (k,1)).1 (actualFaceEndpointsNonzero (k,1)).2
      (actualFaceEndpointsNonzero (l,3)).1 (actualFaceEndpointsNonzero (l,3)).2
      (fun j t ht0 ht1 => actualFaceIntervalNoZero (k,1) j t ht0 ht1)
      (fun j t ht0 ht1 => actualFaceIntervalNoZero (l,3) j t ht0 ht1)
    change Odd (actualFaceIncidenceCount (k,1) u) ↔
      Odd (actualFaceIncidenceCount (l,3) u) at hactual
    exact Nat.even_add'.mpr hactual
  have actualPhaseAdjacentFaceIncidencesEven (k l : activeCells)
      (htime : k.val.1 = l.val.1) (hphase : k.val.2.succ = l.val.2.castSucc)
      (u : Interval) (hroot : actualFaceHeight (k,2) u = 0) :
      Even (actualFaceIncidenceCount (k,2) u + actualFaceIncidenceCount (l,0) u) := by
    let γ : C(Interval,S) := (actualTimeEdge k.val.1 k.val.2.succ).toContinuousMap
    have hcoordk (q : Interval) : squareCoordinates
        ⟨(boundaryFace 2 q).val,(boundaryFace 2 q).property.le⟩ = (q,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hcoordl (q : Interval) : squareCoordinates
        ⟨(boundaryFace 0 q).val,(boundaryFace 0 q).property.le⟩ = (q,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have htracek (q : Interval) : γ q = regularizedCells k.val
        (squareCoordinates ⟨(boundaryFace 2 q).val,(boundaryFace 2 q).property.le⟩) := by
      rw [hcoordk,(regularizedCellFaces k.val q).2.2.1]
      rfl
    have htracel (q : Interval) : γ q = regularizedCells l.val
        (squareCoordinates ⟨(boundaryFace 0 q).val,(boundaryFace 0 q).property.le⟩) := by
      rw [hcoordl,(regularizedCellFaces l.val q).1]
      change actualTimeEdge k.val.1 k.val.2.succ q = actualTimeEdge l.val.1 l.val.2.castSucc q
      rw [htime,hphase]
    have hpC : γ u ∈ chartDomain (chart k.val) := by
      rw [htracek u]
      exact regularizedCellRange k.val _
    have hpD : γ u ∈ chartDomain (chart l.val) := by
      rw [htracel u]
      exact regularizedCellRange l.val _
    have hn : (regularizedCellLoops k.val (boundaryFace 2 u)).val.1 = 0 :=
      (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hb : γ u ∈ b.val.image := by
      apply (activeCellAxis k _ hpC).mpr
      rw [htracek u,actualCellBoundaryFormula]
      exact hn
    have hu0 : u ≠ 0 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,2)).1 (he ▸ hroot)
    have hu1 : u ≠ 1 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,2)).2 (he ▸ hroot)
    have huI : u ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne u.property.1 hu0.symm,lt_of_le_of_ne u.property.2 hu1⟩
    have hnormalK (q : Interval) : actualFaceHeight (k,2) q =
        (convexChart (chart k.val) (γ q)).1 / (cellCenter k.val).val.1 := by
      change (regularizedCellLoops k.val (boundaryFace 2 q)).val.1 /
        (cellCenter k.val).val.1 = _
      rw [htracek q,actualCellBoundaryFormula]
    have hnormalL (q : Interval) : actualFaceHeight (l,0) q =
        (convexChart (chart l.val) (γ q)).1 / (cellCenter l.val).val.1 := by
      change (regularizedCellLoops l.val (boundaryFace 0 q)).val.1 /
        (cellCenter l.val).val.1 = _
      rw [htracel q,actualCellBoundaryFormula]
    have hactual := actual_shared_mesh_root_incidence_parity b.val γ u huI hb
      (convexChart (chart k.val)) (convexChart (chart l.val)) hpC hpD
      (activeCellAxis k) (activeCellAxis l)
      (actualFaceHeight (k,2)) (actualFaceHeight (l,0))
      (cellCenter k.val).val.1 (cellCenter l.val).val.1
      (cellCenterAxisNonzero k.val (activeCellAxis k))
      (cellCenterAxisNonzero l.val (activeCellAxis l)) hnormalK hnormalL
      (activeFaceSize (k,2)) (activeFaceSize (l,0))
      (activeFaceMesh (k,2)) (activeFaceMesh (l,0))
      (activeFaceMono (k,2)) (activeFaceMono (l,0))
      (activeFaceStart (k,2)) (activeFaceStart (l,0))
      (activeFaceEnd (k,2)) (activeFaceEnd (l,0))
      (actualFaceEndpointsNonzero (k,2)).1 (actualFaceEndpointsNonzero (k,2)).2
      (actualFaceEndpointsNonzero (l,0)).1 (actualFaceEndpointsNonzero (l,0)).2
      (fun j t ht0 ht1 => actualFaceIntervalNoZero (k,2) j t ht0 ht1)
      (fun j t ht0 ht1 => actualFaceIntervalNoZero (l,0) j t ht0 ht1)
    change Odd (actualFaceIncidenceCount (k,2) u) ↔
      Odd (actualFaceIncidenceCount (l,0) u) at hactual
    exact Nat.even_add'.mpr hactual
  have actualSeamFaceIncidencesEven (k l : activeCells)
      (htime : k.val.1 = l.val.1) (hkphase : k.val.2 = 0)
      (hlphase : l.val.2 = Fin.last n)
      (u : Interval) (hroot : actualFaceHeight (k,0) u = 0) :
      Even (actualFaceIncidenceCount (k,0) u + actualFaceIncidenceCount (l,2) u) := by
    let γ : C(Interval,S) := (actualTimeEdge k.val.1 0).toContinuousMap
    have hcoordk (q : Interval) : squareCoordinates
        ⟨(boundaryFace 0 q).val,(boundaryFace 0 q).property.le⟩ = (q,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hcoordl (q : Interval) : squareCoordinates
        ⟨(boundaryFace 2 q).val,(boundaryFace 2 q).property.le⟩ = (q,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have htracek (q : Interval) : γ q = regularizedCells k.val
        (squareCoordinates ⟨(boundaryFace 0 q).val,(boundaryFace 0 q).property.le⟩) := by
      rw [hcoordk,(regularizedCellFaces k.val q).1]
      change actualTimeEdge k.val.1 0 q = actualTimeEdge k.val.1 k.val.2.castSucc q
      have hphasezero : k.val.2.castSucc = (0 : Fin (n+2)) := by
        apply Fin.ext
        exact congrArg (fun j : Fin (n+1) => j.val) hkphase
      exact congrArg (fun j : Fin (n+2) => actualTimeEdge k.val.1 j q) hphasezero.symm
    have htracel (q : Interval) : γ q = regularizedCells l.val
        (squareCoordinates ⟨(boundaryFace 2 q).val,(boundaryFace 2 q).property.le⟩) := by
      rw [hcoordl,(regularizedCellFaces l.val q).2.2.1]
      change actualTimeEdge k.val.1 0 q = actualTimeEdge l.val.1 l.val.2.succ q
      rw [htime,hlphase,lastSucc]
      exact actualTimeEdgeSeam l.val.1 q
    have hpC : γ u ∈ chartDomain (chart k.val) := by
      rw [htracek u]
      exact regularizedCellRange k.val _
    have hpD : γ u ∈ chartDomain (chart l.val) := by
      rw [htracel u]
      exact regularizedCellRange l.val _
    have hn : (regularizedCellLoops k.val (boundaryFace 0 u)).val.1 = 0 :=
      (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hb : γ u ∈ b.val.image := by
      apply (activeCellAxis k _ hpC).mpr
      rw [htracek u,actualCellBoundaryFormula]
      exact hn
    have hu0 : u ≠ 0 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,0)).1 (he ▸ hroot)
    have hu1 : u ≠ 1 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,0)).2 (he ▸ hroot)
    have huI : u ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne u.property.1 hu0.symm,lt_of_le_of_ne u.property.2 hu1⟩
    have hnormalK (q : Interval) : actualFaceHeight (k,0) q =
        (convexChart (chart k.val) (γ q)).1 / (cellCenter k.val).val.1 := by
      change (regularizedCellLoops k.val (boundaryFace 0 q)).val.1 /
        (cellCenter k.val).val.1 = _
      rw [htracek q,actualCellBoundaryFormula]
    have hnormalL (q : Interval) : actualFaceHeight (l,2) q =
        (convexChart (chart l.val) (γ q)).1 / (cellCenter l.val).val.1 := by
      change (regularizedCellLoops l.val (boundaryFace 2 q)).val.1 /
        (cellCenter l.val).val.1 = _
      rw [htracel q,actualCellBoundaryFormula]
    have hactual := actual_shared_mesh_root_incidence_parity b.val γ u huI hb
      (convexChart (chart k.val)) (convexChart (chart l.val)) hpC hpD
      (activeCellAxis k) (activeCellAxis l)
      (actualFaceHeight (k,0)) (actualFaceHeight (l,2))
      (cellCenter k.val).val.1 (cellCenter l.val).val.1
      (cellCenterAxisNonzero k.val (activeCellAxis k))
      (cellCenterAxisNonzero l.val (activeCellAxis l)) hnormalK hnormalL
      (activeFaceSize (k,0)) (activeFaceSize (l,2))
      (activeFaceMesh (k,0)) (activeFaceMesh (l,2))
      (activeFaceMono (k,0)) (activeFaceMono (l,2))
      (activeFaceStart (k,0)) (activeFaceStart (l,2))
      (activeFaceEnd (k,0)) (activeFaceEnd (l,2))
      (actualFaceEndpointsNonzero (k,0)).1 (actualFaceEndpointsNonzero (k,0)).2
      (actualFaceEndpointsNonzero (l,2)).1 (actualFaceEndpointsNonzero (l,2)).2
      (fun j t ht0 ht1 => actualFaceIntervalNoZero (k,0) j t ht0 ht1)
      (fun j t ht0 ht1 => actualFaceIntervalNoZero (l,2) j t ht0 ht1)
    change Odd (actualFaceIncidenceCount (k,0) u) ↔
      Odd (actualFaceIncidenceCount (l,2) u) at hactual
    exact Nat.even_add'.mpr hactual
  have activeFaceRadialAgreement (k : activeCells) (i j : Fin 4)
      (z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k.val z).val.1 / (cellCenter k.val).val.1 ≤ 0}) :
      activeFaceRadial (k,i) z = activeFaceRadial (k,j) z := by
    obtain ⟨u,hu,huf⟩ := activeFaceRadialFormula (k,i) z
    obtain ⟨v,hv,hvf⟩ := activeFaceRadialFormula (k,j) z
    have huv : u = v := Subtype.ext (huf.trans hvf.symm)
    exact hu.trans ((congrArg squareCoordinates huv).trans hv.symm)
  have activeFaceRadialInjective (k : activeCells) (i : Fin 4) :
      Function.Injective (activeFaceRadial (k,i)) := by
    obtain ⟨q,hqi,hqb,hqf⟩ := actualConeZeroRadial k.val (activeCellAxis k)
    have hagree (z) : activeFaceRadial (k,i) z = q z := by
      obtain ⟨u,hu,huf⟩ := activeFaceRadialFormula (k,i) z
      obtain ⟨v,hv,hvf⟩ := hqf z
      have huv : u = v := Subtype.ext (huf.trans hvf.symm)
      exact hu.trans ((congrArg squareCoordinates huv).trans hv.symm)
    intro z w he
    apply hqi
    exact (hagree z).symm.trans (he.trans (hagree w))
  -- Negative selected radial directions produce actual zero vertices in the
  -- open cell, so no neighboring cell can contribute to their endpoint fiber.
  have actualNegativeRadialCoordinates (p : activeCells × Fin 4)
      (z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops p.1.val z).val.1 / (cellCenter p.1.val).val.1 ≤ 0})
      (hneg : (regularizedCellLoops p.1.val z.val).val.1 / (cellCenter p.1.val).val.1 < 0) :
      (activeFaceRadial p z).1 ∈ Set.Ioo (0 : Interval) 1 ∧
        (activeFaceRadial p z).2 ∈ Set.Ioo (0 : Interval) 1 := by
    obtain ⟨w,hw,hwf⟩ := activeFaceRadialFormula p z
    have hd : 0 < 1-(regularizedCellLoops p.1.val z.val).val.1 /
        (cellCenter p.1.val).val.1 := by linarith only [hneg]
    have hpos : 0 < 1/(1-(regularizedCellLoops p.1.val z.val).val.1 /
        (cellCenter p.1.val).val.1) := div_pos zero_lt_one hd
    have hlt : 1/(1-(regularizedCellLoops p.1.val z.val).val.1 /
        (cellCenter p.1.val).val.1) < 1 := (div_lt_one hd).mpr (by linarith only [hneg])
    have hn : ‖w.val‖ < 1 := by
      rw [hwf,norm_smul,Real.norm_eq_abs,abs_of_pos hpos,z.val.property,mul_one]
      exact hlt
    rw [hw]
    have hb : -1 < w.val.1 ∧ w.val.1 < 1 ∧ -1 < w.val.2 ∧ w.val.2 < 1 := by
      have hh : |w.val.1| < 1 ∧ |w.val.2| < 1 := by
        simpa only [Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using hn
      exact ⟨(abs_lt.mp hh.1).1,(abs_lt.mp hh.1).2,
        (abs_lt.mp hh.2).1,(abs_lt.mp hh.2).2⟩
    change (0 < (w.val.1+1)/2 ∧ (w.val.1+1)/2 < 1) ∧
      (0 < (w.val.2+1)/2 ∧ (w.val.2+1)/2 < 1)
    constructor <;> constructor <;> linarith only [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  let zeroEdgeIndex := Σ p : activeCells × Fin 4,
    {j : Fin (activeFaceSize p+1) |
      (regularizedCellLoops p.1.val (boundaryFace p.2
        (intervalMidpoint (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)))).val.1 /
        (cellCenter p.1.val).val.1 < 0}
  have zeroEdgeIndexFinite : Finite zeroEdgeIndex := inferInstance
  have selectedZeroEdge (e : zeroEdgeIndex) := activeFaceEdges e.1 e.2.val e.2.property
  choose zeroEdge zeroEdgeEmbedding zeroEdgeOnComparison zeroParameter zeroLeft zeroRight
    zeroLeftBoundary zeroRightBoundary zeroSource zeroTarget using selectedZeroEdge
  -- Actual endpoint incidence, with no side/parity certificate assumed.
  -- The cone's embedding reduces equality of actual geometric endpoints to
  -- equality of their actual face-mesh parameters.
  have zeroLeftEndpointOnSameFace (e : zeroEdgeIndex)
      (t : Interval)
      (z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops e.1.1.val z).val.1 /
          (cellCenter e.1.1.val).val.1 ≤ 0})
      (hz : z.val = boundaryFace e.1.2 t) :
      zeroEdge e 0 = activeFaceRadial e.1 z ↔
        activeFaceMesh e.1 e.2.val.castSucc = t := by
    rw [zeroSource e]
    constructor
    · intro h
      have hrad := activeFaceRadialInjective e.1.1 e.1.2 h
      have hface := congrArg Subtype.val hrad
      rw [zeroLeftBoundary e, hz] at hface
      exact boundaryFaceInjective e.1.2 hface
    · intro h
      apply congrArg (activeFaceRadial e.1)
      apply Subtype.ext
      rw [zeroLeftBoundary e, hz, h]
  have zeroRightEndpointOnSameFace (e : zeroEdgeIndex)
      (t : Interval)
      (z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops e.1.1.val z).val.1 /
          (cellCenter e.1.1.val).val.1 ≤ 0})
      (hz : z.val = boundaryFace e.1.2 t) :
      zeroEdge e 1 = activeFaceRadial e.1 z ↔
        activeFaceMesh e.1 e.2.val.succ = t := by
    rw [zeroTarget e]
    constructor
    · intro h
      have hrad := activeFaceRadialInjective e.1.1 e.1.2 h
      have hface := congrArg Subtype.val hrad
      rw [zeroRightBoundary e, hz] at hface
      exact boundaryFaceInjective e.1.2 hface
    · intro h
      apply congrArg (activeFaceRadial e.1)
      apply Subtype.ext
      rw [zeroRightBoundary e, hz, h]
  -- An endpoint on an open root-face cannot come from another face of the
  -- same actual cell. This isolates the actual Sigma-index incidence fiber.
  -- Actual off-axis mesh nodes produce both adjacent cone edges; these are
  -- the interior-cell subdivision vertices in the global endpoint census.
  have actualNegativeMeshFaceIncidenceTwo (p : activeCells × Fin 4)
      (i : Fin (activeFaceSize p+2)) (hi0 : i ≠ 0)
      (hi1 : i ≠ Fin.last (activeFaceSize p+1))
      (hneg : actualFaceHeight p (activeFaceMesh p i) < 0) :
      actualFaceIncidenceCount p (activeFaceMesh p i) = 2 := by
    obtain ⟨l,hl⟩ := Fin.exists_succ_eq.mpr hi0
    obtain ⟨r,hr⟩ := Fin.exists_castSucc_eq.mpr hi1
    have hgl : actualFaceHeight p (activeFaceMesh p l.succ) < 0 := hl.symm ▸ hneg
    have hgr : actualFaceHeight p (activeFaceMesh p r.castSucc) < 0 := hr.symm ▸ hneg
    have hnl := ((actualFaceEndpointGerms p l).2 (ne_of_lt hgl)).mpr hgl
    have hnr := ((actualFaceEndpointGerms p r).1 (ne_of_lt hgr)).mpr hgr
    have hlu (j : Fin (activeFaceSize p+1)) :
        activeFaceMesh p j.succ = activeFaceMesh p i ↔ j = l := by
      constructor
      · intro he
        apply Fin.succ_injective
        apply (activeFaceMono p).injective
        exact he.trans (congrArg (activeFaceMesh p) hl).symm
      · rintro rfl
        exact congrArg (activeFaceMesh p) hl
    have hru (j : Fin (activeFaceSize p+1)) :
        activeFaceMesh p j.castSucc = activeFaceMesh p i ↔ j = r := by
      constructor
      · intro he
        apply Fin.castSucc_injective
        apply (activeFaceMono p).injective
        exact he.trans (congrArg (activeFaceMesh p) hr).symm
      · rintro rfl
        exact congrArg (activeFaceMesh p) hr
    have hL : Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0 ∧
          activeFaceMesh p j.succ = activeFaceMesh p i) = {l} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hlu j]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hnl,rfl⟩
    have hR : Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0 ∧
          activeFaceMesh p j.castSucc = activeFaceMesh p i) = {r} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hru j]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hnr,rfl⟩
    change (Finset.univ.filter _).card + (Finset.univ.filter _).card = 2
    rw [hL,hR]
    norm_num
  have actualNegativeFaceStartCount (p : activeCells × Fin 4)
      (hneg : actualFaceHeight p 0 < 0) :
      (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.castSucc = 0)).card = 1 ∧
      (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.succ = 0)).card = 0 := by
    have hzero : activeFaceMesh p (0 : Fin (activeFaceSize p+1)).castSucc = 0 := activeFaceStart p
    have hmneg : actualFaceHeight p (intervalMidpoint
        (activeFaceMesh p (0 : Fin (activeFaceSize p+1)).castSucc)
        (activeFaceMesh p (0 : Fin (activeFaceSize p+1)).succ)) < 0 :=
      ((actualFaceEndpointGerms p 0).1 (by rw [hzero]; exact ne_of_lt hneg)).mpr
        (by rwa [hzero])
    have hstartunique (j : Fin (activeFaceSize p+1)) :
        activeFaceMesh p j.castSucc = 0 ↔ j = 0 := by
      rw [←activeFaceStart p]
      constructor
      · intro he
        apply Fin.ext
        exact congrArg (fun i : Fin (activeFaceSize p+2) => i.val)
          ((activeFaceMono p).injective he)
      · rintro rfl
        rfl
    have hsucnot (j : Fin (activeFaceSize p+1)) : activeFaceMesh p j.succ ≠ 0 := by
      intro he
      have hi := (activeFaceMono p).injective (he.trans (activeFaceStart p).symm)
      exact Fin.succ_ne_zero j hi
    have hL : Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.castSucc = 0) = {0} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hstartunique j]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hmneg,rfl⟩
    have hR : Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.succ = 0) = ∅ := by
      ext j
      simp [hsucnot j]
    rw [hL,hR]
    simp
  have actualNegativeFaceEndCount (p : activeCells × Fin 4)
      (hneg : actualFaceHeight p 1 < 0) :
      (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.succ = 1)).card = 1 ∧
      (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.castSucc = 1)).card = 0 := by
    let j₁ := Fin.last (activeFaceSize p)
    have hlast : j₁.succ = Fin.last (activeFaceSize p+1) := by apply Fin.ext; rfl
    have hend : activeFaceMesh p j₁.succ = 1 := hlast ▸ activeFaceEnd p
    have hmneg : actualFaceHeight p (intervalMidpoint
        (activeFaceMesh p j₁.castSucc) (activeFaceMesh p j₁.succ)) < 0 :=
      ((actualFaceEndpointGerms p j₁).2 (by rw [hend]; exact ne_of_lt hneg)).mpr
        (by rwa [hend])
    have hendunique (j : Fin (activeFaceSize p+1)) :
        activeFaceMesh p j.succ = 1 ↔ j = j₁ := by
      constructor
      · intro he
        apply Fin.succ_injective
        apply (activeFaceMono p).injective
        exact he.trans hend.symm
      · rintro rfl
        exact hend
    have hcastnot (j : Fin (activeFaceSize p+1)) : activeFaceMesh p j.castSucc ≠ 1 := by
      intro he
      have hi := (activeFaceMono p).injective (he.trans (activeFaceEnd p).symm)
      exact Fin.castSucc_ne_last j hi
    have hL : Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.succ = 1) = {j₁} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hendunique j]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hmneg,rfl⟩
    have hR : Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
        actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
          (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.castSucc = 1) = ∅ := by
      ext j
      simp [hcastnot j]
    rw [hL,hR]
    simp
  have actualNegativeMeshNeighborEdges (p : activeCells × Fin 4)
      (i : Fin (activeFaceSize p+2)) (hi0 : i ≠ 0)
      (hi1 : i ≠ Fin.last (activeFaceSize p+1))
      (hneg : actualFaceHeight p (activeFaceMesh p i) < 0) :
      ∃ eL eR : zeroEdgeIndex, eL ≠ eR ∧ eL.1 = p ∧ eR.1 = p ∧
        zeroEdge eL 1 = zeroEdge eR 0 := by
    obtain ⟨l,hl⟩ := Fin.exists_succ_eq.mpr hi0
    obtain ⟨r,hr⟩ := Fin.exists_castSucc_eq.mpr hi1
    have hgl : actualFaceHeight p (activeFaceMesh p l.succ) < 0 := hl.symm ▸ hneg
    have hgr : actualFaceHeight p (activeFaceMesh p r.castSucc) < 0 := hr.symm ▸ hneg
    have hnl := ((actualFaceEndpointGerms p l).2 (ne_of_lt hgl)).mpr hgl
    have hnr := ((actualFaceEndpointGerms p r).1 (ne_of_lt hgr)).mpr hgr
    let eL : zeroEdgeIndex := ⟨p,⟨l,hnl⟩⟩
    let eR : zeroEdgeIndex := ⟨p,⟨r,hnr⟩⟩
    let z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops p.1.val z).val.1 / (cellCenter p.1.val).val.1 ≤ 0} :=
      ⟨boundaryFace p.2 (activeFaceMesh p i),hneg.le⟩
    have hL : zeroEdge eL 1 = activeFaceRadial p z :=
      (zeroRightEndpointOnSameFace eL (activeFaceMesh p i) z rfl).mpr (congrArg (activeFaceMesh p) hl)
    have hR : zeroEdge eR 0 = activeFaceRadial p z :=
      (zeroLeftEndpointOnSameFace eR (activeFaceMesh p i) z rfl).mpr (congrArg (activeFaceMesh p) hr)
    refine ⟨eL,eR,?_,rfl,rfl,hL.trans hR.symm⟩
    intro he
    have hidx := congrArg (fun e : zeroEdgeIndex => e.2.val.val) he
    have hadj := congrArg Fin.val (hl.trans hr.symm)
    change l.val = r.val at hidx
    change l.val+1 = r.val at hadj
    omega
  have actualOpenRootSourceFaceUnique (k : activeCells) (i j : Fin 4)
      (t : Interval) (ht01 : t ∈ Set.Ioo (0 : Interval) 1)
      (ht : actualFaceHeight (k,i) t = 0)
      (x : {r : Fin (activeFaceSize (k,j)+1) |
        actualFaceHeight (k,j) (intervalMidpoint
          (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0})
      (he : zeroEdge ⟨(k,j),x⟩ 0 = squareCoordinates
        ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩) : j = i := by
    let e : zeroEdgeIndex := ⟨(k,j),x⟩
    let z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k.val z).val.1 / (cellCenter k.val).val.1 ≤ 0} :=
      ⟨boundaryFace i t,ht.le⟩
    have hn : (regularizedCellLoops k.val (boundaryFace i t)).val.1 = 0 :=
      (div_eq_zero_iff.mp ht).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hf := activeFaceBoundaryFix (k,i) z hn
    have hr : activeFaceRadial (k,i) (zeroLeft e) = activeFaceRadial (k,i) z :=
      (activeFaceRadialAgreement k i j (zeroLeft e)).trans
        ((zeroSource e).symm.trans (he.trans hf.symm))
    have hd := congrArg Subtype.val (activeFaceRadialInjective k i hr)
    have hface : boundaryFace j (activeFaceMesh (k,j) x.val.castSucc) =
        boundaryFace i t := (zeroLeftBoundary e).symm.trans hd
    exact (boundaryFaceOpenUnique i j t _ ht01 hface.symm).symm
  have actualOpenRootTargetFaceUnique (k : activeCells) (i j : Fin 4)
      (t : Interval) (ht01 : t ∈ Set.Ioo (0 : Interval) 1)
      (ht : actualFaceHeight (k,i) t = 0)
      (x : {r : Fin (activeFaceSize (k,j)+1) |
        actualFaceHeight (k,j) (intervalMidpoint
          (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0})
      (he : zeroEdge ⟨(k,j),x⟩ 1 = squareCoordinates
        ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩) : j = i := by
    let e : zeroEdgeIndex := ⟨(k,j),x⟩
    let z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k.val z).val.1 / (cellCenter k.val).val.1 ≤ 0} :=
      ⟨boundaryFace i t,ht.le⟩
    have hn : (regularizedCellLoops k.val (boundaryFace i t)).val.1 = 0 :=
      (div_eq_zero_iff.mp ht).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hf := activeFaceBoundaryFix (k,i) z hn
    have hr : activeFaceRadial (k,i) (zeroRight e) = activeFaceRadial (k,i) z :=
      (activeFaceRadialAgreement k i j (zeroRight e)).trans
        ((zeroTarget e).symm.trans (he.trans hf.symm))
    have hd := congrArg Subtype.val (activeFaceRadialInjective k i hr)
    have hface : boundaryFace j (activeFaceMesh (k,j) x.val.succ) =
        boundaryFace i t := (zeroRightBoundary e).symm.trans hd
    exact (boundaryFaceOpenUnique i j t _ ht01 hface.symm).symm
  -- Radial injectivity also identifies an open face at a NEGATIVE direction,
  -- where the actual graph endpoint lies strictly inside the grid cell.
  have actualOpenConeSourceFaceUnique (k : activeCells) (i j : Fin 4)
      (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0)
      (x : {r : Fin (activeFaceSize (k,j)+1) |
        actualFaceHeight (k,j) (intervalMidpoint
          (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0})
      (he : zeroEdge ⟨(k,j),x⟩ 0 = activeFaceRadial (k,i)
        ⟨boundaryFace i t,hle⟩) : j = i := by
    let e : zeroEdgeIndex := ⟨(k,j),x⟩
    have hr : activeFaceRadial (k,i) (zeroLeft e) = activeFaceRadial (k,i)
        ⟨boundaryFace i t,hle⟩ :=
      (activeFaceRadialAgreement k i j (zeroLeft e)).trans ((zeroSource e).symm.trans he)
    have hd := congrArg Subtype.val (activeFaceRadialInjective k i hr)
    have hface : boundaryFace j (activeFaceMesh (k,j) x.val.castSucc) = boundaryFace i t :=
      (zeroLeftBoundary e).symm.trans hd
    exact (boundaryFaceOpenUnique i j t _ ht hface.symm).symm
  have actualOpenConeTargetFaceUnique (k : activeCells) (i j : Fin 4)
      (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0)
      (x : {r : Fin (activeFaceSize (k,j)+1) |
        actualFaceHeight (k,j) (intervalMidpoint
          (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0})
      (he : zeroEdge ⟨(k,j),x⟩ 1 = activeFaceRadial (k,i)
        ⟨boundaryFace i t,hle⟩) : j = i := by
    let e : zeroEdgeIndex := ⟨(k,j),x⟩
    have hr : activeFaceRadial (k,i) (zeroRight e) = activeFaceRadial (k,i)
        ⟨boundaryFace i t,hle⟩ :=
      (activeFaceRadialAgreement k i j (zeroRight e)).trans ((zeroTarget e).symm.trans he)
    have hd := congrArg Subtype.val (activeFaceRadialInjective k i hr)
    have hface : boundaryFace j (activeFaceMesh (k,j) x.val.succ) = boundaryFace i t :=
      (zeroRightBoundary e).symm.trans hd
    exact (boundaryFaceOpenUnique i j t _ ht hface.symm).symm
  -- Each actual cell incidence fiber is equivalent to the concrete mesh-index
  -- list on the unique open face; this includes every actual edge in the cell.
  have actualOpenConeSourceFiber (k : activeCells) (i : Fin 4)
      (t : Interval) (ht01 : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0) :
      Nonempty
        ({e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} ≃
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.castSucc = t}) := by
    let toIndex := fun e : {e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} => by
      rcases e with ⟨⟨j,x⟩,he⟩
      have hj := actualOpenConeSourceFaceUnique k i j t ht01 hle x he
      subst j
      exact (⟨x,(zeroLeftEndpointOnSameFace ⟨(k,i),x⟩ t ⟨boundaryFace i t,hle⟩ rfl).mp he⟩ :
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.castSucc = t})
    refine ⟨{
      toFun := toIndex
      invFun := fun x => ⟨⟨i,x.val⟩,
        (zeroLeftEndpointOnSameFace ⟨(k,i),x.val⟩ t ⟨boundaryFace i t,hle⟩ rfl).mpr x.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨j,x⟩,he⟩
      have hj := actualOpenConeSourceFaceUnique k i j t ht01 hle x he
      subst j
      rfl
    · intro x
      rfl
  -- Each actual cell incidence fiber is equivalent to the concrete mesh-index
  -- list on the unique open face; this includes every actual edge in the cell.
  have actualOpenConeTargetFiber (k : activeCells) (i : Fin 4)
      (t : Interval) (ht01 : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0) :
      Nonempty
        ({e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} ≃
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.succ = t}) := by
    let toIndex := fun e : {e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} => by
      rcases e with ⟨⟨j,x⟩,he⟩
      have hj := actualOpenConeTargetFaceUnique k i j t ht01 hle x he
      subst j
      exact (⟨x,(zeroRightEndpointOnSameFace ⟨(k,i),x⟩ t ⟨boundaryFace i t,hle⟩ rfl).mp he⟩ :
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.succ = t})
    refine ⟨{
      toFun := toIndex
      invFun := fun x => ⟨⟨i,x.val⟩,
        (zeroRightEndpointOnSameFace ⟨(k,i),x.val⟩ t ⟨boundaryFace i t,hle⟩ rfl).mpr x.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨j,x⟩,he⟩
      have hj := actualOpenConeTargetFaceUnique k i j t ht01 hle x he
      subst j
      rfl
    · intro x
      rfl
  have actualCornerSourceDirectionIncidence (k : activeCells) (i : Fin 4)
      (t : Interval) (hle : actualFaceHeight (k,i) t ≤ 0)
      (j : Fin 4)
      (x : {r : Fin (activeFaceSize (k,j)+1) |
        actualFaceHeight (k,j) (intervalMidpoint
          (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0}) :
      zeroEdge ⟨(k,j),x⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩ ↔
        boundaryFace j (activeFaceMesh (k,j) x.val.castSucc) = boundaryFace i t := by
    let e : zeroEdgeIndex := ⟨(k,j),x⟩
    rw [zeroSource e]
    constructor
    · intro he
      have hr := (activeFaceRadialAgreement k i j (zeroLeft e)).trans he
      have hd := congrArg Subtype.val (activeFaceRadialInjective k i hr)
      exact (zeroLeftBoundary e).symm.trans hd
    · intro he
      have hd : zeroLeft e = ⟨boundaryFace i t,hle⟩ :=
        Subtype.ext ((zeroLeftBoundary e).trans he)
      rw [hd]
      exact (activeFaceRadialAgreement k i j ⟨boundaryFace i t,hle⟩).symm
  have actualCornerTargetDirectionIncidence (k : activeCells) (i : Fin 4)
      (t : Interval) (hle : actualFaceHeight (k,i) t ≤ 0)
      (j : Fin 4)
      (x : {r : Fin (activeFaceSize (k,j)+1) |
        actualFaceHeight (k,j) (intervalMidpoint
          (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0}) :
      zeroEdge ⟨(k,j),x⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩ ↔
        boundaryFace j (activeFaceMesh (k,j) x.val.succ) = boundaryFace i t := by
    let e : zeroEdgeIndex := ⟨(k,j),x⟩
    rw [zeroTarget e]
    constructor
    · intro he
      have hr := (activeFaceRadialAgreement k i j (zeroRight e)).trans he
      have hd := congrArg Subtype.val (activeFaceRadialInjective k i hr)
      exact (zeroRightBoundary e).symm.trans hd
    · intro he
      have hd : zeroRight e = ⟨boundaryFace i t,hle⟩ :=
        Subtype.ext ((zeroRightBoundary e).trans he)
      rw [hd]
      exact (activeFaceRadialAgreement k i j ⟨boundaryFace i t,hle⟩).symm
  have actualFaceZeroAdjacentIntervals (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0) :
      ∃ l r : Fin (activeFaceSize p+1),
        activeFaceMesh p l.succ = t ∧ activeFaceMesh p r.castSucc = t ∧
        l.val+1 = r.val ∧
        (∀ j : Fin (activeFaceSize p+1), activeFaceMesh p j.succ = t ↔ j = l) ∧
        (∀ j : Fin (activeFaceSize p+1), activeFaceMesh p j.castSucc = t ↔ j = r) := by
    exact mesh_zero_adjacent (activeFaceSize p) (activeFaceMesh p)
      (activeFaceMono p) (activeFaceStart p) (activeFaceEnd p)
      (actualFaceHeight p) (actualFaceEndpointsNonzero p).1
      (actualFaceEndpointsNonzero p).2
      (fun j r hr0 hr1 => actualFaceIntervalNoZero p j r hr0 hr1) t ht
  have actualFaceRootSourceIncidence (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0)
      (j : Fin (activeFaceSize p+1))
      (hneg : actualFaceHeight p (intervalMidpoint
        (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0) :
      zeroEdge ⟨p,⟨j,hneg⟩⟩ 0 = squareCoordinates
        ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩ ↔
        activeFaceMesh p j.castSucc = t := by
    let z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops p.1.val z).val.1 /
          (cellCenter p.1.val).val.1 ≤ 0} := ⟨boundaryFace p.2 t,ht.le⟩
    have hn : (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 = 0 :=
      (div_eq_zero_iff.mp ht).resolve_right
        (cellCenterAxisNonzero p.1.val (activeCellAxis p.1))
    have hf := activeFaceBoundaryFix p z hn
    have hh := zeroLeftEndpointOnSameFace ⟨p,⟨j,hneg⟩⟩ t z rfl
    rwa [hf] at hh
  have actualFaceRootTargetIncidence (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0)
      (j : Fin (activeFaceSize p+1))
      (hneg : actualFaceHeight p (intervalMidpoint
        (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0) :
      zeroEdge ⟨p,⟨j,hneg⟩⟩ 1 = squareCoordinates
        ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩ ↔
        activeFaceMesh p j.succ = t := by
    let z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops p.1.val z).val.1 /
          (cellCenter p.1.val).val.1 ≤ 0} := ⟨boundaryFace p.2 t,ht.le⟩
    have hn : (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 = 0 :=
      (div_eq_zero_iff.mp ht).resolve_right
        (cellCenterAxisNonzero p.1.val (activeCellAxis p.1))
    have hf := activeFaceBoundaryFix p z hn
    have hh := zeroRightEndpointOnSameFace ⟨p,⟨j,hneg⟩⟩ t z rfl
    rwa [hf] at hh
  -- Each actual cell incidence fiber is equivalent to the concrete mesh-index
  -- list on the unique open face; this includes every actual edge in the cell.
  have actualOpenRootSourceFiber (k : activeCells) (i : Fin 4)
      (t : Interval) (ht01 : t ∈ Set.Ioo (0 : Interval) 1)
      (ht : actualFaceHeight (k,i) t = 0) :
      Nonempty
        ({e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 0 = squareCoordinates
            ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩} ≃
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.castSucc = t}) := by
    let toIndex := fun e : {e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 0 = squareCoordinates
            ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩} => by
      rcases e with ⟨⟨j,x⟩,he⟩
      have hj := actualOpenRootSourceFaceUnique k i j t ht01 ht x he
      subst j
      exact (⟨x,(actualFaceRootSourceIncidence (k,i) t ht x.val x.property).mp he⟩ :
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.castSucc = t})
    refine ⟨{
      toFun := toIndex
      invFun := fun x => ⟨⟨i,x.val⟩,
        (actualFaceRootSourceIncidence (k,i) t ht x.val.val x.val.property).mpr x.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨j,x⟩,he⟩
      have hj := actualOpenRootSourceFaceUnique k i j t ht01 ht x he
      subst j
      rfl
    · intro x
      rfl
  -- Each actual cell incidence fiber is equivalent to the concrete mesh-index
  -- list on the unique open face; this includes every actual edge in the cell.
  have actualOpenRootTargetFiber (k : activeCells) (i : Fin 4)
      (t : Interval) (ht01 : t ∈ Set.Ioo (0 : Interval) 1)
      (ht : actualFaceHeight (k,i) t = 0) :
      Nonempty
        ({e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 1 = squareCoordinates
            ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩} ≃
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.succ = t}) := by
    let toIndex := fun e : {e : Σ j : Fin 4, {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,e.1),e.2⟩ 1 = squareCoordinates
            ⟨(boundaryFace i t).val,(boundaryFace i t).property.le⟩} => by
      rcases e with ⟨⟨j,x⟩,he⟩
      have hj := actualOpenRootTargetFaceUnique k i j t ht01 ht x he
      subst j
      exact (⟨x,(actualFaceRootTargetIncidence (k,i) t ht x.val x.property).mp he⟩ :
        {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.succ = t})
    refine ⟨{
      toFun := toIndex
      invFun := fun x => ⟨⟨i,x.val⟩,
        (actualFaceRootTargetIncidence (k,i) t ht x.val.val x.val.property).mpr x.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨j,x⟩,he⟩
      have hj := actualOpenRootTargetFaceUnique k i j t ht01 ht x he
      subst j
      rfl
    · intro x
      rfl
  let actualCellEdgeIndex (k : activeCells) := Σ j : Fin 4,
    {r : Fin (activeFaceSize (k,j)+1) |
      actualFaceHeight (k,j) (intervalMidpoint
        (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0}
  let actualCellSourceCount (k : activeCells) (x : Interval × Interval) : ℕ :=
    (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
      zeroEdge ⟨(k,e.1),e.2⟩ 0 = x)).card
  let actualCellTargetCount (k : activeCells) (x : Interval × Interval) : ℕ :=
    (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
      zeroEdge ⟨(k,e.1),e.2⟩ 1 = x)).card
  have actualOpenConeCellSourceCount (k : activeCells) (i : Fin 4)
      (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0) :
      actualCellSourceCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,i)+1) =>
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0 ∧
          activeFaceMesh (k,i) r.castSucc = t)).card := by
    calc
      actualCellSourceCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
          Fintype.card {e : actualCellEdgeIndex k |
            zeroEdge ⟨(k,e.1),e.2⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.castSucc = t} :=
        Fintype.card_congr (Classical.choice (actualOpenConeSourceFiber k i t ht hle))
      _ = Fintype.card {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0 ∧
          activeFaceMesh (k,i) r.castSucc = t} :=
        Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun r : Fin (activeFaceSize (k,i)+1) => actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0)
          (fun r : Fin (activeFaceSize (k,i)+1) => activeFaceMesh (k,i) r.castSucc = t))
      _ = _ := Fintype.card_subtype _
  have actualOpenConeCellTargetCount (k : activeCells) (i : Fin 4)
      (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0) :
      actualCellTargetCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,i)+1) =>
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0 ∧
          activeFaceMesh (k,i) r.succ = t)).card := by
    calc
      actualCellTargetCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
          Fintype.card {e : actualCellEdgeIndex k |
            zeroEdge ⟨(k,e.1),e.2⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} |
          activeFaceMesh (k,i) x.val.succ = t} :=
        Fintype.card_congr (Classical.choice (actualOpenConeTargetFiber k i t ht hle))
      _ = Fintype.card {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0 ∧
          activeFaceMesh (k,i) r.succ = t} :=
        Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun r : Fin (activeFaceSize (k,i)+1) => actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0)
          (fun r : Fin (activeFaceSize (k,i)+1) => activeFaceMesh (k,i) r.succ = t))
      _ = _ := Fintype.card_subtype _
  have actualOpenConeCellEndpointCount (k : activeCells) (i : Fin 4)
      (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (hle : actualFaceHeight (k,i) t ≤ 0) :
      actualCellSourceCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) +
        actualCellTargetCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
      actualFaceIncidenceCount (k,i) t := by
    rw [actualOpenConeCellSourceCount k i t ht hle,actualOpenConeCellTargetCount k i t ht hle]
    exact Nat.add_comm _ _
  have actualRootCellEndpointCount (k : activeCells) (i : Fin 4) (u : Interval)
      (hroot : actualFaceHeight (k,i) u = 0) :
      actualCellSourceCount k (squareCoordinates
        ⟨(boundaryFace i u).val,(boundaryFace i u).property.le⟩) +
      actualCellTargetCount k (squareCoordinates
        ⟨(boundaryFace i u).val,(boundaryFace i u).property.le⟩) =
      actualFaceIncidenceCount (k,i) u := by
    have hu0 : u ≠ 0 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,i)).1 (he ▸ hroot)
    have hu1 : u ≠ 1 := by
      intro he
      exact (actualFaceEndpointsNonzero (k,i)).2 (he ▸ hroot)
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne u.property.1 hu0.symm,lt_of_le_of_ne u.property.2 hu1⟩
    have hn : (regularizedCellLoops k.val (boundaryFace i u)).val.1 = 0 :=
      (div_eq_zero_iff.mp hroot).resolve_right (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hf := activeFaceBoundaryFix (k,i) ⟨boundaryFace i u,hroot.le⟩ hn
    have hcount := actualOpenConeCellEndpointCount k i u hu hroot.le
    rw [hf] at hcount
    exact hcount
  have actualCellFaceEndpointFiberPartition (k : activeCells) (P : actualCellEdgeIndex k → Prop) :
      Nonempty ({e : actualCellEdgeIndex k | P e} ≃
        Σ i : Fin 4, {x : {r : Fin (activeFaceSize (k,i)+1) |
          actualFaceHeight (k,i) (intervalMidpoint
            (activeFaceMesh (k,i) r.castSucc) (activeFaceMesh (k,i) r.succ)) < 0} | P ⟨i,x⟩}) := by
    refine ⟨{
      toFun := fun e => ⟨e.val.1,⟨e.val.2,e.property⟩⟩
      invFun := fun e => ⟨⟨e.1,e.2.val⟩,e.2.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨i,x⟩,he⟩
      rfl
    · rintro ⟨i,⟨x,he⟩⟩
      rfl
  have actualCellSourceCornerDirectionCount (k : activeCells) (i : Fin 4)
      (t : Interval) (hle : actualFaceHeight (k,i) t ≤ 0) :
      actualCellSourceCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
        ∑ j : Fin 4, (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace i t)).card := by
    calc
      actualCellSourceCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
          Fintype.card {e : actualCellEdgeIndex k |
            zeroEdge ⟨(k,e.1),e.2⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card (Σ j : Fin 4, {x : {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,j),x⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩}) :=
        Fintype.card_congr (Classical.choice (actualCellFaceEndpointFiberPartition k
          (fun e => zeroEdge ⟨(k,e.1),e.2⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩)))
      _ = ∑ j : Fin 4, Fintype.card {x : {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,j),x⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} := Fintype.card_sigma
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          Fintype.card {x : {r : Fin (activeFaceSize (k,j)+1) |
              actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
              zeroEdge ⟨(k,j),x⟩ 0 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} =
            Fintype.card {x : {r : Fin (activeFaceSize (k,j)+1) |
              actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
              boundaryFace j (activeFaceMesh (k,j) x.val.castSucc) = boundaryFace i t} :=
            Fintype.card_congr (Equiv.subtypeEquivRight
              (fun x => actualCornerSourceDirectionIncidence k i t hle j x))
          _ = Fintype.card {r : Fin (activeFaceSize (k,j)+1) |
              actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
              boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace i t} :=
            Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
              (fun r : Fin (activeFaceSize (k,j)+1) => actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0)
              (fun r : Fin (activeFaceSize (k,j)+1) =>
                boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace i t))
          _ = _ := Fintype.card_subtype _
  have actualCellTargetCornerDirectionCount (k : activeCells) (i : Fin 4)
      (t : Interval) (hle : actualFaceHeight (k,i) t ≤ 0) :
      actualCellTargetCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
        ∑ j : Fin 4, (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace i t)).card := by
    calc
      actualCellTargetCount k (activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩) =
          Fintype.card {e : actualCellEdgeIndex k |
            zeroEdge ⟨(k,e.1),e.2⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = Fintype.card (Σ j : Fin 4, {x : {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,j),x⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩}) :=
        Fintype.card_congr (Classical.choice (actualCellFaceEndpointFiberPartition k
          (fun e => zeroEdge ⟨(k,e.1),e.2⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩)))
      _ = ∑ j : Fin 4, Fintype.card {x : {r : Fin (activeFaceSize (k,j)+1) |
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
          zeroEdge ⟨(k,j),x⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} := Fintype.card_sigma
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          Fintype.card {x : {r : Fin (activeFaceSize (k,j)+1) |
              actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
              zeroEdge ⟨(k,j),x⟩ 1 = activeFaceRadial (k,i) ⟨boundaryFace i t,hle⟩} =
            Fintype.card {x : {r : Fin (activeFaceSize (k,j)+1) |
              actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0} |
              boundaryFace j (activeFaceMesh (k,j) x.val.succ) = boundaryFace i t} :=
            Fintype.card_congr (Equiv.subtypeEquivRight
              (fun x => actualCornerTargetDirectionIncidence k i t hle j x))
          _ = Fintype.card {r : Fin (activeFaceSize (k,j)+1) |
              actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
              boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace i t} :=
            Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
              (fun r : Fin (activeFaceSize (k,j)+1) => actualFaceHeight (k,j) (intervalMidpoint
                (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0)
              (fun r : Fin (activeFaceSize (k,j)+1) =>
                boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace i t))
          _ = _ := Fintype.card_subtype _
  have actualNegativeCorner00CellCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,0) (0 : Interval) < 0) :
      actualCellSourceCount k (activeFaceRadial (k,0) ⟨boundaryFace 0 0,hneg.le⟩) +
      actualCellTargetCount k (activeFaceRadial (k,0) ⟨boundaryFace 0 0,hneg.le⟩) = 2 := by
    have hn1 : actualFaceHeight (k,0) (0 : Interval) < 0 := hneg
    have hn2 : actualFaceHeight (k,3) (0 : Interval) < 0 := by
        have hf : boundaryFace 3 (0 : Interval) = boundaryFace 0 0 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        change (regularizedCellLoops k.val (boundaryFace 3 (0 : Interval))).val.1 /
          (cellCenter k.val).val.1 < 0
        rw [hf]
        exact hneg
    have hc1 := actualNegativeFaceStartCount (k,0) hn1
    have hc2 := actualNegativeFaceStartCount (k,3) hn2
    rw [actualCellSourceCornerDirectionCount k 0 0 hneg.le,
      actualCellTargetCornerDirectionCount k 0 0 hneg.le,←Finset.sum_add_distrib]
    have hterm (j : Fin 4) :
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace 0 0)).card +
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace 0 0)).card =
          if j = 0 ∨ j = 3 then 1 else 0 := by
      simp_rw [(actualCornerFaceClassification j _).1]
      fin_cases j
      all_goals first
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.1 hc1.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.2 hc1.1)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.1 hc2.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.2 hc2.1)
        | simp
    simp_rw [hterm]
    decide
  have actualNegativeCorner01CellCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,0) (1 : Interval) < 0) :
      actualCellSourceCount k (activeFaceRadial (k,0) ⟨boundaryFace 0 1,hneg.le⟩) +
      actualCellTargetCount k (activeFaceRadial (k,0) ⟨boundaryFace 0 1,hneg.le⟩) = 2 := by
    have hn1 : actualFaceHeight (k,0) (1 : Interval) < 0 := hneg
    have hn2 : actualFaceHeight (k,1) (0 : Interval) < 0 := by
        have hf : boundaryFace 1 (0 : Interval) = boundaryFace 0 1 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        change (regularizedCellLoops k.val (boundaryFace 1 (0 : Interval))).val.1 /
          (cellCenter k.val).val.1 < 0
        rw [hf]
        exact hneg
    have hc1 := actualNegativeFaceEndCount (k,0) hn1
    have hc2 := actualNegativeFaceStartCount (k,1) hn2
    rw [actualCellSourceCornerDirectionCount k 0 1 hneg.le,
      actualCellTargetCornerDirectionCount k 0 1 hneg.le,←Finset.sum_add_distrib]
    have hterm (j : Fin 4) :
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace 0 1)).card +
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace 0 1)).card =
          if j = 0 ∨ j = 1 then 1 else 0 := by
      simp_rw [(actualCornerFaceClassification j _).2.1]
      fin_cases j
      all_goals first
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.1 hc1.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.2 hc1.1)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.1 hc2.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.2 hc2.1)
        | simp
    simp_rw [hterm]
    decide
  have actualNegativeCorner20CellCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,2) (0 : Interval) < 0) :
      actualCellSourceCount k (activeFaceRadial (k,2) ⟨boundaryFace 2 0,hneg.le⟩) +
      actualCellTargetCount k (activeFaceRadial (k,2) ⟨boundaryFace 2 0,hneg.le⟩) = 2 := by
    have hn1 : actualFaceHeight (k,2) (0 : Interval) < 0 := hneg
    have hn2 : actualFaceHeight (k,3) (1 : Interval) < 0 := by
        have hf : boundaryFace 3 (1 : Interval) = boundaryFace 2 0 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        change (regularizedCellLoops k.val (boundaryFace 3 (1 : Interval))).val.1 /
          (cellCenter k.val).val.1 < 0
        rw [hf]
        exact hneg
    have hc1 := actualNegativeFaceStartCount (k,2) hn1
    have hc2 := actualNegativeFaceEndCount (k,3) hn2
    rw [actualCellSourceCornerDirectionCount k 2 0 hneg.le,
      actualCellTargetCornerDirectionCount k 2 0 hneg.le,←Finset.sum_add_distrib]
    have hterm (j : Fin 4) :
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace 2 0)).card +
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace 2 0)).card =
          if j = 2 ∨ j = 3 then 1 else 0 := by
      simp_rw [(actualCornerFaceClassification j _).2.2.1]
      fin_cases j
      all_goals first
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.1 hc1.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.2 hc1.1)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.1 hc2.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.2 hc2.1)
        | simp
    simp_rw [hterm]
    decide
  have actualNegativeCorner21CellCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,2) (1 : Interval) < 0) :
      actualCellSourceCount k (activeFaceRadial (k,2) ⟨boundaryFace 2 1,hneg.le⟩) +
      actualCellTargetCount k (activeFaceRadial (k,2) ⟨boundaryFace 2 1,hneg.le⟩) = 2 := by
    have hn1 : actualFaceHeight (k,2) (1 : Interval) < 0 := hneg
    have hn2 : actualFaceHeight (k,1) (1 : Interval) < 0 := by
        have hf : boundaryFace 1 (1 : Interval) = boundaryFace 2 1 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        change (regularizedCellLoops k.val (boundaryFace 1 (1 : Interval))).val.1 /
          (cellCenter k.val).val.1 < 0
        rw [hf]
        exact hneg
    have hc1 := actualNegativeFaceEndCount (k,2) hn1
    have hc2 := actualNegativeFaceEndCount (k,1) hn2
    rw [actualCellSourceCornerDirectionCount k 2 1 hneg.le,
      actualCellTargetCornerDirectionCount k 2 1 hneg.le,←Finset.sum_add_distrib]
    have hterm (j : Fin 4) :
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.castSucc) = boundaryFace 2 1)).card +
        (Finset.univ.filter (fun r : Fin (activeFaceSize (k,j)+1) =>
          actualFaceHeight (k,j) (intervalMidpoint
            (activeFaceMesh (k,j) r.castSucc) (activeFaceMesh (k,j) r.succ)) < 0 ∧
          boundaryFace j (activeFaceMesh (k,j) r.succ) = boundaryFace 2 1)).card =
          if j = 2 ∨ j = 1 then 1 else 0 := by
      simp_rw [(actualCornerFaceClassification j _).2.2.2]
      fin_cases j
      all_goals first
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.1 hc1.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc1.2 hc1.1)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.1 hc2.2)
        | (simpa using congrArg₂ (fun x y : ℕ => x+y) hc2.2 hc2.1)
        | simp
    simp_rw [hterm]
    decide
  have actualSingleCellEndpointFiber (P : zeroEdgeIndex → Prop) (k : activeCells)
      (hcell : ∀ e, P e → e.1.1 = k) :
      Nonempty ({e : zeroEdgeIndex | P e} ≃
        {e : actualCellEdgeIndex k | P ⟨(k,e.1),e.2⟩}) := by
    let toIndex := fun e : {e : zeroEdgeIndex | P e} => by
      rcases e with ⟨⟨⟨l,i⟩,x⟩,he⟩
      have hl := hcell ⟨(l,i),x⟩ he
      change l = k at hl
      subst l
      exact (⟨⟨i,x⟩,he⟩ : {e : actualCellEdgeIndex k | P ⟨(k,e.1),e.2⟩})
    refine ⟨{
      toFun := toIndex
      invFun := fun e => ⟨⟨(k,e.val.1),e.val.2⟩,e.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨⟨l,i⟩,x⟩,he⟩
      have hl := hcell ⟨(l,i),x⟩ he
      change l = k at hl
      subst l
      rfl
    · rintro ⟨⟨i,x⟩,he⟩
      rfl
  have actualCellIndexReassociation :
      Nonempty (zeroEdgeIndex ≃ Σ k : activeCells, actualCellEdgeIndex k) := by
    refine ⟨{
      toFun := fun e => ⟨e.1.1,⟨e.1.2,e.2⟩⟩
      invFun := fun e => ⟨(e.1,e.2.1),e.2.2⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨k,i⟩,x⟩
      rfl
    · rintro ⟨k,⟨i,x⟩⟩
      rfl
  have actualSigmaEndpointFiberPartition (P : zeroEdgeIndex → Prop) :
      Nonempty ({e : zeroEdgeIndex | P e} ≃
        Σ k : activeCells, {e : actualCellEdgeIndex k | P ⟨(k,e.1),e.2⟩}) := by
    refine ⟨{
      toFun := fun e => ⟨e.val.1.1,⟨⟨e.val.1.2,e.val.2⟩,e.property⟩⟩
      invFun := fun e => ⟨⟨(e.1,e.2.val.1),e.2.val.2⟩,e.2.property⟩
      left_inv := ?_
      right_inv := ?_}⟩
    · rintro ⟨⟨⟨k,i⟩,x⟩,he⟩
      rfl
    · rintro ⟨k,⟨⟨i,x⟩,he⟩⟩
      rfl
  have actualTwoCellEndpointFiber (P : zeroEdgeIndex → Prop) (k l : activeCells)
      (hkl : k ≠ l) (hcell : ∀ e, P e → e.1.1 = k ∨ e.1.1 = l) :
      Fintype.card {e : zeroEdgeIndex | P e} =
        Fintype.card {e : actualCellEdgeIndex k | P ⟨(k,e.1),e.2⟩} +
        Fintype.card {e : actualCellEdgeIndex l | P ⟨(l,e.1),e.2⟩} := by
    calc
      Fintype.card {e : zeroEdgeIndex | P e} =
          Fintype.card (Σ c : activeCells,
            {e : actualCellEdgeIndex c | P ⟨(c,e.1),e.2⟩}) :=
        Fintype.card_congr (Classical.choice (actualSigmaEndpointFiberPartition P))
      _ = ∑ c : activeCells,
          Fintype.card {e : actualCellEdgeIndex c | P ⟨(c,e.1),e.2⟩} :=
        Fintype.card_sigma
      _ = _ := by
        apply Finset.sum_eq_add_of_mem k l (Finset.mem_univ _) (Finset.mem_univ _) hkl
        intro c hc hneq
        have hempty : IsEmpty {e : actualCellEdgeIndex c | P ⟨(c,e.1),e.2⟩} := ⟨by
          intro e
          rcases hcell ⟨(c,e.val.1),e.val.2⟩ e.property with hk | hl
          · exact hneq.1 hk
          · exact hneq.2 hl⟩
        exact Fintype.card_of_isEmpty
  -- Every actual endpoint comes from its selected mesh direction; its height
  -- is either an actual face root or a negative direction inside that cell.
  have actualSourceEndpointDirectionCases (e : zeroEdgeIndex) :
      actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) = 0 ∨
        actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) < 0 := by
    have hle : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) ≤ 0 := by
      have hh := (zeroLeft e).property
      rw [zeroLeftBoundary e] at hh
      exact hh
    exact eq_or_lt_of_le hle
  have actualTargetEndpointDirectionCases (e : zeroEdgeIndex) :
      actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) = 0 ∨
        actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) < 0 := by
    have hle : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) ≤ 0 := by
      have hh := (zeroRight e).property
      rw [zeroRightBoundary e] at hh
      exact hh
    exact eq_or_lt_of_le hle
  have actualSourceRootEndpointFormula (e : zeroEdgeIndex)
      (hroot : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) = 0) :
      zeroEdge e 0 = squareCoordinates
        ⟨(boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.castSucc)).val,
          (boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.castSucc)).property.le⟩ := by
    rw [zeroSource e]
    have hn : (regularizedCellLoops e.1.1.val (zeroLeft e).val).val.1 = 0 := by
      rw [zeroLeftBoundary e]
      exact (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero e.1.1.val (activeCellAxis e.1.1))
    rw [activeFaceBoundaryFix e.1 (zeroLeft e) hn]
    apply congrArg squareCoordinates
    apply Subtype.ext
    exact congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val) (zeroLeftBoundary e)
  have actualTargetRootEndpointFormula (e : zeroEdgeIndex)
      (hroot : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) = 0) :
      zeroEdge e 1 = squareCoordinates
        ⟨(boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.succ)).val,
          (boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.succ)).property.le⟩ := by
    rw [zeroTarget e]
    have hn : (regularizedCellLoops e.1.1.val (zeroRight e).val).val.1 = 0 := by
      rw [zeroRightBoundary e]
      exact (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero e.1.1.val (activeCellAxis e.1.1))
    rw [activeFaceBoundaryFix e.1 (zeroRight e) hn]
    apply congrArg squareCoordinates
    apply Subtype.ext
    exact congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val) (zeroRightBoundary e)
  have actualSourceMeshNodeCases (e : zeroEdgeIndex) :
      e.2.val.castSucc = 0 ∨
        (e.2.val.castSucc ≠ 0 ∧ e.2.val.castSucc ≠ Fin.last (activeFaceSize e.1+1)) := by
    by_cases h : e.2.val.castSucc = 0
    · exact Or.inl h
    · exact Or.inr ⟨h,Fin.castSucc_ne_last e.2.val⟩
  have actualTargetMeshNodeCases (e : zeroEdgeIndex) :
      e.2.val.succ = Fin.last (activeFaceSize e.1+1) ∨
        (e.2.val.succ ≠ 0 ∧ e.2.val.succ ≠ Fin.last (activeFaceSize e.1+1)) := by
    by_cases h : e.2.val.succ = Fin.last (activeFaceSize e.1+1)
    · exact Or.inl h
    · exact Or.inr ⟨Fin.succ_ne_zero e.2.val,h⟩
  have actualInternalMeshNodeOpenParameter (p : activeCells × Fin 4)
      (i : Fin (activeFaceSize p+2)) (hi0 : i ≠ 0)
      (hi1 : i ≠ Fin.last (activeFaceSize p+1)) :
      activeFaceMesh p i ∈ Set.Ioo (0 : Interval) 1 := by
    have hiLo : (0 : Fin (activeFaceSize p+2)) < i := by
      change 0 < i.val
      have hne : i.val ≠ 0 := fun he => hi0 (Fin.ext he)
      omega
    have hiHi : i < Fin.last (activeFaceSize p+1) := by
      change i.val < activeFaceSize p+1
      have hne : i.val ≠ activeFaceSize p+1 := fun he => hi1 (Fin.ext he)
      omega
    have hl := activeFaceMono p hiLo
    have hh := activeFaceMono p hiHi
    rw [activeFaceStart p] at hl
    rw [activeFaceEnd p] at hh
    exact ⟨hl,hh⟩
  have actualSourceRootOpenFace (e : zeroEdgeIndex)
      (hroot : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) = 0) :
      activeFaceMesh e.1 e.2.val.castSucc ∈ Set.Ioo (0 : Interval) 1 := by
    obtain ⟨i,hi,hi0,hi1⟩ := actualFaceZeroIsInternalMesh e.1 _ hroot
    exact hi ▸ actualInternalMeshNodeOpenParameter e.1 i hi0 hi1
  have actualTargetRootOpenFace (e : zeroEdgeIndex)
      (hroot : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) = 0) :
      activeFaceMesh e.1 e.2.val.succ ∈ Set.Ioo (0 : Interval) 1 := by
    obtain ⟨i,hi,hi0,hi1⟩ := actualFaceZeroIsInternalMesh e.1 _ hroot
    exact hi ▸ actualInternalMeshNodeOpenParameter e.1 i hi0 hi1
  have actualFaceZeroFromNegativeLeft (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0)
      (j : Fin (activeFaceSize p+1))
      (hj : activeFaceMesh p j.succ = t)
      (hneg : actualFaceHeight p (intervalMidpoint
        (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0) :
      ∃ e : zeroEdgeIndex, e.1 = p ∧ zeroEdge e 1 =
        squareCoordinates ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩ := by
    let e : zeroEdgeIndex := ⟨p,⟨j,hneg⟩⟩
    refine ⟨e,rfl,?_⟩
    have hn : (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 = 0 := by
      change (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 /
        (cellCenter p.1.val).val.1 = 0 at ht
      exact (div_eq_zero_iff.mp ht).resolve_right
        (cellCenterAxisNonzero p.1.val (activeCellAxis p.1))
    rw [zeroTarget e]
    have hz : (regularizedCellLoops p.1.val (zeroRight e).val).val.1 = 0 := by
      rw [zeroRightBoundary e]
      change (regularizedCellLoops p.1.val (boundaryFace p.2 (activeFaceMesh p j.succ))).val.1 = 0
      rw [hj]
      exact hn
    rw [activeFaceBoundaryFix p (zeroRight e) hz,zeroRightBoundary e]
    change squareCoordinates ⟨(boundaryFace p.2 (activeFaceMesh p j.succ)).val,_⟩ = _
    simp only [hj]
  have actualFaceZeroFromNegativeRight (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0)
      (j : Fin (activeFaceSize p+1))
      (hj : activeFaceMesh p j.castSucc = t)
      (hneg : actualFaceHeight p (intervalMidpoint
        (activeFaceMesh p j.castSucc) (activeFaceMesh p j.succ)) < 0) :
      ∃ e : zeroEdgeIndex, e.1 = p ∧ zeroEdge e 0 =
        squareCoordinates ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩ := by
    let e : zeroEdgeIndex := ⟨p,⟨j,hneg⟩⟩
    refine ⟨e,rfl,?_⟩
    have hn : (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 = 0 := by
      change (regularizedCellLoops p.1.val (boundaryFace p.2 t)).val.1 /
        (cellCenter p.1.val).val.1 = 0 at ht
      exact (div_eq_zero_iff.mp ht).resolve_right
        (cellCenterAxisNonzero p.1.val (activeCellAxis p.1))
    rw [zeroSource e]
    have hz : (regularizedCellLoops p.1.val (zeroLeft e).val).val.1 = 0 := by
      rw [zeroLeftBoundary e]
      change (regularizedCellLoops p.1.val (boundaryFace p.2 (activeFaceMesh p j.castSucc))).val.1 = 0
      rw [hj]
      exact hn
    rw [activeFaceBoundaryFix p (zeroLeft e) hz,zeroLeftBoundary e]
    change squareCoordinates ⟨(boundaryFace p.2 (activeFaceMesh p j.castSucc)).val,_⟩ = _
    simp only [hj]
  -- This constructs an actual cone zero-edge at the original crossing;
  -- no sign change or incidence parity is supplied by the caller.
  have actualTransverseFaceZeroCovered (p : activeCells × Fin 4)
      (t : Interval) (ht : actualFaceHeight p t = 0)
      (d : Curve S) (γ : C(Interval,S))
      (hγ : Set.InjOn γ (Set.Ioo 0 1))
      (hγimage : Set.range γ ⊆ d.image)
      (hcross : CrossesAt b.val d (γ t))
      (htrace : ∀ r : Interval, γ r = regularizedCells p.1.val
        (squareCoordinates ⟨(boundaryFace p.2 r).val,(boundaryFace p.2 r).property.le⟩)) :
      (∃ e : zeroEdgeIndex, e.1 = p ∧
        (zeroEdge e 0 = squareCoordinates
          ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩ ∨
         zeroEdge e 1 = squareCoordinates
          ⟨(boundaryFace p.2 t).val,(boundaryFace p.2 t).property.le⟩)) ∧
        (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
          actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
            (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.succ = t)).card +
        (Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
          actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
            (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.castSucc = t)).card = 1 := by
    obtain ⟨l,r,hl,hr,hlr,hlunique,hrunique⟩ := actualFaceZeroAdjacentIntervals p t ht
    let x := activeFaceMesh p l.castSucc
    let y := activeFaceMesh p r.succ
    let sl := intervalMidpoint x t
    let sr := intervalMidpoint t y
    have hxt : x < t := by
      rw [← hl]
      exact activeFaceMono p (by change l.val < l.val+1; omega)
    have hty : t < y := by
      rw [← hr]
      exact activeFaceMono p (by change r.val < r.val+1; omega)
    have htI : 0 < (t : ℝ) ∧ (t : ℝ) < 1 :=
      ⟨lt_of_le_of_lt x.property.1 hxt,lt_of_lt_of_le hty y.property.2⟩
    have hsl : sl ∈ Set.Ioo x t := by
      change x.val < (x.val+t.val)/2 ∧ (x.val+t.val)/2 < t.val
      have hh : x.val < t.val := hxt
      constructor <;> linarith only [hh]
    have hsr : sr ∈ Set.Ioo t y := by
      change t.val < (t.val+y.val)/2 ∧ (t.val+y.val)/2 < y.val
      have hh : t.val < y.val := hty
      constructor <;> linarith only [hh]
    have hnormal (q : Interval) : actualFaceHeight p q =
        (convexChart (chart p.1.val) (γ q)).1 / (cellCenter p.1.val).val.1 := by
      change (regularizedCellLoops p.1.val (boundaryFace p.2 q)).val.1 /
        (cellCenter p.1.val).val.1 = _
      rw [htrace q,actualCellBoundaryFormula]
    have hp : γ t ∈ (convexChart (chart p.1.val)).source := by
      rw [htrace t]
      exact regularizedCellRange p.1.val _
    have hleft : ∀ q, x < q → q < t → actualFaceHeight p q ≠ 0 := by
      intro q hq0 hq1
      apply actualFaceIntervalNoZero p l q hq0
      rwa [hl]
    have hright : ∀ q, t < q → q < y → actualFaceHeight p q ≠ 0 := by
      intro q hq0 hq1
      apply actualFaceIntervalNoZero p r q _ hq1
      rwa [hr]
    have hopposite := actual_transverse_adjacent_intervals_have_opposite_signs
      t htI γ hγ hγimage hcross (convexChart (chart p.1.val)) hp
      (activeCellAxis p.1) (actualFaceHeight p) (cellCenter p.1.val).val.1
      (cellCenterAxisNonzero p.1.val (activeCellAxis p.1)) hnormal
      x y sl sr hxt hty hsl hsr hleft hright
    let L := Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
      actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
        (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.succ = t)
    let R := Finset.univ.filter (fun j : Fin (activeFaceSize p+1) =>
      actualFaceHeight p (intervalMidpoint (activeFaceMesh p j.castSucc)
        (activeFaceMesh p j.succ)) < 0 ∧ activeFaceMesh p j.castSucc = t)
    have hL : L = if actualFaceHeight p sl < 0 then {l} else ∅ := by
      ext j
      simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,hlunique j]
      by_cases hn : actualFaceHeight p sl < 0
      · simp only [if_pos hn,Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨by simpa only [hl] using hn,rfl⟩
      · simp only [if_neg hn,Finset.notMem_empty,iff_false]
        rintro ⟨hj,rfl⟩
        exact hn (by simpa only [hl] using hj)
    have hR : R = if actualFaceHeight p sr < 0 then {r} else ∅ := by
      ext j
      simp only [R,Finset.mem_filter,Finset.mem_univ,true_and,hrunique j]
      by_cases hn : actualFaceHeight p sr < 0
      · simp only [if_pos hn,Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨by simpa only [hr] using hn,rfl⟩
      · simp only [if_neg hn,Finset.notMem_empty,iff_false]
        rintro ⟨hj,rfl⟩
        exact hn (by simpa only [hr] using hj)
    have hcard : L.card + R.card = 1 := by
      rw [hL,hR]
      by_cases hn : actualFaceHeight p sl < 0
      · have hrn := hopposite.mp hn
        simp only [if_pos hn,if_neg hrn,Finset.card_singleton,Finset.card_empty,Nat.add_zero]
      · have hrp : actualFaceHeight p sr < 0 := by
          by_contra hno
          exact hn (hopposite.mpr hno)
        simp only [if_neg hn,if_pos hrp,Finset.card_empty,Finset.card_singleton,Nat.zero_add]
    refine ⟨?_,hcard⟩
    by_cases hn : actualFaceHeight p sl < 0
    · have hneg : actualFaceHeight p (intervalMidpoint
          (activeFaceMesh p l.castSucc) (activeFaceMesh p l.succ)) < 0 := by
        simpa only [hl] using hn
      obtain ⟨e,he,hpos⟩ := actualFaceZeroFromNegativeLeft p t ht l hl hneg
      exact ⟨e,he,Or.inr hpos⟩
    · have hneg : actualFaceHeight p sr < 0 := by
        by_contra hno
        exact hn (hopposite.mpr hno)
      have hneg' : actualFaceHeight p (intervalMidpoint
          (activeFaceMesh p r.castSucc) (activeFaceMesh p r.succ)) < 0 := by
        simpa only [hr] using hneg
      obtain ⟨e,he,hpos⟩ := actualFaceZeroFromNegativeRight p t ht r hr hneg'
      exact ⟨e,he,Or.inl hpos⟩
  have actualBottomFaceZeroCovered (k : activeCells) (hk : k.val.1 = 0)
      (t : Interval) (hroot : actualFaceHeight (k,3) t = 0) :
      (∃ e : zeroEdgeIndex, e.1 = (k,3) ∧
        (zeroEdge e 0 = (0,t) ∨ zeroEdge e 1 = (0,t))) ∧
      (Finset.univ.filter (fun j : Fin (activeFaceSize (k,3)+1) =>
        actualFaceHeight (k,3) (intervalMidpoint
          (activeFaceMesh (k,3) j.castSucc) (activeFaceMesh (k,3) j.succ)) < 0 ∧
          activeFaceMesh (k,3) j.succ = t)).card +
      (Finset.univ.filter (fun j : Fin (activeFaceSize (k,3)+1) =>
        actualFaceHeight (k,3) (intervalMidpoint
          (activeFaceMesh (k,3) j.castSucc) (activeFaceMesh (k,3) j.succ)) < 0 ∧
          activeFaceMesh (k,3) j.castSucc = t)).card = 1 := by
    let γ : C(Interval,S) := (actualSpaceEdge 0 k.val.2).toContinuousMap
    have hformula (q : Interval) : ∃ u : Interval,
        u.val = (1-q.val)*(phaseGrid k.val.2.castSucc).val +
          q.val*(phaseGrid k.val.2.succ).val ∧
        γ q = intervalCurveLoopFrom a.val z₀ u := by
      obtain ⟨u,hu,hp⟩ := actualBoundarySpaceEdge 0 (Or.inl rfl) k.val.2 q
      refine ⟨u,hu,?_⟩
      change actualSpaceEdge 0 k.val.2 q = _
      have h0 : phaseGrid (0 : Fin (n+2)) = 0 := by simp [phaseGrid]
      rw [h0,Fzero] at hp
      exact hp
    obtain ⟨hγimage,hγinj,hγcross⟩ := actual_original_boundary_subarc_geometry
      a.val b.val ht z₀ (phaseGrid k.val.2.castSucc) (phaseGrid k.val.2.succ)
      (phaseStep k.val.2) γ hformula
    have hcoords (q : Interval) : squareCoordinates
        ⟨(boundaryFace 3 q).val,(boundaryFace 3 q).property.le⟩ = (0,q) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
        <;> ring
    have htrace (q : Interval) : γ q = regularizedCells k.val
        (squareCoordinates ⟨(boundaryFace 3 q).val,(boundaryFace 3 q).property.le⟩) := by
      rw [hcoords,(regularizedCellFaces k.val q).2.2.2,hk]
      rfl
    have hn : (regularizedCellLoops k.val (boundaryFace 3 t)).val.1 = 0 := by
      change (regularizedCellLoops k.val (boundaryFace 3 t)).val.1 /
        (cellCenter k.val).val.1 = 0 at hroot
      exact (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have htB : γ t ∈ b.val.image := by
      rw [htrace t]
      apply (activeCellAxis k _ (regularizedCellRange k.val _)).mpr
      rw [actualCellBoundaryFormula]
      exact hn
    have hactual := actualTransverseFaceZeroCovered (k,3) t hroot a.val γ
      hγinj hγimage (hγcross t htB) htrace
    obtain ⟨e,he,hpos⟩ := hactual.1
    refine ⟨⟨e,he,?_⟩,hactual.2⟩
    simpa only [hcoords] using hpos

  have actualTopFaceZeroCovered (k : activeCells) (hk : k.val.1 = Fin.last n)
      (t : Interval) (hroot : actualFaceHeight (k,1) t = 0) :
      (∃ e : zeroEdgeIndex, e.1 = (k,1) ∧
        (zeroEdge e 0 = (1,t) ∨ zeroEdge e 1 = (1,t))) ∧
      (Finset.univ.filter (fun j : Fin (activeFaceSize (k,1)+1) =>
        actualFaceHeight (k,1) (intervalMidpoint
          (activeFaceMesh (k,1) j.castSucc) (activeFaceMesh (k,1) j.succ)) < 0 ∧
          activeFaceMesh (k,1) j.succ = t)).card +
      (Finset.univ.filter (fun j : Fin (activeFaceSize (k,1)+1) =>
        actualFaceHeight (k,1) (intervalMidpoint
          (activeFaceMesh (k,1) j.castSucc) (activeFaceMesh (k,1) j.succ)) < 0 ∧
          activeFaceMesh (k,1) j.castSucc = t)).card = 1 := by
    let γ : C(Interval,S) := (actualSpaceEdge (Fin.last (n+1)) k.val.2).toContinuousMap
    have hformula (q : Interval) : ∃ u : Interval,
        u.val = (1-q.val)*(phaseGrid k.val.2.castSucc).val +
          q.val*(phaseGrid k.val.2.succ).val ∧
        γ q = intervalCurveLoopFrom endCurve z₀ u := by
      obtain ⟨u,hu,hp⟩ := actualBoundarySpaceEdge (Fin.last (n+1)) (Or.inr rfl) k.val.2 q
      refine ⟨u,hu,?_⟩
      change actualSpaceEdge (Fin.last (n+1)) k.val.2 q = _
      have h0 : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
      rw [h0,Fone] at hp
      exact hp
    obtain ⟨hγimage,hγinj,hγcross⟩ := actual_original_boundary_subarc_geometry
      endCurve b.val htEnd z₀ (phaseGrid k.val.2.castSucc) (phaseGrid k.val.2.succ)
      (phaseStep k.val.2) γ hformula
    have hcoords (q : Interval) : squareCoordinates
        ⟨(boundaryFace 1 q).val,(boundaryFace 1 q).property.le⟩ = (1,q) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
        <;> ring
    have htrace (q : Interval) : γ q = regularizedCells k.val
        (squareCoordinates ⟨(boundaryFace 1 q).val,(boundaryFace 1 q).property.le⟩) := by
      rw [hcoords,(regularizedCellFaces k.val q).2.1,hk,lastSucc]
      rfl
    have hn : (regularizedCellLoops k.val (boundaryFace 1 t)).val.1 = 0 := by
      change (regularizedCellLoops k.val (boundaryFace 1 t)).val.1 /
        (cellCenter k.val).val.1 = 0 at hroot
      exact (div_eq_zero_iff.mp hroot).resolve_right
        (cellCenterAxisNonzero k.val (activeCellAxis k))
    have htB : γ t ∈ b.val.image := by
      rw [htrace t]
      apply (activeCellAxis k _ (regularizedCellRange k.val _)).mpr
      rw [actualCellBoundaryFormula]
      exact hn
    have hactual := actualTransverseFaceZeroCovered (k,1) t hroot endCurve γ
      hγinj hγimage (hγcross t htB) htrace
    obtain ⟨e,he,hpos⟩ := hactual.1
    refine ⟨⟨e,he,?_⟩,hactual.2⟩
    simpa only [hcoords] using hpos
  have zeroParameterInterior (e : zeroEdgeIndex) (t : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) :
      ∃ (r : Interval) (z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops e.1.1.val z).val.1 / (cellCenter e.1.1.val).val.1 ≤ 0}),
        z.val = boundaryFace e.1.2 r ∧
        zeroEdge e t = activeFaceRadial e.1 z ∧
        r ∈ Set.Ioo (activeFaceMesh e.1 e.2.val.castSucc)
          (activeFaceMesh e.1 e.2.val.succ) ∧ r ∈ Set.Ioo (0 : Interval) 1 := by
    obtain ⟨r,z,hr,hz,hp,hneg⟩ := zeroParameter e t
    have hxy : (activeFaceMesh e.1 e.2.val.castSucc).val <
        (activeFaceMesh e.1 e.2.val.succ).val :=
      activeFaceMono e.1 (by change e.2.val.val < e.2.val.val+1; omega)
    have ht0 : 0 < t.val := ht.1
    have ht1 : t.val < 1 := ht.2
    have hleft : activeFaceMesh e.1 e.2.val.castSucc < r := by
      change (activeFaceMesh e.1 e.2.val.castSucc).val < r.val
      rw [hr]; nlinarith
    have hright : r < activeFaceMesh e.1 e.2.val.succ := by
      change r.val < (activeFaceMesh e.1 e.2.val.succ).val
      rw [hr]; nlinarith
    exact ⟨r,z,hz,hp,⟨hleft,hright⟩,
      ⟨lt_of_le_of_lt (activeFaceMesh e.1 e.2.val.castSucc).property.1 hleft,
       lt_of_lt_of_le hright (activeFaceMesh e.1 e.2.val.succ).property.2⟩⟩
  have zeroEdgeInteriorRadial (e : zeroEdgeIndex) (t : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) :
      ∃ u : {z : ℝ × ℝ // ‖z‖ ≤ 1},
        zeroEdge e t = squareCoordinates u ∧ ‖u.val‖ < 1 := by
    obtain ⟨r,z,hr,hz,hp,hneg⟩ := zeroParameter e t
    obtain ⟨u,hu,huf⟩ := activeFaceRadialFormula e.1 z
    refine ⟨u,hp.trans hu,?_⟩
    let h := (regularizedCellLoops e.1.1.val z.val).val.1 /
      (cellCenter e.1.1.val).val.1
    have hh : h < 0 := hneg ht
    have hd : 0 < 1-h := by linarith only [hh]
    have hpos : 0 < 1/(1-h) := div_pos zero_lt_one hd
    have hlt : 1/(1-h) < 1 := (div_lt_one hd).mpr (by linarith only [hh])
    rw [huf,norm_smul,Real.norm_eq_abs,abs_of_pos hpos,z.val.property,mul_one]
    exact hlt
  have zeroEdgeInteriorCoordinates (e : zeroEdgeIndex) (t : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) :
      (zeroEdge e t).1 ∈ Set.Ioo (0 : Interval) 1 ∧
      (zeroEdge e t).2 ∈ Set.Ioo (0 : Interval) 1 := by
    obtain ⟨u,hu,hn⟩ := zeroEdgeInteriorRadial e t ht
    rw [hu]
    have hb : -1 < u.val.1 ∧ u.val.1 < 1 ∧
        -1 < u.val.2 ∧ u.val.2 < 1 := by
      have hh : |u.val.1| < 1 ∧ |u.val.2| < 1 := by
        simpa only [Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using hn
      exact ⟨(abs_lt.mp hh.1).1,(abs_lt.mp hh.1).2,
        (abs_lt.mp hh.2).1,(abs_lt.mp hh.2).2⟩
    change (0 < (u.val.1+1)/2 ∧ (u.val.1+1)/2 < 1) ∧
      (0 < (u.val.2+1)/2 ∧ (u.val.2+1)/2 < 1)
    constructor <;> constructor <;> linarith only [hb.1,hb.2.1,hb.2.2.1,hb.2.2.2]
  -- zeroEdgeIndex is an ACTUAL finite index set. Every zeroEdge e is an
  -- embedded path in its actual selected cell whose image under that same
  -- cell filler lies on b. Endpoint labels retain the actual face mesh and
  -- radial formula; no geometric graph or innermost region is assumed.
  let cellToGlobal : Fin (n+1) × Fin (n+1) → C(Interval × Interval,Interval × Interval) := fun k =>
    ⟨fun z =>
      (⟨(1-z.1.val)*(phaseGrid k.1.castSucc).val+z.1.val*(phaseGrid k.1.succ).val,by
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2) (phaseGrid k.1.castSucc).property.1)
            (mul_nonneg z.1.property.1 (phaseGrid k.1.succ).property.1)
        · nlinarith [z.1.property.1,z.1.property.2,(phaseGrid k.1.castSucc).property.1,
            (phaseGrid k.1.castSucc).property.2,(phaseGrid k.1.succ).property.1,(phaseGrid k.1.succ).property.2]⟩,
       ⟨(1-z.2.val)*(phaseGrid k.2.castSucc).val+z.2.val*(phaseGrid k.2.succ).val,by
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.2.property.2) (phaseGrid k.2.castSucc).property.1)
            (mul_nonneg z.2.property.1 (phaseGrid k.2.succ).property.1)
        · nlinarith [z.2.property.1,z.2.property.2,(phaseGrid k.2.castSucc).property.1,
            (phaseGrid k.2.castSucc).property.2,(phaseGrid k.2.succ).property.1,(phaseGrid k.2.succ).property.2]⟩),by fun_prop⟩
  have cellToGlobalInCell (k : Fin (n+1) × Fin (n+1)) (z : Interval × Interval) :
      cellToGlobal k z ∈ cellDomain k := by
    have first : phaseGrid k.1.castSucc ≤ (cellToGlobal k z).1 ∧
        (cellToGlobal k z).1 ≤ phaseGrid k.1.succ := by
      have hh := (phaseStep k.1).le
      change (phaseGrid k.1.castSucc).val ≤
        (1-z.1.val)*(phaseGrid k.1.castSucc).val+z.1.val*(phaseGrid k.1.succ).val ∧
        (1-z.1.val)*(phaseGrid k.1.castSucc).val+z.1.val*(phaseGrid k.1.succ).val ≤ (phaseGrid k.1.succ).val
      constructor <;> nlinarith only [hh,z.1.property.1,z.1.property.2]
    have second : phaseGrid k.2.castSucc ≤ (cellToGlobal k z).2 ∧
        (cellToGlobal k z).2 ≤ phaseGrid k.2.succ := by
      have hh := (phaseStep k.2).le
      change (phaseGrid k.2.castSucc).val ≤
        (1-z.2.val)*(phaseGrid k.2.castSucc).val+z.2.val*(phaseGrid k.2.succ).val ∧
        (1-z.2.val)*(phaseGrid k.2.castSucc).val+z.2.val*(phaseGrid k.2.succ).val ≤ (phaseGrid k.2.succ).val
      constructor <;> nlinarith only [hh,z.2.property.1,z.2.property.2]
    exact ⟨first.1,first.2,second.1,second.2⟩
  have cellToGlobalInverse (k : Fin (n+1) × Fin (n+1)) (z : Interval × Interval) :
      cellCoordinates k (cellToGlobal k z) = z := by
    have hz := cellToGlobalInCell k z
    apply Prod.ext <;> apply Subtype.ext
    · change (localCoordinate k.1 ((cellToGlobal k z).1)).val = z.1.val
      rw [localCoordinateOnCell k.1 _ hz.1 hz.2.1]
      change (((1-z.1.val)*(phaseGrid k.1.castSucc).val+z.1.val*(phaseGrid k.1.succ).val)-
        (phaseGrid k.1.castSucc).val)/((phaseGrid k.1.succ).val-(phaseGrid k.1.castSucc).val) = z.1.val
      apply (div_eq_iff (ne_of_gt (sub_pos.mpr (phaseStep k.1)))).mpr
      ring
    · change (localCoordinate k.2 ((cellToGlobal k z).2)).val = z.2.val
      rw [localCoordinateOnCell k.2 _ hz.2.2.1 hz.2.2.2]
      change (((1-z.2.val)*(phaseGrid k.2.castSucc).val+z.2.val*(phaseGrid k.2.succ).val)-
        (phaseGrid k.2.castSucc).val)/((phaseGrid k.2.succ).val-(phaseGrid k.2.castSucc).val) = z.2.val
      apply (div_eq_iff (ne_of_gt (sub_pos.mpr (phaseStep k.2)))).mpr
      ring
  have cellToGlobalEmbedding (k : Fin (n+1) × Fin (n+1)) : Topology.IsEmbedding (cellToGlobal k) :=
    ((cellToGlobal k).continuous.isClosedEmbedding (fun z w he => by
      have hh := congrArg (cellCoordinates k) he
      simpa only [cellToGlobalInverse] using hh)).isEmbedding
  let globalZeroEdge (e : zeroEdgeIndex) : C(Interval,Interval × Interval) :=
    (cellToGlobal e.1.1.val).comp (zeroEdge e)
  have globalZeroEdgeEmbedding (e : zeroEdgeIndex) : Topology.IsEmbedding (globalZeroEdge e) :=
    (cellToGlobalEmbedding e.1.1.val).comp (zeroEdgeEmbedding e)
  have globalZeroEdgeOnComparison (e : zeroEdgeIndex) (t : Interval) :
      regularizedTrace (globalZeroEdge e t) ∈ b.val.image := by
    change regularizedTrace (cellToGlobal e.1.1.val (zeroEdge e t)) ∈ b.val.image
    rw [regularizedOnCells _ _ (cellToGlobalInCell _ _),cellToGlobalInverse]
    exact zeroEdgeOnComparison e t
  have affineInterior (i : Fin (n+1)) (r : Interval)
      (hr : r ∈ Set.Ioo (0 : Interval) 1) :
      (phaseGrid i.castSucc).val <
        (1-r.val)*(phaseGrid i.castSucc).val+r.val*(phaseGrid i.succ).val ∧
      (1-r.val)*(phaseGrid i.castSucc).val+r.val*(phaseGrid i.succ).val <
        (phaseGrid i.succ).val := by
    have hi : (phaseGrid i.castSucc).val < (phaseGrid i.succ).val := phaseStep i
    have hr0 : 0 < r.val := hr.1
    have hr1 : r.val < 1 := hr.2
    constructor <;> nlinarith only [hi,hr0,hr1]
  have globalZeroEdgeInterior (e : zeroEdgeIndex) (t : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) :
      (globalZeroEdge e t).1 ∈ Set.Ioo (phaseGrid e.1.1.val.1.castSucc)
        (phaseGrid e.1.1.val.1.succ) ∧
      (globalZeroEdge e t).2 ∈ Set.Ioo (phaseGrid e.1.1.val.2.castSucc)
        (phaseGrid e.1.1.val.2.succ) := by
    obtain ⟨hx,hy⟩ := zeroEdgeInteriorCoordinates e t ht
    exact ⟨affineInterior _ _ hx,affineInterior _ _ hy⟩
  have phaseOpenIntervalsUnique (i j : Fin (n+1)) (r : Interval)
      (hi : r ∈ Set.Ioo (phaseGrid i.castSucc) (phaseGrid i.succ))
      (hj : r ∈ Set.Ioo (phaseGrid j.castSucc) (phaseGrid j.succ)) : i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hle : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
      have hgrid := phaseGridStrict.monotone hle
      exact False.elim (not_lt_of_ge (le_trans hgrid hj.1.le) hi.2)
    · exact hij
    · have hle : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact hji
      have hgrid := phaseGridStrict.monotone hle
      exact False.elim (not_lt_of_ge (le_trans hgrid hi.1.le) hj.2)
  have phaseOpenClosedUnique (i j : Fin (n+1)) (r : Interval)
      (hi : r ∈ Set.Ioo (phaseGrid i.castSucc) (phaseGrid i.succ))
      (hj : r ∈ Set.Icc (phaseGrid j.castSucc) (phaseGrid j.succ)) : i = j := by
    rcases lt_trichotomy i j with hij | hij | hji
    · have hle : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
      have hm := phaseGridStrict.monotone hle
      exact False.elim (not_lt_of_ge (le_trans hm hj.1) hi.2)
    · exact hij
    · have hle : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact hji
      have hm := phaseGridStrict.monotone hle
      exact False.elim (not_lt_of_ge (le_trans hj.2 hm) hi.1)
  have globalZeroClosedCoordinates (e : zeroEdgeIndex) (t : Interval) :
      (globalZeroEdge e t).1 ∈ Set.Icc (phaseGrid e.1.1.val.1.castSucc)
        (phaseGrid e.1.1.val.1.succ) ∧
      (globalZeroEdge e t).2 ∈ Set.Icc (phaseGrid e.1.1.val.2.castSucc)
        (phaseGrid e.1.1.val.2.succ) := by
    have hh := cellToGlobalInCell e.1.1.val (zeroEdge e t)
    exact ⟨⟨hh.1,hh.2.1⟩,⟨hh.2.2.1,hh.2.2.2⟩⟩
  -- No edge from another grid cell can contribute to an original-boundary
  -- root lying in this open phase interval.
  -- An actual strict grid node belongs only to its two adjacent closed cells.
  have phaseClosedCellAtGridNode (i : Fin (n+2)) (j : Fin (n+1))
      (hi : phaseGrid i ∈ Set.Icc (phaseGrid j.castSucc) (phaseGrid j.succ)) :
      j.castSucc = i ∨ j.succ = i := by
    have hlo := phaseGridStrict.le_iff_le.mp hi.1
    have hhi := phaseGridStrict.le_iff_le.mp hi.2
    change j.val ≤ i.val at hlo
    change i.val ≤ j.val+1 at hhi
    have he : i.val = j.val ∨ i.val = j.val+1 := by omega
    rcases he with he | he
    · exact Or.inl (Fin.ext he.symm)
    · exact Or.inr (Fin.ext he.symm)
  have actualBottomCellIdentification (e : zeroEdgeIndex) (r : Interval)
      (j : Fin (n+1)) (t : Interval)
      (ht : t ∈ Set.Ioo (phaseGrid j.castSucc) (phaseGrid j.succ))
      (he : globalZeroEdge e r = (0,t)) : e.1.1.val = (0,j) := by
    have hc := globalZeroClosedCoordinates e r
    rw [he] at hc
    have hz : phaseGrid (0 : Fin (n+2)) = 0 := by simp [phaseGrid]
    have hg : phaseGrid e.1.1.val.1.castSucc = phaseGrid 0 := by
      rw [hz]
      exact le_antisymm hc.1.1 (phaseGrid e.1.1.val.1.castSucc).property.1
    have hi := congrArg Fin.val (phaseGridStrict.injective hg)
    have hi' : e.1.1.val.1 = 0 := by
      apply Fin.ext
      exact hi
    have hj := phaseOpenClosedUnique j e.1.1.val.2 t ht hc.2
    exact Prod.ext hi' hj.symm
  have actualTopCellIdentification (e : zeroEdgeIndex) (r : Interval)
      (j : Fin (n+1)) (t : Interval)
      (ht : t ∈ Set.Ioo (phaseGrid j.castSucc) (phaseGrid j.succ))
      (he : globalZeroEdge e r = (1,t)) : e.1.1.val = (Fin.last n,j) := by
    have hc := globalZeroClosedCoordinates e r
    rw [he] at hc
    have hz : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
    have hg : phaseGrid e.1.1.val.1.succ = phaseGrid (Fin.last (n+1)) := by
      rw [hz]
      exact le_antisymm (phaseGrid e.1.1.val.1.succ).property.2 hc.1.2
    have hi := congrArg Fin.val (phaseGridStrict.injective hg)
    have hi' : e.1.1.val.1 = Fin.last n := by
      apply Fin.ext
      change e.1.1.val.1.val + 1 = n+1 at hi
      change e.1.1.val.1.val = n
      omega
    have hj := phaseOpenClosedUnique j e.1.1.val.2 t ht hc.2
    exact Prod.ext hi' hj.symm
  have actualBottomRootCell (k : activeCells) (hk : k.val.1 = 0)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (e : zeroEdgeIndex) (r : Interval)
      (he : globalZeroEdge e r = cellToGlobal k.val (0,u)) : e.1.1 = k := by
    let t := (cellToGlobal k.val (0,u)).2
    have htime : (cellToGlobal k.val (0,u)).1 = 0 := by
      apply Subtype.ext
      change (1-(0 : ℝ))*(phaseGrid k.val.1.castSucc).val+
        (0 : ℝ)*(phaseGrid k.val.1.succ).val = 0
      simp [hk,phaseGrid]
    have hphase : t ∈ Set.Ioo (phaseGrid k.val.2.castSucc) (phaseGrid k.val.2.succ) := by
      exact affineInterior k.val.2 u hu
    have hpoint : cellToGlobal k.val (0,u) = (0,t) := Prod.ext htime rfl
    have hc := actualBottomCellIdentification e r k.val.2 t hphase (he.trans hpoint)
    apply Subtype.ext
    have hkpair : k.val = (0,k.val.2) := Prod.ext hk rfl
    exact hc.trans hkpair.symm
  have actualTopRootCell (k : activeCells) (hk : k.val.1 = Fin.last n)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (e : zeroEdgeIndex) (r : Interval)
      (he : globalZeroEdge e r = cellToGlobal k.val (1,u)) : e.1.1 = k := by
    let t := (cellToGlobal k.val (1,u)).2
    have htime : (cellToGlobal k.val (1,u)).1 = 1 := by
      apply Subtype.ext
      change (1-(1 : ℝ))*(phaseGrid k.val.1.castSucc).val+
        (1 : ℝ)*(phaseGrid k.val.1.succ).val = 1
      simp [hk,phaseGrid]
    have hphase : t ∈ Set.Ioo (phaseGrid k.val.2.castSucc) (phaseGrid k.val.2.succ) := by
      exact affineInterior k.val.2 u hu
    have hpoint : cellToGlobal k.val (1,u) = (1,t) := Prod.ext htime rfl
    have hc := actualTopCellIdentification e r k.val.2 t hphase (he.trans hpoint)
    apply Subtype.ext
    have hkpair : k.val = (Fin.last n,k.val.2) := Prod.ext hk rfl
    exact hc.trans hkpair.symm
  have actualBottomRootSourceIndex (k : activeCells) (hk : k.val.1 = 0)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : actualFaceHeight (k,3) u = 0) (e : zeroEdgeIndex) :
      globalZeroEdge e 0 = cellToGlobal k.val (0,u) ↔
        e.1 = (k,3) ∧ activeFaceMesh e.1 e.2.val.castSucc = u := by
    have hcoords : squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    constructor
    · intro he
      have hc := actualBottomRootCell k hk u hu e 0 he
      rcases e with ⟨⟨l,j⟩,x⟩
      change l = k at hc
      subst l
      have hz : zeroEdge ⟨(k,j),x⟩ 0 = (0,u) :=
        (cellToGlobalEmbedding k.val).injective he
      have hj := actualOpenRootSourceFaceUnique k 3 j u hu hroot x (hz.trans hcoords.symm)
      subst j
      refine ⟨rfl,?_⟩
      exact (actualFaceRootSourceIncidence (k,3) u hroot x.val x.property).mp
        (hz.trans hcoords.symm)
    · rintro ⟨hp,hm⟩
      rcases e with ⟨⟨l,j⟩,x⟩
      have hl : l = k := congrArg Prod.fst hp
      have hj : j = 3 := congrArg Prod.snd hp
      subst l
      subst j
      have hz := (actualFaceRootSourceIncidence (k,3) u hroot x.val x.property).mpr hm
      have he : zeroEdge ⟨(k,3),x⟩ 0 = (0,u) := hz.trans hcoords
      exact congrArg (cellToGlobal k.val) he
  have actualBottomRootTargetIndex (k : activeCells) (hk : k.val.1 = 0)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : actualFaceHeight (k,3) u = 0) (e : zeroEdgeIndex) :
      globalZeroEdge e 1 = cellToGlobal k.val (0,u) ↔
        e.1 = (k,3) ∧ activeFaceMesh e.1 e.2.val.succ = u := by
    have hcoords : squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    constructor
    · intro he
      have hc := actualBottomRootCell k hk u hu e 1 he
      rcases e with ⟨⟨l,j⟩,x⟩
      change l = k at hc
      subst l
      have hz : zeroEdge ⟨(k,j),x⟩ 1 = (0,u) :=
        (cellToGlobalEmbedding k.val).injective he
      have hj := actualOpenRootTargetFaceUnique k 3 j u hu hroot x (hz.trans hcoords.symm)
      subst j
      refine ⟨rfl,?_⟩
      exact (actualFaceRootTargetIncidence (k,3) u hroot x.val x.property).mp
        (hz.trans hcoords.symm)
    · rintro ⟨hp,hm⟩
      rcases e with ⟨⟨l,j⟩,x⟩
      have hl : l = k := congrArg Prod.fst hp
      have hj : j = 3 := congrArg Prod.snd hp
      subst l
      subst j
      have hz := (actualFaceRootTargetIncidence (k,3) u hroot x.val x.property).mpr hm
      have he : zeroEdge ⟨(k,3),x⟩ 1 = (0,u) := hz.trans hcoords
      exact congrArg (cellToGlobal k.val) he
  have actualTopRootSourceIndex (k : activeCells) (hk : k.val.1 = Fin.last n)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : actualFaceHeight (k,1) u = 0) (e : zeroEdgeIndex) :
      globalZeroEdge e 0 = cellToGlobal k.val (1,u) ↔
        e.1 = (k,1) ∧ activeFaceMesh e.1 e.2.val.castSucc = u := by
    have hcoords : squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    constructor
    · intro he
      have hc := actualTopRootCell k hk u hu e 0 he
      rcases e with ⟨⟨l,j⟩,x⟩
      change l = k at hc
      subst l
      have hz : zeroEdge ⟨(k,j),x⟩ 0 = (1,u) :=
        (cellToGlobalEmbedding k.val).injective he
      have hj := actualOpenRootSourceFaceUnique k 1 j u hu hroot x (hz.trans hcoords.symm)
      subst j
      refine ⟨rfl,?_⟩
      exact (actualFaceRootSourceIncidence (k,1) u hroot x.val x.property).mp
        (hz.trans hcoords.symm)
    · rintro ⟨hp,hm⟩
      rcases e with ⟨⟨l,j⟩,x⟩
      have hl : l = k := congrArg Prod.fst hp
      have hj : j = 1 := congrArg Prod.snd hp
      subst l
      subst j
      have hz := (actualFaceRootSourceIncidence (k,1) u hroot x.val x.property).mpr hm
      have he : zeroEdge ⟨(k,1),x⟩ 0 = (1,u) := hz.trans hcoords
      exact congrArg (cellToGlobal k.val) he
  have actualTopRootTargetIndex (k : activeCells) (hk : k.val.1 = Fin.last n)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : actualFaceHeight (k,1) u = 0) (e : zeroEdgeIndex) :
      globalZeroEdge e 1 = cellToGlobal k.val (1,u) ↔
        e.1 = (k,1) ∧ activeFaceMesh e.1 e.2.val.succ = u := by
    have hcoords : squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    constructor
    · intro he
      have hc := actualTopRootCell k hk u hu e 1 he
      rcases e with ⟨⟨l,j⟩,x⟩
      change l = k at hc
      subst l
      have hz : zeroEdge ⟨(k,j),x⟩ 1 = (1,u) :=
        (cellToGlobalEmbedding k.val).injective he
      have hj := actualOpenRootTargetFaceUnique k 1 j u hu hroot x (hz.trans hcoords.symm)
      subst j
      refine ⟨rfl,?_⟩
      exact (actualFaceRootTargetIncidence (k,1) u hroot x.val x.property).mp
        (hz.trans hcoords.symm)
    · rintro ⟨hp,hm⟩
      rcases e with ⟨⟨l,j⟩,x⟩
      have hl : l = k := congrArg Prod.fst hp
      have hj : j = 1 := congrArg Prod.snd hp
      subst l
      subst j
      have hz := (actualFaceRootTargetIncidence (k,1) u hroot x.val x.property).mpr hm
      have he : zeroEdge ⟨(k,1),x⟩ 1 = (1,u) := hz.trans hcoords
      exact congrArg (cellToGlobal k.val) he
  have actualBoundaryRootTraceMembership (k : activeCells) (i : Fin 4) (u : Interval) :
      actualFaceHeight (k,i) u = 0 ↔
        regularizedTrace (cellToGlobal k.val (squareCoordinates
          ⟨(boundaryFace i u).val,(boundaryFace i u).property.le⟩)) ∈ b.val.image := by
    rw [regularizedOnCells _ _ (cellToGlobalInCell _ _),cellToGlobalInverse]
    rw [activeCellAxis k _ (regularizedCellRange k.val _),actualCellBoundaryFormula]
    change (regularizedCellLoops k.val (boundaryFace i u)).val.1 /
      (cellCenter k.val).val.1 = 0 ↔
      (regularizedCellLoops k.val (boundaryFace i u)).val.1 = 0
    exact div_eq_zero_iff.trans (or_iff_left
      (cellCenterAxisNonzero k.val (activeCellAxis k)))
  have actualCellActiveAtRoot (k : Fin (n+1) × Fin (n+1)) (z : Interval × Interval)
      (hz : z ∈ cellDomain k) (hroot : regularizedTrace z ∈ b.val.image) : k ∈ activeCells := by
    have hchart : regularizedTrace z ∈ chartDomain (chart k) := by
      rw [regularizedOnCells k z hz]
      exact regularizedCellRange k _
    change ¬Disjoint (chartDomain (chart k)) b.val.image
    intro hd
    exact Set.disjoint_left.mp hd hchart hroot
  have actualRootFirstPhaseSeamNeighborActive (k : activeCells)
      (hk : k.val.2 = 0) (u : Interval)
      (hroot : actualFaceHeight (k,0) u = 0) :
      ∃ l : activeCells, k.val.1 = l.val.1 ∧ l.val.2 = Fin.last n ∧
        actualFaceHeight (l,2) u = 0 := by
    let l0 : Fin (n+1) × Fin (n+1) := (k.val.1,Fin.last n)
    let t : Interval := (cellToGlobal k.val (u,0)).1
    have hkphase : (cellToGlobal k.val (u,0)).2 = 0 := by
      apply Subtype.ext
      change (1-(0 : ℝ))*(phaseGrid k.val.2.castSucc).val+
        (0 : ℝ)*(phaseGrid k.val.2.succ).val = 0
      have hi : k.val.2.castSucc = (0 : Fin (n+2)) := by
        rw [hk]
        rfl
      rw [hi]
      simp [phaseGrid]
    have hlphase : (cellToGlobal l0 (u,1)).2 = 1 := by
      apply Subtype.ext
      change (1-(1 : ℝ))*(phaseGrid (Fin.last n).castSucc).val+
        (1 : ℝ)*(phaseGrid (Fin.last n).succ).val = 1
      rw [lastSucc]
      simp [phaseGrid]
    have hleft : cellToGlobal k.val (u,0) = (t,0) := Prod.ext rfl hkphase
    have hright : cellToGlobal l0 (u,1) = (t,1) := Prod.ext rfl hlphase
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hb := (actualBoundaryRootTraceMembership k 0 u).mp hroot
    rw [hcoordk,hleft,regularizedSeam t,←hright] at hb
    have hlact := actualCellActiveAtRoot l0 (cellToGlobal l0 (u,1))
      (cellToGlobalInCell l0 (u,1)) hb
    let l : activeCells := ⟨l0,hlact⟩
    refine ⟨l,rfl,rfl,?_⟩
    apply (actualBoundaryRootTraceMembership l 2 u).mpr
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    rw [hcoordl]
    exact hb
  have actualRootLastPhaseSeamNeighborActive (k : activeCells)
      (hk : k.val.2 = Fin.last n) (u : Interval)
      (hroot : actualFaceHeight (k,2) u = 0) :
      ∃ l : activeCells, k.val.1 = l.val.1 ∧ l.val.2 = 0 ∧
        actualFaceHeight (l,0) u = 0 := by
    let l0 : Fin (n+1) × Fin (n+1) := (k.val.1,0)
    let t : Interval := (cellToGlobal k.val (u,1)).1
    have hkphase : (cellToGlobal k.val (u,1)).2 = 1 := by
      apply Subtype.ext
      change (1-(1 : ℝ))*(phaseGrid k.val.2.castSucc).val+
        (1 : ℝ)*(phaseGrid k.val.2.succ).val = 1
      rw [hk,lastSucc]
      simp [phaseGrid]
    have hlphase : (cellToGlobal l0 (u,0)).2 = 0 := by
      apply Subtype.ext
      change (1-(0 : ℝ))*(phaseGrid (0 : Fin (n+1)).castSucc).val+
        (0 : ℝ)*(phaseGrid (0 : Fin (n+1)).succ).val = 0
      simp [phaseGrid]
    have hleft : cellToGlobal k.val (u,1) = (t,1) := Prod.ext rfl hkphase
    have hright : cellToGlobal l0 (u,0) = (t,0) := Prod.ext rfl hlphase
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hb := (actualBoundaryRootTraceMembership k 2 u).mp hroot
    rw [hcoordk,hleft,←regularizedSeam t,←hright] at hb
    have hlact := actualCellActiveAtRoot l0 (cellToGlobal l0 (u,0))
      (cellToGlobalInCell l0 (u,0)) hb
    let l : activeCells := ⟨l0,hlact⟩
    refine ⟨l,rfl,rfl,?_⟩
    apply (actualBoundaryRootTraceMembership l 0 u).mpr
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    rw [hcoordl]
    exact hb
  have actualTimeGridNeighborCellPoint (k l : Fin (n+1) × Fin (n+1))
      (htime : k.1.succ = l.1.castSucc) (hphase : k.2 = l.2)
      (u : Interval) : cellToGlobal k (1,u) = cellToGlobal l (0,u) := by
    apply Prod.ext <;> apply Subtype.ext
    · change (1-(1 : ℝ))*(phaseGrid k.1.castSucc).val+
        (1 : ℝ)*(phaseGrid k.1.succ).val =
        (1-(0 : ℝ))*(phaseGrid l.1.castSucc).val+
        (0 : ℝ)*(phaseGrid l.1.succ).val
      rw [htime]
      ring
    · change (1-u.val)*(phaseGrid k.2.castSucc).val+u.val*(phaseGrid k.2.succ).val =
        (1-u.val)*(phaseGrid l.2.castSucc).val+u.val*(phaseGrid l.2.succ).val
      rw [hphase]
  have actualRootRightTimeNeighborActive (k : activeCells)
      (hk : k.val.1 ≠ Fin.last n) (u : Interval)
      (hroot : actualFaceHeight (k,1) u = 0) :
      ∃ l : activeCells, k.val.1.succ = l.val.1.castSucc ∧
        k.val.2 = l.val.2 ∧ actualFaceHeight (l,3) u = 0 := by
    have hindex : k.val.1.val < n := by
      have hneq : k.val.1.val ≠ n := by
        intro he
        exact hk (Fin.ext he)
      have hb := k.val.1.isLt
      omega
    let j : Fin (n+1) := ⟨k.val.1.val+1,by omega⟩
    let l0 : Fin (n+1) × Fin (n+1) := (j,k.val.2)
    have htime : k.val.1.succ = l0.1.castSucc := by
      apply Fin.ext
      rfl
    have hpoint := actualTimeGridNeighborCellPoint k.val l0 htime rfl u
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hb := (actualBoundaryRootTraceMembership k 1 u).mp hroot
    rw [hcoordk,hpoint] at hb
    have hlact := actualCellActiveAtRoot l0 (cellToGlobal l0 (0,u))
      (cellToGlobalInCell l0 (0,u)) hb
    let l : activeCells := ⟨l0,hlact⟩
    refine ⟨l,htime,rfl,?_⟩
    apply (actualBoundaryRootTraceMembership l 3 u).mpr
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    rw [hcoordl]
    exact hb
  have actualRootLeftTimeNeighborActive (k : activeCells)
      (hk : k.val.1 ≠ 0) (u : Interval)
      (hroot : actualFaceHeight (k,3) u = 0) :
      ∃ l : activeCells, l.val.1.succ = k.val.1.castSucc ∧
        l.val.2 = k.val.2 ∧ actualFaceHeight (l,1) u = 0 := by
    have hindex : 0 < k.val.1.val := by
      by_contra he
      have hv : k.val.1.val = 0 := by omega
      exact hk (Fin.ext hv)
    let j : Fin (n+1) := ⟨k.val.1.val-1,by have hb := k.val.1.isLt; omega⟩
    let l0 : Fin (n+1) × Fin (n+1) := (j,k.val.2)
    have htime : l0.1.succ = k.val.1.castSucc := by
      apply Fin.ext
      change k.val.1.val-1+1 = k.val.1.val
      omega
    have hpoint := actualTimeGridNeighborCellPoint l0 k.val htime rfl u
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hb := (actualBoundaryRootTraceMembership k 3 u).mp hroot
    rw [hcoordk,←hpoint] at hb
    have hlact := actualCellActiveAtRoot l0 (cellToGlobal l0 (1,u))
      (cellToGlobalInCell l0 (1,u)) hb
    let l : activeCells := ⟨l0,hlact⟩
    refine ⟨l,htime,rfl,?_⟩
    apply (actualBoundaryRootTraceMembership l 1 u).mpr
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    rw [hcoordl]
    exact hb
  have actualPhaseGridNeighborCellPoint (k l : Fin (n+1) × Fin (n+1))
      (htime : k.1 = l.1) (hphase : k.2.succ = l.2.castSucc)
      (u : Interval) : cellToGlobal k (u,1) = cellToGlobal l (u,0) := by
    apply Prod.ext <;> apply Subtype.ext
    · change (1-u.val)*(phaseGrid k.1.castSucc).val+u.val*(phaseGrid k.1.succ).val =
        (1-u.val)*(phaseGrid l.1.castSucc).val+u.val*(phaseGrid l.1.succ).val
      rw [htime]
    · change (1-(1 : ℝ))*(phaseGrid k.2.castSucc).val+
        (1 : ℝ)*(phaseGrid k.2.succ).val =
        (1-(0 : ℝ))*(phaseGrid l.2.castSucc).val+
        (0 : ℝ)*(phaseGrid l.2.succ).val
      rw [hphase]
      ring
  have actualRootUpperPhaseNeighborActive (k : activeCells)
      (hk : k.val.2 ≠ Fin.last n) (u : Interval)
      (hroot : actualFaceHeight (k,2) u = 0) :
      ∃ l : activeCells, k.val.2.succ = l.val.2.castSucc ∧
        k.val.1 = l.val.1 ∧ actualFaceHeight (l,0) u = 0 := by
    have hindex : k.val.2.val < n := by
      have hneq : k.val.2.val ≠ n := by
        intro he
        exact hk (Fin.ext he)
      have hb := k.val.2.isLt
      omega
    let j : Fin (n+1) := ⟨k.val.2.val+1,by omega⟩
    let l0 : Fin (n+1) × Fin (n+1) := (k.val.1,j)
    have hphase : k.val.2.succ = l0.2.castSucc := by
      apply Fin.ext
      rfl
    have hpoint := actualPhaseGridNeighborCellPoint k.val l0 rfl hphase u
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hb := (actualBoundaryRootTraceMembership k 2 u).mp hroot
    rw [hcoordk,hpoint] at hb
    have hlact := actualCellActiveAtRoot l0 (cellToGlobal l0 (u,0))
      (cellToGlobalInCell l0 (u,0)) hb
    let l : activeCells := ⟨l0,hlact⟩
    refine ⟨l,hphase,rfl,?_⟩
    apply (actualBoundaryRootTraceMembership l 0 u).mpr
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    rw [hcoordl]
    exact hb
  have actualRootLowerPhaseNeighborActive (k : activeCells)
      (hk : k.val.2 ≠ 0) (u : Interval)
      (hroot : actualFaceHeight (k,0) u = 0) :
      ∃ l : activeCells, l.val.2.succ = k.val.2.castSucc ∧
        l.val.1 = k.val.1 ∧ actualFaceHeight (l,2) u = 0 := by
    have hindex : 0 < k.val.2.val := by
      by_contra he
      have hv : k.val.2.val = 0 := by omega
      exact hk (Fin.ext hv)
    let j : Fin (n+1) := ⟨k.val.2.val-1,by have hb := k.val.2.isLt; omega⟩
    let l0 : Fin (n+1) × Fin (n+1) := (k.val.1,j)
    have hphase : l0.2.succ = k.val.2.castSucc := by
      apply Fin.ext
      change k.val.2.val-1+1 = k.val.2.val
      omega
    have hpoint := actualPhaseGridNeighborCellPoint l0 k.val rfl hphase u
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hb := (actualBoundaryRootTraceMembership k 0 u).mp hroot
    rw [hcoordk,←hpoint] at hb
    have hlact := actualCellActiveAtRoot l0 (cellToGlobal l0 (u,1))
      (cellToGlobalInCell l0 (u,1)) hb
    let l : activeCells := ⟨l0,hlact⟩
    refine ⟨l,hphase,rfl,?_⟩
    apply (actualBoundaryRootTraceMembership l 2 u).mpr
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    rw [hcoordl]
    exact hb
  have actualTimeNeighborCellPoint (k l : activeCells)
      (htime : k.val.1.succ = l.val.1.castSucc) (hphase : k.val.2 = l.val.2)
      (u : Interval) : cellToGlobal k.val (1,u) = cellToGlobal l.val (0,u) := by
    apply Prod.ext <;> apply Subtype.ext
    · change (1-(1 : ℝ))*(phaseGrid k.val.1.castSucc).val+
        (1 : ℝ)*(phaseGrid k.val.1.succ).val =
        (1-(0 : ℝ))*(phaseGrid l.val.1.castSucc).val+
        (0 : ℝ)*(phaseGrid l.val.1.succ).val
      rw [htime]
      ring
    · change (1-u.val)*(phaseGrid k.val.2.castSucc).val+u.val*(phaseGrid k.val.2.succ).val =
        (1-u.val)*(phaseGrid l.val.2.castSucc).val+u.val*(phaseGrid l.val.2.succ).val
      rw [hphase]
  have actualPhaseNeighborCellPoint (k l : activeCells)
      (htime : k.val.1 = l.val.1) (hphase : k.val.2.succ = l.val.2.castSucc)
      (u : Interval) : cellToGlobal k.val (u,1) = cellToGlobal l.val (u,0) := by
    apply Prod.ext <;> apply Subtype.ext
    · change (1-u.val)*(phaseGrid k.val.1.castSucc).val+u.val*(phaseGrid k.val.1.succ).val =
        (1-u.val)*(phaseGrid l.val.1.castSucc).val+u.val*(phaseGrid l.val.1.succ).val
      rw [htime]
    · change (1-(1 : ℝ))*(phaseGrid k.val.2.castSucc).val+
        (1 : ℝ)*(phaseGrid k.val.2.succ).val =
        (1-(0 : ℝ))*(phaseGrid l.val.2.castSucc).val+
        (0 : ℝ)*(phaseGrid l.val.2.succ).val
      rw [hphase]
      ring
  have actualGridRootSquareCellAlternatives (k l : activeCells) (u : Interval)
      (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (htime : k.val.1.succ = l.val.1.castSucc) (hphase : k.val.2 = l.val.2)
      (e : zeroEdgeIndex) (r : Interval)
      (he : globalZeroEdge e r = cellToGlobal k.val (1,u)) :
      e.1.1 = k ∨ e.1.1 = l := by
    have hc := globalZeroClosedCoordinates e r
    rw [he] at hc
    have htimecoord : (cellToGlobal k.val (1,u)).1 = phaseGrid k.val.1.succ := by
      apply Subtype.ext
      change (1-(1 : ℝ))*(phaseGrid k.val.1.castSucc).val+
        (1 : ℝ)*(phaseGrid k.val.1.succ).val = (phaseGrid k.val.1.succ).val
      ring
    have hphaseopen : (cellToGlobal k.val (1,u)).2 ∈
        Set.Ioo (phaseGrid k.val.2.castSucc) (phaseGrid k.val.2.succ) := by
      exact affineInterior k.val.2 u hu
    rw [htimecoord] at hc
    have hp := phaseOpenClosedUnique k.val.2 e.1.1.val.2 _ hphaseopen hc.2
    rcases phaseClosedCellAtGridNode k.val.1.succ e.1.1.val.1 hc.1 with hi | hi
    · right
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.castSucc_injective
        exact hi.trans htime
      · exact hp.symm.trans hphase
    · left
      apply Subtype.ext
      have htimeEq : e.1.1.val.1 = k.val.1 := by
        apply Fin.ext
        have hv := congrArg (fun j : Fin (n+2) => j.val) hi
        change e.1.1.val.1.val+1 = k.val.1.val+1 at hv
        omega
      exact Prod.ext htimeEq hp.symm
  have actualPhaseGridRootSquareCellAlternatives (k l : activeCells) (u : Interval)
      (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (htime : k.val.1 = l.val.1) (hphase : k.val.2.succ = l.val.2.castSucc)
      (e : zeroEdgeIndex) (r : Interval)
      (he : globalZeroEdge e r = cellToGlobal k.val (u,1)) :
      e.1.1 = k ∨ e.1.1 = l := by
    have hc := globalZeroClosedCoordinates e r
    rw [he] at hc
    have hphasecoord : (cellToGlobal k.val (u,1)).2 = phaseGrid k.val.2.succ := by
      apply Subtype.ext
      change (1-(1 : ℝ))*(phaseGrid k.val.2.castSucc).val+
        (1 : ℝ)*(phaseGrid k.val.2.succ).val = (phaseGrid k.val.2.succ).val
      ring
    have htimeopen : (cellToGlobal k.val (u,1)).1 ∈
        Set.Ioo (phaseGrid k.val.1.castSucc) (phaseGrid k.val.1.succ) := by
      exact affineInterior k.val.1 u hu
    rw [hphasecoord] at hc
    have hp := phaseOpenClosedUnique k.val.1 e.1.1.val.1 _ htimeopen hc.1
    rcases phaseClosedCellAtGridNode k.val.2.succ e.1.1.val.2 hc.2 with hi | hi
    · right
      apply Subtype.ext
      apply Prod.ext
      · exact hp.symm.trans htime
      · apply Fin.castSucc_injective
        exact hi.trans hphase
    · left
      apply Subtype.ext
      have hphaseEq : e.1.1.val.2 = k.val.2 := by
        apply Fin.ext
        have hv := congrArg (fun j : Fin (n+2) => j.val) hi
        change e.1.1.val.2.val+1 = k.val.2.val+1 at hv
        omega
      exact Prod.ext hp.symm hphaseEq
  have actualBottomCellEndpointCountOne (k : activeCells) (hk : k.val.1 = 0)
      (u : Interval) (hroot : actualFaceHeight (k,3) u = 0) :
      actualCellSourceCount k (0,u) + actualCellTargetCount k (0,u) = 1 := by
    obtain ⟨j,hj,hj0,hj1⟩ := actualFaceZeroIsInternalMesh (k,3) u hroot
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      hj ▸ actualInternalMeshNodeOpenParameter (k,3) j hj0 hj1
    have hcoords : squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hn : (regularizedCellLoops k.val (boundaryFace 3 u)).val.1 = 0 :=
      (div_eq_zero_iff.mp hroot).resolve_right (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hf := activeFaceBoundaryFix (k,3) ⟨boundaryFace 3 u,hroot.le⟩ hn
    have hcount := actualOpenConeCellEndpointCount k 3 u hu hroot.le
    rw [hf,hcoords] at hcount
    exact hcount.trans (actualBottomFaceZeroCovered k hk u hroot).2
  have actualTopCellEndpointCountOne (k : activeCells) (hk : k.val.1 = Fin.last n)
      (u : Interval) (hroot : actualFaceHeight (k,1) u = 0) :
      actualCellSourceCount k (1,u) + actualCellTargetCount k (1,u) = 1 := by
    obtain ⟨j,hj,hj0,hj1⟩ := actualFaceZeroIsInternalMesh (k,1) u hroot
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      hj ▸ actualInternalMeshNodeOpenParameter (k,1) j hj0 hj1
    have hcoords : squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hn : (regularizedCellLoops k.val (boundaryFace 1 u)).val.1 = 0 :=
      (div_eq_zero_iff.mp hroot).resolve_right (cellCenterAxisNonzero k.val (activeCellAxis k))
    have hf := activeFaceBoundaryFix (k,1) ⟨boundaryFace 1 u,hroot.le⟩ hn
    have hcount := actualOpenConeCellEndpointCount k 1 u hu hroot.le
    rw [hf,hcoords] at hcount
    exact hcount.trans (actualTopFaceZeroCovered k hk u hroot).2
  have actualNegativeInternalMeshCellCountTwo (k : activeCells) (i : Fin 4)
      (j : Fin (activeFaceSize (k,i)+2)) (hj0 : j ≠ 0)
      (hj1 : j ≠ Fin.last (activeFaceSize (k,i)+1))
      (hneg : actualFaceHeight (k,i) (activeFaceMesh (k,i) j) < 0) :
      actualCellSourceCount k (activeFaceRadial (k,i)
        ⟨boundaryFace i (activeFaceMesh (k,i) j),hneg.le⟩) +
      actualCellTargetCount k (activeFaceRadial (k,i)
        ⟨boundaryFace i (activeFaceMesh (k,i) j),hneg.le⟩) = 2 := by
    rw [actualOpenConeCellEndpointCount k i _
      (actualInternalMeshNodeOpenParameter (k,i) j hj0 hj1) hneg.le]
    exact actualNegativeMeshFaceIncidenceTwo (k,i) j hj0 hj1 hneg
  have actualZeroEndpointInOpenCellUnique (k : activeCells) (z : Interval × Interval)
      (hz : z.1 ∈ Set.Ioo (0 : Interval) 1 ∧ z.2 ∈ Set.Ioo (0 : Interval) 1)
      (e : zeroEdgeIndex) (r : Interval)
      (he : globalZeroEdge e r = cellToGlobal k.val z) : e.1.1 = k := by
    have hc := globalZeroClosedCoordinates e r
    rw [he] at hc
    have hin : (cellToGlobal k.val z).1 ∈ Set.Ioo
        (phaseGrid k.val.1.castSucc) (phaseGrid k.val.1.succ) ∧
        (cellToGlobal k.val z).2 ∈ Set.Ioo
        (phaseGrid k.val.2.castSucc) (phaseGrid k.val.2.succ) := by
      exact ⟨affineInterior k.val.1 z.1 hz.1,affineInterior k.val.2 z.2 hz.2⟩
    have h1 := phaseOpenClosedUnique k.val.1 e.1.1.val.1 _ hin.1 hc.1
    have h2 := phaseOpenClosedUnique k.val.2 e.1.1.val.2 _ hin.2 hc.2
    exact Subtype.ext (Prod.ext h1.symm h2.symm)
  have actualNegativeRadialEndpointCellUnique (k : activeCells) (i : Fin 4)
      (z : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (regularizedCellLoops k.val z).val.1 / (cellCenter k.val).val.1 ≤ 0})
      (hneg : (regularizedCellLoops k.val z.val).val.1 / (cellCenter k.val).val.1 < 0)
      (e : zeroEdgeIndex) (r : Interval)
      (he : globalZeroEdge e r = cellToGlobal k.val (activeFaceRadial (k,i) z)) : e.1.1 = k :=
    actualZeroEndpointInOpenCellUnique k _ (actualNegativeRadialCoordinates (k,i) z hneg) e r he
  have globalZeroInteriorSameCell (e f : zeroEdgeIndex) (t u : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (heq : globalZeroEdge e t = globalZeroEdge f u) : e.1.1.val = f.1.1.val := by
    obtain ⟨he1,he2⟩ := globalZeroEdgeInterior e t ht
    obtain ⟨hf1,hf2⟩ := globalZeroEdgeInterior f u hu
    rw [← heq] at hf1 hf2
    exact Prod.ext (phaseOpenIntervalsUnique _ _ _ he1 hf1)
      (phaseOpenIntervalsUnique _ _ _ he2 hf2)
  let cylinderProjection : C(Interval × Interval,Interval × Circle) :=
    ⟨fun z => (z.1,Circle.exp (2*Real.pi*z.2.val)),by fun_prop⟩
  let zeroEndpointLeft (e : zeroEdgeIndex) := cylinderProjection (globalZeroEdge e 0)
  let zeroEndpointRight (e : zeroEdgeIndex) := cylinderProjection (globalZeroEdge e 1)
  let zeroEndpointSet : Set (Interval × Circle) :=
    Set.range zeroEndpointLeft ∪ Set.range zeroEndpointRight
  have zeroEndpointFinite : zeroEndpointSet.Finite :=
    (Set.finite_range zeroEndpointLeft).union (Set.finite_range zeroEndpointRight)
  letI : Finite zeroEndpointSet := zeroEndpointFinite.to_subtype
  have actualInteriorPhaseCylinderCellUnique (k : activeCells) (z : Interval × Interval)
      (hz : z.1 ∈ Set.Ioo (0 : Interval) 1 ∧ z.2 ∈ Set.Ioo (0 : Interval) 1)
      (e : zeroEdgeIndex) (r : Interval)
      (he : cylinderProjection (globalZeroEdge e r) = cylinderProjection (cellToGlobal k.val z)) :
      e.1.1 = k := by
    have hs := phaseStep k.val.2
    have hz0 : 0 < z.2.val := hz.2.1
    have hz1 : z.2.val < 1 := hz.2.2
    have hphase : (cellToGlobal k.val z).2 ∈ Set.Ioo (0 : Interval) 1 := by
      change (0 < (1-z.2.val)*(phaseGrid k.val.2.castSucc).val+
          z.2.val*(phaseGrid k.val.2.succ).val) ∧
        (1-z.2.val)*(phaseGrid k.val.2.castSucc).val+
          z.2.val*(phaseGrid k.val.2.succ).val < 1
      constructor <;> nlinarith [(phaseGrid k.val.2.castSucc).property.1,
        (phaseGrid k.val.2.succ).property.2]
    have hsquare := actual_cylinder_interior_phase_fiber_unique
      (globalZeroEdge e r) (cellToGlobal k.val z) hphase he
    exact actualZeroEndpointInOpenCellUnique k z hz e r hsquare
  have actualSeamCellPoint (k l : activeCells) (htime : k.val.1 = l.val.1)
      (hkphase : k.val.2 = 0) (hlphase : l.val.2 = Fin.last n)
      (u : Interval) : cylinderProjection (cellToGlobal k.val (u,0)) =
        cylinderProjection (cellToGlobal l.val (u,1)) := by
    apply Prod.ext
    · apply Subtype.ext
      change (1-u.val)*(phaseGrid k.val.1.castSucc).val+u.val*(phaseGrid k.val.1.succ).val =
        (1-u.val)*(phaseGrid l.val.1.castSucc).val+u.val*(phaseGrid l.val.1.succ).val
      rw [htime]
    · have hleft : (cellToGlobal k.val (u,0)).2 = 0 := by
        apply Subtype.ext
        change (1-(0 : ℝ))*(phaseGrid k.val.2.castSucc).val+
          (0 : ℝ)*(phaseGrid k.val.2.succ).val = 0
        have hi : k.val.2.castSucc = (0 : Fin (n+2)) := by
          apply Fin.ext
          exact congrArg (fun j : Fin (n+1) => j.val) hkphase
        rw [hi]
        simp [phaseGrid]
      have hright : (cellToGlobal l.val (u,1)).2 = 1 := by
        apply Subtype.ext
        change (1-(1 : ℝ))*(phaseGrid l.val.2.castSucc).val+
          (1 : ℝ)*(phaseGrid l.val.2.succ).val = 1
        rw [hlphase,lastSucc]
        simp [phaseGrid]
      change Circle.exp (2*Real.pi*(cellToGlobal k.val (u,0)).2.val) =
        Circle.exp (2*Real.pi*(cellToGlobal l.val (u,1)).2.val)
      rw [hleft,hright]
      simp
  have actualSeamRootCylinderCellAlternatives (k l : activeCells)
      (htime : k.val.1 = l.val.1) (hkphase : k.val.2 = 0)
      (hlphase : l.val.2 = Fin.last n) (u : Interval)
      (hu : u ∈ Set.Ioo (0 : Interval) 1) (e : zeroEdgeIndex) (r : Interval)
      (he : cylinderProjection (globalZeroEdge e r) =
        cylinderProjection (cellToGlobal k.val (u,0))) : e.1.1 = k ∨ e.1.1 = l := by
    have hzphase : (cellToGlobal k.val (u,0)).2 = 0 := by
      apply Subtype.ext
      change (1-(0 : ℝ))*(phaseGrid k.val.2.castSucc).val+
        (0 : ℝ)*(phaseGrid k.val.2.succ).val = 0
      have hi : k.val.2.castSucc = (0 : Fin (n+2)) := by
        apply Fin.ext
        exact congrArg (fun j : Fin (n+1) => j.val) hkphase
      rw [hi]
      simp [phaseGrid]
    have htimeopen : (cellToGlobal k.val (u,0)).1 ∈
        Set.Ioo (phaseGrid k.val.1.castSucc) (phaseGrid k.val.1.succ) := by
      exact affineInterior k.val.1 u hu
    have hprojection := (actual_cylinder_projection_fiber
      (globalZeroEdge e r) (cellToGlobal k.val (u,0))).mp he
    have hphasecases : (globalZeroEdge e r).2 = 0 ∨ (globalZeroEdge e r).2 = 1 := by
      rcases hprojection.2 with hsame | ⟨h0,h1⟩ | ⟨h1,h0⟩
      · exact Or.inl (hsame.trans hzphase)
      · exact Or.inl h0
      · exact Or.inr h1
    have hc := globalZeroClosedCoordinates e r
    rw [hprojection.1] at hc
    have hitime := (phaseOpenClosedUnique k.val.1 e.1.1.val.1 _ htimeopen hc.1).symm
    rcases hphasecases with h0 | h1
    · left
      apply Subtype.ext
      apply Prod.ext hitime
      rw [h0] at hc
      have hgrid : phaseGrid e.1.1.val.2.castSucc = phaseGrid 0 := by
        have hz : phaseGrid (0 : Fin (n+2)) = 0 := by simp [phaseGrid]
        rw [hz]
        exact le_antisymm hc.2.1 (phaseGrid e.1.1.val.2.castSucc).property.1
      have hi : e.1.1.val.2 = 0 := by
        apply Fin.ext
        exact congrArg (fun j : Fin (n+2) => j.val) (phaseGridStrict.injective hgrid)
      exact hi.trans hkphase.symm
    · right
      apply Subtype.ext
      apply Prod.ext (hitime.trans htime)
      rw [h1] at hc
      have hgrid : phaseGrid e.1.1.val.2.succ = phaseGrid (Fin.last (n+1)) := by
        have hz : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
        rw [hz]
        exact le_antisymm (phaseGrid e.1.1.val.2.succ).property.2 hc.2.2
      have hi : e.1.1.val.2 = Fin.last n := by
        apply Fin.ext
        have hh := congrArg (fun j : Fin (n+2) => j.val) (phaseGridStrict.injective hgrid)
        change e.1.1.val.2.val + 1 = n+1 at hh
        change e.1.1.val.2.val = n
        omega
      exact hi.trans hlphase.symm
  let zeroVertex := Sum zeroEndpointSet (zeroEdgeIndex × Fin 2)
  letI : Fintype zeroVertex := Fintype.ofFinite zeroVertex
  let zeroLeftVertex (e : zeroEdgeIndex) : zeroVertex :=
    Sum.inl ⟨zeroEndpointLeft e,Or.inl ⟨e,rfl⟩⟩
  let zeroRightVertex (e : zeroEdgeIndex) : zeroVertex :=
    Sum.inl ⟨zeroEndpointRight e,Or.inr ⟨e,rfl⟩⟩
  let zeroDirectedIncidence : zeroVertex → zeroVertex → Prop := fun v w => ∃ e : zeroEdgeIndex,
    (v = zeroLeftVertex e ∧ w = Sum.inr (e,0)) ∨
    (v = Sum.inr (e,0) ∧ w = Sum.inr (e,1)) ∨
    (v = Sum.inr (e,1) ∧ w = zeroRightVertex e)
  let actualZeroGraph : SimpleGraph zeroVertex := SimpleGraph.fromRel zeroDirectedIncidence
  have zeroGraphLeftAdj (e : zeroEdgeIndex) :
      actualZeroGraph.Adj (zeroLeftVertex e) (Sum.inr (e,0)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroGraphMiddleAdj (e : zeroEdgeIndex) :
      actualZeroGraph.Adj (Sum.inr (e,0)) (Sum.inr (e,1)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩⟩
    intro he
    have hh := congrArg Prod.snd (Sum.inr.inj he)
    norm_num at hh
  have zeroGraphRightAdj (e : zeroEdgeIndex) :
      actualZeroGraph.Adj (Sum.inr (e,1)) (zeroRightVertex e) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  let zeroBottomVertices : Finset zeroVertex := Finset.univ.filter
    (fun v => ∃ p : zeroEndpointSet, v = Sum.inl p ∧ p.val.1 = 0)
  let zeroTopVertices : Finset zeroVertex := Finset.univ.filter
    (fun v => ∃ p : zeroEndpointSet, v = Sum.inl p ∧ p.val.1 = 1)
  have zeroBoundarySetsDisjoint : Disjoint zeroBottomVertices zeroTopVertices := by
    apply Finset.disjoint_left.mpr
    intro v hvB hvT
    obtain ⟨p,hvp,hp⟩ := (Finset.mem_filter.mp hvB).2
    obtain ⟨q,hvq,hq⟩ := (Finset.mem_filter.mp hvT).2
    have he : p = q := Sum.inl.inj (hvp.symm.trans hvq)
    subst q
    rw [hp] at hq
    norm_num at hq
  -- The finite incidence graph above is CONSTRUCTED from actual zero edges,
  -- identifying seam endpoint copies through their actual cylinder positions.
  -- The two private vertices per edge preserve parallel edges and loops.
  -- Its geometric embedding and boundary-degree/count classification remain
  -- obligations; they are not premises of graph construction or of the target.
  have zeroSubdivisionNeighborsLeft (e : zeroEdgeIndex) :
      actualZeroGraph.neighborFinset (Sum.inr (e,0)) =
        {zeroLeftVertex e,Sum.inr (e,1)} := by
    ext v
    rcases v with p | ⟨e',j⟩
    · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
        zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
    · fin_cases j <;>
        simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  have zeroSubdivisionNeighborsRight (e : zeroEdgeIndex) :
      actualZeroGraph.neighborFinset (Sum.inr (e,1)) =
        {Sum.inr (e,0),zeroRightVertex e} := by
    ext v
    rcases v with p | ⟨e',j⟩
    · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
        zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
    · fin_cases j <;>
        simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  let leftIncidentEdges (p : zeroEndpointSet) : Finset zeroEdgeIndex :=
    Finset.univ.filter (fun e => Sum.inl p = zeroLeftVertex e)
  let rightIncidentEdges (p : zeroEndpointSet) : Finset zeroEdgeIndex :=
    Finset.univ.filter (fun e => Sum.inl p = zeroRightVertex e)
  have zeroEndpointNeighbors (p : zeroEndpointSet) :
      actualZeroGraph.neighborFinset (Sum.inl p) =
        (leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) ∪
        (rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
    ext v
    rcases v with q | ⟨e,j⟩
    · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
        zeroDirectedIncidence,leftIncidentEdges,rightIncidentEdges,
        zeroLeftVertex,zeroRightVertex,zeroVertex]
    · fin_cases j <;>
        simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,leftIncidentEdges,rightIncidentEdges,
          zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq]
  have actualLeftIncidentPositionFilter (p : zeroEndpointSet) :
      leftIncidentEdges p = Finset.univ.filter (fun e => zeroEndpointLeft e = p.val) := by
    ext e
    simp only [leftIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    change Sum.inl p = Sum.inl ⟨zeroEndpointLeft e,_⟩ ↔ zeroEndpointLeft e = p.val
    constructor
    · intro he
      exact (congrArg Subtype.val (Sum.inl.inj he)).symm
    · intro he
      apply congrArg Sum.inl
      apply Subtype.ext
      exact he.symm
  have actualRightIncidentPositionFilter (p : zeroEndpointSet) :
      rightIncidentEdges p = Finset.univ.filter (fun e => zeroEndpointRight e = p.val) := by
    ext e
    simp only [rightIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    change Sum.inl p = Sum.inl ⟨zeroEndpointRight e,_⟩ ↔ zeroEndpointRight e = p.val
    constructor
    · intro he
      exact (congrArg Subtype.val (Sum.inl.inj he)).symm
    · intro he
      apply congrArg Sum.inl
      apply Subtype.ext
      exact he.symm
  have actualEndpointSourceCellPartition (p : zeroEndpointSet) :
      (leftIncidentEdges p).card = ∑ k : activeCells,
        (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
          zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val)).card := by
    calc
      (leftIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointLeft e = p.val} := by
        rw [actualLeftIncidentPositionFilter p]
        exact (Fintype.card_subtype _).symm
      _ = Fintype.card (Σ k : activeCells, {e : actualCellEdgeIndex k |
          zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val}) :=
        Fintype.card_congr (Classical.choice (actualSigmaEndpointFiberPartition
          (fun e => zeroEndpointLeft e = p.val)))
      _ = ∑ k : activeCells, Fintype.card {e : actualCellEdgeIndex k |
          zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val} := Fintype.card_sigma
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Fintype.card_subtype _
  have actualEndpointTargetCellPartition (p : zeroEndpointSet) :
      (rightIncidentEdges p).card = ∑ k : activeCells,
        (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
          zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val)).card := by
    calc
      (rightIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointRight e = p.val} := by
        rw [actualRightIncidentPositionFilter p]
        exact (Fintype.card_subtype _).symm
      _ = Fintype.card (Σ k : activeCells, {e : actualCellEdgeIndex k |
          zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val}) :=
        Fintype.card_congr (Classical.choice (actualSigmaEndpointFiberPartition
          (fun e => zeroEndpointRight e = p.val)))
      _ = ∑ k : activeCells, Fintype.card {e : actualCellEdgeIndex k |
          zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val} := Fintype.card_sigma
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Fintype.card_subtype _
  have actualEndpointCellPartition (p : zeroEndpointSet) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = ∑ k : activeCells,
        ((Finset.univ.filter (fun e : actualCellEdgeIndex k =>
          zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val)).card +
        (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
          zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val)).card) := by
    rw [actualEndpointSourceCellPartition,actualEndpointTargetCellPartition,Finset.sum_add_distrib]
  have actualOpenCellCylinderEndpointCount (k : activeCells) (z : Interval × Interval)
      (hz : z.1 ∈ Set.Ioo (0 : Interval) 1 ∧ z.2 ∈ Set.Ioo (0 : Interval) 1)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val z)) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card =
        actualCellSourceCount k z + actualCellTargetCount k z := by
    have hLcell (e : zeroEdgeIndex) (he : zeroEndpointLeft e = p.val) : e.1.1 = k := by
      apply actualInteriorPhaseCylinderCellUnique k z hz e 0
      exact he.trans hp
    have hRcell (e : zeroEdgeIndex) (he : zeroEndpointRight e = p.val) : e.1.1 = k := by
      apply actualInteriorPhaseCylinderCellUnique k z hz e 1
      exact he.trans hp
    have hphase : (cellToGlobal k.val z).2 ∈ Set.Ioo (0 : Interval) 1 := by
      have hs := phaseStep k.val.2
      have h0 : 0 < z.2.val := hz.2.1
      have h1 : z.2.val < 1 := hz.2.2
      change (0 < (1-z.2.val)*(phaseGrid k.val.2.castSucc).val+
          z.2.val*(phaseGrid k.val.2.succ).val) ∧
        (1-z.2.val)*(phaseGrid k.val.2.castSucc).val+
          z.2.val*(phaseGrid k.val.2.succ).val < 1
      constructor <;> nlinarith [(phaseGrid k.val.2.castSucc).property.1,
        (phaseGrid k.val.2.succ).property.2]
    have hiff (e : actualCellEdgeIndex k) (r : Interval) :
        cylinderProjection (globalZeroEdge ⟨(k,e.1),e.2⟩ r) = p.val ↔
          zeroEdge ⟨(k,e.1),e.2⟩ r = z := by
      rw [hp]
      constructor
      · intro he
        exact (cellToGlobalEmbedding k.val).injective
          (actual_cylinder_interior_phase_fiber_unique _ _ hphase he)
      · intro he
        exact congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) he
    have hL : (leftIncidentEdges p).card = actualCellSourceCount k z := by
      calc
        (leftIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointLeft e = p.val} := by
          rw [actualLeftIncidentPositionFilter p]
          exact (Fintype.card_subtype _).symm
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val} :=
          Fintype.card_congr (Classical.choice (actualSingleCellEndpointFiber
            (fun e => zeroEndpointLeft e = p.val) k hLcell))
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEdge ⟨(k,e.1),e.2⟩ 0 = z} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun e => hiff e 0))
        _ = _ := Fintype.card_subtype _
    have hR : (rightIncidentEdges p).card = actualCellTargetCount k z := by
      calc
        (rightIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointRight e = p.val} := by
          rw [actualRightIncidentPositionFilter p]
          exact (Fintype.card_subtype _).symm
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val} :=
          Fintype.card_congr (Classical.choice (actualSingleCellEndpointFiber
            (fun e => zeroEndpointRight e = p.val) k hRcell))
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEdge ⟨(k,e.1),e.2⟩ 1 = z} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun e => hiff e 1))
        _ = _ := Fintype.card_subtype _
    rw [hL,hR]
  have actualNegativeInternalCylinderEndpointCountTwo (k : activeCells) (i : Fin 4)
      (j : Fin (activeFaceSize (k,i)+2)) (hj0 : j ≠ 0)
      (hj1 : j ≠ Fin.last (activeFaceSize (k,i)+1))
      (hneg : actualFaceHeight (k,i) (activeFaceMesh (k,i) j) < 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (activeFaceRadial (k,i)
        ⟨boundaryFace i (activeFaceMesh (k,i) j),hneg.le⟩))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hcoords := actualNegativeRadialCoordinates (k,i)
      ⟨boundaryFace i (activeFaceMesh (k,i) j),hneg.le⟩ hneg
    exact (actualOpenCellCylinderEndpointCount k _ hcoords p hp).trans
      (actualNegativeInternalMeshCellCountTwo k i j hj0 hj1 hneg)
  have zeroEndpointDegreeExact (p : zeroEndpointSet) :
      actualZeroGraph.degree (Sum.inl p) =
        (leftIncidentEdges p).card + (rightIncidentEdges p).card := by
    change (actualZeroGraph.neighborFinset (Sum.inl p)).card = _
    rw [zeroEndpointNeighbors]
    have hd : Disjoint
        ((leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)))
        ((rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex))) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨f,hf,h⟩ := Finset.mem_image.mp hw
      have hh := congrArg (fun v : zeroEdgeIndex × Fin 2 => v.2) (Sum.inr.inj h)
      norm_num at hh
    rw [Finset.card_union_of_disjoint hd]
    have hi0 : Function.Injective (fun e : zeroEdgeIndex => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) := by
      intro e f h
      exact congrArg Prod.fst (Sum.inr.inj h)
    have hi1 : Function.Injective (fun e : zeroEdgeIndex => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
      intro e f h
      exact congrArg Prod.fst (Sum.inr.inj h)
    rw [Finset.card_image_of_injective _ hi0,Finset.card_image_of_injective _ hi1]
  have zeroSubdivisionDegrees (e : zeroEdgeIndex) :
      actualZeroGraph.degree (Sum.inr (e,0)) = 2 ∧
      actualZeroGraph.degree (Sum.inr (e,1)) = 2 := by
    change (actualZeroGraph.neighborFinset (Sum.inr (e,0))).card = 2 ∧
      (actualZeroGraph.neighborFinset (Sum.inr (e,1))).card = 2
    rw [zeroSubdivisionNeighborsLeft,zeroSubdivisionNeighborsRight]
    simp [zeroLeftVertex,zeroRightVertex]
  have cellAngularWidth (j : Fin (n+1)) :
      (phaseGrid j.succ).val-(phaseGrid j.castSucc).val < 1 := by
    have h0 : phaseGrid (0 : Fin (n+2)) = 0 := by simp [phaseGrid]
    by_cases hj : j.val = 0
    · have hleft : j.castSucc = 0 := by apply Fin.ext; exact hj
      have hright : phaseGrid j.succ < phaseGrid (Fin.last (n+1)) :=
        phaseGridStrict (by change j.val+1 < n+1; omega)
      have h1 : phaseGrid (Fin.last (n+1)) = 1 := by simp [phaseGrid]
      rw [hleft,h0]
      have hr : (phaseGrid j.succ).val < 1 := by
        have hh : phaseGrid j.succ < 1 := h1 ▸ hright
        exact hh
      simpa using hr
    · have hleft : 0 < phaseGrid j.castSucc := by
        rw [← h0]
        apply phaseGridStrict
        change (0 : ℕ) < j.val
        omega
      have hl : 0 < (phaseGrid j.castSucc).val := hleft
      linarith only [hl,(phaseGrid j.succ).property.2]
  have actualNegativeCorner00CylinderCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,0) (0 : Interval) < 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (activeFaceRadial (k,0)
        ⟨boundaryFace 0 0,hneg.le⟩))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hcoords := actualNegativeRadialCoordinates (k,0) ⟨boundaryFace 0 0,hneg.le⟩ hneg
    exact (actualOpenCellCylinderEndpointCount k _ hcoords p hp).trans
      (actualNegativeCorner00CellCountTwo k hneg)
  have actualNegativeCorner01CylinderCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,0) (1 : Interval) < 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (activeFaceRadial (k,0)
        ⟨boundaryFace 0 1,hneg.le⟩))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hcoords := actualNegativeRadialCoordinates (k,0) ⟨boundaryFace 0 1,hneg.le⟩ hneg
    exact (actualOpenCellCylinderEndpointCount k _ hcoords p hp).trans
      (actualNegativeCorner01CellCountTwo k hneg)
  have actualNegativeCorner20CylinderCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,2) (0 : Interval) < 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (activeFaceRadial (k,2)
        ⟨boundaryFace 2 0,hneg.le⟩))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hcoords := actualNegativeRadialCoordinates (k,2) ⟨boundaryFace 2 0,hneg.le⟩ hneg
    exact (actualOpenCellCylinderEndpointCount k _ hcoords p hp).trans
      (actualNegativeCorner20CellCountTwo k hneg)
  have actualNegativeCorner21CylinderCountTwo (k : activeCells)
      (hneg : actualFaceHeight (k,2) (1 : Interval) < 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (activeFaceRadial (k,2)
        ⟨boundaryFace 2 1,hneg.le⟩))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hcoords := actualNegativeRadialCoordinates (k,2) ⟨boundaryFace 2 1,hneg.le⟩ hneg
    exact (actualOpenCellCylinderEndpointCount k _ hcoords p hp).trans
      (actualNegativeCorner21CellCountTwo k hneg)
  have actualBottomCylinderEndpointCountOne (k : activeCells) (hk : k.val.1 = 0)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : actualFaceHeight (k,3) u = 0) (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (0,u))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 1 := by
    have hphase : (cellToGlobal k.val (0,u)).2 ∈ Set.Ioo (0 : Interval) 1 := by
      have hs := phaseStep k.val.2
      have h0 : 0 < u.val := hu.1
      have h1 : u.val < 1 := hu.2
      change (0 < (1-u.val)*(phaseGrid k.val.2.castSucc).val+
          u.val*(phaseGrid k.val.2.succ).val) ∧
        (1-u.val)*(phaseGrid k.val.2.castSucc).val+
          u.val*(phaseGrid k.val.2.succ).val < 1
      constructor <;> nlinarith [(phaseGrid k.val.2.castSucc).property.1,
        (phaseGrid k.val.2.succ).property.2]
    have hcell (e : zeroEdgeIndex) (r : Interval)
        (he : cylinderProjection (globalZeroEdge e r) = p.val) : e.1.1 = k := by
      rw [hp] at he
      exact actualBottomRootCell k hk u hu e r
        (actual_cylinder_interior_phase_fiber_unique _ _ hphase he)
    have hiff (e : actualCellEdgeIndex k) (r : Interval) :
        cylinderProjection (globalZeroEdge ⟨(k,e.1),e.2⟩ r) = p.val ↔
          zeroEdge ⟨(k,e.1),e.2⟩ r = (0,u) := by
      rw [hp]
      constructor
      · intro he
        exact (cellToGlobalEmbedding k.val).injective
          (actual_cylinder_interior_phase_fiber_unique _ _ hphase he)
      · intro he
        exact congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) he
    have hL : (leftIncidentEdges p).card = actualCellSourceCount k (0,u) := by
      calc
        (leftIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointLeft e = p.val} := by
          rw [actualLeftIncidentPositionFilter p]
          exact (Fintype.card_subtype _).symm
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val} :=
          Fintype.card_congr (Classical.choice (actualSingleCellEndpointFiber
            (fun e => zeroEndpointLeft e = p.val) k (fun e he => hcell e 0 he)))
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEdge ⟨(k,e.1),e.2⟩ 0 = (0,u)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun e => hiff e 0))
        _ = _ := Fintype.card_subtype _
    have hR : (rightIncidentEdges p).card = actualCellTargetCount k (0,u) := by
      calc
        (rightIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointRight e = p.val} := by
          rw [actualRightIncidentPositionFilter p]
          exact (Fintype.card_subtype _).symm
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val} :=
          Fintype.card_congr (Classical.choice (actualSingleCellEndpointFiber
            (fun e => zeroEndpointRight e = p.val) k (fun e he => hcell e 1 he)))
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEdge ⟨(k,e.1),e.2⟩ 1 = (0,u)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun e => hiff e 1))
        _ = _ := Fintype.card_subtype _
    rw [hL,hR]
    exact actualBottomCellEndpointCountOne k hk u hroot
  have actualTopCylinderEndpointCountOne (k : activeCells) (hk : k.val.1 = Fin.last n)
      (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : actualFaceHeight (k,1) u = 0) (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (1,u))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 1 := by
    have hphase : (cellToGlobal k.val (1,u)).2 ∈ Set.Ioo (0 : Interval) 1 := by
      have hs := phaseStep k.val.2
      have h0 : 0 < u.val := hu.1
      have h1 : u.val < 1 := hu.2
      change (0 < (1-u.val)*(phaseGrid k.val.2.castSucc).val+
          u.val*(phaseGrid k.val.2.succ).val) ∧
        (1-u.val)*(phaseGrid k.val.2.castSucc).val+
          u.val*(phaseGrid k.val.2.succ).val < 1
      constructor <;> nlinarith [(phaseGrid k.val.2.castSucc).property.1,
        (phaseGrid k.val.2.succ).property.2]
    have hcell (e : zeroEdgeIndex) (r : Interval)
        (he : cylinderProjection (globalZeroEdge e r) = p.val) : e.1.1 = k := by
      rw [hp] at he
      exact actualTopRootCell k hk u hu e r
        (actual_cylinder_interior_phase_fiber_unique _ _ hphase he)
    have hiff (e : actualCellEdgeIndex k) (r : Interval) :
        cylinderProjection (globalZeroEdge ⟨(k,e.1),e.2⟩ r) = p.val ↔
          zeroEdge ⟨(k,e.1),e.2⟩ r = (1,u) := by
      rw [hp]
      constructor
      · intro he
        exact (cellToGlobalEmbedding k.val).injective
          (actual_cylinder_interior_phase_fiber_unique _ _ hphase he)
      · intro he
        exact congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) he
    have hL : (leftIncidentEdges p).card = actualCellSourceCount k (1,u) := by
      calc
        (leftIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointLeft e = p.val} := by
          rw [actualLeftIncidentPositionFilter p]
          exact (Fintype.card_subtype _).symm
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEndpointLeft ⟨(k,e.1),e.2⟩ = p.val} :=
          Fintype.card_congr (Classical.choice (actualSingleCellEndpointFiber
            (fun e => zeroEndpointLeft e = p.val) k (fun e he => hcell e 0 he)))
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEdge ⟨(k,e.1),e.2⟩ 0 = (1,u)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun e => hiff e 0))
        _ = _ := Fintype.card_subtype _
    have hR : (rightIncidentEdges p).card = actualCellTargetCount k (1,u) := by
      calc
        (rightIncidentEdges p).card = Fintype.card {e : zeroEdgeIndex | zeroEndpointRight e = p.val} := by
          rw [actualRightIncidentPositionFilter p]
          exact (Fintype.card_subtype _).symm
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEndpointRight ⟨(k,e.1),e.2⟩ = p.val} :=
          Fintype.card_congr (Classical.choice (actualSingleCellEndpointFiber
            (fun e => zeroEndpointRight e = p.val) k (fun e he => hcell e 1 he)))
        _ = Fintype.card {e : actualCellEdgeIndex k | zeroEdge ⟨(k,e.1),e.2⟩ 1 = (1,u)} :=
          Fintype.card_congr (Equiv.subtypeEquivRight (fun e => hiff e 1))
        _ = _ := Fintype.card_subtype _
    rw [hL,hR]
    exact actualTopCellEndpointCountOne k hk u hroot
  have actualFaceDirectionHeightAgreement (k : activeCells) (i j : Fin 4)
      (u v : Interval) (he : boundaryFace i u = boundaryFace j v) :
      actualFaceHeight (k,i) u = actualFaceHeight (k,j) v := by
    change (regularizedCellLoops k.val (boundaryFace i u)).val.1 / (cellCenter k.val).val.1 =
      (regularizedCellLoops k.val (boundaryFace j v)).val.1 / (cellCenter k.val).val.1
    rw [he]
  have actualFaceDirectionRadialAgreement (k : activeCells) (i j : Fin 4)
      (u v : Interval) (he : boundaryFace i u = boundaryFace j v)
      (hi : actualFaceHeight (k,i) u ≤ 0) (hj : actualFaceHeight (k,j) v ≤ 0) :
      activeFaceRadial (k,i) ⟨boundaryFace i u,hi⟩ =
        activeFaceRadial (k,j) ⟨boundaryFace j v,hj⟩ := by
    rw [activeFaceRadialAgreement k i j]
    apply congrArg (activeFaceRadial (k,j))
    apply Subtype.ext
    exact he
  have actualNegativeAnyCornerCylinderCountTwo (k : activeCells) (i : Fin 4)
      (u : Interval) (hu : u = 0 ∨ u = 1)
      (hneg : actualFaceHeight (k,i) u < 0) (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (activeFaceRadial (k,i)
        ⟨boundaryFace i u,hneg.le⟩))) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    rcases hu with rfl | rfl
    · fin_cases i
      · exact actualNegativeCorner00CylinderCountTwo k hneg p hp
      · have he : boundaryFace 1 (0 : Interval) = boundaryFace 0 1 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        have hneg' : actualFaceHeight (k,0) (1 : Interval) < 0 := by
          rw [←actualFaceDirectionHeightAgreement k 1 0 0 1 he]
          exact hneg
        have hrad := actualFaceDirectionRadialAgreement k 1 0 0 1 he hneg.le hneg'.le
        have hp' := hp.trans (congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) hrad)
        exact actualNegativeCorner01CylinderCountTwo k hneg' p hp'
      · exact actualNegativeCorner20CylinderCountTwo k hneg p hp
      · have he : boundaryFace 3 (0 : Interval) = boundaryFace 0 0 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        have hneg' : actualFaceHeight (k,0) (0 : Interval) < 0 := by
          rw [←actualFaceDirectionHeightAgreement k 3 0 0 0 he]
          exact hneg
        have hrad := actualFaceDirectionRadialAgreement k 3 0 0 0 he hneg.le hneg'.le
        have hp' := hp.trans (congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) hrad)
        exact actualNegativeCorner00CylinderCountTwo k hneg' p hp'
    · fin_cases i
      · exact actualNegativeCorner01CylinderCountTwo k hneg p hp
      · have he : boundaryFace 1 (1 : Interval) = boundaryFace 2 1 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        have hneg' : actualFaceHeight (k,2) (1 : Interval) < 0 := by
          rw [←actualFaceDirectionHeightAgreement k 1 2 1 1 he]
          exact hneg
        have hrad := actualFaceDirectionRadialAgreement k 1 2 1 1 he hneg.le hneg'.le
        have hp' := hp.trans (congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) hrad)
        exact actualNegativeCorner21CylinderCountTwo k hneg' p hp'
      · exact actualNegativeCorner21CylinderCountTwo k hneg p hp
      · have he : boundaryFace 3 (1 : Interval) = boundaryFace 2 0 := by
          apply Subtype.ext
          norm_num [boundaryFace,boundaryFaceRaw]
        have hneg' : actualFaceHeight (k,2) (0 : Interval) < 0 := by
          rw [←actualFaceDirectionHeightAgreement k 3 2 1 0 he]
          exact hneg
        have hrad := actualFaceDirectionRadialAgreement k 3 2 1 0 he hneg.le hneg'.le
        have hp' := hp.trans (congrArg (fun w => cylinderProjection (cellToGlobal k.val w)) hrad)
        exact actualNegativeCorner20CylinderCountTwo k hneg' p hp'
  have actualNegativeSelectedSourceCountTwo (e : zeroEdgeIndex)
      (hneg : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) < 0)
      (p : zeroEndpointSet) (hp : p.val = zeroEndpointLeft e) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hpoint : zeroEdge e 0 = activeFaceRadial e.1
        ⟨boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.castSucc),hneg.le⟩ := by
      rw [zeroSource e]
      apply congrArg (activeFaceRadial e.1)
      apply Subtype.ext
      exact zeroLeftBoundary e
    have hpRad : p.val = cylinderProjection (cellToGlobal e.1.1.val (activeFaceRadial e.1
        ⟨boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.castSucc),hneg.le⟩)) :=
      hp.trans (congrArg (fun z => cylinderProjection (cellToGlobal e.1.1.val z)) hpoint)
    rcases actualSourceMeshNodeCases e with hstart | hint
    · have hu : activeFaceMesh e.1 e.2.val.castSucc = 0 := by
        rw [hstart]
        exact activeFaceStart e.1
      exact actualNegativeAnyCornerCylinderCountTwo e.1.1 e.1.2 _ (Or.inl hu) hneg p hpRad
    · exact actualNegativeInternalCylinderEndpointCountTwo e.1.1 e.1.2 e.2.val.castSucc
        hint.1 hint.2 hneg p hpRad
  have actualNegativeSelectedTargetCountTwo (e : zeroEdgeIndex)
      (hneg : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) < 0)
      (p : zeroEndpointSet) (hp : p.val = zeroEndpointRight e) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 2 := by
    have hpoint : zeroEdge e 1 = activeFaceRadial e.1
        ⟨boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.succ),hneg.le⟩ := by
      rw [zeroTarget e]
      apply congrArg (activeFaceRadial e.1)
      apply Subtype.ext
      exact zeroRightBoundary e
    have hpRad : p.val = cylinderProjection (cellToGlobal e.1.1.val (activeFaceRadial e.1
        ⟨boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.succ),hneg.le⟩)) :=
      hp.trans (congrArg (fun z => cylinderProjection (cellToGlobal e.1.1.val z)) hpoint)
    rcases actualTargetMeshNodeCases e with hend | hint
    · have hu : activeFaceMesh e.1 e.2.val.succ = 1 := by
        rw [hend]
        exact activeFaceEnd e.1
      exact actualNegativeAnyCornerCylinderCountTwo e.1.1 e.1.2 _ (Or.inr hu) hneg p hpRad
    · exact actualNegativeInternalCylinderEndpointCountTwo e.1.1 e.1.2 e.2.val.succ
        hint.1 hint.2 hneg p hpRad
  have actualCellPhaseInterior (k : activeCells) (z : Interval × Interval)
      (hz : z.2 ∈ Set.Ioo (0 : Interval) 1) :
      (cellToGlobal k.val z).2 ∈ Set.Ioo (0 : Interval) 1 := by
    have hs := phaseStep k.val.2
    have h0 : 0 < z.2.val := hz.1
    have h1 : z.2.val < 1 := hz.2
    have hlo := (phaseGrid k.val.2.castSucc).property.1
    have hhi := (phaseGrid k.val.2.succ).property.2
    change 0 < (1-z.2.val)*(phaseGrid k.val.2.castSucc).val+
      z.2.val*(phaseGrid k.val.2.succ).val ∧
      (1-z.2.val)*(phaseGrid k.val.2.castSucc).val+
      z.2.val*(phaseGrid k.val.2.succ).val < 1
    constructor <;> nlinarith only [hs,h0,h1,hlo,hhi]
  have actualTimeRootCylinderCellAlternatives (k l : activeCells) (u : Interval)
      (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (htime : k.val.1.succ = l.val.1.castSucc) (hphase : k.val.2 = l.val.2)
      (e : zeroEdgeIndex) (r : Interval)
      (he : cylinderProjection (globalZeroEdge e r) =
        cylinderProjection (cellToGlobal k.val (1,u))) :
      e.1.1 = k ∨ e.1.1 = l := by
    have hpoint : globalZeroEdge e r = cellToGlobal k.val (1,u) :=
      actual_cylinder_interior_phase_fiber_unique _ _
        (actualCellPhaseInterior k (1,u) hu) he
    exact actualGridRootSquareCellAlternatives k l u hu htime hphase e r hpoint
  have actualPhaseRootCylinderCellAlternatives (k l : activeCells) (u : Interval)
      (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (htime : k.val.1 = l.val.1) (hphase : k.val.2.succ = l.val.2.castSucc)
      (e : zeroEdgeIndex) (r : Interval)
      (he : cylinderProjection (globalZeroEdge e r) =
        cylinderProjection (cellToGlobal k.val (u,1))) :
      e.1.1 = k ∨ e.1.1 = l := by
    have hrphase : (cellToGlobal k.val (u,1)).2 ∈ Set.Ioo (0 : Interval) 1 := by
      have hcoord : (cellToGlobal k.val (u,1)).2 = phaseGrid k.val.2.succ := by
        apply Subtype.ext
        change (1-(1 : ℝ))*(phaseGrid k.val.2.castSucc).val+
          (1 : ℝ)*(phaseGrid k.val.2.succ).val = (phaseGrid k.val.2.succ).val
        ring
      rw [hcoord]
      constructor
      · have hs := phaseStep k.val.2
        exact lt_of_le_of_lt (phaseGrid k.val.2.castSucc).property.1 hs
      · rw [hphase]
        have hs := phaseStep l.val.2
        exact lt_of_lt_of_le hs (phaseGrid l.val.2.succ).property.2
    have hpoint : globalZeroEdge e r = cellToGlobal k.val (u,1) :=
      actual_cylinder_interior_phase_fiber_unique _ _ hrphase he
    exact actualPhaseGridRootSquareCellAlternatives k l u hu htime hphase e r hpoint
  let cellCylinder : Fin (n+1) × Fin (n+1) → C(Interval × Interval,Interval × Circle) :=
    fun k => cylinderProjection.comp (cellToGlobal k)
  have cellCylinderEmbedding (k : Fin (n+1) × Fin (n+1)) : Topology.IsEmbedding (cellCylinder k) := by
    apply ((cellCylinder k).continuous.isClosedEmbedding ?_).isEmbedding
    intro z w he
    have hefirst := congrArg Prod.fst he
    have hesecond := congrArg Prod.snd he
    change Circle.exp (2*Real.pi*(cellToGlobal k z).2.val) =
      Circle.exp (2*Real.pi*(cellToGlobal k w).2.val) at hesecond
    have hperiod : 2*Real.pi*(phaseGrid k.2.succ).val-
        2*Real.pi*(phaseGrid k.2.castSucc).val < 2*Real.pi := by
      have hm := mul_lt_mul_of_pos_left (cellAngularWidth k.2)
        (by positivity : 0 < 2*Real.pi)
      nlinarith only [hm]
    have hmem (u : Interval × Interval) :
        2*Real.pi*(cellToGlobal k u).2.val ∈
          Set.Icc (2*Real.pi*(phaseGrid k.2.castSucc).val)
            (2*Real.pi*(phaseGrid k.2.succ).val) := by
      have hu := cellToGlobalInCell k u
      have hl : (phaseGrid k.2.castSucc).val ≤ (cellToGlobal k u).2.val := hu.2.2.1
      have hr : (cellToGlobal k u).2.val ≤ (phaseGrid k.2.succ).val := hu.2.2.2
      exact ⟨mul_le_mul_of_nonneg_left hl (by positivity),
        mul_le_mul_of_nonneg_left hr (by positivity)⟩
    have hangle := Circle.exp_injOn_Icc hperiod (hmem z) (hmem w) hesecond
    have hesecond' : (cellToGlobal k z).2 = (cellToGlobal k w).2 := by
      apply Subtype.ext
      exact mul_left_cancel₀ (by positivity : (2*Real.pi : ℝ) ≠ 0) hangle
    exact (cellToGlobalEmbedding k).injective (Prod.ext hefirst hesecond')
  have actualCellCylinderSourceCount (k : activeCells) (z : Interval × Interval) :
      (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
        zeroEndpointLeft ⟨(k,e.1),e.2⟩ = cylinderProjection (cellToGlobal k.val z))).card =
      actualCellSourceCount k z := by
    change (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
      zeroEndpointLeft ⟨(k,e.1),e.2⟩ = cylinderProjection (cellToGlobal k.val z))).card =
      (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
        zeroEdge ⟨(k,e.1),e.2⟩ 0 = z)).card
    congr 1
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change cellCylinder k.val (zeroEdge ⟨(k,e.1),e.2⟩ 0) = cellCylinder k.val z ↔
      zeroEdge ⟨(k,e.1),e.2⟩ 0 = z
    exact (cellCylinderEmbedding k.val).injective.eq_iff
  have actualCellCylinderTargetCount (k : activeCells) (z : Interval × Interval) :
      (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
        zeroEndpointRight ⟨(k,e.1),e.2⟩ = cylinderProjection (cellToGlobal k.val z))).card =
      actualCellTargetCount k z := by
    change (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
      zeroEndpointRight ⟨(k,e.1),e.2⟩ = cylinderProjection (cellToGlobal k.val z))).card =
      (Finset.univ.filter (fun e : actualCellEdgeIndex k =>
        zeroEdge ⟨(k,e.1),e.2⟩ 1 = z)).card
    congr 1
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change cellCylinder k.val (zeroEdge ⟨(k,e.1),e.2⟩ 1) = cellCylinder k.val z ↔
      zeroEdge ⟨(k,e.1),e.2⟩ 1 = z
    exact (cellCylinderEmbedding k.val).injective.eq_iff
  have actualTwoCellCylinderEndpointCount (k l : activeCells) (hkl : k ≠ l)
      (z w : Interval × Interval) (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val z))
      (hw : cylinderProjection (cellToGlobal k.val z) = cylinderProjection (cellToGlobal l.val w))
      (hcell : ∀ e r, (r = (0 : Interval) ∨ r = 1) →
        cylinderProjection (globalZeroEdge e r) = cylinderProjection (cellToGlobal k.val z) →
        e.1.1 = k ∨ e.1.1 = l) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card =
        (actualCellSourceCount k z + actualCellTargetCount k z) +
        (actualCellSourceCount l w + actualCellTargetCount l w) := by
    have hleft := actualTwoCellEndpointFiber (fun e => zeroEndpointLeft e = p.val)
      k l hkl (fun e he => hcell e 0 (Or.inl rfl) (he.trans hp))
    have hright := actualTwoCellEndpointFiber (fun e => zeroEndpointRight e = p.val)
      k l hkl (fun e he => hcell e 1 (Or.inr rfl) (he.trans hp))
    simp only [Fintype.card_subtype,Set.mem_setOf_eq] at hleft hright
    rw [actualLeftIncidentPositionFilter,actualRightIncidentPositionFilter,hleft,hright]
    rw [hp,actualCellCylinderSourceCount,actualCellCylinderTargetCount]
    rw [hw,actualCellCylinderSourceCount,actualCellCylinderTargetCount]
    omega
  have actualTimeRootCylinderIncidenceEven (k l : activeCells)
      (htime : k.val.1.succ = l.val.1.castSucc) (hphase : k.val.2 = l.val.2)
      (u : Interval) (hroot : actualFaceHeight (k,1) u = 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (1,u))) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    obtain ⟨j,hj,hj0,hj1⟩ := actualFaceZeroIsInternalMesh (k,1) u hroot
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      hj ▸ actualInternalMeshNodeOpenParameter (k,1) j hj0 hj1
    have hkl : k ≠ l := by
      intro he
      have ht := congrArg (fun j : Fin (n+2) => j.val) htime
      rw [← he] at ht
      change k.val.1.val+1 = k.val.1.val at ht
      omega
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hshared := actualTimeNeighborCellPoint k l htime hphase u
    have hrootl : actualFaceHeight (l,3) u = 0 := by
      apply (actualBoundaryRootTraceMembership l 3 u).mpr
      have hb := (actualBoundaryRootTraceMembership k 1 u).mp hroot
      rw [hcoordk,hshared,← hcoordl] at hb
      exact hb
    have hcount := actualTwoCellCylinderEndpointCount k l hkl (1,u) (0,u) p hp
      (congrArg cylinderProjection hshared)
      (fun e r hr he => actualTimeRootCylinderCellAlternatives k l u hu htime hphase e r he)
    have hcountk := actualRootCellEndpointCount k 1 u hroot
    rw [hcoordk] at hcountk
    have hcountl := actualRootCellEndpointCount l 3 u hrootl
    rw [hcoordl] at hcountl
    rw [hcount,hcountk,hcountl]
    exact actualTimeAdjacentFaceIncidencesEven k l htime hphase u hroot
  have actualPhaseRootCylinderIncidenceEven (k l : activeCells)
      (htime : k.val.1 = l.val.1) (hphase : k.val.2.succ = l.val.2.castSucc)
      (u : Interval) (hroot : actualFaceHeight (k,2) u = 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (u,1))) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    obtain ⟨j,hj,hj0,hj1⟩ := actualFaceZeroIsInternalMesh (k,2) u hroot
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      hj ▸ actualInternalMeshNodeOpenParameter (k,2) j hj0 hj1
    have hkl : k ≠ l := by
      intro he
      have ht := congrArg (fun j : Fin (n+2) => j.val) hphase
      rw [← he] at ht
      change k.val.2.val+1 = k.val.2.val at ht
      omega
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hshared := actualPhaseNeighborCellPoint k l htime hphase u
    have hrootl : actualFaceHeight (l,0) u = 0 := by
      apply (actualBoundaryRootTraceMembership l 0 u).mpr
      have hb := (actualBoundaryRootTraceMembership k 2 u).mp hroot
      rw [hcoordk,hshared,← hcoordl] at hb
      exact hb
    have hcount := actualTwoCellCylinderEndpointCount k l hkl (u,1) (u,0) p hp
      (congrArg cylinderProjection hshared)
      (fun e r hr he => actualPhaseRootCylinderCellAlternatives k l u hu htime hphase e r he)
    have hcountk := actualRootCellEndpointCount k 2 u hroot
    rw [hcoordk] at hcountk
    have hcountl := actualRootCellEndpointCount l 0 u hrootl
    rw [hcoordl] at hcountl
    rw [hcount,hcountk,hcountl]
    exact actualPhaseAdjacentFaceIncidencesEven k l htime hphase u hroot
  let cylinderZeroEdge (e : zeroEdgeIndex) : C(Interval,Interval × Circle) :=
    (cellCylinder e.1.1.val).comp (zeroEdge e)
  have cylinderZeroEdgeEmbedding (e : zeroEdgeIndex) : Topology.IsEmbedding (cylinderZeroEdge e) :=
    (cellCylinderEmbedding e.1.1.val).comp (zeroEdgeEmbedding e)
  have cylinderZeroEdgeEndpoints (e : zeroEdgeIndex) :
      cylinderZeroEdge e 0 = zeroEndpointLeft e ∧ cylinderZeroEdge e 1 = zeroEndpointRight e :=
    ⟨rfl,rfl⟩
  have intervalExpOffOne (u v : Interval) (hu : u ≠ 1) (hv : v ≠ 1)
      (he : Circle.exp (2*Real.pi*u.val) = Circle.exp (2*Real.pi*v.val)) : u = v := by
    have hmem (t : Interval) (ht : t ≠ 1) :
        2*Real.pi*t.val ∈ Set.Ico (0 : ℝ) (2*Real.pi) := by
      have hlt : t.val < 1 := lt_of_le_of_ne t.property.2 (by intro h; apply ht; exact Subtype.ext h)
      constructor
      · exact mul_nonneg (by positivity : 0 ≤ 2*Real.pi) t.property.1
      · have hh := mul_lt_mul_of_pos_left hlt (by positivity : 0 < 2*Real.pi)
        simpa only [mul_one] using hh
    have hh := Circle.exp_injOn_Ico (by simp : 2*Real.pi-0 ≤ 2*Real.pi)
      (hmem u hu) (hmem v hv) he
    apply Subtype.ext
    exact mul_left_cancel₀ (by positivity : (2*Real.pi : ℝ) ≠ 0) hh
  have cylinderZeroInteriorSameCell (e f : zeroEdgeIndex) (t u : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (heq : cylinderZeroEdge e t = cylinderZeroEdge f u) :
      e.1.1.val = f.1.1.val := by
    have hnotOne (d : zeroEdgeIndex) (r : Interval)
        (hr : r ∈ Set.Ioo (0 : Interval) 1) : (globalZeroEdge d r).2 ≠ 1 := by
      have hh := (globalZeroEdgeInterior d r hr).2.2
      have hlt : (globalZeroEdge d r).2 < 1 :=
        lt_of_lt_of_le hh (phaseGrid d.1.1.val.2.succ).property.2
      exact ne_of_lt hlt
    have hfirst : (globalZeroEdge e t).1 = (globalZeroEdge f u).1 :=
      congrArg (fun z : Interval × Circle => z.1) heq
    have hangle : Circle.exp (2*Real.pi*(globalZeroEdge e t).2.val) =
        Circle.exp (2*Real.pi*(globalZeroEdge f u).2.val) :=
      congrArg (fun z : Interval × Circle => z.2) heq
    have hsecond := intervalExpOffOne _ _ (hnotOne e t ht) (hnotOne f u hu) hangle
    exact globalZeroInteriorSameCell e f t u ht hu (Prod.ext hfirst hsecond)
  have cylinderZeroEdgeInteriorsDisjoint (e f : zeroEdgeIndex) (t u : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (heq : cylinderZeroEdge e t = cylinderZeroEdge f u) : e = f := by
    have hcell := cylinderZeroInteriorSameCell e f t u ht hu heq
    rcases e with ⟨⟨k,i⟩,x⟩
    rcases f with ⟨⟨l,j⟩,y⟩
    have hkl : k = l := Subtype.ext hcell
    subst l
    have hp : zeroEdge ⟨(k,i),x⟩ t = zeroEdge ⟨(k,j),y⟩ u :=
      (cellCylinderEmbedding k.val).injective heq
    obtain ⟨r,z,hz,hzp,hr,hr01⟩ := zeroParameterInterior ⟨(k,i),x⟩ t ht
    obtain ⟨s,w,hw,hwp,hs,hs01⟩ := zeroParameterInterior ⟨(k,j),y⟩ u hu
    have hzw : z = w := activeFaceRadialInjective k i
      (hzp.symm.trans (hp.trans (hwp.trans (activeFaceRadialAgreement k j i w))))
    have hface : boundaryFace i r = boundaryFace j s :=
      hz.symm.trans ((congrArg Subtype.val hzw).trans hw)
    have hij : i = j := boundaryFaceInteriorUnique i j r s hr01 hs01 hface
    subst j
    have hrs : r = s := boundaryFaceInjective i hface
    rw [← hrs] at hs
    have hxy : x.val = y.val := by
      rcases lt_trichotomy x.val y.val with hlt | he | hgt
      · have hle : x.val.succ ≤ y.val.castSucc := by
          change x.val.val+1 ≤ y.val.val; exact hlt
        have hm := (activeFaceMono (k,i)).monotone hle
        exact False.elim (not_lt_of_ge (le_trans hm hs.1.le) hr.2)
      · exact he
      · have hle : y.val.succ ≤ x.val.castSucc := by
          change y.val.val+1 ≤ x.val.val; exact hgt
        have hm := (activeFaceMono (k,i)).monotone hle
        exact False.elim (not_lt_of_ge (le_trans hm hr.1.le) hs.2)
    have hxy' : x = y := Subtype.ext hxy
    subst y
    rfl
  have intervalExpFiber (u v : Interval)
      (he : Circle.exp (2*Real.pi*u.val) = Circle.exp (2*Real.pi*v.val)) :
      u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
    by_cases hu : u = 1
    · by_cases hv : v = 1
      · exact Or.inl (hu.trans hv.symm)
      · have he0 : Circle.exp (2*Real.pi*v.val) = Circle.exp (2*Real.pi*(0 : Interval).val) := by
          simpa [hu] using he.symm
        exact Or.inr (Or.inr ⟨hu,intervalExpOffOne v 0 hv (by norm_num) he0⟩)
    · by_cases hv : v = 1
      · have he0 : Circle.exp (2*Real.pi*u.val) = Circle.exp (2*Real.pi*(0 : Interval).val) := by
          simpa [hv] using he
        exact Or.inr (Or.inl ⟨intervalExpOffOne u 0 hu (by norm_num) he0,hv⟩)
      · exact Or.inl (intervalExpOffOne u v hu hv he)
  have cylinderZeroInteriorAvoidEndpoints (e f : zeroEdgeIndex) (t v : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1) (hv : v = 0 ∨ v = 1) :
      cylinderZeroEdge e t ≠ cylinderZeroEdge f v := by
    intro heq
    obtain ⟨he1,he2⟩ := globalZeroEdgeInterior e t ht
    obtain ⟨hf1,hf2⟩ := globalZeroClosedCoordinates f v
    have ht0 : 0 < (globalZeroEdge e t).2 :=
      lt_of_le_of_lt (phaseGrid e.1.1.val.2.castSucc).property.1 he2.1
    have ht1 : (globalZeroEdge e t).2 < 1 :=
      lt_of_lt_of_le he2.2 (phaseGrid e.1.1.val.2.succ).property.2
    have hfirst : (globalZeroEdge e t).1 = (globalZeroEdge f v).1 :=
      congrArg (fun z : Interval × Circle => z.1) heq
    have hangle : Circle.exp (2*Real.pi*(globalZeroEdge e t).2.val) =
        Circle.exp (2*Real.pi*(globalZeroEdge f v).2.val) :=
      congrArg (fun z : Interval × Circle => z.2) heq
    have hsecond : (globalZeroEdge e t).2 = (globalZeroEdge f v).2 := by
      rcases intervalExpFiber _ _ hangle with h | h | h
      · exact h
      · exact False.elim ((ne_of_gt ht0) h.1)
      · exact False.elim ((ne_of_lt ht1) h.1)
    rw [← hfirst] at hf1
    rw [← hsecond] at hf2
    have hcell : e.1.1.val = f.1.1.val := Prod.ext
      (phaseOpenClosedUnique _ _ _ he1 hf1) (phaseOpenClosedUnique _ _ _ he2 hf2)
    rcases e with ⟨⟨k,i⟩,x⟩
    rcases f with ⟨⟨l,j⟩,y⟩
    have hkl : k = l := Subtype.ext hcell
    subst l
    have hp : zeroEdge ⟨(k,i),x⟩ t = zeroEdge ⟨(k,j),y⟩ v :=
      (cellCylinderEmbedding k.val).injective heq
    obtain ⟨r,z,hz,hzp,hr,hr01⟩ := zeroParameterInterior ⟨(k,i),x⟩ t ht
    obtain ⟨s,w,hsval,hw,hwp,hneg⟩ := zeroParameter ⟨(k,j),y⟩ v
    have hzw : z = w := activeFaceRadialInjective k i
      (hzp.symm.trans (hp.trans (hwp.trans (activeFaceRadialAgreement k j i w))))
    have hface : boundaryFace i r = boundaryFace j s :=
      hz.symm.trans ((congrArg Subtype.val hzw).trans hw)
    have hij : i = j := boundaryFaceOpenUnique i j r s hr01 hface
    subst j
    have hrs : r = s := boundaryFaceInjective i hface
    have noMeshVertex (q : Fin (activeFaceSize (k,i)+2))
        (hq : r = activeFaceMesh (k,i) q) : False := by
      have hleft := (activeFaceMono (k,i)).lt_iff_lt.mp (hq ▸ hr.1)
      have hright := (activeFaceMono (k,i)).lt_iff_lt.mp (hq ▸ hr.2)
      change x.val.val < q.val at hleft
      change q.val < x.val.val+1 at hright
      omega
    rcases hv with hv | hv
    · have hs : s = activeFaceMesh (k,i) y.val.castSucc := by
        apply Subtype.ext
        simpa [hv] using hsval
      exact noMeshVertex _ (hrs.trans hs)
    · have hs : s = activeFaceMesh (k,i) y.val.succ := by
        apply Subtype.ext
        simpa [hv] using hsval
      exact noMeshVertex _ (hrs.trans hs)
  have actualZeroEdgeCollisionClassification (e f : zeroEdgeIndex) (t u : Interval)
      (he : cylinderZeroEdge e t = cylinderZeroEdge f u) :
      (e = f ∧ t = u) ∨
        ((t = (0 : Interval) ∨ t = 1) ∧ (u = (0 : Interval) ∨ u = 1)) := by
    by_cases ht : t = (0 : Interval) ∨ t = 1
    · by_cases hu : u = (0 : Interval) ∨ u = 1
      · exact Or.inr ⟨ht,hu⟩
      · have huI : u ∈ Set.Ioo (0 : Interval) 1 := by
          constructor
          · exact lt_of_le_of_ne u.property.1 (by intro h; exact hu (Or.inl h.symm))
          · exact lt_of_le_of_ne u.property.2 (by intro h; exact hu (Or.inr h))
        exact False.elim (cylinderZeroInteriorAvoidEndpoints f e u t huI ht he.symm)
    · have htI : t ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · exact lt_of_le_of_ne t.property.1 (by intro h; exact ht (Or.inl h.symm))
        · exact lt_of_le_of_ne t.property.2 (by intro h; exact ht (Or.inr h))
      by_cases hu : u = (0 : Interval) ∨ u = 1
      · exact False.elim (cylinderZeroInteriorAvoidEndpoints e f t u htI hu he)
      · have huI : u ∈ Set.Ioo (0 : Interval) 1 := by
          constructor
          · exact lt_of_le_of_ne u.property.1 (by intro h; exact hu (Or.inl h.symm))
          · exact lt_of_le_of_ne u.property.2 (by intro h; exact hu (Or.inr h))
        have hef := cylinderZeroEdgeInteriorsDisjoint e f t u htI huI he
        subst f
        exact Or.inl ⟨rfl,(cylinderZeroEdgeEmbedding e).injective he⟩
  let privateParameter : Fin 2 → Interval := fun j =>
    if j = 0 then ⟨1/3,by norm_num⟩ else ⟨2/3,by norm_num⟩
  have privateParameterInterior (j : Fin 2) :
      privateParameter j ∈ Set.Ioo (0 : Interval) 1 := by
    change 0 < (privateParameter j).val ∧ (privateParameter j).val < 1
    fin_cases j <;> norm_num [privateParameter]
  have privateParameterInjective : Function.Injective privateParameter := by
    intro j k he
    have hh := congrArg Subtype.val he
    fin_cases j <;> fin_cases k <;> first | rfl | (norm_num [privateParameter] at hh)
  let zeroVertexPosition : zeroVertex → Interval × Circle := fun v =>
    match v with
    | Sum.inl p => p.val
    | Sum.inr (e,j) => cylinderZeroEdge e (privateParameter j)
  have zeroVertexPositionInjective : Function.Injective zeroVertexPosition := by
    intro v w he
    rcases v with p | ⟨e,j⟩ <;> rcases w with q | ⟨f,k⟩
    · exact congrArg Sum.inl (Subtype.ext he)
    · have hp : p.val ∈ zeroEndpointSet := p.property
      rcases hp with hp | hp
      · obtain ⟨d,hd⟩ := hp
        have hh : cylinderZeroEdge f (privateParameter k) = cylinderZeroEdge d 0 :=
          he.symm.trans hd.symm
        exact False.elim (cylinderZeroInteriorAvoidEndpoints f d _ 0
          (privateParameterInterior k) (Or.inl rfl) hh)
      · obtain ⟨d,hd⟩ := hp
        have hh : cylinderZeroEdge f (privateParameter k) = cylinderZeroEdge d 1 :=
          he.symm.trans hd.symm
        exact False.elim (cylinderZeroInteriorAvoidEndpoints f d _ 1
          (privateParameterInterior k) (Or.inr rfl) hh)
    · have hq : q.val ∈ zeroEndpointSet := q.property
      rcases hq with hq | hq
      · obtain ⟨d,hd⟩ := hq
        have hh : cylinderZeroEdge e (privateParameter j) = cylinderZeroEdge d 0 :=
          he.trans hd.symm
        exact False.elim (cylinderZeroInteriorAvoidEndpoints e d _ 0
          (privateParameterInterior j) (Or.inl rfl) hh)
      · obtain ⟨d,hd⟩ := hq
        have hh : cylinderZeroEdge e (privateParameter j) = cylinderZeroEdge d 1 :=
          he.trans hd.symm
        exact False.elim (cylinderZeroInteriorAvoidEndpoints e d _ 1
          (privateParameterInterior j) (Or.inr rfl) hh)
    · have hef : e = f := cylinderZeroEdgeInteriorsDisjoint e f _ _
        (privateParameterInterior j) (privateParameterInterior k) he
      subst f
      have hjk := privateParameterInjective ((cylinderZeroEdgeEmbedding e).injective he)
      subst k
      rfl
  have actualZeroVertexOnEdgeBreakpoint (v : zeroVertex) (e : zeroEdgeIndex)
      (t : Interval) (he : zeroVertexPosition v = cylinderZeroEdge e t) :
      t = 0 ∨ t = privateParameter 0 ∨ t = privateParameter 1 ∨ t = 1 := by
    have oldEndpointCollision (f : zeroEdgeIndex) (u : Interval)
        (hu : u = 0 ∨ u = 1) (h : cylinderZeroEdge e t = cylinderZeroEdge f u) :
        t = 0 ∨ t = 1 := by
      rcases actualZeroEdgeCollisionClassification e f t u h with ⟨hef,htu⟩ | ⟨ht,hu'⟩
      · rwa [htu]
      · exact ht
    rcases v with p | ⟨f,j⟩
    · rcases p.property with hleft | hright
      · obtain ⟨f,hf⟩ := hleft
        have h : cylinderZeroEdge e t = cylinderZeroEdge f 0 := he.symm.trans hf.symm
        rcases oldEndpointCollision f 0 (Or.inl rfl) h with h0 | h1
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inr h1))
      · obtain ⟨f,hf⟩ := hright
        have h : cylinderZeroEdge e t = cylinderZeroEdge f 1 := he.symm.trans hf.symm
        rcases oldEndpointCollision f 1 (Or.inr rfl) h with h0 | h1
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inr h1))
    · change cylinderZeroEdge f (privateParameter j) = cylinderZeroEdge e t at he
      rcases actualZeroEdgeCollisionClassification e f t (privateParameter j) he.symm with
        ⟨hef,htu⟩ | ⟨ht,hu⟩
      · fin_cases j
        · exact Or.inr (Or.inl htu)
        · exact Or.inr (Or.inr (Or.inl htu))
      · rcases hu with hu | hu
        · have h := (privateParameterInterior j).1
          rw [hu] at h
          exact False.elim (lt_irrefl _ h)
        · have h := (privateParameterInterior j).2
          rw [hu] at h
          exact False.elim (lt_irrefl _ h)
  have cylinderProjectionSurjective : Function.Surjective cylinderProjection := by
    have hcover : Circle.exp '' Set.Icc (0 : ℝ) (2*Real.pi) = Set.univ := by
      rw [show 2*Real.pi = 0+2*Real.pi by ring,
        Circle.periodic_exp.image_Icc (by positivity : 0 < 2*Real.pi),Circle.exp_surjective.range_eq]
    intro p
    have hp : p.2 ∈ Circle.exp '' Set.Icc (0 : ℝ) (2*Real.pi) := by rw [hcover]; trivial
    obtain ⟨r,hr,hp⟩ := hp
    let u : Interval := ⟨r/(2*Real.pi),⟨div_nonneg hr.1 (by positivity),
      (div_le_one (by positivity : 0 < 2*Real.pi)).mpr hr.2⟩⟩
    refine ⟨(p.1,u),?_⟩
    apply Prod.ext
    · rfl
    · change Circle.exp (2*Real.pi*(r/(2*Real.pi))) = p.2
      rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi : ℝ) ≠ 0)]
      exact hp
  have regularizedRespectsCylinder (p q : Interval × Interval)
      (he : cylinderProjection p = cylinderProjection q) : regularizedTrace p = regularizedTrace q := by
    have ht : p.1 = q.1 := congrArg (fun z : Interval × Circle => z.1) he
    have hs := congrArg Prod.snd he
    rcases intervalExpFiber p.2 q.2 hs with hs | ⟨hp,hq⟩ | ⟨hp,hq⟩
    · have hpq : p = q := Prod.ext ht hs
      rw [hpq]
    · have hp' : p = (q.1,0) := Prod.ext ht hp
      have hq' : q = (q.1,1) := Prod.ext rfl hq
      rw [hp',hq']; exact regularizedSeam q.1
    · have hp' : p = (q.1,1) := Prod.ext ht hp
      have hq' : q = (q.1,0) := Prod.ext rfl hq
      rw [hp',hq']; exact (regularizedSeam q.1).symm
  let cylinderTraceFun : Interval × Circle → S := fun p =>
    regularizedTrace (Function.surjInv cylinderProjectionSurjective p)
  have cylinderTraceOnSquare (p : Interval × Interval) :
      cylinderTraceFun (cylinderProjection p) = regularizedTrace p :=
    regularizedRespectsCylinder _ p (Function.surjInv_eq cylinderProjectionSurjective _)
  have cylinderTraceContinuous : Continuous cylinderTraceFun := by
    have hquot := cylinderProjection.continuous.isClosedMap.isQuotientMap
      cylinderProjection.continuous cylinderProjectionSurjective
    apply hquot.continuous_iff.mpr
    have he : cylinderTraceFun ∘ cylinderProjection = regularizedTrace := funext cylinderTraceOnSquare
    rw [he]
    exact regularizedTrace.continuous
  let cylinderTrace : C(Interval × Circle,S) := ⟨cylinderTraceFun,cylinderTraceContinuous⟩
  have actualSeamRootCylinderIncidenceEven (k l : activeCells)
      (htime : k.val.1 = l.val.1) (hkphase : k.val.2 = 0)
      (hlphase : l.val.2 = Fin.last n)
      (u : Interval) (hroot : actualFaceHeight (k,0) u = 0)
      (p : zeroEndpointSet)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (u,0))) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    obtain ⟨j,hj,hj0,hj1⟩ := actualFaceZeroIsInternalMesh (k,0) u hroot
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      hj ▸ actualInternalMeshNodeOpenParameter (k,0) j hj0 hj1
    have hkl : k ≠ l := by
      intro he
      have ht := congrArg (fun c : activeCells => c.val.2) he
      rw [hkphase,hlphase] at ht
      have hv := congrArg (fun j : Fin (n+1) => j.val) ht
      change 0 = n at hv
      omega
    have hcoordk : squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hcoordl : squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
    have hshared := actualSeamCellPoint k l htime hkphase hlphase u
    have hrootl : actualFaceHeight (l,2) u = 0 := by
      apply (actualBoundaryRootTraceMembership l 2 u).mpr
      have hb := (actualBoundaryRootTraceMembership k 0 u).mp hroot
      rw [hcoordk] at hb
      rw [hcoordl]
      have heTrace : regularizedTrace (cellToGlobal k.val (u,0)) =
          regularizedTrace (cellToGlobal l.val (u,1)) := by
        rw [← cylinderTraceOnSquare,← cylinderTraceOnSquare]
        exact congrArg cylinderTrace hshared
      rw [heTrace] at hb
      exact hb
    have hcount := actualTwoCellCylinderEndpointCount k l hkl (u,0) (u,1) p hp
      hshared
      (fun e r hr he => actualSeamRootCylinderCellAlternatives k l htime hkphase hlphase u hu e r he)
    have hcountk := actualRootCellEndpointCount k 0 u hroot
    rw [hcoordk] at hcountk
    have hcountl := actualRootCellEndpointCount l 2 u hrootl
    rw [hcoordl] at hcountl
    rw [hcount,hcountk,hcountl]
    exact actualSeamFaceIncidencesEven k l htime hkphase hlphase u hroot
  have cylinderZeroEdgesOnComparison (e : zeroEdgeIndex) (t : Interval) :
      cylinderTrace (cylinderZeroEdge e t) ∈ b.val.image := by
    change cylinderTraceFun (cylinderProjection (globalZeroEdge e t)) ∈ b.val.image
    rw [cylinderTraceOnSquare]
    exact globalZeroEdgeOnComparison e t
  have zeroVertexOnComparison (v : zeroVertex) :
      cylinderTrace (zeroVertexPosition v) ∈ b.val.image := by
    rcases v with p | ⟨e,j⟩
    · rcases p.property with hp | hp
      · obtain ⟨e,he⟩ := hp
        change cylinderTrace p.val ∈ b.val.image
        rw [← he]
        exact cylinderZeroEdgesOnComparison e 0
      · obtain ⟨e,he⟩ := hp
        change cylinderTrace p.val ∈ b.val.image
        rw [← he]
        exact cylinderZeroEdgesOnComparison e 1
    · exact cylinderZeroEdgesOnComparison e (privateParameter j)
  have actualEmbeddedEdgeSubpath (e : zeroEdgeIndex) (r s : Interval) (hrs : r < s) :
      ∃ p : Path (cylinderZeroEdge e r) (cylinderZeroEdge e s),
        Topology.IsEmbedding p ∧
        Set.range p ⊆ cylinderZeroEdge e '' Set.Icc r s ∧
        p '' Set.Ioo (0 : Interval) 1 ⊆ cylinderZeroEdge e '' Set.Ioo r s ∧
        ∀ t, cylinderTrace (p t) ∈ b.val.image := by
    obtain ⟨p,hp,hrange,hinterior⟩ := actual_embedded_affine_subarc
      (cylinderZeroEdge e) (cylinderZeroEdgeEmbedding e) r s hrs
    refine ⟨p,hp,hrange,hinterior,?_⟩
    intro t
    obtain ⟨u,hu,he⟩ := hrange ⟨t,rfl⟩
    rw [← he]
    exact cylinderZeroEdgesOnComparison e u
  have actualPrivateParametersOrdered :
      (0 : Interval) < privateParameter 0 ∧
      privateParameter 0 < privateParameter 1 ∧ privateParameter 1 < 1 := by
    change 0 < (privateParameter 0).val ∧
      (privateParameter 0).val < (privateParameter 1).val ∧ (privateParameter 1).val < 1
    norm_num [privateParameter]
  have actualDirectedEmbeddedGeometricPath (v w : zeroVertex)
      (hv : zeroDirectedIncidence v w) :
      ∃ p : Path (zeroVertexPosition v) (zeroVertexPosition w),
        Topology.IsEmbedding p ∧ ∀ t, cylinderTrace (p t) ∈ b.val.image := by
    obtain ⟨e,h | h | h⟩ := hv
    · rcases h with ⟨rfl,rfl⟩
      obtain ⟨p,hp,_,_,hb⟩ := actualEmbeddedEdgeSubpath e 0 (privateParameter 0)
        actualPrivateParametersOrdered.1
      exact ⟨p,hp,hb⟩
    · rcases h with ⟨rfl,rfl⟩
      obtain ⟨p,hp,_,_,hb⟩ := actualEmbeddedEdgeSubpath e (privateParameter 0) (privateParameter 1)
        actualPrivateParametersOrdered.2.1
      exact ⟨p,hp,hb⟩
    · rcases h with ⟨rfl,rfl⟩
      obtain ⟨p,hp,_,_,hb⟩ := actualEmbeddedEdgeSubpath e (privateParameter 1) 1
        actualPrivateParametersOrdered.2.2
      exact ⟨p,hp,hb⟩
  have actualEdgeSubpath (e : zeroEdgeIndex) (r s : Interval) :
      ∃ p : Path (cylinderZeroEdge e r) (cylinderZeroEdge e s),
        ∀ t, cylinderTrace (p t) ∈ b.val.image := by
    let d : Path r s := {
      toFun := fun t => ⟨(1-t.val)*r.val+t.val*s.val,by
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) r.property.1)
            (mul_nonneg t.property.1 s.property.1)
        · nlinarith only [t.property.1,t.property.2,r.property.1,r.property.2,s.property.1,s.property.2]⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
    exact ⟨d.map (cylinderZeroEdge e).continuous,
      fun t => cylinderZeroEdgesOnComparison e (d t)⟩
  have zeroDirectedGeometricPath (v w : zeroVertex) (hv : zeroDirectedIncidence v w) :
      ∃ p : Path (zeroVertexPosition v) (zeroVertexPosition w),
        ∀ t, cylinderTrace (p t) ∈ b.val.image := by
    obtain ⟨e,h | h | h⟩ := hv
    · rcases h with ⟨rfl,rfl⟩
      exact actualEdgeSubpath e 0 (privateParameter 0)
    · rcases h with ⟨rfl,rfl⟩
      exact actualEdgeSubpath e (privateParameter 0) (privateParameter 1)
    · rcases h with ⟨rfl,rfl⟩
      exact actualEdgeSubpath e (privateParameter 1) 1
  have actualGraphGeometricPath (v w : zeroVertex) (h : actualZeroGraph.Adj v w) :
      ∃ p : Path (zeroVertexPosition v) (zeroVertexPosition w),
        ∀ t, cylinderTrace (p t) ∈ b.val.image := by
    have hh : v ≠ w ∧ (zeroDirectedIncidence v w ∨ zeroDirectedIncidence w v) := h
    rcases hh.2 with hd | hd
    · exact zeroDirectedGeometricPath v w hd
    · obtain ⟨p,hp⟩ := zeroDirectedGeometricPath w v hd
      exact ⟨p.symm,fun t => hp (unitInterval.symm t)⟩
  have actualGraphWalkGeometricPath {v w : zeroVertex} (walk : actualZeroGraph.Walk v w) :
      ∃ p : Path (zeroVertexPosition v) (zeroVertexPosition w),
        Set.range (cylinderTrace ∘ p) ⊆ b.val.image := by
    induction walk with
    | nil =>
      refine ⟨Path.refl _,?_⟩
      rintro _ ⟨t,rfl⟩
      exact zeroVertexOnComparison _
    | @cons v u w h walk ih =>
      obtain ⟨p,hp⟩ := actualGraphGeometricPath v u h
      obtain ⟨q,hq⟩ := ih
      refine ⟨p.trans q,?_⟩
      rintro _ ⟨t,rfl⟩
      have hm : p.trans q t ∈ Set.range p ∪ Set.range q := by
        rw [← Path.trans_range]
        exact ⟨t,rfl⟩
      rcases hm with ⟨r,hr⟩ | ⟨r,hr⟩
      · change cylinderTrace (p.trans q t) ∈ b.val.image
        rw [← hr]; exact hp r
      · change cylinderTrace (p.trans q t) ∈ b.val.image
        rw [← hr]; exact hq ⟨r,rfl⟩
  have globalBottomEventCoverage (t : Interval)
      (hB : regularizedTrace (0,t) ∈ b.val.image) :
      ∃ e : zeroEdgeIndex, globalZeroEdge e 0 = (0,t) ∨ globalZeroEdge e 1 = (0,t) := by
    obtain ⟨j,hj0,hj1⟩ := phaseGridCovers t
    let r := localCoordinate j t
    have hcell : (0,t) ∈ cellDomain (0,j) := by
      refine ⟨?_,(phaseGrid (Fin.succ 0)).property.1,hj0,hj1⟩
      change phaseGrid (0 : Fin (n+2)) ≤ 0
      simp [phaseGrid]
    have hlocal : regularizedCells (0,j) (0,r) ∈ b.val.image := by
      rw [regularizedOnCells (0,j) (0,t) hcell] at hB
      change regularizedCells (0,j) (localCoordinate 0 0,r) ∈ b.val.image at hB
      rwa [coordinateZero] at hB
    have hactive : ¬ Disjoint (chartDomain (chart (0,j))) b.val.image := by
      intro hd
      exact Set.disjoint_left.mp hd (regularizedCellRange (0,j) (0,r)) hlocal
    let k : activeCells := ⟨(0,j),hactive⟩
    have hcoords : squareCoordinates
        ⟨(boundaryFace 3 r).val,(boundaryFace 3 r).property.le⟩ = (0,r) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
        <;> ring
    have hroot : actualFaceHeight (k,3) r = 0 := by
      have hn := (activeCellAxis k _ (regularizedCellRange k.val (0,r))).mp hlocal
      have hf := actualCellBoundaryFormula k.val (boundaryFace 3 r)
      rw [hcoords] at hf
      rw [hf] at hn
      change (regularizedCellLoops k.val (boundaryFace 3 r)).val.1 /
        (cellCenter k.val).val.1 = 0
      rw [hn]
      simp
    obtain ⟨e,he,hpos⟩ := (actualBottomFaceZeroCovered k rfl r hroot).1
    have hk : e.1.1.val = (0,j) := congrArg (fun p : activeCells × Fin 4 => p.1.val) he
    have hparam : cellToGlobal (0,j) (0,r) = (0,t) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [cellToGlobal,phaseGrid]
      · exact localCoordinateAffine j t hj0 hj1
    refine ⟨e,?_⟩
    rcases hpos with hp | hp
    · left
      change cellToGlobal e.1.1.val (zeroEdge e 0) = (0,t)
      rw [hp,hk]
      exact hparam
    · right
      change cellToGlobal e.1.1.val (zeroEdge e 1) = (0,t)
      rw [hp,hk]
      exact hparam

  have globalTopEventCoverage (t : Interval)
      (hB : regularizedTrace (1,t) ∈ b.val.image) :
      ∃ e : zeroEdgeIndex, globalZeroEdge e 0 = (1,t) ∨ globalZeroEdge e 1 = (1,t) := by
    obtain ⟨j,hj0,hj1⟩ := phaseGridCovers t
    let r := localCoordinate j t
    have hcell : (1,t) ∈ cellDomain (Fin.last n,j) := by
      refine ⟨(phaseGrid (Fin.last n).castSucc).property.2,?_,hj0,hj1⟩
      change (1 : Interval) ≤ phaseGrid (Fin.last n).succ
      simp [lastSucc,phaseGrid]
    have hlocal : regularizedCells (Fin.last n,j) (1,r) ∈ b.val.image := by
      rw [regularizedOnCells (Fin.last n,j) (1,t) hcell] at hB
      change regularizedCells (Fin.last n,j) (localCoordinate (Fin.last n) 1,r) ∈ b.val.image at hB
      rwa [coordinateOne] at hB
    have hactive : ¬ Disjoint (chartDomain (chart (Fin.last n,j))) b.val.image := by
      intro hd
      exact Set.disjoint_left.mp hd (regularizedCellRange (Fin.last n,j) (1,r)) hlocal
    let k : activeCells := ⟨(Fin.last n,j),hactive⟩
    have hcoords : squareCoordinates
        ⟨(boundaryFace 1 r).val,(boundaryFace 1 r).property.le⟩ = (1,r) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
        <;> ring
    have hroot : actualFaceHeight (k,1) r = 0 := by
      have hn := (activeCellAxis k _ (regularizedCellRange k.val (1,r))).mp hlocal
      have hf := actualCellBoundaryFormula k.val (boundaryFace 1 r)
      rw [hcoords] at hf
      rw [hf] at hn
      change (regularizedCellLoops k.val (boundaryFace 1 r)).val.1 /
        (cellCenter k.val).val.1 = 0
      rw [hn]
      simp
    obtain ⟨e,he,hpos⟩ := (actualTopFaceZeroCovered k rfl r hroot).1
    have hk : e.1.1.val = (Fin.last n,j) := congrArg (fun p : activeCells × Fin 4 => p.1.val) he
    have hparam : cellToGlobal (Fin.last n,j) (1,r) = (1,t) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [cellToGlobal,lastSucc,phaseGrid]
      · exact localCoordinateAffine j t hj0 hj1
    refine ⟨e,?_⟩
    rcases hpos with hp | hp
    · left
      change cellToGlobal e.1.1.val (zeroEdge e 0) = (1,t)
      rw [hp,hk]
      exact hparam
    · right
      change cellToGlobal e.1.1.val (zeroEdge e 1) = (1,t)
      rw [hp,hk]
      exact hparam

  have cylinderBoundaryOriginal (z : Circle) :
      cylinderTrace (0,z) = a.val.map (z₀*z) ∧
      cylinderTrace (1,z) = endCurve.map (z₀*z) := by
    obtain ⟨p,hp⟩ := cylinderProjectionSurjective (0,z)
    have hez : Circle.exp (2*Real.pi*p.2.val) = z := congrArg Prod.snd hp
    have h0 : cylinderProjection (0,p.2) = (0,z) := Prod.ext rfl hez
    have h1 : cylinderProjection (1,p.2) = (1,z) := Prod.ext rfl hez
    constructor
    · rw [← h0]
      change cylinderTraceFun (cylinderProjection (0,p.2)) = a.val.map (z₀*z)
      rw [cylinderTraceOnSquare,(regularizedOriginalBoundary p.2).1,Fzero]
      change a.val.map (z₀ * Circle.exp (2*Real.pi*p.2.val)) = a.val.map (z₀*z)
      rw [hez]
    · rw [← h1]
      change cylinderTraceFun (cylinderProjection (1,p.2)) = endCurve.map (z₀*z)
      rw [cylinderTraceOnSquare,(regularizedOriginalBoundary p.2).2,Fone]
      change endCurve.map (z₀ * Circle.exp (2*Real.pi*p.2.val)) = endCurve.map (z₀*z)
      rw [hez]
  let actualSegmentStartParameter (q : zeroEdgeIndex × Fin 3) : Interval :=
    if q.2 = 0 then 0 else if q.2 = 1 then privateParameter 0 else privateParameter 1
  let actualSegmentEndParameter (q : zeroEdgeIndex × Fin 3) : Interval :=
    if q.2 = 0 then privateParameter 0 else if q.2 = 1 then privateParameter 1 else 1
  let actualSegmentStartVertex (q : zeroEdgeIndex × Fin 3) : zeroVertex :=
    if q.2 = 0 then zeroLeftVertex q.1 else if q.2 = 1 then Sum.inr (q.1,0) else Sum.inr (q.1,1)
  let actualSegmentEndVertex (q : zeroEdgeIndex × Fin 3) : zeroVertex :=
    if q.2 = 0 then Sum.inr (q.1,0) else if q.2 = 1 then Sum.inr (q.1,1) else zeroRightVertex q.1
  have actualSegmentParameterOrder (q : zeroEdgeIndex × Fin 3) :
      actualSegmentStartParameter q < actualSegmentEndParameter q := by
    rcases q with ⟨e,j⟩
    fin_cases j
    · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.1
    · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.1
    · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.2
  let actualSegmentCylinderPath (q : zeroEdgeIndex × Fin 3) :
      Path (cylinderZeroEdge q.1 (actualSegmentStartParameter q))
        (cylinderZeroEdge q.1 (actualSegmentEndParameter q)) :=
    Classical.choose (actualEmbeddedEdgeSubpath q.1 _ _ (actualSegmentParameterOrder q))
  have actualSegmentCylinderPathEmbedding (q : zeroEdgeIndex × Fin 3) :
      Topology.IsEmbedding (actualSegmentCylinderPath q) :=
    (Classical.choose_spec (actualEmbeddedEdgeSubpath q.1 _ _ (actualSegmentParameterOrder q))).1
  have actualSegmentCylinderPathRange (q : zeroEdgeIndex × Fin 3) :
      Set.range (actualSegmentCylinderPath q) ⊆ cylinderZeroEdge q.1 ''
        Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q) :=
    (Classical.choose_spec (actualEmbeddedEdgeSubpath q.1 _ _ (actualSegmentParameterOrder q))).2.1
  have actualSegmentCylinderPathOnComparison (q : zeroEdgeIndex × Fin 3) (t : Interval) :
      cylinderTrace (actualSegmentCylinderPath q t) ∈ b.val.image :=
    (Classical.choose_spec (actualEmbeddedEdgeSubpath q.1 _ _ (actualSegmentParameterOrder q))).2.2.2 t
  have actualSegmentStartPosition (q : zeroEdgeIndex × Fin 3) :
      zeroVertexPosition (actualSegmentStartVertex q) =
        cylinderZeroEdge q.1 (actualSegmentStartParameter q) := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> simp [actualSegmentStartVertex,actualSegmentStartParameter,
      zeroVertexPosition,zeroLeftVertex,zeroEndpointLeft] <;> rfl
  have actualSegmentEndPosition (q : zeroEdgeIndex × Fin 3) :
      zeroVertexPosition (actualSegmentEndVertex q) =
        cylinderZeroEdge q.1 (actualSegmentEndParameter q) := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> simp [actualSegmentEndVertex,actualSegmentEndParameter,
      zeroVertexPosition,zeroRightVertex,zeroEndpointRight] <;> rfl
  let actualPlanarVertexPosition (v : zeroVertex) : Schoenflies.Plane :=
    actualOuterCylinderSchoenflies (zeroVertexPosition v)
  have actualPlanarVertexPositionInjective : Function.Injective actualPlanarVertexPosition :=
    actualOuterCylinderSchoenflies_embedding.injective.comp zeroVertexPositionInjective
  let actualSegmentPlanarPath (q : zeroEdgeIndex × Fin 3) :
      Path (actualOuterCylinderSchoenflies (cylinderZeroEdge q.1 (actualSegmentStartParameter q)))
        (actualOuterCylinderSchoenflies (cylinderZeroEdge q.1 (actualSegmentEndParameter q))) :=
    (actualSegmentCylinderPath q).map actualOuterCylinderSchoenflies.continuous
  have actualSegmentPlanarPathEmbedding (q : zeroEdgeIndex × Fin 3) :
      Topology.IsEmbedding (actualSegmentPlanarPath q) :=
    actualOuterCylinderSchoenflies_embedding.comp (actualSegmentCylinderPathEmbedding q)
  have actualSegmentPlanarSource (q : zeroEdgeIndex × Fin 3) :
      actualSegmentPlanarPath q 0 = actualPlanarVertexPosition (actualSegmentStartVertex q) := by
    rw [Path.source]
    exact congrArg actualOuterCylinderSchoenflies (actualSegmentStartPosition q).symm
  have actualSegmentPlanarTarget (q : zeroEdgeIndex × Fin 3) :
      actualSegmentPlanarPath q 1 = actualPlanarVertexPosition (actualSegmentEndVertex q) := by
    rw [Path.target]
    exact congrArg actualOuterCylinderSchoenflies (actualSegmentEndPosition q).symm
  let actualPlanarGraph : Graph Schoenflies.Plane (zeroEdgeIndex × Fin 3) := {
    vertexSet := Set.range actualPlanarVertexPosition
    edgeSet := Set.univ
    IsLink := fun q x y =>
      (x = actualSegmentPlanarPath q 0 ∧ y = actualSegmentPlanarPath q 1) ∨
      (x = actualSegmentPlanarPath q 1 ∧ y = actualSegmentPlanarPath q 0)
    isLink_symm := by
      intro q hq
      constructor
      intro x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inr ⟨hy,hx⟩
      · exact Or.inl ⟨hy,hx⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro q x y z w hx hz
      rcases hx with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
        rcases hz with ⟨hz,hw⟩ | ⟨hz,hw⟩
      · exact Or.inl (hx.trans hz.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inl (hx.trans hz.symm)
    edge_mem_iff_exists_isLink := by
      intro q
      constructor
      · intro hq
        exact ⟨actualSegmentPlanarPath q 0,actualSegmentPlanarPath q 1,Or.inl ⟨rfl,rfl⟩⟩
      · intro hq
        exact Set.mem_univ _
    left_mem_of_isLink := by
      intro q x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans hx.symm⟩
      · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans hx.symm⟩ }
  let actualPlanarDrawing (q : zeroEdgeIndex × Fin 3) : ℝ → Schoenflies.Plane :=
    (actualSegmentPlanarPath q).extend
  have actualPlanarEdgeParameter (q : zeroEdgeIndex × Fin 3) :
      ContinuousOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      actualPlanarGraph.IsLink q (actualPlanarDrawing q 0) (actualPlanarDrawing q 1) := by
    refine ⟨(actualSegmentPlanarPath q).continuous_extend.continuousOn,?_,?_⟩
    · intro s hs t ht he
      change (actualSegmentPlanarPath q).extend s = (actualSegmentPlanarPath q).extend t at he
      rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
      exact congrArg Subtype.val ((actualSegmentPlanarPathEmbedding q).injective he)
    · change (actualPlanarDrawing q 0 = actualSegmentPlanarPath q 0 ∧
        actualPlanarDrawing q 1 = actualSegmentPlanarPath q 1) ∨ _
      exact Or.inl ⟨by simp [actualPlanarDrawing],by simp [actualPlanarDrawing]⟩
  have actualSegmentStartValue (q : zeroEdgeIndex × Fin 3) :
      (actualSegmentStartParameter q).val = actualThreeSegmentStart q.2 := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> norm_num [actualSegmentStartParameter,privateParameter,actualThreeSegmentStart]
  have actualSegmentEndValue (q : zeroEdgeIndex × Fin 3) :
      (actualSegmentEndParameter q).val = actualThreeSegmentEnd q.2 := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> norm_num [actualSegmentEndParameter,privateParameter,actualThreeSegmentEnd]
  have actualSegmentBreakpointIsEndpoint (q : zeroEdgeIndex × Fin 3) (u : Interval)
      (hu : u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hb : u = 0 ∨ u = privateParameter 0 ∨ u = privateParameter 1 ∨ u = 1) :
      u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q := by
    have hreal : u.val ∈ Set.Icc (actualThreeSegmentStart q.2) (actualThreeSegmentEnd q.2) := by
      rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
      exact hu
    have hbReal : u.val = 0 ∨ u.val = 1/3 ∨ u.val = 2/3 ∨ u.val = 1 := by
      rcases hb with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by norm_num [privateParameter]))
      · exact Or.inr (Or.inr (Or.inl (by norm_num [privateParameter])))
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases actualThreeSegment_breakpoint_is_endpoint q.2 u.val hreal hbReal with h | h
    · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
    · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
  have actualDistinctSegmentParameterIntersection (q r : zeroEdgeIndex × Fin 3)
      (hj : q.2 ≠ r.2) (u : Interval)
      (hu : u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hv : u ∈ Set.Icc (actualSegmentStartParameter r) (actualSegmentEndParameter r)) :
      (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
        (u = actualSegmentStartParameter r ∨ u = actualSegmentEndParameter r) := by
    have huReal : u.val ∈ Set.Icc (actualThreeSegmentStart q.2) (actualThreeSegmentEnd q.2) := by
      rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
      exact hu
    have hvReal : u.val ∈ Set.Icc (actualThreeSegmentStart r.2) (actualThreeSegmentEnd r.2) := by
      rw [←actualSegmentStartValue r,←actualSegmentEndValue r]
      exact hv
    obtain ⟨hq,hr⟩ := actualThreeSegment_distinct_intersection q.2 r.2 hj u.val huReal hvReal
    constructor
    · rcases hq with h | h
      · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
      · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
    · rcases hr with h | h
      · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue r).symm))
      · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue r).symm))
  have actualPlanarEdgeArcParameter (q : zeroEdgeIndex × Fin 3) (z : Schoenflies.Plane)
      (hz : z ∈ Graph.edgeArc actualPlanarDrawing q) :
      ∃ u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q),
        actualOuterCylinderSchoenflies (cylinderZeroEdge q.1 u) = z := by
    obtain ⟨s,hs,he⟩ := hz
    change (actualSegmentPlanarPath q).extend s = z at he
    rw [Path.extend_apply _ hs] at he
    obtain ⟨u,hu,hup⟩ := actualSegmentCylinderPathRange q ⟨⟨s,hs⟩,rfl⟩
    exact ⟨u,hu,(congrArg actualOuterCylinderSchoenflies hup).trans he⟩
  have actualSegmentEndpointPlanarPosition (q : zeroEdgeIndex × Fin 3) (u : Interval)
      (hu : u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) :
      actualOuterCylinderSchoenflies (cylinderZeroEdge q.1 u) = actualSegmentPlanarPath q 0 ∨
        actualOuterCylinderSchoenflies (cylinderZeroEdge q.1 u) = actualSegmentPlanarPath q 1 := by
    rcases hu with rfl | rfl
    · exact Or.inl (Path.source _).symm
    · exact Or.inr (Path.target _).symm
  have actualSegmentVertexOnArcIsEndpoint (q : zeroEdgeIndex × Fin 3) (v : zeroVertex)
      (hv : actualPlanarVertexPosition v ∈ Graph.edgeArc actualPlanarDrawing q) :
      actualPlanarVertexPosition v = actualSegmentPlanarPath q 0 ∨
        actualPlanarVertexPosition v = actualSegmentPlanarPath q 1 := by
    obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter q _ hv
    have hpoint : zeroVertexPosition v = cylinderZeroEdge q.1 u :=
      (actualOuterCylinderSchoenflies_embedding.injective he).symm
    have hb := actualZeroVertexOnEdgeBreakpoint v q.1 u hpoint
    have hend := actualSegmentBreakpointIsEndpoint q u hu hb
    rw [←he]
    exact actualSegmentEndpointPlanarPosition q u hend
  have actualDistinctSegmentArcIntersection (q r : zeroEdgeIndex × Fin 3)
      (hqr : q ≠ r) (z : Schoenflies.Plane)
      (hq : z ∈ Graph.edgeArc actualPlanarDrawing q)
      (hr : z ∈ Graph.edgeArc actualPlanarDrawing r) :
      (z = actualSegmentPlanarPath q 0 ∨ z = actualSegmentPlanarPath q 1) ∧
        (z = actualSegmentPlanarPath r 0 ∨ z = actualSegmentPlanarPath r 1) := by
    obtain ⟨u,hu,hup⟩ := actualPlanarEdgeArcParameter q z hq
    obtain ⟨v,hv,hvp⟩ := actualPlanarEdgeArcParameter r z hr
    have he : cylinderZeroEdge q.1 u = cylinderZeroEdge r.1 v :=
      actualOuterCylinderSchoenflies_embedding.injective (hup.trans hvp.symm)
    have hends : (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
        (v = actualSegmentStartParameter r ∨ v = actualSegmentEndParameter r) := by
      rcases actualZeroEdgeCollisionClassification q.1 r.1 u v he with ⟨hedge,huv⟩ | ⟨hu0,hv0⟩
      · have hj : q.2 ≠ r.2 := by
          intro hj
          exact hqr (Prod.ext hedge hj)
        subst v
        exact actualDistinctSegmentParameterIntersection q r hj u hu hv
      · have hbu : u = 0 ∨ u = privateParameter 0 ∨ u = privateParameter 1 ∨ u = 1 := by
          rcases hu0 with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inr (Or.inr h1))
        have hbv : v = 0 ∨ v = privateParameter 0 ∨ v = privateParameter 1 ∨ v = 1 := by
          rcases hv0 with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inr (Or.inr h1))
        exact ⟨actualSegmentBreakpointIsEndpoint q u hu hbu,
          actualSegmentBreakpointIsEndpoint r v hv hbv⟩
    constructor
    · rw [←hup]
      exact actualSegmentEndpointPlanarPosition q u hends.1
    · rw [←hvp]
      exact actualSegmentEndpointPlanarPosition r v hends.2
  have actualPlanarDrawingIsDrawing : Graph.IsDrawing actualPlanarGraph actualPlanarDrawing := by
    refine ⟨?_,?_,?_⟩
    · intro q hq
      exact actualPlanarEdgeParameter q
    · intro q x y z hlink hz hze
      obtain ⟨v,rfl⟩ := hz
      have hend := actualSegmentVertexOnArcIsEndpoint q v hze
      change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨
        (_ = actualSegmentPlanarPath q 1 ∧ _ = actualSegmentPlanarPath q 0) at hlink
      rcases hlink with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hend
      · exact hend.elim Or.inr Or.inl
    · intro q r hq hr hqr z hze hzr
      obtain ⟨hqend,hrend⟩ := actualDistinctSegmentArcIntersection q r hqr z hze hzr
      have hver : z ∈ actualPlanarGraph.vertexSet := by
        rcases hqend with h0 | h1
        · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans h0.symm⟩
        · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans h1.symm⟩
      refine ⟨hver,?_,?_⟩
      · rcases hqend with h0 | h1
        · exact ⟨actualSegmentPlanarPath q 1,Or.inl ⟨h0,rfl⟩⟩
        · exact ⟨actualSegmentPlanarPath q 0,Or.inr ⟨h1,rfl⟩⟩
      · rcases hrend with h0 | h1
        · exact ⟨actualSegmentPlanarPath r 1,Or.inl ⟨h0,rfl⟩⟩
        · exact ⟨actualSegmentPlanarPath r 0,Or.inr ⟨h1,rfl⟩⟩
  have actualCylinderZeroEdgeInteriorTimePositive (e : zeroEdgeIndex) (u : Interval)
      (hu : u ∈ Set.Ioo (0 : Interval) 1) : 0 < (cylinderZeroEdge e u).1 := by
    have hi := (globalZeroEdgeInterior e u hu).1.1
    change (0 : ℝ) < (globalZeroEdge e u).1.val
    exact lt_of_le_of_lt (phaseGrid e.1.1.val.1.castSucc).property.1 hi
  have actualPlanarEdgeArcBottomIsEndpoint (q : zeroEdgeIndex × Fin 3) (z : Schoenflies.Plane)
      (hz : z ∈ Graph.edgeArc actualPlanarDrawing q)
      (hb : z ∈ Set.range actualCylinderBottomCircle) :
      z = actualSegmentPlanarPath q 0 ∨ z = actualSegmentPlanarPath q 1 := by
    obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter q z hz
    obtain ⟨w,hw⟩ := hb
    have hnorm : ‖z‖ = 2 := by
      rw [←hw]
      change ‖actualOuterCylinderSchoenflies (0,w)‖ = 2
      rw [actualOuterCylinderSchoenflies_norm]
      norm_num
    have htime : (cylinderZeroEdge q.1 u).1 = 0 := by
      apply Subtype.ext
      have hn := actualOuterCylinderSchoenflies_norm (cylinderZeroEdge q.1 u)
      rw [he,hnorm] at hn
      change (cylinderZeroEdge q.1 u).1.val = 0
      linarith only [hn]
    have huOld : u = 0 ∨ u = 1 := by
      by_contra hn
      have huI : u ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · exact lt_of_le_of_ne u.property.1 (by intro h; exact hn (Or.inl h.symm))
        · exact lt_of_le_of_ne u.property.2 (by intro h; exact hn (Or.inr h))
      have hpos := actualCylinderZeroEdgeInteriorTimePositive q.1 u huI
      rw [htime] at hpos
      exact lt_irrefl _ hpos
    have huBreak : u = 0 ∨ u = privateParameter 0 ∨ u = privateParameter 1 ∨ u = 1 := by
      rcases huOld with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (Or.inr (Or.inr h1))
    rw [←he]
    exact actualSegmentEndpointPlanarPosition q u
      (actualSegmentBreakpointIsEndpoint q u hu huBreak)
  have actualPlanarEdgeArcBottomIsGraphVertex (q : zeroEdgeIndex × Fin 3) (z : Schoenflies.Plane)
      (hz : z ∈ Graph.edgeArc actualPlanarDrawing q)
      (hb : z ∈ Set.range actualCylinderBottomCircle) : z ∈ actualPlanarGraph.vertexSet := by
    rcases actualPlanarEdgeArcBottomIsEndpoint q z hz hb with h0 | h1
    · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans h0.symm⟩
    · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans h1.symm⟩
  have actualAnyInteriorRootFaceIncidenceEven (k : activeCells) (i : Fin 4)
      (u : Interval) (hroot : actualFaceHeight (k,i) u = 0)
      (p : zeroEndpointSet) (hnot0 : p.val.1 ≠ 0) (hnot1 : p.val.1 ≠ 1)
      (hp : p.val = cylinderProjection (cellToGlobal k.val (squareCoordinates
        ⟨(boundaryFace i u).val,(boundaryFace i u).property.le⟩))) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    fin_cases i
    · change actualFaceHeight (k,0) u = 0 at hroot
      change p.val = cylinderProjection (cellToGlobal k.val (squareCoordinates
        ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩)) at hp
      have hcoord : squareCoordinates
          ⟨(boundaryFace 0 u).val,(boundaryFace 0 u).property.le⟩ = (u,0) := by
        apply Prod.ext <;> apply Subtype.ext
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      rw [hcoord] at hp
      by_cases hk : k.val.2 = 0
      · obtain ⟨l,htime,hlphase,hrootl⟩ := actualRootFirstPhaseSeamNeighborActive k hk u hroot
        exact actualSeamRootCylinderIncidenceEven k l htime hk hlphase u hroot p hp
      · obtain ⟨l,hphase,htime,hrootl⟩ := actualRootLowerPhaseNeighborActive k hk u hroot
        have he := actualPhaseGridNeighborCellPoint l.val k.val htime hphase u
        have hp' : p.val = cylinderProjection (cellToGlobal l.val (u,1)) :=
          hp.trans (congrArg cylinderProjection he).symm
        exact actualPhaseRootCylinderIncidenceEven l k htime hphase u hrootl p hp'
    · change actualFaceHeight (k,1) u = 0 at hroot
      change p.val = cylinderProjection (cellToGlobal k.val (squareCoordinates
        ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩)) at hp
      have hcoord : squareCoordinates
          ⟨(boundaryFace 1 u).val,(boundaryFace 1 u).property.le⟩ = (1,u) := by
        apply Prod.ext <;> apply Subtype.ext
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      rw [hcoord] at hp
      by_cases hk : k.val.1 = Fin.last n
      · have htime : (cellToGlobal k.val (1,u)).1 = 1 := by
          apply Subtype.ext
          change (1-(1 : ℝ))*(phaseGrid k.val.1.castSucc).val+
            (1 : ℝ)*(phaseGrid k.val.1.succ).val = 1
          rw [hk,lastSucc]
          simp [phaseGrid]
        have hpt := congrArg (fun z : Interval × Circle => z.1) hp
        change p.val.1 = (cellToGlobal k.val (1,u)).1 at hpt
        exact False.elim (hnot1 (hpt.trans htime))
      · obtain ⟨l,htime,hphase,hrootl⟩ := actualRootRightTimeNeighborActive k hk u hroot
        exact actualTimeRootCylinderIncidenceEven k l htime hphase u hroot p hp
    · change actualFaceHeight (k,2) u = 0 at hroot
      change p.val = cylinderProjection (cellToGlobal k.val (squareCoordinates
        ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩)) at hp
      have hcoord : squareCoordinates
          ⟨(boundaryFace 2 u).val,(boundaryFace 2 u).property.le⟩ = (u,1) := by
        apply Prod.ext <;> apply Subtype.ext
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      rw [hcoord] at hp
      by_cases hk : k.val.2 = Fin.last n
      · obtain ⟨l,htime,hlphase,hrootl⟩ := actualRootLastPhaseSeamNeighborActive k hk u hroot
        have he := actualSeamCellPoint l k htime.symm hlphase hk u
        have hp' : p.val = cylinderProjection (cellToGlobal l.val (u,0)) := hp.trans he.symm
        exact actualSeamRootCylinderIncidenceEven l k htime.symm hlphase hk u hrootl p hp'
      · obtain ⟨l,hphase,htime,hrootl⟩ := actualRootUpperPhaseNeighborActive k hk u hroot
        exact actualPhaseRootCylinderIncidenceEven k l htime hphase u hroot p hp
    · change actualFaceHeight (k,3) u = 0 at hroot
      change p.val = cylinderProjection (cellToGlobal k.val (squareCoordinates
        ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩)) at hp
      have hcoord : squareCoordinates
          ⟨(boundaryFace 3 u).val,(boundaryFace 3 u).property.le⟩ = (0,u) := by
        apply Prod.ext <;> apply Subtype.ext
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
        · simp [squareCoordinates,boundaryFace,boundaryFaceRaw] <;> ring
      rw [hcoord] at hp
      by_cases hk : k.val.1 = 0
      · have htime : (cellToGlobal k.val (0,u)).1 = 0 := by
          apply Subtype.ext
          change (1-(0 : ℝ))*(phaseGrid k.val.1.castSucc).val+
            (0 : ℝ)*(phaseGrid k.val.1.succ).val = 0
          have hi : k.val.1.castSucc = (0 : Fin (n+2)) := by
            rw [hk]
            rfl
          rw [hi]
          simp [phaseGrid]
        have hpt := congrArg (fun z : Interval × Circle => z.1) hp
        change p.val.1 = (cellToGlobal k.val (0,u)).1 at hpt
        exact False.elim (hnot0 (hpt.trans htime))
      · obtain ⟨l,htime,hphase,hrootl⟩ := actualRootLeftTimeNeighborActive k hk u hroot
        have he := actualTimeGridNeighborCellPoint l.val k.val htime hphase u
        have hp' : p.val = cylinderProjection (cellToGlobal l.val (1,u)) :=
          hp.trans (congrArg cylinderProjection he).symm
        exact actualTimeRootCylinderIncidenceEven l k htime hphase u hrootl p hp'
  have actualBottomEventCellRepresentation (t : Interval)
      (hB : regularizedTrace (0,t) ∈ b.val.image) :
      ∃ k : activeCells, k.val.1 = 0 ∧
        ∃ u : Interval, u ∈ Set.Ioo (0 : Interval) 1 ∧ actualFaceHeight (k,3) u = 0 ∧
          cellToGlobal k.val (0,u) = (0,t) := by
    obtain ⟨j,hj0,hj1⟩ := phaseGridCovers t
    let r := localCoordinate j t
    have hcell : (0,t) ∈ cellDomain (0,j) := by
      refine ⟨?_,(phaseGrid (Fin.succ 0)).property.1,hj0,hj1⟩
      change phaseGrid (0 : Fin (n+2)) ≤ 0
      simp [phaseGrid]
    have hlocal : regularizedCells (0,j) (0,r) ∈ b.val.image := by
      rw [regularizedOnCells (0,j) (0,t) hcell] at hB
      change regularizedCells (0,j) (localCoordinate 0 0,r) ∈ b.val.image at hB
      rwa [coordinateZero] at hB
    have hactive : ¬ Disjoint (chartDomain (chart (0,j))) b.val.image := by
      intro hd
      exact Set.disjoint_left.mp hd (regularizedCellRange (0,j) (0,r)) hlocal
    let k : activeCells := ⟨(0,j),hactive⟩
    have hcoords : squareCoordinates
        ⟨(boundaryFace 3 r).val,(boundaryFace 3 r).property.le⟩ = (0,r) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
        <;> ring
    have hroot : actualFaceHeight (k,3) r = 0 := by
      have hn := (activeCellAxis k _ (regularizedCellRange k.val (0,r))).mp hlocal
      have hf := actualCellBoundaryFormula k.val (boundaryFace 3 r)
      rw [hcoords] at hf
      rw [hf] at hn
      change (regularizedCellLoops k.val (boundaryFace 3 r)).val.1 /
        (cellCenter k.val).val.1 = 0
      rw [hn]
      simp
    obtain ⟨i,hi,hi0,hi1⟩ := actualFaceZeroIsInternalMesh (k,3) r hroot
    have hrI : r ∈ Set.Ioo (0 : Interval) 1 :=
      hi ▸ actualInternalMeshNodeOpenParameter (k,3) i hi0 hi1
    have hparam : cellToGlobal (0,j) (0,r) = (0,t) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [cellToGlobal,phaseGrid]
      · exact localCoordinateAffine j t hj0 hj1
    exact ⟨k,rfl,r,hrI,hroot,hparam⟩
  have actualTopEventCellRepresentation (t : Interval)
      (hB : regularizedTrace (1,t) ∈ b.val.image) :
      ∃ k : activeCells, k.val.1 = Fin.last n ∧
        ∃ u : Interval, u ∈ Set.Ioo (0 : Interval) 1 ∧ actualFaceHeight (k,1) u = 0 ∧
          cellToGlobal k.val (1,u) = (1,t) := by
    obtain ⟨j,hj0,hj1⟩ := phaseGridCovers t
    let r := localCoordinate j t
    have hcell : (1,t) ∈ cellDomain (Fin.last n,j) := by
      refine ⟨(phaseGrid (Fin.last n).castSucc).property.2,?_,hj0,hj1⟩
      change (1 : Interval) ≤ phaseGrid (Fin.last n).succ
      simp [lastSucc,phaseGrid]
    have hlocal : regularizedCells (Fin.last n,j) (1,r) ∈ b.val.image := by
      rw [regularizedOnCells (Fin.last n,j) (1,t) hcell] at hB
      change regularizedCells (Fin.last n,j) (localCoordinate (Fin.last n) 1,r) ∈ b.val.image at hB
      rwa [coordinateOne] at hB
    have hactive : ¬ Disjoint (chartDomain (chart (Fin.last n,j))) b.val.image := by
      intro hd
      exact Set.disjoint_left.mp hd (regularizedCellRange (Fin.last n,j) (1,r)) hlocal
    let k : activeCells := ⟨(Fin.last n,j),hactive⟩
    have hcoords : squareCoordinates
        ⟨(boundaryFace 1 r).val,(boundaryFace 1 r).property.le⟩ = (1,r) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
      · simp [squareCoordinates,boundaryFace,boundaryFaceRaw]
        <;> ring
    have hroot : actualFaceHeight (k,1) r = 0 := by
      have hn := (activeCellAxis k _ (regularizedCellRange k.val (1,r))).mp hlocal
      have hf := actualCellBoundaryFormula k.val (boundaryFace 1 r)
      rw [hcoords] at hf
      rw [hf] at hn
      change (regularizedCellLoops k.val (boundaryFace 1 r)).val.1 /
        (cellCenter k.val).val.1 = 0
      rw [hn]
      simp
    obtain ⟨i,hi,hi0,hi1⟩ := actualFaceZeroIsInternalMesh (k,1) r hroot
    have hrI : r ∈ Set.Ioo (0 : Interval) 1 :=
      hi ▸ actualInternalMeshNodeOpenParameter (k,1) i hi0 hi1
    have hparam : cellToGlobal (Fin.last n,j) (1,r) = (1,t) := by
      apply Prod.ext <;> apply Subtype.ext
      · simp [cellToGlobal,lastSucc,phaseGrid]
      · exact localCoordinateAffine j t hj0 hj1
    exact ⟨k,rfl,r,hrI,hroot,hparam⟩
  have actualBottomEndpointIncidenceOne (p : zeroEndpointSet) (hpTime : p.val.1 = 0) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 1 := by
    obtain ⟨q,hq⟩ := cylinderProjectionSurjective p.val
    have hqtime : q.1 = 0 := (congrArg (fun z : Interval × Circle => z.1) hq).trans hpTime
    have hq' : q = (0,q.2) := Prod.ext hqtime rfl
    have htrace : cylinderTrace p.val = regularizedTrace (0,q.2) :=
      (congrArg cylinderTrace hq).symm.trans
        ((cylinderTraceOnSquare q).trans (congrArg regularizedTrace hq'))
    have hB : regularizedTrace (0,q.2) ∈ b.val.image := by
      rw [←htrace]
      exact zeroVertexOnComparison (Sum.inl p)
    obtain ⟨k,hk,u,hu,hroot,hparam⟩ := actualBottomEventCellRepresentation q.2 hB
    have hp : p.val = cylinderProjection (cellToGlobal k.val (0,u)) :=
      hq.symm.trans ((congrArg cylinderProjection hq').trans
        (congrArg cylinderProjection hparam).symm)
    exact actualBottomCylinderEndpointCountOne k hk u hu hroot p hp
  have actualTopEndpointIncidenceOne (p : zeroEndpointSet) (hpTime : p.val.1 = 1) :
      (leftIncidentEdges p).card + (rightIncidentEdges p).card = 1 := by
    obtain ⟨q,hq⟩ := cylinderProjectionSurjective p.val
    have hqtime : q.1 = 1 := (congrArg (fun z : Interval × Circle => z.1) hq).trans hpTime
    have hq' : q = (1,q.2) := Prod.ext hqtime rfl
    have htrace : cylinderTrace p.val = regularizedTrace (1,q.2) :=
      (congrArg cylinderTrace hq).symm.trans
        ((cylinderTraceOnSquare q).trans (congrArg regularizedTrace hq'))
    have hB : regularizedTrace (1,q.2) ∈ b.val.image := by
      rw [←htrace]
      exact zeroVertexOnComparison (Sum.inl p)
    obtain ⟨k,hk,u,hu,hroot,hparam⟩ := actualTopEventCellRepresentation q.2 hB
    have hp : p.val = cylinderProjection (cellToGlobal k.val (1,u)) :=
      hq.symm.trans ((congrArg cylinderProjection hq').trans
        (congrArg cylinderProjection hparam).symm)
    exact actualTopCylinderEndpointCountOne k hk u hu hroot p hp
  have actualRootSelectedSourceIncidenceEven (e : zeroEdgeIndex)
      (hroot : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.castSucc) = 0)
      (p : zeroEndpointSet) (hnot0 : p.val.1 ≠ 0) (hnot1 : p.val.1 ≠ 1)
      (hp : p.val = zeroEndpointLeft e) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    have hpoint := actualSourceRootEndpointFormula e hroot
    have hpFace : p.val = cylinderProjection (cellToGlobal e.1.1.val (squareCoordinates
        ⟨(boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.castSucc)).val,
          (boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.castSucc)).property.le⟩)) :=
      hp.trans (congrArg (fun z => cylinderProjection (cellToGlobal e.1.1.val z)) hpoint)
    exact actualAnyInteriorRootFaceIncidenceEven e.1.1 e.1.2 _ hroot p hnot0 hnot1 hpFace
  have actualRootSelectedTargetIncidenceEven (e : zeroEdgeIndex)
      (hroot : actualFaceHeight e.1 (activeFaceMesh e.1 e.2.val.succ) = 0)
      (p : zeroEndpointSet) (hnot0 : p.val.1 ≠ 0) (hnot1 : p.val.1 ≠ 1)
      (hp : p.val = zeroEndpointRight e) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    have hpoint := actualTargetRootEndpointFormula e hroot
    have hpFace : p.val = cylinderProjection (cellToGlobal e.1.1.val (squareCoordinates
        ⟨(boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.succ)).val,
          (boundaryFace e.1.2 (activeFaceMesh e.1 e.2.val.succ)).property.le⟩)) :=
      hp.trans (congrArg (fun z => cylinderProjection (cellToGlobal e.1.1.val z)) hpoint)
    exact actualAnyInteriorRootFaceIncidenceEven e.1.1 e.1.2 _ hroot p hnot0 hnot1 hpFace
  have actualInteriorEndpointIncidenceEven (p : zeroEndpointSet)
      (hnot0 : p.val.1 ≠ 0) (hnot1 : p.val.1 ≠ 1) :
      Even ((leftIncidentEdges p).card + (rightIncidentEdges p).card) := by
    rcases p.property with hleft | hright
    · obtain ⟨e,he⟩ := hleft
      rcases actualSourceEndpointDirectionCases e with hroot | hneg
      · exact actualRootSelectedSourceIncidenceEven e hroot p hnot0 hnot1 he.symm
      · rw [actualNegativeSelectedSourceCountTwo e hneg p he.symm]
        norm_num
    · obtain ⟨e,he⟩ := hright
      rcases actualTargetEndpointDirectionCases e with hroot | hneg
      · exact actualRootSelectedTargetIncidenceEven e hroot p hnot0 hnot1 he.symm
      · rw [actualNegativeSelectedTargetCountTwo e hneg p he.symm]
        norm_num
  have actualEndpointIncidenceOddIffOriginalBoundary (p : zeroEndpointSet) :
      Odd ((leftIncidentEdges p).card + (rightIncidentEdges p).card) ↔
        p.val.1 = 0 ∨ p.val.1 = 1 := by
    constructor
    · intro hodd
      by_contra hn
      have hnot0 : p.val.1 ≠ 0 := fun h => hn (Or.inl h)
      have hnot1 : p.val.1 ≠ 1 := fun h => hn (Or.inr h)
      exact (Nat.not_even_iff_odd.mpr hodd) (actualInteriorEndpointIncidenceEven p hnot0 hnot1)
    · rintro (h0 | h1)
      · rw [actualBottomEndpointIncidenceOne p h0]
        norm_num
      · rw [actualTopEndpointIncidenceOne p h1]
        norm_num
  have actualOldVertexBoundaryMembership (p : zeroEndpointSet) :
      (Sum.inl p ∈ zeroBottomVertices ↔ p.val.1 = 0) ∧
        (Sum.inl p ∈ zeroTopVertices ↔ p.val.1 = 1) := by
    constructor
    all_goals simp only [zeroBottomVertices,zeroTopVertices,Finset.mem_filter,
      Finset.mem_univ,true_and]
    all_goals constructor
    · rintro ⟨q,he,hq⟩
      have hpq : p = q := Sum.inl.inj he
      rwa [hpq]
    · intro hp
      exact ⟨p,rfl,hp⟩
    · rintro ⟨q,he,hq⟩
      have hpq : p = q := Sum.inl.inj he
      rwa [hpq]
    · intro hp
      exact ⟨p,rfl,hp⟩
  have actualGraphOddDegreeIffOriginalBoundary (v : zeroVertex) :
      Odd (actualZeroGraph.degree v) ↔ v ∈ zeroBottomVertices ∪ zeroTopVertices := by
    rcases v with p | ⟨e,j⟩
    · rw [zeroEndpointDegreeExact p,actualEndpointIncidenceOddIffOriginalBoundary p,
        Finset.mem_union,(actualOldVertexBoundaryMembership p).1,
        (actualOldVertexBoundaryMembership p).2]
    · fin_cases j
      · change Odd (actualZeroGraph.degree (Sum.inr (e,0))) ↔
          Sum.inr (e,0) ∈ zeroBottomVertices ∪ zeroTopVertices
        rw [(zeroSubdivisionDegrees e).1]
        simp [zeroBottomVertices,zeroTopVertices]
      · change Odd (actualZeroGraph.degree (Sum.inr (e,1))) ↔
          Sum.inr (e,1) ∈ zeroBottomVertices ∪ zeroTopVertices
        rw [(zeroSubdivisionDegrees e).2]
        simp [zeroBottomVertices,zeroTopVertices]
  have actualOriginalBoundaryVertexDegreeOne (v : zeroVertex)
      (hv : v ∈ zeroBottomVertices ∪ zeroTopVertices) : actualZeroGraph.degree v = 1 := by
    rcases v with p | ⟨e,j⟩
    · rw [Finset.mem_union,(actualOldVertexBoundaryMembership p).1,
        (actualOldVertexBoundaryMembership p).2] at hv
      rw [zeroEndpointDegreeExact p]
      rcases hv with h0 | h1
      · exact actualBottomEndpointIncidenceOne p h0
      · exact actualTopEndpointIncidenceOne p h1
    · simp [zeroBottomVertices,zeroTopVertices] at hv
  have actualReturningPathBoundarySupportOnlyEndpoints
      {v w : zeroVertex} (p : actualZeroGraph.Walk v w) (hp : p.IsPath)
      (r : zeroVertex) (hr : r ∈ p.support)
      (hboundary : r ∈ zeroBottomVertices ∪ zeroTopVertices) : r = v ∨ r = w :=
    actual_degree_one_path_support_is_endpoint actualZeroGraph p hp hr
      (by simpa only [←SimpleGraph.ncard_neighborSet] using
        actualOriginalBoundaryVertexDegreeOne r hboundary)
  have actualBottomCylinderEventSet (z : Circle) :
      (0,z) ∈ zeroEndpointSet ↔ cylinderTrace (0,z) ∈ b.val.image := by
    constructor
    · intro hz
      exact zeroVertexOnComparison (Sum.inl ⟨(0,z),hz⟩)
    · intro hz
      obtain ⟨q,hq⟩ := cylinderProjectionSurjective (0,z)
      have ht : q.1 = 0 := congrArg Prod.fst hq
      have hq' : q = (0,q.2) := Prod.ext ht rfl
      have hc : cylinderProjection (0,q.2) = (0,z) :=
        (congrArg cylinderProjection hq').symm.trans hq
      have hs : cylinderTrace (0,z) = regularizedTrace (0,q.2) :=
        (congrArg cylinderTrace hq).symm.trans
          ((cylinderTraceOnSquare q).trans (congrArg regularizedTrace hq'))
      have hzero : regularizedTrace (0,q.2) ∈ b.val.image := hs ▸ hz
      obtain ⟨e,he⟩ := globalBottomEventCoverage q.2 hzero
      rcases he with he | he
      · exact Or.inl ⟨e,by change cylinderProjection (globalZeroEdge e 0) = (0,z); rw [he]; exact hc⟩
      · exact Or.inr ⟨e,by change cylinderProjection (globalZeroEdge e 1) = (0,z); rw [he]; exact hc⟩
  have actualTopCylinderEventSet (z : Circle) :
      (1,z) ∈ zeroEndpointSet ↔ cylinderTrace (1,z) ∈ b.val.image := by
    constructor
    · intro hz
      exact zeroVertexOnComparison (Sum.inl ⟨(1,z),hz⟩)
    · intro hz
      obtain ⟨q,hq⟩ := cylinderProjectionSurjective (1,z)
      have ht : q.1 = 1 := congrArg Prod.fst hq
      have hq' : q = (1,q.2) := Prod.ext ht rfl
      have hc : cylinderProjection (1,q.2) = (1,z) :=
        (congrArg cylinderProjection hq').symm.trans hq
      have hs : cylinderTrace (1,z) = regularizedTrace (1,q.2) :=
        (congrArg cylinderTrace hq).symm.trans
          ((cylinderTraceOnSquare q).trans (congrArg regularizedTrace hq'))
      have hzero : regularizedTrace (1,q.2) ∈ b.val.image := hs ▸ hz
      obtain ⟨e,he⟩ := globalTopEventCoverage q.2 hzero
      rcases he with he | he
      · exact Or.inl ⟨e,by change cylinderProjection (globalZeroEdge e 0) = (1,z); rw [he]; exact hc⟩
      · exact Or.inr ⟨e,by change cylinderProjection (globalZeroEdge e 1) = (1,z); rw [he]; exact hc⟩
  have actualBottomGraphVertexCount : zeroBottomVertices.card =
      ((fun z : Circle => cylinderTrace (0,z)) ⁻¹' b.val.image).ncard := by
    let phase : zeroVertex → Circle := fun v => (zeroVertexPosition v).2
    have htime (v : zeroVertex) (hv : v ∈ zeroBottomVertices) :
        (zeroVertexPosition v).1 = 0 := by
      obtain ⟨p,rfl,hp⟩ := (Finset.mem_filter.mp hv).2
      exact hp
    have hbij : Set.BijOn phase (zeroBottomVertices : Set zeroVertex)
        ((fun z : Circle => cylinderTrace (0,z)) ⁻¹' b.val.image) := by
      refine ⟨?_,?_,?_⟩
      · intro v hv
        have hh := zeroVertexOnComparison v
        have he : zeroVertexPosition v = (0,phase v) := Prod.ext (htime v hv) rfl
        rwa [he] at hh
      · intro v hv w hw he
        apply zeroVertexPositionInjective
        exact Prod.ext ((htime v hv).trans (htime w hw).symm) he
      · intro z hz
        have hze : (0,z) ∈ zeroEndpointSet := (actualBottomCylinderEventSet z).mpr hz
        let p : zeroEndpointSet := ⟨(0,z),hze⟩
        refine ⟨Sum.inl p,?_,rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,rfl,rfl⟩
    simpa only [Set.ncard_coe_finset] using hbij.ncard_eq
  have actualTopGraphVertexCount : zeroTopVertices.card =
      ((fun z : Circle => cylinderTrace (1,z)) ⁻¹' b.val.image).ncard := by
    let phase : zeroVertex → Circle := fun v => (zeroVertexPosition v).2
    have htime (v : zeroVertex) (hv : v ∈ zeroTopVertices) :
        (zeroVertexPosition v).1 = 1 := by
      obtain ⟨p,rfl,hp⟩ := (Finset.mem_filter.mp hv).2
      exact hp
    have hbij : Set.BijOn phase (zeroTopVertices : Set zeroVertex)
        ((fun z : Circle => cylinderTrace (1,z)) ⁻¹' b.val.image) := by
      refine ⟨?_,?_,?_⟩
      · intro v hv
        have hh := zeroVertexOnComparison v
        have he : zeroVertexPosition v = (1,phase v) := Prod.ext (htime v hv) rfl
        rwa [he] at hh
      · intro v hv w hw he
        apply zeroVertexPositionInjective
        exact Prod.ext ((htime v hv).trans (htime w hw).symm) he
      · intro z hz
        have hze : (1,z) ∈ zeroEndpointSet := (actualTopCylinderEventSet z).mpr hz
        let p : zeroEndpointSet := ⟨(1,z),hze⟩
        refine ⟨Sum.inl p,?_,rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,rfl,rfl⟩
    simpa only [Set.ncard_coe_finset] using hbij.ncard_eq

  have circleBoundaryEventCount (c : Curve S) (htc : Transverse c b.val) :
      ∃ hf : ((fun z : Circle => c.map (z₀*z)) ⁻¹' b.val.image).Finite,
        hf.toFinset.card = htc.1.toFinset.card := by
    let γ : Circle → S := fun z => c.map (z₀*z)
    let E := γ ⁻¹' b.val.image
    have hinj : Function.Injective γ := fun z w he => mul_left_cancel (c.embedded.injective he)
    have hf : E.Finite := (htc.1.preimage hinj.injOn).subset (fun z hz => ⟨⟨z₀*z,rfl⟩,hz⟩)
    have hbij : Set.BijOn γ E (c.image ∩ b.val.image) := by
      refine ⟨?_,hinj.injOn,?_⟩
      · intro z hz
        exact ⟨⟨z₀*z,rfl⟩,hz⟩
      · intro x hx
        obtain ⟨w,hw⟩ := hx.1
        refine ⟨z₀⁻¹*w,?_,?_⟩
        · change c.map (z₀*(z₀⁻¹*w)) ∈ b.val.image
          simpa only [mul_inv_cancel_left,hw] using hx.2
        · change c.map (z₀*(z₀⁻¹*w)) = x
          simpa only [mul_inv_cancel_left] using hw
    refine ⟨hf,?_⟩
    rw [← Set.ncard_eq_toFinset_card _ hf,← Set.ncard_eq_toFinset_card _ htc.1]
    exact hbij.ncard_eq
  obtain ⟨cylinderInitialFinite,cylinderInitialCount⟩ := circleBoundaryEventCount a.val ht
  obtain ⟨cylinderFinalFinite,cylinderFinalCount⟩ := circleBoundaryEventCount endCurve htEnd
  have cylinderComparisonCountDecrease :
      ((fun z : Circle => cylinderTrace (1,z)) ⁻¹' b.val.image).ncard <
        ((fun z : Circle => cylinderTrace (0,z)) ⁻¹' b.val.image).ncard := by
    have h0 : (fun z : Circle => cylinderTrace (0,z)) = (fun z => a.val.map (z₀*z)) :=
      funext (fun z => (cylinderBoundaryOriginal z).1)
    have h1 : (fun z : Circle => cylinderTrace (1,z)) = (fun z => endCurve.map (z₀*z)) :=
      funext (fun z => (cylinderBoundaryOriginal z).2)
    rw [h0,h1,Set.ncard_eq_toFinset_card _ cylinderFinalFinite,
      Set.ncard_eq_toFinset_card _ cylinderInitialFinite,cylinderInitialCount,cylinderFinalCount]
    have hset : htEnd.1.toFinset = ht'.1.toFinset := by
      ext x; simp only [Set.Finite.mem_toFinset,Set.mem_inter_iff,hendImage]
    rw [hset]
    exact hless
  have actualGraphBoundaryCountDecrease : zeroTopVertices.card < zeroBottomVertices.card := by
    rw [actualTopGraphVertexCount,actualBottomGraphVertexCount]
    exact cylinderComparisonCountDecrease
  have actualReturningGraphPath :
      ∃ v ∈ zeroBottomVertices, ∃ w ∈ zeroBottomVertices, v ≠ w ∧
        ∃ walk : actualZeroGraph.Walk v w, walk.IsPath :=
    graphReturnsToBottom actualZeroGraph zeroBottomVertices zeroTopVertices
      actualGraphOddDegreeIffOriginalBoundary actualGraphBoundaryCountDecrease
  have actualPlanarSegmentLink (q : zeroEdgeIndex × Fin 3) :
      actualPlanarGraph.IsLink q
        (actualPlanarVertexPosition (actualSegmentStartVertex q))
        (actualPlanarVertexPosition (actualSegmentEndVertex q)) := by
    change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨ _
    exact Or.inl ⟨(actualSegmentPlanarSource q).symm,(actualSegmentPlanarTarget q).symm⟩
  have actualPlanarDirectedLink (v w : zeroVertex) (hv : zeroDirectedIncidence v w) :
      ∃ q, actualPlanarGraph.IsLink q (actualPlanarVertexPosition v)
        (actualPlanarVertexPosition w) := by
    obtain ⟨e,h | h | h⟩ := hv
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨(e,0),by simpa [actualSegmentStartVertex,actualSegmentEndVertex] using
        actualPlanarSegmentLink (e,0)⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨(e,1),by simpa [actualSegmentStartVertex,actualSegmentEndVertex] using
        actualPlanarSegmentLink (e,1)⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨(e,2),by simpa [actualSegmentStartVertex,actualSegmentEndVertex] using
        actualPlanarSegmentLink (e,2)⟩
  have actualPlanarAdjacentLink {v w : zeroVertex} (hv : actualZeroGraph.Adj v w) :
      ∃ q, actualPlanarGraph.IsLink q (actualPlanarVertexPosition v)
        (actualPlanarVertexPosition w) := by
    rcases hv.2 with hv | hv
    · exact actualPlanarDirectedLink v w hv
    · obtain ⟨q,hq⟩ := actualPlanarDirectedLink w v hv
      exact ⟨q,hq.symm⟩
  have actualPlanarLinkRecoversZeroGraphAdjacency {v w : zeroVertex}
      {q : zeroEdgeIndex × Fin 3}
      (hq : actualPlanarGraph.IsLink q (actualPlanarVertexPosition v) (actualPlanarVertexPosition w)) :
      actualZeroGraph.Adj v w := by
    have hAdjacent : actualZeroGraph.Adj (actualSegmentStartVertex q) (actualSegmentEndVertex q) := by
      rcases q with ⟨e,j⟩
      fin_cases j
      · simpa [actualSegmentStartVertex,actualSegmentEndVertex] using zeroGraphLeftAdj e
      · simpa [actualSegmentStartVertex,actualSegmentEndVertex] using zeroGraphMiddleAdj e
      · simpa [actualSegmentStartVertex,actualSegmentEndVertex] using zeroGraphRightAdj e
    change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨
      (_ = actualSegmentPlanarPath q 1 ∧ _ = actualSegmentPlanarPath q 0) at hq
    rw [actualSegmentPlanarSource,actualSegmentPlanarTarget] at hq
    rcases hq with ⟨hv,hw⟩ | ⟨hv,hw⟩
    · have hv' := actualPlanarVertexPositionInjective hv
      have hw' := actualPlanarVertexPositionInjective hw
      exact hv'.symm ▸ hw'.symm ▸ hAdjacent
    · have hv' := actualPlanarVertexPositionInjective hv
      have hw' := actualPlanarVertexPositionInjective hw
      exact hv'.symm ▸ hw'.symm ▸ hAdjacent.symm
  let actualClosedCapZeroGraph (D : Set Schoenflies.Plane) : SimpleGraph zeroVertex := {
    Adj := fun v w => actualZeroGraph.Adj v w ∧
      ∃ q : zeroEdgeIndex × Fin 3, actualPlanarGraph.IsLink q
        (actualPlanarVertexPosition v) (actualPlanarVertexPosition w) ∧
        Graph.edgeArc actualPlanarDrawing q ⊆ D
    symm := ⟨by
      intro v w hvw
      obtain ⟨hvw,q,hq,hD⟩ := hvw
      exact ⟨hvw.symm,q,hq.symm,hD⟩⟩
    loopless := by
      refine ⟨?_⟩
      intro v hv
      exact actualZeroGraph.loopless.irrefl v hv.1 }
  have actualClosedCapGraph_le (D : Set Schoenflies.Plane) :
      actualClosedCapZeroGraph D ≤ actualZeroGraph := fun v w h => h.1
  have actualClosedCapGraphOutsideDegreeZero (D : Set Schoenflies.Plane) (v : zeroVertex)
      (hv : actualPlanarVertexPosition v ∉ D) : (actualClosedCapZeroGraph D).degree v = 0 := by
    apply (SimpleGraph.degree_eq_zero (actualClosedCapZeroGraph D) v).mpr
    intro w hw
    obtain ⟨hvw,q,hq,hD⟩ := hw
    exact hv (hD (actualPlanarDrawingIsDrawing.edge_isArcBetween hq).left_mem)
  have actualClosedCapGraphDegreeAtMostOriginal (D : Set Schoenflies.Plane) (v : zeroVertex) :
      (actualClosedCapZeroGraph D).degree v ≤ actualZeroGraph.degree v :=
    by simpa only [←SimpleGraph.ncard_neighborSet] using
      (SimpleGraph.degree_le_of_le (v := v) (actualClosedCapGraph_le D))
  have actualClosedCapGraphBoundaryDegreeOne (D : Set Schoenflies.Plane) (v w : zeroVertex)
      (hv : v ∈ zeroBottomVertices ∪ zeroTopVertices)
      (hvw : (actualClosedCapZeroGraph D).Adj v w) : (actualClosedCapZeroGraph D).degree v = 1 := by
    have hle := actualClosedCapGraphDegreeAtMostOriginal D v
    have hpos := hvw.degree_pos_left
    have hone := actualOriginalBoundaryVertexDegreeOne v hv
    simp only [←SimpleGraph.ncard_neighborSet] at hle hpos hone ⊢
    omega
  have actualClosedCapGraphInteriorHasAllOriginalNeighbors
      (A : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3))
      (hA : A ⊆ Set.range actualCylinderBottomCircle)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualPlanarDrawing W))
      (v w : zeroVertex) (hv : actualPlanarVertexPosition v ∈
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))
      (hvw : actualZeroGraph.Adj v w) :
      (actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).Adj v w := by
    obtain ⟨q,hq⟩ := actualPlanarAdjacentLink hvw
    have hQ := actualPlanarDrawingIsDrawing.edge_isArcBetween hq
    have hqNotW : q ∉ W := by
      intro hqW
      have hp : actualPlanarVertexPosition v ∈ Graph.edgesCover actualPlanarDrawing W :=
        Graph.mem_edgesCover hqW hQ.left_mem
      exact Schoenflies.inside_subset_compl hv (Or.inr hp)
    have endpointOfQ (x : Schoenflies.Plane)
        (hx : x = actualSegmentPlanarPath q 0 ∨ x = actualSegmentPlanarPath q 1) :
        x = actualPlanarVertexPosition v ∨ x = actualPlanarVertexPosition w := by
      change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨
        (_ = actualSegmentPlanarPath q 1 ∧ _ = actualSegmentPlanarPath q 0) at hq
      rcases hq with ⟨hv0,hw1⟩ | ⟨hv1,hw0⟩
      · rcases hx with hx0 | hx1
        · exact Or.inl (hx0.trans hv0.symm)
        · exact Or.inr (hx1.trans hw1.symm)
      · rcases hx with hx0 | hx1
        · exact Or.inr (hx0.trans hw0.symm)
        · exact Or.inl (hx1.trans hv1.symm)
    have hdisjoint : Disjoint (Graph.edgeArc actualPlanarDrawing q \
        {actualPlanarVertexPosition v,actualPlanarVertexPosition w})
        (A ∪ Graph.edgesCover actualPlanarDrawing W) := by
      rw [Set.disjoint_left]
      intro x hxQ hxJ
      have hnotEnds : ¬ (x = actualPlanarVertexPosition v ∨ x = actualPlanarVertexPosition w) := by
        simpa using hxQ.2
      rcases hxJ with hxA | hxP
      · exact hnotEnds (endpointOfQ x (actualPlanarEdgeArcBottomIsEndpoint q x hxQ.1 (hA hxA)))
      · obtain ⟨r,hrW,hxr⟩ := Graph.mem_edgesCover_iff.mp hxP
        have hqr : q ≠ r := fun h => hqNotW (h.symm ▸ hrW)
        have hxVertex := actualPlanarDrawingIsDrawing.edge_inter (Set.mem_univ q)
          (Set.mem_univ r) hqr hxQ.1 hxr
        exact hnotEnds (hxVertex.2.1.eq_or_eq_of_isLink hq)
    have hQcap := actual_arc_closed_cap_containment_of_endpoint_inside hJ hQ hdisjoint hv
    exact ⟨hvw,q,hq,hQcap⟩
  have actualClosedCapGraphInteriorDegreeEqualsOriginal
      (A : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3))
      (hA : A ⊆ Set.range actualCylinderBottomCircle)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualPlanarDrawing W))
      (v : zeroVertex) (hv : actualPlanarVertexPosition v ∈
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) :
      (actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).degree v =
          actualZeroGraph.degree v := by
    rw [←SimpleGraph.ncard_neighborSet,←SimpleGraph.ncard_neighborSet]
    congr 1
    ext w
    constructor
    · exact fun h => h.1
    · exact actualClosedCapGraphInteriorHasAllOriginalNeighbors A W hA hJ v w hv
  have actualOriginalBoundaryVertexTime (v : zeroVertex)
      (hv : v ∈ zeroBottomVertices ∪ zeroTopVertices) :
      (zeroVertexPosition v).1 = 0 ∨ (zeroVertexPosition v).1 = 1 := by
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hvu,p,rfl,hp⟩ := Finset.mem_filter.mp hv
      exact Or.inl hp
    · obtain ⟨hvu,p,rfl,hp⟩ := Finset.mem_filter.mp hv
      exact Or.inr hp
  have actualClosedCapGraphInteriorDegreeEven
      (A : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3))
      (hA : A ⊆ Set.range actualCylinderBottomCircle)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualPlanarDrawing W))
      (hBound : ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) ⊆
          Set.range actualOuterCylinderSchoenflies)
      (v : zeroVertex) (hv : actualPlanarVertexPosition v ∈
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) :
      Even ((actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).degree v) := by
    rw [actualClosedCapGraphInteriorDegreeEqualsOriginal A W hA hJ v hv]
    by_contra hn
    have hOdd : Odd (actualZeroGraph.degree v) := Nat.not_even_iff_odd.mp hn
    have hBoundary := (actualGraphOddDegreeIffOriginalBoundary v).mp hOdd
    have hAnnBounds : ∀ z ∈ (A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W),
        1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := by
      intro z hz
      have hzr := hBound hz
      rw [actualOuterCylinderSchoenflies_range] at hzr
      exact hzr
    have hStrict := actual_annular_jordan_cap_interior_strict_bounds hJ hAnnBounds hv
    have hNorm := actualOuterCylinderSchoenflies_norm (zeroVertexPosition v)
    change ‖actualPlanarVertexPosition v‖ = 2 - (zeroVertexPosition v).1.val at hNorm
    rcases actualOriginalBoundaryVertexTime v hBoundary with h0 | h1
    · rw [h0] at hNorm
      norm_num at hNorm
      linarith only [hNorm,hStrict.2]
    · rw [h1] at hNorm
      norm_num at hNorm
      linarith only [hNorm,hStrict.1]
  have actualClosedCapGraphOddVerticesOnBoundary
      (A : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3))
      (hA : A ⊆ Set.range actualCylinderBottomCircle)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualPlanarDrawing W))
      (hBound : ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) ⊆
          Set.range actualOuterCylinderSchoenflies)
      (v : zeroVertex)
      (hOdd : Odd ((actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).degree v)) :
      actualPlanarVertexPosition v ∈ A ∪ Graph.edgesCover actualPlanarDrawing W := by
    by_contra hnot
    by_cases hin : actualPlanarVertexPosition v ∈ Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)
    · exact (Nat.not_even_iff_odd.mpr hOdd)
        (actualClosedCapGraphInteriorDegreeEven A W hA hJ hBound v hin)
    · have hout : actualPlanarVertexPosition v ∉ (A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
          Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W) := by
        intro h
        exact h.elim hnot hin
      rw [actualClosedCapGraphOutsideDegreeZero _ v hout] at hOdd
      norm_num at hOdd
  have actualClosedCapGraphExtraBoundaryHasOriginalNeighbor
      (A : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3))
      (a b : zeroVertex) (B : Set Schoenflies.Plane)
      (hCut : Schoenflies.IsCutPair (Set.range actualCylinderBottomCircle)
        (actualPlanarVertexPosition a) (actualPlanarVertexPosition b) A B)
      (hP : Schoenflies.IsArcBetween (Graph.edgesCover actualPlanarDrawing W)
        (actualPlanarVertexPosition a) (actualPlanarVertexPosition b))
      (hPi : Graph.edgesCover actualPlanarDrawing W \ 
        {actualPlanarVertexPosition a,actualPlanarVertexPosition b} ⊆
        Schoenflies.inside (Set.range actualCylinderBottomCircle))
      (v w : zeroVertex) (hv : actualPlanarVertexPosition v ∈ A)
      (hne : actualPlanarVertexPosition v ∉
        ({actualPlanarVertexPosition a,actualPlanarVertexPosition b} : Set Schoenflies.Plane))
      (hvw : actualZeroGraph.Adj v w) :
      (actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).Adj v w := by
    obtain ⟨q,hq⟩ := actualPlanarAdjacentLink hvw
    have hQ := actualPlanarDrawingIsDrawing.edge_isArcBetween hq
    have hqNotW : q ∉ W := by
      intro hqW
      have hp : actualPlanarVertexPosition v ∈ Graph.edgesCover actualPlanarDrawing W :=
        Graph.mem_edgesCover hqW hQ.left_mem
      exact Schoenflies.inside_subset_compl (hPi ⟨hp,hne⟩) (hCut.fst_subset hv)
    have endpointOfQ (x : Schoenflies.Plane)
        (hx : x = actualSegmentPlanarPath q 0 ∨ x = actualSegmentPlanarPath q 1) :
        x = actualPlanarVertexPosition v ∨ x = actualPlanarVertexPosition w := by
      change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨
        (_ = actualSegmentPlanarPath q 1 ∧ _ = actualSegmentPlanarPath q 0) at hq
      rcases hq with ⟨hv0,hw1⟩ | ⟨hv1,hw0⟩
      · rcases hx with hx0 | hx1
        · exact Or.inl (hx0.trans hv0.symm)
        · exact Or.inr (hx1.trans hw1.symm)
      · rcases hx with hx0 | hx1
        · exact Or.inr (hx0.trans hw0.symm)
        · exact Or.inl (hx1.trans hv1.symm)
    have hQi : Graph.edgeArc actualPlanarDrawing q \ 
        {actualPlanarVertexPosition v,actualPlanarVertexPosition w} ⊆
        Schoenflies.inside (Set.range actualCylinderBottomCircle) := by
      rintro x ⟨hxQ,hnot⟩
      obtain ⟨t,ht,he⟩ := actualPlanarEdgeArcParameter q x hxQ
      have hNorm := actualOuterCylinderSchoenflies_norm (cylinderZeroEdge q.1 t)
      have hle : ‖x‖ ≤ 2 := by
        rw [←he,hNorm]
        exact sub_le_self _ (cylinderZeroEdge q.1 t).1.property.1
      have hneNorm : ‖x‖ ≠ 2 := by
        intro hn
        have hxB : x ∈ Set.range actualCylinderBottomCircle := by
          rw [actualCylinderBottomCircle_range,Metric.mem_sphere,dist_zero_right]
          exact hn
        exact hnot (by simpa using (endpointOfQ x
          (actualPlanarEdgeArcBottomIsEndpoint q x hxQ hxB)))
      rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right]
      exact lt_of_le_of_ne hle hneNorm
    have hdisjoint : Disjoint (Graph.edgeArc actualPlanarDrawing q \ 
        {actualPlanarVertexPosition v,actualPlanarVertexPosition w})
        (Graph.edgesCover actualPlanarDrawing W) := by
      rw [Set.disjoint_left]
      intro x hxQ hxP
      have hnotEnds : ¬ (x = actualPlanarVertexPosition v ∨ x = actualPlanarVertexPosition w) := by
        simpa using hxQ.2
      obtain ⟨r,hrW,hxr⟩ := Graph.mem_edgesCover_iff.mp hxP
      have hqr : q ≠ r := fun h => hqNotW (h.symm ▸ hrW)
      have hxVertex := actualPlanarDrawingIsDrawing.edge_inter (Set.mem_univ q)
        (Set.mem_univ r) hqr hxQ.1 hxr
      exact hnotEnds (hxVertex.2.1.eq_or_eq_of_isLink hq)
    have hQcap := actual_crosscut_boundary_arc_stays_in_selected_cap
      actualCylinderBottomCircle_jordan hP hCut hPi hQ hv hne hQi hdisjoint
    exact ⟨hvw,q,hq,hQcap⟩
  have actualClosedCapExtraBoundaryOddPartner
      (A B : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3))
      (a b r : zeroVertex)
      (hCut : Schoenflies.IsCutPair (Set.range actualCylinderBottomCircle)
        (actualPlanarVertexPosition a) (actualPlanarVertexPosition b) A B)
      (hP : Schoenflies.IsArcBetween (Graph.edgesCover actualPlanarDrawing W)
        (actualPlanarVertexPosition a) (actualPlanarVertexPosition b))
      (hPi : Graph.edgesCover actualPlanarDrawing W \ 
        {actualPlanarVertexPosition a,actualPlanarVertexPosition b} ⊆
        Schoenflies.inside (Set.range actualCylinderBottomCircle))
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualPlanarDrawing W))
      (hBound : ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) ⊆
          Set.range actualOuterCylinderSchoenflies)
      (hrBottom : r ∈ zeroBottomVertices) (hrA : actualPlanarVertexPosition r ∈ A)
      (hne : actualPlanarVertexPosition r ∉
        ({actualPlanarVertexPosition a,actualPlanarVertexPosition b} : Set Schoenflies.Plane)) :
      ∃ y, y ≠ r ∧ actualPlanarVertexPosition y ∈ A ∪ Graph.edgesCover actualPlanarDrawing W ∧
        ∃ p : (actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
          Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).Walk r y, p.IsPath := by
    let D := (A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
      Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)
    have hdegree : actualZeroGraph.degree r = 1 :=
      actualOriginalBoundaryVertexDegreeOne r (Finset.mem_union.mpr (Or.inl hrBottom))
    have hpos : 0 < actualZeroGraph.degree r := by omega
    have hnotIso := (SimpleGraph.degree_pos actualZeroGraph r).mp hpos
    obtain ⟨s,hs⟩ : ∃ s, actualZeroGraph.Adj r s := by
      simpa only [SimpleGraph.IsIsolated,not_forall,not_not] using hnotIso
    have hcapAdj := actualClosedCapGraphExtraBoundaryHasOriginalNeighbor
      A W a b B hCut hP hPi r s hrA hne hs
    have hcapDegree := actualClosedCapGraphBoundaryDegreeOne D r s
      (Finset.mem_union.mpr (Or.inl hrBottom)) hcapAdj
    have hcapOdd : Odd ((actualClosedCapZeroGraph D).degree r) := by
      rw [hcapDegree]
      decide
    obtain ⟨y,hyne,hyOdd,p,hp⟩ := actual_odd_vertex_has_distinct_path_partner
      (actualClosedCapZeroGraph D) r hcapOdd
    exact ⟨y,hyne,actualClosedCapGraphOddVerticesOnBoundary A W hCut.fst_subset hJ hBound y hyOdd,p,hp⟩
  have actualReturningPlanarPathWithOriginalSupport :
      ∃ v ∈ zeroBottomVertices, ∃ w ∈ zeroBottomVertices, v ≠ w ∧
        ∃ p : actualZeroGraph.Walk v w, p.IsPath ∧
          ∃ W, W ≠ [] ∧ actualPlanarGraph.IsPath (actualPlanarVertexPosition v) W
            (actualPlanarVertexPosition w) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition v) W =
              actualPlanarVertexPosition '' {r | r ∈ p.support} := by
    obtain ⟨v,hv,w,hw,hvw,p,hp⟩ := actualReturningGraphPath
    obtain ⟨W,hW,hverts⟩ := actual_simple_graph_path_to_labeled_graph_with_vertices
      actualZeroGraph actualPlanarGraph actualPlanarVertexPosition
      actualPlanarVertexPositionInjective (fun r => ⟨r,rfl⟩) actualPlanarAdjacentLink p hp
    refine ⟨v,hv,w,hw,hvw,p,hp,W,?_,hW,hverts⟩
    intro hnil
    rw [hnil] at hW
    exact hvw (actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil)
  have actualVertexAtBottomIsOriginal (v : zeroVertex)
      (hv : (zeroVertexPosition v).1 = 0) : v ∈ zeroBottomVertices := by
    rcases v with p | ⟨e,j⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,p,rfl,hv⟩
    · have hpos := actualCylinderZeroEdgeInteriorTimePositive e (privateParameter j)
        (privateParameterInterior j)
      change (cylinderZeroEdge e (privateParameter j)).1 = 0 at hv
      rw [hv] at hpos
      exact False.elim (lt_irrefl _ hpos)
  have actualPlanarPathBottomOnlyEndpoints {v w : zeroVertex}
      (p : actualZeroGraph.Walk v w) (hp : p.IsPath) (W : List (zeroEdgeIndex × Fin 3))
      (hverts : actualPlanarGraph.walkVertices (actualPlanarVertexPosition v) W =
        actualPlanarVertexPosition '' {r | r ∈ p.support})
      (z : Schoenflies.Plane) (hz : z ∈ Graph.edgesCover actualPlanarDrawing W)
      (hb : z ∈ Set.range actualCylinderBottomCircle) :
      z = actualPlanarVertexPosition v ∨ z = actualPlanarVertexPosition w := by
    obtain ⟨q,hq,hze⟩ := Graph.mem_edgesCover_iff.mp hz
    have hinc : actualPlanarGraph.Inc q z := by
      rcases actualPlanarEdgeArcBottomIsEndpoint q z hze hb with h0 | h1
      · exact ⟨actualSegmentPlanarPath q 1,Or.inl ⟨h0,rfl⟩⟩
      · exact ⟨actualSegmentPlanarPath q 0,Or.inr ⟨h1,rfl⟩⟩
    have hzVertex : z ∈ actualPlanarGraph.walkVertices (actualPlanarVertexPosition v) W :=
      Graph.mem_walkVertices_of_mem_covered ⟨q,hq,hinc⟩
    rw [hverts] at hzVertex
    obtain ⟨r,hr,he⟩ := hzVertex
    obtain ⟨u,hu⟩ := hb
    have hnorm : ‖z‖ = 2 := by
      rw [←hu]
      change ‖actualOuterCylinderSchoenflies (0,u)‖ = 2
      rw [actualOuterCylinderSchoenflies_norm]
      norm_num
    have htime : (zeroVertexPosition r).1 = 0 := by
      apply Subtype.ext
      have hn := actualOuterCylinderSchoenflies_norm (zeroVertexPosition r)
      change ‖actualPlanarVertexPosition r‖ = 2 - (zeroVertexPosition r).1.val at hn
      rw [he,hnorm] at hn
      change (zeroVertexPosition r).1.val = 0
      linarith only [hn]
    have hrBottom := actualVertexAtBottomIsOriginal r htime
    have hrBoundary : r ∈ zeroBottomVertices ∪ zeroTopVertices :=
      Finset.mem_union.mpr (Or.inl hrBottom)
    rcases actualReturningPathBoundarySupportOnlyEndpoints p hp r hr hrBoundary with rfl | rfl
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  have actualOriginalVertexOnBottomCircle (v : zeroVertex)
      (hv : actualPlanarVertexPosition v ∈ Set.range actualCylinderBottomCircle) :
      v ∈ zeroBottomVertices := by
    have hn : ‖actualPlanarVertexPosition v‖ = 2 := by
      rw [actualCylinderBottomCircle_range,Metric.mem_sphere,dist_zero_right] at hv
      exact hv
    have hnorm := actualOuterCylinderSchoenflies_norm (zeroVertexPosition v)
    change ‖actualPlanarVertexPosition v‖ = 2 - (zeroVertexPosition v).1.val at hnorm
    have ht : (zeroVertexPosition v).1 = 0 := by
      apply Subtype.ext
      change (zeroVertexPosition v).1.val = 0
      linarith only [hn,hnorm]
    exact actualVertexAtBottomIsOriginal v ht
  have actualCapGraphPartnerProducesReturningPath
      (A : Set Schoenflies.Plane) (W : List (zeroEdgeIndex × Fin 3)) (a b r y : zeroVertex)
      (hA : A ⊆ Set.range actualCylinderBottomCircle)
      (hb : b ∈ zeroBottomVertices) (hbA : actualPlanarVertexPosition b ∈ A) (hrb : r ≠ b)
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition a) W (actualPlanarVertexPosition b))
      (hyr : y ≠ r) (hy : actualPlanarVertexPosition y ∈ A ∪ Graph.edgesCover actualPlanarDrawing W)
      (p : (actualClosedCapZeroGraph ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W))).Walk r y) :
      ∃ z ∈ zeroBottomVertices, z ≠ r ∧ actualPlanarVertexPosition z ∈ A ∧
        ∃ U, actualPlanarGraph.IsPath (actualPlanarVertexPosition r) U (actualPlanarVertexPosition z) ∧
          ∀ q ∈ U, Graph.edgeArc actualPlanarDrawing q ⊆
            ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
              Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) := by
    let D := (A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
      Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)
    obtain ⟨U,hU,hUD⟩ := actual_simple_graph_walk_to_labeled_graph_with_edge_constraint
      (actualClosedCapZeroGraph D) actualPlanarGraph actualPlanarVertexPosition
      (fun q => Graph.edgeArc actualPlanarDrawing q ⊆ D)
      (fun v => ⟨v,rfl⟩) (fun {v w} hvw => hvw.2) p
    rcases hy with hyA | hyP
    · have hyB := actualOriginalVertexOnBottomCircle y (hA hyA)
      obtain ⟨Q,hQ,hQU⟩ := hU.contains_path
      exact ⟨y,hyB,hyr,hyA,Q,hQ,fun q hq => hUD q (hQU hq)⟩
    · obtain ⟨q,hq,hye⟩ := Graph.mem_edgesCover_iff.mp hyP
      have hinc : actualPlanarGraph.Inc q (actualPlanarVertexPosition y) := by
        rcases actualSegmentVertexOnArcIsEndpoint q y hye with h0 | h1
        · exact ⟨actualSegmentPlanarPath q 1,Or.inl ⟨h0,rfl⟩⟩
        · exact ⟨actualSegmentPlanarPath q 0,Or.inr ⟨h1,rfl⟩⟩
      have hyvisited : actualPlanarVertexPosition y ∈
          actualPlanarGraph.walkVertices (actualPlanarVertexPosition a) W :=
        Graph.mem_walkVertices_of_mem_covered ⟨q,hq,hinc⟩
      have hWD : ∀ q ∈ W, Graph.edgeArc actualPlanarDrawing q ⊆ D := by
        intro q hq x hx
        exact Or.inl (Or.inr (Graph.mem_edgesCover hq hx))
      obtain ⟨Q,hQ,hQD⟩ := actual_drawn_cap_path_join_at_visited_vertex actualPlanarGraph
        (fun q => Graph.edgeArc actualPlanarDrawing q ⊆ D) hU hW hyvisited hUD hWD
      exact ⟨b,hb,hrb.symm,hbA,Q,hQ,hQD⟩
  have actualAnyReturningEmbeddedCylinderPathWithGraphCarrier
      (v w : zeroVertex) (hv : v ∈ zeroBottomVertices) (hw : w ∈ zeroBottomVertices)
      (hvw : v ≠ w) (W : List (zeroEdgeIndex × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition v) W (actualPlanarVertexPosition w)) :
      ∃ q : Path (zeroVertexPosition v) (zeroVertexPosition w),
        Topology.IsEmbedding q ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1, 0 < (q t).1) ∧
        Set.range (cylinderTrace ∘ q) ⊆ b.val.image ∧
        actualOuterCylinderSchoenflies '' Set.range q = Graph.edgesCover actualPlanarDrawing W := by
    obtain ⟨p,hp,hverts⟩ := actual_labeled_graph_path_to_simple_graph_with_vertices
      actualZeroGraph actualPlanarGraph actualPlanarVertexPosition
      actualPlanarVertexPositionInjective (fun z hz => hz)
      (fun {v w e} h => actualPlanarLinkRecoversZeroGraphAdjacency h) hW v w rfl rfl
    have hWne : W ≠ [] := by
      intro hnil
      rw [hnil] at hW
      exact hvw (actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil)
    have hArc := actualPlanarDrawingIsDrawing.path_isArcBetween hW hWne
    have hAnn : Graph.edgesCover actualPlanarDrawing W ⊆ Set.range actualOuterCylinderSchoenflies := by
      intro z hz
      obtain ⟨e,he,hze⟩ := Graph.mem_edgesCover_iff.mp hz
      obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e z hze
      exact ⟨cylinderZeroEdge e.1 u,hpoint⟩
    obtain ⟨q,hq,himage⟩ := actual_annular_arc_lifts_to_embedded_cylinder_path hArc hAnn
    have hqpoint (t : Interval) : actualOuterCylinderSchoenflies (q t) ∈
        Graph.edgesCover actualPlanarDrawing W := himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
    refine ⟨q,hq,?_,?_,himage⟩
    · intro t ht
      by_contra hn
      have htime : (q t).1 = 0 := by
        apply Subtype.ext
        change (q t).1.val = 0
        have hle : (q t).1.val ≤ 0 := le_of_not_gt hn
        exact le_antisymm hle (q t).1.property.1
      have hbottom : actualOuterCylinderSchoenflies (q t) ∈ Set.range actualCylinderBottomCircle := by
        refine ⟨(q t).2,?_⟩
        change actualOuterCylinderSchoenflies (0,(q t).2) = actualOuterCylinderSchoenflies (q t)
        exact congrArg actualOuterCylinderSchoenflies (Prod.ext htime.symm rfl)
      rcases actualPlanarPathBottomOnlyEndpoints p hp W hverts _ (hqpoint t) hbottom with hv' | hw'
      · have hqv : q t = zeroVertexPosition v := actualOuterCylinderSchoenflies_embedding.injective hv'
        have ht0 : t = 0 := hq.injective (hqv.trans q.source.symm)
        exact (ne_of_gt ht.1) ht0
      · have hqw : q t = zeroVertexPosition w := actualOuterCylinderSchoenflies_embedding.injective hw'
        have ht1 : t = 1 := hq.injective (hqw.trans q.target.symm)
        exact (ne_of_lt ht.2) ht1
    · rintro z ⟨t,rfl⟩
      obtain ⟨e,he,hze⟩ := Graph.mem_edgesCover_iff.mp (hqpoint t)
      obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e _ hze
      have hqt : cylinderZeroEdge e.1 u = q t := actualOuterCylinderSchoenflies_embedding.injective hpoint
      change cylinderTrace (q t) ∈ b.val.image
      rw [←hqt]
      exact cylinderZeroEdgesOnComparison e.1 u
  have actualReturningEmbeddedCylinderPathWithGraphCarrier :
      ∃ v ∈ zeroBottomVertices, ∃ w ∈ zeroBottomVertices, v ≠ w ∧
        ∃ W : List (zeroEdgeIndex × Fin 3), W ≠ [] ∧
          actualPlanarGraph.IsPath (actualPlanarVertexPosition v) W (actualPlanarVertexPosition w) ∧
          ∃ q : Path (zeroVertexPosition v) (zeroVertexPosition w),
            Topology.IsEmbedding q ∧
            (∀ t ∈ Set.Ioo (0 : Interval) 1, 0 < (q t).1) ∧
            Set.range (cylinderTrace ∘ q) ⊆ b.val.image ∧
            actualOuterCylinderSchoenflies '' Set.range q = Graph.edgesCover actualPlanarDrawing W := by
    obtain ⟨v,hv,w,hw,hvw,p,hp,W,hWne,hW,hverts⟩ := actualReturningPlanarPathWithOriginalSupport
    have hArc := actualPlanarDrawingIsDrawing.path_isArcBetween hW hWne
    have hAnn : Graph.edgesCover actualPlanarDrawing W ⊆ Set.range actualOuterCylinderSchoenflies := by
      intro z hz
      obtain ⟨e,he,hze⟩ := Graph.mem_edgesCover_iff.mp hz
      obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e z hze
      exact ⟨cylinderZeroEdge e.1 u,hpoint⟩
    obtain ⟨q,hq,himage⟩ := actual_annular_arc_lifts_to_embedded_cylinder_path hArc hAnn
    have hqpoint (t : Interval) : actualOuterCylinderSchoenflies (q t) ∈
        Graph.edgesCover actualPlanarDrawing W := himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
    refine ⟨v,hv,w,hw,hvw,W,hWne,hW,q,hq,?_,?_,himage⟩
    · intro t ht
      by_contra hn
      have htime : (q t).1 = 0 := by
        apply Subtype.ext
        change (q t).1.val = 0
        have hle : (q t).1.val ≤ 0 := le_of_not_gt hn
        exact le_antisymm hle (q t).1.property.1
      have hbottom : actualOuterCylinderSchoenflies (q t) ∈ Set.range actualCylinderBottomCircle := by
        refine ⟨(q t).2,?_⟩
        change actualOuterCylinderSchoenflies (0,(q t).2) = actualOuterCylinderSchoenflies (q t)
        exact congrArg actualOuterCylinderSchoenflies (Prod.ext htime.symm rfl)
      rcases actualPlanarPathBottomOnlyEndpoints p hp W hverts _ (hqpoint t) hbottom with hv' | hw'
      · have hqv : q t = zeroVertexPosition v := actualOuterCylinderSchoenflies_embedding.injective hv'
        have ht0 : t = 0 := hq.injective (hqv.trans q.source.symm)
        exact (ne_of_gt ht.1) ht0
      · have hqw : q t = zeroVertexPosition w := actualOuterCylinderSchoenflies_embedding.injective hw'
        have ht1 : t = 1 := hq.injective (hqw.trans q.target.symm)
        exact (ne_of_lt ht.2) ht1
    · rintro z ⟨t,rfl⟩
      obtain ⟨e,he,hze⟩ := Graph.mem_edgesCover_iff.mp (hqpoint t)
      obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e _ hze
      have hqt : cylinderZeroEdge e.1 u = q t := actualOuterCylinderSchoenflies_embedding.injective hpoint
      change cylinderTrace (q t) ∈ b.val.image
      rw [←hqt]
      exact cylinderZeroEdgesOnComparison e.1 u
  have actualReturningEmbeddedCylinderPath :
      ∃ v ∈ zeroBottomVertices, ∃ w ∈ zeroBottomVertices, v ≠ w ∧
        ∃ q : Path (zeroVertexPosition v) (zeroVertexPosition w),
          Topology.IsEmbedding q ∧
          (∀ t ∈ Set.Ioo (0 : Interval) 1, 0 < (q t).1) ∧
          Set.range (cylinderTrace ∘ q) ⊆ b.val.image := by
    obtain ⟨v,hv,w,hw,hvw,W,hWne,hW,q,hq,hproper,htrace,himage⟩ :=
      actualReturningEmbeddedCylinderPathWithGraphCarrier
    exact ⟨v,hv,w,hw,hvw,q,hq,hproper,htrace⟩
  have actualReturningSurfacePathsWithHomotopy :
      ∃ u v : S, u ≠ v ∧ u ∈ a.val.image ∩ b.val.image ∧
        v ∈ a.val.image ∩ b.val.image ∧
        ∃ f g : Path u v, Topology.IsEmbedding f ∧
          Set.range f ⊆ a.val.image ∧ Set.range g ⊆ b.val.image ∧ f.Homotopic g := by
    obtain ⟨v,hv,w,hw,hvw,q,hq,hproper,htrace⟩ := actualReturningEmbeddedCylinderPath
    have htime (r : zeroVertex) (hr : r ∈ zeroBottomVertices) :
        (zeroVertexPosition r).1 = 0 := by
      obtain ⟨hru,p,he,hp⟩ := Finset.mem_filter.mp hr
      subst r
      exact hp
    have hb (z : Circle) : cylinderTrace (0,z) = a.val.map (z₀*z) :=
      (cylinderBoundaryOriginal z).1
    obtain ⟨hne,hu,hv',f,g,hf,hfa,hgb,hH⟩ := actual_proper_cylinder_returning_surface_paths
      a.val b.val cylinderTrace z₀ hb q hq (htime v hv) (htime w hw) hproper htrace
    exact ⟨cylinderTrace (zeroVertexPosition v),cylinderTrace (zeroVertexPosition w),
      hne,hu,hv',f,g,hf,hfa,hgb,hH⟩
  let actualReturningGraphCapProperty (v w : zeroVertex)
      (W : List (zeroEdgeIndex × Fin 3)) (A B : Set Schoenflies.Plane) : Prop :=
    v ∈ zeroBottomVertices ∧ w ∈ zeroBottomVertices ∧ v ≠ w ∧ W ≠ [] ∧
      actualPlanarGraph.IsPath (actualPlanarVertexPosition v) W (actualPlanarVertexPosition w) ∧
      Schoenflies.IsCutPair (Set.range actualCylinderBottomCircle)
        (actualPlanarVertexPosition v) (actualPlanarVertexPosition w) A B ∧
      Graph.edgesCover actualPlanarDrawing W \
        {actualPlanarVertexPosition v,actualPlanarVertexPosition w} ⊆
          Schoenflies.inside (Set.range actualCylinderBottomCircle) ∧
      Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualPlanarDrawing W) ∧
      ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) ⊆
          Set.range actualOuterCylinderSchoenflies
  have actualReturningGraphCapExists :
      ∃ v w W A B, actualReturningGraphCapProperty v w W A B := by
    obtain ⟨v,hv,w,hw,hvw,W,hWne,hW,q,hq,hproper,htrace,himage⟩ :=
      actualReturningEmbeddedCylinderPathWithGraphCarrier
    have htime (r : zeroVertex) (hr : r ∈ zeroBottomVertices) :
        (zeroVertexPosition r).1 = 0 := by
      obtain ⟨hru,p,he,hp⟩ := Finset.mem_filter.mp hr
      subst r
      exact hp
    obtain ⟨A,hA,hAC,hJ,hBound,B,hCut⟩ :=
      actual_proper_cylinder_arc_produces_annular_cap_with_cut_pair q hq (htime v hv) (htime w hw) hproper
    have hPimage : Set.range (actualOuterCylinderSchoenflies ∘ q) =
        Graph.edgesCover actualPlanarDrawing W := by
      rw [Set.range_comp]
      exact himage
    rw [hPimage] at hJ hBound
    have hPi : Graph.edgesCover actualPlanarDrawing W \
        {actualPlanarVertexPosition v,actualPlanarVertexPosition w} ⊆
          Schoenflies.inside (Set.range actualCylinderBottomCircle) := by
      rintro z ⟨hzP,hnot⟩
      rw [←hPimage] at hzP
      obtain ⟨t,he⟩ := hzP
      have ht0 : t ≠ 0 := by
        intro ht
        subst t
        apply hnot
        rw [←he]
        simp [actualPlanarVertexPosition]
      have ht1 : t ≠ 1 := by
        intro ht
        subst t
        apply hnot
        rw [←he]
        simp [actualPlanarVertexPosition]
      have htI : t ∈ Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩
      rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right,←he]
      change ‖actualOuterCylinderSchoenflies (q t)‖ < 2
      rw [actualOuterCylinderSchoenflies_norm]
      have htPos : 0 < (q t).1.val := hproper t htI
      linarith only [htPos]
    exact ⟨v,w,W,A,B,hv,hw,hvw,hWne,hW,hCut,hPi,hJ,hBound⟩
  let actualReturningCapEventCount (v w : zeroVertex) (A : Set Schoenflies.Plane) : ℕ :=
    (zeroBottomVertices.filter (fun r => actualPlanarVertexPosition r ∈ A ∧ r ≠ v ∧ r ≠ w)).card
  let actualReturningCapCountRealized (n : ℕ) : Prop :=
    ∃ v w W A B, actualReturningGraphCapProperty v w W A B ∧ actualReturningCapEventCount v w A = n
  have actualReturningCapCountExists : ∃ n, actualReturningCapCountRealized n := by
    obtain ⟨v,w,W,A,B,h⟩ := actualReturningGraphCapExists
    exact ⟨actualReturningCapEventCount v w A,v,w,W,A,B,h,rfl⟩
  let actualMinimumCapEventCount := Nat.find actualReturningCapCountExists
  have actualMinimumCapEventWitness : actualReturningCapCountRealized actualMinimumCapEventCount :=
    Nat.find_spec actualReturningCapCountExists
  have actualMinimumCapEventBound (v w : zeroVertex) (W : List (zeroEdgeIndex × Fin 3))
      (A B : Set Schoenflies.Plane) (h : actualReturningGraphCapProperty v w W A B) :
      actualMinimumCapEventCount ≤ actualReturningCapEventCount v w A :=
    Nat.find_min' actualReturningCapCountExists ⟨v,w,W,A,B,h,rfl⟩
  have actualMinimumReturningCapHasNoExtraEvents : actualMinimumCapEventCount = 0 := by
    obtain ⟨v,w,W,A,B,hOld,hCount⟩ := actualMinimumCapEventWitness
    obtain ⟨hv,hw,hvw,hWne,hW,hCut,hPi,hJ,hBound⟩ := hOld
    by_contra hnonzero
    have hpositive : 0 < actualReturningCapEventCount v w A := by omega
    obtain ⟨r,hr⟩ := Finset.card_pos.mp hpositive
    obtain ⟨hrBottom,hrA,hrv,hrw⟩ := Finset.mem_filter.mp hr
    have hrEnds : actualPlanarVertexPosition r ∉
        ({actualPlanarVertexPosition v,actualPlanarVertexPosition w} : Set Schoenflies.Plane) := by
      intro he
      rcases (by simpa using he : actualPlanarVertexPosition r = actualPlanarVertexPosition v ∨
        actualPlanarVertexPosition r = actualPlanarVertexPosition w) with he | he
      · exact hrv (actualPlanarVertexPositionInjective he)
      · exact hrw (actualPlanarVertexPositionInjective he)
    have hP := actualPlanarDrawingIsDrawing.path_isArcBetween hW hWne
    obtain ⟨y,hyr,hy,p,hp⟩ := actualClosedCapExtraBoundaryOddPartner
      A B W v w r hCut hP hPi hJ hBound hrBottom hrA hrEnds
    obtain ⟨z,hzBottom,hzr,hzA,Q,hQ,hQD⟩ := actualCapGraphPartnerProducesReturningPath
      A W v w r y hCut.fst_subset hw hCut.fst.right_mem hrw hW hyr hy p
    obtain ⟨R,T,hNewCut,hRA,hStrict⟩ := actual_boundary_cut_pair_with_strict_event_decrease
      zeroBottomVertices actualPlanarVertexPosition actualPlanarVertexPositionInjective
      v w r z hCut hrBottom hrA hrv hrw hzA hzr
    have hQne : Q ≠ [] := by
      intro hnil
      rw [hnil] at hQ
      exact hzr (actualPlanarVertexPositionInjective hQ.isWalk.eq_of_nil).symm
    have hQArc := actualPlanarDrawingIsDrawing.path_isArcBetween hQ hQne
    obtain ⟨q,hq,hqProper,hqTrace,hqImage⟩ := actualAnyReturningEmbeddedCylinderPathWithGraphCarrier
      r z hrBottom hzBottom hzr.symm Q hQ
    have hQImage : Set.range (actualOuterCylinderSchoenflies ∘ q) =
        Graph.edgesCover actualPlanarDrawing Q := by
      rw [Set.range_comp]
      exact hqImage
    have hNewPi : Graph.edgesCover actualPlanarDrawing Q \ 
        {actualPlanarVertexPosition r,actualPlanarVertexPosition z} ⊆
          Schoenflies.inside (Set.range actualCylinderBottomCircle) := by
      rintro x ⟨hxP,hnot⟩
      rw [←hQImage] at hxP
      obtain ⟨t,he⟩ := hxP
      have ht0 : t ≠ 0 := by
        intro ht
        subst t
        apply hnot
        rw [←he]
        simp [actualPlanarVertexPosition]
      have ht1 : t ≠ 1 := by
        intro ht
        subst t
        apply hnot
        rw [←he]
        simp [actualPlanarVertexPosition]
      have htI : t ∈ Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩
      rw [actualCylinderBottomCircle_inside,Metric.mem_ball,dist_zero_right,←he]
      change ‖actualOuterCylinderSchoenflies (q t)‖ < 2
      rw [actualOuterCylinderSchoenflies_norm]
      have hpositiveTime : (0 : ℝ) < (q t).1.val := hqProper t htI
      linarith only [hpositiveTime]
    have hQOld : Graph.edgesCover actualPlanarDrawing Q ⊆
        ((A ∪ Graph.edgesCover actualPlanarDrawing W) ∪
          Schoenflies.inside (A ∪ Graph.edgesCover actualPlanarDrawing W)) := by
      intro x hx
      obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
      exact hQD e he hxe
    obtain ⟨hNewJordan,hNewBound⟩ := actual_boundary_subarc_returning_cap_nested_general_endpoints
      actualCylinderBottomCircle_jordan hCut.fst hP hCut.fst_subset hPi
      hNewCut.fst hRA hQArc hNewPi hQOld
    have hNewProperty : actualReturningGraphCapProperty r z Q R T :=
      ⟨hrBottom,hzBottom,hzr.symm,hQne,hQ,hNewCut,hNewPi,hNewJordan,hNewBound.trans hBound⟩
    have hMinBound := actualMinimumCapEventBound r z Q R T hNewProperty
    have hStrictCount : actualReturningCapEventCount r z R < actualReturningCapEventCount v w A := by
      dsimp only [actualReturningCapEventCount]
      convert hStrict using 1 <;> congr 1 <;> ext x <;> simp
    omega
  -- The actual minimum cap has no extra events; realize its selected clean side on S.
  obtain ⟨v,w,W,A,B,hOld,hCount⟩ := actualMinimumCapEventWitness
  obtain ⟨hv,hw,hvw,hWne,hW,hCut,hPi,hJ,hBound⟩ := hOld
  have hNoEvents : actualReturningCapEventCount v w A = 0 := by
    rw [hCount,actualMinimumReturningCapHasNoExtraEvents]
  obtain ⟨p,hp,hproper,htrace,hPImage⟩ := actualAnyReturningEmbeddedCylinderPathWithGraphCarrier
    v w hv hw hvw W hW
  have hPRange : Set.range (actualOuterCylinderSchoenflies ∘ p) =
      Graph.edgesCover actualPlanarDrawing W := by
    rw [Set.range_comp]
    exact hPImage
  rw [←hPRange] at hJ hBound
  obtain ⟨q,hq,hqBottom,hqImage,hpq⟩ := actual_selected_cap_boundary_path_with_homotopy
    p hCut.fst hCut.fst_subset hJ hBound
  have hClean (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1) :
      cylinderTrace (q t) ∉ b.val.image := by
    intro htb
    have hqt0 : q t = (0,(q t).2) := Prod.ext (hqBottom t) rfl
    have hEP : q t ∈ zeroEndpointSet := by
      rw [hqt0]
      apply (actualBottomCylinderEventSet (q t).2).mpr
      rw [hqt0] at htb
      exact htb
    let r : zeroVertex := Sum.inl ⟨q t,hEP⟩
    have hrBottom : r ∈ zeroBottomVertices := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,⟨q t,hEP⟩,rfl,hqBottom t⟩
    have hrA : actualPlanarVertexPosition r ∈ A := by
      rw [←hqImage]
      exact ⟨q t,⟨t,rfl⟩,rfl⟩
    have hrv : r ≠ v := by
      intro he
      have hpos : q t = zeroVertexPosition v := congrArg zeroVertexPosition he
      have ht0 : t = 0 := hq.injective (hpos.trans q.source.symm)
      exact (ne_of_gt ht.1) ht0
    have hrw : r ≠ w := by
      intro he
      have hpos : q t = zeroVertexPosition w := congrArg zeroVertexPosition he
      have ht1 : t = 1 := hq.injective (hpos.trans q.target.symm)
      exact (ne_of_lt ht.2) ht1
    have hmem : r ∈ zeroBottomVertices.filter
        (fun s => actualPlanarVertexPosition s ∈ A ∧ s ≠ v ∧ s ≠ w) :=
      Finset.mem_filter.mpr ⟨hrBottom,hrA,hrv,hrw⟩
    have hpos := Finset.card_pos.mpr ⟨r,hmem⟩
    change 0 < actualReturningCapEventCount v w A at hpos
    omega
  have htime (r : zeroVertex) (hr : r ∈ zeroBottomVertices) :
      (zeroVertexPosition r).1 = 0 := by
    obtain ⟨hru,x,he,hx⟩ := Finset.mem_filter.mp hr
    subst r
    exact hx
  have bottomInjective {r s : Interval × Circle} (hr : r.1 = 0) (hs : s.1 = 0)
      (h : cylinderTrace r = cylinderTrace s) : r = s := by
    have hre : r = (0,r.2) := Prod.ext hr rfl
    have hse : s = (0,s.2) := Prod.ext hs rfl
    rw [hre,hse,(cylinderBoundaryOriginal r.2).1,(cylinderBoundaryOriginal s.2).1] at h
    exact Prod.ext (hr.trans hs.symm) (mul_left_cancel (a.val.embedded.injective h))
  have hneq : cylinderTrace (zeroVertexPosition v) ≠ cylinderTrace (zeroVertexPosition w) := by
    intro he
    have hpos := bottomInjective (htime v hv) (htime w hw) he
    exact hvw (zeroVertexPositionInjective hpos)
  have hOnOriginal (r : zeroVertex) (hr : r ∈ zeroBottomVertices) :
      cylinderTrace (zeroVertexPosition r) ∈ a.val.image := by
    rw [show zeroVertexPosition r = (0,(zeroVertexPosition r).2) from Prod.ext (htime r hr) rfl,
      (cylinderBoundaryOriginal (zeroVertexPosition r).2).1]
    exact ⟨z₀*(zeroVertexPosition r).2,rfl⟩
  let f := q.map cylinderTrace.continuous
  let g := p.map cylinderTrace.continuous
  have hf : Topology.IsEmbedding f := by
    apply (f.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    exact hq.injective (bottomInjective (hqBottom t) (hqBottom u) he)
  refine ⟨cylinderTrace (zeroVertexPosition v),cylinderTrace (zeroVertexPosition w),hneq,
    ⟨hOnOriginal v hv,htrace ⟨0,by simp⟩⟩,
    ⟨hOnOriginal w hw,htrace ⟨1,by simp⟩⟩,f,g,hf,?_,?_,?_,?_⟩
  · rintro x ⟨t,rfl⟩
    change cylinderTrace (q t) ∈ a.val.image
    rw [show q t = (0,(q t).2) from Prod.ext (hqBottom t) rfl,
      (cylinderBoundaryOriginal (q t).2).1]
    exact ⟨z₀*(q t).2,rfl⟩
  · exact htrace
  · rintro x ⟨t,ht,rfl⟩
    exact hClean t ht
  · exact (hpq.map cylinderTrace).symm

end CurveComplex.LocalSurgery
