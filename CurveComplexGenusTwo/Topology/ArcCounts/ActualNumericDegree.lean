import CurveComplexGenusTwo.Topology.ArcCounts.ActualObjectFaceCountNamedHeader
import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.TwoArcs
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance : DecidableEq S := Classical.decEq _
set_option maxHeartbeats 2800000

/-- Exactly the local simple endpoint graph used in `actual_object_face_count`.
It forgets parallel multiplicity, so actual representative labels are retained separately. -/
def actualEndpointWalkGraph (M : HyperellipticModel E S) {ι : Type}
    (r : ι → EssentialMarkedArc M) : SimpleGraph S where
  Adj q z := q ≠ z ∧ ∃ v : ι,
    ((r v).val.map 0 = q ∧ (r v).val.map 1 = z) ∨
    ((r v).val.map 0 = z ∧ (r v).val.map 1 = q)
  symm := ⟨by
    intro q z h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨v,hv⟩ := h.2
    exact ⟨v,hv.elim Or.inr Or.inl⟩⟩
  loopless := ⟨fun q h => h.1 rfl⟩

/-- Exact extraction of the finite-graph connectedness-to-endpoint-chain argument. -/
theorem actual_marked_graph_component_endpoint_chain
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w))) :
    let G := ⋃ v, (r v).val.image
    let R : S → S → Prop := fun p q => ∃ v : ι,
      ((r v).val.map 0 = p ∧ (r v).val.map 1 = q) ∨
      ((r v).val.map 0 = q ∧ (r v).val.map 1 = p)
    ∀ x ∈ M.cover.branch, x ∈ G → ∀ y ∈ M.cover.branch,
      y ∈ connectedComponentIn G x → Relation.ReflTransGen R x y := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  intro G R x hxb hxG y hyb hy
  let reach : S → Prop := Relation.ReflTransGen R x
  have hedge : ∀ v, reach ((r v).val.map 0) ↔ reach ((r v).val.map 1) := by
    intro v
    constructor
    · intro h
      exact Relation.ReflTransGen.tail h ⟨v,Or.inl ⟨rfl,rfl⟩⟩
    · intro h
      exact Relation.ReflTransGen.tail h ⟨v,Or.inr ⟨rfl,rfl⟩⟩
  have hmark : ∀ v z, z ∈ (r v).val.image → z ∈ M.cover.branch →
      (reach z ↔ reach ((r v).val.map 0)) := by
    intro v z hz hzb
    have he : z ∈ (markedArcEndset (r v).val : Set S) := by
      rw [← markedArc_image_inter_branch]
      exact ⟨hz,hzb⟩
    rcases (by simpa [markedArcEndset] using he : z = (r v).val.map 0 ∨ z = (r v).val.map 1) with he | he
    · rw [he]
    · rw [he]; exact (hedge v).symm
  let I : Finset ι := Finset.univ.filter (fun v => reach ((r v).val.map 0))
  let J : Finset ι := Finset.univ.filter (fun v => ¬reach ((r v).val.map 0))
  let C : Set S := ⋃ v ∈ I, (r v).val.image
  let D : Set S := ⋃ v ∈ J, (r v).val.image
  have hc : IsClosed C := I.finite_toSet.isClosed_biUnion
    (fun v _ => (markedArc_image_compact (r v).val).isClosed)
  have hdclosed : IsClosed D := J.finite_toSet.isClosed_biUnion
    (fun v _ => (markedArc_image_compact (r v).val).isClosed)
  have hcover : G = C ∪ D := by
    ext z
    constructor
    · intro hz
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hz
      by_cases hr : reach ((r v).val.map 0)
      · exact Or.inl (Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,hv⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,hv⟩⟩)
    · rintro (h | h)
      · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
        obtain ⟨_,hv⟩ := Set.mem_iUnion.mp hv
        exact Set.mem_iUnion.mpr ⟨v,hv⟩
      · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
        obtain ⟨_,hv⟩ := Set.mem_iUnion.mp hv
        exact Set.mem_iUnion.mpr ⟨v,hv⟩
  have hdisj : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hzC
    obtain ⟨hvI,hzv⟩ := Set.mem_iUnion.mp hv
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzD
    obtain ⟨hwJ,hzw⟩ := Set.mem_iUnion.mp hw
    have hrv : reach ((r v).val.map 0) := (Finset.mem_filter.mp hvI).2
    have hrw : ¬ reach ((r w).val.map 0) := (Finset.mem_filter.mp hwJ).2
    have hne : v ≠ w := by intro he; exact hrw (he ▸ hrv)
    have hzb : z ∈ M.cover.branch := by
      by_contra hn
      exact Set.disjoint_left.mp (hd v w hne) ⟨hzv,hn⟩ ⟨hzw,hn⟩
    exact hrw ((hmark w z hzw hzb).mp ((hmark v z hzv hzb).mpr hrv))
  have hxC : x ∈ C := by
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
    have hr : reach ((r v).val.map 0) := (hmark v x hv hxb).mp Relation.ReflTransGen.refl
    exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩,hv⟩⟩
  have hyC : y ∈ C := by
    by_contra hn
    have hyG := connectedComponentIn_subset G x hy
    have hyD : y ∈ D := (hcover ▸ hyG).resolve_left hn
    have hconn := isConnected_connectedComponentIn_iff.mpr hxG
    have hsub : connectedComponentIn G x ⊆ C ∪ D := by
      rw [← hcover]; exact connectedComponentIn_subset _ _
    obtain ⟨z,hzc,hzC,hzD⟩ := isPreconnected_closed_iff.mp hconn.isPreconnected
      C D hc hdclosed hsub ⟨x,mem_connectedComponentIn hxG,hxC⟩ ⟨y,hy,hyD⟩
    exact Set.disjoint_left.mp hdisj hzC hzD
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hyC
  obtain ⟨hvI,hvy⟩ := Set.mem_iUnion.mp hv
  exact (hmark v y hvy hyb).mpr (Finset.mem_filter.mp hvI).2

/-- Retain a concrete simple endpoint walk and an actual arc label for EVERY step.
The input is topological component membership; no reachability or incidence
certificate is assumed. The labels are indexed by the actual walk length. -/
theorem actual_marked_graph_component_labeled_walk
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    {x y : S} (hxb : x ∈ M.cover.branch) (hx : x ∈ ⋃ v, (r v).val.image)
    (hyb : y ∈ M.cover.branch)
    (hy : y ∈ connectedComponentIn (⋃ v, (r v).val.image) x) :
    ∃ W : (actualEndpointWalkGraph M r).Walk x y, W.IsPath ∧
      ∃ label : Fin W.length → ι,
        (∀ n, ((r (label n)).val.map 0 = W.getVert n.val ∧
                (r (label n)).val.map 1 = W.getVert (n.val + 1)) ∨
               ((r (label n)).val.map 0 = W.getVert (n.val + 1) ∧
                (r (label n)).val.map 1 = W.getVert n.val)) ∧
        (∀ n, (r (label n)).val.map 0 ≠ (r (label n)).val.map 1) ∧
        (∀ n, (r (label n)).val.image ⊆ ⋃ v, (r v).val.image) := by
  classical
  let R : S → S → Prop := fun q z => ∃ v : ι,
    ((r v).val.map 0 = q ∧ (r v).val.map 1 = z) ∨
    ((r v).val.map 0 = z ∧ (r v).val.map 1 = q)
  let H := actualEndpointWalkGraph M r
  have hchain : Relation.ReflTransGen R x y :=
    actual_marked_graph_component_endpoint_chain M r hd x hxb hx y hyb hy
  have hreach : H.Reachable x y := by
    apply (H.reachable_iff_reflTransGen x y).mpr
    exact Relation.ReflTransGen.lift' (r := R) (p := H.Adj) (id : S → S) (fun q z h => by
      by_cases he : q = z
      · subst z; exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨he,h⟩) x y hchain
  obtain ⟨W,hW⟩ := hreach.exists_isPath
  have hstep : ∀ n : Fin W.length, ∃ i : ι,
      ((r i).val.map 0 = W.getVert n.val ∧ (r i).val.map 1 = W.getVert (n.val + 1)) ∨
      ((r i).val.map 0 = W.getVert (n.val + 1) ∧ (r i).val.map 1 = W.getVert n.val) := by
    intro n
    exact (W.adj_getVert_succ n.isLt).2
  let label : Fin W.length → ι := fun n => Classical.choose (hstep n)
  have hlabel := fun n => Classical.choose_spec (hstep n)
  refine ⟨W,hW,label,hlabel,?_,?_⟩
  · intro n he
    have hne := (W.adj_getVert_succ n.isLt).1
    rcases hlabel n with h | h
    · exact hne (h.1.symm.trans (he.trans h.2))
    · exact hne (h.2.symm.trans (he.symm.trans h.1))
  · intro n z hz
    exact Set.mem_iUnion.mpr ⟨label n,hz⟩

/-- Retain the same actual arc labels together with their directed planar
arc-between geometry. This is the local `hArc` constructor, not an assumed
boundary-walk certificate. -/
theorem actual_marked_graph_component_labeled_plane_walk
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (p : S) (hp : p ∉ ⋃ v, (r v).val.image)
    {x y : S} (hxb : x ∈ M.cover.branch) (hx : x ∈ ⋃ v, (r v).val.image)
    (hyb : y ∈ M.cover.branch)
    (hy : y ∈ connectedComponentIn (⋃ v, (r v).val.image) x) :
    let e := M.puncturedPlane p
    let φ : S → Schoenflies.Plane := fun z => if hz : z ≠ p then e ⟨z,hz⟩ else 0
    let g : ι → Interval → Schoenflies.Plane := fun v t => e ⟨(r v).val.map t, by
      intro he
      exact hp (he ▸ Set.mem_iUnion.mpr ⟨v,Set.mem_range_self t⟩)⟩
    ∃ W : (actualEndpointWalkGraph M r).Walk x y, W.IsPath ∧
      ∃ label : Fin W.length → ι,
        (∀ n, ((r (label n)).val.map 0 = W.getVert n.val ∧
                (r (label n)).val.map 1 = W.getVert (n.val + 1)) ∨
               ((r (label n)).val.map 0 = W.getVert (n.val + 1) ∧
                (r (label n)).val.map 1 = W.getVert n.val)) ∧
        (∀ n, Schoenflies.IsArcBetween (Set.range (g (label n)))
          (φ (W.getVert n.val)) (φ (W.getVert (n.val + 1)))) := by
  classical
  intro e φ g
  obtain ⟨W,hW,label,hlabel,hNL,_⟩ :=
    actual_marked_graph_component_labeled_walk M r hd hxb hx hyb hy
  refine ⟨W,hW,label,hlabel,?_⟩
  have hgφ : ∀ v t, g v t = φ ((r v).val.map t) := by
    intro v t
    dsimp [g,φ]
    rw [dite_eq_left]
  intro n
  let a : NonLoopArc M := ⟨(r (label n)).val, hNL n⟩
  have hpi : p ∉ a.val.image := fun he => hp (Set.mem_iUnion.mpr ⟨label n,he⟩)
  have ha : Schoenflies.IsArcBetween (Set.range (g (label n)))
      (g (label n) 0) (g (label n) 1) := a.plane_isArcBetween p hpi
  rcases hlabel n with h | h
  · simpa only [hgφ,h.1,h.2] using ha
  · simpa only [hgφ,h.1,h.2] using ha.reverse

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_graph_component_endpoint_chain
#print axioms CurveComplex.HyperellipticModel.actual_marked_graph_component_labeled_walk

#print axioms CurveComplex.HyperellipticModel.actual_marked_graph_component_labeled_plane_walk

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Concatenate a concrete simple endpoint walk while retaining its actual
representative labels and EXACT selected-arc trace. -/
theorem actual_endpoint_path_exact_labeled_arc
    (M : HyperellipticModel E S) {ι : Type}
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (p : S) (hp : p ∉ ⋃ v, (r v).val.image)
    {x y : S} (W : (actualEndpointWalkGraph M r).Walk x y)
    (hW : W.IsPath) (hne : x ≠ y)
    (hx : x ∈ ⋃ v, (r v).val.image) (hy : y ∈ ⋃ v, (r v).val.image) :
    ∃ label : (actualEndpointWalkGraph M r).Dart → ι,
      (∀ d, ((r (label d)).val.map 0 = d.fst ∧ (r (label d)).val.map 1 = d.snd) ∨
            ((r (label d)).val.map 0 = d.snd ∧ (r (label d)).val.map 1 = d.fst)) ∧
      ∃ b : C(Interval,S), Function.Injective b ∧ b 0 = x ∧ b 1 = y ∧
        Set.range b = ⋃ d ∈ W.darts, (r (label d)).val.image := by
  classical
  let H := actualEndpointWalkGraph M r
  let label : H.Dart → ι := fun d => Classical.choose d.adj.2
  have hlabel : ∀ d : H.Dart,
      ((r (label d)).val.map 0 = d.fst ∧ (r (label d)).val.map 1 = d.snd) ∨
      ((r (label d)).val.map 0 = d.snd ∧ (r (label d)).val.map 1 = d.fst) :=
    fun d => Classical.choose_spec d.adj.2
  let e := M.puncturedPlane p
  let φ : S → Schoenflies.Plane := fun z => if hz : z ≠ p then e ⟨z,hz⟩ else 0
  let g : ι → Interval → Schoenflies.Plane := fun v t => e ⟨(r v).val.map t, by
    intro he
    exact hp (he ▸ Set.mem_iUnion.mpr ⟨v,Set.mem_range_self t⟩)⟩
  have hgφ : ∀ v t, g v t = φ ((r v).val.map t) := by
    intro v t
    dsimp [g,φ]
    rw [dite_eq_left]
  have hArc : ∀ d : H.Dart,
      Schoenflies.IsArcBetween (Set.range (g (label d))) (φ d.fst) (φ d.snd) := by
    intro d
    have hni : (r (label d)).val.map 0 ≠ (r (label d)).val.map 1 := by
      intro he
      rcases hlabel d with h | h
      · exact d.fst_ne_snd (h.1.symm.trans (he.trans h.2))
      · exact d.fst_ne_snd (h.2.symm.trans (he.symm.trans h.1))
    let a : NonLoopArc M := ⟨(r (label d)).val,hni⟩
    have hpi : p ∉ a.val.image := fun he => hp (Set.mem_iUnion.mpr ⟨label d,he⟩)
    have ha : Schoenflies.IsArcBetween (Set.range (g (label d)))
        (g (label d) 0) (g (label d) 1) := a.plane_isArcBetween p hpi
    rcases hlabel d with h | h
    · simpa only [hgφ,h.1,h.2] using ha
    · simpa only [hgφ,h.1,h.2] using ha.reverse
  let Trace {u v : S} (P : H.Walk u v) : Set Schoenflies.Plane :=
    ⋃ d ∈ P.darts, Set.range (g (label d))
  let T : List S → Set Schoenflies.Plane := fun L => {z | ∃ i : ι,
    (r i).val.map 0 ∈ L ∧ (r i).val.map 1 ∈ L ∧ z ∈ Set.range (g i)}
  have hTmono : ∀ {L K : List S}, (∀ z ∈ L, z ∈ K) → T L ⊆ T K := by
    intro L K h z hz
    obtain ⟨i,hi0,hi1,hzi⟩ := hz
    exact ⟨i,h _ hi0,h _ hi1,hzi⟩
  have hwalk : ∀ {u v : S} (W : H.Walk u v), W.IsPath → u ≠ v →
      Schoenflies.IsArcBetween (Trace W) (φ u) (φ v) ∧ Trace W ⊆ T W.support := by
    intro u v W
    induction W with
    | nil => intro _ hn; exact False.elim (hn rfl)
    | @cons u w v hadj W ih =>
      intro hpath hn
      have htail : W.IsPath := hpath.of_cons
      have hun : u ∉ W.support := (SimpleGraph.Walk.cons_isPath_iff hadj W).mp hpath |>.2
      let d : H.Dart := ⟨⟨u,w⟩,hadj⟩
      let i := label d
      have hiArc := hArc d
      have hiends : ((r i).val.map 0 = u ∧ (r i).val.map 1 = w) ∨
          ((r i).val.map 0 = w ∧ (r i).val.map 1 = u) := hlabel d
      have htrace : Trace (.cons hadj W) = Set.range (g i) ∪ Trace W := by
        ext z
        simp [Trace, SimpleGraph.Walk.darts_cons, d, i]
      have hiT : Set.range (g i) ⊆ T (u :: W.support) := by
        intro z hz
        rcases hiends with hiends | hiends
        · exact ⟨i,List.mem_cons.mpr (Or.inl hiends.1),
            List.mem_cons.mpr (Or.inr (by rw [hiends.2]; exact W.start_mem_support)),hz⟩
        · exact ⟨i,List.mem_cons.mpr (Or.inr (by rw [hiends.1]; exact W.start_mem_support)),
            List.mem_cons.mpr (Or.inl hiends.2),hz⟩
      by_cases hneTail : w ≠ v
      · let P := Trace W
        obtain ⟨hP,hPT⟩ := ih htail hneTail
        have hmeet : ∀ z ∈ Set.range (g i), z ∈ P → z = φ w := by
          intro z hzi hzP
          obtain ⟨s,hs⟩ := hzi
          obtain ⟨j,hj0,hj1,t,ht⟩ := hPT hzP
          have hij : i ≠ j := by
            intro he
            have hu : u ∈ W.support := by
              rcases hiends with hiends | hiends
              · exact hiends.1 ▸ (he.symm ▸ hj0)
              · exact hiends.2 ▸ (he.symm ▸ hj1)
            exact hun hu
          have heS : (r i).val.map s = (r j).val.map t := by
            exact congrArg Subtype.val (e.injective (hs.trans ht.symm))
          have hb : (r i).val.map s ∈ M.cover.branch := by
            by_contra hb
            exact Set.disjoint_left.mp (hd i j hij) ⟨Set.mem_range_self s,hb⟩
              ⟨⟨t,heS.symm⟩,hb⟩
          have hpnt : (r i).val.map s = u ∨ (r i).val.map s = w := by
            rcases (r i).val.marked_only_at_ends s hb with he | he
            · rcases hiends with h | h
              · exact Or.inl ((congrArg (r i).val.map he).trans h.1)
              · exact Or.inr ((congrArg (r i).val.map he).trans h.1)
            · rcases hiends with h | h
              · exact Or.inr ((congrArg (r i).val.map he).trans h.2)
              · exact Or.inl ((congrArg (r i).val.map he).trans h.2)
          have hew : (r i).val.map s = w := by
            rcases hpnt with heu | hew
            · exfalso
              have hju : (r j).val.map t = u := heS.symm.trans heu
              have hbj : (r j).val.map t ∈ M.cover.branch := heS ▸ hb
              rcases (r j).val.marked_only_at_ends t hbj with he | he
              · exact hun ((hju.symm.trans (congrArg (r j).val.map he)) ▸ hj0)
              · exact hun ((hju.symm.trans (congrArg (r j).val.map he)) ▸ hj1)
            · exact hew
          calc
            z = g i s := hs.symm
            _ = φ ((r i).val.map s) := hgφ i s
            _ = φ w := congrArg φ hew
        rw [htrace]
        refine ⟨hiArc.concatenate hP hmeet,?_⟩
        intro z hz
        rcases hz with hz | hz
        · exact hiT hz
        · exact hTmono (fun z hz => List.mem_cons.mpr (Or.inr hz)) (hPT hz)
      · have he : w = v := not_ne_iff.mp hneTail
        subst v
        have hnil : W = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil).mp htail
        subst W
        simpa [Trace, SimpleGraph.Walk.darts_cons, d, i] using
          (show Schoenflies.IsArcBetween (Set.range (g i)) (φ u) (φ w) ∧
            Set.range (g i) ⊆ T (u :: [w]) from ⟨hiArc,hiT⟩)
  obtain ⟨hP,_⟩ := hwalk W hW hne
  obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hP
  let fS : Interval → S := fun t => (e.symm (f t)).val
  have hfcS : Continuous fS := (continuous_subtype_val.comp e.symm.continuous).comp
    (continuousOn_iff_continuous_domRestrict.mp hfc)
  have hfiS : Function.Injective fS := by
    intro t u he
    apply Subtype.ext
    apply hfi t.property u.property
    exact e.symm.injective (Subtype.ext he)
  have hxp : x ≠ p := fun he => hp (he ▸ hx)
  have hyp : y ≠ p := fun he => hp (he ▸ hy)
  have hφx : φ x = e ⟨x,hxp⟩ := dif_pos hxp
  have hφy : φ y = e ⟨y,hyp⟩ := dif_pos hyp
  refine ⟨label,hlabel,⟨fS,hfcS⟩,hfiS,?_,?_,?_⟩
  · change (e.symm (f 0)).val = x
    rw [hf0,hφx,e.symm_apply_apply]
  · change (e.symm (f 1)).val = y
    rw [hf1,hφy,e.symm_apply_apply]
  · change Set.range fS = ⋃ d ∈ W.darts, (r (label d)).val.image
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      have hfmem : f t ∈ Trace W := hfim ▸ Set.mem_image_of_mem f t.property
      obtain ⟨d,hh⟩ := Set.mem_iUnion.mp hfmem
      obtain ⟨hdW,s,hs⟩ := Set.mem_iUnion.mp hh
      have he : fS t = (r (label d)).val.map s := by
        dsimp [fS]
        rw [← hs]
        change (e.symm (e _)).val = _
        rw [e.symm_apply_apply]
      exact Set.mem_iUnion.mpr ⟨d,Set.mem_iUnion.mpr ⟨hdW,he.symm ▸ Set.mem_range_self s⟩⟩
    · intro hz
      obtain ⟨d,hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hdW,t,ht⟩ := Set.mem_iUnion.mp hz
      have hgmem : g (label d) t ∈ Trace W :=
        Set.mem_iUnion.mpr ⟨d,Set.mem_iUnion.mpr ⟨hdW,Set.mem_range_self t⟩⟩
      obtain ⟨s,hs,he⟩ := hfim.symm ▸ hgmem
      refine ⟨⟨s,hs⟩,?_⟩
      dsimp [fS]
      rw [he]
      change (e.symm (e _)).val = z
      rw [e.symm_apply_apply]
      exact ht

/-- Close the retained labeled path by the additional actual nonloop arc.
The resulting Jordan circuit has EXACTLY the specified actual-arc union as
its image. Its directed traversal is W from a(0) to a(1), followed by a in
reverse, so the original representatives and their directions are retained. -/
theorem actual_cycle_with_exact_directed_labels
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (a : NonLoopArc M)
    (ha : ∀ v, Disjoint (a.val.image \ (M.cover.branch : Set S)) (arcInterior M (r v)))
    (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
    (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
    (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
    ∃ W : (actualEndpointWalkGraph M r).Walk (a.val.map 0) (a.val.map 1), W.IsPath ∧
      ∃ label : (actualEndpointWalkGraph M r).Dart → ι,
        (∀ d, ((r (label d)).val.map 0 = d.fst ∧ (r (label d)).val.map 1 = d.snd) ∨
              ((r (label d)).val.map 0 = d.snd ∧ (r (label d)).val.map 1 = d.fst)) ∧
        ∃ b : C(Interval,S), ∃ c : Curve S,
          Function.Injective b ∧ b 0 = a.val.map 0 ∧ b 1 = a.val.map 1 ∧
          Set.range b = ⋃ d ∈ W.darts, (r (label d)).val.image ∧
          c.image = a.val.image ∪ (⋃ d ∈ W.darts, (r (label d)).val.image) := by
  classical
  let t : Interval := ⟨(1:ℝ)/2, by constructor <;> norm_num⟩
  have ht0 : t ≠ 0 := by intro he; have h := congrArg Subtype.val he; norm_num [t] at h
  have ht1 : t ≠ 1 := by intro he; have h := congrArg Subtype.val he; norm_num [t] at h
  have htm : a.val.map t ∉ M.cover.branch := by
    intro hm
    exact ((a.val.marked_only_at_ends t hm).elim ht0 ht1)
  have hp : a.val.map t ∉ ⋃ v, (r v).val.image := by
    intro h
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp h
    exact Set.disjoint_left.mp (ha v) ⟨Set.mem_range_self t,htm⟩ ⟨hv,htm⟩
  obtain ⟨W,hW,_,_,_,_⟩ := actual_marked_graph_component_labeled_walk
    M r hd a.val.start_marked h0 a.val.end_marked hc
  obtain ⟨label,hlabel,b,hbi,hb0,hb1,hbtrace⟩ :=
    actual_endpoint_path_exact_labeled_arc M r hd (a.val.map t) hp W hW a.property h0 h1
  have hbG : Set.range b ⊆ ⋃ v, (r v).val.image := by
    rw [hbtrace]
    intro z hz
    obtain ⟨d,hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨_,hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨label d,hz⟩
  let f : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hinter : ∀ s u : Interval, f s = b u →
      (s = 0 ∧ u = 0) ∨ (s = 1 ∧ u = 1) := by
    intro s u he
    have he' : a.val.map s = b u := he
    have hxG : a.val.map s ∈ ⋃ v, (r v).val.image := by
      rw [he']; exact hbG (Set.mem_range_self u)
    have hmarked : a.val.map s ∈ M.cover.branch := by
      by_contra hn
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
      exact Set.disjoint_left.mp (ha v) ⟨Set.mem_range_self s,hn⟩ ⟨hv,hn⟩
    rcases a.val.marked_only_at_ends s hmarked with hs | hs
    · refine Or.inl ⟨hs,?_⟩
      apply hbi
      exact he.symm.trans ((congrArg a.val.map hs).trans hb0.symm)
    · refine Or.inr ⟨hs,?_⟩
      apply hbi
      exact he.symm.trans ((congrArg a.val.map hs).trans hb1.symm)
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨c,hcimage⟩ := CurveComplex.exists_curve_of_two_arcs
    f b a.injective hbi hb0.symm hb1.symm hinter
  refine ⟨W,hW,label,hlabel,b,c,hbi,hb0,hb1,hbtrace,?_⟩
  change c.image = a.val.image ∪ Set.range b at hcimage
  simpa only [hbtrace] using hcimage


/-- Produce an actual finite closed sequence of indexed directed arc pieces,
with chain compatibility, closure, and exact Jordan-curve image. `none` labels
the closing arc a; `some i` labels the original representative r i; the Bool
records traversal in reverse. No closed-walk certificate is an input. -/
theorem actual_cycle_finite_directed_sequence
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (a : NonLoopArc M)
    (ha : ∀ v, Disjoint (a.val.image \ (M.cover.branch : Set S)) (arcInterior M (r v)))
    (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
    (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
    (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
    let edge : Option ι → MarkedArc M := fun i => match i with
      | some j => (r j).val
      | none => a.val
    let start : Option ι × Bool → S := fun d =>
      if d.2 then (edge d.1).map 1 else (edge d.1).map 0
    let finish : Option ι × Bool → S := fun d =>
      if d.2 then (edge d.1).map 0 else (edge d.1).map 1
    ∃ L : List (Option ι × Bool), ∃ c : Curve S,
      L.IsChain (fun d e => finish d = start e) ∧
      L.head?.map start = some (a.val.map 0) ∧
      L.getLast?.map finish = some (a.val.map 0) ∧
      c.image = ⋃ d ∈ L, (edge d.1).image ∧
      ∃ W : (actualEndpointWalkGraph M r).Walk (a.val.map 0) (a.val.map 1),
        W.IsPath ∧ L.length = W.length + 1 := by
  classical
  intro edge start finish
  let H := actualEndpointWalkGraph M r
  obtain ⟨W,hW,label,hlabel,b,c,_,_,_,_,hcimage⟩ :=
    actual_cycle_with_exact_directed_labels M r hd a ha h0 h1 hc
  let step : H.Dart → Option ι × Bool := fun d =>
    (some (label d), if (r (label d)).val.map 0 = d.fst then false else true)
  have hstep : ∀ d : H.Dart, start (step d) = d.fst ∧ finish (step d) = d.snd := by
    intro d
    by_cases he : (r (label d)).val.map 0 = d.fst
    · rcases hlabel d with h | h
      · simp [start,finish,edge,step,he,h.1,h.2]
      · exact False.elim (d.fst_ne_snd (he.symm.trans h.1))
    · rcases hlabel d with h | h
      · exact False.elim (he h.1)
      · simp [start,finish,edge,step,he,h.1,h.2]
  have hsequence : ∀ {u v : S} (P : H.Walk u v) (tail : Option ι × Bool), start tail = v →
      (P.darts.map step ++ [tail]).IsChain (fun d e => finish d = start e) ∧
      (P.darts.map step ++ [tail]).head?.map start = some u := by
    intro u v P
    induction P with
    | nil =>
      intro tail ht
      exact ⟨List.IsChain.singleton tail, by simpa using congrArg some ht⟩
    | @cons u w v hadj P ih =>
      intro tail ht
      obtain ⟨hchain,hhead⟩ := ih tail ht
      let d : H.Dart := ⟨⟨u,w⟩,hadj⟩
      have hs : start (step d) = u := (hstep d).1
      have hf : finish (step d) = w := (hstep d).2
      simp only [SimpleGraph.Walk.darts_cons,List.map_cons,List.cons_append]
      cases htail : P.darts.map step ++ [tail] with
      | nil =>
        have hn : P.darts.map step ++ [tail] ≠ [] := by simp
        exact False.elim (hn htail)
      | cons q qs =>
        rw [htail] at hchain hhead
        have hq : start q = w := by simpa using hhead
        constructor
        · apply List.isChain_cons_cons.mpr
          exact ⟨by change finish (step d) = start q; rw [hf,hq],hchain⟩
        · simpa only [List.head?_cons,Option.map_some] using congrArg some hs
  let L := W.darts.map step ++ [(none,true)]
  have ht : start (none,true) = a.val.map 1 := by simp [start,edge]
  obtain ⟨hchain,hhead⟩ := hsequence W (none,true) ht
  refine ⟨L,c,hchain,hhead,?_,?_,W,hW,?_⟩
  · simp [L,List.getLast?_append_cons,finish,edge]
  · rw [hcimage]
    ext z
    simp [L,edge,step,Set.mem_iUnion,or_comm]
    rfl
  · simp [L]

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_endpoint_path_exact_labeled_arc
#print axioms CurveComplex.HyperellipticModel.actual_cycle_with_exact_directed_labels

#print axioms CurveComplex.HyperellipticModel.actual_cycle_finite_directed_sequence

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- An actual nonloop cycle edge splits its containing OLD graph face into
exactly two local faces. The finite split family and containing face are
constructed; no side or face certificate is assumed. The original proof's
Jordan crosscut argument is retained, with its path replaced by the exact
labeled-cycle producer. -/
theorem actual_nonloop_cycle_edge_split_faces
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (a : EssentialMarkedArc M) (haNL : a.val.map 0 ≠ a.val.map 1)
    (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
    (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
    (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
    (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
    ∃ U : Set S, IsComplementComponent (⋃ v, (r v).val.image) U ∧
      a.val.image ⊆ U ∪ (⋃ v, (r v).val.image) ∧ arcInterior M a ⊆ U ∧
      ∃ F : Finset (Set S), F.card = 2 ∧
        ∀ V : Set S, IsComplementComponent (Uᶜ ∪ a.val.image) V ↔ V ∈ F := by
  have hplace (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
      (r : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
      (hd : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
      (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
      (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image) :
      ∃ U : Set S, IsComplementComponent (⋃ v, (r v).val.image) U ∧
        a.val.image ⊆ U ∪ (⋃ v, (r v).val.image) ∧ arcInterior M a ⊆ U ∧
        a.val.image ⊆ closure U ∧ a.val.map 0 ∈ frontier U ∧ a.val.map 1 ∈ frontier U := by
    have hi : a.val.map '' Set.Ioo (0 : Interval) 1 = arcInterior M a := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        refine ⟨⟨t,rfl⟩,?_⟩
        intro hb
        rcases a.val.marked_only_at_ends t hb with h | h
        · simpa [h] using ht.1
        · simpa [h] using ht.2
      · rintro ⟨⟨t,rfl⟩,hn⟩
        have ht0 : (t : ℝ) ≠ 0 := by
          intro h
          have he : t = (0 : Interval) := Subtype.ext h
          exact hn (he ▸ a.val.start_marked)
        have ht1 : (t : ℝ) ≠ 1 := by
          intro h
          have he : t = (1 : Interval) := Subtype.ext h
          exact hn (he ▸ a.val.end_marked)
        refine ⟨t,?_,rfl⟩
        change (0 : ℝ) < t.val ∧ t.val < 1
        exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
    have hci : IsConnected (arcInterior M a) := by
      rw [← hi]
      have hc : IsConnected (Set.Ioo (0 : Interval) 1) :=
        ⟨⟨⟨(1:ℝ)/2, by constructor <;> norm_num⟩, by
            constructor
            · change (0 : ℝ) < 1/2; norm_num
            · change (1 : ℝ)/2 < 1; norm_num⟩,
          isPreconnected_Ioo⟩
      exact hc.image a.val.map a.val.continuous.continuousOn
    have hdense : a.val.image ⊆ closure (arcInterior M a) := by
      rintro y ⟨t,ht⟩
      have htcl : t ∈ closure (Set.Ioo (0 : Interval) 1) := by
        rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
        constructor
        · change (0 : ℝ) ≤ t.val; exact t.property.1
        · change t.val ≤ (1 : ℝ); exact t.property.2
      have hm : a.val.map t ∈ closure (a.val.map '' Set.Ioo (0 : Interval) 1) :=
        image_closure_subset_closure_image a.val.continuous ⟨t,htcl,rfl⟩
      rw [hi] at hm
      exact ht ▸ hm
    let G := ⋃ v, (r v).val.image
    have havoid : arcInterior M a ⊆ Gᶜ := by
      intro x hx hxG
      obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
      exact Set.disjoint_left.mp (hd v) hx ⟨hv,hx.2⟩
    obtain ⟨x,hx⟩ := hci.nonempty
    let U := connectedComponentIn Gᶜ x
    have hU : IsComplementComponent G U :=
      complementComponent_iff_componentIn.mpr ⟨x,havoid hx,rfl⟩
    have hsub : arcInterior M a ⊆ U := hci.isPreconnected.subset_connectedComponentIn hx havoid
    have hclU : a.val.image ⊆ closure U := hdense.trans (closure_mono hsub)
    letI : T2Space S := M.sphere.symm.t2Space
    letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
    have hopen : IsOpen U := complementComponent_open
      (markedFamily_graph_compact (fun v => (r v).val)).isClosed hU
    have hf0 : a.val.map 0 ∈ frontier U := by
      rw [hopen.frontier_eq]
      exact ⟨hclU (Set.mem_range_self 0),fun hx => hU.2.2.1 hx h0⟩
    have hf1 : a.val.map 1 ∈ frontier U := by
      rw [hopen.frontier_eq]
      exact ⟨hclU (Set.mem_range_self 1),fun hx => hU.2.2.1 hx h1⟩
    refine ⟨U,hU,?_,hsub,hclU,hf0,hf1⟩
    intro y hy
    by_cases hb : y ∈ M.cover.branch
    · right
      obtain ⟨t,ht⟩ := hy
      have htm : a.val.map t ∈ M.cover.branch := ht.symm ▸ hb
      rcases a.val.marked_only_at_ends t htm with he | he
      · exact ht ▸ he ▸ h0
      · exact ht ▸ he ▸ h1
    · left
      exact hsub ⟨hy,hb⟩
  have hcycle (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
      (r : ι → EssentialMarkedArc M)
      (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
      (a : NonLoopArc M)
      (ha : ∀ v, Disjoint (a.val.image \ (M.cover.branch : Set S)) (arcInterior M (r v)))
      (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
      (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
      (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
      ∃ b : C(Interval,S), ∃ c : Curve S,
        Function.Injective b ∧ b 0 = a.val.map 0 ∧ b 1 = a.val.map 1 ∧
        Set.range b ⊆ ⋃ v, (r v).val.image ∧ c.image = a.val.image ∪ Set.range b := by
    obtain ⟨W,hW,label,hlabel,b,c,hbi,hb0,hb1,hbtrace,hcimage⟩ :=
      actual_cycle_with_exact_directed_labels M r hd a ha h0 h1 hc
    have hbG : Set.range b ⊆ ⋃ v, (r v).val.image := by
      rw [hbtrace]
      intro z hz
      obtain ⟨d,hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨_,hz⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨label d,hz⟩
    refine ⟨b,c,hbi,hb0,hb1,hbG,?_⟩
    simpa only [hbtrace] using hcimage
  have hoff (M : HyperellipticModel E S) (c : Curve S) :
      ∃ p : S, p ∉ c.image := by
    have hcircle : ¬ IsPreconnected (({(1 : Circle),-1} : Set Circle)ᶜ) := by
      intro hc
      let u : Circle := ⟨-Complex.I, by change -Complex.I ∈ Metric.sphere (0 : ℂ) 1; rw [mem_sphere_zero_iff_norm]; simp⟩
      let v : Circle := ⟨Complex.I, by change Complex.I ∈ Metric.sphere (0 : ℂ) 1; rw [mem_sphere_zero_iff_norm]; simp⟩
      have hu : u ∈ ({(1 : Circle),-1} : Set Circle)ᶜ := by
        intro h
        rcases (by simpa using h : u = 1 ∨ u = -1) with h | h
        · have he := congrArg (fun z : Circle => (z : ℂ).im) h
          norm_num [u] at he
        · have he := congrArg (fun z : Circle => (z : ℂ).im) h
          norm_num [u] at he
      have hv : v ∈ ({(1 : Circle),-1} : Set Circle)ᶜ := by
        intro h
        rcases (by simpa using h : v = 1 ∨ v = -1) with h | h
        · have he := congrArg (fun z : Circle => (z : ℂ).im) h
          norm_num [v] at he
        · have he := congrArg (fun z : Circle => (z : ℂ).im) h
          norm_num [v] at he
      let f : Circle → ℝ := fun z => (z : ℂ).im
      have hf : Continuous f := by fun_prop
      have hz : (0 : ℝ) ∈ Set.Icc (f u) (f v) := by norm_num [f,u,v]
      obtain ⟨z,hzT,hz0⟩ := hc.intermediate_value hu hv hf.continuousOn hz
      have hzim : (z : ℂ).im = 0 := hz0
      have hzre : (z : ℂ).re ^ 2 = 1 := by
        have h := Complex.sq_norm_sub_sq_im (z : ℂ)
        rw [Circle.norm_coe,hzim] at h
        nlinarith
      rcases sq_eq_one_iff.mp hzre with h | h
      · have he : z = 1 := Circle.ext (by
          apply Complex.ext
          · simpa using h
          · simpa using hzim)
        exact hzT (by simp [he])
      · have he : z = -1 := Circle.ext (by
          apply Complex.ext
          · simpa using h
          · simpa using hzim)
        exact hzT (by simp [he])
    have hfinite : ∀ (F : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)),
        F.Finite → ∀ v ∈ F, IsPreconnected Fᶜ := by
      intro F hF v hv
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
      let e := stereographic' 2 v
      have he : Topology.IsOpenEmbedding e.symm := e.symm.isOpenEmbedding (by simp [e])
      have hr : Set.range e.symm = {v}ᶜ := by
        simpa [e] using e.symm.image_source_eq_target
      have hpre : (e.symm ⁻¹' F).Finite := hF.preimage he.injective.injOn
      have hc := hpre.countable.isConnected_compl_of_one_lt_rank
        (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)))
      have hi : e.symm '' (e.symm ⁻¹' F)ᶜ = Fᶜ := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          have hxv : x ≠ v := fun h => hx (h ▸ hv)
          have hxr : x ∈ Set.range e.symm := by rwa [hr]
          obtain ⟨y, rfl⟩ := hxr
          exact ⟨y, hx, rfl⟩
      rw [← hi]
      exact hc.isPreconnected.image _ he.continuous.continuousOn
    classical
    by_contra h
    push Not at h
    have hsurj : Function.Surjective c.map := h
    let e : Circle ≃ₜ CurveComplex.SpherePort.Sphere :=
      (c.embedded.toHomeomorphOfSurjective hsurj).trans M.sphere
    let F : Set CurveComplex.SpherePort.Sphere := e '' ({(1 : Circle),-1} : Set Circle)
    have hpair : ({(1 : Circle),-1} : Set Circle).Finite := by simp
    have hF : F.Finite := hpair.image e
    have he1 : e 1 ∈ F := Set.mem_image_of_mem e (by simp)
    have hc : IsPreconnected Fᶜ := hfinite F hF (e 1) he1
    have heq : e.symm '' Fᶜ = ({(1 : Circle),-1} : Set Circle)ᶜ := by
      rw [e.symm.image_compl]
      have hback : e.symm '' F = ({(1 : Circle),-1} : Set Circle) := by
        rw [← image_comp,e.symm_comp_self,image_id]
      rw [hback]
    apply hcircle
    rw [← heq]
    exact hc.image _ e.symm.continuous.continuousOn
  have hsplit (M : HyperellipticModel E S) (a : NonLoopArc M)
      (b : C(Interval,S)) (hbi : Function.Injective b)
      (hb0 : b 0 = a.val.map 0) (hb1 : b 1 = a.val.map 1)
      (hmeet : Set.range b ∩ a.image = {a.val.map 0,a.val.map 1})
      {U : Set S} (hbU : Disjoint (Set.range b) U) (hU : IsOpen U)
      (hcU : IsConnected U) (h0 : a.val.map 0 ∉ U) (h1 : a.val.map 1 ∉ U)
      (hinter : a.image \ {a.val.map 0,a.val.map 1} ⊆ U)
      (p : S) (hp : p ∉ a.image ∪ Set.range b) :
      ∃ x ∈ U \ a.image, ∃ y ∈ U \ a.image,
        connectedComponentIn (U \ a.image) x ≠ connectedComponentIn (U \ a.image) y ∧
        ∀ z ∈ U \ a.image, z ∈ connectedComponentIn (U \ a.image) x ∨
          z ∈ connectedComponentIn (U \ a.image) y := by
    have hplane (M : HyperellipticModel E S) (a : NonLoopArc M)
        (b : C(Interval,S)) (hbi : Function.Injective b)
        (hb0 : b 0 = a.val.map 0) (hb1 : b 1 = a.val.map 1)
        (hmeet : Set.range b ∩ a.image = {a.val.map 0,a.val.map 1})
        {U : Set S} (hbU : Disjoint (Set.range b) U) (hU : IsOpen U) (hcU : IsConnected U)
        (h0 : a.val.map 0 ∉ U) (h1 : a.val.map 1 ∉ U)
        (hinter : a.image \ {a.val.map 0,a.val.map 1} ⊆ U)
        (p : S) (hp : p ∉ a.image ∪ Set.range b) :
        let e := M.puncturedPlane p
        let f : Schoenflies.Plane → S := fun z => (e.symm z).val
        let g : Interval → Schoenflies.Plane := fun t => e ⟨a.val.map t,by
          intro he; exact hp (Or.inl (he ▸ Set.mem_range_self t))⟩
        ∃ zL ∈ f ⁻¹' U \ Set.range g, ∃ zR ∈ f ⁻¹' U \ Set.range g,
          connectedComponentIn (f ⁻¹' U \ Set.range g) zL ≠
            connectedComponentIn (f ⁻¹' U \ Set.range g) zR ∧
          ∀ x ∈ f ⁻¹' U \ Set.range g,
            x ∈ connectedComponentIn (f ⁻¹' U \ Set.range g) zL ∨
            x ∈ connectedComponentIn (f ⁻¹' U \ Set.range g) zR := by
      have htwo {D A P : Set Plane} {a b : Plane}
        (hDopen : IsOpen D) (hDconn : IsConnected D)
        (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
        (hmeet : A ∩ P = {a,b}) (hAD : Disjoint A D)
        (ha : a ∉ D) (hb : b ∉ D) (hPD : P \ {a,b} ⊆ D) :
        ∃ x ∈ D \ P, ∃ y ∈ D \ P,
          connectedComponentIn (D \ P) x ≠ connectedComponentIn (D \ P) y ∧
          ∀ z ∈ D \ P, z ∈ connectedComponentIn (D \ P) x ∨
            z ∈ connectedComponentIn (D \ P) y := by
        have hJ : IsJordanCurve (A ∪ P) := isJordanCurve_union hA hP (fun z hzA hzP => by
          have hz : z ∈ ({a,b} : Set Plane) := hmeet ▸ ⟨hzA,hzP⟩
          simpa using hz)
        have hsep := jordan_curve_theorem hJ
        obtain ⟨f,hf,hfi,hfr,hfa,hfb⟩ := hP
        have hhalf : (1/2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have hzP : f (1/2) ∈ P := by rw [← hfr]; exact ⟨1/2,hhalf,rfl⟩
        have hzab : f (1/2) ∉ ({a,b} : Set Plane) := by
          intro hz
          rcases (by simpa using hz : f (1/2) = a ∨ f (1/2) = b) with hz|hz
          · have he := hfi hhalf (by norm_num : (0 : ℝ) ∈ Icc 0 1) (hz.trans hfa.symm)
            norm_num at he
          · have he := hfi hhalf (by norm_num : (1 : ℝ) ∈ Icc 0 1) (hz.trans hfb.symm)
            norm_num at he
        have hzD := hPD ⟨hzP,hzab⟩
        have hzclI : f (1/2) ∈ closure (inside (A ∪ P)) := by
          apply frontier_subset_closure
          rw [hsep.frontier_inside]
          exact Or.inr hzP
        have hzclO : f (1/2) ∈ closure (outside (A ∪ P)) := by
          apply frontier_subset_closure
          rw [hsep.frontier_outside]
          exact Or.inr hzP
        obtain ⟨x,hxD,hxI⟩ := mem_closure_iff.mp hzclI D hDopen hzD
        obtain ⟨y,hyD,hyO⟩ := mem_closure_iff.mp hzclO D hDopen hzD
        have hx : x ∈ D \ P := ⟨hxD,fun hxP => inside_subset_compl hxI (Or.inr hxP)⟩
        have hy : y ∈ D \ P := ⟨hyD,fun hyP => outside_subset_compl hyO (Or.inr hyP)⟩
        have hsub : D \ P ⊆ (A ∪ P)ᶜ := by
          rintro z ⟨hzD,hzP⟩ (hzA|hzP')
          · exact disjoint_left.mp hAD hzA hzD
          · exact hzP hzP'
        have hxi : connectedComponentIn (D \ P) x ⊆ inside (A ∪ P) := by
          have hs : connectedComponentIn (D \ P) x ⊆ connectedComponentIn (A ∪ P)ᶜ x :=
            (isConnected_connectedComponentIn_iff.mpr hx).isPreconnected.subset_connectedComponentIn
              (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans hsub)
          rw [hsep.connectedComponentIn_eq_inside hxI] at hs
          exact hs
        have hne : connectedComponentIn (D \ P) x ≠ connectedComponentIn (D \ P) y := by
          intro he
          have hyI := hxi (he.symm ▸ mem_connectedComponentIn hy)
          exact disjoint_left.mp disjoint_inside_outside hyI hyO
        refine ⟨x,hx,y,hy,hne,?_⟩
        exact crosscut_components_exhaust_of_collars hDopen hDconn.isPreconnected
          ⟨f,hf,hfi,hfr,hfa,hfb⟩ ha hb hPD
          (hasArcCollars_of_jordan_arc_split hDopen hA ⟨f,hf,hfi,hfr,hfa,hfb⟩ hmeet hJ ha hb hPD)
          hx hy hne
      have hpuncture : ∀ {U : Set S}, IsOpen U → IsConnected U → ∀ p : S,
          IsConnected (U \ {p}) := by
        intro U hU hcU p
        letI : T2Space S := M.sphere.symm.t2Space
        letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
        have hlocal : ∀ {U N : Set S} {p : S}, IsOpen U → IsConnected U →
            IsOpen N → p ∈ N → N ⊆ U → IsConnected (N \ {p}) → IsConnected (U \ {p}) := by
          intro U N p hU hcU hN hpN hNU hcN
          obtain ⟨x,hx⟩ := hcN.nonempty
          let C := connectedComponentIn (U \ {p}) x
          have hxU : x ∈ U \ {p} := ⟨hNU hx.1,hx.2⟩
          have hcC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxU
          have hNC : N \ {p} ⊆ C := hcN.isPreconnected.subset_connectedComponentIn hx
            (fun y hy => ⟨hNU hy.1,hy.2⟩)
          have hCsub : C ⊆ U \ {p} := connectedComponentIn_subset _ _
          have hcomp : IsComplementComponent (Uᶜ ∪ {p}) C := by
            apply complementComponent_iff_componentIn.mpr
            refine ⟨x,?_,?_⟩
            · simpa only [mem_compl_iff,mem_union,not_or,not_not,mem_sdiff] using hxU
            · change connectedComponentIn (U \ {p}) x = _
              congr 1
              ext y
              simp [and_comm]
          have hclosed : IsClosed (Uᶜ ∪ {p}) := hU.isClosed_compl.union isClosed_singleton
          have hCopen : IsOpen C := complementComponent_open hclosed hcomp
          have heq : C ∪ {p} = C ∪ N := by
            ext y
            constructor
            · rintro (hy|hy)
              · exact Or.inl hy
              · exact Or.inr ((mem_singleton_iff.mp hy) ▸ hpN)
            · rintro (hy|hy)
              · exact Or.inl hy
              · by_cases hyp : y = p
                · exact Or.inr (mem_singleton_iff.mpr hyp)
                · exact Or.inl (hNC ⟨hy,hyp⟩)
          have hopen : IsOpen (C ∪ {p}) := heq ▸ hCopen.union hN
          have hfront : frontier C ⊆ Uᶜ ∪ {p} := complementComponent_frontier_subset hclosed hcomp
          have hall : U ⊆ C ∪ {p} := hcU.isPreconnected.subset_of_closure_inter_subset hopen
            ⟨x,hxU.1,Or.inl (mem_connectedComponentIn hxU)⟩ (by
              rintro y ⟨hy,hyU⟩
              rw [closure_union,isClosed_singleton.closure_eq] at hy
              rcases hy with hy|hy
              · by_cases hyC : y ∈ C
                · exact Or.inl hyC
                · have hf : y ∈ frontier C := by
                    rw [frontier,hCopen.interior_eq]
                    exact ⟨hy,hyC⟩
                  rcases hfront hf with hn|hp
                  · exact False.elim (hn hyU)
                  · exact Or.inr hp
              · exact Or.inr hy)
          have he : U \ {p} = C := by
            apply Subset.antisymm
            · intro y hy
              exact (hall hy.1).resolve_right hy.2
            · exact hCsub
          exact he.symm ▸ hcC
        have hball : ∀ z : Schoenflies.Plane, ∀ r : ℝ, 0 < r →
            IsConnected (Metric.ball z r \ {z}) := by
          intro z r hr
          let F := OpenPartialHomeomorph.univBall z r
          have hsource : F.source = Set.univ := OpenPartialHomeomorph.univBall_source z r
          have htarget : F.target = Metric.ball z r := OpenPartialHomeomorph.univBall_target z hr
          have hF : Continuous F := OpenPartialHomeomorph.continuous_univBall z r
          have hzero : F 0 = z := OpenPartialHomeomorph.univBall_apply_zero z r
          have hi : F '' ({0} : Set Schoenflies.Plane)ᶜ = Metric.ball z r \ {z} := by
            ext y
            constructor
            · rintro ⟨x,hx,rfl⟩
              refine ⟨?_,?_⟩
              · rw [← htarget]; exact F.map_source (hsource ▸ Set.mem_univ x)
              · intro he
                have hx0 : x = 0 := F.injOn (hsource ▸ Set.mem_univ x)
                  (hsource ▸ Set.mem_univ 0) ((Set.mem_singleton_iff.mp he).trans hzero.symm)
                exact hx (Set.mem_singleton_iff.mpr hx0)
            · rintro ⟨hy,hyn⟩
              have hyt : y ∈ F.target := htarget ▸ hy
              refine ⟨F.symm y,?_,F.right_inv hyt⟩
              intro he
              have hyz : y = z := (F.right_inv hyt).symm.trans
                ((congrArg F (Set.mem_singleton_iff.mp he)).trans hzero)
              exact hyn (Set.mem_singleton_iff.mpr hyz)
          rw [← hi]
          exact (isConnected_compl_singleton_of_one_lt_rank
            (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ Schoenflies.Plane) 0).image F hF.continuousOn
        by_cases hpU : p ∈ U
        · obtain ⟨q,hq⟩ : ∃ q : S, q ≠ p := by
            classical
            by_contra h
            push_neg at h
            have hs : M.cover.branch ⊆ {p} := by
              intro q hq
              exact Finset.mem_singleton.mpr (h q)
            have hc := Finset.card_le_card hs
            rw [M.cover.branch_card,Finset.card_singleton] at hc
            omega
          let e := M.puncturedPlane q
          let f : Schoenflies.Plane → S := fun z => (e.symm z).val
          let z := e ⟨p,Ne.symm hq⟩
          have hf : Topology.IsOpenEmbedding f :=
            isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
          have hfz : f z = p := congrArg Subtype.val (e.symm_apply_apply _)
          have hD : IsOpen (f ⁻¹' U) := hU.preimage hf.continuous
          obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hD z (by simpa [hfz] using hpU)
          let N := f '' Metric.ball z r
          have hN : IsOpen N := hf.isOpenMap _ isOpen_ball
          have hpN : p ∈ N := ⟨z,mem_ball_self hr,hfz⟩
          have hNU : N ⊆ U := by
            rintro y ⟨w,hw,rfl⟩
            exact hsub hw
          have heq : N \ {p} = f '' (Metric.ball z r \ {z}) := by
            ext y
            constructor
            · rintro ⟨⟨w,hw,rfl⟩,hwp⟩
              refine ⟨w,⟨hw,?_⟩,rfl⟩
              intro he
              exact hwp (mem_singleton_iff.mpr ((congrArg f (mem_singleton_iff.mp he)).trans hfz))
            · rintro ⟨w,⟨hw,hwn⟩,rfl⟩
              refine ⟨⟨w,hw,rfl⟩,?_⟩
              intro he
              exact hwn (mem_singleton_iff.mpr (hf.injective ((mem_singleton_iff.mp he).trans hfz.symm)))
          apply hlocal hU hcU hN hpN hNU
          rw [heq]
          exact (hball z r hr).image f hf.continuous.continuousOn
        · have heq : U \ {p} = U := by
            ext y
            simp only [mem_sdiff,mem_singleton_iff]
            exact ⟨And.left,fun hy => ⟨hy,fun he => hpU (he ▸ hy)⟩⟩
          exact heq.symm ▸ hcU
      intro e f g
      letI : T2Space S := M.sphere.symm.t2Space
      have hf : Topology.IsOpenEmbedding f :=
        isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
      have hDopen : IsOpen (f ⁻¹' U) := hU.preimage hf.continuous
      have hDconn : IsConnected (f ⁻¹' U) := by
        have hconn := (hpuncture hU hcU p).preimage_of_isOpenMap hf.injective hf.isOpenMap (by
          intro x hx
          exact ⟨e ⟨x,by simpa only [mem_singleton_iff] using hx.2⟩,
            congrArg Subtype.val (e.symm_apply_apply _)⟩)
        convert hconn using 1
        ext z
        simp only [mem_preimage,mem_sdiff,mem_singleton_iff]
        exact ⟨fun hz => ⟨hz,(e.symm z).property⟩,And.left⟩
      have hPa : Schoenflies.IsArcBetween (Set.range g) (g 0) (g 1) :=
        a.plane_isArcBetween p (fun hx => hp (Or.inl hx))
      let k : Interval → Schoenflies.Plane := fun t => e ⟨b t,by
        intro he; exact hp (Or.inr (he ▸ Set.mem_range_self t))⟩
      have hk : Continuous k := e.continuous.comp (Continuous.subtype_mk b.continuous _)
      have hk0 : k 0 = g 0 := by exact congrArg e (Subtype.ext hb0)
      have hk1 : k 1 = g 1 := by exact congrArg e (Subtype.ext hb1)
      have hPb : Schoenflies.IsArcBetween (Set.range k) (g 0) (g 1) := by
        let F : ℝ → Schoenflies.Plane := fun t =>
          if ht : t ∈ Set.Icc (0 : ℝ) 1 then k ⟨t,ht⟩ else k 0
        have hF (t : Interval) : F t = k t := dite_eq_left t.property
        refine ⟨F,?_,?_,?_,?_,?_⟩
        · exact continuousOn_iff_continuous_domRestrict.mpr (by
            convert hk using 1
            funext t
            exact hF t)
        · intro t ht u hu he
          have he' : k ⟨t,ht⟩ = k ⟨u,hu⟩ := (hF ⟨t,ht⟩).symm.trans (he.trans (hF ⟨u,hu⟩))
          exact congrArg Subtype.val (hbi (congrArg Subtype.val (e.injective he')))
        · ext z
          constructor
          · rintro ⟨t,ht,rfl⟩
            exact ⟨⟨t,ht⟩,(hF ⟨t,ht⟩).symm⟩
          · rintro ⟨t,rfl⟩
            exact ⟨t.val,t.property,hF t⟩
        · exact (hF 0).trans hk0
        · exact (hF 1).trans hk1
      have hmeet : Set.range k ∩ Set.range g = {g 0,g 1} := by
        apply Subset.antisymm
        · rintro z ⟨⟨t,ht⟩,⟨u,hu⟩⟩
          have he : b t = a.val.map u := congrArg Subtype.val (e.injective (ht.trans hu.symm))
          have hz : b t ∈ Set.range b ∩ a.image := ⟨mem_range_self t,he ▸ mem_range_self u⟩
          rw [hmeet] at hz
          rcases (by simpa using hz : b t = a.val.map 0 ∨ b t = a.val.map 1) with hz|hz
          · left
            exact ht.symm.trans (congrArg e (Subtype.ext hz))
          · right
            exact ht.symm.trans (congrArg e (Subtype.ext hz))
        · intro z hz
          rcases (by simpa using hz : z = g 0 ∨ z = g 1) with rfl|rfl
          · exact ⟨⟨0,hk0⟩,mem_range_self 0⟩
          · exact ⟨⟨1,hk1⟩,mem_range_self 1⟩
      have hJ : Schoenflies.IsJordanCurve (Set.range k ∪ Set.range g) :=
        Schoenflies.isJordanCurve_union hPb hPa (fun z hzk hzg => by
          have hz : z ∈ ({g 0,g 1} : Set Schoenflies.Plane) := hmeet ▸ ⟨hzk,hzg⟩
          simpa using hz)
      have h0D : g 0 ∉ f ⁻¹' U := by
        simpa [f,g,e] using h0
      have h1D : g 1 ∉ f ⁻¹' U := by
        simpa [f,g,e] using h1
      have hPD : Set.range g \ {g 0,g 1} ⊆ f ⁻¹' U := by
        rintro z ⟨⟨t,rfl⟩,hnt⟩
        change f (g t) ∈ U
        have hfg : f (g t) = a.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
        rw [hfg]
        apply hinter
        refine ⟨mem_range_self t,?_⟩
        intro he
        rcases (by simpa using he : a.val.map t = a.val.map 0 ∨ a.val.map t = a.val.map 1) with he|he
        · exact hnt (Or.inl (congrArg e (Subtype.ext he)))
        · exact hnt (Or.inr (congrArg e (Subtype.ext he)))
      have hAD : Disjoint (Set.range k) (f ⁻¹' U) := by
        apply disjoint_left.mpr
        rintro z ⟨t,rfl⟩ hz
        have hfk : f (k t) = b t := congrArg Subtype.val (e.symm_apply_apply _)
        exact disjoint_left.mp hbU (mem_range_self t) (hfk ▸ hz)
      exact htwo hDopen hDconn hPb hPa hmeet hAD h0D h1D hPD
    have hremove (M : HyperellipticModel E S) {W : Set S} (hW : IsOpen W)
        {p x y : S} (hx : x ∈ W \ {p}) (hy : y ∈ W \ {p})
        (hne : connectedComponentIn (W \ {p}) x ≠ connectedComponentIn (W \ {p}) y)
        (hcov : ∀ z ∈ W \ {p}, z ∈ connectedComponentIn (W \ {p}) x ∨
          z ∈ connectedComponentIn (W \ {p}) y) :
        connectedComponentIn W x ≠ connectedComponentIn W y ∧
          ∀ z ∈ W, z ∈ connectedComponentIn W x ∨ z ∈ connectedComponentIn W y := by
      have hpuncture : ∀ {U : Set S}, IsOpen U → IsConnected U → ∀ p : S,
          IsConnected (U \ {p}) := by
        intro U hU hcU p
        letI : T2Space S := M.sphere.symm.t2Space
        letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
        have hlocal : ∀ {U N : Set S} {p : S}, IsOpen U → IsConnected U →
            IsOpen N → p ∈ N → N ⊆ U → IsConnected (N \ {p}) → IsConnected (U \ {p}) := by
          intro U N p hU hcU hN hpN hNU hcN
          obtain ⟨x,hx⟩ := hcN.nonempty
          let C := connectedComponentIn (U \ {p}) x
          have hxU : x ∈ U \ {p} := ⟨hNU hx.1,hx.2⟩
          have hcC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxU
          have hNC : N \ {p} ⊆ C := hcN.isPreconnected.subset_connectedComponentIn hx
            (fun y hy => ⟨hNU hy.1,hy.2⟩)
          have hCsub : C ⊆ U \ {p} := connectedComponentIn_subset _ _
          have hcomp : IsComplementComponent (Uᶜ ∪ {p}) C := by
            apply complementComponent_iff_componentIn.mpr
            refine ⟨x,?_,?_⟩
            · simpa only [mem_compl_iff,mem_union,not_or,not_not,mem_sdiff] using hxU
            · change connectedComponentIn (U \ {p}) x = _
              congr 1
              ext y
              simp [and_comm]
          have hclosed : IsClosed (Uᶜ ∪ {p}) := hU.isClosed_compl.union isClosed_singleton
          have hCopen : IsOpen C := complementComponent_open hclosed hcomp
          have heq : C ∪ {p} = C ∪ N := by
            ext y
            constructor
            · rintro (hy|hy)
              · exact Or.inl hy
              · exact Or.inr ((mem_singleton_iff.mp hy) ▸ hpN)
            · rintro (hy|hy)
              · exact Or.inl hy
              · by_cases hyp : y = p
                · exact Or.inr (mem_singleton_iff.mpr hyp)
                · exact Or.inl (hNC ⟨hy,hyp⟩)
          have hopen : IsOpen (C ∪ {p}) := heq ▸ hCopen.union hN
          have hfront : frontier C ⊆ Uᶜ ∪ {p} := complementComponent_frontier_subset hclosed hcomp
          have hall : U ⊆ C ∪ {p} := hcU.isPreconnected.subset_of_closure_inter_subset hopen
            ⟨x,hxU.1,Or.inl (mem_connectedComponentIn hxU)⟩ (by
              rintro y ⟨hy,hyU⟩
              rw [closure_union,isClosed_singleton.closure_eq] at hy
              rcases hy with hy|hy
              · by_cases hyC : y ∈ C
                · exact Or.inl hyC
                · have hf : y ∈ frontier C := by
                    rw [frontier,hCopen.interior_eq]
                    exact ⟨hy,hyC⟩
                  rcases hfront hf with hn|hp
                  · exact False.elim (hn hyU)
                  · exact Or.inr hp
              · exact Or.inr hy)
          have he : U \ {p} = C := by
            apply Subset.antisymm
            · intro y hy
              exact (hall hy.1).resolve_right hy.2
            · exact hCsub
          exact he.symm ▸ hcC
        have hball : ∀ z : Schoenflies.Plane, ∀ r : ℝ, 0 < r →
            IsConnected (Metric.ball z r \ {z}) := by
          intro z r hr
          let F := OpenPartialHomeomorph.univBall z r
          have hsource : F.source = Set.univ := OpenPartialHomeomorph.univBall_source z r
          have htarget : F.target = Metric.ball z r := OpenPartialHomeomorph.univBall_target z hr
          have hF : Continuous F := OpenPartialHomeomorph.continuous_univBall z r
          have hzero : F 0 = z := OpenPartialHomeomorph.univBall_apply_zero z r
          have hi : F '' ({0} : Set Schoenflies.Plane)ᶜ = Metric.ball z r \ {z} := by
            ext y
            constructor
            · rintro ⟨x,hx,rfl⟩
              refine ⟨?_,?_⟩
              · rw [← htarget]; exact F.map_source (hsource ▸ Set.mem_univ x)
              · intro he
                have hx0 : x = 0 := F.injOn (hsource ▸ Set.mem_univ x)
                  (hsource ▸ Set.mem_univ 0) ((Set.mem_singleton_iff.mp he).trans hzero.symm)
                exact hx (Set.mem_singleton_iff.mpr hx0)
            · rintro ⟨hy,hyn⟩
              have hyt : y ∈ F.target := htarget ▸ hy
              refine ⟨F.symm y,?_,F.right_inv hyt⟩
              intro he
              have hyz : y = z := (F.right_inv hyt).symm.trans
                ((congrArg F (Set.mem_singleton_iff.mp he)).trans hzero)
              exact hyn (Set.mem_singleton_iff.mpr hyz)
          rw [← hi]
          exact (isConnected_compl_singleton_of_one_lt_rank
            (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ Schoenflies.Plane) 0).image F hF.continuousOn
        by_cases hpU : p ∈ U
        · obtain ⟨q,hq⟩ : ∃ q : S, q ≠ p := by
            classical
            by_contra h
            push_neg at h
            have hs : M.cover.branch ⊆ {p} := by
              intro q hq
              exact Finset.mem_singleton.mpr (h q)
            have hc := Finset.card_le_card hs
            rw [M.cover.branch_card,Finset.card_singleton] at hc
            omega
          let e := M.puncturedPlane q
          let f : Schoenflies.Plane → S := fun z => (e.symm z).val
          let z := e ⟨p,Ne.symm hq⟩
          have hf : Topology.IsOpenEmbedding f :=
            isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
          have hfz : f z = p := congrArg Subtype.val (e.symm_apply_apply _)
          have hD : IsOpen (f ⁻¹' U) := hU.preimage hf.continuous
          obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hD z (by simpa [hfz] using hpU)
          let N := f '' Metric.ball z r
          have hN : IsOpen N := hf.isOpenMap _ isOpen_ball
          have hpN : p ∈ N := ⟨z,mem_ball_self hr,hfz⟩
          have hNU : N ⊆ U := by
            rintro y ⟨w,hw,rfl⟩
            exact hsub hw
          have heq : N \ {p} = f '' (Metric.ball z r \ {z}) := by
            ext y
            constructor
            · rintro ⟨⟨w,hw,rfl⟩,hwp⟩
              refine ⟨w,⟨hw,?_⟩,rfl⟩
              intro he
              exact hwp (mem_singleton_iff.mpr ((congrArg f (mem_singleton_iff.mp he)).trans hfz))
            · rintro ⟨w,⟨hw,hwn⟩,rfl⟩
              refine ⟨⟨w,hw,rfl⟩,?_⟩
              intro he
              exact hwn (mem_singleton_iff.mpr (hf.injective ((mem_singleton_iff.mp he).trans hfz.symm)))
          apply hlocal hU hcU hN hpN hNU
          rw [heq]
          exact (hball z r hr).image f hf.continuous.continuousOn
        · have heq : U \ {p} = U := by
            ext y
            simp only [mem_sdiff,mem_singleton_iff]
            exact ⟨And.left,fun hy => ⟨hy,fun he => hpU (he ▸ hy)⟩⟩
          exact heq.symm ▸ hcU
      letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
      have hcomp : ∀ t ∈ W \ {p}, connectedComponentIn (W \ {p}) t =
          connectedComponentIn W t \ {p} := by
        intro t ht
        have hc : IsConnected (connectedComponentIn W t \ {p}) :=
          hpuncture hW.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr ht.1) p
        apply Subset.antisymm
        · intro z hz
          exact ⟨connectedComponentIn_mono t sdiff_subset hz,(connectedComponentIn_subset _ _ hz).2⟩
        · exact hc.isPreconnected.subset_connectedComponentIn
            ⟨mem_connectedComponentIn ht.1,ht.2⟩
            (fun z hz => ⟨connectedComponentIn_subset _ _ hz.1,hz.2⟩)
      refine ⟨?_,?_⟩
      · intro he
        apply hne
        rw [hcomp x hx,hcomp y hy,he]
      · intro z hz
        by_cases hzp : z = p
        · have hc : IsConnected (connectedComponentIn W z \ {p}) :=
            hpuncture hW.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hz) p
          obtain ⟨t,ht⟩ := hc.nonempty
          have htW : t ∈ W \ {p} := ⟨connectedComponentIn_subset _ _ ht.1,ht.2⟩
          rcases hcov t htW with htX|htY
          · left
            have htx : t ∈ connectedComponentIn W x := connectedComponentIn_mono x sdiff_subset htX
            rw [(connectedComponentIn_eq htx).trans (connectedComponentIn_eq ht.1).symm]
            exact mem_connectedComponentIn hz
          · right
            have hty : t ∈ connectedComponentIn W y := connectedComponentIn_mono y sdiff_subset htY
            rw [(connectedComponentIn_eq hty).trans (connectedComponentIn_eq ht.1).symm]
            exact mem_connectedComponentIn hz
        · rcases hcov z ⟨hz,hzp⟩ with hx|hy
          · exact Or.inl (connectedComponentIn_mono x sdiff_subset hx)
          · exact Or.inr (connectedComponentIn_mono y sdiff_subset hy)
    have hmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
        (f : X → Y) (hf : Topology.IsOpenEmbedding f) {W : Set Y}
        (hW : W ⊆ Set.range f) {x : X} (hx : f x ∈ W) :
        f '' connectedComponentIn (f ⁻¹' W) x = connectedComponentIn W (f x) := by
      apply Subset.antisymm
      · exact (hf.continuous.continuousOn.image_connectedComponentIn_subset
          (show x ∈ f ⁻¹' W from hx)).trans
          (connectedComponentIn_mono (f x) (image_preimage_subset f W))
      · have hc : IsConnected (f ⁻¹' connectedComponentIn W (f x)) :=
          (isConnected_connectedComponentIn_iff.mpr hx).preimage_of_isOpenMap
            hf.injective hf.isOpenMap ((connectedComponentIn_subset _ _).trans hW)
        have hsub : f ⁻¹' connectedComponentIn W (f x) ⊆ connectedComponentIn (f ⁻¹' W) x :=
          hc.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hx)
            (fun t ht => connectedComponentIn_subset W (f x) ht)
        intro y hy
        obtain ⟨z,hz⟩ := hW (connectedComponentIn_subset _ _ hy)
        refine ⟨z,hsub ?_,hz⟩
        change f z ∈ connectedComponentIn W (f x)
        rw [hz]
        exact hy
    letI : T2Space S := M.sphere.symm.t2Space
    let e := M.puncturedPlane p
    let f : Plane → S := fun z => (e.symm z).val
    let g : Interval → Plane := fun t => e ⟨a.val.map t,by
      intro he; exact hp (Or.inl (he ▸ mem_range_self t))⟩
    let W := U \ a.image
    let V := W \ {p}
    have hf : Topology.IsOpenEmbedding f :=
      isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
    have hWopen : IsOpen W := hU.sdiff (markedArc_image_compact a.val).isClosed
    have hfg : ∀ t, f (g t) = a.val.map t := fun t =>
      congrArg Subtype.val (e.symm_apply_apply _)
    have hpre : f ⁻¹' V = f ⁻¹' U \ Set.range g := by
      ext z
      have heq : f z ∈ a.image ↔ z ∈ Set.range g := by
        constructor
        · rintro ⟨t,ht⟩
          refine ⟨t,hf.injective ?_⟩
          exact (hfg t).trans ht
        · rintro ⟨t,rfl⟩
          rw [hfg]
          exact mem_range_self t
      change (f z ∈ U ∧ f z ∉ a.image) ∧ f z ∉ ({p} : Set S) ↔
        f z ∈ U ∧ z ∉ Set.range g
      simp only [mem_singleton_iff]
      exact ⟨fun hz => ⟨hz.1.1,fun hg => hz.1.2 (heq.mpr hg)⟩,
        fun hz => ⟨⟨hz.1,fun ha => hz.2 (heq.mp ha)⟩,(e.symm z).property⟩⟩
    have hVrange : V ⊆ Set.range f := by
      intro z hz
      exact ⟨e ⟨z,by simpa only [mem_singleton_iff] using hz.2⟩,
        congrArg Subtype.val (e.symm_apply_apply _)⟩
    obtain ⟨x,hx,y,hy,hne,hcov⟩ := hplane M a b hbi hb0 hb1 hmeet hbU hU hcU h0 h1 hinter p hp
    have hxV : f x ∈ V := by change x ∈ f ⁻¹' V; rw [hpre]; exact hx
    have hyV : f y ∈ V := by change y ∈ f ⁻¹' V; rw [hpre]; exact hy
    have hmx := hmap f hf hVrange hxV
    have hmy := hmap f hf hVrange hyV
    rw [hpre] at hmx hmy
    have hneV : connectedComponentIn V (f x) ≠ connectedComponentIn V (f y) := by
      intro he
      apply hne
      apply hf.injective.image_injective
      exact hmx.trans (he.trans hmy.symm)
    have hcovV : ∀ z ∈ V, z ∈ connectedComponentIn V (f x) ∨ z ∈ connectedComponentIn V (f y) := by
      intro z hz
      obtain ⟨t,ht⟩ := hVrange hz
      have htD : t ∈ f ⁻¹' U \ Set.range g := by
        rw [← hpre]
        change f t ∈ V
        rw [ht]
        exact hz
      rcases hcov t htD with htX|htY
      · left
        rw [← hmx]
        exact ⟨t,htX,ht⟩
      · right
        rw [← hmy]
        exact ⟨t,htY,ht⟩
    obtain ⟨hneW,hcovW⟩ := hremove M hWopen hxV hyV hneV hcovV
    exact ⟨f x,hxV.1,f y,hyV.1,hneW,hcovW⟩
  classical
  let n : NonLoopArc M := ⟨a.val,haNL⟩
  obtain ⟨U,hU,hinc,hint,hcl,hfr0,hfr1⟩ := hplace M r a ha h0 h1
  obtain ⟨b,c,hbi,hb0,hb1,hbG,hcimg⟩ := hcycle M r hd n ha h0 h1 hc
  obtain ⟨p,hp⟩ := hoff M c
  have hpunct : p ∉ n.image ∪ Set.range b := by
    change p ∉ a.val.image ∪ Set.range b
    rw [← hcimg]
    exact hp
  have hopen := (actualFamily_face_open_frontier M (fun v => (r v).val) hU).1
  have hbU : Disjoint (Set.range b) U := disjoint_left.mpr (fun z hz hzU => hU.2.2.1 hzU (hbG hz))
  have hmeet : Set.range b ∩ n.image = {n.val.map 0,n.val.map 1} := by
    apply Subset.antisymm
    · rintro z ⟨hzB,⟨t,ht⟩⟩
      have hzG := hbG hzB
      have hzmark : z ∈ M.cover.branch := by
        by_contra hn
        obtain ⟨v,hv⟩ := mem_iUnion.mp hzG
        exact disjoint_left.mp (ha v) ⟨⟨t,ht⟩,hn⟩ ⟨hv,hn⟩
      have htmark : a.val.map t ∈ M.cover.branch := ht.symm ▸ hzmark
      rcases a.val.marked_only_at_ends t htmark with ht0|ht1
      · left; exact ht.symm.trans (congrArg a.val.map ht0)
      · right; exact ht.symm.trans (congrArg a.val.map ht1)
    · intro z hz
      rcases (by simpa using hz : z = n.val.map 0 ∨ z = n.val.map 1) with rfl|rfl
      · exact ⟨⟨0,hb0⟩,mem_range_self 0⟩
      · exact ⟨⟨1,hb1⟩,mem_range_self 1⟩
  have h0U : n.val.map 0 ∉ U := fun h => hU.2.2.1 h h0
  have h1U : n.val.map 1 ∉ U := fun h => hU.2.2.1 h h1
  have hPU : n.image \ {n.val.map 0,n.val.map 1} ⊆ U := by
    rintro z ⟨⟨t,ht⟩,hz⟩
    apply hint
    refine ⟨⟨t,ht⟩,?_⟩
    intro hmark
    have htmark : a.val.map t ∈ M.cover.branch := ht.symm ▸ hmark
    rcases a.val.marked_only_at_ends t htmark with ht0|ht1
    · exact hz (Or.inl (ht.symm.trans (congrArg a.val.map ht0)))
    · exact hz (Or.inr (ht.symm.trans (congrArg a.val.map ht1)))
  obtain ⟨x,hx,y,hy,hne,hcov⟩ := hsplit M n b hbi hb0 hb1 hmeet hbU hopen hU.2.1 h0U h1U hPU p hpunct
  change x ∈ U \ a.val.image at hx
  change y ∈ U \ a.val.image at hy
  let A := connectedComponentIn (U \ a.val.image) x
  let B := connectedComponentIn (U \ a.val.image) y
  have he : (Uᶜ ∪ a.val.image)ᶜ = U \ a.val.image := by ext z; simp
  have hA : IsComplementComponent (Uᶜ ∪ a.val.image) A :=
    complementComponent_iff_componentIn.mpr ⟨x,by simpa [he] using hx,by rw [he]⟩
  have hB : IsComplementComponent (Uᶜ ∪ a.val.image) B :=
    complementComponent_iff_componentIn.mpr ⟨y,by simpa [he] using hy,by rw [he]⟩
  refine ⟨U,hU,hinc,hint,{A,B},Finset.card_pair hne,?_⟩
  intro V
  constructor
  · intro hV
    obtain ⟨z,hz⟩ := hV.1
    have hzcut : z ∈ U \ a.val.image := by rw [← he]; exact hV.2.2.1 hz
    rcases hcov z hzcut with hzA|hzB
    · have heq : V = A := by
        by_contra hne
        exact disjoint_left.mp (complementComponents_disjoint hV hA hne) hz hzA
      simp [heq]
    · have heq : V = B := by
        by_contra hne
        exact disjoint_left.mp (complementComponents_disjoint hV hB hne) hz hzB
      simp [heq]
  · intro hV
    rcases Finset.mem_insert.mp hV with hV|hV
    · exact hV ▸ hA
    · exact (Finset.mem_singleton.mp hV) ▸ hB

/-- Concrete geometric per-edge bound: every full-graph face touching the
interior of this nonloop cycle edge belongs to a constructed two-element
family. No incidence, ownership, or side bound is assumed. -/
theorem actual_nonloop_cycle_edge_incident_faces_atMostTwo
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (a : EssentialMarkedArc M) (haNL : a.val.map 0 ≠ a.val.map 1)
    (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
    (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
    (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
    (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, IsComplementComponent ((⋃ v, (r v).val.image) ∪ a.val.image) V →
        (frontier V ∩ arcInterior M a).Nonempty → V ∈ F := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨U,hU,_,hint,F,hcard,hF⟩ :=
    actual_nonloop_cycle_edge_split_faces M r hd a haNL ha h0 h1 hc
  have hopen : IsOpen U := complementComponent_open
    (markedFamily_graph_compact (fun v => (r v).val)).isClosed hU
  let G := ⋃ v, (r v).val.image
  have hGU : G ⊆ Uᶜ := fun x hx hxU => hU.2.2.1 hxU hx
  refine ⟨F,hcard,?_⟩
  intro V hV htouch
  obtain ⟨z,hzfr,hza⟩ := htouch
  have hmeet : (U ∩ V).Nonempty := Set.Nonempty.of_closure
    ⟨z,hopen.inter_closure ⟨hint hza,frontier_subset_closure hzfr⟩⟩
  obtain ⟨x,hxU,hxV⟩ := hmeet
  have hVG : V ⊆ Gᶜ := fun y hy hG => hV.2.2.1 hy (Or.inl hG)
  have hVC : V ⊆ connectedComponentIn Gᶜ x :=
    hV.2.1.isPreconnected.subset_connectedComponentIn hxV hVG
  have hUC : U = connectedComponentIn Gᶜ x := by
    obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hU
    rw [he]
    exact connectedComponentIn_eq (he ▸ hxU)
  have hVU : V ⊆ U := hUC.symm ▸ hVC
  have hlocal : IsComplementComponent (Uᶜ ∪ a.val.image) V := by
    refine ⟨hV.1,hV.2.1,?_,?_⟩
    · intro y hy h
      rcases h with hn | ha
      · exact hn (hVU hy)
      · exact hV.2.2.1 hy (Or.inr ha)
    · intro T hT hVT hTL
      have hTH : T ⊆ (G ∪ a.val.image)ᶜ := by
        intro y hy h
        rcases h with hG | ha
        · exact hTL hy (Or.inl (hGU hG))
        · exact hTL hy (Or.inr ha)
      exact hV.2.2.2 T hT hVT hTH
  exact (hF V).1 hlocal


noncomputable local instance edgeIncidenceClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- Actual per-edge incidence producer for every nonloop member of an all-bad
family. The required closing path is recovered from its actual parallel
companion after deleting the selected edge; no cycle or side certificate is
assumed. -/
theorem actual_bad_nonloop_edge_incident_faces_atMostTwo
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) σ = σ)
    (u : {v // v ∈ σ}) (hNL : (r u).val.map 0 ≠ (r u).val.map 1) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, IsComplementComponent (⋃ v, (r v).val.image) V →
        (frontier V ∩ arcInterior M (r u)).Nonempty → V ∈ F := by
  classical
  have hUn : ¬ (actualArcLabels M).isLoop u.val := by
    intro hl
    have hc : (markedArcEndset (r u).val).card = 1 := by
      rw [markedArcEndset_eq_classEndpoints,hr]
      exact hl
    have hc2 : (markedArcEndset (r u).val).card = 2 := Finset.card_pair hNL
    omega
  have hu : u.val ∈ CurveGenusTwo.Filtration.badVertices (actualArcLabels M) σ :=
    hbad.symm ▸ u.property
  simp only [CurveGenusTwo.Filtration.badVertices,Finset.mem_filter] at hu
  rcases hu.2 with hl | ⟨w,hw,hwu,_,_,he⟩
  · exact False.elim (hUn hl)
  · let z : {v // v ∈ σ} := ⟨w,hw⟩
    have hzu : z ≠ u := fun h => hwu (congrArg Subtype.val h)
    have hends : markedArcEndset (r u).val = markedArcEndset (r z).val := by
      rw [markedArcEndset_eq_classEndpoints,markedArcEndset_eq_classEndpoints,hr,hr]
      exact he.symm
    let rr : {v : {v // v ∈ σ} // v ≠ u} → EssentialMarkedArc M := fun v => r v.val
    let G := ⋃ v, (rr v).val.image
    have h0z : (r u).val.map 0 ∈ (r z).val.image := by
      have hh : (r u).val.map 0 ∈ (markedArcEndset (r z).val : Set S) := by
        rw [← hends]; simp [markedArcEndset]
      rw [← markedArc_image_inter_branch] at hh
      exact hh.1
    have h1z : (r u).val.map 1 ∈ (r z).val.image := by
      have hh : (r u).val.map 1 ∈ (markedArcEndset (r z).val : Set S) := by
        rw [← hends]; simp [markedArcEndset]
      rw [← markedArc_image_inter_branch] at hh
      exact hh.1
    have hzsub : (r z).val.image ⊆ G := fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨z,hzu⟩,hx⟩
    have h0 : (r u).val.map 0 ∈ G := hzsub h0z
    have h1 : (r u).val.map 1 ∈ G := hzsub h1z
    have hc : (r u).val.map 1 ∈ connectedComponentIn G ((r u).val.map 0) :=
      (markedArc_image_connected (r z).val).isPreconnected.subset_connectedComponentIn
        h0z hzsub h1z
    have hdr : ∀ v w, v ≠ w → Disjoint (arcInterior M (rr v)) (arcInterior M (rr w)) := by
      intro v w hvw
      exact hd v.val w.val (fun he => hvw (Subtype.ext he))
    have ha : ∀ v, Disjoint (arcInterior M (r u)) (arcInterior M (rr v)) := by
      intro v
      exact hd u v.val v.property.symm
    obtain ⟨F,hcard,hF⟩ := actual_nonloop_cycle_edge_incident_faces_atMostTwo
      M rr hdr (r u) hNL ha h0 h1 hc
    have hgraph : (⋃ v, (r v).val.image) = G ∪ (r u).val.image := by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
        by_cases hvu : v = u
        · exact Or.inr (hvu ▸ hv)
        · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v,hvu⟩,hv⟩)
      · rintro (hx | hx)
        · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨v.val,hv⟩
        · exact Set.mem_iUnion.mpr ⟨u,hx⟩
    refine ⟨F,hcard,?_⟩
    intro V hV htouch
    apply hF V ?_ htouch
    change IsComplementComponent (G ∪ (r u).val.image) V
    rw [← hgraph]
    exact hV


open scoped Classical

/-- Concrete finite counting form of the geometric nonloop-edge producer.
Faces are filtered by actual frontier contact with the actual arc interior;
no external incidence count is supplied. -/
theorem actual_bad_nonloop_edge_face_count_le_two
    (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) σ = σ)
    (u : {v // v ∈ σ}) (hNL : (r u).val.map 0 ≠ (r u).val.map 1)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V) :
    (F.filter (fun V => (frontier V ∩ arcInterior M (r u)).Nonempty)).card ≤ 2 := by
  classical
  obtain ⟨T,hcard,hT⟩ := actual_bad_nonloop_edge_incident_faces_atMostTwo M r hr hd hbad u hNL
  have hsub : F.filter (fun V => (frontier V ∩ arcInterior M (r u)).Nonempty) ⊆ T := by
    intro V hV
    obtain ⟨hVF,htouch⟩ := Finset.mem_filter.mp hV
    exact hT V (hF V hVF) htouch
  exact (Finset.card_le_card hsub).trans_eq hcard

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_nonloop_cycle_edge_split_faces

#print axioms CurveComplex.HyperellipticModel.actual_nonloop_cycle_edge_incident_faces_atMostTwo

#print axioms CurveComplex.HyperellipticModel.actual_bad_nonloop_edge_incident_faces_atMostTwo

#print axioms CurveComplex.HyperellipticModel.actual_bad_nonloop_edge_face_count_le_two
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance : DecidableEq S := Classical.decEq _
set_option maxHeartbeats 2800000
/-- The source proof's concrete connected open sphere domain puncture lemma. -/
theorem actual_open_puncture_connected (M : HyperellipticModel E S) :
    ∀ {U : Set S}, IsOpen U → IsConnected U → ∀ p : S, IsConnected (U \ {p}) := by
  intro U hU hcU p
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hlocal : ∀ {U N : Set S} {p : S}, IsOpen U → IsConnected U →
      IsOpen N → p ∈ N → N ⊆ U → IsConnected (N \ {p}) → IsConnected (U \ {p}) := by
    intro U N p hU hcU hN hpN hNU hcN
    obtain ⟨x,hx⟩ := hcN.nonempty
    let C := connectedComponentIn (U \ {p}) x
    have hxU : x ∈ U \ {p} := ⟨hNU hx.1,hx.2⟩
    have hcC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxU
    have hNC : N \ {p} ⊆ C := hcN.isPreconnected.subset_connectedComponentIn hx
      (fun y hy => ⟨hNU hy.1,hy.2⟩)
    have hCsub : C ⊆ U \ {p} := connectedComponentIn_subset _ _
    have hcomp : IsComplementComponent (Uᶜ ∪ {p}) C := by
      apply complementComponent_iff_componentIn.mpr
      refine ⟨x,?_,?_⟩
      · simpa only [mem_compl_iff,mem_union,not_or,not_not,mem_sdiff] using hxU
      · change connectedComponentIn (U \ {p}) x = _
        congr 1
        ext y
        simp [and_comm]
    have hclosed : IsClosed (Uᶜ ∪ {p}) := hU.isClosed_compl.union isClosed_singleton
    have hCopen : IsOpen C := complementComponent_open hclosed hcomp
    have heq : C ∪ {p} = C ∪ N := by
      ext y
      constructor
      · rintro (hy|hy)
        · exact Or.inl hy
        · exact Or.inr ((mem_singleton_iff.mp hy) ▸ hpN)
      · rintro (hy|hy)
        · exact Or.inl hy
        · by_cases hyp : y = p
          · exact Or.inr (mem_singleton_iff.mpr hyp)
          · exact Or.inl (hNC ⟨hy,hyp⟩)
    have hopen : IsOpen (C ∪ {p}) := heq ▸ hCopen.union hN
    have hfront : frontier C ⊆ Uᶜ ∪ {p} := complementComponent_frontier_subset hclosed hcomp
    have hall : U ⊆ C ∪ {p} := hcU.isPreconnected.subset_of_closure_inter_subset hopen
      ⟨x,hxU.1,Or.inl (mem_connectedComponentIn hxU)⟩ (by
        rintro y ⟨hy,hyU⟩
        rw [closure_union,isClosed_singleton.closure_eq] at hy
        rcases hy with hy|hy
        · by_cases hyC : y ∈ C
          · exact Or.inl hyC
          · have hf : y ∈ frontier C := by
              rw [frontier,hCopen.interior_eq]
              exact ⟨hy,hyC⟩
            rcases hfront hf with hn|hp
            · exact False.elim (hn hyU)
            · exact Or.inr hp
        · exact Or.inr hy)
    have he : U \ {p} = C := by
      apply Subset.antisymm
      · intro y hy
        exact (hall hy.1).resolve_right hy.2
      · exact hCsub
    exact he.symm ▸ hcC
  have hball : ∀ z : Schoenflies.Plane, ∀ r : ℝ, 0 < r →
      IsConnected (Metric.ball z r \ {z}) := by
    intro z r hr
    let F := OpenPartialHomeomorph.univBall z r
    have hsource : F.source = Set.univ := OpenPartialHomeomorph.univBall_source z r
    have htarget : F.target = Metric.ball z r := OpenPartialHomeomorph.univBall_target z hr
    have hF : Continuous F := OpenPartialHomeomorph.continuous_univBall z r
    have hzero : F 0 = z := OpenPartialHomeomorph.univBall_apply_zero z r
    have hi : F '' ({0} : Set Schoenflies.Plane)ᶜ = Metric.ball z r \ {z} := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨?_,?_⟩
        · rw [← htarget]; exact F.map_source (hsource ▸ Set.mem_univ x)
        · intro he
          have hx0 : x = 0 := F.injOn (hsource ▸ Set.mem_univ x)
            (hsource ▸ Set.mem_univ 0) ((Set.mem_singleton_iff.mp he).trans hzero.symm)
          exact hx (Set.mem_singleton_iff.mpr hx0)
      · rintro ⟨hy,hyn⟩
        have hyt : y ∈ F.target := htarget ▸ hy
        refine ⟨F.symm y,?_,F.right_inv hyt⟩
        intro he
        have hyz : y = z := (F.right_inv hyt).symm.trans
          ((congrArg F (Set.mem_singleton_iff.mp he)).trans hzero)
        exact hyn (Set.mem_singleton_iff.mpr hyz)
    rw [← hi]
    exact (isConnected_compl_singleton_of_one_lt_rank
      (by rw [← Module.finrank_eq_rank]; norm_num : 1 < Module.rank ℝ Schoenflies.Plane) 0).image F hF.continuousOn
  by_cases hpU : p ∈ U
  · obtain ⟨q,hq⟩ : ∃ q : S, q ≠ p := by
      classical
      by_contra h
      push_neg at h
      have hs : M.cover.branch ⊆ {p} := by
        intro q hq
        exact Finset.mem_singleton.mpr (h q)
      have hc := Finset.card_le_card hs
      rw [M.cover.branch_card,Finset.card_singleton] at hc
      omega
    let e := M.puncturedPlane q
    let f : Schoenflies.Plane → S := fun z => (e.symm z).val
    let z := e ⟨p,Ne.symm hq⟩
    have hf : Topology.IsOpenEmbedding f :=
      isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
    have hfz : f z = p := congrArg Subtype.val (e.symm_apply_apply _)
    have hD : IsOpen (f ⁻¹' U) := hU.preimage hf.continuous
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hD z (by simpa [hfz] using hpU)
    let N := f '' Metric.ball z r
    have hN : IsOpen N := hf.isOpenMap _ isOpen_ball
    have hpN : p ∈ N := ⟨z,mem_ball_self hr,hfz⟩
    have hNU : N ⊆ U := by
      rintro y ⟨w,hw,rfl⟩
      exact hsub hw
    have heq : N \ {p} = f '' (Metric.ball z r \ {z}) := by
      ext y
      constructor
      · rintro ⟨⟨w,hw,rfl⟩,hwp⟩
        refine ⟨w,⟨hw,?_⟩,rfl⟩
        intro he
        exact hwp (mem_singleton_iff.mpr ((congrArg f (mem_singleton_iff.mp he)).trans hfz))
      · rintro ⟨w,⟨hw,hwn⟩,rfl⟩
        refine ⟨⟨w,hw,rfl⟩,?_⟩
        intro he
        exact hwn (mem_singleton_iff.mpr (hf.injective ((mem_singleton_iff.mp he).trans hfz.symm)))
    apply hlocal hU hcU hN hpN hNU
    rw [heq]
    exact (hball z r hr).image f hf.continuous.continuousOn
  · have heq : U \ {p} = U := by
      ext y
      simp only [mem_sdiff,mem_singleton_iff]
      exact ⟨And.left,fun hy => ⟨hy,fun he => hpU (he ▸ hy)⟩⟩
    exact heq.symm ▸ hcU
/-- Restore the puncture without changing an actual open domain's two
components. The point-removal argument is extracted from the source proof. -/
theorem actual_component_coverage_restore_puncture
    (M : HyperellipticModel E S) {W : Set S} (hW : IsOpen W)
    {p x y : S} (hx : x ∈ W \ {p}) (hy : y ∈ W \ {p})
    (hne : connectedComponentIn (W \ {p}) x ≠ connectedComponentIn (W \ {p}) y)
    (hcov : ∀ z ∈ W \ {p}, z ∈ connectedComponentIn (W \ {p}) x ∨
      z ∈ connectedComponentIn (W \ {p}) y) :
    connectedComponentIn W x ≠ connectedComponentIn W y ∧
      ∀ z ∈ W, z ∈ connectedComponentIn W x ∨ z ∈ connectedComponentIn W y := by
  letI : T2Space S := M.sphere.symm.t2Space
  have hpuncture : ∀ {U : Set S}, IsOpen U → IsConnected U → ∀ p : S,
      IsConnected (U \ {p}) := actual_open_puncture_connected M
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hcomp : ∀ t ∈ W \ {p}, connectedComponentIn (W \ {p}) t =
      connectedComponentIn W t \ {p} := by
    intro t ht
    have hc : IsConnected (connectedComponentIn W t \ {p}) :=
      hpuncture hW.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr ht.1) p
    apply Subset.antisymm
    · intro z hz
      exact ⟨connectedComponentIn_mono t sdiff_subset hz,(connectedComponentIn_subset _ _ hz).2⟩
    · exact hc.isPreconnected.subset_connectedComponentIn
        ⟨mem_connectedComponentIn ht.1,ht.2⟩
        (fun z hz => ⟨connectedComponentIn_subset _ _ hz.1,hz.2⟩)
  refine ⟨?_,?_⟩
  · intro he
    apply hne
    rw [hcomp x hx,hcomp y hy,he]
  · intro z hz
    by_cases hzp : z = p
    · have hc : IsConnected (connectedComponentIn W z \ {p}) :=
        hpuncture hW.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hz) p
      obtain ⟨t,ht⟩ := hc.nonempty
      have htW : t ∈ W \ {p} := ⟨connectedComponentIn_subset _ _ ht.1,ht.2⟩
      rcases hcov t htW with htX|htY
      · left
        have htx : t ∈ connectedComponentIn W x := connectedComponentIn_mono x sdiff_subset htX
        rw [(connectedComponentIn_eq htx).trans (connectedComponentIn_eq ht.1).symm]
        exact mem_connectedComponentIn hz
      · right
        have hty : t ∈ connectedComponentIn W y := connectedComponentIn_mono y sdiff_subset htY
        rw [(connectedComponentIn_eq hty).trans (connectedComponentIn_eq ht.1).symm]
        exact mem_connectedComponentIn hz
    · rcases hcov z ⟨hz,hzp⟩ with hx|hy
      · exact Or.inl (connectedComponentIn_mono x sdiff_subset hx)
      · exact Or.inr (connectedComponentIn_mono y sdiff_subset hy)

/-- Exact connected-component transport by the actual open plane embedding. -/
theorem actual_open_embedding_component_transport
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsOpenEmbedding f) {W : Set Y}
    (hW : W ⊆ Set.range f) {x : X} (hx : f x ∈ W) :
    f '' connectedComponentIn (f ⁻¹' W) x = connectedComponentIn W (f x) := by
  apply Subset.antisymm
  · exact (hf.continuous.continuousOn.image_connectedComponentIn_subset
      (show x ∈ f ⁻¹' W from hx)).trans
      (connectedComponentIn_mono (f x) (image_preimage_subset f W))
  · have hc : IsConnected (f ⁻¹' connectedComponentIn W (f x)) :=
      (isConnected_connectedComponentIn_iff.mpr hx).preimage_of_isOpenMap
        hf.injective hf.isOpenMap ((connectedComponentIn_subset _ _).trans hW)
    have hsub : f ⁻¹' connectedComponentIn W (f x) ⊆ connectedComponentIn (f ⁻¹' W) x :=
      hc.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hx)
        (fun t ht => connectedComponentIn_subset W (f x) ht)
    intro y hy
    obtain ⟨z,hz⟩ := hW (connectedComponentIn_subset _ _ hy)
    refine ⟨z,hsub ?_,hz⟩
    change f z ∈ connectedComponentIn W (f x)
    rw [hz]
    exact hy
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_open_puncture_connected
#print axioms CurveComplex.HyperellipticModel.actual_component_coverage_restore_puncture
#print axioms CurveComplex.HyperellipticModel.actual_open_embedding_component_transport
open Set Metric unitInterval
namespace Schoenflies
set_option maxHeartbeats 2800000

/-- Construct a collar of any compact middle segment of an actual Jordan
loop, relative to the WHOLE loop. The prescribed open domain contains the
loop away from its basepoint. No collar certificate is an input. -/
theorem loop_middle_has_actual_collar
    {f : ℝ → Plane} (hf : IsLoop f) {D : Set Plane} (hD : IsOpen D)
    (hinter : f '' Ioo 0 1 ⊆ D)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    Nonempty (ArcCollar D (f '' I) (f '' Icc s t)) := by
  let s₀ := s / 2
  let t₀ := (t + 1) / 2
  have hs₀ : 0 < s₀ := by dsimp [s₀]; linarith
  have hss : s₀ < s := by dsimp [s₀]; linarith
  have htt : t < t₀ := by dsimp [t₀]; linarith
  have ht₀ : t₀ < 1 := by dsimp [t₀]; linarith
  have hst₀ : s₀ < t₀ := by linarith
  have hsI : s₀ ∈ I := ⟨hs₀.le, by linarith⟩
  have htI : t₀ ∈ I := ⟨by linarith,ht₀.le⟩
  let Q := f '' Icc s₀ t₀
  let A := f '' Icc 0 s₀ ∪ f '' Icc t₀ 1
  have hQ : IsArcBetween Q (f s₀) (f t₀) :=
    hf.middle_IsArcBetween hsI htI (ne_of_lt ht₀) hst₀
  have hA : IsArcBetween A (f t₀) (f s₀) :=
    hf.outside_IsArcBetween hsI htI (ne_of_lt (by linarith : s₀ < 1)) (ne_of_lt ht₀) hst₀
  have hcover : Q ∪ A = f '' I := IsLoop.pieces_cover hsI htI
  have hmeet : Q ∩ A = {f s₀,f t₀} :=
    hf.pieces_meet_at_ends hsI htI (ne_of_lt (by linarith : s₀ < 1)) (ne_of_lt ht₀) hst₀
  let D' := D \ A
  have hD' : IsOpen D' := hD.sdiff hA.isArc.isClosed
  have hleft : f s₀ ∉ D' := fun h => h.2 hA.right_mem
  have hright : f t₀ ∉ D' := fun h => h.2 hA.left_mem
  have hQD' : Q \ {f s₀,f t₀} ⊆ D' := by
    rintro y ⟨⟨u,hu,rfl⟩,hne⟩
    refine ⟨hinter ⟨u,⟨by linarith [hu.1],by linarith [hu.2]⟩,rfl⟩,?_⟩
    intro hyA
    exact hne (hmeet ▸ ⟨Set.mem_image_of_mem f hu,hyA⟩)
  have hJ : IsJordanCurve (A ∪ Q) := by
    rw [Set.union_comm,hcover]
    exact ⟨f,hf,rfl⟩
  have hcollars : HasArcCollars D' Q :=
    hasArcCollars_of_jordan_arc_split hD' hA.reverse hQ
      (by rwa [Set.inter_comm] at hmeet) hJ hleft hright hQD'
  have hKsub : f '' Icc s t ⊆ D' ∩ Q := by
    rintro y ⟨u,hu,rfl⟩
    have huQ : u ∈ Icc s₀ t₀ := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hyQ : f u ∈ Q := ⟨u,huQ,rfl⟩
    refine ⟨⟨hinter ⟨u,⟨by linarith [hu.1],by linarith [hu.2]⟩,rfl⟩,?_⟩,hyQ⟩
    intro hyA
    have hyPair : f u ∈ ({f s₀,f t₀} : Set Plane) := hmeet ▸ ⟨hyQ,hyA⟩
    rcases (by simpa using hyPair : f u = f s₀ ∨ f u = f t₀) with he | he
    · have hue := hf.injective_on_middle hsI htI (ne_of_lt ht₀) huQ (left_mem_Icc.mpr hst₀.le) he
      linarith [hu.1]
    · have hue := hf.injective_on_middle hsI htI (ne_of_lt ht₀) huQ (right_mem_Icc.mpr hst₀.le) he
      linarith [hu.2]
  have hsubI : Icc s t ⊆ I := fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hcompact : IsCompact (f '' Icc s t) :=
    isCompact_image_of_subset_I hf.continuousOn hsubI isClosed_Icc
  have hpre : IsPreconnected (f '' Icc s t) :=
    isPreconnected_Icc.image f (hf.continuousOn.mono hsubI)
  have hnontriv : (f '' Icc s t).Nontrivial := by
    refine ⟨f s,⟨s,left_mem_Icc.mpr hst.le,rfl⟩,f t,⟨t,right_mem_Icc.mpr hst.le,rfl⟩,?_⟩
    intro he
    have hstEq := hf.injOn ⟨hs.le,by linarith⟩ ⟨by linarith,ht⟩ he
    exact (ne_of_lt hst) hstEq
  obtain ⟨C⟩ := hcollars _ hKsub hcompact hpre hnontriv
  refine ⟨{ nbhd := C.nbhd
            left := C.left
            right := C.right
            isOpen_nbhd := C.isOpen_nbhd
            subset_nbhd := C.subset_nbhd
            nbhd_subset := fun y hy => (C.nbhd_subset hy).1
            nbhd_diff := ?_
            isConnected_left := C.isConnected_left
            isConnected_right := C.isConnected_right
            subset_closure_left := C.subset_closure_left
            subset_closure_right := C.subset_closure_right }⟩
  calc
    C.nbhd \ (f '' I) = C.nbhd \ Q := by
      rw [← hcover]
      ext y
      constructor
      · rintro ⟨hy,hn⟩
        exact ⟨hy,fun hyQ => hn (Or.inl hyQ)⟩
      · rintro ⟨hy,hn⟩
        refine ⟨hy,?_⟩
        rintro (hyQ | hyA)
        · exact hn hyQ
        · exact (C.nbhd_subset hy).2 hyA
    _ = C.left ∪ C.right := C.nbhd_diff

/-- A connected open domain cut by an actual loop has at most two sides,
provided the whole open loop is in the domain and its basepoint is outside. -/
theorem actual_loop_domain_atMostTwo
    {f : ℝ → Plane} (hf : IsLoop f) {D : Set Plane}
    (hD : IsOpen D) (hconn : IsPreconnected D)
    (hbase : f 0 ∉ D) (hinter : f '' Ioo 0 1 ⊆ D) :
    ∃ zL ∈ D \ (f '' I), ∃ zR ∈ D \ (f '' I),
      ∀ x ∈ D \ (f '' I),
        x ∈ connectedComponentIn (D \ (f '' I)) zL ∨
        x ∈ connectedComponentIn (D \ (f '' I)) zR := by
  have hJ : IsJordanCurve (f '' I) := ⟨f,hf,rfl⟩
  obtain ⟨C₀⟩ := loop_middle_has_actual_collar hf hD hinter
    (s := 1/4) (t := 3/4) (by norm_num) (by norm_num) (by norm_num)
  have hz₀ : f (1/2) ∈ f '' Icc (1/4 : ℝ) (3/4) :=
    ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  refine ⟨C₀.ptL,C₀.ptL_mem_diff,C₀.ptR,C₀.ptR_mem_diff,?_⟩
  intro x hx
  refine covered_by_two_of_local hD hconn hJ.isClosed C₀.ptL_mem_diff (fun w hw => ?_) hx
  obtain ⟨u,hu,hu1,huw⟩ := hf.parameter_before_finish hw.2
  have hu0 : u ≠ 0 := fun he => hbase (by simpa [← huw,he] using hw.1)
  have huInterior : u ∈ Ioo 0 1 := ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩
  obtain ⟨C⟩ := loop_middle_has_actual_collar hf hD hinter
    (s := min u (1/4)) (t := max u (3/4))
    (lt_min huInterior.1 (by norm_num))
    (by have := min_le_right u (1/4 : ℝ); have := le_max_right u (3/4 : ℝ); linarith)
    (max_lt huInterior.2 (by norm_num))
  refine ⟨C.nbhd,C.isOpen_nbhd,?_,C.nbhd_subset,?_⟩
  · rw [← huw]
    exact C.subset_nbhd ⟨u,⟨min_le_left _ _,le_max_left _ _⟩,rfl⟩
  · exact C₀.nbhd_diff_subset_components C hz₀
      ⟨1/2,⟨le_trans (min_le_right _ _) (by norm_num),le_trans (by norm_num) (le_max_right _ _)⟩,rfl⟩

/-- Both Jordan sides occur, and the collar argument exhausts the domain. -/
theorem actual_loop_domain_exact_two
    {f : ℝ → Plane} (hf : IsLoop f) {D : Set Plane}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hbase : f 0 ∉ D) (hinter : f '' Ioo 0 1 ⊆ D) :
    ∃ x ∈ D \ (f '' I), ∃ y ∈ D \ (f '' I),
      connectedComponentIn (D \ (f '' I)) x ≠ connectedComponentIn (D \ (f '' I)) y ∧
      ∀ z ∈ D \ (f '' I),
        z ∈ connectedComponentIn (D \ (f '' I)) x ∨
        z ∈ connectedComponentIn (D \ (f '' I)) y := by
  have hJ : IsJordanCurve (f '' I) := ⟨f,hf,rfl⟩
  have hsep := jordan_curve_theorem hJ
  have hmidP : f (1/2) ∈ f '' I := ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hmidD : f (1/2) ∈ D := hinter ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩
  have hclI : f (1/2) ∈ closure (inside (f '' I)) :=
    frontier_subset_closure (hsep.frontier_inside.symm ▸ hmidP)
  have hclO : f (1/2) ∈ closure (outside (f '' I)) :=
    frontier_subset_closure (hsep.frontier_outside.symm ▸ hmidP)
  obtain ⟨x,hxD,hxI⟩ := mem_closure_iff.mp hclI D hD hmidD
  obtain ⟨y,hyD,hyO⟩ := mem_closure_iff.mp hclO D hD hmidD
  have hx : x ∈ D \ (f '' I) := ⟨hxD,inside_subset_compl hxI⟩
  have hy : y ∈ D \ (f '' I) := ⟨hyD,outside_subset_compl hyO⟩
  have hxi : connectedComponentIn (D \ (f '' I)) x ⊆ inside (f '' I) := by
    have hs : connectedComponentIn (D \ (f '' I)) x ⊆ connectedComponentIn (f '' I)ᶜ x :=
      (isConnected_connectedComponentIn_iff.mpr hx).isPreconnected.subset_connectedComponentIn
        (mem_connectedComponentIn hx) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
    rw [hsep.connectedComponentIn_eq_inside hxI] at hs
    exact hs
  have hne : connectedComponentIn (D \ (f '' I)) x ≠ connectedComponentIn (D \ (f '' I)) y := by
    intro he
    have hyI := hxi (he.symm ▸ mem_connectedComponentIn hy)
    exact Set.disjoint_left.mp disjoint_inside_outside hyI hyO
  obtain ⟨zL,hzL,zR,hzR,hcov⟩ := actual_loop_domain_atMostTwo hf hD hconn.isPreconnected hbase hinter
  exact ⟨x,hx,y,hy,hne,covered_by_two_components_of_ne hcov hx hy hne⟩

end Schoenflies
#print axioms Schoenflies.loop_middle_has_actual_collar
#print axioms Schoenflies.actual_loop_domain_atMostTwo

#print axioms Schoenflies.actual_loop_domain_exact_two
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An actual marked loop splits a connected open sphere domain containing
its entire interior into two genuine complement components. The loop's
marked basepoint is outside the domain. No side certificate is assumed. -/
theorem actual_loop_domain_split_faces
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (hloop : a.val.map 0 = a.val.map 1)
    {U : Set S} (hU : IsOpen U) (hcU : IsConnected U)
    (hbase : a.val.map 0 ∉ U) (hinter : arcInterior M a ⊆ U) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, IsComplementComponent (Uᶜ ∪ a.val.image) V ↔ V ∈ F := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨p,hpmark,hpne⟩ := Finset.exists_mem_ne
    (by rw [M.cover.branch_card]; norm_num : 1 < M.cover.branch.card) (a.val.map 0)
  have hp : p ∉ a.val.image := by
    rintro ⟨t,ht⟩
    have hm : a.val.map t ∈ M.cover.branch := ht.symm ▸ hpmark
    rcases a.val.marked_only_at_ends t hm with he | he
    · exact hpne (ht.symm.trans (congrArg a.val.map he))
    · exact hpne ((ht.symm.trans (congrArg a.val.map he)).trans hloop.symm)
  let e := M.puncturedPlane p
  let f : Plane → S := fun z => (e.symm z).val
  let g : Interval → Plane := fun t => e ⟨a.val.map t,by
    intro he; exact hp (he ▸ Set.mem_range_self t)⟩
  have hg : Continuous g := e.continuous.comp (Continuous.subtype_mk a.val.continuous _)
  let l : ℝ → Plane := fun t => if ht : t ∈ I then g ⟨t,ht⟩ else g 0
  have hl : ∀ t : Interval, l t = g t := fun t => dite_eq_left t.property
  have hl0 : l (0 : ℝ) = g (0 : Interval) := by simpa using hl (0 : Interval)
  have hl1 : l (1 : ℝ) = g (1 : Interval) := by simpa using hl (1 : Interval)
  have hloopL : IsLoop l := by
    refine ⟨?_,?_,?_⟩
    · exact continuousOn_iff_continuous_domRestrict.mpr (by
        convert hg using 1
        funext t
        exact hl t)
    · rw [hl0,hl1]
      exact congrArg e (Subtype.ext hloop)
    · intro t ht u hu he
      let T : Interval := ⟨t,⟨ht.1,ht.2.le⟩⟩
      let A : Interval := ⟨u,⟨hu.1,hu.2.le⟩⟩
      have heG : g T = g A := (hl T).symm.trans (he.trans (hl A))
      have heA : a.val.map T = a.val.map A := congrArg Subtype.val (e.injective heG)
      rcases a.val.injective_except_loop_closure T A heA with he | ⟨_,he⟩ | ⟨he,_⟩
      · exact congrArg Subtype.val he
      · have hu1 : u = 1 := congrArg Subtype.val he
        linarith [hu.2]
      · have ht1 : t = 1 := congrArg Subtype.val he
        linarith [ht.2]
  have hlrange : l '' I = Set.range g := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,(hl ⟨t,ht⟩).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,hl t⟩
  have hf : Topology.IsOpenEmbedding f :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  have hDopen : IsOpen (f ⁻¹' U) := hU.preimage hf.continuous
  have hDconn : IsConnected (f ⁻¹' U) := by
    have hconn := (actual_open_puncture_connected M hU hcU p).preimage_of_isOpenMap
      hf.injective hf.isOpenMap (by
        intro x hx
        exact ⟨e ⟨x,by simpa only [mem_singleton_iff] using hx.2⟩,
          congrArg Subtype.val (e.symm_apply_apply _)⟩)
    convert hconn using 1
    ext z
    simp only [mem_preimage,mem_sdiff,mem_singleton_iff]
    exact ⟨fun hz => ⟨hz,(e.symm z).property⟩,And.left⟩
  have hfg : ∀ t, f (g t) = a.val.map t := fun t =>
    congrArg Subtype.val (e.symm_apply_apply _)
  have hbaseL : l 0 ∉ f ⁻¹' U := by
    rw [hl0]
    exact fun h => hbase (hfg 0 ▸ h)
  have hinterL : l '' Ioo 0 1 ⊆ f ⁻¹' U := by
    rintro z ⟨t,ht,rfl⟩
    let T : Interval := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
    rw [hl T]
    change f (g T) ∈ U
    rw [hfg]
    apply hinter
    refine ⟨Set.mem_range_self T,?_⟩
    intro hm
    rcases a.val.marked_only_at_ends T hm with he | he
    · have ht0 : t = 0 := congrArg Subtype.val he
      linarith [ht.1]
    · have ht1 : t = 1 := congrArg Subtype.val he
      linarith [ht.2]
  let W := U \ a.val.image
  let V := W \ {p}
  have hWopen : IsOpen W := hU.sdiff (markedArc_image_compact a.val).isClosed
  have hpre : f ⁻¹' V = f ⁻¹' U \ Set.range g := by
    ext z
    have heq : f z ∈ a.val.image ↔ z ∈ Set.range g := by
      constructor
      · rintro ⟨t,ht⟩
        refine ⟨t,hf.injective ?_⟩
        exact (hfg t).trans ht
      · rintro ⟨t,rfl⟩
        rw [hfg]
        exact Set.mem_range_self t
    change (f z ∈ U ∧ f z ∉ a.val.image) ∧ f z ∉ ({p} : Set S) ↔
      f z ∈ U ∧ z ∉ Set.range g
    simp only [mem_singleton_iff]
    exact ⟨fun hz => ⟨hz.1.1,fun hg => hz.1.2 (heq.mpr hg)⟩,
      fun hz => ⟨⟨hz.1,fun ha => hz.2 (heq.mp ha)⟩,(e.symm z).property⟩⟩
  have hVrange : V ⊆ Set.range f := by
    intro z hz
    exact ⟨e ⟨z,by simpa only [mem_singleton_iff] using hz.2⟩,
      congrArg Subtype.val (e.symm_apply_apply _)⟩
  obtain ⟨x,hx,y,hy,hne,hcov⟩ :=
    actual_loop_domain_exact_two hloopL hDopen hDconn hbaseL hinterL
  rw [hlrange] at hx hy hne hcov
  have hxV : f x ∈ V := by change x ∈ f ⁻¹' V; rw [hpre]; exact hx
  have hyV : f y ∈ V := by change y ∈ f ⁻¹' V; rw [hpre]; exact hy
  have hmx := actual_open_embedding_component_transport f hf hVrange hxV
  have hmy := actual_open_embedding_component_transport f hf hVrange hyV
  rw [hpre] at hmx hmy
  have hneV : connectedComponentIn V (f x) ≠ connectedComponentIn V (f y) := by
    intro he
    apply hne
    apply hf.injective.image_injective
    exact hmx.trans (he.trans hmy.symm)
  have hcovV : ∀ z ∈ V, z ∈ connectedComponentIn V (f x) ∨ z ∈ connectedComponentIn V (f y) := by
    intro z hz
    obtain ⟨t,ht⟩ := hVrange hz
    have htD : t ∈ f ⁻¹' U \ Set.range g := by
      rw [← hpre]
      change f t ∈ V
      rw [ht]
      exact hz
    rcases hcov t htD with htX | htY
    · left
      rw [← hmx]
      exact ⟨t,htX,ht⟩
    · right
      rw [← hmy]
      exact ⟨t,htY,ht⟩
  obtain ⟨hneW,hcovW⟩ := actual_component_coverage_restore_puncture M hWopen hxV hyV hneV hcovV
  let A := connectedComponentIn W (f x)
  let B := connectedComponentIn W (f y)
  have hcomp : (Uᶜ ∪ a.val.image)ᶜ = W := by ext z; simp [W]
  have hA : IsComplementComponent (Uᶜ ∪ a.val.image) A :=
    complementComponent_iff_componentIn.mpr ⟨f x,by simpa [hcomp] using hxV.1,by rw [hcomp]⟩
  have hB : IsComplementComponent (Uᶜ ∪ a.val.image) B :=
    complementComponent_iff_componentIn.mpr ⟨f y,by simpa [hcomp] using hyV.1,by rw [hcomp]⟩
  refine ⟨{A,B},Finset.card_pair hneW,?_⟩
  intro T
  constructor
  · intro hT
    obtain ⟨z,hz⟩ := hT.1
    have hzW : z ∈ W := by rw [← hcomp]; exact hT.2.2.1 hz
    rcases hcovW z hzW with hzA | hzB
    · have he : T = A := by
        by_contra hne
        exact Set.disjoint_left.mp (complementComponents_disjoint hT hA hne) hz hzA
      simp [he]
    · have he : T = B := by
        by_contra hne
        exact Set.disjoint_left.mp (complementComponents_disjoint hT hB hne) hz hzB
      simp [he]
  · intro hT
    rcases Finset.mem_insert.mp hT with hT | hT
    · exact hT ▸ hA
    · exact (Finset.mem_singleton.mp hT) ▸ hB
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_loop_domain_split_faces

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Genuine global incidence producer for an actual loop edge. Other
representatives only need to avoid its interior. The auxiliary deleted graph
includes the loop basepoint; this does not change the full graph. -/
theorem actual_loop_edge_incident_faces_atMostTwo
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hloop : a.val.map 0 = a.val.map 1)
    (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, IsComplementComponent ((⋃ v, (r v).val.image) ∪ a.val.image) V →
        (frontier V ∩ arcInterior M a).Nonempty → V ∈ F := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hi : a.val.map '' Set.Ioo (0 : Interval) 1 = arcInterior M a := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨⟨t,rfl⟩,?_⟩
      intro hb
      rcases a.val.marked_only_at_ends t hb with h | h
      · simpa [h] using ht.1
      · simpa [h] using ht.2
    · rintro ⟨⟨t,rfl⟩,hn⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h
        have he : t = (0 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.start_marked)
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h
        have he : t = (1 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.end_marked)
      refine ⟨t,?_,rfl⟩
      change (0 : ℝ) < t.val ∧ t.val < 1
      exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
  have hci : IsConnected (arcInterior M a) := by
    rw [← hi]
    have hc : IsConnected (Set.Ioo (0 : Interval) 1) :=
      ⟨⟨⟨(1:ℝ)/2, by constructor <;> norm_num⟩, by
          constructor
          · change (0 : ℝ) < 1/2; norm_num
          · change (1 : ℝ)/2 < 1; norm_num⟩,
        isPreconnected_Ioo⟩
    exact hc.image a.val.map a.val.continuous.continuousOn
  let G : Set S := (⋃ v, (r v).val.image) ∪ {a.val.map 0}
  have havoid : arcInterior M a ⊆ Gᶜ := by
    intro x hx hxG
    rcases hxG with hxG | hxp
    · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
      exact Set.disjoint_left.mp (ha v) hx ⟨hv,hx.2⟩
    · exact hx.2 ((Set.mem_singleton_iff.mp hxp).symm ▸ a.val.start_marked)
  obtain ⟨x,hx⟩ := hci.nonempty
  let U := connectedComponentIn Gᶜ x
  have hU : IsComplementComponent G U :=
    complementComponent_iff_componentIn.mpr ⟨x,havoid hx,rfl⟩
  have hint : arcInterior M a ⊆ U := hci.isPreconnected.subset_connectedComponentIn hx havoid
  have hbase : a.val.map 0 ∉ U := fun h => hU.2.2.1 h (Or.inr (Set.mem_singleton _))
  have hGcompact : IsCompact G :=
    (markedFamily_graph_compact (fun v => (r v).val)).union isCompact_singleton
  have hopen : IsOpen U := complementComponent_open hGcompact.isClosed hU
  obtain ⟨F,hcard,hF⟩ := actual_loop_domain_split_faces M a hloop hopen hU.2.1 hbase hint
  have hGU : G ⊆ Uᶜ := fun z hz hzU => hU.2.2.1 hzU hz
  have hgraph : G ∪ a.val.image = (⋃ v, (r v).val.image) ∪ a.val.image := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact Or.inl hz
      · right
        rw [Set.mem_singleton_iff.mp hz]
        exact Set.mem_range_self 0
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl (Or.inl hz)
      · exact Or.inr hz
  refine ⟨F,hcard,?_⟩
  intro V hV htouch
  rw [← hgraph] at hV
  obtain ⟨z,hzfr,hza⟩ := htouch
  have hmeet : (U ∩ V).Nonempty := Set.Nonempty.of_closure
    ⟨z,hopen.inter_closure ⟨hint hza,frontier_subset_closure hzfr⟩⟩
  obtain ⟨y,hyU,hyV⟩ := hmeet
  have hVG : V ⊆ Gᶜ := fun z hz hG => hV.2.2.1 hz (Or.inl hG)
  have hVC : V ⊆ connectedComponentIn Gᶜ y :=
    hV.2.1.isPreconnected.subset_connectedComponentIn hyV hVG
  have hUC : U = connectedComponentIn Gᶜ y := by
    obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hU
    rw [he]
    exact connectedComponentIn_eq (he ▸ hyU)
  have hVU : V ⊆ U := hUC.symm ▸ hVC
  have hlocal : IsComplementComponent (Uᶜ ∪ a.val.image) V := by
    refine ⟨hV.1,hV.2.1,?_,?_⟩
    · intro z hz h
      rcases h with hn | ha
      · exact hn (hVU hz)
      · exact hV.2.2.1 hz (Or.inr ha)
    · intro T hT hVT hTL
      have hTH : T ⊆ (G ∪ a.val.image)ᶜ := by
        intro z hz h
        rcases h with hG | ha
        · exact hTL hz (Or.inl (hGU hG))
        · exact hTL hz (Or.inr ha)
      exact hV.2.2.2 T hT hVT hTH
  exact (hF V).1 hlocal
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_loop_edge_incident_faces_atMostTwo
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
open scoped Classical BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance allEdgeClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- The actual all-bad edge incidence producer, covering loops and nonloops. -/
theorem actual_bad_edge_incident_faces_atMostTwo
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (u : {v // v ∈ sigma}) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, IsComplementComponent (⋃ v, (r v).val.image) V →
        (frontier V ∩ arcInterior M (r u)).Nonempty → V ∈ F := by
  classical
  by_cases hloop : (r u).val.map 0 = (r u).val.map 1
  · let rr : {v : {v // v ∈ sigma} // v ≠ u} → EssentialMarkedArc M := fun v => r v.val
    have ha : ∀ v, Disjoint (arcInterior M (r u)) (arcInterior M (rr v)) := by
      intro v
      exact hd u v.val v.property.symm
    obtain ⟨F,hcard,hF⟩ := actual_loop_edge_incident_faces_atMostTwo M rr (r u) hloop ha
    have hgraph : (⋃ v, (r v).val.image) = (⋃ v, (rr v).val.image) ∪ (r u).val.image := by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
        by_cases hvu : v = u
        · exact Or.inr (hvu ▸ hv)
        · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v,hvu⟩,hv⟩)
      · rintro (hx | hx)
        · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨v.val,hv⟩
        · exact Set.mem_iUnion.mpr ⟨u,hx⟩
    refine ⟨F,hcard,?_⟩
    intro V hV htouch
    exact hF V (hgraph ▸ hV) htouch
  · exact actual_bad_nonloop_edge_incident_faces_atMostTwo M r hr hd hbad u hloop

/-- Count genuine frontier-contact incidences for each actual edge; there is
no caller-supplied edgeFaceCount or side bound. -/
theorem actual_bad_edge_face_count_le_two
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (u : {v // v ∈ sigma}) (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V) :
    (F.filter (fun V => (frontier V ∩ arcInterior M (r u)).Nonempty)).card ≤ 2 := by
  classical
  obtain ⟨T,hcard,hT⟩ := actual_bad_edge_incident_faces_atMostTwo M r hr hd hbad u
  have hsub : F.filter (fun V => (frontier V ∩ arcInterior M (r u)).Nonempty) ⊆ T := by
    intro V hV
    obtain ⟨hVF,htouch⟩ := Finset.mem_filter.mp hV
    exact hT V (hF V hVF) htouch
  exact (Finset.card_le_card hsub).trans_eq hcard

/-- Total concrete face-edge incidences are at most twice the number of
actual representatives. The degree is computed from actual frontier contact,
not supplied as a numerical hypothesis. -/
theorem actual_bad_total_face_edge_incidence_le
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V) :
    (∑ V ∈ F, (Finset.univ.filter (fun u : {v // v ∈ sigma} =>
      (frontier V ∩ arcInterior M (r u)).Nonempty)).card) ≤ 2 * sigma.card := by
  classical
  have hswap :
      (∑ V ∈ F, (Finset.univ.filter (fun u : {v // v ∈ sigma} =>
        (frontier V ∩ arcInterior M (r u)).Nonempty)).card) =
      ∑ u : {v // v ∈ sigma}, (F.filter (fun V =>
        (frontier V ∩ arcInterior M (r u)).Nonempty)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  calc
    _ ≤ ∑ _u : {v // v ∈ sigma}, (2 : ℕ) := Finset.sum_le_sum
      (fun u _ => actual_bad_edge_face_count_le_two M r hr hd hbad u F hF)
    _ = 2 * sigma.card := by simp [Fintype.card_coe,Nat.mul_comm]
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_bad_edge_incident_faces_atMostTwo
#print axioms CurveComplex.HyperellipticModel.actual_bad_edge_face_count_le_two
#print axioms CurveComplex.HyperellipticModel.actual_bad_total_face_edge_incidence_le

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Upgrade the actual inserted-edge local split to global complementary faces.
Each of the two local components really contacts the inserted arc. -/
theorem actual_inserted_split_faces_global_incident
    (M : HyperellipticModel E S) (G U : Set S) (a : EssentialMarkedArc M)
    (hG : IsClosed G) (hU : IsComplementComponent G U)
    (hcut : a.val.image ∩ U ⊆ arcInterior M a)
    (F : Finset (Set S)) (hcard : F.card = 2)
    (hF : ∀ V : Set S, IsComplementComponent (Uᶜ ∪ a.val.image) V ↔ V ∈ F) :
    ∀ V ∈ F, IsComplementComponent (G ∪ a.val.image) V ∧
      (frontier V ∩ arcInterior M a).Nonempty := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hclosed : IsClosed (Uᶜ ∪ a.val.image) :=
    hopen.isClosed_compl.union (markedArc_image_compact a.val).isClosed
  intro V hVF
  have hV := (hF V).2 hVF
  have hVU : V ⊆ U := fun x hx => by
    by_contra hn
    exact hV.2.2.1 hx (Or.inl hn)
  have hglobal : IsComplementComponent (G ∪ a.val.image) V := by
    refine ⟨hV.1,hV.2.1,?_,?_⟩
    · intro x hx hg
      rcases hg with hg | ha
      · exact hU.2.2.1 (hVU hx) hg
      · exact hV.2.2.1 hx (Or.inr ha)
    · intro T hT hVT hTL
      obtain ⟨x,hx⟩ := hV.1
      have hTU : T ⊆ U := by
        have hTC := hT.isPreconnected.subset_connectedComponentIn (hVT hx)
          (fun y hy hg => hTL hy (Or.inl hg))
        obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hU
        have hUC : U = connectedComponentIn Gᶜ x := by
          rw [he]
          exact connectedComponentIn_eq (he ▸ hVU hx)
        exact hUC.symm ▸ hTC
      exact hV.2.2.2 T hT hVT (fun y hy hh => by
        rcases hh with hn | ha
        · exact hn (hTU hy)
        · exact hTL hy (Or.inr ha))
  refine ⟨hglobal,?_⟩
  by_contra hnone
  have hcl : closure V ∩ U ⊆ V := by
    intro z hz
    by_contra hzV
    have hzfr : z ∈ frontier V := by
      rw [(complementComponent_open hclosed hV).frontier_eq]
      exact ⟨hz.1,hzV⟩
    have hzcut : z ∈ a.val.image := by
      rcases complementComponent_frontier_subset hclosed hV hzfr with hn | ha
      · exact False.elim (hn hz.2)
      · exact ha
    exact hnone ⟨z,hzfr,hcut ⟨hzcut,hz.2⟩⟩
  have hUV : U ⊆ V := hU.2.1.isPreconnected.subset_of_closure_inter_subset
    (complementComponent_open hclosed hV)
    (by obtain ⟨x,hx⟩ := hV.1; exact ⟨x,hVU hx,hx⟩) hcl
  obtain ⟨W,hWF,hWV⟩ := Finset.exists_mem_ne (by omega : 1 < F.card) V
  have hW := (hF W).2 hWF
  obtain ⟨w,hw⟩ := hW.1
  have hwU : w ∈ U := by
    by_contra hn
    exact hW.2.2.1 hw (Or.inl hn)
  exact Set.disjoint_left.mp (complementComponents_disjoint hW hV hWV) hw (hUV hwU)

/-- Exact incident-face characterization of a concrete two-component split. -/
theorem actual_inserted_split_faces_exact_incidence
    (M : HyperellipticModel E S) (G U : Set S) (a : EssentialMarkedArc M)
    (hG : IsClosed G) (hU : IsComplementComponent G U)
    (hint : arcInterior M a ⊆ U)
    (hcut : a.val.image ∩ U ⊆ arcInterior M a)
    (F : Finset (Set S)) (hcard : F.card = 2)
    (hF : ∀ V : Set S, IsComplementComponent (Uᶜ ∪ a.val.image) V ↔ V ∈ F) :
    ∀ V : Set S, V ∈ F ↔ IsComplementComponent (G ∪ a.val.image) V ∧
      (frontier V ∩ arcInterior M a).Nonempty := by
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hGU : G ⊆ Uᶜ := fun z hz hzU => hU.2.2.1 hzU hz
  intro V
  constructor
  · exact actual_inserted_split_faces_global_incident M G U a hG hU hcut F hcard hF V
  · rintro ⟨hV,z,hzfr,hza⟩
    have hmeet : (U ∩ V).Nonempty := Set.Nonempty.of_closure
      ⟨z,hopen.inter_closure ⟨hint hza,frontier_subset_closure hzfr⟩⟩
    obtain ⟨x,hxU,hxV⟩ := hmeet
    have hVG : V ⊆ Gᶜ := fun y hy hG => hV.2.2.1 hy (Or.inl hG)
    have hVC : V ⊆ connectedComponentIn Gᶜ x :=
      hV.2.1.isPreconnected.subset_connectedComponentIn hxV hVG
    have hUC : U = connectedComponentIn Gᶜ x := by
      obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hU
      rw [he]
      exact connectedComponentIn_eq (he ▸ hxU)
    have hVU : V ⊆ U := hUC.symm ▸ hVC
    apply (hF V).1
    refine ⟨hV.1,hV.2.1,?_,?_⟩
    · intro y hy h
      rcases h with hn | ha
      · exact hn (hVU hy)
      · exact hV.2.2.1 hy (Or.inr ha)
    · intro T hT hVT hTL
      have hTH : T ⊆ (G ∪ a.val.image)ᶜ := by
        intro y hy h
        rcases h with hG | ha
        · exact hTL hy (Or.inl (hGU hG))
        · exact hTL hy (Or.inr ha)
      exact hV.2.2.2 T hT hVT hTH
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_inserted_split_faces_global_incident

#print axioms CurveComplex.HyperellipticModel.actual_inserted_split_faces_exact_incidence

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2800000
theorem actual_nonloop_cycle_edge_exact_incident_faces
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (a : EssentialMarkedArc M) (haNL : a.val.map 0 ≠ a.val.map 1)
    (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
    (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
    (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
    (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, V ∈ F ↔
        IsComplementComponent ((⋃ v, (r v).val.image) ∪ a.val.image) V ∧
        (frontier V ∩ arcInterior M a).Nonempty := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  obtain ⟨U,hU,_,hint,F,hcard,hF⟩ :=
    actual_nonloop_cycle_edge_split_faces M r hd a haNL ha h0 h1 hc
  have hcut : a.val.image ∩ U ⊆ arcInterior M a := by
    rintro z ⟨hz,hzU⟩
    refine ⟨hz,?_⟩
    rintro hb
    obtain ⟨t,rfl⟩ := hz
    rcases a.val.marked_only_at_ends t hb with ht | ht
    · exact hU.2.2.1 hzU (ht.symm ▸ h0)
    · exact hU.2.2.1 hzU (ht.symm ▸ h1)
  exact ⟨F,hcard,actual_inserted_split_faces_exact_incidence M _ U a
    (markedFamily_graph_compact (fun v => (r v).val)).isClosed hU hint hcut F hcard hF⟩

theorem actual_loop_edge_exact_incident_faces
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hloop : a.val.map 0 = a.val.map 1)
    (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, V ∈ F ↔
        IsComplementComponent ((⋃ v, (r v).val.image) ∪ a.val.image) V ∧
        (frontier V ∩ arcInterior M a).Nonempty := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hi : a.val.map '' Set.Ioo (0 : Interval) 1 = arcInterior M a := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨⟨t,rfl⟩,?_⟩
      intro hb
      rcases a.val.marked_only_at_ends t hb with h | h
      · simpa [h] using ht.1
      · simpa [h] using ht.2
    · rintro ⟨⟨t,rfl⟩,hn⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h
        have he : t = (0 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.start_marked)
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h
        have he : t = (1 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.end_marked)
      refine ⟨t,?_,rfl⟩
      change (0 : ℝ) < t.val ∧ t.val < 1
      exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
  have hci : IsConnected (arcInterior M a) := by
    rw [← hi]
    have hc : IsConnected (Set.Ioo (0 : Interval) 1) :=
      ⟨⟨⟨(1:ℝ)/2, by constructor <;> norm_num⟩, by
          constructor
          · change (0 : ℝ) < 1/2; norm_num
          · change (1 : ℝ)/2 < 1; norm_num⟩,
        isPreconnected_Ioo⟩
    exact hc.image a.val.map a.val.continuous.continuousOn
  let G : Set S := (⋃ v, (r v).val.image) ∪ {a.val.map 0}
  have havoid : arcInterior M a ⊆ Gᶜ := by
    intro x hx hxG
    rcases hxG with hxG | hxp
    · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
      exact Set.disjoint_left.mp (ha v) hx ⟨hv,hx.2⟩
    · exact hx.2 ((Set.mem_singleton_iff.mp hxp).symm ▸ a.val.start_marked)
  obtain ⟨x,hx⟩ := hci.nonempty
  let U := connectedComponentIn Gᶜ x
  have hU : IsComplementComponent G U :=
    complementComponent_iff_componentIn.mpr ⟨x,havoid hx,rfl⟩
  have hint : arcInterior M a ⊆ U := hci.isPreconnected.subset_connectedComponentIn hx havoid
  have hbase : a.val.map 0 ∉ U := fun h => hU.2.2.1 h (Or.inr (Set.mem_singleton _))
  have hGcompact : IsCompact G :=
    (markedFamily_graph_compact (fun v => (r v).val)).union isCompact_singleton
  have hopen : IsOpen U := complementComponent_open hGcompact.isClosed hU
  obtain ⟨F,hcard,hF⟩ := actual_loop_domain_split_faces M a hloop hopen hU.2.1 hbase hint
  have hgraph : G ∪ a.val.image = (⋃ v, (r v).val.image) ∪ a.val.image := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact Or.inl hz
      · right
        rw [Set.mem_singleton_iff.mp hz]
        exact Set.mem_range_self 0
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl (Or.inl hz)
      · exact Or.inr hz
  have hcut : a.val.image ∩ U ⊆ arcInterior M a := by
    rintro z ⟨hz,hzU⟩
    refine ⟨hz,?_⟩
    rintro hb
    obtain ⟨t,rfl⟩ := hz
    rcases a.val.marked_only_at_ends t hb with ht | ht
    · apply hbase
      simpa [ht] using hzU
    · apply hbase
      simpa [ht, ← hloop] using hzU
  refine ⟨F,hcard,?_⟩
  intro V
  rw [← hgraph]
  exact actual_inserted_split_faces_exact_incidence M G U a hGcompact.isClosed
    hU hint hcut F hcard hF V

noncomputable local instance exactEdgeClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
theorem actual_bad_nonloop_edge_exact_incident_faces
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (u : {v // v ∈ sigma}) (hNL : (r u).val.map 0 ≠ (r u).val.map 1) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, V ∈ F ↔
        IsComplementComponent (⋃ v, (r v).val.image) V ∧
        (frontier V ∩ arcInterior M (r u)).Nonempty := by
  classical
  have hUn : ¬ (actualArcLabels M).isLoop u.val := by
    intro hl
    have hc : (markedArcEndset (r u).val).card = 1 := by
      rw [markedArcEndset_eq_classEndpoints,hr]
      exact hl
    have hc2 : (markedArcEndset (r u).val).card = 2 := Finset.card_pair hNL
    omega
  have hu : u.val ∈ CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma :=
    hbad.symm ▸ u.property
  simp only [CurveGenusTwo.Filtration.badVertices,Finset.mem_filter] at hu
  rcases hu.2 with hl | ⟨w,hw,hwu,_,_,he⟩
  · exact False.elim (hUn hl)
  · let z : {v // v ∈ sigma} := ⟨w,hw⟩
    have hzu : z ≠ u := fun h => hwu (congrArg Subtype.val h)
    have hends : markedArcEndset (r u).val = markedArcEndset (r z).val := by
      rw [markedArcEndset_eq_classEndpoints,markedArcEndset_eq_classEndpoints,hr,hr]
      exact he.symm
    let rr : {v : {v // v ∈ sigma} // v ≠ u} → EssentialMarkedArc M := fun v => r v.val
    let G := ⋃ v, (rr v).val.image
    have h0z : (r u).val.map 0 ∈ (r z).val.image := by
      have hh : (r u).val.map 0 ∈ (markedArcEndset (r z).val : Set S) := by
        rw [← hends]; simp [markedArcEndset]
      rw [← markedArc_image_inter_branch] at hh
      exact hh.1
    have h1z : (r u).val.map 1 ∈ (r z).val.image := by
      have hh : (r u).val.map 1 ∈ (markedArcEndset (r z).val : Set S) := by
        rw [← hends]; simp [markedArcEndset]
      rw [← markedArc_image_inter_branch] at hh
      exact hh.1
    have hzsub : (r z).val.image ⊆ G := fun x hx =>
      Set.mem_iUnion.mpr ⟨⟨z,hzu⟩,hx⟩
    have h0 : (r u).val.map 0 ∈ G := hzsub h0z
    have h1 : (r u).val.map 1 ∈ G := hzsub h1z
    have hc : (r u).val.map 1 ∈ connectedComponentIn G ((r u).val.map 0) :=
      (markedArc_image_connected (r z).val).isPreconnected.subset_connectedComponentIn
        h0z hzsub h1z
    have hdr : ∀ v w, v ≠ w → Disjoint (arcInterior M (rr v)) (arcInterior M (rr w)) := by
      intro v w hvw
      exact hd v.val w.val (fun he => hvw (Subtype.ext he))
    have ha : ∀ v, Disjoint (arcInterior M (r u)) (arcInterior M (rr v)) := by
      intro v
      exact hd u v.val v.property.symm
    obtain ⟨F,hcard,hF⟩ := actual_nonloop_cycle_edge_exact_incident_faces
      M rr hdr (r u) hNL ha h0 h1 hc
    have hgraph : (⋃ v, (r v).val.image) = G ∪ (r u).val.image := by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
        by_cases hvu : v = u
        · exact Or.inr (hvu ▸ hv)
        · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v,hvu⟩,hv⟩)
      · rintro (hx | hx)
        · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨v.val,hv⟩
        · exact Set.mem_iUnion.mpr ⟨u,hx⟩
    refine ⟨F,hcard,?_⟩
    intro V
    rw [hgraph]
    exact hF V

theorem actual_bad_edge_exact_incident_faces
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (u : {v // v ∈ sigma}) :
    ∃ F : Finset (Set S), F.card = 2 ∧
      ∀ V : Set S, V ∈ F ↔
        IsComplementComponent (⋃ v, (r v).val.image) V ∧
        (frontier V ∩ arcInterior M (r u)).Nonempty := by
  classical
  by_cases hloop : (r u).val.map 0 = (r u).val.map 1
  · let rr : {v : {v // v ∈ sigma} // v ≠ u} → EssentialMarkedArc M := fun v => r v.val
    have ha : ∀ v, Disjoint (arcInterior M (r u)) (arcInterior M (rr v)) := by
      intro v
      exact hd u v.val v.property.symm
    obtain ⟨F,hcard,hF⟩ := actual_loop_edge_exact_incident_faces M rr (r u) hloop ha
    have hgraph : (⋃ v, (r v).val.image) = (⋃ v, (rr v).val.image) ∪ (r u).val.image := by
      ext x
      constructor
      · intro hx
        obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
        by_cases hvu : v = u
        · exact Or.inr (hvu ▸ hv)
        · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨v,hvu⟩,hv⟩)
      · rintro (hx | hx)
        · obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨v.val,hv⟩
        · exact Set.mem_iUnion.mpr ⟨u,hx⟩
    refine ⟨F,hcard,?_⟩
    intro V
    rw [hgraph]
    exact hF V
  · exact actual_bad_nonloop_edge_exact_incident_faces M r hr hd hbad u hloop


/-- Two genuine incident faces label the two local sides of each all-bad edge.
The labels are unordered: no cyclic boundary walk or orientation is asserted. -/
theorem actual_bad_edge_two_face_labels
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma) :
    ∃ side : ({v // v ∈ sigma} × Bool) → Set S,
      (∀ u, side (u,false) ≠ side (u,true)) ∧
      (∀ d, IsComplementComponent (⋃ v, (r v).val.image) (side d) ∧
        (frontier (side d) ∩ arcInterior M (r d.1)).Nonempty) ∧
      (∀ u V, IsComplementComponent (⋃ v, (r v).val.image) V ∧
        (frontier V ∩ arcInterior M (r u)).Nonempty ↔
        ∃ b : Bool, side (u,b) = V) := by
  classical
  have hex : ∀ u : {v // v ∈ sigma}, ∃ A B : Set S, A ≠ B ∧
      ∀ V : Set S, IsComplementComponent (⋃ v, (r v).val.image) V ∧
        (frontier V ∩ arcInterior M (r u)).Nonempty ↔ V = A ∨ V = B := by
    intro u
    obtain ⟨T,hcard,hT⟩ := actual_bad_edge_exact_incident_faces M r hr hd hbad u
    obtain ⟨A,B,hne,hpair⟩ := Finset.card_eq_two.mp hcard
    refine ⟨A,B,hne,?_⟩
    intro V
    rw [← hT V,hpair]
    simp
  choose A B hne hfaces using hex
  let side : ({v // v ∈ sigma} × Bool) → Set S := fun d => if d.2 then B d.1 else A d.1
  refine ⟨side,?_,?_,?_⟩
  · intro u
    simpa [side] using hne u
  · rintro ⟨u,b⟩
    cases b
    · exact (hfaces u (A u)).2 (Or.inl rfl)
    · exact (hfaces u (B u)).2 (Or.inr rfl)
  · intro u V
    rw [hfaces]
    constructor
    · rintro (h | h)
      · exact ⟨false,by simpa [side] using h.symm⟩
      · exact ⟨true,by simpa [side] using h.symm⟩
    · rintro ⟨b,hb⟩
      cases b
      · exact Or.inl (by simpa [side] using hb.symm)
      · exact Or.inr (by simpa [side] using hb.symm)

/-- Counting the actual split-component labels retains both copies of every
edge. No identification of repeated labels is made by the counting formula. -/
theorem actual_bad_split_side_incidence_identity
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hcover : ∀ V, IsComplementComponent (⋃ v, (r v).val.image) V → V ∈ F) :
    ∃ side : ({v // v ∈ sigma} × Bool) → Set S,
      (∀ u, side (u,false) ≠ side (u,true)) ∧
      (∀ d, IsComplementComponent (⋃ v, (r v).val.image) (side d) ∧
        (frontier (side d) ∩ arcInterior M (r d.1)).Nonempty) ∧
      (∑ V ∈ F, (Finset.univ.filter (fun d => side d = V)).card) = 2 * sigma.card := by
  classical
  obtain ⟨side,hne,hactual,_⟩ := actual_bad_edge_two_face_labels M r hr hd hbad
  refine ⟨side,hne,hactual,?_⟩
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hall : Finset.univ.filter (fun d => side d ∈ F) =
      (Finset.univ : Finset ({v // v ∈ sigma} × Bool)) := by
    ext d
    simp [hcover (side d) (hactual d).1]
  rw [hall]
  simp [Fintype.card_prod,Fintype.card_coe,Nat.mul_comm]

open scoped Classical

/-- For the concrete all-bad split labels, each edge contacts two DISTINCT
faces. Thus projecting side occurrences to edges loses no multiplicity within
one face. This statement makes no claim for arbitrary bridge-containing graphs. -/
theorem actual_bad_split_side_degree_eq_contact
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma) :
    ∃ side : ({v // v ∈ sigma} × Bool) → Set S,
      (∀ u, side (u,false) ≠ side (u,true)) ∧
      (∀ d, IsComplementComponent (⋃ v, (r v).val.image) (side d) ∧
        (frontier (side d) ∩ arcInterior M (r d.1)).Nonempty) ∧
      ∀ V, IsComplementComponent (⋃ v, (r v).val.image) V →
        (Finset.univ.filter (fun d => side d = V)).card =
          (Finset.univ.filter (fun u => (frontier V ∩ arcInterior M (r u)).Nonempty)).card := by
  classical
  obtain ⟨side,hne,hactual,hfaces⟩ := actual_bad_edge_two_face_labels M r hr hd hbad
  refine ⟨side,hne,hactual,?_⟩
  intro V hV
  let T := Finset.univ.filter (fun d => side d = V)
  have hinj : Set.InjOn Prod.fst (T : Set ({v // v ∈ sigma} × Bool)) := by
    rintro ⟨u,b⟩ hd ⟨w,c⟩ he hfst
    change u = w at hfst
    subst w
    have hb : side (u,b) = V := (Finset.mem_filter.mp hd).2
    have hc : side (u,c) = V := (Finset.mem_filter.mp he).2
    apply Prod.ext
    · rfl
    · cases b <;> cases c
      · rfl
      · exact False.elim (hne u (hb.trans hc.symm))
      · exact False.elim (hne u (hc.trans hb.symm))
      · rfl
  have himage : T.image Prod.fst = Finset.univ.filter
      (fun u => (frontier V ∩ arcInterior M (r u)).Nonempty) := by
    ext u
    constructor
    · intro hu
      obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hu
      have hside : side d = V := (Finset.mem_filter.mp hd).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      simpa [hside,he] using (hactual d).2
    · intro hu
      have htouch := (Finset.mem_filter.mp hu).2
      obtain ⟨b,hb⟩ := (hfaces u V).1 ⟨hV,htouch⟩
      exact Finset.mem_image.mpr ⟨(u,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
  change T.card = _
  rw [← Finset.card_image_of_injOn hinj,himage]

/-- Concrete all-bad side incidence upper bound, for any finite selection of
actual faces; missing faces simply omit some of the two edge-side labels. -/
theorem actual_bad_split_side_incidence_le
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S)) :
    ∃ side : ({v // v ∈ sigma} × Bool) → Set S,
      (∀ u, side (u,false) ≠ side (u,true)) ∧
      (∀ d, IsComplementComponent (⋃ v, (r v).val.image) (side d) ∧
        (frontier (side d) ∩ arcInterior M (r d.1)).Nonempty) ∧
      (∑ V ∈ F, (Finset.univ.filter (fun d => side d = V)).card) ≤ 2 * sigma.card := by
  classical
  obtain ⟨side,hne,hactual,_⟩ := actual_bad_edge_two_face_labels M r hr hd hbad
  refine ⟨side,hne,hactual,?_⟩
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ (Finset.univ : Finset ({v // v ∈ sigma} × Bool)).card :=
      Finset.card_filter_le _ _
    _ = 2 * sigma.card := by simp [Fintype.card_prod,Fintype.card_coe,Nat.mul_comm]

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_bad_edge_exact_incident_faces

#print axioms CurveComplex.HyperellipticModel.actual_bad_edge_two_face_labels
#print axioms CurveComplex.HyperellipticModel.actual_bad_split_side_incidence_identity

#print axioms CurveComplex.HyperellipticModel.actual_bad_split_side_degree_eq_contact
#print axioms CurveComplex.HyperellipticModel.actual_bad_split_side_incidence_le

namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance numericDegreeClassDecEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- The concrete numeric face degree needed by the Card12 consumers. -/
noncomputable def actualIncidentEdgeDegree (M : HyperellipticModel E S)
    {ι : Type} [Fintype ι] (r : ι → EssentialMarkedArc M) (V : Set S) : ℕ := by
  classical
  exact (Finset.univ.filter (fun u => (frontier V ∩ arcInterior M (r u)).Nonempty)).card

/-- The concrete number of actual faces incident to one actual edge. -/
noncomputable def actualEdgeIncidentFaceCount (M : HyperellipticModel E S)
    {ι : Type} (r : ι → EssentialMarkedArc M) (F : Finset (Set S)) (u : ι) : ℕ := by
  classical
  exact (F.filter (fun V => (frontier V ∩ arcInterior M (r u)).Nonempty)).card

/-- Exchange the two sums for literal geometric frontier contacts. -/
theorem actual_incident_degree_double_count
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M) (F : Finset (Set S)) :
    (∑ V ∈ F, actualIncidentEdgeDegree M r V) =
      ∑ u, actualEdgeIncidentFaceCount M r F u := by
  classical
  simp_rw [actualIncidentEdgeDegree,actualEdgeIncidentFaceCount,
    Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- The earlier geometric producer supplies the canonical numeric degree bound. -/
theorem actual_bad_incident_degree_sum_le
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V) :
    (∑ V ∈ F, actualIncidentEdgeDegree M r V) ≤ 2 * sigma.card :=
  actual_bad_total_face_edge_incidence_le M r hr hd hbad F hF

/-- A genuine covering face family has exactly two incident faces per all-bad
edge, as required by the canonical finite-cellulation consumer. -/
theorem actual_bad_edge_incident_face_count_eq_two
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V)
    (hcover : ∀ x ∈ (⋃ v, (r v).val.image)ᶜ, ∃ V ∈ F, x ∈ V)
    (u : {v // v ∈ sigma}) : actualEdgeIncidentFaceCount M r F u = 2 := by
  classical
  have hcomplete : ∀ V, IsComplementComponent (⋃ v, (r v).val.image) V → V ∈ F := by
    intro V hV
    obtain ⟨x,hx⟩ := hV.1
    obtain ⟨W,hWF,hxW⟩ := hcover x (hV.2.2.1 hx)
    have he : V = W := by
      by_contra hn
      exact Set.disjoint_left.mp (complementComponents_disjoint hV (hF W hWF) hn) hx hxW
    exact he.symm ▸ hWF
  obtain ⟨T,hcard,hT⟩ := actual_bad_edge_exact_incident_faces M r hr hd hbad u
  have he : F.filter (fun V => (frontier V ∩ arcInterior M (r u)).Nonempty) = T := by
    ext V
    constructor
    · intro hV
      obtain ⟨hVF,htouch⟩ := Finset.mem_filter.mp hV
      exact (hT V).2 ⟨hF V hVF,htouch⟩
    · intro hV
      obtain ⟨hglobal,htouch⟩ := (hT V).1 hV
      exact Finset.mem_filter.mpr ⟨hcomplete V hglobal,htouch⟩
  simpa [actualEdgeIncidentFaceCount,he] using hcard

/-- Concrete hincidence and htwo input packet for Card12EulerBridge; there is
no caller-supplied degree or edge-face-count certificate. -/
theorem actual_bad_card12_incidence_packet
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V)
    (hcover : ∀ x ∈ (⋃ v, (r v).val.image)ᶜ, ∃ V ∈ F, x ∈ V) :
    ((∑ V : {V // V ∈ F}, actualIncidentEdgeDegree M r V.val) =
      ∑ u, actualEdgeIncidentFaceCount M r F u) ∧
    (∀ u, actualEdgeIncidentFaceCount M r F u = 2) ∧
    (∑ V : {V // V ∈ F}, actualIncidentEdgeDegree M r V.val) = 2 * sigma.card := by
  classical
  have ht := actual_bad_edge_incident_face_count_eq_two M r hr hd hbad F hF hcover
  have hi : (∑ V : {V // V ∈ F}, actualIncidentEdgeDegree M r V.val) =
      ∑ u, actualEdgeIncidentFaceCount M r F u := by
    simpa only [Finset.sum_coe_sort] using actual_incident_degree_double_count M r F
  refine ⟨hi,ht,?_⟩
  rw [hi]
  calc
    _ = ∑ _u : {v // v ∈ sigma}, (2 : ℕ) :=
      Finset.sum_congr rfl (fun u _ => ht u)
    _ = 2 * sigma.card := by simp [Fintype.card_coe,Nat.mul_comm]
/-- The concrete weighted deficit before marking/hole classification. The bad
faces are computed from actual incidence; no bad-cardinality budget is assumed. -/
theorem actual_bad_low_degree_deficit_bound
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) sigma = sigma)
    (F : Finset (Set S))
    (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V) :
    3 * F.card ≤ 2 * sigma.card +
      3 * (F.filter (fun V => actualIncidentEdgeDegree M r V < 3)).card := by
  classical
  have hp : ∀ V ∈ F, (3 : ℕ) ≤ actualIncidentEdgeDegree M r V +
      3 * (if actualIncidentEdgeDegree M r V < 3 then 1 else 0) := by
    intro V hVF
    by_cases h : actualIncidentEdgeDegree M r V < 3
    · simp [h]
    · simp only [h,ite_false,mul_zero,add_zero]
      omega
  have hs := Finset.sum_le_sum hp
  have hdef : 3 * F.card ≤ (∑ V ∈ F, actualIncidentEdgeDegree M r V) +
      3 * (F.filter (fun V => actualIncidentEdgeDegree M r V < 3)).card := by
    have hcount : (∑ V ∈ F, 3 * (if actualIncidentEdgeDegree M r V < 3 then 1 else 0)) =
        3 * (F.filter (fun V => actualIncidentEdgeDegree M r V < 3)).card := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.sum_boole, Nat.cast_id]
    simp only [Finset.sum_add_distrib] at hs
    rw [hcount] at hs
    simpa [Nat.mul_comm] using hs
  exact hdef.trans (Nat.add_le_add_right
    (actual_bad_incident_degree_sum_le M r hr hd hbad F hF) _)

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_bad_card12_incidence_packet

#print axioms CurveComplex.HyperellipticModel.actual_bad_low_degree_deficit_bound
