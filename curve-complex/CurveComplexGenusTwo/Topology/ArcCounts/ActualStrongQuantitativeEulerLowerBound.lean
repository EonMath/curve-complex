import CurveComplexGenusTwo.Topology.ArcCounts.ActualArcNowhereDenseHeaders
import CurveComplexGenusTwo.Filtration.Geometry.ActualJordanRegionsHeader
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Logic.Relation
import Mathlib.Topology.Order.IntermediateValue
import Schoenflies.Concatenate
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2400000
theorem actual_strong_quantitative_euler_lower_bound (M : HyperellipticModel E S) {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    ∃ F : Finset (Set S), Fintype.card ι + (Finset.univ.image (fun i : ι => connectedComponentIn (⋃ j, (r j).val.image) ((r i).val.map 0))).card + 1 ≤
      F.card + (markedFamilyVertices (fun i => (r i).val)).card ∧
      ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U := by
  have hseed (M : HyperellipticModel E S) {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    ∃ P : Finset ι, P.card + (Finset.univ.image (fun i : ι => connectedComponentIn (⋃ j, (r j).val.image) ((r i).val.map 0))).card = (markedFamilyVertices (fun i => (r i).val)).card ∧
      P.card ≤ 5 ∧ ∀ i : ι, (r i).val.map 0 ≠ (r i).val.map 1 →
        (r i).val.map 0 ∈ (⋃ v : {v // v ∈ P}, (r v).val.image) ∧
        (r i).val.map 1 ∈ connectedComponentIn (⋃ v : {v // v ∈ P}, (r v).val.image) ((r i).val.map 0) := by
    have hforestcount {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
      Nat.card G.edgeSet + Nat.card G.ConnectedComponent = Fintype.card V := by
      classical
      letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
      have hedges :
        Nat.card G.edgeSet = ∑ c : G.ConnectedComponent, Nat.card c.toSimpleGraph.edgeSet := by
      
        classical
        letI : Fintype G.edgeSet := Fintype.ofFinite _
        letI (c : G.ConnectedComponent) : Fintype c.toSimpleGraph.edgeSet := Fintype.ofFinite _
        let f : (Σ c : G.ConnectedComponent, c.toSimpleGraph.edgeSet) → G.edgeSet :=
          fun z => ⟨z.2.val.map Subtype.val,z.1.toSimpleGraph_hom.map_mem_edgeSet z.2.property⟩
        have hf : Function.Bijective f := by
          constructor
          · intro z w h
            obtain ⟨c,e⟩ := z
            obtain ⟨d,k⟩ := w
            let x := e.val.out.1
            let y := e.val.out.2
            let u := k.val.out.1
            let v := k.val.out.2
            have he : s(x,y) = e.val := e.val.out_eq
            have hk : s(u,v) = k.val := k.val.out_eq
            have hp : s(x.val,y.val) = s(u.val,v.val) := by
              simpa only [f,← he,← hk,Sym2.map_mk] using congrArg Subtype.val h
            have hcd : c = d := by
              rcases Sym2.eq_iff.mp hp with h|h
              · exact x.property.symm.trans ((congrArg G.connectedComponentMk h.1).trans u.property)
              · exact x.property.symm.trans ((congrArg G.connectedComponentMk h.1).trans v.property)
            subst d
            have hek : e = k := Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
            cases hek
            rfl
          · intro e
            let x := e.val.out.1
            let y := e.val.out.2
            have he : s(x,y) = e.val := e.val.out_eq
            have hxy : G.Adj x y := G.mem_edgeSet.mp (he.symm ▸ e.property)
            let c := G.connectedComponentMk x
            have hx : x ∈ c.supp := rfl
            have hy : y ∈ c.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy.symm
            let k : c.toSimpleGraph.edgeSet := ⟨s(⟨x,hx⟩,⟨y,hy⟩),c.toSimpleGraph.mem_edgeSet.mpr hxy⟩
            refine ⟨⟨c,k⟩,?_⟩
            apply Subtype.ext
            exact he
        rw [Nat.card_eq_fintype_card,← Fintype.card_congr (Equiv.ofBijective f hf)]
        simp only [Fintype.card_sigma,Nat.card_eq_fintype_card]
      have hcomponents :
        (∑ c : G.ConnectedComponent, Nat.card c.toSimpleGraph.edgeSet) +
          Nat.card G.ConnectedComponent = Fintype.card V := by
      
        classical
        letI (c : G.ConnectedComponent) : Fintype c := Fintype.ofFinite _
        letI (c : G.ConnectedComponent) : Fintype c.toSimpleGraph.edgeSet := Fintype.ofFinite _
        have hc (c : G.ConnectedComponent) : Nat.card c.toSimpleGraph.edgeSet + 1 = Fintype.card c := by
          rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
          exact (hG.isTree_connectedComponent c).card_edgeFinset
        have hv : (∑ c : G.ConnectedComponent, Fintype.card c) = Fintype.card V := by
          calc
            _ = Fintype.card (Σ c : G.ConnectedComponent, c) := Fintype.card_sigma.symm
            _ = Fintype.card V := Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
        simpa only [← hv, ← hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_one, Nat.card_eq_fintype_card]
      rw [hedges]
      exact hcomponents
    have hactualcomponents (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
      (r : ι → EssentialMarkedArc M)
      (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
      :
      let V := markedFamilyVertices (fun i => (r i).val)
      let H : SimpleGraph {z // z ∈ V} := {
        Adj := fun x y => x ≠ y ∧ ∃ i,
          ((r i).val.map 0 = x.val ∧ (r i).val.map 1 = y.val) ∨
          ((r i).val.map 0 = y.val ∧ (r i).val.map 1 = x.val)
        symm := ⟨by
          intro x y h
          refine ⟨Ne.symm h.1,?_⟩
          obtain ⟨i,hi⟩ := h.2
          exact ⟨i,hi.elim Or.inr Or.inl⟩⟩
        loopless := ⟨by intro x h; exact h.1 rfl⟩ }
      let G : Set S := ⋃ i, (r i).val.image
      let C : Finset (Set S) := Finset.univ.image
        (fun i : ι => connectedComponentIn G ((r i).val.map 0))
      Nat.card H.ConnectedComponent = C.card := by
      have hreflect (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
        (r : ι → EssentialMarkedArc M)
        (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
        :
        let V := markedFamilyVertices (fun i => (r i).val)
        let H : SimpleGraph {z // z ∈ V} := {
          Adj := fun x y => x ≠ y ∧ ∃ i,
            ((r i).val.map 0 = x.val ∧ (r i).val.map 1 = y.val) ∨
            ((r i).val.map 0 = y.val ∧ (r i).val.map 1 = x.val)
          symm := ⟨by
            intro x y h
            refine ⟨Ne.symm h.1,?_⟩
            obtain ⟨i,hi⟩ := h.2
            exact ⟨i,hi.elim Or.inr Or.inl⟩⟩
          loopless := ⟨by intro x h; exact h.1 rfl⟩ }
        ∀ x y : {z // z ∈ V}, H.Reachable x y ↔
          y.val ∈ connectedComponentIn (⋃ i, (r i).val.image) x.val := by
        have hconnect (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
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
        classical
        intro V H
        let R : S → S → Prop := fun p q => ∃ i : ι,
          ((r i).val.map 0 = p ∧ (r i).val.map 1 = q) ∨
          ((r i).val.map 0 = q ∧ (r i).val.map 1 = p)
        have hV (x : S) : x ∈ V ↔ x ∈ (⋃ i, (r i).val.image) ∧ x ∈ M.cover.branch := by
          change x ∈ (markedFamilyVertices (fun i => (r i).val) : Set S) ↔ _
          rw [← markedFamily_graph_inter_branch]
          rfl
        have hRvertex {x y : S} (h : R x y) : x ∈ V ∧ y ∈ V := by
          obtain ⟨i,hi⟩ := h
          have hs : (r i).val.map 0 ∈ V := (hV _).mpr ⟨mem_iUnion.mpr ⟨i,mem_range_self 0⟩,(r i).val.start_marked⟩
          have he : (r i).val.map 1 ∈ V := (hV _).mpr ⟨mem_iUnion.mpr ⟨i,mem_range_self 1⟩,(r i).val.end_marked⟩
          rcases hi with ⟨h0,h1⟩|⟨h0,h1⟩
          · exact ⟨h0 ▸ hs,h1 ▸ he⟩
          · exact ⟨h1 ▸ he,h0 ▸ hs⟩
        have hlift {x y : S} (hx : x ∈ V) (h : Relation.ReflTransGen R x y) :
            ∀ hy : y ∈ V, H.Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
          induction h with
          | refl => intro hy; exact SimpleGraph.Reachable.refl _
          | @tail y z hxy hyz ih =>
            intro hz
            have hy := (hRvertex hyz).1
            apply (ih hy).trans
            by_cases he : y = z
            · subst z; exact SimpleGraph.Reachable.refl _
            · apply SimpleGraph.Adj.reachable
              exact ⟨fun he' => he (congrArg Subtype.val he'),hyz⟩
        have hwalk : ∀ {x y : {z // z ∈ V}}, H.Walk x y →
            y.val ∈ connectedComponentIn (⋃ i, (r i).val.image) x.val := by
          intro x y w
          induction w with
          | @nil z => exact mem_connectedComponentIn ((hV _).mp z.property).1
          | @cons x z y hxz w ih =>
            obtain ⟨i,hi⟩ := hxz.2
            have hxzarc : x.val ∈ (r i).val.image ∧ z.val ∈ (r i).val.image := by
              rcases hi with ⟨h0,h1⟩|⟨h0,h1⟩
              · exact ⟨⟨0,h0⟩,⟨1,h1⟩⟩
              · exact ⟨⟨1,h1⟩,⟨0,h0⟩⟩
            have hzC : z.val ∈ connectedComponentIn (⋃ i, (r i).val.image) x.val :=
              (markedArc_image_connected (r i).val).isPreconnected.subset_connectedComponentIn
                hxzarc.1 (fun q hq => mem_iUnion.mpr ⟨i,hq⟩) hxzarc.2
            exact (connectedComponentIn_eq hzC).symm ▸ ih
        intro x y
        constructor
        · rintro ⟨w⟩
          exact hwalk w
        · intro hcomp
          have hx := (hV x.val).mp x.property
          have hy := (hV y.val).mp y.property
          exact hlift x.property (hconnect M r hd x.val hx.2 hx.1 y.val hy.2 hcomp) y.property
      classical
      intro V H G C
      have href (x y : {z // z ∈ V}) : H.Reachable x y ↔
          y.val ∈ connectedComponentIn G x.val := hreflect M r hd x y
      have hV (x : S) : x ∈ V ↔ x ∈ G ∧ x ∈ M.cover.branch := by
        change x ∈ (markedFamilyVertices (fun i => (r i).val) : Set S) ↔ _
        rw [← markedFamily_graph_inter_branch]
        rfl
      have hC (z : {z // z ∈ V}) : connectedComponentIn G z.val ∈ C := by
        obtain ⟨i,hi⟩ := mem_iUnion.mp ((hV _).mp z.property).1
        have hs : (r i).val.map 0 ∈ connectedComponentIn G z.val :=
          (markedArc_image_connected (r i).val).isPreconnected.subset_connectedComponentIn
            hi (fun q hq => mem_iUnion.mpr ⟨i,hq⟩) (mem_range_self 0)
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(connectedComponentIn_eq hs).symm⟩
      let f : H.ConnectedComponent → {U // U ∈ C} := Quot.lift
        (fun z : {z // z ∈ V} => ⟨connectedComponentIn G z.val,hC z⟩)
        (by
          intro x y hxy
          apply Subtype.ext
          exact connectedComponentIn_eq ((href x y).mp hxy))
      have hf : Function.Bijective f := by
        constructor
        · intro c d
          refine Quot.inductionOn c ?_
          intro x
          refine Quot.inductionOn d ?_
          intro y h
          apply SimpleGraph.ConnectedComponent.sound
          apply (href x y).mpr
          have he : connectedComponentIn G x.val = connectedComponentIn G y.val := congrArg Subtype.val h
          rw [he]
          exact mem_connectedComponentIn ((hV _).mp y.property).1
        · intro U
          obtain ⟨i,_,hi⟩ := Finset.mem_image.mp U.property
          have hx : (r i).val.map 0 ∈ V := (hV _).mpr
            ⟨mem_iUnion.mpr ⟨i,mem_range_self 0⟩,(r i).val.start_marked⟩
          refine ⟨H.connectedComponentMk ⟨(r i).val.map 0,hx⟩,?_⟩
          apply Subtype.ext
          exact hi
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
        Nat.card_congr (Equiv.ofBijective f hf)
    classical
    let V := markedFamilyVertices (fun i => (r i).val)
    have hmem0 (i : ι) : (r i).val.map 0 ∈ V := by
      change (r i).val.map 0 ∈ (markedFamilyVertices (fun i => (r i).val) : Set S)
      rw [← markedFamily_graph_inter_branch]
      exact ⟨mem_iUnion.mpr ⟨i,mem_range_self 0⟩,(r i).val.start_marked⟩
    have hmem1 (i : ι) : (r i).val.map 1 ∈ V := by
      change (r i).val.map 1 ∈ (markedFamilyVertices (fun i => (r i).val) : Set S)
      rw [← markedFamily_graph_inter_branch]
      exact ⟨mem_iUnion.mpr ⟨i,mem_range_self 1⟩,(r i).val.end_marked⟩
    let H : SimpleGraph {z // z ∈ V} := {
      Adj := fun x y => x ≠ y ∧ ∃ i,
        ((r i).val.map 0 = x.val ∧ (r i).val.map 1 = y.val) ∨
        ((r i).val.map 0 = y.val ∧ (r i).val.map 1 = x.val)
      symm := ⟨by intro x y h; exact ⟨Ne.symm h.1,by obtain ⟨i,hi⟩ := h.2; exact ⟨i,hi.elim Or.inr Or.inl⟩⟩⟩
      loopless := ⟨by intro x h; exact h.1 rfl⟩ }
    obtain ⟨i0⟩ := ‹Nonempty ι›
    letI : Nonempty {z // z ∈ V} := ⟨⟨(r i0).val.map 0,hmem0 i0⟩⟩
    obtain ⟨Q,hQH,hQA,hreach⟩ := H.exists_isAcyclic_reachable_eq_le
    letI : Fintype Q.edgeSet := Fintype.ofFinite _
    let C : Finset (Set S) := Finset.univ.image
      (fun i : ι => connectedComponentIn (⋃ j, (r j).val.image) ((r i).val.map 0))
    have hcc : Nat.card Q.ConnectedComponent = Nat.card H.ConnectedComponent :=
      Nat.card_congr (Quot.congrRight (fun x y => by rw [hreach]))
    have hHcc : Nat.card H.ConnectedComponent = C.card := hactualcomponents M r hd
    have hQcard : Nat.card Q.edgeSet + C.card = V.card := by
      have hcount := hforestcount Q hQA
      rw [hcc,hHcc] at hcount
      simpa using hcount
    have hCpos : 1 ≤ C.card := by
      exact Finset.one_le_card.mpr ⟨_,Finset.mem_image.mpr ⟨i0,Finset.mem_univ _,rfl⟩⟩
    let L : ι → Sym2 {z // z ∈ V} := fun i => s(⟨(r i).val.map 0,hmem0 i⟩,⟨(r i).val.map 1,hmem1 i⟩)
    have hlabel : ∀ e : Q.edgeSet, ∃ i : ι, L i = e.val := by
      intro e
      let x := e.val.out.1
      let y := e.val.out.2
      have he : s(x,y) = e.val := e.val.out_eq
      have hxy : Q.Adj x y := Q.mem_edgeSet.mp (he.symm ▸ e.property)
      obtain ⟨i,hi⟩ := (hQH hxy).2
      refine ⟨i,?_⟩
      rw [← he]
      rcases hi with ⟨h0,h1⟩|⟨h0,h1⟩
      · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h0,Subtype.ext h1⟩)
      · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h0,Subtype.ext h1⟩)
    choose f hf using hlabel
    have hfinj : Function.Injective f := by
      intro e d hed
      apply Subtype.ext
      exact (hf e).symm.trans ((congrArg L hed).trans (hf d))
    let P : Finset ι := Finset.univ.image f
    let GP : Set S := ⋃ i : {i // i ∈ P}, (r i).val.image
    have hPcard : P.card = Nat.card Q.edgeSet := by
      rw [Finset.card_image_of_injective _ hfinj]
      simp [Nat.card_eq_fintype_card]
    have hedge {x y : {z // z ∈ V}} (hxy : Q.Adj x y) :
        ∃ i ∈ P, x.val ∈ (r i).val.image ∧ y.val ∈ (r i).val.image := by
      let e : Q.edgeSet := ⟨s(x,y),Q.mem_edgeSet.mpr hxy⟩
      have hi : L (f e) = s(x,y) := hf e
      have he :
          (⟨(r (f e)).val.map 0,hmem0 (f e)⟩ : {z // z ∈ V}) = x ∧
          (⟨(r (f e)).val.map 1,hmem1 (f e)⟩ : {z // z ∈ V}) = y ∨
          (⟨(r (f e)).val.map 0,hmem0 (f e)⟩ : {z // z ∈ V}) = y ∧
          (⟨(r (f e)).val.map 1,hmem1 (f e)⟩ : {z // z ∈ V}) = x := by
        simpa only [L,Sym2.eq_iff] using hi
      refine ⟨f e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩,?_⟩
      rcases he with ⟨h0,h1⟩|⟨h0,h1⟩
      · exact ⟨⟨0,congrArg Subtype.val h0⟩,⟨1,congrArg Subtype.val h1⟩⟩
      · exact ⟨⟨1,congrArg Subtype.val h1⟩,⟨0,congrArg Subtype.val h0⟩⟩
  
    have hwalk : ∀ {x y : {z // z ∈ V}} (w : Q.Walk x y),
        x.val ∈ GP → y.val ∈ connectedComponentIn GP x.val := by
      intro x y w
      induction w with
      | nil => exact mem_connectedComponentIn
      | @cons x z y hxz w ih =>
        intro hx
        obtain ⟨j,hj,hxj,hzj⟩ := hedge hxz
        have hsub : (r j).val.image ⊆ GP := fun p hp => mem_iUnion.mpr ⟨⟨j,hj⟩,hp⟩
        have hzGP : z.val ∈ GP := hsub hzj
        have hzC : z.val ∈ connectedComponentIn GP x.val :=
          (markedArc_image_connected (r j).val).isPreconnected.subset_connectedComponentIn hxj hsub hzj
        have he : connectedComponentIn GP x.val = connectedComponentIn GP z.val := connectedComponentIn_eq hzC
        exact he.symm ▸ ih hzGP
    refine ⟨P,?_,?_,?_⟩
    · change P.card + C.card = V.card
      rw [hPcard]
      exact hQcard
    · have hv : V.card ≤ 6 := markedFamilyVertices_card_le_six _
      rw [hPcard]
      omega
    · intro i hni
      let x : {z // z ∈ V} := ⟨(r i).val.map 0,hmem0 i⟩
      let y : {z // z ∈ V} := ⟨(r i).val.map 1,hmem1 i⟩
      have hne : x ≠ y := fun he => hni (congrArg Subtype.val he)
      have hxy : H.Adj x y := ⟨hne,⟨i,Or.inl ⟨rfl,rfl⟩⟩⟩
      have hQxy : Q.Reachable x y := by rw [hreach]; exact hxy.reachable
      obtain ⟨w⟩ := hQxy
      obtain ⟨j,hj,hxj,hzj⟩ := hedge (w.adj_snd (w.not_nil_of_ne hne))
      have hxGP : x.val ∈ GP := mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩
      exact ⟨hxGP,hwalk w hxGP⟩
  have hlower (M : HyperellipticModel E S) {ι : Type} [DecidableEq ι] [Nonempty ι]
      (r : ι → EssentialMarkedArc M)
      (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
      (P I : Finset ι) (hdis : Disjoint P I)
      (hcompat : ∀ i ∈ I, (r i).val.map 0 ≠ (r i).val.map 1 →
        (r i).val.map 0 ∈ (⋃ v : {v // v ∈ P}, (r v).val.image) ∧
        (r i).val.map 1 ∈ connectedComponentIn (⋃ v : {v // v ∈ P}, (r v).val.image) ((r i).val.map 0)) :
      ∃ F : Finset (Set S), I.card + 1 ≤ F.card ∧
        ∀ U ∈ F, IsComplementComponent (⋃ v : {v // v ∈ P ∪ I}, (r v).val.image) U := by
    have hcycle (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
        (r : ι → EssentialMarkedArc M)
        (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
        (a : EssentialMarkedArc M) (haNL : a.val.map 0 ≠ a.val.map 1)
        (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
        (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
        (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
        (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0))
        (F : Finset (Set S))
        (hF : ∀ V ∈ F, IsComplementComponent (⋃ v, (r v).val.image) V) :
        ∃ F' : Finset (Set S), F.card + 1 ≤ F'.card ∧
          ∀ V ∈ F', IsComplementComponent ((⋃ v, (r v).val.image) ∪ a.val.image) V := by
      have hcycle (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
          (r : ι → EssentialMarkedArc M)
          (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
          (a : EssentialMarkedArc M) (haNL : a.val.map 0 ≠ a.val.map 1)
          (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
          (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
          (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
          (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0)) :
          ∃ U : Set S, IsComplementComponent (⋃ v, (r v).val.image) U ∧
            a.val.image ⊆ U ∪ (⋃ v, (r v).val.image) ∧
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
          have hconnect :
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
          have hpath : ∀ (p x y : S), (p ∉ ⋃ v, (r v).val.image) →
              (x ∈ ⋃ v, (r v).val.image) → (y ∈ ⋃ v, (r v).val.image) → x ≠ y →
              Relation.ReflTransGen
                (fun q z => ∃ v : ι,
                  ((r v).val.map 0 = q ∧ (r v).val.map 1 = z) ∨
                  ((r v).val.map 0 = z ∧ (r v).val.map 1 = q)) x y →
              ∃ f : C(Interval,S), Function.Injective f ∧ f 0 = x ∧ f 1 = y ∧
                Set.range f ⊆ ⋃ v, (r v).val.image := by
            intro p x y hp hx hy hne hchain  
            classical
            let G := ⋃ v, (r v).val.image
            let R : S → S → Prop := fun q z => ∃ v : ι,
              ((r v).val.map 0 = q ∧ (r v).val.map 1 = z) ∨
              ((r v).val.map 0 = z ∧ (r v).val.map 1 = q)
            let H : SimpleGraph S := {
              Adj := fun q z => q ≠ z ∧ R q z
              symm := ⟨by
                intro q z h
                refine ⟨h.1.symm,?_⟩
                obtain ⟨v,hv⟩ := h.2
                exact ⟨v,hv.elim Or.inr Or.inl⟩⟩
              loopless := ⟨fun q h => h.1 rfl⟩ }
            have hreach : H.Reachable x y := by
              apply (H.reachable_iff_reflTransGen x y).mpr
              exact Relation.ReflTransGen.lift' (r := R) (p := H.Adj) (id : S → S) (fun q z h => by
                by_cases he : q = z
                · subst z; exact Relation.ReflTransGen.refl
                · exact Relation.ReflTransGen.single ⟨he,h⟩) x y hchain
            let e := M.puncturedPlane p
            let φ : S → Schoenflies.Plane := fun z => if hz : z ≠ p then e ⟨z,hz⟩ else 0
            let g : ι → Interval → Schoenflies.Plane := fun v t => e ⟨(r v).val.map t, by
              intro he
              exact hp (he ▸ Set.mem_iUnion.mpr ⟨v,Set.mem_range_self t⟩)⟩
            have hgφ : ∀ v t, g v t = φ ((r v).val.map t) := by
              intro v t
              dsimp [g,φ]
              rw [dite_eq_left]
            have hArc : ∀ {u w : S}, H.Adj u w → ∃ i : ι,
                Schoenflies.IsArcBetween (Set.range (g i)) (φ u) (φ w) ∧
                (((r i).val.map 0 = u ∧ (r i).val.map 1 = w) ∨
                ((r i).val.map 0 = w ∧ (r i).val.map 1 = u)) := by
              intro u w h
              obtain ⟨i,hi⟩ := h.2
              have hni : (r i).val.map 0 ≠ (r i).val.map 1 := by
                intro he
                rcases hi with hi | hi
                · exact h.1 (hi.1.symm.trans (he.trans hi.2))
                · exact h.1 (hi.2.symm.trans (he.symm.trans hi.1))
              let a : NonLoopArc M := ⟨(r i).val,hni⟩
              have hpi : p ∉ a.val.image := fun he => hp (Set.mem_iUnion.mpr ⟨i,he⟩)
              have ha : Schoenflies.IsArcBetween (Set.range (g i)) (g i 0) (g i 1) :=
                a.plane_isArcBetween p hpi
              refine ⟨i,?_,hi⟩
              rcases hi with hi | hi
              · simpa only [hgφ,hi.1,hi.2] using ha
              · simpa only [hgφ,hi.1,hi.2] using ha.reverse
            let T : List S → Set Schoenflies.Plane := fun L => {z | ∃ i : ι,
              (r i).val.map 0 ∈ L ∧ (r i).val.map 1 ∈ L ∧ z ∈ Set.range (g i)}
            have hTmono : ∀ {L K : List S}, (∀ z ∈ L, z ∈ K) → T L ⊆ T K := by
              intro L K h z hz
              obtain ⟨i,hi0,hi1,hzi⟩ := hz
              exact ⟨i,h _ hi0,h _ hi1,hzi⟩
            have hwalk : ∀ {u v : S} (W : H.Walk u v), W.IsPath → u ≠ v →
                ∃ P : Set Schoenflies.Plane, Schoenflies.IsArcBetween P (φ u) (φ v) ∧ P ⊆ T W.support := by
              intro u v W
              induction W with
              | nil => intro _ hn; exact False.elim (hn rfl)
              | @cons u w v hadj W ih =>
                intro hpath hn
                have htail : W.IsPath := hpath.of_cons
                have hun : u ∉ W.support := (SimpleGraph.Walk.cons_isPath_iff hadj W).mp hpath |>.2
                obtain ⟨i,hiArc,hiends⟩ := hArc hadj
                have hiT : Set.range (g i) ⊆ T (u :: W.support) := by
                  intro z hz
                  rcases hiends with hiends | hiends
                  · exact ⟨i,List.mem_cons.mpr (Or.inl hiends.1),
                      List.mem_cons.mpr (Or.inr (hiends.2 ▸ W.start_mem_support)),hz⟩
                  · exact ⟨i,List.mem_cons.mpr (Or.inr (hiends.1 ▸ W.start_mem_support)),
                      List.mem_cons.mpr (Or.inl hiends.2),hz⟩
                by_cases hneTail : w ≠ v
                · obtain ⟨P,hP,hPT⟩ := ih htail hneTail
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
                  refine ⟨Set.range (g i) ∪ P,hiArc.concatenate hP hmeet,?_⟩
                  intro z hz
                  rcases hz with hz | hz
                  · exact hiT hz
                  · exact hTmono (fun z hz => List.mem_cons.mpr (Or.inr hz)) (hPT hz)
                · have he : w = v := not_ne_iff.mp hneTail
                  subst v
                  have hnil : W = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil).mp htail
                  subst W
                  exact ⟨Set.range (g i),hiArc,hiT⟩
            obtain ⟨W,hW⟩ := hreach.exists_isPath
            obtain ⟨P,hP,hPT⟩ := hwalk W hW hne
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
            refine ⟨⟨fS,hfcS⟩,hfiS,?_,?_,?_⟩
            · change (e.symm (f 0)).val = x
              rw [hf0,hφx,e.symm_apply_apply]
            · change (e.symm (f 1)).val = y
              rw [hf1,hφy,e.symm_apply_apply]
            · rintro z ⟨t,rfl⟩
              have hfmem : f t ∈ P := hfim ▸ Set.mem_image_of_mem f t.property
              obtain ⟨i,_,_,s,hs⟩ := hPT hfmem
              have he : (e.symm (f t)).val = (r i).val.map s := by
                rw [← hs]
                change (e.symm (e _)).val = _
                rw [e.symm_apply_apply]
              change (e.symm (f t)).val ∈ ⋃ v, (r v).val.image
              rw [he]
              exact Set.mem_iUnion.mpr ⟨i,Set.mem_range_self s⟩
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
          have hchain := hconnect (a.val.map 0) a.val.start_marked h0
            (a.val.map 1) a.val.end_marked hc
          obtain ⟨b,hbi,hb0,hb1,hbG⟩ := hpath (a.val.map t) (a.val.map 0)
            (a.val.map 1) hp h0 h1 a.property hchain
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
          obtain ⟨c,hcimage⟩ := CurveComplex.exists_curve_of_two_arcs f b a.injective hbi hb0.symm hb1.symm hinter
          exact ⟨b,c,hbi,hb0,hb1,hbG,hcimage⟩
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
        refine ⟨U,hU,hinc,{A,B},Finset.card_pair hne,?_⟩
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
      have hinsert (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
          (r : ι → MarkedArc M) (a : MarkedArc M) (U : Set S)
          (hU : IsComplementComponent (⋃ i, (r i).image) U)
          (hplaced : a.image ⊆ U ∪ (⋃ i, (r i).image)) :
          ∀ V : Set S,
            IsComplementComponent ((⋃ i, (r i).image) ∪ a.image) V ↔
            (IsComplementComponent (⋃ i, (r i).image) V ∧ V ≠ U) ∨
            IsComplementComponent (Uᶜ ∪ a.image) V := by
        let G := ⋃ i, (r i).image
        have hGU : G ⊆ Uᶜ := fun x hx hxU => hU.2.2.1 hxU hx
        have hpreserve : ∀ W : Set S, IsComplementComponent G W → W ≠ U →
            IsComplementComponent (G ∪ a.image) W := by
          intro W hW hne
          apply complementComponent_of_graph_enlargement hW (subset_union_left)
          apply Set.disjoint_left.mpr
          intro x hxW hxnew
          rcases hxnew with hxG | hxa
          · exact hW.2.2.1 hxW hxG
          · rcases hplaced hxa with hxU | hxG
            · exact Set.disjoint_left.mp (complementComponents_disjoint hW hU hne) hxW hxU
            · exact hW.2.2.1 hxW hxG
        have hlocal : ∀ V : Set S, IsComplementComponent (Uᶜ ∪ a.image) V →
            IsComplementComponent (G ∪ a.image) V := by
          intro V hV
          have hVU : V ⊆ U := by
            intro x hx
            by_contra hn
            exact hV.2.2.1 hx (Or.inl hn)
          have hVH : V ⊆ (G ∪ a.image)ᶜ := by
            intro x hx h
            rcases h with hxG | hxa
            · exact hGU hxG (hVU hx)
            · exact hV.2.2.1 hx (Or.inr hxa)
          refine ⟨hV.1,hV.2.1,hVH,?_⟩
          intro W hW hVW hWH
          obtain ⟨x,hxV⟩ := hV.1
          have hWG : W ⊆ Gᶜ := fun y hy hG => hWH hy (Or.inl hG)
          have hWComp : W ⊆ connectedComponentIn Gᶜ x :=
            hW.isPreconnected.subset_connectedComponentIn (hVW hxV) hWG
          have hUComp : U = connectedComponentIn Gᶜ x := by
            obtain ⟨z,hz,he⟩ := complementComponent_iff_componentIn.mp hU
            rw [he]
            exact connectedComponentIn_eq (he ▸ hVU hxV)
          have hWU : W ⊆ U := hUComp.symm ▸ hWComp
          have hWL : W ⊆ (Uᶜ ∪ a.image)ᶜ := by
            intro y hy h
            rcases h with hn | ha
            · exact hn (hWU hy)
            · exact hWH hy (Or.inr ha)
          exact hV.2.2.2 W hW hVW hWL
        intro V
        constructor
        · intro hV
          obtain ⟨x,hxV⟩ := hV.1
          have hxG : x ∈ Gᶜ := fun hx => hV.2.2.1 hxV (Or.inl hx)
          let W := connectedComponentIn Gᶜ x
          have hW : IsComplementComponent G W :=
            complementComponent_iff_componentIn.mpr ⟨x,hxG,rfl⟩
          have hVW : V ⊆ W := hV.2.1.isPreconnected.subset_connectedComponentIn hxV
            (fun y hy hG => hV.2.2.1 hy (Or.inl hG))
          by_cases he : W = U
          · right
            have hVU : V ⊆ U := he ▸ hVW
            have hVL : V ⊆ (Uᶜ ∪ a.image)ᶜ := by
              intro y hy h
              rcases h with hn | ha
              · exact hn (hVU hy)
              · exact hV.2.2.1 hy (Or.inr ha)
            refine ⟨hV.1,hV.2.1,hVL,?_⟩
            intro T hT hVT hTL
            have hTH : T ⊆ (G ∪ a.image)ᶜ := by
              intro y hy h
              rcases h with hG | ha
              · exact hTL hy (Or.inl (hGU hG))
              · exact hTL hy (Or.inr ha)
            exact hV.2.2.2 T hT hVT hTH
          · left
            have hWH := hpreserve W hW he
            have hWV : W = V := hV.2.2.2 W hWH.2.1 hVW hWH.2.2.1
            exact ⟨hWV ▸ hW, hWV ▸ he⟩
        · rintro (⟨hV,hne⟩ | hV)
          · exact hpreserve V hV hne
          · exact hlocal V hV
      classical
      obtain ⟨U,hU,hplace,H,hHcard,hH⟩ := hcycle M r hd a haNL ha h0 h1 hc
      have hdis : Disjoint (F.erase U) H := by
        apply Finset.disjoint_left.mpr
        intro V hVF hVH
        obtain ⟨hVU,hVF⟩ := Finset.mem_erase.mp hVF
        have hV := hF V hVF
        have hHV := (hH V).mpr hVH
        obtain ⟨x,hx⟩ := hHV.1
        have hxU : x ∈ U := by
          by_contra hn
          exact hHV.2.2.1 hx (Or.inl hn)
        exact disjoint_left.mp (complementComponents_disjoint hV hU hVU) hx hxU
      let F' := F.erase U ∪ H
      have hcard : F.card + 1 ≤ F'.card := by
        rw [Finset.card_union_of_disjoint hdis,hHcard]
        have hc : F.card ≤ (F.erase U).card + 1 := by
          by_cases hUF : U ∈ F
          · exact (Finset.card_erase_add_one hUF).ge
          · rw [Finset.erase_eq_of_notMem hUF]
            omega
        omega
      refine ⟨F',hcard,?_⟩
      intro V hVF
      apply (hinsert M (fun v => (r v).val) a.val U hU hplace V).mpr
      rcases Finset.mem_union.mp hVF with hVF|hVH
      · obtain ⟨hne,hVF⟩ := Finset.mem_erase.mp hVF
        exact Or.inl ⟨hF V hVF,hne⟩
      · exact Or.inr ((hH V).mpr hVH)
    have hnonloop (M : HyperellipticModel E S) (a : NonLoopArc M) : IsNowhereDense a.val.image := by
      have hpuncture (M : HyperellipticModel E S) {U : Set S} (hU : IsOpen U)
          (hcU : IsConnected U) (p : S) : IsConnected (U \ {p}) := by
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
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
      have hclosed : IsClosed a.val.image := (markedArc_image_compact a.val).isClosed
      change interior (closure a.val.image) = ∅
      rw [hclosed.closure_eq]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      let U := connectedComponentIn (interior a.val.image) x
      have hxU : x ∈ U := mem_connectedComponentIn hx
      have hUopen : IsOpen U := isOpen_interior.connectedComponentIn
      have hUconn : IsConnected U := isConnected_connectedComponentIn_iff.mpr hx
      have hUsub : U ⊆ a.val.image := (connectedComponentIn_subset _ _).trans interior_subset
      have hVopen : IsOpen (a.val.map ⁻¹' U) := hUopen.preimage a.val.continuous
      obtain ⟨t0,ht0⟩ := hUsub hxU
      have hVne : (a.val.map ⁻¹' U).Nonempty := ⟨t0,by change a.val.map t0 ∈ U; rw [ht0]; exact hxU⟩
      have hdense : Dense (Set.Ioo (0 : Interval) 1) := by
        rw [dense_iff_closure_eq,closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
        ext t
        simp only [Set.mem_Icc,Set.mem_univ,iff_true]
        exact ⟨unitInterval.nonneg t,unitInterval.le_one t⟩
      obtain ⟨t,htV,htI⟩ := hdense.inter_open_nonempty _ hVopen hVne
      have htclL : t ∈ closure (Set.Ioo (0 : Interval) t) := by
        rw [closure_Ioo (ne_of_lt htI.1)]
        exact ⟨htI.1.le,le_rfl⟩
      have htclR : t ∈ closure (Set.Ioo t (1 : Interval)) := by
        rw [closure_Ioo (ne_of_lt htI.2)]
        exact ⟨le_rfl,htI.2.le⟩
      obtain ⟨s,hsV,hsI⟩ := mem_closure_iff.mp htclL _ hVopen htV
      obtain ⟨v,hvV,hvI⟩ := mem_closure_iff.mp htclR _ hVopen htV
      have hc : IsConnected (U \ {a.val.map t}) := hpuncture M hUopen hUconn (a.val.map t)
      have hparam : IsConnected (a.val.map ⁻¹' (U \ {a.val.map t})) :=
        hc.preimage_of_isClosedMap a.injective a.val.continuous.isClosedMap (fun z hz => hUsub hz.1)
      have hs : s ∈ a.val.map ⁻¹' (U \ {a.val.map t}) :=
        ⟨hsV,fun he => (ne_of_lt hsI.2) (a.injective (Set.mem_singleton_iff.mp he))⟩
      have hv : v ∈ a.val.map ⁻¹' (U \ {a.val.map t}) :=
        ⟨hvV,fun he => (ne_of_gt hvI.1) (a.injective (Set.mem_singleton_iff.mp he))⟩
      have ht : t ∈ a.val.map ⁻¹' (U \ {a.val.map t}) :=
        hparam.isPreconnected.ordConnected.out hs hv ⟨hsI.2.le,hvI.1.le⟩
      exact ht.2 (Set.mem_singleton _)
    have hloop (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
        (r : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
        (hloop : a.val.map 0 = a.val.map 1)
        (ha : ∀ i, Disjoint (arcInterior M a) (arcInterior M (r i)))
        (F : Finset (Set S))
        (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
        ∃ F' : Finset (Set S), F.card + 1 ≤ F'.card ∧
          ∀ U ∈ F', IsComplementComponent ((⋃ i, (r i).val.image) ∪ a.val.image) U := by
      have hregions (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
          (hloop : a.val.map 0 = a.val.map 1) :
          ∃ A B : Set S, IsComplementComponent a.val.image A ∧
            IsComplementComponent a.val.image B ∧ Disjoint A B ∧
            frontier A = a.val.image ∧ frontier B = a.val.image := by
        classical
        have hcomponent : ∀ (g : CurveComplex.SpherePort.Sphere ≃ₜ S)
            {A U : Set CurveComplex.SpherePort.Sphere},
            IsComplementComponent A U → IsComplementComponent (g '' A) (g '' U) := by
          intro g A U hU
          rcases hU with ⟨hne, hconn, hsub, hmax⟩
          refine ⟨hne.image g, hconn.image g g.continuous.continuousOn, ?_, ?_⟩
          · rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
            exact hsub hx (g.injective heq ▸ hy)
          · intro V hV hUV hVA
            have hUV' : U ⊆ g.symm '' V := by
              intro x hx
              exact ⟨g x, hUV ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩
            have hVA' : g.symm '' V ⊆ Aᶜ := by
              rintro _ ⟨x, hx, rfl⟩ ha
              exact hVA hx ⟨g.symm x, ha, g.apply_symm_apply x⟩
            have hEq := hmax (g.symm '' V) (hV.image g.symm g.symm.continuous.continuousOn)
              hUV' hVA'
            calc
              V = g '' (g.symm '' V) := by
                ext x
                simp only [Set.mem_image]
                constructor
                · intro hx; exact ⟨g.symm x, ⟨x, hx, rfl⟩, g.apply_symm_apply x⟩
                · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
              _ = g '' U := congrArg (fun W : Set CurveComplex.SpherePort.Sphere => g '' W) hEq
      
      
        let J : CurveComplex.SpherePort.JordanCurve := {
          map := M.sphere ∘ a.val.map
          continuous := M.sphere.continuous.comp a.val.continuous
          injective_except_ends := fun t u h => a.val.injective_except_loop_closure t u (M.sphere.injective h)
          closed := congrArg M.sphere hloop }
        have hJ : J.image = M.sphere '' a.val.image := Set.range_comp M.sphere a.val.map
        obtain ⟨p, hpmark, hpne⟩ := Finset.exists_mem_ne
          (by rw [M.cover.branch_card]; norm_num : 1 < M.cover.branch.card) (a.val.map 0)
        have hpJ : M.sphere p ∉ J.image := by
          rintro ⟨t, ht⟩
          have htp : a.val.map t = p := M.sphere.injective ht
          have htm : a.val.map t ∈ M.cover.branch := by simpa only [htp] using hpmark
          rcases a.val.marked_only_at_ends t htm with ht | ht
          · exact hpne (htp.symm.trans (congrArg a.val.map ht))
          · exact hpne ((htp.symm.trans (congrArg a.val.map ht)).trans hloop.symm)
        let P : CurveComplex.SpherePort.Chart J := {
          puncture := M.sphere p
          avoids := hpJ
          plane := puncturedSpherePlane (M.sphere p) }
        obtain ⟨U,V,hU,hV,_,_,hdisj,hne,hcover,hfrU,hfrV⟩ := sphereJordan_two_regions J P
        have hback : M.sphere.symm '' J.image = a.val.image := by
          rw [hJ, ← image_comp, M.sphere.symm_comp_self, image_id]
        have hcU := hcomponent M.sphere.symm hU
        have hcV := hcomponent M.sphere.symm hV
        rw [hback] at hcU hcV
        let A := M.sphere.symm '' U
        let B := M.sphere.symm '' V
        have hneAB : A ≠ B := fun he => hne ((Set.image_injective.mpr M.sphere.symm.injective) he)
        have hAB : A ∪ B = a.val.imageᶜ := by
          rw [← Set.image_union, hcover, M.sphere.symm.image_compl, hback]
        refine ⟨A,B,hcU,hcV,?_,?_,?_⟩
        · exact hdisj.image M.sphere.symm.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
        · rw [← M.sphere.symm.image_frontier,hfrU,hback]
        · rw [← M.sphere.symm.image_frontier,hfrV,hback]
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
      let G := ⋃ i, (r i).val.image
      have hG : IsClosed G := isClosed_iUnion_of_finite (fun i => (markedArc_image_compact (r i).val).isClosed)
      have haClosed : IsClosed a.val.image := (markedArc_image_compact a.val).isClosed
      have haInt : interior a.val.image = ∅ := by
        have hnd := actual_loop_nowhereDense M a.val hloop
        change interior (closure a.val.image) = ∅ at hnd
        rwa [haClosed.closure_eq] at hnd
      let t : Interval := ⟨1/2,by norm_num⟩
      have hm : a.val.map t ∉ M.cover.branch := by
        intro hm
        rcases a.val.marked_only_at_ends t hm with ht|ht
        · have he := congrArg Subtype.val ht; norm_num [t] at he
        · have he := congrArg Subtype.val ht; norm_num [t] at he
      have hmid : a.val.map t ∉ G := by
        intro hg
        obtain ⟨i,hi⟩ := mem_iUnion.mp hg
        exact Set.disjoint_left.mp (ha i) ⟨mem_range_self t,hm⟩ ⟨hi,hm⟩
      let U := connectedComponentIn Gᶜ (a.val.map t)
      have hU : IsComplementComponent G U := complementComponent_iff_componentIn.mpr ⟨a.val.map t,hmid,rfl⟩
      have hUopen : IsOpen U := complementComponent_open hG hU
      have hmidU : a.val.map t ∈ U := mem_connectedComponentIn hmid
      obtain ⟨A,B,hA,hB,hdis,hfrA,hfrB⟩ := hregions M a hloop
      have hchoice : ∀ Q : Set S, IsComplementComponent G Q →
          ∃ V : Set S, IsComplementComponent (G ∪ a.val.image) V ∧ V ⊆ Q := by
        intro Q hQ
        have hopen : IsOpen Q := complementComponent_open hG hQ
        have hpoint : ∃ x ∈ Q, x ∉ a.val.image := by
          by_contra hn
          have hsub : Q ⊆ a.val.image := by intro x hx; by_contra ha; exact hn ⟨x,hx,ha⟩
          have hsubI : Q ⊆ interior a.val.image := by rw [← hopen.interior_eq]; exact interior_mono hsub
          obtain ⟨x,hx⟩ := hQ.1
          have hi := hsubI hx
          rw [haInt] at hi
          exact hi
        obtain ⟨x,hxQ,hxa⟩ := hpoint
        have hxc : x ∈ (G ∪ a.val.image)ᶜ := fun h => h.elim (hQ.2.2.1 hxQ) hxa
        let V := connectedComponentIn (G ∪ a.val.image)ᶜ x
        have hV : IsComplementComponent (G ∪ a.val.image) V := complementComponent_iff_componentIn.mpr ⟨x,hxc,rfl⟩
        have hEq : Q = connectedComponentIn Gᶜ x :=
          (hQ.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hQ.2.2.1 hxQ))
            (hQ.2.1.isPreconnected.subset_connectedComponentIn hxQ hQ.2.2.1)
            (connectedComponentIn_subset _ _)).symm
        refine ⟨V,hV,?_⟩
        rw [hEq]
        exact connectedComponentIn_mono x (fun z hz => fun hg => hz (Or.inl hg))
      have hside (R : Set S) (hR : IsComplementComponent a.val.image R) (hfr : frontier R = a.val.image) :
          ∃ V : Set S, IsComplementComponent (G ∪ a.val.image) V ∧ V ⊆ U ∧ V ⊆ R := by
        have hmfr : a.val.map t ∈ frontier R := hfr.symm ▸ mem_range_self t
        obtain ⟨x,hxU,hxR⟩ := mem_closure_iff.mp (frontier_subset_closure hmfr) U hUopen hmidU
        have hxnew : x ∈ (G ∪ a.val.image)ᶜ := fun h => h.elim (hU.2.2.1 hxU) (hR.2.2.1 hxR)
        let V := connectedComponentIn (G ∪ a.val.image)ᶜ x
        have hV : IsComplementComponent (G ∪ a.val.image) V := complementComponent_iff_componentIn.mpr ⟨x,hxnew,rfl⟩
        have heU : U = connectedComponentIn Gᶜ x :=
          (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hU.2.2.1 hxU))
            (hU.2.1.isPreconnected.subset_connectedComponentIn hxU hU.2.2.1)
            (connectedComponentIn_subset _ _)).symm
        have heR : R = connectedComponentIn a.val.imageᶜ x :=
          (hR.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hR.2.2.1 hxR))
            (hR.2.1.isPreconnected.subset_connectedComponentIn hxR hR.2.2.1)
            (connectedComponentIn_subset _ _)).symm
        refine ⟨V,hV,?_,?_⟩
        · rw [heU]; exact connectedComponentIn_mono x (fun z hz hg => hz (Or.inl hg))
        · rw [heR]; exact connectedComponentIn_mono x (fun z hz hg => hz (Or.inr hg))
      obtain ⟨V,hV,hVU,hVA⟩ := hside A hA hfrA
      obtain ⟨W,hW,hWU,hWB⟩ := hside B hB hfrB
      have hVW : V ≠ W := by
        intro he
        obtain ⟨x,hx⟩ := hV.1
        exact Set.disjoint_left.mp hdis (hVA hx) (hWB (he ▸ hx))
      have hchoiceF : ∀ Q : {Q // Q ∈ F.erase U}, ∃ R : Set S,
          IsComplementComponent (G ∪ a.val.image) R ∧ R ⊆ Q.val := by
        intro Q
        exact hchoice Q.val (hF Q.val (Finset.mem_erase.mp Q.property).2)
      choose R hR hsub using hchoiceF
      have hRinj : Function.Injective R := by
        intro Q L he
        apply Subtype.ext
        by_contra hn
        obtain ⟨x,hx⟩ := (hR Q).1
        exact Set.disjoint_left.mp (complementComponents_disjoint
          (hF Q.val (Finset.mem_erase.mp Q.property).2)
          (hF L.val (Finset.mem_erase.mp L.property).2) hn)
          (hsub Q hx) (hsub L (he ▸ hx))
      let D := Finset.univ.image R
      have hDcard : D.card = (F.erase U).card := by rw [Finset.card_image_of_injective _ hRinj]; simp
      have hDdis : Disjoint D ({V,W} : Finset (Set S)) := by
        apply Finset.disjoint_left.mpr
        intro Z hZD hZH
        obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hZD
        have hQne : Q.val ≠ U := (Finset.mem_erase.mp Q.property).1
        have hRU : R Q ⊆ U := by
          rcases Finset.mem_insert.mp hZH with he|he
          · exact he.symm ▸ hVU
          · exact (Finset.mem_singleton.mp he).symm ▸ hWU
        obtain ⟨x,hx⟩ := (hR Q).1
        exact Set.disjoint_left.mp (complementComponents_disjoint
          (hF Q.val (Finset.mem_erase.mp Q.property).2) hU hQne)
          (hsub Q hx) (hRU hx)
      refine ⟨D ∪ {V,W},?_,?_⟩
      · rw [Finset.card_union_of_disjoint hDdis,hDcard,Finset.card_pair hVW]
        by_cases hUF : U ∈ F
        · have he := Finset.card_erase_add_one hUF; omega
        · rw [Finset.erase_eq_of_notMem hUF]; omega
      · intro Z hZ
        rcases Finset.mem_union.mp hZ with hZD|hZH
        · obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hZD
          exact hR Q
        · rcases Finset.mem_insert.mp hZH with he|he
          · exact he ▸ hV
          · exact (Finset.mem_singleton.mp he) ▸ hW
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let G : Finset ι → Set S := fun J => ⋃ v : {v // v ∈ J}, (r v).val.image
    have hmono {J K : Finset ι} (hJK : J ⊆ K) : G J ⊆ G K := by
      intro z hz
      obtain ⟨⟨v,hv⟩,hz⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨⟨v,hJK hv⟩,hz⟩
    have hgraph_insert (J : Finset ι) (i : ι) : G (insert i J) = G J ∪ (r i).val.image := by
      ext z
      constructor
      · intro hz
        obtain ⟨⟨j,hj⟩,hz⟩ := mem_iUnion.mp hz
        rcases Finset.mem_insert.mp hj with hj|hj
        · exact Or.inr (hj ▸ hz)
        · exact Or.inl (mem_iUnion.mpr ⟨⟨j,hj⟩,hz⟩)
      · rintro (hz|hz)
        · obtain ⟨⟨j,hj⟩,hz⟩ := mem_iUnion.mp hz
          exact mem_iUnion.mpr ⟨⟨j,Finset.mem_insert_of_mem hj⟩,hz⟩
        · exact mem_iUnion.mpr ⟨⟨i,Finset.mem_insert_self _ _⟩,hz⟩
    have hseedND : IsNowhereDense (G P) := by
      apply IsNowhereDense.iUnion
      intro i
      by_cases hl : (r i).val.map 0 = (r i).val.map 1
      · exact actual_loop_nowhereDense M (r i).val hl
      · exact hnonloop M ⟨(r i).val,hl⟩
    have hseedclosed : IsClosed (G P) := isClosed_iUnion_of_finite (fun i => (markedArc_image_compact (r i).val).isClosed)
    have hseedpoint : ∃ x, x ∉ G P := by
      by_contra hn
      have heq : G P = Set.univ := Set.eq_univ_iff_forall.mpr (fun x => by by_contra hx; exact hn ⟨x,hx⟩)
      change interior (closure (G P)) = ∅ at hseedND
      rw [heq,closure_univ,interior_univ] at hseedND
      obtain ⟨i⟩ := ‹Nonempty ι›
      exact Set.notMem_empty ((r i).val.map 0) (hseedND ▸ Set.mem_univ _)
    have hmain : ∀ J : Finset ι, Disjoint P J →
        (∀ i ∈ J, (r i).val.map 0 ≠ (r i).val.map 1 →
          (r i).val.map 0 ∈ G P ∧ (r i).val.map 1 ∈ connectedComponentIn (G P) ((r i).val.map 0)) →
        ∃ F : Finset (Set S), J.card + 1 ≤ F.card ∧
          ∀ U ∈ F, IsComplementComponent (G (P ∪ J)) U := by
      intro J
      induction J using Finset.induction_on with
      | empty =>
        intro _ _
        obtain ⟨x,hx⟩ := hseedpoint
        let U := connectedComponentIn (G P)ᶜ x
        refine ⟨{U},by simp,?_⟩
        intro W hW
        have he : W = U := Finset.mem_singleton.mp hW
        subst W
        simp only [Finset.union_empty]
        exact complementComponent_iff_componentIn.mpr ⟨x,hx,rfl⟩
      | @insert i J hi ih =>
        intro hdis hcompat
        have hdisJ : Disjoint P J := hdis.mono_right (Finset.subset_insert _ _)
        have hiP : i ∉ P := by
          intro hip
          exact Finset.disjoint_left.mp hdis hip (Finset.mem_insert_self _ _)
        have hinot : i ∉ P ∪ J := by simp [hiP,hi]
        obtain ⟨F,hFcard,hF⟩ := ih hdisJ (fun j hj => hcompat j (Finset.mem_insert_of_mem hj))
        have hPG : G P ⊆ G (P ∪ J) := hmono Finset.subset_union_left
        have ha : ∀ v : {v // v ∈ P ∪ J}, Disjoint (arcInterior M (r i)) (arcInterior M (r v)) := by
          intro v
          exact hd i v.val (fun he => hinot (he ▸ v.property))
        have hins : ∃ F' : Finset (Set S), F.card + 1 ≤ F'.card ∧
            ∀ U ∈ F', IsComplementComponent (G (P ∪ J) ∪ (r i).val.image) U := by
          by_cases hl : (r i).val.map 0 = (r i).val.map 1
          · exact hloop M (fun v : {v // v ∈ P ∪ J} => r v) (r i) hl ha F hF
          · obtain ⟨h0P,hcP⟩ := hcompat i (Finset.mem_insert_self _ _) hl
            have h1P : (r i).val.map 1 ∈ G P := connectedComponentIn_subset _ _ hcP
            have hc : (r i).val.map 1 ∈ connectedComponentIn (G (P ∪ J)) ((r i).val.map 0) :=
              connectedComponentIn_mono _ hPG hcP
            exact hcycle M (fun v : {v // v ∈ P ∪ J} => r v)
              (fun v w hvw => hd v.val w.val (fun he => hvw (Subtype.ext he)))
              (r i) hl ha (hPG h0P) (hPG h1P) hc F hF
        obtain ⟨F',hF'card,hF'⟩ := hins
        refine ⟨F',?_,?_⟩
        · rw [Finset.card_insert_of_notMem hi]
          omega
        · have heq : P ∪ insert i J = insert i (P ∪ J) := by ext j; simp [or_left_comm,or_assoc]
          rw [heq,hgraph_insert]
          exact hF'
    exact hmain I hdis hcompat
  classical
  obtain ⟨P,hPc,hPfive,hPcompat⟩ := hseed M r hd
  let I : Finset ι := Finset.univ \ P
  have hdis : Disjoint P I := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiI
    exact (Finset.mem_sdiff.mp hiI).2 hiP
  obtain ⟨F,hFc,hF⟩ := hlower M r hd P I hdis (fun i _ => hPcompat i)
  have heq : P ∪ I = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ P)
  have hcard : I.card + P.card = Fintype.card ι := by
    dsimp [I]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P),Finset.card_univ]
    exact Nat.sub_add_cancel (Finset.card_le_univ P)
  have hgraph : (⋃ v : {v // v ∈ P ∪ I}, (r v).val.image) = ⋃ i, (r i).val.image := by
    ext z
    constructor
    · intro hz
      obtain ⟨v,hv⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨v.val,hv⟩
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨⟨i,heq.symm ▸ Finset.mem_univ i⟩,hi⟩
  refine ⟨F,by omega,?_⟩
  rw [← hgraph]
  exact hF
end CurveComplex.HyperellipticModel
