import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Filtration.Geometry.ActualJordanRegionsHeader
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import Schoenflies.Concatenate
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualObjectFaceCountNamedHeader_1 : DecidableEq S := Classical.decEq _
set_option maxHeartbeats 2800000
theorem actual_object_face_count (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M σ) :
    ∃ F : Finset (Set S), F.card = (if O.card = 1 then 2 else O.card) ∧
      ∀ U : Set S, IsComplementComponent (actualObjectTrace M r O) U ↔ U ∈ F := by
  have hendpoint (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
      (r : {v // v ∈ σ} → EssentialMarkedArc M)
      (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
      (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
      (v : EssentialArcClass M) (hc : 2 ≤ (actualEndpointFibre M σ v).card) :
      ∃ F : Finset (Set S), F.card = (actualEndpointFibre M σ v).card ∧
        ∀ U : Set S, IsComplementComponent (actualObjectTrace M r (actualEndpointFibre M σ v)) U ↔ U ∈ F := by
    have hparallel (M : HyperellipticModel E S) {ι : Type} [DecidableEq ι]
        (r : ι → EssentialMarkedArc M) (p q : S) (hpq : p ≠ q)
        (hends : ∀ i, markedArcEndset (r i).val = {p,q})
        (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
        (I : Finset ι) (hI : I.Nonempty) :
        ∃ F : Finset (Set S), F.card = I.card ∧
          ∀ U : Set S, IsComplementComponent (⋃ v : {i // i ∈ I}, (r v).val.image) U ↔ U ∈ F := by
      have hinc (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
          (r : ι → EssentialMarkedArc M)
          (hd : ∀ v w, v ≠ w → Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
          (a : EssentialMarkedArc M) (haNL : a.val.map 0 ≠ a.val.map 1)
          (ha : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v)))
          (h0 : a.val.map 0 ∈ ⋃ v, (r v).val.image)
          (h1 : a.val.map 1 ∈ ⋃ v, (r v).val.image)
          (hc : a.val.map 1 ∈ connectedComponentIn (⋃ v, (r v).val.image) (a.val.map 0))
          (F : Finset (Set S))
          (hF : ∀ V : Set S, IsComplementComponent (⋃ v, (r v).val.image) V ↔ V ∈ F) :
          ∃ F' : Finset (Set S), F'.card = F.card + 1 ∧
            ∀ V : Set S, IsComplementComponent ((⋃ v, (r v).val.image) ∪ a.val.image) V ↔ V ∈ F' := by
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
        have hUF : U ∈ F := (hF U).mp hU
        have hdis : Disjoint (F.erase U) H := by
          apply Finset.disjoint_left.mpr
          intro V hVF hVH
          obtain ⟨hVU,hVF⟩ := Finset.mem_erase.mp hVF
          have hV := (hF V).mpr hVF
          have hHV := (hH V).mpr hVH
          obtain ⟨x,hx⟩ := hHV.1
          have hxU : x ∈ U := by
            by_contra hn
            exact hHV.2.2.1 hx (Or.inl hn)
          exact disjoint_left.mp (complementComponents_disjoint hV hU hVU) hx hxU
        let F' := F.erase U ∪ H
        have hcard : F'.card = F.card + 1 := by
          rw [Finset.card_union_of_disjoint hdis,hHcard]
          have hc := Finset.card_erase_add_one hUF
          omega
        refine ⟨F',hcard,?_⟩
        intro V
        rw [hinsert M (fun v => (r v).val) a.val U hU hplace]
        simp only [F',Finset.mem_union,Finset.mem_erase]
        rw [hF V,hH V]
        exact or_congr (and_comm) Iff.rfl
      have hbase (M : HyperellipticModel E S) (a : NonLoopArc M) :
          ∃ F : Finset (Set S), F.card = 1 ∧
            ∀ U : Set S, IsComplementComponent a.val.image U ↔ U ∈ F := by
        have hc : IsConnected a.val.imageᶜ := by  
          classical
          letI : T2Space S := M.sphere.symm.t2Space
          letI : CompactSpace S := M.sphere.symm.compactSpace
          obtain ⟨p,_,hp⟩ := a.exists_marked_puncture
          let e := M.puncturedPlane p
          let g : Interval → Schoenflies.Plane := fun t => e ⟨a.val.map t, by
            intro he; exact hp (he ▸ Set.mem_range_self t)⟩
          have hArc : Schoenflies.IsArc (Set.range g) := (a.plane_isArcBetween p hp).isArc
          let D : Set S := (fun z : Schoenflies.Plane => (e.symm z).val) '' (Set.range g)ᶜ
          have hD : IsConnected D := (Schoenflies.arc_complement hArc).image _
            (continuous_subtype_val.comp e.symm.continuous).continuousOn
          have hDeq : D = a.val.imageᶜ \ {p} := by
            ext x
            constructor
            · rintro ⟨z,hz,rfl⟩
              refine ⟨?_, by simpa using (e.symm z).property⟩
              rintro ⟨t,ht⟩
              apply hz
              refine ⟨t, ?_⟩
              apply e.symm.injective
              apply Subtype.ext
              simpa [g] using ht
            · rintro ⟨hx,hxp⟩
              have hxp' : x ≠ p := by simpa using hxp
              refine ⟨e ⟨x,hxp'⟩, ?_, by simp⟩
              rintro ⟨t,ht⟩
              have he : a.val.map t = x := congrArg Subtype.val (e.injective ht)
              exact hx ⟨t,he⟩
          have hclosed : IsClosed a.val.image := (markedArc_image_compact a.val).isClosed
          have hpcl : p ∈ closure D := by
            by_contra hn
            have hsingleton : IsOpen ({p} : Set S) := by
              have heq : a.val.imageᶜ ∩ (closure D)ᶜ = {p} := by
                ext x
                constructor
                · rintro ⟨hx,hxn⟩
                  by_contra hxp
                  apply hxn
                  apply subset_closure
                  rw [hDeq]
                  exact ⟨hx,hxp⟩
                · rintro rfl
                  exact ⟨hp,hn⟩
              rw [← heq]
              exact hclosed.isOpen_compl.inter isClosed_closure.isOpen_compl
            have hk : IsCompact ({x : S | x ≠ p}) := by
              have hset : {x : S | x ≠ p} = ({p} : Set S)ᶜ := by ext x; simp
              rw [hset]
              exact hsingleton.isClosed_compl.isCompact
            letI : CompactSpace {x : S // x ≠ p} := isCompact_iff_compactSpace.mp hk
            have hplane : IsCompact (Set.univ : Set Schoenflies.Plane) := by
              simpa using isCompact_univ.image e.continuous
            exact noncompact_univ Schoenflies.Plane hplane
          exact hD.subset_closure (by rw [hDeq]; exact sdiff_subset)
            (by intro x hx; by_cases hxp : x = p
                · exact hxp ▸ hpcl
                · apply subset_closure; rw [hDeq]; exact ⟨hx,by simpa using hxp⟩)
        classical
        refine ⟨{a.val.imageᶜ}, Finset.card_singleton _, ?_⟩
        intro U
        have hfull : IsComplementComponent a.val.image a.val.imageᶜ := by
          refine ⟨hc.nonempty,hc,Subset.rfl,?_⟩
          intro V hV hUV hVA
          exact Subset.antisymm hVA hUV
        constructor
        · intro hU
          have he : a.val.imageᶜ = U := hU.2.2.2 _ hc hU.2.2.1 Subset.rfl
          exact Finset.mem_singleton.mpr he.symm
        · intro hU
          exact (Finset.mem_singleton.mp hU) ▸ hfull
      
      classical
      have hNL : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1 := by
        intro i he
        have hc : (markedArcEndset (r i).val).card = 2 := by
          rw [hends i,Finset.card_pair hpq]
        simp [markedArcEndset,he] at hc
      have hpoint : ∀ i z, z ∈ ({p,q} : Finset S) → z ∈ (r i).val.image := by
        intro i z hz
        have hz' : z ∈ (markedArcEndset (r i).val : Set S) := by rw [hends i]; exact hz
        rw [← markedArc_image_inter_branch] at hz'
        exact hz'.1
      have hgraph_insert : ∀ (s : Finset ι) (i : ι),
          (⋃ v : {j // j ∈ insert i s}, (r v).val.image) =
            (⋃ v : {j // j ∈ s}, (r v).val.image) ∪ (r i).val.image := by
        intro s i
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
      suffices h : ∀ s : Finset ι, s.Nonempty → ∃ F : Finset (Set S), F.card = s.card ∧
          ∀ U : Set S, IsComplementComponent (⋃ v : {i // i ∈ s}, (r v).val.image) U ↔ U ∈ F by
        exact h I hI
      intro s
      induction s using Finset.induction_on with
      | empty => intro hs; exact False.elim (Finset.not_nonempty_empty hs)
      | @insert i s hi ih =>
        intro hne
        by_cases hs : s.Nonempty
        · obtain ⟨F,hFcard,hF⟩ := ih hs
          obtain ⟨j,hj⟩ := hs
          letI : Nonempty {j // j ∈ s} := ⟨⟨j,hj⟩⟩
          let rr : {j // j ∈ s} → EssentialMarkedArc M := fun j => r j
          let G := ⋃ v : {j // j ∈ s}, (r v).val.image
          have hconn : IsConnected G := markedFamily_graph_connected_of_common_endpoint
            (fun v : {j // j ∈ s} => (r v).val) p (fun v => by rw [hends]; simp)
          have he0 : (r i).val.map 0 ∈ ({p,q} : Finset S) := by
            rw [← hends i]; simp [markedArcEndset]
          have he1 : (r i).val.map 1 ∈ ({p,q} : Finset S) := by
            rw [← hends i]; simp [markedArcEndset]
          have h0 : (r i).val.map 0 ∈ G := mem_iUnion.mpr ⟨⟨j,hj⟩,hpoint j _ he0⟩
          have h1 : (r i).val.map 1 ∈ G := mem_iUnion.mpr ⟨⟨j,hj⟩,hpoint j _ he1⟩
          have hc : (r i).val.map 1 ∈ connectedComponentIn G ((r i).val.map 0) := by
            rw [hconn.isPreconnected.connectedComponentIn h0]; exact h1
          have hdi : ∀ v : {j // j ∈ s}, Disjoint (arcInterior M (r i)) (arcInterior M (rr v)) := by
            intro v; apply hd
            intro he; exact hi (he.symm ▸ v.property)
          have hdr : ∀ v w : {j // j ∈ s}, v ≠ w → Disjoint (arcInterior M (rr v)) (arcInterior M (rr w)) := by
            intro v w hn; exact hd _ _ (fun he => hn (Subtype.ext he))
          obtain ⟨F',hcard,hfaces⟩ := hinc M rr hdr (r i) (hNL i) hdi h0 h1 hc F hF
          refine ⟨F',?_,?_⟩
          · rw [hcard,hFcard,Finset.card_insert_of_notMem hi]
          · intro U
            rw [hgraph_insert]
            exact hfaces U
        · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
          subst s
          let n : NonLoopArc M := ⟨(r i).val,hNL i⟩
          obtain ⟨F,hcard,hfaces⟩ := hbase M n
          refine ⟨F,by simpa using hcard,?_⟩
          intro U
          rw [hgraph_insert]
          have hempty : (⋃ v : {j // j ∈ (∅ : Finset ι)}, (r v).val.image) = ∅ := by simp
          rw [hempty,empty_union]
          exact hfaces U
    classical
    let O := actualEndpointFibre M σ v
    have hO : O.Nonempty := Finset.card_pos.mp (by change 0 < (actualEndpointFibre M σ v).card; omega)
    obtain ⟨u,hu⟩ := hO
    let lift : {w // w ∈ O} → {w // w ∈ σ} := fun w => ⟨w.val,actualEndpointFibre_subset M σ v w.property⟩
    let rr : {w // w ∈ O} → EssentialMarkedArc M := fun w => r (lift w)
    let uO : {w // w ∈ O} := ⟨u,hu⟩
    have hn : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (rr uO)) := by
      rw [hr]; exact (Finset.mem_filter.mp hu).2.1
    let p := (rr uO).val.map 0
    let q := (rr uO).val.map 1
    have hpq : p ≠ q := actualRepresentative_nonloop M (rr uO) hn
    have hends : ∀ w : {w // w ∈ O}, markedArcEndset (rr w).val = {p,q} := by
      intro w
      have he : markedArcEndset (rr w).val = markedArcEndset (rr uO).val := by
        rw [markedArcEndset_eq_classEndpoints,markedArcEndset_eq_classEndpoints,hr,hr]
        exact (Finset.mem_filter.mp w.property).2.2.trans (Finset.mem_filter.mp hu).2.2.symm
      rw [he]
      rfl
    have hdr : ∀ w z : {w // w ∈ O}, w ≠ z → Disjoint (arcInterior M (rr w)) (arcInterior M (rr z)) := by
      intro w z hwz
      apply hd
      intro he
      exact hwz (Subtype.ext (congrArg (fun t : {v // v ∈ σ} => t.val) he))
    have hI : (Finset.univ : Finset {w // w ∈ O}).Nonempty := ⟨uO,Finset.mem_univ _⟩
    obtain ⟨F,hcard,hfaces⟩ := hparallel M rr p q hpq hends hdr Finset.univ hI
    have htrace : actualObjectTrace M r O =
        ⋃ w : {w : {w // w ∈ O} // w ∈ (Finset.univ : Finset {w // w ∈ O})}, (rr w.val).val.image := by
      ext x
      constructor
      · intro hx
        obtain ⟨w,hw⟩ := mem_iUnion.mp hx
        obtain ⟨hwO,hwx⟩ := mem_iUnion.mp hw
        let wo : {w // w ∈ O} := ⟨w.val,hwO⟩
        refine mem_iUnion.mpr ⟨⟨wo,Finset.mem_univ _⟩,?_⟩
        have he : lift wo = w := Subtype.ext rfl
        change x ∈ (r (lift wo)).val.image
        rw [he]; exact hwx
      · intro hx
        obtain ⟨w,hwx⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨lift w.val,mem_iUnion.mpr ⟨w.val.property,hwx⟩⟩
    refine ⟨F,?_,?_⟩
    · simpa using hcard
    · intro U
      rw [htrace]
      exact hfaces U
  have hloop (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
      (hloop : a.val.map 0 = a.val.map 1) :
      ∃ F : Finset (Set S), F.card = 2 ∧
        ∀ U : Set S, IsComplementComponent a.val.image U ↔ U ∈ F := by
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
    obtain ⟨U,V,hU,hV,_,_,hdisj,hne,hcover,_⟩ := sphereJordan_two_regions J P
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
    refine ⟨{A,B}, Finset.card_pair hneAB, ?_⟩
    intro W
    constructor
    · intro hW
      obtain ⟨x,hx⟩ := hW.1
      have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hW.2.2.1 hx
      rcases hxAB with hxA | hxB
      · have he : W = A := by
          by_contra hn
          exact Set.disjoint_left.mp (complementComponents_disjoint hW hcU hn) hx hxA
        simp [he]
      · have he : W = B := by
          by_contra hn
          exact Set.disjoint_left.mp (complementComponents_disjoint hW hcV hn) hx hxB
        simp [he]
    · intro hW
      rcases Finset.mem_insert.mp hW with hW | hW
      · exact hW ▸ hcU
      · exact (Finset.mem_singleton.mp hW) ▸ hcV
  classical
  simp only [actualObjectFamily,Finset.mem_union,Finset.mem_image,Finset.mem_filter] at hO
  rcases hO with ⟨v,⟨hv,hvl⟩,rfl⟩ | ⟨v,⟨hv,hvn,hvc⟩,rfl⟩
  · let V : {v // v ∈ σ} := ⟨v,hv⟩
    have hclass : (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (r V)) := by
      rw [hr]; exact hvl
    have hcard : (markedArcEndset (r V).val).card = 1 := by
      change (classEndpoints M (Quotient.mk (essentialArcSetoid M) (r V))).card = 1 at hclass
      rw [markedArcEndset_eq_classEndpoints]; exact hclass
    have hends : (r V).val.map 0 = (r V).val.map 1 := by
      by_contra hn
      change ({(r V).val.map 0,(r V).val.map 1} : Finset S).card = 1 at hcard
      rw [Finset.card_pair hn] at hcard
      omega
    obtain ⟨F,hcard,hfaces⟩ := hloop M (r V) hends
    refine ⟨F,by simpa using hcard,?_⟩
    intro U
    rw [actualObjectTrace_loop M r hv]
    exact hfaces U
  · obtain ⟨F,hcard,hfaces⟩ := hendpoint M r hr hd v hvc
    refine ⟨F,?_,hfaces⟩
    have hn : (actualEndpointFibre M σ v).card ≠ 1 := by omega
    simpa [hn] using hcard
end CurveComplex.HyperellipticModel
