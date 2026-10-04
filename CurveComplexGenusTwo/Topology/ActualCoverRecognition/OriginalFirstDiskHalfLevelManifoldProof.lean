import ClassificationOfSurfaces.Moise.IntrinsicComplex
import ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import ClassificationOfSurfaces.Moise.EmbeddedComplexValence
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import Mathlib
open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces.Moise
namespace CurveComplex.LocalSurgery
open Real Set Metric Topology LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
theorem actual_half_level_neighborhood_is_surface_with_boundary
    {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (P : IntrinsicTwoComplex) (selected : Finset P.Vertex)
    (ι : P.realization → U) (hι : Topology.IsEmbedding ι)
    (hInterior : ∀ x : P.realization,
      (1 : ℝ) / 2 ≤ ∑ v ∈ selected,x.val v → ι x ∈ interior (Set.range ι)) :
    let N := {x : P.realization | (1 : ℝ) / 2 ≤ ∑ v ∈ selected,x.val v}
    ∃ charts : ChartedSpace (EuclideanHalfSpace 2) N,
      letI := charts
      IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 N := by
  classical
  have interiorLocalChart {X U : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace U]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
      (ι : X → U) (hι : Topology.IsEmbedding ι) (F : X → ℝ) (hF : Continuous F)
      (hInterior : ∀ x, (1 : ℝ)/2 ≤ F x → ι x ∈ interior (Set.range ι)) :
      let N := {x : X | (1 : ℝ)/2 ≤ F x}
      ∀ x : N, (1 : ℝ)/2 < F x.val →
        ∃ e : OpenPartialHomeomorph N (EuclideanHalfSpace 2), x ∈ e.source := by
    classical
    let N : Set X := {x | (1 : ℝ)/2 ≤ F x}
    change ∀ x : N, (1 : ℝ)/2 < F x.val →
      ∃ e : OpenPartialHomeomorph N (EuclideanHalfSpace 2), x ∈ e.source
    intro x hx
    have adapter : Nonempty (ChartedSpace (EuclideanHalfSpace 2) U) := by
          let P := EuclideanSpace ℝ (Fin 2)
          let h : P ≃ₜ ℝ × ℝ :=
            (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
          let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
            ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
              h.symm.toOpenPartialHomeomorph)
          have es : e.source = univ := by simp [e]
          have et : e.target = {x : P | 0 < x 0} := by
            ext x
            simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
            rfl
          have ep (x : P) : 0 < e x 0 := by
            have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
            rwa [et] at hh
          let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
            toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
            invFun := fun y => e.symm y.val
            source := univ
            target := {y | 0 < y.val 0}
            map_source' := fun x _ => ep x
            map_target' := fun _ _ => mem_univ _
            left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
            right_inv' := by
              intro y hy
              apply Subtype.ext
              exact e.right_inv (by rwa [et])
            open_source := isOpen_univ
            open_target := isOpen_lt continuous_const
              (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
            continuousOn_toFun := by
              apply Continuous.continuousOn
              exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
            continuousOn_invFun := by
              apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
              intro y hy
              rwa [e.symm_source, et]
          }
          letI : ChartedSpace (EuclideanHalfSpace 2) P := {
            atlas := {a}
            chartAt := fun _ => a
            mem_chart_source := fun _ => mem_univ _
            chart_mem_atlas := fun _ => mem_singleton _
          }
          exact ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P U⟩
      
    letI : ChartedSpace (EuclideanHalfSpace 2) U := adapter.some
    let G : Set X := {x | (1 : ℝ)/2 < F x}
    have hGOpen : IsOpen G := isOpen_lt continuous_const hF
    obtain ⟨V,hV,hImage⟩ := hι.isInducing.image_eq_isOpen_inter_range hGOpen
    have hImageInterior : ι '' G ⊆ interior (Set.range ι) := by
      rintro z ⟨y,hy,rfl⟩
      exact hInterior y (le_of_lt hy)
    have hImageEq : ι '' G = V ∩ interior (Set.range ι) := by
      apply Set.Subset.antisymm
      · intro y hy
        exact ⟨(hImage ▸ hy).1,hImageInterior hy⟩
      · intro y hy
        rw [hImage]
        exact ⟨hy.1,interior_subset hy.2⟩
    have hImageOpen : IsOpen (ι '' G) := by rw [hImageEq]; exact hV.inter isOpen_interior
    let mapG : G → U := fun y => ι y.val
    have hRangeG : Set.range mapG = ι '' G := by
      ext y
      constructor
      · rintro ⟨q,rfl⟩; exact ⟨q.val,q.property,rfl⟩
      · rintro ⟨q,hq,rfl⟩; exact ⟨⟨q,hq⟩,rfl⟩
    have hMapGEmbedding : Topology.IsEmbedding mapG := hι.comp Topology.IsEmbedding.subtypeVal
    have hMapGOpen : Topology.IsOpenEmbedding mapG := ⟨hMapGEmbedding,by rw [hRangeG]; exact hImageOpen⟩
    let mapGN : G → N := fun y => ⟨y.val,by change (1 : ℝ)/2 ≤ F y.val; exact le_of_lt y.property⟩
    have hMapGNContinuous : Continuous mapGN := continuous_subtype_val.subtype_mk _
    have hMapGNEmbedding : Topology.IsEmbedding mapGN :=
      Topology.IsEmbedding.of_comp hMapGNContinuous continuous_subtype_val Topology.IsEmbedding.subtypeVal
    have hRangeGN : Set.range mapGN = {y : N | (1 : ℝ)/2 < F y.val} := by
      ext y
      constructor
      · rintro ⟨q,rfl⟩; exact q.property
      · intro hy; exact ⟨⟨y.val,hy⟩,Subtype.ext rfl⟩
    have hMapGNOpen : Topology.IsOpenEmbedding mapGN := ⟨hMapGNEmbedding,by
      rw [hRangeGN]
      exact isOpen_lt continuous_const (hF.comp continuous_subtype_val)⟩
    letI : Nonempty G := ⟨⟨x.val,hx⟩⟩
    let actualG := hMapGOpen.toOpenPartialHomeomorph mapG
    let actualChart := actualG.trans (chartAt (EuclideanHalfSpace 2) (ι x.val))
    have hxG : (⟨x.val,hx⟩ : G) ∈ actualChart.source := by
      change (⟨x.val,hx⟩ : G) ∈ actualG.source ∧ actualG ⟨x.val,hx⟩ ∈
        (chartAt (EuclideanHalfSpace 2) (ι x.val)).source
      refine ⟨Set.mem_univ _,?_⟩
      exact ChartedSpace.mem_chart_source (ι x.val)
    refine ⟨actualChart.lift_openEmbedding hMapGNOpen,?_⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    exact ⟨⟨x.val,hx⟩,hxG,Subtype.ext rfl⟩
  have actualMixedValence {U : Type} [TopologicalSpace U] [T2Space U]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
      (P : IntrinsicTwoComplex) (selected : Finset P.Vertex)
      (ι : P.realization → U) (hι : Topology.IsEmbedding ι)
      (hInterior : ∀ x : P.realization, (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v → ι x ∈ interior (Set.range ι)) :
      ∀ e : P.Edge, (e.val ∩ selected).Nonempty → ¬ e.val ⊆ selected →
        (P.faces.filter fun t => e.val ⊆ t).card = 2 := by
    classical
    have adapter : Nonempty (ChartedSpace (EuclideanHalfSpace 2) U) := by
          let P := EuclideanSpace ℝ (Fin 2)
          let h : P ≃ₜ ℝ × ℝ :=
            (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
          let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
            ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
              h.symm.toOpenPartialHomeomorph)
          have es : e.source = univ := by simp [e]
          have et : e.target = {x : P | 0 < x 0} := by
            ext x
            simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
            rfl
          have ep (x : P) : 0 < e x 0 := by
            have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
            rwa [et] at hh
          let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
            toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
            invFun := fun y => e.symm y.val
            source := univ
            target := {y | 0 < y.val 0}
            map_source' := fun x _ => ep x
            map_target' := fun _ _ => mem_univ _
            left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
            right_inv' := by
              intro y hy
              apply Subtype.ext
              exact e.right_inv (by rwa [et])
            open_source := isOpen_univ
            open_target := isOpen_lt continuous_const
              (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
            continuousOn_toFun := by
              apply Continuous.continuousOn
              exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
            continuousOn_invFun := by
              apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
              intro y hy
              rwa [e.symm_source, et]
          }
          letI : ChartedSpace (EuclideanHalfSpace 2) P := {
            atlas := {a}
            chartAt := fun _ => a
            mem_chart_source := fun _ => mem_univ _
            chart_mem_atlas := fun _ => mem_singleton _
          }
          exact ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P U⟩
      
    letI : ChartedSpace (EuclideanHalfSpace 2) U := adapter.some
    have htwoFaces (P : IntrinsicTwoComplex) (ι : P.realization → U)
      (hι : _root_.Topology.IsEmbedding ι)
      (e : Finset P.Vertex) (he : e.card = 2) (x : P.realization)
      (hxpos : ∀ v ∈ e, 0 < x.val v) (hxzero : ∀ v ∉ e, x.val v = 0)
      (hxint : ι x ∈ interior (range ι)) :
      2 ≤ (P.faces.filter fun t => e ⊆ t).card := by
        classical
        have hreflect  {X : Type} [TopologicalSpace X]
          {f : X → U} {g : X → EuclideanSpace ℝ (Fin 2)}
          (hf : _root_.Topology.IsEmbedding f) (hg : _root_.Topology.IsEmbedding g)
          {x : X} (hx : f x ∈ interior (range f)) :
          g x ∈ interior (range g) := by
            let P := EuclideanSpace ℝ (Fin 2)
            let z : U := f x
            let c : OpenPartialHomeomorph U P := chartAt P z
            let W : Set P :=
              c.target ∩ c.symm ⁻¹' interior (Set.range f)
            have hWopen : IsOpen W := by
              exact c.continuousOn_symm.isOpen_inter_preimage c.open_target isOpen_interior
            have hzTarget : c z ∈ c.target := c.map_source (ChartedSpace.mem_chart_source z)
            have hcz : c.symm (c z) = z :=
              c.left_inv (ChartedSpace.mem_chart_source z)
            have hczW : c z ∈ W := by
              refine ⟨hzTarget, ?_⟩
              change c.symm (c z) ∈ interior (Set.range f)
              rw [hcz]
              exact hx
            have hcSymm : Continuous (fun w : W ↦ c.symm w.1) := by
              apply ContinuousOn.restrict
              exact c.continuousOn_symm.mono fun w hw ↦ hw.1
            let toOldRange : W → Set.range f :=
              fun w ↦ ⟨c.symm w.1, interior_subset w.2.2⟩
            have htoOldRange : Continuous toOldRange :=
              Continuous.subtype_mk hcSymm _
            let source : W → X :=
              fun w ↦ hf.toHomeomorph.symm (toOldRange w)
            have hsourceCont : Continuous source :=
              hf.toHomeomorph.symm.continuous.comp htoOldRange
            have hsourceInj : Function.Injective source := by
              intro u v huv
              have huvRange : toOldRange u = toOldRange v :=
                hf.toHomeomorph.symm.injective huv
              have huvSurface : c.symm u.1 = c.symm v.1 :=
                congrArg Subtype.val huvRange
              apply Subtype.ext
              exact c.symm.injOn u.2.1 v.2.1
                huvSurface
            let localMap : W → P := fun w ↦ g (source w)
            have hlocalCont : Continuous localMap :=
              hg.continuous.comp hsourceCont
            have hlocalInj : Function.Injective localMap :=
              hg.injective.comp hsourceInj
            have hlocalOpen : IsOpen (Set.range localMap) :=
              isOpen_range_of_isOpen_of_continuous_injective
                (modelWithCornersSelf ℝ P) hWopen localMap
                hlocalCont hlocalInj
            let w₀ : W := ⟨c z, hczW⟩
            have hsourceW₀ : source w₀ = x := by
              apply hf.injective
              change (hf.toHomeomorph (source w₀)).1 = f x
              rw [hf.toHomeomorph.apply_symm_apply]
              change c.symm (c z) = f x
              exact hcz
            have hlocalAt : localMap w₀ = g x := by
              rw [show localMap w₀ = g (source w₀) by rfl, hsourceW₀]
            apply mem_interior_iff_mem_nhds.mpr
            apply Filter.mem_of_superset
              (hlocalOpen.mem_nhds ⟨w₀, hlocalAt⟩)
            rintro y ⟨w, rfl⟩
            exact Set.mem_range_self (source w)
      
        by_contra hn
        have hcount : (P.faces.filter fun t => e ⊆ t).card ≤ 1 := by omega
        obtain ⟨t, ht, hxt⟩ := x.property.2
        have het : e ⊆ t := by
          intro v hv
          by_contra hvt
          have hz := hxt v hvt
          have hp := hxpos v hv
          linarith
        have hsole : ∀ u ∈ P.faces, e ⊆ u → u = t := by
          intro u hu heu
          exact (Finset.card_le_one.mp hcount) u (Finset.mem_filter.mpr ⟨hu,heu⟩)
            t (Finset.mem_filter.mpr ⟨ht,het⟩)
        let T : P.Face := ⟨t,ht⟩
        let other : Set U := ⋃ u : P.Face,
          if u.val = t then ∅ else ι '' P.faceCarrier u.val
        have ho : IsClosed other := by
          apply isClosed_iUnion_of_finite
          intro u
          split_ifs
          · exact isClosed_empty
          · exact ((P.faceCarrier_closed u.val).isCompact.image hι.continuous).isClosed
        have hxo : ι x ∉ other := by
          intro hx
          obtain ⟨u,hu⟩ := mem_iUnion.mp hx
          by_cases hut : u.val = t
          · simpa [hut] using hu
          · simp only [if_neg hut] at hu
            obtain ⟨y,hy,heq⟩ := hu
            have hyx : y = x := hι.injective heq
            subst y
            have heu : e ⊆ u.val := by
              intro v hv
              by_contra hvu
              have hz := hy v hvu
              have hp := hxpos v hv
              linarith
            exact hut (hsole u.val u.property heu)
        let W := interior (range ι) ∩ otherᶜ
        have hW : IsOpen W := isOpen_interior.inter ho.isOpen_compl
        let f : P.ClosedFace T → U := fun y => ι y.val
        have hf : _root_.Topology.IsEmbedding f := hι.comp _root_.Topology.IsEmbedding.subtypeVal
        have hWF : W ⊆ range f := by
          intro z hz
          obtain ⟨y,hy⟩ := interior_subset hz.1
          obtain ⟨u,hu,hyu⟩ := y.property.2
          have hut : u = t := by
            by_contra hut
            apply hz.2
            apply mem_iUnion.mpr
            refine ⟨⟨u,hu⟩, ?_⟩
            simp only [if_neg hut]
            exact ⟨y,hyu,hy⟩
          subst u
          exact ⟨⟨y,hyu⟩,hy⟩
        have hxf : f ⟨x,hxt⟩ ∈ interior (range f) :=
          (hW.subset_interior_iff.mpr hWF) ⟨hxint,hxo⟩
        let g : P.ClosedFace T → Plane := fun y => (P.facePlaneHomeomorph T y).val
        have hg : _root_.Topology.IsEmbedding g :=
          _root_.Topology.IsEmbedding.subtypeVal.comp (P.facePlaneHomeomorph T).isEmbedding
        have hgRange : range g = standardTrianglePlaneComplex.support := by
          ext z
          constructor
          · rintro ⟨y,rfl⟩
            exact (P.facePlaneHomeomorph T y).property
          · intro hz
            refine ⟨(P.facePlaneHomeomorph T).symm ⟨z,hz⟩, ?_⟩
            exact congrArg Subtype.val ((P.facePlaneHomeomorph T).apply_symm_apply ⟨z,hz⟩)
        have hpint := hreflect hf hg hxf
        rw [hgRange] at hpint
        have hnot : ¬ t ⊆ e := by
          intro hte
          have hle := Finset.card_le_card hte
          rw [P.faces_card t ht, he] at hle
          omega
        obtain ⟨v,hvt,hve⟩ := Finset.not_subset.mp hnot
        let p : standardTrianglePlaneComplex.support := P.facePlaneHomeomorph T ⟨x,hxt⟩
        let i : Fin 3 := (P.faceVertexEquiv T).symm ⟨v,hvt⟩
        have hpi : p.val ∈ interior
            (standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier standardTriangleMeshFace.val) := by
          rw [show standardTrianglePlaneComplex.toTriangleMesh.triangleCarrier
            standardTriangleMeshFace.val = standardTrianglePlaneComplex.support by
              exact standardTriangle_cellCarrier_univ]
          exact hpint
        have hcoord : 0 < standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace p.val i := by
          rw [standardTrianglePlaneComplex.faceCoords_apply_of_mem standardTriangleMeshFace (Finset.mem_univ i)]
          rw [standardTrianglePlaneComplex.toTriangleMesh.interior_triangleCarrier standardTriangleMeshFace] at hpi
          exact hpi (standardTrianglePlaneComplex.toTriangleMesh.triangleEquiv
            standardTriangleMeshFace ⟨i,Finset.mem_univ i⟩)
        have hcoordEq : x.val v = standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace p.val i := by
          calc
            x.val v = ((P.facePlaneHomeomorph T).symm p).val.val v := by
              have h := (P.facePlaneHomeomorph T).symm_apply_apply ⟨x,hxt⟩
              exact congrFun (congrArg (fun z => z.val.val) h.symm) v
            _ = P.facePlaneInverseAffine T p.val v :=
              congrFun (P.facePlaneHomeomorph_symm_val T p) v
            _ = _ := by
              simp only [IntrinsicTwoComplex.facePlaneInverseAffine, AffineMap.comp_apply,
                P.faceCoordExtensionAffine_apply_of_mem T
                  (standardTrianglePlaneComplex.faceCoords standardTriangleMeshFace p.val) hvt]
              rfl
        have hz := hxzero v hve
        linarith
  
    intro e hyes hno
    let r : Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
    let x : P.realization := P.edgePath e r
    have hxzero : ∀ v ∉ e.val, x.val v = 0 := by
      have hx : x ∈ P.faceCarrier e.val := by
        rw [← P.range_edgePath e]
        exact ⟨r,rfl⟩
      exact hx
    have hxf : x.val (P.edgeFirst e) = 1 / 2 := by
      change (P.edgePath e r).val (P.edgeFirst e) = 1 / 2
      rw [P.edgePath_apply_first]
      norm_num [r]
    have hxs : x.val (P.edgeSecond e) = 1 / 2 := by
      change (P.edgePath e r).val (P.edgeSecond e) = 1 / 2
      rw [P.edgePath_apply_second]
    have hxpos : ∀ v ∈ e.val, 0 < x.val v := by
      intro v hv
      rw [P.edge_eq_pair e] at hv
      rcases Finset.mem_insert.mp hv with hv | hv
      · subst v
        rw [hxf]
        norm_num
      · have hv' := Finset.mem_singleton.mp hv
        subst v
        rw [hxs]
        norm_num
    have habits : (P.edgeFirst e ∈ selected ∧ P.edgeSecond e ∉ selected) ∨
        (P.edgeSecond e ∈ selected ∧ P.edgeFirst e ∉ selected) := by
      rw [P.edge_eq_pair e] at hyes hno
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hno
      by_cases ha : P.edgeFirst e ∈ selected
      · exact Or.inl ⟨ha,fun hb => hno ⟨ha,hb⟩⟩
      · refine Or.inr ⟨?_,ha⟩
        obtain ⟨v,hv⟩ := hyes
        have hvpair := (Finset.mem_inter.mp hv).1
        have hvs := (Finset.mem_inter.mp hv).2
        simp only [Finset.mem_insert,Finset.mem_singleton] at hvpair
        rcases hvpair with rfl | rfl
        · exact False.elim (ha hvs)
        · exact hvs
    have hsum : (∑ v ∈ selected, x.val v) = 1 / 2 := by
      rcases habits with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · rw [Finset.sum_eq_single (P.edgeFirst e)]
        · exact hxf
        · intro v hv hne
          apply hxzero
          rw [P.edge_eq_pair e]
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
          exact ⟨hne,fun heq => hb (heq ▸ hv)⟩
        · exact fun hn => False.elim (hn ha)
      · rw [Finset.sum_eq_single (P.edgeSecond e)]
        · exact hxs
        · intro v hv hne
          apply hxzero
          rw [P.edge_eq_pair e]
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
          exact ⟨fun heq => ha (heq ▸ hv),hne⟩
        · exact fun hn => False.elim (hn hb)
    have hxint : ι x ∈ interior (Set.range ι) := hInterior x (by rw [hsum])
    have hlow := htwoFaces P ι hι e.val (P.card_of_mem_edges e.property) x hxpos hxzero hxint
    have hhigh := edge_valence_le_two_of_isEmbedding P.faces P.faces_card ι hι e.val
      (P.card_of_mem_edges e.property)
    exact Nat.le_antisymm hhigh hlow
  have twoFaceArrangement (P : IntrinsicTwoComplex) (a b : P.Vertex) (hab : a ≠ b)
      (hValence : (P.faces.filter fun face => ({a,b} : Finset P.Vertex) ⊆ face).card = 2) :
      ∃ c d : P.Vertex, a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d ∧
        ({a,b,c} : Finset P.Vertex) ∈ P.faces ∧ ({a,b,d} : Finset P.Vertex) ∈ P.faces ∧
        (∀ face ∈ P.faces, ({a,b} : Finset P.Vertex) ⊆ face →
          face = {a,b,c} ∨ face = {a,b,d}) := by
    classical
    let edge : Finset P.Vertex := {a,b}
    have hThird (face : Finset P.Vertex) (hFace : face ∈ P.faces) (hSub : edge ⊆ face) :
        ∃ c : P.Vertex, a ≠ c ∧ b ≠ c ∧ face = {a,b,c} := by
      have hDiff : (face \ edge).card = 1 := by
        rw [Finset.card_sdiff,Finset.inter_eq_left.mpr hSub,P.faces_card face hFace]
        simp [edge,hab]
      obtain ⟨c,hEq⟩ := Finset.card_eq_one.mp hDiff
      have hMem : c ∈ face \ edge := hEq ▸ Finset.mem_singleton_self c
      have hc := (Finset.mem_sdiff.mp hMem).2
      have hac : a ≠ c := by intro he; apply hc; simp [edge,← he]
      have hbc : b ≠ c := by intro he; apply hc; simp [edge,← he]
      refine ⟨c,hac,hbc,?_⟩
      have hu : edge ∪ (face \ edge) = face := Finset.union_sdiff_of_subset hSub
      rw [hEq] at hu
      rw [← hu]
      ext v
      simp only [edge,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      tauto
    obtain ⟨firstFace,secondFace,hNe,hEq⟩ := Finset.card_eq_two.mp hValence
    have hFirst : firstFace ∈ P.faces.filter fun face => edge ⊆ face := by
      rw [hEq]
      simp
    have hSecond : secondFace ∈ P.faces.filter fun face => edge ⊆ face := by
      rw [hEq]
      simp
    obtain ⟨c,hac,hbc,hFC⟩ := hThird firstFace (Finset.mem_filter.mp hFirst).1 (Finset.mem_filter.mp hFirst).2
    obtain ⟨d,had,hbd,hFD⟩ := hThird secondFace (Finset.mem_filter.mp hSecond).1 (Finset.mem_filter.mp hSecond).2
    have hcd : c ≠ d := by
      intro he
      exact hNe (hFC.trans (he ▸ hFD.symm))
    refine ⟨c,d,hac,hbc,had,hbd,hcd,hFC ▸ (Finset.mem_filter.mp hFirst).1,
      hFD ▸ (Finset.mem_filter.mp hSecond).1,?_⟩
    intro face hFace hSub
    have hm : face ∈ P.faces.filter fun face => edge ⊆ face := Finset.mem_filter.mpr ⟨hFace,hSub⟩
    rw [hEq] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact Or.inl (hm.trans hFC)
    · exact Or.inr ((Finset.mem_singleton.mp hm).trans hFD)
  have mixedEdgeLocalChart (P : IntrinsicTwoComplex) (selected : Finset P.Vertex)
      (a b c d : P.Vertex) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
      (hPlus : ({a,b,c} : Finset P.Vertex) ∈ P.faces)
      (hMinus : ({a,b,d} : Finset P.Vertex) ∈ P.faces)
      (haSelected : a ∈ selected) (hbSelected : b ∉ selected)
      (hFaceSet : ∀ face ∈ P.faces, ({a,b} : Finset P.Vertex) ⊆ face →
        face = {a,b,c} ∨ face = {a,b,d}) :
      let N := {x : P.realization | (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v}
      ∃ e : OpenPartialHomeomorph N (EuclideanHalfSpace 2),
        ∀ x : N, (0 < x.val.val a ∧ 0 < x.val.val b) → x ∈ e.source := by
    classical
    let plus (q : ℝ × ℝ) := max q.2 0
    let minus (q : ℝ × ℝ) := max (-q.2) 0
    let first (q : ℝ × ℝ) := (1 : ℝ)/2 + q.1 -
      (if c ∈ selected then plus q else 0) - (if d ∈ selected then minus q else 0)
    let second (q : ℝ × ℝ) := 1 - first q - plus q - minus q
    let W : Set (ℝ × ℝ) := {q | 0 < first q ∧ 0 < second q}
    let coordinates (q : ℝ × ℝ) : P.Vertex → ℝ :=
      Pi.single a (first q) + Pi.single b (second q) +
        Pi.single c (plus q) + Pi.single d (minus q)
    have hCoordA (q) : coordinates q a = first q := by simp [coordinates,hab,hac,had]
    have hCoordB (q) : coordinates q b = second q := by simp [coordinates,hab.symm,hbc,hbd]
    have hCoordC (q) : coordinates q c = plus q := by simp [coordinates,hac.symm,hbc.symm,hcd]
    have hCoordD (q) : coordinates q d = minus q := by simp [coordinates,had.symm,hbd.symm,hcd.symm]
    have hOther (q) (v) (ha : v ≠ a) (hb : v ≠ b) (hc : v ≠ c) (hd : v ≠ d) :
        coordinates q v = 0 := by simp [coordinates,ha,hb,hc,hd]
    have hSum (q) : ∑ v,coordinates q v = 1 := by
      simp only [coordinates,Pi.add_apply,Finset.sum_add_distrib]
      rw [Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single']
      simp only [Finset.mem_univ,if_true]
      dsimp [second]
      ring
    let inverse (q : W) : P.realization := ⟨coordinates q.val,⟨by
      intro v
      by_cases ha : v = a
      · subst v; rw [hCoordA]; exact q.property.1.le
      by_cases hb : v = b
      · subst v; rw [hCoordB]; exact q.property.2.le
      by_cases hc : v = c
      · subst v; rw [hCoordC]; exact le_max_right _ _
      by_cases hd : v = d
      · subst v; rw [hCoordD]; exact le_max_right _ _
      rw [hOther _ _ ha hb hc hd],hSum q.val⟩,by
      by_cases hv : 0 ≤ q.val.2
      · refine ⟨{a,b,c},hPlus,?_⟩
        intro v hv'
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv'
        by_cases hd : v = d
        · subst v; rw [hCoordD]; exact max_eq_right (neg_nonpos.mpr hv)
        · exact hOther _ _ hv'.1 hv'.2.1 hv'.2.2 hd
      · refine ⟨{a,b,d},hMinus,?_⟩
        intro v hv'
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv'
        by_cases hc : v = c
        · subst v; rw [hCoordC]; exact max_eq_right (le_of_not_ge hv)
        · exact hOther _ _ hv'.1 hv'.2.1 hc hv'.2.2⟩
    have hContinuous : Continuous inverse := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro v
      dsimp [inverse,coordinates,first,second,plus,minus]
      simp only [Pi.add_apply,Pi.single_apply]
      split_ifs <;> fun_prop
    have hSelectedInverse (q : W) : (∑ v ∈ selected,(inverse q).val v) = (1 : ℝ)/2 + q.val.1 := by
      change (∑ v ∈ selected,coordinates q.val v) = (1 : ℝ)/2 + q.val.1
      simp only [coordinates,Pi.add_apply,Finset.sum_add_distrib]
      rw [Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single']
      simp only [if_pos haSelected,if_neg hbSelected,add_zero]
      dsimp [first]
      split_ifs <;> ring
    have hSignedInverse (q : W) : (inverse q).val c - (inverse q).val d = q.val.2 := by
      change coordinates q.val c - coordinates q.val d = q.val.2
      rw [hCoordC,hCoordD]
      dsimp [plus,minus]
      by_cases hv : 0 ≤ q.val.2
      · rw [max_eq_left hv,max_eq_right (neg_nonpos.mpr hv)]
        ring
      · have hv' : q.val.2 ≤ 0 := le_of_not_ge hv
        rw [max_eq_right hv',max_eq_left (neg_nonneg.mpr hv')]
        ring
    let chart (x : P.realization) : ℝ × ℝ := ((∑ v ∈ selected,x.val v) - 1/2,x.val c-x.val d)
    let star : Set P.realization := {x | 0 < x.val a ∧ 0 < x.val b}
    have hStarFaces (x : star) : x.val ∈ P.faceCarrier {a,b,c} ∨ x.val ∈ P.faceCarrier {a,b,d} := by
      obtain ⟨face,hFace,hCarrier⟩ := x.val.property.2
      have haFace : a ∈ face := by
        by_contra hn
        have hZero := hCarrier a hn
        linarith only [hZero,x.property.1]
      have hbFace : b ∈ face := by
        by_contra hn
        have hZero := hCarrier b hn
        linarith only [hZero,x.property.2]
      have hSub : ({a,b} : Finset P.Vertex) ⊆ face := by
        simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
        exact ⟨haFace,hbFace⟩
      rcases hFaceSet face hFace hSub with he | he
      · exact Or.inl (he ▸ hCarrier)
      · exact Or.inr (he ▸ hCarrier)
    have hStarOutside (x : star) (v : P.Vertex) (hv : v ∉ ({a,b,c,d} : Finset P.Vertex)) : x.val.val v = 0 := by
      have hv' : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
        simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hv
      rcases hStarFaces x with h | h
      · exact h v (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨hv'.1,hv'.2.1,hv'.2.2.1⟩)
      · exact h v (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; exact ⟨hv'.1,hv'.2.1,hv'.2.2.2⟩)
    have hRepresentation (x : star) : x.val.val =
        Pi.single a (x.val.val a) + Pi.single b (x.val.val b) +
          Pi.single c (x.val.val c) + Pi.single d (x.val.val d) := by
      funext v
      by_cases ha : v = a
      · subst v; simp [hab,hac,had]
      by_cases hb : v = b
      · subst v; simp [hab.symm,hbc,hbd]
      by_cases hc : v = c
      · subst v; simp [hac.symm,hbc.symm,hcd]
      by_cases hd : v = d
      · subst v; simp [had.symm,hbd.symm,hcd.symm]
      rw [hStarOutside x v (by simp [ha,hb,hc,hd])]
      simp [ha,hb,hc,hd]
    have hStarMax (x : star) : plus (chart x.val) = x.val.val c ∧ minus (chart x.val) = x.val.val d := by
      dsimp [plus,minus,chart]
      rcases hStarFaces x with h | h
      · have hd0 : x.val.val d = 0 := h d (by simp [had.symm,hbd.symm,hcd.symm])
        rw [hd0,sub_zero]
        exact ⟨max_eq_left (x.val.property.1.1 c),max_eq_right (neg_nonpos.mpr (x.val.property.1.1 c))⟩
      · have hc0 : x.val.val c = 0 := h c (by simp [hac.symm,hbc.symm,hcd])
        rw [hc0,zero_sub,neg_neg]
        exact ⟨max_eq_right (neg_nonpos.mpr (x.val.property.1.1 d)),max_eq_left (x.val.property.1.1 d)⟩
    have hStarSum (x : star) : x.val.val a + x.val.val b + x.val.val c + x.val.val d = 1 := by
      have hs := x.val.property.1.2
      rw [hRepresentation x] at hs
      simp only [Pi.add_apply,Finset.sum_add_distrib] at hs
      rw [Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single'] at hs
      simpa using hs
    have hStarSelected (x : star) : (∑ v ∈ selected,x.val.val v) =
        x.val.val a + (if c ∈ selected then x.val.val c else 0) +
          (if d ∈ selected then x.val.val d else 0) := by
      conv_lhs => rw [hRepresentation x]
      simp only [Pi.add_apply,Finset.sum_add_distrib]
      rw [Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single',Finset.sum_pi_single']
      simp only [if_pos haSelected,if_neg hbSelected,add_zero]
    have hStarFirst (x : star) : first (chart x.val) = x.val.val a := by
      dsimp [first]
      change 1/2 + ((∑ v ∈ selected,x.val.val v)-1/2) -
        (if c ∈ selected then plus (chart x.val) else 0) -
        (if d ∈ selected then minus (chart x.val) else 0) = x.val.val a
      rw [hStarSelected x,(hStarMax x).1,(hStarMax x).2]
      ring
    have hStarSecond (x : star) : second (chart x.val) = x.val.val b := by
      dsimp [second]
      rw [hStarFirst x,(hStarMax x).1,(hStarMax x).2]
      linarith [hStarSum x]
    have hChartW (x : star) : chart x.val ∈ W := by
      change 0 < first (chart x.val) ∧ 0 < second (chart x.val)
      rw [hStarFirst x,hStarSecond x]
      exact x.property
    have hInverseChart (x : star) : inverse ⟨chart x.val,hChartW x⟩ = x.val := by
      apply Subtype.ext
      change coordinates (chart x.val) = x.val.val
      rw [hRepresentation x]
      dsimp [coordinates]
      rw [hStarFirst x,hStarSecond x,(hStarMax x).1,(hStarMax x).2]
    have hChartInverse (q : W) : chart (inverse q) = q.val := by
      apply Prod.ext
      · change (∑ v ∈ selected,(inverse q).val v)-1/2 = q.val.1
        rw [hSelectedInverse q]
        ring
      · exact hSignedInverse q
    have hInverseStar (q : W) : inverse q ∈ star := by
      change 0 < coordinates q.val a ∧ 0 < coordinates q.val b
      rw [hCoordA,hCoordB]
      exact q.property
    have hChartContinuous : Continuous chart := by
      have hs : Continuous (fun x : P.realization => ∑ v ∈ selected,x.val v) :=
        continuous_finset_sum selected (fun v _ => (continuous_apply v).comp continuous_subtype_val)
      exact (hs.sub continuous_const).prodMk
        (((continuous_apply c).comp continuous_subtype_val).sub
          ((continuous_apply d).comp continuous_subtype_val))
    let starHomeomorph : star ≃ₜ W := {
      toFun := fun x => ⟨chart x.val,hChartW x⟩
      invFun := fun q => ⟨inverse q,hInverseStar q⟩
      left_inv := fun x => Subtype.ext (hInverseChart x)
      right_inv := fun q => Subtype.ext (hChartInverse q)
      continuous_toFun := (hChartContinuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := hContinuous.subtype_mk _ }
    have hStarOpen : IsOpen star := by
      change IsOpen ({x : P.realization | 0 < x.val a} ∩ {x : P.realization | 0 < x.val b})
      exact (isOpen_lt continuous_const ((continuous_apply a).comp continuous_subtype_val)).inter
        (isOpen_lt continuous_const ((continuous_apply b).comp continuous_subtype_val))
    have hFirstContinuous : Continuous first := by
      dsimp [first,plus,minus]
      split_ifs <;> fun_prop
    have hSecondContinuous : Continuous second := by
      dsimp [second,plus,minus]
      fun_prop
    have hWOpen : IsOpen W := (isOpen_lt continuous_const hFirstContinuous).inter
      (isOpen_lt continuous_const hSecondContinuous)
    let N : Set P.realization := {x | (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v}
    let halfPair := {q : ℝ × ℝ | 0 ≤ q.1}
    let localDomain : Set N := {x | x.val ∈ star}
    let pairTarget : Set halfPair := {q | q.val ∈ W}
    have hMappedNonnegative (x : localDomain) : 0 ≤ (chart x.val.val).1 := by
      change 0 ≤ (∑ v ∈ selected,x.val.val.val v)-1/2
      have hx := x.val.property
      change (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val.val.val v at hx
      linarith only [hx]
    have hInverseInN (q : pairTarget) : inverse ⟨q.val.val,q.property⟩ ∈ N := by
      change (1 : ℝ)/2 ≤ ∑ v ∈ selected,(inverse ⟨q.val.val,q.property⟩).val v
      rw [hSelectedInverse]
      have hq := q.val.property
      change 0 ≤ q.val.val.1 at hq
      linarith only [hq]
    let restrictedHomeomorph : localDomain ≃ₜ pairTarget := {
      toFun := fun x => ⟨⟨chart x.val.val,hMappedNonnegative x⟩,hChartW ⟨x.val.val,x.property⟩⟩
      invFun := fun q => ⟨⟨inverse ⟨q.val.val,q.property⟩,hInverseInN q⟩,hInverseStar ⟨q.val.val,q.property⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        exact hInverseChart ⟨x.val.val,x.property⟩
      right_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        exact hChartInverse ⟨q.val.val,q.property⟩
      continuous_toFun := ((hChartContinuous.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _
      continuous_invFun := (hContinuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _ |>.subtype_mk _ }
    let planePair : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
      (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
    let halfHomeomorph : EuclideanHalfSpace 2 ≃ₜ halfPair := planePair.subtype (by
      intro q
      rfl)
    let targetHalf : Set (EuclideanHalfSpace 2) := halfHomeomorph ⁻¹' pairTarget
    let targetRestriction : pairTarget ≃ₜ targetHalf := halfHomeomorph.symm.subtype (by
      intro q
      change q ∈ pairTarget ↔ halfHomeomorph (halfHomeomorph.symm q) ∈ pairTarget
      rw [halfHomeomorph.apply_symm_apply])
    let halfChartHomeomorph : localDomain ≃ₜ targetHalf := restrictedHomeomorph.trans targetRestriction
    have hLocalDomainOpen : IsOpen localDomain := hStarOpen.preimage continuous_subtype_val
    have hPairTargetOpen : IsOpen pairTarget := hWOpen.preimage continuous_subtype_val
    have hTargetHalfOpen : IsOpen targetHalf := hPairTargetOpen.preimage halfHomeomorph.continuous
    let zeroPoint : W := ⟨(0,0),by
      change 0 < first (0,0) ∧ 0 < second (0,0)
      norm_num [first,second,plus,minus]⟩
    have hZeroN : inverse zeroPoint ∈ N := by
      change (1 : ℝ)/2 ≤ ∑ v ∈ selected,(inverse zeroPoint).val v
      rw [hSelectedInverse]
      norm_num [zeroPoint]
    let sourcePoint : localDomain := ⟨⟨inverse zeroPoint,hZeroN⟩,hInverseStar zeroPoint⟩
    have hSourceNonempty : Nonempty localDomain := ⟨sourcePoint⟩
    have hTargetNonempty : Nonempty targetHalf := hSourceNonempty.map halfChartHomeomorph
    let sourceOpen : TopologicalSpace.Opens N := ⟨localDomain,hLocalDomainOpen⟩
    let targetOpen : TopologicalSpace.Opens (EuclideanHalfSpace 2) := ⟨targetHalf,hTargetHalfOpen⟩
    let actualChart : OpenPartialHomeomorph N (EuclideanHalfSpace 2) :=
      (sourceOpen.openPartialHomeomorphSubtypeCoe hSourceNonempty).symm.trans
        (halfChartHomeomorph.toOpenPartialHomeomorph.trans
          (targetOpen.openPartialHomeomorphSubtypeCoe hTargetNonempty))
    have hActualChartSource : actualChart.source = localDomain := by
      simp [actualChart,OpenPartialHomeomorph.trans_source,sourceOpen]
    refine ⟨actualChart,?_⟩
    intro x hx
    rw [hActualChartSource]
    exact hx
  have actualMixedPoint (P : IntrinsicTwoComplex) (selected : Finset P.Vertex) (x : P.realization)
      (hHalf : (∑ v ∈ selected,x.val v) = (1 : ℝ)/2) :
      ∃ a b : P.Vertex, a ≠ b ∧ a ∈ selected ∧ b ∉ selected ∧
        0 < x.val a ∧ 0 < x.val b ∧ ∃ e : P.Edge, e.val = {a,b} := by
    classical
    have hPositive : 0 < ∑ v ∈ selected,x.val v := by rw [hHalf]; norm_num
    obtain ⟨a,ha,hxa⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun v _ => x.property.1.1 v)).mp hPositive
    have hOutside : ∃ b : P.Vertex, b ∉ selected ∧ 0 < x.val b := by
      by_contra! hn
      have hzero (v) (hv : v ∉ selected) : x.val v = 0 :=
        le_antisymm (hn v hv) (x.property.1.1 v)
      have hsum : (∑ v ∈ selected,x.val v) = ∑ v,x.val v :=
        Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hzero v hv)
      rw [x.property.1.2,hHalf] at hsum
      norm_num at hsum
    obtain ⟨b,hb,hxb⟩ := hOutside
    have hab : a ≠ b := by intro he; exact hb (he ▸ ha)
    obtain ⟨face,hFace,hCarrier⟩ := x.property.2
    have haFace : a ∈ face := by
      by_contra hn
      have he := hCarrier a hn
      linarith only [he,hxa]
    have hbFace : b ∈ face := by
      by_contra hn
      have he := hCarrier b hn
      linarith only [he,hxb]
    have hEdge : ({a,b} : Finset P.Vertex) ∈ P.edges := by
      apply Finset.mem_biUnion.mpr
      refine ⟨face,hFace,Finset.mem_powersetCard.mpr ⟨?_,by simp [hab]⟩⟩
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨haFace,hbFace⟩
    exact ⟨a,b,hab,ha,hb,hxa,hxb,⟨{a,b},hEdge⟩,rfl⟩
  let N : Set P.realization := {x | (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val v}
  change ∃ charts : ChartedSpace (EuclideanHalfSpace 2) N,
    letI := charts
    IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 N
  have hF : Continuous (fun x : P.realization => ∑ v ∈ selected,x.val v) :=
    continuous_finset_sum selected (fun v _ => (continuous_apply v).comp continuous_subtype_val)
  have hLocal (x : N) : ∃ e : OpenPartialHomeomorph N (EuclideanHalfSpace 2), x ∈ e.source := by
    by_cases hStrict : (1 : ℝ)/2 < ∑ v ∈ selected,x.val.val v
    · exact interiorLocalChart ι hι (fun x => ∑ v ∈ selected,x.val v) hF hInterior x hStrict
    · have hx := x.property
      change (1 : ℝ)/2 ≤ ∑ v ∈ selected,x.val.val v at hx
      have hHalf : (∑ v ∈ selected,x.val.val v) = (1 : ℝ)/2 := le_antisymm (le_of_not_gt hStrict) hx
      obtain ⟨a,b,hab,ha,hb,hxa,hxb,e,hEdge⟩ := actualMixedPoint P selected x.val hHalf
      have hYes : (e.val ∩ selected).Nonempty := ⟨a,Finset.mem_inter.mpr ⟨by rw [hEdge]; simp,ha⟩⟩
      have hNo : ¬ e.val ⊆ selected := fun h => hb (h (by rw [hEdge]; simp))
      have hValence := actualMixedValence P selected ι hι hInterior e hYes hNo
      rw [hEdge] at hValence
      obtain ⟨c,d,hac,hbc,had,hbd,hcd,hPlus,hMinus,hFaceSet⟩ := twoFaceArrangement P a b hab hValence
      obtain ⟨chart,hSource⟩ := mixedEdgeLocalChart P selected a b c d hab hac had hbc hbd hcd hPlus hMinus ha hb hFaceSet
      exact ⟨chart,hSource x ⟨hxa,hxb⟩⟩
  choose localChart hSource using hLocal
  let charts : ChartedSpace (EuclideanHalfSpace 2) N := {
    atlas := Set.range localChart
    chartAt := localChart
    mem_chart_source := hSource
    chart_mem_atlas := Set.mem_range_self }
  refine ⟨charts,?_⟩
  letI : ChartedSpace (EuclideanHalfSpace 2) N := charts
  infer_instance

#print axioms actual_half_level_neighborhood_is_surface_with_boundary
end CurveComplex.LocalSurgery
