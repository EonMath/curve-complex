import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualOriginalBoundarySubarcInteriorTransferKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualTerminalMarkedAttachedWalkProjectionKernelRecovery
import Schoenflies.MatchedArc
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualModelSquareClosedCapInteriorKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualUnitSquareModelPlaneKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualBoundaryArcSelectsCutPairKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSameEmbeddedSquareTailCrosscutKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedTailCentralBandAttachmentKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedTailConeFamilyDisjointnessKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualPhysicalTraceTransversalityKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedNegativeComplexSeamSideTransferKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualAffineLogSeamAxisCrossingKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedCollarQuadrilateralInteriorKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedCollarQuadrilateralParameterKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailClosedConeParameterKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailRelativeStripHomotopyKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualSharedMarkedTailCompactStripContinuityKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualBoundaryCornerParameterKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedSharedAxisSectorNamedKernelRecovery
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualNegativeInternalMeshNodeIncidenceKernelRecovery
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Topology.IntersectionParity.ActualMarkedCrossingSign
import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Mathlib.Topology.Subpath
import Mathlib.Order.Interval.Set.Infinite
import CurveComplexGenusTwo.Topology.WeightedSurgery.SupportedEndpointRotation
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualAdjacentMarkedArcSweep
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.MarkedFiniteExcursionProducer
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedPreparedFamilyCover
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Convex.Combination
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects

set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Proposed cancellation selector; intentional sorry pending statement review.
The punctured carrier retains only the chosen initial corner, not both ends of b. -/
theorem actual_adjacent_original_subpaths_punctured_homotopic
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hadj : ArcAdjacent M (Quotient.mk (essentialArcSetoid M) a)
      (Quotient.mk (essentialArcSetoid M) b))
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ q ∈ ArcSurgery.crossings M a b,
      ArcSurgery.CrossesInDisk M a b q)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) :
    ∃ (f g : C(Interval,S)) (u v : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = u ∧ g 0 = u ∧ f 1 = v ∧ g 1 = v ∧ u ≠ v ∧
      range f ∩ range g = {u,v} ∧
      v ∈ ArcSurgery.crossings M a b ∧
      (u ∈ ArcSurgery.crossings M a b ∨
        (u ∈ a.val.image ∩ b.val.image ∧ u ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β := by
  have hane : a.val.map 0 ≠ a.val.map 1 :=
    actualRepresentative_nonloop M a hadj.2.1
  have hbne : b.val.map 0 ≠ b.val.map 1 :=
    actualRepresentative_nonloop M b hadj.2.2.1
  have hcontacts : {t : Interval | b.val.map t ∈ a.val.image}.Finite :=
    actual_nonloop_all_contact_parameters_finite M a b hbne hfinite
  obtain ⟨F,hFzero,hFinjective,hFends,hFmarks,hFterminal⟩ :=
    actual_adjacent_marked_arc_embedded_sweep M a b hadj
  have hFterminalFull : ∀ t : Interval, t ≠ 0 → t ≠ 1 →
      F (1,t) ∉ a.val.image := by
    as_aux_lemma =>
      intro t ht0 ht1 ht
      exact hFterminal t ht0 ht1 ⟨ht,hFmarks 1 t ht0 ht1⟩
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI := (actualSphereSmoothAtlas M).charts
  let oldFamily : Fin 1 → EssentialMarkedArc M := fun _ => a
  have hOldFamilyNonloop : ∀ i,(oldFamily i).val.map 0≠(oldFamily i).val.map 1 := fun _ => hane
  have hOldFamilyDisjoint : ∀ i j,i≠j → Disjoint (arcInterior M (oldFamily i)) (arcInterior M (oldFamily j)) := by
    as_aux_lemma =>
      intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
  have actualConvexChartWithinOpen (U : Set S) (hU : IsOpen U)
      (hUmarks : Disjoint U (M.cover.branch : Set S)) (x : S) (hx : x∈U) :
      ∃ D : OpenPartialHomeomorph S (ℝ × ℝ),x∈D.source ∧
        Convex ℝ D.target ∧ D.source⊆U ∧
        (Disjoint D.source a.val.image ∨
          ∀ y∈D.source,y∈a.val.image ↔ (D y).1=0) := by
    as_aux_lemma =>
      have hxmarks : x∉(M.cover.branch : Set S) := fun hm => (Set.disjoint_left.mp hUmarks) hx hm
      obtain ⟨e,he,hmarks,label,hflat⟩ :=
        actual_disjoint_system_prepared_interior_cover M oldFamily hOldFamilyNonloop hOldFamilyDisjoint x hxmarks
      let L : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
      let D₀ := e.trans L.toOpenPartialHomeomorph
      have hD₀source : D₀.source=e.source := by
        ext y
        simp [D₀,OpenPartialHomeomorph.trans_source]
      have hxD₀ : x∈D₀.source := hD₀source.symm ▸ he
      let W : Set (ℝ × ℝ) := D₀.target ∩ D₀.symm ⁻¹' U
      have hW : IsOpen W := D₀.isOpen_inter_preimage_symm hU
      have hxW : D₀ x∈W := by
        refine ⟨D₀.map_source hxD₀,?_⟩
        change D₀.symm (D₀ x)∈U
        rwa [D₀.left_inv hxD₀]
      obtain ⟨radius,hradius,hball⟩ := Metric.isOpen_iff.mp hW (D₀ x) hxW
      let D := (D₀.symm.restrOpen (Metric.ball (D₀ x) radius) Metric.isOpen_ball).symm
      have hsource : D.source=D₀.source ∩ D₀ ⁻¹' Metric.ball (D₀ x) radius := rfl
      have htarget : D.target=Metric.ball (D₀ x) radius := by
        change D₀.target ∩ Metric.ball (D₀ x) radius=Metric.ball (D₀ x) radius
        exact Set.inter_eq_right.mpr (fun y hy => (hball hy).1)
      refine ⟨D,hsource.symm ▸ ⟨hxD₀,Metric.mem_ball_self hradius⟩,?_,?_,?_⟩
      · rw [htarget]
        exact convex_ball _ _
      · intro y hy
        have hyD₀ := (hsource ▸ hy).1
        have hyU := (hball (hsource ▸ hy).2).2
        change D₀.symm (D₀ y)∈U at hyU
        rwa [D₀.left_inv hyD₀] at hyU
      · cases hlabel : label with
        | none =>
          left
          apply Set.disjoint_left.mpr
          intro y hy hya
          have hye : y∈e.source := hD₀source ▸ (hsource ▸ hy).1
          have hh := (hflat 0 y hye).mp hya
          rw [hlabel] at hh
          cases hh.1
        | some i =>
          right
          intro y hy
          have hye : y∈e.source := hD₀source ▸ (hsource ▸ hy).1
          have hi : i=0 := Subsingleton.elim _ _
          have hf := hflat 0 y hye
          rw [hlabel,hi] at hf
          change y∈a.val.image ↔ (D₀ y).1=0
          change y∈a.val.image ↔ e y 0=0
          simpa only [oldFamily,eq_self,true_and] using hf
  have actualOffComparisonWithinOpen (U : Set S) (hU : IsOpen U)
      (hUmarks : Disjoint U (M.cover.branch : Set S)) (x : S) (hx : x∈U) :
      ∃ y∈U,y∉a.val.image := by
    as_aux_lemma =>
      by_cases hxa : x∈a.val.image
      · obtain ⟨D,hxD,hconvex,hDU,haxis⟩ := actualConvexChartWithinOpen U hU hUmarks x hx
        have hflat : ∀ y∈D.source,y∈a.val.image ↔ (D y).1=0 := by
          rcases haxis with hdis | hflat
          · exact False.elim ((Set.disjoint_left.mp hdis) hxD hxa)
          · exact hflat
        have hcenter : (D x).1=0 := (hflat x hxD).mp hxa
        obtain ⟨radius,hradius,hball⟩ := Metric.isOpen_iff.mp D.open_target (D x) (D.map_source hxD)
        let z : ℝ × ℝ := (radius/2,(D x).2)
        have hz : z∈Metric.ball (D x) radius := by
          rw [Metric.mem_ball,Prod.dist_eq]
          change max (dist (radius/2) (D x).1) (dist (D x).2 (D x).2)<radius
          rw [hcenter,dist_self,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hradius)]
          exact max_lt (half_lt_self hradius) hradius
        have hzD : z∈D.target := hball hz
        refine ⟨D.symm z,hDU (D.map_target hzD),?_⟩
        intro hhit
        have he := (hflat (D.symm z) (D.map_target hzD)).mp hhit
        rw [D.right_inv hzD] at he
        change radius/2=0 at he
        exact (ne_of_gt (half_pos hradius)) he
      · exact ⟨x,hx,hxa⟩
  have finitePathTrans {Y : Type} [TopologicalSpace Y]
      (B : Set Y) {x y z : Y} (p : Path x y) (q : Path y z)
      (hp : (p ⁻¹' B).Finite) (hq : (q ⁻¹' B).Finite) :
      ((p.trans q) ⁻¹' B).Finite := by
    as_aux_lemma =>
      let E0 : Set ℝ := (fun t : Interval => t.val) '' (p ⁻¹' B)
      let E1 : Set ℝ := (fun t : Interval => t.val) '' (q ⁻¹' B)
      let f0 : Interval → ℝ := fun t => 2*t.val
      let f1 : Interval → ℝ := fun t => 2*t.val-1
      have hi0 : Function.Injective f0 := by
        intro t u h
        apply Subtype.ext
        change 2*t.val = 2*u.val at h
        linarith only [h]
      have hi1 : Function.Injective f1 := by
        intro t u h
        apply Subtype.ext
        change 2*t.val-1 = 2*u.val-1 at h
        linarith only [h]
      have h0 : (f0 ⁻¹' E0).Finite := (hp.image _).preimage hi0.injOn
      have h1 : (f1 ⁻¹' E1).Finite := (hq.image _).preimage hi1.injOn
      apply (h0.union h1).subset
      intro t ht
      change (p.trans q) t ∈ B at ht
      by_cases h : t.val ≤ 1/2
      · left
        simp only [Path.trans_apply,dif_pos h] at ht
        exact ⟨⟨2*t.val,by constructor <;> linarith only [h,t.property.1,t.property.2]⟩,ht,rfl⟩
      · right
        simp only [Path.trans_apply,dif_neg h] at ht
        exact ⟨⟨2*t.val-1,by constructor <;> linarith only [h,t.property.1,t.property.2]⟩,ht,rfl⟩
  have convexSegmentFinite (V : Set (ℝ × ℝ)) (hV : Convex ℝ V) (x y : V)
      (hend : x.val.1 ≠ 0 ∨ y.val.1 ≠ 0) :
      ∃ p : Path x y, ({t : Interval | (p t).val.1 = 0}).Finite := by
    as_aux_lemma =>
      let p : Path x y := {
        toFun := fun t => ⟨(1-t.val) • x.val+t.val • y.val,
          hV x.property y.property (by linarith only [t.property.2]) t.property.1 (by ring)⟩
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
  have actualLocalRegularizationInCarrier (U : Set S) (hU : IsOpen U)
      (hUmarks : Disjoint U (M.cover.branch : Set S))
      (D : OpenPartialHomeomorph S (ℝ × ℝ)) (hconvex : Convex ℝ D.target)
      (hDU : D.source⊆U)
      (haxis : Disjoint D.source a.val.image ∨
        ∀ z∈D.source,z∈a.val.image ↔ (D z).1=0)
      {x y : U} (g : Path x y) (hg : ∀ t,(g t : S)∈D.source) :
      ∃ p : Path x y,(∀ t,(p t : S)∈D.source) ∧ p.Homotopic g ∧
        {t : Interval | (p t : S)∈a.val.image}.Finite := by
    as_aux_lemma =>
      rcases haxis with hdis | haxis
      · refine ⟨g,hg,Path.Homotopic.refl g,?_⟩
        apply finite_empty.subset
        intro t ht
        exact False.elim ((Set.disjoint_left.mp hdis) (hg t) ht)
      · have hxD : (x:S)∈D.source := g.source ▸ hg 0
        have hyD : (y:S)∈D.source := g.target ▸ hg 1
        have hDmarks : Disjoint D.source (M.cover.branch : Set S) :=
          hUmarks.mono hDU (Subset.refl _)
        obtain ⟨w,hw,hwoff⟩ := actualOffComparisonWithinOpen D.source D.open_source hDmarks x hxD
        let xs : D.source := ⟨x,hxD⟩
        let ys : D.source := ⟨y,hyD⟩
        let ws : D.source := ⟨w,hw⟩
        let H := D.toHomeomorphSourceTarget
        have hwcoord : (H ws).val.1≠0 := fun hz => hwoff ((haxis w hw).mpr hz)
        obtain ⟨c₀,hc₀⟩ := convexSegmentFinite D.target hconvex (H xs) (H ws) (Or.inr hwcoord)
        obtain ⟨c₁,hc₁⟩ := convexSegmentFinite D.target hconvex (H ws) (H ys) (Or.inl hwcoord)
        let c := c₀.trans c₁
        have hc : (c ⁻¹' {z : D.target | z.val.1=0}).Finite :=
          finitePathTrans {z : D.target | z.val.1=0} c₀ c₁ hc₀ hc₁
        let r : Path xs ys := (c.map H.symm.continuous).cast
          (H.symm_apply_apply xs).symm (H.symm_apply_apply ys).symm
        let inclusion : C(D.source,U) := {
          toFun := fun z => ⟨z.val,hDU z.property⟩
          continuous_toFun := by fun_prop }
        let p : Path x y := r.map inclusion.continuous
        let gs : Path xs ys := {
          toFun := fun t => ⟨(g t:S),hg t⟩
          continuous_toFun := by fun_prop
          source' := by apply Subtype.ext; exact congrArg (fun z : U => (z:S)) g.source
          target' := by apply Subtype.ext; exact congrArg (fun z : U => (z:S)) g.target }
        have hgs : gs.map inclusion.continuous=g := by ext t; rfl
        letI : ContractibleSpace D.target := hconvex.contractibleSpace ⟨H xs,(H xs).property⟩
        letI : ContractibleSpace D.source := H.contractibleSpace_iff.mpr inferInstance
        have hhom : p.Homotopic g := by
          rw [←hgs]
          exact (SimplyConnectedSpace.paths_homotopic r gs).map inclusion
        refine ⟨p,fun t => (r t).property,hhom,hc.subset ?_⟩
        intro t ht
        change (c t).val.1=0
        have hz := (haxis (p t) (r t).property).mp ht
        have he : D (p t)=(c t).val := by
          change (H (H.symm (c t))).val=(c t).val
          rw [H.apply_symm_apply]
        rwa [he] at hz
  have actualRegularizePathInOpenCarrier (U : Set S) (hU : IsOpen U)
      (hUmarks : Disjoint U (M.cover.branch : Set S))
      {x y : U} (g : Path x y) (hxOff : (x:S)∉a.val.image) :
      ∃ p : Path x y,p.Homotopic g ∧ {t : Interval | (p t:S)∈a.val.image}.Finite := by
    as_aux_lemma =>
      have hpoint (t : Interval) :
          ∃ D : OpenPartialHomeomorph S (ℝ × ℝ),(g t:S)∈D.source ∧
            Convex ℝ D.target ∧ D.source⊆U ∧
            (Disjoint D.source a.val.image ∨
              ∀ z∈D.source,z∈a.val.image ↔ (D z).1=0) :=
        actualConvexChartWithinOpen U hU hUmarks (g t) (g t).property
      choose atlas hatlasPoint hatlasConvex hatlasU hatlasAxis using hpoint
      let W : Interval → Set Interval := fun t => {s | (g s:S)∈(atlas t).source}
      have hW : ∀ t,IsOpen (W t) := fun t => (atlas t).open_source.preimage
        (continuous_subtype_val.comp g.continuous)
      have hcover : (Set.univ : Set Interval)⊆⋃ t,W t := by
        intro t _
        exact Set.mem_iUnion.mpr ⟨t,hatlasPoint t⟩
      obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hcover
      obtain ⟨m,hm,hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
      have hmR : (0:ℝ)< m := by exact_mod_cast hm
      let mesh : ℕ → Interval := fun k => ⟨min ((k:ℝ)/m) 1,
        le_min (by positivity) (by norm_num),min_le_right _ _⟩
      have meshValue (k : ℕ) (hk : k≤ m) : (mesh k).val=(k:ℝ)/m := by
        apply min_eq_left
        apply (div_le_one hmR).mpr
        exact_mod_cast hk
      have hmesh0 : mesh 0=0 := by apply Subtype.ext; simp [mesh]
      have hmesh1 : mesh m=1 := by
        apply Subtype.ext
        rw [meshValue m le_rfl,div_self hmR.ne']
        rfl
      have segment (k : ℕ) (hk : k< m) :
          ∃ p : Path (g (mesh k)) (g (mesh (k+1))),
            {t : Interval | (p t:S)∈a.val.image}.Finite ∧
            ∃ d : Path (mesh k) (mesh (k+1)),p.Homotopic (d.map g.continuous) := by
        obtain ⟨t,ht⟩ := hball (mesh k) (Set.mem_univ _)
        let d : Path (mesh k) (mesh (k+1)) := {
          toFun := fun r => ⟨(1-r.val)*(mesh k).val+r.val*(mesh (k+1)).val,by
            constructor
            · exact add_nonneg (mul_nonneg (sub_nonneg.mpr r.property.2) (mesh k).property.1)
                (mul_nonneg r.property.1 (mesh (k+1)).property.1)
            · nlinarith only [r.property.1,r.property.2,(mesh k).property.2,(mesh (k+1)).property.2]⟩
          continuous_toFun := by fun_prop
          source' := by apply Subtype.ext; simp
          target' := by apply Subtype.ext; simp }
        have hd (r : Interval) : ((d.map g.continuous) r:S)∈(atlas t).source := by
          apply ht
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_lt]
          change -δ<(1-r.val)*(mesh k).val+r.val*(mesh (k+1)).val-(mesh k).val ∧
            (1-r.val)*(mesh k).val+r.val*(mesh (k+1)).val-(mesh k).val<δ
          rw [meshValue k hk.le,meshValue (k+1) (by omega)]
          have hstep : ((k+1:ℕ):ℝ)/m=(k:ℝ)/m+(m:ℝ)⁻¹ := by
            rw [Nat.cast_add,Nat.cast_one,add_div,one_div]
          rw [hstep]
          have hmeshpos : (0:ℝ)<(m:ℝ)⁻¹ := inv_pos.mpr hmR
          constructor <;> nlinarith only [hmeshpos,hmesh,r.property.1,r.property.2]
        obtain ⟨p,hp,hhom,hfin⟩ := actualLocalRegularizationInCarrier U hU hUmarks
          (atlas t) (hatlasConvex t) (hatlasU t) (hatlasAxis t) (d.map g.continuous) hd
        exact ⟨p,hfin,d,hhom⟩
      have chain (j : ℕ) (hj : j≤ m) :
          ∃ p : Path (g (mesh 0)) (g (mesh j)),
            {t : Interval | (p t:S)∈a.val.image}.Finite ∧
            ∃ d : Path (mesh 0) (mesh j),p.Homotopic (d.map g.continuous) := by
        induction j with
        | zero =>
          refine ⟨Path.refl (g (mesh 0)),?_,Path.refl (mesh 0),Path.Homotopic.refl _⟩
          apply finite_empty.subset
          intro t ht
          apply hxOff
          change (g (mesh 0):S)∈a.val.image at ht
          rwa [hmesh0,g.source] at ht
        | succ j ih =>
          obtain ⟨p,hpfin,d,hpd⟩ := ih (by omega)
          obtain ⟨q,hqfin,e,hqe⟩ := segment j (by omega)
          refine ⟨p.trans q,finitePathTrans {z : U | (z:S)∈a.val.image} p q hpfin hqfin,d.trans e,?_⟩
          rw [Path.map_trans]
          exact hpd.hcomp hqe
      obtain ⟨p,hpfin,d,hpd⟩ := chain m le_rfl
      let idpath : Path (0:Interval) 1 := {
        toFun := id
        continuous_toFun := continuous_id
        source' := rfl
        target' := rfl }
      let d₀ : Path (mesh 0) (mesh m) := idpath.cast hmesh0 hmesh1
      letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
      have hdom : d.Homotopic d₀ := SimplyConnectedSpace.paths_homotopic d d₀
      have hstart : x=g (mesh 0) := ((congrArg g hmesh0).trans g.source).symm
      have hfinish : y=g (mesh m) := ((congrArg g hmesh1).trans g.target).symm
      let p₀ : Path x y := p.cast hstart hfinish
      have heq : (d₀.map g.continuous).cast hstart hfinish=g := by ext t; rfl
      have hhom : p₀.Homotopic g := by
        rw [←heq]
        exact (hpd.trans (hdom.map g.toContinuousMap)).pathCast hstart hfinish
      exact ⟨p₀,hhom,hpfin⟩
  have actualOffVertexConnectorWithinOpen (U : Set S) (hU : IsOpen U)
      (hUmarks : Disjoint U (M.cover.branch : Set S)) (x : U) :
      ∃ y : U,(y:S)∉a.val.image ∧ Nonempty (Path x y) := by
    as_aux_lemma =>
      obtain ⟨D,hxD,hconvex,hDU,haxis⟩ := actualConvexChartWithinOpen U hU hUmarks x x.property
      have hDmarks : Disjoint D.source (M.cover.branch : Set S) := hUmarks.mono hDU (Subset.refl _)
      obtain ⟨w,hw,hwoff⟩ := actualOffComparisonWithinOpen D.source D.open_source hDmarks x hxD
      let xs : D.source := ⟨x,hxD⟩
      let ws : D.source := ⟨w,hw⟩
      let H := D.toHomeomorphSourceTarget
      have hwcoord : (H ws).val.1≠0 ∨ Disjoint D.source a.val.image := by
        rcases haxis with hdis | hflat
        · exact Or.inr hdis
        · exact Or.inl (fun he => hwoff ((hflat w hw).mpr he))
      have hpath : Nonempty (Path (H xs) (H ws)) := by
        letI : ContractibleSpace D.target := hconvex.contractibleSpace ⟨H xs,(H xs).property⟩
        exact ⟨PathConnectedSpace.somePath (H xs) (H ws)⟩
      obtain ⟨c⟩ := hpath
      let r : Path xs ws := (c.map H.symm.continuous).cast
        (H.symm_apply_apply xs).symm (H.symm_apply_apply ws).symm
      let inclusion : C(D.source,U) := {
        toFun := fun z => ⟨z.val,hDU z.property⟩
        continuous_toFun := by fun_prop }
      exact ⟨⟨w,hDU hw⟩,hwoff,⟨r.map inclusion.continuous⟩⟩
  have actualFiniteBoundaryRelativeGrid (G : C(Interval × Interval,S))
      (hGmarks : ∀ z,G z∉(M.cover.branch : Set S))
      (hGtop : ∀ t,G (1,t)∉a.val.image)
      (hGends : G (0,0)∉a.val.image ∧ G (0,1)∉a.val.image)
      (hGB : {t : Interval | G (0,t)∈a.val.image}.Finite)
      (hGL : {t : Interval | G (t,0)∈a.val.image}.Finite)
      (hGR : {t : Interval | G (t,1)∈a.val.image}.Finite) :
      ∃ (n : ℕ) (hn : 0<n) (mesh : Fin (n+2) → Interval),
        mesh 0=0 ∧ mesh (Fin.last (n+1))=1 ∧ StrictMono mesh ∧
        (∀ i,G (0,mesh i)∉a.val.image ∧ G (mesh i,0)∉a.val.image ∧ G (mesh i,1)∉a.val.image) ∧
        (∀ t : Interval,∃ k : Fin (n+1),mesh k.castSucc≤t ∧ t≤ mesh k.succ) ∧
        ∃ D : Fin (n+1) × Fin (n+1) → OpenPartialHomeomorph S (ℝ × ℝ),
          (∀ k,Convex ℝ (D k).target ∧ Disjoint (D k).source (M.cover.branch : Set S) ∧
            (Disjoint (D k).source a.val.image ∨ ∀ x∈(D k).source,x∈a.val.image ↔ (D k x).1=0)) ∧
          ∀ k z,mesh k.1.castSucc≤z.1 → z.1≤ mesh k.1.succ →
            mesh k.2.castSucc≤z.2 → z.2≤ mesh k.2.succ → G z∈(D k).source := by
    as_aux_lemma =>
      let unmarked : Set S := (M.cover.branch : Set S)ᶜ
      have hunmarkedOpen : IsOpen unmarked := M.cover.branch.finite_toSet.isClosed.isOpen_compl
      have hunmarkedMarks : Disjoint unmarked (M.cover.branch : Set S) :=
        Set.disjoint_left.mpr (fun _ hx hm => hx hm)
      have hpoint (z : Interval × Interval) :
          ∃ D : OpenPartialHomeomorph S (ℝ × ℝ),G z∈D.source ∧ Convex ℝ D.target ∧
            D.source⊆unmarked ∧ (Disjoint D.source a.val.image ∨
              ∀ x∈D.source,x∈a.val.image ↔ (D x).1=0) :=
        actualConvexChartWithinOpen unmarked hunmarkedOpen hunmarkedMarks (G z) (hGmarks z)
      choose convexChart hconvexPoint hconvexTarget hconvexUnmarked hconvexAxis using hpoint
      have haloFiniteGrid {I : Type} (U : I → Set S) (hU : ∀ i, IsOpen (U i))
          (hcov : ∀ z : Interval × Interval, ∃ i, G z ∈ U i) :
          ∃ n : ℕ, 0 < n ∧ ∃ chart : Fin (n+1) × Fin (n+1) → I,
            ∀ k : Fin (n+1) × Fin (n+1), ∀ z : Interval × Interval,
              (k.1.val-1 : ℝ)/n ≤ z.1.val → z.1.val ≤ (k.1.val+1 : ℝ)/n →
              (k.2.val-1 : ℝ)/n ≤ z.2.val → z.2.val ≤ (k.2.val+1 : ℝ)/n →
              G z ∈ U (chart k) := by
        let V : I → Set (Interval × Interval) := fun i => G ⁻¹' U i
        have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage G.continuous
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
          constructor <;> linarith only [hlo,hhi,hmesh]
        exact ⟨hcoord k.1 z.1 ht0 ht1,hcoord k.2 z.2 hs0 hs1⟩
      let chartDomain : (Interval × Interval) → Set S := fun z => (convexChart z).source
      have hDomainOpen : ∀ z,IsOpen (chartDomain z) := fun z => (convexChart z).open_source
      have hgridCover : ∀ z : Interval × Interval,∃ i,G z∈chartDomain i :=
        fun z => ⟨z,hconvexPoint z⟩
      obtain ⟨n,hn,chart,hgrid⟩ := haloFiniteGrid chartDomain hDomainOpen hgridCover
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
      let bad : Set Interval := {t | G (0,t)∈a.val.image} ∪ {t | G (t,0)∈a.val.image} ∪ {t | G (t,1)∈a.val.image}
      have hbad : bad.Finite := (hGB.union hGL).union hGR
      obtain ⟨phase,hphase0,hphase1,hphaseAvoid⟩ := endpointAvoidingPhase bad hbad n hn
      let phasePoint : Fin n → Interval := fun k =>
        ⟨(k.val+phase)/n,by
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn
          constructor
          · exact (div_pos (by positivity) hnR).le
          · apply (div_le_one hnR).mpr
            have hkR : (k.val : ℝ)+1 ≤ n := by exact_mod_cast k.isLt
            linarith only [hkR,hphase1]⟩
      have phasePointStrict (i j : Fin n) (hij : i < j) : phasePoint i < phasePoint j := by
        change (i.val+phase)/(n : ℝ) < (j.val+phase)/(n : ℝ)
        apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hn)).mpr
        have hijR : (i.val : ℝ) < j.val := by exact_mod_cast hij
        linarith only [hijR]
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
              linarith only [hiR]
          · simp only [phaseGrid,h0,dif_neg,h1]
            change (i.val-1 : ℝ)/n ≤ (((i.val-1 : ℕ) : ℝ)+phase)/n ∧
              (((i.val-1 : ℕ) : ℝ)+phase)/n ≤ (i.val : ℝ)/n
            have hiR : ((i.val-1 : ℕ) : ℝ) = (i.val : ℝ)-1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ i.val),Nat.cast_one]
            rw [hiR]
            constructor
            · exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith only [hphase0,hphase1])
            · exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith only [hphase0,hphase1])
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
            linarith only [hiR,hphase1]
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
          G z ∈ chartDomain (chart k) := by
        apply hgrid k z
        · exact (phaseGridBounds k.1.castSucc).1.trans ht0
        · have ht1R : z.1.val ≤ (phaseGrid k.1.succ).val := ht1
          have h := ht1R.trans (phaseGridBounds k.1.succ).2
          simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one] using h
        · exact (phaseGridBounds k.2.castSucc).1.trans hs0
        · have hs1R : z.2.val ≤ (phaseGrid k.2.succ).val := hs1
          have h := hs1R.trans (phaseGridBounds k.2.succ).2
          simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one] using h
      have hgridBoundaryClear (i : Fin (n+2)) :
          G (0,phaseGrid i)∉a.val.image ∧ G (phaseGrid i,0)∉a.val.image ∧ G (phaseGrid i,1)∉a.val.image := by
        by_cases hi0 : i.val=0
        · have he : phaseGrid i=0 := by simp only [phaseGrid,dif_pos hi0]
          rw [he]
          exact ⟨hGends.1,hGends.1,hGends.2⟩
        · by_cases hi1 : i.val=n+1
          · have he : phaseGrid i=1 := by simp only [phaseGrid,dif_neg hi0,dif_pos hi1]
            rw [he]
            exact ⟨hGends.2,hGtop 0,hGtop 1⟩
          · have hav : phaseGrid i∉bad := by
              apply hphaseAvoid ⟨i.val-1,by omega⟩ (phaseGrid i)
              simp only [phaseGrid,dif_neg hi0,dif_neg hi1,phasePoint]
            exact ⟨fun h => hav (Or.inl (Or.inl h)),fun h => hav (Or.inl (Or.inr h)),fun h => hav (Or.inr h)⟩
      refine ⟨n,hn,phaseGrid,by simp [phaseGrid],by simp [phaseGrid],phaseGridStrict,hgridBoundaryClear,phaseGridCovers,
        fun k => convexChart (chart k),?_,?_⟩
      · intro k
        exact ⟨hconvexTarget (chart k),hunmarkedMarks.mono (hconvexUnmarked (chart k)) (Subset.refl _),hconvexAxis (chart k)⟩
      · exact phaseGridCellCover
  have actualCompatibleGridVertexConnectors (G : C(Interval × Interval,S))
      (hGmarks : ∀ z,G z∉(M.cover.branch : Set S)) (hGtop : ∀ t,G (1,t)∉a.val.image)
      (n : ℕ) (mesh : Fin (n+2) → Interval) (hzero : mesh 0=0)
      (hone : mesh (Fin.last (n+1))=1)
      (hclear : ∀ i,G (0,mesh i)∉a.val.image ∧ G (mesh i,0)∉a.val.image ∧ G (mesh i,1)∉a.val.image)
      (D : Fin (n+1) × Fin (n+1) → OpenPartialHomeomorph S (ℝ × ℝ))
      (hcontains : ∀ k z,mesh k.1.castSucc≤z.1 → z.1≤ mesh k.1.succ →
        mesh k.2.castSucc≤z.2 → z.2≤ mesh k.2.succ → G z∈(D k).source) :
      ∃ vertices : (Fin (n+2) × Fin (n+2)) → S,
        (∀ v,vertices v∉a.val.image ∧ vertices v∉(M.cover.branch : Set S)) ∧
        ∃ connectors : ∀ v,Path (G (mesh v.1,mesh v.2)) (vertices v),
          (∀ v t,connectors v t∉(M.cover.branch : Set S)) ∧
          (∀ v k t,mesh k.1.castSucc≤ mesh v.1 → mesh v.1≤ mesh k.1.succ →
            mesh k.2.castSucc≤ mesh v.2 → mesh v.2≤ mesh k.2.succ → connectors v t∈(D k).source) ∧
          (∀ v,v.1=0 ∨ v.1=Fin.last (n+1) ∨ v.2=0 ∨ v.2=Fin.last (n+1) →
            ∀ t,connectors v t=G (mesh v.1,mesh v.2)) := by
    as_aux_lemma =>
      let gridVertex (v : Fin (n+2) × Fin (n+2)) : Interval × Interval := (mesh v.1,mesh v.2)
      let incident (k : Fin (n+1) × Fin (n+1)) (v : Fin (n+2) × Fin (n+2)) : Prop :=
        mesh k.1.castSucc≤ mesh v.1 ∧ mesh v.1≤ mesh k.1.succ ∧
          mesh k.2.castSucc≤ mesh v.2 ∧ mesh v.2≤ mesh k.2.succ
      let boundary (v : Fin (n+2) × Fin (n+2)) : Prop :=
        v.1=0 ∨ v.1=Fin.last (n+1) ∨ v.2=0 ∨ v.2=Fin.last (n+1)
      have hboundaryOff (v : Fin (n+2) × Fin (n+2)) (hv : boundary v) : G (gridVertex v)∉a.val.image := by
        rcases hv with hv | hv | hv | hv
        · change G (mesh v.1,mesh v.2)∉a.val.image
          rw [hv,hzero]
          exact (hclear v.2).1
        · change G (mesh v.1,mesh v.2)∉a.val.image
          rw [hv,hone]
          exact hGtop (mesh v.2)
        · change G (mesh v.1,mesh v.2)∉a.val.image
          rw [hv,hzero]
          exact (hclear v.1).2.1
        · change G (mesh v.1,mesh v.2)∉a.val.image
          rw [hv,hone]
          exact (hclear v.1).2.2
      let U (v : Fin (n+2) × Fin (n+2)) : Set S :=
        (M.cover.branch : Set S)ᶜ ∩ ⋂ k,if incident k v then (D k).source else Set.univ
      have hUopen (v : Fin (n+2) × Fin (n+2)) : IsOpen (U v) := by
        apply M.cover.branch.finite_toSet.isClosed.isOpen_compl.inter
        apply isOpen_iInter_of_finite
        intro k
        split_ifs
        · exact (D k).open_source
        · exact isOpen_univ
      have hUmarks (v : Fin (n+2) × Fin (n+2)) : Disjoint (U v) (M.cover.branch : Set S) :=
        Set.disjoint_left.mpr (fun _ hx hm => hx.1 hm)
      have hOriginalInU (v : Fin (n+2) × Fin (n+2)) : G (gridVertex v)∈U v := by
        refine ⟨hGmarks (gridVertex v),Set.mem_iInter.mpr ?_⟩
        intro k
        split_ifs with hk
        · exact hcontains k (gridVertex v) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
        · exact Set.mem_univ _
      let originalVertex (v : Fin (n+2) × Fin (n+2)) : U v := ⟨G (gridVertex v),hOriginalInU v⟩
      have hvertexData (v : Fin (n+2) × Fin (n+2)) :
          ∃ x : U v,∃ d : Path (originalVertex v) x,
            (x:S)∉a.val.image ∧ (boundary v → ∀ t,d t=originalVertex v) := by
        by_cases hv : boundary v
        · exact ⟨originalVertex v,Path.refl (originalVertex v),hboundaryOff v hv,fun _ _ => rfl⟩
        · obtain ⟨x,hx,⟨d⟩⟩ := actualOffVertexConnectorWithinOpen (U v) (hUopen v) (hUmarks v) (originalVertex v)
          exact ⟨x,d,hx,fun hb => False.elim (hv hb)⟩
      choose vertex connector hVertexOff hBoundaryConstant using hvertexData
      let vertices (v : Fin (n+2) × Fin (n+2)) : S := (vertex v:S)
      let connectors (v : Fin (n+2) × Fin (n+2)) : Path (G (gridVertex v)) (vertices v) :=
        (connector v).map continuous_subtype_val
      refine ⟨vertices,fun v => ⟨hVertexOff v,(vertex v).property.1⟩,connectors,?_,?_,?_⟩
      · intro v t
        exact (connector v t).property.1
      · intro v k t h₀ h₁ h₂ h₃
        have hk : incident k v := ⟨h₀,h₁,h₂,h₃⟩
        have hm := Set.mem_iInter.mp (connector v t).property.2 k
        change (connector v t:S)∈(D k).source
        simpa only [if_pos hk] using hm
      · intro v hv t
        exact congrArg (fun z : U v => (z:S)) (hBoundaryConstant v hv t)
  have actualCompatibleSharedEdge (G : C(Interval × Interval,S))
      (hGmarks : ∀ z,G z∉(M.cover.branch : Set S))
      (n : ℕ) (mesh : Fin (n+2) → Interval)
      (D : Fin (n+1) × Fin (n+1) → OpenPartialHomeomorph S (ℝ × ℝ))
      (hcontains : ∀ k z,mesh k.1.castSucc≤z.1 → z.1≤ mesh k.1.succ →
        mesh k.2.castSucc≤z.2 → z.2≤ mesh k.2.succ → G z∈(D k).source)
      (vertices : (Fin (n+2) × Fin (n+2)) → S) (hOff : ∀ v,vertices v∉a.val.image)
      (connectors : ∀ v,Path (G (mesh v.1,mesh v.2)) (vertices v))
      (hConnectorMarks : ∀ v t,connectors v t∉(M.cover.branch : Set S))
      (hConnectorCharts : ∀ v k t,mesh k.1.castSucc≤ mesh v.1 → mesh v.1≤ mesh k.1.succ →
        mesh k.2.castSucc≤ mesh v.2 → mesh v.2≤ mesh k.2.succ → connectors v t∈(D k).source)
      (v w : Fin (n+2) × Fin (n+2)) :
      ∃ original : Path (G (mesh v.1,mesh v.2)) (G (mesh w.1,mesh w.2)),
        (∀ t,original t=G
          (⟨(1-t.val)*(mesh v.1).val+t.val*(mesh w.1).val,by
            constructor
            · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (mesh v.1).property.1)
                (mul_nonneg t.property.1 (mesh w.1).property.1)
            · nlinarith only [t.property.1,t.property.2,(mesh v.1).property.2,(mesh w.1).property.2]⟩,
           ⟨(1-t.val)*(mesh v.2).val+t.val*(mesh w.2).val,by
            constructor
            · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (mesh v.2).property.1)
                (mul_nonneg t.property.1 (mesh w.2).property.1)
            · nlinarith only [t.property.1,t.property.2,(mesh v.2).property.2,(mesh w.2).property.2]⟩)) ∧
        (∀ k t,mesh k.1.castSucc≤ mesh v.1 → mesh v.1≤ mesh k.1.succ →
          mesh k.2.castSucc≤ mesh v.2 → mesh v.2≤ mesh k.2.succ →
          mesh k.1.castSucc≤ mesh w.1 → mesh w.1≤ mesh k.1.succ →
          mesh k.2.castSucc≤ mesh w.2 → mesh w.2≤ mesh k.2.succ → original t∈(D k).source) ∧
        ∃ p : Path (vertices v) (vertices w),
          (p ⁻¹' a.val.image).Finite ∧ (∀ t,p t∉(M.cover.branch : Set S)) ∧
          (∀ k t,mesh k.1.castSucc≤ mesh v.1 → mesh v.1≤ mesh k.1.succ →
            mesh k.2.castSucc≤ mesh v.2 → mesh v.2≤ mesh k.2.succ →
            mesh k.1.castSucc≤ mesh w.1 → mesh w.1≤ mesh k.1.succ →
            mesh k.2.castSucc≤ mesh w.2 → mesh w.2≤ mesh k.2.succ → p t∈(D k).source) ∧
          ∃ (U : Set S) (hx : vertices v∈U) (hy : vertices w∈U),
            IsOpen U ∧ Disjoint U (M.cover.branch : Set S) ∧
            ∃ α β : Path (⟨vertices v,hx⟩ : U) ⟨vertices w,hy⟩,
              (∀ t,(α t:S)=p t) ∧
              (∀ t,(β t:S)=((connectors v).symm.trans original |>.trans (connectors w)) t) ∧
              α.Homotopic β := by
    as_aux_lemma =>
      let gridVertex (x : Fin (n+2) × Fin (n+2)) : Interval × Interval := (mesh x.1,mesh x.2)
      let incident (k : Fin (n+1) × Fin (n+1)) (x : Fin (n+2) × Fin (n+2)) : Prop :=
        mesh k.1.castSucc≤ mesh x.1 ∧ mesh x.1≤ mesh k.1.succ ∧
          mesh k.2.castSucc≤ mesh x.2 ∧ mesh x.2≤ mesh k.2.succ
      let d : Path (gridVertex v) (gridVertex w) := {
        toFun := fun t =>
          (⟨(1-t.val)*(mesh v.1).val+t.val*(mesh w.1).val,by
            constructor
            · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (mesh v.1).property.1)
                (mul_nonneg t.property.1 (mesh w.1).property.1)
            · nlinarith only [t.property.1,t.property.2,(mesh v.1).property.2,(mesh w.1).property.2]⟩,
           ⟨(1-t.val)*(mesh v.2).val+t.val*(mesh w.2).val,by
            constructor
            · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (mesh v.2).property.1)
                (mul_nonneg t.property.1 (mesh w.2).property.1)
            · nlinarith only [t.property.1,t.property.2,(mesh v.2).property.2,(mesh w.2).property.2]⟩)
        continuous_toFun := by fun_prop
        source' := by apply Prod.ext <;> apply Subtype.ext <;> simp [gridVertex]
        target' := by apply Prod.ext <;> apply Subtype.ext <;> simp [gridVertex] }
      let original := d.map G.continuous
      let I := {k : Fin (n+1) × Fin (n+1) // incident k v ∧ incident k w}
      let U : Set S := (M.cover.branch : Set S)ᶜ ∩ ⋂ k : I,(D k.val).source
      have hU : IsOpen U := M.cover.branch.finite_toSet.isClosed.isOpen_compl.inter
        (isOpen_iInter_of_finite (fun k => (D k.val).open_source))
      have hUmarks : Disjoint U (M.cover.branch : Set S) := Set.disjoint_left.mpr (fun _ hx hm => hx.1 hm)
      have hleftU (t : Interval) : connectors v t∈U := by
        refine ⟨hConnectorMarks v t,Set.mem_iInter.mpr ?_⟩
        intro k
        exact hConnectorCharts v k.val t k.property.1.1 k.property.1.2.1 k.property.1.2.2.1 k.property.1.2.2.2
      have hrightU (t : Interval) : connectors w t∈U := by
        refine ⟨hConnectorMarks w t,Set.mem_iInter.mpr ?_⟩
        intro k
        exact hConnectorCharts w k.val t k.property.2.1 k.property.2.2.1 k.property.2.2.2.1 k.property.2.2.2.2
      have hcoordinateBounds (l u x y : Interval) (hlx : l≤x) (hxu : x≤u)
          (hly : l≤y) (hyu : y≤u) (t : Interval) :
          l.val≤(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val≤u.val := by
        have hL₀ := mul_nonneg (sub_nonneg.mpr (show l.val≤x.val from hlx)) (sub_nonneg.mpr t.property.2)
        have hL₁ := mul_nonneg (sub_nonneg.mpr (show l.val≤y.val from hly)) t.property.1
        have hU₀ := mul_nonneg (sub_nonneg.mpr (show x.val≤u.val from hxu)) (sub_nonneg.mpr t.property.2)
        have hU₁ := mul_nonneg (sub_nonneg.mpr (show y.val≤u.val from hyu)) t.property.1
        constructor
        · nlinarith only [hL₀,hL₁]
        · nlinarith only [hU₀,hU₁]
      have horiginalU (t : Interval) : original t∈U := by
        refine ⟨hGmarks (d t),Set.mem_iInter.mpr ?_⟩
        intro k
        have h₀ := hcoordinateBounds (mesh k.val.1.castSucc) (mesh k.val.1.succ) (mesh v.1) (mesh w.1)
          k.property.1.1 k.property.1.2.1 k.property.2.1 k.property.2.2.1 t
        have h₁ := hcoordinateBounds (mesh k.val.2.castSucc) (mesh k.val.2.succ) (mesh v.2) (mesh w.2)
          k.property.1.2.2.1 k.property.1.2.2.2 k.property.2.2.2.1 k.property.2.2.2.2 t
        exact hcontains k.val (d t) h₀.1 h₀.2 h₁.1 h₁.2
      let candidate := ((connectors v).symm.trans original).trans (connectors w)
      have hcU : Set.range candidate⊆U := by
        rw [Path.trans_range,Path.trans_range,Path.symm_range]
        exact Set.union_subset (Set.union_subset (by rintro _ ⟨t,rfl⟩; exact hleftU t)
          (by rintro _ ⟨t,rfl⟩; exact horiginalU t)) (by rintro _ ⟨t,rfl⟩; exact hrightU t)
      have hx : vertices v∈U := candidate.source ▸ hcU ⟨0,rfl⟩
      have hy : vertices w∈U := candidate.target ▸ hcU ⟨1,rfl⟩
      let β : Path (⟨vertices v,hx⟩ : U) ⟨vertices w,hy⟩ := {
        toFun := fun t => ⟨candidate t,hcU ⟨t,rfl⟩⟩
        continuous_toFun := by fun_prop
        source' := by apply Subtype.ext; exact candidate.source
        target' := by apply Subtype.ext; exact candidate.target }
      obtain ⟨α,hhom,hfinite⟩ := actualRegularizePathInOpenCarrier U hU hUmarks β (hOff v)
      let p := α.map continuous_subtype_val
      refine ⟨original,fun _ => rfl,?_,p,hfinite,?_,?_,U,hx,hy,hU,hUmarks,α,β,fun _ => rfl,fun _ => rfl,hhom⟩
      · intro k t hv₀ hv₁ hv₂ hv₃ hw₀ hw₁ hw₂ hw₃
        let ki : I := ⟨k,⟨hv₀,hv₁,hv₂,hv₃⟩,⟨hw₀,hw₁,hw₂,hw₃⟩⟩
        exact Set.mem_iInter.mp (horiginalU t).2 ki
      · intro t
        exact (α t).property.1
      · intro k t hv₀ hv₁ hv₂ hv₃ hw₀ hw₁ hw₂ hw₃
        let ki : I := ⟨k,⟨hv₀,hv₁,hv₂,hv₃⟩,⟨hw₀,hw₁,hw₂,hw₃⟩⟩
        exact Set.mem_iInter.mp (α t).property.2 ki
  have squareCoordinateBounds (z : {z : ℝ × ℝ // ‖z‖ ≤ 1}) :
      (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
    as_aux_lemma =>
      simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using z.property
  let squareCoordinates : {z : ℝ × ℝ // ‖z‖ ≤ 1} ≃ₜ Interval × Interval := {
    toFun := fun z =>
      (⟨(z.val.1+1)/2,by constructor <;> linarith [(squareCoordinateBounds z).1.1,(squareCoordinateBounds z).1.2]⟩,
       ⟨(z.val.2+1)/2,by constructor <;> linarith [(squareCoordinateBounds z).2.1,(squareCoordinateBounds z).2.2]⟩)
    invFun := fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
      simp only [Prod.norm_mk,Real.norm_eq_abs,max_le_iff,abs_le]
      constructor <;> constructor <;> linarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩
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
    as_aux_lemma =>
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
            refine ⟨(⟨1 - ‖(z : ℝ × ℝ)‖, by constructor <;> linarith [z.property, norm_nonneg (z : ℝ × ℝ)]⟩, u), ?_⟩
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
    as_aux_lemma =>
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
    as_aux_lemma =>
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
    as_aux_lemma =>
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
    as_aux_lemma =>
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
    as_aux_lemma =>
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
    as_aux_lemma =>
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
  let actualIntervalSegment (x y : Interval) : C(Interval,Interval) := {
    toFun := fun t => ⟨(1-t.val)*x.val+t.val*y.val,by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property.1)
          (mul_nonneg t.property.1 y.property.1)
      · nlinarith only [t.property.1,t.property.2,x.property.2,y.property.2]⟩
    continuous_toFun := by fun_prop }
  have actualIntervalSegmentFiniteContacts (B : Set Interval) (hB : B.Finite)
      (x y : Interval) (hx : x∉B) : (actualIntervalSegment x y ⁻¹' B).Finite := by
    as_aux_lemma =>
      by_cases hxy : x=y
      · have hconstant (t : Interval) : actualIntervalSegment x y t=x := by
          apply Subtype.ext
          change (1-t.val)*x.val+t.val*y.val=x.val
          rw [←hxy]
          ring
        apply finite_empty.subset
        intro t ht
        exact False.elim (hx (hconstant t ▸ ht))
      · apply hB.preimage
        intro t _ u _ he
        have hv := congrArg Subtype.val he
        change (1-t.val)*x.val+t.val*y.val=(1-u.val)*x.val+u.val*y.val at hv
        have hden : y.val-x.val≠0 := by
          intro heq
          apply hxy
          apply Subtype.ext
          exact (sub_eq_zero.mp heq).symm
        apply Subtype.ext
        apply mul_left_cancel₀ hden
        nlinarith only [hv]
  have actualBoundaryOriginalSegmentFinite (G : C(Interval × Interval,S))
      (hGtop : ∀ t,G (1,t)∉a.val.image)
      (hGB : {t : Interval | G (0,t)∈a.val.image}.Finite)
      (hGL : {t : Interval | G (t,0)∈a.val.image}.Finite)
      (hGR : {t : Interval | G (t,1)∈a.val.image}.Finite)
      (x y : Interval × Interval) (hxOff : G x∉a.val.image)
      (original : Path (G x) (G y))
      (hformula : ∀ t,original t=G (actualIntervalSegment x.1 y.1 t,actualIntervalSegment x.2 y.2 t))
      (hboundary : (x.1=y.1 ∧ (x.1=0 ∨ x.1=1)) ∨ (x.2=y.2 ∧ (x.2=0 ∨ x.2=1))) :
      (original ⁻¹' a.val.image).Finite := by
    as_aux_lemma =>
      have hconstant (c : Interval) (t : Interval) : actualIntervalSegment c c t=c := by
        apply Subtype.ext
        change (1-t.val)*c.val+t.val*c.val=c.val
        ring
      rcases hboundary with ⟨heq,hzero|hone⟩ | ⟨heq,hzero|hone⟩
      · have hoff : x.2∉{t : Interval | G (0,t)∈a.val.image} := by
          intro hhit
          apply hxOff
          change G (0,x.2)∈a.val.image at hhit
          have he : x=(0,x.2) := Prod.ext hzero rfl
          rwa [he]
        apply (actualIntervalSegmentFiniteContacts {t : Interval | G (0,t)∈a.val.image} hGB x.2 y.2 hoff).subset
        intro t ht
        change G (0,actualIntervalSegment x.2 y.2 t)∈a.val.image
        change original t∈a.val.image at ht
        rw [hformula t,←heq,hconstant,hzero] at ht
        exact ht
      · apply finite_empty.subset
        intro t ht
        change original t∈a.val.image at ht
        rw [hformula t,←heq,hconstant,hone] at ht
        exact False.elim (hGtop (actualIntervalSegment x.2 y.2 t) ht)
      · have hoff : x.1∉{t : Interval | G (t,0)∈a.val.image} := by
          intro hhit
          apply hxOff
          change G (x.1,0)∈a.val.image at hhit
          have he : x=(x.1,0) := Prod.ext rfl hzero
          rwa [he]
        apply (actualIntervalSegmentFiniteContacts {t : Interval | G (t,0)∈a.val.image} hGL x.1 y.1 hoff).subset
        intro t ht
        change G (actualIntervalSegment x.1 y.1 t,0)∈a.val.image
        change original t∈a.val.image at ht
        rw [hformula t,←heq,hconstant,hzero] at ht
        exact ht
      · have hoff : x.1∉{t : Interval | G (t,1)∈a.val.image} := by
          intro hhit
          apply hxOff
          change G (x.1,1)∈a.val.image at hhit
          have he : x=(x.1,1) := Prod.ext rfl hone
          rwa [he]
        apply (actualIntervalSegmentFiniteContacts {t : Interval | G (t,1)∈a.val.image} hGR x.1 y.1 hoff).subset
        intro t ht
        change G (actualIntervalSegment x.1 y.1 t,1)∈a.val.image
        change original t∈a.val.image at ht
        rw [hformula t,←heq,hconstant,hone] at ht
        exact ht
  have actualCoherentFiniteCellGlue (n : ℕ) (mesh : Fin (n+2) → Interval)
      (hstrict : StrictMono mesh)
      (hcover : ∀ t : Interval,∃ k : Fin (n+1),mesh k.castSucc≤t ∧ t≤ mesh k.succ)
      (cells : Fin (n+1) × Fin (n+1) → C(Interval × Interval,S))
      (hvertical : ∀ i j : Fin (n+1),i.val+1=j.val → ∀ k t,cells (i,k) (1,t)=cells (j,k) (0,t))
      (hhorizontal : ∀ i j : Fin (n+1),i.val+1=j.val → ∀ k t,cells (k,i) (t,1)=cells (k,j) (t,0)) :
      ∃ coord : Fin (n+1) → C(Interval,Interval),
        (∀ k t,mesh k.castSucc≤t → t≤ mesh k.succ → actualIntervalSegment (mesh k.castSucc) (mesh k.succ) (coord k t)=t) ∧
        (∀ k,coord k (mesh k.castSucc)=0) ∧ (∀ k,coord k (mesh k.succ)=1) ∧
        ∃ H : C(Interval × Interval,S),∀ k z,
          mesh k.1.castSucc≤z.1 → z.1≤ mesh k.1.succ →
          mesh k.2.castSucc≤z.2 → z.2≤ mesh k.2.succ → H z=cells k (coord k.1 z.1,coord k.2 z.2) := by
    as_aux_lemma =>
      let phaseGrid := mesh
      have phaseGridStrict : StrictMono phaseGrid := hstrict
      have phaseGridCovers (t : Interval) : ∃ k : Fin (n+1),phaseGrid k.castSucc≤t ∧ t≤ phaseGrid k.succ := hcover t
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
          (div_le_one hgap).mpr (by linarith only [ht1R])
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
      obtain ⟨H,hH⟩ := coherentCellGlue cells
        (fun i j s hij k => hvertical i j hij k s)
        (fun i j t hij k => hhorizontal i j hij k t)
      refine ⟨localCoordinate,?_,localCoordinateLeft,localCoordinateRight,H,?_⟩
      · intro k t hlo hhi
        apply Subtype.ext
        change (1-(localCoordinate k t).val)*(phaseGrid k.castSucc).val+
          (localCoordinate k t).val*(phaseGrid k.succ).val=t.val
        rw [localCoordinateOnCell k t hlo hhi]
        have hgap : (phaseGrid k.succ).val-(phaseGrid k.castSucc).val≠0 := ne_of_gt (sub_pos.mpr (phaseStep k))
        field_simp [hgap]
        <;> ring
      · intro k z h₀ h₁ h₂ h₃
        exact hH k z ⟨h₀,h₁,h₂,h₃⟩
  have actualMarkedConeZeroRadial (D : OpenPartialHomeomorph S (ℝ × ℝ))
      (cell : C(Interval × Interval,S))
      (loop : C({z : ℝ × ℝ // ‖z‖=1},D.target)) (center : D.target)
      (hRange : ∀ x,cell x∈D.source)
      (haxis : ∀ x∈D.source,x∈a.val.image ↔ (D x).1=0)
      (hcenterOff : center.val.1≠0)
      (hCone : ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          D (cell (squareCoordinates u))=(1-r.val) • (loop z).val+r.val • center.val) :
      let N := {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1/center.val.1≤0}
      ∃ q : C(N,Interval × Interval),Function.Injective q ∧
        (∀ z,cell (q z)∈a.val.image) ∧
        ∀ z,∃ u : {z : ℝ × ℝ // ‖z‖≤1},q z=squareCoordinates u ∧
          u.val=(1/(1-(loop z.val).val.1/center.val.1)) • z.val.val := by
    as_aux_lemma =>
      dsimp only
      let c := (center).val.1
      have hc : c ≠ 0 := hcenterOff
      let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (loop z).val.1 / c ≤ 0}
      let h : C(N,ℝ) := ⟨fun z => (loop z.val).val.1 / c,by fun_prop⟩
      have hnonpos (z : N) : h z ≤ 0 := z.property
      have hden (z : N) : 0 < 1-h z := by linarith only [hnonpos z]
      let radius : C(N,Interval) :=
        ⟨fun z => ⟨1/(1-h z),⟨(one_div_pos.mpr (hden z)).le,
          (div_le_one (hden z)).mpr (by linarith only [hnonpos z])⟩⟩,
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
      let r : Interval := ⟨1-(radius z).val,by constructor <;> linarith only [(radius z).property.1,(radius z).property.2]⟩
      obtain ⟨u,hu,hval⟩ := hCone r z.val
      have he : u = radial z := by
        apply Subtype.ext
        rw [hu]
        change (1-(1-(radius z).val)) • z.val.val = (radius z).val • z.val.val
        congr 1
        ring
      rw [he] at hval
      apply (haxis _ (hRange (q z))).mpr
      have hfirst := congrArg Prod.fst hval
      change (D (cell (q z))).1 =
        (1-r.val)*(loop z.val).val.1+r.val*c at hfirst
      have hrval : 1-r.val = (radius z).val := by change 1-(1-(radius z).val) = (radius z).val; ring
      rw [hrval] at hfirst
      rw [hfirst]
      change (1/(1-(loop z.val).val.1/c))*
        (loop z.val).val.1+
        (1-1/(1-(loop z.val).val.1/c))*c = 0
      have hd : 1-(loop z.val).val.1/c ≠ 0 := (hden z).ne'
      have hsub : c-(loop z.val).val.1 ≠ 0 := by
        intro he
        have heq := sub_eq_zero.mp he
        rw [← heq,div_self hc,sub_self] at hd
        exact hd rfl
      field_simp [hc,hd,hsub]
      <;> ring
  have actualMarkedConeCellZeroSet (D : OpenPartialHomeomorph S (ℝ × ℝ))
      (cell : C(Interval × Interval,S))
      (loop : C({z : ℝ × ℝ // ‖z‖=1},D.target)) (center : D.target)
      (hRange : ∀ x,cell x∈D.source)
      (haxis : ∀ x∈D.source,x∈a.val.image ↔ (D x).1=0)
      (hcenterOff : center.val.1≠0)
      (hCone : ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          D (cell (squareCoordinates u))=(1-r.val) • (loop z).val+r.val • center.val) :
      let N := {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1/center.val.1≤0}
      ∃ q : C(N,Interval × Interval),Function.Injective q ∧
        Set.range q={x | cell x∈a.val.image} ∧
        ∀ z,∃ u : {z : ℝ × ℝ // ‖z‖≤1},q z=squareCoordinates u ∧
          u.val=(1/(1-(loop z.val).val.1/center.val.1)) • z.val.val := by
    as_aux_lemma =>
      dsimp only
      obtain ⟨q,hqi,hqb,hqformula⟩ := actualMarkedConeZeroRadial D cell loop center hRange haxis hcenterOff hCone
      refine ⟨q,hqi,?_,hqformula⟩
      ext x
      constructor
      · rintro ⟨z,rfl⟩; exact hqb z
      · intro hx
        let u := squareCoordinates.symm x
        let c := (center).val.1
        have hc : c ≠ 0 := hcenterOff
        have hxu : x = squareCoordinates u := (squareCoordinates.apply_symm_apply x).symm
        have hu0 : u.val ≠ 0 := by
          intro hu0
          let z0 : {z : ℝ × ℝ // ‖z‖ = 1} := ⟨(1,0),by norm_num [Prod.norm_def]⟩
          obtain ⟨v,hv,hformula⟩ := hCone 1 z0
          have hvu : v = u := by apply Subtype.ext; simpa [hu0] using hv
          rw [hvu] at hformula
          have hz := (haxis _ (hRange x)).mp hx
          rw [hxu] at hz
          have hf : D (cell (squareCoordinates u)) = center := by
            simpa using hformula
          rw [hf] at hz
          exact hc hz
        have hn : 0 < ‖u.val‖ := norm_pos_iff.mpr hu0
        let z : {z : ℝ × ℝ // ‖z‖ = 1} :=
          ⟨‖u.val‖⁻¹ • u.val,by
            rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']⟩
        let r : Interval := ⟨1-‖u.val‖,by constructor <;> linarith only [u.property,hn]⟩
        obtain ⟨v,hv,hformula⟩ := hCone r z
        have hvu : v = u := by
          apply Subtype.ext
          rw [hv]
          change (1-(1-‖u.val‖)) • (‖u.val‖⁻¹ • u.val) = u.val
          have he : 1-(1-‖u.val‖) = ‖u.val‖ := by ring
          rw [he,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
        rw [hvu] at hformula
        have hz := (haxis _ (hRange x)).mp hx
        rw [hxu] at hz
        have hfirst := congrArg Prod.fst hformula
        change (D (cell (squareCoordinates u))).1 =
          (1-r.val)*(loop z).val.1+r.val*c at hfirst
        rw [hz] at hfirst
        have hr : 1-r.val = ‖u.val‖ := by change 1-(1-‖u.val‖) = ‖u.val‖; ring
        rw [hr] at hfirst
        have heq : ‖u.val‖*((loop z).val.1/c)+(1-‖u.val‖) = 0 := by
          apply (mul_right_cancel₀ hc)
          field_simp [hc]
          nlinarith only [hfirst]
        have hneg : (loop z).val.1/c ≤ 0 := by
          by_contra hh
          have hhpos : 0 < (loop z).val.1/c := lt_of_not_ge hh
          have hprod := mul_pos hn hhpos
          linarith only [u.property,hprod,heq]
        let zn := (⟨z,hneg⟩ : {z : {z : ℝ × ℝ // ‖z‖ = 1} |
          (loop z).val.1/(center).val.1 ≤ 0})
        obtain ⟨w,hw,hwrad⟩ := hqformula zn
        have hd : 0 < 1-(loop z).val.1/c := by linarith only [hneg]
        have hrad : 1/(1-(loop z).val.1/c) = ‖u.val‖ := by
          apply (div_eq_iff hd.ne').mpr
          nlinarith only [heq]
        have hwu : w = u := by
          apply Subtype.ext
          rw [hwrad]
          change (1/(1-(loop z).val.1/c)) • (‖u.val‖⁻¹ • u.val) = u.val
          rw [hrad,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
        exact ⟨zn,hw.trans ((congrArg squareCoordinates hwu).trans hxu.symm)⟩
  have unitSquareBoundaryCompact : CompactSpace {z : ℝ × ℝ // ‖z‖ = 1} := by
    as_aux_lemma =>
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
  have actualMarkedConeCellGeometry (D : OpenPartialHomeomorph S (ℝ × ℝ))
      (cell : C(Interval × Interval,S))
      (loop : C({z : ℝ × ℝ // ‖z‖=1},D.target)) (center : D.target)
      (hRange : ∀ x,cell x∈D.source)
      (haxes : Disjoint D.source a.val.image ∨ ∀ x∈D.source,x∈a.val.image ↔ (D x).1=0)
      (hcenter : Disjoint D.source a.val.image ∨ center.val.1≠0)
      (hCone : ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          D (cell (squareCoordinates u))=(1-r.val) • (loop z).val+r.val • center.val) :
      (∀ x,cell x∉a.val.image) ∨
        (let N := {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1/center.val.1≤0}
         ∃ q : C(N,Interval × Interval),IsEmbedding q ∧ Set.range q={x | cell x∈a.val.image}) := by
    as_aux_lemma =>
      by_cases hoff : Disjoint D.source a.val.image
      · exact Or.inl (fun x hx => (Set.disjoint_left.mp hoff) (hRange x) hx)
      · right
        have haxis := haxes.resolve_left hoff
        have hc := hcenter.resolve_left hoff
        obtain ⟨q,hqi,hqrange,hqformula⟩ := actualMarkedConeCellZeroSet D cell loop center hRange haxis hc hCone
        letI := unitSquareBoundaryCompact
        have hN : IsClosed {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1/center.val.1≤0} :=
          isClosed_le (by fun_prop) continuous_const
        letI := isCompact_iff_compactSpace.mp hN.isCompact
        exact ⟨q,(q.continuous.isClosedEmbedding hqi).isEmbedding,hqrange⟩
  have actualSquareBoundaryContactsFinite (cell : C(Interval × Interval,S))
      (bottom right top left : C(Interval,S))
      (hbottom : (bottom ⁻¹' a.val.image).Finite) (hright : (right ⁻¹' a.val.image).Finite)
      (htop : (top ⁻¹' a.val.image).Finite) (hleft : (left ⁻¹' a.val.image).Finite)
      (hfaces : ∀ t,cell (t,0)=bottom t ∧ cell (1,t)=right t ∧ cell (t,1)=top t ∧ cell (0,t)=left t) :
      {z : {z : ℝ × ℝ // ‖z‖=1} | cell (squareCoordinates ⟨z.val,z.property.le⟩)∈a.val.image}.Finite := by
    as_aux_lemma =>
      let skeleton : Set (Interval × Interval) :=
        {z | (z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) ∧ cell z∈a.val.image}
      have hSkeleton : skeleton.Finite := by
        have firstFixed (r : Interval) (p : C(Interval,S)) (hp : (p ⁻¹' a.val.image).Finite)
            (hface : ∀ t, cell (r,t) = p t) :
            ({z : Interval × Interval | z.1 = r ∧ cell z ∈ a.val.image}).Finite := by
          apply Set.Finite.of_injOn (f := Prod.snd) (t := p ⁻¹' a.val.image) _ _ hp
          · rintro z ⟨hz,hb⟩
            change p z.2 ∈ a.val.image
            rw [← hface z.2,← hz]
            exact hb
          · intro z hz w hw he
            exact Prod.ext (hz.1.trans hw.1.symm) he
        have secondFixed (r : Interval) (p : C(Interval,S)) (hp : (p ⁻¹' a.val.image).Finite)
            (hface : ∀ t, cell (t,r) = p t) :
            ({z : Interval × Interval | z.2 = r ∧ cell z ∈ a.val.image}).Finite := by
          apply Set.Finite.of_injOn (f := Prod.fst) (t := p ⁻¹' a.val.image) _ _ hp
          · rintro z ⟨hz,hb⟩
            change p z.1 ∈ a.val.image
            rw [← hface z.1,← hz]
            exact hb
          · intro z hz w hw he
            exact Prod.ext he (hz.1.trans hw.1.symm)
        have hl := firstFixed 0 left hleft (fun t => (hfaces t).2.2.2)
        have hr := firstFixed 1 right hright (fun t => (hfaces t).2.1)
        have hb := secondFixed 0 bottom hbottom (fun t => (hfaces t).1)
        have ht := secondFixed 1 top htop (fun t => (hfaces t).2.2.1)
        apply (((hl.union hr).union hb).union ht).subset
        rintro z ⟨hz,hB⟩
        rcases hz with hz | hz | hz | hz
        · exact Or.inl (Or.inl (Or.inl ⟨hz,hB⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hz,hB⟩))
        · exact Or.inl (Or.inr ⟨hz,hB⟩)
        · exact Or.inr ⟨hz,hB⟩
      let f : {z : ℝ × ℝ // ‖z‖ = 1} → Interval × Interval :=
        fun z => squareCoordinates ⟨z.val,z.property.le⟩
      apply Set.Finite.of_injOn (f := f) (t := skeleton) _ _ (hSkeleton)
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
            linarith only [hx]
          · left
            apply Subtype.ext
            change (z.val.1+1)/2 = 0
            rw [abs_of_neg (lt_of_not_ge hpos)] at hx
            linarith only [hx]
        · by_cases hpos : 0 ≤ z.val.2
          · right; right; right
            apply Subtype.ext
            change (z.val.2+1)/2 = 1
            rw [abs_of_nonneg hpos] at hy
            linarith only [hy]
          · right; right; left
            apply Subtype.ext
            change (z.val.2+1)/2 = 0
            rw [abs_of_neg (lt_of_not_ge hpos)] at hy
            linarith only [hy]
      · intro z hz w hw he
        have hh := squareCoordinates.injective he
        exact Subtype.ext (congrArg (fun a : {z : ℝ × ℝ // ‖z‖ ≤ 1} => a.val) hh)
  have actualBoundaryLoopAxisZerosFinite (D : OpenPartialHomeomorph S (ℝ × ℝ))
      (cell : C(Interval × Interval,S))
      (loop : C({z : ℝ × ℝ // ‖z‖=1},D.target)) (center : D.target)
      (hRange : ∀ x,cell x∈D.source)
      (haxis : ∀ x∈D.source,x∈a.val.image ↔ (D x).1=0)
      (hCone : ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          D (cell (squareCoordinates u))=(1-r.val) • (loop z).val+r.val • center.val)
      (hFinite : {z : {z : ℝ × ℝ // ‖z‖=1} |
        cell (squareCoordinates ⟨z.val,z.property.le⟩)∈a.val.image}.Finite) :
      {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1=0}.Finite := by
    as_aux_lemma =>
      have hFormula (z : {z : ℝ × ℝ // ‖z‖=1}) :
          D (cell (squareCoordinates ⟨z.val,z.property.le⟩))=(loop z).val := by
        obtain ⟨u,hu,hv⟩ := hCone 0 z
        have he : u=⟨z.val,z.property.le⟩ := by
          apply Subtype.ext
          simpa using hu
        rw [he] at hv
        simpa using hv
      apply hFinite.subset
      intro z hz
      apply (haxis _ (hRange _)).mpr
      rw [hFormula]
      exact hz
  have actualConeLowerLeftCornerPositive (D : OpenPartialHomeomorph S (ℝ × ℝ))
      (cell : C(Interval × Interval,S))
      (loop : C({z : ℝ × ℝ // ‖z‖=1},D.target)) (center : D.target)
      (hCenter : D (cell (0,0))=center.val) (hOff : center.val.1≠0)
      (hCone : ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          D (cell (squareCoordinates u))=(1-r.val) • (loop z).val+r.val • center.val) :
      ∃ z : {z : ℝ × ℝ // ‖z‖=1},0<(loop z).val.1/center.val.1 := by
    as_aux_lemma =>
      let z : {z : ℝ × ℝ // ‖z‖=1} :=
        ⟨(-1,-1),by norm_num [Prod.norm_def,Real.norm_eq_abs]⟩
      obtain ⟨u,hu,hv⟩ := hCone 0 z
      have he : u=⟨z.val,z.property.le⟩ := by
        apply Subtype.ext
        simpa using hu
      have hs : squareCoordinates ⟨z.val,z.property.le⟩=(0,0) := by
        apply Prod.ext <;> apply Subtype.ext <;> norm_num [squareCoordinates,z]
      rw [he,hs,hCenter] at hv
      have hl : (loop z).val=center.val := by simpa using hv.symm
      refine ⟨z,?_⟩
      rw [hl,div_self hOff]
      norm_num
  have actualFiniteZeroMesh (g : C(Interval,ℝ)) (hf : (g ⁻¹' {0}).Finite) :
      ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,
        StrictMono mesh ∧ mesh 0 = 0 ∧ mesh (Fin.last (m+1)) = 1 ∧
        (∀ j, mesh j=0 ∨ mesh j=1 ∨ g (mesh j)=0) ∧
        ∀ (i : Fin (m+1)) (t : Interval),
          mesh i.castSucc < t → t < mesh i.succ → g t ≠ 0 := by
    as_aux_lemma =>
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
      have hnodes (j : Fin (m+2)) : e j=0 ∨ e j=1 ∨ g (e j)=0 := by
        have hj : e j ∈ P := by
          have hr : e j ∈ Set.range e := ⟨j,rfl⟩
          rw [Finset.range_orderEmbOfFin] at hr
          exact hr
        rcases Finset.mem_union.mp hj with hj | hj
        · right; right
          exact hf.mem_toFinset.mp hj
        · have hh : e j=0 ∨ e j=1 := by simpa using hj
          exact hh.elim Or.inl (fun h => Or.inr (Or.inl h))
      refine ⟨m,e,hmono,hz,ho,hnodes,?_⟩
      intro i t ht0 ht1 hgt
      have htP : t ∈ P := Finset.mem_union_left _ (hf.mem_toFinset.mpr hgt)
      have hr : t ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact htP
      obtain ⟨j,hj⟩ := hr
      have hj0 := hmono.lt_iff_lt.mp (hj ▸ ht0)
      have hj1 := hmono.lt_iff_lt.mp (hj ▸ ht1)
      change i.val < j.val at hj0
      change j.val < i.val+1 at hj1
      omega
  have actualNoZeroIntervalSign (g : C(Interval,ℝ)) (x y s : Interval)
      (hxs : x < s) (hsy : s < y) (hs : g s < 0)
      (hn : ∀ t, x < t → t < y → g t ≠ 0) :
      ∀ t ∈ Set.Icc x y, g t ≤ 0 := by
    as_aux_lemma =>
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
  have actualIntervalSignConstant (g : C(Interval,ℝ))
      (x y s t : Interval) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
      (hn : ∀ z, x < z → z < y → g z ≠ 0) :
      g s < 0 ↔ g t < 0 := by
    as_aux_lemma =>
      constructor
      · intro h
        exact lt_of_le_of_ne (actualNoZeroIntervalSign g x y s hs.1 hs.2 h hn t
          ⟨ht.1.le,ht.2.le⟩) (hn t ht.1 ht.2)
      · intro h
        exact lt_of_le_of_ne (actualNoZeroIntervalSign g x y t ht.1 ht.2 h hn s
          ⟨hs.1.le,hs.2.le⟩) (hn s hs.1 hs.2)
  have actualOrderedMeshCovers {m : ℕ} (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (hzero : mesh 0 = 0) (hone : mesh (Fin.last (m+1)) = 1) :
      ∀ t : Interval, ∃ k : Fin (m+1), mesh k.castSucc ≤ t ∧ t ≤ mesh k.succ := by
    as_aux_lemma =>
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
  have actualFiniteNegativeIntervals (g : C(Interval,ℝ)) (hf : (g ⁻¹' {0}).Finite) :
      ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval, ∃ negative : Fin (m+1) → Prop,
        StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
        (∀ j,mesh j=0 ∨ mesh j=1 ∨ g (mesh j)=0) ∧
        (∀ (j : Fin (m+1)) (t : Interval),mesh j.castSucc < t → t < mesh j.succ → g t≠0) ∧
        (∀ j,negative j → ∀ t∈Set.Icc (mesh j.castSucc) (mesh j.succ),g t≤0) ∧
        ∀ t,g t≤0 ↔ g t=0 ∨ ∃ j,negative j ∧ t∈Set.Icc (mesh j.castSucc) (mesh j.succ) := by
    as_aux_lemma =>
      obtain ⟨m,mesh,hm,h0,h1,hnodes,hno⟩ := actualFiniteZeroMesh g hf
      let midpoint (j : Fin (m+1)) : Interval :=
        ⟨((mesh j.castSucc).val+(mesh j.succ).val)/2,by
          constructor <;> linarith only [(mesh j.castSucc).property.1,(mesh j.castSucc).property.2,
            (mesh j.succ).property.1,(mesh j.succ).property.2]⟩
      have hmid (j : Fin (m+1)) : mesh j.castSucc < midpoint j ∧ midpoint j < mesh j.succ := by
        have hs : (mesh j.castSucc).val < (mesh j.succ).val := hm (by change j.val < j.val+1; omega)
        constructor
        · change (mesh j.castSucc).val < ((mesh j.castSucc).val+(mesh j.succ).val)/2
          linarith only [hs]
        · change ((mesh j.castSucc).val+(mesh j.succ).val)/2 < (mesh j.succ).val
          linarith only [hs]
      let negative (j : Fin (m+1)) : Prop := g (midpoint j)<0
      have hnegative (j : Fin (m+1)) (hj : negative j) :
          ∀ t∈Set.Icc (mesh j.castSucc) (mesh j.succ),g t≤0 :=
        actualNoZeroIntervalSign g _ _ (midpoint j) (hmid j).1 (hmid j).2 hj (hno j)
      refine ⟨m,mesh,negative,hm,h0,h1,hnodes,hno,hnegative,?_⟩
      intro t
      constructor
      · intro ht
        by_cases hz : g t=0
        · exact Or.inl hz
        right
        obtain ⟨j,hj0,hj1⟩ := actualOrderedMeshCovers mesh hm h0 h1 t
        refine ⟨j,?_,hj0,hj1⟩
        by_contra hn
        have hmidpos : 0<g (midpoint j) :=
          lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hno j _ (hmid j).1 (hmid j).2))
        let ng : C(Interval,ℝ) := ⟨fun s => -g s,g.continuous.neg⟩
        have hngmid : ng (midpoint j)<0 := neg_neg_of_pos hmidpos
        have hngno (s : Interval) (hs0 : mesh j.castSucc < s) (hs1 : s < mesh j.succ) : ng s≠0 :=
          neg_ne_zero.mpr (hno j s hs0 hs1)
        have hnonpos := actualNoZeroIntervalSign ng _ _ (midpoint j) (hmid j).1 (hmid j).2
          hngmid hngno t ⟨hj0,hj1⟩
        change -g t≤0 at hnonpos
        exact hz (le_antisymm ht (neg_nonpos.mp hnonpos))
      · rintro (hz | ⟨j,hj,ht⟩)
        · exact hz.le
        · exact hnegative j hj t ht
  let actualBoundaryFaceRaw : Fin 4 → Interval → ℝ × ℝ := fun i t =>
    if i.val=0 then (2*t.val-1,-1) else if i.val=1 then (1,2*t.val-1)
    else if i.val=2 then (2*t.val-1,1) else (-1,2*t.val-1)
  have hActualBoundaryFaceNorm (i : Fin 4) (t : Interval) : ‖actualBoundaryFaceRaw i t‖=1 := by
    as_aux_lemma =>
      have ha : |2*t.val-1| ≤ 1 := abs_le.mpr (by
        constructor <;> linarith only [t.property.1,t.property.2])
      fin_cases i <;> simp [actualBoundaryFaceRaw,Prod.norm_def,Real.norm_eq_abs,
        max_eq_left ha,max_eq_right ha]
  let actualBoundaryFace : Fin 4 → C(Interval,{z : ℝ × ℝ // ‖z‖=1}) := fun i =>
    ⟨fun t => ⟨actualBoundaryFaceRaw i t,hActualBoundaryFaceNorm i t⟩,by
      fin_cases i <;> simp [actualBoundaryFaceRaw] <;> fun_prop⟩
  have hActualBoundaryFaceInjective (i : Fin 4) : Function.Injective (actualBoundaryFace i) := by
    as_aux_lemma =>
      intro x y he
      have heq := congrArg Subtype.val he
      fin_cases i
      · have hh := congrArg Prod.fst heq
        apply Subtype.ext
        change 2*x.val-1=2*y.val-1 at hh
        linarith only [hh]
      · have hh := congrArg Prod.snd heq
        apply Subtype.ext
        change 2*x.val-1=2*y.val-1 at hh
        linarith only [hh]
      · have hh := congrArg Prod.fst heq
        apply Subtype.ext
        change 2*x.val-1=2*y.val-1 at hh
        linarith only [hh]
      · have hh := congrArg Prod.snd heq
        apply Subtype.ext
        change 2*x.val-1=2*y.val-1 at hh
        linarith only [hh]
  have actualFaceScalarZerosFinite
      (g : C({z : ℝ × ℝ // ‖z‖=1},ℝ))
      (hf : (g ⁻¹' {0}).Finite) (i : Fin 4) :
      ((g.comp (actualBoundaryFace i)) ⁻¹' {0}).Finite := by
    as_aux_lemma =>
      change (actualBoundaryFace i ⁻¹' (g ⁻¹' {0})).Finite
      exact hf.preimage (hActualBoundaryFaceInjective i).injOn
  let actualIntervalMidpoint (x y : Interval) : Interval := ⟨(x.val+y.val)/2,by
    constructor <;> linarith only [x.property.1,x.property.2,y.property.1,y.property.2]⟩
  have actualFiniteFaceRadialComponents (D : OpenPartialHomeomorph S (ℝ × ℝ))
      (cell : C(Interval × Interval,S))
      (loop : C({z : ℝ × ℝ // ‖z‖=1},D.target)) (center : D.target)
      (hRange : ∀ x,cell x∈D.source)
      (haxis : ∀ x∈D.source,x∈a.val.image ↔ (D x).1=0)
      (hc : center.val.1≠0)
      (hCone : ∀ (r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          D (cell (squareCoordinates u))=(1-r.val) • (loop z).val+r.val • center.val)
      (hfinite : {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1=0}.Finite)
      (i : Fin 4) :
      let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (loop z).val.1 / (center).val.1 ≤ 0}
      ∃ (m : ℕ) (mesh : Fin (m+2) → Interval) (q : C(N,Interval × Interval)),
        StrictMono mesh ∧ mesh 0 = 0 ∧ mesh (Fin.last (m+1)) = 1 ∧
        (∀ (j : Fin (m+1)) (t : Interval), mesh j.castSucc < t → t < mesh j.succ →
          (loop (actualBoundaryFace i t)).val.1 ≠ 0) ∧
        (∀ z : N, (loop z.val).val.1 = 0 →
          q z = squareCoordinates ⟨z.val.val,z.val.property.le⟩) ∧
        (∀ z : N, ∃ u : {z : ℝ × ℝ // ‖z‖ ≤ 1}, q z = squareCoordinates u ∧
          u.val = (1/(1-(loop z.val).val.1 /
            (center).val.1)) • z.val.val) ∧
        ∀ j : Fin (m+1),
          (loop (actualBoundaryFace i
            (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)))).val.1 /
            (center).val.1 < 0 →
          ∃ p : C(Interval,Interval × Interval), Topology.IsEmbedding p ∧
            (∀ t, cell (p t) ∈ a.val.image) ∧
            (∀ t, ∃ (r : Interval) (z : N),
              r.val = (1-t.val)*(mesh j.castSucc).val+t.val*(mesh j.succ).val ∧
              z.val = actualBoundaryFace i r ∧ p t = q z ∧
              (t ∈ Set.Ioo (0 : Interval) 1 →
                (loop z.val).val.1 / (center).val.1 < 0)) ∧
            ∃ zl zr : N, zl.val = actualBoundaryFace i (mesh j.castSucc) ∧
              zr.val = actualBoundaryFace i (mesh j.succ) ∧ p 0 = q zl ∧ p 1 = q zr := by
    as_aux_lemma =>
      dsimp only
      let g0 : C(Interval,ℝ) := ⟨fun t => (loop (actualBoundaryFace i t)).val.1,by fun_prop⟩
      have hf0 : (g0 ⁻¹' {0}).Finite := by
        change (actualBoundaryFace i ⁻¹' {z : {z : ℝ × ℝ // ‖z‖=1} | (loop z).val.1=0}).Finite
        exact hfinite.preimage (hActualBoundaryFaceInjective i).injOn
      obtain ⟨m,mesh,hm,hzero,hone,hnodes,hno⟩ := actualFiniteZeroMesh g0 hf0
      obtain ⟨q,hqi,hqb,hqformula⟩ := actualMarkedConeZeroRadial D cell loop center hRange haxis hc hCone
      let c := (center).val.1
      have hc0 : c ≠ 0 := hc
      let N := {z : {z : ℝ × ℝ // ‖z‖ = 1} |
        (loop z).val.1/c ≤ 0}
      have hfix (z : N) (hz : (loop z.val).val.1 = 0) :
          q z = squareCoordinates ⟨z.val.val,z.val.property.le⟩ := by
        obtain ⟨w,hw,hwrad⟩ := hqformula z
        have he : w = ⟨z.val.val,z.val.property.le⟩ := by
          apply Subtype.ext
          simpa [hz] using hwrad
        exact hw.trans (congrArg squareCoordinates he)
      let g : C(Interval,ℝ) :=
        ⟨fun t => (loop (actualBoundaryFace i t)).val.1/c,by fun_prop⟩
      refine ⟨m,mesh,q,hm,hzero,hone,hno,hfix,hqformula,?_⟩
      intro j hneg
      let x := mesh j.castSucc
      let y := mesh j.succ
      have hxy : x < y := hm (by change j.val < j.val+1; omega)
      let s := actualIntervalMidpoint x y
      have hxs : x < s := by change x.val < (x.val+y.val)/2; have hh : x.val < y.val := hxy; linarith only [hh]
      have hsy : s < y := by change (x.val+y.val)/2 < y.val; have hh : x.val < y.val := hxy; linarith only [hh]
      have hn : ∀ t, x < t → t < y → g t ≠ 0 := by
        intro t ht0 ht1
        exact div_ne_zero (hno j t ht0 ht1) hc
      have hsign : ∀ t ∈ Set.Icc x y, g t ≤ 0 := actualNoZeroIntervalSign g x y s hxs hsy hneg hn
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
        constructor <;> nlinarith only [t.property.1,t.property.2,hh]
      have hdi : Function.Injective d := by
        intro t u he
        apply Subtype.ext
        have hh := congrArg Subtype.val he
        change (1-t.val)*x.val+t.val*y.val = (1-u.val)*x.val+u.val*y.val at hh
        have hlt : x.val < y.val := hxy
        nlinarith only [hh,hlt]
      let f : C(Interval,N) := ⟨fun t => ⟨actualBoundaryFace i (d t),hsign _ (hd t)⟩,by fun_prop⟩
      have hfi : Function.Injective f := by
        intro t u he
        exact hdi (hActualBoundaryFaceInjective i (congrArg Subtype.val he))
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
      · change actualBoundaryFace i (d 0) = actualBoundaryFace i x
        rw [d.source]
      · change actualBoundaryFace i (d 1) = actualBoundaryFace i y
        rw [d.target]
  have actualIntervalSegmentInjective (x y : Interval) (hxy : x<y) :
      Function.Injective (actualIntervalSegment x y) := by
    as_aux_lemma =>
      intro t u he
      have hh := congrArg Subtype.val he
      change (1-t.val)*x.val+t.val*y.val=(1-u.val)*x.val+u.val*y.val at hh
      have hxyR : x.val<y.val := hxy
      apply Subtype.ext
      nlinarith only [hh,hxyR]
  have actualIntervalSegmentBounds (x y : Interval) (hxy : x<y) (t : Interval) :
      x≤actualIntervalSegment x y t ∧ actualIntervalSegment x y t≤y := by
    as_aux_lemma =>
      have hxyR : x.val<y.val := hxy
      change x.val≤(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val≤y.val
      constructor <;> nlinarith only [hxyR,t.property.1,t.property.2]
  have actualAffineCellEmbedding (x₀ x₁ y₀ y₁ : Interval) (hx : x₀<x₁) (hy : y₀<y₁) :
      ∃ f : C(Interval × Interval,Interval × Interval),IsEmbedding f ∧
        (∀ z,f z=(actualIntervalSegment x₀ x₁ z.1,actualIntervalSegment y₀ y₁ z.2)) ∧
        ∀ z,x₀≤(f z).1 ∧ (f z).1≤x₁ ∧ y₀≤(f z).2 ∧ (f z).2≤y₁ := by
    as_aux_lemma =>
      let f : C(Interval × Interval,Interval × Interval) :=
        ⟨fun z => (actualIntervalSegment x₀ x₁ z.1,actualIntervalSegment y₀ y₁ z.2),by fun_prop⟩
      have hfi : Function.Injective f := by
        intro z w he
        exact Prod.ext (actualIntervalSegmentInjective x₀ x₁ hx (congrArg Prod.fst he))
          (actualIntervalSegmentInjective y₀ y₁ hy (congrArg Prod.snd he))
      refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,fun _ => rfl,?_⟩
      intro z
      exact ⟨(actualIntervalSegmentBounds x₀ x₁ hx z.1).1,(actualIntervalSegmentBounds x₀ x₁ hx z.1).2,
        (actualIntervalSegmentBounds y₀ y₁ hy z.2).1,(actualIntervalSegmentBounds y₀ y₁ hy z.2).2⟩
  have actualZeroIsMeshNode (g : C(Interval,ℝ)) (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (h0 : mesh 0=0) (h1 : mesh (Fin.last (m+1))=1)
      (hno : ∀ (j : Fin (m+1)) (t : Interval),mesh j.castSucc < t → t < mesh j.succ → g t≠0)
      (t : Interval) (ht : g t=0) : ∃ j,mesh j=t := by
    as_aux_lemma =>
      obtain ⟨j,hj0,hj1⟩ := actualOrderedMeshCovers mesh hmono h0 h1 t
      by_cases he0 : mesh j.castSucc=t
      · exact ⟨j.castSucc,he0⟩
      by_cases he1 : t=mesh j.succ
      · exact ⟨j.succ,he1.symm⟩
      exact False.elim (hno j t (lt_of_le_of_ne hj0 he0) (lt_of_le_of_ne hj1 he1) ht)
  have actualMarkedAdjacentIntervalsOppositeSigns
      (u : unitInterval) (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1)
      (γ : C(unitInterval, S)) (hγ : Set.InjOn γ (Set.Ioo 0 1))
      (hγimage : Set.range γ ⊆ b.val.image) (hcross : ArcSurgery.CrossesInDisk M a b (γ u))
      (C : OpenPartialHomeomorph S (ℝ × ℝ)) (hpC : γ u ∈ C.source)
      (hCa : ∀ x ∈ C.source, x ∈ a.val.image ↔ (C x).1 = 0)
      (g : C(Interval,ℝ)) (c : ℝ) (hc : c ≠ 0)
      (hg : ∀ t, g t = (C (γ t)).1 / c)
      (x y sl sr : Interval) (hxu : x < u) (huy : u < y)
      (hsl : sl ∈ Set.Ioo x u) (hsr : sr ∈ Set.Ioo u y)
      (hleft : ∀ z, x < z → z < u → g z ≠ 0)
      (hright : ∀ z, u < z → z < y → g z ≠ 0) :
      g sl < 0 ↔ ¬ g sr < 0 := by
    as_aux_lemma =>
      obtain ⟨δ,hδ,hflip⟩ := actual_marked_transverse_uncentered_axis_signs_flip
        M a b u hu γ hγ hγimage hcross C hpC hCa
      have hlo : max (x : ℝ) ((u : ℝ)-δ/2) < (u : ℝ) :=
        max_lt (show (x : ℝ) < (u : ℝ) from hxu) (by linarith only [hδ])
      obtain ⟨v,hv0,hv1⟩ := exists_between hlo
      have hvI : v ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact x.property.1.trans (le_max_left _ _ |>.trans hv0.le)
        · exact hv1.le.trans u.property.2
      let vI : Interval := ⟨v,hvI⟩
      have hhi : (u : ℝ) < min (y : ℝ) ((u : ℝ)+δ/2) :=
        lt_min (show (u : ℝ) < (y : ℝ) from huy) (by linarith only [hδ])
      obtain ⟨w,hw0,hw1⟩ := exists_between hhi
      have hwI : w ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact u.property.1.trans hw0.le
        · exact hw1.le.trans ((min_le_left _ _).trans y.property.2)
      let wI : Interval := ⟨w,hwI⟩
      have hvnear : (u : ℝ)-δ < vI := by
        change (u : ℝ)-δ < v
        have hh := (le_max_right _ _).trans_lt hv0
        linarith only [hh,hδ]
      have hwnear : (wI : ℝ) < (u : ℝ)+δ := by
        change w < (u : ℝ)+δ
        have hh := hw1.trans_le (min_le_right _ _)
        linarith only [hh,hδ]
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
      have hl := actualIntervalSignConstant g x u vI sl hvleft hsl hleft
      have hr := actualIntervalSignConstant g u y wI sr hwright hsr hright
      exact hl.symm.trans (hsample.trans (not_congr hr))
  
  have actualBoundaryFaceCover (z : {z : ℝ × ℝ // ‖z‖=1}) :
      ∃ (i : Fin 4) (t : Interval),actualBoundaryFace i t=z := by
    as_aux_lemma =>
      have hn : max |z.val.1| |z.val.2|=1 := by
        simpa only [Prod.norm_def,Real.norm_eq_abs] using z.property
      have hx : |z.val.1|≤1 := (le_max_left _ _).trans hn.le
      have hy : |z.val.2|≤1 := (le_max_right _ _).trans hn.le
      let tx : Interval := ⟨(z.val.1+1)/2,by
        obtain ⟨h₀,h₁⟩ := abs_le.mp hx
        constructor <;> linarith only [h₀,h₁]⟩
      let ty : Interval := ⟨(z.val.2+1)/2,by
        obtain ⟨h₀,h₁⟩ := abs_le.mp hy
        constructor <;> linarith only [h₀,h₁]⟩
      rcases le_total |z.val.1| |z.val.2| with hle | hle
      · rw [max_eq_right hle] at hn
        by_cases hp : 0≤z.val.2
        · rw [abs_of_nonneg hp] at hn
          refine ⟨2,tx,?_⟩
          apply Subtype.ext
          apply Prod.ext
          · change 2*((z.val.1+1)/2)-1=z.val.1
            ring
          · change 1=z.val.2
            exact hn.symm
        · rw [abs_of_neg (lt_of_not_ge hp)] at hn
          refine ⟨0,tx,?_⟩
          apply Subtype.ext
          apply Prod.ext
          · change 2*((z.val.1+1)/2)-1=z.val.1
            ring
          · change -1=z.val.2
            linarith only [hn]
      · rw [max_eq_left hle] at hn
        by_cases hp : 0≤z.val.1
        · rw [abs_of_nonneg hp] at hn
          refine ⟨1,ty,?_⟩
          apply Subtype.ext
          apply Prod.ext
          · change 1=z.val.1
            exact hn.symm
          · change 2*((z.val.2+1)/2)-1=z.val.2
            ring
        · rw [abs_of_neg (lt_of_not_ge hp)] at hn
          refine ⟨3,ty,?_⟩
          apply Subtype.ext
          apply Prod.ext
          · change -1=z.val.1
            linarith only [hn]
          · change 2*((z.val.2+1)/2)-1=z.val.2
            ring
  have actualClosedNegativeSample (g : C(Interval,ℝ)) (x y mid t : Interval)
      (hmid : x < mid ∧ mid < y)
      (hno : ∀ s,x<s → s<y → g s≠0)
      (ht : t∈Set.Icc x y) (hneg : g t<0) : g mid<0 := by
    as_aux_lemma =>
      by_contra hn
      have hpos : 0<g mid :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hno mid hmid.1 hmid.2))
      let ng : C(Interval,ℝ) := ⟨fun s => -g s,g.continuous.neg⟩
      have hngno (s : Interval) (hs0 : x<s) (hs1 : s<y) : ng s≠0 := neg_ne_zero.mpr (hno s hs0 hs1)
      have hh := actualNoZeroIntervalSign ng x y mid hmid.1 hmid.2 (neg_neg_of_pos hpos)
        hngno t ht
      change -g t≤0 at hh
      exact (not_lt_of_ge (neg_nonpos.mp hh)) hneg
  have actualIntervalSegmentSurjectiveOnBounds (x y t : Interval)
      (ht : t∈Set.Icc x y) : ∃ w : Interval,actualIntervalSegment x y w=t := by
    as_aux_lemma =>
      have h0 : actualIntervalSegment x y 0=x := by
        apply Subtype.ext
        change (1-(0 : ℝ))*x.val+(0 : ℝ)*y.val=x.val
        ring
      have h1 : actualIntervalSegment x y 1=y := by
        apply Subtype.ext
        change (1-(1 : ℝ))*x.val+(1 : ℝ)*y.val=y.val
        ring
      have ht' : t∈Set.Icc (actualIntervalSegment x y 0) (actualIntervalSegment x y 1) := by
        rwa [h0,h1]
      obtain ⟨w,hw,he⟩ := intermediate_value_Icc (show (0 : Interval)≤1 by norm_num)
        (actualIntervalSegment x y).continuous.continuousOn ht'
      exact ⟨w,he⟩
  have actualIntervalSegmentInterior (x y t : Interval) (hxy : x<y)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      x<actualIntervalSegment x y t ∧ actualIntervalSegment x y t<y := by
    as_aux_lemma =>
      have hxyR : x.val<y.val := hxy
      have ht0 : 0<t.val := ht.1
      have ht1 : t.val<1 := ht.2
      change x.val<(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val<y.val
      constructor <;> nlinarith only [hxyR,ht0,ht1]
  have actualSquareStrictInterior (u : {z : ℝ × ℝ // ‖z‖≤1}) (hu : ‖u.val‖<1) :
      (squareCoordinates u).1∈Set.Ioo (0 : Interval) 1 ∧
        (squareCoordinates u).2∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      have hx : |u.val.1|<1 := lt_of_le_of_lt (by
        change |u.val.1| ≤ max |u.val.1| |u.val.2|
        exact le_max_left _ _) hu
      have hy : |u.val.2|<1 := lt_of_le_of_lt (by
        change |u.val.2| ≤ max |u.val.1| |u.val.2|
        exact le_max_right _ _) hu
      obtain ⟨hx0,hx1⟩ := abs_lt.mp hx
      obtain ⟨hy0,hy1⟩ := abs_lt.mp hy
      constructor
      · constructor
        · change (0 : ℝ)<(u.val.1+1)/2
          linarith only [hx0]
        · change (u.val.1+1)/2<(1 : ℝ)
          linarith only [hx1]
      · constructor
        · change (0 : ℝ)<(u.val.2+1)/2
          linarith only [hy0]
        · change (u.val.2+1)/2<(1 : ℝ)
          linarith only [hy1]
  have actualNegativeRadialPointInterior (z : {z : ℝ × ℝ // ‖z‖=1}) (h : ℝ)
      (hh : h<0) (u : {z : ℝ × ℝ // ‖z‖≤1})
      (hu : u.val=(1/(1-h)) • z.val) :
      (squareCoordinates u).1∈Set.Ioo (0 : Interval) 1 ∧
        (squareCoordinates u).2∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      apply actualSquareStrictInterior u
      have hd : 0<1-h := by linarith only [hh]
      have hr : 0<1/(1-h) := one_div_pos.mpr hd
      rw [hu,norm_smul,Real.norm_eq_abs,abs_of_pos hr,z.property,mul_one]
      exact (div_lt_one hd).mpr (by linarith only [hh])
  have actualBoundaryFaceInteriorUnique (i j : Fin 4) (t u : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) (hu : u∈Set.Ioo (0 : Interval) 1)
      (he : actualBoundaryFace i t=actualBoundaryFace j u) : i=j := by
    as_aux_lemma =>
      have hf := congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} => z.val.1) he
      have hs := congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} => z.val.2) he
      have ht0 : 0<t.val := ht.1
      have ht1 : t.val<1 := ht.2
      have hu0 : 0<u.val := hu.1
      have hu1 : u.val<1 := hu.2
      fin_cases i <;> fin_cases j
      all_goals first | rfl |
        (simp [actualBoundaryFace,actualBoundaryFaceRaw] at hf hs; exfalso; linarith)
  have actualBoundaryFaceOpenUnique (i j : Fin 4) (t u : Interval)
      (ht : t ∈ Set.Ioo (0 : Interval) 1)
      (he : actualBoundaryFace i t = actualBoundaryFace j u) : i = j := by
    as_aux_lemma =>
      have hf := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val.1) he
      have hs := congrArg (fun z : {z : ℝ × ℝ // ‖z‖ = 1} => z.val.2) he
      have ht0 : 0 < t.val := ht.1
      have ht1 : t.val < 1 := ht.2
      fin_cases i <;> fin_cases j
      all_goals first | rfl |
        (simp [actualBoundaryFace,actualBoundaryFaceRaw] at hf hs; exfalso;
          first | exact (ne_of_gt ht.1) hf | exact (ne_of_gt ht.1) hs |
            exact (ne_of_lt ht.2) hf | exact (ne_of_lt ht.2) hs | linarith)
  have actualOrderedMeshNoNodesInside (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (j : Fin (m+1)) (k : Fin (m+2)) :
      ¬(mesh j.castSucc < mesh k ∧ mesh k < mesh j.succ) := by
    as_aux_lemma =>
      rintro ⟨hleft,hright⟩
      have hk0 := hmono.lt_iff_lt.mp hleft
      have hk1 := hmono.lt_iff_lt.mp hright
      change j.val < k.val at hk0
      change k.val < j.val+1 at hk1
      omega
  let actualPairSchoenflies : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let actualParameterSquarePlane : C(Interval × Interval,Schoenflies.Plane) :=
    ⟨fun z => actualPairSchoenflies (z.1.val,z.2.val),by fun_prop⟩
  have hActualParameterSquarePlaneInjective : Function.Injective actualParameterSquarePlane := by
    as_aux_lemma =>
      intro z w he
      have hh := actualPairSchoenflies.injective he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  have hActualParameterSquarePlaneEmbedding : IsEmbedding actualParameterSquarePlane :=
    (actualParameterSquarePlane.continuous.isClosedEmbedding hActualParameterSquarePlaneInjective).isEmbedding
  have actualInteriorZeroMeshNeighbors (g : C(Interval,ℝ)) (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (h0 : mesh 0=0) (h1 : mesh (Fin.last (m+1))=1)
      (hno : ∀ (j : Fin (m+1)) (t : Interval),mesh j.castSucc<t → t< mesh j.succ → g t≠0)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1) (hz : g u=0) :
      ∃ l r : Fin (m+1),mesh l.succ=u ∧ mesh r.castSucc=u ∧
        mesh l.castSucc<u ∧ u< mesh r.succ := by
    as_aux_lemma =>
      obtain ⟨q,hq⟩ := actualZeroIsMeshNode g m mesh hmono h0 h1 hno u hz
      have hqpos : 0<q.val := by
        by_contra hn
        have hq0 : q=0 := Fin.ext (by change q.val=0;omega)
        have he : u=0 := hq.symm.trans (by simpa only [hq0] using h0)
        exact (ne_of_gt hu.1) he
      have hqlast : q.val< m+1 := by
        by_contra hn
        have hlast : q=Fin.last (m+1) := Fin.ext (by change q.val=m+1;omega)
        have he : u=1 := hq.symm.trans (by simpa only [hlast] using h1)
        exact (ne_of_lt hu.2) he
      let l : Fin (m+1) := ⟨q.val-1,by omega⟩
      let r : Fin (m+1) := ⟨q.val,hqlast⟩
      have hlq : l.succ=q := Fin.ext (by dsimp [l];omega)
      have hrq : r.castSucc=q := rfl
      have hlu : mesh l.succ=u := by simpa only [hlq] using hq
      have hru : mesh r.castSucc=u := by simpa only [hrq] using hq
      refine ⟨l,r,hlu,hru,?_,?_⟩
      · rw [←hlu]
        exact hmono (by change l.val<l.val+1;omega)
      · rw [←hru]
        exact hmono (by change r.val<r.val+1;omega)
  have actualMeshIncidentIntervalUnique (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (l r : Fin (m+1)) (u : Interval)
      (hlu : mesh l.succ=u) (hru : mesh r.castSucc=u) (j : Fin (m+1))
      (hj : mesh j.castSucc=u ∨ mesh j.succ=u) : j=l ∨ j=r := by
    as_aux_lemma =>
      rcases hj with hj | hj
      · right
        have he := hmono.injective (hj.trans hru.symm)
        apply Fin.ext
        exact congrArg (fun z : Fin (m+2) => z.val) he
      · left
        have he := congrArg Fin.val (hmono.injective (hj.trans hlu.symm))
        apply Fin.ext
        change j.val+1=l.val+1 at he
        omega
  have actualMeshNegativeIncidenceUnique (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (negative : Fin (m+1) → Prop) (l r : Fin (m+1))
      (u : Interval) (hlu : mesh l.succ=u) (hru : mesh r.castSucc=u)
      (hflip : negative l ↔ ¬negative r) :
      ∃! j : Fin (m+1),negative j ∧ (mesh j.castSucc=u ∨ mesh j.succ=u) := by
    as_aux_lemma =>
      by_cases hl : negative l
      · refine ⟨l,⟨hl,Or.inr hlu⟩,?_⟩
        intro j hj
        rcases actualMeshIncidentIntervalUnique m mesh hmono l r u hlu hru j hj.2 with he | he
        · exact he
        · have hr : ¬negative r := hflip.mp hl
          exact False.elim (hr (he ▸ hj.1))
      · have hr : negative r := by
          by_contra hn
          exact hl (hflip.mpr hn)
        refine ⟨r,⟨hr,Or.inl hru⟩,?_⟩
        intro j hj
        rcases actualMeshIncidentIntervalUnique m mesh hmono l r u hlu hru j hj.2 with he | he
        · exact False.elim (hl (he ▸ hj.1))
        · exact he
  have actualIntervalSegmentInteriorReflect (x y t : Interval)
      (hlo : x<actualIntervalSegment x y t) (hhi : actualIntervalSegment x y t<y) :
      t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      have ht0 : t≠0 := by
        intro he
        subst t
        change x.val<(1-(0 : ℝ))*x.val+0*y.val at hlo
        nlinarith only [hlo]
      have ht1 : t≠1 := by
        intro he
        subst t
        change (1-(1 : ℝ))*x.val+1*y.val<y.val at hhi
        nlinarith only [hhi]
      exact ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
  have htailAvoidance (c : Interval) (hc : c=0 ∨ c=1)
      (hcOff : b.val.map c ∉ a.val.image) :
      ∃ V : Set Interval, IsOpen V ∧ c ∈ V ∧
        ∀ τ t : Interval, t ∈ V → F (τ,t) ∉ a.val.image := by
    as_aux_lemma =>
      let N : Set (Interval × Interval) := F ⁻¹' a.val.imageᶜ
      have hN : IsOpen N := (isCompact_range a.val.continuous).isClosed.isOpen_compl.preimage
        F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {c} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have htEq : t = c := mem_singleton_iff.mp ht
        subst t
        change F (τ,c) ∉ a.val.image
        rcases hc with rfl | rfl
        · simpa only [(hFends τ).1] using hcOff
        · simpa only [(hFends τ).2] using hcOff
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      exact ⟨V,hV,hVc (mem_singleton c),fun τ t ht => hUV ⟨hUall (mem_univ τ),ht⟩⟩
  have htailMargin (c : Interval) (hc : c=0 ∨ c=1) :
      ∃ δ : ℝ, 0 < δ ∧ (b.val.map c ∉ a.val.image →
        ∀ τ t : Interval, dist t c < δ → F (τ,t) ∉ a.val.image) := by
    as_aux_lemma =>
      by_cases hcOff : b.val.map c ∉ a.val.image
      · obtain ⟨V,hV,hcV,havoid⟩ := htailAvoidance c hc hcOff
        obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcV)
        exact ⟨δ,hδ,fun _ τ t ht => havoid τ t (hball ht)⟩
      · exact ⟨1,by norm_num,fun h => False.elim (hcOff h)⟩
  obtain ⟨δ₀,hδ₀,htail₀⟩ := htailMargin 0 (Or.inl rfl)
  obtain ⟨δ₁,hδ₁,htail₁⟩ := htailMargin 1 (Or.inr rfl)
  have hactualOldArcOrientation : ∃ e : Interval ≃ₜ Interval,
      (e=Homeomorph.refl _ ∨ e=unitInterval.symmHomeomorph) ∧
      ∀ c : Interval,c=0 ∨ c=1 → b.val.map c ∈ a.val.image → b.val.map c=a.val.map (e 0) := by
    as_aux_lemma =>
      classical
      have hane : a.val.map 0≠a.val.map 1 :=
        CurveComplex.HyperellipticModel.actualRepresentative_nonloop M a hadj.2.1
      have hends := hadj.2.2.2.1
      change ({a.val.map 0,a.val.map 1}:Finset S)≠{b.val.map 0,b.val.map 1} at hends
      have hnoBoth : ¬((a.val.map 0=b.val.map 0 ∨ a.val.map 0=b.val.map 1) ∧
          (a.val.map 1=b.val.map 0 ∨ a.val.map 1=b.val.map 1)) := by
        rintro ⟨h₀,h₁⟩
        rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
        · exact hane (h₀.trans h₁.symm)
        · exact hends (by rw [h₀,h₁])
        · exact hends (by rw [h₀,h₁,Finset.pair_comm])
        · exact hane (h₀.trans h₁.symm)
      by_cases hs : a.val.map 1=b.val.map 0 ∨ a.val.map 1=b.val.map 1
      · refine ⟨unitInterval.symmHomeomorph,Or.inr rfl,?_⟩
        intro c hc hx
        have hm : b.val.map c ∈ (M.cover.branch : Set S) := by
          rcases hc with rfl | rfl
          · exact b.val.start_marked
          · exact b.val.end_marked
        obtain ⟨t,ht⟩ := hx
        have hmt : a.val.map t ∈ (M.cover.branch : Set S) := ht.symm ▸ hm
        have he : unitInterval.symmHomeomorph (0 : Icc (0:ℝ) 1)=1 :=
          Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
        rw [he]
        rcases a.val.marked_only_at_ends t hmt with rfl | rfl
        · exfalso
          apply hnoBoth
          refine ⟨?_,hs⟩
          rcases hc with rfl | rfl
          · exact Or.inl ht
          · exact Or.inr ht
        · exact ht.symm
      · refine ⟨Homeomorph.refl _,Or.inl rfl,?_⟩
        intro c hc hx
        have hm : b.val.map c ∈ (M.cover.branch : Set S) := by
          rcases hc with rfl | rfl
          · exact b.val.start_marked
          · exact b.val.end_marked
        obtain ⟨t,ht⟩ := hx
        have hmt : a.val.map t ∈ (M.cover.branch : Set S) := ht.symm ▸ hm
        rcases a.val.marked_only_at_ends t hmt with rfl | rfl
        · exact ht.symm
        · exfalso
          apply hs
          rcases hc with rfl | rfl
          · exact Or.inl ht
          · exact Or.inr ht
  obtain ⟨oldParameterOrientation,hOldParameterOrientation,hOriginalAnySharedOldStart⟩ := hactualOldArcOrientation
  let af : C(Interval,S) := {
    toFun := fun t => a.val.map (oldParameterOrientation t)
    continuous_toFun := a.val.continuous.comp oldParameterOrientation.continuous }
  have haf : IsEmbedding af :=
    ((a.val.continuous.isClosedEmbedding (NonLoopArc.injective ⟨a.val,hane⟩)).isEmbedding).comp
      oldParameterOrientation.isEmbedding
  have hAFRange : range af=a.val.image := by
    as_aux_lemma =>
      ext x
      constructor
      · rintro ⟨t,ht⟩
        exact ⟨oldParameterOrientation t,ht⟩
      · rintro ⟨t,ht⟩
        refine ⟨oldParameterOrientation.symm t,?_⟩
        change a.val.map (oldParameterOrientation (oldParameterOrientation.symm t))=x
        rw [oldParameterOrientation.apply_symm_apply]
        exact ht
  have hAFEnds : (af 0=a.val.map 0 ∧ af 1=a.val.map 1) ∨
      (af 0=a.val.map 1 ∧ af 1=a.val.map 0) := by
    as_aux_lemma =>
      rcases hOldParameterOrientation with he | he
      · left
        constructor <;> simp [af,he]
      · right
        have hσ₀ : unitInterval.symm (0:Interval)=1 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
        have hσ₁ : unitInterval.symm (1:Interval)=0 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
        constructor
        · change a.val.map (oldParameterOrientation 0)=a.val.map 1
          rw [he]
          exact congrArg a.val.map hσ₀
        · change a.val.map (oldParameterOrientation 1)=a.val.map 0
          rw [he]
          exact congrArg a.val.map hσ₁
  have hAFStartMarked : af 0 ∈ (M.cover.branch : Set S) := by
    as_aux_lemma =>
      rcases hAFEnds with ⟨h₀,_⟩ | ⟨h₀,_⟩
      · rw [h₀]
        exact a.val.start_marked
      · rw [h₀]
        exact a.val.end_marked
  have hAFEndMarked : af 1 ∈ (M.cover.branch : Set S) := by
    as_aux_lemma =>
      rcases hAFEnds with ⟨_,h₁⟩ | ⟨_,h₁⟩
      · rw [h₁]
        exact a.val.end_marked
      · rw [h₁]
        exact a.val.start_marked
  have hAFEndset : ({a.val.map 0,a.val.map 1}:Set S)={af 0,af 1} := by
    as_aux_lemma =>
      rcases hAFEnds with ⟨h₀,h₁⟩ | ⟨h₀,h₁⟩
      · rw [h₀,h₁]
      · rw [h₀,h₁]
        exact Set.pair_comm _ _
  have hAnySharedOldStart (c : Interval) (hc : c=0 ∨ c=1) (hx : b.val.map c ∈ a.val.image) :
      b.val.map c=af 0 := hOriginalAnySharedOldStart c hc hx
  let stripCarrier : Set S := ((M.cover.branch : Set S) \ {a.val.map 0,a.val.map 1})ᶜ
  have hstripOpen : IsOpen stripCarrier :=
    (M.cover.branch.finite_toSet.subset Set.diff_subset).isClosed.isOpen_compl
  have hafCarrier : range af ⊆ stripCarrier := by
    intro x hx hbad
    obtain ⟨t,ht⟩ := hAFRange ▸ hx
    have hm : a.val.map t ∈ (M.cover.branch : Set S) := ht.symm ▸ hbad.1
    rcases a.val.marked_only_at_ends t hm with rfl | rfl
    · exact hbad.2 (ht ▸ (by simp))
    · exact hbad.2 (ht ▸ (by simp))
  obtain ⟨B,hB,hBcenter,hBcarrier⟩ :=
    CurveComplex.source_whole_embedded_arc_strip af haf stripCarrier hstripOpen hafCarrier
  have hBaxis (t : Interval) (y : Set.Icc (-1:ℝ) 1) :
      B (t,y) ∈ a.val.image ↔ (y:ℝ) = 0 := by
    as_aux_lemma =>
      constructor
      · intro hx
        obtain ⟨s,hs⟩ := hAFRange.symm ▸ hx
        have heq : B (t,y) = B (s,⟨0,by norm_num⟩) := hs.symm.trans (hBcenter s).symm
        exact congrArg (fun z : Interval × Set.Icc (-1:ℝ) 1 => (z.2:ℝ)) (hB.injective heq)
      · intro hy
        have hy0 : y = (⟨0,by norm_num⟩ : Set.Icc (-1:ℝ) 1) := Subtype.ext hy
        rw [hy0,hBcenter]
        exact hAFRange ▸ mem_range_self t
  have hBmarks (t : Interval) (y : Set.Icc (-1:ℝ) 1)
      (ht0 : t ≠ 0) (ht1 : t ≠ 1) : B (t,y) ∉ (M.cover.branch : Set S) := by
    as_aux_lemma =>
      intro hm
      have he : B (t,y) ∈ ({a.val.map 0,a.val.map 1} : Set S) := by
        by_contra hn
        exact hBcarrier (mem_range_self (t,y)) ⟨hm,hn⟩
      rw [hAFEndset] at he
      rcases he with he | he
      · have heq : B (t,y) = B (0,⟨0,by norm_num⟩) := he.trans (hBcenter 0).symm
        exact ht0 (congrArg Prod.fst (hB.injective heq))
      · have heq : B (t,y) = B (1,⟨0,by norm_num⟩) := he.trans (hBcenter 1).symm
        exact ht1 (congrArg Prod.fst (hB.injective heq))
  let bandProjection : Schoenflies.Plane → Interval × Set.Icc (-1:ℝ) 1 := fun z =>
    (Set.projIcc 0 1 zero_le_one (z 0),Set.projIcc (-1) 1 (by norm_num) (z 1))
  let bandMap : Schoenflies.Plane → S := B ∘ bandProjection
  let rectangle : Set Schoenflies.Plane :=
    {z | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1}
  have hrectangleOpen : IsOpen rectangle := by
    as_aux_lemma =>
      convert (isOpen_Ioo.preimage (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop)).inter
        (isOpen_Ioo.preimage (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop)) using 1
      ext z
      simp only [rectangle,mem_setOf_eq,mem_inter_iff,mem_preimage,mem_Ioo]
      tauto
  have hbandMapContinuous : Continuous bandMap := by
    exact hB.continuous.comp
      ((continuous_projIcc.comp (by fun_prop)).prodMk
        (continuous_projIcc.comp (by fun_prop)))
  have hbandProjection (z : Schoenflies.Plane) (hz : z ∈ rectangle) :
      ((bandProjection z).1:ℝ) = z 0 ∧ ((bandProjection z).2:ℝ) = z 1 := by
    as_aux_lemma =>
      exact ⟨by simp only [bandProjection,Set.projIcc_of_mem zero_le_one ⟨hz.1.le,hz.2.1.le⟩],
        by simp only [bandProjection,Set.projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
          ⟨hz.2.2.1.le,hz.2.2.2.le⟩]⟩
  have hbandMapInjective : Set.InjOn bandMap rectangle := by
    as_aux_lemma =>
      intro z hz w hw he
      have hp := hB.injective he
      have h0 := congrArg (fun t : Interval × Set.Icc (-1:ℝ) 1 => (t.1:ℝ)) hp
      have h1 := congrArg (fun t : Interval × Set.Icc (-1:ℝ) 1 => (t.2:ℝ)) hp
      rw [(hbandProjection z hz).1,(hbandProjection w hw).1] at h0
      rw [(hbandProjection z hz).2,(hbandProjection w hw).2] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
  let bandOpen : Set S := bandMap '' rectangle
  have hbandOpen : IsOpen bandOpen :=
    CurveComplex.surface_invariance_of_domain_probe bandMap rectangle hrectangleOpen
      hbandMapContinuous.continuousOn hbandMapInjective
  have hbandMarks : Disjoint bandOpen (M.cover.branch : Set S) := by
    as_aux_lemma =>
      apply Set.disjoint_left.mpr
      rintro _ ⟨z,hz,rfl⟩ hm
      have ht0 : (bandProjection z).1 ≠ 0 := by
        intro h
        have he := congrArg Subtype.val h
        rw [(hbandProjection z hz).1] at he
        exact (ne_of_gt hz.1) he
      have ht1 : (bandProjection z).1 ≠ 1 := by
        intro h
        have he := congrArg Subtype.val h
        rw [(hbandProjection z hz).1] at he
        exact (ne_of_lt hz.2.1) he
      exact hBmarks (bandProjection z).1 (bandProjection z).2 ht0 ht1 hm
  have haxisInBand : arcInterior M a ⊆ bandOpen := by
    as_aux_lemma =>
      rintro x ⟨hx,hnm⟩
      obtain ⟨t,ht⟩ := hAFRange.symm ▸ hx
      have ht0 : (0:ℝ) < t := by
        apply lt_of_le_of_ne t.property.1
        intro he
        have he0 : t = (0:Interval) := Subtype.ext he.symm
        subst t
        exact hnm (ht ▸ hAFStartMarked)
      have ht1 : (t:ℝ) < 1 := by
        apply lt_of_le_of_ne t.property.2
        intro he
        have he1 : t = (1:Interval) := Subtype.ext he
        subst t
        exact hnm (ht ▸ hAFEndMarked)
      let z : Schoenflies.Plane := Schoenflies.Plane.mk (t:ℝ) 0
      have hz : z ∈ rectangle := by simpa [rectangle,z,Schoenflies.Plane.mk] using ⟨ht0,ht1⟩
      refine ⟨z,hz,?_⟩
      have hp : bandProjection z = (t,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · apply Subtype.ext
          simpa [z,Schoenflies.Plane.mk] using (hbandProjection z hz).1
        · apply Subtype.ext
          simpa [z,Schoenflies.Plane.mk] using (hbandProjection z hz).2
      change B (bandProjection z) = x
      rw [hp,hBcenter]
      exact ht
  let transverse : C(Set.range B,ℝ) :=
    ⟨fun x => ((hB.toHomeomorph.symm x).2:ℝ),by fun_prop⟩
  let K : Set Interval := {t | b.val.map t ∈ ArcSurgery.crossings M a b}
  have hKfinite : K.Finite := hfinite.preimage (NonLoopArc.injective ⟨b.val,hbne⟩).injOn
  have hKnonempty : K.Nonempty := by
    as_aux_lemma =>
      obtain ⟨t,ht⟩ := hp.2.1
      refine ⟨t,?_⟩
      change b.val.map t ∈ ArcSurgery.crossings M a b
      rw [ht]
      exact hp
  obtain ⟨l,hl,hlmin⟩ := hKfinite.isCompact.exists_isLeast hKnonempty
  obtain ⟨u,hu,humax⟩ := hKfinite.isCompact.exists_isGreatest hKnonempty
  have hlpos : (0:ℝ) < (l:ℝ) := by
    as_aux_lemma =>
      apply lt_of_le_of_ne l.property.1
      intro h
      have he : l = (0:Interval) := Subtype.ext h.symm
      exact hl.2.2 (he ▸ b.val.start_marked)
  have hult : (u:ℝ) < (1:ℝ) := by
    as_aux_lemma =>
      apply lt_of_le_of_ne u.property.2
      intro h
      have he : u = (1:Interval) := Subtype.ext h
      exact hu.2.2 (he ▸ b.val.end_marked)
  let ε : ℝ := min (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)/2
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε < 1/2 := by
    as_aux_lemma =>
      have hle : (l:ℝ) ≤ u := hlmin hu
      have hm := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans
        (min_le_left (l:ℝ) (1-(u:ℝ)))
      dsimp [ε]; linarith
  have hεcross (t : Interval) (ht : t ∈ K) : ε < (t:ℝ) ∧ (t:ℝ) < 1-ε := by
    as_aux_lemma =>
      have hlo : (l:ℝ) ≤ t := hlmin ht
      have hhi : (t:ℝ) ≤ u := humax ht
      have hm₁ := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans
        (min_le_left (l:ℝ) (1-(u:ℝ)))
      have hm₂ := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans
        (min_le_right (l:ℝ) (1-(u:ℝ)))
      dsimp [ε]
      constructor <;> linarith
  have hεδ₀ : ε < δ₀ := by
    as_aux_lemma =>
      have hm := (min_le_right (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
      dsimp [ε]; linarith
  have hεδ₁ : ε < δ₁ := by
    as_aux_lemma =>
      have hm := (min_le_right (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
      dsimp [ε]; linarith
  have hleftTail (hoff : b.val.map 0 ∉ a.val.image) (τ t : Interval)
      (ht : (t:ℝ) ≤ ε) : F (τ,t) ∉ a.val.image := by
    as_aux_lemma =>
      apply htail₀ hoff τ t
      rw [Subtype.dist_eq,Real.dist_eq]
      change |(t:ℝ)-0| < δ₀
      simpa only [sub_zero,abs_of_nonneg t.property.1] using ht.trans_lt hεδ₀
  have hrightTail (hoff : b.val.map 1 ∉ a.val.image) (τ t : Interval)
      (ht : 1-ε ≤ (t:ℝ)) : F (τ,t) ∉ a.val.image := by
    as_aux_lemma =>
      apply htail₁ hoff τ t
      rw [Subtype.dist_eq,Real.dist_eq]
      change |(t:ℝ)-1| < δ₁
      rw [abs_of_nonpos (by linarith [t.property.2])]
      linarith
  let centralParam : Interval → Interval := fun t =>
    ⟨ε+(1-2*ε)*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩
  have hcentralPos (t : Interval) : (0:ℝ) < (centralParam t:ℝ) := by
    as_aux_lemma =>
      dsimp [centralParam]; nlinarith [t.property.1,t.property.2]
  have hcentralLt (t : Interval) : (centralParam t:ℝ) < (1:ℝ) := by
    as_aux_lemma =>
      dsimp [centralParam]; nlinarith [t.property.1,t.property.2]
  have hcrossCaptured (t : Interval) (ht : t ∈ K) :
      ∃ s : Interval, centralParam s = t := by
    as_aux_lemma =>
      obtain ⟨hlo,hhi⟩ := hεcross t ht
      have hden : 0 < 1-2*ε := by linarith
      let s : Interval := ⟨((t:ℝ)-ε)/(1-2*ε),by
        constructor
        · exact div_nonneg (by linarith) hden.le
        · apply (div_le_one hden).mpr
          linarith⟩
      refine ⟨s,Subtype.ext ?_⟩
      change ε+(1-2*ε)*(((t:ℝ)-ε)/(1-2*ε)) = (t:ℝ)
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hden.ne']
      ring
  let G : C(Interval × Interval,S) :=
    ⟨fun z => F (z.1,centralParam z.2),by fun_prop⟩
  have hGmarks (z : Interval × Interval) : G z ∉ (M.cover.branch : Set S) :=
    hFmarks z.1 (centralParam z.2)
      (ne_of_gt (hcentralPos z.2)) (ne_of_lt (hcentralLt z.2))
  have htransverseAxis (x : Set.range B) : transverse x = 0 ↔ x.val ∈ a.val.image := by
    as_aux_lemma =>
      let z := hB.toHomeomorph.symm x
      have hz : B z = x.val := congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply x)
      have haxis := hBaxis z.1 z.2
      change B z ∈ a.val.image ↔ (z.2:ℝ) = 0 at haxis
      rw [hz] at haxis
      exact haxis.symm
  have hbandSubset : bandOpen ⊆ Set.range B := by
    as_aux_lemma =>
      rintro _ ⟨z,hz,rfl⟩
      exact mem_range_self (bandProjection z)
  let T : Set (Interval × Interval) := G ⁻¹' bandOpen
  have hTopen : IsOpen T := hbandOpen.preimage G.continuous
  have hGzerosInT : G ⁻¹' a.val.image ⊆ T := by
    intro z hz
    exact haxisInBand ⟨hz,hGmarks z⟩
  let liftG : C(T,Set.range B) :=
    ⟨fun z => ⟨G z.val,hbandSubset z.property⟩,by fun_prop⟩
  let ψ : C(T,ℝ) := transverse.comp liftG
  have hcoordinatesInterior (z : T) :
      0 < ((hB.toHomeomorph.symm (liftG z)).1:ℝ) ∧
      ((hB.toHomeomorph.symm (liftG z)).1:ℝ) < 1 ∧ -1 < ψ z ∧ ψ z < 1 := by
    as_aux_lemma =>
      obtain ⟨w,hw,hwG⟩ := z.property
      have he : B (hB.toHomeomorph.symm (liftG z)) = G z.val :=
        congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply (liftG z))
      have hcoord : hB.toHomeomorph.symm (liftG z) = bandProjection w :=
        hB.injective (he.trans hwG.symm)
      change 0 < ((hB.toHomeomorph.symm (liftG z)).1:ℝ) ∧
        ((hB.toHomeomorph.symm (liftG z)).1:ℝ) < 1 ∧
        -1 < ((hB.toHomeomorph.symm (liftG z)).2:ℝ) ∧
        ((hB.toHomeomorph.symm (liftG z)).2:ℝ) < 1
      rw [hcoord,(hbandProjection w hw).1,(hbandProjection w hw).2]
      exact hw
  have hψzero (z : T) : ψ z = 0 ↔ G z.val ∈ a.val.image :=
    htransverseAxis (liftG z)
  have hψtop (z : T) (hz : z.val.1 = 1) : ψ z ≠ 0 := by
    as_aux_lemma =>
      intro hzero
      have hhit := (hψzero z).mp hzero
      change F (z.val.1,centralParam z.val.2) ∈ a.val.image at hhit
      rw [hz] at hhit
      exact hFterminalFull (centralParam z.val.2)
        (ne_of_gt (hcentralPos z.val.2)) (ne_of_lt (hcentralLt z.val.2)) hhit
  have hGinitial (t : Interval) : G (0,t) = b.val.map (centralParam t) := hFzero _
  have hcrossZeroCaptured (t : Interval) (ht : t ∈ K) :
      ∃ s : Interval, ∃ hs : (0,s) ∈ T,
        G (0,s) = b.val.map t ∧ ψ ⟨(0,s),hs⟩ = 0 := by
    as_aux_lemma =>
      obtain ⟨s,hs⟩ := hcrossCaptured t ht
      have he : G (0,s) = b.val.map t := by rw [hGinitial,hs]
      have hhit : G (0,s) ∈ a.val.image := he.symm ▸ ht.1.1
      have hT : (0,s) ∈ T := hGzerosInT hhit
      exact ⟨s,hT,he,(hψzero ⟨(0,s),hT⟩).mpr hhit⟩
  let r : Fin 1 → EssentialMarkedArc M := fun _ => a
  have hrne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1 := fun _ => hane
  have hrdis : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)) := by
    as_aux_lemma =>
      intro i j hij
      exact False.elim (hij (Subsingleton.elim i j))
  have hcharts (z : Interval × Interval) :
      ∃ e : OpenPartialHomeomorph S Schoenflies.Plane,
        G z ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
        ∃ label : Option (Fin 1),
          (∀ x ∈ e.source, (x ∈ a.val.image ↔ label = some 0 ∧ e x 0 = 0)) ∧
          (label = some 0 → e.source ⊆ bandOpen) ∧
          (label = none → Disjoint e.source a.val.image) := by
    as_aux_lemma =>
      obtain ⟨e,hpoint,hmarks,label,hflat⟩ :=
        actual_disjoint_system_prepared_interior_cover M r hrne hrdis (G z) (hGmarks z)
      by_cases hhit : G z ∈ a.val.image
      · have hlabel : label = some 0 := ((hflat 0 (G z) hpoint).mp hhit).1
        let ec := e.restr bandOpen
        have hsource : ec.source = e.source ∩ bandOpen := by
          rw [OpenPartialHomeomorph.restr_source,hbandOpen.interior_eq]
        refine ⟨ec,hsource.symm ▸ ⟨hpoint,haxisInBand ⟨hhit,hGmarks z⟩⟩,
          hmarks.mono (fun x hx => (hsource.le hx).1) (Subset.refl _),some 0,?_,?_,?_⟩
        · intro x hx
          have hf := hflat 0 x (hsource.le hx).1
          change x ∈ a.val.image ↔ label = some 0 ∧ e x 0 = 0 at hf
          rw [hlabel] at hf
          simpa only [ec,OpenPartialHomeomorph.restr_apply] using hf
        · intro _ x hx
          exact (hsource.le hx).2
        · intro h
          cases h
      · let ec := e.restr a.val.imageᶜ
        have hoffOpen : IsOpen a.val.imageᶜ := (isCompact_range a.val.continuous).isClosed.isOpen_compl
        have hsource : ec.source = e.source ∩ a.val.imageᶜ := by
          rw [OpenPartialHomeomorph.restr_source,hoffOpen.interior_eq]
        refine ⟨ec,hsource.symm ▸ ⟨hpoint,hhit⟩,
          hmarks.mono (fun x hx => (hsource.le hx).1) (Subset.refl _),none,?_,?_,?_⟩
        · intro x hx
          constructor
          · intro ha
            exact False.elim ((hsource.le hx).2 ha)
          · rintro ⟨h,_⟩
            cases h
        · intro h
          cases h
        · intro _
          exact Set.disjoint_left.mpr (fun x hx ha => (hsource.le hx).2 ha)
  choose chart hpoint hchartmarks label hflat hchartBand hchartOff using hcharts
  let W : (Interval × Interval) → Set (Interval × Interval) :=
    fun z => G ⁻¹' (chart z).source
  have hWopen : ∀ z, IsOpen (W z) :=
    fun z => (chart z).open_source.preimage G.continuous
  have hWcover : (Set.univ : Set (Interval × Interval)) ⊆ ⋃ z, W z := by
    as_aux_lemma =>
      intro z _
      exact mem_iUnion.mpr ⟨z,hpoint z⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hWopen hWcover
  obtain ⟨n₀,hn₀,hmesh₀⟩ := Real.exists_nat_pos_inv_lt hδ
  let n : ℕ := n₀+3
  have hn : 0 < n := by dsimp [n]; omega
  have hnLarge : 3 < n := by dsimp [n]; omega
  have hmesh : (n:ℝ)⁻¹ < δ := by
    as_aux_lemma =>
      have hle : (n₀:ℝ) ≤ (n:ℝ) := by dsimp [n]; norm_num
      have hn₀R : (0:ℝ) < n₀ := by exact_mod_cast hn₀
      have h := one_div_le_one_div_of_le hn₀R hle
      rw [one_div,one_div] at h
      exact lt_of_le_of_lt h hmesh₀
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let lower : Fin n → Interval := fun k =>
    ⟨(k.val:ℝ)/n,by
      constructor
      · positivity
      · apply (div_le_one hnR).mpr
        exact_mod_cast k.isLt.le⟩
  choose index hindex using (fun k : Fin n × Fin n =>
    hball (lower k.1,lower k.2) (mem_univ _))
  have hcells : ∀ k : Fin n × Fin n, ∀ z : Interval × Interval,
      (k.1.val:ℝ)/n ≤ (z.1:ℝ) → (z.1:ℝ) ≤ (k.1.val+1:ℝ)/n →
      (k.2.val:ℝ)/n ≤ (z.2:ℝ) → (z.2:ℝ) ≤ (k.2.val+1:ℝ)/n →
      G z ∈ (chart (index k)).source := by
    intro k z hlow₁ hhigh₁ hlow₂ hhigh₂
    apply hindex k
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    have hdist : ∀ j : Fin n, ∀ t : Interval,
        (j.val:ℝ)/n ≤ (t:ℝ) → (t:ℝ) ≤ (j.val+1:ℝ)/n →
        dist t (lower j) < δ := by
      intro j t hlo hhi
      rw [Subtype.dist_eq,Real.dist_eq]
      change |(t:ℝ)-(j.val:ℝ)/n| < δ
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      have heq : (j.val+1:ℝ)/n = (j.val:ℝ)/n+(n:ℝ)⁻¹ := by
        rw [add_div,one_div]
      rw [heq] at hhi
      linarith
    exact ⟨hdist k.1 z.1 hlow₁ hhigh₁,hdist k.2 z.2 hlow₂ hhigh₂⟩
  have hcellBand (k : Fin n × Fin n) (hk : label (index k) = some 0)
      (z : Interval × Interval)
      (hlow₁ : (k.1.val:ℝ)/n ≤ (z.1:ℝ)) (hhigh₁ : (z.1:ℝ) ≤ (k.1.val+1:ℝ)/n)
      (hlow₂ : (k.2.val:ℝ)/n ≤ (z.2:ℝ)) (hhigh₂ : (z.2:ℝ) ≤ (k.2.val+1:ℝ)/n) :
      z ∈ T := hchartBand (index k) hk (hcells k z hlow₁ hhigh₁ hlow₂ hhigh₂)
  have hcellOff (k : Fin n × Fin n) (hk : label (index k) = none)
      (z : Interval × Interval)
      (hlow₁ : (k.1.val:ℝ)/n ≤ (z.1:ℝ)) (hhigh₁ : (z.1:ℝ) ≤ (k.1.val+1:ℝ)/n)
      (hlow₂ : (k.2.val:ℝ)/n ≤ (z.2:ℝ)) (hhigh₂ : (z.2:ℝ) ≤ (k.2.val+1:ℝ)/n) :
      G z ∉ a.val.image :=
    Set.disjoint_left.mp (hchartOff (index k) hk) (hcells k z hlow₁ hhigh₁ hlow₂ hhigh₂)
  let cellMap (k : Fin n × Fin n) : C(Interval × Interval,Interval × Interval) :=
    ⟨fun z => (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),
      (ArcFinitePosition.intervalMeshParameter_continuous n hn k.1 |>.comp continuous_fst).prodMk
      (ArcFinitePosition.intervalMeshParameter_continuous n hn k.2 |>.comp continuous_snd)⟩
  let cell (k : Fin n × Fin n) : Set (Interval × Interval) := range (cellMap k)
  have hcellClosed (k : Fin n × Fin n) : IsClosed (cell k) :=
    (isCompact_range (cellMap k).continuous).isClosed
  have hmeshBound (j : Fin n) (t : Interval) :
      (j.val:ℝ)/n ≤ (ArcFinitePosition.intervalMeshParameter n hn j t:ℝ) ∧
      (ArcFinitePosition.intervalMeshParameter n hn j t:ℝ) ≤ (j.val+1:ℝ)/n := by
    as_aux_lemma =>
      change (j.val:ℝ)/n ≤ ((j.val:ℝ)+(t:ℝ))/n ∧
        ((j.val:ℝ)+(t:ℝ))/n ≤ (j.val+1:ℝ)/n
      constructor
      · exact div_le_div_of_nonneg_right (by linarith [t.property.1]) hnR.le
      · exact div_le_div_of_nonneg_right (by linarith [t.property.2]) hnR.le
  have hcellSource (k : Fin n × Fin n) (z : Interval × Interval) (hz : z ∈ cell k) :
      G z ∈ (chart (index k)).source := by
    as_aux_lemma =>
      obtain ⟨s,rfl⟩ := hz
      exact hcells k (cellMap k s) (hmeshBound k.1 s.1).1 (hmeshBound k.1 s.1).2
        (hmeshBound k.2 s.2).1 (hmeshBound k.2 s.2).2
  have hcellCover (z : Interval × Interval) : ∃ k, z ∈ cell k := by
    as_aux_lemma =>
      obtain ⟨i,s,hs⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
      obtain ⟨j,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
      exact ⟨(i,j),(s,t),Prod.ext hs ht⟩
  let support : Set (Interval × Interval) :=
    ⋃ k : Fin n × Fin n, if label (index k)=some 0 then cell k else ∅
  let offCells : Set (Interval × Interval) :=
    ⋃ k : Fin n × Fin n, if label (index k)=none then cell k else ∅
  have hsupportClosed : IsClosed support := by
    apply isClosed_iUnion_of_finite
    intro k
    by_cases hk : label (index k)=some 0
    · simpa only [if_pos hk] using hcellClosed k
    · simp only [if_neg hk]; exact isClosed_empty
  have hoffClosed : IsClosed offCells := by
    apply isClosed_iUnion_of_finite
    intro k
    by_cases hk : label (index k)=none
    · simpa only [if_pos hk] using hcellClosed k
    · simp only [if_neg hk]; exact isClosed_empty
  have hsupportInT : support ⊆ T := by
    as_aux_lemma =>
      intro z hz
      obtain ⟨k,hkz⟩ := mem_iUnion.mp hz
      by_cases hk : label (index k)=some 0
      · have hzc : z ∈ cell k := by simpa only [if_pos hk] using hkz
        exact hchartBand (index k) hk (hcellSource k z hzc)
      · simp only [if_neg hk,mem_empty_iff_false] at hkz
  have hoffAvoids : ∀ z ∈ offCells, G z ∉ a.val.image := by
    as_aux_lemma =>
      intro z hz
      obtain ⟨k,hkz⟩ := mem_iUnion.mp hz
      by_cases hk : label (index k)=none
      · have hzc : z ∈ cell k := by simpa only [if_pos hk] using hkz
        exact Set.disjoint_left.mp (hchartOff (index k) hk) (hcellSource k z hzc)
      · simp only [if_neg hk,mem_empty_iff_false] at hkz
  have houtsideOffInSupport : offCellsᶜ ⊆ support := by
    as_aux_lemma =>
      intro z hz
      obtain ⟨k,hkz⟩ := hcellCover z
      have hnotnone : label (index k) ≠ none := by
        intro hk
        exact hz (mem_iUnion.mpr ⟨k,by simpa only [if_pos hk] using hkz⟩)
      have hk : label (index k) = some 0 := by
        cases he : label (index k) with
        | none => exact False.elim (hnotnone he)
        | some j => simpa only [Subsingleton.elim j (0:Fin 1)] using he
      exact mem_iUnion.mpr ⟨k,by simpa only [if_pos hk] using hkz⟩
  let Z : Set (Interval × Interval) := G ⁻¹' a.val.image
  have hZclosed : IsClosed Z := (isCompact_range a.val.continuous).isClosed.preimage G.continuous
  have hZinterior : Z ⊆ interior support := by
    as_aux_lemma =>
      have hZoff : Z ⊆ offCellsᶜ := fun z hz hzo => hoffAvoids z hzo hz
      exact hZoff.trans (hoffClosed.isOpen_compl.subset_interior_iff.mpr houtsideOffInSupport)
  have hsep : Disjoint (interior support)ᶜ Z := by
    as_aux_lemma =>
      exact Set.disjoint_left.mpr (fun z hz hzZ => hz (hZinterior hzZ))
  obtain ⟨cutoff,hcutoffOutside,hcutoffZeros,hcutoffRange⟩ :=
    exists_continuous_zero_one_of_isClosed isOpen_interior.isClosed_compl hZclosed hsep
  let weights (z : Interval × Interval) : Fin 4 → ℝ :=
    ![max (1-(z.1:ℝ)-(z.2:ℝ)) 0, min (z.1:ℝ) (1-(z.2:ℝ)),
      min (z.2:ℝ) (1-(z.1:ℝ)), max ((z.1:ℝ)+(z.2:ℝ)-1) 0]
  have hweightsNonneg (z : Interval × Interval) (i : Fin 4) : 0 ≤ weights z i := by
    as_aux_lemma =>
      fin_cases i
      · exact le_max_right _ _
      · exact le_min z.1.property.1 (by linarith [z.2.property.2])
      · exact le_min z.2.property.1 (by linarith [z.1.property.2])
      · exact le_max_right _ _
  have hweightsSum (z : Interval × Interval) : ∑ i : Fin 4, weights z i = 1 := by
    as_aux_lemma =>
      by_cases h : (z.1:ℝ)+(z.2:ℝ) ≤ 1
      · have h₀ : 0 ≤ 1-(z.1:ℝ)-(z.2:ℝ) := by linarith
        have h₁ : (z.1:ℝ) ≤ 1-(z.2:ℝ) := by linarith
        have h₂ : (z.2:ℝ) ≤ 1-(z.1:ℝ) := by linarith
        have h₃ : (z.1:ℝ)+(z.2:ℝ)-1 ≤ 0 := by linarith
        rw [Fin.sum_univ_four]
        change max (1-(z.1:ℝ)-(z.2:ℝ)) 0 + min (z.1:ℝ) (1-(z.2:ℝ)) +
          min (z.2:ℝ) (1-(z.1:ℝ)) + max ((z.1:ℝ)+(z.2:ℝ)-1) 0 = 1
        rw [max_eq_left h₀,min_eq_left h₁,min_eq_left h₂,max_eq_right h₃]
        ring
      · have h₀ : 1-(z.1:ℝ)-(z.2:ℝ) ≤ 0 := by linarith
        have h₁ : 1-(z.2:ℝ) ≤ (z.1:ℝ) := by linarith
        have h₂ : 1-(z.1:ℝ) ≤ (z.2:ℝ) := by linarith
        have h₃ : 0 ≤ (z.1:ℝ)+(z.2:ℝ)-1 := by linarith
        rw [Fin.sum_univ_four]
        change max (1-(z.1:ℝ)-(z.2:ℝ)) 0 + min (z.1:ℝ) (1-(z.2:ℝ)) +
          min (z.2:ℝ) (1-(z.1:ℝ)) + max ((z.1:ℝ)+(z.2:ℝ)-1) 0 = 1
        rw [max_eq_right h₀,min_eq_right h₁,min_eq_right h₂,max_eq_left h₃]
        ring
  let corners : Fin 4 → Interval × Interval := ![(0,0),(1,0),(0,1),(1,1)]
  have hweightsEdges (t : Interval) :
      weights (0,t) = ![1-t.val,0,t.val,0] ∧
      weights (1,t) = ![0,1-t.val,0,t.val] ∧
      weights (t,0) = ![1-t.val,t.val,0,0] ∧
      weights (t,1) = ![0,0,1-t.val,t.val] := by
    as_aux_lemma =>
      have hpos : 0 ≤ 1-t.val := by linarith [t.property.2]
      have hneg : t.val-1 ≤ 0 := by linarith [t.property.2]
      have ht := t.property.1
      have ht1 := t.property.2
      refine ⟨?_,?_,?_,?_⟩ <;> ext j <;> fin_cases j <;>
        norm_num [weights,max_eq_left hpos,max_eq_right hneg,
          max_eq_right (neg_nonpos.mpr ht),min_eq_left ht1,min_eq_right ht,
          min_eq_left ht,min_eq_left hpos,min_eq_right hpos,max_eq_left ht]
      all_goals exact ht
  have hweightsEdgeSums (t : Interval) (v : Fin 4 → ℝ) :
      (∑ i, weights (0,t) i * v i) = (1-t.val)*v 0 + t.val*v 2 ∧
      (∑ i, weights (1,t) i * v i) = (1-t.val)*v 1 + t.val*v 3 ∧
      (∑ i, weights (t,0) i * v i) = (1-t.val)*v 0 + t.val*v 1 ∧
      (∑ i, weights (t,1) i * v i) = (1-t.val)*v 2 + t.val*v 3 := by
    as_aux_lemma =>
      obtain ⟨hl,hr,hb,ht⟩ := hweightsEdges t
      rw [hl,hr,hb,ht]
      simp [Fin.sum_univ_four]
  have hweightsCorners (i j : Fin 4) : weights (corners i) j = if j=i then 1 else 0 := by
    as_aux_lemma =>
      fin_cases i <;> fin_cases j <;> norm_num [weights,corners]
  let sourceCoords (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) : Interval × Set.Icc (-1:ℝ) 1 :=
    hB.toHomeomorph.symm (liftG ⟨cellMap k z,
      hchartBand (index k) hk (hcellSource k _ (mem_range_self _))⟩)
  have hlocalPLRedrawing (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      ∃ P : C(Interval × Interval,S),
        (∀ z, P z ∉ (M.cover.branch : Set S)) ∧
        ∃ Q : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
          (∀ z, P z = B (Q z)) ∧
          (∀ z, (Q z).1.val = ∑ i : Fin 4, weights z i *
            ((hB.toHomeomorph.symm (liftG ⟨cellMap k (corners i),
              hchartBand (index k) hk (hcellSource k _ (mem_range_self _))⟩)).1:ℝ)) ∧
          (∀ z, (Q z).2.val = ∑ i : Fin 4, weights z i *
            ((hB.toHomeomorph.symm (liftG ⟨cellMap k (corners i),
              hchartBand (index k) hk (hcellSource k _ (mem_range_self _))⟩)).2:ℝ)) ∧
          (∀ i, P (corners i) = G (cellMap k (corners i))) ∧
          ∃ H : C(Interval × (Interval × Interval),S),
            (∀ z, H z ∉ (M.cover.branch : Set S)) ∧
            (∀ z, H (0,z) = G (cellMap k z)) ∧
            (∀ z, H (1,z) = P z) ∧
            (∀ τ i, H (τ,corners i) = G (cellMap k (corners i))) ∧
            ∃ J : C(Interval × (Interval × Interval),Interval × Set.Icc (-1:ℝ) 1),
              (∀ z, H z = B (J z)) ∧
              (∀ z, (J z).1.val = (1-z.1.val)*(sourceCoords k hk z.2).1.val +
                z.1.val*(Q z.2).1.val) ∧
              (∀ z, (J z).2.val = (1-z.1.val)*(sourceCoords k hk z.2).2.val +
                z.1.val*(Q z.2).2.val) := by
    as_aux_lemma =>
      let V (i : Fin 4) : Interval × Set.Icc (-1:ℝ) 1 :=
        hB.toHomeomorph.symm (liftG ⟨cellMap k (corners i),
          hchartBand (index k) hk (hcellSource k _ (mem_range_self _))⟩)
      have hVlong (i : Fin 4) : (V i).1.val ∈ Ioo (0:ℝ) 1 :=
        ⟨(hcoordinatesInterior _).1,(hcoordinatesInterior _).2.1⟩
      have hVwidth (i : Fin 4) : (V i).2.val ∈ Ioo (-1:ℝ) 1 :=
        ⟨(hcoordinatesInterior _).2.2.1,(hcoordinatesInterior _).2.2.2⟩
      have hlong (z : Interval × Interval) :
          (∑ i : Fin 4, weights z i * (V i).1.val) ∈ Ioo (0:ℝ) 1 := by
        simpa only [smul_eq_mul] using
          (convex_Ioo (𝕜:=ℝ) (0:ℝ) 1).sum_mem (fun i _ => hweightsNonneg z i)
            (hweightsSum z) (fun i _ => hVlong i)
      have hwidth (z : Interval × Interval) :
          (∑ i : Fin 4, weights z i * (V i).2.val) ∈ Ioo (-1:ℝ) 1 := by
        simpa only [smul_eq_mul] using
          (convex_Ioo (𝕜:=ℝ) (-1:ℝ) 1).sum_mem (fun i _ => hweightsNonneg z i)
            (hweightsSum z) (fun i _ => hVwidth i)
      let Q : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z => (⟨∑ i : Fin 4, weights z i * (V i).1.val,
          (hlong z).1.le,(hlong z).2.le⟩,
          ⟨∑ i : Fin 4, weights z i * (V i).2.val,(hwidth z).1.le,(hwidth z).2.le⟩)
        continuous_toFun := by
          unfold weights
          fun_prop }
      have hQcorners (i : Fin 4) : Q (corners i) = V i := by
        apply Prod.ext <;> apply Subtype.ext
        · change (∑ j : Fin 4, weights (corners i) j * (V j).1.val) = (V i).1.val
          simp [hweightsCorners]
        · change (∑ j : Fin 4, weights (corners i) j * (V j).2.val) = (V i).2.val
          simp [hweightsCorners]
      let P : C(Interval × Interval,S) := ⟨B ∘ Q,hB.continuous.comp Q.continuous⟩
      have hPcorners (i : Fin 4) : P (corners i) = G (cellMap k (corners i)) := by
        change B (Q (corners i)) = _
        rw [hQcorners]
        exact congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
      let sourceCell : C(Interval × Interval,T) := {
        toFun := fun z => ⟨cellMap k z,
          hchartBand (index k) hk (hcellSource k _ (mem_range_self _))⟩
        continuous_toFun := (cellMap k).continuous.subtype_mk _ }
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        (⟨hB.toHomeomorph.symm,hB.toHomeomorph.symm.continuous⟩ :
          C(range B,Interval × Set.Icc (-1:ℝ) 1)).comp (liftG.comp sourceCell)
      have hRlong (z : Interval × Interval) : (R z).1.val ∈ Ioo (0:ℝ) 1 :=
        ⟨(hcoordinatesInterior _).1,(hcoordinatesInterior _).2.1⟩
      have hRwidth (z : Interval × Interval) : (R z).2.val ∈ Ioo (-1:ℝ) 1 :=
        ⟨(hcoordinatesInterior _).2.2.1,(hcoordinatesInterior _).2.2.2⟩
      have hmixlong (z : Interval × (Interval × Interval)) :
          (1-z.1.val)*(R z.2).1.val + z.1.val*(Q z.2).1.val ∈ Ioo (0:ℝ) 1 := by
        have h := (convex_Ioo (𝕜:=ℝ) (0:ℝ) 1).lineMap_mem
          (hRlong z.2) (hlong z.2) z.1.property
        change z.1.val * ((Q z.2).1.val - (R z.2).1.val) + (R z.2).1.val ∈ Ioo (0:ℝ) 1 at h
        convert h using 1 <;> ring
      have hmixwidth (z : Interval × (Interval × Interval)) :
          (1-z.1.val)*(R z.2).2.val + z.1.val*(Q z.2).2.val ∈ Ioo (-1:ℝ) 1 := by
        have h := (convex_Ioo (𝕜:=ℝ) (-1:ℝ) 1).lineMap_mem
          (hRwidth z.2) (hwidth z.2) z.1.property
        change z.1.val * ((Q z.2).2.val - (R z.2).2.val) + (R z.2).2.val ∈ Ioo (-1:ℝ) 1 at h
        convert h using 1 <;> ring
      let mix : C(Interval × (Interval × Interval),Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z =>
          (⟨(1-z.1.val)*(R z.2).1.val + z.1.val*(Q z.2).1.val,
            (hmixlong z).1.le,(hmixlong z).2.le⟩,
          ⟨(1-z.1.val)*(R z.2).2.val + z.1.val*(Q z.2).2.val,
            (hmixwidth z).1.le,(hmixwidth z).2.le⟩)
        continuous_toFun := by fun_prop }
      let H : C(Interval × (Interval × Interval),S) := ⟨B ∘ mix,hB.continuous.comp mix.continuous⟩
      have hHmarks (z : Interval × (Interval × Interval)) : H z ∉ (M.cover.branch : Set S) :=
        hBmarks (mix z).1 (mix z).2
          (ne_of_gt (hmixlong z).1) (ne_of_lt (hmixlong z).2)
      have hHinitial (z : Interval × Interval) : H (0,z) = G (cellMap k z) := by
        change B (mix (0,z)) = _
        have hm : mix (0,z) = R z := by ext <;> simp [mix]
        rw [hm]
        exact congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
      have hHcorners (τ : Interval) (i : Fin 4) :
          H (τ,corners i) = G (cellMap k (corners i)) := by
        have hRc : R (corners i) = V i := rfl
        change B (mix (τ,corners i)) = _
        have hm : mix (τ,corners i) = V i := by
          apply Prod.ext <;> apply Subtype.ext
          · change (1-τ.val)*(R (corners i)).1.val + τ.val*(Q (corners i)).1.val = (V i).1.val
            rw [hRc,hQcorners]
            ring
          · change (1-τ.val)*(R (corners i)).2.val + τ.val*(Q (corners i)).2.val = (V i).2.val
            rw [hRc,hQcorners]
            ring
        rw [hm]
        exact congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
      have hHfinal (z : Interval × Interval) : H (1,z) = P z := by
        change B (mix (1,z)) = B (Q z)
        congr 1
        ext <;> simp [mix]
      refine ⟨P,?_,Q,fun _ => rfl,fun _ => rfl,fun _ => rfl,
        hPcorners,H,hHmarks,hHinitial,hHfinal,hHcorners,mix,
        (fun _ => rfl),(fun _ => rfl),(fun _ => rfl)⟩
      intro z
      exact hBmarks (Q z).1 (Q z).2
        (ne_of_gt (hlong z).1) (ne_of_lt (hlong z).2)
  have hcellHorizontalNeighbor (k l : Fin n × Fin n)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (t : Interval) :
      cellMap k (1,t) = cellMap l (0,t) := by
    as_aux_lemma =>
      apply Prod.ext
      · apply Subtype.ext
        have hc : (l.1.val:ℝ) = (k.1.val:ℝ)+1 := by exact_mod_cast hl₁
        change ((k.1.val:ℝ)+(1:Interval).val)/(n:ℝ) =
          ((l.1.val:ℝ)+(0:Interval).val)/(n:ℝ)
        simp [hc]
      · change ArcFinitePosition.intervalMeshParameter n hn k.2 t =
          ArcFinitePosition.intervalMeshParameter n hn l.2 t
        rw [hl₂]
  have hcellVerticalNeighbor (k l : Fin n × Fin n)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (t : Interval) :
      cellMap k (t,1) = cellMap l (t,0) := by
    as_aux_lemma =>
      apply Prod.ext
      · change ArcFinitePosition.intervalMeshParameter n hn k.1 t =
          ArcFinitePosition.intervalMeshParameter n hn l.1 t
        rw [hl₁]
      · apply Subtype.ext
        have hc : (l.2.val:ℝ) = (k.2.val:ℝ)+1 := by exact_mod_cast hl₂
        change ((k.2.val:ℝ)+(1:Interval).val)/(n:ℝ) =
          ((l.2.val:ℝ)+(0:Interval).val)/(n:ℝ)
        simp [hc]
  choose P hPmarks Q hPQ hQlong hQwidth hPvertices H hHmarks hHinitial hHfinal hHvertices J hHJ hJlong hJwidth
    using hlocalPLRedrawing
  let activeV (k : Fin n × Fin n) (hk : label (index k)=some 0) (i : Fin 4) :
      Interval × Set.Icc (-1:ℝ) 1 :=
    hB.toHomeomorph.symm (liftG ⟨cellMap k (corners i),
      hchartBand (index k) hk (hcellSource k _ (mem_range_self _))⟩)
  have hactiveVEqual (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (i j : Fin 4) (he : cellMap k (corners i)=cellMap l (corners j)) :
      activeV k hk i = activeV l hl j := by
    apply congrArg hB.toHomeomorph.symm
    apply congrArg liftG
    exact Subtype.ext he
  have hQHorizontal (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (t : Interval) :
      Q k hk (1,t) = Q l hl (0,t) := by
    as_aux_lemma =>
      have hv₀ : activeV k hk 1 = activeV l hl 0 :=
        hactiveVEqual k l hk hl 1 0 (hcellHorizontalNeighbor k l hl₁ hl₂ 0)
      have hv₁ : activeV k hk 3 = activeV l hl 2 :=
        hactiveVEqual k l hk hl 3 2 (hcellHorizontalNeighbor k l hl₁ hl₂ 1)
      apply Prod.ext <;> apply Subtype.ext
      · rw [hQlong,hQlong]
        change (∑ i,weights (1,t) i * (activeV k hk i).1.val) =
          (∑ i,weights (0,t) i * (activeV l hl i).1.val)
        rw [(hweightsEdgeSums t (fun i => (activeV k hk i).1.val)).2.1,
          (hweightsEdgeSums t (fun i => (activeV l hl i).1.val)).1,hv₀,hv₁]
      · rw [hQwidth,hQwidth]
        change (∑ i,weights (1,t) i * (activeV k hk i).2.val) =
          (∑ i,weights (0,t) i * (activeV l hl i).2.val)
        rw [(hweightsEdgeSums t (fun i => (activeV k hk i).2.val)).2.1,
          (hweightsEdgeSums t (fun i => (activeV l hl i).2.val)).1,hv₀,hv₁]
  have hQVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (t : Interval) :
      Q k hk (t,1) = Q l hl (t,0) := by
    as_aux_lemma =>
      have hv₀ : activeV k hk 2 = activeV l hl 0 :=
        hactiveVEqual k l hk hl 2 0 (hcellVerticalNeighbor k l hl₁ hl₂ 0)
      have hv₁ : activeV k hk 3 = activeV l hl 1 :=
        hactiveVEqual k l hk hl 3 1 (hcellVerticalNeighbor k l hl₁ hl₂ 1)
      apply Prod.ext <;> apply Subtype.ext
      · rw [hQlong,hQlong]
        change (∑ i,weights (t,1) i * (activeV k hk i).1.val) =
          (∑ i,weights (t,0) i * (activeV l hl i).1.val)
        rw [(hweightsEdgeSums t (fun i => (activeV k hk i).1.val)).2.2.2,
          (hweightsEdgeSums t (fun i => (activeV l hl i).1.val)).2.2.1,hv₀,hv₁]
      · rw [hQwidth,hQwidth]
        change (∑ i,weights (t,1) i * (activeV k hk i).2.val) =
          (∑ i,weights (t,0) i * (activeV l hl i).2.val)
        rw [(hweightsEdgeSums t (fun i => (activeV k hk i).2.val)).2.2.2,
          (hweightsEdgeSums t (fun i => (activeV l hl i).2.val)).2.2.1,hv₀,hv₁]
  have hPHorizontal (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (t : Interval) :
      P k hk (1,t) = P l hl (0,t) := by
    as_aux_lemma =>
      rw [hPQ,hPQ,hQHorizontal k l hk hl hl₁ hl₂ t]
  have hPVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (t : Interval) :
      P k hk (t,1) = P l hl (t,0) := by
    as_aux_lemma =>
      rw [hPQ,hPQ,hQVertical k l hk hl hl₁ hl₂ t]
  have hsourceCoordsEqual (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (z w : Interval × Interval) (he : cellMap k z=cellMap l w) :
      sourceCoords k hk z = sourceCoords l hl w := by
    apply congrArg hB.toHomeomorph.symm
    apply congrArg liftG
    exact Subtype.ext he
  have hHHorizontal (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (τ t : Interval) :
      H k hk (τ,(1,t)) = H l hl (τ,(0,t)) := by
    as_aux_lemma =>
      rw [hHJ,hHJ]
      apply congrArg B
      have hr := hsourceCoordsEqual k l hk hl (1,t) (0,t)
        (hcellHorizontalNeighbor k l hl₁ hl₂ t)
      have hq := hQHorizontal k l hk hl hl₁ hl₂ t
      apply Prod.ext <;> apply Subtype.ext
      · rw [hJlong,hJlong,hr,hq]
      · rw [hJwidth,hJwidth,hr,hq]
  have hHVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (τ t : Interval) :
      H k hk (τ,(t,1)) = H l hl (τ,(t,0)) := by
    as_aux_lemma =>
      rw [hHJ,hHJ]
      apply congrArg B
      have hr := hsourceCoordsEqual k l hk hl (t,1) (t,0)
        (hcellVerticalNeighbor k l hl₁ hl₂ t)
      have hq := hQVertical k l hk hl hl₁ hl₂ t
      apply Prod.ext <;> apply Subtype.ext
      · rw [hJlong,hJlong,hr,hq]
      · rw [hJwidth,hJwidth,hr,hq]
  have hblendIcc (c d : ℝ) (x y : Set.Icc c d) (τ : Interval) :
      (1-τ.val)*x.val + τ.val*y.val ∈ Icc c d := by
    as_aux_lemma =>
      have h := (convex_Icc (𝕜:=ℝ) c d).lineMap_mem x.property y.property τ.property
      change τ.val*(y.val-x.val)+x.val ∈ Icc c d at h
      convert h using 1 <;> ring
  let blend : C(Interval × ((Interval × Set.Icc (-1:ℝ) 1) ×
      (Interval × Set.Icc (-1:ℝ) 1)),Interval × Set.Icc (-1:ℝ) 1) := {
    toFun := fun z =>
      (⟨(1-z.1.val)*z.2.1.1.val+z.1.val*z.2.2.1.val,
        hblendIcc 0 1 z.2.1.1 z.2.2.1 z.1⟩,
       ⟨(1-z.1.val)*z.2.1.2.val+z.1.val*z.2.2.2.val,
        hblendIcc (-1) 1 z.2.1.2 z.2.2.2 z.1⟩)
    continuous_toFun := by fun_prop }
  have hblendZero (v w : Interval × Set.Icc (-1:ℝ) 1) : blend (0,(v,w)) = v := by
    as_aux_lemma =>
      ext <;> simp [blend]
  have hblendOne (v w : Interval × Set.Icc (-1:ℝ) 1) : blend (1,(v,w)) = w := by
    as_aux_lemma =>
      ext <;> simp [blend]
  have hblendSame (τ : Interval) (v : Interval × Set.Icc (-1:ℝ) 1) :
      blend (τ,(v,v)) = v := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext <;> dsimp [blend] <;> ring
  have hblendIoo (c d x y : ℝ) (hx : x ∈ Ioo c d) (hy : y ∈ Ioo c d)
      (τ : Interval) : (1-τ.val)*x+τ.val*y ∈ Ioo c d := by
    as_aux_lemma =>
      have h := (convex_Ioo (𝕜:=ℝ) c d).lineMap_mem hx hy τ.property
      change τ.val*(y-x)+x ∈ Ioo c d at h
      convert h using 1 <;> ring
  have hQinterior (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) :
      (Q k hk z).1.val ∈ Ioo (0:ℝ) 1 ∧ (Q k hk z).2.val ∈ Ioo (-1:ℝ) 1 := by
    as_aux_lemma =>
      constructor
      · rw [hQlong]
        simpa only [smul_eq_mul] using
          (convex_Ioo (𝕜:=ℝ) (0:ℝ) 1).sum_mem (fun i _ => hweightsNonneg z i)
            (hweightsSum z) (fun i _ =>
              (show (activeV k hk i).1.val ∈ Ioo (0:ℝ) 1 from
                ⟨(hcoordinatesInterior _).1,(hcoordinatesInterior _).2.1⟩))
      · rw [hQwidth]
        simpa only [smul_eq_mul] using
          (convex_Ioo (𝕜:=ℝ) (-1:ℝ) 1).sum_mem (fun i _ => hweightsNonneg z i)
            (hweightsSum z) (fun i _ =>
              (show (activeV k hk i).2.val ∈ Ioo (-1:ℝ) 1 from
                ⟨(hcoordinatesInterior _).2.2.1,(hcoordinatesInterior _).2.2.2⟩))
  have hsourceCoordsContinuous (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      Continuous (sourceCoords k hk) :=
    hB.toHomeomorph.symm.continuous.comp
      (liftG.continuous.comp ((cellMap k).continuous.subtype_mk _))
  have hsourceCoordsInterior (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) :
      (sourceCoords k hk z).1.val ∈ Ioo (0:ℝ) 1 ∧
      (sourceCoords k hk z).2.val ∈ Ioo (-1:ℝ) 1 :=
    ⟨⟨(hcoordinatesInterior _).1,(hcoordinatesInterior _).2.1⟩,
      ⟨(hcoordinatesInterior _).2.2.1,(hcoordinatesInterior _).2.2.2⟩⟩
  have hactualLowerParameterRelativeCell (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t, D (t,0) = sourceCoords k hk (t,0)) ∧
        (∀ t, D (t,1) = Q k hk (t,1)) ∧
        ∃ Hr : C(Interval × (Interval × Interval),S),
          (∀ z, Hr z ∉ (M.cover.branch : Set S)) ∧
          (∀ z, Hr (0,z) = G (cellMap k z)) ∧
          (∀ z, Hr (1,z) = B (D z)) ∧
          (∀ τ t, Hr (τ,(t,0)) = G (cellMap k (t,0))) := by
    as_aux_lemma =>
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        ⟨sourceCoords k hk,hsourceCoordsContinuous k hk⟩
      let D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z => blend (z.2,(R (z.1,0),Q k hk (z.1,1)))
        continuous_toFun := by fun_prop }
      have hDzero (t : Interval) : D (t,0) = R (t,0) := hblendZero _ _
      have hDone (t : Interval) : D (t,1) = Q k hk (t,1) := hblendOne _ _
      have hDinterior (z : Interval × Interval) :
          (D z).1.val ∈ Ioo (0:ℝ) 1 ∧ (D z).2.val ∈ Ioo (-1:ℝ) 1 :=
        ⟨hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk _).1 (hQinterior k hk _).1 z.2,
         hblendIoo (-1) 1 _ _ (hsourceCoordsInterior k hk _).2 (hQinterior k hk _).2 z.2⟩
      let Hr : C(Interval × (Interval × Interval),S) := {
        toFun := fun z => B (blend (z.1,(R z.2,D z.2)))
        continuous_toFun := by exact hB.continuous.comp (by fun_prop) }
      have hBR (z : Interval × Interval) : B (R z) = G (cellMap k z) :=
        congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
      refine ⟨D,hDzero,hDone,Hr,?_,?_,?_,?_⟩
      · intro z
        have hlong := hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk z.2).1
          (hDinterior z.2).1 z.1
        exact hBmarks _ _ (ne_of_gt hlong.1) (ne_of_lt hlong.2)
      · intro z
        change B (blend (0,(R z,D z))) = _
        rw [hblendZero]
        exact hBR z
      · intro z
        change B (blend (1,(R z,D z))) = _
        rw [hblendOne]
      · intro τ t
        change B (blend (τ,(R (t,0),D (t,0)))) = _
        rw [hDzero,hblendSame]
        exact hBR (t,0)
  have hactualInitialTimeRelativeCell (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t, D (0,t) = sourceCoords k hk (0,t)) ∧
        (∀ t, D (1,t) = Q k hk (1,t)) ∧
        ∃ Hr : C(Interval × (Interval × Interval),S),
          (∀ z, Hr z ∉ (M.cover.branch : Set S)) ∧
          (∀ z, Hr (0,z) = G (cellMap k z)) ∧
          (∀ z, Hr (1,z) = B (D z)) ∧
          (∀ τ t, Hr (τ,(0,t)) = G (cellMap k (0,t))) ∧
          (∀ z,D z = blend (z.1,(sourceCoords k hk (0,z.2),Q k hk (1,z.2)))) ∧
          (∀ z,Hr z = B (blend (z.1,(sourceCoords k hk z.2,D z.2)))) := by
    as_aux_lemma =>
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        ⟨sourceCoords k hk,hsourceCoordsContinuous k hk⟩
      let D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z => blend (z.1,(R (0,z.2),Q k hk (1,z.2)))
        continuous_toFun := by fun_prop }
      have hDzero (t : Interval) : D (0,t) = R (0,t) := hblendZero _ _
      have hDone (t : Interval) : D (1,t) = Q k hk (1,t) := hblendOne _ _
      have hDinterior (z : Interval × Interval) :
          (D z).1.val ∈ Ioo (0:ℝ) 1 ∧ (D z).2.val ∈ Ioo (-1:ℝ) 1 :=
        ⟨hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk _).1 (hQinterior k hk _).1 z.1,
         hblendIoo (-1) 1 _ _ (hsourceCoordsInterior k hk _).2 (hQinterior k hk _).2 z.1⟩
      let Hr : C(Interval × (Interval × Interval),S) := {
        toFun := fun z => B (blend (z.1,(R z.2,D z.2)))
        continuous_toFun := by exact hB.continuous.comp (by fun_prop) }
      have hBR (z : Interval × Interval) : B (R z) = G (cellMap k z) :=
        congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
      refine ⟨D,hDzero,hDone,Hr,?_,?_,?_,?_,(fun _ => rfl),(fun _ => rfl)⟩
      · intro z
        have hlong := hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk z.2).1
          (hDinterior z.2).1 z.1
        exact hBmarks _ _ (ne_of_gt hlong.1) (ne_of_lt hlong.2)
      · intro z
        change B (blend (0,(R z,D z))) = _
        rw [hblendZero]
        exact hBR z
      · intro z
        change B (blend (1,(R z,D z))) = _
        rw [hblendOne]
      · intro τ t
        change B (blend (τ,(R (0,t),D (0,t)))) = _
        rw [hDzero,hblendSame]
        exact hBR (0,t)
  have hcellInitialBoundary (k : Fin n × Fin n) (hk₀ : k.1.val=0) (t : Interval) :
      G (cellMap k (0,t)) = b.val.map
        (centralParam (ArcFinitePosition.intervalMeshParameter n hn k.2 t)) := by
    as_aux_lemma =>
      have he : cellMap k (0,t) =
          (0,ArcFinitePosition.intervalMeshParameter n hn k.2 t) := by
        apply Prod.ext
        · apply Subtype.ext
          change ((k.1.val:ℝ)+(0:Interval).val)/(n:ℝ) = (0:Interval).val
          simp [hk₀]
        · rfl
      rw [he,hGinitial]
  have hactualFirstTimeRow (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (hk₀ : k.1.val=0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t,D (1,t)=Q k hk (1,t)) ∧
        ∃ Hr : C(Interval × (Interval × Interval),S),
          (∀ z,Hr z ∉ (M.cover.branch : Set S)) ∧
          (∀ z,Hr (0,z)=G (cellMap k z)) ∧
          (∀ z,Hr (1,z)=B (D z)) ∧
          (∀ τ t,Hr (τ,(0,t)) = b.val.map
            (centralParam (ArcFinitePosition.intervalMeshParameter n hn k.2 t))) := by
    as_aux_lemma =>
      obtain ⟨D,hDzero,hDone,Hr,hmarks,hzero,hone,hrelative,hDformula,hHrformula⟩ := hactualInitialTimeRelativeCell k hk
      refine ⟨D,hDone,Hr,hmarks,hzero,hone,?_⟩
      intro τ t
      rw [hrelative,hcellInitialBoundary k hk₀ t]
  choose Dinitial hDinitialZero hDinitialOne Hinitial hHinitialMarks hHinitialStart
    hHinitialFinish hHinitialRelative hDinitialFormula hHinitialFormula
    using hactualInitialTimeRelativeCell
  have hDinitialVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (t : Interval) :
      Dinitial k hk (t,1)=Dinitial l hl (t,0) := by
    as_aux_lemma =>
      rw [hDinitialFormula,hDinitialFormula]
      have hr := hsourceCoordsEqual k l hk hl (0,1) (0,0)
        (hcellVerticalNeighbor k l hl₁ hl₂ 0)
      have hq := hQVertical k l hk hl hl₁ hl₂ 1
      rw [hr,hq]
  have hHinitialVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (τ t : Interval) :
      Hinitial k hk (τ,(t,1))=Hinitial l hl (τ,(t,0)) := by
    as_aux_lemma =>
      rw [hHinitialFormula,hHinitialFormula]
      have hr := hsourceCoordsEqual k l hk hl (t,1) (t,0)
        (hcellVerticalNeighbor k l hl₁ hl₂ t)
      rw [hr,hDinitialVertical k l hk hl hl₁ hl₂ t]
  have hHinitialToStandard (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (τ t : Interval) :
      Hinitial k hk (τ,(1,t))=H l hl (τ,(0,t)) := by
    as_aux_lemma =>
      rw [hHinitialFormula,hHJ,hDinitialOne]
      apply congrArg B
      have hr := hsourceCoordsEqual k l hk hl (1,t) (0,t)
        (hcellHorizontalNeighbor k l hl₁ hl₂ t)
      have hq := hQHorizontal k l hk hl hl₁ hl₂ t
      apply Prod.ext <;> apply Subtype.ext
      · change (1-τ.val)*(sourceCoords k hk (1,t)).1.val +
          τ.val*(Q k hk (1,t)).1.val = (J l hl (τ,(0,t))).1.val
        rw [hJlong,hr,hq]
      · change (1-τ.val)*(sourceCoords k hk (1,t)).2.val +
          τ.val*(Q k hk (1,t)).2.val = (J l hl (τ,(0,t))).2.val
        rw [hJwidth,hr,hq]
  have hcompactClip (c d : ℝ) (r q : C(Interval × Interval,ℝ))
      (hr : ∀ z,r z ∈ Ioo c d) (hq : ∀ z,q z ∈ Ioo c d) :
      ∃ clip : C(ℝ,ℝ), (∀ x,clip x ∈ Ioo c d) ∧
        (∀ z,clip (r z)=r z) ∧ (∀ z,clip (q z)=q z) := by
    as_aux_lemma =>
      let A : Set ℝ := range r ∪ range q
      have hA : IsCompact A := (isCompact_range r.continuous).union (isCompact_range q.continuous)
      have hne : A.Nonempty := ⟨r (0,0),Or.inl (mem_range_self _)⟩
      have hAI : A ⊆ Ioo c d := by
        intro x hx
        rcases hx with ⟨z,rfl⟩ | ⟨z,rfl⟩
        · exact hr z
        · exact hq z
      obtain ⟨c',hc',hmin⟩ := hA.exists_isLeast hne
      obtain ⟨d',hd',hmax⟩ := hA.exists_isGreatest hne
      have hcd : c' ≤ d' := hmin hd'
      let clip : C(ℝ,ℝ) := ⟨fun x => (Set.projIcc c' d' hcd x).val,
        continuous_subtype_val.comp continuous_projIcc⟩
      refine ⟨clip,?_,?_,?_⟩
      · intro x
        exact ⟨lt_of_lt_of_le (hAI hc').1 (Set.projIcc c' d' hcd x).property.1,
          lt_of_le_of_lt (Set.projIcc c' d' hcd x).property.2 (hAI hd').2⟩
      · intro z
        have hz : r z ∈ A := Or.inl (mem_range_self _)
        change (Set.projIcc c' d' hcd (r z)).val = r z
        rw [Set.projIcc_of_mem _ ⟨hmin hz,hmax hz⟩]
      · intro z
        have hz : q z ∈ A := Or.inr (mem_range_self _)
        change (Set.projIcc c' d' hcd (q z)).val = q z
        rw [Set.projIcc_of_mem _ ⟨hmin hz,hmax hz⟩]
  have hBsourceCoords (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) : B (sourceCoords k hk z)=G (cellMap k z) :=
    congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
  have hQsourceVertices (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) : Q k hk (corners i)=sourceCoords k hk (corners i) := by
    as_aux_lemma =>
      apply hB.injective
      rw [←hPQ k hk (corners i),hPvertices k hk i,hBsourceCoords k hk (corners i)]
  have hactualTwoBoundaryRelativeCell (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t,D (0,t)=sourceCoords k hk (0,t)) ∧
        (∀ t,D (t,0)=sourceCoords k hk (t,0)) ∧
        (∀ t,D (1,t)=Q k hk (1,t)) ∧
        (∀ t,D (t,1)=Q k hk (t,1)) ∧
        (∀ z,(D z).1.val ∈ Ioo (0:ℝ) 1 ∧ (D z).2.val ∈ Ioo (-1:ℝ) 1) := by
    as_aux_lemma =>
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        ⟨sourceCoords k hk,hsourceCoordsContinuous k hk⟩
      let r₁ : C(Interval × Interval,ℝ) := ⟨fun z => (R z).1.val,by fun_prop⟩
      let r₂ : C(Interval × Interval,ℝ) := ⟨fun z => (R z).2.val,by fun_prop⟩
      let q₁ : C(Interval × Interval,ℝ) := ⟨fun z => (Q k hk z).1.val,by fun_prop⟩
      let q₂ : C(Interval × Interval,ℝ) := ⟨fun z => (Q k hk z).2.val,by fun_prop⟩
      obtain ⟨clip₁,hclip₁,hclip₁r,hclip₁q⟩ := hcompactClip 0 1 r₁ q₁
        (fun z => (hsourceCoordsInterior k hk z).1) (fun z => (hQinterior k hk z).1)
      obtain ⟨clip₂,hclip₂,hclip₂r,hclip₂q⟩ := hcompactClip (-1) 1 r₂ q₂
        (fun z => (hsourceCoordsInterior k hk z).2) (fun z => (hQinterior k hk z).2)
      let coons (r q : C(Interval × Interval,ℝ)) : C(Interval × Interval,ℝ) := {
        toFun := fun z => q z + (1-z.1.val)*(r (0,z.2)-q (0,z.2)) +
          (1-z.2.val)*(r (z.1,0)-q (z.1,0))
        continuous_toFun := by fun_prop }
      let D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z =>
          (⟨clip₁ (coons r₁ q₁ z),(hclip₁ _).1.le,(hclip₁ _).2.le⟩,
           ⟨clip₂ (coons r₂ q₂ z),(hclip₂ _).1.le,(hclip₂ _).2.le⟩)
        continuous_toFun := by fun_prop }
      have hc₀ : Q k hk (0,0)=R (0,0) := hQsourceVertices k hk 0
      have hc₁ : Q k hk (1,0)=R (1,0) := hQsourceVertices k hk 1
      have hc₂ : Q k hk (0,1)=R (0,1) := hQsourceVertices k hk 2
      have hcoonsEdges (r q : C(Interval × Interval,ℝ))
          (h₀ : q (0,0)=r (0,0)) (h₁ : q (1,0)=r (1,0))
          (h₂ : q (0,1)=r (0,1)) (t : Interval) :
          coons r q (0,t)=r (0,t) ∧ coons r q (t,0)=r (t,0) ∧
          coons r q (1,t)=q (1,t) ∧ coons r q (t,1)=q (t,1) := by
        dsimp [coons]
        simp only [h₀,h₁,h₂,sub_self,mul_zero,add_zero]
        constructor
        · ring
        constructor
        · ring
        constructor <;> ring
      have he₁ (t : Interval) := hcoonsEdges r₁ q₁
        (congrArg (fun z => z.1.val) hc₀) (congrArg (fun z => z.1.val) hc₁)
        (congrArg (fun z => z.1.val) hc₂) t
      have he₂ (t : Interval) := hcoonsEdges r₂ q₂
        (congrArg (fun z => z.2.val) hc₀) (congrArg (fun z => z.2.val) hc₁)
        (congrArg (fun z => z.2.val) hc₂) t
      refine ⟨D,?_,?_,?_,?_,fun z => ⟨hclip₁ _,hclip₂ _⟩⟩
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (0,t))=r₁ (0,t)
          rw [(he₁ t).1,hclip₁r]
        · change clip₂ (coons r₂ q₂ (0,t))=r₂ (0,t)
          rw [(he₂ t).1,hclip₂r]
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (t,0))=r₁ (t,0)
          rw [(he₁ t).2.1,hclip₁r]
        · change clip₂ (coons r₂ q₂ (t,0))=r₂ (t,0)
          rw [(he₂ t).2.1,hclip₂r]
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (1,t))=q₁ (1,t)
          rw [(he₁ t).2.2.1,hclip₁q]
        · change clip₂ (coons r₂ q₂ (1,t))=q₂ (1,t)
          rw [(he₂ t).2.2.1,hclip₂q]
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (t,1))=q₁ (t,1)
          rw [(he₁ t).2.2.2,hclip₁q]
        · change clip₂ (coons r₂ q₂ (t,1))=q₂ (t,1)
          rw [(he₂ t).2.2.2,hclip₂q]
  have hactualTwoBoundaryRelativeHomotopy (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        ∃ Hr : C(Interval × (Interval × Interval),S),
          (∀ z,Hr z ∉ (M.cover.branch : Set S)) ∧
          (∀ z,Hr (0,z)=G (cellMap k z)) ∧
          (∀ z,Hr (1,z)=B (D z)) ∧
          (∀ τ t,Hr (τ,(0,t))=G (cellMap k (0,t))) ∧
          (∀ τ t,Hr (τ,(t,0))=G (cellMap k (t,0))) ∧
          (∀ τ t,Hr (τ,(1,t))=H k hk (τ,(1,t))) ∧
          (∀ τ t,Hr (τ,(t,1))=H k hk (τ,(t,1))) := by
    as_aux_lemma =>
      obtain ⟨D,hDleft,hDbottom,hDright,hDtop,hDinterior⟩ := hactualTwoBoundaryRelativeCell k hk
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        ⟨sourceCoords k hk,hsourceCoordsContinuous k hk⟩
      let Hr : C(Interval × (Interval × Interval),S) := {
        toFun := fun z => B (blend (z.1,(R z.2,D z.2)))
        continuous_toFun := hB.continuous.comp (by fun_prop) }
      have hRsource (z : Interval × Interval) : B (R z)=G (cellMap k z) :=
        hBsourceCoords k hk z
      have hHblend (τ : Interval) (z : Interval × Interval) :
          H k hk (τ,z)=B (blend (τ,(R z,Q k hk z))) := by
        rw [hHJ]
        apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · rw [hJlong]
          rfl
        · rw [hJwidth]
          rfl
      refine ⟨D,Hr,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        have hlong := hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk z.2).1
          (hDinterior z.2).1 z.1
        exact hBmarks _ _ (ne_of_gt hlong.1) (ne_of_lt hlong.2)
      · intro z
        change B (blend (0,(R z,D z))) = _
        rw [hblendZero]
        exact hRsource z
      · intro z
        change B (blend (1,(R z,D z))) = _
        rw [hblendOne]
      · intro τ t
        change B (blend (τ,(sourceCoords k hk (0,t),D (0,t)))) = _
        rw [hDleft,hblendSame]
        exact hBsourceCoords k hk (0,t)
      · intro τ t
        change B (blend (τ,(sourceCoords k hk (t,0),D (t,0)))) = _
        rw [hDbottom,hblendSame]
        exact hBsourceCoords k hk (t,0)
      · intro τ t
        change B (blend (τ,(R (1,t),D (1,t)))) = _
        rw [hDright,hHblend]
      · intro τ t
        change B (blend (τ,(R (t,1),D (t,1)))) = _
        rw [hDtop,hHblend]
  let ActiveCell := {k : Fin n × Fin n // label (index k)=some 0}
  have hActiveNonempty : Nonempty ActiveCell := by
    as_aux_lemma =>
      obtain ⟨s,hs,he,hzero⟩ := hcrossZeroCaptured l hl
      have hz : (0,s) ∈ Z := (hψzero ⟨(0,s),hs⟩).mp hzero
      have hsupport : (0,s) ∈ support := interior_subset (hZinterior hz)
      obtain ⟨k,hk⟩ := mem_iUnion.mp hsupport
      by_cases he : label (index k)=some 0
      · exact ⟨⟨k,he⟩⟩
      · simp only [if_neg he,mem_empty_iff_false] at hk
  let vertexWidth (j : ActiveCell × Fin 4) : ℝ :=
    (activeV j.1.val j.1.property j.2).2.val
  have hvertexInterior (j : ActiveCell × Fin 4) : vertexWidth j ∈ Ioo (-1:ℝ) 1 :=
    ⟨(hcoordinatesInterior _).2.2.1,(hcoordinatesInterior _).2.2.2⟩
  have hactualVertexShift : ∃ δ : ℝ, 0 < δ ∧
      ∀ j : ActiveCell × Fin 4, vertexWidth j+δ ∈ Ioo (-1:ℝ) 1 ∧
        vertexWidth j+δ ≠ 0 ∧ (vertexWidth j < 0 → vertexWidth j+δ < 0) := by
    as_aux_lemma =>
      have hfinite : (range vertexWidth).Finite := Set.finite_range _
      have hne : (range vertexWidth).Nonempty := by
        obtain ⟨k⟩ := hActiveNonempty
        exact ⟨vertexWidth (k,0),mem_range_self _⟩
      obtain ⟨wmax,hwmax,hmax⟩ := hfinite.isCompact.exists_isGreatest hne
      have hwmaxlt : wmax < 1 := by
        obtain ⟨j,rfl⟩ := hwmax
        exact (hvertexInterior j).2
      let negatives : Set ℝ := {w ∈ range vertexWidth | w < 0} ∪ {(-1:ℝ)}
      have hnegFinite : negatives.Finite :=
        (hfinite.subset (fun _ hx => hx.1)).union (finite_singleton _)
      have hnegNonempty : negatives.Nonempty := ⟨-1,Or.inr rfl⟩
      obtain ⟨wneg,hwneg,hnegmax⟩ := hnegFinite.isCompact.exists_isGreatest hnegNonempty
      have hwneglt : wneg < 0 := by
        rcases hwneg with hw | hw
        · exact hw.2
        · have he : wneg=(-1:ℝ) := hw
          rw [he]
          norm_num
      let margin : ℝ := min ((1-wmax)/2) ((-wneg)/2)
      have hmargin : 0 < margin := lt_min (by linarith only [hwmaxlt]) (by linarith only [hwneglt])
      let δ : ℝ := margin/2
      have hδpos : 0 < δ := by dsimp [δ]; linarith only [hmargin]
      have hδwidth : δ < (1-wmax)/2 := by
        have hm := min_le_left ((1-wmax)/2) ((-wneg)/2)
        change margin ≤ (1-wmax)/2 at hm
        dsimp [δ]
        linarith only [hmargin,hm]
      have hδnegative : δ < (-wneg)/2 := by
        have hm := min_le_right ((1-wmax)/2) ((-wneg)/2)
        change margin ≤ (-wneg)/2 at hm
        dsimp [δ]
        linarith only [hmargin,hm]
      have hpreserve (j : ActiveCell × Fin 4) (hj : vertexWidth j<0) : vertexWidth j+δ<0 := by
        have hbound : vertexWidth j ≤ wneg := hnegmax (Or.inl ⟨mem_range_self j,hj⟩)
        linarith only [hbound,hδnegative,hwneglt]
      refine ⟨δ,hδpos,?_⟩
      intro j
      refine ⟨⟨by linarith only [(hvertexInterior j).1,hδpos],?_⟩,?_,hpreserve j⟩
      · have hj : vertexWidth j ≤ wmax := hmax (mem_range_self j)
        linarith only [hj,hδwidth,hwmaxlt]
      · by_cases hj : vertexWidth j<0
        · exact ne_of_lt (hpreserve j hj)
        · exact ne_of_gt (by linarith only [hj,hδpos])
  obtain ⟨vertexShift,hvertexShiftPos,hvertexShift⟩ := hactualVertexShift
  have hshiftedWidthInterior (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) : (Q k hk z).2.val+vertexShift ∈ Ioo (-1:ℝ) 1 := by
    as_aux_lemma =>
      have hv (i : Fin 4) : (activeV k hk i).2.val+vertexShift ∈ Ioo (-1:ℝ) 1 :=
        (hvertexShift (⟨k,hk⟩,i)).1
      have h := (convex_Ioo (𝕜:=ℝ) (-1:ℝ) 1).sum_mem
        (fun i _ => hweightsNonneg z i) (hweightsSum z) (fun i _ => hv i)
      simp only [smul_eq_mul,mul_add,Finset.sum_add_distrib] at h
      rw [←Finset.sum_mul,hweightsSum,one_mul] at h
      rw [hQwidth]
      exact h
  let Qshift (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
    toFun := fun z => ((Q k hk z).1,
      ⟨(Q k hk z).2.val+vertexShift,(hshiftedWidthInterior k hk z).1.le,
        (hshiftedWidthInterior k hk z).2.le⟩)
    continuous_toFun := by fun_prop }
  have hQshiftVertices (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) : (Qshift k hk (corners i)).2.val ≠ 0 := by
    as_aux_lemma =>
      change (Q k hk (corners i)).2.val+vertexShift ≠ 0
      rw [hQsourceVertices]
      exact (hvertexShift (⟨k,hk⟩,i)).2.1
  have hQshiftHorizontal (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (t : Interval) :
      Qshift k hk (1,t)=Qshift l hl (0,t) := by
    as_aux_lemma =>
      apply Prod.ext
      · change (Q k hk (1,t)).1 = (Q l hl (0,t)).1
        exact congrArg Prod.fst (hQHorizontal k l hk hl hl₁ hl₂ t)
      · apply Subtype.ext
        change (Q k hk (1,t)).2.val+vertexShift = (Q l hl (0,t)).2.val+vertexShift
        rw [hQHorizontal k l hk hl hl₁ hl₂ t]
  have hQshiftVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (t : Interval) :
      Qshift k hk (t,1)=Qshift l hl (t,0) := by
    as_aux_lemma =>
      apply Prod.ext
      · change (Q k hk (t,1)).1 = (Q l hl (t,0)).1
        exact congrArg Prod.fst (hQVertical k l hk hl hl₁ hl₂ t)
      · apply Subtype.ext
        change (Q k hk (t,1)).2.val+vertexShift = (Q l hl (t,0)).2.val+vertexShift
        rw [hQVertical k l hk hl hl₁ hl₂ t]
  have hQshiftMarks (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) : B (Qshift k hk z) ∉ (M.cover.branch : Set S) :=
    hBmarks _ _ (ne_of_gt (hQinterior k hk z).1.1) (ne_of_lt (hQinterior k hk z).1.2)
  have hpathOneSign (f : C(Interval,ℝ)) (hzero : ∀ t,f t ≠ 0) :
      (∀ t,0 < f t) ∨ (∀ t,f t < 0) := by
    as_aux_lemma =>
      by_cases hp : 0 < f 0
      · left
        intro t
        by_contra ht
        obtain ⟨u,hu⟩ := intermediate_value_univ t (0:Interval) f.continuous
          (show (0:ℝ) ∈ Icc (f t) (f 0) from ⟨le_of_not_gt ht,hp.le⟩)
        exact hzero u hu
      · have hn : f 0 < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hzero 0)
        right
        intro t
        by_contra ht
        obtain ⟨u,hu⟩ := intermediate_value_univ (0:Interval) t f.continuous
          (show (0:ℝ) ∈ Icc (f 0) (f t) from ⟨hn.le,le_of_not_gt ht⟩)
        exact hzero u hu
  have hQshiftTerminalAvoids (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (hlast : k.1.val+1=n) (t : Interval) : B (Qshift k hk (1,t)) ∉ a.val.image := by
    as_aux_lemma =>
      have htime (s : Interval) : (cellMap k (1,s)).1=1 := by
        apply Subtype.ext
        change ((k.1.val:ℝ)+(1:Interval).val)/(n:ℝ) = (1:Interval).val
        have hc : (k.1.val:ℝ)+1=(n:ℝ) := by exact_mod_cast hlast
        have hnreal : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        change ((k.1.val:ℝ)+1)/(n:ℝ) = 1
        rw [hc,div_self hnreal]
      let f : C(Interval,ℝ) := ⟨fun s => (sourceCoords k hk (1,s)).2.val,
        by exact continuous_subtype_val.comp (continuous_snd.comp
          ((hsourceCoordsContinuous k hk).comp (continuous_const.prodMk continuous_id)))⟩
      have hfzero (s : Interval) : f s ≠ 0 :=
        hψtop ⟨cellMap k (1,s),hchartBand (index k) hk
          (hcellSource k _ (mem_range_self _))⟩ (htime s)
      have hvalue : (Qshift k hk (1,t)).2.val =
          (1-t.val)*((activeV k hk 1).2.val+vertexShift) +
          t.val*((activeV k hk 3).2.val+vertexShift) := by
        change (Q k hk (1,t)).2.val+vertexShift = _
        rw [hQwidth]
        change (∑ i,weights (1,t) i*(activeV k hk i).2.val)+vertexShift = _
        rw [(hweightsEdgeSums t (fun i => (activeV k hk i).2.val)).2.1]
        ring
      have hnzero : (Qshift k hk (1,t)).2.val ≠ 0 := by
        rcases hpathOneSign f hfzero with hp | hn
        · have hv₀ : 0 < (activeV k hk 1).2.val+vertexShift := by
            have h : 0 < (activeV k hk 1).2.val := hp 0
            linarith only [h,hvertexShiftPos]
          have hv₁ : 0 < (activeV k hk 3).2.val+vertexShift := by
            have h : 0 < (activeV k hk 3).2.val := hp 1
            linarith only [h,hvertexShiftPos]
          have hmix := (convex_Ioi (𝕜:=ℝ) (0:ℝ)).lineMap_mem hv₀ hv₁ t.property
          change t.val*((activeV k hk 3).2.val+vertexShift-
            ((activeV k hk 1).2.val+vertexShift))+((activeV k hk 1).2.val+vertexShift) ∈ Ioi (0:ℝ) at hmix
          apply ne_of_gt
          rw [hvalue]
          change (0:ℝ) < _ at hmix
          convert hmix using 1 <;> ring
        · have hv₀ : (activeV k hk 1).2.val+vertexShift < 0 :=
            (hvertexShift (⟨k,hk⟩,1)).2.2 (hn 0)
          have hv₁ : (activeV k hk 3).2.val+vertexShift < 0 :=
            (hvertexShift (⟨k,hk⟩,3)).2.2 (hn 1)
          have hmix := (convex_Iio (𝕜:=ℝ) (0:ℝ)).lineMap_mem hv₀ hv₁ t.property
          change t.val*((activeV k hk 3).2.val+vertexShift-
            ((activeV k hk 1).2.val+vertexShift))+((activeV k hk 1).2.val+vertexShift) ∈ Iio (0:ℝ) at hmix
          apply ne_of_lt
          rw [hvalue]
          change _ < (0:ℝ) at hmix
          convert hmix using 1 <;> ring
      intro hhit
      exact hnzero ((hBaxis _ _).mp hhit)
  have hweightsLowerTriangle (z : Interval × Interval) (v : Fin 4 → ℝ)
      (hz : z.1.val+z.2.val ≤ 1) :
      (∑ i,weights z i*v i) = (1-z.1.val-z.2.val)*v 0+z.1.val*v 1+z.2.val*v 2 := by
    as_aux_lemma =>
      have h₀ : 0 ≤ 1-z.1.val-z.2.val := by linarith only [hz]
      have h₁ : z.1.val ≤ 1-z.2.val := by linarith only [hz]
      have h₂ : z.2.val ≤ 1-z.1.val := by linarith only [hz]
      have h₃ : z.1.val+z.2.val-1 ≤ 0 := by linarith only [hz]
      rw [Fin.sum_univ_four]
      change max (1-z.1.val-z.2.val) 0*v 0 + min z.1.val (1-z.2.val)*v 1 +
        min z.2.val (1-z.1.val)*v 2 + max (z.1.val+z.2.val-1) 0*v 3 = _
      rw [max_eq_left h₀,min_eq_left h₁,min_eq_left h₂,max_eq_right h₃]
      ring
  have hweightsUpperTriangle (z : Interval × Interval) (v : Fin 4 → ℝ)
      (hz : 1 ≤ z.1.val+z.2.val) :
      (∑ i,weights z i*v i) = (1-z.2.val)*v 1+(1-z.1.val)*v 2+
        (z.1.val+z.2.val-1)*v 3 := by
    as_aux_lemma =>
      have h₀ : 1-z.1.val-z.2.val ≤ 0 := by linarith only [hz]
      have h₁ : 1-z.2.val ≤ z.1.val := by linarith only [hz]
      have h₂ : 1-z.1.val ≤ z.2.val := by linarith only [hz]
      have h₃ : 0 ≤ z.1.val+z.2.val-1 := by linarith only [hz]
      rw [Fin.sum_univ_four]
      change max (1-z.1.val-z.2.val) 0*v 0 + min z.1.val (1-z.2.val)*v 1 +
        min z.2.val (1-z.1.val)*v 2 + max (z.1.val+z.2.val-1) 0*v 3 = _
      rw [max_eq_right h₀,min_eq_right h₁,min_eq_right h₂,max_eq_left h₃]
      ring
  let affineContactLower (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : ℝ × ℝ) : ℝ :=
    (1-z.1-z.2)*((activeV k hk 0).2.val+vertexShift) +
      z.1*((activeV k hk 1).2.val+vertexShift) +
      z.2*((activeV k hk 2).2.val+vertexShift)
  let affineContactUpper (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : ℝ × ℝ) : ℝ :=
    (1-z.2)*((activeV k hk 1).2.val+vertexShift) +
      (1-z.1)*((activeV k hk 2).2.val+vertexShift) +
      (z.1+z.2-1)*((activeV k hk 3).2.val+vertexShift)
  have hactualCellContactAffine (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      affineContactLower k hk (0,0) ≠ 0 ∧ affineContactUpper k hk (1,1) ≠ 0 ∧
      ∀ z : Interval × Interval, B (Qshift k hk z) ∈ a.val.image →
        affineContactLower k hk (z.1.val,z.2.val)=0 ∨
        affineContactUpper k hk (z.1.val,z.2.val)=0 := by
    as_aux_lemma =>
      refine ⟨?_,?_,?_⟩
      · simpa [affineContactLower] using (hvertexShift (⟨k,hk⟩,0)).2.1
      · simpa [affineContactUpper] using (hvertexShift (⟨k,hk⟩,3)).2.1
      · intro z hz
        have hzero := (hBaxis _ _).mp hz
        change (Q k hk z).2.val+vertexShift=0 at hzero
        rw [hQwidth k hk z] at hzero
        by_cases h : z.1.val+z.2.val ≤ 1
        · left
          change (1-z.1.val-z.2.val)*((activeV k hk 0).2.val+vertexShift) +
            z.1.val*((activeV k hk 1).2.val+vertexShift)+
            z.2.val*((activeV k hk 2).2.val+vertexShift)=0
          have he := hweightsLowerTriangle z (fun i => (activeV k hk i).2.val) h
          change (∑ i,weights z i*(activeV k hk i).2.val)+vertexShift=0 at hzero
          rw [he] at hzero
          nlinarith only [hzero]
        · right
          change (1-z.2.val)*((activeV k hk 1).2.val+vertexShift) +
            (1-z.1.val)*((activeV k hk 2).2.val+vertexShift)+
            (z.1.val+z.2.val-1)*((activeV k hk 3).2.val+vertexShift)=0
          have he := hweightsUpperTriangle z (fun i => (activeV k hk i).2.val) (le_of_not_ge h)
          change (∑ i,weights z i*(activeV k hk i).2.val)+vertexShift=0 at hzero
          rw [he] at hzero
          nlinarith only [hzero]
  let gridBoundary (z : Interval × Interval) : Prop :=
    z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1
  let relativeVertexWidth (k : Fin n × Fin n) (hk : label (index k)=some 0) (i : Fin 4) : ℝ :=
    (activeV k hk i).2.val + if gridBoundary (cellMap k (corners i)) then 0 else vertexShift
  have hrelativeVertexInterior (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) : relativeVertexWidth k hk i ∈ Ioo (-1:ℝ) 1 := by
    as_aux_lemma =>
      by_cases hb : gridBoundary (cellMap k (corners i))
      · simpa only [relativeVertexWidth,if_pos hb,add_zero] using
          hvertexInterior (⟨k,hk⟩,i)
      · simpa only [relativeVertexWidth,if_neg hb] using
          (hvertexShift (⟨k,hk⟩,i)).1
  have hrelativeInteriorVertexNonzero (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) (hb : ¬gridBoundary (cellMap k (corners i))) : relativeVertexWidth k hk i ≠ 0 := by
    as_aux_lemma =>
      simpa only [relativeVertexWidth,if_neg hb] using (hvertexShift (⟨k,hk⟩,i)).2.1
  have hrelativeBoundaryVertexFixed (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) (hb : gridBoundary (cellMap k (corners i))) :
      relativeVertexWidth k hk i = (activeV k hk i).2.val := by
    as_aux_lemma =>
      simp only [relativeVertexWidth,if_pos hb,add_zero]
  have hrelativeVertexEqual (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (i j : Fin 4) (he : cellMap k (corners i)=cellMap l (corners j)) :
      relativeVertexWidth k hk i = relativeVertexWidth l hl j := by
    as_aux_lemma =>
      have hv := hactiveVEqual k l hk hl i j he
      dsimp [relativeVertexWidth]
      rw [hv,he]
  have hrelativeQwidth (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) :
      (∑ i, weights z i * relativeVertexWidth k hk i) ∈ Ioo (-1:ℝ) 1 := by
    as_aux_lemma =>
      simpa only [smul_eq_mul] using
        (convex_Ioo (𝕜:=ℝ) (-1:ℝ) 1).sum_mem (fun i _ => hweightsNonneg z i)
          (hweightsSum z) (fun i _ => hrelativeVertexInterior k hk i)
  let Qrelative (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
    toFun := fun z => ((Q k hk z).1,
      ⟨∑ i,weights z i * relativeVertexWidth k hk i,
        (hrelativeQwidth k hk z).1.le,(hrelativeQwidth k hk z).2.le⟩)
    continuous_toFun := by unfold weights; fun_prop }
  have hQrelativeVertices (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) : (Qrelative k hk (corners i)).2.val = relativeVertexWidth k hk i := by
    as_aux_lemma =>
      change (∑ j,weights (corners i) j * relativeVertexWidth k hk j) = _
      simp [hweightsCorners]
  have hQrelativeBoundaryVertex (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (i : Fin 4) (hb : gridBoundary (cellMap k (corners i))) :
      Qrelative k hk (corners i)=sourceCoords k hk (corners i) := by
    as_aux_lemma =>
      apply Prod.ext
      · change (Q k hk (corners i)).1 = (sourceCoords k hk (corners i)).1
        exact congrArg Prod.fst (hQsourceVertices k hk i)
      · apply Subtype.ext
        rw [hQrelativeVertices,hrelativeBoundaryVertexFixed k hk i hb]
  have hQrelativeHorizontal (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1.val=k.1.val+1) (hl₂ : l.2=k.2) (t : Interval) :
      Qrelative k hk (1,t)=Qrelative l hl (0,t) := by
    as_aux_lemma =>
      apply Prod.ext
      · change (Q k hk (1,t)).1=(Q l hl (0,t)).1
        exact congrArg Prod.fst (hQHorizontal k l hk hl hl₁ hl₂ t)
      · apply Subtype.ext
        change (∑ i,weights (1,t) i*relativeVertexWidth k hk i)=
          (∑ i,weights (0,t) i*relativeVertexWidth l hl i)
        have hv₀ := hrelativeVertexEqual k l hk hl 1 0 (hcellHorizontalNeighbor k l hl₁ hl₂ 0)
        have hv₁ := hrelativeVertexEqual k l hk hl 3 2 (hcellHorizontalNeighbor k l hl₁ hl₂ 1)
        rw [(hweightsEdgeSums t (relativeVertexWidth k hk)).2.1,
          (hweightsEdgeSums t (relativeVertexWidth l hl)).1,hv₀,hv₁]
  have hQrelativeVertical (k l : Fin n × Fin n)
      (hk : label (index k)=some 0) (hl : label (index l)=some 0)
      (hl₁ : l.1=k.1) (hl₂ : l.2.val=k.2.val+1) (t : Interval) :
      Qrelative k hk (t,1)=Qrelative l hl (t,0) := by
    as_aux_lemma =>
      apply Prod.ext
      · change (Q k hk (t,1)).1=(Q l hl (t,0)).1
        exact congrArg Prod.fst (hQVertical k l hk hl hl₁ hl₂ t)
      · apply Subtype.ext
        change (∑ i,weights (t,1) i*relativeVertexWidth k hk i)=
          (∑ i,weights (t,0) i*relativeVertexWidth l hl i)
        have hv₀ := hrelativeVertexEqual k l hk hl 2 0 (hcellVerticalNeighbor k l hl₁ hl₂ 0)
        have hv₁ := hrelativeVertexEqual k l hk hl 3 1 (hcellVerticalNeighbor k l hl₁ hl₂ 1)
        rw [(hweightsEdgeSums t (relativeVertexWidth k hk)).2.2.2,
          (hweightsEdgeSums t (relativeVertexWidth l hl)).2.2.1,hv₀,hv₁]
  have hGinitialEndsAvoid (s : Interval) (hs : s=0 ∨ s=1) : G (0,s) ∉ a.val.image := by
    as_aux_lemma =>
      intro hhit
      have hmark : b.val.map (centralParam s) ∉ (M.cover.branch : Set S) :=
        (hGinitial s) ▸ hGmarks (0,s)
      have hhit' : b.val.map (centralParam s) ∈ a.val.image := (hGinitial s) ▸ hhit
      have hK : centralParam s ∈ K :=
        ⟨⟨hhit',hmark⟩,⟨mem_range_self _,hmark⟩⟩
      have hbounds := hεcross (centralParam s) hK
      rcases hs with rfl | rfl
      · dsimp [centralParam] at hbounds
        linarith only [hbounds.1]
      · dsimp [centralParam] at hbounds
        linarith only [hbounds.2]
  have hgridInteriorNotBoundary (z : Interval × Interval)
      (hx : z.1.val ∈ Ioo (0:ℝ) 1) (hy : z.2.val ∈ Ioo (0:ℝ) 1) : ¬gridBoundary z := by
    as_aux_lemma =>
      rintro (h | h | h | h)
      · exact (ne_of_gt hx.1) (congrArg Subtype.val h)
      · exact (ne_of_lt hx.2) (congrArg Subtype.val h)
      · exact (ne_of_gt hy.1) (congrArg Subtype.val h)
      · exact (ne_of_lt hy.2) (congrArg Subtype.val h)
  have hmeshVertexInterior (k : Fin n × Fin n) (i : Fin 4)
      (hx₀ : (0:ℝ) < (k.1.val:ℝ)+(corners i).1.val)
      (hx₁ : (k.1.val:ℝ)+(corners i).1.val < (n:ℝ))
      (hy₀ : (0:ℝ) < (k.2.val:ℝ)+(corners i).2.val)
      (hy₁ : (k.2.val:ℝ)+(corners i).2.val < (n:ℝ)) :
      ¬gridBoundary (cellMap k (corners i)) := by
    as_aux_lemma =>
      apply hgridInteriorNotBoundary
      · exact ⟨div_pos hx₀ hnR,(div_lt_one hnR).mpr hx₁⟩
      · exact ⟨div_pos hy₀ hnR,(div_lt_one hnR).mpr hy₁⟩
  have hrelativeLowerTriangleNonzero (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      relativeVertexWidth k hk 0 ≠ 0 ∨ relativeVertexWidth k hk 1 ≠ 0 ∨
        relativeVertexWidth k hk 2 ≠ 0 := by
    as_aux_lemma =>
      have hnx : (k.1.val:ℝ) < n := by exact_mod_cast k.1.isLt
      have hny : (k.2.val:ℝ) < n := by exact_mod_cast k.2.isLt
      have hn₁ : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
      by_cases hx : k.1.val=0
      · by_cases hy : k.2.val=0
        · left
          have he : cellMap k (corners 0)=(0,0) := by
            apply Prod.ext <;> apply Subtype.ext <;>
              dsimp [cellMap,corners,ArcFinitePosition.intervalMeshParameter] <;> simp [hx,hy]
          have hb : gridBoundary (cellMap k (corners 0)) := by
            change (cellMap k (corners 0)).1=0 ∨ _
            exact Or.inl (congrArg Prod.fst he)
          rw [hrelativeBoundaryVertexFixed k hk 0 hb]
          intro hz
          have hhit : G (cellMap k (corners 0)) ∈ a.val.image := by
            rw [←hBsourceCoords k hk (corners 0)]
            exact (hBaxis _ _).mpr hz
          rw [he] at hhit
          exact hGinitialEndsAvoid 0 (Or.inl rfl) hhit
        · right; left
          apply hrelativeInteriorVertexNonzero k hk 1
          apply hmeshVertexInterior k 1
          · dsimp [corners]; simp [hx]
          · dsimp [corners]; simpa [hx] using hn₁
          · have hypos : (0:ℝ) < k.2.val := by exact_mod_cast (Nat.pos_of_ne_zero hy)
            simpa [corners] using hypos
          · simpa [corners] using hny
      · by_cases hy : k.2.val=0
        · right; right
          apply hrelativeInteriorVertexNonzero k hk 2
          apply hmeshVertexInterior k 2
          · have hxpos : (0:ℝ) < k.1.val := by exact_mod_cast (Nat.pos_of_ne_zero hx)
            simpa [corners] using hxpos
          · simpa [corners] using hnx
          · dsimp [corners]; simp [hy]
          · dsimp [corners]; simpa [hy] using hn₁
        · left
          apply hrelativeInteriorVertexNonzero k hk 0
          apply hmeshVertexInterior k 0
          · have hxpos : (0:ℝ) < k.1.val := by exact_mod_cast (Nat.pos_of_ne_zero hx)
            simpa [corners] using hxpos
          · simpa [corners] using hnx
          · have hypos : (0:ℝ) < k.2.val := by exact_mod_cast (Nat.pos_of_ne_zero hy)
            simpa [corners] using hypos
          · simpa [corners] using hny
  have hrelativeUpperTriangleNonzero (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      relativeVertexWidth k hk 1 ≠ 0 ∨ relativeVertexWidth k hk 2 ≠ 0 ∨
        relativeVertexWidth k hk 3 ≠ 0 := by
    as_aux_lemma =>
      have hnx : (k.1.val:ℝ) < n := by exact_mod_cast k.1.isLt
      have hny : (k.2.val:ℝ) < n := by exact_mod_cast k.2.isLt
      by_cases hx : k.1.val+1=n
      · by_cases hy : k.2.val+1=n
        · right; right
          have hnreal : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
          have hxc : (k.1.val:ℝ)+1=(n:ℝ) := by exact_mod_cast hx
          have hyc : (k.2.val:ℝ)+1=(n:ℝ) := by exact_mod_cast hy
          have he : cellMap k (corners 3)=(1,1) := by
            apply Prod.ext <;> apply Subtype.ext
            · change ((k.1.val:ℝ)+1)/(n:ℝ)=1
              rw [hxc,div_self hnreal]
            · change ((k.2.val:ℝ)+1)/(n:ℝ)=1
              rw [hyc,div_self hnreal]
          have hb : gridBoundary (cellMap k (corners 3)) :=
            Or.inr (Or.inl (congrArg Prod.fst he))
          rw [hrelativeBoundaryVertexFixed k hk 3 hb]
          exact hψtop ⟨cellMap k (corners 3),hchartBand (index k) hk
            (hcellSource k _ (mem_range_self _))⟩ (congrArg Prod.fst he)
        · right; left
          have hxpos : (0:ℝ) < k.1.val := by exact_mod_cast (show 0<k.1.val by omega)
          have hylt : (k.2.val:ℝ)+1<(n:ℝ) := by exact_mod_cast (show k.2.val+1<n by omega)
          apply hrelativeInteriorVertexNonzero k hk 2
          apply hmeshVertexInterior k 2
          · simpa [corners] using hxpos
          · simpa [corners] using hnx
          · dsimp [corners]
            positivity
          · simpa [corners] using hylt
      · by_cases hy : k.2.val+1=n
        · left
          have hypos : (0:ℝ) < k.2.val := by exact_mod_cast (show 0<k.2.val by omega)
          have hxlt : (k.1.val:ℝ)+1<(n:ℝ) := by exact_mod_cast (show k.1.val+1<n by omega)
          apply hrelativeInteriorVertexNonzero k hk 1
          apply hmeshVertexInterior k 1
          · dsimp [corners]
            positivity
          · simpa [corners] using hxlt
          · simpa [corners] using hypos
          · simpa [corners] using hny
        · right; right
          have hxlt : (k.1.val:ℝ)+1<(n:ℝ) := by exact_mod_cast (show k.1.val+1<n by omega)
          have hylt : (k.2.val:ℝ)+1<(n:ℝ) := by exact_mod_cast (show k.2.val+1<n by omega)
          apply hrelativeInteriorVertexNonzero k hk 3
          apply hmeshVertexInterior k 3
          · dsimp [corners]
            positivity
          · simpa [corners] using hxlt
          · dsimp [corners]
            positivity
          · simpa [corners] using hylt
  let relativeContactLower (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : ℝ × ℝ) : ℝ := (1-z.1-z.2)*relativeVertexWidth k hk 0 +
        z.1*relativeVertexWidth k hk 1 + z.2*relativeVertexWidth k hk 2
  let relativeContactUpper (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : ℝ × ℝ) : ℝ := (1-z.2)*relativeVertexWidth k hk 1 +
        (1-z.1)*relativeVertexWidth k hk 2 + (z.1+z.2-1)*relativeVertexWidth k hk 3
  have hactualRelativeCellAffineContact (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      (∃ z : ℝ × ℝ,relativeContactLower k hk z ≠ 0) ∧
      (∃ z : ℝ × ℝ,relativeContactUpper k hk z ≠ 0) ∧
      ∀ z : Interval × Interval,B (Qrelative k hk z) ∈ a.val.image →
        relativeContactLower k hk (z.1.val,z.2.val)=0 ∨
        relativeContactUpper k hk (z.1.val,z.2.val)=0 := by
    as_aux_lemma =>
      refine ⟨?_,?_,?_⟩
      · rcases hrelativeLowerTriangleNonzero k hk with h | h | h
        · exact ⟨(0,0),by simpa [relativeContactLower] using h⟩
        · exact ⟨(1,0),by simpa [relativeContactLower] using h⟩
        · exact ⟨(0,1),by simpa [relativeContactLower] using h⟩
      · rcases hrelativeUpperTriangleNonzero k hk with h | h | h
        · exact ⟨(1,0),by simpa [relativeContactUpper] using h⟩
        · exact ⟨(0,1),by simpa [relativeContactUpper] using h⟩
        · exact ⟨(1,1),by simpa [relativeContactUpper] using h⟩
      · intro z hz
        have hzero := (hBaxis _ _).mp hz
        change (∑ i,weights z i*relativeVertexWidth k hk i)=0 at hzero
        by_cases h : z.1.val+z.2.val ≤ 1
        · left
          exact (hweightsLowerTriangle z (relativeVertexWidth k hk) h).symm.trans hzero
        · right
          exact (hweightsUpperTriangle z (relativeVertexWidth k hk) (le_of_not_ge h)).symm.trans hzero
  have hQrelativeInterior (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (z : Interval × Interval) :
      (Qrelative k hk z).1.val ∈ Ioo (0:ℝ) 1 ∧
      (Qrelative k hk z).2.val ∈ Ioo (-1:ℝ) 1 :=
    ⟨(hQinterior k hk z).1,hrelativeQwidth k hk z⟩
  have hcellLeftZero (k : Fin n × Fin n) (hleft : k.1.val=0) (t : Interval) :
      (cellMap k (0,t)).1=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change ((k.1.val:ℝ)+(0:Interval).val)/(n:ℝ)=(0:Interval).val
      simp [hleft]
  have hcellBottomZero (k : Fin n × Fin n) (hbottom : k.2.val=0) (t : Interval) :
      (cellMap k (t,0)).2=0 := by
    as_aux_lemma =>
      apply Subtype.ext
      change ((k.2.val:ℝ)+(0:Interval).val)/(n:ℝ)=(0:Interval).val
      simp [hbottom]
  have hactualRelativeInitialTimeCell (k : Fin n × Fin n) (hk : label (index k)=some 0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t, D (0,t) = sourceCoords k hk (0,t)) ∧
        (∀ t, D (1,t) = Qrelative k hk (1,t)) ∧
        ∃ Hr : C(Interval × (Interval × Interval),S),
          (∀ z, Hr z ∉ (M.cover.branch : Set S)) ∧
          (∀ z, Hr (0,z) = G (cellMap k z)) ∧
          (∀ z, Hr (1,z) = B (D z)) ∧
          (∀ τ t, Hr (τ,(0,t)) = G (cellMap k (0,t))) ∧
          (∀ z,D z = blend (z.1,(sourceCoords k hk (0,z.2),Qrelative k hk (1,z.2)))) ∧
          (∀ z,Hr z = B (blend (z.1,(sourceCoords k hk z.2,D z.2)))) := by
    as_aux_lemma =>
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        ⟨sourceCoords k hk,hsourceCoordsContinuous k hk⟩
      let D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z => blend (z.1,(R (0,z.2),Qrelative k hk (1,z.2)))
        continuous_toFun := by fun_prop }
      have hDzero (t : Interval) : D (0,t) = R (0,t) := hblendZero _ _
      have hDone (t : Interval) : D (1,t) = Qrelative k hk (1,t) := hblendOne _ _
      have hDinterior (z : Interval × Interval) :
          (D z).1.val ∈ Ioo (0:ℝ) 1 ∧ (D z).2.val ∈ Ioo (-1:ℝ) 1 :=
        ⟨hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk _).1 (hQrelativeInterior k hk _).1 z.1,
         hblendIoo (-1) 1 _ _ (hsourceCoordsInterior k hk _).2 (hQrelativeInterior k hk _).2 z.1⟩
      let Hr : C(Interval × (Interval × Interval),S) := {
        toFun := fun z => B (blend (z.1,(R z.2,D z.2)))
        continuous_toFun := by exact hB.continuous.comp (by fun_prop) }
      have hBR (z : Interval × Interval) : B (R z) = G (cellMap k z) :=
        congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply _)
      refine ⟨D,hDzero,hDone,Hr,?_,?_,?_,?_,(fun _ => rfl),(fun _ => rfl)⟩
      · intro z
        have hlong := hblendIoo 0 1 _ _ (hsourceCoordsInterior k hk z.2).1
          (hDinterior z.2).1 z.1
        exact hBmarks _ _ (ne_of_gt hlong.1) (ne_of_lt hlong.2)
      · intro z
        change B (blend (0,(R z,D z))) = _
        rw [hblendZero]
        exact hBR z
      · intro z
        change B (blend (1,(R z,D z))) = _
        rw [hblendOne]
      · intro τ t
        change B (blend (τ,(R (0,t),D (0,t)))) = _
        rw [hDzero,hblendSame]
        exact hBR (0,t)
  have hactualRelativeFirstTimeRow (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (hk₀ : k.1.val=0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t,D (1,t)=Qrelative k hk (1,t)) ∧
        ∃ Hr : C(Interval × (Interval × Interval),S),
          (∀ z,Hr z ∉ (M.cover.branch : Set S)) ∧
          (∀ z,Hr (0,z)=G (cellMap k z)) ∧
          (∀ z,Hr (1,z)=B (D z)) ∧
          (∀ τ t,Hr (τ,(0,t)) = b.val.map
            (centralParam (ArcFinitePosition.intervalMeshParameter n hn k.2 t))) := by
    as_aux_lemma =>
      obtain ⟨D,hDzero,hDone,Hr,hmarks,hzero,hone,hrelative,hDformula,hHrformula⟩ := hactualRelativeInitialTimeCell k hk
      refine ⟨D,hDone,Hr,hmarks,hzero,hone,?_⟩
      intro τ t
      rw [hrelative,hcellInitialBoundary k hk₀ t]
  have hactualRelativeCornerCell (k : Fin n × Fin n) (hk : label (index k)=some 0)
      (hleft : k.1.val=0) (hbottom : k.2.val=0) :
      ∃ D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1),
        (∀ t,D (0,t)=sourceCoords k hk (0,t)) ∧
        (∀ t,D (t,0)=sourceCoords k hk (t,0)) ∧
        (∀ t,D (1,t)=Qrelative k hk (1,t)) ∧
        (∀ t,D (t,1)=Qrelative k hk (t,1)) ∧
        (∀ z,(D z).1.val ∈ Ioo (0:ℝ) 1 ∧ (D z).2.val ∈ Ioo (-1:ℝ) 1) := by
    as_aux_lemma =>
      let R : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) :=
        ⟨sourceCoords k hk,hsourceCoordsContinuous k hk⟩
      let r₁ : C(Interval × Interval,ℝ) := ⟨fun z => (R z).1.val,by fun_prop⟩
      let r₂ : C(Interval × Interval,ℝ) := ⟨fun z => (R z).2.val,by fun_prop⟩
      let q₁ : C(Interval × Interval,ℝ) := ⟨fun z => (Qrelative k hk z).1.val,by fun_prop⟩
      let q₂ : C(Interval × Interval,ℝ) := ⟨fun z => (Qrelative k hk z).2.val,by fun_prop⟩
      obtain ⟨clip₁,hclip₁,hclip₁r,hclip₁q⟩ := hcompactClip 0 1 r₁ q₁
        (fun z => (hsourceCoordsInterior k hk z).1) (fun z => (hQrelativeInterior k hk z).1)
      obtain ⟨clip₂,hclip₂,hclip₂r,hclip₂q⟩ := hcompactClip (-1) 1 r₂ q₂
        (fun z => (hsourceCoordsInterior k hk z).2) (fun z => (hQrelativeInterior k hk z).2)
      let coons (r q : C(Interval × Interval,ℝ)) : C(Interval × Interval,ℝ) := {
        toFun := fun z => q z + (1-z.1.val)*(r (0,z.2)-q (0,z.2)) +
          (1-z.2.val)*(r (z.1,0)-q (z.1,0))
        continuous_toFun := by fun_prop }
      let D : C(Interval × Interval,Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun z =>
          (⟨clip₁ (coons r₁ q₁ z),(hclip₁ _).1.le,(hclip₁ _).2.le⟩,
           ⟨clip₂ (coons r₂ q₂ z),(hclip₂ _).1.le,(hclip₂ _).2.le⟩)
        continuous_toFun := by fun_prop }
      have hc₀ : Qrelative k hk (0,0)=R (0,0) := hQrelativeBoundaryVertex k hk 0 (Or.inl (hcellLeftZero k hleft 0))
      have hc₁ : Qrelative k hk (1,0)=R (1,0) := hQrelativeBoundaryVertex k hk 1 (Or.inr (Or.inr (Or.inl (hcellBottomZero k hbottom 1))))
      have hc₂ : Qrelative k hk (0,1)=R (0,1) := hQrelativeBoundaryVertex k hk 2 (Or.inl (hcellLeftZero k hleft 1))
      have hcoonsEdges (r q : C(Interval × Interval,ℝ))
          (h₀ : q (0,0)=r (0,0)) (h₁ : q (1,0)=r (1,0))
          (h₂ : q (0,1)=r (0,1)) (t : Interval) :
          coons r q (0,t)=r (0,t) ∧ coons r q (t,0)=r (t,0) ∧
          coons r q (1,t)=q (1,t) ∧ coons r q (t,1)=q (t,1) := by
        dsimp [coons]
        simp only [h₀,h₁,h₂,sub_self,mul_zero,add_zero]
        constructor
        · ring
        constructor
        · ring
        constructor <;> ring
      have he₁ (t : Interval) := hcoonsEdges r₁ q₁
        (congrArg (fun z => z.1.val) hc₀) (congrArg (fun z => z.1.val) hc₁)
        (congrArg (fun z => z.1.val) hc₂) t
      have he₂ (t : Interval) := hcoonsEdges r₂ q₂
        (congrArg (fun z => z.2.val) hc₀) (congrArg (fun z => z.2.val) hc₁)
        (congrArg (fun z => z.2.val) hc₂) t
      refine ⟨D,?_,?_,?_,?_,fun z => ⟨hclip₁ _,hclip₂ _⟩⟩
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (0,t))=r₁ (0,t)
          rw [(he₁ t).1,hclip₁r]
        · change clip₂ (coons r₂ q₂ (0,t))=r₂ (0,t)
          rw [(he₂ t).1,hclip₂r]
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (t,0))=r₁ (t,0)
          rw [(he₁ t).2.1,hclip₁r]
        · change clip₂ (coons r₂ q₂ (t,0))=r₂ (t,0)
          rw [(he₂ t).2.1,hclip₂r]
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (1,t))=q₁ (1,t)
          rw [(he₁ t).2.2.1,hclip₁q]
        · change clip₂ (coons r₂ q₂ (1,t))=q₂ (1,t)
          rw [(he₂ t).2.2.1,hclip₂q]
      · intro t
        apply Prod.ext <;> apply Subtype.ext
        · change clip₁ (coons r₁ q₁ (t,1))=q₁ (t,1)
          rw [(he₁ t).2.2.2,hclip₁q]
        · change clip₂ (coons r₂ q₂ (t,1))=q₂ (t,1)
          rw [(he₂ t).2.2.2,hclip₂q]
  have hplanarStraighteningWithEnds (f : C(Interval,Plane)) (hf : IsEmbedding f) :
      ∃ T : Plane ≃ₜ Plane,T '' range f=sideTop ∧ T (f 0)=cornerNE ∧ T (f 1)=cornerNW := by
    as_aux_lemma =>
      let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
      have hfc : Continuous fc := f.continuous.comp continuous_projIcc
      have hfcval (t : Interval) : fc t=f t := by simp [fc,Set.projIcc_of_mem zero_le_one t.property]
      have hfi : InjOn fc (Icc (0:ℝ) 1) := by
        intro t ht u hu he
        have he' : f ⟨t,ht⟩=f ⟨u,hu⟩ := by simpa only [←hfcval] using he
        exact congrArg Subtype.val (hf.injective he')
      have hfcim : fc '' Icc (0:ℝ) 1=range f := by
        ext x
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨⟨t,ht⟩,by simp [fc,Set.projIcc_of_mem zero_le_one ht]⟩
        · rintro ⟨t,rfl⟩
          exact ⟨t,t.property,hfcval t⟩
      have hP : IsArcBetween (range f) (f 0) (f 1) :=
        ⟨fc,hfc.continuousOn,hfi,hfcim,hfcval 0,hfcval 1⟩
      obtain ⟨A,hA,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hP
      let Bm : Set Plane := sideLeft ∪ (sideBottom ∪ sideRight)
      have hBm : IsArcBetween Bm cornerNE cornerNW := isArcBetween_other_three_sides.reverse
      obtain ⟨e,heImage,he₀,he₁⟩ := exists_homeomorph_union_arcs_preserving_second hA hP hBm
        isArcBetween_sideTop hmeet other_three_sides_meet_top
      have hm : Bm ∪ sideTop=modelCurve := by
        dsimp [Bm]
        rw [modelCurve_eq_sides]
        ac_rfl
      let em : ↥(A ∪ range f) ≃ₜ ↥modelCurve := e.trans (Homeomorph.setCongr hm)
      obtain ⟨T,hT⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve em
      have heT (x : ↥(A ∪ range f)) : T x.val=(e x).val := hT x
      have hImage : T '' range f=sideTop := by
        ext y
        constructor
        · rintro ⟨x,hx,rfl⟩
          have hxJ : x ∈ A ∪ range f := Or.inr hx
          have hym : T x ∈ Subtype.val '' (e '' {z : ↥(A ∪ range f) | z.val ∈ range f}) :=
            ⟨e ⟨x,hxJ⟩,⟨⟨x,hxJ⟩,hx,rfl⟩,(heT ⟨x,hxJ⟩).symm⟩
          rw [heImage] at hym
          exact hym
        · intro hy
          have hym : y ∈ Subtype.val '' (e '' {z : ↥(A ∪ range f) | z.val ∈ range f}) :=
            heImage.symm ▸ hy
          obtain ⟨z,⟨x,hx,hxz⟩,hzy⟩ := hym
          refine ⟨x.val,hx,?_⟩
          rw [heT x]
          exact (congrArg Subtype.val hxz).trans hzy
      refine ⟨T,hImage,?_,?_⟩
      · calc
          T (f 0) = (e ⟨f 0,Or.inl hA.left_mem⟩).val := heT ⟨f 0,Or.inl hA.left_mem⟩
          _ = cornerNE := congrArg Subtype.val he₀
      · calc
          T (f 1) = (e ⟨f 1,Or.inl hA.right_mem⟩).val := heT ⟨f 1,Or.inl hA.right_mem⟩
          _ = cornerNW := congrArg Subtype.val he₁
  let oldEndpointChart := chartAt Plane (af 0)
  have holdChartPre : IsOpen (af ⁻¹' oldEndpointChart.source) :=
    oldEndpointChart.open_source.preimage af.continuous
  have holdChartZero : (0:Interval) ∈ af ⁻¹' oldEndpointChart.source := mem_chart_source _ _
  obtain ⟨endpointRadius,hendpointRadius,hendpointBall⟩ :=
    Metric.mem_nhds_iff.mp (holdChartPre.mem_nhds holdChartZero)
  let endpointLength : ℝ := min (endpointRadius/2) (1/2)
  have hendpointLength : 0 < endpointLength := by dsimp [endpointLength]; positivity
  have hendpointLengthOne : endpointLength < 1 := by
    as_aux_lemma =>
      have h := min_le_right (endpointRadius/2) (1/2:ℝ)
      dsimp [endpointLength]
      linarith only [h]
  have hendpointLengthRadius : endpointLength < endpointRadius := by
    as_aux_lemma =>
      have h := min_le_left (endpointRadius/2) (1/2:ℝ)
      dsimp [endpointLength]
      linarith only [h,hendpointRadius]
  let oldPrefixParam : C(Interval,Interval) := {
    toFun := fun t => ⟨endpointLength*t.val,
      mul_nonneg hendpointLength.le t.property.1,
      (mul_le_mul_of_nonneg_left t.property.2 hendpointLength.le).trans
        (by simpa using hendpointLengthOne.le)⟩
    continuous_toFun := by fun_prop }
  have holdPrefixParamInj : Function.Injective oldPrefixParam := by
    as_aux_lemma =>
      intro t u he
      exact Subtype.ext (mul_left_cancel₀ hendpointLength.ne' (congrArg Subtype.val he))
  let oldPrefix : C(Interval,S) := af.comp oldPrefixParam
  have holdPrefixEmbedding : IsEmbedding oldPrefix :=
    haf.comp ((oldPrefixParam.continuous.isClosedEmbedding holdPrefixParamInj).isEmbedding)
  have holdPrefixChart : range oldPrefix ⊆ oldEndpointChart.source := by
    as_aux_lemma =>
      rintro x ⟨t,rfl⟩
      apply hendpointBall
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |endpointLength*t.val-0| < endpointRadius
      rw [sub_zero,abs_of_nonneg (mul_nonneg hendpointLength.le t.property.1)]
      exact (mul_le_mul_of_nonneg_left t.property.2 hendpointLength.le).trans_lt
        (by simpa using hendpointLengthRadius)
  let planarOldPrefix : C(Interval,Plane) := {
    toFun := fun t => oldEndpointChart (oldPrefix t)
    continuous_toFun := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (oldEndpointChart.continuousAt (holdPrefixChart (mem_range_self t))).comp
        oldPrefix.continuous.continuousAt }
  have hplanarOldPrefixInj : Function.Injective planarOldPrefix := by
    as_aux_lemma =>
      intro t u he
      exact holdPrefixEmbedding.injective (oldEndpointChart.injOn
        (holdPrefixChart (mem_range_self t)) (holdPrefixChart (mem_range_self u)) he)
  have hplanarOldPrefixEmbedding : IsEmbedding planarOldPrefix :=
    (planarOldPrefix.continuous.isClosedEmbedding hplanarOldPrefixInj).isEmbedding
  obtain ⟨endpointStraightener,hendpointStraightened,hendpointStart,hendpointFinish⟩ :=
    hplanarStraighteningWithEnds planarOldPrefix hplanarOldPrefixEmbedding
  have holdPrefixZero : oldPrefix 0=af 0 := by
    as_aux_lemma =>
      change af (oldPrefixParam 0)=af 0
      congr 1
      apply Subtype.ext
      simp [oldPrefixParam]
  have hactualEndpointStart : endpointStraightener (oldEndpointChart (af 0))=cornerNE := by
    as_aux_lemma =>
      change endpointStraightener (oldEndpointChart (oldPrefix 0))=cornerNE at hendpointStart
      rwa [holdPrefixZero] at hendpointStart
  let oldPrefixCut : Interval := ⟨endpointLength/2,by
    constructor <;> linarith only [hendpointLength,hendpointLengthOne]⟩
  let oldEndpointRemainder : Set S := af '' Icc oldPrefixCut 1
  have holdEndpointRemainderClosed : IsClosed oldEndpointRemainder :=
    (isCompact_Icc.image af.continuous).isClosed
  have holdStartNotRemainder : af 0 ∉ oldEndpointRemainder := by
    as_aux_lemma =>
      rintro ⟨t,ht,he⟩
      have hzero : t=(0:Interval) := haf.injective he
      have htlow := ht.1
      rw [hzero] at htlow
      have hnum : endpointLength/2 ≤ (0:ℝ) := htlow
      linarith only [hnum,hendpointLength]
  let sharedMarkCarrier : Set S := ((M.cover.branch : Set S) \ {af 0})ᶜ
  have hsharedMarkCarrierOpen : IsOpen sharedMarkCarrier :=
    (M.cover.branch.finite_toSet.subset Set.diff_subset).isClosed.isOpen_compl
  have hsharedMarkCarrierStart : af 0 ∈ sharedMarkCarrier := by
    as_aux_lemma =>
      change af 0 ∉ ((M.cover.branch : Set S) \ {af 0})
      simp
  let sharedEndpointNeighborhood : Set S :=
    (oldEndpointChart.source \ oldEndpointRemainder) ∩ sharedMarkCarrier
  have hsharedEndpointNeighborhoodOpen : IsOpen sharedEndpointNeighborhood :=
    (oldEndpointChart.open_source.sdiff holdEndpointRemainderClosed).inter hsharedMarkCarrierOpen
  have hsharedEndpointNeighborhoodStart : af 0 ∈ sharedEndpointNeighborhood :=
    ⟨⟨mem_chart_source _ _,holdStartNotRemainder⟩,hsharedMarkCarrierStart⟩
  have hactualSharedEndpointAxis (x : S) (hx : x ∈ sharedEndpointNeighborhood) :
      x ∈ a.val.image ↔ endpointStraightener (oldEndpointChart x) ∈ sideTop := by
    as_aux_lemma =>
      constructor
      · intro ha
        obtain ⟨t,ht⟩ := hAFRange.symm ▸ ha
        have htcut : t < oldPrefixCut := by
          by_contra hn
          exact hx.1.2 ⟨t,⟨le_of_not_gt hn,t.property.2⟩,ht⟩
        have htlength : t.val ≤ endpointLength := by
          have hh : t.val < endpointLength/2 := htcut
          linarith only [hh,hendpointLength]
        let u : Interval := ⟨t.val/endpointLength,
          div_nonneg t.property.1 hendpointLength.le,(div_le_one hendpointLength).mpr htlength⟩
        have hparam : oldPrefixParam u=t := by
          apply Subtype.ext
          change endpointLength*(t.val/endpointLength)=t.val
          exact mul_div_cancel₀ _ hendpointLength.ne'
        have huprefix : oldPrefix u=x := by
          change af (oldPrefixParam u)=x
          rw [hparam]
          exact ht
        have him : endpointStraightener (oldEndpointChart x) ∈ endpointStraightener '' range planarOldPrefix :=
          ⟨planarOldPrefix u,mem_range_self u,by change endpointStraightener (oldEndpointChart (oldPrefix u))=_; rw [huprefix]⟩
        rwa [hendpointStraightened] at him
      · intro hxaxis
        have him : endpointStraightener (oldEndpointChart x) ∈ endpointStraightener '' range planarOldPrefix :=
          hendpointStraightened.symm ▸ hxaxis
        obtain ⟨y,⟨u,hu⟩,hy⟩ := him
        have he : oldEndpointChart (oldPrefix u)=oldEndpointChart x := by
          apply endpointStraightener.injective
          exact (congrArg endpointStraightener hu).trans hy
        have hpoint : oldPrefix u=x := oldEndpointChart.injOn
          (holdPrefixChart (mem_range_self u)) hx.1.1 he
        exact hAFRange ▸ ⟨oldPrefixParam u,hpoint⟩
  have hactualSharedEndpointUniformTail (c : Interval) (hc : c=0 ∨ c=1)
      (hshared : b.val.map c=af 0) :
      ∃ V : Set Interval,IsOpen V ∧ c ∈ V ∧
        ∀ τ t : Interval,t ∈ V → F (τ,t) ∈ sharedEndpointNeighborhood := by
    as_aux_lemma =>
      let N : Set (Interval × Interval) := F ⁻¹' sharedEndpointNeighborhood
      have hN : IsOpen N := hsharedEndpointNeighborhoodOpen.preimage F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {c} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have he : t=c := mem_singleton_iff.mp ht
        subst t
        change F (τ,c) ∈ sharedEndpointNeighborhood
        rcases hc with rfl | rfl
        · rw [(hFends τ).1,hshared]
          exact hsharedEndpointNeighborhoodStart
        · rw [(hFends τ).2,hshared]
          exact hsharedEndpointNeighborhoodStart
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      exact ⟨V,hV,hVc (mem_singleton c),fun τ t ht => hUV ⟨hUall (mem_univ τ),ht⟩⟩
  let sharedEndpointChart : OpenPartialHomeomorph S Plane :=
    (oldEndpointChart.transHomeomorph endpointStraightener).restr sharedEndpointNeighborhood
  have hsharedEndpointChartSource : sharedEndpointChart.source=sharedEndpointNeighborhood := by
    as_aux_lemma =>
      change oldEndpointChart.source ∩ interior sharedEndpointNeighborhood=sharedEndpointNeighborhood
      rw [hsharedEndpointNeighborhoodOpen.interior_eq]
      exact Set.inter_eq_right.mpr (fun _ hx => hx.1.1)
  have hsharedEndpointChartStart : sharedEndpointChart (af 0)=cornerNE := hactualEndpointStart
  have hsharedEndpointChartAxis (x : S) (hx : x ∈ sharedEndpointChart.source) :
      x ∈ a.val.image ↔ sharedEndpointChart x ∈ sideTop :=
    hactualSharedEndpointAxis x (hsharedEndpointChartSource ▸ hx)
  have hsharedCornerTarget : cornerNE ∈ sharedEndpointChart.target := by
    as_aux_lemma =>
      rw [←hsharedEndpointChartStart]
      apply sharedEndpointChart.map_source
      exact hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart
  obtain ⟨sharedChartRadius,hsharedChartRadius,hsharedChartBall⟩ :=
    Metric.isOpen_iff.mp sharedEndpointChart.open_target cornerNE hsharedCornerTarget
  let sharedCornerPatch : Set S := sharedEndpointChart.source ∩
    sharedEndpointChart ⁻¹' Metric.ball cornerNE sharedChartRadius
  have hsharedCornerPatchOpen : IsOpen sharedCornerPatch :=
    sharedEndpointChart.isOpen_inter_preimage Metric.isOpen_ball
  have hsharedCornerPatchStart : af 0 ∈ sharedCornerPatch := by
    refine ⟨hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart,?_⟩
    change dist (sharedEndpointChart (af 0)) cornerNE < sharedChartRadius
    rw [hsharedEndpointChartStart,dist_self]
    exact hsharedChartRadius
  have hactualSharedMarkSmallChartTail (c : Interval) (hc : c=0 ∨ c=1)
      (hshared : b.val.map c=af 0) :
      ∃ V : Set Interval,IsOpen V ∧ c ∈ V ∧
        ∀ τ t : Interval,t ∈ V →
          F (τ,t) ∈ sharedEndpointChart.source ∧
          sharedEndpointChart (F (τ,t)) ∈ Metric.ball cornerNE sharedChartRadius ∧
          (t ≠ 0 → t ≠ 1 → sharedEndpointChart (F (τ,t)) ≠ cornerNE) := by
    as_aux_lemma =>
      let N : Set (Interval × Interval) := F ⁻¹' sharedCornerPatch
      have hN : IsOpen N := hsharedCornerPatchOpen.preimage F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {c} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have he : t=c := mem_singleton_iff.mp ht
        subst t
        change F (τ,c) ∈ sharedCornerPatch
        rcases hc with rfl | rfl
        · rw [(hFends τ).1,hshared]
          exact hsharedCornerPatchStart
        · rw [(hFends τ).2,hshared]
          exact hsharedCornerPatchStart
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      refine ⟨V,hV,hVc (mem_singleton c),?_⟩
      intro τ t ht
      have hpatch : F (τ,t) ∈ sharedCornerPatch := hUV ⟨hUall (mem_univ τ),ht⟩
      refine ⟨hpatch.1,hpatch.2,?_⟩
      intro ht₀ ht₁ he
      have hpoint : F (τ,t)=af 0 := sharedEndpointChart.injOn hpatch.1
        (hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart)
        (he.trans hsharedEndpointChartStart.symm)
      exact hFmarks τ t ht₀ ht₁ (hpoint.symm ▸ hAFStartMarked)
  have hactualSharedStartLogarithmicTail (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (_hd : 0<d) (hd1 : d<1),
        ∃ L : C(Interval × Set.Ioc (0:ℝ) d,ℂ),
          ∀ z : Interval × Set.Ioc (0:ℝ) d,
            Complex.exp (L z) = ArcFinitePosition.planeComplexLinearEquiv
              (sharedEndpointChart (F (z.1,⟨z.2.val,
                z.2.property.1.le,z.2.property.2.trans hd1.le⟩))-cornerNE) := by
    as_aux_lemma =>
      obtain ⟨V,hV,hVzero,hVtail⟩ := hactualSharedMarkSmallChartTail 0 (Or.inl rfl) hshared
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hVzero)
      let d : ℝ := min (r/2) (1/2)
      have hd : 0<d := by dsimp [d]; positivity
      have hd1 : d<1 := by
        have h := min_le_right (r/2) (1/2:ℝ)
        dsimp [d]
        linarith only [h]
      have hdr : d<r := by
        have h := min_le_left (r/2) (1/2:ℝ)
        dsimp [d]
        linarith only [h,hr]
      let Tail := Set.Ioc (0:ℝ) d
      letI : ContractibleSpace Tail := (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).contractibleSpace
        ⟨d,hd,le_rfl⟩
      letI : LocallyPathConnectedSpace Tail := (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).locallyPathConnectedSpace
      letI : ContractibleSpace Interval := (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace
        ⟨0,by norm_num⟩
      letI : LocallyPathConnectedSpace Interval := (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
      let param : C(Tail,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩,
        by fun_prop⟩
      have hparamV (t : Tail) : param t ∈ V := by
        apply hball
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |t.val-0|<r
        rw [sub_zero,abs_of_pos t.property.1]
        exact t.property.2.trans_lt hdr
      let tailSource : C(Interval × Tail,S) := {
        toFun := fun z => F (z.1,param z.2)
        continuous_toFun := by fun_prop }
      have htailChart (z : Interval × Tail) : tailSource z ∈ sharedEndpointChart.source :=
        (hVtail z.1 (param z.2) (hparamV z.2)).1
      let g : C(Interval × Tail,ℂ) := {
        toFun := fun z => ArcFinitePosition.planeComplexLinearEquiv
          (sharedEndpointChart (tailSource z)-cornerNE)
        continuous_toFun := by
          apply ArcFinitePosition.planeComplexLinearEquiv.continuous.comp
          apply Continuous.sub ?_ continuous_const
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedEndpointChart.continuousAt (htailChart z)).comp
            tailSource.continuous.continuousAt }
      have hgzero (z : Interval × Tail) : g z ≠ 0 := by
        intro he
        have hplane : sharedEndpointChart (tailSource z)-cornerNE=0 :=
          ArcFinitePosition.planeComplexLinearEquiv.injective (he.trans
            ArcFinitePosition.planeComplexLinearEquiv.map_zero.symm)
        have hpoint : sharedEndpointChart (tailSource z)=cornerNE := sub_eq_zero.mp hplane
        have ht₀ : param z.2 ≠ (0:Interval) := by
          intro he
          exact (ne_of_gt z.2.property.1) (congrArg Subtype.val he)
        have ht₁ : param z.2 ≠ (1:Interval) := by
          intro he
          exact (ne_of_lt (z.2.property.2.trans_lt hd1)) (congrArg Subtype.val he)
        exact (hVtail z.1 (param z.2) (hparamV z.2)).2.2 ht₀ ht₁ hpoint
      let gNonzero : C(Interval × Tail,{z : ℂ // z ≠ 0}) :=
        ⟨fun z => ⟨g z,hgzero z⟩,g.continuous.subtype_mk _⟩
      let base : Interval × Tail := (0,⟨d,hd,le_rfl⟩)
      have hbase : (⟨Complex.exp (Complex.log (g base)),Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) =
          gNonzero base := Subtype.ext (Complex.exp_log (hgzero base))
      obtain ⟨L,⟨hLbase,hL⟩,hLunique⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
        gNonzero base (Complex.log (g base)) hbase
      refine ⟨d,hd,hd1,L,?_⟩
      intro z
      exact congrArg Subtype.val (congrFun hL z)
  have hactualSharedStartPuncturedInterpolation
      (hshared : b.val.map 0 = af 0) :
      ∃ (d : ℝ) (_hd : 0 < d) (hd1 : d < 1),
      ∃ L : C(Interval × Ioc (0:ℝ) d, ℂ),
      ∃ H : C(Interval × (Interval × Ioc (0:ℝ) d), ℂ),
        (∀ z, H z ≠ 0) ∧
        (∀ z, H (0,z) = ArcFinitePosition.planeComplexLinearEquiv
          (sharedEndpointChart (F (z.1,
            ⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩))-cornerNE)) ∧
        (∀ z, H (1,z) = (z.2.val/d:ℂ) *
          ArcFinitePosition.planeComplexLinearEquiv
            (sharedEndpointChart (F (z.1,⟨d,_hd.le,hd1.le⟩))-cornerNE)) ∧
        (∀ z, ‖H z‖ ≤ max
          ‖ArcFinitePosition.planeComplexLinearEquiv
            (sharedEndpointChart (F (z.2.1,
              ⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))-cornerNE)‖
          ((z.2.2.val/d) * ‖ArcFinitePosition.planeComplexLinearEquiv
            (sharedEndpointChart (F (z.2.1,⟨d,_hd.le,hd1.le⟩))-cornerNE)‖)) ∧
        (∀ τ η, H (η,(τ,⟨d,_hd,le_rfl⟩)) =
          ArcFinitePosition.planeComplexLinearEquiv
            (sharedEndpointChart (F (τ,⟨d,_hd.le,hd1.le⟩))-cornerNE)) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,L,hL⟩ := hactualSharedStartLogarithmicTail hshared
      let outer : Ioc (0:ℝ) d := ⟨d,hd,le_rfl⟩
      let H : C(Interval × (Interval × Ioc (0:ℝ) d),ℂ) := {
        toFun := fun z => Complex.exp
          ((1-(z.1.val:ℂ))*L z.2 + (z.1.val:ℂ)*
            (L (z.2.1,outer) + (Real.log (z.2.2.val/d):ℂ)))
        continuous_toFun := by
          apply Complex.continuous_exp.comp
          apply Continuous.add
          · fun_prop
          · apply Continuous.mul
            · fun_prop
            · apply Continuous.add
              · fun_prop
              · apply continuous_iff_continuousAt.mpr
                intro z
                apply Complex.continuous_ofReal.continuousAt.comp
                exact ContinuousAt.comp
                  (f := fun w : Interval × (Interval × Ioc (0:ℝ) d) => w.2.2.val/d)
                  (x := z) (Real.continuousAt_log
                    (ne_of_gt (div_pos z.2.2.property.1 hd))) (by fun_prop) }
      refine ⟨d,hd,hd1,L,H,?_,?_,?_,?_,?_⟩
      · intro z
        exact Complex.exp_ne_zero _
      · intro z
        change Complex.exp ((1-(0:ℂ))*L z + (0:ℂ)*_) = _
        simpa using hL z
      · intro z
        change Complex.exp ((1-(1:ℂ))*L z + (1:ℂ)*
          (L (z.1,outer)+(Real.log (z.2.val/d):ℂ))) = _
        simp only [sub_self,zero_mul,one_mul,zero_add]
        rw [Complex.exp_add,← Complex.ofReal_exp,Real.exp_log (div_pos z.2.property.1 hd),
          hL (z.1,outer)]
        simp only [Complex.ofReal_div]
        exact mul_comm _ _
      · intro z
        let A : ℂ := L z.2
        let B : ℂ := L (z.2.1,outer)+(Real.log (z.2.2.val/d):ℂ)
        let m : ℝ := max A.re B.re
        have hlinear : (1-z.1.val)*A.re+z.1.val*B.re ≤ m := by
          calc
            _ ≤ (1-z.1.val)*m+z.1.val*m := add_le_add
              (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr z.1.property.2))
              (mul_le_mul_of_nonneg_left (le_max_right _ _) z.1.property.1)
            _ = m := by ring
        have hnorm : ‖H z‖ ≤ max ‖Complex.exp A‖ ‖Complex.exp B‖ := by
          have heq : ‖H z‖ = Real.exp ((1-z.1.val)*A.re+z.1.val*B.re) := by
            simp [H,A,B,Complex.norm_exp]
          rw [heq,Complex.norm_exp,Complex.norm_exp]
          rcases le_total A.re B.re with hab | hba
          · rw [max_eq_right (Real.exp_le_exp.mpr hab)]
            exact Real.exp_le_exp.mpr (hlinear.trans_eq (max_eq_right hab))
          · rw [max_eq_left (Real.exp_le_exp.mpr hba)]
            exact Real.exp_le_exp.mpr (hlinear.trans_eq (max_eq_left hba))
        have hBnorm : ‖Complex.exp B‖ = (z.2.2.val/d)*‖Complex.exp (L (z.2.1,outer))‖ := by
          rw [Complex.norm_exp]
          change Real.exp ((L (z.2.1,outer)).re+Real.log (z.2.2.val/d)) = _
          rw [Real.exp_add,Real.exp_log (div_pos z.2.2.property.1 hd),Complex.norm_exp]
          exact mul_comm _ _
        rw [hBnorm] at hnorm
        simpa only [A,hL] using hnorm
      · intro τ η
        have hdd : (d/d:ℝ)=1 := div_self (ne_of_gt hd)
        change Complex.exp ((1-(η.val:ℂ))*L (τ,outer) +
          (η.val:ℂ)*(L (τ,outer)+(Real.log (d/d):ℂ))) = _
        rw [hdd]
        simp only [Real.log_one,Complex.ofReal_zero,add_zero]
        have he : (1-(η.val:ℂ))*L (τ,outer)+(η.val:ℂ)*L (τ,outer)=L (τ,outer) := by ring
        rw [he]
        exact hL (τ,outer)
  let sharedComplexFrame : Plane ≃ₜ ℂ :=
    (Homeomorph.addRight (-cornerNE)).trans
      ArcFinitePosition.planeComplexLinearEquiv.toHomeomorph
  let sharedComplexChart : OpenPartialHomeomorph S ℂ :=
    sharedEndpointChart.transHomeomorph sharedComplexFrame
  have hsharedComplexSource : sharedComplexChart.source=sharedEndpointChart.source := rfl
  have hsharedComplexFormula (x : S) : sharedComplexChart x =
      ArcFinitePosition.planeComplexLinearEquiv (sharedEndpointChart x-cornerNE) := by
    as_aux_lemma =>
      change ArcFinitePosition.planeComplexLinearEquiv (sharedEndpointChart x+(-cornerNE))=_
      rw [sub_eq_add_neg]
  have hsharedComplexStart : sharedComplexChart (af 0)=0 := by
    as_aux_lemma =>
      rw [hsharedComplexFormula,hsharedEndpointChartStart,sub_self,map_zero]
  have hsharedComplexTarget : (0:ℂ) ∈ sharedComplexChart.target := by
    as_aux_lemma =>
      rw [←hsharedComplexStart]
      apply sharedComplexChart.map_source
      exact hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart
  obtain ⟨complexRadius,hcomplexRadius,hcomplexBall⟩ :=
    Metric.isOpen_iff.mp sharedComplexChart.open_target 0 hsharedComplexTarget
  let sharedComplexPatch : Set S := sharedComplexChart.source ∩
    sharedComplexChart ⁻¹' Metric.ball 0 complexRadius
  have hsharedComplexPatchOpen : IsOpen sharedComplexPatch :=
    sharedComplexChart.isOpen_inter_preimage Metric.isOpen_ball
  have hsharedComplexPatchStart : af 0 ∈ sharedComplexPatch := by
    refine ⟨hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart,?_⟩
    change dist (sharedComplexChart (af 0)) 0 < complexRadius
    rw [hsharedComplexStart,dist_self]
    exact hcomplexRadius
  have hactualSharedComplexSmallTail (hshared : b.val.map 0=af 0) :
      ∃ V : Set Interval,IsOpen V ∧ (0:Interval) ∈ V ∧
        ∀ τ t : Interval,t ∈ V →
          F (τ,t) ∈ sharedComplexChart.source ∧
          ‖sharedComplexChart (F (τ,t))‖ < complexRadius := by
    as_aux_lemma =>
      let N : Set (Interval × Interval) := F ⁻¹' sharedComplexPatch
      have hN : IsOpen N := hsharedComplexPatchOpen.preimage F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {(0:Interval)} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have he : t=(0:Interval) := mem_singleton_iff.mp ht
        subst t
        change F (τ,0) ∈ sharedComplexPatch
        rw [(hFends τ).1,hshared]
        exact hsharedComplexPatchStart
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      refine ⟨V,hV,hVc (mem_singleton 0),?_⟩
      intro τ t ht
      have hx : F (τ,t) ∈ sharedComplexPatch := hUV ⟨hUall (mem_univ τ),ht⟩
      exact ⟨hx.1,by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.2⟩
  have hactualSharedStartChartContainedInterpolation (hshared : b.val.map 0=af 0) :
      ∃ (d₀ : ℝ) (hd₀ : 0<d₀) (hd₀1 : d₀<1),
      ∃ H : C(Interval × (Interval × Ioc (0:ℝ) d₀),ℂ),
      ∃ (d : ℝ), 0<d ∧ d≤d₀ ∧
        (∀ z,z.2.2.val≤d → H z ∈ sharedComplexChart.target ∧ H z≠0 ∧
          F (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,
            z.2.2.property.2.trans hd₀1.le⟩) ∈ sharedComplexChart.source) ∧
        (∀ z, ‖H z‖ ≤ max
          ‖sharedComplexChart (F (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,
            z.2.2.property.2.trans hd₀1.le⟩))‖
          ((z.2.2.val/d₀)*‖sharedComplexChart (F (z.2.1,⟨d₀,hd₀.le,hd₀1.le⟩))‖)) ∧
        (∀ z,H (0,z)=sharedComplexChart
          (F (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd₀1.le⟩))) ∧
        (∀ z,H (1,z)=(z.2.val/d₀:ℂ)*sharedComplexChart
          (F (z.1,⟨d₀,hd₀.le,hd₀1.le⟩))) := by
    as_aux_lemma =>
      obtain ⟨d₀,hd₀,hd₀1,L,H,hHnonzero,hHinitial,hHterminal,hHnorm,hHouter⟩ :=
        hactualSharedStartPuncturedInterpolation hshared
      let outer : Ioc (0:ℝ) d₀ := ⟨d₀,hd₀,le_rfl⟩
      let outerNorm : C(Interval,ℝ) := {
        toFun := fun τ => ‖H (1,(τ,outer))‖
        continuous_toFun := by fun_prop }
      obtain ⟨m,hm,hmax⟩ := (isCompact_range outerNorm.continuous).exists_isGreatest
        ⟨outerNorm 0,mem_range_self 0⟩
      have hmnonneg : 0 ≤ m := (norm_nonneg (H (1,((0:Interval),outer)))).trans
        (hmax (mem_range_self (0:Interval)))
      have hmpos : 0 < m+1 := by linarith only [hmnonneg]
      have houterBound (τ : Interval) :
          ‖sharedComplexChart (F (τ,⟨d₀,hd₀.le,hd₀1.le⟩))‖ ≤ m+1 := by
        have hsource : H (1,(τ,outer))=
            sharedComplexChart (F (τ,⟨d₀,hd₀.le,hd₀1.le⟩)) := by
          have hfirst := hHterminal (τ,outer)
          change H (1,(τ,outer))=(d₀:ℂ)/(d₀:ℂ)*_ at hfirst
          rw [div_self (by exact_mod_cast ne_of_gt hd₀),one_mul] at hfirst
          simpa only [hsharedComplexFormula] using hfirst
        rw [←hsource]
        exact (hmax (mem_range_self τ)).trans (le_add_of_nonneg_right zero_le_one)
      obtain ⟨V,hV,hVzero,hVtail⟩ := hactualSharedComplexSmallTail hshared
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hVzero)
      let d : ℝ := min d₀ (min (r/2) (complexRadius*d₀/(2*(m+1))))
      have hd : 0<d := by dsimp [d]; positivity
      have hdd₀ : d≤d₀ := min_le_left _ _
      have hdr : d<r := by
        have h : d ≤ r/2 := (min_le_right d₀ _).trans (min_le_left (r/2) _)
        dsimp [d]
        linarith only [h,hr]
      have hdscale : d*(m+1) ≤ complexRadius*d₀/2 := by
        have hh : d ≤ complexRadius*d₀/(2*(m+1)) :=
          (min_le_right d₀ _).trans (min_le_right (r/2) _)
        have hh' := (le_div_iff₀ (by positivity : 0<2*(m+1))).mp hh
        nlinarith only [hh']
      refine ⟨d₀,hd₀,hd₀1,H,d,hd,hdd₀,?_,?_,?_,?_⟩
      · intro z hz
        have hparamV : (⟨z.2.2.val,z.2.2.property.1.le,
            z.2.2.property.2.trans hd₀1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.2.property.1]
          exact hz.trans_lt hdr
        have hsmall := (hVtail z.2.1 _ hparamV).2
        have hradial : (z.2.2.val/d₀)*
            ‖sharedComplexChart (F (z.2.1,⟨d₀,hd₀.le,hd₀1.le⟩))‖ < complexRadius := by
          calc
            _ ≤ (z.2.2.val/d₀)*(m+1) := mul_le_mul_of_nonneg_left
              (houterBound z.2.1) (div_nonneg z.2.2.property.1.le hd₀.le)
            _ = z.2.2.val*(m+1)/d₀ := by ring
            _ ≤ (complexRadius*d₀/2)/d₀ := (div_le_div_iff_of_pos_right hd₀).mpr
              ((mul_le_mul_of_nonneg_right hz hmpos.le).trans hdscale)
            _ = complexRadius/2 := by field_simp [ne_of_gt hd₀]
            _ < complexRadius := by linarith only [hcomplexRadius]
        have hnormsmall : ‖H z‖ < complexRadius :=
          (hHnorm z).trans_lt (max_lt
            (by simpa only [hsharedComplexFormula] using hsmall)
            (by simpa only [hsharedComplexFormula] using hradial))
        refine ⟨hcomplexBall ?_,hHnonzero z,(hVtail z.2.1 _ hparamV).1⟩
        simpa only [Metric.mem_ball,dist_zero_right] using hnormsmall
      · intro z
        simpa only [hsharedComplexFormula] using hHnorm z
      · intro z
        simpa only [hsharedComplexFormula] using hHinitial z
      · intro z
        simpa only [hsharedComplexFormula] using hHterminal z
  have hactualSharedStartPuncturedSurfacePatch (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ B : C(Interval,ℝ), ∃ K : C(Interval × (Interval × Ioc (0:ℝ) d),S),
        (∀ z,K z ∈ sharedComplexChart.source) ∧
        (∀ z,‖sharedComplexChart (K z)‖ ≤
          ‖sharedComplexChart (F (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,
            z.2.2.property.2.trans hd1.le⟩))‖ + z.2.2.val*B z.2.1) ∧
        (∀ z,K z ∉ (M.cover.branch : Set S)) ∧
        (∀ z,K (0,z)=F
          (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩)) ∧
        (∀ η τ,K (η,(τ,⟨d,hd,le_rfl⟩))=F (τ,⟨d,hd.le,hd1.le⟩)) := by
    as_aux_lemma =>
      obtain ⟨d₀,hd₀,hd₀1,H,d,hd,hdd₀,hHrange,hHnorm,hHinitial,hHterminal⟩ :=
        hactualSharedStartChartContainedInterpolation hshared
      have hd1 : d<1 := hdd₀.trans_lt hd₀1
      let Tail := Ioc (0:ℝ) d
      let cutoff : C(Tail,Interval) := {
        toFun := fun t => ⟨min 1 (2*(d-t.val)/d),by
          constructor
          · exact le_min zero_le_one (div_nonneg
              (mul_nonneg (by norm_num) (sub_nonneg.mpr t.property.2)) hd.le)
          · exact min_le_left _ _⟩
        continuous_toFun := by fun_prop }
      have hcutoffOuter : cutoff ⟨d,hd,le_rfl⟩=0 := by
        apply Subtype.ext
        simp [cutoff]
      let input : C(Interval × (Interval × Tail),Interval × (Interval × Ioc (0:ℝ) d₀)) := {
        toFun := fun z => (⟨z.1.val*(cutoff z.2.2).val,
          mul_nonneg z.1.property.1 (cutoff z.2.2).property.1,
          (mul_le_mul_of_nonneg_left (cutoff z.2.2).property.2 z.1.property.1).trans
            (by simpa only [mul_one] using z.1.property.2)⟩,
          (z.2.1,⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hdd₀⟩))
        continuous_toFun := by fun_prop }
      let HC : C(Interval × (Interval × Tail),ℂ) := H.comp input
      have hHCtarget (z : Interval × (Interval × Tail)) : HC z ∈ sharedComplexChart.target :=
        (hHrange (input z) z.2.2.property.2).1
      have hHCnonzero (z : Interval × (Interval × Tail)) : HC z≠0 :=
        (hHrange (input z) z.2.2.property.2).2.1
      let K : C(Interval × (Interval × Tail),S) := {
        toFun := fun z => sharedComplexChart.symm (HC z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.symm.continuousAt (hHCtarget z)).comp
            HC.continuous.continuousAt }
      have hKchart (z : Interval × (Interval × Tail)) : sharedComplexChart (K z)=HC z :=
        sharedComplexChart.right_inv (hHCtarget z)
      have hKsource (z : Interval × (Interval × Tail)) : K z ∈ sharedComplexChart.source :=
        sharedComplexChart.map_target (hHCtarget z)
      have hKne (z : Interval × (Interval × Tail)) : K z≠af 0 := by
        intro he
        exact hHCnonzero z ((hKchart z).symm.trans
          ((congrArg sharedComplexChart he).trans hsharedComplexStart))
      have hinputZero (z : Interval × Tail) : (input (0,z)).1=0 := by
        apply Subtype.ext
        simp [input]
      have hinputOuter (η τ : Interval) : (input (η,(τ,⟨d,hd,le_rfl⟩))).1=0 := by
        apply Subtype.ext
        change η.val*(cutoff ⟨d,hd,le_rfl⟩).val=0
        rw [hcutoffOuter]
        simp
      have hKinitial (z : Interval × Tail) : K (0,z)=F
          (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩) := by
        apply sharedComplexChart.injOn (hKsource (0,z))
          (hHrange (input (0,z)) z.2.property.2).2.2
        rw [hKchart]
        change H (input (0,z))=_
        rw [show input (0,z)=(0,(input (0,z)).2) from Prod.ext (hinputZero z) rfl,
          hHinitial]
      let outer : Ioc (0:ℝ) d₀ := ⟨d₀,hd₀,le_rfl⟩
      let B : C(Interval,ℝ) := {
        toFun := fun τ => ‖H (1,(τ,outer))‖/d₀
        continuous_toFun := by fun_prop }
      have hBformula (τ : Interval) : B τ=
          ‖sharedComplexChart (F (τ,⟨d₀,hd₀.le,hd₀1.le⟩))‖/d₀ := by
        have he := hHterminal (τ,outer)
        have hratio : (d₀:ℂ)/(d₀:ℂ)=1 := div_self (by exact_mod_cast ne_of_gt hd₀)
        change H (1,(τ,outer))=(d₀:ℂ)/(d₀:ℂ)*_ at he
        rw [hratio,one_mul] at he
        change ‖H (1,(τ,outer))‖/d₀=_
        rw [he]
      refine ⟨d,hd,hd1,B,K,hKsource,?_,?_,hKinitial,?_⟩
      · intro z
        rw [hKchart,hBformula]
        have hb := hHnorm (input z)
        have hnonneg : 0 ≤ (z.2.2.val/d₀)*
            ‖sharedComplexChart (F (z.2.1,⟨d₀,hd₀.le,hd₀1.le⟩))‖ :=
          mul_nonneg (div_nonneg z.2.2.property.1.le hd₀.le) (norm_nonneg _)
        have he : z.2.2.val*
            (‖sharedComplexChart (F (z.2.1,⟨d₀,hd₀.le,hd₀1.le⟩))‖/d₀)=
            (z.2.2.val/d₀)*‖sharedComplexChart (F (z.2.1,⟨d₀,hd₀.le,hd₀1.le⟩))‖ := by ring
        rw [he]
        exact hb.trans (max_le (le_add_of_nonneg_right hnonneg)
          (le_add_of_nonneg_left (norm_nonneg _)))
      · intro z hm
        have hcarrier : K z ∈ sharedMarkCarrier :=
          (hsharedEndpointChartSource ▸ hKsource z).2
        apply hcarrier
        exact ⟨hm,by simpa only [mem_singleton_iff] using hKne z⟩
      · intro η τ
        apply sharedComplexChart.injOn (hKsource (η,(τ,⟨d,hd,le_rfl⟩)))
          (hHrange (input (η,(τ,⟨d,hd,le_rfl⟩))) le_rfl).2.2
        rw [hKchart]
        change H (input (η,(τ,⟨d,hd,le_rfl⟩)))=_
        rw [show input (η,(τ,⟨d,hd,le_rfl⟩))=
          (0,(input (η,(τ,⟨d,hd,le_rfl⟩))).2) from
            Prod.ext (hinputOuter η τ) rfl,hHinitial]
  have hactualSharedStartMarkedPointExtension (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ K : C(Interval × (Interval × Icc (0:ℝ) d),S),
        (∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0) ∧
        (∀ z,0<z.2.2.val → K z ∉ (M.cover.branch : Set S)) ∧
        (∀ z,K (0,z)=F
          (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩)) ∧
        (∀ η τ,K (η,(τ,⟨d,hd.le,le_rfl⟩))=F (τ,⟨d,hd.le,hd1.le⟩)) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,B,K,hKsource,hKnorm,hKmarks,hKinitial,hKouter⟩ :=
        hactualSharedStartPuncturedSurfacePatch hshared
      let Tail := Ioc (0:ℝ) d
      let ClosedTail := Icc (0:ℝ) d
      let X := Interval × (Interval × ClosedTail)
      let PC : C(Interval × (Interval × Tail),ℂ) := {
        toFun := fun z => sharedComplexChart (K z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.continuousAt (hKsource z)).comp K.continuous.continuousAt }
      let source : C(X,S) := {
        toFun := fun z => F (z.2.1,⟨z.2.2.val,z.2.2.property.1,
          z.2.2.property.2.trans hd1.le⟩)
        continuous_toFun := by fun_prop }
      have hsourceChart (z : X) : source z ∈ sharedComplexChart.source := by
        by_cases ht : 0<z.2.2.val
        · let t : Tail := ⟨z.2.2.val,ht,z.2.2.property.2⟩
          have he := hKinitial (z.2.1,t)
          exact he ▸ hKsource (0,(z.2.1,t))
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          have hparam : (⟨z.2.2.val,z.2.2.property.1,
              z.2.2.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext he
          change F (z.2.1,_) ∈ sharedComplexChart.source
          rw [hparam,(hFends z.2.1).1,hshared]
          exact hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart
      let sourceC : C(X,ℂ) := {
        toFun := fun z => sharedComplexChart (source z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.continuousAt (hsourceChart z)).comp source.continuous.continuousAt }
      let majorant : C(X,ℝ) := {
        toFun := fun z => ‖sourceC z‖+z.2.2.val*B z.2.1
        continuous_toFun := by fun_prop }
      let extPC : X → ℂ := fun z => if ht : 0<z.2.2.val then
        PC (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)) else 0
      have hnormBound (z : X) : ‖extPC z‖ ≤ majorant z := by
        by_cases ht : 0<z.2.2.val
        · dsimp only [extPC]
          rw [dif_pos ht]
          exact hKnorm (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩))
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          simp only [extPC,dif_neg ht,norm_zero,majorant,ContinuousMap.coe_mk,he,
            zero_mul,add_zero]
          exact norm_nonneg _
      have hzeroValues (z : X) (hz : z.2.2.val=0) : extPC z=0 ∧ majorant z=0 := by
        have hparam : (⟨z.2.2.val,z.2.2.property.1,
            z.2.2.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext hz
        constructor
        · simp only [extPC,hz,lt_self_iff_false,dif_neg,not_false_eq_true]
        · change ‖sharedComplexChart (F (z.2.1,_))‖+z.2.2.val*B z.2.1=0
          rw [hparam,(hFends z.2.1).1,hshared,hsharedComplexStart,norm_zero,hz]
          ring
      have hextContinuous : Continuous extPC := by
        apply continuous_iff_continuousAt.mpr
        intro z
        by_cases hz : 0<z.2.2.val
        · let a : ℝ := z.2.2.val/2
          have ha : 0<a := by dsimp [a]; positivity
          have haz : a<z.2.2.val := by dsimp [a]; linarith only [hz]
          have had : a≤d := haz.le.trans z.2.2.property.2
          let clamp : C(X,Interval × (Interval × Tail)) := {
            toFun := fun w => (w.1,(w.2.1,⟨max w.2.2.val a,
              ha.trans_le (le_max_right _ _),max_le w.2.2.property.2 had⟩))
            continuous_toFun := by fun_prop }
          have hopen : IsOpen {w : X | a<w.2.2.val} :=
            isOpen_lt continuous_const (by fun_prop)
          have hnear : ∀ᶠ w : X in 𝓝 z,a<w.2.2.val := hopen.mem_nhds haz
          apply (PC.continuous.comp clamp.continuous).continuousAt.congr_of_eventuallyEq
          filter_upwards [hnear] with w hw
          dsimp only [extPC]
          rw [dif_pos (ha.trans hw)]
          change PC (w.1,(w.2.1,⟨w.2.2.val,ha.trans hw,w.2.2.property.2⟩))=
            PC (w.1,(w.2.1,⟨max w.2.2.val a,
              ha.trans_le (le_max_right _ _),max_le w.2.2.property.2 had⟩))
          apply congrArg PC
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · rfl
            · apply Subtype.ext
              exact (max_eq_left hw.le).symm
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt hz) z.2.2.property.1
          have hzero := hzeroValues z he
          have htend : Filter.Tendsto majorant (𝓝 z) (𝓝 (0:ℝ)) := by
            simpa only [hzero.2] using (majorant.continuous.continuousAt (x := z)).tendsto
          change Filter.Tendsto extPC (𝓝 z) (𝓝 (extPC z))
          rw [hzero.1]
          exact squeeze_zero_norm hnormBound htend
      let EC : C(X,ℂ) := ⟨extPC,hextContinuous⟩
      have hECtarget (z : X) : EC z ∈ sharedComplexChart.target := by
        by_cases ht : 0<z.2.2.val
        · change extPC z ∈ _
          dsimp only [extPC]
          rw [dif_pos ht]
          exact sharedComplexChart.map_source (hKsource
            (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)))
        · change extPC z ∈ _
          dsimp only [extPC]
          rw [dif_neg ht]
          exact hsharedComplexTarget
      let result : C(X,S) := {
        toFun := fun z => sharedComplexChart.symm (EC z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.symm.continuousAt (hECtarget z)).comp EC.continuous.continuousAt }
      have hresultPositive (z : X) (ht : 0<z.2.2.val) : result z=
          K (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)) := by
        change sharedComplexChart.symm (extPC z)=_
        dsimp only [extPC]
        rw [dif_pos ht]
        exact sharedComplexChart.left_inv (hKsource _)
      have hresultZero (z : X) (ht : z.2.2.val=0) : result z=af 0 := by
        change sharedComplexChart.symm (extPC z)=af 0
        rw [(hzeroValues z ht).1,←hsharedComplexStart]
        exact sharedComplexChart.left_inv
          (hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart)
      refine ⟨d,hd,hd1,result,?_,?_,?_,?_⟩
      · intro η τ
        exact hresultZero _ rfl
      · intro z ht
        rw [hresultPositive z ht]
        exact hKmarks _
      · intro z
        by_cases ht : 0<z.2.val
        · rw [hresultPositive (0,z) ht]
          exact hKinitial _
        · have he : z.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.property.1
          rw [hresultZero (0,z) he]
          have hp : (⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩ : Interval)=0 :=
            Subtype.ext he
          rw [hp,(hFends z.1).1,hshared]
      · intro η τ
        rw [hresultPositive (η,(τ,⟨d,hd.le,le_rfl⟩)) hd]
        exact hKouter η τ
  have hactualSharedStartBoundaryRelativePatch (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ K : C(Interval × (Interval × Icc (0:ℝ) d),S),
        (∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0) ∧
        (∀ z,0<z.2.2.val → K z ∉ (M.cover.branch : Set S)) ∧
        (∀ z,K (0,z)=F
          (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩)) ∧
        (∀ η τ,K (η,(τ,⟨d,hd.le,le_rfl⟩))=F (τ,⟨d,hd.le,hd1.le⟩)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → K (η,(τ,t))=F
          (τ,⟨t.val,t.property.1,t.property.2.trans hd1.le⟩)) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,K,hKzero,hKmarks,hKinitial,hKouter⟩ :=
        hactualSharedStartMarkedPointExtension hshared
      let temporal : C(Interval,Interval) := {
        toFun := fun τ => ⟨min 1 (4*τ.val)*min 1 (4*(1-τ.val)),by
          have hleft : 0 ≤ min 1 (4*τ.val) := le_min zero_le_one (mul_nonneg (by norm_num) τ.property.1)
          have hright : 0 ≤ min 1 (4*(1-τ.val)) :=
            le_min zero_le_one (mul_nonneg (by norm_num) (sub_nonneg.mpr τ.property.2))
          constructor
          · exact mul_nonneg hleft hright
          · exact (mul_le_mul_of_nonneg_left (min_le_left 1 _) hleft).trans
              (by simpa only [mul_one] using min_le_left 1 (4*τ.val))⟩
        continuous_toFun := by fun_prop }
      have htemporalZero : temporal 0=0 := by
        apply Subtype.ext
        norm_num [temporal]
      have htemporalOne : temporal 1=0 := by
        apply Subtype.ext
        norm_num [temporal]
      let input : C(Interval × (Interval × Icc (0:ℝ) d),
          Interval × (Interval × Icc (0:ℝ) d)) := {
        toFun := fun z => (⟨z.1.val*(temporal z.2.1).val,
          mul_nonneg z.1.property.1 (temporal z.2.1).property.1,
          (mul_le_mul_of_nonneg_left (temporal z.2.1).property.2 z.1.property.1).trans
            (by simpa only [mul_one] using z.1.property.2)⟩,z.2)
        continuous_toFun := by fun_prop }
      let result := K.comp input
      have hinputZero (z : Interval × Icc (0:ℝ) d) : input (0,z)=(0,z) := by
        apply Prod.ext
        · apply Subtype.ext
          simp [input]
        · rfl
      have hinputBoundary (η τ : Interval) (t : Icc (0:ℝ) d) (hτ : τ=0 ∨ τ=1) :
          input (η,(τ,t))=(0,(τ,t)) := by
        apply Prod.ext
        · apply Subtype.ext
          change η.val*(temporal τ).val=0
          rcases hτ with rfl | rfl
          · rw [htemporalZero]
            simp
          · rw [htemporalOne]
            simp
        · rfl
      refine ⟨d,hd,hd1,result,?_,?_,?_,?_,?_⟩
      · intro η τ
        exact hKzero (input (η,(τ,⟨0,le_rfl,hd.le⟩))).1 τ
      · intro z ht
        exact hKmarks (input z) ht
      · intro z
        change K (input (0,z))=_
        rw [hinputZero]
        exact hKinitial z
      · intro η τ
        exact hKouter (input (η,(τ,⟨d,hd.le,le_rfl⟩))).1 τ
      · intro η τ t hτ
        change K (input (η,(τ,t)))=_
        rw [hinputBoundary η τ t hτ]
        exact hKinitial (τ,t)
  have hactualSharedStartGlobalBoundaryRelativeDeformation
      (hshared : b.val.map 0=af 0) :
      ∃ HG : C(Interval × (Interval × Interval),S),
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,K,hKzero,hKmarks,hKinitial,hKouter,hKboundary⟩ :=
        hactualSharedStartBoundaryRelativePatch hshared
      let clamp : C(Interval,Icc (0:ℝ) d) := {
        toFun := fun t => ⟨min t.val d,le_min t.property.1 hd.le,min_le_right _ _⟩
        continuous_toFun := by fun_prop }
      let X := Interval × (Interval × Interval)
      let first : C(X,S) := K.comp {
        toFun := fun z => (z.1,(z.2.1,clamp z.2.2))
        continuous_toFun := by fun_prop }
      let outside : C(X,S) := F.comp {
        toFun := fun z => z.2
        continuous_toFun := continuous_snd }
      let A : Set X := {z | z.2.2.val≤d}
      have hjoin (z : X) (hz : z ∈ frontier A) : first z=outside z := by
        have hv : z.2.2.val=d := (frontier_le_subset_eq
          (by fun_prop : Continuous (fun w : X => w.2.2.val)) continuous_const) hz
        have hc : clamp z.2.2=⟨d,hd.le,le_rfl⟩ := by
          apply Subtype.ext
          simp only [clamp,ContinuousMap.coe_mk,hv,min_self]
        change K (z.1,(z.2.1,clamp z.2.2))=F (z.2.1,z.2.2)
        rw [hc,hKouter]
        have ht : (⟨d,hd.le,hd1.le⟩ : Interval)=z.2.2 := Subtype.ext hv.symm
        rw [ht]
      let HG : C(X,S) := ⟨A.piecewise first outside,
        Continuous.piecewise hjoin first.continuous outside.continuous⟩
      have hinside (z : X) (hz : z.2.2.val≤d) : HG z=K (z.1,(z.2.1,clamp z.2.2)) :=
        Set.piecewise_eq_of_mem A first outside hz
      have houtside (z : X) (hz : ¬z.2.2.val≤d) : HG z=F z.2 :=
        Set.piecewise_eq_of_notMem A first outside hz
      have hparam (t : Interval) (ht : t.val≤d) :
          (⟨(clamp t).val,(clamp t).property.1,
            (clamp t).property.2.trans hd1.le⟩ : Interval)=t :=
        Subtype.ext (min_eq_left ht)
      have hclampZero : clamp 0=⟨0,le_rfl,hd.le⟩ := by
        apply Subtype.ext
        exact min_eq_left hd.le
      refine ⟨HG,?_,?_,?_,?_⟩
      · intro z
        by_cases ht : z.2.val≤d
        · rw [hinside (0,z) ht,hKinitial,hparam z.2 ht]
        · exact houtside (0,z) ht
      · intro η τ t hτ
        by_cases ht : t.val≤d
        · rw [hinside (η,(τ,t)) ht,hKboundary η τ (clamp t) hτ,hparam t ht]
        · exact houtside (η,(τ,t)) ht
      · intro η τ t ht
        rcases ht with rfl | rfl
        · rw [hinside (η,(τ,0)) hd.le,hclampZero,hKzero,(hFends τ).1,hshared]
        · exact houtside (η,(τ,1)) (not_le_of_gt hd1)
      · intro η τ t ht₀ ht₁
        by_cases ht : t.val≤d
        · rw [hinside (η,(τ,t)) ht]
          have hpos : 0<t.val := lt_of_le_of_ne t.property.1
            (by intro he; exact ht₀ (Subtype.ext he.symm))
          exact hKmarks (η,(τ,clamp t)) (lt_min hpos hd)
        · rw [houtside (η,(τ,t)) ht]
          exact hFmarks τ t ht₀ ht₁
  have hcomplexExpConvexNorm (z w : ℂ) (t : Interval) :
      ‖Complex.exp ((1-(t.val:ℂ))*z+(t.val:ℂ)*w)‖ ≤
        max ‖Complex.exp z‖ ‖Complex.exp w‖ := by
    as_aux_lemma =>
      have hlinear : (1-t.val)*z.re+t.val*w.re ≤ max z.re w.re := by
        calc
          _ ≤ (1-t.val)*max z.re w.re+t.val*max z.re w.re := add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr t.property.2))
            (mul_le_mul_of_nonneg_left (le_max_right _ _) t.property.1)
          _ = max z.re w.re := by ring
      simp only [Complex.norm_exp,Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.sub_im,
        Complex.one_re,Complex.ofReal_re,Complex.one_im,Complex.ofReal_im,
        sub_zero,mul_zero,sub_zero,zero_mul]
      rcases le_total z.re w.re with h | h
      · rw [max_eq_right (Real.exp_le_exp.mpr h)]
        exact Real.exp_le_exp.mpr (hlinear.trans_eq (max_eq_right h))
      · rw [max_eq_left (Real.exp_le_exp.mpr h)]
        exact Real.exp_le_exp.mpr (hlinear.trans_eq (max_eq_left h))
  have hactualInitialSweepSmallTailOldFree (t : Interval)
      (ht₀ : t≠0) (htε : t.val≤ε) : F (0,t) ∉ a.val.image := by
    as_aux_lemma =>
      have ht₁ : t≠1 := by
        intro he
        have hh : (1:ℝ)≤ε := by simpa [he] using htε
        linarith only [hh,hεhalf]
      intro ha
      have hm := hFmarks 0 t ht₀ ht₁
      rw [hFzero t] at ha hm
      have hc : b.val.map t ∈ ArcSurgery.crossings M a b :=
        ⟨⟨ha,hm⟩,⟨mem_range_self t,hm⟩⟩
      exact (not_le_of_gt (hεcross t hc).1) htε
  have hmodelSmallComplexAxis (z : Plane) (hn : ‖CurveComplex.ArcFinitePosition.planeComplexLinearEquiv (z-cornerNE)‖<1) :
      z ∈ sideTop ↔ CurveComplex.ArcFinitePosition.planeComplexLinearEquiv (z-cornerNE) ∉ Complex.slitPlane := by
    as_aux_lemma =>
      have hre : (CurveComplex.ArcFinitePosition.planeComplexLinearEquiv (z-cornerNE)).re=z 0-1 := by
        rfl
      have him : (CurveComplex.ArcFinitePosition.planeComplexLinearEquiv (z-cornerNE)).im=z 1-1 := by
        rfl
      rw [mem_sideTop,Complex.mem_slitPlane_iff,hre,him]
      constructor
      · rintro ⟨hy,hx⟩
        push_neg
        constructor
        · exact sub_nonpos.mpr (le_abs_self _ |>.trans hx)
        · linarith only [hy]
      · rintro h
        push_neg at h
        obtain ⟨hx,hy⟩ := h
        have hnorm : |z 0-1|<1 :=
          (Complex.abs_re_le_norm (CurveComplex.ArcFinitePosition.planeComplexLinearEquiv (z-cornerNE))).trans_lt hn
        have hlow : -1<z 0-1 := (abs_lt.mp hnorm).1
        refine ⟨by linarith only [hy],abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith only [hlow,hx]
  have hactualSmallComplexChartAxis (x : S) (hx : x ∈ sharedComplexChart.source)
      (hn : ‖sharedComplexChart x‖<1) :
      x ∈ a.val.image ↔ sharedComplexChart x ∉ Complex.slitPlane := by
    as_aux_lemma =>
      rw [hsharedEndpointChartAxis x hx,hsharedComplexFormula]
      exact hmodelSmallComplexAxis (sharedEndpointChart x) (hsharedComplexFormula x ▸ hn)
  have hactualSharedComplexUnitTail (hshared : b.val.map 0=af 0) :
      ∃ V : Set Interval,IsOpen V ∧ (0:Interval) ∈ V ∧
        ∀ τ t : Interval,t ∈ V → F (τ,t) ∈ sharedComplexChart.source ∧
          ‖sharedComplexChart (F (τ,t))‖<complexRadius ∧
          ‖sharedComplexChart (F (τ,t))‖<1 := by
    as_aux_lemma =>
      let P : Set S := sharedComplexChart.source ∩
        sharedComplexChart ⁻¹' Metric.ball 0 (min complexRadius 1)
      have hP : IsOpen P := sharedComplexChart.isOpen_inter_preimage Metric.isOpen_ball
      have hPstart : af 0 ∈ P := by
        refine ⟨hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart,?_⟩
        change dist (sharedComplexChart (af 0)) 0 < min complexRadius 1
        rw [hsharedComplexStart,dist_self]
        exact lt_min hcomplexRadius zero_lt_one
      let N : Set (Interval × Interval) := F ⁻¹' P
      have hN : IsOpen N := hP.preimage F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {(0:Interval)} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have he : t=(0:Interval) := mem_singleton_iff.mp ht
        subst t
        change F (τ,0) ∈ P
        rw [(hFends τ).1,hshared]
        exact hPstart
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      refine ⟨V,hV,hVc (mem_singleton 0),?_⟩
      intro τ t ht
      have hx : F (τ,t) ∈ P := hUV ⟨hUall (mem_univ τ),ht⟩
      have hn : ‖sharedComplexChart (F (τ,t))‖< min complexRadius 1 := by
        simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.2
      exact ⟨hx.1,(lt_min_iff.mp hn).1,(lt_min_iff.mp hn).2⟩
  have hactualSharedStartAffineLogBoundaryInterpolation (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ L : C(Interval × Ioc (0:ℝ) d,ℂ),
      ∃ H : C(Interval × (Interval × Ioc (0:ℝ) d),ℂ),
        d≤ε ∧
        (∀ t : Ioc (0:ℝ) d,
          F (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image ∧
          F (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image) ∧
        (∀ z : Interval × Ioc (0:ℝ) d,F (z.1,⟨z.2.val,z.2.property.1.le,
          z.2.property.2.trans hd1.le⟩) ∈ sharedComplexChart.source) ∧
        (∀ z,Complex.exp (L z)=sharedComplexChart
          (F (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩))) ∧
        (∀ z,‖Complex.exp (L z)‖<1) ∧
        (∀ z,H z ∈ sharedComplexChart.target ∧ H z≠0) ∧
        (∀ z,‖H z‖ ≤ max ‖Complex.exp (L z.2)‖
          (max ‖Complex.exp (L (0,z.2.2))‖ ‖Complex.exp (L (1,z.2.2))‖)) ∧
        (∀ z,H z=Complex.exp ((1-(z.1.val:ℂ))*L z.2+
          (z.1.val:ℂ)*((1-((min 1 (max 0 (2*z.2.2.val/d-1)):ℝ):ℂ))*
            ((1-(z.2.1.val:ℂ))*L (0,z.2.2)+(z.2.1.val:ℂ)*L (1,z.2.2))+
            ((min 1 (max 0 (2*z.2.2.val/d-1)):ℝ):ℂ)*L z.2))) ∧
        (∀ z,H (0,z)=Complex.exp (L z)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → H (η,(τ,t))=Complex.exp (L (τ,t))) ∧
        (∀ η τ,H (η,(τ,⟨d,hd,le_rfl⟩))=Complex.exp (L (τ,⟨d,hd,le_rfl⟩))) ∧
        (∀ (τ : Interval) (t : Ioc (0:ℝ) d),t.val≤d/2 → H (1,(τ,t))=
          Complex.exp ((1-(τ.val:ℂ))*L (0,t)+(τ.val:ℂ)*L (1,t))) := by
    as_aux_lemma =>
      obtain ⟨d₀,hd₀,hd₀1,L₀,hL₀⟩ := hactualSharedStartLogarithmicTail hshared
      obtain ⟨V,hV,hVzero,hVtail⟩ := hactualSharedComplexUnitTail hshared
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hVzero)
      let d : ℝ := min d₀ (min (r/2) (ε/2))
      have hd : 0<d := by dsimp [d]; positivity
      have hdd₀ : d≤d₀ := min_le_left _ _
      have hd1 : d<1 := hdd₀.trans_lt hd₀1
      have hdr : d<r := by
        have h : d≤r/2 := (min_le_right d₀ _).trans (min_le_left (r/2) _)
        linarith only [h,hr]
      have hdε : d≤ε := by
        have h : d≤ε/2 := (min_le_right d₀ _).trans (min_le_right (r/2) _)
        linarith only [h,hεpos]
      have hboundaryOldFree (t : Ioc (0:ℝ) d) :
          F (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image ∧
          F (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image := by
        have ht₀ : (⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩ : Interval)≠0 := by
          intro he
          exact (ne_of_gt t.property.1) (congrArg Subtype.val he)
        have ht₁ : (⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩ : Interval)≠1 := by
          intro he
          exact (ne_of_lt (t.property.2.trans_lt hd1)) (congrArg Subtype.val he)
        exact ⟨hactualInitialSweepSmallTailOldFree _ ht₀ (t.property.2.trans hdε),
          hFterminalFull _ ht₀ ht₁⟩
      let Tail := Ioc (0:ℝ) d
      let tailInclusion : C(Interval × Tail,Interval × Ioc (0:ℝ) d₀) := {
        toFun := fun z => (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hdd₀⟩)
        continuous_toFun := by fun_prop }
      let L : C(Interval × Tail,ℂ) := L₀.comp tailInclusion
      have hL (z : Interval × Tail) : Complex.exp (L z)=sharedComplexChart
          (F (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩)) := by
        simpa [L,tailInclusion,hsharedComplexFormula] using hL₀ (tailInclusion z)
      have hsourceChart (z : Interval × Tail) :
          F (z.1,⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩) ∈ sharedComplexChart.source := by
        have hparamV : (⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.property.1]
          exact z.2.property.2.trans_lt hdr
        exact (hVtail z.1 _ hparamV).1
      have hsourceSmall (z : Interval × Tail) : ‖Complex.exp (L z)‖<complexRadius := by
        have hparamV : (⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.property.1]
          exact z.2.property.2.trans_lt hdr
        rw [hL]
        exact (hVtail z.1 _ hparamV).2.1
      have hsourceUnit (z : Interval × Tail) : ‖Complex.exp (L z)‖<1 := by
        have hparamV : (⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.property.1]
          exact z.2.property.2.trans_lt hdr
        rw [hL]
        exact (hVtail z.1 _ hparamV).2.2
      let collarWeight : C(Tail,Interval) := {
        toFun := fun t => ⟨min 1 (max 0 (2*t.val/d-1)),
          le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩
        continuous_toFun := by fun_prop }
      have hweightOuter : collarWeight ⟨d,hd,le_rfl⟩=1 := by
        apply Subtype.ext
        change min 1 (max 0 (2*d/d-1))=1
        rw [mul_div_cancel_right₀ _ (ne_of_gt hd)]
        norm_num
      have hweightInner (t : Tail) (ht : t.val≤d/2) : collarWeight t=0 := by
        apply Subtype.ext
        change min 1 (max 0 (2*t.val/d-1))=0
        have hh : 2*t.val/d-1≤0 := by
          have he : 2*t.val≤d := by linarith only [ht]
          exact sub_nonpos.mpr ((div_le_one hd).mpr he)
        rw [max_eq_left hh]
        norm_num
      let boundaryLog : C(Interval × Tail,ℂ) := {
        toFun := fun z => (1-(z.1.val:ℂ))*L (0,z.2)+(z.1.val:ℂ)*L (1,z.2)
        continuous_toFun := by fun_prop }
      let targetLog : C(Interval × Tail,ℂ) := {
        toFun := fun z => (1-((collarWeight z.2).val:ℂ))*boundaryLog z+
          ((collarWeight z.2).val:ℂ)*L z
        continuous_toFun := by fun_prop }
      let H : C(Interval × (Interval × Tail),ℂ) := {
        toFun := fun z => Complex.exp ((1-(z.1.val:ℂ))*L z.2+
          (z.1.val:ℂ)*targetLog z.2)
        continuous_toFun := by fun_prop }
      have hboundarySmall (z : Interval × Tail) :
          ‖Complex.exp (boundaryLog z)‖<complexRadius :=
        (hcomplexExpConvexNorm (L (0,z.2)) (L (1,z.2)) z.1).trans_lt
          (max_lt (hsourceSmall (0,z.2)) (hsourceSmall (1,z.2)))
      have htargetSmall (z : Interval × Tail) :
          ‖Complex.exp (targetLog z)‖<complexRadius :=
        (hcomplexExpConvexNorm (boundaryLog z) (L z) (collarWeight z.2)).trans_lt
          (max_lt (hboundarySmall z) (hsourceSmall z))
      have htargetBoundary (τ : Interval) (t : Tail) (hτ : τ=0 ∨ τ=1) :
          targetLog (τ,t)=L (τ,t) := by
        have hb : boundaryLog (τ,t)=L (τ,t) := by
          rcases hτ with rfl | rfl <;> simp [boundaryLog]
        change (1-((collarWeight t).val:ℂ))*boundaryLog (τ,t)+
          ((collarWeight t).val:ℂ)*L (τ,t)=L (τ,t)
        rw [hb]
        ring
      have htargetOuter (τ : Interval) : targetLog (τ,⟨d,hd,le_rfl⟩)=L (τ,⟨d,hd,le_rfl⟩) := by
        change (1-((collarWeight ⟨d,hd,le_rfl⟩).val:ℂ))*_+
          ((collarWeight ⟨d,hd,le_rfl⟩).val:ℂ)*_= _
        rw [hweightOuter]
        simp
      refine ⟨d,hd,hd1,L,H,hdε,hboundaryOldFree,hsourceChart,hL,hsourceUnit,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        have hs : ‖H z‖<complexRadius :=
          (hcomplexExpConvexNorm (L z.2) (targetLog z.2) z.1).trans_lt
            (max_lt (hsourceSmall z.2) (htargetSmall z.2))
        refine ⟨hcomplexBall ?_,Complex.exp_ne_zero _⟩
        simpa only [Metric.mem_ball,dist_zero_right] using hs
      · intro z
        let m : ℝ := max ‖Complex.exp (L z.2)‖
          (max ‖Complex.exp (L (0,z.2.2))‖ ‖Complex.exp (L (1,z.2.2))‖)
        have hsource : ‖Complex.exp (L z.2)‖ ≤ m := le_max_left _ _
        have hboundary : ‖Complex.exp (boundaryLog z.2)‖ ≤ m :=
          (hcomplexExpConvexNorm (L (0,z.2.2)) (L (1,z.2.2)) z.2.1).trans
            (le_max_right _ _)
        have htarget : ‖Complex.exp (targetLog z.2)‖ ≤ m :=
          (hcomplexExpConvexNorm (boundaryLog z.2) (L z.2) (collarWeight z.2.2)).trans
            (max_le hboundary hsource)
        exact (hcomplexExpConvexNorm (L z.2) (targetLog z.2) z.1).trans
          (max_le hsource htarget)
      · intro z
        rfl
      · intro z
        change Complex.exp ((1-(0:ℂ))*L z+(0:ℂ)*_)=_
        simp
      · intro η τ t hτ
        change Complex.exp ((1-(η.val:ℂ))*L (τ,t)+(η.val:ℂ)*targetLog (τ,t))=_
        rw [htargetBoundary τ t hτ]
        congr 1
        ring
      · intro η τ
        change Complex.exp ((1-(η.val:ℂ))*L (τ,⟨d,hd,le_rfl⟩)+
          (η.val:ℂ)*targetLog (τ,⟨d,hd,le_rfl⟩))=_
        rw [htargetOuter]
        congr 1
        ring
      · intro τ t ht
        change Complex.exp ((1-(1:ℂ))*L (τ,t)+(1:ℂ)*targetLog (τ,t))=_
        simp only [sub_self,zero_mul,one_mul,zero_add]
        change Complex.exp ((1-((collarWeight t).val:ℂ))*boundaryLog (τ,t)+
          ((collarWeight t).val:ℂ)*L (τ,t))=_
        rw [hweightInner t ht]
        simp [boundaryLog]
  have hcontinuousLogStripe (d : ℝ) (hd : 0<d) (L : C(Ioc (0:ℝ) d,ℂ))
      (hslit : ∀ t,Complex.exp (L t) ∈ Complex.slitPlane) :
      ∃ n : ℤ,(∀ t,L t=Complex.log (Complex.exp (L t))+n*(2*(Real.pi:ℂ)*Complex.I)) ∧
        ∀ t,(L t).im ∈ Ioo (-Real.pi+(n:ℝ)*(2*Real.pi)) (Real.pi+(n:ℝ)*(2*Real.pi)) := by
    as_aux_lemma =>
      letI : ContractibleSpace (Ioc (0:ℝ) d) := (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).contractibleSpace
        ⟨d,hd,le_rfl⟩
      let base : Ioc (0:ℝ) d := ⟨d,hd,le_rfl⟩
      obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
        (Complex.exp_log (Complex.exp_ne_zero (L base))).symm
      let Q : Ioc (0:ℝ) d → ℂ := fun t => Complex.log (Complex.exp (L t))+n*(2*(Real.pi:ℂ)*Complex.I)
      have hlogcont : Continuous (fun t => Complex.log (Complex.exp (L t))) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact ContinuousAt.comp (f := fun t : Ioc (0:ℝ) d => Complex.exp (L t)) (x := t)
          (Complex.expOpenPartialHomeomorph.symm.continuousAt (hslit t))
          ((Complex.continuous_exp.comp L.continuous).continuousAt (x := t))
      have hQ : Continuous Q := hlogcont.add continuous_const
      have hcomp : (fun z => (⟨Complex.exp z,Complex.exp_ne_zero z⟩ : {z : ℂ // z≠0})) ∘ L =
          (fun z => (⟨Complex.exp z,Complex.exp_ne_zero z⟩ : {z : ℂ // z≠0})) ∘ Q := by
        funext t
        apply Subtype.ext
        exact ((Complex.exp_eq_exp_iff_exists_int.mpr ⟨n,rfl⟩).trans
          (Complex.exp_log (Complex.exp_ne_zero (L t)))).symm
      have he : (L : Ioc (0:ℝ) d → ℂ)=Q := Complex.isCoveringMap_exp.eq_of_comp_eq
        L.continuous hQ hcomp base hn
      refine ⟨n,fun t => congrFun he t,?_⟩
      intro t
      have hb := Complex.expOpenPartialHomeomorph.map_target (hslit t)
      change (Complex.log (Complex.exp (L t))).im ∈ Ioo (-Real.pi) Real.pi at hb
      have him : ((n:ℂ)*(2*(Real.pi:ℂ)*Complex.I)).im=(n:ℝ)*(2*Real.pi) := by
        simp [Complex.mul_im,Complex.mul_re]
      rw [congrFun he t,Complex.add_im,him]
      constructor <;> linarith only [hb.1,hb.2]
  have hactualSharedStartBoundaryLogStripes (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ L : C(Interval × Ioc (0:ℝ) d,ℂ),
      ∃ H : C(Interval × (Interval × Ioc (0:ℝ) d),ℂ),
      ∃ n₀ n₁ : ℤ,
        (∀ z : Interval × Ioc (0:ℝ) d,F (z.1,⟨z.2.val,z.2.property.1.le,
          z.2.property.2.trans hd1.le⟩) ∈ sharedComplexChart.source) ∧
        (∀ z,Complex.exp (L z)=sharedComplexChart
          (F (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩))) ∧
        (∀ z,H z ∈ sharedComplexChart.target ∧ H z≠0) ∧
        (∀ z,‖H z‖<1) ∧
        (∀ z,‖H z‖≤ max
          ‖sharedComplexChart (F (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
          (max ‖sharedComplexChart (F (0,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
            ‖sharedComplexChart (F (1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖)) ∧
        (∀ t,(L (0,t)).im ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi))
          (Real.pi+(n₀:ℝ)*(2*Real.pi)) ∧
          (L (1,t)).im ∈ Ioo (-Real.pi+(n₁:ℝ)*(2*Real.pi))
          (Real.pi+(n₁:ℝ)*(2*Real.pi))) ∧
        (∀ z,H (0,z)=Complex.exp (L z)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → H (η,(τ,t))=Complex.exp (L (τ,t))) ∧
        (∀ η τ,H (η,(τ,⟨d,hd,le_rfl⟩))=Complex.exp (L (τ,⟨d,hd,le_rfl⟩))) ∧
        (∀ (τ : Interval) (t : Ioc (0:ℝ) d),t.val≤d/2 → H (1,(τ,t))=
          Complex.exp ((1-(τ.val:ℂ))*L (0,t)+(τ.val:ℂ)*L (1,t))) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,L,H,hdε,hboundaryOldFree,hsourceChart,hL,hsourceUnit,
        hHrange,hHnorm,hHformula,hHzero,hHboundary,hHouter,hHinner⟩ :=
        hactualSharedStartAffineLogBoundaryInterpolation hshared
      let Tail := Ioc (0:ℝ) d
      let left : C(Tail,ℂ) := L.comp {
        toFun := fun t => (0,t)
        continuous_toFun := by fun_prop }
      let right : C(Tail,ℂ) := L.comp {
        toFun := fun t => (1,t)
        continuous_toFun := by fun_prop }
      have hleftSlit (t : Tail) : Complex.exp (left t) ∈ Complex.slitPlane := by
        have hn : ‖sharedComplexChart (F (0,⟨t.val,t.property.1.le,
            t.property.2.trans hd1.le⟩))‖<1 := hL (0,t) ▸ hsourceUnit (0,t)
        have ha := hactualSmallComplexChartAxis
          (F (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩)) (hsourceChart (0,t)) hn
        change Complex.exp (L (0,t)) ∈ Complex.slitPlane
        rw [hL]
        by_contra hh
        exact (hboundaryOldFree t).1 (ha.mpr hh)
      have hrightSlit (t : Tail) : Complex.exp (right t) ∈ Complex.slitPlane := by
        have hn : ‖sharedComplexChart (F (1,⟨t.val,t.property.1.le,
            t.property.2.trans hd1.le⟩))‖<1 := hL (1,t) ▸ hsourceUnit (1,t)
        have ha := hactualSmallComplexChartAxis
          (F (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩)) (hsourceChart (1,t)) hn
        change Complex.exp (L (1,t)) ∈ Complex.slitPlane
        rw [hL]
        by_contra hh
        exact (hboundaryOldFree t).2 (ha.mpr hh)
      obtain ⟨n₀,hleftLog,hleftStripe⟩ := hcontinuousLogStripe d hd left hleftSlit
      obtain ⟨n₁,hrightLog,hrightStripe⟩ := hcontinuousLogStripe d hd right hrightSlit
      refine ⟨d,hd,hd1,L,H,n₀,n₁,hsourceChart,hL,hHrange,?_,?_,?_,hHzero,
        hHboundary,hHouter,hHinner⟩
      · intro z
        exact (hHnorm z).trans_lt (max_lt (hsourceUnit z.2)
          (max_lt (hsourceUnit (0,z.2.2)) (hsourceUnit (1,z.2.2))))
      · intro z
        simpa only [hL] using hHnorm z
      · intro t
        exact ⟨hleftStripe t,hrightStripe t⟩
  have hexpNegativeAxisLevels (z : ℂ) : Complex.exp z ∉ Complex.slitPlane ↔
      ∃ n : ℤ,z.im=Real.pi+(n:ℝ)*(2*Real.pi) := by
    as_aux_lemma =>
      have hperiod (n : ℤ) : ((n:ℂ)*(2*(Real.pi:ℂ)*Complex.I)).im=(n:ℝ)*(2*Real.pi) := by
        simp [Complex.mul_im,Complex.mul_re]
      constructor
      · intro hz
        rw [Complex.mem_slitPlane_iff] at hz
        push_neg at hz
        have hre : (Complex.exp z).re<0 := lt_of_le_of_ne hz.1 (by
          intro he
          apply Complex.exp_ne_zero z
          exact Complex.ext he hz.2)
        have harg := Complex.arg_eq_pi_iff.mpr ⟨hre,hz.2⟩
        obtain ⟨n,hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
          (Complex.exp_log (Complex.exp_ne_zero z)).symm
        refine ⟨n,?_⟩
        rw [hn,Complex.add_im,Complex.log_im,harg,hperiod]
      · rintro ⟨n,hn⟩
        let w : ℂ := (z.re:ℂ)+(Real.pi:ℂ)*Complex.I
        have he : z=w+n*(2*(Real.pi:ℂ)*Complex.I) := by
          apply Complex.ext
          · simp [w,Complex.mul_re,Complex.mul_im]
          · simpa [w,Complex.mul_im,Complex.mul_re] using hn
        have hexp : Complex.exp z=-(Real.exp z.re:ℂ) := by
          rw [Complex.exp_eq_exp_iff_exists_int.mpr ⟨n,he⟩]
          change Complex.exp ((z.re:ℂ)+(Real.pi:ℂ)*Complex.I)=_
          rw [Complex.exp_add,←Complex.ofReal_exp,Complex.exp_pi_mul_I]
          ring
        rw [hexp,Complex.mem_slitPlane_iff,Complex.neg_re,Complex.ofReal_re,
          Complex.neg_im,Complex.ofReal_im]
        push_neg
        exact ⟨neg_nonpos.mpr (Real.exp_pos _).le,neg_zero⟩
  have haffineLevelGraph {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (c : ℝ)
      (ha : ∀ x,a x<c) (hb : ∀ x,c<b x) :
      ∃ γ : C(X,(Icc (0:ℝ) 1)),(∀ x,0<(γ x).val ∧ (γ x).val<1) ∧
        ∀ x (τ : (Icc (0:ℝ) 1)),(1-τ.val)*a x+τ.val*b x=c ↔ τ=γ x := by
    as_aux_lemma =>
      have hδ (x : X) : 0<b x-a x := sub_pos.mpr ((ha x).trans (hb x))
      let γ : C(X,(Icc (0:ℝ) 1)) := {
        toFun := fun x => ⟨(c-a x)/(b x-a x),
          (div_pos (sub_pos.mpr (ha x)) (hδ x)).le,
          (div_lt_one (hδ x)).mpr (by linarith only [hb x]) |>.le⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact (continuous_const.sub a.continuous).div (b.continuous.sub a.continuous)
            (fun x => ne_of_gt (hδ x)) }
      have hγ (x : X) : (1-(γ x).val)*a x+(γ x).val*b x=c := by
        have he : (γ x).val*(b x-a x)=c-a x := div_mul_cancel₀ _ (ne_of_gt (hδ x))
        nlinarith only [he]
      refine ⟨γ,?_,?_⟩
      · intro x
        exact ⟨div_pos (sub_pos.mpr (ha x)) (hδ x),
          (div_lt_one (hδ x)).mpr (by linarith only [hb x])⟩
      · intro x τ
        constructor
        · intro hτ
          have he : (τ.val-(γ x).val)*(b x-a x)=0 := by nlinarith only [hτ,hγ x]
          exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt (hδ x))))
        · intro he
          subst τ
          exact hγ x
  have horderedLevels {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (n₀ n₁ : ℤ) (hn : n₀≤n₁)
      (ha : ∀ x,a x ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₀:ℝ)*(2*Real.pi)))
      (hb : ∀ x,b x ∈ Ioo (-Real.pi+(n₁:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi))) :
      ∃ γ : {k : ℤ // k ∈ Finset.Icc n₀ (n₁-1)} → C(X,Icc (0:ℝ) 1),
        (∀ k x,0<(γ k x).val ∧ (γ k x).val<1) ∧
        (∀ k x,(1-(γ k x).val)*a x+(γ k x).val*b x=Real.pi+(k.val:ℝ)*(2*Real.pi)) ∧
        ∀ x (τ : Icc (0:ℝ) 1),
          (∃ k : ℤ,(1-τ.val)*a x+τ.val*b x=Real.pi+(k:ℝ)*(2*Real.pi)) ↔
          ∃ k : {k : ℤ // k ∈ Finset.Icc n₀ (n₁-1)},τ=γ k x := by
    as_aux_lemma =>
      classical
      let Level := {k : ℤ // k ∈ Finset.Icc n₀ (n₁-1)}
      have hnR : (n₀:ℝ)≤(n₁:ℝ) := by exact_mod_cast hn
      have hlevel (k : Level) (x : X) :
          a x<Real.pi+(k.val:ℝ)*(2*Real.pi) ∧ Real.pi+(k.val:ℝ)*(2*Real.pi)<b x := by
        have hk₀ : n₀≤k.val := (Finset.mem_Icc.mp k.property).1
        have hk₁ : k.val+1≤n₁ := by have hh := (Finset.mem_Icc.mp k.property).2; omega
        have hk₀R : (n₀:ℝ)≤(k.val:ℝ) := by exact_mod_cast hk₀
        have hk₁R : (k.val:ℝ)+1≤(n₁:ℝ) := by exact_mod_cast hk₁
        constructor
        · nlinarith only [(ha x).2,hk₀R,Real.pi_pos]
        · nlinarith only [(hb x).1,hk₁R,Real.pi_pos]
      have hexists : ∀ k : Level,∃ g : C(X,Icc (0:ℝ) 1),
          (∀ x,0<(g x).val ∧ (g x).val<1) ∧
          ∀ x (τ : Icc (0:ℝ) 1),(1-τ.val)*a x+τ.val*b x=Real.pi+(k.val:ℝ)*(2*Real.pi) ↔ τ=g x := by
        intro k
        exact haffineLevelGraph a b _ (fun x => (hlevel k x).1) (fun x => (hlevel k x).2)
      choose γ hstrict hsolve using hexists
      have hbounds (x : X) (τ : Icc (0:ℝ) 1) :
          (1-τ.val)*a x+τ.val*b x ∈ Ioo
            (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi)) := by
        have hax : a x ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi)) :=
          ⟨(ha x).1,by nlinarith only [(ha x).2,hnR,Real.pi_pos]⟩
        have hbx : b x ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi)) :=
          ⟨by nlinarith only [(hb x).1,hnR,Real.pi_pos],(hb x).2⟩
        exact (convex_Ioo (𝕜:=ℝ) _ _) hax hbx
          (sub_nonneg.mpr τ.property.2) τ.property.1 (by ring)
      refine ⟨γ,hstrict,fun k x => (hsolve k x (γ k x)).mpr rfl,?_⟩
      intro x τ
      constructor
      · rintro ⟨k,hk⟩
        have hbnd := hbounds x τ
        rw [hk] at hbnd
        have hk₀ : n₀≤k := by
          by_contra hh
          have hh' : k+1≤n₀ := by omega
          have hhR : (k:ℝ)+1≤(n₀:ℝ) := by exact_mod_cast hh'
          nlinarith only [hbnd.1,hhR,Real.pi_pos]
        have hk₁ : k≤n₁-1 := by
          by_contra hh
          have hh' : n₁≤k := by omega
          have hhR : (n₁:ℝ)≤(k:ℝ) := by exact_mod_cast hh'
          nlinarith only [hbnd.2,hhR,Real.pi_pos]
        let level : Level := ⟨k,Finset.mem_Icc.mpr ⟨hk₀,hk₁⟩⟩
        exact ⟨level,(hsolve level x τ).mp hk⟩
      · rintro ⟨k,hk⟩
        exact ⟨k.val,(hsolve k x τ).mpr hk⟩

  have hfiniteUnorderedLevels {X : Type} [TopologicalSpace X] (a b : C(X,ℝ)) (n₀ n₁ : ℤ)
      (ha : ∀ x,a x ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₀:ℝ)*(2*Real.pi)))
      (hb : ∀ x,b x ∈ Ioo (-Real.pi+(n₁:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi))) :
      ∃ lo hi : ℤ,∃ γ : {k : ℤ // k ∈ Finset.Icc lo (hi-1)} → C(X,Icc (0:ℝ) 1),
        (∀ k x,0<(γ k x).val ∧ (γ k x).val<1) ∧
        (∀ k x,(1-(γ k x).val)*a x+(γ k x).val*b x=Real.pi+(k.val:ℝ)*(2*Real.pi)) ∧
        (∀ k,IsEmbedding (fun x => (γ k x,x))) ∧
        ∀ x (τ : Icc (0:ℝ) 1),
          (∃ k : ℤ,(1-τ.val)*a x+τ.val*b x=Real.pi+(k:ℝ)*(2*Real.pi)) ↔
          ∃ k : {k : ℤ // k ∈ Finset.Icc lo (hi-1)},τ=γ k x := by
    as_aux_lemma =>
      by_cases hn : n₀≤n₁
      · obtain ⟨γ,hstrict,hlevels,hsolve⟩ := horderedLevels a b n₀ n₁ hn ha hb
        refine ⟨n₀,n₁,γ,hstrict,hlevels,?_,hsolve⟩
        intro k
        exact .of_comp ((γ k).continuous.prodMk continuous_id) continuous_snd .id
      · obtain ⟨γ,hstrict,hlevels,hsolve⟩ := horderedLevels b a n₁ n₀ (le_of_lt (lt_of_not_ge hn)) hb ha
        let mirror : C(Icc (0:ℝ) 1,Icc (0:ℝ) 1) := {
          toFun := fun τ => ⟨1-τ.val,sub_nonneg.mpr τ.property.2,
            by linarith only [τ.property.1]⟩
          continuous_toFun := by fun_prop }
        let δ : {k : ℤ // k ∈ Finset.Icc n₁ (n₀-1)} → C(X,Icc (0:ℝ) 1) :=
          fun k => mirror.comp (γ k)
        have hmirror (τ : Icc (0:ℝ) 1) : mirror (mirror τ)=τ := by
          apply Subtype.ext
          change 1-(1-τ.val)=τ.val
          ring
        refine ⟨n₁,n₀,δ,?_,?_,?_,?_⟩
        · intro k x
          change 0<1-(γ k x).val ∧ 1-(γ k x).val<1
          constructor <;> linarith only [(hstrict k x).1,(hstrict k x).2]
        · intro k x
          change (1-(1-(γ k x).val))*a x+(1-(γ k x).val)*b x=_
          have he := hlevels k x
          nlinarith only [he]
        · intro k
          exact .of_comp ((δ k).continuous.prodMk continuous_id) continuous_snd .id
        · intro x τ
          have he : (1-τ.val)*a x+τ.val*b x=
              (1-(mirror τ).val)*b x+(mirror τ).val*a x := by
            change _=(1-(1-τ.val))*b x+(1-τ.val)*a x
            ring
          rw [he,hsolve]
          constructor
          · rintro ⟨k,hk⟩
            exact ⟨k,by simpa only [δ,ContinuousMap.comp_apply,hmirror] using congrArg mirror hk⟩
          · rintro ⟨k,hk⟩
            exact ⟨k,by simpa only [δ,ContinuousMap.comp_apply,hmirror] using congrArg mirror hk⟩
  have hactualSharedStartFiniteInnerContacts (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ P : C(Interval × Ioc (0:ℝ) d,S),∃ lo hi : ℤ,
      ∃ γ : {k : ℤ // k ∈ Finset.Icc lo (hi-1)} → C(Ioc (0:ℝ) d,Interval),
        (∀ z,P z ∈ sharedComplexChart.source) ∧
        (∀ z,P z ∉ (M.cover.branch : Set S)) ∧
        (∀ τ t,τ=0 ∨ τ=1 → P (τ,t)=
          F (τ,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩)) ∧
        (∀ k t,0<(γ k t).val ∧ (γ k t).val<1) ∧
        (∀ k,IsEmbedding (fun t => (γ k t,t))) ∧
        (∀ t,Function.Injective (fun k => γ k t)) ∧
        (∀ (τ : Interval) (t : Ioc (0:ℝ) d),t.val≤d/2 →
          ‖sharedComplexChart (P (τ,t))‖≤
            max ‖sharedComplexChart (F (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩))‖
              ‖sharedComplexChart (F (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩))‖) ∧
        ∀ (τ : Interval) (t : Ioc (0:ℝ) d),t.val≤d/2 →
          (P (τ,t) ∈ a.val.image ↔
            ∃ k : {k : ℤ // k ∈ Finset.Icc lo (hi-1)},τ=γ k t) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,L,H,n₀,n₁,hsource,hL,hHrange,hHunit,hHsourceNorm,hstripes,
        hHzero,hHboundary,hHouter,hHinner⟩ := hactualSharedStartBoundaryLogStripes hshared
      let Tail := Ioc (0:ℝ) d
      let left : C(Tail,ℝ) := {
        toFun := fun t => (L (0,t)).im
        continuous_toFun := by fun_prop }
      let right : C(Tail,ℝ) := {
        toFun := fun t => (L (1,t)).im
        continuous_toFun := by fun_prop }
      obtain ⟨lo,hi,γ,hstrict,hlevels,hgraph,hsolve⟩ := hfiniteUnorderedLevels left right n₀ n₁
        (fun t => (hstripes t).1) (fun t => (hstripes t).2)
      have hγinjective (t : Tail) : Function.Injective (fun k => γ k t) := by
        intro j k he
        have hj := hlevels j t
        have hk := hlevels k t
        change γ j t=γ k t at he
        rw [he] at hj
        have hc : (j.val:ℝ)=(k.val:ℝ) := mul_right_cancel₀
          (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos))
          (by linarith only [hj,hk])
        exact Subtype.ext (Int.cast_injective hc)
      let P : C(Interval × Tail,S) := {
        toFun := fun z => sharedComplexChart.symm (H (1,z))
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact ContinuousAt.comp (f := fun z : Interval × Tail => H (1,z)) (x := z)
            (sharedComplexChart.symm.continuousAt (hHrange (1,z)).1)
            ((H.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt (x := z)) }
      have hPchart (z : Interval × Tail) : sharedComplexChart (P z)=H (1,z) :=
        sharedComplexChart.right_inv (hHrange (1,z)).1
      have hPsource (z : Interval × Tail) : P z ∈ sharedComplexChart.source :=
        sharedComplexChart.map_target (hHrange (1,z)).1
      have hPne (z : Interval × Tail) : P z≠af 0 := by
        intro he
        exact (hHrange (1,z)).2 ((hPchart z).symm.trans
          ((congrArg sharedComplexChart he).trans hsharedComplexStart))
      refine ⟨d,hd,hd1,P,lo,hi,γ,hPsource,?_,?_,hstrict,hgraph,hγinjective,?_,?_⟩
      · intro z hm
        have hc : P z ∈ sharedMarkCarrier :=
          (hsharedEndpointChartSource ▸ hPsource z).2
        exact hc ⟨hm,hPne z⟩
      · intro τ t hτ
        change sharedComplexChart.symm (H (1,(τ,t)))=_
        rw [hHboundary 1 τ t hτ,hL]
        exact sharedComplexChart.left_inv (hsource (τ,t))
      · intro τ t ht
        rw [hPchart,hHinner τ t ht]
        exact (hcomplexExpConvexNorm (L (0,t)) (L (1,t)) τ).trans_eq
          (by rw [hL (0,t),hL (1,t)])
      · intro τ t ht
        have hn : ‖sharedComplexChart (P (τ,t))‖<1 :=
          (hPchart (τ,t)).symm ▸ hHunit (1,(τ,t))
        rw [hactualSmallComplexChartAxis (P (τ,t)) (hPsource (τ,t)) hn,
          hPchart,hHinner τ t ht,hexpNegativeAxisLevels]
        have him : ((1-(τ.val:ℂ))*L (0,t)+(τ.val:ℂ)*L (1,t)).im=
            (1-τ.val)*left t+τ.val*right t := by
          simp [left,right,Complex.mul_im,Complex.sub_im]
        rw [him]
        exact hsolve t τ
  have hboundedPuncturedZeroExtension (d : ℝ) (hd : 0<d) (f : C(Ioc (0:ℝ) d,ℂ)) (B : C(Icc (0:ℝ) d,ℝ))
      (hBzero : B ⟨0,le_rfl,hd.le⟩=0)
      (hbound : ∀ t,‖f t‖≤B ⟨t.val,t.property.1.le,t.property.2⟩) :
      ∃ E : C(Icc (0:ℝ) d,ℂ), E ⟨0,le_rfl,hd.le⟩=0 ∧
        ∀ t (ht : 0<t.val),E t=f ⟨t.val,ht,t.property.2⟩ := by
    as_aux_lemma =>
      let E : Icc (0:ℝ) d → ℂ := fun t => if ht : 0<t.val then f ⟨t.val,ht,t.property.2⟩ else 0
      have hnorm (t : Icc (0:ℝ) d) : ‖E t‖≤B t := by
        by_cases ht : 0<t.val
        · change ‖if ht : 0<t.val then f ⟨t.val,ht,t.property.2⟩ else 0‖≤B t
          rw [dif_pos ht]
          exact hbound ⟨t.val,ht,t.property.2⟩
        · have he : t=⟨0,le_rfl,hd.le⟩ := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
          simp [E,ht,he,hBzero]
      have hcont : Continuous E := by
        apply continuous_iff_continuousAt.mpr
        intro t
        by_cases ht : 0<t.val
        · let a : ℝ := t.val/2
          have ha : 0<a := by dsimp [a]; positivity
          have hat : a<t.val := by dsimp [a]; linarith only [ht]
          have had : a≤d := hat.le.trans t.property.2
          let clamp : C(Icc (0:ℝ) d,Ioc (0:ℝ) d) := {
            toFun := fun s => ⟨max s.val a,ha.trans_le (le_max_right _ _),max_le s.property.2 had⟩
            continuous_toFun := by fun_prop }
          have hopen : IsOpen {s : Icc (0:ℝ) d | a<s.val} := isOpen_lt continuous_const continuous_subtype_val
          have hnear : ∀ᶠ s in 𝓝 t,a<s.val := hopen.mem_nhds hat
          apply (f.continuous.comp clamp.continuous).continuousAt.congr_of_eventuallyEq
          filter_upwards [hnear] with s hs
          dsimp only [E]
          rw [dif_pos (ha.trans hs)]
          apply congrArg f
          apply Subtype.ext
          exact (max_eq_left hs.le).symm
        · have he : t=⟨0,le_rfl,hd.le⟩ := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
          have hzero : E t=0 := dif_neg ht
          have htend : Filter.Tendsto B (𝓝 t) (𝓝 (0:ℝ)) := by
            simpa only [he,hBzero] using (B.continuous.continuousAt (x := t)).tendsto
          change Filter.Tendsto E (𝓝 t) (𝓝 (E t))
          rw [hzero]
          exact squeeze_zero_norm hnorm htend
      refine ⟨⟨E,hcont⟩,?_,?_⟩
      · exact dif_neg (lt_irrefl (0:ℝ))
      · intro t ht
        exact dif_pos ht
  have hactualSharedStartContactIdealEnds (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),∃ lo hi : ℤ,
      ∃ C : {k : ℤ // k ∈ Finset.Icc lo (hi-1)} → C(Icc (0:ℝ) (d/2),S),
        (∀ k,C k ⟨0,le_rfl,(half_pos hd).le⟩=af 0) ∧
        (∀ k t,0<t.val → C k t ∈ a.val.image ∧ C k t ∉ (M.cover.branch : Set S)) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,P,lo,hi,γ,hPsource,hPmarks,hPboundary,hstrict,hgraph,hγinjective,hPnorm,hPcontact⟩ :=
        hactualSharedStartFiniteInnerContacts hshared
      let Level := {k : ℤ // k ∈ Finset.Icc lo (hi-1)}
      let CT := Icc (0:ℝ) (d/2)
      let IT := Ioc (0:ℝ) (d/2)
      have hh : 0<d/2 := half_pos hd
      have hhalf : d/2≤d := half_le_self hd.le
      let source (τ : Interval) : C(CT,S) := {
        toFun := fun t => F (τ,⟨t.val,t.property.1,t.property.2.trans (hhalf.trans hd1.le)⟩)
        continuous_toFun := by fun_prop }
      have hSourceChart (τ : Interval) (hτ : τ=0 ∨ τ=1) (t : CT) :
          source τ t ∈ sharedComplexChart.source := by
        by_cases ht : 0<t.val
        · let u : Ioc (0:ℝ) d := ⟨t.val,ht,t.property.2.trans hhalf⟩
          have he := hPboundary τ u hτ
          exact he ▸ hPsource (τ,u)
        · have he : t.val=0 := le_antisymm (le_of_not_gt ht) t.property.1
          have hp : (⟨t.val,t.property.1,t.property.2.trans (hhalf.trans hd1.le)⟩ : Interval)=0 :=
            Subtype.ext he
          change F (τ,_) ∈ sharedComplexChart.source
          rw [hp,(hFends τ).1,hshared]
          exact hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart
      let boundaryC (τ : Interval) (hτ : τ=0 ∨ τ=1) : C(CT,ℂ) := {
        toFun := fun t => sharedComplexChart (source τ t)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro t
          exact (sharedComplexChart.continuousAt (hSourceChart τ hτ t)).comp
            (source τ).continuous.continuousAt }
      let leftC := boundaryC 0 (Or.inl rfl)
      let rightC := boundaryC 1 (Or.inr rfl)
      let B : C(CT,ℝ) := {
        toFun := fun t => max ‖leftC t‖ ‖rightC t‖
        continuous_toFun := by fun_prop }
      have hBzero : B ⟨0,le_rfl,hh.le⟩=0 := by
        change max ‖sharedComplexChart (F (0,0))‖ ‖sharedComplexChart (F (1,0))‖=0
        rw [(hFends 0).1,(hFends 1).1,hshared,hsharedComplexStart,norm_zero,max_self]
      let inTail : C(IT,Ioc (0:ℝ) d) := {
        toFun := fun t => ⟨t.val,t.property.1,t.property.2.trans hhalf⟩
        continuous_toFun := by fun_prop }
      let parameters (k : Level) : C(IT,Interval × Ioc (0:ℝ) d) := {
        toFun := fun t => (γ k (inTail t),inTail t)
        continuous_toFun := by fun_prop }
      let points (k : Level) : C(IT,S) := P.comp (parameters k)
      let complexPoints (k : Level) : C(IT,ℂ) := {
        toFun := fun t => sharedComplexChart (points k t)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro t
          exact ContinuousAt.comp (f := fun t : IT => points k t) (x := t)
            (sharedComplexChart.continuousAt (hPsource (parameters k t)))
            ((points k).continuous.continuousAt (x := t)) }
      have hbound (k : Level) (t : IT) :
          ‖complexPoints k t‖≤B ⟨t.val,t.property.1.le,t.property.2⟩ := by
        exact hPnorm (γ k (inTail t)) (inTail t) t.property.2
      have hext : ∀ k : Level,∃ EC : C(CT,ℂ),EC ⟨0,le_rfl,hh.le⟩=0 ∧
          ∀ t (ht : 0<t.val),EC t=complexPoints k ⟨t.val,ht,t.property.2⟩ := by
        intro k
        exact hboundedPuncturedZeroExtension (d/2) hh (complexPoints k) B hBzero (hbound k)
      choose EC hECzero hECpositive using hext
      have hECtarget (k : Level) (t : CT) : EC k t ∈ sharedComplexChart.target := by
        by_cases ht : 0<t.val
        · rw [hECpositive k t ht]
          exact sharedComplexChart.map_source (hPsource (parameters k ⟨t.val,ht,t.property.2⟩))
        · have he : t=⟨0,le_rfl,hh.le⟩ := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
          rw [he,hECzero]
          exact hsharedComplexTarget
      let C (k : Level) : C(CT,S) := {
        toFun := fun t => sharedComplexChart.symm (EC k t)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro t
          exact (sharedComplexChart.symm.continuousAt (hECtarget k t)).comp
            (EC k).continuous.continuousAt }
      have hCpositive (k : Level) (t : CT) (ht : 0<t.val) :
          C k t=points k ⟨t.val,ht,t.property.2⟩ := by
        change sharedComplexChart.symm (EC k t)=_
        rw [hECpositive k t ht]
        exact sharedComplexChart.left_inv (hPsource (parameters k ⟨t.val,ht,t.property.2⟩))
      refine ⟨d,hd,hd1,lo,hi,C,?_,?_⟩
      · intro k
        change sharedComplexChart.symm (EC k ⟨0,le_rfl,hh.le⟩)=af 0
        rw [hECzero,←hsharedComplexStart]
        exact sharedComplexChart.left_inv
          (hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart)
      · intro k t ht
        rw [hCpositive k t ht]
        let u : IT := ⟨t.val,ht,t.property.2⟩
        refine ⟨?_,hPmarks (parameters k u)⟩
        exact (hPcontact (γ k (inTail u)) (inTail u) t.property.2).mpr ⟨k,rfl⟩
  have hactualSharedStartAffineMarkedPointExtension (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),∃ n₀ n₁ : ℤ,
      ∃ L : C(Interval × Ioc (0:ℝ) d,ℂ),
      ∃ K : C(Interval × (Interval × Icc (0:ℝ) d),S),
        (∀ t,(L (0,t)).im ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₀:ℝ)*(2*Real.pi)) ∧
          (L (1,t)).im ∈ Ioo (-Real.pi+(n₁:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi))) ∧
        (∀ z,K z ∈ sharedComplexChart.source) ∧
        (∀ z,‖sharedComplexChart (K z)‖<1) ∧
        (∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0) ∧
        (∀ z,0<z.2.2.val → K z ∉ (M.cover.branch : Set S)) ∧
        (∀ z,K (0,z)=F (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩)) ∧
        (∀ η τ,K (η,(τ,⟨d,hd.le,le_rfl⟩))=F (τ,⟨d,hd.le,hd1.le⟩)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → K (η,(τ,t))=
          F (τ,⟨t.val,t.property.1,t.property.2.trans hd1.le⟩)) ∧
        (∀ (τ : Interval) (t : Icc (0:ℝ) d) (ht : 0<t.val),t.val≤d/2 →
          sharedComplexChart (K (1,(τ,t)))=Complex.exp
            ((1-(τ.val:ℂ))*L (0,⟨t.val,ht,t.property.2⟩)+(τ.val:ℂ)*L (1,⟨t.val,ht,t.property.2⟩))) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,L,H,n₀,n₁,hsource,hL,hHrange,hHunit,hHsourceNorm,hstripes,
        hHzero,hHboundary,hHouter,hHinner⟩ := hactualSharedStartBoundaryLogStripes hshared
      let K : C(Interval × (Interval × Ioc (0:ℝ) d),S) := {
        toFun := fun z => sharedComplexChart.symm (H z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.symm.continuousAt (hHrange z).1).comp H.continuous.continuousAt }
      have hKchart (z : Interval × (Interval × Ioc (0:ℝ) d)) : sharedComplexChart (K z)=H z :=
        sharedComplexChart.right_inv (hHrange z).1
      have hKsource (z : Interval × (Interval × Ioc (0:ℝ) d)) : K z ∈ sharedComplexChart.source :=
        sharedComplexChart.map_target (hHrange z).1
      have hKne (z : Interval × (Interval × Ioc (0:ℝ) d)) : K z≠af 0 := by
        intro he
        exact (hHrange z).2 ((hKchart z).symm.trans ((congrArg sharedComplexChart he).trans hsharedComplexStart))
      have hKmarks (z : Interval × (Interval × Ioc (0:ℝ) d)) : K z ∉ (M.cover.branch : Set S) := by
        intro hm
        have hc : K z ∈ sharedMarkCarrier := (hsharedEndpointChartSource ▸ hKsource z).2
        exact hc ⟨hm,hKne z⟩
      have hKnorm (z : Interval × (Interval × Ioc (0:ℝ) d)) :
          ‖sharedComplexChart (K z)‖≤ max
            ‖sharedComplexChart (F (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
            (max ‖sharedComplexChart (F (0,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
              ‖sharedComplexChart (F (1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖) := by
        rw [hKchart]
        exact hHsourceNorm z
      have hKinitial (z : Interval × Ioc (0:ℝ) d) : K (0,z)=
          F (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩) := by
        change sharedComplexChart.symm (H (0,z))=_
        rw [hHzero,hL]
        exact sharedComplexChart.left_inv (hsource z)
      have hKouter (η τ : Interval) : K (η,(τ,⟨d,hd,le_rfl⟩))=F (τ,⟨d,hd.le,hd1.le⟩) := by
        change sharedComplexChart.symm (H (η,(τ,⟨d,hd,le_rfl⟩)))=_
        rw [hHouter,hL]
        exact sharedComplexChart.left_inv (hsource _)
      have hKboundary (η τ : Interval) (t : Ioc (0:ℝ) d) (hτ : τ=0 ∨ τ=1) :
          K (η,(τ,t))=F (τ,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) := by
        change sharedComplexChart.symm (H (η,(τ,t)))=_
        rw [hHboundary η τ t hτ,hL]
        exact sharedComplexChart.left_inv (hsource _)
      let Tail := Ioc (0:ℝ) d
      let ClosedTail := Icc (0:ℝ) d
      let X := Interval × (Interval × ClosedTail)
      let PC : C(Interval × (Interval × Tail),ℂ) := {
        toFun := fun z => sharedComplexChart (K z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.continuousAt (hKsource z)).comp K.continuous.continuousAt }
      let source : C(X,S) := {
        toFun := fun z => F (z.2.1,⟨z.2.2.val,z.2.2.property.1,
          z.2.2.property.2.trans hd1.le⟩)
        continuous_toFun := by fun_prop }
      have hsourceChart (z : X) : source z ∈ sharedComplexChart.source := by
        by_cases ht : 0<z.2.2.val
        · let t : Tail := ⟨z.2.2.val,ht,z.2.2.property.2⟩
          have he := hKinitial (z.2.1,t)
          exact he ▸ hKsource (0,(z.2.1,t))
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          have hparam : (⟨z.2.2.val,z.2.2.property.1,
              z.2.2.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext he
          change F (z.2.1,_) ∈ sharedComplexChart.source
          rw [hparam,(hFends z.2.1).1,hshared]
          exact hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart
      let sourceC : C(X,ℂ) := {
        toFun := fun z => sharedComplexChart (source z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.continuousAt (hsourceChart z)).comp source.continuous.continuousAt }
      let leftSourceC : C(X,ℂ) := sourceC.comp {
        toFun := fun z => (z.1,(0,z.2.2))
        continuous_toFun := by fun_prop }
      let rightSourceC : C(X,ℂ) := sourceC.comp {
        toFun := fun z => (z.1,(1,z.2.2))
        continuous_toFun := by fun_prop }
      let majorant : C(X,ℝ) := {
        toFun := fun z => max ‖sourceC z‖ (max ‖leftSourceC z‖ ‖rightSourceC z‖)
        continuous_toFun := by fun_prop }
      let extPC : X → ℂ := fun z => if ht : 0<z.2.2.val then
        PC (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)) else 0
      have hnormBound (z : X) : ‖extPC z‖ ≤ majorant z := by
        by_cases ht : 0<z.2.2.val
        · dsimp only [extPC]
          rw [dif_pos ht]
          exact hKnorm (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩))
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          simp only [extPC,dif_neg ht,norm_zero,majorant,ContinuousMap.coe_mk,he,
            zero_mul,add_zero]
          exact (norm_nonneg _).trans (le_max_left _ _)
      have hzeroValues (z : X) (hz : z.2.2.val=0) : extPC z=0 ∧ majorant z=0 := by
        have hparam : (⟨z.2.2.val,z.2.2.property.1,
            z.2.2.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext hz
        constructor
        · simp only [extPC,hz,lt_self_iff_false,dif_neg,not_false_eq_true]
        · change max ‖sharedComplexChart (F (z.2.1,
              ⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hd1.le⟩))‖
            (max ‖sharedComplexChart (F (0,
              ⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hd1.le⟩))‖
              ‖sharedComplexChart (F (1,
                ⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hd1.le⟩))‖)=0
          simp only [hparam,(hFends z.2.1).1,(hFends 0).1,(hFends 1).1,hshared,
            hsharedComplexStart,norm_zero,max_self]
      have hextContinuous : Continuous extPC := by
        apply continuous_iff_continuousAt.mpr
        intro z
        by_cases hz : 0<z.2.2.val
        · let a : ℝ := z.2.2.val/2
          have ha : 0<a := by dsimp [a]; positivity
          have haz : a<z.2.2.val := by dsimp [a]; linarith only [hz]
          have had : a≤d := haz.le.trans z.2.2.property.2
          let clamp : C(X,Interval × (Interval × Tail)) := {
            toFun := fun w => (w.1,(w.2.1,⟨max w.2.2.val a,
              ha.trans_le (le_max_right _ _),max_le w.2.2.property.2 had⟩))
            continuous_toFun := by fun_prop }
          have hopen : IsOpen {w : X | a<w.2.2.val} :=
            isOpen_lt continuous_const (by fun_prop)
          have hnear : ∀ᶠ w : X in 𝓝 z,a<w.2.2.val := hopen.mem_nhds haz
          apply (PC.continuous.comp clamp.continuous).continuousAt.congr_of_eventuallyEq
          filter_upwards [hnear] with w hw
          dsimp only [extPC]
          rw [dif_pos (ha.trans hw)]
          change PC (w.1,(w.2.1,⟨w.2.2.val,ha.trans hw,w.2.2.property.2⟩))=
            PC (w.1,(w.2.1,⟨max w.2.2.val a,
              ha.trans_le (le_max_right _ _),max_le w.2.2.property.2 had⟩))
          apply congrArg PC
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · rfl
            · apply Subtype.ext
              exact (max_eq_left hw.le).symm
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt hz) z.2.2.property.1
          have hzero := hzeroValues z he
          have htend : Filter.Tendsto majorant (𝓝 z) (𝓝 (0:ℝ)) := by
            simpa only [hzero.2] using (majorant.continuous.continuousAt (x := z)).tendsto
          change Filter.Tendsto extPC (𝓝 z) (𝓝 (extPC z))
          rw [hzero.1]
          exact squeeze_zero_norm hnormBound htend
      let EC : C(X,ℂ) := ⟨extPC,hextContinuous⟩
      have hECtarget (z : X) : EC z ∈ sharedComplexChart.target := by
        by_cases ht : 0<z.2.2.val
        · change extPC z ∈ _
          dsimp only [extPC]
          rw [dif_pos ht]
          exact sharedComplexChart.map_source (hKsource
            (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)))
        · change extPC z ∈ _
          dsimp only [extPC]
          rw [dif_neg ht]
          exact hsharedComplexTarget
      let result : C(X,S) := {
        toFun := fun z => sharedComplexChart.symm (EC z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.symm.continuousAt (hECtarget z)).comp EC.continuous.continuousAt }
      have hresultPositive (z : X) (ht : 0<z.2.2.val) : result z=
          K (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)) := by
        change sharedComplexChart.symm (extPC z)=_
        dsimp only [extPC]
        rw [dif_pos ht]
        exact sharedComplexChart.left_inv (hKsource _)
      have hresultZero (z : X) (ht : z.2.2.val=0) : result z=af 0 := by
        change sharedComplexChart.symm (extPC z)=af 0
        rw [(hzeroValues z ht).1,←hsharedComplexStart]
        exact sharedComplexChart.left_inv
          (hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart)
      refine ⟨d,hd,hd1,n₀,n₁,L,result,hstripes,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        exact sharedComplexChart.map_target (hECtarget z)
      · intro z
        by_cases ht : 0<z.2.2.val
        · rw [hresultPositive z ht,hKchart]
          exact hHunit _
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          rw [hresultZero z he,hsharedComplexStart,norm_zero]
          norm_num
      · intro η τ
        exact hresultZero _ rfl
      · intro z ht
        rw [hresultPositive z ht]
        exact hKmarks _
      · intro z
        by_cases ht : 0<z.2.val
        · rw [hresultPositive (0,z) ht]
          exact hKinitial _
        · have he : z.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.property.1
          rw [hresultZero (0,z) he]
          have hp : (⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩ : Interval)=0 :=
            Subtype.ext he
          rw [hp,(hFends z.1).1,hshared]
      · intro η τ
        rw [hresultPositive (η,(τ,⟨d,hd.le,le_rfl⟩)) hd]
        exact hKouter η τ
      · intro η τ t hτ
        by_cases ht : 0<t.val
        · rw [hresultPositive (η,(τ,t)) ht]
          exact hKboundary η τ ⟨t.val,ht,t.property.2⟩ hτ
        · have he : t.val=0 := le_antisymm (le_of_not_gt ht) t.property.1
          rw [hresultZero (η,(τ,t)) he]
          have hp : (⟨t.val,t.property.1,t.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext he
          rw [hp,(hFends τ).1,hshared]
      · intro τ t ht hhalf
        rw [hresultPositive (1,(τ,t)) ht]
        rw [hKchart]
        exact hHinner τ ⟨t.val,ht,t.property.2⟩ hhalf
  have hActualSharedAffineLevelGraphClosesAtOriginalMark
      (d : ℝ) (hd : 0<d) (hd1 : d<1)
      (L : C(Interval × Ioc (0:ℝ) d,ℂ))
      (K : C(Interval × (Interval × Icc (0:ℝ) d),S))
      (hsource : ∀ z,K z∈sharedComplexChart.source)
      (hunit : ∀ z,‖sharedComplexChart (K z)‖<1)
      (hzero : ∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0)
      (hinner : ∀ (τ : Interval) (t : Icc (0:ℝ) d) (ht : 0<t.val),t.val≤d/2 →
        sharedComplexChart (K (1,(τ,t)))=Complex.exp
          ((1-(τ.val:ℂ))*L (0,⟨t.val,ht,t.property.2⟩)+(τ.val:ℂ)*L (1,⟨t.val,ht,t.property.2⟩)))
      (n : ℤ) (γ : C(Ioc (0:ℝ) d,Interval))
      (hlevel : ∀ t,(1-(γ t).val)*(L (0,t)).im+(γ t).val*(L (1,t)).im=
        Real.pi+(n:ℝ)*(2*Real.pi)) :
      ∃ f : Path (af 0) (K (1,(γ ⟨d/2,half_pos hd,half_le_self hd.le⟩,
        ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))),
        range f⊆a.val.image ∧
        ∀ t : {t : Interval // t≠0},f t.val=K (1,(γ
          ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
            (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
            (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩,
          ⟨(d/2)*t.val.val,mul_nonneg (half_pos hd).le t.val.property.1,
            (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩)) := by
    as_aux_lemma =>
      let σ : C(Interval,Icc (0:ℝ) d) :=
        ⟨fun t => ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
          (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
      let H : C(Interval × Interval,S) := K.comp
        ⟨fun z => (1,(z.1,σ z.2)),by fun_prop⟩
      let σp : C({t : Interval // t≠0},Ioc (0:ℝ) d) :=
        ⟨fun t => ⟨(σ t.val).val,mul_pos (half_pos hd)
          (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
          (σ t.val).property.2⟩,by fun_prop⟩
      let γp := γ.comp σp
      have hHboundary (x : Interval) : H (x,0)=af 0 := by
        change K (1,(x,σ 0))=af 0
        have he : σ 0=⟨0,le_rfl,hd.le⟩ := by apply Subtype.ext;simp [σ]
        rw [he,hzero]
      have hcontact (t : {t : Interval // t≠0}) : H (γp t,t.val)∈a.val.image := by
        change K (1,(γ (σp t),σ t.val))∈a.val.image
        rw [hactualSmallComplexChartAxis _ (hsource _) (hunit _),
          hinner _ _ (σp t).property.1 (mul_le_of_le_one_right (half_pos hd).le t.val.property.2),
          hexpNegativeAxisLevels]
        refine ⟨n,?_⟩
        have he := hlevel (σp t)
        simpa only [σp,ContinuousMap.coe_mk,Complex.add_im,Complex.mul_im,Complex.sub_im,Complex.one_im,
          Complex.ofReal_im,Complex.one_re,Complex.ofReal_re,Complex.sub_re,zero_sub,mul_zero,zero_mul,
          add_zero,sub_zero,neg_zero] using he
      obtain ⟨f,hf,hr⟩ := CurveComplex.LocalSurgery.actualCompactStripPuncturedContactPath
        H (af 0) hHboundary 0 γp a.val.image
          (hAFRange ▸ (show af 0∈range af from ⟨0,rfl⟩)) hcontact
      have htarget : K (1,(γ ⟨d/2,half_pos hd,half_le_self hd.le⟩,
          ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))=H (γp ⟨1,by simp⟩,1) := by
        change K (1,(γ ⟨d/2,half_pos hd,half_le_self hd.le⟩,
          ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))=K (1,(γ (σp ⟨1,by simp⟩),σ 1))
        apply congrArg K
        apply Prod.ext
        · rfl
        apply Prod.ext
        · apply congrArg γ
          apply Subtype.ext
          simp [σp,σ]
        · apply Subtype.ext
          simp [σ]
      refine ⟨f.cast rfl htarget,hr,?_⟩
      intro t
      exact hf t
  have hActualSharedAffineStripRetainedOriginalCornerCarrier
      (d : ℝ) (hd : 0<d)
      (K : C(Interval × (Interval × Icc (0:ℝ) d),S))
      (hzero : ∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0)
      (hmarks : ∀ (z : Interval × (Interval × Icc (0:ℝ) d)),0<z.2.2.val →
        K z∉(M.cover.branch : Set S)) :
      let σ : Interval → Icc (0:ℝ) d := fun t =>
        ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
          (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩
      ∃ H : C(Interval × Interval,{x : S // x∉((M.cover.branch : Set S)\{af 0})}),
        ∀ z,(H z).val=K (1,(z.1,σ z.2)) := by
    let σ : C(Interval,Icc (0:ℝ) d) :=
      ⟨fun t => ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
        (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
    let H₀ : C(Interval × Interval,S) := K.comp
      ⟨fun z => (1,(z.1,σ z.2)),by fun_prop⟩
    have hcarrier (z : Interval × Interval) : H₀ z∉((M.cover.branch : Set S)\{af 0}) := by
      change K (1,(z.1,σ z.2))∉((M.cover.branch : Set S)\{af 0})
      by_cases ht : z.2=0
      · have he : σ z.2=⟨0,le_rfl,hd.le⟩ := by
          apply Subtype.ext
          simp [σ,ht]
        rw [he,hzero]
        simp
      · have hp : 0<z.2.val := lt_of_le_of_ne z.2.property.1
          (fun he => ht (Subtype.ext he.symm))
        exact fun h => hmarks (1,(z.1,σ z.2)) (mul_pos (half_pos hd) hp) h.1
    refine ⟨⟨fun z => ⟨H₀ z,hcarrier z⟩,H₀.continuous.subtype_mk _⟩,?_⟩
    intro z
    rfl
  have hActualSharedAffineContactTailRetainedOriginalBoundaryRoute
      (d : ℝ) (hd : 0<d) (hd1 : d<1) (ξ : Interval → Interval)
      (L : C(Interval × Ioc (0:ℝ) d,ℂ))
      (K : C(Interval × (Interval × Icc (0:ℝ) d),S))
      (hsource : ∀ z,K z∈sharedComplexChart.source)
      (hunit : ∀ z,‖sharedComplexChart (K z)‖<1)
      (hzero : ∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0)
      (hmarks : ∀ (z : Interval × (Interval × Icc (0:ℝ) d)),0<z.2.2.val →
        K z∉(M.cover.branch : Set S))
      (hboundaryKzero : ∀ t,K (1,(0,t))=
        b.val.map (ξ ⟨t.val,t.property.1,t.property.2.trans hd1.le⟩))
      (hinner : ∀ (τ : Interval) (t : Icc (0:ℝ) d) (ht : 0<t.val),t.val≤d/2 →
        sharedComplexChart (K (1,(τ,t)))=Complex.exp
          ((1-(τ.val:ℂ))*L (0,⟨t.val,ht,t.property.2⟩)+(τ.val:ℂ)*L (1,⟨t.val,ht,t.property.2⟩)))
      (n : ℤ) (γ : C(Ioc (0:ℝ) d,Interval))
      (hlevel : ∀ t,(1-(γ t).val)*(L (0,t)).im+(γ t).val*(L (1,t)).im=
        Real.pi+(n:ℝ)*(2*Real.pi)) :
      let σ : Interval → Icc (0:ℝ) d := fun t =>
        ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
          (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩
      ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
      ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
        c.val=af 0 ∧
        range (fun t => (α t).val)⊆a.val.image ∧
        (∀ t,(v t).val=b.val.map
          (ξ ⟨(σ t).val,(σ t).property.1,(σ t).property.2.trans hd1.le⟩)) ∧
        (∀ t,(w t).val=K (1,
          (⟨t.val*(γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,
            mul_nonneg t.property.1 (γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).property.1,
            (mul_le_of_le_one_right t.property.1
              (γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).property.2).trans t.property.2⟩,
            ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))) ∧
        (∀ t : {t : Interval // t≠0},(α t.val).val=K (1,
          (γ ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
            (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
            (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩,
            σ t.val))) ∧
        α.Homotopic (v.trans w) := by
    let σ : C(Interval,Icc (0:ℝ) d) :=
      ⟨fun t => ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
        (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
    obtain ⟨H,hH⟩ := hActualSharedAffineStripRetainedOriginalCornerCarrier d hd K hzero hmarks
    let σp : C({t : Interval // t≠0},Ioc (0:ℝ) d) :=
      ⟨fun t => ⟨(σ t.val).val,mul_pos (half_pos hd)
        (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
        (σ t.val).property.2⟩,by fun_prop⟩
    let γp := γ.comp σp
    let c := H (0,0)
    have hc : c.val=af 0 := by
      rw [hH]
      have he : σ 0=⟨0,le_rfl,hd.le⟩ := by apply Subtype.ext;simp [σ]
      change K (1,(0,σ 0))=af 0
      rw [he,hzero]
    have hboundary (x : Interval) : H (x,0)=c := by
      apply Subtype.ext
      rw [hc,hH]
      have he : σ 0=⟨0,le_rfl,hd.le⟩ := by apply Subtype.ext;simp [σ]
      change K (1,(x,σ 0))=af 0
      rw [he,hzero]
    obtain ⟨α,v,w,hα,hv,hw,hhom⟩ :=
      CurveComplex.LocalSurgery.actualCompactStripPuncturedContactTraceHomotopicToBoundaryRoute
        H c hboundary γp
    obtain ⟨f,hfrange,hftrace⟩ := hActualSharedAffineLevelGraphClosesAtOriginalMark
      d hd hd1 L K hsource hunit hzero hinner n γ hlevel
    refine ⟨c,_,_,α,v,w,hc,?_,?_,?_,?_,hhom⟩
    · rintro x ⟨t,rfl⟩
      change (α t).val∈a.val.image
      by_cases ht : t=0
      · subst t
        rw [α.source,hc]
        exact hAFRange ▸ (show af 0∈range af from ⟨0,rfl⟩)
      · have he := congrArg Subtype.val (hα ⟨t,ht⟩)
        rw [hH] at he
        have hf := hftrace ⟨t,ht⟩
        have heq : (α t).val=f t := by
          exact he.trans hf.symm
        rw [heq]
        exact hfrange ⟨t,rfl⟩
    · intro t
      have he := (congrArg Subtype.val (hv t)).trans (hH _)
      rw [hboundaryKzero] at he
      exact he
    · intro t
      have he := (congrArg Subtype.val (hw t)).trans (hH _)
      simpa [γp,σp,σ] using he
    · intro t
      exact (congrArg Subtype.val (hα t)).trans (hH _)
  have hActualSharedAffineOriginalContactTailClosesAsEmbeddedConeParameterPath
      (d : ℝ) (hd : 0<d) (hd1 : d<1)
      (L : C(Interval × Ioc (0:ℝ) d,ℂ))
      (K : C(Interval × (Interval × Icc (0:ℝ) d),S))
      (hsource : ∀ z,K z∈sharedComplexChart.source)
      (hunit : ∀ z,‖sharedComplexChart (K z)‖<1)
      (hzero : ∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0)
      (hinner : ∀ (τ : Interval) (t : Icc (0:ℝ) d) (ht : 0<t.val),t.val≤d/2 →
        sharedComplexChart (K (1,(τ,t)))=Complex.exp
          ((1-(τ.val:ℂ))*L (0,⟨t.val,ht,t.property.2⟩)+(τ.val:ℂ)*L (1,⟨t.val,ht,t.property.2⟩)))
      (n : ℤ) (γ : C(Ioc (0:ℝ) d,Interval))
      (hlevel : ∀ t,(1-(γ t).val)*(L (0,t)).im+(γ t).val*(L (1,t)).im=
        Real.pi+(n:ℝ)*(2*Real.pi))
      (hstrict : ∀ t,0<(γ t).val ∧ (γ t).val<1) :
      let σ : Interval → Icc (0:ℝ) d := fun t =>
        ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
          (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩
      ∃ f : Path (af 0) (K (1,(γ ⟨d/2,half_pos hd,half_le_self hd.le⟩,
        ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))),range f⊆a.val.image ∧
      ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=γ ⟨d/2,half_pos hd,half_le_self hd.le⟩ ∧
      (∀ t : {t : Interval // t≠0},Γ t=γ
        ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
          (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
          (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩) ∧
      ∃ P : Path ((0,0) : ℝ × ℝ) ((γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,d/2),
        IsEmbedding P ∧
        (∀ t : {t : Interval // t≠0},f t.val=K (1,(Γ t,σ t.val))) ∧
        (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,(d/2)*t.val.val)) ∧
        (∀ t : {t : Interval // t≠0},0<(Γ t).val ∧ (Γ t).val<1) ∧
        (∀ t : Interval,(P t).2=(d/2)*t.val) := by
    let σp : C({t : Interval // t≠0},Ioc (0:ℝ) d) :=
      ⟨fun t => ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
        (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
        (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
    let Γ := γ.comp σp
    have hΓend : Γ ⟨1,by simp⟩=γ ⟨d/2,half_pos hd,half_le_self hd.le⟩ := by
      apply congrArg γ
      apply Subtype.ext
      simp [σp]
    obtain ⟨f,hf,hftrace⟩ := hActualSharedAffineLevelGraphClosesAtOriginalMark
      d hd hd1 L K hsource hunit hzero hinner n γ hlevel
    obtain ⟨P,hP,hPtrace,hPsecond,hPinside⟩ :=
      CurveComplex.LocalSurgery.actualSharedMarkedTailClosedConeParameterInterior
        (d/2) (half_pos hd) Γ (fun t => hstrict (σp t))
    have hPend : ((γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,d/2)=
        ((Γ ⟨1,by simp⟩).val,d/2) := by
      apply Prod.ext
      · exact congrArg Subtype.val hΓend.symm
      · rfl
    refine ⟨f,hf,Γ,hΓend,(fun t => rfl),P.cast rfl hPend,hP,?_,hPtrace,fun t => hstrict (σp t),hPsecond⟩
    intro t
    exact hftrace t

  have hactualSharedStartGlobalFiniteCornerDeformation (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),∃ lo hi : ℤ,
      ∃ γ : {k : ℤ // k ∈ Finset.Icc lo (hi-1)} → C(Ioc (0:ℝ) d,Interval),
      ∃ HG : C(Interval × (Interval × Interval),S),
        (∀ k t,0<(γ k t).val ∧ (γ k t).val<1) ∧
        (∀ k,IsEmbedding (fun t => (γ k t,t))) ∧
        (∀ t,Function.Injective (fun k => γ k t)) ∧
        (∀ τ : Interval,HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈sharedComplexChart.source ∧
          ‖sharedComplexChart (HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))‖<1) ∧
        (∀ k,(sharedComplexChart (HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).re<0 ∧ ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
          (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
          v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
          γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
          w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
          (sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
          (sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
          ((sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0 ↔
            ¬(sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0)) ∧
        (∀ (k : {k : ℤ // k∈Finset.Icc lo (hi-1)}) (C : OpenPartialHomeomorph S (ℝ × ℝ)),
          HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
            ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source →
          (∀ x∈C.source,x∈a.val.image ↔ (C x).1=0) →
          ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
            (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
            v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
            γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
            w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
            HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            (C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            (C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            ((C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0 ↔
              ¬(C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0)) ∧
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        (∀ η τ t,d<t.val → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ (τ t : Interval) (ht₀ : t≠0) (ht : t.val≤d/2),
          HG (1,(τ,t)) ∈ a.val.image ↔
            ∃ k : {k : ℤ // k ∈ Finset.Icc lo (hi-1)},τ=γ k
              ⟨t.val,lt_of_le_of_ne t.property.1 (by intro he; exact ht₀ (Subtype.ext he.symm)),
                ht.trans (half_le_self hd.le)⟩) ∧
        ∀ k,∃ f : Path (af 0) (HG (1,(γ k
          ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,by linarith⟩))),
          range f⊆a.val.image ∧
          (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
          ∃ Γ : C({t : Interval // t≠0},Interval),
            Γ ⟨1,by simp⟩=γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ ∧
            (∀ t : {t : Interval // t≠0},Γ t=γ k
              ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
                (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
                (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩) ∧
          ∃ P : Path ((0,0) : ℝ × ℝ)
            ((γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,d/2),
            IsEmbedding P ∧
            (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,
              ⟨(d/2)*t.val.val,mul_nonneg (half_pos hd).le t.val.property.1,
                ((mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans
                  (half_le_self hd.le)).trans hd1.le⟩))) ∧
            (∀ t : {t : Interval // t≠0},P t.val=
              (t.val.val*(Γ t).val,(d/2)*t.val.val)) ∧
            (∀ t : {t : Interval // t≠0},0<(Γ t).val ∧ (Γ t).val<1) ∧
            (∀ t : Interval,(P t).2=(d/2)*t.val) ∧
          ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
          ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
            c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
            (∀ t,(v t).val=b.val.map
              ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
                ((mul_le_of_le_one_right (half_pos hd).le t.property.2).trans
                  (half_le_self hd.le)).trans hd1.le⟩) ∧
            (∀ t,(w t).val=HG (1,
              (⟨t.val*(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,
                mul_nonneg t.property.1 (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).property.1,
                (mul_le_of_le_one_right t.property.1
                  (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).property.2).trans t.property.2⟩,
                ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))) ∧
            α.Homotopic (v.trans w) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,n₀,n₁,L,K,hstripes,hKsource,hKunit,hKzero,hKmarks,hKinitial,
        hKouter,hKboundary,hKinner⟩ := hactualSharedStartAffineMarkedPointExtension hshared
      let left : C(Ioc (0:ℝ) d,ℝ) := {
        toFun := fun t => (L (0,t)).im
        continuous_toFun := by fun_prop }
      let right : C(Ioc (0:ℝ) d,ℝ) := {
        toFun := fun t => (L (1,t)).im
        continuous_toFun := by fun_prop }
      obtain ⟨lo,hi,γ,hstrict,hlevels,hgraph,hsolve⟩ := hfiniteUnorderedLevels left right n₀ n₁
        (fun t => (hstripes t).1) (fun t => (hstripes t).2)
      have hγinjective (t : Ioc (0:ℝ) d) : Function.Injective (fun k => γ k t) := by
        intro j k he
        have hj := hlevels j t
        have hk := hlevels k t
        change γ j t=γ k t at he
        rw [he] at hj
        have hc : (j.val:ℝ)=(k.val:ℝ) := mul_right_cancel₀
          (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos))
          (by linarith only [hj,hk])
        exact Subtype.ext (Int.cast_injective hc)
      let clamp : C(Interval,Icc (0:ℝ) d) := {
        toFun := fun t => ⟨min t.val d,le_min t.property.1 hd.le,min_le_right _ _⟩
        continuous_toFun := by fun_prop }
      let X := Interval × (Interval × Interval)
      let first : C(X,S) := K.comp {
        toFun := fun z => (z.1,(z.2.1,clamp z.2.2))
        continuous_toFun := by fun_prop }
      let outside : C(X,S) := F.comp {
        toFun := fun z => z.2
        continuous_toFun := continuous_snd }
      let A : Set X := {z | z.2.2.val≤d}
      have hjoin (z : X) (hz : z ∈ frontier A) : first z=outside z := by
        have hv : z.2.2.val=d := (frontier_le_subset_eq
          (by fun_prop : Continuous (fun w : X => w.2.2.val)) continuous_const) hz
        have hc : clamp z.2.2=⟨d,hd.le,le_rfl⟩ := by
          apply Subtype.ext
          simp only [clamp,ContinuousMap.coe_mk,hv,min_self]
        change K (z.1,(z.2.1,clamp z.2.2))=F (z.2.1,z.2.2)
        rw [hc,hKouter]
        have ht : (⟨d,hd.le,hd1.le⟩ : Interval)=z.2.2 := Subtype.ext hv.symm
        rw [ht]
      let HG : C(X,S) := ⟨A.piecewise first outside,
        Continuous.piecewise hjoin first.continuous outside.continuous⟩
      have hinside (z : X) (hz : z.2.2.val≤d) : HG z=K (z.1,(z.2.1,clamp z.2.2)) :=
        Set.piecewise_eq_of_mem A first outside hz
      have houtside (z : X) (hz : ¬z.2.2.val≤d) : HG z=F z.2 :=
        Set.piecewise_eq_of_notMem A first outside hz
      have hparam (t : Interval) (ht : t.val≤d) :
          (⟨(clamp t).val,(clamp t).property.1,
            (clamp t).property.2.trans hd1.le⟩ : Interval)=t :=
        Subtype.ext (min_eq_left ht)
      have hclampZero : clamp 0=⟨0,le_rfl,hd.le⟩ := by
        apply Subtype.ext
        exact min_eq_left hd.le
      have hSeamActual (τ : Interval) :
          HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))=
            K (1,(τ,⟨d/2,(half_pos hd).le,half_le_self hd.le⟩)) := by
        rw [hinside _ (half_le_self hd.le)]
        apply congrArg K
        apply Prod.ext
        · rfl
        apply Prod.ext
        · rfl
        apply Subtype.ext
        exact min_eq_left (half_le_self hd.le)
      have hSeamChartData (τ : Interval) :
          HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈sharedComplexChart.source ∧
            ‖sharedComplexChart (HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))‖<1 := by
        rw [hSeamActual]
        exact ⟨hKsource _,hKunit _⟩
      have hSeamComplexFormula (τ : Interval) :
          sharedComplexChart (HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))=
            Complex.exp ((1-(τ.val:ℂ))*L (0,⟨d/2,half_pos hd,half_le_self hd.le⟩)+
              (τ.val:ℂ)*L (1,⟨d/2,half_pos hd,half_le_self hd.le⟩)) := by
        rw [hinside _ (half_le_self hd.le)]
        have he : clamp ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩=
            ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩ := by
          apply Subtype.ext
          exact min_eq_left (half_le_self hd.le)
        rw [he]
        exact hKinner τ ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩ (half_pos hd) le_rfl
      have hSeamSides (k : {k : ℤ // k∈Finset.Icc lo (hi-1)}) :
          (sharedComplexChart (HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).re<0 ∧
          ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
            (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
            v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
            γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
            w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
            (sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
            (sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
            ((sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0 ↔
              ¬(sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0) := by
        let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,half_le_self hd.le⟩
        have hlevel := hlevels k t
        change (1-(γ k t).val)*(L (0,t)).im+(γ k t).val*(L (1,t)).im=
          Real.pi+(k.val:ℝ)*(2*Real.pi) at hlevel
        have him : ((1-((γ k t).val:ℂ))*L (0,t)+((γ k t).val:ℂ)*L (1,t)).im=
            Real.pi+(k.val:ℝ)*(2*Real.pi) := by
          simpa [Complex.mul_im,Complex.sub_im] using hlevel
        have hNegativeReal : (sharedComplexChart (HG (1,(γ k t,
            ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).re<0 := by
          rw [hSeamComplexFormula,Complex.exp_re,him,Real.cos_add_int_mul_two_pi,Real.cos_pi]
          have hp := Real.exp_pos (((1-((γ k t).val:ℂ))*L (0,t)+((γ k t).val:ℂ)*L (1,t)).re)
          simpa only [mul_neg_one] using neg_neg_of_pos hp
        have hSlope := CurveComplex.LocalSurgery.actualAffineLogSeamSlopeNonzeroOfStripLevel
          (L (0,t)) (L (1,t)) (γ k t).val n₀ k.val (hstripes t).1 hlevel
        obtain ⟨δ,hδ,hflip⟩ := CurveComplex.LocalSurgery.actualAffineLogSeamCrossesNegativeAxisLocally
          (L (0,t)) (L (1,t)) (γ k t).val k.val hSlope hlevel
        refine ⟨hNegativeReal,δ,hδ,?_⟩
        intro v w hvlo hvu huw hwhi
        rw [hSeamComplexFormula,hSeamComplexFormula]
        exact hflip v.val w.val hvlo hvu huw hwhi
      have hSeamAdaptedSides (k : {k : ℤ // k∈Finset.Icc lo (hi-1)})
          (C : OpenPartialHomeomorph S (ℝ × ℝ))
          (hpC : HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
            ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source)
          (hCaxis : ∀ x∈C.source,x∈a.val.image ↔ (C x).1=0) :
          ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
            (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
            v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
            γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
            w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
            HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            (C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            (C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            ((C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0 ↔
              ¬(C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0) := by
        let r : Interval := ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩
        let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,half_le_self hd.le⟩
        let β : C(Interval,S) := ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩
        obtain ⟨hneg,δ,hδ,hflip⟩ := hSeamSides k
        have hdata := hSeamChartData (γ k t)
        have hlevel := hlevels k t
        change (1-(γ k t).val)*(L (0,t)).im+(γ k t).val*(L (1,t)).im=
          Real.pi+(k.val:ℝ)*(2*Real.pi) at hlevel
        have him : ((1-((γ k t).val:ℂ))*L (0,t)+((γ k t).val:ℂ)*L (1,t)).im=
            Real.pi+(k.val:ℝ)*(2*Real.pi) := by
          simpa [Complex.mul_im,Complex.sub_im] using hlevel
        have hpointImag : (sharedComplexChart (β (γ k t))).im=0 := by
          change (sharedComplexChart (HG (1,(γ k t,r)))).im=0
          rw [hSeamComplexFormula,Complex.exp_im,him,Real.sin_add_int_mul_two_pi,Real.sin_pi,mul_zero]
        have hpA : β (γ k t)∈a.val.image := by
          apply (hactualSmallComplexChartAxis _ hdata.1 hdata.2).mpr
          change sharedComplexChart (β (γ k t))∉Complex.slitPlane
          have hnegβ : (sharedComplexChart (β (γ k t))).re<0 := hneg
          simp only [Complex.slitPlane,Set.mem_setOf_eq,not_or,not_lt,not_not]
          exact ⟨hnegβ.le,hpointImag⟩
        exact CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel.actualMarkedNegativeComplexSeamTraceChangesSideInEveryAdaptedChart
          M a sharedComplexChart (fun x hx hn => hactualSmallComplexChartAxis x hx hn)
          β (γ k t) hpA hdata.1 hdata.2 hneg C hpC hCaxis δ hδ hflip
      refine ⟨d,hd,hd1,lo,hi,γ,HG,hstrict,hgraph,hγinjective,hSeamChartData,hSeamSides,hSeamAdaptedSides,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        by_cases ht : z.2.val≤d
        · rw [hinside (0,z) ht,hKinitial,hparam z.2 ht]
        · exact houtside (0,z) ht
      · intro η τ t hτ
        by_cases ht : t.val≤d
        · rw [hinside (η,(τ,t)) ht,hKboundary η τ (clamp t) hτ,hparam t ht]
        · exact houtside (η,(τ,t)) ht
      · intro η τ t ht
        rcases ht with rfl | rfl
        · rw [hinside (η,(τ,0)) hd.le,hclampZero,hKzero,(hFends τ).1,hshared]
        · exact houtside (η,(τ,1)) (not_le_of_gt hd1)
      · intro η τ t ht₀ ht₁
        by_cases ht : t.val≤d
        · rw [hinside (η,(τ,t)) ht]
          have hpos : 0<t.val := lt_of_le_of_ne t.property.1
            (by intro he; exact ht₀ (Subtype.ext he.symm))
          exact hKmarks (η,(τ,clamp t)) (lt_min hpos hd)
        · rw [houtside (η,(τ,t)) ht]
          exact hFmarks τ t ht₀ ht₁
      · intro η τ t ht
        exact houtside (η,(τ,t)) (not_le_of_gt ht)
      · intro τ t ht₀ htHalf
        have ht : t.val≤d := htHalf.trans (half_le_self hd.le)
        have hpos : 0<t.val := lt_of_le_of_ne t.property.1
          (by intro he; exact ht₀ (Subtype.ext he.symm))
        rw [hinside (1,(τ,t)) ht]
        have hc : (clamp t).val=t.val := min_eq_left ht
        have hcp : 0<(clamp t).val := hc ▸ hpos
        rw [hactualSmallComplexChartAxis _ (hKsource (1,(τ,clamp t))) (hKunit (1,(τ,clamp t))),
          hKinner τ (clamp t) hcp (hc ▸ htHalf),hexpNegativeAxisLevels]
        have him : ((1-(τ.val:ℂ))*L (0,⟨(clamp t).val,hcp,(clamp t).property.2⟩)+
            (τ.val:ℂ)*L (1,⟨(clamp t).val,hcp,(clamp t).property.2⟩)).im=
            (1-τ.val)*left ⟨t.val,hpos,ht⟩+τ.val*right ⟨t.val,hpos,ht⟩ := by
          have he : (⟨(clamp t).val,hcp,(clamp t).property.2⟩ : Ioc (0:ℝ) d)=⟨t.val,hpos,ht⟩ :=
            Subtype.ext hc
          rw [he]
          simp [left,right,Complex.mul_im,Complex.sub_im]
        rw [him]
        exact hsolve ⟨t.val,hpos,ht⟩ τ
      · intro k
        obtain ⟨f,hf,Γ,hΓend,hΓnormalization,P,hP,htrace,hPtrace,hΓstrict,hPsecond⟩ :=
          hActualSharedAffineOriginalContactTailClosesAsEmbeddedConeParameterPath
            d hd hd1 L K hKsource hKunit hKzero hKinner k.val (γ k) (hlevels k) (hstrict k)
        let r : Interval := ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩
        have hend : HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,r))=
            K (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
              ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩)) := by
          rw [hinside _ (half_le_self hd.le)]
          apply congrArg K
          apply Prod.ext
          · rfl
          apply Prod.ext
          · rfl
          apply Subtype.ext
          exact min_eq_left (half_le_self hd.le)
        obtain ⟨c,y,z,α,v,w,hc,hαrange,hv,hw,hαtrace,hhom⟩ :=
          hActualSharedAffineContactTailRetainedOriginalBoundaryRoute
            d hd hd1 id L K hKsource hKunit hKzero hKmarks
            (fun t => (hKboundary 1 0 t (Or.inl rfl)).trans (hFzero _))
            hKinner k.val (γ k) (hlevels k)
        refine ⟨f.cast rfl hend,hf,?_,Γ,hΓend,hΓnormalization,P,hP,?_,hPtrace,hΓstrict,hPsecond,c,y,z,α,v,w,hc,?_,hv,?_,hhom⟩
        · intro t ht
          change f t∉(M.cover.branch : Set S)
          rw [htrace ⟨t,ht⟩]
          exact hKmarks _ (mul_pos (half_pos hd)
            (lt_of_le_of_ne t.property.1 (fun h => ht (Subtype.ext h.symm))))
        · intro t
          change f t.val=HG (1,(Γ t,_))
          rw [htrace t]
          symm
          have ht : (d/2)*t.val.val≤d :=
            (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)
          rw [hinside _ ht]
          apply congrArg K
          apply Prod.ext
          · rfl
          apply Prod.ext
          · rfl
          apply Subtype.ext
          exact min_eq_left ht
        · intro t
          change (α t).val=f t
          by_cases ht : t=0
          · subst t
            exact (congrArg Subtype.val α.source).trans (hc.trans f.source.symm)
          · have hftrace := htrace ⟨t,ht⟩
            rw [hΓnormalization] at hftrace
            exact (hαtrace ⟨t,ht⟩).trans hftrace.symm
        · intro t
          rw [hw t]
          symm
          rw [hinside _ (half_le_self hd.le)]
          apply congrArg K
          apply Prod.ext
          · rfl
          apply Prod.ext
          · rfl
          apply Subtype.ext
          exact min_eq_left (half_le_self hd.le)
  have hactualSharedStartFiniteInnerSeam (hshared : b.val.map 0=af 0) :
      ∃ r : Interval,r≠0 ∧ r≠1 ∧ ∃ HG : C(Interval × (Interval × Interval),S),
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,lo,hi,γ,HG,hstrict,hgraph,hγinjective,hSeamChartData,hSeamSides,hSeamAdaptedSides,hzero,hboundary,hends,hmarks,hExterior,hcontact,hclosedtails⟩ :=
        hactualSharedStartGlobalFiniteCornerDeformation hshared
      have hhalf : d/2≤d := half_le_self hd.le
      let r : Interval := ⟨d/2,(half_pos hd).le,hhalf.trans hd1.le⟩
      have hr₀ : r≠0 := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_gt (half_pos hd)) hv
      have hr₁ : r≠1 := by
        intro he
        have hv := congrArg Subtype.val he
        have hr : d/2<1 := hhalf.trans_lt hd1
        exact (ne_of_lt hr) hv
      let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,hhalf⟩
      have hfinite : {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
        apply (Set.finite_range (fun k => γ k t)).subset
        intro τ hτ
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        exact ⟨k,hk.symm⟩
      exact ⟨r,hr₀,hr₁,HG,hzero,hboundary,hends,hmarks,hfinite⟩
  have hsymmNeZero (t : Interval) (ht : t≠1) : unitInterval.symm t≠0 := by
    as_aux_lemma =>
      intro he
      apply ht
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change 1-t.val=0 at hv
      change t.val=1
      linarith only [hv]
  have hsymmNeOne (t : Interval) (ht : t≠0) : unitInterval.symm t≠1 := by
    as_aux_lemma =>
      intro he
      apply ht
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change 1-t.val=1 at hv
      change t.val=0
      linarith only [hv]
  let Fref : C(Interval × Interval,S) := F.comp {
    toFun := fun z => (z.1,unitInterval.symm z.2)
    continuous_toFun := by fun_prop }
  have hactualSharedComplexUnitEitherTail (c : Interval) (hc : c=0 ∨ c=1)
      (hshared : b.val.map c=af 0) :
      ∃ V : Set Interval,IsOpen V ∧ c ∈ V ∧
        ∀ τ t : Interval,t ∈ V → F (τ,t) ∈ sharedComplexChart.source ∧
          ‖sharedComplexChart (F (τ,t))‖<complexRadius ∧
          ‖sharedComplexChart (F (τ,t))‖<1 := by
    as_aux_lemma =>
      let P : Set S := sharedComplexChart.source ∩
        sharedComplexChart ⁻¹' Metric.ball 0 (min complexRadius 1)
      have hP : IsOpen P := sharedComplexChart.isOpen_inter_preimage Metric.isOpen_ball
      have hPstart : af 0 ∈ P := by
        refine ⟨hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart,?_⟩
        change dist (sharedComplexChart (af 0)) 0 < min complexRadius 1
        rw [hsharedComplexStart,dist_self]
        exact lt_min hcomplexRadius zero_lt_one
      let N : Set (Interval × Interval) := F ⁻¹' P
      have hN : IsOpen N := hP.preimage F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {c} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have he : t=c := mem_singleton_iff.mp ht
        subst t
        change F (τ,c) ∈ P
        rcases hc with rfl | rfl
        · rw [(hFends τ).1,hshared]
          exact hPstart
        · rw [(hFends τ).2,hshared]
          exact hPstart
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      refine ⟨V,hV,hVc (mem_singleton c),?_⟩
      intro τ t ht
      have hx : F (τ,t) ∈ P := hUV ⟨hUall (mem_univ τ),ht⟩
      have hn : ‖sharedComplexChart (F (τ,t))‖< min complexRadius 1 := by
        simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hx.2
      exact ⟨hx.1,(lt_min_iff.mp hn).1,(lt_min_iff.mp hn).2⟩
  have hactualSharedComplexUnitReflectedTail (hshared : b.val.map 1=af 0) :
      ∃ V : Set Interval,IsOpen V ∧ (0:Interval) ∈ V ∧
        ∀ τ t : Interval,t ∈ V → Fref (τ,t) ∈ sharedComplexChart.source ∧
          ‖sharedComplexChart (Fref (τ,t))‖<complexRadius ∧
          ‖sharedComplexChart (Fref (τ,t))‖<1 := by
    as_aux_lemma =>
      obtain ⟨V,hV,hVone,hVtail⟩ := hactualSharedComplexUnitEitherTail 1 (Or.inr rfl) hshared
      refine ⟨unitInterval.symm ⁻¹' V,hV.preimage unitInterval.continuous_symm,?_,?_⟩
      · simpa only [mem_preimage,unitInterval.symm_zero] using hVone
      · intro τ t ht
        exact hVtail τ (unitInterval.symm t) ht
  have hFrefTerminalFull (t : Interval) (ht₀ : t≠0) (ht₁ : t≠1) :
      Fref (1,t) ∉ a.val.image :=
    hFterminalFull (unitInterval.symm t)
      (hsymmNeZero _ ht₁)
      (hsymmNeOne _ ht₀)
  have hactualReflectedInitialSmallTailOldFree (t : Interval) (ht₀ : t≠0) (htε : t.val≤ε) :
      Fref (0,t) ∉ a.val.image := by
    as_aux_lemma =>
      have ht₁ : t≠1 := by
        intro he
        have ht : (1:ℝ)≤ε := by simpa [he] using htε
        linarith only [ht,hεhalf]
      have hm : Fref (0,t) ∉ (M.cover.branch : Set S) := hFmarks 0 (unitInterval.symm t)
        (hsymmNeZero _ ht₁)
        (hsymmNeOne _ ht₀)
      intro ha
      have hb : Fref (0,t)=b.val.map (unitInterval.symm t) := hFzero _
      have hK : unitInterval.symm t ∈ K :=
        ⟨⟨hb ▸ ha,hb ▸ hm⟩,⟨mem_range_self _,hb ▸ hm⟩⟩
      have hh := (hεcross (unitInterval.symm t) hK).2
      rw [unitInterval.coe_symm_eq] at hh
      linarith only [hh,htε]
  have hactualSharedReflectedLogarithmicTail (hshared : b.val.map 1=af 0) :
      ∃ (d : ℝ) (_hd : 0<d) (hd1 : d<1),
        ∃ L : C(Interval × Set.Ioc (0:ℝ) d,ℂ),
          ∀ z : Interval × Set.Ioc (0:ℝ) d,
            Complex.exp (L z) = ArcFinitePosition.planeComplexLinearEquiv
              (sharedEndpointChart (Fref (z.1,⟨z.2.val,
                z.2.property.1.le,z.2.property.2.trans hd1.le⟩))-cornerNE) := by
    as_aux_lemma =>
      obtain ⟨V₁,hV₁,hVone,hV₁tail⟩ := hactualSharedMarkSmallChartTail 1 (Or.inr rfl) hshared
      let V := unitInterval.symm ⁻¹' V₁
      have hV : IsOpen V := hV₁.preimage unitInterval.continuous_symm
      have hVzero : (0:Interval) ∈ V := by
        simpa only [V,mem_preimage,unitInterval.symm_zero] using hVone
      have hVtail (τ t : Interval) (ht : t ∈ V) := hV₁tail τ (unitInterval.symm t) ht
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hVzero)
      let d : ℝ := min (r/2) (1/2)
      have hd : 0<d := by dsimp [d]; positivity
      have hd1 : d<1 := by
        have h := min_le_right (r/2) (1/2:ℝ)
        dsimp [d]
        linarith only [h]
      have hdr : d<r := by
        have h := min_le_left (r/2) (1/2:ℝ)
        dsimp [d]
        linarith only [h,hr]
      let Tail := Set.Ioc (0:ℝ) d
      letI : ContractibleSpace Tail := (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).contractibleSpace
        ⟨d,hd,le_rfl⟩
      letI : LocallyPathConnectedSpace Tail := (convex_Ioc (𝕜:=ℝ) (0:ℝ) d).locallyPathConnectedSpace
      letI : ContractibleSpace Interval := (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace
        ⟨0,by norm_num⟩
      letI : LocallyPathConnectedSpace Interval := (convex_Icc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
      let param : C(Tail,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩,
        by fun_prop⟩
      have hparamV (t : Tail) : param t ∈ V := by
        apply hball
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |t.val-0|<r
        rw [sub_zero,abs_of_pos t.property.1]
        exact t.property.2.trans_lt hdr
      let tailSource : C(Interval × Tail,S) := {
        toFun := fun z => Fref (z.1,param z.2)
        continuous_toFun := by fun_prop }
      have htailChart (z : Interval × Tail) : tailSource z ∈ sharedEndpointChart.source :=
        (hVtail z.1 (param z.2) (hparamV z.2)).1
      let g : C(Interval × Tail,ℂ) := {
        toFun := fun z => ArcFinitePosition.planeComplexLinearEquiv
          (sharedEndpointChart (tailSource z)-cornerNE)
        continuous_toFun := by
          apply ArcFinitePosition.planeComplexLinearEquiv.continuous.comp
          apply Continuous.sub ?_ continuous_const
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedEndpointChart.continuousAt (htailChart z)).comp
            tailSource.continuous.continuousAt }
      have hgzero (z : Interval × Tail) : g z ≠ 0 := by
        intro he
        have hplane : sharedEndpointChart (tailSource z)-cornerNE=0 :=
          ArcFinitePosition.planeComplexLinearEquiv.injective (he.trans
            ArcFinitePosition.planeComplexLinearEquiv.map_zero.symm)
        have hpoint : sharedEndpointChart (tailSource z)=cornerNE := sub_eq_zero.mp hplane
        have ht₀ : param z.2 ≠ (0:Interval) := by
          intro he
          exact (ne_of_gt z.2.property.1) (congrArg Subtype.val he)
        have ht₁ : param z.2 ≠ (1:Interval) := by
          intro he
          exact (ne_of_lt (z.2.property.2.trans_lt hd1)) (congrArg Subtype.val he)
        exact (hVtail z.1 (param z.2) (hparamV z.2)).2.2 (hsymmNeZero _ ht₁)
          (hsymmNeOne _ ht₀) hpoint
      let gNonzero : C(Interval × Tail,{z : ℂ // z ≠ 0}) :=
        ⟨fun z => ⟨g z,hgzero z⟩,g.continuous.subtype_mk _⟩
      let base : Interval × Tail := (0,⟨d,hd,le_rfl⟩)
      have hbase : (⟨Complex.exp (Complex.log (g base)),Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) =
          gNonzero base := Subtype.ext (Complex.exp_log (hgzero base))
      obtain ⟨L,⟨hLbase,hL⟩,hLunique⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
        gNonzero base (Complex.log (g base)) hbase
      refine ⟨d,hd,hd1,L,?_⟩
      intro z
      exact congrArg Subtype.val (congrFun hL z)
  have hactualSharedReflectedAffineLogBoundaryInterpolation (hshared : b.val.map 1=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ L : C(Interval × Ioc (0:ℝ) d,ℂ),
      ∃ H : C(Interval × (Interval × Ioc (0:ℝ) d),ℂ),
        d≤ε ∧
        (∀ t : Ioc (0:ℝ) d,
          Fref (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image ∧
          Fref (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image) ∧
        (∀ z : Interval × Ioc (0:ℝ) d,Fref (z.1,⟨z.2.val,z.2.property.1.le,
          z.2.property.2.trans hd1.le⟩) ∈ sharedComplexChart.source) ∧
        (∀ z,Complex.exp (L z)=sharedComplexChart
          (Fref (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩))) ∧
        (∀ z,‖Complex.exp (L z)‖<1) ∧
        (∀ z,H z ∈ sharedComplexChart.target ∧ H z≠0) ∧
        (∀ z,‖H z‖ ≤ max ‖Complex.exp (L z.2)‖
          (max ‖Complex.exp (L (0,z.2.2))‖ ‖Complex.exp (L (1,z.2.2))‖)) ∧
        (∀ z,H z=Complex.exp ((1-(z.1.val:ℂ))*L z.2+
          (z.1.val:ℂ)*((1-((min 1 (max 0 (2*z.2.2.val/d-1)):ℝ):ℂ))*
            ((1-(z.2.1.val:ℂ))*L (0,z.2.2)+(z.2.1.val:ℂ)*L (1,z.2.2))+
            ((min 1 (max 0 (2*z.2.2.val/d-1)):ℝ):ℂ)*L z.2))) ∧
        (∀ z,H (0,z)=Complex.exp (L z)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → H (η,(τ,t))=Complex.exp (L (τ,t))) ∧
        (∀ η τ,H (η,(τ,⟨d,hd,le_rfl⟩))=Complex.exp (L (τ,⟨d,hd,le_rfl⟩))) ∧
        (∀ (τ : Interval) (t : Ioc (0:ℝ) d),t.val≤d/2 → H (1,(τ,t))=
          Complex.exp ((1-(τ.val:ℂ))*L (0,t)+(τ.val:ℂ)*L (1,t))) := by
    as_aux_lemma =>
      obtain ⟨d₀,hd₀,hd₀1,L₀,hL₀⟩ := hactualSharedReflectedLogarithmicTail hshared
      obtain ⟨V,hV,hVzero,hVtail⟩ := hactualSharedComplexUnitReflectedTail hshared
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hVzero)
      let d : ℝ := min d₀ (min (r/2) (ε/2))
      have hd : 0<d := by dsimp [d]; positivity
      have hdd₀ : d≤d₀ := min_le_left _ _
      have hd1 : d<1 := hdd₀.trans_lt hd₀1
      have hdr : d<r := by
        have h : d≤r/2 := (min_le_right d₀ _).trans (min_le_left (r/2) _)
        linarith only [h,hr]
      have hdε : d≤ε := by
        have h : d≤ε/2 := (min_le_right d₀ _).trans (min_le_right (r/2) _)
        linarith only [h,hεpos]
      have hboundaryOldFree (t : Ioc (0:ℝ) d) :
          Fref (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image ∧
          Fref (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) ∉ a.val.image := by
        have ht₀ : (⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩ : Interval)≠0 := by
          intro he
          exact (ne_of_gt t.property.1) (congrArg Subtype.val he)
        have ht₁ : (⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩ : Interval)≠1 := by
          intro he
          exact (ne_of_lt (t.property.2.trans_lt hd1)) (congrArg Subtype.val he)
        exact ⟨hactualReflectedInitialSmallTailOldFree _ ht₀ (t.property.2.trans hdε),
          hFrefTerminalFull _ ht₀ ht₁⟩
      let Tail := Ioc (0:ℝ) d
      let tailInclusion : C(Interval × Tail,Interval × Ioc (0:ℝ) d₀) := {
        toFun := fun z => (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hdd₀⟩)
        continuous_toFun := by fun_prop }
      let L : C(Interval × Tail,ℂ) := L₀.comp tailInclusion
      have hL (z : Interval × Tail) : Complex.exp (L z)=sharedComplexChart
          (Fref (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩)) := by
        simpa [L,tailInclusion,hsharedComplexFormula] using hL₀ (tailInclusion z)
      have hsourceChart (z : Interval × Tail) :
          Fref (z.1,⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩) ∈ sharedComplexChart.source := by
        have hparamV : (⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.property.1]
          exact z.2.property.2.trans_lt hdr
        exact (hVtail z.1 _ hparamV).1
      have hsourceSmall (z : Interval × Tail) : ‖Complex.exp (L z)‖<complexRadius := by
        have hparamV : (⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.property.1]
          exact z.2.property.2.trans_lt hdr
        rw [hL]
        exact (hVtail z.1 _ hparamV).2.1
      have hsourceUnit (z : Interval × Tail) : ‖Complex.exp (L z)‖<1 := by
        have hparamV : (⟨z.2.val,z.2.property.1.le,
            z.2.property.2.trans hd1.le⟩ : Interval) ∈ V := by
          apply hball
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |z.2.val-0|<r
          rw [sub_zero,abs_of_pos z.2.property.1]
          exact z.2.property.2.trans_lt hdr
        rw [hL]
        exact (hVtail z.1 _ hparamV).2.2
      let collarWeight : C(Tail,Interval) := {
        toFun := fun t => ⟨min 1 (max 0 (2*t.val/d-1)),
          le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩
        continuous_toFun := by fun_prop }
      have hweightOuter : collarWeight ⟨d,hd,le_rfl⟩=1 := by
        apply Subtype.ext
        change min 1 (max 0 (2*d/d-1))=1
        rw [mul_div_cancel_right₀ _ (ne_of_gt hd)]
        norm_num
      have hweightInner (t : Tail) (ht : t.val≤d/2) : collarWeight t=0 := by
        apply Subtype.ext
        change min 1 (max 0 (2*t.val/d-1))=0
        have hh : 2*t.val/d-1≤0 := by
          have he : 2*t.val≤d := by linarith only [ht]
          exact sub_nonpos.mpr ((div_le_one hd).mpr he)
        rw [max_eq_left hh]
        norm_num
      let boundaryLog : C(Interval × Tail,ℂ) := {
        toFun := fun z => (1-(z.1.val:ℂ))*L (0,z.2)+(z.1.val:ℂ)*L (1,z.2)
        continuous_toFun := by fun_prop }
      let targetLog : C(Interval × Tail,ℂ) := {
        toFun := fun z => (1-((collarWeight z.2).val:ℂ))*boundaryLog z+
          ((collarWeight z.2).val:ℂ)*L z
        continuous_toFun := by fun_prop }
      let H : C(Interval × (Interval × Tail),ℂ) := {
        toFun := fun z => Complex.exp ((1-(z.1.val:ℂ))*L z.2+
          (z.1.val:ℂ)*targetLog z.2)
        continuous_toFun := by fun_prop }
      have hboundarySmall (z : Interval × Tail) :
          ‖Complex.exp (boundaryLog z)‖<complexRadius :=
        (hcomplexExpConvexNorm (L (0,z.2)) (L (1,z.2)) z.1).trans_lt
          (max_lt (hsourceSmall (0,z.2)) (hsourceSmall (1,z.2)))
      have htargetSmall (z : Interval × Tail) :
          ‖Complex.exp (targetLog z)‖<complexRadius :=
        (hcomplexExpConvexNorm (boundaryLog z) (L z) (collarWeight z.2)).trans_lt
          (max_lt (hboundarySmall z) (hsourceSmall z))
      have htargetBoundary (τ : Interval) (t : Tail) (hτ : τ=0 ∨ τ=1) :
          targetLog (τ,t)=L (τ,t) := by
        have hb : boundaryLog (τ,t)=L (τ,t) := by
          rcases hτ with rfl | rfl <;> simp [boundaryLog]
        change (1-((collarWeight t).val:ℂ))*boundaryLog (τ,t)+
          ((collarWeight t).val:ℂ)*L (τ,t)=L (τ,t)
        rw [hb]
        ring
      have htargetOuter (τ : Interval) : targetLog (τ,⟨d,hd,le_rfl⟩)=L (τ,⟨d,hd,le_rfl⟩) := by
        change (1-((collarWeight ⟨d,hd,le_rfl⟩).val:ℂ))*_+
          ((collarWeight ⟨d,hd,le_rfl⟩).val:ℂ)*_= _
        rw [hweightOuter]
        simp
      refine ⟨d,hd,hd1,L,H,hdε,hboundaryOldFree,hsourceChart,hL,hsourceUnit,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        have hs : ‖H z‖<complexRadius :=
          (hcomplexExpConvexNorm (L z.2) (targetLog z.2) z.1).trans_lt
            (max_lt (hsourceSmall z.2) (htargetSmall z.2))
        refine ⟨hcomplexBall ?_,Complex.exp_ne_zero _⟩
        simpa only [Metric.mem_ball,dist_zero_right] using hs
      · intro z
        let m : ℝ := max ‖Complex.exp (L z.2)‖
          (max ‖Complex.exp (L (0,z.2.2))‖ ‖Complex.exp (L (1,z.2.2))‖)
        have hsource : ‖Complex.exp (L z.2)‖ ≤ m := le_max_left _ _
        have hboundary : ‖Complex.exp (boundaryLog z.2)‖ ≤ m :=
          (hcomplexExpConvexNorm (L (0,z.2.2)) (L (1,z.2.2)) z.2.1).trans
            (le_max_right _ _)
        have htarget : ‖Complex.exp (targetLog z.2)‖ ≤ m :=
          (hcomplexExpConvexNorm (boundaryLog z.2) (L z.2) (collarWeight z.2.2)).trans
            (max_le hboundary hsource)
        exact (hcomplexExpConvexNorm (L z.2) (targetLog z.2) z.1).trans
          (max_le hsource htarget)
      · intro z
        rfl
      · intro z
        change Complex.exp ((1-(0:ℂ))*L z+(0:ℂ)*_)=_
        simp
      · intro η τ t hτ
        change Complex.exp ((1-(η.val:ℂ))*L (τ,t)+(η.val:ℂ)*targetLog (τ,t))=_
        rw [htargetBoundary τ t hτ]
        congr 1
        ring
      · intro η τ
        change Complex.exp ((1-(η.val:ℂ))*L (τ,⟨d,hd,le_rfl⟩)+
          (η.val:ℂ)*targetLog (τ,⟨d,hd,le_rfl⟩))=_
        rw [htargetOuter]
        congr 1
        ring
      · intro τ t ht
        change Complex.exp ((1-(1:ℂ))*L (τ,t)+(1:ℂ)*targetLog (τ,t))=_
        simp only [sub_self,zero_mul,one_mul,zero_add]
        change Complex.exp ((1-((collarWeight t).val:ℂ))*boundaryLog (τ,t)+
          ((collarWeight t).val:ℂ)*L (τ,t))=_
        rw [hweightInner t ht]
        simp [boundaryLog]
  have hFrefEnds (τ : Interval) : Fref (τ,0)=b.val.map 1 ∧ Fref (τ,1)=b.val.map 0 := by
    as_aux_lemma =>
      have hσ₀ : unitInterval.symm (0:Interval)=1 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
      have hσ₁ : unitInterval.symm (1:Interval)=0 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
      change F (τ,unitInterval.symm 0)=_ ∧ F (τ,unitInterval.symm 1)=_
      rw [hσ₀,hσ₁]
      exact ⟨(hFends τ).2,(hFends τ).1⟩
  have hFrefMarks (τ t : Interval) (ht₀ : t≠0) (ht₁ : t≠1) :
      Fref (τ,t) ∉ (M.cover.branch : Set S) :=
    hFmarks τ (unitInterval.symm t) (hsymmNeZero t ht₁) (hsymmNeOne t ht₀)
  have hactualSharedReflectedBoundaryLogStripes (hshared : b.val.map 1=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ L : C(Interval × Ioc (0:ℝ) d,ℂ),
      ∃ H : C(Interval × (Interval × Ioc (0:ℝ) d),ℂ),
      ∃ n₀ n₁ : ℤ,
        (∀ z : Interval × Ioc (0:ℝ) d,Fref (z.1,⟨z.2.val,z.2.property.1.le,
          z.2.property.2.trans hd1.le⟩) ∈ sharedComplexChart.source) ∧
        (∀ z,Complex.exp (L z)=sharedComplexChart
          (Fref (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩))) ∧
        (∀ z,H z ∈ sharedComplexChart.target ∧ H z≠0) ∧
        (∀ z,‖H z‖<1) ∧
        (∀ z,‖H z‖≤ max
          ‖sharedComplexChart (Fref (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
          (max ‖sharedComplexChart (Fref (0,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
            ‖sharedComplexChart (Fref (1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖)) ∧
        (∀ t,(L (0,t)).im ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi))
          (Real.pi+(n₀:ℝ)*(2*Real.pi)) ∧
          (L (1,t)).im ∈ Ioo (-Real.pi+(n₁:ℝ)*(2*Real.pi))
          (Real.pi+(n₁:ℝ)*(2*Real.pi))) ∧
        (∀ z,H (0,z)=Complex.exp (L z)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → H (η,(τ,t))=Complex.exp (L (τ,t))) ∧
        (∀ η τ,H (η,(τ,⟨d,hd,le_rfl⟩))=Complex.exp (L (τ,⟨d,hd,le_rfl⟩))) ∧
        (∀ (τ : Interval) (t : Ioc (0:ℝ) d),t.val≤d/2 → H (1,(τ,t))=
          Complex.exp ((1-(τ.val:ℂ))*L (0,t)+(τ.val:ℂ)*L (1,t))) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,L,H,hdε,hboundaryOldFree,hsourceChart,hL,hsourceUnit,
        hHrange,hHnorm,hHformula,hHzero,hHboundary,hHouter,hHinner⟩ :=
        hactualSharedReflectedAffineLogBoundaryInterpolation hshared
      let Tail := Ioc (0:ℝ) d
      let left : C(Tail,ℂ) := L.comp {
        toFun := fun t => (0,t)
        continuous_toFun := by fun_prop }
      let right : C(Tail,ℂ) := L.comp {
        toFun := fun t => (1,t)
        continuous_toFun := by fun_prop }
      have hleftSlit (t : Tail) : Complex.exp (left t) ∈ Complex.slitPlane := by
        have hn : ‖sharedComplexChart (Fref (0,⟨t.val,t.property.1.le,
            t.property.2.trans hd1.le⟩))‖<1 := hL (0,t) ▸ hsourceUnit (0,t)
        have ha := hactualSmallComplexChartAxis
          (Fref (0,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩)) (hsourceChart (0,t)) hn
        change Complex.exp (L (0,t)) ∈ Complex.slitPlane
        rw [hL]
        by_contra hh
        exact (hboundaryOldFree t).1 (ha.mpr hh)
      have hrightSlit (t : Tail) : Complex.exp (right t) ∈ Complex.slitPlane := by
        have hn : ‖sharedComplexChart (Fref (1,⟨t.val,t.property.1.le,
            t.property.2.trans hd1.le⟩))‖<1 := hL (1,t) ▸ hsourceUnit (1,t)
        have ha := hactualSmallComplexChartAxis
          (Fref (1,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩)) (hsourceChart (1,t)) hn
        change Complex.exp (L (1,t)) ∈ Complex.slitPlane
        rw [hL]
        by_contra hh
        exact (hboundaryOldFree t).2 (ha.mpr hh)
      obtain ⟨n₀,hleftLog,hleftStripe⟩ := hcontinuousLogStripe d hd left hleftSlit
      obtain ⟨n₁,hrightLog,hrightStripe⟩ := hcontinuousLogStripe d hd right hrightSlit
      refine ⟨d,hd,hd1,L,H,n₀,n₁,hsourceChart,hL,hHrange,?_,?_,?_,hHzero,
        hHboundary,hHouter,hHinner⟩
      · intro z
        exact (hHnorm z).trans_lt (max_lt (hsourceUnit z.2)
          (max_lt (hsourceUnit (0,z.2.2)) (hsourceUnit (1,z.2.2))))
      · intro z
        simpa only [hL] using hHnorm z
      · intro t
        exact ⟨hleftStripe t,hrightStripe t⟩
  have hactualSharedReflectedAffineMarkedPointExtension (hshared : b.val.map 1=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),∃ n₀ n₁ : ℤ,
      ∃ L : C(Interval × Ioc (0:ℝ) d,ℂ),
      ∃ K : C(Interval × (Interval × Icc (0:ℝ) d),S),
        (∀ t,(L (0,t)).im ∈ Ioo (-Real.pi+(n₀:ℝ)*(2*Real.pi)) (Real.pi+(n₀:ℝ)*(2*Real.pi)) ∧
          (L (1,t)).im ∈ Ioo (-Real.pi+(n₁:ℝ)*(2*Real.pi)) (Real.pi+(n₁:ℝ)*(2*Real.pi))) ∧
        (∀ z,K z ∈ sharedComplexChart.source) ∧
        (∀ z,‖sharedComplexChart (K z)‖<1) ∧
        (∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0) ∧
        (∀ z,0<z.2.2.val → K z ∉ (M.cover.branch : Set S)) ∧
        (∀ z,K (0,z)=Fref (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩)) ∧
        (∀ η τ,K (η,(τ,⟨d,hd.le,le_rfl⟩))=Fref (τ,⟨d,hd.le,hd1.le⟩)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → K (η,(τ,t))=
          Fref (τ,⟨t.val,t.property.1,t.property.2.trans hd1.le⟩)) ∧
        (∀ (τ : Interval) (t : Icc (0:ℝ) d) (ht : 0<t.val),t.val≤d/2 →
          sharedComplexChart (K (1,(τ,t)))=Complex.exp
            ((1-(τ.val:ℂ))*L (0,⟨t.val,ht,t.property.2⟩)+(τ.val:ℂ)*L (1,⟨t.val,ht,t.property.2⟩))) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,L,H,n₀,n₁,hsource,hL,hHrange,hHunit,hHsourceNorm,hstripes,
        hHzero,hHboundary,hHouter,hHinner⟩ := hactualSharedReflectedBoundaryLogStripes hshared
      let K : C(Interval × (Interval × Ioc (0:ℝ) d),S) := {
        toFun := fun z => sharedComplexChart.symm (H z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.symm.continuousAt (hHrange z).1).comp H.continuous.continuousAt }
      have hKchart (z : Interval × (Interval × Ioc (0:ℝ) d)) : sharedComplexChart (K z)=H z :=
        sharedComplexChart.right_inv (hHrange z).1
      have hKsource (z : Interval × (Interval × Ioc (0:ℝ) d)) : K z ∈ sharedComplexChart.source :=
        sharedComplexChart.map_target (hHrange z).1
      have hKne (z : Interval × (Interval × Ioc (0:ℝ) d)) : K z≠af 0 := by
        intro he
        exact (hHrange z).2 ((hKchart z).symm.trans ((congrArg sharedComplexChart he).trans hsharedComplexStart))
      have hKmarks (z : Interval × (Interval × Ioc (0:ℝ) d)) : K z ∉ (M.cover.branch : Set S) := by
        intro hm
        have hc : K z ∈ sharedMarkCarrier := (hsharedEndpointChartSource ▸ hKsource z).2
        exact hc ⟨hm,hKne z⟩
      have hKnorm (z : Interval × (Interval × Ioc (0:ℝ) d)) :
          ‖sharedComplexChart (K z)‖≤ max
            ‖sharedComplexChart (Fref (z.2.1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
            (max ‖sharedComplexChart (Fref (0,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖
              ‖sharedComplexChart (Fref (1,⟨z.2.2.val,z.2.2.property.1.le,z.2.2.property.2.trans hd1.le⟩))‖) := by
        rw [hKchart]
        exact hHsourceNorm z
      have hKinitial (z : Interval × Ioc (0:ℝ) d) : K (0,z)=
          Fref (z.1,⟨z.2.val,z.2.property.1.le,z.2.property.2.trans hd1.le⟩) := by
        change sharedComplexChart.symm (H (0,z))=_
        rw [hHzero,hL]
        exact sharedComplexChart.left_inv (hsource z)
      have hKouter (η τ : Interval) : K (η,(τ,⟨d,hd,le_rfl⟩))=Fref (τ,⟨d,hd.le,hd1.le⟩) := by
        change sharedComplexChart.symm (H (η,(τ,⟨d,hd,le_rfl⟩)))=_
        rw [hHouter,hL]
        exact sharedComplexChart.left_inv (hsource _)
      have hKboundary (η τ : Interval) (t : Ioc (0:ℝ) d) (hτ : τ=0 ∨ τ=1) :
          K (η,(τ,t))=Fref (τ,⟨t.val,t.property.1.le,t.property.2.trans hd1.le⟩) := by
        change sharedComplexChart.symm (H (η,(τ,t)))=_
        rw [hHboundary η τ t hτ,hL]
        exact sharedComplexChart.left_inv (hsource _)
      let Tail := Ioc (0:ℝ) d
      let ClosedTail := Icc (0:ℝ) d
      let X := Interval × (Interval × ClosedTail)
      let PC : C(Interval × (Interval × Tail),ℂ) := {
        toFun := fun z => sharedComplexChart (K z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.continuousAt (hKsource z)).comp K.continuous.continuousAt }
      let source : C(X,S) := {
        toFun := fun z => Fref (z.2.1,⟨z.2.2.val,z.2.2.property.1,
          z.2.2.property.2.trans hd1.le⟩)
        continuous_toFun := by fun_prop }
      have hsourceChart (z : X) : source z ∈ sharedComplexChart.source := by
        by_cases ht : 0<z.2.2.val
        · let t : Tail := ⟨z.2.2.val,ht,z.2.2.property.2⟩
          have he := hKinitial (z.2.1,t)
          exact he ▸ hKsource (0,(z.2.1,t))
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          have hparam : (⟨z.2.2.val,z.2.2.property.1,
              z.2.2.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext he
          change Fref (z.2.1,_) ∈ sharedComplexChart.source
          rw [hparam,(hFrefEnds z.2.1).1,hshared]
          exact hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart
      let sourceC : C(X,ℂ) := {
        toFun := fun z => sharedComplexChart (source z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.continuousAt (hsourceChart z)).comp source.continuous.continuousAt }
      let leftSourceC : C(X,ℂ) := sourceC.comp {
        toFun := fun z => (z.1,(0,z.2.2))
        continuous_toFun := by fun_prop }
      let rightSourceC : C(X,ℂ) := sourceC.comp {
        toFun := fun z => (z.1,(1,z.2.2))
        continuous_toFun := by fun_prop }
      let majorant : C(X,ℝ) := {
        toFun := fun z => max ‖sourceC z‖ (max ‖leftSourceC z‖ ‖rightSourceC z‖)
        continuous_toFun := by fun_prop }
      let extPC : X → ℂ := fun z => if ht : 0<z.2.2.val then
        PC (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)) else 0
      have hnormBound (z : X) : ‖extPC z‖ ≤ majorant z := by
        by_cases ht : 0<z.2.2.val
        · dsimp only [extPC]
          rw [dif_pos ht]
          exact hKnorm (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩))
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          simp only [extPC,dif_neg ht,norm_zero,majorant,ContinuousMap.coe_mk,he,
            zero_mul,add_zero]
          exact (norm_nonneg _).trans (le_max_left _ _)
      have hzeroValues (z : X) (hz : z.2.2.val=0) : extPC z=0 ∧ majorant z=0 := by
        have hparam : (⟨z.2.2.val,z.2.2.property.1,
            z.2.2.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext hz
        constructor
        · simp only [extPC,hz,lt_self_iff_false,dif_neg,not_false_eq_true]
        · change max ‖sharedComplexChart (Fref (z.2.1,
              ⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hd1.le⟩))‖
            (max ‖sharedComplexChart (Fref (0,
              ⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hd1.le⟩))‖
              ‖sharedComplexChart (Fref (1,
                ⟨z.2.2.val,z.2.2.property.1,z.2.2.property.2.trans hd1.le⟩))‖)=0
          simp only [hparam,(hFrefEnds z.2.1).1,(hFrefEnds 0).1,(hFrefEnds 1).1,hshared,
            hsharedComplexStart,norm_zero,max_self]
      have hextContinuous : Continuous extPC := by
        apply continuous_iff_continuousAt.mpr
        intro z
        by_cases hz : 0<z.2.2.val
        · let a : ℝ := z.2.2.val/2
          have ha : 0<a := by dsimp [a]; positivity
          have haz : a<z.2.2.val := by dsimp [a]; linarith only [hz]
          have had : a≤d := haz.le.trans z.2.2.property.2
          let clamp : C(X,Interval × (Interval × Tail)) := {
            toFun := fun w => (w.1,(w.2.1,⟨max w.2.2.val a,
              ha.trans_le (le_max_right _ _),max_le w.2.2.property.2 had⟩))
            continuous_toFun := by fun_prop }
          have hopen : IsOpen {w : X | a<w.2.2.val} :=
            isOpen_lt continuous_const (by fun_prop)
          have hnear : ∀ᶠ w : X in 𝓝 z,a<w.2.2.val := hopen.mem_nhds haz
          apply (PC.continuous.comp clamp.continuous).continuousAt.congr_of_eventuallyEq
          filter_upwards [hnear] with w hw
          dsimp only [extPC]
          rw [dif_pos (ha.trans hw)]
          change PC (w.1,(w.2.1,⟨w.2.2.val,ha.trans hw,w.2.2.property.2⟩))=
            PC (w.1,(w.2.1,⟨max w.2.2.val a,
              ha.trans_le (le_max_right _ _),max_le w.2.2.property.2 had⟩))
          apply congrArg PC
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · rfl
            · apply Subtype.ext
              exact (max_eq_left hw.le).symm
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt hz) z.2.2.property.1
          have hzero := hzeroValues z he
          have htend : Filter.Tendsto majorant (𝓝 z) (𝓝 (0:ℝ)) := by
            simpa only [hzero.2] using (majorant.continuous.continuousAt (x := z)).tendsto
          change Filter.Tendsto extPC (𝓝 z) (𝓝 (extPC z))
          rw [hzero.1]
          exact squeeze_zero_norm hnormBound htend
      let EC : C(X,ℂ) := ⟨extPC,hextContinuous⟩
      have hECtarget (z : X) : EC z ∈ sharedComplexChart.target := by
        by_cases ht : 0<z.2.2.val
        · change extPC z ∈ _
          dsimp only [extPC]
          rw [dif_pos ht]
          exact sharedComplexChart.map_source (hKsource
            (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)))
        · change extPC z ∈ _
          dsimp only [extPC]
          rw [dif_neg ht]
          exact hsharedComplexTarget
      let result : C(X,S) := {
        toFun := fun z => sharedComplexChart.symm (EC z)
        continuous_toFun := by
          apply continuous_iff_continuousAt.mpr
          intro z
          exact (sharedComplexChart.symm.continuousAt (hECtarget z)).comp EC.continuous.continuousAt }
      have hresultPositive (z : X) (ht : 0<z.2.2.val) : result z=
          K (z.1,(z.2.1,⟨z.2.2.val,ht,z.2.2.property.2⟩)) := by
        change sharedComplexChart.symm (extPC z)=_
        dsimp only [extPC]
        rw [dif_pos ht]
        exact sharedComplexChart.left_inv (hKsource _)
      have hresultZero (z : X) (ht : z.2.2.val=0) : result z=af 0 := by
        change sharedComplexChart.symm (extPC z)=af 0
        rw [(hzeroValues z ht).1,←hsharedComplexStart]
        exact sharedComplexChart.left_inv
          (hsharedEndpointChartSource.symm ▸ hsharedEndpointNeighborhoodStart)
      refine ⟨d,hd,hd1,n₀,n₁,L,result,hstripes,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        exact sharedComplexChart.map_target (hECtarget z)
      · intro z
        by_cases ht : 0<z.2.2.val
        · rw [hresultPositive z ht,hKchart]
          exact hHunit _
        · have he : z.2.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.2.property.1
          rw [hresultZero z he,hsharedComplexStart,norm_zero]
          norm_num
      · intro η τ
        exact hresultZero _ rfl
      · intro z ht
        rw [hresultPositive z ht]
        exact hKmarks _
      · intro z
        by_cases ht : 0<z.2.val
        · rw [hresultPositive (0,z) ht]
          exact hKinitial _
        · have he : z.2.val=0 := le_antisymm (le_of_not_gt ht) z.2.property.1
          rw [hresultZero (0,z) he]
          have hp : (⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩ : Interval)=0 :=
            Subtype.ext he
          rw [hp,(hFrefEnds z.1).1,hshared]
      · intro η τ
        rw [hresultPositive (η,(τ,⟨d,hd.le,le_rfl⟩)) hd]
        exact hKouter η τ
      · intro η τ t hτ
        by_cases ht : 0<t.val
        · rw [hresultPositive (η,(τ,t)) ht]
          exact hKboundary η τ ⟨t.val,ht,t.property.2⟩ hτ
        · have he : t.val=0 := le_antisymm (le_of_not_gt ht) t.property.1
          rw [hresultZero (η,(τ,t)) he]
          have hp : (⟨t.val,t.property.1,t.property.2.trans hd1.le⟩ : Interval)=0 := Subtype.ext he
          rw [hp,(hFrefEnds τ).1,hshared]
      · intro τ t ht hhalf
        rw [hresultPositive (1,(τ,t)) ht]
        rw [hKchart]
        exact hHinner τ ⟨t.val,ht,t.property.2⟩ hhalf
  have hactualSharedReflectedGlobalFiniteCornerDeformation (hshared : b.val.map 1=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),∃ lo hi : ℤ,
      ∃ γ : {k : ℤ // k ∈ Finset.Icc lo (hi-1)} → C(Ioc (0:ℝ) d,Interval),
      ∃ HG : C(Interval × (Interval × Interval),S),
        (∀ k t,0<(γ k t).val ∧ (γ k t).val<1) ∧
        (∀ k,IsEmbedding (fun t => (γ k t,t))) ∧
        (∀ t,Function.Injective (fun k => γ k t)) ∧
        (∀ τ : Interval,HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈sharedComplexChart.source ∧
          ‖sharedComplexChart (HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))‖<1) ∧
        (∀ k,(sharedComplexChart (HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).re<0 ∧ ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
          (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
          v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
          γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
          w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
          (sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
          (sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
          ((sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0 ↔
            ¬(sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0)) ∧
        (∀ (k : {k : ℤ // k∈Finset.Icc lo (hi-1)}) (C : OpenPartialHomeomorph S (ℝ × ℝ)),
          HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
            ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source →
          (∀ x∈C.source,x∈a.val.image ↔ (C x).1=0) →
          ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
            (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
            v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
            γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
            w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
            HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            (C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            (C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            ((C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0 ↔
              ¬(C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0)) ∧
        (∀ z,HG (0,z)=Fref z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        (∀ η τ t,d<t.val → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ (τ t : Interval) (ht₀ : t≠0) (ht : t.val≤d/2),
          HG (1,(τ,t)) ∈ a.val.image ↔
            ∃ k : {k : ℤ // k ∈ Finset.Icc lo (hi-1)},τ=γ k
              ⟨t.val,lt_of_le_of_ne t.property.1 (by intro he; exact ht₀ (Subtype.ext he.symm)),
                ht.trans (half_le_self hd.le)⟩) ∧
        ∀ k,∃ f : Path (af 0) (HG (1,(γ k
          ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,by linarith⟩))),
          range f⊆a.val.image ∧
          (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
          ∃ Γ : C({t : Interval // t≠0},Interval),
            Γ ⟨1,by simp⟩=γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ ∧
            (∀ t : {t : Interval // t≠0},Γ t=γ k
              ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
                (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
                (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩) ∧
          ∃ P : Path ((0,0) : ℝ × ℝ)
            ((γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,d/2),
            IsEmbedding P ∧
            (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,
              ⟨(d/2)*t.val.val,mul_nonneg (half_pos hd).le t.val.property.1,
                ((mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans
                  (half_le_self hd.le)).trans hd1.le⟩))) ∧
            (∀ t : {t : Interval // t≠0},P t.val=
              (t.val.val*(Γ t).val,(d/2)*t.val.val)) ∧
            (∀ t : {t : Interval // t≠0},0<(Γ t).val ∧ (Γ t).val<1) ∧
            (∀ t : Interval,(P t).2=(d/2)*t.val) ∧
          ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
          ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
            c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
            (∀ t,(v t).val=b.val.map (unitInterval.symm
              ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
                ((mul_le_of_le_one_right (half_pos hd).le t.property.2).trans
                  (half_le_self hd.le)).trans hd1.le⟩)) ∧
            (∀ t,(w t).val=HG (1,
              (⟨t.val*(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,
                mul_nonneg t.property.1 (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).property.1,
                (mul_le_of_le_one_right t.property.1
                  (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).property.2).trans t.property.2⟩,
                ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))) ∧
            α.Homotopic (v.trans w) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,n₀,n₁,L,K,hstripes,hKsource,hKunit,hKzero,hKmarks,hKinitial,
        hKouter,hKboundary,hKinner⟩ := hactualSharedReflectedAffineMarkedPointExtension hshared
      let left : C(Ioc (0:ℝ) d,ℝ) := {
        toFun := fun t => (L (0,t)).im
        continuous_toFun := by fun_prop }
      let right : C(Ioc (0:ℝ) d,ℝ) := {
        toFun := fun t => (L (1,t)).im
        continuous_toFun := by fun_prop }
      obtain ⟨lo,hi,γ,hstrict,hlevels,hgraph,hsolve⟩ := hfiniteUnorderedLevels left right n₀ n₁
        (fun t => (hstripes t).1) (fun t => (hstripes t).2)
      have hγinjective (t : Ioc (0:ℝ) d) : Function.Injective (fun k => γ k t) := by
        intro j k he
        have hj := hlevels j t
        have hk := hlevels k t
        change γ j t=γ k t at he
        rw [he] at hj
        have hc : (j.val:ℝ)=(k.val:ℝ) := mul_right_cancel₀
          (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos))
          (by linarith only [hj,hk])
        exact Subtype.ext (Int.cast_injective hc)
      let clamp : C(Interval,Icc (0:ℝ) d) := {
        toFun := fun t => ⟨min t.val d,le_min t.property.1 hd.le,min_le_right _ _⟩
        continuous_toFun := by fun_prop }
      let X := Interval × (Interval × Interval)
      let first : C(X,S) := K.comp {
        toFun := fun z => (z.1,(z.2.1,clamp z.2.2))
        continuous_toFun := by fun_prop }
      let outside : C(X,S) := Fref.comp {
        toFun := fun z => z.2
        continuous_toFun := continuous_snd }
      let A : Set X := {z | z.2.2.val≤d}
      have hjoin (z : X) (hz : z ∈ frontier A) : first z=outside z := by
        have hv : z.2.2.val=d := (frontier_le_subset_eq
          (by fun_prop : Continuous (fun w : X => w.2.2.val)) continuous_const) hz
        have hc : clamp z.2.2=⟨d,hd.le,le_rfl⟩ := by
          apply Subtype.ext
          simp only [clamp,ContinuousMap.coe_mk,hv,min_self]
        change K (z.1,(z.2.1,clamp z.2.2))=Fref (z.2.1,z.2.2)
        rw [hc,hKouter]
        have ht : (⟨d,hd.le,hd1.le⟩ : Interval)=z.2.2 := Subtype.ext hv.symm
        rw [ht]
      let HG : C(X,S) := ⟨A.piecewise first outside,
        Continuous.piecewise hjoin first.continuous outside.continuous⟩
      have hinside (z : X) (hz : z.2.2.val≤d) : HG z=K (z.1,(z.2.1,clamp z.2.2)) :=
        Set.piecewise_eq_of_mem A first outside hz
      have houtside (z : X) (hz : ¬z.2.2.val≤d) : HG z=Fref z.2 :=
        Set.piecewise_eq_of_notMem A first outside hz
      have hparam (t : Interval) (ht : t.val≤d) :
          (⟨(clamp t).val,(clamp t).property.1,
            (clamp t).property.2.trans hd1.le⟩ : Interval)=t :=
        Subtype.ext (min_eq_left ht)
      have hclampZero : clamp 0=⟨0,le_rfl,hd.le⟩ := by
        apply Subtype.ext
        exact min_eq_left hd.le
      have hSeamActual (τ : Interval) :
          HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))=
            K (1,(τ,⟨d/2,(half_pos hd).le,half_le_self hd.le⟩)) := by
        rw [hinside _ (half_le_self hd.le)]
        apply congrArg K
        apply Prod.ext
        · rfl
        apply Prod.ext
        · rfl
        apply Subtype.ext
        exact min_eq_left (half_le_self hd.le)
      have hSeamChartData (τ : Interval) :
          HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈sharedComplexChart.source ∧
            ‖sharedComplexChart (HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))‖<1 := by
        rw [hSeamActual]
        exact ⟨hKsource _,hKunit _⟩
      have hSeamComplexFormula (τ : Interval) :
          sharedComplexChart (HG (1,(τ,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))=
            Complex.exp ((1-(τ.val:ℂ))*L (0,⟨d/2,half_pos hd,half_le_self hd.le⟩)+
              (τ.val:ℂ)*L (1,⟨d/2,half_pos hd,half_le_self hd.le⟩)) := by
        rw [hinside _ (half_le_self hd.le)]
        have he : clamp ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩=
            ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩ := by
          apply Subtype.ext
          exact min_eq_left (half_le_self hd.le)
        rw [he]
        exact hKinner τ ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩ (half_pos hd) le_rfl
      have hSeamSides (k : {k : ℤ // k∈Finset.Icc lo (hi-1)}) :
          (sharedComplexChart (HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).re<0 ∧
          ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
            (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
            v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
            γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
            w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
            (sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
            (sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im≠0 ∧
            ((sharedComplexChart (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0 ↔
              ¬(sharedComplexChart (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).im<0) := by
        let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,half_le_self hd.le⟩
        have hlevel := hlevels k t
        change (1-(γ k t).val)*(L (0,t)).im+(γ k t).val*(L (1,t)).im=
          Real.pi+(k.val:ℝ)*(2*Real.pi) at hlevel
        have him : ((1-((γ k t).val:ℂ))*L (0,t)+((γ k t).val:ℂ)*L (1,t)).im=
            Real.pi+(k.val:ℝ)*(2*Real.pi) := by
          simpa [Complex.mul_im,Complex.sub_im] using hlevel
        have hNegativeReal : (sharedComplexChart (HG (1,(γ k t,
            ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).re<0 := by
          rw [hSeamComplexFormula,Complex.exp_re,him,Real.cos_add_int_mul_two_pi,Real.cos_pi]
          have hp := Real.exp_pos (((1-((γ k t).val:ℂ))*L (0,t)+((γ k t).val:ℂ)*L (1,t)).re)
          simpa only [mul_neg_one] using neg_neg_of_pos hp
        have hSlope := CurveComplex.LocalSurgery.actualAffineLogSeamSlopeNonzeroOfStripLevel
          (L (0,t)) (L (1,t)) (γ k t).val n₀ k.val (hstripes t).1 hlevel
        obtain ⟨δ,hδ,hflip⟩ := CurveComplex.LocalSurgery.actualAffineLogSeamCrossesNegativeAxisLocally
          (L (0,t)) (L (1,t)) (γ k t).val k.val hSlope hlevel
        refine ⟨hNegativeReal,δ,hδ,?_⟩
        intro v w hvlo hvu huw hwhi
        rw [hSeamComplexFormula,hSeamComplexFormula]
        exact hflip v.val w.val hvlo hvu huw hwhi
      have hSeamAdaptedSides (k : {k : ℤ // k∈Finset.Icc lo (hi-1)})
          (C : OpenPartialHomeomorph S (ℝ × ℝ))
          (hpC : HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
            ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source)
          (hCaxis : ∀ x∈C.source,x∈a.val.image ↔ (C x).1=0) :
          ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
            (γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val-δ<v.val →
            v<γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ →
            γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩<w →
            w.val<(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩).val+δ →
            HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩))∈C.source ∧
            (C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            (C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1≠0 ∧
            ((C (HG (1,(v,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0 ↔
              ¬(C (HG (1,(w,⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩)))).1<0) := by
        let r : Interval := ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩
        let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,half_le_self hd.le⟩
        let β : C(Interval,S) := ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩
        obtain ⟨hneg,δ,hδ,hflip⟩ := hSeamSides k
        have hdata := hSeamChartData (γ k t)
        have hlevel := hlevels k t
        change (1-(γ k t).val)*(L (0,t)).im+(γ k t).val*(L (1,t)).im=
          Real.pi+(k.val:ℝ)*(2*Real.pi) at hlevel
        have him : ((1-((γ k t).val:ℂ))*L (0,t)+((γ k t).val:ℂ)*L (1,t)).im=
            Real.pi+(k.val:ℝ)*(2*Real.pi) := by
          simpa [Complex.mul_im,Complex.sub_im] using hlevel
        have hpointImag : (sharedComplexChart (β (γ k t))).im=0 := by
          change (sharedComplexChart (HG (1,(γ k t,r)))).im=0
          rw [hSeamComplexFormula,Complex.exp_im,him,Real.sin_add_int_mul_two_pi,Real.sin_pi,mul_zero]
        have hpA : β (γ k t)∈a.val.image := by
          apply (hactualSmallComplexChartAxis _ hdata.1 hdata.2).mpr
          change sharedComplexChart (β (γ k t))∉Complex.slitPlane
          have hnegβ : (sharedComplexChart (β (γ k t))).re<0 := hneg
          simp only [Complex.slitPlane,Set.mem_setOf_eq,not_or,not_lt,not_not]
          exact ⟨hnegβ.le,hpointImag⟩
        exact CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel.actualMarkedNegativeComplexSeamTraceChangesSideInEveryAdaptedChart
          M a sharedComplexChart (fun x hx hn => hactualSmallComplexChartAxis x hx hn)
          β (γ k t) hpA hdata.1 hdata.2 hneg C hpC hCaxis δ hδ hflip
      refine ⟨d,hd,hd1,lo,hi,γ,HG,hstrict,hgraph,hγinjective,hSeamChartData,hSeamSides,hSeamAdaptedSides,?_,?_,?_,?_,?_,?_,?_⟩
      · intro z
        by_cases ht : z.2.val≤d
        · rw [hinside (0,z) ht,hKinitial,hparam z.2 ht]
        · exact houtside (0,z) ht
      · intro η τ t hτ
        by_cases ht : t.val≤d
        · rw [hinside (η,(τ,t)) ht,hKboundary η τ (clamp t) hτ,hparam t ht]
        · exact houtside (η,(τ,t)) ht
      · intro η τ t ht
        rcases ht with rfl | rfl
        · rw [hinside (η,(τ,0)) hd.le,hclampZero,hKzero,(hFrefEnds τ).1,hshared]
        · exact houtside (η,(τ,1)) (not_le_of_gt hd1)
      · intro η τ t ht₀ ht₁
        by_cases ht : t.val≤d
        · rw [hinside (η,(τ,t)) ht]
          have hpos : 0<t.val := lt_of_le_of_ne t.property.1
            (by intro he; exact ht₀ (Subtype.ext he.symm))
          exact hKmarks (η,(τ,clamp t)) (lt_min hpos hd)
        · rw [houtside (η,(τ,t)) ht]
          exact hFrefMarks τ t ht₀ ht₁
      · intro η τ t ht
        exact houtside (η,(τ,t)) (not_le_of_gt ht)
      · intro τ t ht₀ htHalf
        have ht : t.val≤d := htHalf.trans (half_le_self hd.le)
        have hpos : 0<t.val := lt_of_le_of_ne t.property.1
          (by intro he; exact ht₀ (Subtype.ext he.symm))
        rw [hinside (1,(τ,t)) ht]
        have hc : (clamp t).val=t.val := min_eq_left ht
        have hcp : 0<(clamp t).val := hc ▸ hpos
        rw [hactualSmallComplexChartAxis _ (hKsource (1,(τ,clamp t))) (hKunit (1,(τ,clamp t))),
          hKinner τ (clamp t) hcp (hc ▸ htHalf),hexpNegativeAxisLevels]
        have him : ((1-(τ.val:ℂ))*L (0,⟨(clamp t).val,hcp,(clamp t).property.2⟩)+
            (τ.val:ℂ)*L (1,⟨(clamp t).val,hcp,(clamp t).property.2⟩)).im=
            (1-τ.val)*left ⟨t.val,hpos,ht⟩+τ.val*right ⟨t.val,hpos,ht⟩ := by
          have he : (⟨(clamp t).val,hcp,(clamp t).property.2⟩ : Ioc (0:ℝ) d)=⟨t.val,hpos,ht⟩ :=
            Subtype.ext hc
          rw [he]
          simp [left,right,Complex.mul_im,Complex.sub_im]
        rw [him]
        exact hsolve ⟨t.val,hpos,ht⟩ τ
      · intro k
        obtain ⟨f,hf,Γ,hΓend,hΓnormalization,P,hP,htrace,hPtrace,hΓstrict,hPsecond⟩ :=
          hActualSharedAffineOriginalContactTailClosesAsEmbeddedConeParameterPath
            d hd hd1 L K hKsource hKunit hKzero hKinner k.val (γ k) (hlevels k) (hstrict k)
        let r : Interval := ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩
        have hend : HG (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,r))=
            K (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
              ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩)) := by
          rw [hinside _ (half_le_self hd.le)]
          apply congrArg K
          apply Prod.ext
          · rfl
          apply Prod.ext
          · rfl
          apply Subtype.ext
          exact min_eq_left (half_le_self hd.le)
        obtain ⟨c,y,z,α,v,w,hc,hαrange,hv,hw,hαtrace,hhom⟩ :=
          hActualSharedAffineContactTailRetainedOriginalBoundaryRoute
            d hd hd1 unitInterval.symm L K hKsource hKunit hKzero hKmarks
            (fun t => (hKboundary 1 0 t (Or.inl rfl)).trans (hFzero _))
            hKinner k.val (γ k) (hlevels k)
        refine ⟨f.cast rfl hend,hf,?_,Γ,hΓend,hΓnormalization,P,hP,?_,hPtrace,hΓstrict,hPsecond,c,y,z,α,v,w,hc,?_,hv,?_,hhom⟩
        · intro t ht
          change f t∉(M.cover.branch : Set S)
          rw [htrace ⟨t,ht⟩]
          exact hKmarks _ (mul_pos (half_pos hd)
            (lt_of_le_of_ne t.property.1 (fun h => ht (Subtype.ext h.symm))))
        · intro t
          change f t.val=HG (1,(Γ t,_))
          rw [htrace t]
          symm
          have ht : (d/2)*t.val.val≤d :=
            (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)
          rw [hinside _ ht]
          apply congrArg K
          apply Prod.ext
          · rfl
          apply Prod.ext
          · rfl
          apply Subtype.ext
          exact min_eq_left ht
        · intro t
          change (α t).val=f t
          by_cases ht : t=0
          · subst t
            exact (congrArg Subtype.val α.source).trans (hc.trans f.source.symm)
          · have hftrace := htrace ⟨t,ht⟩
            rw [hΓnormalization] at hftrace
            exact (hαtrace ⟨t,ht⟩).trans hftrace.symm
        · intro t
          rw [hw t]
          symm
          rw [hinside _ (half_le_self hd.le)]
          apply congrArg K
          apply Prod.ext
          · rfl
          apply Prod.ext
          · rfl
          apply Subtype.ext
          exact min_eq_left (half_le_self hd.le)
  have hactualSharedReflectedFiniteInnerSeam (hshared : b.val.map 1=af 0) :
      ∃ r : Interval,r≠0 ∧ r≠1 ∧ ∃ HG : C(Interval × (Interval × Interval),S),
        (∀ z,HG (0,z)=Fref z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,lo,hi,γ,HG,hstrict,hgraph,hγinjective,hSeamChartData,hSeamSides,hSeamAdaptedSides,hzero,hboundary,hends,hmarks,hExterior,hcontact,hclosedtails⟩ :=
        hactualSharedReflectedGlobalFiniteCornerDeformation hshared
      have hhalf : d/2≤d := half_le_self hd.le
      let r : Interval := ⟨d/2,(half_pos hd).le,hhalf.trans hd1.le⟩
      have hr₀ : r≠0 := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_gt (half_pos hd)) hv
      have hr₁ : r≠1 := by
        intro he
        have hv := congrArg Subtype.val he
        have hr : d/2<1 := hhalf.trans_lt hd1
        exact (ne_of_lt hr) hv
      let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,hhalf⟩
      have hfinite : {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
        apply (Set.finite_range (fun k => γ k t)).subset
        intro τ hτ
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        exact ⟨k,hk.symm⟩
      exact ⟨r,hr₀,hr₁,HG,hzero,hboundary,hends,hmarks,hfinite⟩
  have hactualSharedTerminalFiniteInnerSeam (hshared : b.val.map 1=af 0) :
      ∃ r : Interval,r≠0 ∧ r≠1 ∧ ∃ HG : C(Interval × (Interval × Interval),S),
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
    as_aux_lemma =>
      obtain ⟨r,hr₀,hr₁,R,hzero,hboundary,hends,hmarks,hfinite⟩ :=
        hactualSharedReflectedFiniteInnerSeam hshared
      have hσσ (t : Interval) : unitInterval.symm (unitInterval.symm t)=t := by
        apply Subtype.ext
        change 1-(1-t.val)=t.val
        ring
      have hσ₀ : unitInterval.symm (0:Interval)=1 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
      have hσ₁ : unitInterval.symm (1:Interval)=0 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
      let HG : C(Interval × (Interval × Interval),S) := R.comp {
        toFun := fun z => (z.1,(z.2.1,unitInterval.symm z.2.2))
        continuous_toFun := by fun_prop }
      refine ⟨unitInterval.symm r,hsymmNeZero r hr₁,hsymmNeOne r hr₀,HG,?_,?_,?_,?_,?_⟩
      · intro z
        change R (0,(z.1,unitInterval.symm z.2))=F z
        rw [hzero]
        change F (z.1,unitInterval.symm (unitInterval.symm z.2))=F z
        rw [hσσ]
      · intro η τ t hτ
        change R (η,(τ,unitInterval.symm t))=F (τ,t)
        rw [hboundary η τ (unitInterval.symm t) hτ]
        change F (τ,unitInterval.symm (unitInterval.symm t))=F (τ,t)
        rw [hσσ]
      · intro η τ t ht
        have hs : unitInterval.symm t=0 ∨ unitInterval.symm t=1 := by
          rcases ht with rfl | rfl
          · exact Or.inr hσ₀
          · exact Or.inl hσ₁
        change R (η,(τ,unitInterval.symm t))=F (τ,t)
        rw [hends η τ (unitInterval.symm t) hs]
        change F (τ,unitInterval.symm (unitInterval.symm t))=F (τ,t)
        rw [hσσ]
      · intro η τ t ht₀ ht₁
        exact hmarks η τ (unitInterval.symm t) (hsymmNeZero t ht₁) (hsymmNeOne t ht₀)
      · change {τ : Interval | R (1,(τ,unitInterval.symm (unitInterval.symm r))) ∈ a.val.image}.Finite
        simpa only [hσσ] using hfinite
  have actualPhysicalTraceTransverseOnIncreasingSegment
      (β : C(Interval,S)) (hβ : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) β)
      (x y : Interval) (hxy : x<y) :
      (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) (β.comp (actualIntervalSegment x y)) := by
    as_aux_lemma =>
      intro u hu C hpC hCaxis
      obtain ⟨δ,hδ,hflip⟩ := hβ (actualIntervalSegment x y u) hu C hpC hCaxis
      have hden : 0<y.val-x.val := sub_pos.mpr hxy
      refine ⟨δ/(y.val-x.val),div_pos hδ hden,?_⟩
      intro v w hvlo hvu huw hwhi
      have hform (t : Interval) : (actualIntervalSegment x y t).val=x.val+(y.val-x.val)*t.val := by
        change (1-t.val)*x.val+t.val*y.val=x.val+(y.val-x.val)*t.val
        ring
      have hvuR : v.val<u.val := hvu
      have huwR : u.val<w.val := huw
      have hvnear : (actualIntervalSegment x y u).val-δ<(actualIntervalSegment x y v).val := by
        rw [hform,hform]
        have hh := mul_lt_mul_of_pos_left hvlo hden
        have hcancel : (y.val-x.val)*(δ/(y.val-x.val))=δ := by field_simp
        rw [mul_sub,hcancel] at hh
        nlinarith only [hh]
      have hwnear : (actualIntervalSegment x y w).val<(actualIntervalSegment x y u).val+δ := by
        rw [hform,hform]
        have hh := mul_lt_mul_of_pos_left hwhi hden
        have hcancel : (y.val-x.val)*(δ/(y.val-x.val))=δ := by field_simp
        rw [mul_add,hcancel] at hh
        nlinarith only [hh]
      have hvu' : actualIntervalSegment x y v<actualIntervalSegment x y u := by
        change (actualIntervalSegment x y v).val<(actualIntervalSegment x y u).val
        rw [hform,hform]
        nlinarith only [hden,hvuR]
      have huw' : actualIntervalSegment x y u<actualIntervalSegment x y w := by
        change (actualIntervalSegment x y u).val<(actualIntervalSegment x y w).val
        rw [hform,hform]
        nlinarith only [hden,huwR]
      exact hflip _ _ hvnear hvu' huw' hwnear
  have actualPhysicalTransverseAdjacentIntervalsOppositeSigns
      (γ : C(Interval,S)) (hγ : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) γ)
      (u : Interval) (hu : γ u∈a.val.image)
      (C : OpenPartialHomeomorph S (ℝ × ℝ)) (hpC : γ u∈C.source)
      (hCa : ∀ x∈C.source,x∈a.val.image ↔ (C x).1=0)
      (g : C(Interval,ℝ)) (c : ℝ) (hc : c≠0)
      (hg : ∀ t,g t=(C (γ t)).1/c)
      (x y sl sr : Interval) (hxu : x<u) (huy : u<y)
      (hsl : sl∈Set.Ioo x u) (hsr : sr∈Set.Ioo u y)
      (hleft : ∀ z,x<z → z<u → g z≠0)
      (hright : ∀ z,u<z → z<y → g z≠0) :
      g sl<0 ↔ ¬g sr<0 := by
    as_aux_lemma =>
      obtain ⟨δ,hδ,hflip⟩ := hγ u hu C hpC hCa
      have hlo : max (x : ℝ) ((u : ℝ)-δ/2) < (u : ℝ) :=
        max_lt (show (x : ℝ) < (u : ℝ) from hxu) (by linarith only [hδ])
      obtain ⟨v,hv0,hv1⟩ := exists_between hlo
      have hvI : v ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact x.property.1.trans (le_max_left _ _ |>.trans hv0.le)
        · exact hv1.le.trans u.property.2
      let vI : Interval := ⟨v,hvI⟩
      have hhi : (u : ℝ) < min (y : ℝ) ((u : ℝ)+δ/2) :=
        lt_min (show (u : ℝ) < (y : ℝ) from huy) (by linarith only [hδ])
      obtain ⟨w,hw0,hw1⟩ := exists_between hhi
      have hwI : w ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact u.property.1.trans hw0.le
        · exact hw1.le.trans ((min_le_left _ _).trans y.property.2)
      let wI : Interval := ⟨w,hwI⟩
      have hvnear : (u : ℝ)-δ < vI := by
        change (u : ℝ)-δ < v
        have hh := (le_max_right _ _).trans_lt hv0
        linarith only [hh,hδ]
      have hwnear : (wI : ℝ) < (u : ℝ)+δ := by
        change w < (u : ℝ)+δ
        have hh := hw1.trans_le (min_le_right _ _)
        linarith only [hh,hδ]
      obtain ⟨_,_,hnv,hnw,hnegpos⟩ := hflip vI wI hvnear hv1 hw0 hwnear
      have hpos : 0 < (C (γ vI)).1 ↔ ¬ 0 < (C (γ wI)).1 := by
        have hvsign : 0 < (C (γ vI)).1 ↔ ¬ (C (γ vI)).1 < 0 := by
          constructor
          · intro h; exact not_lt_of_ge h.le
          · intro h; exact lt_of_le_of_ne (le_of_not_gt h) hnv.symm
        have hwsign : 0 < (C (γ wI)).1 ↔ ¬ (C (γ wI)).1 < 0 := by
          constructor
          · intro h; exact not_lt_of_ge h.le
          · intro h; exact lt_of_le_of_ne (le_of_not_gt h) hnw.symm
        rw [hvsign,hwsign]
        exact not_congr hnegpos
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
      have hl := actualIntervalSignConstant g x u vI sl hvleft hsl hleft
      have hr := actualIntervalSignConstant g u y wI sr hwright hsr hright
      exact hl.symm.trans (hsample.trans (not_congr hr))

  have hactualSharedStartTwoFiniteSeams (hshared : b.val.map 0=af 0) :
      ∃ r q : Interval,r≠0 ∧ q≠1 ∧ r<q ∧
      ∃ HG : C(Interval × (Interval × Interval),S),
        (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩ ∧
      ∃ ΓFamily : {τ : Interval // HG (1,(τ,r))∈a.val.image} → C({t : Interval // t≠0},Interval),
        (∀ τ,ΓFamily τ ⟨1,by simp⟩=τ.val) ∧
        (∀ t,Function.Injective (fun τ => ΓFamily τ t)) ∧
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite ∧
        {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}.Finite ∧
        (∀ t : Interval,t≠0 → t.val≤r.val → F (0,t) ∉ a.val.image) ∧
        (∀ t : Interval,t≠1 → q.val≤t.val → F (0,t) ∉ a.val.image) ∧
        (∀ (τ : Interval) (hτ : HG (1,(τ,r))∈a.val.image),
          ∃ f : Path (af 0) (HG (1,(τ,r))),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧
              Γ=ΓFamily ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,0) : ℝ × ℝ) (τ.val,r.val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,
                ⟨r.val*t.val.val,mul_nonneg r.property.1 t.val.property.1,
                  (mul_le_of_le_one_right r.property.1 t.val.property.2).trans r.property.2⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,r.val*t.val.val)) ∧
              (∀ t : Interval,(P t).2=r.val*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=0 ∧ θ 1=r ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=HG (1,
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,r))) ∧
              α.Homotopic (v.trans w)) ∧
        ∀ τ : Interval,HG (1,(τ,q))∉a.val.image := by
    as_aux_lemma =>
      have hoff : b.val.map 1 ∉ a.val.image := by
        intro hx
        exact hbne (hshared.trans (hAnySharedOldStart 1 (Or.inr rfl) hx).symm)
      obtain ⟨d,hd,hd1,lo,hi,γ,HG,hstrict,hgraph,hγinjective,hSeamChartData,hSeamSides,hSeamAdaptedSides,hzero,hboundary,hends,hmarks,hExterior,hcontact,hclosedtails⟩ :=
        hactualSharedStartGlobalFiniteCornerDeformation hshared
      let m : ℝ := min ((1-d)/2) (δ₁/2)
      have hm : 0< m := by dsimp [m]; positivity
      have hmgap : m≤(1-d)/2 := min_le_left _ _
      have hmδ : m<δ₁ := by
        have hh : m≤δ₁/2 := min_le_right _ _
        linarith only [hh,hδ₁]
      have hqd : d<1-m := by linarith only [hmgap,hd1]
      have hq₀ : 0<1-m := hd.trans hqd
      have hq₁ : 1-m<1 := by linarith only [hm]
      let q : Interval := ⟨1-m,hq₀.le,hq₁.le⟩
      let r : Interval := ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩
      have hr₀ : r≠0 := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_gt (half_pos hd)) hv
      have hqne : q≠1 := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_lt hq₁) hv
      have hrq : r<q := (half_le_self hd.le).trans_lt hqd
      have hqdist : dist q (1:Interval)<δ₁ := by
        rw [Subtype.dist_eq,Real.dist_eq]
        change |(1-m)-1|<δ₁
        rw [show (1-m)-1=-m by ring,abs_neg,abs_of_pos hm]
        exact hmδ
      have hqoff (τ : Interval) : HG (1,(τ,q)) ∉ a.val.image := by
        rw [hExterior 1 τ q hqd]
        exact htail₁ hoff τ q hqdist
      have hfiniteR : {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
        let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,half_le_self hd.le⟩
        apply (Set.finite_range (fun k => γ k t)).subset
        intro τ hτ
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        exact ⟨k,hk.symm⟩
      have hfiniteQ : {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}.Finite := by
        have he : {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}=(∅ : Set Interval) := by
          ext τ
          exact iff_of_false (hqoff τ) (notMem_empty τ)
        rw [he]
        exact finite_empty
      have hActualSeamTransverse : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩ := by
        intro τ hτ C hpC hCaxis
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        subst τ
        exact hSeamAdaptedSides k C hpC hCaxis
      let selectedLevel (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) :
          {k : ℤ // k∈Finset.Icc lo (hi-1)} :=
        Classical.choose ((hcontact τ.val r hr₀ le_rfl).mp τ.property)
      have selectedLevelEnd (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) :
          τ.val=γ (selectedLevel τ) ⟨d/2,half_pos hd,half_le_self hd.le⟩ :=
        Classical.choose_spec ((hcontact τ.val r hr₀ le_rfl).mp τ.property)
      let scaledPositiveParameter : C({t : Interval // t≠0},Ioc (0:ℝ) d) :=
        ⟨fun t => ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
          (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
          (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
      let ΓFamily (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) : C({t : Interval // t≠0},Interval) :=
        (γ (selectedLevel τ)).comp scaledPositiveParameter
      have hΓFamilyEnd (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) :
          ΓFamily τ ⟨1,by simp⟩=τ.val := by
        have he : scaledPositiveParameter ⟨1,by simp⟩=⟨d/2,half_pos hd,half_le_self hd.le⟩ := by
          apply Subtype.ext
          simp [scaledPositiveParameter]
        change γ (selectedLevel τ) (scaledPositiveParameter ⟨1,by simp⟩)=τ.val
        rw [he]
        exact (selectedLevelEnd τ).symm
      have hΓFamilyInjective (t : {t : Interval // t≠0}) :
          Function.Injective (fun τ => ΓFamily τ t) := by
        intro τ υ he
        change γ (selectedLevel τ) (scaledPositiveParameter t)=
          γ (selectedLevel υ) (scaledPositiveParameter t) at he
        have hk := hγinjective (scaledPositiveParameter t) he
        apply Subtype.ext
        exact (selectedLevelEnd τ).trans
          ((congrArg (fun k => γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩) hk).trans
            (selectedLevelEnd υ).symm)
      have hsourceLower (t : Interval) (ht₀ : t≠0) (htr : t.val≤r.val) : F (0,t) ∉ a.val.image := by
        intro hhit
        have hh : HG (1,(0,t)) ∈ a.val.image := by
          rw [hboundary 1 0 t (Or.inl rfl)]
          exact hhit
        have hhalf : t.val≤d/2 := htr
        obtain ⟨k,hk⟩ := (hcontact 0 t ht₀ hhalf).mp hh
        have htpos : 0<t.val := lt_of_le_of_ne t.property.1
          (by intro he; exact ht₀ (Subtype.ext he.symm))
        have htupper : t.val≤d := hhalf.trans (half_le_self hd.le)
        have hv := congrArg Subtype.val hk
        exact (ne_of_gt (hstrict k ⟨t.val,htpos,htupper⟩).1) hv.symm
      have hsourceUpper (t : Interval) (_ht₁ : t≠1) (hqt : q.val≤t.val) : F (0,t) ∉ a.val.image := by
        apply htail₁ hoff 0 t
        rw [Subtype.dist_eq,Real.dist_eq]
        change |t.val-1|<δ₁
        rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
        have hqtR : 1-m≤t.val := hqt
        linarith only [hqtR,hmδ]
      have hclosedLower (τ : Interval) (hτ : HG (1,(τ,r))∈a.val.image) :
          ∃ f : Path (af 0) (HG (1,(τ,r))),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧
              Γ=ΓFamily ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,0) : ℝ × ℝ) (τ.val,r.val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,
                ⟨r.val*t.val.val,mul_nonneg r.property.1 t.val.property.1,
                  (mul_le_of_le_one_right r.property.1 t.val.property.2).trans r.property.2⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,r.val*t.val.val)) ∧
              (∀ t : Interval,(P t).2=r.val*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=0 ∧ θ 1=r ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=HG (1,
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,r))) ∧
              α.Homotopic (v.trans w) := by
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        obtain ⟨f,hf,hm,Γ,hΓend,hΓnormalization,P,hP,hΓtrace,hPtrace,hΓstrict,hPsecond,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩ := hclosedtails k
        have he : τ=γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ := hk
        have htarget : HG (1,(τ,r))=HG (1,(γ k
            ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,by linarith⟩)) := by
          rw [he]
        have hΓτ : Γ ⟨1,by simp⟩=τ := hΓend.trans he.symm
        have hkselected : k=selectedLevel ⟨τ,hτ⟩ :=
          hγinjective ⟨d/2,half_pos hd,half_le_self hd.le⟩
            (he.symm.trans (selectedLevelEnd ⟨τ,hτ⟩))
        have hΓChosen : Γ=ΓFamily ⟨τ,hτ⟩ := by
          apply ContinuousMap.ext
          intro t
          rw [hΓnormalization,hkselected]
          rfl

        obtain ⟨P₀,hP₀,hP₀trace,hP₀second,zQ,Q,hQ,hQP,hQinside⟩ :=
          CurveComplex.LocalSurgery.actualSharedMarkedTailClosedLowerSquareParameterContactPath
            r.val q.val (half_pos hd) hrq hq₁ Γ hΓstrict
        have hPend : (τ.val,r.val)=((Γ ⟨1,by simp⟩).val,r.val) := by
          apply Prod.ext
          · exact congrArg Subtype.val hΓτ.symm
          · rfl
        let P₁ := P₀.cast rfl hPend
        let θ := actualIntervalSegment 0 r
        have hθemb : IsEmbedding θ :=
          (((actualIntervalSegment 0 r).continuous.isClosedEmbedding
            (actualIntervalSegmentInjective 0 r (half_pos hd))).isEmbedding)
        refine ⟨f.cast rfl htarget,hf,hm,Γ,hΓτ,hΓChosen,P₁,hP₀,hΓtrace,hP₀trace,hP₀second,zQ,Q,hQ,hQP,hQinside,θ,?_,?_,hθemb,c,y,z,α,v,w,hc,hα,?_,?_,hhom⟩
        · apply Subtype.ext
          simp [θ,actualIntervalSegment,unitInterval.symm]
        · apply Subtype.ext
          simp [θ,actualIntervalSegment,unitInterval.symm]
        · intro t
          rw [hv t]
          apply congrArg b.val.map
          apply Subtype.ext
          simp only [θ,actualIntervalSegment,ContinuousMap.coe_mk]
          change (d/2)*t.val=(1-t.val)*0+t.val*(d/2)
          ring
        · intro t
          rw [hw t,he]
      exact ⟨r,q,hr₀,hqne,hrq,HG,hActualSeamTransverse,ΓFamily,hΓFamilyEnd,hΓFamilyInjective,hzero,hboundary,hends,hmarks,hfiniteR,hfiniteQ,
        hsourceLower,hsourceUpper,hclosedLower,hqoff⟩
  have hFrefTailEndAvoid (hoff : b.val.map 0 ∉ a.val.image) (τ t : Interval)
      (ht : dist t (1:Interval)<δ₀) : Fref (τ,t) ∉ a.val.image := by
    apply htail₀ hoff τ (unitInterval.symm t)
    have hdist : dist (unitInterval.symm t) (0:Interval)=dist t (1:Interval) := by
      rw [Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      change |(1-t.val)-0|=|t.val-1|
      rw [sub_zero,show 1-t.val=-(t.val-1) by ring,abs_neg]
    rw [hdist]
    exact ht
  have hactualSharedReflectedTwoFiniteSeams (hshared : b.val.map 1=af 0) :
      ∃ r q : Interval,r≠0 ∧ q≠1 ∧ r<q ∧
      ∃ HG : C(Interval × (Interval × Interval),S),
        (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩ ∧
      ∃ ΓFamily : {τ : Interval // HG (1,(τ,r))∈a.val.image} → C({t : Interval // t≠0},Interval),
        (∀ τ,ΓFamily τ ⟨1,by simp⟩=τ.val) ∧
        (∀ t,Function.Injective (fun τ => ΓFamily τ t)) ∧
        (∀ z,HG (0,z)=Fref z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=Fref (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite ∧
        {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}.Finite ∧
        (∀ t : Interval,t≠0 → t.val≤r.val → Fref (0,t) ∉ a.val.image) ∧
        (∀ t : Interval,t≠1 → q.val≤t.val → Fref (0,t) ∉ a.val.image) ∧
        (∀ (τ : Interval) (hτ : HG (1,(τ,r))∈a.val.image),
          ∃ f : Path (af 0) (HG (1,(τ,r))),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧
              Γ=ΓFamily ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,0) : ℝ × ℝ) (τ.val,r.val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,
                ⟨r.val*t.val.val,mul_nonneg r.property.1 t.val.property.1,
                  (mul_le_of_le_one_right r.property.1 t.val.property.2).trans r.property.2⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,r.val*t.val.val)) ∧
              (∀ t : Interval,(P t).2=r.val*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=1 ∧ θ 1=unitInterval.symm r ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=HG (1,
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,r))) ∧
              α.Homotopic (v.trans w)) ∧
        ∀ τ : Interval,HG (1,(τ,q))∉a.val.image := by
    as_aux_lemma =>
      have hoff : b.val.map 0 ∉ a.val.image := by
        intro hx
        exact hbne ((hAnySharedOldStart 0 (Or.inl rfl) hx).trans hshared.symm)
      obtain ⟨d,hd,hd1,lo,hi,γ,HG,hstrict,hgraph,hγinjective,hSeamChartData,hSeamSides,hSeamAdaptedSides,hzero,hboundary,hends,hmarks,hExterior,hcontact,hclosedtails⟩ :=
        hactualSharedReflectedGlobalFiniteCornerDeformation hshared
      let m : ℝ := min ((1-d)/2) (δ₀/2)
      have hm : 0< m := by dsimp [m]; positivity
      have hmgap : m≤(1-d)/2 := min_le_left _ _
      have hmδ : m<δ₀ := by
        have hh : m≤δ₀/2 := min_le_right _ _
        linarith only [hh,hδ₀]
      have hqd : d<1-m := by linarith only [hmgap,hd1]
      have hq₀ : 0<1-m := hd.trans hqd
      have hq₁ : 1-m<1 := by linarith only [hm]
      let q : Interval := ⟨1-m,hq₀.le,hq₁.le⟩
      let r : Interval := ⟨d/2,(half_pos hd).le,(half_le_self hd.le).trans hd1.le⟩
      have hr₀ : r≠0 := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_gt (half_pos hd)) hv
      have hqne : q≠1 := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_lt hq₁) hv
      have hrq : r<q := (half_le_self hd.le).trans_lt hqd
      have hqdist : dist q (1:Interval)<δ₀ := by
        rw [Subtype.dist_eq,Real.dist_eq]
        change |(1-m)-1|<δ₀
        rw [show (1-m)-1=-m by ring,abs_neg,abs_of_pos hm]
        exact hmδ
      have hqoff (τ : Interval) : HG (1,(τ,q)) ∉ a.val.image := by
        rw [hExterior 1 τ q hqd]
        exact hFrefTailEndAvoid hoff τ q hqdist
      have hfiniteR : {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite := by
        let t : Ioc (0:ℝ) d := ⟨d/2,half_pos hd,half_le_self hd.le⟩
        apply (Set.finite_range (fun k => γ k t)).subset
        intro τ hτ
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        exact ⟨k,hk.symm⟩
      have hfiniteQ : {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}.Finite := by
        have he : {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}=(∅ : Set Interval) := by
          ext τ
          exact iff_of_false (hqoff τ) (notMem_empty τ)
        rw [he]
        exact finite_empty
      have hActualSeamTransverse : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩ := by
        intro τ hτ C hpC hCaxis
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        subst τ
        exact hSeamAdaptedSides k C hpC hCaxis
      let selectedLevel (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) :
          {k : ℤ // k∈Finset.Icc lo (hi-1)} :=
        Classical.choose ((hcontact τ.val r hr₀ le_rfl).mp τ.property)
      have selectedLevelEnd (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) :
          τ.val=γ (selectedLevel τ) ⟨d/2,half_pos hd,half_le_self hd.le⟩ :=
        Classical.choose_spec ((hcontact τ.val r hr₀ le_rfl).mp τ.property)
      let scaledPositiveParameter : C({t : Interval // t≠0},Ioc (0:ℝ) d) :=
        ⟨fun t => ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
          (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
          (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
      let ΓFamily (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) : C({t : Interval // t≠0},Interval) :=
        (γ (selectedLevel τ)).comp scaledPositiveParameter
      have hΓFamilyEnd (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) :
          ΓFamily τ ⟨1,by simp⟩=τ.val := by
        have he : scaledPositiveParameter ⟨1,by simp⟩=⟨d/2,half_pos hd,half_le_self hd.le⟩ := by
          apply Subtype.ext
          simp [scaledPositiveParameter]
        change γ (selectedLevel τ) (scaledPositiveParameter ⟨1,by simp⟩)=τ.val
        rw [he]
        exact (selectedLevelEnd τ).symm
      have hΓFamilyInjective (t : {t : Interval // t≠0}) :
          Function.Injective (fun τ => ΓFamily τ t) := by
        intro τ υ he
        change γ (selectedLevel τ) (scaledPositiveParameter t)=
          γ (selectedLevel υ) (scaledPositiveParameter t) at he
        have hk := hγinjective (scaledPositiveParameter t) he
        apply Subtype.ext
        exact (selectedLevelEnd τ).trans
          ((congrArg (fun k => γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩) hk).trans
            (selectedLevelEnd υ).symm)
      have hsourceLower (t : Interval) (ht₀ : t≠0) (htr : t.val≤r.val) : Fref (0,t) ∉ a.val.image := by
        intro hhit
        have hh : HG (1,(0,t)) ∈ a.val.image := by
          rw [hboundary 1 0 t (Or.inl rfl)]
          exact hhit
        have hhalf : t.val≤d/2 := htr
        obtain ⟨k,hk⟩ := (hcontact 0 t ht₀ hhalf).mp hh
        have htpos : 0<t.val := lt_of_le_of_ne t.property.1
          (by intro he; exact ht₀ (Subtype.ext he.symm))
        have htupper : t.val≤d := hhalf.trans (half_le_self hd.le)
        have hv := congrArg Subtype.val hk
        exact (ne_of_gt (hstrict k ⟨t.val,htpos,htupper⟩).1) hv.symm
      have hsourceUpper (t : Interval) (_ht₁ : t≠1) (hqt : q.val≤t.val) : Fref (0,t) ∉ a.val.image := by
        apply hFrefTailEndAvoid hoff 0 t
        rw [Subtype.dist_eq,Real.dist_eq]
        change |t.val-1|<δ₀
        rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
        have hqtR : 1-m≤t.val := hqt
        linarith only [hqtR,hmδ]
      have hclosedLower (τ : Interval) (hτ : HG (1,(τ,r))∈a.val.image) :
          ∃ f : Path (af 0) (HG (1,(τ,r))),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧
              Γ=ΓFamily ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,0) : ℝ × ℝ) (τ.val,r.val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,
                ⟨r.val*t.val.val,mul_nonneg r.property.1 t.val.property.1,
                  (mul_le_of_le_one_right r.property.1 t.val.property.2).trans r.property.2⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,r.val*t.val.val)) ∧
              (∀ t : Interval,(P t).2=r.val*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=1 ∧ θ 1=unitInterval.symm r ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=HG (1,
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,r))) ∧
              α.Homotopic (v.trans w) := by
        obtain ⟨k,hk⟩ := (hcontact τ r hr₀ le_rfl).mp hτ
        obtain ⟨f,hf,hm,Γ,hΓend,hΓnormalization,P,hP,hΓtrace,hPtrace,hΓstrict,hPsecond,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩ := hclosedtails k
        have he : τ=γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩ := hk
        have htarget : HG (1,(τ,r))=HG (1,(γ k
            ⟨d/2,half_pos hd,half_le_self hd.le⟩,⟨d/2,(half_pos hd).le,by linarith⟩)) := by
          rw [he]
        have hΓτ : Γ ⟨1,by simp⟩=τ := hΓend.trans he.symm
        have hkselected : k=selectedLevel ⟨τ,hτ⟩ :=
          hγinjective ⟨d/2,half_pos hd,half_le_self hd.le⟩
            (he.symm.trans (selectedLevelEnd ⟨τ,hτ⟩))
        have hΓChosen : Γ=ΓFamily ⟨τ,hτ⟩ := by
          apply ContinuousMap.ext
          intro t
          rw [hΓnormalization,hkselected]
          rfl

        obtain ⟨P₀,hP₀,hP₀trace,hP₀second,zQ,Q,hQ,hQP,hQinside⟩ :=
          CurveComplex.LocalSurgery.actualSharedMarkedTailClosedLowerSquareParameterContactPath
            r.val q.val (half_pos hd) hrq hq₁ Γ hΓstrict
        have hPend : (τ.val,r.val)=((Γ ⟨1,by simp⟩).val,r.val) := by
          apply Prod.ext
          · exact congrArg Subtype.val hΓτ.symm
          · rfl
        let P₁ := P₀.cast rfl hPend
        let θ : C(Interval,Interval) := ⟨fun t => unitInterval.symm (actualIntervalSegment 0 r t),by fun_prop⟩
        have hθemb : IsEmbedding θ :=
          unitInterval.symmHomeomorph.isEmbedding.comp
            (((actualIntervalSegment 0 r).continuous.isClosedEmbedding
              (actualIntervalSegmentInjective 0 r (half_pos hd))).isEmbedding)
        refine ⟨f.cast rfl htarget,hf,hm,Γ,hΓτ,hΓChosen,P₁,hP₀,hΓtrace,hP₀trace,hP₀second,zQ,Q,hQ,hQP,hQinside,θ,?_,?_,hθemb,c,y,z,α,v,w,hc,hα,?_,?_,hhom⟩
        · apply Subtype.ext
          simp [θ,actualIntervalSegment,unitInterval.symm]
        · apply Subtype.ext
          simp [θ,actualIntervalSegment,unitInterval.symm]
        · intro t
          rw [hv t]
          apply congrArg b.val.map
          apply congrArg unitInterval.symm
          apply Subtype.ext
          simp only [θ,actualIntervalSegment,ContinuousMap.coe_mk]
          change (d/2)*t.val=(1-t.val)*0+t.val*(d/2)
          ring
        · intro t
          rw [hw t,he]
      exact ⟨r,q,hr₀,hqne,hrq,HG,hActualSeamTransverse,ΓFamily,hΓFamilyEnd,hΓFamilyInjective,hzero,hboundary,hends,hmarks,hfiniteR,hfiniteQ,
        hsourceLower,hsourceUpper,hclosedLower,hqoff⟩
  have hactualTwoFiniteInnerSeams :
      ∃ r q : Interval,r≠0 ∧ q≠1 ∧ r<q ∧
      ∃ HG : C(Interval × (Interval × Interval),S),
      ∃ ΓLower : {τ : Interval // HG (1,(τ,r))∈a.val.image} → C({t : Interval // t≠0},Interval),
      ∃ ΓUpper : {τ : Interval // HG (1,(τ,q))∈a.val.image} → C({t : Interval // t≠0},Interval),
        (∀ τ,ΓLower τ ⟨1,by simp⟩=τ.val) ∧
        (∀ t,Function.Injective (fun τ => ΓLower τ t)) ∧
        (∀ τ,ΓUpper τ ⟨1,by simp⟩=τ.val) ∧
        (∀ t,Function.Injective (fun τ => ΓUpper τ t)) ∧
        (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => HG (1,(τ,r)),by fun_prop⟩ ∧
        (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => HG (1,(τ,q)),by fun_prop⟩ ∧
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        {τ : Interval | HG (1,(τ,r)) ∈ a.val.image}.Finite ∧
        {τ : Interval | HG (1,(τ,q)) ∈ a.val.image}.Finite ∧
        (∀ t : Interval,t≠0 → t.val≤r.val → F (0,t) ∉ a.val.image) ∧
        (∀ t : Interval,t≠1 → q.val≤t.val → F (0,t) ∉ a.val.image) ∧
        (∀ (τ : Interval) (hτ : HG (1,(τ,r))∈a.val.image), b.val.map 0=af 0 ∧
          ∃ f : Path (af 0) (HG (1,(τ,r))),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧ Γ=ΓLower ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,0) : ℝ × ℝ) (τ.val,(r).val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,⟨(r).val*t.val.val,by constructor <;> nlinarith only [(r).property.1,(r).property.2,t.val.property.1,t.val.property.2]⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,(r).val*t.val.val)) ∧
              (∀ t : Interval,(P t).2=(r).val*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=0 ∧ θ 1=r ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=HG (1,
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,r))) ∧
              α.Homotopic (v.trans w)) ∧
        (∀ (τ : Interval) (hτ : HG (1,(τ,q))∈a.val.image), b.val.map 1=af 0 ∧
          ∃ f : Path (af 0) (HG (1,(τ,q))),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧ Γ=ΓUpper ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,1) : ℝ × ℝ) (τ.val,(q).val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,⟨1-(1-(q).val)*t.val.val,by constructor <;> nlinarith only [(q).property.1,(q).property.2,t.val.property.1,t.val.property.2]⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,1-(1-(q).val)*t.val.val)) ∧
              (∀ t : Interval,(P t).2=1-(1-(q).val)*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,1) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=1 ∧ θ 1=q ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=HG (1,
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,q))) ∧
              α.Homotopic (v.trans w)) := by
    as_aux_lemma =>
      by_cases h₀ : b.val.map 0 ∈ a.val.image
      · obtain ⟨r,q,hr,hq,hrq,HG,hActualSeamTransverse,ΓFamily,hΓFamilyEnd,hΓFamilyInjective,hz,hb,he,hm,hfr,hfq,hsl,hsu,hclosedR,hQoff⟩ :=
          hactualSharedStartTwoFiniteSeams (hAnySharedOldStart 0 (Or.inl rfl) h₀)
        let ΓEmpty : {τ : Interval // HG (1,(τ,q))∈a.val.image} → C({t : Interval // t≠0},Interval) :=
          fun τ => False.elim (hQoff τ.val τ.property)
        have hEmptyEnd (τ : {τ : Interval // HG (1,(τ,q))∈a.val.image}) : ΓEmpty τ ⟨1,by simp⟩=τ.val :=
          False.elim (hQoff τ.val τ.property)
        have hEmptyInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓEmpty τ t) := by
          intro τ υ _
          exact False.elim (hQoff τ.val τ.property)
        exact ⟨r,q,hr,hq,hrq,HG,ΓFamily,ΓEmpty,hΓFamilyEnd,hΓFamilyInjective,hEmptyEnd,hEmptyInjective,hActualSeamTransverse,(by intro τ hτ; exact False.elim (hQoff τ hτ)),hz,hb,he,hm,hfr,hfq,hsl,hsu,
          (fun τ hτ => by
            obtain ⟨f,hf,hm,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩ := hclosedR τ hτ
            exact ⟨hAnySharedOldStart 0 (Or.inl rfl) h₀,f,hf,hm,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩),
          fun τ hτ => False.elim (hQoff τ hτ)⟩
      · by_cases h₁ : b.val.map 1 ∈ a.val.image
        · obtain ⟨r,q,hr₀,hq₁,hrq,R,hActualSeamTransverse,ΓFamily,hΓFamilyEnd,hΓFamilyInjective,hzero,hboundary,hends,hmarks,hfiniteR,hfiniteQ,hsourceLower,hsourceUpper,hclosedR,hQoff⟩ :=
            hactualSharedReflectedTwoFiniteSeams (hAnySharedOldStart 1 (Or.inr rfl) h₁)
          have hσσ (t : Interval) : unitInterval.symm (unitInterval.symm t)=t := by
            apply Subtype.ext
            change 1-(1-t.val)=t.val
            ring
          have hσ₀ : unitInterval.symm (0:Interval)=1 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
          have hσ₁ : unitInterval.symm (1:Interval)=0 := Subtype.ext (by norm_num [unitInterval.coe_symm_eq])
          let HG : C(Interval × (Interval × Interval),S) := R.comp {
            toFun := fun z => (z.1,(z.2.1,unitInterval.symm z.2.2))
            continuous_toFun := by fun_prop }
          have hreverseOrder : unitInterval.symm q<unitInterval.symm r := by
            change 1-q.val<1-r.val
            exact sub_lt_sub_left (show r.val<q.val from hrq) (1:ℝ)
          let ΓEmpty : {τ : Interval // HG (1,(τ,unitInterval.symm q))∈a.val.image} →
              C({t : Interval // t≠0},Interval) := fun τ => False.elim (hQoff τ.val (by
                simpa only [HG,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hσσ] using τ.property))
          let ΓReflected : {τ : Interval // HG (1,(τ,unitInterval.symm r))∈a.val.image} →
              C({t : Interval // t≠0},Interval) := fun τ => ΓFamily ⟨τ.val,by
                have hh := τ.property
                change R (1,(τ.val,unitInterval.symm (unitInterval.symm r)))∈a.val.image at hh
                simpa only [hσσ] using hh⟩
          have hEmptyEnd (τ : {τ : Interval // HG (1,(τ,unitInterval.symm q))∈a.val.image}) :
              ΓEmpty τ ⟨1,by simp⟩=τ.val := by
            have hh : R (1,(τ.val,q))∈a.val.image := by simpa only [HG,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hσσ] using τ.property
            exact False.elim (hQoff τ.val hh)
          have hEmptyInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓEmpty τ t) := by
            intro τ υ _
            have hh : R (1,(τ.val,q))∈a.val.image := by simpa only [HG,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hσσ] using τ.property
            exact False.elim (hQoff τ.val hh)
          have hReflectedEnd (τ : {τ : Interval // HG (1,(τ,unitInterval.symm r))∈a.val.image}) :
              ΓReflected τ ⟨1,by simp⟩=τ.val := hΓFamilyEnd _
          have hReflectedInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓReflected τ t) := by
            intro τ υ he
            have hh := hΓFamilyInjective t he
            exact Subtype.ext (congrArg (fun z : {τ : Interval // R (1,(τ,r))∈a.val.image} => z.val) hh)
          refine ⟨unitInterval.symm q,unitInterval.symm r,hsymmNeZero q hq₁,
            hsymmNeOne r hr₀,hreverseOrder,HG,ΓEmpty,ΓReflected,hEmptyEnd,hEmptyInjective,hReflectedEnd,hReflectedInjective,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · intro τ hτ
            have hh : R (1,(τ,q))∈a.val.image := by
              change R (1,(τ,unitInterval.symm (unitInterval.symm q)))∈a.val.image at hτ
              simpa only [hσσ] using hτ
            exact False.elim (hQoff τ hh)
          · intro τ hτ C hpC hCaxis
            have htrace (v : Interval) : HG (1,(v,unitInterval.symm r))=R (1,(v,r)) := by
              change R (1,(v,unitInterval.symm (unitInterval.symm r)))=R (1,(v,r))
              rw [hσσ]
            change HG (1,(τ,unitInterval.symm r))∈a.val.image at hτ
            change HG (1,(τ,unitInterval.symm r))∈C.source at hpC
            rw [htrace] at hτ hpC
            obtain ⟨δ,hδ,hflip⟩ := hActualSeamTransverse τ hτ C hpC hCaxis
            refine ⟨δ,hδ,?_⟩
            intro v w hvlo hvu huw hwhi
            simpa only [ContinuousMap.coe_mk,htrace] using hflip v w hvlo hvu huw hwhi
          · intro z
            change R (0,(z.1,unitInterval.symm z.2))=F z
            rw [hzero]
            change F (z.1,unitInterval.symm (unitInterval.symm z.2))=F z
            rw [hσσ]
          · intro η τ t hτ
            change R (η,(τ,unitInterval.symm t))=F (τ,t)
            rw [hboundary η τ (unitInterval.symm t) hτ]
            change F (τ,unitInterval.symm (unitInterval.symm t))=F (τ,t)
            rw [hσσ]
          · intro η τ t ht
            have hs : unitInterval.symm t=0 ∨ unitInterval.symm t=1 := by
              rcases ht with rfl | rfl
              · exact Or.inr hσ₀
              · exact Or.inl hσ₁
            change R (η,(τ,unitInterval.symm t))=F (τ,t)
            rw [hends η τ (unitInterval.symm t) hs]
            change F (τ,unitInterval.symm (unitInterval.symm t))=F (τ,t)
            rw [hσσ]
          · intro η τ t ht₀ ht₁
            exact hmarks η τ (unitInterval.symm t) (hsymmNeZero t ht₁) (hsymmNeOne t ht₀)
          · change {τ : Interval | R (1,(τ,unitInterval.symm (unitInterval.symm q))) ∈ a.val.image}.Finite
            simpa only [hσσ] using hfiniteQ
          · change {τ : Interval | R (1,(τ,unitInterval.symm (unitInterval.symm r))) ∈ a.val.image}.Finite
            simpa only [hσσ] using hfiniteR
          · intro t ht₀ htr
            have hbound : q.val≤(unitInterval.symm t).val := by
              change t.val≤1-q.val at htr
              change q.val≤1-t.val
              linarith only [htr]
            have hoff := hsourceUpper (unitInterval.symm t) (hsymmNeOne t ht₀) hbound
            change F (0,unitInterval.symm (unitInterval.symm t)) ∉ a.val.image at hoff
            simpa only [hσσ] using hoff
          · intro t ht₁ hqt
            have hbound : (unitInterval.symm t).val≤r.val := by
              change 1-r.val≤t.val at hqt
              change 1-t.val≤r.val
              linarith only [hqt]
            have hoff := hsourceLower (unitInterval.symm t) (hsymmNeZero t ht₁) hbound
            change F (0,unitInterval.symm (unitInterval.symm t)) ∉ a.val.image at hoff
            simpa only [hσσ] using hoff
          · intro τ hτ
            have hh : R (1,(τ,q))∈a.val.image := by
              change R (1,(τ,unitInterval.symm (unitInterval.symm q)))∈a.val.image at hτ
              simpa only [hσσ] using hτ
            exact False.elim (hQoff τ hh)
          · intro τ hτ
            have hh : R (1,(τ,r))∈a.val.image := by
              change R (1,(τ,unitInterval.symm (unitInterval.symm r)))∈a.val.image at hτ
              simpa only [hσσ] using hτ
            obtain ⟨f,hf,hm,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩ := hclosedR τ hh
            have he : HG (1,(τ,unitInterval.symm r))=R (1,(τ,r)) := by
              change R (1,(τ,unitInterval.symm (unitInterval.symm r)))=R (1,(τ,r))
              rw [hσσ]
            let mirror : C(ℝ × ℝ,ℝ × ℝ) := ⟨fun z => (z.1,1-z.2),by fun_prop⟩
            let PUpper : Path ((0,1) : ℝ × ℝ) (τ.val,(unitInterval.symm r).val) :=
              (P.map mirror.continuous).cast (by apply Prod.ext <;> dsimp [mirror] <;> norm_num) rfl
            have hPUpperInjective : Function.Injective PUpper := by
              intro t u he
              apply hP.injective
              apply Prod.ext
              · have hh := congrArg Prod.fst he
                change (P t).1=(P u).1 at hh
                exact hh
              · have hh := congrArg Prod.snd he
                change 1-(P t).2=1-(P u).2 at hh
                linarith only [hh]
            let reflectQ := CurveComplex.LocalSurgery.actualMarkedCollarSquareReflection
            have hsQ : ((0,1) : Interval × Interval)=reflectQ (0,0) := by
              apply Prod.ext
              · rfl
              · apply Subtype.ext
                norm_num [reflectQ,CurveComplex.LocalSurgery.actualMarkedCollarSquareReflection,unitInterval.symm]
            let QUpper := (Q.map reflectQ.continuous).cast hsQ rfl
            have hQUpperInjective : Function.Injective QUpper :=
              CurveComplex.LocalSurgery.actualMarkedCollarSquareReflectionInjective.comp hQ.injective
            have hrr : 1-(unitInterval.symm r).val=r.val := by
              change 1-(1-r.val)=r.val
              ring
            have hqq : 1-(unitInterval.symm q).val=q.val := by
              change 1-(1-q.val)=q.val
              ring
            refine ⟨hAnySharedOldStart 1 (Or.inr rfl) h₁,f.cast rfl he,hf,hm,
              Γ,hΓτ,hΓChosen,PUpper,(PUpper.continuous.isClosedEmbedding hPUpperInjective).isEmbedding,
              ?_,?_,?_,reflectQ zQ,QUpper,(QUpper.continuous.isClosedEmbedding hQUpperInjective).isEmbedding,
              ?_,?_,θ,hθzero,hθone,hθemb,c,y,z,α,v,w,hc,hα,hv,?_,hhom⟩
            · intro t
              change f t.val=R (1,(Γ t,unitInterval.symm _))
              rw [hΓtrace]
              apply congrArg R
              apply Prod.ext
              · rfl
              apply Prod.ext
              · rfl
              apply Subtype.ext
              change r.val*t.val.val=1-(1-(1-(unitInterval.symm r).val)*t.val.val)
              rw [hrr]
              ring
            · intro t
              change mirror (P t.val)=_
              rw [hPtrace]
              apply Prod.ext
              · rfl
              change 1-r.val*t.val.val=1-(1-(unitInterval.symm r).val)*t.val.val
              rw [hrr]
            · intro t
              change 1-(P t).2=1-(1-(unitInterval.symm r).val)*t.val
              rw [hPsecond,hrr]
            · intro t
              change CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
                (unitInterval.symm q).val (unitInterval.symm r).val (reflectQ (Q t))=mirror (P t)
              rw [CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralReflection,hrr,hqq,hQP]
              rfl
            · intro t
              obtain ⟨hx,hy⟩ := hQinside t
              refine ⟨hx,?_,?_⟩
              · change 0<1-(Q t.val).2.val
                exact sub_pos.mpr hy.2
              · change 1-(Q t.val).2.val<1
                have hh : 0<(Q t.val).2.val := hy.1
                linarith only [hh]

            intro t
            change (w t).val=R (1,
              (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,
                unitInterval.symm (unitInterval.symm r)))
            rw [hσσ]
            exact hw t
        · let r := centralParam 0
          let q := centralParam 1
          have hr₀ : r≠0 := by
            intro he
            exact (ne_of_gt (hcentralPos 0)) (congrArg Subtype.val he)
          have hq₁ : q≠1 := by
            intro he
            exact (ne_of_lt (hcentralLt 1)) (congrArg Subtype.val he)
          have hrq : r<q := by
            change ε+(1-2*ε)*0<ε+(1-2*ε)*1
            linarith only [hεhalf]
          let HG : C(Interval × (Interval × Interval),S) := F.comp {
            toFun := fun z => z.2
            continuous_toFun := continuous_snd }
          have hRoff (τ : Interval) : HG (1,(τ,r))∉a.val.image :=
            hleftTail h₀ τ r (by change ε+(1-2*ε)*0≤ε; simp)
          have hQoff (τ : Interval) : HG (1,(τ,q))∉a.val.image :=
            hrightTail h₁ τ q (by change 1-ε≤ε+(1-2*ε)*1; linarith only [])
          let ΓL : {τ : Interval // HG (1,(τ,r))∈a.val.image} → C({t : Interval // t≠0},Interval) :=
            fun τ => False.elim (hRoff τ.val τ.property)
          let ΓU : {τ : Interval // HG (1,(τ,q))∈a.val.image} → C({t : Interval // t≠0},Interval) :=
            fun τ => False.elim (hQoff τ.val τ.property)
          have hΓLEnd (τ : {τ : Interval // HG (1,(τ,r))∈a.val.image}) : ΓL τ ⟨1,by simp⟩=τ.val :=
            False.elim (hRoff τ.val τ.property)
          have hΓUEnd (τ : {τ : Interval // HG (1,(τ,q))∈a.val.image}) : ΓU τ ⟨1,by simp⟩=τ.val :=
            False.elim (hQoff τ.val τ.property)
          have hΓLInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓL τ t) := by
            intro τ υ _
            exact False.elim (hRoff τ.val τ.property)
          have hΓUInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓU τ t) := by
            intro τ υ _
            exact False.elim (hQoff τ.val τ.property)
          refine ⟨r,q,hr₀,hq₁,hrq,HG,ΓL,ΓU,hΓLEnd,hΓLInjective,hΓUEnd,hΓUInjective,(by intro τ hτ; exact False.elim (hleftTail h₀ τ r (by change ε+(1-2*ε)*0≤ε; simp) hτ)),
            (by intro τ hτ; exact False.elim (hrightTail h₁ τ q (by change 1-ε≤ε+(1-2*ε)*1; linarith only []) hτ)),fun z => rfl,fun _ _ _ _ => rfl,
            fun _ _ _ _ => rfl,fun _ τ t ht₀ ht₁ => hFmarks τ t ht₀ ht₁,?_,?_,?_,?_,?_,?_⟩
          · apply finite_empty.subset
            intro τ hτ
            exact False.elim (hleftTail h₀ τ r (by change ε+(1-2*ε)*0≤ε; simp) hτ)
          · apply finite_empty.subset
            intro τ hτ
            exact False.elim (hrightTail h₁ τ q (by change 1-ε≤ε+(1-2*ε)*1; linarith only []) hτ)
          · intro t _ht₀ htr
            apply hleftTail h₀ 0 t
            change t.val≤ε+(1-2*ε)*0 at htr
            simpa using htr
          · intro t _ht₁ hqt
            apply hrightTail h₁ 0 t
            change ε+(1-2*ε)*1≤t.val at hqt
            linarith only [hqt]
          · intro τ hτ
            exact False.elim (hleftTail h₀ τ r (by change ε+(1-2*ε)*0≤ε;simp) hτ)
          · intro τ hτ
            exact False.elim (hrightTail h₁ τ q (by change 1-ε≤ε+(1-2*ε)*1;linarith only []) hτ)
  have hactualRedrawnFiniteBoundarySweep :
      ∃ HG : C(Interval × (Interval × Interval),S),
      ∃ φ : C(Interval,Interval),∃ G₁ : C(Interval × Interval,S),
      ∃ ΓLower : {τ : Interval // G₁ (τ,0)∈a.val.image} → C({t : Interval // t≠0},Interval),
      ∃ ΓUpper : {τ : Interval // G₁ (τ,1)∈a.val.image} → C({t : Interval // t≠0},Interval),
        (∀ τ,ΓLower τ ⟨1,by simp⟩=τ.val) ∧
        (∀ t,Function.Injective (fun τ => ΓLower τ t)) ∧
        (∀ τ,ΓUpper τ ⟨1,by simp⟩=τ.val) ∧
        (∀ t,Function.Injective (fun τ => ΓUpper τ t)) ∧
        (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => G₁ (τ,0),by fun_prop⟩ ∧
        (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => G₁ (τ,1),by fun_prop⟩ ∧
        (∀ z,HG (0,z)=F z) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t=0 ∨ t=1 → HG (η,(τ,t))=F (τ,t)) ∧
        (∀ η τ t,t≠0 → t≠1 → HG (η,(τ,t)) ∉ (M.cover.branch : Set S)) ∧
        (∀ t,0<(φ t).val ∧ (φ t).val<1) ∧
        Function.Injective φ ∧ StrictMono φ ∧
        (∀ t : Interval,b.val.map t ∈ ArcSurgery.crossings M a b → ∃ v : Interval,φ v=t) ∧
        (∀ z,G₁ z=HG (1,(z.1,φ z.2))) ∧
        (∀ t,G₁ (0,t)=b.val.map (φ t)) ∧
        (G₁ (0,0) ∉ a.val.image ∧ G₁ (0,1) ∉ a.val.image) ∧
        (∀ t,G₁ (1,t) ∉ a.val.image) ∧
        (∀ z,G₁ z ∉ (M.cover.branch : Set S)) ∧
        IsEmbedding (fun t : Interval => G₁ (0,t)) ∧
        {t : Interval | G₁ (0,t) ∈ a.val.image}.Finite ∧
        {τ : Interval | G₁ (τ,0) ∈ a.val.image}.Finite ∧
        {τ : Interval | G₁ (τ,1) ∈ a.val.image}.Finite ∧
        (∀ (τ : Interval) (hτ : G₁ (τ,0)∈a.val.image), b.val.map 0=af 0 ∧
          ∃ f : Path (af 0) (G₁ (τ,0)),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧ Γ=ΓLower ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,0) : ℝ × ℝ) (τ.val,(φ 0).val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,⟨(φ 0).val*t.val.val,by constructor <;> nlinarith only [(φ 0).property.1,(φ 0).property.2,t.val.property.1,t.val.property.2]⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,(φ 0).val*t.val.val)) ∧
              (∀ t : Interval,(P t).2=(φ 0).val*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap (φ 0).val (φ 1).val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=0 ∧ θ 1=φ 0 ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=G₁
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,0)) ∧
              α.Homotopic (v.trans w)) ∧
        (∀ (τ : Interval) (hτ : G₁ (τ,1)∈a.val.image), b.val.map 1=af 0 ∧
          ∃ f : Path (af 0) (G₁ (τ,1)),range f⊆a.val.image ∧
            (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
            ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=τ ∧ Γ=ΓUpper ⟨τ,hτ⟩ ∧
            ∃ P : Path ((0,1) : ℝ × ℝ) (τ.val,(φ 1).val),IsEmbedding P ∧
              (∀ t : {t : Interval // t≠0},f t.val=HG (1,(Γ t,⟨1-(1-(φ 1).val)*t.val.val,by constructor <;> nlinarith only [(φ 1).property.1,(φ 1).property.2,t.val.property.1,t.val.property.2]⟩))) ∧
              (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,1-(1-(φ 1).val)*t.val.val)) ∧
              (∀ t : Interval,(P t).2=1-(1-(φ 1).val)*t.val) ∧
            ∃ zQ : Interval × Interval,∃ Q : Path ((0,1) : Interval × Interval) zQ,
              IsEmbedding Q ∧
              (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap (φ 0).val (φ 1).val (Q t)=P t) ∧
              (∀ t : {t : Interval // t≠0},
                (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1) ∧
            ∃ θ : C(Interval,Interval),θ 0=1 ∧ θ 1=φ 1 ∧ IsEmbedding θ ∧
            ∃ (c y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
            ∃ α : Path c y,∃ v : Path c z,∃ w : Path z y,
              c.val=af 0 ∧ (∀ t,(α t).val=f t) ∧
              (∀ t,(v t).val=b.val.map (θ t)) ∧
              (∀ t,(w t).val=G₁
                (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
                  (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,1)) ∧
              α.Homotopic (v.trans w)) := by
    as_aux_lemma =>
      obtain ⟨r,q,hr₀,hq₁,hrq,HG,ΓLowerOld,ΓUpperOld,hΓLowerOldEnd,hΓLowerOldInjective,hΓUpperOldEnd,hΓUpperOldInjective,hLowerTransverse,hUpperTransverse,hzero,hboundary,hends,hmarks,hfiniteR,hfiniteQ,hSourceLower,hSourceUpper,hclosedR,hclosedQ⟩ :=
        hactualTwoFiniteInnerSeams
      have hrpos : 0<r.val := lt_of_le_of_ne r.property.1
        (by intro he; exact hr₀ (Subtype.ext he.symm))
      have hqlt : q.val<1 := lt_of_le_of_ne q.property.2
        (by intro he; exact hq₁ (Subtype.ext he))
      have hparamBounds (t : Interval) :
          0<r.val+(q.val-r.val)*t.val ∧ r.val+(q.val-r.val)*t.val<1 := by
        have hrqR : r.val<q.val := hrq
        have hbetween : r.val≤r.val+(q.val-r.val)*t.val ∧
            r.val+(q.val-r.val)*t.val≤q.val := by
          constructor <;> nlinarith only [hrqR,t.property.1,t.property.2]
        exact ⟨hrpos.trans_le hbetween.1,hbetween.2.trans_lt hqlt⟩
      let φ : C(Interval,Interval) := {
        toFun := fun t => ⟨r.val+(q.val-r.val)*t.val,(hparamBounds t).1.le,(hparamBounds t).2.le⟩
        continuous_toFun := by fun_prop }
      have hφinjective : Function.Injective φ := by
        intro s t he
        have hv := congrArg Subtype.val he
        change r.val+(q.val-r.val)*s.val=r.val+(q.val-r.val)*t.val at hv
        have hδ : q.val-r.val≠0 := ne_of_gt (sub_pos.mpr (show r.val<q.val from hrq))
        apply Subtype.ext
        exact mul_left_cancel₀ hδ (by linarith only [hv])
      have hSourceCapture (t : Interval) (ht : b.val.map t ∈ ArcSurgery.crossings M a b) :
          ∃ v : Interval,φ v=t := by
        have ht₀ : t≠0 := by
          intro he
          rw [he] at ht
          exact ht.1.2 b.val.start_marked
        have ht₁ : t≠1 := by
          intro he
          rw [he] at ht
          exact ht.1.2 b.val.end_marked
        have hsourceHit : F (0,t) ∈ a.val.image := by
          rw [hFzero]
          exact ht.1.1
        have hleft : r.val<t.val := lt_of_not_ge (fun he => hSourceLower t ht₀ he hsourceHit)
        have hright : t.val<q.val := lt_of_not_ge (fun he => hSourceUpper t ht₁ he hsourceHit)
        have hden : 0<q.val-r.val := sub_pos.mpr (show r.val<q.val from hrq)
        let v : Interval := ⟨(t.val-r.val)/(q.val-r.val),
          div_nonneg (sub_nonneg.mpr hleft.le) hden.le,
          (div_le_one hden).mpr (sub_le_sub_right hright.le r.val)⟩
        refine ⟨v,Subtype.ext ?_⟩
        change r.val+(q.val-r.val)*((t.val-r.val)/(q.val-r.val))=t.val
        rw [←mul_div_assoc,mul_div_cancel_left₀ _ hden.ne']
        ring
      have hφzero : φ 0=r := by
        apply Subtype.ext
        change r.val+(q.val-r.val)*0=r.val
        ring
      have hφone : φ 1=q := by
        apply Subtype.ext
        change r.val+(q.val-r.val)*1=q.val
        ring
      have hφmono : StrictMono φ :=
        φ.continuous.strictMono_of_inj_boundedOrder (by
          change φ (0 : Interval)≤φ (1 : Interval)
          rw [hφzero,hφone]
          exact hrq.le) hφinjective
      have hφne (t : Interval) : φ t≠0 ∧ φ t≠1 := by
        constructor
        · intro he
          exact (ne_of_gt (hparamBounds t).1) (congrArg Subtype.val he)
        · intro he
          exact (ne_of_lt (hparamBounds t).2) (congrArg Subtype.val he)
      let G₁ : C(Interval × Interval,S) := HG.comp {
        toFun := fun z => (1,(z.1,φ z.2))
        continuous_toFun := by fun_prop }
      let ΓLower : {τ : Interval // G₁ (τ,0)∈a.val.image} → C({t : Interval // t≠0},Interval) :=
        fun τ => ΓLowerOld ⟨τ.val,by
          have hh := τ.property
          change HG (1,(τ.val,φ 0))∈a.val.image at hh
          simpa only [hφzero] using hh⟩
      let ΓUpper : {τ : Interval // G₁ (τ,1)∈a.val.image} → C({t : Interval // t≠0},Interval) :=
        fun τ => ΓUpperOld ⟨τ.val,by
          have hh := τ.property
          change HG (1,(τ.val,φ 1))∈a.val.image at hh
          simpa only [hφone] using hh⟩
      have hΓLowerEnd (τ : {τ : Interval // G₁ (τ,0)∈a.val.image}) : ΓLower τ ⟨1,by simp⟩=τ.val :=
        hΓLowerOldEnd _
      have hΓUpperEnd (τ : {τ : Interval // G₁ (τ,1)∈a.val.image}) : ΓUpper τ ⟨1,by simp⟩=τ.val :=
        hΓUpperOldEnd _
      have hΓLowerInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓLower τ t) := by
        intro τ υ he
        have hh := hΓLowerOldInjective t he
        exact Subtype.ext (congrArg (fun z : {τ : Interval // HG (1,(τ,r))∈a.val.image} => z.val) hh)
      have hΓUpperInjective (t : {t : Interval // t≠0}) : Function.Injective (fun τ => ΓUpper τ t) := by
        intro τ υ he
        have hh := hΓUpperOldInjective t he
        exact Subtype.ext (congrArg (fun z : {τ : Interval // HG (1,(τ,q))∈a.val.image} => z.val) hh)
      have hCentralLowerTransverse : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => G₁ (τ,0),by fun_prop⟩ := by
        have htrace (τ : Interval) : G₁ (τ,0)=HG (1,(τ,r)) := by
          change HG (1,(τ,φ 0))=HG (1,(τ,r))
          rw [hφzero]
        intro τ hτ C hpC hCaxis
        change G₁ (τ,0)∈a.val.image at hτ
        change G₁ (τ,0)∈C.source at hpC
        rw [htrace] at hτ hpC
        obtain ⟨δ,hδ,hflip⟩ := hLowerTransverse τ hτ C hpC hCaxis
        refine ⟨δ,hδ,?_⟩
        intro v w hvlo hvu huw hwhi
        simpa only [ContinuousMap.coe_mk,htrace] using hflip v w hvlo hvu huw hwhi
      have hCentralUpperTransverse : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) ⟨fun τ => G₁ (τ,1),by fun_prop⟩ := by
        have htrace (τ : Interval) : G₁ (τ,1)=HG (1,(τ,q)) := by
          change HG (1,(τ,φ 1))=HG (1,(τ,q))
          rw [hφone]
        intro τ hτ C hpC hCaxis
        change G₁ (τ,1)∈a.val.image at hτ
        change G₁ (τ,1)∈C.source at hpC
        rw [htrace] at hτ hpC
        obtain ⟨δ,hδ,hflip⟩ := hUpperTransverse τ hτ C hpC hCaxis
        refine ⟨δ,hδ,?_⟩
        intro v w hvlo hvu huw hwhi
        simpa only [ContinuousMap.coe_mk,htrace] using hflip v w hvlo hvu huw hwhi
      have hG₁initial (t : Interval) : G₁ (0,t)=b.val.map (φ t) := by
        change HG (1,(0,φ t))=_
        rw [hboundary 1 0 (φ t) (Or.inl rfl),hFzero]
      let initialCurve : C(Interval,S) := G₁.comp {
        toFun := fun t => (0,t)
        continuous_toFun := by fun_prop }
      have hInitialInjective : Function.Injective initialCurve := by
        intro s t he
        apply hφinjective
        apply (NonLoopArc.injective ⟨b.val,hbne⟩)
        rw [←hG₁initial s,←hG₁initial t]
        exact he
      have hInitialEmbedding : IsEmbedding (fun t : Interval => G₁ (0,t)) :=
        (initialCurve.continuous.isClosedEmbedding hInitialInjective).isEmbedding
      have hInitialContactsFinite : {t : Interval | G₁ (0,t) ∈ a.val.image}.Finite := by
        apply (hcontacts.preimage hφinjective.injOn).subset
        intro t ht
        change b.val.map (φ t) ∈ a.val.image
        exact hG₁initial t ▸ ht
      refine ⟨HG,φ,G₁,ΓLower,ΓUpper,hΓLowerEnd,hΓLowerInjective,hΓUpperEnd,hΓUpperInjective,hCentralLowerTransverse,hCentralUpperTransverse,hzero,hboundary,hends,hmarks,hparamBounds,hφinjective,hφmono,hSourceCapture,
        fun z => rfl,hG₁initial,?_,?_,?_,hInitialEmbedding,hInitialContactsFinite,?_,?_,?_,?_⟩
      · constructor
        · rw [hG₁initial,hφzero,←hFzero]
          exact hSourceLower r hr₀ le_rfl
        · rw [hG₁initial,hφone,←hFzero]
          exact hSourceUpper q hq₁ le_rfl
      · intro t
        change HG (1,(1,φ t)) ∉ a.val.image
        rw [hboundary 1 1 (φ t) (Or.inr rfl)]
        exact hFterminalFull (φ t) (hφne t).1 (hφne t).2
      · intro z
        exact hmarks 1 z.1 (φ z.2) (hφne z.2).1 (hφne z.2).2
      · change {τ : Interval | HG (1,(τ,φ 0)) ∈ a.val.image}.Finite
        simpa only [hφzero] using hfiniteR
      · change {τ : Interval | HG (1,(τ,φ 1)) ∈ a.val.image}.Finite
        simpa only [hφone] using hfiniteQ
      · intro τ hτ
        have hh : HG (1,(τ,r))∈a.val.image := by
          change HG (1,(τ,φ 0))∈a.val.image at hτ
          simpa only [hφzero] using hτ
        obtain ⟨hshared,f,hf,hm,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩ := hclosedR τ hh
        have he : G₁ (τ,0)=HG (1,(τ,r)) := by
          change HG (1,(τ,φ 0))=HG (1,(τ,r))
          rw [hφzero]
        let P₁ := P.cast rfl (congrArg (fun h : Interval => (τ.val,h.val)) hφzero)
        refine ⟨hshared,f.cast rfl he,hf,hm,Γ,hΓτ,hΓChosen,P₁,hP,
          ?_,?_,?_,zQ,Q,hQ,?_,hQinside,θ,hθzero,
          hθone.trans hφzero.symm,hθemb,c,y,z,α,v,w,hc,hα,hv,?_,hhom⟩
        · intro t
          simpa only [P₁,Path.cast_coe,hφzero] using hΓtrace t
        · intro t
          simpa only [P₁,Path.cast_coe,hφzero] using hPtrace t
        · intro t
          simpa only [P₁,Path.cast_coe,hφzero] using hPsecond t
        · intro t
          simpa only [P₁,Path.cast_coe,hφzero,hφone] using hQP t
        · intro t
          change (w t).val=HG (1,
          (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
            (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,φ 0))
          rw [hφzero]
          exact hw t
      · intro τ hτ
        have hh : HG (1,(τ,q))∈a.val.image := by
          change HG (1,(τ,φ 1))∈a.val.image at hτ
          simpa only [hφone] using hτ
        obtain ⟨hshared,f,hf,hm,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,c,y,z,α,v,w,hc,hα,hv,hw,hhom⟩ := hclosedQ τ hh
        have he : G₁ (τ,1)=HG (1,(τ,q)) := by
          change HG (1,(τ,φ 1))=HG (1,(τ,q))
          rw [hφone]
        let P₁ := P.cast rfl (congrArg (fun h : Interval => (τ.val,h.val)) hφone)
        refine ⟨hshared,f.cast rfl he,hf,hm,Γ,hΓτ,hΓChosen,P₁,hP,
          ?_,?_,?_,zQ,Q,hQ,?_,hQinside,θ,hθzero,
          hθone.trans hφone.symm,hθemb,c,y,z,α,v,w,hc,hα,hv,?_,hhom⟩
        · intro t
          simpa only [P₁,Path.cast_coe,hφone] using hΓtrace t
        · intro t
          simpa only [P₁,Path.cast_coe,hφone] using hPtrace t
        · intro t
          simpa only [P₁,Path.cast_coe,hφone] using hPsecond t
        · intro t
          simpa only [P₁,Path.cast_coe,hφzero,hφone] using hQP t
        · intro t
          change (w t).val=HG (1,
          (⟨t.val*τ.val,mul_nonneg t.property.1 τ.property.1,
            (mul_le_of_le_one_right t.property.1 τ.property.2).trans t.property.2⟩,φ 1))
          rw [hφone]
          exact hw t
  obtain ⟨actualCornerDeformation,actualCentralParameter,actualCentralSweep,
    actualCentralLowerTailFamily,actualCentralUpperTailFamily,
    hActualCentralLowerTailFamilyEnd,hActualCentralLowerTailFamilyInjective,
    hActualCentralUpperTailFamilyEnd,hActualCentralUpperTailFamilyInjective,
    hActualCentralLowerTraceTransverse,hActualCentralUpperTraceTransverse,
    hActualDeformationInitial,hActualDeformationBoundary,hActualDeformationEnds,
    hActualDeformationMarks,hActualCentralParameterInterior,hActualCentralParameterInjective,hActualCentralParameterStrictMono,hActualOriginalCrossingCapture,hActualCentralSweepFormula,
    hActualCentralSweepInitial,hActualCentralInitialEndsOff,hActualCentralSweepTerminal,hActualCentralSweepMarks,
    hActualCentralSweepInitialEmbedding,hActualCentralInitialContactsFinite,
    hActualCentralLowerContactsFinite,hActualCentralUpperContactsFinite,
    hActualCentralLowerOriginalSharedContactTail,hActualCentralUpperOriginalSharedContactTail⟩ :=
    hactualRedrawnFiniteBoundarySweep
  have hActualCentralOriginalCrossingRealized (t : Interval)
      (ht : b.val.map t ∈ ArcSurgery.crossings M a b) :
      ∃ v : Interval,actualCentralSweep (0,v)=b.val.map t ∧
        actualCentralSweep (0,v) ∈ ArcSurgery.crossings M a b := by
    as_aux_lemma =>
      obtain ⟨v,hv⟩ := hActualOriginalCrossingCapture t ht
      refine ⟨v,?_,?_⟩
      · rw [hActualCentralSweepInitial,hv]
      · rw [hActualCentralSweepInitial,hv]
        exact ht
  have hActualCentralInitialContactsNonempty :
      {t : Interval | actualCentralSweep (0,t) ∈ a.val.image}.Nonempty := by
    as_aux_lemma =>
      obtain ⟨t,ht⟩ := hKnonempty
      obtain ⟨v,hv,hcross⟩ := hActualCentralOriginalCrossingRealized t ht
      exact ⟨v,hcross.1.1⟩
  have hActualCentralBoundaryBadFinite :
      ({t : Interval | actualCentralSweep (0,t) ∈ a.val.image} ∪
        {t : Interval | actualCentralSweep (t,0) ∈ a.val.image} ∪
        {t : Interval | actualCentralSweep (t,1) ∈ a.val.image}).Finite :=
    (hActualCentralInitialContactsFinite.union hActualCentralLowerContactsFinite).union
      hActualCentralUpperContactsFinite
  have hActualCentralClearBoundaryVertex (l u : Interval) (hlu : l<u) :
      ∃ t : Interval,l<t ∧ t<u ∧
        actualCentralSweep (0,t) ∉ a.val.image ∧
        actualCentralSweep (t,0) ∉ a.val.image ∧
        actualCentralSweep (t,1) ∉ a.val.image := by
    as_aux_lemma =>
      obtain ⟨t,ht,havoid⟩ := (Set.Ioo_infinite hlu).exists_notMem_finite hActualCentralBoundaryBadFinite
      refine ⟨t,ht.1,ht.2,?_,?_,?_⟩
      · intro hhit
        exact havoid (Or.inl (Or.inl hhit))
      · intro hhit
        exact havoid (Or.inl (Or.inr hhit))
      · intro hhit
        exact havoid (Or.inr hhit)
  have hActualCentralAllCornersOff (τ t : Interval) (hτ : τ=0 ∨ τ=1)
      (ht : t=0 ∨ t=1) : actualCentralSweep (τ,t) ∉ a.val.image := by
    as_aux_lemma =>
      rcases hτ with rfl | rfl
      · rcases ht with rfl | rfl
        · exact hActualCentralInitialEndsOff.1
        · exact hActualCentralInitialEndsOff.2
      · exact hActualCentralSweepTerminal t
  obtain ⟨actualContactGridSize,hActualContactGridPositive,actualContactGridParameter,
    hActualContactGridZero,hActualContactGridOne,hActualContactGridStrict,
    hActualContactGridBoundaryClear,hActualContactGridCover,
    actualContactGridCharts,hActualContactGridChartData,hActualContactGridChartContains⟩ :=
    actualFiniteBoundaryRelativeGrid actualCentralSweep hActualCentralSweepMarks
      hActualCentralSweepTerminal hActualCentralInitialEndsOff
      hActualCentralInitialContactsFinite hActualCentralLowerContactsFinite hActualCentralUpperContactsFinite
  have hActualContactGridCoversSweep (z : Interval × Interval) :
      ∃ k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1),
        actualContactGridParameter k.1.castSucc≤z.1 ∧ z.1≤ actualContactGridParameter k.1.succ ∧
        actualContactGridParameter k.2.castSucc≤z.2 ∧ z.2≤ actualContactGridParameter k.2.succ ∧
        actualCentralSweep z∈(actualContactGridCharts k).source := by
    as_aux_lemma =>
      obtain ⟨i,hi₀,hi₁⟩ := hActualContactGridCover z.1
      obtain ⟨j,hj₀,hj₁⟩ := hActualContactGridCover z.2
      exact ⟨(i,j),hi₀,hi₁,hj₀,hj₁,hActualContactGridChartContains (i,j) z hi₀ hi₁ hj₀ hj₁⟩
  have hActualCentralBottomContactStrictlyInsideEdge (t : Interval)
      (ht : actualCentralSweep (0,t)∈a.val.image) :
      ∃ k : Fin (actualContactGridSize+1),
        actualContactGridParameter k.castSucc<t ∧ t<actualContactGridParameter k.succ := by
    as_aux_lemma =>
      obtain ⟨k,hlo,hhi⟩ := hActualContactGridCover t
      refine ⟨k,lt_of_le_of_ne hlo ?_,lt_of_le_of_ne hhi ?_⟩
      · intro he
        exact (hActualContactGridBoundaryClear k.castSucc).1 (he.symm ▸ ht)
      · intro he
        exact (hActualContactGridBoundaryClear k.succ).1 (he ▸ ht)
  have hActualOriginalCrossingInsideContactGrid (t : Interval)
      (ht : b.val.map t∈ArcSurgery.crossings M a b) :
      ∃ v : Interval,∃ k : Fin (actualContactGridSize+1),
        actualCentralSweep (0,v)=b.val.map t ∧
        actualContactGridParameter k.castSucc<v ∧ v<actualContactGridParameter k.succ := by
    as_aux_lemma =>
      obtain ⟨v,hv,hcross⟩ := hActualCentralOriginalCrossingRealized t ht
      obtain ⟨k,hk₀,hk₁⟩ := hActualCentralBottomContactStrictlyInsideEdge v hcross.1.1
      exact ⟨v,k,hv,hk₀,hk₁⟩
  obtain ⟨actualGridVertices,hActualGridVerticesOff,actualGridVertexConnectors,
    hActualGridVertexConnectorMarks,hActualGridVertexConnectorCharts,hActualGridBoundaryConnectorsConstant⟩ :=
    actualCompatibleGridVertexConnectors actualCentralSweep hActualCentralSweepMarks
      hActualCentralSweepTerminal actualContactGridSize actualContactGridParameter
      hActualContactGridZero hActualContactGridOne hActualContactGridBoundaryClear
      actualContactGridCharts hActualContactGridChartContains
  have hActualGridVerticesFixedOnBoundary (v : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hv : v.1=0 ∨ v.1=Fin.last (actualContactGridSize+1) ∨
        v.2=0 ∨ v.2=Fin.last (actualContactGridSize+1)) :
      actualGridVertices v=actualCentralSweep (actualContactGridParameter v.1,actualContactGridParameter v.2) :=
    (actualGridVertexConnectors v).target.symm.trans (hActualGridBoundaryConnectorsConstant v hv 1)
  have hActualGridSharedEdge (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) :=
    actualCompatibleSharedEdge actualCentralSweep hActualCentralSweepMarks actualContactGridSize
      actualContactGridParameter actualContactGridCharts hActualContactGridChartContains
      actualGridVertices (fun v => (hActualGridVerticesOff v).1)
      actualGridVertexConnectors hActualGridVertexConnectorMarks hActualGridVertexConnectorCharts v w
  choose actualGridOriginalSegments hActualGridOriginalSegments hActualGridOriginalSegmentCharts
    actualGridRegularizedEdges hActualGridEdgeContactsFinite hActualGridEdgeMarks hActualGridEdgeCharts
    actualGridEdgeCarriers hActualGridEdgeCarrierStart hActualGridEdgeCarrierEnd
    hActualGridEdgeCarrierOpen hActualGridEdgeCarrierMarks actualGridEdgeLifts actualGridOriginalEdgeLifts
    hActualGridEdgeLift hActualGridOriginalEdgeLift hActualGridEdgeHomotopies using hActualGridSharedEdge
  have hActualGridOriginalSegmentsAffine
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) (t : Interval) :
      actualGridOriginalSegments v w t=actualCentralSweep
        (actualIntervalSegment (actualContactGridParameter v.1) (actualContactGridParameter w.1) t,
         actualIntervalSegment (actualContactGridParameter v.2) (actualContactGridParameter w.2) t) :=
    hActualGridOriginalSegments v w t
  have hActualGridOriginalSegmentMarks
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) (t : Interval) :
      actualGridOriginalSegments v w t∉(M.cover.branch : Set S) := by
    as_aux_lemma =>
      rw [hActualGridOriginalSegmentsAffine]
      exact hActualCentralSweepMarks _
  let actualBoundaryGridPair (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) : Prop :=
    (v.1=w.1 ∧ (v.1=0 ∨ v.1=Fin.last (actualContactGridSize+1))) ∨
      (v.2=w.2 ∧ (v.2=0 ∨ v.2=Fin.last (actualContactGridSize+1)))
  have hActualBoundaryGridPairEndpoints
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hvw : actualBoundaryGridPair v w) :
      (v.1=0 ∨ v.1=Fin.last (actualContactGridSize+1) ∨ v.2=0 ∨ v.2=Fin.last (actualContactGridSize+1)) ∧
      (w.1=0 ∨ w.1=Fin.last (actualContactGridSize+1) ∨ w.2=0 ∨ w.2=Fin.last (actualContactGridSize+1)) := by
    as_aux_lemma =>
      rcases hvw with ⟨he,hv|hv⟩ | ⟨he,hv|hv⟩
      · exact ⟨Or.inl hv,Or.inl (he.symm.trans hv)⟩
      · exact ⟨Or.inr (Or.inl hv),Or.inr (Or.inl (he.symm.trans hv))⟩
      · exact ⟨Or.inr (Or.inr (Or.inl hv)),Or.inr (Or.inr (Or.inl (he.symm.trans hv)))⟩
      · exact ⟨Or.inr (Or.inr (Or.inr hv)),Or.inr (Or.inr (Or.inr (he.symm.trans hv)))⟩
  have hActualGridBoundaryOriginalContactsFinite
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hvw : actualBoundaryGridPair v w) : (actualGridOriginalSegments v w ⁻¹' a.val.image).Finite := by
    as_aux_lemma =>
      have hvb := (hActualBoundaryGridPairEndpoints v w hvw).1
      have hvOff : actualCentralSweep (actualContactGridParameter v.1,actualContactGridParameter v.2)∉a.val.image := by
        rw [←hActualGridVerticesFixedOnBoundary v hvb]
        exact (hActualGridVerticesOff v).1
      apply actualBoundaryOriginalSegmentFinite actualCentralSweep hActualCentralSweepTerminal
        hActualCentralInitialContactsFinite hActualCentralLowerContactsFinite hActualCentralUpperContactsFinite
        (actualContactGridParameter v.1,actualContactGridParameter v.2)
        (actualContactGridParameter w.1,actualContactGridParameter w.2) hvOff
        (actualGridOriginalSegments v w) (hActualGridOriginalSegmentsAffine v w)
      rcases hvw with ⟨he,hv|hv⟩ | ⟨he,hv|hv⟩
      · exact Or.inl ⟨congrArg actualContactGridParameter he,Or.inl (by rw [hv,hActualContactGridZero])⟩
      · exact Or.inl ⟨congrArg actualContactGridParameter he,Or.inr (by rw [hv,hActualContactGridOne])⟩
      · exact Or.inr ⟨congrArg actualContactGridParameter he,Or.inl (by rw [hv,hActualContactGridZero])⟩
      · exact Or.inr ⟨congrArg actualContactGridParameter he,Or.inr (by rw [hv,hActualContactGridOne])⟩
  let actualCompatibleGridEdges
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) :
      Path (actualGridVertices v) (actualGridVertices w) :=
    if hb : actualBoundaryGridPair v w then
      (actualGridOriginalSegments v w).cast
        (hActualGridVerticesFixedOnBoundary v (hActualBoundaryGridPairEndpoints v w hb).1)
        (hActualGridVerticesFixedOnBoundary w (hActualBoundaryGridPairEndpoints v w hb).2)
    else actualGridRegularizedEdges v w
  have hActualCompatibleGridEdgesFinite
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) :
      (actualCompatibleGridEdges v w ⁻¹' a.val.image).Finite := by
    as_aux_lemma =>
      by_cases hb : actualBoundaryGridPair v w
      · simp only [actualCompatibleGridEdges,dif_pos hb]
        exact hActualGridBoundaryOriginalContactsFinite v w hb
      · simp only [actualCompatibleGridEdges,dif_neg hb]
        exact hActualGridEdgeContactsFinite v w
  have hActualCompatibleGridEdgesMarks
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2)) (t : Interval) :
      actualCompatibleGridEdges v w t∉(M.cover.branch : Set S) := by
    as_aux_lemma =>
      by_cases hb : actualBoundaryGridPair v w
      · simp only [actualCompatibleGridEdges,dif_pos hb]
        exact hActualGridOriginalSegmentMarks v w t
      · simp only [actualCompatibleGridEdges,dif_neg hb]
        exact hActualGridEdgeMarks v w t
  have hActualCompatibleGridEdgesCharts
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) (t : Interval)
      (hv₀ : actualContactGridParameter k.1.castSucc≤actualContactGridParameter v.1)
      (hv₁ : actualContactGridParameter v.1≤ actualContactGridParameter k.1.succ)
      (hv₂ : actualContactGridParameter k.2.castSucc≤actualContactGridParameter v.2)
      (hv₃ : actualContactGridParameter v.2≤ actualContactGridParameter k.2.succ)
      (hw₀ : actualContactGridParameter k.1.castSucc≤actualContactGridParameter w.1)
      (hw₁ : actualContactGridParameter w.1≤ actualContactGridParameter k.1.succ)
      (hw₂ : actualContactGridParameter k.2.castSucc≤actualContactGridParameter w.2)
      (hw₃ : actualContactGridParameter w.2≤ actualContactGridParameter k.2.succ) :
      actualCompatibleGridEdges v w t∈(actualContactGridCharts k).source := by
    as_aux_lemma =>
      by_cases hb : actualBoundaryGridPair v w
      · simp only [actualCompatibleGridEdges,dif_pos hb]
        exact hActualGridOriginalSegmentCharts v w k t hv₀ hv₁ hv₂ hv₃ hw₀ hw₁ hw₂ hw₃
      · simp only [actualCompatibleGridEdges,dif_neg hb]
        exact hActualGridEdgeCharts v w k t hv₀ hv₁ hv₂ hv₃ hw₀ hw₁ hw₂ hw₃
  have hActualCompatibleGridBoundaryEdgesExact
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hb : actualBoundaryGridPair v w) (t : Interval) :
      actualCompatibleGridEdges v w t=actualGridOriginalSegments v w t := by
    as_aux_lemma =>
      simp only [actualCompatibleGridEdges,dif_pos hb]
      rfl
  have hActualContactGridStep (i : Fin (actualContactGridSize+1)) :
      actualContactGridParameter i.castSucc<actualContactGridParameter i.succ :=
    hActualContactGridStrict (by change i.val < i.val+1; omega)
  let actualCellLowerLeft (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2) := (k.1.castSucc,k.2.castSucc)
  let actualCellLowerRight (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2) := (k.1.succ,k.2.castSucc)
  let actualCellUpperLeft (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2) := (k.1.castSucc,k.2.succ)
  let actualCellUpperRight (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2) := (k.1.succ,k.2.succ)
  have hActualCellCornerIncident
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (v : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hv₁ : v.1=k.1.castSucc ∨ v.1=k.1.succ) (hv₂ : v.2=k.2.castSucc ∨ v.2=k.2.succ) :
      actualContactGridParameter k.1.castSucc≤actualContactGridParameter v.1 ∧
        actualContactGridParameter v.1≤ actualContactGridParameter k.1.succ ∧
        actualContactGridParameter k.2.castSucc≤actualContactGridParameter v.2 ∧
        actualContactGridParameter v.2≤ actualContactGridParameter k.2.succ := by
    as_aux_lemma =>
      have hrow : actualContactGridParameter k.1.castSucc≤actualContactGridParameter v.1 ∧
          actualContactGridParameter v.1≤ actualContactGridParameter k.1.succ := by
        rcases hv₁ with he | he
        · rw [he]
          exact ⟨le_rfl,(hActualContactGridStep k.1).le⟩
        · rw [he]
          exact ⟨(hActualContactGridStep k.1).le,le_rfl⟩
      have hcol : actualContactGridParameter k.2.castSucc≤actualContactGridParameter v.2 ∧
          actualContactGridParameter v.2≤ actualContactGridParameter k.2.succ := by
        rcases hv₂ with he | he
        · rw [he]
          exact ⟨le_rfl,(hActualContactGridStep k.2).le⟩
        · rw [he]
          exact ⟨(hActualContactGridStep k.2).le,le_rfl⟩
      exact ⟨hrow.1,hrow.2,hcol.1,hcol.2⟩
  have hActualCellCornerVertexInChart
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (v : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hv₁ : v.1=k.1.castSucc ∨ v.1=k.1.succ) (hv₂ : v.2=k.2.castSucc ∨ v.2=k.2.succ) :
      actualGridVertices v∈(actualContactGridCharts k).source := by
    as_aux_lemma =>
      obtain ⟨h₀,h₁,h₂,h₃⟩ := hActualCellCornerIncident k v hv₁ hv₂
      have hh := hActualGridVertexConnectorCharts v k 1 h₀ h₁ h₂ h₃
      rwa [(actualGridVertexConnectors v).target] at hh
  have hActualCellCornerEdgeRange
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (v w : Fin (actualContactGridSize+2) × Fin (actualContactGridSize+2))
      (hv₁ : v.1=k.1.castSucc ∨ v.1=k.1.succ) (hv₂ : v.2=k.2.castSucc ∨ v.2=k.2.succ)
      (hw₁ : w.1=k.1.castSucc ∨ w.1=k.1.succ) (hw₂ : w.2=k.2.castSucc ∨ w.2=k.2.succ) :
      Set.range (actualCompatibleGridEdges v w)⊆(actualContactGridCharts k).source := by
    as_aux_lemma =>
      obtain ⟨hv₀,hv₁',hv₂',hv₃⟩ := hActualCellCornerIncident k v hv₁ hv₂
      obtain ⟨hw₀,hw₁',hw₂',hw₃⟩ := hActualCellCornerIncident k w hw₁ hw₂
      rintro z ⟨t,rfl⟩
      exact hActualCompatibleGridEdgesCharts v w k t hv₀ hv₁' hv₂' hv₃ hw₀ hw₁' hw₂' hw₃
  let actualCellBottomEdge (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualCompatibleGridEdges (actualCellLowerLeft k) (actualCellLowerRight k)
  let actualCellRightEdge (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualCompatibleGridEdges (actualCellLowerRight k) (actualCellUpperRight k)
  let actualCellTopEdge (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualCompatibleGridEdges (actualCellUpperLeft k) (actualCellUpperRight k)
  let actualCellLeftEdge (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualCompatibleGridEdges (actualCellLowerLeft k) (actualCellUpperLeft k)
  have hActualCellBottomRange (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Set.range (actualCellBottomEdge k)⊆(actualContactGridCharts k).source :=
    hActualCellCornerEdgeRange k (actualCellLowerLeft k) (actualCellLowerRight k)
      (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have hActualCellRightRange (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Set.range (actualCellRightEdge k)⊆(actualContactGridCharts k).source :=
    hActualCellCornerEdgeRange k (actualCellLowerRight k) (actualCellUpperRight k)
      (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have hActualCellTopRange (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Set.range (actualCellTopEdge k)⊆(actualContactGridCharts k).source :=
    hActualCellCornerEdgeRange k (actualCellUpperLeft k) (actualCellUpperRight k)
      (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have hActualCellLeftRange (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Set.range (actualCellLeftEdge k)⊆(actualContactGridCharts k).source :=
    hActualCellCornerEdgeRange k (actualCellLowerLeft k) (actualCellUpperLeft k)
      (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have hActualCellLowerLeftSource (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      actualGridVertices (actualCellLowerLeft k)∈(actualContactGridCharts k).source :=
    hActualCellCornerVertexInChart k (actualCellLowerLeft k) (Or.inl rfl) (Or.inl rfl)
  let actualCellCenters (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      (actualContactGridCharts k).target :=
    ⟨actualContactGridCharts k (actualGridVertices (actualCellLowerLeft k)),
      (actualContactGridCharts k).map_source (hActualCellLowerLeftSource k)⟩
  have hActualCellCenterAxisOff (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Disjoint (actualContactGridCharts k).source a.val.image ∨ (actualCellCenters k).val.1≠0 := by
    as_aux_lemma =>
      rcases (hActualContactGridChartData k).2.2 with hdis | haxis
      · exact Or.inl hdis
      · right
        intro hz
        exact (hActualGridVerticesOff (actualCellLowerLeft k)).1
          ((haxis _ (hActualCellLowerLeftSource k)).mpr hz)
  have hActualGridConeCellData (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    surfaceSquareFill (actualContactGridCharts k) (hActualContactGridChartData k).1
      (actualCellBottomEdge k) (actualCellRightEdge k) (actualCellTopEdge k) (actualCellLeftEdge k)
      (hActualCellBottomRange k) (hActualCellRightRange k) (hActualCellTopRange k) (hActualCellLeftRange k)
      (actualCellCenters k)
  choose actualConeCells actualCellBoundaryLoops hActualConeCellRange hActualConeCellBoundary
    hActualConeCellRadial using hActualGridConeCellData
  have hActualConeCellsMarks (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (z : Interval × Interval) : actualConeCells k z∉(M.cover.branch : Set S) :=
    fun hm => (Set.disjoint_left.mp (hActualContactGridChartData k).2.1) (hActualConeCellRange k z) hm
  have hActualConeCellsAdjacentFirst (i j : Fin (actualContactGridSize+1))
      (hij : i.val+1=j.val) (k : Fin (actualContactGridSize+1)) (t : Interval) :
      actualConeCells (i,k) (1,t)=actualConeCells (j,k) (0,t) := by
    as_aux_lemma =>
      have he : i.succ=j.castSucc := Fin.ext hij
      rw [(hActualConeCellBoundary (i,k) t).2.1,(hActualConeCellBoundary (j,k) t).2.2.2]
      change actualCompatibleGridEdges (i.succ,k.castSucc) (i.succ,k.succ) t=
        actualCompatibleGridEdges (j.castSucc,k.castSucc) (j.castSucc,k.succ) t
      rw [he]
  have hActualConeCellsAdjacentSecond (i j : Fin (actualContactGridSize+1))
      (hij : i.val+1=j.val) (k : Fin (actualContactGridSize+1)) (t : Interval) :
      actualConeCells (k,i) (t,1)=actualConeCells (k,j) (t,0) := by
    as_aux_lemma =>
      have he : i.succ=j.castSucc := Fin.ext hij
      rw [(hActualConeCellBoundary (k,i) t).2.2.1,(hActualConeCellBoundary (k,j) t).1]
      change actualCompatibleGridEdges (k.castSucc,i.succ) (k.succ,i.succ) t=
        actualCompatibleGridEdges (k.castSucc,j.castSucc) (k.succ,j.castSucc) t
      rw [he]
  obtain ⟨actualContactGridLocalCoordinate,hActualGridCoordinateReconstruct,
    hActualGridCoordinateLeft,hActualGridCoordinateRight,
    actualFiniteConeSweep,hActualFiniteConeSweepOnCell⟩ :=
    actualCoherentFiniteCellGlue actualContactGridSize actualContactGridParameter
      hActualContactGridStrict hActualContactGridCover actualConeCells
      (fun i j hij k t => hActualConeCellsAdjacentFirst i j hij k t)
      (fun i j hij k t => hActualConeCellsAdjacentSecond i j hij k t)
  have hActualFiniteConeSweepMarks (z : Interval × Interval) :
      actualFiniteConeSweep z∉(M.cover.branch : Set S) := by
    as_aux_lemma =>
      obtain ⟨k,h₀,h₁,h₂,h₃,_⟩ := hActualContactGridCoversSweep z
      rw [hActualFiniteConeSweepOnCell k z h₀ h₁ h₂ h₃]
      exact hActualConeCellsMarks k _
  have hActualIntervalSegmentConstant (x t : Interval) : actualIntervalSegment x x t=x := by
    as_aux_lemma =>
      apply Subtype.ext
      change (1-t.val)*x.val+t.val*x.val=x.val
      ring
  have hActualGridLocalCoordinateZero : actualContactGridLocalCoordinate (0 : Fin (actualContactGridSize+1)) 0=0 := by
    as_aux_lemma =>
      have he : (0 : Fin (actualContactGridSize+1)).castSucc=(0 : Fin (actualContactGridSize+2)) := rfl
      simpa only [he,hActualContactGridZero] using hActualGridCoordinateLeft (0 : Fin (actualContactGridSize+1))
  have hActualGridLocalCoordinateOne :
      actualContactGridLocalCoordinate (Fin.last actualContactGridSize) 1=1 := by
    as_aux_lemma =>
      have he : (Fin.last actualContactGridSize).succ=Fin.last (actualContactGridSize+1) := by apply Fin.ext; rfl
      simpa only [he,hActualContactGridOne] using hActualGridCoordinateRight (Fin.last actualContactGridSize)
  have hActualFiniteConeSweepInitial (t : Interval) : actualFiniteConeSweep (0,t)=actualCentralSweep (0,t) := by
    as_aux_lemma =>
      obtain ⟨j,hj₀,hj₁⟩ := hActualContactGridCover t
      have hlo : actualContactGridParameter (0 : Fin (actualContactGridSize+1)).castSucc≤(0 : Interval) := by
        change actualContactGridParameter (0 : Fin (actualContactGridSize+2))≤0
        rw [hActualContactGridZero]
      have hhi : (0 : Interval)≤actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ :=
        (actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ).property.1
      rw [hActualFiniteConeSweepOnCell (0,j) (0,t) hlo hhi hj₀ hj₁,hActualGridLocalCoordinateZero,
        (hActualConeCellBoundary (0,j) (actualContactGridLocalCoordinate j t)).2.2.2]
      change actualCompatibleGridEdges (0,j.castSucc) (0,j.succ) (actualContactGridLocalCoordinate j t)=actualCentralSweep (0,t)
      rw [hActualCompatibleGridBoundaryEdgesExact (0,j.castSucc) (0,j.succ) (Or.inl ⟨rfl,Or.inl rfl⟩),
        hActualGridOriginalSegmentsAffine,hActualContactGridZero,hActualIntervalSegmentConstant,
        hActualGridCoordinateReconstruct j t hj₀ hj₁]
  have hActualFiniteConeSweepTerminal (t : Interval) : actualFiniteConeSweep (1,t)=actualCentralSweep (1,t) := by
    as_aux_lemma =>
      obtain ⟨j,hj₀,hj₁⟩ := hActualContactGridCover t
      have he : (Fin.last actualContactGridSize).succ=Fin.last (actualContactGridSize+1) := by apply Fin.ext; rfl
      have hlo : actualContactGridParameter (Fin.last actualContactGridSize).castSucc≤(1 : Interval) :=
        (actualContactGridParameter (Fin.last actualContactGridSize).castSucc).property.2
      have hhi : (1 : Interval)≤actualContactGridParameter (Fin.last actualContactGridSize).succ := by
        rw [he,hActualContactGridOne]
      rw [hActualFiniteConeSweepOnCell (Fin.last actualContactGridSize,j) (1,t) hlo hhi hj₀ hj₁,
        hActualGridLocalCoordinateOne,
        (hActualConeCellBoundary (Fin.last actualContactGridSize,j) (actualContactGridLocalCoordinate j t)).2.1]
      change actualCompatibleGridEdges ((Fin.last actualContactGridSize).succ,j.castSucc)
        ((Fin.last actualContactGridSize).succ,j.succ) (actualContactGridLocalCoordinate j t)=actualCentralSweep (1,t)
      rw [he,hActualCompatibleGridBoundaryEdgesExact (Fin.last (actualContactGridSize+1),j.castSucc)
        (Fin.last (actualContactGridSize+1),j.succ) (Or.inl ⟨rfl,Or.inr rfl⟩),
        hActualGridOriginalSegmentsAffine,hActualContactGridOne,hActualIntervalSegmentConstant,
        hActualGridCoordinateReconstruct j t hj₀ hj₁]
  have hActualFiniteConeSweepLower (t : Interval) : actualFiniteConeSweep (t,0)=actualCentralSweep (t,0) := by
    as_aux_lemma =>
      obtain ⟨i,hi₀,hi₁⟩ := hActualContactGridCover t
      have hlo : actualContactGridParameter (0 : Fin (actualContactGridSize+1)).castSucc≤(0 : Interval) := by
        change actualContactGridParameter (0 : Fin (actualContactGridSize+2))≤0
        rw [hActualContactGridZero]
      have hhi : (0 : Interval)≤actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ :=
        (actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ).property.1
      rw [hActualFiniteConeSweepOnCell (i,0) (t,0) hi₀ hi₁ hlo hhi,hActualGridLocalCoordinateZero,
        (hActualConeCellBoundary (i,0) (actualContactGridLocalCoordinate i t)).1]
      change actualCompatibleGridEdges (i.castSucc,0) (i.succ,0) (actualContactGridLocalCoordinate i t)=actualCentralSweep (t,0)
      rw [hActualCompatibleGridBoundaryEdgesExact (i.castSucc,0) (i.succ,0) (Or.inr ⟨rfl,Or.inl rfl⟩),
        hActualGridOriginalSegmentsAffine,hActualContactGridZero,hActualIntervalSegmentConstant,
        hActualGridCoordinateReconstruct i t hi₀ hi₁]
  have hActualFiniteConeSweepUpper (t : Interval) : actualFiniteConeSweep (t,1)=actualCentralSweep (t,1) := by
    as_aux_lemma =>
      obtain ⟨i,hi₀,hi₁⟩ := hActualContactGridCover t
      have he : (Fin.last actualContactGridSize).succ=Fin.last (actualContactGridSize+1) := by apply Fin.ext; rfl
      have hlo : actualContactGridParameter (Fin.last actualContactGridSize).castSucc≤(1 : Interval) :=
        (actualContactGridParameter (Fin.last actualContactGridSize).castSucc).property.2
      have hhi : (1 : Interval)≤actualContactGridParameter (Fin.last actualContactGridSize).succ := by
        rw [he,hActualContactGridOne]
      rw [hActualFiniteConeSweepOnCell (i,Fin.last actualContactGridSize) (t,1) hi₀ hi₁ hlo hhi,
        hActualGridLocalCoordinateOne,
        (hActualConeCellBoundary (i,Fin.last actualContactGridSize) (actualContactGridLocalCoordinate i t)).2.2.1]
      change actualCompatibleGridEdges (i.castSucc,(Fin.last actualContactGridSize).succ)
        (i.succ,(Fin.last actualContactGridSize).succ) (actualContactGridLocalCoordinate i t)=actualCentralSweep (t,1)
      rw [he,hActualCompatibleGridBoundaryEdgesExact (i.castSucc,Fin.last (actualContactGridSize+1))
        (i.succ,Fin.last (actualContactGridSize+1)) (Or.inr ⟨rfl,Or.inr rfl⟩),
        hActualGridOriginalSegmentsAffine,hActualContactGridOne,hActualIntervalSegmentConstant,
        hActualGridCoordinateReconstruct i t hi₀ hi₁]
  have hActualFiniteConeOriginalCrossingCaptured (t : Interval)
      (ht : b.val.map t∈ArcSurgery.crossings M a b) :
      ∃ v : Interval,actualFiniteConeSweep (0,v)=b.val.map t := by
    as_aux_lemma =>
      obtain ⟨v,hv,_⟩ := hActualCentralOriginalCrossingRealized t ht
      exact ⟨v,(hActualFiniteConeSweepInitial v).trans hv⟩
  have hActualFiniteConeSweepTopAvoids (t : Interval) : actualFiniteConeSweep (1,t)∉a.val.image := by
    as_aux_lemma =>
      rw [hActualFiniteConeSweepTerminal]
      exact hActualCentralSweepTerminal t
  have hActualConstructedCellContactGeometry
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualMarkedConeCellGeometry (actualContactGridCharts k) (actualConeCells k)
      (actualCellBoundaryLoops k) (actualCellCenters k) (hActualConeCellRange k)
      (hActualContactGridChartData k).2.2 (hActualCellCenterAxisOff k) (hActualConeCellRadial k)
  have hActualConstructedCellBoundaryContactsFinite
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualSquareBoundaryContactsFinite (actualConeCells k)
      (actualCellBottomEdge k).toContinuousMap (actualCellRightEdge k).toContinuousMap
      (actualCellTopEdge k).toContinuousMap (actualCellLeftEdge k).toContinuousMap
      (hActualCompatibleGridEdgesFinite (actualCellLowerLeft k) (actualCellLowerRight k))
      (hActualCompatibleGridEdgesFinite (actualCellLowerRight k) (actualCellUpperRight k))
      (hActualCompatibleGridEdgesFinite (actualCellUpperLeft k) (actualCellUpperRight k))
      (hActualCompatibleGridEdgesFinite (actualCellLowerLeft k) (actualCellUpperLeft k))
      (hActualConeCellBoundary k)
  have hActualConstructedCellLoopAxisZerosFinite
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (haxis : ∀ x∈(actualContactGridCharts k).source,
        x∈a.val.image ↔ ((actualContactGridCharts k) x).1=0) :=
    actualBoundaryLoopAxisZerosFinite (actualContactGridCharts k) (actualConeCells k)
      (actualCellBoundaryLoops k) (actualCellCenters k) (hActualConeCellRange k) haxis
      (hActualConeCellRadial k) (hActualConstructedCellBoundaryContactsFinite k)
  have actualConstructedCellFiniteFaceMesh
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (haxis : ∀ x∈(actualContactGridCharts k).source,
        x∈a.val.image ↔ ((actualContactGridCharts k) x).1=0)
      (hc : (actualCellCenters k).val.1≠0) (i : Fin 4) :
      ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval,
        StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
        (∀ j,mesh j=0 ∨ mesh j=1 ∨
          (actualCellBoundaryLoops k (actualBoundaryFace i (mesh j))).val.1/(actualCellCenters k).val.1=0) ∧
        ∀ (j : Fin (m+1)) (t : Interval),
          mesh j.castSucc < t → t < mesh j.succ →
          (actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1/(actualCellCenters k).val.1≠0 := by
    as_aux_lemma =>
      let g : C({z : ℝ × ℝ // ‖z‖=1},ℝ) :=
        ⟨fun z => (actualCellBoundaryLoops k z).val.1/(actualCellCenters k).val.1,by fun_prop⟩
      have hg : (g ⁻¹' {0}).Finite := by
        apply (hActualConstructedCellLoopAxisZerosFinite k haxis).subset
        intro z hz
        change (actualCellBoundaryLoops k z).val.1/(actualCellCenters k).val.1=0 at hz
        simpa only [Set.mem_setOf_eq,div_eq_zero_iff,hc,or_false] using hz
      exact actualFiniteZeroMesh (g.comp (actualBoundaryFace i)) (actualFaceScalarZerosFinite g hg i)
  have actualConstructedCellNegativeFaceIntervals
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      Disjoint (actualContactGridCharts k).source a.val.image ∨
      ((actualCellCenters k).val.1≠0 ∧ ∀ i : Fin 4,
        ∃ m : ℕ, ∃ mesh : Fin (m+2) → Interval, ∃ negative : Fin (m+1) → Prop,
          StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
          (∀ j,mesh j=0 ∨ mesh j=1 ∨
            (actualCellBoundaryLoops k (actualBoundaryFace i (mesh j))).val.1/(actualCellCenters k).val.1=0) ∧
          (∀ (j : Fin (m+1)) (t : Interval),mesh j.castSucc < t → t < mesh j.succ →
            (actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1/(actualCellCenters k).val.1≠0) ∧
          (∀ j,negative j → ∀ t∈Set.Icc (mesh j.castSucc) (mesh j.succ),
            (actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1/(actualCellCenters k).val.1≤0) ∧
          ∀ t,(actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1/(actualCellCenters k).val.1≤0 ↔
            (actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1/(actualCellCenters k).val.1=0 ∨
              ∃ j,negative j ∧ t∈Set.Icc (mesh j.castSucc) (mesh j.succ)) := by
    as_aux_lemma =>
      by_cases hoff : Disjoint (actualContactGridCharts k).source a.val.image
      · exact Or.inl hoff
      right
      have haxis := (hActualContactGridChartData k).2.2.resolve_left hoff
      have hc := (hActualCellCenterAxisOff k).resolve_left hoff
      refine ⟨hc,?_⟩
      intro i
      let g : C({z : ℝ × ℝ // ‖z‖=1},ℝ) :=
        ⟨fun z => (actualCellBoundaryLoops k z).val.1/(actualCellCenters k).val.1,by fun_prop⟩
      have hg : (g ⁻¹' {0}).Finite := by
        apply (hActualConstructedCellLoopAxisZerosFinite k haxis).subset
        intro z hz
        change (actualCellBoundaryLoops k z).val.1/(actualCellCenters k).val.1=0 at hz
        simpa only [Set.mem_setOf_eq,div_eq_zero_iff,hc,or_false] using hz
      exact actualFiniteNegativeIntervals (g.comp (actualBoundaryFace i)) (actualFaceScalarZerosFinite g hg i)
  have hActualConstructedCellCornersOff
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :
      actualConeCells k (0,0)∉a.val.image ∧ actualConeCells k (1,0)∉a.val.image ∧
        actualConeCells k (0,1)∉a.val.image ∧ actualConeCells k (1,1)∉a.val.image := by
    as_aux_lemma =>
      constructor
      · rw [(hActualConeCellBoundary k 0).1,(actualCellBottomEdge k).source]
        exact (hActualGridVerticesOff _).1
      constructor
      · rw [(hActualConeCellBoundary k 1).1,(actualCellBottomEdge k).target]
        exact (hActualGridVerticesOff _).1
      constructor
      · rw [(hActualConeCellBoundary k 0).2.2.1,(actualCellTopEdge k).source]
        exact (hActualGridVerticesOff _).1
      · rw [(hActualConeCellBoundary k 1).2.2.1,(actualCellTopEdge k).target]
        exact (hActualGridVerticesOff _).1
  have actualConstructedCellFaceRadialComponents
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (hactive : ¬Disjoint (actualContactGridCharts k).source a.val.image) (i : Fin 4) :=
    actualFiniteFaceRadialComponents (actualContactGridCharts k) (actualConeCells k)
      (actualCellBoundaryLoops k) (actualCellCenters k) (hActualConeCellRange k)
      ((hActualContactGridChartData k).2.2.resolve_left hactive)
      ((hActualCellCenterAxisOff k).resolve_left hactive) (hActualConeCellRadial k)
      (hActualConstructedCellLoopAxisZerosFinite k
        ((hActualContactGridChartData k).2.2.resolve_left hactive)) i
  let actualOriginalBottomPath : C(Interval,S) :=
    actualCentralSweep.comp ⟨fun t => (0,t),continuous_const.prodMk continuous_id⟩
  have hActualOriginalBottomPathInjective : Set.InjOn actualOriginalBottomPath (Set.Ioo 0 1) :=
    hActualCentralSweepInitialEmbedding.injective.injOn
  have hActualOriginalBottomPathImage : Set.range actualOriginalBottomPath⊆b.val.image := by
    as_aux_lemma =>
      rintro x ⟨t,rfl⟩
      change actualCentralSweep (0,t)∈b.val.image
      rw [hActualCentralSweepInitial]
      exact ⟨actualCentralParameter t,rfl⟩
  have actualOriginalCrossingCellSigns (t : Interval)
      (ht : b.val.map t∈ArcSurgery.crossings M a b) :
      ∃ v : Interval,∃ j : Fin (actualContactGridSize+1),
        actualOriginalBottomPath v=b.val.map t ∧
        actualContactGridParameter j.castSucc < v ∧ v < actualContactGridParameter j.succ ∧
        ∃ δ : ℝ,0<δ ∧ ∀ l r : Interval,
          v.val-δ<l.val → l<v → v<r → r.val<v.val+δ →
          ((actualContactGridCharts (0,j)) (actualOriginalBottomPath l)).1≠0 ∧
          ((actualContactGridCharts (0,j)) (actualOriginalBottomPath r)).1≠0 ∧
          ((0<((actualContactGridCharts (0,j)) (actualOriginalBottomPath l)).1) ↔
            ¬(0<((actualContactGridCharts (0,j)) (actualOriginalBottomPath r)).1)) := by
    as_aux_lemma =>
      obtain ⟨v,j,hv,hj₀,hj₁⟩ := hActualOriginalCrossingInsideContactGrid t ht
      have hv0 : 0<v.val := lt_of_le_of_lt (actualContactGridParameter j.castSucc).property.1 hj₀
      have hv1 : v.val<1 := lt_of_lt_of_le hj₁ (actualContactGridParameter j.succ).property.2
      have hsource : actualOriginalBottomPath v∈(actualContactGridCharts (0,j)).source := by
        apply hActualContactGridChartContains (0,j) (0,v)
        · have he : (0 : Fin (actualContactGridSize+1)).castSucc=0 := rfl
          rw [he,hActualContactGridZero]
        · exact (actualContactGridParameter _).property.1
        · exact hj₀.le
        · exact hj₁.le
      have hmem : actualOriginalBottomPath v∈a.val.image := by
        change actualCentralSweep (0,v)∈a.val.image
        rw [hv]
        exact ht.1.1
      have hactive : ¬Disjoint (actualContactGridCharts (0,j)).source a.val.image :=
        fun hd => (Set.disjoint_left.mp hd) hsource hmem
      have haxis := (hActualContactGridChartData (0,j)).2.2.resolve_left hactive
      have hcross : ArcSurgery.CrossesInDisk M a b (actualOriginalBottomPath v) := by
        change ArcSurgery.CrossesInDisk M a b (actualCentralSweep (0,v))
        rw [hv]
        exact htransverse _ ht
      obtain ⟨δ,hδ,hflip⟩ := actual_marked_transverse_uncentered_axis_signs_flip
        M a b v ⟨hv0,hv1⟩ actualOriginalBottomPath hActualOriginalBottomPathInjective
        hActualOriginalBottomPathImage hcross (actualContactGridCharts (0,j)) hsource haxis
      exact ⟨v,j,hv,hj₀,hj₁,δ,hδ,hflip⟩
  have hActualAffineCellData (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) :=
    actualAffineCellEmbedding (actualContactGridParameter k.1.castSucc) (actualContactGridParameter k.1.succ)
      (actualContactGridParameter k.2.castSucc) (actualContactGridParameter k.2.succ)
      (hActualContactGridStep k.1) (hActualContactGridStep k.2)
  choose actualAffineCells hActualAffineCellEmbedding hActualAffineCellFormula hActualAffineCellBounds
    using hActualAffineCellData
  have hActualGlobalConeSweepAffineCell
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1)) (x : Interval × Interval) :
      actualFiniteConeSweep (actualAffineCells k x)=actualConeCells k x := by
    as_aux_lemma =>
      obtain ⟨h₀,h₁,h₂,h₃⟩ := hActualAffineCellBounds k x
      rw [hActualFiniteConeSweepOnCell k _ h₀ h₁ h₂ h₃]
      have hx₁ : actualContactGridLocalCoordinate k.1 (actualAffineCells k x).1=x.1 := by
        apply actualIntervalSegmentInjective _ _ (hActualContactGridStep k.1)
        rw [hActualGridCoordinateReconstruct k.1 _ h₀ h₁,hActualAffineCellFormula]
      have hx₂ : actualContactGridLocalCoordinate k.2 (actualAffineCells k x).2=x.2 := by
        apply actualIntervalSegmentInjective _ _ (hActualContactGridStep k.2)
        rw [hActualGridCoordinateReconstruct k.2 _ h₂ h₃,hActualAffineCellFormula]
      rw [hx₁,hx₂]
  let actualActiveContactCells := {k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1) |
    ¬Disjoint (actualContactGridCharts k).source a.val.image}
  have actualActiveFaceComponentData (p : actualActiveContactCells × Fin 4) :=
    actualConstructedCellFaceRadialComponents p.1.val p.1.property p.2
  choose actualFaceContactSize actualFaceContactMesh actualFaceContactRadial actualFaceContactMono
    actualFaceContactStart actualFaceContactEnd actualFaceContactNoZero actualFaceContactBoundaryFix
    actualFaceContactRadialFormula actualFaceContactArcs using actualActiveFaceComponentData
  let actualNegativeFaceIntervals := Σ p : actualActiveContactCells × Fin 4,
    {j : Fin (actualFaceContactSize p+1) |
      (actualCellBoundaryLoops p.1.val (actualBoundaryFace p.2
        (actualIntervalMidpoint (actualFaceContactMesh p j.castSucc) (actualFaceContactMesh p j.succ)))).val.1/
        (actualCellCenters p.1.val).val.1<0}
  have actualNegativeFaceArcData (e : actualNegativeFaceIntervals) :=
    actualFaceContactArcs e.1 e.2.val e.2.property
  choose actualLocalContactArcs hActualLocalContactArcEmbedding hActualLocalContactArcImage
    hActualLocalContactArcFormula actualLocalContactArcStart actualLocalContactArcEnd
    hActualLocalContactArcStartFace hActualLocalContactArcEndFace
    hActualLocalContactArcStart hActualLocalContactArcEnd using actualNegativeFaceArcData
  let actualGlobalContactArcs (e : actualNegativeFaceIntervals) : C(Interval,Interval × Interval) :=
    (actualAffineCells e.1.1.val).comp (actualLocalContactArcs e)
  have hActualGlobalContactArcEmbedding (e : actualNegativeFaceIntervals) :
      IsEmbedding (actualGlobalContactArcs e) :=
    (hActualAffineCellEmbedding e.1.1.val).comp (hActualLocalContactArcEmbedding e)
  have hActualGlobalContactArcImage (e : actualNegativeFaceIntervals) (t : Interval) :
      actualFiniteConeSweep (actualGlobalContactArcs e t)∈a.val.image := by
    as_aux_lemma =>
      change actualFiniteConeSweep (actualAffineCells e.1.1.val (actualLocalContactArcs e t))∈a.val.image
      rw [hActualGlobalConeSweepAffineCell]
      exact hActualLocalContactArcImage e t
  have hActualGlobalContactArcMarks (e : actualNegativeFaceIntervals) (t : Interval) :
      actualFiniteConeSweep (actualGlobalContactArcs e t)∉(M.cover.branch : Set S) :=
    hActualFiniteConeSweepMarks _
  have hActualFaceRadialsAgreeWithinCell (k : actualActiveContactCells) (i j : Fin 4)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) :
      actualFaceContactRadial (k,i) z=actualFaceContactRadial (k,j) z := by
    as_aux_lemma =>
      obtain ⟨u,hu,hur⟩ := actualFaceContactRadialFormula (k,i) z
      obtain ⟨v,hv,hvr⟩ := actualFaceContactRadialFormula (k,j) z
      have huv : u=v := Subtype.ext (hur.trans hvr.symm)
      exact hu.trans ((congrArg squareCoordinates huv).trans hv.symm)
  have hActualNegativeFaceIntervalsFinite : Finite actualNegativeFaceIntervals := inferInstance
  have actualCompleteRadialData (k : actualActiveContactCells) :=
    actualMarkedConeCellZeroSet (actualContactGridCharts k.val) (actualConeCells k.val)
      (actualCellBoundaryLoops k.val) (actualCellCenters k.val) (hActualConeCellRange k.val)
      ((hActualContactGridChartData k.val).2.2.resolve_left k.property)
      ((hActualCellCenterAxisOff k.val).resolve_left k.property) (hActualConeCellRadial k.val)
  choose actualCompleteCellRadial hActualCompleteCellRadialInjective
    hActualCompleteCellRadialRange hActualCompleteCellRadialFormula using actualCompleteRadialData
  have hActualCompleteRadialMatchesFace (k : actualActiveContactCells) (i : Fin 4)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) :
      actualCompleteCellRadial k z=actualFaceContactRadial (k,i) z := by
    as_aux_lemma =>
      obtain ⟨u,hu,hur⟩ := hActualCompleteCellRadialFormula k z
      obtain ⟨v,hv,hvr⟩ := actualFaceContactRadialFormula (k,i) z
      exact hu.trans ((congrArg squareCoordinates (Subtype.ext (hur.trans hvr.symm))).trans hv.symm)
  let actualCellSkeletonNodePosition (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (z : {z : ℝ × ℝ // ‖z‖=1}) : Interval × Interval :=
    actualAffineCells k (squareCoordinates ⟨z.val,z.property.le⟩)
  let actualSkeletonContactNodes : Set (Interval × Interval) :=
    ⋃ k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1),
      actualCellSkeletonNodePosition k ''
        {z : {z : ℝ × ℝ // ‖z‖=1} |
          actualConeCells k (squareCoordinates ⟨z.val,z.property.le⟩)∈a.val.image}
  have hActualSkeletonContactNodesFinite : actualSkeletonContactNodes.Finite :=
    Set.finite_iUnion (fun k => (hActualConstructedCellBoundaryContactsFinite k).image
      (actualCellSkeletonNodePosition k))
  have hActualCompleteCellRadialContactCover (k : actualActiveContactCells)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) :
      actualAffineCells k.val (actualCompleteCellRadial k z)∈actualSkeletonContactNodes ∨
        ∃ e : actualNegativeFaceIntervals,∃ w : Interval,
          actualGlobalContactArcs e w=actualAffineCells k.val (actualCompleteCellRadial k z) := by
    as_aux_lemma =>
      by_cases hz0 : (actualCellBoundaryLoops k.val z.val).val.1=0
      · left
        obtain ⟨u,hu,hur⟩ := hActualCompleteCellRadialFormula k z
        have hu' : u=⟨z.val.val,z.val.property.le⟩ := by
          apply Subtype.ext
          simpa [hz0] using hur
        have hq : actualCompleteCellRadial k z=squareCoordinates ⟨z.val.val,z.val.property.le⟩ :=
          hu.trans (congrArg squareCoordinates hu')
        apply Set.mem_iUnion.mpr
        refine ⟨k.val,z.val,?_,?_⟩
        · have hcontact : actualConeCells k.val (actualCompleteCellRadial k z)∈a.val.image := by
            have hh : actualCompleteCellRadial k z∈Set.range (actualCompleteCellRadial k) := ⟨z,rfl⟩
            rw [hActualCompleteCellRadialRange k] at hh
            exact hh
          rwa [hq] at hcontact
        · change actualAffineCells k.val (squareCoordinates ⟨z.val.val,z.val.property.le⟩)=_
          rw [hq]
      · right
        obtain ⟨i,t,hit⟩ := actualBoundaryFaceCover z.val
        let p : actualActiveContactCells × Fin 4 := (k,i)
        let g : C(Interval,ℝ) :=
          ⟨fun s => (actualCellBoundaryLoops k.val (actualBoundaryFace i s)).val.1/
            (actualCellCenters k.val).val.1,by fun_prop⟩
        have hc : (actualCellCenters k.val).val.1≠0 :=
          (hActualCellCenterAxisOff k.val).resolve_left k.property
        have htneg : g t<0 := by
          change (actualCellBoundaryLoops k.val (actualBoundaryFace i t)).val.1/(actualCellCenters k.val).val.1<0
          rw [hit]
          exact lt_of_le_of_ne z.property (div_ne_zero hz0 hc)
        obtain ⟨j,hj0,hj1⟩ := actualOrderedMeshCovers (actualFaceContactMesh p)
          (actualFaceContactMono p) (actualFaceContactStart p) (actualFaceContactEnd p) t
        have hxy : actualFaceContactMesh p j.castSucc < actualFaceContactMesh p j.succ :=
          actualFaceContactMono p (by change j.val < j.val+1; omega)
        have hmid : actualFaceContactMesh p j.castSucc <
            actualIntervalMidpoint (actualFaceContactMesh p j.castSucc) (actualFaceContactMesh p j.succ) ∧
            actualIntervalMidpoint (actualFaceContactMesh p j.castSucc) (actualFaceContactMesh p j.succ) <
              actualFaceContactMesh p j.succ := by
          have hxyR : (actualFaceContactMesh p j.castSucc).val < (actualFaceContactMesh p j.succ).val := hxy
          constructor
          · change (actualFaceContactMesh p j.castSucc).val <
              ((actualFaceContactMesh p j.castSucc).val+(actualFaceContactMesh p j.succ).val)/2
            linarith only [hxyR]
          · change ((actualFaceContactMesh p j.castSucc).val+(actualFaceContactMesh p j.succ).val)/2 <
              (actualFaceContactMesh p j.succ).val
            linarith only [hxyR]
        have hno (s : Interval) (hs0 : actualFaceContactMesh p j.castSucc < s)
            (hs1 : s < actualFaceContactMesh p j.succ) : g s≠0 :=
          div_ne_zero (actualFaceContactNoZero p j s hs0 hs1) hc
        have hneg := actualClosedNegativeSample g _ _ _ t hmid hno ⟨hj0,hj1⟩ htneg
        let e : actualNegativeFaceIntervals := ⟨p,⟨j,hneg⟩⟩
        obtain ⟨w,hw⟩ := actualIntervalSegmentSurjectiveOnBounds
          (actualFaceContactMesh p j.castSucc) (actualFaceContactMesh p j.succ) t ⟨hj0,hj1⟩
        obtain ⟨r,zr,hr,hzr,hp,_⟩ := hActualLocalContactArcFormula e w
        have hrt : r=t := by
          apply Subtype.ext
          exact hr.trans (congrArg Subtype.val hw)
        have hzr' : zr=z := by
          apply Subtype.ext
          exact hzr.trans ((congrArg (actualBoundaryFace i) hrt).trans hit)
        refine ⟨e,w,?_⟩
        change actualAffineCells k.val (actualLocalContactArcs e w)=_
        rw [hp,hzr',←hActualCompleteRadialMatchesFace k i z]
  have hActualFiniteConeContactCover (x : Interval × Interval)
      (hx : actualFiniteConeSweep x∈a.val.image) :
      x∈actualSkeletonContactNodes ∨ ∃ e : actualNegativeFaceIntervals,∃ t : Interval,
        actualGlobalContactArcs e t=x := by
    as_aux_lemma =>
      obtain ⟨k,h₀,h₁,h₂,h₃,_⟩ := hActualContactGridCoversSweep x
      let y : Interval × Interval :=
        (actualContactGridLocalCoordinate k.1 x.1,actualContactGridLocalCoordinate k.2 x.2)
      have hy : actualConeCells k y∈a.val.image := by
        rw [hActualFiniteConeSweepOnCell k x h₀ h₁ h₂ h₃] at hx
        exact hx
      have hactive : ¬Disjoint (actualContactGridCharts k).source a.val.image :=
        fun hd => (Set.disjoint_left.mp hd) (hActualConeCellRange k y) hy
      let ka : actualActiveContactCells := ⟨k,hactive⟩
      have hyr : y∈Set.range (actualCompleteCellRadial ka) := by
        rw [hActualCompleteCellRadialRange ka]
        exact hy
      obtain ⟨z,hz⟩ := hyr
      have hxy : actualAffineCells k y=x := by
        rw [hActualAffineCellFormula]
        exact Prod.ext (hActualGridCoordinateReconstruct k.1 x.1 h₀ h₁)
          (hActualGridCoordinateReconstruct k.2 x.2 h₂ h₃)
      rcases hActualCompleteCellRadialContactCover ka z with hskel | ⟨e,t,he⟩
      · left
        change actualAffineCells k (actualCompleteCellRadial ka z)∈actualSkeletonContactNodes at hskel
        rw [hz,hxy] at hskel
        exact hskel
      · right
        exact ⟨e,t,he.trans ((congrArg (actualAffineCells k) hz).trans hxy)⟩
  have hActualLocalContactArcStrictInterior (e : actualNegativeFaceIntervals) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      (actualLocalContactArcs e t).1∈Set.Ioo (0 : Interval) 1 ∧
        (actualLocalContactArcs e t).2∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨r,z,hr,hz,hp,hnegative⟩ := hActualLocalContactArcFormula e t
      obtain ⟨u,hu,hur⟩ := actualFaceContactRadialFormula e.1 z
      rw [hp,hu]
      exact actualNegativeRadialPointInterior z.val
        ((actualCellBoundaryLoops e.1.1.val z.val).val.1/(actualCellCenters e.1.1.val).val.1)
        (hnegative ht) u hur
  have hActualGlobalContactArcStrictCell (e : actualNegativeFaceIntervals) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      actualContactGridParameter e.1.1.val.1.castSucc < (actualGlobalContactArcs e t).1 ∧
        (actualGlobalContactArcs e t).1 < actualContactGridParameter e.1.1.val.1.succ ∧
        actualContactGridParameter e.1.1.val.2.castSucc < (actualGlobalContactArcs e t).2 ∧
        (actualGlobalContactArcs e t).2 < actualContactGridParameter e.1.1.val.2.succ := by
    as_aux_lemma =>
      obtain ⟨h₁,h₂⟩ := hActualLocalContactArcStrictInterior e t ht
      change actualContactGridParameter e.1.1.val.1.castSucc <
        (actualAffineCells e.1.1.val (actualLocalContactArcs e t)).1 ∧
        (actualAffineCells e.1.1.val (actualLocalContactArcs e t)).1 < actualContactGridParameter e.1.1.val.1.succ ∧
        actualContactGridParameter e.1.1.val.2.castSucc < (actualAffineCells e.1.1.val (actualLocalContactArcs e t)).2 ∧
        (actualAffineCells e.1.1.val (actualLocalContactArcs e t)).2 < actualContactGridParameter e.1.1.val.2.succ
      rw [hActualAffineCellFormula]
      obtain ⟨hl₁,hr₁⟩ := actualIntervalSegmentInterior _ _ _ (hActualContactGridStep e.1.1.val.1) h₁
      obtain ⟨hl₂,hr₂⟩ := actualIntervalSegmentInterior _ _ _ (hActualContactGridStep e.1.1.val.2) h₂
      exact ⟨hl₁,hr₁,hl₂,hr₂⟩
  have hActualGridStrictIntervalUnique (i j : Fin (actualContactGridSize+1)) (x : Interval)
      (hi : actualContactGridParameter i.castSucc < x ∧ x < actualContactGridParameter i.succ)
      (hj : actualContactGridParameter j.castSucc < x ∧ x < actualContactGridParameter j.succ) : i=j := by
    as_aux_lemma =>
      rcases lt_trichotomy i j with hij | hij | hij
      · have hstep : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
        exact False.elim ((not_lt_of_ge ((hActualContactGridStrict.monotone hstep).trans hj.1.le)) hi.2)
      · exact hij
      · have hstep : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact hij
        exact False.elim ((not_lt_of_ge ((hActualContactGridStrict.monotone hstep).trans hi.1.le)) hj.2)
  have hActualGlobalContactArcInteriorCellUnique (e f : actualNegativeFaceIntervals)
      (t u : Interval) (ht : t∈Set.Ioo (0 : Interval) 1) (hu : u∈Set.Ioo (0 : Interval) 1)
      (he : actualGlobalContactArcs e t=actualGlobalContactArcs f u) : e.1.1.val=f.1.1.val := by
    as_aux_lemma =>
      obtain ⟨he₀,he₁,he₂,he₃⟩ := hActualGlobalContactArcStrictCell e t ht
      obtain ⟨hf₀,hf₁,hf₂,hf₃⟩ := hActualGlobalContactArcStrictCell f u hu
      rw [←he] at hf₀ hf₁ hf₂ hf₃
      exact Prod.ext (hActualGridStrictIntervalUnique _ _ _ ⟨he₀,he₁⟩ ⟨hf₀,hf₁⟩)
        (hActualGridStrictIntervalUnique _ _ _ ⟨he₂,he₃⟩ ⟨hf₂,hf₃⟩)
  have hActualLocalContactParameterInterior (e : actualNegativeFaceIntervals) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      ∃ r : Interval,∃ z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops e.1.1.val z).val.1/(actualCellCenters e.1.1.val).val.1≤0},
        z.val=actualBoundaryFace e.1.2 r ∧
        actualLocalContactArcs e t=actualFaceContactRadial e.1 z ∧
        r∈Set.Ioo (actualFaceContactMesh e.1 e.2.val.castSucc) (actualFaceContactMesh e.1 e.2.val.succ) ∧
        r∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨r,z,hr,hz,hp,_⟩ := hActualLocalContactArcFormula e t
      have hseg : r=actualIntervalSegment (actualFaceContactMesh e.1 e.2.val.castSucc)
          (actualFaceContactMesh e.1 e.2.val.succ) t := Subtype.ext hr
      have hstep : actualFaceContactMesh e.1 e.2.val.castSucc < actualFaceContactMesh e.1 e.2.val.succ :=
        actualFaceContactMono e.1 (by change e.2.val.val < e.2.val.val+1; omega)
      have hri : r∈Set.Ioo (actualFaceContactMesh e.1 e.2.val.castSucc)
          (actualFaceContactMesh e.1 e.2.val.succ) := by
        rw [hseg]
        exact actualIntervalSegmentInterior _ _ _ hstep ht
      have hr01 : r∈Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_lt (actualFaceContactMesh e.1 e.2.val.castSucc).property.1 hri.1,
          lt_of_lt_of_le hri.2 (actualFaceContactMesh e.1 e.2.val.succ).property.2⟩
      exact ⟨r,z,hz,hp,hri,hr01⟩
  have hActualGlobalContactArcInteriorsDisjoint (e f : actualNegativeFaceIntervals) (t u : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) (hu : u∈Set.Ioo (0 : Interval) 1)
      (heq : actualGlobalContactArcs e t=actualGlobalContactArcs f u) : e=f := by
    as_aux_lemma =>
      have hcell := hActualGlobalContactArcInteriorCellUnique e f t u ht hu heq
      rcases e with ⟨⟨k,i⟩,x⟩
      rcases f with ⟨⟨l,j⟩,y⟩
      have hkl : k=l := Subtype.ext hcell
      subst l
      have hp : actualLocalContactArcs ⟨(k,i),x⟩ t=actualLocalContactArcs ⟨(k,j),y⟩ u :=
        (hActualAffineCellEmbedding k.val).injective heq
      obtain ⟨r,z,hz,hzp,hr,hr01⟩ := hActualLocalContactParameterInterior ⟨(k,i),x⟩ t ht
      obtain ⟨s,w,hw,hwp,hs,hs01⟩ := hActualLocalContactParameterInterior ⟨(k,j),y⟩ u hu
      have hzw : z=w := hActualCompleteCellRadialInjective k
        ((hActualCompleteRadialMatchesFace k i z).trans
          (hzp.symm.trans (hp.trans (hwp.trans (hActualCompleteRadialMatchesFace k j w).symm))))
      have hface : actualBoundaryFace i r=actualBoundaryFace j s :=
        hz.symm.trans ((congrArg Subtype.val hzw).trans hw)
      have hij : i=j := actualBoundaryFaceInteriorUnique i j r s hr01 hs01 hface
      subst j
      have hrs : r=s := hActualBoundaryFaceInjective i hface
      rw [←hrs] at hs
      have hxy : x.val=y.val := by
        rcases lt_trichotomy x.val y.val with hlt | he | hgt
        · have hle : x.val.succ≤y.val.castSucc := by
            change x.val.val+1≤y.val.val
            exact hlt
          have hm := (actualFaceContactMono (k,i)).monotone hle
          exact False.elim (not_lt_of_ge (le_trans hm hs.1.le) hr.2)
        · exact he
        · have hle : y.val.succ≤x.val.castSucc := by
            change y.val.val+1≤x.val.val
            exact hgt
          have hm := (actualFaceContactMono (k,i)).monotone hle
          exact False.elim (not_lt_of_ge (le_trans hm hr.1.le) hs.2)
      have hxy' : x=y := Subtype.ext hxy
      subst y
      rfl
  have hActualGridOpenClosedUnique (i j : Fin (actualContactGridSize+1)) (r : Interval)
      (hi : r∈Set.Ioo (actualContactGridParameter i.castSucc) (actualContactGridParameter i.succ))
      (hj : r∈Set.Icc (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ)) : i=j := by
    as_aux_lemma =>
      rcases lt_trichotomy i j with hij | hij | hji
      · have hle : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
        have hm := hActualContactGridStrict.monotone hle
        exact False.elim (not_lt_of_ge (le_trans hm hj.1) hi.2)
      · exact hij
      · have hle : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact hji
        have hm := hActualContactGridStrict.monotone hle
        exact False.elim (not_lt_of_ge (le_trans hj.2 hm) hi.1)
  have hActualGlobalContactArcClosedCell (e : actualNegativeFaceIntervals) (t : Interval) :
      (actualGlobalContactArcs e t).1∈Set.Icc (actualContactGridParameter e.1.1.val.1.castSucc)
        (actualContactGridParameter e.1.1.val.1.succ) ∧
      (actualGlobalContactArcs e t).2∈Set.Icc (actualContactGridParameter e.1.1.val.2.castSucc)
        (actualContactGridParameter e.1.1.val.2.succ) := by
    as_aux_lemma =>
      obtain ⟨h₀,h₁,h₂,h₃⟩ := hActualAffineCellBounds e.1.1.val (actualLocalContactArcs e t)
      exact ⟨⟨h₀,h₁⟩,⟨h₂,h₃⟩⟩
  have hActualGlobalContactArcInteriorAvoidEndpoints (e f : actualNegativeFaceIntervals) (t v : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) (hv : v=0 ∨ v=1) :
      actualGlobalContactArcs e t≠actualGlobalContactArcs f v := by
    as_aux_lemma =>
      intro heq
      obtain ⟨he₀,he₁,he₂,he₃⟩ := hActualGlobalContactArcStrictCell e t ht
      obtain ⟨hf₁,hf₂⟩ := hActualGlobalContactArcClosedCell f v
      rw [←heq] at hf₁ hf₂
      have hcell : e.1.1.val=f.1.1.val := Prod.ext
        (hActualGridOpenClosedUnique _ _ _ ⟨he₀,he₁⟩ hf₁)
        (hActualGridOpenClosedUnique _ _ _ ⟨he₂,he₃⟩ hf₂)
      rcases e with ⟨⟨k,i⟩,x⟩
      rcases f with ⟨⟨l,j⟩,y⟩
      have hkl : k=l := Subtype.ext hcell
      subst l
      have hp : actualLocalContactArcs ⟨(k,i),x⟩ t=actualLocalContactArcs ⟨(k,j),y⟩ v :=
        (hActualAffineCellEmbedding k.val).injective heq
      obtain ⟨r,z,hz,hzp,hr,hr01⟩ := hActualLocalContactParameterInterior ⟨(k,i),x⟩ t ht
      obtain ⟨s,w,hsval,hw,hwp,hneg⟩ := hActualLocalContactArcFormula ⟨(k,j),y⟩ v
      have hzw : z=w := hActualCompleteCellRadialInjective k
        ((hActualCompleteRadialMatchesFace k i z).trans
          (hzp.symm.trans (hp.trans (hwp.trans (hActualCompleteRadialMatchesFace k j w).symm))))
      have hface : actualBoundaryFace i r=actualBoundaryFace j s :=
        hz.symm.trans ((congrArg Subtype.val hzw).trans hw)
      have hij : i=j := actualBoundaryFaceOpenUnique i j r s hr01 hface
      subst j
      have hrs : r=s := hActualBoundaryFaceInjective i hface
      have noMeshVertex (q : Fin (actualFaceContactSize (k,i)+2))
          (hq : r=actualFaceContactMesh (k,i) q) : False := by
        rw [hq] at hr
        exact actualOrderedMeshNoNodesInside _ (actualFaceContactMesh (k,i))
          (actualFaceContactMono (k,i)) x.val q hr
      rcases hv with hv | hv
      · have hs : s=actualFaceContactMesh (k,i) y.val.castSucc := by
          apply Subtype.ext
          simpa [hv] using hsval
        exact noMeshVertex _ (hrs.trans hs)
      · have hs : s=actualFaceContactMesh (k,i) y.val.succ := by
          apply Subtype.ext
          simpa [hv] using hsval
        exact noMeshVertex _ (hrs.trans hs)
  have hActualContactArcCollisionClassification (e f : actualNegativeFaceIntervals) (t u : Interval)
      (he : actualGlobalContactArcs e t=actualGlobalContactArcs f u) :
      (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
    as_aux_lemma =>
      by_cases ht : t=0 ∨ t=1
      · by_cases hu : u=0 ∨ u=1
        · exact Or.inr ⟨ht,hu⟩
        · have huI : u∈Set.Ioo (0 : Interval) 1 :=
            ⟨lt_of_le_of_ne u.property.1 (fun h => hu (Or.inl h.symm)),
              lt_of_le_of_ne u.property.2 (fun h => hu (Or.inr h))⟩
          exact False.elim (hActualGlobalContactArcInteriorAvoidEndpoints f e u t huI ht he.symm)
      · have htI : t∈Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (fun h => ht (Or.inl h.symm)),
            lt_of_le_of_ne t.property.2 (fun h => ht (Or.inr h))⟩
        by_cases hu : u=0 ∨ u=1
        · exact False.elim (hActualGlobalContactArcInteriorAvoidEndpoints e f t u htI hu he)
        · have huI : u∈Set.Ioo (0 : Interval) 1 :=
            ⟨lt_of_le_of_ne u.property.1 (fun h => hu (Or.inl h.symm)),
              lt_of_le_of_ne u.property.2 (fun h => hu (Or.inr h))⟩
          have hef := hActualGlobalContactArcInteriorsDisjoint e f t u htI huI he
          subst f
          exact Or.inl ⟨rfl,(hActualGlobalContactArcEmbedding e).injective he⟩
  let actualContactVertices : Set (Interval × Interval) :=
    actualSkeletonContactNodes ∪ Set.range (fun e : actualNegativeFaceIntervals => actualGlobalContactArcs e 0) ∪
      Set.range (fun e : actualNegativeFaceIntervals => actualGlobalContactArcs e 1)
  have hActualContactVerticesFinite : actualContactVertices.Finite :=
    (hActualSkeletonContactNodesFinite.union (Set.finite_range _)).union (Set.finite_range _)
  have hActualContactArcStartInVertices (e : actualNegativeFaceIntervals) :
      actualGlobalContactArcs e 0∈actualContactVertices :=
    Or.inl (Or.inr ⟨e,rfl⟩)
  have hActualContactArcEndInVertices (e : actualNegativeFaceIntervals) :
      actualGlobalContactArcs e 1∈actualContactVertices := Or.inr ⟨e,rfl⟩
  have hActualContactVerticesImage (v : actualContactVertices) :
      actualFiniteConeSweep v.val∈a.val.image := by
    as_aux_lemma =>
      rcases v.property with (hskel | ⟨e,he⟩) | ⟨e,he⟩
      · obtain ⟨k,z,hz,he⟩ := Set.mem_iUnion.mp hskel
        rw [←he]
        change actualFiniteConeSweep (actualAffineCells k (squareCoordinates ⟨z.val,z.property.le⟩))∈a.val.image
        rw [hActualGlobalConeSweepAffineCell]
        exact hz
      · rw [←he]
        exact hActualGlobalContactArcImage e 0
      · rw [←he]
        exact hActualGlobalContactArcImage e 1
  have hActualContactVerticesMarks (v : actualContactVertices) :
      actualFiniteConeSweep v.val∉(M.cover.branch : Set S) := hActualFiniteConeSweepMarks _
  have hActualFiniteContactVertexAndArcCover (x : Interval × Interval)
      (hx : actualFiniteConeSweep x∈a.val.image) :
      x∈actualContactVertices ∨ ∃ e : actualNegativeFaceIntervals,∃ t : Interval,
        actualGlobalContactArcs e t=x := by
    as_aux_lemma =>
      rcases hActualFiniteConeContactCover x hx with hv | he
      · exact Or.inl (Or.inl (Or.inl hv))
      · exact Or.inr he
  have hActualInitialLeftCellEdgeFormula (j : Fin (actualContactGridSize+1)) (t : Interval) :
      actualCellLeftEdge (0,j) t=actualCentralSweep
        (0,actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) t) := by
    as_aux_lemma =>
      change actualCompatibleGridEdges (0,j.castSucc) (0,j.succ) t=_
      rw [hActualCompatibleGridBoundaryEdgesExact (0,j.castSucc) (0,j.succ) (Or.inl ⟨rfl,Or.inl rfl⟩),
        hActualGridOriginalSegmentsAffine,hActualContactGridZero,hActualIntervalSegmentConstant]
  have hActualInitialLeftCellEdgeInjective (j : Fin (actualContactGridSize+1)) :
      Function.Injective (actualCellLeftEdge (0,j)) := by
    as_aux_lemma =>
      intro t u he
      rw [hActualInitialLeftCellEdgeFormula,hActualInitialLeftCellEdgeFormula] at he
      exact actualIntervalSegmentInjective _ _ (hActualContactGridStep j)
        (hActualCentralSweepInitialEmbedding.injective he)
  have hActualInitialLeftCellEdgeImage (j : Fin (actualContactGridSize+1)) :
      Set.range (actualCellLeftEdge (0,j))⊆b.val.image := by
    as_aux_lemma =>
      rintro x ⟨t,rfl⟩
      rw [hActualInitialLeftCellEdgeFormula,hActualCentralSweepInitial]
      exact ⟨actualCentralParameter (actualIntervalSegment (actualContactGridParameter j.castSucc)
        (actualContactGridParameter j.succ) t),rfl⟩
  have hActualInitialLeftCellEdgeMarkedTransverse (j : Fin (actualContactGridSize+1))
      (t : Interval) (ht : actualCellLeftEdge (0,j) t∈a.val.image) :
      ArcSurgery.CrossesInDisk M a b (actualCellLeftEdge (0,j) t) := by
    as_aux_lemma =>
      have hb : actualCellLeftEdge (0,j) t∈b.val.image := hActualInitialLeftCellEdgeImage j ⟨t,rfl⟩
      have hm : actualCellLeftEdge (0,j) t∉(M.cover.branch : Set S) :=
        hActualCompatibleGridEdgesMarks (0,j.castSucc) (0,j.succ) t
      exact htransverse _ ⟨⟨ht,hm⟩,⟨hb,hm⟩⟩
  have hActualCellBoundaryLoopFormula
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (z : {z : ℝ × ℝ // ‖z‖=1}) :
      (actualContactGridCharts k) (actualConeCells k (squareCoordinates ⟨z.val,z.property.le⟩))=
        (actualCellBoundaryLoops k z).val := by
    as_aux_lemma =>
      obtain ⟨u,hu,hv⟩ := hActualConeCellRadial k 0 z
      have he : u=⟨z.val,z.property.le⟩ := by
        apply Subtype.ext
        simpa using hu
      rw [he] at hv
      simpa using hv
  have hActualBoundaryFaceThreeCoordinates (t : Interval) :
      squareCoordinates ⟨(actualBoundaryFace 3 t).val,(actualBoundaryFace 3 t).property.le⟩=(0,t) := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change ((-1 : ℝ)+1)/2=0
        norm_num
      · change (2*t.val-1+1)/2=t.val
        ring
  have hActualInitialFaceNormalizedHeightFormula (j : Fin (actualContactGridSize+1)) (t : Interval) :
      (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 t)).val.1/(actualCellCenters (0,j)).val.1=
        ((actualContactGridCharts (0,j)) (actualCellLeftEdge (0,j) t)).1/(actualCellCenters (0,j)).val.1 := by
    as_aux_lemma =>
      rw [←hActualCellBoundaryLoopFormula,hActualBoundaryFaceThreeCoordinates,
        (hActualConeCellBoundary (0,j) t).2.2.2]
  have hActualLowerBottomCellEdgeFormula (j : Fin (actualContactGridSize+1)) (t : Interval) :
      actualCellBottomEdge (j,0) t=actualCentralSweep
        (actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) t,0) := by
    as_aux_lemma =>
      change actualCompatibleGridEdges (j.castSucc,0) (j.succ,0) t=_
      rw [hActualCompatibleGridBoundaryEdgesExact (j.castSucc,0) (j.succ,0) (Or.inr ⟨rfl,Or.inl rfl⟩),
        hActualGridOriginalSegmentsAffine,hActualContactGridZero,hActualIntervalSegmentConstant]
  have hActualUpperTopCellEdgeFormula (j : Fin (actualContactGridSize+1)) (t : Interval) :
      actualCellTopEdge (j,Fin.last actualContactGridSize) t=actualCentralSweep
        (actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) t,1) := by
    as_aux_lemma =>
      change actualCompatibleGridEdges (j.castSucc,Fin.last (actualContactGridSize+1))
        (j.succ,Fin.last (actualContactGridSize+1)) t=_
      rw [hActualCompatibleGridBoundaryEdgesExact
        (j.castSucc,Fin.last (actualContactGridSize+1)) (j.succ,Fin.last (actualContactGridSize+1))
        (Or.inr ⟨rfl,Or.inr rfl⟩),hActualGridOriginalSegmentsAffine,hActualContactGridOne,hActualIntervalSegmentConstant]
  have hActualLowerBottomCellEdgeTransverse (j : Fin (actualContactGridSize+1)) :
      (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) (actualCellBottomEdge (j,0)).toContinuousMap := by
    as_aux_lemma =>
      let β : C(Interval,S) := ⟨fun τ => actualCentralSweep (τ,0),by fun_prop⟩
      have he : (actualCellBottomEdge (j,0)).toContinuousMap=
          β.comp (actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ)) := by
        apply ContinuousMap.ext
        intro t
        exact hActualLowerBottomCellEdgeFormula j t
      rw [he]
      exact actualPhysicalTraceTransverseOnIncreasingSegment β hActualCentralLowerTraceTransverse
        _ _ (hActualContactGridStep j)
  have hActualUpperTopCellEdgeTransverse (j : Fin (actualContactGridSize+1)) :
      (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) (actualCellTopEdge (j,Fin.last actualContactGridSize)).toContinuousMap := by
    as_aux_lemma =>
      let β : C(Interval,S) := ⟨fun τ => actualCentralSweep (τ,1),by fun_prop⟩
      have he : (actualCellTopEdge (j,Fin.last actualContactGridSize)).toContinuousMap=
          β.comp (actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ)) := by
        apply ContinuousMap.ext
        intro t
        exact hActualUpperTopCellEdgeFormula j t
      rw [he]
      exact actualPhysicalTraceTransverseOnIncreasingSegment β hActualCentralUpperTraceTransverse
        _ _ (hActualContactGridStep j)
  have hActualBoundaryFaceZeroCoordinates (t : Interval) :
      squareCoordinates ⟨(actualBoundaryFace 0 t).val,(actualBoundaryFace 0 t).property.le⟩=(t,0) := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change (2*t.val-1+1)/2=t.val
        ring
      · change ((-1 : ℝ)+1)/2=0
        norm_num
  have hActualBoundaryFaceTwoCoordinates (t : Interval) :
      squareCoordinates ⟨(actualBoundaryFace 2 t).val,(actualBoundaryFace 2 t).property.le⟩=(t,1) := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change (2*t.val-1+1)/2=t.val
        ring
      · change ((1 : ℝ)+1)/2=1
        norm_num
  have hActualTransverseFaceAdjacentNegativeSigns
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (i : Fin 4) (β : C(Interval,S)) (hβ : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) β)
      (hsource : ∀ t,β t∈(actualContactGridCharts k).source)
      (hformula : ∀ t,(actualCellBoundaryLoops k (actualBoundaryFace i t)).val=
        (actualContactGridCharts k) (β t))
      (hactive : ¬Disjoint (actualContactGridCharts k).source a.val.image)
      (u : Interval) (hroot : (actualCellBoundaryLoops k (actualBoundaryFace i u)).val.1=0)
      (x y sl sr : Interval) (hxu : x<u) (huy : u<y)
      (hsl : sl∈Set.Ioo x u) (hsr : sr∈Set.Ioo u y)
      (hleft : ∀ z,x<z → z<u →
        (actualCellBoundaryLoops k (actualBoundaryFace i z)).val.1/(actualCellCenters k).val.1≠0)
      (hright : ∀ z,u<z → z<y →
        (actualCellBoundaryLoops k (actualBoundaryFace i z)).val.1/(actualCellCenters k).val.1≠0) :
      (actualCellBoundaryLoops k (actualBoundaryFace i sl)).val.1/(actualCellCenters k).val.1<0 ↔
        ¬(actualCellBoundaryLoops k (actualBoundaryFace i sr)).val.1/(actualCellCenters k).val.1<0 := by
    as_aux_lemma =>
      have haxis := (hActualContactGridChartData k).2.2.resolve_left hactive
      have hc := (hActualCellCenterAxisOff k).resolve_left hactive
      have hmem : β u∈a.val.image := (haxis _ (hsource u)).mpr
        ((congrArg Prod.fst (hformula u)).symm.trans hroot)
      let g : C(Interval,ℝ) := ⟨fun t =>
        (actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1/(actualCellCenters k).val.1,by fun_prop⟩
      exact actualPhysicalTransverseAdjacentIntervalsOppositeSigns β hβ u hmem
        (actualContactGridCharts k) (hsource u) haxis g (actualCellCenters k).val.1 hc
        (fun t => congrArg (fun z : ℝ × ℝ => z.1/(actualCellCenters k).val.1) (hformula t))
        x y sl sr hxu huy hsl hsr hleft hright
  have hActualInitialFaceAdjacentNegativeSigns (j : Fin (actualContactGridSize+1))
      (hactive : ¬Disjoint (actualContactGridCharts (0,j)).source a.val.image)
      (u : Interval) (hu : 0<u.val ∧ u.val<1)
      (hroot : (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 u)).val.1=0)
      (x y sl sr : Interval) (hxu : x<u) (huy : u<y)
      (hsl : sl∈Set.Ioo x u) (hsr : sr∈Set.Ioo u y)
      (hleft : ∀ z,x<z → z<u →
        (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 z)).val.1/(actualCellCenters (0,j)).val.1≠0)
      (hright : ∀ z,u<z → z<y →
        (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 z)).val.1/(actualCellCenters (0,j)).val.1≠0) :
      (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 sl)).val.1/(actualCellCenters (0,j)).val.1<0 ↔
        ¬(actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 sr)).val.1/(actualCellCenters (0,j)).val.1<0 := by
    as_aux_lemma =>
      let γ : C(Interval,S) := (actualCellLeftEdge (0,j)).toContinuousMap
      let g : C(Interval,ℝ) :=
        ⟨fun t => (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 t)).val.1/
          (actualCellCenters (0,j)).val.1,by fun_prop⟩
      have hsource : γ u∈(actualContactGridCharts (0,j)).source :=
        hActualCellLeftRange (0,j) ⟨u,rfl⟩
      have haxis := (hActualContactGridChartData (0,j)).2.2.resolve_left hactive
      have hc := (hActualCellCenterAxisOff (0,j)).resolve_left hactive
      have hnormal : ((actualContactGridCharts (0,j)) (γ u)).1=0 := by
        have hh := hActualCellBoundaryLoopFormula (0,j) (actualBoundaryFace 3 u)
        rw [hActualBoundaryFaceThreeCoordinates,(hActualConeCellBoundary (0,j) u).2.2.2] at hh
        exact (congrArg Prod.fst hh).trans hroot
      have hmem := (haxis _ hsource).mpr hnormal
      exact actualMarkedAdjacentIntervalsOppositeSigns u hu γ
        (hActualInitialLeftCellEdgeInjective j).injOn (hActualInitialLeftCellEdgeImage j)
        (hActualInitialLeftCellEdgeMarkedTransverse j u hmem) (actualContactGridCharts (0,j)) hsource haxis
        g (actualCellCenters (0,j)).val.1 hc (hActualInitialFaceNormalizedHeightFormula j)
        x y sl sr hxu huy hsl hsr hleft hright
  have hActualGlobalContactArcInteriorAvoidSkeleton (e : actualNegativeFaceIntervals) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      actualGlobalContactArcs e t∉actualSkeletonContactNodes := by
    as_aux_lemma =>
      intro hv
      obtain ⟨k,z,hz,he⟩ := Set.mem_iUnion.mp hv
      have hpoint : actualGlobalContactArcs e t=
          actualAffineCells k (squareCoordinates ⟨z.val,z.property.le⟩) := he.symm
      obtain ⟨he₀,he₁,he₂,he₃⟩ := hActualGlobalContactArcStrictCell e t ht
      obtain ⟨hk₀,hk₁,hk₂,hk₃⟩ :=
        hActualAffineCellBounds k (squareCoordinates ⟨z.val,z.property.le⟩)
      rw [←hpoint] at hk₀ hk₁ hk₂ hk₃
      have hcell : e.1.1.val=k := Prod.ext
        (hActualGridOpenClosedUnique _ _ _ ⟨he₀,he₁⟩ ⟨hk₀,hk₁⟩)
        (hActualGridOpenClosedUnique _ _ _ ⟨he₂,he₃⟩ ⟨hk₂,hk₃⟩)
      have hp : actualLocalContactArcs e t=squareCoordinates ⟨z.val,z.property.le⟩ := by
        apply (hActualAffineCellEmbedding k).injective
        change actualAffineCells e.1.1.val (actualLocalContactArcs e t)=
          actualAffineCells k (squareCoordinates ⟨z.val,z.property.le⟩) at hpoint
        simpa only [hcell] using hpoint
      obtain ⟨h₁,h₂⟩ := hActualLocalContactArcStrictInterior e t ht
      rw [hp] at h₁ h₂
      have hx₀ : -1<z.val.1 := by
        have h : (0 : ℝ)<(z.val.1+1)/2 := h₁.1
        linarith only [h]
      have hx₁ : z.val.1<1 := by
        have h : (z.val.1+1)/2<(1 : ℝ) := h₁.2
        linarith only [h]
      have hy₀ : -1<z.val.2 := by
        have h : (0 : ℝ)<(z.val.2+1)/2 := h₂.1
        linarith only [h]
      have hy₁ : z.val.2<1 := by
        have h : (z.val.2+1)/2<(1 : ℝ) := h₂.2
        linarith only [h]
      have hn : ‖z.val‖<1 := by
        change max |z.val.1| |z.val.2|<1
        exact max_lt (abs_lt.mpr ⟨hx₀,hx₁⟩) (abs_lt.mpr ⟨hy₀,hy₁⟩)
      exact (ne_of_lt hn) z.property
  have hActualGlobalContactArcInteriorAvoidVertices (e : actualNegativeFaceIntervals) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      actualGlobalContactArcs e t∉actualContactVertices := by
    as_aux_lemma =>
      intro hv
      rcases hv with (hskel | ⟨f,hf⟩) | ⟨f,hf⟩
      · exact hActualGlobalContactArcInteriorAvoidSkeleton e t ht hskel
      · exact hActualGlobalContactArcInteriorAvoidEndpoints e f t 0 ht (Or.inl rfl) hf.symm
      · exact hActualGlobalContactArcInteriorAvoidEndpoints e f t 1 ht (Or.inr rfl) hf.symm
  let actualContactPlaneArc (e : actualNegativeFaceIntervals) : C(Interval,Schoenflies.Plane) :=
    actualParameterSquarePlane.comp (actualGlobalContactArcs e)
  have hActualContactPlaneArcEmbedding (e : actualNegativeFaceIntervals) :
      IsEmbedding (actualContactPlaneArc e) :=
    hActualParameterSquarePlaneEmbedding.comp (hActualGlobalContactArcEmbedding e)
  let actualContactPlaneVertices : Set Schoenflies.Plane :=
    actualParameterSquarePlane '' actualContactVertices
  have hActualContactPlaneVerticesFinite : actualContactPlaneVertices.Finite :=
    hActualContactVerticesFinite.image actualParameterSquarePlane
  have hActualContactPlaneStart (e : actualNegativeFaceIntervals) :
      actualContactPlaneArc e 0∈actualContactPlaneVertices :=
    ⟨actualGlobalContactArcs e 0,hActualContactArcStartInVertices e,rfl⟩
  have hActualContactPlaneEnd (e : actualNegativeFaceIntervals) :
      actualContactPlaneArc e 1∈actualContactPlaneVertices :=
    ⟨actualGlobalContactArcs e 1,hActualContactArcEndInVertices e,rfl⟩
  have hActualContactPlaneArcInteriorAvoidVertices (e : actualNegativeFaceIntervals) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      actualContactPlaneArc e t∉actualContactPlaneVertices := by
    as_aux_lemma =>
      rintro ⟨v,hv,he⟩
      have hpoint : v=actualGlobalContactArcs e t :=
        hActualParameterSquarePlaneInjective he
      exact hActualGlobalContactArcInteriorAvoidVertices e t ht (hpoint ▸ hv)
  have hActualContactPlaneArcCollisionClassification (e f : actualNegativeFaceIntervals)
      (t u : Interval) (he : actualContactPlaneArc e t=actualContactPlaneArc f u) :
      (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) :=
    hActualContactArcCollisionClassification e f t u (hActualParameterSquarePlaneInjective he)
  let actualContactPlanePath (e : actualNegativeFaceIntervals) :
      Path (actualContactPlaneArc e 0) (actualContactPlaneArc e 1) := {
    toFun := actualContactPlaneArc e
    continuous_toFun := (actualContactPlaneArc e).continuous
    source' := rfl
    target' := rfl }
  have hActualContactPlanePathEmbedding (e : actualNegativeFaceIntervals) :
      IsEmbedding (actualContactPlanePath e) := hActualContactPlaneArcEmbedding e
  have hActualContactPlanePathEndpointsDistinct (e : actualNegativeFaceIntervals) :
      actualContactPlanePath e 0≠actualContactPlanePath e 1 := by
    as_aux_lemma =>
      intro he
      have h := (hActualContactPlanePathEmbedding e).injective he
      exact zero_ne_one (congrArg Subtype.val h)
  letI : Fintype actualNegativeFaceIntervals := Fintype.ofFinite _
  letI : Fintype actualContactVertices := hActualContactVerticesFinite.fintype
  let zeroVertex := Sum actualContactVertices (actualNegativeFaceIntervals × Fin 2)
  letI : Fintype zeroVertex := Fintype.ofFinite zeroVertex
  let zeroLeftVertex (e : actualNegativeFaceIntervals) : zeroVertex :=
    Sum.inl ⟨actualGlobalContactArcs e 0,hActualContactArcStartInVertices e⟩
  let zeroRightVertex (e : actualNegativeFaceIntervals) : zeroVertex :=
    Sum.inl ⟨actualGlobalContactArcs e 1,hActualContactArcEndInVertices e⟩
  let zeroDirectedIncidence : zeroVertex → zeroVertex → Prop := fun v w => ∃ e : actualNegativeFaceIntervals,
    (v = zeroLeftVertex e ∧ w = Sum.inr (e,0)) ∨
    (v = Sum.inr (e,0) ∧ w = Sum.inr (e,1)) ∨
    (v = Sum.inr (e,1) ∧ w = zeroRightVertex e)
  let actualZeroGraph : SimpleGraph zeroVertex := SimpleGraph.fromRel zeroDirectedIncidence
  have zeroGraphLeftAdj (e : actualNegativeFaceIntervals) :
      actualZeroGraph.Adj (zeroLeftVertex e) (Sum.inr (e,0)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroGraphMiddleAdj (e : actualNegativeFaceIntervals) :
      actualZeroGraph.Adj (Sum.inr (e,0)) (Sum.inr (e,1)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩⟩
    intro he
    have hh := congrArg Prod.snd (Sum.inr.inj he)
    norm_num at hh
  have zeroGraphRightAdj (e : actualNegativeFaceIntervals) :
      actualZeroGraph.Adj (Sum.inr (e,1)) (zeroRightVertex e) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroSubdivisionNeighborsLeft (e : actualNegativeFaceIntervals) :
      actualZeroGraph.neighborFinset (Sum.inr (e,0)) =
        {zeroLeftVertex e,Sum.inr (e,1)} := by
    as_aux_lemma =>
      ext v
      rcases v with p | ⟨e',j⟩
      · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
      · fin_cases j <;>
          simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
            zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  have zeroSubdivisionNeighborsRight (e : actualNegativeFaceIntervals) :
      actualZeroGraph.neighborFinset (Sum.inr (e,1)) =
        {Sum.inr (e,0),zeroRightVertex e} := by
    as_aux_lemma =>
      ext v
      rcases v with p | ⟨e',j⟩
      · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
      · fin_cases j <;>
          simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
            zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  let leftIncidentEdges (p : actualContactVertices) : Finset actualNegativeFaceIntervals :=
    Finset.univ.filter (fun e => Sum.inl p = zeroLeftVertex e)
  let rightIncidentEdges (p : actualContactVertices) : Finset actualNegativeFaceIntervals :=
    Finset.univ.filter (fun e => Sum.inl p = zeroRightVertex e)
  have zeroEndpointNeighbors (p : actualContactVertices) :
      actualZeroGraph.neighborFinset (Sum.inl p) =
        (leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) ∪
        (rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
    as_aux_lemma =>
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
  have zeroEndpointDegreeExact (p : actualContactVertices) :
      actualZeroGraph.degree (Sum.inl p) =
        (leftIncidentEdges p).card + (rightIncidentEdges p).card := by
    as_aux_lemma =>
      change (actualZeroGraph.neighborFinset (Sum.inl p)).card = _
      rw [zeroEndpointNeighbors]
      have hd : Disjoint
          ((leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)))
          ((rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex))) := by
        apply Finset.disjoint_left.mpr
        intro v hv hw
        obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨f,hf,h⟩ := Finset.mem_image.mp hw
        have hh := congrArg (fun v : actualNegativeFaceIntervals × Fin 2 => v.2) (Sum.inr.inj h)
        norm_num at hh
      rw [Finset.card_union_of_disjoint hd]
      have hi0 : Function.Injective (fun e : actualNegativeFaceIntervals => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) := by
        intro e f h
        exact congrArg Prod.fst (Sum.inr.inj h)
      have hi1 : Function.Injective (fun e : actualNegativeFaceIntervals => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
        intro e f h
        exact congrArg Prod.fst (Sum.inr.inj h)
      rw [Finset.card_image_of_injective _ hi0,Finset.card_image_of_injective _ hi1]
  have zeroSubdivisionDegrees (e : actualNegativeFaceIntervals) :
      actualZeroGraph.degree (Sum.inr (e,0)) = 2 ∧
      actualZeroGraph.degree (Sum.inr (e,1)) = 2 := by
    as_aux_lemma =>
      change (actualZeroGraph.neighborFinset (Sum.inr (e,0))).card = 2 ∧
        (actualZeroGraph.neighborFinset (Sum.inr (e,1))).card = 2
      rw [zeroSubdivisionNeighborsLeft,zeroSubdivisionNeighborsRight]
      simp [zeroLeftVertex,zeroRightVertex]
  let privateParameter : Fin 2 → Interval := fun j =>
    if j=0 then ⟨1/3,by norm_num⟩ else ⟨2/3,by norm_num⟩
  have privateParameterInterior (j : Fin 2) :
      privateParameter j∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      change 0<(privateParameter j).val ∧ (privateParameter j).val<1
      fin_cases j <;> norm_num [privateParameter]
  have privateParameterInjective : Function.Injective privateParameter := by
    as_aux_lemma =>
      intro j k he
      have hh := congrArg Subtype.val he
      fin_cases j <;> fin_cases k <;> first | rfl | (norm_num [privateParameter] at hh)
  let zeroVertexPosition : zeroVertex → Interval × Interval := fun v =>
    match v with
    | Sum.inl p => p.val
    | Sum.inr (e,j) => actualGlobalContactArcs e (privateParameter j)
  have zeroVertexPositionInjective : Function.Injective zeroVertexPosition := by
    as_aux_lemma =>
      intro v w he
      rcases v with p | ⟨e,j⟩ <;> rcases w with q | ⟨f,k⟩
      · exact congrArg Sum.inl (Subtype.ext he)
      · change p.val=actualGlobalContactArcs f (privateParameter k) at he
        have hh : actualGlobalContactArcs f (privateParameter k)∈actualContactVertices :=
          he ▸ p.property
        exact False.elim (hActualGlobalContactArcInteriorAvoidVertices f _ (privateParameterInterior k) hh)
      · change actualGlobalContactArcs e (privateParameter j)=q.val at he
        have hh : actualGlobalContactArcs e (privateParameter j)∈actualContactVertices :=
          he.symm ▸ q.property
        exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e _ (privateParameterInterior j) hh)
      · have hef : e=f := hActualGlobalContactArcInteriorsDisjoint e f _ _
          (privateParameterInterior j) (privateParameterInterior k) he
        subst f
        have hjk := privateParameterInjective ((hActualGlobalContactArcEmbedding e).injective he)
        subst k
        rfl
  let actualPlanarVertexPosition (v : zeroVertex) : Schoenflies.Plane :=
    actualParameterSquarePlane (zeroVertexPosition v)
  have actualPlanarVertexPositionInjective : Function.Injective actualPlanarVertexPosition :=
    hActualParameterSquarePlaneInjective.comp zeroVertexPositionInjective
  have hActualContactGraphVertexImage (v : zeroVertex) :
      actualFiniteConeSweep (zeroVertexPosition v)∈a.val.image := by
    as_aux_lemma =>
      rcases v with p | ⟨e,j⟩
      · exact hActualContactVerticesImage p
      · exact hActualGlobalContactArcImage e _
  have hActualContactGraphVertexMarks (v : zeroVertex) :
      actualFiniteConeSweep (zeroVertexPosition v)∉(M.cover.branch : Set S) :=
    hActualFiniteConeSweepMarks _
  have actualPrivateParametersOrdered :
      (0 : Interval)<privateParameter 0 ∧ privateParameter 0<privateParameter 1 ∧
        privateParameter 1<(1 : Interval) := by
    as_aux_lemma =>
      change 0<(privateParameter 0).val ∧ (privateParameter 0).val<(privateParameter 1).val ∧
        (privateParameter 1).val<1
      norm_num [privateParameter]
  let actualSegmentStartParameter (q : actualNegativeFaceIntervals × Fin 3) : Interval :=
    if q.2=0 then 0 else if q.2=1 then privateParameter 0 else privateParameter 1
  let actualSegmentEndParameter (q : actualNegativeFaceIntervals × Fin 3) : Interval :=
    if q.2=0 then privateParameter 0 else if q.2=1 then privateParameter 1 else 1
  let actualSegmentStartVertex (q : actualNegativeFaceIntervals × Fin 3) : zeroVertex :=
    if q.2=0 then zeroLeftVertex q.1 else if q.2=1 then Sum.inr (q.1,0) else Sum.inr (q.1,1)
  let actualSegmentEndVertex (q : actualNegativeFaceIntervals × Fin 3) : zeroVertex :=
    if q.2=0 then Sum.inr (q.1,0) else if q.2=1 then Sum.inr (q.1,1) else zeroRightVertex q.1
  have actualSegmentParameterOrder (q : actualNegativeFaceIntervals × Fin 3) :
      actualSegmentStartParameter q<actualSegmentEndParameter q := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j
      · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.1
      · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.1
      · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.2
  let actualSegmentSquarePath (q : actualNegativeFaceIntervals × Fin 3) :
      Path (actualGlobalContactArcs q.1 (actualSegmentStartParameter q))
        (actualGlobalContactArcs q.1 (actualSegmentEndParameter q)) := {
    toFun := fun t => actualGlobalContactArcs q.1
      (actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q) t)
    continuous_toFun := (actualGlobalContactArcs q.1).continuous.comp
      (actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q)).continuous
    source' := by
      apply congrArg (actualGlobalContactArcs q.1)
      apply Subtype.ext
      change (1-(0 : ℝ))*(actualSegmentStartParameter q).val+0*(actualSegmentEndParameter q).val=
        (actualSegmentStartParameter q).val
      ring
    target' := by
      apply congrArg (actualGlobalContactArcs q.1)
      apply Subtype.ext
      change (1-(1 : ℝ))*(actualSegmentStartParameter q).val+1*(actualSegmentEndParameter q).val=
        (actualSegmentEndParameter q).val
      ring }
  have actualSegmentSquarePathEmbedding (q : actualNegativeFaceIntervals × Fin 3) :
      IsEmbedding (actualSegmentSquarePath q) :=
    (hActualGlobalContactArcEmbedding q.1).comp
      (((actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q)).continuous.isClosedEmbedding (actualIntervalSegmentInjective _ _ (actualSegmentParameterOrder q))).isEmbedding)
  have actualSegmentSquarePathRange (q : actualNegativeFaceIntervals × Fin 3) :
      Set.range (actualSegmentSquarePath q)⊆actualGlobalContactArcs q.1 ''
        Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q) := by
    as_aux_lemma =>
      rintro z ⟨t,rfl⟩
      refine ⟨actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q) t,?_,rfl⟩
      exact actualIntervalSegmentBounds _ _ (actualSegmentParameterOrder q) t
  have actualSegmentStartPosition (q : actualNegativeFaceIntervals × Fin 3) :
      zeroVertexPosition (actualSegmentStartVertex q)=
        actualGlobalContactArcs q.1 (actualSegmentStartParameter q) := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> simp [actualSegmentStartVertex,actualSegmentStartParameter,
        zeroVertexPosition,zeroLeftVertex] <;> rfl
  have actualSegmentEndPosition (q : actualNegativeFaceIntervals × Fin 3) :
      zeroVertexPosition (actualSegmentEndVertex q)=
        actualGlobalContactArcs q.1 (actualSegmentEndParameter q) := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> simp [actualSegmentEndVertex,actualSegmentEndParameter,
        zeroVertexPosition,zeroRightVertex] <;> rfl
  let actualSegmentPlanarPath (q : actualNegativeFaceIntervals × Fin 3) :
      Path (actualParameterSquarePlane (actualGlobalContactArcs q.1 (actualSegmentStartParameter q)))
        (actualParameterSquarePlane (actualGlobalContactArcs q.1 (actualSegmentEndParameter q))) :=
    (actualSegmentSquarePath q).map actualParameterSquarePlane.continuous
  have actualSegmentPlanarPathEmbedding (q : actualNegativeFaceIntervals × Fin 3) :
      IsEmbedding (actualSegmentPlanarPath q) :=
    hActualParameterSquarePlaneEmbedding.comp (actualSegmentSquarePathEmbedding q)
  have actualSegmentPlanarSource (q : actualNegativeFaceIntervals × Fin 3) :
      actualSegmentPlanarPath q 0=actualPlanarVertexPosition (actualSegmentStartVertex q) := by
    as_aux_lemma =>
      rw [Path.source]
      exact congrArg actualParameterSquarePlane (actualSegmentStartPosition q).symm
  have actualSegmentPlanarTarget (q : actualNegativeFaceIntervals × Fin 3) :
      actualSegmentPlanarPath q 1=actualPlanarVertexPosition (actualSegmentEndVertex q) := by
    as_aux_lemma =>
      rw [Path.target]
      exact congrArg actualParameterSquarePlane (actualSegmentEndPosition q).symm
  let actualPlanarGraph : Graph Schoenflies.Plane (actualNegativeFaceIntervals × Fin 3) := {
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
  let actualPlanarDrawing (q : actualNegativeFaceIntervals × Fin 3) : ℝ → Schoenflies.Plane :=
    (actualSegmentPlanarPath q).extend
  have actualPlanarEdgeParameter (q : actualNegativeFaceIntervals × Fin 3) :
      ContinuousOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      actualPlanarGraph.IsLink q (actualPlanarDrawing q 0) (actualPlanarDrawing q 1) := by
    as_aux_lemma =>
      refine ⟨(actualSegmentPlanarPath q).continuous_extend.continuousOn,?_,?_⟩
      · intro s hs t ht he
        change (actualSegmentPlanarPath q).extend s = (actualSegmentPlanarPath q).extend t at he
        rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
        exact congrArg Subtype.val ((actualSegmentPlanarPathEmbedding q).injective he)
      · change (actualPlanarDrawing q 0 = actualSegmentPlanarPath q 0 ∧
          actualPlanarDrawing q 1 = actualSegmentPlanarPath q 1) ∨ _
        exact Or.inl ⟨by simp [actualPlanarDrawing],by simp [actualPlanarDrawing]⟩
  have actualZeroVertexOnEdgeBreakpoint (v : zeroVertex) (e : actualNegativeFaceIntervals)
      (t : Interval) (he : zeroVertexPosition v=actualGlobalContactArcs e t) :
      t=0 ∨ t=privateParameter 0 ∨ t=privateParameter 1 ∨ t=1 := by
    as_aux_lemma =>
      rcases v with p | ⟨f,j⟩
      · by_cases ht0 : t=0
        · exact Or.inl ht0
        by_cases ht1 : t=1
        · exact Or.inr (Or.inr (Or.inr ht1))
        have ht : t∈Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
        change p.val=actualGlobalContactArcs e t at he
        exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e t ht (he ▸ p.property))
      · change actualGlobalContactArcs f (privateParameter j)=actualGlobalContactArcs e t at he
        rcases hActualContactArcCollisionClassification f e _ t he with ⟨hfe,ht⟩ | ⟨hf,ht⟩
        · fin_cases j
          · exact Or.inr (Or.inl ht.symm)
          · exact Or.inr (Or.inr (Or.inl ht.symm))
        · rcases hf with hf | hf
          · exact False.elim ((ne_of_gt (privateParameterInterior j).1) hf)
          · exact False.elim ((ne_of_lt (privateParameterInterior j).2) hf)
  have actualSegmentStartValue (q : actualNegativeFaceIntervals × Fin 3) :
      (actualSegmentStartParameter q).val=CurveComplex.LocalSurgery.actualThreeSegmentStart q.2 := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> norm_num [actualSegmentStartParameter,privateParameter,
        CurveComplex.LocalSurgery.actualThreeSegmentStart]
  have actualSegmentEndValue (q : actualNegativeFaceIntervals × Fin 3) :
      (actualSegmentEndParameter q).val=CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2 := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> norm_num [actualSegmentEndParameter,privateParameter,
        CurveComplex.LocalSurgery.actualThreeSegmentEnd]
  have actualSegmentBreakpointIsEndpoint (q : actualNegativeFaceIntervals × Fin 3) (u : Interval)
      (hu : u∈Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hb : u=0 ∨ u=privateParameter 0 ∨ u=privateParameter 1 ∨ u=1) :
      u=actualSegmentStartParameter q ∨ u=actualSegmentEndParameter q := by
    as_aux_lemma =>
      have hreal : u.val∈Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart q.2)
          (CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2) := by
        rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
        exact hu
      have hbReal : u.val=0 ∨ u.val=1/3 ∨ u.val=2/3 ∨ u.val=1 := by
        rcases hb with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by norm_num [privateParameter]))
        · exact Or.inr (Or.inr (Or.inl (by norm_num [privateParameter])))
        · exact Or.inr (Or.inr (Or.inr rfl))
      rcases CurveComplex.LocalSurgery.actualThreeSegment_breakpoint_is_endpoint q.2 u.val hreal hbReal with h | h
      · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
      · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
  have actualDistinctSegmentParameterIntersection (q r : actualNegativeFaceIntervals × Fin 3)
      (hj : q.2 ≠ r.2) (u : Interval)
      (hu : u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hv : u ∈ Set.Icc (actualSegmentStartParameter r) (actualSegmentEndParameter r)) :
      (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
        (u = actualSegmentStartParameter r ∨ u = actualSegmentEndParameter r) := by
    as_aux_lemma =>
      have huReal : u.val ∈ Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart q.2) (CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2) := by
        rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
        exact hu
      have hvReal : u.val ∈ Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart r.2) (CurveComplex.LocalSurgery.actualThreeSegmentEnd r.2) := by
        rw [←actualSegmentStartValue r,←actualSegmentEndValue r]
        exact hv
      obtain ⟨hq,hr⟩ := CurveComplex.LocalSurgery.actualThreeSegment_distinct_intersection q.2 r.2 hj u.val huReal hvReal
      constructor
      · rcases hq with h | h
        · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
        · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
      · rcases hr with h | h
        · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue r).symm))
        · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue r).symm))
  have actualPlanarEdgeArcParameter (q : actualNegativeFaceIntervals × Fin 3) (z : Schoenflies.Plane)
      (hz : z ∈ Graph.edgeArc actualPlanarDrawing q) :
      ∃ u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q),
        actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = z := by
    as_aux_lemma =>
      obtain ⟨s,hs,he⟩ := hz
      change (actualSegmentPlanarPath q).extend s = z at he
      rw [Path.extend_apply _ hs] at he
      obtain ⟨u,hu,hup⟩ := actualSegmentSquarePathRange q ⟨⟨s,hs⟩,rfl⟩
      exact ⟨u,hu,(congrArg actualParameterSquarePlane hup).trans he⟩
  have actualSegmentEndpointPlanarPosition (q : actualNegativeFaceIntervals × Fin 3) (u : Interval)
      (hu : u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) :
      actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = actualSegmentPlanarPath q 0 ∨
        actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = actualSegmentPlanarPath q 1 := by
    as_aux_lemma =>
      rcases hu with rfl | rfl
      · exact Or.inl (Path.source _).symm
      · exact Or.inr (Path.target _).symm
  have actualSegmentVertexOnArcIsEndpoint (q : actualNegativeFaceIntervals × Fin 3) (v : zeroVertex)
      (hv : actualPlanarVertexPosition v ∈ Graph.edgeArc actualPlanarDrawing q) :
      actualPlanarVertexPosition v = actualSegmentPlanarPath q 0 ∨
        actualPlanarVertexPosition v = actualSegmentPlanarPath q 1 := by
    as_aux_lemma =>
      obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter q _ hv
      have hpoint : zeroVertexPosition v = actualGlobalContactArcs q.1 u :=
        (hActualParameterSquarePlaneInjective he).symm
      have hb := actualZeroVertexOnEdgeBreakpoint v q.1 u hpoint
      have hend := actualSegmentBreakpointIsEndpoint q u hu hb
      rw [←he]
      exact actualSegmentEndpointPlanarPosition q u hend
  have actualDistinctSegmentArcIntersection (q r : actualNegativeFaceIntervals × Fin 3)
      (hqr : q ≠ r) (z : Schoenflies.Plane)
      (hq : z ∈ Graph.edgeArc actualPlanarDrawing q)
      (hr : z ∈ Graph.edgeArc actualPlanarDrawing r) :
      (z = actualSegmentPlanarPath q 0 ∨ z = actualSegmentPlanarPath q 1) ∧
        (z = actualSegmentPlanarPath r 0 ∨ z = actualSegmentPlanarPath r 1) := by
    as_aux_lemma =>
      obtain ⟨u,hu,hup⟩ := actualPlanarEdgeArcParameter q z hq
      obtain ⟨v,hv,hvp⟩ := actualPlanarEdgeArcParameter r z hr
      have he : actualGlobalContactArcs q.1 u = actualGlobalContactArcs r.1 v :=
        hActualParameterSquarePlaneInjective (hup.trans hvp.symm)
      have hends : (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
          (v = actualSegmentStartParameter r ∨ v = actualSegmentEndParameter r) := by
        rcases hActualContactArcCollisionClassification q.1 r.1 u v he with ⟨hedge,huv⟩ | ⟨hu0,hv0⟩
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
    as_aux_lemma =>
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
  have hActualInitialAffineCellPlacement (j : Fin (actualContactGridSize+1)) (u : Interval) :
      actualAffineCells (0,j) (0,u)=(0,actualIntervalSegment (actualContactGridParameter j.castSucc)
        (actualContactGridParameter j.succ) u) := by
    as_aux_lemma =>
      rw [hActualAffineCellFormula]
      apply Prod.ext
      · apply Subtype.ext
        change (1-(0 : ℝ))*(actualContactGridParameter (0 : Fin (actualContactGridSize+1)).castSucc).val+
          0*(actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ).val=0
        have hz : (actualContactGridParameter (0 : Fin (actualContactGridSize+2))).val=0 :=
          congrArg Subtype.val hActualContactGridZero
        simpa using hz
      · rfl
  have hActualTransverseFaceContactHasActualArcEndpoint
      (k : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1))
      (i : Fin 4) (β : C(Interval,S)) (hβ : (CurveComplex.LocalSurgery.actualPhysicalTraceTransverse a.val.image) β)
      (hsource : ∀ t,β t∈(actualContactGridCharts k).source)
      (hformula : ∀ t,(actualCellBoundaryLoops k (actualBoundaryFace i t)).val=
        (actualContactGridCharts k) (β t))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1) (hmem : β u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,e.1.1.val=k ∧ e.1.2=i ∧
        (actualGlobalContactArcs e 0=actualAffineCells k
          (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) ∨
          actualGlobalContactArcs e 1=actualAffineCells k
          (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩)) ∧
        ∀ f : actualNegativeFaceIntervals,f.1.1.val=k → f.1.2=i →
          (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
            actualFaceContactMesh f.1 f.2.val.succ=u) → f=e := by
    as_aux_lemma =>
      have hactive : ¬Disjoint (actualContactGridCharts k).source a.val.image := by
        intro hd
        exact Set.disjoint_left.mp hd (hsource u) hmem
      let ka : actualActiveContactCells := ⟨k,hactive⟩
      let P : actualActiveContactCells × Fin 4 := (ka,i)
      let g : C(Interval,ℝ) := ⟨fun t => (actualCellBoundaryLoops k (actualBoundaryFace i t)).val.1,
        by fun_prop⟩
      have hc := (hActualCellCenterAxisOff k).resolve_left hactive
      have hroot : g u=0 := by
        have hn := ((hActualContactGridChartData k).2.2.resolve_left hactive _ (hsource u)).mp hmem
        exact (congrArg Prod.fst (hformula u)).trans hn
      obtain ⟨l,r,hlu,hru,hxu,huy⟩ := actualInteriorZeroMeshNeighbors g (actualFaceContactSize P)
        (actualFaceContactMesh P) (actualFaceContactMono P) (actualFaceContactStart P)
        (actualFaceContactEnd P) (actualFaceContactNoZero P) u hu hroot
      let x := actualFaceContactMesh P l.castSucc
      let y := actualFaceContactMesh P r.succ
      have hsl : actualIntervalMidpoint x u∈Set.Ioo x u := by
        change x.val<(x.val+u.val)/2 ∧ (x.val+u.val)/2<u.val
        have h : x.val<u.val := hxu
        constructor <;> linarith only [h]
      have hsr : actualIntervalMidpoint u y∈Set.Ioo u y := by
        change u.val<(u.val+y.val)/2 ∧ (u.val+y.val)/2<y.val
        have h : u.val<y.val := huy
        constructor <;> linarith only [h]
      have hleft : ∀ z,x<z → z<u → g z/(actualCellCenters k).val.1≠0 := by
        intro z hx hz
        exact div_ne_zero (actualFaceContactNoZero P l z hx (hlu.symm ▸ hz)) hc
      have hright : ∀ z,u<z → z<y → g z/(actualCellCenters k).val.1≠0 := by
        intro z hz hy
        exact div_ne_zero (actualFaceContactNoZero P r z (hru.symm ▸ hz) hy) hc
      have hflip := hActualTransverseFaceAdjacentNegativeSigns k i β hβ hsource hformula hactive u hroot
        x y (actualIntervalMidpoint x u) (actualIntervalMidpoint u y) hxu huy hsl hsr hleft hright
      let negative : Fin (actualFaceContactSize P+1) → Prop := fun z =>
        (actualCellBoundaryLoops k (actualBoundaryFace i
          (actualIntervalMidpoint (actualFaceContactMesh P z.castSucc)
            (actualFaceContactMesh P z.succ)))).val.1/(actualCellCenters k).val.1<0
      have hnegativeflip : negative l ↔ ¬negative r := by
        simpa only [negative,hlu,hru] using hflip
      obtain ⟨w,hw,hunique⟩ := actualMeshNegativeIncidenceUnique (actualFaceContactSize P)
        (actualFaceContactMesh P) (actualFaceContactMono P) negative l r u hlu hru hnegativeflip
      by_cases hl : g (actualIntervalMidpoint x u)/(actualCellCenters k).val.1<0
      · let e : actualNegativeFaceIntervals := ⟨P,⟨l,by
          change g (actualIntervalMidpoint x (actualFaceContactMesh P l.succ))/(actualCellCenters k).val.1<0
          rw [hlu]
          exact hl⟩⟩
        refine ⟨e,rfl,rfl,?_,?_⟩
        · right
          change actualAffineCells k (actualLocalContactArcs e 1)=actualAffineCells k (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩)
          apply congrArg (actualAffineCells k)
          rw [hActualLocalContactArcEnd]
          have hz : (actualLocalContactArcEnd e).val=actualBoundaryFace i u :=
            (hActualLocalContactArcEndFace e).trans (congrArg (actualBoundaryFace i) hlu)
          rw [actualFaceContactBoundaryFix P _ (by
            change (actualCellBoundaryLoops k _).val.1=0
            rw [hz]
            exact hroot)]
          exact (congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} =>
            squareCoordinates ⟨z.val,z.property.le⟩) hz)
        · intro f hfcell hfface hfmesh
          have hfP : f.1=P := Prod.ext (Subtype.ext hfcell) hfface
          rcases f with ⟨Q,z⟩
          change Q=P at hfP
          subst Q
          have hz : z.val=w := hunique z.val ⟨z.property,hfmesh⟩
          have he : l=w := hunique l ⟨e.2.property,Or.inr hlu⟩
          exact congrArg (fun z : {z : Fin (actualFaceContactSize P+1) | negative z} =>
            (⟨P,z⟩ : actualNegativeFaceIntervals)) (Subtype.ext (hz.trans he.symm))
      · have hr : g (actualIntervalMidpoint u y)/(actualCellCenters k).val.1<0 := by
          by_contra hn
          exact hl (hflip.mpr hn)
        let e : actualNegativeFaceIntervals := ⟨P,⟨r,by
          change g (actualIntervalMidpoint (actualFaceContactMesh P r.castSucc) y)/(actualCellCenters k).val.1<0
          rw [hru]
          exact hr⟩⟩
        refine ⟨e,rfl,rfl,?_,?_⟩
        · left
          change actualAffineCells k (actualLocalContactArcs e 0)=actualAffineCells k (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩)
          apply congrArg (actualAffineCells k)
          rw [hActualLocalContactArcStart]
          have hz : (actualLocalContactArcStart e).val=actualBoundaryFace i u :=
            (hActualLocalContactArcStartFace e).trans (congrArg (actualBoundaryFace i) hru)
          rw [actualFaceContactBoundaryFix P _ (by
            change (actualCellBoundaryLoops k _).val.1=0
            rw [hz]
            exact hroot)]
          exact (congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} =>
            squareCoordinates ⟨z.val,z.property.le⟩) hz)
        · intro f hfcell hfface hfmesh
          have hfP : f.1=P := Prod.ext (Subtype.ext hfcell) hfface
          rcases f with ⟨Q,z⟩
          change Q=P at hfP
          subst Q
          have hz : z.val=w := hunique z.val ⟨z.property,hfmesh⟩
          have he : r=w := hunique r ⟨e.2.property,Or.inl hru⟩
          exact congrArg (fun z : {z : Fin (actualFaceContactSize P+1) | negative z} =>
            (⟨P,z⟩ : actualNegativeFaceIntervals)) (Subtype.ext (hz.trans he.symm))
  have hActualInitialFaceContactHasActualArcEndpoint (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellLeftEdge (0,j) u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,e.1.1.val=(0,j) ∧ e.1.2=3 ∧
        (actualGlobalContactArcs e 0=actualAffineCells (0,j) (0,u) ∨
          actualGlobalContactArcs e 1=actualAffineCells (0,j) (0,u)) ∧
        ∀ f : actualNegativeFaceIntervals,f.1.1.val=(0,j) → f.1.2=3 →
          (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
            actualFaceContactMesh f.1 f.2.val.succ=u) → f=e := by
    as_aux_lemma =>
      have hactive : ¬Disjoint (actualContactGridCharts (0,j)).source a.val.image := by
        intro hd
        exact Set.disjoint_left.mp hd (hActualCellLeftRange (0,j) ⟨u,rfl⟩) hmem
      let k : actualActiveContactCells := ⟨(0,j),hactive⟩
      let P : actualActiveContactCells × Fin 4 := (k,3)
      let g : C(Interval,ℝ) := ⟨fun t => (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3 t)).val.1,
        by fun_prop⟩
      have hc := (hActualCellCenterAxisOff (0,j)).resolve_left hactive
      have hroot : g u=0 := by
        have hn := ((hActualContactGridChartData (0,j)).2.2.resolve_left hactive _
          (hActualCellLeftRange (0,j) ⟨u,rfl⟩)).mp hmem
        have hh := hActualCellBoundaryLoopFormula (0,j) (actualBoundaryFace 3 u)
        rw [hActualBoundaryFaceThreeCoordinates,(hActualConeCellBoundary (0,j) u).2.2.2] at hh
        exact (congrArg Prod.fst hh).symm.trans hn
      obtain ⟨l,r,hlu,hru,hxu,huy⟩ := actualInteriorZeroMeshNeighbors g (actualFaceContactSize P)
        (actualFaceContactMesh P) (actualFaceContactMono P) (actualFaceContactStart P)
        (actualFaceContactEnd P) (actualFaceContactNoZero P) u hu hroot
      let x := actualFaceContactMesh P l.castSucc
      let y := actualFaceContactMesh P r.succ
      have hsl : actualIntervalMidpoint x u∈Set.Ioo x u := by
        change x.val<(x.val+u.val)/2 ∧ (x.val+u.val)/2<u.val
        have h : x.val<u.val := hxu
        constructor <;> linarith only [h]
      have hsr : actualIntervalMidpoint u y∈Set.Ioo u y := by
        change u.val<(u.val+y.val)/2 ∧ (u.val+y.val)/2<y.val
        have h : u.val<y.val := huy
        constructor <;> linarith only [h]
      have hleft : ∀ z,x<z → z<u → g z/(actualCellCenters (0,j)).val.1≠0 := by
        intro z hx hz
        exact div_ne_zero (actualFaceContactNoZero P l z hx (hlu.symm ▸ hz)) hc
      have hright : ∀ z,u<z → z<y → g z/(actualCellCenters (0,j)).val.1≠0 := by
        intro z hz hy
        exact div_ne_zero (actualFaceContactNoZero P r z (hru.symm ▸ hz) hy) hc
      have hflip := hActualInitialFaceAdjacentNegativeSigns j hactive u ⟨hu.1,hu.2⟩ hroot
        x y (actualIntervalMidpoint x u) (actualIntervalMidpoint u y) hxu huy hsl hsr hleft hright
      let negative : Fin (actualFaceContactSize P+1) → Prop := fun z =>
        (actualCellBoundaryLoops (0,j) (actualBoundaryFace 3
          (actualIntervalMidpoint (actualFaceContactMesh P z.castSucc)
            (actualFaceContactMesh P z.succ)))).val.1/(actualCellCenters (0,j)).val.1<0
      have hnegativeflip : negative l ↔ ¬negative r := by
        simpa only [negative,hlu,hru] using hflip
      obtain ⟨w,hw,hunique⟩ := actualMeshNegativeIncidenceUnique (actualFaceContactSize P)
        (actualFaceContactMesh P) (actualFaceContactMono P) negative l r u hlu hru hnegativeflip
      by_cases hl : g (actualIntervalMidpoint x u)/(actualCellCenters (0,j)).val.1<0
      · let e : actualNegativeFaceIntervals := ⟨P,⟨l,by
          change g (actualIntervalMidpoint x (actualFaceContactMesh P l.succ))/(actualCellCenters (0,j)).val.1<0
          rw [hlu]
          exact hl⟩⟩
        refine ⟨e,rfl,rfl,?_,?_⟩
        · right
          change actualAffineCells (0,j) (actualLocalContactArcs e 1)=actualAffineCells (0,j) (0,u)
          apply congrArg (actualAffineCells (0,j))
          rw [hActualLocalContactArcEnd]
          have hz : (actualLocalContactArcEnd e).val=actualBoundaryFace 3 u :=
            (hActualLocalContactArcEndFace e).trans (congrArg (actualBoundaryFace 3) hlu)
          rw [actualFaceContactBoundaryFix P _ (by
            change (actualCellBoundaryLoops (0,j) _).val.1=0
            rw [hz]
            exact hroot)]
          exact (congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} =>
            squareCoordinates ⟨z.val,z.property.le⟩) hz).trans (hActualBoundaryFaceThreeCoordinates u)
        · intro f hfcell hfface hfmesh
          have hfP : f.1=P := Prod.ext (Subtype.ext hfcell) hfface
          rcases f with ⟨Q,z⟩
          change Q=P at hfP
          subst Q
          have hz : z.val=w := hunique z.val ⟨z.property,hfmesh⟩
          have he : l=w := hunique l ⟨e.2.property,Or.inr hlu⟩
          exact congrArg (fun z : {z : Fin (actualFaceContactSize P+1) | negative z} =>
            (⟨P,z⟩ : actualNegativeFaceIntervals)) (Subtype.ext (hz.trans he.symm))
      · have hr : g (actualIntervalMidpoint u y)/(actualCellCenters (0,j)).val.1<0 := by
          by_contra hn
          exact hl (hflip.mpr hn)
        let e : actualNegativeFaceIntervals := ⟨P,⟨r,by
          change g (actualIntervalMidpoint (actualFaceContactMesh P r.castSucc) y)/(actualCellCenters (0,j)).val.1<0
          rw [hru]
          exact hr⟩⟩
        refine ⟨e,rfl,rfl,?_,?_⟩
        · left
          change actualAffineCells (0,j) (actualLocalContactArcs e 0)=actualAffineCells (0,j) (0,u)
          apply congrArg (actualAffineCells (0,j))
          rw [hActualLocalContactArcStart]
          have hz : (actualLocalContactArcStart e).val=actualBoundaryFace 3 u :=
            (hActualLocalContactArcStartFace e).trans (congrArg (actualBoundaryFace 3) hru)
          rw [actualFaceContactBoundaryFix P _ (by
            change (actualCellBoundaryLoops (0,j) _).val.1=0
            rw [hz]
            exact hroot)]
          exact (congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} =>
            squareCoordinates ⟨z.val,z.property.le⟩) hz).trans (hActualBoundaryFaceThreeCoordinates u)
        · intro f hfcell hfface hfmesh
          have hfP : f.1=P := Prod.ext (Subtype.ext hfcell) hfface
          rcases f with ⟨Q,z⟩
          change Q=P at hfP
          subst Q
          have hz : z.val=w := hunique z.val ⟨z.property,hfmesh⟩
          have he : r=w := hunique r ⟨e.2.property,Or.inl hru⟩
          exact congrArg (fun z : {z : Fin (actualFaceContactSize P+1) | negative z} =>
            (⟨P,z⟩ : actualNegativeFaceIntervals)) (Subtype.ext (hz.trans he.symm))
  have hActualEveryOriginalCrossingHasContactGraphEndpoint (t : Interval)
      (ht : b.val.map t∈ArcSurgery.crossings M a b) :
      ∃ v : Interval,actualFiniteConeSweep (0,v)=b.val.map t ∧
        ∃ e : actualNegativeFaceIntervals,actualGlobalContactArcs e 0=(0,v) ∨
          actualGlobalContactArcs e 1=(0,v) := by
    as_aux_lemma =>
      obtain ⟨v,j,hv,hj₀,hj₁⟩ := hActualOriginalCrossingInsideContactGrid t ht
      let u := actualContactGridLocalCoordinate j v
      have hlocal : actualIntervalSegment (actualContactGridParameter j.castSucc)
          (actualContactGridParameter j.succ) u=v :=
        hActualGridCoordinateReconstruct j v hj₀.le hj₁.le
      have hu : u∈Set.Ioo (0 : Interval) 1 :=
        actualIntervalSegmentInteriorReflect _ _ u (hlocal.symm ▸ hj₀) (hlocal.symm ▸ hj₁)
      have hleft : actualCellLeftEdge (0,j) u=actualCentralSweep (0,v) := by
        rw [hActualInitialLeftCellEdgeFormula,hlocal]
      have hmem : actualCellLeftEdge (0,j) u∈a.val.image := by
        rw [hleft,hv]
        exact ht.1.1
      obtain ⟨e,hecell,heface,he,hunique⟩ := hActualInitialFaceContactHasActualArcEndpoint j u hu hmem
      have hparam : actualAffineCells (0,j) (0,u)=(0,v) := by
        rw [hActualAffineCellFormula,hlocal]
        apply Prod.ext
        · apply Subtype.ext
          change (1-(0 : ℝ))*(actualContactGridParameter (0 : Fin (actualContactGridSize+1)).castSucc).val+
            0*(actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ).val=0
          have hz : (actualContactGridParameter (0 : Fin (actualContactGridSize+2))).val=0 :=
            congrArg Subtype.val hActualContactGridZero
          simpa using hz
        · rfl
      refine ⟨v,(hActualFiniteConeSweepInitial v).trans hv,e,?_⟩
      exact he.imp (fun h => h.trans hparam) (fun h => h.trans hparam)
  have actualThreeSubedgeParameterCover (e : actualNegativeFaceIntervals) (t : Interval) :
      ∃ j : Fin 3,t∈Set.Icc (actualSegmentStartParameter (e,j))
        (actualSegmentEndParameter (e,j)) := by
    as_aux_lemma =>
      by_cases h0 : t≤privateParameter 0
      · refine ⟨0,?_⟩
        simpa [actualSegmentStartParameter,actualSegmentEndParameter] using
          (show t∈Set.Icc (0 : Interval) (privateParameter 0) from ⟨t.property.1,h0⟩)
      by_cases h1 : t≤privateParameter 1
      · refine ⟨1,?_⟩
        simpa [actualSegmentStartParameter,actualSegmentEndParameter] using
          (show t∈Set.Icc (privateParameter 0) (privateParameter 1) from ⟨(lt_of_not_ge h0).le,h1⟩)
      · refine ⟨2,?_⟩
        simpa [actualSegmentStartParameter,actualSegmentEndParameter] using
          (show t∈Set.Icc (privateParameter 1) (1 : Interval) from ⟨(lt_of_not_ge h1).le,t.property.2⟩)
  have actualContactPlanarArcThreeSubedgeCoverage (e : actualNegativeFaceIntervals) :
      Set.range (fun t : Interval => actualParameterSquarePlane (actualGlobalContactArcs e t))=
        ⋃ j : Fin 3,Graph.edgeArc actualPlanarDrawing (e,j) := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        obtain ⟨j,hj⟩ := actualThreeSubedgeParameterCover e t
        obtain ⟨w,hw⟩ := actualIntervalSegmentSurjectiveOnBounds
          (actualSegmentStartParameter (e,j)) (actualSegmentEndParameter (e,j)) t hj
        apply Set.mem_iUnion.mpr
        refine ⟨j,w.val,w.property,?_⟩
        change (actualSegmentPlanarPath (e,j)).extend w.val=
          actualParameterSquarePlane (actualGlobalContactArcs e t)
        rw [Path.extend_apply _ w.property]
        change actualParameterSquarePlane (actualGlobalContactArcs e
          (actualIntervalSegment (actualSegmentStartParameter (e,j)) (actualSegmentEndParameter (e,j)) w))=
            actualParameterSquarePlane (actualGlobalContactArcs e t)
        rw [hw]
      · intro hz
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
        obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter (e,j) z hj
        exact ⟨u,he⟩
  have actualContactPlanarGraphVerticesFinite : actualPlanarGraph.vertexSet.Finite := Set.finite_range _
  have actualOriginalPlanarContactVerticesRetained : actualContactPlaneVertices⊆actualPlanarGraph.vertexSet := by
    as_aux_lemma =>
      rintro z ⟨v,hv,rfl⟩
      exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩
  have hActualContactArcOnInitialBoundaryCell (e : actualNegativeFaceIntervals) (t v : Interval)
      (j : Fin (actualContactGridSize+1))
      (hj : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ))
      (he : actualGlobalContactArcs e t=(0,v)) : e.1.1.val=(0,j) := by
    as_aux_lemma =>
      obtain ⟨hx,hy⟩ := hActualGlobalContactArcClosedCell e t
      rw [he] at hx hy
      have hx0 : actualContactGridParameter e.1.1.val.1.castSucc=0 :=
        le_antisymm hx.1 (actualContactGridParameter e.1.1.val.1.castSucc).property.1
      have hidx := hActualContactGridStrict.injective (hx0.trans hActualContactGridZero.symm)
      have hi : e.1.1.val.1=0 := by
        apply Fin.ext
        change e.1.1.val.1.val=0
        simpa using congrArg (fun z : Fin (actualContactGridSize+2) => z.val) hidx
      have hj' : j=e.1.1.val.2 := hActualGridOpenClosedUnique _ _ v hj hy
      exact Prod.ext hi hj'.symm
  have hActualContactArcOnInitialBoundaryIsEndpoint (e : actualNegativeFaceIntervals) (t v : Interval)
      (he : actualGlobalContactArcs e t=(0,v)) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      by_cases ht : t=0 ∨ t=1
      · exact ht
      have htI : t∈Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun h => ht (Or.inl h.symm)),
          lt_of_le_of_ne t.property.2 (fun h => ht (Or.inr h))⟩
      obtain ⟨hlo,hhi,hlo',hhi'⟩ := hActualGlobalContactArcStrictCell e t htI
      rw [he] at hlo
      exact False.elim (not_lt_of_ge (actualContactGridParameter e.1.1.val.1.castSucc).property.1 hlo)
  have hActualLocalContactArcInitialBoundaryFace (f : actualNegativeFaceIntervals) (t u : Interval)
      (hu : u∈Set.Ioo (0 : Interval) 1) (ht : t=0 ∨ t=1)
      (hp : actualLocalContactArcs f t=(0,u)) :
      f.1.2=3 ∧ (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
        actualFaceContactMesh f.1 f.2.val.succ=u) := by
    as_aux_lemma =>
      let k := f.1.1
      have hmem : actualCellLeftEdge k.val u∈a.val.image := by
        have hm := hActualLocalContactArcImage f t
        rw [hp,(hActualConeCellBoundary k.val u).2.2.2] at hm
        exact hm
      have hnormal := ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
        (hActualCellLeftRange k.val ⟨u,rfl⟩)).mp hmem
      have hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace 3 u)).val.1=0 := by
        have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 3 u)
        rw [hActualBoundaryFaceThreeCoordinates,(hActualConeCellBoundary k.val u).2.2.2] at hh
        exact (congrArg Prod.fst hh).symm.trans hnormal
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
        ⟨actualBoundaryFace 3 u,by
          change (actualCellBoundaryLoops k.val (actualBoundaryFace 3 u)).val.1/(actualCellCenters k.val).val.1≤0
          rw [hroot]
          simp⟩
      have hqroot : actualCompleteCellRadial k z0=(0,u) :=
        (hActualCompleteRadialMatchesFace k 3 z0).trans
          ((actualFaceContactBoundaryFix (k,3) z0 hroot).trans (hActualBoundaryFaceThreeCoordinates u))
      have faceAtRoot (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) (r : Interval)
          (hz : z.val=actualBoundaryFace f.1.2 r)
          (hq : actualFaceContactRadial f.1 z=(0,u)) : f.1.2=3 ∧ r=u := by
        have hqz : actualCompleteCellRadial k z=(0,u) :=
          (hActualCompleteRadialMatchesFace k f.1.2 z).trans hq
        have hzz : z=z0 := hActualCompleteCellRadialInjective k (hqz.trans hqroot.symm)
        have he : actualBoundaryFace f.1.2 r=actualBoundaryFace 3 u :=
          hz.symm.trans (congrArg Subtype.val hzz)
        have hfi : 3=f.1.2 := actualBoundaryFaceOpenUnique 3 f.1.2 u r hu he.symm
        have hr : r=u := hActualBoundaryFaceInjective 3 (by simpa only [←hfi] using he)
        exact ⟨hfi.symm,hr⟩
      rcases ht with rfl | rfl
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcStart f)
          (actualFaceContactMesh f.1 f.2.val.castSucc) (hActualLocalContactArcStartFace f)
          ((hActualLocalContactArcStart f).symm.trans hp)
        exact ⟨hf,Or.inl hr⟩
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcEnd f)
          (actualFaceContactMesh f.1 f.2.val.succ) (hActualLocalContactArcEndFace f)
          ((hActualLocalContactArcEnd f).symm.trans hp)
        exact ⟨hf,Or.inr hr⟩
  have hActualInitialBoundaryRootUniqueActualContactArc (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellLeftEdge (0,j) u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,
        (actualGlobalContactArcs e 0=actualAffineCells (0,j) (0,u) ∨
          actualGlobalContactArcs e 1=actualAffineCells (0,j) (0,u)) ∧
        ∀ (f : actualNegativeFaceIntervals) (t : Interval),
          actualGlobalContactArcs f t=actualAffineCells (0,j) (0,u) → f=e := by
    as_aux_lemma =>
      obtain ⟨e,hecell,heface,he,hunique⟩ := hActualInitialFaceContactHasActualArcEndpoint j u hu hmem
      let v := actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) u
      have hv : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) :=
        actualIntervalSegmentInterior _ _ u (hActualContactGridStep j) hu
      have hparam : actualAffineCells (0,j) (0,u)=(0,v) := hActualInitialAffineCellPlacement j u
      refine ⟨e,he,?_⟩
      intro f t hf
      have hpoint : actualGlobalContactArcs f t=(0,v) := hf.trans hparam
      have hfcell := hActualContactArcOnInitialBoundaryCell f t v j hv hpoint
      have hft := hActualContactArcOnInitialBoundaryIsEndpoint f t v hpoint
      have hlocal : actualLocalContactArcs f t=(0,u) := by
        apply (hActualAffineCellEmbedding f.1.1.val).injective
        change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=
          actualAffineCells f.1.1.val (0,u)
        change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=
          actualAffineCells (0,j) (0,u) at hf
        simpa only [hfcell] using hf
      obtain ⟨hface,hmesh⟩ := hActualLocalContactArcInitialBoundaryFace f t u hu hft hlocal
      exact hunique f hfcell hface hmesh
  have hActualLowerFaceContactHasActualArcEndpoint (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellBottomEdge (j,0) u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,e.1.1.val=(j,0) ∧ e.1.2=0 ∧
        (actualGlobalContactArcs e 0=actualAffineCells (j,0) (u,0) ∨
          actualGlobalContactArcs e 1=actualAffineCells (j,0) (u,0)) ∧
        ∀ f : actualNegativeFaceIntervals,f.1.1.val=(j,0) → f.1.2=0 →
          (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
            actualFaceContactMesh f.1 f.2.val.succ=u) → f=e := by
    as_aux_lemma =>
      have hf (t : Interval) : (actualCellBoundaryLoops (j,0) (actualBoundaryFace 0 t)).val=
          (actualContactGridCharts (j,0)) (actualCellBottomEdge (j,0) t) := by
        rw [←hActualCellBoundaryLoopFormula,hActualBoundaryFaceZeroCoordinates,(hActualConeCellBoundary (j,0) t).1]
      obtain ⟨e,hecell,heface,he,hunique⟩ := hActualTransverseFaceContactHasActualArcEndpoint
        (j,0) 0 (actualCellBottomEdge (j,0)).toContinuousMap (hActualLowerBottomCellEdgeTransverse j)
        (fun t => hActualCellBottomRange (j,0) ⟨t,rfl⟩) hf u hu hmem
      refine ⟨e,hecell,heface,?_,hunique⟩
      simpa only [hActualBoundaryFaceZeroCoordinates] using he
  have hActualContactArcOnLowerBoundaryCell (e : actualNegativeFaceIntervals) (t v : Interval)
      (j : Fin (actualContactGridSize+1))
      (hj : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ))
      (he : actualGlobalContactArcs e t=(v,0)) : e.1.1.val=(j,0) := by
    as_aux_lemma =>
      obtain ⟨hx,hy⟩ := hActualGlobalContactArcClosedCell e t
      rw [he] at hx hy
      have hy0 : actualContactGridParameter e.1.1.val.2.castSucc=0 :=
        le_antisymm hy.1 (actualContactGridParameter e.1.1.val.2.castSucc).property.1
      have hidx := hActualContactGridStrict.injective (hy0.trans hActualContactGridZero.symm)
      have hi : e.1.1.val.2=0 := by
        apply Fin.ext
        change e.1.1.val.2.val=0
        simpa using congrArg (fun z : Fin (actualContactGridSize+2) => z.val) hidx
      have hj' : j=e.1.1.val.1 := hActualGridOpenClosedUnique _ _ v hj hx
      exact Prod.ext hj'.symm hi
  have hActualContactArcOnLowerBoundaryIsEndpoint (e : actualNegativeFaceIntervals) (t v : Interval)
      (he : actualGlobalContactArcs e t=(v,0)) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      by_cases ht : t=0 ∨ t=1
      · exact ht
      have htI : t∈Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun h => ht (Or.inl h.symm)),
          lt_of_le_of_ne t.property.2 (fun h => ht (Or.inr h))⟩
      obtain ⟨hlo,hhi,hlo',hhi'⟩ := hActualGlobalContactArcStrictCell e t htI
      rw [he] at hlo'
      exact False.elim (not_lt_of_ge (actualContactGridParameter e.1.1.val.2.castSucc).property.1 hlo')
  have hActualLocalContactArcLowerBoundaryFace (f : actualNegativeFaceIntervals) (t u : Interval)
      (hu : u∈Set.Ioo (0 : Interval) 1) (ht : t=0 ∨ t=1)
      (hp : actualLocalContactArcs f t=(u,0)) :
      f.1.2=0 ∧ (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
        actualFaceContactMesh f.1 f.2.val.succ=u) := by
    as_aux_lemma =>
      let k := f.1.1
      have hmem : actualCellBottomEdge k.val u∈a.val.image := by
        have hm := hActualLocalContactArcImage f t
        rw [hp,(hActualConeCellBoundary k.val u).1] at hm
        exact hm
      have hnormal := ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
        (hActualCellBottomRange k.val ⟨u,rfl⟩)).mp hmem
      have hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace 0 u)).val.1=0 := by
        have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 0 u)
        rw [hActualBoundaryFaceZeroCoordinates,(hActualConeCellBoundary k.val u).1] at hh
        exact (congrArg Prod.fst hh).symm.trans hnormal
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
        ⟨actualBoundaryFace 0 u,by
          change (actualCellBoundaryLoops k.val (actualBoundaryFace 0 u)).val.1/(actualCellCenters k.val).val.1≤0
          rw [hroot]
          simp⟩
      have hqroot : actualCompleteCellRadial k z0=(u,0) :=
        (hActualCompleteRadialMatchesFace k 0 z0).trans
          ((actualFaceContactBoundaryFix (k,0) z0 hroot).trans (hActualBoundaryFaceZeroCoordinates u))
      have faceAtRoot (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) (r : Interval)
          (hz : z.val=actualBoundaryFace f.1.2 r)
          (hq : actualFaceContactRadial f.1 z=(u,0)) : f.1.2=0 ∧ r=u := by
        have hqz : actualCompleteCellRadial k z=(u,0) :=
          (hActualCompleteRadialMatchesFace k f.1.2 z).trans hq
        have hzz : z=z0 := hActualCompleteCellRadialInjective k (hqz.trans hqroot.symm)
        have he : actualBoundaryFace f.1.2 r=actualBoundaryFace 0 u :=
          hz.symm.trans (congrArg Subtype.val hzz)
        have hfi : 0=f.1.2 := actualBoundaryFaceOpenUnique 0 f.1.2 u r hu he.symm
        have hr : r=u := hActualBoundaryFaceInjective 0 (by simpa only [←hfi] using he)
        exact ⟨hfi.symm,hr⟩
      rcases ht with rfl | rfl
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcStart f)
          (actualFaceContactMesh f.1 f.2.val.castSucc) (hActualLocalContactArcStartFace f)
          ((hActualLocalContactArcStart f).symm.trans hp)
        exact ⟨hf,Or.inl hr⟩
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcEnd f)
          (actualFaceContactMesh f.1 f.2.val.succ) (hActualLocalContactArcEndFace f)
          ((hActualLocalContactArcEnd f).symm.trans hp)
        exact ⟨hf,Or.inr hr⟩
  have hActualLowerBoundaryRootUniqueActualContactArc (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellBottomEdge (j,0) u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,
        (actualGlobalContactArcs e 0=actualAffineCells (j,0) (u,0) ∨
          actualGlobalContactArcs e 1=actualAffineCells (j,0) (u,0)) ∧
        ∀ (f : actualNegativeFaceIntervals) (t : Interval),
          actualGlobalContactArcs f t=actualAffineCells (j,0) (u,0) → f=e := by
    as_aux_lemma =>
      obtain ⟨e,hecell,heface,he,hunique⟩ := hActualLowerFaceContactHasActualArcEndpoint j u hu hmem
      let v := actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) u
      have hv : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) :=
        actualIntervalSegmentInterior _ _ u (hActualContactGridStep j) hu
      have hparam : actualAffineCells (j,0) (u,0)=(v,0) := by
        rw [hActualAffineCellFormula]
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          have hz := congrArg Subtype.val hActualContactGridZero
          change (1-(0 : ℝ))*(actualContactGridParameter (0 : Fin (actualContactGridSize+2))).val+
            0*(actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ).val=0
          simpa using hz
      refine ⟨e,he,?_⟩
      intro f t hf
      have hpoint : actualGlobalContactArcs f t=(v,0) := hf.trans hparam
      have hfcell := hActualContactArcOnLowerBoundaryCell f t v j hv hpoint
      have hft := hActualContactArcOnLowerBoundaryIsEndpoint f t v hpoint
      have hlocal : actualLocalContactArcs f t=(u,0) := by
        apply (hActualAffineCellEmbedding f.1.1.val).injective
        change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=
          actualAffineCells f.1.1.val (u,0)
        change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=
          actualAffineCells (j,0) (u,0) at hf
        simpa only [hfcell] using hf
      obtain ⟨hface,hmesh⟩ := hActualLocalContactArcLowerBoundaryFace f t u hu hft hlocal
      exact hunique f hfcell hface hmesh
  have hActualUpperFaceContactHasActualArcEndpoint (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellTopEdge (j,Fin.last actualContactGridSize) u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,e.1.1.val=(j,Fin.last actualContactGridSize) ∧ e.1.2=2 ∧
        (actualGlobalContactArcs e 0=actualAffineCells (j,Fin.last actualContactGridSize) (u,1) ∨
          actualGlobalContactArcs e 1=actualAffineCells (j,Fin.last actualContactGridSize) (u,1)) ∧
        ∀ f : actualNegativeFaceIntervals,f.1.1.val=(j,Fin.last actualContactGridSize) → f.1.2=2 →
          (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
            actualFaceContactMesh f.1 f.2.val.succ=u) → f=e := by
    as_aux_lemma =>
      have hf (t : Interval) : (actualCellBoundaryLoops (j,Fin.last actualContactGridSize) (actualBoundaryFace 2 t)).val=
          (actualContactGridCharts (j,Fin.last actualContactGridSize)) (actualCellTopEdge (j,Fin.last actualContactGridSize) t) := by
        rw [←hActualCellBoundaryLoopFormula,hActualBoundaryFaceTwoCoordinates,(hActualConeCellBoundary (j,Fin.last actualContactGridSize) t).2.2.1]
      obtain ⟨e,hecell,heface,he,hunique⟩ := hActualTransverseFaceContactHasActualArcEndpoint
        (j,Fin.last actualContactGridSize) 2 (actualCellTopEdge (j,Fin.last actualContactGridSize)).toContinuousMap (hActualUpperTopCellEdgeTransverse j)
        (fun t => hActualCellTopRange (j,Fin.last actualContactGridSize) ⟨t,rfl⟩) hf u hu hmem
      refine ⟨e,hecell,heface,?_,hunique⟩
      simpa only [hActualBoundaryFaceTwoCoordinates] using he
  have hActualContactArcOnUpperBoundaryCell (e : actualNegativeFaceIntervals) (t v : Interval)
      (j : Fin (actualContactGridSize+1))
      (hj : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ))
      (he : actualGlobalContactArcs e t=(v,1)) : e.1.1.val=(j,Fin.last actualContactGridSize) := by
    as_aux_lemma =>
      obtain ⟨hx,hy⟩ := hActualGlobalContactArcClosedCell e t
      rw [he] at hx hy
      have hy1 : actualContactGridParameter e.1.1.val.2.succ=1 :=
        le_antisymm (actualContactGridParameter e.1.1.val.2.succ).property.2 hy.2
      have hidx := hActualContactGridStrict.injective (hy1.trans hActualContactGridOne.symm)
      have hi : e.1.1.val.2=Fin.last actualContactGridSize := by
        apply Fin.ext
        have hh := congrArg (fun z : Fin (actualContactGridSize+2) => z.val) hidx
        change e.1.1.val.2.val+1=actualContactGridSize+1 at hh
        change e.1.1.val.2.val=actualContactGridSize
        omega
      have hj' : j=e.1.1.val.1 := hActualGridOpenClosedUnique _ _ v hj hx
      exact Prod.ext hj'.symm hi
  have hActualContactArcOnUpperBoundaryIsEndpoint (e : actualNegativeFaceIntervals) (t v : Interval)
      (he : actualGlobalContactArcs e t=(v,1)) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      by_cases ht : t=0 ∨ t=1
      · exact ht
      have htI : t∈Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun h => ht (Or.inl h.symm)),
          lt_of_le_of_ne t.property.2 (fun h => ht (Or.inr h))⟩
      obtain ⟨hlo,hhi,hlo',hhi'⟩ := hActualGlobalContactArcStrictCell e t htI
      rw [he] at hhi'
      exact False.elim (not_lt_of_ge (actualContactGridParameter e.1.1.val.2.succ).property.2 hhi')
  have hActualLocalContactArcUpperBoundaryFace (f : actualNegativeFaceIntervals) (t u : Interval)
      (hu : u∈Set.Ioo (0 : Interval) 1) (ht : t=0 ∨ t=1)
      (hp : actualLocalContactArcs f t=(u,1)) :
      f.1.2=2 ∧ (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
        actualFaceContactMesh f.1 f.2.val.succ=u) := by
    as_aux_lemma =>
      let k := f.1.1
      have hmem : actualCellTopEdge k.val u∈a.val.image := by
        have hm := hActualLocalContactArcImage f t
        rw [hp,(hActualConeCellBoundary k.val u).2.2.1] at hm
        exact hm
      have hnormal := ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
        (hActualCellTopRange k.val ⟨u,rfl⟩)).mp hmem
      have hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace 2 u)).val.1=0 := by
        have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 2 u)
        rw [hActualBoundaryFaceTwoCoordinates,(hActualConeCellBoundary k.val u).2.2.1] at hh
        exact (congrArg Prod.fst hh).symm.trans hnormal
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
        ⟨actualBoundaryFace 2 u,by
          change (actualCellBoundaryLoops k.val (actualBoundaryFace 2 u)).val.1/(actualCellCenters k.val).val.1≤0
          rw [hroot]
          simp⟩
      have hqroot : actualCompleteCellRadial k z0=(u,1) :=
        (hActualCompleteRadialMatchesFace k 2 z0).trans
          ((actualFaceContactBoundaryFix (k,2) z0 hroot).trans (hActualBoundaryFaceTwoCoordinates u))
      have faceAtRoot (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) (r : Interval)
          (hz : z.val=actualBoundaryFace f.1.2 r)
          (hq : actualFaceContactRadial f.1 z=(u,1)) : f.1.2=2 ∧ r=u := by
        have hqz : actualCompleteCellRadial k z=(u,1) :=
          (hActualCompleteRadialMatchesFace k f.1.2 z).trans hq
        have hzz : z=z0 := hActualCompleteCellRadialInjective k (hqz.trans hqroot.symm)
        have he : actualBoundaryFace f.1.2 r=actualBoundaryFace 2 u :=
          hz.symm.trans (congrArg Subtype.val hzz)
        have hfi : 2=f.1.2 := actualBoundaryFaceOpenUnique 2 f.1.2 u r hu he.symm
        have hr : r=u := hActualBoundaryFaceInjective 2 (by simpa only [←hfi] using he)
        exact ⟨hfi.symm,hr⟩
      rcases ht with rfl | rfl
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcStart f)
          (actualFaceContactMesh f.1 f.2.val.castSucc) (hActualLocalContactArcStartFace f)
          ((hActualLocalContactArcStart f).symm.trans hp)
        exact ⟨hf,Or.inl hr⟩
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcEnd f)
          (actualFaceContactMesh f.1 f.2.val.succ) (hActualLocalContactArcEndFace f)
          ((hActualLocalContactArcEnd f).symm.trans hp)
        exact ⟨hf,Or.inr hr⟩
  have hActualUpperBoundaryRootUniqueActualContactArc (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellTopEdge (j,Fin.last actualContactGridSize) u∈a.val.image) :
      ∃ e : actualNegativeFaceIntervals,
        (actualGlobalContactArcs e 0=actualAffineCells (j,Fin.last actualContactGridSize) (u,1) ∨
          actualGlobalContactArcs e 1=actualAffineCells (j,Fin.last actualContactGridSize) (u,1)) ∧
        ∀ (f : actualNegativeFaceIntervals) (t : Interval),
          actualGlobalContactArcs f t=actualAffineCells (j,Fin.last actualContactGridSize) (u,1) → f=e := by
    as_aux_lemma =>
      obtain ⟨e,hecell,heface,he,hunique⟩ := hActualUpperFaceContactHasActualArcEndpoint j u hu hmem
      let v := actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) u
      have hv : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) :=
        actualIntervalSegmentInterior _ _ u (hActualContactGridStep j) hu
      have hparam : actualAffineCells (j,Fin.last actualContactGridSize) (u,1)=(v,1) := by
        rw [hActualAffineCellFormula]
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          have hz := congrArg Subtype.val hActualContactGridOne
          change (1-(1 : ℝ))*(actualContactGridParameter (Fin.last actualContactGridSize).castSucc).val+
            1*(actualContactGridParameter (Fin.last (actualContactGridSize+1))).val=1
          simpa using hz
      refine ⟨e,he,?_⟩
      intro f t hf
      have hpoint : actualGlobalContactArcs f t=(v,1) := hf.trans hparam
      have hfcell := hActualContactArcOnUpperBoundaryCell f t v j hv hpoint
      have hft := hActualContactArcOnUpperBoundaryIsEndpoint f t v hpoint
      have hlocal : actualLocalContactArcs f t=(u,1) := by
        apply (hActualAffineCellEmbedding f.1.1.val).injective
        change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=
          actualAffineCells f.1.1.val (u,1)
        change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=
          actualAffineCells (j,Fin.last actualContactGridSize) (u,1) at hf
        simpa only [hfcell] using hf
      obtain ⟨hface,hmesh⟩ := hActualLocalContactArcUpperBoundaryFace f t u hu hft hlocal
      exact hunique f hfcell hface hmesh
  have hActualUniqueContactArcProducesDegreeOne (point : Interval × Interval)
      (hpoint : ∃ e : actualNegativeFaceIntervals,
        (actualGlobalContactArcs e 0=point ∨ actualGlobalContactArcs e 1=point) ∧
        ∀ (f : actualNegativeFaceIntervals) (t : Interval),actualGlobalContactArcs f t=point → f=e) :
      ∃ w : actualContactVertices,w.val=point ∧ actualZeroGraph.degree (Sum.inl w)=1 := by
    as_aux_lemma =>
      obtain ⟨e,he,hunique⟩ := hpoint
      have hv : point∈actualContactVertices := by
        rcases he with he | he
        · change actualGlobalContactArcs e 0=point at he
          exact he ▸ hActualContactArcStartInVertices e
        · change actualGlobalContactArcs e 1=point at he
          exact he ▸ hActualContactArcEndInVertices e
      let w : actualContactVertices := ⟨point,hv⟩
      have leftMem (f : actualNegativeFaceIntervals) :
          f∈leftIncidentEdges w ↔ actualGlobalContactArcs f 0=point := by
        simp only [leftIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hf
          exact (congrArg Subtype.val (Sum.inl.inj hf)).symm
        · intro hf
          apply congrArg Sum.inl
          exact Subtype.ext hf.symm
      have rightMem (f : actualNegativeFaceIntervals) :
          f∈rightIncidentEdges w ↔ actualGlobalContactArcs f 1=point := by
        simp only [rightIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hf
          exact (congrArg Subtype.val (Sum.inl.inj hf)).symm
        · intro hf
          apply congrArg Sum.inl
          exact Subtype.ext hf.symm
      refine ⟨w,rfl,?_⟩
      by_cases he0 : actualGlobalContactArcs e 0=point
      · have hl : leftIncidentEdges w={e} := by
          ext f
          rw [leftMem,Finset.mem_singleton]
          constructor
          · exact hunique f 0
          · rintro rfl
            exact he0
        have hr : rightIncidentEdges w=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro f hf
          have hf0 := rightMem f |>.mp hf
          have hfe : f=e := hunique f 1 hf0
          subst f
          have h01 := (hActualGlobalContactArcEmbedding e).injective (he0.trans hf0.symm)
          exact zero_ne_one (congrArg Subtype.val h01)
        rw [zeroEndpointDegreeExact,hl,hr]
        simp
      · have he1 : actualGlobalContactArcs e 1=point := he.resolve_left he0
        have hl : leftIncidentEdges w=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro f hf
          have hf0 := leftMem f |>.mp hf
          have hfe : f=e := hunique f 0 hf0
          subst f
          exact he0 hf0
        have hr : rightIncidentEdges w={e} := by
          ext f
          rw [rightMem,Finset.mem_singleton]
          constructor
          · exact hunique f 1
          · rintro rfl
            exact he1
        rw [zeroEndpointDegreeExact,hl,hr]
        simp
  have hActualInitialBoundaryRootProducesDegreeOne (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellLeftEdge (0,j) u∈a.val.image) :
      ∃ w : actualContactVertices,w.val=actualAffineCells (0,j) (0,u) ∧
        actualZeroGraph.degree (Sum.inl w)=1 := by
    exact hActualUniqueContactArcProducesDegreeOne _
      (hActualInitialBoundaryRootUniqueActualContactArc j u hu hmem)
  have hActualLowerBoundaryRootProducesDegreeOne (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellBottomEdge (j,0) u∈a.val.image) :
      ∃ w : actualContactVertices,w.val=actualAffineCells (j,0) (u,0) ∧
        actualZeroGraph.degree (Sum.inl w)=1 := by
    exact hActualUniqueContactArcProducesDegreeOne _
      (hActualLowerBoundaryRootUniqueActualContactArc j u hu hmem)
  have hActualUpperBoundaryRootProducesDegreeOne (j : Fin (actualContactGridSize+1))
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellTopEdge (j,Fin.last actualContactGridSize) u∈a.val.image) :
      ∃ w : actualContactVertices,w.val=actualAffineCells (j,Fin.last actualContactGridSize) (u,1) ∧
        actualZeroGraph.degree (Sum.inl w)=1 := by
    exact hActualUniqueContactArcProducesDegreeOne _
      (hActualUpperBoundaryRootUniqueActualContactArc j u hu hmem)
  have hActualEveryLowerSeamContactVertexDegreeOne (w : actualContactVertices)
      (hw : w.val.2=0) : actualZeroGraph.degree (Sum.inl w)=1 := by
    as_aux_lemma =>
      have hpoint : w.val=(w.val.1,0) := Prod.ext rfl hw
      have hm : actualCentralSweep (w.val.1,0)∈a.val.image := by
        have hh := hActualContactVerticesImage w
        rw [hpoint,hActualFiniteConeSweepLower] at hh
        exact hh
      obtain ⟨j,hlo,hhi⟩ := hActualContactGridCover w.val.1
      have hj₀ : actualContactGridParameter j.castSucc<w.val.1 := lt_of_le_of_ne hlo (by
        intro he
        exact (hActualContactGridBoundaryClear j.castSucc).2.1 (he.symm ▸ hm))
      have hj₁ : w.val.1<actualContactGridParameter j.succ := lt_of_le_of_ne hhi (by
        intro he
        exact (hActualContactGridBoundaryClear j.succ).2.1 (he ▸ hm))
      let u := actualContactGridLocalCoordinate j w.val.1
      have hlocal : actualIntervalSegment (actualContactGridParameter j.castSucc)
          (actualContactGridParameter j.succ) u=w.val.1 :=
        hActualGridCoordinateReconstruct j w.val.1 hlo hhi
      have hu : u∈Set.Ioo (0 : Interval) 1 :=
        actualIntervalSegmentInteriorReflect _ _ u (hlocal.symm ▸ hj₀) (hlocal.symm ▸ hj₁)
      have hmem : actualCellBottomEdge (j,0) u∈a.val.image := by
        rw [hActualLowerBottomCellEdgeFormula,hlocal]
        exact hm
      obtain ⟨z,hz,hdegree⟩ := hActualLowerBoundaryRootProducesDegreeOne j u hu hmem
      have hparam : actualAffineCells (j,0) (u,0)=w.val := by
        rw [hpoint,hActualAffineCellFormula,hlocal]
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          have hh := congrArg Subtype.val hActualContactGridZero
          change (1-(0 : ℝ))*(actualContactGridParameter (0 : Fin (actualContactGridSize+2))).val+
            0*(actualContactGridParameter (0 : Fin (actualContactGridSize+1)).succ).val=0
          simpa using hh
      have hzw : z=w := Subtype.ext (hz.trans hparam)
      exact hzw ▸ hdegree
  have hActualEveryUpperSeamContactVertexDegreeOne (w : actualContactVertices)
      (hw : w.val.2=1) : actualZeroGraph.degree (Sum.inl w)=1 := by
    as_aux_lemma =>
      have hpoint : w.val=(w.val.1,1) := Prod.ext rfl hw
      have hm : actualCentralSweep (w.val.1,1)∈a.val.image := by
        have hh := hActualContactVerticesImage w
        rw [hpoint,hActualFiniteConeSweepUpper] at hh
        exact hh
      obtain ⟨j,hlo,hhi⟩ := hActualContactGridCover w.val.1
      have hj₀ : actualContactGridParameter j.castSucc<w.val.1 := lt_of_le_of_ne hlo (by
        intro he
        exact (hActualContactGridBoundaryClear j.castSucc).2.2 (he.symm ▸ hm))
      have hj₁ : w.val.1<actualContactGridParameter j.succ := lt_of_le_of_ne hhi (by
        intro he
        exact (hActualContactGridBoundaryClear j.succ).2.2 (he ▸ hm))
      let u := actualContactGridLocalCoordinate j w.val.1
      have hlocal : actualIntervalSegment (actualContactGridParameter j.castSucc)
          (actualContactGridParameter j.succ) u=w.val.1 :=
        hActualGridCoordinateReconstruct j w.val.1 hlo hhi
      have hu : u∈Set.Ioo (0 : Interval) 1 :=
        actualIntervalSegmentInteriorReflect _ _ u (hlocal.symm ▸ hj₀) (hlocal.symm ▸ hj₁)
      have hmem : actualCellTopEdge (j,Fin.last actualContactGridSize) u∈a.val.image := by
        rw [hActualUpperTopCellEdgeFormula,hlocal]
        exact hm
      obtain ⟨z,hz,hdegree⟩ := hActualUpperBoundaryRootProducesDegreeOne j u hu hmem
      have hparam : actualAffineCells (j,Fin.last actualContactGridSize) (u,1)=w.val := by
        rw [hpoint,hActualAffineCellFormula,hlocal]
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          have hh := congrArg Subtype.val hActualContactGridOne
          change (1-(1 : ℝ))*(actualContactGridParameter (Fin.last actualContactGridSize).castSucc).val+
            1*(actualContactGridParameter (Fin.last (actualContactGridSize+1))).val=1
          simpa using hh
      have hzw : z=w := Subtype.ext (hz.trans hparam)
      exact hzw ▸ hdegree
  have hActualEveryMarkedSeamContactVertexDegreeOne (w : actualContactVertices)
      (hw : w.val.2=0 ∨ w.val.2=1) : actualZeroGraph.degree (Sum.inl w)=1 := by
    rcases hw with hw | hw
    · exact hActualEveryLowerSeamContactVertexDegreeOne w hw
    · exact hActualEveryUpperSeamContactVertexDegreeOne w hw
  have hActualEveryOriginalCrossingProducesDegreeOne (t : Interval)
      (ht : b.val.map t∈ArcSurgery.crossings M a b) :
      ∃ w : actualContactVertices,actualFiniteConeSweep w.val=b.val.map t ∧
        w.val.1=0 ∧ actualZeroGraph.degree (Sum.inl w)=1 := by
    as_aux_lemma =>
      obtain ⟨v,j,hv,hj₀,hj₁⟩ := hActualOriginalCrossingInsideContactGrid t ht
      let u := actualContactGridLocalCoordinate j v
      have hlocal : actualIntervalSegment (actualContactGridParameter j.castSucc)
          (actualContactGridParameter j.succ) u=v :=
        hActualGridCoordinateReconstruct j v hj₀.le hj₁.le
      have hu : u∈Set.Ioo (0 : Interval) 1 :=
        actualIntervalSegmentInteriorReflect _ _ u (hlocal.symm ▸ hj₀) (hlocal.symm ▸ hj₁)
      have hleft : actualCellLeftEdge (0,j) u=actualCentralSweep (0,v) := by
        rw [hActualInitialLeftCellEdgeFormula,hlocal]
      have hmem : actualCellLeftEdge (0,j) u∈a.val.image := by
        rw [hleft,hv]
        exact ht.1.1
      obtain ⟨w,hw,hdegree⟩ := hActualInitialBoundaryRootProducesDegreeOne j u hu hmem
      have hwpoint : w.val=(0,v) := hw.trans ((hActualInitialAffineCellPlacement j u).trans (Prod.ext rfl hlocal))
      refine ⟨w,?_,congrArg Prod.fst hwpoint,hdegree⟩
      rw [hwpoint,hActualFiniteConeSweepInitial]
      exact hv
  have hActualSpecifiedOriginalCrossingProducesOddVertex :
      ∃ w : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧
        Odd (actualZeroGraph.degree (Sum.inl w)) := by
    as_aux_lemma =>
      obtain ⟨t,ht⟩ := hp.2.1
      have hcross : b.val.map t∈ArcSurgery.crossings M a b := ht.symm ▸ hp
      obtain ⟨w,hw,hboundary,hdegree⟩ := hActualEveryOriginalCrossingProducesDegreeOne t hcross
      refine ⟨w,hw.trans ht,hboundary,?_⟩
      rw [hdegree]
      norm_num
  have hActualSpecifiedOriginalCrossingHasActualOddContactPartner :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ W : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),W.IsPath := by
    as_aux_lemma =>
      obtain ⟨w,hw,hboundary,hodd⟩ := hActualSpecifiedOriginalCrossingProducesOddVertex
      obtain ⟨v,hvw,hvodd,W,hW⟩ := CurveComplex.LocalSurgery.actual_odd_vertex_has_distinct_path_partner
        actualZeroGraph (Sum.inl w) hodd
      rcases v with z | ⟨e,j⟩
      · refine ⟨w,z,hw,hboundary,?_,hvodd,W,hW⟩
        intro he
        exact hvw (congrArg Sum.inl he)
      · fin_cases j
        · change Odd (actualZeroGraph.degree (Sum.inr (e,(0 : Fin 2)))) at hvodd
          rw [(zeroSubdivisionDegrees e).1] at hvodd
          norm_num at hvodd
        · change Odd (actualZeroGraph.degree (Sum.inr (e,(1 : Fin 2)))) at hvodd
          rw [(zeroSubdivisionDegrees e).2] at hvodd
          norm_num at hvodd
  have hActualPlanarSubedgeLink (q : actualNegativeFaceIntervals × Fin 3) :
      actualPlanarGraph.IsLink q (actualPlanarVertexPosition (actualSegmentStartVertex q))
        (actualPlanarVertexPosition (actualSegmentEndVertex q)) :=
    Or.inl ⟨(actualSegmentPlanarSource q).symm,(actualSegmentPlanarTarget q).symm⟩
  have hActualDirectedContactIncidenceProducesPlanarLink (v w : zeroVertex)
      (h : zeroDirectedIncidence v w) :
      ∃ q,actualPlanarGraph.IsLink q (actualPlanarVertexPosition v) (actualPlanarVertexPosition w) := by
    as_aux_lemma =>
      rcases h with ⟨e,h⟩
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · refine ⟨(e,0),?_⟩
        simpa only [actualSegmentStartVertex,actualSegmentEndVertex,if_pos rfl] using hActualPlanarSubedgeLink (e,0)
      · refine ⟨(e,1),?_⟩
        simpa [actualSegmentStartVertex,actualSegmentEndVertex] using hActualPlanarSubedgeLink (e,1)
      · refine ⟨(e,2),?_⟩
        simpa [actualSegmentStartVertex,actualSegmentEndVertex] using hActualPlanarSubedgeLink (e,2)
  have hActualContactGraphAdjacencyProducesPlanarLink {v w : zeroVertex}
      (h : actualZeroGraph.Adj v w) :
      ∃ q,actualPlanarGraph.IsLink q (actualPlanarVertexPosition v) (actualPlanarVertexPosition w) := by
    as_aux_lemma =>
      rcases h.2 with h | h
      · exact hActualDirectedContactIncidenceProducesPlanarLink v w h
      · obtain ⟨q,hq⟩ := hActualDirectedContactIncidenceProducesPlanarLink w v h
        exact ⟨q,hq.symm⟩
  have hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          ∃ W : List (actualNegativeFaceIntervals × Fin 3),W≠[] ∧
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
              actualPlanarVertexPosition '' {r | r∈P.support} ∧
            Schoenflies.IsArcBetween (Graph.edgesCover actualPlanarDrawing W)
              (actualPlanarVertexPosition (Sum.inl w)) (actualPlanarVertexPosition (Sum.inl z)) := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP⟩ := hActualSpecifiedOriginalCrossingHasActualOddContactPartner
      obtain ⟨W,hW,hvertices⟩ := CurveComplex.LocalSurgery.actual_simple_graph_path_to_labeled_graph_with_vertices
        actualZeroGraph actualPlanarGraph actualPlanarVertexPosition actualPlanarVertexPositionInjective
        (fun r => ⟨r,rfl⟩) (fun h => hActualContactGraphAdjacencyProducesPlanarLink h) P hP
      have hne : W≠[] := by
        intro hn
        rw [hn] at hW
        have he : (Sum.inl w : zeroVertex)=Sum.inl z := actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil
        exact hzw (Sum.inl.inj he).symm
      exact ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,
        actualPlanarDrawingIsDrawing.path_isArcBetween hW hne⟩
  have hActualPlanarArcLiftsToEmbeddedParameterSquarePath
      (A : Set Schoenflies.Plane) (x y : Interval × Interval)
      (hA : Schoenflies.IsArcBetween A (actualParameterSquarePlane x) (actualParameterSquarePlane y))
      (hRange : A⊆Set.range actualParameterSquarePlane) :
      ∃ q : Path x y,IsEmbedding q ∧ actualParameterSquarePlane '' Set.range q=A := by
    as_aux_lemma =>
      obtain ⟨γ,hγc,hγi,hγA,hγ₀,hγ₁⟩ := hA
      let R := Set.range actualParameterSquarePlane
      let rx : R := ⟨actualParameterSquarePlane x,⟨x,rfl⟩⟩
      let ry : R := ⟨actualParameterSquarePlane y,⟨y,rfl⟩⟩
      have hγR (t : Interval) : γ t.val∈R := hRange (hγA ▸ ⟨t.val,t.property,rfl⟩)
      let r : Path rx ry := {
        toFun := fun t => ⟨γ t.val,hγR t⟩
        continuous_toFun := (continuousOn_iff_continuous_restrict.mp hγc).subtype_mk _
        source' := by apply Subtype.ext;exact hγ₀
        target' := by apply Subtype.ext;exact hγ₁ }
      let E := hActualParameterSquarePlaneEmbedding.toHomeomorph
      have hback (z : R) : actualParameterSquarePlane (E.symm z)=z.val :=
        congrArg Subtype.val (E.apply_symm_apply z)
      have hrx : E.symm rx=x := hActualParameterSquarePlaneInjective (hback rx)
      have hry : E.symm ry=y := hActualParameterSquarePlaneInjective (hback ry)
      let q : Path x y := (r.map E.symm.continuous).cast hrx.symm hry.symm
      have hq : IsEmbedding q := by
        apply (q.continuous.isClosedEmbedding ?_).isEmbedding
        intro t u he
        have hr : r t=r u := E.symm.injective he
        exact Subtype.ext (hγi t.property u.property (congrArg Subtype.val hr))
      have hpoint (t : Interval) : actualParameterSquarePlane (q t)=γ t.val := hback (r t)
      refine ⟨q,hq,?_⟩
      ext z
      constructor
      · rintro ⟨v,⟨t,rfl⟩,rfl⟩
        rw [hpoint]
        exact hγA ▸ ⟨t.val,t.property,rfl⟩
      · intro hz
        obtain ⟨t,ht,he⟩ := (show z∈γ '' Set.Icc (0 : ℝ) 1 from hγA.symm ▸ hz)
        exact ⟨q ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,(hpoint ⟨t,ht⟩).trans he⟩
  have hActualSpecifiedCrossingProducesEmbeddedSquareContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          ∃ W : List (actualNegativeFaceIntervals × Fin 3),W≠[] ∧
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            ∃ q : Path w.val z.val,IsEmbedding q ∧
              actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W ∧
              (∀ t,actualFiniteConeSweep (q t)∈a.val.image) ∧
              (∀ t,actualFiniteConeSweep (q t)∉(M.cover.branch : Set S)) := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,hArc⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 u,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqu : actualGlobalContactArcs e.1 u=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqu]
        exact hActualGlobalContactArcImage e.1 u
      exact ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,q,hq,himage,hcontact,
        fun t => hActualFiniteConeSweepMarks _⟩
  have hActualOldArcContactPathHasOriginalInteriorParameters
      (x y : Interval × Interval) (q : Path x y)
      (hcontact : ∀ t,actualFiniteConeSweep (q t)∈a.val.image)
      (hmarks : ∀ t,actualFiniteConeSweep (q t)∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
        ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      let R := Set.range a.val.map
      let E := (NonLoopArc.isEmbedding (⟨a.val,hane⟩ : NonLoopArc M)).toHomeomorph
      let r : C(Interval,R) := {
        toFun := fun t => ⟨actualFiniteConeSweep (q t),hcontact t⟩
        continuous_toFun := (actualFiniteConeSweep.continuous.comp q.continuous).subtype_mk _ }
      let κ : C(Interval,Interval) := ⟨fun t => E.symm (r t),E.symm.continuous.comp r.continuous⟩
      have hκ (t : Interval) : a.val.map (κ t)=actualFiniteConeSweep (q t) :=
        congrArg Subtype.val (E.apply_symm_apply (r t))
      refine ⟨κ,hκ,?_⟩
      intro t
      have hκ₀ : κ t≠0 := by
        intro he
        have ht := hκ t
        rw [he] at ht
        exact hmarks t (ht ▸ a.val.start_marked)
      have hκ₁ : κ t≠1 := by
        intro he
        have ht := hκ t
        rw [he] at ht
        exact hmarks t (ht ▸ a.val.end_marked)
      exact ⟨lt_of_le_of_ne (κ t).property.1 (Ne.symm hκ₀),
        lt_of_le_of_ne (κ t).property.2 hκ₁⟩
  have hActualSpecifiedCrossingProducesOriginalParameterContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,q,hq,himage,hcontact,hmarks⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedSquareContactPath
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact hmarks
      exact ⟨w,z,hw,hleft,hzw,hodd,q,hq,κ,hκ,hinside⟩
  have hActualOriginalInteriorParameterPathStraightensInSelectedCarrier
      (κ : C(Interval,Interval)) (hκ : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) (u : S) :
      ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨a.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=a.val.map (κ t)) ∧
        (∀ t,(β t : S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let J := Set.Ioo (0 : ℝ) 1
      let x : J := ⟨(κ 0).val,hκ 0⟩
      let y : J := ⟨(κ 1).val,hκ 1⟩
      let r : Path x y := {
        toFun := fun t => ⟨(κ t).val,hκ t⟩
        continuous_toFun := (continuous_subtype_val.comp κ.continuous).subtype_mk hκ
        source' := rfl
        target' := rfl }
      have hseg (t : Interval) : (actualIntervalSegment (κ 0) (κ 1) t).val∈J := by
        have hx₀ : 0<(κ 0).val := (hκ 0).1
        have hx₁ : (κ 0).val<1 := (hκ 0).2
        have hy₀ : 0<(κ 1).val := (hκ 1).1
        have hy₁ : (κ 1).val<1 := (hκ 1).2
        change 0<(1-t.val)*(κ 0).val+t.val*(κ 1).val ∧
          (1-t.val)*(κ 0).val+t.val*(κ 1).val<1
        simpa only [smul_eq_mul,Set.mem_Ioo] using (convex_Ioo (0 : ℝ) 1) (show (κ 0).val∈Set.Ioo (0 : ℝ) 1 from ⟨hx₀,hx₁⟩) (show (κ 1).val∈Set.Ioo (0 : ℝ) 1 from ⟨hy₀,hy₁⟩) (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
      let s : Path x y := {
        toFun := fun t => ⟨(actualIntervalSegment (κ 0) (κ 1) t).val,hseg t⟩
        continuous_toFun := (continuous_subtype_val.comp (actualIntervalSegment (κ 0) (κ 1)).continuous).subtype_mk hseg
        source' := by apply Subtype.ext;change (1-(0 : ℝ))*(κ 0).val+0*(κ 1).val=(κ 0).val;ring
        target' := by apply Subtype.ext;change (1-(1 : ℝ))*(κ 0).val+1*(κ 1).val=(κ 1).val;ring }
      let inc : C(J,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2.le⟩,
        continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1.le,t.property.2.le⟩)⟩
      have havoid (t : J) : a.val.map (inc t)∉(M.cover.branch : Set S) := by
        intro hm
        rcases a.val.marked_only_at_ends (inc t) hm with he | he
        · have hv := congrArg Subtype.val he
          exact (ne_of_gt t.property.1) hv
        · have hv := congrArg Subtype.val he
          exact (ne_of_lt t.property.2) hv
      let T := ((M.cover.branch : Set S)\{u})ᶜ
      have htarget (t : J) : a.val.map (inc t)∈T := by
        intro hm
        exact havoid t hm.1
      let A : C(J,T) := ⟨fun t => ⟨a.val.map (inc t),htarget t⟩,
        (a.val.continuous.comp inc.continuous).subtype_mk htarget⟩
      letI : ContractibleSpace J := (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨x,x.property⟩
      have hhom : r.Homotopic s := SimplyConnectedSpace.paths_homotopic r s
      exact ⟨htarget x,htarget y,r.map A.continuous,s.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualSpecifiedCrossingProducesPuncturedOldArcPathHomotopy (u : S) :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            (∀ t,κ t∈Set.Ioo (0 : Interval) 1) ∧
            ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
              (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
              (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
                ⟨a.val.map (κ 1),hy⟩),
              (∀ t,(α t : S)=actualFiniteConeSweep (q t)) ∧
              (∀ t,(β t : S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
              α.Homotopic β := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,q,hq,κ,hκ,hinside⟩ :=
        hActualSpecifiedCrossingProducesOriginalParameterContactPath
      obtain ⟨hx,hy,α,β,hα,hβ,hhom⟩ :=
        hActualOriginalInteriorParameterPathStraightensInSelectedCarrier κ hinside u
      exact ⟨w,z,hw,hleft,hzw,hodd,q,hq,κ,hκ,hinside,hx,hy,α,β,
        fun t => (hα t).trans (hκ t),hβ,hhom⟩
  have hActualEveryInitialContactVertexDegreeOne (v : actualContactVertices)
      (hv : v.val.1=0) : actualZeroGraph.degree (Sum.inl v)=1 := by
    as_aux_lemma =>
      have hvpoint : v.val=(0,v.val.2) := Prod.ext hv rfl
      have hpoint : actualFiniteConeSweep v.val=b.val.map (actualCentralParameter v.val.2) := by
        rw [hvpoint,hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
      have hcross : b.val.map (actualCentralParameter v.val.2)∈ArcSurgery.crossings M a b := by
        refine ⟨⟨hpoint ▸ hActualContactVerticesImage v,hpoint ▸ hActualFiniteConeSweepMarks v.val⟩,
          ⟨⟨actualCentralParameter v.val.2,rfl⟩,hpoint ▸ hActualFiniteConeSweepMarks v.val⟩⟩
      obtain ⟨w,hw,hwleft,hwdegree⟩ :=
        hActualEveryOriginalCrossingProducesDegreeOne (actualCentralParameter v.val.2) hcross
      have hwpoint : w.val=(0,w.val.2) := Prod.ext hwleft rfl
      have he : actualCentralSweep (0,w.val.2)=actualCentralSweep (0,v.val.2) := by
        rw [←hActualFiniteConeSweepInitial,←hwpoint,hw,←hpoint,hvpoint,hActualFiniteConeSweepInitial]
      have hcoord : w.val.2=v.val.2 := hActualCentralSweepInitialEmbedding.injective he
      have hepair : ((0 : Interval),w.val.2)=((0 : Interval),v.val.2) := Prod.ext rfl hcoord
      have hwv : w=v := Subtype.ext (hwpoint.trans (hepair.trans hvpoint.symm))
      exact hwv ▸ hwdegree
  have hActualOriginalInitialContactPathSupportOnlyEndpoints
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (v : actualContactVertices) (hv : v.val.1=0)
      (hsupport : Sum.inl v∈P.support) : v=w ∨ v=z := by
    as_aux_lemma =>
      have he := CurveComplex.LocalSurgery.actual_degree_one_path_support_is_endpoint
        actualZeroGraph P hP hsupport (hActualEveryInitialContactVertexDegreeOne v hv)
      exact he.elim (fun h => Or.inl (Sum.inl.inj h)) (fun h => Or.inr (Sum.inl.inj h))
  have hActualSourceSquarePathsHomotopicInSelectedPuncturedCarrier
      (u : S) {x y : Interval × Interval} (q r : Path x y) :
      ∃ (hx : actualFiniteConeSweep x∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : actualFiniteConeSweep y∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨actualFiniteConeSweep x,hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨actualFiniteConeSweep y,hy⟩),
        (∀ t,(α t : S)=actualFiniteConeSweep (q t)) ∧
        (∀ t,(β t : S)=actualFiniteConeSweep (r t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let T := ((M.cover.branch : Set S)\{u})ᶜ
      have havoid (z : Interval × Interval) : actualFiniteConeSweep z∈T := by
        intro hz
        exact hActualFiniteConeSweepMarks z hz.1
      let A : C(Interval × Interval,T) := ⟨fun z => ⟨actualFiniteConeSweep z,havoid z⟩,
        actualFiniteConeSweep.continuous.subtype_mk _⟩
      letI : ContractibleSpace Interval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
      have hhom : q.Homotopic r := SimplyConnectedSpace.paths_homotopic q r
      exact ⟨havoid x,havoid y,q.map A.continuous,r.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualBottomEndpointsContactPathHomotopicToOriginalBoundary
      (u : S) {x y : Interval × Interval} (q : Path x y)
      (hx₀ : x.1=0) (hy₀ : y.1=0) :
      ∃ (hx : actualFiniteConeSweep x∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : actualFiniteConeSweep y∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨actualFiniteConeSweep x,hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨actualFiniteConeSweep y,hy⟩),
        (∀ t,(α t : S)=actualFiniteConeSweep (q t)) ∧
        (∀ t,(β t : S)=b.val.map (actualCentralParameter (actualIntervalSegment x.2 y.2 t))) ∧
        α.Homotopic β := by
    as_aux_lemma =>
      let r₀ : Path ((0 : Interval),x.2) ((0 : Interval),y.2) := {
        toFun := fun t => (0,actualIntervalSegment x.2 y.2 t)
        continuous_toFun := continuous_const.prodMk (actualIntervalSegment x.2 y.2).continuous
        source' := by apply Prod.ext; rfl; apply Subtype.ext; change (1-(0 : ℝ))*x.2.val+0*y.2.val=x.2.val; ring
        target' := by apply Prod.ext; rfl; apply Subtype.ext; change (1-(1 : ℝ))*x.2.val+1*y.2.val=y.2.val; ring }
      have hx : x=((0 : Interval),x.2) := Prod.ext hx₀ rfl
      have hy : y=((0 : Interval),y.2) := Prod.ext hy₀ rfl
      let r : Path x y := r₀.cast hx hy
      obtain ⟨hxm,hym,α,β,hα,hβ,hhom⟩ :=
        hActualSourceSquarePathsHomotopicInSelectedPuncturedCarrier u q r
      refine ⟨hxm,hym,α,β,hα,?_,hhom⟩
      intro t
      rw [hβ t]
      change actualFiniteConeSweep (0,actualIntervalSegment x.2 y.2 t)=_
      rw [hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
  have hActualBottomContactOriginalOldArcParametersDistinct
      (w z : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0) (hzw : z≠w)
      (q : Path w.val z.val) (κ : C(Interval,Interval))
      (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) : κ 0≠κ 1 := by
    as_aux_lemma =>
      intro he
      have hpoint : actualFiniteConeSweep w.val=actualFiniteConeSweep z.val := by
        simpa only [q.source,q.target] using (hκ 0).symm.trans ((congrArg a.val.map he).trans (hκ 1))
      have hwpoint : w.val=((0 : Interval),w.val.2) := Prod.ext hw rfl
      have hzpoint : z.val=((0 : Interval),z.val.2) := Prod.ext hz rfl
      rw [hwpoint,hzpoint,hActualFiniteConeSweepInitial,hActualFiniteConeSweepInitial] at hpoint
      have hcoord : w.val.2=z.val.2 := hActualCentralSweepInitialEmbedding.injective hpoint
      have hepair : ((0 : Interval),w.val.2)=((0 : Interval),z.val.2) := Prod.ext rfl hcoord
      exact hzw (Subtype.ext (hzpoint.trans (hepair.symm.trans hwpoint.symm)))
  have actualIntervalSegmentInjectiveOfNe (x y : Interval) (hxy : x≠y) :
      Function.Injective (actualIntervalSegment x y) := by
    as_aux_lemma =>
      intro t s he
      have hv := congrArg Subtype.val he
      change (1-t.val)*x.val+t.val*y.val=(1-s.val)*x.val+s.val*y.val at hv
      have hprod : (y.val-x.val)*(t.val-s.val)=0 := by nlinarith only [hv]
      rcases mul_eq_zero.mp hprod with hbad | hts
      · exact False.elim (hxy (Subtype.ext (sub_eq_zero.mp hbad).symm))
      · exact Subtype.ext (sub_eq_zero.mp hts)
  have hActualNondegenerateOldArcIntervalSubpathEmbedding (x y : Interval) (hxy : x≠y) :
      IsEmbedding (fun t : Interval => a.val.map (actualIntervalSegment x y t)) := by
    as_aux_lemma =>
      exact (NonLoopArc.isEmbedding (⟨a.val,hane⟩ : NonLoopArc M)).comp
        (((actualIntervalSegment x y).continuous.isClosedEmbedding
          (actualIntervalSegmentInjectiveOfNe x y hxy)).isEmbedding)
  have hActualInitialContactPlanarCarrierOnlyEndpoints
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (W : List (actualNegativeFaceIntervals × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
        (actualPlanarVertexPosition (Sum.inl z)))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (v : actualContactVertices) (hv : v.val.1=0)
      (hcarrier : actualPlanarVertexPosition (Sum.inl v)∈Graph.edgesCover actualPlanarDrawing W) :
      v=w ∨ v=z := by
    as_aux_lemma =>
      obtain ⟨e,he,hve⟩ := Graph.mem_edgesCover_iff.mp hcarrier
      have hvvertex : actualPlanarVertexPosition (Sum.inl v)∈actualPlanarGraph.vertexSet :=
        ⟨Sum.inl v,rfl⟩
      have hend := actualPlanarDrawingIsDrawing.vertex_mem_edgeArc
        (hActualPlanarSubedgeLink e) hvvertex hve
      have hinc : actualPlanarGraph.Inc e (actualPlanarVertexPosition (Sum.inl v)) := by
        rcases hend with h | h
        · exact h ▸ (hActualPlanarSubedgeLink e).inc_left
        · exact h ▸ (hActualPlanarSubedgeLink e).inc_right
      have hwalk : actualPlanarVertexPosition (Sum.inl v)∈
          actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W :=
        Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices he hinc)
      rw [hvertices] at hwalk
      obtain ⟨r,hr,heq⟩ := hwalk
      have hrv : r=Sum.inl v := actualPlanarVertexPositionInjective heq
      exact hActualOriginalInitialContactPathSupportOnlyEndpoints P hP v hv (hrv ▸ hr)
  have hActualEmbeddedSquareContactPathMeetsInitialBoundaryOnlyAtEnds
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (W : List (actualNegativeFaceIntervals × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
        (actualPlanarVertexPosition (Sum.inl z)))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (q : Path w.val z.val) (hq : IsEmbedding q)
      (himage : actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W)
      (t : Interval) (ht : (q t).1=0) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      have hcarrier : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
        himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
      obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hcarrier
      obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
      have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
      have hqrinitial : actualGlobalContactArcs e.1 r=(0,(q t).2) :=
        hqr.trans (Prod.ext ht rfl)
      have hrend := hActualContactArcOnInitialBoundaryIsEndpoint e.1 r (q t).2 hqrinitial
      have hv : q t∈actualContactVertices := by
        rcases hrend with rfl | rfl
        · exact hqr ▸ hActualContactArcStartInVertices e.1
        · exact hqr ▸ hActualContactArcEndInVertices e.1
      let v : actualContactVertices := ⟨q t,hv⟩
      have hvposition : actualPlanarVertexPosition (Sum.inl v)=actualParameterSquarePlane (q t) := rfl
      have hend : v=w ∨ v=z := hActualInitialContactPlanarCarrierOnlyEndpoints P hP W hW
        hvertices v ht (hvposition.symm ▸ hcarrier)
      rcases hend with h | h
      · have hpoint : q t=w.val := congrArg Subtype.val h
        exact Or.inl (hq.injective (hpoint.trans q.source.symm))
      · have hpoint : q t=z.val := congrArg Subtype.val h
        exact Or.inr (hq.injective (hpoint.trans q.target.symm))
  have hActualSpecifiedCrossingProducesBottomProperOriginalContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧ (∀ t,(q t).1=0 → t=0 ∨ t=1) ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,hArc⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 r,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqr]
        exact hActualGlobalContactArcImage e.1 r
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact
        (fun t => hActualFiniteConeSweepMarks (q t))
      exact ⟨w,z,hw,hleft,hzw,hodd,q,hq,
        fun t ht => hActualEmbeddedSquareContactPathMeetsInitialBoundaryOnlyAtEnds P hP W hW
          hvertices q hq himage t ht,κ,hκ,hinside⟩
  have hActualGlobalContactArcOnOuterBoundaryIsEndpoint
      (e : actualNegativeFaceIntervals) (t : Interval)
      (hboundary : (actualGlobalContactArcs e t).1=0 ∨ (actualGlobalContactArcs e t).1=1 ∨
        (actualGlobalContactArcs e t).2=0 ∨ (actualGlobalContactArcs e t).2=1) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      rcases hboundary with hx | hx | hy | hy
      · exact hActualContactArcOnInitialBoundaryIsEndpoint e t (actualGlobalContactArcs e t).2 (Prod.ext hx rfl)
      · by_cases ht : t=0 ∨ t=1
        · exact ht
        have htI : t∈Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (fun h => ht (Or.inl h.symm)),
            lt_of_le_of_ne t.property.2 (fun h => ht (Or.inr h))⟩
        have hhi := (hActualGlobalContactArcStrictCell e t htI).2.1
        rw [hx] at hhi
        exact False.elim (not_lt_of_ge (actualContactGridParameter e.1.1.val.1.succ).property.2 hhi)
      · exact hActualContactArcOnLowerBoundaryIsEndpoint e t (actualGlobalContactArcs e t).1 (Prod.ext rfl hy)
      · exact hActualContactArcOnUpperBoundaryIsEndpoint e t (actualGlobalContactArcs e t).1 (Prod.ext rfl hy)
  have hActualOriginalOuterContactPathSupportOnlyEndpoints
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (v : actualContactVertices)
      (hv : v.val.1=0 ∨ v.val.1=1 ∨ v.val.2=0 ∨ v.val.2=1)
      (hsupport : Sum.inl v∈P.support) : v=w ∨ v=z := by
    as_aux_lemma =>
      have hdegree : actualZeroGraph.degree (Sum.inl v)=1 := by
        rcases hv with hv | hv | hv | hv
        · exact hActualEveryInitialContactVertexDegreeOne v hv
        · have he : v.val=(1,v.val.2) := Prod.ext hv rfl
          have hm := hActualContactVerticesImage v
          rw [he] at hm
          exact False.elim (hActualFiniteConeSweepTopAvoids v.val.2 hm)
        · exact hActualEveryLowerSeamContactVertexDegreeOne v hv
        · exact hActualEveryUpperSeamContactVertexDegreeOne v hv
      have he := CurveComplex.LocalSurgery.actual_degree_one_path_support_is_endpoint
        actualZeroGraph P hP hsupport hdegree
      exact he.elim (fun h => Or.inl (Sum.inl.inj h)) (fun h => Or.inr (Sum.inl.inj h))
  have hActualOuterContactPlanarCarrierOnlyEndpoints
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (W : List (actualNegativeFaceIntervals × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
        (actualPlanarVertexPosition (Sum.inl z)))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (v : actualContactVertices) (hv : v.val.1=0 ∨ v.val.1=1 ∨ v.val.2=0 ∨ v.val.2=1)
      (hcarrier : actualPlanarVertexPosition (Sum.inl v)∈Graph.edgesCover actualPlanarDrawing W) :
      v=w ∨ v=z := by
    as_aux_lemma =>
      obtain ⟨e,he,hve⟩ := Graph.mem_edgesCover_iff.mp hcarrier
      have hvvertex : actualPlanarVertexPosition (Sum.inl v)∈actualPlanarGraph.vertexSet :=
        ⟨Sum.inl v,rfl⟩
      have hend := actualPlanarDrawingIsDrawing.vertex_mem_edgeArc
        (hActualPlanarSubedgeLink e) hvvertex hve
      have hinc : actualPlanarGraph.Inc e (actualPlanarVertexPosition (Sum.inl v)) := by
        rcases hend with h | h
        · exact h ▸ (hActualPlanarSubedgeLink e).inc_left
        · exact h ▸ (hActualPlanarSubedgeLink e).inc_right
      have hwalk : actualPlanarVertexPosition (Sum.inl v)∈
          actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W :=
        Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices he hinc)
      rw [hvertices] at hwalk
      obtain ⟨r,hr,heq⟩ := hwalk
      have hrv : r=Sum.inl v := actualPlanarVertexPositionInjective heq
      exact hActualOriginalOuterContactPathSupportOnlyEndpoints P hP v hv (hrv ▸ hr)
  have hActualEmbeddedSquareContactPathMeetsOuterBoundaryOnlyAtEnds
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (W : List (actualNegativeFaceIntervals × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
        (actualPlanarVertexPosition (Sum.inl z)))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (q : Path w.val z.val) (hq : IsEmbedding q)
      (himage : actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W)
      (t : Interval) (ht : (q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      have hcarrier : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
        himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
      obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hcarrier
      obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
      have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
      have hrend : r=0 ∨ r=1 := hActualGlobalContactArcOnOuterBoundaryIsEndpoint e.1 r (by
        rw [hqr]
        exact ht)
      have hv : q t∈actualContactVertices := by
        rcases hrend with rfl | rfl
        · exact hqr ▸ hActualContactArcStartInVertices e.1
        · exact hqr ▸ hActualContactArcEndInVertices e.1
      let v : actualContactVertices := ⟨q t,hv⟩
      have hvposition : actualPlanarVertexPosition (Sum.inl v)=actualParameterSquarePlane (q t) := rfl
      have hend : v=w ∨ v=z := hActualOuterContactPlanarCarrierOnlyEndpoints P hP W hW
        hvertices v ht (hvposition.symm ▸ hcarrier)
      rcases hend with h | h
      · have hpoint : q t=w.val := congrArg Subtype.val h
        exact Or.inl (hq.injective (hpoint.trans q.source.symm))
      · have hpoint : q t=z.val := congrArg Subtype.val h
        exact Or.inr (hq.injective (hpoint.trans q.target.symm))
  have hActualSpecifiedCrossingProducesOuterProperOriginalContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          ∃ W : List (actualNegativeFaceIntervals × Fin 3),W≠[] ∧
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W (actualPlanarVertexPosition (Sum.inl z)) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=actualPlanarVertexPosition '' {r | r∈P.support} ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧ actualParameterSquarePlane '' range q=Graph.edgesCover actualPlanarDrawing W ∧ (∀ t,(q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → t=0 ∨ t=1) ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,hArc⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 r,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqr]
        exact hActualGlobalContactArcImage e.1 r
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact
        (fun t => hActualFiniteConeSweepMarks (q t))
      exact ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,q,hq,himage,
        fun t ht => hActualEmbeddedSquareContactPathMeetsOuterBoundaryOnlyAtEnds P hP W hW
          hvertices q hq himage t ht,κ,hκ,hinside⟩
  have hActualMarkedArcInteriorParametersStraightenInSelectedCarrier
      (d : EssentialMarkedArc M) (κ : C(Interval,Interval)) (hκ : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) (u : S) :
      ∃ (hx : d.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : d.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨d.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=d.val.map (κ t)) ∧
        (∀ t,(β t : S)=d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let J := Set.Ioo (0 : ℝ) 1
      let x : J := ⟨(κ 0).val,hκ 0⟩
      let y : J := ⟨(κ 1).val,hκ 1⟩
      let r : Path x y := {
        toFun := fun t => ⟨(κ t).val,hκ t⟩
        continuous_toFun := (continuous_subtype_val.comp κ.continuous).subtype_mk hκ
        source' := rfl
        target' := rfl }
      have hseg (t : Interval) : (actualIntervalSegment (κ 0) (κ 1) t).val∈J := by
        have hx₀ : 0<(κ 0).val := (hκ 0).1
        have hx₁ : (κ 0).val<1 := (hκ 0).2
        have hy₀ : 0<(κ 1).val := (hκ 1).1
        have hy₁ : (κ 1).val<1 := (hκ 1).2
        change 0<(1-t.val)*(κ 0).val+t.val*(κ 1).val ∧
          (1-t.val)*(κ 0).val+t.val*(κ 1).val<1
        simpa only [smul_eq_mul,Set.mem_Ioo] using (convex_Ioo (0 : ℝ) 1) (show (κ 0).val∈Set.Ioo (0 : ℝ) 1 from ⟨hx₀,hx₁⟩) (show (κ 1).val∈Set.Ioo (0 : ℝ) 1 from ⟨hy₀,hy₁⟩) (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
      let s : Path x y := {
        toFun := fun t => ⟨(actualIntervalSegment (κ 0) (κ 1) t).val,hseg t⟩
        continuous_toFun := (continuous_subtype_val.comp (actualIntervalSegment (κ 0) (κ 1)).continuous).subtype_mk hseg
        source' := by apply Subtype.ext;change (1-(0 : ℝ))*(κ 0).val+0*(κ 1).val=(κ 0).val;ring
        target' := by apply Subtype.ext;change (1-(1 : ℝ))*(κ 0).val+1*(κ 1).val=(κ 1).val;ring }
      let inc : C(J,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2.le⟩,
        continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1.le,t.property.2.le⟩)⟩
      have havoid (t : J) : d.val.map (inc t)∉(M.cover.branch : Set S) := by
        intro hm
        rcases d.val.marked_only_at_ends (inc t) hm with he | he
        · have hv := congrArg Subtype.val he
          exact (ne_of_gt t.property.1) hv
        · have hv := congrArg Subtype.val he
          exact (ne_of_lt t.property.2) hv
      let T := ((M.cover.branch : Set S)\{u})ᶜ
      have htarget (t : J) : d.val.map (inc t)∈T := by
        intro hm
        exact havoid t hm.1
      let A : C(J,T) := ⟨fun t => ⟨d.val.map (inc t),htarget t⟩,
        (d.val.continuous.comp inc.continuous).subtype_mk htarget⟩
      letI : ContractibleSpace J := (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨x,x.property⟩
      have hhom : r.Homotopic s := SimplyConnectedSpace.paths_homotopic r s
      exact ⟨htarget x,htarget y,r.map A.continuous,s.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualOriginalBottomBoundaryParametersStraightenInSelectedCarrier
      (x y : Interval) (u : S) :
      let ρ := actualCentralParameter.comp (actualIntervalSegment x y)
      ∃ (hx : b.val.map (ρ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : b.val.map (ρ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨b.val.map (ρ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨b.val.map (ρ 1),hy⟩),
        (∀ t,(α t : S)=b.val.map (actualCentralParameter (actualIntervalSegment x y t))) ∧
        (∀ t,(β t : S)=b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let ρ := actualCentralParameter.comp (actualIntervalSegment x y)
      have hρ (t : Interval) : ρ t∈Set.Ioo (0 : Interval) 1 :=
        hActualCentralParameterInterior (actualIntervalSegment x y t)
      exact hActualMarkedArcInteriorParametersStraightenInSelectedCarrier b ρ hρ u
  let actualCentralStripDomain : Set (Interval × Interval) := actualCentralSweep ⁻¹' bandOpen
  have hActualCentralStripDomainOpen : IsOpen actualCentralStripDomain :=
    hbandOpen.preimage actualCentralSweep.continuous
  have hActualCentralContactsInStrip : actualCentralSweep ⁻¹' a.val.image ⊆ actualCentralStripDomain := by
    intro z hz
    exact haxisInBand ⟨hz,hActualCentralSweepMarks z⟩
  let actualCentralStripLift : C(actualCentralStripDomain,Set.range B) := {
    toFun := fun z => ⟨actualCentralSweep z.val,hbandSubset z.property⟩
    continuous_toFun := by fun_prop }
  let actualCentralTransverseCoordinate : C(actualCentralStripDomain,ℝ) :=
    transverse.comp actualCentralStripLift
  have hActualCentralCoordinateZero (z : actualCentralStripDomain) :
      actualCentralTransverseCoordinate z=0 ↔ actualCentralSweep z.val ∈ a.val.image :=
    htransverseAxis (actualCentralStripLift z)
  have hActualCentralCoordinateTop (z : actualCentralStripDomain) (hz : z.val.1=1) :
      actualCentralTransverseCoordinate z≠0 := by
    as_aux_lemma =>
      intro hzero
      have hhit := (hActualCentralCoordinateZero z).mp hzero
      have he : z.val=(1,z.val.2) := Prod.ext hz rfl
      rw [he] at hhit
      exact hActualCentralSweepTerminal z.val.2 hhit
  have hActualOriginalBottomToBottomSubpathsPuncturedHomotopic
      (u : S) {x y : Interval × Interval} (q : Path x y)
      (hx₀ : x.1=0) (hy₀ : y.1=0)
      (κ : C(Interval,Interval)) (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t))
      (hinside : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) :
      ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨a.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        (∀ t,(β t : S)=b.val.map (actualIntervalSegment
          (actualCentralParameter x.2) (actualCentralParameter y.2) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      obtain ⟨hx,hy,A₀,A₁,hA₀,hA₁,hA⟩ :=
        hActualMarkedArcInteriorParametersStraightenInSelectedCarrier a κ hinside u
      obtain ⟨hx',hy',Q₀,Q₁,hQ₀,hQ₁,hQ⟩ :=
        hActualBottomEndpointsContactPathHomotopicToOriginalBoundary u q hx₀ hy₀
      have ex : (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=⟨actualFiniteConeSweep x,hx'⟩ :=
        Subtype.ext (by simpa only [q.source] using hκ 0)
      have ey : (⟨a.val.map (κ 1),hy⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=⟨actualFiniteConeSweep y,hy'⟩ :=
        Subtype.ext (by simpa only [q.target] using hκ 1)
      have hAQ : A₀=Q₀.cast ex ey := by
        ext t
        exact (hA₀ t).trans ((hκ t).trans (hQ₀ t).symm)
      obtain ⟨hx'',hy'',B₀,B₁,hB₀,hB₁,hB⟩ :=
        hActualOriginalBottomBoundaryParametersStraightenInSelectedCarrier x.2 y.2 u
      have exb : (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=
          ⟨b.val.map ((actualCentralParameter.comp (actualIntervalSegment x.2 y.2)) 0),hx''⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val ex).trans ((congrArg Subtype.val Q₁.source).symm.trans (hQ₁ 0))
      have eyb : (⟨a.val.map (κ 1),hy⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=
          ⟨b.val.map ((actualCentralParameter.comp (actualIntervalSegment x.2 y.2)) 1),hy''⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val ey).trans ((congrArg Subtype.val Q₁.target).symm.trans (hQ₁ 1))
      have hQB : Q₁.cast ex ey=B₀.cast exb eyb := by
        ext t
        exact (hQ₁ t).trans (hB₀ t).symm
      have hfirst : A₁.Homotopic (Q₁.cast ex ey) := by
        exact hA.symm.trans (hAQ ▸ hQ.pathCast ex ey)
      have hlast : A₁.Homotopic (B₁.cast exb eyb) :=
        hfirst.trans (hQB ▸ hB.pathCast exb eyb)
      refine ⟨hx,hy,A₁,B₁.cast exb eyb,hA₁,?_,hlast⟩
      have hs₀ : actualIntervalSegment x.2 y.2 0=x.2 := by
        apply Subtype.ext
        change (1-(0 : ℝ))*x.2.val+0*y.2.val=x.2.val
        ring
      have hs₁ : actualIntervalSegment x.2 y.2 1=y.2 := by
        apply Subtype.ext
        change (1-(1 : ℝ))*x.2.val+1*y.2.val=y.2.val
        ring
      intro t
      change (B₁ t : S)=_
      simpa only [ContinuousMap.comp_apply,hs₀,hs₁] using hB₁ t
  let actualSourceFaceRawHeight (P : actualActiveContactCells × Fin 4) : C(Interval,ℝ) :=
    ⟨fun t => (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2 t)).val.1,by fun_prop⟩
  let actualSourceFaceHeight (P : actualActiveContactCells × Fin 4) : C(Interval,ℝ) :=
    ⟨fun t => actualSourceFaceRawHeight P t/(actualCellCenters P.1.val).val.1,by fun_prop⟩
  have hActualSourceMeshMidpointInterior (P : actualActiveContactCells × Fin 4)
      (j : Fin (actualFaceContactSize P+1)) :
      actualIntervalMidpoint (actualFaceContactMesh P j.castSucc) (actualFaceContactMesh P j.succ)∈
        Set.Ioo (actualFaceContactMesh P j.castSucc) (actualFaceContactMesh P j.succ) := by
    as_aux_lemma =>
      have hstep : (actualFaceContactMesh P j.castSucc).val<(actualFaceContactMesh P j.succ).val :=
        actualFaceContactMono P (by change j.val<j.val+1;omega)
      change (actualFaceContactMesh P j.castSucc).val<
        ((actualFaceContactMesh P j.castSucc).val+(actualFaceContactMesh P j.succ).val)/2 ∧
        ((actualFaceContactMesh P j.castSucc).val+(actualFaceContactMesh P j.succ).val)/2<
          (actualFaceContactMesh P j.succ).val
      constructor <;> linarith only [hstep]
  have hActualSourceFaceHeightNoZero (P : actualActiveContactCells × Fin 4)
      (j : Fin (actualFaceContactSize P+1)) (t : Interval)
      (ht0 : actualFaceContactMesh P j.castSucc<t) (ht1 : t<actualFaceContactMesh P j.succ) :
      actualSourceFaceHeight P t≠0 :=
    div_ne_zero (actualFaceContactNoZero P j t ht0 ht1)
      ((hActualCellCenterAxisOff P.1.val).resolve_left P.1.property)
  let actualSourceCellEndpointIncidence (k : actualActiveContactCells) (x : Interval × Interval)
      (t : Interval) := Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
        f.1.1=k ∧ actualLocalContactArcs f t=x)
  have hActualLocalContactArcOpenRadialFaceAndOrientation (f : actualNegativeFaceIntervals)
      (i : Fin 4) (t u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (ht : t=0 ∨ t=1)
      (hle : (actualCellBoundaryLoops f.1.1.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters f.1.1.val).val.1≤0)
      (hp : actualLocalContactArcs f t=actualFaceContactRadial (f.1.1,i) ⟨actualBoundaryFace i u,hle⟩) :
      f.1.2=i ∧ (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
        actualFaceContactMesh f.1 f.2.val.succ=u) ∧
        (t=0 → actualFaceContactMesh f.1 f.2.val.castSucc=u) ∧
        (t=1 → actualFaceContactMesh f.1 f.2.val.succ=u) := by
    as_aux_lemma =>
      let k := f.1.1
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
        ⟨actualBoundaryFace i u,hle⟩
      have hqroot : actualCompleteCellRadial k z0=actualFaceContactRadial (k,i) z0 :=
        hActualCompleteRadialMatchesFace k i z0
      have faceAtRoot (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) (r : Interval)
          (hz : z.val=actualBoundaryFace f.1.2 r)
          (hq : actualFaceContactRadial f.1 z=actualFaceContactRadial (k,i) z0) : f.1.2=i ∧ r=u := by
        have hqz : actualCompleteCellRadial k z=actualFaceContactRadial (k,i) z0 :=
          (hActualCompleteRadialMatchesFace k f.1.2 z).trans hq
        have hzz : z=z0 := hActualCompleteCellRadialInjective k (hqz.trans hqroot.symm)
        have he : actualBoundaryFace f.1.2 r=actualBoundaryFace i u :=
          hz.symm.trans (congrArg Subtype.val hzz)
        have hfi : i=f.1.2 := actualBoundaryFaceOpenUnique i f.1.2 u r hu he.symm
        have hr : r=u := hActualBoundaryFaceInjective i (by simpa only [←hfi] using he)
        exact ⟨hfi.symm,hr⟩
      rcases ht with rfl | rfl
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcStart f)
          (actualFaceContactMesh f.1 f.2.val.castSucc) (hActualLocalContactArcStartFace f)
          ((hActualLocalContactArcStart f).symm.trans hp)
        refine ⟨hf,Or.inl hr,(fun _ => hr),?_⟩
        intro hbad
        have h01 : (0 : Interval)≠1 := fun he => zero_ne_one (congrArg Subtype.val he)
        exact False.elim (h01 hbad)
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcEnd f)
          (actualFaceContactMesh f.1 f.2.val.succ) (hActualLocalContactArcEndFace f)
          ((hActualLocalContactArcEnd f).symm.trans hp)
        refine ⟨hf,Or.inr hr,?_,(fun _ => hr)⟩
        intro hbad
        have h10 : (1 : Interval)≠0 := fun he => one_ne_zero (congrArg Subtype.val he)
        exact False.elim (h10 hbad)
  have hActualFaceRadialSourceIncidence (P : actualActiveContactCells × Fin 4)
      (u : Interval)
      (hle : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2 u)).val.1/
        (actualCellCenters P.1.val).val.1≤0)
      (j : Fin (actualFaceContactSize P+1))
      (hneg : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2
        (actualIntervalMidpoint (actualFaceContactMesh P j.castSucc) (actualFaceContactMesh P j.succ)))).val.1/
        (actualCellCenters P.1.val).val.1<0) :
      actualLocalContactArcs ⟨P,⟨j,hneg⟩⟩ 0=
        actualFaceContactRadial P ⟨actualBoundaryFace P.2 u,hle⟩ ↔
        actualFaceContactMesh P j.castSucc=u := by
    as_aux_lemma =>
      let f : actualNegativeFaceIntervals := ⟨P,⟨j,hneg⟩⟩
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops P.1.val z).val.1/(actualCellCenters P.1.val).val.1≤0} :=
        ⟨actualBoundaryFace P.2 u,hle⟩
      constructor
      · intro hp
        have he : actualCompleteCellRadial P.1 (actualLocalContactArcStart f)=actualCompleteCellRadial P.1 z0 := by
          exact (hActualCompleteRadialMatchesFace P.1 P.2 (actualLocalContactArcStart f)).trans
            ((hActualLocalContactArcStart f).symm.trans (hp.trans (hActualCompleteRadialMatchesFace P.1 P.2 z0).symm))
        have hz := congrArg Subtype.val (hActualCompleteCellRadialInjective P.1 he)
        have hface := (hActualLocalContactArcStartFace f).symm.trans hz
        exact hActualBoundaryFaceInjective P.2 hface
      · intro hj
        have hz : actualLocalContactArcStart f=z0 := by
          apply Subtype.ext
          exact (hActualLocalContactArcStartFace f).trans (congrArg (actualBoundaryFace P.2) hj)
        exact (hActualLocalContactArcStart f).trans (congrArg (actualFaceContactRadial P) hz)
  have hActualFaceRadialTargetIncidence (P : actualActiveContactCells × Fin 4)
      (u : Interval)
      (hle : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2 u)).val.1/
        (actualCellCenters P.1.val).val.1≤0)
      (j : Fin (actualFaceContactSize P+1))
      (hneg : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2
        (actualIntervalMidpoint (actualFaceContactMesh P j.castSucc) (actualFaceContactMesh P j.succ)))).val.1/
        (actualCellCenters P.1.val).val.1<0) :
      actualLocalContactArcs ⟨P,⟨j,hneg⟩⟩ 1=
        actualFaceContactRadial P ⟨actualBoundaryFace P.2 u,hle⟩ ↔
        actualFaceContactMesh P j.succ=u := by
    as_aux_lemma =>
      let f : actualNegativeFaceIntervals := ⟨P,⟨j,hneg⟩⟩
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops P.1.val z).val.1/(actualCellCenters P.1.val).val.1≤0} :=
        ⟨actualBoundaryFace P.2 u,hle⟩
      constructor
      · intro hp
        have he : actualCompleteCellRadial P.1 (actualLocalContactArcEnd f)=actualCompleteCellRadial P.1 z0 := by
          exact (hActualCompleteRadialMatchesFace P.1 P.2 (actualLocalContactArcEnd f)).trans
            ((hActualLocalContactArcEnd f).symm.trans (hp.trans (hActualCompleteRadialMatchesFace P.1 P.2 z0).symm))
        have hz := congrArg Subtype.val (hActualCompleteCellRadialInjective P.1 he)
        have hface := (hActualLocalContactArcEndFace f).symm.trans hz
        exact hActualBoundaryFaceInjective P.2 hface
      · intro hj
        have hz : actualLocalContactArcEnd f=z0 := by
          apply Subtype.ext
          exact (hActualLocalContactArcEndFace f).trans (congrArg (actualBoundaryFace P.2) hj)
        exact (hActualLocalContactArcEnd f).trans (congrArg (actualFaceContactRadial P) hz)
  have hActualOpenRadialSourceFiber (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      Nonempty
        ({f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 0=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} ≃
        {j : Fin (actualFaceContactSize (k,i)+1) |
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.castSucc=u}) := by
    as_aux_lemma =>
      let toIndex := fun f : {f : actualNegativeFaceIntervals | f.1.1=k ∧
            actualLocalContactArcs f 0=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} => by
        rcases f with ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRadialFaceAndOrientation ⟨(k,j),r⟩ i 0 u hu
          (Or.inl rfl) hle hp).1
        change j=i at hj
        subst j
        exact (⟨r.val,r.property,(hActualFaceRadialSourceIncidence (k,i) u hle r.val r.property).mp hp⟩ :
          {j : Fin (actualFaceContactSize (k,i)+1) |
            actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
            actualFaceContactMesh (k,i) j.castSucc=u})
      refine ⟨{
        toFun := toIndex
        invFun := fun j =>
        ⟨⟨(k,i),⟨j.val,j.property.1⟩⟩,rfl,
          (hActualFaceRadialSourceIncidence (k,i) u hle j.val j.property.1).mpr j.property.2⟩
        left_inv := ?_
        right_inv := ?_}⟩
      · rintro ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRadialFaceAndOrientation ⟨(k,j),r⟩ i 0 u hu
          (Or.inl rfl) hle hp).1
        change j=i at hj
        subst j
        rfl
      · intro j
        rfl
  have hActualOpenRadialTargetFiber (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      Nonempty
        ({f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 1=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} ≃
        {j : Fin (actualFaceContactSize (k,i)+1) |
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.succ=u}) := by
    as_aux_lemma =>
      let toIndex := fun f : {f : actualNegativeFaceIntervals | f.1.1=k ∧
            actualLocalContactArcs f 1=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} => by
        rcases f with ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRadialFaceAndOrientation ⟨(k,j),r⟩ i 1 u hu
          (Or.inr rfl) hle hp).1
        change j=i at hj
        subst j
        exact (⟨r.val,r.property,(hActualFaceRadialTargetIncidence (k,i) u hle r.val r.property).mp hp⟩ :
          {j : Fin (actualFaceContactSize (k,i)+1) |
            actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
            actualFaceContactMesh (k,i) j.succ=u})
      refine ⟨{
        toFun := toIndex
        invFun := fun j =>
        ⟨⟨(k,i),⟨j.val,j.property.1⟩⟩,rfl,
          (hActualFaceRadialTargetIncidence (k,i) u hle j.val j.property.1).mpr j.property.2⟩
        left_inv := ?_
        right_inv := ?_}⟩
      · rintro ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRadialFaceAndOrientation ⟨(k,j),r⟩ i 1 u hu
          (Or.inr rfl) hle hp).1
        change j=i at hj
        subst j
        rfl
      · intro j
        rfl
  have hActualOpenRadialCellSourceCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      (actualSourceCellEndpointIncidence k
        (actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩) 0).card=
      (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.castSucc=u)).card := by
    calc
      _ = Fintype.card {f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 0=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = _ := (Fintype.card_congr (Classical.choice (hActualOpenRadialSourceFiber k i u hu hle))).trans
        (Fintype.card_subtype _)
  have hActualOpenRadialCellTargetCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      (actualSourceCellEndpointIncidence k
        (actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩) 1).card=
      (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.succ=u)).card := by
    calc
      _ = Fintype.card {f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 1=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = _ := (Fintype.card_congr (Classical.choice (hActualOpenRadialTargetFiber k i u hu hle))).trans
        (Fintype.card_subtype _)
  have hActualInternalNegativeRadialCellEndpointCountTwo
      (k : actualActiveContactCells) (i : Fin 4)
      (q : Fin (actualFaceContactSize (k,i)+2))
      (hq₀ : q≠0) (hq₁ : q≠Fin.last (actualFaceContactSize (k,i)+1))
      (hu : actualFaceContactMesh (k,i) q∈Set.Ioo (0 : Interval) 1)
      (hle : (actualCellBoundaryLoops k.val
        (actualBoundaryFace i (actualFaceContactMesh (k,i) q))).val.1/
        (actualCellCenters k.val).val.1≤0)
      (hneg : actualSourceFaceHeight (k,i) (actualFaceContactMesh (k,i) q)<0) :
      (actualSourceCellEndpointIncidence k
        (actualFaceContactRadial (k,i)
          ⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩) 0).card+
      (actualSourceCellEndpointIncidence k
        (actualFaceContactRadial (k,i)
          ⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩) 1).card=2 := by
    as_aux_lemma =>
      rw [hActualOpenRadialCellSourceCount k i _ hu hle,
        hActualOpenRadialCellTargetCount k i _ hu hle]
      calc
        _ = (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          (actualFaceContactMesh (k,i) j.castSucc=actualFaceContactMesh (k,i) q ∨
            actualFaceContactMesh (k,i) j.succ=actualFaceContactMesh (k,i) q))).card :=
          CurveComplex.LocalSurgery.actualMeshSourceTargetCardAdd (actualFaceContactSize (k,i))
            (actualFaceContactMesh (k,i)) (actualFaceContactMono (k,i))
            (fun j => actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0)
            (actualFaceContactMesh (k,i) q)
        _ = 2 := CurveComplex.LocalSurgery.actualNegativeInternalMeshNodeIncidenceTwo
          (actualFaceContactSize (k,i)) (actualFaceContactMesh (k,i))
          (actualFaceContactMono (k,i)) (actualSourceFaceHeight (k,i))
          (hActualSourceMeshMidpointInterior (k,i)) (hActualSourceFaceHeightNoZero (k,i)) q hq₀ hq₁ hneg
  have hActualContactArcThroughCellInteriorCellUnique (f : actualNegativeFaceIntervals)
      (t : Interval) (k : actualActiveContactCells) (z : Interval × Interval)
      (hz : z.1∈Set.Ioo (0 : Interval) 1 ∧ z.2∈Set.Ioo (0 : Interval) 1)
      (hp : actualGlobalContactArcs f t=actualAffineCells k.val z) : f.1.1=k := by
    as_aux_lemma =>
      have hin : (actualAffineCells k.val z).1∈Set.Ioo
          (actualContactGridParameter k.val.1.castSucc) (actualContactGridParameter k.val.1.succ) ∧
          (actualAffineCells k.val z).2∈Set.Ioo
          (actualContactGridParameter k.val.2.castSucc) (actualContactGridParameter k.val.2.succ) := by
        rw [hActualAffineCellFormula]
        exact ⟨actualIntervalSegmentInterior _ _ _ (hActualContactGridStep k.val.1) hz.1,
          actualIntervalSegmentInterior _ _ _ (hActualContactGridStep k.val.2) hz.2⟩
      have hclosed := hActualGlobalContactArcClosedCell f t
      rw [hp] at hclosed
      exact Subtype.ext (Prod.ext
        (hActualGridOpenClosedUnique k.val.1 f.1.1.val.1 _ hin.1 hclosed.1).symm
        (hActualGridOpenClosedUnique k.val.2 f.1.1.val.2 _ hin.2 hclosed.2).symm)
  have hActualNegativeRadialContactCellUnique (f : actualNegativeFaceIntervals)
      (t : Interval) (k : actualActiveContactCells) (i : Fin 4)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0})
      (hneg : (actualCellBoundaryLoops k.val z.val).val.1/(actualCellCenters k.val).val.1<0)
      (hp : actualGlobalContactArcs f t=actualAffineCells k.val (actualFaceContactRadial (k,i) z)) :
      f.1.1=k := by
    as_aux_lemma =>
      obtain ⟨r,hr,hformula⟩ := actualFaceContactRadialFormula (k,i) z
      have hpoint : (actualFaceContactRadial (k,i) z).1∈Set.Ioo (0 : Interval) 1 ∧
          (actualFaceContactRadial (k,i) z).2∈Set.Ioo (0 : Interval) 1 := by
        rw [hr]
        exact actualNegativeRadialPointInterior z.val _ hneg r hformula
      exact hActualContactArcThroughCellInteriorCellUnique f t k _ hpoint hp
  have hActualGlobalLocalCellEndpointHit (k : actualActiveContactCells)
      (f : actualNegativeFaceIntervals) (t : Interval) (x : Interval × Interval)
      (hf : f.1.1=k) :
      actualGlobalContactArcs f t=actualAffineCells k.val x ↔ actualLocalContactArcs f t=x := by
    as_aux_lemma =>
      change actualAffineCells f.1.1.val (actualLocalContactArcs f t)=actualAffineCells k.val x ↔ _
      rw [hf]
      exact (hActualAffineCellEmbedding k.val).injective.eq_iff
  have hActualGlobalCellEndpointCountAsLocal (k : actualActiveContactCells)
      (t : Interval) (x : Interval × Interval) :
      (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
        actualGlobalContactArcs f t=actualAffineCells k.val x ∧ f.1.1=k)).card=
        (actualSourceCellEndpointIncidence k x t).card := by
    as_aux_lemma =>
      congr 1
      ext f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,actualSourceCellEndpointIncidence]
      constructor
      · rintro ⟨hh,hf⟩
        exact ⟨hf,(hActualGlobalLocalCellEndpointHit k f t x hf).mp hh⟩
      · rintro ⟨hf,hh⟩
        exact ⟨(hActualGlobalLocalCellEndpointHit k f t x hf).mpr hh,hf⟩
  have hActualGraphEndpointDegreeAsGlobalArcCounts (w : actualContactVertices) :
      actualZeroGraph.degree (Sum.inl w)=
      (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f 0=w.val)).card+
      (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f 1=w.val)).card := by
    as_aux_lemma =>
      rw [zeroEndpointDegreeExact]
      congr 1
      · congr 1
        ext f
        simp only [leftIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hf
          exact (congrArg Subtype.val (Sum.inl.inj hf)).symm
        · intro hf
          apply congrArg Sum.inl
          exact Subtype.ext hf.symm
      · congr 1
        ext f
        simp only [rightIncidentEdges,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hf
          exact (congrArg Subtype.val (Sum.inl.inj hf)).symm
        · intro hf
          apply congrArg Sum.inl
          exact Subtype.ext hf.symm
  have hActualInternalNegativeRadialGraphVertexDegreeTwo
      (k : actualActiveContactCells) (i : Fin 4)
      (q : Fin (actualFaceContactSize (k,i)+2))
      (hq₀ : q≠0) (hq₁ : q≠Fin.last (actualFaceContactSize (k,i)+1))
      (hu : actualFaceContactMesh (k,i) q∈Set.Ioo (0 : Interval) 1)
      (hle : (actualCellBoundaryLoops k.val
        (actualBoundaryFace i (actualFaceContactMesh (k,i) q))).val.1/
        (actualCellCenters k.val).val.1≤0)
      (hneg : actualSourceFaceHeight (k,i) (actualFaceContactMesh (k,i) q)<0)
      (w : actualContactVertices)
      (hw : w.val=actualAffineCells k.val (actualFaceContactRadial (k,i)
        ⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩)) :
      actualZeroGraph.degree (Sum.inl w)=2 := by
    as_aux_lemma =>
      let z : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
        ⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩
      let x := actualFaceContactRadial (k,i) z
      have hneg' : (actualCellBoundaryLoops k.val z.val).val.1/
          (actualCellCenters k.val).val.1<0 := hneg
      have hcount (t : Interval) :
          (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
            actualGlobalContactArcs f t=actualAffineCells k.val x)).card=
          (actualSourceCellEndpointIncidence k x t).card := by
        rw [←hActualGlobalCellEndpointCountAsLocal k t x]
        congr 1
        ext f
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hf
          exact ⟨hf,hActualNegativeRadialContactCellUnique f t k i z hneg' hf⟩
        · exact And.left
      rw [hActualGraphEndpointDegreeAsGlobalArcCounts w,hw]
      change (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
        actualGlobalContactArcs f 0=actualAffineCells k.val x)).card+
        (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
          actualGlobalContactArcs f 1=actualAffineCells k.val x)).card=2
      rw [hcount 0,hcount 1]
      exact hActualInternalNegativeRadialCellEndpointCountTwo k i q hq₀ hq₁ hu hle hneg
  have hActualNondegenerateOriginalBottomBIntervalSubpathEmbedding
      (x y : Interval) (hxy : x≠y) :
      IsEmbedding (fun t : Interval => b.val.map (actualIntervalSegment
        (actualCentralParameter x) (actualCentralParameter y) t)) := by
    have hp : actualCentralParameter x≠actualCentralParameter y :=
      fun h => hxy (hActualCentralParameterInjective h)
    exact (NonLoopArc.isEmbedding (⟨b.val,hbne⟩ : NonLoopArc M)).comp
      (((actualIntervalSegment (actualCentralParameter x) (actualCentralParameter y)).continuous.isClosedEmbedding
        (actualIntervalSegmentInjectiveOfNe _ _ hp)).isEmbedding)
  have hActualOriginalBottomContactSubpathPairBothEmbedded
      (w z : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0) (hzw : z≠w)
      (q : Path w.val z.val) (κ : C(Interval,Interval))
      (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) :
      IsEmbedding (fun t : Interval => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
      IsEmbedding (fun t : Interval => b.val.map (actualIntervalSegment
        (actualCentralParameter w.val.2) (actualCentralParameter z.val.2) t)) := by
    have hcoord : w.val.2≠z.val.2 := by
      intro he
      apply hzw
      apply Subtype.ext
      exact Prod.ext (hz.trans hw.symm) he.symm
    exact ⟨hActualNondegenerateOldArcIntervalSubpathEmbedding _ _
      (hActualBottomContactOriginalOldArcParametersDistinct w z hw hz hzw q κ hκ),
      hActualNondegenerateOriginalBottomBIntervalSubpathEmbedding _ _ hcoord⟩
  have hActualOddContactVertexHasActualArcEndpoint
      (w : actualContactVertices) (hodd : Odd (actualZeroGraph.degree (Sum.inl w))) :
      ∃ e : actualNegativeFaceIntervals,actualGlobalContactArcs e 0=w.val ∨
        actualGlobalContactArcs e 1=w.val := by
    by_contra! hn
    have hzero₀ : (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
        actualGlobalContactArcs f 0=w.val))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact (hn f).1
    have hzero₁ : (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
        actualGlobalContactArcs f 1=w.val))=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact (hn f).2
    rw [hActualGraphEndpointDegreeAsGlobalArcCounts w,hzero₀,hzero₁] at hodd
    norm_num at hodd
  have actualMarkedSharedAxisChartsSameSide (p : S)
      (hp : p ∈ a.val.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
      (hpC : p ∈ C.source) (hpD : p ∈ D.source)
      (hC : ∀ x ∈ C.source, x ∈ a.val.image ↔ (C x).1 = 0)
      (hD : ∀ x ∈ D.source, x ∈ a.val.image ↔ (D x).1 = 0) :
      ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ C.source ∩ D.source ∧
        ∀ x ∈ U, ∀ y ∈ U, x ∉ a.val.image → y ∉ a.val.image →
          (((C x).1 < 0 ↔ (C y).1 < 0) ↔
            ((D x).1 < 0 ↔ (D y).1 < 0)) := by
    as_aux_lemma =>
      exact CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel.actualMarkedSharedAxisChartsSameSide M a p hp C D hpC hpD hC hD
  have actualMarkedSharedAxisTraceSameSectorSign
      (γ : C(Interval,S)) (u : Interval) (hu : u ∈ Set.Ioo (0 : Interval) 1)
      (hroot : γ u ∈ a.val.image) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
      (hpC : γ u ∈ C.source) (hpD : γ u ∈ D.source)
      (hC : ∀ x ∈ C.source, x ∈ a.val.image ↔ (C x).1 = 0)
      (hD : ∀ x ∈ D.source, x ∈ a.val.image ↔ (D x).1 = 0)
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
    as_aux_lemma =>
      exact CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel.actualMarkedSharedAxisTraceSameSectorSign M a γ u hu hroot C D hpC hpD hC hD g h c d hc hd hg hh x y sl sr X Y sL sR hxu huy hXu huY hsl hsr hsL hsR hgl hgr hhl hhr
  have actualMarkedSectorIndicatorsEven (x y X Y : ℝ)
      (hs : ((x<0 ↔ y<0) ↔ (X<0 ↔ Y<0))) :
      Even ((if x<0 then 1 else 0)+(if y<0 then 1 else 0)+
        (if X<0 then 1 else 0)+(if Y<0 then 1 else 0) : ℕ) := by
    as_aux_lemma =>
      by_cases hx : x<0 <;> by_cases hy : y<0 <;> by_cases hX : X<0 <;> by_cases hY : Y<0
      all_goals try (norm_num [hx,hy,hX,hY] at hs)
      all_goals norm_num [hx,hy,hX,hY]
  have actualMeshNegativeEndpointCard (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (negative : Fin (m+1) → Prop) (l r : Fin (m+1))
      (u : Interval) (hlu : mesh l.succ=u) (hru : mesh r.castSucc=u) :
      (Finset.univ.filter (fun j => negative j ∧
        (mesh j.castSucc=u ∨ mesh j.succ=u))).card =
        (if negative l then 1 else 0)+(if negative r then 1 else 0) := by
    as_aux_lemma =>
      exact CurveComplex.LocalSurgery.actualMeshNegativeEndpointCard m mesh hmono negative l r u hlu hru
  have actualMeshSourceTargetCardAdd (m : ℕ) (mesh : Fin (m+2) → Interval)
      (hmono : StrictMono mesh) (negative : Fin (m+1) → Prop) (u : Interval) :
      (Finset.univ.filter (fun j => negative j ∧ mesh j.castSucc=u)).card+
      (Finset.univ.filter (fun j => negative j ∧ mesh j.succ=u)).card=
      (Finset.univ.filter (fun j => negative j ∧ (mesh j.castSucc=u ∨ mesh j.succ=u))).card := by
    as_aux_lemma =>
      exact CurveComplex.LocalSurgery.actualMeshSourceTargetCardAdd m mesh hmono negative u
  have actualNegativeEndpointForcesInteriorSign (g : C(Interval,ℝ)) (x y s t : Interval)
      (hs : s∈Set.Ioo x y) (ht : t∈Set.Icc x y) (hneg : g t<0)
      (hn : ∀ z,x<z → z<y → g z≠0) : g s<0 := by
    as_aux_lemma =>
      exact CurveComplex.LocalSurgery.actualNegativeEndpointForcesInteriorSign g x y s t hs ht hneg hn
  have actualInteriorGridNodeClosedCells (n : ℕ) (grid : Fin (n+2) → Interval)
      (hmono : StrictMono grid) (i : Fin n) (k : Fin (n+1))
      (hleft : grid k.castSucc≤grid i.succ.castSucc)
      (hright : grid i.succ.castSucc≤grid k.succ) : k=i.castSucc ∨ k=i.succ := by
    as_aux_lemma =>
      have hl := hmono.le_iff_le.mp hleft
      have hr := hmono.le_iff_le.mp hright
      change k.val ≤ i.val+1 at hl
      change i.val+1 ≤ k.val+1 at hr
      by_cases he : k.val=i.val
      · exact Or.inl (Fin.ext he)
      · right
        apply Fin.ext
        change k.val=i.val+1
        have hlo : i.val ≤ k.val := Nat.le_of_succ_le_succ hr
        have hgt : i.val < k.val := lt_of_le_of_ne hlo (Ne.symm he)
        exact Nat.le_antisymm hl hgt
  have actualFiniteTwoLabelIncidenceCard (A B : Type) [Fintype A] [DecidableEq B]
      (label : A → B) (hit : A → Prop) (k l : B) (hkl : k≠l)
      (hcover : ∀ e,hit e → label e=k ∨ label e=l) :
      (Finset.univ.filter hit).card=
        (Finset.univ.filter (fun e => hit e ∧ label e=k)).card+
        (Finset.univ.filter (fun e => hit e ∧ label e=l)).card := by
    have hd : Disjoint (Finset.univ.filter (fun e => hit e ∧ label e=k))
        (Finset.univ.filter (fun e => hit e ∧ label e=l)) := by
      apply Finset.disjoint_left.mpr
      intro e hek hel
      exact hkl ((Finset.mem_filter.mp hek).2.2.symm.trans (Finset.mem_filter.mp hel).2.2)
    rw [←Finset.card_union_of_disjoint hd]
    congr 1
    ext e
    simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro he
      rcases hcover e he with hk | hl
      · exact Or.inl ⟨he,hk⟩
      · exact Or.inr ⟨he,hl⟩
    · rintro (⟨he,_⟩ | ⟨he,_⟩) <;> exact he
  let actualSourceNegativeIndicator (P : actualActiveContactCells × Fin 4)
      (j : Fin (actualFaceContactSize P+1)) : ℕ :=
    if actualSourceFaceHeight P (actualIntervalMidpoint (actualFaceContactMesh P j.castSucc)
      (actualFaceContactMesh P j.succ))<0 then 1 else 0
  have hActualBoundaryFaceOneCoordinates (t : Interval) :
      squareCoordinates ⟨(actualBoundaryFace 1 t).val,(actualBoundaryFace 1 t).property.le⟩=(1,t) := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change ((1 : ℝ)+1)/2=1
        norm_num
      · change (2*t.val-1+1)/2=t.val
        ring
  have hActualSourceFaceRightRawFormula (k : actualActiveContactCells) (t : Interval) :
      actualSourceFaceRawHeight (k,1) t=((actualContactGridCharts k.val) (actualCellRightEdge k.val t)).1 := by
    have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 1 t)
    rw [hActualBoundaryFaceOneCoordinates,(hActualConeCellBoundary k.val t).2.1] at hh
    exact (congrArg Prod.fst hh).symm
  have hActualSourceFaceLeftRawFormula (k : actualActiveContactCells) (t : Interval) :
      actualSourceFaceRawHeight (k,3) t=((actualContactGridCharts k.val) (actualCellLeftEdge k.val t)).1 := by
    have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 3 t)
    rw [hActualBoundaryFaceThreeCoordinates,(hActualConeCellBoundary k.val t).2.2.2] at hh
    exact (congrArg Prod.fst hh).symm
  have hActualVerticalCellSharedTrace (i : Fin actualContactGridSize) (j : Fin (actualContactGridSize+1))
      (t : Interval) : actualCellRightEdge (i.castSucc,j) t=actualCellLeftEdge (i.succ,j) t := by
    rfl
  have hActualLocalContactArcOpenRootFaceAndOrientation (f : actualNegativeFaceIntervals)
      (i : Fin 4) (t u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (ht : t=0 ∨ t=1)
      (hroot : (actualCellBoundaryLoops f.1.1.val (actualBoundaryFace i u)).val.1=0)
      (hp : actualLocalContactArcs f t=squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) :
      f.1.2=i ∧ (actualFaceContactMesh f.1 f.2.val.castSucc=u ∨
        actualFaceContactMesh f.1 f.2.val.succ=u) ∧
        (t=0 → actualFaceContactMesh f.1 f.2.val.castSucc=u) ∧
        (t=1 → actualFaceContactMesh f.1 f.2.val.succ=u) := by
    as_aux_lemma =>
      let k := f.1.1
      let z0 : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
        ⟨actualBoundaryFace i u,by
          change (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/(actualCellCenters k.val).val.1≤0
          rw [hroot]
          simp⟩
      have hqroot : actualCompleteCellRadial k z0=squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩ :=
        (hActualCompleteRadialMatchesFace k i z0).trans
          ((actualFaceContactBoundaryFix (k,i) z0 hroot).trans (rfl))
      have faceAtRoot (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
          (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0}) (r : Interval)
          (hz : z.val=actualBoundaryFace f.1.2 r)
          (hq : actualFaceContactRadial f.1 z=squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) : f.1.2=i ∧ r=u := by
        have hqz : actualCompleteCellRadial k z=squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩ :=
          (hActualCompleteRadialMatchesFace k f.1.2 z).trans hq
        have hzz : z=z0 := hActualCompleteCellRadialInjective k (hqz.trans hqroot.symm)
        have he : actualBoundaryFace f.1.2 r=actualBoundaryFace i u :=
          hz.symm.trans (congrArg Subtype.val hzz)
        have hfi : i=f.1.2 := actualBoundaryFaceOpenUnique i f.1.2 u r hu he.symm
        have hface : actualBoundaryFace i r=actualBoundaryFace i u := by
          have hright : actualBoundaryFace i u=actualBoundaryFace f.1.2 u := congrArg (fun q => actualBoundaryFace q u) hfi
          exact (congrArg (fun q => actualBoundaryFace q r) hfi).trans he
        have hr : r=u := hActualBoundaryFaceInjective i hface
        exact ⟨hfi.symm,hr⟩
      rcases ht with rfl | rfl
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcStart f)
          (actualFaceContactMesh f.1 f.2.val.castSucc) (hActualLocalContactArcStartFace f)
          ((hActualLocalContactArcStart f).symm.trans hp)
        refine ⟨hf,Or.inl hr,(fun _ => hr),?_⟩
        intro hbad
        have h01 : (0 : Interval)≠1 := fun he => zero_ne_one (congrArg Subtype.val he)
        exact False.elim (h01 hbad)
      · obtain ⟨hf,hr⟩ := faceAtRoot (actualLocalContactArcEnd f)
          (actualFaceContactMesh f.1 f.2.val.succ) (hActualLocalContactArcEndFace f)
          ((hActualLocalContactArcEnd f).symm.trans hp)
        refine ⟨hf,Or.inr hr,?_,(fun _ => hr)⟩
        intro hbad
        have h10 : (1 : Interval)≠0 := fun he => one_ne_zero (congrArg Subtype.val he)
        exact False.elim (h10 hbad)
  have hActualFaceRootSourceIncidence (P : actualActiveContactCells × Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2 u)).val.1=0)
      (j : Fin (actualFaceContactSize P+1))
      (hneg : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2
        (actualIntervalMidpoint (actualFaceContactMesh P j.castSucc) (actualFaceContactMesh P j.succ)))).val.1/
        (actualCellCenters P.1.val).val.1<0) :
      actualLocalContactArcs ⟨P,⟨j,hneg⟩⟩ 0=
        squareCoordinates ⟨(actualBoundaryFace P.2 u).val,(actualBoundaryFace P.2 u).property.le⟩ ↔
        actualFaceContactMesh P j.castSucc=u := by
    as_aux_lemma =>
      let f : actualNegativeFaceIntervals := ⟨P,⟨j,hneg⟩⟩
      constructor
      · intro hp
        exact (hActualLocalContactArcOpenRootFaceAndOrientation f P.2 0 u hu (Or.inl rfl)
          hroot hp).2.2.1 rfl
      · intro hj
        have hz := hActualLocalContactArcStartFace f
        have hn : (actualCellBoundaryLoops P.1.val (actualLocalContactArcStart f).val).val.1=0 := by
          rw [hz]
          change (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2
            (actualFaceContactMesh P j.castSucc))).val.1=0
          rw [hj]
          exact hroot
        change actualLocalContactArcs f 0=_
        rw [hActualLocalContactArcStart f,actualFaceContactBoundaryFix P _ hn]
        apply congrArg squareCoordinates
        apply Subtype.ext
        exact congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} => z.val)
          (hz.trans (congrArg (actualBoundaryFace P.2) hj))
  have hActualFaceRootTargetIncidence (P : actualActiveContactCells × Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2 u)).val.1=0)
      (j : Fin (actualFaceContactSize P+1))
      (hneg : (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2
        (actualIntervalMidpoint (actualFaceContactMesh P j.castSucc) (actualFaceContactMesh P j.succ)))).val.1/
        (actualCellCenters P.1.val).val.1<0) :
      actualLocalContactArcs ⟨P,⟨j,hneg⟩⟩ 1=
        squareCoordinates ⟨(actualBoundaryFace P.2 u).val,(actualBoundaryFace P.2 u).property.le⟩ ↔
        actualFaceContactMesh P j.succ=u := by
    as_aux_lemma =>
      let f : actualNegativeFaceIntervals := ⟨P,⟨j,hneg⟩⟩
      constructor
      · intro hp
        exact (hActualLocalContactArcOpenRootFaceAndOrientation f P.2 1 u hu (Or.inr rfl)
          hroot hp).2.2.2 rfl
      · intro hj
        have hz := hActualLocalContactArcEndFace f
        have hn : (actualCellBoundaryLoops P.1.val (actualLocalContactArcEnd f).val).val.1=0 := by
          rw [hz]
          change (actualCellBoundaryLoops P.1.val (actualBoundaryFace P.2
            (actualFaceContactMesh P j.succ))).val.1=0
          rw [hj]
          exact hroot
        change actualLocalContactArcs f 1=_
        rw [hActualLocalContactArcEnd f,actualFaceContactBoundaryFix P _ hn]
        apply congrArg squareCoordinates
        apply Subtype.ext
        exact congrArg (fun z : {z : ℝ × ℝ // ‖z‖=1} => z.val)
          (hz.trans (congrArg (actualBoundaryFace P.2) hj))
  have hActualOpenRootSourceFiber (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0) :
      Nonempty
        ({f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 0=squareCoordinates
            ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩} ≃
        {j : Fin (actualFaceContactSize (k,i)+1) |
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.castSucc=u}) := by
    as_aux_lemma =>
      let toIndex := fun f : {f : actualNegativeFaceIntervals | f.1.1=k ∧
            actualLocalContactArcs f 0=squareCoordinates
              ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩} => by
        rcases f with ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRootFaceAndOrientation ⟨(k,j),r⟩ i 0 u hu
          (Or.inl rfl) hroot hp).1
        change j=i at hj
        subst j
        exact (⟨r.val,r.property,(hActualFaceRootSourceIncidence (k,i) u hu hroot r.val r.property).mp hp⟩ :
          {j : Fin (actualFaceContactSize (k,i)+1) |
            actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
            actualFaceContactMesh (k,i) j.castSucc=u})
      refine ⟨{
        toFun := toIndex
        invFun := fun j =>
        ⟨⟨(k,i),⟨j.val,j.property.1⟩⟩,rfl,
          (hActualFaceRootSourceIncidence (k,i) u hu hroot j.val j.property.1).mpr j.property.2⟩
        left_inv := ?_
        right_inv := ?_}⟩
      · rintro ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRootFaceAndOrientation ⟨(k,j),r⟩ i 0 u hu
          (Or.inl rfl) hroot hp).1
        change j=i at hj
        subst j
        rfl
      · intro j
        rfl
  have hActualOpenRootTargetFiber (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0) :
      Nonempty
        ({f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 1=squareCoordinates
            ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩} ≃
        {j : Fin (actualFaceContactSize (k,i)+1) |
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.succ=u}) := by
    as_aux_lemma =>
      let toIndex := fun f : {f : actualNegativeFaceIntervals | f.1.1=k ∧
            actualLocalContactArcs f 1=squareCoordinates
              ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩} => by
        rcases f with ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRootFaceAndOrientation ⟨(k,j),r⟩ i 1 u hu
          (Or.inr rfl) hroot hp).1
        change j=i at hj
        subst j
        exact (⟨r.val,r.property,(hActualFaceRootTargetIncidence (k,i) u hu hroot r.val r.property).mp hp⟩ :
          {j : Fin (actualFaceContactSize (k,i)+1) |
            actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
            actualFaceContactMesh (k,i) j.succ=u})
      refine ⟨{
        toFun := toIndex
        invFun := fun j =>
        ⟨⟨(k,i),⟨j.val,j.property.1⟩⟩,rfl,
          (hActualFaceRootTargetIncidence (k,i) u hu hroot j.val j.property.1).mpr j.property.2⟩
        left_inv := ?_
        right_inv := ?_}⟩
      · rintro ⟨⟨⟨l,j⟩,r⟩,he,hp⟩
        change l=k at he
        subst l
        have hj := (hActualLocalContactArcOpenRootFaceAndOrientation ⟨(k,j),r⟩ i 1 u hu
          (Or.inr rfl) hroot hp).1
        change j=i at hj
        subst j
        rfl
      · intro j
        rfl
  have hActualOpenRootCellSourceCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0) :
      (actualSourceCellEndpointIncidence k
        (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) 0).card=
      (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.castSucc=u)).card := by
    calc
      _ = Fintype.card {f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 0=squareCoordinates
            ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩} :=
        (Fintype.card_subtype _).symm
      _ = _ := (Fintype.card_congr (Classical.choice (hActualOpenRootSourceFiber k i u hu hroot))).trans
        (Fintype.card_subtype _)
  have hActualOpenRootCellTargetCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0) :
      (actualSourceCellEndpointIncidence k
        (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) 1).card=
      (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.succ=u)).card := by
    calc
      _ = Fintype.card {f : actualNegativeFaceIntervals | f.1.1=k ∧
          actualLocalContactArcs f 1=squareCoordinates
            ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩} :=
        (Fintype.card_subtype _).symm
      _ = _ := (Fintype.card_congr (Classical.choice (hActualOpenRootTargetFiber k i u hu hroot))).trans
        (Fintype.card_subtype _)
  have hActualBoundaryFace0Coordinates (t : Interval) :
      squareCoordinates ⟨(actualBoundaryFace 0 t).val,(actualBoundaryFace 0 t).property.le⟩=(t,0) := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change (2*t.val-1+1)/2=t.val
        ring
      · change ((-1 : ℝ)+1)/2=0
        norm_num
  have hActualBoundaryFace2Coordinates (t : Interval) :
      squareCoordinates ⟨(actualBoundaryFace 2 t).val,(actualBoundaryFace 2 t).property.le⟩=(t,1) := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change (2*t.val-1+1)/2=t.val
        ring
      · change ((1 : ℝ)+1)/2=1
        norm_num
  have hActualSourceFaceTopRawFormula (k : actualActiveContactCells) (t : Interval) :
      actualSourceFaceRawHeight (k,2) t=((actualContactGridCharts k.val) (actualCellTopEdge k.val t)).1 := by
    have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 2 t)
    rw [hActualBoundaryFace2Coordinates,(hActualConeCellBoundary k.val t).2.2.1] at hh
    exact (congrArg Prod.fst hh).symm
  have hActualSourceFaceBottomRawFormula (k : actualActiveContactCells) (t : Interval) :
      actualSourceFaceRawHeight (k,0) t=((actualContactGridCharts k.val) (actualCellBottomEdge k.val t)).1 := by
    have hh := hActualCellBoundaryLoopFormula k.val (actualBoundaryFace 0 t)
    rw [hActualBoundaryFace0Coordinates,(hActualConeCellBoundary k.val t).1] at hh
    exact (congrArg Prod.fst hh).symm
  have hActualHorizontalCellSharedTrace (i : Fin (actualContactGridSize+1)) (j : Fin actualContactGridSize)
      (t : Interval) : actualCellTopEdge (i,j.castSucc) t=actualCellBottomEdge (i,j.succ) t := by
    rfl
  have hActualVerticalRootProducesEvenActualSectorCount (i : Fin actualContactGridSize)
      (j : Fin (actualContactGridSize+1)) (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellRightEdge (i.castSucc,j) u∈a.val.image) :
      ∃ k l : actualActiveContactCells,k.val=(i.castSucc,j) ∧ l.val=(i.succ,j) ∧
        ∃ kl kr : Fin (actualFaceContactSize (k,1)+1),
          ∃ ll lr : Fin (actualFaceContactSize (l,3)+1),
            actualFaceContactMesh (k,1) kl.succ=u ∧ actualFaceContactMesh (k,1) kr.castSucc=u ∧
            actualFaceContactMesh (l,3) ll.succ=u ∧ actualFaceContactMesh (l,3) lr.castSucc=u ∧
            Even (actualSourceNegativeIndicator (k,1) kl+actualSourceNegativeIndicator (k,1) kr+
              actualSourceNegativeIndicator (l,3) ll+actualSourceNegativeIndicator (l,3) lr) := by
    as_aux_lemma =>
      have hkactive : ¬Disjoint (actualContactGridCharts (i.castSucc,j)).source a.val.image := by
        intro hd
        exact Set.disjoint_left.mp hd (hActualCellRightRange (i.castSucc,j) ⟨u,rfl⟩) hmem
      have hleftmem : actualCellLeftEdge (i.succ,j) u∈a.val.image := by
        rw [←hActualVerticalCellSharedTrace i j u]
        exact hmem
      have hlactive : ¬Disjoint (actualContactGridCharts (i.succ,j)).source a.val.image := by
        intro hd
        exact Set.disjoint_left.mp hd (hActualCellLeftRange (i.succ,j) ⟨u,rfl⟩) hleftmem
      let k : actualActiveContactCells := ⟨(i.castSucc,j),hkactive⟩
      let l : actualActiveContactCells := ⟨(i.succ,j),hlactive⟩
      let γ := (actualCellRightEdge k.val).toContinuousMap
      let g := actualSourceFaceHeight (k,1)
      let h := actualSourceFaceHeight (l,3)
      have haxisC := (hActualContactGridChartData k.val).2.2.resolve_left k.property
      have haxisD := (hActualContactGridChartData l.val).2.2.resolve_left l.property
      have hc := (hActualCellCenterAxisOff k.val).resolve_left k.property
      have hd := (hActualCellCenterAxisOff l.val).resolve_left l.property
      have hrawk : actualSourceFaceRawHeight (k,1) u=0 :=
        (hActualSourceFaceRightRawFormula k u).trans
          ((haxisC _ (hActualCellRightRange k.val ⟨u,rfl⟩)).mp hmem)
      have hrawl : actualSourceFaceRawHeight (l,3) u=0 :=
        (hActualSourceFaceLeftRawFormula l u).trans
          ((haxisD _ (hActualCellLeftRange l.val ⟨u,rfl⟩)).mp hleftmem)
      obtain ⟨kl,kr,hkl,hkr,hxl,hxr⟩ := actualInteriorZeroMeshNeighbors (actualSourceFaceRawHeight (k,1))
        (actualFaceContactSize (k,1)) (actualFaceContactMesh (k,1)) (actualFaceContactMono (k,1))
        (actualFaceContactStart (k,1)) (actualFaceContactEnd (k,1)) (actualFaceContactNoZero (k,1)) u hu hrawk
      obtain ⟨ll,lr,hll,hlr,hXl,hXr⟩ := actualInteriorZeroMeshNeighbors (actualSourceFaceRawHeight (l,3))
        (actualFaceContactSize (l,3)) (actualFaceContactMesh (l,3)) (actualFaceContactMono (l,3))
        (actualFaceContactStart (l,3)) (actualFaceContactEnd (l,3)) (actualFaceContactNoZero (l,3)) u hu hrawl
      let x := actualFaceContactMesh (k,1) kl.castSucc
      let y := actualFaceContactMesh (k,1) kr.succ
      let X := actualFaceContactMesh (l,3) ll.castSucc
      let Y := actualFaceContactMesh (l,3) lr.succ
      let sl := actualIntervalMidpoint (actualFaceContactMesh (k,1) kl.castSucc)
        (actualFaceContactMesh (k,1) kl.succ)
      let sr := actualIntervalMidpoint (actualFaceContactMesh (k,1) kr.castSucc)
        (actualFaceContactMesh (k,1) kr.succ)
      let sL := actualIntervalMidpoint (actualFaceContactMesh (l,3) ll.castSucc)
        (actualFaceContactMesh (l,3) ll.succ)
      let sR := actualIntervalMidpoint (actualFaceContactMesh (l,3) lr.castSucc)
        (actualFaceContactMesh (l,3) lr.succ)
      have hsl : sl∈Set.Ioo x u := by
        have hm := hActualSourceMeshMidpointInterior (k,1) kl
        change sl∈Set.Ioo x (actualFaceContactMesh (k,1) kl.succ) at hm
        rw [hkl] at hm
        exact hm
      have hsr : sr∈Set.Ioo u y := by
        have hm := hActualSourceMeshMidpointInterior (k,1) kr
        change sr∈Set.Ioo (actualFaceContactMesh (k,1) kr.castSucc) y at hm
        rw [hkr] at hm
        exact hm
      have hsL : sL∈Set.Ioo X u := by
        have hm := hActualSourceMeshMidpointInterior (l,3) ll
        change sL∈Set.Ioo X (actualFaceContactMesh (l,3) ll.succ) at hm
        rw [hll] at hm
        exact hm
      have hsR : sR∈Set.Ioo u Y := by
        have hm := hActualSourceMeshMidpointInterior (l,3) lr
        change sR∈Set.Ioo (actualFaceContactMesh (l,3) lr.castSucc) Y at hm
        rw [hlr] at hm
        exact hm
      have hg : ∀ t,g t=((actualContactGridCharts k.val) (γ t)).1/(actualCellCenters k.val).val.1 := by
        intro t
        change actualSourceFaceRawHeight (k,1) t/(actualCellCenters k.val).val.1=
          ((actualContactGridCharts k.val) (actualCellRightEdge k.val t)).1/(actualCellCenters k.val).val.1
        rw [hActualSourceFaceRightRawFormula]
      have hh : ∀ t,h t=((actualContactGridCharts l.val) (γ t)).1/(actualCellCenters l.val).val.1 := by
        intro t
        change actualSourceFaceRawHeight (l,3) t/(actualCellCenters l.val).val.1=
          ((actualContactGridCharts l.val) (actualCellRightEdge k.val t)).1/(actualCellCenters l.val).val.1
        rw [hActualSourceFaceLeftRawFormula,hActualVerticalCellSharedTrace i j t]
      have hpD : γ u∈(actualContactGridCharts l.val).source := by
        change actualCellRightEdge (i.castSucc,j) u∈(actualContactGridCharts (i.succ,j)).source
        rw [hActualVerticalCellSharedTrace i j u]
        exact hActualCellLeftRange l.val ⟨u,rfl⟩
      have hs := actualMarkedSharedAxisTraceSameSectorSign γ u hu hmem
        (actualContactGridCharts k.val) (actualContactGridCharts l.val)
        (hActualCellRightRange k.val ⟨u,rfl⟩) hpD haxisC haxisD g h
        (actualCellCenters k.val).val.1 (actualCellCenters l.val).val.1 hc hd hg hh
        x y sl sr X Y sL sR hxl hxr hXl hXr hsl hsr hsL hsR
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (k,1) kl t ht0 (hkl.symm ▸ ht1))
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (k,1) kr t (hkr.symm ▸ ht0) ht1)
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (l,3) ll t ht0 (hll.symm ▸ ht1))
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (l,3) lr t (hlr.symm ▸ ht0) ht1)
      refine ⟨k,l,rfl,rfl,kl,kr,ll,lr,hkl,hkr,hll,hlr,?_⟩
      exact actualMarkedSectorIndicatorsEven (g sl) (g sr) (h sL) (h sR) hs
  have hActualHorizontalRootProducesEvenActualSectorCount (i : Fin (actualContactGridSize+1))
      (j : Fin actualContactGridSize) (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellTopEdge (i,j.castSucc) u∈a.val.image) :
      ∃ k l : actualActiveContactCells,k.val=(i,j.castSucc) ∧ l.val=(i,j.succ) ∧
        ∃ kl kr : Fin (actualFaceContactSize (k,2)+1),
          ∃ ll lr : Fin (actualFaceContactSize (l,0)+1),
            actualFaceContactMesh (k,2) kl.succ=u ∧ actualFaceContactMesh (k,2) kr.castSucc=u ∧
            actualFaceContactMesh (l,0) ll.succ=u ∧ actualFaceContactMesh (l,0) lr.castSucc=u ∧
            Even (actualSourceNegativeIndicator (k,2) kl+actualSourceNegativeIndicator (k,2) kr+
              actualSourceNegativeIndicator (l,0) ll+actualSourceNegativeIndicator (l,0) lr) := by
    as_aux_lemma =>
      have hkactive : ¬Disjoint (actualContactGridCharts (i,j.castSucc)).source a.val.image := by
        intro hd
        exact Set.disjoint_left.mp hd (hActualCellTopRange (i,j.castSucc) ⟨u,rfl⟩) hmem
      have hleftmem : actualCellBottomEdge (i,j.succ) u∈a.val.image := by
        rw [←hActualHorizontalCellSharedTrace i j u]
        exact hmem
      have hlactive : ¬Disjoint (actualContactGridCharts (i,j.succ)).source a.val.image := by
        intro hd
        exact Set.disjoint_left.mp hd (hActualCellBottomRange (i,j.succ) ⟨u,rfl⟩) hleftmem
      let k : actualActiveContactCells := ⟨(i,j.castSucc),hkactive⟩
      let l : actualActiveContactCells := ⟨(i,j.succ),hlactive⟩
      let γ := (actualCellTopEdge k.val).toContinuousMap
      let g := actualSourceFaceHeight (k,2)
      let h := actualSourceFaceHeight (l,0)
      have haxisC := (hActualContactGridChartData k.val).2.2.resolve_left k.property
      have haxisD := (hActualContactGridChartData l.val).2.2.resolve_left l.property
      have hc := (hActualCellCenterAxisOff k.val).resolve_left k.property
      have hd := (hActualCellCenterAxisOff l.val).resolve_left l.property
      have hrawk : actualSourceFaceRawHeight (k,2) u=0 :=
        (hActualSourceFaceTopRawFormula k u).trans
          ((haxisC _ (hActualCellTopRange k.val ⟨u,rfl⟩)).mp hmem)
      have hrawl : actualSourceFaceRawHeight (l,0) u=0 :=
        (hActualSourceFaceBottomRawFormula l u).trans
          ((haxisD _ (hActualCellBottomRange l.val ⟨u,rfl⟩)).mp hleftmem)
      obtain ⟨kl,kr,hkl,hkr,hxl,hxr⟩ := actualInteriorZeroMeshNeighbors (actualSourceFaceRawHeight (k,2))
        (actualFaceContactSize (k,2)) (actualFaceContactMesh (k,2)) (actualFaceContactMono (k,2))
        (actualFaceContactStart (k,2)) (actualFaceContactEnd (k,2)) (actualFaceContactNoZero (k,2)) u hu hrawk
      obtain ⟨ll,lr,hll,hlr,hXl,hXr⟩ := actualInteriorZeroMeshNeighbors (actualSourceFaceRawHeight (l,0))
        (actualFaceContactSize (l,0)) (actualFaceContactMesh (l,0)) (actualFaceContactMono (l,0))
        (actualFaceContactStart (l,0)) (actualFaceContactEnd (l,0)) (actualFaceContactNoZero (l,0)) u hu hrawl
      let x := actualFaceContactMesh (k,2) kl.castSucc
      let y := actualFaceContactMesh (k,2) kr.succ
      let X := actualFaceContactMesh (l,0) ll.castSucc
      let Y := actualFaceContactMesh (l,0) lr.succ
      let sl := actualIntervalMidpoint (actualFaceContactMesh (k,2) kl.castSucc)
        (actualFaceContactMesh (k,2) kl.succ)
      let sr := actualIntervalMidpoint (actualFaceContactMesh (k,2) kr.castSucc)
        (actualFaceContactMesh (k,2) kr.succ)
      let sL := actualIntervalMidpoint (actualFaceContactMesh (l,0) ll.castSucc)
        (actualFaceContactMesh (l,0) ll.succ)
      let sR := actualIntervalMidpoint (actualFaceContactMesh (l,0) lr.castSucc)
        (actualFaceContactMesh (l,0) lr.succ)
      have hsl : sl∈Set.Ioo x u := by
        have hm := hActualSourceMeshMidpointInterior (k,2) kl
        change sl∈Set.Ioo x (actualFaceContactMesh (k,2) kl.succ) at hm
        rw [hkl] at hm
        exact hm
      have hsr : sr∈Set.Ioo u y := by
        have hm := hActualSourceMeshMidpointInterior (k,2) kr
        change sr∈Set.Ioo (actualFaceContactMesh (k,2) kr.castSucc) y at hm
        rw [hkr] at hm
        exact hm
      have hsL : sL∈Set.Ioo X u := by
        have hm := hActualSourceMeshMidpointInterior (l,0) ll
        change sL∈Set.Ioo X (actualFaceContactMesh (l,0) ll.succ) at hm
        rw [hll] at hm
        exact hm
      have hsR : sR∈Set.Ioo u Y := by
        have hm := hActualSourceMeshMidpointInterior (l,0) lr
        change sR∈Set.Ioo (actualFaceContactMesh (l,0) lr.castSucc) Y at hm
        rw [hlr] at hm
        exact hm
      have hg : ∀ t,g t=((actualContactGridCharts k.val) (γ t)).1/(actualCellCenters k.val).val.1 := by
        intro t
        change actualSourceFaceRawHeight (k,2) t/(actualCellCenters k.val).val.1=
          ((actualContactGridCharts k.val) (actualCellTopEdge k.val t)).1/(actualCellCenters k.val).val.1
        rw [hActualSourceFaceTopRawFormula]
      have hh : ∀ t,h t=((actualContactGridCharts l.val) (γ t)).1/(actualCellCenters l.val).val.1 := by
        intro t
        change actualSourceFaceRawHeight (l,0) t/(actualCellCenters l.val).val.1=
          ((actualContactGridCharts l.val) (actualCellTopEdge k.val t)).1/(actualCellCenters l.val).val.1
        rw [hActualSourceFaceBottomRawFormula,hActualHorizontalCellSharedTrace i j t]
      have hpD : γ u∈(actualContactGridCharts l.val).source := by
        change actualCellTopEdge (i,j.castSucc) u∈(actualContactGridCharts (i,j.succ)).source
        rw [hActualHorizontalCellSharedTrace i j u]
        exact hActualCellBottomRange l.val ⟨u,rfl⟩
      have hs := actualMarkedSharedAxisTraceSameSectorSign γ u hu hmem
        (actualContactGridCharts k.val) (actualContactGridCharts l.val)
        (hActualCellTopRange k.val ⟨u,rfl⟩) hpD haxisC haxisD g h
        (actualCellCenters k.val).val.1 (actualCellCenters l.val).val.1 hc hd hg hh
        x y sl sr X Y sL sR hxl hxr hXl hXr hsl hsr hsL hsR
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (k,2) kl t ht0 (hkl.symm ▸ ht1))
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (k,2) kr t (hkr.symm ▸ ht0) ht1)
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (l,0) ll t ht0 (hll.symm ▸ ht1))
        (fun t ht0 ht1 => hActualSourceFaceHeightNoZero (l,0) lr t (hlr.symm ▸ ht0) ht1)
      refine ⟨k,l,rfl,rfl,kl,kr,ll,lr,hkl,hkr,hll,hlr,?_⟩
      exact actualMarkedSectorIndicatorsEven (g sl) (g sr) (h sL) (h sR) hs
  let actualSourceFaceEndpointIncidence (P : actualActiveContactCells × Fin 4) (u : Interval) :=
    Finset.univ.filter (fun j : Fin (actualFaceContactSize P+1) =>
      actualSourceFaceHeight P (actualIntervalMidpoint (actualFaceContactMesh P j.castSucc)
        (actualFaceContactMesh P j.succ))<0 ∧
      (actualFaceContactMesh P j.castSucc=u ∨ actualFaceContactMesh P j.succ=u))
  have hActualVerticalRootActualFaceIncidenceEven (i : Fin actualContactGridSize)
      (j : Fin (actualContactGridSize+1)) (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellRightEdge (i.castSucc,j) u∈a.val.image) :
      ∃ k l : actualActiveContactCells,k.val=(i.castSucc,j) ∧ l.val=(i.succ,j) ∧
        Even ((actualSourceFaceEndpointIncidence (k,1) u).card+
          (actualSourceFaceEndpointIncidence (l,3) u).card) := by
    as_aux_lemma =>
      obtain ⟨k,l,hk,hl,kl,kr,ll,lr,hkl,hkr,hll,hlr,heven⟩ :=
        hActualVerticalRootProducesEvenActualSectorCount i j u hu hmem
      refine ⟨k,l,hk,hl,?_⟩
      have hc (P : actualActiveContactCells × Fin 4) (s t : Fin (actualFaceContactSize P+1))
          (hs : actualFaceContactMesh P s.succ=u) (ht : actualFaceContactMesh P t.castSucc=u) :
          (actualSourceFaceEndpointIncidence P u).card=
            actualSourceNegativeIndicator P s+actualSourceNegativeIndicator P t :=
        actualMeshNegativeEndpointCard (actualFaceContactSize P) (actualFaceContactMesh P)
          (actualFaceContactMono P) (fun q => actualSourceFaceHeight P
            (actualIntervalMidpoint (actualFaceContactMesh P q.castSucc) (actualFaceContactMesh P q.succ))<0)
          s t u hs ht
      rw [hc (k,1) kl kr hkl hkr,hc (l,3) ll lr hll hlr]
      simpa only [Nat.add_assoc] using heven
  have hActualHorizontalRootActualFaceIncidenceEven (i : Fin (actualContactGridSize+1))
      (j : Fin actualContactGridSize) (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellTopEdge (i,j.castSucc) u∈a.val.image) :
      ∃ k l : actualActiveContactCells,k.val=(i,j.castSucc) ∧ l.val=(i,j.succ) ∧
        Even ((actualSourceFaceEndpointIncidence (k,2) u).card+
          (actualSourceFaceEndpointIncidence (l,0) u).card) := by
    as_aux_lemma =>
      obtain ⟨k,l,hk,hl,kl,kr,ll,lr,hkl,hkr,hll,hlr,heven⟩ :=
        hActualHorizontalRootProducesEvenActualSectorCount i j u hu hmem
      refine ⟨k,l,hk,hl,?_⟩
      have hc (P : actualActiveContactCells × Fin 4) (s t : Fin (actualFaceContactSize P+1))
          (hs : actualFaceContactMesh P s.succ=u) (ht : actualFaceContactMesh P t.castSucc=u) :
          (actualSourceFaceEndpointIncidence P u).card=
            actualSourceNegativeIndicator P s+actualSourceNegativeIndicator P t :=
        actualMeshNegativeEndpointCard (actualFaceContactSize P) (actualFaceContactMesh P)
          (actualFaceContactMono P) (fun q => actualSourceFaceHeight P
            (actualIntervalMidpoint (actualFaceContactMesh P q.castSucc) (actualFaceContactMesh P q.succ))<0)
          s t u hs ht
      rw [hc (k,2) kl kr hkl hkr,hc (l,0) ll lr hll hlr]
      simpa only [Nat.add_assoc] using heven
  have hActualOpenRootCellEndpointCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0) :
      (actualSourceCellEndpointIncidence k
        (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) 0).card+
      (actualSourceCellEndpointIncidence k
        (squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩) 1).card=
      (actualSourceFaceEndpointIncidence (k,i) u).card := by
    rw [hActualOpenRootCellSourceCount k i u hu hroot,hActualOpenRootCellTargetCount k i u hu hroot]
    exact actualMeshSourceTargetCardAdd (actualFaceContactSize (k,i)) (actualFaceContactMesh (k,i))
      (actualFaceContactMono (k,i)) (fun j => actualSourceFaceHeight (k,i)
        (actualIntervalMidpoint (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0) u
  have hActualNegativeInternalMeshNodeFaceIncidenceTwo (P : actualActiveContactCells × Fin 4)
      (q : Fin (actualFaceContactSize P+2)) (hq₀ : q≠0)
      (hq₁ : q≠Fin.last (actualFaceContactSize P+1))
      (hneg : actualSourceFaceHeight P (actualFaceContactMesh P q)<0) :
      (actualSourceFaceEndpointIncidence P (actualFaceContactMesh P q)).card=2 := by
    exact CurveComplex.LocalSurgery.actualNegativeInternalMeshNodeIncidenceTwo (actualFaceContactSize P) (actualFaceContactMesh P) (actualFaceContactMono P) (actualSourceFaceHeight P) (hActualSourceMeshMidpointInterior P) (hActualSourceFaceHeightNoZero P) q hq₀ hq₁ hneg
  have hActualContactArcOnInternalVerticalSeamCells (e : actualNegativeFaceIntervals)
      (t v : Interval) (i : Fin actualContactGridSize) (j : Fin (actualContactGridSize+1))
      (hj : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ))
      (he : actualGlobalContactArcs e t=(actualContactGridParameter i.succ.castSucc,v)) :
      e.1.1.val=(i.castSucc,j) ∨ e.1.1.val=(i.succ,j) := by
    as_aux_lemma =>
      obtain ⟨hx,hy⟩ := hActualGlobalContactArcClosedCell e t
      rw [he] at hx hy
      have hi := actualInteriorGridNodeClosedCells actualContactGridSize actualContactGridParameter
        hActualContactGridStrict i e.1.1.val.1 hx.1 hx.2
      have hj' : j=e.1.1.val.2 := hActualGridOpenClosedUnique _ _ v hj hy
      rcases hi with hi | hi
      · exact Or.inl (Prod.ext hi hj'.symm)
      · exact Or.inr (Prod.ext hi hj'.symm)
  have hActualContactArcOnInternalHorizontalSeamCells (e : actualNegativeFaceIntervals)
      (t v : Interval) (i : Fin (actualContactGridSize+1)) (j : Fin actualContactGridSize)
      (hi : v∈Set.Ioo (actualContactGridParameter i.castSucc) (actualContactGridParameter i.succ))
      (he : actualGlobalContactArcs e t=(v,actualContactGridParameter j.succ.castSucc)) :
      e.1.1.val=(i,j.castSucc) ∨ e.1.1.val=(i,j.succ) := by
    as_aux_lemma =>
      obtain ⟨hx,hy⟩ := hActualGlobalContactArcClosedCell e t
      rw [he] at hx hy
      have hj := actualInteriorGridNodeClosedCells actualContactGridSize actualContactGridParameter
        hActualContactGridStrict j e.1.1.val.2 hy.1 hy.2
      have hi' : i=e.1.1.val.1 := hActualGridOpenClosedUnique _ _ v hi hx
      rcases hj with hj | hj
      · exact Or.inl (Prod.ext hi'.symm hj)
      · exact Or.inr (Prod.ext hi'.symm hj)
  have hActualVerticalAffineCellSeam (i : Fin actualContactGridSize)
      (j : Fin (actualContactGridSize+1)) (u : Interval) :
      actualAffineCells (i.castSucc,j) (1,u)=actualAffineCells (i.succ,j) (0,u) := by
    as_aux_lemma =>
      rw [hActualAffineCellFormula,hActualAffineCellFormula]
      apply Prod.ext <;> apply Subtype.ext
      · change (1-(1 : ℝ))*(actualContactGridParameter i.castSucc.castSucc).val+
            1*(actualContactGridParameter i.castSucc.succ).val=
            (1-(0 : ℝ))*(actualContactGridParameter i.succ.castSucc).val+
            0*(actualContactGridParameter i.succ.succ).val
        have he : i.castSucc.succ=i.succ.castSucc := by apply Fin.ext; rfl
        rw [he]
        ring
      · rfl
  have hActualHorizontalAffineCellSeam (i : Fin (actualContactGridSize+1))
      (j : Fin actualContactGridSize) (u : Interval) :
      actualAffineCells (i,j.castSucc) (u,1)=actualAffineCells (i,j.succ) (u,0) := by
    as_aux_lemma =>
      rw [hActualAffineCellFormula,hActualAffineCellFormula]
      apply Prod.ext <;> apply Subtype.ext
      · rfl
      · change (1-(1 : ℝ))*(actualContactGridParameter j.castSucc.castSucc).val+
            1*(actualContactGridParameter j.castSucc.succ).val=
            (1-(0 : ℝ))*(actualContactGridParameter j.succ.castSucc).val+
            0*(actualContactGridParameter j.succ.succ).val
        have he : j.castSucc.succ=j.succ.castSucc := by apply Fin.ext; rfl
        rw [he]
        ring
  have hActualInternalVerticalContactVertexDegreeEven (i : Fin actualContactGridSize)
      (j : Fin (actualContactGridSize+1)) (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellRightEdge (i.castSucc,j) u∈a.val.image)
      (w : actualContactVertices) (hw : w.val=actualAffineCells (i.castSucc,j) (1,u)) :
      Even (actualZeroGraph.degree (Sum.inl w)) := by
    as_aux_lemma =>
      obtain ⟨k,l,hk,hl,heven⟩ := hActualVerticalRootActualFaceIncidenceEven i j u hu hmem
      have hkl : k≠l := by
        intro h
        have hh : (i.castSucc,j)=(i.succ,j) := hk.symm.trans ((congrArg Subtype.val h).trans hl)
        have hv := congrArg (fun z : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1) => z.1.val) hh
        change i.val=i.val+1 at hv
        exact (Nat.ne_of_lt (Nat.lt_succ_self i.val)) hv
      let v := actualIntervalSegment (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) u
      have hv : v∈Set.Ioo (actualContactGridParameter j.castSucc) (actualContactGridParameter j.succ) :=
        actualIntervalSegmentInterior _ _ u (hActualContactGridStep j) hu
      have hp : w.val=(actualContactGridParameter i.succ.castSucc,v) := by
        rw [hw,hActualAffineCellFormula]
        apply Prod.ext
        · apply Subtype.ext
          change (1-(1 : ℝ))*(actualContactGridParameter i.castSucc.castSucc).val+
            1*(actualContactGridParameter i.castSucc.succ).val=(actualContactGridParameter i.succ.castSucc).val
          have hi : i.castSucc.succ=i.succ.castSucc := by apply Fin.ext; rfl
          rw [hi]
          ring
        · rfl
      have hcover (f : actualNegativeFaceIntervals) (t : Interval)
          (hh : actualGlobalContactArcs f t=w.val) : f.1.1=k ∨ f.1.1=l := by
        rcases hActualContactArcOnInternalVerticalSeamCells f t v i j hv (hh.trans hp) with hc | hc
        · exact Or.inl (Subtype.ext (hc.trans hk.symm))
        · exact Or.inr (Subtype.ext (hc.trans hl.symm))
      have hwk : w.val=actualAffineCells k.val (1,u) := by simpa only [hk] using hw
      have hwl : w.val=actualAffineCells l.val (0,u) := by
        simpa only [hl] using hw.trans (hActualVerticalAffineCellSeam i j u)
      have count (t : Interval) :
          (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val)).card=
          (actualSourceCellEndpointIncidence k (1,u) t).card+
            (actualSourceCellEndpointIncidence l (0,u) t).card := by
        have hpartition :
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val)).card=
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=k)).card+
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=l)).card := by
          convert actualFiniteTwoLabelIncidenceCard actualNegativeFaceIntervals actualActiveContactCells
            (fun f => f.1.1) (fun f => actualGlobalContactArcs f t=w.val) k l hkl (fun f => hcover f t) using 1
          all_goals congr 1
          all_goals try apply congrArg Finset.card
          all_goals ext f
          all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        have hkcount :
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=k)).card=
            (actualSourceCellEndpointIncidence k (1,u) t).card := by
          rw [hwk]
          convert hActualGlobalCellEndpointCountAsLocal k t (1,u) using 1
        have hlcount :
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=l)).card=
            (actualSourceCellEndpointIncidence l (0,u) t).card := by
          rw [hwl]
          convert hActualGlobalCellEndpointCountAsLocal l t (0,u) using 1
        exact hpartition.trans (congrArg₂ (·+·) hkcount hlcount)
      have hrootk : (actualCellBoundaryLoops k.val (actualBoundaryFace 1 u)).val.1=0 := by
        have hm : actualCellRightEdge k.val u∈a.val.image := by
          rw [hk]
          exact hmem
        have hraw := ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
          (hActualCellRightRange k.val ⟨u,rfl⟩)).mp hm
        exact (hActualSourceFaceRightRawFormula k u).trans hraw
      have hrootl : (actualCellBoundaryLoops l.val (actualBoundaryFace 3 u)).val.1=0 := by
        have hm : actualCellLeftEdge l.val u∈a.val.image := by
          rw [hl,←hActualVerticalCellSharedTrace i j u]
          exact hmem
        have hraw := ((hActualContactGridChartData l.val).2.2.resolve_left l.property _
          (hActualCellLeftRange l.val ⟨u,rfl⟩)).mp hm
        exact (hActualSourceFaceLeftRawFormula l u).trans hraw
      have hck := hActualOpenRootCellEndpointCount k 1 u hu hrootk
      have hcl := hActualOpenRootCellEndpointCount l 3 u hu hrootl
      rw [hActualBoundaryFaceOneCoordinates] at hck
      rw [hActualBoundaryFaceThreeCoordinates] at hcl
      rw [hActualGraphEndpointDegreeAsGlobalArcCounts,count 0,count 1]
      have htotal :
          (actualSourceCellEndpointIncidence k (1,u) 0).card+
            (actualSourceCellEndpointIncidence l (0,u) 0).card+
          ((actualSourceCellEndpointIncidence k (1,u) 1).card+
            (actualSourceCellEndpointIncidence l (0,u) 1).card)=
          (actualSourceFaceEndpointIncidence (k,1) u).card+
            (actualSourceFaceEndpointIncidence (l,3) u).card := by
        calc
          _ = ((actualSourceCellEndpointIncidence k (1,u) 0).card+
            (actualSourceCellEndpointIncidence k (1,u) 1).card)+
            ((actualSourceCellEndpointIncidence l (0,u) 0).card+
            (actualSourceCellEndpointIncidence l (0,u) 1).card) := by ac_rfl
          _ = _ := by rw [hck,hcl]
      rw [htotal]
      exact heven
  have hActualInternalHorizontalContactVertexDegreeEven (i : Fin (actualContactGridSize+1))
      (j : Fin actualContactGridSize) (u : Interval) (hu : u∈Set.Ioo (0 : Interval) 1)
      (hmem : actualCellTopEdge (i,j.castSucc) u∈a.val.image)
      (w : actualContactVertices) (hw : w.val=actualAffineCells (i,j.castSucc) (u,1)) :
      Even (actualZeroGraph.degree (Sum.inl w)) := by
    as_aux_lemma =>
      obtain ⟨k,l,hk,hl,heven⟩ := hActualHorizontalRootActualFaceIncidenceEven i j u hu hmem
      have hkl : k≠l := by
        intro h
        have hh : (i,j.castSucc)=(i,j.succ) := hk.symm.trans ((congrArg Subtype.val h).trans hl)
        have hv := congrArg (fun z : Fin (actualContactGridSize+1) × Fin (actualContactGridSize+1) => z.2.val) hh
        change j.val=j.val+1 at hv
        exact (Nat.ne_of_lt (Nat.lt_succ_self j.val)) hv
      let v := actualIntervalSegment (actualContactGridParameter i.castSucc) (actualContactGridParameter i.succ) u
      have hv : v∈Set.Ioo (actualContactGridParameter i.castSucc) (actualContactGridParameter i.succ) :=
        actualIntervalSegmentInterior _ _ u (hActualContactGridStep i) hu
      have hp : w.val=(v,actualContactGridParameter j.succ.castSucc) := by
        rw [hw,hActualAffineCellFormula]
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change (1-(1 : ℝ))*(actualContactGridParameter j.castSucc.castSucc).val+
            1*(actualContactGridParameter j.castSucc.succ).val=(actualContactGridParameter j.succ.castSucc).val
          have hj : j.castSucc.succ=j.succ.castSucc := by apply Fin.ext; rfl
          rw [hj]
          ring
      have hcover (f : actualNegativeFaceIntervals) (t : Interval)
          (hh : actualGlobalContactArcs f t=w.val) : f.1.1=k ∨ f.1.1=l := by
        rcases hActualContactArcOnInternalHorizontalSeamCells f t v i j hv (hh.trans hp) with hc | hc
        · exact Or.inl (Subtype.ext (hc.trans hk.symm))
        · exact Or.inr (Subtype.ext (hc.trans hl.symm))
      have hwk : w.val=actualAffineCells k.val (u,1) := by simpa only [hk] using hw
      have hwl : w.val=actualAffineCells l.val (u,0) := by
        simpa only [hl] using hw.trans (hActualHorizontalAffineCellSeam i j u)
      have count (t : Interval) :
          (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val)).card=
          (actualSourceCellEndpointIncidence k (u,1) t).card+
            (actualSourceCellEndpointIncidence l (u,0) t).card := by
        have hpartition :
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val)).card=
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=k)).card+
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=l)).card := by
          convert actualFiniteTwoLabelIncidenceCard actualNegativeFaceIntervals actualActiveContactCells
            (fun f => f.1.1) (fun f => actualGlobalContactArcs f t=w.val) k l hkl (fun f => hcover f t) using 1
          all_goals congr 1
          all_goals try apply congrArg Finset.card
          all_goals ext f
          all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        have hkcount :
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=k)).card=
            (actualSourceCellEndpointIncidence k (u,1) t).card := by
          rw [hwk]
          convert hActualGlobalCellEndpointCountAsLocal k t (u,1) using 1
        have hlcount :
            (Finset.univ.filter (fun f : actualNegativeFaceIntervals => actualGlobalContactArcs f t=w.val ∧ f.1.1=l)).card=
            (actualSourceCellEndpointIncidence l (u,0) t).card := by
          rw [hwl]
          convert hActualGlobalCellEndpointCountAsLocal l t (u,0) using 1
        exact hpartition.trans (congrArg₂ (·+·) hkcount hlcount)
      have hrootk : (actualCellBoundaryLoops k.val (actualBoundaryFace 2 u)).val.1=0 := by
        have hm : actualCellTopEdge k.val u∈a.val.image := by
          rw [hk]
          exact hmem
        have hraw := ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
          (hActualCellTopRange k.val ⟨u,rfl⟩)).mp hm
        exact (hActualSourceFaceTopRawFormula k u).trans hraw
      have hrootl : (actualCellBoundaryLoops l.val (actualBoundaryFace 0 u)).val.1=0 := by
        have hm : actualCellBottomEdge l.val u∈a.val.image := by
          rw [hl,←hActualHorizontalCellSharedTrace i j u]
          exact hmem
        have hraw := ((hActualContactGridChartData l.val).2.2.resolve_left l.property _
          (hActualCellBottomRange l.val ⟨u,rfl⟩)).mp hm
        exact (hActualSourceFaceBottomRawFormula l u).trans hraw
      have hck := hActualOpenRootCellEndpointCount k 2 u hu hrootk
      have hcl := hActualOpenRootCellEndpointCount l 0 u hu hrootl
      rw [hActualBoundaryFace2Coordinates] at hck
      rw [hActualBoundaryFace0Coordinates] at hcl
      rw [hActualGraphEndpointDegreeAsGlobalArcCounts,count 0,count 1]
      have htotal :
          (actualSourceCellEndpointIncidence k (u,1) 0).card+
            (actualSourceCellEndpointIncidence l (u,0) 0).card+
          ((actualSourceCellEndpointIncidence k (u,1) 1).card+
            (actualSourceCellEndpointIncidence l (u,0) 1).card)=
          (actualSourceFaceEndpointIncidence (k,2) u).card+
            (actualSourceFaceEndpointIncidence (l,0) u).card := by
        calc
          _ = ((actualSourceCellEndpointIncidence k (u,1) 0).card+
            (actualSourceCellEndpointIncidence k (u,1) 1).card)+
            ((actualSourceCellEndpointIncidence l (u,0) 0).card+
            (actualSourceCellEndpointIncidence l (u,0) 1).card) := by ac_rfl
          _ = _ := by rw [hck,hcl]
      rw [htotal]
      exact heven
  let actualIndexedCellEndpointIncidence (k : actualActiveContactCells) (i : Fin 4)
      (x : Interval × Interval) (t : Interval) := Finset.univ.filter
        (fun f : actualNegativeFaceIntervals => f.1.1=k ∧ f.1.2=i ∧ actualLocalContactArcs f t=x)
  have hActualIndexedRadialSourceFiber (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      Nonempty
        ({f : actualNegativeFaceIntervals | f.1.1=k ∧ f.1.2=i ∧
          actualLocalContactArcs f 0=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} ≃
        {j : Fin (actualFaceContactSize (k,i)+1) |
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.castSucc=u}) := by
    as_aux_lemma =>
      let toIndex := fun f : {f : actualNegativeFaceIntervals | f.1.1=k ∧ f.1.2=i ∧
            actualLocalContactArcs f 0=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} => by
        rcases f with ⟨⟨⟨l,j⟩,r⟩,he,hj,hp⟩
        change l=k at he
        subst l
        change j=i at hj
        subst j
        exact (⟨r.val,r.property,(hActualFaceRadialSourceIncidence (k,i) u hle r.val r.property).mp hp⟩ :
          {j : Fin (actualFaceContactSize (k,i)+1) |
            actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
            actualFaceContactMesh (k,i) j.castSucc=u})
      refine ⟨{
        toFun := toIndex
        invFun := fun j => ⟨⟨(k,i),⟨j.val,j.property.1⟩⟩,rfl,rfl,
          (hActualFaceRadialSourceIncidence (k,i) u hle j.val j.property.1).mpr j.property.2⟩
        left_inv := ?_
        right_inv := ?_}⟩
      · rintro ⟨⟨⟨l,j⟩,r⟩,he,hj,hp⟩
        change l=k at he
        subst l
        change j=i at hj
        subst j
        rfl
      · intro j
        rfl
  have hActualIndexedRadialSourceCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      (actualIndexedCellEndpointIncidence k i
        (actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩) 0).card=
      (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.castSucc=u)).card := by
    calc
      _ = Fintype.card {f : actualNegativeFaceIntervals | f.1.1=k ∧ f.1.2=i ∧
          actualLocalContactArcs f 0=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = _ := (Fintype.card_congr (Classical.choice (hActualIndexedRadialSourceFiber k i u hle))).trans
        (Fintype.card_subtype _)
  have hActualIndexedRadialTargetFiber (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      Nonempty
        ({f : actualNegativeFaceIntervals | f.1.1=k ∧ f.1.2=i ∧
          actualLocalContactArcs f 1=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} ≃
        {j : Fin (actualFaceContactSize (k,i)+1) |
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.succ=u}) := by
    as_aux_lemma =>
      let toIndex := fun f : {f : actualNegativeFaceIntervals | f.1.1=k ∧ f.1.2=i ∧
            actualLocalContactArcs f 1=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} => by
        rcases f with ⟨⟨⟨l,j⟩,r⟩,he,hj,hp⟩
        change l=k at he
        subst l
        change j=i at hj
        subst j
        exact (⟨r.val,r.property,(hActualFaceRadialTargetIncidence (k,i) u hle r.val r.property).mp hp⟩ :
          {j : Fin (actualFaceContactSize (k,i)+1) |
            actualSourceFaceHeight (k,i) (actualIntervalMidpoint
              (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
            actualFaceContactMesh (k,i) j.succ=u})
      refine ⟨{
        toFun := toIndex
        invFun := fun j => ⟨⟨(k,i),⟨j.val,j.property.1⟩⟩,rfl,rfl,
          (hActualFaceRadialTargetIncidence (k,i) u hle j.val j.property.1).mpr j.property.2⟩
        left_inv := ?_
        right_inv := ?_}⟩
      · rintro ⟨⟨⟨l,j⟩,r⟩,he,hj,hp⟩
        change l=k at he
        subst l
        change j=i at hj
        subst j
        rfl
      · intro j
        rfl
  have hActualIndexedRadialTargetCount (k : actualActiveContactCells) (i : Fin 4)
      (u : Interval)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0) :
      (actualIndexedCellEndpointIncidence k i
        (actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩) 1).card=
      (Finset.univ.filter (fun j : Fin (actualFaceContactSize (k,i)+1) =>
          actualSourceFaceHeight (k,i) (actualIntervalMidpoint
            (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0 ∧
          actualFaceContactMesh (k,i) j.succ=u)).card := by
    calc
      _ = Fintype.card {f : actualNegativeFaceIntervals | f.1.1=k ∧ f.1.2=i ∧
          actualLocalContactArcs f 1=actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩} :=
        (Fintype.card_subtype _).symm
      _ = _ := (Fintype.card_congr (Classical.choice (hActualIndexedRadialTargetFiber k i u hle))).trans
        (Fintype.card_subtype _)
  have hActualCellEndpointIncidencePartitionsOverFourFaces
      (k : actualActiveContactCells) (x : Interval × Interval) (t : Interval) :
      (actualSourceCellEndpointIncidence k x t).card=
        ∑ i : Fin 4,(actualIndexedCellEndpointIncidence k i x t).card := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (s:=actualSourceCellEndpointIncidence k x t) (t:=(Finset.univ : Finset (Fin 4)))
      (f:=fun f : actualNegativeFaceIntervals => f.1.2)
      (fun _ _ => Finset.mem_univ _)
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,actualSourceCellEndpointIncidence,
      actualIndexedCellEndpointIncidence]
    constructor
    · rintro ⟨⟨hc,hp⟩,hi⟩
      exact ⟨hc,hi,hp⟩
    · rintro ⟨hc,hi,hp⟩
      exact ⟨⟨hc,hp⟩,hi⟩
  have hActualIndexedNegativeBoundaryRadialEndpointCountOne
      (k : actualActiveContactCells) (i : Fin 4) (u : Interval) (hu : u=0 ∨ u=1)
      (hle : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1/
        (actualCellCenters k.val).val.1≤0)
      (hneg : actualSourceFaceHeight (k,i) u<0) :
      (actualIndexedCellEndpointIncidence k i
        (actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩) 0).card+
      (actualIndexedCellEndpointIncidence k i
        (actualFaceContactRadial (k,i) ⟨actualBoundaryFace i u,hle⟩) 1).card=1 := by
    rw [hActualIndexedRadialSourceCount k i u hle,hActualIndexedRadialTargetCount k i u hle]
    have hsum := CurveComplex.LocalSurgery.actualMeshSourceTargetCardAdd (actualFaceContactSize (k,i))
      (actualFaceContactMesh (k,i)) (actualFaceContactMono (k,i))
      (fun j => actualSourceFaceHeight (k,i) (actualIntervalMidpoint
        (actualFaceContactMesh (k,i) j.castSucc) (actualFaceContactMesh (k,i) j.succ))<0) u
    rw [hsum]
    rcases hu with rfl | rfl
    · have hh := CurveComplex.LocalSurgery.actualNegativeFirstMeshNodeIncidenceOne
        (actualFaceContactSize (k,i)) (actualFaceContactMesh (k,i))
        (actualFaceContactMono (k,i)) (actualSourceFaceHeight (k,i))
        (hActualSourceMeshMidpointInterior (k,i)) (hActualSourceFaceHeightNoZero (k,i))
        (show actualSourceFaceHeight (k,i) (actualFaceContactMesh (k,i) 0)<0 by
          simpa only [actualFaceContactStart] using hneg)
      convert hh using 1
      all_goals congr 1
      all_goals ext j
      all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and,actualFaceContactStart]
      all_goals rfl
    · have hh := CurveComplex.LocalSurgery.actualNegativeLastMeshNodeIncidenceOne
        (actualFaceContactSize (k,i)) (actualFaceContactMesh (k,i))
        (actualFaceContactMono (k,i)) (actualSourceFaceHeight (k,i))
        (hActualSourceMeshMidpointInterior (k,i)) (hActualSourceFaceHeightNoZero (k,i))
        (show actualSourceFaceHeight (k,i) (actualFaceContactMesh (k,i) (Fin.last (actualFaceContactSize (k,i)+1)))<0 by
          simpa only [actualFaceContactEnd] using hneg)
      convert hh using 1
      all_goals congr 1
      all_goals ext j
      all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and,actualFaceContactEnd]
      all_goals rfl
  have hActualBoundaryFaceCornerParameterIsEndpoint (i j : Fin 4)
      (t u : Interval) (ht : t=0 ∨ t=1)
      (he : actualBoundaryFace j u=actualBoundaryFace i t) : u=0 ∨ u=1 := by
    as_aux_lemma =>
      exact CurveComplex.LocalSurgery.h1BoundaryCornerParameterIsEndpoint i j t u ht
        (congrArg Subtype.val he)
  have hActualBoundaryFaceCornerIncidentFacesTwo (i : Fin 4) (t : Interval)
      (ht : t=0 ∨ t=1) :
      (Finset.univ.filter (fun j : Fin 4 => ∃ u : Interval,
        (u=0 ∨ u=1) ∧ actualBoundaryFace j u=actualBoundaryFace i t)).card=2 := by
    as_aux_lemma =>
      have huniv : (Finset.univ : Finset (Fin 4))={0,1,2,3} := by
        ext j
        fin_cases j <;> simp
      have hreduce (j : Fin 4) :
          (∃ u : Interval,(u=0 ∨ u=1) ∧ actualBoundaryFace j u=actualBoundaryFace i t) ↔
          actualBoundaryFace j 0=actualBoundaryFace i t ∨
            actualBoundaryFace j 1=actualBoundaryFace i t := by
        constructor
        · rintro ⟨u,(rfl | rfl),hu⟩
          · exact Or.inl hu
          · exact Or.inr hu
        · rintro (h | h)
          · exact ⟨0,Or.inl rfl,h⟩
          · exact ⟨1,Or.inr rfl,h⟩
      simp_rw [hreduce]
      rcases ht with rfl | rfl <;> fin_cases i
      all_goals norm_num [huniv,actualBoundaryFace,actualBoundaryFaceRaw,
        Finset.filter_insert,Finset.filter_singleton]
  have hActualNegativeCornerIndexedFaceContribution
      (k : actualActiveContactCells) (i : Fin 4) (t : Interval) (ht : t=0 ∨ t=1)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0})
      (hz : z.val=actualBoundaryFace i t)
      (hneg : (actualCellBoundaryLoops k.val z.val).val.1/(actualCellCenters k.val).val.1<0)
      (j : Fin 4) :
      (actualIndexedCellEndpointIncidence k j (actualCompleteCellRadial k z) 0).card+
      (actualIndexedCellEndpointIncidence k j (actualCompleteCellRadial k z) 1).card=
        if ∃ u : Interval,(u=0 ∨ u=1) ∧ actualBoundaryFace j u=z.val then 1 else 0 := by
    as_aux_lemma =>
      by_cases hj : ∃ u : Interval,(u=0 ∨ u=1) ∧ actualBoundaryFace j u=z.val
      · rw [if_pos hj]
        obtain ⟨u,hu,hpoint⟩ := hj
        have hle : (actualCellBoundaryLoops k.val (actualBoundaryFace j u)).val.1/
            (actualCellCenters k.val).val.1≤0 := by
          have hh : (actualCellBoundaryLoops k.val z.val).val.1/
              (actualCellCenters k.val).val.1≤0 := z.property
          simpa only [hpoint] using hh
        have hnegative : actualSourceFaceHeight (k,j) u<0 := by
          change (actualCellBoundaryLoops k.val (actualBoundaryFace j u)).val.1/
            (actualCellCenters k.val).val.1<0
          simpa only [hpoint] using hneg
        let z' : {z : {z : ℝ × ℝ // ‖z‖=1} |
            (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0} :=
          ⟨actualBoundaryFace j u,hle⟩
        have hzz : z=z' := Subtype.ext hpoint.symm
        rw [hzz,hActualCompleteRadialMatchesFace k j z']
        exact hActualIndexedNegativeBoundaryRadialEndpointCountOne k j u hu hle hnegative
      · rw [if_neg hj]
        have hno (f : actualNegativeFaceIntervals) (r : Interval) (hr : r=0 ∨ r=1)
            (hcell : f.1.1=k) (hface : f.1.2=j)
            (hpoint : actualLocalContactArcs f r=actualCompleteCellRadial k z) : False := by
          subst k
          rcases hr with rfl | rfl
          · have he : actualCompleteCellRadial f.1.1 (actualLocalContactArcStart f)=
                actualCompleteCellRadial f.1.1 z :=
              (hActualCompleteRadialMatchesFace f.1.1 f.1.2 (actualLocalContactArcStart f)).trans
                ((hActualLocalContactArcStart f).symm.trans hpoint)
            have hez := hActualCompleteCellRadialInjective f.1.1 he
            have hboundary : actualBoundaryFace f.1.2
                (actualFaceContactMesh f.1 f.2.val.castSucc)=z.val :=
              (hActualLocalContactArcStartFace f).symm.trans (congrArg Subtype.val hez)
            have hend := hActualBoundaryFaceCornerParameterIsEndpoint i f.1.2 t
              (actualFaceContactMesh f.1 f.2.val.castSucc) ht (hboundary.trans hz)
            have hboundary' : actualBoundaryFace j (actualFaceContactMesh f.1 f.2.val.castSucc)=z.val :=
              (congrArg (fun l : Fin 4 => actualBoundaryFace l
                (actualFaceContactMesh f.1 f.2.val.castSucc)) hface).symm.trans hboundary
            exact hj ⟨actualFaceContactMesh f.1 f.2.val.castSucc,hend,hboundary'⟩
          · have he : actualCompleteCellRadial f.1.1 (actualLocalContactArcEnd f)=
                actualCompleteCellRadial f.1.1 z :=
              (hActualCompleteRadialMatchesFace f.1.1 f.1.2 (actualLocalContactArcEnd f)).trans
                ((hActualLocalContactArcEnd f).symm.trans hpoint)
            have hez := hActualCompleteCellRadialInjective f.1.1 he
            have hboundary : actualBoundaryFace f.1.2
                (actualFaceContactMesh f.1 f.2.val.succ)=z.val :=
              (hActualLocalContactArcEndFace f).symm.trans (congrArg Subtype.val hez)
            have hend := hActualBoundaryFaceCornerParameterIsEndpoint i f.1.2 t
              (actualFaceContactMesh f.1 f.2.val.succ) ht (hboundary.trans hz)
            have hboundary' : actualBoundaryFace j (actualFaceContactMesh f.1 f.2.val.succ)=z.val :=
              (congrArg (fun l : Fin 4 => actualBoundaryFace l
                (actualFaceContactMesh f.1 f.2.val.succ)) hface).symm.trans hboundary
            exact hj ⟨actualFaceContactMesh f.1 f.2.val.succ,hend,hboundary'⟩
        have hzero (r : Interval) (hr : r=0 ∨ r=1) :
            actualIndexedCellEndpointIncidence k j (actualCompleteCellRadial k z) r=∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro f hf
          simp only [actualIndexedCellEndpointIncidence,Finset.mem_filter,Finset.mem_univ,true_and] at hf
          exact hno f r hr hf.1 hf.2.1 hf.2.2
        rw [hzero 0 (Or.inl rfl),hzero 1 (Or.inr rfl),Finset.card_empty]
  have hActualNegativeRadialCornerCellEndpointCountTwo
      (k : actualActiveContactCells) (i : Fin 4) (t : Interval) (ht : t=0 ∨ t=1)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0})
      (hz : z.val=actualBoundaryFace i t)
      (hneg : (actualCellBoundaryLoops k.val z.val).val.1/(actualCellCenters k.val).val.1<0) :
      (actualSourceCellEndpointIncidence k (actualCompleteCellRadial k z) 0).card+
      (actualSourceCellEndpointIncidence k (actualCompleteCellRadial k z) 1).card=2 := by
    as_aux_lemma =>
      rw [hActualCellEndpointIncidencePartitionsOverFourFaces k _ 0,
        hActualCellEndpointIncidencePartitionsOverFourFaces k _ 1,←Finset.sum_add_distrib]
      calc
        _ = ∑ j : Fin 4,if ∃ u : Interval,(u=0 ∨ u=1) ∧ actualBoundaryFace j u=z.val then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hActualNegativeCornerIndexedFaceContribution k i t ht z hz hneg j
        _ = (Finset.univ.filter (fun j : Fin 4 => ∃ u : Interval,
            (u=0 ∨ u=1) ∧ actualBoundaryFace j u=z.val)).card := by
          simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
        _ = 2 := by
          simpa only [hz] using hActualBoundaryFaceCornerIncidentFacesTwo i t ht
  have hActualNegativeRadialCornerGraphVertexDegreeTwo
      (k : actualActiveContactCells) (i : Fin 4) (t : Interval) (ht : t=0 ∨ t=1)
      (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
        (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0})
      (hz : z.val=actualBoundaryFace i t)
      (hneg : (actualCellBoundaryLoops k.val z.val).val.1/(actualCellCenters k.val).val.1<0)
      (w : actualContactVertices) (hw : w.val=actualAffineCells k.val (actualCompleteCellRadial k z)) :
      actualZeroGraph.degree (Sum.inl w)=2 := by
    as_aux_lemma =>
      have hcount (r : Interval) :
          (Finset.univ.filter (fun f : actualNegativeFaceIntervals =>
            actualGlobalContactArcs f r=actualAffineCells k.val (actualCompleteCellRadial k z))).card=
          (actualSourceCellEndpointIncidence k (actualCompleteCellRadial k z) r).card := by
        rw [←hActualGlobalCellEndpointCountAsLocal k r (actualCompleteCellRadial k z)]
        congr 1
        ext f
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · intro hf
          refine ⟨hf,hActualNegativeRadialContactCellUnique f r k 0 z hneg ?_⟩
          exact hf.trans (congrArg (actualAffineCells k.val) (hActualCompleteRadialMatchesFace k 0 z))
        · exact And.left
      rw [hActualGraphEndpointDegreeAsGlobalArcCounts w,hw,hcount 0,hcount 1]
      exact hActualNegativeRadialCornerCellEndpointCountTwo k i t ht z hz hneg
  have hActualOddRadialMeshNodeIsSourceRoot
      (k : actualActiveContactCells) (i : Fin 4)
      (q : Fin (actualFaceContactSize (k,i)+2))
      (hle : (actualCellBoundaryLoops k.val
        (actualBoundaryFace i (actualFaceContactMesh (k,i) q))).val.1/
        (actualCellCenters k.val).val.1≤0)
      (w : actualContactVertices)
      (hw : w.val=actualAffineCells k.val (actualFaceContactRadial (k,i)
        ⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩))
      (hodd : Odd (actualZeroGraph.degree (Sum.inl w))) :
      (actualCellBoundaryLoops k.val
        (actualBoundaryFace i (actualFaceContactMesh (k,i) q))).val.1=0 := by
    as_aux_lemma =>
      have hnot := Nat.not_even_iff_odd.mpr hodd
      have hratio : actualSourceFaceHeight (k,i) (actualFaceContactMesh (k,i) q)=0 := by
        by_contra hn
        have hneg : actualSourceFaceHeight (k,i) (actualFaceContactMesh (k,i) q)<0 :=
          lt_of_le_of_ne hle hn
        have hdegree : actualZeroGraph.degree (Sum.inl w)=2 := by
          by_cases hq₀ : q=0
          · have hparam : actualFaceContactMesh (k,i) q=0 := by rw [hq₀,actualFaceContactStart]
            let z := (⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩ :
              {z : {z : ℝ × ℝ // ‖z‖=1} |
                (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0})
            apply hActualNegativeRadialCornerGraphVertexDegreeTwo k i _ (Or.inl hparam) z rfl hneg w
            exact hw.trans (congrArg (actualAffineCells k.val) (hActualCompleteRadialMatchesFace k i z).symm)
          · by_cases hq₁ : q=Fin.last (actualFaceContactSize (k,i)+1)
            · have hparam : actualFaceContactMesh (k,i) q=1 := by rw [hq₁,actualFaceContactEnd]
              let z := (⟨actualBoundaryFace i (actualFaceContactMesh (k,i) q),hle⟩ :
                {z : {z : ℝ × ℝ // ‖z‖=1} |
                  (actualCellBoundaryLoops k.val z).val.1/(actualCellCenters k.val).val.1≤0})
              apply hActualNegativeRadialCornerGraphVertexDegreeTwo k i _ (Or.inr hparam) z rfl hneg w
              exact hw.trans (congrArg (actualAffineCells k.val) (hActualCompleteRadialMatchesFace k i z).symm)
            · have hu : actualFaceContactMesh (k,i) q∈Set.Ioo (0 : Interval) 1 := by
                constructor
                · rw [←actualFaceContactStart (k,i)]
                  exact actualFaceContactMono (k,i) (Fin.pos_iff_ne_zero.mpr hq₀)
                · rw [←actualFaceContactEnd (k,i)]
                  apply actualFaceContactMono (k,i)
                  exact lt_of_le_of_ne (Fin.le_last q) hq₁
              exact hActualInternalNegativeRadialGraphVertexDegreeTwo k i q hq₀ hq₁ hu hle hneg w hw
        apply hnot
        rw [hdegree]
        exact ⟨1,by omega⟩
      have hc : (actualCellCenters k.val).val.1≠0 :=
        (hActualCellCenterAxisOff k.val).resolve_left k.property
      exact (div_eq_zero_iff.mp hratio).resolve_right hc
  have hActualOddContactVertexHasActualSourceRootRepresentation
      (w : actualContactVertices) (hodd : Odd (actualZeroGraph.degree (Sum.inl w))) :
      ∃ k : actualActiveContactCells,∃ i : Fin 4,
        ∃ q : Fin (actualFaceContactSize (k,i)+2),
        (actualCellBoundaryLoops k.val (actualBoundaryFace i (actualFaceContactMesh (k,i) q))).val.1=0 ∧
        w.val=actualAffineCells k.val (squareCoordinates
          ⟨(actualBoundaryFace i (actualFaceContactMesh (k,i) q)).val,
            (actualBoundaryFace i (actualFaceContactMesh (k,i) q)).property.le⟩) := by
    as_aux_lemma =>
      obtain ⟨f,hf⟩ := hActualOddContactVertexHasActualArcEndpoint w hodd
      have fromEndpoint (q : Fin (actualFaceContactSize f.1+2))
          (z : {z : {z : ℝ × ℝ // ‖z‖=1} |
            (actualCellBoundaryLoops f.1.1.val z).val.1/(actualCellCenters f.1.1.val).val.1≤0})
          (hz : z.val=actualBoundaryFace f.1.2 (actualFaceContactMesh f.1 q))
          (hw : w.val=actualAffineCells f.1.1.val (actualCompleteCellRadial f.1.1 z)) :
          ∃ k : actualActiveContactCells,∃ i : Fin 4,
            ∃ q : Fin (actualFaceContactSize (k,i)+2),
            (actualCellBoundaryLoops k.val (actualBoundaryFace i (actualFaceContactMesh (k,i) q))).val.1=0 ∧
            w.val=actualAffineCells k.val (squareCoordinates
              ⟨(actualBoundaryFace i (actualFaceContactMesh (k,i) q)).val,
                (actualBoundaryFace i (actualFaceContactMesh (k,i) q)).property.le⟩) := by
        have hle : (actualCellBoundaryLoops f.1.1.val
            (actualBoundaryFace f.1.2 (actualFaceContactMesh f.1 q))).val.1/
            (actualCellCenters f.1.1.val).val.1≤0 := by rw [←hz];exact z.property
        let z' := (⟨actualBoundaryFace f.1.2 (actualFaceContactMesh f.1 q),hle⟩ :
          {z : {z : ℝ × ℝ // ‖z‖=1} |
            (actualCellBoundaryLoops f.1.1.val z).val.1/(actualCellCenters f.1.1.val).val.1≤0})
        have hzz : z=z' := Subtype.ext hz
        have hhw : w.val=actualAffineCells f.1.1.val (actualFaceContactRadial f.1 z') := by
          rw [hzz,hActualCompleteRadialMatchesFace] at hw
          exact hw
        have hroot := hActualOddRadialMeshNodeIsSourceRoot f.1.1 f.1.2 q hle w hhw hodd
        refine ⟨f.1.1,f.1.2,q,hroot,?_⟩
        obtain ⟨v,hv,hvr⟩ := hActualCompleteCellRadialFormula f.1.1 z'
        have hroot' : (actualCellBoundaryLoops f.1.1.val z'.val).val.1=0 := hroot
        have hv' : v=⟨z'.val.val,z'.val.property.le⟩ := by
          apply Subtype.ext
          simpa [hroot'] using hvr
        rw [hzz] at hw
        exact hw.trans (congrArg (actualAffineCells f.1.1.val)
          (hv.trans (congrArg squareCoordinates hv')))
      rcases hf with hf | hf
      · apply fromEndpoint f.2.val.castSucc (actualLocalContactArcStart f)
          (hActualLocalContactArcStartFace f)
        change actualAffineCells f.1.1.val (actualLocalContactArcs f 0)=w.val at hf
        exact hf.symm.trans (congrArg (actualAffineCells f.1.1.val)
          ((hActualLocalContactArcStart f).trans
            (hActualCompleteRadialMatchesFace f.1.1 f.1.2 (actualLocalContactArcStart f)).symm))
      · apply fromEndpoint f.2.val.succ (actualLocalContactArcEnd f)
          (hActualLocalContactArcEndFace f)
        change actualAffineCells f.1.1.val (actualLocalContactArcs f 1)=w.val at hf
        exact hf.symm.trans (congrArg (actualAffineCells f.1.1.val)
          ((hActualLocalContactArcEnd f).trans
            (hActualCompleteRadialMatchesFace f.1.1 f.1.2 (actualLocalContactArcEnd f)).symm))
  have hActualSourceFaceRootParameterInterior (k : actualActiveContactCells)
      (i : Fin 4) (u : Interval)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0) :
      u∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      let x := squareCoordinates ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩
      have hraw : ((actualContactGridCharts k.val) (actualConeCells k.val x)).1=0 :=
        (congrArg Prod.fst (hActualCellBoundaryLoopFormula k.val (actualBoundaryFace i u))).trans hroot
      have hmem : actualConeCells k.val x∈a.val.image :=
        ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
          (hActualConeCellRange k.val x)).mpr hraw
      change actualConeCells k.val (squareCoordinates
        ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩)∈a.val.image at hmem
      have hcorners := hActualConstructedCellCornersOff k.val
      have hnoends : ¬(u=0 ∨ u=1) := by
        rintro (rfl | rfl)
        · fin_cases i
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 0 0).val,(actualBoundaryFace 0 0).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFace0Coordinates] at hmem
            exact hcorners.1 hmem
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 1 0).val,(actualBoundaryFace 1 0).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFaceOneCoordinates] at hmem
            exact hcorners.2.1 hmem
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 2 0).val,(actualBoundaryFace 2 0).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFace2Coordinates] at hmem
            exact hcorners.2.2.1 hmem
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 3 0).val,(actualBoundaryFace 3 0).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFaceThreeCoordinates] at hmem
            exact hcorners.1 hmem
        · fin_cases i
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 0 1).val,(actualBoundaryFace 0 1).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFace0Coordinates] at hmem
            exact hcorners.2.1 hmem
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 1 1).val,(actualBoundaryFace 1 1).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFaceOneCoordinates] at hmem
            exact hcorners.2.2.2 hmem
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 2 1).val,(actualBoundaryFace 2 1).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFace2Coordinates] at hmem
            exact hcorners.2.2.2 hmem
          · change actualConeCells k.val (squareCoordinates
              ⟨(actualBoundaryFace 3 1).val,(actualBoundaryFace 3 1).property.le⟩)∈a.val.image at hmem
            rw [hActualBoundaryFaceThreeCoordinates] at hmem
            exact hcorners.2.2.1 hmem
      exact ⟨lt_of_le_of_ne (show (0 : Interval)≤u from u.property.1)
        (fun h => hnoends (Or.inl h.symm)),
        lt_of_le_of_ne (show u≤(1 : Interval) from u.property.2)
        (fun h => hnoends (Or.inr h))⟩
  have hActualOddSourceRootFaceIsOnOuterMeshBoundary
      (k : actualActiveContactCells) (i : Fin 4) (u : Interval)
      (hroot : (actualCellBoundaryLoops k.val (actualBoundaryFace i u)).val.1=0)
      (w : actualContactVertices)
      (hw : w.val=actualAffineCells k.val (squareCoordinates
        ⟨(actualBoundaryFace i u).val,(actualBoundaryFace i u).property.le⟩))
      (hodd : Odd (actualZeroGraph.degree (Sum.inl w))) :
      (i=0 ∧ k.val.2=0) ∨ (i=1 ∧ k.val.1=Fin.last actualContactGridSize) ∨
        (i=2 ∧ k.val.2=Fin.last actualContactGridSize) ∨ (i=3 ∧ k.val.1=0) := by
    as_aux_lemma =>
      have hu := hActualSourceFaceRootParameterInterior k i u hroot
      have hnot := Nat.not_even_iff_odd.mpr hodd
      fin_cases i
      · change (actualCellBoundaryLoops k.val (actualBoundaryFace 0 u)).val.1=0 at hroot
        change w.val=actualAffineCells k.val (squareCoordinates
          ⟨(actualBoundaryFace 0 u).val,(actualBoundaryFace 0 u).property.le⟩) at hw
        rw [hActualBoundaryFace0Coordinates] at hw
        by_cases houter : k.val.2=0
        · exact Or.inl ⟨rfl,houter⟩
        · exfalso
          have hmem : actualCellBottomEdge k.val u∈a.val.image := by
            apply ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
              (hActualCellBottomRange k.val ⟨u,rfl⟩)).mpr
            exact (hActualSourceFaceBottomRawFormula k u).symm.trans hroot
          have hpos : 0<k.val.2.val := Fin.pos_iff_ne_zero.mpr houter
          let r : Fin actualContactGridSize := ⟨k.val.2.val-1,by have hh := k.val.2.isLt;omega⟩
          have hr : r.succ=k.val.2 := by apply Fin.ext;dsimp [r];omega
          have hm : actualCellTopEdge (k.val.1,r.castSucc) u∈a.val.image := by
            rw [hActualHorizontalCellSharedTrace k.val.1 r u,hr]
            exact hmem
          have hp : w.val=actualAffineCells (k.val.1,r.castSucc) (u,1) := by
            rw [hActualHorizontalAffineCellSeam k.val.1 r u,hr]
            exact hw
          exact hnot (hActualInternalHorizontalContactVertexDegreeEven k.val.1 r u hu hm w hp)
      · change (actualCellBoundaryLoops k.val (actualBoundaryFace 1 u)).val.1=0 at hroot
        change w.val=actualAffineCells k.val (squareCoordinates
          ⟨(actualBoundaryFace 1 u).val,(actualBoundaryFace 1 u).property.le⟩) at hw
        rw [hActualBoundaryFaceOneCoordinates] at hw
        by_cases houter : k.val.1=Fin.last actualContactGridSize
        · exact Or.inr (Or.inl ⟨rfl,houter⟩)
        · exfalso
          have hmem : actualCellRightEdge k.val u∈a.val.image := by
            apply ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
              (hActualCellRightRange k.val ⟨u,rfl⟩)).mpr
            exact (hActualSourceFaceRightRawFormula k u).symm.trans hroot
          have hlt : k.val.1.val<actualContactGridSize := by
            have hh := k.val.1.isLt
            have hne : k.val.1.val≠actualContactGridSize := by
              intro he;apply houter;apply Fin.ext;exact he
            omega
          let r : Fin actualContactGridSize := ⟨k.val.1.val,hlt⟩
          have hr : r.castSucc=k.val.1 := by apply Fin.ext;rfl
          have hm : actualCellRightEdge (r.castSucc,k.val.2) u∈a.val.image := by
            rw [hr]
            exact hmem
          have hp : w.val=actualAffineCells (r.castSucc,k.val.2) (1,u) := by
            rw [hr]
            exact hw
          exact hnot (hActualInternalVerticalContactVertexDegreeEven r k.val.2 u hu hm w hp)
      · change (actualCellBoundaryLoops k.val (actualBoundaryFace 2 u)).val.1=0 at hroot
        change w.val=actualAffineCells k.val (squareCoordinates
          ⟨(actualBoundaryFace 2 u).val,(actualBoundaryFace 2 u).property.le⟩) at hw
        rw [hActualBoundaryFace2Coordinates] at hw
        by_cases houter : k.val.2=Fin.last actualContactGridSize
        · exact Or.inr (Or.inr (Or.inl ⟨rfl,houter⟩))
        · exfalso
          have hmem : actualCellTopEdge k.val u∈a.val.image := by
            apply ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
              (hActualCellTopRange k.val ⟨u,rfl⟩)).mpr
            exact (hActualSourceFaceTopRawFormula k u).symm.trans hroot
          have hlt : k.val.2.val<actualContactGridSize := by
            have hh := k.val.2.isLt
            have hne : k.val.2.val≠actualContactGridSize := by
              intro he;apply houter;apply Fin.ext;exact he
            omega
          let r : Fin actualContactGridSize := ⟨k.val.2.val,hlt⟩
          have hr : r.castSucc=k.val.2 := by apply Fin.ext;rfl
          have hm : actualCellTopEdge (k.val.1,r.castSucc) u∈a.val.image := by
            rw [hr]
            exact hmem
          have hp : w.val=actualAffineCells (k.val.1,r.castSucc) (u,1) := by
            rw [hr]
            exact hw
          exact hnot (hActualInternalHorizontalContactVertexDegreeEven k.val.1 r u hu hm w hp)
      · change (actualCellBoundaryLoops k.val (actualBoundaryFace 3 u)).val.1=0 at hroot
        change w.val=actualAffineCells k.val (squareCoordinates
          ⟨(actualBoundaryFace 3 u).val,(actualBoundaryFace 3 u).property.le⟩) at hw
        rw [hActualBoundaryFaceThreeCoordinates] at hw
        by_cases houter : k.val.1=0
        · exact Or.inr (Or.inr (Or.inr ⟨rfl,houter⟩))
        · exfalso
          have hmem : actualCellLeftEdge k.val u∈a.val.image := by
            apply ((hActualContactGridChartData k.val).2.2.resolve_left k.property _
              (hActualCellLeftRange k.val ⟨u,rfl⟩)).mpr
            exact (hActualSourceFaceLeftRawFormula k u).symm.trans hroot
          have hpos : 0<k.val.1.val := Fin.pos_iff_ne_zero.mpr houter
          let r : Fin actualContactGridSize := ⟨k.val.1.val-1,by have hh := k.val.1.isLt;omega⟩
          have hr : r.succ=k.val.1 := by apply Fin.ext;dsimp [r];omega
          have hm : actualCellRightEdge (r.castSucc,k.val.2) u∈a.val.image := by
            rw [hActualVerticalCellSharedTrace r k.val.2 u,hr]
            exact hmem
          have hp : w.val=actualAffineCells (r.castSucc,k.val.2) (1,u) := by
            rw [hActualVerticalAffineCellSeam r k.val.2 u,hr]
            exact hw
          exact hnot (hActualInternalVerticalContactVertexDegreeEven r k.val.2 u hu hm w hp)
  have hActualOddContactVertexLiesOnOriginalOuterBoundary
      (w : actualContactVertices) (hodd : Odd (actualZeroGraph.degree (Sum.inl w))) :
      w.val.1=0 ∨ w.val.1=1 ∨ w.val.2=0 ∨ w.val.2=1 := by
    as_aux_lemma =>
      obtain ⟨k,i,q,hroot,hw⟩ := hActualOddContactVertexHasActualSourceRootRepresentation w hodd
      let u := actualFaceContactMesh (k,i) q
      have houter := hActualOddSourceRootFaceIsOnOuterMeshBoundary k i u hroot w hw hodd
      rcases houter with ⟨rfl,hk⟩ | ⟨rfl,hk⟩ | ⟨rfl,hk⟩ | ⟨rfl,hk⟩
      · right;right;left
        rw [hw,hActualBoundaryFace0Coordinates,hActualAffineCellFormula]
        apply Subtype.ext
        change (1-(0 : ℝ))*(actualContactGridParameter k.val.2.castSucc).val+
          0*(actualContactGridParameter k.val.2.succ).val=0
        have he : k.val.2.castSucc=0 := by rw [hk];rfl
        rw [he,hActualContactGridZero]
        norm_num
      · right;left
        rw [hw,hActualBoundaryFaceOneCoordinates,hActualAffineCellFormula]
        apply Subtype.ext
        change (1-(1 : ℝ))*(actualContactGridParameter k.val.1.castSucc).val+
          1*(actualContactGridParameter k.val.1.succ).val=1
        have he : k.val.1.succ=Fin.last (actualContactGridSize+1) := by rw [hk];rfl
        rw [he,hActualContactGridOne]
        norm_num
      · right;right;right
        rw [hw,hActualBoundaryFace2Coordinates,hActualAffineCellFormula]
        apply Subtype.ext
        change (1-(1 : ℝ))*(actualContactGridParameter k.val.2.castSucc).val+
          1*(actualContactGridParameter k.val.2.succ).val=1
        have he : k.val.2.succ=Fin.last (actualContactGridSize+1) := by rw [hk];rfl
        rw [he,hActualContactGridOne]
        norm_num
      · left
        rw [hw,hActualBoundaryFaceThreeCoordinates,hActualAffineCellFormula]
        apply Subtype.ext
        change (1-(0 : ℝ))*(actualContactGridParameter k.val.1.castSucc).val+
          0*(actualContactGridParameter k.val.1.succ).val=0
        have he : k.val.1.castSucc=0 := by rw [hk];rfl
        rw [he,hActualContactGridZero]
        norm_num
  have hActualOddContactVertexOnInitialBoundaryOrMarkedTailSides
      (w : actualContactVertices) (hodd : Odd (actualZeroGraph.degree (Sum.inl w))) :
      w.val.1=0 ∨ w.val.2=0 ∨ w.val.2=1 := by
    as_aux_lemma =>
      have hnotterminal : w.val.1≠1 := by
        intro ht
        have he : w.val=(1,w.val.2) := Prod.ext ht rfl
        have hm := hActualContactVerticesImage w
        rw [he] at hm
        exact hActualFiniteConeSweepTopAvoids w.val.2 hm
      rcases hActualOddContactVertexLiesOnOriginalOuterBoundary w hodd with h | h | h | h
      · exact Or.inl h
      · exact False.elim (hnotterminal h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hActualSpecifiedCrossingProducesBoundaryLocalizedOriginalContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        (z.val.1=0 ∨ z.val.2=0 ∨ z.val.2=1) ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,q,hq,κ,hκ,hinside⟩ :=
        hActualSpecifiedCrossingProducesOriginalParameterContactPath
      exact ⟨w,z,hw,hleft,hzw,hodd,
        hActualOddContactVertexOnInitialBoundaryOrMarkedTailSides z hodd,q,hq,κ,hκ,hinside⟩
  have hActualClosedOldArcContactPathHasOriginalParameters
      (x y : S) (q : Path x y) (hcontact : range q⊆a.val.image) :
      ∃ κ : C(Interval,Interval),∀ t,a.val.map (κ t)=q t := by
    as_aux_lemma =>
      let R := Set.range a.val.map
      let H := (NonLoopArc.isEmbedding (⟨a.val,hane⟩ : NonLoopArc M)).toHomeomorph
      let r : C(Interval,R) :=
        ⟨fun t => ⟨q t,hcontact ⟨t,rfl⟩⟩,q.continuous.subtype_mk _⟩
      let κ : C(Interval,Interval) :=
        ⟨fun t => H.symm (r t),H.symm.continuous.comp r.continuous⟩
      exact ⟨κ,fun t => congrArg Subtype.val (H.apply_symm_apply (r t))⟩
  have hActualSharedStartAffineProducerSuppliesOriginalClosedContactTails
      (hshared : b.val.map 0=af 0) :
      ∃ (d : ℝ) (hd : 0<d) (hd1 : d<1),
      ∃ K : C(Interval × (Interval × Icc (0:ℝ) d),S),
      ∃ lo hi : ℤ,∃ γ : {k : ℤ // k∈Finset.Icc lo (hi-1)} → C(Ioc (0:ℝ) d,Interval),
        (∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0) ∧
        (∀ z,0<z.2.2.val → K z∉(M.cover.branch : Set S)) ∧
        (∀ z,K (0,z)=F (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans hd1.le⟩)) ∧
        (∀ η τ t,τ=0 ∨ τ=1 → K (η,(τ,t))=
          F (τ,⟨t.val,t.property.1,t.property.2.trans hd1.le⟩)) ∧
        (∀ k t,0<(γ k t).val ∧ (γ k t).val<1) ∧
        (∀ k,IsEmbedding (fun t => (γ k t,t))) ∧
        (∀ t,Function.Injective (fun k => γ k t)) ∧
        ∀ k,∃ f : Path (af 0) (K (1,(γ k ⟨d/2,half_pos hd,half_le_self hd.le⟩,
          ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))),
          range f⊆a.val.image ∧
          (∀ t : Interval,t≠0 → f t∉(M.cover.branch : Set S)) ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=f t) ∧
            (κ 0=0 ∨ κ 0=1) ∧
            ∀ t : Interval,t≠0 → κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨d,hd,hd1,n₀,n₁,L,K,hstripes,hsource,hunit,hzero,hmarks,hinitial,houter,hboundary,hinner⟩ :=
        hactualSharedStartAffineMarkedPointExtension hshared
      let left : C(Ioc (0:ℝ) d,ℝ) := ⟨fun t => (L (0,t)).im,by fun_prop⟩
      let right : C(Ioc (0:ℝ) d,ℝ) := ⟨fun t => (L (1,t)).im,by fun_prop⟩
      obtain ⟨lo,hi,γ,hstrict,hlevels,hgraph,hsolve⟩ := hfiniteUnorderedLevels left right n₀ n₁
        (fun t => (hstripes t).1) (fun t => (hstripes t).2)
      have hγinjective (t : Ioc (0:ℝ) d) : Function.Injective (fun k => γ k t) := by
        intro j k he
        have hj := hlevels j t
        have hk := hlevels k t
        change γ j t=γ k t at he
        rw [he] at hj
        have hc : (j.val:ℝ)=(k.val:ℝ) := mul_right_cancel₀
          (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos))
          (by linarith only [hj,hk])
        exact Subtype.ext (Int.cast_injective hc)
      refine ⟨d,hd,hd1,K,lo,hi,γ,hzero,hmarks,hinitial,hboundary,hstrict,hgraph,hγinjective,?_⟩
      intro k
      obtain ⟨f,hf,htrace⟩ := hActualSharedAffineLevelGraphClosesAtOriginalMark
        d hd hd1 L K hsource hunit hzero hinner k.val (γ k) (hlevels k)
      obtain ⟨κ,hκ⟩ := hActualClosedOldArcContactPathHasOriginalParameters _ _ f hf
      have havoid (t : Interval) (ht : t≠0) : f t∉(M.cover.branch : Set S) := by
        rw [htrace ⟨t,ht⟩]
        exact hmarks _ (mul_pos (half_pos hd)
          (lt_of_le_of_ne t.property.1 (fun h => ht (Subtype.ext h.symm))))
      have hκzero : κ 0=0 ∨ κ 0=1 := by
        have h := (hκ 0).trans f.source
        rcases hAFEnds with ⟨hstart,_⟩ | ⟨hstart,_⟩
        · exact Or.inl ((NonLoopArc.injective ⟨a.val,hane⟩) (h.trans hstart))
        · exact Or.inr ((NonLoopArc.injective ⟨a.val,hane⟩) (h.trans hstart))
      refine ⟨f,hf,havoid,κ,hκ,hκzero,?_⟩
      intro t ht
      have hlo : κ t≠0 := by
        intro he
        have hh := hκ t
        rw [he] at hh
        exact havoid t ht (hh ▸ a.val.start_marked)
      have hhi : κ t≠1 := by
        intro he
        have hh := hκ t
        rw [he] at hh
        exact havoid t ht (hh ▸ a.val.end_marked)
      exact ⟨lt_of_le_of_ne (κ t).property.1 (Ne.symm hlo),
        lt_of_le_of_ne (κ t).property.2 hhi⟩
  have hActualOriginalStartMarkedParameterPathStraightensInRetainedStartCarrier
      (markedArc : M.EssentialMarkedArc)
      (κ : C(Interval,Interval)) (hκ : ∀ t,κ t∈Set.Ico (0 : Interval) 1) :
      ∃ (hx : markedArc.val.map (κ 0)∈((M.cover.branch : Set S)\{markedArc.val.map 0})ᶜ)
        (hy : markedArc.val.map (κ 1)∈((M.cover.branch : Set S)\{markedArc.val.map 0})ᶜ)
        (α β : Path (⟨markedArc.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{markedArc.val.map 0})ᶜ)
          ⟨markedArc.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=markedArc.val.map (κ t)) ∧
        (∀ t,(β t : S)=markedArc.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let J := Set.Ico (0 : ℝ) 1
      let x : J := ⟨(κ 0).val,hκ 0⟩
      let y : J := ⟨(κ 1).val,hκ 1⟩
      let r : Path x y := {
        toFun := fun t => ⟨(κ t).val,hκ t⟩
        continuous_toFun := (continuous_subtype_val.comp κ.continuous).subtype_mk hκ
        source' := rfl
        target' := rfl }
      have hseg (t : Interval) : (actualIntervalSegment (κ 0) (κ 1) t).val∈J := by
        have hx₀ : 0≤(κ 0).val := (hκ 0).1
        have hx₁ : (κ 0).val<1 := (hκ 0).2
        have hy₀ : 0≤(κ 1).val := (hκ 1).1
        have hy₁ : (κ 1).val<1 := (hκ 1).2
        change 0≤(1-t.val)*(κ 0).val+t.val*(κ 1).val ∧
          (1-t.val)*(κ 0).val+t.val*(κ 1).val<1
        simpa only [smul_eq_mul,Set.mem_Ico] using (convex_Ico (0 : ℝ) 1) (show (κ 0).val∈Set.Ico (0 : ℝ) 1 from ⟨hx₀,hx₁⟩) (show (κ 1).val∈Set.Ico (0 : ℝ) 1 from ⟨hy₀,hy₁⟩) (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
      let s : Path x y := {
        toFun := fun t => ⟨(actualIntervalSegment (κ 0) (κ 1) t).val,hseg t⟩
        continuous_toFun := (continuous_subtype_val.comp (actualIntervalSegment (κ 0) (κ 1)).continuous).subtype_mk hseg
        source' := by apply Subtype.ext;change (1-(0 : ℝ))*(κ 0).val+0*(κ 1).val=(κ 0).val;ring
        target' := by apply Subtype.ext;change (1-(1 : ℝ))*(κ 0).val+1*(κ 1).val=(κ 1).val;ring }
      let inc : C(J,Interval) := ⟨fun t => ⟨t.val,t.property.1,t.property.2.le⟩,
        continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1,t.property.2.le⟩)⟩
      let T := ((M.cover.branch : Set S)\{markedArc.val.map 0})ᶜ
      have htarget (t : J) : markedArc.val.map (inc t)∈T := by
        intro hm
        rcases markedArc.val.marked_only_at_ends (inc t) hm.1 with he | he
        · exact hm.2 (show markedArc.val.map (inc t)∈{markedArc.val.map 0} from he ▸ rfl)
        · have hv := congrArg Subtype.val he
          exact (ne_of_lt t.property.2) hv
      let A : C(J,T) := ⟨fun t => ⟨markedArc.val.map (inc t),htarget t⟩,
        (markedArc.val.continuous.comp inc.continuous).subtype_mk htarget⟩
      letI : ContractibleSpace J := (convex_Ico (0 : ℝ) 1).contractibleSpace ⟨x,x.property⟩
      have hhom : r.Homotopic s := SimplyConnectedSpace.paths_homotopic r s
      exact ⟨htarget x,htarget y,r.map A.continuous,s.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualOriginalEndMarkedParameterPathStraightensInRetainedEndCarrier
      (markedArc : M.EssentialMarkedArc)
      (κ : C(Interval,Interval)) (hκ : ∀ t,κ t∈Set.Ioc (0 : Interval) 1) :
      ∃ (hx : markedArc.val.map (κ 0)∈((M.cover.branch : Set S)\{markedArc.val.map 1})ᶜ)
        (hy : markedArc.val.map (κ 1)∈((M.cover.branch : Set S)\{markedArc.val.map 1})ᶜ)
        (α β : Path (⟨markedArc.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{markedArc.val.map 1})ᶜ)
          ⟨markedArc.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=markedArc.val.map (κ t)) ∧
        (∀ t,(β t : S)=markedArc.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let J := Set.Ioc (0 : ℝ) 1
      let x : J := ⟨(κ 0).val,hκ 0⟩
      let y : J := ⟨(κ 1).val,hκ 1⟩
      let r : Path x y := {
        toFun := fun t => ⟨(κ t).val,hκ t⟩
        continuous_toFun := (continuous_subtype_val.comp κ.continuous).subtype_mk hκ
        source' := rfl
        target' := rfl }
      have hseg (t : Interval) : (actualIntervalSegment (κ 0) (κ 1) t).val∈J := by
        have hx₀ : 0<(κ 0).val := (hκ 0).1
        have hx₁ : (κ 0).val≤1 := (hκ 0).2
        have hy₀ : 0<(κ 1).val := (hκ 1).1
        have hy₁ : (κ 1).val≤1 := (hκ 1).2
        change 0<(1-t.val)*(κ 0).val+t.val*(κ 1).val ∧
          (1-t.val)*(κ 0).val+t.val*(κ 1).val≤1
        simpa only [smul_eq_mul,Set.mem_Ioc] using (convex_Ioc (0 : ℝ) 1) (show (κ 0).val∈Set.Ioc (0 : ℝ) 1 from ⟨hx₀,hx₁⟩) (show (κ 1).val∈Set.Ioc (0 : ℝ) 1 from ⟨hy₀,hy₁⟩) (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
      let s : Path x y := {
        toFun := fun t => ⟨(actualIntervalSegment (κ 0) (κ 1) t).val,hseg t⟩
        continuous_toFun := (continuous_subtype_val.comp (actualIntervalSegment (κ 0) (κ 1)).continuous).subtype_mk hseg
        source' := by apply Subtype.ext;change (1-(0 : ℝ))*(κ 0).val+0*(κ 1).val=(κ 0).val;ring
        target' := by apply Subtype.ext;change (1-(1 : ℝ))*(κ 0).val+1*(κ 1).val=(κ 1).val;ring }
      let inc : C(J,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2⟩,
        continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1.le,t.property.2⟩)⟩
      let T := ((M.cover.branch : Set S)\{markedArc.val.map 1})ᶜ
      have htarget (t : J) : markedArc.val.map (inc t)∈T := by
        intro hm
        rcases markedArc.val.marked_only_at_ends (inc t) hm.1 with he | he
        · have hv := congrArg Subtype.val he
          exact (ne_of_gt t.property.1) hv
        · exact hm.2 (show markedArc.val.map (inc t)∈{markedArc.val.map 1} from he ▸ rfl)
      let A : C(J,T) := ⟨fun t => ⟨markedArc.val.map (inc t),htarget t⟩,
        (markedArc.val.continuous.comp inc.continuous).subtype_mk htarget⟩
      letI : ContractibleSpace J := (convex_Ioc (0 : ℝ) 1).contractibleSpace ⟨x,x.property⟩
      have hhom : r.Homotopic s := SimplyConnectedSpace.paths_homotopic r s
      exact ⟨htarget x,htarget y,r.map A.continuous,s.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualClosedOldContactTailStraightensInRetainedCorner
      (x y : S) (hxends : x=a.val.map 0 ∨ x=a.val.map 1)
      (q : Path x y) (hcontact : range q⊆a.val.image)
      (hmarks : ∀ t : Interval,t≠0 → q t∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),
        (∀ t,a.val.map (κ t)=q t) ∧
        IsEmbedding (fun t => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{x})ᶜ)
          (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{x})ᶜ)
          (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{x})ᶜ)
            ⟨a.val.map (κ 1),hy⟩),
          (∀ t,(α t : S)=q t) ∧
          (∀ t,(β t : S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
          α.Homotopic β := by
    as_aux_lemma =>
      obtain ⟨κ,hκ⟩ := hActualClosedOldArcContactPathHasOriginalParameters x y q hcontact
      have hκzero : κ 0=0 ∨ κ 0=1 := by
        rcases hxends with hx | hx
        · exact Or.inl ((NonLoopArc.injective ⟨a.val,hane⟩) ((hκ 0).trans (q.source.trans hx)))
        · exact Or.inr ((NonLoopArc.injective ⟨a.val,hane⟩) ((hκ 0).trans (q.source.trans hx)))
      have hκinside (t : Interval) (ht : t≠0) : κ t∈Set.Ioo (0 : Interval) 1 := by
        have hlo : κ t≠0 := by
          intro he
          have hh := hκ t
          rw [he] at hh
          exact hmarks t ht (hh ▸ a.val.start_marked)
        have hhi : κ t≠1 := by
          intro he
          have hh := hκ t
          rw [he] at hh
          exact hmarks t ht (hh ▸ a.val.end_marked)
        exact ⟨lt_of_le_of_ne (κ t).property.1 (Ne.symm hlo),
          lt_of_le_of_ne (κ t).property.2 hhi⟩
      have hinsideOne := hκinside 1 (by norm_num)
      have hneq : κ 0≠κ 1 := by
        intro he
        rcases hκzero with hz | hz
        · exact (ne_of_gt hinsideOne.1) (he.symm.trans hz)
        · exact (ne_of_lt hinsideOne.2) (he.symm.trans hz)
      refine ⟨κ,hκ,hActualNondegenerateOldArcIntervalSubpathEmbedding _ _ hneq,?_⟩
      rcases hκzero with hz | hz
      · have hall (t : Interval) : κ t∈Set.Ico (0 : Interval) 1 := by
          by_cases ht : t=0
          · rw [ht,hz]
            constructor <;> norm_num
          · exact ⟨(hκinside t ht).1.le,(hκinside t ht).2⟩
        obtain ⟨ha,hb,α,β,hα,hβ,hhom⟩ :=
          hActualOriginalStartMarkedParameterPathStraightensInRetainedStartCarrier a κ hall
        have hx : x=a.val.map 0 := by rw [←q.source,←hκ 0,hz]
        subst x
        exact ⟨ha,hb,α,β,fun t => (hα t).trans (hκ t),hβ,hhom⟩
      · have hall (t : Interval) : κ t∈Set.Ioc (0 : Interval) 1 := by
          by_cases ht : t=0
          · rw [ht,hz]
            constructor <;> norm_num
          · exact ⟨(hκinside t ht).1,(hκinside t ht).2.le⟩
        obtain ⟨ha,hb,α,β,hα,hβ,hhom⟩ :=
          hActualOriginalEndMarkedParameterPathStraightensInRetainedEndCarrier a κ hall
        have hx : x=a.val.map 1 := by rw [←q.source,←hκ 0,hz]
        subst x
        exact ⟨ha,hb,α,β,fun t => (hα t).trans (hκ t),hβ,hhom⟩
  have hActualMarkedTailSideContactVertexHasOriginalSharedMarkedTail
      (c : Interval) (hc : c=0 ∨ c=1)
      (w : actualContactVertices) (hw : w.val.2=c) :
      b.val.map c=af 0 ∧
      ∃ q : Path (af 0) (actualFiniteConeSweep w.val),range q⊆a.val.image ∧
        ∀ t : Interval,t≠0 → q t∉(M.cover.branch : Set S) := by
    as_aux_lemma =>
      have hpoint : w.val=(w.val.1,c) := Prod.ext rfl hw
      have hm := hActualContactVerticesImage w
      rcases hc with rfl | rfl
      · have he : actualFiniteConeSweep w.val=actualCentralSweep (w.val.1,0) := by
          rw [hpoint,hActualFiniteConeSweepLower]
        rw [he] at hm
        obtain ⟨hshared,q,hq,hmarks,hBoundaryHomotopy⟩ := hActualCentralLowerOriginalSharedContactTail w.val.1 hm
        exact ⟨hshared,q.cast rfl he,hq,hmarks⟩
      · have he : actualFiniteConeSweep w.val=actualCentralSweep (w.val.1,1) := by
          rw [hpoint,hActualFiniteConeSweepUpper]
        rw [he] at hm
        obtain ⟨hshared,q,hq,hmarks,hBoundaryHomotopy⟩ := hActualCentralUpperOriginalSharedContactTail w.val.1 hm
        exact ⟨hshared,q.cast rfl he,hq,hmarks⟩
  have hActualMarkedTailSideContactVertexHasEmbeddedOriginalOldSubpathHomotopy
      (c : Interval) (hc : c=0 ∨ c=1)
      (w : actualContactVertices) (hw : w.val.2=c) :
      b.val.map c=af 0 ∧
      ∃ q : Path (af 0) (actualFiniteConeSweep w.val),
      ∃ κ : C(Interval,Interval),
        (∀ t,a.val.map (κ t)=q t) ∧
        IsEmbedding (fun t => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{af 0})ᶜ)
          (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{af 0})ᶜ)
          (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)
            ⟨a.val.map (κ 1),hy⟩),
          (∀ t,(α t : S)=q t) ∧
          (∀ t,(β t : S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
          α.Homotopic β := by
    as_aux_lemma =>
      obtain ⟨hshared,q,hq,hmarks⟩ := hActualMarkedTailSideContactVertexHasOriginalSharedMarkedTail c hc w hw
      have hxends : af 0=a.val.map 0 ∨ af 0=a.val.map 1 := by
        rcases hAFEnds with ⟨hx,_⟩ | ⟨hx,_⟩
        · exact Or.inl hx
        · exact Or.inr hx
      obtain ⟨κ,hκ,hemb,hx,hy,α,β,hα,hβ,hhom⟩ :=
        hActualClosedOldContactTailStraightensInRetainedCorner _ _ hxends q hq hmarks
      exact ⟨hshared,q,κ,hκ,hemb,hx,hy,α,β,hα,hβ,hhom⟩
  have hActualMarkedTailSideContactVertexRetainsOriginalBoundaryRouteHomotopy
      (c : Interval) (hc : c=0 ∨ c=1)
      (w : actualContactVertices) (hw : w.val.2=c) :
      b.val.map c=af 0 ∧
      ∃ q : Path (af 0) (actualFiniteConeSweep w.val),range q⊆a.val.image ∧
      (∀ t : Interval,t≠0 → q t∉(M.cover.branch : Set S)) ∧
      ∃ θ : C(Interval,Interval),θ 0=c ∧ θ 1=actualCentralParameter c ∧ IsEmbedding θ ∧
      ∃ (x y z : {x : S // x∉((M.cover.branch : Set S)\{af 0})}),
      ∃ α : Path x y,∃ β : Path x z,∃ ρ : Path z y,
        x.val=af 0 ∧ (∀ t,(α t).val=q t) ∧
        (∀ t,(β t).val=b.val.map (θ t)) ∧
        (∀ t,(ρ t).val=actualFiniteConeSweep
          (⟨t.val*w.val.1.val,mul_nonneg t.property.1 w.val.1.property.1,
            (mul_le_of_le_one_right t.property.1 w.val.1.property.2).trans t.property.2⟩,c)) ∧
        α.Homotopic (β.trans ρ) := by
    have hpoint : w.val=(w.val.1,c) := Prod.ext rfl hw
    have hm := hActualContactVerticesImage w
    rcases hc with rfl | rfl
    · have he : actualFiniteConeSweep w.val=actualCentralSweep (w.val.1,0) := by
        rw [hpoint,hActualFiniteConeSweepLower]
      rw [he] at hm
      obtain ⟨hshared,q,hq,hmarks,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,x,y,z,α,β,ρ,hx,hα,hβ,hρ,hhom⟩ :=
        hActualCentralLowerOriginalSharedContactTail w.val.1 hm
      refine ⟨hshared,q.cast rfl he,hq,hmarks,θ,hθzero,hθone,hθemb,
        x,y,z,α,β,ρ,hx,hα,hβ,?_,hhom⟩
      intro t
      exact (hρ t).trans (hActualFiniteConeSweepLower _).symm
    · have he : actualFiniteConeSweep w.val=actualCentralSweep (w.val.1,1) := by
        rw [hpoint,hActualFiniteConeSweepUpper]
      rw [he] at hm
      obtain ⟨hshared,q,hq,hmarks,Γ,hΓτ,hΓChosen,P,hP,hΓtrace,hPtrace,hPsecond,zQ,Q,hQ,hQP,hQinside,θ,hθzero,hθone,hθemb,x,y,z,α,β,ρ,hx,hα,hβ,hρ,hhom⟩ :=
        hActualCentralUpperOriginalSharedContactTail w.val.1 hm
      refine ⟨hshared,q.cast rfl he,hq,hmarks,θ,hθzero,hθone,hθemb,
        x,y,z,α,β,ρ,hx,hα,hβ,?_,hhom⟩
      intro t
      exact (hρ t).trans (hActualFiniteConeSweepUpper _).symm
  have hActualMarkedSideContactBandBoundaryRouteHomotopy
      (c τ t : Interval) (q : Path (τ,c) ((0 : Interval),t)) :
      ∃ (hx : actualFiniteConeSweep (0,c)∈((M.cover.branch : Set S)\{af 0})ᶜ)
        (hy : actualFiniteConeSweep (τ,c)∈((M.cover.branch : Set S)\{af 0})ᶜ)
        (hz : actualFiniteConeSweep (0,t)∈((M.cover.branch : Set S)\{af 0})ᶜ),
      ∃ ρ : Path (⟨actualFiniteConeSweep (0,c),hx⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)
        ⟨actualFiniteConeSweep (τ,c),hy⟩,
      ∃ Q : Path (⟨actualFiniteConeSweep (τ,c),hy⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)
        ⟨actualFiniteConeSweep (0,t),hz⟩,
      ∃ B : Path (⟨actualFiniteConeSweep (0,c),hx⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)
        ⟨actualFiniteConeSweep (0,t),hz⟩,
        (∀ u,(ρ u : S)=actualFiniteConeSweep
          (⟨u.val*τ.val,mul_nonneg u.property.1 τ.property.1,
            (mul_le_of_le_one_right u.property.1 τ.property.2).trans u.property.2⟩,c)) ∧
        (∀ u,(Q u : S)=actualFiniteConeSweep (q u)) ∧
        (∀ u,(B u : S)=b.val.map (actualCentralParameter (actualIntervalSegment c t u))) ∧
        (ρ.trans Q).Homotopic B := by
    let T := ((M.cover.branch : Set S)\{af 0})ᶜ
    have havoid (z : Interval × Interval) : actualFiniteConeSweep z∈T := by
      intro hz
      exact hActualFiniteConeSweepMarks z hz.1
    let A : C(Interval × Interval,T) :=
      ⟨fun z => ⟨actualFiniteConeSweep z,havoid z⟩,
        actualFiniteConeSweep.continuous.subtype_mk _⟩
    let W : Path ((0 : Interval),c) (τ,c) := {
      toFun := fun u =>
        (⟨u.val*τ.val,mul_nonneg u.property.1 τ.property.1,
          (mul_le_of_le_one_right u.property.1 τ.property.2).trans u.property.2⟩,c)
      continuous_toFun := by fun_prop
      source' := by apply Prod.ext;apply Subtype.ext;simp;rfl
      target' := by apply Prod.ext;apply Subtype.ext;simp;rfl }
    let R : Path ((0 : Interval),c) ((0 : Interval),t) := {
      toFun := fun u => (0,actualIntervalSegment c t u)
      continuous_toFun := continuous_const.prodMk (actualIntervalSegment c t).continuous
      source' := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change (1-(0 : ℝ))*c.val+0*t.val=c.val
          ring
      target' := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change (1-(1 : ℝ))*c.val+1*t.val=t.val
          ring }
    let ρ := W.map A.continuous
    let Q := q.map A.continuous
    let B := R.map A.continuous
    letI : ContractibleSpace Interval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    have hh := (SimplyConnectedSpace.paths_homotopic (W.trans q) R).map A
    rw [Path.map_trans] at hh
    refine ⟨havoid _,havoid _,havoid _,ρ,Q,B,fun _ => rfl,fun _ => rfl,?_,hh⟩
    intro u
    change actualFiniteConeSweep (0,actualIntervalSegment c t u)=_
    rw [hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
  have hActualMarkedSidePartnerContactPathJoinsOriginalArcBoundaryRoutes
      (c : Interval) (hc : c=0 ∨ c=1) (w : actualContactVertices) (hw : w.val.2=c)
      (t : Interval) (q : Path w.val ((0 : Interval),t))
      (hcontact : ∀ u,actualFiniteConeSweep (q u)∈a.val.image) :
      ∃ (x y : ↑((M.cover.branch : Set S)\{af 0})ᶜ),
      ∃ A B : Path x y,x.val=af 0 ∧ y.val=actualFiniteConeSweep (0,t) ∧
        range (fun u => (A u : S))⊆a.val.image ∧
        range (fun u => (B u : S))⊆b.val.image ∧ A.Homotopic B := by
    obtain ⟨hshared,old,hOldRange,hOldMarks,θ,hθzero,hθone,hθemb,
      x,y,z,α,β,ρ,hx,hα,hβ,hρ,hTailHom⟩ :=
      hActualMarkedTailSideContactVertexRetainsOriginalBoundaryRouteHomotopy c hc w hw
    have hpoint : w.val=(w.val.1,c) := Prod.ext rfl hw
    let qb : Path (w.val.1,c) ((0 : Interval),t) := q.cast hpoint.symm rfl
    obtain ⟨hfoot,hside,hend,ρb,Qb,Bb,hρb,hQb,hBb,hBandHom⟩ :=
      hActualMarkedSideContactBandBoundaryRouteHomotopy c w.val.1 t qb
    have ey : y=(⟨actualFiniteConeSweep (w.val.1,c),hside⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ) := by
      apply Subtype.ext
      have he := hα 1
      rw [α.target,old.target] at he
      exact he.trans (congrArg actualFiniteConeSweep hpoint)
    have ez : z=(⟨actualFiniteConeSweep (0,c),hfoot⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ) := by
      apply Subtype.ext
      change z.val=actualFiniteConeSweep (0,c)
      have he := hβ 1
      rw [β.target,hθone] at he
      exact he.trans (by rw [hActualFiniteConeSweepInitial,hActualCentralSweepInitial])
    have hρeq : ρ=ρb.cast ez ey := by
      ext u
      exact (hρ u).trans (hρb u).symm
    let Q := Qb.cast ey rfl
    let Bb' := Bb.cast ez rfl
    have hBand : (ρ.trans Q).Homotopic Bb' := by
      have hh := hBandHom.pathCast ez rfl
      rw [Path.cast_trans ρb Qb ez ey rfl,←hρeq] at hh
      exact hh
    let A := α.trans Q
    let B := β.trans Bb'
    have hhom : A.Homotopic B :=
      (hTailHom.hcomp (Path.Homotopic.refl Q)).trans
        ((Path.Homotopic.trans_assoc β ρ Q).trans
          ((Path.Homotopic.refl β).hcomp hBand))
    refine ⟨x,_,A,B,hx,rfl,?_,?_,hhom⟩
    · rintro s ⟨u,rfl⟩
      change (A u : S)∈a.val.image
      have hm : A u∈range α ∪ range Q := by
        rw [←Path.trans_range]
        exact ⟨u,rfl⟩
      rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he := congrArg Subtype.val hv
        rw [←he,hα v]
        exact hOldRange ⟨v,rfl⟩
      · have he := congrArg Subtype.val hv
        rw [←he]
        change (Qb v : S)∈a.val.image
        rw [hQb v]
        exact hcontact v
    · rintro s ⟨u,rfl⟩
      change (B u : S)∈b.val.image
      have hm : B u∈range β ∪ range Bb' := by
        rw [←Path.trans_range]
        exact ⟨u,rfl⟩
      rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he := congrArg Subtype.val hv
        rw [←he,hβ v]
        exact ⟨θ v,rfl⟩
      · have he := congrArg Subtype.val hv
        rw [←he]
        change (Bb v : S)∈b.val.image
        rw [hBb v]
        exact ⟨actualCentralParameter (actualIntervalSegment c t v),rfl⟩
  have hActualNonloopMarkedArcCarrierPathStraightensToEmbeddedOriginalInterval
      (markedArc : M.EssentialMarkedArc) (hne : markedArc.val.map 0≠markedArc.val.map 1)
      (u : S) (huends : u=markedArc.val.map 0 ∨ u=markedArc.val.map 1)
      (x y : ↑((M.cover.branch : Set S)\{u})ᶜ) (hxy : x.val≠y.val)
      (Q : Path x y) (hQ : ∀ t,(Q t : S)∈markedArc.val.image) :
      ∃ κ : C(Interval,Interval),(∀ t,markedArc.val.map (κ t)=(Q t : S)) ∧
        IsEmbedding (fun t => markedArc.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        ∃ B : Path x y,(∀ t,(B t : S)=markedArc.val.map
          (actualIntervalSegment (κ 0) (κ 1) t)) ∧ Q.Homotopic B := by
    let R := Set.range markedArc.val.map
    let H := (NonLoopArc.isEmbedding (⟨markedArc.val,hne⟩ : NonLoopArc M)).toHomeomorph
    let r : C(Interval,R) :=
      ⟨fun t => ⟨(Q t : S),hQ t⟩,
        (continuous_subtype_val.comp Q.continuous).subtype_mk _⟩
    let κ : C(Interval,Interval) :=
      ⟨fun t => H.symm (r t),H.symm.continuous.comp r.continuous⟩
    have hκ (t : Interval) : markedArc.val.map (κ t)=(Q t : S) :=
      congrArg Subtype.val (H.apply_symm_apply (r t))
    have hx : markedArc.val.map (κ 0)=x.val :=
      (hκ 0).trans (congrArg Subtype.val Q.source)
    have hy : markedArc.val.map (κ 1)=y.val :=
      (hκ 1).trans (congrArg Subtype.val Q.target)
    have hκne : κ 0≠κ 1 :=
      fun he => hxy (hx.symm.trans ((congrArg markedArc.val.map he).trans hy))
    have hemb : IsEmbedding (fun t => markedArc.val.map (actualIntervalSegment (κ 0) (κ 1) t)) :=
      (NonLoopArc.isEmbedding (⟨markedArc.val,hne⟩ : NonLoopArc M)).comp
        (((actualIntervalSegment (κ 0) (κ 1)).continuous.isClosedEmbedding
          (actualIntervalSegmentInjectiveOfNe _ _ hκne)).isEmbedding)
    rcases huends with rfl | rfl
    · have hhalf (t : Interval) : κ t∈Set.Ico (0 : Interval) 1 := by
        refine ⟨(κ t).property.1,lt_of_le_of_ne (κ t).property.2 ?_⟩
        intro he
        have heq : κ t=1 := he
        have hp : (Q t : S)=markedArc.val.map 1 :=
          (hκ t).symm.trans (congrArg markedArc.val.map heq)
        have hm : (Q t : S)∈(M.cover.branch : Set S) := hp.symm ▸ markedArc.val.end_marked
        have hneq : (Q t : S)≠markedArc.val.map 0 :=
          fun hh => hne (hh.symm.trans hp)
        exact (Q t).property ⟨hm,by simpa only [Set.mem_singleton_iff] using hneq⟩
      obtain ⟨hxs,hys,A₀,A₁,hA₀,hA₁,hhom⟩ :=
        hActualOriginalStartMarkedParameterPathStraightensInRetainedStartCarrier markedArc κ hhalf
      have ex : x=(⟨markedArc.val.map (κ 0),hxs⟩ : ↑((M.cover.branch : Set S)\{markedArc.val.map 0})ᶜ) :=
        Subtype.ext hx.symm
      have ey : y=(⟨markedArc.val.map (κ 1),hys⟩ : ↑((M.cover.branch : Set S)\{markedArc.val.map 0})ᶜ) :=
        Subtype.ext hy.symm
      have hQA : Q=A₀.cast ex ey := by
        ext t
        exact (hκ t).symm.trans (hA₀ t).symm
      refine ⟨κ,hκ,hemb,A₁.cast ex ey,hA₁,?_⟩
      rw [hQA]
      exact hhom.pathCast ex ey
    · have hhalf (t : Interval) : κ t∈Set.Ioc (0 : Interval) 1 := by
        refine ⟨lt_of_le_of_ne (κ t).property.1 ?_,(κ t).property.2⟩
        intro he
        have heq : κ t=0 := he.symm
        have hp : (Q t : S)=markedArc.val.map 0 :=
          (hκ t).symm.trans (congrArg markedArc.val.map heq)
        have hm : (Q t : S)∈(M.cover.branch : Set S) := hp.symm ▸ markedArc.val.start_marked
        have hneq : (Q t : S)≠markedArc.val.map 1 :=
          fun hh => hne (hp.symm.trans hh)
        exact (Q t).property ⟨hm,by simpa only [Set.mem_singleton_iff] using hneq⟩
      obtain ⟨hxs,hys,A₀,A₁,hA₀,hA₁,hhom⟩ :=
        hActualOriginalEndMarkedParameterPathStraightensInRetainedEndCarrier markedArc κ hhalf
      have ex : x=(⟨markedArc.val.map (κ 0),hxs⟩ : ↑((M.cover.branch : Set S)\{markedArc.val.map 1})ᶜ) :=
        Subtype.ext hx.symm
      have ey : y=(⟨markedArc.val.map (κ 1),hys⟩ : ↑((M.cover.branch : Set S)\{markedArc.val.map 1})ᶜ) :=
        Subtype.ext hy.symm
      have hQA : Q=A₀.cast ex ey := by
        ext t
        exact (hκ t).symm.trans (hA₀ t).symm
      refine ⟨κ,hκ,hemb,A₁.cast ex ey,hA₁,?_⟩
      rw [hQA]
      exact hhom.pathCast ex ey
  have hActualMarkedSidePartnerYieldsBothEmbeddedOriginalSubpathsPuncturedHomotopic
      (c : Interval) (hc : c=0 ∨ c=1) (w : actualContactVertices) (hw : w.val.2=c)
      (t : Interval) (q : Path w.val ((0 : Interval),t))
      (hcontact : ∀ u,actualFiniteConeSweep (q u)∈a.val.image) :
      ∃ f g : C(Interval,S),IsEmbedding f ∧ IsEmbedding g ∧
        range f⊆a.val.image ∧ range g⊆b.val.image ∧
        f 0=af 0 ∧ g 0=af 0 ∧
        f 1=actualFiniteConeSweep (0,t) ∧ g 1=actualFiniteConeSweep (0,t) ∧
        af 0≠actualFiniteConeSweep (0,t) ∧
        ∃ (hu : af 0∈((M.cover.branch : Set S)\{af 0})ᶜ)
          (hv : actualFiniteConeSweep (0,t)∈((M.cover.branch : Set S)\{af 0})ᶜ)
          (α β : Path (⟨af 0,hu⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)
            ⟨actualFiniteConeSweep (0,t),hv⟩),
          (∀ u,(α u : S)=f u) ∧ (∀ u,(β u : S)=g u) ∧ α.Homotopic β := by
    obtain ⟨x,y,A,B,hx,hy,hAimage,hBimage,hAB⟩ :=
      hActualMarkedSidePartnerContactPathJoinsOriginalArcBoundaryRoutes c hc w hw t q hcontact
    have hne : af 0≠actualFiniteConeSweep (0,t) := by
      intro he
      exact hActualFiniteConeSweepMarks (0,t) (he ▸ hAFStartMarked)
    have hxy : x.val≠y.val := by
      rw [hx,hy]
      exact hne
    have haends : af 0=a.val.map 0 ∨ af 0=a.val.map 1 := by
      rcases hAFEnds with ⟨hh,_⟩ | ⟨hh,_⟩
      · exact Or.inl hh
      · exact Or.inr hh
    have hbends : af 0=b.val.map 0 ∨ af 0=b.val.map 1 := by
      obtain ⟨hh,_⟩ := hActualMarkedTailSideContactVertexRetainsOriginalBoundaryRouteHomotopy c hc w hw
      rcases hc with rfl | rfl
      · exact Or.inl hh.symm
      · exact Or.inr hh.symm
    obtain ⟨κa,hκa,hembA,A₁,hA₁,hAA₁⟩ :=
      hActualNonloopMarkedArcCarrierPathStraightensToEmbeddedOriginalInterval
        a hane (af 0) haends x y hxy A (fun u => hAimage ⟨u,rfl⟩)
    obtain ⟨κb,hκb,hembB,B₁,hB₁,hBB₁⟩ :=
      hActualNonloopMarkedArcCarrierPathStraightensToEmbeddedOriginalInterval
        b hbne (af 0) hbends x y hxy B (fun u => hBimage ⟨u,rfl⟩)
    let f : C(Interval,S) :=
      ⟨fun u => a.val.map (actualIntervalSegment (κa 0) (κa 1) u),
        a.val.continuous.comp (actualIntervalSegment (κa 0) (κa 1)).continuous⟩
    let g : C(Interval,S) :=
      ⟨fun u => b.val.map (actualIntervalSegment (κb 0) (κb 1) u),
        b.val.continuous.comp (actualIntervalSegment (κb 0) (κb 1)).continuous⟩
    have hf₀ : f 0=af 0 :=
      (hA₁ 0).symm.trans ((congrArg Subtype.val A₁.source).trans hx)
    have hg₀ : g 0=af 0 :=
      (hB₁ 0).symm.trans ((congrArg Subtype.val B₁.source).trans hx)
    have hf₁ : f 1=actualFiniteConeSweep (0,t) :=
      (hA₁ 1).symm.trans ((congrArg Subtype.val A₁.target).trans hy)
    have hg₁ : g 1=actualFiniteConeSweep (0,t) :=
      (hB₁ 1).symm.trans ((congrArg Subtype.val B₁.target).trans hy)
    have hhu : af 0∈((M.cover.branch : Set S)\{af 0})ᶜ := by simp
    have hhv : actualFiniteConeSweep (0,t)∈((M.cover.branch : Set S)\{af 0})ᶜ := by
      intro hh
      exact hActualFiniteConeSweepMarks (0,t) hh.1
    have ex : (⟨af 0,hhu⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)=x := Subtype.ext hx.symm
    have ey : (⟨actualFiniteConeSweep (0,t),hhv⟩ : ↑((M.cover.branch : Set S)\{af 0})ᶜ)=y := Subtype.ext hy.symm
    have hhom : A₁.Homotopic B₁ := hAA₁.symm.trans (hAB.trans hBB₁)
    refine ⟨f,g,hembA,hembB,?_,?_,hf₀,hg₀,hf₁,hg₁,hne,
      hhu,hhv,A₁.cast ex ey,B₁.cast ex ey,hA₁,hB₁,hhom.pathCast ex ey⟩
    · rintro s ⟨u,rfl⟩
      exact ⟨actualIntervalSegment (κa 0) (κa 1) u,rfl⟩
    · rintro s ⟨u,rfl⟩
      exact ⟨actualIntervalSegment (κb 0) (κb 1) u,rfl⟩
  have hActualBottomPartnerYieldsBothEmbeddedOriginalSubpathsPuncturedHomotopic
      (w z : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0) (hzw : z≠w)
      (q : Path w.val z.val) (κ : C(Interval,Interval))
      (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t))
      (hinside : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) :
      ∃ f g : C(Interval,S),IsEmbedding f ∧ IsEmbedding g ∧
        range f⊆a.val.image ∧ range g⊆b.val.image ∧
        f 0=actualFiniteConeSweep z.val ∧ g 0=actualFiniteConeSweep z.val ∧
        f 1=actualFiniteConeSweep w.val ∧ g 1=actualFiniteConeSweep w.val ∧
        actualFiniteConeSweep z.val≠actualFiniteConeSweep w.val ∧
        ∃ (hu : actualFiniteConeSweep z.val∈((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ)
          (hv : actualFiniteConeSweep w.val∈((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ)
          (α β : Path (⟨actualFiniteConeSweep z.val,hu⟩ : ↑((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ)
            ⟨actualFiniteConeSweep w.val,hv⟩),
          (∀ u,(α u : S)=f u) ∧ (∀ u,(β u : S)=g u) ∧ α.Homotopic β := by
    let κr : C(Interval,Interval) :=
      ⟨fun t => κ (unitInterval.symm t),κ.continuous.comp unitInterval.symmHomeomorph.continuous⟩
    have hκr (t : Interval) : a.val.map (κr t)=actualFiniteConeSweep (q.symm t) :=
      hκ (unitInterval.symm t)
    have hinsideR (t : Interval) : κr t∈Set.Ioo (0 : Interval) 1 := hinside (unitInterval.symm t)
    obtain ⟨hx,hy,A,B,hA,hB,hhom⟩ :=
      hActualOriginalBottomToBottomSubpathsPuncturedHomotopic
        (actualFiniteConeSweep z.val) q.symm hz hw κr hκr hinsideR
    obtain ⟨hembA,hembB⟩ := hActualOriginalBottomContactSubpathPairBothEmbedded
      z w hz hw hzw.symm q.symm κr hκr
    have hxpoint : a.val.map (κr 0)=actualFiniteConeSweep z.val :=
      (hκr 0).trans (congrArg actualFiniteConeSweep q.symm.source)
    have hypoint : a.val.map (κr 1)=actualFiniteConeSweep w.val :=
      (hκr 1).trans (congrArg actualFiniteConeSweep q.symm.target)
    let f : C(Interval,S) :=
      ⟨fun u => a.val.map (actualIntervalSegment (κr 0) (κr 1) u),
        a.val.continuous.comp (actualIntervalSegment (κr 0) (κr 1)).continuous⟩
    let g : C(Interval,S) :=
      ⟨fun u => b.val.map (actualIntervalSegment (actualCentralParameter z.val.2)
        (actualCentralParameter w.val.2) u),
        b.val.continuous.comp (actualIntervalSegment (actualCentralParameter z.val.2)
          (actualCentralParameter w.val.2)).continuous⟩
    have hf₀ : f 0=actualFiniteConeSweep z.val :=
      (hA 0).symm.trans ((congrArg Subtype.val A.source).trans hxpoint)
    have hg₀ : g 0=actualFiniteConeSweep z.val :=
      (hB 0).symm.trans ((congrArg Subtype.val B.source).trans hxpoint)
    have hf₁ : f 1=actualFiniteConeSweep w.val :=
      (hA 1).symm.trans ((congrArg Subtype.val A.target).trans hypoint)
    have hg₁ : g 1=actualFiniteConeSweep w.val :=
      (hB 1).symm.trans ((congrArg Subtype.val B.target).trans hypoint)
    have hne : actualFiniteConeSweep z.val≠actualFiniteConeSweep w.val := by
      intro he
      have h01 := hembA.injective (hf₀.trans (he.trans hf₁.symm))
      have hv := congrArg Subtype.val h01
      norm_num at hv
    have hu : actualFiniteConeSweep z.val∈((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ := by simp
    have hv : actualFiniteConeSweep w.val∈((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ := by
      intro hh
      exact hActualFiniteConeSweepMarks w.val hh.1
    have ex : (⟨actualFiniteConeSweep z.val,hu⟩ : ↑((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ)=
        ⟨a.val.map (κr 0),hx⟩ := Subtype.ext hxpoint.symm
    have ey : (⟨actualFiniteConeSweep w.val,hv⟩ : ↑((M.cover.branch : Set S)\{actualFiniteConeSweep z.val})ᶜ)=
        ⟨a.val.map (κr 1),hy⟩ := Subtype.ext hypoint.symm
    refine ⟨f,g,hembA,hembB,?_,?_,hf₀,hg₀,hf₁,hg₁,hne,
      hu,hv,A.cast ex ey,B.cast ex ey,hA,hB,hhom.pathCast ex ey⟩
    · rintro s ⟨u,rfl⟩
      exact ⟨actualIntervalSegment (κr 0) (κr 1) u,rfl⟩
    · rintro s ⟨u,rfl⟩
      exact ⟨actualIntervalSegment (actualCentralParameter z.val.2)
        (actualCentralParameter w.val.2) u,rfl⟩
  have hActualSpecifiedCrossingOriginalEmbeddedSubpathPairBeforePhysicalEndpointReduction :
      ∃ (f g : C(Interval,S)) (u : S),IsEmbedding f ∧ IsEmbedding g ∧
        range f⊆a.val.image ∧ range g⊆b.val.image ∧
        f 0=u ∧ g 0=u ∧ f 1=p ∧ g 1=p ∧ u≠p ∧
        (u∈ArcSurgery.crossings M a b ∨
          (u∈a.val.image∩b.val.image ∧ u∈(M.cover.branch : Set S))) ∧
        ∃ (hu : u∈((M.cover.branch : Set S)\{u})ᶜ)
          (hv : p∈((M.cover.branch : Set S)\{u})ᶜ)
          (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ) ⟨p,hv⟩),
          (∀ t,(α t : S)=f t) ∧ (∀ t,(β t : S)=g t) ∧ α.Homotopic β := by
    obtain ⟨w,z,hwpoint,hw,hzw,hodd,hboundary,q,hq,κ,hκ,hinside⟩ :=
      hActualSpecifiedCrossingProducesBoundaryLocalizedOriginalContactPath
    rcases hboundary with hz | hside
    · obtain ⟨f,g,hf,hg,hfr,hgr,hf₀,hg₀,hf₁,hg₁,hne,hu,hv,α,β,hα,hβ,hhom⟩ :=
        hActualBottomPartnerYieldsBothEmbeddedOriginalSubpathsPuncturedHomotopic
          w z hw hz hzw q κ hκ hinside
      have ha : actualFiniteConeSweep z.val∈a.val.image := hActualContactVerticesImage z
      have hb : actualFiniteConeSweep z.val∈b.val.image := by
        have he : z.val=((0 : Interval),z.val.2) := Prod.ext hz rfl
        rw [he,hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
        exact ⟨actualCentralParameter z.val.2,rfl⟩
      have hm : actualFiniteConeSweep z.val∉(M.cover.branch : Set S) := hActualFiniteConeSweepMarks z.val
      have huCross : actualFiniteConeSweep z.val∈ArcSurgery.crossings M a b :=
        ⟨⟨ha,hm⟩,⟨hb,hm⟩⟩
      rw [←hwpoint]
      exact ⟨f,g,actualFiniteConeSweep z.val,hf,hg,hfr,hgr,hf₀,hg₀,hf₁,hg₁,hne,
        Or.inl huCross,hu,hv,α,β,hα,hβ,hhom⟩
    · have he : w.val=((0 : Interval),w.val.2) := Prod.ext hw rfl
      let qr : Path z.val ((0 : Interval),w.val.2) := q.symm.cast rfl he.symm
      have hcontact (t : Interval) : actualFiniteConeSweep (qr t)∈a.val.image :=
        ⟨κ (unitInterval.symm t),(hκ (unitInterval.symm t))⟩
      obtain ⟨f,g,hf,hg,hfr,hgr,hf₀,hg₀,hf₁,hg₁,hne,hu,hv,α,β,hα,hβ,hhom⟩ :=
        hActualMarkedSidePartnerYieldsBothEmbeddedOriginalSubpathsPuncturedHomotopic
          z.val.2 hside z rfl w.val.2 qr hcontact
      have htarget : actualFiniteConeSweep ((0 : Interval),w.val.2)=p :=
        (congrArg actualFiniteConeSweep he.symm).trans hwpoint
      have huShared : af 0∈a.val.image∩b.val.image ∧ af 0∈(M.cover.branch : Set S) :=
        ⟨⟨hfr ⟨0,hf₀⟩,hgr ⟨0,hg₀⟩⟩,hAFStartMarked⟩
      rw [←htarget]
      exact ⟨f,g,af 0,hf,hg,hfr,hgr,hf₀,hg₀,hf₁,hg₁,hne,
        Or.inr huShared,hu,hv,α,β,hα,hβ,hhom⟩
  have hActualOriginalArcsPhysicalIntersectionFinite :
      (a.val.image∩b.val.image).Finite := by
    apply (hcontacts.image b.val.map).subset
    rintro x ⟨ha,hb⟩
    obtain ⟨t,ht⟩ := hb
    refine ⟨t,?_,ht⟩
    change b.val.map t∈a.val.image
    rw [ht]
    exact ha
  have hActualOriginalSubpathPairPhysicalIntersectionFinite
      (f g : C(Interval,S)) (hf : range f⊆a.val.image) (hg : range g⊆b.val.image) :
      (range f∩range g).Finite :=
    hActualOriginalArcsPhysicalIntersectionFinite.subset
      (fun _ hx => ⟨hf hx.1,hg hx.2⟩)

  have hActualSharedAffineOriginalContactTailClosesAsProperSquareParameterPath
      (d : ℝ) (hd : 0<d) (hd1 : d<1)
      (q : ℝ) (hdq : d/2<q) (hq : q<1)
      (L : C(Interval × Ioc (0:ℝ) d,ℂ))
      (K : C(Interval × (Interval × Icc (0:ℝ) d),S))
      (hsource : ∀ z,K z∈sharedComplexChart.source)
      (hunit : ∀ z,‖sharedComplexChart (K z)‖<1)
      (hzero : ∀ η τ,K (η,(τ,⟨0,le_rfl,hd.le⟩))=af 0)
      (hinner : ∀ (τ : Interval) (t : Icc (0:ℝ) d) (ht : 0<t.val),t.val≤d/2 →
        sharedComplexChart (K (1,(τ,t)))=Complex.exp
          ((1-(τ.val:ℂ))*L (0,⟨t.val,ht,t.property.2⟩)+(τ.val:ℂ)*L (1,⟨t.val,ht,t.property.2⟩)))
      (n : ℤ) (γ : C(Ioc (0:ℝ) d,Interval))
      (hlevel : ∀ t,(1-(γ t).val)*(L (0,t)).im+(γ t).val*(L (1,t)).im=
        Real.pi+(n:ℝ)*(2*Real.pi))
      (hstrict : ∀ t,0<(γ t).val ∧ (γ t).val<1) :
      let σ : Interval → Icc (0:ℝ) d := fun t =>
        ⟨(d/2)*t.val,mul_nonneg (half_pos hd).le t.property.1,
          (mul_le_of_le_one_right (half_pos hd).le t.property.2).trans (half_le_self hd.le)⟩
      ∃ f : Path (af 0) (K (1,(γ ⟨d/2,half_pos hd,half_le_self hd.le⟩,
        ⟨d/2,(half_pos hd).le,half_le_self hd.le⟩))),range f⊆a.val.image ∧
      ∃ Γ : C({t : Interval // t≠0},Interval),Γ ⟨1,by simp⟩=γ ⟨d/2,half_pos hd,half_le_self hd.le⟩ ∧
      ∃ P : Path ((0,0) : ℝ × ℝ) ((γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,d/2),
        IsEmbedding P ∧
        (∀ t : {t : Interval // t≠0},f t.val=K (1,(Γ t,σ t.val))) ∧
        (∀ t : {t : Interval // t≠0},P t.val=(t.val.val*(Γ t).val,(d/2)*t.val.val)) ∧
        (∀ t : {t : Interval // t≠0},0<(Γ t).val ∧ (Γ t).val<1) ∧
        (∀ t : Interval,(P t).2=(d/2)*t.val) ∧
        ∃ z : Interval × Interval,∃ Q : Path ((0,0) : Interval × Interval) z,
          IsEmbedding Q ∧
          (∀ t,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap (d/2) q (Q t)=P t) ∧
          ∀ t : {t : Interval // t≠0},
            (Q t.val).1∈Ioo (0 : Interval) 1 ∧ (Q t.val).2∈Ioo (0 : Interval) 1 := by
    let σp : C({t : Interval // t≠0},Ioc (0:ℝ) d) :=
      ⟨fun t => ⟨(d/2)*t.val.val,mul_pos (half_pos hd)
        (lt_of_le_of_ne t.val.property.1 (fun h => t.property (Subtype.ext h.symm))),
        (mul_le_of_le_one_right (half_pos hd).le t.val.property.2).trans (half_le_self hd.le)⟩,by fun_prop⟩
    let Γ := γ.comp σp
    have hΓend : Γ ⟨1,by simp⟩=γ ⟨d/2,half_pos hd,half_le_self hd.le⟩ := by
      apply congrArg γ
      apply Subtype.ext
      simp [σp]
    obtain ⟨f,hf,hftrace⟩ := hActualSharedAffineLevelGraphClosesAtOriginalMark
      d hd hd1 L K hsource hunit hzero hinner n γ hlevel
    obtain ⟨P,hP,hPtrace,hPsecond,z,Q,hQ,hQP,hQinside⟩ :=
      CurveComplex.LocalSurgery.actualSharedMarkedTailClosedLowerSquareParameterContactPath
        (d/2) q (half_pos hd) hdq hq Γ (fun t => hstrict (σp t))
    have hPend : ((γ ⟨d/2,half_pos hd,half_le_self hd.le⟩).val,d/2)=
        ((Γ ⟨1,by simp⟩).val,d/2) := by
      apply Prod.ext
      · exact congrArg Subtype.val hΓend.symm
      · rfl
    refine ⟨f,hf,Γ,hΓend,P.cast rfl hPend,hP,?_,hPtrace,fun t => hstrict (σp t),hPsecond,z,Q,hQ,hQP,hQinside⟩
    intro t
    exact hftrace t
  let actualLowerSeamContacts := {τ : Interval // actualCentralSweep (τ,0)∈a.val.image}
  let actualUpperSeamContacts := {τ : Interval // actualCentralSweep (τ,1)∈a.val.image}
  have hActualChosenLowerTailPackage (τ : actualLowerSeamContacts) :=
    (hActualCentralLowerOriginalSharedContactTail τ.val τ.property).2
  have hActualChosenUpperTailPackage (τ : actualUpperSeamContacts) :=
    (hActualCentralUpperOriginalSharedContactTail τ.val τ.property).2
  choose actualLowerPhysicalTail hActualLowerPhysicalTailRange hActualLowerPhysicalTailMarks
    actualLowerChosenΓ hActualLowerChosenΓEnd hActualLowerChosenΓFamily
    actualLowerParameterTail hActualLowerParameterTailEmbedding hActualLowerPhysicalTailTrace
    hActualLowerParameterTailTrace hActualLowerParameterTailHeight
    actualLowerSquareTailEnd actualLowerSquareTail hActualLowerSquareTailEmbedding
    hActualLowerSquareTailParameter hActualLowerSquareTailProper hActualLowerSameBoundaryRoute
    using hActualChosenLowerTailPackage
  choose actualUpperPhysicalTail hActualUpperPhysicalTailRange hActualUpperPhysicalTailMarks
    actualUpperChosenΓ hActualUpperChosenΓEnd hActualUpperChosenΓFamily
    actualUpperParameterTail hActualUpperParameterTailEmbedding hActualUpperPhysicalTailTrace
    hActualUpperParameterTailTrace hActualUpperParameterTailHeight
    actualUpperSquareTailEnd actualUpperSquareTail hActualUpperSquareTailEmbedding
    hActualUpperSquareTailParameter hActualUpperSquareTailProper hActualUpperSameBoundaryRoute
    using hActualChosenUpperTailPackage
  have hActualLowerChosenΓInjective (t : {t : Interval // t≠0}) :
      Function.Injective (fun τ => actualLowerChosenΓ τ t) := by
    as_aux_lemma =>
      intro τ υ he
      have hτ : actualLowerChosenΓ τ t=actualCentralLowerTailFamily τ t :=
        congrArg (fun γ : C({t : Interval // t≠0},Interval) => γ t) (hActualLowerChosenΓFamily τ)
      have hυ : actualLowerChosenΓ υ t=actualCentralLowerTailFamily υ t :=
        congrArg (fun γ : C({t : Interval // t≠0},Interval) => γ t) (hActualLowerChosenΓFamily υ)
      exact hActualCentralLowerTailFamilyInjective t (hτ.symm.trans (he.trans hυ))
  have hActualUpperChosenΓInjective (t : {t : Interval // t≠0}) :
      Function.Injective (fun τ => actualUpperChosenΓ τ t) := by
    as_aux_lemma =>
      intro τ υ he
      have hτ : actualUpperChosenΓ τ t=actualCentralUpperTailFamily τ t :=
        congrArg (fun γ : C({t : Interval // t≠0},Interval) => γ t) (hActualUpperChosenΓFamily τ)
      have hυ : actualUpperChosenΓ υ t=actualCentralUpperTailFamily υ t :=
        congrArg (fun γ : C({t : Interval // t≠0},Interval) => γ t) (hActualUpperChosenΓFamily υ)
      exact hActualCentralUpperTailFamilyInjective t (hτ.symm.trans (he.trans hυ))
  have hActualLowerTailFamilyDistinctOnlyMeetAtMarkedTip
      (τ υ : actualLowerSeamContacts) (hτυ : τ≠υ) :
      range (actualLowerParameterTail τ)∩range (actualLowerParameterTail υ)={(0,0)} := by
    as_aux_lemma =>
      exact CurveComplex.LocalSurgery.actualMarkedTailConeDifferentLevelsOnlyMeetAtMarkedTip
        (actualCentralParameter 0).val (ne_of_gt (hActualCentralParameterInterior 0).1)
        (fun τ t => actualLowerChosenΓ τ t) hActualLowerChosenΓInjective
        (fun τ => actualLowerParameterTail τ) (fun τ => Path.source _) hActualLowerParameterTailTrace τ υ hτυ
  have hActualUpperTailFamilyPositiveTraceInjective :
      Function.Injective (fun z : actualUpperSeamContacts × {t : Interval // t≠0} =>
        actualUpperParameterTail z.1 z.2.val) := by
    as_aux_lemma =>
      let P : actualUpperSeamContacts → Interval → ℝ × ℝ :=
        fun τ t => ((actualUpperParameterTail τ t).1,1-(actualUpperParameterTail τ t).2)
      have htrace (τ : actualUpperSeamContacts) (t : {t : Interval // t≠0}) :
          P τ t.val=(t.val.val*(actualUpperChosenΓ τ t).val,(1-(actualCentralParameter 1).val)*t.val.val) := by
        dsimp only [P]
        rw [hActualUpperParameterTailTrace]
        apply Prod.ext
        · rfl
        · change 1-(1-(1-(actualCentralParameter 1).val)*t.val.val)=
            (1-(actualCentralParameter 1).val)*t.val.val
          ring
      have hP := CurveComplex.LocalSurgery.actualMarkedTailConePositiveFamilyTraceInjective
        (1-(actualCentralParameter 1).val) (ne_of_gt (sub_pos.mpr (hActualCentralParameterInterior 1).2))
        (fun τ t => actualUpperChosenΓ τ t) hActualUpperChosenΓInjective P htrace
      intro z w he
      apply hP
      exact congrArg (fun v : ℝ × ℝ => (v.1,1-v.2)) he
  have hActualUpperTailFamilyDistinctOnlyMeetAtMarkedTip
      (τ υ : actualUpperSeamContacts) (hτυ : τ≠υ) :
      range (actualUpperParameterTail τ)∩range (actualUpperParameterTail υ)={(0,1)} := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
        by_cases ht : t=0
        · subst t
          exact mem_singleton_iff.mpr (Path.source _)
        by_cases hu₀ : u=0
        · subst u
          exact mem_singleton_iff.mpr (hu.symm.trans (Path.source _))
        have hp := hActualUpperTailFamilyPositiveTraceInjective
          (a₁ := (τ,⟨t,ht⟩)) (a₂ := (υ,⟨u,hu₀⟩)) hu.symm
        exact (hτυ (congrArg Prod.fst hp)).elim
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,Path.source _⟩,⟨0,Path.source _⟩⟩
  let actualCollarCentralEmbedding : C(Interval × Interval,ℝ × ℝ) :=
    ⟨fun z => (z.1.val,(actualCentralParameter z.2).val),by fun_prop⟩
  have hActualCollarCentralEmbeddingInjective : Function.Injective actualCollarCentralEmbedding := by
    as_aux_lemma =>
      intro z w he
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst he)
      · exact hActualCentralParameterInjective (Subtype.ext (congrArg Prod.snd he))
  have hActualLowerTailMeetsSameCentralBandOnlyAtSeam (τ : actualLowerSeamContacts) :
      range (actualLowerParameterTail τ)∩range actualCollarCentralEmbedding=
        {(τ.val.val,(actualCentralParameter 0).val)} := by
    as_aux_lemma =>
      have hend : actualLowerParameterTail τ 1∈
          (fun z : Interval × Interval => (z.1.val,(actualCentralParameter z.2).val)) '' Set.univ := by
        refine ⟨(τ.val,0),mem_univ _,?_⟩
        exact (Path.target _).symm
      simpa only [actualCollarCentralEmbedding,ContinuousMap.coe_mk,Set.image_univ,Path.target] using
        CurveComplex.LocalSurgery.actualMarkedTailCentralDrawingLowerAttachment
          actualCentralParameter hActualCentralParameterStrictMono (actualLowerParameterTail τ)
          (hActualCentralParameterInterior 0).1 (hActualLowerParameterTailHeight τ) Set.univ hend
  have hActualUpperTailMeetsSameCentralBandOnlyAtSeam (τ : actualUpperSeamContacts) :
      range (actualUpperParameterTail τ)∩range actualCollarCentralEmbedding=
        {(τ.val.val,(actualCentralParameter 1).val)} := by
    as_aux_lemma =>
      have hend : actualUpperParameterTail τ 1∈
          (fun z : Interval × Interval => (z.1.val,(actualCentralParameter z.2).val)) '' Set.univ := by
        refine ⟨(τ.val,1),mem_univ _,?_⟩
        exact (Path.target _).symm
      simpa only [actualCollarCentralEmbedding,ContinuousMap.coe_mk,Set.image_univ,Path.target] using
        CurveComplex.LocalSurgery.actualMarkedTailCentralDrawingUpperAttachment
          actualCentralParameter hActualCentralParameterStrictMono (actualUpperParameterTail τ)
          (hActualCentralParameterInterior 1).2 (hActualUpperParameterTailHeight τ) Set.univ hend
  have hActualLowerUpperTailFamiliesDisjoint (τ : actualLowerSeamContacts) (υ : actualUpperSeamContacts) :
      Disjoint (range (actualLowerParameterTail τ)) (range (actualUpperParameterTail υ)) := by
    as_aux_lemma =>
      apply Set.disjoint_left.mpr
      rintro z ⟨t,rfl⟩ ⟨u,hu⟩
      have he := congrArg Prod.snd hu
      rw [hActualLowerParameterTailHeight,hActualUpperParameterTailHeight] at he
      have hr : 0<(actualCentralParameter 0).val := (hActualCentralParameterInterior 0).1
      have hq : (actualCentralParameter 1).val<1 := (hActualCentralParameterInterior 1).2
      have hrq : (actualCentralParameter 0).val<(actualCentralParameter 1).val :=
        hActualCentralParameterStrictMono (by change (0 : ℝ)<1;norm_num)
      nlinarith only [he,hr,hq,hrq,t.property.1,t.property.2,u.property.1,u.property.2]
  have hActualCentralContactDrawingEmbedsInOriginalMarkedCollarQuadrilateral :
      ∃ ρ : C(Interval × Interval,Interval × Interval),IsEmbedding ρ ∧
        (∀ z,CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
          (actualCentralParameter 0).val (actualCentralParameter 1).val (ρ z)=
          (z.1.val,(actualCentralParameter z.2).val)) ∧
        (∀ t : Interval,ρ (0,t)=(0,actualCentralParameter t)) ∧
        (∀ z : Interval × Interval,z.1∈Set.Ioo (0 : Interval) 1 →
          (ρ z).1∈Set.Ioo (0 : Interval) 1 ∧ (ρ z).2∈Set.Ioo (0 : Interval) 1) := by
    let r := actualCentralParameter 0
    let q := actualCentralParameter 1
    have hqr : r.val<q.val :=
      hActualCentralParameterStrictMono (by change (0 : ℝ)<1;norm_num)
    let Ψ := CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap r.val q.val
    have hΨ : IsEmbedding Ψ :=
      CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMapEmbedding r.val q.val hqr
    let Φ : C(Interval × Interval,ℝ × ℝ) :=
      ⟨fun z => (z.1.val,(actualCentralParameter z.2).val),by fun_prop⟩
    have hΦinj : Function.Injective Φ := by
      intro z w he
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst he)
      · exact hActualCentralParameterInjective (Subtype.ext (congrArg Prod.snd he))
    have hΦrange : range Φ⊆range Ψ := by
      rintro y ⟨z,rfl⟩
      rw [CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMapRange r.val q.val hqr]
      have hl : r.val≤(actualCentralParameter z.2).val :=
        hActualCentralParameterStrictMono.monotone z.2.property.1
      have hu : (actualCentralParameter z.2).val≤q.val :=
        hActualCentralParameterStrictMono.monotone z.2.property.2
      have hr : 0≤r.val := r.property.1
      have hleft := mul_le_of_le_one_left hr z.1.property.2
      have hright := mul_le_of_le_one_left (sub_nonneg.mpr q.property.2) z.1.property.2
      refine ⟨z.1.property.1,z.1.property.2,hleft.trans hl,?_⟩
      change (actualCentralParameter z.2).val≤1-z.1.val*(1-q.val)
      linarith only [hu,hright]
    let H := hΨ.toHomeomorph
    let σ : C(Interval × Interval,range Ψ) :=
      ⟨fun z => ⟨Φ z,hΦrange ⟨z,rfl⟩⟩,Φ.continuous.subtype_mk _⟩
    let ρ : C(Interval × Interval,Interval × Interval) :=
      ⟨fun z => H.symm (σ z),H.symm.continuous.comp σ.continuous⟩
    have hρ (z : Interval × Interval) : Ψ (ρ z)=Φ z :=
      congrArg Subtype.val (H.apply_symm_apply (σ z))
    have hρinj : Function.Injective ρ := by
      intro z w he
      exact hΦinj ((hρ z).symm.trans ((congrArg Ψ he).trans (hρ w)))
    refine ⟨ρ,(ρ.continuous.isClosedEmbedding hρinj).isEmbedding,hρ,?_,?_⟩
    · intro t
      apply hΨ.injective
      have hleft := (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterBoundary r.val q.val).1
      exact (hρ (0,t)).trans (hleft (actualCentralParameter t)).symm
    · intro z hz
      have hr : 0<r.val := (hActualCentralParameterInterior 0).1
      have hq : q.val<1 := (hActualCentralParameterInterior 1).2
      have hl : r.val≤(actualCentralParameter z.2).val := hActualCentralParameterStrictMono.monotone z.2.property.1
      have hu : (actualCentralParameter z.2).val≤q.val := hActualCentralParameterStrictMono.monotone z.2.property.2
      apply CurveComplex.LocalSurgery.actualMarkedCollarStrictRegionParameterInterior r.val q.val hqr (ρ z)
      · rw [hρ]
        exact hz.1
      · rw [hρ]
        exact hz.2
      · rw [hρ]
        have hzR : z.1.val<(1 : ℝ) := hz.2
        have hh : z.1.val*r.val<r.val := by
          simpa only [one_mul] using mul_lt_mul_of_pos_right hzR hr
        exact hh.trans_le hl
      · rw [hρ]
        have hzR : z.1.val<(1 : ℝ) := hz.2
        have hden : (0 : ℝ)<1-q.val := sub_pos.mpr hq
        have hh := mul_lt_mul_of_pos_right hzR hden
        change (actualCentralParameter z.2).val<1-z.1.val*(1-q.val)
        nlinarith only [hh,hu]

  obtain ⟨actualCentralCollarSquare,hActualCentralCollarSquareEmbedding,
    hActualCentralCollarSquareFormula,hActualCentralCollarSquareInitial,hActualCentralCollarSquareInterior⟩ :=
    hActualCentralContactDrawingEmbedsInOriginalMarkedCollarQuadrilateral
  have hActualCollarQuadrilateralInjective : Function.Injective
      (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
        (actualCentralParameter 0).val (actualCentralParameter 1).val) :=
    (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMapEmbedding
      (actualCentralParameter 0).val (actualCentralParameter 1).val
      (hActualCentralParameterStrictMono (by change (0 : ℝ)<1;norm_num))).injective
  have hActualLowerSameSquareTailEndMatchesCentral (τ : actualLowerSeamContacts) :
      actualLowerSquareTail τ 1=actualCentralCollarSquare (τ.val,0) := by
    as_aux_lemma =>
      apply hActualCollarQuadrilateralInjective
      rw [hActualLowerSquareTailParameter,Path.target,hActualCentralCollarSquareFormula]
  have hActualUpperSameSquareTailEndMatchesCentral (τ : actualUpperSeamContacts) :
      actualUpperSquareTail τ 1=actualCentralCollarSquare (τ.val,1) := by
    as_aux_lemma =>
      apply hActualCollarQuadrilateralInjective
      rw [hActualUpperSquareTailParameter,Path.target,hActualCentralCollarSquareFormula]
  have hActualLowerSameSquareTailOnlyMeetsCentralAtSeam (τ : actualLowerSeamContacts) :
      range (actualLowerSquareTail τ)∩range actualCentralCollarSquare={actualLowerSquareTail τ 1} := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨w,hw⟩⟩
        have hp : actualLowerParameterTail τ t=actualCollarCentralEmbedding w :=
          (hActualLowerSquareTailParameter τ t).symm.trans
            ((congrArg (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
              (actualCentralParameter 0).val (actualCentralParameter 1).val) hw.symm).trans
              (hActualCentralCollarSquareFormula w))
        have hmem : actualLowerParameterTail τ t∈
            range (actualLowerParameterTail τ)∩range actualCollarCentralEmbedding :=
          ⟨⟨t,rfl⟩,⟨w,hp.symm⟩⟩
        rw [hActualLowerTailMeetsSameCentralBandOnlyAtSeam] at hmem
        have ht : t=1 := (hActualLowerParameterTailEmbedding τ).injective
          ((mem_singleton_iff.mp hmem).trans (Path.target _).symm)
        subst t
        exact mem_singleton _
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨1,rfl⟩,⟨(τ.val,0),(hActualLowerSameSquareTailEndMatchesCentral τ).symm⟩⟩
  have hActualUpperSameSquareTailOnlyMeetsCentralAtSeam (τ : actualUpperSeamContacts) :
      range (actualUpperSquareTail τ)∩range actualCentralCollarSquare={actualUpperSquareTail τ 1} := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨w,hw⟩⟩
        have hp : actualUpperParameterTail τ t=actualCollarCentralEmbedding w :=
          (hActualUpperSquareTailParameter τ t).symm.trans
            ((congrArg (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
              (actualCentralParameter 0).val (actualCentralParameter 1).val) hw.symm).trans
              (hActualCentralCollarSquareFormula w))
        have hmem : actualUpperParameterTail τ t∈
            range (actualUpperParameterTail τ)∩range actualCollarCentralEmbedding :=
          ⟨⟨t,rfl⟩,⟨w,hp.symm⟩⟩
        rw [hActualUpperTailMeetsSameCentralBandOnlyAtSeam] at hmem
        have ht : t=1 := (hActualUpperParameterTailEmbedding τ).injective
          ((mem_singleton_iff.mp hmem).trans (Path.target _).symm)
        subst t
        exact mem_singleton _
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨1,rfl⟩,⟨(τ.val,1),(hActualUpperSameSquareTailEndMatchesCentral τ).symm⟩⟩
  have hActualMarkedSeamContactFirstCoordinateInterior (w : actualContactVertices)
      (hw : w.val.2=0 ∨ w.val.2=1) : w.val.1∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      have hm := hActualContactVerticesImage w
      have hwzero : w.val.1≠0 := by
        intro he
        have hp : w.val=(0,w.val.2) := Prod.ext he rfl
        rw [hp,hActualFiniteConeSweepInitial] at hm
        exact hActualCentralAllCornersOff 0 w.val.2 (Or.inl rfl) hw hm
      have hwone : w.val.1≠1 := by
        intro he
        have hp : w.val=(1,w.val.2) := Prod.ext he rfl
        rw [hp] at hm
        exact hActualFiniteConeSweepTopAvoids w.val.2 hm
      exact ⟨lt_of_le_of_ne w.val.1.property.1 hwzero.symm,
        lt_of_le_of_ne w.val.1.property.2 hwone⟩
  have hActualOuterProperCentralPathPositiveCollarInterior
      (w z : actualContactVertices) (q : Path w.val z.val)
      (hproper : ∀ t,(q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → t=0 ∨ t=1)
      (hz : z.val.2=0 ∨ z.val.2=1)
      (hcontact : ∀ t,actualFiniteConeSweep (q t)∈a.val.image) :
      ∀ t : Interval,t≠0 → (actualCentralCollarSquare (q t)).1∈Set.Ioo (0 : Interval) 1 ∧
        (actualCentralCollarSquare (q t)).2∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      intro t ht
      have hxzero : (q t).1≠0 := by
        intro he
        have hend := (hproper t (Or.inl he)).resolve_left ht
        subst t
        rw [Path.target] at he
        exact (ne_of_gt (hActualMarkedSeamContactFirstCoordinateInterior z hz).1) he
      have hxone : (q t).1≠1 := by
        intro he
        have hp : q t=(1,(q t).2) := Prod.ext he rfl
        have hm := hcontact t
        rw [hp] at hm
        exact hActualFiniteConeSweepTopAvoids (q t).2 hm
      exact hActualCentralCollarSquareInterior (q t)
        ⟨lt_of_le_of_ne (q t).1.property.1 hxzero.symm,
          lt_of_le_of_ne (q t).1.property.2 hxone⟩
  have hActualLowerSameChosenTailProducesProperOriginalCrosscut
      (w z : actualContactVertices) (q : Path w.val z.val) (hq : IsEmbedding q)
      (hproper : ∀ t,(q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → t=0 ∨ t=1)
      (hcontact : ∀ t,actualFiniteConeSweep (q t)∈a.val.image)
      (τ : actualLowerSeamContacts) (hz : z.val=(τ.val,0)) :
      ∃ J : Path (actualCentralCollarSquare w.val) ((0,0) : Interval × Interval),IsEmbedding J ∧
        range J=range (fun t => actualCentralCollarSquare (q t))∪range (actualLowerSquareTail τ) ∧
        ∀ t : Interval,t∈Set.Ioo (0 : Interval) 1 →
          (J t).1∈Set.Ioo (0 : Interval) 1 ∧ (J t).2∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      have hend : actualLowerSquareTail τ 1=actualCentralCollarSquare z.val := by
        rw [hz]
        exact hActualLowerSameSquareTailEndMatchesCentral τ
      exact CurveComplex.LocalSurgery.actualSameEmbeddedSquareTailProducesProperCrosscut
        actualCentralCollarSquare hActualCentralCollarSquareEmbedding q hq
        (actualLowerSquareTail τ) (hActualLowerSquareTailEmbedding τ) hend
        (hActualLowerSameSquareTailOnlyMeetsCentralAtSeam τ)
        (hActualOuterProperCentralPathPositiveCollarInterior w z q hproper
          (Or.inl (congrArg Prod.snd hz)) hcontact)
        (fun t ht => hActualLowerSquareTailProper τ ⟨t,ht⟩)
  have hActualUpperSameChosenTailProducesProperOriginalCrosscut
      (w z : actualContactVertices) (q : Path w.val z.val) (hq : IsEmbedding q)
      (hproper : ∀ t,(q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → t=0 ∨ t=1)
      (hcontact : ∀ t,actualFiniteConeSweep (q t)∈a.val.image)
      (τ : actualUpperSeamContacts) (hz : z.val=(τ.val,1)) :
      ∃ J : Path (actualCentralCollarSquare w.val) ((0,1) : Interval × Interval),IsEmbedding J ∧
        range J=range (fun t => actualCentralCollarSquare (q t))∪range (actualUpperSquareTail τ) ∧
        ∀ t : Interval,t∈Set.Ioo (0 : Interval) 1 →
          (J t).1∈Set.Ioo (0 : Interval) 1 ∧ (J t).2∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      have hend : actualUpperSquareTail τ 1=actualCentralCollarSquare z.val := by
        rw [hz]
        exact hActualUpperSameSquareTailEndMatchesCentral τ
      exact CurveComplex.LocalSurgery.actualSameEmbeddedSquareTailProducesProperCrosscut
        actualCentralCollarSquare hActualCentralCollarSquareEmbedding q hq
        (actualUpperSquareTail τ) (hActualUpperSquareTailEmbedding τ) hend
        (hActualUpperSameSquareTailOnlyMeetsCentralAtSeam τ)
        (hActualOuterProperCentralPathPositiveCollarInterior w z q hproper
          (Or.inr (congrArg Prod.snd hz)) hcontact)
        (fun t ht => hActualUpperSquareTailProper τ ⟨t,ht⟩)
  have hActualLowerSameSquareTailFamilyOnlyMeetsAtMarkedTip
      (τ υ : actualLowerSeamContacts) (hτυ : τ≠υ) :
      range (actualLowerSquareTail τ)∩range (actualLowerSquareTail υ)={(0,0)} := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
        have hp : actualLowerParameterTail τ t=actualLowerParameterTail υ u :=
          (hActualLowerSquareTailParameter τ t).symm.trans
            ((congrArg (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
              (actualCentralParameter 0).val (actualCentralParameter 1).val) hu.symm).trans
              (hActualLowerSquareTailParameter υ u))
        have hm : actualLowerParameterTail τ t∈
            range (actualLowerParameterTail τ)∩range (actualLowerParameterTail υ) :=
          ⟨⟨t,rfl⟩,⟨u,hp.symm⟩⟩
        rw [hActualLowerTailFamilyDistinctOnlyMeetAtMarkedTip τ υ hτυ] at hm
        have ht : t=0 := (hActualLowerParameterTailEmbedding τ).injective
          ((mem_singleton_iff.mp hm).trans (Path.source _).symm)
        subst t
        exact mem_singleton_iff.mpr (Path.source _)
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,Path.source _⟩,⟨0,Path.source _⟩⟩
  have hActualUpperSameSquareTailFamilyOnlyMeetsAtMarkedTip
      (τ υ : actualUpperSeamContacts) (hτυ : τ≠υ) :
      range (actualUpperSquareTail τ)∩range (actualUpperSquareTail υ)={(0,1)} := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
        have hp : actualUpperParameterTail τ t=actualUpperParameterTail υ u :=
          (hActualUpperSquareTailParameter τ t).symm.trans
            ((congrArg (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
              (actualCentralParameter 0).val (actualCentralParameter 1).val) hu.symm).trans
              (hActualUpperSquareTailParameter υ u))
        have hm : actualUpperParameterTail τ t∈
            range (actualUpperParameterTail τ)∩range (actualUpperParameterTail υ) :=
          ⟨⟨t,rfl⟩,⟨u,hp.symm⟩⟩
        rw [hActualUpperTailFamilyDistinctOnlyMeetAtMarkedTip τ υ hτυ] at hm
        have ht : t=0 := (hActualUpperParameterTailEmbedding τ).injective
          ((mem_singleton_iff.mp hm).trans (Path.source _).symm)
        subst t
        exact mem_singleton_iff.mpr (Path.source _)
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,Path.source _⟩,⟨0,Path.source _⟩⟩
  have hActualLowerUpperSameSquareTailFamiliesDisjoint
      (τ : actualLowerSeamContacts) (υ : actualUpperSeamContacts) :
      Disjoint (range (actualLowerSquareTail τ)) (range (actualUpperSquareTail υ)) := by
    as_aux_lemma =>
      apply Set.disjoint_left.mpr
      rintro z ⟨t,rfl⟩ ⟨u,hu⟩
      have hp : actualLowerParameterTail τ t=actualUpperParameterTail υ u :=
        (hActualLowerSquareTailParameter τ t).symm.trans
          ((congrArg (CurveComplex.LocalSurgery.actualMarkedCollarQuadrilateralParameterMap
            (actualCentralParameter 0).val (actualCentralParameter 1).val) hu.symm).trans
            (hActualUpperSquareTailParameter υ u))
      exact Set.disjoint_left.mp (hActualLowerUpperTailFamiliesDisjoint τ υ)
        ⟨t,rfl⟩ ⟨u,hp.symm⟩
  let actualAttachedMarkHeight : Fin 2 → Interval := fun m => if m=0 then 0 else 1
  have hActualAttachedMarkHeightInjective : Function.Injective actualAttachedMarkHeight := by
    as_aux_lemma =>
      intro m n he
      fin_cases m <;> fin_cases n <;> first | rfl | (norm_num [actualAttachedMarkHeight] at he)
  let actualAttachedTailIncidence (v : zeroVertex) (m : Fin 2) : Prop :=
    ∃ c : actualContactVertices,v=Sum.inl c ∧ c.val.2=actualAttachedMarkHeight m
  let actualAttachedContactVertex := Sum zeroVertex (Fin 2)
  letI : Fintype actualAttachedContactVertex := Fintype.ofFinite actualAttachedContactVertex
  let actualAttachedContactGraph : SimpleGraph actualAttachedContactVertex := {
    Adj := fun v w => match v,w with
      | Sum.inl v,Sum.inl w => actualZeroGraph.Adj v w
      | Sum.inl v,Sum.inr m => actualAttachedTailIncidence v m
      | Sum.inr m,Sum.inl v => actualAttachedTailIncidence v m
      | Sum.inr _,Sum.inr _ => False
    symm := ⟨by
      intro v w h
      cases v <;> cases w
      · exact actualZeroGraph.adj_symm h
      · exact h
      · exact h
      · exact h.elim⟩
    loopless := ⟨by
      intro v
      cases v
      · exact actualZeroGraph.irrefl
      · exact not_false⟩ }
  have hActualSameTailAttachedSeamNeighborFinset
      (c : actualContactVertices) (m : Fin 2) (hc : c.val.2=actualAttachedMarkHeight m) :
      actualAttachedContactGraph.neighborFinset (Sum.inl (Sum.inl c))=
        (actualZeroGraph.neighborFinset (Sum.inl c)).image Sum.inl ∪ {Sum.inr m} := by
    as_aux_lemma =>
      ext v
      cases v with
      | inl v =>
        rw [SimpleGraph.mem_neighborFinset]
        change actualZeroGraph.Adj (Sum.inl c) v ↔ _
        constructor
        · intro hv
          exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨v,(by simpa using hv),rfl⟩)
        · intro hv
          rcases Finset.mem_union.mp hv with hv | hv
          · obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hv
            have huv : u=v := Sum.inl.inj he
            subst u
            simpa using hu
          · exact False.elim (Sum.inl_ne_inr (Finset.mem_singleton.mp hv))
      | inr n =>
        have hh : c.val.2=actualAttachedMarkHeight n ↔ n=m := by
          constructor
          · intro he
            exact hActualAttachedMarkHeightInjective (he.symm.trans hc)
          · intro he
            subst n
            exact hc
        have hi : actualAttachedTailIncidence (Sum.inl c) n ↔ c.val.2=actualAttachedMarkHeight n := by
          constructor
          · rintro ⟨d,he,hd⟩
            have hcd : c=d := Sum.inl.inj he
            subst d
            exact hd
          · intro hd
            exact ⟨c,rfl,hd⟩
        rw [SimpleGraph.mem_neighborFinset]
        change actualAttachedTailIncidence (Sum.inl c) n ↔ _
        rw [hi,hh]
        constructor
        · intro he
          subst n
          exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
        · intro hn
          rcases Finset.mem_union.mp hn with hn | hn
          · obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hn
            exact False.elim (Sum.inl_ne_inr he)
          · exact Sum.inr.inj (Finset.mem_singleton.mp hn)
  have hActualSameChosenTailAttachedActualSeamDegreeTwo
      (c : actualContactVertices) (m : Fin 2) (hc : c.val.2=actualAttachedMarkHeight m) :
      actualAttachedContactGraph.degree (Sum.inl (Sum.inl c))=2 := by
    as_aux_lemma =>
      have hd : actualZeroGraph.degree (Sum.inl c)=1 := by
        apply hActualEveryMarkedSeamContactVertexDegreeOne c
        fin_cases m
        · exact Or.inl (by simpa [actualAttachedMarkHeight] using hc)
        · exact Or.inr (by simpa [actualAttachedMarkHeight] using hc)
      change (actualAttachedContactGraph.neighborFinset (Sum.inl (Sum.inl c))).card=2
      rw [hActualSameTailAttachedSeamNeighborFinset c m hc]
      have hj : Disjoint ((actualZeroGraph.neighborFinset (Sum.inl c)).image
          (Sum.inl : zeroVertex → actualAttachedContactVertex)) {Sum.inr m} := by
        apply Finset.disjoint_left.mpr
        intro z hz hm
        obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hz
        exact Sum.inl_ne_inr (he.trans (Finset.mem_singleton.mp hm))
      rw [Finset.card_union_of_disjoint hj,Finset.card_image_of_injective _ Sum.inl_injective]
      change actualZeroGraph.degree (Sum.inl c)+1=2
      rw [hd]
  have hActualCentralCollarSquareAvoidsBothMarkedTips (z : Interval × Interval)
      (c : Interval) (hc : c=0 ∨ c=1) : actualCentralCollarSquare z≠(0,c) := by
    as_aux_lemma =>
      intro he
      have hf := hActualCentralCollarSquareFormula z
      rw [he] at hf
      have hz : z.1=0 := by
        apply Subtype.ext
        have hh := congrArg Prod.fst hf
        change (0 : ℝ)=z.1.val at hh
        exact hh.symm
      have hzpair : z=(0,z.2) := Prod.ext hz rfl
      rw [hzpair,hActualCentralCollarSquareInitial] at he
      have hh : actualCentralParameter z.2=c := congrArg Prod.snd he
      rcases hc with rfl | rfl
      · exact (ne_of_gt (hActualCentralParameterInterior z.2).1) (congrArg Subtype.val hh)
      · exact (ne_of_lt (hActualCentralParameterInterior z.2).2) (congrArg Subtype.val hh)
  let actualAttachedSquareVertexPosition : actualAttachedContactVertex → Interval × Interval := fun v =>
    match v with
    | Sum.inl v => actualCentralCollarSquare (zeroVertexPosition v)
    | Sum.inr m => (0,actualAttachedMarkHeight m)
  have hActualAttachedSquareVertexPositionInjective : Function.Injective actualAttachedSquareVertexPosition := by
    as_aux_lemma =>
      intro v w he
      cases v with
      | inl v =>
        cases w with
        | inl w => exact congrArg Sum.inl (zeroVertexPositionInjective
            (hActualCentralCollarSquareEmbedding.injective he))
        | inr m =>
          exact False.elim (hActualCentralCollarSquareAvoidsBothMarkedTips
            (zeroVertexPosition v) (actualAttachedMarkHeight m)
            (by fin_cases m <;> simp [actualAttachedMarkHeight]) he)
      | inr m =>
        cases w with
        | inl w =>
          exact False.elim (hActualCentralCollarSquareAvoidsBothMarkedTips
            (zeroVertexPosition w) (actualAttachedMarkHeight m)
            (by fin_cases m <;> simp [actualAttachedMarkHeight]) he.symm)
        | inr n => exact congrArg Sum.inr (hActualAttachedMarkHeightInjective (congrArg Prod.snd he))
  have hActualAttachedOldVertexWithoutTailNeighborFinset
      (v : zeroVertex) (hv : ∀ m,¬actualAttachedTailIncidence v m) :
      actualAttachedContactGraph.neighborFinset (Sum.inl v)=
        (actualZeroGraph.neighborFinset v).image Sum.inl := by
    as_aux_lemma =>
      ext w
      cases w with
      | inl w =>
        rw [SimpleGraph.mem_neighborFinset]
        change actualZeroGraph.Adj v w ↔ _
        constructor
        · intro hw
          exact Finset.mem_image.mpr ⟨w,(by simpa using hw),rfl⟩
        · intro hw
          obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hw
          have huw : u=w := Sum.inl.inj he
          subst u
          simpa using hu
      | inr m =>
        rw [SimpleGraph.mem_neighborFinset]
        change actualAttachedTailIncidence v m ↔ _
        constructor
        · intro hm
          exact False.elim (hv m hm)
        · intro hm
          obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hm
          exact False.elim (Sum.inl_ne_inr he)
  have hActualAttachedOldVertexWithoutTailDegree
      (v : zeroVertex) (hv : ∀ m,¬actualAttachedTailIncidence v m) :
      actualAttachedContactGraph.degree (Sum.inl v)=actualZeroGraph.degree v := by
    as_aux_lemma =>
      change (actualAttachedContactGraph.neighborFinset (Sum.inl v)).card=_
      rw [hActualAttachedOldVertexWithoutTailNeighborFinset v hv,
        Finset.card_image_of_injective _ Sum.inl_injective]
      rfl
  have hActualAttachedEveryInitialContactVertexDegreeOne
      (c : actualContactVertices) (hc : c.val.1=0) :
      actualAttachedContactGraph.degree (Sum.inl (Sum.inl c))=1 := by
    as_aux_lemma =>
      have hn : ∀ m,¬actualAttachedTailIncidence (Sum.inl c) m := by
        intro m hm
        obtain ⟨d,he,hd⟩ := hm
        have hcd : c=d := Sum.inl.inj he
        subst d
        have hs : c.val.2=0 ∨ c.val.2=1 := by
          fin_cases m
          · exact Or.inl (by simpa [actualAttachedMarkHeight] using hd)
          · exact Or.inr (by simpa [actualAttachedMarkHeight] using hd)
        have hh := (hActualMarkedSeamContactFirstCoordinateInterior c hs).1
        rw [hc] at hh
        exact lt_irrefl _ hh
      rw [hActualAttachedOldVertexWithoutTailDegree _ hn]
      exact hActualEveryInitialContactVertexDegreeOne c hc
  have hActualAttachedOddContactVertexIsInitialOrMarked
      (v : actualAttachedContactVertex) (hv : Odd (actualAttachedContactGraph.degree v)) :
      (∃ c : actualContactVertices,v=Sum.inl (Sum.inl c) ∧ c.val.1=0) ∨
        (∃ m : Fin 2,v=Sum.inr m) := by
    as_aux_lemma =>
      cases v with
      | inr m => exact Or.inr ⟨m,rfl⟩
      | inl v =>
        by_cases ht : ∃ m,actualAttachedTailIncidence v m
        · obtain ⟨m,c,he,hc⟩ := ht
          subst v
          rw [hActualSameChosenTailAttachedActualSeamDegreeTwo c m hc] at hv
          norm_num at hv
        · have hn : ∀ m,¬actualAttachedTailIncidence v m := by
            intro m hm
            exact ht ⟨m,hm⟩
          rw [hActualAttachedOldVertexWithoutTailDegree v hn] at hv
          cases v with
          | inl c =>
            rcases hActualOddContactVertexOnInitialBoundaryOrMarkedTailSides c hv with hc | hc | hc
            · exact Or.inl ⟨c,rfl,hc⟩
            · exact False.elim (hn 0 ⟨c,rfl,by simpa [actualAttachedMarkHeight] using hc⟩)
            · exact False.elim (hn 1 ⟨c,rfl,by simpa [actualAttachedMarkHeight] using hc⟩)
          | inr e =>
            obtain ⟨e,j⟩ := e
            have hd : actualZeroGraph.degree (Sum.inr (e,j))=2 := by
              fin_cases j
              · exact (zeroSubdivisionDegrees e).1
              · exact (zeroSubdivisionDegrees e).2
            rw [hd] at hv
            norm_num at hv
  have hActualAttachedIncidenceCarriesSameChosenSquareTail
      (v : zeroVertex) (m : Fin 2) (hvm : actualAttachedTailIncidence v m) :
      ∃ c : actualContactVertices,v=Sum.inl c ∧
      ∃ Q : Path ((0,actualAttachedMarkHeight m) : Interval × Interval)
          (actualCentralCollarSquare c.val),IsEmbedding Q ∧
        (∀ t : Interval,t≠0 → (Q t).1∈Ioo (0 : Interval) 1 ∧ (Q t).2∈Ioo (0 : Interval) 1) ∧
        range Q∩range actualCentralCollarSquare={actualCentralCollarSquare c.val} ∧
        ((m=0 ∧ ∃ τ : actualLowerSeamContacts,c.val=(τ.val,0) ∧
          ∀ t,Q t=actualLowerSquareTail τ t) ∨
         (m=1 ∧ ∃ τ : actualUpperSeamContacts,c.val=(τ.val,1) ∧
          ∀ t,Q t=actualUpperSquareTail τ t)) := by
    as_aux_lemma =>
      obtain ⟨c,hvc,hc⟩ := hvm
      subst v
      fin_cases m
      · have hcy : c.val.2=0 := by simpa [actualAttachedMarkHeight] using hc
        have hcp : c.val=(c.val.1,0) := Prod.ext rfl hcy
        have hm := hActualContactVerticesImage c
        rw [hcp,hActualFiniteConeSweepLower] at hm
        let τ : actualLowerSeamContacts := ⟨c.val.1,hm⟩
        have he : actualCentralCollarSquare c.val=actualLowerSquareTail τ 1 :=
          (congrArg actualCentralCollarSquare hcp).trans
            (hActualLowerSameSquareTailEndMatchesCentral τ).symm
        let Q : Path ((0,actualAttachedMarkHeight 0) : Interval × Interval)
            (actualCentralCollarSquare c.val) :=
          (actualLowerSquareTail τ).cast (by simp [actualAttachedMarkHeight])
            (he.trans (Path.target _))
        refine ⟨c,rfl,Q,hActualLowerSquareTailEmbedding τ,?_,?_,?_⟩
        · intro t ht
          exact hActualLowerSquareTailProper τ ⟨t,ht⟩
        · change range (actualLowerSquareTail τ)∩range actualCentralCollarSquare=
            {actualCentralCollarSquare c.val}
          rw [he]
          exact hActualLowerSameSquareTailOnlyMeetsCentralAtSeam τ
        · exact Or.inl ⟨rfl,τ,hcp,fun t => rfl⟩
      · have hcy : c.val.2=1 := by simpa [actualAttachedMarkHeight] using hc
        have hcp : c.val=(c.val.1,1) := Prod.ext rfl hcy
        have hm := hActualContactVerticesImage c
        rw [hcp,hActualFiniteConeSweepUpper] at hm
        let τ : actualUpperSeamContacts := ⟨c.val.1,hm⟩
        have he : actualCentralCollarSquare c.val=actualUpperSquareTail τ 1 :=
          (congrArg actualCentralCollarSquare hcp).trans
            (hActualUpperSameSquareTailEndMatchesCentral τ).symm
        let Q : Path ((0,actualAttachedMarkHeight 1) : Interval × Interval)
            (actualCentralCollarSquare c.val) :=
          (actualUpperSquareTail τ).cast (by simp [actualAttachedMarkHeight])
            (he.trans (Path.target _))
        refine ⟨c,rfl,Q,hActualUpperSquareTailEmbedding τ,?_,?_,?_⟩
        · intro t ht
          exact hActualUpperSquareTailProper τ ⟨t,ht⟩
        · change range (actualUpperSquareTail τ)∩range actualCentralCollarSquare=
            {actualCentralCollarSquare c.val}
          rw [he]
          exact hActualUpperSameSquareTailOnlyMeetsCentralAtSeam τ
        · exact Or.inr ⟨rfl,τ,hcp,fun t => rfl⟩
  have hActualSpecifiedOriginalCrossingHasSameTailAttachedGraphPartner :
      ∃ w : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧
      ∃ v : actualAttachedContactVertex,v≠Sum.inl (Sum.inl w) ∧
        ((∃ c : actualContactVertices,v=Sum.inl (Sum.inl c) ∧ c.val.1=0) ∨
         (∃ m : Fin 2,v=Sum.inr m)) ∧
        ∃ P : actualAttachedContactGraph.Walk (Sum.inl (Sum.inl w)) v,P.IsPath := by
    as_aux_lemma =>
      obtain ⟨w,hw,hinitial,hodd⟩ := hActualSpecifiedOriginalCrossingProducesOddVertex
      have hd := hActualAttachedEveryInitialContactVertexDegreeOne w hinitial
      have hv : Odd (actualAttachedContactGraph.degree (Sum.inl (Sum.inl w))) := by
        rw [hd]
        norm_num
      obtain ⟨v,hvw,hvOdd,P,hP⟩ := CurveComplex.LocalSurgery.actual_odd_vertex_has_distinct_path_partner
        actualAttachedContactGraph (Sum.inl (Sum.inl w)) hv
      exact ⟨w,hw,hinitial,v,hvw,hActualAttachedOddContactVertexIsInitialOrMarked v hvOdd,P,hP⟩
  have hActualOuterProperCentralPathInteriorCollar
      (w z : actualContactVertices) (q : Path w.val z.val)
      (hproper : ∀ t,(q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → t=0 ∨ t=1) :
      ∀ t : Interval,t∈Ioo (0 : Interval) 1 →
        (actualCentralCollarSquare (q t)).1∈Ioo (0 : Interval) 1 ∧
        (actualCentralCollarSquare (q t)).2∈Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      intro t ht
      have hn : ¬(t=0 ∨ t=1) := by
        rintro (rfl | rfl)
        · exact lt_irrefl _ ht.1
        · exact lt_irrefl _ ht.2
      apply hActualCentralCollarSquareInterior
      constructor
      · apply lt_of_le_of_ne (q t).1.property.1
        intro he
        exact hn (hproper t (Or.inl (Subtype.ext he.symm)))
      · apply lt_of_le_of_ne (q t).1.property.2
        intro he
        exact hn (hproper t (Or.inr (Or.inl (Subtype.ext he))))
  have hActualSpecifiedCrossingProducesSameTailProperLeftCrosscut :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
          ∃ s : Interval,∃ J : Path (actualCentralCollarSquare w.val) ((0,s) : Interval × Interval),
            IsEmbedding J ∧
            (∀ t : Interval,t∈Ioo (0 : Interval) 1 →
              (J t).1∈Ioo (0 : Interval) 1 ∧ (J t).2∈Ioo (0 : Interval) 1) ∧
            ((z.val.1=0 ∧ s=actualCentralParameter z.val.2 ∧
                range J=range (fun t => actualCentralCollarSquare (q t))) ∨
             (s=0 ∧ ∃ τ : actualLowerSeamContacts,z.val=(τ.val,0) ∧
                range J=range (fun t => actualCentralCollarSquare (q t))∪range (actualLowerSquareTail τ)) ∨
             (s=1 ∧ ∃ τ : actualUpperSeamContacts,z.val=(τ.val,1) ∧
                range J=range (fun t => actualCentralCollarSquare (q t))∪range (actualUpperSquareTail τ))) := by
    as_aux_lemma =>
      obtain ⟨w,z,hwp,hw,hzw,hodd,P,hP,W,hWne,hW,hvertices,q,hq,himage,hproper,κ,hκ,hinside⟩ :=
        hActualSpecifiedCrossingProducesOuterProperOriginalContactPath
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        rw [←hκ t]
        exact ⟨κ t,rfl⟩
      rcases hActualOddContactVertexOnInitialBoundaryOrMarkedTailSides z hodd with hz | hz | hz
      · have hzp : z.val=(0,z.val.2) := Prod.ext hz rfl
        have hend : (0,actualCentralParameter z.val.2)=actualCentralCollarSquare z.val := by
          rw [hzp,hActualCentralCollarSquareInitial]
        let J : Path (actualCentralCollarSquare w.val) (0,actualCentralParameter z.val.2) :=
          (q.map actualCentralCollarSquare.continuous).cast rfl hend
        exact ⟨w,z,hwp,hw,q,hq,κ,hκ,actualCentralParameter z.val.2,J,
          hActualCentralCollarSquareEmbedding.comp hq,
          hActualOuterProperCentralPathInteriorCollar w z q hproper,
          Or.inl ⟨hz,rfl,rfl⟩⟩
      · have hzp : z.val=(z.val.1,0) := Prod.ext rfl hz
        have hm := hActualContactVerticesImage z
        rw [hzp,hActualFiniteConeSweepLower] at hm
        let τ : actualLowerSeamContacts := ⟨z.val.1,hm⟩
        obtain ⟨J,hJ,hJrange,hJinside⟩ := hActualLowerSameChosenTailProducesProperOriginalCrosscut
          w z q hq hproper hcontact τ hzp
        exact ⟨w,z,hwp,hw,q,hq,κ,hκ,0,J,hJ,hJinside,
          Or.inr (Or.inl ⟨rfl,τ,hzp,hJrange⟩)⟩
      · have hzp : z.val=(z.val.1,1) := Prod.ext rfl hz
        have hm := hActualContactVerticesImage z
        rw [hzp,hActualFiniteConeSweepUpper] at hm
        let τ : actualUpperSeamContacts := ⟨z.val.1,hm⟩
        obtain ⟨J,hJ,hJrange,hJinside⟩ := hActualUpperSameChosenTailProducesProperOriginalCrosscut
          w z q hq hproper hcontact τ hzp
        exact ⟨w,z,hwp,hw,q,hq,κ,hκ,1,J,hJ,hJinside,
          Or.inr (Or.inr ⟨rfl,τ,hzp,hJrange⟩)⟩
  have hActualProperLeftSquareCrosscutProducesLiteralLeftBoundaryCap
      {x y : Interval × Interval} (J : Path x y) (hJ : IsEmbedding J)
      (hx : x.1=0) (hy : y.1=0)
      (hinside : ∀ t : Interval,t∈Ioo (0 : Interval) 1 →
        (J t).1∈Ioo (0 : Interval) 1 ∧ (J t).2∈Ioo (0 : Interval) 1) :
      let N := CurveComplex.LocalSurgery.actualUnitSquareModelPlane
      let A := range (fun t : Interval => N (0,actualIntervalSegment x.2 y.2 t))
      let P := range (fun t : Interval => N (J t))
      ∃ B : Set Schoenflies.Plane,Schoenflies.IsCutPair Schoenflies.modelCurve (N x) (N y) A B ∧
        Schoenflies.IsJordanCurve (A∪P) ∧
        ((A∪P)∪Schoenflies.inside (A∪P))⊆Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve := by
    as_aux_lemma =>
      dsimp only
      let N := CurveComplex.LocalSurgery.actualUnitSquareModelPlane
      have hxy : x≠y := by
        intro he
        have hh : (0 : Interval)=1 := hJ.injective
          ((Path.source J).trans (he.trans (Path.target J).symm))
        norm_num at hh
      have hcoords : x.2≠y.2 := by
        intro he
        exact hxy (Prod.ext (hx.trans hy.symm) he)
      let L : Path x y := {
        toFun := fun t => (0,actualIntervalSegment x.2 y.2 t)
        continuous_toFun := by fun_prop
        source' := by
          apply Prod.ext
          · exact hx.symm
          · apply Subtype.ext
            change (1-(0 : ℝ))*x.2.val+0*y.2.val=x.2.val
            ring
        target' := by
          apply Prod.ext
          · exact hy.symm
          · apply Subtype.ext
            change (1-(1 : ℝ))*x.2.val+1*y.2.val=y.2.val
            ring }
      have hL : IsEmbedding L := by
        apply L.continuous.isClosedEmbedding _ |>.isEmbedding
        intro t u he
        exact actualIntervalSegmentInjectiveOfNe x.2 y.2 hcoords (congrArg Prod.snd he)
      let A := range (fun t : Interval => N (L t))
      let γ := J.map N.continuous
      have hA : Schoenflies.IsArcBetween A (N x) (N y) :=
        CurveComplex.LocalSurgery.actual_embedded_path_isArcBetween (L.map N.continuous)
          (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.comp hL)
      have hAC : A⊆Schoenflies.modelCurve := by
        rintro z ⟨t,rfl⟩
        exact CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary (L t) (Or.inl rfl)
      have hγ : Schoenflies.IsArcBetween (range γ) (N x) (N y) :=
        CurveComplex.LocalSurgery.actual_embedded_path_isArcBetween γ
          (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.comp hJ)
      have hPi : range γ\{N x,N y}⊆Schoenflies.inside Schoenflies.modelCurve := by
        rintro z ⟨⟨t,rfl⟩,hn⟩
        have ht0 : t≠0 := by
          intro he
          subst t
          exact hn (Or.inl (by change N (J 0)=N x;rw [Path.source]))
        have ht1 : t≠1 := by
          intro he
          subst t
          exact hn (Or.inr (mem_singleton_iff.mpr (by change N (J 1)=N y;rw [Path.target])))
        exact CurveComplex.LocalSurgery.actualUnitSquareModelPlaneInterior (J t)
          (hinside t ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩)
      obtain ⟨B,hcut⟩ := CurveComplex.LocalSurgery.actualBoundaryArcSelectsCutPair
        Schoenflies.isJordanCurve_modelCurve hA hAC
      have hJordan : Schoenflies.IsJordanCurve (A∪range γ) := by
        apply Schoenflies.isJordanCurve_union hA hγ
        intro z hzA hzγ
        by_contra hn
        have hznot : z∉({N x,N y} : Set Schoenflies.Plane) := by simpa using hn
        exact Schoenflies.inside_subset_compl (hPi ⟨hzγ,hznot⟩) (hAC hzA)
      have hpartition := CurveComplex.LocalSurgery.actual_crosscut_closed_cap_partition
        Schoenflies.isJordanCurve_modelCurve hγ hcut hPi
      refine ⟨B,hcut,hJordan,?_⟩
      intro z hz
      rw [←hpartition.1]
      exact Or.inl hz
  let actualOriginalLeftBoundaryEvents : Finset Interval := hcontacts.toFinset
  have hActualUnmarkedOriginalBoundaryEventIsPhysicalCrossing
      (t : Interval) (ht : t∈actualOriginalLeftBoundaryEvents) (ht0 : t≠0) (ht1 : t≠1) :
      b.val.map t∈ArcSurgery.crossings M a b := by
    as_aux_lemma =>
      have ha : b.val.map t∈a.val.image := hcontacts.mem_toFinset.mp ht
      have hm : b.val.map t∉(M.cover.branch : Set S) := by
        intro hm
        rcases b.val.marked_only_at_ends t hm with he | he
        · exact ht0 he
        · exact ht1 he
      exact ⟨⟨ha,hm⟩,⟨⟨t,rfl⟩,hm⟩⟩
  have hActualEveryUnmarkedPhysicalBoundaryEventIsSameAttachedInitialVertex
      (t : Interval) (ht : t∈actualOriginalLeftBoundaryEvents) (ht0 : t≠0) (ht1 : t≠1) :
      ∃ c : actualContactVertices,c.val.1=0 ∧
        actualAttachedSquareVertexPosition (Sum.inl (Sum.inl c))=(0,t) ∧
        actualAttachedContactGraph.degree (Sum.inl (Sum.inl c))=1 := by
    as_aux_lemma =>
      have hcross := hActualUnmarkedOriginalBoundaryEventIsPhysicalCrossing t ht ht0 ht1
      obtain ⟨c,hpoint,hc,hdegree⟩ := hActualEveryOriginalCrossingProducesDegreeOne t hcross
      have hcp : c.val=(0,c.val.2) := Prod.ext hc rfl
      have hb : b.val.map (actualCentralParameter c.val.2)=b.val.map t := by
        rw [←hActualCentralSweepInitial,←hActualFiniteConeSweepInitial,←hcp]
        exact hpoint
      have hparam := (NonLoopArc.isEmbedding (⟨b.val,hbne⟩ : NonLoopArc M)).injective hb
      refine ⟨c,hc,?_,hActualAttachedEveryInitialContactVertexDegreeOne c hc⟩
      change actualCentralCollarSquare c.val=(0,t)
      rw [hcp,hActualCentralCollarSquareInitial,hparam]
  have hActualSpecifiedCrossingProducesLiteralLeftBoundaryJordanCap :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧
      ∃ q : Path w.val z.val,IsEmbedding q ∧
      ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
      ∃ s : Interval,∃ J : Path (actualCentralCollarSquare w.val) ((0,s) : Interval × Interval),IsEmbedding J ∧
        (∀ t : Interval,t∈Ioo (0 : Interval) 1 →
          (J t).1∈Ioo (0 : Interval) 1 ∧ (J t).2∈Ioo (0 : Interval) 1) ∧
      ∃ B : Set Schoenflies.Plane,
        let N := CurveComplex.LocalSurgery.actualUnitSquareModelPlane
        let A := range (fun t : Interval => N (0,actualIntervalSegment (actualCentralParameter w.val.2) s t))
        let P := range (fun t : Interval => N (J t))
        Schoenflies.IsCutPair Schoenflies.modelCurve (N (actualCentralCollarSquare w.val)) (N (0,s)) A B ∧
        Schoenflies.IsJordanCurve (A∪P) ∧
        ((A∪P)∪Schoenflies.inside (A∪P))⊆Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve := by
    as_aux_lemma =>
      obtain ⟨w,z,hwp,hw,q,hq,κ,hκ,s,J,hJ,hinside,hroute⟩ :=
        hActualSpecifiedCrossingProducesSameTailProperLeftCrosscut
      have hwpair : w.val=(0,w.val.2) := Prod.ext hw rfl
      have hstart : actualCentralCollarSquare w.val=(0,actualCentralParameter w.val.2) := by
        rw [hwpair,hActualCentralCollarSquareInitial]
      obtain ⟨B,hcut,hJordan,hbound⟩ := hActualProperLeftSquareCrosscutProducesLiteralLeftBoundaryCap
        J hJ (by rw [hstart]) rfl hinside
      refine ⟨w,z,hwp,hw,q,hq,κ,hκ,s,J,hJ,hinside,B,?_,?_,?_⟩
      · simpa only [hstart] using hcut
      · simpa only [hstart] using hJordan
      · simpa only [hstart] using hbound
  let actualAttachedTailLabels := {e : zeroVertex × Fin 2 // actualAttachedTailIncidence e.1 e.2}
  letI : Fintype actualAttachedTailLabels := Fintype.ofFinite actualAttachedTailLabels
  have hActualSameChosenTailAttachedSquarePathProducer (e : actualAttachedTailLabels) :
      ∃ Q : Path ((0,actualAttachedMarkHeight e.val.2) : Interval × Interval)
          (actualCentralCollarSquare (zeroVertexPosition e.val.1)),IsEmbedding Q ∧
        (∀ t : Interval,t≠0 → (Q t).1∈Ioo (0 : Interval) 1 ∧ (Q t).2∈Ioo (0 : Interval) 1) ∧
        range Q∩range actualCentralCollarSquare={actualCentralCollarSquare (zeroVertexPosition e.val.1)} ∧
        ((e.val.2=0 ∧ ∃ τ : actualLowerSeamContacts,
          zeroVertexPosition e.val.1=(τ.val,0) ∧ ∀ t,Q t=actualLowerSquareTail τ t) ∨
         (e.val.2=1 ∧ ∃ τ : actualUpperSeamContacts,
          zeroVertexPosition e.val.1=(τ.val,1) ∧ ∀ t,Q t=actualUpperSquareTail τ t)) := by
    as_aux_lemma =>
      obtain ⟨c,hvc,Q,hQ,hproper,hattach,htags⟩ :=
        hActualAttachedIncidenceCarriesSameChosenSquareTail e.val.1 e.val.2 e.property
      have hpos : zeroVertexPosition e.val.1=c.val := by rw [hvc]
      let Q' : Path ((0,actualAttachedMarkHeight e.val.2) : Interval × Interval)
          (actualCentralCollarSquare (zeroVertexPosition e.val.1)) := Q.cast rfl (congrArg actualCentralCollarSquare hpos)
      refine ⟨Q',hQ,hproper,?_,?_⟩
      · change range Q∩range actualCentralCollarSquare={actualCentralCollarSquare (zeroVertexPosition e.val.1)}
        rw [hpos]
        exact hattach
      · simpa only [Q',Path.cast_coe,hpos] using htags
  choose actualSameAttachedSquareTail hActualSameAttachedSquareTailEmbedding
    hActualSameAttachedSquareTailInterior hActualSameAttachedSquareTailCentralAttachment
    hActualSameAttachedSquareTailIdentity using hActualSameChosenTailAttachedSquarePathProducer
  let actualAttachedCentralSquareEdgePath (e : actualNegativeFaceIntervals × Fin 3) :
      Path (actualCentralCollarSquare (zeroVertexPosition (actualSegmentStartVertex e)))
        (actualCentralCollarSquare (zeroVertexPosition (actualSegmentEndVertex e))) :=
    ((actualSegmentSquarePath e).map actualCentralCollarSquare.continuous).cast
      (congrArg actualCentralCollarSquare (actualSegmentStartPosition e))
      (congrArg actualCentralCollarSquare (actualSegmentEndPosition e))
  have hActualAttachedCentralSquareEdgePathEmbedding (e : actualNegativeFaceIntervals × Fin 3) :
      IsEmbedding (actualAttachedCentralSquareEdgePath e) :=
    hActualCentralCollarSquareEmbedding.comp (actualSegmentSquarePathEmbedding e)
  let actualAttachedEdgeLabels := Sum (actualNegativeFaceIntervals × Fin 3) actualAttachedTailLabels
  letI : Fintype actualAttachedEdgeLabels := Fintype.ofFinite actualAttachedEdgeLabels
  let actualAttachedEdgeStart : actualAttachedEdgeLabels → actualAttachedContactVertex := fun e => match e with
    | Sum.inl e => Sum.inl (actualSegmentStartVertex e)
    | Sum.inr e => Sum.inr e.val.2
  let actualAttachedEdgeEnd : actualAttachedEdgeLabels → actualAttachedContactVertex := fun e => match e with
    | Sum.inl e => Sum.inl (actualSegmentEndVertex e)
    | Sum.inr e => Sum.inl e.val.1
  let actualAttachedSquareEdgePath (e : actualAttachedEdgeLabels) :
      Path (actualAttachedSquareVertexPosition (actualAttachedEdgeStart e))
        (actualAttachedSquareVertexPosition (actualAttachedEdgeEnd e)) :=
    match e with
    | Sum.inl e => actualAttachedCentralSquareEdgePath e
    | Sum.inr e => actualSameAttachedSquareTail e
  have hActualAttachedSquareEdgePathEmbedding (e : actualAttachedEdgeLabels) :
      IsEmbedding (actualAttachedSquareEdgePath e) := by
    as_aux_lemma =>
      cases e with
      | inl e => exact hActualAttachedCentralSquareEdgePathEmbedding e
      | inr e => exact hActualSameAttachedSquareTailEmbedding e
  have hActualAttachedCentralSquareEdgeMeetsVerticesOnlyAtEnds
      (e : actualNegativeFaceIntervals × Fin 3) (v : actualAttachedContactVertex) (t : Interval)
      (he : actualAttachedSquareVertexPosition v=actualAttachedCentralSquareEdgePath e t) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      cases v with
      | inl v =>
        have hp : zeroVertexPosition v=actualSegmentSquarePath e t :=
          hActualCentralCollarSquareEmbedding.injective he
        have hplane : actualPlanarVertexPosition v=actualSegmentPlanarPath e t :=
          congrArg actualParameterSquarePlane hp
        have hmem : actualPlanarVertexPosition v∈Graph.edgeArc actualPlanarDrawing e :=
          ⟨t.val,t.property,(Path.extend_apply (actualSegmentPlanarPath e) t.property).trans hplane.symm⟩
        rcases actualSegmentVertexOnArcIsEndpoint e v hmem with hv | hv
        · exact Or.inl ((actualSegmentPlanarPathEmbedding e).injective (hplane.symm.trans hv))
        · exact Or.inr ((actualSegmentPlanarPathEmbedding e).injective (hplane.symm.trans hv))
      | inr m =>
        exact False.elim (hActualCentralCollarSquareAvoidsBothMarkedTips (actualSegmentSquarePath e t)
          (actualAttachedMarkHeight m) (by fin_cases m <;> simp [actualAttachedMarkHeight]) he.symm)
  have hActualSameAttachedSquareTailMeetsVerticesOnlyAtEnds
      (e : actualAttachedTailLabels) (v : actualAttachedContactVertex) (t : Interval)
      (he : actualAttachedSquareVertexPosition v=actualSameAttachedSquareTail e t) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      cases v with
      | inl v =>
        have hm : actualSameAttachedSquareTail e t∈
            range (actualSameAttachedSquareTail e)∩range actualCentralCollarSquare :=
          ⟨⟨t,rfl⟩,⟨zeroVertexPosition v,he⟩⟩
        rw [hActualSameAttachedSquareTailCentralAttachment e] at hm
        have hp : actualSameAttachedSquareTail e t=actualSameAttachedSquareTail e 1 :=
          (mem_singleton_iff.mp hm).trans (Path.target _).symm
        exact Or.inr ((hActualSameAttachedSquareTailEmbedding e).injective hp)
      | inr m =>
        by_cases ht : t=0
        · exact Or.inl ht
        have hi := (hActualSameAttachedSquareTailInterior e t ht).1.1
        have hz : (actualSameAttachedSquareTail e t).1=0 := (congrArg Prod.fst he).symm
        rw [hz] at hi
        exact False.elim (lt_irrefl _ hi)
  have hActualAttachedSquareEdgesMeetVerticesOnlyAtEnds
      (e : actualAttachedEdgeLabels) (v : actualAttachedContactVertex) (t : Interval)
      (he : actualAttachedSquareVertexPosition v=actualAttachedSquareEdgePath e t) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      cases e with
      | inl e => exact hActualAttachedCentralSquareEdgeMeetsVerticesOnlyAtEnds e v t he
      | inr e => exact hActualSameAttachedSquareTailMeetsVerticesOnlyAtEnds e v t he
  have hActualSameAttachedTailLabelDeterminedBySeamPosition
      (e f : actualAttachedTailLabels)
      (hpos : zeroVertexPosition e.val.1=zeroVertexPosition f.val.1) (hmark : e.val.2=f.val.2) : e=f := by
    as_aux_lemma =>
      exact Subtype.ext (Prod.ext (zeroVertexPositionInjective hpos) hmark)
  have hActualDistinctSameAttachedSquareTailsOnlyMeetAtStarts
      (e f : actualAttachedTailLabels) (hef : e≠f) (t u : Interval)
      (he : actualSameAttachedSquareTail e t=actualSameAttachedSquareTail f u) : t=0 ∧ u=0 := by
    as_aux_lemma =>
      rcases hActualSameAttachedSquareTailIdentity e with ⟨he0,τ,hepos,hetrace⟩ | ⟨he1,τ,hepos,hetrace⟩ <;>
        rcases hActualSameAttachedSquareTailIdentity f with ⟨hf0,υ,hfpos,hftrace⟩ | ⟨hf1,υ,hfpos,hftrace⟩
      · have hτυ : τ≠υ := by
          intro hτυ
          subst υ
          exact hef (hActualSameAttachedTailLabelDeterminedBySeamPosition e f
            (hepos.trans hfpos.symm) (he0.trans hf0.symm))
        have hp : actualLowerSquareTail τ t=actualLowerSquareTail υ u :=
          (hetrace t).symm.trans (he.trans (hftrace u))
        have hm : actualLowerSquareTail τ t∈range (actualLowerSquareTail τ)∩range (actualLowerSquareTail υ) :=
          ⟨⟨t,rfl⟩,⟨u,hp.symm⟩⟩
        rw [hActualLowerSameSquareTailFamilyOnlyMeetsAtMarkedTip τ υ hτυ] at hm
        have ht := (hActualLowerSquareTailEmbedding τ).injective
          ((mem_singleton_iff.mp hm).trans (Path.source _).symm)
        have hu := (hActualLowerSquareTailEmbedding υ).injective
          (hp.symm.trans ((mem_singleton_iff.mp hm).trans (Path.source _).symm))
        exact ⟨ht,hu⟩
      · have hp : actualLowerSquareTail τ t=actualUpperSquareTail υ u :=
          (hetrace t).symm.trans (he.trans (hftrace u))
        exact False.elim (Set.disjoint_left.mp (hActualLowerUpperSameSquareTailFamiliesDisjoint τ υ)
          ⟨t,rfl⟩ ⟨u,hp.symm⟩)
      · have hp : actualLowerSquareTail υ u=actualUpperSquareTail τ t :=
          (hftrace u).symm.trans (he.symm.trans (hetrace t))
        exact False.elim (Set.disjoint_left.mp (hActualLowerUpperSameSquareTailFamiliesDisjoint υ τ)
          ⟨u,rfl⟩ ⟨t,hp.symm⟩)
      · have hτυ : τ≠υ := by
          intro hτυ
          subst υ
          exact hef (hActualSameAttachedTailLabelDeterminedBySeamPosition e f
            (hepos.trans hfpos.symm) (he1.trans hf1.symm))
        have hp : actualUpperSquareTail τ t=actualUpperSquareTail υ u :=
          (hetrace t).symm.trans (he.trans (hftrace u))
        have hm : actualUpperSquareTail τ t∈range (actualUpperSquareTail τ)∩range (actualUpperSquareTail υ) :=
          ⟨⟨t,rfl⟩,⟨u,hp.symm⟩⟩
        rw [hActualUpperSameSquareTailFamilyOnlyMeetsAtMarkedTip τ υ hτυ] at hm
        have ht := (hActualUpperSquareTailEmbedding τ).injective
          ((mem_singleton_iff.mp hm).trans (Path.source _).symm)
        have hu := (hActualUpperSquareTailEmbedding υ).injective
          (hp.symm.trans ((mem_singleton_iff.mp hm).trans (Path.source _).symm))
        exact ⟨ht,hu⟩
  have hActualAttachedCentralAndSameSquareTailIntersectionOnlyAtEnds
      (e : actualNegativeFaceIntervals × Fin 3) (f : actualAttachedTailLabels) (t u : Interval)
      (he : actualAttachedCentralSquareEdgePath e t=actualSameAttachedSquareTail f u) :
      (t=0 ∨ t=1) ∧ u=1 := by
    as_aux_lemma =>
      have hm : actualSameAttachedSquareTail f u∈
          range (actualSameAttachedSquareTail f)∩range actualCentralCollarSquare :=
        ⟨⟨u,rfl⟩,⟨actualSegmentSquarePath e t,he⟩⟩
      rw [hActualSameAttachedSquareTailCentralAttachment f] at hm
      have hu : u=1 := (hActualSameAttachedSquareTailEmbedding f).injective
        ((mem_singleton_iff.mp hm).trans (Path.target _).symm)
      have hv : actualAttachedSquareVertexPosition (Sum.inl f.val.1)=actualAttachedCentralSquareEdgePath e t :=
        (mem_singleton_iff.mp hm).symm.trans he.symm
      exact ⟨hActualAttachedCentralSquareEdgeMeetsVerticesOnlyAtEnds e (Sum.inl f.val.1) t hv,hu⟩
  have hActualDistinctAttachedCentralSquareEdgesOnlyMeetAtEnds
      (e f : actualNegativeFaceIntervals × Fin 3) (hef : e≠f) (t u : Interval)
      (he : actualAttachedCentralSquareEdgePath e t=actualAttachedCentralSquareEdgePath f u) :
      (t=0 ∨ t=1) ∧ (u=0 ∨ u=1) := by
    as_aux_lemma =>
      have hp : actualSegmentSquarePath e t=actualSegmentSquarePath f u :=
        hActualCentralCollarSquareEmbedding.injective he
      have hplane : actualSegmentPlanarPath e t=actualSegmentPlanarPath f u :=
        congrArg actualParameterSquarePlane hp
      obtain ⟨heend,hfend⟩ := actualDistinctSegmentArcIntersection e f hef (actualSegmentPlanarPath e t)
        ⟨t.val,t.property,Path.extend_apply (actualSegmentPlanarPath e) t.property⟩
        ⟨u.val,u.property,(Path.extend_apply (actualSegmentPlanarPath f) u.property).trans hplane.symm⟩
      constructor
      · rcases heend with h | h
        · exact Or.inl ((actualSegmentPlanarPathEmbedding e).injective h)
        · exact Or.inr ((actualSegmentPlanarPathEmbedding e).injective h)
      · rcases hfend with h | h
        · exact Or.inl ((actualSegmentPlanarPathEmbedding f).injective (hplane.symm.trans h))
        · exact Or.inr ((actualSegmentPlanarPathEmbedding f).injective (hplane.symm.trans h))
  have hActualDistinctAttachedSquareEdgesOnlyMeetAtEnds
      (e f : actualAttachedEdgeLabels) (hef : e≠f) (t u : Interval)
      (he : actualAttachedSquareEdgePath e t=actualAttachedSquareEdgePath f u) :
      (t=0 ∨ t=1) ∧ (u=0 ∨ u=1) := by
    as_aux_lemma =>
      cases e with
      | inl e =>
        cases f with
        | inl f =>
            exact hActualDistinctAttachedCentralSquareEdgesOnlyMeetAtEnds e f
              (fun h => hef (congrArg Sum.inl h)) t u he
        | inr f =>
          obtain ⟨ht,hu⟩ := hActualAttachedCentralAndSameSquareTailIntersectionOnlyAtEnds e f t u he
          exact ⟨ht,Or.inr hu⟩
      | inr e =>
        cases f with
        | inl f =>
          obtain ⟨hu,ht⟩ := hActualAttachedCentralAndSameSquareTailIntersectionOnlyAtEnds f e u t he.symm
          exact ⟨Or.inr ht,hu⟩
        | inr f =>
          obtain ⟨ht,hu⟩ := hActualDistinctSameAttachedSquareTailsOnlyMeetAtStarts e f
            (fun h => hef (congrArg Sum.inr h)) t u he
          exact ⟨Or.inl ht,Or.inl hu⟩
  let actualAttachedPlanarVertexPosition (v : actualAttachedContactVertex) : Schoenflies.Plane :=
    CurveComplex.LocalSurgery.actualUnitSquareModelPlane (actualAttachedSquareVertexPosition v)
  have hActualAttachedPlanarVertexPositionInjective : Function.Injective actualAttachedPlanarVertexPosition :=
    CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective.comp
      hActualAttachedSquareVertexPositionInjective
  let actualAttachedPlanarEdgePath (e : actualAttachedEdgeLabels) :=
    (actualAttachedSquareEdgePath e).map CurveComplex.LocalSurgery.actualUnitSquareModelPlane.continuous
  have hActualAttachedPlanarEdgePathEmbedding (e : actualAttachedEdgeLabels) :
      IsEmbedding (actualAttachedPlanarEdgePath e) :=
    CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.comp (hActualAttachedSquareEdgePathEmbedding e)
  have hActualAttachedPlanarEdgeSource (e : actualAttachedEdgeLabels) :
      actualAttachedPlanarEdgePath e 0=actualAttachedPlanarVertexPosition (actualAttachedEdgeStart e) := Path.source _
  have hActualAttachedPlanarEdgeTarget (e : actualAttachedEdgeLabels) :
      actualAttachedPlanarEdgePath e 1=actualAttachedPlanarVertexPosition (actualAttachedEdgeEnd e) := Path.target _
  let actualAttachedPlanarGraph : Graph Schoenflies.Plane actualAttachedEdgeLabels := {
    vertexSet := range actualAttachedPlanarVertexPosition
    edgeSet := Set.univ
    IsLink := fun e x y =>
      (x=actualAttachedPlanarEdgePath e 0 ∧ y=actualAttachedPlanarEdgePath e 1) ∨
      (x=actualAttachedPlanarEdgePath e 1 ∧ y=actualAttachedPlanarEdgePath e 0)
    isLink_symm := by
      intro e he
      constructor
      intro x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inr ⟨hy,hx⟩
      · exact Or.inl ⟨hy,hx⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y z w hx hz
      rcases hx with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rcases hz with ⟨hz,hw⟩ | ⟨hz,hw⟩
      · exact Or.inl (hx.trans hz.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inl (hx.trans hz.symm)
    edge_mem_iff_exists_isLink := by
      intro e
      constructor
      · intro he
        exact ⟨actualAttachedPlanarEdgePath e 0,actualAttachedPlanarEdgePath e 1,Or.inl ⟨rfl,rfl⟩⟩
      · intro he
        exact mem_univ _
    left_mem_of_isLink := by
      intro e x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨actualAttachedEdgeStart e,(hActualAttachedPlanarEdgeSource e).symm.trans hx.symm⟩
      · exact ⟨actualAttachedEdgeEnd e,(hActualAttachedPlanarEdgeTarget e).symm.trans hx.symm⟩ }
  let actualAttachedPlanarDrawing (e : actualAttachedEdgeLabels) : ℝ → Schoenflies.Plane :=
    (actualAttachedPlanarEdgePath e).extend
  have hActualAttachedPlanarEdgePointParameter (e : actualAttachedEdgeLabels) (z : Schoenflies.Plane)
      (hz : z∈Graph.edgeArc actualAttachedPlanarDrawing e) :
      ∃ t : Interval,actualAttachedPlanarEdgePath e t=z := by
    as_aux_lemma =>
      obtain ⟨t,ht,he⟩ := hz
      exact ⟨⟨t,ht⟩,(Path.extend_apply (actualAttachedPlanarEdgePath e) ht).symm.trans he⟩
  have hActualAttachedPlanarVertexOnEdgeOnlyEnds (e : actualAttachedEdgeLabels)
      (v : actualAttachedContactVertex) (hv : actualAttachedPlanarVertexPosition v∈Graph.edgeArc actualAttachedPlanarDrawing e) :
      actualAttachedPlanarVertexPosition v=actualAttachedPlanarEdgePath e 0 ∨
        actualAttachedPlanarVertexPosition v=actualAttachedPlanarEdgePath e 1 := by
    as_aux_lemma =>
      obtain ⟨t,he⟩ := hActualAttachedPlanarEdgePointParameter e _ hv
      have hp : actualAttachedSquareVertexPosition v=actualAttachedSquareEdgePath e t :=
        CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective he.symm
      rcases hActualAttachedSquareEdgesMeetVerticesOnlyAtEnds e v t hp with rfl | rfl
      · exact Or.inl he.symm
      · exact Or.inr he.symm
  have hActualAttachedPlanarDistinctEdgesOnlyMeetAtEnds (e f : actualAttachedEdgeLabels) (hef : e≠f)
      (z : Schoenflies.Plane) (he : z∈Graph.edgeArc actualAttachedPlanarDrawing e)
      (hf : z∈Graph.edgeArc actualAttachedPlanarDrawing f) :
      (z=actualAttachedPlanarEdgePath e 0 ∨ z=actualAttachedPlanarEdgePath e 1) ∧
      (z=actualAttachedPlanarEdgePath f 0 ∨ z=actualAttachedPlanarEdgePath f 1) := by
    as_aux_lemma =>
      obtain ⟨t,het⟩ := hActualAttachedPlanarEdgePointParameter e z he
      obtain ⟨u,hfu⟩ := hActualAttachedPlanarEdgePointParameter f z hf
      have hp : actualAttachedSquareEdgePath e t=actualAttachedSquareEdgePath f u :=
        CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective (het.trans hfu.symm)
      obtain ⟨hte,huf⟩ := hActualDistinctAttachedSquareEdgesOnlyMeetAtEnds e f hef t u hp
      constructor
      · rcases hte with rfl | rfl
        · exact Or.inl het.symm
        · exact Or.inr het.symm
      · rcases huf with rfl | rfl
        · exact Or.inl hfu.symm
        · exact Or.inr hfu.symm
  have hActualSameChosenTailAttachedPlanarDrawingIsDrawing :
      Graph.IsDrawing actualAttachedPlanarGraph actualAttachedPlanarDrawing := by
    as_aux_lemma =>
      refine ⟨?_,?_,?_⟩
      · intro e he
        refine ⟨(actualAttachedPlanarEdgePath e).continuous_extend.continuousOn,?_,?_⟩
        · intro t ht u hu he
          change (actualAttachedPlanarEdgePath e).extend t=(actualAttachedPlanarEdgePath e).extend u at he
          rw [Path.extend_apply _ ht,Path.extend_apply _ hu] at he
          exact congrArg Subtype.val ((hActualAttachedPlanarEdgePathEmbedding e).injective he)
        · change (actualAttachedPlanarDrawing e 0=actualAttachedPlanarEdgePath e 0 ∧
              actualAttachedPlanarDrawing e 1=actualAttachedPlanarEdgePath e 1) ∨ _
          exact Or.inl ⟨by simp [actualAttachedPlanarDrawing],by simp [actualAttachedPlanarDrawing]⟩
      · intro e x y z hlink hz hze
        obtain ⟨v,rfl⟩ := hz
        have hend := hActualAttachedPlanarVertexOnEdgeOnlyEnds e v hze
        change (_=actualAttachedPlanarEdgePath e 0 ∧ _=actualAttachedPlanarEdgePath e 1) ∨
          (_=actualAttachedPlanarEdgePath e 1 ∧ _=actualAttachedPlanarEdgePath e 0) at hlink
        rcases hlink with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hend
        · exact hend.elim Or.inr Or.inl
      · intro e f he hf hef z hze hzf
        obtain ⟨heend,hfend⟩ := hActualAttachedPlanarDistinctEdgesOnlyMeetAtEnds e f hef z hze hzf
        have hv : z∈actualAttachedPlanarGraph.vertexSet := by
          rcases heend with h | h
          · exact ⟨actualAttachedEdgeStart e,(hActualAttachedPlanarEdgeSource e).symm.trans h.symm⟩
          · exact ⟨actualAttachedEdgeEnd e,(hActualAttachedPlanarEdgeTarget e).symm.trans h.symm⟩
        refine ⟨hv,?_,?_⟩
        · rcases heend with h | h
          · exact ⟨actualAttachedPlanarEdgePath e 1,Or.inl ⟨h,rfl⟩⟩
          · exact ⟨actualAttachedPlanarEdgePath e 0,Or.inr ⟨h,rfl⟩⟩
        · rcases hfend with h | h
          · exact ⟨actualAttachedPlanarEdgePath f 1,Or.inl ⟨h,rfl⟩⟩
          · exact ⟨actualAttachedPlanarEdgePath f 0,Or.inr ⟨h,rfl⟩⟩
  have hActualAttachedCentralSquareEdgeInterior (e : actualNegativeFaceIntervals × Fin 3)
      (t : Interval) (ht : t∈Ioo (0 : Interval) 1) :
      (actualAttachedCentralSquareEdgePath e t).1∈Ioo (0 : Interval) 1 ∧
        (actualAttachedCentralSquareEdgePath e t).2∈Ioo (0 : Interval) 1 := by
      let s := actualIntervalSegment (actualSegmentStartParameter e) (actualSegmentEndParameter e) t
      have hbetween := actualIntervalSegmentInterior (actualSegmentStartParameter e)
        (actualSegmentEndParameter e) t (actualSegmentParameterOrder e) ht
      have hs : s∈Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_lt (actualSegmentStartParameter e).property.1 hbetween.1,
          lt_of_lt_of_le hbetween.2 (actualSegmentEndParameter e).property.2⟩
      have hno : ¬((actualGlobalContactArcs e.1 s).1=0 ∨ (actualGlobalContactArcs e.1 s).1=1) := by
        intro hx
        have hed := hActualGlobalContactArcOnOuterBoundaryIsEndpoint e.1 s
          (hx.elim Or.inl (fun h => Or.inr (Or.inl h)))
        rcases hed with he0 | he1
        · exact (ne_of_gt hs.1) he0
        · exact (ne_of_lt hs.2) he1
      apply hActualCentralCollarSquareInterior (actualSegmentSquarePath e t)
      constructor
      · exact unitInterval.pos_iff_ne_zero.mpr (fun h => hno (Or.inl h))
      · exact unitInterval.lt_one_iff_ne_one.mpr (fun h => hno (Or.inr h))
  have hActualAttachedSquareEdgeInterior (e : actualAttachedEdgeLabels) (t : Interval)
      (ht : t∈Ioo (0 : Interval) 1) :
      (actualAttachedSquareEdgePath e t).1∈Ioo (0 : Interval) 1 ∧
        (actualAttachedSquareEdgePath e t).2∈Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      cases e with
      | inl e => exact hActualAttachedCentralSquareEdgeInterior e t ht
      | inr e => exact hActualSameAttachedSquareTailInterior e t (ne_of_gt ht.1)
  have hActualSameTailAttachedPlanarEdgeInterior (e : actualAttachedEdgeLabels) (t : Interval)
      (ht : t∈Ioo (0 : Interval) 1) : actualAttachedPlanarEdgePath e t∈Schoenflies.inside Schoenflies.modelCurve :=
    CurveComplex.LocalSurgery.actualUnitSquareModelPlaneInterior _ (hActualAttachedSquareEdgeInterior e t ht)
  have hActualSameTailAttachedPlanarEdgeBoundaryOnlyEndpoints (e : actualAttachedEdgeLabels) (t : Interval)
      (ht : actualAttachedPlanarEdgePath e t∈Schoenflies.modelCurve) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      by_cases he : t=0 ∨ t=1
      · exact he
      have hti : t∈Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun h => he (Or.inl h.symm)),
          lt_of_le_of_ne t.property.2 (fun h => he (Or.inr h))⟩
      exact False.elim (Schoenflies.inside_subset_compl (hActualSameTailAttachedPlanarEdgeInterior e t hti) ht)
  have hActualSameAttachedGraphAdjacencyHasLiteralEdge
      {v w : actualAttachedContactVertex} (hvw : actualAttachedContactGraph.Adj v w) :
      ∃ e : actualAttachedEdgeLabels,
        (v=actualAttachedEdgeStart e ∧ w=actualAttachedEdgeEnd e) ∨
        (v=actualAttachedEdgeEnd e ∧ w=actualAttachedEdgeStart e) := by
    as_aux_lemma =>
      cases v with
      | inl v =>
        cases w with
        | inl w =>
          obtain ⟨e,he⟩ := hActualContactGraphAdjacencyProducesPlanarLink hvw
          change (_=actualSegmentPlanarPath e 0 ∧ _=actualSegmentPlanarPath e 1) ∨
            (_=actualSegmentPlanarPath e 1 ∧ _=actualSegmentPlanarPath e 0) at he
          rcases he with ⟨hv,hw⟩ | ⟨hv,hw⟩
          · have hvs := actualPlanarVertexPositionInjective (hv.trans (actualSegmentPlanarSource e))
            have hwe := actualPlanarVertexPositionInjective (hw.trans (actualSegmentPlanarTarget e))
            exact ⟨Sum.inl e,Or.inl ⟨congrArg Sum.inl hvs,congrArg Sum.inl hwe⟩⟩
          · have hve := actualPlanarVertexPositionInjective (hv.trans (actualSegmentPlanarTarget e))
            have hws := actualPlanarVertexPositionInjective (hw.trans (actualSegmentPlanarSource e))
            exact ⟨Sum.inl e,Or.inr ⟨congrArg Sum.inl hve,congrArg Sum.inl hws⟩⟩
        | inr m =>
          let e : actualAttachedTailLabels := ⟨(v,m),hvw⟩
          exact ⟨Sum.inr e,Or.inr ⟨rfl,rfl⟩⟩
      | inr m =>
        cases w with
        | inl w =>
          let e : actualAttachedTailLabels := ⟨(w,m),hvw⟩
          exact ⟨Sum.inr e,Or.inl ⟨rfl,rfl⟩⟩
        | inr n => exact hvw.elim
  have hActualSameAttachedGraphAdjacencyProducesPlanarLink
      {v w : actualAttachedContactVertex} (hvw : actualAttachedContactGraph.Adj v w) :
      ∃ e,actualAttachedPlanarGraph.IsLink e (actualAttachedPlanarVertexPosition v)
        (actualAttachedPlanarVertexPosition w) := by
    as_aux_lemma =>
      obtain ⟨e,he⟩ := hActualSameAttachedGraphAdjacencyHasLiteralEdge hvw
      refine ⟨e,?_⟩
      change (_=actualAttachedPlanarEdgePath e 0 ∧ _=actualAttachedPlanarEdgePath e 1) ∨
        (_=actualAttachedPlanarEdgePath e 1 ∧ _=actualAttachedPlanarEdgePath e 0)
      rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨(hActualAttachedPlanarEdgeSource e).symm,(hActualAttachedPlanarEdgeTarget e).symm⟩
      · exact Or.inr ⟨(hActualAttachedPlanarEdgeTarget e).symm,(hActualAttachedPlanarEdgeSource e).symm⟩
  have hActualSpecifiedOriginalCrossingHasSameTailAttachedDrawnCarrier :
      ∃ w : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧
      ∃ v : actualAttachedContactVertex,v≠Sum.inl (Sum.inl w) ∧
        ((∃ c : actualContactVertices,v=Sum.inl (Sum.inl c) ∧ c.val.1=0) ∨
         (∃ m : Fin 2,v=Sum.inr m)) ∧
      ∃ P : actualAttachedContactGraph.Walk (Sum.inl (Sum.inl w)) v,P.IsPath ∧
      ∃ W : List actualAttachedEdgeLabels,W≠[] ∧
        actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition (Sum.inl (Sum.inl w))) W
          (actualAttachedPlanarVertexPosition v) ∧
        actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition (Sum.inl (Sum.inl w))) W=
          actualAttachedPlanarVertexPosition '' {r | r∈P.support} ∧
        Schoenflies.IsArcBetween (Graph.edgesCover actualAttachedPlanarDrawing W)
          (actualAttachedPlanarVertexPosition (Sum.inl (Sum.inl w))) (actualAttachedPlanarVertexPosition v) := by
    as_aux_lemma =>
      obtain ⟨w,hw,hinitial,v,hvw,hboundary,P,hP⟩ := hActualSpecifiedOriginalCrossingHasSameTailAttachedGraphPartner
      obtain ⟨W,hW,hvertices⟩ := CurveComplex.LocalSurgery.actual_simple_graph_path_to_labeled_graph_with_vertices
        actualAttachedContactGraph actualAttachedPlanarGraph actualAttachedPlanarVertexPosition
        hActualAttachedPlanarVertexPositionInjective (fun r => ⟨r,rfl⟩)
        (fun h => hActualSameAttachedGraphAdjacencyProducesPlanarLink h) P hP
      have hWne : W≠[] := by
        intro he
        rw [he] at hW
        have hp : CurveComplex.LocalSurgery.actualUnitSquareModelPlane
            (actualAttachedSquareVertexPosition (Sum.inl (Sum.inl w)))=
            CurveComplex.LocalSurgery.actualUnitSquareModelPlane (actualAttachedSquareVertexPosition v) :=
          hW.isWalk.eq_of_nil
        have hsquare : actualAttachedSquareVertexPosition (Sum.inl (Sum.inl w))=
            actualAttachedSquareVertexPosition v :=
          CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective hp
        have hveq : Sum.inl (Sum.inl w)=v := hActualAttachedSquareVertexPositionInjective hsquare
        exact hvw hveq.symm
      exact ⟨w,hw,hinitial,v,hvw,hboundary,P,hP,W,hWne,hW,hvertices,
        hActualSameChosenTailAttachedPlanarDrawingIsDrawing.path_isArcBetween hW hWne⟩
  have hActualAttachedPlanarEdgeArcModelBoundaryOnlyEnds
      (e : actualAttachedEdgeLabels) (x : Schoenflies.Plane)
      (hx : x∈Graph.edgeArc actualAttachedPlanarDrawing e) (hxmodel : x∈Schoenflies.modelCurve) :
      x=actualAttachedPlanarEdgePath e 0 ∨ x=actualAttachedPlanarEdgePath e 1 := by
    as_aux_lemma =>
      obtain ⟨t,he⟩ := hActualAttachedPlanarEdgePointParameter e x hx
      have ht := hActualSameTailAttachedPlanarEdgeBoundaryOnlyEndpoints e t (he.symm ▸ hxmodel)
      rcases ht with rfl | rfl
      · exact Or.inl he.symm
      · exact Or.inr he.symm
  have hActualAttachedOddVertexOnModelBoundary
      (v : actualAttachedContactVertex) (hv : Odd (actualAttachedContactGraph.degree v)) :
      actualAttachedPlanarVertexPosition v∈Schoenflies.modelCurve := by
    as_aux_lemma =>
      rcases hActualAttachedOddContactVertexIsInitialOrMarked v hv with ⟨c,rfl,hc⟩ | ⟨m,rfl⟩
      · apply CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary
        apply Or.inl
        change (actualCentralCollarSquare c.val).1=0
        have hcp : c.val=(0,c.val.2) := Prod.ext hc rfl
        rw [hcp,hActualCentralCollarSquareInitial]
      · exact CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inl rfl)
  let actualAttachedClosedCapZeroGraph (D : Set Schoenflies.Plane) : SimpleGraph actualAttachedContactVertex := {
    Adj := fun v w => actualAttachedContactGraph.Adj v w ∧
      ∃ q : actualAttachedEdgeLabels, actualAttachedPlanarGraph.IsLink q
        (actualAttachedPlanarVertexPosition v) (actualAttachedPlanarVertexPosition w) ∧
        Graph.edgeArc actualAttachedPlanarDrawing q ⊆ D
    symm := ⟨by
      intro v w hvw
      obtain ⟨hvw,q,hq,hD⟩ := hvw
      exact ⟨hvw.symm,q,hq.symm,hD⟩⟩
    loopless := by
      refine ⟨?_⟩
      intro v hv
      exact actualAttachedContactGraph.loopless.irrefl v hv.1 }
  have actualAttachedClosedCapGraph_le (D : Set Schoenflies.Plane) :
      actualAttachedClosedCapZeroGraph D ≤ actualAttachedContactGraph := fun v w h => h.1
  have actualAttachedClosedCapGraphOutsideDegreeZero (D : Set Schoenflies.Plane) (v : actualAttachedContactVertex)
      (hv : actualAttachedPlanarVertexPosition v ∉ D) : (actualAttachedClosedCapZeroGraph D).degree v = 0 := by
    apply (SimpleGraph.degree_eq_zero (actualAttachedClosedCapZeroGraph D) v).mpr
    intro w hw
    obtain ⟨hvw,q,hq,hD⟩ := hw
    exact hv (hD (hActualSameChosenTailAttachedPlanarDrawingIsDrawing.edge_isArcBetween hq).left_mem)
  have actualAttachedClosedCapGraphDegreeAtMostOriginal (D : Set Schoenflies.Plane) (v : actualAttachedContactVertex) :
      (actualAttachedClosedCapZeroGraph D).degree v ≤ actualAttachedContactGraph.degree v :=
    by simpa only [←SimpleGraph.ncard_neighborSet] using
      (SimpleGraph.degree_le_of_le (v := v) (actualAttachedClosedCapGraph_le D))
  have actualAttachedClosedCapGraphInteriorHasAllOriginalNeighbors
      (A : Set Schoenflies.Plane) (W : List (actualAttachedEdgeLabels))
      (hA : A ⊆ Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))
      (v w : actualAttachedContactVertex) (hv : actualAttachedPlanarVertexPosition v ∈
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))
      (hvw : actualAttachedContactGraph.Adj v w) :
      (actualAttachedClosedCapZeroGraph ((A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))).Adj v w := by
    obtain ⟨q,hq⟩ := hActualSameAttachedGraphAdjacencyProducesPlanarLink hvw
    have hQ := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.edge_isArcBetween hq
    have hqNotW : q ∉ W := by
      intro hqW
      have hp : actualAttachedPlanarVertexPosition v ∈ Graph.edgesCover actualAttachedPlanarDrawing W :=
        Graph.mem_edgesCover hqW hQ.left_mem
      exact Schoenflies.inside_subset_compl hv (Or.inr hp)
    have endpointOfQ (x : Schoenflies.Plane)
        (hx : x = actualAttachedPlanarEdgePath q 0 ∨ x = actualAttachedPlanarEdgePath q 1) :
        x = actualAttachedPlanarVertexPosition v ∨ x = actualAttachedPlanarVertexPosition w := by
      change (_ = actualAttachedPlanarEdgePath q 0 ∧ _ = actualAttachedPlanarEdgePath q 1) ∨
        (_ = actualAttachedPlanarEdgePath q 1 ∧ _ = actualAttachedPlanarEdgePath q 0) at hq
      rcases hq with ⟨hv0,hw1⟩ | ⟨hv1,hw0⟩
      · rcases hx with hx0 | hx1
        · exact Or.inl (hx0.trans hv0.symm)
        · exact Or.inr (hx1.trans hw1.symm)
      · rcases hx with hx0 | hx1
        · exact Or.inr (hx0.trans hw0.symm)
        · exact Or.inl (hx1.trans hv1.symm)
    have hdisjoint : Disjoint (Graph.edgeArc actualAttachedPlanarDrawing q \
        {actualAttachedPlanarVertexPosition v,actualAttachedPlanarVertexPosition w})
        (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) := by
      rw [Set.disjoint_left]
      intro x hxQ hxJ
      have hnotEnds : ¬ (x = actualAttachedPlanarVertexPosition v ∨ x = actualAttachedPlanarVertexPosition w) := by
        simpa using hxQ.2
      rcases hxJ with hxA | hxP
      · exact hnotEnds (endpointOfQ x (hActualAttachedPlanarEdgeArcModelBoundaryOnlyEnds q x hxQ.1 (hA hxA)))
      · obtain ⟨r,hrW,hxr⟩ := Graph.mem_edgesCover_iff.mp hxP
        have hqr : q ≠ r := fun h => hqNotW (h.symm ▸ hrW)
        have hxVertex := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.edge_inter (Set.mem_univ q)
          (Set.mem_univ r) hqr hxQ.1 hxr
        exact hnotEnds (hxVertex.2.1.eq_or_eq_of_isLink hq)
    have hQcap := CurveComplex.LocalSurgery.actual_arc_closed_cap_containment_of_endpoint_inside hJ hQ hdisjoint hv
    exact ⟨hvw,q,hq,hQcap⟩
  have actualAttachedClosedCapGraphInteriorDegreeEqualsOriginal
      (A : Set Schoenflies.Plane) (W : List (actualAttachedEdgeLabels))
      (hA : A ⊆ Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))
      (v : actualAttachedContactVertex) (hv : actualAttachedPlanarVertexPosition v ∈
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W)) :
      (actualAttachedClosedCapZeroGraph ((A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))).degree v =
          actualAttachedContactGraph.degree v := by
    rw [←SimpleGraph.ncard_neighborSet,←SimpleGraph.ncard_neighborSet]
    congr 1
    ext w
    constructor
    · exact fun h => h.1
    · exact actualAttachedClosedCapGraphInteriorHasAllOriginalNeighbors A W hA hJ v w hv
  have hActualAttachedClosedCapGraphInitialDegreeOne
      (D : Set Schoenflies.Plane) (c : actualContactVertices) (hc : c.val.1=0)
      (w : actualAttachedContactVertex)
      (hvw : (actualAttachedClosedCapZeroGraph D).Adj (Sum.inl (Sum.inl c)) w) :
      (actualAttachedClosedCapZeroGraph D).degree (Sum.inl (Sum.inl c))=1 := by
    as_aux_lemma =>
      have hle := actualAttachedClosedCapGraphDegreeAtMostOriginal D (Sum.inl (Sum.inl c))
      have hpos := hvw.degree_pos_left
      have hone := hActualAttachedEveryInitialContactVertexDegreeOne c hc
      simp only [←SimpleGraph.ncard_neighborSet] at hle hpos hone ⊢
      omega
  have hActualAttachedClosedCapGraphInteriorDegreeEven
      (A : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (hA : A⊆Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A∪Graph.edgesCover actualAttachedPlanarDrawing W))
      (hBound : ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
          Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))⊆
          Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve)
      (v : actualAttachedContactVertex)
      (hv : actualAttachedPlanarVertexPosition v∈Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W)) :
      Even ((actualAttachedClosedCapZeroGraph ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))).degree v) := by
    as_aux_lemma =>
      rw [actualAttachedClosedCapGraphInteriorDegreeEqualsOriginal A W hA hJ v hv]
      by_contra hn
      have hOdd : Odd (actualAttachedContactGraph.degree v) := Nat.not_even_iff_odd.mp hn
      have hModel := hActualAttachedOddVertexOnModelBoundary v hOdd
      have hInside := CurveComplex.LocalSurgery.actualModelSquareClosedCapInterior hJ hBound hv
      exact Schoenflies.inside_subset_compl hInside hModel
  have actualAttachedClosedCapGraphOddVerticesOnBoundary
      (A : Set Schoenflies.Plane) (W : List (actualAttachedEdgeLabels))
      (hA : A ⊆ Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))
      (hBound : ((A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W)) ⊆
          Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve)
      (v : actualAttachedContactVertex)
      (hOdd : Odd ((actualAttachedClosedCapZeroGraph ((A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))).degree v)) :
      actualAttachedPlanarVertexPosition v ∈ A ∪ Graph.edgesCover actualAttachedPlanarDrawing W := by
    by_contra hnot
    by_cases hin : actualAttachedPlanarVertexPosition v ∈ Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W)
    · exact (Nat.not_even_iff_odd.mpr hOdd)
        (hActualAttachedClosedCapGraphInteriorDegreeEven A W hA hJ hBound v hin)
    · have hout : actualAttachedPlanarVertexPosition v ∉ (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) ∪
          Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) := by
        intro h
        exact h.elim hnot hin
      rw [actualAttachedClosedCapGraphOutsideDegreeZero _ v hout] at hOdd
      norm_num at hOdd
  have actualAttachedClosedCapGraphExtraBoundaryHasOriginalNeighbor
      (A : Set Schoenflies.Plane) (W : List (actualAttachedEdgeLabels))
      (a b : actualAttachedContactVertex) (B : Set Schoenflies.Plane)
      (hCut : Schoenflies.IsCutPair (Schoenflies.modelCurve)
        (actualAttachedPlanarVertexPosition a) (actualAttachedPlanarVertexPosition b) A B)
      (hP : Schoenflies.IsArcBetween (Graph.edgesCover actualAttachedPlanarDrawing W)
        (actualAttachedPlanarVertexPosition a) (actualAttachedPlanarVertexPosition b))
      (hPi : Graph.edgesCover actualAttachedPlanarDrawing W \ 
        {actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b} ⊆
        Schoenflies.inside (Schoenflies.modelCurve))
      (v w : actualAttachedContactVertex) (hv : actualAttachedPlanarVertexPosition v ∈ A)
      (hne : actualAttachedPlanarVertexPosition v ∉
        ({actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b} : Set Schoenflies.Plane))
      (hvw : actualAttachedContactGraph.Adj v w) :
      (actualAttachedClosedCapZeroGraph ((A ∪ Graph.edgesCover actualAttachedPlanarDrawing W) ∪
        Schoenflies.inside (A ∪ Graph.edgesCover actualAttachedPlanarDrawing W))).Adj v w := by
    obtain ⟨q,hq⟩ := hActualSameAttachedGraphAdjacencyProducesPlanarLink hvw
    have hQ := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.edge_isArcBetween hq
    have hqNotW : q ∉ W := by
      intro hqW
      have hp : actualAttachedPlanarVertexPosition v ∈ Graph.edgesCover actualAttachedPlanarDrawing W :=
        Graph.mem_edgesCover hqW hQ.left_mem
      exact Schoenflies.inside_subset_compl (hPi ⟨hp,hne⟩) (hCut.fst_subset hv)
    have endpointOfQ (x : Schoenflies.Plane)
        (hx : x = actualAttachedPlanarEdgePath q 0 ∨ x = actualAttachedPlanarEdgePath q 1) :
        x = actualAttachedPlanarVertexPosition v ∨ x = actualAttachedPlanarVertexPosition w := by
      change (_ = actualAttachedPlanarEdgePath q 0 ∧ _ = actualAttachedPlanarEdgePath q 1) ∨
        (_ = actualAttachedPlanarEdgePath q 1 ∧ _ = actualAttachedPlanarEdgePath q 0) at hq
      rcases hq with ⟨hv0,hw1⟩ | ⟨hv1,hw0⟩
      · rcases hx with hx0 | hx1
        · exact Or.inl (hx0.trans hv0.symm)
        · exact Or.inr (hx1.trans hw1.symm)
      · rcases hx with hx0 | hx1
        · exact Or.inr (hx0.trans hw0.symm)
        · exact Or.inl (hx1.trans hv1.symm)
    have hQi : Graph.edgeArc actualAttachedPlanarDrawing q \ 
        {actualAttachedPlanarVertexPosition v,actualAttachedPlanarVertexPosition w}⊆
        Schoenflies.inside Schoenflies.modelCurve := by
      rintro x ⟨hxQ,hnot⟩
      obtain ⟨t,he⟩ := hActualAttachedPlanarEdgePointParameter q x hxQ
      have hn : ¬(x=actualAttachedPlanarVertexPosition v ∨ x=actualAttachedPlanarVertexPosition w) := by
        simpa using hnot
      have ht0 : t≠0 := by
        intro ht
        subst t
        exact hn (endpointOfQ x (Or.inl he.symm))
      have ht1 : t≠1 := by
        intro ht
        subst t
        exact hn (endpointOfQ x (Or.inr he.symm))
      exact he ▸ hActualSameTailAttachedPlanarEdgeInterior q t
        ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩
    have hdisjoint : Disjoint (Graph.edgeArc actualAttachedPlanarDrawing q \ 
        {actualAttachedPlanarVertexPosition v,actualAttachedPlanarVertexPosition w})
        (Graph.edgesCover actualAttachedPlanarDrawing W) := by
      rw [Set.disjoint_left]
      intro x hxQ hxP
      have hnotEnds : ¬ (x = actualAttachedPlanarVertexPosition v ∨ x = actualAttachedPlanarVertexPosition w) := by
        simpa using hxQ.2
      obtain ⟨r,hrW,hxr⟩ := Graph.mem_edgesCover_iff.mp hxP
      have hqr : q ≠ r := fun h => hqNotW (h.symm ▸ hrW)
      have hxVertex := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.edge_inter (Set.mem_univ q)
        (Set.mem_univ r) hqr hxQ.1 hxr
      exact hnotEnds (hxVertex.2.1.eq_or_eq_of_isLink hq)
    have hQcap := CurveComplex.LocalSurgery.actual_crosscut_boundary_arc_stays_in_selected_cap
      Schoenflies.isJordanCurve_modelCurve hP hCut hPi hQ hv hne hQi hdisjoint
    exact ⟨hvw,q,hq,hQcap⟩
  have hActualAttachedClosedCapExtraPhysicalInitialEventOddPartner
      (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (a b : actualAttachedContactVertex)
      (hcut : Schoenflies.IsCutPair Schoenflies.modelCurve
        (actualAttachedPlanarVertexPosition a) (actualAttachedPlanarVertexPosition b) A B)
      (hP : Schoenflies.IsArcBetween (Graph.edgesCover actualAttachedPlanarDrawing W)
        (actualAttachedPlanarVertexPosition a) (actualAttachedPlanarVertexPosition b))
      (hPi : Graph.edgesCover actualAttachedPlanarDrawing W\
        {actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b}⊆Schoenflies.inside Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A∪Graph.edgesCover actualAttachedPlanarDrawing W))
      (hBound : ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
          Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))⊆
          Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve)
      (c : actualContactVertices) (hc : c.val.1=0)
      (hcA : actualAttachedPlanarVertexPosition (Sum.inl (Sum.inl c))∈A)
      (hne : actualAttachedPlanarVertexPosition (Sum.inl (Sum.inl c))∉
        ({actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b} : Set Schoenflies.Plane)) :
      ∃ y : actualAttachedContactVertex,y≠Sum.inl (Sum.inl c) ∧
        actualAttachedPlanarVertexPosition y∈A∪Graph.edgesCover actualAttachedPlanarDrawing W ∧
      ∃ P : (actualAttachedClosedCapZeroGraph ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))).Walk (Sum.inl (Sum.inl c)) y,P.IsPath := by
    as_aux_lemma =>
      let D := (A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W)
      have hdegree := hActualAttachedEveryInitialContactVertexDegreeOne c hc
      have hpos : 0<actualAttachedContactGraph.degree (Sum.inl (Sum.inl c)) := by omega
      have hnotIso := (SimpleGraph.degree_pos actualAttachedContactGraph (Sum.inl (Sum.inl c))).mp hpos
      obtain ⟨d,hd⟩ : ∃ d,actualAttachedContactGraph.Adj (Sum.inl (Sum.inl c)) d := by
        simpa only [SimpleGraph.IsIsolated,not_forall,not_not] using hnotIso
      have hcapAdj := actualAttachedClosedCapGraphExtraBoundaryHasOriginalNeighbor A W a b B
        hcut hP hPi (Sum.inl (Sum.inl c)) d hcA hne hd
      have hcapDegree := hActualAttachedClosedCapGraphInitialDegreeOne D c hc d hcapAdj
      have hcapOdd : Odd ((actualAttachedClosedCapZeroGraph D).degree (Sum.inl (Sum.inl c))) := by
        rw [hcapDegree]
        norm_num
      obtain ⟨y,hyne,hyOdd,P,hP⟩ := CurveComplex.LocalSurgery.actual_odd_vertex_has_distinct_path_partner
        (actualAttachedClosedCapZeroGraph D) (Sum.inl (Sum.inl c)) hcapOdd
      exact ⟨y,hyne,actualAttachedClosedCapGraphOddVerticesOnBoundary A W hcut.fst_subset hJ hBound y hyOdd,P,hP⟩
  have hActualOriginalCentralGraphVertexFirstCoordinateNotOne (v : zeroVertex) :
      (zeroVertexPosition v).1≠1 := by
    intro he
    have hp : zeroVertexPosition v=(1,(zeroVertexPosition v).2) := Prod.ext he rfl
    have hm := hActualContactGraphVertexImage v
    rw [hp] at hm
    exact hActualFiniteConeSweepTopAvoids (zeroVertexPosition v).2 hm
  have hActualOriginalCentralGraphLeftVertexIsPhysicalInitial (v : zeroVertex)
      (hv : (zeroVertexPosition v).1=0) :
      ∃ c : actualContactVertices,v=Sum.inl c ∧ c.val.1=0 := by
    cases v with
    | inl c => exact ⟨c,rfl,hv⟩
    | inr e =>
      have he := hActualGlobalContactArcOnOuterBoundaryIsEndpoint e.1 (privateParameter e.2) (Or.inl hv)
      have ht := privateParameterInterior e.2
      exact (he.elim (fun h => (ne_of_gt ht.1) h) (fun h => (ne_of_lt ht.2) h)).elim
  let actualAttachedLeftBoundaryVertices : Finset actualAttachedContactVertex :=
    Finset.univ.filter (fun v => (actualAttachedSquareVertexPosition v).1=0)
  have hActualAttachedVertexOnModelBoundaryIsOnActualLeftSide
      (v : actualAttachedContactVertex) (hv : actualAttachedPlanarVertexPosition v∈Schoenflies.modelCurve) :
      v∈actualAttachedLeftBoundaryVertices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases v with
    | inr m => rfl
    | inl v =>
      have hx : (zeroVertexPosition v).1=0 := by
        by_contra hn
        have hi := hActualCentralCollarSquareInterior (zeroVertexPosition v)
          ⟨lt_of_le_of_ne (zeroVertexPosition v).1.property.1 (fun h => hn h.symm),
            lt_of_le_of_ne (zeroVertexPosition v).1.property.2
              (hActualOriginalCentralGraphVertexFirstCoordinateNotOne v)⟩
        have hinside := CurveComplex.LocalSurgery.actualUnitSquareModelPlaneInterior
          (actualCentralCollarSquare (zeroVertexPosition v)) hi
        exact Schoenflies.inside_subset_compl hinside hv
      change (actualCentralCollarSquare (zeroVertexPosition v)).1=0
      rw [show zeroVertexPosition v=(0,(zeroVertexPosition v).2) from Prod.ext hx rfl,
        hActualCentralCollarSquareInitial]
  have hActualAttachedActualLeftSideVertexIsInitialOrChosenMark
      (v : actualAttachedContactVertex) (hv : v∈actualAttachedLeftBoundaryVertices) :
      (∃ c : actualContactVertices,v=Sum.inl (Sum.inl c) ∧ c.val.1=0) ∨
        (∃ m : Fin 2,v=Sum.inr m) := by
    cases v with
    | inr m => exact Or.inr ⟨m,rfl⟩
    | inl v =>
      have hz := (Finset.mem_filter.mp hv).2
      change (actualCentralCollarSquare (zeroVertexPosition v)).1=0 at hz
      have hf := hActualCentralCollarSquareFormula (zeroVertexPosition v)
      have hx : (zeroVertexPosition v).1=0 := by
        apply Subtype.ext
        have hh := congrArg Prod.fst hf
        change (actualCentralCollarSquare (zeroVertexPosition v)).1.val=(zeroVertexPosition v).1.val at hh
        rw [hz] at hh
        change (0 : ℝ)=(zeroVertexPosition v).1.val at hh
        exact hh.symm
      obtain ⟨c,rfl,hc⟩ := hActualOriginalCentralGraphLeftVertexIsPhysicalInitial v hx
      exact Or.inl ⟨c,rfl,hc⟩
  have hActualAttachedCapPartnerProducesActualLeftReturningCarrier
      (A : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (a b r y : actualAttachedContactVertex) (hA : A⊆Schoenflies.modelCurve)
      (hb : b∈actualAttachedLeftBoundaryVertices) (hbA : actualAttachedPlanarVertexPosition b∈A)
      (hrb : r≠b)
      (hW : actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition a) W
        (actualAttachedPlanarVertexPosition b))
      (hyr : y≠r) (hy : actualAttachedPlanarVertexPosition y∈A∪Graph.edgesCover actualAttachedPlanarDrawing W)
      (p : (actualAttachedClosedCapZeroGraph ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))).Walk r y) :
      ∃ z∈actualAttachedLeftBoundaryVertices,z≠r ∧ actualAttachedPlanarVertexPosition z∈A ∧
        ∃ U,actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition r) U
          (actualAttachedPlanarVertexPosition z) ∧
          ∀ q∈U,Graph.edgeArc actualAttachedPlanarDrawing q⊆
            ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
              Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W)) := by
    let D := (A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
      Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W)
    obtain ⟨U,hU,hUD⟩ := CurveComplex.LocalSurgery.actual_simple_graph_walk_to_labeled_graph_with_edge_constraint
      (actualAttachedClosedCapZeroGraph D) actualAttachedPlanarGraph actualAttachedPlanarVertexPosition
      (fun q => Graph.edgeArc actualAttachedPlanarDrawing q⊆D)
      (fun v => ⟨v,rfl⟩) (fun {v w} hvw => hvw.2) p
    rcases hy with hyA | hyP
    · have hyB := hActualAttachedVertexOnModelBoundaryIsOnActualLeftSide y (hA hyA)
      obtain ⟨Q,hQ,hQU⟩ := hU.contains_path
      exact ⟨y,hyB,hyr,hyA,Q,hQ,fun q hq => hUD q (hQU hq)⟩
    · obtain ⟨q,hq,hye⟩ := Graph.mem_edgesCover_iff.mp hyP
      have hinc : actualAttachedPlanarGraph.Inc q (actualAttachedPlanarVertexPosition y) := by
        rcases hActualAttachedPlanarVertexOnEdgeOnlyEnds q y hye with h0 | h1
        · exact ⟨actualAttachedPlanarEdgePath q 1,Or.inl ⟨h0,rfl⟩⟩
        · exact ⟨actualAttachedPlanarEdgePath q 0,Or.inr ⟨h1,rfl⟩⟩
      have hyvisited : actualAttachedPlanarVertexPosition y∈
          actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition a) W :=
        Graph.mem_walkVertices_of_mem_covered ⟨q,hq,hinc⟩
      have hWD : ∀ q∈W,Graph.edgeArc actualAttachedPlanarDrawing q⊆D := by
        intro q hq x hx
        exact Or.inl (Or.inr (Graph.mem_edgesCover hq hx))
      obtain ⟨Q,hQ,hQD⟩ := CurveComplex.LocalSurgery.actual_drawn_cap_path_join_at_visited_vertex
        actualAttachedPlanarGraph (fun q => Graph.edgeArc actualAttachedPlanarDrawing q⊆D)
        hU hW hyvisited hUD hWD
      exact ⟨b,hb,hrb.symm,hbA,Q,hQ,hQD⟩
  have hActualSameRestrictedCapSimplePathFirstBoundaryPrefix
      {V : Type} (G : SimpleGraph V) {v w : V} (P : G.Walk v w)
      (hP : P.IsPath) (hne : v≠w) (B : V→Prop) (hw : B w) :
      ∃ z : V,B z ∧ z≠v ∧ ∃ Q : G.Walk v z,Q.IsPath ∧
        (∀ r,r∈Q.support → r≠v → r≠z → ¬B r) := by
    as_aux_lemma =>
      have hlen : 0<P.length := Nat.pos_of_ne_zero (fun h => hne (SimpleGraph.Walk.eq_of_length_eq_zero h))
      have hex : ∃ n : ℕ,0<n ∧ n≤P.length ∧ B (P.getVert n) :=
        ⟨P.length,hlen,le_refl _,by simpa using hw⟩
      let n := Nat.find hex
      have hn := Nat.find_spec hex
      change 0<n ∧ n≤P.length ∧ B (P.getVert n) at hn
      have hzv : P.getVert n≠v := by
        intro h
        have he := hP.getVert_injOn hn.2.1 (show 0≤P.length by omega) (h.trans P.getVert_zero.symm)
        omega
      refine ⟨P.getVert n,hn.2.2,hzv,P.take n,hP.take n,?_⟩
      intro r hr hrv hrz hBr
      obtain ⟨m,hmr,hm⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hr
      have hmn : m≤n := by
        simpa only [SimpleGraph.Walk.take_length,Nat.min_eq_left hn.2.1] using hm
      have hmr' : P.getVert m=r := by
        simpa only [SimpleGraph.Walk.take_getVert,Nat.min_eq_right hmn] using hmr
      have hmpos : 0 < m := by
        by_contra h
        have hm0 : m=0 := by omega
        rw [hm0,SimpleGraph.Walk.getVert_zero] at hmr'
        exact hrv hmr'.symm
      have hmlt : m < n := lt_of_le_of_ne hmn (fun he => hrz (hmr'.symm.trans (congrArg P.getVert he)))
      have hnm := Nat.find_min' hex ⟨hmpos,hmn.trans hn.2.1,hmr'.symm ▸ hBr⟩
      omega
  have hActualRestrictedCapSimplePathHasSameDrawnVerticesAndConstrainedEdges
      (D : Set Schoenflies.Plane) {v w : actualAttachedContactVertex}
      (P : (actualAttachedClosedCapZeroGraph D).Walk v w) (hP : P.IsPath) :
      ∃ W,actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition v) W
        (actualAttachedPlanarVertexPosition w) ∧
        actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition v) W=
          actualAttachedPlanarVertexPosition '' {u | u∈P.support} ∧
        ∀ e∈W,Graph.edgeArc actualAttachedPlanarDrawing e⊆D := by
    revert hP
    induction P with
    | nil =>
      intro hP
      refine ⟨[],Graph.IsPath.nil ⟨_,rfl⟩,?_,by simp⟩
      simp [Graph.walkVertices_nil]
    | @cons v u w hadj P ih =>
      intro hP
      obtain ⟨hpp,hfresh⟩ := (SimpleGraph.Walk.cons_isPath_iff hadj P).mp hP
      obtain ⟨e,he,hR⟩ := hadj.2
      obtain ⟨W,hW,hverts,hconstraint⟩ := ih hpp
      have hnew : actualAttachedPlanarVertexPosition v∉
          actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition u) W := by
        intro hv
        rw [hverts] at hv
        obtain ⟨r,hr,heq⟩ := hv
        exact hfresh (hActualAttachedPlanarVertexPositionInjective heq ▸ hr)
      refine ⟨e::W,Graph.IsPath.cons he hW hnew,?_,?_⟩
      · ext x
        constructor
        · intro hx
          rcases Graph.mem_walkVertices_cons he hx with rfl | htail
          · exact ⟨v,by simp,rfl⟩
          · rw [hverts] at htail
            obtain ⟨r,hr,heq⟩ := htail
            exact ⟨r,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];exact Or.inr hr,heq⟩
        · rintro ⟨r,hr,rfl⟩
          simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact Graph.mem_walkVertices_self
          · apply Graph.mem_walkVertices_cons_of_mem he
            rw [hverts]
            exact ⟨r,hr,rfl⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hR
        · exact hconstraint q hq
  have hActualSameRestrictedCapDrawnCarrierBoundaryOnlyAtPathEnds
      (D : Set Schoenflies.Plane) {v w : actualAttachedContactVertex}
      (P : (actualAttachedClosedCapZeroGraph D).Walk v w)
      (hboundary : ∀ r,r∈P.support → r≠v → r≠w → r∉actualAttachedLeftBoundaryVertices)
      (W : List actualAttachedEdgeLabels)
      (hvertices : actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition v) W=
        actualAttachedPlanarVertexPosition '' {r | r∈P.support})
      (x : Schoenflies.Plane) (hx : x∈Graph.edgesCover actualAttachedPlanarDrawing W)
      (hmodel : x∈Schoenflies.modelCurve) :
      x=actualAttachedPlanarVertexPosition v ∨ x=actualAttachedPlanarVertexPosition w := by
    obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
    rcases hActualAttachedPlanarEdgeArcModelBoundaryOnlyEnds e x hxe hmodel with h0 | h1
    all_goals
      have hinc : actualAttachedPlanarGraph.Inc e x := by
        first
        | exact ⟨actualAttachedPlanarEdgePath e 1,Or.inl ⟨h0,rfl⟩⟩
        | exact ⟨actualAttachedPlanarEdgePath e 0,Or.inr ⟨h1,rfl⟩⟩
      have hvisit : x∈actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition v) W :=
        Graph.mem_walkVertices_of_mem_covered ⟨e,he,hinc⟩
      rw [hvertices] at hvisit
      obtain ⟨r,hr,hrx⟩ := hvisit
      have hrB := hActualAttachedVertexOnModelBoundaryIsOnActualLeftSide r (hrx.symm ▸ hmodel)
      by_cases hrv : r=v
      · exact Or.inl (hrx.symm.trans (congrArg actualAttachedPlanarVertexPosition hrv))
      by_cases hrw : r=w
      · exact Or.inr (hrx.symm.trans (congrArg actualAttachedPlanarVertexPosition hrw))
      exact (hboundary r hr hrv hrw hrB).elim
  have hActualSameAttachedModelArcLiftsToEmbeddedUnitSquarePath
      (A : Set Schoenflies.Plane) (x y : Interval × Interval)
      (hA : Schoenflies.IsArcBetween A (CurveComplex.LocalSurgery.actualUnitSquareModelPlane x) (CurveComplex.LocalSurgery.actualUnitSquareModelPlane y))
      (hRange : A⊆Set.range CurveComplex.LocalSurgery.actualUnitSquareModelPlane) :
      ∃ q : Path x y,IsEmbedding q ∧ CurveComplex.LocalSurgery.actualUnitSquareModelPlane '' Set.range q=A := by
    as_aux_lemma =>
      obtain ⟨γ,hγc,hγi,hγA,hγ₀,hγ₁⟩ := hA
      let R := Set.range CurveComplex.LocalSurgery.actualUnitSquareModelPlane
      let rx : R := ⟨CurveComplex.LocalSurgery.actualUnitSquareModelPlane x,⟨x,rfl⟩⟩
      let ry : R := ⟨CurveComplex.LocalSurgery.actualUnitSquareModelPlane y,⟨y,rfl⟩⟩
      have hγR (t : Interval) : γ t.val∈R := hRange (hγA ▸ ⟨t.val,t.property,rfl⟩)
      let r : Path rx ry := {
        toFun := fun t => ⟨γ t.val,hγR t⟩
        continuous_toFun := (continuousOn_iff_continuous_restrict.mp hγc).subtype_mk _
        source' := by apply Subtype.ext;exact hγ₀
        target' := by apply Subtype.ext;exact hγ₁ }
      let E := CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.toHomeomorph
      have hback (z : R) : CurveComplex.LocalSurgery.actualUnitSquareModelPlane (E.symm z)=z.val :=
        congrArg Subtype.val (E.apply_symm_apply z)
      have hrx : E.symm rx=x := CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective (hback rx)
      have hry : E.symm ry=y := CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective (hback ry)
      let q : Path x y := (r.map E.symm.continuous).cast hrx.symm hry.symm
      have hq : IsEmbedding q := by
        apply (q.continuous.isClosedEmbedding ?_).isEmbedding
        intro t u he
        have hr : r t=r u := E.symm.injective he
        exact Subtype.ext (hγi t.property u.property (congrArg Subtype.val hr))
      have hpoint (t : Interval) : CurveComplex.LocalSurgery.actualUnitSquareModelPlane (q t)=γ t.val := hback (r t)
      refine ⟨q,hq,?_⟩
      ext z
      constructor
      · rintro ⟨v,⟨t,rfl⟩,rfl⟩
        rw [hpoint]
        exact hγA ▸ ⟨t.val,t.property,rfl⟩
      · intro hz
        obtain ⟨t,ht,he⟩ := (show z∈γ '' Set.Icc (0 : ℝ) 1 from hγA.symm ▸ hz)
        exact ⟨q ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,(hpoint ⟨t,ht⟩).trans he⟩
  have hActualRestrictedCapSimplePathFirstLeftBoundaryProducesProperCrosscut
      (D : Set Schoenflies.Plane) (v w : actualAttachedContactVertex)
      (hv : v∈actualAttachedLeftBoundaryVertices) (hw : w∈actualAttachedLeftBoundaryVertices)
      (hne : v≠w) (P : (actualAttachedClosedCapZeroGraph D).Walk v w) (hP : P.IsPath) :
      ∃ z∈actualAttachedLeftBoundaryVertices,z≠v ∧
        ∃ Q : (actualAttachedClosedCapZeroGraph D).Walk v z,Q.IsPath ∧
          (∀ r,r∈Q.support → r≠v → r≠z → r∉actualAttachedLeftBoundaryVertices) ∧
        ∃ W,W≠[] ∧ actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition v) W
          (actualAttachedPlanarVertexPosition z) ∧
          (∀ e∈W,Graph.edgeArc actualAttachedPlanarDrawing e⊆D) ∧
        ∃ J : Path (actualAttachedSquareVertexPosition v) (actualAttachedSquareVertexPosition z),
          IsEmbedding J ∧
          CurveComplex.LocalSurgery.actualUnitSquareModelPlane '' range J=
            Graph.edgesCover actualAttachedPlanarDrawing W ∧
          (∀ t∈Set.Ioo (0 : Interval) 1,(J t).1∈Set.Ioo (0 : Interval) 1 ∧
            (J t).2∈Set.Ioo (0 : Interval) 1) := by
    obtain ⟨z,hz,hzv,Q,hQ,honly⟩ := hActualSameRestrictedCapSimplePathFirstBoundaryPrefix
      (actualAttachedClosedCapZeroGraph D) P hP hne
      (fun r => r∈actualAttachedLeftBoundaryVertices) hw
    obtain ⟨W,hW,hvertices,hWD⟩ := hActualRestrictedCapSimplePathHasSameDrawnVerticesAndConstrainedEdges D Q hQ
    have hWne : W≠[] := by
      intro he
      rw [he] at hW
      exact hzv (hActualAttachedSquareVertexPositionInjective
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective hW.isWalk.eq_of_nil)).symm
    have hArc := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.path_isArcBetween hW hWne
    have hRange : Graph.edgesCover actualAttachedPlanarDrawing W⊆
        range CurveComplex.LocalSurgery.actualUnitSquareModelPlane := by
      intro x hx
      obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
      obtain ⟨t,ht⟩ := hActualAttachedPlanarEdgePointParameter e x hxe
      exact ⟨actualAttachedSquareEdgePath e t,ht⟩
    obtain ⟨J,hJ,himage⟩ := hActualSameAttachedModelArcLiftsToEmbeddedUnitSquarePath
      (Graph.edgesCover actualAttachedPlanarDrawing W)
      (actualAttachedSquareVertexPosition v) (actualAttachedSquareVertexPosition z) hArc hRange
    have hInside (t : Interval) (ht : t∈Set.Ioo (0 : Interval) 1) :
        (J t).1∈Set.Ioo (0 : Interval) 1 ∧ (J t).2∈Set.Ioo (0 : Interval) 1 := by
      have hnot : CurveComplex.LocalSurgery.actualUnitSquareModelPlane (J t)∉Schoenflies.modelCurve := by
        intro hmodel
        have hx : CurveComplex.LocalSurgery.actualUnitSquareModelPlane (J t)∈
            Graph.edgesCover actualAttachedPlanarDrawing W := himage ▸ ⟨J t,⟨t,rfl⟩,rfl⟩
        rcases hActualSameRestrictedCapDrawnCarrierBoundaryOnlyAtPathEnds D Q honly W hvertices _ hx hmodel
          with hstart | hend
        · have hpoint : J t=actualAttachedSquareVertexPosition v :=
            CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective hstart
          have htime : t=0 := hJ.injective (hpoint.trans J.source.symm)
          exact (ne_of_gt ht.1) htime
        · have hpoint : J t=actualAttachedSquareVertexPosition z :=
            CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.injective hend
          have htime : t=1 := hJ.injective (hpoint.trans J.target.symm)
          exact (ne_of_lt ht.2) htime
      have hx0 : (J t).1≠0 := fun h => hnot
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inl h))
      have hx1 : (J t).1≠1 := fun h => hnot
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inr (Or.inl h)))
      have hy0 : (J t).2≠0 := fun h => hnot
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inr (Or.inr (Or.inl h))))
      have hy1 : (J t).2≠1 := fun h => hnot
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inr (Or.inr (Or.inr h))))
      exact ⟨⟨lt_of_le_of_ne (J t).1.property.1 hx0.symm,lt_of_le_of_ne (J t).1.property.2 hx1⟩,
        ⟨lt_of_le_of_ne (J t).2.property.1 hy0.symm,lt_of_le_of_ne (J t).2.property.2 hy1⟩⟩
    exact ⟨z,hz,hzv,Q,hQ,honly,W,hWne,hW,hWD,J,hJ,himage,hInside⟩
  have hActualSameAttachedPlanarLinkRecoversLiteralContactAdjacency
      {v w : actualAttachedContactVertex} {e : actualAttachedEdgeLabels}
      (he : actualAttachedPlanarGraph.IsLink e (actualAttachedPlanarVertexPosition v)
        (actualAttachedPlanarVertexPosition w)) : actualAttachedContactGraph.Adj v w := by
    have hAdj : actualAttachedContactGraph.Adj (actualAttachedEdgeStart e) (actualAttachedEdgeEnd e) := by
      cases e with
      | inl e =>
        change actualZeroGraph.Adj (actualSegmentStartVertex e) (actualSegmentEndVertex e)
        rcases e with ⟨e,j⟩
        fin_cases j
        · simpa [actualSegmentStartVertex,actualSegmentEndVertex] using zeroGraphLeftAdj e
        · simpa [actualSegmentStartVertex,actualSegmentEndVertex] using zeroGraphMiddleAdj e
        · simpa [actualSegmentStartVertex,actualSegmentEndVertex] using zeroGraphRightAdj e
      | inr e => exact e.property
    change (_=actualAttachedPlanarEdgePath e 0 ∧ _=actualAttachedPlanarEdgePath e 1) ∨
      (_=actualAttachedPlanarEdgePath e 1 ∧ _=actualAttachedPlanarEdgePath e 0) at he
    rw [hActualAttachedPlanarEdgeSource,hActualAttachedPlanarEdgeTarget] at he
    rcases he with ⟨hv,hw⟩ | ⟨hv,hw⟩
    · have hv' := hActualAttachedPlanarVertexPositionInjective hv
      have hw' := hActualAttachedPlanarVertexPositionInjective hw
      exact hv'.symm ▸ hw'.symm ▸ hAdj
    · have hv' := hActualAttachedPlanarVertexPositionInjective hv
      have hw' := hActualAttachedPlanarVertexPositionInjective hw
      exact hv'.symm ▸ hw'.symm ▸ hAdj.symm
  have hActualSameCapConstrainedPlanarPathRecoversRestrictedSimplePath
      (D : Set Schoenflies.Plane) {x y : Schoenflies.Plane} {W : List actualAttachedEdgeLabels}
      (hW : actualAttachedPlanarGraph.IsPath x W y)
      (hWD : ∀ e∈W,Graph.edgeArc actualAttachedPlanarDrawing e⊆D) :
      ∀ v w,actualAttachedPlanarVertexPosition v=x → actualAttachedPlanarVertexPosition w=y →
        ∃ P : (actualAttachedClosedCapZeroGraph D).Walk v w,P.IsPath ∧
          actualAttachedPlanarGraph.walkVertices x W=
            actualAttachedPlanarVertexPosition '' {r | r∈P.support} := by
    revert hWD
    induction hW with
    | @nil x hx =>
      intro hWD v w hv hw
      have he : v=w := hActualAttachedPlanarVertexPositionInjective (hv.trans hw.symm)
      subst w
      refine ⟨SimpleGraph.Walk.nil,by simp,?_⟩
      subst x
      simp [Graph.walkVertices_nil]
    | @cons x z y e W he hW hnew ih =>
      intro hWD v w hv hw
      obtain ⟨k,hk⟩ := he.right_mem
      obtain ⟨P,hP,hverts⟩ := ih (fun q hq => hWD q (List.mem_cons_of_mem e hq)) k w hk hw
      have helink : actualAttachedPlanarGraph.IsLink e (actualAttachedPlanarVertexPosition v)
          (actualAttachedPlanarVertexPosition k) := hv.symm ▸ hk.symm ▸ he
      have ha : (actualAttachedClosedCapZeroGraph D).Adj v k :=
        ⟨hActualSameAttachedPlanarLinkRecoversLiteralContactAdjacency helink,e,helink,hWD e (by simp)⟩
      have hfresh : v∉P.support := by
        intro hm
        apply hnew
        rw [hverts]
        exact ⟨v,hm,hv⟩
      refine ⟨SimpleGraph.Walk.cons ha P,
        (SimpleGraph.Walk.cons_isPath_iff ha P).mpr ⟨hP,hfresh⟩,?_⟩
      ext q
      constructor
      · intro hq
        rcases Graph.mem_walkVertices_cons he hq with hq | hq
        · exact ⟨v,by simp,hv.trans hq.symm⟩
        · rw [hverts] at hq
          obtain ⟨r,hr,heq⟩ := hq
          exact ⟨r,by simp only [SimpleGraph.Walk.support_cons,List.mem_cons];exact Or.inr hr,heq⟩
      · rintro ⟨r,hr,rfl⟩
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hr
        rcases hr with rfl | hr
        · rw [hv]
          exact Graph.mem_walkVertices_self
        · apply Graph.mem_walkVertices_cons_of_mem he
          rw [hverts]
          exact ⟨r,hr,rfl⟩
  have hActualSelectedClosedCapMeetsModelBoundaryOnlyInCutArc
      (A : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (a b : actualAttachedContactVertex) (B : Set Schoenflies.Plane)
      (hcut : Schoenflies.IsCutPair Schoenflies.modelCurve (actualAttachedPlanarVertexPosition a)
        (actualAttachedPlanarVertexPosition b) A B)
      (hPi : Graph.edgesCover actualAttachedPlanarDrawing W\
        {actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b}⊆
          Schoenflies.inside Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A∪Graph.edgesCover actualAttachedPlanarDrawing W))
      (hBound : ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))⊆
          Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve)
      (x : Schoenflies.Plane)
      (hx : x∈(A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))
      (hxmodel : x∈Schoenflies.modelCurve) : x∈A := by
    rcases hx with (hxA | hxP) | hxI
    · exact hxA
    · by_cases hxa : x=actualAttachedPlanarVertexPosition a
      · exact hxa.symm ▸ hcut.fst.left_mem
      by_cases hxb : x=actualAttachedPlanarVertexPosition b
      · exact hxb.symm ▸ hcut.fst.right_mem
      have hn : x∉({actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b} : Set Schoenflies.Plane) := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
        exact ⟨hxa,hxb⟩
      exact (Schoenflies.inside_subset_compl (hPi ⟨hxP,hn⟩) hxmodel).elim
    · exact (Schoenflies.inside_subset_compl
        (CurveComplex.LocalSurgery.actualModelSquareClosedCapInterior hJ hBound hxI) hxmodel).elim
  let actualOriginalPhysicalInitialEventVertices : Finset actualAttachedContactVertex :=
    Finset.univ.filter (fun v => ∃ c : actualContactVertices,v=Sum.inl (Sum.inl c) ∧ c.val.1=0)
  have hActualEveryOriginalPhysicalInitialEventIsActualCrossing
      (v : actualAttachedContactVertex) (hv : v∈actualOriginalPhysicalInitialEventVertices) :
      ∃ c : actualContactVertices,v=Sum.inl (Sum.inl c) ∧ c.val.1=0 ∧
        b.val.map (actualAttachedSquareVertexPosition v).2∈ArcSurgery.crossings M a b := by
    obtain ⟨c,rfl,hc⟩ := (Finset.mem_filter.mp hv).2
    have hcp : c.val=(0,c.val.2) := Prod.ext hc rfl
    have hp : b.val.map (actualCentralParameter c.val.2)=actualFiniteConeSweep c.val := by
      rw [hcp,hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
    have hcross : b.val.map (actualCentralParameter c.val.2)∈ArcSurgery.crossings M a b := by
      refine ⟨⟨hp.symm ▸ hActualContactVerticesImage c,?_⟩,⟨⟨actualCentralParameter c.val.2,rfl⟩,?_⟩⟩
      all_goals exact hp.symm ▸ hActualFiniteConeSweepMarks c.val
    refine ⟨c,rfl,hc,?_⟩
    change b.val.map (actualCentralCollarSquare c.val).2∈ArcSurgery.crossings M a b
    rw [hcp,hActualCentralCollarSquareInitial]
    exact hcross
  have hActualExtraPhysicalInitialEventProducesStrictlySmallerNestedProperCap
      (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (a b r : actualAttachedContactVertex)
      (hcut : Schoenflies.IsCutPair Schoenflies.modelCurve
        (actualAttachedPlanarVertexPosition a) (actualAttachedPlanarVertexPosition b) A B)
      (hW : actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition a) W
        (actualAttachedPlanarVertexPosition b)) (hWne : W≠[])
      (hPi : Graph.edgesCover actualAttachedPlanarDrawing W\
        {actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b}⊆Schoenflies.inside Schoenflies.modelCurve)
      (hJ : Schoenflies.IsJordanCurve (A∪Graph.edgesCover actualAttachedPlanarDrawing W))
      (hBound : ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))⊆
          Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve)
      (hb : b∈actualAttachedLeftBoundaryVertices)
      (hrE : r∈actualOriginalPhysicalInitialEventVertices) (hrA : actualAttachedPlanarVertexPosition r∈A)
      (hra : r≠a) (hrb : r≠b) :
      ∃ z∈actualAttachedLeftBoundaryVertices,z≠r ∧ ∃ R T : Set Schoenflies.Plane,
        Schoenflies.IsCutPair Schoenflies.modelCurve (actualAttachedPlanarVertexPosition r)
          (actualAttachedPlanarVertexPosition z) R T ∧ R⊆A ∧
        (actualOriginalPhysicalInitialEventVertices.filter (fun x =>
          actualAttachedPlanarVertexPosition x∈R ∧ x≠r ∧ x≠z)).card<
        (actualOriginalPhysicalInitialEventVertices.filter (fun x =>
          actualAttachedPlanarVertexPosition x∈A ∧ x≠a ∧ x≠b)).card ∧
      ∃ U,U≠[] ∧ actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition r) U
        (actualAttachedPlanarVertexPosition z) ∧
        Schoenflies.IsJordanCurve (R∪Graph.edgesCover actualAttachedPlanarDrawing U) ∧
        ((R∪Graph.edgesCover actualAttachedPlanarDrawing U)∪
          Schoenflies.inside (R∪Graph.edgesCover actualAttachedPlanarDrawing U))⊆
            ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
              Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W)) ∧
      ∃ J : Path (actualAttachedSquareVertexPosition r) (actualAttachedSquareVertexPosition z),
        IsEmbedding J ∧ CurveComplex.LocalSurgery.actualUnitSquareModelPlane '' range J=
          Graph.edgesCover actualAttachedPlanarDrawing U ∧
        (∀ t∈Set.Ioo (0 : Interval) 1,(J t).1∈Set.Ioo (0 : Interval) 1 ∧
          (J t).2∈Set.Ioo (0 : Interval) 1) := by
    obtain ⟨c,hrc,hc,hPhysicalCrossing⟩ := hActualEveryOriginalPhysicalInitialEventIsActualCrossing r hrE
    have hOldArc := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.path_isArcBetween hW hWne
    have hrne : actualAttachedPlanarVertexPosition r∉
        ({actualAttachedPlanarVertexPosition a,actualAttachedPlanarVertexPosition b} : Set Schoenflies.Plane) := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
      exact ⟨fun h => hra (hActualAttachedPlanarVertexPositionInjective h),
        fun h => hrb (hActualAttachedPlanarVertexPositionInjective h)⟩
    obtain ⟨y,hyne,hy,P,hP⟩ := hActualAttachedClosedCapExtraPhysicalInitialEventOddPartner
      A B W a b hcut hOldArc hPi hJ hBound c hc (hrc ▸ hrA) (hrc ▸ hrne)
    have P' : (actualAttachedClosedCapZeroGraph ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
        Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))).Walk r y := P.copy hrc.symm rfl
    have hyr : y≠r := by simpa only [hrc] using hyne
    obtain ⟨z,hz,hzr,hzA,U,hU,hUD⟩ := hActualAttachedCapPartnerProducesActualLeftReturningCarrier
      A W a b r y hcut.fst_subset hb hcut.fst.right_mem hrb hW hyr hy P'
    let D := (A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
      Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W)
    obtain ⟨Q,hQ,hvertices⟩ := hActualSameCapConstrainedPlanarPathRecoversRestrictedSimplePath
      D hU hUD r z rfl rfl
    have hrB := hActualAttachedVertexOnModelBoundaryIsOnActualLeftSide r (hcut.fst_subset hrA)
    obtain ⟨z',hz',hz'r,Q',hQ',honly,U',hU'ne,hU',hU'D,J',hJ',hJ'image,hJ'inside⟩ :=
      hActualRestrictedCapSimplePathFirstLeftBoundaryProducesProperCrosscut D r z hrB hz hzr.symm Q hQ
    have hNewArc := hActualSameChosenTailAttachedPlanarDrawingIsDrawing.path_isArcBetween hU' hU'ne
    have hNewCarrierD : Graph.edgesCover actualAttachedPlanarDrawing U'⊆D := by
      intro x hx
      obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
      exact hU'D e he hxe
    have hz'model : actualAttachedPlanarVertexPosition z'∈Schoenflies.modelCurve :=
      CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inl (Finset.mem_filter.mp hz').2)
    have hz'A := hActualSelectedClosedCapMeetsModelBoundaryOnlyInCutArc A W a b B
      hcut hPi hJ hBound _ (hNewCarrierD hNewArc.right_mem) hz'model
    obtain ⟨R,T,hRT,hRA,hDrop⟩ := CurveComplex.LocalSurgery.actual_boundary_cut_pair_with_strict_event_decrease
      actualOriginalPhysicalInitialEventVertices actualAttachedPlanarVertexPosition
      hActualAttachedPlanarVertexPositionInjective a b r z' hcut hrE hrA hra hrb hz'A hz'r
    have hNewPi : Graph.edgesCover actualAttachedPlanarDrawing U'\
        {actualAttachedPlanarVertexPosition r,actualAttachedPlanarVertexPosition z'}⊆
          Schoenflies.inside Schoenflies.modelCurve := by
      rintro x ⟨hx,hn⟩
      rw [←hJ'image] at hx
      obtain ⟨s,⟨t,rfl⟩,rfl⟩ := hx
      have ht0 : t≠0 := by
        intro he
        subst t
        exact hn (Or.inl (by change _=CurveComplex.LocalSurgery.actualUnitSquareModelPlane _;rw [J'.source]))
      have ht1 : t≠1 := by
        intro he
        subst t
        exact hn (Or.inr (Set.mem_singleton_iff.mpr
          (by change _=CurveComplex.LocalSurgery.actualUnitSquareModelPlane _;rw [J'.target])))
      exact CurveComplex.LocalSurgery.actualUnitSquareModelPlaneInterior (J' t)
        (hJ'inside t ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩)
    have hNested := CurveComplex.LocalSurgery.actual_boundary_subarc_returning_cap_nested_general_endpoints
      Schoenflies.isJordanCurve_modelCurve hcut.fst hOldArc hcut.fst_subset hPi hRT.fst hRA
      hNewArc hNewPi hNewCarrierD
    exact ⟨z',hz',hz'r,R,T,hRT,hRA,hDrop,U',hU'ne,hU',hNested.1,hNested.2,
      J',hJ',hJ'image,hJ'inside⟩
  have hActualAnyUnitSquarePointIsInClosedModelSquare (z : Interval × Interval) :
      CurveComplex.LocalSurgery.actualUnitSquareModelPlane z∈
        Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve := by
    by_cases hx0 : z.1=0
    · exact Or.inl (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary z (Or.inl hx0))
    by_cases hx1 : z.1=1
    · exact Or.inl (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary z (Or.inr (Or.inl hx1)))
    by_cases hy0 : z.2=0
    · exact Or.inl (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary z (Or.inr (Or.inr (Or.inl hy0))))
    by_cases hy1 : z.2=1
    · exact Or.inl (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary z (Or.inr (Or.inr (Or.inr hy1))))
    exact Or.inr (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneInterior z
      ⟨⟨lt_of_le_of_ne z.1.property.1 (fun h => hx0 h.symm),lt_of_le_of_ne z.1.property.2 hx1⟩,
        ⟨lt_of_le_of_ne z.2.property.1 (fun h => hy0 h.symm),lt_of_le_of_ne z.2.property.2 hy1⟩⟩)
  have hActualAttachedContactGraphEqualsItsClosedModelRestriction :
      actualAttachedContactGraph≤actualAttachedClosedCapZeroGraph
        (Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve) := by
    intro v w hvw
    obtain ⟨e,he⟩ := hActualSameAttachedGraphAdjacencyProducesPlanarLink hvw
    refine ⟨hvw,e,he,?_⟩
    intro x hx
    obtain ⟨t,ht⟩ := hActualAttachedPlanarEdgePointParameter e x hx
    exact ht ▸ hActualAnyUnitSquarePointIsInClosedModelSquare (actualAttachedSquareEdgePath e t)
  have hActualPhysicalInitialEventIsOnSameLeftBoundary
      (v : actualAttachedContactVertex) (hv : v∈actualOriginalPhysicalInitialEventVertices) :
      v∈actualAttachedLeftBoundaryVertices := by
    obtain ⟨c,rfl,hc⟩ := (Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (actualCentralCollarSquare c.val).1=0
    rw [show c.val=(0,c.val.2) from Prod.ext hc rfl,hActualCentralCollarSquareInitial]
  have hActualSpecifiedOriginalCrossingStartsPhysicalInitialEventProperDrawnCap :
      ∃ v∈actualOriginalPhysicalInitialEventVertices,∃ z∈actualAttachedLeftBoundaryVertices,z≠v ∧
      ∃ W,W≠[] ∧ actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition v) W
        (actualAttachedPlanarVertexPosition z) ∧
      ∃ J : Path (actualAttachedSquareVertexPosition v) (actualAttachedSquareVertexPosition z),
        IsEmbedding J ∧ CurveComplex.LocalSurgery.actualUnitSquareModelPlane '' range J=
          Graph.edgesCover actualAttachedPlanarDrawing W ∧
        (∀ t∈Set.Ioo (0 : Interval) 1,(J t).1∈Set.Ioo (0 : Interval) 1 ∧
          (J t).2∈Set.Ioo (0 : Interval) 1) := by
    obtain ⟨w,hw,hinitial,v,hvw,hboundary,P,hP⟩ := hActualSpecifiedOriginalCrossingHasSameTailAttachedGraphPartner
    have hwE : Sum.inl (Sum.inl w)∈actualOriginalPhysicalInitialEventVertices :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,rfl,hinitial⟩
    have hwB := hActualPhysicalInitialEventIsOnSameLeftBoundary _ hwE
    have hvB : v∈actualAttachedLeftBoundaryVertices := by
      rcases hboundary with ⟨c,rfl,hc⟩ | ⟨m,rfl⟩
      · exact hActualPhysicalInitialEventIsOnSameLeftBoundary _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,rfl,hc⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
    let Q := P.mapLe hActualAttachedContactGraphEqualsItsClosedModelRestriction
    have hQ : Q.IsPath := hP.mapLe hActualAttachedContactGraphEqualsItsClosedModelRestriction
    obtain ⟨z,hz,hzne,Q',hQ',honly,W,hWne,hW,hWD,J,hJ,himage,hinside⟩ :=
      hActualRestrictedCapSimplePathFirstLeftBoundaryProducesProperCrosscut
        (Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve)
        (Sum.inl (Sum.inl w)) v hwB hvB hvw.symm Q hQ
    exact ⟨Sum.inl (Sum.inl w),hwE,z,hz,hzne,W,hWne,hW,J,hJ,himage,hinside⟩
  have hActualProperSquareCrosscutHasPlanarInterior
      {x y : Interval × Interval} (J : Path x y)
      (hinside : ∀ t∈Set.Ioo (0 : Interval) 1,(J t).1∈Set.Ioo (0 : Interval) 1 ∧
        (J t).2∈Set.Ioo (0 : Interval) 1) :
      (CurveComplex.LocalSurgery.actualUnitSquareModelPlane '' range J)\
        {CurveComplex.LocalSurgery.actualUnitSquareModelPlane x,CurveComplex.LocalSurgery.actualUnitSquareModelPlane y}⊆
          Schoenflies.inside Schoenflies.modelCurve := by
    rintro z ⟨⟨s,⟨t,rfl⟩,rfl⟩,hn⟩
    have ht0 : t≠0 := by
      intro he
      subst t
      exact hn (Or.inl (by rw [J.source]))
    have ht1 : t≠1 := by
      intro he
      subst t
      exact hn (Or.inr (Set.mem_singleton_iff.mpr (by rw [J.target])))
    exact CurveComplex.LocalSurgery.actualUnitSquareModelPlaneInterior (J t)
      (hinside t ⟨lt_of_le_of_ne t.property.1 ht0.symm,lt_of_le_of_ne t.property.2 ht1⟩)
  let actualAttachedPhysicalLeftLine : Set Schoenflies.Plane :=
    range (fun t : Interval => CurveComplex.LocalSurgery.actualUnitSquareModelPlane (0,t))
  let actualAttachedProperPhysicalInitialCap (v z : actualAttachedContactVertex)
      (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels) : Prop :=
    v∈actualOriginalPhysicalInitialEventVertices ∧ z∈actualAttachedLeftBoundaryVertices ∧ z≠v ∧ W≠[] ∧
    actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition v) W (actualAttachedPlanarVertexPosition z) ∧
    Schoenflies.IsCutPair Schoenflies.modelCurve (actualAttachedPlanarVertexPosition v)
      (actualAttachedPlanarVertexPosition z) A B ∧ A⊆actualAttachedPhysicalLeftLine ∧
    Graph.edgesCover actualAttachedPlanarDrawing W\
      {actualAttachedPlanarVertexPosition v,actualAttachedPlanarVertexPosition z}⊆Schoenflies.inside Schoenflies.modelCurve ∧
    Schoenflies.IsJordanCurve (A∪Graph.edgesCover actualAttachedPlanarDrawing W) ∧
    ((A∪Graph.edgesCover actualAttachedPlanarDrawing W)∪
      Schoenflies.inside (A∪Graph.edgesCover actualAttachedPlanarDrawing W))⊆
        Schoenflies.modelCurve∪Schoenflies.inside Schoenflies.modelCurve ∧
    ∃ J : Path (actualAttachedSquareVertexPosition v) (actualAttachedSquareVertexPosition z),
      IsEmbedding J ∧ CurveComplex.LocalSurgery.actualUnitSquareModelPlane '' range J=
        Graph.edgesCover actualAttachedPlanarDrawing W ∧
      (∀ t∈Set.Ioo (0 : Interval) 1,(J t).1∈Set.Ioo (0 : Interval) 1 ∧
        (J t).2∈Set.Ioo (0 : Interval) 1)
  have hActualProperPhysicalInitialCapExists :
      ∃ v z A B W,actualAttachedProperPhysicalInitialCap v z A B W := by
    obtain ⟨v,hv,z,hz,hzv,W,hWne,hW,J,hJ,himage,hinside⟩ :=
      hActualSpecifiedOriginalCrossingStartsPhysicalInitialEventProperDrawnCap
    have hvB := hActualPhysicalInitialEventIsOnSameLeftBoundary v hv
    have hv0 := (Finset.mem_filter.mp hvB).2
    have hz0 := (Finset.mem_filter.mp hz).2
    obtain ⟨B,hcut,hJordan,hBound⟩ := hActualProperLeftSquareCrosscutProducesLiteralLeftBoundaryCap
      J hJ hv0 hz0 hinside
    let A := range (fun t : Interval => CurveComplex.LocalSurgery.actualUnitSquareModelPlane
      (0,actualIntervalSegment (actualAttachedSquareVertexPosition v).2 (actualAttachedSquareVertexPosition z).2 t))
    have hcarrier : range (fun t : Interval => CurveComplex.LocalSurgery.actualUnitSquareModelPlane (J t))=
        Graph.edgesCover actualAttachedPlanarDrawing W := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact himage ▸ ⟨J t,⟨t,rfl⟩,rfl⟩
      · intro hx
        rw [←himage] at hx
        obtain ⟨s,⟨t,rfl⟩,he⟩ := hx
        exact ⟨t,he⟩
    have hAleft : A⊆actualAttachedPhysicalLeftLine := by
      rintro x ⟨t,rfl⟩
      exact ⟨actualIntervalSegment (actualAttachedSquareVertexPosition v).2
        (actualAttachedSquareVertexPosition z).2 t,rfl⟩
    have hPi := hActualProperSquareCrosscutHasPlanarInterior J hinside
    rw [himage] at hPi
    refine ⟨v,z,A,B,W,hv,hz,hzv,hWne,hW,hcut,hAleft,hPi,?_,?_,J,hJ,himage,hinside⟩
    · simpa only [hcarrier] using hJordan
    · simpa only [hcarrier] using hBound
  let actualAttachedPhysicalCapEventCount (A : Set Schoenflies.Plane) (v z : actualAttachedContactVertex) : ℕ :=
    (actualOriginalPhysicalInitialEventVertices.filter
      (fun r => actualAttachedPlanarVertexPosition r∈A ∧ r≠v ∧ r≠z)).card
  have hActualProperPhysicalInitialCapHasMinimumEventCount :
      ∃ v z A B W,actualAttachedProperPhysicalInitialCap v z A B W ∧
        ∀ v' z' A' B' W',actualAttachedProperPhysicalInitialCap v' z' A' B' W' →
          actualAttachedPhysicalCapEventCount A v z≤actualAttachedPhysicalCapEventCount A' v' z' := by
    have hex : ∃ n : ℕ,∃ v z A B W,actualAttachedProperPhysicalInitialCap v z A B W ∧
        actualAttachedPhysicalCapEventCount A v z=n := by
      obtain ⟨v,z,A,B,W,hCap⟩ := hActualProperPhysicalInitialCapExists
      exact ⟨_,v,z,A,B,W,hCap,rfl⟩
    obtain ⟨v,z,A,B,W,hCap,hcount⟩ := Nat.find_spec hex
    refine ⟨v,z,A,B,W,hCap,?_⟩
    intro v' z' A' B' W' hCap'
    rw [hcount]
    exact Nat.find_min' hex ⟨v',z',A',B',W',hCap',rfl⟩
  have hActualMinimumProperPhysicalInitialCapHasNoExtraOriginalPhysicalEvent :
      ∃ v z A B W,actualAttachedProperPhysicalInitialCap v z A B W ∧
        ∀ r∈actualOriginalPhysicalInitialEventVertices,actualAttachedPlanarVertexPosition r∈A → r=v ∨ r=z := by
    obtain ⟨v,z,A,B,W,hCap,hmin⟩ := hActualProperPhysicalInitialCapHasMinimumEventCount
    refine ⟨v,z,A,B,W,hCap,?_⟩
    intro r hrE hrA
    by_contra hne
    have hra : r≠v := fun he => hne (Or.inl he)
    have hrb : r≠z := fun he => hne (Or.inr he)
    obtain ⟨hv,hz,hzv,hWne,hW,hcut,hAleft,hPi,hJ,hBound,J,hJemb,hJimage,hJinside⟩ := hCap
    obtain ⟨z',hz',hz'r,R,T,hRT,hRA,hDrop,U,hUne,hU,hNewJ,hNested,J',hJ'emb,hJ'image,hJ'inside⟩ :=
      hActualExtraPhysicalInitialEventProducesStrictlySmallerNestedProperCap A B W v z r
        hcut hW hWne hPi hJ hBound hz hrE hrA hra hrb
    have hRleft : R⊆actualAttachedPhysicalLeftLine := hRA.trans hAleft
    have hNewBound := hNested.trans hBound
    have hNewPi := hActualProperSquareCrosscutHasPlanarInterior J' hJ'inside
    rw [hJ'image] at hNewPi
    have hNewCap : actualAttachedProperPhysicalInitialCap r z' R T U :=
      ⟨hrE,hz',hz'r,hUne,hU,hRT,hRleft,hNewPi,hNewJ,hNewBound,J',hJ'emb,hJ'image,hJ'inside⟩
    have hle := hmin r z' R T U hNewCap
    change actualAttachedPhysicalCapEventCount R r z'<actualAttachedPhysicalCapEventCount A v z at hDrop
    exact (not_lt_of_ge hle) hDrop
  have hActualPhysicalLeftLineIsEmbeddedArc :
      Schoenflies.IsArcBetween actualAttachedPhysicalLeftLine
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlane (0,0))
        (CurveComplex.LocalSurgery.actualUnitSquareModelPlane (0,1)) := by
    let L : Path ((0 : Interval),(0 : Interval)) ((0 : Interval),(1 : Interval)) := {
      toFun := fun t => (0,t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
    have hL : IsEmbedding L := by
      apply L.continuous.isClosedEmbedding _ |>.isEmbedding
      intro t s he
      exact congrArg Prod.snd he
    exact CurveComplex.LocalSurgery.actual_embedded_path_isArcBetween
      (L.map CurveComplex.LocalSurgery.actualUnitSquareModelPlane.continuous)
      (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.comp hL)
  have hActualProperInitialCapCutArcIsLiteralOriginalBoundaryInterval
      (v z : actualAttachedContactVertex) (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (hCap : actualAttachedProperPhysicalInitialCap v z A B W) :
      A=range (fun t : Interval => CurveComplex.LocalSurgery.actualUnitSquareModelPlane
        (0,actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2 t)) := by
    obtain ⟨hv,hz,hzv,hWne,hW,hcut,hAleft,hs⟩ := hCap
    have hv0 := (Finset.mem_filter.mp (hActualPhysicalInitialEventIsOnSameLeftBoundary v hv)).2
    have hz0 := (Finset.mem_filter.mp hz).2
    have hcoords : (actualAttachedSquareVertexPosition v).2≠(actualAttachedSquareVertexPosition z).2 := by
      intro he
      exact hzv (hActualAttachedSquareVertexPositionInjective
        (Prod.ext (hz0.trans hv0.symm) he.symm))
    let L : Path (actualAttachedSquareVertexPosition v) (actualAttachedSquareVertexPosition z) := {
      toFun := fun t => (0,actualIntervalSegment (actualAttachedSquareVertexPosition v).2
        (actualAttachedSquareVertexPosition z).2 t)
      continuous_toFun := continuous_const.prodMk
        (actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2).continuous
      source' := by
        apply Prod.ext
        · exact hv0.symm
        · apply Subtype.ext
          change (1-(0 : ℝ))*_+0*_= _
          ring
      target' := by
        apply Prod.ext
        · exact hz0.symm
        · apply Subtype.ext
          change (1-(1 : ℝ))*_+1*_= _
          ring }
    have hL : IsEmbedding L := by
      apply L.continuous.isClosedEmbedding _ |>.isEmbedding
      intro t s he
      exact actualIntervalSegmentInjectiveOfNe _ _ hcoords (congrArg Prod.snd he)
    have hArc := CurveComplex.LocalSurgery.actual_embedded_path_isArcBetween
      (L.map CurveComplex.LocalSurgery.actualUnitSquareModelPlane.continuous)
      (CurveComplex.LocalSurgery.actualUnitSquareModelPlaneEmbedding.comp hL)
    have hLleft : range (L.map CurveComplex.LocalSurgery.actualUnitSquareModelPlane.continuous)⊆
        actualAttachedPhysicalLeftLine := by
      rintro x ⟨t,rfl⟩
      exact ⟨actualIntervalSegment (actualAttachedSquareVertexPosition v).2
        (actualAttachedSquareVertexPosition z).2 t,rfl⟩
    exact hcut.fst.eq_of_subset_arc hArc hActualPhysicalLeftLineIsEmbeddedArc hAleft hLleft
  have hActualMinimumPhysicalCapOriginalBoundaryInteriorAvoidsAllOriginalOldArc :
      ∃ v z A B W,actualAttachedProperPhysicalInitialCap v z A B W ∧
        ∀ t∈Set.Ioo (0 : Interval) 1,b.val.map
          (actualIntervalSegment (actualAttachedSquareVertexPosition v).2
            (actualAttachedSquareVertexPosition z).2 t)∉a.val.image := by
    obtain ⟨v,z,A,B,W,hCap,hno⟩ := hActualMinimumProperPhysicalInitialCapHasNoExtraOriginalPhysicalEvent
    have hA := hActualProperInitialCapCutArcIsLiteralOriginalBoundaryInterval v z A B W hCap
    refine ⟨v,z,A,B,W,hCap,?_⟩
    intro t ht ha
    have hvE := hCap.1
    have hzB := hCap.2.1
    have hzv := hCap.2.2.1
    obtain ⟨c,hvc,hc,hcross⟩ := hActualEveryOriginalPhysicalInitialEventIsActualCrossing v hvE
    have hvpair : actualAttachedSquareVertexPosition v=(0,actualCentralParameter c.val.2) := by
      rw [hvc]
      change actualCentralCollarSquare c.val=(0,actualCentralParameter c.val.2)
      rw [show c.val=(0,c.val.2) from Prod.ext hc rfl,hActualCentralCollarSquareInitial]
    let s := actualIntervalSegment (actualAttachedSquareVertexPosition v).2
      (actualAttachedSquareVertexPosition z).2 t
    have hvInterior : (actualAttachedSquareVertexPosition v).2∈Set.Ioo (0 : Interval) 1 := by
      rw [hvpair]
      exact hActualCentralParameterInterior c.val.2
    have hsInterior : s∈Set.Ioo (0 : Interval) 1 := by
      change 0<(1-t.val)*(actualAttachedSquareVertexPosition v).2.val+
        t.val*(actualAttachedSquareVertexPosition z).2.val ∧
        (1-t.val)*(actualAttachedSquareVertexPosition v).2.val+
        t.val*(actualAttachedSquareVertexPosition z).2.val<1
      have ht0 : 0<t.val := ht.1
      have ht1 : t.val<1 := ht.2
      have hv0 : 0<(actualAttachedSquareVertexPosition v).2.val := hvInterior.1
      have hv1 : (actualAttachedSquareVertexPosition v).2.val<1 := hvInterior.2
      have hz0 := (actualAttachedSquareVertexPosition z).2.property.1
      have hz1 := (actualAttachedSquareVertexPosition z).2.property.2
      have hpos := mul_pos (sub_pos.mpr ht1) hv0
      have hpos' := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hv1)
      have hnonneg := mul_nonneg (le_of_lt ht0) hz0
      have hnonneg' := mul_nonneg (le_of_lt ht0) (sub_nonneg.mpr hz1)
      constructor <;> nlinarith
    have hsE : s∈actualOriginalLeftBoundaryEvents := hcontacts.mem_toFinset.mpr ha
    obtain ⟨r,hr0,hrpos,hrdegree⟩ := hActualEveryUnmarkedPhysicalBoundaryEventIsSameAttachedInitialVertex
      s hsE (ne_of_gt hsInterior.1) (ne_of_lt hsInterior.2)
    have hrE : Sum.inl (Sum.inl r)∈actualOriginalPhysicalInitialEventVertices :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,rfl,hr0⟩
    have hrA : actualAttachedPlanarVertexPosition (Sum.inl (Sum.inl r))∈A := by
      rw [hA]
      refine ⟨t,?_⟩
      change CurveComplex.LocalSurgery.actualUnitSquareModelPlane (0,s)=
        CurveComplex.LocalSurgery.actualUnitSquareModelPlane (actualAttachedSquareVertexPosition (Sum.inl (Sum.inl r)))
      exact congrArg CurveComplex.LocalSurgery.actualUnitSquareModelPlane hrpos.symm
    have hv0 := (Finset.mem_filter.mp (hActualPhysicalInitialEventIsOnSameLeftBoundary v hvE)).2
    have hz0 := (Finset.mem_filter.mp hzB).2
    have hcoords : (actualAttachedSquareVertexPosition v).2≠(actualAttachedSquareVertexPosition z).2 := by
      intro he
      exact hzv (hActualAttachedSquareVertexPositionInjective (Prod.ext (hz0.trans hv0.symm) he.symm))
    rcases hno _ hrE hrA with he | he
    · have hs : s=(actualAttachedSquareVertexPosition v).2 :=
        (congrArg Prod.snd (hrpos.symm.trans (congrArg actualAttachedSquareVertexPosition he)))
      have he0 : actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2 t=
          actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2 0 := by
        apply Subtype.ext
        change s.val=(1-(0 : ℝ))*_+0*_
        rw [hs]
        ring
      exact (ne_of_gt ht.1) (actualIntervalSegmentInjectiveOfNe _ _ hcoords he0)
    · have hs : s=(actualAttachedSquareVertexPosition z).2 :=
        (congrArg Prod.snd (hrpos.symm.trans (congrArg actualAttachedSquareVertexPosition he)))
      have he1 : actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2 t=
          actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2 1 := by
        apply Subtype.ext
        change s.val=(1-(1 : ℝ))*_+1*_
        rw [hs]
        ring
      exact (ne_of_lt ht.2) (actualIntervalSegmentInjectiveOfNe _ _ hcoords he1)
  have hActualAnyOriginalCentralContactWalkProducesEmbeddedOriginalContactPath
      (w z : actualContactVertices) (hzw : z≠w)
      (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z)) (hP : P.IsPath) :
      ∃ q : Path w.val z.val,IsEmbedding q ∧
        (∀ t,actualFiniteConeSweep (q t)∈a.val.image) ∧
      ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
        (∀ t,κ t∈Set.Ioo (0 : Interval) 1) := by
    obtain ⟨W,hW,hvertices⟩ := CurveComplex.LocalSurgery.actual_simple_graph_path_to_labeled_graph_with_vertices
      actualZeroGraph actualPlanarGraph actualPlanarVertexPosition actualPlanarVertexPositionInjective
      (fun r => ⟨r,rfl⟩) (fun h => hActualContactGraphAdjacencyProducesPlanarLink h) P hP
    have hne : W≠[] := by
      intro hn
      rw [hn] at hW
      have he : (Sum.inl w : zeroVertex)=Sum.inl z := actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil
      exact hzw (Sum.inl.inj he).symm
    have hArc := actualPlanarDrawingIsDrawing.path_isArcBetween hW hne
    have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
      intro x hx
      obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
      obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
      exact ⟨actualGlobalContactArcs e.1 u,hpoint⟩
    obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
    have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
      have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
        himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
      obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
      obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
      have hqu : actualGlobalContactArcs e.1 u=q t := hActualParameterSquarePlaneInjective hpoint
      rw [←hqu]
      exact hActualGlobalContactArcImage e.1 u
    obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact
      (fun t => hActualFiniteConeSweepMarks (q t))
    exact ⟨q,hq,hcontact,κ,hκ,hinside⟩
  have hActualAttachedPlanarVisitedVertexIsOnSameDrawnCarrier
      {v z : actualAttachedContactVertex} {W : List actualAttachedEdgeLabels}
      (hW : actualAttachedPlanarGraph.IsPath (actualAttachedPlanarVertexPosition v) W
        (actualAttachedPlanarVertexPosition z)) (hne : W≠[])
      (x : Schoenflies.Plane)
      (hx : x∈actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition v) W) :
      x∈Graph.edgesCover actualAttachedPlanarDrawing W := by
    rw [hW.isWalk.walkVertices_eq_covered hne] at hx
    obtain ⟨e,he,y,hlink⟩ := hx
    exact Graph.mem_edgesCover he
      (hActualSameChosenTailAttachedPlanarDrawingIsDrawing.edge_isArcBetween hlink).left_mem
  have hActualProperPhysicalCapSameWalkMarkedVerticesOnlyAtTerminal
      (v z : actualAttachedContactVertex) (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (hCap : actualAttachedProperPhysicalInitialCap v z A B W) :
      ∃ P : actualAttachedContactGraph.Walk v z,P.IsPath ∧
        actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition v) W=
          actualAttachedPlanarVertexPosition '' {r | r∈P.support} ∧
        ∀ m : Fin 2,Sum.inr m∈P.support → Sum.inr m=z := by
    obtain ⟨hv,hz,hzv,hWne,hW,hcut,hAleft,hPi,hs⟩ := hCap
    obtain ⟨P,hP,hvertices⟩ := CurveComplex.LocalSurgery.actual_labeled_graph_path_to_simple_graph_with_vertices
      actualAttachedContactGraph actualAttachedPlanarGraph actualAttachedPlanarVertexPosition
      hActualAttachedPlanarVertexPositionInjective (fun x hx => hx)
      (fun {v w e} he => hActualSameAttachedPlanarLinkRecoversLiteralContactAdjacency he)
      hW v z rfl rfl
    refine ⟨P,hP,hvertices,?_⟩
    intro m hm
    have hvisit : actualAttachedPlanarVertexPosition (Sum.inr m)∈
        actualAttachedPlanarGraph.walkVertices (actualAttachedPlanarVertexPosition v) W :=
      hvertices ▸ ⟨Sum.inr m,hm,rfl⟩
    have hcarrier := hActualAttachedPlanarVisitedVertexIsOnSameDrawnCarrier hW hWne _ hvisit
    have hmodel : actualAttachedPlanarVertexPosition (Sum.inr m)∈Schoenflies.modelCurve :=
      CurveComplex.LocalSurgery.actualUnitSquareModelPlaneBoundary _ (Or.inl rfl)
    have hmv : Sum.inr m≠v := by
      obtain ⟨c,hc,hfirst⟩ := (Finset.mem_filter.mp hv).2
      rw [hc]
      exact Sum.inr_ne_inl
    by_contra hmz
    have hne : actualAttachedPlanarVertexPosition (Sum.inr m)∉
        ({actualAttachedPlanarVertexPosition v,actualAttachedPlanarVertexPosition z} : Set Schoenflies.Plane) := by
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
      exact ⟨fun h => hmv (hActualAttachedPlanarVertexPositionInjective h),
        fun h => hmz (hActualAttachedPlanarVertexPositionInjective h)⟩
    exact Schoenflies.inside_subset_compl (hPi ⟨hcarrier,hne⟩) hmodel
  have hActualProperInitialCapRecoversOriginalCentralWalkAndSameTerminalTail
      (v z : actualAttachedContactVertex) (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (hCap : actualAttachedProperPhysicalInitialCap v z A B W) :
      ∃ w : actualContactVertices,v=Sum.inl (Sum.inl w) ∧ w.val.1=0 ∧
        ((∃ c : actualContactVertices,z=Sum.inl (Sum.inl c) ∧ c.val.1=0 ∧ c≠w ∧
          ∃ Q : actualZeroGraph.Walk (Sum.inl w) (Sum.inl c),Q.IsPath) ∨
         (∃ m : Fin 2,z=Sum.inr m ∧ ∃ c : actualContactVertices,
          c.val.2=actualAttachedMarkHeight m ∧ c≠w ∧
          ∃ Q : actualZeroGraph.Walk (Sum.inl c) (Sum.inl w),Q.IsPath)) := by
    obtain ⟨w,hvw,hw⟩ := (Finset.mem_filter.mp hCap.1).2
    obtain ⟨P,hP,hvertices,hMarks⟩ := hActualProperPhysicalCapSameWalkMarkedVerticesOnlyAtTerminal v z A B W hCap
    have hzBoundary := hCap.2.1
    have hzv := hCap.2.2.1
    refine ⟨w,hvw,hw,?_⟩
    rcases hActualAttachedActualLeftSideVertexIsInitialOrChosenMark z hzBoundary with ⟨c,hzc,hc⟩ | ⟨m,hzm⟩
    · subst v z
      have hcw : c≠w := by
        intro he
        exact hzv (congrArg (fun r : actualContactVertices => (Sum.inl (Sum.inl r) : actualAttachedContactVertex)) he)
      have hOnly : ∀ r∈P.support,∃ x : zeroVertex,r=Sum.inl x := by
        intro r hr
        cases r with
        | inl x => exact ⟨x,rfl⟩
        | inr m => exact (Sum.inr_ne_inl (hMarks m hr)).elim
      obtain ⟨Q,hQ,hSupport⟩ := CurveComplex.LocalSurgery.actualCentralOnlyAttachedWalkProjects
        actualZeroGraph actualAttachedContactGraph (fun u v h => h) P hP hOnly
      exact Or.inl ⟨c,rfl,hc,hcw,Q,hQ⟩
    · subst v z
      have hOnlyMark : ∀ n : Fin 2,Sum.inr n∈P.support → n=m := by
        intro n hn
        exact Sum.inr.inj (hMarks n hn)
      obtain ⟨r,hr,Q,hQ⟩ := CurveComplex.LocalSurgery.actualTerminalMarkedAttachedWalkProjects
        actualZeroGraph actualAttachedContactGraph actualAttachedTailIncidence
        (fun u v h => h) (fun m n h => h) (fun m v h => h) P hP hOnlyMark
      obtain ⟨c,hrc,hc⟩ := hr
      subst r
      have hcBoundary : c.val.2=0 ∨ c.val.2=1 := by
        fin_cases m
        · exact Or.inl hc
        · exact Or.inr hc
      have hcw : c≠w := by
        intro he
        have hpos := (hActualMarkedSeamContactFirstCoordinateInterior c hcBoundary).1
        rw [he,hw] at hpos
        exact (lt_irrefl (0 : Interval)) hpos
      exact Or.inr ⟨m,rfl,c,hc,hcw,Q,hQ⟩
  have hActualProperPhysicalInitialCapProducesOriginalEmbeddedSubpathPair
      (v z : actualAttachedContactVertex) (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (hCap : actualAttachedProperPhysicalInitialCap v z A B W) :
      ∃ (f g : C(Interval,S)) (u vPhysical : S),IsEmbedding f ∧ IsEmbedding g ∧
        range f⊆a.val.image ∧ range g⊆b.val.image ∧
        f 0=u ∧ g 0=u ∧ f 1=vPhysical ∧ g 1=vPhysical ∧ u≠vPhysical ∧
        g 0=b.val.map (actualAttachedSquareVertexPosition z).2 ∧
        g 1=b.val.map (actualAttachedSquareVertexPosition v).2 ∧
        vPhysical∈ArcSurgery.crossings M a b ∧
        (u∈ArcSurgery.crossings M a b ∨ (u∈a.val.image∩b.val.image ∧ u∈(M.cover.branch : Set S))) ∧
        ∃ (hu : u∈((M.cover.branch : Set S)\{u})ᶜ)
          (hv : vPhysical∈((M.cover.branch : Set S)\{u})ᶜ)
          (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ) ⟨vPhysical,hv⟩),
          (∀ t,(α t : S)=f t) ∧ (∀ t,(β t : S)=g t) ∧ α.Homotopic β := by
    obtain ⟨w,hvw,hw,hRoute⟩ := hActualProperInitialCapRecoversOriginalCentralWalkAndSameTerminalTail v z A B W hCap
    have hwpair : w.val=(0,w.val.2) := Prod.ext hw rfl
    have hStartPhysical : b.val.map (actualAttachedSquareVertexPosition v).2=actualFiniteConeSweep w.val := by
      rw [hvw]
      change b.val.map (actualCentralCollarSquare w.val).2=actualFiniteConeSweep w.val
      rw [hwpair,hActualCentralCollarSquareInitial,hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
    have hStartCross : b.val.map (actualAttachedSquareVertexPosition v).2∈ArcSurgery.crossings M a b :=
      (hActualEveryOriginalPhysicalInitialEventIsActualCrossing v hCap.1).choose_spec.2.2
    rcases hRoute with ⟨c,hzc,hc,hcw,Q,hQ⟩ | ⟨m,hzm,c,hc,hcw,Q,hQ⟩
    · obtain ⟨q,hq,hcontact,κ,hκ,hκinside⟩ :=
        hActualAnyOriginalCentralContactWalkProducesEmbeddedOriginalContactPath w c hcw Q hQ
      obtain ⟨f,g,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,hne,hu,hv,α,β,hα,hβ,hhom⟩ :=
        hActualBottomPartnerYieldsBothEmbeddedOriginalSubpathsPuncturedHomotopic w c hw hc hcw q κ hκ hκinside
      have hcpair : c.val=(0,c.val.2) := Prod.ext hc rfl
      have hEndPhysical : b.val.map (actualAttachedSquareVertexPosition z).2=actualFiniteConeSweep c.val := by
        rw [hzc]
        change b.val.map (actualCentralCollarSquare c.val).2=actualFiniteConeSweep c.val
        rw [hcpair,hActualCentralCollarSquareInitial,hActualFiniteConeSweepInitial,hActualCentralSweepInitial]
      have hzE : z∈actualOriginalPhysicalInitialEventVertices :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,c,hzc,hc⟩
      have hEndCross : b.val.map (actualAttachedSquareVertexPosition z).2∈ArcSurgery.crossings M a b :=
        (hActualEveryOriginalPhysicalInitialEventIsActualCrossing z hzE).choose_spec.2.2
      exact ⟨f,g,actualFiniteConeSweep c.val,actualFiniteConeSweep w.val,hf,hg,hfa,hgb,
        hf0,hg0,hf1,hg1,hne,hg0.trans hEndPhysical.symm,hg1.trans hStartPhysical.symm,
        hStartPhysical ▸ hStartCross,Or.inl (hEndPhysical ▸ hEndCross),hu,hv,α,β,hα,hβ,hhom⟩
    · have hm : actualAttachedMarkHeight m=0 ∨ actualAttachedMarkHeight m=1 := by
        fin_cases m
        · exact Or.inl rfl
        · exact Or.inr rfl
      obtain ⟨q,hq,hcontact,κ,hκ,hκinside⟩ :=
        hActualAnyOriginalCentralContactWalkProducesEmbeddedOriginalContactPath c w hcw.symm Q hQ
      let q' : Path c.val ((0 : Interval),w.val.2) := q.cast rfl hwpair.symm
      obtain ⟨f,g,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,hne,hu,hv,α,β,hα,hβ,hhom⟩ :=
        hActualMarkedSidePartnerYieldsBothEmbeddedOriginalSubpathsPuncturedHomotopic
          (actualAttachedMarkHeight m) hm c hc w.val.2 q' (fun t => hcontact t)
      have hEndPhysical : b.val.map (actualAttachedSquareVertexPosition z).2=af 0 := by
        rw [hzm]
        exact (hActualMarkedTailSideContactVertexRetainsOriginalBoundaryRouteHomotopy
          (actualAttachedMarkHeight m) hm c hc).1
      have hStartPhysical' : b.val.map (actualAttachedSquareVertexPosition v).2=actualFiniteConeSweep (0,w.val.2) :=
        hStartPhysical.trans (congrArg actualFiniteConeSweep hwpair)
      have hUMarked : af 0∈a.val.image∩b.val.image ∧ af 0∈(M.cover.branch : Set S) :=
        ⟨⟨hfa ⟨0,hf0⟩,hgb ⟨0,hg0⟩⟩,hAFStartMarked⟩
      exact ⟨f,g,af 0,actualFiniteConeSweep (0,w.val.2),hf,hg,hfa,hgb,
        hf0,hg0,hf1,hg1,hne,hg0.trans hEndPhysical.symm,hg1.trans hStartPhysical'.symm,
        hStartPhysical' ▸ hStartCross,Or.inr hUMarked,hu,hv,α,β,hα,hβ,hhom⟩
  have hActualAnyEmbeddedOriginalBoundarySubpathBetweenMinimumCapCornersAvoidsOriginalOldArc
      (v z : actualAttachedContactVertex) (A B : Set Schoenflies.Plane) (W : List actualAttachedEdgeLabels)
      (hCap : actualAttachedProperPhysicalInitialCap v z A B W)
      (hAvoid : ∀ t∈Set.Ioo (0 : Interval) 1,b.val.map
        (actualIntervalSegment (actualAttachedSquareVertexPosition v).2
          (actualAttachedSquareVertexPosition z).2 t)∉a.val.image)
      (g : C(Interval,S)) (hg : IsEmbedding g) (hgb : range g⊆b.val.image)
      (hg0 : g 0=b.val.map (actualAttachedSquareVertexPosition z).2)
      (hg1 : g 1=b.val.map (actualAttachedSquareVertexPosition v).2) :
      ∀ t∈Set.Ioo (0 : Interval) 1,g t∉a.val.image := by
    have hv0 := (Finset.mem_filter.mp (hActualPhysicalInitialEventIsOnSameLeftBoundary v hCap.1)).2
    have hz0 := (Finset.mem_filter.mp hCap.2.1).2
    have hcoords : (actualAttachedSquareVertexPosition v).2≠(actualAttachedSquareVertexPosition z).2 := by
      intro he
      exact hCap.2.2.1 (hActualAttachedSquareVertexPositionInjective
        (Prod.ext (hz0.trans hv0.symm) he.symm))
    let η : C(Interval,Interval) := ⟨fun t => actualIntervalSegment
      (actualAttachedSquareVertexPosition v).2 (actualAttachedSquareVertexPosition z).2 (unitInterval.symm t),
      (actualIntervalSegment (actualAttachedSquareVertexPosition v).2
        (actualAttachedSquareVertexPosition z).2).continuous.comp unitInterval.symmHomeomorph.continuous⟩
    have hη : Function.Injective η := (actualIntervalSegmentInjectiveOfNe _ _ hcoords).comp
      unitInterval.symmHomeomorph.injective
    have hη0 : η 0=(actualAttachedSquareVertexPosition z).2 := by
      change actualIntervalSegment _ _ (unitInterval.symm 0)=_
      rw [unitInterval.symm_zero]
      apply Subtype.ext
      change (1-(1 : ℝ))*_+1*_= _
      ring
    have hη1 : η 1=(actualAttachedSquareVertexPosition v).2 := by
      change actualIntervalSegment _ _ (unitInterval.symm 1)=_
      rw [unitInterval.symm_one]
      apply Subtype.ext
      change (1-(0 : ℝ))*_+0*_= _
      ring
    have hηAvoid : ∀ t∈Set.Ioo (0 : Interval) 1,b.val.map (η t)∉a.val.image := by
      intro t ht
      apply hAvoid (unitInterval.symm t)
      change 0<1-t.val ∧ 1-t.val<1
      have h0 : 0<t.val := ht.1
      have h1 : t.val<1 := ht.2
      constructor <;> linarith
    exact CurveComplex.LocalSurgery.actualOriginalBoundarySubarcInteriorAvoidance
      ⟨b.val.map,b.val.continuous⟩ g a.val.image (NonLoopArc.isEmbedding ⟨b.val,hbne⟩)
      hg hgb η hη (hg0.trans (congrArg b.val.map hη0.symm))
      (hg1.trans (congrArg b.val.map hη1.symm)) hηAvoid
  obtain ⟨v,z,A,B,W,hCap,hAvoidOriginalBoundary⟩ :=
    hActualMinimumPhysicalCapOriginalBoundaryInteriorAvoidsAllOriginalOldArc
  obtain ⟨f,g,u,vPhysical,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,hne,hg0param,hg1param,
    hVcross,hUcorner,hu,hv,α,β,hα,hβ,hhom⟩ :=
    hActualProperPhysicalInitialCapProducesOriginalEmbeddedSubpathPair v z A B W hCap
  have hAvoidG := hActualAnyEmbeddedOriginalBoundarySubpathBetweenMinimumCapCornersAvoidsOriginalOldArc
    v z A B W hCap hAvoidOriginalBoundary g hg hgb hg0param hg1param
  have hPhysicalIntersection : range f∩range g=({u,vPhysical} : Set S) := by
    ext x
    constructor
    · rintro ⟨hxf,⟨t,ht⟩⟩
      by_cases ht0 : t=0
      · subst t
        exact Or.inl (ht.symm.trans hg0)
      by_cases ht1 : t=1
      · subst t
        exact Or.inr (Set.mem_singleton_iff.mpr (ht.symm.trans hg1))
      exact (hAvoidG t ⟨lt_of_le_of_ne t.property.1 (fun h => ht0 h.symm),
        lt_of_le_of_ne t.property.2 ht1⟩ (ht.symm ▸ hfa hxf)).elim
    · intro hx
      rcases hx with hx | hx
      · have he : x=u := hx
        subst x
        exact ⟨⟨0,hf0⟩,⟨0,hg0⟩⟩
      · have he : x=vPhysical := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨1,hf1⟩,⟨1,hg1⟩⟩
  exact ⟨f,g,u,vPhysical,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,hne,hPhysicalIntersection,
    hVcross,hUcorner,hu,hv,α,β,hα,hβ,hhom⟩

end CurveComplex.HyperellipticModel
