import ClassificationOfSurfaces.NormalForm
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12FullConnectivity
import ClassificationOfSurfaces.DiskSquare
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.ActualSourceSixArcParametersCanonicalReuse
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.ActualOneFaceCutTotalAttachingProof
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.ActualCornerBoundaryRunNormalizationProof
import CurveComplexGenusTwo.Topology.ActualSourceTree.ActualSourceFiveEdgeTreeContractionProof
import CurveComplexGenusTwo.Topology.ActualSourceTree.CollapseLocal
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.ConeChains
import CurveComplexGenusTwo.Filtration.GoodSubcomplexAcyclic
import CurveComplexGenusTwo.Topology.ActualAlternatingModelTransfer
import CurveComplexGenusTwo.Topology.ArcCounts.ActualFullACard12

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
open scoped Simplicial

open Set Topology Metric Bornology AlternatingSphereCover

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
open CurveComplexGenusTwo.Topology
open scoped Manifold ContDiff

theorem actual_entire_alternating_total_standard_genus_two_octagon : Nonempty (AlternatingSphereCover.Total ≃ₜ Quot (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel 2 0)) := by
  classical
  have hboundary_half_rectangle :
      let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
      let K : Set B := {v | v.1.val=0 ∧ |v.2.val|≤1}
      ∃ F : C(B,B),
        (∀ v, (F v).1.val=v.1.val) ∧ Function.Surjective F ∧
        (∀ v w, F v=F w ↔ v=w ∨ (v∈K ∧ w∈K)) ∧
        (∀ v : B, (v.1.val=2 ∨ |v.2.val|=2) → F v=v) := by
    dsimp only
    let D := Set.Icc (-2:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
    obtain ⟨F,hformula,hs,hker,hbd⟩ :=
      AlternatingSphereCover.actual_central_arc_rectangle_collapse
    have hx (v : D) : (F v).1.val=v.1.val := (hformula v).1
    let j : B → D := fun v => (⟨v.1.val,⟨by linarith [v.1.property.1],v.1.property.2⟩⟩,v.2)
    have hj : Function.Injective j := by
      intro v w h
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z : D => z.1.val) h
      · exact congrArg (fun z : D => z.2) h
    let f : C(B,B) :=
      ⟨fun v => (⟨(F (j v)).1.val,⟨by rw [hx];exact v.1.property.1,
        (F (j v)).1.property.2⟩⟩,(F (j v)).2),by
        have hjc : Continuous j := by
          change Continuous (fun v : B => ((⟨v.1.val,_⟩ : Set.Icc (-2:ℝ) 2),v.2))
          exact (continuous_fst.subtype_val.subtype_mk _).prodMk continuous_snd
        have hc := F.continuous.comp hjc
        exact (hc.fst.subtype_val.subtype_mk _).prodMk hc.snd⟩
    have hfj (v : B) : j (f v)=F (j v) := by rfl
    refine ⟨f,fun v => hx (j v),?_,?_,?_⟩
    · intro w
      obtain ⟨v,hv⟩ := hs (j w)
      have hvx : v.1.val=w.1.val := by
        simpa only [hx] using congrArg (fun z : D => z.1.val) hv
      let v' : B := (⟨v.1.val,⟨by rw [hvx];exact w.1.property.1,v.1.property.2⟩⟩,v.2)
      have hjv : j v'=v := by rfl
      refine ⟨v',hj ?_⟩
      rw [hfj,hjv,hv]
    · intro v w
      constructor
      · intro h
        have h' := (hker (j v) (j w)).mp (by rw [←hfj,←hfj,h])
        rcases h' with h'|h'
        · exact Or.inl (hj h')
        · exact Or.inr h'
      · rintro (h|h)
        · exact congrArg f h
        · apply hj
          rw [hfj,hfj]
          exact (hker _ _).mpr (Or.inr h)
    · intro v hv
      apply hj
      rw [hfj]
      apply hbd
      rcases hv with hv|hv
      · left;change |v.1.val|=2;rw [hv];norm_num
      · exact Or.inr hv
  have hsurviving_actual_parameters :
      ∃ G : C(AlternatingSphereCover.Total,AlternatingSphereCover.Total),
        Function.Surjective G ∧
        ∀ p q : AlternatingSphereCover.Sphere, ∀ hp : AlternatingSphereCover.height p=0,
        ∀ hq : AlternatingSphereCover.height q=0,
          ¬AlternatingSphereCover.branch p → ¬AlternatingSphereCover.branch q →
          (G (AlternatingSphereCover.northDiskFace false (AlternatingSphereCover.diskBoundaryPoint p hp))=
           G (AlternatingSphereCover.northDiskFace false (AlternatingSphereCover.diskBoundaryPoint q hq)) ↔ p=q) := by
    classical
    let A : Set Total := northDiskFace true ''
      (Set.ofPred (fun v : StandardDisk => ∃ q : Sphere, ∃ hq : height q=0,
        (∃ i : Fin 6, i≠0 ∧ closedArcSector i q) ∧ v=diskBoundaryPoint q hq))
    have hintersection (p : Sphere) (hp : height p=0) :
        northDiskFace false (diskBoundaryPoint p hp)∈A ↔ branch p := by
        dsimp [A]
        constructor
        · rintro ⟨v,⟨q,hq,hi,rfl⟩,he⟩
          rw [northDiskFace_boundary,northDiskFace_boundary] at he
          have hqp : q=p := congrArg projection he
          subst q
          change (Quotient.mk setoid (pieceToRaw (Sum.inl (northBoundary p hq true))) : Total)=
            Quotient.mk setoid (pieceToRaw (Sum.inl (northBoundary p hp false))) at he
          rw [Quotient.eq] at he
          change p=p ∧ (branch p ∨ label (pieceToRaw (Sum.inl (northBoundary p hq true)))=
            label (pieceToRaw (Sum.inl (northBoundary p hp false)))) at he
          have hb := he.2
          by_cases hpos : 0<seamPolynomial p <;>
            simpa [label,pieceToRaw,northBoundary,hpos] using hb
        · intro hb
          obtain ⟨i,hi⟩ := (branch_iff_mem_range p).mp hb
          obtain ⟨j,hji⟩ := cyclicBranchEquiv.surjective i
          have hbp : branchPoint (cyclicBranch j)=p := by
            change cyclicBranch j=i at hji
            rw [hji];exact hi
          let k : Fin 6 := if j=0 then 5 else j
          have hk0 : k≠0 := by fin_cases j <;> norm_num [k]
          have hk : closedArcSector k p := by
            rw [←hbp,closedArcSector_branch_iff_endpoints]
            fin_cases j <;> norm_num [k]
          refine ⟨diskBoundaryPoint p hp,⟨p,hp,⟨k,hk0,hk⟩,rfl⟩,?_⟩
          rw [northDiskFace_boundary,northDiskFace_boundary]
          apply (branch_fiber_unique hb).unique
          · exact projection_northCharacteristic _
          · exact projection_northCharacteristic _
    obtain ⟨G,hGs,hGker,hHomeo⟩ := actual_source_five_edge_tree_contraction
    refine ⟨G,hGs,?_⟩
    intro p q hp hq hnp hnq
    constructor
    · intro h
      rcases (hGker _ _).mp h with he|ha
      · have he' := congrArg projection he
        simpa [northDiskFace_boundary,projection_northCharacteristic,northBoundary] using he'
      · exact False.elim (hnp ((hintersection p hp).mp ha.1))
    · intro he
      subst q
      rfl
  have hleft_boundary_run_collar :
      let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
      let K : Set B := {v | v.1.val=0 ∧ |v.2.val|≤1}
      ∃ E : C(B,↥unitInterval × ↥unitInterval), IsEmbedding E ∧
        (∀ v, (E v).1.val=v.1.val/100 ∧ (E v).2.val=(v.2.val+9)/14) ∧
        E '' K=Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.1.val=0 ∧
          (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7) := by
    dsimp only
    let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let E : C(B,↥unitInterval × ↥unitInterval) := ⟨fun v =>
      (⟨v.1.val/100,⟨by linarith [v.1.property.1],by linarith [v.1.property.2]⟩⟩,
       ⟨(v.2.val+9)/14,⟨by linarith [v.2.property.1],by linarith [v.2.property.2]⟩⟩),by
        apply Continuous.prodMk
        · exact ((continuous_fst.subtype_val.div_const 100).subtype_mk _)
        · exact (((continuous_snd.subtype_val.add continuous_const).div_const 14).subtype_mk _)⟩
    have hEi : Function.Injective E := by
      intro v w h
      have hx := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.1.val) h
      have hy := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.2.val) h
      change v.1.val/100=w.1.val/100 at hx
      change (v.2.val+9)/14=(w.2.val+9)/14 at hy
      apply Prod.ext <;> apply Subtype.ext <;> linarith
    refine ⟨E,(E.continuous.isClosedEmbedding hEi).isEmbedding,fun v => ⟨rfl,rfl⟩,?_⟩
    ext z
    constructor
    · rintro ⟨v,⟨hvx,hvy⟩,rfl⟩
      change v.1.val/100=0 ∧ 4/7≤(v.2.val+9)/14 ∧ (v.2.val+9)/14≤5/7
      have hyl := (abs_le.mp hvy).1
      have hyu := (abs_le.mp hvy).2
      constructor
      · rw [hvx];norm_num
      · constructor <;> linarith
    · rintro ⟨hx,hyl,hyu⟩
      let v : B := (⟨0,by norm_num⟩,⟨14*z.2.val-9,⟨by linarith,by linarith⟩⟩)
      refine ⟨v,⟨rfl,?_⟩,?_⟩
      · change abs (14*z.2.val-9)≤1
        rw [abs_le];constructor <;> linarith
      · apply Prod.ext <;> apply Subtype.ext
        · change 0/100=z.1.val
          rw [hx];norm_num
        · change (14*z.2.val-9+9)/14=z.2.val
          ring
  have actualRunData := actual_same_chart_eighteen_perimeter_intervals
  dsimp only at actualRunData
  obtain ⟨L,H,M0,hL,hH,hML,hMR,Gg,hGg,M3,h3L,h3R,hImages,
    hVertical,hBottomN,hBottomS,hTop,hCorners⟩ := actualRunData
  have hOriginalLeftSource := hVertical (3 : Fin 4) false
  norm_num at hOriginalLeftSource
  obtain ⟨Eleft,hEleft,hEleftFormula,hEleftKernelImage⟩ := hleft_boundary_run_collar
  norm_num at hEleftKernelImage
  have hActualLeftSourcePlacement := hEleftKernelImage.trans hOriginalLeftSource.symm
  have hEleftRelativeInterior :
      ∀ v, (v.1.val<2 ∧ abs v.2.val<2) → Eleft v∈interior (Set.range Eleft) := by
    intro v hv
    let O : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
      z.1.val<(1/50:ℝ) ∧ (1/2:ℝ)<z.2.val ∧ z.2.val<11/14)
    have hO : IsOpen O :=
      (isOpen_lt (continuous_fst.subtype_val) continuous_const).inter
        ((isOpen_lt continuous_const (continuous_snd.subtype_val)).inter
          (isOpen_lt (continuous_snd.subtype_val) continuous_const))
    have hsub : O ⊆ Set.range Eleft := by
      intro z hz
      change z.1.val<1/50 ∧ 1/2<z.2.val ∧ z.2.val<11/14 at hz
      let w : Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2 :=
        (⟨100*z.1.val,⟨by linarith [z.1.property.1],by linarith⟩⟩,
         ⟨14*z.2.val-9,⟨by linarith,by linarith⟩⟩)
      refine ⟨w,?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · rw [(hEleftFormula w).1]
        change 100*z.1.val/100=z.1.val
        ring
      · rw [(hEleftFormula w).2]
        change (14*z.2.val-9+9)/14=z.2.val
        ring
    have hvin : Eleft v∈O := by
      change (Eleft v).1.val<1/50 ∧ 1/2<(Eleft v).2.val ∧ (Eleft v).2.val<11/14
      rw [(hEleftFormula v).1,(hEleftFormula v).2]
      have hyl := (abs_lt.mp hv.2).1
      have hyu := (abs_lt.mp hv.2).2
      constructor
      · linarith [hv.1]
      · constructor <;> linarith
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hO.mem_nhds hvin) hsub
  have hEleftRelativeFrontier :
      ∀ v, Eleft v∈frontier (Set.range Eleft) →
        v.1.val=2 ∨ abs v.2.val=2 := by
    intro v hf
    by_contra hn
    have hxne : v.1.val≠2 := fun h => hn (Or.inl h)
    have hyne : abs v.2.val≠2 := fun h => hn (Or.inr h)
    have hxlt : v.1.val<2 := lt_of_le_of_ne v.1.property.2 hxne
    have hyle : abs v.2.val≤2 := by
      rw [abs_le]
      exact v.2.property
    have hylt : abs v.2.val<2 := lt_of_le_of_ne hyle hyne
    have hni : Eleft v∉interior (Set.range Eleft) := hf.2
    exact hni (hEleftRelativeInterior v ⟨hxlt,hylt⟩)
  have hCutDiskBoundaryCollapse :
      let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
      let K : Set B := {v | v.1.val=0 ∧ abs v.2.val≤1}
      ∀ E : C(B,↥unitInterval × ↥unitInterval), IsEmbedding E →
        (∀ v, E v∈frontier (Set.range E) → v.1.val=2 ∨ abs v.2.val=2) →
        ∃ G : C(↥unitInterval × ↥unitInterval,↥unitInterval × ↥unitInterval),
          (∀ z, z∉interior (Set.range E) → G z=z) ∧ Function.Surjective G ∧
          (∀ z w, G z=G w ↔ z=w ∨ (z∈E '' K ∧ w∈E '' K)) ∧
          (∃ h : Quotient (Relation.EqvGen.setoid
            (fun z w : ↥unitInterval × ↥unitInterval => z∈E '' K ∧ w∈E '' K)) ≃ₜ
              (↥unitInterval × ↥unitInterval), ∀ z, h (Quotient.mk _ z)=G z) ∧
          (∀ v : B, ∃ w : B, G (E v)=E w ∧ w.1.val=v.1.val) := by
    dsimp only
    intro E hE hEF
    classical
    let Xboundary := ↥unitInterval × ↥unitInterval
    let D := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let K : Set D := {v | v.1.val=0 ∧ abs v.2.val≤1}
    obtain ⟨F,hFx,hFs,hFker,hFboundary⟩ := hboundary_half_rectangle
    let A := E '' K
    have hEK : E '' K=A := rfl
    have hEKexact : E '' K=A := hEK
    let R := Set.range E
    have hRc : IsClosed R := (isCompact_range E.continuous).isClosed
    let inv : R → D := hE.toHomeomorph.symm
    have hinv (v : D) : inv ⟨E v,⟨v,rfl⟩⟩=v := hE.toHomeomorph.symm_apply_apply v
    have hEinv (z : Xboundary) (hz : z∈R) : E (inv ⟨z,hz⟩)=z :=
      congrArg Subtype.val (hE.toHomeomorph.apply_symm_apply ⟨z,hz⟩)
    let inner : C(R,Xboundary) := ⟨fun z => E (F (inv z)),
      E.continuous.comp (F.continuous.comp hE.toHomeomorph.symm.continuous)⟩
    let g : Xboundary → Xboundary := Function.extend Subtype.val inner id
    have hgin (z : Xboundary) (hz : z∈R) : g z=E (F (inv ⟨z,hz⟩)) :=
      Subtype.val_injective.extend_apply _ _ ⟨z,hz⟩
    have hgc : ContinuousOn g R := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : R.domRestrict g=inner := funext (fun z => hgin z.val z.property)
      rw [heq];exact inner.continuous
    have hboundary (z : Xboundary) (hz : z∈frontier R) : g z=z := by
      rw [hRc.frontier_eq] at hz
      let v := inv ⟨z,hz.1⟩
      have hev : E v=z := hEinv z hz.1
      have hb : v.1.val=2 ∨ abs v.2.val=2 := by
        apply hEF v
        rw [hev,hRc.frontier_eq]
        exact hz
      rw [hgin z hz.1]
      change E (F v)=z
      rw [hFboundary v hb,hev]
    let G : C(Xboundary,Xboundary) := ⟨R.piecewise g id,
      continuous_piecewise hboundary (by rw [hRc.closure_eq];exact hgc) continuous_id.continuousOn⟩
    have hGpin (v : D) : G (E v)=E (F v) := by
      change R.piecewise g id (E v)=_
      rw [Set.piecewise_eq_of_mem R g id (show E v∈R from ⟨v,rfl⟩)]
      rw [hgin (E v) ⟨v,rfl⟩,hinv]
    have hGout (z : Xboundary) (hz : z∉R) : G z=z :=
      Set.piecewise_eq_of_notMem R g id hz
    have hGsupport (z : Xboundary) (hz : z∉interior R) : G z=z := by
      by_cases hr : z∈R
      · have hfr : z∈frontier R := by rw [hRc.frontier_eq];exact ⟨hr,hz⟩
        change R.piecewise g id z=z
        rw [Set.piecewise_eq_of_mem R g id hr,hboundary z hfr]
      · exact hGout z hr
    have hAsub : A⊆R := by
      rw [←hEKexact]
      rintro z ⟨v,hv,rfl⟩;exact ⟨v,rfl⟩
    have hEA (v : D) : E v∈A ↔ v∈K := by
      rw [←hEKexact]
      constructor
      · rintro ⟨w,hw,he⟩
        exact hE.injective he ▸ hw
      · intro hv;exact ⟨v,hv,rfl⟩
    have hGsurj : Function.Surjective G := by
      intro z
      by_cases hz : z∈R
      · obtain ⟨v,rfl⟩ := hz
        obtain ⟨u,hu⟩ := hFs v
        exact ⟨E u,(hGpin u).trans (congrArg E hu)⟩
      · exact ⟨z,hGout z hz⟩
    have hGker (z w : Xboundary) : G z=G w ↔ z=w ∨ (z∈A ∧ w∈A) := by
      by_cases hz : z∈R
      · obtain ⟨v,rfl⟩ := hz
        by_cases hw : w∈R
        · obtain ⟨u,rfl⟩ := hw
          rw [hGpin,hGpin]
          constructor
          · intro he
            rcases (hFker v u).mp (hE.injective he) with he|he
            · exact Or.inl (congrArg E he)
            · exact Or.inr ⟨(hEA v).mpr he.1,(hEA u).mpr he.2⟩
          · rintro (he|he)
            · exact congrArg (fun x => E (F x)) (hE.injective he)
            · exact congrArg E ((hFker v u).mpr (Or.inr ⟨(hEA v).mp he.1,(hEA u).mp he.2⟩))
        · rw [hGpin,hGout w hw]
          constructor
          · intro he
            exact False.elim (hw (he ▸ Set.mem_range_self (F v)))
          · rintro (he|he)
            · exact False.elim (hw (he ▸ Set.mem_range_self v))
            · exact False.elim (hw (hAsub he.2))
      · by_cases hw : w∈R
        · obtain ⟨u,rfl⟩ := hw
          rw [hGout z hz,hGpin]
          constructor
          · intro he
            exact False.elim (hz (he.symm ▸ Set.mem_range_self (F u)))
          · rintro (he|he)
            · exact False.elim (hz (he.symm ▸ Set.mem_range_self u))
            · exact False.elim (hz (hAsub he.1))
        · rw [hGout z hz,hGout w hw]
          constructor
          · exact Or.inl
          · rintro (he|he)
            · exact he
            · exact False.elim (hz (hAsub he.1))
    let Q := Quotient (Relation.EqvGen.setoid (fun z w : Xboundary => z∈A ∧ w∈A))
    have hrespect (z w : Xboundary) (h : Relation.EqvGen (fun z w : Xboundary => z∈A ∧ w∈A) z w) : G z=G w := by
      induction h with
      | rel z w h => exact (hGker z w).mpr (Or.inr h)
      | refl z => rfl
      | symm z w h ih => exact ih.symm
      | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    let q : Q → Xboundary := Quotient.lift G hrespect
    have hqc : Continuous q := G.continuous.quotient_lift _
    have hqi : Function.Injective q := by
      intro x y he
      induction x using Quotient.inductionOn with
      | _ z =>
        induction y using Quotient.inductionOn with
        | _ w =>
          change G z=G w at he
          rcases (hGker z w).mp he with he|he
          · exact congrArg (Quotient.mk _) he
          · exact Quotient.sound (Relation.EqvGen.rel z w he)
    have hqs : Function.Surjective q := by
      intro z
      obtain ⟨w,hw⟩ := hGsurj z
      exact ⟨Quotient.mk _ w,hw⟩
    let e := Equiv.ofBijective q ⟨hqi,hqs⟩
    let Hq : Q ≃ₜ Xboundary := (show Continuous (e : Q → Xboundary) from hqc).homeoOfEquivCompactToT2
    refine ⟨G,hGsupport,hGsurj,hGker,⟨Hq,fun _ => rfl⟩,?_⟩
    intro v
    exact ⟨F v,hGpin v,hFx v⟩
  let Bleft := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
  let Kleft : Set Bleft := {v | v.1.val=0 ∧ abs v.2.val≤1}
  let Aleft := Eleft '' Kleft
  obtain ⟨Fleft,hFleftx,hFleftsurj,hFleftker,hFleftboundary⟩ := hboundary_half_rectangle
  have hActualLeftRunGlobalCollapse :
      ∃ G : C(↥unitInterval × ↥unitInterval,↥unitInterval × ↥unitInterval),
        Function.Surjective G ∧
        (∀ z w, G z=G w ↔ z=w ∨ (z∈Aleft ∧ w∈Aleft)) ∧
        ∃ h : Quotient (Relation.EqvGen.setoid
          (fun z w : ↥unitInterval × ↥unitInterval => z∈Aleft ∧ w∈Aleft)) ≃ₜ
            (↥unitInterval × ↥unitInterval), ∀ z, h (Quotient.mk _ z)=G z := by
    obtain ⟨G,hSupport,hSurj,hKer,hHomeo,hAxis⟩ := hCutDiskBoundaryCollapse Eleft hEleft hEleftRelativeFrontier
    exact ⟨G,hSurj,hKer,hHomeo⟩
  have hright_boundary_run_collar :
      let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
      let K : Set B := {v | v.1.val=0 ∧ |v.2.val|≤1}
      ∃ E : C(B,↥unitInterval × ↥unitInterval), IsEmbedding E ∧
        (∀ v, (E v).1.val=1-v.1.val/100 ∧ (E v).2.val=(v.2.val+5)/14) ∧
        E '' K=Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.1.val=1 ∧
          (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7) := by
    dsimp only
    let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let E : C(B,↥unitInterval × ↥unitInterval) := ⟨fun v =>
      (⟨1-v.1.val/100,⟨by linarith [v.1.property.1,v.1.property.2],by linarith [v.1.property.1,v.1.property.2]⟩⟩,
       ⟨(v.2.val+5)/14,⟨by linarith [v.2.property.1],by linarith [v.2.property.2]⟩⟩),by
        apply Continuous.prodMk
        · exact ((continuous_const.sub (continuous_fst.subtype_val.div_const 100)).subtype_mk _)
        · exact (((continuous_snd.subtype_val.add continuous_const).div_const 14).subtype_mk _)⟩
    have hEi : Function.Injective E := by
      intro v w h
      have hx := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.1.val) h
      have hy := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.2.val) h
      change 1-v.1.val/100=1-w.1.val/100 at hx
      change (v.2.val+5)/14=(w.2.val+5)/14 at hy
      apply Prod.ext <;> apply Subtype.ext <;> linarith
    refine ⟨E,(E.continuous.isClosedEmbedding hEi).isEmbedding,fun v => ⟨rfl,rfl⟩,?_⟩
    ext z
    constructor
    · rintro ⟨v,⟨hvx,hvy⟩,rfl⟩
      change 1-v.1.val/100=1 ∧ 2/7≤(v.2.val+5)/14 ∧ (v.2.val+5)/14≤3/7
      have hyl := (abs_le.mp hvy).1
      have hyu := (abs_le.mp hvy).2
      constructor
      · rw [hvx];norm_num
      · constructor <;> linarith
    · rintro ⟨hx,hyl,hyu⟩
      let v : B := (⟨0,by norm_num⟩,⟨14*z.2.val-5,⟨by linarith,by linarith⟩⟩)
      refine ⟨v,⟨rfl,?_⟩,?_⟩
      · change abs (14*z.2.val-5)≤1
        rw [abs_le];constructor <;> linarith
      · apply Prod.ext <;> apply Subtype.ext
        · change 1-0/100=z.1.val
          rw [hx];norm_num
        · change (14*z.2.val-5+5)/14=z.2.val
          ring
  obtain ⟨Eright,hEright,hErightFormula,hErightKernelImage⟩ := hright_boundary_run_collar
  have hOriginalRightSource := hVertical (0 : Fin 4) true
  norm_num at hOriginalRightSource hErightKernelImage
  have hActualRightSourcePlacement := hErightKernelImage.trans hOriginalRightSource.symm
  have hErightRelativeInterior :
      ∀ v, (v.1.val<2 ∧ abs v.2.val<2) → Eright v∈interior (Set.range Eright) := by
    intro v hv
    let O : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
      (49/50:ℝ)<z.1.val ∧ (3/14:ℝ)<z.2.val ∧ z.2.val<1/2)
    have hO : IsOpen O :=
      (isOpen_lt continuous_const (continuous_fst.subtype_val)).inter
        ((isOpen_lt continuous_const (continuous_snd.subtype_val)).inter
          (isOpen_lt (continuous_snd.subtype_val) continuous_const))
    have hsub : O ⊆ Set.range Eright := by
      intro z hz
      change 49/50<z.1.val ∧ 3/14<z.2.val ∧ z.2.val<1/2 at hz
      let w : Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2 :=
        (⟨100*(1-z.1.val),⟨by linarith [z.1.property.2],by linarith⟩⟩,
         ⟨14*z.2.val-5,⟨by linarith,by linarith⟩⟩)
      refine ⟨w,?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · rw [(hErightFormula w).1]
        change 1-100*(1-z.1.val)/100=z.1.val
        ring
      · rw [(hErightFormula w).2]
        change (14*z.2.val-5+5)/14=z.2.val
        ring
    have hvin : Eright v∈O := by
      change 49/50<(Eright v).1.val ∧ 3/14<(Eright v).2.val ∧ (Eright v).2.val<1/2
      rw [(hErightFormula v).1,(hErightFormula v).2]
      have hyl := (abs_lt.mp hv.2).1
      have hyu := (abs_lt.mp hv.2).2
      constructor
      · linarith [hv.1]
      · constructor <;> linarith
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hO.mem_nhds hvin) hsub
  have hErightRelativeFrontier :
      ∀ v, Eright v∈frontier (Set.range Eright) →
        v.1.val=2 ∨ abs v.2.val=2 := by
    intro v hf
    by_contra hn
    have hxne : v.1.val≠2 := fun h => hn (Or.inl h)
    have hyne : abs v.2.val≠2 := fun h => hn (Or.inr h)
    have hxlt : v.1.val<2 := lt_of_le_of_ne v.1.property.2 hxne
    have hyle : abs v.2.val≤2 := by
      rw [abs_le]
      exact v.2.property
    have hylt : abs v.2.val<2 := lt_of_le_of_ne hyle hyne
    have hni : Eright v∉interior (Set.range Eright) := hf.2
    exact hni (hErightRelativeInterior v ⟨hxlt,hylt⟩)
  have hActualRightRunGlobalCollapse :=
    hCutDiskBoundaryCollapse Eright hEright hErightRelativeFrontier
  have hbottom_boundary_run_collar :
      let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
      let K : Set B := {v | v.1.val=0 ∧ abs v.2.val≤1}
      ∃ E : C(B,↥unitInterval × ↥unitInterval), IsEmbedding E ∧
        (∀ v, (E v).1.val=(v.2.val+7)/12 ∧ (E v).2.val=v.1.val/100) ∧
        E '' K=Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.2.val=0 ∧
          (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3) := by
    dsimp only
    let B := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let E : C(B,↥unitInterval × ↥unitInterval) := ⟨fun v =>
      (⟨(v.2.val+7)/12,⟨by linarith [v.2.property.1],by linarith [v.2.property.2]⟩⟩,
       ⟨v.1.val/100,⟨by linarith [v.1.property.1],by linarith [v.1.property.2]⟩⟩),by
        exact (((continuous_snd.subtype_val.add continuous_const).div_const 12).subtype_mk _).prodMk
          ((continuous_fst.subtype_val.div_const 100).subtype_mk _)⟩
    have hEi : Function.Injective E := by
      intro v w h
      have hx := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.1.val) h
      have hy := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.2.val) h
      change (v.2.val+7)/12=(w.2.val+7)/12 at hx
      change v.1.val/100=w.1.val/100 at hy
      apply Prod.ext <;> apply Subtype.ext <;> linarith
    refine ⟨E,(E.continuous.isClosedEmbedding hEi).isEmbedding,fun v => ⟨rfl,rfl⟩,?_⟩
    ext z
    constructor
    · rintro ⟨v,⟨hvx,hvy⟩,rfl⟩
      change v.1.val/100=0 ∧ 1/2≤(v.2.val+7)/12 ∧ (v.2.val+7)/12≤2/3
      have hyl := (abs_le.mp hvy).1
      have hyu := (abs_le.mp hvy).2
      constructor
      · rw [hvx];norm_num
      · constructor <;> linarith
    · rintro ⟨hy,hxl,hxu⟩
      let v : B := (⟨0,by norm_num⟩,⟨12*z.1.val-7,⟨by linarith,by linarith⟩⟩)
      refine ⟨v,⟨rfl,?_⟩,?_⟩
      · change abs (12*z.1.val-7)≤1
        rw [abs_le];constructor <;> linarith
      · apply Prod.ext <;> apply Subtype.ext
        · change (12*z.1.val-7+7)/12=z.1.val
          ring
        · change 0/100=z.2.val
          rw [hy];norm_num
  obtain ⟨Ebottom,hEbottom,hEbottomFormula,hEbottomKernelImage⟩ := hbottom_boundary_run_collar
  have hBottomSRaw := hBottomS
  norm_num at hBottomS hEbottomKernelImage
  have hActualBottomSourcePlacement := hEbottomKernelImage.trans hBottomS.symm
  have hEbottomRelativeInterior :
      ∀ v, (v.1.val<2 ∧ abs v.2.val<2) → Ebottom v∈interior (Set.range Ebottom) := by
    intro v hv
    let O : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
      z.2.val<(1/50:ℝ) ∧ (5/12:ℝ)<z.1.val ∧ z.1.val<3/4)
    have hO : IsOpen O :=
      (isOpen_lt (continuous_snd.subtype_val) continuous_const).inter
        ((isOpen_lt continuous_const (continuous_fst.subtype_val)).inter
          (isOpen_lt (continuous_fst.subtype_val) continuous_const))
    have hsub : O ⊆ Set.range Ebottom := by
      intro z hz
      change z.2.val<1/50 ∧ 5/12<z.1.val ∧ z.1.val<3/4 at hz
      let w : Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2 :=
        (⟨100*z.2.val,⟨by linarith [z.2.property.1],by linarith⟩⟩,
         ⟨12*z.1.val-7,⟨by linarith,by linarith⟩⟩)
      refine ⟨w,?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · rw [(hEbottomFormula w).1]
        change (12*z.1.val-7+7)/12=z.1.val
        ring
      · rw [(hEbottomFormula w).2]
        change 100*z.2.val/100=z.2.val
        ring
    have hvin : Ebottom v∈O := by
      change (Ebottom v).2.val<1/50 ∧ 5/12<(Ebottom v).1.val ∧ (Ebottom v).1.val<3/4
      rw [(hEbottomFormula v).1,(hEbottomFormula v).2]
      have hyl := (abs_lt.mp hv.2).1
      have hyu := (abs_lt.mp hv.2).2
      constructor
      · linarith [hv.1]
      · constructor <;> linarith
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hO.mem_nhds hvin) hsub
  have hEbottomRelativeFrontier :
      ∀ v, Ebottom v∈frontier (Set.range Ebottom) →
        v.1.val=2 ∨ abs v.2.val=2 := by
    intro v hf
    by_contra hn
    have hxne : v.1.val≠2 := fun h => hn (Or.inl h)
    have hyne : abs v.2.val≠2 := fun h => hn (Or.inr h)
    have hxlt : v.1.val<2 := lt_of_le_of_ne v.1.property.2 hxne
    have hyle : abs v.2.val≤2 := abs_le.mpr v.2.property
    have hylt : abs v.2.val<2 := lt_of_le_of_ne hyle hyne
    exact hf.2 (hEbottomRelativeInterior v ⟨hxlt,hylt⟩)
  have hActualBottomRunGlobalCollapse :=
    hCutDiskBoundaryCollapse Ebottom hEbottom hEbottomRelativeFrontier
  let θ (t : ℝ) := (1+t/100+(49/100)*min 1 (max (-1) t))/2
  have hθc : Continuous θ := by dsimp [θ];fun_prop
  have hθi : StrictMono θ := by
    intro t u htu
    have hm : min (1:ℝ) (max (-1) t)≤ min 1 (max (-1) u) :=
      min_le_min le_rfl (max_le_max le_rfl htu.le)
    dsimp [θ];linarith
  have hθm : θ (-2)=(49/200:ℝ) := by norm_num [θ]
  have hθp : θ 2=(151/200:ℝ) := by norm_num [θ]
  have hθcore (t : ℝ) (ht : abs t≤1) : θ t=(t+2)/4 := by
    have ht' := abs_le.mp ht
    dsimp [θ]
    rw [max_eq_right ht'.1,min_eq_right ht'.2]
    ring
  have hθrange : θ '' Icc (-2:ℝ) 2=Icc (49/200:ℝ) (151/200) := by
    rw [hθc.image_Icc_of_strictMono hθi,hθm,hθp]
  have hθbound (t : Set.Icc (-2:ℝ) 2) : 49/200≤θ t.val ∧ θ t.val≤151/200 := by
    constructor
    · rw [←hθm];exact hθi.monotone t.property.1
    · rw [←hθp];exact hθi.monotone t.property.2
  let Bstd := Set.Icc (0:ℝ) 2 × Set.Icc (-2:ℝ) 2
  let Kstd : Set Bstd := {v | v.1.val=0 ∧ abs v.2.val≤1}
  let Estd : C(Bstd,↥unitInterval × ↥unitInterval) := ⟨fun v =>
    (⟨1-v.1.val/100,⟨by linarith [v.1.property.2],by linarith [v.1.property.1]⟩⟩,
     ⟨θ v.2.val,⟨by linarith [(hθbound v.2).1],by linarith [(hθbound v.2).2]⟩⟩),by
      exact ((continuous_const.sub (continuous_fst.subtype_val.div_const 100)).subtype_mk _).prodMk
        ((hθc.comp continuous_snd.subtype_val).subtype_mk _)⟩
  have hEstdFormula (v : Bstd) : (Estd v).1.val=1-v.1.val/100 ∧ (Estd v).2.val=θ v.2.val := ⟨rfl,rfl⟩
  have hEstd : IsEmbedding Estd := by
    apply IsClosedEmbedding.isEmbedding
    apply Estd.continuous.isClosedEmbedding
    intro v w h
    have hx := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.1.val) h
    have hy := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.2.val) h
    apply Prod.ext
    · apply Subtype.ext
      change 1-v.1.val/100=1-w.1.val/100 at hx
      linarith
    · apply Subtype.ext
      exact hθi.injective hy
  have hEstdKernelImage : Estd '' Kstd=Set.ofPred (fun z : ↥unitInterval × ↥unitInterval =>
      z.1.val=1 ∧ (1/4:ℝ)≤z.2.val ∧ z.2.val≤3/4) := by
    ext z
    constructor
    · rintro ⟨v,hv,rfl⟩
      change v.1.val=0 ∧ abs v.2.val≤1 at hv
      change 1-v.1.val/100=1 ∧ 1/4≤θ v.2.val ∧ θ v.2.val≤3/4
      rw [hv.1,hθcore v.2.val hv.2]
      have hb := abs_le.mp hv.2
      constructor
      · norm_num
      · constructor <;> linarith
    · rintro ⟨hx,hy0,hy1⟩
      let v : Bstd := (⟨0,by norm_num⟩,⟨4*z.2.val-2,⟨by linarith,by linarith⟩⟩)
      have hv : abs v.2.val≤1 := by change abs (4*z.2.val-2)≤1;rw [abs_le];constructor <;> linarith
      refine ⟨v,⟨rfl,hv⟩,?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · change 1-0/100=z.1.val
        rw [hx];norm_num
      · change θ v.2.val=z.2.val
        rw [hθcore v.2.val hv]
        dsimp [v];ring
  have hEstdRangeBounds (z : ↥unitInterval × ↥unitInterval) (hz : z∈Set.range Estd) :
      (49/50:ℝ)≤z.1.val ∧ (49/200:ℝ)≤z.2.val ∧ z.2.val≤151/200 := by
    obtain ⟨v,rfl⟩ := hz
    change 49/50≤1-v.1.val/100 ∧ 49/200≤θ v.2.val ∧ θ v.2.val≤151/200
    exact ⟨by linarith [v.1.property.2],hθbound v.2⟩
  have hEstdRelativeInterior :
      ∀ v, (v.1.val<2 ∧ abs v.2.val<2) → Estd v∈interior (Set.range Estd) := by
    intro v hv
    let O : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
      (49/50:ℝ)<z.1.val ∧ (49/200:ℝ)<z.2.val ∧ z.2.val<151/200)
    have hO : IsOpen O :=
      (isOpen_lt continuous_const (continuous_fst.subtype_val)).inter
        ((isOpen_lt continuous_const (continuous_snd.subtype_val)).inter
          (isOpen_lt (continuous_snd.subtype_val) continuous_const))
    have hsub : O ⊆ Set.range Estd := by
      intro z hz
      change 49/50<z.1.val ∧ 49/200<z.2.val ∧ z.2.val<151/200 at hz
      have hy : z.2.val∈θ '' Icc (-2:ℝ) 2 := by rw [hθrange];exact ⟨hz.2.1.le,hz.2.2.le⟩
      obtain ⟨y,hy,hθy⟩ := hy
      let w : Bstd := (⟨100*(1-z.1.val),⟨by linarith [z.1.property.2],by linarith⟩⟩,⟨y,hy⟩)
      refine ⟨w,?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · change 1-100*(1-z.1.val)/100=z.1.val
        ring
      · exact hθy
    have hvin : Estd v∈O := by
      change 49/50<1-v.1.val/100 ∧ 49/200<θ v.2.val ∧ θ v.2.val<151/200
      have hy := abs_lt.mp hv.2
      refine ⟨by linarith [hv.1],?_,?_⟩
      · rw [←hθm];exact hθi hy.1
      · rw [←hθp];exact hθi hy.2
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (hO.mem_nhds hvin) hsub
  have hEstdRelativeFrontier :
      ∀ v, Estd v∈frontier (Set.range Estd) → v.1.val=2 ∨ abs v.2.val=2 := by
    intro v hf
    by_contra hn
    have hxne : v.1.val≠2 := fun h => hn (Or.inl h)
    have hyne : abs v.2.val≠2 := fun h => hn (Or.inr h)
    exact hf.2 (hEstdRelativeInterior v
      ⟨lt_of_le_of_ne v.1.property.2 hxne,
       lt_of_le_of_ne (abs_le.mpr v.2.property) hyne⟩)
  have hConjugatedBoundaryCollar :
      ∀ H : (↥unitInterval × ↥unitInterval) ≃ₜ (↥unitInterval × ↥unitInterval),
      ∃ E : C(Bstd,↥unitInterval × ↥unitInterval), IsEmbedding E ∧
        (∀ v, E v=H.symm (Estd v)) ∧
        E '' Kstd=H.symm '' Set.ofPred (fun z : ↥unitInterval × ↥unitInterval =>
          z.1.val=1 ∧ (1/4:ℝ)≤z.2.val ∧ z.2.val≤3/4) ∧
        (∀ v, E v∈frontier (Set.range E) → v.1.val=2 ∨ abs v.2.val=2) ∧
        (∀ z, z∈Set.range E → H z∈Set.range Estd) := by
    intro H
    let E : C(Bstd,↥unitInterval × ↥unitInterval) := (⟨H.symm,H.symm.continuous⟩ : C(↥unitInterval × ↥unitInterval,↥unitInterval × ↥unitInterval)).comp Estd
    have hE : IsEmbedding E := H.symm.isEmbedding.comp hEstd
    have hR : Set.range E=H ⁻¹' Set.range Estd := by
      ext z
      constructor
      · rintro ⟨v,rfl⟩
        change H (H.symm (Estd v))∈Set.range Estd
        rw [H.apply_symm_apply]
        exact Set.mem_range_self v
      · rintro ⟨v,hv⟩
        refine ⟨v,?_⟩
        change H.symm (Estd v)=z
        rw [hv,H.symm_apply_apply]
    refine ⟨E,hE,fun v => rfl,?_,?_,?_⟩
    · change (H.symm ∘ Estd) '' Kstd=_
      rw [Set.image_comp,hEstdKernelImage]
    · intro v hf
      rw [hR,←H.preimage_frontier] at hf
      change H (H.symm (Estd v))∈frontier (Set.range Estd) at hf
      rw [H.apply_symm_apply] at hf
      exact hEstdRelativeFrontier v hf
    · intro z hz
      rw [hR] at hz
      exact hz
  have corner0Data := actual_corner_boundary_run_radial_normalization (0:Fin 2)
  have corner1Data := actual_corner_boundary_run_radial_normalization (1:Fin 2)
  dsimp only at corner0Data corner1Data
  obtain ⟨Hcorner0,hHcorner0Formula,hHcorner0Image⟩ := corner0Data
  obtain ⟨Hcorner1,hHcorner1Formula,hHcorner1Image⟩ := corner1Data
  let Pcorner0 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
    (z.1.val=0 ∧ 6/7≤z.2.val ∧ z.2.val≤1))
  let Pcorner1 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    (z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
    (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1))
  obtain ⟨Ecorner0,hEcorner0,hEcorner0Pin,hEcorner0Image,hEcorner0Frontier,hEcorner0Range⟩ :=
    hConjugatedBoundaryCollar Hcorner0
  obtain ⟨Ecorner1,hEcorner1,hEcorner1Pin,hEcorner1Image,hEcorner1Frontier,hEcorner1Range⟩ :=
    hConjugatedBoundaryCollar Hcorner1
  have hActualCorner0KernelImage : Ecorner0 '' Kstd=Pcorner0 := by
    rw [hEcorner0Image,←hHcorner0Image]
    exact Hcorner0.toEquiv.symm_image_image _
  have hActualCorner1KernelImage : Ecorner1 '' Kstd=Pcorner1 := by
    rw [hEcorner1Image,←hHcorner1Image]
    exact Hcorner1.toEquiv.symm_image_image _
  have hOriginalCorner0Source := hCorners false true
  dsimp [Pcorner0] at hActualCorner0KernelImage
  norm_num at hOriginalCorner0Source hActualCorner0KernelImage
  have hActualCorner0SourcePlacement := hActualCorner0KernelImage.trans hOriginalCorner0Source.symm
  have hActualCorner0RunGlobalCollapse :=
    hCutDiskBoundaryCollapse Ecorner0 hEcorner0 hEcorner0Frontier
  have hActualCorner1RunGlobalCollapse :=
    hCutDiskBoundaryCollapse Ecorner1 hEcorner1 hEcorner1Frontier
  let R0norm : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
    fun a b => ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (0:Fin 6) p ∧
      a=Sum.inl (diskBoundaryPoint p hp) ∧ b=Sum.inr (diskBoundaryPoint p hp)
  let Q0norm := Quotient (Relation.EqvGen.setoid R0norm)
  let R1norm : (Q0norm ⊕ Q0norm) → (Q0norm ⊕ Q0norm) → Prop := fun a b =>
    ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (1:Fin 6) p ∧
      a=Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inl (diskBoundaryPoint p hp))) ∧
      b=Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inr (diskBoundaryPoint p hp)))
  let q0norm (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0norm)
    (if sheet then Sum.inr v else Sum.inl v)
  let qFacenorm (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1norm)
    (if right then Sum.inr (q0norm (!sheet) v) else Sum.inl (q0norm sheet v))
  let OccNorm (right sheet : Bool) (i : Fin 6) : Set (Quotient (Relation.EqvGen.setoid R1norm)) :=
    Set.ofPred (fun q => ∃ p : Sphere, ∃ hp : height p=0,
      closedArcSector i p ∧ q=qFacenorm right sheet (diskBoundaryPoint p hp))
  have hOccST1 : M3 '' OccNorm false true 1=
      Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1/2) := by
    have h := hTop (0:Fin 2) false
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false] at h
    exact h
  have hOccNT1 : M3 '' OccNorm true true 1=
      Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.2.val=1 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3) := by
    have h := hTop (0:Fin 2) true
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false] at h
    exact h
  have hOccNT2 : M3 '' OccNorm true true 2=
      Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.2.val=1 ∧ (2/3:ℝ)≤z.1.val ∧ z.1.val≤7/10) := by
    have h := hTop (1:Fin 2) true
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false] at h
    exact h
  have hOccNT3 : M3 '' OccNorm true true 3=
      Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => (z.2.val=1 ∧ (7/10:ℝ)≤z.1.val ∧ z.1.val≤1) ∨ (z.1.val=1 ∧ (6/7:ℝ)≤z.2.val ∧ z.2.val≤1)) := by
    have h := hCorners true true
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false] at h
    exact h
  have hOccNT4 : M3 '' OccNorm true true 4=
      Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.1.val=1 ∧ (5/7:ℝ)≤z.2.val ∧ z.2.val≤6/7) := by
    have h := hVertical (2:Fin 4) true
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false] at h
    exact h
  have hOccNT5 : M3 '' OccNorm true true 5=
      Set.ofPred (fun z : ↥unitInterval × ↥unitInterval => z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7) := by
    have h := hVertical (3:Fin 4) true
    norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, ite_true, ite_false] at h
    exact h
  let UbigCorner := OccNorm false true 1 ∪ OccNorm true true 1 ∪
    OccNorm true true 2 ∪ OccNorm true true 3 ∪ OccNorm true true 4 ∪ OccNorm true true 5
  have hActualBigCornerSourceImage : M3 '' UbigCorner=Pcorner1 := by
    dsimp only [UbigCorner]
    simp only [Set.image_union,hOccST1,hOccNT1,hOccNT2,hOccNT3,hOccNT4,hOccNT5]
    ext z
    simp only [Set.mem_union,Set.mem_ofPred_eq]
    dsimp only [Pcorner1,Set.ofPred] at ⊢
    constructor
    · intro hz
      rcases hz with (((((hz|hz)|hz)|hz)|hz)|hz)
      · rcases hz with ⟨hy,hl,hu⟩
        exact Or.inl ⟨hy,hl,by linarith⟩
      · rcases hz with ⟨hy,hl,hu⟩
        exact Or.inl ⟨hy,by linarith,by linarith⟩
      · rcases hz with ⟨hy,hl,hu⟩
        exact Or.inl ⟨hy,by linarith,by linarith⟩
      · rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
        · exact Or.inl ⟨hy,by linarith,hu⟩
        · exact Or.inr ⟨hx,by linarith,hu⟩
      · rcases hz with ⟨hx,hl,hu⟩
        exact Or.inr ⟨hx,by linarith,by linarith⟩
      · rcases hz with ⟨hx,hl,hu⟩
        exact Or.inr ⟨hx,hl,by linarith⟩
    · rintro (⟨hy,hl,hu⟩|⟨hx,hl,hu⟩)
      · by_cases h1 : z.1.val≤(1/2:ℝ)
        · have hc : z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1/2 := ⟨hy,hl,h1⟩
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))
        · by_cases h2 : z.1.val≤(2/3:ℝ)
          · have hc : z.2.val=1 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3 := ⟨hy,by linarith,h2⟩
            exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))
          · by_cases h3 : z.1.val≤(7/10:ℝ)
            · have hc : z.2.val=1 ∧ (2/3:ℝ)≤z.1.val ∧ z.1.val≤7/10 := ⟨hy,by linarith,h3⟩
              exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
            · have hc : z.2.val=1 ∧ (7/10:ℝ)≤z.1.val ∧ z.1.val≤1 := ⟨hy,by linarith,hu⟩
              exact Or.inl (Or.inl (Or.inr (Or.inl hc)))
      · by_cases h1 : z.2.val≤(5/7:ℝ)
        · have hc : z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7 := ⟨hx,hl,h1⟩
          exact Or.inr hc
        · by_cases h2 : z.2.val≤(6/7:ℝ)
          · have hc : z.1.val=1 ∧ (5/7:ℝ)≤z.2.val ∧ z.2.val≤6/7 := ⟨hx,by linarith,h2⟩
            exact Or.inl (Or.inr hc)
          · have hc : z.1.val=1 ∧ (6/7:ℝ)≤z.2.val ∧ z.2.val≤1 := ⟨hx,by linarith,hu⟩
            exact Or.inl (Or.inl (Or.inr (Or.inr hc)))
  have hCorner0Scalar (z : ↥unitInterval × ↥unitInterval) :
      ∃ c : ℝ, 0≤c ∧
      (Hcorner0 z).1.val=(c*(-(10/3)*(z.1.val-3/10)+7*(z.2.val-6/7))+1)/2 ∧
      (Hcorner0 z).2.val=(c*(5/3*(z.1.val-3/10)+7/2*(z.2.val-6/7))+1)/2 := by
    let Lc : (ℝ × ℝ) → (ℝ × ℝ) := fun u => (-(10/3)*u.1+7*u.2,5/3*u.1+7/2*u.2)
    let sc := Lc '' (Icc (-(3/10):ℝ) (1-3/10) ×ˢ Icc (-(6/7):ℝ) (1-6/7))
    let w := Lc (z.1.val-3/10,z.2.val-6/7)
    let c := gauge sc w / gauge (closedBall (0:ℝ × ℝ) 1) w
    have hf := hHcorner0Formula z
    simp only [ite_true] at hf
    change ((Hcorner0 z).1.val,(Hcorner0 z).2.val)=
      (((c • w).1+1)/2,((c • w).2+1)/2) at hf
    refine ⟨c,div_nonneg (gauge_nonneg w) (gauge_nonneg w),?_,?_⟩
    · exact congrArg Prod.fst hf
    · exact congrArg Prod.snd hf
  have hCorner1Scalar (z : ↥unitInterval × ↥unitInterval) :
      ∃ c : ℝ, 0≤c ∧
      (Hcorner1 z).1.val=(c*(3/2*(z.1.val-1/3)+7/3*(z.2.val-4/7))+1)/2 ∧
      (Hcorner1 z).2.val=(c*(3/4*(z.1.val-1/3)-7/6*(z.2.val-4/7))+1)/2 := by
    let Lc : (ℝ × ℝ) → (ℝ × ℝ) := fun u => (3/2*u.1+7/3*u.2,3/4*u.1-7/6*u.2)
    let sc := Lc '' (Icc (-(1/3):ℝ) (1-1/3) ×ˢ Icc (-(4/7):ℝ) (1-4/7))
    let w := Lc (z.1.val-1/3,z.2.val-4/7)
    let c := gauge sc w / gauge (closedBall (0:ℝ × ℝ) 1) w
    have hf := hHcorner1Formula z
    have hk : (1:Fin 2)≠0 := by decide
    simp only [hk,ite_false] at hf
    change ((Hcorner1 z).1.val,(Hcorner1 z).2.val)=
      (((c • w).1+1)/2,((c • w).2+1)/2) at hf
    refine ⟨c,div_nonneg (gauge_nonneg w) (gauge_nonneg w),?_,?_⟩
    · exact congrArg Prod.fst hf
    · exact congrArg Prod.snd hf
  have hCorner0OutsideCriterion (z : ↥unitInterval × ↥unitInterval)
      (hz : (-(10/3)*(z.1.val-3/10)+7*(z.2.val-6/7)≤0) ∨
        ((3/5:ℝ)*(-(10/3)*(z.1.val-3/10)+7*(z.2.val-6/7))≤
          5/3*(z.1.val-3/10)+7/2*(z.2.val-6/7))) :
      z ∉ Set.range Ecorner0 := by
    intro he
    have hb := hEstdRangeBounds (Hcorner0 z) (hEcorner0Range z he)
    obtain ⟨c,hc,hx,hy⟩ := hCorner0Scalar z
    rw [hx,hy] at hb
    rcases hz with hz|hz
    · have hn := mul_nonpos_of_nonneg_of_nonpos hc hz
      linarith [hb.1]
    · have hn := mul_le_mul_of_nonneg_left hz hc
      nlinarith [hb.1,hb.2.2]
  have hCorner1OutsideCriterion (z : ↥unitInterval × ↥unitInterval)
      (hz : (3/2*(z.1.val-1/3)+7/3*(z.2.val-4/7)≤0) ∨
        ((3/5:ℝ)*(3/2*(z.1.val-1/3)+7/3*(z.2.val-4/7))≤
          3/4*(z.1.val-1/3)-7/6*(z.2.val-4/7)) ∨
        (3/4*(z.1.val-1/3)-7/6*(z.2.val-4/7)≤
          -(11/20:ℝ)*(3/2*(z.1.val-1/3)+7/3*(z.2.val-4/7)))) :
      z ∉ Set.range Ecorner1 := by
    intro he
    have hb := hEstdRangeBounds (Hcorner1 z) (hEcorner1Range z he)
    obtain ⟨c,hc,hx,hy⟩ := hCorner1Scalar z
    rw [hx,hy] at hb
    rcases hz with hz|hz|hz
    · have hn := mul_nonpos_of_nonneg_of_nonpos hc hz
      linarith [hb.1]
    · have hn := mul_le_mul_of_nonneg_left hz hc
      nlinarith [hb.1,hb.2.2]
    · have hn := mul_le_mul_of_nonneg_left hz hc
      nlinarith [hb.1,hb.2.1]
  have hCorner0OutsideOtherRuns (z : ↥unitInterval × ↥unitInterval)
      (hz : (z.1.val=0 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7) ∨
        z∈Pcorner1 ∨
        (z.1.val=1 ∧ (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7) ∨
        (z.2.val=0 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3)) :
      z ∉ Set.range Ecorner0 := by
    apply hCorner0OutsideCriterion
    rcases hz with hz|hz|hz|hz
    · exact Or.inl (by rcases hz with ⟨hx,hl,hu⟩;linarith)
    · change (z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
        (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · exact Or.inl (by rcases hz with ⟨hx,hl,hu⟩;linarith)
    · exact Or.inl (by rcases hz with ⟨hy,hl,hu⟩;linarith)
  have hCorner1OutsideOtherRuns (z : ↥unitInterval × ↥unitInterval)
      (hz : (z.1.val=0 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7) ∨
        z∈Pcorner0 ∨
        (z.1.val=1 ∧ (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7) ∨
        (z.2.val=0 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3)) :
      z ∉ Set.range Ecorner1 := by
    apply hCorner1OutsideCriterion
    rcases hz with hz|hz|hz|hz
    · exact Or.inl (by rcases hz with ⟨hx,hl,hu⟩;linarith)
    · change (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
        (z.1.val=0 ∧ (6/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by rcases hz with ⟨hx,hl,hu⟩;linarith))
    · exact Or.inl (by rcases hz with ⟨hy,hl,hu⟩;linarith)
  let Aleft : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=0 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7)
  let Aright : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=1 ∧ (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7)
  let Abottom : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.2.val=0 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3)
  have hLeftOutsideOtherRuns (z : ↥unitInterval × ↥unitInterval)
      (hz : z∈Pcorner0 ∨ z∈Pcorner1 ∨ z∈Aright ∨ z∈Abottom) :
      z ∉ Set.range Eleft := by
    intro he
    obtain ⟨v,hv⟩ := he
    have hf := hEleftFormula v
    rw [hv] at hf
    have hb : z.1.val≤(1/50:ℝ) ∧ (1/2:ℝ)≤z.2.val ∧ z.2.val≤11/14 := by
      rw [hf.1,hf.2]
      exact ⟨by linarith [v.1.property.2],by linarith [v.2.property.1],by linarith [v.2.property.2]⟩
    rcases hz with hz|hz|hz|hz
    · change (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
        (z.1.val=0 ∧ (6/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩ <;> linarith [hb.2.2]
    · change (z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
        (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
      · linarith [hb.2.2]
      · linarith [hb.1]
    · change z.1.val=1 ∧ (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7 at hz
      linarith [hb.1,hz.1]
    · change z.2.val=0 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3 at hz
      linarith [hb.2.1,hz.1]
  have hRightOutsideOtherRuns (z : ↥unitInterval × ↥unitInterval)
      (hz : z∈Aleft ∨ z∈Pcorner0 ∨ z∈Pcorner1 ∨ z∈Abottom) :
      z ∉ Set.range Eright := by
    intro he
    obtain ⟨v,hv⟩ := he
    have hf := hErightFormula v
    rw [hv] at hf
    have hb : (49/50:ℝ)≤z.1.val ∧ (3/14:ℝ)≤z.2.val ∧ z.2.val≤1/2 := by
      rw [hf.1,hf.2]
      exact ⟨by linarith [v.1.property.2],by linarith [v.2.property.1],by linarith [v.2.property.2]⟩
    rcases hz with hz|hz|hz|hz
    · change z.1.val=0 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7 at hz
      linarith [hb.1,hz.1]
    · change (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
        (z.1.val=0 ∧ (6/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
      · linarith [hb.2.2]
      · linarith [hb.1]
    · change (z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
        (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩ <;> linarith [hb.2.2]
    · change z.2.val=0 ∧ (1/2:ℝ)≤z.1.val ∧ z.1.val≤2/3 at hz
      linarith [hb.2.1,hz.1]
  have hBottomOutsideOtherRuns (z : ↥unitInterval × ↥unitInterval)
      (hz : z∈Aleft ∨ z∈Pcorner0 ∨ z∈Pcorner1 ∨ z∈Aright) :
      z ∉ Set.range Ebottom := by
    intro he
    obtain ⟨v,hv⟩ := he
    have hf := hEbottomFormula v
    rw [hv] at hf
    have hb : (5/12:ℝ)≤z.1.val ∧ z.1.val≤3/4 ∧ z.2.val≤1/50 := by
      rw [hf.1,hf.2]
      exact ⟨by linarith [v.2.property.1],by linarith [v.2.property.2],by linarith [v.1.property.2]⟩
    rcases hz with hz|hz|hz|hz
    · change z.1.val=0 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤5/7 at hz
      linarith [hb.1,hz.1]
    · change (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
        (z.1.val=0 ∧ (6/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
      · linarith [hb.2.2]
      · linarith [hb.1]
    · change (z.2.val=1 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1) ∨
        (z.1.val=1 ∧ (4/7:ℝ)≤z.2.val ∧ z.2.val≤1) at hz
      rcases hz with ⟨hy,hl,hu⟩|⟨hx,hl,hu⟩
      · linarith [hb.2.2]
      · linarith [hb.2.1]
    · change z.1.val=1 ∧ (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7 at hz
      linarith [hb.2.1,hz.1]
  have hComposeBoundaryCollapses :
      ∀ (F G : C(↥unitInterval × ↥unitInterval, ↥unitInterval × ↥unitInterval))
        (A : Set (Set (↥unitInterval × ↥unitInterval))) (B : Set (↥unitInterval × ↥unitInterval)),
      (∀ z w, F z=F w ↔ z=w ∨ ∃ a∈A, z∈a ∧ w∈a) →
      (∀ z w, G z=G w ↔ z=w ∨ (z∈B ∧ w∈B)) →
      (∀ a∈A, Disjoint a B) → (∀ z∈B, F z=z) →
      (∀ z w, (G.comp F) z=(G.comp F) w ↔
        z=w ∨ (∃ a∈A, z∈a ∧ w∈a) ∨ (z∈B ∧ w∈B)) := by
    intro F G A B hF hG hdis hfix z w
    have hpre : ∀ t, F t∈B ↔ t∈B := by
      intro t
      constructor
      · intro ht
        have hk := (hF t (F t)).mp (by rw [hfix (F t) ht])
        rcases hk with he|⟨a,ha,hta,hFta⟩
        · exact he.symm ▸ ht
        · exact False.elim ((Set.disjoint_left.mp (hdis a ha)) hFta ht)
      · intro ht
        simpa only [hfix t ht] using ht
    change G (F z)=G (F w) ↔ _
    rw [hG,hF,hpre z,hpre w]
    exact or_assoc
  let Aruns : Fin 5 → Set (↥unitInterval × ↥unitInterval) :=
    ![Aleft,Pcorner0,Pcorner1,Aright,Abottom]
  let Eruns : Fin 5 → C(Bstd,↥unitInterval × ↥unitInterval) :=
    ![Eleft,Ecorner0,Ecorner1,Eright,Ebottom]
  have hSourceCollarSeparation : ∀ i j : Fin 5, i≠j →
      ∀ z∈Aruns j, z∉Set.range (Eruns i) := by
    intro i j hij z hz
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hLeftOutsideOtherRuns z (Or.inl hz)
    · exact hLeftOutsideOtherRuns z (Or.inr (Or.inl hz))
    · exact hLeftOutsideOtherRuns z (Or.inr (Or.inr (Or.inl hz)))
    · exact hLeftOutsideOtherRuns z (Or.inr (Or.inr (Or.inr hz)))
    · exact hCorner0OutsideOtherRuns z (Or.inl hz)
    · exact False.elim (hij rfl)
    · exact hCorner0OutsideOtherRuns z (Or.inr (Or.inl hz))
    · exact hCorner0OutsideOtherRuns z (Or.inr (Or.inr (Or.inl hz)))
    · exact hCorner0OutsideOtherRuns z (Or.inr (Or.inr (Or.inr hz)))
    · exact hCorner1OutsideOtherRuns z (Or.inl hz)
    · exact hCorner1OutsideOtherRuns z (Or.inr (Or.inl hz))
    · exact False.elim (hij rfl)
    · exact hCorner1OutsideOtherRuns z (Or.inr (Or.inr (Or.inl hz)))
    · exact hCorner1OutsideOtherRuns z (Or.inr (Or.inr (Or.inr hz)))
    · exact hRightOutsideOtherRuns z (Or.inl hz)
    · exact hRightOutsideOtherRuns z (Or.inr (Or.inl hz))
    · exact hRightOutsideOtherRuns z (Or.inr (Or.inr (Or.inl hz)))
    · exact False.elim (hij rfl)
    · exact hRightOutsideOtherRuns z (Or.inr (Or.inr (Or.inr hz)))
    · exact hBottomOutsideOtherRuns z (Or.inl hz)
    · exact hBottomOutsideOtherRuns z (Or.inr (Or.inl hz))
    · exact hBottomOutsideOtherRuns z (Or.inr (Or.inr (Or.inl hz)))
    · exact hBottomOutsideOtherRuns z (Or.inr (Or.inr (Or.inr hz)))
    · exact False.elim (hij rfl)
  have hRunImage : ∀ i : Fin 5, (Eruns i) '' Kstd=Aruns i := by
    intro i
    fin_cases i
    · change Eleft '' Kstd=Aleft
      simpa only [Aleft,Kstd,Subtype.ext_iff,Set.Icc.coe_zero,Set.Icc.coe_one] using hEleftKernelImage
    · change Ecorner0 '' Kstd=Pcorner0
      simpa only [Pcorner0,Kstd,Subtype.ext_iff,Set.Icc.coe_zero,Set.Icc.coe_one] using hActualCorner0KernelImage
    · exact hActualCorner1KernelImage
    · change Eright '' Kstd=Aright
      simpa only [Aright,Kstd,Subtype.ext_iff,Set.Icc.coe_zero,Set.Icc.coe_one] using hErightKernelImage
    · change Ebottom '' Kstd=Abottom
      simpa only [Abottom,Kstd,Subtype.ext_iff,Set.Icc.coe_zero,Set.Icc.coe_one] using hEbottomKernelImage
  have hRunPairwiseDisjoint : ∀ i j : Fin 5, i≠j → Disjoint (Aruns i) (Aruns j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    rw [←hRunImage i] at hzi
    obtain ⟨v,hv,hev⟩ := hzi
    exact hSourceCollarSeparation i j hij z hzj ⟨v,hev⟩
  obtain ⟨Fleft,hFleftFix,hFleftSurj,hFleftKernel,hFleftQuot,hFleftAxis⟩ :=
    hCutDiskBoundaryCollapse Eleft hEleft hEleftRelativeFrontier
  obtain ⟨Fcorner0,hFcorner0Fix,hFcorner0Surj,hFcorner0Kernel,hFcorner0Quot,hFcorner0Axis⟩ :=
    hActualCorner0RunGlobalCollapse
  obtain ⟨Fcorner1,hFcorner1Fix,hFcorner1Surj,hFcorner1Kernel,hFcorner1Quot,hFcorner1Axis⟩ :=
    hActualCorner1RunGlobalCollapse
  obtain ⟨Fright,hFrightFix,hFrightSurj,hFrightKernel,hFrightQuot,hFrightAxis⟩ :=
    hActualRightRunGlobalCollapse
  obtain ⟨Fbottom,hFbottomFix,hFbottomSurj,hFbottomKernel,hFbottomQuot,hFbottomAxis⟩ :=
    hActualBottomRunGlobalCollapse
  let Fruns : Fin 5 → C(↥unitInterval × ↥unitInterval,↥unitInterval × ↥unitInterval) :=
    ![Fleft,Fcorner0,Fcorner1,Fright,Fbottom]
  have hRunsSurjective : ∀ i : Fin 5, Function.Surjective (Fruns i) := by
    intro i
    fin_cases i
    · exact hFleftSurj
    · exact hFcorner0Surj
    · exact hFcorner1Surj
    · exact hFrightSurj
    · exact hFbottomSurj
  have hRunsKernel : ∀ (i : Fin 5) z w,
      Fruns i z=Fruns i w ↔ z=w ∨ (z∈Aruns i ∧ w∈Aruns i) := by
    intro i z w
    fin_cases i
    · change Fleft z=Fleft w ↔ _
      rw [hFleftKernel]
      change (z=w ∨ (z∈(Eruns 0) '' Kstd ∧ w∈(Eruns 0) '' Kstd)) ↔ _
      rw [hRunImage 0]
      rfl
    · change Fcorner0 z=Fcorner0 w ↔ _
      rw [hFcorner0Kernel]
      change (z=w ∨ (z∈(Eruns 1) '' Kstd ∧ w∈(Eruns 1) '' Kstd)) ↔ _
      rw [hRunImage 1]
      rfl
    · change Fcorner1 z=Fcorner1 w ↔ _
      rw [hFcorner1Kernel]
      change (z=w ∨ (z∈(Eruns 2) '' Kstd ∧ w∈(Eruns 2) '' Kstd)) ↔ _
      rw [hRunImage 2]
      rfl
    · change Fright z=Fright w ↔ _
      rw [hFrightKernel]
      change (z=w ∨ (z∈(Eruns 3) '' Kstd ∧ w∈(Eruns 3) '' Kstd)) ↔ _
      rw [hRunImage 3]
      rfl
    · change Fbottom z=Fbottom w ↔ _
      rw [hFbottomKernel]
      change (z=w ∨ (z∈(Eruns 4) '' Kstd ∧ w∈(Eruns 4) '' Kstd)) ↔ _
      rw [hRunImage 4]
      rfl
  have hRunsFixOther : ∀ (i j : Fin 5), i≠j → ∀ z∈Aruns j, Fruns i z=z := by
    intro i j hij z hz
    have houtside : z∉interior (Set.range (Eruns i)) := by
      intro hh
      exact hSourceCollarSeparation i j hij z hz (interior_subset hh)
    fin_cases i
    · exact hFleftFix z houtside
    · exact hFcorner0Fix z houtside
    · exact hFcorner1Fix z houtside
    · exact hFrightFix z houtside
    · exact hFbottomFix z houtside
  let LiteralPerimeter : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1)
  have hActualAllFiveSourceCollarNormalCoordinates : ∀ (i : Fin 5) v,
      ∃ w, Fruns i (Eruns i v)=Eruns i w ∧ w.1.val=v.1.val := by
    intro i v
    fin_cases i
    · exact hFleftAxis v
    · exact hFcorner0Axis v
    · exact hFcorner1Axis v
    · exact hFrightAxis v
    · exact hFbottomAxis v
  have hGaugeLinearTransport :
      ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∀ r : Set (ℝ × ℝ), ∀ x : ℝ × ℝ,
        gauge (L '' r) (L x)=gauge r x := by
    intro L r x
    have he : Set.ofPred (fun a : ℝ => a∈Ioi 0 ∧ a⁻¹ • L x∈L '' r)=
        Set.ofPred (fun a : ℝ => a∈Ioi 0 ∧ a⁻¹ • x∈r) := by
      ext a
      constructor
      · rintro ⟨ha,z,hz,hzx⟩
        have hz' : z=a⁻¹ • x := L.injective (by simpa using hzx)
        exact ⟨ha,hz' ▸ hz⟩
      · rintro ⟨ha,hx⟩
        exact ⟨ha,a⁻¹ • x,hx,by simp⟩
    rw [gauge_def',he,←gauge_def']
  have hShiftedSquareFrontier :
      ∀ o : ℝ × ℝ, ∀ z : ↥unitInterval × ↥unitInterval,
        (z.1.val-o.1,z.2.val-o.2)∈frontier
          (Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)) ↔
        z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1 := by
    intro o z
    rw [(isClosed_Icc.prod isClosed_Icc).frontier_eq,interior_prod_eq,interior_Icc,interior_Icc]
    constructor
    · rintro ⟨hz,hni⟩
      by_contra hn
      push Not at hn
      apply hni
      constructor <;> constructor
      · have h : 0<z.1.val := lt_of_le_of_ne z.1.property.1 (Ne.symm hn.1)
        linarith
      · have h : z.1.val<1 := lt_of_le_of_ne z.1.property.2 hn.2.1
        linarith
      · have h : 0<z.2.val := lt_of_le_of_ne z.2.property.1 (Ne.symm hn.2.2.1)
        linarith
      · have h : z.2.val<1 := lt_of_le_of_ne z.2.property.2 hn.2.2.2
        linarith
    · intro hz
      refine ⟨⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
        ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩,?_⟩
      rintro ⟨hx,hy⟩
      change -o.1<z.1.val-o.1 ∧ z.1.val-o.1<1-o.1 at hx
      change -o.2<z.2.val-o.2 ∧ z.2.val-o.2<1-o.2 at hy
      rcases hz with hz|hz|hz|hz <;> linarith
  let Lcorner0 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun v => (-(10/3)*v.1+7*v.2,(5/3)*v.1+(7/2)*v.2)
    invFun := fun v => ((3/20)*(2*v.2-v.1),(v.1+2*v.2)/14)
    left_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    right_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    map_add' := by intro v w;apply Prod.ext <;> dsimp <;> ring
    map_smul' := by intro c v;apply Prod.ext <;> dsimp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let Lcorner1 : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun v => ((3/2)*v.1+(7/3)*v.2,(3/4)*v.1-(7/6)*v.2)
    invFun := fun v => ((v.1+2*v.2)/3,(3/14)*(v.1-2*v.2))
    left_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    right_inv := by intro v;apply Prod.ext <;> dsimp <;> ring
    map_add' := by intro v w;apply Prod.ext <;> dsimp <;> ring
    map_smul' := by intro c v;apply Prod.ext <;> dsimp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hActualUnitSquarePerimeterNorm (z : ↥unitInterval × ↥unitInterval) :
      z∈LiteralPerimeter ↔ ‖((2*z.1.val-1,2*z.2.val-1) : ℝ × ℝ)‖ = 1 := by
    have hx : abs (2*z.1.val-1)≤1 := abs_le.mpr ⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩
    have hy : abs (2*z.2.val-1)≤1 := abs_le.mpr ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    constructor
    · intro hz
      rcases hz with hz|hz|hz|hz
      · have he : abs (2*z.1.val-1)=1 := by rw [hz];norm_num
        rw [he,max_eq_left hy]
      · have he : abs (2*z.1.val-1)=1 := by rw [hz];norm_num
        rw [he,max_eq_left hy]
      · have he : abs (2*z.2.val-1)=1 := by rw [hz];norm_num
        rw [he,max_eq_right hx]
      · have he : abs (2*z.2.val-1)=1 := by rw [hz];norm_num
        rw [he,max_eq_right hx]
    · intro hn
      by_cases hxy : abs (2*z.1.val-1)≤abs (2*z.2.val-1)
      · rw [max_eq_right hxy] at hn
        rcases eq_or_eq_neg_of_abs_eq hn with he|he
        · exact Or.inr (Or.inr (Or.inr (by linarith)))
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · rw [max_eq_left (le_of_not_ge hxy)] at hn
        rcases eq_or_eq_neg_of_abs_eq hn with he|he
        · exact Or.inr (Or.inl (by linarith))
        · exact Or.inl (by linarith)
  have hActualRadialChartPerimeter :
      ∀ o : ℝ × ℝ, (0<o.1 ∧ o.1<1 ∧ 0<o.2 ∧ o.2<1) →
      ∀ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∀ H : (↥unitInterval × ↥unitInterval) ≃ₜ (↥unitInterval × ↥unitInterval),
      (∀ z, let w := (gaugeRescale
        (L '' (Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)))
        (closedBall (0 : ℝ × ℝ) 1) (L (z.1.val-o.1,z.2.val-o.2)));
        ((H z).1.val,(H z).2.val)=((w.1+1)/2,(w.2+1)/2)) →
      ∀ z, H z∈LiteralPerimeter ↔ z∈LiteralPerimeter := by
    intro o ho L H hformula z
    let r : Set (ℝ × ℝ) := Icc (-o.1) (1-o.1) ×ˢ Icc (-o.2) (1-o.2)
    let w := L (z.1.val-o.1,z.2.val-o.2)
    let t : Set (ℝ × ℝ) := closedBall 0 1
    let W := gaugeRescale (L '' r) t w
    have hrc : Convex ℝ r := (convex_Icc _ _).prod (convex_Icc _ _)
    have hr0 : r∈𝓝 (0:ℝ × ℝ) := by
      have hopen := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        (show (0:ℝ × ℝ)∈Ioo (-o.1) (1-o.1) ×ˢ Ioo (-o.2) (1-o.2) from by
          change (-o.1<0 ∧ 0<1-o.1) ∧ (-o.2<0 ∧ 0<1-o.2)
          constructor <;> constructor <;> linarith only [ho.1,ho.2.1,ho.2.2.1,ho.2.2.2])
      exact Filter.mem_of_superset hopen (by
        rintro v ⟨hv,hv'⟩
        exact ⟨⟨hv.1.le,hv.2.le⟩,⟨hv'.1.le,hv'.2.le⟩⟩)
    have hgt (v : ℝ × ℝ) : gauge t v=‖v‖ := by
      simp only [t,gauge_closedBall (by norm_num : (0:ℝ)≤1),div_one]
    have hGauge : ‖W‖=gauge r (z.1.val-o.1,z.2.val-o.2) := by
      have hg := gauge_gaugeRescale (L '' r)
        (absorbent_nhds_zero (closedBall_mem_nhds (0 : ℝ × ℝ) (by norm_num : (0:ℝ)<1)))
        (NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall) w
      change gauge t W=gauge (L '' r) (L (z.1.val-o.1,z.2.val-o.2)) at hg
      rw [hgt,hGaugeLinearTransport] at hg
      exact hg
    have hc : ((2*(H z).1.val-1,2*(H z).2.val-1) : ℝ × ℝ)=W := by
      have hf := hformula z
      change ((H z).1.val,(H z).2.val)=((W.1+1)/2,(W.2+1)/2) at hf
      have hx := congrArg Prod.fst hf
      have hy := congrArg Prod.snd hf
      apply Prod.ext <;> dsimp only at hx hy ⊢ <;> linarith
    rw [hActualUnitSquarePerimeterNorm (H z),hc,hGauge,
      gauge_eq_one_iff_mem_frontier hrc hr0]
    exact hShiftedSquareFrontier o z
  have hActualCorner0ChartPreservesPerimeter : ∀ z,
      Hcorner0 z∈LiteralPerimeter ↔ z∈LiteralPerimeter := by
    apply hActualRadialChartPerimeter (3/10,6/7) (by norm_num) Lcorner0 Hcorner0
    intro z
    have hf := hHcorner0Formula z
    simp only [ite_true] at hf
    exact hf
  have hActualCorner1ChartPreservesPerimeter : ∀ z,
      Hcorner1 z∈LiteralPerimeter ↔ z∈LiteralPerimeter := by
    apply hActualRadialChartPerimeter (1/3,4/7) (by norm_num) Lcorner1 Hcorner1
    intro z
    have hf := hHcorner1Formula z
    have hk : (1 : Fin 2)≠0 := by decide
    simp only [hk,ite_false] at hf
    exact hf
  have hActualStandardCollarMeetsPerimeter (v : Bstd) :
      Estd v∈LiteralPerimeter ↔ v.1.val=0 := by
    change (1-v.1.val/100=0 ∨ 1-v.1.val/100=1 ∨ θ v.2.val=0 ∨ θ v.2.val=1) ↔ _
    have hy := hθbound v.2
    constructor
    · rintro (hx|hx|hy0|hy1) <;> linarith [v.1.property.1,v.1.property.2,hy.1,hy.2]
    · intro hx
      exact Or.inr (Or.inl (by rw [hx];norm_num))
  have hActualCorner0InversePreservesPerimeter (z : ↥unitInterval × ↥unitInterval) :
      Hcorner0.symm z∈LiteralPerimeter ↔ z∈LiteralPerimeter := by
    have he := hActualCorner0ChartPreservesPerimeter (Hcorner0.symm z)
    rw [Hcorner0.apply_symm_apply] at he
    exact he.symm
  have hActualCorner1InversePreservesPerimeter (z : ↥unitInterval × ↥unitInterval) :
      Hcorner1.symm z∈LiteralPerimeter ↔ z∈LiteralPerimeter := by
    have he := hActualCorner1ChartPreservesPerimeter (Hcorner1.symm z)
    rw [Hcorner1.apply_symm_apply] at he
    exact he.symm
  have hActualFiveCollarsMeetSourcePerimeter : ∀ (i : Fin 5) v,
      Eruns i v∈LiteralPerimeter ↔ v.1.val=0 := by
    intro i v
    fin_cases i
    · change ((Eleft v).1.val=0 ∨ (Eleft v).1.val=1 ∨
        (Eleft v).2.val=0 ∨ (Eleft v).2.val=1) ↔ _
      rw [(hEleftFormula v).1,(hEleftFormula v).2]
      constructor
      · rintro (hx|hx|hy|hy) <;> linarith [v.1.property.1,v.1.property.2,v.2.property.1,v.2.property.2]
      · intro hx
        exact Or.inl (by rw [hx];norm_num)
    · change Ecorner0 v∈LiteralPerimeter ↔ _
      rw [hEcorner0Pin,hActualCorner0InversePreservesPerimeter]
      exact hActualStandardCollarMeetsPerimeter v
    · change Ecorner1 v∈LiteralPerimeter ↔ _
      rw [hEcorner1Pin,hActualCorner1InversePreservesPerimeter]
      exact hActualStandardCollarMeetsPerimeter v
    · change ((Eright v).1.val=0 ∨ (Eright v).1.val=1 ∨
        (Eright v).2.val=0 ∨ (Eright v).2.val=1) ↔ _
      rw [(hErightFormula v).1,(hErightFormula v).2]
      constructor
      · rintro (hx|hx|hy|hy) <;> linarith [v.1.property.1,v.1.property.2,v.2.property.1,v.2.property.2]
      · intro hx
        exact Or.inr (Or.inl (by rw [hx];norm_num))
    · change ((Ebottom v).1.val=0 ∨ (Ebottom v).1.val=1 ∨
        (Ebottom v).2.val=0 ∨ (Ebottom v).2.val=1) ↔ _
      rw [(hEbottomFormula v).1,(hEbottomFormula v).2]
      constructor
      · rintro (hx|hx|hy|hy) <;> linarith [v.1.property.1,v.1.property.2,v.2.property.1,v.2.property.2]
      · intro hx
        exact Or.inr (Or.inr (Or.inl (by rw [hx];norm_num)))
  have hActualAllFiveRunMapsFixOutsideCollars : ∀ (i : Fin 5) z,
      z∉Set.range (Eruns i) → Fruns i z=z := by
    intro i z hz
    have hi : z∉interior (Set.range (Eruns i)) := fun h => hz (interior_subset h)
    fin_cases i
    · exact hFleftFix z hi
    · exact hFcorner0Fix z hi
    · exact hFcorner1Fix z hi
    · exact hFrightFix z hi
    · exact hFbottomFix z hi
  have hActualAllFiveSourceRunMapsPreservePerimeter : ∀ (i : Fin 5) z,
      Fruns i z∈LiteralPerimeter ↔ z∈LiteralPerimeter := by
    intro i z
    by_cases hz : z∈Set.range (Eruns i)
    · obtain ⟨v,rfl⟩ := hz
      obtain ⟨w,hf,hx⟩ := hActualAllFiveSourceCollarNormalCoordinates i v
      rw [hf,hActualFiveCollarsMeetSourcePerimeter i w,hActualFiveCollarsMeetSourcePerimeter i v,hx]
    · rw [hActualAllFiveRunMapsFixOutsideCollars i z hz]
  have hComposeRunList : ∀ l : List (Fin 5), l.Nodup →
      ∃ F : C(↥unitInterval × ↥unitInterval,↥unitInterval × ↥unitInterval),
      Function.Surjective F ∧
      (∀ z w, F z=F w ↔ z=w ∨ ∃ i∈l, z∈Aruns i ∧ w∈Aruns i) ∧
      (∀ j : Fin 5, j∉l → ∀ z∈Aruns j, F z=z) ∧
      (∀ z, F z∈LiteralPerimeter ↔ z∈LiteralPerimeter) := by
    intro l
    induction l with
    | nil =>
      intro hl
      refine ⟨ContinuousMap.id _,Function.surjective_id,?_,?_,?_⟩
      · intro z w
        simp only [ContinuousMap.id_apply,List.not_mem_nil,false_and,exists_false,or_false]
      · intro j hj z hz
        rfl
      · intro z
        rfl
    | cons i l ih =>
      intro hl
      obtain ⟨hni,hnl⟩ := List.nodup_cons.mp hl
      obtain ⟨F,hFs,hFk,hFfix,hFperim⟩ := ih hnl
      have hpre : ∀ z, F z∈Aruns i ↔ z∈Aruns i := by
        intro z
        constructor
        · intro hz
          have hk := (hFk z (F z)).mp (by rw [hFfix i hni (F z) hz])
          rcases hk with he|⟨j,hj,hzj,hFzj⟩
          · exact he.symm ▸ hz
          · have hji : j≠i := by intro he;subst j;exact hni hj
            exact False.elim ((Set.disjoint_left.mp (hRunPairwiseDisjoint j i hji)) hFzj hz)
        · intro hz
          rw [hFfix i hni z hz]
          exact hz
      refine ⟨(Fruns i).comp F,(hRunsSurjective i).comp hFs,?_,?_,?_⟩
      · intro z w
        change Fruns i (F z)=Fruns i (F w) ↔ _
        rw [hRunsKernel,hFk,hpre z,hpre w]
        constructor
        · rintro ((he|⟨j,hj,hzj,hwj⟩)|⟨hzi,hwi⟩)
          · exact Or.inl he
          · exact Or.inr ⟨j,List.mem_cons_of_mem i hj,hzj,hwj⟩
          · exact Or.inr ⟨i,List.mem_cons_self,hzi,hwi⟩
        · rintro (he|⟨j,hj,hzj,hwj⟩)
          · exact Or.inl (Or.inl he)
          · rcases List.mem_cons.mp hj with he|hj
            · subst j
              exact Or.inr ⟨hzj,hwj⟩
            · exact Or.inl (Or.inr ⟨j,hj,hzj,hwj⟩)
      · intro j hj z hz
        have hji : i≠j := by
          intro he
          subst j
          exact hj List.mem_cons_self
        have hjl : j∉l := fun hh => hj (List.mem_cons_of_mem i hh)
        change Fruns i (F z)=z
        rw [hFfix j hjl z hz,hRunsFixOther i j hji z hz]
      · intro z
        exact (hActualAllFiveSourceRunMapsPreservePerimeter i (F z)).trans (hFperim z)
  let allRuns : List (Fin 5) := [0,1,2,3,4]
  obtain ⟨Fboundary,hFboundarySurj,hFboundaryKernel,hFboundaryFix,hFboundaryPerimeter⟩ :=
    hComposeRunList allRuns (by decide)
  have hEveryRun (i : Fin 5) : i∈allRuns := by
    fin_cases i <;> decide
  have hActualFiveBoundaryRunKernel : ∀ z w,
      Fboundary z=Fboundary w ↔ z=w ∨ ∃ i : Fin 5, z∈Aruns i ∧ w∈Aruns i := by
    intro z w
    simpa only [hEveryRun,true_and] using hFboundaryKernel z w
  let Rboundary : (↥unitInterval × ↥unitInterval) → (↥unitInterval × ↥unitInterval) → Prop :=
    fun z w => ∃ i : Fin 5, z∈Aruns i ∧ w∈Aruns i
  let Qboundary := Quotient (Relation.EqvGen.setoid Rboundary)
  have hActualFiveBoundaryRunDiskHomeomorphism :
      ∃ h : Qboundary ≃ₜ (↥unitInterval × ↥unitInterval),
      ∀ z, h (Quotient.mk (Relation.EqvGen.setoid Rboundary) z)=Fboundary z := by
    have hrespect (z w : ↥unitInterval × ↥unitInterval) (h : Relation.EqvGen Rboundary z w) :
        Fboundary z=Fboundary w := by
      induction h with
      | rel z w h => exact (hActualFiveBoundaryRunKernel z w).mpr (Or.inr h)
      | refl z => rfl
      | symm z w h ih => exact ih.symm
      | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
    let q : Qboundary → (↥unitInterval × ↥unitInterval) := Quotient.lift Fboundary hrespect
    have hqc : Continuous q := Fboundary.continuous.quotient_lift _
    have hqi : Function.Injective q := by
      intro x y he
      induction x using Quotient.inductionOn with
      | _ z =>
        induction y using Quotient.inductionOn with
        | _ w =>
          change Fboundary z=Fboundary w at he
          rcases (hActualFiveBoundaryRunKernel z w).mp he with he|he
          · exact congrArg (Quotient.mk _) he
          · exact Quotient.sound (Relation.EqvGen.rel z w he)
    have hqs : Function.Surjective q := by
      intro z
      obtain ⟨w,hw⟩ := hFboundarySurj z
      exact ⟨Quotient.mk _ w,hw⟩
    let e := Equiv.ofBijective q ⟨hqi,hqs⟩
    let Hq : Qboundary ≃ₜ (↥unitInterval × ↥unitInterval) :=
      (show Continuous (e : Qboundary → (↥unitInterval × ↥unitInterval)) from hqc).homeoOfEquivCompactToT2
    exact ⟨Hq,fun _ => rfl⟩
  have actualCutData := actual_one_face_source_cut_disk_total_attaching
  dsimp only at actualCutData
  obtain ⟨Fa,hFaSurj,hFaNorth0,hFaSouth1,hFaNorth1,hFaSouth0,hFaDisk⟩ := actualCutData
  let Atree : Set Total := northDiskFace true ''
    Set.ofPred (fun v : StandardDisk => ∃ p : Sphere, ∃ hp : height p=0,
      (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp)
  have actualTreeData := actual_source_five_edge_tree_contraction
  dsimp only at actualTreeData
  obtain ⟨Gtree,hGtreeSurj,hGtreeKernel,hGtreeQuotient⟩ := actualTreeData
  have hNorthTreeMember (i : Fin 6) (hi : i≠0) (p : Sphere) (hp : height p=0)
      (hsector : closedArcSector i p) : northDiskFace true (diskBoundaryPoint p hp)∈Atree :=
    ⟨diskBoundaryPoint p hp,⟨p,hp,⟨i,hi,hsector⟩,rfl⟩,rfl⟩
  have hOddSouthTreeAttach (p : Sphere) (hp : height p=0) (s : Bool)
      (hi : closedArcSector (1:Fin 6) p ∨ closedArcSector (3:Fin 6) p ∨ closedArcSector (5:Fin 6) p) :
      southDiskFace s (diskBoundaryPoint p hp)=northDiskFace s (diskBoundaryPoint p hp) := by
    symm
    rw [northDiskFace_boundary,southDiskFace_boundary,boundary_attach]
    have hn : seamPolynomial p≤0 := by
      rw [seamPolynomial_factor]
      rcases hi with hi|hi|hi
      · have hv := hi.2
        change 0≤p.val 1 ∧ seamA p≤0 ∧ 0 ≤ seamB p at hv
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv.1 hv.2.1) hv.2.2
      · have hv := hi.2
        change p.val 1≤0 ∧ seamA p≤0 ∧ seamB p≤0 at hv
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos hv.1 hv.2.1) hv.2.2
      · have hv := hi.2
        change p.val 1≤0 ∧ 0 ≤ seamA p ∧ 0 ≤ seamB p at hv
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hv.1 hv.2.1) hv.2.2
    right
    simp [not_lt.mpr hn]
  have hEvenSouthTreeAttach (p : Sphere) (hp : height p=0) (s : Bool)
      (hi : closedArcSector (2:Fin 6) p ∨ closedArcSector (4:Fin 6) p) :
      southDiskFace (!s) (diskBoundaryPoint p hp)=northDiskFace s (diskBoundaryPoint p hp) := by
    symm
    rw [northDiskFace_boundary,southDiskFace_boundary,boundary_attach]
    have hn : 0 ≤ seamPolynomial p := by
      rw [seamPolynomial_factor]
      rcases hi with hi|hi
      · have hv := hi.2
        change 0≤p.val 1 ∧ seamA p≤0 ∧ seamB p≤0 at hv
        exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hv.1 hv.2.1) hv.2.2
      · have hv := hi.2
        change p.val 1≤0 ∧ 0 ≤ seamA p ∧ seamB p≤0 at hv
        exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hv.1 hv.2.1) hv.2.2
    by_cases hpos : 0<seamPolynomial p
    · right
      simp [hpos]
    · left
      exact ⟨hp,le_antisymm (le_of_not_gt hpos) hn⟩
  have hFaNorthOccurrence (i : Fin 6) (hi : i≠0) :
      ∀ q∈OccNorm true true i, Fa q∈Atree := by
    rintro q ⟨p,hp,hsector,rfl⟩
    change Fa (Quotient.mk _ (Sum.inr (Quotient.mk _ (Sum.inl (diskBoundaryPoint p hp)))))∈Atree
    rw [hFaNorth1]
    exact hNorthTreeMember i hi p hp hsector
  have hFaOddSouthOccurrence (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=5) :
      ∀ q∈OccNorm false true i, Fa q∈Atree := by
    rintro q ⟨p,hp,hsector,rfl⟩
    change Fa (Quotient.mk _ (Sum.inl (Quotient.mk _ (Sum.inr (diskBoundaryPoint p hp)))))∈Atree
    rw [hFaSouth1]
    have hodd : closedArcSector (1:Fin 6) p ∨ closedArcSector (3:Fin 6) p ∨ closedArcSector (5:Fin 6) p := by
      rcases hi with rfl|rfl|rfl
      · exact Or.inl hsector
      · exact Or.inr (Or.inl hsector)
      · exact Or.inr (Or.inr hsector)
    rw [hOddSouthTreeAttach p hp true hodd]
    have hn : i≠0 := by rcases hi with rfl|rfl|rfl <;> decide
    exact hNorthTreeMember i hn p hp hsector
  have hFaEvenSouthOccurrence (i : Fin 6) (hi : i=2 ∨ i=4) :
      ∀ q∈OccNorm true false i, Fa q∈Atree := by
    rintro q ⟨p,hp,hsector,rfl⟩
    change Fa (Quotient.mk _ (Sum.inr (Quotient.mk _ (Sum.inr (diskBoundaryPoint p hp)))))∈Atree
    rw [hFaSouth0]
    have heven : closedArcSector (2:Fin 6) p ∨ closedArcSector (4:Fin 6) p := by
      rcases hi with rfl|rfl
      · exact Or.inl hsector
      · exact Or.inr hsector
    have hattach := hEvenSouthTreeAttach p hp true heven
    simp only [Bool.not_true] at hattach
    rw [hattach]
    have hn : i≠0 := by rcases hi with rfl|rfl <;> decide
    exact hNorthTreeMember i hn p hp hsector
  have hOccLeftSource : M3 '' OccNorm false true 5=Aleft := by
    exact hVertical (3:Fin 4) false
  have hOccSmallCornerSource : M3 '' OccNorm false true 3=Pcorner0 := by
    exact hCorners false true
  have hOccRightSource : M3 '' OccNorm true false 4=Aright := by
    exact hVertical (0:Fin 4) true
  have hOccBottomSource : M3 '' OccNorm true false 2=Abottom := by
    exact hBottomSRaw
  have hSourcePullback (U : Set (Quotient (Relation.EqvGen.setoid R1norm))) (z : ↥unitInterval × ↥unitInterval)
      (hz : z∈M3 '' U) : M3.symm z∈U := by
    obtain ⟨q,hq,he⟩ := hz
    rw [←he,M3.symm_apply_apply]
    exact hq
  have hActualFiveBoundaryRunsIntoTree : ∀ (i : Fin 5) z,
      z∈Aruns i → Fa (M3.symm z)∈Atree := by
    intro i z hz
    fin_cases i
    · change z∈Aleft at hz
      rw [←hOccLeftSource] at hz
      exact hFaOddSouthOccurrence 5 (Or.inr (Or.inr rfl)) _ (hSourcePullback _ z hz)
    · change z∈Pcorner0 at hz
      rw [←hOccSmallCornerSource] at hz
      exact hFaOddSouthOccurrence 3 (Or.inr (Or.inl rfl)) _ (hSourcePullback _ z hz)
    · change z∈Pcorner1 at hz
      rw [←hActualBigCornerSourceImage] at hz
      have hq := hSourcePullback _ z hz
      change (((((M3.symm z∈OccNorm false true 1 ∨ M3.symm z∈OccNorm true true 1) ∨
        M3.symm z∈OccNorm true true 2) ∨ M3.symm z∈OccNorm true true 3) ∨
        M3.symm z∈OccNorm true true 4) ∨ M3.symm z∈OccNorm true true 5) at hq
      rcases hq with (((((hq|hq)|hq)|hq)|hq)|hq)
      · exact hFaOddSouthOccurrence 1 (Or.inl rfl) _ hq
      · exact hFaNorthOccurrence 1 (by decide) _ hq
      · exact hFaNorthOccurrence 2 (by decide) _ hq
      · exact hFaNorthOccurrence 3 (by decide) _ hq
      · exact hFaNorthOccurrence 4 (by decide) _ hq
      · exact hFaNorthOccurrence 5 (by decide) _ hq
    · change z∈Aright at hz
      rw [←hOccRightSource] at hz
      exact hFaEvenSouthOccurrence 4 (Or.inr rfl) _ (hSourcePullback _ z hz)
    · change z∈Abottom at hz
      rw [←hOccBottomSource] at hz
      exact hFaEvenSouthOccurrence 2 (Or.inl rfl) _ (hSourcePullback _ z hz)
  let Jsource : C(↥unitInterval × ↥unitInterval,Total) :=
    Gtree.comp (Fa.comp (⟨M3.symm,M3.symm.continuous⟩ : C(↥unitInterval × ↥unitInterval,_)))
  have hJsourceSurj : Function.Surjective Jsource :=
    hGtreeSurj.comp (hFaSurj.comp M3.symm.surjective)
  have hJsourceRespect (z w : ↥unitInterval × ↥unitInterval) (h : Relation.EqvGen Rboundary z w) :
      Jsource z=Jsource w := by
    induction h with
    | rel z w h =>
      obtain ⟨i,hz,hw⟩ := h
      exact (hGtreeKernel _ _).mpr (Or.inr ⟨hActualFiveBoundaryRunsIntoTree i z hz,hActualFiveBoundaryRunsIntoTree i w hw⟩)
    | refl z => rfl
    | symm z w h ih => exact ih.symm
    | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  let Jquotient : C(Qboundary,Total) :=
    ⟨Quotient.lift Jsource hJsourceRespect,Jsource.continuous.quotient_lift _⟩
  have hJquotientSurj : Function.Surjective Jquotient := by
    intro z
    obtain ⟨w,hw⟩ := hJsourceSurj z
    exact ⟨Quotient.mk _ w,hw⟩
  obtain ⟨Hboundary,hHboundaryPins⟩ := hActualFiveBoundaryRunDiskHomeomorphism
  let Jnormalized : C(↥unitInterval × ↥unitInterval,Total) :=
    Jquotient.comp (⟨Hboundary.symm,Hboundary.symm.continuous⟩ : C(↥unitInterval × ↥unitInterval,Qboundary))
  have hActualNormalizedDiskAttachingSurj : Function.Surjective Jnormalized :=
    hJquotientSurj.comp Hboundary.symm.surjective
  have hActualNormalizedDiskAttachingPins (z : ↥unitInterval × ↥unitInterval) :
      Jnormalized (Fboundary z)=Gtree (Fa (M3.symm z)) := by
    rw [←hHboundaryPins z]
    change Jquotient (Hboundary.symm (Hboundary (Quotient.mk _ z)))=_
    rw [Hboundary.symm_apply_apply]
    rfl
  have hActualEightSurvivingSourcePairPins :
      ∀ (k : Fin 4) (p : Sphere) (hp : height p=0),
      closedArcSector (![ (2:Fin 6),3,4,5] k) p →
      Jnormalized (Fboundary (M3 (qFacenorm false false (diskBoundaryPoint p hp))))=
        Jnormalized (Fboundary (M3 (qFacenorm (![false,true,false,true] k)
          (![true,false,true,false] k) (diskBoundaryPoint p hp)))) := by
    intro k p hp hsector
    rw [hActualNormalizedDiskAttachingPins,hActualNormalizedDiskAttachingPins,
      M3.symm_apply_apply,M3.symm_apply_apply]
    have hN : Fa (qFacenorm false false (diskBoundaryPoint p hp))=
        northDiskFace false (diskBoundaryPoint p hp) := hFaNorth0 _
    have hS1 : Fa (qFacenorm false true (diskBoundaryPoint p hp))=
        southDiskFace true (diskBoundaryPoint p hp) := hFaSouth1 _
    have hS0 : Fa (qFacenorm true false (diskBoundaryPoint p hp))=
        southDiskFace false (diskBoundaryPoint p hp) := hFaSouth0 _
    fin_cases k
    · change closedArcSector (2:Fin 6) p at hsector
      change Gtree (Fa (qFacenorm false false (diskBoundaryPoint p hp)))=
        Gtree (Fa (qFacenorm false true (diskBoundaryPoint p hp)))
      rw [hN,hS1]
      exact congrArg Gtree (hEvenSouthTreeAttach p hp false (Or.inl hsector)).symm
    · change closedArcSector (3:Fin 6) p at hsector
      change Gtree (Fa (qFacenorm false false (diskBoundaryPoint p hp)))=
        Gtree (Fa (qFacenorm true false (diskBoundaryPoint p hp)))
      rw [hN,hS0]
      exact congrArg Gtree (hOddSouthTreeAttach p hp false (Or.inr (Or.inl hsector))).symm
    · change closedArcSector (4:Fin 6) p at hsector
      change Gtree (Fa (qFacenorm false false (diskBoundaryPoint p hp)))=
        Gtree (Fa (qFacenorm false true (diskBoundaryPoint p hp)))
      rw [hN,hS1]
      exact congrArg Gtree (hEvenSouthTreeAttach p hp false (Or.inr hsector)).symm
    · change closedArcSector (5:Fin 6) p at hsector
      change Gtree (Fa (qFacenorm false false (diskBoundaryPoint p hp)))=
        Gtree (Fa (qFacenorm true false (diskBoundaryPoint p hp)))
      rw [hN,hS0]
      exact congrArg Gtree (hOddSouthTreeAttach p hp false (Or.inr (Or.inr hsector))).symm
  let survivingRight : Fin 8 → Bool := ![false,false,false,false,false,false,true,true]
  let survivingSheet : Fin 8 → Bool := ![false,false,false,false,true,true,false,false]
  let survivingSector : Fin 8 → Fin 6 := ![2,3,4,5,4,2,5,3]
  let T0 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.2.val=0 ∧ (1/3:ℝ)≤z.1.val ∧ z.1.val≤1/2)
  let T1 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    (z.2.val=0 ∧ 0≤z.1.val ∧ z.1.val≤1/3) ∨
    (z.1.val=0 ∧ 0≤z.2.val ∧ z.2.val≤2/7))
  let T2 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=0 ∧ (2/7:ℝ)≤z.2.val ∧ z.2.val≤3/7)
  let T3 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=0 ∧ (3/7:ℝ)≤z.2.val ∧ z.2.val≤4/7)
  let T4 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=0 ∧ (5/7:ℝ)≤z.2.val ∧ z.2.val≤6/7)
  let T5 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.2.val=1 ∧ (3/10:ℝ)≤z.1.val ∧ z.1.val≤1/3)
  let T6 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    z.1.val=1 ∧ (3/7:ℝ)≤z.2.val ∧ z.2.val≤4/7)
  let T7 : Set (↥unitInterval × ↥unitInterval) := Set.ofPred (fun z =>
    (z.2.val=0 ∧ (1-(1/3:ℝ))≤z.1.val ∧ z.1.val≤1) ∨
    (z.1.val=1 ∧ 0≤z.2.val ∧ z.2.val≤2/7))
  let survivingPerimeter : Fin 8 → Set (↥unitInterval × ↥unitInterval) :=
    ![T0,T1,T2,T3,T4,T5,T6,T7]
  have hActualEightWholeSourcePerimeterImages : ∀ k : Fin 8,
      M3 '' OccNorm (survivingRight k) (survivingSheet k) (survivingSector k)=
        survivingPerimeter k := by
    intro k
    fin_cases k
    · exact hBottomN
    · exact hCorners false false
    · exact hVertical (0:Fin 4) false
    · exact hVertical (1:Fin 4) false
    · exact hVertical (2:Fin 4) false
    · exact hTop (1:Fin 2) false
    · exact hVertical (1:Fin 4) true
    · exact hCorners true false
  have hActualEightNormalizedSourceImages : ∀ k : Fin 8,
      Fboundary '' (M3 '' OccNorm (survivingRight k) (survivingSheet k) (survivingSector k))=
        Fboundary '' survivingPerimeter k := by
    intro k
    rw [hActualEightWholeSourcePerimeterImages]
  have hActualNorthFalseTreeIntersection (p : Sphere) (hp : height p=0) :
      northDiskFace false (diskBoundaryPoint p hp)∈Atree ↔ branch p := by
      dsimp [Atree]
      constructor
      · rintro ⟨v,⟨q,hq,hi,rfl⟩,he⟩
        rw [northDiskFace_boundary,northDiskFace_boundary] at he
        have hqp : q=p := congrArg projection he
        subst q
        change (Quotient.mk setoid (pieceToRaw (Sum.inl (northBoundary p hq true))) : Total)=
          Quotient.mk setoid (pieceToRaw (Sum.inl (northBoundary p hp false))) at he
        rw [Quotient.eq] at he
        change p=p ∧ (branch p ∨ label (pieceToRaw (Sum.inl (northBoundary p hq true)))=
          label (pieceToRaw (Sum.inl (northBoundary p hp false)))) at he
        have hb := he.2
        by_cases hpos : 0<seamPolynomial p <;>
          simpa [label,pieceToRaw,northBoundary,hpos] using hb
      · intro hb
        obtain ⟨i,hi⟩ := (branch_iff_mem_range p).mp hb
        obtain ⟨j,hji⟩ := cyclicBranchEquiv.surjective i
        have hbp : branchPoint (cyclicBranch j)=p := by
          change cyclicBranch j=i at hji
          rw [hji];exact hi
        let k : Fin 6 := if j=0 then 5 else j
        have hk0 : k≠0 := by fin_cases j <;> norm_num [k]
        have hk : closedArcSector k p := by
          rw [←hbp,closedArcSector_branch_iff_endpoints]
          fin_cases j <;> norm_num [k]
        refine ⟨diskBoundaryPoint p hp,⟨p,hp,⟨k,hk0,hk⟩,rfl⟩,?_⟩
        rw [northDiskFace_boundary,northDiskFace_boundary]
        apply (branch_fiber_unique hb).unique
        · exact projection_northCharacteristic _
        · exact projection_northCharacteristic _
  have hActualNormalizedNorthParameters :
      ∀ (p q : Sphere) (hp : height p=0) (hq : height q=0),
      ¬branch p → ¬branch q →
      (Jnormalized (Fboundary (M3 (qFacenorm false false (diskBoundaryPoint p hp))))=
        Jnormalized (Fboundary (M3 (qFacenorm false false (diskBoundaryPoint q hq)))) ↔ p=q) := by
    intro p q hp hq hnp hnq
    rw [hActualNormalizedDiskAttachingPins,hActualNormalizedDiskAttachingPins,
      M3.symm_apply_apply,M3.symm_apply_apply]
    have hN (r : Sphere) (hr : height r=0) : Fa (qFacenorm false false (diskBoundaryPoint r hr))=
        northDiskFace false (diskBoundaryPoint r hr) := hFaNorth0 _
    rw [hN p hp,hN q hq]
    constructor
    · intro h
      rcases (hGtreeKernel _ _).mp h with he|ha
      · have he' := congrArg projection he
        simpa [northDiskFace_boundary,projection_northCharacteristic,northBoundary] using he'
      · exact False.elim (hnp ((hActualNorthFalseTreeIntersection p hp).mp ha.1))
    · intro he
      subst q
      rfl
  have hActualEightArcsAndFiveRunsCoverPerimeter : ∀ z : ↥unitInterval × ↥unitInterval,
      ((∃ k : Fin 8, z∈survivingPerimeter k) ∨ (∃ i : Fin 5, z∈Aruns i)) ↔
      (z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1) := by
    intro z
    constructor
    · rintro (⟨k,hz⟩|⟨i,hz⟩)
      · fin_cases k
        · exact Or.inr (Or.inr (Or.inl hz.1))
        · rcases hz with hz|hz
          · exact Or.inr (Or.inr (Or.inl hz.1))
          · exact Or.inl hz.1
        · exact Or.inl hz.1
        · exact Or.inl hz.1
        · exact Or.inl hz.1
        · exact Or.inr (Or.inr (Or.inr hz.1))
        · exact Or.inr (Or.inl hz.1)
        · rcases hz with hz|hz
          · exact Or.inr (Or.inr (Or.inl hz.1))
          · exact Or.inr (Or.inl hz.1)
      · fin_cases i
        · exact Or.inl hz.1
        · rcases hz with hz|hz
          · exact Or.inr (Or.inr (Or.inr hz.1))
          · exact Or.inl hz.1
        · rcases hz with hz|hz
          · exact Or.inr (Or.inr (Or.inr hz.1))
          · exact Or.inr (Or.inl hz.1)
        · exact Or.inr (Or.inl hz.1)
        · exact Or.inr (Or.inr (Or.inl hz.1))
    · rintro (hx|hx|hy|hy)
      · by_cases h2 : z.2.val≤(2/7:ℝ)
        · exact Or.inl ⟨1,Or.inr ⟨hx,z.2.property.1,h2⟩⟩
        · by_cases h3 : z.2.val≤(3/7:ℝ)
          · exact Or.inl ⟨2,⟨hx,by linarith,h3⟩⟩
          · by_cases h4 : z.2.val≤(4/7:ℝ)
            · exact Or.inl ⟨3,⟨hx,by linarith,h4⟩⟩
            · by_cases h5 : z.2.val≤(5/7:ℝ)
              · exact Or.inr ⟨0,⟨hx,by linarith,h5⟩⟩
              · by_cases h6 : z.2.val≤(6/7:ℝ)
                · exact Or.inl ⟨4,⟨hx,by linarith,h6⟩⟩
                · exact Or.inr ⟨1,Or.inr ⟨hx,by linarith,z.2.property.2⟩⟩
      · by_cases h2 : z.2.val≤(2/7:ℝ)
        · exact Or.inl ⟨7,Or.inr ⟨hx,z.2.property.1,h2⟩⟩
        · by_cases h3 : z.2.val≤(3/7:ℝ)
          · exact Or.inr ⟨3,⟨hx,by linarith,h3⟩⟩
          · by_cases h4 : z.2.val≤(4/7:ℝ)
            · exact Or.inl ⟨6,⟨hx,by linarith,h4⟩⟩
            · exact Or.inr ⟨2,Or.inr ⟨hx,by linarith,z.2.property.2⟩⟩
      · by_cases h3 : z.1.val≤(1/3:ℝ)
        · exact Or.inl ⟨1,Or.inl ⟨hy,z.1.property.1,h3⟩⟩
        · by_cases h5 : z.1.val≤(1/2:ℝ)
          · exact Or.inl ⟨0,⟨hy,by linarith,h5⟩⟩
          · by_cases h6 : z.1.val≤(2/3:ℝ)
            · exact Or.inr ⟨4,⟨hy,by linarith,h6⟩⟩
            · exact Or.inl ⟨7,Or.inl ⟨hy,by linarith,z.1.property.2⟩⟩
      · by_cases h3 : z.1.val≤(3/10:ℝ)
        · exact Or.inr ⟨1,Or.inl ⟨hy,z.1.property.1,h3⟩⟩
        · by_cases h4 : z.1.val≤(1/3:ℝ)
          · exact Or.inl ⟨5,⟨hy,by linarith,h4⟩⟩
          · exact Or.inr ⟨2,Or.inl ⟨hy,by linarith,z.1.property.2⟩⟩
  have hActualEveryRunMeetsSurvivingArc : ∀ i : Fin 5,
      ∃ z : ↥unitInterval × ↥unitInterval, z∈Aruns i ∧ ∃ k : Fin 8, z∈survivingPerimeter k := by
    intro i
    fin_cases i
    · refine ⟨(⟨0,by norm_num⟩,⟨4/7,by norm_num⟩),?_,3,?_⟩ <;> norm_num [Aruns,Aleft,survivingPerimeter,T3]
    · refine ⟨(⟨3/10,by norm_num⟩,⟨1,by norm_num⟩),?_,5,?_⟩ <;> norm_num [Aruns,Pcorner0,survivingPerimeter,T5]
    · refine ⟨(⟨1/3,by norm_num⟩,⟨1,by norm_num⟩),?_,5,?_⟩ <;> norm_num [Aruns,Pcorner1,survivingPerimeter,T5]
    · refine ⟨(⟨1,by norm_num⟩,⟨3/7,by norm_num⟩),?_,6,?_⟩ <;> norm_num [Aruns,Aright,survivingPerimeter,T6]
    · refine ⟨(⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),?_,0,?_⟩ <;> norm_num [Aruns,Abottom,survivingPerimeter,T0]
  have hActualNormalizedEightArcsCoverSourceBoundary :
      Fboundary '' LiteralPerimeter = ⋃ k : Fin 8, Fboundary '' survivingPerimeter k := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      rcases (hActualEightArcsAndFiveRunsCoverPerimeter z).mpr hz with ⟨k,hk⟩|⟨i,hi⟩
      · exact Set.mem_iUnion.mpr ⟨k,⟨z,hk,rfl⟩⟩
      · obtain ⟨w,hwi,k,hwk⟩ := hActualEveryRunMeetsSurvivingArc i
        have he : Fboundary w=Fboundary z :=
          (hActualFiveBoundaryRunKernel w z).mpr (Or.inr ⟨i,hwi,hi⟩)
        exact Set.mem_iUnion.mpr ⟨k,⟨w,hwk,he⟩⟩
    · intro hy
      obtain ⟨k,z,hz,rfl⟩ := Set.mem_iUnion.mp hy
      refine ⟨z,?_,rfl⟩
      exact (hActualEightArcsAndFiveRunsCoverPerimeter z).mp (Or.inl ⟨k,hz⟩)
  let Nsource (p : Sphere) (hp : height p=0) := Fboundary (M3 (qFacenorm false false (diskBoundaryPoint p hp)))
  let S1source (p : Sphere) (hp : height p=0) := Fboundary (M3 (qFacenorm false true (diskBoundaryPoint p hp)))
  let S0source (p : Sphere) (hp : height p=0) := Fboundary (M3 (qFacenorm true false (diskBoundaryPoint p hp)))
  let Tsource (p : Sphere) (hp : height p=0) := Fboundary (M3 (qFacenorm true true (diskBoundaryPoint p hp)))
  let Rsurviving : (↥unitInterval × ↥unitInterval) → (↥unitInterval × ↥unitInterval) → Prop :=
    fun z w => ∃ k : Fin 4, ∃ p : Sphere, ∃ hp : height p=0,
      closedArcSector (![(2:Fin 6),3,4,5] k) p ∧ z=Nsource p hp ∧
      w=(if k.val % 2=0 then S1source p hp else S0source p hp)
  have hSourcePair2 (p : Sphere) (hp : height p=0) (hc : closedArcSector (2:Fin 6) p) :
      Relation.EqvGen Rsurviving (Nsource p hp) (S1source p hp) :=
    Relation.EqvGen.rel _ _ ⟨0,p,hp,hc,rfl,rfl⟩
  have hSourcePair3 (p : Sphere) (hp : height p=0) (hc : closedArcSector (3:Fin 6) p) :
      Relation.EqvGen Rsurviving (Nsource p hp) (S0source p hp) :=
    Relation.EqvGen.rel _ _ ⟨1,p,hp,hc,rfl,rfl⟩
  have hSourcePair4 (p : Sphere) (hp : height p=0) (hc : closedArcSector (4:Fin 6) p) :
      Relation.EqvGen Rsurviving (Nsource p hp) (S1source p hp) :=
    Relation.EqvGen.rel _ _ ⟨2,p,hp,hc,rfl,rfl⟩
  have hSourcePair5 (p : Sphere) (hp : height p=0) (hc : closedArcSector (5:Fin 6) p) :
      Relation.EqvGen Rsurviving (Nsource p hp) (S0source p hp) :=
    Relation.EqvGen.rel _ _ ⟨3,p,hp,hc,rfl,rfl⟩
  have hActualSelectedSeam0Left (p : Sphere) (hp : height p=0) (hc : closedArcSector (0:Fin 6) p) :
      Nsource p hp=S1source p hp := by
    apply congrArg (fun q => Fboundary (M3 q))
    change Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inl (diskBoundaryPoint p hp))))=
      Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inr (diskBoundaryPoint p hp))))
    apply congrArg (fun q : Q0norm => Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inl q))
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨p,hp,hc,rfl,rfl⟩)
  have hActualSelectedSeam0Right (p : Sphere) (hp : height p=0) (hc : closedArcSector (0:Fin 6) p) :
      Tsource p hp=S0source p hp := by
    apply congrArg (fun q => Fboundary (M3 q))
    change Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inl (diskBoundaryPoint p hp))))=
      Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inr (diskBoundaryPoint p hp))))
    apply congrArg (fun q : Q0norm => Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inr q))
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨p,hp,hc,rfl,rfl⟩)
  have hActualSelectedSeam1 (p : Sphere) (hp : height p=0) (hc : closedArcSector (1:Fin 6) p) :
      Nsource p hp=S0source p hp := by
    apply congrArg (fun q => Fboundary (M3 q))
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨p,hp,hc,rfl,rfl⟩)
  have hSourcePointMembership (right sheet : Bool) (i : Fin 6) (p : Sphere) (hp : height p=0)
      (hc : closedArcSector i p) : M3 (qFacenorm right sheet (diskBoundaryPoint p hp))∈M3 '' OccNorm right sheet i :=
    ⟨qFacenorm right sheet (diskBoundaryPoint p hp),⟨p,hp,hc,rfl⟩,rfl⟩
  have hSourceNorthernTreePerimeter (i : Fin 6) (hi : i≠0) (p : Sphere) (hp : height p=0)
      (hc : closedArcSector i p) : M3 (qFacenorm true true (diskBoundaryPoint p hp))∈Aruns 2 := by
    have hq : qFacenorm true true (diskBoundaryPoint p hp)∈UbigCorner := by
      fin_cases i
      · exact False.elim (hi rfl)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨p,hp,hc,rfl⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨p,hp,hc,rfl⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨p,hp,hc,rfl⟩))
      · exact Or.inl (Or.inr ⟨p,hp,hc,rfl⟩)
      · exact Or.inr ⟨p,hp,hc,rfl⟩
    have hm : M3 (qFacenorm true true (diskBoundaryPoint p hp))∈M3 '' UbigCorner :=
      ⟨_,hq,rfl⟩
    rw [hActualBigCornerSourceImage] at hm
    exact hm
  have hSourceSouthOneLargePerimeter (p : Sphere) (hp : height p=0) (hc : closedArcSector (1:Fin 6) p) :
      M3 (qFacenorm false true (diskBoundaryPoint p hp))∈Aruns 2 := by
    have hq : qFacenorm false true (diskBoundaryPoint p hp)∈UbigCorner :=
      Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨p,hp,hc,rfl⟩))))
    have hm : M3 (qFacenorm false true (diskBoundaryPoint p hp))∈M3 '' UbigCorner := ⟨_,hq,rfl⟩
    rw [hActualBigCornerSourceImage] at hm
    exact hm
  have hSourceSouthThreePerimeter (p : Sphere) (hp : height p=0) (hc : closedArcSector (3:Fin 6) p) :
      M3 (qFacenorm false true (diskBoundaryPoint p hp))∈Aruns 1 := by
    have hm := hSourcePointMembership false true 3 p hp hc
    rw [hOccSmallCornerSource] at hm
    exact hm
  have hSourceSouthFivePerimeter (p : Sphere) (hp : height p=0) (hc : closedArcSector (5:Fin 6) p) :
      M3 (qFacenorm false true (diskBoundaryPoint p hp))∈Aruns 0 := by
    have hm := hSourcePointMembership false true 5 p hp hc
    rw [hOccLeftSource] at hm
    exact hm
  have hSourceSouthTwoPerimeter (p : Sphere) (hp : height p=0) (hc : closedArcSector (2:Fin 6) p) :
      M3 (qFacenorm true false (diskBoundaryPoint p hp))∈Aruns 4 := by
    have hm := hSourcePointMembership true false 2 p hp hc
    rw [hOccBottomSource] at hm
    exact hm
  have hSourceSouthFourPerimeter (p : Sphere) (hp : height p=0) (hc : closedArcSector (4:Fin 6) p) :
      M3 (qFacenorm true false (diskBoundaryPoint p hp))∈Aruns 3 := by
    have hm := hSourcePointMembership true false 4 p hp hc
    rw [hOccRightSource] at hm
    exact hm
  let bsource (j : Fin 6) := branchPoint (cyclicBranch j)
  have hSourceBranchSectorStart (j : Fin 6) : closedArcSector j (bsource j) := by
    rw [closedArcSector_branch_iff_endpoints]
    exact Or.inl rfl
  have hSourceBranchSectorEnd (j : Fin 6) : closedArcSector j (bsource (j+1)) := by
    rw [closedArcSector_branch_iff_endpoints]
    exact Or.inr rfl
  have hbsource (j : Fin 6) : height (bsource j)=0 := (hSourceBranchSectorStart j).1
  have hb0five : closedArcSector (5:Fin 6) (bsource 0) := by
    exact hSourceBranchSectorEnd 5
  let sourceRoot := Tsource (bsource 0) (hbsource 0)
  have hActualNorthernTreeOneVertex (i : Fin 6) (hi : i≠0) (p : Sphere) (hp : height p=0)
      (hc : closedArcSector i p) : Tsource p hp=sourceRoot := by
    exact (hActualFiveBoundaryRunKernel _ _).mpr (Or.inr
      ⟨2,hSourceNorthernTreePerimeter i hi p hp hc,
        hSourceNorthernTreePerimeter 5 (by decide) _ _ hb0five⟩)
  have hActualSouthOneOneVertex (p : Sphere) (hp : height p=0) (hc : closedArcSector (1:Fin 6) p) :
      S1source p hp=sourceRoot := by
    exact (hActualFiveBoundaryRunKernel _ _).mpr (Or.inr
      ⟨2,hSourceSouthOneLargePerimeter p hp hc,
        hSourceNorthernTreePerimeter 5 (by decide) _ _ hb0five⟩)
  have hActualSouthThreeOneVertex (p : Sphere) (hp : height p=0) (hc : closedArcSector (3:Fin 6) p) :
      S1source p hp=S1source (bsource 3) (hbsource 3) := by
    exact (hActualFiveBoundaryRunKernel _ _).mpr (Or.inr
      ⟨1,hSourceSouthThreePerimeter p hp hc,
        hSourceSouthThreePerimeter _ _ (hSourceBranchSectorStart 3)⟩)
  have hActualSouthFiveOneVertex (p : Sphere) (hp : height p=0) (hc : closedArcSector (5:Fin 6) p) :
      S1source p hp=S1source (bsource 0) (hbsource 0) := by
    exact (hActualFiveBoundaryRunKernel _ _).mpr (Or.inr
      ⟨0,hSourceSouthFivePerimeter p hp hc,
        hSourceSouthFivePerimeter _ _ (hb0five)⟩)
  have hActualSouthTwoOneVertex (p : Sphere) (hp : height p=0) (hc : closedArcSector (2:Fin 6) p) :
      S0source p hp=S0source (bsource 2) (hbsource 2) := by
    exact (hActualFiveBoundaryRunKernel _ _).mpr (Or.inr
      ⟨4,hSourceSouthTwoPerimeter p hp hc,
        hSourceSouthTwoPerimeter _ _ (hSourceBranchSectorStart 2)⟩)
  have hActualSouthFourOneVertex (p : Sphere) (hp : height p=0) (hc : closedArcSector (4:Fin 6) p) :
      S0source p hp=S0source (bsource 4) (hbsource 4) := by
    exact (hActualFiveBoundaryRunKernel _ _).mpr (Or.inr
      ⟨3,hSourceSouthFourPerimeter p hp hc,
        hSourceSouthFourPerimeter _ _ (hSourceBranchSectorStart 4)⟩)
  have hActualLeftVertexIdentified : Relation.EqvGen Rsurviving
      (S1source (bsource 0) (hbsource 0)) sourceRoot := by
    have hp := hSourcePair5 (bsource 0) (hbsource 0) hb0five
    rw [hActualSelectedSeam0Left _ _ (hSourceBranchSectorStart 0),
      ←hActualSelectedSeam0Right _ _ (hSourceBranchSectorStart 0)] at hp
    exact hp
  have hActualBottomVertexIdentified : Relation.EqvGen Rsurviving
      (S0source (bsource 2) (hbsource 2)) sourceRoot := by
    have hp := hSourcePair2 (bsource 2) (hbsource 2) (hSourceBranchSectorStart 2)
    have he : Nsource (bsource 2) (hbsource 2)=S0source (bsource 2) (hbsource 2) :=
      hActualSelectedSeam1 _ _ (hSourceBranchSectorEnd 1)
    have hf : S1source (bsource 2) (hbsource 2)=sourceRoot :=
      hActualSouthOneOneVertex _ _ (hSourceBranchSectorEnd 1)
    exact Eq.mp (congrArg₂ (Relation.EqvGen Rsurviving) he hf) hp
  have hActualSmallCornerVertexIdentified : Relation.EqvGen Rsurviving
      (S1source (bsource 3) (hbsource 3)) sourceRoot := by
    have h2 := hSourcePair2 (bsource 3) (hbsource 3) (hSourceBranchSectorEnd 2)
    have h3 := hSourcePair3 (bsource 3) (hbsource 3) (hSourceBranchSectorStart 3)
    have h := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h2) h3
    have he : S0source (bsource 3) (hbsource 3)=S0source (bsource 2) (hbsource 2) :=
      hActualSouthTwoOneVertex _ _ (hSourceBranchSectorEnd 2)
    have hc : Relation.EqvGen Rsurviving (S0source (bsource 3) (hbsource 3)) sourceRoot :=
      Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualBottomVertexIdentified)
    exact Relation.EqvGen.trans _ _ _ h hc
  have hActualRightVertexIdentified : Relation.EqvGen Rsurviving
      (S0source (bsource 4) (hbsource 4)) sourceRoot := by
    have h3 := hSourcePair3 (bsource 4) (hbsource 4) (hSourceBranchSectorEnd 3)
    have h4 := hSourcePair4 (bsource 4) (hbsource 4) (hSourceBranchSectorStart 4)
    have h := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h3) h4
    have he : S1source (bsource 4) (hbsource 4)=S1source (bsource 3) (hbsource 3) :=
      hActualSouthThreeOneVertex _ _ (hSourceBranchSectorEnd 3)
    have hc : Relation.EqvGen Rsurviving (S1source (bsource 4) (hbsource 4)) sourceRoot :=
      Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualSmallCornerVertexIdentified)
    exact Relation.EqvGen.trans _ _ _ h hc
  have hActualAllFiveBoundaryRunVerticesIdentified : ∀ (i : Fin 5) z,
      z∈Aruns i → Relation.EqvGen Rsurviving (Fboundary z) sourceRoot := by
    intro i z hz
    fin_cases i
    · have he : Fboundary z=S1source (bsource 0) (hbsource 0) :=
        (hActualFiveBoundaryRunKernel z _).mpr (Or.inr ⟨0,hz,hSourceSouthFivePerimeter (bsource 0) (hbsource 0) hb0five⟩)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualLeftVertexIdentified)
    · have he : Fboundary z=S1source (bsource 3) (hbsource 3) :=
        (hActualFiveBoundaryRunKernel z _).mpr (Or.inr ⟨1,hz,hSourceSouthThreePerimeter (bsource 3) (hbsource 3) (hSourceBranchSectorStart 3)⟩)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualSmallCornerVertexIdentified)
    · have he : Fboundary z=sourceRoot :=
        (hActualFiveBoundaryRunKernel z _).mpr (Or.inr ⟨2,hz,hSourceNorthernTreePerimeter 5 (by decide) (bsource 0) (hbsource 0) hb0five⟩)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (Relation.EqvGen.refl sourceRoot)
    · have he : Fboundary z=S0source (bsource 4) (hbsource 4) :=
        (hActualFiveBoundaryRunKernel z _).mpr (Or.inr ⟨3,hz,hSourceSouthFourPerimeter (bsource 4) (hbsource 4) (hSourceBranchSectorStart 4)⟩)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualRightVertexIdentified)
    · have he : Fboundary z=S0source (bsource 2) (hbsource 2) :=
        (hActualFiveBoundaryRunKernel z _).mpr (Or.inr ⟨4,hz,hSourceSouthTwoPerimeter (bsource 2) (hbsource 2) (hSourceBranchSectorStart 2)⟩)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualBottomVertexIdentified)
  have hActualAllNorthernBranchVerticesIdentified : ∀ j : Fin 6,
      Relation.EqvGen Rsurviving (Nsource (bsource j) (hbsource j)) sourceRoot := by
    intro j
    fin_cases j
    · have he : Nsource (bsource 0) (hbsource 0)=S1source (bsource 0) (hbsource 0) :=
        hActualSelectedSeam0Left _ _ (hSourceBranchSectorStart 0)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualLeftVertexIdentified)
    · have he1 : Nsource (bsource 1) (hbsource 1)=S0source (bsource 1) (hbsource 1) :=
        hActualSelectedSeam1 _ _ (hSourceBranchSectorStart 1)
      have he0 : Tsource (bsource 1) (hbsource 1)=S0source (bsource 1) (hbsource 1) :=
        hActualSelectedSeam0Right _ _ (hSourceBranchSectorEnd 0)
      have heT : Tsource (bsource 1) (hbsource 1)=sourceRoot :=
        hActualNorthernTreeOneVertex 1 (by decide) _ _ (hSourceBranchSectorStart 1)
      have he := he1.trans (he0.symm.trans heT)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (Relation.EqvGen.refl sourceRoot)
    · have he : Nsource (bsource 2) (hbsource 2)=S0source (bsource 2) (hbsource 2) :=
        hActualSelectedSeam1 _ _ (hSourceBranchSectorEnd 1)
      exact Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualBottomVertexIdentified)
    · exact Relation.EqvGen.trans _ _ _
        (hSourcePair2 _ _ (hSourceBranchSectorEnd 2)) hActualSmallCornerVertexIdentified
    · have he : S1source (bsource 4) (hbsource 4)=S1source (bsource 3) (hbsource 3) :=
        hActualSouthThreeOneVertex _ _ (hSourceBranchSectorEnd 3)
      have hc : Relation.EqvGen Rsurviving (S1source (bsource 4) (hbsource 4)) sourceRoot :=
        Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualSmallCornerVertexIdentified)
      exact Relation.EqvGen.trans _ _ _ (hSourcePair4 _ _ (hSourceBranchSectorStart 4)) hc
    · have he : S1source (bsource 5) (hbsource 5)=S1source (bsource 0) (hbsource 0) :=
        hActualSouthFiveOneVertex _ _ (hSourceBranchSectorStart 5)
      have hc : Relation.EqvGen Rsurviving (S1source (bsource 5) (hbsource 5)) sourceRoot :=
        Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) (hActualLeftVertexIdentified)
      exact Relation.EqvGen.trans _ _ _ (hSourcePair4 _ _ (hSourceBranchSectorEnd 4)) hc
  have hSourceEqvOfEquality {z w : ↥unitInterval × ↥unitInterval} (he : z=w) :
      Relation.EqvGen Rsurviving z w :=
    Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u w) he) (Relation.EqvGen.refl w)
  have hActualAllSixSectorSourceAttachments : ∀ (i : Fin 6) (s : Bool)
      (p : Sphere) (hp : height p=0), closedArcSector i p →
      Relation.EqvGen Rsurviving (if s then Tsource p hp else Nsource p hp)
        (if (if i.val % 2=0 then !s else s) then S1source p hp else S0source p hp) := by
    intro i s p hp hc
    fin_cases i <;> cases s
    · exact hSourceEqvOfEquality (hActualSelectedSeam0Left p hp hc)
    · exact hSourceEqvOfEquality (hActualSelectedSeam0Right p hp hc)
    · exact hSourceEqvOfEquality (hActualSelectedSeam1 p hp hc)
    · have hn : Relation.EqvGen Rsurviving (Tsource p hp) sourceRoot :=
        hSourceEqvOfEquality (hActualNorthernTreeOneVertex 1 (by decide) p hp hc)
      have hs : Relation.EqvGen Rsurviving (S1source p hp) sourceRoot :=
        hSourceEqvOfEquality (hActualSouthOneOneVertex p hp hc)
      exact Relation.EqvGen.trans _ _ _ hn (Relation.EqvGen.symm _ _ hs)
    · exact hSourcePair2 p hp hc
    · have hn : Relation.EqvGen Rsurviving (Tsource p hp) sourceRoot :=
        hSourceEqvOfEquality (hActualNorthernTreeOneVertex 2 (by decide) p hp hc)
      have he := hActualSouthTwoOneVertex p hp hc
      have hs : Relation.EqvGen Rsurviving (S0source p hp) sourceRoot :=
        Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) hActualBottomVertexIdentified
      exact Relation.EqvGen.trans _ _ _ hn (Relation.EqvGen.symm _ _ hs)
    · exact hSourcePair3 p hp hc
    · have hn : Relation.EqvGen Rsurviving (Tsource p hp) sourceRoot :=
        hSourceEqvOfEquality (hActualNorthernTreeOneVertex 3 (by decide) p hp hc)
      have he := hActualSouthThreeOneVertex p hp hc
      have hs : Relation.EqvGen Rsurviving (S1source p hp) sourceRoot :=
        Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) hActualSmallCornerVertexIdentified
      exact Relation.EqvGen.trans _ _ _ hn (Relation.EqvGen.symm _ _ hs)
    · exact hSourcePair4 p hp hc
    · have hn : Relation.EqvGen Rsurviving (Tsource p hp) sourceRoot :=
        hSourceEqvOfEquality (hActualNorthernTreeOneVertex 4 (by decide) p hp hc)
      have he := hActualSouthFourOneVertex p hp hc
      have hs : Relation.EqvGen Rsurviving (S0source p hp) sourceRoot :=
        Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) hActualRightVertexIdentified
      exact Relation.EqvGen.trans _ _ _ hn (Relation.EqvGen.symm _ _ hs)
    · exact hSourcePair5 p hp hc
    · have hn : Relation.EqvGen Rsurviving (Tsource p hp) sourceRoot :=
        hSourceEqvOfEquality (hActualNorthernTreeOneVertex 5 (by decide) p hp hc)
      have he := hActualSouthFiveOneVertex p hp hc
      have hs : Relation.EqvGen Rsurviving (S1source p hp) sourceRoot :=
        Eq.mpr (congrArg (fun u => Relation.EqvGen Rsurviving u sourceRoot) he) hActualLeftVertexIdentified
      exact Relation.EqvGen.trans _ _ _ hn (Relation.EqvGen.symm _ _ hs)
  have hActualNorthFalseBranchClass (p : Sphere) (hp : height p=0) (hb : branch p) :
      Relation.EqvGen Rsurviving (Nsource p hp) sourceRoot := by
    obtain ⟨i,hi⟩ := (branch_iff_mem_range p).mp hb
    obtain ⟨j,hj⟩ := cyclicBranchEquiv.surjective i
    have he : bsource j=p := by
      change cyclicBranch j=i at hj
      change branchPoint (cyclicBranch j)=p
      exact (congrArg branchPoint hj).trans hi
    clear hi
    subst p
    exact hActualAllNorthernBranchVerticesIdentified j
  have hActualNorthTrueBranchClass (p : Sphere) (hp : height p=0) (hb : branch p) :
      Tsource p hp=sourceRoot := by
    obtain ⟨i,hi⟩ := (branch_iff_mem_range p).mp hb
    obtain ⟨j,hj⟩ := cyclicBranchEquiv.surjective i
    have he : bsource j=p := by
      change cyclicBranch j=i at hj
      change branchPoint (cyclicBranch j)=p
      exact (congrArg branchPoint hj).trans hi
    clear hi
    subst p
    by_cases hj0 : j=0
    · subst j
      exact hActualNorthernTreeOneVertex 5 (by decide) _ _ hb0five
    · exact hActualNorthernTreeOneVertex j hj0 _ _ (hSourceBranchSectorStart j)
  have hActualSouthBranchIndexClass : ∀ (j : Fin 6) (sheet : Bool),
      Relation.EqvGen Rsurviving
        (if sheet then S1source (bsource j) (hbsource j) else S0source (bsource j) (hbsource j)) sourceRoot := by
    intro j sheet
    fin_cases j <;> cases sheet
    · have hpair := hActualAllSixSectorSourceAttachments 5 false (bsource 0) (hbsource 0) hb0five
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hActualAllNorthernBranchVerticesIdentified 0)
    · have hpair := hActualAllSixSectorSourceAttachments 5 true (bsource 0) (hbsource 0) hb0five
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hSourceEqvOfEquality (hActualNorthernTreeOneVertex 5 (by decide) _ _ hb0five))
    · have hpair := hActualAllSixSectorSourceAttachments 1 false (bsource 1) (hbsource 1) (hSourceBranchSectorStart 1)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hActualAllNorthernBranchVerticesIdentified 1)
    · have hpair := hActualAllSixSectorSourceAttachments 1 true (bsource 1) (hbsource 1) (hSourceBranchSectorStart 1)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hSourceEqvOfEquality (hActualNorthernTreeOneVertex 1 (by decide) _ _ (hSourceBranchSectorStart 1)))
    · have hpair := hActualAllSixSectorSourceAttachments 2 true (bsource 2) (hbsource 2) (hSourceBranchSectorStart 2)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hSourceEqvOfEquality (hActualNorthernTreeOneVertex 2 (by decide) _ _ (hSourceBranchSectorStart 2)))
    · have hpair := hActualAllSixSectorSourceAttachments 2 false (bsource 2) (hbsource 2) (hSourceBranchSectorStart 2)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hActualAllNorthernBranchVerticesIdentified 2)
    · have hpair := hActualAllSixSectorSourceAttachments 3 false (bsource 3) (hbsource 3) (hSourceBranchSectorStart 3)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hActualAllNorthernBranchVerticesIdentified 3)
    · have hpair := hActualAllSixSectorSourceAttachments 3 true (bsource 3) (hbsource 3) (hSourceBranchSectorStart 3)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hSourceEqvOfEquality (hActualNorthernTreeOneVertex 3 (by decide) _ _ (hSourceBranchSectorStart 3)))
    · have hpair := hActualAllSixSectorSourceAttachments 4 true (bsource 4) (hbsource 4) (hSourceBranchSectorStart 4)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hSourceEqvOfEquality (hActualNorthernTreeOneVertex 4 (by decide) _ _ (hSourceBranchSectorStart 4)))
    · have hpair := hActualAllSixSectorSourceAttachments 4 false (bsource 4) (hbsource 4) (hSourceBranchSectorStart 4)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hActualAllNorthernBranchVerticesIdentified 4)
    · have hpair := hActualAllSixSectorSourceAttachments 5 false (bsource 5) (hbsource 5) (hSourceBranchSectorStart 5)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hActualAllNorthernBranchVerticesIdentified 5)
    · have hpair := hActualAllSixSectorSourceAttachments 5 true (bsource 5) (hbsource 5) (hSourceBranchSectorStart 5)
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hpair) (hSourceEqvOfEquality (hActualNorthernTreeOneVertex 5 (by decide) _ _ (hSourceBranchSectorStart 5)))
  have hActualSouthBranchClass (p : Sphere) (hp : height p=0) (hb : branch p) (sheet : Bool) :
      Relation.EqvGen Rsurviving (if sheet then S1source p hp else S0source p hp) sourceRoot := by
    obtain ⟨i,hi⟩ := (branch_iff_mem_range p).mp hb
    obtain ⟨j,hj⟩ := cyclicBranchEquiv.surjective i
    have he : bsource j=p := by
      change cyclicBranch j=i at hj
      change branchPoint (cyclicBranch j)=p
      exact (congrArg branchPoint hj).trans hi
    clear hi
    subst p
    exact hActualSouthBranchIndexClass j sheet
  have hActualPhysicalNorthSouthSourcePair (p : Sphere) (hp : height p=0) (s t : Bool)
      (hl : label (equatorRaw p hp true s)=label (equatorRaw p hp false t)) :
      Relation.EqvGen Rsurviving (if s then Tsource p hp else Nsource p hp)
        (if t then S1source p hp else S0source p hp) := by
    by_cases hb : branch p
    · have hn : Relation.EqvGen Rsurviving (if s then Tsource p hp else Nsource p hp) sourceRoot := by
        cases s
        · exact hActualNorthFalseBranchClass p hp hb
        · exact hSourceEqvOfEquality (hActualNorthTrueBranchClass p hp hb)
      have hs := hActualSouthBranchClass p hp hb t
      exact Relation.EqvGen.trans _ _ _ hn (Relation.EqvGen.symm _ _ hs)
    · have he : northCharacteristic (northBoundary p hp s)=southCharacteristic (southBoundary p hp t) := by
        change (Quotient.mk setoid (equatorRaw p hp true s) : Total)=Quotient.mk setoid (equatorRaw p hp false t)
        exact Quotient.sound ⟨rfl,Or.inr hl⟩
      have hbool := ((boundary_attach p hp s t).mp he).resolve_left hb
      have ht : t=(s ^^ decide (0 < seamPolynomial p)) := by
        cases s <;> cases t <;> by_cases hv : 0 < seamPolynomial p <;> simp [hv] at hbool ⊢
      obtain ⟨i,hi⟩ := arcSector_exists hp hb
      have hd : decide (0 < seamPolynomial p)=decide (i.val % 2=0) := by
        by_cases he : i.val % 2=0
        · have hs := (arcSector_alternating_sign hi).mpr he
          simp only [hs,he,decide_true]
        · have hs : ¬0 < seamPolynomial p := fun h => he ((arcSector_alternating_sign hi).mp h)
          simp only [hs,he,decide_false]
      have ht' : t=(if i.val % 2=0 then !s else s) := by
        rw [ht,hd]
        cases s <;> by_cases hv : i.val % 2=0 <;> simp [hv]
      clear ht
      subst t
      exact hActualAllSixSectorSourceAttachments i s p hp (arcSector_subset_closed hi)
  let sourceDisk (p : Sphere) := coordinateDiskClosedBallHomeomorph (diskProjection p)
  let sourceFromRaw (x : Raw) :=
    if x.val.2.1 then
      if x.val.2.2 then Fboundary (M3 (qFacenorm true true (sourceDisk x.val.1)))
      else Fboundary (M3 (qFacenorm false false (sourceDisk x.val.1)))
    else
      if x.val.2.2 then Fboundary (M3 (qFacenorm false true (sourceDisk x.val.1)))
      else Fboundary (M3 (qFacenorm true false (sourceDisk x.val.1)))
  have hActualSourceRawBranchClass (x : Raw) (hb : branch x.val.1) :
      Relation.EqvGen Rsurviving (sourceFromRaw x) sourceRoot := by
    rcases x with ⟨⟨p,b,s⟩,hx⟩
    cases b <;> cases s
    · exact hActualSouthBranchClass p hb.1 hb false
    · exact hActualSouthBranchClass p hb.1 hb true
    · exact hActualNorthFalseBranchClass p hb.1 hb
    · exact hSourceEqvOfEquality (hActualNorthTrueBranchClass p hb.1 hb)
  have hActualFullSourceRawRelationRespected : ∀ (x y : Raw), Rel x y →
      Relation.EqvGen Rsurviving (sourceFromRaw x) (sourceFromRaw y) := by
    intro x y h
    rcases x with ⟨⟨p,b,s⟩,hx⟩
    rcases y with ⟨⟨q,c,t⟩,hy⟩
    rcases h with ⟨hbase,hlabel⟩
    change p=q at hbase
    subst q
    rcases hlabel with hb|hl
    · have hleft := hActualSourceRawBranchClass (⟨(p,b,s),hx⟩ : Raw) hb
      have hright := hActualSourceRawBranchClass (⟨(p,c,t),hy⟩ : Raw) hb
      exact Relation.EqvGen.trans _ _ _ hleft (Relation.EqvGen.symm _ _ hright)
    · cases b <;> cases c
      · have hs : s=t := by simpa [label] using hl
        subst t
        exact Relation.EqvGen.refl _
      · have hp : height p=0 := by
          change height p ≤ 0 at hx
          change 0 ≤ height p at hy
          exact le_antisymm hx hy
        change Relation.EqvGen Rsurviving (if s then S1source p hp else S0source p hp)
          (if t then Tsource p hp else Nsource p hp)
        exact Relation.EqvGen.symm _ _ (hActualPhysicalNorthSouthSourcePair p hp t s hl.symm)
      · have hp : height p=0 := by
          change 0 ≤ height p at hx
          change height p ≤ 0 at hy
          exact le_antisymm hy hx
        change Relation.EqvGen Rsurviving (if s then Tsource p hp else Nsource p hp)
          (if t then S1source p hp else S0source p hp)
        exact hActualPhysicalNorthSouthSourcePair p hp s t hl
      · have hs : s=t := by
          cases s <;> cases t <;> by_cases hp : 0 < seamPolynomial p <;> simp [label,hp] at hl ⊢
        subst t
        exact Relation.EqvGen.refl _
  let Qsource := Quotient (Relation.EqvGen.setoid Rsurviving)
  have hSourceQFaceContinuous (right sheet : Bool) : Continuous (qFacenorm right sheet) := by
    cases right <;> cases sheet <;> dsimp [qFacenorm,q0norm]
    · exact continuous_quotient_mk'.comp (continuous_inl.comp (continuous_quotient_mk'.comp continuous_inl))
    · exact continuous_quotient_mk'.comp (continuous_inl.comp (continuous_quotient_mk'.comp continuous_inr))
    · exact continuous_quotient_mk'.comp (continuous_inr.comp (continuous_quotient_mk'.comp continuous_inr))
    · exact continuous_quotient_mk'.comp (continuous_inr.comp (continuous_quotient_mk'.comp continuous_inl))
  have hSourceRawFaceContinuous (right sheet : Bool) :
      Continuous (fun x : Raw => Fboundary (M3 (qFacenorm right sheet (sourceDisk x.val.1)))) :=
    Fboundary.continuous.comp (M3.continuous.comp ((hSourceQFaceContinuous right sheet).comp
      (coordinateDiskClosedBallHomeomorph.continuous.comp (diskProjection_continuous.comp
        (continuous_fst.comp continuous_subtype_val)))))
  have hBoolTrueClopen : IsClopen (Set.ofPred (fun b : Bool => b=true)) := isClopen_discrete _
  have hRawBankClopen : IsClopen (Set.ofPred (fun x : Raw => x.val.2.1=true)) :=
    hBoolTrueClopen.preimage (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
  have hRawSheetClopen : IsClopen (Set.ofPred (fun x : Raw => x.val.2.2=true)) :=
    hBoolTrueClopen.preimage (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))
  have hActualSourceFromRawContinuous : Continuous sourceFromRaw := by
    apply Continuous.if
    · intro x hx
      rw [hRawBankClopen.frontier_eq] at hx
      exact False.elim hx
    · apply Continuous.if
      · intro x hx
        rw [hRawSheetClopen.frontier_eq] at hx
        exact False.elim hx
      · exact hSourceRawFaceContinuous true true
      · exact hSourceRawFaceContinuous false false
    · apply Continuous.if
      · intro x hx
        rw [hRawSheetClopen.frontier_eq] at hx
        exact False.elim hx
      · exact hSourceRawFaceContinuous false true
      · exact hSourceRawFaceContinuous true false
  have hRawToSourceQuotientRespect (x y : Raw) (h : Rel x y) :
      (Quotient.mk (Relation.EqvGen.setoid Rsurviving) (sourceFromRaw x) : Qsource)=
        Quotient.mk (Relation.EqvGen.setoid Rsurviving) (sourceFromRaw y) :=
    Quotient.sound (hActualFullSourceRawRelationRespected x y h)
  let Boriginal : C(Total,Qsource) :=
    ⟨Quotient.lift (fun x => Quotient.mk (Relation.EqvGen.setoid Rsurviving) (sourceFromRaw x))
        hRawToSourceQuotientRespect,
      (continuous_quotient_mk'.comp hActualSourceFromRawContinuous).quotient_lift _⟩
  have hSourceDiskNorth (sheet : Bool) (v : StandardDisk) : sourceDisk (diskToNorth (sheet,v)).val.1=v := by
    change coordinateDiskClosedBallHomeomorph (northHemisphereDiskHomeomorph
      (northHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)))=v
    rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply]
  have hSourceDiskSouth (sheet : Bool) (v : StandardDisk) : sourceDisk (diskToSouth (sheet,v)).val.1=v := by
    change coordinateDiskClosedBallHomeomorph (southHemisphereDiskHomeomorph
      (southHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)))=v
    rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply]
  have hBoriginalNorth (sheet : Bool) (v : StandardDisk) :
      Boriginal (northDiskFace sheet v)=
        Quotient.mk (Relation.EqvGen.setoid Rsurviving) (Fboundary (M3 (qFacenorm sheet sheet v))) := by
    cases sheet
    · change Quotient.mk (Relation.EqvGen.setoid Rsurviving)
        (Fboundary (M3 (qFacenorm false false (sourceDisk (diskToNorth (false,v)).val.1))))=_
      rw [hSourceDiskNorth]
    · change Quotient.mk (Relation.EqvGen.setoid Rsurviving)
        (Fboundary (M3 (qFacenorm true true (sourceDisk (diskToNorth (true,v)).val.1))))=_
      rw [hSourceDiskNorth]
  have hBoriginalSouth (sheet : Bool) (v : StandardDisk) :
      Boriginal (southDiskFace sheet v)=
        Quotient.mk (Relation.EqvGen.setoid Rsurviving) (Fboundary (M3 (qFacenorm (!sheet) sheet v))) := by
    cases sheet
    · change Quotient.mk (Relation.EqvGen.setoid Rsurviving)
        (Fboundary (M3 (qFacenorm true false (sourceDisk (diskToSouth (false,v)).val.1))))=_
      rw [hSourceDiskSouth]
      simp only [Bool.not_false]
    · change Quotient.mk (Relation.EqvGen.setoid Rsurviving)
        (Fboundary (M3 (qFacenorm false true (sourceDisk (diskToSouth (true,v)).val.1))))=_
      rw [hSourceDiskSouth]
      simp only [Bool.not_true]
  have hBoriginalTreeConstant (x : Total) (hx : x∈Atree) :
      Boriginal x=Quotient.mk (Relation.EqvGen.setoid Rsurviving) sourceRoot := by
    rcases hx with ⟨v,⟨p,hp,⟨i,hi0,hi⟩,rfl⟩,rfl⟩
    rw [hBoriginalNorth]
    exact congrArg (Quotient.mk (Relation.EqvGen.setoid Rsurviving))
      (hActualNorthernTreeOneVertex i hi0 p hp hi)
  let Bafter (z : Total) := Boriginal (Classical.choose (hGtreeSurj z))
  have hActualBafterPins (x : Total) : Bafter (Gtree x)=Boriginal x := by
    have he : Gtree (Classical.choose (hGtreeSurj (Gtree x)))=Gtree x :=
      Classical.choose_spec (hGtreeSurj (Gtree x))
    rcases (hGtreeKernel _ _).mp he with he|ha
    · exact congrArg Boriginal he
    · exact (hBoriginalTreeConstant _ ha.1).trans (hBoriginalTreeConstant x ha.2).symm
  letI : CompactSpace Total := total_compact
  letI : T2Space Total := actual_t2Space
  have hGtreeQuotientMap : IsQuotientMap Gtree :=
    Gtree.continuous.isClosedMap.isQuotientMap Gtree.continuous hGtreeSurj
  have hActualBafterContinuous : Continuous Bafter := by
    apply hGtreeQuotientMap.continuous_iff.mpr
    have he : Bafter ∘ Gtree=Boriginal := funext hActualBafterPins
    rw [he]
    exact Boriginal.continuous
  have hActualOriginalSourceQuotientBackwardPins (q : Quotient (Relation.EqvGen.setoid R1norm)) :
      Boriginal (Fa q)=Quotient.mk (Relation.EqvGen.setoid Rsurviving) (Fboundary (M3 q)) := by
    refine Quotient.inductionOn q ?_
    intro q
    cases q with
    | inl q =>
      refine Quotient.inductionOn q ?_
      intro v
      cases v with
      | inl v =>
        change Boriginal (Fa (qFacenorm false false v))=Quotient.mk _ (Fboundary (M3 (qFacenorm false false v)))
        have hf : Fa (qFacenorm false false v)=northDiskFace false v := hFaNorth0 v
        rw [hf,hBoriginalNorth]
      | inr v =>
        change Boriginal (Fa (qFacenorm false true v))=Quotient.mk _ (Fboundary (M3 (qFacenorm false true v)))
        have hf : Fa (qFacenorm false true v)=southDiskFace true v := hFaSouth1 v
        rw [hf,hBoriginalSouth]
        simp only [Bool.not_true]
    | inr q =>
      refine Quotient.inductionOn q ?_
      intro v
      cases v with
      | inl v =>
        change Boriginal (Fa (qFacenorm true true v))=Quotient.mk _ (Fboundary (M3 (qFacenorm true true v)))
        have hf : Fa (qFacenorm true true v)=northDiskFace true v := hFaNorth1 v
        rw [hf,hBoriginalNorth]
      | inr v =>
        change Boriginal (Fa (qFacenorm true false v))=Quotient.mk _ (Fboundary (M3 (qFacenorm true false v)))
        have hf : Fa (qFacenorm true false v)=southDiskFace false v := hFaSouth0 v
        rw [hf,hBoriginalSouth]
        simp only [Bool.not_false]
  have hActualNormalizedAttachingBackwardPins (z : ↥unitInterval × ↥unitInterval) :
      Bafter (Jnormalized z)=Quotient.mk (Relation.EqvGen.setoid Rsurviving) z := by
    obtain ⟨w,rfl⟩ := hFboundarySurj z
    rw [hActualNormalizedDiskAttachingPins,hActualBafterPins,hActualOriginalSourceQuotientBackwardPins,
      M3.apply_symm_apply]
  have hActualNormalizedSurvivingPairRelationRespect (z w : ↥unitInterval × ↥unitInterval)
      (h : Relation.EqvGen Rsurviving z w) : Jnormalized z=Jnormalized w := by
    induction h with
    | rel z w h =>
      obtain ⟨k,p,hp,hc,rfl,rfl⟩ := h
      fin_cases k
      · exact hActualEightSurvivingSourcePairPins 0 p hp hc
      · exact hActualEightSurvivingSourcePairPins 1 p hp hc
      · exact hActualEightSurvivingSourcePairPins 2 p hp hc
      · exact hActualEightSurvivingSourcePairPins 3 p hp hc
    | refl z => rfl
    | symm z w h ih => exact ih.symm
    | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  let JsourceQuotient : C(Qsource,Total) :=
    ⟨Quotient.lift Jnormalized hActualNormalizedSurvivingPairRelationRespect,
      Jnormalized.continuous.quotient_lift _⟩
  have hActualSourceQuotientSurjective : Function.Surjective JsourceQuotient := by
    intro x
    obtain ⟨z,hz⟩ := hActualNormalizedDiskAttachingSurj x
    exact ⟨Quotient.mk (Relation.EqvGen.setoid Rsurviving) z,hz⟩
  have hActualSourceQuotientLeftInverse : Function.LeftInverse Bafter JsourceQuotient := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    exact hActualNormalizedAttachingBackwardPins z
  have hActualSurvivingFourPairQuotientHomeomorphTotal :
      ∃ H : Qsource ≃ₜ Total, ∀ z : ↥unitInterval × ↥unitInterval,
        H (Quotient.mk (Relation.EqvGen.setoid Rsurviving) z)=Jnormalized z := by
    let e := Equiv.ofBijective JsourceQuotient
      ⟨hActualSourceQuotientLeftInverse.injective,hActualSourceQuotientSurjective⟩
    let H : Qsource ≃ₜ Total :=
      (show Continuous (e : Qsource → Total) from JsourceQuotient.continuous).homeoOfEquivCompactToT2
    exact ⟨H,fun _ => rfl⟩
  have hActualNormalizedAttachingExactSurvivingKernel (z w : ↥unitInterval × ↥unitInterval) :
      Jnormalized z=Jnormalized w ↔ Relation.EqvGen Rsurviving z w := by
    constructor
    · intro he
      have hq := congrArg Bafter he
      rw [hActualNormalizedAttachingBackwardPins,hActualNormalizedAttachingBackwardPins] at hq
      exact Quotient.exact hq
    · exact hActualNormalizedSurvivingPairRelationRespect z w
  have hActualFiveBoundaryRunPerimeterImage : Fboundary '' LiteralPerimeter=LiteralPerimeter := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hFboundaryPerimeter w).mpr hw
    · intro hz
      obtain ⟨w,rfl⟩ := hFboundarySurj z
      exact ⟨w,(hFboundaryPerimeter w).mp hz,rfl⟩
  have hActualEightSurvivingArcsCoverIntrinsicDiskPerimeter :
      LiteralPerimeter=⋃ k : Fin 8, Fboundary '' survivingPerimeter k :=
    hActualFiveBoundaryRunPerimeterImage.symm.trans hActualNormalizedEightArcsCoverSourceBoundary
  let sourceEdgeStartBranch : Fin 8 → Fin 6 := ![2,3,4,5,5,3,0,4]
  let sourceEdgeEndBranch : Fin 8 → Fin 6 := ![3,4,5,0,4,2,5,3]
  let actualSourceEdgeStart (k : Fin 8) :=
    Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
      (diskBoundaryPoint (bsource (sourceEdgeStartBranch k)) (hbsource _))))
  let actualSourceEdgeEnd (k : Fin 8) :=
    Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
      (diskBoundaryPoint (bsource (sourceEdgeEndBranch k)) (hbsource _))))
  have hActualEightSourceBranchesBindWholeArcs : ∀ k : Fin 8,
      closedArcSector (survivingSector k) (bsource (sourceEdgeStartBranch k)) ∧
        closedArcSector (survivingSector k) (bsource (sourceEdgeEndBranch k)) := by
    intro k
    fin_cases k
    · exact ⟨hSourceBranchSectorStart 2,hSourceBranchSectorEnd 2⟩
    · exact ⟨hSourceBranchSectorStart 3,hSourceBranchSectorEnd 3⟩
    · exact ⟨hSourceBranchSectorStart 4,hSourceBranchSectorEnd 4⟩
    · exact ⟨hSourceBranchSectorStart 5,hb0five⟩
    · exact ⟨hSourceBranchSectorEnd 4,hSourceBranchSectorStart 4⟩
    · exact ⟨hSourceBranchSectorEnd 2,hSourceBranchSectorStart 2⟩
    · exact ⟨hb0five,hSourceBranchSectorStart 5⟩
    · exact ⟨hSourceBranchSectorEnd 3,hSourceBranchSectorStart 3⟩
  have hActualEightSourceBoundaryCyclicEndpoints : ∀ k : Fin 8,
      actualSourceEdgeEnd k=actualSourceEdgeStart (k+1) := by
    intro k
    fin_cases k
    · rfl
    · rfl
    · rfl
    · change Nsource (bsource 0) (hbsource 0)=S1source (bsource 5) (hbsource 5)
      exact (hActualSelectedSeam0Left _ _ (hSourceBranchSectorStart 0)).trans
        (hActualSouthFiveOneVertex _ _ (hSourceBranchSectorStart 5)).symm
    · change S1source (bsource 4) (hbsource 4)=S1source (bsource 3) (hbsource 3)
      exact hActualSouthThreeOneVertex _ _ (hSourceBranchSectorEnd 3)
    · change S1source (bsource 2) (hbsource 2)=S0source (bsource 0) (hbsource 0)
      exact (hActualSouthOneOneVertex _ _ (hSourceBranchSectorEnd 1)).trans
        (hActualSelectedSeam0Right _ _ (hSourceBranchSectorStart 0))
    · change S0source (bsource 5) (hbsource 5)=S0source (bsource 4) (hbsource 4)
      exact hActualSouthFourOneVertex _ _ (hSourceBranchSectorEnd 4)
    · change S0source (bsource 3) (hbsource 3)=Nsource (bsource 2) (hbsource 2)
      exact (hActualSouthTwoOneVertex _ _ (hSourceBranchSectorEnd 2)).trans
        (hActualSelectedSeam1 _ _ (hSourceBranchSectorEnd 1)).symm
  obtain ⟨Pactual,Qactual,hPactualContinuous,hPactualInjective,hPactualHeight,hPactualClosed,
    hPactualOpen,hPactualStart,hPactualEnd,hQactualContinuous,hQactualInverse⟩ :=
      actual_six_arc_parameterization
  let actualEdgeParameter (k : Fin 8) (t : ↥unitInterval) : ℝ :=
    if k.val < 4 then 2*t.val-1 else 1-2*t.val
  have hActualEdgeParameterContinuous (k : Fin 8) : Continuous (actualEdgeParameter k) := by
    by_cases hk : k.val < 4 <;> simp only [actualEdgeParameter,hk,ite_true,ite_false] <;> fun_prop
  have hActualEdgeParameterBounds (k : Fin 8) (t : ↥unitInterval) :
      actualEdgeParameter k t∈Icc (-1:ℝ) 1 := by
    by_cases hk : k.val < 4 <;> simp only [actualEdgeParameter,hk,ite_true,ite_false]
    all_goals constructor <;> linarith only [t.property.1,t.property.2]
  have hActualEdgeParameterSurjective (k : Fin 8) (u : ℝ) (hu : u∈Icc (-1:ℝ) 1) :
      ∃ t : ↥unitInterval, actualEdgeParameter k t=u := by
    by_cases hk : k.val < 4
    · let t : ↥unitInterval := ⟨(u+1)/2,⟨by linarith only [hu.1],by linarith only [hu.2]⟩⟩
      refine ⟨t,?_⟩
      change (if k.val < 4 then 2*((u+1)/2)-1 else 1-2*((u+1)/2))=u
      rw [ite_eq_left hk]
      ring
    · let t : ↥unitInterval := ⟨(1-u)/2,⟨by linarith only [hu.2],by linarith only [hu.1]⟩⟩
      refine ⟨t,?_⟩
      change (if k.val < 4 then 2*((1-u)/2)-1 else 1-2*((1-u)/2))=u
      rw [ite_eq_right hk]
      ring
  have hActualEdgeParameterZero (k : Fin 8) :
      actualEdgeParameter k 0=(if k.val < 4 then -1 else 1) := by
    by_cases hk : k.val < 4 <;> norm_num [actualEdgeParameter,hk]
  have hActualEdgeParameterOne (k : Fin 8) :
      actualEdgeParameter k 1=(if k.val < 4 then 1 else -1) := by
    by_cases hk : k.val < 4 <;> norm_num [actualEdgeParameter,hk]
  have hActualSourceDiskContinuous : Continuous sourceDisk :=
    coordinateDiskClosedBallHomeomorph.continuous.comp diskProjection_continuous
  let actualSourceEdgePath (k : Fin 8) : C(↥unitInterval,↥unitInterval × ↥unitInterval) :=
    ⟨fun t => Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
      (sourceDisk (Pactual (survivingSector k) (actualEdgeParameter k t))))),
      Fboundary.continuous.comp (M3.continuous.comp ((hSourceQFaceContinuous _ _).comp
        (hActualSourceDiskContinuous.comp ((hPactualContinuous _).comp (hActualEdgeParameterContinuous k)))))⟩
  have hActualEightPhysicalParameterBranchPins : ∀ k : Fin 8,
      Pactual (survivingSector k) (actualEdgeParameter k 0)=bsource (sourceEdgeStartBranch k) ∧
        Pactual (survivingSector k) (actualEdgeParameter k 1)=bsource (sourceEdgeEndBranch k) := by
    intro k
    fin_cases k
    · constructor
      · change Pactual (2:Fin 6) (actualEdgeParameter (0:Fin 8) 0) = bsource (2:Fin 6)
        have hp : actualEdgeParameter (0:Fin 8) 0=(-1:ℝ) := by
          simpa using hActualEdgeParameterZero (0:Fin 8)
        rw [hp]
        exact hPactualStart 2
      · change Pactual (2:Fin 6) (actualEdgeParameter (0:Fin 8) 1) = bsource (3:Fin 6)
        have hp : actualEdgeParameter (0:Fin 8) 1=(1:ℝ) := by
          simpa using hActualEdgeParameterOne (0:Fin 8)
        rw [hp]
        exact hPactualEnd 2
    · constructor
      · change Pactual (3:Fin 6) (actualEdgeParameter (1:Fin 8) 0) = bsource (3:Fin 6)
        have hp : actualEdgeParameter (1:Fin 8) 0=(-1:ℝ) := by
          simpa using hActualEdgeParameterZero (1:Fin 8)
        rw [hp]
        exact hPactualStart 3
      · change Pactual (3:Fin 6) (actualEdgeParameter (1:Fin 8) 1) = bsource (4:Fin 6)
        have hp : actualEdgeParameter (1:Fin 8) 1=(1:ℝ) := by
          simpa using hActualEdgeParameterOne (1:Fin 8)
        rw [hp]
        exact hPactualEnd 3
    · constructor
      · change Pactual (4:Fin 6) (actualEdgeParameter (2:Fin 8) 0) = bsource (4:Fin 6)
        have hp : actualEdgeParameter (2:Fin 8) 0=(-1:ℝ) := by
          simpa using hActualEdgeParameterZero (2:Fin 8)
        rw [hp]
        exact hPactualStart 4
      · change Pactual (4:Fin 6) (actualEdgeParameter (2:Fin 8) 1) = bsource (5:Fin 6)
        have hp : actualEdgeParameter (2:Fin 8) 1=(1:ℝ) := by
          simpa using hActualEdgeParameterOne (2:Fin 8)
        rw [hp]
        exact hPactualEnd 4
    · constructor
      · change Pactual (5:Fin 6) (actualEdgeParameter (3:Fin 8) 0) = bsource (5:Fin 6)
        have hp : actualEdgeParameter (3:Fin 8) 0=(-1:ℝ) := by
          simpa using hActualEdgeParameterZero (3:Fin 8)
        rw [hp]
        exact hPactualStart 5
      · change Pactual (5:Fin 6) (actualEdgeParameter (3:Fin 8) 1) = bsource (0:Fin 6)
        have hp : actualEdgeParameter (3:Fin 8) 1=(1:ℝ) := by
          simpa using hActualEdgeParameterOne (3:Fin 8)
        rw [hp]
        exact hPactualEnd 5
    · constructor
      · change Pactual (4:Fin 6) (actualEdgeParameter (4:Fin 8) 0) = bsource (5:Fin 6)
        have hp : actualEdgeParameter (4:Fin 8) 0=(1:ℝ) := by
          simpa using hActualEdgeParameterZero (4:Fin 8)
        rw [hp]
        exact hPactualEnd 4
      · change Pactual (4:Fin 6) (actualEdgeParameter (4:Fin 8) 1) = bsource (4:Fin 6)
        have hp : actualEdgeParameter (4:Fin 8) 1=(-1:ℝ) := by
          simpa using hActualEdgeParameterOne (4:Fin 8)
        rw [hp]
        exact hPactualStart 4
    · constructor
      · change Pactual (2:Fin 6) (actualEdgeParameter (5:Fin 8) 0) = bsource (3:Fin 6)
        have hp : actualEdgeParameter (5:Fin 8) 0=(1:ℝ) := by
          simpa using hActualEdgeParameterZero (5:Fin 8)
        rw [hp]
        exact hPactualEnd 2
      · change Pactual (2:Fin 6) (actualEdgeParameter (5:Fin 8) 1) = bsource (2:Fin 6)
        have hp : actualEdgeParameter (5:Fin 8) 1=(-1:ℝ) := by
          simpa using hActualEdgeParameterOne (5:Fin 8)
        rw [hp]
        exact hPactualStart 2
    · constructor
      · change Pactual (5:Fin 6) (actualEdgeParameter (6:Fin 8) 0) = bsource (0:Fin 6)
        have hp : actualEdgeParameter (6:Fin 8) 0=(1:ℝ) := by
          simpa using hActualEdgeParameterZero (6:Fin 8)
        rw [hp]
        exact hPactualEnd 5
      · change Pactual (5:Fin 6) (actualEdgeParameter (6:Fin 8) 1) = bsource (5:Fin 6)
        have hp : actualEdgeParameter (6:Fin 8) 1=(-1:ℝ) := by
          simpa using hActualEdgeParameterOne (6:Fin 8)
        rw [hp]
        exact hPactualStart 5
    · constructor
      · change Pactual (3:Fin 6) (actualEdgeParameter (7:Fin 8) 0) = bsource (4:Fin 6)
        have hp : actualEdgeParameter (7:Fin 8) 0=(1:ℝ) := by
          simpa using hActualEdgeParameterZero (7:Fin 8)
        rw [hp]
        exact hPactualEnd 3
      · change Pactual (3:Fin 6) (actualEdgeParameter (7:Fin 8) 1) = bsource (3:Fin 6)
        have hp : actualEdgeParameter (7:Fin 8) 1=(-1:ℝ) := by
          simpa using hActualEdgeParameterOne (7:Fin 8)
        rw [hp]
        exact hPactualStart 3
  have hActualEightSourceEdgePathEndpoints : ∀ k : Fin 8,
      actualSourceEdgePath k 0=actualSourceEdgeStart k ∧ actualSourceEdgePath k 1=actualSourceEdgeEnd k := by
    intro k
    constructor
    · change Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
        (sourceDisk (Pactual (survivingSector k) (actualEdgeParameter k 0)))))=
        Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
          (sourceDisk (bsource (sourceEdgeStartBranch k)))))
      rw [(hActualEightPhysicalParameterBranchPins k).1]
    · change Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
        (sourceDisk (Pactual (survivingSector k) (actualEdgeParameter k 1)))))=
        Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
          (sourceDisk (bsource (sourceEdgeEndBranch k)))))
      rw [(hActualEightPhysicalParameterBranchPins k).2]
  have hActualEightSourceEdgePathCyclicEndpoints : ∀ k : Fin 8,
      actualSourceEdgePath k 1=actualSourceEdgePath (k+1) 0 := by
    intro k
    exact ((hActualEightSourceEdgePathEndpoints k).2).trans
      ((hActualEightSourceBoundaryCyclicEndpoints k).trans
        ((hActualEightSourceEdgePathEndpoints (k+1)).1).symm)
  have hActualEightSourceEdgePathWholeImages : ∀ k : Fin 8,
      Set.range (actualSourceEdgePath k)=Fboundary '' survivingPerimeter k := by
    intro k
    rw [←hActualEightNormalizedSourceImages k]
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      have hc : closedArcSector (survivingSector k)
          (Pactual (survivingSector k) (actualEdgeParameter k t)) := by
        have hm : Pactual (survivingSector k) (actualEdgeParameter k t)∈
            Pactual (survivingSector k) '' Icc (-1:ℝ) 1 :=
          ⟨actualEdgeParameter k t,hActualEdgeParameterBounds k t,rfl⟩
        rw [hPactualClosed] at hm
        exact hm
      exact ⟨M3 (qFacenorm (survivingRight k) (survivingSheet k)
        (sourceDisk (Pactual (survivingSector k) (actualEdgeParameter k t)))),
        ⟨_,⟨Pactual (survivingSector k) (actualEdgeParameter k t),hPactualHeight _ _,hc,rfl⟩,rfl⟩,rfl⟩
    · rintro ⟨w,⟨q,⟨p,hp,hc,rfl⟩,rfl⟩,rfl⟩
      have hm : p∈Pactual (survivingSector k) '' Icc (-1:ℝ) 1 := by
        rw [hPactualClosed]
        exact hc
      obtain ⟨u,hu,hpu⟩ := hm
      obtain ⟨t,ht⟩ := hActualEdgeParameterSurjective k u hu
      refine ⟨t,?_⟩
      change Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k)
          (sourceDisk (Pactual (survivingSector k) (actualEdgeParameter k t)))))=
        Fboundary (M3 (qFacenorm (survivingRight k) (survivingSheet k) (sourceDisk p)))
      rw [ht,hpu]
  have hActualEightSourcePathsCoverIntrinsicDiskPerimeter :
      LiteralPerimeter=⋃ k : Fin 8, Set.range (actualSourceEdgePath k) := by
    rw [hActualEightSurvivingArcsCoverIntrinsicDiskPerimeter]
    congr 1
    funext k
    exact (hActualEightSourceEdgePathWholeImages k).symm
  have hActualSurvivingArcRunIntersectionSingleton : ∀ (k : Fin 8) (i : Fin 5)
      (z w : ↥unitInterval × ↥unitInterval), z∈survivingPerimeter k →
        w∈survivingPerimeter k → z∈Aruns i → w∈Aruns i → z=w := by
    intro k i z w hz hw hzi hwi
    fin_cases k <;> fin_cases i
    · change z∈T0 at hz
      change w∈T0 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T0,Aleft,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T0 at hz
      change w∈T0 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T0,Pcorner0,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T0 at hz
      change w∈T0 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T0,Pcorner1,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T0 at hz
      change w∈T0 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T0,Aright,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T0 at hz
      change w∈T0 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T0,Abottom,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T1 at hz
      change w∈T1 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T1,Aleft,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T1 at hz
      change w∈T1 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T1,Pcorner0,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T1 at hz
      change w∈T1 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T1,Pcorner1,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T1 at hz
      change w∈T1 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T1,Aright,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T1 at hz
      change w∈T1 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T1,Abottom,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T2 at hz
      change w∈T2 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T2,Aleft,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T2 at hz
      change w∈T2 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T2,Pcorner0,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T2 at hz
      change w∈T2 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T2,Pcorner1,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T2 at hz
      change w∈T2 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T2,Aright,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T2 at hz
      change w∈T2 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T2,Abottom,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T3 at hz
      change w∈T3 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T3,Aleft,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T3 at hz
      change w∈T3 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T3,Pcorner0,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T3 at hz
      change w∈T3 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T3,Pcorner1,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T3 at hz
      change w∈T3 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T3,Aright,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T3 at hz
      change w∈T3 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T3,Abottom,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T4 at hz
      change w∈T4 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T4,Aleft,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T4 at hz
      change w∈T4 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T4,Pcorner0,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T4 at hz
      change w∈T4 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T4,Pcorner1,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T4 at hz
      change w∈T4 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T4,Aright,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T4 at hz
      change w∈T4 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T4,Abottom,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T5 at hz
      change w∈T5 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T5,Aleft,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T5 at hz
      change w∈T5 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T5,Pcorner0,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T5 at hz
      change w∈T5 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T5,Pcorner1,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T5 at hz
      change w∈T5 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T5,Aright,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T5 at hz
      change w∈T5 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T5,Abottom,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T6 at hz
      change w∈T6 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T6,Aleft,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T6 at hz
      change w∈T6 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T6,Pcorner0,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T6 at hz
      change w∈T6 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T6,Pcorner1,Set.ofPred] at hz hw hzi hwi
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T6 at hz
      change w∈T6 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T6,Aright,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T6 at hz
      change w∈T6 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T6,Abottom,Set.ofPred] at hz hw hzi hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T7 at hz
      change w∈T7 at hw
      change z∈Aleft at hzi
      change w∈Aleft at hwi
      dsimp only [T7,Aleft,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T7 at hz
      change w∈T7 at hw
      change z∈Pcorner0 at hzi
      change w∈Pcorner0 at hwi
      dsimp only [T7,Pcorner0,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T7 at hz
      change w∈T7 at hw
      change z∈Pcorner1 at hzi
      change w∈Pcorner1 at hwi
      dsimp only [T7,Pcorner1,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals rcases hzi with hzi|hzi <;> rcases hwi with hwi|hwi
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T7 at hz
      change w∈T7 at hw
      change z∈Aright at hzi
      change w∈Aright at hwi
      dsimp only [T7,Aright,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
    · change z∈T7 at hz
      change w∈T7 at hw
      change z∈Abottom at hzi
      change w∈Abottom at hwi
      dsimp only [T7,Abottom,Set.ofPred] at hz hw hzi hwi
      rcases hz with hz|hz <;> rcases hw with hw|hw
      all_goals
        obtain ⟨hz1,hz2,hz3⟩ := hz
        obtain ⟨hw1,hw2,hw3⟩ := hw
        obtain ⟨hzi1,hzi2,hzi3⟩ := hzi
        obtain ⟨hwi1,hwi2,hwi3⟩ := hwi
        apply Prod.ext <;> apply Subtype.ext <;>
          linarith only [hz1,hz2,hz3,hw1,hw2,hw3,hzi1,hzi2,hzi3,hwi1,hwi2,hwi3]
  have hActualFiveRunCollapseInjectiveOnSurvivingArc (k : Fin 8) :
      Set.InjOn Fboundary (survivingPerimeter k) := by
    intro z hz w hw he
    rcases (hActualFiveBoundaryRunKernel z w).mp he with he|⟨i,hzi,hwi⟩
    · exact he
    · exact hActualSurvivingArcRunIntersectionSingleton k i z w hz hw hzi hwi
  have hActualSourceDiskEquatorInjective (p q : Sphere) (hp : height p=0)
      (hq : height q=0) (he : sourceDisk p=sourceDisk q) : p=q := by
    have hd : diskProjection p=diskProjection q :=
      coordinateDiskClosedBallHomeomorph.injective he
    have h0 := congrArg (fun v : CoordinateDisk => v.val 0) hd
    have h1 := congrArg (fun v : CoordinateDisk => v.val 1) hd
    dsimp only [diskProjection,horizontal] at h0 h1
    apply Subtype.ext
    ext j
    fin_cases j
    · exact h0
    · exact h1
    · exact hp.trans hq.symm
  have hActualSourceFaceQuotientInjective (right sheet : Bool) :
      Function.Injective (qFacenorm right sheet) := by
    intro v w he
    have hf := congrArg Fa he
    cases right <;> cases sheet
    · have hv : Fa (qFacenorm false false v)=northDiskFace false v := hFaNorth0 v
      have hw : Fa (qFacenorm false false w)=northDiskFace false w := hFaNorth0 w
      exact northDiskFace_injective false (hv.symm.trans (hf.trans hw))
    · have hv : Fa (qFacenorm false true v)=southDiskFace true v := hFaSouth1 v
      have hw : Fa (qFacenorm false true w)=southDiskFace true w := hFaSouth1 w
      exact southDiskFace_injective true (hv.symm.trans (hf.trans hw))
    · have hv : Fa (qFacenorm true false v)=southDiskFace false v := hFaSouth0 v
      have hw : Fa (qFacenorm true false w)=southDiskFace false w := hFaSouth0 w
      exact southDiskFace_injective false (hv.symm.trans (hf.trans hw))
    · have hv : Fa (qFacenorm true true v)=northDiskFace true v := hFaNorth1 v
      have hw : Fa (qFacenorm true true w)=northDiskFace true w := hFaNorth1 w
      exact northDiskFace_injective true (hv.symm.trans (hf.trans hw))
  have hActualEightPrecollapsePathPointsOnWholeSourceArc (k : Fin 8) (t : ↥unitInterval) :
      M3 (qFacenorm (survivingRight k) (survivingSheet k)
        (sourceDisk (Pactual (survivingSector k) (actualEdgeParameter k t))))∈survivingPerimeter k := by
    rw [←hActualEightWholeSourcePerimeterImages k]
    have hc : closedArcSector (survivingSector k)
        (Pactual (survivingSector k) (actualEdgeParameter k t)) := by
      have hm : Pactual (survivingSector k) (actualEdgeParameter k t)∈
          Pactual (survivingSector k) '' Icc (-1:ℝ) 1 :=
        ⟨actualEdgeParameter k t,hActualEdgeParameterBounds k t,rfl⟩
      rw [hPactualClosed] at hm
      exact hm
    exact ⟨_,⟨Pactual (survivingSector k) (actualEdgeParameter k t),hPactualHeight _ _,hc,rfl⟩,rfl⟩
  have hActualEightSourceEdgePathInjective (k : Fin 8) :
      Function.Injective (actualSourceEdgePath k) := by
    intro t u he
    have he0 := hActualFiveRunCollapseInjectiveOnSurvivingArc k
      (hActualEightPrecollapsePathPointsOnWholeSourceArc k t)
      (hActualEightPrecollapsePathPointsOnWholeSourceArc k u) he
    have he1 := hActualSourceFaceQuotientInjective (survivingRight k) (survivingSheet k)
      (M3.injective he0)
    have he2 := hActualSourceDiskEquatorInjective _ _ (hPactualHeight _ _) (hPactualHeight _ _) he1
    have he3 := hPactualInjective (survivingSector k) he2
    apply Subtype.ext
    by_cases hk : k.val < 4
    · change (if k.val < 4 then 2*t.val-1 else 1-2*t.val)=
        (if k.val < 4 then 2*u.val-1 else 1-2*u.val) at he3
      rw [ite_eq_left hk,ite_eq_left hk] at he3
      linarith only [he3]
    · change (if k.val < 4 then 2*t.val-1 else 1-2*t.val)=
        (if k.val < 4 then 2*u.val-1 else 1-2*u.val) at he3
      rw [ite_eq_right hk,ite_eq_right hk] at he3
      linarith only [he3]
  let actualSourcePartner : Fin 8 → Fin 8 := ![5,7,4,6,2,0,3,1]
  have hActualSourcePartnerParameter (k : Fin 8) (t : ↥unitInterval) :
      actualEdgeParameter (actualSourcePartner k) (unitInterval.symmHomeomorph t)=
        actualEdgeParameter k t := by
    fin_cases k <;>
      norm_num [actualSourcePartner,actualEdgeParameter,unitInterval.symmHomeomorph,unitInterval.symm]
    all_goals ring
  have hActualSourcePathPhysicalSector (k : Fin 8) (t : ↥unitInterval) :
      closedArcSector (survivingSector k)
        (Pactual (survivingSector k) (actualEdgeParameter k t)) := by
    have hm : Pactual (survivingSector k) (actualEdgeParameter k t)∈
        Pactual (survivingSector k) '' Icc (-1:ℝ) 1 :=
      ⟨actualEdgeParameter k t,hActualEdgeParameterBounds k t,rfl⟩
    rw [hPactualClosed] at hm
    exact hm
  have hActualEightSourceReversedParameterPairs : ∀ (k : Fin 8) (t : ↥unitInterval),
      Relation.EqvGen Rsurviving (actualSourceEdgePath k t)
        (actualSourceEdgePath (actualSourcePartner k) (unitInterval.symmHomeomorph t)) := by
    intro k t
    have hparam := hActualSourcePartnerParameter k t
    fin_cases k
    · change Relation.EqvGen Rsurviving
        (Nsource (Pactual (2:Fin 6) (actualEdgeParameter (0:Fin 8) t)) (hPactualHeight _ _))
        (S1source (Pactual (2:Fin 6) (actualEdgeParameter (5:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (5:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (0:Fin 8) t := hparam
      rw [hp]
      exact hSourcePair2 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (0:Fin 8) t)
    · change Relation.EqvGen Rsurviving
        (Nsource (Pactual (3:Fin 6) (actualEdgeParameter (1:Fin 8) t)) (hPactualHeight _ _))
        (S0source (Pactual (3:Fin 6) (actualEdgeParameter (7:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (7:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (1:Fin 8) t := hparam
      rw [hp]
      exact hSourcePair3 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (1:Fin 8) t)
    · change Relation.EqvGen Rsurviving
        (Nsource (Pactual (4:Fin 6) (actualEdgeParameter (2:Fin 8) t)) (hPactualHeight _ _))
        (S1source (Pactual (4:Fin 6) (actualEdgeParameter (4:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (4:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (2:Fin 8) t := hparam
      rw [hp]
      exact hSourcePair4 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (2:Fin 8) t)
    · change Relation.EqvGen Rsurviving
        (Nsource (Pactual (5:Fin 6) (actualEdgeParameter (3:Fin 8) t)) (hPactualHeight _ _))
        (S0source (Pactual (5:Fin 6) (actualEdgeParameter (6:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (6:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (3:Fin 8) t := hparam
      rw [hp]
      exact hSourcePair5 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (3:Fin 8) t)
    · change Relation.EqvGen Rsurviving
        (S1source (Pactual (4:Fin 6) (actualEdgeParameter (4:Fin 8) t)) (hPactualHeight _ _))
        (Nsource (Pactual (4:Fin 6) (actualEdgeParameter (2:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (2:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (4:Fin 8) t := hparam
      rw [hp]
      exact Relation.EqvGen.symm _ _ (hSourcePair4 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (4:Fin 8) t))
    · change Relation.EqvGen Rsurviving
        (S1source (Pactual (2:Fin 6) (actualEdgeParameter (5:Fin 8) t)) (hPactualHeight _ _))
        (Nsource (Pactual (2:Fin 6) (actualEdgeParameter (0:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (0:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (5:Fin 8) t := hparam
      rw [hp]
      exact Relation.EqvGen.symm _ _ (hSourcePair2 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (5:Fin 8) t))
    · change Relation.EqvGen Rsurviving
        (S0source (Pactual (5:Fin 6) (actualEdgeParameter (6:Fin 8) t)) (hPactualHeight _ _))
        (Nsource (Pactual (5:Fin 6) (actualEdgeParameter (3:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (3:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (6:Fin 8) t := hparam
      rw [hp]
      exact Relation.EqvGen.symm _ _ (hSourcePair5 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (6:Fin 8) t))
    · change Relation.EqvGen Rsurviving
        (S0source (Pactual (3:Fin 6) (actualEdgeParameter (7:Fin 8) t)) (hPactualHeight _ _))
        (Nsource (Pactual (3:Fin 6) (actualEdgeParameter (1:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _))
      have hp : actualEdgeParameter (1:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (7:Fin 8) t := hparam
      rw [hp]
      exact Relation.EqvGen.symm _ _ (hSourcePair3 _ (hPactualHeight _ _) (hActualSourcePathPhysicalSector (7:Fin 8) t))
  have hActualEightSourceAttachingReversedPairs : ∀ (k : Fin 8) (t : ↥unitInterval),
      Jnormalized (actualSourceEdgePath k t)=
        Jnormalized (actualSourceEdgePath (actualSourcePartner k) (unitInterval.symmHomeomorph t)) := by
    intro k t
    exact hActualNormalizedSurvivingPairRelationRespect _ _
      (hActualEightSourceReversedParameterPairs k t)
  have hActualEightSourceSideIntervalHomeomorphs : ∀ k : Fin 8,
      ∃ E : ↥unitInterval ≃ₜ ↥(Fboundary '' survivingPerimeter k),
        ∀ t : ↥unitInterval, (E t).val=actualSourceEdgePath k t := by
    intro k
    have hEmb : IsEmbedding (actualSourceEdgePath k) :=
      ((actualSourceEdgePath k).continuous.isClosedEmbedding
        (hActualEightSourceEdgePathInjective k)).isEmbedding
    refine ⟨hEmb.toHomeomorph.trans
      (Homeomorph.setCongr (hActualEightSourceEdgePathWholeImages k)),?_⟩
    intro t
    rfl
  let firstFourSourceIndex (i : Fin 4) : Fin 8 := ⟨i.val,by omega⟩
  have hActualFirstFourSourceSector (i : Fin 4) :
      survivingSector (firstFourSourceIndex i)=![(2:Fin 6),3,4,5] i := by
    fin_cases i <;> rfl
  have hActualFirstFourPhysicalSourcePathPair (i : Fin 4) (t : ↥unitInterval) :
      actualSourceEdgePath (firstFourSourceIndex i) t=
        Nsource (Pactual (![(2:Fin 6),3,4,5] i) (actualEdgeParameter (firstFourSourceIndex i) t)) (hPactualHeight _ _) ∧
      actualSourceEdgePath (actualSourcePartner (firstFourSourceIndex i)) (unitInterval.symmHomeomorph t)=
        (if i.val % 2=0 then
          S1source (Pactual (![(2:Fin 6),3,4,5] i) (actualEdgeParameter (firstFourSourceIndex i) t)) (hPactualHeight _ _)
        else S0source (Pactual (![(2:Fin 6),3,4,5] i) (actualEdgeParameter (firstFourSourceIndex i) t)) (hPactualHeight _ _)) := by
    have hparam := hActualSourcePartnerParameter (firstFourSourceIndex i) t
    fin_cases i
    · constructor
      · rfl
      · change S1source (Pactual (2:Fin 6) (actualEdgeParameter (5:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _)=
          S1source (Pactual (2:Fin 6) (actualEdgeParameter (0:Fin 8) t)) (hPactualHeight _ _)
        have hp : actualEdgeParameter (5:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (0:Fin 8) t := hparam
        rw [hp]
    · constructor
      · rfl
      · change S0source (Pactual (3:Fin 6) (actualEdgeParameter (7:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _)=
          S0source (Pactual (3:Fin 6) (actualEdgeParameter (1:Fin 8) t)) (hPactualHeight _ _)
        have hp : actualEdgeParameter (7:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (1:Fin 8) t := hparam
        rw [hp]
    · constructor
      · rfl
      · change S1source (Pactual (4:Fin 6) (actualEdgeParameter (4:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _)=
          S1source (Pactual (4:Fin 6) (actualEdgeParameter (2:Fin 8) t)) (hPactualHeight _ _)
        have hp : actualEdgeParameter (4:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (2:Fin 8) t := hparam
        rw [hp]
    · constructor
      · rfl
      · change S0source (Pactual (5:Fin 6) (actualEdgeParameter (6:Fin 8) (unitInterval.symmHomeomorph t))) (hPactualHeight _ _)=
          S0source (Pactual (5:Fin 6) (actualEdgeParameter (3:Fin 8) t)) (hPactualHeight _ _)
        have hp : actualEdgeParameter (6:Fin 8) (unitInterval.symmHomeomorph t)=actualEdgeParameter (3:Fin 8) t := hparam
        rw [hp]
  let RactualEightPaths : (↥unitInterval × ↥unitInterval) → (↥unitInterval × ↥unitInterval) → Prop :=
    fun z w => ∃ (i : Fin 4) (t : ↥unitInterval),
      z=actualSourceEdgePath (firstFourSourceIndex i) t ∧
      w=actualSourceEdgePath (actualSourcePartner (firstFourSourceIndex i)) (unitInterval.symmHomeomorph t)
  have hActualLiteralSourcePairIsPathPair : ∀ z w, Rsurviving z w → RactualEightPaths z w := by
    rintro z w ⟨i,p,hp,hc,hz,hw⟩
    have hm : p∈Pactual (![(2:Fin 6),3,4,5] i) '' Icc (-1:ℝ) 1 := by
      rw [hPactualClosed]
      exact hc
    obtain ⟨u,hu,hpu⟩ := hm
    obtain ⟨t,ht⟩ := hActualEdgeParameterSurjective (firstFourSourceIndex i) u hu
    have hpActual : Pactual (![(2:Fin 6),3,4,5] i)
        (actualEdgeParameter (firstFourSourceIndex i) t)=p := by rw [ht,hpu]
    have hpoint := congrArg sourceDisk hpActual
    refine ⟨i,t,?_,?_⟩
    · rw [(hActualFirstFourPhysicalSourcePathPair i t).1]
      change z=Fboundary (M3 (qFacenorm false false
        (sourceDisk (Pactual (![(2:Fin 6),3,4,5] i)
          (actualEdgeParameter (firstFourSourceIndex i) t)))))
      rw [hpoint]
      exact hz
    · rw [(hActualFirstFourPhysicalSourcePathPair i t).2]
      by_cases hi : i.val % 2=0
      · rw [ite_eq_left hi]
        change w=Fboundary (M3 (qFacenorm false true
          (sourceDisk (Pactual (![(2:Fin 6),3,4,5] i)
            (actualEdgeParameter (firstFourSourceIndex i) t)))))
        rw [hpoint]
        exact Eq.trans hw (ite_eq_left hi)
      · rw [ite_eq_right hi]
        change w=Fboundary (M3 (qFacenorm true false
          (sourceDisk (Pactual (![(2:Fin 6),3,4,5] i)
            (actualEdgeParameter (firstFourSourceIndex i) t)))))
        rw [hpoint]
        exact Eq.trans hw (ite_eq_right hi)
  have hActualPathPairIsGeneratedSourcePair : ∀ z w,
      RactualEightPaths z w → Relation.EqvGen Rsurviving z w := by
    rintro z w ⟨i,t,rfl,rfl⟩
    exact hActualEightSourceReversedParameterPairs (firstFourSourceIndex i) t
  have hActualSourceAndEightPathGeneratedRelations : ∀ z w,
      Relation.EqvGen Rsurviving z w ↔ Relation.EqvGen RactualEightPaths z w := by
    intro z w
    constructor
    · intro h
      induction h with
      | rel z w hr => exact Relation.EqvGen.rel _ _ (hActualLiteralSourcePairIsPathPair z w hr)
      | refl z => exact Relation.EqvGen.refl z
      | symm z w h ih => exact Relation.EqvGen.symm _ _ ih
      | trans z w v h1 h2 ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    · intro h
      induction h with
      | rel z w hr => exact hActualPathPairIsGeneratedSourcePair z w hr
      | refl z => exact Relation.EqvGen.refl z
      | symm z w h ih => exact Relation.EqvGen.symm _ _ ih
      | trans z w v h1 h2 ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hActualNormalizedAttachingExactEightSourcePathKernel : ∀ z w,
      Jnormalized z=Jnormalized w ↔ Relation.EqvGen RactualEightPaths z w := by
    intro z w
    exact (hActualNormalizedAttachingExactSurvivingKernel z w).trans
      (hActualSourceAndEightPathGeneratedRelations z w)
  have hActualPrecollapseSelectedSeam0Left (p : Sphere) (hp : height p=0) (hc : closedArcSector (0:Fin 6) p) :
      M3 (qFacenorm false false (diskBoundaryPoint p hp))=M3 (qFacenorm false true (diskBoundaryPoint p hp)) := by
    apply congrArg M3
    change Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inl (diskBoundaryPoint p hp))))=
      Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inr (diskBoundaryPoint p hp))))
    apply congrArg (fun q : Q0norm => Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inl q))
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨p,hp,hc,rfl,rfl⟩)
  have hActualPrecollapseSelectedSeam0Right (p : Sphere) (hp : height p=0) (hc : closedArcSector (0:Fin 6) p) :
      M3 (qFacenorm true true (diskBoundaryPoint p hp))=M3 (qFacenorm true false (diskBoundaryPoint p hp)) := by
    apply congrArg M3
    change Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inl (diskBoundaryPoint p hp))))=
      Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0norm) (Sum.inr (diskBoundaryPoint p hp))))
    apply congrArg (fun q : Q0norm => Quotient.mk (Relation.EqvGen.setoid R1norm) (Sum.inr q))
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨p,hp,hc,rfl,rfl⟩)
  have hActualPrecollapseSelectedSeam1 (p : Sphere) (hp : height p=0) (hc : closedArcSector (1:Fin 6) p) :
      M3 (qFacenorm false false (diskBoundaryPoint p hp))=M3 (qFacenorm true false (diskBoundaryPoint p hp)) := by
    apply congrArg M3
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨p,hp,hc,rfl,rfl⟩)
  have hActualSourcePrePointMembership (k : Fin 8) (p : Sphere) (hp : height p=0)
      (hc : closedArcSector (survivingSector k) p) :
      M3 (qFacenorm (survivingRight k) (survivingSheet k) (diskBoundaryPoint p hp))∈survivingPerimeter k := by
    rw [←hActualEightWholeSourcePerimeterImages k]
    exact hSourcePointMembership _ _ _ p hp hc
  let actualPreSourceStart (k : Fin 8) := M3 (qFacenorm (survivingRight k) (survivingSheet k)
    (diskBoundaryPoint (bsource (sourceEdgeStartBranch k)) (hbsource _)))
  let actualPreSourceEnd (k : Fin 8) := M3 (qFacenorm (survivingRight k) (survivingSheet k)
    (diskBoundaryPoint (bsource (sourceEdgeEndBranch k)) (hbsource _)))
  have hActualEightPrecollapseSourceEndpointCoordinates : ∀ k : Fin 8,
      (actualPreSourceStart k).1.val=![(1/2:ℝ),1/3,0,0,0,3/10,1,1] k ∧
      (actualPreSourceStart k).2.val=![(0:ℝ),0,2/7,3/7,5/7,1,4/7,2/7] k ∧
      (actualPreSourceEnd k).1.val=![(1/3:ℝ),0,0,0,0,1/3,1,2/3] k ∧
      (actualPreSourceEnd k).2.val=![(0:ℝ),2/7,3/7,4/7,6/7,1,3/7,0] k := by
    intro k
    fin_cases k
    · have hs : (actualPreSourceStart (0:Fin 8)).1.val=(1/2:ℝ) ∧ (actualPreSourceStart (0:Fin 8)).2.val=(0:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (2:Fin 6)) (hbsource _)))
        change z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        have ha : z∈T0 := hActualSourcePrePointMembership (0:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (0:Fin 8)).1
        have hb : z∈Aruns (4:Fin 5) := by
          change M3 (qFacenorm false false (diskBoundaryPoint (bsource (2:Fin 6)) (hbsource _)))∈Aruns (4:Fin 5)
          rw [hActualPrecollapseSelectedSeam1 (bsource (2:Fin 6)) (hbsource 2) (hSourceBranchSectorEnd (1:Fin 6))]
          exact hSourceSouthTwoPerimeter _ _ (hSourceBranchSectorStart (2:Fin 6))
        change z∈Abottom at hb
        dsimp only [T0,Abottom,Set.ofPred] at ha hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (0:Fin 8)).1.val=(1/3:ℝ) ∧ (actualPreSourceEnd (0:Fin 8)).2.val=(0:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (3:Fin 6)) (hbsource _)))
        change z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        have ha : z∈T0 := hActualSourcePrePointMembership (0:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (0:Fin 8)).2
        have hb : z∈T1 := hActualSourcePrePointMembership (1:Fin 8) _ _ (hSourceBranchSectorStart (3:Fin 6))
        dsimp only [T0,T1,Set.ofPred] at ha hb
        all_goals rcases hb with hb|hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (1:Fin 8)).1.val=(1/3:ℝ) ∧ (actualPreSourceStart (1:Fin 8)).2.val=(0:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (3:Fin 6)) (hbsource _)))
        change z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        have ha : z∈T1 := hActualSourcePrePointMembership (1:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (1:Fin 8)).1
        have hb : z∈T0 := hActualSourcePrePointMembership (0:Fin 8) _ _ (hSourceBranchSectorEnd (2:Fin 6))
        dsimp only [T1,T0,Set.ofPred] at ha hb
        rcases ha with ha|ha
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (1:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceEnd (1:Fin 8)).2.val=(2/7:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (4:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        have ha : z∈T1 := hActualSourcePrePointMembership (1:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (1:Fin 8)).2
        have hb : z∈T2 := hActualSourcePrePointMembership (2:Fin 8) _ _ (hSourceBranchSectorStart (4:Fin 6))
        dsimp only [T1,T2,Set.ofPred] at ha hb
        rcases ha with ha|ha
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (2:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceStart (2:Fin 8)).2.val=(2/7:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (4:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        have ha : z∈T2 := hActualSourcePrePointMembership (2:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (2:Fin 8)).1
        have hb : z∈T1 := hActualSourcePrePointMembership (1:Fin 8) _ _ (hSourceBranchSectorEnd (3:Fin 6))
        dsimp only [T2,T1,Set.ofPred] at ha hb
        all_goals rcases hb with hb|hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (2:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceEnd (2:Fin 8)).2.val=(3/7:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (5:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        have ha : z∈T2 := hActualSourcePrePointMembership (2:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (2:Fin 8)).2
        have hb : z∈T3 := hActualSourcePrePointMembership (3:Fin 8) _ _ (hSourceBranchSectorStart (5:Fin 6))
        dsimp only [T2,T3,Set.ofPred] at ha hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (3:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceStart (3:Fin 8)).2.val=(3/7:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (5:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        have ha : z∈T3 := hActualSourcePrePointMembership (3:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (3:Fin 8)).1
        have hb : z∈T2 := hActualSourcePrePointMembership (2:Fin 8) _ _ (hSourceBranchSectorEnd (4:Fin 6))
        dsimp only [T3,T2,Set.ofPred] at ha hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (3:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceEnd (3:Fin 8)).2.val=(4/7:ℝ) := by
        let z := M3 (qFacenorm false false (diskBoundaryPoint (bsource (0:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(4/7:ℝ)
        have ha : z∈T3 := hActualSourcePrePointMembership (3:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (3:Fin 8)).2
        have hb : z∈Aruns (0:Fin 5) := by
          change M3 (qFacenorm false false (diskBoundaryPoint (bsource (0:Fin 6)) (hbsource _)))∈Aruns (0:Fin 5)
          rw [hActualPrecollapseSelectedSeam0Left (bsource (0:Fin 6)) (hbsource 0) (hSourceBranchSectorStart (0:Fin 6))]
          exact hSourceSouthFivePerimeter _ _ (hb0five)
        change z∈Aleft at hb
        dsimp only [T3,Aleft,Set.ofPred] at ha hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (4:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceStart (4:Fin 8)).2.val=(5/7:ℝ) := by
        let z := M3 (qFacenorm false true (diskBoundaryPoint (bsource (5:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        have ha : z∈T4 := hActualSourcePrePointMembership (4:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (4:Fin 8)).1
        have hb : z∈Aruns (0:Fin 5) := by
          exact hSourceSouthFivePerimeter _ _ (hSourceBranchSectorStart (5:Fin 6))
        change z∈Aleft at hb
        dsimp only [T4,Aleft,Set.ofPred] at ha hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (4:Fin 8)).1.val=(0:ℝ) ∧ (actualPreSourceEnd (4:Fin 8)).2.val=(6/7:ℝ) := by
        let z := M3 (qFacenorm false true (diskBoundaryPoint (bsource (4:Fin 6)) (hbsource _)))
        change z.1.val=(0:ℝ) ∧ z.2.val=(6/7:ℝ)
        have ha : z∈T4 := hActualSourcePrePointMembership (4:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (4:Fin 8)).2
        have hb : z∈Aruns (1:Fin 5) := by
          exact hSourceSouthThreePerimeter _ _ (hSourceBranchSectorEnd (3:Fin 6))
        change z∈Pcorner0 at hb
        dsimp only [T4,Pcorner0,Set.ofPred] at ha hb
        all_goals rcases hb with hb|hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (5:Fin 8)).1.val=(3/10:ℝ) ∧ (actualPreSourceStart (5:Fin 8)).2.val=(1:ℝ) := by
        let z := M3 (qFacenorm false true (diskBoundaryPoint (bsource (3:Fin 6)) (hbsource _)))
        change z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        have ha : z∈T5 := hActualSourcePrePointMembership (5:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (5:Fin 8)).1
        have hb : z∈Aruns (1:Fin 5) := by
          exact hSourceSouthThreePerimeter _ _ (hSourceBranchSectorStart (3:Fin 6))
        change z∈Pcorner0 at hb
        dsimp only [T5,Pcorner0,Set.ofPred] at ha hb
        all_goals rcases hb with hb|hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (5:Fin 8)).1.val=(1/3:ℝ) ∧ (actualPreSourceEnd (5:Fin 8)).2.val=(1:ℝ) := by
        let z := M3 (qFacenorm false true (diskBoundaryPoint (bsource (2:Fin 6)) (hbsource _)))
        change z.1.val=(1/3:ℝ) ∧ z.2.val=(1:ℝ)
        have ha : z∈T5 := hActualSourcePrePointMembership (5:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (5:Fin 8)).2
        have hb : z∈Aruns (2:Fin 5) := by
          exact hSourceSouthOneLargePerimeter _ _ (hSourceBranchSectorEnd (1:Fin 6))
        change z∈Pcorner1 at hb
        dsimp only [T5,Pcorner1,Set.ofPred] at ha hb
        all_goals rcases hb with hb|hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (6:Fin 8)).1.val=(1:ℝ) ∧ (actualPreSourceStart (6:Fin 8)).2.val=(4/7:ℝ) := by
        let z := M3 (qFacenorm true false (diskBoundaryPoint (bsource (0:Fin 6)) (hbsource _)))
        change z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        have ha : z∈T6 := hActualSourcePrePointMembership (6:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (6:Fin 8)).1
        have hb : z∈Aruns (2:Fin 5) := by
          change M3 (qFacenorm true false (diskBoundaryPoint (bsource (0:Fin 6)) (hbsource _)))∈Aruns (2:Fin 5)
          rw [←hActualPrecollapseSelectedSeam0Right (bsource (0:Fin 6)) (hbsource 0) (hSourceBranchSectorStart (0:Fin 6))]
          exact hSourceNorthernTreePerimeter 5 (by decide) _ _ hb0five
        change z∈Pcorner1 at hb
        dsimp only [T6,Pcorner1,Set.ofPred] at ha hb
        all_goals rcases hb with hb|hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (6:Fin 8)).1.val=(1:ℝ) ∧ (actualPreSourceEnd (6:Fin 8)).2.val=(3/7:ℝ) := by
        let z := M3 (qFacenorm true false (diskBoundaryPoint (bsource (5:Fin 6)) (hbsource _)))
        change z.1.val=(1:ℝ) ∧ z.2.val=(3/7:ℝ)
        have ha : z∈T6 := hActualSourcePrePointMembership (6:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (6:Fin 8)).2
        have hb : z∈Aruns (3:Fin 5) := by
          exact hSourceSouthFourPerimeter _ _ (hSourceBranchSectorEnd (4:Fin 6))
        change z∈Aright at hb
        dsimp only [T6,Aright,Set.ofPred] at ha hb
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
    · have hs : (actualPreSourceStart (7:Fin 8)).1.val=(1:ℝ) ∧ (actualPreSourceStart (7:Fin 8)).2.val=(2/7:ℝ) := by
        let z := M3 (qFacenorm true false (diskBoundaryPoint (bsource (4:Fin 6)) (hbsource _)))
        change z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        have ha : z∈T7 := hActualSourcePrePointMembership (7:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (7:Fin 8)).1
        have hb : z∈Aruns (3:Fin 5) := by
          exact hSourceSouthFourPerimeter _ _ (hSourceBranchSectorStart (4:Fin 6))
        change z∈Aright at hb
        dsimp only [T7,Aright,Set.ofPred] at ha hb
        rcases ha with ha|ha
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      have he : (actualPreSourceEnd (7:Fin 8)).1.val=(2/3:ℝ) ∧ (actualPreSourceEnd (7:Fin 8)).2.val=(0:ℝ) := by
        let z := M3 (qFacenorm true false (diskBoundaryPoint (bsource (3:Fin 6)) (hbsource _)))
        change z.1.val=(2/3:ℝ) ∧ z.2.val=(0:ℝ)
        have ha : z∈T7 := hActualSourcePrePointMembership (7:Fin 8) _ _
          (hActualEightSourceBranchesBindWholeArcs (7:Fin 8)).2
        have hb : z∈Aruns (4:Fin 5) := by
          exact hSourceSouthTwoPerimeter _ _ (hSourceBranchSectorEnd (2:Fin 6))
        change z∈Abottom at hb
        dsimp only [T7,Abottom,Set.ofPred] at ha hb
        rcases ha with ha|ha
        all_goals
          obtain ⟨ha1,ha2,ha3⟩ := ha
          obtain ⟨hb1,hb2,hb3⟩ := hb
          constructor <;> linarith only [ha1,ha2,ha3,hb1,hb2,hb3]
      exact ⟨hs.1,hs.2,he.1,he.2⟩
  let sourceStartX : Fin 8 → ℝ := ![(1/2:ℝ),1/3,0,0,0,3/10,1,1]
  let sourceStartY : Fin 8 → ℝ := ![(0:ℝ),0,2/7,3/7,5/7,1,4/7,2/7]
  have hActualPreSourceStartCoordinateInjective :
      Function.Injective (fun k : Fin 8 => (sourceStartX k,sourceStartY k)) := by
    intro k l he
    fin_cases k <;> fin_cases l
    all_goals norm_num [sourceStartX,sourceStartY] at he
    all_goals rfl
  have hActualPreSourceStartInjective : Function.Injective actualPreSourceStart := by
    intro k l he
    have hx := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.1.val) he
    have hy := congrArg (fun z : ↥unitInterval × ↥unitInterval => z.2.val) he
    rw [(hActualEightPrecollapseSourceEndpointCoordinates k).1,
      (hActualEightPrecollapseSourceEndpointCoordinates l).1] at hx
    rw [(hActualEightPrecollapseSourceEndpointCoordinates k).2.1,
      (hActualEightPrecollapseSourceEndpointCoordinates l).2.1] at hy
    exact hActualPreSourceStartCoordinateInjective (Prod.ext hx hy)
  have hActualPreSourceStartRunMembership : ∀ (k : Fin 8) (i : Fin 5),
      actualPreSourceStart k∈Aruns i ↔ k=![(4:Fin 8),5,6,7,0] i := by
    intro k i
    fin_cases k <;> fin_cases i
    · change actualPreSourceStart (0:Fin 8)∈Aleft ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (0:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (0:Fin 8)).2.val ∧ (actualPreSourceStart (0:Fin 8)).2.val≤5/7) ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (0:Fin 8)∈Pcorner0 ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (0:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (0:Fin 8)).1.val ∧ (actualPreSourceStart (0:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (0:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (0:Fin 8)).2.val ∧ (actualPreSourceStart (0:Fin 8)).2.val≤1)) ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (0:Fin 8)∈Pcorner1 ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (0:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (0:Fin 8)).1.val ∧ (actualPreSourceStart (0:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (0:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (0:Fin 8)).2.val ∧ (actualPreSourceStart (0:Fin 8)).2.val≤1)) ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (0:Fin 8)∈Aright ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (0:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (0:Fin 8)).2.val ∧ (actualPreSourceStart (0:Fin 8)).2.val≤3/7) ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (0:Fin 8)∈Abottom ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (0:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (0:Fin 8)).1.val ∧ (actualPreSourceStart (0:Fin 8)).1.val≤2/3) ↔ (0:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (1:Fin 8)∈Aleft ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (1:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (1:Fin 8)).2.val ∧ (actualPreSourceStart (1:Fin 8)).2.val≤5/7) ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (1:Fin 8)∈Pcorner0 ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (1:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (1:Fin 8)).1.val ∧ (actualPreSourceStart (1:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (1:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (1:Fin 8)).2.val ∧ (actualPreSourceStart (1:Fin 8)).2.val≤1)) ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (1:Fin 8)∈Pcorner1 ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (1:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (1:Fin 8)).1.val ∧ (actualPreSourceStart (1:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (1:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (1:Fin 8)).2.val ∧ (actualPreSourceStart (1:Fin 8)).2.val≤1)) ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (1:Fin 8)∈Aright ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (1:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (1:Fin 8)).2.val ∧ (actualPreSourceStart (1:Fin 8)).2.val≤3/7) ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (1:Fin 8)∈Abottom ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (1:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (1:Fin 8)).1.val ∧ (actualPreSourceStart (1:Fin 8)).1.val≤2/3) ↔ (1:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (2:Fin 8)∈Aleft ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (2:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (2:Fin 8)).2.val ∧ (actualPreSourceStart (2:Fin 8)).2.val≤5/7) ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (2:Fin 8)∈Pcorner0 ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (2:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (2:Fin 8)).1.val ∧ (actualPreSourceStart (2:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (2:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (2:Fin 8)).2.val ∧ (actualPreSourceStart (2:Fin 8)).2.val≤1)) ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (2:Fin 8)∈Pcorner1 ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (2:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (2:Fin 8)).1.val ∧ (actualPreSourceStart (2:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (2:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (2:Fin 8)).2.val ∧ (actualPreSourceStart (2:Fin 8)).2.val≤1)) ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (2:Fin 8)∈Aright ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (2:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (2:Fin 8)).2.val ∧ (actualPreSourceStart (2:Fin 8)).2.val≤3/7) ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (2:Fin 8)∈Abottom ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (2:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (2:Fin 8)).1.val ∧ (actualPreSourceStart (2:Fin 8)).1.val≤2/3) ↔ (2:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (3:Fin 8)∈Aleft ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (3:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (3:Fin 8)).2.val ∧ (actualPreSourceStart (3:Fin 8)).2.val≤5/7) ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (3:Fin 8)∈Pcorner0 ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (3:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (3:Fin 8)).1.val ∧ (actualPreSourceStart (3:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (3:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (3:Fin 8)).2.val ∧ (actualPreSourceStart (3:Fin 8)).2.val≤1)) ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (3:Fin 8)∈Pcorner1 ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (3:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (3:Fin 8)).1.val ∧ (actualPreSourceStart (3:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (3:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (3:Fin 8)).2.val ∧ (actualPreSourceStart (3:Fin 8)).2.val≤1)) ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (3:Fin 8)∈Aright ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (3:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (3:Fin 8)).2.val ∧ (actualPreSourceStart (3:Fin 8)).2.val≤3/7) ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (3:Fin 8)∈Abottom ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (3:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (3:Fin 8)).1.val ∧ (actualPreSourceStart (3:Fin 8)).1.val≤2/3) ↔ (3:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (4:Fin 8)∈Aleft ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (4:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (4:Fin 8)).2.val ∧ (actualPreSourceStart (4:Fin 8)).2.val≤5/7) ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (4:Fin 8)∈Pcorner0 ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (4:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (4:Fin 8)).1.val ∧ (actualPreSourceStart (4:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (4:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (4:Fin 8)).2.val ∧ (actualPreSourceStart (4:Fin 8)).2.val≤1)) ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (4:Fin 8)∈Pcorner1 ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (4:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (4:Fin 8)).1.val ∧ (actualPreSourceStart (4:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (4:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (4:Fin 8)).2.val ∧ (actualPreSourceStart (4:Fin 8)).2.val≤1)) ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (4:Fin 8)∈Aright ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (4:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (4:Fin 8)).2.val ∧ (actualPreSourceStart (4:Fin 8)).2.val≤3/7) ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (4:Fin 8)∈Abottom ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (4:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (4:Fin 8)).1.val ∧ (actualPreSourceStart (4:Fin 8)).1.val≤2/3) ↔ (4:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (5:Fin 8)∈Aleft ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (5:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (5:Fin 8)).2.val ∧ (actualPreSourceStart (5:Fin 8)).2.val≤5/7) ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (5:Fin 8)∈Pcorner0 ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (5:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (5:Fin 8)).1.val ∧ (actualPreSourceStart (5:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (5:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (5:Fin 8)).2.val ∧ (actualPreSourceStart (5:Fin 8)).2.val≤1)) ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (5:Fin 8)∈Pcorner1 ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (5:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (5:Fin 8)).1.val ∧ (actualPreSourceStart (5:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (5:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (5:Fin 8)).2.val ∧ (actualPreSourceStart (5:Fin 8)).2.val≤1)) ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (5:Fin 8)∈Aright ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (5:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (5:Fin 8)).2.val ∧ (actualPreSourceStart (5:Fin 8)).2.val≤3/7) ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (5:Fin 8)∈Abottom ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (5:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (5:Fin 8)).1.val ∧ (actualPreSourceStart (5:Fin 8)).1.val≤2/3) ↔ (5:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (6:Fin 8)∈Aleft ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (6:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (6:Fin 8)).2.val ∧ (actualPreSourceStart (6:Fin 8)).2.val≤5/7) ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (6:Fin 8)∈Pcorner0 ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (6:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (6:Fin 8)).1.val ∧ (actualPreSourceStart (6:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (6:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (6:Fin 8)).2.val ∧ (actualPreSourceStart (6:Fin 8)).2.val≤1)) ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (6:Fin 8)∈Pcorner1 ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (6:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (6:Fin 8)).1.val ∧ (actualPreSourceStart (6:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (6:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (6:Fin 8)).2.val ∧ (actualPreSourceStart (6:Fin 8)).2.val≤1)) ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (6:Fin 8)∈Aright ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (6:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (6:Fin 8)).2.val ∧ (actualPreSourceStart (6:Fin 8)).2.val≤3/7) ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (6:Fin 8)∈Abottom ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (6:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (6:Fin 8)).1.val ∧ (actualPreSourceStart (6:Fin 8)).1.val≤2/3) ↔ (6:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (7:Fin 8)∈Aleft ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      change ((actualPreSourceStart (7:Fin 8)).1.val=0 ∧ (4/7:ℝ)≤(actualPreSourceStart (7:Fin 8)).2.val ∧ (actualPreSourceStart (7:Fin 8)).2.val≤5/7) ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (0:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (7:Fin 8)∈Pcorner0 ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      change (((actualPreSourceStart (7:Fin 8)).2.val=1 ∧ (0:ℝ)≤(actualPreSourceStart (7:Fin 8)).1.val ∧ (actualPreSourceStart (7:Fin 8)).1.val≤3/10) ∨ ((actualPreSourceStart (7:Fin 8)).1.val=0 ∧ (6/7:ℝ)≤(actualPreSourceStart (7:Fin 8)).2.val ∧ (actualPreSourceStart (7:Fin 8)).2.val≤1)) ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (1:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (7:Fin 8)∈Pcorner1 ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      change (((actualPreSourceStart (7:Fin 8)).2.val=1 ∧ (1/3:ℝ)≤(actualPreSourceStart (7:Fin 8)).1.val ∧ (actualPreSourceStart (7:Fin 8)).1.val≤1) ∨ ((actualPreSourceStart (7:Fin 8)).1.val=1 ∧ (4/7:ℝ)≤(actualPreSourceStart (7:Fin 8)).2.val ∧ (actualPreSourceStart (7:Fin 8)).2.val≤1)) ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (2:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (7:Fin 8)∈Aright ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      change ((actualPreSourceStart (7:Fin 8)).1.val=1 ∧ (2/7:ℝ)≤(actualPreSourceStart (7:Fin 8)).2.val ∧ (actualPreSourceStart (7:Fin 8)).2.val≤3/7) ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (3:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1]
      norm_num
    · change actualPreSourceStart (7:Fin 8)∈Abottom ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      change ((actualPreSourceStart (7:Fin 8)).2.val=0 ∧ (1/2:ℝ)≤(actualPreSourceStart (7:Fin 8)).1.val ∧ (actualPreSourceStart (7:Fin 8)).1.val≤2/3) ↔ (7:Fin 8)=![(4:Fin 8),5,6,7,0] (4:Fin 5)
      rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1,
        (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1]
      norm_num
  have hActualEightNormalizedSourceVerticesInjective : Function.Injective actualSourceEdgeStart := by
    intro k l he
    change Fboundary (actualPreSourceStart k)=Fboundary (actualPreSourceStart l) at he
    rcases (hActualFiveBoundaryRunKernel _ _).mp he with he|⟨i,hk,hl⟩
    · exact hActualPreSourceStartInjective he
    · exact ((hActualPreSourceStartRunMembership k i).mp hk).trans
        ((hActualPreSourceStartRunMembership l i).mp hl).symm
  have hActualEightSourcePathVerticesDistinct (k l : Fin 8) (hkl : k≠l) :
      actualSourceEdgePath k 0≠actualSourceEdgePath l 0 := by
    intro he
    rw [(hActualEightSourceEdgePathEndpoints k).1,
      (hActualEightSourceEdgePathEndpoints l).1] at he
    exact hkl (hActualEightNormalizedSourceVerticesInjective he)
  have hActualEightSourceEdgeEndpointsDistinct (k : Fin 8) :
      actualSourceEdgePath k 0≠actualSourceEdgePath k 1 := by
    intro he
    have hi := hActualEightSourceEdgePathInjective k he
    exact zero_ne_one hi
  have hActualSourcePathInteriorAvoidsItsEndpoints (k : Fin 8) (t : ↥unitInterval)
      (ht0 : t≠0) (ht1 : t≠1) :
      actualSourceEdgePath k t≠actualSourceEdgePath k 0 ∧
        actualSourceEdgePath k t≠actualSourceEdgePath k 1 := by
    exact ⟨fun he => ht0 (hActualEightSourceEdgePathInjective k he),
      fun he => ht1 (hActualEightSourceEdgePathInjective k he)⟩
  have hActualDifferentSurvivingArcsIntersectOnlyAtTheirEndpoints :
      ∀ (k l : Fin 8) (z : ↥unitInterval × ↥unitInterval), k≠l →
        z∈survivingPerimeter k → z∈survivingPerimeter l →
        z=actualPreSourceStart k ∨ z=actualPreSourceEnd k := by
    intro k l z hkl ha hb
    fin_cases k <;> fin_cases l
    · exact False.elim (hkl rfl)
    · change z∈T0 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T2,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T3,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T4,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T5,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T6,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,T7,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T0,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
    · change z∈T1 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T2,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T3,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T4,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T5,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T6,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,T7,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T0,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
    · change z∈T2 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T3,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T4,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T5,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T6,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,T7,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T0,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T2,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
    · change z∈T3 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T4,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T5,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T6,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,T7,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T0,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T2,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T3,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
    · change z∈T4 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T5,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T6,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,T7,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T0,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T2,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T3,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T4,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
    · change z∈T5 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T6,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,T7,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T0,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T2,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T3,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T4,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T5,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
    · change z∈T6 at ha
      change z∈T7 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,T7,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T0 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T0,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T1 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T1,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T2 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T2,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T3 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T3,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T4 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T4,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T5 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T5,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈T6 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,T6,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · exact False.elim (hkl rfl)
  have hActualSurvivingArcRunMeetsOnlyAtEndpoint :
      ∀ (k : Fin 8) (i : Fin 5) (z : ↥unitInterval × ↥unitInterval),
        z∈survivingPerimeter k → z∈Aruns i →
        z=actualPreSourceStart k ∨ z=actualPreSourceEnd k := by
    intro k i z ha hb
    fin_cases k <;> fin_cases i
    · change z∈T0 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,Aleft,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,Pcorner0,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,Pcorner1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,Aright,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T0 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (0:Fin 8) ∨ z=actualPreSourceEnd (0:Fin 8)
      dsimp only [T0,Abottom,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/2:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/2:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (0:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,Aleft,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,Pcorner0,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,Pcorner1,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,Aright,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T1 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (1:Fin 8) ∨ z=actualPreSourceEnd (1:Fin 8)
      dsimp only [T1,Abottom,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1/3:ℝ) ∧ z.2.val=(0:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1/3:ℝ) ∨ z.2.val≠(0:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (1:Fin 8)).2.2.2]
              change z.2.val=(2/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,Aleft,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,Pcorner0,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,Pcorner1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,Aright,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T2 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (2:Fin 8) ∨ z=actualPreSourceEnd (2:Fin 8)
      dsimp only [T2,Abottom,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (2:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,Aleft,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,Pcorner0,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,Pcorner1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,Aright,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T3 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (3:Fin 8) ∨ z=actualPreSourceEnd (3:Fin 8)
      dsimp only [T3,Abottom,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(3/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(3/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (3:Fin 8)).2.2.2]
              change z.2.val=(4/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,Aleft,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,Pcorner0,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,Pcorner1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,Aright,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T4 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (4:Fin 8) ∨ z=actualPreSourceEnd (4:Fin 8)
      dsimp only [T4,Abottom,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(0:ℝ) ∧ z.2.val=(5/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(0:ℝ) ∨ z.2.val≠(5/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.1]
              change z.1.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (4:Fin 8)).2.2.2]
              change z.2.val=(6/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,Aleft,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,Pcorner0,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,Pcorner1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,Aright,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T5 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (5:Fin 8) ∨ z=actualPreSourceEnd (5:Fin 8)
      dsimp only [T5,Abottom,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(3/10:ℝ) ∧ z.2.val=(1:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(3/10:ℝ) ∨ z.2.val≠(1:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.1]
              change z.1.val=(1/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (5:Fin 8)).2.2.2]
              change z.2.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,Aleft,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,Pcorner0,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,Pcorner1,Set.ofPred] at ha hb
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,Aright,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T6 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (6:Fin 8) ∨ z=actualPreSourceEnd (6:Fin 8)
      dsimp only [T6,Abottom,Set.ofPred] at ha hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(4/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(4/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.1]
              change z.1.val=(1:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (6:Fin 8)).2.2.2]
              change z.2.val=(3/7:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈Aleft at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,Aleft,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈Pcorner0 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,Pcorner0,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈Pcorner1 at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,Pcorner1,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals rcases hb with hb|hb
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈Aright at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,Aright,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
    · change z∈T7 at ha
      change z∈Abottom at hb
      change z=actualPreSourceStart (7:Fin 8) ∨ z=actualPreSourceEnd (7:Fin 8)
      dsimp only [T7,Abottom,Set.ofPred] at ha hb
      rcases ha with ha|ha
      all_goals
        obtain ⟨ha1,ha2,ha3⟩ := ha
        obtain ⟨hb1,hb2,hb3⟩ := hb
        by_cases hs : z.1.val=(1:ℝ) ∧ z.2.val=(2/7:ℝ)
        · apply Or.inl
          apply Prod.ext <;> apply Subtype.ext
          · exact hs.1.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).1.symm
          · exact hs.2.trans (hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.1.symm
        · apply Or.inr
          have hn : z.1.val≠(1:ℝ) ∨ z.2.val≠(2/7:ℝ) := not_and_or.mp hs
          rcases hn with hn|hn
          all_goals rcases lt_or_gt_of_ne hn with hn|hn
          all_goals
            apply Prod.ext <;> apply Subtype.ext
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.1]
              change z.1.val=(2/3:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
            · rw [(hActualEightPrecollapseSourceEndpointCoordinates (7:Fin 8)).2.2.2]
              change z.2.val=(0:ℝ)
              linarith only [ha1,ha2,ha3,hb1,hb2,hb3,hn]
  have hActualNormalizedDifferentWholeArcsIntersectOnlyAtOwnVertices :
      ∀ (k l : Fin 8) (z : ↥unitInterval × ↥unitInterval), k≠l →
        z∈Fboundary '' survivingPerimeter k → z∈Fboundary '' survivingPerimeter l →
        z=actualSourceEdgeStart k ∨ z=actualSourceEdgeEnd k := by
    intro k l z hkl hk hl
    obtain ⟨v,hv,hvz⟩ := hk
    obtain ⟨w,hw,hwz⟩ := hl
    have he : Fboundary v=Fboundary w := hvz.trans hwz.symm
    have hendpoint : v=actualPreSourceStart k ∨ v=actualPreSourceEnd k := by
      rcases (hActualFiveBoundaryRunKernel v w).mp he with he|⟨i,hvi,hwi⟩
      · rw [←he] at hw
        exact hActualDifferentSurvivingArcsIntersectOnlyAtTheirEndpoints k l v hkl hv hw
      · exact hActualSurvivingArcRunMeetsOnlyAtEndpoint k i v hv hvi
    rcases hendpoint with he|he
    · exact Or.inl (hvz.symm.trans (congrArg Fboundary he))
    · exact Or.inr (hvz.symm.trans (congrArg Fboundary he))
  have hActualEightSourcePathCrossingForcesEndpoint (k l : Fin 8) (t u : ↥unitInterval)
      (hkl : k≠l) (he : actualSourceEdgePath k t=actualSourceEdgePath l u) : t=0 ∨ t=1 := by
    have hk : actualSourceEdgePath k t∈Fboundary '' survivingPerimeter k := by
      rw [←hActualEightSourceEdgePathWholeImages k]
      exact ⟨t,rfl⟩
    have hl : actualSourceEdgePath k t∈Fboundary '' survivingPerimeter l := by
      rw [he,←hActualEightSourceEdgePathWholeImages l]
      exact ⟨u,rfl⟩
    rcases hActualNormalizedDifferentWholeArcsIntersectOnlyAtOwnVertices k l _ hkl hk hl with hv|hv
    · exact Or.inl (hActualEightSourceEdgePathInjective k
        (hv.trans (hActualEightSourceEdgePathEndpoints k).1.symm))
    · exact Or.inr (hActualEightSourceEdgePathInjective k
        (hv.trans (hActualEightSourceEdgePathEndpoints k).2.symm))
  have hActualEightSourcePathInteriorsDisjoint (k l : Fin 8) (hkl : k≠l)
      (t u : ↥unitInterval) (ht0 : t≠0) (ht1 : t≠1) :
      actualSourceEdgePath k t≠actualSourceEdgePath l u := by
    intro he
    exact (hActualEightSourcePathCrossingForcesEndpoint k l t u hkl he).elim ht0 ht1
  have hActualEightSourceCyclePointEquality : ∀ (k l : Fin 8) (t u : ↥unitInterval),
      actualSourceEdgePath k t=actualSourceEdgePath l u ↔
        (k=l ∧ t=u) ∨ (t=1 ∧ u=0 ∧ l=k+1) ∨ (t=0 ∧ u=1 ∧ k=l+1) := by
    intro k l t u
    constructor
    · intro he
      by_cases hkl : k=l
      · subst l
        exact Or.inl ⟨rfl,hActualEightSourceEdgePathInjective k he⟩
      · have ht := hActualEightSourcePathCrossingForcesEndpoint k l t u hkl he
        have hu := hActualEightSourcePathCrossingForcesEndpoint l k u t (Ne.symm hkl) he.symm
        rcases ht with rfl|rfl <;> rcases hu with rfl|rfl
        · exact False.elim (hActualEightSourcePathVerticesDistinct k l hkl he)
        · have hv : actualSourceEdgeStart k=actualSourceEdgeStart (l+1) := by
            rw [←(hActualEightSourceEdgePathEndpoints k).1,
              ←(hActualEightSourceEdgePathEndpoints (l+1)).1,
              ←hActualEightSourceEdgePathCyclicEndpoints l]
            exact he
          exact Or.inr (Or.inr ⟨rfl,rfl,hActualEightNormalizedSourceVerticesInjective hv⟩)
        · have hv : actualSourceEdgeStart (k+1)=actualSourceEdgeStart l := by
            rw [←(hActualEightSourceEdgePathEndpoints (k+1)).1,
              ←(hActualEightSourceEdgePathEndpoints l).1,
              ←hActualEightSourceEdgePathCyclicEndpoints k]
            exact he
          exact Or.inr (Or.inl ⟨rfl,rfl,(hActualEightNormalizedSourceVerticesInjective hv).symm⟩)
        · have hv : actualSourceEdgeStart (k+1)=actualSourceEdgeStart (l+1) := by
            rw [←(hActualEightSourceEdgePathEndpoints (k+1)).1,
              ←(hActualEightSourceEdgePathEndpoints (l+1)).1,
              ←hActualEightSourceEdgePathCyclicEndpoints k,
              ←hActualEightSourceEdgePathCyclicEndpoints l]
            exact he
          exact False.elim (hkl (add_right_cancel (hActualEightNormalizedSourceVerticesInjective hv)))
    · rintro (⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)
      · rfl
      · exact hActualEightSourceEdgePathCyclicEndpoints k
      · exact (hActualEightSourceEdgePathCyclicEndpoints l).symm
  let SourceCycleRaw := Σ _k : Fin 8, ↥unitInterval
  let RactualCycle : SourceCycleRaw → SourceCycleRaw → Prop :=
    fun a b => a.2=1 ∧ b.2=0 ∧ b.1=a.1+1
  let QactualCycle := Quotient (Relation.EqvGen.setoid RactualCycle)
  let sourceCycleMap : SourceCycleRaw → ↥unitInterval × ↥unitInterval :=
    fun a => actualSourceEdgePath a.1 a.2
  have hActualCycleRawMapContinuous : Continuous sourceCycleMap :=
    continuous_sigma (fun k => (actualSourceEdgePath k).continuous)
  have hActualCycleRelationRespect : ∀ a b, Relation.EqvGen RactualCycle a b →
      sourceCycleMap a=sourceCycleMap b := by
    intro a b h
    induction h with
    | rel a b hr =>
      obtain ⟨ha,hb,hk⟩ := hr
      change actualSourceEdgePath a.1 a.2=actualSourceEdgePath b.1 b.2
      rw [ha,hb,hk]
      exact hActualEightSourceEdgePathCyclicEndpoints a.1
    | refl a => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2
  have hActualSourceCycleExactKernel : ∀ a b,
      sourceCycleMap a=sourceCycleMap b ↔ Relation.EqvGen RactualCycle a b := by
    intro a b
    constructor
    · intro he
      rcases (hActualEightSourceCyclePointEquality a.1 b.1 a.2 b.2).mp he with
        ⟨hk,ht⟩|⟨ht,hu,hk⟩|⟨ht,hu,hk⟩
      · have hab : a=b := Sigma.ext hk (heq_of_eq ht)
        rw [hab]
        exact Relation.EqvGen.refl b
      · exact Relation.EqvGen.rel _ _ ⟨ht,hu,hk⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hu,ht,hk⟩)
    · exact hActualCycleRelationRespect a b
  let SourceCycleBoundary := ↥LiteralPerimeter
  let sourceCycleBoundaryMap : C(SourceCycleRaw,SourceCycleBoundary) :=
    ⟨fun a => ⟨sourceCycleMap a,by
      rw [hActualEightSourcePathsCoverIntrinsicDiskPerimeter]
      exact Set.mem_iUnion.mpr ⟨a.1,⟨a.2,rfl⟩⟩⟩,
      continuous_induced_rng.2 hActualCycleRawMapContinuous⟩
  let actualCycleBoundaryQuotientMap : C(QactualCycle,SourceCycleBoundary) :=
    ⟨Quotient.lift sourceCycleBoundaryMap (fun a b h =>
      Subtype.ext (hActualCycleRelationRespect a b h)),
      continuous_coinduced_dom.mpr sourceCycleBoundaryMap.continuous⟩
  have hActualCycleBoundaryQuotientInjective :
      Function.Injective actualCycleBoundaryQuotientMap := by
    intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        intro he
        apply Quotient.sound
        exact (hActualSourceCycleExactKernel a b).mp (congrArg Subtype.val he)
  have hActualCycleBoundaryQuotientSurjective :
      Function.Surjective actualCycleBoundaryQuotientMap := by
    intro z
    have hz : z.val∈⋃ k : Fin 8, Set.range (actualSourceEdgePath k) :=
      Eq.mp (congrArg (fun U : Set (↥unitInterval × ↥unitInterval) => z.val∈U)
        hActualEightSourcePathsCoverIntrinsicDiskPerimeter) z.property
    obtain ⟨k,t,ht⟩ := Set.mem_iUnion.mp hz
    refine ⟨Quotient.mk _ ⟨k,t⟩,?_⟩
    apply Subtype.ext
    exact ht
  have hActualEightSourceCycleBoundaryHomeomorphism :
      ∃ Hcycle : QactualCycle ≃ₜ SourceCycleBoundary,
        ∀ (k : Fin 8) (t : ↥unitInterval),
          (Hcycle (Quotient.mk _ ⟨k,t⟩)).val=actualSourceEdgePath k t := by
    let Ecycle : QactualCycle ≃ SourceCycleBoundary :=
      Equiv.ofBijective actualCycleBoundaryQuotientMap
        ⟨hActualCycleBoundaryQuotientInjective,hActualCycleBoundaryQuotientSurjective⟩
    let Hcycle : QactualCycle ≃ₜ SourceCycleBoundary :=
      Continuous.homeoOfEquivCompactToT2 (f:=Ecycle) actualCycleBoundaryQuotientMap.continuous
    exact ⟨Hcycle,fun _ _ => rfl⟩
  have hStandardEightCycleCircleHomeomorphism :
      ∃ Hstd : QactualCycle ≃ₜ Circle,
        ∀ (k : Fin 8) (t : unitInterval),
          Hstd (Quotient.mk _ ⟨k,t⟩) = Circle.exp
            (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.sideAngle k t) := by
    classical
    let Raw8 := Σ _k : Fin 8, unitInterval
    let R8 : Raw8 → Raw8 → Prop := fun a b => a.2=1 ∧ b.2=0 ∧ b.1=a.1+1
    let Q8 := Quotient (Relation.EqvGen.setoid R8)
    have hAngles (s u : ℝ) (hs : 0 ≤ s ∧ s ≤ 8) (hu : 0 ≤ u ∧ u ≤ 8) :
        Circle.exp (2 * Real.pi * s / 8) = Circle.exp (2 * Real.pi * u / 8) ↔
          s = u ∨ (s = 0 ∧ u = 8) ∨ (s = 8 ∧ u = 0) := by
      constructor
      · intro h
        obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
        have hmEq : s = u + 8 * (m : ℝ) := by
          have hprod : (2 * Real.pi) * (s - u - 8 * (m : ℝ)) = 0 := by
            linear_combination 8 * hm
          have hzero : s - u - 8 * (m : ℝ) = 0 :=
            (mul_eq_zero.mp hprod).resolve_left (ne_of_gt Real.two_pi_pos)
          linarith
        have hmLower : (-1 : ℝ) ≤ (m : ℝ) := by linarith [hs.1, hu.2]
        have hmUpper : (m : ℝ) ≤ 1 := by linarith [hs.2, hu.1]
        have hmLowerZ : (-1 : ℤ) ≤ m := by exact_mod_cast hmLower
        have hmUpperZ : m ≤ 1 := by exact_mod_cast hmUpper
        interval_cases m
        · right; left; constructor <;> norm_num at hmEq <;> linarith [hs.1, hu.2]
        · left; norm_num at hmEq; exact hmEq
        · right; right; constructor <;> norm_num at hmEq <;> linarith [hs.2, hu.1]
      · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · rfl
        · norm_num [Circle.exp_zero, Circle.exp_two_pi]
        · norm_num [Circle.exp_zero, Circle.exp_two_pi]
    have hScalars (k l : Fin 8) (t u : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (hu : 0 ≤ u ∧ u ≤ 1) :
        (((k.val : ℝ)+t=(l.val : ℝ)+u) ∨
          ((k.val : ℝ)+t=0 ∧ (l.val : ℝ)+u=8) ∨
          ((k.val : ℝ)+t=8 ∧ (l.val : ℝ)+u=0)) ↔
        (k=l ∧ t=u) ∨ (t=1 ∧ u=0 ∧ l=k+1) ∨ (t=0 ∧ u=1 ∧ k=l+1) := by
      fin_cases k <;> fin_cases l
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(0:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(1:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(2:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(3:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(4:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(5:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(6:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((0:ℝ)+t=(7:ℝ)+u ∨ ((0:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((0:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(0:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(1:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(2:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(3:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(4:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(5:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(6:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((1:ℝ)+t=(7:ℝ)+u ∨ ((1:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((1:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(0:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(1:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(2:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(3:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(4:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(5:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(6:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((2:ℝ)+t=(7:ℝ)+u ∨ ((2:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((2:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(0:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(1:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(2:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(3:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(4:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(5:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(6:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((3:ℝ)+t=(7:ℝ)+u ∨ ((3:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((3:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(0:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(1:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(2:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(3:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(4:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(5:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(6:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((4:ℝ)+t=(7:ℝ)+u ∨ ((4:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((4:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(0:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(1:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(2:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(3:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(4:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(5:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(6:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((5:ℝ)+t=(7:ℝ)+u ∨ ((5:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((5:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(0:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(1:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(2:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(3:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(4:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(5:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(6:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((6:ℝ)+t=(7:ℝ)+u ∨ ((6:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((6:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(0:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (0:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (0:ℝ)+u=0)) ↔ (t=1 ∧ u=0)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(1:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (1:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (1:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(2:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (2:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (2:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(3:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (3:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (3:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(4:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (4:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (4:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(5:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (5:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (5:ℝ)+u=0)) ↔ False
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals linarith [ht.1,ht.2,hu.1,hu.2]
        · exact False.elim
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(6:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (6:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (6:ℝ)+u=0)) ↔ (t=0 ∧ u=1)
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          all_goals constructor <;> linarith [ht.1,ht.2,hu.1,hu.2]
        · rintro ⟨rfl,rfl⟩
          norm_num
      · norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, Fin.reduceAdd, Fin.reduceEq,
          Nat.cast_ofNat, true_and, false_and, and_true, and_false, false_or, or_false]
        change ((7:ℝ)+t=(7:ℝ)+u ∨ ((7:ℝ)+t=0 ∧ (7:ℝ)+u=8) ∨
          ((7:ℝ)+t=8 ∧ (7:ℝ)+u=0)) ↔ t=u
        constructor
        · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
          · linarith
          · linarith [ht.1,ht.2,hu.1,hu.2]
          · linarith [ht.1,ht.2,hu.1,hu.2]
        · intro h; left; linarith
    let f : Raw8 → Circle := fun a => Circle.exp (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.sideAngle a.1 a.2)
    have hf : Continuous f := continuous_sigma (fun k =>
      Circle.exp.continuous.comp (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.continuous_sideAngle k))
    have hPoints (k l : Fin 8) (t u : unitInterval) :
        f ⟨k,t⟩=f ⟨l,u⟩ ↔
          (k=l ∧ t=u) ∨ (t=1 ∧ u=0 ∧ l=k+1) ∨ (t=0 ∧ u=1 ∧ k=l+1) := by
      have hk : (k.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
      have hl : (l.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ l.isLt)
      have hs : 0 ≤ (k.val : ℝ)+t.val ∧ (k.val : ℝ)+t.val ≤ 8 := by
        constructor <;> linarith [show (0:ℝ)≤(k.val:ℝ) from Nat.cast_nonneg _,t.property.1,t.property.2]
      have hu : 0 ≤ (l.val : ℝ)+u.val ∧ (l.val : ℝ)+u.val ≤ 8 := by
        constructor <;> linarith [show (0:ℝ)≤(l.val:ℝ) from Nat.cast_nonneg _,u.property.1,u.property.2]
      change Circle.exp (2 * Real.pi * ((k.val : ℝ)+t.val) / 8) =
        Circle.exp (2 * Real.pi * ((l.val : ℝ)+u.val) / 8) ↔ _
      rw [hAngles _ _ hs hu]
      simp only [Subtype.ext_iff]
      change _ ↔ (k=l ∧ t.val=u.val) ∨ (t.val=1 ∧ u.val=0 ∧ l=k+1) ∨
        (t.val=0 ∧ u.val=1 ∧ k=l+1)
      exact hScalars k l t.val u.val t.property u.property
    have hRespect : ∀ a b, Relation.EqvGen R8 a b → f a=f b := by
      intro a b h
      induction h with
      | rel a b h => exact (hPoints a.1 b.1 a.2 b.2).mpr (Or.inr (Or.inl h))
      | refl a => rfl
      | symm a b h ih => exact ih.symm
      | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2
    have hKernel : ∀ a b, f a=f b ↔ Relation.EqvGen R8 a b := by
      intro a b
      constructor
      · intro he
        rcases (hPoints a.1 b.1 a.2 b.2).mp he with
          ⟨hk,ht⟩|⟨ht,hu,hk⟩|⟨ht,hu,hk⟩
        · have hab : a=b := Sigma.ext hk (heq_of_eq ht)
          rw [hab]
          exact Relation.EqvGen.refl b
        · exact Relation.EqvGen.rel _ _ ⟨ht,hu,hk⟩
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hu,ht,hk⟩)
      · exact hRespect a b
    have hSurj : Function.Surjective f := by
      intro z
      obtain ⟨k,t,ht⟩ := LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.exists_side_eq_of_mem_sphere (n:=8) (by norm_num)
        (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.ofCircle 8 z) z.property
      refine ⟨⟨k,t⟩,?_⟩
      apply Subtype.ext
      exact congrArg (fun w : LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 => w.val) ht
    let F : C(Q8,Circle) :=
      ⟨Quotient.lift f hRespect,continuous_coinduced_dom.mpr hf⟩
    have hInj : Function.Injective F := by
      intro a b
      induction a using Quotient.inductionOn with
      | h a =>
        induction b using Quotient.inductionOn with
        | h b =>
          intro he
          exact Quotient.sound ((hKernel a b).mp he)
    have hOnto : Function.Surjective F := by
      intro z
      obtain ⟨a,ha⟩ := hSurj z
      exact ⟨Quotient.mk _ a,ha⟩
    let E : Q8 ≃ Circle := Equiv.ofBijective F ⟨hInj,hOnto⟩
    let H : Q8 ≃ₜ Circle := Continuous.homeoOfEquivCompactToT2 (f:=E) F.continuous
    exact ⟨H,fun _ _ => rfl⟩
  have hActualEightMarkedCircleBoundaryHomeomorphism :
      ∃ Hcircle : Circle ≃ₜ SourceCycleBoundary,
        ∀ (k : Fin 8) (t : unitInterval),
          (Hcircle (Circle.exp
            (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.sideAngle k t))).val =
            actualSourceEdgePath k t := by
    obtain ⟨Hstd,hstd⟩ := hStandardEightCycleCircleHomeomorphism
    obtain ⟨Hactual,hactual⟩ := hActualEightSourceCycleBoundaryHomeomorphism
    let Hcircle : Circle ≃ₜ SourceCycleBoundary := Hstd.symm.trans Hactual
    refine ⟨Hcircle,?_⟩
    intro k t
    rw [←hstd k t]
    change (Hactual (Hstd.symm (Hstd (Quotient.mk _ ⟨k,t⟩)))).val = _
    rw [Hstd.symm_apply_apply]
    exact hactual k t
  have hActualAffineSquareBoundaryExtension :
      ∃ E : (unitInterval × unitInterval) ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.square,
        (∀ z, (E z).val.re=2*z.1.val-1 ∧ (E z).val.im=2*z.2.val-1) ∧
        (∀ z, (E z).val∈LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary ↔ z∈LiteralPerimeter) ∧
        ∃ Eb : SourceCycleBoundary ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary,
          ∀ z, (Eb z).val=(E z.val).val := by
    let f : unitInterval × unitInterval → LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.square := fun z =>
      ⟨⟨2*z.1.val-1,2*z.2.val-1⟩,by
        change max (abs (2*z.1.val-1)) (abs (2*z.2.val-1)) ≤ 1
        rw [max_le_iff,abs_le,abs_le]
        constructor <;> constructor <;> linarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      have hc : Continuous (fun z : unitInterval × unitInterval =>
          ((2*z.1.val-1 : ℝ) : ℂ) + ((2*z.2.val-1 : ℝ) : ℂ) * Complex.I) := by
        fun_prop
      convert hc using 1
      funext z
      apply Complex.ext <;> simp
    have hInj : Function.Injective f := by
      intro z w h
      have hre := congrArg (fun a : LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.square => a.val.re) h
      have him := congrArg (fun a : LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.square => a.val.im) h
      apply Prod.ext <;> apply Subtype.ext
      · change 2*z.1.val-1=2*w.1.val-1 at hre
        linarith
      · change 2*z.2.val-1=2*w.2.val-1 at him
        linarith
    have hSurj : Function.Surjective f := by
      intro w
      have hw : abs (w.val.re) ≤ 1 ∧ abs (w.val.im) ≤ 1 := max_le_iff.mp w.property
      have hre := abs_le.mp hw.1
      have him := abs_le.mp hw.2
      let x : unitInterval := ⟨(w.val.re+1)/2,by constructor <;> linarith⟩
      let y : unitInterval := ⟨(w.val.im+1)/2,by constructor <;> linarith⟩
      refine ⟨(x,y),?_⟩
      apply Subtype.ext
      apply Complex.ext <;> dsimp [f,x,y] <;> ring
    let e := Equiv.ofBijective f ⟨hInj,hSurj⟩
    let E : (unitInterval × unitInterval) ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.square :=
      Continuous.homeoOfEquivCompactToT2 (f:=e) hf
    let A : Set (unitInterval × unitInterval) := Set.ofPred (fun z =>
      z.1.val=0 ∨ z.1.val=1 ∨ z.2.val=0 ∨ z.2.val=1)
    have hBoundary : ∀ z, (E z).val∈LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary ↔ z∈A := by
      intro z
      change max (abs (2*z.1.val-1)) (abs (2*z.2.val-1))=1 ↔ _
      have hx : abs (2*z.1.val-1) ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [z.1.property.1,z.1.property.2]
      have hy : abs (2*z.2.val-1) ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [z.2.property.1,z.2.property.2]
      constructor
      · intro h
        rcases le_total (abs (2*z.1.val-1)) (abs (2*z.2.val-1)) with ht|ht
        · rw [max_eq_right ht] at h
          rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp h with h|h
          · right; right; right; linarith
          · right; right; left; linarith
        · rw [max_eq_left ht] at h
          rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp h with h|h
          · right; left; linarith
          · left; linarith
      · rintro (h|h|h|h)
        · rw [h]; norm_num; exact hy
        · rw [h]; norm_num; exact hy
        · rw [h]; norm_num; exact hx
        · rw [h]; norm_num; exact hx
    let fb : C(A,LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary) :=
      ⟨fun z => ⟨(E z.val).val,(hBoundary z.val).mpr z.property⟩,
        continuous_induced_rng.2
          ((continuous_subtype_val : Continuous (fun w : LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.square => w.val)).comp
            (E.continuous.comp (continuous_subtype_val : Continuous (fun z : A => z.val))))⟩
    let gb : C(LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary,A) :=
      ⟨fun w => ⟨E.symm (LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundaryInclusion w),by
        apply (hBoundary _).mp
        rw [E.apply_symm_apply]
        exact w.property⟩,
        continuous_induced_rng.2 (E.symm.continuous.comp LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundaryInclusion.continuous)⟩
    have hleft : Function.LeftInverse gb fb := by
      intro z
      apply Subtype.ext
      change E.symm ⟨(E z.val).val,_⟩=z.val
      exact E.symm_apply_apply z.val
    have hright : Function.RightInverse gb fb := by
      intro w
      apply Subtype.ext
      change (E (E.symm (LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundaryInclusion w))).val=w.val
      rw [E.apply_symm_apply]
      rfl
    let Eb : A ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary :=
      ⟨⟨fb,gb,hleft,hright⟩,fb.continuous,gb.continuous⟩
    exact ⟨E,fun _ => ⟨rfl,rfl⟩,hBoundary,Eb,fun _ => rfl⟩
  have hActualMarkedOctagonCutDiskHomeomorphism :
      ∃ Edisk : LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 ≃ₜ
          (unitInterval × unitInterval),
        ∀ (k : Fin 8) (t : unitInterval),
          Edisk (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side k t)=
            actualSourceEdgePath k t := by
    obtain ⟨E,hEcoords,hEboundary,Eb,hEb⟩ := hActualAffineSquareBoundaryExtension
    obtain ⟨Hcircle,hcircle⟩ := hActualEightMarkedCircleBoundaryHomeomorphism
    let b : Circle ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.boundary :=
      Hcircle.trans Eb
    let Edisk : LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 ≃ₜ
        (unitInterval × unitInterval) :=
      (LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.cellSquareHomeomorph b).trans E.symm
    refine ⟨Edisk,?_⟩
    intro k t
    change E.symm
      (LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.cellSquareHomeomorph b
        (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.ofCircle 8
          (Circle.exp (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.sideAngle k t)))) = _
    rw [LeanEval.Topology.ClassificationOfSurfaces.DiskSquare.cellSquareHomeomorph_ofCircle]
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    change (Eb (Hcircle (Circle.exp
      (LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.sideAngle k t)))).val = _
    exact (hEb _).trans (congrArg (fun z => (E z).val) (hcircle k t))
  obtain ⟨actualMarkedDisk,hActualMarkedDiskSidePins⟩ := hActualMarkedOctagonCutDiskHomeomorphism
  let ActualPolygonCell := LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8
  let actualPolygonSide : Fin 8 → C(unitInterval,ActualPolygonCell) :=
    LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side
  let RactualPolygon : ActualPolygonCell → ActualPolygonCell → Prop :=
    fun z w => ∃ (i : Fin 4) (t : unitInterval),
      z=actualPolygonSide (firstFourSourceIndex i) t ∧
      w=actualPolygonSide (actualSourcePartner (firstFourSourceIndex i)) (unitInterval.symmHomeomorph t)
  have hActualPolygonGeneratorForward : ∀ z w, RactualPolygon z w →
      RactualEightPaths (actualMarkedDisk z) (actualMarkedDisk w) := by
    rintro z w ⟨i,t,rfl,rfl⟩
    exact ⟨i,t,hActualMarkedDiskSidePins _ _,hActualMarkedDiskSidePins _ _⟩
  have hActualPolygonGeneratorBackward : ∀ z w, RactualEightPaths z w →
      RactualPolygon (actualMarkedDisk.symm z) (actualMarkedDisk.symm w) := by
    rintro z w ⟨i,t,rfl,rfl⟩
    refine ⟨i,t,?_,?_⟩
    · rw [←hActualMarkedDiskSidePins _ _,actualMarkedDisk.symm_apply_apply]
    · rw [←hActualMarkedDiskSidePins _ _,actualMarkedDisk.symm_apply_apply]
  have hActualPolygonGeneratedForward : ∀ z w, Relation.EqvGen RactualPolygon z w →
      Relation.EqvGen RactualEightPaths (actualMarkedDisk z) (actualMarkedDisk w) := by
    intro z w h
    induction h with
    | rel z w h => exact Relation.EqvGen.rel _ _ (hActualPolygonGeneratorForward z w h)
    | refl z => exact Relation.EqvGen.refl _
    | symm z w h ih => exact Relation.EqvGen.symm _ _ ih
    | trans z w v h1 h2 ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have hActualPolygonGeneratedBackward : ∀ z w, Relation.EqvGen RactualEightPaths z w →
      Relation.EqvGen RactualPolygon (actualMarkedDisk.symm z) (actualMarkedDisk.symm w) := by
    intro z w h
    induction h with
    | rel z w h => exact Relation.EqvGen.rel _ _ (hActualPolygonGeneratorBackward z w h)
    | refl z => exact Relation.EqvGen.refl _
    | symm z w h ih => exact Relation.EqvGen.symm _ _ ih
    | trans z w v h1 h2 ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  let actualPolygonAttaching : C(ActualPolygonCell,Total) :=
    Jnormalized.comp ⟨actualMarkedDisk,actualMarkedDisk.continuous⟩
  have hActualPolygonAttachingExactKernel : ∀ z w,
      actualPolygonAttaching z=actualPolygonAttaching w ↔ Relation.EqvGen RactualPolygon z w := by
    intro z w
    constructor
    · intro h
      have hgen := hActualPolygonGeneratedBackward _ _
        ((hActualNormalizedAttachingExactEightSourcePathKernel _ _).mp h)
      change Relation.EqvGen RactualPolygon (actualMarkedDisk.symm (actualMarkedDisk z)) (actualMarkedDisk.symm (actualMarkedDisk w)) at hgen
      rw [actualMarkedDisk.symm_apply_apply,actualMarkedDisk.symm_apply_apply] at hgen
      exact hgen
    · intro h
      exact (hActualNormalizedAttachingExactEightSourcePathKernel _ _).mpr
        (hActualPolygonGeneratedForward z w h)
  have hActualPolygonAttachingSurjective : Function.Surjective actualPolygonAttaching := by
    intro x
    obtain ⟨z,hz⟩ := hActualNormalizedDiskAttachingSurj x
    exact ⟨actualMarkedDisk.symm z,by
      change Jnormalized (actualMarkedDisk (actualMarkedDisk.symm z))=x
      rw [actualMarkedDisk.apply_symm_apply]
      exact hz⟩
  let ActualPolygonQuotient := Quotient (Relation.EqvGen.setoid RactualPolygon)
  let actualPolygonQuotientAttaching : C(ActualPolygonQuotient,Total) :=
    ⟨Quotient.lift actualPolygonAttaching (fun z w h =>
      (hActualPolygonAttachingExactKernel z w).mpr h),
      continuous_coinduced_dom.mpr actualPolygonAttaching.continuous⟩
  have hActualPolygonQuotientAttachingInjective : Function.Injective actualPolygonQuotientAttaching := by
    intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        intro h
        exact Quotient.sound ((hActualPolygonAttachingExactKernel a b).mp h)
  have hActualPolygonQuotientAttachingSurjective : Function.Surjective actualPolygonQuotientAttaching := by
    intro x
    obtain ⟨z,hz⟩ := hActualPolygonAttachingSurjective x
    exact ⟨Quotient.mk _ z,hz⟩
  letI : CompactSpace ActualPolygonCell := actualMarkedDisk.symm.compactSpace
  have hActualLiteralMarkedOctagonQuotientHomeomorphismTotal :
      ∃ Hpolygon : ActualPolygonQuotient ≃ₜ Total,
        ∀ z, Hpolygon (Quotient.mk _ z)=Jnormalized (actualMarkedDisk z) := by
    let Epolygon := Equiv.ofBijective actualPolygonQuotientAttaching
      ⟨hActualPolygonQuotientAttachingInjective,hActualPolygonQuotientAttachingSurjective⟩
    let Hpolygon : ActualPolygonQuotient ≃ₜ Total :=
      Continuous.homeoOfEquivCompactToT2 (f:=Epolygon) actualPolygonQuotientAttaching.continuous
    exact ⟨Hpolygon,fun _ => rfl⟩
  have hActualSourceWordGeometricGenusTwoNormalization :
      let word : List (LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart (Fin 4)) :=
        [.pos 0,.pos 1,.pos 2,.pos 3,.neg 2,.neg 0,.neg 3,.neg 1]
      ∃ valid : (LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.Dyck.oneFace word).IsSurfaceValid,
        Nonempty ((LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.Dyck.oneFace word).PolygonalRealization valid ≃ₜ
          Quot (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel 2 0))
    := by
    classical
    let word : List (LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart (Fin 4)) :=
      [.pos 0,.pos 1,.pos 2,.pos 3,.neg 2,.neg 0,.neg 3,.neg 1]
    have valid : (LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.Dyck.oneFace word).IsSurfaceValid := by
      have hface : Nonempty (LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.Dyck.oneFace word).Face := ⟨⟨0,by decide⟩⟩
      refine ⟨hface,?_,?_,?_⟩
      · intro f
        fin_cases f
        decide
      · intro f g h
        fin_cases f <;> fin_cases g <;> rfl
      · intro e
        fin_cases e <;> right
        all_goals norm_num [word,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.Dyck.oneFace,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.edgeMultiplicity,
          LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.faceEdgeMultiplicity,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.boundary,
          LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.edgeOfDart]
        all_goals decide
    let form : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.WordReduction.Pairing.InterleavedOccurrenceForm word (0:Fin 4) (1:Fin 4) :=
      { bNegativeInside := false
        beforeB := []
        beforeNegA := [.pos 2,.pos 3,.neg 2]
        beforeOutsideB := [.neg 3]
        remainder := []
        rotated := by simpa [word,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.WordReduction.Pairing.dart] using (List.IsRotated.refl word)
        edge_ne := by decide
        a_not_mem_beforeB := by decide
        a_not_mem_beforeNegA := by decide
        a_not_mem_beforeOutsideB := by decide
        a_not_mem_remainder := by decide
        b_not_mem_beforeB := by decide
        b_not_mem_beforeNegA := by decide
        b_not_mem_beforeOutsideB := by decide
        b_not_mem_remainder := by decide }
    obtain ⟨vg,hgroup⟩ := form.exists_normalizationEquivalent_grouped valid
    let names : Fin 4 ≃ LeanEval.Topology.ClassificationOfSurfaces.NormalForm.OrientableEdge 2 0 :=
      { toFun := ![LeanEval.Topology.ClassificationOfSurfaces.NormalForm.OrientableEdge.a 0,.b 0,.b 1,.a 1]
        invFun := fun x => match x with
          | .a i => if i=0 then 0 else 3
          | .b i => if i=0 then 1 else 2
          | .c i => Fin.elim0 i
          | .h i => Fin.elim0 i
        left_inv := by intro i; fin_cases i <;> rfl
        right_inv := by
          intro x
          cases x with
          | a i => fin_cases i <;> rfl
          | b i => fin_cases i <;> rfl
          | c i => exact Fin.elim0 i
          | h i => exact Fin.elim0 i }
    let relabel : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.EdgeRelabeling (Fin 4) (LeanEval.Topology.ClassificationOfSurfaces.NormalForm.OrientableEdge 2 0) :=
      ⟨names,fun i => decide (i=3)⟩
    have hword : (form.groupedWord.map relabel.mapDart).IsRotated
        (LeanEval.Topology.ClassificationOfSurfaces.NormalForm.orientableBoundaryWord 2 0) := by
      have he : form.groupedWord.map relabel.mapDart = LeanEval.Topology.ClassificationOfSurfaces.NormalForm.orientableBoundaryWord 2 0 := by
        decide
      rw [he]
    let result := LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.WordReduction.orientableNormalizationResultOfSignedRotated form.groupedWord relabel hword vg
      (by simp [LeanEval.Topology.ClassificationOfSurfaces.NormalForm.IsEvalAdmissible])
    let hcanon := (LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.NormalizationResult.ofEquivalent hgroup result).realizationHomeomorph
    exact ⟨valid,⟨hcanon.trans (LeanEval.Topology.ClassificationOfSurfaces.NormalForm.canonicalOrientableRealizationHomeomorph
      (by simp))⟩⟩
  have hActualFaithfulSourcePolygonQuotientAdapter :
      let word : List (LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart (Fin 4)) :=
        [.pos 0,.pos 1,.pos 2,.pos 3,.neg 2,.neg 0,.neg 3,.neg 1]
      let P := LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.Dyck.oneFace word
      ∃ valid : P.IsSurfaceValid, Nonempty (P.PolygonalRealization valid ≃ₜ ActualPolygonQuotient) := by
    classical
    let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
      [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
        LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
    let partner : Fin 8 → Fin 8 := ![5,7,4,6,2,0,3,1]
    let first : Fin 4 → Fin 8 := fun i => ⟨i.val,by omega⟩
    let R : LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 → LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 → Prop := fun z w =>
      ∃ (i : Fin 4) (t : unitInterval), z=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (first i) t ∧
        w=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (partner (first i)) (unitInterval.symmHomeomorph t)
    have hValidConnected :
        let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
          [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
            LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
        P.IsSurfaceValid ∧ P.IsConnected
        := by
      let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
        [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
          LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
      have hface : Nonempty P.Face := ⟨⟨0,by decide⟩⟩
      constructor
      · refine ⟨hface,?_,?_,?_⟩
        · intro f
          fin_cases f
          decide
        · intro f g h
          fin_cases f <;> fin_cases g <;> rfl
        · intro e
          fin_cases e <;> right
          all_goals norm_num [P,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.edgeMultiplicity,
            LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.faceEdgeMultiplicity,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.boundary,
            LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.edgeOfDart]
          all_goals decide
      · refine ⟨hface,?_⟩
        intro f g
        fin_cases f <;> fin_cases g
        exact Relation.ReflTransGen.refl
    have hPreCell :
        let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
          [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
            LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
        ∃ E : P.PolygonalPreRealization ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8,
          ∀ (o : P.BoundaryOccurrence) (t : unitInterval),
            (E ((P.occurrenceSide o).point t)).val =
              (Circle.exp (2*Real.pi*((o.2.val:ℝ)+t.val)/8) : ℂ)
        := by
      let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
        [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
          LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
      let f : P.PolygonalPreRealization → LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 := fun x => ⟨x.2.val,x.2.property⟩
      let g : LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 → P.PolygonalPreRealization := fun z => ⟨0,⟨z.val,z.property⟩⟩
      have hf : Continuous f := by
        apply continuous_sigma
        intro k
        exact continuous_induced_rng.2 LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.continuous_val
      have hg : Continuous g := by
        exact continuous_sigmaMk.comp (continuous_induced_rng.2 LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.continuous_val)
      have hleft : Function.LeftInverse g f := by
        rintro ⟨k,z⟩
        fin_cases k
        rfl
      have hright : Function.RightInverse g f := by
        intro z
        rfl
      let E : P.PolygonalPreRealization ≃ₜ LeanEval.Topology.ClassificationOfSurfaces.PolygonCell 8 := ⟨⟨f,g,hleft,hright⟩,hf,hg⟩
      refine ⟨E,?_⟩
      rintro ⟨k,i⟩ t
      fin_cases k
      rfl
    have hPairings :
        let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
          [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
            LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
        let partner : Fin 8 → Fin 8 := ![5,7,4,6,2,0,3,1]
        ∀ pairing : P.BoundaryPairing,
          ∃ k : Fin 8, pairing.source.2.val=k.val ∧
            pairing.target.2.val=(partner k).val ∧ pairing.direction=.opposite
        := by
      let P : LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation := ⟨4,
        [[LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 1,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.pos 3,
          LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 2,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 0,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 3,LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.neg 1]]⟩
      let partner : Fin 8 → Fin 8 := ![5,7,4,6,2,0,3,1]
      change ∀ pairing : P.BoundaryPairing,
        ∃ k : Fin 8, pairing.source.2.val=k.val ∧
          pairing.target.2.val=(partner k).val ∧ pairing.direction=.opposite
      rintro ⟨⟨sf,si⟩,⟨tf,ti⟩,hne,hs,ht,dir,hcompat⟩
      fin_cases sf <;> fin_cases tf
      fin_cases si <;> fin_cases ti <;> cases dir
      all_goals simp [P,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.BoundaryOccurrence.dart,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.boundary,
        LeanEval.Topology.ClassificationOfSurfaces.SurfaceCellComplex.SignedDart.flip] at hcompat
      all_goals simp at hne
      all_goals first
        | exact ⟨0,rfl,rfl,rfl⟩
        | exact ⟨1,rfl,rfl,rfl⟩
        | exact ⟨2,rfl,rfl,rfl⟩
        | exact ⟨3,rfl,rfl,rfl⟩
        | exact ⟨4,rfl,rfl,rfl⟩
        | exact ⟨5,rfl,rfl,rfl⟩
        | exact ⟨6,rfl,rfl,rfl⟩
        | exact ⟨7,rfl,rfl,rfl⟩
    have valid : P.IsSurfaceValid := hValidConnected.1
    obtain ⟨Epre,hEpre⟩ := hPreCell
    let Pside (k : Fin 8) (t : unitInterval) : P.PolygonalPreRealization :=
      ⟨0,LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side k t⟩
    have hPside (k : Fin 8) (t : unitInterval) : Epre (Pside k t)=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side k t := by
      apply LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.ext
      exact hEpre ⟨0,k⟩ t
    have hForward : ∀ a b, LeanEval.Topology.ClassificationOfSurfaces.PolygonGluing.Generator (P.polygonalIdentifications valid) a b →
        Relation.EqvGen R (Epre a) (Epre b) := by
      intro a b h
      cases h with
      | glue ident hi t =>
        obtain ⟨pairing,rfl⟩ := hi
        obtain ⟨k,hsrc,htgt,hdir⟩ := hPairings pairing
        have hs : Epre ((P.occurrenceSide pairing.source).point t)=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side k t := by
          apply LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.ext
          change (Epre ((P.occurrenceSide pairing.source).point t)).val =
            (Circle.exp (2*Real.pi*((k.val:ℝ)+t.val)/8) : ℂ)
          simpa only [hsrc] using hEpre pairing.source t
        have ht : Epre ((P.occurrenceSide pairing.target).point (unitInterval.symmHomeomorph t))=
            LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (partner k) (unitInterval.symmHomeomorph t) := by
          apply LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.ext
          change (Epre ((P.occurrenceSide pairing.target).point (unitInterval.symmHomeomorph t))).val =
            (Circle.exp (2*Real.pi*(((partner k).val:ℝ)+(unitInterval.symmHomeomorph t).val)/8) : ℂ)
          simpa only [htgt] using hEpre pairing.target (unitInterval.symmHomeomorph t)
        change Relation.EqvGen R (Epre ((P.occurrenceSide pairing.source).point t))
          (Epre ((P.occurrenceSide pairing.target).point (pairing.direction.homeomorph t)))
        rw [hdir]
        change Relation.EqvGen R (Epre ((P.occurrenceSide pairing.source).point t))
          (Epre ((P.occurrenceSide pairing.target).point (unitInterval.symmHomeomorph t)))
        rw [hs,ht]
        fin_cases k
        · exact Relation.EqvGen.rel _ _ ⟨0,t,rfl,rfl⟩
        · exact Relation.EqvGen.rel _ _ ⟨1,t,rfl,rfl⟩
        · exact Relation.EqvGen.rel _ _ ⟨2,t,rfl,rfl⟩
        · exact Relation.EqvGen.rel _ _ ⟨3,t,rfl,rfl⟩
        · apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          refine ⟨2,unitInterval.symmHomeomorph t,rfl,?_⟩
          change LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (4:Fin 8) t=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (4:Fin 8) (unitInterval.symm (unitInterval.symm t))
          rw [unitInterval.symm_symm]
        · apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          refine ⟨0,unitInterval.symmHomeomorph t,rfl,?_⟩
          change LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (5:Fin 8) t=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (5:Fin 8) (unitInterval.symm (unitInterval.symm t))
          rw [unitInterval.symm_symm]
        · apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          refine ⟨3,unitInterval.symmHomeomorph t,rfl,?_⟩
          change LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (6:Fin 8) t=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (6:Fin 8) (unitInterval.symm (unitInterval.symm t))
          rw [unitInterval.symm_symm]
        · apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          refine ⟨1,unitInterval.symmHomeomorph t,rfl,?_⟩
          change LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (7:Fin 8) t=LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side (7:Fin 8) (unitInterval.symm (unitInterval.symm t))
          rw [unitInterval.symm_symm]
    have hAllEdgesTwice (e : P.Edge) : P.edgeMultiplicity e=2 := by
      fin_cases e
      all_goals norm_num [P,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.edgeMultiplicity,
        LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.faceEdgeMultiplicity,LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.boundary,
        LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.edgeOfDart]
      all_goals decide
    have hBackward : ∀ z w, R z w →
        Relation.EqvGen (LeanEval.Topology.ClassificationOfSurfaces.PolygonGluing.Generator (P.polygonalIdentifications valid))
          (Epre.symm z) (Epre.symm w) := by
      rintro z w ⟨i,t,rfl,rfl⟩
      let pairing : P.BoundaryPairing :=
        { source := ⟨0,first i⟩
          target := ⟨0,partner (first i)⟩
          source_ne_target := by fin_cases i <;> exact of_decide_eq_true rfl
          source_not_boundary := by
            change P.edgeMultiplicity _ ≠ 1
            rw [hAllEdgesTwice]
            decide
          target_not_boundary := by
            change P.edgeMultiplicity _ ≠ 1
            rw [hAllEdgesTwice]
            decide
          direction := .opposite
          compatible := by fin_cases i <;> exact of_decide_eq_true rfl }
      rw [←hPside _ _,←hPside _ _,Epre.symm_apply_apply,Epre.symm_apply_apply]
      have hGlue : LeanEval.Topology.ClassificationOfSurfaces.PolygonGluing.Generator (P.polygonalIdentifications valid)
          ((P.occurrenceSide pairing.source).point t)
          ((P.occurrenceSide pairing.target).point (unitInterval.symmHomeomorph t)) :=
        LeanEval.Topology.ClassificationOfSurfaces.PolygonGluing.Generator.glue pairing.identification
          (LeanEval.Topology.ClassificationOfSurfaces.FiniteCyclicPresentation.pairing_identification_mem valid pairing) t
      exact Relation.EqvGen.rel _ _ hGlue
    have hForwardGen : ∀ a b,
        Relation.EqvGen (LeanEval.Topology.ClassificationOfSurfaces.PolygonGluing.Generator (P.polygonalIdentifications valid)) a b →
          Relation.EqvGen R (Epre a) (Epre b) := by
      intro a b h
      induction h with
      | rel a b h => exact hForward a b h
      | refl a => exact Relation.EqvGen.refl _
      | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c h1 h2 ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    have hBackwardGen : ∀ z w, Relation.EqvGen R z w →
        Relation.EqvGen (LeanEval.Topology.ClassificationOfSurfaces.PolygonGluing.Generator (P.polygonalIdentifications valid))
          (Epre.symm z) (Epre.symm w) := by
      intro z w h
      induction h with
      | rel z w h => exact hBackward z w h
      | refl z => exact Relation.EqvGen.refl _
      | symm z w h ih => exact Relation.EqvGen.symm _ _ ih
      | trans z w v h1 h2 ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    have hRelations : ∀ a b, (P.PolygonalGluingRel valid) a b ↔
        (Relation.EqvGen.setoid R) (Epre a) (Epre b) := by
      intro a b
      constructor
      · exact hForwardGen a b
      · intro h
        have hb := hBackwardGen _ _ h
        rw [Epre.symm_apply_apply,Epre.symm_apply_apply] at hb
        exact hb
    exact ⟨valid,⟨Homeomorph.Quotient.congr Epre hRelations⟩⟩
  have hActualEntireAlternatingTotalStandardGenusTwoOctagon :
      Nonempty (Total ≃ₜ Quot (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel 2 0)) := by
    obtain ⟨validAdapter,⟨Eadapter⟩⟩ := hActualFaithfulSourcePolygonQuotientAdapter
    obtain ⟨validNormal,⟨Enormal⟩⟩ := hActualSourceWordGeometricGenusTwoNormalization
    obtain ⟨Hpolygon,hpolygonPins⟩ := hActualLiteralMarkedOctagonQuotientHomeomorphismTotal
    exact ⟨Hpolygon.symm.trans (Eadapter.symm.trans Enormal)⟩
  exact hActualEntireAlternatingTotalStandardGenusTwoOctagon
end CurveComplexGenusTwo.SourceTopology
