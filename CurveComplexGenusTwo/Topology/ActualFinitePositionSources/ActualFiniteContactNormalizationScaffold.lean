import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.CountControlledChordAndTails
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualFiniteContactIsolatedWholeCrosscutsNamed
import CurveComplexGenusTwo.Filtration.Geometry.ActualCompactTimeCrosscutExtraction
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedTrimmedCrosscutAssembly
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteTransverseCrosscutRedrawing
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedPreparedFamilyCover
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedBothEndpointClearance
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut

open Set Schoenflies

set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CurveComplex.HyperellipticModel.ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Normalize the literal finite contacts with the fixed anchor without
increasing their count, in the original marked isotopy class. -/
theorem actual_finite_contact_transverse_normalization
    (M : HyperellipticModel E S) (anchor b : EssentialMarkedArc M)
    (hf : (crossings M anchor b).Finite) :
    ∃ c : EssentialMarkedArc M,
      vertex M c = vertex M b ∧
      (crossings M anchor c).Finite ∧
      (∀ p ∈ crossings M anchor c, CrossesInDisk M anchor c p) ∧
      (crossings M anchor c).ncard ≤ (crossings M anchor b).ncard := by
  classical
  let old : Unit → EssentialMarkedArc M := fun _ => anchor
  let K := {p // p ∈ crossings M anchor b}
  letI : Fintype K := hf.fintype
  obtain ⟨α,β,e,F,hbounds,hEsub,hEdis,hemarks,hEsquare,hpoint,hcentral,hEends,hEcurve,
    hEslice,haxis,hisolate,hends0,houtside0⟩ := actual_finite_contact_isolated_whole_crosscuts M anchor b hf
  let a := b
  let label : K → Option Unit := fun _ => some ()
  have hEmarks : ∀ k, Disjoint (F k).source (M.cover.branch : Set S) :=
    fun k => (hemarks k).mono_left (hEsub k)
  have hlabel : ∀ k j x, x ∈ (e k).source →
      (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0) := by
    intro k j x hx
    cases j
    simpa [old,label] using haxis k x hx
  have hends : ∀ k j, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∉ (old j).val.image ∧
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∉ (old j).val.image := fun k _ => hends0 k
  have houtside : ∀ j, Disjoint
      (arcInterior M a \ ⋃ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
      (old j).val.image := fun _ => houtside0
  have hhorizontal : segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) =
      {z : Schoenflies.Plane | z ∈ Schoenflies.Plane.closedSquare 0 1 ∧ z 1 = 0} := by
    ext z
    constructor
    · intro hz
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨t,ht,rfl⟩ := hz
      have h0 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
          (Schoenflies.Plane.mk 1 0) t) 0 = 2*t-1 := by
        simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
      have h1 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
          (Schoenflies.Plane.mk 1 0) t) 1 = 0 := by
        simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]
      refine ⟨?_,h1⟩
      change Schoenflies.Plane.supDist (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) t) 0 ≤ 1
      simp only [Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,sub_zero]
      rw [h0,h1,abs_zero,max_le_iff]
      constructor
      · rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
      · norm_num
    · intro hz
      have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
        simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hz.1
      have hbound : |z 0| ≤ 1 :=
        (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
      rw [abs_le] at hbound
      rw [segment_eq_image_lineMap]
      refine ⟨(z 0+1)/2,⟨by linarith [hbound.1],by linarith [hbound.2]⟩,?_⟩
      ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
      · simpa [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk] using hz.2.symm
  let A : Set Schoenflies.Plane := segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0)
  have hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) :=
    Schoenflies.isArcBetween_segment (by intro h; have hh := congrArg (fun z : Schoenflies.Plane => z 0) h; norm_num [Schoenflies.Plane.mk] at hh)
  have hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
      Schoenflies.Plane.openSquare 0 1 := by
    intro z hz
    have hzline := hhorizontal.le hz.1
    have h0 : |z 0| ≤ 1 := by
      have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
        simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hzline.1
      exact (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
    have hne0 : z 0 ≠ -1 := by
      intro h
      apply hz.2
      left
      ext i
      fin_cases i
      · simpa [Schoenflies.Plane.mk] using h
      · simpa [Schoenflies.Plane.mk] using hzline.2
    have hne1 : z 0 ≠ 1 := by
      intro h
      apply hz.2
      right
      apply Set.mem_singleton_iff.mpr
      ext i
      fin_cases i
      · simpa [Schoenflies.Plane.mk] using h
      · simpa [Schoenflies.Plane.mk] using hzline.2
    rw [Schoenflies.Plane.mem_openSquare_iff]
    intro i
    fin_cases i
    · simp only [PiLp.zero_apply,sub_zero]
      rw [abs_lt]
      exact ⟨lt_of_le_of_ne (abs_le.mp h0).1 hne0.symm,
        lt_of_le_of_ne (abs_le.mp h0).2 hne1⟩
    · simp [hzline.2]
  have hselected (k : K) :
      {x : S | x ∈ (F k).source ∧ F k x ∈ A} =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
    rw [← hEslice k]
    ext x
    constructor
    · intro hx
      have hz := hhorizontal.le hx.2
      exact ⟨⟨hx.1,hz.1⟩,(hEcurve k x hx.1).mpr hz.2⟩
    · intro hx
      exact ⟨hx.1.1,hhorizontal.ge ⟨hx.1.2,(hEcurve k x hx.1.1).mp hx.2⟩⟩
  have hactual (k : K) :
      {x : S | x ∈ (F k).source ∧ F k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩ a.val.image =
      {x : S | x ∈ (F k).source ∧ F k x ∈ A} := (hEslice k).trans (hselected k).symm
  let T : K → OpenPartialHomeomorph Schoenflies.Plane Schoenflies.Plane :=
    fun k => (F k).symm.trans (e k)
  have hTsquare (k : K) : Schoenflies.Plane.closedSquare 0 1 ⊆ (T k).source := by
    intro z hz
    have hzE : z ∈ (F k).target := hEsquare k hz
    exact ⟨hzE,hEsub k ((F k).symm.map_source hzE)⟩
  have hleftSource (k : K) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∈ (F k).source :=
    hcentral k (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr (hbounds k).2.1.le))
  have hrightSource (k : K) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∈ (F k).source :=
    hcentral k (Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr (hbounds k).2.1.le))
  have hleftInv (k : K) : (F k).symm (Schoenflies.Plane.mk (-1) 0) =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
    rw [← (hEends k).1,(F k).left_inv (hleftSource k)]
  have hrightInv (k : K) : (F k).symm (Schoenflies.Plane.mk 1 0) =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
    rw [← (hEends k).2,(F k).left_inv (hrightSource k)]
  have hTargets (k : K) : ∃ B : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween B (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) ∧
      B \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆ Schoenflies.Plane.openSquare 0 1 ∧
      ∀ j, label k = some j → ((T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0}).Finite ∧
        ((T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0}).ncard ≤ 1 ∧
        ∀ p ∈ (T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0},
        ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ (T k).target ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ T k '' B ↔ z 1 = p 1 + m*z 0) := by
    cases hL : label k with
    | none =>
      refine ⟨A,hA,hAi,?_⟩
      intro j hj
      cases hj
    | some j =>
      have ha0 : T k (Schoenflies.Plane.mk (-1) 0) 0 ≠ 0 := by
        intro h0
        have hh : (e k) ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) 0 = 0 := by
          simpa only [T,OpenPartialHomeomorph.trans_apply,hleftInv] using h0
        exact (hends k j).1 ((hlabel k j _ (hEsub k (hleftSource k))).mpr ⟨hL,hh⟩)
      have hb0 : T k (Schoenflies.Plane.mk 1 0) 0 ≠ 0 := by
        intro h0
        have hh : (e k) ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) 0 = 0 := by
          simpa only [T,OpenPartialHomeomorph.trans_apply,hrightInv] using h0
        exact (hends k j).2 ((hlabel k j _ (hEsub k (hrightSource k))).mpr ⟨hL,hh⟩)
      have hOrigSub : ((T k '' A) ∩ {z : Plane | z 0=0}) ⊆ {e k k.val} := by
        rintro z ⟨⟨w,hw,rfl⟩,hz⟩
        have hwT := hTsquare k ((hhorizontal.le hw).1)
        let x := (F k).symm w
        have hxF : x ∈ (F k).source := (F k).symm.map_source hwT.1
        have hxA : x ∈ a.val.image := by
          apply (hEcurve k x hxF).mpr
          change F k ((F k).symm w) 1=0
          rw [(F k).right_inv hwT.1]
          exact (hhorizontal.le hw).2
        have hxanchor : x ∈ anchor.val.image := by
          apply (haxis k x (hEsub k hxF)).mpr
          exact hz
        have hxmarks : x ∉ M.cover.branch :=
          fun hm => Set.disjoint_left.mp (hEmarks k) hxF hm
        have hxcontact : x ∈ crossings M anchor a := ⟨⟨hxanchor,hxmarks⟩,hxA,hxmarks⟩
        have hxeq : x=k.val := (hisolate k x hxF).mp hxcontact
        change e k x ∈ {e k k.val}
        rw [hxeq]
        exact mem_singleton _
      have hOrigFin := (Set.finite_singleton (e k k.val)).subset hOrigSub
      have hOrigCount : ((T k '' A) ∩ {z : Plane | z 0=0}).ncard ≤ 1 := by
        simpa using Set.ncard_le_ncard hOrigSub (Set.finite_singleton _)
      have hSingle : ((T k '' A) ∩ {z : Plane | z 0=0}).Subsingleton := by
        intro x hx y hy
        exact (Set.mem_singleton_iff.mp (hOrigSub hx)).trans
          (Set.mem_singleton_iff.mp (hOrigSub hy)).symm
      rcases Set.eq_empty_or_nonempty ((T k '' A) ∩ {z : Plane | z 0=0}) with hNo | hYes
      · obtain ⟨B,hB,hBi,hfinite,hcount,hgraph⟩ :=
          countControlledProperCrosscutOfNoContact (T k) hNo
        exact ⟨B,hB,hBi,fun _ _ => ⟨hfinite,hcount.trans hOrigCount,hgraph⟩⟩
      · obtain ⟨B,hB,hBi,hfinite,hcount,hgraph⟩ :=
          countControlledProperCrosscutOfOneContact (T k) (hTsquare k) ha0 hb0 hOrigFin hSingle hYes
        exact ⟨B,hB,hBi,fun _ _ => ⟨hfinite,hcount.trans hOrigCount,hgraph⟩⟩
  choose B hB hBi hBcontrol using hTargets
  obtain ⟨G,d,_,hdclass,_,hdreplace⟩ := actual_marked_finite_surface_replacement
    M a K F hEdis hEmarks hEsquare A hA hAi hactual B hB hBi
  let Bp : K → Set S := fun k => {x | x ∈ (F k).source ∧ F k x ∈ B k}
  have hfinite (k : K) (j : Unit) : (Bp k ∩ (old j).val.image).Finite := by
    by_cases hj : label k = some j
    · apply (((hBcontrol k j hj).1).image (e k).symm).subset
      rintro x ⟨hx,hxold⟩
      have hxE : x ∈ (e k).source := hEsub k hx.1
      refine ⟨e k x,⟨?_,((hlabel k j x hxE).mp hxold).2⟩,(e k).left_inv hxE⟩
      refine ⟨F k x,hx.2,?_⟩
      simp only [T,OpenPartialHomeomorph.trans_apply]
      rw [(F k).left_inv hx.1]
    · apply Set.Finite.subset Set.finite_empty
      rintro x ⟨hx,hxold⟩
      exact (hj ((hlabel k j x (hEsub k hx.1)).mp hxold).1).elim
  have hfiniteD (j : Unit) : (arcInterior M d ∩ (old j).val.image).Finite := by
    apply (Set.finite_iUnion (fun k => hfinite k j)).subset
    rintro x ⟨hx,hxold⟩
    have hximage : x ∈ d.val.image := hx.1
    rw [hdreplace] at hximage
    rcases hximage with hxrest | hxnew
    · have hxA : x ∈ arcInterior M a := ⟨hxrest.1,hx.2⟩
      have hxoutside : x ∈ arcInterior M a \ ⋃ k,
          (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
        refine ⟨hxA,?_⟩
        intro hh
        obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
        exact hxrest.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
      exact (Set.disjoint_left.mp (houtside j) hxoutside hxold).elim
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hxnew
      exact Set.mem_iUnion.mpr ⟨k,hk,hxold⟩
  have hBsq (k : K) : B k ⊆ Schoenflies.Plane.closedSquare 0 1 := by
    intro z hz
    by_cases he : z ∈ ({Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} : Set Schoenflies.Plane)
    · rcases he with rfl | he
      · norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
      · rw [Set.mem_singleton_iff.mp he]
        norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
    · exact Schoenflies.Plane.openSquare_subset_closedSquare 0 1 (hBi k ⟨hz,he⟩)
  have hd2local (k : K) (x : S) (hx : x ∈ (F k).source)
      (hxo : F k x ∈ Schoenflies.Plane.openSquare 0 1) :
      x ∈ d.val.image ↔ F k x ∈ B k := by
    rw [hdreplace]
    constructor
    · intro h
      rcases h with h | h
      · have hAselect : x ∈ {x : S | x ∈ (F k).source ∧ F k x ∈ A} := by
          rw [← hactual k]
          exact ⟨⟨hx,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hxo⟩,h.1⟩
        exact False.elim (h.2 (Set.mem_iUnion.mpr ⟨k,hAselect⟩))
      · obtain ⟨l,hl⟩ := Set.mem_iUnion.mp h
        by_cases hkl : k = l
        · subst l
          exact hl.2
        · exact False.elim (Set.disjoint_left.mp (hEdis k l hkl) hx hl.1)
    · intro h
      exact Or.inr (Set.mem_iUnion.mpr ⟨k,hx,h⟩)
  have hTimage (k : K) (x : S) (hx : x ∈ (F k).source) :
      e k x ∈ T k '' B k ↔ F k x ∈ B k := by
    constructor
    · rintro ⟨z,hz,heq⟩
      have hzT := hTsquare k (hBsq k hz)
      have hzE : z ∈ (F k).target := hzT.1
      have hze : (F k).symm z ∈ (e k).source := hzT.2
      have hsymm : (F k).symm z = x :=
        (e k).injOn hze (hEsub k hx) heq
      have hzcoord : z = F k x := by rw [← hsymm,(F k).right_inv hzE]
      exact hzcoord ▸ hz
    · intro hz
      refine ⟨F k x,hz,?_⟩
      change e k ((F k).symm (F k x)) = e k x
      rw [(F k).left_inv hx]
  have htransverse (j : Unit) : ∀ p ∈ arcInterior M d ∩ (old j).val.image,
      ArcSurgery.CrossesInDisk M (old j) d p := by
    intro p hp
    have hpBunion : p ∈ ⋃ k, {x : S | x ∈ (F k).source ∧ F k x ∈ B k} := by
      have hpd : p ∈ d.val.image := hp.1.1
      rw [hdreplace] at hpd
      rcases hpd with hrem | hBmem
      · have hrem' : p ∈ arcInterior M a \ ⋃ k,
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
          refine ⟨⟨hrem.1,hp.1.2⟩,?_⟩
          intro hh
          obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
          exact hrem.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
        exact False.elim (Set.disjoint_left.mp (houtside j) hrem' hp.2)
      · exact hBmem
    obtain ⟨k,hpk⟩ := Set.mem_iUnion.mp hpBunion
    have hpe : p ∈ (e k).source := hEsub k hpk.1
    have hplabel : label k = some j := ((hlabel k j p hpe).mp hp.2).1
    have hp0 : e k p 0 = 0 := ((hlabel k j p hpe).mp hp.2).2
    have hpint : F k p ∈ Schoenflies.Plane.openSquare 0 1 := by
      apply hBi k
      refine ⟨hpk.2,?_⟩
      intro he
      rcases he with he | he
      · have hpa : p = (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
          rw [← hleftInv k,← he,(F k).left_inv hpk.1]
        exact (hends k j).1 (hpa ▸ hp.2)
      · have hpb : p = (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
          rw [← hrightInv k,← Set.mem_singleton_iff.mp he,(F k).left_inv hpk.1]
        exact (hends k j).2 (hpb ▸ hp.2)
    have hpT : e k p ∈ T k '' B k := (hTimage k p hpk.1).mpr hpk.2
    obtain ⟨W,hWo,hpW,hWtarget,m,hm⟩ := (hBcontrol k j hplabel).2.2 (e k p) ⟨hpT,hp0⟩
    have hnear : (F k).source ∩ ((F k) ⁻¹' Schoenflies.Plane.openSquare 0 1 ∩ (e k) ⁻¹' W) ∈ nhds p :=
      Filter.inter_mem ((F k).open_source.mem_nhds hpk.1)
        (Filter.inter_mem (((F k).continuousAt hpk.1).preimage_mem_nhds
          ((Schoenflies.Plane.isOpen_openSquare 0 1).mem_nhds hpint))
          (((e k).continuousAt hpe).preimage_mem_nhds (hWo.mem_nhds hpW)))
    obtain ⟨V,hVsub,hVo,hpV⟩ := mem_nhds_iff.mp hnear
    let F := (e k).restr V
    have hFsource : F.source = (e k).source ∩ V := by
      rw [OpenPartialHomeomorph.restr_source,hVo.interior_eq]
    have hpF : p ∈ F.source := hFsource.symm ▸ ⟨hpe,hpV⟩
    apply actual_affine_graph_crosses_in_disk M (old j) d F p hpF
      ((hEmarks k).mono (fun x hx => (hVsub (hFsource.le hx).2).1) Set.Subset.rfl) hp0 m
    · intro x hx
      have hxe := (hFsource.le hx).1
      change x ∈ (old j).val.image ↔ e k x 0 = 0
      simpa only [hplabel,eq_self,true_and] using hlabel k j x hxe
    · intro x hx
      have hxV := (hFsource.le hx).2
      have hxloc := hVsub hxV
      change x ∈ d.val.image ↔ e k x 1 = e k p 1+m*e k x 0
      rw [hd2local k x hxloc.1 hxloc.2.1,← hTimage k x hxloc.1]
      exact hm (e k x) hxloc.2.2
  have hpatchUnique (k : K) : (Bp k ∩ anchor.val.image).Subsingleton := by
    intro x hx y hy
    have hxE : x ∈ (e k).source := hEsub k hx.1.1
    have hyE : y ∈ (e k).source := hEsub k hy.1.1
    have hxT : e k x ∈ (T k '' B k) ∩ {z : Plane | z 0=0} :=
      ⟨(hTimage k x hx.1.1).mpr hx.1.2,(haxis k x hxE).mp hx.2⟩
    have hyT : e k y ∈ (T k '' B k) ∩ {z : Plane | z 0=0} :=
      ⟨(hTimage k y hy.1.1).mpr hy.1.2,(haxis k y hyE).mp hy.2⟩
    apply (e k).injOn hxE hyE
    exact (Set.ncard_le_one ((hBcontrol k () rfl).1)).mp
      ((hBcontrol k () rfl).2.1) _ hxT _ hyT
  have hcross : crossings M anchor d = arcInterior M d ∩ anchor.val.image := by
    ext x
    simp only [crossings,arcInterior,Set.mem_inter_iff,Set.mem_diff,Set.mem_setOf_eq]
    tauto
  have hcover : ∀ x ∈ crossings M anchor d, ∃ k : K, x ∈ Bp k ∩ anchor.val.image := by
    intro x hx
    rw [hcross] at hx
    have hxd : x ∈ d.val.image := hx.1.1
    rw [hdreplace] at hxd
    rcases hxd with hr | hn
    · exfalso
      apply Set.disjoint_left.mp houtside0 ⟨⟨hr.1,hx.1.2⟩,?_⟩ hx.2
      intro hu
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hu
      exact hr.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hn
      exact ⟨k,hk,hx.2⟩
  let assign : S → S := fun x => if hx : x ∈ crossings M anchor d then
    ((hcover x hx).choose).val else x
  have hassign : ∀ x ∈ crossings M anchor d, assign x ∈ crossings M anchor b := by
    intro x hx
    simpa [assign,hx] using ((hcover x hx).choose).property
  have hassignInj : Set.InjOn assign (crossings M anchor d) := by
    intro x hx y hy he
    let kx := (hcover x hx).choose
    let ky := (hcover y hy).choose
    have hk : kx=ky := Subtype.ext (by simpa [assign,hx,hy,kx,ky] using he)
    apply hpatchUnique kx (hcover x hx).choose_spec
    simpa only [hk] using (hcover y hy).choose_spec
  refine ⟨d,hdclass,?_,?_,Set.ncard_le_ncard_of_injOn assign hassign hassignInj hf⟩
  · rw [hcross]
    exact hfiniteD ()
  · rw [hcross]
    exact htransverse ()


end CurveComplex.HyperellipticModel.ArcSurgery
