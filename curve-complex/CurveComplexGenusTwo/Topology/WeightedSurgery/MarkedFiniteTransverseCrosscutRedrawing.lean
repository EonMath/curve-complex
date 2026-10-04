import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteSurfaceReplacement
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedAffineCrossingDisk
import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_finite_transverse_crosscut_redrawing
    (M : HyperellipticModel E S) {ι K : Type} [Fintype ι] [Fintype K]
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (e F : K → OpenPartialHomeomorph S Plane) (label : K → Option ι)
    (α β : K → ℝ) (hbounds : ∀ k, 0 < α k ∧ α k < β k ∧ β k < 1)
    (hEsub : ∀ k, (F k).source ⊆ (e k).source)
    (hEdis : ∀ i j, i ≠ j → Disjoint (F i).source (F j).source)
    (hEmarks : ∀ k, Disjoint (F k).source (M.cover.branch : Set S))
    (hEsquare : ∀ k, Plane.closedSquare 0 1 ⊆ (F k).target)
    (hcentral : ∀ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source)
    (hEends : ∀ k, F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
      F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0)
    (hEcurve : ∀ k x, x ∈ (F k).source → (x ∈ a.val.image ↔ F k x 1 = 0))
    (hEslice : ∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ a.val.image =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
    (hlabel : ∀ k j x, x ∈ (e k).source →
      (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0))
    (hends : ∀ k j, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∉ (old j).val.image ∧
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∉ (old j).val.image)
    (houtside : ∀ j, Disjoint
      (arcInterior M a \ ⋃ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
      (old j).val.image) :
    ∃ d : EssentialMarkedArc M,
      Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) a ∧
      ∀ j, (arcInterior M d ∩ (old j).val.image).Finite ∧
        ∀ p ∈ arcInterior M d ∩ (old j).val.image, ArcSurgery.CrossesInDisk M (old j) d p := by
  classical
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
      obtain ⟨B,hB,hBi,hfinite,hgraph⟩ := position_proper_affine_crosscut (T k) (hTsquare k) ha0 hb0
      exact ⟨B,hB,hBi,fun _ _ => ⟨hfinite,hgraph⟩⟩
  choose B hB hBi hBcontrol using hTargets
  obtain ⟨G,d,_,hdclass,_,hdreplace⟩ := actual_marked_finite_surface_replacement
    M a K F hEdis hEmarks hEsquare A hA hAi hactual B hB hBi
  let Bp : K → Set S := fun k => {x | x ∈ (F k).source ∧ F k x ∈ B k}
  have hfinite (k : K) (j : ι) : (Bp k ∩ (old j).val.image).Finite := by
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
  have hfiniteD (j : ι) : (arcInterior M d ∩ (old j).val.image).Finite := by
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
  refine ⟨d,hdclass,?_⟩
  intro j
  refine ⟨hfiniteD j,?_⟩
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
  obtain ⟨W,hWo,hpW,hWtarget,m,hm⟩ := (hBcontrol k j hplabel).2 (e k p) ⟨hpT,hp0⟩
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

end CurveComplex.HyperellipticModel
