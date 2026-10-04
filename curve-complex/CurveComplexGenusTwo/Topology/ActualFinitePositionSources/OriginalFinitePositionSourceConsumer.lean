import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualRawSimultaneousCompatibleMinimum
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorPointNearbySlide
import Mathlib.Order.Interval.Set.Infinite

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

private theorem actualRawContactCoordinateMargin
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (C : Set S) (hC : C.Finite) (hCa : C ⊆ anchor.val.image)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (haxis : ∀ q : U, q.val ∈ anchor.val.image ↔ (e q).val 1 = 0)
    (p : U) (hp0 : (e p).val = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ q, q ∈ C → q ≠ p.val → ∀ hq : q ∈ U, ε < |(e ⟨q,hq⟩).val 0| := by
  classical
  let K : Set ℝ := (fun q : U => (e q).val 0) ''
    {q : U | q.val ∈ C ∧ q.val ≠ p.val}
  have hK : K.Finite := ((hC.preimage Subtype.val_injective.injOn).subset
    (show {q : U | q.val ∈ C ∧ q.val ≠ p.val} ⊆ Subtype.val ⁻¹' C from fun _ h => h.1)).image _
  have hn : ∀ x ∈ K, x ≠ 0 := by
    rintro x ⟨q,hq,rfl⟩ he
    apply hq.2
    have hy := (haxis q).mp (hCa hq.1)
    have hqp : (e q).val = (e p).val := by
      rw [hp0]
      ext i
      fin_cases i
      · exact he
      · exact hy
    exact congrArg Subtype.val (e.injective (Subtype.ext hqp))
  obtain ⟨ε,hε,hε1,hcover⟩ := actual_finite_nonzero_coordinate_margin K hK hn
  refine ⟨ε,hε,hε1,?_⟩
  intro q hq hne hqU
  exact hcover _ ⟨⟨q,hqU⟩,⟨hq,hne⟩,rfl⟩

private theorem actualRawRelativeSingleContactAvoidanceMove
    (M : HyperellipticModel E S) (anchor b : EssentialMarkedArc M)
    (hf : (crossings M anchor b).Finite)
    (ht : ∀ z ∈ crossings M anchor b, CrossesInDisk M anchor b z)
    (A : Set S) (hA : IsClosed A)
    (X : Set S) (hX : X.Finite) (p : S) (hp : p ∈ crossings M anchor b)
    (hpA : p ∉ A) :
    ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image) ∧
      (∀ q, q ∈ crossings M anchor b → q ≠ p → ∀ t, G.map (t,q) = q) ∧
      (∀ t z, z ∈ A → G.map (t,z) = z) ∧
      G.finalMap p ∉ X := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨U,V,hU,e,hCV,hm,haxis,hpU,hp0⟩ :=
    actual_crossing_disk_slide_chart M anchor b p (ht p hp)
  have hpPlane : (e ⟨p,hpU⟩).val = 0 := planeCoordinates.injective hp0
  obtain ⟨δ,hδ,hδ1,hmarginδ⟩ := actualRawContactCoordinateMargin M anchor (crossings M anchor b) hf
    (fun _ h => h.1.1) U V e haxis ⟨p,hpU⟩ hpPlane
  let Wrel : Set V := (fun z : V => (e.symm z).val) ⁻¹' Aᶜ
  have hWrel : IsOpen Wrel := hA.isOpen_compl.preimage
    (continuous_subtype_val.comp e.symm.continuous)
  obtain ⟨W,hW,hWpre⟩ := isOpen_induced_iff.mp hWrel
  have hpW : (0 : Plane) ∈ W := by
    have hpe : (e ⟨p,hpU⟩).val ∈ W := by
      change e ⟨p,hpU⟩ ∈ Subtype.val ⁻¹' W
      rw [hWpre]
      change (e.symm (e ⟨p,hpU⟩)).val ∉ A
      simpa only [e.symm_apply_apply] using hpA
    rwa [hpPlane] at hpe
  obtain ⟨s,hs,hsδ,hsmall⟩ := Plane.exists_openSquare_subset hW hpW hδ
  let ε : ℝ := s/2
  have hε : 0 < ε := half_pos hs
  have hεs : ε < s := by dsimp [ε]; linarith
  have hεδ : ε < δ := hεs.trans_le hsδ
  have hε1 : ε < 1 := hεδ.trans hδ1
  have hmargin (z : S) (hz : z ∈ crossings M anchor b) (hne : z ≠ p) (hzU : z ∈ U) :
      ε < |(e ⟨z,hzU⟩).val 0| := hεδ.trans (hmarginδ z hz hne hzU)
  have hclear (z : U) (hz : z.val ∈ A) :
      ε ≤ |(e z).val 0| ∨ ε ≤ |(e z).val 1| := by
    by_contra hne
    have hh : |(e z).val 0| < ε ∧ |(e z).val 1| < ε := by
      simpa only [not_or,not_le] using hne
    have heW : (e z).val ∈ W := hsmall (by
      change Plane.supDist (e z).val 0 < s
      rw [Plane.supDist,sub_zero]
      change max |(e z).val 0| |(e z).val 1| < s
      exact max_lt (hh.1.trans hεs) (hh.2.trans hεs))
    have heWrel : e z ∈ Wrel := by
      rw [← hWpre]
      exact heW
    change (e.symm (e z)).val ∉ A at heWrel
    rw [e.symm_apply_apply] at heWrel
    exact heWrel hz
  let coord : S → ℝ := fun z => if hz : z ∈ U then (e ⟨z,hz⟩).val 0 / ε else 2
  obtain ⟨a₀,ha₀,haX⟩ := (Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).exists_notMem_finite
    (hX.image coord)
  let a : Amount := ⟨a₀,abs_lt.mpr ha₀⟩
  let H := scaledPlaneSlide ε hε a
  obtain ⟨K,G,hcoord,hGU,hout⟩ := position_surface_chart_lift S U V hU e
    (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1) hCV H
    (scaledPlaneSlide_fixed_outside_unit ε hε hε1.le a)
  have hmarks : ∀ t z, z ∈ M.cover.branch → G.map (t,z) = z := by
    intro t z hz
    exact hout t z (fun hzU => Set.disjoint_left.mp hm hzU hz)
  have hmem (t : Interval) (z : S) : G.map (t,z) ∈ anchor.val.image ↔ z ∈ anchor.val.image := by
    by_cases hz : z ∈ U
    · rw [hGU t ⟨z,hz⟩,haxis (K.map (t,⟨z,hz⟩))]
      change _ ↔ (⟨z,hz⟩ : U).val ∈ anchor.val.image
      rw [haxis ⟨z,hz⟩,hcoord]
      rw [scaledPlaneSlide_second]
    · rw [hout t z hz]
  have hanchor : ∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image := by
    intro t
    ext z
    constructor
    · rintro ⟨q,hq,rfl⟩; exact (hmem t q).mpr hq
    · intro hz
      obtain ⟨g,hg⟩ := G.homeomorphism_at t
      refine ⟨g.symm z,?_,?_⟩
      · apply (hmem t (g.symm z)).mp
        rw [← hg,g.apply_symm_apply]
        exact hz
      · change G.map (t,g.symm z) = z
        rw [← hg,g.apply_symm_apply]
  refine ⟨G,hmarks,hanchor,?_,?_,?_⟩
  · intro q hq hne t
    by_cases hqU : q ∈ U
    · have hK : K.map (t,⟨q,hqU⟩) = ⟨q,hqU⟩ := by
        apply e.injective
        apply Subtype.ext
        rw [hcoord]
        exact scaledPlaneSlide_fixed ε hε a t _
          (Or.inl (hmargin q hq hne hqU).le)
      rw [hGU t ⟨q,hqU⟩,hK]
    · exact hout t q hqU
  · intro τ z hz
    by_cases hzU : z ∈ U
    · have hK : K.map (τ,⟨z,hzU⟩) = ⟨z,hzU⟩ := by
        apply e.injective
        apply Subtype.ext
        rw [hcoord]
        exact scaledPlaneSlide_fixed ε hε a τ _ (hclear ⟨z,hzU⟩ hz)
      rw [hGU τ ⟨z,hzU⟩,hK]
    · exact hout τ z hzU
  · intro hnew
    have hnewU : G.finalMap p ∈ U := by
      change G.map (1,p) ∈ U
      rw [hGU (1 : Interval) ⟨p,hpU⟩]
      exact (K.map (1,⟨p,hpU⟩)).property
    have hKfinal : (K.map (1,⟨p,hpU⟩)) = ⟨G.finalMap p,hnewU⟩ := by
      apply Subtype.ext
      exact (hGU (1 : Interval) ⟨p,hpU⟩).symm
    have hc := hcoord (1 : Interval) ⟨p,hpU⟩
    rw [hKfinal,hpPlane,scaledPlaneSlide_origin] at hc
    have hc0 := congrArg (fun z : Plane => z 0) hc
    have hco : coord (G.finalMap p) = a₀ := by
      dsimp [coord]
      rw [dite_eq_left hnewU]
      change (e ⟨G.finalMap p,hnewU⟩).val 0 / ε = a₀
      change (e ⟨G.finalMap p,hnewU⟩).val 0 = ε*1*a.val at hc0
      rw [hc0]
      dsimp [a]
      field_simp
    exact haX ⟨G.finalMap p,hnew,hco⟩
private theorem actualRawRelativeSingleContactAvoidanceDescent
    (M : HyperellipticModel E S) (anchor b : EssentialMarkedArc M)
    (hf : (crossings M anchor b).Finite)
    (ht : ∀ z ∈ crossings M anchor b, CrossesInDisk M anchor b z)
    (A : Set S) (hA : IsClosed A)
    (hAb : Disjoint (arcInterior M b) A)
    (X : Set S) (hX : X.Finite)
    (hnot : ¬ Disjoint X (crossings M anchor b)) :
    ∃ c : EssentialMarkedArc M,
      vertex M c = vertex M b ∧ (crossings M anchor c).Finite ∧
      Disjoint (arcInterior M c) A ∧
      (∀ z ∈ crossings M anchor c, CrossesInDisk M anchor c z) ∧
      (crossings M anchor c).ncard = (crossings M anchor b).ncard ∧
      (X ∩ crossings M anchor c).ncard < (X ∩ crossings M anchor b).ncard := by
  classical
  obtain ⟨p,hpX,hp⟩ := Set.not_disjoint_iff.mp hnot
  have hpA : p ∉ A := fun hpA => Set.disjoint_left.mp hAb hp.2 hpA
  obtain ⟨G,hm,ha,hfix,hfixA,hnew⟩ :=
    actualRawRelativeSingleContactAvoidanceMove M anchor b hf ht A hA X hX p hp hpA
  let h := timeHomeomorph G 1
  have hmarks : ∀ z, z ∈ M.cover.branch → h z = z :=
    fun z hz => (timeHomeomorph_apply G 1 z).trans (hm 1 z hz)
  have hanchor : h '' anchor.val.image = anchor.val.image :=
    (congrArg (fun f : S → S => f '' anchor.val.image)
      (funext (timeHomeomorph_apply G 1))).trans (ha 1)
  let c := b.transport h hmarks
  have hcross : crossings M anchor c = h '' crossings M anchor b :=
    actual_crossings_transport_preserving_anchor_image anchor b h hmarks hanchor
  have hnew' : h p ∉ X := by
    change G.map (1,p) ∉ X at hnew
    simpa only [h,timeHomeomorph_apply] using hnew
  have hfixed (z : S) (hz : z ∈ crossings M anchor b) (hne : z ≠ p) : h z = z :=
    (timeHomeomorph_apply G 1 z).trans (hfix z hz hne 1)
  have hsub : X ∩ crossings M anchor c ⊆ X ∩ crossings M anchor b := by
    rintro z ⟨hzX,hzc⟩
    rw [hcross] at hzc
    obtain ⟨x,hxb,hxz⟩ := hzc
    have hne : x ≠ p := by intro he; subst x; exact hnew' (hxz.symm ▸ hzX)
    have hxz' : x=z := (hfixed x hxb hne).symm.trans hxz
    exact ⟨hzX,hxz' ▸ hxb⟩
  have hpnew : p ∉ crossings M anchor c := by
    intro hpc
    rw [hcross] at hpc
    obtain ⟨x,hxb,hxp⟩ := hpc
    by_cases he : x=p
    · subst x
      exact hnew' (hxp.symm ▸ hpX)
    · exact he ((hfixed x hxb he).symm.trans hxp)
  have hclass : vertex M b = vertex M c := by
    apply Quotient.sound
    refine ⟨G,hm,?_⟩
    change G.finalMap '' b.val.image = (b.val.transport h hmarks).image
    rw [MarkedArc.transport_image]
    congr 1
    funext z
    exact (timeHomeomorph_apply G 1 z).symm
  have hAc : Disjoint (arcInterior M c) A := by
    rw [arcInterior_transport]
    apply Set.disjoint_left.mpr
    rintro z ⟨y,hy,rfl⟩ hzA
    have hhy : h (h y) = h y :=
      (timeHomeomorph_apply G 1 (h y)).trans (hfixA 1 (h y) hzA)
    have heq : h y = y := h.injective hhy
    exact Set.disjoint_left.mp hAb hy (heq ▸ hzA)
  refine ⟨c,hclass.symm,?_,hAc,?_,?_,?_⟩
  · rw [hcross]; exact hf.image h
  · intro z hz
    rw [hcross] at hz
    obtain ⟨x,hx,rfl⟩ := hz
    exact actual_crossesInDisk_transport_preserving_anchor_image M anchor b h hmarks hanchor x (ht x hx)
  · rw [hcross]
    exact Set.ncard_image_of_injective _ h.injective
  · apply Set.ncard_lt_ncard _ (hX.subset inter_subset_left)
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hsub,?_⟩
    intro he
    have hpOld : p ∈ X ∩ crossings M anchor b := ⟨hpX,hp⟩
    exact hpnew (he.symm ▸ hpOld).2

private theorem actualRawRelativeFiniteAnchorContactClearance
    (M : HyperellipticModel E S) (anchor b : EssentialMarkedArc M)
    (hf : (crossings M anchor b).Finite)
    (ht : ∀ z ∈ crossings M anchor b, CrossesInDisk M anchor b z)
    (A : Set S) (hA : IsClosed A)
    (hAb : Disjoint (arcInterior M b) A)
    (X : Set S) (hX : X.Finite) :
    ∃ c : EssentialMarkedArc M,
      vertex M c = vertex M b ∧ (crossings M anchor c).Finite ∧
      Disjoint (arcInterior M c) A ∧
      (∀ z ∈ crossings M anchor c, CrossesInDisk M anchor c z) ∧
      (crossings M anchor c).ncard = (crossings M anchor b).ncard ∧
      Disjoint X (crossings M anchor c) := by
  classical
  have main : ∀ n : ℕ, ∀ b : EssentialMarkedArc M,
      (crossings M anchor b).Finite →
      Disjoint (arcInterior M b) A →
      (∀ z ∈ crossings M anchor b, CrossesInDisk M anchor b z) →
      (X ∩ crossings M anchor b).ncard = n →
      ∃ c : EssentialMarkedArc M,
        vertex M c = vertex M b ∧ (crossings M anchor c).Finite ∧
        Disjoint (arcInterior M c) A ∧
        (∀ z ∈ crossings M anchor c, CrossesInDisk M anchor c z) ∧
        (crossings M anchor c).ncard = (crossings M anchor b).ncard ∧
        Disjoint X (crossings M anchor c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hf hAb ht hn
      by_cases hd : Disjoint X (crossings M anchor b)
      · exact ⟨b,rfl,hf,hAb,ht,rfl,hd⟩
      · obtain ⟨c,hclass,hcf,hAc,hct,hcount,hlt⟩ :=
          actualRawRelativeSingleContactAvoidanceDescent M anchor b hf ht A hA hAb X hX hd
        obtain ⟨d,hdclass,hdf,hAd,hdt,hdcount,hdis⟩ :=
          ih (X ∩ crossings M anchor c).ncard (hlt.trans_eq hn) c hcf hAc hct rfl
        exact ⟨d,hdclass.trans hclass,hdf,hAd,hdt,hdcount.trans hcount,hdis⟩
  exact main (X ∩ crossings M anchor b).ncard b hf hAb ht rfl

private theorem actualFiniteRawCompatibleFamilyDistinctContactRefinement
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    {ι : Type} [Fintype ι] (R : ι → ι → Prop)
    (hR : ∀ v w, R v w → R w v)
    (r : ι → EssentialMarkedArc M)
    (hf : ∀ v, (crossings M anchor (r v)).Finite)
    (ht : ∀ v p, p ∈ crossings M anchor (r v) → CrossesInDisk M anchor (r v) p)
    (hd : ∀ v w, v ≠ w → R v w → Disjoint (arcInterior M (r v)) (arcInterior M (r w))) :
    ∃ q : ι → EssentialMarkedArc M,
      (∀ v, vertex M (q v) = vertex M (r v)) ∧
      (∀ v, (crossings M anchor (q v)).Finite) ∧
      (∀ v p, p ∈ crossings M anchor (q v) → CrossesInDisk M anchor (q v) p) ∧
      (∀ v, (crossings M anchor (q v)).ncard = (crossings M anchor (r v)).ncard) ∧
      (∀ v w, v ≠ w → R v w → Disjoint (arcInterior M (q v)) (arcInterior M (q w))) ∧
      ∀ v w, v ≠ w → Disjoint (crossings M anchor (q v)) (crossings M anchor (q w)) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  have main : ∀ D : Finset ι,
      ∃ q : ι → EssentialMarkedArc M,
        (∀ v, vertex M (q v) = vertex M (r v)) ∧
        (∀ v, (crossings M anchor (q v)).Finite) ∧
        (∀ v p, p ∈ crossings M anchor (q v) → CrossesInDisk M anchor (q v) p) ∧
        (∀ v, (crossings M anchor (q v)).ncard = (crossings M anchor (r v)).ncard) ∧
        (∀ v w, v ≠ w → R v w → Disjoint (arcInterior M (q v)) (arcInterior M (q w))) ∧
        ∀ v ∈ D, ∀ w ∈ D, v ≠ w →
          Disjoint (crossings M anchor (q v)) (crossings M anchor (q w)) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      exact ⟨r,fun _ => rfl,hf,ht,fun _ => rfl,hd,by simp⟩
    | @insert v D hv ih =>
      obtain ⟨q,hq,hqf,hqt,hqn,hqd,hqcontacts⟩ := ih
      let X : Set S := ⋃ w : {w // w ∈ D}, crossings M anchor (q w.val)
      have hX : X.Finite := finite_iUnion (fun w => hqf w.val)
      let A : Set S := ⋃ w : {w // w ≠ v ∧ R v w}, (q w.val).val.image
      have hAc : IsClosed A := (isCompact_iUnion (fun w : {w // w ≠ v ∧ R v w} =>
        isCompact_range (q w.val).val.continuous)).isClosed
      have hqA : Disjoint (arcInterior M (q v)) A := by
        apply Set.disjoint_left.mpr
        intro z hz hzA
        obtain ⟨w,hw⟩ := mem_iUnion.mp hzA
        have hz' : z ∈ arcInterior M (q w.val) := ⟨hw,hz.2⟩
        exact Set.disjoint_left.mp (hqd v w.val w.property.1.symm w.property.2) hz hz'
      obtain ⟨b,hb,hbf,hbA,hbt,hbn,hbX⟩ := actualRawRelativeFiniteAnchorContactClearance M
        anchor (q v) (hqf v) (hqt v) A hAc hqA X hX
      let out : ι → EssentialMarkedArc M := fun w => if w = v then b else q w
      have hselected : out v = b := by simp [out]
      have hsame (w : ι) (hw : w ≠ v) : out w = q w := by simp [out,hw]
      have hnewPair (w : ι) (hw : w ≠ v) (hrw : R v w) :
          Disjoint (arcInterior M b) (arcInterior M (q w)) :=
        hbA.mono subset_rfl (fun z hz => mem_iUnion.mpr ⟨⟨w,hw,hrw⟩,hz.1⟩)
      refine ⟨out,?_,?_,?_,?_,?_,?_⟩
      · intro w
        by_cases hw : w=v
        · subst w; rw [hselected,hb,hq]
        · rw [hsame w hw]; exact hq w
      · intro w
        by_cases hw : w=v
        · subst w; rw [hselected]; exact hbf
        · rw [hsame w hw]; exact hqf w
      · intro w z hz
        by_cases hw : w=v
        · subst w; rw [hselected] at hz ⊢; exact hbt z hz
        · rw [hsame w hw] at hz ⊢; exact hqt w z hz
      · intro w
        by_cases hw : w=v
        · subst w; rw [hselected,hbn,hqn]
        · rw [hsame w hw,hqn]
      · intro w z hwz hrwz
        by_cases hw : w=v
        · subst w
          have hz : z ≠ v := hwz.symm
          rw [hselected,hsame z hz]
          exact hnewPair z hz hrwz
        · by_cases hz : z=v
          · subst z
            rw [hsame w hw,hselected]
            exact (hnewPair w hw (hR w v hrwz)).symm
          · rw [hsame w hw,hsame z hz]
            exact hqd w z hwz hrwz
      · intro w hw z hz hwz
        by_cases hew : w=v
        · subst w
          have hez : z ≠ v := hwz.symm
          have hzD : z ∈ D := (Finset.mem_insert.mp hz).resolve_left hez
          rw [hselected,hsame z hez]
          exact hbX.symm.mono subset_rfl
            (fun p hp => mem_iUnion.mpr ⟨⟨z,hzD⟩,hp⟩)
        · have hwD : w ∈ D := (Finset.mem_insert.mp hw).resolve_left hew
          by_cases hez : z=v
          · subst z
            rw [hsame w hew,hselected]
            exact hbX.mono (fun p hp => mem_iUnion.mpr ⟨⟨w,hwD⟩,hp⟩) subset_rfl
          · have hzD : z ∈ D := (Finset.mem_insert.mp hz).resolve_left hez
            rw [hsame w hew,hsame z hez]
            exact hqcontacts w hwD z hzD hwz
  obtain ⟨q,hq,hqf,hqt,hqn,hqd,hqc⟩ := main Finset.univ
  exact ⟨q,hq,hqf,hqt,hqn,hqd,fun v w hne => hqc v (Finset.mem_univ v) w (Finset.mem_univ w) hne⟩

noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

private theorem actualFinitePositionFromRawSimultaneousMinimum
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M))
    (r : {v // v ∈ F} → EssentialMarkedArc M)
    (hr : ∀ v, vertex M (r v) = v.val)
    (hf : ∀ v, (crossings M anchor (r v)).Finite)
    (ht : ∀ v p, p ∈ crossings M anchor (r v) → CrossesInDisk M anchor (r v) p)
    (hd : ∀ (v w : {v // v ∈ F}), v ≠ w → IsArcSimplex M {v.val,w.val} →
      Disjoint (arcInterior M (r v)) (arcInterior M (r w)))
    (hmin : ∀ v (b : EssentialMarkedArc M), vertex M b = v.val →
      (crossings M anchor b).Finite →
      (crossings M anchor (r v)).ncard ≤ (crossings M anchor b).ncard) :
    Nonempty (FinitePosition M anchor F) := by
  classical
  let R : {v // v ∈ F} → {v // v ∈ F} → Prop :=
    fun v w => IsArcSimplex M {v.val,w.val}
  have hRsymm : ∀ v w, R v w → R w v := by
    intro v w hw
    dsimp [R] at hw ⊢
    have he : ({v.val,w.val} : Finset (EssentialArcClass M)) = {w.val,v.val} := by
      ext a
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact or_comm
    rwa [← he]
  obtain ⟨q,hq,hqf,hqt,hqn,hqd,hqc⟩ :=
    actualFiniteRawCompatibleFamilyDistinctContactRefinement M anchor R hRsymm r hf ht hd
  exact ⟨{
    rep := q
    represents := fun v => (hq v).trans (hr v)
    simplex_disjoint := fun v w hne hp => hqd v w hne hp
    finite := hqf
    transverse := hqt
    distinct_crossings := hqc
    minimal := by
      intro v b hb hbf
      rw [hqn v]
      exact hmin v b hb hbf }⟩

end

noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- Source pp.4–5: simultaneous minimal position. This PRODUCES the certificate. -/
theorem finitePosition_exists (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M)) :
    Nonempty (FinitePosition M anchor F) := by
  obtain ⟨r,hr,hf,ht,hd,hmin⟩ := actual_raw_simultaneous_compatible_minimum_family M anchor F
  exact actualFinitePositionFromRawSimultaneousMinimum M anchor F r hr hf ht hd hmin

end CurveComplex.HyperellipticModel.ArcSurgery
