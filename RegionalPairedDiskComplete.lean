import RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualRegionalCompatibleReturn.RegionalOrdinaryDiskContactCleanup
import RegionalHalfDiskDescent
import CurveComplexGenusTwo.Topology.ActualRegionalCompatibleReturn.RegionalHalfDiskContactCleanup
import OriginalHalfDiskBoundarySideRelativeOpen
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.SubsetNullBoundaryDiskFilling
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ActualTwoSideDiskSubsetDescent
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts

open CurveComplex Set Topology RegionalTotalDecrease
open CoherentEndpointMotion.FreeBoundaryNullGeometry
open CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex.BranchedDoubleCover
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
universe v
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- PLAN C: produce an actual paired clean ordinary or half F disk; third traces may cross the disk. -/
theorem regional_F_null_boundary_has_paired_clean_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ a b : IntrinsicEssentialArc,
      (a.val.val 0 ≠ b.val.val 0 ∧ a.val.val 0 ≠ b.val.val 1 ∧
        a.val.val 1 ≠ b.val.val 0 ∧ a.val.val 1 ≠ b.val.val 1) →
      (range a.val.val ∩ range b.val.val).Finite →
      RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F a.val.val b.val.val →
      (Nonempty (NullBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val) ∨
        Nonempty (NullHalfBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val)) →
      Nonempty (PairedBigonDisk F {y | y.val ∈ frontier F} a.val.val b.val.val) ∨
        Nonempty (PairedHalfBigonDisk F {y | y.val ∈ boundaryCircle}
          {y | y.val ∈ frontier F} a.val.val b.val.val) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro a b hends hfinite hcross hnull
  let B : Set ↥F := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
  have hBfront : B ⊆ {y : ↥F | y.val ∈ frontier F} := by
    intro y hy
    rw [hfrontier]
    exact Or.inl hy
  have hproper : ∀ t ∈ Ioo (0 : Interval) 1,
      a.val.val t ∉ B ∧ b.val.val t ∉ B := by
    intro t ht
    exact ⟨fun h => a.val.property.2.2.2 t ht (hBfront h),
      fun h => b.val.property.2.2.2 t ht (hBfront h)⟩
  have hbdends : a.val.val 0 ∈ B ∧ a.val.val 1 ∈ B ∧
      b.val.val 0 ∈ B ∧ b.val.val 1 ∈ B :=
    ⟨a.val.property.2.1,a.val.property.2.2.1,b.val.property.2.1,b.val.property.2.2.1⟩
  have hdisends : Disjoint ({a.val.val 0,a.val.val 1} : Set ↥F)
      {b.val.val 0,b.val.val 1} := by
    simp only [Set.disjoint_insert_left,Set.disjoint_singleton_left,
      Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨⟨hends.1,hends.2.1⟩,hends.2.2⟩
  have hnormalize (a f : C(Interval,↥F)) (ha : IsEmbedding a) (hf : IsEmbedding f)
      (hfa : range f ⊆ range a) :
      ∃ u v : Interval, ∃ q : C(Interval,↥F), u ≠ v ∧ IsEmbedding q ∧
        (∀ t, q t = a (intervalAffine u v t)) ∧
        q 0 = f 0 ∧ q 1 = f 1 ∧ range q = range f := by
    obtain ⟨u,hu⟩ := hfa (mem_range_self 0)
    obtain ⟨v,hv⟩ := hfa (mem_range_self 1)
    have huv : u ≠ v := fun he => zero_ne_one (hf.injective (hu.symm.trans ((congrArg a he).trans hv)))
    let q : C(Interval,↥F) := ⟨fun t => a (intervalAffine u v t),by
      apply a.continuous.comp
      apply Continuous.subtype_mk
      fun_prop⟩
    have hq : IsEmbedding q := (q.continuous.isClosedEmbedding (by
      intro z w he
      have hh := congrArg Subtype.val (ha.injective he)
      change (1-z.val)*u.val+z.val*v.val = (1-w.val)*u.val+w.val*v.val at hh
      have hz : (z.val-w.val)*(v.val-u.val) = 0 := by nlinarith
      exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
        (sub_ne_zero.mpr (fun he => huv (Subtype.ext he.symm))))))).isEmbedding
    have hq0 : q 0 = f 0 := by simpa [q,intervalAffine] using hu
    have hq1 : q 1 = f 1 := by simpa [q,intervalAffine] using hv
    have hqa : range q ⊆ range a := by rintro _ ⟨t,rfl⟩; exact mem_range_self _
    have hqf : range q = range f := Set.Subset.antisymm
      (CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem a f q ha hq
        hfa hqa ⟨0,hq0.symm⟩ ⟨1,hq1.symm⟩)
      (CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem a q f ha hf
        hqa hfa ⟨0,hq0⟩ ⟨1,hq1⟩)
    exact ⟨u,v,q,huv,hq,(fun _ => rfl),hq0,hq1,hqf⟩
  have ordinaryRecord (f k : C(Interval,↥F))
      (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F))
      (hf : IsEmbedding f) (hk : IsEmbedding k) (he : IsEmbedding e)
      (hfa : range f ⊆ range a.val.val) (hkb : range k ⊆ range b.val.val)
      (h0 : f 0 = k 0) (h1 : f 1 = k 1)
      (hboundary' : e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range f ∪ range k)
      (hempty : Disjoint (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (range a.val.val ∪ range b.val.val)) :
      Nonempty (PairedBigonDisk F {y | y.val ∈ frontier F} a.val.val b.val.val) := by
    have hcorners (i : Interval) (hi : i = 0 ∨ i = 1) : (f i).val ∉ frontier F := by
      obtain ⟨s,hs⟩ := hfa (mem_range_self i)
      obtain ⟨t,ht⟩ := hkb (mem_range_self i)
      have hfk : f i = k i := hi.elim (fun he => he ▸ h0) (fun he => he ▸ h1)
      have hst : a.val.val s = b.val.val t := hs.trans (hfk.trans ht.symm)
      have hsI := (free_boundary_contact_parameters_interior B a.val.val b.val.val
        hbdends hproper hdisends s t hst).1
      exact hs ▸ a.val.property.2.2.2 s hsI
    have hsideclear (q : C(Interval,↥F)) (hq : IsEmbedding q)
        (a' : C(Interval,↥F)) (ha' : IsEmbedding a')
        (hqa' : range q ⊆ range a')
        (hap : ∀ t ∈ Ioo (0 : Interval) 1, (a' t).val ∉ frontier F)
        (hc0 : (q 0).val ∉ frontier F) (hc1 : (q 1).val ∉ frontier F) :
        ∀ t, (q t).val ∉ frontier F := by
      intro t
      obtain ⟨u,hu⟩ := hqa' (mem_range_self t)
      by_cases hu0 : u = 0
      · have ht := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
          a' q ha' hq hqa' t (Or.inl (hu.symm.trans (congrArg a' hu0)))
        exact ht.elim (fun he => he ▸ hc0) (fun he => he ▸ hc1)
      by_cases hu1 : u = 1
      · have ht := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
          a' q ha' hq hqa' t (Or.inr (hu.symm.trans (congrArg a' hu1)))
        exact ht.elim (fun he => he ▸ hc0) (fun he => he ▸ hc1)
      exact hu ▸ hap u ⟨lt_of_le_of_ne u.property.1 (Ne.symm hu0),
        lt_of_le_of_ne u.property.2 hu1⟩
    have hfclear := hsideclear f hf a.val.val a.val.property.1 hfa
      a.val.property.2.2.2 (hcorners 0 (Or.inl rfl)) (hcorners 1 (Or.inr rfl))
    have hkclear := hsideclear k hk b.val.val b.val.property.1 hkb
      b.val.property.2.2.2 (h0 ▸ hcorners 0 (Or.inl rfl)) (h1 ▸ hcorners 1 (Or.inr rfl))
    have hclassify (z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :
        z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∨
        e z ∈ range f ∪ range k := by
      by_cases hz : z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      · exact Or.inl hz
      · right
        have hzle : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
        have hznot : ¬ dist z.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 := hz
        have hzs : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
          le_antisymm hzle (not_lt.mp hznot)
        exact hboundary' ▸ (show e z ∈ e '' {z | z.val ∈ Metric.sphere
          (0 : EuclideanSpace ℝ (Fin 2)) 1} from ⟨z,hzs,rfl⟩)
    have heclear : ∀ y ∈ range e, y.val ∈ interior F := by
      rintro y ⟨z,rfl⟩
      apply RegionalEmbeddedFamily.mem_interior_of_mem_subtype_not_frontier
      rcases hclassify z with hz | ⟨t,ht⟩ | ⟨t,ht⟩
      · exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier S F e he z hz
      · exact ht ▸ hfclear t
      · exact ht ▸ hkclear t
    have hcontacts : range e ∩ (range a.val.val ∩ range b.val.val) = {f 0,f 1} := by
      exact regional_empty_two_side_disk_whole_contact_cleanup S g hg hS x R hR htarget
        F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        a b hends hfinite hcross f k e hf hk he hfa hkb h0 h1 hboundary' hempty
    have hwholeA : range e ∩ range a.val.val = range f := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨z,rfl⟩,hya⟩
        rcases hclassify z with hz | hyf | hyk
        · exact False.elim (Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inl hya))
        · exact hyf
        · have hh : e z ∈ ({f 0,f 1} : Set ↥F) := hcontacts ▸ ⟨mem_range_self z,hya,hkb hyk⟩
          rcases hh with hh | hh
          · exact ⟨0,hh.symm⟩
          · exact ⟨1,hh.symm⟩
      · intro y hy
        exact ⟨Set.image_subset_range _ _ (hboundary'.symm ▸ (show y ∈ range f ∪ range k from Or.inl hy)),hfa hy⟩
    have hwholeB : range e ∩ range b.val.val = range k := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨z,rfl⟩,hyb⟩
        rcases hclassify z with hz | hyf | hyk
        · exact False.elim (Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inr hyb))
        · have hh : e z ∈ ({f 0,f 1} : Set ↥F) := hcontacts ▸ ⟨mem_range_self z,hfa hyf,hyb⟩
          rcases hh with hh | hh
          · exact ⟨0,h0.symm.trans hh.symm⟩
          · exact ⟨1,h1.symm.trans hh.symm⟩
        · exact hyk
      · intro y hy
        exact ⟨Set.image_subset_range _ _ (hboundary'.symm ▸ (show y ∈ range f ∪ range k from Or.inr hy)),hkb hy⟩
    have hsides : range f ∩ range k = {f 0,f 1} := by
      apply Set.Subset.antisymm
      · intro y hy
        rw [← hcontacts]
        exact ⟨Set.image_subset_range _ _ (hboundary'.symm ▸ (show y ∈ range f ∪ range k from Or.inl hy.1)),hfa hy.1,hkb hy.2⟩
      · rintro y (rfl | rfl)
        · exact ⟨mem_range_self 0,⟨0,h0.symm⟩⟩
        · exact ⟨mem_range_self 1,⟨1,h1.symm⟩⟩
    obtain ⟨u,v,q,huv,hq,hqa,hq0,hq1,hqf⟩ := hnormalize a.val.val f a.val.property.1 hf hfa
    obtain ⟨w,z,r,hwz,hr,hrb,hr0,hr1,hrk⟩ := hnormalize b.val.val k b.val.property.1 hk hkb
    exact ⟨{
      first := q, second := r, first_embedded := hq, second_embedded := hr
      aStart := u, aFinish := v, bStart := w, bFinish := z
      a_distinct := huv, b_distinct := hwz, first_eq := hqa, second_eq := hrb
      zero_eq := hq0.trans (h0.trans hr0.symm)
      one_eq := hq1.trans (h1.trans hr1.symm)
      corners_distinct := fun hh => zero_ne_one (hq.injective hh)
      corners_off_frontier := ⟨hq0 ▸ hcorners 0 (Or.inl rfl),hq1 ▸ hcorners 1 (Or.inr rfl)⟩
      sides_inter := by rw [hqf,hrk,hsides,hq0,hq1]
      disk := e, disk_embedded := he
      boundary_image := by rw [hqf,hrk]; exact hboundary'
      whole_first := by rw [hqf]; exact hwholeA
      whole_second := by rw [hrk]; exact hwholeB
      ambient_interior := heclear
      strict_interior_clear := fun z hz =>
        ⟨fun ha => Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inl ha),
         fun hb => Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inr hb)⟩ }⟩
  rcases hnull with hnull | hnull
  · obtain ⟨N⟩ := hnull
    obtain ⟨d,hd,hbd⟩ := CoherentEndpointMotion.subset_nullhomotopic_curve_bounds_literal_disk
      S g hg hS F N.loop N.loop_null
    have hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range N.first ∪ range N.second := hbd.trans N.loop_image
    have hBfree : Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y hy ⟨z,hz,rfl⟩
      exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier S F d hd z hz (hBfront hy)
    obtain ⟨f,k,e,hf,hk,he,hfa,hkb,h0,h1,hboundary',hesub,hempty⟩ :=
      CoherentEndpointMotion.actual_two_side_disk_in_subset_has_empty_subdisk F B
        a.val.val b.val.val a.val.property.1 b.val.property.1
        ⟨a.val.property.2.1,a.val.property.2.2.1⟩
        ⟨b.val.property.2.1,b.val.property.2.2.1⟩ hfinite
        N.first N.second N.first_embedded N.second_embedded N.first_on_a N.second_on_b
        N.zero_eq N.one_eq d hd hboundary hBfree
    exact Or.inl (ordinaryRecord f k e hf hk he hfa hkb h0 h1 hboundary' hempty)
  · obtain ⟨N⟩ := hnull
    obtain ⟨d,hd,hbd⟩ := CoherentEndpointMotion.subset_nullhomotopic_curve_bounds_literal_disk
      S g hg hS F N.loop N.loop_null
    have hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range N.first ∪ range N.second ∪ range N.boundarySide := hbd.trans N.loop_image
    rcases regional_actual_interval_half_disk_has_empty_subdisk S g hg hS x R hR htarget
      F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
      a b hends hfinite hcross N d hd hboundary with hOrd | hHalf
    · obtain ⟨M,e,he,hbe,hesub,hempty⟩ := hOrd
      exact Or.inl (ordinaryRecord M.first M.second e M.first_embedded M.second_embedded
        he M.first_on_a M.second_on_b M.zero_eq M.one_eq hbe hempty)
    obtain ⟨N,d,hd,hboundary,hdsub,hempty⟩ := hHalf
    have hClean : range d ∩ (range a.val.val ∩ range b.val.val) = {N.first 1} :=
      regional_empty_three_side_half_disk_whole_contact_cleanup S g hg hS x R hR htarget
        F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        a b hends hfinite hcross N d hd hboundary hempty
    have hfrontierFree : ∀ z, z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        (d z).val ∉ frontier F :=
      RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier S F d hd
    have hcontactFront {y : ↥F} (ha : y ∈ range a.val.val)
        (hb : y ∈ range b.val.val) : y.val ∉ frontier F := by
      obtain ⟨s,hs⟩ := ha
      obtain ⟨t,ht⟩ := hb
      have hsI := (free_boundary_contact_parameters_interior B a.val.val b.val.val
        hbdends hproper hdisends s t (hs.trans ht.symm)).1
      exact hs ▸ a.val.property.2.2.2 s hsI
    have hcornerFront : (N.first 1).val ∉ frontier F := hcontactFront
      (N.first_on_a (mem_range_self 1))
      (N.second_on_b ⟨1,N.corner_eq.symm⟩)
    have hsideFront (q : C(Interval,↥F)) (hq : IsEmbedding q)
        (a' : C(Interval,↥F)) (ha' : IsEmbedding a')
        (hqa : range q ⊆ range a')
        (hap : ∀ t ∈ Ioo (0 : Interval) 1, (a' t).val ∉ frontier F) :
        ∀ t ∈ Ioo (0 : Interval) 1, (q t).val ∉ frontier F := by
      intro t ht
      obtain ⟨u,hu⟩ := hqa (mem_range_self t)
      have hnot (he : u = 0 ∨ u = 1) : False := by
        have heq : q t = a' 0 ∨ q t = a' 1 :=
          he.elim (fun hh => Or.inl (hu.symm.trans (congrArg a' hh)))
            (fun hh => Or.inr (hu.symm.trans (congrArg a' hh)))
        have htend := CurveComplex.HyperellipticModel.actual_embedded_side_source_endpoint
          a' q ha' hq hqa t heq
        exact htend.elim (fun hh => ht.1.ne' hh) (fun hh => ht.2.ne hh)
      exact hu ▸ hap u ⟨lt_of_le_of_ne u.property.1 (fun hh => hnot (Or.inl hh.symm)),
        lt_of_le_of_ne u.property.2 (fun hh => hnot (Or.inr hh))⟩
    have hfirstFront := hsideFront N.first N.first_embedded a.val.val a.val.property.1
      N.first_on_a a.val.property.2.2.2
    have hsecondFront := hsideFront N.second N.second_embedded b.val.val b.val.property.1
      N.second_on_b b.val.property.2.2.2
    have hwholeFront : range d ∩ {y : ↥F | y.val ∈ frontier F} = range N.boundarySide := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨z,rfl⟩,hzFront⟩
        have hzn : ¬ z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
          fun hz => hfrontierFree z hz hzFront
        have hzle : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
        have hznot : ¬ dist z.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 := hzn
        have hzs : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
          le_antisymm hzle (not_lt.mp hznot)
        have hzb : d z ∈ range N.first ∪ range N.second ∪ range N.boundarySide :=
          hboundary ▸ (show d z ∈ d '' {z | z.val ∈ Metric.sphere
            (0 : EuclideanSpace ℝ (Fin 2)) 1} from ⟨z,hzs,rfl⟩)
        rcases hzb with (⟨t,ht⟩ | ⟨t,ht⟩) | hz
        · by_cases ht0 : t = 0
          · exact ⟨0,N.boundary_zero.trans ((congrArg N.first ht0).symm.trans ht)⟩
          by_cases ht1 : t = 1
          · exact False.elim (hcornerFront (by
              have hh : (N.first t).val ∈ frontier F := ht.symm ▸ hzFront
              simpa only [ht1] using hh))
          exact False.elim (hfirstFront t
            ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
            (ht.symm ▸ hzFront))
        · by_cases ht0 : t = 0
          · exact ⟨1,N.boundary_one.trans ((congrArg N.second ht0).symm.trans ht)⟩
          by_cases ht1 : t = 1
          · exact False.elim (hcornerFront (by
              have hh0 : (N.second t).val ∈ frontier F := ht.symm ▸ hzFront
              have hh : (N.second 1).val ∈ frontier F := by simpa only [ht1] using hh0
              exact N.corner_eq.symm ▸ hh))
          exact False.elim (hsecondFront t
            ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
            (ht.symm ▸ hzFront))
        · exact hz
      · rintro y ⟨t,rfl⟩
        refine ⟨Set.image_subset_range _ _ (hboundary.symm ▸
          (show N.boundarySide t ∈ range N.first ∪ range N.second ∪ range N.boundarySide
            from Or.inr (mem_range_self t))),hBfront (N.boundary_in_B t)⟩
    have hDiskB : range d ∩ B = range N.boundarySide := by
      apply Set.Subset.antisymm
      · intro y hy
        exact hwholeFront ▸ ⟨hy.1,hBfront hy.2⟩
      · rintro y ⟨t,rfl⟩
        exact ⟨(hwholeFront.symm ▸ (mem_range_self t : N.boundarySide t ∈ range N.boundarySide)).1,
          N.boundary_in_B t⟩
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let BQ : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    let j : C(↥F,↥Q) := ⟨Set.inclusion houtside, continuous_inclusion houtside⟩
    have hj : IsEmbedding j := IsEmbedding.inclusion houtside
    let L : Curve ↥Q := {map := j ∘ N.loop.map, embedded := hj.comp N.loop.embedded}
    have hLimage : L.image = j '' N.loop.image := by
      exact Set.range_comp j N.loop.map
    let M : NullHalfBigonBoundary BQ (j.comp a.val.val) (j.comp b.val.val) := {
      first := j.comp N.first, second := j.comp N.second
      boundarySide := j.comp N.boundarySide
      first_embedded := hj.comp N.first_embedded
      second_embedded := hj.comp N.second_embedded
      boundary_embedded := hj.comp N.boundary_embedded
      first_on_a := by
        simpa only [ContinuousMap.coe_comp,Set.range_comp] using Set.image_mono N.first_on_a
      second_on_b := by
        simpa only [ContinuousMap.coe_comp,Set.range_comp] using Set.image_mono N.second_on_b
      first_zero_boundary := N.first_zero_boundary
      second_zero_boundary := N.second_zero_boundary
      corner_eq := congrArg j N.corner_eq
      corner_off_boundary := N.corner_off_boundary
      first_interior := N.first_interior
      second_interior := N.second_interior
      boundary_in_B := N.boundary_in_B
      boundary_zero := congrArg j N.boundary_zero
      boundary_one := congrArg j N.boundary_one
      sides_inter := by
        change range (j ∘ N.first) ∩ range (j ∘ N.second) = {j (N.first 1)}
        rw [Set.range_comp,Set.range_comp,← Set.image_inter hj.injective,N.sides_inter]
        exact Set.image_singleton
      loop := L
      loop_image := by
        rw [hLimage,N.loop_image,Set.image_union,Set.image_union]
        simp only [ContinuousMap.coe_comp,Set.range_comp]
      loop_null := N.loop_null.comp_right j }
    let dQ := j.comp d
    have hboundaryQ : dQ '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range M.first ∪ range M.second ∪ range M.boundarySide := by
      change (j ∘ d) '' _ = _
      rw [Set.image_comp,hboundary,Set.image_union,Set.image_union]
      simp only [M,ContinuousMap.coe_comp,Set.range_comp]
    have hDiskBQ : range dQ ∩ BQ = range M.boundarySide := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨z,rfl⟩,hy⟩
        have hz : d z ∈ range N.boundarySide := hDiskB ▸ ⟨mem_range_self z,hy⟩
        obtain ⟨t,ht⟩ := hz
        exact ⟨t,congrArg j ht⟩
      · rintro y ⟨t,rfl⟩
        have ht : N.boundarySide t ∈ range d ∩ B := hDiskB.symm ▸ mem_range_self t
        obtain ⟨z,hz⟩ := ht.1
        exact ⟨⟨z,congrArg j hz⟩,ht.2⟩
    have hOpenQ := original_half_disk_boundary_side_relative_open S g hg hS x R hR htarget
      (j.comp a.val.val) (j.comp b.val.val) M dQ (hj.comp hd) hboundaryQ hDiskBQ
    have hBoundaryRelativeInterior : N.boundarySide '' Ioo (0 : Interval) 1 ⊆
        interior (range d : Set ↥F) := by
      have hp : j ⁻¹' interior (range dQ) ⊆ range d := by
        intro y hy
        obtain ⟨z,hz⟩ := interior_subset hy
        exact ⟨z,hj.injective hz⟩
      have hp' := interior_maximal hp (isOpen_interior.preimage j.continuous)
      rintro y ⟨t,ht,rfl⟩
      exact hp' (hOpenQ ⟨t,ht,rfl⟩)
    have hRangeClosure (f : C(Interval,↥F)) : Set.range f ⊆
        closure (f '' Ioo (0 : Interval) 1) := by
      rintro y ⟨u,rfl⟩
      apply image_closure_subset_closure_image f.continuous
      refine ⟨u,?_,rfl⟩
      rw [closure_Ioo (zero_ne_one : (0 : Interval) ≠ 1)]
      exact ⟨bot_le,le_top⟩
    have hInteriorContactClosure (f : C(Interval,↥F)) (A : Set ↥F)
        (hA : IsClosed A)
        (hMidA : ∀ u ∈ Ioo (0 : Interval) 1, f u ∈ Set.range d → f u ∈ A) :
        ∀ u : Interval, f u ∈ interior (Set.range d : Set ↥F) → f u ∈ A := by
      have hSub : f '' Ioo (0 : Interval) 1 ⊆ (interior (Set.range d : Set ↥F))ᶜ ∪ A := by
        rintro y ⟨u,hu,rfl⟩
        by_cases hi : f u ∈ interior (Set.range d : Set ↥F)
        · exact Or.inr (hMidA u hu (interior_subset hi))
        · exact Or.inl hi
      have hClosure := closure_minimal hSub (isOpen_interior.isClosed_compl.union hA)
      intro u hu
      rcases hClosure (hRangeClosure f (Set.mem_range_self u)) with hn | hA
      · exact (hn hu).elim
      · exact hA
    have hWholeDiskBoundary (y : ↥F) (hyD : y ∈ Set.range d)
        (hyAQ : y ∈ Set.range a.val.val ∪ Set.range b.val.val) :
        y ∈ Set.range N.first ∪ Set.range N.second ∪ Set.range N.boundarySide := by
      obtain ⟨z,rfl⟩ := hyD
      have hzSphere : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
        apply le_antisymm z.property
        apply le_of_not_gt
        intro hzBall
        exact Set.disjoint_left.mp hempty ⟨z,hzBall,rfl⟩ hyAQ
      exact hboundary ▸ ⟨z,hzSphere,rfl⟩
    have hDiskContactFirst (y : ↥F) (hyD : y ∈ Set.range d)
        (hya : y ∈ Set.range a.val.val) (hyq : y ∈ Set.range b.val.val) : y = N.first 1 := by
      exact Set.mem_singleton_iff.mp (hClean ▸ ⟨hyD,hya,hyq⟩)
    have hFirstMid (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1)
        (huD : a.val.val u ∈ Set.range d) : a.val.val u ∈ Set.range N.first := by
      rcases hWholeDiskBoundary (a.val.val u) huD (Or.inl (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
      · exact hFirst
      · exact ⟨1,(hDiskContactFirst _ huD (Set.mem_range_self u) (N.second_on_b hSecond)).symm⟩
      · obtain ⟨v,hv⟩ := hSide
        exact ((hproper u hu).1 (hv ▸ N.boundary_in_B v)).elim
    have hSecondMid (u : Interval) (hu : u ∈ Ioo (0 : Interval) 1)
        (huD : b.val.val u ∈ Set.range d) : b.val.val u ∈ Set.range N.second := by
      rcases hWholeDiskBoundary (b.val.val u) huD (Or.inr (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
      · exact ⟨1,N.corner_eq.symm.trans
          (hDiskContactFirst _ huD (N.first_on_a hFirst) (Set.mem_range_self u)).symm⟩
      · exact hSecond
      · obtain ⟨v,hv⟩ := hSide
        exact ((hproper u hu).2 (hv ▸ N.boundary_in_B v)).elim
    have hFirstClosure := hInteriorContactClosure a.val.val (Set.range N.first)
      (isCompact_range N.first.continuous).isClosed hFirstMid
    have hSecondClosure := hInteriorContactClosure b.val.val (Set.range N.second)
      (isCompact_range N.second.continuous).isClosed hSecondMid
    have hWholeFirstExact : Set.range d ∩ Set.range a.val.val = Set.range N.first := by
      apply Set.Subset.antisymm
      · rintro y ⟨hyD,⟨u,rfl⟩⟩
        rcases hWholeDiskBoundary (a.val.val u) hyD (Or.inl (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
        · exact hFirst
        · exact ⟨1,(hDiskContactFirst _ hyD (Set.mem_range_self u) (N.second_on_b hSecond)).symm⟩
        · obtain ⟨v,hv⟩ := hSide
          by_cases hv0 : v = 0
          · exact ⟨0,N.boundary_zero.symm.trans (hv0 ▸ hv)⟩
          by_cases hv1 : v = 1
          · have hSecond : a.val.val u ∈ Set.range N.second :=
              ⟨0,N.boundary_one.symm.trans (hv1 ▸ hv)⟩
            exact ⟨1,(hDiskContactFirst _ hyD (Set.mem_range_self u) (N.second_on_b hSecond)).symm⟩
          exact hFirstClosure u (hBoundaryRelativeInterior
            ⟨v,⟨bot_lt_iff_ne_bot.mpr hv0,lt_top_iff_ne_top.mpr hv1⟩,hv⟩)
      · intro y hy
        refine ⟨?_,N.first_on_a hy⟩
        apply Set.image_subset_range d {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        rw [hboundary]
        exact Or.inl (Or.inl hy)
    have hWholeSecondExact : Set.range d ∩ Set.range b.val.val = Set.range N.second := by
      apply Set.Subset.antisymm
      · rintro y ⟨hyD,⟨u,rfl⟩⟩
        rcases hWholeDiskBoundary (b.val.val u) hyD (Or.inr (Set.mem_range_self u)) with (hFirst | hSecond) | hSide
        · exact ⟨1,N.corner_eq.symm.trans
            (hDiskContactFirst _ hyD (N.first_on_a hFirst) (Set.mem_range_self u)).symm⟩
        · exact hSecond
        · obtain ⟨v,hv⟩ := hSide
          by_cases hv0 : v = 0
          · have hFirst : b.val.val u ∈ Set.range N.first :=
              ⟨0,N.boundary_zero.symm.trans (hv0 ▸ hv)⟩
            exact ⟨1,N.corner_eq.symm.trans
              (hDiskContactFirst _ hyD (N.first_on_a hFirst) (Set.mem_range_self u)).symm⟩
          by_cases hv1 : v = 1
          · exact ⟨0,N.boundary_one.symm.trans (hv1 ▸ hv)⟩
          exact hSecondClosure u (hBoundaryRelativeInterior
            ⟨v,⟨bot_lt_iff_ne_bot.mpr hv0,lt_top_iff_ne_top.mpr hv1⟩,hv⟩)
      · intro y hy
        refine ⟨?_,N.second_on_b hy⟩
        apply Set.image_subset_range d {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        rw [hboundary]
        exact Or.inl (Or.inr hy)
    obtain ⟨u,v,q,huv,hq,hqa,hq0,hq1,hqf⟩ := hnormalize a.val.val N.first
      a.val.property.1 N.first_embedded N.first_on_a
    obtain ⟨w,z,r,hwz,hr,hrb,hr0,hr1,hrk⟩ := hnormalize b.val.val N.second
      b.val.property.1 N.second_embedded N.second_on_b
    have hfirstSide : range N.first ∩ range N.boundarySide = {N.first 0} := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨t,rfl⟩,⟨v,hv⟩⟩
        have htB : N.first t ∈ B := hv ▸ N.boundary_in_B v
        by_cases ht0 : t = 0
        · simp only [ht0,Set.mem_singleton_iff]
        by_cases ht1 : t = 1
        · exact False.elim (N.corner_off_boundary (ht1 ▸ htB))
        exact False.elim (N.first_interior t
          ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ htB)
      · rintro y rfl
        exact ⟨mem_range_self 0,⟨0,N.boundary_zero⟩⟩
    have hsecondSide : range N.second ∩ range N.boundarySide = {N.second 0} := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨t,rfl⟩,⟨v,hv⟩⟩
        have htB : N.second t ∈ B := hv ▸ N.boundary_in_B v
        by_cases ht0 : t = 0
        · simp only [ht0,Set.mem_singleton_iff]
        by_cases ht1 : t = 1
        · exact False.elim (N.corner_off_boundary (N.corner_eq.symm ▸ (ht1 ▸ htB)))
        exact False.elim (N.second_interior t
          ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ htB)
      · rintro y rfl
        exact ⟨mem_range_self 0,⟨1,N.boundary_one⟩⟩
    apply Or.inr
    exact ⟨{
      first := q, second := r, boundarySide := N.boundarySide
      first_embedded := hq, second_embedded := hr, boundary_embedded := N.boundary_embedded
      aStart := u, aFinish := v, bStart := w, bFinish := z
      a_distinct := huv, b_distinct := hwz, first_eq := hqa, second_eq := hrb
      first_zero := hq0 ▸ N.first_zero_boundary
      second_zero := hr0 ▸ N.second_zero_boundary
      boundary_endpoints_distinct := by
        intro he
        apply zero_ne_one (N.boundary_embedded.injective ?_)
        exact N.boundary_zero.trans (hq0.symm.trans (he.trans (hr0.trans N.boundary_one.symm)))
      corner_eq := hq1.trans (N.corner_eq.trans hr1.symm)
      corner_off_frontier := hq1 ▸ hcornerFront
      first_interior := hsideFront q hq a.val.val a.val.property.1
        (hqf ▸ N.first_on_a) a.val.property.2.2.2
      second_interior := hsideFront r hr b.val.val b.val.property.1
        (hrk ▸ N.second_on_b) b.val.property.2.2.2
      boundary_in_B := N.boundary_in_B
      boundary_zero := N.boundary_zero.trans hq0.symm
      boundary_one := N.boundary_one.trans hr0.symm
      sides_inter := by rw [hqf,hrk,N.sides_inter,hq1]
      first_boundary_inter := by rw [hqf,hfirstSide,hq0]
      second_boundary_inter := by rw [hrk,hsecondSide,hr0]
      loop := N.loop
      loop_image := by rw [hqf,hrk]; exact N.loop_image
      disk := d, disk_embedded := hd
      boundary_image := by rw [hqf,hrk]; exact hboundary
      whole_first := by rw [hqf]; exact hWholeFirstExact
      whole_second := by rw [hrk]; exact hWholeSecondExact
      whole_frontier := hwholeFront
      strict_interior_clear := fun z hz =>
        ⟨fun ha => Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inl ha),
         fun hb => Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inr hb),hfrontierFree z hz⟩ }⟩
