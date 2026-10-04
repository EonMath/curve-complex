import RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ActualTwoSideDiskSubsetDescent
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EssentialArcDiskExclusion

open CurveComplex Set Topology RegionalTotalDecrease
open CoherentEndpointMotion.FreeBoundaryNullGeometry
universe v
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 8000000

/-- Exact hcap producer for an intrusive actual three-side B half disk:
an empty ordinary F cap or a three-side F half cap excluding an old vertex.
All boundary and nullhomotopy records refer to the same original whole arcs. -/
theorem regional_actual_interval_half_disk_intrusion_has_strict_cap
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
      ∀ (N : NullHalfBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val)
        (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)),
        IsEmbedding d →
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range N.first ∪ range N.second ∪ range N.boundarySide →
        (¬ Disjoint
          (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
          (range a.val.val ∪ range b.val.val)) →
        (∃ N' : NullBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val,
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              range N'.first ∪ range N'.second ∧
            range e ⊆ range d ∧
            Disjoint (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
              (range a.val.val ∪ range b.val.val)) ∨
        (∃ N' : NullHalfBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val,
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              range N'.first ∪ range N'.second ∪ range N'.boundarySide ∧
            range e ⊆ range d ∧ ∃ y ∈ ({N.first 0,N.second 0,N.first 1} : Set ↥F), y ∉ range e) := by
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    a b hend hfinite hcross N d hd hboundary hempty
  letI : ClosedSurface S := Classical.choice hS.2.1
  let B : Set ↥F := {y | y.val ∈ boundaryCircle}
  let U : Set ↥F := d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hBfront : ∀ y : ↥F, y ∈ B → y.val ∈ frontier F := by
    intro y hy
    rw [hfrontier]
    exact Or.inl hy
  have hBfree : Disjoint B U := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨z,hz,rfl⟩
    exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier
      S F d hd z hz (hBfront (d z) hy)
  have haB : a.val.val 0 ∈ B ∧ a.val.val 1 ∈ B :=
    ⟨a.val.property.2.1,a.val.property.2.2.1⟩
  have hbB : b.val.val 0 ∈ B ∧ b.val.val 1 ∈ B :=
    ⟨b.val.property.2.1,b.val.property.2.2.1⟩
  have haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a.val.val t ∉ B := by
    intro t ht h
    exact a.val.property.2.2.2 t ht (hBfront _ h)
  have hbInterior : ∀ t ∈ Ioo (0 : Interval) 1, b.val.val t ∉ B := by
    intro t ht h
    exact b.val.property.2.2.2 t ht (hBfront _ h)
  have ha0 : a.val.val 0 ∉ U := fun h => Set.disjoint_left.mp hBfree haB.1 h
  have ha1 : a.val.val 1 ∉ U := fun h => Set.disjoint_left.mp hBfree haB.2 h
  have hb0 : b.val.val 0 ∉ U := fun h => Set.disjoint_left.mp hBfree hbB.1 h
  have hb1 : b.val.val 1 ∉ U := fun h => Set.disjoint_left.mp hBfree hbB.2 h
  have hUf : Disjoint U (range N.first ∪ range N.second ∪ range N.boundarySide) := by
    rw [← hboundary]
    apply Set.disjoint_left.mpr
    rintro y ⟨u,hu,he⟩ ⟨v,hv,hvEq⟩
    have huv : u = v := hd.injective (he.trans hvEq.symm)
    subst v
    have hlu : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hev : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hin : ((range a.val.val ∪ range b.val.val) ∩ U).Nonempty := by
    by_contra h
    apply hempty
    apply Set.disjoint_right.mpr
    intro y hyArc hyU
    exact h ⟨y,hyArc,hyU⟩
  let lift (f : C(Interval,↥F)) : C(Interval,S) :=
    ⟨fun t => (f t).val,continuous_subtype_val.comp f.continuous⟩
  let ds : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have hcrosscut (f : C(Interval,↥F)) (hf : IsEmbedding f)
      (hf0 : f 0 ∉ U) (hf1 : f 1 ∉ U)
      (hfU : (range f ∩ U).Nonempty) :
      ∃ q : C(Interval,↥F), IsEmbedding q ∧ range q ⊆ range f ∧
        q 0 ∈ range N.first ∪ range N.second ∪ range N.boundarySide ∧
        q 1 ∈ range N.first ∪ range N.second ∪ range N.boundarySide ∧
        q '' Ioo (0 : Interval) 1 ⊆ U := by
    have hf0s : lift f 0 ∉ ds ''
        {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rintro ⟨z,hz,he⟩
      exact hf0 ⟨z,hz,Subtype.ext he⟩
    have hf1s : lift f 1 ∉ ds ''
        {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rintro ⟨z,hz,he⟩
      exact hf1 ⟨z,hz,Subtype.ext he⟩
    have hfUs : (range (lift f) ∩ (ds ''
        {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty := by
      obtain ⟨y,⟨t,ht⟩,⟨z,hz,hzEq⟩⟩ := hfU
      exact ⟨y.val,⟨t,congrArg Subtype.val ht⟩,z,hz,congrArg Subtype.val hzEq⟩
    obtain ⟨q,hq,hqf,hq0,hq1,hqi⟩ :=
      CurveComplex.LocalSurgery.raw_embedded_arc_entering_disk_has_crosscut
        (lift f) (IsEmbedding.subtypeVal.comp hf)
        ds (IsEmbedding.subtypeVal.comp hd) hf0s hf1s hfUs
    have hqF (t : Interval) : q t ∈ F := by
      obtain ⟨v,hv⟩ := hqf (Set.mem_range_self t)
      exact hv ▸ (f v).property
    let qF : C(Interval,↥F) := ⟨fun t => ⟨q t,hqF t⟩,q.continuous.subtype_mk _⟩
    have hqFemb : IsEmbedding qF :=
      (qF.continuous.isClosedEmbedding (by
        intro s t he
        exact hq.injective (congrArg Subtype.val he))).isEmbedding
    refine ⟨qF,hqFemb,?_,?_,?_,?_⟩
    · rintro y ⟨t,rfl⟩
      obtain ⟨v,hv⟩ := hqf (Set.mem_range_self t)
      exact ⟨v,Subtype.ext hv⟩
    · obtain ⟨z,hz,he⟩ := hq0
      exact hboundary ▸ (show qF 0 ∈ d ''
        {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        from ⟨z,hz,Subtype.ext he⟩)
    · obtain ⟨z,hz,he⟩ := hq1
      exact hboundary ▸ (show qF 1 ∈ d ''
        {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
        from ⟨z,hz,Subtype.ext he⟩)
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨z,hz,he⟩ := hqi (Set.mem_image_of_mem q ht)
      exact ⟨z,hz,Subtype.ext he⟩
  have hinEither : (range a.val.val ∩ U).Nonempty ∨ (range b.val.val ∩ U).Nonempty := by
    obtain ⟨y,hya | hyb,hyU⟩ := hin
    · exact Or.inl ⟨y,hya,hyU⟩
    · exact Or.inr ⟨y,hyb,hyU⟩
  have hcrosscutEndOffOwn
      (f p g w q : C(Interval,↥F)) (hf : IsEmbedding f) (hp : IsEmbedding p)
      (hpf : range p ⊆ range f) (hqf : range q ⊆ range f)
      (hp0 : p 0 ∈ range g ∪ range w) (hp1 : p 1 ∈ range g ∪ range w)
      (hfree : Disjoint U (range p ∪ range g ∪ range w))
      (hqi : q '' Ioo (0 : Interval) 1 ⊆ U)
      (e : Interval) (hqe : q e ∈ range p ∪ range g ∪ range w) :
      q e ∈ range g ∪ range w := by
    by_contra hnot
    have hfirst : q e ∈ range p := by
      rcases hqe with (h | h) | h
      · exact h
      · exact (hnot (Or.inl h)).elim
      · exact (hnot (Or.inr h)).elim
    obtain ⟨v,hv⟩ := hfirst
    have hv0 : v ≠ 0 := by
      intro h
      exact hnot ((congrArg p h).symm.trans hv ▸ hp0)
    have hv1 : v ≠ 1 := by
      intro h
      exact hnot ((congrArg p h).symm.trans hv ▸ hp1)
    have hvI : v ∈ Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne v.property.1 (Ne.symm hv0),lt_of_le_of_ne v.property.2 hv1⟩
    let qf : C(Interval,range f) :=
      ⟨fun t => ⟨q t,hqf (mem_range_self t)⟩,q.continuous.subtype_mk _⟩
    let V : Set Interval := qf ⁻¹' {y : range f | (y : ↥F) ∈ p '' Ioo (0 : Interval) 1}
    have hVo : IsOpen V :=
      (CurveComplex.LocalSurgery.embedded_interval_subarc_interior_isOpen f p hf hp hpf).preimage
        qf.continuous
    have heV : e ∈ V := ⟨v,hvI,hv⟩
    have hecl : e ∈ closure (Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      exact e.property
    obtain ⟨t,htV,htI⟩ := mem_closure_iff_nhds.mp hecl V (hVo.mem_nhds heV)
    have htU : q t ∈ U := hqi (mem_image_of_mem q htI)
    obtain ⟨u,hu,huEq⟩ := htV
    exact Set.disjoint_left.mp hfree htU (Or.inl (Or.inl ⟨u,huEq⟩))
  have hNoBoundaryCrosscut
      (f q : C(Interval,↥F)) (hf : IsEmbedding f) (hq : IsEmbedding q)
      (hfInterior : ∀ t ∈ Ioo (0 : Interval) 1, f t ∉ B)
      (hfEssential : ¬ ∃ w : C(Interval,↥F), IsEmbedding w ∧ (∀ t, w t ∈ B) ∧
        ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F), IsEmbedding e ∧
          e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} = range f ∪ range w)
      (hqf : range q ⊆ range f)
      (hq0 : q 0 ∈ range N.boundarySide) (hq1 : q 1 ∈ range N.boundarySide)
      (hqi : q '' Ioo (0 : Interval) 1 ⊆ U) : False := by
    have hqB (e : Interval) (he : q e ∈ range N.boundarySide) :
        q e = f 0 ∨ q e = f 1 := by
      have heB : q e ∈ B := by
        obtain ⟨t,ht⟩ := he
        exact ht ▸ N.boundary_in_B t
      obtain ⟨u,hu⟩ := hqf (mem_range_self e)
      by_cases hu0 : u = 0
      · exact Or.inl ((congrArg f hu0).symm.trans hu).symm
      by_cases hu1 : u = 1
      · exact Or.inr ((congrArg f hu1).symm.trans hu).symm
      exact (hfInterior u ⟨lt_of_le_of_ne u.property.1 (Ne.symm hu0),
        lt_of_le_of_ne u.property.2 hu1⟩ (hu.symm ▸ heB)).elim
    have hqDistinct : q 0 ≠ q 1 := fun he => zero_ne_one (hq.injective he)
    have hfEnds : f 0 ∈ range q ∧ f 1 ∈ range q := by
      rcases hqB 0 hq0 with h0 | h0 <;> rcases hqB 1 hq1 with h1 | h1
      · exact (hqDistinct (h0.trans h1.symm)).elim
      · exact ⟨⟨0,h0⟩,⟨1,h1⟩⟩
      · exact ⟨⟨1,h1⟩,⟨0,h0⟩⟩
      · exact (hqDistinct (h0.trans h1.symm)).elim
    have hfq : range f ⊆ range q :=
      CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem
        f q f hf hf hqf Set.Subset.rfl hfEnds.1 hfEnds.2
    have hwD : range N.boundarySide ⊆ range d := by
      intro y hy
      exact image_subset_range _ _ (hboundary.symm ▸
        (show y ∈ range N.first ∪ range N.second ∪ range N.boundarySide from Or.inr hy))
    have hqD : range q ⊆ range d := by
      rintro y ⟨t,rfl⟩
      by_cases ht0 : t = 0
      · exact hwD (ht0 ▸ hq0)
      by_cases ht1 : t = 1
      · exact hwD (ht1 ▸ hq1)
      exact image_subset_range _ _ (hqi (mem_image_of_mem q
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩))
    have hfBends : f 0 ∈ range N.boundarySide ∧ f 1 ∈ range N.boundarySide := by
      rcases hqB 0 hq0 with h0 | h0 <;> rcases hqB 1 hq1 with h1 | h1
      · exact (hqDistinct (h0.trans h1.symm)).elim
      · exact ⟨h0 ▸ hq0,h1 ▸ hq1⟩
      · exact ⟨h1 ▸ hq1,h0 ▸ hq0⟩
      · exact (hqDistinct (h0.trans h1.symm)).elim
    exact hfEssential (proper_arc_in_boundary_attached_disk_is_boundary_parallel
      B f hf hfInterior d hd (hfq.trans hqD) N.boundarySide N.boundary_embedded
      N.boundary_in_B hwD hfBends.1 hfBends.2)
  have hcutEither :
      (∃ q : C(Interval,↥F), IsEmbedding q ∧ range q ⊆ range a.val.val ∧
        q 0 ∈ range N.first ∪ range N.second ∪ range N.boundarySide ∧
        q 1 ∈ range N.first ∪ range N.second ∪ range N.boundarySide ∧
        q '' Ioo (0 : Interval) 1 ⊆ U) ∨
      (∃ q : C(Interval,↥F), IsEmbedding q ∧ range q ⊆ range b.val.val ∧
        q 0 ∈ range N.first ∪ range N.second ∪ range N.boundarySide ∧
        q 1 ∈ range N.first ∪ range N.second ∪ range N.boundarySide ∧
        q '' Ioo (0 : Interval) 1 ⊆ U) := by
    rcases hinEither with haU | hbU
    · exact Or.inl (hcrosscut a.val.val a.val.property.1 ha0 ha1 haU)
    · exact Or.inr (hcrosscut b.val.val b.val.property.1 hb0 hb1 hbU)
  have hcutClassified :
      (∃ q : C(Interval,↥F), IsEmbedding q ∧ range q ⊆ range a.val.val ∧
        q 0 ∈ range N.second ∪ range N.boundarySide ∧
        q 1 ∈ range N.second ∪ range N.boundarySide ∧
        q '' Ioo (0 : Interval) 1 ⊆ U ∧
        ¬ (q 0 ∈ range N.boundarySide ∧ q 1 ∈ range N.boundarySide)) ∨
      (∃ q : C(Interval,↥F), IsEmbedding q ∧ range q ⊆ range b.val.val ∧
        q 0 ∈ range N.first ∪ range N.boundarySide ∧
        q 1 ∈ range N.first ∪ range N.boundarySide ∧
        q '' Ioo (0 : Interval) 1 ⊆ U ∧
        ¬ (q 0 ∈ range N.boundarySide ∧ q 1 ∈ range N.boundarySide)) := by
    rcases hcutEither with ⟨q,hq,hqa,hq0,hq1,hqi⟩ | ⟨q,hq,hqb,hq0,hq1,hqi⟩
    · refine Or.inl ⟨q,hq,hqa,?_,?_,hqi,?_⟩
      · exact hcrosscutEndOffOwn a.val.val N.first N.second N.boundarySide q
          a.val.property.1 N.first_embedded N.first_on_a hqa
          (Or.inr ⟨0,N.boundary_zero⟩) (Or.inl ⟨1,N.corner_eq.symm⟩) hUf hqi 0 hq0
      · exact hcrosscutEndOffOwn a.val.val N.first N.second N.boundarySide q
          a.val.property.1 N.first_embedded N.first_on_a hqa
          (Or.inr ⟨0,N.boundary_zero⟩) (Or.inl ⟨1,N.corner_eq.symm⟩) hUf hqi 1 hq1
      · rintro ⟨h0,h1⟩
        exact hNoBoundaryCrosscut a.val.val q a.val.property.1 hq
          haInterior a.property hqa h0 h1 hqi
    · have hswap : range N.first ∪ range N.second ∪ range N.boundarySide =
          range N.second ∪ range N.first ∪ range N.boundarySide := by
        rw [union_comm (range N.first) (range N.second)]
      refine Or.inr ⟨q,hq,hqb,?_,?_,hqi,?_⟩
      · exact hcrosscutEndOffOwn b.val.val N.second N.first N.boundarySide q
          b.val.property.1 N.second_embedded N.second_on_b hqb
          (Or.inr ⟨1,N.boundary_one⟩) (Or.inl ⟨1,N.corner_eq⟩)
          (hswap ▸ hUf) hqi 0 (hswap ▸ hq0)
      · exact hcrosscutEndOffOwn b.val.val N.second N.first N.boundarySide q
          b.val.property.1 N.second_embedded N.second_on_b hqb
          (Or.inr ⟨1,N.boundary_one⟩) (Or.inl ⟨1,N.corner_eq⟩)
          (hswap ▸ hUf) hqi 1 (hswap ▸ hq1)
      · rintro ⟨h0,h1⟩
        exact hNoBoundaryCrosscut b.val.val q b.val.property.1 hq
          hbInterior b.property hqb h0 h1 hqi
  have hnull (c : Curve ↥F)
      (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F))
      (he : IsEmbedding e) (hc : c.image ⊆ range e) :
      (⟨c.map,c.embedded.continuous⟩ : C(Circle,↥F)).Nullhomotopic := by
    let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
    letI : ContractibleSpace D := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace
      ⟨0,by simp⟩
    let k : C(Circle,D) := ⟨fun z => he.toHomeomorph.symm ⟨c.map z,hc (mem_range_self z)⟩,
      he.toHomeomorph.symm.continuous.comp (c.embedded.continuous.subtype_mk _)⟩
    have hk : e.comp k = (⟨c.map,c.embedded.continuous⟩ : C(Circle,↥F)) := by
      apply ContinuousMap.ext
      intro z
      exact congrArg Subtype.val (he.toHomeomorph.apply_symm_apply ⟨c.map z,hc (mem_range_self z)⟩)
    rw [← hk]
    exact ((id_nullhomotopic D).comp_left k).comp_right e
  have hsubarc (f : C(Interval,↥F)) (hf : IsEmbedding f)
      (r s : Interval) (hrs : r ≠ s) :
      ∃ p : C(Interval,↥F), IsEmbedding p ∧ range p ⊆ range f ∧
        p 0 = f r ∧ p 1 = f s := by
    let affine : Interval → Interval := fun t =>
      ⟨(1-t.val)*r.val+t.val*s.val,by
        constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
          s.property.1,s.property.2]⟩
    let p : C(Interval,↥F) := ⟨f ∘ affine,f.continuous.comp (by fun_prop)⟩
    have hi : Function.Injective p := by
      intro t u he
      have hv := congrArg Subtype.val (hf.injective he)
      apply Subtype.ext
      have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
      dsimp [affine] at hv
      have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact sub_eq_zero.mp hz
      · exact False.elim (hne (sub_eq_zero.mp hz).symm)
    refine ⟨p,(p.continuous.isClosedEmbedding hi).isEmbedding,?_,?_,?_⟩
    · rintro y ⟨t,rfl⟩; exact mem_range_self (affine t)
    · simp [p,affine]
    · simp [p,affine]
  have hsubdisk (q p : C(Interval,↥F)) (hq : IsEmbedding q) (hp : IsEmbedding p)
      (h0 : q 0 = p 0) (h1 : q 1 = p 1)
      (hpb : range p ⊆ range N.first ∪ range N.second ∪ range N.boundarySide)
      (hqi : q '' Ioo (0 : Interval) 1 ⊆ U) :
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        IsEmbedding e ∧ e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range q ∪ range p ∧ range e ⊆ range d := by
    have hmeet (s t : Interval) (hst : q s = p t) :
        (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
      by_cases hs0 : s=0
      · exact Or.inl ⟨hs0,hp.injective (hst.symm.trans ((congrArg q hs0).trans h0))⟩
      by_cases hs1 : s=1
      · exact Or.inr ⟨hs1,hp.injective (hst.symm.trans ((congrArg q hs1).trans h1))⟩
      exact (Set.disjoint_left.mp hUf
        (hqi ⟨s,⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩,rfl⟩)
        (hst.symm ▸ hpb (mem_range_self t))).elim
    obtain ⟨c,hc⟩ := exists_curve_of_two_arcs q p hq.injective hp.injective h0 h1 hmeet
    have hpd : range p ⊆ range d := fun y hy => image_subset_range d _ (hboundary.symm ▸ hpb hy)
    have hqd : range q ⊆ range d := by
      rintro y ⟨t,rfl⟩
      by_cases ht0 : t=0
      · exact hpd ⟨0,(congrArg q ht0).trans h0 |>.symm⟩
      by_cases ht1 : t=1
      · exact hpd ⟨1,(congrArg q ht1).trans h1 |>.symm⟩
      exact image_subset_range d _ (hqi ⟨t,
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
    obtain ⟨e,he,heb,hed⟩ := LocalSurgery.curve_in_embedded_disk_bounds_subdisk c d hd
      (hc ▸ Set.union_subset hqd hpd)
    exact ⟨e,he,heb.trans hc,hed⟩
  have hdiskSides (p q : C(Interval,↥F)) (hp : IsEmbedding p) (hq : IsEmbedding q)
      (h0 : p 0 = q 0) (h1 : p 1 = q 1)
      (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)) (he : IsEmbedding e)
      (heb : e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} = range p ∪ range q) :
      range p ∩ range q = ({p 0,p 1} : Set ↥F) := by
    obtain ⟨P,hP,hPe,hPs⟩ := RegionalEmbeddedFamily.embedded_disk_boundary_arc_lift e he p hp
      (by change range p ⊆ e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}; rw [heb]; exact subset_union_left)
    obtain ⟨Q,hQ,hQe,hQs⟩ := RegionalEmbeddedFamily.embedded_disk_boundary_arc_lift e he q hq
      (by change range q ⊆ e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}; rw [heb]; exact subset_union_right)
    let u : C(Interval,EuclideanSpace ℝ (Fin 2)) :=
      ⟨fun t => (P t).val,continuous_subtype_val.comp P.continuous⟩
    let v : C(Interval,EuclideanSpace ℝ (Fin 2)) :=
      ⟨fun t => (Q t).val,continuous_subtype_val.comp Q.continuous⟩
    have huv0 : u 0 = v 0 := congrArg Subtype.val (he.injective ((hPe 0).trans (h0.trans (hQe 0).symm)))
    have huv1 : u 1 = v 1 := congrArg Subtype.val (he.injective ((hPe 1).trans (h1.trans (hQe 1).symm)))
    have hunion : range u ∪ range v = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      apply Subset.antisymm
      · rintro y (⟨t,rfl⟩ | ⟨t,rfl⟩)
        · exact hPs t
        · exact hQs t
      · intro y hy
        let z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨y,Metric.sphere_subset_closedBall hy⟩
        have hz : e z ∈ range p ∪ range q := heb ▸ (show e z ∈ e ''
          {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} from ⟨z,hy,rfl⟩)
        rcases hz with ⟨t,ht⟩ | ⟨t,ht⟩
        · exact Or.inl ⟨t,congrArg Subtype.val (he.injective ((hPe t).trans ht))⟩
        · exact Or.inr ⟨t,congrArg Subtype.val (he.injective ((hQe t).trans ht))⟩
    have hinter := Schoenflies.two_arcs_inter_of_union RegionalEmbeddedFamily.unit_sphere_isJordanCurve
      (RegionalEmbeddedFamily.planar_embedded_path_isArcBetween u (IsEmbedding.subtypeVal.comp hP))
      (show Schoenflies.IsArcBetween (range v) (u 0) (u 1) from by
        rw [huv0,huv1]
        exact RegionalEmbeddedFamily.planar_embedded_path_isArcBetween v (IsEmbedding.subtypeVal.comp hQ))
      hunion
    apply Subset.antisymm
    · rintro y ⟨⟨s,rfl⟩,⟨t,ht⟩⟩
      have hpq : P s = Q t := he.injective ((hPe s).trans (ht.symm.trans (hQe t).symm))
      have hu : u s ∈ range u ∩ range v := ⟨mem_range_self s,⟨t,(congrArg Subtype.val hpq).symm⟩⟩
      have hz : u s ∈ ({u 0,u 1} : Set (EuclideanSpace ℝ (Fin 2))) := hinter ▸ hu
      rcases hz with h | h
      · exact Or.inl ((hPe s).symm.trans ((congrArg e (Subtype.ext h)).trans (hPe 0)))
      · exact Or.inr ((hPe s).symm.trans ((congrArg e (Subtype.ext h)).trans (hPe 1)))
    · rintro y (rfl | rfl)
      · exact ⟨mem_range_self 0,⟨0,h0.symm⟩⟩
      · exact ⟨mem_range_self 1,⟨1,h1.symm⟩⟩
  let Ordinary (f g : C(Interval,↥F)) : Prop :=
    ∃ N' : NullBigonBoundary B f g,
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        IsEmbedding e ∧ e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range N'.first ∪ range N'.second ∧ range e ⊆ range d ∧
        Disjoint (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
          (range f ∪ range g)
  let Half (f g : C(Interval,↥F)) (y : ↥F) : Prop :=
    ∃ N' : NullHalfBigonBoundary B f g,
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        IsEmbedding e ∧ e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range N'.first ∪ range N'.second ∪ range N'.boundarySide ∧ range e ⊆ range d ∧ y ∉ range e
  have hBfreeAny (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F))
      (he : IsEmbedding e) : Disjoint B
        (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨z,hz,rfl⟩
    exact RegionalEmbeddedFamily.embedded_regional_disk_interior_avoids_frontier S F e he z hz (hBfront _ hy)
  have hcontactOff : ∀ y ∈ range a.val.val ∩ range b.val.val, y ∉ B := by
    rintro y ⟨⟨r,hr⟩,⟨s,hs⟩⟩ hyB
    have haEnd : r=0 ∨ r=1 := by
      by_cases hr0 : r=0
      · exact Or.inl hr0
      by_cases hr1 : r=1
      · exact Or.inr hr1
      exact (haInterior r ⟨lt_of_le_of_ne r.property.1 (Ne.symm hr0),
        lt_of_le_of_ne r.property.2 hr1⟩ (hr.symm ▸ hyB)).elim
    have hbEnd : s=0 ∨ s=1 := by
      by_cases hs0 : s=0
      · exact Or.inl hs0
      by_cases hs1 : s=1
      · exact Or.inr hs1
      exact (hbInterior s ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),
        lt_of_le_of_ne s.property.2 hs1⟩ (hs.symm ▸ hyB)).elim
    have hab : a.val.val r = b.val.val s := hr.trans hs.symm
    rcases haEnd with rfl | rfl <;> rcases hbEnd with rfl | rfl
    · exact hend.1 hab
    · exact hend.2.1 hab
    · exact hend.2.2.1 hab
    · exact hend.2.2.2 hab
  have hclean (f g : C(Interval,↥F)) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hfB : f 0 ∈ B ∧ f 1 ∈ B) (hgB : g 0 ∈ B ∧ g 1 ∈ B)
      (hfin : (range f ∩ range g).Finite)
      (hoff : ∀ y ∈ range f ∩ range g, y ∉ B)
      (p q : C(Interval,↥F)) (hp : IsEmbedding p) (hq : IsEmbedding q)
      (hpf : range p ⊆ range f) (hqg : range q ⊆ range g)
      (h0 : p 0 = q 0) (h1 : p 1 = q 1)
      (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)) (he : IsEmbedding e)
      (heb : e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} = range p ∪ range q)
      (hed : range e ⊆ range d) : Ordinary f g := by
    obtain ⟨p',q',e',hp',hq',he',hpf',hqg',h0',h1',heb',hesub',hempty'⟩ :=
      CoherentEndpointMotion.actual_two_side_disk_in_subset_has_empty_subdisk F B f g hf hg
        hfB hgB hfin p q hp hq hpf hqg h0 h1 e he heb (hBfreeAny e he)
    have hinter := hdiskSides p' q' hp' hq' h0' h1' e' he' heb'
    have hmeet (s t : Interval) (hst : p' s = q' t) :
        (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
      have hx : p' s ∈ ({p' 0,p' 1} : Set ↥F) := hinter ▸ ⟨mem_range_self s,⟨t,hst.symm⟩⟩
      rcases hx with hx | hx
      · exact Or.inl ⟨hp'.injective hx,hq'.injective (hst.symm.trans (hx.trans h0'))⟩
      · exact Or.inr ⟨hp'.injective hx,hq'.injective (hst.symm.trans (hx.trans h1'))⟩
    obtain ⟨c,hc⟩ := exists_curve_of_two_arcs p' q' hp'.injective hq'.injective h0' h1' hmeet
    let N' : NullBigonBoundary B f g := {
      first := p', second := q', first_embedded := hp', second_embedded := hq'
      first_on_a := hpf', second_on_b := hqg', zero_eq := h0', one_eq := h1'
      corners_off_boundary := ⟨hoff _ ⟨hpf' (mem_range_self 0),hqg' ⟨0,h0'.symm⟩⟩,
        hoff _ ⟨hpf' (mem_range_self 1),hqg' ⟨1,h1'.symm⟩⟩⟩
      sides_inter := hinter, loop := c, loop_image := hc
      loop_null := hnull c e' he' (by rw [hc,← heb']; exact image_subset_range _ _) }
    exact ⟨N',e',he',heb',hesub'.trans hed,hempty'⟩
  have holdExcluded
      (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)) (he : IsEmbedding e)
      (hed : range e ⊆ range d) (y : ↥F)
      (hyold : y ∈ range N.first ∪ range N.second ∪ range N.boundarySide)
      (hynew : y ∉ e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
      y ∉ range e := by
    let E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
      ⟨fun z => (e z).val,continuous_subtype_val.comp e.continuous⟩
    have hE : IsEmbedding E := IsEmbedding.subtypeVal.comp he
    have hD : IsEmbedding ds := IsEmbedding.subtypeVal.comp hd
    have hED : range E ⊆ range ds := by
      rintro z ⟨t,rfl⟩
      obtain ⟨u,hu⟩ := hed (mem_range_self t)
      exact ⟨u,congrArg Subtype.val hu⟩
    have hopen : E '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
        ds '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [← LocalSurgery.embedded_surface_disk_interior_eq ds hD]
      exact (LocalSurgery.embedded_surface_disk_interior_isOpen E hE).subset_interior_iff.mpr
        ((image_subset_range _ _).trans hED)
    rintro ⟨z,hz⟩
    have hlt : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) < 1 := by
      apply lt_of_le_of_ne z.property
      intro heq
      exact hynew ⟨z,heq,hz⟩
    obtain ⟨u,hu,huEq⟩ := hopen ⟨z,hlt,congrArg Subtype.val hz⟩
    exact Set.disjoint_left.mp hUf ⟨u,hu,Subtype.ext huEq⟩ hyold
  have hcapOfCut (f g : C(Interval,↥F)) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hfB : f 0 ∈ B ∧ f 1 ∈ B) (hgB : g 0 ∈ B ∧ g 1 ∈ B)
      (hfin : (range f ∩ range g).Finite) (hoff : ∀ y ∈ range f ∩ range g, y ∉ B)
      (M : NullHalfBigonBoundary B f g)
      (hMb : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range M.first ∪ range M.second ∪ range M.boundarySide)
      (q : C(Interval,↥F)) (hq : IsEmbedding q) (hqf : range q ⊆ range f)
      (hq0 : q 0 ∈ range M.second ∪ range M.boundarySide)
      (hq1 : q 1 ∈ range M.second ∪ range M.boundarySide)
      (hqi : q '' Ioo (0 : Interval) 1 ⊆ U)
      (hnotBB : ¬ (q 0 ∈ range M.boundarySide ∧ q 1 ∈ range M.boundarySide)) :
      Ordinary f g ∨ ∃ y ∈ ({M.first 0,M.second 0,M.first 1} : Set ↥F), Half f g y := by
    have hMsub : range M.first ∪ range M.second ∪ range M.boundarySide ⊆
        range N.first ∪ range N.second ∪ range N.boundarySide := by rw [← hMb,← hboundary]
    have hord (hq0p : q 0 ∈ range M.second) (hq1p : q 1 ∈ range M.second) : Ordinary f g := by
      obtain ⟨r,hr⟩ := hq0p
      obtain ⟨s,hs⟩ := hq1p
      have hrs : r ≠ s := fun h => zero_ne_one (hq.injective (hr.symm.trans ((congrArg M.second h).trans hs)))
      obtain ⟨p,hp,hpp,hp0,hp1⟩ := hsubarc M.second M.second_embedded r s hrs
      have hp0q : p 0 = q 0 := hp0.trans hr
      have hp1q : p 1 = q 1 := hp1.trans hs
      obtain ⟨e,he,heb,hed⟩ := hsubdisk q p hq hp hp0q.symm hp1q.symm
        (fun y hy => hMsub (Or.inl (Or.inr (hpp hy)))) hqi
      exact hclean f g hf hg hfB hgB hfin hoff q p hq hp hqf (hpp.trans M.second_on_b)
        hp0q.symm hp1q.symm e he heb hed
    have hmixed (q : C(Interval,↥F)) (hq : IsEmbedding q) (hqf : range q ⊆ range f)
        (hq0w : q 0 ∈ range M.boundarySide) (hq1p : q 1 ∈ range M.second)
        (hqi : q '' Ioo (0 : Interval) 1 ⊆ U) :
        ∃ y ∈ ({M.first 0,M.second 0,M.first 1} : Set ↥F), Half f g y := by
      obtain ⟨u,hu⟩ := hq0w
      obtain ⟨r,hr⟩ := hq1p
      have hq0B : q 0 ∈ B := hu ▸ M.boundary_in_B u
      have hq1notB : q 1 ∉ B := hoff _ ⟨hqf (mem_range_self 1),M.second_on_b ⟨r,hr⟩⟩
      have hr0 : r ≠ 0 := by
        intro he
        exact hq1notB (hr ▸ (he ▸ M.second_zero_boundary))
      have hu1 : u ≠ 1 := by
        intro he
        have hq0g : q 0 ∈ range g := M.second_on_b ⟨0,
          M.boundary_one.symm.trans ((congrArg M.boundarySide he).symm.trans hu)⟩
        exact hoff _ ⟨hqf (mem_range_self 0),hq0g⟩ hq0B
      obtain ⟨p,hp,hpp,hp0,hp1⟩ := hsubarc M.second M.second_embedded 0 r (Ne.symm hr0)
      obtain ⟨w,hw,hww,hw0,hw1⟩ := hsubarc M.boundarySide M.boundary_embedded u 1 hu1
      have hp1q : p 1 = q 1 := hp1.trans hr
      have hw0q : w 0 = q 0 := hw0.trans hu
      have hw1p : w 1 = p 0 := hw1.trans (M.boundary_one.trans hp0.symm)
      have hwB (t : Interval) : w t ∈ B := by
        obtain ⟨v,hv⟩ := hww (mem_range_self t)
        exact hv ▸ M.boundary_in_B v
      have hpBOnly (t : Interval) (ht : p t ∈ B) : t=0 := by
        obtain ⟨s,hs⟩ := hpp (mem_range_self t)
        have hs0 : s=0 := by
          by_contra hn
          by_cases hs1 : s=1
          · exact M.corner_off_boundary (M.corner_eq.symm ▸ (hs1 ▸ (hs.symm ▸ ht)))
          exact M.second_interior s
            ⟨lt_of_le_of_ne s.property.1 (Ne.symm hn),lt_of_le_of_ne s.property.2 hs1⟩ (hs.symm ▸ ht)
        exact hp.injective (hs.symm.trans ((congrArg M.second hs0).trans hp0.symm))
      have hpI : ∀ t ∈ Ioo (0 : Interval) 1, p t ∉ B := by
        intro t ht htB
        exact (ne_of_gt ht.1) (hpBOnly t htB)
      have hwp : range w ∩ range p = ({p 0} : Set ↥F) := by
        apply Subset.antisymm
        · rintro y ⟨⟨s,rfl⟩,⟨t,ht⟩⟩
          exact ht.symm.trans (congrArg p (hpBOnly t (ht.symm ▸ hwB s)))
        · rintro y rfl
          exact ⟨⟨1,hw1p⟩,mem_range_self 0⟩
      let W : Path (q 0) (p 0) := ⟨w,hw0q,hw1p⟩
      let P : Path (p 0) (q 1) := ⟨p,rfl,hp1q⟩
      let j : C(Interval,↥F) := (W.trans P).toContinuousMap
      have hj : IsEmbedding j := (j.continuous.isClosedEmbedding
        (LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
          W P hw.injective hp.injective hwp)).isEmbedding
      have hj0 : j 0 = q 0 := (W.trans P).source
      have hj1 : j 1 = q 1 := (W.trans P).target
      have hjrange : range j = range w ∪ range p := Path.trans_range W P
      have hpb : range p ⊆ range N.first ∪ range N.second ∪ range N.boundarySide :=
        fun y hy => hMsub (Or.inl (Or.inr (hpp hy)))
      have hwb : range w ⊆ range N.first ∪ range N.second ∪ range N.boundarySide :=
        fun y hy => hMsub (Or.inr (hww hy))
      have hjb : range j ⊆ range N.first ∪ range N.second ∪ range N.boundarySide := by
        rw [hjrange]
        exact union_subset hwb hpb
      obtain ⟨e,he,heb,hed⟩ := hsubdisk q j hq hj hj0.symm hj1.symm hjb hqi
      have hqI : ∀ t ∈ Ioo (0 : Interval) 1, q t ∉ B := by
        intro t ht hB
        exact Set.disjoint_left.mp hBfree hB (hqi ⟨t,ht,rfl⟩)
      have hqp : range q ∩ range p = ({q 1} : Set ↥F) := by
        apply Subset.antisymm
        · rintro y ⟨⟨t,rfl⟩,htp⟩
          by_cases ht0 : t=0
          · have hq0g : q 0 ∈ range g := M.second_on_b (hpp (ht0 ▸ htp))
            exact (hoff _ ⟨hqf (mem_range_self 0),hq0g⟩ hq0B).elim
          by_cases ht1 : t=1
          · exact congrArg q ht1
          exact (Set.disjoint_left.mp hUf
            (hqi ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
            (hpb htp)).elim
        · rintro y rfl
          exact ⟨mem_range_self 1,⟨1,hp1q⟩⟩
      have hqj := hdiskSides q j hq hj hj0.symm hj1.symm e he heb
      have hmeet (s t : Interval) (hst : q s = j t) :
          (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
        have hx : q s ∈ ({q 0,q 1} : Set ↥F) := hqj ▸ ⟨mem_range_self s,⟨t,hst.symm⟩⟩
        rcases hx with hx | hx
        · exact Or.inl ⟨hq.injective hx,hj.injective (hst.symm.trans (hx.trans hj0.symm))⟩
        · exact Or.inr ⟨hq.injective hx,hj.injective (hst.symm.trans (hx.trans hj1.symm))⟩
      obtain ⟨c,hc⟩ := exists_curve_of_two_arcs q j hq.injective hj.injective hj0.symm hj1.symm hmeet
      have hshape : range q ∪ range j = range q ∪ range p ∪ range w := by
        rw [hjrange,union_comm (range w) (range p),union_assoc]
      let M' : NullHalfBigonBoundary B f g := {
        first := q, second := p, boundarySide := w
        first_embedded := hq, second_embedded := hp, boundary_embedded := hw
        first_on_a := hqf, second_on_b := hpp.trans M.second_on_b
        first_zero_boundary := hq0B, second_zero_boundary := hp0.symm ▸ M.second_zero_boundary
        corner_eq := hp1q.symm, corner_off_boundary := hq1notB
        first_interior := hqI, second_interior := hpI, boundary_in_B := hwB
        boundary_zero := hw0q, boundary_one := hw1p, sides_inter := hqp
        loop := c, loop_image := hc.trans hshape
        loop_null := hnull c e he (by rw [hc,← heb]; exact image_subset_range _ _) }
      have hqBoundaryOnly (y : ↥F)
          (hy : y ∈ range N.first ∪ range N.second ∪ range N.boundarySide)
          (hy0 : y ≠ q 0) (hy1 : y ≠ q 1) : y ∉ range q := by
        rintro ⟨t,ht⟩
        by_cases ht0 : t=0
        · exact hy0 (ht.symm.trans (congrArg q ht0))
        by_cases ht1 : t=1
        · exact hy1 (ht.symm.trans (congrArg q ht1))
        exact Set.disjoint_left.mp hUf
          (ht ▸ hqi ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩) hy
      have hnotBoth : ¬ (u=0 ∧ r=1) := by
        rintro ⟨hu0,hr1⟩
        have hq0 : q 0 = M.first 0 := hu.symm.trans ((congrArg M.boundarySide hu0).trans M.boundary_zero)
        have hq1 : q 1 = M.first 1 := hr.symm.trans ((congrArg M.second hr1).trans M.corner_eq.symm)
        have hqOwn := LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem f M.first q
          hf hq M.first_on_a hqf ⟨0,hq0.symm⟩ ⟨1,hq1.symm⟩
        let t : Interval := ⟨1/2,by norm_num⟩
        exact Set.disjoint_left.mp hUf (hqi ⟨t,by change (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1; norm_num,rfl⟩)
          (hMsub (Or.inl (Or.inl (hqOwn (mem_range_self t)))))
      have hmissing : ∃ y ∈ ({M.first 0,M.second 0,M.first 1} : Set ↥F), y ∉ range e := by
        by_cases hu0 : u=0
        · have hr1 : r ≠ 1 := fun h => hnotBoth ⟨hu0,h⟩
          let y := M.first 1
          have hyOld := hMsub (show y ∈ range M.first ∪ range M.second ∪ range M.boundarySide from
            Or.inl (Or.inl (mem_range_self 1)))
          have hyq : y ∉ range q := hqBoundaryOnly y hyOld
            (fun he => M.corner_off_boundary (show y ∈ B from he.symm ▸ hq0B))
            (fun he => hr1 (M.second_embedded.injective (hr.trans (he.symm.trans M.corner_eq))))
          have hyp : y ∉ range p := by
            rintro ⟨t,ht⟩
            have htEnds := HyperellipticModel.actual_embedded_side_source_endpoint M.second p
              M.second_embedded hp hpp t (Or.inr (ht.trans M.corner_eq))
            rcases htEnds with ht0 | ht1
            · exact M.corner_off_boundary (show y ∈ B from ht ▸ (ht0 ▸ (hp0.symm ▸ M.second_zero_boundary)))
            · exact hyq ⟨1,hp1q.symm.trans ((congrArg p ht1).symm.trans ht)⟩
          have hyw : y ∉ range w := by
            rintro ⟨t,ht⟩; exact M.corner_off_boundary (show y ∈ B from ht ▸ hwB t)
          refine ⟨y,Or.inr (Or.inr rfl),holdExcluded e he hed y hyOld ?_⟩
          rw [heb,hshape]
          exact fun h => h.elim (fun h => h.elim hyq hyp) hyw
        · let y := M.first 0
          have hyOld := hMsub (show y ∈ range M.first ∪ range M.second ∪ range M.boundarySide from
            Or.inl (Or.inl (mem_range_self 0)))
          have hyq : y ∉ range q := hqBoundaryOnly y hyOld
            (fun he => hu0 (M.boundary_embedded.injective (hu.trans (he.symm.trans M.boundary_zero.symm))))
            (fun he => hq1notB (he ▸ M.first_zero_boundary))
          have hyp : y ∉ range p := by
            intro hy
            exact hoff _ ⟨M.first_on_a (mem_range_self 0),M.second_on_b (hpp hy)⟩ M.first_zero_boundary
          have hyw : y ∉ range w := by
            rintro ⟨t,ht⟩
            have htEnds := HyperellipticModel.actual_embedded_side_source_endpoint M.boundarySide w
              M.boundary_embedded hw hww t (Or.inl (ht.trans M.boundary_zero.symm))
            rcases htEnds with ht0 | ht1
            · exact hyq ⟨0,hw0q.symm.trans ((congrArg w ht0).symm.trans ht)⟩
            · exact hyp ⟨0,hw1p.symm.trans ((congrArg w ht1).symm.trans ht)⟩
          refine ⟨y,Or.inl rfl,holdExcluded e he hed y hyOld ?_⟩
          rw [heb,hshape]
          exact fun h => h.elim (fun h => h.elim hyq hyp) hyw
      obtain ⟨y,hy,hye⟩ := hmissing
      exact ⟨y,hy,M',e,he,heb.trans hshape,hed,hye⟩
    by_cases hq0p : q 0 ∈ range M.second
    · by_cases hq1p : q 1 ∈ range M.second
      · exact Or.inl (hord hq0p hq1p)
      · let qr : C(Interval,↥F) := q.comp ⟨unitInterval.symm,unitInterval.symmHomeomorph.continuous⟩
        have hqr : IsEmbedding qr := hq.comp unitInterval.symmHomeomorph.isEmbedding
        have hqrf : range qr ⊆ range f := by
          rintro y ⟨t,rfl⟩; exact hqf (mem_range_self _)
        apply Or.inr
        apply hmixed qr hqr hqrf
        · change q (unitInterval.symm 0) ∈ range M.boundarySide
          rw [unitInterval.symm_zero]
          exact hq1.resolve_left hq1p
        · change q (unitInterval.symm 1) ∈ range M.second
          rw [unitInterval.symm_one]
          exact hq0p
        · rintro y ⟨t,ht,rfl⟩
          apply hqi
          refine ⟨unitInterval.symm t,?_,rfl⟩
          change 0 < 1-t.val ∧ 1-t.val < 1
          exact ⟨sub_pos.mpr ht.2,sub_lt_self _ (show (0:ℝ) < t.val from ht.1)⟩
    · have hq0w := hq0.resolve_left hq0p
      have hq1p : q 1 ∈ range M.second := hq1.resolve_right (fun h => hnotBB ⟨hq0w,h⟩)
      exact Or.inr (hmixed q hq hqf hq0w hq1p hqi)
  rcases hcutClassified with ⟨q,hq,hqf,hq0,hq1,hqi,hnotBB⟩ | ⟨q,hq,hqf,hq0,hq1,hqi,hnotBB⟩
  · rcases hcapOfCut a.val.val b.val.val a.val.property.1 b.val.property.1 haB hbB hfinite
      hcontactOff N hboundary q hq hqf hq0 hq1 hqi hnotBB with ho | ⟨y,hy,N',e,he,heb,hed,hye⟩
    · exact Or.inl ho
    · exact Or.inr ⟨N',e,he,heb,hed,y,hy,hye⟩
  · let wr : C(Interval,↥F) := N.boundarySide.comp
      ⟨unitInterval.symm,unitInterval.symmHomeomorph.continuous⟩
    have hwrange : range wr = range N.boundarySide := by
      change range (N.boundarySide ∘ unitInterval.symm) = _
      rw [range_comp,show range unitInterval.symm = univ from unitInterval.symmHomeomorph.surjective.range_eq,image_univ]
    let M : NullHalfBigonBoundary B b.val.val a.val.val := {
      first := N.second, second := N.first, boundarySide := wr
      first_embedded := N.second_embedded, second_embedded := N.first_embedded
      boundary_embedded := N.boundary_embedded.comp unitInterval.symmHomeomorph.isEmbedding
      first_on_a := N.second_on_b, second_on_b := N.first_on_a
      first_zero_boundary := N.second_zero_boundary, second_zero_boundary := N.first_zero_boundary
      corner_eq := N.corner_eq.symm, corner_off_boundary := N.corner_eq ▸ N.corner_off_boundary
      first_interior := N.second_interior, second_interior := N.first_interior
      boundary_in_B := fun t => N.boundary_in_B _
      boundary_zero := by change N.boundarySide (unitInterval.symm 0) = _; rw [unitInterval.symm_zero]; exact N.boundary_one
      boundary_one := by change N.boundarySide (unitInterval.symm 1) = _; rw [unitInterval.symm_one]; exact N.boundary_zero
      sides_inter := by rw [inter_comm,N.sides_inter,N.corner_eq]
      loop := N.loop
      loop_image := by rw [N.loop_image,hwrange,union_comm (range N.first) (range N.second)]
      loop_null := N.loop_null }
    have hMb : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range M.first ∪ range M.second ∪ range M.boundarySide := by
      change _ = range N.second ∪ range N.first ∪ range wr
      rw [hboundary,hwrange,union_comm (range N.first) (range N.second)]
    have hq0' : q 0 ∈ range M.second ∪ range M.boundarySide := by
      change q 0 ∈ range N.first ∪ range wr
      rwa [hwrange]
    have hq1' : q 1 ∈ range M.second ∪ range M.boundarySide := by
      change q 1 ∈ range N.first ∪ range wr
      rwa [hwrange]
    have hnotBB' : ¬ (q 0 ∈ range M.boundarySide ∧ q 1 ∈ range M.boundarySide) := by
      change ¬ (q 0 ∈ range wr ∧ q 1 ∈ range wr)
      rwa [hwrange]
    have hfin : (range b.val.val ∩ range a.val.val).Finite := by rwa [inter_comm]
    have hoff : ∀ y ∈ range b.val.val ∩ range a.val.val, y ∉ B :=
      fun y hy => hcontactOff y ⟨hy.2,hy.1⟩
    rcases hcapOfCut b.val.val a.val.val b.val.property.1 a.val.property.1 hbB haB hfin hoff
      M hMb q hq hqf hq0' hq1' hqi hnotBB' with ⟨K,e,he,heb,hed,hempty⟩ | ⟨y,hy,K,e,he,heb,hed,hye⟩
    · let K' : NullBigonBoundary B a.val.val b.val.val := {
        first := K.second, second := K.first
        first_embedded := K.second_embedded, second_embedded := K.first_embedded
        first_on_a := K.second_on_b, second_on_b := K.first_on_a
        zero_eq := K.zero_eq.symm, one_eq := K.one_eq.symm
        corners_off_boundary := ⟨K.zero_eq ▸ K.corners_off_boundary.1,K.one_eq ▸ K.corners_off_boundary.2⟩
        sides_inter := by rw [inter_comm,K.sides_inter,K.zero_eq,K.one_eq]
        loop := K.loop, loop_image := K.loop_image.trans (union_comm _ _), loop_null := K.loop_null }
      refine Or.inl ⟨K',e,he,heb.trans (union_comm _ _),hed,?_⟩
      simpa only [union_comm] using hempty
    · let wK : C(Interval,↥F) := K.boundarySide.comp
        ⟨unitInterval.symm,unitInterval.symmHomeomorph.continuous⟩
      have hwK : range wK = range K.boundarySide := by
        change range (K.boundarySide ∘ unitInterval.symm) = _
        rw [range_comp,show range unitInterval.symm = univ from unitInterval.symmHomeomorph.surjective.range_eq,image_univ]
      let K' : NullHalfBigonBoundary B a.val.val b.val.val := {
        first := K.second, second := K.first, boundarySide := wK
        first_embedded := K.second_embedded, second_embedded := K.first_embedded
        boundary_embedded := K.boundary_embedded.comp unitInterval.symmHomeomorph.isEmbedding
        first_on_a := K.second_on_b, second_on_b := K.first_on_a
        first_zero_boundary := K.second_zero_boundary, second_zero_boundary := K.first_zero_boundary
        corner_eq := K.corner_eq.symm, corner_off_boundary := K.corner_eq ▸ K.corner_off_boundary
        first_interior := K.second_interior, second_interior := K.first_interior
        boundary_in_B := fun t => K.boundary_in_B _
        boundary_zero := by change K.boundarySide (unitInterval.symm 0) = _; rw [unitInterval.symm_zero]; exact K.boundary_one
        boundary_one := by change K.boundarySide (unitInterval.symm 1) = _; rw [unitInterval.symm_one]; exact K.boundary_zero
        sides_inter := by rw [inter_comm,K.sides_inter,K.corner_eq]
        loop := K.loop
        loop_image := by rw [K.loop_image,hwK,union_comm (range K.first) (range K.second)]
        loop_null := K.loop_null }
      have hK'b : e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range K'.first ∪ range K'.second ∪ range K'.boundarySide := by
        change _ = range K.second ∪ range K.first ∪ range wK
        rw [heb,hwK,union_comm (range K.first) (range K.second)]
      refine Or.inr ⟨K',e,he,hK'b,hed,y,?_,hye⟩
      change y ∈ ({N.second 0,N.first 0,N.second 1} : Set ↥F) at hy
      rcases hy with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (h.trans N.corner_eq.symm))
