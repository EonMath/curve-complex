import RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.ActualTwoSideDiskSubsetDescent
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.EssentialArcDiskExclusion
import RegionalHalfDescentCap

open CurveComplex Set Topology RegionalTotalDecrease
open CoherentEndpointMotion.FreeBoundaryNullGeometry
universe v
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- C half descent: a literal three-side B-boundary F disk contains an ordinary or half F subdisk with empty whole-arc interior. Output nullity is produced with the actual F disk. -/
theorem regional_actual_interval_half_disk_has_empty_subdisk
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
            range e ⊆ range d ∧
            Disjoint (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
              (range a.val.val ∪ range b.val.val)) := by
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    a b hend hfinite hcross N d hd hboundary
  letI : ClosedSurface S := Classical.choice hS.2.1
  let B : Set ↥F := {y | y.val ∈ boundaryCircle}
  let C : Set ↥F := (range a.val.val ∩ range b.val.val) ∪
    {a.val.val 0,a.val.val 1,b.val.val 0,b.val.val 1}
  have hCfinite : C.Finite := hfinite.union (by simp)
  let energy (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)) : ℕ :=
    (C ∩ range e).ncard
  have hstep
      (N : NullHalfBigonBoundary B a.val.val b.val.val)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F))
      (hd : IsEmbedding d)
      (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range N.first ∪ range N.second ∪ range N.boundarySide)
      (hempty : ¬ Disjoint
        (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (range a.val.val ∪ range b.val.val)) :
      (∃ N' : NullBigonBoundary B a.val.val b.val.val,
        ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          IsEmbedding e ∧
          e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range N'.first ∪ range N'.second ∧
          range e ⊆ range d ∧
          Disjoint (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
            (range a.val.val ∪ range b.val.val)) ∨
      (∃ N' : NullHalfBigonBoundary B a.val.val b.val.val,
        ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          IsEmbedding e ∧
          e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range N'.first ∪ range N'.second ∪ range N'.boundarySide ∧
          range e ⊆ range d ∧ energy e < energy d) := by
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
    let oldVertices : Set ↥F := {N.first 0,N.second 0,N.first 1}
    have hboundaryParameter (f : C(Interval,↥F))
        (hfInterior : ∀ t ∈ Ioo (0 : Interval) 1, f t ∉ B)
        (y : ↥F) (hyf : y ∈ range f) (hyB : y ∈ B) : y = f 0 ∨ y = f 1 := by
      obtain ⟨t,ht⟩ := hyf
      by_cases ht0 : t = 0
      · exact Or.inl (ht.symm.trans (congrArg f ht0))
      by_cases ht1 : t = 1
      · exact Or.inr (ht.symm.trans (congrArg f ht1))
      exact (hfInterior t ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩ (ht.symm ▸ hyB)).elim
    have hvertexC : oldVertices ⊆ C := by
      rintro y (rfl | rfl | rfl)
      · have h := hboundaryParameter a.val.val haInterior (N.first 0)
          (N.first_on_a (mem_range_self 0)) N.first_zero_boundary
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · have h := hboundaryParameter b.val.val hbInterior (N.second 0)
          (N.second_on_b (mem_range_self 0)) N.second_zero_boundary
        rcases h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inl ⟨N.first_on_a (mem_range_self 1),
          N.second_on_b ⟨1,N.corner_eq.symm⟩⟩
    have hvertexD : oldVertices ⊆ range d := by
      intro y hy
      apply image_subset_range d _
      rw [hboundary]
      rcases hy with rfl | rfl | rfl
      · exact Or.inl (Or.inl (mem_range_self 0))
      · exact Or.inl (Or.inr (mem_range_self 0))
      · exact Or.inl (Or.inl (mem_range_self 1))
    have hdrop (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F))
        (hesub : range e ⊆ range d)
        (hexcluded : ∃ y ∈ oldVertices, y ∉ range e) : energy e < energy d := by
      apply Set.ncard_lt_ncard _ (hCfinite.inter_of_left _)
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨Set.inter_subset_inter_right C hesub,?_⟩
      intro heq
      obtain ⟨y,hy,hyNot⟩ := hexcluded
      have hyE : y ∈ C ∩ range e := heq.symm ▸ ⟨hvertexC hy,hvertexD hy⟩
      exact hyNot hyE.2
    have hcap :
        (∃ N' : NullBigonBoundary B a.val.val b.val.val,
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              range N'.first ∪ range N'.second ∧
            range e ⊆ range d ∧
            Disjoint (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
              (range a.val.val ∪ range b.val.val)) ∨
        (∃ N' : NullHalfBigonBoundary B a.val.val b.val.val,
          ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            IsEmbedding e ∧
            e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              range N'.first ∪ range N'.second ∪ range N'.boundarySide ∧
            range e ⊆ range d ∧ ∃ y ∈ oldVertices, y ∉ range e) := by
      exact regional_actual_interval_half_disk_intrusion_has_strict_cap
        S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
        J c hdisjoint hbaseDisjoint hfrontier a b hend hfinite hcross N d hd hboundary hempty
    rcases hcap with hordinary | ⟨N',e,he,heBoundary,heSub,heExcluded⟩
    · exact Or.inl hordinary
    · exact Or.inr ⟨N',e,he,heBoundary,heSub,hdrop e heSub heExcluded⟩
  let P : ℕ → Prop := fun n =>
    ∃ N' : NullHalfBigonBoundary B a.val.val b.val.val,
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        IsEmbedding e ∧
        e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range N'.first ∪ range N'.second ∪ range N'.boundarySide ∧
        range e ⊆ range d ∧ energy e = n
  have hex : ∃ n, P n := ⟨energy d,N,d,hd,hboundary,Set.Subset.rfl,rfl⟩
  obtain ⟨N',e,he,heBoundary,heD,heEnergy⟩ := Nat.find_spec hex
  by_cases hclear : Disjoint
      (e '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (range a.val.val ∪ range b.val.val)
  · exact Or.inr ⟨N',e,he,heBoundary,heD,hclear⟩
  rcases hstep N' e he heBoundary hclear with hordinary | hsmaller
  · obtain ⟨N'',e',he',he'Boundary,he'e,he'Empty⟩ := hordinary
    exact Or.inl ⟨N'',e',he',he'Boundary,he'e.trans heD,he'Empty⟩
  · obtain ⟨N'',e',he',he'Boundary,he'e,he'Energy⟩ := hsmaller
    exact False.elim (Nat.find_min hex (he'Energy.trans_eq heEnergy)
      ⟨N'',e',he',he'Boundary,he'e.trans heD,rfl⟩)
