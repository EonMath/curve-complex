import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
open Set Topology CurveComplex

/-- A proper embedded arc inside a disk is boundary parallel if its endpoints
can be joined by an embedded boundary interval lying in the same disk. The
conclusion is the literal embedded-disk witness used by the original arc complex. -/
theorem proper_arc_in_boundary_attached_disk_is_boundary_parallel
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (a : C(Interval, X)) (ha : IsEmbedding a)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, X))
    (hd : IsEmbedding d) (haD : Set.range a ⊆ Set.range d)
    (w : C(Interval, X)) (hw : IsEmbedding w)
    (hwB : ∀ t, w t ∈ B) (hwD : Set.range w ⊆ Set.range d)
    (h0 : a 0 ∈ Set.range w) (h1 : a 1 ∈ Set.range w) :
    ∃ b : C(Interval, X), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, X),
        IsEmbedding e ∧
        e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a ∪ Set.range b := by
  obtain ⟨p,hp⟩ := h0
  obtain ⟨q,hq⟩ := h1
  have hpq : p ≠ q := by
    intro heq
    have he : a 0 = a 1 := hp.symm.trans ((congrArg w heq).trans hq)
    have hz := ha.injective he
    have hzv := congrArg Subtype.val hz
    norm_num at hzv
  let f : Interval → Interval := fun t =>
    ⟨(1 - (t : ℝ)) * (p : ℝ) + (t : ℝ) * (q : ℝ), by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) p.property.1)
          (mul_nonneg t.property.1 q.property.1)
      · nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr p.property.2),
          mul_nonneg t.property.1 (sub_nonneg.mpr q.property.2)]⟩
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hfi : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    dsimp [f] at hh
    have hpqv : (p : ℝ) ≠ (q : ℝ) := fun he => hpq (Subtype.ext he)
    have : ((s : ℝ) - (t : ℝ)) * ((q : ℝ) - (p : ℝ)) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with hs | hpq'
    · linarith
    · exact (hpqv (by linarith)).elim
  have hf0 : f 0 = p := Subtype.ext (by simp [f])
  have hf1 : f 1 = q := Subtype.ext (by simp [f])
  let b : C(Interval,X) := w.comp ⟨f,hfc⟩
  have hb : IsEmbedding b := hw.comp (hfc.isClosedEmbedding hfi).isEmbedding
  have hb0 : b 0 = a 0 := by change w (f 0) = _; rw [hf0,hp]
  have hb1 : b 1 = a 1 := by change w (f 1) = _; rw [hf1,hq]
  have hbB (t : Interval) : b t ∈ B := hwB (f t)
  have hbD : Set.range b ⊆ Set.range d := by
    rintro z ⟨t,rfl⟩
    exact hwD ⟨f t,rfl⟩
  have hmeet (s t : Interval) (hst : a s = b t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hsB : a s ∈ B := hst.symm ▸ hbB t
    by_cases hs0 : s = 0
    · left
      refine ⟨hs0,hb.injective ?_⟩
      rw [hb0]
      exact hst.symm.trans (congrArg a hs0)
    · have hs1 : s = 1 := by
        by_contra hs1
        have hspos : (0 : ℝ) < s := lt_of_le_of_ne s.property.1
          (fun h => hs0 (Subtype.ext h.symm))
        have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2
          (fun h => hs1 (Subtype.ext h))
        exact haInterior s ⟨hspos,hslt⟩ hsB
      right
      refine ⟨hs1,hb.injective ?_⟩
      rw [hb1]
      exact hst.symm.trans (congrArg a hs1)
  obtain ⟨c,hc⟩ := exists_curve_of_two_arcs a b ha.injective hb.injective hb0.symm hb1.symm hmeet
  obtain ⟨e,he,hebd,-⟩ := LocalSurgery.curve_in_embedded_disk_bounds_subdisk c d hd
    (by rw [hc]; exact Set.union_subset haD hbD)
  exact ⟨b,hb,hbB,e,he,hebd.trans hc⟩

#print axioms proper_arc_in_boundary_attached_disk_is_boundary_parallel

/-- An essential proper arc in a surface subset cannot enter a disk through
its boundary interval when it avoids the other boundary sides. All disk
witnesses stay in the same subset, as required by original essentiality. -/
theorem essential_proper_arc_avoids_boundary_attached_disk_interior
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (F : Set S) (B : Set ↥F) (a : C(Interval, ↥F)) (ha : IsEmbedding a)
    (hends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ b : C(Interval, ↥F), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F),
        IsEmbedding e ∧
        e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a ∪ Set.range b)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F))
    (hd : IsEmbedding d)
    (w : C(Interval, ↥F)) (hw : IsEmbedding w)
    (hwB : ∀ t, w t ∈ B) (hwD : Set.range w ⊆ Set.range d)
    (hBD : Set.range d ∩ B ⊆ Set.range w)
    (hside : Set.range a ∩
      (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) ⊆ B) :
    Disjoint (a '' Ioo (0 : Interval) 1) (Set.range d) := by
  let A : C(Interval,S) := ⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩
  let D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun z => (d z).val, continuous_subtype_val.comp d.continuous⟩
  have hD : IsEmbedding D := IsEmbedding.subtypeVal.comp hd
  let O := A '' Ioo (0 : Interval) 1
  have hO : IsPreconnected O := isPreconnected_Ioo.image A A.continuous.continuousOn
  have hOside : Disjoint O
      (D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t,ht,rfl⟩ ⟨z,hz,heq⟩
    exact haInterior t ht (hside ⟨⟨t,rfl⟩,⟨z,hz,Subtype.ext heq⟩⟩)
  have hcover : O ⊆ interior (Set.range D) ∪ (Set.range D)ᶜ := by
    intro y hy
    by_cases hyD : y ∈ Set.range D
    · left
      obtain ⟨z,rfl⟩ := hyD
      rw [LocalSurgery.embedded_surface_disk_interior_eq D hD]
      refine ⟨z,?_,rfl⟩
      have hzle : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
      apply lt_of_le_of_ne hzle
      intro he
      exact Set.disjoint_left.mp hOside hy ⟨z,he,rfl⟩
    · exact Or.inr hyD
  have hclosed : IsClosed (Set.range D) := (isCompact_range D.continuous).isClosed
  apply Set.disjoint_left.mpr
  rintro y ⟨t,ht,rfl⟩ ⟨z,hz⟩
  have hinside : O ⊆ interior (Set.range D) :=
    (hO.subset_or_subset isOpen_interior hclosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover).resolve_right (fun hout =>
        hout ⟨t,ht,rfl⟩ ⟨z,congrArg Subtype.val hz⟩)
  have hmidD : O ⊆ Set.range D := hinside.trans interior_subset
  have hrange : Set.range A ⊆ closure O := by
    rintro y ⟨t,rfl⟩
    apply A.continuous.continuousOn.image_closure
    refine ⟨t,?_,rfl⟩
    rw [closure_Ioo (show (0 : Interval) ≠ 1 by norm_num)]
    exact ⟨by exact t.property.1, by exact t.property.2⟩
  have haD : Set.range a ⊆ Set.range d := by
    rintro y ⟨t,rfl⟩
    obtain ⟨v,hv⟩ := (hrange.trans (closure_minimal hmidD hclosed)) ⟨t,rfl⟩
    exact ⟨v,Subtype.ext hv⟩
  exact hessential (proper_arc_in_boundary_attached_disk_is_boundary_parallel B a ha
    haInterior d hd haD w hw hwB hwD
    (hBD ⟨haD ⟨0,rfl⟩,hends.1⟩) (hBD ⟨haD ⟨1,rfl⟩,hends.2⟩))

#print axioms essential_proper_arc_avoids_boundary_attached_disk_interior

/-- In the literal punctured surface an embedded disk has no ambient-interior
point on the original chart boundary. No collar certificate is assumed. -/
theorem original_chart_boundary_avoids_disk_interior
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q)),
      IsEmbedding d →
      Disjoint B (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
  intro Q B d hd
  letI : ClosedSurface S := Classical.choice hS.2.1
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let O : Set S := e.symm '' Metric.ball (e x) R
  let D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun z => (d z).val, continuous_subtype_val.comp d.continuous⟩
  have hD : IsEmbedding D := IsEmbedding.subtypeVal.comp hd
  let U := D '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  have hU : IsOpen U := LocalSurgery.embedded_surface_disk_interior_isOpen D hD
  have hUQ : U ⊆ Oᶜ := by
    rintro y ⟨z,hz,rfl⟩
    exact (d z).property
  have hBcl : ∀ y : ↥Q, y ∈ B → y.val ∈ closure O := by
    rintro y ⟨z,hz,hzy⟩
    rw [← hzy]
    have hcl : z ∈ closure (Metric.ball (e x) R) := by
      rw [closure_ball _ hR.ne']
      exact Metric.sphere_subset_closedBall hz
    have hc : ContinuousOn e.symm (closure (Metric.ball (e x) R)) := by
      rw [closure_ball _ hR.ne']
      exact e.symm.continuousOn.mono htarget
    exact hc.image_closure ⟨z,hcl,rfl⟩
  apply Set.disjoint_left.mpr
  rintro y hy ⟨z,hz,rfl⟩
  have hycl := hBcl (d z) hy
  have hyU : (d z).val ∈ U := ⟨z,hz,rfl⟩
  obtain ⟨v,hvU,hvO⟩ := (mem_closure_iff.mp hycl) U hU hyU
  exact hUQ hvU hvO

#print axioms original_chart_boundary_avoids_disk_interior

/-- Literal disk essentiality clears an entire proper arc from the interior of
an actual boundary half-bigon whose two nonboundary sides it avoids. -/
theorem essential_arc_clears_boundary_half_bigon
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (F : Set S) (B : Set ↥F) (a : C(Interval, ↥F)) (ha : IsEmbedding a)
    (hends : a 0 ∈ B ∧ a 1 ∈ B)
    (haInterior : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (hessential : ¬ ∃ b : C(Interval, ↥F), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
      ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F),
        IsEmbedding e ∧
        e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a ∪ Set.range b)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F))
    (hd : IsEmbedding d)
    (hBfree : Disjoint B
      (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}))
    (p q w : C(Interval, ↥F)) (hw : IsEmbedding w)
    (hwB : ∀ t, w t ∈ B)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      (Set.range p ∪ Set.range q) ∪ Set.range w)
    (hpB : Set.range p ∩ B ⊆ Set.range w)
    (hqB : Set.range q ∩ B ⊆ Set.range w)
    (hap : Disjoint (Set.range a) (Set.range p))
    (haq : Disjoint (Set.range a) (Set.range q)) :
    Disjoint (Set.range a)
      (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
  have hwD : Set.range w ⊆ Set.range d := by
    intro y hy
    have hybd : y ∈ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [hboundary]
      exact Or.inr hy
    exact Set.image_subset_range _ _ hybd
  have hBD : Set.range d ∩ B ⊆ Set.range w := by
    rintro y ⟨⟨z,rfl⟩,hyB⟩
    have hz : z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      have hzle : dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 := z.property
      apply le_antisymm hzle
      apply not_lt.mp
      intro hzlt
      exact Set.disjoint_left.mp hBfree hyB ⟨z,hzlt,rfl⟩
    have hy : d z ∈ (Set.range p ∪ Set.range q) ∪ Set.range w :=
      hboundary ▸ Set.mem_image_of_mem d hz
    rcases hy with (hyp | hyq) | hyw
    · exact hpB ⟨hyp,hyB⟩
    · exact hqB ⟨hyq,hyB⟩
    · exact hyw
  have hside : Set.range a ∩
      (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) ⊆ B := by
    rintro y ⟨hya,hys⟩
    rw [hboundary] at hys
    rcases hys with (hyp | hyq) | ⟨t,rfl⟩
    · exact (Set.disjoint_left.mp hap hya hyp).elim
    · exact (Set.disjoint_left.mp haq hya hyq).elim
    · exact hwB t
  have hclear := essential_proper_arc_avoids_boundary_attached_disk_interior
    F B a ha hends haInterior hessential d hd w hw hwB hwD hBD hside
  apply Set.disjoint_left.mpr
  rintro y ⟨t,rfl⟩ hyD
  by_cases ht0 : t = 0
  · exact Set.disjoint_left.mp hBfree (ht0 ▸ hends.1) hyD
  by_cases ht1 : t = 1
  · exact Set.disjoint_left.mp hBfree (ht1 ▸ hends.2) hyD
  have ht : t ∈ Ioo (0 : Interval) 1 := by
    constructor
    · exact lt_of_le_of_ne t.property.1 (fun h => ht0 h.symm)
    · exact lt_of_le_of_ne t.property.2 (fun h => ht1 h)
  exact Set.disjoint_left.mp hclear ⟨t,ht,rfl⟩ (Set.image_subset_range _ _ hyD)

#print axioms essential_arc_clears_boundary_half_bigon

private theorem half_arc_boundary_contact_is_initial
    {X : Type} [TopologicalSpace X] (B : Set X) (p w : C(Interval,X))
    (hp0 : p 0 ∈ Set.range w) (hp1 : p 1 ∉ B)
    (hpInterior : ∀ t ∈ Ioo (0 : Interval) 1, p t ∉ B) :
    Set.range p ∩ B ⊆ Set.range w := by
  rintro y ⟨⟨t,rfl⟩,htB⟩
  by_cases ht0 : t = 0
  · simpa only [ht0] using hp0
  by_cases ht1 : t = 1
  · exact (hp1 (ht1 ▸ htB)).elim
  exact (hpInterior t ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ htB).elim

/-- The actual original-Q half-bigon clearance consumer: essentiality and
avoidance of its two arc sides produce interior clearance. The chart boundary
and the boundary-contact condition are derived, not supplied as certificates. -/
theorem original_essential_arc_clears_half_bigon
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hS : IsGenus S g) (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (a : C(Interval, ↥Q)), IsEmbedding a →
      (a 0 ∈ B ∧ a 1 ∈ B) →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B) →
      (¬ ∃ b : C(Interval, ↥Q), IsEmbedding b ∧ (∀ t, b t ∈ B) ∧
        ∃ e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding e ∧
          e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a ∪ Set.range b) →
      ∀ (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q)),
        IsEmbedding d →
      ∀ (p q w : C(Interval, ↥Q)), IsEmbedding w →
        (∀ t, w t ∈ B) →
        (d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          (Set.range p ∪ Set.range q) ∪ Set.range w) →
        p 0 ∈ Set.range w → q 0 ∈ Set.range w → p 1 ∉ B → q 1 ∉ B →
        (∀ t ∈ Ioo (0 : Interval) 1, p t ∉ B) →
        (∀ t ∈ Ioo (0 : Interval) 1, q t ∉ B) →
        Disjoint (Set.range a) (Set.range p) →
        Disjoint (Set.range a) (Set.range q) →
        Disjoint (Set.range a)
          (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
  intro Q B a ha hends haInterior hessential d hd p q w hw hwB hboundary
    hp0 hq0 hp1 hq1 hpInterior hqInterior hap haq
  letI : ClosedSurface S := Classical.choice hS.2.1
  exact essential_arc_clears_boundary_half_bigon Q B a ha hends haInterior hessential d hd
    (original_chart_boundary_avoids_disk_interior S g hS x R hR htarget d hd)
    p q w hw hwB hboundary
    (half_arc_boundary_contact_is_initial B p w hp0 hp1 hpInterior)
    (half_arc_boundary_contact_is_initial B q w hq0 hq1 hqInterior) hap haq

#print axioms original_essential_arc_clears_half_bigon
