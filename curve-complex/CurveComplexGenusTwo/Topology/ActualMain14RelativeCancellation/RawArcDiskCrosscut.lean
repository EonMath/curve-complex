import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior

namespace CurveComplex.LocalSurgery
open Set Topology
variable {S : Type} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]

/-- A raw embedded interval with both endpoints outside the open disk produces
an actual crosscut upon intrusion; no closed curve or chosen return is supplied. -/
theorem raw_embedded_arc_entering_disk_has_crosscut
    (g : C(Interval,S)) (hg : IsEmbedding g)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d)
    (h0 : g 0 ∉ d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
    (h1 : g 1 ∉ d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
    (hin : (range g ∩ (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
    ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ range g ∧
      q 0 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      q 1 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      q '' Ioo (0:Interval) 1 ⊆
        d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  classical
  let U : Set S := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  let K : Set S := range d
  have hUo : IsOpen U := embedded_surface_disk_interior_isOpen d hd
  have hKc : IsClosed K := (isCompact_range d.continuous).isClosed
  have hUK : U ⊆ K := image_subset_range _ _
  obtain ⟨x,⟨t,rfl⟩,htU⟩ := hin
  have htf : t ≠ 0 := by intro ht; exact h0 (ht ▸ htU)
  have htl : t ≠ 1 := by intro ht; exact h1 (ht ▸ htU)
  let L : Set Interval := Icc 0 t ∩ g ⁻¹' Uᶜ
  let R : Set Interval := Icc t 1 ∩ g ⁻¹' Uᶜ
  have hpre : IsClosed (g ⁻¹' Uᶜ) := hUo.isClosed_compl.preimage g.continuous
  have hL : L.Nonempty := ⟨0,⟨le_rfl,t.property.1⟩,h0⟩
  have hR : R.Nonempty := ⟨1,⟨t.property.2,le_rfl⟩,h1⟩
  obtain ⟨r,hr,hrmax⟩ := (isCompact_Icc.inter_right hpre).exists_isGreatest hL
  obtain ⟨s,hs,hsmin⟩ := (isCompact_Icc.inter_right hpre).exists_isLeast hR
  have hrt : r < t := lt_of_le_of_ne hr.1.2 (by intro he; exact hr.2 (he ▸ htU))
  have hts : t < s := lt_of_le_of_ne hs.1.1 (by intro he; exact hs.2 (he.symm ▸ htU))
  have hrs : r < s := hrt.trans hts
  have hinside (v : Interval) (hv : v ∈ Ioo r s) : g v ∈ U := by
    by_contra hnot
    by_cases hvt : v ≤ t
    · exact (not_lt_of_ge (hrmax ⟨⟨v.property.1,hvt⟩,hnot⟩)) hv.1
    · exact (not_lt_of_ge (hsmin ⟨⟨le_of_not_ge hvt,v.property.2⟩,hnot⟩)) hv.2
  have hIccK : Icc r s ⊆ g ⁻¹' K := by
    rw [← closure_Ioo hrs.ne]
    apply (hKc.preimage g.continuous).closure_subset_iff.mpr
    exact fun v hv => hUK (hinside v hv)
  have hboundary (v : Interval) (hvK : g v ∈ K) (hvU : g v ∉ U) :
      g v ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    obtain ⟨u,hu⟩ := hvK
    refine ⟨u,?_,hu⟩
    have hn : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hnot : ¬ ‖u.val‖ < 1 := by
      intro h
      apply hvU
      exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using h,hu⟩
    simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
      using le_antisymm hn (le_of_not_gt hnot)
  let affine : Interval → Interval := fun u =>
    ⟨(1-u.val)*r.val+u.val*s.val,by
      constructor <;> nlinarith [u.property.1,u.property.2,r.property.1,r.property.2,
        s.property.1,s.property.2]⟩
  have haff (u : Interval) : affine u ∈ Icc r s := by
    constructor
    · change r.val ≤ (1-u.val)*r.val+u.val*s.val
      nlinarith [u.property.1,u.property.2,show r.val < s.val from hrs]
    · change (1-u.val)*r.val+u.val*s.val ≤ s.val
      nlinarith [u.property.1,u.property.2,show r.val < s.val from hrs]
  have haffi : Function.Injective affine := by
    intro u v he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    dsimp [affine] at he'
    have hz : (u.val-v.val)*(s.val-r.val)=0 := by nlinarith only [he']
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact False.elim ((ne_of_gt (show r.val < s.val from hrs)) (sub_eq_zero.mp hz))
  let q : C(Interval,S) := ⟨g ∘ affine,g.continuous.comp (by fun_prop)⟩
  have hq0 : q 0 = g r := congrArg g (Subtype.ext (by simp [affine]))
  have hq1 : q 1 = g s := congrArg g (Subtype.ext (by simp [affine]))
  refine ⟨q,(q.continuous.isClosedEmbedding (hg.injective.comp haffi)).isEmbedding,?_,
    hq0.symm ▸ hboundary r (hIccK ⟨le_rfl,hrs.le⟩) hr.2,
    hq1.symm ▸ hboundary s (hIccK ⟨hrs.le,le_rfl⟩) hs.2,?_⟩
  · rintro z ⟨u,rfl⟩
    exact mem_range_self (affine u)
  · rintro z ⟨u,hu,rfl⟩
    apply hinside
    constructor
    · change r.val < (1-u.val)*r.val+u.val*s.val
      nlinarith [show 0 < u.val from hu.1,show u.val < 1 from hu.2,
        show r.val < s.val from hrs]
    · change (1-u.val)*r.val+u.val*s.val < s.val
      nlinarith [show 0 < u.val from hu.1,show u.val < 1 from hu.2,
        show r.val < s.val from hrs]

end CurveComplex.LocalSurgery
