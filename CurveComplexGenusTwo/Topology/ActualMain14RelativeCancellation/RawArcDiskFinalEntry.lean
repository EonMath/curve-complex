import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcDiskCrosscut

namespace CurveComplex.LocalSurgery
open Set Topology
variable {S : Type} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]

/-- The actual last entry of an escaping embedded arc whose final endpoint is
inside an embedded disk. The resulting entire terminal segment lies in the
closed disk, and only its initial point is on the boundary. -/
theorem raw_embedded_arc_final_entry_segment
    (g : C(Interval,S)) (hg : IsEmbedding g)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d)
    (h1 : g 1 ∈ d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
    (hout : ∃ t : Interval, g t ∉ Set.range d) :
    ∃ r : Interval, r < 1 ∧
      g r ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
      (∀ v : Interval, r < v → g v ∈
        d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) ∧
      ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ range g ∧
        range q ⊆ range d ∧ q 0 = g r ∧ q 1 = g 1 ∧
        q '' Ioc (0:Interval) 1 ⊆
          d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  classical
  let U : Set S := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  let K : Set S := range d
  have hUo : IsOpen U := embedded_surface_disk_interior_isOpen d hd
  have hKc : IsClosed K := (isCompact_range d.continuous).isClosed
  have hUK : U ⊆ K := image_subset_range _ _
  obtain ⟨t,ht⟩ := hout
  have hpre : IsClosed (g ⁻¹' Uᶜ) := hUo.isClosed_compl.preimage g.continuous
  obtain ⟨r,hr,hrmax⟩ := hpre.isCompact.exists_isGreatest
    (show (g ⁻¹' Uᶜ).Nonempty from ⟨t,fun htU => ht (hUK htU)⟩)
  have hr1 : r < 1 := lt_of_le_of_ne r.property.2
    (by intro he; exact hr (he ▸ h1))
  have hinside (v : Interval) (hv : r < v) : g v ∈ U := by
    by_contra hnot
    exact (not_lt_of_ge (hrmax hnot)) hv
  have hIccK : Icc r 1 ⊆ g ⁻¹' K := by
    rw [← closure_Ioo hr1.ne]
    apply (hKc.preimage g.continuous).closure_subset_iff.mpr
    exact fun v hv => hUK (hinside v hv.1)
  have hboundary : g r ∈ d ''
      {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    obtain ⟨u,hu⟩ := hIccK ⟨le_rfl,hr1.le⟩
    refine ⟨u,?_,hu⟩
    have hn : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hnot : ¬ ‖u.val‖ < 1 := by
      intro h
      exact hr ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using h,hu⟩
    simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
      using le_antisymm hn (le_of_not_gt hnot)
  let affine : Interval → Interval := fun u =>
    ⟨(1-u.val)*r.val+u.val,by
      constructor <;> nlinarith [u.property.1,u.property.2,r.property.1,r.property.2]⟩
  have haff (u : Interval) : affine u ∈ Icc r 1 := by
    constructor
    · change r.val ≤ (1-u.val)*r.val+u.val
      nlinarith [u.property.1,u.property.2,show r.val < 1 from hr1]
    · exact (affine u).property.2
  have haffi : Function.Injective affine := by
    intro u v he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    dsimp [affine] at he'
    have hz : (u.val-v.val)*(1-r.val)=0 := by nlinarith only [he']
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · nlinarith [show r.val < 1 from hr1]
  let q : C(Interval,S) := ⟨g ∘ affine,g.continuous.comp (by fun_prop)⟩
  refine ⟨r,hr1,hboundary,hinside,q,
    (q.continuous.isClosedEmbedding (hg.injective.comp haffi)).isEmbedding,?_,?_,?_,?_,?_⟩
  · rintro z ⟨u,rfl⟩
    exact mem_range_self (affine u)
  · rintro z ⟨u,rfl⟩
    exact hIccK (haff u)
  · exact congrArg g (Subtype.ext (by simp [affine]))
  · exact congrArg g (Subtype.ext (by simp [affine]))
  · rintro z ⟨u,hu,rfl⟩
    apply hinside
    change r.val < (1-u.val)*r.val+u.val
    nlinarith [show 0 < u.val from hu.1,show r.val < 1 from hr1]

end CurveComplex.LocalSurgery
