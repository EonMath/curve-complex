import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 5000000

theorem actual_arc_join_inside_embedded_disk
    {S : Type} [TopologicalSpace S] [T2Space S]
    (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d)
    (f g : C(Interval,S)) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfg : f 1=g 0) (hne : f 0≠g 1)
    (hfD : range f ⊆ range d) (hgD : range g ⊆ range d) :
    ∃ h : C(Interval,S), IsEmbedding h ∧ h 0=f 0 ∧ h 1=g 1 ∧
      range h ⊆ range f ∪ range g := by
  let lf : C(Interval,Metric.closedBall (0:Plane) 1) :=
    ⟨fun t => hd.toHomeomorph.symm ⟨f t,hfD (Set.mem_range_self t)⟩,
      hd.toHomeomorph.symm.continuous.comp (f.continuous.subtype_mk _)⟩
  let lg : C(Interval,Metric.closedBall (0:Plane) 1) :=
    ⟨fun t => hd.toHomeomorph.symm ⟨g t,hgD (Set.mem_range_self t)⟩,
      hd.toHomeomorph.symm.continuous.comp (g.continuous.subtype_mk _)⟩
  have hlf (t : Interval) : d (lf t)=f t :=
    congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply ⟨f t,hfD (Set.mem_range_self t)⟩)
  have hlg (t : Interval) : d (lg t)=g t :=
    congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply ⟨g t,hgD (Set.mem_range_self t)⟩)
  let qf : C(Interval,Plane) := ⟨fun t => (lf t).val,continuous_subtype_val.comp lf.continuous⟩
  let qg : C(Interval,Plane) := ⟨fun t => (lg t).val,continuous_subtype_val.comp lg.continuous⟩
  have hqfi : Function.Injective qf := by
    intro t s he
    exact hf.injective ((hlf t).symm.trans ((congrArg d (Subtype.ext he)).trans (hlf s)))
  have hqgi : Function.Injective qg := by
    intro t s he
    exact hg.injective ((hlg t).symm.trans ((congrArg d (Subtype.ext he)).trans (hlg s)))
  have hqf : IsEmbedding qf := (qf.continuous.isClosedEmbedding hqfi).isEmbedding
  have hqg : IsEmbedding qg := (qg.continuous.isClosedEmbedding hqgi).isEmbedding
  let Id := (Homeomorph.refl Plane).toOpenPartialHomeomorph
  have hfA : IsArcBetween (range qf) (qf 0) (qf 1) := by
    simpa [Id] using actual_chart_continuous_arc Id qf hqf (fun _ => Set.mem_univ _)
  have hgA : IsArcBetween (range qg) (qg 0) (qg 1) := by
    simpa [Id] using actual_chart_continuous_arc Id qg hqg (fun _ => Set.mem_univ _)
  have hqfg : qf 1=qg 0 := congrArg Subtype.val
    (hd.injective ((hlf 1).trans (hfg.trans (hlg 0).symm)))
  have hqne : qf 0≠qg 1 := by
    intro he
    exact hne ((hlf 0).symm.trans ((congrArg d (Subtype.ext he)).trans (hlg 1)))
  obtain ⟨A,hAS,hA⟩ := Schoenflies.exists_arc_in_union_of_arcs hfA (hqfg.symm ▸ hgA) hqne
  obtain ⟨z,hz,hzR,hz0,hz1⟩ := actual_pullback_chart_arc Id (qf 0) (qg 1)
    (Set.mem_univ _) (Set.mem_univ _) A (by simpa [Id] using hA) (fun _ _ => Set.mem_univ _)
  have hzA : range z=A := by simpa [Id] using hzR
  have hzD (t : Interval) : z t ∈ Metric.closedBall (0:Plane) 1 := by
    have htA : z t ∈ A := hzA ▸ Set.mem_range_self t
    rcases hAS htA with htF|htG
    · obtain ⟨s,hs⟩ := htF
      exact hs ▸ (lf s).property
    · obtain ⟨s,hs⟩ := htG
      exact hs ▸ (lg s).property
  let h : C(Interval,S) := ⟨fun t => d ⟨z t,hzD t⟩,
    d.continuous.comp (z.continuous.subtype_mk _)⟩
  have hi : Function.Injective h := by
    intro t s he
    exact hz.injective (congrArg Subtype.val (hd.injective he))
  refine ⟨h,(h.continuous.isClosedEmbedding hi).isEmbedding,?_,?_,?_⟩
  · have he : (⟨z 0,hzD 0⟩ : Metric.closedBall (0:Plane) 1)=lf 0 := Subtype.ext hz0
    change d ⟨z 0,hzD 0⟩=f 0
    rw [he,hlf]
  · have he : (⟨z 1,hzD 1⟩ : Metric.closedBall (0:Plane) 1)=lg 1 := Subtype.ext hz1
    change d ⟨z 1,hzD 1⟩=g 1
    rw [he,hlg]
  · rintro x ⟨t,rfl⟩
    have htA : z t ∈ A := hzA ▸ Set.mem_range_self t
    rcases hAS htA with htF|htG
    · obtain ⟨s,hs⟩ := htF
      left
      refine ⟨s,?_⟩
      have he : lf s=⟨z t,hzD t⟩ := Subtype.ext hs
      change f s=d ⟨z t,hzD t⟩
      rw [← he,hlf]
    · obtain ⟨s,hs⟩ := htG
      right
      refine ⟨s,?_⟩
      have he : lg s=⟨z t,hzD t⟩ := Subtype.ext hs
      change g s=d ⟨z t,hzD t⟩
      rw [← he,hlg]
end CurveComplex
