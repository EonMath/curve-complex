import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior

open Set Topology
open scoped Manifold

namespace CurveComplex.LocalSurgery

/-- An embedded surface disk has exactly its parametrized open ball as ambient
interior. This ensures a nested subdisk cannot hide an old boundary corner in
its interior. -/
theorem embedded_surface_disk_interior_eq
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) :
    interior (Set.range d) =
      d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
  classical
  let Plane := EuclideanSpace ℝ (Fin 2)
  let K := Set.range d
  let U := interior K
  let inv : S → Plane := fun y => if hy : y ∈ K then
    (hd.toHomeomorph.symm ⟨y, hy⟩).val else 0
  have hinv (x : Metric.closedBall (0 : Plane) 1) : inv (d x) = x.val := by
    simp only [inv, dif_pos (show d x ∈ K from ⟨x, rfl⟩)]
    exact congrArg Subtype.val (hd.toHomeomorph.symm_apply_apply x)
  have hcont : ContinuousOn inv K := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hc := continuous_subtype_val.comp hd.toHomeomorph.symm.continuous
    exact hc.congr fun x => by simp [inv, x.property]
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := interior_subset hy
    let E := chartAt Plane (d x)
    let Ω := E.target ∩ E.symm ⁻¹' U
    have hΩ : IsOpen Ω := E.symm.continuousOn.isOpen_inter_preimage E.open_target isOpen_interior
    have hxΩ : E (d x) ∈ Ω := ⟨E.map_source (mem_chart_source Plane (d x)), by
      change E.symm (E (d x)) ∈ U
      rwa [E.left_inv (mem_chart_source Plane (d x))]⟩
    let f := inv ∘ E.symm
    have hf : ContinuousOn f Ω := hcont.comp
      (E.symm.continuousOn.mono inter_subset_left) (fun z hz => interior_subset hz.2)
    have hfi : Set.InjOn f Ω := by
      intro z hz w hw he
      obtain ⟨v, hv⟩ := interior_subset hz.2
      obtain ⟨u, hu⟩ := interior_subset hw.2
      change inv (E.symm z) = inv (E.symm w) at he
      rw [← hv, ← hu, hinv, hinv] at he
      have hsame : E.symm z = E.symm w := by rw [← hv, ← hu, Subtype.ext he]
      exact E.symm.injOn hz.1 hw.1 hsame
    have hopen : IsOpen (f '' Ω) :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
        f Ω hΩ hf hfi
    have hsub : f '' Ω ⊆ Metric.closedBall (0 : Plane) 1 := by
      rintro z ⟨w, hw, rfl⟩
      obtain ⟨v, hv⟩ := interior_subset hw.2
      change inv (E.symm w) ∈ Metric.closedBall (0 : Plane) 1
      rw [← hv, hinv]
      exact v.property
    have hximage : x.val ∈ f '' Ω := by
      refine ⟨E (d x), hxΩ, ?_⟩
      change inv (E.symm (E (d x))) = x.val
      rw [E.left_inv (mem_chart_source Plane (d x)), hinv]
    have hxball : x.val ∈ Metric.ball (0 : Plane) 1 := by
      rw [← interior_closedBall (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
      exact (hopen.subset_interior_iff.mpr hsub) hximage
    exact ⟨x, hxball, rfl⟩
  · apply (embedded_surface_disk_interior_isOpen d hd).subset_interior_iff.mpr
    exact Set.image_subset_range _ _

end CurveComplex.LocalSurgery
