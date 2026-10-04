import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import ClassificationOfSurfaces.Topology.InvarianceOfDomain

open Set Topology
open scoped Manifold

namespace CurveComplex.LocalSurgery

/-- Invariance of domain for the actual open part of an embedded surface disk. -/
theorem embedded_surface_disk_interior_isOpen
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, S))
    (hd : Topology.IsEmbedding d) :
    IsOpen (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
  classical
  let Plane := EuclideanSpace ℝ (Fin 2)
  let B : Set Plane := Metric.ball 0 1
  let D : Set (Metric.closedBall (0 : Plane) 1) := {x | x.val ∈ B}
  let f : Plane → S := fun x => if hx : x ∈ Metric.closedBall 0 1 then d ⟨x, hx⟩ else d ⟨0, by simp⟩
  have hf_eq (x : Plane) (hx : x ∈ B) : f x = d ⟨x, Metric.ball_subset_closedBall hx⟩ := by
    dsimp [f]
    rw [dite_eq_left (Metric.ball_subset_closedBall hx)]
  have hfcont : ContinuousOn f B := by
    apply continuousOn_iff_continuous_restrict.mpr
    let j : B → Metric.closedBall (0 : Plane) 1 := fun x => ⟨x, Metric.ball_subset_closedBall x.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    exact (d.continuous.comp hj).congr fun x => (hf_eq x x.property).symm
  have hfinj : Set.InjOn f B := by
    intro x hx y hy heq
    have heq' : d ⟨x, Metric.ball_subset_closedBall hx⟩ = d ⟨y, Metric.ball_subset_closedBall hy⟩ := by
      rwa [hf_eq x hx, hf_eq y hy] at heq
    exact congrArg Subtype.val (hd.injective heq')
  have hwhole : f '' B = d '' D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, Metric.ball_subset_closedBall hx⟩, hx, (hf_eq x hx).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.val, hu, hf_eq u hu⟩
  change IsOpen (d '' D)
  rw [← hwhole]
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  let E := chartAt Plane (f x)
  have hxE : f x ∈ E.source := mem_chart_source Plane (f x)
  let Ω := B ∩ f ⁻¹' E.source
  have hΩopen : IsOpen Ω := hfcont.isOpen_inter_preimage Metric.isOpen_ball E.open_source
  have hxΩ : x ∈ Ω := ⟨hx, hxE⟩
  let g := E ∘ f
  have hgcont : ContinuousOn g Ω := E.continuousOn.comp (hfcont.mono inter_subset_left) (fun _ ht => ht.2)
  have hginj : Set.InjOn g Ω := by
    intro z hz w hw heq
    exact hfinj hz.1 hw.1 (E.injOn hz.2 hw.2 heq)
  have hopen : IsOpen (g '' Ω) :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      g Ω hΩopen hgcont hginj
  have hgsub : g '' Ω ⊆ E.target := by
    rintro z ⟨w, hw, rfl⟩
    exact E.map_source hw.2
  have hbackOpen : IsOpen (E.symm '' (g '' Ω)) :=
    E.symm.isOpen_image_of_subset_source hopen hgsub
  have heq : E.symm '' (g '' Ω) = f '' Ω := by
    ext z
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, (E.left_inv hv.2).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g v, Set.mem_image_of_mem g hv, E.left_inv hv.2⟩
  rw [heq] at hbackOpen
  exact Filter.mem_of_superset (hbackOpen.mem_nhds ⟨x, hxΩ, rfl⟩) (Set.image_mono inter_subset_left)

end CurveComplex.LocalSurgery
