import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Analysis.Convex.Contractible

open Set Topology
namespace CurveComplex.LocalSurgery

/-- Actual small contractible chart neighborhoods inside any prescribed open set. -/
theorem charted_surface_contractible_neighborhood
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (W : Set S) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ U : Set S, x ∈ U ∧ IsOpen U ∧ U ⊆ W ∧ ContractibleSpace U := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let Z := e.target ∩ e.symm ⁻¹' W
  have hZ : IsOpen Z := e.isOpen_inter_preimage_symm hW
  have hex : e x ∈ Z := ⟨e.map_source (mem_chart_source _ x), by
    change e.symm (e x) ∈ W
    rwa [e.left_inv (mem_chart_source _ x)]⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hZ (e x) hex
  let U := e.symm '' Metric.ball (e x) r
  have hsub : Metric.ball (e x) r ⊆ e.symm.source := fun _ hy => (hball hy).1
  have hU : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub
  have hxU : x ∈ U := ⟨e x,Metric.mem_ball_self hr,e.left_inv (mem_chart_source _ x)⟩
  have hUW : U ⊆ W := by
    rintro y ⟨z,hz,rfl⟩
    exact (hball hz).2
  letI : ContractibleSpace (Metric.ball (e x) r) := Metric.contractibleSpace_ball hr
  let f : Metric.ball (e x) r ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hsub rfl
  exact ⟨U,hxU,hU,hUW,f.symm.contractibleSpace⟩

/-- Local topology required for the path-homotopy universal-cover construction. -/
theorem charted_surface_strongly_locally_contractible
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    StronglyLocallyContractibleSpace S := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_self]
  intro t ht
  obtain ⟨W,hWt,hW,hxW⟩ := mem_nhds_iff.mp ht
  obtain ⟨U,hxU,hU,hUW,hcontr⟩ :=
    charted_surface_contractible_neighborhood x W hW hxW
  exact ⟨U,hU.mem_nhds hxU,hcontr,hUW.trans hWt⟩

end CurveComplex.LocalSurgery
