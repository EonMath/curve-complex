import CurveComplexGenusTwo.Hyperbolic.OriginalG1.H2LocalUnitGeodesicPROVED
import Mathlib.Topology.Homotopy.Lifting
namespace CurveComplex.Hyperbolic
open Set
set_option maxHeartbeats 1000000
theorem actual_developed_geodesic_preimage_is_union_complete_lines {E : Type} [MetricSpace E] (p : H2 → E) (hp : IsCoveringMap p)
    (hmetric : ∀ x : H2, ∃ U : Set H2, IsOpen U ∧ x∈U ∧
      ∀ y∈U,∀ z∈U,dist (p y) (p z)=dist y z)
    (γ : C(ℝ,E))
    (hunit : ∀ t : ℝ, ∃ ε : ℝ,0<ε ∧ ∀ s v : ℝ,
      |s-t|<ε → |v-t|<ε → dist (γ s) (γ v)=|s-v|) :
    ∃ a : {x : H2 // p x∈Set.range γ} → ℝ → H2,
      (∀ x,Isometry (a x)) ∧
      p ⁻¹' Set.range γ = ⋃ x,Set.range (a x) := by
  classical
  let F := {x : H2 // p x∈Set.range γ}
  have hlift (x : F) : ∃ δ : C(ℝ,H2), Isometry δ ∧
      p ∘ δ=γ ∧ x.val∈Set.range δ := by
    obtain ⟨t,ht⟩ := x.property
    obtain ⟨δ,⟨hδt,hδp⟩,_⟩ := hp.existsUnique_continuousMap_lifts γ t x.val ht.symm
    have hprojection (u : ℝ) : p (δ u)=γ u := congrFun hδp u
    have hlocal (u : ℝ) : ∃ ε : ℝ,0<ε ∧ ∀ s v : ℝ,
        |s-u|<ε → |v-u|<ε → dist (δ s) (δ v)=|s-v| := by
      obtain ⟨ε₀,hε₀,hu⟩ := hunit u
      obtain ⟨U,hU,hδU,hm⟩ := hmetric (δ u)
      obtain ⟨ε₁,hε₁,hball⟩ := Metric.isOpen_iff.mp
        (hU.preimage δ.continuous) u hδU
      refine ⟨min ε₀ ε₁,lt_min hε₀ hε₁,?_⟩
      intro s v hs hv
      have hsU : δ s∈U := hball (by
        simpa only [Metric.mem_ball,Real.dist_eq] using hs.trans_le (min_le_right _ _))
      have hvU : δ v∈U := hball (by
        simpa only [Metric.mem_ball,Real.dist_eq] using hv.trans_le (min_le_right _ _))
      rw [←hm (δ s) hsU (δ v) hvU,hprojection s,hprojection v]
      exact hu s v (hs.trans_le (min_le_left _ _)) (hv.trans_le (min_le_left _ _))
    exact ⟨δ,actual_h2_local_unit_geodesic_isometry δ δ.continuous hlocal,hδp,⟨t,hδt⟩⟩
  choose δ hδiso hδproj hδrange using hlift
  refine ⟨fun x => δ x,hδiso,?_⟩
  ext z
  constructor
  · intro hz
    exact Set.mem_iUnion.mpr ⟨⟨z,hz⟩,hδrange ⟨z,hz⟩⟩
  · intro hz
    obtain ⟨x,t,rfl⟩ := Set.mem_iUnion.mp hz
    exact ⟨t,congrFun (hδproj x) t|>.symm⟩
end CurveComplex.Hyperbolic
