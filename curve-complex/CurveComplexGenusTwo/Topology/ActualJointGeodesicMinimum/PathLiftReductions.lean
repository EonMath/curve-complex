import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import Mathlib.Topology.Homotopy.Lifting

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology

theorem homotopic_paths_have_common_endpoint_lifts
    {E : Type} [TopologicalSpace E] (u v : E) (f g : Path u v)
    (hhom : f.Homotopic g)
    (p : H2 → connectedComponent u) (hp : IsCoveringMap p)
    (hpsurj : Function.Surjective p) :
    ∃ F G : C(Interval, H2),
      (∀ t, (p (F t)).val = f t) ∧
      (∀ t, (p (G t)).val = g t) ∧
      F 0 = G 0 ∧ F 1 = G 1 := by
  classical
  have hfcomponent (t : Interval) : f t ∈ connectedComponent u :=
    (isConnected_range f.continuous).isPreconnected.subset_connectedComponent
      ⟨0, f.source⟩ ⟨t, rfl⟩
  have hgcomponent (t : Interval) : g t ∈ connectedComponent u :=
    (isConnected_range g.continuous).isPreconnected.subset_connectedComponent
      ⟨0, g.source⟩ ⟨t, rfl⟩
  let fc : C(Interval, connectedComponent u) :=
    ⟨fun t => ⟨f t, hfcomponent t⟩, f.continuous.subtype_mk _⟩
  let gc : C(Interval, connectedComponent u) :=
    ⟨fun t => ⟨g t, hgcomponent t⟩, g.continuous.subtype_mk _⟩
  obtain ⟨hom⟩ := hhom
  have hcomponent (z : Interval × Interval) : hom z ∈ connectedComponent u :=
    (isConnected_range hom.continuous).isPreconnected.subset_connectedComponent
      ⟨(0, 0), (hom.apply_zero 0).trans f.source⟩ ⟨z, rfl⟩
  let homc : fc.HomotopyRel gc {0, 1} := {
    toContinuousMap :=
      ⟨fun z => ⟨hom z, hcomponent z⟩, hom.continuous.subtype_mk _⟩
    map_zero_left := fun t => Subtype.ext (hom.apply_zero t)
    map_one_left := fun t => Subtype.ext (hom.apply_one t)
    prop' := fun t z hz => Subtype.ext (hom.prop t z hz) }
  obtain ⟨x, hx⟩ := hpsurj ⟨u, mem_connectedComponent⟩
  have hfc0 : fc 0 = p x := by rw [hx]; exact Subtype.ext f.source
  have hgc0 : gc 0 = p x := by rw [hx]; exact Subtype.ext g.source
  let F := hp.liftPath fc x hfc0
  let G := hp.liftPath gc x hgc0
  refine ⟨F, G, ?_, ?_, ?_, ?_⟩
  · intro t
    exact congrArg Subtype.val (congrFun (hp.liftPath_lifts fc x hfc0) t)
  · intro t
    exact congrArg Subtype.val (congrFun (hp.liftPath_lifts gc x hgc0) t)
  · exact (hp.liftPath_zero fc x hfc0).trans (hp.liftPath_zero gc x hgc0).symm
  · exact hp.liftPath_apply_one_eq_of_homotopicRel ⟨homc⟩ x hfc0 hgc0

end CurveComplex.Hyperbolic.JointMinimum
