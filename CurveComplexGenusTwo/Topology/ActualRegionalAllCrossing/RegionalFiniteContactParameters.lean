import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalPlanarCover

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

theorem regional_finite_contact_parameters
    {S : Type} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a)
    (hfinite : (Set.range a ∩ Set.range b).Finite) :
    {s : Interval | a s ∈ Set.range b}.Finite := by
  let T : Set Interval := {s | a s ∈ Set.range a ∩ Set.range b}
  have hT : T.Finite := hfinite.of_injOn
    (show Set.MapsTo a T (Set.range a ∩ Set.range b) from
      fun s hs => hs)
    (fun s _ t _ heq => ha.injective heq)
  convert hT using 1
  ext s
  simp [T]

end RegionalEmbeddedFamily
