import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14CrossesAtImageAgreement

namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 4000000

/-- Image equality transfers actual transversality, including its finite set
of crossings and the literal coordinate crossing witnesses. -/
theorem transverse_of_curve_images_eq
    {E : Type} [TopologicalSpace E] [ChartedSpace Plane E] [ClosedSurface E]
    (a b c d : Curve E) (ha : a.image = c.image) (hb : b.image = d.image)
    (ht : Transverse c d) : Transverse a b := by
  refine ⟨?_,?_⟩
  · simpa only [ha,hb] using ht.1
  · intro p hp
    apply crossesAt_of_curve_images_agree_on_open a b c d p Set.univ isOpen_univ (Set.mem_univ p)
    · intro x hx; rw [ha]
    · intro x hx; rw [hb]
    · exact ht.2 p (by simpa only [ha,hb] using hp)

end CurveComplex
