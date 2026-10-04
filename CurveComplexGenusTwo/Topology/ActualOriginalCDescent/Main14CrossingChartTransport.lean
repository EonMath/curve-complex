import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14SingleCrossing
import CurveComplexGenusTwo.Intersection.SphereChart

open Set Topology

namespace CurveComplex

/-- Pull actual axis charts back through an open embedding. -/
theorem crossesAt_of_openEmbedding
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X → Y) (he : IsOpenEmbedding e)
    (a b : Curve X) (c d : Curve Y)
    (ha : c.image = e '' a.image) (hb : d.image = e '' b.image)
    (p : X) (hp : CrossesAt c d (e p)) : CrossesAt a b p := by
  obtain ⟨U,V,hpU,h,hU,hV,hzero,haxes⟩ := hp
  let U' := e ⁻¹' U
  let j : U' → U := U.restrictPreimage e
  let f : U' → ℝ × ℝ := fun z => (h (j z)).val
  have hf : IsOpenEmbedding f :=
    hV.isOpenEmbedding_subtypeVal.comp (h.isOpenEmbedding.comp (he.restrictPreimage U))
  let k := hf.isEmbedding.toHomeomorph
  refine ⟨U',Set.range f,hpU,k,hU.preimage he.continuous,hf.isOpen_range,?_,?_⟩
  · exact hzero
  · intro x hx
    have ha' : x ∈ a.image ↔ e x ∈ c.image := by
      rw [ha]
      constructor
      · intro hx; exact ⟨x,hx,rfl⟩
      · rintro ⟨z,hz,hzx⟩; exact he.injective hzx ▸ hz
    have hb' : x ∈ b.image ↔ e x ∈ d.image := by
      rw [hb]
      constructor
      · intro hx; exact ⟨x,hx,rfl⟩
      · rintro ⟨z,hz,hzx⟩; exact he.injective hzx ▸ hz
    exact ⟨ha'.trans (haxes (e x) hx).1,hb'.trans (haxes (e x) hx).2⟩

end CurveComplex
