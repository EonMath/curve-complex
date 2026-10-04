import CurveComplexGenusTwo.Dictionary.CircleVertexAPI
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualMarkedCircleTransport
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleParallel

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- The actual original 3|3 circle has a genuine disjoint marked-isotopic
parallel 3|3 circle, with actual isotopic disjoint full preimages upstairs. -/
theorem circle33_actual_disjoint_parallel
    (M : HyperellipticModel E S) (c : Circle33 M) :
    ∃ d : Circle33 M,
      MarkedIsotopyRel M c.val.image d.val.image ∧
      Disjoint d.val.image c.val.image ∧
      AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
        (M.cover.projection ⁻¹' d.val.image) ∧
      Disjoint (M.cover.projection ⁻¹' d.val.image) (M.cover.projection ⁻¹' c.val.image) := by
  obtain ⟨H,hfix,hdisjoint⟩ := M.actual_marked_punctured_circle_parallel_isotopy c.val
  obtain ⟨d,hi,hiso⟩ := M.actual_marked_isotopy_circle33_transport c H hfix
  have hd : Disjoint d.val.image c.val.image := by rw [hi]; exact hdisjoint
  refine ⟨d,hiso,hd,M.marked_isotopy_preimage hiso,?_⟩
  exact hd.preimage M.cover.projection

/-- For the original arbitrary upstairs isotopy to a circle33 full preimage,
construct an actual zero-crossing representative with the reference curve
literally fixed. The zero count is a conclusion, never a supplied certificate. -/
theorem circle33_actual_isotopic_zero_comparison
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c : Circle33 M)
    (hb : b.val.image = M.cover.projection ⁻¹' c.val.image)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image) :
    ∃ a' : EssentialCurve E,
      AmbientIsotopy.Rel a.val.image a'.val.image ∧
      ∃ ht' : Transverse a'.val b.val, ht'.1.toFinset.card = 0 := by
  classical
  obtain ⟨d,hdown,hd,hup,hdisjoint⟩ := M.circle33_actual_disjoint_parallel c
  let a' := M.circle33_essential_preimage d
  have ha' : a'.val.image = M.cover.projection ⁻¹' d.val.image := M.circle33_essential_preimage_image d
  have hi : AmbientIsotopy.Rel a.val.image a'.val.image := by
    rw [ha']
    exact ambientIsotopy_equivalence.trans hiso (hb.symm ▸ hup)
  have hdisjoint' : Disjoint a'.val.image b.val.image := by rw [ha',hb]; exact hdisjoint
  have he : a'.val.image ∩ b.val.image = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisjoint'
  have ht' : Transverse a'.val b.val := by
    refine ⟨?_,?_⟩
    · rw [he]; exact Set.finite_empty
    · intro p hp; rw [he] at hp; exact False.elim hp
  refine ⟨a',hi,ht',?_⟩
  rw [← Set.ncard_eq_toFinset_card _ ht'.1,he,Set.ncard_empty]
end CurveComplex.HyperellipticModel
