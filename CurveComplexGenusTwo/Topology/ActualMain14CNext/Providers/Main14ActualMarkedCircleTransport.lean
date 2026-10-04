import CurveComplexGenusTwo.Topology.IntersectionParity.HomeomorphTransport
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Dictionary.ActualCircle24Components

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 4000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]

/-- An actual homeomorphism fixing the given marks transports an actual
punctured circle, preserving its literal image and all marked side counts. -/
theorem actual_marked_homeomorph_circle_transport
    (M : HyperellipticModel E S) (c : PuncturedCircle M) (e : S ≃ₜ S)
    (hfix : ∀ x ∈ M.cover.branch, e x = x) :
    ∃ c' : PuncturedCircle M, c'.image = e '' c.image ∧
      ∀ m n, SplitsMarked M c m n → SplitsMarked M c' m n := by
  classical
  let curve := LocalSurgery.homeomorphCurve e c.curve
  have hi : curve.image = e '' c.image := by
    change Set.range (e ∘ c.curve.map) = e '' Set.range c.curve.map
    exact Set.range_comp _ _
  have hfree : Disjoint curve.image (M.cover.branch : Set S) := by
    rw [hi]
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,he⟩ hx
    have hyx : y = x := e.injective (he.trans (hfix x hx).symm)
    exact Set.disjoint_left.mp c.avoids_branch (hyx ▸ hy) hx
  let c' : PuncturedCircle M := ⟨curve,hfree⟩
  refine ⟨c',hi,?_⟩
  intro m n hs
  obtain ⟨U,V,hU,hV,hUc,hVc,hUne,hVne,hUV,hcompl,hcountU,hcountV⟩ := hs
  have hmem (W : Set S) (x : S) (hx : x ∈ M.cover.branch) : x ∈ e '' W ↔ x ∈ W := by
    constructor
    · rintro ⟨y,hy,he⟩
      have hyx : y = x := e.injective (he.trans (hfix x hx).symm)
      exact hyx ▸ hy
    · intro hw; exact ⟨x,hw,hfix x hx⟩
  have hfilter (W : Set S) :
      M.cover.branch.filter (· ∈ e '' W) = M.cover.branch.filter (· ∈ W) := by
    apply Finset.filter_congr
    intro x hx
    exact hmem W x hx
  refine ⟨e '' U,e '' V,e.isOpenMap U hU,e.isOpenMap V hV,
    (e.isConnected_image).mpr hUc,(e.isConnected_image).mpr hVc,
    hUne.image e,hVne.image e,?_,?_,?_,?_⟩
  · exact (Set.disjoint_image_iff e.injective).mpr hUV
  · rw [← Set.image_union,hcompl,e.image_compl]
    exact congrArg Set.compl hi.symm
  · rw [hfilter]; exact hcountU
  · rw [hfilter]; exact hcountV

end CurveComplex.HyperellipticModel
