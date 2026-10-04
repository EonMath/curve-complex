import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.GeometricPosition.OneCurveExtensionStatement
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- The actual moving punctured circle has a cover by mark-free patches
containing either no fixed circle or its literal coordinate axis. Only one
fixed circle is involved, so no generic essential-family position is assumed. -/
theorem actual_marked_two_circle_prepared_cover [ChartedSpace Plane S] [ClosedSurface S]
    (M : HyperellipticModel E S) (c d : PuncturedCircle M) :
    ∃ e : d.image → OpenPartialHomeomorph S Plane,
      (∀ p, p.val ∈ (e p).source) ∧
      (∀ p, (e p).source ⊆ (M.cover.branch : Set S)ᶜ) ∧
      (∀ p, ∃ i : Option Unit, ∀ j : Unit, ∀ x ∈ (e p).source,
        x ∈ c.image ↔ i = some j ∧ e p x 0 = 0) := by
  classical
  have hbranch : IsOpen (M.cover.branch : Set S)ᶜ := M.cover.branch.finite_toSet.isClosed.isOpen_compl
  have hclosed : IsClosed c.image := (isCompact_range c.curve.embedded.continuous).isClosed
  let L : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let flip : Plane ≃ₜ Plane := (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
  have hflip (z : Plane) : flip z 0 = z 1 := rfl
  have hlocal (p : d.image) : ∃ F : OpenPartialHomeomorph S Plane,
      p.val ∈ F.source ∧ F.source ⊆ (M.cover.branch : Set S)ᶜ ∧
      ∃ i : Option Unit, ∀ j : Unit, ∀ x ∈ F.source,
        x ∈ c.image ↔ i = some j ∧ F x 0 = 0 := by
    have hpbranch : p.val ∈ (M.cover.branch : Set S)ᶜ :=
      fun h => Set.disjoint_left.mp d.avoids_branch p.property h
    by_cases hp : p.val ∈ c.image
    · obtain ⟨F,hpF,hF0,hsub,hsq,hflat⟩ := PositionUniverseV2.position_curve_crosscut_chart
        S c.curve p.val hp (M.cover.branch : Set S)ᶜ hbranch hpbranch
      let G := F.trans flip.toOpenPartialHomeomorph
      have hs : G.source = F.source := by ext x; simp [G,OpenPartialHomeomorph.trans_source]
      refine ⟨G,hs.symm ▸ hpF,hs ▸ hsub,some (),?_⟩
      intro j x hx
      cases j
      have hcoord : G x 0 = F x 1 := hflip _
      simpa only [PuncturedCircle.image,hcoord,eq_self,true_and] using hflat x (hs ▸ hx)
    · let W := c.imageᶜ ∩ (M.cover.branch : Set S)ᶜ
      have hW : IsOpen W := hclosed.isOpen_compl.inter hbranch
      let F := (chartAt Plane p.val).restr W
      have hs : F.source = (chartAt Plane p.val).source ∩ W := by
        rw [OpenPartialHomeomorph.restr_source,hW.interior_eq]
      refine ⟨F,hs.symm ▸ ⟨mem_chart_source _ _,hp,hpbranch⟩,
        fun x hx => (hs ▸ hx).2.2,none,?_⟩
      intro j x hx
      constructor
      · intro hc; exact False.elim ((hs ▸ hx).2.1 hc)
      · rintro ⟨h,_⟩; cases h
  choose e hp hfree hi using hlocal
  exact ⟨e,hp,hfree,hi⟩
end CurveComplex.HyperellipticModel
