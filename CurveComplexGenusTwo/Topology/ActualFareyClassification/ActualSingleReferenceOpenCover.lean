import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
namespace CurveComplex
open Set
/-- An unchanged actual curve has single-reference coordinate patches inside
any prescribed open neighborhood of its whole image. -/
theorem actual_single_reference_open_cover
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace Schoenflies.Plane S] [ClosedSurface S]
    (a c : EssentialCurve S) (W : Set S) (hW : IsOpen W)
    (hcW : c.val.image ⊆ W) :
    ∃ e : c.val.image → OpenPartialHomeomorph S Schoenflies.Plane,
      (∀ p, p.val ∈ (e p).source) ∧
      (∀ p, (e p).source ⊆ W) ∧
      (∀ p, ∃ i : Option Unit, ∀ j : Unit, ∀ x, x ∈ (e p).source →
        (x ∈ a.val.image ↔ i = some j ∧ e p x 0 = 0)) := by
  classical
  let L : Schoenflies.Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let flip : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
  have hflip (z : Schoenflies.Plane) : flip z 0 = z 1 := rfl
  have hlocal (p : c.val.image) :
      ∃ E : OpenPartialHomeomorph S Schoenflies.Plane,
        p.val ∈ E.source ∧ E.source ⊆ W ∧
        ∃ i : Option Unit, ∀ j : Unit, ∀ x, x ∈ E.source →
          (x ∈ a.val.image ↔ i = some j ∧ E x 0 = 0) := by
    by_cases hp : p.val ∈ a.val.image
    · obtain ⟨E0,hp0,_,hsub,_,hflat⟩ :=
        PositionUniverseV2.position_curve_crosscut_chart S a.val p.val hp W hW
          (hcW p.property)
      let E := E0.trans flip.toOpenPartialHomeomorph
      have hs : E.source = E0.source := by
        ext x; simp [E,OpenPartialHomeomorph.trans_source]
      refine ⟨E,hs.symm ▸ hp0,fun _ hx => hsub (hs ▸ hx),some (),?_⟩
      intro j x hx
      have hcoord : E x 0 = E0 x 1 := hflip (E0 x)
      cases j
      simpa only [Option.some.injEq,eq_self,true_and,hcoord] using hflat x (hs ▸ hx)
    · have ho : IsOpen (W ∩ a.val.imageᶜ) := hW.inter
        (isCompact_range a.val.embedded.continuous).isClosed.isOpen_compl
      let E0 := chartAt Schoenflies.Plane p.val
      let E := E0.restr (W ∩ a.val.imageᶜ)
      have hs : E.source = E0.source ∩ (W ∩ a.val.imageᶜ) := by
        rw [OpenPartialHomeomorph.restr_source,ho.interior_eq]
      refine ⟨E,hs.symm ▸ ⟨mem_chart_source _ _,hcW p.property,hp⟩,
        fun _ hx => (hs.le hx).2.1,none,?_⟩
      intro j x hx
      constructor
      · intro ha
        exact False.elim ((hs.le hx).2.2 ha)
      · rintro ⟨h,_⟩; cases h
  choose e hp hsub hi using hlocal
  exact ⟨e,hp,hsub,hi⟩
end CurveComplex
