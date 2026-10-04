import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorPrefixTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePositions

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
variable (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
  (G : AmbientIsotopy S)
  (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
  (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)

/-- Outermost selected class and remaining order are transported by the actual
derived anchor order isomorphism; no new choice of a first crossing is assumed. -/
def transportFirstCrossing (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P) (t : Interval) :
    FirstCrossing M anchor F (timePosition M anchor F P G hm ha t) where
  selected := x.selected
  t := anchorParameterOrderIso M anchor G hm ha t x.t
  s := x.s
  t_interior := by
    let e := anchorParameterOrderIso M anchor G hm ha t
    have he0 : e 0 = 0 := closedAnchorParameterMove_zero M anchor G hm ha t
    have he1 : e 1 = 1 := closedAnchorParameterMove_one M anchor G hm ha t
    have h0 := e.strictMono (show (0 : Interval) < x.t from x.t_interior.1)
    have h1 := e.strictMono (show x.t < (1 : Interval) from x.t_interior.2)
    rw [he0] at h0
    rw [he1] at h1
    exact ⟨h0,h1⟩
  s_interior := x.s_interior
  same_point := by
    rw [anchorParameterOrderIso_map,x.same_point]
    exact (timeTransport_map M G hm t (P.rep x.selected) x.s).symm
  first := by
    intro v r hr0 hrt hr
    let e := anchorParameterOrderIso M anchor G hm ha t
    let u := e.symm r
    have he0 : e 0 = 0 := closedAnchorParameterMove_zero M anchor G hm ha t
    change (0 : Interval) < r at hr0
    change r < e x.t at hrt
    have hu0 : 0 < u.val := by
      change (0 : Interval) < e.symm r
      apply e.lt_iff_lt.mp
      simpa only [he0,OrderIso.apply_symm_apply] using hr0
    have hut : u.val < x.t.val := by
      change e.symm r < x.t
      exact e.lt_iff_lt.mp (by simpa only [OrderIso.apply_symm_apply] using hrt)
    have hcross : G.map (t,anchor.val.map u) ∈
        arcInterior M (timeTransport M G hm t (P.rep v)) := by
      rw [← anchorParameterOrderIso_map]
      change anchor.val.map (e (e.symm r)) ∈ _
      rw [e.apply_symm_apply]
      exact hr
    unfold timeTransport at hcross
    rw [arcInterior_transport] at hcross
    obtain ⟨q,hq,hqeq⟩ := hcross
    have hp : q = anchor.val.map u :=
      (timeHomeomorph G t).injective
        (hqeq.trans (timeHomeomorph_apply G t (anchor.val.map u)).symm)
    exact x.first v u hu0 hut (hp ▸ hq)

/-- All anchor crossing coordinates in the actual new system have an exact
order-preserving correspondence with old coordinates. -/
def transportAnchorCrossingParameter (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (v : {v // v ∈ F}) (t : Interval)
    (r : AnchorCrossingParameter M anchor (P.rep v)) :
    AnchorCrossingParameter M anchor ((timePosition M anchor F P G hm ha t).rep v) := by
  let e := anchorParameterOrderIso M anchor G hm ha t
  have he0 : e 0 = 0 := closedAnchorParameterMove_zero M anchor G hm ha t
  have he1 : e 1 = 1 := closedAnchorParameterMove_one M anchor G hm ha t
  refine ⟨e r.val,?_,?_,?_⟩
  · change (0 : Interval) < e r.val
    rw [← he0]
    exact e.strictMono r.property.1
  · change e r.val < (1 : Interval)
    rw [← he1]
    exact e.strictMono r.property.2.1
  · change anchor.val.map (e r.val) ∈ arcInterior M (timeTransport M G hm t (P.rep v))
    rw [anchorParameterOrderIso_map]
    unfold timeTransport
    rw [arcInterior_transport]
    exact ⟨anchor.val.map r.val,r.property.2.2,timeHomeomorph_apply G t _⟩

theorem transported_crossing_order (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (v w : {v // v ∈ F}) (t : Interval)
    (r : AnchorCrossingParameter M anchor (P.rep v))
    (s : AnchorCrossingParameter M anchor (P.rep w)) :
    (transportAnchorCrossingParameter M anchor G hm ha F P v t r).val.val <
      (transportAnchorCrossingParameter M anchor G hm ha F P w t s).val.val ↔ r.val.val < s.val.val :=
  (anchorParameterOrderIso M anchor G hm ha t).lt_iff_lt

end
end CurveComplex.HyperellipticModel.ArcSurgery
