import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualRelativeCrossingSlide

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

abbrev UnitBox := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
def doublePlaneCoordinates : (ℝ × ℝ) ≃ₜ Plane :=
  planeCoordinates.symm.trans (Homeomorph.smul (Units.mk0 (2 : ℝ) (by norm_num)))

theorem doublePlaneCoordinates_apply (q : ℝ × ℝ) :
    doublePlaneCoordinates q = (2 : ℝ) • planeCoordinates.symm q := rfl

theorem doublePlaneCoordinates_first (q : ℝ × ℝ) :
    doublePlaneCoordinates q 0 = 2*q.1 := rfl

theorem doublePlaneCoordinates_second (q : ℝ × ℝ) :
    doublePlaneCoordinates q 1 = 2*q.2 := rfl

/-- A genuine actual crossing disk PRODUCES the chart for the compactly
supported anchor-relative slide; no alignment or isotopy witness is supplied. -/
theorem actual_crossing_disk_slide_chart (M : HyperellipticModel E S)
    (anchor b : EssentialMarkedArc M) (p : S) (hc : CrossesInDisk M anchor b p) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
      Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
      (∀ q : U, q.val ∈ anchor.val.image ↔ (e q).val 1 = 0) ∧
      ∃ hp : p ∈ U, planeCoordinates (e ⟨p,hp⟩).val = (0,0) := by
  obtain ⟨U,hU,hp,hm,e,he0,hanchor,hb⟩ := hc
  let B : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  let V := doublePlaneCoordinates '' B
  let f : U ≃ₜ V := e.trans (doublePlaneCoordinates.image B)
  have hCV : Plane.closedSquare 0 1 ⊆ V := by
    intro z hz
    have hcoords : |z 0| ≤ 1 ∧ |z 1| ≤ 1 := by
      simpa only [mem_closedSquare_zero_one, Plane.supNorm, max_le_iff] using hz
    let q : ℝ × ℝ := (z 0/2,z 1/2)
    have hq : q ∈ B := by
      change |z 0/2| < 1 ∧ |z 1/2| < 1
      rw [abs_div, abs_div]
      norm_num
      constructor <;> linarith [hcoords.1,hcoords.2]
    refine ⟨q,hq,?_⟩
    apply planeCoordinates.injective
    apply Prod.ext
    · change 2*(z 0/2) = z 0
      ring
    · change 2*(z 1/2) = z 1
      ring
  refine ⟨U,V,hU,f,hCV,hm,?_,hp,?_⟩
  · intro q
    have hh := hanchor q
    change q.val ∈ anchor.val.image ↔ 2*(e q).val.2 = 0
    rw [hh]
    constructor <;> intro h <;> linarith
  · apply Prod.ext
    · change 2*(e ⟨p,hp⟩).val.1 = 0
      rw [he0]
      norm_num
    · change 2*(e ⟨p,hp⟩).val.2 = 0
      rw [he0]
      norm_num

/-- Actual local crossing-slide existence derived from topological
transversality, including an explicit nonzero displacement when a ≠ 0. -/
theorem actual_crossing_disk_slide (M : HyperellipticModel E S)
    (anchor b : EssentialMarkedArc M) (p : S) (hc : CrossesInDisk M anchor b p)
    (a : Amount) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ e : U ≃ₜ V, ∃ hp : p ∈ U,
    ∃ K : AmbientIsotopy U, ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image) ∧
      (∀ t, G.map (t,p) = (K.map (t,⟨p,hp⟩)).val) ∧
      (∀ t, planeCoordinates (e (K.map (t,⟨p,hp⟩))).val = (t.val*a.val,0)) ∧
      (a.val ≠ 0 → G.map (1,p) ≠ p) := by
  obtain ⟨U,V,hU,e,hCV,hm,haxis,hp,hp0⟩ := actual_crossing_disk_slide_chart M anchor b p hc
  obtain ⟨K,G,hmarks,hanchor,hGU,hmove⟩ :=
    actual_relative_crossing_slide_moves_origin M anchor U V hU e hCV hm haxis a ⟨p,hp⟩ hp0
  refine ⟨U,V,e,hp,K,G,hmarks,hanchor,hGU,hmove,?_⟩
  intro ha heq
  have he : K.map (1,⟨p,hp⟩) = ⟨p,hp⟩ := Subtype.ext ((hGU 1).symm.trans heq)
  have hh := hmove (1 : Interval)
  rw [he,hp0] at hh
  have ha0 := congrArg Prod.fst hh
  exact ha (by simpa using ha0.symm)

end
end CurveComplex.HyperellipticModel.ArcSurgery
