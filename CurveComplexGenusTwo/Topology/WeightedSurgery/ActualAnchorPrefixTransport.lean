import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorParameterTransport

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
variable (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
  (G : AmbientIsotopy S)
  (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
  (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)

def closedAnchorParameterMove (t : Interval) (r : Interval) : Interval :=
  if hz : r.val = 0 then 0 else if ho : r.val = 1 then 1 else
    openAnchorInterval (anchorParameterMove M anchor G hm ha t
      ⟨r.val,lt_of_le_of_ne r.property.1 (Ne.symm hz),lt_of_le_of_ne r.property.2 ho⟩)

theorem closedAnchorParameterMove_zero (t : Interval) :
    closedAnchorParameterMove M anchor G hm ha t 0 = 0 := by
  simp [closedAnchorParameterMove]

theorem closedAnchorParameterMove_one (t : Interval) :
    closedAnchorParameterMove M anchor G hm ha t 1 = 1 := by
  simp [closedAnchorParameterMove]

theorem closedAnchorParameterMove_open (t : Interval) (r : OpenAnchorParameter) :
    closedAnchorParameterMove M anchor G hm ha t (openAnchorInterval r) =
      openAnchorInterval (anchorParameterMove M anchor G hm ha t r) := by
  unfold closedAnchorParameterMove
  rw [dite_eq_right (show (openAnchorInterval r).val ≠ 0 from ne_of_gt r.property.1),
    dite_eq_right (show (openAnchorInterval r).val ≠ 1 from ne_of_lt r.property.2)]
  rfl

theorem closedAnchorParameterMove_strictMono (t : Interval) :
    StrictMono (closedAnchorParameterMove M anchor G hm ha t) := by
  intro r s hrs
  have hr1 : r.val < 1 := lt_of_lt_of_le hrs s.property.2
  have hs0 : 0 < s.val := lt_of_le_of_lt r.property.1 hrs
  by_cases hr0 : r.val = 0
  · have he : r = 0 := Subtype.ext hr0
    rw [he,closedAnchorParameterMove_zero]
    by_cases hs1 : s.val = 1
    · rw [show s = 1 from Subtype.ext hs1,closedAnchorParameterMove_one]
      norm_num
    · let q : OpenAnchorParameter := ⟨s.val,hs0,lt_of_le_of_ne s.property.2 hs1⟩
      have hsq : s = openAnchorInterval q := rfl
      rw [hsq,closedAnchorParameterMove_open]
      exact (anchorParameterMove M anchor G hm ha t q).property.1
  · let p : OpenAnchorParameter := ⟨r.val,lt_of_le_of_ne r.property.1 (Ne.symm hr0),hr1⟩
    have hrp : r = openAnchorInterval p := rfl
    by_cases hs1 : s.val = 1
    · rw [show s = 1 from Subtype.ext hs1,closedAnchorParameterMove_one,hrp,closedAnchorParameterMove_open]
      exact (anchorParameterMove M anchor G hm ha t p).property.2
    · let q : OpenAnchorParameter := ⟨s.val,hs0,lt_of_le_of_ne s.property.2 hs1⟩
      have hsq : s = openAnchorInterval q := rfl
      rw [hrp,hsq,closedAnchorParameterMove_open,closedAnchorParameterMove_open]
      exact anchorParameterMove_strictMono M anchor G hm ha t hrs

theorem closedAnchorParameterMove_surjective (t : Interval) :
    Function.Surjective (closedAnchorParameterMove M anchor G hm ha t) := by
  intro s
  by_cases hs0 : s.val = 0
  · exact ⟨0,(closedAnchorParameterMove_zero M anchor G hm ha t).trans (Subtype.ext hs0).symm⟩
  · by_cases hs1 : s.val = 1
    · exact ⟨1,(closedAnchorParameterMove_one M anchor G hm ha t).trans (Subtype.ext hs1).symm⟩
    · let q : OpenAnchorParameter :=
        ⟨s.val,lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩
      obtain ⟨r,hr⟩ := anchorParameterMove_surjective M anchor G hm ha t q
      refine ⟨openAnchorInterval r,?_⟩
      rw [closedAnchorParameterMove_open,hr]
      rfl

/-- Actual order transport along the anchor, derived even for loop anchors. -/
def anchorParameterOrderIso (t : Interval) : Interval ≃o Interval :=
  RelIso.ofSurjective (OrderEmbedding.ofStrictMono
    (closedAnchorParameterMove M anchor G hm ha t)
    (closedAnchorParameterMove_strictMono M anchor G hm ha t))
    (closedAnchorParameterMove_surjective M anchor G hm ha t)

theorem anchorParameterOrderIso_map (t : Interval) (r : Interval) :
    anchor.val.map (anchorParameterOrderIso M anchor G hm ha t r) = G.map (t,anchor.val.map r) := by
  change anchor.val.map (closedAnchorParameterMove M anchor G hm ha t r) = _
  by_cases hr0 : r.val = 0
  · have he : r = 0 := Subtype.ext hr0
    rw [he,closedAnchorParameterMove_zero]
    exact (hm t _ anchor.val.start_marked).symm
  · by_cases hr1 : r.val = 1
    · have he : r = 1 := Subtype.ext hr1
      rw [he,closedAnchorParameterMove_one]
      exact (hm t _ anchor.val.end_marked).symm
    · let q : OpenAnchorParameter :=
        ⟨r.val,lt_of_le_of_ne r.property.1 (Ne.symm hr0),lt_of_le_of_ne r.property.2 hr1⟩
      have hrq : r = openAnchorInterval q := rfl
      rw [hrq,closedAnchorParameterMove_open,anchorParameterMove_map]

theorem actual_anchor_prefix_transport (t : Interval) (u : Interval) :
    (fun p => G.map (t,p)) '' (anchor.val.map '' {r : Interval | r.val ≤ u.val}) =
      anchor.val.map '' {r : Interval | r.val ≤ (anchorParameterOrderIso M anchor G hm ha t u).val} := by
  let e := anchorParameterOrderIso M anchor G hm ha t
  ext p
  constructor
  · rintro ⟨q,⟨r,hr,rfl⟩,rfl⟩
    exact ⟨e r,e.monotone hr,anchorParameterOrderIso_map M anchor G hm ha t r⟩
  · rintro ⟨s,hs,rfl⟩
    refine ⟨anchor.val.map (e.symm s),⟨e.symm s,?_,rfl⟩,?_⟩
    · exact (e.le_iff_le).mp (by simpa using hs)
    · exact (anchorParameterOrderIso_map M anchor G hm ha t (e.symm s)).symm.trans
        (congrArg anchor.val.map (e.apply_symm_apply s))

end
end CurveComplex.HyperellipticModel.ArcSurgery
