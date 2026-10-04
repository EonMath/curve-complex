import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorInteriorCoordinates

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
variable (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
  (G : AmbientIsotopy S)
  (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
  (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)

include hm ha

theorem anchor_interior_image (t : Interval) :
    (fun p => G.map (t,p)) '' arcInterior M anchor = arcInterior M anchor := by
  let h := timeHomeomorph G t
  have hmarks : ∀ p, p ∈ M.cover.branch → h p = p :=
    fun p hp => (timeHomeomorph_apply G t p).trans (hm t p hp)
  have hanchor : h '' anchor.val.image = anchor.val.image :=
    (congrArg (fun f : S → S => f '' anchor.val.image)
      (funext (timeHomeomorph_apply G t))).trans (ha t)
  have hi : arcInterior M (anchor.transport h hmarks) = arcInterior M anchor := by
    change (anchor.val.transport h hmarks).image \ (M.cover.branch : Set S) = _
    rw [MarkedArc.transport_image,hanchor]
    rfl
  rw [arcInterior_transport] at hi
  exact (congrArg (fun f : S → S => f '' arcInterior M anchor)
    (funext (timeHomeomorph_apply G t))).symm.trans hi

def anchorInteriorMove
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)
    (t : Interval) (p : arcInterior M anchor) : arcInterior M anchor :=
  ⟨G.map (t,p.val), by
    exact (anchor_interior_image M anchor G hm ha t).le (mem_image_of_mem _ p.property)⟩

def anchorParameterMove
    (hm : ∀ t p, p ∈ M.cover.branch → G.map (t,p) = p)
    (ha : ∀ t, (fun p => G.map (t,p)) '' anchor.val.image = anchor.val.image)
    (t : Interval) (r : OpenAnchorParameter) : OpenAnchorParameter :=
  (anchorInteriorCoordinates M anchor).symm
    (anchorInteriorMove M anchor G hm ha t (anchorInteriorCoordinates M anchor r))

theorem anchorParameterMove_continuous :
    Continuous (fun z : Interval × OpenAnchorParameter =>
      anchorParameterMove M anchor G hm ha z.1 z.2) := by
  apply (anchorInteriorCoordinates M anchor).symm.continuous.comp
  apply Continuous.subtype_mk
  exact G.map.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp
      ((anchorInteriorCoordinates M anchor).continuous.comp continuous_snd)))

theorem anchorParameterMove_map (t : Interval) (r : OpenAnchorParameter) :
    anchor.val.map (openAnchorInterval (anchorParameterMove M anchor G hm ha t r)) =
      G.map (t,anchor.val.map (openAnchorInterval r)) := by
  change (anchorInteriorCoordinates M anchor (anchorParameterMove M anchor G hm ha t r)).val = _
  rw [anchorParameterMove,Homeomorph.apply_symm_apply]
  rfl

theorem anchorParameterMove_zero (r : OpenAnchorParameter) :
    anchorParameterMove M anchor G hm ha 0 r = r := by
  apply (anchorInteriorCoordinates M anchor).injective
  apply Subtype.ext
  change anchor.val.map (openAnchorInterval (anchorParameterMove M anchor G hm ha 0 r)) = _
  rw [anchorParameterMove_map]
  exact G.at_zero _

theorem anchorParameterMove_injective (t : Interval) :
    Function.Injective (anchorParameterMove M anchor G hm ha t) := by
  intro r s he
  apply (anchorInteriorCoordinates M anchor).injective
  apply Subtype.ext
  have hc := congrArg (fun r => anchor.val.map (openAnchorInterval r)) he
  rw [anchorParameterMove_map,anchorParameterMove_map] at hc
  obtain ⟨h,hh⟩ := G.homeomorphism_at t
  rw [← hh,← hh] at hc
  exact h.injective hc

theorem anchorParameterMove_surjective (t : Interval) :
    Function.Surjective (anchorParameterMove M anchor G hm ha t) := by
  intro r
  have hr := (anchor_interior_image M anchor G hm ha t).symm.le
    (anchorInteriorCoordinates M anchor r).property
  obtain ⟨p,hp,hpr⟩ := hr
  let s := (anchorInteriorCoordinates M anchor).symm ⟨p,hp⟩
  refine ⟨s,?_⟩
  apply (anchorInteriorCoordinates M anchor).injective
  apply Subtype.ext
  change (anchorInteriorCoordinates M anchor
    ((anchorInteriorCoordinates M anchor).symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  change G.map (t,(anchorInteriorCoordinates M anchor s).val) = _
  rw [Homeomorph.apply_symm_apply]
  exact hpr

/-- All-time anchor-image preservation from an actual isotopy fixes the order
orientation even for loop anchors. No monotonicity premise is supplied. -/
theorem anchorParameterMove_strictMono (t : Interval) :
    StrictMono (anchorParameterMove M anchor G hm ha t) := by
  let r : OpenAnchorParameter := ⟨1/3,by norm_num⟩
  let s : OpenAnchorParameter := ⟨2/3,by norm_num⟩
  let Δ : Interval → ℝ := fun u =>
    (anchorParameterMove M anchor G hm ha u s).val -
      (anchorParameterMove M anchor G hm ha u r).val
  have hc : Continuous Δ := by
    exact (continuous_subtype_val.comp ((anchorParameterMove_continuous M anchor G hm ha).comp
      (continuous_id.prodMk continuous_const))).sub
      (continuous_subtype_val.comp ((anchorParameterMove_continuous M anchor G hm ha).comp
        (continuous_id.prodMk continuous_const)))
  have h0 : Δ 0 = 1/3 := by
    simp only [Δ,anchorParameterMove_zero]
    norm_num [r,s]
  have hne (u : Interval) : Δ u ≠ 0 := by
    intro he
    have hh : anchorParameterMove M anchor G hm ha u s =
        anchorParameterMove M anchor G hm ha u r := Subtype.ext (sub_eq_zero.mp he)
    have hsr := anchorParameterMove_injective M anchor G hm ha u hh
    have hval := congrArg Subtype.val hsr
    norm_num [r,s] at hval
  have hpos : 0 < Δ t := by
    by_contra ht
    have hmem : (0 : ℝ) ∈ Icc (Δ t) (Δ 0) := ⟨le_of_not_gt ht,by rw [h0]; norm_num⟩
    obtain ⟨u,_,hu⟩ := intermediate_value_Icc' (show (0 : Interval) ≤ t from t.property.1)
      hc.continuousOn hmem
    exact hne u hu
  have hct : Continuous (anchorParameterMove M anchor G hm ha t) :=
    (anchorParameterMove_continuous M anchor G hm ha).comp (continuous_const.prodMk continuous_id)
  let f : ℝ → ℝ := fun x => if hx : x ∈ Ioo (0 : ℝ) 1 then
    (anchorParameterMove M anchor G hm ha t ⟨x,hx⟩).val else x
  have hfe (r : OpenAnchorParameter) : f r.val = (anchorParameterMove M anchor G hm ha t r).val := by
    simp only [f,dite_eq_left r.property]
  have hfc : ContinuousOn f (Ioo (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun r : OpenAnchorParameter => f r.val) =
        (fun r => (anchorParameterMove M anchor G hm ha t r).val) := funext hfe
    change Continuous (fun r : OpenAnchorParameter => f r.val)
    rw [he]
    exact continuous_subtype_val.comp hct
  have hfi : InjOn f (Ioo (0 : ℝ) 1) := by
    intro x hx y hy he
    have hh : anchorParameterMove M anchor G hm ha t ⟨x,hx⟩ =
        anchorParameterMove M anchor G hm ha t ⟨y,hy⟩ := by
      apply Subtype.ext
      rw [← hfe,← hfe]
      exact he
    exact congrArg Subtype.val (anchorParameterMove_injective M anchor G hm ha t hh)
  rcases hfc.strictMonoOn_of_injOn_Ioo (by norm_num : (0 : ℝ) < 1) hfi with hmono | hanti
  · intro x y hxy
    change (anchorParameterMove M anchor G hm ha t x).val <
      (anchorParameterMove M anchor G hm ha t y).val
    rw [← hfe,← hfe]
    exact hmono x.property y.property hxy
  · have hrs : r < s := by change (1/3 : ℝ) < 2/3; norm_num
    have hh := hanti r.property s.property hrs
    rw [hfe,hfe] at hh
    change (anchorParameterMove M anchor G hm ha t s).val <
      (anchorParameterMove M anchor G hm ha t r).val at hh
    unfold Δ at hpos
    linarith

end
end CurveComplex.HyperellipticModel.ArcSurgery
