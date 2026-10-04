import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialMarkedDiskCrosscut
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Construct a genuine subdisk from an actual entering old arc in a
half-bigon. The marked boundary corner is permitted and retained as the
only possible mark; the original UNMARKED corner is excluded from the
whole new disk. No strengthening to full closed-disk mark-freeness occurs. -/
theorem actual_essential_half_bigon_obstruction_produces_subdisk
    (M : HyperellipticModel E S) {ι : Type} (old : ι → EssentialMarkedArc M)
    (hsystem : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (i j : ι) (hji : j ≠ i)
    (firstSide g : C(Interval,S)) (hg : IsEmbedding g)
    (hfirst : range firstSide ⊆ (old i).val.image) (hgnew : range g ⊆ a.val.image)
    (hzero : firstSide 0 = g 0) (hone : firstSide 1 = g 1)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S))
    (hmarkCorner : ∀ p ∈ range d, p ∈ (M.cover.branch : Set S) → p = g 0)
    (hlastFree : g 1 ∉ (M.cover.branch : Set S))
    (hboundary : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      range firstSide ∪ range g)
    (hin : ((old j).val.image ∩
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
    ∃ (f g' : C(Interval,S))
      (d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)),
      IsEmbedding f ∧ IsEmbedding g' ∧ IsEmbedding d' ∧
      f 0 ≠ f 1 ∧ g' 0 = f 0 ∧ g' 1 = f 1 ∧
      range f ⊆ (old j).val.image ∧ range g' ⊆ a.val.image ∧
      range f ∩ range g' = {f 0,f 1} ∧
      d' '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        range f ∪ range g' ∧
      range d' ⊆ range d ∧ g 1 ∉ range d' ∧
      Disjoint (d' '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S) ∧
      (∀ p ∈ range d', p ∈ (M.cover.branch : Set S) → p = g 0) ∧
      (∀ p ∈ range d', p ∈ (M.cover.branch : Set S) → p = f 0 ∨ p = f 1) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  obtain ⟨f,hf,hfon,hf0boundary,hf1boundary,hfin⟩ :=
    actual_essential_marked_arc_entering_interior_free_disk_has_crosscut
      M (old j) d hd hmarks hin
  have hfne : f 0 ≠ f 1 := fun he => zero_ne_one (hf.injective he)
  have endpoint (t : Interval)
      (ht : f t ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
      f t ∈ range g := by
    have htK : f t ∈ range d := image_subset_range _ _ ht
    by_cases hm : f t ∈ (M.cover.branch : Set S)
    · exact ⟨0,(hmarkCorner (f t) htK hm).symm⟩
    rw [hboundary] at ht
    rcases ht with ht | ht
    · exact False.elim (disjoint_left.mp (hsystem j i hji)
        ⟨hfon ⟨t,rfl⟩,hm⟩ ⟨hfirst ht,hm⟩)
    · exact ht
  have hf0 : f 0 ∈ range g := endpoint 0 hf0boundary
  have hf1 : f 1 ∈ range g := endpoint 1 hf1boundary
  obtain ⟨r,hr⟩ := hf0
  obtain ⟨s,hs⟩ := hf1
  have hrs : r ≠ s := fun he => hfne (hr.symm.trans ((congrArg g he).trans hs))
  have hlast : g 1 ∈ arcInterior M (old i) := ⟨hfirst ⟨1,hone⟩,hlastFree⟩
  have hlastNotF : g 1 ∉ range f := fun htf =>
    disjoint_left.mp (hsystem j i hji) ⟨hfon htf,hlastFree⟩ hlast
  have hr1 : r ≠ 1 := fun he => hlastNotF (he ▸ ⟨0,hr.symm⟩)
  have hs1 : s ≠ 1 := fun he => hlastNotF (he ▸ ⟨1,hs.symm⟩)
  let affine : Interval → Interval := fun t =>
    ⟨(1-t.val)*r.val+t.val*s.val,by constructor <;>
      nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,s.property.1,s.property.2]⟩
  let g' : C(Interval,S) := ⟨g ∘ affine,g.continuous.comp (by fun_prop)⟩
  have hg0 : g' 0 = f 0 := by simpa [g',affine] using hr
  have hg1 : g' 1 = f 1 := by simpa [g',affine] using hs
  have hginj : Function.Injective g' := by
    intro t u he
    have hv := congrArg Subtype.val (hg.injective he)
    apply Subtype.ext
    have hne : r.val ≠ s.val := fun h => hrs (Subtype.ext h)
    dsimp [affine] at hv
    have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
    rcases mul_eq_zero.mp hz with hz | hz
    · exact sub_eq_zero.mp hz
    · exact False.elim (hne (sub_eq_zero.mp hz).symm)
  have hge : IsEmbedding g' := (g'.continuous.isClosedEmbedding hginj).isEmbedding
  have hgg : range g' ⊆ range g := by rintro y ⟨t,rfl⟩; exact ⟨affine t,rfl⟩
  have hboundaryfree : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (range firstSide ∪ range g) := by
    rw [← hboundary]
    apply disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := hd.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by simpa [Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hcross (t u : Interval) (he : f t = g' u) :
      (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
    by_cases ht0 : t=0
    · left; refine ⟨ht0,hginj ?_⟩; rw [hg0,← he,ht0]
    by_cases ht1 : t=1
    · right; refine ⟨ht1,hginj ?_⟩; rw [hg1,← he,ht1]
    have htI : t ∈ Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
    exact False.elim (disjoint_left.mp hboundaryfree (hfin ⟨t,htI,rfl⟩)
      (he.symm ▸ Or.inr (hgg ⟨u,rfl⟩)))
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g' hf.injective hge.injective
    hg0.symm hg1.symm hcross
  have hcK : c.image ⊆ range d := by
    rw [hc]
    rintro y (⟨t,rfl⟩ | hgy)
    · by_cases ht0 : t=0
      · subst t; exact image_subset_range _ _ (hboundary.symm ▸ (show f 0 ∈ range firstSide ∪ range g from Or.inr ⟨r,hr⟩))
      by_cases ht1 : t=1
      · subst t; exact image_subset_range _ _ (hboundary.symm ▸ (show f 1 ∈ range firstSide ∪ range g from Or.inr ⟨s,hs⟩))
      exact image_subset_range _ _ (hfin ⟨t,
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
    · exact image_subset_range _ _ (hboundary.symm ▸ (show y ∈ range firstSide ∪ range g from Or.inr (hgg hgy)))
  obtain ⟨d',hd',hd'b,hsub⟩ := LocalSurgery.curve_in_embedded_disk_bounds_subdisk c d hd hcK
  have hnotG : g 1 ∉ range g' := by
    rintro ⟨t,ht⟩
    have he := congrArg Subtype.val (hg.injective ht)
    have hrlt : r.val < 1 := lt_of_le_of_ne r.property.2 (fun h => hr1 (Subtype.ext h))
    have hslt : s.val < 1 := lt_of_le_of_ne s.property.2 (fun h => hs1 (Subtype.ext h))
    change (1-t.val)*r.val+t.val*s.val = 1 at he
    by_cases ht1 : t.val=1
    · simp only [ht1,sub_self,zero_mul,one_mul,zero_add] at he
      exact hs1 (Subtype.ext he)
    have hp := mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht1)) (sub_pos.mpr hrlt)
    have hn := mul_nonneg t.property.1 (sub_nonneg.mpr hslt.le)
    nlinarith
  have hnotC : g 1 ∉ c.image := by
    rw [hc]; exact fun h => h.elim hlastNotF hnotG
  have hmissing : g 1 ∉ range d' := by
    rintro ⟨v,hv⟩
    have hn : ‖v.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
    have hne : ‖v.val‖ ≠ 1 := by
      intro heq
      exact hnotC (hd'b ▸ ⟨v,by simpa [Metric.mem_sphere,dist_zero_right] using heq,hv⟩)
    have hvopen : d' v ∈ d' '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
      ⟨v,by simpa [Metric.mem_ball,dist_zero_right] using lt_of_le_of_ne hn hne,rfl⟩
    have hinOld : d' v ∈ interior (range d) :=
      ((LocalSurgery.embedded_surface_disk_interior_isOpen d' hd').subset_interior_iff.mpr
        (fun z hz => hsub (image_subset_range _ _ hz))) hvopen
    rw [LocalSurgery.embedded_surface_disk_interior_eq d hd,hv] at hinOld
    exact disjoint_left.mp hboundaryfree hinOld (Or.inr ⟨1,rfl⟩)
  have hinsideSub :
      d' '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
      d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    rw [← LocalSurgery.embedded_surface_disk_interior_eq d hd]
    exact (LocalSurgery.embedded_surface_disk_interior_isOpen d' hd').subset_interior_iff.mpr
      (fun z hz => hsub (image_subset_range _ _ hz))
  have hsides : range f ∩ range g' = {f 0,f 1} := by
    ext y
    constructor
    · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      rcases hcross t u (ht.trans hu.symm) with ⟨ht0,_⟩ | ⟨ht1,_⟩
      · simp [← ht,ht0]
      · simp [← ht,ht1]
    · intro hy
      rcases mem_insert_iff.mp hy with hy | hy
      · subst y; exact ⟨⟨0,rfl⟩,⟨0,hg0⟩⟩
      · have hy' : y=f 1 := mem_singleton_iff.mp hy
        subst y; exact ⟨⟨1,rfl⟩,⟨1,hg1⟩⟩
  have hcorners : ∀ p ∈ range d', p ∈ (M.cover.branch : Set S) → p = f 0 ∨ p = f 1 := by
    rintro p ⟨v,hv⟩ hm
    have hn : ‖v.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
    have hnnot : ¬ ‖v.val‖ < 1 := by
      intro hlt
      exact disjoint_left.mp (hmarks.mono_left hinsideSub)
        ⟨v,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hlt,hv⟩ hm
    have hpb : p ∈ range f ∪ range g' := by
      rw [← hc,← hd'b]
      exact ⟨v,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
        using le_antisymm hn (not_lt.mp hnnot),hv⟩
    rcases hpb with ⟨t,ht⟩ | ⟨t,ht⟩
    · by_cases ht0 : t = 0
      · exact Or.inl (ht.symm.trans (congrArg f ht0))
      by_cases ht1 : t = 1
      · exact Or.inr (ht.symm.trans (congrArg f ht1))
      have htI : t ∈ Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
      exact False.elim (disjoint_left.mp hmarks (hfin ⟨t,htI,rfl⟩) (ht ▸ hm))
    · have he : g' t = g 0 := hmarkCorner (g' t)
        (image_subset_range _ _ (hboundary.symm ▸
          (show g' t ∈ range firstSide ∪ range g from Or.inr (hgg ⟨t,rfl⟩)))) (ht ▸ hm)
      rcases actual_embedded_side_source_endpoint g g' hg hge hgg t (Or.inl he) with ht0 | ht1
      · exact Or.inl (ht.symm.trans ((congrArg g' ht0).trans hg0))
      · exact Or.inr (ht.symm.trans ((congrArg g' ht1).trans hg1))
  exact ⟨f,g',d',hf,hge,hd',hfne,hg0,hg1,hfon,hgg.trans hgnew,hsides,
    hd'b.trans hc,hsub,hmissing,hmarks.mono_left hinsideSub,
    (fun p hp hm => hmarkCorner p (hsub hp) hm),hcorners⟩

#print axioms actual_essential_half_bigon_obstruction_produces_subdisk
end CurveComplex.HyperellipticModel
