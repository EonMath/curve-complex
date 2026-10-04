import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily FreeBoundaryNullGeometry

/-- A clean lifted return produces the complete ordinary Q-null boundary,
including both whole-trace containments and an actual nullhomotopy in Q. -/
theorem free_boundary_clean_return_gives_null_bigon
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] [SimplyConnectedSpace Y]
    (B : Set X) (p : Y → X) (hp : Continuous p)
    (a b : C(Interval,X)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hends : a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B)
    (hdis : Disjoint ({a 0,a 1} : Set X) {b 0,b 1})
    (A D : C(Interval,Y)) (hAp : ∀ t, p (A t) = a t) (hBp : ∀ t, p (D t) = b t)
    (l r : Interval) (hlr : l < r) (hl : D l ∈ range A) (hr : D r ∈ range A)
    (hgap : ∀ u : Interval, l < u → u < r → b u ∉ range a) :
    Nonempty (NullBigonBoundary B a b) := by
  have hAemb : Topology.IsEmbedding A := by
    apply Topology.IsEmbedding.of_comp A.continuous hp
    have he : p ∘ (A : Interval → Y) = a := funext hAp
    rwa [he]
  have hBemb : Topology.IsEmbedding D := by
    apply Topology.IsEmbedding.of_comp D.continuous hp
    have he : p ∘ (D : Interval → Y) = b := funext hBp
    rwa [he]
  obtain ⟨s,hs⟩ := hl
  obtain ⟨t,ht⟩ := hr
  have hst : s ≠ t := by
    intro he
    exact hlr.ne (hBemb.injective (hs.symm.trans (he ▸ ht)))
  obtain ⟨P,hP,hPrange⟩ := regional_embedded_subarc_between A hAemb s t hst
  obtain ⟨Q,hQ,hQrange,hQint⟩ := LocalSurgery.actual_embedded_affine_subarc D hBemb l r hlr
  let Q' : Path (A s) (A t) := Q.cast hs ht
  let first : Path (p (A s)) (p (A t)) := P.map hp
  let second : Path (p (A s)) (p (A t)) := Q'.map hp
  have hfirstA : Set.range first ⊆ Set.range a := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hv⟩ := hPrange (Set.mem_range_self u)
    exact ⟨v,(hAp v).symm.trans (congrArg p hv)⟩
  have hsecondB : Set.range second ⊆ Set.range b := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hv⟩ := hQrange.trans (Set.image_subset_range D _) (Set.mem_range_self u)
    exact ⟨v,(hBp v).symm.trans (congrArg p hv)⟩
  have hfirst : Topology.IsEmbedding first := by
    apply first.continuous.isClosedEmbedding _ |>.isEmbedding
    intro u v he
    obtain ⟨u',hu'⟩ := hPrange (Set.mem_range_self u)
    obtain ⟨v',hv'⟩ := hPrange (Set.mem_range_self v)
    have he' : a u' = a v' := by
      rw [← hAp,← hAp,hu',hv']
      exact he
    exact hP.injective (hu'.symm.trans ((ha.injective he') ▸ hv'))
  have hsecond : Topology.IsEmbedding second := by
    apply second.continuous.isClosedEmbedding _ |>.isEmbedding
    intro u v he
    obtain ⟨u',hu'⟩ := hQrange.trans (Set.image_subset_range D _) (Set.mem_range_self u)
    obtain ⟨v',hv'⟩ := hQrange.trans (Set.image_subset_range D _) (Set.mem_range_self v)
    have he' : b u' = b v' := by
      rw [← hBp,← hBp,hu',hv']
      exact he
    exact hQ.injective (hu'.symm.trans ((hb.injective he') ▸ hv'))
  have hzero : first 0 = second 0 := first.source.trans second.source.symm
  have hone : first 1 = second 1 := first.target.trans second.target.symm
  have hf0 : first 0 = b l := first.source.trans ((congrArg p hs).trans (hBp l))
  have hf1 : first 1 = b r := first.target.trans ((congrArg p ht).trans (hBp r))
  have hne : first 0 ≠ first 1 := by
    intro he
    exact hlr.ne (hb.injective (hf0.symm.trans (he.trans hf1)))
  have hclean : ∀ z ∈ Set.range second, z ∈ Set.range a →
      z = first 0 ∨ z = first 1 := by
    rintro z ⟨u,rfl⟩ hza
    by_cases hu0 : u = 0
    · exact Or.inl (hu0 ▸ hzero.symm)
    by_cases hu1 : u = 1
    · exact Or.inr (hu1 ▸ hone.symm)
    have hu : u ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne u.property.1 (Ne.symm hu0),lt_of_le_of_ne u.property.2 hu1⟩
    obtain ⟨v,hv,he⟩ := hQint ⟨u,hu,rfl⟩
    have hbv : b v = second u := (hBp v).symm.trans (congrArg p he)
    exact False.elim (hgap v hv.1 hv.2 (hbv.symm ▸ hza))
  have hmeet : Set.range first ∩ Set.range second = {first 0,first 1} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzf,hzs⟩
      exact (hclean z hzs (hfirstA hzf)).elim
        (fun he => Or.inl he) (fun he => Or.inr he)
    · rintro z (rfl | rfl)
      · exact ⟨Set.mem_range_self 0,⟨0,hzero.symm⟩⟩
      · exact ⟨Set.mem_range_self 1,⟨1,hone.symm⟩⟩
  have hcollision : ∀ u v, first u = second v →
      (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 1) := by
    intro u v he
    rcases hclean (first u) ⟨v,he.symm⟩ (hfirstA (Set.mem_range_self u)) with h | h
    · exact Or.inl ⟨hfirst.injective h,hsecond.injective (he.symm.trans (h.trans hzero))⟩
    · exact Or.inr ⟨hfirst.injective h,hsecond.injective (he.symm.trans (h.trans hone))⟩
  have hhom : first.Homotopic second :=
    (SimplyConnectedSpace.paths_homotopic P Q').map ⟨p,hp⟩
  obtain ⟨loop,hloop,hnull⟩ := clean_homotopic_arcs_bound_null_curve
    first second hfirst hsecond hcollision hhom
  have hcorner (u : Interval) : first u = second u → first u ∉ B := by
    intro heu
    obtain ⟨v,hv⟩ := hfirstA (Set.mem_range_self u)
    obtain ⟨w,hw⟩ := hsecondB (Set.mem_range_self u)
    have hvw : a v = b w := hv.trans (heu.trans hw.symm)
    exact hv ▸ (free_boundary_contact_parameters_interior B a b hends hproper hdis v w hvw).2.2
  exact ⟨{
    first := first.toContinuousMap
    second := second.toContinuousMap
    first_embedded := hfirst
    second_embedded := hsecond
    first_on_a := hfirstA
    second_on_b := hsecondB
    zero_eq := hzero
    one_eq := hone
    corners_off_boundary := ⟨hcorner 0 hzero,hcorner 1 hone⟩
    sides_inter := hmeet
    loop := loop
    loop_image := hloop
    loop_null := hnull }⟩

end CoherentEndpointMotion.FreeBoundaryContactRepair
