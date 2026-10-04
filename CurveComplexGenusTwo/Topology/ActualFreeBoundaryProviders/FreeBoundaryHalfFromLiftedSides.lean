import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts
import CurveComplexGenusTwo.Topology.FrontierCircle.PathGluingProbe

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily FreeBoundaryNullGeometry

/-- Three simple sides with a common lifted triangle give the exact half-bigon
record. The nullhomotopy is projected through p into the original codomain. -/
theorem free_boundary_lifted_three_sides_give_null_half_bigon
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (B : Set X) (a b f g c : C(Interval,X))
    (hf : IsEmbedding f) (hg : IsEmbedding g) (hc : IsEmbedding c)
    (hfa : range f ⊆ range a) (hgb : range g ⊆ range b)
    (hf0 : f 0 ∈ B) (hg0 : g 0 ∈ B)
    (h1 : f 1 = g 1) (hf1 : f 1 ∉ B)
    (hfi : ∀ t ∈ Ioo (0 : Interval) 1, f t ∉ B)
    (hgi : ∀ t ∈ Ioo (0 : Interval) 1, g t ∉ B)
    (hcB : ∀ t, c t ∈ B) (hc0 : c 0 = f 0) (hc1 : c 1 = g 0)
    (hinter : range f ∩ range g = {f 1})
    (p : Y → X) (hp : Continuous p)
    (F G C : C(Interval,Y))
    (hFp : ∀ t, p (F t) = f t) (hGp : ∀ t, p (G t) = g t)
    (hCp : ∀ t, p (C t) = c t)
    (hFG : F 1 = G 1) (hC0 : C 0 = F 0) (hC1 : C 1 = G 0) :
    Nonempty (NullHalfBigonBoundary B a b) := by
  let P : Path (F 0) (F 1) := ⟨F,rfl,rfl⟩
  let Q : Path (F 1) (G 0) := (⟨G,rfl,rfl⟩ : Path (G 0) (G 1)).symm.cast hFG rfl
  let R : Path (F 0) (G 0) := ⟨C,hC0,hC1⟩
  let first := (P.trans Q).map hp
  let second := R.map hp
  let fp := P.map hp
  let gp := Q.map hp
  have hfp (t : Interval) : fp t = f t := hFp t
  have hgp (t : Interval) : gp t = g (unitInterval.symm t) := hGp _
  have hfirsteq : first = fp.trans gp := Path.map_trans P Q hp
  have hsecondeq : ∀ t, second t = c t := hCp
  have hfprange : range fp = range f := congrArg range (funext hfp)
  have hgprange : range gp = range g := by
    rw [show (gp : Interval → X) = g ∘ unitInterval.symm from funext hgp]
    rw [Set.range_comp]
    have hs : Function.Surjective unitInterval.symm := unitInterval.symmHomeomorph.surjective
    rw [hs.range_eq,Set.image_univ]
  have hfirst : IsEmbedding first := by
    rw [hfirsteq]
    apply isEmbedding_path_trans_of_inter_singleton_probe fp gp
    · rw [show (fp : Interval → X) = f from funext hfp]
      exact hf
    · rw [show (gp : Interval → X) = g ∘ unitInterval.symm from funext hgp]
      exact hg.comp unitInterval.symmHomeomorph.isEmbedding
    · simpa only [hfprange,hgprange,hFp] using hinter
  have hsecond : IsEmbedding second := by
    have he : (second : Interval → X) = c := funext hsecondeq
    rw [he]
    exact hc
  have hfirstRange : range first = range f ∪ range g := by
    rw [hfirsteq,Path.trans_range,hfprange,hgprange]
  have first_boundary (t : Interval) (ht : first t ∈ B) : t = 0 ∨ t = 1 := by
    have boundary_only (k : C(Interval,X))
        (hi : ∀ u ∈ Ioo (0 : Interval) 1, k u ∉ B) (h1 : k 1 ∉ B)
        (u : Interval) (hu : k u ∈ B) : u = 0 := by
      by_contra h0
      by_cases hu1 : u = 1
      · exact h1 (hu1 ▸ hu)
      · exact hi u ⟨lt_of_le_of_ne u.property.1 (Ne.symm h0),
          lt_of_le_of_ne u.property.2 hu1⟩ hu
    have hfR : first t ∈ range f ∪ range g := hfirstRange ▸ Set.mem_range_self t
    rcases hfR with ⟨u,hu⟩ | ⟨u,hu⟩
    · have he := boundary_only f hfi hf1 u (hu ▸ ht)
      exact Or.inl (hfirst.injective (hu.symm.trans ((congrArg f he).trans ((hFp 0).symm.trans first.source.symm))))
    · have hg1 : g 1 ∉ B := h1 ▸ hf1
      have he := boundary_only g hgi hg1 u (hu ▸ ht)
      exact Or.inr (hfirst.injective (hu.symm.trans ((congrArg g he).trans ((hGp 0).symm.trans first.target.symm))))
  have hcollision : ∀ s t, first s = second t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    have hsB : first s ∈ B := by rw [hst,hsecondeq]; exact hcB t
    rcases first_boundary s hsB with hs | hs
    · refine Or.inl ⟨hs,hsecond.injective ?_⟩
      exact hst.symm.trans ((congrArg first hs).trans (first.source.trans second.source.symm))
    · refine Or.inr ⟨hs,hsecond.injective ?_⟩
      exact hst.symm.trans ((congrArg first hs).trans (first.target.trans second.target.symm))
  have hhom : first.Homotopic second := by
    exact (SimplyConnectedSpace.paths_homotopic (P.trans Q) R).map ⟨p,hp⟩
  obtain ⟨loop,hloop,hnull⟩ := clean_homotopic_arcs_bound_null_curve
    first second hfirst hsecond hcollision hhom
  have hrange2 : range second = range c := congrArg range (funext hsecondeq)
  refine ⟨⟨f,g,c,hf,hg,hc,hfa,hgb,hf0,hg0,h1,hf1,hfi,hgi,hcB,hc0,hc1,hinter,
    loop,?_,hnull⟩⟩
  simpa only [hfirstRange,hrange2] using hloop

end CoherentEndpointMotion.FreeBoundaryContactRepair
