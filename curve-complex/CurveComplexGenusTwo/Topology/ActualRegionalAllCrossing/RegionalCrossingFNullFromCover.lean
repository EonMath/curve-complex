import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCoverLiftFamily

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- A clean return in a simply connected cover of F gives a genuine F-null
embedded circle. The selected sides project injectively because the original
arcs are embedded; the original nonclean contact forces an interior corner. -/
theorem regional_clean_return_in_F_cover_gives_F_null_subloop
    {S X : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace X] [T2Space X] [SimplyConnectedSpace X]
    {F : Set S} (p : X → ↥F) (hp : Continuous p)
    (a b : C(Interval, ↥F)) (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hnonclean : ¬ ∀ s t, a s = b t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (A B : C(Interval,X))
    (hAp : ∀ t, p (A t) = a t) (hBp : ∀ t, p (B t) = b t)
    (l r : Interval) (hlr : l < r)
    (hl : B l ∈ Set.range A) (hr : B r ∈ Set.range A)
    (hgap : ∀ u : Interval, l < u → u < r → b u ∉ Set.range a) :
    ∃ (first second : C(Interval, ↥F)) (loop : Curve ↥F),
      Topology.IsEmbedding first ∧ Topology.IsEmbedding second ∧
      Set.range first ⊆ Set.range a ∧ Set.range second ⊆ Set.range b ∧
      first 0 = second 0 ∧ first 1 = second 1 ∧ first 0 ≠ first 1 ∧
      Set.range first ∩ Set.range second = {first 0,first 1} ∧
      loop.image = Set.range first ∪ Set.range second ∧
      (⟨loop.map,loop.embedded.continuous⟩ : C(Circle, ↥F)).Nullhomotopic ∧
      ∃ s t : Interval,
        s ∈ Set.Ioo (0 : Interval) 1 ∧ t ∈ Set.Ioo (0 : Interval) 1 ∧
        a s = b t ∧ (a s = first 0 ∨ a s = first 1) := by
  have hAemb : Topology.IsEmbedding A := by
    apply Topology.IsEmbedding.of_comp A.continuous hp
    have he : p ∘ (A : Interval → X) = a := funext hAp
    rwa [he]
  have hBemb : Topology.IsEmbedding B := by
    apply Topology.IsEmbedding.of_comp B.continuous hp
    have he : p ∘ (B : Interval → X) = b := funext hBp
    rwa [he]
  obtain ⟨s,hs⟩ := hl
  obtain ⟨t,ht⟩ := hr
  have hst : s ≠ t := by
    intro he
    exact hlr.ne (hBemb.injective (hs.symm.trans (he ▸ ht)))
  obtain ⟨P,hP,hPrange⟩ := regional_embedded_subarc_between A hAemb s t hst
  obtain ⟨Q,hQ,hQrange,hQint⟩ := LocalSurgery.actual_embedded_affine_subarc B hBemb l r hlr
  let Q' : Path (A s) (A t) := Q.cast hs ht
  let first : Path (p (A s)) (p (A t)) := P.map hp
  let second : Path (p (A s)) (p (A t)) := Q'.map hp
  have hfirstA : Set.range first ⊆ Set.range a := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hv⟩ := hPrange (Set.mem_range_self u)
    exact ⟨v,(hAp v).symm.trans (congrArg p hv)⟩
  have hsecondB : Set.range second ⊆ Set.range b := by
    rintro z ⟨u,rfl⟩
    obtain ⟨v,hv⟩ := hQrange.trans (Set.image_subset_range B _) (Set.mem_range_self u)
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
    obtain ⟨u',hu'⟩ := hQrange.trans (Set.image_subset_range B _) (Set.mem_range_self u)
    obtain ⟨v',hv'⟩ := hQrange.trans (Set.image_subset_range B _) (Set.mem_range_self v)
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
  refine ⟨first.toContinuousMap,second.toContinuousMap,loop,hfirst,hsecond,
    hfirstA,hsecondB,hzero,hone,hne,hmeet,hloop,hnull,?_⟩
  have hcorners : l ≠ 0 ∨ r ≠ 1 := by
    by_contra hn
    push Not at hn
    obtain ⟨u,v,hu,hv,huv⟩ := regional_nonclean_has_interior_contact a b ha hb h0 h1 hnonclean
    exact hgap v (hn.1 ▸ hv.1) (hn.2 ▸ hv.2) ⟨u,huv⟩
  have interior_first_param (u v : Interval) (hv : v ∈ Set.Ioo (0 : Interval) 1)
      (he : a u = b v) : u ∈ Set.Ioo (0 : Interval) 1 := by
    have hu0 : u ≠ 0 := by
      intro h
      have h' : b v = b 0 := he.symm.trans (h ▸ h0.symm)
      exact hv.1.ne' (hb.injective h')
    have hu1 : u ≠ 1 := by
      intro h
      have h' : b v = b 1 := he.symm.trans (h ▸ h1.symm)
      exact hv.2.ne (hb.injective h')
    exact ⟨lt_of_le_of_ne u.property.1 (Ne.symm hu0),lt_of_le_of_ne u.property.2 hu1⟩
  rcases hcorners with hl0 | hr1
  · have hlI : l ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne l.property.1 (Ne.symm hl0),hlr.trans_le r.property.2⟩
    have hsl : a s = b l := (hAp s).symm.trans ((congrArg p hs).trans (hBp l))
    exact ⟨s,l,interior_first_param s l hlI hsl,hlI,hsl,Or.inl (hsl.trans hf0.symm)⟩
  · have hrI : r ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨l.property.1.trans_lt hlr,lt_of_le_of_ne r.property.2 hr1⟩
    have htr : a t = b r := (hAp t).symm.trans ((congrArg p ht).trans (hBp r))
    exact ⟨t,r,interior_first_param t r hrI htr,hrI,htr,Or.inr (htr.trans hf1.symm)⟩

end RegionalEmbeddedFamily
