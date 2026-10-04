import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryHalfFromLiftedSides
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryTracks

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies FreeBoundaryNullGeometry
open CurveComplex.BranchedDoubleCover

noncomputable def arcSegment {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (l r : Interval) : C(Interval,X) :=
  ⟨fun t => a (intervalAffine l r t),a.continuous.comp (by
    apply Continuous.subtype_mk; fun_prop)⟩

@[simp] lemma arcSegment_zero {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (l r : Interval) : arcSegment a l r 0 = a l := by
  simp [arcSegment,intervalAffine]
@[simp] lemma arcSegment_one {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (l r : Interval) : arcSegment a l r 1 = a r := by
  simp [arcSegment,intervalAffine]

lemma arcSegment_embedding {X : Type} [TopologicalSpace X]
    (a : C(Interval,X)) (ha : IsEmbedding a)
    (l r : Interval) (hlr : l ≠ r) : IsEmbedding (arcSegment a l r) := by
  apply ha.comp
  apply (show Continuous (intervalAffine l r) from by
    apply Continuous.subtype_mk; fun_prop).isClosedEmbedding _ |>.isEmbedding
  intro s t he
  have he' := congrArg Subtype.val he
  change (1-s.val)*l.val+s.val*r.val = (1-t.val)*l.val+t.val*r.val at he'
  have hne : l.val ≠ r.val := fun h => hlr (Subtype.ext h)
  apply Subtype.ext
  have hh : (s.val-t.val)*(r.val-l.val) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hne.symm))

lemma affine_endpoint_interior (e s t : Interval) (he : e = 0 ∨ e = 1)
    (hs : s ∈ Ioo (0 : Interval) 1) (ht : t ∈ Ioo (0 : Interval) 1) :
    intervalAffine e s t ∈ Ioo (0 : Interval) 1 := by
  have hs0 : 0 < s.val := hs.1
  have hs1 : s.val < 1 := hs.2
  have ht0 : 0 < t.val := ht.1
  have ht1 : t.val < 1 := ht.2
  rcases he with rfl | rfl
  · constructor
    · change 0 < (1-t.val)*0+t.val*s.val
      nlinarith [mul_pos ht0 hs0]
    · change (1-t.val)*0+t.val*s.val < 1
      nlinarith [mul_pos (sub_pos.mpr ht1) hs0]
  · constructor
    · change 0 < (1-t.val)*1+t.val*s.val
      nlinarith [mul_pos ht0 hs0]
    · change (1-t.val)*1+t.val*s.val < 1
      nlinarith [mul_pos ht0 (sub_pos.mpr hs1)]

/-- The mixed clean return supplies the same actual lifted corners for all three
sides. Projected trace containment is tied to the original a and b. -/
theorem mixed_track_return_gives_null_half_bigon
    {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (B : Set X) (a b : C(Interval,X)) (ha : IsEmbedding a)
    (ha0 : a 0 ∈ B) (ha1 : a 1 ∈ B)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (p : Y → X) (hp : Continuous p)
    {a₀ b₀ b₁ : Y} (P : Path a₀ b₀) (Q : Path b₀ b₁)
    (hQemb : IsEmbedding (fun t => p (Q t)))
    (hQb : range (fun t => p (Q t)) ⊆ range b)
    (hQ0 : p (Q 0) ∈ B)
    (hQi : ∀ t ∈ Ioo (0 : Interval) 1, p (Q t) ∉ B)
    (hPB : ∀ t, p (P t) ∈ B)
    (E : C(Interval,Y)) (hEp : ∀ t, p (E t) = a t)
    (u v : Interval) (_hu : u < 1) (hv : v ∈ Ioo (0 : Interval) 1)
    (huE : P u ∈ range E) (hvE : Q v ∈ range E)
    (hCemb : IsEmbedding (fun t => p (P (intervalAffine u 1 t))))
    (havoid : ∀ t : Interval, t < v → p (Q t) ∉ range a) :
    Nonempty (NullHalfBigonBoundary B a b) := by
  obtain ⟨e,he⟩ := huE
  obtain ⟨s,hs⟩ := hvE
  have heB : a e ∈ B := by rw [← hEp,he]; exact hPB u
  have he01 : e = 0 ∨ e = 1 := by
    by_contra hh
    push Not at hh
    exact hai e ⟨lt_of_le_of_ne e.property.1 hh.1.symm,
      lt_of_le_of_ne e.property.2 hh.2⟩ heB
  have hsB : a s ∉ B := by rw [← hEp,hs]; exact hQi v hv
  have hsI : s ∈ Ioo (0 : Interval) 1 := by
    constructor
    · apply lt_of_le_of_ne (show (0 : Interval) ≤ s from s.property.1)
      intro hh
      exact hsB (by simpa only [← hh] using ha0)
    · apply lt_of_le_of_ne (show s ≤ (1 : Interval) from s.property.2)
      intro hh
      exact hsB (by simpa only [hh] using ha1)
  have hes : e ≠ s := fun hh => hsB (hh ▸ heB)
  let q : C(Interval,X) := ⟨fun t => p (Q t),hp.comp Q.continuous⟩
  let f := arcSegment a e s
  let k := arcSegment q 0 v
  let c : C(Interval,X) := ⟨fun t => p (P (intervalAffine u 1 t)),by
    apply hp.comp; apply P.continuous.comp
    apply Continuous.subtype_mk; fun_prop⟩
  let F := arcSegment E e s
  let G := arcSegment Q.toContinuousMap 0 v
  let C := arcSegment P.toContinuousMap u 1
  have hf : IsEmbedding f := arcSegment_embedding a ha e s hes
  have hk : IsEmbedding k := arcSegment_embedding q hQemb 0 v hv.1.ne
  have hfa : range f ⊆ range a := by rintro _ ⟨t,rfl⟩; exact mem_range_self _
  have hkb : range k ⊆ range b := by
    rintro _ ⟨t,rfl⟩
    exact hQb (mem_range_self _)
  have hf0 : f 0 ∈ B := by simpa only [f,arcSegment_zero] using heB
  have hk0 : k 0 ∈ B := by simpa only [k,arcSegment_zero,q,ContinuousMap.coe_mk] using hQ0
  have h1 : f 1 = k 1 := by
    simp only [f,k,arcSegment_one]
    exact (hEp s).symm.trans (congrArg p hs)
  have hf1 : f 1 ∉ B := by simpa only [f,arcSegment_one] using hsB
  have hfi : ∀ t ∈ Ioo (0 : Interval) 1, f t ∉ B := by
    intro t ht
    exact hai _ (affine_endpoint_interior e s t he01 hsI ht)
  have hki : ∀ t ∈ Ioo (0 : Interval) 1, k t ∉ B := by
    intro t ht
    exact hQi _ (affine_endpoint_interior 0 v t (Or.inl rfl) hv ht)
  have hc0 : c 0 = f 0 := by
    change p (P (intervalAffine u 1 0)) = arcSegment a e s 0
    simp only [arcSegment_zero]
    simpa [intervalAffine] using (congrArg p he).symm.trans (hEp e)
  have hc1 : c 1 = k 0 := by
    change p (P (intervalAffine u 1 1)) = arcSegment q 0 v 0
    simp only [arcSegment_zero]
    simp [intervalAffine,q]
  have hclean (t : Interval) (ht : t < 1) : k t ∉ range a := by
    apply havoid
    change (1-t.val)*0+t.val*v.val < v.val
    have ht' : t.val < 1 := ht
    have hv' : 0 < v.val := hv.1
    nlinarith [mul_pos (sub_pos.mpr ht') hv']
  have hinter : range f ∩ range k = {f 1} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzf,t,rfl⟩
      by_cases ht : t = 1
      · simp only [ht,h1,Set.mem_singleton_iff]
      · exact False.elim (hclean t (lt_of_le_of_ne t.property.2 ht) (hfa hzf))
    · rintro z rfl
      exact ⟨mem_range_self 1,⟨1,h1.symm⟩⟩
  apply free_boundary_lifted_three_sides_give_null_half_bigon B a b f k c
    hf hk hCemb hfa hkb hf0 hk0 h1 hf1 hfi hki
    (fun t => hPB _) hc0 hc1 hinter p hp F G C
    (fun t => hEp _) (fun _ => rfl) (fun _ => rfl)
  · simpa only [F,G,arcSegment_one,Path.coe_toContinuousMap] using hs
  · simpa only [C,F,arcSegment_zero,Path.coe_toContinuousMap] using he.symm
  · simpa only [C,G,arcSegment_one,arcSegment_zero,Path.coe_toContinuousMap] using P.target.trans Q.source.symm

end CoherentEndpointMotion.FreeBoundaryContactRepair
