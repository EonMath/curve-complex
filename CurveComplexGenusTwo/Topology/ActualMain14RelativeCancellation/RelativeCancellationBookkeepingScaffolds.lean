import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.ArcCounts.ActualTwoTraceShape

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_cancellation_zero_contacts
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hzero : ArcSurgery.crossings M a.toEssential b.toEssential = ∅) :
    ∃ b' : NonLoopArc M, ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      Disjoint (a.image \ (M.cover.branch:Set S))
        (b'.image \ (M.cover.branch:Set S)) := by
  let H : AmbientIsotopy S := {
    map := ⟨fun p => p.2, continuous_snd⟩
    homeomorphism_at := fun _ => ⟨Homeomorph.refl S, fun _ => rfl⟩
    at_zero := fun _ => rfl }
  refine ⟨b, H, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, hb, ?_⟩
  · exact Set.image_id b.image
  · apply Set.disjoint_iff_inter_eq_empty.mpr
    exact hzero

theorem relative_cancellation_zero_ncard
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hzero : (ArcSurgery.crossings M a.toEssential b.toEssential).ncard = 0) :
    ∃ b' : NonLoopArc M, ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' b.image=b'.image ∧ b'.image ⊆ interior N.closedSet ∧
      Disjoint (a.image \ (M.cover.branch:Set S))
        (b'.image \ (M.cover.branch:Set S)) := by
  exact relative_cancellation_zero_contacts M a b N hb
    ((Set.ncard_eq_zero hfinite).mp hzero)

theorem relative_supported_final_image_subset
    (H : AmbientIsotopy S) (U A : Set S)
    (hfix : ∀ t x, x ∉ U → H.map (t,x) = x) (hA : A ⊆ U) :
    H.finalMap '' A ⊆ U := by
  obtain ⟨e, he⟩ := H.homeomorphism_at 1
  rintro y ⟨x, hx, rfl⟩
  by_contra hout
  have heq : H.finalMap (H.finalMap x) = H.finalMap x := hfix 1 _ hout
  have hinj : Function.Injective H.finalMap := by
    intro u v huv
    apply e.injective
    exact (he u).trans (huv.trans (he v).symm)
  have hxfix : H.finalMap x = x := hinj heq
  exact hout (hxfix.symm ▸ hA hx)

theorem relative_cancellation_compose_motions
    (H K : AmbientIsotopy S) (P : Set S)
    (hH : ∀ t x, x ∈ P → H.map (t,x) = x)
    (hK : ∀ t x, x ∈ P → K.map (t,x) = x) :
    ∃ L : AmbientIsotopy S,
      (∀ t x, x ∈ P → L.map (t,x) = x) ∧
      (∀ x, L.finalMap x = K.finalMap (H.finalMap x)) := by
  let L : AmbientIsotopy S := {
    map := ⟨fun p => K.map (p.1,H.map p),
      K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩
    homeomorphism_at := by
      intro t
      obtain ⟨h, hh⟩ := H.homeomorphism_at t
      obtain ⟨k, hk⟩ := K.homeomorphism_at t
      refine ⟨h.trans k, ?_⟩
      intro x
      change k (h x) = K.map (t,H.map (t,x))
      rw [hh, hk]
    at_zero := by
      intro x
      change K.map (_, H.map (_,x)) = x
      rw [H.at_zero, K.at_zero] }
  refine ⟨L, ?_, fun _ => rfl⟩
  intro t x hx
  change K.map (t,H.map (t,x)) = x
  rw [hH t x hx, hK t x hx]

theorem relative_original_disk_mark_free_of_endpoint_free
    (M : HyperellipticModel E S) (a : NonLoopArc M)
    (N : ArcNeighborhood a) (C : Set S) (hC : C ⊆ N.closedSet)
    (hends : Disjoint C ({a.val.map 0, a.val.map 1} : Set S)) :
    Disjoint C (M.cover.branch : Set S) := by
  apply Set.disjoint_left.mpr
  intro x hx hmark
  have hxends : x ∈ ({a.val.map 0, a.val.map 1} : Set S) := by
    exact N.marked_inside ▸ (show x ∈ (M.cover.branch : Set S) ∩ N.closedSet
      from ⟨hmark, hC hx⟩)
  exact Set.disjoint_left.mp hends hx hxends

theorem relative_finite_contact_produces_clean_endpoint_prefixes
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (hstart : a.val.map 0 = b.val.map 0)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ r s : Interval,
      0 < r ∧ r < 1 ∧ 0 < s ∧ s < 1 ∧ a.val.map r = b.val.map s ∧
      ∀ u v : Interval, u ≤ r → v ≤ s → a.val.map u = b.val.map v →
        (u = 0 ∧ v = 0) ∨ (u = r ∧ v = s) := by
  classical
  let T : Set (Interval × Interval) := {z |
    a.val.map z.1 = b.val.map z.2 ∧
    a.val.map z.1 ∈ ArcSurgery.crossings M a.toEssential b.toEssential}
  have hTf : T.Finite := hfinite.of_injOn
    (show MapsTo (fun z : Interval × Interval => a.val.map z.1) T
      (ArcSurgery.crossings M a.toEssential b.toEssential) from fun _ hz => hz.2)
    (by
      intro z hz w hw he
      apply Prod.ext
      · exact a.injective he
      · apply b.injective
        exact hz.1.symm.trans (he.trans hw.1))
  have hTn : T.Nonempty := by
    obtain ⟨p, hp⟩ := hpositive
    obtain ⟨r, hr⟩ := hp.1.1
    obtain ⟨s, hs⟩ := hp.2.1
    exact ⟨(r,s), hr.trans hs.symm, hr.symm ▸ hp⟩
  obtain ⟨z, hz, hmin⟩ := Set.exists_min_image T
    (fun z : Interval × Interval => z.1.val + z.2.val) hTf hTn
  have hzA : a.val.map z.1 ∉ M.cover.branch := hz.2.1.2
  have hzB : b.val.map z.2 ∉ M.cover.branch := hz.1 ▸ hzA
  have hr0 : z.1 ≠ 0 := by intro h; exact hzA (h ▸ a.val.start_marked)
  have hr1 : z.1 ≠ 1 := by intro h; exact hzA (h ▸ a.val.end_marked)
  have hs0 : z.2 ≠ 0 := by intro h; exact hzB (h ▸ b.val.start_marked)
  have hs1 : z.2 ≠ 1 := by intro h; exact hzB (h ▸ b.val.end_marked)
  have hrlt : z.1 < 1 := lt_of_le_of_ne z.1.property.2 hr1
  have hslt : z.2 < 1 := lt_of_le_of_ne z.2.property.2 hs1
  refine ⟨z.1,z.2,lt_of_le_of_ne z.1.property.1 (Ne.symm hr0), hrlt,
    lt_of_le_of_ne z.2.property.1 (Ne.symm hs0),hslt,hz.1,?_⟩
  intro u v hur hvs he
  by_cases hmark : a.val.map u ∈ M.cover.branch
  · have hu0 : u = 0 := by
      rcases a.val.marked_only_at_ends u hmark with hu | hu
      · exact hu
      · have hbad : (1 : Interval) ≤ z.1 := by
          calc (1 : Interval) = u := hu.symm
               _ ≤ z.1 := hur
        exact False.elim (not_le_of_gt hrlt hbad)
    left
    refine ⟨hu0, b.injective ?_⟩
    exact he.symm.trans ((congrArg a.val.map hu0).trans hstart)
  · have huvT : (u,v) ∈ T := by
      refine ⟨he, ?_⟩
      exact ⟨⟨⟨u,rfl⟩,hmark⟩,⟨⟨v,he.symm⟩,he ▸ hmark⟩⟩
    have hsum := hmin (u,v) huvT
    have hu : u.val = z.1.val := by
      have hv : v.val ≤ z.2.val := hvs
      have hu : u.val ≤ z.1.val := hur
      dsimp at hsum
      linarith
    have hv : v.val = z.2.val := by
      have hv : v.val ≤ z.2.val := hvs
      dsimp at hsum
      linarith
    exact Or.inr ⟨Subtype.ext hu,Subtype.ext hv⟩

theorem relative_finite_contact_produces_actual_endpoint_jordan_candidate
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hstart : a.val.map 0 = b.val.map 0)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ c : Curve S,
      c.image ⊆ interior N.closedSet ∧
      c.image ⊆ a.image ∪ b.image ∧
      ∀ x ∈ c.image, x ∈ M.cover.branch → x = a.val.map 0 := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨r,s,hr0,hr1,hs0,hs1,hmeet,hclean⟩ :=
    relative_finite_contact_produces_clean_endpoint_prefixes M a b hstart hfinite hpositive
  let scale (v : Interval) (t : Interval) : Interval :=
    ⟨t.val * v.val, by
      constructor
      · exact mul_nonneg t.property.1 v.property.1
      · nlinarith [t.property.1,t.property.2,v.property.1,v.property.2]⟩
  have hsc_cont (v : Interval) : Continuous (scale v) := by
    exact (continuous_subtype_val.mul continuous_const).subtype_mk _
  have hsc_zero (v : Interval) : scale v 0 = 0 := Subtype.ext (by simp [scale])
  have hsc_one (v : Interval) : scale v 1 = v := Subtype.ext (by simp [scale])
  have hsc_le (v t : Interval) : scale v t ≤ v := by
    change t.val * v.val ≤ v.val
    nlinarith [t.property.1,t.property.2,v.property.1]
  have hsc_inj (v : Interval) (hv : 0 < v) : Function.Injective (scale v) := by
    intro t u he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    dsimp [scale] at he'
    exact mul_right_cancel₀ (ne_of_gt (show 0 < v.val from hv)) he'
  let f : C(Interval,S) := ⟨a.val.map ∘ scale r,a.val.continuous.comp (hsc_cont r)⟩
  let g : C(Interval,S) := ⟨b.val.map ∘ scale s,b.val.continuous.comp (hsc_cont s)⟩
  have hf0 : f 0 = g 0 := by simpa [f,g,hsc_zero] using hstart
  have hf1 : f 1 = g 1 := by simpa [f,g,hsc_one] using hmeet
  have hfinj : Function.Injective f := a.injective.comp (hsc_inj r hr0)
  have hginj : Function.Injective g := b.injective.comp (hsc_inj s hs0)
  have hinter : ∀ u v : Interval, f u = g v →
      (u=0 ∧ v=0) ∨ (u=1 ∧ v=1) := by
    intro u v he
    rcases hclean (scale r u) (scale s v) (hsc_le r u) (hsc_le s v) he with h | h
    · exact Or.inl ⟨hsc_inj r hr0 (h.1.trans (hsc_zero r).symm),
        hsc_inj s hs0 (h.2.trans (hsc_zero s).symm)⟩
    · exact Or.inr ⟨hsc_inj r hr0 (h.1.trans (hsc_one r).symm),
        hsc_inj s hs0 (h.2.trans (hsc_one s).symm)⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hfinj hginj hf0 hf1 hinter
  have hfa : range f ⊆ a.image := by rintro x ⟨t,rfl⟩; exact mem_range_self _
  have hgb : range g ⊆ b.image := by rintro x ⟨t,rfl⟩; exact mem_range_self _
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hc]
    exact union_subset (hfa.trans N.arc_inside) (hgb.trans hb)
  · rw [hc]
    exact union_subset_union hfa hgb
  · intro x hx hmark
    rw [hc] at hx
    rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · rcases a.val.marked_only_at_ends (scale r t) hmark with ht | ht
      · exact congrArg a.val.map ht
      · have hbad : (1:Interval) ≤ r := ht.symm.trans_le (hsc_le r t)
        exact False.elim (not_le_of_gt hr1 hbad)
    · rcases b.val.marked_only_at_ends (scale s t) hmark with ht | ht
      · exact (congrArg b.val.map ht).trans hstart.symm
      · have hbad : (1:Interval) ≤ s := ht.symm.trans_le (hsc_le s t)
        exact False.elim (not_le_of_gt hs1 hbad)

theorem relative_finite_contact_produces_actual_jordan_candidate
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ c : Curve S,
      c.image ⊆ interior N.closedSet ∧
      c.image ⊆ a.image ∪ b.image ∧
      ∀ x ∈ c.image, x ∈ M.cover.branch → x = a.val.map 0 := by
  have ha0 : a.val.map 0 ∈ ({b.val.map 0,b.val.map 1} : Set S) := by
    rw [← hends]
    exact Set.mem_insert _ _
  rcases Set.mem_insert_iff.mp ha0 with hstart | hlast
  · exact relative_finite_contact_produces_actual_endpoint_jordan_candidate
      M a b N hb hstart hfinite hpositive
  · have hlast' : a.val.map 0 = b.val.map 1 := Set.mem_singleton_iff.mp hlast
    obtain ⟨d,hd0,hd1,hdim⟩ := actual_nonloop_reversed_representative M b.toEssential b.property
    have hdne : d.val.map 0 ≠ d.val.map 1 := by
      rw [hd0,hd1]
      exact b.property.symm
    let b' : NonLoopArc M := ⟨d.val,hdne⟩
    have him : b'.image = b.image := hdim
    have hc : ArcSurgery.crossings M a.toEssential b'.toEssential =
        ArcSurgery.crossings M a.toEssential b.toEssential := by
      change (a.image \ (M.cover.branch : Set S)) ∩
        (b'.image \ (M.cover.branch : Set S)) = _
      rw [him]
      rfl
    obtain ⟨c,hcN,hcab,hmark⟩ :=
      relative_finite_contact_produces_actual_endpoint_jordan_candidate M a b' N
        (him.symm ▸ hb) (hlast'.trans hd0.symm)
        (hc.symm ▸ hfinite) (hc.symm ▸ hpositive)
    exact ⟨c,hcN,by simpa only [him] using hcab,hmark⟩

end CurveComplex.HyperellipticModel
