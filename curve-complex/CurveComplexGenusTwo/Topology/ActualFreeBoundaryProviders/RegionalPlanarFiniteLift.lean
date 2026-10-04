import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalPlanarCover
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalFiniteContactParameters
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- Lift a finite-contact homotopic regional pair to embedded arcs in a plane
    covering. Their lifted endpoints coincide and their intersections remain
    finite. -/
theorem finite_homotopic_regional_arcs_lift_to_plane
    {S : Type} [TopologicalSpace S] {F : Set S}
    (p : Plane → S) (hp : IsCoveringMap p)
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hhom : Path.Homotopic
      (⟨a,rfl,rfl⟩ : Path (a 0) (a 1))
      (⟨b,h0,h1⟩ : Path (a 0) (a 1)))
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (e : Plane) (he : p e = (a 0).val) :
    ∃ A B : C(Interval, Plane),
      Topology.IsEmbedding A ∧ Topology.IsEmbedding B ∧
      A 0 = e ∧ B 0 = e ∧ A 1 = B 1 ∧
      (∀ t, p (A t) = (a t).val) ∧
      (∀ t, p (B t) = (b t).val) ∧
      (Set.range A ∩ Set.range B).Finite := by
  let aS : C(Interval,S) :=
    ⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩
  let bS : C(Interval,S) :=
    ⟨fun t => (b t).val, continuous_subtype_val.comp b.continuous⟩
  let inc : C(↥F,S) := ⟨Subtype.val,continuous_subtype_val⟩
  have hhomS : ContinuousMap.HomotopicRel aS bS {0,1} := by
    have hm := hhom.map inc
    rcases hm with ⟨H⟩
    refine ⟨?_⟩
    convert H using 1 <;> ext t <;> rfl
  let A : C(Interval,Plane) := hp.liftPath aS e he.symm
  have hbStart : bS 0 = p e := by
    change (b 0).val = p e
    rw [h0,← he]
  let B : C(Interval,Plane) := hp.liftPath bS e hbStart
  have hA0 : A 0 = e := hp.liftPath_zero aS e he.symm
  have hB0 : B 0 = e := hp.liftPath_zero bS e hbStart
  have hA1 : A 1 = B 1 :=
    hp.liftPath_apply_one_eq_of_homotopicRel hhomS e he.symm hbStart
  have hAp (t : Interval) : p (A t) = (a t).val := by
    have hh := congrFun (hp.liftPath_lifts aS e he.symm) t
    exact hh
  have hBp (t : Interval) : p (B t) = (b t).val := by
    have hh := congrFun (hp.liftPath_lifts bS e hbStart) t
    exact hh
  have hAS : Topology.IsEmbedding aS :=
    Topology.IsEmbedding.subtypeVal.comp ha
  have hBS : Topology.IsEmbedding bS :=
    Topology.IsEmbedding.subtypeVal.comp hb
  have hAemb : Topology.IsEmbedding A := by
    apply Topology.IsEmbedding.of_comp A.continuous hp.continuous
    convert hAS using 1
    funext t
    exact hAp t
  have hBemb : Topology.IsEmbedding B := by
    apply Topology.IsEmbedding.of_comp B.continuous hp.continuous
    convert hBS using 1
    funext t
    exact hBp t
  have hfinLift : (Set.range A ∩ Set.range B).Finite := by
    let T : Set Interval := {s | a s ∈ Set.range a ∩ Set.range b}
    have hT : T.Finite := hfinite.of_injOn
      (show Set.MapsTo a T (Set.range a ∩ Set.range b) from
        fun s hs => hs)
      (fun s _ t _ heq => ha.injective heq)
    apply (hT.image A).subset
    rintro z ⟨⟨s,hs⟩,⟨t,ht⟩⟩
    refine ⟨s, ?_, hs⟩
    change a s ∈ Set.range a ∩ Set.range b
    refine ⟨Set.mem_range_self s, ⟨t,?_⟩⟩
    apply Subtype.ext
    calc
      (b t).val = p (B t) := (hBp t).symm
      _ = p z := by rw [ht]
      _ = p (A s) := by rw [hs]
      _ = (a s).val := hAp s
  exact ⟨A,B,hAemb,hBemb,hA0,hB0,hA1,hAp,hBp,hfinLift⟩

theorem original_finite_homotopic_regional_arcs_have_planar_lifts
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hhom : Path.Homotopic
      (⟨a,rfl,rfl⟩ : Path (a 0) (a 1))
      (⟨b,h0,h1⟩ : Path (a 0) (a 1)))
    (hfinite : (Set.range a ∩ Set.range b).Finite) :
    ∃ (p : Plane → S) (A B : C(Interval, Plane)),
      IsCoveringMap p ∧
      Topology.IsEmbedding A ∧ Topology.IsEmbedding B ∧
      A 0 = B 0 ∧ A 1 = B 1 ∧
      (∀ t, p (A t) = (a t).val) ∧
      (∀ t, p (B t) = (b t).val) ∧
      (Set.range A ∩ Set.range B).Finite := by
  classical
  let u : S := (a 0).val
  obtain ⟨top, hcov, hsurj, ⟨e⟩⟩ :=
    genus_at_least_two_universal_cover_plane S g hg hS u
  let U := Σ y : S, Path.Homotopic.Quotient u y
  let : TopologicalSpace U := top
  obtain ⟨y,hy⟩ := hsurj u
  let p : Plane → S := Sigma.fst ∘ e
  have hp : IsCoveringMap p := hcov.comp_homeomorph e
  let z : Plane := e.symm y
  have hz : p z = (a 0).val := by
    change Sigma.fst (e (e.symm y)) = u
    rw [e.apply_symm_apply]
    exact hy
  obtain ⟨A,B,hA,hB,hA0,hB0,hA1,hpA,hpB,hABfin⟩ :=
    finite_homotopic_regional_arcs_lift_to_plane
      p hp a b ha hb h0 h1 hhom hfinite z hz
  exact ⟨p,A,B,hp,hA,hB,hA0.trans hB0.symm,hA1,hpA,hpB,hABfin⟩

/-- Every projected contact is represented on the fixed lift of the second
    arc by a genuine lift of the first arc through that point. -/
theorem regional_contact_has_matching_planar_lift
    {S : Type} [TopologicalSpace S] {F : Set S}
    (p : Plane → S) (hp : IsCoveringMap p)
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a)
    (B : C(Interval,Plane))
    (hBp : ∀ t, p (B t) = (b t).val)
    (s t : Interval) (hst : a s = b t) :
    ∃ A : C(Interval,Plane),
      Topology.IsEmbedding A ∧
      A s = B t ∧
      (∀ u, p (A u) = (a u).val) := by
  let aS : C(Interval,S) :=
    ⟨fun u => (a u).val, continuous_subtype_val.comp a.continuous⟩
  have he : p (B t) = aS s := by
    change p (B t) = (a s).val
    exact (hBp t).trans (congrArg Subtype.val hst.symm)
  let : ContractibleSpace Interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : LocallyPathConnectedSpace Interval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA,hAuniq⟩ :=
    hp.existsUnique_continuousMap_lifts aS s (B t) he
  have hAp (u : Interval) : p (A u) = (a u).val := by
    have hh := congrFun hA.2 u
    exact hh
  have hAS : Topology.IsEmbedding aS :=
    Topology.IsEmbedding.subtypeVal.comp ha
  have hAemb : Topology.IsEmbedding A := by
    apply Topology.IsEmbedding.of_comp A.continuous hp.continuous
    convert hAS using 1
    funext u
    exact hAp u
  exact ⟨A,hAemb,hA.1,hAp⟩

/-- The matching lift through any one projected contact sees only finitely
    many contacts with the fixed lifted arc. -/
theorem regional_matching_lift_finite_contacts
    {S : Type} [TopologicalSpace S] {F : Set S}
    (p : Plane → S) (a b : C(Interval, ↥F))
    (A B : C(Interval,Plane))
    (hAp : ∀ u, p (A u) = (a u).val)
    (hBp : ∀ u, p (B u) = (b u).val)
    (ha : Topology.IsEmbedding a)
    (hfinite : (Set.range a ∩ Set.range b).Finite) :
    (Set.range A ∩ Set.range B).Finite := by
  have hT := regional_finite_contact_parameters a b ha hfinite
  apply (hT.image A).subset
  rintro z ⟨⟨s,hs⟩,⟨t,ht⟩⟩
  refine ⟨s, ?_, hs⟩
  change a s ∈ Set.range b
  refine ⟨t,?_⟩
  apply Subtype.ext
  calc
    (b t).val = p (B t) := (hBp t).symm
    _ = p z := by rw [ht]
    _ = p (A s) := by rw [hs]
    _ = (a s).val := hAp s

theorem regional_contact_has_finite_matching_planar_lift
    {S : Type} [TopologicalSpace S] {F : Set S}
    (p : Plane → S) (hp : IsCoveringMap p)
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (B : C(Interval,Plane))
    (hBp : ∀ t, p (B t) = (b t).val)
    (s t : Interval) (hst : a s = b t) :
    ∃ A : C(Interval,Plane),
      Topology.IsEmbedding A ∧ A s = B t ∧
      (∀ u, p (A u) = (a u).val) ∧
      (Set.range A ∩ Set.range B).Finite := by
  obtain ⟨A,hA,hAs,hAp⟩ :=
    regional_contact_has_matching_planar_lift p hp a b ha B hBp s t hst
  exact ⟨A,hA,hAs,hAp,
    regional_matching_lift_finite_contacts p a b A B hAp hBp ha hfinite⟩

/-- A finite family of lifts, one for each parameter contact on the first
    arc, represents every projected contact against the fixed second lift. -/
theorem regional_finite_matching_lift_family
    {S : Type} [TopologicalSpace S] {F : Set S}
    (p : Plane → S) (hp : IsCoveringMap p)
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (B : C(Interval,Plane))
    (hBp : ∀ t, p (B t) = (b t).val) :
    ∃ (T : Set Interval) (L : T → C(Interval,Plane)),
      T.Finite ∧
      (∀ s, Topology.IsEmbedding (L s)) ∧
      (∀ s u, p (L s u) = (a u).val) ∧
      (∀ s : T, ∃ t : Interval, L s s.val = B t ∧ a s.val = b t) ∧
      (∀ s t : Interval, a s = b t →
        B t ∈ ⋃ u : T, Set.range (L u)) ∧
      (∀ s : T, (Set.range (L s) ∩ Set.range B).Finite) := by
  classical
  let T : Set Interval := {s | a s ∈ Set.range b}
  have hT : T.Finite := regional_finite_contact_parameters a b ha hfinite
  have hchoose (s : T) :
      ∃ A : C(Interval,Plane),
        Topology.IsEmbedding A ∧
        (∀ u, p (A u) = (a u).val) ∧
        (∃ t : Interval, A s.val = B t ∧ a s.val = b t) ∧
        (Set.range A ∩ Set.range B).Finite := by
    obtain ⟨t,ht⟩ := s.property
    obtain ⟨A,hA,hAs,hAp,hfin⟩ :=
      regional_contact_has_finite_matching_planar_lift
        p hp a b ha hfinite B hBp s.val t ht.symm
    exact ⟨A,hA,hAp,⟨t,hAs,ht.symm⟩,hfin⟩
  let L (s : T) : C(Interval,Plane) := Classical.choose (hchoose s)
  have hL (s : T) := Classical.choose_spec (hchoose s)
  refine ⟨T,L,hT,(fun s => (hL s).1),(fun s u => (hL s).2.1 u),
    (fun s => (hL s).2.2.1),?_,(fun s => (hL s).2.2.2)⟩
  intro s t hst
  let u : T := ⟨s,⟨t,hst.symm⟩⟩
  obtain ⟨v,hLv,hav⟩ := (hL u).2.2.1
  have htv : t = v := by
    apply hb.injective
    exact hst.symm.trans hav
  exact Set.mem_iUnion.mpr ⟨u,⟨s,by simpa only [htv] using hLv⟩⟩

theorem regional_matching_lift_family_projects_all_contacts
    {S : Type} [TopologicalSpace S] {F : Set S}
    (p : Plane → S) (a b : C(Interval, ↥F))
    (B : C(Interval,Plane))
    (hBp : ∀ t, p (B t) = (b t).val)
    (T : Set Interval) (L : T → C(Interval,Plane))
    (hLp : ∀ s u, p (L s u) = (a u).val)
    (hcover : ∀ s t : Interval, a s = b t →
      B t ∈ ⋃ u : T, Set.range (L u)) :
    {z : S | ∃ s t : Interval, z = (a s).val ∧ a s = b t} =
      p '' (Set.range B ∩ ⋃ u : T, Set.range (L u)) := by
  ext z
  constructor
  · rintro ⟨s,t,rfl,hst⟩
    refine ⟨B t,⟨⟨t,rfl⟩,hcover s t hst⟩,?_⟩
    exact (hBp t).trans (congrArg Subtype.val hst.symm)
  · rintro ⟨w,⟨⟨t,ht⟩,hwL⟩,rfl⟩
    obtain ⟨u,⟨s,hs⟩⟩ := Set.mem_iUnion.mp hwL
    refine ⟨s,t,?_,?_⟩
    · calc
        p w = p (L u s) := by rw [hs]
        _ = (a s).val := hLp u s
    · apply Subtype.ext
      calc
        (a s).val = p (L u s) := (hLp u s).symm
        _ = p w := by rw [hs]
        _ = p (B t) := by rw [ht]
        _ = (b t).val := hBp t

theorem regional_finite_matching_lift_union_contacts
    (B : C(Interval,Plane))
    (T : Set Interval) (hT : T.Finite)
    (L : T → C(Interval,Plane))
    (hfinite : ∀ s : T, (Set.range (L s) ∩ Set.range B).Finite) :
    ((⋃ s : T, Set.range (L s)) ∩ Set.range B).Finite := by
  have : Finite T := hT.to_subtype
  have heq : (⋃ s : T, Set.range (L s)) ∩ Set.range B =
      ⋃ s : T, Set.range (L s) ∩ Set.range B := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  rw [heq]
  exact Set.finite_iUnion hfinite

end RegionalEmbeddedFamily
