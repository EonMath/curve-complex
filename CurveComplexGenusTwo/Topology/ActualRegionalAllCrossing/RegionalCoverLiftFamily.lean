import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalFiniteContactParameters
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingCoverTransfer

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- Two lifts of the same embedded parameterized interval agree as soon as
their images meet. -/
theorem contact_arc_lifts_equal_of_contact
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsCoveringMap p)
    (a : C(Interval,Y)) (ha : Function.Injective a)
    (A D : C(Interval,X)) (hA : ∀ t, p (A t) = a t) (hD : ∀ t, p (D t) = a t)
    (hm : (Set.range A ∩ Set.range D).Nonempty) : A = D := by
  obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hm
  have hst : s = t := ha ((hA s).symm.trans
    ((congrArg p (hs.trans ht.symm)).trans (hD t)))
  apply ContinuousMap.coe_injective
  apply hp.eq_of_comp_eq A.continuous D.continuous
    (funext fun u => (hA u).trans (hD u).symm) s
  exact hs.trans (by simpa only [hst] using ht.symm)

/-- Construct, in any actual cover, the finite disjoint family of all lifts
meeting the fixed second lift, with exact projected-contact detection. -/
theorem contact_finite_disjoint_lift_family
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsCoveringMap p)
    (a b : C(Interval,Y)) (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (B : C(Interval,X)) (hBp : ∀ t, p (B t) = b t) :
    ∃ K : Finset C(Interval,X),
      (∀ A ∈ K, Topology.IsEmbedding A) ∧
      (∀ A ∈ K, ∀ t, p (A t) = a t) ∧
      (∀ A ∈ K, ∀ D ∈ K, A ≠ D → Disjoint (Set.range A) (Set.range D)) ∧
      (∀ t, b t ∈ Set.range a ↔ ∃ A ∈ K, B t ∈ Set.range A) := by
  classical
  let T : Set Interval := {t | b t ∈ Set.range a}
  have hT : T.Finite := hfinite.of_injOn
    (show Set.MapsTo b T (Set.range a ∩ Set.range b) from
      fun t ht => ⟨ht,Set.mem_range_self _⟩)
    (fun s _ t _ he => hb.injective he)
  have hlift (t : T) : ∃ A : C(Interval,X),
      (∀ u, p (A u) = a u) ∧ B t.val ∈ Set.range A := by
    obtain ⟨s,hs⟩ := t.property
    let : ContractibleSpace Interval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    let : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
    obtain ⟨A,hA,_⟩ := hp.existsUnique_continuousMap_lifts a s (B t.val)
      ((hBp t.val).trans hs.symm)
    exact ⟨A,fun u => congrFun hA.2 u,⟨s,hA.1⟩⟩
  choose L hLp hLm using hlift
  let : Finite T := hT.to_subtype
  have hK : (Set.range L).Finite := Set.finite_range L
  let K := hK.toFinset
  have hmem (A : C(Interval,X)) : A ∈ K ↔ ∃ t, L t = A := by
    simp only [K,Set.Finite.mem_toFinset,Set.mem_range]
  have hproj (A : C(Interval,X)) (hA : A ∈ K) (t : Interval) : p (A t) = a t := by
    obtain ⟨s,rfl⟩ := (hmem A).mp hA
    exact hLp s t
  refine ⟨K,?_,hproj,?_,?_⟩
  · intro A hA
    apply Topology.IsEmbedding.of_comp A.continuous hp.continuous
    have he : p ∘ (A : Interval → X) = a := funext (hproj A hA)
    rw [he]
    exact ha
  · intro A hA D hD hne
    apply Set.disjoint_left.mpr
    intro z hzA hzD
    exact hne (contact_arc_lifts_equal_of_contact p hp a ha.injective A D
      (hproj A hA) (hproj D hD) ⟨z,hzA,hzD⟩)
  · intro t
    constructor
    · intro ht
      exact ⟨L ⟨t,ht⟩,(hmem _).mpr ⟨⟨t,ht⟩,rfl⟩,hLm ⟨t,ht⟩⟩
    · rintro ⟨A,hA,s,hs⟩
      exact ⟨s,(hproj A hA s).symm.trans ((congrArg p hs).trans (hBp t))⟩

/-- Lift the original endpoint-relative homotopy through an actual covering
of its codomain, retaining both common lifted endpoints. -/
theorem contact_homotopic_pair_has_matched_lifts
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (a b : C(Interval,Y))
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hhom : Path.Homotopic
      (⟨a,rfl,rfl⟩ : Path (a 0) (a 1)) (⟨b,h0,h1⟩ : Path (a 0) (a 1))) :
    ∃ A B : C(Interval,X),
      (∀ t, p (A t) = a t) ∧ (∀ t, p (B t) = b t) ∧
      A 0 = B 0 ∧ A 1 = B 1 := by
  obtain ⟨z,hz⟩ := hsurj (a 0)
  let A := hp.liftPath a z hz.symm
  have hbz : b 0 = p z := h0.trans hz.symm
  let B := hp.liftPath b z hbz
  refine ⟨A,B,fun t => congrFun (hp.liftPath_lifts a z hz.symm) t,
    fun t => congrFun (hp.liftPath_lifts b z hbz) t,?_,?_⟩
  · exact (hp.liftPath_zero a z hz.symm).trans (hp.liftPath_zero b z hbz).symm
  · exact hp.liftPath_apply_one_eq_of_homotopicRel hhom z hz.symm hbz

/-- In a cover with genuinely separating proper lifts, the approved
all-crossing geometry eliminates every singleton obstruction to a clean
return. No nullity of the ambient surface cover is used. -/
theorem regional_all_crossing_has_clean_return_in_separating_cover
    {S X : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace X]
    {F : Set S} (p : X → ↥F) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (a b : C(Interval, ↥F)) (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hhom : Path.Homotopic
      (⟨a,rfl,rfl⟩ : Path (a 0) (a 1)) (⟨b,h0,h1⟩ : Path (a 0) (a 1)))
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (hcross : RegionalAllInteriorContactsCross F a b)
    (hsep : ∀ A : C(Interval,X), (∀ t, p (A t) = a t) →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
        U ∪ V = (Set.range A)ᶜ ∧ frontier U = Set.range A ∧ frontier V = Set.range A) :
    ∃ (A B : C(Interval,X)) (l r : Interval),
      (∀ t, p (A t) = a t) ∧ (∀ t, p (B t) = b t) ∧
      l < r ∧ B l ∈ Set.range A ∧ B r ∈ Set.range A ∧
      ∀ u : Interval, l < u → u < r → b u ∉ Set.range a := by
  obtain ⟨A₀,B,hA₀p,hBp,hzero,hone⟩ :=
    contact_homotopic_pair_has_matched_lifts p hp hsurj a b h0 h1 hhom
  obtain ⟨K,hKemb,hKp,hKdis,hcover⟩ :=
    contact_finite_disjoint_lift_family p hp a b ha hb hfinite B hBp
  have hA₀ : A₀ ∈ K := by
    obtain ⟨A,hA,s,hs⟩ := (hcover 0).mp ⟨0,h0.symm⟩
    have he : A₀ = A := contact_arc_lifts_equal_of_contact p hp a ha.injective A₀ A
      hA₀p (hKp A hA) ⟨B 0,⟨0,hzero⟩,⟨s,hs⟩⟩
    exact he ▸ hA
  have hf : {t : Interval | ∃ A ∈ K, B t ∈ Set.range A}.Finite := by
    have hbf := regional_finite_contact_parameters b a hb (by simpa only [inter_comm] using hfinite)
    exact hbf.subset fun t ht => (hcover t).mpr ht
  have hswitch : ∀ A ∈ K, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (Set.range A)ᶜ ∧
      ∀ t : Interval, t ∈ Set.Ioo (0 : Interval) 1 → B t ∈ Set.range A →
        ∀ l r : Interval, l < t → t < r →
          ∃ u v : Interval, l < u ∧ u < t ∧ t < v ∧ v < r ∧
            ((B u ∈ U ∧ B v ∈ V) ∨ (B u ∈ V ∧ B v ∈ U)) := by
    intro A hA
    obtain ⟨U,V,hU,hV,hdis,hcov,hfu,hfv⟩ := hsep A (hKp A hA)
    refine ⟨U,V,hU,hV,hdis,hcov,?_⟩
    intro t ht hAt
    obtain ⟨s,hs⟩ := hAt
    have hst : a s = b t := (hKp A hA s).symm.trans ((congrArg p hs).trans (hBp t))
    have hs0 : s ≠ 0 := by
      intro he
      have htb : b t = b 0 := hst.symm.trans (he ▸ h0.symm)
      exact ht.1.ne' (hb.injective htb)
    have hs1 : s ≠ 1 := by
      intro he
      have htb : b t = b 1 := hst.symm.trans (he ▸ h1.symm)
      exact ht.2.ne (hb.injective htb)
    have hsI : s ∈ Set.Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne s.property.1 (Ne.symm hs0),lt_of_le_of_ne s.property.2 hs1⟩
    obtain ⟨C,hC⟩ := hcross s t hsI ht hst
    exact regional_crossing_lift_switches_separating_sides p hp a b ha A B
      (hKp A hA) hBp s t hs C hC U V hU hV hdis hcov hfu hfv
  obtain ⟨A,hA,l,r,hlr,hl,hr,hgap⟩ := contact_finite_separating_family_has_clean_return
    B K hf hKdis hswitch A₀ hA₀ ⟨0,hzero⟩ ⟨1,hone⟩
  refine ⟨A,B,l,r,hKp A hA,hBp,hlr,hl,hr,?_⟩
  intro u hlu hur hu
  obtain ⟨D,hD,huD⟩ := (hcover u).mp hu
  exact hgap u hlu hur D hD huD

end RegionalEmbeddedFamily
