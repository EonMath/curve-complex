import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCoverLiftFamily
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryReturnCore

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily

/-- Finite contact times, with no embedding assumption on the moving track,
give the finite family of all lifts met by that track. -/
theorem free_finite_event_disjoint_lift_family
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsCoveringMap p)
    (a : C(Interval,Y)) (ha : IsEmbedding a)
    (Γ : C(Interval,X))
    (hfinite : {t : Interval | p (Γ t) ∈ range a}.Finite) :
    ∃ K : Finset C(Interval,X),
      (∀ A ∈ K, IsEmbedding A) ∧
      (∀ A ∈ K, ∀ t, p (A t) = a t) ∧
      (∀ A ∈ K, ∀ D ∈ K, A ≠ D → Disjoint (range A) (range D)) ∧
      (∀ t, p (Γ t) ∈ range a ↔ ∃ A ∈ K, Γ t ∈ range A) := by
  classical
  let T : Set Interval := {t | p (Γ t) ∈ range a}
  have hlift (t : T) : ∃ A : C(Interval,X),
      (∀ u, p (A u) = a u) ∧ Γ t.val ∈ range A := by
    obtain ⟨s,hs⟩ := t.property
    let : ContractibleSpace Interval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    let : LocallyPathConnectedSpace Interval :=
      (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
    obtain ⟨A,hA,_⟩ := hp.existsUnique_continuousMap_lifts a s (Γ t.val) hs.symm
    exact ⟨A,fun u => congrFun hA.2 u,⟨s,hA.1⟩⟩
  choose L hLp hLm using hlift
  let : Finite T := hfinite.to_subtype
  have hK : (range L).Finite := Set.finite_range L
  let K := hK.toFinset
  have hmem (A : C(Interval,X)) : A ∈ K ↔ ∃ t, L t = A := by
    simp only [K,Set.Finite.mem_toFinset,Set.mem_range]
  have hproj (A : C(Interval,X)) (hA : A ∈ K) (t : Interval) : p (A t) = a t := by
    obtain ⟨s,rfl⟩ := (hmem A).mp hA
    exact hLp s t
  refine ⟨K,?_,hproj,?_,?_⟩
  · intro A hA
    apply IsEmbedding.of_comp A.continuous hp.continuous
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
      exact ⟨s,(hproj A hA s).symm.trans (congrArg p hs)⟩

/-- Exact detection includes any actual lift that meets the track, so a
caller-supplied seed lift is retained without changing its identity. -/
theorem free_detected_lift_mem_family
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsCoveringMap p)
    (a : C(Interval,Y)) (ha : Function.Injective a)
    (Γ : C(Interval,X)) (K : Finset C(Interval,X))
    (hKp : ∀ A ∈ K, ∀ t, p (A t) = a t)
    (hdetect : ∀ t, p (Γ t) ∈ range a ↔ ∃ A ∈ K, Γ t ∈ range A)
    (A : C(Interval,X)) (hAp : ∀ t, p (A t) = a t)
    (t : Interval) (ht : Γ t ∈ range A) : A ∈ K := by
  obtain ⟨s,hs⟩ := ht
  have hproject : p (Γ t) ∈ range a :=
    ⟨s,(hAp s).symm.trans (congrArg p hs)⟩
  obtain ⟨D,hD,hΓD⟩ := (hdetect t).mp hproject
  have he : A = D := contact_arc_lifts_equal_of_contact p hp a ha A D
    hAp (hKp D hD) ⟨Γ t,⟨s,hs⟩,hΓD⟩
  exact he ▸ hD

/-- The generic finite-event adapter gives a return clean against the whole
projected arc. Separator switching and the repeated seed contact are explicit
inputs; the moving track may be a concatenation with self-intersections. -/
theorem free_finite_event_separating_cover_clean_return
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsCoveringMap p)
    (a : C(Interval,Y)) (ha : IsEmbedding a)
    (Γ : C(Interval,X))
    (hfinite : {t : Interval | p (Γ t) ∈ range a}.Finite)
    (hswitch : ∀ A : C(Interval,X), (∀ t, p (A t) = a t) →
      ∃ U V : Set X,
        IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range A)ᶜ ∧
        ∀ t : Interval, t ∈ Ioo (0 : Interval) 1 → Γ t ∈ range A →
          ∀ l r : Interval, l < t → t < r →
            ∃ u v : Interval, l < u ∧ u < t ∧ t < v ∧ v < r ∧
              ((Γ u ∈ U ∧ Γ v ∈ V) ∨ (Γ u ∈ V ∧ Γ v ∈ U)))
    (A₀ : C(Interval,X)) (hA₀p : ∀ t, p (A₀ t) = a t)
    (l₀ r₀ : Interval) (hlr₀ : l₀ < r₀)
    (hl₀ : Γ l₀ ∈ range A₀) (hr₀ : Γ r₀ ∈ range A₀) :
    ∃ (A : C(Interval,X)) (l r : Interval),
      (∀ t, p (A t) = a t) ∧ l < r ∧
      Γ l ∈ range A ∧ Γ r ∈ range A ∧
      ∀ u : Interval, l < u → u < r → p (Γ u) ∉ range a := by
  obtain ⟨K,_,hKp,hdis,hdetect⟩ :=
    free_finite_event_disjoint_lift_family p hp a ha Γ hfinite
  have hA₀ : A₀ ∈ K :=
    free_detected_lift_mem_family p hp a ha.injective Γ K hKp hdetect A₀ hA₀p l₀ hl₀
  have hf : {t : Interval | ∃ A ∈ K, Γ t ∈ range A}.Finite :=
    hfinite.subset fun t ht => (hdetect t).mpr ht
  obtain ⟨A,hA,l,r,hlr,hl,hr,hgap⟩ :=
    free_contact_finite_separating_family_has_clean_return Γ K hf hdis
      (fun A hA => hswitch A (hKp A hA)) A₀ hA₀ l₀ r₀ hlr₀ hl₀ hr₀
  refine ⟨A,l,r,hKp A hA,hlr,hl,hr,?_⟩
  intro u hlu hur hu
  obtain ⟨D,hD,huD⟩ := (hdetect u).mp hu
  exact hgap u hlu hur D hD huD

end CoherentEndpointMotion.FreeBoundaryContactRepair
