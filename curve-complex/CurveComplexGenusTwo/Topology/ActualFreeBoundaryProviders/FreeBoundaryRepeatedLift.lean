import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullFromReturn
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryReturnCore

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily FreeBoundaryNullGeometry

/-- Any repeated intersection with one lift, in the actual separating cover,
forces an ordinary null bigon even when the original endpoints are free. -/
theorem free_boundary_repeated_lift_gives_null_bigon
    {S X : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace X] [T2Space X] [SimplyConnectedSpace X]
    {Q : Set S} (B : Set ↥Q)
    (p : X → ↥Q) (hp : IsCoveringMap p)
    (a b : C(Interval,↥Q)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hends : a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B)
    (hdis : Disjoint ({a 0,a 1} : Set ↥Q) {b 0,b 1})
    (hfinite : (range a ∩ range b).Finite)
    (hcross : RegionalAllInteriorContactsCross Q a b)
    (hsep : ∀ A : C(Interval,X), (∀ t, p (A t) = a t) →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
        U ∪ V = (range A)ᶜ ∧ frontier U = range A ∧ frontier V = range A)
    (D : C(Interval,X)) (hDp : ∀ t, p (D t) = b t)
    (A₀ : C(Interval,X)) (hA₀p : ∀ t, p (A₀ t) = a t)
    (l₀ r₀ : Interval) (hlr₀ : l₀ < r₀)
    (hl₀ : D l₀ ∈ range A₀) (hr₀ : D r₀ ∈ range A₀) :
    Nonempty (NullBigonBoundary B a b) := by
  obtain ⟨K,hKemb,hKp,hKdis,hcover⟩ :=
    contact_finite_disjoint_lift_family p hp a b ha hb hfinite D hDp
  have hA₀ : A₀ ∈ K := by
    obtain ⟨s,hs⟩ := hl₀
    have hbase : b l₀ ∈ range a := ⟨s,(hA₀p s).symm.trans ((congrArg p hs).trans (hDp l₀))⟩
    obtain ⟨A,hA,hDA⟩ := (hcover l₀).mp hbase
    have he : A₀ = A := contact_arc_lifts_equal_of_contact p hp a ha.injective A₀ A
      hA₀p (hKp A hA) ⟨D l₀,⟨s,hs⟩,hDA⟩
    exact he ▸ hA
  have hf : {t : Interval | ∃ A ∈ K, D t ∈ range A}.Finite := by
    have hbf := regional_finite_contact_parameters b a hb (by simpa only [inter_comm] using hfinite)
    exact hbf.subset fun t ht => (hcover t).mpr ht
  have hswitch : ∀ A ∈ K, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range A)ᶜ ∧
      ∀ t : Interval, t ∈ Ioo (0 : Interval) 1 → D t ∈ range A →
        ∀ l r : Interval, l < t → t < r →
          ∃ u v : Interval, l < u ∧ u < t ∧ t < v ∧ v < r ∧
            ((D u ∈ U ∧ D v ∈ V) ∨ (D u ∈ V ∧ D v ∈ U)) := by
    intro A hA
    obtain ⟨U,V,hU,hV,hUV,hcov,hfu,hfv⟩ := hsep A (hKp A hA)
    refine ⟨U,V,hU,hV,hUV,hcov,?_⟩
    intro t ht hAt
    obtain ⟨s,hs⟩ := hAt
    have hst : a s = b t := (hKp A hA s).symm.trans ((congrArg p hs).trans (hDp t))
    have hsI := (free_boundary_contact_parameters_interior B a b hends hproper hdis s t hst).1
    obtain ⟨C,hC⟩ := hcross s t hsI ht hst
    exact regional_crossing_lift_switches_separating_sides p hp a b ha A D
      (hKp A hA) hDp s t hs C hC U V hU hV hUV hcov hfu hfv
  obtain ⟨A,hA,l,r,hlr,hl,hr,hgap⟩ := free_contact_finite_separating_family_has_clean_return
    D K hf hKdis hswitch A₀ hA₀ l₀ r₀ hlr₀ hl₀ hr₀
  apply free_boundary_clean_return_gives_null_bigon B p hp.continuous a b ha hb
    hends hproper hdis A D (hKp A hA) hDp l r hlr hl hr
  intro u hlu hur hu
  obtain ⟨C,hC,huC⟩ := (hcover u).mp hu
  exact hgap u hlu hur C hC huC

end CoherentEndpointMotion.FreeBoundaryContactRepair
