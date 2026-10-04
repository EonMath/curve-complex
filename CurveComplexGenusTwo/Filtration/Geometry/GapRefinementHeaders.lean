import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
namespace CurveComplex.HyperellipticModel
open Set
variable {X : Type} [TopologicalSpace X]

theorem complementComponent_refinement {A B U : Set X} (hAB : A ⊆ B)
    (hU : IsComplementComponent A U) (ho : IsOpen U)
    (hempty : interior B = ∅) :
    ∃ V : Set X, IsComplementComponent B V ∧ V ⊆ U := by
  have hx : (U \ B).Nonempty := by
    by_contra hn
    have hUB : U ⊆ B := by
      intro x hx
      by_contra hxb
      exact hn ⟨x, hx, hxb⟩
    have hUI : U ⊆ interior B := by
      simpa only [ho.interior_eq] using interior_mono hUB
    obtain ⟨x, hx⟩ := hU.1
    simpa only [hempty, mem_empty_iff_false] using hUI hx
  obtain ⟨x, hxU, hxB⟩ := hx
  let V := connectedComponentIn Bᶜ x
  have hv : IsComplementComponent B V :=
    complementComponent_iff_componentIn.mpr ⟨x, hxB, rfl⟩
  have hVAc : V ⊆ Aᶜ := fun y hy ha => hv.2.2.1 hy (hAB ha)
  have hVA : V ⊆ connectedComponentIn Aᶜ x :=
    hv.2.1.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hxB) hVAc
  have hUA : U = connectedComponentIn Aᶜ x :=
    (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hU.2.2.1 hxU))
      (hU.2.1.isPreconnected.subset_connectedComponentIn hxU hU.2.2.1)
      (connectedComponentIn_subset _ _)).symm
  exact ⟨V, hv, hUA.symm ▸ hVA⟩

theorem two_complementComponents_refinement {A B U W : Set X} (hAB : A ⊆ B)
    (hU : IsComplementComponent A U) (hW : IsComplementComponent A W)
    (hoU : IsOpen U) (hoW : IsOpen W) (hd : Disjoint U W)
    (hempty : interior B = ∅) :
    ∃ V Z : Set X, IsComplementComponent B V ∧ IsComplementComponent B Z ∧
      V ⊆ U ∧ Z ⊆ W ∧ Disjoint V Z ∧ V ≠ Z := by
  have hrefine : ∀ U : Set X, IsComplementComponent A U → IsOpen U →
      ∃ V : Set X, IsComplementComponent B V ∧ V ⊆ U := by
    intro U hU ho
    have hx : (U \ B).Nonempty := by
      by_contra hn
      have hUB : U ⊆ B := by
        intro x hx
        by_contra hxb
        exact hn ⟨x, hx, hxb⟩
      have hUI : U ⊆ interior B := by
        simpa only [ho.interior_eq] using interior_mono hUB
      obtain ⟨x, hx⟩ := hU.1
      simpa only [hempty, mem_empty_iff_false] using hUI hx
    obtain ⟨x, hxU, hxB⟩ := hx
    let V := connectedComponentIn Bᶜ x
    have hv : IsComplementComponent B V :=
      complementComponent_iff_componentIn.mpr ⟨x, hxB, rfl⟩
    have hVAc : V ⊆ Aᶜ := fun y hy ha => hv.2.2.1 hy (hAB ha)
    have hVA : V ⊆ connectedComponentIn Aᶜ x :=
      hv.2.1.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hxB) hVAc
    have hUA : U = connectedComponentIn Aᶜ x :=
      (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hU.2.2.1 hxU))
        (hU.2.1.isPreconnected.subset_connectedComponentIn hxU hU.2.2.1)
        (connectedComponentIn_subset _ _)).symm
    exact ⟨V, hv, hUA.symm ▸ hVA⟩
  obtain ⟨V, hV, hVU⟩ := hrefine U hU hoU
  obtain ⟨Z, hZ, hZW⟩ := hrefine W hW hoW
  have hdisj : Disjoint V Z := hd.mono hVU hZW
  refine ⟨V, Z, hV, hZ, hVU, hZW, hdisj, ?_⟩
  intro heq
  obtain ⟨x, hx⟩ := hV.1
  exact Set.disjoint_left.mp hdisj hx (heq ▸ hx)

end CurveComplex.HyperellipticModel
