import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenToConstructedCommonPairLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies

-- Identify the source-produced facing side with a given model facing side.
example {X : Type} [TopologicalSpace X] (C D U V P Q : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hP : IsOpen P) (hQ : IsOpen Q)
    (hcU : IsConnected U) (hcV : IsConnected V)
    (hcP : IsConnected P) (hcQ : IsConnected Q)
    (hdUV : Disjoint U V) (hdPQ : Disjoint P Q)
    (hcoverUV : U ∪ V=Cᶜ) (hcoverPQ : P ∪ Q=Cᶜ)
    (hD : D.Nonempty) (hDU : D ⊆ U) (hDP : D ⊆ P) : U=P ∧ V=Q := by
  audit_main14_base3
    have hUP : U ⊆ P := by
      have hs : U ⊆ P ∪ Q := by rw [hcoverPQ,←hcoverUV];exact Set.subset_union_left
      rcases hcU.isPreconnected.subset_or_subset hP hQ hdPQ hs with hp | hq
      · exact hp
      · obtain ⟨x,hx⟩ := hD
        exact False.elim (Set.disjoint_left.mp hdPQ (hDP hx) (hq (hDU hx)))
    have hPU : P ⊆ U := by
      have hs : P ⊆ U ∪ V := by rw [hcoverUV,←hcoverPQ];exact Set.subset_union_left
      rcases hcP.isPreconnected.subset_or_subset hU hV hdUV hs with hu | hv
      · exact hu
      · obtain ⟨x,hx⟩ := hD
        exact False.elim (Set.disjoint_left.mp hdUV (hDU hx) (hv (hDP hx)))
    have he : U=P := Set.Subset.antisymm hUP hPU
    refine ⟨he,?_⟩
    apply Set.Subset.antisymm
    · intro x hx
      have hxc : x ∈ Cᶜ := hcoverUV ▸ Or.inr hx
      have hs : x ∈ P ∪ Q := hcoverPQ.symm ▸ hxc
      exact hs.resolve_left (fun hp => Set.disjoint_left.mp hdUV (he.symm ▸ hp) hx)
    · intro x hx
      have hxc : x ∈ Cᶜ := hcoverPQ ▸ Or.inr hx
      have hs : x ∈ U ∪ V := hcoverUV.symm ▸ hxc
      exact hs.resolve_left (fun hu => Set.disjoint_left.mp hdPQ (he ▸ hu) hx)
end CurveComplex.HyperellipticModel
