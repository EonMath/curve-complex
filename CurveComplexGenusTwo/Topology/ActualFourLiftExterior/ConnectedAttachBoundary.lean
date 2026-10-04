import Mathlib.Topology.Connected.Basic

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem connected_union_of_boundary_attachment
    {X : Type} [TopologicalSpace X]
    (R A : Set X) (hR : IsConnected R) (hA : IsConnected A)
    (x : X) (hxA : x ∈ A) (hxR : x ∈ closure R) :
    IsConnected (R ∪ A) := by
  have hRpoint : IsConnected (R ∪ {x}) :=
    hR.subset_closure subset_union_left (by
      rintro y (hy | hy)
      · exact subset_closure hy
      · simpa only [mem_singleton_iff] using hy ▸ hxR)
  have hMeet : ((R ∪ {x}) ∩ A).Nonempty :=
    ⟨x,Or.inr (mem_singleton x),hxA⟩
  have h := IsConnected.union hMeet hRpoint hA
  convert h using 1
  ext y
  simp only [mem_union,mem_singleton_iff]
  have hyA : y = x → y ∈ A := by rintro rfl; exact hxA
  tauto

end CurveComplex.HyperellipticModel
