import Mathlib.Topology.Connected.LocallyConnected

namespace CurveComplex
open Set

/-- A dense connected subset fills any intermediate set. -/
theorem theta_connected_of_dense_connected
    {X : Type*} [TopologicalSpace X] {L U : Set X}
    (hL : IsConnected L) (hLU : L ⊆ U) (hU : U ⊆ closure L) :
    IsConnected U := hL.subset_closure hLU hU

/-- If an open set contains two connected dense pieces and a common limit point,
local connectedness joins those pieces inside the open set. -/
theorem theta_open_connected_of_common_limit
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {L R U : Set X} (hL : IsConnected L) (hR : IsConnected R)
    (hLU : L ⊆ U) (hRU : R ⊆ U) (hU : IsOpen U)
    (hd : U ⊆ closure (L ∪ R))
    {x : X} (hxU : x ∈ U) (hxL : x ∈ closure L) (hxR : x ∈ closure R) :
    IsConnected U := by
  let N := connectedComponentIn U x
  have hNopen : IsOpen N := hU.connectedComponentIn
  have hxN : x ∈ N := mem_connectedComponentIn hxU
  have hNconn : IsConnected N := isConnected_connectedComponentIn_iff.mpr hxU
  obtain ⟨l,hlN,hlL⟩ := mem_closure_iff.mp hxL N hNopen hxN
  obtain ⟨r,hrN,hrR⟩ := mem_closure_iff.mp hxR N hNopen hxN
  have hLN : IsConnected (L ∪ N) := hL.union ⟨l,hlL,hlN⟩ hNconn
  have hLNR : IsConnected ((L ∪ N) ∪ R) :=
    hLN.union ⟨r,Or.inr hrN,hrR⟩ hR
  apply hLNR.subset_closure
  · exact union_subset (union_subset hLU (connectedComponentIn_subset U x)) hRU
  · have hsub : L ∪ R ⊆ (L ∪ N) ∪ R := by
      intro z hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inl hz)
      · exact Or.inr hz
    exact hd.trans (closure_mono hsub)

/-- The elementary component-count step of theta retention. An open cover of a
connected set with a common dense core consisting of two connected pieces has
a connected member. -/
theorem theta_open_cover_connected_member
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {Y U V L R : Set X}
    (hY : IsConnected Y) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Y)
    (hL : IsConnected L) (hR : IsConnected R)
    (hLU : L ⊆ U) (hLV : L ⊆ V) (hRU : R ⊆ U) (hRV : R ⊆ V)
    (hd : Y ⊆ closure (L ∪ R)) :
    IsConnected U ∨ IsConnected V := by
  have hUY : U ⊆ Y := by rw [← hcover]; exact subset_union_left
  have hVY : V ⊆ Y := by rw [← hcover]; exact subset_union_right
  have hYcover : Y ⊆ closure L ∪ closure R := by
    rw [← closure_union]; exact hd
  obtain ⟨x,hxY,hxL,hxR⟩ := isPreconnected_closed_iff.mp hY.isPreconnected
    (closure L) (closure R) isClosed_closure isClosed_closure hYcover
    (by obtain ⟨l,hl⟩ := hL.nonempty; exact ⟨l,hUY (hLU hl),subset_closure hl⟩)
    (by obtain ⟨r,hr⟩ := hR.nonempty; exact ⟨r,hUY (hRU hr),subset_closure hr⟩)
  have hxUV : x ∈ U ∪ V := hcover.symm ▸ hxY
  rcases hxUV with hxU | hxV
  · exact Or.inl (theta_open_connected_of_common_limit hL hR hLU hRU hU
      (hUY.trans hd) hxU hxL hxR)
  · exact Or.inr (theta_open_connected_of_common_limit hL hR hLV hRV hV
      (hVY.trans hd) hxV hxL hxR)

end CurveComplex
#print axioms CurveComplex.theta_open_cover_connected_member
