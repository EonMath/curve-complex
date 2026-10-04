import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceComponentBridge

namespace CurveComplex
open Set
variable {X : Type*} [TopologicalSpace X]

/-- A local two-track neighborhood. At an endpoint the two tracks may coincide.
The closure condition concerns every point of the deleted set inside the open
neighborhood, so overlap propagation requires no orientation choices. -/
structure SurfaceLocalSides (D P : Set X) where
  nbhd : Set X
  left : Set X
  right : Set X
  isOpen_nbhd : IsOpen nbhd
  nbhd_subset : nbhd ⊆ D
  nbhd_diff : nbhd \ P = left ∪ right
  connected_left : IsConnected left
  connected_right : IsConnected right
  limit_left : nbhd ∩ P ⊆ closure left
  limit_right : nbhd ∩ P ⊆ closure right

namespace SurfaceLocalSides
variable {D P : Set X}

theorem left_subset_diff (C : SurfaceLocalSides D P) : C.left ⊆ D \ P := by
  intro x hx
  have hn : x ∈ C.nbhd \ P := by rw [C.nbhd_diff]; exact Or.inl hx
  exact ⟨C.nbhd_subset hn.1,hn.2⟩

theorem right_subset_diff (C : SurfaceLocalSides D P) : C.right ⊆ D \ P := by
  intro x hx
  have hn : x ∈ C.nbhd \ P := by rw [C.nbhd_diff]; exact Or.inr hx
  exact ⟨C.nbhd_subset hn.1,hn.2⟩

/-- Membership in two fixed complementary components propagates through any
local two-track neighborhood that overlaps on the deleted set. -/
theorem covered_of_overlap (C B : SurfaceLocalSides D P) {z l r : X}
    (hzC : z ∈ C.nbhd) (hzB : z ∈ B.nbhd) (hzP : z ∈ P)
    (hC : C.nbhd \ P ⊆ connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) r) :
    B.nbhd \ P ⊆ connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) r := by
  have htrack : ∀ T : Set X, IsConnected T → T ⊆ D \ P → z ∈ closure T →
      T ⊆ connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) r := by
    intro T hT hTD hzT
    obtain ⟨w,hwC,hwT⟩ := mem_closure_iff.mp hzT C.nbhd C.isOpen_nbhd hzC
    have hwA := hC ⟨hwC,(hTD hwT).2⟩
    rcases hwA with hwA | hwA
    · have heq := connectedComponentIn_eq hwA
      have hsub := hT.isPreconnected.subset_connectedComponentIn hwT hTD
      exact fun x hx => Or.inl (by rw [heq]; exact hsub hx)
    · have heq := connectedComponentIn_eq hwA
      have hsub := hT.isPreconnected.subset_connectedComponentIn hwT hTD
      exact fun x hx => Or.inr (by rw [heq]; exact hsub hx)
  rw [B.nbhd_diff]
  exact union_subset
    (htrack B.left B.connected_left B.left_subset_diff (B.limit_left ⟨hzB,hzP⟩))
    (htrack B.right B.connected_right B.right_subset_diff (B.limit_right ⟨hzB,hzP⟩))

end SurfaceLocalSides

/-- Local two-track neighborhoods suffice for global component exhaustion.
Connectedness of the deleted interior propagates the component choices; no
single chart or whole-arc collar is required. -/
theorem theta_at_most_two_of_local_sides
    [LocallyConnectedSpace X] {D P : Set X}
    (hD : IsOpen D) (hDc : IsPreconnected D) (hP : IsClosed P)
    (hK : IsConnected (D ∩ P))
    (hlocal : ∀ x ∈ D ∩ P, ∃ C : SurfaceLocalSides D P, x ∈ C.nbhd) :
    ∃ l ∈ D \ P, ∃ r ∈ D \ P, ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) l ∨ x ∈ connectedComponentIn (D \ P) r := by
  classical
  obtain ⟨x0,hx0⟩ := hK.nonempty
  let C : ∀ x : ↥(D ∩ P), SurfaceLocalSides D P := fun x => Classical.choose (hlocal x x.property)
  have hxC (x : ↥(D ∩ P)) : (x:X) ∈ (C x).nbhd := Classical.choose_spec (hlocal x x.property)
  let c0 := C ⟨x0,hx0⟩
  let l := c0.connected_left.nonempty.some
  let r := c0.connected_right.nonempty.some
  have hl : l ∈ c0.left := c0.connected_left.nonempty.some_mem
  have hr : r ∈ c0.right := c0.connected_right.nonempty.some_mem
  let A := connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) r
  let good := fun x : ↥(D ∩ P) => (C x).nbhd \ P ⊆ A
  have hc0 : good ⟨x0,hx0⟩ := by
    change c0.nbhd \ P ⊆ A
    rw [c0.nbhd_diff]
    exact union_subset
      (fun z hz => Or.inl (c0.connected_left.isPreconnected.subset_connectedComponentIn hl c0.left_subset_diff hz))
      (fun z hz => Or.inr (c0.connected_right.isPreconnected.subset_connectedComponentIn hr c0.right_subset_diff hz))
  let G : Set X := ⋃₀ {(C x).nbhd | (x : ↥(D ∩ P)) (_ : good x)}
  let H : Set X := ⋃₀ {(C x).nbhd | (x : ↥(D ∩ P)) (_ : ¬ good x)}
  have hG : IsOpen G := isOpen_sUnion (by rintro U ⟨x,hx,rfl⟩; exact (C x).isOpen_nbhd)
  have hH : IsOpen H := isOpen_sUnion (by rintro U ⟨x,hx,rfl⟩; exact (C x).isOpen_nbhd)
  have hcover : D ∩ P ⊆ G ∪ H := by
    intro x hx
    by_cases hg : good ⟨x,hx⟩
    · exact Or.inl ⟨(C ⟨x,hx⟩).nbhd,⟨⟨x,hx⟩,hg,rfl⟩,hxC ⟨x,hx⟩⟩
    · exact Or.inr ⟨(C ⟨x,hx⟩).nbhd,⟨⟨x,hx⟩,hg,rfl⟩,hxC ⟨x,hx⟩⟩
  have hall : ∀ x, good x := by
    intro x
    by_contra hx
    obtain ⟨z,hzK,hzG,hzH⟩ := hK.isPreconnected G H hG hH hcover
      ⟨x0,hx0,(C ⟨x0,hx0⟩).nbhd,⟨⟨x0,hx0⟩,hc0,rfl⟩,hxC ⟨x0,hx0⟩⟩
      ⟨x,x.property,(C x).nbhd,⟨x,hx,rfl⟩,hxC x⟩
    obtain ⟨U,⟨u,hu,rfl⟩,hzU⟩ := hzG
    obtain ⟨V,⟨v,hv,rfl⟩,hzV⟩ := hzH
    exact hv ((C u).covered_of_overlap (C v) hzU hzV hzK.2 hu)
  refine ⟨l,c0.left_subset_diff hl,r,c0.right_subset_diff hr,?_⟩
  intro x hx
  exact theta_covered_by_two_of_local hD hDc hP (c0.left_subset_diff hl)
    (fun w hw => ⟨(C ⟨w,hw⟩).nbhd,(C ⟨w,hw⟩).isOpen_nbhd,hxC ⟨w,hw⟩,
      (C ⟨w,hw⟩).nbhd_subset,hall ⟨w,hw⟩⟩) hx

end CurveComplex
#print axioms CurveComplex.theta_at_most_two_of_local_sides
