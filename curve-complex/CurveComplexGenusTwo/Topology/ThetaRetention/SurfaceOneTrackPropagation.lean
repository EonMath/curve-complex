import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceLocalSides
namespace CurveComplex
open Set
variable {X : Type*} [TopologicalSpace X]
theorem theta_exhaustion_from_start_local_sides
    [LocallyConnectedSpace X] {D P : Set X}
    (hD : IsOpen D) (hDc : IsPreconnected D) (hP : IsClosed P)
    (hK : IsConnected (D ∩ P))
    (hlocal : ∀ x ∈ D ∩ P, ∃ C : SurfaceLocalSides D P, x ∈ C.nbhd)
    (C0 : SurfaceLocalSides D P) (x0 : X) (hx0 : x0 ∈ D ∩ P) (hstart : x0 ∈ C0.nbhd)
    (l r : X) (hl : l ∈ D \ P)
    (hC0 : C0.nbhd \ P ⊆ connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) r) :
    ∀ x ∈ D \ P,
      x ∈ connectedComponentIn (D \ P) l ∨ x ∈ connectedComponentIn (D \ P) r := by
  classical
  let C : ∀ x : ↥(D ∩ P), SurfaceLocalSides D P := fun x =>
    if h : (x:X) = x0 then C0 else Classical.choose (hlocal x x.property)
  have hxC (x : ↥(D ∩ P)) : (x:X) ∈ (C x).nbhd := by
    dsimp [C]
    split
    · rename_i he
      exact he ▸ hstart
    · exact Classical.choose_spec (hlocal x x.property)
  let A := connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) r
  let good := fun x : ↥(D ∩ P) => (C x).nbhd \ P ⊆ A
  have hc0 : good ⟨x0,hx0⟩ := by
    simpa [good,C,A] using hC0
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
  intro x hx
  exact theta_covered_by_two_of_local hD hDc hP hl
    (fun w hw => ⟨(C ⟨w,hw⟩).nbhd,(C ⟨w,hw⟩).isOpen_nbhd,hxC ⟨w,hw⟩,
      (C ⟨w,hw⟩).nbhd_subset,hall ⟨w,hw⟩⟩) hx


/-- A one-track endpoint neighborhood connects the entire complement once
local packets propagate along the connected deleted set. -/
theorem theta_connected_complement_of_one_track_start
    [LocallyConnectedSpace X] {D P : Set X}
    (hD : IsOpen D) (hDc : IsPreconnected D) (hP : IsClosed P)
    (hK : IsConnected (D ∩ P))
    (hlocal : ∀ x ∈ D ∩ P, ∃ C : SurfaceLocalSides D P, x ∈ C.nbhd)
    (C0 : SurfaceLocalSides D P) (x0 : X) (hx0 : x0 ∈ D ∩ P) (hstart : x0 ∈ C0.nbhd)
    (hone : C0.left = C0.right) : IsConnected (D \ P) := by
  let l := C0.connected_left.nonempty.some
  have hl : l ∈ C0.left := C0.connected_left.nonempty.some_mem
  have hlD : l ∈ D \ P := C0.left_subset_diff hl
  have hC0 : C0.nbhd \ P ⊆ connectedComponentIn (D \ P) l ∪ connectedComponentIn (D \ P) l := by
    rw [C0.nbhd_diff,← hone,union_self]
    intro z hz
    exact Or.inl (C0.connected_left.isPreconnected.subset_connectedComponentIn hl C0.left_subset_diff hz)
  have hex := theta_exhaustion_from_start_local_sides hD hDc hP hK hlocal C0 x0 hx0 hstart l l hlD hC0
  have heq : D \ P = connectedComponentIn (D \ P) l := by
    apply Subset.antisymm
    · exact fun x hx => (hex x hx).elim id id
    · exact connectedComponentIn_subset _ _
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hlD

end CurveComplex
#print axioms CurveComplex.theta_connected_complement_of_one_track_start
