import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSurvivingEventLocality
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalGridOrbitInteraction

open Set Topology Schoenflies CurveComplex

theorem actual_horizontal_surviving_crossing_has_fixed_open_neighborhood
    (G : C(ℝ,Plane)) (T a b c r s : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (phi : Plane ≃ₜ Plane)
    (hcontact : (phi '' Plane.closedSquare 0 1)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b)
    (hold : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 1=c+(i:ℝ)*T}={G r,G s})
    (H : AmbientIsotopy Plane)
    (hfix : ∀ t z, z∉⋃ i : ℤ×ℤ,
      (fun w : Plane => w+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.openSquare 0 1) →
      H.map (t,z)=z)
    (q : Plane)
    (hqFamily : q∈⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))
    (hqGrid : ∃ i : ℤ, q 1=c+(i:ℝ)*T)
    (hqSurvive : q∉⋃ i : ℤ×ℤ,
      ({G r+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T),
        G s+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)} : Set Plane)) :
    ∃ U : Set Plane, IsOpen U ∧ q∈U ∧ ∀ t z, z∈U → H.map (t,z)=z := by
  let D := ⋃ i : ℤ×ℤ,
    (fun w : Plane => w+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.closedSquare 0 1)
  have hD : IsClosed D := plane_compact_full_lattice_support_isClosed _
    ((isCompact_closedSquare 0 1).image phi.continuous) T hT
  obtain ⟨hFull,_⟩ := normalized_actual_family_disk_full_lattice_contact G T a b hp phi hcontact
  have hOldFull := plane_actual_horizontal_grid_contacts_full_lattice_orbit T c (G '' Icc a b) {G r,G s} hold
  have hqD : q∉D := by
    intro hh
    have hqA := hFull ▸ (show q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))∩D from ⟨hqFamily,hh⟩)
    have hqOld : q∈⋃ i : ℤ×ℤ,
        (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' ({G r,G s} : Set Plane) :=
      hOldFull ▸ (show q∈(⋃ i : ℤ×ℤ,
        (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (G '' Icc a b))∩
          {z : Plane | ∃ i : ℤ, z 1=c+(i:ℝ)*T} from ⟨hqA,hqGrid⟩)
    apply hqSurvive
    simpa only [image_pair] using hqOld
  refine ⟨Dᶜ,hD.isOpen_compl,hqD,?_⟩
  intro t z hz
  apply hfix t z
  intro hh
  apply hz
  obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hh
  refine mem_iUnion.mpr ⟨i,w,?_,rfl⟩
  apply image_mono _ hw
  intro x hx
  exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hx).le


#print axioms actual_horizontal_surviving_crossing_has_fixed_open_neighborhood
