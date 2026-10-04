import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualGridOrbitInteraction

open Set Schoenflies

theorem plane_horizontal_grid_membership_lattice_translate_iff
    (T c : ℝ) (i : ℤ×ℤ) (z : Plane) :
    (∃ k : ℤ, (z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) 1=c+(k:ℝ)*T) ↔
    ∃ k : ℤ, z 1=c+(k:ℝ)*T := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k-i.2,?_⟩
    change z 1+(i.2:ℝ)*T=c+(k:ℝ)*T at hk
    push_cast
    linarith
  · rintro ⟨k,hk⟩
    refine ⟨k+i.2,?_⟩
    change z 1+(i.2:ℝ)*T=c+((k+i.2:ℤ):ℝ)*T
    push_cast
    linarith

/-- An exact actual local contact identity propagates to the FULL lattice,
including mixed horizontal/vertical translates. -/
theorem plane_actual_horizontal_grid_contacts_full_lattice_orbit
    (T c : ℝ) (A F : Set Plane)
    (hcontact : A∩{z : Plane | ∃ k : ℤ, z 1=c+(k:ℝ)*T}=F) :
    (⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' A) ∩
      {z : Plane | ∃ k : ℤ, z 1=c+(k:ℝ)*T} =
    ⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' F := by
  ext z
  constructor
  · rintro ⟨hz,hzg⟩
    obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hz
    have hwg := (plane_horizontal_grid_membership_lattice_translate_iff T c i w).mp hzg
    exact mem_iUnion.mpr ⟨i,w,hcontact ▸ ⟨hw,hwg⟩,rfl⟩
  · intro hz
    obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hz
    have hh : w∈A∩{z : Plane | ∃ k : ℤ, z 1=c+(k:ℝ)*T} := hcontact.symm ▸ hw
    exact ⟨mem_iUnion.mpr ⟨i,w,hh.1,rfl⟩,
      (plane_horizontal_grid_membership_lattice_translate_iff T c i w).mpr hh.2⟩

/-- Actual target avoidance also propagates to every mixed deck translate. -/
theorem plane_actual_horizontal_grid_free_full_lattice_orbit
    (T c : ℝ) (B : Set Plane)
    (havoid : ∀ z∈B, ∀ k : ℤ, z 1≠c+(k:ℝ)*T) :
    Disjoint (⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' B)
      {z : Plane | ∃ k : ℤ, z 1=c+(k:ℝ)*T} := by
  apply disjoint_left.mpr
  intro z hz hzg
  obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hz
  obtain ⟨k,hk⟩ := (plane_horizontal_grid_membership_lattice_translate_iff T c i w).mp hzg
  exact havoid w hw k hk


#print axioms plane_actual_horizontal_grid_contacts_full_lattice_orbit
#print axioms plane_actual_horizontal_grid_free_full_lattice_orbit
