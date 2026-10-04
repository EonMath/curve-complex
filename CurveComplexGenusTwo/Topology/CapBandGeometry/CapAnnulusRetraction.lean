import CurveComplexGenusTwo.Topology.CapBandGeometry.CapAnnulusRadial

noncomputable section
open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry
variable {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    (N : Set S) (hN : IsClosed N) (c : Curve S) (hfront : frontier N = c.image)
    (f : C(CapDisk,S)) (hf : IsEmbedding f) (hboundary : f '' capBoundary = c.image)
    (houtside : f '' capInterior ⊆ interior Nᶜ) (hfill : N ∪ Set.range f = Set.univ)

def capExterior : Set S := (f '' capInnerDisk)ᶜ

include houtside in
theorem capN_subset_exterior : N ⊆ capExterior f := by
  intro x hx hn
  obtain ⟨z,hz,rfl⟩ := hn
  have hz' : z ∈ capInterior := by
    change dist (z:CapPlane) 0 < 1
    have hh : dist (z:CapPlane) 0 ≤ 1/2 := hz
    linarith
  exact (interior_subset (houtside ⟨z,hz',rfl⟩)) hx

def capDiskCoordinate (x : capExterior f) (hx : (x:S) ∈ Set.range f) : CapOuter :=
  ⟨hf.toHomeomorph.symm ⟨x,hx⟩, by
    have he : f (hf.toHomeomorph.symm ⟨x,hx⟩) = (x:S) :=
      congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply ⟨x,hx⟩)
    change 1/2 < ‖(hf.toHomeomorph.symm ⟨x,hx⟩:CapPlane)‖
    by_contra hn
    have hz : hf.toHomeomorph.symm ⟨x,hx⟩ ∈ capInnerDisk := by
      change dist _ 0 ≤ 1/2
      rw [dist_zero_right]
      exact le_of_not_gt hn
    exact x.2 ⟨_,hz,he⟩⟩

theorem capDiskCoordinate_image (x : capExterior f) (hx : (x:S) ∈ Set.range f) :
    f (capDiskCoordinate f hf x hx).1 = (x:S) :=
  congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply ⟨x,hx⟩)

def capPastingPiece (i : Fin 2) : Set (I × capExterior f) :=
  if i = 0 then {p | (p.2:S) ∈ N} else {p | (p.2:S) ∈ Set.range f}

include hN in
theorem capPastingPiece_closed (i : Fin 2) : IsClosed (capPastingPiece N f i) := by
  unfold capPastingPiece
  split_ifs
  · exact hN.preimage (by fun_prop)
  · exact (isCompact_range f.continuous).isClosed.preimage (by fun_prop)

include hfill in
theorem capPastingPiece_cover : (⋃ i : Fin 2, capPastingPiece N f i) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  have hp : (p.2:S) ∈ N ∪ Set.range f := hfill.symm ▸ Set.mem_univ _
  rcases hp with hn | hf
  · exact ⟨0,by simpa [capPastingPiece] using hn⟩
  · exact ⟨1,by simpa [capPastingPiece] using hf⟩

def capRadialPieceMap : C(capPastingPiece N f 1, capExterior f) := by
  let g : C(capPastingPiece N f 1, CapOuter) := {
    toFun := fun p => capDiskCoordinate f hf p.1.2 (by simpa [capPastingPiece] using p.2)
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact hf.toHomeomorph.symm.continuous.comp (by fun_prop) }
  let rad : C(capPastingPiece N f 1, CapDisk) :=
    ⟨fun p => capAnnulusRadial (p.1.1,g p),capAnnulusRadial_continuous.comp (by fun_prop)⟩
  refine { toFun := fun p => ⟨f (rad p), ?_⟩, continuous_toFun := ?_ }
  · rintro ⟨z,hz,he⟩
    have hze : z = rad p := hf.injective he
    subst z
    have hle : ‖(rad p:CapPlane)‖ ≤ 1/2 := by
      have hh : dist (rad p:CapPlane) 0 ≤ 1/2 := hz
      simpa only [dist_zero_right] using hh
    exact not_lt_of_ge hle (capAnnulusRadial_outer (p.1.1,g p))
  · exact Continuous.subtype_mk (f.continuous.comp rad.continuous) _

def capIdentityPieceMap : C(capPastingPiece N f 0, capExterior f) :=
  ⟨fun p => p.1.2,by fun_prop⟩

def capPastingMap (i : Fin 2) : C(capPastingPiece N f i, capExterior f) := by
  classical
  by_cases hi : i = 0
  · subst i; exact capIdentityPieceMap N f
  · have hi1 : i = 1 := by apply Fin.ext; omega
    subst i; exact capRadialPieceMap N f hf

include hN c hfront hboundary houtside in
theorem capPastingMap_agree (i j : Fin 2) (p : I × capExterior f)
    (hi : p ∈ capPastingPiece N f i) (hj : p ∈ capPastingPiece N f j) :
    capPastingMap N f hf i ⟨p,hi⟩ = capPastingMap N f hf j ⟨p,hj⟩ := by
  have hseam (hn : (p.2:S) ∈ N) (hr : (p.2:S) ∈ Set.range f) :
      capAnnulusRadial (p.1,capDiskCoordinate f hf p.2 hr) =
        (capDiskCoordinate f hf p.2 hr).1 := by
    have hx : (p.2:S) ∈ c.image :=
      (Set.ext_iff.mp (exterior_disk_meets_closed_neighborhood_at_frontier
        N hN c hfront f hboundary houtside) (p.2:S)).mp ⟨hn,hr⟩
    obtain ⟨z,hz,hze⟩ := hboundary.symm ▸ hx
    have hzz : z = (capDiskCoordinate f hf p.2 hr).1 :=
      hf.injective (hze.trans (capDiskCoordinate_image f hf p.2 hr).symm)
    exact capAnnulusRadial_boundary _ _ (hzz ▸ hz)
  fin_cases i <;> fin_cases j
  · rfl
  · apply Subtype.ext
    change (p.2:S) = f (capAnnulusRadial (p.1,capDiskCoordinate f hf p.2 _))
    rw [hseam (by simpa [capPastingPiece] using hi) (by simpa [capPastingPiece] using hj),
      capDiskCoordinate_image]
  · apply Subtype.ext
    change f (capAnnulusRadial (p.1,capDiskCoordinate f hf p.2 _)) = (p.2:S)
    rw [hseam (by simpa [capPastingPiece] using hj) (by simpa [capPastingPiece] using hi),
      capDiskCoordinate_image]
  · rfl

def capExteriorHomotopy : C(I × capExterior f, capExterior f) :=
  finiteClosedCoverMap (capPastingPiece N f) (capPastingPiece_closed N hN f)
    (capPastingPiece_cover N f hfill) (capPastingMap N f hf)
      (capPastingMap_agree N hN c hfront f hf hboundary houtside)

include hN c hfront hf hboundary houtside hfill in
theorem capExteriorHomotopy_on_N (s : I) (x : capExterior f) (hx : (x:S) ∈ N) :
    capExteriorHomotopy N hN c hfront f hf hboundary houtside hfill (s,x) = x := by
  have hp : (s,x) ∈ capPastingPiece N f 0 := by simpa [capPastingPiece] using hx
  have hh := finiteClosedCoverMap_apply (capPastingPiece N f) (capPastingPiece_closed N hN f)
    (capPastingPiece_cover N f hfill) (capPastingMap N f hf)
      (capPastingMap_agree N hN c hfront f hf hboundary houtside) 0 ⟨(s,x),hp⟩
  simpa [capExteriorHomotopy,capPastingMap,capIdentityPieceMap] using hh

include hN c hfront hf hboundary houtside hfill in
theorem capExteriorHomotopy_on_disk (s : I) (x : capExterior f)
    (hx : (x:S) ∈ Set.range f) :
    (capExteriorHomotopy N hN c hfront f hf hboundary houtside hfill (s,x):S) =
      f (capAnnulusRadial (s,capDiskCoordinate f hf x hx)) := by
  have hp : (s,x) ∈ capPastingPiece N f 1 := by simpa [capPastingPiece] using hx
  have hh := finiteClosedCoverMap_apply (capPastingPiece N f) (capPastingPiece_closed N hN f)
    (capPastingPiece_cover N f hfill) (capPastingMap N f hf)
      (capPastingMap_agree N hN c hfront f hf hboundary houtside) 1 ⟨(s,x),hp⟩
  have hh' := congrArg (fun y : capExterior f => (y:S)) hh
  change (capExteriorHomotopy N hN c hfront f hf hboundary houtside hfill (s,x):S) =
    f (capAnnulusRadial (s,capDiskCoordinate f hf x hx)) at hh'
  exact hh' 

include hN c hfront hf hboundary houtside hfill in
theorem capExteriorHomotopy_zero (x : capExterior f) :
    capExteriorHomotopy N hN c hfront f hf hboundary houtside hfill (0,x) = x := by
  have hx : (x:S) ∈ N ∪ Set.range f := hfill.symm ▸ Set.mem_univ _
  rcases hx with hx | hx
  · exact capExteriorHomotopy_on_N N hN c hfront f hf hboundary houtside hfill 0 x hx
  · apply Subtype.ext
    rw [capExteriorHomotopy_on_disk N hN c hfront f hf hboundary houtside hfill 0 x hx,
      capAnnulusRadial_zero,capDiskCoordinate_image]

include hN c hfront hf hboundary houtside hfill in
theorem capExteriorHomotopy_one (x : capExterior f) :
    (capExteriorHomotopy N hN c hfront f hf hboundary houtside hfill (1,x):S) ∈ N := by
  have hx : (x:S) ∈ N ∪ Set.range f := hfill.symm ▸ Set.mem_univ _
  rcases hx with hx | hx
  · rw [capExteriorHomotopy_on_N N hN c hfront f hf hboundary houtside hfill 1 x hx]
    exact hx
  · rw [capExteriorHomotopy_on_disk N hN c hfront f hf hboundary houtside hfill 1 x hx]
    apply hN.frontier_subset
    rw [hfront,← hboundary]
    exact ⟨_,capAnnulusRadial_one _,rfl⟩

def capExteriorNeighborhoodHomotopyEquiv : ContinuousMap.HomotopyEquiv (capExterior f) N := by
  let H := capExteriorHomotopy N hN c hfront f hf hboundary houtside hfill
  let r : C(capExterior f,N) := {
    toFun := fun x => ⟨H (1,x),capExteriorHomotopy_one N hN c hfront f hf hboundary houtside hfill x⟩
    continuous_toFun := by fun_prop }
  let inc : C(N,capExterior f) :=
    ⟨fun x => ⟨x,capN_subset_exterior N f houtside x.2⟩,by fun_prop⟩
  refine { toFun := r, invFun := inc, left_inv := ?_, right_inv := ?_ }
  · let h : ContinuousMap.Homotopy (ContinuousMap.id (capExterior f)) (inc.comp r) := {
      toFun := H
      continuous_toFun := H.continuous
      map_zero_left := capExteriorHomotopy_zero N hN c hfront f hf hboundary houtside hfill
      map_one_left := by intro x; rfl }
    exact ⟨h.symm⟩
  · have hright : r.comp inc = ContinuousMap.id N := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun y : capExterior f => (y:S)) (capExteriorHomotopy_on_N N hN c hfront f hf hboundary houtside hfill
        1 (inc x) x.2)
    exact hright ▸ ContinuousMap.Homotopic.refl _

#print axioms capExteriorNeighborhoodHomotopyEquiv
#print axioms capExteriorHomotopy
end CurveComplex.CapBandGeometry
