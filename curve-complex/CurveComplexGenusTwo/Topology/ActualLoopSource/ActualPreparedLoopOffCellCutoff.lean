import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeActualPlanarDrawing
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual loop movie's complete contact set produces a finite uniform
cell support in its existing common-strip domain and an actual cutoff. No
finite support, subdivision or cutoff certificate is an input. -/
theorem actual_prepared_loop_off_cell_cutoff
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (G : C(Interval × Interval,S))
    (T : Set (Interval × Interval)) (hT : IsOpen T)
    (hcontacts : G ⁻¹' a.val.image ⊆ T) :
    ∃ n : ℕ, ∃ hn : 0<n,
    ∃ cell : (Fin n × Fin n) → Set (Interval × Interval),
      (∀ k,cell k=range (fun z : Interval × Interval =>
        (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2))) ∧
      (∀ k,IsClosed (cell k)) ∧ (∀ z,∃ k,z ∈ cell k) ∧
    ∃ label : (Fin n × Fin n) → Bool,
      (∀ k,label k=true → cell k ⊆ T) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,G z ∉ a.val.image) ∧
    ∃ support : Set (Interval × Interval),
      support=(⋃ k,if label k=true then cell k else ∅) ∧
      IsClosed support ∧ support ⊆ T ∧ G ⁻¹' a.val.image ⊆ interior support ∧
    ∃ cutoff : C(Interval × Interval,ℝ),
      (∀ z,cutoff z ∈ Icc (0:ℝ) 1) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,cutoff z=0) ∧
      (∀ z,z ∉ interior support → cutoff z=0) ∧
      (∀ z,G z ∈ a.val.image → cutoff z=1) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨n,hn,cell,hcell,hcellClosed,hcellCover,label,hcellT,hcellOff,
    support,hsupport,hsupportClosed,hsupportT,hcontactsSupport,
    oldCutoff,holdRange,holdOutside,holdContacts⟩ :=
    actual_prepared_loop_finite_core_support M a G T hT hcontacts
  let Z := G ⁻¹' a.val.image
  have hZ : IsClosed Z := (isCompact_range a.val.continuous).isClosed.preimage G.continuous
  let off : Set (Interval × Interval) := ⋃ k,if label k=false then cell k else ∅
  have hoff : IsClosed off := by
    apply isClosed_iUnion_of_finite
    intro k
    split_ifs
    · exact hcellClosed k
    · exact isClosed_empty
  have hZoff : Disjoint off Z := by
    apply Set.disjoint_left.mpr
    intro z hz hcontact
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    by_cases hb : label k=false
    · exact hcellOff k hb z (by simpa only [ite_eq_left hb] using hk) hcontact
    · simp only [ite_eq_right hb,mem_empty_iff_false] at hk
  have hZoutside : Disjoint (interior support)ᶜ Z :=
    Set.disjoint_left.mpr (fun z hz hcontact => hz (hcontactsSupport hcontact))
  let bad := off ∪ (interior support)ᶜ
  have hbad : IsClosed bad := hoff.union isOpen_interior.isClosed_compl
  have hdisjoint : Disjoint bad Z := hZoff.union_left hZoutside
  obtain ⟨cutoff,hbadZero,hcontactOne,hrange⟩ :=
    exists_continuous_zero_one_of_isClosed hbad hZ hdisjoint
  refine ⟨n,hn,cell,hcell,hcellClosed,hcellCover,label,hcellT,hcellOff,
    support,hsupport,hsupportClosed,hsupportT,hcontactsSupport,cutoff,hrange,?_,?_,?_⟩
  · intro k hk z hz
    exact hbadZero (Or.inl (mem_iUnion.mpr ⟨k,by simpa only [ite_eq_left hk] using hz⟩))
  · intro z hz
    exact hbadZero (Or.inr hz)
  · intro z hz
    exact hcontactOne hz
end CurveComplex.HyperellipticModel
