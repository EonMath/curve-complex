import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic.Push

/- The clopen proof below adapts Schoenflies/CrosscutAtMostTwo.lean
Copyright (c) 2026 Álvaro Begué. Released under Apache 2.0. -/
namespace CurveComplex
open Set
variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
variable {D P : Set X}

theorem theta_isOpen_notMem_two_components {S : Set X} (hS : IsOpen S) (zL zR : X) :
    IsOpen {y | y ∈ S ∧ y ∉ connectedComponentIn S zL ∧ y ∉ connectedComponentIn S zR} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyS, hyL, hyR⟩
  refine ⟨connectedComponentIn S y, ?_, hS.connectedComponentIn,
    mem_connectedComponentIn hyS⟩
  intro w hw
  -- Two components are equal or disjoint: if `w` were in one of the two named components, that
  -- component would *be* the component of `y`, and `y` would be in it.
  have hcw : connectedComponentIn S y = connectedComponentIn S w := connectedComponentIn_eq hw
  refine ⟨connectedComponentIn_subset S y hw, fun hwL => hyL ?_, fun hwR => hyR ?_⟩
  · rw [show connectedComponentIn S zL = connectedComponentIn S y from
      (connectedComponentIn_eq hwL).trans hcw.symm]
    exact mem_connectedComponentIn hyS
  · rw [show connectedComponentIn S zR = connectedComponentIn S y from
      (connectedComponentIn_eq hwR).trans hcw.symm]
    exact mem_connectedComponentIn hyS

/-- **The clopen step, and the whole of "at most two sides" once a collar is available.** If
every point of `P` inside the region `D` has a neighbourhood inside `D` whose complement of `P`
is covered by the components of two fixed points `z_L, z_R`, then all of `D ∖ P` is covered by
those two components.

The set `T` of points of `D ∖ P` in neither component is open; the union `U` of the two
components with all the good neighbourhoods is open, contains `P ∩ D` and meets `D`; the two
are disjoint and cover `D`. Connectedness of `D` kills `T`. -/
theorem theta_covered_by_two_of_local (hDopen : IsOpen D) (hDconn : IsPreconnected D)
    (hPclosed : IsClosed P) {zL zR : X} (hzL : zL ∈ D \ P)
    (hloc : ∀ w ∈ D ∩ P, ∃ V : Set X, IsOpen V ∧ w ∈ V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR)
    {x : X} (hx : x ∈ D \ P) :
    x ∈ connectedComponentIn (D \ P) zL ∨ x ∈ connectedComponentIn (D \ P) zR := by
  by_contra hcon
  push Not at hcon
  have hSopen : IsOpen (D \ P) := hDopen.sdiff hPclosed
  -- `W` gathers every open piece of `D` that the hypothesis certifies.
  have hWopen : IsOpen (⋃₀ {V : Set X | IsOpen V ∧ V ⊆ D ∧
      V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    isOpen_sUnion fun _ hV => hV.1
  have hUopen : IsOpen (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set X | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) :=
    ((hSopen.connectedComponentIn).union
      (hSopen.connectedComponentIn)).union hWopen
  have hTopen := theta_isOpen_notMem_two_components hSopen zL zR
  -- `U` and `T` are disjoint: a point of `T` is off `P`, so if it were in `W` it would be in
  -- one of the two components, and it is in neither by definition.
  have hdisj : ∀ y, y ∈ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set X | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR} →
      y ∈ {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} → False := by
    rintro y (hy | hy) ⟨hyS, hyL, hyR⟩
    · exact hy.elim hyL hyR
    · obtain ⟨V, hV, hyV⟩ := hy
      exact (hV.2.2 ⟨hyV, hyS.2⟩).elim hyL hyR
  -- and they cover `D`: a point of `D` on `P` is inside one of the certified pieces.
  have hcover : D ⊆ (connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR ∪
      ⋃₀ {V : Set X | IsOpen V ∧ V ⊆ D ∧
        V \ P ⊆ connectedComponentIn (D \ P) zL ∪ connectedComponentIn (D \ P) zR}) ∪
      {y | y ∈ D \ P ∧ y ∉ connectedComponentIn (D \ P) zL ∧
        y ∉ connectedComponentIn (D \ P) zR} := by
    intro y hyD
    by_cases hyP : y ∈ P
    · obtain ⟨V, hVopen, hyV, hVD, hVsub⟩ := hloc y ⟨hyD, hyP⟩
      exact Or.inl (Or.inr ⟨V, ⟨hVopen, hVD, hVsub⟩, hyV⟩)
    · by_cases hyL : y ∈ connectedComponentIn (D \ P) zL
      · exact Or.inl (Or.inl (Or.inl hyL))
      by_cases hyR : y ∈ connectedComponentIn (D \ P) zR
      · exact Or.inl (Or.inl (Or.inr hyR))
      exact Or.inr ⟨⟨hyD, hyP⟩, hyL, hyR⟩
  obtain ⟨y, hyD, hyU, hyT⟩ := hDconn _ _ hUopen hTopen hcover
    ⟨zL, hzL.1, Or.inl (Or.inl (mem_connectedComponentIn hzL))⟩
    ⟨x, hx.1, hx, hcon.1, hcon.2⟩
  exact hdisj y hyU hyT


end CurveComplex
#print axioms CurveComplex.theta_covered_by_two_of_local
