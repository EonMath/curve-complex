import Mathlib

open Set Topology
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

/-- A map from a disjoint union is nullhomotopic when all its restrictions are
nullhomotopic and the target is path connected. No finiteness premise is needed. -/
theorem nullhomotopic_of_sigma_restrictions
    {ι : Type} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
    {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]
    (f : C((i : ι) × X i, Y))
    (h : ∀ i, (f.comp ⟨Sigma.mk i, continuous_sigmaMk⟩).Nullhomotopic) :
    f.Nullhomotopic := by
  classical
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  have hh (i : ι) : (f.comp ⟨Sigma.mk i, continuous_sigmaMk⟩).Homotopic
      (ContinuousMap.const (X i) y) := by
    obtain ⟨p, hp⟩ := h i
    exact hp.trans ⟨(PathConnectedSpace.somePath p y).toHomotopyConst⟩
  let H (i : ι) := (hh i).some
  refine ⟨y, ⟨{
    toFun := fun p => H p.2.1 (p.1, p.2.2)
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · have hc : Continuous (fun p : (i : ι) × (X i × unitInterval) => H p.1 (p.2.2, p.2.1)) :=
      continuous_sigma (fun i => (H i).continuous.comp continuous_swap)
    exact hc.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)
  · rintro ⟨i, x⟩
    exact (H i).map_zero_left x
  · rintro ⟨i, x⟩
    exact (H i).map_one_left x

/-- A locally connected space is a topological disjoint union of its connected
components, so componentwise nullhomotopy suffices. -/
theorem nullhomotopic_of_connectedComponent_restrictions
    {X Y : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (f : C(X, Y))
    (h : ∀ x : X,
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(connectedComponent x, X))).Nullhomotopic) :
    f.Nullhomotopic := by
  classical
  let F (c : ConnectedComponents X) := {x : X | ConnectedComponents.mk x = c}
  have hopen (c : ConnectedComponents X) : IsOpen (F c) :=
    (isOpen_discrete {c}).preimage ConnectedComponents.continuous_coe
  let e : ((c : ConnectedComponents X) × ↥(F c)) ≃ₜ X :=
    (Equiv.sigmaFiberEquiv ConnectedComponents.mk).toHomeomorphOfContinuousOpen
      (continuous_sigma (fun _ => continuous_subtype_val))
      (isOpenMap_sigma.mpr (fun c => (hopen c).isOpenEmbedding_subtypeVal.isOpenMap))
  have hc (c : ConnectedComponents X) :
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(F c), X))).Nullhomotopic := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    have heq : F (ConnectedComponents.mk x) = connectedComponent x := by
      ext y
      exact ConnectedComponents.coe_eq_coe'
    let q := Homeomorph.setCongr heq
    exact (h x).comp_left ⟨q, q.continuous⟩
  have hh : (f.comp ⟨e, e.continuous⟩).Nullhomotopic := by
    apply nullhomotopic_of_sigma_restrictions
    exact hc
  have hh' := hh.comp_left (⟨e.symm, e.symm.continuous⟩ : C(X, _))
  have heq : (f.comp (⟨e, e.continuous⟩ : C(_, X))).comp ⟨e.symm, e.symm.continuous⟩ = f := by
    ext x
    exact congrArg f (e.apply_symm_apply x)
  rwa [heq] at hh'

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
