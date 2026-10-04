import CurveComplexGenusTwo.Dictionary.MarkedSphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- A genuine square restoring ONLY one specified corner mark constructs
its four literal boundary paths and their actual punctured boundary word.
No boundary path or path-homotopy certificate is supplied. -/
theorem actual_one_corner_square_boundary_homotopy
    (M : HyperellipticModel E S) (c : S) (G : C(unitInterval × unitInterval,S))
    (hmarks : ∀ z, G z ∉ ((M.cover.branch : Set S) \ {c})) :
    ∃ h00 : G (0,0) ∈ ((M.cover.branch : Set S) \ {c})ᶜ,
    ∃ h01 : G (0,1) ∈ ((M.cover.branch : Set S) \ {c})ᶜ,
    ∃ h10 : G (1,0) ∈ ((M.cover.branch : Set S) \ {c})ᶜ,
    ∃ h11 : G (1,1) ∈ ((M.cover.branch : Set S) \ {c})ᶜ,
    ∃ bottom : Path (⟨G (0,0),h00⟩ : ↑((M.cover.branch : Set S) \ {c})ᶜ) ⟨G (0,1),h01⟩,
    ∃ right : Path (⟨G (0,1),h01⟩ : ↑((M.cover.branch : Set S) \ {c})ᶜ) ⟨G (1,1),h11⟩,
    ∃ left : Path (⟨G (0,0),h00⟩ : ↑((M.cover.branch : Set S) \ {c})ᶜ) ⟨G (1,0),h10⟩,
    ∃ top : Path (⟨G (1,0),h10⟩ : ↑((M.cover.branch : Set S) \ {c})ᶜ) ⟨G (1,1),h11⟩,
      (∀ t, (bottom t:S)=G (0,t)) ∧ (∀ t, (right t:S)=G (t,1)) ∧
      (∀ t, (left t:S)=G (t,0)) ∧ (∀ t, (top t:S)=G (1,t)) ∧
      (bottom.trans right).Homotopic (left.trans top) := by
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let F : C(unitInterval × unitInterval,↑((M.cover.branch : Set S) \ {c})ᶜ) :=
    ⟨fun z => ⟨G z,hmarks z⟩,G.continuous.subtype_mk hmarks⟩
  let d : Path ((0,0):unitInterval × unitInterval) (0,1) := {
    toFun := fun t => (0,t)
    continuous_toFun := continuous_const.prodMk continuous_id
    source' := rfl
    target' := rfl }
  let r : Path ((0,1):unitInterval × unitInterval) (1,1) := {
    toFun := fun t => (t,1)
    continuous_toFun := continuous_id.prodMk continuous_const
    source' := rfl
    target' := rfl }
  let l : Path ((0,0):unitInterval × unitInterval) (1,0) := {
    toFun := fun t => (t,0)
    continuous_toFun := continuous_id.prodMk continuous_const
    source' := rfl
    target' := rfl }
  let t : Path ((1,0):unitInterval × unitInterval) (1,1) := {
    toFun := fun t => (1,t)
    continuous_toFun := continuous_const.prodMk continuous_id
    source' := rfl
    target' := rfl }
  have hh := (SimplyConnectedSpace.paths_homotopic (d.trans r) (l.trans t)).map F
  rw [Path.map_trans,Path.map_trans] at hh
  exact ⟨hmarks (0,0),hmarks (0,1),hmarks (1,0),hmarks (1,1),
    d.map F.continuous,r.map F.continuous,l.map F.continuous,t.map F.continuous,
    (fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),hh⟩
end CurveComplex.HyperellipticModel
