import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
theorem actual_localized_marked_crossing_chart (M : HyperellipticModel E S)
    (c d : EssentialMarkedArc M) (p : S) (hp : CrossesInDisk M c d p)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ F : OpenPartialHomeomorph S (ℝ × ℝ),
      p ∈ F.source ∧ F.source ⊆ W ∧ F p=(0,0) ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      (∀ x ∈ F.source, x ∈ c.val.image ↔ (F x).2=0) ∧
      (∀ x ∈ F.source, x ∈ d.val.image ↔ (F x).1=0) := by
  obtain ⟨U,hU,hpU,hfree,e,hep,hc,hd⟩ := hp
  have : Nonempty U := ⟨⟨p,hpU⟩⟩
  let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  have hV : IsOpen V :=
    (isOpen_lt (continuous_fst.abs) continuous_const).inter
      (isOpen_lt (continuous_snd.abs) continuous_const)
  let coeU : OpenPartialHomeomorph U S :=
    hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let f : U → ℝ × ℝ := fun u => (e u).val
  have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let coeE : OpenPartialHomeomorph U (ℝ × ℝ) := hf.toOpenPartialHomeomorph f
  let E0 := coeU.symm.trans coeE
  have hE0source : E0.source=U := by
    simp [E0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have hE0 (x : S) (hx : x ∈ U) : E0 x=(e ⟨x,hx⟩).val := by
    have hu : coeU.symm x=⟨x,hx⟩ :=
      hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
    change f (coeU.symm x)=_
    rw [hu]
  let F := E0.restr W
  have hFs : F.source=U ∩ W := by simp [F,hW.interior_eq,hE0source]
  refine ⟨F,hFs.symm ▸ ⟨hpU,hpW⟩,?_,?_,?_,?_,?_⟩
  · intro x hx; exact (hFs.le hx).2
  · change E0 p=(0,0); exact (hE0 p hpU).trans hep
  · exact hfree.mono_left (fun x hx => (hFs.le hx).1)
  · intro x hx
    change x ∈ c.val.image ↔ (E0 x).2=0
    rw [hE0 x (hFs.le hx).1]
    exact hc ⟨x,(hFs.le hx).1⟩
  · intro x hx
    change x ∈ d.val.image ↔ (E0 x).1=0
    rw [hE0 x (hFs.le hx).1]
    exact hd ⟨x,(hFs.le hx).1⟩
end CurveComplex.HyperellipticModel
