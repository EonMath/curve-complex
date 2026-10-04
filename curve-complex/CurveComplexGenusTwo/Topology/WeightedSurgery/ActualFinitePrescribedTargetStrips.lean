import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualTargetComplementaryCoreStrips

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Literal geometric target core and its produced whole strip. This datatype
stores no ambient isotopy, move sequence, terminal alignment or homotopy. -/
structure ActualTargetCoreStrip (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (Q : FinitePosition M anchor F) (v : {v // v ∈ F}) where
  left : ℝ
  right : ℝ
  left_pos : 0 < left
  right_lt : right < 1
  ordered : left < right
  map : Interval × Set.Icc (-1:ℝ) 1 → S
  embedded : IsEmbedding map
  center : ∀ t, map (t,⟨0,by norm_num⟩) =
    (Q.rep v).val.map (actualCoreParameter left right left_pos.le right_lt.le ordered.le t)
  clear : ∀ z ∈ range map, z ∉ M.cover.branch ∧ z ∉ anchor.val.image ∧
    ∀ w, w ≠ v → z ∉ (Q.rep w).val.image

namespace ActualTargetCoreStrip
variable {M : HyperellipticModel E S} {anchor : EssentialMarkedArc M}
  {F : Finset (EssentialArcClass M)} {Q : FinitePosition M anchor F} {v : {v // v ∈ F}}

def parameterOpen (B : ActualTargetCoreStrip M anchor F Q v) : Set Interval :=
  {r | B.left < r.val ∧ r.val < B.right}

theorem parameterOpen_isOpen (B : ActualTargetCoreStrip M anchor F Q v) : IsOpen B.parameterOpen :=
  (isOpen_Ioo.preimage continuous_subtype_val)

/-- Every covered parameter is literally on the produced center trace. -/
theorem covered_point_mem_strip (B : ActualTargetCoreStrip M anchor F Q v)
    (r : Interval) (hr : r ∈ B.parameterOpen) : (Q.rep v).val.map r ∈ range B.map := by
  have hd : 0 < B.right-B.left := sub_pos.mpr B.ordered
  let t : Interval := ⟨(r.val-B.left)/(B.right-B.left),
    (div_nonneg (sub_nonneg.mpr hr.1.le) hd.le),
    (div_le_one hd).mpr (by linarith [hr.2])⟩
  refine ⟨(t,⟨0,by norm_num⟩),?_⟩
  rw [B.center]
  congr 1
  apply Subtype.ext
  dsimp [actualCoreParameter,t]
  field_simp
  ring
end ActualTargetCoreStrip

/-- A literal target interior point away from the stationary anchor produces
its own geometric strip and an open parameter neighborhood that it covers. -/
theorem actual_target_parameter_strip_producer
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (Q : FinitePosition M anchor F) (v : {v // v ∈ F})
    (r : Interval) (hr : 0 < r.val ∧ r.val < 1)
    (hra : (Q.rep v).val.map r ∉ anchor.val.image) :
    ∃ B : ActualTargetCoreStrip M anchor F Q v, r ∈ B.parameterOpen := by
  obtain ⟨α,β,hα,hβ,hαβ,har,hrb,B,hB,hcenter,hclear,_⟩ :=
    actual_target_position_complementary_core_strip M anchor F hF Q v r hr hra
  exact ⟨⟨α,β,hα,hβ,hαβ,B,hB,hcenter,hclear⟩,har,hrb⟩

/-- Construct finite literal target strip geometry over any compact part of
the prescribed Q parameter interval away from its endpoints and the stationary
anchor. Each strip avoids every OTHER prescribed Q image. The cover is derived
from the actual point producers and compactness, never supplied. -/
theorem actual_compact_prescribed_target_finite_strips
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (hF : IsArcSimplex M F)
    (Q : FinitePosition M anchor F) (v : {v // v ∈ F})
    (K : Set Interval) (hK : IsCompact K)
    (hKinterior : ∀ r ∈ K, 0 < r.val ∧ r.val < 1)
    (hKanchor : ∀ r ∈ K, (Q.rep v).val.map r ∉ anchor.val.image) :
    ∃ strips : Finset (ActualTargetCoreStrip M anchor F Q v),
      K ⊆ ⋃ B ∈ strips, B.parameterOpen ∧
      (Q.rep v).val.map '' K ⊆ ⋃ B ∈ strips, range B.map := by
  classical
  have hex (r : K) : ∃ B : ActualTargetCoreStrip M anchor F Q v, r.val ∈ B.parameterOpen :=
    actual_target_parameter_strip_producer M anchor F hF Q v r.val
      (hKinterior r.val r.property) (hKanchor r.val r.property)
  choose B hB using hex
  have hcover : K ⊆ ⋃ r : K, (B r).parameterOpen := by
    intro r hr
    exact mem_iUnion.mpr ⟨⟨r,hr⟩,hB ⟨r,hr⟩⟩
  obtain ⟨selected,hselected⟩ := hK.elim_finite_subcover
    (fun r : K => (B r).parameterOpen) (fun r => (B r).parameterOpen_isOpen) hcover
  refine ⟨selected.image B,?_,?_⟩
  · intro r hr
    obtain ⟨x,hx⟩ := mem_iUnion.mp (hselected hr)
    obtain ⟨hxs,hrx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨B x,mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨x,hxs,rfl⟩,hrx⟩⟩
  · rintro z ⟨r,hr,rfl⟩
    obtain ⟨x,hx⟩ := mem_iUnion.mp (hselected hr)
    obtain ⟨hxs,hrx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨B x,mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨x,hxs,rfl⟩,
      (B x).covered_point_mem_strip r hrx⟩⟩

end
end CurveComplex.HyperellipticModel.ArcSurgery
