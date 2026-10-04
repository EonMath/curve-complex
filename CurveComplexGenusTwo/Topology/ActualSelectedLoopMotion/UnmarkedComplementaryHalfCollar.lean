import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ClosedDiskRelativeHalfCollar
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.UnmarkedLoopDiscDecomposition

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Transport the distance-controlled disk construction through the literal
Schoenflies disk. This collar includes and fixes the common original base. -/
theorem unmarked_complementary_disk_relative_half_collar
    (M : HyperellipticModel E S) (a : C(Interval,S))
    (ha : a 0 = a 1)
    (hloopinj : ∀ s s', a s = a s' →
      s = s' ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) (U : Set S) (D : UnmarkedComplementaryDiscSide a U)
    (P : Set S) (hP : IsClosed P) (hbase : a 0 ∈ P)
    (havoid : ∀ x ∈ (Set.range a), x ≠ a 0 → x ∉ P) :
    ∃ C : C(Interval × Interval,S),
      (∀ s, C (s,0) = a s) ∧
      (∀ w, C (0,w) = a 0 ∧ C (1,w) = a 0) ∧
      (∀ s w s' w', C (s,w) = C (s',w') →
        (s = s' ∧ w = w') ∨
        ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
      (∀ s w, C (s,w) ≠ a 0 → C (s,w) ∉ P) ∧
      (∀ s ∈ Set.Ioo (0 : Interval) 1, ∀ w, 0 < w → C (s,w) ∈ U) := by
  let : T2Space S := M.sphere.symm.t2Space
  have hcl (s : Interval) : a s ∈ closure U := by
    rw [D.closure_eq]
    exact Or.inr (Set.mem_range_self s)
  let L : C(Interval,closure U) :=
    ⟨fun s => ⟨a s,hcl s⟩,a.continuous.subtype_mk _⟩
  let α : C(Interval,JordanClosedDisk) :=
    ⟨fun s => D.closedDisk.symm (L s),D.closedDisk.symm.continuous.comp L.continuous⟩
  have hα (s) : (D.closedDisk (α s)).val = a s :=
    congrArg Subtype.val (D.closedDisk.apply_symm_apply (L s))
  have hunit (s) : ‖(α s).val‖ = 1 := by
    apply (D.disk_boundary (α s)).mp
    rw [hα]
    exact Set.mem_range_self s
  have hend : α 1 = α 0 := D.closedDisk.injective
    (Subtype.ext ((hα 1).trans (ha.symm.trans (hα 0).symm)))
  have hinj (s s') (he : α s = α s') :
      s = s' ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
    have he' : a s = a s' :=
      (hα s).symm.trans ((congrArg (fun z : JordanClosedDisk => (D.closedDisk z).val) he).trans (hα s'))
    exact hloopinj s s' he'
  let Q : Set JordanClosedDisk := {z | (D.closedDisk z).val ∈ P}
  have hQ : IsClosed Q := hP.preimage
    (continuous_subtype_val.comp D.closedDisk.continuous)
  let F : Set JordanPlane := Subtype.val '' Q
  have hF : IsClosed F := (hQ.isCompact.image continuous_subtype_val).isClosed
  have hbaseF : (α 0).val ∈ F := ⟨α 0,by
    change (D.closedDisk (α 0)).val ∈ P
    rw [hα]
    exact hbase,rfl⟩
  have hαavoid (s : Interval) (hs : s ∈ Set.Ioo (0 : Interval) 1) : (α s).val ∉ F := by
    rintro ⟨z,hz,hzs⟩
    have he : z = α s := Subtype.ext hzs
    have hmark : a s ∈ P := by
      change (D.closedDisk z).val ∈ P at hz
      rwa [he,hα] at hz
    apply havoid _ (Set.mem_range_self s) _ hmark
    intro hbaseeq
    rcases hloopinj s 0 hbaseeq with he | he
    · exact (ne_of_gt hs.1) he
    · rcases he.1 with he | he
      · exact (ne_of_gt hs.1) he
      · exact (ne_of_lt hs.2) he
  obtain ⟨β,hβ0,hβends,hβinj,hβavoid,hβinterior⟩ :=
    closed_disk_relative_radial_half_collar α hunit hend hinj F hF hbaseF hαavoid
  let C : C(Interval × Interval,S) :=
    ⟨fun z => (D.closedDisk (β z)).val,
      continuous_subtype_val.comp (D.closedDisk.continuous.comp β.continuous)⟩
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro s
    change (D.closedDisk (β (s,0))).val = a s
    rw [hβ0,hα]
  · intro w
    constructor <;> change (D.closedDisk _).val = a 0
    · rw [(hβends w).1,hα]
    · rw [(hβends w).2,hα]
  · intro s w s' w' he
    exact hβinj s w s' w' (D.closedDisk.injective (Subtype.ext he))
  · intro s w hne hmem
    have hβne : β (s,w) ≠ α 0 := by
      intro he
      apply hne
      change (D.closedDisk (β (s,w))).val = a 0
      rw [he,hα]
    apply hβavoid s w hβne
    exact ⟨β (s,w),hmem,rfl⟩
  · intro s hs w hw
    exact (D.disk_interior (β (s,w))).mpr (hβinterior s hs w hw)

end CurveComplex.HyperellipticModel
