import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualClosedSeparatedCornerSquares
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualRawRetainedCrossings
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualDisjointChartTranslations
namespace CurveComplex
open Set Topology Schoenflies
/-- Perform both actual corner translations while preserving the genuine
crossing charts of every retained target crossing. The fixed open remote
region is produced from the closed-separated chart sources. -/
theorem source_first_return_both_corner_translations_preserve_crossings
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (v : Bool → Plane) (hv : ∀ k, ‖v k‖ < 1/4) :
    ∃ E : Bool → OpenPartialHomeomorph S Plane,
      (∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
        E k (if k then D.finish else D.start)=0) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      Disjoint (closure (E false).source) (closure (E true).source) ∧
      (∀ k, Disjoint (closure (E k).source) (source_surgery_retained_crossings B i)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0)) ∧
      ∃ H : AmbientIsotopy S, ∃ d : Curve S,
        d.image=H.finalMap '' (B.boundary i).image ∧
        AmbientIsotopy.Rel (B.boundary i).image d.image ∧
        (∀ t x, x ∉ (E false).source ∪ (E true).source → H.map (t,x)=x) ∧
        (∀ k t x, x ∈ (E k).source → H.map (t,x) ∈ (E k).source) ∧
        (∀ k t x, x ∈ (E k).source → ‖E k x‖≤1/4 →
          E k (H.map (t,x))=E k x+(t:ℝ) • v k) ∧
        (∀ k x, x ∈ (E k).source → ‖E k x-v k‖≤1/4 →
          (x ∈ d.image ↔
            (E k x 0=v k 0 ∧ v k 1≤E k x 1) ∨
            (v k 0≤E k x 0 ∧ E k x 1=v k 1))) ∧
        ∃ U : Set S, IsOpen U ∧ source_surgery_retained_crossings B i ⊆ U ∧
          (∀ t x, x ∈ U → H.map (t,x)=x) ∧
          (∀ x ∈ U, x ∈ d.image ↔ x ∈ (B.boundary i).image) ∧
          ∀ p ∈ source_surgery_retained_crossings B i, CrossesAt a d p := by
  classical
  obtain ⟨E,hp,hsquare,hdis,hER,ha,hb,hbranch⟩ :=
    source_first_return_closed_separated_corner_squares S D B ht i
  let P : Bool → Plane → Prop := fun _ z => (z 0=0 ∧ 0≤z 1) ∨ (0≤z 0 ∧ z 1=0)
  obtain ⟨H,d,hd,hrel,hfix,hsource,hmove,htrace⟩ :=
    source_two_disjoint_closed_curve_chart_translations S (B.boundary i) E hsquare
      (hdis.mono subset_closure subset_closure) P hbranch v hv
  let U : Set S := (closure (E false).source ∪ closure (E true).source)ᶜ
  have hU : IsOpen U := (isClosed_closure.union isClosed_closure).isOpen_compl
  have hUR : source_surgery_retained_crossings B i ⊆ U := by
    intro x hx
    rintro (hh | hh)
    · exact Set.disjoint_left.mp (hER false) hh hx
    · exact Set.disjoint_left.mp (hER true) hh hx
  have hUout (x : S) (hx : x ∈ U) : x ∉ (E false).source ∪ (E true).source := by
    rintro (hh | hh)
    · exact hx (Or.inl (subset_closure hh))
    · exact hx (Or.inr (subset_closure hh))
  have hUtrace (x : S) (hx : x ∈ U) : x ∈ d.image ↔ x ∈ (B.boundary i).image := by
    rw [hd]
    exact source_supported_curve_image_outside H (B.boundary i).image
      ((E false).source ∪ (E true).source) hfix x (hUout x hx)
  refine ⟨E,hp,hsquare,hdis,hER,ha,hb,H,d,hd,hrel,hfix,hsource,hmove,?_,
    U,hU,hUR,(fun t x hx => hfix t x (hUout x hx)),hUtrace,?_⟩
  · intro k x hx hn
    rw [htrace k x hx hn]
    change ((E k x 0-v k 0=0 ∧ 0≤E k x 1-v k 1) ∨
      (0≤E k x 0-v k 0 ∧ E k x 1-v k 1=0)) ↔ _
    simp only [sub_eq_zero,sub_nonneg]
  · intro p hpR
    exact source_crossing_transfer_local_trace
      (source_raw_branch_retained_crossings D B ht i p hpR) U hU (hUR hpR) hUtrace
end CurveComplex
#print axioms CurveComplex.source_first_return_both_corner_translations_preserve_crossings
