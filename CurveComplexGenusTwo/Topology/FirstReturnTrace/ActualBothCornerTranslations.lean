import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualDisjointChartTranslations
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualLocalizedCornerSquare
namespace CurveComplex
open Set Topology Schoenflies
/-- Both signed corner translations are performed on ONE ACTUAL whole closed
first-return branch. The chart supports are produced disjointly, the exact
affine coordinate formula survives composition for all time, and every
retained crossing is fixed. -/
theorem source_first_return_both_corner_translations
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool)
    (v : Bool → Plane) (hv : ∀ k, ‖v k‖ < 1/4) :
    ∃ E : Bool → OpenPartialHomeomorph S Plane,
      (∀ k, (if k then D.finish else D.start) ∈ (E k).source ∧
        E k (if k then D.finish else D.start)=0) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      Disjoint (E false).source (E true).source ∧
      (∀ k, Disjoint (E k).source (source_surgery_retained_crossings B i)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ a.image ↔ E k x 0=0)) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ b.image ↔ E k x 1=0)) ∧
      ∃ H : AmbientIsotopy S, ∃ d : Curve S,
        d.image=H.finalMap '' (B.boundary i).image ∧
        AmbientIsotopy.Rel (B.boundary i).image d.image ∧
        (∀ t x, x ∉ (E false).source ∪ (E true).source → H.map (t,x)=x) ∧
        (∀ t x, x ∈ source_surgery_retained_crossings B i → H.map (t,x)=x) ∧
        source_surgery_retained_crossings B i ⊆ d.image ∩ a.image ∧
        (∀ k t x, x ∈ (E k).source → H.map (t,x) ∈ (E k).source) ∧
        (∀ k t x, x ∈ (E k).source → ‖E k x‖≤1/4 →
          E k (H.map (t,x))=E k x+(t:ℝ) • v k) ∧
        (∀ k x, x ∈ (E k).source → ‖E k x-v k‖≤1/4 →
          (x ∈ d.image ↔
            (E k x 0=v k 0 ∧ v k 1≤E k x 1) ∨
            (v k 0≤E k x 0 ∧ E k x 1=v k 1))) ∧
        ∀ k, E k (H.finalMap (if k then D.finish else D.start))=v k := by
  classical
  obtain ⟨E,hp,hsquare,hdis,hER,ha,hb,hbranch⟩ :=
    source_first_return_disjoint_corner_squares S D B ht i
  let P : Bool → Plane → Prop := fun _ z => (z 0=0 ∧ 0≤z 1) ∨ (0≤z 0 ∧ z 1=0)
  obtain ⟨H,d,hd,hrel,hfix,hsource,hmove,htrace⟩ :=
    source_two_disjoint_closed_curve_chart_translations S (B.boundary i) E hsquare
      (hdis false true (by decide)) P hbranch v hv
  have hRfix (t : Interval) (x : S) (hx : x ∈ source_surgery_retained_crossings B i) :
      H.map (t,x)=x := by
    apply hfix t x
    rintro (hh | hh)
    · exact Set.disjoint_left.mp (hER false) hh hx
    · exact Set.disjoint_left.mp (hER true) hh hx
  have hRret : source_surgery_retained_crossings B i ⊆ d.image ∩ a.image := by
    intro x hx
    refine ⟨?_,hx.1.2⟩
    rw [hd]
    refine ⟨x,?_,hRfix ⟨1,by norm_num⟩ x hx⟩
    rw [B.boundary_image]
    exact Or.inr hx.1.1
  refine ⟨E,hp,hsquare,hdis false true (by decide),hER,ha,hb,
    H,d,hd,hrel,hfix,hRfix,hRret,hsource,hmove,?_,?_⟩
  · intro k x hx hn
    rw [htrace k x hx hn]
    change ((E k x 0-v k 0=0 ∧ 0≤E k x 1-v k 1) ∨
      (0≤E k x 0-v k 0 ∧ E k x 1-v k 1=0)) ↔ _
    simp only [sub_eq_zero,sub_nonneg]
  · intro k
    unfold AmbientIsotopy.finalMap
    rw [hmove k ⟨1,by norm_num⟩ _ (hp k).1 (by rw [(hp k).2]; norm_num),(hp k).2]
    simp
end CurveComplex
#print axioms CurveComplex.source_first_return_both_corner_translations
