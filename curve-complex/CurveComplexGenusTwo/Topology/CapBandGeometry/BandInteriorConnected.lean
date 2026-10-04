import CurveComplexGenusTwo.Topology.CapBandGeometry.BandHOne
import CurveComplexGenusTwo.Topology.CapBandGeometry.SquareSideCap
import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierGeometry
import CurveComplexGenusTwo.Topology.FrontierCircle.BandNeighborhoodProbe

noncomputable section
open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

abbrev OpenBandRectangle := Ioo (0 : ℝ) 1 × Ioo (-1 : ℝ) 1

def bandOpenCoreMap {S : Type} (F : I × BandWidth → S) : OpenBandRectangle → S :=
  fun p => F (⟨p.1, ⟨p.1.2.1.le, p.1.2.2.le⟩⟩,
    ⟨p.2, ⟨p.2.2.1.le, p.2.2.2.le⟩⟩)

theorem bandOpenCore_preconnected {S : Type} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : Continuous F) :
    IsPreconnected (Set.range (bandOpenCoreMap F)) := by
  letI : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    (convex_Ioo _ _).contractibleSpace ⟨1/2, by norm_num⟩
  letI : ContractibleSpace (Ioo (-1 : ℝ) 1) :=
    (convex_Ioo _ _).contractibleSpace ⟨0, by norm_num⟩
  exact (isConnected_range (by unfold bandOpenCoreMap; fun_prop)).2

theorem bandOpenCore_dense_range {S : Type} [TopologicalSpace S]
    (F : I × BandWidth → S) (hF : Continuous F) :
    Set.range F ⊆ closure (Set.range (bandOpenCoreMap F)) := by
  let U : Set (I × BandWidth) := {p | (p.1 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
    (p.2 : ℝ) ∈ Ioo (-1 : ℝ) 1}
  let e : I × BandWidth → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have he : IsEmbedding e := IsEmbedding.subtypeVal.prodMap IsEmbedding.subtypeVal
  have himage : e '' U = Ioo (0 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro hp
      exact ⟨(⟨p.1, ⟨hp.1.1.le, hp.1.2.le⟩⟩,
        ⟨p.2, ⟨hp.2.1.le, hp.2.2.le⟩⟩), hp, rfl⟩
  have hd : Dense U := he.toIsInducing.dense_iff.mpr (by
    intro p
    rw [himage, closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1),
      closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact ⟨p.1.2, p.2.2⟩)
  have hcore : F '' U = Set.range (bandOpenCoreMap F) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(⟨p.1, ⟨p.1.2.1.le,p.1.2.2.le⟩⟩,
        ⟨p.2, ⟨p.2.2.1.le,p.2.2.2.le⟩⟩), ⟨p.1.2,p.2.2⟩, rfl⟩
  have hh := image_closure_subset_closure_image hF (s := U)
  rwa [hd.closure_eq, Set.image_univ, hcore] at hh

variable {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)

def squareOpenCoreMap : Metric.ball ((0,0) : ℝ × ℝ) D.radius → S :=
  fun z => D.square ⟨z, Metric.ball_subset_closedBall z.2⟩

theorem squareOpenCore_range : Set.range (squareOpenCoreMap D) = D.openSquare := by
  rw [D.openSquare_eq]
  ext x
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨⟨z,Metric.ball_subset_closedBall z.2⟩,z.2,rfl⟩
  · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,hz⟩,rfl⟩

theorem squareOpenCore_preconnected : IsPreconnected D.openSquare := by
  letI : ContractibleSpace (Metric.ball ((0,0) : ℝ × ℝ) D.radius) :=
    (convex_ball _ _).contractibleSpace ⟨(0,0), Metric.mem_ball_self D.radius_pos⟩
  rw [← squareOpenCore_range]
  exact (isConnected_range (D.square_embedded.continuous.comp
    (IsEmbedding.inclusion Metric.ball_subset_closedBall).continuous)).2

theorem squareOpenCore_dense_range : Set.range D.square ⊆ closure D.openSquare := by
  let U : Set (SupSquare D.radius) := {z | (z : ℝ × ℝ) ∈ Metric.ball ((0,0) : ℝ × ℝ) D.radius}
  have himage : (Subtype.val : SupSquare D.radius → ℝ × ℝ) '' U =
      Metric.ball ((0,0) : ℝ × ℝ) D.radius := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩; exact hz
    · intro hx; exact ⟨⟨x,Metric.ball_subset_closedBall hx⟩,hx,rfl⟩
  have hd : Dense U := Subtype.dense_iff.mpr (by
    rw [himage, closure_ball _ D.radius_pos.ne'])
  have hh := image_closure_subset_closure_image D.square_embedded.continuous (s := U)
  rw [hd.closure_eq, Set.image_univ] at hh
  simpa only [D.openSquare_eq] using hh

/-- The interior of the literal square with attached bands is connected. -/
theorem actual_band_interior_preconnected : IsPreconnected (interior (bandUnion D B)) := by
  let R1 := Set.range (bandOpenCoreMap B.first)
  let R2 := Set.range (bandOpenCoreMap B.second)
  let C := ((D.openSquare ∪ a.image) ∪ b.image) ∪ R1 ∪ R2
  let z0 : SupSquare D.radius := ⟨(0,0), by simpa using D.radius_pos.le⟩
  have hz0 : D.square z0 ∈ D.openSquare := by
    rw [D.openSquare_eq]
    exact ⟨z0, Metric.mem_ball_self D.radius_pos, rfl⟩
  have hza : D.square z0 ∈ a.image := (D.first_axis z0).mpr rfl
  have hzb : D.square z0 ∈ b.image := (D.second_axis z0).mpr rfl
  have hca : IsPreconnected a.image := (isConnected_range a.embedded.continuous).2
  have hcb : IsPreconnected b.image := (isConnected_range b.embedded.continuous).2
  have hC0 : IsPreconnected ((D.openSquare ∪ a.image) ∪ b.image) :=
    ((squareOpenCore_preconnected D).union _ hz0 hza hca).union _ (Or.inl hz0) hzb hcb
  let t : I := ⟨1/2, by norm_num⟩
  have hr1 : B.first (t,⟨0,by norm_num⟩) ∈ R1 := ⟨(⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),rfl⟩
  have hr2 : B.second (t,⟨0,by norm_num⟩) ∈ R2 := ⟨(⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),rfl⟩
  have ha1 : B.first (t,⟨0,by norm_num⟩) ∈ a.image := by
    rw [B.first_center]
    have hh : D.firstArc t ∈ Set.range D.firstArc := Set.mem_range_self _
    rw [D.firstArc_range] at hh
    exact hh.1
  have hb2 : B.second (t,⟨0,by norm_num⟩) ∈ b.image := by
    rw [B.second_center]
    have hh : D.secondArc t ∈ Set.range D.secondArc := Set.mem_range_self _
    rw [D.secondArc_range] at hh
    exact hh.1
  have hC : IsPreconnected C :=
    (hC0.union (B.first (t,⟨0,by norm_num⟩)) (Or.inl (Or.inr ha1)) hr1
      (bandOpenCore_preconnected _ B.first_embedded.continuous)).union (B.second (t,⟨0,by norm_num⟩))
        (Or.inl (Or.inr hb2)) hr2 (bandOpenCore_preconnected _ B.second_embedded.continuous)
  have hCint : C ⊆ interior (bandUnion D B) := by
    have hcurves := (compatibleOutsideBands_compact_connected_neighborhood_probe D B).2.2
    have hO : D.openSquare ⊆ interior (bandUnion D B) :=
      D.openSquare_open.subset_interior_iff.mpr (by
        rw [D.openSquare_eq]
        exact fun _ hx => Or.inl (Or.inl (Set.image_subset_range _ _ hx)))
    have hR (F : I × BandWidth → S) (hF : IsEmbedding F) (hFN : Set.range F ⊆ bandUnion D B) :
        Set.range (bandOpenCoreMap F) ⊆ interior (bandUnion D B) := by
      rintro x ⟨p,rfl⟩
      exact interior_mono hFN (embedded_band_open_rectangle_interior F hF _ _
        p.1.2.1 p.1.2.2 p.2.2.1 p.2.2.2)
    exact union_subset (union_subset (union_subset (union_subset hO
      (fun _ hx => hcurves (Or.inl hx))) (fun _ hx => hcurves (Or.inr hx)))
        (hR _ B.first_embedded (fun _ hx => Or.inl (Or.inr hx))))
          (hR _ B.second_embedded (fun _ hx => Or.inr hx))
  have hNclosure : bandUnion D B ⊆ closure C := by
    exact union_subset (union_subset
      ((squareOpenCore_dense_range D).trans (closure_mono (fun _ hx => Or.inl (Or.inl (Or.inl (Or.inl hx))))))
      ((bandOpenCore_dense_range _ B.first_embedded.continuous).trans
        (closure_mono (fun _ hx => Or.inl (Or.inr hx)))))
      ((bandOpenCore_dense_range _ B.second_embedded.continuous).trans
        (closure_mono (fun _ hx => Or.inr hx)))
  exact hC.subset_closure hCint (interior_subset.trans hNclosure)

#print axioms actual_band_interior_preconnected
end CurveComplex.CapBandGeometry
