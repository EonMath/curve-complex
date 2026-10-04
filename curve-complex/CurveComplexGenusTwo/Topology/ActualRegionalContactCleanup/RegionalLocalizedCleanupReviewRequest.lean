import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFStripAvoidClosed
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRawBranchBilateralCleanup
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRelativeSupportNeighborhood

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_raw_branch_supported_full_contact_cleanup
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F)
    (hbase : boundaryCircle S x R ⊆ F)
    (houtside : F ⊆ (openDisk S x R)ᶜ)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image (boundaryCircle S x R))
    (hfrontier : frontier F = boundaryCircle S x R ∪ ⋃ i, (c i).val.image)
    (anchor old : C(Interval,↥F))
    (ha : Topology.IsEmbedding anchor) (ho : Topology.IsEmbedding old)
    (haends : (anchor 0).val ∈ boundaryCircle S x R ∧
      (anchor 1).val ∈ boundaryCircle S x R)
    (hoends : (old 0).val ∈ boundaryCircle S x R ∧
      (old 1).val ∈ boundaryCircle S x R)
    (hap : ∀ t ∈ Set.Ioo (0 : Interval) 1, (anchor t).val ∉ frontier F)
    (hop : ∀ t ∈ Set.Ioo (0 : Interval) 1, (old t).val ∉ frontier F)
    (r s : Interval) (hr : r ∈ Set.Ioo (0 : Interval) 1)
    (hs : s ∈ Set.Ioo (0 : Interval) 1)
    (hcontact : anchor r = old s)
    (hfirst : ∀ t < r, anchor t ∉ Set.range old)
    (hfinite : (Set.range old ∩ Set.range anchor).Finite)
    (right : Bool)
    {ι : Type} [Fintype ι] (retained : ι → C(Interval,↥F))
    (havoid : ∀ i, Disjoint
      (Set.range (regionalRawSurgeryBranch anchor old r s hcontact right))
      (Set.range (retained i)))
    (O : Set ↥F) (hO : IsOpen O)
    (hbranchO : Set.range (regionalRawSurgeryBranch anchor old r s hcontact right) ⊆ O) :
    ∃ b : C(Interval,↥F),
      Topology.IsEmbedding b ∧
      (b 0).val ∈ boundaryCircle S x R ∧
      (b 1).val ∈ boundaryCircle S x R ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
      Set.range b ⊆ O ∧
      (∀ i, Disjoint (Set.range b) (Set.range (retained i))) ∧
      Set.range b ∩ Set.range anchor ⊆
        (Set.range old ∩ Set.range anchor) \ {old s} ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) ''
          {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => H.map (t,y)) ''
          {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range
          (regionalRawSurgeryBranch anchor old r s hcontact right) = Set.range b ∧
        (∀ i t z, H.map (t,retained i z) = retained i z) ∧
        (∀ t y, y ∉ O → H.map (t,y) = y) := by
  let a : C(Interval,↥F) :=
    (regionalRawSurgeryBranch anchor old r s hcontact right).toContinuousMap
  have hproper := regionalRawSurgeryBranch_proper anchor old ha ho hap hop
    haends.1 hoends.1 hoends.2 r s hr hs hcontact hfirst right
  have haE : Topology.IsEmbedding a := hproper.1
  obtain ⟨U,hU,haU,hUO,hUret⟩ :=
    regional_relative_support_neighborhood a retained havoid O hO hbranchO
  obtain ⟨E,hE,hEc,hEe,hEi,hEo⟩ := regional_original_proper_arc_has_F_strip
    S g hg hS x R hR htarget F hFcompact hbase houtside J c hbaseDisjoint hfrontier
    a haE hproper.2.1 hproper.2.2.1 hproper.2.2.2
  obtain ⟨N,hN,hNU,hNc,hNe,hNi,hNo⟩ := regional_proper_F_strip_narrow_into_open
    F (boundaryCircle S x R) a E hE hEc hEe hEi hEo U hU haU
  have hBF : boundaryCircle S x R ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  obtain ⟨b,hb,hb0,hb1,hbp,hbN,hcontacts,H,hHB,hHF,hmove,hout⟩ :=
    regional_raw_branch_profile_cleanup (boundaryCircle S x R) hBF hFcompact
      anchor old ha r s hcontact right haE hfinite N hN hNc hNe hNi hNo hr
  refine ⟨b,hb,hb0,hb1,hbp,hbN.trans (hNU.trans hUO),?_,hcontacts,
    H,hHB,hHF,hmove,?_,?_⟩
  · intro i
    exact (hUret i).mono_left (hbN.trans hNU)
  · intro i t z
    apply hout t (retained i z)
    intro hy
    exact Set.disjoint_left.mp (hUret i) (hNU hy) (Set.mem_range_self z)
  · intro t y hy
    exact hout t y (fun hn => hy (hUO (hNU hn)))

#print axioms regional_original_raw_branch_supported_full_contact_cleanup
