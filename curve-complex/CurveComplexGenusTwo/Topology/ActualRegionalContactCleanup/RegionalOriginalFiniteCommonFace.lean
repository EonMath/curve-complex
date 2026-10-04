import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalAutomaticStripEntry
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFStripAvoidClosed

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_first_contact_finite_face_common_face
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
    {ι : Type} [Fintype ι]
    (anchor : C(Interval,↥F)) (a : ι → C(Interval,↥F)) (k : ι)
    (hold : Topology.IsEmbedding (a k))
    (hold0 : ((a k) 0).val ∈ boundaryCircle S x R)
    (hold1 : ((a k) 1).val ∈ boundaryCircle S x R)
    (holdProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      ((a k) t).val ∉ frontier F)
    (hface : ∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j)))
    (r s : Interval) (hr : (0 : Interval) < r)
    (hcontact : anchor r = a k s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range (a k))
    (right : Bool) :
    ∃ b : C(Interval,↥F),
      Topology.IsEmbedding b ∧
      (b 0).val ∈ boundaryCircle S x R ∧
      (b 1).val ∈ boundaryCircle S x R ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
      Disjoint (Set.range b) (Set.range (a k)) ∧
      Disjoint (Set.range b)
        (Set.range (regionalRawSurgeryBranch anchor (a k) r s hcontact right)) ∧
      (∀ i, i ≠ k → Disjoint (Set.range b) (Set.range (a i))) ∧
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) ''
          {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => H.map (t,y)) ''
          {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range (a k) = Set.range b ∧
        (∀ i t z, i ≠ k → H.map (t,a i z) = a i z) := by
  classical
  let B := boundaryCircle S x R
  let C : Set ↥F := ⋃ i : {i : ι // i ≠ k}, Set.range (a i.val)
  have hC : IsClosed C := isClosed_iUnion_of_finite
    (fun i => (isCompact_range (a i.val).continuous).isClosed)
  have haU : Set.range (a k) ⊆ Cᶜ := by
    intro y hy hyC
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hyC
    exact Set.disjoint_left.mp (hface k i.val i.property.symm) hy hi
  obtain ⟨E,hE,hcenter,hend,hint,hopen⟩ :=
    regional_original_proper_arc_has_F_strip
      S g hg hS x R hR htarget F hFcompact hbase houtside
      J c hbaseDisjoint hfrontier (a k) hold hold0 hold1 holdProper
  obtain ⟨N,hN,hNU,hNcenter,hNend,hNint,hNopen⟩ :=
    regional_proper_F_strip_narrow_into_open F B (a k) E hE
      hcenter hend hint hopen Cᶜ hC.isOpen_compl haU
  have hBFront : B ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  obtain ⟨b,hb,hb0,hb1,hbp,hbk,hbranch,H,hHB,hHF,hmove,hout⟩ :=
    regional_first_contact_strip_common_face_automatic
      F B hFcompact hBFront anchor (a k) hold r s hr hcontact hfirst
      N hN hNcenter hNend hNint hNopen right
  have hfix : ∀ i t z, i ≠ k → H.map (t,a i z) = a i z := by
    intro i t z hi
    apply hout
    intro hzN
    exact (hNU hzN) (Set.mem_iUnion.mpr ⟨⟨i,hi⟩,Set.mem_range_self z⟩)
  have hbOther : ∀ i, i ≠ k → Disjoint (Set.range b) (Set.range (a i)) := by
    intro i hi
    apply Set.disjoint_left.mpr
    intro y hyb hyi
    rw [← hmove] at hyb
    obtain ⟨p,hp,hpy⟩ := hyb
    obtain ⟨z,hzy⟩ := hyi
    have hfixed := hfix i 1 z hi
    change H.finalMap (a i z) = a i z at hfixed
    have heq : H.finalMap p = H.finalMap (a i z) := by
      calc
        H.finalMap p = y := hpy
        _ = a i z := hzy.symm
        _ = H.finalMap (a i z) := hfixed.symm
    obtain ⟨e,he⟩ := H.homeomorphism_at 1
    change H.map (1,p) = H.map (1,a i z) at heq
    have hpz : p = a i z := e.injective (by simpa only [he] using heq)
    exact Set.disjoint_left.mp (hface k i hi.symm) hp (hpz ▸ Set.mem_range_self z)
  exact ⟨b,hb,hb0,hb1,hbp,hbk,hbranch,hbOther,H,hHB,hHF,hmove,hfix⟩

#print axioms regional_original_first_contact_finite_face_common_face
