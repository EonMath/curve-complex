import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalBoundaryParallelTransport
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFiniteEssentialSurgeryFirst
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalLocalizedCleanupReviewRequest
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalLocalizedLastRailContact
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOriginalFiniteCommonFace

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_finite_face_full_contact_common_step
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
    (anchor : C(Interval,↥F)) (a : ι → C(Interval,↥F))
    (hanchorEmb : Topology.IsEmbedding anchor)
    (haEmb : ∀ i, Topology.IsEmbedding (a i))
    (hanchorEnds : (anchor 0).val ∈ boundaryCircle S x R ∧
      (anchor 1).val ∈ boundaryCircle S x R)
    (haEnds : ∀ i, ((a i) 0).val ∈ boundaryCircle S x R ∧
      ((a i) 1).val ∈ boundaryCircle S x R)
    (hanchorProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (haProper : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
      ((a i) t).val ∉ frontier F)
    (hanchorEssential : ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range anchor ∪ Set.range v)
    (haEssential : ∀ i, ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range (a i) ∪ Set.range v)
    (hface : ∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j)))
    (hstart : ∀ i, anchor 0 ∉ Set.range (a i))
    (hfinite : ∀ i, (Set.range anchor ∩ Set.range (a i)).Finite)
    (hpositive : ∃ (u : Interval) (i : ι) (s : Interval),
      u ∈ Set.Ioo (0 : Interval) 1 ∧ s ∈ Set.Ioo (0 : Interval) 1 ∧
      anchor u = a i s) :
    ∃ (k : ι) (raw new oldCopy : C(Interval,↥F)),
      (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range raw ∪ Set.range v) ∧
      Topology.IsEmbedding new ∧ Topology.IsEmbedding oldCopy ∧
      (new 0).val ∈ boundaryCircle S x R ∧ (new 1).val ∈ boundaryCircle S x R ∧
      (oldCopy 0).val ∈ boundaryCircle S x R ∧ (oldCopy 1).val ∈ boundaryCircle S x R ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (new t).val ∉ frontier F) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (oldCopy t).val ∉ frontier F) ∧
      (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range new ∪ Set.range v) ∧
      (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range oldCopy ∪ Set.range v) ∧
      Disjoint (Set.range new) (Set.range oldCopy) ∧
      (∀ i, i ≠ k → Disjoint (Set.range new) (Set.range (a i))) ∧
      (∀ i, i ≠ k → Disjoint (Set.range oldCopy) (Set.range (a i))) ∧
      (Set.range new ∩ Set.range anchor).Finite ∧
      (Set.range new ∩ Set.range anchor).ncard < (Set.range (a k) ∩ Set.range anchor).ncard ∧
      ∃ H G : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range raw = Set.range new ∧
        (∀ i t z, i ≠ k → H.map (t,a i z) = a i z) ∧
        (∀ t z, H.map (t,oldCopy z) = oldCopy z) ∧
        (∀ t, (fun y => G.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => G.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        G.finalMap '' Set.range (a k) = Set.range oldCopy ∧
        (∀ i t z, i ≠ k → G.map (t,a i z) = a i z) := by
  classical
  obtain ⟨r,k,s,hr,hs,hcontact,hfirst,right,hrawEmb,hraw0,hraw1,hrawP,hrawEss,
    hrawOther,hbudget⟩ :=
    regional_original_finite_face_first_essential_surgery_with_first S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier anchor a
      hanchorEmb haEmb hanchorEnds haEnds hanchorProper haProper
      hanchorEssential haEssential hface hstart hfinite hpositive
  obtain ⟨oldCopy,hcopyEmb,hcopy0,hcopy1,hcopyP,hcopyOld,hcopyRaw,hcopyFace,
    G,hGB,hGF,hGmove,hGfix⟩ :=
    regional_original_first_contact_finite_face_common_face S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier anchor a k (haEmb k)
      (haEnds k).1 (haEnds k).2 (haProper k) hface r s hr.1 hcontact
      (fun t ht => hfirst k t ht) right
  have hcopyEss := (regional_essential_arc_ambient_transport F (boundaryCircle S x R)
    (a k) oldCopy G (hGB 1) hGmove).mp (haEssential k)
  let raw : C(Interval,↥F) :=
    (regionalRawSurgeryBranch anchor (a k) r s hcontact right).toContinuousMap
  let retained : Option {i : ι // i ≠ k} → C(Interval,↥F) :=
    fun i => match i with | none => oldCopy | some j => a j.val
  have hret : ∀ i, Disjoint (Set.range raw) (Set.range (retained i)) := by
    intro i
    cases i with
    | none => exact hcopyRaw.symm
    | some j => exact hrawOther j.val j.property
  obtain ⟨new,hnew,hnew0,hnew1,hnewP,hnewO,hnewRet,hcontacts,
    H,hHB,hHF,hmove,hfix,hout⟩ :=
    regional_original_raw_branch_supported_full_contact_cleanup S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier
      anchor (a k) hanchorEmb (haEmb k) hanchorEnds (haEnds k)
      hanchorProper (haProper k) r s hr hs hcontact (fun t ht => hfirst k t ht)
      (by simpa [Set.inter_comm] using hfinite k) right retained hret
      Set.univ isOpen_univ (Set.subset_univ _)
  have hnewEss := (regional_essential_arc_ambient_transport
    F (boundaryCircle S x R) raw new H (hHB 1) hmove).mp hrawEss
  have hcount := regional_cleanup_contact_containment_strict_drop anchor (a k) new r s
    hcontact (by simpa [Set.inter_comm] using hfinite k) hcontacts
  refine ⟨k,raw,new,oldCopy,hrawEss,hnew,hcopyEmb,hnew0,hnew1,hcopy0,hcopy1,
    hnewP,hcopyP,hnewEss,hcopyEss,hnewRet none,?_,hcopyFace,hcount.1,hcount.2,
    H,G,hHB,hHF,hmove,?_,?_,hGB,hGF,hGmove,hGfix⟩
  · intro i hi
    exact hnewRet (some ⟨i,hi⟩)
  · intro i t z hi
    exact hfix (some ⟨i,hi⟩) t z
  · intro t z
    exact hfix none t z

#print axioms regional_original_finite_face_full_contact_common_step
