import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFiniteFullContactCommonStep
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalNeighborCommonCopy

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_finite_graph_tied_full_contact_common_step
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
    (adjacent : ι → ι → Prop)
    (hadjSymm : ∀ i j, adjacent i j → adjacent j i) (hadjIrrefl : ∀ i, ¬ adjacent i i)
    (hface : ∀ i j, adjacent i j → Disjoint (Set.range (a i)) (Set.range (a j)))
    (hstart : ∀ i, anchor 0 ∉ Set.range (a i))
    (hfinite : ∀ i, (Set.range anchor ∩ Set.range (a i)).Finite)
    (hpositive : ∃ (u : Interval) (i : ι) (s : Interval),
      u ∈ Set.Ioo (0 : Interval) 1 ∧ s ∈ Set.Ioo (0 : Interval) 1 ∧
      anchor u = a i s) :
    ∃ (r : Interval) (k : ι) (s : Interval),
      r ∈ Set.Ioo (0 : Interval) 1 ∧ s ∈ Set.Ioo (0 : Interval) 1 ∧
      (∀ i t, t < r → anchor t ∉ Set.range (a i)) ∧
      ∃ hcontact : anchor r = a k s,
      ∃ right : Bool,
      let raw := (regionalRawSurgeryBranch anchor (a k) r s hcontact right).toContinuousMap
      ∃ new oldCopy : C(Interval,↥F),
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
      (∀ i, adjacent k i → Disjoint (Set.range new) (Set.range (a i))) ∧
      (∀ i, adjacent k i → Disjoint (Set.range oldCopy) (Set.range (a i))) ∧
      Set.range new ∩ Set.range anchor ⊆
        (Set.range (a k) ∩ Set.range anchor) \ {a k s} ∧
      (Set.range new ∩ Set.range anchor).Finite ∧
      (Set.range new ∩ Set.range anchor).ncard < (Set.range (a k) ∩ Set.range anchor).ncard ∧
      ∃ H G : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range raw = Set.range new ∧
        (∀ i t z, adjacent k i → H.map (t,a i z) = a i z) ∧
        (∀ t z, H.map (t,oldCopy z) = oldCopy z) ∧
        (∀ t, (fun y => G.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => G.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        G.finalMap '' Set.range (a k) = Set.range oldCopy ∧
        (∀ i t z, adjacent k i → G.map (t,a i z) = a i z) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  have hBF : boundaryCircle S x R ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  obtain ⟨r,k,s,hr,hs,hcontact,hclear,hbranches⟩ :=
    regional_finite_family_first_proper_surgery_pair anchor a
      hanchorEmb haEmb hanchorProper haProper hBF hanchorEnds.1
      haEnds hstart hfinite hpositive
  let d := regionalRawSurgeryBranch anchor (a k) r s hcontact false
  let e := regionalRawSurgeryBranch anchor (a k) r s hcontact true
  obtain ⟨hdEmb,hd0,hd1,hdProper,hdBudget⟩ := hbranches false
  obtain ⟨heEmb,he0,he1,heProper,heBudget⟩ := hbranches true
  have hprefix : ∀ v t : Interval, t ≤ r → a k v = anchor t →
      v = s ∧ t = r :=
    regional_finite_first_contact_selected_prefix_unique anchor a
      haEmb r s k hcontact hclear
  have hess := regional_original_F_first_contact_raw_pair_essential
    S g hg hS x R hR htarget F hFcompact hbase houtside
    J c hbaseDisjoint hfrontier anchor (a k) d e
    hanchorEmb (haEmb k) hdEmb heEmb
    hanchorEnds.1 hanchorEnds.2 (haEnds k).1 (haEnds k).2
    hanchorProper (haProper k) hdProper heProper
    hanchorEssential (haEssential k)
    r s hr.1 hr.2 hs.1 hs.2 hcontact hprefix
    (by exact d.source) (by exact e.source)
    (by exact d.target) (by exact e.target)
    (by exact regionalRawSurgeryBranch_range anchor (a k) r s hcontact false)
    (by exact regionalRawSurgeryBranch_range anchor (a k) r s hcontact true)
  obtain ⟨right,hrawEss⟩ : ∃ right : Bool,
      ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
        (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
        ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding D ∧
          D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range (regionalRawSurgeryBranch anchor (a k) r s hcontact right) ∪
              Set.range v := by
    rcases hess with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  let raw : C(Interval,↥F) :=
    (regionalRawSurgeryBranch anchor (a k) r s hcontact right).toContinuousMap
  have hrawOther : ∀ i, adjacent k i → Disjoint (Set.range raw) (Set.range (a i)) := by
    intro i hi
    apply Set.disjoint_left.mpr
    intro y hy hyi
    change y ∈ Set.range (regionalRawSurgeryBranch anchor (a k) r s hcontact right) at hy
    rw [regionalRawSurgeryBranch_range] at hy
    rcases hy with ⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩
    · rcases lt_or_eq_of_le hu.2 with hur | hur
      · exact hclear i u hur hyi
      · have hp : a k s ∈ Set.range (a i) := by simpa [hur,hcontact] using hyi
        exact Set.disjoint_left.mp (hface k i hi) (Set.mem_range_self s) hp
    · exact Set.disjoint_left.mp (hface k i hi) (Set.mem_range_self v) hyi
  let neighbors : {i : ι // adjacent k i} → C(Interval,↥F) := fun i => a i.val
  obtain ⟨oldCopy,hcopyEmb,hcopy0,hcopy1,hcopyP,hcopyOld,hcopyRaw,hcopyFace,
    G,hGB,hGF,hGmove,hGfix⟩ :=
    regional_original_first_contact_neighbor_common_face S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier anchor neighbors (a k)
      (haEmb k) (haEnds k).1 (haEnds k).2 (haProper k)
      (fun i => hface k i.val i.property) r s hr.1 hcontact
      (fun t ht => hclear k t ht) right
  have hcopyEss := (regional_essential_arc_ambient_transport F (boundaryCircle S x R)
    (a k) oldCopy G (hGB 1) hGmove).mp (haEssential k)
  let retained : Option {i : ι // adjacent k i} → C(Interval,↥F) :=
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
      hanchorProper (haProper k) r s hr hs hcontact (fun t ht => hclear k t ht)
      (by simpa [Set.inter_comm] using hfinite k) right retained hret
      Set.univ isOpen_univ (Set.subset_univ _)
  have hnewEss := (regional_essential_arc_ambient_transport
    F (boundaryCircle S x R) raw new H (hHB 1) hmove).mp hrawEss
  have hcount := regional_cleanup_contact_containment_strict_drop anchor (a k) new r s
    hcontact (by simpa [Set.inter_comm] using hfinite k) hcontacts
  refine ⟨r,k,s,hr,hs,hclear,hcontact,right,new,oldCopy,hrawEss,hnew,hcopyEmb,hnew0,hnew1,hcopy0,hcopy1,
    hnewP,hcopyP,hnewEss,hcopyEss,hnewRet none,?_,?_,hcontacts,hcount.1,hcount.2,
    H,G,hHB,hHF,hmove,?_,?_,hGB,hGF,hGmove,?_⟩
  · intro i hi
    exact hnewRet (some ⟨i,hi⟩)
  · intro i hi
    exact hcopyFace ⟨i,hi⟩
  · intro i t z hi
    exact hfix (some ⟨i,hi⟩) t z
  · intro t z
    exact hfix none t z
  · intro i t z hi
    exact hGfix ⟨i,hi⟩ t z

#print axioms regional_original_finite_graph_tied_full_contact_common_step
