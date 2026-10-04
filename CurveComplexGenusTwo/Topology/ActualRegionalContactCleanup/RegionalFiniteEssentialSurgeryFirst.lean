import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFiniteFirstContactUniqueness
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOriginalFEssentialBranch

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_finite_face_first_essential_surgery_with_first
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
    ∃ (r : Interval) (k : ι) (s : Interval),
      r ∈ Set.Ioo (0 : Interval) 1 ∧
      s ∈ Set.Ioo (0 : Interval) 1 ∧
      ∃ hcontact : anchor r = a k s,
      (∀ i u, u < r → anchor u ∉ Set.range (a i)) ∧
      ∃ right : Bool,
        let branch := regionalRawSurgeryBranch anchor (a k) r s hcontact right
        Topology.IsEmbedding branch ∧
        (branch 0).val ∈ boundaryCircle S x R ∧
        (branch 1).val ∈ boundaryCircle S x R ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1,
          (branch t).val ∉ frontier F) ∧
        (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
          (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
          ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
            Topology.IsEmbedding D ∧
            D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
              Set.range branch ∪ Set.range v) ∧
        (∀ i, i ≠ k → Disjoint (Set.range branch) (Set.range (a i))) ∧
        ((Set.range branch \ (anchor '' Set.Icc 0 r)) ∩ Set.range anchor).ncard <
          ((a k '' (if right then Set.Icc s 1 else Set.Icc 0 s)) ∩
            Set.range anchor).ncard := by
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
  refine ⟨r,k,s,hr,hs,hcontact,hclear,?_⟩
  rcases hess with hdEss | heEss
  · refine ⟨false,hdEmb,hd0,hd1,hdProper,hdEss,?_,hdBudget⟩
    exact regional_raw_branch_disjoint_remaining_face anchor a hface
      r s k hcontact hclear false
  · refine ⟨true,heEmb,he0,he1,heProper,heEss,?_,heBudget⟩
    exact regional_raw_branch_disjoint_remaining_face anchor a hface
      r s k hcontact hclear true

#print axioms regional_original_finite_face_first_essential_surgery_with_first
