import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFLocalEssentialSurgery
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFProperBranchToQ
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOriginalFEssentialToQ

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_F_first_contact_raw_pair_essential
    (S : Type) [TopologicalSpace S]
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
    (a b d e : C(Interval,↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hd : Topology.IsEmbedding d) (he : Topology.IsEmbedding e)
    (ha0 : (a 0).val ∈ boundaryCircle S x R)
    (ha1 : (a 1).val ∈ boundaryCircle S x R)
    (hb0 : (b 0).val ∈ boundaryCircle S x R)
    (hb1 : (b 1).val ∈ boundaryCircle S x R)
    (had : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    (hbd : ∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F)
    (hdd : ∀ t ∈ Set.Ioo (0 : Interval) 1, (d t).val ∉ frontier F)
    (hed : ∀ t ∈ Set.Ioo (0 : Interval) 1, (e t).val ∉ frontier F)
    (haess : ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a ∪ Set.range v)
    (hbess : ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range b ∪ Set.range v)
    (r u : Interval) (hr0 : 0 < r) (hr1 : r < 1)
    (hu0 : 0 < u) (hu1 : u < 1)
    (hcontact : a r = b u)
    (hprefix : ∀ s t : Interval, t ≤ r → b s = a t → s = u ∧ t = r)
    (hd0 : d 0 = a 0) (he0 : e 0 = a 0)
    (hd1 : d 1 = b 0) (he1 : e 1 = b 1)
    (hdimage : Set.range d = (a '' Set.Icc 0 r) ∪ (b '' Set.Icc 0 u))
    (heimage : Set.range e = (a '' Set.Icc 0 r) ∪ (b '' Set.Icc u 1)) :
    (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range d ∪ Set.range v) ∨
    (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range e ∪ Set.range v) := by
  let B : Set S := boundaryCircle S x R
  have hBF : B ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  let i : C(↥F,Q S x R) :=
    ⟨fun y => ⟨y.val,houtside y.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hi : Topology.IsEmbedding i := by
    apply Topology.IsEmbedding.of_comp i.continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  let qa : ProperArc S x R :=
    ⟨i.comp a,hi.comp ha,ha0,ha1,
      (fun t ht hbt => had t ht (hBF hbt))⟩
  let qb : ProperArc S x R :=
    ⟨i.comp b,hi.comp hb,hb0,hb1,
      (fun t ht hbt => hbd t ht (hBF hbt))⟩
  have hqa : ¬ boundaryParallel S x R qa := by
    exact regional_original_F_essential_arc_is_Q_essential
      S g hg hS x R hR htarget F hFcompact hbase houtside
      J c hbaseDisjoint hfrontier a ha ha0 ha1 had haess
  have hqb : ¬ boundaryParallel S x R qb := by
    exact regional_original_F_essential_arc_is_Q_essential
      S g hg hS x R hR htarget F hFcompact hbase houtside
      J c hbaseDisjoint hfrontier b hb hb0 hb1 hbd hbess
  let aq : EssentialProperArc S x R := ⟨qa,hqa⟩
  let bq : EssentialProperArc S x R := ⟨qb,hqb⟩
  obtain ⟨dq,hdq⟩ := regional_original_F_proper_branch_to_Q
    x R F houtside B rfl hBF d hd (hd0 ▸ ha0) (hd1 ▸ hb0) hdd
  obtain ⟨eq,heq⟩ := regional_original_F_proper_branch_to_Q
    x R F houtside B rfl hBF e he (he0 ▸ ha0) (he1 ▸ hb1) hed
  exact regional_F_first_contact_raw_pair_has_essential_branch
    S x R g hg hS hR htarget F B houtside rfl
    a b d e aq bq dq eq (fun _ => rfl) (fun _ => rfl)
    (fun t => (congrArg Subtype.val (hdq t)).symm)
    (fun t => (congrArg Subtype.val (heq t)).symm)
    r u hr0 hr1 hu0 hu1 hcontact hprefix
    hd0 he0 hd1 he1 hdimage heimage

#print axioms regional_original_F_first_contact_raw_pair_essential
