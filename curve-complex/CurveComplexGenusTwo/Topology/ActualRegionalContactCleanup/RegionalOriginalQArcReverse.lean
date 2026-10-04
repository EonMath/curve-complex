import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem regional_original_Q_proper_arc_reverse
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (a : ProperArc S x R) :
    ∃ b : ProperArc S x R,
      (∀ t : Interval, b.val t = a.val (unitInterval.symm t)) ∧
      Set.range b.val = Set.range a.val := by
  let f : C(Interval,Q S x R) :=
    ⟨fun t => a.val (unitInterval.symm t),
      a.val.continuous.comp unitInterval.continuous_symm⟩
  have hf : Topology.IsEmbedding f :=
    a.property.1.comp unitInterval.symmHomeomorph.isEmbedding
  have hzero : f 0 ∈ boundaryQ S x R := by
    change a.val (unitInterval.symm 0) ∈ boundaryQ S x R
    rw [unitInterval.symm_zero]
    exact a.property.2.2.1
  have hone : f 1 ∈ boundaryQ S x R := by
    change a.val (unitInterval.symm 1) ∈ boundaryQ S x R
    rw [unitInterval.symm_one]
    exact a.property.2.1
  have hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      f t ∉ boundaryQ S x R := by
    intro t ht
    apply a.property.2.2.2 (unitInterval.symm t)
    have ht0 : (0 : ℝ) < (t : ℝ) := ht.1
    have ht1 : (t : ℝ) < 1 := ht.2
    constructor
    · change 0 < 1-(t : ℝ)
      linarith only [ht1]
    · change 1-(t : ℝ) < 1
      linarith only [ht0]
  let p : ProperArc S x R := ⟨f,hf,hzero,hone,hproper⟩
  have hrange : Set.range p.val = Set.range a.val := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨t,rfl⟩
      exact ⟨unitInterval.symm t,by
        change a.val (unitInterval.symm (unitInterval.symm t)) = a.val t
        rw [unitInterval.symm_involutive]⟩
  exact ⟨p,fun _ => rfl,hrange⟩

theorem regional_original_Q_essential_arc_reverse
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (a : EssentialProperArc S x R) :
    ∃ b : EssentialProperArc S x R,
      (∀ t : Interval, b.val.val t = a.val.val (unitInterval.symm t)) ∧
      Set.range b.val.val = Set.range a.val.val := by
  let f : C(Interval,Q S x R) :=
    ⟨fun t => a.val.val (unitInterval.symm t),
      a.val.val.continuous.comp unitInterval.continuous_symm⟩
  have hf : Topology.IsEmbedding f :=
    a.val.property.1.comp unitInterval.symmHomeomorph.isEmbedding
  have hzero : f 0 ∈ boundaryQ S x R := by
    change a.val.val (unitInterval.symm 0) ∈ boundaryQ S x R
    rw [unitInterval.symm_zero]
    exact a.val.property.2.2.1
  have hone : f 1 ∈ boundaryQ S x R := by
    change a.val.val (unitInterval.symm 1) ∈ boundaryQ S x R
    rw [unitInterval.symm_one]
    exact a.val.property.2.1
  have hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      f t ∉ boundaryQ S x R := by
    intro t ht
    apply a.val.property.2.2.2 (unitInterval.symm t)
    have hst : 0 < (unitInterval.symm t : ℝ) ∧
        (unitInterval.symm t : ℝ) < 1 := by
      have ht0 : (0 : ℝ) < (t : ℝ) := ht.1
      have ht1 : (t : ℝ) < 1 := ht.2
      change 0 < 1-(t : ℝ) ∧ 1-(t : ℝ) < 1
      exact ⟨by linarith only [ht1],by linarith only [ht0]⟩
    exact ⟨hst.1,hst.2⟩
  let p : ProperArc S x R := ⟨f,hf,hzero,hone,hproper⟩
  have hrange : Set.range p.val = Set.range a.val.val := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact Set.mem_range_self _
    · rintro ⟨t,rfl⟩
      exact ⟨unitInterval.symm t,by
        change a.val.val (unitInterval.symm (unitInterval.symm t)) = a.val.val t
        rw [unitInterval.symm_involutive]⟩
  have hpess : ¬ boundaryParallel S x R p := by
    intro hp
    apply a.property
    change ∃ b : C(Interval,Q S x R), Topology.IsEmbedding b ∧
      (∀ t, b t ∈ boundaryQ S x R) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a.val.val ∪ Set.range b
    obtain ⟨b,hb,hbB,d,hd,hdimage⟩ := hp
    exact ⟨b,hb,hbB,d,hd,by rw [← hrange]; exact hdimage⟩
  exact ⟨⟨p,hpess⟩,fun _ => rfl,hrange⟩

#print axioms regional_original_Q_proper_arc_reverse
#print axioms regional_original_Q_essential_arc_reverse
