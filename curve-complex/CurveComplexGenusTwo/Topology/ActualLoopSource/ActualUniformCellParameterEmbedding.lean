import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCellMovieFiniteGluing
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual affine uniform cell parameter is embedded. -/
theorem actual_uniform_cell_parameter_embedding (n : ℕ) (hn : 0<n) (k : Fin n × Fin n) :
    IsEmbedding (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
       ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)) := by
  have hc : Continuous (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
       ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)) := by
    exact ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.1).comp continuous_fst).prodMk
      ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.2).comp continuous_snd)
  refine (hc.isClosedEmbedding ?_).isEmbedding
  intro z w he
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply Prod.ext
  · apply Subtype.ext
    have hh := congrArg (fun x : Interval × Interval => x.1.val) he
    change ((k.1.val:ℝ)+z.1.val)/n=((k.1.val:ℝ)+w.1.val)/n at hh
    have h := (div_left_inj' hnR).mp hh
    linarith only [h]
  · apply Subtype.ext
    have hh := congrArg (fun x : Interval × Interval => x.2.val) he
    change ((k.2.val:ℝ)+z.2.val)/n=((k.2.val:ℝ)+w.2.val)/n at hh
    have h := (div_left_inj' hnR).mp hh
    linarith only [h]
/-- Original uniform cells overlap only at their literal cell boundaries. -/
theorem actual_uniform_cell_parameter_collision (n : ℕ) (hn : 0<n)
    (k l : Fin n × Fin n) (z w : Interval × Interval)
    (he : (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)=
      (ArcFinitePosition.intervalMeshParameter n hn l.1 w.1,
       ArcFinitePosition.intervalMeshParameter n hn l.2 w.2)) :
    (k=l ∧ z=w) ∨
      (z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) ∧
      (w.1=0 ∨ w.1=1 ∨ w.2=0 ∨ w.2=1) := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have coordinate (i j : Fin n) (s t : Interval)
      (hh : ArcFinitePosition.intervalMeshParameter n hn i s=
        ArcFinitePosition.intervalMeshParameter n hn j t) :
      (i=j ∧ s=t) ∨ ((s=0 ∨ s=1) ∧ (t=0 ∨ t=1)) := by
    have hv := congrArg Subtype.val hh
    change ((i.val:ℝ)+s.val)/n=((j.val:ℝ)+t.val)/n at hv
    have hv' := (div_left_inj' hnR).mp hv
    by_cases hij : i=j
    · left
      refine ⟨hij,?_⟩
      subst j
      exact Subtype.ext (by linarith only [hv'])
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hi : (i.val:ℝ)+1≤ j.val := by exact_mod_cast hij
        have hs : s=1 := Subtype.ext (by change s.val=1; linarith only [hv',hi,t.property.1,s.property.2])
        have ht : t=0 := Subtype.ext (by change t.val=0; linarith only [hv',hi,t.property.1,s.property.2])
        exact Or.inr ⟨Or.inr hs,Or.inl ht⟩
      · have hi : (j.val:ℝ)+1≤ i.val := by exact_mod_cast hji
        have hs : s=0 := Subtype.ext (by change s.val=0; linarith only [hv',hi,s.property.1,t.property.2])
        have ht : t=1 := Subtype.ext (by change t.val=1; linarith only [hv',hi,s.property.1,t.property.2])
        exact Or.inr ⟨Or.inl hs,Or.inr ht⟩
  rcases coordinate k.1 l.1 z.1 w.1 (congrArg Prod.fst he) with ⟨hkl,hzw⟩ | ⟨hz,hw⟩
  · rcases coordinate k.2 l.2 z.2 w.2 (congrArg Prod.snd he) with ⟨hkl',hzw'⟩ | ⟨hz,hw⟩
    · exact Or.inl ⟨Prod.ext hkl hkl',Prod.ext hzw hzw'⟩
    · exact Or.inr ⟨hz.elim (fun h => Or.inr (Or.inr (Or.inl h)))
          (fun h => Or.inr (Or.inr (Or.inr h))),
        hw.elim (fun h => Or.inr (Or.inr (Or.inl h)))
          (fun h => Or.inr (Or.inr (Or.inr h)))⟩
  · exact Or.inr ⟨hz.elim Or.inl (fun h => Or.inr (Or.inl h)),
      hw.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
end CurveComplex.HyperellipticModel
