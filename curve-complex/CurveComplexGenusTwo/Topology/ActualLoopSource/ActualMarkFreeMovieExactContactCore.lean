import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkedArcCompactContactCore
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorCoreExactStrip
namespace CurveComplex.HyperellipticModel
open Set Topology ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual compact mark-free movie contact image constructs an exact original
arc axis strip and contact coordinate, also when the original arc is a loop.
The compact target core and strip are constructed from the actual movie. -/
theorem actual_mark_free_movie_exact_contact_core
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (G : C(Interval × Interval,S))
    (hGmarks : ∀ z,G z ∉ (M.cover.branch : Set S))
    (htop : ∀ z : Interval × Interval,z.1=1 → G z ∉ a.val.image) :
    ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S, ∃ hB : IsEmbedding B,
      (∀ z, B z ∉ (M.cover.branch : Set S)) ∧
      (∀ z, B z ∈ a.val.image ↔ z.2.val=0) ∧
    ∃ T : Set (Interval × Interval), IsOpen T ∧ G ⁻¹' a.val.image ⊆ T ∧
    ∃ L : C(T,Set.range B), (∀ z : T, (L z).val=G z.val) ∧
    ∃ ψ : C(T,ℝ),
      (∀ z : T, ψ z=((hB.toHomeomorph.symm (L z)).2:ℝ)) ∧
      (∀ z : T, 0<((hB.toHomeomorph.symm (L z)).1:ℝ) ∧
        ((hB.toHomeomorph.symm (L z)).1:ℝ)<1 ∧ -1<ψ z ∧ ψ z<1) ∧
      (∀ z : T, ψ z=0 ↔ G z.val ∈ a.val.image) ∧
      (∀ z : T, z.val.1=1 → ψ z≠0) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  have hdis : Disjoint (range G) (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,rfl⟩ hm
    exact hGmarks z hm
  obtain ⟨l,u,hl,hlu,hu,hcontact⟩ := actual_marked_arc_compact_contact_core M a
    (range G) (isCompact_range G.continuous) hdis
  let α := l/2
  let β := (u+1)/2
  have hα : 0<α := by dsimp [α]; linarith
  have hβ : β<1 := by dsimp [β]; linarith
  have hαβ : α<β := by dsimp [α,β]; linarith
  obtain ⟨B,hB,hBcenter,hBmarks,hBaxis⟩ :=
    actual_anchor_interior_core_exact_strip M a α β hα hβ hαβ
  let bandProjection : Schoenflies.Plane → Interval × Set.Icc (-1:ℝ) 1 := fun z =>
    (Set.projIcc 0 1 zero_le_one (z 0),Set.projIcc (-1) 1 (by norm_num) (z 1))
  let bandMap : Schoenflies.Plane → S := B ∘ bandProjection
  let rectangle : Set Schoenflies.Plane :=
    {z | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1}
  have hrectangleOpen : IsOpen rectangle := by
    convert (isOpen_Ioo.preimage (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop)).inter
      (isOpen_Ioo.preimage (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop)) using 1
    ext z
    simp only [rectangle,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_Ioo]
    tauto
  have hbandMapContinuous : Continuous bandMap := by
    exact hB.continuous.comp
      ((continuous_projIcc.comp (by fun_prop)).prodMk
        (continuous_projIcc.comp (by fun_prop)))
  have hbandProjection (z : Schoenflies.Plane) (hz : z ∈ rectangle) :
      ((bandProjection z).1:ℝ) = z 0 ∧ ((bandProjection z).2:ℝ) = z 1 := by
    exact ⟨by simp only [bandProjection,Set.projIcc_of_mem zero_le_one ⟨hz.1.le,hz.2.1.le⟩],
      by simp only [bandProjection,Set.projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
        ⟨hz.2.2.1.le,hz.2.2.2.le⟩]⟩
  have hbandMapInjective : Set.InjOn bandMap rectangle := by
    intro z hz w hw he
    have hp := hB.injective he
    have h0 := congrArg (fun t : Interval × Set.Icc (-1:ℝ) 1 => (t.1:ℝ)) hp
    have h1 := congrArg (fun t : Interval × Set.Icc (-1:ℝ) 1 => (t.2:ℝ)) hp
    rw [(hbandProjection z hz).1,(hbandProjection w hw).1] at h0
    rw [(hbandProjection z hz).2,(hbandProjection w hw).2] at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  let bandOpen : Set S := bandMap '' rectangle
  have hbandOpen : IsOpen bandOpen :=
    CurveComplex.surface_invariance_of_domain_probe bandMap rectangle hrectangleOpen
      hbandMapContinuous.continuousOn hbandMapInjective
  have hbandMarks : Disjoint bandOpen (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hm
    exact hBmarks (bandProjection z) hm
  let transverse : C(Set.range B,ℝ) :=
    ⟨fun x => ((hB.toHomeomorph.symm x).2:ℝ),by fun_prop⟩
  have hbandSubset : bandOpen ⊆ range B := by
    rintro _ ⟨z,hz,rfl⟩; exact mem_range_self (bandProjection z)
  let T : Set (Interval × Interval) := G ⁻¹' bandOpen
  have hTopen : IsOpen T := hbandOpen.preimage G.continuous
  have hGzerosInT : G ⁻¹' a.val.image ⊆ T := by
    intro z hz
    obtain ⟨q,hq⟩ := hz
    obtain ⟨hlq,hqu⟩ := hcontact q (by rw [hq]; exact mem_range_self z)
    have hαq : α<(q:ℝ) := by dsimp [α]; linarith
    have hqβ : (q:ℝ)<β := by dsimp [β]; linarith
    have hd : 0<β-α := sub_pos.mpr hαβ
    let t : Interval := ⟨((q:ℝ)-α)/(β-α),by
      constructor
      · exact div_nonneg (by linarith) hd.le
      · exact (div_le_one hd).mpr (by linarith)⟩
    have ht0 : 0<(t:ℝ) := div_pos (by linarith) hd
    have ht1 : (t:ℝ)<1 := (div_lt_one hd).mpr (by linarith)
    let w : Schoenflies.Plane := Schoenflies.Plane.mk (t:ℝ) 0
    have hw : w ∈ rectangle := by simpa [rectangle,w,Schoenflies.Plane.mk] using ⟨ht0,ht1⟩
    refine ⟨w,hw,?_⟩
    have hproj : bandProjection w=(t,⟨0,by norm_num⟩) := by
      apply Prod.ext <;> apply Subtype.ext
      · simpa [w,Schoenflies.Plane.mk] using (hbandProjection w hw).1
      · simpa [w,Schoenflies.Plane.mk] using (hbandProjection w hw).2
    change B (bandProjection w)=G z
    rw [hproj,hBcenter]
    have htq : actualCoreParameter α β hα.le hβ.le hαβ.le t=q := by
      apply Subtype.ext
      dsimp [actualCoreParameter,t]
      field_simp
      ring
    rw [htq]; exact hq
  let L : C(T,range B) := ⟨fun z => ⟨G z.val,hbandSubset z.property⟩,by fun_prop⟩
  let ψ : C(T,ℝ) := transverse.comp L
  have hψcoordinates (z : T) :
      0<((hB.toHomeomorph.symm (L z)).1:ℝ) ∧
      ((hB.toHomeomorph.symm (L z)).1:ℝ)<1 ∧ -1<ψ z ∧ ψ z<1 := by
    obtain ⟨w,hw,hwG⟩ := z.property
    have he : B (hB.toHomeomorph.symm (L z))=G z.val :=
      congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply (L z))
    have hcoord : hB.toHomeomorph.symm (L z)=bandProjection w :=
      hB.injective (he.trans hwG.symm)
    change 0<((hB.toHomeomorph.symm (L z)).1:ℝ) ∧
      ((hB.toHomeomorph.symm (L z)).1:ℝ)<1 ∧
      -1<((hB.toHomeomorph.symm (L z)).2:ℝ) ∧ ((hB.toHomeomorph.symm (L z)).2:ℝ)<1
    rw [hcoord,(hbandProjection w hw).1,(hbandProjection w hw).2]
    exact hw
  have hψzero (z : T) : ψ z=0 ↔ G z.val ∈ a.val.image := by
    let q := hB.toHomeomorph.symm (L z)
    have hq : B q=G z.val := congrArg Subtype.val (hB.toHomeomorph.apply_symm_apply (L z))
    have hh := hBaxis q
    rw [hq] at hh
    exact hh.symm
  refine ⟨B,hB,hBmarks,hBaxis,T,hTopen,hGzerosInT,L,(fun _ => rfl),
    ψ,(fun _ => rfl),hψcoordinates,hψzero,?_⟩
  intro z hz hzero
  exact htop z.val hz ((hψzero z).mp hzero)
end CurveComplex.HyperellipticModel
