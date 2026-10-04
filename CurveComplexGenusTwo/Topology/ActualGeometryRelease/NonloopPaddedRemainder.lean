import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedTwoSideDisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_nonloop_initial_side_produces_padded_remainder
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
      (K D W : Set S) (hK : K.Finite) (hKa : K ⊆ arcInterior M a)
      (hW : IsOpen W)
      (hcoreW : (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β ⊆ W)
      (hD : D ∩ a.val.image = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β) :
      ∃ (hi : ℝ) (C R : Set S), β < hi ∧ hi < 1 ∧
        C = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∧
        IsCompact C ∧ IsCompact R ∧ C ⊆ W ∧ a.val.image = C ∪ R ∧
        a.val.map 0 ∈ R ∧ a.val.map 1 ∈ R ∧
        D ∩ R = {a.val.map 0} ∧
        C ∩ K ⊆ (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β ∧
        Disjoint (R ∩ K) C := by
  letI : T2Space S := M.sphere.symm.t2Space
  have hane := actualRepresentative_nonloop M a ha
  have haInjective : Function.Injective a.val.map := NonLoopArc.injective ⟨a.val,hane⟩
  let g : ℝ → S := a.val.map ∘ projIcc 0 1 zero_le_one
  have hgc : Continuous g := a.val.continuous.comp continuous_projIcc
  have hgi (t u : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1)
      (he : g t = g u) : t = u := by
    have hh : a.val.map (⟨t,ht⟩ : Interval) = a.val.map ⟨u,hu⟩ := by
      simpa only [g,Function.comp_apply,projIcc_of_mem zero_le_one ht,
        projIcc_of_mem zero_le_one hu] using he
    exact congrArg Subtype.val (haInjective hh)
  have hg0 : g 0 = a.val.map 0 := by simp [g]
  have hg1 : g 1 = a.val.map 1 := by simp [g]
  let F := K \ (g '' Icc 0 β)
  have hFclosed : IsClosed F := (hK.subset diff_subset).isClosed
  let N := g ⁻¹' (W ∩ Fᶜ)
  have hN : IsOpen N := (hW.inter hFclosed.isOpen_compl).preimage hgc
  have hβN : β ∈ N := ⟨hcoreW ⟨β,⟨hβ0.le,le_rfl⟩,rfl⟩,
    fun hp => hp.2 ⟨β,⟨hβ0.le,le_rfl⟩,rfl⟩⟩
  obtain ⟨δ,hδ,hδN⟩ := Metric.isOpen_iff.mp hN β hβN
  let ε := min δ (1-β)/2
  have hε : 0 < ε := half_pos (lt_min hδ (sub_pos.mpr hβ1))
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ (1-β)]
  have hεβ : ε < 1-β := by dsimp [ε]; linarith [min_le_right δ (1-β)]
  let hi := β+ε
  have hβhi : β < hi := by dsimp [hi]; linarith
  have hhi1 : hi < 1 := by dsimp [hi]; linarith
  have hhi0 : 0 < hi := hβ0.trans hβhi
  have hslabN (t : ℝ) (ht : t ∈ Icc β hi) : t ∈ N := by
    apply hδN
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1)]
    dsimp [hi] at ht
    linarith [ht.2]
  let C := g '' Icc 0 hi
  let R := (g '' Icc hi 1) ∪ {a.val.map 0}
  have hCcompact : IsCompact C := isCompact_Icc.image hgc
  have hRcompact : IsCompact R := (isCompact_Icc.image hgc).union isCompact_singleton
  have hCsub : C ⊆ a.val.image := by rintro x ⟨t,ht,rfl⟩; exact mem_range_self _
  have hRsub : R ⊆ a.val.image := by
    rintro x (⟨t,ht,rfl⟩ | hx)
    · exact mem_range_self _
    · exact mem_singleton_iff.mp hx ▸ mem_range_self _
  have hK0 : a.val.map 0 ∉ K := fun hk => (hKa hk).2 a.val.start_marked
  have hhiK : g hi ∉ K := by
    intro hk
    have hc : g hi ∈ g '' Icc 0 β := by
      by_contra hn
      exact (hslabN hi ⟨hβhi.le,le_rfl⟩).2 ⟨hk,hn⟩
    obtain ⟨t,ht,he⟩ := hc
    have hth : t=hi := hgi t hi ⟨ht.1,ht.2.trans hβ1.le⟩ ⟨hhi0.le,hhi1.le⟩ he
    exact (not_le_of_gt hβhi) (hth ▸ ht.2)
  have hDeq : D ∩ R = {a.val.map 0} := by
    ext x
    constructor
    · rintro ⟨hxD,hxR⟩
      rcases hxR with ⟨t,ht,rfl⟩ | hx
      · have hc : g t ∈ g '' Icc 0 β := hD ▸ ⟨hxD,mem_range_self _⟩
        obtain ⟨u,hu,he⟩ := hc
        have hut : u=t := hgi u t ⟨hu.1,hu.2.trans hβ1.le⟩
          ⟨hhi0.le.trans ht.1,ht.2⟩ he
        exact False.elim ((not_le_of_gt hβhi) ((hut ▸ hu.2).trans' ht.1))
      · exact hx
    · intro hx
      have he : x=a.val.map 0 := mem_singleton_iff.mp hx
      subst x
      refine ⟨?_,Or.inr (mem_singleton _)⟩
      have hc : a.val.map 0 ∈ g '' Icc 0 β := ⟨0,⟨le_rfl,hβ0.le⟩,hg0⟩
      exact (hD.symm ▸ hc).1
  refine ⟨hi,C,R,hβhi,hhi1,rfl,hCcompact,hRcompact,?_,?_,
    Or.inr (mem_singleton _),Or.inl ⟨1,⟨hhi1.le,le_rfl⟩,hg1⟩,hDeq,?_,?_⟩
  · rintro x ⟨t,ht,rfl⟩
    by_cases htβ : t ≤ β
    · exact hcoreW ⟨t,⟨ht.1,htβ⟩,rfl⟩
    · exact (hslabN t ⟨(not_le.mp htβ).le,ht.2⟩).1
  · apply Subset.antisymm
    · rintro x ⟨t,rfl⟩
      by_cases ht : (t:ℝ) ≤ hi
      · exact Or.inl ⟨t,⟨t.property.1,ht⟩,by simp [g,projIcc_of_mem zero_le_one t.property]⟩
      · exact Or.inr (Or.inl ⟨t,⟨(not_le.mp ht).le,t.property.2⟩,
          by simp [g,projIcc_of_mem zero_le_one t.property]⟩)
    · intro x hx; exact hx.elim (fun hc => hCsub hc) (fun hr => hRsub hr)
  · rintro x ⟨⟨t,ht,rfl⟩,hk⟩
    by_cases htβ : t ≤ β
    · exact ⟨t,⟨ht.1,htβ⟩,rfl⟩
    · by_contra hn
      exact (hslabN t ⟨(not_le.mp htβ).le,ht.2⟩).2 ⟨hk,hn⟩
  · apply disjoint_left.mpr
    rintro x ⟨hxR,hxK⟩ ⟨u,hu,heu⟩
    rcases hxR with ⟨t,ht,het⟩ | hx0
    · have hut : u=t := hgi u t ⟨hu.1,hu.2.trans hhi1.le⟩
        ⟨hhi0.le.trans ht.1,ht.2⟩ (heu.trans het.symm)
      have hth : t=hi := le_antisymm (hut ▸ hu.2) ht.1
      have hxhi : x=g hi := het.symm.trans (congrArg g hth)
      exact hhiK (hxhi ▸ hxK)
    · exact hK0 (mem_singleton_iff.mp hx0 ▸ hxK)

end CurveComplex.HyperellipticModel
