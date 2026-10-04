import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
namespace CurveComplex.HyperellipticModel.ArcSurgery
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
attribute [local instance] instDecidableEqEssentialArcClass_arcSurgeryProducers
theorem surgery_common_simplex (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x)
    (σ : Finset (EssentialArcClass M)) (hF : σ ⊆ F)
    (hσ : IsArcSimplex M σ) (hx : x.selected.val ∈ σ) :
    IsArcSimplex M (σ ∪ replacementClasses M anchor F P x R)  := by
  classical
  have down {τ υ : Finset (EssentialArcClass M)} (hsub : τ ⊆ υ)
      (hυ : IsArcSimplex M υ) : IsArcSimplex M τ := by
    obtain ⟨rep, hrep, hdisj⟩ := hυ
    refine ⟨fun v => rep ⟨v.val, hsub v.property⟩, fun v => hrep _, ?_⟩
    intro v w hne
    apply hdisj
    exact fun he => hne (Subtype.ext (Subtype.mk.inj he))
  let T := σ ∪ replacementClasses M anchor F P x R
  have pick : ∀ v : {v // v ∈ T}, v.val ∉ σ →
      ∃ side : {side // side ∈ R.retained}, vertex M (R.pushed side) = v.val := by
    intro v hv
    have hn : v.val ∈ replacementClasses M anchor F P x R :=
      (Finset.mem_union.mp v.property).resolve_left hv
    obtain ⟨side, _, he⟩ := Finset.mem_image.mp hn
    exact ⟨side, he⟩
  let side (v : {v // v ∈ T}) (hv : v.val ∉ σ) := Classical.choose (pick v hv)
  have side_eq (v : {v // v ∈ T}) (hv : v.val ∉ σ) :
      vertex M (R.pushed (side v hv)) = v.val := Classical.choose_spec (pick v hv)
  let rep (v : {v // v ∈ T}) : EssentialMarkedArc M :=
    if hv : v.val ∈ σ then P.rep ⟨v.val, hF hv⟩ else R.pushed (side v hv)
  refine ⟨rep, ?_, ?_⟩
  · intro v
    by_cases hv : v.val ∈ σ
    · simpa [rep, hv, vertex] using P.represents ⟨v.val, hF hv⟩
    · simpa [rep, hv, vertex] using side_eq v hv
  · intro v w hvw
    have hval : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
    have pair (u z : {v // v ∈ T}) (hu : u.val ∈ σ) (hz : z.val ∈ σ) :
        IsArcSimplex M {u.val, z.val} := by
      apply down _ hσ
      intro q hq
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hq : q = u.val ∨ q = z.val) with hq | hq
      · simpa [hq] using hu
      · simpa [hq] using hz
    by_cases hv : v.val ∈ σ <;> by_cases hw : w.val ∈ σ
    · simp only [rep, dite_eq_left hv, dite_eq_left hw]
      exact P.simplex_disjoint ⟨v.val, hF hv⟩ ⟨w.val, hF hw⟩
        (fun h => hval (Subtype.mk.inj h)) (pair v w hv hw)
    · simp only [rep, dite_eq_left hv, dite_eq_right hw]
      by_cases he : v.val = x.selected.val
      · have hind : (⟨v.val, hF hv⟩ : {v // v ∈ F}) = x.selected := Subtype.ext he
        rw [hind]
        exact (R.disjoint_old (side w hw)).symm
      · exact (R.disjoint_neighbors (side w hw) ⟨v.val, hF hv⟩
          (fun h => he (congrArg Subtype.val h))
          (pair v ⟨x.selected.val, Finset.mem_union_left _ hx⟩ hv hx)).symm
    · simp only [rep, dite_eq_right hv, dite_eq_left hw]
      by_cases he : w.val = x.selected.val
      · have hind : (⟨w.val, hF hw⟩ : {v // v ∈ F}) = x.selected := Subtype.ext he
        rw [hind]
        exact R.disjoint_old (side v hv)
      · exact R.disjoint_neighbors (side v hv) ⟨w.val, hF hw⟩
          (fun h => he (congrArg Subtype.val h))
          (pair w ⟨x.selected.val, Finset.mem_union_left _ hx⟩ hw hx)
    · simp only [rep, dite_eq_right hv, dite_eq_right hw]
      apply R.pushed_disjoint
      intro he
      apply hval
      rw [← side_eq v hv, ← side_eq w hw, he]



end CurveComplex.HyperellipticModel.ArcSurgery
