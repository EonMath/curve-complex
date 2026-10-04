import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.Subarc

namespace Schoenflies
open Set

/-- General Jordan crosscut alternation used for source Fact3.5 simplicity, obtained from canonical arbitrary-crosscut component/closure classification. The first crosscut is a genuinely arbitrary embedded arc, with no polygonality assumption. -/
theorem arbitrary_jordan_crosscut_alternating_inter_nonempty {C P A₁ A₂ Q : Set Plane} {a b w₁ w₂ : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P a b)
    (hcut : IsCutPair C a b A₁ A₂) (hPC : P ∩ C = {a,b})
    (hPD : P \ {a,b} ⊆ inside C) (hQ : IsPreconnected Q) (hQD : Q ⊆ inside C)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ A₁) (hw₁B : w₁ ∉ A₂) (hw₂B : w₂ ∈ A₂) (hw₂A : w₂ ∉ A₁) :
    (Q ∩ P).Nonempty := by
  obtain ⟨hexh,hdis,hne₁,hne₂,hneq,hcomp₁,hcomp₂,hcomponents,hclosure₁,hclosure₂⟩ :=
    general_crosscut_arbitrary hC hP hcut hPC hPD
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty,Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ inside C \ P := fun z hz => ⟨hQD hz,fun hp => hempty z ⟨hz,hp⟩⟩
  obtain ⟨z,hz⟩ : Q.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h,closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ inside (A₁ ∪ P) ∪ inside (A₂ ∪ P) := by
    rw [← hexh]
    exact hsub hz
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ inside (A₁ ∪ P) := by
      have h := hQ.subset_connectedComponentIn hz hsub
      rwa [hcomp₁ z hz₁] at h
    have hmem : w₂ ∈ closure (inside (A₁ ∪ P)) ∩ C :=
      ⟨closure_mono hQ₁ hw₂,hcut.snd_subset hw₂B⟩
    rw [hclosure₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ inside (A₂ ∪ P) := by
      have h := hQ.subset_connectedComponentIn hz hsub
      rwa [hcomp₂ z hz₂] at h
    have hmem : w₁ ∈ closure (inside (A₂ ∪ P)) ∩ C :=
      ⟨closure_mono hQ₂ hw₁,hcut.fst_subset hw₁A⟩
    rw [hclosure₂] at hmem
    exact hw₁B hmem

end Schoenflies
