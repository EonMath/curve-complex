import CurveComplexGenusTwo.Topology.TorusStrip.ProperLineSeparationCore

open Set Topology

namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

theorem proper_disjoint_lines_lie_on_one_side
    (F G : C(ℝ, Schoenflies.Plane))
    (hF : IsClosedEmbedding F)
    (hdis : Disjoint (Set.range F) (Set.range G)) :
    ∃ U V : Set Schoenflies.Plane,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (Set.range F)ᶜ ∧
      frontier U = Set.range F ∧ frontier V = Set.range F ∧
      (Set.range G ⊆ U ∨ Set.range G ⊆ V) := by
  let a := G 0
  have ha : a ∉ Set.range F := by
    exact Set.disjoint_right.mp hdis (Set.mem_range_self 0)
  have hJ := proper_line_inversion_isJordanCurve F hF.isProperMap hF.injective a ha
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hpart, hUf, hVf⟩ :=
    proper_line_sides_of_inversion_jordan (Set.range F) a ha hJ
  refine ⟨U, V, hU, hV, hUc, hVc, hUV, hpart, hUf, hVf, ?_⟩
  have hGconn : IsConnected (Set.range G) := by
    rw [← Set.image_univ]
    exact isConnected_univ.image G G.continuous.continuousOn
  have hcover : Set.range G ⊆ U ∪ V := by
    rw [hpart]
    exact Set.disjoint_right.mp hdis
  exact hGconn.isPreconnected.subset_or_subset hU hV hUV hcover

theorem proper_disjoint_lines_choose_facing_sides
    (F G : C(ℝ, Schoenflies.Plane))
    (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (Set.range F) (Set.range G)) :
    ∃ U Uout V Vout : Set Schoenflies.Plane,
      IsOpen U ∧ IsOpen Uout ∧ IsOpen V ∧ IsOpen Vout ∧
      IsConnected U ∧ IsConnected Uout ∧ IsConnected V ∧ IsConnected Vout ∧
      Disjoint U Uout ∧ Disjoint V Vout ∧
      U ∪ Uout = (Set.range F)ᶜ ∧ V ∪ Vout = (Set.range G)ᶜ ∧
      frontier U = Set.range F ∧ frontier Uout = Set.range F ∧
      frontier V = Set.range G ∧ frontier Vout = Set.range G ∧
      Set.range G ⊆ U ∧ Set.range F ⊆ V := by
  have orient (K L : C(ℝ, Schoenflies.Plane))
      (hK : IsClosedEmbedding K)
      (hKL : Disjoint (Set.range K) (Set.range L)) :
      ∃ A B : Set Schoenflies.Plane,
        IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = (Set.range K)ᶜ ∧
        frontier A = Set.range K ∧ frontier B = Set.range K ∧
        Set.range L ⊆ A := by
    obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hpart, hAf, hBf, hside⟩ :=
      proper_disjoint_lines_lie_on_one_side K L hK hKL
    rcases hside with hLA | hLB
    · exact ⟨A, B, hA, hB, hAc, hBc, hAB, hpart, hAf, hBf, hLA⟩
    · exact ⟨B, A, hB, hA, hBc, hAc, hAB.symm, by simpa [Set.union_comm] using hpart,
        hBf, hAf, hLB⟩
  obtain ⟨U, Uout, hU, hUout, hUc, hUoutc, hUUout, hUpart, hUf, hUoutf, hGinU⟩ :=
    orient F G hF hdis
  obtain ⟨V, Vout, hV, hVout, hVc, hVoutc, hVVout, hVpart, hVf, hVoutf, hFinV⟩ :=
    orient G F hG hdis.symm
  exact ⟨U, Uout, V, Vout, hU, hUout, hV, hVout,
    hUc, hUoutc, hVc, hVoutc, hUUout, hVVout,
    hUpart, hVpart, hUf, hUoutf, hVf, hVoutf, hGinU, hFinV⟩

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
