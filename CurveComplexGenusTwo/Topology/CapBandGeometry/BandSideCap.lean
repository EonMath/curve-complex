import CurveComplexGenusTwo.Topology.CapBandGeometry.LocalCapSeam
import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierGeometry

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

noncomputable def bandSidePatch
    (t : I) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (sign : ℝ) (hsign : sign = -1 ∨ sign = 1) : BandWidth × I → I × BandWidth :=
  let δ := min (t : ℝ) (1 - (t : ℝ)) / 2
  fun p => (⟨(t : ℝ) + δ * (p.1 : ℝ), by
    have hdpos : 0 < δ := div_pos (lt_min ht0 (by linarith)) (by norm_num)
    have hd0 : δ ≤ (t : ℝ)/2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hd1 : δ ≤ (1 - (t : ℝ))/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    constructor <;> nlinarith [p.1.property.1, p.1.property.2]⟩,
    ⟨sign * (1 - (p.2 : ℝ)/2), by
      rcases hsign with hsign | hsign <;> rw [hsign] <;>
        constructor <;> nlinarith [p.2.property.1, p.2.property.2]⟩)

theorem bandSidePatch_embedded
    (t : I) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (sign : ℝ) (hsign : sign = -1 ∨ sign = 1) : IsEmbedding (bandSidePatch t ht0 ht1 sign hsign) := by
  have hc : Continuous (bandSidePatch t ht0 ht1 sign hsign) := by
    unfold bandSidePatch
    fun_prop
  apply (hc.isClosedEmbedding ?_).isEmbedding
  intro p q he
  have hx := congrArg (fun z : I × BandWidth => (z.1 : ℝ)) he
  have hy := congrArg (fun z : I × BandWidth => (z.2 : ℝ)) he
  dsimp [bandSidePatch] at hx hy
  have hdpos : 0 < min (t : ℝ) (1 - (t : ℝ)) / 2 :=
    div_pos (lt_min ht0 (by linarith)) (by norm_num)
  apply Prod.ext <;> apply Subtype.ext
  · nlinarith
  · rcases hsign with hsign | hsign <;> rw [hsign] at hy <;> linarith

theorem bandSidePatch_parameter_bounds
    (t : I) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (sign : ℝ) (hsign : sign = -1 ∨ sign = 1) (p : BandWidth × I) :
    0 < ((bandSidePatch t ht0 ht1 sign hsign p).1 : ℝ) ∧
    ((bandSidePatch t ht0 ht1 sign hsign p).1 : ℝ) < 1 := by
  dsimp [bandSidePatch]
  have hdpos : 0 < min (t : ℝ) (1 - (t : ℝ)) / 2 :=
    div_pos (lt_min ht0 (by linarith)) (by norm_num)
  have hd0 : min (t : ℝ) (1 - (t : ℝ)) / 2 ≤ (t : ℝ)/2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hd1 : min (t : ℝ) (1 - (t : ℝ)) / 2 ≤ (1 - (t : ℝ))/2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  constructor <;> nlinarith [p.1.property.1, p.1.property.2]

/-- The same-witness cap fills every interior point of either actual lateral band side. -/
theorem actual_band_first_lateral_cap_interior
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    {c : Curve S} (hfront : frontier (bandUnion D B) = c.image)
    (f : C(CapDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' capBoundary = c.image)
    (houtside : f '' capInterior ⊆ interior (bandUnion D B)ᶜ)
    (t : I) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (u : BandWidth) (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B.first (t, u) ∈ interior (bandUnion D B ∪ Set.range f) := by
  let L := B.first ∘ bandSidePatch t ht0 ht1 u hu
  have hL : IsEmbedding L := B.first_embedded.comp (bandSidePatch_embedded t ht0 ht1 u hu)
  have hLN : Set.range L ⊆ bandUnion D B := by
    rintro x ⟨p, rfl⟩
    exact Or.inl (Or.inr (Set.mem_range_self _))
  have hLfront (p : BandWidth × I) : L p ∈ c.image ↔ p.2 = 0 := by
    constructor
    · intro hp
      have hpfront : L p ∈ frontier (bandUnion D B) := hfront.symm ▸ hp
      by_contra hn
      have hp2pos : 0 < (p.2 : ℝ) := lt_of_le_of_ne p.2.property.1
        (by intro he; exact hn (Subtype.ext he.symm))
      have hbounds := bandSidePatch_parameter_bounds t ht0 ht1 u hu p
      have hu0 : -1 < ((bandSidePatch t ht0 ht1 u hu p).2 : ℝ) := by
        dsimp [bandSidePatch]
        rcases hu with hu | hu <;> rw [hu] <;> linarith [p.2.property.2]
      have hu1 : ((bandSidePatch t ht0 ht1 u hu p).2 : ℝ) < 1 := by
        dsimp [bandSidePatch]
        rcases hu with hu | hu <;> rw [hu] <;> linarith [p.2.property.2]
      have hi := embedded_band_open_rectangle_interior B.first B.first_embedded
        _ _ hbounds.1 hbounds.2 hu0 hu1
      exact hpfront.2 (interior_mono (fun x hx => Or.inl (Or.inr hx)) hi)
    · intro hp0
      apply hfront ▸ (compatibleOutsideBands_first_lateral_frontier_all D B _ _ ?_)
      dsimp [bandSidePatch]
      simpa [hp0] using hu
  have hi := embedded_half_rectangle_cap_seam (bandUnion D B)
    (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed c hfront
    f hf hboundary houtside L hL hLN hLfront ⟨0, by norm_num⟩ (by norm_num) (by norm_num)
  have heq : L (⟨0, by norm_num⟩, 0) = B.first (t, u) := by
    change B.first (bandSidePatch t ht0 ht1 u hu (⟨0, by norm_num⟩, 0)) = B.first (t, u)
    congr 1
    apply Prod.ext <;> apply Subtype.ext <;> simp [L, bandSidePatch]
  rwa [heq] at hi

/-- The same-witness cap fills every interior point of either actual lateral band side. -/
theorem actual_band_second_lateral_cap_interior
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    {c : Curve S} (hfront : frontier (bandUnion D B) = c.image)
    (f : C(CapDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' capBoundary = c.image)
    (houtside : f '' capInterior ⊆ interior (bandUnion D B)ᶜ)
    (t : I) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1)
    (u : BandWidth) (hu : (u : ℝ) = -1 ∨ (u : ℝ) = 1) :
    B.second (t, u) ∈ interior (bandUnion D B ∪ Set.range f) := by
  let L := B.second ∘ bandSidePatch t ht0 ht1 u hu
  have hL : IsEmbedding L := B.second_embedded.comp (bandSidePatch_embedded t ht0 ht1 u hu)
  have hLN : Set.range L ⊆ bandUnion D B := by
    rintro x ⟨p, rfl⟩
    exact Or.inr (Set.mem_range_self _)
  have hLfront (p : BandWidth × I) : L p ∈ c.image ↔ p.2 = 0 := by
    constructor
    · intro hp
      have hpfront : L p ∈ frontier (bandUnion D B) := hfront.symm ▸ hp
      by_contra hn
      have hp2pos : 0 < (p.2 : ℝ) := lt_of_le_of_ne p.2.property.1
        (by intro he; exact hn (Subtype.ext he.symm))
      have hbounds := bandSidePatch_parameter_bounds t ht0 ht1 u hu p
      have hu0 : -1 < ((bandSidePatch t ht0 ht1 u hu p).2 : ℝ) := by
        dsimp [bandSidePatch]
        rcases hu with hu | hu <;> rw [hu] <;> linarith [p.2.property.2]
      have hu1 : ((bandSidePatch t ht0 ht1 u hu p).2 : ℝ) < 1 := by
        dsimp [bandSidePatch]
        rcases hu with hu | hu <;> rw [hu] <;> linarith [p.2.property.2]
      have hi := embedded_band_open_rectangle_interior B.second B.second_embedded
        _ _ hbounds.1 hbounds.2 hu0 hu1
      exact hpfront.2 (interior_mono (fun x hx => Or.inr hx) hi)
    · intro hp0
      apply hfront ▸ (compatibleOutsideBands_second_lateral_frontier_all D B _ _ ?_)
      dsimp [bandSidePatch]
      simpa [hp0] using hu
  have hi := embedded_half_rectangle_cap_seam (bandUnion D B)
    (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed c hfront
    f hf hboundary houtside L hL hLN hLfront ⟨0, by norm_num⟩ (by norm_num) (by norm_num)
  have heq : L (⟨0, by norm_num⟩, 0) = B.second (t, u) := by
    change B.second (bandSidePatch t ht0 ht1 u hu (⟨0, by norm_num⟩, 0)) = B.second (t, u)
    congr 1
    apply Prod.ext <;> apply Subtype.ext <;> simp [L, bandSidePatch]
  rwa [heq] at hi

#print axioms actual_band_first_lateral_cap_interior
end CurveComplex.CapBandGeometry
