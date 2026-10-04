import CurveComplexGenusTwo.Octagon.VertexChartGlueWave11

set_option maxHeartbeats 1000000
namespace CurveComplex.Octagon

theorem quarter_radial_eq {k l : Fin 8} {p q : quarterParams}
    (h : radialSector (vertexCycle k) p.1.1 p.1.2 =
      radialSector (vertexCycle l) q.1.1 q.1.2) : k = l ∧ p = q := by
  obtain ⟨hr, ht0, ht1⟩ := quarterParams_bounds p
  obtain ⟨_, hu0, hu1⟩ := quarterParams_bounds q
  obtain ⟨hi, hr, ht⟩ := radialSector_eq_of_quarter_bounds _ _ _ _ _ _
    hr ht0 ht1 hu0 hu1 h
  exact ⟨vertexCycle_bijective.1 hi, Subtype.ext (Prod.ext hr ht)⟩

theorem quarter_seam_fiber_plane (k : Fin 8) (s : unitInterval)
    (hs : s ≠ 0) (hsb : (s : ℝ) ≤ 1 / 2) (q : vertexModel)
    (h : vertexModelSource q =
      mk (radialSector (vertexCycle k) 0 (outgoingHalf s))) :
    vertexModelPlane q = sectorUnfoldPoint k 0 (outgoingHalf s) := by
  have hmem : radialSector (vertexCycle q.1) q.2.1.1 q.2.1.2 ∈
      mk ⁻¹' ({mk (radialSector (vertexCycle k) 0 (outgoingHalf s))} : Set Surface) := h
  rw [radialSector_seam_exact_fiber k s hs] at hmem
  obtain ⟨hrb, htl, htu⟩ := quarterParams_bounds q.2
  have ho0 : (1 : ℝ) / 4 ≤ outgoingHalf s := by dsimp [outgoingHalf]; linarith [s.property.1]
  have ho1 : (outgoingHalf s : ℝ) ≤ 3 / 4 := by dsimp [outgoingHalf]; linarith
  have hi0 : (1 : ℝ) / 4 ≤ incomingHalf s := by dsimp [incomingHalf]; linarith
  have hi1 : (incomingHalf s : ℝ) ≤ 3 / 4 := by dsimp [incomingHalf]; linarith [s.property.1]
  rcases Set.mem_insert_iff.mp hmem with he | he
  · obtain ⟨hk, hr, ht⟩ := radialSector_eq_of_quarter_bounds _ _ _ _ _ _ hrb htl htu ho0 ho1 he
    have hk := vertexCycle_bijective.1 hk
    simp only [vertexModelPlane, hk, hr, ht]
  · have he := Set.mem_singleton_iff.mp he
    obtain ⟨hk, hr, ht⟩ := radialSector_eq_of_quarter_bounds _ _ _ _ _ _ hrb htl htu hi0 hi1 he
    have hk := vertexCycle_bijective.1 hk
    simp only [vertexModelPlane, hk, hr, ht]
    exact (sectorUnfoldPoint_seam_all k s).symm

theorem vertexModel_source_implies_plane (p q : vertexModel)
    (h : vertexModelSource p = vertexModelSource q) :
    vertexModelPlane p = vertexModelPlane q := by
  by_cases hv : vertexModelSource p = mk (vertexPoint 0)
  · have hp := (vertexModel_vertex_iff_plane_zero p).mp hv
    have hq := (vertexModel_vertex_iff_plane_zero q).mp (h.symm.trans hv)
    exact hp.trans hq.symm
  by_cases hr : p.2.1.1 = 0
  · obtain ⟨_, ht0, ht1⟩ := quarterParams_bounds p.2
    by_cases ht : (1 : ℝ) / 2 ≤ p.2.1.2
    · let s : unitInterval := ⟨2 * (p.2.1.2 : ℝ) - 1, by constructor <;> linarith⟩
      have hsb : (s : ℝ) ≤ 1 / 2 := by dsimp [s]; linarith
      have hpt : p.2.1.2 = outgoingHalf s := by apply Subtype.ext; dsimp [outgoingHalf, s]; ring
      have hs : s ≠ 0 := by
        intro hs
        apply hv
        simp only [vertexModelSource, hr, hpt, hs]
        simpa [outgoingHalf] using radialSector_center_quotient (vertexCycle p.1)
      have hq := quarter_seam_fiber_plane p.1 s hs hsb q (by simpa [vertexModelSource, hr, hpt] using h.symm)
      simpa only [vertexModelPlane, hr, hpt] using hq.symm
    · let s : unitInterval := ⟨1 - 2 * (p.2.1.2 : ℝ), by constructor <;> linarith⟩
      have hsb : (s : ℝ) ≤ 1 / 2 := by dsimp [s]; linarith
      have hpt : p.2.1.2 = incomingHalf s := by apply Subtype.ext; dsimp [incomingHalf, s]; ring
      have hs : s ≠ 0 := by
        intro hs
        have hh := congrArg (fun x : unitInterval => (x : ℝ)) hs
        dsimp [s] at hh
        change 1 - 2 * (p.2.1.2 : ℝ) = 0 at hh
        linarith
      obtain ⟨k, hk⟩ := (show ∀ l : Fin 8, ∃ k : Fin 8, next k = l by decide) p.1
      have hq := quarter_seam_fiber_plane k s hs hsb q (by
        calc
          vertexModelSource q = vertexModelSource p := h.symm
          _ = mk (radialSector (vertexCycle (next k)) 0 (incomingHalf s)) := by simp [vertexModelSource, hk, hr, hpt]
          _ = mk (radialSector (vertexCycle k) 0 (outgoingHalf s)) := (radialSector_seam_quotient k s).symm)
      calc
        vertexModelPlane p = sectorUnfoldPoint (next k) 0 (incomingHalf s) := by simp [vertexModelPlane, hk, hr, hpt]
        _ = sectorUnfoldPoint k 0 (outgoingHalf s) := (sectorUnfoldPoint_seam_all k s).symm
        _ = vertexModelPlane q := hq.symm
  · have he := mem_diskInterior_of_mk_eq_mk
      (radialSector_interior_norm (vertexCycle p.1) p.2.1.1 p.2.1.2 hr) h
    obtain ⟨hk, hp⟩ := quarter_radial_eq he
    have : p = q := Prod.ext hk hp
    rw [this]

end CurveComplex.Octagon
