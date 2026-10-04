import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.LocalSquareLiftProof
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchMetricBaseDevelopmentCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactConeSquareBranchChart
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchDeckCoordinates

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem actual_branch_contractive_development (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∈ q.ramification) (i : Fin 6)
    (hposition : identify (q.projection x) = Metric.toGlueL
      (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)
      ⟨regularHexagonCandidate.vertex i,
        hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩) :
    ∃ e : OpenPartialHomeomorph E H2, ∃ d : OpenPartialHomeomorph S HalfTurnMetricCone,
      x ∈ e.source ∧ e x = normalizedConeVertex ∧
      (∀ y ∈ e.source, q.projection y ∈ d.source ∧
        d (q.projection y) = toHalfTurnMetricCone (e y)) ∧
      (∀ y ∈ e.source, q.deck y ∈ e.source ∧
        e (q.deck y) = vertexHalfTurnEquiv (e y)) ∧
      (∀ y ∈ e.source, y ≠ x → ∃ V : Set E, IsOpen V ∧ y ∈ V ∧ V ⊆ e.source ∧
        ∀ z ∈ V, ∀ w ∈ V,
          dist (e z) (e w) = dist (identify (q.projection z)) (identify (q.projection w))) ∧
      (∀ y ∈ e.source, ∀ z ∈ e.source,
        dist (identify (q.projection y)) (identify (q.projection z)) ≤ dist (e y) (e z)) := by
  classical
  obtain ⟨d, hd, p, hp, hi, hcenter, r, hr, htarget, hmetric⟩ :=
    actual_branch_metric_base_development q identify x hx i hposition
  obtain ⟨c, U, hU, hxU, hUc, hstable, hram, hdeck⟩ :=
    q.actual_branch_deck_coordinate_neighborhood x hx
  letI : Nonempty HalfTurnMetricCone := ⟨toHalfTurnMetricCone normalizedConeVertex⟩
  let k := coneSquareCoordinate_isOpenEmbedding.toOpenPartialHomeomorph coneSquareCoordinate
  let h := c.downstairs.symm.trans (d.trans k)
  have hpv : p = normalizedConeVertex := by
    apply UpperHalfPlane.ext_re_im
    · exact hp
    · exact hi
  have h0inv : c.downstairs.symm (0 : ℂ) = q.projection x := by
    rw [← c.downstairs_center]
    exact c.downstairs.left_inv c.downstairs_mem
  have hzeroSource : (0 : ℂ) ∈ h.source := by
    change (0 : ℂ) ∈ c.downstairs.target ∩ c.downstairs.symm ⁻¹' (d.trans k).source
    refine ⟨?_, ?_⟩
    · rw [← c.downstairs_center]
      exact c.downstairs.map_source c.downstairs_mem
    · rw [Set.mem_preimage, h0inv]
      exact ⟨hd, by simp [k]⟩
  have hzero : h 0 = 0 := by
    change coneSquareCoordinate (d (c.downstairs.symm 0)) = 0
    rw [h0inv, hcenter, hpv, coneSquareCoordinate_projection,
      normalizedConeVertex_cayley, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have hct : (0 : ℂ) ∈ c.upstairs.target := by
    rw [← c.upstairs_center]
    exact c.upstairs.map_source c.upstairs_mem
  obtain ⟨g, hgs, hg0, hgc, hgv, hsq, hneg⟩ :=
    local_plane_homeomorphism_square_lift_in_neighborhoods h hzeroSource hzero
      c.upstairs.target (Metric.ball (0 : ℂ) 1) c.upstairs.open_target Metric.isOpen_ball
      hct (Metric.mem_ball_self (by norm_num))
  let f : H2 → ℂ := fun z => (cayley z : ℂ)
  have hf : IsOpenEmbedding f :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp cayleyHomeomorph.isOpenEmbedding
  let a := hf.toOpenPartialHomeomorph f
  have has : a.source = Set.univ := by simp [a]
  have hat : a.target = Metric.ball (0 : ℂ) 1 := by
    rw [show a.target = Set.range f from hf.toOpenPartialHomeomorph_target f]
    change Set.range f = _
    change Set.range (Subtype.val ∘ cayleyHomeomorph) = _
    rw [Set.range_comp, cayleyHomeomorph.surjective.range_eq, Set.image_univ,
      Subtype.range_coe_subtype]
    rfl
  let e0 := c.upstairs.trans (g.trans a.symm)
  let e := e0.restrOpen U hU
  have hsource (y : E) : y ∈ e.source ↔ y ∈ U ∧ c.upstairs y ∈ g.source := by
    change (y ∈ c.upstairs.source ∧ c.upstairs y ∈ g.source ∧
      g (c.upstairs y) ∈ a.target) ∧ y ∈ U ↔ _
    constructor
    · intro hy
      exact ⟨hy.2, hy.1.2.1⟩
    · intro hy
      exact ⟨⟨hUc hy.1, hy.2, hat.symm ▸ hgv (g.map_source hy.2)⟩, hy.1⟩
  have hvalue (y : E) : e y = a.symm (g (c.upstairs y)) := rfl
  have hcayley (y : E) (hy : y ∈ e.source) :
      (cayley (e y) : ℂ) = g (c.upstairs y) := by
    have ht : g (c.upstairs y) ∈ a.target :=
      hat.symm ▸ hgv (g.map_source ((hsource y).mp hy).2)
    exact a.right_inv ht
  have hxe : x ∈ e.source := (hsource x).mpr ⟨hxU, by simpa [c.upstairs_center] using hgs⟩
  have hecenter : e x = normalizedConeVertex := by
    apply cayley_injective
    apply Subtype.ext
    rw [hcayley x hxe, c.upstairs_center, hg0, normalizedConeVertex_cayley]
  have heproj (y : E) (hy : y ∈ e.source) :
      q.projection y ∈ d.source ∧ d (q.projection y) = toHalfTurnMetricCone (e y) := by
    obtain ⟨hyU, hyg⟩ := (hsource y).mp hy
    have hyc := hUc hyU
    have hinv : c.downstairs.symm ((c.upstairs y) ^ 2) = q.projection y := by
      rw [← c.square y hyc]
      exact c.downstairs.left_inv (c.image_mem y hyc)
    have hhs := (hsq _ hyg).1
    have hyd : q.projection y ∈ d.source := by
      change (c.upstairs y) ^ 2 ∈ c.downstairs.target ∩
        c.downstairs.symm ⁻¹' (d.trans k).source at hhs
      have hh := hhs.2.1
      change c.downstairs.symm ((c.upstairs y) ^ 2) ∈ d.source at hh
      rwa [hinv] at hh
    refine ⟨hyd, ?_⟩
    apply coneSquareCoordinate_injective
    rw [coneSquareCoordinate_projection, hcayley y hy, (hsq _ hyg).2]
    change coneSquareCoordinate (d (q.projection y)) =
      coneSquareCoordinate (d (c.downstairs.symm ((c.upstairs y) ^ 2)))
    rw [hinv]
  refine ⟨e, d, hxe, hecenter, heproj, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hyU, hyg⟩ := (hsource y).mp hy
    have hdy : q.deck y ∈ e.source := (hsource _).mpr
      ⟨hstable _ hyU, by rw [hdeck _ hyU]; exact (hneg _ hyg).1⟩
    refine ⟨hdy, ?_⟩
    apply cayley_injective
    apply Subtype.ext
    rw [hcayley _ hdy, cayley_halfTurn, hcayley _ hy, hdeck _ hyU]
    exact (hneg _ hyg).2

  · intro y hy hne
    have hfixed : vertexHalfTurnEquiv (e y) ≠ e y := by
      intro hfix
      obtain ⟨hre, him⟩ := vertexHalfTurn_fixed_iff (e y) |>.mp hfix
      have hev : e y = normalizedConeVertex := UpperHalfPlane.ext_re_im hre him
      exact hne (e.injOn hy hxe (hev.trans hecenter.symm))
    let t := dist (e y) (vertexHalfTurnEquiv (e y)) / 4
    have ht : 0 < t := div_pos (dist_pos.mpr (Ne.symm hfixed)) (by norm_num)
    let V := e.source ∩ e ⁻¹' Metric.ball (e y) t
    have hV : IsOpen V := e.isOpen_inter_preimage Metric.isOpen_ball
    have hyV : y ∈ V := ⟨hy, Metric.mem_ball_self ht⟩
    refine ⟨V, hV, hyV, Set.inter_subset_left, ?_⟩
    intro z hz w hw
    have hzi := halfTurnMetricCone_isometry_on_small_ball (e y) hfixed
    have heq := hzi.dist_eq ⟨e z, hz.2⟩ ⟨e w, hw.2⟩
    calc
      dist (e z) (e w) = dist (toHalfTurnMetricCone (e z)) (toHalfTurnMetricCone (e w)) := heq.symm
      _ = dist (d (q.projection z)) (d (q.projection w)) := by
        rw [(heproj z hz.1).2, (heproj w hw.1).2]
      _ = dist (identify (q.projection z)) (identify (q.projection w)) :=
        hmetric _ (heproj z hz.1).1 _ (heproj w hw.1).1

  · intro y hy z hz
    rw [← hmetric _ (heproj y hy).1 _ (heproj z hz).1,
      (heproj y hy).2, (heproj z hz).2]
    exact halfTurnMetricCone_projection_distance_le (e y) (e z)

end CurveComplex.Hyperbolic
