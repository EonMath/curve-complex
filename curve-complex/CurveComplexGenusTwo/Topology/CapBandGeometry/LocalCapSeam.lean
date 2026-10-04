import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
import CurveComplexGenusTwo.Topology.FrontierCircle.SeamGluingProbe
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapBandPacket

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

abbrev CapPlane := EuclideanSpace ℝ (Fin 2)
abbrev CapDisk := Metric.closedBall (0 : CapPlane) 1

def capInterior : Set CapDisk := {x | (x : CapPlane) ∈ Metric.ball 0 1}
def capBoundary : Set CapDisk := {x | (x : CapPlane) ∈ Metric.sphere 0 1}

/-- A nondegenerate inward radial strip along a literal embedded sphere arc. -/
noncomputable def diskRadialStrip (v : BandWidth → CapDisk)
    (hv : ∀ t, ‖(v t : CapPlane)‖ = 1) : BandWidth × I → CapDisk :=
  fun p => ⟨(1 - (p.2 : ℝ)/2) • (v p.1 : CapPlane), by
    change dist ((1 - (p.2 : ℝ)/2) • (v p.1 : CapPlane)) 0 ≤ 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, hv p.1, mul_one,
      abs_of_pos (by linarith [p.2.property.2] : 0 < 1 - (p.2 : ℝ)/2)]
    linarith [p.2.property.1]⟩

@[simp]
theorem diskRadialStrip_zero (v : BandWidth → CapDisk)
    (hv : ∀ t, ‖(v t : CapPlane)‖ = 1) (t : BandWidth) :
    diskRadialStrip v hv (t, 0) = v t := by
  apply Subtype.ext
  simp [diskRadialStrip]

theorem diskRadialStrip_embedded (v : BandWidth → CapDisk)
    (hv : ∀ t, ‖(v t : CapPlane)‖ = 1) (hvc : Continuous v)
    (hvi : Function.Injective v) : IsEmbedding (diskRadialStrip v hv) := by
  have hc : Continuous (diskRadialStrip v hv) := by
    unfold diskRadialStrip
    fun_prop
  apply (hc.isClosedEmbedding ?_).isEmbedding
  intro p q hpq
  have hpq' := congrArg Subtype.val hpq
  have hn := congrArg norm hpq'
  have hpn : 0 < 1 - (p.2 : ℝ)/2 := by linarith [p.2.property.2]
  have hqn : 0 < 1 - (q.2 : ℝ)/2 := by linarith [q.2.property.2]
  simp only [diskRadialStrip, norm_smul, Real.norm_eq_abs, hv, mul_one,
    abs_of_pos hpn, abs_of_pos hqn] at hn
  have hsecond : p.2 = q.2 := Subtype.ext (by linarith)
  have hfirst : p.1 = q.1 := by
    apply hvi
    apply Subtype.ext
    have hcneq : (1 - (p.2 : ℝ)/2) ≠ 0 := hpn.ne'
    have he : (1 - (p.2 : ℝ)/2) • (v p.1 : CapPlane) =
        (1 - (p.2 : ℝ)/2) • (v q.1 : CapPlane) := by
      simpa only [diskRadialStrip, ← hsecond] using hpq'
    exact (smul_right_injective CapPlane hcneq) he
  exact Prod.ext hfirst hsecond

theorem diskRadialStrip_boundary_iff (v : BandWidth → CapDisk)
    (hv : ∀ t, ‖(v t : CapPlane)‖ = 1) (p : BandWidth × I) :
    diskRadialStrip v hv p ∈ capBoundary ↔ p.2 = 0 := by
  have hpos : 0 < 1 - (p.2 : ℝ)/2 := by linarith [p.2.property.2]
  change dist ((1 - (p.2 : ℝ)/2) • (v p.1 : CapPlane)) 0 = 1 ↔ p.2 = 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_pos hpos]
  constructor
  · intro h
    exact Subtype.ext (by change (p.2 : ℝ) = 0; linarith)
  · intro h
    simp [h]

/-- A genuine band-side half rectangle and the SAME exterior cap form an
ambient neighborhood. The half rectangle is a geometric intermediate to
be constructed from D/B, not a new premise of the source-facing producer. -/
theorem embedded_half_rectangle_cap_seam
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    (N : Set S) (hNclosed : IsClosed N) (c : Curve S)
    (hfront : frontier N = c.image)
    (f : C(CapDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' capBoundary = c.image)
    (houtside : f '' capInterior ⊆ interior Nᶜ)
    (L : BandWidth × I → S) (hL : IsEmbedding L)
    (hLN : Set.range L ⊆ N)
    (hLfront : ∀ p : BandWidth × I, L p ∈ c.image ↔ p.2 = 0)
    (t : BandWidth) (ht0 : (-1 : ℝ) < t) (ht1 : (t : ℝ) < 1) :
    L (t, 0) ∈ interior (N ∪ Set.range f) := by
  let v : BandWidth → CapDisk := fun u => hf.toHomeomorph.symm
    ⟨L (u, 0), by
      have hcu := (hLfront (u, 0)).mpr rfl
      obtain ⟨z, hz, he⟩ := hboundary.symm ▸ hcu
      exact ⟨z, he⟩⟩
  have hvimage (u : BandWidth) : f (v u) = L (u, 0) := by
    exact congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply _)
  have hvnorm (u : BandWidth) : ‖(v u : CapPlane)‖ = 1 := by
    have hcu := (hLfront (u, 0)).mpr rfl
    obtain ⟨z, hz, he⟩ := hboundary.symm ▸ hcu
    have hvz : v u = z := hf.injective ((hvimage u).trans he.symm)
    rw [hvz]
    simpa [capBoundary, dist_zero_right] using hz
  have hvc : Continuous v := by
    exact hf.toHomeomorph.symm.continuous.comp
      ((hL.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _)
  have hvi : Function.Injective v := by
    intro u w he
    have h : L (u, 0) = L (w, 0) := (hvimage u).symm.trans
      ((congrArg f he).trans (hvimage w))
    exact congrArg Prod.fst (hL.injective h)
  let R : BandWidth × I → S := f ∘ diskRadialStrip v hvnorm
  have hR : IsEmbedding R := hf.comp (diskRadialStrip_embedded v hvnorm hvc hvi)
  have hseam (u : BandWidth) : L (u, 0) = R (u, 0) := by
    simp only [R, Function.comp_apply, diskRadialStrip_zero, hvimage]
  have hmeet : Set.range L ∩ Set.range R = Set.range (fun u => L (u, 0)) := by
    ext x
    constructor
    · rintro ⟨⟨p, rfl⟩, q, he⟩
      have hxN : L p ∈ N := hLN (Set.mem_range_self p)
      have hxrange : L p ∈ Set.range f := ⟨diskRadialStrip v hvnorm q, he⟩
      have hxboundary : L p ∈ c.image := by
        exact (exterior_disk_meets_closed_neighborhood_at_frontier N hNclosed c
          hfront f hboundary houtside) ▸ ⟨hxN, hxrange⟩
      have hp0 : p.2 = 0 := (hLfront p).mp hxboundary
      refine ⟨p.1, ?_⟩
      exact congrArg L (Prod.ext rfl hp0.symm)
    · rintro ⟨u, rfl⟩
      exact ⟨Set.mem_range_self _, ⟨(u, 0), (hseam u).symm⟩⟩
  have hsub : Set.range L ∪ Set.range R ⊆ N ∪ Set.range f := by
    apply Set.union_subset_union hLN
    rintro x ⟨p, rfl⟩
    exact Set.mem_range_self _
  exact interior_mono hsub (glued_half_rectangles_seam_interior_probe L R
    hL hR hseam hmeet t ht0 ht1)

#print axioms diskRadialStrip_embedded
#print axioms embedded_half_rectangle_cap_seam
end CurveComplex.CapBandGeometry
