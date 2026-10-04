import CurveComplexGenusTwo.Topology.ThetaRetention.PlanarRectangleSides
import CurveComplexGenusTwo.Topology.FrontierCircle.BandStraightening
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe

namespace CurveComplex
open Set Topology Schoenflies

/-- The ordinary interior of an embedded rectangle supplies local two sides
when the actual deleted set meets that rectangle exactly in its center. -/
theorem source_embedded_rectangle_local_sides
    {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    {l r b t : ℝ} (hlr : l < r) (hb : b < 0) (ht : 0 < t)
    (B : Icc l r × Icc b t → S) (hB : IsEmbedding B)
    (D P : Set S) (hBD : Set.range B ⊆ D)
    (hBP : ∀ z, B z ∈ P ↔ (z.2:ℝ) = 0) :
    ∃ C : SurfaceLocalSides D P,
      ∀ s : Icc l r, l < (s:ℝ) → (s:ℝ) < r →
        B (s,⟨0,⟨hb.le,ht.le⟩⟩) ∈ C.nbhd := by
  let q : Plane → Icc l r × Icc b t := fun z =>
    (Set.projIcc l r hlr.le (z 0),Set.projIcc b t (hb.le.trans ht.le) (z 1))
  let F : Plane → S := B ∘ q
  have hFc : Continuous F := hB.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop)))
  have hqval (z : Plane) (hz : z ∈ thetaRect l r b t) :
      ((q z).1:ℝ) = z 0 ∧ ((q z).2:ℝ) = z 1 := by
    exact ⟨by simp [q,Set.projIcc_of_mem hlr.le ⟨hz.1.le,hz.2.1.le⟩],
      by simp [q,Set.projIcc_of_mem (hb.le.trans ht.le) ⟨hz.2.2.1.le,hz.2.2.2.le⟩]⟩
  have hFi : InjOn F (thetaRect l r b t) := by
    intro z hz w hw he
    have heq := hB.injective he
    have h0 := congrArg (fun z : Icc l r × Icc b t => (z.1:ℝ)) heq
    have h1 := congrArg (fun z : Icc l r × Icc b t => (z.2:ℝ)) heq
    rw [(hqval z hz).1,(hqval w hw).1] at h0
    rw [(hqval z hz).2,(hqval w hw).2] at h1
    ext i
    fin_cases i <;> assumption
  have hFP (z : Plane) (hz : z ∈ thetaRect l r b t) : F z ∈ P ↔ z 1 = 0 := by
    change B (q z) ∈ P ↔ _
    rw [hBP,(hqval z hz).2]
  obtain ⟨A,hA⟩ := thetaRect_local_sides hlr hb ht
  let C : SurfaceLocalSides D P := {
    nbhd := F '' A.nbhd
    left := F '' A.left
    right := F '' A.right
    isOpen_nbhd := by rw [hA]; exact surface_invariance_of_domain_probe F _ (thetaRect_open _ _ _ _) hFc.continuousOn hFi
    nbhd_subset := by rintro x ⟨z,hz,rfl⟩; exact hBD (Set.mem_range_self (q z))
    nbhd_diff := by
      ext x
      constructor
      · rintro ⟨⟨z,hz,rfl⟩,hn⟩
        have hzP : z ∉ {z : Plane | z 1 = 0} := by
          intro he
          exact hn ((hFP z (hA ▸ hz)).mpr he)
        have hh : z ∈ A.left ∪ A.right := A.nbhd_diff ▸ ⟨hz,hzP⟩
        exact hh.elim (fun h => Or.inl ⟨z,h,rfl⟩) (fun h => Or.inr ⟨z,h,rfl⟩)
      · rintro (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩)
        · have hzN : z ∈ A.nbhd \ {z : Plane | z 1 = 0} := by rw [A.nbhd_diff]; exact Or.inl hz
          exact ⟨⟨z,hzN.1,rfl⟩,fun hp => hzN.2 ((hFP z (hA ▸ hzN.1)).mp hp)⟩
        · have hzN : z ∈ A.nbhd \ {z : Plane | z 1 = 0} := by rw [A.nbhd_diff]; exact Or.inr hz
          exact ⟨⟨z,hzN.1,rfl⟩,fun hp => hzN.2 ((hFP z (hA ▸ hzN.1)).mp hp)⟩
    connected_left := A.connected_left.image F hFc.continuousOn
    connected_right := A.connected_right.image F hFc.continuousOn
    limit_left := by
      rintro x ⟨⟨z,hz,rfl⟩,hp⟩
      exact hFc.continuousWithinAt.mem_closure_image (A.limit_left ⟨hz,(hFP z (hA ▸ hz)).mp hp⟩)
    limit_right := by
      rintro x ⟨⟨z,hz,rfl⟩,hp⟩
      exact hFc.continuousWithinAt.mem_closure_image (A.limit_right ⟨hz,(hFP z (hA ▸ hz)).mp hp⟩) }
  refine ⟨C,?_⟩
  intro s hsl hsr
  refine ⟨Plane.mk s 0,?_,?_⟩
  · rw [hA]
    exact ⟨hsl,hsr,hb,ht⟩
  · change F (Plane.mk s 0) = B _
    change B (q (Plane.mk s 0)) = B _
    apply congrArg B
    apply Prod.ext <;> apply Subtype.ext
    · simp [q,Plane.mk,Set.projIcc_of_mem hlr.le s.property]
    · simp [q,Plane.mk,Set.projIcc_of_mem (hb.le.trans ht.le) ⟨hb.le,ht.le⟩]

/-- Actual local collars on an arbitrary embedded surface interval. This uses
only the already-proved local rectangular-band producer; the center and its
avoidance of the whole original arc are exact. -/
theorem source_embedded_path_internal_local_sides
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m : unitInterval) (hm0 : 0 < m) (hm1 : m < 1)
    (D : Set S) (hD : IsOpen D) (hmD : p m ∈ D) :
    ∃ C : SurfaceLocalSides D (Set.range p), p m ∈ C.nbhd := by
  obtain ⟨η,hη,hlo,hhi,δ,hδ,B,hB,hBD,hcenter,hmeet⟩ :=
    exists_local_rectangular_band_on_surface p hp m hm0 hm1 D hD hmD
  have hBP (z : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ) :
      B z ∈ Set.range p ↔ (z.2:ℝ) = 0 := by
    constructor
    · intro hz
      have hm : B z ∈ Set.range B ∩ Set.range p := ⟨Set.mem_range_self z,hz⟩
      rw [hmeet] at hm
      obtain ⟨w,hw⟩ := hm
      have he : B (w,⟨0,by constructor <;> linarith⟩) = B z := (hcenter w).trans hw
      have heq := hB.injective he
      exact (congrArg (fun v : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ => (v.2:ℝ)) heq).symm
    · intro hz
      have heq : z = (z.1,⟨0,by constructor <;> linarith⟩) := by
        exact Prod.ext rfl (Subtype.ext hz)
      rw [heq,hcenter]
      rw [← p.extend_range]
      exact Set.mem_range_self _
  obtain ⟨C,hCn⟩ := source_embedded_rectangle_local_sides
    (show (1/3:ℝ) < 2/3 by norm_num) (show -δ < 0 by linarith) hδ B hB D (Set.range p) hBD hBP
  refine ⟨C,?_⟩
  have hmid := hCn ⟨1/2,by constructor <;> norm_num⟩ (by norm_num) (by norm_num)
  rw [hcenter] at hmid
  have he : (m:ℝ)-η+2*η*((⟨1/2,by constructor <;> norm_num⟩ : Icc (1/3:ℝ) (2/3)):ℝ) = m := by
    dsimp; ring
  rw [he,p.extend_extends' m] at hmid
  exact hmid

end CurveComplex
#print axioms CurveComplex.source_embedded_path_internal_local_sides
