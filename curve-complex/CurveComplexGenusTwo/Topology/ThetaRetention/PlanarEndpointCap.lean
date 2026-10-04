import CurveComplexGenusTwo.Topology.ThetaRetention.PlanarRectangleSides

namespace CurveComplex
open Set Topology Schoenflies

/-- A rectangle with a vertical slit ending at an interior point is connected.
Its two side strips meet the strip beyond the endpoint. -/
theorem thetaRect_endpoint_slit_connected
    {l r b t c d : ℝ} (hlc : l < c) (hcr : c < r) (hbd : b < d) (hdt : d < t) :
    IsConnected (thetaRect l r b t \ {z : Plane | z 0 = c ∧ z 1 ≤ d}) := by
  have heq : thetaRect l r b t \ {z : Plane | z 0 = c ∧ z 1 ≤ d} =
      (thetaRect l c b t ∪ thetaRect l r d t) ∪ thetaRect c r b t := by
    ext z
    simp only [thetaRect,Set.mem_sdiff,Set.mem_ofPred_eq,Set.mem_union]
    constructor
    · rintro ⟨⟨h0l,h0r,h1b,h1t⟩,hn⟩
      rcases lt_trichotomy (z 0) c with h | h | h
      · exact Or.inl (Or.inl ⟨h0l,h,h1b,h1t⟩)
      · have hd : d < z 1 := lt_of_not_ge (fun he => hn ⟨h,he⟩)
        exact Or.inl (Or.inr ⟨h0l,h0r,hd,h1t⟩)
      · exact Or.inr ⟨h,h0r,h1b,h1t⟩
    · rintro ((hz | hz) | hz)
      · exact ⟨⟨hz.1,hz.2.1.trans hcr,hz.2.2⟩,fun he => (ne_of_lt hz.2.1) he.1⟩
      · exact ⟨⟨hz.1,hz.2.1,hbd.trans hz.2.2.1,hz.2.2.2⟩,fun he => (not_le_of_gt hz.2.2.1) he.2⟩
      · exact ⟨⟨hlc.trans hz.1,hz.2⟩,fun he => (ne_of_gt hz.1) he.1⟩
  have hbt := hbd.trans hdt
  have hL := thetaRect_connected hlc hbt
  have hT := thetaRect_connected (hlc.trans hcr) hdt
  have hR := thetaRect_connected hcr hbt
  have hLT : (thetaRect l c b t ∩ thetaRect l r d t).Nonempty := by
    refine ⟨Plane.mk ((l+c)/2) ((d+t)/2),?_,?_⟩ <;>
      dsimp [thetaRect]
    all_goals exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hTR : ((thetaRect l c b t ∪ thetaRect l r d t) ∩ thetaRect c r b t).Nonempty := by
    refine ⟨Plane.mk ((c+r)/2) ((d+t)/2),Or.inr ?_,?_⟩ <;>
      dsimp [thetaRect]
    all_goals exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  rw [heq]
  exact (hL.union hLT hT).union hTR hR

/-- The endpoint cap is an actual local packet with one connected track,
listed twice to share the internal two-track propagation interface. -/
theorem thetaRect_endpoint_cap_local_sides
    {l r b t c d : ℝ} (hlc : l < c) (hcr : c < r) (hbd : b < d) (hdt : d < t) :
    ∃ C : SurfaceLocalSides (thetaRect l r b t) {z : Plane | z 0 = c ∧ z 1 ≤ d},
      C.nbhd = thetaRect l r b t ∧ C.left = C.right := by
  let N := thetaRect l r b t
  let P : Set Plane := {z | z 0 = c ∧ z 1 ≤ d}
  have hconn : IsConnected (N \ P) := thetaRect_endpoint_slit_connected hlc hcr hbd hdt
  have hlimit : N ∩ P ⊆ closure (N \ P) := by
    rintro z ⟨hz,hzP⟩
    have hcl : c ∈ closure (Ioo l c) := by rw [closure_Ioo hlc.ne]; exact ⟨hlc.le,le_rfl⟩
    have heq : z = Plane.mk c (z 1) := by
      ext i
      fin_cases i
      · exact hzP.1
      · rfl
    rw [heq]
    apply closure_mono (s := (fun x : ℝ => Plane.mk x (z 1)) '' Ioo l c)
    · rintro w ⟨x,hx,rfl⟩
      exact ⟨⟨hx.1,hx.2.trans hcr,hz.2.2⟩,fun he => (ne_of_lt hx.2) he.1⟩
    · exact (show Continuous (fun x : ℝ => Plane.mk x (z 1)) by fun_prop).continuousWithinAt.mem_closure_image hcl
  exact ⟨{
    nbhd := N,left := N \ P,right := N \ P,
    isOpen_nbhd := thetaRect_open _ _ _ _,nbhd_subset := Subset.rfl,
    nbhd_diff := (union_self _).symm,connected_left := hconn,connected_right := hconn,
    limit_left := hlimit,limit_right := hlimit },rfl,rfl⟩

end CurveComplex
#print axioms CurveComplex.thetaRect_endpoint_cap_local_sides
