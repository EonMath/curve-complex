import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import CurveComplexGenusTwo.Hyperbolic.Stabilizer
import CurveComplexGenusTwo.Hyperbolic.VerticalRigidity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
namespace CurveComplex.Hyperbolic
open Set
set_option maxHeartbeats 2000000
theorem actual_complete_geodesic_complement_component_metric_convex {ι : Type} (a : ι → ℝ → H2) (ha : ∀ i, Isometry (a i)) (x : H2) :
    let F := (⋃ i, Set.range (a i))ᶜ
    ∀ y∈connectedComponentIn F x, ∀ z∈connectedComponentIn F x, ∀ w : H2,
      dist y w+dist w z=dist y z → w∈connectedComponentIn F x := by
  dsimp only
  let F := (⋃ i, Set.range (a i))ᶜ
  let C := connectedComponentIn F x
  have hpos (k : ℝ) (a b w : H2) (ha : k≤a.re) (hb : k≤b.re)
      (hw : dist a w+dist w b=dist a b) : k≤w.re := by
      by_contra hn
      have hneg : w.re<k := lt_of_not_ge hn
      let p : H2 := ⟨(k:ℂ)+(w.im:ℂ)*Complex.I,by simpa using w.im_pos⟩
      have pre : p.re=k := by simp [p]
      have pim : p.im=w.im := by simp [p]
      have hshort (z : H2) (hz : k≤z.re) : dist z p<dist z w := by
        have hden : 0<2*z.im*w.im := by positivity
        have hsq : (z.re-k)^2 < (z.re-w.re)^2 := by nlinarith
        have hc : Real.cosh (dist z p)<Real.cosh (dist z w) := by
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',pre,pim]
          exact (div_lt_div_iff_of_pos_right hden).mpr (by linarith)
        simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_lt_cosh.mp hc
      have hpa := hshort a ha
      have hpb := hshort b hb
      have htri := dist_triangle a p b
      rw [dist_comm b p,dist_comm b w] at hpb
      linarith
  have hneg (k : ℝ) (a b w : H2) (ha : a.re≤k) (hb : b.re≤k)
      (hw : dist a w+dist w b=dist a b) : w.re≤k := by
      by_contra hn
      have hneg : k<w.re := lt_of_not_ge hn
      let p : H2 := ⟨(k:ℂ)+(w.im:ℂ)*Complex.I,by simpa using w.im_pos⟩
      have pre : p.re=k := by simp [p]
      have pim : p.im=w.im := by simp [p]
      have hshort (z : H2) (hz : z.re≤k) : dist z p<dist z w := by
        have hden : 0<2*z.im*w.im := by positivity
        have hsq : (z.re-k)^2 < (z.re-w.re)^2 := by nlinarith
        have hc : Real.cosh (dist z p)<Real.cosh (dist z w) := by
          rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',pre,pim]
          exact (div_lt_div_iff_of_pos_right hden).mpr (by linarith)
        simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_lt_cosh.mp hc
      have hpa := hshort a ha
      have hpb := hshort b hb
      have htri := dist_triangle a p b
      rw [dist_comm b p,dist_comm b w] at hpb
      linarith
  have hnormalize (a : ℝ → H2) (ha : Isometry a) :
      ∃ e : H2 ≃ᵢ H2, ∀ t, a t=e (verticalPath t) := by
      obtain ⟨e,he0,he1⟩ := exists_ordered_pair_isometry (a 0) (a 1) (by
        rw [ha.dist_eq];norm_num [Real.dist_eq])
      have h0 : e (verticalPath 0) = a 0 := by
        have hv : verticalPath 0 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext
          apply Complex.ext <;> simp [verticalPath,UpperHalfPlane.I]
        rw [hv]
        exact he0
      refine ⟨e,?_⟩
      have hf : Isometry (fun t : ℝ => e.symm (a t)) := e.symm.isometry.comp ha
      have hf0 : e.symm (a 0) = verticalPath 0 := by rw [←h0,e.symm_apply_apply]
      have hf1 : e.symm (a 1) = verticalPath 1 := by rw [←he1,e.symm_apply_apply]
      intro t
      have ht := isometry_eq_vertical_of_values _ hf hf0 hf1 t
      simpa only [e.apply_symm_apply] using congrArg e ht
  intro y hy z hz w hw
  change y∈C at hy
  change z∈C at hz
  change w∈C
  have hsegmentF : {v : H2 | dist y v+dist v z=dist y z}⊆F := by
    intro v hv
    change dist y v + dist v z = dist y z at hv
    intro hunion
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hunion
    obtain ⟨e,he⟩ := hnormalize (a i) (ha i)
    have hnot (p : H2) (hp : p∈C) : (e.symm p).re≠0 := by
      intro hzero
      have hm : p∈Set.range (a i) := by
        refine ⟨Real.log (e.symm p).im,?_⟩
        rw [he]
        apply e.symm.injective
        rw [e.symm_apply_apply]
        apply UpperHalfPlane.ext_re_im
        · simpa [verticalPath] using hzero.symm
        · simp [verticalPath,Real.exp_log (e.symm p).im_pos]
      exact (connectedComponentIn_subset F x hp) (Set.mem_iUnion.mpr ⟨i,hm⟩)
    have hcont : ContinuousOn (fun p : H2 => (e.symm p).re) C :=
      (UpperHalfPlane.continuous_re.comp e.symm.continuous).continuousOn
    have hc : IsPreconnected C := isPreconnected_connectedComponentIn
    have hv' : dist (e.symm y) (e.symm v)+dist (e.symm v) (e.symm z)=
        dist (e.symm y) (e.symm z) := by simpa only [e.symm.dist_eq] using hv
    have hzero : (e.symm v).re=0 := by
      obtain ⟨t,rfl⟩ := hi
      rw [he,e.symm_apply_apply]
      simp [verticalPath]
    rcases lt_or_gt_of_ne (hnot y hy) with hyl | hyr
    · have hzl : (e.symm z).re<0 := hc.gt_of_ne hcont hnot ⟨y,hy,hyl⟩ hz
      have hbound := hneg (max (e.symm y).re (e.symm z).re)
        (e.symm y) (e.symm z) (e.symm v) (le_max_left _ _) (le_max_right _ _) hv'
      have hmax : max (e.symm y).re (e.symm z).re<0 := max_lt hyl hzl
      linarith
    · have hzr : 0<(e.symm z).re := hc.lt_of_ne hcont hnot ⟨y,hy,hyr⟩ hz
      have hbound := hpos (min (e.symm y).re (e.symm z).re)
        (e.symm y) (e.symm z) (e.symm v) (min_le_left _ _) (min_le_right _ _) hv'
      have hmin : 0 < min (e.symm y).re (e.symm z).re := lt_min hyr hzr
      linarith
  by_cases hyz : y=z
  · subst z
    have hyw : y=w := dist_eq_zero.mp (by
      rw [dist_self,dist_comm w y] at hw
      linarith)
    simpa [←hyw] using hy
  · obtain ⟨f,hf,hfinj,hf0,hf1,hfrange⟩ := metric_segment_has_parametrization y z hyz
    have hs : IsPreconnected {v : H2 | dist y v+dist v z=dist y z} := by
      rw [←hfrange]
      exact isPreconnected_Icc.image f hf.continuousOn
    have hyS : y∈{v : H2 | dist y v+dist v z=dist y z} := by simp
    have hsub := hs.subset_connectedComponentIn hyS hsegmentF
    have heq : connectedComponentIn F x=connectedComponentIn F y := connectedComponentIn_eq hy
    change w∈connectedComponentIn F x
    rw [heq]
    exact hsub hw
end CurveComplex.Hyperbolic
