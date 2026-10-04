import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import Mathlib.Topology.Maps.Proper.Basic
namespace CurveComplex.Hyperbolic
open Set
open scoped unitInterval
set_option maxHeartbeats 2000000
theorem actual_h2_metric_convex_subset_closure_metric_convex (C : Set H2)
    (hC : ∀ a∈C,∀ b∈C,∀ z : H2,dist a z+dist z b=dist a b → z∈C) :
    ∀ a∈closure C,∀ b∈closure C,∀ z : H2,dist a z+dist z b=dist a b → z∈closure C := by
  have hinterp : ∃ f : ContinuousMap (unitInterval × H2 × H2) H2,
      ∀ x, dist x.2.1 (f x)+dist (f x) x.2.2=dist x.2.1 x.2.2 ∧
        dist x.2.1 (f x)=(x.1:ℝ)*dist x.2.1 x.2.2 := by
    classical
    have hpoint (a b : H2) (t : unitInterval) :
        ∃! z : H2,dist a z+dist z b=dist a b ∧ dist a z=(t:ℝ)*dist a b := by
      obtain ⟨e,ha,hb⟩ := exists_pair_vertical_isometry a b
      let α := Real.log (e a).im
      let β := Real.log (e b).im
      let s := (1-(t:ℝ))*α+(t:ℝ)*β
      let z := e.symm (verticalPath s)
      have hs : s∈Set.uIcc α β := by
        rw [←segment_eq_uIcc,segment_eq_image]
        exact ⟨t,t.property,by simp only [smul_eq_mul];rfl⟩
      have hezre : (e z).re=0 := by simp [z,verticalPath]
      have hezlog : Real.log (e z).im=s := by simp [z,verticalPath]
      have hseg : dist a z+dist z b=dist a b :=
        (metric_segment_iff_in_vertical_interval e a b z ha hb).mpr ⟨hezre,by simpa [hezlog] using hs⟩
      have hdist : dist a z=(t:ℝ)*dist a b := by
        rw [←e.dist_eq a z,←e.dist_eq a b,UpperHalfPlane.dist_of_re_eq (ha.trans hezre.symm),
          UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm),hezlog]
        change |α-s|=(t:ℝ)*|α-β|
        rw [show α-s=(t:ℝ)*(α-β) by dsimp [s];ring,abs_mul,abs_of_nonneg t.property.1]
      refine ⟨z,⟨hseg,hdist⟩,?_⟩
      intro u hu
      obtain ⟨hure,hulog⟩ := (metric_segment_iff_in_vertical_interval e a b u ha hb).mp hu.1
      have huDist := hu.2
      rw [←e.dist_eq a u,←e.dist_eq a b,UpperHalfPlane.dist_of_re_eq (ha.trans hure.symm),
        UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm)] at huDist
      have hlog : Real.log (e u).im=s := by
        change |α-Real.log (e u).im|=(t:ℝ)*|α-β| at huDist
        change Real.log (e u).im∈Set.uIcc α β at hulog
        rcases le_total α β with hab | hba
        · rw [Set.uIcc_of_le hab,Set.mem_Icc] at hulog
          rw [abs_of_nonpos (by linarith : α-Real.log (e u).im≤0),
            abs_of_nonpos (by linarith : α-β≤0)] at huDist
          dsimp [s]
          nlinarith
        · rw [Set.uIcc_of_ge hba,Set.mem_Icc] at hulog
          rw [abs_of_nonneg (by linarith : 0≤α-Real.log (e u).im),
            abs_of_nonneg (by linarith : 0≤α-β)] at huDist
          dsimp [s]
          nlinarith
      apply e.injective
      change e u=e (e.symm (verticalPath s))
      rw [e.apply_symm_apply]
      apply UpperHalfPlane.ext_re_im
      · simpa [verticalPath] using hure
      · have hh := congrArg Real.exp hlog
        simpa [verticalPath,Real.exp_log (e u).im_pos] using hh
    let f : unitInterval × H2 × H2 → H2 := fun x => (hpoint x.2.1 x.2.2 x.1).exists.choose
    have hf : ∀ x, dist x.2.1 (f x)+dist (f x) x.2.2=dist x.2.1 x.2.2 ∧
        dist x.2.1 (f x)=(x.1:ℝ)*dist x.2.1 x.2.2 := by
      intro x
      exact (hpoint x.2.1 x.2.2 x.1).exists.choose_spec
    have hu : ∀ x z, dist x.2.1 z+dist z x.2.2=dist x.2.1 x.2.2 →
        dist x.2.1 z=(x.1:ℝ)*dist x.2.1 x.2.2 → z=f x := by
      intro x z hz1 hz2
      exact (hpoint x.2.1 x.2.2 x.1).unique ⟨hz1,hz2⟩ (hf x)
    have hc : Continuous f := by
      have hlocal (o : H2) (R : ℝ) :
          ContinuousOn f {x | dist o x.2.1 ≤ R ∧ dist o x.2.2 ≤ R} := by
        let S : Set (unitInterval × H2 × H2) := {x | dist o x.2.1 ≤ R ∧ dist o x.2.2 ≤ R}
        let T : Set H2 := Metric.closedBall o (3*R)
        have hbound (x : S) : f x.val ∈ T := by
          have hab := dist_triangle x.val.2.1 o x.val.2.2
          have haz := dist_triangle o x.val.2.1 (f x.val)
          have hbz := dist_nonneg (x := f x.val) (y := x.val.2.2)
          have hz := (hf x.val).1
          have ha := x.property.1
          have hb := x.property.2
          rw [dist_comm x.val.2.1 o] at hab
          change dist (f x.val) o ≤ 3*R
          rw [dist_comm]
          linarith
        let g : S → T := fun x => ⟨f x.val, hbound x⟩
        have hgraph : IsClosed g.graph := by
          have h1 : Continuous (fun p : S × T => dist p.1.val.2.1 p.2.val +
              dist p.2.val p.1.val.2.2) := by fun_prop
          have h2 : Continuous (fun p : S × T => dist p.1.val.2.1 p.1.val.2.2) := by fun_prop
          have h3 : Continuous (fun p : S × T => dist p.1.val.2.1 p.2.val) := by fun_prop
          have h4 : Continuous (fun p : S × T => (p.1.val.1 : ℝ) *
              dist p.1.val.2.1 p.1.val.2.2) := by fun_prop
          convert (isClosed_eq h1 h2).inter (isClosed_eq h3 h4) using 1
          ext p
          change g p.1 = p.2 ↔ _
          constructor
          · intro h
            have he : f p.1.val = p.2.val := congrArg Subtype.val h
            simpa [he] using hf p.1.val
          · intro h
            apply Subtype.ext
            exact (hu p.1.val p.2.val h.1 h.2).symm
        letI : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_closedBall o (3*R))
        have hg : Continuous g := continuous_of_isClosed_graph hgraph
        exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hg)
      rw [continuous_iff_continuousAt]
      intro x
      let R := max (dist x.2.1 x.2.1) (dist x.2.1 x.2.2) + 1
      apply (hlocal x.2.1 R).continuousAt
      have ha : dist x.2.1 x.2.1 < R := by dsimp [R]; linarith [le_max_left (dist x.2.1 x.2.1) (dist x.2.1 x.2.2)]
      have hb : dist x.2.1 x.2.2 < R := by dsimp [R]; linarith [le_max_right (dist x.2.1 x.2.1) (dist x.2.1 x.2.2)]
      have hca : Continuous (fun y : unitInterval × H2 × H2 => dist x.2.1 y.2.1) := by fun_prop
      have hcb : Continuous (fun y : unitInterval × H2 × H2 => dist x.2.1 y.2.2) := by fun_prop
      apply Filter.mem_of_superset (Filter.inter_mem ((hca.isOpen_preimage _ isOpen_Iio).mem_nhds ha) ((hcb.isOpen_preimage _ isOpen_Iio).mem_nhds hb))
      intro y hy
      exact ⟨hy.1.le,hy.2.le⟩
    exact ⟨⟨f,hc⟩,hf⟩
  have hpoint (a b : H2) (t : unitInterval) :
      ∃! z : H2,dist a z+dist z b=dist a b ∧ dist a z=(t:ℝ)*dist a b := by
    obtain ⟨e,ha,hb⟩ := exists_pair_vertical_isometry a b
    let α := Real.log (e a).im
    let β := Real.log (e b).im
    let s := (1-(t:ℝ))*α+(t:ℝ)*β
    let z := e.symm (verticalPath s)
    have hs : s∈Set.uIcc α β := by
      rw [←segment_eq_uIcc,segment_eq_image]
      exact ⟨t,t.property,by simp only [smul_eq_mul];rfl⟩
    have hezre : (e z).re=0 := by simp [z,verticalPath]
    have hezlog : Real.log (e z).im=s := by simp [z,verticalPath]
    have hseg : dist a z+dist z b=dist a b :=
      (metric_segment_iff_in_vertical_interval e a b z ha hb).mpr ⟨hezre,by simpa [hezlog] using hs⟩
    have hdist : dist a z=(t:ℝ)*dist a b := by
      rw [←e.dist_eq a z,←e.dist_eq a b,UpperHalfPlane.dist_of_re_eq (ha.trans hezre.symm),
        UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm),hezlog]
      change |α-s|=(t:ℝ)*|α-β|
      rw [show α-s=(t:ℝ)*(α-β) by dsimp [s];ring,abs_mul,abs_of_nonneg t.property.1]
    refine ⟨z,⟨hseg,hdist⟩,?_⟩
    intro u hu
    obtain ⟨hure,hulog⟩ := (metric_segment_iff_in_vertical_interval e a b u ha hb).mp hu.1
    have huDist := hu.2
    rw [←e.dist_eq a u,←e.dist_eq a b,UpperHalfPlane.dist_of_re_eq (ha.trans hure.symm),
      UpperHalfPlane.dist_of_re_eq (ha.trans hb.symm)] at huDist
    have hlog : Real.log (e u).im=s := by
      change |α-Real.log (e u).im|=(t:ℝ)*|α-β| at huDist
      change Real.log (e u).im∈Set.uIcc α β at hulog
      rcases le_total α β with hab | hba
      · rw [Set.uIcc_of_le hab,Set.mem_Icc] at hulog
        rw [abs_of_nonpos (by linarith : α-Real.log (e u).im≤0),
          abs_of_nonpos (by linarith : α-β≤0)] at huDist
        dsimp [s]
        nlinarith
      · rw [Set.uIcc_of_ge hba,Set.mem_Icc] at hulog
        rw [abs_of_nonneg (by linarith : 0≤α-Real.log (e u).im),
          abs_of_nonneg (by linarith : 0≤α-β)] at huDist
        dsimp [s]
        nlinarith
    apply e.injective
    change e u=e (e.symm (verticalPath s))
    rw [e.apply_symm_apply]
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using hure
    · have hh := congrArg Real.exp hlog
      simpa [verticalPath,Real.exp_log (e u).im_pos] using hh
  obtain ⟨f,hf⟩ := hinterp
  intro a ha b hb z hz
  by_cases hab : a=b
  · subst b
    rw [dist_self] at hz
    have hzero : dist a z=0 := by linarith [dist_nonneg (x:=a) (y:=z),dist_nonneg (x:=z) (y:=a)]
    exact (dist_eq_zero.mp hzero) ▸ ha
  have hpos : 0<dist a b := dist_pos.mpr hab
  have hle : dist a z≤dist a b := by linarith [dist_nonneg (x:=z) (y:=b)]
  let t : unitInterval := ⟨dist a z/dist a b,⟨div_nonneg dist_nonneg hpos.le,(div_le_one hpos).mpr hle⟩⟩
  have hfrac : dist a z=(t:ℝ)*dist a b := by dsimp [t];field_simp
  have he : z=f (t,a,b) := (hpoint a b t).unique ⟨hz,hfrac⟩ (hf (t,a,b))
  rw [he]
  refine map_mem_closure₂ (f:=fun a b => f (t,a,b)) ?_ ha hb ?_
  · exact f.continuous.comp (continuous_const.prodMk continuous_id)
  · intro a ha b hb
    exact hC a ha b hb (f (t,a,b)) (hf (t,a,b)).1
end CurveComplex.Hyperbolic
