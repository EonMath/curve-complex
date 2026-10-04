import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualStripSurfaceChart
namespace CurveComplex
open Set Schoenflies
set_option maxHeartbeats 2500000

/-- A coordinate lower bound on all four literal boundary edges of an actual
embedded rectangle holds on the WHOLE rectangle. A hypothetical smaller
minimum lies in its open planar interior and can be decreased there. -/
theorem actual_embedded_rectangle_coordinate_lower_bound
    (B : Interval × Interval → Plane) (hB : Topology.IsEmbedding B)
    (i : Fin 2) (c : ℝ)
    (hboundary : ∀ z, z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → c≤B z i) :
    ∀ z, c≤B z i := by
  let g : Interval × Interval → ℝ := fun z => B z i
  have hgc : Continuous g := by dsimp [g]; fun_prop
  obtain ⟨z,hz,hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
    hgc.continuousOn
  have hlow : c≤B z i := by
    by_contra hn
    have hstrict : B z i<c := lt_of_not_ge hn
    have hn0 : z.1≠0 := by intro hh; have hb := hboundary z (Or.inl hh); linarith
    have hn1 : z.1≠1 := by intro hh; have hb := hboundary z (Or.inr (Or.inl hh)); linarith
    have hm0 : z.2≠0 := by intro hh; have hb := hboundary z (Or.inr (Or.inr (Or.inl hh))); linarith
    have hm1 : z.2≠1 := by intro hh; have hb := hboundary z (Or.inr (Or.inr (Or.inr hh))); linarith
    have hz0 : 0<(z.1:ℝ) := lt_of_le_of_ne z.1.property.1 (fun he => hn0 (Subtype.ext he.symm))
    have hz1 : (z.1:ℝ)<1 := lt_of_le_of_ne z.1.property.2 (fun he => hn1 (Subtype.ext he))
    have hw0 : 0<(z.2:ℝ) := lt_of_le_of_ne z.2.property.1 (fun he => hm0 (Subtype.ext he.symm))
    have hw1 : (z.2:ℝ)<1 := lt_of_le_of_ne z.2.property.2 (fun he => hm1 (Subtype.ext he))
    let O : Set Plane := {p | 0<p 0 ∧ p 0<1 ∧ 0<p 1 ∧ p 1<1}
    have hc0 : Continuous (fun p : Plane => p 0) := by fun_prop
    have hc1 : Continuous (fun p : Plane => p 1) := by fun_prop
    have hO : IsOpen O := (isOpen_lt continuous_const hc0).inter
      ((isOpen_lt hc0 continuous_const).inter
        ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)))
    let q : Plane → Interval × Interval := fun p =>
      (projIcc 0 1 zero_le_one (p 0),projIcc 0 1 zero_le_one (p 1))
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hqval (p : Plane) (hp : p∈O) :
        q p=(⟨p 0,⟨hp.1.le,hp.2.1.le⟩⟩,⟨p 1,⟨hp.2.2.1.le,hp.2.2.2.le⟩⟩) :=
      Prod.ext (projIcc_of_mem zero_le_one ⟨hp.1.le,hp.2.1.le⟩)
        (projIcc_of_mem zero_le_one ⟨hp.2.2.1.le,hp.2.2.2.le⟩)
    let F : Plane → Plane := B ∘ q
    have hFc : Continuous F := hB.continuous.comp hqc
    have hFi : Set.InjOn F O := by
      intro p hp v hv he
      have hh := hB.injective he
      change q p=q v at hh
      rw [hqval p hp,hqval v hv] at hh
      have hh0 := congrArg (fun w => (w.1:ℝ)) hh
      have hh1 := congrArg (fun w => (w.2:ℝ)) hh
      ext j; fin_cases j <;> assumption
    have hopen : IsOpen (F '' O) := surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
    let p : Plane := Plane.mk z.1 z.2
    have hp : p∈O := ⟨hz0,hz1,hw0,hw1⟩
    have hqz : q p=z := by
      rw [hqval p hp]
      rfl
    have hBz : B z∈F '' O := ⟨p,hp,by change B (q p)=B z; rw [hqz]⟩
    let d : Plane := Plane.mk (if i=0 then 1 else 0) (if i=1 then 1 else 0)
    have hdi : d i=1 := by fin_cases i <;> norm_num [d,Plane.mk]
    let v : ℝ → Plane := fun t => B z-t • d
    have hvc : Continuous v := by dsimp [v]; fun_prop
    have hv0 : v 0∈F '' O := by simpa [v] using hBz
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
      ((hopen.preimage hvc).mem_nhds hv0)
    have hve : v (ε/2)∈F '' O := hball (by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
      linarith)
    obtain ⟨u,hu,heu⟩ := hve
    have hminu := hmin (show q u∈Set.univ from Set.mem_univ _)
    change B z i≤B (q u) i at hminu
    have hco := congrArg (fun w : Plane => w i) heu
    change B (q u) i=B z i-(ε/2)*d i at hco
    rw [hdi] at hco
    nlinarith
  intro v
  have hh := hmin (show v∈Set.univ from Set.mem_univ _)
  exact hlow.trans hh
/-- The strict interior of any ACTUAL embedded rectangle has open image. -/
theorem actual_embedded_rectangle_interior_image_open
    (B : Interval × Interval → Plane) (hB : Topology.IsEmbedding B) :
    IsOpen (B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ 0<(z.2:ℝ) ∧ (z.2:ℝ)<1}) := by
  let O : Set Plane := {p | 0<p 0 ∧ p 0<1 ∧ 0<p 1 ∧ p 1<1}
  have hc0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have hc1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have hO : IsOpen O := (isOpen_lt continuous_const hc0).inter
    ((isOpen_lt hc0 continuous_const).inter
      ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)))
  let q : Plane → Interval × Interval := fun p =>
    (projIcc 0 1 zero_le_one (p 0),projIcc 0 1 zero_le_one (p 1))
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqval (p : Plane) (hp : p∈O) :
      q p=(⟨p 0,⟨hp.1.le,hp.2.1.le⟩⟩,⟨p 1,⟨hp.2.2.1.le,hp.2.2.2.le⟩⟩) :=
    Prod.ext (projIcc_of_mem zero_le_one ⟨hp.1.le,hp.2.1.le⟩)
      (projIcc_of_mem zero_le_one ⟨hp.2.2.1.le,hp.2.2.2.le⟩)
  let F : Plane → Plane := B ∘ q
  have hFc : Continuous F := hB.continuous.comp hqc
  have hFi : Set.InjOn F O := by
    intro p hp v hv he
    have hh := hB.injective he
    change q p=q v at hh
    rw [hqval p hp,hqval v hv] at hh
    have hh0 := congrArg (fun w => (w.1:ℝ)) hh
    have hh1 := congrArg (fun w => (w.2:ℝ)) hh
    ext j; fin_cases j <;> assumption
  have hopen := surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
  have heq : F '' O=B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ 0<(z.2:ℝ) ∧ (z.2:ℝ)<1} := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨q p,?_,rfl⟩
      rw [hqval p hp]
      exact hp
    · rintro ⟨z,hz,rfl⟩
      let p : Plane := Plane.mk z.1 z.2
      have hp : p∈O := hz
      refine ⟨p,hp,?_⟩
      change B (q p)=B z
      rw [hqval p hp]
      rfl
  exact heq ▸ hopen

/-- A coordinate attaining its whole-rectangle lower bound lies on the
actual rectangle boundary. This detects the common center edge after filling. -/
theorem actual_embedded_rectangle_coordinate_equality_on_boundary
    (B : Interval × Interval → Plane) (hB : Topology.IsEmbedding B)
    (i : Fin 2) (c : ℝ) (hall : ∀ z,c≤B z i)
    (z : Interval × Interval) (heq : B z i=c) :
    z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 := by
  by_contra hn
  have hn0 : z.1≠0 := fun he => hn (Or.inl he)
  have hn1 : z.1≠1 := fun he => hn (Or.inr (Or.inl he))
  have hm0 : z.2≠0 := fun he => hn (Or.inr (Or.inr (Or.inl he)))
  have hm1 : z.2≠1 := fun he => hn (Or.inr (Or.inr (Or.inr he)))
  have hz0 : 0<(z.1:ℝ) := lt_of_le_of_ne z.1.property.1 (fun he => hn0 (Subtype.ext he.symm))
  have hz1 : (z.1:ℝ)<1 := lt_of_le_of_ne z.1.property.2 (fun he => hn1 (Subtype.ext he))
  have hw0 : 0<(z.2:ℝ) := lt_of_le_of_ne z.2.property.1 (fun he => hm0 (Subtype.ext he.symm))
  have hw1 : (z.2:ℝ)<1 := lt_of_le_of_ne z.2.property.2 (fun he => hm1 (Subtype.ext he))
  let I := B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧ 0<(z.2:ℝ) ∧ (z.2:ℝ)<1}
  have hI : IsOpen I := actual_embedded_rectangle_interior_image_open B hB
  have hzI : B z∈I := ⟨z,⟨hz0,hz1,hw0,hw1⟩,rfl⟩
  let d : Plane := Plane.mk (if i=0 then 1 else 0) (if i=1 then 1 else 0)
  have hdi : d i=1 := by fin_cases i <;> norm_num [d,Plane.mk]
  let v : ℝ → Plane := fun t => B z-t • d
  have hvc : Continuous v := by dsimp [v]; fun_prop
  have hv0 : v 0∈I := by simpa [v] using hzI
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hI.preimage hvc).mem_nhds hv0)
  have hve : v (ε/2)∈I := hball (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
    linarith)
  obtain ⟨w,hw,hew⟩ := hve
  have hbw := hall w
  have hco := congrArg (fun p : Plane => p i) hew
  change B w i=B z i-(ε/2)*d i at hco
  rw [hdi,heq] at hco
  nlinarith

/-- The upper-bound companion uses the actual negated embedded rectangle. -/
theorem actual_embedded_rectangle_coordinate_upper_bound
    (B : Interval × Interval → Plane) (hB : Topology.IsEmbedding B)
    (i : Fin 2) (c : ℝ)
    (hboundary : ∀ z, z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → B z i≤c) :
    ∀ z,B z i≤c := by
  let C : Interval × Interval → Plane := fun z => -B z
  have hCc : Continuous C := by dsimp [C]; fun_prop
  have hCi : Function.Injective C := by
    intro z w he
    apply hB.injective
    exact neg_injective he
  have hC : Topology.IsEmbedding C := (hCc.isClosedEmbedding hCi).isEmbedding
  have hb : ∀ z, z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → -c≤C z i := by
    intro z hz
    have hh := hboundary z hz
    change -c≤-(B z i)
    linarith
  intro z
  have hh := actual_embedded_rectangle_coordinate_lower_bound C hC i (-c) hb z
  change -c≤-(B z i) at hh
  linarith
end CurveComplex
