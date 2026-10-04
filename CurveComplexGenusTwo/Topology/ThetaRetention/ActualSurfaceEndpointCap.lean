import CurveComplexGenusTwo.Topology.ThetaRetention.ActualInternalSurfaceSides
import CurveComplexGenusTwo.Topology.ThetaRetention.SurfaceSidesTransport
import CurveComplexGenusTwo.Topology.ThetaRetention.PlanarEndpointCap
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Topology.CompletedJordan

namespace CurveComplex
open Set Topology Schoenflies Metric unitInterval

/-- Convert the actual interval parametrization to Schoenflies' real-domain
arc representation without changing its image. -/
theorem source_planar_interval_isArcBetween
    (g : C(I,Plane)) (hg : IsEmbedding g) :
    IsArcBetween (Set.range g) (g 0) (g 1) := by
  let f : ℝ → Plane := g ∘ Set.projIcc 0 1 zero_le_one
  have hf : Continuous f := g.continuous.comp continuous_projIcc
  have hval (t : I) : f t = g t := by
    simp [f,Set.projIcc_of_mem zero_le_one t.property]
  have hi : InjOn f I := by
    intro x hx y hy he
    have hh : g ⟨x,hx⟩ = g ⟨y,hy⟩ := by simpa only [← hval] using he
    exact congrArg Subtype.val (hg.injective hh)
  have hr : f '' I = Set.range g := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,(hval ⟨t,ht⟩).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,hval t⟩
  exact ⟨f,hf.continuousOn,hi,hr,hval 0,hval 1⟩

/-- A genuine connected endpoint cap for an arbitrary embedded surface arc.
Only a short initial subarc is put in a chart. The far tail is excluded by an
open neighborhood, and Jordan-Schoenflies straightens that actual local arc. -/
theorem source_embedded_path_zero_endpoint_cap
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (D : Set S) (hD : IsOpen D) (hpD : p 0 ∈ D) :
    ∃ C : SurfaceLocalSides D (Set.range p), p 0 ∈ C.nbhd ∧ C.left = C.right := by
  classical
  let e := chartAt Plane (p 0)
  have hpre : p.extend ⁻¹' e.source ∈ 𝓝 (0:ℝ) := by
    apply p.extend.continuous.continuousAt.preimage_mem_nhds
    apply e.open_source.mem_nhds
    rw [show p.extend (0:ℝ) = p 0 from p.extend_extends' 0]
    exact mem_chart_source Plane (p 0)
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min ε 1 / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; have := min_le_left ε (1:ℝ); linarith
  have hr1 : r < 1 := by dsimp [r]; have := min_le_right ε (1:ℝ); linarith
  let rI : I := ⟨r,hr.le,hr1.le⟩
  let qpar : I → I := fun t => ⟨r*(t:ℝ),by
    constructor
    · exact mul_nonneg hr.le t.property.1
    · nlinarith [t.property.2]⟩
  have hqpar : Continuous qpar := by fun_prop
  have hqpari : Function.Injective qpar := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change r*(t:ℝ) = r*(u:ℝ) at hh
    exact (mul_left_cancel₀ (ne_of_gt hr) hh)
  let q : C(I,S) := ⟨p ∘ qpar,p.continuous.comp hqpar⟩
  have hqi : Function.Injective q := hp.injective.comp hqpari
  have hqe (t : I) : q t ∈ e.source := by
    have hbound : |r*(t:ℝ)| < ε := by
      rw [abs_of_nonneg (mul_nonneg hr.le t.property.1)]
      nlinarith [t.property.2]
    have hmem := hεsub (show r*(t:ℝ) ∈ ball (0:ℝ) ε by simpa [Real.dist_eq] using hbound)
    change p.extend (r*(t:ℝ)) ∈ e.source at hmem
    change p.extend ((qpar t):ℝ) ∈ e.source at hmem
    rw [p.extend_extends' (qpar t)] at hmem
    exact hmem
  let g : C(I,Plane) := ⟨fun t => e (q t),by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (e.continuousAt (hqe t)).comp q.continuous.continuousAt⟩
  have hgi : Function.Injective g := by
    intro t u he
    exact hqi (e.injOn (hqe t) (hqe u) he)
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
  have hq0 : q 0 = p 0 := by
    change p (qpar 0) = p 0
    congr 1
    apply Subtype.ext
    simp [qpar]
  have hq1 : q 1 = p rI := by
    change p (qpar 1) = p rI
    congr 1
    apply Subtype.ext
    simp [qpar,rI]
  have hqr : Set.range q = p '' Icc (0:I) rI := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨qpar t,⟨?_,?_⟩,rfl⟩
      · exact (qpar t).property.1
      · change r*(t:ℝ) ≤ r
        nlinarith [t.property.2]
    · rintro ⟨t,ht,rfl⟩
      let u : I := ⟨(t:ℝ)/r,by
        constructor
        · exact div_nonneg ht.1 hr.le
        · exact (div_le_one hr).mpr ht.2⟩
      refine ⟨u,?_⟩
      change p (qpar u) = p t
      congr 1
      apply Subtype.ext
      change r*((t:ℝ)/r) = t
      field_simp
  have hP := source_planar_interval_isArcBetween g hg
  obtain ⟨A,hA,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hP
  obtain ⟨F,hF,hF0,hF1⟩ := exists_ambient_straightening_of_jordan_arc_split hA hP hmeet hJ
  let E := e.trans F.toOpenPartialHomeomorph
  have hEs : E.source = e.source := by simp [E,OpenPartialHomeomorph.trans_source]
  have hpEs : p 0 ∈ E.source := by rw [hEs]; exact mem_chart_source Plane (p 0)
  have hE0 : E (p 0) = cornerNE := by
    change F (e (p 0)) = cornerNE
    change F (e (q 0)) = cornerNE at hF0
    rw [hq0] at hF0
    exact hF0
  let T := p '' Icc rI (1:I)
  have hTc : IsClosed T := (isCompact_Icc.image p.continuous).isClosed
  have hpT : p 0 ∉ T := by
    rintro ⟨t,ht,he⟩
    have heq : t = 0 := hp.injective he
    have hh : r ≤ (t:ℝ) := ht.1
    rw [heq] at hh
    exact (not_le_of_gt hr) hh
  let V := E.target ∩ E.symm ⁻¹' (D \ T)
  have hV : IsOpen V := E.isOpen_inter_preimage_symm (hD.sdiff hTc)
  have hV0 : cornerNE ∈ V := by
    refine ⟨hE0 ▸ E.map_source hpEs,?_⟩
    change E.symm cornerNE ∈ D \ T
    rw [← hE0,E.left_inv hpEs]
    exact ⟨hpD,hpT⟩
  let k : ℝ × ℝ → Plane := fun z => Plane.mk z.1 z.2
  have hk : Continuous k := by fun_prop
  have hk0 : k (1,1) = cornerNE := rfl
  have hNV : k ⁻¹' V ∈ 𝓝 ((1:ℝ),(1:ℝ)) := hk.continuousAt.preimage_mem_nhds (hV.mem_nhds (hk0 ▸ hV0))
  obtain ⟨U,hU,W,hW,hUW⟩ := mem_nhds_prod_iff.mp hNV
  obtain ⟨α,hα,hαU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨β,hβ,hβW⟩ := Metric.mem_nhds_iff.mp hW
  let δ : ℝ := min α (min β 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδα : δ < α := by dsimp [δ]; have := min_le_left α (min β 1); linarith
  have hδβ : δ < β := by dsimp [δ]; have := (min_le_right α (min β 1)).trans (min_le_left β 1); linarith
  have hδ1 : δ < 1 := by dsimp [δ]; have := (min_le_right α (min β 1)).trans (min_le_right β 1); linarith
  let N := thetaRect (1-δ) (1+δ) (1-δ) (1+δ)
  have hNVsub : N ⊆ V := by
    intro z hz
    have hx : z 0 ∈ U := hαU (by
      rw [mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.1,hz.2.1])
    have hy : z 1 ∈ W := hβW (by
      rw [mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.2.2.1,hz.2.2.2])
    have hh : k (z 0,z 1) ∈ V := hUW (show (z 0,z 1) ∈ U ×ˢ W from ⟨hx,hy⟩)
    have he : k (z 0,z 1) = z := by ext i; fin_cases i <;> rfl
    exact he ▸ hh
  have hPN (z : Plane) (hz : z ∈ N) : E.symm z ∈ Set.range p ↔ z 0 = 1 ∧ z 1 ≤ 1 := by
    have hzV := hNVsub hz
    have heInv : E (E.symm z) = z := E.right_inv hzV.1
    constructor
    · rintro ⟨s,hs⟩
      have hsNot : s ∉ Icc rI (1:I) := by intro he; exact hzV.2.2 ⟨s,he,hs⟩
      have hsr : s < rI := lt_of_not_ge (by intro he; exact hsNot ⟨he,s.property.2⟩)
      have hsq : p s ∈ Set.range q := hqr.symm ▸ ⟨s,⟨s.property.1,hsr.le⟩,rfl⟩
      obtain ⟨u,hu⟩ := hsq
      have hzF : z ∈ F '' Set.range g := by
        refine ⟨g u,Set.mem_range_self u,?_⟩
        change E (q u) = z
        rw [hu,hs,heInv]
      rw [hF] at hzF
      rcases hzF with hzBottom | hzRight
      · have hy := (mem_sideBottom.mp hzBottom).1
        exfalso
        have hzlo := hz.2.2.1
        linarith
      · exact ⟨(mem_sideRight.mp hzRight).1,(abs_le.mp (mem_sideRight.mp hzRight).2).2⟩
    · intro hs
      have hzRight : z ∈ sideRight := mem_sideRight.mpr ⟨hs.1,abs_le.mpr ⟨by linarith [hz.2.2.1],hs.2⟩⟩
      have hzF : z ∈ F '' Set.range g := hF.symm ▸ Or.inr hzRight
      obtain ⟨w,⟨u,rfl⟩,hu⟩ := hzF
      refine ⟨qpar u,?_⟩
      change q u = E.symm z
      have heq : E (q u) = z := hu
      have hqu : q u ∈ E.source := by rw [hEs]; exact hqe u
      rw [← heq,E.left_inv hqu]
  obtain ⟨C,hCN,hCr⟩ := thetaRect_endpoint_cap_local_sides
    (show 1-δ < 1 by linarith) (show 1 < 1+δ by linarith)
    (show 1-δ < 1 by linarith) (show 1 < 1+δ by linarith)
  let B := C.pullbackChart E (by rw [hCN]; exact fun z hz => (hNVsub hz).1)
    (by rintro x ⟨z,hz,rfl⟩; exact (hNVsub (by simpa only [N,hCN] using hz)).2.1)
    (by intro z hz; exact hPN z (by simpa only [N,hCN] using hz))
  refine ⟨B,?_,?_⟩
  · refine ⟨cornerNE,?_,?_⟩
    · rw [hCN]
      change 1-δ < 1 ∧ 1 < 1+δ ∧ 1-δ < 1 ∧ 1 < 1+δ
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · rw [← hE0,E.left_inv hpEs]
  · exact congrArg (fun Q : Set Plane => E.symm '' Q) hCr

end CurveComplex
#print axioms CurveComplex.source_embedded_path_zero_endpoint_cap
