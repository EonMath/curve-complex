import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.JordanSchoenflies
import Mathlib

namespace CurveComplex.G3Review
open CurveComplex Set Topology Schoenflies
set_option maxHeartbeats 8000000

theorem actual_four_arc_cycle_has_prescribed_embedded_square
    (P Q E R : Interval → Schoenflies.Plane)
    (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Q)
    (hE : Topology.IsEmbedding E) (hR : Topology.IsEmbedding R)
    (hPE : P 0 = E 0) (hPR : P 1 = R 0)
    (hQE : Q 0 = E 1) (hQR : Q 1 = R 1)
    (hPEm : ∀ s t, P s = E t → s = 0 ∧ t = 0)
    (hPRm : ∀ s t, P s = R t → s = 1 ∧ t = 0)
    (hQEm : ∀ s t, Q s = E t → s = 0 ∧ t = 1)
    (hQRm : ∀ s t, Q s = R t → s = 1 ∧ t = 1)
    (hPQ : Disjoint (Set.range P) (Set.range Q))
    (hER : Disjoint (Set.range E) (Set.range R)) :
    ∃ B : Interval × Interval → Schoenflies.Plane, Topology.IsEmbedding B ∧
      (∀ u, B (u,0) = P u) ∧ (∀ u, B (u,1) = Q u) ∧
      (∀ v, B (0,v) = E v) ∧ (∀ v, B (1,v) = R v) := by
  classical
  have four_edge_loop (C D L R : C(Interval,Plane))
      (hC : Topology.IsEmbedding C) (hD : Topology.IsEmbedding D)
      (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
      (hC0 : C 0=L 0) (hC1 : C 1=R 0) (hD0 : D 0=L 1) (hD1 : D 1=R 1)
      (hCD : Disjoint (Set.range C) (Set.range D))
      (hLR : Disjoint (Set.range L) (Set.range R))
      (hCR : ∀ x ∈ Set.range C,x ∈ Set.range R → x=C 1)
      (hCL : ∀ x ∈ Set.range C,x ∈ Set.range L → x=C 0)
      (hDR : ∀ x ∈ Set.range D,x ∈ Set.range R → x=D 1)
      (hDL : ∀ x ∈ Set.range D,x ∈ Set.range L → x=D 0) :
      ∃ f : ℝ → Plane, IsLoop f ∧
        f '' Interval=((Set.range C ∪ Set.range R) ∪ (Set.range D ∪ Set.range L)) ∧
        ∀ t : Interval, f ((t:ℝ)/4)=C t ∧ f (((t:ℝ)+1)/4)=R t ∧
          f ((3-(t:ℝ))/4)=D t ∧ f (1-(t:ℝ)/4)=L t := by
    have raw_arc (g : C(Interval,Plane)) (hg : Topology.IsEmbedding g) :
        ∃ F : ℝ → Plane, ContinuousOn F Interval ∧ InjOn F Interval ∧
          F '' Interval=Set.range g ∧ ∀ t : Interval,F (t:ℝ)=g t := by
      let F : ℝ → Plane := g ∘ Set.projIcc 0 1 zero_le_one
      have hval (t : Interval) : F (t:ℝ)=g t := by
        simp [F,Set.projIcc_of_mem zero_le_one t.property]
      refine ⟨F,(g.continuous.comp continuous_projIcc).continuousOn,?_,?_,hval⟩
      · intro x hx y hy he
        have hh : g ⟨x,hx⟩=g ⟨y,hy⟩ := by simpa only [← hval] using he
        exact congrArg Subtype.val (hg.injective hh)
      · ext x
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨⟨t,ht⟩,(hval ⟨t,ht⟩).symm⟩
        · rintro ⟨t,rfl⟩
          exact ⟨t,t.property,hval t⟩
    let Dr : C(Interval,Plane) := D.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    let Lr : C(Interval,Plane) := L.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    have hDr : Topology.IsEmbedding Dr := (Dr.continuous.isClosedEmbedding
      (hD.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
    have hLr : Topology.IsEmbedding Lr := (Lr.continuous.isClosedEmbedding
      (hL.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
    have hDrange : Set.range Dr=Set.range D := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,by simp [Dr,Lr]⟩
    have hLrange : Set.range Lr=Set.range L := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,by simp [Dr,Lr]⟩
    obtain ⟨craw,hcc,hci,hcr,hcv⟩ := raw_arc C hC
    obtain ⟨rraw,hrc,hri,hrr,hrv⟩ := raw_arc R hR
    obtain ⟨draw,hdc,hdi,hdr,hdv⟩ := raw_arc Dr hDr
    obtain ⟨lraw,hlc,hli,hlr,hlv⟩ := raw_arc Lr hLr
    have hc0 : craw 0=C 0 := hcv 0
    have hc1 : craw 1=C 1 := hcv 1
    have hr0 : rraw 0=R 0 := hrv 0
    have hr1 : rraw 1=R 1 := hrv 1
    have hd0 : draw 0=D 1 := by simpa [Dr] using hdv 0
    have hd1 : draw 1=D 0 := by simpa [Dr] using hdv 1
    have hl0 : lraw 0=L 1 := by simpa [Lr] using hlv 0
    have hl1 : lraw 1=L 0 := by simpa [Lr] using hlv 1
    have hcmid : craw 1=rraw 0 := hc1.trans (hC1.trans hr0.symm)
    have hdmid : draw 1=lraw 0 := hd1.trans (hD0.trans hl0.symm)
    have hcmeet : ∀ x ∈ craw '' Interval,x ∈ rraw '' Interval → x=craw 1 := by
      intro x hx hy
      rw [hcr] at hx
      rw [hrr] at hy
      exact (hCR x hx hy).trans hc1.symm
    have hdmeet : ∀ x ∈ draw '' Interval,x ∈ lraw '' Interval → x=draw 1 := by
      intro x hx hy
      rw [hdr,hDrange] at hx
      rw [hlr,hLrange] at hy
      exact (hDL x hx hy).trans hd1.symm
    let F := Schoenflies.concatenate craw rraw
    let G := Schoenflies.concatenate draw lraw
    have hFc : ContinuousOn F Interval := continuousOn_concatenate hcc hrc hcmid
    have hGc : ContinuousOn G Interval := continuousOn_concatenate hdc hlc hdmid
    have hFi : InjOn F Interval := injOn_concatenate hci hri hcmid hcmeet
    have hGi : InjOn G Interval := injOn_concatenate hdi hli hdmid hdmeet
    have hFr : F '' Interval=Set.range C ∪ Set.range R := by
      rw [image_concatenate hcmid,hcr,hrr]
    have hGr : G '' Interval=Set.range D ∪ Set.range L := by
      rw [image_concatenate hdmid,hdr,hlr,hDrange,hLrange]
    have hF0 : F 0=C 0 := (concatenate_zero).trans hc0
    have hF1 : F 1=R 1 := (concatenate_one).trans hr1
    have hG0 : G 0=D 1 := (concatenate_zero).trans hd0
    have hG1 : G 1=L 0 := (concatenate_one).trans hl1
    have hmid : F 1=G 0 := hF1.trans (hD1.symm.trans hG0.symm)
    have hclose : G 1=F 0 := hG1.trans (hC0.symm.trans hF0.symm)
    have hmeet : ∀ x ∈ F '' Interval,x ∈ G '' Interval → x=F 0 ∨ x=F 1 := by
      intro x hx hy
      rw [hFr] at hx
      rw [hGr] at hy
      rcases hx with hxC | hxR <;> rcases hy with hyD | hyL
      · exact False.elim (Set.disjoint_left.mp hCD hxC hyD)
      · exact Or.inl ((hCL x hxC hyL).trans hF0.symm)
      · exact Or.inr ((hDR x hyD hxR).trans (hD1.trans hF1.symm))
      · exact False.elim (Set.disjoint_left.mp hLR hyL hxR)
    let f := Schoenflies.concatenate F G
    refine ⟨f,IsLoop.concatenate hFc hFi hGc hGi hmid hclose hmeet,?_,?_⟩
    · rw [image_concatenate hmid,hFr,hGr]
    · intro t
      refine ⟨?_,?_,?_,?_⟩
      · change Schoenflies.concatenate F G ((t:ℝ)/4)=C t
        rw [concatenate_of_le (by linarith [t.property.2])]
        change Schoenflies.concatenate craw rraw (2*((t:ℝ)/4))=C t
        rw [concatenate_of_le (by linarith [t.property.2])]
        convert hcv t using 1 <;> congr 1 <;> ring
      · change Schoenflies.concatenate F G (((t:ℝ)+1)/4)=R t
        rw [concatenate_of_le (by linarith [t.property.2])]
        change Schoenflies.concatenate craw rraw (2*(((t:ℝ)+1)/4))=R t
        rw [concatenate_upperHalf hcmid ⟨by linarith [t.property.1],by linarith [t.property.2]⟩]
        convert hrv t using 1 <;> congr 1 <;> ring
      · change Schoenflies.concatenate F G ((3-(t:ℝ))/4)=D t
        rw [concatenate_upperHalf hmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
        change Schoenflies.concatenate draw lraw (2*((3-(t:ℝ))/4)-1)=D t
        rw [concatenate_of_le (by linarith [t.property.1])]
        have hh := hdv (unitInterval.symm t)
        simpa only [Dr,ContinuousMap.comp_apply,ContinuousMap.coe_mk,unitInterval.symm_symm] using
          (show draw (2*(2*((3-(t:ℝ))/4)-1))=Dr (unitInterval.symm t) from by
            convert hh using 1 <;> congr 1 <;> change _=1-(t:ℝ) <;> ring)
      · change Schoenflies.concatenate F G (1-(t:ℝ)/4)=L t
        rw [concatenate_upperHalf hmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
        change Schoenflies.concatenate draw lraw (2*(1-(t:ℝ)/4)-1)=L t
        rw [concatenate_upperHalf hdmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
        have hh := hlv (unitInterval.symm t)
        simpa only [Lr,ContinuousMap.comp_apply,ContinuousMap.coe_mk,unitInterval.symm_symm] using
          (show lraw (2*(2*(1-(t:ℝ)/4)-1)-1)=Lr (unitInterval.symm t) from by
            convert hh using 1 <;> congr 1 <;> change _=1-(t:ℝ) <;> ring)
  let Cedge : C(Interval,Plane) := ⟨P,hP.continuous⟩
  let Dedge : C(Interval,Plane) := ⟨Q,hQ.continuous⟩
  let Ledge : C(Interval,Plane) := ⟨E,hE.continuous⟩
  let Redge : C(Interval,Plane) := ⟨R,hR.continuous⟩
  have hCRmeet : ∀ x ∈ Set.range Cedge,x ∈ Set.range Redge → x=Cedge 1 := by
    rintro x ⟨s,rfl⟩ ⟨t,he⟩
    change R t = P s at he
    change P s = P 1
    rw [(hPRm s t he.symm).1]
  have hCLmeet : ∀ x ∈ Set.range Cedge,x ∈ Set.range Ledge → x=Cedge 0 := by
    rintro x ⟨s,rfl⟩ ⟨t,he⟩
    change E t = P s at he
    change P s = P 0
    rw [(hPEm s t he.symm).1]
  have hDRmeet : ∀ x ∈ Set.range Dedge,x ∈ Set.range Redge → x=Dedge 1 := by
    rintro x ⟨s,rfl⟩ ⟨t,he⟩
    change R t = Q s at he
    change Q s = Q 1
    rw [(hQRm s t he.symm).1]
  have hDLmeet : ∀ x ∈ Set.range Dedge,x ∈ Set.range Ledge → x=Dedge 0 := by
    rintro x ⟨s,rfl⟩ ⟨t,he⟩
    change E t = Q s at he
    change Q s = Q 0
    rw [(hQEm s t he.symm).1]
  obtain ⟨actualBoundaryLoop,hactualBoundaryLoop,hactualBoundaryLoopRange,hactualBoundaryQuarter⟩ :=
    four_edge_loop Cedge Dedge Ledge Redge hP hQ hE hR
      hPE hPR hQE hQR hPQ hER hCRmeet hCLmeet hDRmeet hDLmeet
  let Jboundary : Set Plane := (Set.range Cedge ∪ Set.range Redge) ∪ (Set.range Dedge ∪ Set.range Ledge)
  have hJboundary : IsJordanCurve Jboundary := ⟨actualBoundaryLoop,hactualBoundaryLoop,hactualBoundaryLoopRange⟩
  let horizontal (a : ℝ) : C(Interval,Plane) := ⟨fun t => Plane.mk (2*(t:ℝ)-1) a,by fun_prop⟩
  let vertical (a : ℝ) : C(Interval,Plane) := ⟨fun t => Plane.mk a (2*(t:ℝ)-1),by fun_prop⟩
  have hhorizontal (a : ℝ) : Topology.IsEmbedding (horizontal a) :=
    ((horizontal a).continuous.isClosedEmbedding (by
      intro t u he
      have hh := congrArg (fun x : Plane => x 0) he
      apply Subtype.ext
      change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
      linarith)).isEmbedding
  have hvertical (a : ℝ) : Topology.IsEmbedding (vertical a) :=
    ((vertical a).continuous.isClosedEmbedding (by
      intro t u he
      have hh := congrArg (fun x : Plane => x 1) he
      apply Subtype.ext
      change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
      linarith)).isEmbedding
  have hhorizontalRange (a : ℝ) : Set.range (horizontal a)={x : Plane | x 1=a ∧ |x 0| ≤ 1} := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨rfl,?_⟩
      change |2*(t:ℝ)-1| ≤ 1
      rw [abs_le]
      constructor <;> linarith [t.property.1,t.property.2]
    · intro hx
      let t : Interval := ⟨(x 0+1)/2,by
        rcases abs_le.mp hx.2 with ⟨hl,hu⟩
        constructor <;> linarith⟩
      refine ⟨t,?_⟩
      ext i
      fin_cases i
      · change 2*((x 0+1)/2)-1=x 0
        ring
      · exact hx.1.symm
  have hverticalRange (a : ℝ) : Set.range (vertical a)={x : Plane | x 0=a ∧ |x 1| ≤ 1} := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨rfl,?_⟩
      change |2*(t:ℝ)-1| ≤ 1
      rw [abs_le]
      constructor <;> linarith [t.property.1,t.property.2]
    · intro hx
      let t : Interval := ⟨(x 1+1)/2,by
        rcases abs_le.mp hx.2 with ⟨hl,hu⟩
        constructor <;> linarith⟩
      refine ⟨t,?_⟩
      ext i
      fin_cases i
      · exact hx.1.symm
      · change 2*((x 1+1)/2)-1=x 1
        ring
  have hmC0 : horizontal (-1) 0=vertical (-1) 0 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmC1 : horizontal (-1) 1=vertical 1 0 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmD0 : horizontal 1 0=vertical (-1) 1 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmD1 : horizontal 1 1=vertical 1 1 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmCD : Disjoint (Set.range (horizontal (-1))) (Set.range (horizontal 1)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := congrArg (fun x : Plane => x 1) he
    change (1:ℝ)=-1 at hh
    norm_num at hh
  have hmLR : Disjoint (Set.range (vertical (-1))) (Set.range (vertical 1)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := congrArg (fun x : Plane => x 0) he
    change (1:ℝ)=-1 at hh
    norm_num at hh
  have horizontal_vertical_meet (a b : ℝ) (t u : Interval)
      (he : horizontal a t=vertical b u) : horizontal a t=Plane.mk b a := by
    have hh := congrArg (fun x : Plane => x 0) he
    ext i
    fin_cases i
    · exact hh
    · rfl
  have hmCR : ∀ x ∈ Set.range (horizontal (-1)),x ∈ Set.range (vertical 1) → x=horizontal (-1) 1 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet (-1) 1 t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  have hmCL : ∀ x ∈ Set.range (horizontal (-1)),x ∈ Set.range (vertical (-1)) → x=horizontal (-1) 0 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet (-1) (-1) t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  have hmDR : ∀ x ∈ Set.range (horizontal 1),x ∈ Set.range (vertical 1) → x=horizontal 1 1 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet 1 1 t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  have hmDL : ∀ x ∈ Set.range (horizontal 1),x ∈ Set.range (vertical (-1)) → x=horizontal 1 0 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet 1 (-1) t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  obtain ⟨modelBoundaryLoop,hmodelBoundaryLoop,hmodelBoundaryLoopRange,hmodelBoundaryQuarter⟩ :=
    four_edge_loop (horizontal (-1)) (horizontal 1) (vertical (-1)) (vertical 1)
      (hhorizontal (-1)) (hhorizontal 1) (hvertical (-1)) (hvertical 1)
      hmC0 hmC1 hmD0 hmD1 hmCD hmLR hmCR hmCL hmDR hmDL
  have hmodelRange : modelBoundaryLoop '' Interval=Schoenflies.modelCurve := by
    rw [hmodelBoundaryLoopRange,hhorizontalRange,hhorizontalRange,hverticalRange,hverticalRange,
      Schoenflies.modelCurve_eq_sides]
    ext x
    simp only [Set.mem_union,Set.mem_setOf_eq,Schoenflies.mem_sideTop,Schoenflies.mem_sideLeft,
      Schoenflies.mem_sideBottom,Schoenflies.mem_sideRight]
    tauto
  obtain ⟨matchedBoundary,hmatchedBoundary⟩ := hmodelBoundaryLoop.exists_homeomorph hactualBoundaryLoop
  let boundaryHomeo : Schoenflies.modelCurve ≃ₜ Jboundary :=
    (Homeomorph.setCongr hmodelRange.symm).trans (matchedBoundary.trans
      (Homeomorph.setCongr hactualBoundaryLoopRange))
  have hboundaryLoop (t : ℝ) (ht : t ∈ Interval) :
      (boundaryHomeo ⟨modelBoundaryLoop t,hmodelRange ▸ Set.mem_image_of_mem _ ht⟩).val=actualBoundaryLoop t :=
    hmatchedBoundary t ht
  obtain ⟨F,hF⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    Schoenflies.isJordanCurve_modelCurve hJboundary boundaryHomeo
  have hfillLoop (t : ℝ) (ht : t ∈ Interval) : F (modelBoundaryLoop t)=actualBoundaryLoop t :=
    (hF ⟨modelBoundaryLoop t,hmodelRange ▸ Set.mem_image_of_mem _ ht⟩).trans (hboundaryLoop t ht)
  let squareMap : Interval × Interval → Plane := fun uv => Plane.mk (2*(uv.1:ℝ)-1) (2*(uv.2:ℝ)-1)
  have hsquareContinuous : Continuous squareMap := by fun_prop
  have hsquareInjective : Function.Injective squareMap := by
    intro x y he
    apply Prod.ext
    · apply Subtype.ext
      have h := congrArg (fun z : Plane => z 0) he
      change 2*(x.1:ℝ)-1=2*(y.1:ℝ)-1 at h
      linarith
    · apply Subtype.ext
      have h := congrArg (fun z : Plane => z 1) he
      change 2*(x.2:ℝ)-1=2*(y.2:ℝ)-1 at h
      linarith
  have hsquareEmbedding : Topology.IsEmbedding squareMap :=
    (hsquareContinuous.isClosedEmbedding hsquareInjective).isEmbedding
  refine ⟨F ∘ squareMap,F.isEmbedding.comp hsquareEmbedding,?_,?_,?_,?_⟩
  · intro u
    have h := hfillLoop ((u:ℝ)/4) ⟨by linarith [u.property.1],by linarith [u.property.2]⟩
    rw [(hmodelBoundaryQuarter u).1,(hactualBoundaryQuarter u).1] at h
    simpa [squareMap,Function.comp_apply,show (2:ℝ)-1=1 by norm_num,
      horizontal,ContinuousMap.coe_mk,Cedge] using h
  · intro u
    have h := hfillLoop ((3-(u:ℝ))/4) ⟨by linarith [u.property.2],by linarith [u.property.1]⟩
    rw [(hmodelBoundaryQuarter u).2.2.1,(hactualBoundaryQuarter u).2.2.1] at h
    simpa [squareMap,Function.comp_apply,show (2:ℝ)-1=1 by norm_num,
      horizontal,ContinuousMap.coe_mk,Dedge] using h
  · intro v
    have h := hfillLoop (1-(v:ℝ)/4) ⟨by linarith [v.property.2],by linarith [v.property.1]⟩
    rw [(hmodelBoundaryQuarter v).2.2.2,(hactualBoundaryQuarter v).2.2.2] at h
    simpa [squareMap,Function.comp_apply,show (2:ℝ)-1=1 by norm_num,
      vertical,ContinuousMap.coe_mk,Ledge] using h
  · intro v
    have h := hfillLoop (((v:ℝ)+1)/4) ⟨by linarith [v.property.1],by linarith [v.property.2]⟩
    rw [(hmodelBoundaryQuarter v).2.1,(hactualBoundaryQuarter v).2.1] at h
    simpa [squareMap,Function.comp_apply,show (2:ℝ)-1=1 by norm_num,
      vertical,ContinuousMap.coe_mk,Redge] using h

end CurveComplex.G3Review
