import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.ActualHarerPrescribedEdgeSquareProof
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.UnitDiskSquareBoundary

open CurveComplex Set Topology Schoenflies
namespace ActualHarerDiskGluing
set_option maxHeartbeats 4000000

theorem actual_disk_attach_half_collar_with_optional_endpoint_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (q g : C(Interval, S)) (d : C(Metric.closedBall (0 : Plane) 1, S))
    (hq : IsEmbedding q) (hg : IsEmbedding g) (hd : IsEmbedding d)
    (hzero : q 0 = g 0) (hone : q 1 = g 1)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range q ∪ range g)
    (hcollision : ∀ s t : Interval, q s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (H : C(Interval × Interval, S)) (c₀ c₁ : Bool)
    (hnotBoth : ¬ (c₀ = true ∧ c₁ = true))
    (hcenter : ∀ t : Interval, H (t, 0) = q t)
    (hHcollision : ∀ t u t' u' : Interval,
      H (t, u) = H (t', u') ↔
        t = t' ∧ (u = u' ∨ collapsedEndpoint c₀ c₁ t))
    (hintersection : range H ∩ range d = range q) :
    ∃ e : C(Metric.closedBall (0 : Plane) 1, S),
      IsEmbedding e ∧ range e = range d ∪ range H ∧
      e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
        range g ∪ range (fun u : Interval => H (0, u)) ∪
          range (fun u : Interval => H (1, u)) ∪
          range (fun t : Interval => H (t, 1)) := by
  classical
  obtain ⟨P,hP,hPr,hPt,hPo⟩ := actual_two_side_disk_constructs_prescribed_edge_square
    q g d hq hg hd hzero hone hboundary hcollision
  obtain ⟨A,B,hAi,hBk,hAB,hs,hAbd,hBbd⟩ := optional_collapse_model c₀ c₁ hnotBoth
  have hPH (t u t' u' : Interval) : P (t,u)=H (t',u') ↔
      t=t' ∧ u=1 ∧ (u'=0 ∨ collapsedEndpoint c₀ c₁ t) := by
    constructor
    · intro he
      have hm : H (t',u') ∈ range q := by
        rw [← hintersection]
        exact ⟨mem_range_self (t',u'),he ▸ (hPr ▸ mem_range_self (t,u))⟩
      obtain ⟨s,hqs⟩ := hm
      have hh : H (s,0)=H (t',u') := (hcenter s).trans hqs
      obtain ⟨hst,hu⟩ := (hHcollision s 0 t' u').mp hh
      have hp : (t,u)=(s,1) := hP.injective (he.trans (hqs.symm.trans (hPt s).symm))
      have ht : t=s := congrArg Prod.fst hp
      have hu1 : u=1 := congrArg Prod.snd hp
      refine ⟨ht.trans hst,hu1,?_⟩
      rcases hu with hu | hc
      · exact Or.inl hu.symm
      · exact Or.inr (ht.symm ▸ hc)
    · rintro ⟨rfl,rfl,hu⟩
      rw [hPt,← hcenter]
      exact (hHcollision t 0 t u').mpr ⟨rfl,hu.elim (fun h => Or.inl h.symm) Or.inr⟩
  let m : C((Interval × Interval) ⊕ (Interval × Interval),Interval × Interval) :=
    ⟨Sum.elim A B,A.continuous.sumElim B.continuous⟩
  let n : C((Interval × Interval) ⊕ (Interval × Interval),S) :=
    ⟨Sum.elim P H,P.continuous.sumElim H.continuous⟩
  have hk (x y : (Interval × Interval) ⊕ (Interval × Interval)) : m x=m y ↔ n x=n y := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact ⟨fun h => congrArg P (hAi h),fun h => congrArg A (hP.injective h)⟩
      | inr y => exact (hAB x.1 x.2 y.1 y.2).trans (hPH x.1 x.2 y.1 y.2).symm
    | inr x =>
      cases y with
      | inl y =>
        exact ⟨fun h => ((hPH y.1 y.2 x.1 x.2).mpr
          ((hAB y.1 y.2 x.1 x.2).mp h.symm)).symm,
          fun h => ((hAB y.1 y.2 x.1 x.2).mpr
          ((hPH y.1 y.2 x.1 x.2).mp h.symm)).symm⟩
      | inr y => exact (hBk x.1 x.2 y.1 y.2).trans (hHcollision x.1 x.2 y.1 y.2).symm
  obtain ⟨f,hf,hfr,hfe⟩ := compact_kernel_transport m n hs hk
  have hfa (z : Interval × Interval) : f (A z)=P z := hfe (Sum.inl z)
  have hfb (z : Interval × Interval) : f (B z)=H z := hfe (Sum.inr z)
  have hfu : range f=range d ∪ range H := by
    rw [hfr,← hPr]
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      cases z with
      | inl z => exact Or.inl (mem_range_self z)
      | inr z => exact Or.inr (mem_range_self z)
    · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
      · exact ⟨Sum.inl z,rfl⟩
      · exact ⟨Sum.inr z,rfl⟩
  have hfbd : f '' squareBoundary =
      range g ∪ range (fun u : Interval => H (0,u)) ∪
      range (fun u : Interval => H (1,u)) ∪ range (fun t : Interval => H (t,1)) := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,hw⟩ := hs z
      cases w with
      | inl w =>
        have hw' : A w = z := hw
        have hz' : A (w.1,w.2) ∈ squareBoundary := by simpa only [Prod.eta,hw'] using hz
        have hb : w.1=0 ∨ w.1=1 ∨ w.2=0 := (hAbd w.1 w.2).mp hz'
        have he : f z=P w := hw ▸ hfa w
        rw [he]
        left; left; left
        rw [← hPo]
        rcases hb with ht | ht | hu
        · exact Or.inl (Or.inr ⟨w.2,by rw [← Prod.eta w,ht]⟩)
        · exact Or.inr ⟨w.2,by rw [← Prod.eta w,ht]⟩
        · exact Or.inl (Or.inl ⟨w.1,by rw [← Prod.eta w,hu]⟩)
      | inr w =>
        have hw' : B w = z := hw
        have hz' : B (w.1,w.2) ∈ squareBoundary := by simpa only [Prod.eta,hw'] using hz
        have hb : w.1=0 ∨ w.1=1 ∨ w.2=1 := (hBbd w.1 w.2).mp hz'
        have he : f z=H w := hw ▸ hfb w
        rw [he]
        rcases hb with ht | ht | hu
        · exact Or.inl (Or.inl (Or.inr ⟨w.2,by rw [← Prod.eta w,ht]⟩))
        · exact Or.inl (Or.inr ⟨w.2,by rw [← Prod.eta w,ht]⟩)
        · exact Or.inr ⟨w.1,by rw [← Prod.eta w,hu]⟩
    · rintro (((hg | ⟨u,rfl⟩) | ⟨u,rfl⟩) | ⟨t,rfl⟩)
      · rw [← hPo] at hg
        rcases hg with (⟨t,rfl⟩ | ⟨u,rfl⟩) | ⟨u,rfl⟩
        · exact ⟨A (t,0),(hAbd t 0).mpr (Or.inr (Or.inr rfl)),hfa (t,0)⟩
        · exact ⟨A (0,u),(hAbd 0 u).mpr (Or.inl rfl),hfa (0,u)⟩
        · exact ⟨A (1,u),(hAbd 1 u).mpr (Or.inr (Or.inl rfl)),hfa (1,u)⟩
      · exact ⟨B (0,u),(hBbd 0 u).mpr (Or.inl rfl),hfb (0,u)⟩
      · exact ⟨B (1,u),(hBbd 1 u).mpr (Or.inr (Or.inl rfl)),hfb (1,u)⟩
      · exact ⟨B (t,1),(hBbd t 1).mpr (Or.inr (Or.inr rfl)),hfb (t,1)⟩
  obtain ⟨J,hJ⟩ := unit_disk_square_boundary_homeomorph
  let e : C(Metric.closedBall (0 : Plane) 1,S) := ⟨f ∘ J,f.continuous.comp J.continuous⟩
  refine ⟨e,hf.comp J.isEmbedding,?_,?_⟩
  · change range (f ∘ J)=range d ∪ range H
    rw [J.surjective.range_comp,hfu]
  · change (f ∘ J) '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = _
    rw [image_comp,hJ,hfbd]

end ActualHarerDiskGluing
