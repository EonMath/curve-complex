import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualConvexMovieEndpointCompletion
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourPathCellContactBoundaryDegreeFamily
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual compatible edge movies with finite final contacts construct a whole
cell movie from the original filling to a finite proper contact family. Neither
an interior homotopy nor a selected contact family is supplied. -/
theorem actual_four_edge_finite_contact_boundary_degree_cell_movie
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (original : C(Interval × Interval,V))
    (bottom right top left : C(Interval × Interval,V))
    (hb : ∀ σ,bottom (σ,0)=original (0,0) ∧ bottom (σ,1)=original (1,0))
    (hr : ∀ σ,right (σ,0)=original (1,0) ∧ right (σ,1)=original (1,1))
    (ht : ∀ σ,top (σ,0)=original (0,1) ∧ top (σ,1)=original (1,1))
    (hl : ∀ σ,left (σ,0)=original (0,0) ∧ left (σ,1)=original (0,1))
    (hstart : ∀ t,bottom (0,t)=original (t,0) ∧ right (0,t)=original (1,t) ∧
      top (0,t)=original (t,1) ∧ left (0,t)=original (0,t))
    (hbottom : {t : Interval | (bottom (1,t)).val.2=0}.Finite)
    (hright : {t : Interval | (right (1,t)).val.2=0}.Finite)
    (htop : {t : Interval | (top (1,t)).val.2=0}.Finite)
    (hleft : {t : Interval | (left (1,t)).val.2=0}.Finite)
    (center : V) (hc : center.val.2≠0) :
    ∃ G : C(Interval × Interval,V),∃ H : original.Homotopy G,
    ∃ middle : C((Interval × Interval) × Interval,V),
    ∃ first : original.Homotopy
        (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,V)),
    ∃ mid : (⟨fun z => middle (z,0),by fun_prop⟩ : C(Interval × Interval,V)).Homotopy
        (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,V)),
    ∃ last : (⟨fun z => middle (z,1),by fun_prop⟩ : C(Interval × Interval,V)).Homotopy G,
      H=(first.trans mid).trans last ∧
      (∀ σ z,mid (σ,z)=middle (z,σ)) ∧
      (∀ σ t,middle ((t,0),σ)=bottom (σ,t) ∧
        middle ((1,t),σ)=right (σ,t) ∧ middle ((t,1),σ)=top (σ,t) ∧
        middle ((0,t),σ)=left (σ,t)) ∧
      (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → first (σ,z)=original z) ∧
      (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → last (σ,z)=G z) ∧
    ∃ vertices : Finset (Interval × Interval),
    ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
      (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
      (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
      (∀ e,IsEmbedding (arc e)) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
      (∀ z,(G z).val.2=0 ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) ∧
      (∀ v : ↑vertices,0<v.val.1.val → v.val.1.val < 1 →
        0<v.val.2.val → v.val.2.val < 1 →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2) ∧
      (∀ (i : Fin 4) (u : Interval),0<u.val → u.val < 1 →
        (G (actualLiteralCellSide i u)).val.2=0 →
        ∀ δ : ℝ,0<δ →
        (∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
          (G (actualLiteralCellSide i v)).val.2/center.val.2≠0 ∧
          (G (actualLiteralCellSide i w)).val.2/center.val.2≠0 ∧
          ((0<(G (actualLiteralCellSide i v)).val.2/center.val.2) ↔
            ¬(0<(G (actualLiteralCellSide i w)).val.2/center.val.2))) →
        {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1) := by
  let pb : Path (original (0,0)) (original (1,0)) :=
    ⟨⟨fun t => bottom (1,t),by fun_prop⟩,(hb 1).1,(hb 1).2⟩
  let pr : Path (original (1,0)) (original (1,1)) :=
    ⟨⟨fun t => right (1,t),by fun_prop⟩,(hr 1).1,(hr 1).2⟩
  let pt : Path (original (0,1)) (original (1,1)) :=
    ⟨⟨fun t => top (1,t),by fun_prop⟩,(ht 1).1,(ht 1).2⟩
  let pl : Path (original (0,0)) (original (0,1)) :=
    ⟨⟨fun t => left (1,t),by fun_prop⟩,(hl 1).1,(hl 1).2⟩
  obtain ⟨G,hSides,vertices,A,hA,arc,hends,hcollision,hclear,hembed,hinterior,hcoverage,hdegree,hboundaryDegree⟩ :=
    actual_four_path_cell_contact_boundary_degree_family V hV pb pr pt pl
      hbottom hright htop hleft center hc
  obtain ⟨middle,hMiddle⟩ := actual_four_edge_joint_convex_cell_extension V hV
    (original (0,0)) (original (1,0)) (original (0,1)) (original (1,1))
    bottom right top left hb hr ht hl (ContinuousMap.const Interval center)
  obtain ⟨first,mid,last,H,hH,hmid,hfirst,hlast⟩ :=
    actual_convex_movie_endpoint_completion V hV original G middle
  have h0 (z : Interval × Interval) (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      middle (z,0)=original z := by
    rcases hz with h | h | h | h
    · rw [show z=(0,z.2) from Prod.ext h rfl]
      exact ((hMiddle 0 z.2).2.2.2).trans (hstart z.2).2.2.2
    · rw [show z=(1,z.2) from Prod.ext h rfl]
      exact ((hMiddle 0 z.2).2.1).trans (hstart z.2).2.1
    · rw [show z=(z.1,0) from Prod.ext rfl h]
      exact ((hMiddle 0 z.1).1).trans (hstart z.1).1
    · rw [show z=(z.1,1) from Prod.ext rfl h]
      exact ((hMiddle 0 z.1).2.2.1).trans (hstart z.1).2.2.1
  have h1 (z : Interval × Interval) (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      middle (z,1)=G z := by
    rcases hz with h | h | h | h
    · rw [show z=(0,z.2) from Prod.ext h rfl]
      exact ((hMiddle 1 z.2).2.2.2).trans ((hSides z.2).2.2.2).symm
    · rw [show z=(1,z.2) from Prod.ext h rfl]
      exact ((hMiddle 1 z.2).2.1).trans ((hSides z.2).2.1).symm
    · rw [show z=(z.1,0) from Prod.ext rfl h]
      exact ((hMiddle 1 z.1).1).trans ((hSides z.1).1).symm
    · rw [show z=(z.1,1) from Prod.ext rfl h]
      exact ((hMiddle 1 z.1).2.2.1).trans ((hSides z.1).2.2.1).symm
  exact ⟨G,H,middle,first,mid,last,hH,hmid,hMiddle,
    fun σ z hz => hfirst σ z (h0 z hz),fun σ z hz => hlast σ z (h1 z hz),
    vertices,A,hA,arc,hends,hcollision,hclear,hembed,hinterior,hcoverage,hdegree,hboundaryDegree⟩
end CurveComplex.HyperellipticModel
