import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualMarkedContactTraceChartStraightening
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual contact ray straightening produces an embedded original-loop side. -/
theorem actual_marked_contact_trace_embedded_straightening
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (hp : a.val.map 0 ∈ U) (hezero : (e ⟨a.val.map 0,hp⟩).val=0)
    (T : C(Icc (0:ℝ) (1/2),S)) (hTU : ∀ t,T t ∈ U)
    (hTzero : T ⟨0,le_rfl,by norm_num⟩=a.val.map 0)
    (hTold : ∀ t,T t ∈ a.val.image)
    (hTnz : ∀ t,0<t.val → T t≠a.val.map 0) :
    ∃ F : C(unitInterval × Icc (0:ℝ) (1/2),S),
      (∀ t,F (0,t)=T t) ∧
      (∀ σ,F (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0) ∧
      (∀ σ,F (σ,⟨1/2,by norm_num,le_rfl⟩)=T ⟨1/2,by norm_num,le_rfl⟩) ∧
      (∀ z,F z ∈ range T) ∧ (∀ z,F z ∈ a.val.image) ∧
      (∀ z,0<z.2.val → F z ∉ (M.cover.branch : Set S)) ∧
      (∀ t (h : F (1,t) ∈ U),(e ⟨F (1,t),h⟩).val=
        (2*t.val) • (e ⟨T ⟨1/2,by norm_num,le_rfl⟩,hTU _⟩).val) ∧ IsEmbedding (fun t => F (1,t)) := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨F,hF0,hFbase,hFend,hFrange,hFold,hFmarks,hFcoord⟩ :=
    actual_marked_contact_trace_chart_straightening M a U V e hmarks haxis hp hezero
      T hTU hTzero hTold hTnz
  let q : Icc (0:ℝ) (1/2) := ⟨1/2,by norm_num,le_rfl⟩
  have hQ : (e ⟨T q,hTU q⟩).val≠0 := by
    intro hz
    have he : e ⟨T q,hTU q⟩=e ⟨a.val.map 0,hp⟩ := Subtype.ext (hz.trans hezero.symm)
    exact hTnz q (by norm_num [q]) (congrArg Subtype.val (e.injective he))
  have hFU (z) : F z ∈ U := by
    obtain ⟨t,ht⟩ := hFrange z
    exact ht ▸ hTU t
  have hi : Function.Injective (fun t => F (1,t)) := by
    intro t u he
    have hh : (2*t.val) • (e ⟨T q,hTU q⟩).val=
        (2*u.val) • (e ⟨T q,hTU q⟩).val := by
      calc
        _ = (e ⟨F (1,t),hFU (1,t)⟩).val := (hFcoord t (hFU (1,t))).symm
        _ = (e ⟨F (1,u),hFU (1,u)⟩).val :=
          congrArg (fun x : U => (e x).val) (Subtype.ext he)
        _ = _ := hFcoord u (hFU (1,u))
    have hs := smul_left_injective ℝ hQ hh
    apply Subtype.ext
    linarith only [hs]
  have hc : Continuous (fun t => F (1,t)) := by fun_prop
  exact ⟨F,hF0,hFbase,hFend,hFrange,hFold,hFmarks,hFcoord,
    (hc.isClosedEmbedding hi).isEmbedding⟩
end CurveComplex.HyperellipticModel
