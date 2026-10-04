import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualMarkedContactSectorEmbeddedSide
import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualOneCornerSquareBoundaryHomotopy
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual filled contact sector produces a one-corner punctured boundary word with an embedded old-loop terminal side. -/
theorem actual_marked_contact_sector_embedded_boundary_word
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (U : Set S) (V : Set Plane) (e : U ≃ₜ V)
    (hmarks : Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}))
    (haxis : ∀ q : U,q.val ∈ a.val.image ↔ (e q).val 1=0)
    (hp : a.val.map 0 ∈ U) (hezero : (e ⟨a.val.map 0,hp⟩).val=0)
    (F : C(unitInterval × Icc (0:ℝ) (1/2),S))
    (hFU : ∀ z,F z ∈ U)
    (hbase : ∀ σ,F (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0)
    (hpositive : ∀ z,0<z.2.val → F z ∉ (M.cover.branch : Set S))
    (hold : ∀ t,F (1,t) ∈ a.val.image) :
    ∃ Q : C(unitInterval × Icc (0:ℝ) (1/2),S),
      (∀ t,Q (0,t)=F (0,t)) ∧
      (∀ σ,Q (σ,⟨0,le_rfl,by norm_num⟩)=a.val.map 0) ∧
      (∀ z,Q z ∈ U) ∧
      (∀ z,0<z.2.val → Q z ∉ (M.cover.branch : Set S)) ∧
      (∀ t,Q (1,t) ∈ a.val.image) ∧ IsEmbedding (fun t => Q (1,t)) ∧
      (∀ t,Q (1,t) ∈ range (fun u => F (1,u))) ∧
      Q (1,⟨1/2,by norm_num,le_rfl⟩)=F (1,⟨1/2,by norm_num,le_rfl⟩) ∧
    ∃ H : C(unitInterval × unitInterval,S),
      (∀ z,H z=Q (z.1,⟨(z.2:ℝ)/2,
        div_nonneg z.2.property.1 (by norm_num),
        div_le_div_of_nonneg_right z.2.property.2 (by norm_num : (0:ℝ)≤2)⟩)) ∧
      (∀ t,H (1,t) ∈ a.val.image) ∧ IsEmbedding (fun t => H (1,t)) ∧
      (∀ σ,H (σ,0)=a.val.map 0) ∧
    ∃ h00 : H (0,0) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ,
    ∃ h01 : H (0,1) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ,
    ∃ h10 : H (1,0) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ,
    ∃ h11 : H (1,1) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ,
    ∃ bottom : Path (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S) \ {a.val.map 0})ᶜ) ⟨H (0,1),h01⟩,
    ∃ right : Path (⟨H (0,1),h01⟩ : ↑((M.cover.branch : Set S) \ {a.val.map 0})ᶜ) ⟨H (1,1),h11⟩,
    ∃ left : Path (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S) \ {a.val.map 0})ᶜ) ⟨H (1,0),h10⟩,
    ∃ top : Path (⟨H (1,0),h10⟩ : ↑((M.cover.branch : Set S) \ {a.val.map 0})ᶜ) ⟨H (1,1),h11⟩,
      (∀ t,(bottom t:S)=H (0,t)) ∧ (∀ t,(right t:S)=H (t,1)) ∧
      (∀ t,(left t:S)=H (t,0)) ∧ (∀ t,(top t:S)=H (1,t)) ∧
      (bottom.trans right).Homotopic (left.trans top) := by
  obtain ⟨Q,hQ0,hQbase,hQU,hQmarks,hQold,hQembed,hQrange,hQend⟩ :=
    actual_marked_contact_sector_embedded_side M a U V e hmarks haxis hp hezero
      F hFU hbase hpositive hold
  let param : C(unitInterval,Icc (0:ℝ) (1/2)) :=
    ⟨fun t => ⟨(t:ℝ)/2,div_nonneg t.property.1 (by norm_num),
      div_le_div_of_nonneg_right t.property.2 (by norm_num : (0:ℝ)≤2)⟩,by fun_prop⟩
  have hpi : Function.Injective param := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change (t:ℝ)/2=(u:ℝ)/2 at hh
    linarith only [hh]
  have hpe : IsEmbedding param := (param.continuous.isClosedEmbedding hpi).isEmbedding
  let H : C(unitInterval × unitInterval,S) := ⟨fun z => Q (z.1,param z.2),by fun_prop⟩
  have hHmarks (z) : H z ∉ ((M.cover.branch : Set S) \ {a.val.map 0}) :=
    Set.disjoint_left.mp hmarks (hQU (z.1,param z.2))
  obtain ⟨h00,h01,h10,h11,bottom,right,left,top,hbottom,hright,hleft,htop,hh⟩ :=
    actual_one_corner_square_boundary_homotopy M (a.val.map 0) H hHmarks
  refine ⟨Q,hQ0,hQbase,hQU,hQmarks,hQold,hQembed,hQrange,hQend,H,
    (fun _ => rfl),(fun t => hQold (param t)),hQembed.comp hpe,?_,
    h00,h01,h10,h11,bottom,right,left,top,hbottom,hright,hleft,htop,hh⟩
  intro σ
  have he : param 0=⟨0,le_rfl,by norm_num⟩ := Subtype.ext (by simp [param])
  change Q (σ,param 0)=a.val.map 0
  rw [he]
  exact hQbase σ
end CurveComplex.HyperellipticModel
