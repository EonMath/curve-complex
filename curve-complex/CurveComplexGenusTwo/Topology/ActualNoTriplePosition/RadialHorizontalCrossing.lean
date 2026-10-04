import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedAffineCrossingDisk
import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.PlanarFanBend

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

theorem crossesSymm (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M) (p : S)
    (hc : CrossesInDisk M a b p) : CrossesInDisk M b a p := by
  obtain ⟨U,hU,hp,hmark,e,he0,ha,hb⟩ := hc
  let Q := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
  let swap : Q ≃ₜ Q := (Homeomorph.prodComm ℝ ℝ).subtype (fun _ => and_comm)
  refine ⟨U,hU,hp,hmark,e.trans swap,?_,?_,?_⟩
  · change ((e ⟨p,hp⟩).val.2,(e ⟨p,hp⟩).val.1)=(0,0)
    rw [he0]
  · exact hb
  · exact ha

private theorem positiveRadialGraph (a b z : Plane) (ha : 0 < a 1) (hb : b 1 < 0)
      (hz : 0 < z 1) (hzn : ‖z‖ < ‖a‖) :
      (z ∈ segment ℝ (0:Plane) a ∪ segment ℝ (0:Plane) b) ↔ z 0=(a 0/a 1)*z 1 := by
    have ha0 : a 1 ≠ 0 := ne_of_gt ha
    constructor
    · intro hseg
      rcases hseg with hseg|hseg
      · rw [segment_eq_image'] at hseg
        obtain ⟨t,ht,he⟩ := hseg
        have h0 := congrArg (fun z : Plane => z 0) he
        have h1 := congrArg (fun z : Plane => z 1) he
        change 0+t*(a 0-0)=z 0 at h0
        change 0+t*(a 1-0)=z 1 at h1
        rw [← h0,← h1]
        field_simp
        ring
      · rw [segment_eq_image'] at hseg
        obtain ⟨t,ht,he⟩ := hseg
        have h1 := congrArg (fun z : Plane => z 1) he
        change 0+t*(b 1-0)=z 1 at h1
        have hle := mul_nonpos_of_nonneg_of_nonpos ht.1 hb.le
        nlinarith
    · intro hgraph
      let t := z 1/a 1
      have ht : 0 < t := div_pos hz ha
      have hvec : z=t • a := by
        ext i
        fin_cases i
        · change z 0=t*a 0
          rw [hgraph]
          dsimp [t]
          ring
        · change z 1=t*a 1
          dsimp [t]
          rw [div_mul_cancel₀ _ ha0]
      have han : 0 < ‖a‖ := norm_pos_iff.mpr (fun he => by
        have hh := congrArg (fun z : Plane => z 1) he
        change a 1=0 at hh
        linarith)
      have ht1 : t < 1 := by
        rw [hvec,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hzn
        nlinarith
      left
      rw [segment_eq_image']
      refine ⟨t,⟨ht.le,ht1.le⟩,?_⟩
      rw [hvec]
      ext i
      simp
private theorem markedRadialHorizontalTransverse
      (M : HyperellipticModel E S)
      (d c : EssentialMarkedArc M) (F : OpenPartialHomeomorph S Plane)
      (p : S) (hpF : p ∈ F.source) (hmark : Disjoint F.source (M.cover.branch : Set S))
      (a b : Plane) (ha : 0 < a 1) (hb : b 1 < 0) (h : ℝ) (hh : 0 < h)
      (hpy : F p 1=h) (hpn : ‖F p‖ < ‖a‖)
      (hOld : ∀ x ∈ F.source, x ∈ d.val.image ↔ F x ∈
        segment ℝ (0:Plane) a ∪ segment ℝ (0:Plane) b)
      (hNew : ∀ x ∈ F.source, x ∈ c.val.image ↔ F x 1=h)
      (hpd : p ∈ d.val.image) : CrossesInDisk M c d p := by
    let O : Set S := F.source ∩ F ⁻¹' (Metric.ball (0:Plane) ‖a‖ ∩ {z : Plane | 0 < z 1})
    have hO : IsOpen O := F.isOpen_inter_preimage
      (isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
    have hpO : p ∈ O := ⟨hpF,by simpa [Metric.mem_ball,dist_zero_right] using hpn,by change 0 < F p 1; rw [hpy]; exact hh⟩
    let Q := F.restrOpen O hO
    have hQs : Q.source=F.source ∩ O := rfl
    have hpQ : p ∈ Q.source := ⟨hpF,hpO⟩
    have hQold (x : S) (hx : x ∈ Q.source) : x ∈ d.val.image ↔ F x 0=(a 0/a 1)*F x 1 := by
      rw [hOld x hx.1]
      exact positiveRadialGraph a b (F x) ha hb hx.2.2.2
        (by simpa [Metric.mem_ball,dist_zero_right] using hx.2.2.1)
    let k := a 0/a 1
    let shear : Plane ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk (z 0-k*z 1) (z 1)
        invFun := fun z => Plane.mk (z 0+k*z 1) (z 1)
        left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk] <;> ring
        right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk] <;> ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let E0 := Q.transHomeomorph shear
    have hEs : E0.source=Q.source := rfl
    have hE0 (x : S) : E0 x 0=F x 0-k*F x 1 := rfl
    have hE1 (x : S) : E0 x 1=F x 1 := rfl
    have hp0 : E0 p 0=0 := by
      rw [hE0]
      exact sub_eq_zero.mpr ((hQold p hpQ).mp hpd)
    apply crossesSymm
    apply actual_affine_graph_crosses_in_disk M d c E0 p hpQ
      (hmark.mono_left (fun x hx => hx.1)) hp0 0
    · intro x hx
      rw [hE0,sub_eq_zero]
      exact hQold x hx
    · intro x hx
      rw [hE1,hE1,hpy,zero_mul,add_zero]
      exact hNew x hx.1

theorem unit_bend_flat_strip_iff (δ : ℝ) (z : Plane)
    (hx : |z 0| < (1 / 2 : ℝ)) :
    z ∈ bendGraph (1 / 2) 1 δ ↔ z 1 = δ := by
  have hheight : bendHeight (1 / 2) 1 (z 0) = 1 :=
    bendHeight_middle (by norm_num) hx.le
  constructor
  · rintro ⟨x,hxI,hz⟩
    have hxeq : x = z 0 := by
      have h := congrArg (fun y : Plane => y 0) hz
      simpa [Plane.mk] using h
    have hy := congrArg (fun y : Plane => y 1) hz
    change δ * bendHeight (1 / 2) 1 x = z 1 at hy
    rw [hxeq,hheight,mul_one] at hy
    exact hy.symm
  · intro hy
    refine ⟨z 0,⟨?_,?_⟩,?_⟩
    · linarith [abs_lt.mp hx]
    · linarith [abs_lt.mp hx]
    ext i
    fin_cases i
    · rfl
    · change δ * bendHeight (1 / 2) 1 (z 0) = z 1
      rw [hheight, mul_one]
      exact hy.symm

theorem upper_ray_contact_norm_lt (v : Plane) (hv : 0 < v 1)
    (δ : ℝ) (hδ : 0 < δ) (hinside : δ < v 1) :
    ‖Plane.mk (δ * v 0 / v 1) δ‖ < ‖v‖ := by
  have he : Plane.mk (δ * v 0 / v 1) δ = (δ / v 1) • v := by
    ext i
    fin_cases i
    · change δ * v 0 / v 1 = (δ / v 1) * v 0
      ring
    · change δ = (δ / v 1) * v 1
      field_simp [ne_of_gt hv]
  have hratio : 0 < δ / v 1 := div_pos hδ hv
  have hratio1 : δ / v 1 < 1 := (div_lt_iff₀ hv).2 (by simpa using hinside)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr (by
    intro he0
    have h := congrArg (fun z : Plane => z 1) he0
    change v 1 = 0 at h
    linarith)
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hratio]
  nlinarith

theorem actual_unit_bend_new_contact_transverse
    (M : HyperellipticModel E S) (c d b : EssentialMarkedArc M)
    (F : OpenPartialHomeomorph S Plane) (q : S)
    (hmarks : Disjoint F.source (M.cover.branch : Set S))
    (hqF : q ∈ F.source)
    (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hqx : |F q 0| < (1 / 2 : ℝ))
    (hqy : F q 1 = δ) (hqy1 : F q 1 < 1)
    (hqn : ‖F q‖ < ‖v‖)
    (haxis : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ c.val.image ↔ F x 1 = 0))
    (hmodel : ∀ x ∈ F.source, F x ∈ Plane.closedSquare 0 1 →
      (x ∈ b.val.image ↔ F x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w))
    (himage : d.val.image =
      (c.val.image \
        {x : S | x ∈ F.source ∧ F x ∈
          segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)}) ∪
        {x : S | x ∈ F.source ∧ F x ∈ bendGraph (1 / 2) 1 δ})
    (hqb : q ∈ b.val.image) : CrossesInDisk M d b q := by
  let D : Set Plane := {z | |z 0| < (1 / 2 : ℝ) ∧
    0 < z 1 ∧ z 1 < 1 ∧ ‖z‖ < ‖v‖}
  have hD : IsOpen D := by
    dsimp [D]
    have hc0 : Continuous (fun z : Plane => z 0) := by fun_prop
    have hc1 : Continuous (fun z : Plane => z 1) := by fun_prop
    have hcn : Continuous (fun z : Plane => ‖z‖) := by fun_prop
    simpa only [Set.setOf_and, Set.inter_assoc] using
      ((isOpen_lt hc0.abs (continuous_const : Continuous (fun _ : Plane => (1 / 2 : ℝ)))).inter
        (isOpen_lt (continuous_const : Continuous (fun _ : Plane => (0 : ℝ))) hc1)).inter
        ((isOpen_lt hc1 (continuous_const : Continuous (fun _ : Plane => (1 : ℝ)))).inter
          (isOpen_lt hcn (continuous_const : Continuous (fun _ : Plane => ‖v‖))))
  have hqD : F q ∈ D := ⟨hqx,by rw [hqy]; exact hδ,hqy1,hqn⟩
  let O : Set S := F.source ∩ F ⁻¹' D
  have hO : IsOpen O := F.isOpen_inter_preimage hD
  let G := F.restrOpen O hO
  have hGsource : G.source = F.source ∩ O := rfl
  have hqG : q ∈ G.source := ⟨hqF,hqF,hqD⟩
  have hGinF (x : S) (hx : x ∈ G.source) : x ∈ F.source := hx.1
  have hGinD (x : S) (hx : x ∈ G.source) : F x ∈ D := hx.2.2
  have hDsq (z : Plane) (hz : z ∈ D) : z ∈ Plane.closedSquare 0 1 := by
    rw [Schoenflies.mem_closedSquare_zero_one]
    change max |z 0| |z 1| ≤ 1
    exact max_le (by linarith [hz.1])
      (abs_le.mpr ⟨by linarith [hz.2.1],by linarith [hz.2.2.1]⟩)
  have hGold (x : S) (hx : x ∈ G.source) :
      x ∈ b.val.image ↔ G x ∈ segment ℝ (0 : Plane) v ∪
        segment ℝ (0 : Plane) w := by
    exact hmodel x (hGinF x hx) (hDsq (F x) (hGinD x hx))
  have hGnew (x : S) (hx : x ∈ G.source) :
      x ∈ d.val.image ↔ G x 1 = δ := by
    rw [himage]
    have hxD := hGinD x hx
    have hxc : x ∉ c.val.image := by
      intro hxc
      have hzero := (haxis x (hGinF x hx) (hDsq (F x) hxD)).mp hxc
      linarith [hxD.2.1]
    have hxB := unit_bend_flat_strip_iff δ (F x) hxD.1
    simp only [Set.mem_union,Set.mem_diff,Set.mem_setOf_eq]
    constructor
    · rintro (⟨hc,_⟩ | ⟨_,hB⟩)
      · exact False.elim (hxc hc)
      · exact hxB.mp hB
    · intro hy
      exact Or.inr ⟨hGinF x hx,hxB.mpr hy⟩
  exact markedRadialHorizontalTransverse M b d G q hqG
    (hmarks.mono_left (fun x hx => hx.1)) v w hv hw δ hδ
    hqy hqn hGold hGnew hqb

end
end CurveComplex.HyperellipticModel.ArcSurgery

#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_unit_bend_new_contact_transverse
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.upper_ray_contact_norm_lt
