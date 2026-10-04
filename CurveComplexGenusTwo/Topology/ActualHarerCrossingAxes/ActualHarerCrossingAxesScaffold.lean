import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerAxisHelpers
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerLinearHelpers

open CurveComplex Set Topology Schoenflies

namespace ActualHarerCornerGeometry

/-- PLAN.md A1: the original opposite-sign packet produces exact axes for
the WHOLE two original arcs, with both original parameter orders retained.
The source can be confined to any supplied smaller open neighborhood. -/
theorem actual_opposite_signed_arc_germs_construct_whole_pair_axis_chart
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (f m : C(Interval, S)) (hf : IsEmbedding f) (hm : IsEmbedding m)
    (s t l h : Interval) (Q : OpenPartialHomeomorph S Plane)
    (ε : ℝ) (U : Set S)
    (hs : s ∈ Ioo (0 : Interval) 1) (ht : t ∈ Ioo (0 : Interval) 1)
    (hcontact : f s = m t) (hls : l < s) (hsh : s < h)
    (hε : ε = (-1 : ℝ) ∨ ε = 1) (hpQ : f s ∈ Q.source)
    (hU : IsOpen U) (hpU : f s ∈ U)
    (hmAxis : ∀ x ∈ Q.source, x ∈ range m ↔ (Q x) 1 = 0)
    (hfWindow : ∀ u ∈ Icc l h, f u ∈ Q.source)
    (hfBefore : ∀ u ∈ Ico l s, ε * (Q (f u)) 1 < 0)
    (hfAfter : ∀ u ∈ Ioc s h, 0 < ε * (Q (f u)) 1) :
    ∃ E : OpenPartialHomeomorph S Plane,
      E.source ⊆ Q.source ∩ U ∧ OrderedWholePairAxes f m s t l h E := by
  classical
  let K := f '' (Ioo l h)ᶜ
  have hK : IsClosed K := (isOpen_Ioo.isClosed_compl.isCompact.image f.continuous).isClosed
  have hpK : f s ∉ K := by
    rintro ⟨u,hu,he⟩
    exact hu ((hf.injective he).symm ▸ ⟨hls,hsh⟩)
  let V := (Q.source ∩ U) \ K
  have hV : IsOpen V := (Q.open_source.inter hU).sdiff hK
  have hpV : f s ∈ V := ⟨⟨hpQ,hpU⟩,hpK⟩
  have hVW : V ⊆ Q.source ∩ U := fun x hx => hx.1
  have hfV (u : Interval) (hu : f u ∈ V) : u ∈ Ioo l h := by
    by_contra hn
    exact hu.2 ⟨u,hn,rfl⟩
  have hcrossOnly (x : S) (hx : x ∈ V) (hxf : x ∈ range f) (hxm : x ∈ range m) :
      x = f s := by
    obtain ⟨u,rfl⟩ := hxf
    have hu := hfV u hx
    have haxis : Q (f u) 1 = 0 := (hmAxis _ hx.1.1).mp hxm
    rcases lt_trichotomy u s with hus | hus | hsu
    · have hh := hfBefore u ⟨hu.1.le,hus⟩
      rw [haxis,mul_zero] at hh
      exact (lt_irrefl 0 hh).elim
    · rw [hus]
    · have hh := hfAfter u ⟨hsu,hu.2.le⟩
      rw [haxis,mul_zero] at hh
      exact (lt_irrefl 0 hh).elim
  let T : Plane ≃ₜ Plane := Homeomorph.addRight (-Q (f s))
  let E := Q.trans T.toOpenPartialHomeomorph
  have hEs : E.source = Q.source := by simp [E]
  have hEp : E (f s) = 0 := by change Q (f s)+ -Q (f s) = 0; abel
  let arcs : Bool → C(Interval,S) := fun j => if j then m else f
  let center : Bool → Interval := fun j => if j then t else s
  have harcs : ∀ j, IsEmbedding (arcs j) := by intro j; cases j <;> assumption
  have hc : ∀ j, center j ∈ Ioo (0:Interval) 1 := by intro j; cases j <;> assumption
  have hp : ∀ j, arcs j (center j) = f s := by
    intro j; cases j
    · rfl
    · exact hcontact.symm
  have hmeet : ∀ i j : Bool, i ≠ j → V ∩ (range (arcs i) ∩ range (arcs j)) ⊆ {f s} := by
    intro i j hij x hx
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hcrossOnly x hx.1 hx.2.1 hx.2.2
    · exact hcrossOnly x hx.1 hx.2.2 hx.2.1
    · exact (hij rfl).elim
  obtain ⟨δ,hδ,hδc,θ,hθ,hθV,R,hRop,hcore,hwindow⟩ :=
    interval_four_arm_radial_core arcs harcs center hc (f s) hp E hEp V hV hpV
      (fun x hx => hEs.symm ▸ hx.1.1) hmeet true
  let moving := R.vector (true,true)
  have hmov : moving ≠ 0 := R.vector_nonzero _
  let L := radialMovingCoordinates moving hmov
  let G := (((E.restr V).trans R.H.toOpenPartialHomeomorph).trans
    (OpenPartialHomeomorph.ofSet (Metric.ball (0:Plane) R.coreRadius) Metric.isOpen_ball)).trans
      L.toOpenPartialHomeomorph
  have hGs : G.source = (E.source ∩ V) ∩ {x | ‖R.H (E x)‖ < R.coreRadius} := by
    ext x
    simp [G,OpenPartialHomeomorph.trans_source,hV.interior_eq,Metric.mem_ball,dist_zero_right]
  have hGval (x : S) : G x = L (R.H (E x)) := rfl
  have hpG : f s ∈ G.source := by
    rw [hGs]
    refine ⟨⟨hEs.symm ▸ hpQ,hpV⟩,?_⟩
    change ‖R.H (E (f s))‖ < R.coreRadius
    rw [hEp,R.fixes_center,norm_zero]
    exact R.core_pos
  have hG0 : G (f s) = (0,0) := by
    rw [hGval,hEp,R.fixes_center]
    exact radialMovingCoordinates_zero moving hmov
  have hGaxis (x : S) (hx : x ∈ G.source) : x ∈ range m ↔ (G x).1 = 0 := by
    have hxx := hGs ▸ hx
    have hh := hcore true x hxx.1.1 hxx.2.le
    change x ∈ range m ↔ R.H (E x) ∈
      segment ℝ (0:Plane) (R.vector (true,false)) ∪ segment ℝ (0:Plane) moving at hh
    have hrel : R.vector (true,false) = -moving := by rw [show moving = R.vector (true,true) from rfl,hRop]; simp
    rw [hrel,union_comm] at hh
    rw [hh,hGval]
    exact radial_axis_segment_iff moving hmov R.coreRadius (R.core_lt_length _) _ hxx.2.le
  let C : Plane ≃ₜ (ℝ × ℝ) := {
    toEquiv := {
      toFun := fun z => (z 1,z 0)
      invFun := fun z => Plane.mk z.2 z.1
      left_inv := by intro z; ext i; fin_cases i <;> rfl
      right_inv := by intro z; rfl }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let P := E.trans C.toOpenPartialHomeomorph
  have hPs : P.source = E.source := by simp [P]
  have hpP : f s ∈ P.source := hPs.symm ▸ hEs.symm ▸ hpQ
  have hP0 : P (f s) = (0,0) := by change C (E (f s)) = _; rw [hEp]; rfl
  have hPaxis (x : S) (hx : x ∈ P.source) : x ∈ range m ↔ (P x).1 = 0 := by
    have hpaxis : Q (f s) 1 = 0 := (hmAxis (f s) hpQ).mp ⟨t,hcontact.symm⟩
    have hv : (P x).1 = Q x 1 := by
      change (Q x+ -Q (f s)) 1 = Q x 1
      simp [hpaxis]
    rw [hv]
    exact hmAxis x (hEs ▸ hPs ▸ hx)
  let A := P.symm.trans G
  have hAs0 : ((0,0):ℝ × ℝ) ∈ A.source := by
    change (0,0) ∈ P.target ∧ P.symm (0,0) ∈ G.source
    rw [← hP0,P.left_inv hpP]
    exact ⟨P.map_source hpP,hpG⟩
  have hA0 : A (0,0) = (0,0) := by
    change G (P.symm (0,0)) = _
    rw [← hP0,P.left_inv hpP,hG0]
    exact hP0.symm
  have hAaxis (z : ℝ × ℝ) (hz : z ∈ A.source) : z.1 = 0 ↔ (A z).1 = 0 := by
    change z ∈ P.target ∧ P.symm z ∈ G.source at hz
    have hPA := hPaxis (P.symm z) (P.map_target hz.1)
    rw [P.right_inv hz.1] at hPA
    exact hPA.symm.trans (hGaxis _ hz.2)
  obtain ⟨ρ,hρ,hρA,η,hη⟩ := CurveComplex.LocalSurgery.local_axis_transition_side_constant A hAs0 hA0 hAaxis
  have hθcont (j : Bool × Bool) : Continuous (θ j) := by
    apply Continuous.subtype_mk
    have he : (fun u : Interval => (θ j u).val) =
        fun u => (center j.1:ℝ)+if j.2 then δ*u.val else -(δ*u.val) := funext (hθ j)
    rw [he]
    split_ifs <;> fun_prop
  have hθzero (j : Bool × Bool) : θ j 0 = center j.1 := by
    apply Subtype.ext
    simp [hθ]
  have hPval (x : S) : (P x).1 = Q x 1 := by
    have hpaxis : Q (f s) 1 = 0 := (hmAxis (f s) hpQ).mp ⟨t,hcontact.symm⟩
    change (Q x+ -Q (f s)) 1 = Q x 1
    simp [hpaxis]
  have hsample (sign : Bool) : ∃ (x : S) (a : ℝ),
      x ∈ G.source ∧ P x ∈ Metric.ball (0,0) ρ ∧
      (if sign then 0 < ε*(P x).1 else ε*(P x).1 < 0) ∧
      0 < a ∧ G x = a • L (R.vector (false,sign)) := by
    let β : Interval → S := fun u => f (θ (false,sign) u)
    have hβ : Continuous β := f.continuous.comp (hθcont _)
    let W := P.source ∩ P ⁻¹' Metric.ball (0,0) ρ
    have hW : IsOpen W := P.isOpen_inter_preimage Metric.isOpen_ball
    have hpW : β 0 ∈ W := by
      change f (θ (false,sign) 0) ∈ W
      rw [hθzero]
      exact ⟨hpP,by change P (f s) ∈ Metric.ball (0,0) ρ; rw [hP0]; exact Metric.mem_ball_self hρ⟩
    obtain ⟨u,hu0,huc,huW⟩ := positive_interval_germ_sample β hβ W hW hpW (R.cut (false,sign)) (R.cut_pos _)
    have huP : β u ∈ P.source := huW.1
    have huBall : P (β u) ∈ Metric.ball (0,0) ρ := huW.2
    have huG : β u ∈ G.source := by
      have hh := (hρA huBall).2
      change P.symm (P (β u)) ∈ G.source at hh
      rwa [P.left_inv huP] at hh
    have hufV : f (θ (false,sign) u) ∈ V := hθV (false,sign) u
    have huWindow := hfV (θ (false,sign) u) hufV
    have hsign : if sign then 0 < ε*(P (β u)).1 else ε*(P (β u)).1 < 0 := by
      rw [hPval]
      cases sign
      · exact hfBefore _ ⟨huWindow.1.le,by
          change (θ (false,false) u).val < s.val
          rw [hθ]; simp only [arcs,center,Bool.false_eq_true,if_false]
          nlinarith⟩
      · exact hfAfter _ ⟨by
          change s.val < (θ (false,true) u).val
          rw [hθ]; simp only [arcs,center,Bool.false_eq_true,if_false,if_true]
          nlinarith,huWindow.2.le⟩
    have hxne : β u ≠ f s := by
      intro he
      have hup := congrArg Subtype.val (hf.injective he)
      rw [hθ] at hup
      cases sign <;> simp only [center,Prod.fst,Bool.false_eq_true,if_false,if_true] at hup <;> nlinarith
    have hray : R.H (E (β u)) ∈ segment ℝ (0:Plane) (R.vector (false,sign)) := by
      have hh : R.H (E (β u)) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix
          (fun j u => E (arcs j.1 (θ j u))) (false,sign) (R.cut (false,sign)) :=
        ⟨E (β u),⟨u,huc.le,rfl⟩,rfl⟩
      simpa only [R.prefix_image,zero_add] using hh
    obtain ⟨a,b,ha,hb,hab,he⟩ := hray
    have heb : R.H (E (β u)) = b • R.vector (false,sign) := by simpa using he.symm
    have hbp : 0 < b := lt_of_le_of_ne hb (by
      intro hbe
      have hz : R.H (E (β u)) = R.H (E (f s)) := by rw [heb,← hbe,zero_smul,hEp,R.fixes_center]
      exact hxne (E.injOn (hEs.symm ▸ hufV.1.1) (hEs.symm ▸ hpQ) (R.H.injective hz)))
    refine ⟨β u,b,huG,huBall,hsign,hbp,?_⟩
    rw [hGval,heb]
    exact radialMovingCoordinates_smul moving hmov b _
  obtain ⟨x₀,a₀,hx₀G,hx₀P,hs₀,ha₀,hx₀⟩ := hsample false
  obtain ⟨x₁,a₁,hx₁G,hx₁P,hs₁,ha₁,hx₁⟩ := hsample true
  change ε*(P x₀).1 < 0 at hs₀
  change 0 < ε*(P x₁).1 at hs₁
  have hPx₀ne : (P x₀).1 ≠ 0 := by intro he; rw [he,mul_zero] at hs₀; exact lt_irrefl 0 hs₀
  have hPx₁ne : (P x₁).1 ≠ 0 := by intro he; rw [he,mul_zero] at hs₁; exact lt_irrefl 0 hs₁
  have hAx (x : S) (hx : x ∈ G.source) : A (P x) = G x := by
    change G (P.symm (P x)) = G x
    rw [P.left_inv (hPs.symm ▸ (hGs ▸ hx).1.1)]
  have hη₀ := hη (P x₀) hx₀P hPx₀ne
  have hη₁ := hη (P x₁) hx₁P hPx₁ne
  rw [hAx x₀ hx₀G] at hη₀
  rw [hAx x₁ hx₁G] at hη₁
  have hUne : (if 0 < (P x₀).1 then (1:ZMod 2) else 0) ≠
      (if 0 < (P x₁).1 then (1:ZMod 2) else 0) := by
    rcases hε with rfl | rfl
    · have hx₀p : 0 < (P x₀).1 := by nlinarith
      have hx₁n : ¬0 < (P x₁).1 := by nlinarith
      simp [hx₀p,hx₁n]
    · have hx₀n : ¬0 < (P x₀).1 := by nlinarith
      have hx₁p : 0 < (P x₁).1 := by nlinarith
      simp [hx₀n,hx₁p]
  have hGne : (if 0 < (G x₀).1 then (1:ZMod 2) else 0) ≠
      (if 0 < (G x₁).1 then (1:ZMod 2) else 0) := by
    rw [hη₀,hη₁]
    exact fun he => hUne (add_right_cancel he)
  have hg₀ne : (G x₀).1 ≠ 0 := by
    intro he
    exact hPx₀ne ((hPaxis x₀ (hPs.symm ▸ (hGs ▸ hx₀G).1.1)).mp ((hGaxis x₀ hx₀G).mpr he))
  have hg₁ne : (G x₁).1 ≠ 0 := by
    intro he
    exact hPx₁ne ((hPaxis x₁ (hPs.symm ▸ (hGs ▸ hx₁G).1.1)).mp ((hGaxis x₁ hx₁G).mpr he))
  have hgOpp : (G x₀).1 * (G x₁).1 < 0 := by
    by_cases h₀ : 0 < (G x₀).1 <;> by_cases h₁ : 0 < (G x₁).1
    · exact False.elim (hGne (by simp [h₀,h₁]))
    · exact mul_neg_of_pos_of_neg h₀ (lt_of_le_of_ne (le_of_not_gt h₁) hg₁ne)
    · exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (le_of_not_gt h₀) hg₀ne) h₁
    · exact False.elim (hGne (by simp [h₀,h₁]))
  have hRayOpp : (L (R.vector (false,false))).1 * (L (R.vector (false,true))).1 < 0 := by
    rw [hx₀,hx₁] at hgOpp
    change (a₀*(L (R.vector (false,false))).1) * (a₁*(L (R.vector (false,true))).1) < 0 at hgOpp
    nlinarith [mul_pos ha₀ ha₁]
  obtain ⟨σ,hσ,hleft,hright⟩ : ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
      σ*(L (R.vector (false,false))).1 < 0 ∧ 0 < σ*(L (R.vector (false,true))).1 := by
    by_cases hp : 0 < (L (R.vector (false,true))).1
    · refine ⟨1,Or.inr rfl,?_,by simpa using hp⟩
      simpa only [one_mul] using (neg_of_mul_neg_left hRayOpp hp.le)
    · have hn : (L (R.vector (false,true))).1 < 0 := by
        have hne : (L (R.vector (false,true))).1 ≠ 0 := by intro he; rw [he,mul_zero] at hRayOpp; linarith
        exact lt_of_le_of_ne (le_of_not_gt hp) hne
      refine ⟨-1,Or.inl rfl,?_,by simpa using neg_pos.mpr hn⟩
      have hleftp := pos_of_mul_neg_left hRayOpp hn.le
      simpa using neg_neg_of_pos hleftp
  let L' := L.trans (horizontalReflection σ hσ)
  let left := L' (R.vector (false,false))
  let right := L' (R.vector (false,true))
  have hleftn : left.1 < 0 := hleft
  have hrightp : 0 < right.1 := hright
  let H := radialHalfplaneShear (right.2/right.1) (left.2/left.1)
  let B := L'.trans H
  have hL'0 : L' 0 = (0,0) := by change horizontalReflection σ hσ (L 0) = _; simp [L]
  have hB0 : B 0 = (0,0) := by change H (L' 0) = _; rw [hL'0]; simp [H]
  have hL'smul (r : ℝ) (z : Plane) : L' (r • z) = r • L' z := by
    change horizontalReflection σ hσ (L (r • z)) = _
    rw [show L (r • z) = r • L z from radialMovingCoordinates_smul moving hmov r z]
    exact horizontalReflection_smul σ hσ r (L z)
  have hBsmul (r : ℝ) (hr : 0 ≤ r) (z : Plane) : B (r • z) = r • B z := by
    change H (L' (r • z)) = _
    rw [hL'smul]
    exact radialHalfplaneShear_smul _ _ r hr (L' z)
  have hBleft : B (R.vector (false,false)) = (left.1,0) := by
    change H left = (left.1,0)
    simpa using radialHalfplaneShear_negative right left hrightp hleftn 1 (by norm_num)
  have hBright : B (R.vector (false,true)) = (right.1,0) := by
    change H right = (right.1,0)
    simpa using radialHalfplaneShear_positive right left hrightp hleftn 1 (by norm_num)
  have hBmoving : B moving = (0,1) := by
    change H (horizontalReflection σ hσ (L moving)) = (0,1)
    rw [show L moving = (0,1) from radialMovingCoordinates_self moving hmov]
    simp [H]
  have hBmovingLeft : B (R.vector (true,false)) = (0,-1) := by
    have he : R.vector (true,false) = (-1:ℝ) • moving := by dsimp [moving]; rw [hRop]; simp
    change H (L' (R.vector (true,false))) = _
    rw [he,hL'smul]
    have hL'm : L' moving = (0,1) := by
      change horizontalReflection σ hσ (L moving) = _
      rw [show L moving = (0,1) from radialMovingCoordinates_self moving hmov]
      simp
    rw [hL'm]
    have heq : (-1:ℝ) • ((0,1):ℝ × ℝ) = (0,-1) := by ext <;> norm_num
    rw [heq]
    simp [H]
  let J := ((E.restr V).trans R.H.toOpenPartialHomeomorph).trans B.toOpenPartialHomeomorph
  let F := J.restr G.source
  have hFs : F.source = G.source := by
    simp only [F,OpenPartialHomeomorph.restr_source,G.open_source.interior_eq]
    have hJs : J.source = E.source ∩ V := by simp [J,hV.interior_eq]
    rw [hJs]
    exact inter_eq_right.mpr (by intro x hx; exact (hGs ▸ hx).1)
  have hFval (x : S) : F x = B (R.H (E x)) := rfl
  have hpF : f s ∈ F.source := hFs.symm ▸ hpG
  have hF0 : F (f s) = (0,0) := by rw [hFval,hEp,R.fixes_center,hB0]
  have hFanchor (x : S) (hx : x ∈ F.source) : x ∈ range f ↔ (F x).2 = 0 := by
    have hxx := hGs ▸ hFs ▸ hx
    have hh := hcore false x hxx.1.1 hxx.2.le
    change x ∈ range f ↔ R.H (E x) ∈
      segment ℝ (0:Plane) (R.vector (false,false)) ∪ segment ℝ (0:Plane) (R.vector (false,true)) at hh
    rw [hh,mem_union,
      axis_ray_membership B hB0 hBsmul _ _ left.1 (ne_of_lt hleftn) hBleft
        (hxx.2.trans (R.core_lt_length _)),
      axis_ray_membership B hB0 hBsmul _ _ right.1 (ne_of_gt hrightp) hBright
        (hxx.2.trans (R.core_lt_length _))]
    change ((F x).2 = 0 ∧ 0 ≤ (F x).1/left.1) ∨
      ((F x).2 = 0 ∧ 0 ≤ (F x).1/right.1) ↔ (F x).2 = 0
    constructor
    · exact fun hh => hh.elim And.left And.left
    · intro hy
      rcases le_total (F x).1 0 with hn|hp
      · exact Or.inl ⟨hy,div_nonneg_of_nonpos hn hleftn.le⟩
      · exact Or.inr ⟨hy,div_nonneg hp hrightp.le⟩
  have hFmoving (x : S) (hx : x ∈ F.source) : x ∈ range m ↔ (F x).1 = 0 := by
    have hh := hGaxis x (hFs ▸ hx)
    have hfv : (F x).1 = σ*(G x).1 := rfl
    rw [hfv]
    rcases hσ with hσ|hσ <;> simp [hσ,hh]
  have hRayData (j sign : Bool) (u : Interval) (hu : arcs j u ∈ F.source)
      (hray : R.H (E (arcs j u)) ∈ segment ℝ (0:Plane) (R.vector (j,sign))) :
      ∃ a : ℝ, 0 ≤ a ∧ F (arcs j u) = a • B (R.vector (j,sign)) ∧
        (if sign then center j ≤ u else u ≤ center j) := by
    have huE : arcs j u ∈ E.source := (hGs ▸ hFs ▸ hu).1.1
    have hpre : R.H (E (arcs j u)) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix
        (fun j u => E (arcs j.1 (θ j u))) (j,sign) (R.cut (j,sign)) := by
      rw [R.prefix_image,zero_add]
      exact hray
    obtain ⟨z,⟨w,hw,rfl⟩,he⟩ := hpre
    have hθw : θ (j,sign) w = u :=
      (harcs j).injective (E.injOn (hEs.symm ▸ (hθV (j,sign) w).1.1) huE (R.H.injective he))
    have horder : if sign then center j ≤ u else u ≤ center j := by
      have hh := hθ (j,sign) w
      rw [hθw] at hh
      cases sign <;> simp only [if_false,if_true,Bool.false_eq_true] at *
      · change u.val ≤ (center j).val
        nlinarith [w.property.1]
      · change (center j).val ≤ u.val
        nlinarith [w.property.1]
    obtain ⟨a,b,ha,hb,hab,hbz⟩ := hray
    have hbz' : R.H (E (arcs j u)) = b • R.vector (j,sign) := by simpa using hbz.symm
    refine ⟨b,hb,?_,horder⟩
    rw [hFval,hbz',hBsmul b hb]
  have hFanchorOrder (u : Interval) (hu : f u ∈ F.source) :
      u ∈ Ioo l h ∧ ((F (f u)).1 < 0 ↔ u < s) ∧ (0 < (F (f u)).1 ↔ s < u) := by
    have hxx := hGs ▸ hFs ▸ hu
    refine ⟨hfV u hxx.1.2,?_⟩
    have hz : (F (f u)).1 = 0 ↔ u = s := by
      constructor
      · intro hx
        have he : F (f u) = F (f s) := by
          rw [hF0]
          apply Prod.ext
          · exact hx
          · exact (hFanchor _ hu).mp (mem_range_self u)
        exact hf.injective (F.injOn hu hpF he)
      · intro he; rw [he,hF0]
    apply ordered_ray_signs u s (F (f u)).1 hz
    rcases (hcore false (f u) hxx.1.1 hxx.2.le).mp (mem_range_self u) with hl|hr
    · obtain ⟨a,ha,he,hsu⟩ := hRayData false false u hu hl
      left
      refine ⟨?_,hsu⟩
      change (F (f u)).1 ≤ 0
      change F (f u) = a • B (R.vector (false,false)) at he
      rw [he,hBleft]
      exact mul_nonpos_of_nonneg_of_nonpos ha hleftn.le
    · obtain ⟨a,ha,he,hsu⟩ := hRayData false true u hu hr
      right
      refine ⟨?_,hsu⟩
      change 0 ≤ (F (f u)).1
      change F (f u) = a • B (R.vector (false,true)) at he
      rw [he,hBright]
      exact mul_nonneg ha hrightp.le
  have hpFm : m t ∈ F.source := hcontact ▸ hpF
  have hF0m : F (m t) = (0,0) := by rw [← hcontact,hF0]
  have hFmovingOrder (u : Interval) (hu : m u ∈ F.source) :
      ((F (m u)).2 < 0 ↔ u < t) ∧ (0 < (F (m u)).2 ↔ t < u) := by
    have hxx := hGs ▸ hFs ▸ hu
    have hz : (F (m u)).2 = 0 ↔ u = t := by
      constructor
      · intro hy
        have he : F (m u) = F (m t) := by
          rw [hF0m]
          apply Prod.ext
          · exact (hFmoving _ hu).mp (mem_range_self u)
          · exact hy
        exact hm.injective (F.injOn hu hpFm he)
      · intro he; rw [he,hF0m]
    apply ordered_ray_signs u t (F (m u)).2 hz
    rcases (hcore true (m u) hxx.1.1 hxx.2.le).mp (mem_range_self u) with hl|hr
    · obtain ⟨a,ha,he,hsu⟩ := hRayData true false u hu hl
      left
      refine ⟨?_,hsu⟩
      change (F (m u)).2 ≤ 0
      change F (m u) = a • B (R.vector (true,false)) at he
      rw [he,hBmovingLeft]
      change a*(-1) ≤ 0
      linarith
    · obtain ⟨a,ha,he,hsu⟩ := hRayData true true u hu hr
      right
      refine ⟨?_,hsu⟩
      change 0 ≤ (F (m u)).2
      change F (m u) = a • B moving at he
      rw [he,hBmoving]
      simpa using ha
  obtain ⟨O,c,hc,hOs,hSquare,hO0,hcoord⟩ :=
    CurveComplex.source_crossing_chart_unit_square F (f s) hpF hF0
  have hOsrc : O.source ⊆ Q.source ∩ U := by
    intro x hx
    exact (hGs ▸ hFs ▸ hOs ▸ hx).1.2.1
  refine ⟨O,hOsrc,⟨hOs.symm ▸ hpF,hO0,hSquare,?_,?_,?_,?_⟩⟩
  · intro x hx
    rw [(hcoord x).2,div_eq_zero_iff]
    simpa [ne_of_gt hc] using hFanchor x (hOs ▸ hx)
  · intro x hx
    rw [(hcoord x).1,div_eq_zero_iff]
    simpa [ne_of_gt hc] using hFmoving x (hOs ▸ hx)
  · intro u hu
    have hh := hFanchorOrder u (hOs ▸ hu)
    rw [(hcoord (f u)).1]
    simpa only [div_lt_iff₀ hc,lt_div_iff₀ hc,zero_mul] using hh
  · intro u hu
    have hh := hFmovingOrder u (hOs ▸ hu)
    rw [(hcoord (m u)).2]
    simpa only [div_lt_iff₀ hc,lt_div_iff₀ hc,zero_mul] using hh

end ActualHarerCornerGeometry
