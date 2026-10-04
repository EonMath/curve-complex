import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.FanConeClearance
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.SelectedSideFanGerm
namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

theorem actual_marked_corner_cone_from_selected_side_germ
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (old : J → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hOld : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
    (hab : (crossings M a b).Finite)
    (ha : ∀ j, (crossings M a (old j)).Finite)
    (hb : ∀ j, (crossings M b (old j)).Finite)
    (B : ActualMarkedTwoSideDisk M a b)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
    (terminal : Bool) (hend : (if terminal then b.val.map 1 else b.val.map 0)=p)
    (s : ℝ) (hs : 0 < s) (hshalf : s < 1/2)
    (hSideGerm : range (b.val.map ∘ endpointGermParameter terminal s hs (by linarith)) ⊆
      range B.secondSide) :
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧
      F.source ∩ (M.cover.branch : Set S)={p} ∧
      ∃ R κ : ℝ, 0 < R ∧ R < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧
      ∀ z : Plane, 0 < z 0 → z 0 < R → -κ*z 0 < z 1 → z 1 < κ*z 0 →
        z ∈ F.target ∧
        F.symm z ∉ a.val.image ∧
        (∀ j, F.symm z ∉ (old j).val.image) ∧
        (F.symm z ∈ b.val.image ↔ z 1=0) ∧
        (z 1=0 → F.symm z ∈ range B.secondSide) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let cut := b.val.map (endpointGermParameter terminal s hs (by linarith) 1)
  have hCutNotP : cut ≠ p := by
    intro he
    have hm : cut ∈ M.cover.branch := he.symm ▸ hp
    obtain h0|h1 := b.val.marked_only_at_ends _ hm
    all_goals
      have hh := congrArg Subtype.val ‹endpointGermParameter terminal s hs (by linarith) 1 = _›
      cases terminal <;> dsimp [endpointGermParameter] at hh <;> norm_num at hh <;> linarith
  let W' := W ∩ ({cut} : Set S)ᶜ
  have hW' : IsOpen W' := hW.inter isClosed_singleton.isOpen_compl
  have hpW' : p ∈ W' := ⟨hpW,by simpa using Ne.symm hCutNotP⟩
  let c : Option (Option J) → EssentialMarkedArc M := fun i => i.elim b (fun j => j.elim a old)
  have hfinite (i k : Option (Option J)) (hik : i ≠ k) : (crossings M (c i) (c k)).Finite := by
    cases i with
    | none =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        cases k with
        | none => simpa [c,ArcSurgery.crossings,Set.inter_comm] using hab
        | some j => exact hb j
    | some i =>
      cases i with
      | none =>
        cases k with
        | none => exact hab
        | some k =>
          cases k with
          | none => exact (hik rfl).elim
          | some j => exact ha j
      | some i =>
        cases k with
        | none => simpa [c,ArcSurgery.crossings,Set.inter_comm] using hb i
        | some k =>
          cases k with
          | none => simpa [c,ArcSurgery.crossings,Set.inter_comm] using ha i
          | some j => exact hOld i j (fun he => hik (congrArg (fun j => some (some j)) he))
  let g0 : Option (Option J) × Bool := (none,terminal)
  let incident : Option (Option J) × Bool → Prop := fun g =>
    (if g.2 then (c g.1).val.map 1 else (c g.1).val.map 0)=p
  obtain ⟨F,hpF,hFp,hFW,hmarks,r,hr,hrhalf,v,hvn,hunit,hopp,hnegative,hmeet,hgerms,
    δ,hδ,hδball,hδnorm,hwhole,htails⟩ :=
    actual_marked_endpoint_source_fan_chart M c hfinite p hp W' hW' hpW' g0 hend
  have hr1 : r < 1 := by linarith
  have hs1 : s < 1 := by linarith
  have hSelected : incident g0 := hend
  have hGermSource : range (b.val.map ∘ endpointGermParameter terminal r hr hr1) ⊆ W' :=
    (hgerms g0 hSelected).1.trans hFW
  have hrs : r < s := actual_selected_endpoint_germ_radius_below_avoided_cut M b terminal r s
    hr hr1 hs hs1 W' hGermSource (by intro hh; exact hh.2 (Set.mem_singleton cut))
  have hGermSide : range (b.val.map ∘ endpointGermParameter terminal r hr hr1) ⊆ range B.secondSide :=
    (actual_endpoint_germ_range_mono_radius M b terminal r s hr hr1 hs hs1 hrs.le).trans hSideGerm
  let other : (Option (Option J) × Bool) → Plane := fun g =>
    if incident g ∧ g ≠ g0 then v g else 0
  have hOtherHorizontal (g : Option (Option J) × Bool) (hy : other g 1=0) : other g 0 ≤ 0 := by
    dsimp [other] at hy ⊢
    split_ifs with hg
    · simp only [if_pos hg] at hy
      exact hnegative g hg.1 hg.2 hy
    · simp
  obtain ⟨κ,hκ,hκ1,hclear⟩ := CurveComplex.actual_finite_fan_positive_cone_clearance other hOtherHorizontal
  let O : Set (ℝ × ℝ) := {q | Plane.mk q.1 q.2 ∈ Metric.ball (0:Plane) δ}
  have hO : IsOpen O := isOpen_ball.preimage (by fun_prop)
  have h0O : (0,0) ∈ O := by
    have hz : Plane.mk (0:ℝ) 0=(0:Plane) := by ext i; fin_cases i <;> rfl
    change Plane.mk 0 0 ∈ Metric.ball (0:Plane) δ
    rw [hz]
    simpa using hδ
  obtain ⟨β,hβ,hβball⟩ := Metric.isOpen_iff.mp hO (0,0) h0O
  let R := min β 1 / 2
  have hR : 0 < R := half_pos (lt_min hβ zero_lt_one)
  have hRβ : R < β := by dsimp [R]; linarith [min_le_left β 1]
  have hR1 : R < 1 := by dsimp [R]; linarith [min_le_right β 1]
  have hCore (z : Plane) (hx : 0 < z 0) (hxr : z 0 < R)
      (hlo : -κ*z 0 < z 1) (hhi : z 1 < κ*z 0) :
      z ∈ Metric.ball (0:Plane) δ := by
    have hxy : (z 0,z 1) ∈ O := hβball (by
      change dist (z 0,z 1) ((0:ℝ),0) < β
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
      constructor
      · rw [abs_of_pos hx]; exact hxr.trans hRβ
      · apply abs_lt.mpr
        have hκx : κ*z 0 ≤ z 0 := mul_le_of_le_one_left hx.le hκ1
        constructor <;> linarith)
    have he : Plane.mk (z 0) (z 1) = z := by ext i; fin_cases i <;> rfl
    change Plane.mk (z 0) (z 1) ∈ Metric.ball (0:Plane) δ at hxy
    rwa [he] at hxy
  refine ⟨F,hpF,hFp,(fun x hx => (hFW hx).1),hmarks,R,κ,hR,hR1,hκ,hκ1,?_⟩
  intro z hx hxr hlo hhi
  have hzBall := hCore z hx hxr hlo hhi
  have hzT := hδball hzBall
  have hzS := F.map_target hzT
  have hFz := F.right_inv hzT
  have hzNorm : F (F.symm z) ∈ Metric.ball (0:Plane) δ := hFz.symm ▸ hzBall
  have hNotOther (g : Option (Option J) × Bool) (hg : incident g) (hne : g ≠ g0) :
      z ∉ segment ℝ (0:Plane) (v g) := by
    have he : other g=v g := by simp [other,hg,hne]
    simpa [he] using hclear z hx hlo hhi g
  have hNoTrace (i : Option (Option J)) (hi : i ≠ none) : F.symm z ∉ (c i).val.image := by
    intro hh
    obtain ⟨t,ht,hseg⟩ := (hwhole i _ hzS hzNorm).mp hh
    rw [hFz] at hseg
    exact hNotOther (i,t) ht (fun he => hi (congrArg Prod.fst he)) hseg
  have hAxisSide (hy : z 1=0) : F.symm z ∈ range B.secondSide := by
    have hzSeg : z ∈ segment ℝ (0:Plane) (v g0) := by
      rw [hunit,segment_eq_image']
      refine ⟨z 0,⟨hx.le,(hxr.trans hR1).le⟩,?_⟩
      ext i
      fin_cases i
      · simp
      · simpa using hy.symm
    rw [← (hgerms g0 hSelected).2] at hzSeg
    obtain ⟨t,he⟩ := hzSeg
    have htF := (hgerms g0 hSelected).1 (Set.mem_range_self t)
    have hsame : b.val.map (endpointGermParameter terminal r hr hr1 t)=F.symm z :=
      F.injOn htF hzS (he.trans hFz.symm)
    exact hsame ▸ hGermSide (Set.mem_range_self t)
  refine ⟨hzT,hNoTrace (some none) (by simp),fun j => hNoTrace (some (some j)) (by simp),?_,hAxisSide⟩
  constructor
  · intro hh
    obtain ⟨t,ht,hseg⟩ := (hwhole none _ hzS hzNorm).mp hh
    rw [hFz] at hseg
    by_cases ht0 : (none,t)=g0
    · rw [ht0,hunit,segment_eq_image'] at hseg
      obtain ⟨u,hu,he⟩ := hseg
      have he1 := congrArg (fun z : Plane => z 1) he
      change 0+u*(0-0)=z 1 at he1
      simpa using he1.symm
    · exact False.elim (hNotOther (none,t) ht ht0 hseg)
  · intro hy
    exact B.second_on_curve (hAxisSide hy)
end CurveComplex.HyperellipticModel
