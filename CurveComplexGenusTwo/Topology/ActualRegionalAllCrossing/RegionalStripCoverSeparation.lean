import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalFrontierLocalBasis
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import Mathlib.Analysis.Complex.Circle

open CurveComplex Set Topology
namespace RegionalEmbeddedFamily
open Filter
set_option maxHeartbeats 3000000

/-- Local homeomorphisms pull back an open contractible neighborhood basis. -/
theorem contact_local_homeomorph_contractible_basis
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsLocalHomeomorph p)
    (hbasis : ∀ (y : Y) (W : Set Y), IsOpen W → y ∈ W →
      ∃ U : Set Y, y ∈ U ∧ IsOpen U ∧ U ⊆ W ∧ ContractibleSpace U) :
    ∀ (x : X) (W : Set X), IsOpen W → x ∈ W →
      ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ U ⊆ W ∧ ContractibleSpace U := by
  intro x W hW hxW
  obtain ⟨e,hxe,he⟩ := hp x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
  obtain ⟨V,hxV,hV,hVW,hcV⟩ := hbasis (e x) _ hopen
    ⟨e.map_source hxe,by simpa only [Set.mem_preimage,e.left_inv hxe] using hxW⟩
  have hVT : V ⊆ e.target := fun _ hz => (hVW hz).1
  let U := e.symm '' V
  have hU : IsOpen U := e.isOpen_image_symm_of_subset_target hV hVT
  let : ContractibleSpace V := hcV
  let f : V ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hVT rfl
  exact ⟨U,⟨e x,hxV,e.left_inv hxe⟩,hU,
    (by rintro _ ⟨z,hz,rfl⟩; exact (hVW hz).2),f.symm.contractibleSpace⟩

/-- The whole compact proper strip lifts through a cover with its chosen center lift. -/
theorem contact_cover_lifts_proper_strip
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (p : X → Y) (hp : IsCoveringMap p)
    (N : C(Interval × Set.Icc (-1 : ℝ) 1,Y)) (hN : IsEmbedding N)
    (hopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (a : C(Interval,Y)) (hcenter : ∀ t, N (t,⟨0,by norm_num⟩) = a t)
    (A : C(Interval,X)) (hA : ∀ t, p (A t) = a t) :
    ∃ M : C(Interval × Set.Icc (-1 : ℝ) 1,X), IsEmbedding M ∧
      (∀ t, M (t,⟨0,by norm_num⟩) = A t) ∧
      IsOpen (M '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) ∧
      (∀ z : Interval × Set.Icc (-1 : ℝ) 1, p (M z) = N z) := by
  classical
  let z : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  let : ContractibleSpace Interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  let : ContractibleSpace (Set.Icc (-1 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨z,z.property⟩
  let : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace (Set.Icc (-1 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨M,⟨hM0,hMp⟩,_⟩ := hp.existsUnique_continuousMap_lifts N (0,z) (A 0)
    ((hA 0).trans (hcenter 0).symm)
  have hproj (u : Interval × Set.Icc (-1 : ℝ) 1) : p (M u) = N u := congrFun hMp u
  have hMi : Function.Injective M := by
    intro u v huv
    apply hN.injective
    rw [← hproj u,← hproj v,huv]
  have hMe : IsEmbedding M := (M.continuous.isClosedEmbedding hMi).isEmbedding
  have hMc : ∀ t, M (t,z) = A t := by
    have hcont : Continuous (fun t : Interval => M (t,z)) := by fun_prop
    have heq : p ∘ (fun t : Interval => M (t,z)) = p ∘ A := by
      ext t
      exact (hproj (t,z)).trans ((hcenter t).trans (hA t).symm)
    exact congrFun (hp.eq_of_comp_eq hcont A.continuous heq 0 hM0)
  let O := {u : Interval × Set.Icc (-1 : ℝ) 1 | (-1 : ℝ) < u.2.val ∧ u.2.val < 1}
  have hn : IsOpenEmbedding (fun u : O => N u.val) := {
    toIsEmbedding := hN.comp IsEmbedding.subtypeVal
    isOpen_range := by
      have he : Set.range (fun u : O => N u.val) = N '' O := by ext x; simp
      rw [he]
      exact hopen }
  have hm : IsOpenEmbedding (fun u : O => M u.val) := by
    apply hp.isLocalHomeomorph.isOpenEmbedding_of_comp
    · have he : p ∘ (fun u : O => M u.val) = (fun u : O => N u.val) :=
        funext (fun u => hproj u.val)
      rw [he]
      exact hn
    · exact M.continuous.comp continuous_subtype_val
  refine ⟨M,hMe,hMc,?_,hproj⟩
  have he : Set.range (fun u : O => M u.val) = M '' O := by ext x; simp
  rw [← he]
  exact hm.isOpen_range

/-- An embedded compact strip with open transverse interior defines a circle map
whose unit fiber is precisely the whole center arc. -/
theorem contact_proper_strip_circle_map
    {X : Type} [TopologicalSpace X] [T2Space X]
    (N : C(Interval × Set.Icc (-1 : ℝ) 1,X)) (hN : IsEmbedding N)
    (hopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ f : C(X,Circle),
      (∀ z, f (N z) = Circle.exp (Real.pi * z.2.val)) ∧
      ∀ x, f x = 1 ↔ ∃ t : Interval, N (t,⟨0,by norm_num⟩) = x := by
  classical
  let D := Interval × Set.Icc (-1 : ℝ) 1
  let z : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  let root : D := (0,z)
  let e : D ≃ₜ Set.range N := hN.toHomeomorph
  let v : X → D := fun x => if hx : x ∈ Set.range N then e.symm ⟨x,hx⟩ else root
  have hv (u : D) : v (N u) = u := by
    simp only [v,dite_eq_left (Set.mem_range_self u)]
    exact e.symm_apply_apply u
  have hvc : ContinuousOn v (Set.range N) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact e.symm.continuous.congr (fun x => by
      change e.symm x = v x.val
      simp only [v,dite_eq_left x.property])
  let phase : D → Circle := fun u => Circle.exp (Real.pi * u.2.val)
  have hphase : Continuous phase := Circle.exp.continuous.comp
    (show Continuous (fun u : Interval × Set.Icc (-1 : ℝ) 1 => Real.pi * u.2.val) by fun_prop)
  have hclosed : IsClosed (Set.range N) := (isCompact_range N.continuous).isClosed
  have hboundary : ∀ x ∈ frontier (Set.range N), phase (v x) = Circle.exp Real.pi := by
    intro x hx
    obtain ⟨u,rfl⟩ := hclosed.frontier_subset hx
    rw [hv]
    have hnot : ¬ ((-1 : ℝ) < u.2.val ∧ u.2.val < 1) := by
      intro hu
      exact hx.2 (interior_maximal (Set.image_subset_range _ _) hopen ⟨u,hu,rfl⟩)
    have hedges : u.2.val = -1 ∨ u.2.val = 1 := by
      have hb := u.2.property
      rcases le_or_gt u.2.val (-1) with hu | hu
      · exact Or.inl (le_antisymm hu hb.1)
      · exact Or.inr (le_antisymm hb.2 (not_lt.mp (fun hh => hnot ⟨hu,hh⟩)))
    change Circle.exp (Real.pi * u.2.val) = Circle.exp Real.pi
    rcases hedges with he | he
    · apply Circle.exp_eq_exp.mpr
      exact ⟨-1,by rw [he]; norm_num; ring⟩
    · simp only [he,mul_one]
  let f : C(X,Circle) := ⟨fun x => if x ∈ Set.range N then phase (v x) else Circle.exp Real.pi,
    continuous_if hboundary
      (by change ContinuousOn (fun x => phase (v x)) (closure (Set.range N))
          rw [hclosed.closure_eq]; exact hphase.comp_continuousOn hvc)
      continuous_const.continuousOn⟩
  have hfN (u : D) : f (N u) = Circle.exp (Real.pi * u.2.val) := by
    change (if N u ∈ Set.range N then phase (v (N u)) else _) = _
    rw [ite_eq_left (Set.mem_range_self u),hv]
  have hphase1 (u : D) : Circle.exp (Real.pi * u.2.val) = 1 ↔ u.2.val = 0 := by
    constructor
    · intro he
      have hr : Real.pi * u.2.val = 0 := by
        by_cases hu : u.2.val ≤ 0
        · apply Circle.exp_injOn_Icc (a := -Real.pi) (b := 0) (by linarith [Real.pi_pos])
            ⟨by nlinarith [u.2.property.1,Real.pi_pos],mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hu⟩
            ⟨by linarith [Real.pi_pos],le_rfl⟩
          simpa only [Circle.exp_zero] using he
        · apply Circle.exp_injOn_Icc (a := 0) (b := Real.pi) (by linarith [Real.pi_pos])
            ⟨mul_nonneg Real.pi_pos.le (not_le.mp hu).le,by nlinarith [u.2.property.2,Real.pi_pos]⟩
            ⟨le_rfl,Real.pi_pos.le⟩
          simpa only [Circle.exp_zero] using he
      exact (mul_eq_zero.mp hr).resolve_left Real.pi_ne_zero
    · intro he
      simp [he]
  refine ⟨f,hfN,?_⟩
  intro x
  constructor
  · intro hx
    by_cases hn : x ∈ Set.range N
    · obtain ⟨u,rfl⟩ := hn
      have hu : u.2.val = 0 := hphase1 u |>.mp ((hfN u).symm.trans hx)
      exact ⟨u.1,congrArg N (Prod.ext rfl (Subtype.ext hu.symm))⟩
    · have hc : f x = Circle.exp Real.pi := ite_eq_right hn
      exact False.elim (Circle.exp_pi_ne_one (hc.symm.trans hx))
  · rintro ⟨t,rfl⟩
    rw [hfN]
    simp

/-- On a simply connected space a proper strip separates along its whole center,
including both endpoints. -/
theorem contact_simply_connected_proper_strip_separates
    {X : Type} [TopologicalSpace X] [T2Space X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (N : C(Interval × Set.Icc (-1 : ℝ) 1,X)) (hN : IsEmbedding N)
    (hopen : IsOpen (N '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (Set.range (fun t : Interval => N (t,⟨0,by norm_num⟩)))ᶜ ∧
      frontier U = Set.range (fun t : Interval => N (t,⟨0,by norm_num⟩)) ∧
      frontier V = Set.range (fun t : Interval => N (t,⟨0,by norm_num⟩)) := by
  let z : Set.Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
  let : ContractibleSpace Interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  let : ContractibleSpace (Set.Icc (-1 : ℝ) 1) :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨z,z.property⟩
  obtain ⟨f,hfN,hfiber⟩ := contact_proper_strip_circle_map N hN hopen
  obtain ⟨g,⟨hg0,hgf⟩,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f
    (N (0,z)) 0 (by rw [hfN]; simp [z])
  have hgN : ∀ u, g (N u) = Real.pi * u.2.val := by
    have hleft : Continuous (fun u : Interval × Set.Icc (-1 : ℝ) 1 => g (N u)) := by fun_prop
    have hright : Continuous (fun u : Interval × Set.Icc (-1 : ℝ) 1 => Real.pi * u.2.val) := by fun_prop
    apply congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq hleft hright ?_ (0,z) ?_)
    · funext u
      exact (congrFun hgf (N u)).trans (hfN u)
    · simpa only [z,Subtype.coe_mk,mul_zero] using hg0
  have hzero : ∀ x, g x = 0 ↔ ∃ t : Interval, N (t,z) = x := by
    intro x
    constructor
    · intro hx
      apply (hfiber x).mp
      rw [← congrFun hgf x]
      change Circle.exp (g x) = 1
      rw [hx,Circle.exp_zero]
    · rintro ⟨t,rfl⟩
      rw [hgN]
      simp [z]
  let U : Set X := {x | g x < 0}
  let V : Set X := {x | 0 < g x}
  have hU : IsOpen U := isOpen_lt g.continuous continuous_const
  have hV : IsOpen V := isOpen_lt continuous_const g.continuous
  have hcminus (t : Interval) : N (t,z) ∈ closure U := by
    have hz : z ∈ closure (Set.Iio z) := by
      rw [closure_Iio' ⟨⟨-1,by norm_num⟩,by norm_num [z]⟩]
      exact Set.mem_Iic.mpr le_rfl
    have hc : Continuous (fun w : Set.Icc (-1 : ℝ) 1 => N (t,w)) := by fun_prop
    apply closure_mono (t := U) ?_ (mem_closure_image hc.continuousAt hz)
    rintro _ ⟨w,hw,rfl⟩
    change g (N (t,w)) < 0
    rw [hgN]
    exact mul_neg_of_pos_of_neg Real.pi_pos hw
  have hcplus (t : Interval) : N (t,z) ∈ closure V := by
    have hz : z ∈ closure (Set.Ioi z) := by
      rw [closure_Ioi' ⟨⟨1,by norm_num⟩,by norm_num [z]⟩]
      exact Set.mem_Ici.mpr le_rfl
    have hc : Continuous (fun w : Set.Icc (-1 : ℝ) 1 => N (t,w)) := by fun_prop
    apply closure_mono (t := V) ?_ (mem_closure_image hc.continuousAt hz)
    rintro _ ⟨w,hw,rfl⟩
    change 0 < g (N (t,w))
    rw [hgN]
    exact mul_pos Real.pi_pos hw
  refine ⟨U,V,hU,hV,Set.disjoint_left.mpr (fun x (hu : g x < 0) (hv : 0 < g x) => lt_asymm hu hv),?_,?_,?_⟩
  · ext x
    change (g x < 0 ∨ 0 < g x) ↔ ¬ ∃ t, N (t,z) = x
    rw [← hzero x]
    constructor
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
    · exact lt_or_gt_of_ne
  · ext x
    constructor
    · exact fun hx => (hzero x).mp ((frontier_lt_subset_eq g.continuous continuous_const) hx)
    · rintro ⟨t,rfl⟩
      rw [frontier,hU.interior_eq]
      refine ⟨hcminus t,?_⟩
      change ¬ g (N (t,z)) < 0
      rw [hgN]
      simp [z]
  · ext x
    constructor
    · exact fun hx => (hzero x).mp ((frontier_lt_subset_eq continuous_const g.continuous) hx).symm
    · rintro ⟨t,rfl⟩
      rw [frontier,hV.interior_eq]
      refine ⟨hcplus t,?_⟩
      change ¬ 0 < g (N (t,z))
      rw [hgN]
      simp [z]

end RegionalEmbeddedFamily
