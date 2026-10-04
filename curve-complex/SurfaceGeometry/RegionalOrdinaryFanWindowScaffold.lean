import RegionalWeightedMovieDefinitions
import RegionalNormalizationChordScaffold
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
import CurveComplexGenusTwo.Topology.ArcCounts.ReverseGeometry.ActualArcNowhereDense
open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
set_option maxHeartbeats 2200000

private theorem finite_point_neighborhoods
    {S K : Type} [TopologicalSpace S] [T2Space S] [Fintype K]
    (p : K → S) (hp : Function.Injective p) :
    ∃ U : K → Set S, (∀ k, IsOpen (U k) ∧ p k ∈ U k) ∧
      ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
  classical
  have hsep (i j : K) : ∃ A B : Set S,
      IsOpen A ∧ IsOpen B ∧ p i ∈ A ∧ p j ∈ B ∧
      (i ≠ j → Disjoint A B) := by
    by_cases hij : i = j
    · exact ⟨univ,univ,isOpen_univ,isOpen_univ,mem_univ _,mem_univ _,
        fun hn => (hn hij).elim⟩
    · obtain ⟨A,B,hA,hB,hi,hj,hd⟩ := t2_separation (fun he => hij (hp he))
      exact ⟨A,B,hA,hB,hi,hj,fun _ => hd⟩
  choose A B hA hB hpa hpb hd using hsep
  let U : K → Set S := fun i => (⋂ j, A i j) ∩ (⋂ j, B j i)
  refine ⟨U,?_,?_⟩
  · intro i
    exact ⟨(isOpen_iInter_of_finite (hA i)).inter
      (isOpen_iInter_of_finite (fun j => hB j i)),
      ⟨mem_iInter.mpr (hpa i),mem_iInter.mpr (fun j => hpb j i)⟩⟩
  · intro i j hij
    exact (hd i j hij).mono (fun x hx => mem_iInter.mp hx.1 j)
      (fun x hx => mem_iInter.mp hx.2 i)

private theorem relative_open_interior_neighborhood
    {S : Type} [TopologicalSpace S] (F : Set S)
    (V : Set ↥F) (hV : IsOpen V) :
    ∃ O : Set S, IsOpen O ∧ O ⊆ interior F ∧
      (∀ y : ↥F, y ∈ V → y.val ∈ interior F → y.val ∈ O) ∧
      O ⊆ Subtype.val '' V := by
  obtain ⟨W,hW,hWV⟩ := isOpen_induced_iff.mp hV
  refine ⟨W ∩ interior F,hW.inter isOpen_interior,inter_subset_right,?_,?_⟩
  · intro y hy hi
    exact ⟨(show y ∈ Subtype.val ⁻¹' W from hWV.symm ▸ hy),hi⟩
  · intro x hx
    refine ⟨⟨x,interior_subset hx.2⟩,?_,rfl⟩
    rw [←hWV]
    exact hx.1


private theorem affine_interval_image (a b : Interval) (hab : a < b) :
    range (CurveComplex.BranchedDoubleCover.intervalAffine a b) = Icc a b := by
  apply Set.Subset.antisymm
  · rintro t ⟨u,rfl⟩
    exact CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hab.le u
  · intro t ht
    let u : Interval := ⟨(t.val-a.val)/(b.val-a.val),by
      have hpos : 0 < b.val-a.val := sub_pos.mpr hab
      have ht0 : a.val ≤ t.val := ht.1
      have ht1 : t.val ≤ b.val := ht.2
      exact ⟨div_nonneg (sub_nonneg.mpr ht0) hpos.le,
        (div_le_one hpos).mpr (by linarith)⟩⟩
    refine ⟨u,?_⟩
    apply Subtype.ext
    change (1-(t.val-a.val)/(b.val-a.val))*a.val+
      ((t.val-a.val)/(b.val-a.val))*b.val=t.val
    have habv : a.val < b.val := hab
    field_simp [sub_ne_zero.mpr habv.ne']
    <;> ring

private theorem interval_image_is_arc
    (f : Interval → Plane) (a b : Interval) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hi : InjOn f (Icc a b)) :
    IsArcBetween (f '' Icc a b) (f a) (f b) := by
  let k : C(Interval,Interval) := CurveComplex.BranchedDoubleCover.intervalSegment a b
  have hkRange : range k = Icc a b := affine_interval_image a b hab
  have hk0 : k 0 = a := by apply Subtype.ext; change (1-0)*a.val+0*b.val=a.val; ring
  have hk1 : k 1 = b := by apply Subtype.ext; change (1-1)*a.val+1*b.val=b.val; ring
  let γ : Path (f a) (f b) := {
    toFun := f ∘ k
    continuous_toFun := hf.comp_continuous k.continuous
      (fun t => hkRange ▸ mem_range_self t)
    source' := congrArg f hk0
    target' := congrArg f hk1 }
  have hγi : Function.Injective γ := by
    intro t u he
    have hk := hi (hkRange ▸ mem_range_self t) (hkRange ▸ mem_range_self u) he
    apply Subtype.ext
    have hv := congrArg Subtype.val hk
    change (1-t.val)*a.val+t.val*b.val=(1-u.val)*a.val+u.val*b.val at hv
    have habv : a.val < b.val := hab
    nlinarith
  have hγRange : range γ = f '' Icc a b := by
    change range (f ∘ k) = _
    rw [Set.range_comp,hkRange]
  refine ⟨γ.extend,γ.continuous_extend.continuousOn,?_,?_,γ.extend_zero,γ.extend_one⟩
  · intro s hs t ht he
    rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
    exact congrArg Subtype.val (hγi he)
  · rw [γ.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))]
    exact hγRange

private theorem window_branch_images
    {S κ : Type} [TopologicalSpace S] {F : Set S}
    (a : κ → C(Interval,↥F)) (ha : ∀ i, IsEmbedding (a i))
    (V : Set ↥F) (p : ↥F) (W : IncidentFanWindow F a V p)
    (i : incidentIndex a p) :
    (fun t => W.chart (a i.val t).val) '' Icc (W.left i) (W.center i) =
      segment ℝ (incidentPorts a p W.chart W.left W.right (i,false)) 0 ∧
    (fun t => W.chart (a i.val t).val) '' Icc (W.center i) (W.right i) =
      segment ℝ 0 (incidentPorts a p W.chart W.left W.right (i,true)) := by
  let f : Interval → Plane := fun t => W.chart (a i.val t).val
  have hsource (t : Interval) (ht : t ∈ Icc (W.left i) (W.right i)) :
      (a i.val t).val ∈ W.chart.source :=
    (W.whole_closed i |>.symm ▸ (show a i.val t ∈ a i.val '' Icc (W.left i) (W.right i)
      from ⟨t,ht,rfl⟩)).1.1
  have hcont : ContinuousOn f (Icc (W.left i) (W.right i)) :=
    W.chart.continuousOn.comp (continuous_subtype_val.comp (a i.val).continuous).continuousOn hsource
  have hinj : InjOn f (Icc (W.left i) (W.right i)) := by
    intro t ht u hu he
    exact (ha i.val).injective (Subtype.ext (W.chart.injOn (hsource t ht) (hsource u hu) he))
  have hcenter : f (W.center i) = 0 := by
    change W.chart (a i.val (W.center i)).val=0
    rw [W.at_center,W.contact_zero]
  have hbeforeSubset : Icc (W.left i) (W.center i) ⊆ Icc (W.left i) (W.right i) :=
    Icc_subset_Icc_right (W.cuts i).2.2.1.le
  have hafterSubset : Icc (W.center i) (W.right i) ⊆ Icc (W.left i) (W.right i) :=
    Icc_subset_Icc_left (W.cuts i).2.1.le
  have hwhole := interval_image_is_arc f (W.left i) (W.right i)
    ((W.cuts i).2.1.trans (W.cuts i).2.2.1) hcont hinj
  have hb := interval_image_is_arc f (W.left i) (W.center i)
    (W.cuts i).2.1 (hcont.mono hbeforeSubset) (hinj.mono hbeforeSubset)
  have he := interval_image_is_arc f (W.center i) (W.right i)
    (W.cuts i).2.2.1 (hcont.mono hafterSubset) (hinj.mono hafterSubset)
  rw [hcenter] at hb he
  have hleftne : f (W.left i) ≠ 0 := by
    intro hz
    have hs := W.ports_on_sphere (i,false)
    change f (W.left i) ∈ Metric.sphere (0:Plane) 1 at hs
    rw [hz,Metric.mem_sphere,dist_self] at hs
    norm_num at hs
  have hrightne : (0:Plane) ≠ f (W.right i) := by
    intro hz
    have hs := W.ports_on_sphere (i,true)
    change f (W.right i) ∈ Metric.sphere (0:Plane) 1 at hs
    rw [←hz,Metric.mem_sphere,dist_self] at hs
    norm_num at hs
  have hradial : f '' Icc (W.left i) (W.right i) =
      segment ℝ (f (W.left i)) 0 ∪ segment ℝ 0 (f (W.right i)) := W.radial_trace i
  constructor
  · exact hb.eq_of_subset_arc (isArcBetween_segment hleftne) hwhole
      (image_mono hbeforeSubset) (hradial.symm ▸ subset_union_left)
  · exact he.eq_of_subset_arc (isArcBetween_segment hrightne) hwhole
      (image_mono hafterSubset) (hradial.symm ▸ subset_union_right)


private theorem homogeneous_norm_homeomorph
    (H : Plane ≃ₜ Plane) (hzero : H 0 = 0)
    (hhom : ∀ r : ℝ, 0 ≤ r → ∀ z, H (r • z) = r • H z) :
    ∃ K : Plane ≃ₜ Plane,
      K 0 = 0 ∧ (∀ z, ‖K z‖ = ‖z‖) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ z, K (r • z) = r • K z) ∧
      ∀ z, K z = (‖z‖ / ‖H z‖) • H z := by
  have hz (z : Plane) : H z = 0 ↔ z = 0 := by
    constructor
    · intro he; exact H.injective (he.trans hzero.symm)
    · rintro rfl; exact hzero
  have hi0 : H.symm 0 = 0 := by simpa using (congrArg H.symm hzero).symm
  have hihom (r : ℝ) (hr : 0 ≤ r) (z : Plane) :
      H.symm (r • z) = r • H.symm z := by
    apply H.injective
    rw [H.apply_symm_apply,hhom r hr,H.apply_symm_apply]
  let k : Plane → Plane := fun z => (‖z‖ / ‖H z‖) • H z
  let kinv : Plane → Plane := fun z => (‖z‖ / ‖H.symm z‖) • H.symm z
  have hk0 : k 0 = 0 := by simp [k,hzero]
  have hki0 : kinv 0 = 0 := by simp [kinv,hi0]
  have hnorm (G : Plane ≃ₜ Plane) (hG : G 0 = 0) (z : Plane) :
      ‖(‖z‖ / ‖G z‖) • G z‖ = ‖z‖ := by
    by_cases he : z = 0
    · simp [he,hG]
    · have hg : G z ≠ 0 := fun hg => he (G.injective (hg.trans hG.symm))
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hg)]
  have hknorm (z : Plane) : ‖k z‖ = ‖z‖ := hnorm H hzero z
  have hkinorm (z : Plane) : ‖kinv z‖ = ‖z‖ := hnorm H.symm hi0 z
  have hinverse (G : Plane ≃ₜ Plane) (hG : G 0 = 0)
      (hGh : ∀ r : ℝ, 0 ≤ r → ∀ z, G (r • z) = r • G z)
      (hGih : ∀ r : ℝ, 0 ≤ r → ∀ z, G.symm (r • z) = r • G.symm z)
      (z : Plane) :
      (‖(‖z‖ / ‖G z‖) • G z‖ /
        ‖G.symm ((‖z‖ / ‖G z‖) • G z)‖) •
        G.symm ((‖z‖ / ‖G z‖) • G z) = z := by
    by_cases hz0 : z = 0
    · simp [hz0,hG]
    · have hg : G z ≠ 0 := fun hg => hz0 (G.injective (hg.trans hG.symm))
      have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      have hng : ‖G z‖ ≠ 0 := norm_ne_zero_iff.mpr hg
      have hc : 0 ≤ ‖z‖ / ‖G z‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [hnorm G hG z,hGih _ hc,G.symm_apply_apply,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hc,smul_smul]
      have hs : ‖z‖ / ((‖z‖ / ‖G z‖) * ‖z‖) * (‖z‖ / ‖G z‖) = 1 := by
        field_simp
      rw [hs,one_smul]
  have hcont (G : Plane ≃ₜ Plane) (hG : G 0 = 0) :
      Continuous (fun z => (‖z‖ / ‖G z‖) • G z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz0 : z = 0
    · subst z
      rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨ε,hε,?_⟩
      intro y hy
      simpa only [norm_zero,zero_div,zero_smul,dist_zero_right,hnorm G hG y] using hy
    · have hg : G z ≠ 0 := fun hg => hz0 (G.injective (hg.trans hG.symm))
      exact (continuous_norm.continuousAt.div (G.continuous.norm.continuousAt)
        (norm_ne_zero_iff.mpr hg)).smul G.continuous.continuousAt
  let K : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := k
      invFun := kinv
      left_inv := hinverse H hzero hhom hihom
      right_inv := by intro z; exact hinverse H.symm hi0 hihom hhom z }
    continuous_toFun := hcont H hzero
    continuous_invFun := hcont H.symm hi0 }
  refine ⟨K,hk0,hknorm,?_,fun _ => rfl⟩
  intro r hr z
  by_cases hr0 : r = 0
  · subst r; simp only [zero_smul]; exact hk0
  · change (‖r • z‖ / ‖H (r • z)‖) • H (r • z) = r • k z
    rw [hhom r hr,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
      mul_div_mul_left _ _ hr0,smul_smul]
    change (‖z‖ / ‖H z‖ * r) • H z = _
    rw [mul_comm,←smul_smul]


private theorem unit_pair_axis_homeomorph (u v : Plane)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
    ∃ K : Plane ≃ₜ Plane,
      K 0 = 0 ∧ (∀ z, ‖K z‖ = ‖z‖) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ z, K (r • z) = r • K z) ∧
      K u 1 = 0 ∧ K v 1 = 0 := by
  let w : Plane := u-v
  have hw : w ≠ 0 := sub_ne_zero.mpr huv
  let n : ℝ := w 0 ^ 2 + w 1 ^ 2
  have hn : 0 < n := by
    have hnonneg : 0 ≤ n := add_nonneg (sq_nonneg _) (sq_nonneg _)
    apply lt_of_le_of_ne hnonneg
    intro hz
    have h0 : w 0 = 0 := by dsimp [n] at hz; nlinarith [sq_nonneg (w 1)]
    have h1 : w 1 = 0 := by dsimp [n] at hz; nlinarith [sq_nonneg (w 0)]
    exact hw (by ext i; fin_cases i <;> assumption)
  let L : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun z => Plane.mk (w 0*z 0+w 1*z 1) (w 0*z 1-w 1*z 0)
      invFun := fun z => Plane.mk ((w 0*z 0-w 1*z 1)/n) ((w 1*z 0+w 0*z 1)/n)
      left_inv := by
        intro z; ext i
        fin_cases i <;> dsimp [Plane.mk] <;> field_simp [hn.ne'] <;> dsimp [n] <;> ring
      right_inv := by
        intro z; ext i
        fin_cases i <;> dsimp [Plane.mk] <;> field_simp [hn.ne'] <;> dsimp [n] <;> ring }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hL0 : L 0 = 0 := by ext i; fin_cases i <;> simp [L,Plane.mk]
  have hLhom (r : ℝ) (z : Plane) : L (r • z) = r • L z := by
    ext i; fin_cases i <;> simp [L,Plane.mk] <;> ring
  have huq : u 0 ^ 2+u 1 ^ 2=1 := by
    have h := EuclideanSpace.real_norm_sq_eq u
    simpa [hu,Fin.sum_univ_two] using h.symm
  have hvq : v 0 ^ 2+v 1 ^ 2=1 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    simpa [hv,Fin.sum_univ_two] using h.symm
  have hLu : 0 < L u 0 := by
    change 0 < (u 0-v 0)*u 0+(u 1-v 1)*u 1
    dsimp [n,w] at hn
    nlinarith
  have hLv : L v 0 < 0 := by
    change (u 0-v 0)*v 0+(u 1-v 1)*v 1 < 0
    dsimp [n,w] at hn
    nlinarith
  let a : ℝ := L u 1 / L u 0
  let b : ℝ := L v 1 / L v 0
  let T : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun z => Plane.mk (z 0) (z 1-(a*max (z 0) 0+b*min (z 0) 0))
      invFun := fun z => Plane.mk (z 0) (z 1+(a*max (z 0) 0+b*min (z 0) 0))
      left_inv := by intro z; ext i; fin_cases i <;> dsimp [Plane.mk] <;> ring
      right_inv := by intro z; ext i; fin_cases i <;> dsimp [Plane.mk] <;> ring }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hT0 : T 0 = 0 := by ext i; fin_cases i <;> simp [T,Plane.mk]
  have hThom (r : ℝ) (hr : 0 ≤ r) (z : Plane) : T (r • z) = r • T z := by
    ext i; fin_cases i
    · rfl
    · change r*z 1-(a*max (r*z 0) 0+b*min (r*z 0) 0)=
        r*(z 1-(a*max (z 0) 0+b*min (z 0) 0))
      rw [←mul_zero r,←mul_max_of_nonneg _ _ hr,←mul_min_of_nonneg _ _ hr]
      ring
  have hTu : T (L u) 1 = 0 := by
    change L u 1-(L u 1/L u 0*max (L u 0) 0+L v 1/L v 0*min (L u 0) 0)=0
    rw [max_eq_left hLu.le,min_eq_right hLu.le]
    simp [hLu.ne']
  have hTv : T (L v) 1 = 0 := by
    change L v 1-(L u 1/L u 0*max (L v 0) 0+L v 1/L v 0*min (L v 0) 0)=0
    rw [max_eq_right hLv.le,min_eq_left hLv.le]
    simp [hLv.ne]
  let H : Plane ≃ₜ Plane := L.trans T
  have hH0 : H 0 = 0 := by change T (L 0)=0; rw [hL0,hT0]
  have hHhom (r : ℝ) (hr : 0 ≤ r) (z : Plane) : H (r • z)=r • H z := by
    change T (L (r • z))=r • T (L z)
    rw [hLhom,hThom r hr]
  obtain ⟨K,hK0,hKn,hKh,hKf⟩ := homogeneous_norm_homeomorph H hH0 hHhom
  refine ⟨K,hK0,hKn,hKh,?_,?_⟩
  · rw [hKf]; change (‖u‖/‖H u‖)*(T (L u) 1)=0; rw [hTu,mul_zero]
  · rw [hKf]; change (‖v‖/‖H v‖)*(T (L v) 1)=0; rw [hTv,mul_zero]


private theorem image_segment_zero (K : Plane ≃ₜ Plane) (h0 : K 0 = 0)
    (hh : ∀ r : ℝ, 0 ≤ r → ∀ z, K (r • z) = r • K z) (v : Plane) :
    K '' segment ℝ 0 v = segment ℝ 0 (K v) := by
  apply Set.Subset.antisymm
  · rintro z ⟨x,⟨a,b,ha,hb,hab,he⟩,rfl⟩
    have hx : x = b • v := by simpa using he.symm
    rw [hx,hh b hb]
    exact ⟨a,b,ha,hb,hab,by simp⟩
  · rintro z ⟨a,b,ha,hb,hab,he⟩
    refine ⟨b • v,⟨a,b,ha,hb,hab,by simp⟩,?_⟩
    rw [hh b hb]
    simpa using he

private theorem window_norm_transform
    {S κ : Type} [TopologicalSpace S] {F : Set S}
    (a : κ → C(Interval,↥F)) (V : Set ↥F) (p : ↥F)
    (W : IncidentFanWindow F a V p)
    (K : Plane ≃ₜ Plane) (h0 : K 0 = 0) (hn : ∀ z, ‖K z‖ = ‖z‖)
    (hh : ∀ r : ℝ, 0 ≤ r → ∀ z, K (r • z) = r • K z) :
    ∃ A : IncidentFanWindow F a V p,
      A.chart = W.chart.trans K.toOpenPartialHomeomorph ∧
      A.left = W.left ∧ A.right = W.right ∧ A.center = W.center ∧
      (∀ B : Set Plane, (∀ z, K z ∈ B ↔ z ∈ B) →
        RegionalChordNormalization.chartPull F A.chart B =
          RegionalChordNormalization.chartPull F W.chart B) := by
  let E := W.chart.trans K.toOpenPartialHomeomorph
  have hsource : E.source = W.chart.source := by
    simp [E,OpenPartialHomeomorph.trans_source]
  have hpull (B : Set Plane) (hB : ∀ z, K z ∈ B ↔ z ∈ B) :
      RegionalChordNormalization.chartPull F E B =
        RegionalChordNormalization.chartPull F W.chart B := by
    ext y
    change (y.val ∈ E.source ∧ K (W.chart y.val) ∈ B) ↔ _
    rw [hsource,hB]
    rfl
  have hc : RegionalChordNormalization.chartPull F E (Metric.closedBall (0:Plane) 1) =
      RegionalChordNormalization.chartPull F W.chart (Metric.closedBall (0:Plane) 1) :=
    hpull _ (fun z => by simp [Metric.mem_closedBall,dist_zero_right,hn])
  have ho : RegionalChordNormalization.chartPull F E (Metric.ball (0:Plane) 1) =
      RegionalChordNormalization.chartPull F W.chart (Metric.ball (0:Plane) 1) :=
    hpull _ (fun z => by simp [Metric.mem_ball,dist_zero_right,hn])
  have hports (z : incidentIndex a p × Bool) :
      incidentPorts a p E W.left W.right z = K (incidentPorts a p W.chart W.left W.right z) := rfl
  let A : IncidentFanWindow F a V p := {
    chart := E
    source_closure := hsource.symm ▸ W.source_closure
    contact_in_source := hsource.symm ▸ W.contact_in_source
    contact_zero := by change K (W.chart p.val) = 0; rw [W.contact_zero,h0]
    disk_in_target := by
      intro z hz
      have hz0 : K.symm z ∈ Metric.closedBall (0:Plane) 1 := by
        have hh := hn (K.symm z)
        rw [K.apply_symm_apply] at hh
        simpa only [Metric.mem_closedBall,dist_zero_right,←hh] using hz
      change z ∈ K.toOpenPartialHomeomorph.target ∩
        K.toOpenPartialHomeomorph.symm ⁻¹' W.chart.target
      exact ⟨mem_univ _,W.disk_in_target hz0⟩
    left := W.left
    right := W.right
    center := W.center
    cuts := W.cuts
    at_center := W.at_center
    whole_closed := by intro i; rw [hc]; exact W.whole_closed i
    whole_open := by intro i; rw [ho]; exact W.whole_open i
    radial_trace := by
      intro i
      change (K ∘ (fun t => W.chart (a i.val t).val)) '' _ = _
      rw [Set.image_comp,W.radial_trace,image_union,hports,hports,
        segment_symm ℝ (incidentPorts a p W.chart W.left W.right (i,false)) 0,
        image_segment_zero K h0 hh,image_segment_zero K h0 hh,
        segment_symm ℝ 0 (K (incidentPorts a p W.chart W.left W.right (i,false)))]
    nonincident_clear := by intro i hi; rw [hc]; exact W.nonincident_clear i hi
    ports_on_sphere := by
      intro z
      rw [hports,Metric.mem_sphere,dist_zero_right,hn]
      simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere z
    ports_injective := fun _ _ he => W.ports_injective (K.injective he) }
  exact ⟨A,rfl,rfl,rfl,rfl,hpull⟩



private theorem chart_axis_compare
    {S : Type} [TopologicalSpace S] (L : Set S) (p : S)
    (hp : p ∈ L) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
    (hpC : p ∈ C.source) (hpD : p ∈ D.source)
    (hC : ∀ x ∈ C.source, x ∈ L ↔ (C x).1 = 0)
    (hD : ∀ x ∈ D.source, x ∈ L ↔ (D x).1 = 0) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ C.source ∩ D.source ∧
      ∀ x ∈ U, ∀ y ∈ U, x ∉ L → y ∉ L →
        (((C x).1 < 0 ↔ (C y).1 < 0) ↔
          ((D x).1 < 0 ↔ (D y).1 < 0)) := by
  classical
  have hCp : (C p).1 = 0 := (hC p hpC).mp hp
  have hDp : (D p).1 = 0 := (hD p hpD).mp hp
  let P := C.trans (Homeomorph.addRight (-C p)).toOpenPartialHomeomorph
  let Q := D.trans (Homeomorph.addRight (-D p)).toOpenPartialHomeomorph
  have hPs : P.source = C.source := by
    ext x
    simp only [P,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  have hQs : Q.source = D.source := by
    ext x
    simp only [Q,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
  have hPf (x : S) : (P x).1 = (C x).1 := by
    change (C x).1 + -(C p).1 = (C x).1
    rw [hCp]
    simp
  have hQf (x : S) : (Q x).1 = (D x).1 := by
    change (D x).1 + -(D p).1 = (D x).1
    rw [hDp]
    simp
  have hPp : P p = (0,0) := by
    change C p + -C p = (0,0)
    exact add_neg_cancel _
  have hQp : Q p = (0,0) := by
    change D p + -D p = (0,0)
    exact add_neg_cancel _
  have hpP : p ∈ P.source := hPs.symm ▸ hpC
  have hpQ : p ∈ Q.source := hQs.symm ▸ hpD
  let T0 := P.symm.trans Q
  have hTs : (0,0) ∈ T0.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hPp ▸ P.map_source hpP,?_⟩
    change P.symm (0,0) ∈ Q.source
    rw [←hPp,P.left_inv hpP]
    exact hpQ
  have hT0 : T0 (0,0) = (0,0) := by
    change Q (P.symm (0,0)) = (0,0)
    rw [←hPp,P.left_inv hpP]
    exact hQp.trans hPp.symm
  have hTa (z : ℝ × ℝ) (hz : z ∈ T0.source) : z.1 = 0 ↔ (T0 z).1 = 0 := by
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hPinv := P.right_inv hz.1
    have hPaxis : P.symm z ∈ L ↔ z.1 = 0 := by
      have hh := hC (P.symm z) (hPs ▸ P.symm.map_source hz.1)
      rw [←hPf (P.symm z),hPinv] at hh
      exact hh
    have hQaxis : P.symm z ∈ L ↔ (Q (P.symm z)).1 = 0 := by
      rw [hQf]
      exact hD (P.symm z) (hQs ▸ hz.2)
    exact hPaxis.symm.trans hQaxis
  obtain ⟨r,hr,hball,ε,hrelative⟩ :=
    CurveComplex.LocalSurgery.local_axis_transition_side_constant T0 hTs hT0 hTa
  let U := Q.source ∩ (P.source ∩ P ⁻¹' Metric.ball (0,0) r)
  have hUopen : IsOpen U := Q.open_source.inter
    (P.isOpen_inter_preimage Metric.isOpen_ball)
  have hpU : p ∈ U := ⟨hpQ,hpP,by
    change P p ∈ Metric.ball (0,0) r
    rw [hPp]
    exact Metric.mem_ball_self hr⟩
  have hsub : U ⊆ C.source ∩ D.source := fun _ hx => ⟨hPs ▸ hx.2.1,hQs ▸ hx.1⟩
  have hlabel (x : S) (hx : x ∈ U) (hxb : x ∉ L) :
      (if 0 < (D x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (C x).1 then (1 : ZMod 2) else 0) + ε := by
    have hn : (P x).1 ≠ 0 := by
      rw [hPf]
      exact fun hh => hxb ((hC x (hPs ▸ hx.2.1)).mpr hh)
    have hh := hrelative (P x) hx.2.2 hn
    have htrans : T0 (P x) = Q x := by
      change Q (P.symm (P x)) = Q x
      rw [P.left_inv hx.2.1]
    simpa only [htrans,hPf,hQf] using hh
  refine ⟨U,hUopen,hpU,hsub,?_⟩
  intro x hx y hy hxb hyb
  have hxnC : (C x).1 ≠ 0 := fun hh => hxb ((hC x (hsub hx).1).mpr hh)
  have hynC : (C y).1 ≠ 0 := fun hh => hyb ((hC y (hsub hy).1).mpr hh)
  have hxnD : (D x).1 ≠ 0 := fun hh => hxb ((hD x (hsub hx).2).mpr hh)
  have hynD : (D y).1 ≠ 0 := fun hh => hyb ((hD y (hsub hy).2).mpr hh)
  have hlabels :
      ((if 0 < (D x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (D y).1 then (1 : ZMod 2) else 0)) ↔
      ((if 0 < (C x).1 then (1 : ZMod 2) else 0) =
        (if 0 < (C y).1 then (1 : ZMod 2) else 0)) := by
    rw [hlabel x hx hxb,hlabel y hy hyb]
    exact add_right_cancel_iff
  by_cases hcx : 0 < (C x).1 <;> by_cases hcy : 0 < (C y).1 <;>
    by_cases hdx : 0 < (D x).1 <;> by_cases hdy : 0 < (D y).1
  all_goals simp only [hcx,hcy,hdx,hdy,ite_true,ite_false] at hlabels
  all_goals have hcnegx : (C x).1 < 0 ↔ ¬0 < (C x).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnC⟩
  all_goals have hcnegy : (C y).1 < 0 ↔ ¬0 < (C y).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynC⟩
  all_goals have hdnegx : (D x).1 < 0 ↔ ¬0 < (D x).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnD⟩
  all_goals have hdnegy : (D y).1 < 0 ↔ ¬0 < (D y).1 :=
    ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynD⟩
  all_goals rw [hcnegx,hcnegy,hdnegx,hdnegy]
  all_goals simp_all


private theorem horizontal_ports_cover (u v z : Plane)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v)
    (hu1 : u 1 = 0) (hv1 : v 1 = 0) (hz : ‖z‖ ≤ 1) :
    z ∈ segment ℝ u 0 ∪ segment ℝ 0 v ↔ z 1 = 0 := by
  have hun : u ≠ 0 := by intro he; simpa [he] using hu
  have hq : u 0 ^ 2 = v 0 ^ 2 := by
    have a := EuclideanSpace.real_norm_sq_eq u
    have b := EuclideanSpace.real_norm_sq_eq v
    simp [hu,hv,hu1,hv1,Fin.sum_univ_two] at a b
    linarith
  have hvu : v = -u := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with he | he
    · exact (huv (by ext i; fin_cases i; exact he; simpa [hu1,hv1])).elim
    · ext i; fin_cases i
      · change v 0 = -u 0; linarith
      · change v 1 = -u 1; rw [hv1,hu1,neg_zero]
  rw [hvu,segment_symm ℝ u 0]
  constructor
  · rintro (⟨a,b,ha,hb,hab,he⟩ | ⟨a,b,ha,hb,hab,he⟩)
    · have := congrArg (fun z : Plane => z 1) he
      simpa [hu1] using this.symm
    · have := congrArg (fun z : Plane => z 1) he
      simpa [hu1] using this.symm
  · intro hz1
    have hd : Plane.det u z = 0 := by simp [Plane.det,hu1,hz1]
    obtain ⟨r,hr⟩ := (Plane.det_eq_zero_iff_smul u z hun).mp hd
    have hnr : |r| ≤ 1 := by
      rw [hr,norm_smul,Real.norm_eq_abs,hu,mul_one] at hz
      exact hz
    rcases le_total 0 r with hp | hm
    · left
      rw [hr]
      exact ⟨1-r,r,sub_nonneg.mpr ((le_abs_self r).trans hnr),hp,by ring,by simp⟩
    · right
      have he : z = (-r) • (-u) := by rw [hr]; module
      rw [he]
      exact ⟨1-(-r),-r,sub_nonneg.mpr ((neg_le_abs r).trans hnr),
        neg_nonneg.mpr hm,by ring,by simp⟩

private theorem window_axis_iff
    {S κ : Type} [TopologicalSpace S] {F : Set S}
    (a : κ → C(Interval,↥F)) (V : Set ↥F) (p : ↥F)
    (W : IncidentFanWindow F a V p) (i : incidentIndex a p)
    (hi0 : incidentPorts a p W.chart W.left W.right (i,false) 1 = 0)
    (hi1 : incidentPorts a p W.chart W.left W.right (i,true) 1 = 0)
    (y : ↥F) (hy : y.val ∈ W.chart.source)
    (hz : ‖W.chart y.val‖ ≤ 1) :
    y ∈ range (a i.val) ↔ W.chart y.val 1 = 0 := by
  let u := incidentPorts a p W.chart W.left W.right (i,false)
  let v := incidentPorts a p W.chart W.left W.right (i,true)
  have hu : ‖u‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,false)
  have hv : ‖v‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,true)
  have huv : u ≠ v := fun he => Bool.false_ne_true (congrArg Prod.snd (W.ports_injective he))
  have hcover := horizontal_ports_cover u v (W.chart y.val) hu hv huv hi0 hi1 hz
  constructor
  · intro hyr
    have hyc : y ∈ a i.val '' Icc (W.left i) (W.right i) :=
      W.whole_closed i ▸ ⟨⟨hy,by simpa [Metric.mem_closedBall,dist_zero_right] using hz⟩,hyr⟩
    obtain ⟨t,ht,rfl⟩ := hyc
    exact hcover.mp (W.radial_trace i ▸ ⟨t,ht,rfl⟩)
  · intro hy0
    obtain ⟨t,ht,he⟩ := W.radial_trace i |>.symm ▸ hcover.mpr hy0
    have hs : (a i.val t).val ∈ W.chart.source :=
      (W.whole_closed i |>.symm ▸ (show a i.val t ∈ a i.val '' Icc (W.left i) (W.right i) from ⟨t,ht,rfl⟩)).1.1
    exact ⟨t,Subtype.ext (W.chart.injOn hs hy he)⟩


private theorem isolated_axis_iff
    {S : Type} [TopologicalSpace S] {F : Set S}
    {a b : C(Interval,↥F)} {r s : Interval}
    (C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s)
    (y : ↥F) (hy : y.val ∈ C.chart.source)
    (hz : C.chart y.val ∈ Plane.closedSquare 0 1) :
    y ∈ range a ↔ C.chart y.val 1 = 0 := by
  constructor
  · intro hyr
    have hyc : y ∈ a '' Icc C.aLeft C.aRight := C.whole_a_trace ▸ ⟨⟨hy,hz⟩,hyr⟩
    obtain ⟨t,ht,hey⟩ := hyc
    have hm : C.chart y.val ∈ (fun t => C.chart (a t).val) '' Icc C.aLeft C.aRight :=
      ⟨t,ht,congrArg (fun y : ↥F => C.chart y.val) hey⟩
    exact (C.anchor_diameter ▸ hm).2
  · intro hy0
    obtain ⟨t,ht,he⟩ := C.anchor_diameter |>.symm ▸ (show C.chart y.val ∈
      {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z 1=0} from ⟨hz,hy0⟩)
    have hs : (a t).val ∈ C.chart.source :=
      (C.whole_a_trace |>.symm ▸ (show a t ∈ a '' Icc C.aLeft C.aRight from ⟨t,ht,rfl⟩)).1.1
    exact ⟨t,Subtype.ext (C.chart.injOn hs hy he)⟩

private def plane_swap_coordinates : Plane ≃ₜ (ℝ × ℝ) where
  toEquiv := {
    toFun := fun z => (z 1,z 0)
    invFun := fun z => Plane.mk z.2 z.1
    left_inv := by intro z; ext i; fin_cases i <;> rfl
    right_inv := by intro z; rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem two_sided_germ_sample
    {S : Type} [TopologicalSpace S] (f : Interval → S) (hf : Continuous f)
    (U : Set S) (hU : IsOpen U) (c l r : Interval)
    (hl : l < c) (hr : c < r) (hc : f c ∈ U) :
    ∃ t ∈ Ioo l c, ∃ u ∈ Ioo c r, f t ∈ U ∧ f u ∈ U := by
  have hn : f ⁻¹' U ∈ nhds c := (hU.preimage hf).mem_nhds hc
  obtain ⟨a,b,ha,hb⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨l,hl⟩ ⟨r,hr⟩).mp hn
  obtain ⟨t,hmt,htc⟩ := exists_between (max_lt ha.1 hl)
  obtain ⟨u,hcu,hum⟩ := exists_between (lt_min ha.2 hr)
  exact ⟨t,⟨(le_max_right a l).trans_lt hmt,htc⟩,
    u,⟨hcu,hum.trans_le (min_le_right b r)⟩,
    hb ⟨(le_max_left a l).trans_lt hmt,htc.trans ha.2⟩,
    hb ⟨ha.1.trans hcu,hum.trans_le (min_le_left b r)⟩⟩


private theorem window_branch_positive_scalar
    {S κ : Type} [TopologicalSpace S] {F : Set S}
    (a : κ → C(Interval,↥F)) (ha : ∀ i, IsEmbedding (a i))
    (V : Set ↥F) (p : ↥F) (W : IncidentFanWindow F a V p)
    (i : incidentIndex a p) (t : Interval) (b : Bool)
    (ht : if b then t ∈ Ioo (W.center i) (W.right i) else t ∈ Ioo (W.left i) (W.center i)) :
    ∃ r : ℝ, 0 < r ∧ W.chart (a i.val t).val =
      r • incidentPorts a p W.chart W.left W.right (i,b) := by
  have hclosed : t ∈ Icc (W.left i) (W.right i) := by
    cases b
    · exact ⟨ht.1.le,ht.2.le.trans (W.cuts i).2.2.1.le⟩
    · exact ⟨(W.cuts i).2.1.le.trans ht.1.le,ht.2.le⟩
  have hs : (a i.val t).val ∈ W.chart.source :=
    (W.whole_closed i |>.symm ▸ (show a i.val t ∈ a i.val '' Icc (W.left i) (W.right i)
      from ⟨t,hclosed,rfl⟩)).1.1
  have htne : t ≠ W.center i := by cases b; exact ht.2.ne; exact ht.1.ne'
  have hn : W.chart (a i.val t).val ≠ 0 := by
    intro hz
    have he := W.chart.injOn hs W.contact_in_source (hz.trans W.contact_zero.symm)
    exact htne ((ha i.val).injective ((Subtype.ext he).trans (W.at_center i).symm))
  have him := window_branch_images a ha V p W i
  have hm : W.chart (a i.val t).val ∈
      segment ℝ 0 (incidentPorts a p W.chart W.left W.right (i,b)) := by
    cases b
    · rw [segment_symm ℝ 0 _]
      exact him.1 ▸ ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
    · exact him.2 ▸ ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  obtain ⟨x,r,hx,hr,hxr,he⟩ := hm
  have her : W.chart (a i.val t).val = r • incidentPorts a p W.chart W.left W.right (i,b) :=
    by simpa using he.symm
  have hr0 : r ≠ 0 := by intro hz; rw [her,hz,zero_smul] at hn; exact hn rfl
  exact ⟨r,lt_of_le_of_ne hr hr0.symm,her⟩


private theorem window_opposite_port_signs
    {S κ : Type} [TopologicalSpace S] {F : Set S}
    (a : κ → C(Interval,↥F)) (ha : ∀ i, IsEmbedding (a i))
    (V : Set ↥F) (p : ↥F) (W : IncidentFanWindow F a V p)
    (i j : incidentIndex a p) (hij : i ≠ j)
    (hi0 : incidentPorts a p W.chart W.left W.right (i,false) 1 = 0)
    (hi1 : incidentPorts a p W.chart W.left W.right (i,true) 1 = 0)
    (C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F
      (a i.val) (a j.val) (W.center i) (W.center j)) (hC : C.OppositeSides) :
    ((0 < incidentPorts a p W.chart W.left W.right (j,false) 1 ∧
      incidentPorts a p W.chart W.left W.right (j,true) 1 < 0) ∨
     (incidentPorts a p W.chart W.left W.right (j,false) 1 < 0 ∧
      0 < incidentPorts a p W.chart W.left W.right (j,true) 1)) := by
  let L : Set S := range (fun t => (a i.val t).val)
  have hL (y : ↥F) : y.val ∈ L ↔ y ∈ range (a i.val) := by
    constructor
    · rintro ⟨t,he⟩; exact ⟨t,Subtype.ext he⟩
    · rintro ⟨t,he⟩; exact ⟨t,congrArg Subtype.val he⟩
  let Uc : Set S := C.chart.source ∩ C.chart ⁻¹' Plane.openSquare 0 1
  let Uw : Set S := W.chart.source ∩ W.chart ⁻¹' Metric.ball (0:Plane) 1
  have hUc : IsOpen Uc := C.chart.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)
  have hUw : IsOpen Uw := W.chart.isOpen_inter_preimage Metric.isOpen_ball
  let E := (C.chart.restr Uc).trans plane_swap_coordinates.toOpenPartialHomeomorph
  let D := (W.chart.restr Uw).trans plane_swap_coordinates.toOpenPartialHomeomorph
  have hEs : E.source = Uc := by
    calc E.source = (C.chart.restr Uc).source := by simp [E]
         _ = C.chart.source ∩ Uc := C.chart.restr_source' Uc hUc
         _ = Uc := inter_eq_right.mpr inter_subset_left
  have hDs : D.source = Uw := by
    calc D.source = (W.chart.restr Uw).source := by simp [D]
         _ = W.chart.source ∩ Uw := W.chart.restr_source' Uw hUw
         _ = Uw := inter_eq_right.mpr inter_subset_left
  have hEf (x : S) : (E x).1 = C.chart x 1 := rfl
  have hDf (x : S) : (D x).1 = W.chart x 1 := rfl
  have hpCs : p.val ∈ C.chart.source := by
    have hh : a i.val (W.center i) ∈ a i.val '' Icc C.aLeft C.aRight :=
      ⟨W.center i,⟨C.a_cuts.2.1.le,C.a_cuts.2.2.1.le⟩,rfl⟩
    have hs := (C.whole_a_trace.symm ▸ hh).1.1
    rwa [W.at_center] at hs
  have hCp : C.chart p.val=0 :=
    (congrArg (fun y : ↥F => C.chart y.val) (W.at_center i)).symm.trans C.contact_at_origin
  have hpE : p.val ∈ E.source := by
    rw [hEs]
    refine ⟨hpCs,?_⟩
    change C.chart p.val ∈ Plane.openSquare 0 1
    rw [hCp]
    exact Plane.mem_openSquare_self (by norm_num)
  have hpD : p.val ∈ D.source := by
    rw [hDs]
    refine ⟨W.contact_in_source,?_⟩
    change W.chart p.val ∈ Metric.ball (0:Plane) 1
    rw [W.contact_zero]
    exact Metric.mem_ball_self (by norm_num)
  have hEaxis (x : S) (hx : x ∈ E.source) : x ∈ L ↔ (E x).1=0 := by
    rw [hEs] at hx
    have hz := Plane.openSquare_subset_closedSquare 0 1 hx.2
    let y : ↥F := ⟨x,interior_subset (C.closed_support_interior ⟨hx.1,hz⟩)⟩
    exact (hL y).trans (isolated_axis_iff C y hx.1 hz)
  have hDaxis (x : S) (hx : x ∈ D.source) : x ∈ L ↔ (D x).1=0 := by
    rw [hDs] at hx
    let y : ↥F := ⟨x,interior_subset (W.source_closure (subset_closure hx.1)).2⟩
    have hz : ‖W.chart x‖ ≤ 1 := by
      have : W.chart x ∈ Metric.ball (0:Plane) 1 := hx.2
      exact (show ‖W.chart x‖ < 1 from by simpa [Metric.mem_ball,dist_zero_right] using this).le
    exact (hL y).trans (window_axis_iff a V p W i hi0 hi1 y hx.1 hz)
  obtain ⟨U,hU,hpU,hsub,hcomp⟩ := chart_axis_compare L p.val
    ((hL p).mpr ⟨W.center i,W.at_center i⟩) E D hpE hpD hEaxis hDaxis
  have hcl : max (W.left j) C.bLeft < W.center j := max_lt (W.cuts j).2.1 C.b_cuts.2.1
  have hcr : W.center j < min (W.right j) C.bRight := lt_min (W.cuts j).2.2.1 C.b_cuts.2.2.1
  obtain ⟨t,ht,u,hu,htU,huU⟩ := two_sided_germ_sample
    (fun t => (a j.val t).val) (continuous_subtype_val.comp (a j.val).continuous)
    U hU (W.center j) (max (W.left j) C.bLeft) (min (W.right j) C.bRight)
    hcl hcr (by rw [W.at_center]; exact hpU)
  have htW : t ∈ Ioo (W.left j) (W.center j) := ⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩
  have huW : u ∈ Ioo (W.center j) (W.right j) := ⟨hu.1,hu.2.trans_le (min_le_left _ _)⟩
  have htC : t ∈ Ioo C.bLeft (W.center j) := ⟨(le_max_right _ _).trans_lt ht.1,ht.2⟩
  have huC : u ∈ Ioo (W.center j) C.bRight := ⟨hu.1,hu.2.trans_le (min_le_right _ _)⟩
  have htNot : (a j.val t).val ∉ L := by
    intro he
    exact ht.2.ne ((C.only_contact t ⟨htC.1.le,(htC.2.trans C.b_cuts.2.2.1).le⟩).mp ((hL _).mp he))
  have huNot : (a j.val u).val ∉ L := by
    intro he
    exact hu.1.ne' ((C.only_contact u ⟨(C.b_cuts.2.1.trans huC.1).le,huC.2.le⟩).mp ((hL _).mp he))
  have hcneg : ¬(C.chart (a j.val t).val 1 < 0 ↔ C.chart (a j.val u).val 1 < 0) := by
    rcases hC with ⟨hbefore,hafter⟩ | ⟨hbefore,hafter⟩
    · intro he; exact (not_lt_of_ge (hbefore t htC).le) (he.mpr (hafter u huC))
    · intro he; exact (not_lt_of_ge (hafter u huC).le) (he.mp (hbefore t htC))
  have hwneg : ¬(W.chart (a j.val t).val 1 < 0 ↔ W.chart (a j.val u).val 1 < 0) := by
    intro he
    exact hcneg ((hcomp _ htU _ huU htNot huNot).mpr he)
  obtain ⟨r,hr,htr⟩ := window_branch_positive_scalar a ha V p W j t false htW
  obtain ⟨s,hs,hus⟩ := window_branch_positive_scalar a ha V p W j u true huW
  let before := incidentPorts a p W.chart W.left W.right (j,false) 1
  let after := incidentPorts a p W.chart W.left W.right (j,true) 1
  have htr1 : W.chart (a j.val t).val 1 = r*before := congrArg (fun z : Plane => z 1) htr
  have hus1 : W.chart (a j.val u).val 1 = s*after := congrArg (fun z : Plane => z 1) hus
  have hbne : before ≠ 0 := by
    intro he
    have hz : (D (a j.val t).val).1=0 := by rw [hDf,htr1,he,mul_zero]
    exact htNot ((hDaxis _ (hsub htU).2).mpr hz)
  have hane : after ≠ 0 := by
    intro he
    have hz : (D (a j.val u).val).1=0 := by rw [hDf,hus1,he,mul_zero]
    exact huNot ((hDaxis _ (hsub huU).2).mpr hz)
  have hneg : ¬(before < 0 ↔ after < 0) := by
    intro he
    apply hwneg
    have hrt : r*before < 0 ↔ before < 0 := by
      simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hr : r*before < r*0 ↔ before < 0)
    have hst : s*after < 0 ↔ after < 0 := by
      simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hs : s*after < s*0 ↔ after < 0)
    rwa [htr1,hus1,hrt,hst]
  by_cases hb : before < 0
  · right
    refine ⟨hb,lt_of_le_of_ne (le_of_not_gt ?_) hane.symm⟩
    intro he
    exact hneg ⟨fun _ => he,fun _ => hb⟩
  · left
    refine ⟨lt_of_le_of_ne (le_of_not_gt hb) hbne.symm,?_⟩
    by_contra he
    exact hneg ⟨fun h => (hb h).elim,fun h => (he h).elim⟩


private theorem isolated_opposite_invariant
    {S : Type} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval,↥F)) (r s : Interval)
    (C D : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s)
    (hC : C.OppositeSides) (hD : D.SameSide ∨ D.OppositeSides) : D.OppositeSides := by
  rcases hD with hD | hD
  swap
  · exact hD
  exfalso
  let p := a r
  let L : Set S := range (fun t => (a t).val)
  have hL (y : ↥F) : y.val ∈ L ↔ y ∈ range a := by
    constructor
    · rintro ⟨t,he⟩; exact ⟨t,Subtype.ext he⟩
    · rintro ⟨t,he⟩; exact ⟨t,congrArg Subtype.val he⟩
  let restricted (E : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s) :=
    (E.chart.restr (E.chart.source ∩ E.chart ⁻¹' Plane.openSquare 0 1)).trans
      plane_swap_coordinates.toOpenPartialHomeomorph
  have hrs (E : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s) :
      (restricted E).source = E.chart.source ∩ E.chart ⁻¹' Plane.openSquare 0 1 := by
    let U := E.chart.source ∩ E.chart ⁻¹' Plane.openSquare 0 1
    have hU : IsOpen U := E.chart.isOpen_inter_preimage (Plane.isOpen_openSquare 0 1)
    calc (restricted E).source = (E.chart.restr U).source := by simp [restricted,U]
         _ = E.chart.source ∩ U := E.chart.restr_source' U hU
         _ = U := inter_eq_right.mpr inter_subset_left
  have hpR (E : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s) :
      p.val ∈ (restricted E).source := by
    rw [hrs]
    have hh : a r ∈ a '' Icc E.aLeft E.aRight :=
      ⟨r,⟨E.a_cuts.2.1.le,E.a_cuts.2.2.1.le⟩,rfl⟩
    refine ⟨(E.whole_a_trace.symm ▸ hh).1.1,?_⟩
    change E.chart (a r).val ∈ Plane.openSquare 0 1
    rw [E.contact_at_origin]
    exact Plane.mem_openSquare_self (by norm_num)
  have haxis (E : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s)
      (x : S) (hx : x ∈ (restricted E).source) : x ∈ L ↔ (restricted E x).1=0 := by
    rw [hrs] at hx
    have hz := Plane.openSquare_subset_closedSquare 0 1 hx.2
    let y : ↥F := ⟨x,interior_subset (E.closed_support_interior ⟨hx.1,hz⟩)⟩
    exact (hL y).trans (isolated_axis_iff E y hx.1 hz)
  obtain ⟨U,hU,hpU,hsub,hcomp⟩ := chart_axis_compare L p.val ⟨r,rfl⟩
    (restricted C) (restricted D) (hpR C) (hpR D) (haxis C) (haxis D)
  obtain ⟨t,ht,u,hu,htU,huU⟩ := two_sided_germ_sample
    (fun t => (b t).val) (continuous_subtype_val.comp b.continuous)
    U hU s (max C.bLeft D.bLeft) (min C.bRight D.bRight)
    (max_lt C.b_cuts.2.1 D.b_cuts.2.1) (lt_min C.b_cuts.2.2.1 D.b_cuts.2.2.1)
    (by change (b s).val ∈ U; rw [←C.contact]; exact hpU)
  have htC : t ∈ Ioo C.bLeft s := ⟨(le_max_left _ _).trans_lt ht.1,ht.2⟩
  have huC : u ∈ Ioo s C.bRight := ⟨hu.1,hu.2.trans_le (min_le_left _ _)⟩
  have htD : t ∈ Ioo D.bLeft s := ⟨(le_max_right _ _).trans_lt ht.1,ht.2⟩
  have huD : u ∈ Ioo s D.bRight := ⟨hu.1,hu.2.trans_le (min_le_right _ _)⟩
  have htNot : (b t).val ∉ L := by
    intro he
    exact ht.2.ne ((C.only_contact t ⟨htC.1.le,(htC.2.trans C.b_cuts.2.2.1).le⟩).mp ((hL _).mp he))
  have huNot : (b u).val ∉ L := by
    intro he
    exact hu.1.ne' ((C.only_contact u ⟨(C.b_cuts.2.1.trans huC.1).le,huC.2.le⟩).mp ((hL _).mp he))
  have he : (C.chart (b t).val 1 < 0 ↔ C.chart (b u).val 1 < 0) ↔
      (D.chart (b t).val 1 < 0 ↔ D.chart (b u).val 1 < 0) :=
    hcomp _ htU _ huU htNot huNot
  have hd : D.chart (b t).val 1 < 0 ↔ D.chart (b u).val 1 < 0 := by
    rcases hD with ⟨hbefore,hafter⟩ | ⟨hbefore,hafter⟩
    · exact ⟨fun h => (not_lt_of_ge (hbefore t htD).le h).elim,
        fun h => (not_lt_of_ge (hafter u huD).le h).elim⟩
    · exact ⟨fun _ => hafter u huD,fun _ => hbefore t htD⟩
  have hc := he.mpr hd
  rcases hC with ⟨hbefore,hafter⟩ | ⟨hbefore,hafter⟩
  · exact not_lt_of_ge (hbefore t htC).le (hc.mpr (hafter u huC))
  · exact not_lt_of_ge (hafter u huC).le (hc.mp (hbefore t htC))


private theorem interior_union_nowhereDense_subset_closure
    {S : Type} [TopologicalSpace S] (U B : Set S) (hB : IsNowhereDense B) :
    interior (U ∪ B) ⊆ closure U := by
  intro x hx
  by_contra hn
  have hopen : IsOpen (interior (U ∪ B) ∩ (closure U)ᶜ) :=
    isOpen_interior.inter isClosed_closure.isOpen_compl
  have hsub : interior (U ∪ B) ∩ (closure U)ᶜ ⊆ B := by
    intro y hy
    rcases interior_subset hy.1 with h | h
    · exact (hy.2 (subset_closure h)).elim
    · exact h
  have hy : x ∈ interior (closure B) :=
    interior_mono subset_closure (hopen.subset_interior_iff.mpr hsub ⟨hx,hn⟩)
  rw [hB] at hy
  exact hy

private theorem supported_isolated_chart
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (a b : C(Interval,↥F)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hfinite : (range a ∩ range b).Finite) (r s : Interval)
    (hr : r ∈ Ioo (0:Interval) 1) (hs : s ∈ Ioo (0:Interval) 1) (hrs : a r = b s)
    (V : Set ↥F) (U : Set S) (hU : IsOpen U) (hpU : (a r).val ∈ U)
    (hUF : U ⊆ F) (hclose : closure U ⊆ Subtype.val '' V) :
    ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s,
      (C.SameSide ∨ C.OppositeSides) ∧
      {y : ↥F | y.val ∈ C.chart.source ∧ C.chart y.val ∈ Plane.closedSquare 0 1} ⊆ V := by
  let fa : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
  let fb : C(Interval,S) := ⟨fun t => (b t).val,continuous_subtype_val.comp b.continuous⟩
  have hfa : IsEmbedding fa := IsEmbedding.subtypeVal.comp ha
  have hfb : IsEmbedding fb := IsEmbedding.subtypeVal.comp hb
  let B : Set S := range fa ∪ range fb
  have hB : IsNowhereDense B :=
    (source_actual_embedded_arc_nowhere_dense fa hfa).union
      (source_actual_embedded_arc_nowhere_dense fb hfb)
  let G : Set S := U ∪ B
  have hGF : G ⊆ F := by
    intro x hx
    rcases hx with hx | hx
    · exact hUF hx
    · rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩ <;> exact Subtype.coe_prop _
  let ag : C(Interval,↥G) := ⟨fun t => ⟨fa t,Or.inr (Or.inl (mem_range_self t))⟩,
    fa.continuous.subtype_mk _⟩
  let bg : C(Interval,↥G) := ⟨fun t => ⟨fb t,Or.inr (Or.inr (mem_range_self t))⟩,
    fb.continuous.subtype_mk _⟩
  have hag : IsEmbedding ag := hfa.codRestrict G _
  have hbg : IsEmbedding bg := hfb.codRestrict G _
  have hfiniteg : (range ag ∩ range bg).Finite := by
    have hfin : (range fa ∩ range fb).Finite := by
      have he : range fa ∩ range fb = Subtype.val '' (range a ∩ range b) := by
        ext x; constructor
        · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
          refine ⟨a t,⟨mem_range_self t,⟨u,Subtype.ext (hu.trans ht.symm)⟩⟩,ht⟩
        · rintro ⟨y,⟨⟨t,ht⟩,⟨u,hu⟩⟩,rfl⟩
          exact ⟨⟨t,congrArg Subtype.val ht⟩,⟨u,congrArg Subtype.val hu⟩⟩
      rw [he]; exact hfinite.image _
    exact (hfin.preimage Subtype.val_injective.injOn).subset
      (fun x hx => ⟨by obtain ⟨t,ht⟩:=hx.1; exact ⟨t,congrArg Subtype.val ht⟩,
        by obtain ⟨t,ht⟩:=hx.2; exact ⟨t,congrArg Subtype.val ht⟩⟩)
  have hrsg : ag r = bg s := Subtype.ext (show (ag r).val=(bg s).val from congrArg (fun y : ↥F => y.val) hrs)
  have hpG : (ag r).val ∈ interior G :=
    hU.subset_interior_iff.mpr subset_union_left hpU
  obtain ⟨D,hD⟩ := RegionalEmbeddedFamily.regional_finite_contact_has_isolated_contact_chart
    G ag bg hag hbg hfiniteg r s hr hs hrsg hpG
  have hinG : interior G ⊆ closure U := interior_union_nowhereDense_subset_closure U B hB
  have hwhole (f : C(Interval,↥F)) (fg : C(Interval,↥G))
      (hfg : ∀ t, (fg t).val = (f t).val) (l q : Interval)
      (hw : ({y : ↥G | y.val ∈ D.chart.source ∧ D.chart y.val ∈ Plane.closedSquare 0 1} ∩
        range fg) = fg '' Icc l q) :
      ({y : ↥F | y.val ∈ D.chart.source ∧ D.chart y.val ∈ Plane.closedSquare 0 1} ∩
        range f) = f '' Icc l q := by
    ext y
    constructor
    · rintro ⟨hy,⟨t,ht⟩⟩
      have hyt : fg t ∈ {y : ↥G | y.val ∈ D.chart.source ∧ D.chart y.val ∈ Plane.closedSquare 0 1} ∩ range fg := by
        refine ⟨?_,mem_range_self t⟩
        change (fg t).val ∈ D.chart.source ∧ D.chart (fg t).val ∈ Plane.closedSquare 0 1
        rw [hfg t,ht]
        exact hy
      obtain ⟨u,hu,heu⟩ := hw ▸ hyt
      refine ⟨u,hu,?_⟩
      apply Subtype.ext
      exact (hfg u).symm.trans ((congrArg Subtype.val heu).trans ((hfg t).trans (congrArg Subtype.val ht)))
    · rintro ⟨t,ht,rfl⟩
      have hyt : fg t ∈ {y : ↥G | y.val ∈ D.chart.source ∧ D.chart y.val ∈ Plane.closedSquare 0 1} ∩ range fg :=
        hw.symm ▸ (show fg t ∈ fg '' Icc l q from ⟨t,ht,rfl⟩)
      exact ⟨by
        change (f t).val ∈ D.chart.source ∧ D.chart (f t).val ∈ Plane.closedSquare 0 1
        have hh : (fg t).val ∈ D.chart.source ∧ D.chart (fg t).val ∈ Plane.closedSquare 0 1 := hyt.1
        rwa [hfg t] at hh,mem_range_self t⟩
  let C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F a b r s := {
    chart := D.chart
    aLeft := D.aLeft
    aRight := D.aRight
    bLeft := D.bLeft
    bRight := D.bRight
    r_interior := hr
    s_interior := hs
    contact := hrs
    a_cuts := D.a_cuts
    b_cuts := D.b_cuts
    square_in_target := D.square_in_target
    closed_support_interior := D.closed_support_interior.trans (interior_mono hGF)
    whole_a_trace := hwhole a ag (fun _ => rfl) _ _ D.whole_a_trace
    whole_b_trace := hwhole b bg (fun _ => rfl) _ _ D.whole_b_trace
    anchor_diameter := D.anchor_diameter
    contact_at_origin := D.contact_at_origin
    b_open_inside := D.b_open_inside
    b_left_boundary := D.b_left_boundary
    b_right_boundary := D.b_right_boundary
    only_contact := by
      intro t ht
      have he : b t ∈ range a ↔ bg t ∈ range ag := by
        constructor
        · rintro ⟨u,hu⟩; exact ⟨u,Subtype.ext (show (ag u).val=(bg t).val from
            congrArg (fun y : ↥F => y.val) hu)⟩
        · rintro ⟨u,hu⟩; exact ⟨u,Subtype.ext (show (a u).val=(b t).val from
            congrArg (fun y : ↥G => y.val) hu)⟩
      exact he.trans (D.only_contact t ht) }
  refine ⟨C,hD,?_⟩
  intro y hy
  obtain ⟨z,hz,he⟩ := hclose (hinG (D.closed_support_interior hy))
  exact Subtype.val_injective he ▸ hz



open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact ordinary M0 fan-window transport: the already-paid event, endpoint,
accounting and continuous whole-trace pieces stay in the caller; this is the remaining window,
selected-axis-sign and in-V isolated-chart construction. -/
theorem regional_paired_disk_fan_window_geometry
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (ι : Type) [Fintype ι] (r : ι → IntrinsicEssentialArc)
      (α : IntrinsicEssentialArc),
      FamilyInvariant (fun i => (r i).val.val) α.val.val →
      (∀ i j : Option ι, i ≠ j →
        RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
          (augmented (fun i => (r i).val.val) α.val.val i)
          (augmented (fun i => (r i).val.val) α.val.val j)) →
      ∀ v w : ι, v ≠ w →
      ∀ d : PairedBigonDisk F {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        (∀ y ∈ closure V, y.val ∈ interior F) →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 0,d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        let a : Option ι → C(Interval,↥F) :=
          augmented (fun i => (r i).val.val) α.val.val
        let events : Set ↥F :=
          contactSites F a {some v,some w} (range d.first ∪ range d.second) V
        ∃ window : ∀ p : ↥events, IncidentFanWindow F a V p.val,
            (∀ p q : ↥events, p ≠ q →
              Disjoint (RegionalChordNormalization.chartPull F (window p).chart
                (Metric.closedBall (0 : Plane) 1))
                (RegionalChordNormalization.chartPull F (window q).chart
                (Metric.closedBall (0 : Plane) 1))) ∧
            (∀ p : ↥events, ∀ i, i ∈ ({some v,some w} : Set (Option ι)) →
              ∀ hip : p.val ∈ range (a i),
              ∃ A : IncidentFanWindow F a V p.val,
                RegionalChordNormalization.chartPull F A.chart
                    (Metric.closedBall (0 : Plane) 1) ⊆
                  RegionalChordNormalization.chartPull F (window p).chart
                    (Metric.ball (0 : Plane) 1) ∧
                incidentPorts a p.val A.chart A.left A.right
                    (⟨i,hip⟩,false) 1 = 0 ∧
                incidentPorts a p.val A.chart A.left A.right
                    (⟨i,hip⟩,true) 1 = 0 ∧
                ∀ j : incidentIndex a p.val, j.val ≠ i →
                  ((0 < incidentPorts a p.val A.chart A.left A.right (j,false) 1 ∧
                    incidentPorts a p.val A.chart A.left A.right (j,true) 1 < 0) ∨
                   (incidentPorts a p.val A.chart A.left A.right (j,false) 1 < 0 ∧
                    0 < incidentPorts a p.val A.chart A.left A.right (j,true) 1))) ∧
            (∀ p : ↥events, ∀ i j, i ≠ j →
              (i ∈ ({some v,some w} : Set (Option ι)) ∨
                j ∈ ({some v,some w} : Set (Option ι))) →
              ∀ u t : Interval, u ∈ Ioo (0 : Interval) 1 →
                t ∈ Ioo (0 : Interval) 1 →
                a i u = p.val → a j t = p.val →
                ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F
                    (a i) (a j) u t,
                  C.OppositeSides ∧
                  {y : ↥F | y.val ∈ C.chart.source ∧
                    C.chart y.val ∈ Plane.closedSquare 0 1} ⊆ V) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV hVinside havoid
    C₀ removed guiding offset a events
  letI : ClosedSurface S := Classical.choice hS.2.1
  have haugEmb : ∀ i : Option ι, IsEmbedding (a i) := by
    intro i
    cases i with
    | none => exact α.val.property.1
    | some i => exact (r i).val.property.1
  have haugFinite : ∀ i j : Option ι, i ≠ j → (range (a i) ∩ range (a j)).Finite := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hinv.2.2.2.2 j
    | some i =>
      cases j with
      | none => exact (hinv.2.2.2.2 i).subset (fun y hy => ⟨hy.2,hy.1⟩)
      | some j => exact hinv.1 i j (fun he => hij (congrArg some he))
  let contacts : Set ↥F := ⋃ i : Option ι, ⋃ j : Option ι,
    if i = j then ∅ else range (a i) ∩ range (a j)
  have hcontacts : contacts.Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.finite_iUnion
    intro j
    split_ifs with he
    · exact Set.finite_empty
    · exact haugFinite i j he
  have hevents : events ⊆ contacts := by
    intro p hp
    obtain ⟨hpV,hps,i,hi,j,hij,hpij⟩ := hp
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,by simpa [hij] using hpij⟩⟩
  have heventsFinite : events.Finite := hcontacts.subset hevents
  letI : Fintype ↥events := heventsFinite.fintype
  have hpInterior (p : ↥events) : p.val.val ∈ interior F :=
    hVinside p.val (subset_closure p.property.1)
  have hBF : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  have hendpoints (i : Option ι) :
      (a i 0).val ∈ frontier F ∧ (a i 1).val ∈ frontier F := by
    cases i with
    | none => exact ⟨hBF α.val.property.2.1,hBF α.val.property.2.2.1⟩
    | some i => exact ⟨hBF (r i).val.property.2.1,hBF (r i).val.property.2.2.1⟩
  have hparam (p : ↥events) (i : Option ι) (hip : p.val ∈ range (a i)) :
      ∃ τ ∈ Ioo (0 : Interval) 1, a i τ = p.val := by
    obtain ⟨τ,hτ⟩ := hip
    have hpOff : p.val.val ∉ frontier F := fun h => h.2 (hpInterior p)
    have hτ0 : τ ≠ 0 := by
      intro he
      exact hpOff (hτ ▸ (he ▸ (hendpoints i).1))
    have hτ1 : τ ≠ 1 := by
      intro he
      exact hpOff (hτ ▸ (he ▸ (hendpoints i).2))
    exact ⟨τ,⟨lt_of_le_of_ne bot_le (Ne.symm hτ0),
      lt_of_le_of_ne le_top hτ1⟩,hτ⟩
  obtain ⟨O,hO,hOF,hpO,hOV⟩ := relative_open_interior_neighborhood F V hV
  obtain ⟨sep,hsepOpen,hsepDisjoint⟩ := finite_point_neighborhoods
    (fun p : ↥events => p.val.val) (Subtype.val_injective.comp Subtype.val_injective)
  let bad : Set S := Subtype.val '' contacts
  have hbad : bad.Finite := hcontacts.image Subtype.val
  have hsmall (p : ↥events) : ∃ N : Set S,
      IsOpen N ∧ p.val.val ∈ N ∧
      closure N ⊆ (O ∩ sep p) \ (bad \ {p.val.val}) := by
    have hopen : IsOpen ((O ∩ sep p) \ (bad \ {p.val.val})) :=
      (hO.inter (hsepOpen p).1).sdiff hbad.sdiff.isClosed
    have hp : p.val.val ∈ (O ∩ sep p) \ (bad \ {p.val.val}) :=
      ⟨⟨hpO p.val p.property.1 (hpInterior p),(hsepOpen p).2⟩,
        fun h => h.2 (mem_singleton _)⟩
    obtain ⟨N,hN,hpN,hclose,hcompact⟩ :=
      exists_open_between_and_isCompact_closure (show IsCompact ({p.val.val} : Set S) from isCompact_singleton)
        hopen (singleton_subset_iff.mpr hp)
    exact ⟨N,hN,hpN (mem_singleton _),hclose⟩
  choose N hN hpN hNclose using hsmall
  have hNF (p : ↥events) : N p ⊆ interior F :=
    subset_closure.trans ((hNclose p).trans (fun x hx => hOF hx.1.1))
  have hOnly (p : ↥events) (i j : Option ι) (hij : i ≠ j)
      (y : ↥F) (hy : y ∈ range (a i) ∩ range (a j)) (hyN : y.val ∈ N p) : y = p.val := by
    have hybad : y.val ∈ bad := ⟨y,mem_iUnion.mpr
      ⟨i,mem_iUnion.mpr ⟨j,by simpa [hij] using hy⟩⟩,rfl⟩
    have hyavoid := ((hNclose p) (subset_closure hyN)).2
    by_contra he
    exact hyavoid ⟨hybad,fun hx => he (Subtype.ext (mem_singleton_iff.mp hx))⟩
  have hOne (p : ↥events) (U : Set S) (hU : IsOpen U) (hpU : p.val.val ∈ U)
      (hUN : U ⊆ N p) : ∃ W : IncidentFanWindow F a V p.val,
      W.chart.source ⊆ U := by
    obtain ⟨i,hi,j,hij,hpij⟩ := p.property.2.2
    obtain ⟨e,l,r₀,τ,hsource,hcenter,htarget,hcuts,hτ,hclosed,hopen,hradial,haway,hsphere,hinj⟩ :=
      regional_finite_incident_whole_trace_disk S g hg hS x R hR htarget F hFcompact
        hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        (Option ι) a haugEmb haugFinite p.val ⟨i,j,hij,hpij⟩ (hparam p)
        U hU hpU (hUN.trans (hNF p)) (fun i j hij y hy hyU => hOnly p i j hij y hy (hUN hyU))
    refine ⟨{
      chart := e
      source_closure := ?_
      contact_in_source := hcenter.1
      contact_zero := hcenter.2
      disk_in_target := htarget
      left := l
      right := r₀
      center := τ
      cuts := hcuts
      at_center := hτ
      whole_closed := hclosed
      whole_open := hopen
      radial_trace := hradial
      nonincident_clear := haway
      ports_on_sphere := hsphere
      ports_injective := hinj },hsource⟩
    intro y hy
    have hh := (hNclose p) (closure_mono (hsource.trans hUN) hy)
    exact ⟨hOV hh.1.1,hOF hh.1.1⟩
  choose window hwindowN using (fun p => hOne p (N p) (hN p) (hpN p) Subset.rfl)
  refine ⟨window,?_,?_,?_⟩
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro y hp hq
    exact Set.disjoint_left.mp (hsepDisjoint p q hpq)
      (((hNclose p) (subset_closure (hwindowN p hp.1))).1.2)
      (((hNclose q) (subset_closure (hwindowN q hq.1))).1.2)
  · intro p i hi hip
    let W := window p
    let U : Set S := (W.chart.source ∩ W.chart ⁻¹' Metric.ball (0:Plane) 1) ∩ N p
    have hU : IsOpen U := (W.chart.isOpen_inter_preimage Metric.isOpen_ball).inter (hN p)
    have hpU : p.val.val ∈ U := by
      refine ⟨⟨W.contact_in_source,?_⟩,hpN p⟩
      change W.chart p.val.val ∈ Metric.ball (0:Plane) 1
      rw [W.contact_zero]
      exact Metric.mem_ball_self (by norm_num)
    obtain ⟨B,hBU⟩ := hOne p U hU hpU inter_subset_right
    let k : incidentIndex a p.val := ⟨i,hip⟩
    let u := incidentPorts a p.val B.chart B.left B.right (k,false)
    let z := incidentPorts a p.val B.chart B.left B.right (k,true)
    have hu : ‖u‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using B.ports_on_sphere (k,false)
    have hz : ‖z‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using B.ports_on_sphere (k,true)
    have huz : u ≠ z := fun he => Bool.false_ne_true (congrArg Prod.snd (B.ports_injective he))
    obtain ⟨K,hK0,hKn,hKh,hKu,hKz⟩ := unit_pair_axis_homeomorph u z hu hz huz
    obtain ⟨A,hAE,hAl,hAr,hAc,hApull⟩ := window_norm_transform a V p.val B K hK0 hKn hKh
    have hAs : A.chart.source = B.chart.source := by
      rw [hAE]
      simp [OpenPartialHomeomorph.trans_source]
    have hAports (x : incidentIndex a p.val × Bool) :
        incidentPorts a p.val A.chart A.left A.right x =
          K (incidentPorts a p.val B.chart B.left B.right x) := by
      rw [hAE,hAl,hAr]
      rfl
    refine ⟨A,?_,?_,?_,?_⟩
    · intro y hy
      have hs := hBU (hAs ▸ hy.1)
      exact hs.1
    · exact (congrArg (fun x : Plane => x 1) (hAports (k,false))).trans hKu
    · exact (congrArg (fun x : Plane => x 1) (hAports (k,true))).trans hKz
    · intro j hji
      have hc (z : incidentIndex a p.val) : A.center z ∈ Ioo (0:Interval) 1 :=
        ⟨(A.cuts z).1.trans (A.cuts z).2.1,
          (A.cuts z).2.2.1.trans (A.cuts z).2.2.2⟩
      obtain ⟨C,hC⟩ := hcross i j.val hji.symm (A.center k) (A.center j)
        (hc k) (hc j) ((A.at_center k).trans (A.at_center j).symm)
      exact window_opposite_port_signs a haugEmb V p.val A k j
        (fun he => hji (congrArg Subtype.val he).symm)
        ((congrArg (fun x : Plane => x 1) (hAports (k,false))).trans hKu)
        ((congrArg (fun x : Plane => x 1) (hAports (k,true))).trans hKz) C hC
  · intro p i j hij hselected u t hu ht hi hj
    obtain ⟨D,hD,hDV⟩ := supported_isolated_chart F (a i) (a j) (haugEmb i) (haugEmb j)
      (haugFinite i j hij) u t hu ht (hi.trans hj.symm) V (N p) (hN p)
      (by rw [hi]; exact hpN p) ((hNF p).trans interior_subset)
      (fun z hz => hOV ((hNclose p) hz).1.1)
    obtain ⟨C,hC⟩ := hcross i j hij u t hu ht (hi.trans hj.symm)
    exact ⟨D,isolated_opposite_invariant (a i) (a j) u t C D hC hD,hDV⟩
