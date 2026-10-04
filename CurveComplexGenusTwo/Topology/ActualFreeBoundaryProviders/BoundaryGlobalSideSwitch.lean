import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalStripCoverSeparation
import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingReturnCore
import Mathlib.Topology.Order.IntermediateValue

open CurveComplex Set Topology Filter
namespace CoherentEndpointMotion.FreeBoundaryContactRepair
universe v
set_option maxHeartbeats 1500000

private theorem boundary_cover_lifts_proper_strip
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
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


/-- The two transverse open halves of the same strip belong to opposite
supplied complementary sides. The frontiers force both labels to occur. -/
private theorem boundary_strip_opposite_widths
    {X : Type*} [TopologicalSpace X]
    (M : C(Interval × Set.Icc (-1 : ℝ) 1, X)) (hM : IsEmbedding M)
    (hopen : IsOpen (M '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (A : C(Interval, X)) (hcenter : ∀ t, M (t, ⟨0,by norm_num⟩) = A t)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = (range A)ᶜ)
    (hfrontU : frontier U = range A) (hfrontV : frontier V = range A)
    (q : Interval) (z w : Interval × Set.Icc (-1 : ℝ) 1)
    (hz : -1 < z.2.val ∧ z.2.val < 0)
    (hw : 0 < w.2.val ∧ w.2.val < 1) :
    (M z ∈ U ∧ M w ∈ V) ∨ (M z ∈ V ∧ M w ∈ U) := by
  let : Fact ((-1 : ℝ) ≤ 1) := ⟨by norm_num⟩
  let W := Set.Icc (-1 : ℝ) 1
  let z0 : W := ⟨0,by norm_num [W]⟩
  let zm : W := ⟨-1,by norm_num [W]⟩
  let zp : W := ⟨1,by norm_num [W]⟩
  let O : Set (Interval × W) := {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}
  let Dm : Set (Interval × W) := Set.univ ×ˢ Set.Ioo zm z0
  let Dp : Set (Interval × W) := Set.univ ×ˢ Set.Ioo z0 zp
  have hInt : IsPreconnected (Set.univ : Set Interval) :=
    isPreconnected_univ
  have hm : IsPreconnected (M '' Dm) :=
    (hInt.prod isPreconnected_Ioo).image M M.continuous.continuousOn
  have hp : IsPreconnected (M '' Dp) :=
    (hInt.prod isPreconnected_Ioo).image M M.continuous.continuousOn
  have haxis (u : Interval × W) : M u ∈ range A ↔ u.2.val = 0 := by
    constructor
    · rintro ⟨s,hs⟩
      have he : (s,z0) = u := hM.injective ((hcenter s).trans hs)
      exact (congrArg (fun z : Interval × W => z.2.val) he).symm
    · intro hu
      refine ⟨u.1,?_⟩
      rw [← hcenter]
      exact congrArg M (Prod.ext rfl (Subtype.ext hu.symm))
  have hsplit : (M '' O) \ range A = (M '' Dm) ∪ (M '' Dp) := by
    ext y
    constructor
    · rintro ⟨⟨u,hu,rfl⟩,huy⟩
      have hn : u.2.val ≠ 0 := fun he => huy ((haxis u).mpr he)
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact Or.inl ⟨u,⟨Set.mem_univ _,hu.1,hn⟩,rfl⟩
      · exact Or.inr ⟨u,⟨Set.mem_univ _,hn,hu.2⟩,rfl⟩
    · rintro (⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩)
      · have hum : -1 < u.2.val ∧ u.2.val < 0 := hu.2
        exact ⟨⟨u,⟨hum.1,hum.2.trans (by norm_num)⟩,rfl⟩,
          fun he => hum.2.ne ((haxis u).mp he)⟩
      · have hup : 0 < u.2.val ∧ u.2.val < 1 := hu.2
        exact ⟨⟨u,⟨(by norm_num : (-1 : ℝ) < 0).trans hup.1,hup.2⟩,rfl⟩,
          fun he => hup.1.ne' ((haxis u).mp he)⟩
  apply RegionalEmbeddedFamily.contact_local_connected_arms_opposite_sides
    (range A) U V (M '' O) (M '' Dm) (M '' Dp) (A q) (M z) (M w)
    hU hV hdis hcover hopen
  · exact ⟨(q,z0),by change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1; norm_num,hcenter q⟩
  · exact frontier_subset_closure (hfrontU.symm ▸ Set.mem_range_self q)
  · exact frontier_subset_closure (hfrontV.symm ▸ Set.mem_range_self q)
  · exact hsplit
  · exact hm
  · exact hp
  · exact ⟨z,⟨Set.mem_univ _,hz⟩,rfl⟩
  · exact ⟨w,⟨Set.mem_univ _,hw⟩,rfl⟩

/-- A nonconstant affine angle has an injective germ, even if the full
boundary path winds more than once. -/
private theorem affine_circle_lift_locally_injective
    {X Y : Type*} (p : X → Y) (b : Circle → Y) (hb : Function.Injective b)
    (u v : ℝ) (huv : u ≠ v) (L : Interval → X)
    (hL : ∀ t, p (L t) = b (Circle.exp ((1 - t.val) * u + t.val * v)))
    (t : Interval) :
    ∃ O : Set Interval, IsOpen O ∧ t ∈ O ∧ Set.InjOn L O := by
  let q : Interval → ℝ := fun s => (1-s.val)*u+s.val*v
  have hq : Continuous q := by fun_prop
  let O := q ⁻¹' Set.Ioo (q t - Real.pi / 2) (q t + Real.pi / 2)
  refine ⟨O,isOpen_Ioo.preimage hq,?_,?_⟩
  · change q t - Real.pi / 2 < q t ∧ q t < q t + Real.pi / 2
    constructor <;> linarith [Real.pi_pos]
  · intro s hs r hr he
    have hec : Circle.exp (q s) = Circle.exp (q r) := by
      apply hb
      exact (hL s).symm.trans ((congrArg p he).trans (hL r))
    have heq : q s = q r := Circle.exp_injOn_Icc
      (a := q t-Real.pi/2) (b := q t+Real.pi/2) (by linarith [Real.pi_pos])
      ⟨hs.1.le,hs.2.le⟩ ⟨hr.1.le,hr.2.le⟩ hec
    have hz : (s.val-r.val)*(v-u) = 0 := by dsimp [q] at heq; nlinarith [heq]
    have hsr : s.val-r.val = 0 := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr huv.symm)
    exact Subtype.ext (sub_eq_zero.mp hsr)

/-- A locally injective boundary path crosses the sides of the same proper
strip at each strict-time contact with its center. -/
private theorem boundary_strip_path_switches_sides
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (M : C(Interval × Set.Icc (-1 : ℝ) 1, X)) (hM : IsEmbedding M)
    (hopen : IsOpen (M '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
    (A : C(Interval, X)) (hcenter : ∀ s, M (s, ⟨0,by norm_num⟩) = A s)
    (D : Set X) (hD : ∀ z, M z ∈ D → z.1 = 0 ∨ z.1 = 1)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = (range A)ᶜ)
    (hfrontU : frontier U = range A) (hfrontV : frontier V = range A)
    (L : C(Interval, X)) (hLD : ∀ s, L s ∈ D)
    (t : Interval) (ht : L t ∈ range A)
    (J : Set Interval) (hJ : IsOpen J) (htJ : t ∈ J) (hLi : Set.InjOn L J)
    (l r : Interval) (hlt : l < t) (htr : t < r) :
    ∃ s w : Interval, l < s ∧ s < t ∧ t < w ∧ w < r ∧
      ((L s ∈ U ∧ L w ∈ V) ∨ (L s ∈ V ∧ L w ∈ U)) := by
  classical
  let W := Set.Icc (-1 : ℝ) 1
  let z0 : W := ⟨0,by norm_num [W]⟩
  obtain ⟨i,hi⟩ := ht
  have hiend : i = 0 ∨ i = 1 := hD (i,z0) (by rw [hcenter,hi]; exact hLD t)
  let other : Interval := if i = 0 then 1 else 0
  have hione : i ≠ other := by
    rcases hiend with hi0 | hi1
    · simp [other,hi0]
    · simp [other,hi1]
  let K : Set X := Set.range (fun w : W => M (other,w))
  have hK : IsClosed K := (isCompact_range (show Continuous (fun w : W => M (other,w)) by fun_prop)).isClosed
  let O : Set X := M '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}
  have htO : L t ∈ O := ⟨(i,z0),by change (-1 : ℝ) < 0 ∧ (0 : ℝ) < 1; norm_num,
    (hcenter i).trans hi⟩
  have htK : L t ∉ K := by
    rintro ⟨w,hw⟩
    have he : (i,z0) = (other,w) := hM.injective (((hcenter i).trans hi).trans hw.symm)
    exact hione (congrArg Prod.fst he)
  have hn : L ⁻¹' (O \ K) ∩ J ∈ 𝓝 t :=
    Filter.inter_mem (((hopen.sdiff hK).preimage L.continuous).mem_nhds ⟨htO,htK⟩)
      (hJ.mem_nhds htJ)
  obtain ⟨c,d,htcd,hcd⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨l,hlt⟩ ⟨r,htr⟩).mp hn
  let e : (Interval × W) ≃ₜ Set.range M := hM.toHomeomorph
  let coord : X → Interval × W := fun y =>
    if hy : y ∈ Set.range M then e.symm ⟨y,hy⟩ else (i,z0)
  have hcM (z : Interval × W) : coord (M z) = z := by
    simp only [coord,dite_eq_left (Set.mem_range_self z)]
    exact e.symm_apply_apply z
  have hcc : ContinuousOn coord (Set.range M) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact e.symm.continuous.congr (fun y => by
      change e.symm y = coord y.val
      simp only [coord,dite_eq_left y.property])
  have hcInv {y : X} (hy : y ∈ Set.range M) : M (coord y) = y := by
    obtain ⟨z,rfl⟩ := hy
    rw [hcM]
  have hLs (s : Interval) (hs : s ∈ Set.Ioo c d) : L s ∈ Set.range M :=
    Set.image_subset_range _ _ (hcd hs).1.1
  have hcoords (s : Interval) (hs : s ∈ Set.Ioo c d) :
      (coord (L s)).1 = i ∧ -1 < (coord (L s)).2.val ∧ (coord (L s)).2.val < 1 := by
    have hbound : -1 < (coord (L s)).2.val ∧ (coord (L s)).2.val < 1 := by
      obtain ⟨z,hz,hzL⟩ := (hcd hs).1.1
      rw [← hzL,hcM]
      exact hz
    refine ⟨?_,hbound⟩
    have hend := hD (coord (L s)) (by rw [hcInv (hLs s hs)]; exact hLD s)
    have hnot : (coord (L s)).1 ≠ other := by
      intro he
      apply (hcd hs).1.2
      refine ⟨(coord (L s)).2,?_⟩
      rw [← he]
      exact hcInv (hLs s hs)
    rcases hiend with hi0 | hi1
    · rcases hend with h0 | h1
      · exact h0.trans hi0.symm
      · exact False.elim (hnot (by simpa [other,hi0] using h1))
    · rcases hend with h0 | h1
      · exact False.elim (hnot (by simpa [other,hi1] using h0))
      · exact h1.trans hi1.symm
  let f : Interval → ℝ := fun s => (coord (L s)).2.val
  have hfc : ContinuousOn f (Set.Ioo c d) :=
    continuous_subtype_val.comp_continuousOn
      (continuous_snd.comp_continuousOn (hcc.comp L.continuous.continuousOn (fun s hs => hLs s hs)))
  have hfi : Set.InjOn f (Set.Ioo c d) := by
    intro s hs w hw he
    apply hLi (hcd hs).2 (hcd hw).2
    rw [← hcInv (hLs s hs),← hcInv (hLs w hw)]
    apply congrArg M
    exact Prod.ext ((hcoords s hs).1.trans (hcoords w hw).1.symm) (Subtype.ext he)
  have hft : f t = 0 := by
    change (coord (L t)).2.val = 0
    rw [← hi,← hcenter,hcM]
  obtain ⟨s,hs⟩ := exists_between (max_lt hlt htcd.1)
  obtain ⟨w,hw⟩ := exists_between (lt_min htr htcd.2)
  have hsI : s ∈ Ioo c d := ⟨(le_max_right l c).trans_lt hs.1,hs.2.trans htcd.2⟩
  have hwI : w ∈ Ioo c d := ⟨htcd.1.trans hw.1,hw.2.trans_le (min_le_right r d)⟩
  refine ⟨s,w,(le_max_left l c).trans_lt hs.1,hs.2,hw.1,
    hw.2.trans_le (min_le_left r d),?_⟩
  rcases hfc.strictMonoOn_of_injOn_Ioo (htcd.1.trans htcd.2) hfi with hm | hm
  · have hsneg : f s < 0 := by simpa only [hft] using hm hsI htcd hs.2
    have hwpos : 0 < f w := by simpa only [hft] using hm htcd hwI hw.1
    have h := boundary_strip_opposite_widths M hM hopen A hcenter U V hU hV hdis
      hcover hfrontU hfrontV i (coord (L s)) (coord (L w))
      ⟨(hcoords s hsI).2.1,hsneg⟩ ⟨hwpos,(hcoords w hwI).2.2⟩
    simpa only [hcInv (hLs s hsI),hcInv (hLs w hwI)] using h
  · have hspos : 0 < f s := by simpa only [hft] using hm hsI htcd hs.2
    have hwneg : f w < 0 := by simpa only [hft] using hm htcd hwI hw.1
    have h := boundary_strip_opposite_widths M hM hopen A hcenter U V hU hV hdis
      hcover hfrontU hfrontV i (coord (L w)) (coord (L s))
      ⟨(hcoords w hwI).2.1,hwneg⟩ ⟨hspos,(hcoords s hsI).2.2⟩
    rw [hcInv (hLs s hsI),hcInv (hLs w hwI)] at h
    exact h.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)

theorem source_actual_affine_boundary_lift_switches_global_sides
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (a : C(Interval, ↥Q)), IsEmbedding a →
      a 0 ∈ B → a 1 ∈ B →
      (∀ s ∈ Ioo (0 : Interval) 1, a s ∉ B) →
      ∀ (X : Type v) [TopologicalSpace X] [T2Space X]
        (p : X → ↥Q), IsCoveringMap p →
        ∀ (E : C(Interval, X)), (∀ s, p (E s) = a s) →
          ∀ (U V : Set X),
            IsOpen U → IsOpen V → Disjoint U V → U ∪ V = (range E)ᶜ →
            frontier U = range E → frontier V = range E →
            ∀ (β : Circle ≃ₜ ↥B) (u v : ℝ), u ≠ v →
              ∀ (L : C(Interval, X)),
                (∀ t, p (L t) =
                  (β (Circle.exp ((1 - t.val) * u + t.val * v))).val) →
                ∀ t : Interval, t ∈ Ioo (0 : Interval) 1 → L t ∈ range E →
                  ∀ l r : Interval, l < t → t < r →
                    ∃ s w : Interval, l < s ∧ s < t ∧ t < w ∧ w < r ∧
                      ((L s ∈ U ∧ L w ∈ V) ∨ (L s ∈ V ∧ L w ∈ U)) := by
  classical
  dsimp only
  intro a ha ha0 ha1 hai X _ _ p hp E hE U V hU hV hdis hcover hfrontU hfrontV
    β u v huv L hL t _ht ht l r hlt htr
  obtain ⟨N,hN,hNc,hNe,hNi,hNo⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget ⟨a,ha,ha0,ha1,hai⟩
  obtain ⟨M,hM,hMc,hMo,hMp⟩ := boundary_cover_lifts_proper_strip p hp N hN hNo a hNc E hE
  obtain ⟨J,hJ,htJ,hLi⟩ := affine_circle_lift_locally_injective p
    (fun z : Circle => (β z).val) (fun _ _ he => β.injective (Subtype.ext he)) u v huv L hL t
  apply boundary_strip_path_switches_sides M hM hMo E hMc
    (p ⁻¹' {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R})
    _ U V hU hV hdis hcover hfrontU hfrontV L _ t ht J hJ htJ hLi l r hlt htr
  · intro z hz
    change p (M z) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R at hz
    rw [hMp] at hz
    by_cases hz0 : z.1 = 0
    · exact Or.inl hz0
    by_cases hz1 : z.1 = 1
    · exact Or.inr hz1
    have hzint : z.1 ∈ Set.Ioo (0 : Interval) 1 := by
      exact ⟨lt_of_le_of_ne (show (0 : Interval) ≤ z.1 from z.1.property.1) (Ne.symm hz0),
        lt_of_le_of_ne (show z.1 ≤ (1 : Interval) from z.1.property.2) hz1⟩
    exact False.elim (hNi z.1 hzint z.2 hz)
  · intro s
    change p (L s) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R
    rw [hL]
    exact (β _).property

end CoherentEndpointMotion.FreeBoundaryContactRepair
