import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryQCover
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundarySweepLifts
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.BoundaryReturnExclusion
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.PathConcatCore
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.MixedHalfBoundary
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryGlobalSideSwitch
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.SubsetNullBoundaryDiskFilling
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryStripFinitePosition
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip

namespace CoherentEndpointMotion.FreeBoundaryNullGeometry
open CurveComplex Set Topology Schoenflies
open CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex.BranchedDoubleCover
open CurveComplex.BranchedDoubleCover
open CoherentEndpointMotion.FreeBoundaryContactRepair
open RegionalEmbeddedFamily
set_option maxHeartbeats 4000000

private theorem single_boundary_track_affine_lift
    {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y]
    {B : Set Z} (β : Circle ≃ₜ B) (p : Y → Z) (hp : IsCoveringMap p)
    (T : C(Interval,Y)) (hB : ∀ t, p (T t) ∈ B) :
    ∃ (u v : ℝ) (L : C(Interval,Y)),
      (∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val) ∧
      L 0 = T 0 ∧ L 1 = T 1 := by
  let τ : C(Interval,Z) := ⟨fun t => p (T t),hp.continuous.comp T.continuous⟩
  let q : C(Interval,Circle) :=
    ⟨fun t => β.symm ⟨τ t,hB t⟩,β.symm.continuous.comp (τ.continuous.subtype_mk _)⟩
  let θ := Circle.isCoveringMap_exp.liftPath q (q 0).val.arg (Circle.exp_arg _).symm
  have hθ (t) : Circle.exp (θ t) = q t :=
    congrFun (Circle.isCoveringMap_exp.liftPath_lifts ..) t
  have hτ (t) : (β (Circle.exp (θ t))).val = τ t := by
    rw [hθ]; exact congrArg Subtype.val (β.apply_symm_apply _)
  let ℓ : C(Interval,Z) :=
    ⟨fun t => (β (Circle.exp (affineAngle (θ 0) (θ 1) t))).val,by fun_prop⟩
  let J : ContinuousMap.HomotopyRel τ ℓ ({0,1} : Set Interval) := {
    toHomotopy := {
      toFun := fun z => (β (Circle.exp
        ((1-z.1.val)*θ z.2+z.1.val*affineAngle (θ 0) (θ 1) z.2))).val
      continuous_toFun := by fun_prop
      map_zero_left := by intro t; simpa using hτ t
      map_one_left := by intro t; simp [ℓ] }
    prop' := by
      intro r t ht
      rcases Set.mem_insert_iff.mp ht with ht | ht
      · subst t
        have he : (1-r.val)*θ (0:Interval)+r.val*affineAngle (θ 0) (θ 1) 0 = θ 0 := by
          change (1-r.val)*θ 0+r.val*((1-0)*θ 0+0*θ 1)=θ 0
          ring
        change (β (Circle.exp _)).val = _
        rw [he]; exact hτ 0
      · obtain rfl := Set.mem_singleton_iff.mp ht
        have he : (1-r.val)*θ (1:Interval)+r.val*affineAngle (θ 0) (θ 1) 1 = θ 1 := by
          change (1-r.val)*θ 1+r.val*((1-1)*θ 0+1*θ 1)=θ 1
          ring
        change (β (Circle.exp _)).val = _
        rw [he]; exact hτ 1 }
  obtain ⟨L,hL,h0,h1⟩ := covering_relative_lift_endpoints J p hp T (fun _ => rfl)
  exact ⟨θ 0,θ 1,L,hL,h0,h1⟩

/-- Private reduction: a boundary path joining the endpoints of one lift can
be straightened without losing either lifted endpoint. The geometric inputs
exclude a clean affine return. -/
private theorem boundary_path_endpoint_connection_excluded
    {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y]
    {B : Set Z} (β : Circle ≃ₜ B) (p : Y → Z) (hp : IsCoveringMap p)
    (a : C(Interval,Z)) (ha : IsEmbedding a)
    (haB : ∀ s, a s ∈ B ↔ s=0 ∨ s=1)
    (hswitch : ∀ (u v : ℝ), u ≠ v → ∀ L : C(Interval,Y),
      (∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val) →
      ∀ E : C(Interval,Y), (∀ t, p (E t) = a t) →
      ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        TrackSwitch L (range E) U V)
    (hno : ∀ (u v : ℝ), u ≠ v → ∀ L : C(Interval,Y),
      (∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val) →
      ∀ E : C(Interval,Y), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → L l ∈ range E → L r ∈ range E →
        (∀ t, l < t → t < r → p (L t) ∉ range a) → False)
    (E : C(Interval,Y)) (hEp : ∀ t, p (E t) = a t)
    (T : C(Interval,Y)) (hTB : ∀ t, p (T t) ∈ B)
    (hT0 : T 0 = E 0) (hT1 : T 1 = E 1) : False := by
  obtain ⟨u,v,L,hL,h0,h1⟩ := single_boundary_track_affine_lift β p hp T hTB
  have huv : u ≠ v := by
    intro he
    have heq : p (L 0) = p (L 1) := by simp only [hL,affineAngle,ContinuousMap.coe_mk,he]; simp
    rw [h0,h1,hT0,hT1,hEp,hEp] at heq
    exact zero_ne_one (ha.injective heq)
  let ℓ : C(Interval,Z) := ⟨fun t => p (L t),hp.continuous.comp L.continuous⟩
  have hf : {t : Interval | p (L t) ∈ range a}.Finite := by
    apply (affineBoundary_finite_contacts β huv ℓ hL {a 0,a 1} (Set.toFinite _)).subset
    rintro t ⟨s,hs⟩
    have hsB : a s ∈ B := by rw [hs,hL]; exact (β _).property
    change p (L t) ∈ ({a 0,a 1} : Set Z)
    rw [← hs]
    rcases (haB s).mp hsB with rfl | rfl <;> simp
  obtain ⟨F,l,r,hFp,hlr,hl,hr,hgap⟩ :=
    free_finite_event_separating_cover_clean_return p hp a ha L hf (hswitch u v huv L hL)
      E hEp 0 1 zero_lt_one ⟨0,(h0.trans hT0).symm⟩ ⟨1,(h1.trans hT1).symm⟩
  exact hno u v huv L hL F hFp l r hlr hl hr hgap

private theorem clean_return_around_disjoint_middle
    {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (p : X → Z) (a : C(Interval,Z))
    {a₀ a₁ b₀ b₁ : X}
    (P : Path a₀ b₀) (Q : Path b₀ b₁) (R : Path a₁ b₁)
    (hQ : ∀ t, p (Q t) ∉ range a)
    (hPno : ∀ (E : C(Interval,X)), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → P l ∈ range E → P r ∈ range E →
        (∀ t, l < t → t < r → p (P t) ∉ range a) → False)
    (hRno : ∀ (E : C(Interval,X)), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → R l ∈ range E → R r ∈ range E →
        (∀ t, l < t → t < r → p (R t) ∉ range a) → False)
    (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
    (l r : Interval) (hlr : l < r)
    (hl : ((P.trans Q).trans R.symm) l ∈ range E)
    (hr : ((P.trans Q).trans R.symm) r ∈ range E)
    (hgap : ∀ t : Interval, l < t → t < r →
      p (((P.trans Q).trans R.symm) t) ∉ range a) :
    ∃ u v : Interval, u < 1 ∧ v < 1 ∧ P u ∈ range E ∧ R v ∈ range E ∧
      (∀ t : Interval, u < t → t ≤ 1 → p (P t) ∉ range a) ∧
      (∀ t : Interval, v < t → t ≤ 1 → p (R t) ∉ range a) := by
  have hproj {z : X} (hz : z ∈ range E) : p z ∈ range a := by
    obtain ⟨s,hs⟩ := hz
    exact ⟨s,(hEp s).symm.trans (congrArg p hs)⟩
  have hPi {u : Interval} (hu : P u ∈ range E) : u < 1 := by
    apply lt_of_le_of_ne (show u ≤ (1 : Interval) from u.property.2)
    intro he
    exact hQ 0 (by simpa only [he,P.target,Q.source] using hproj hu)
  have hRi {u : Interval} (hu : R u ∈ range E) : u < 1 := by
    apply lt_of_le_of_ne (show u ≤ (1 : Interval) from u.property.2)
    intro he
    exact hQ 1 (by simpa only [he,R.target,Q.target] using hproj hu)
  let cP := fun u => halfClock (halfClock u)
  let cQ := fun u => halfClock (laterClock u)
  let cR := fun u => laterClock (unitInterval.symm u)
  have hPclock (u) : ((P.trans Q).trans R.symm) (cP u) = P u := by
    simp only [cP,trans_halfClock]
  have hQclock (u) : ((P.trans Q).trans R.symm) (cQ u) = Q u := by
    simp only [cQ,trans_halfClock,trans_laterClock]
  have hRclock (u) : ((P.trans Q).trans R.symm) (cR u) = R u := by
    simp only [cR,trans_laterClock,Path.symm_apply,Function.comp_apply,unitInterval.symm_symm]
  have hcases (t : Interval) :
      (∃ u, t = cP u) ∨ (∃ u, t = cQ u) ∨ (∃ u, t = cR u) := by
    rcases trans_parameter_cases (P.trans Q) R.symm t with ⟨s,hs,_⟩ | ⟨s,hs,_⟩
    · rcases trans_parameter_cases P Q s with ⟨u,hu,_⟩ | ⟨u,hu,_⟩
      · exact Or.inl ⟨u,hs.trans (congrArg halfClock hu)⟩
      · exact Or.inr (Or.inl ⟨u,hs.trans (congrArg halfClock hu)⟩)
    · exact Or.inr (Or.inr ⟨unitInterval.symm s,by simpa [cR] using hs⟩)
  rcases hcases l with ⟨u,rfl⟩ | ⟨u,rfl⟩ | ⟨u,rfl⟩ <;>
    rcases hcases r with ⟨v,rfl⟩ | ⟨v,rfl⟩ | ⟨v,rfl⟩
  all_goals simp only [hPclock,hQclock,hRclock] at hl hr
  · exact False.elim (hPno E hEp u v (by
      change u.val/2/2 < v.val/2/2 at hlr
      change u.val < v.val; linarith) hl hr (by
        intro t hut htv
        have ht := hgap (cP t) (by
          change u.val/2/2 < t.val/2/2
          change u.val < t.val at hut; linarith) (by
          change t.val/2/2 < v.val/2/2
          change t.val < v.val at htv; linarith)
        simpa only [hPclock] using ht))
  · exact False.elim (hQ v (hproj hr))
  · refine ⟨u,v,hPi hl,hRi hr,hl,hr,?_,?_⟩
    · intro t hut _
      have ht := hgap (cP t) (by
        change u.val/2/2 < t.val/2/2
        change u.val < t.val at hut; linarith) (by
        change t.val/2/2 < (1+(1-v.val))/2
        linarith [t.property.2,v.property.2])
      simpa only [hPclock] using ht
    · intro t hvt _
      have ht := hgap (cR t) (by
        change u.val/2/2 < (1+(1-t.val))/2
        linarith [u.property.2,t.property.2]) (by
        change (1+(1-t.val))/2 < (1+(1-v.val))/2
        change v.val < t.val at hvt; linarith)
      simpa only [hRclock] using ht
  · exact False.elim (hQ u (hproj hl))
  · exact False.elim (hQ u (hproj hl))
  · exact False.elim (hQ u (hproj hl))
  · exfalso
    change (1+(1-u.val))/2 < v.val/2/2 at hlr
    linarith [u.property.2,v.property.2]
  · exact False.elim (hQ v (hproj hr))
  · exact False.elim (hRno E hEp v u (by
      change (1+(1-u.val))/2 < (1+(1-v.val))/2 at hlr
      change v.val < u.val; linarith) hr hl (by
        intro t hvt htu
        have ht := hgap (cR t) (by
          change (1+(1-u.val))/2 < (1+(1-t.val))/2
          change t.val < u.val at htu; linarith) (by
          change (1+(1-t.val))/2 < (1+(1-v.val))/2
          change v.val < t.val at hvt; linarith)
        simpa only [hRclock] using ht))

private theorem actual_Q_all_proper_arcs_separating_cover
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ a : C(Interval, ↥Q), IsEmbedding a → a 0 ∈ B → a 1 ∈ B →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B) →
      ∃ top : TopologicalSpace (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y),
        letI := top
        SimplyConnectedSpace (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) ∧
        T2Space (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) ∧
        IsCoveringMap (Sigma.fst : (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) → ↥Q) ∧
        Function.Surjective
          (Sigma.fst : (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y) → ↥Q) ∧
        ∀ c : C(Interval,↥Q), IsEmbedding c → c 0 ∈ B → c 1 ∈ B →
          (∀ t ∈ Ioo (0 : Interval) 1, c t ∉ B) →
        ∀ A : C(Interval, (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y)),
          (∀ t, (A t).1 = c t) →
          ∃ U V : Set (Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y),
            IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range A)ᶜ ∧
            frontier U = range A ∧ frontier V = range A := by
  classical
  intro Q B a ha ha0 ha1 hint
  let : ClosedSurface S := Classical.choice hS.2.1
  let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hQ : IsClosed Q := (E.symm.isOpen_image_of_subset_source Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans htarget)).isClosed_compl
  have hfront : frontier Q = E.symm '' Metric.sphere (E x) R :=
    chart_deleted_disk_complement_frontier E (E x) R hR htarget
  obtain ⟨c,hc⟩ := contact_chart_sphere_is_curve S E (E x) R hR htarget
  have hconn : IsConnected Q := closed_set_connected_of_connected_frontier Q hQ (by
    rw [hfront,← hc]
    exact isConnected_range c.embedded.continuous)
  let : ConnectedSpace ↥Q := isConnected_iff_connectedSpace.mp hconn
  have hbasis := contact_finite_circle_frontier_contractible_basis Q hQ (fun _ : Unit => c)
    (fun i j hij => False.elim (hij (Subsingleton.elim i j)))
    (by simpa only [Set.iUnion_const,hc] using hfront)
  obtain ⟨top,hsc,ht2,hcov,hsurj⟩ := contact_path_class_universal_cover hbasis (a 0)
  let X := Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y
  let : TopologicalSpace X := top
  let : SimplyConnectedSpace X := hsc
  let : T2Space X := ht2
  have hXbasis := contact_local_homeomorph_contractible_basis (Sigma.fst : X → ↥Q)
    hcov.isLocalHomeomorph hbasis
  let : StronglyLocallyContractibleSpace X := ⟨fun z => by
    rw [Filter.hasBasis_self]
    intro V hV
    obtain ⟨W,hWV,hW,hzW⟩ := mem_nhds_iff.mp hV
    obtain ⟨A,hzA,hA,hAW,hcA⟩ := hXbasis z W hW hzW
    exact ⟨A,hA.mem_nhds hzA,hcA,hAW.trans hWV⟩⟩
  refine ⟨top,hsc,ht2,hcov,hsurj,?_⟩
  intro c hc hc0 hc1 hcint
  let aProper : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨c,hc,hc0,hc1,hcint⟩
  obtain ⟨N,hN,hcenter,_,_,hopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget aProper
  intro A hA
  obtain ⟨M,hM,hMc,hMo⟩ := contact_cover_lifts_proper_strip
    (Sigma.fst : X → ↥Q) hcov N hN hopen c hcenter A hA
  have hsep := contact_simply_connected_proper_strip_separates M hM hMo.1
  simpa only [hMc] using hsep

private theorem actual_boundary_affine_clean_return_excluded
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (B : Set ↥F) (β : Circle ≃ₜ B)
    (a : C(Interval,↥F)) (ha : IsEmbedding a)
    (haB : ∀ s, a s ∈ B ↔ s=0 ∨ s=1)
    (hessential : ¬ ∃ c : C(Interval,↥F), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c)
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (p : X → ↥F) (hp : Continuous p) (u v : ℝ) (huv : u ≠ v)
    (L : C(Interval,X)) (hL : ∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val)
    (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
    (l r : Interval) (hlr : l < r) (hl : L l ∈ range E) (hr : L r ∈ range E)
    (hgap : ∀ t, l < t → t < r → p (L t) ∉ range a) : False := by
  have hLB (t) : p (L t) ∈ B := by rw [hL]; exact (β _).property
  have hproj {z : X} (hz : z ∈ range E) : p z ∈ range a := by
    obtain ⟨s,hs⟩ := hz
    exact ⟨s,(hEp s).symm.trans (congrArg p hs)⟩
  have hmarker {z : ↥F} (hz : z ∈ range a) (hzB : z ∈ B) : z ∈ ({a 0,a 1}:Set ↥F) := by
    obtain ⟨s,rfl⟩ := hz
    rcases (haB s).mp hzB with rfl | rfl <;> simp
  let ℓ : C(Interval,↥F) := ⟨fun t => p (L t),hp.comp L.continuous⟩
  have ha01 : a 0 ≠ a 1 := fun he => zero_ne_one (ha.injective he)
  obtain ⟨hc,_⟩ := affineBoundary_two_marker β huv ℓ hL (a 0) (a 1)
    ((haB 0).mpr (Or.inl rfl)) ((haB 1).mpr (Or.inr rfl)) ha01 hlr
    (hmarker (hproj hl) (hLB l)) (hmarker (hproj hr) (hLB r)) (by
      intro t hlt htr ht
      apply hgap t hlt htr
      rcases Set.mem_insert_iff.mp ht with he | he
      · exact ⟨0,he.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp he).symm⟩)
  apply simple_boundary_lift_return_contradicts_essentiality S g hg hS F B a ha
    (fun t ht hBt => by
      rcases (haB t).mp hBt with he | he
      · exact (ne_of_gt ht.1) he
      · exact (ne_of_lt ht.2) he)
    hessential p hp E L hEp hLB l r hl hr hc

private theorem actual_boundary_path_endpoint_connection_excluded
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let F : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥F := {y | y.val ∈ (chartAt Plane x).symm '' Metric.sphere ((chartAt Plane x) x) R}
    ∀ (β : Circle ≃ₜ B) (a : C(Interval,↥F)), IsEmbedding a →
    (∀ s, a s ∈ B ↔ s=0 ∨ s=1) →
    (¬ ∃ c : C(Interval,↥F), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c) →
    ∀ (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X] [T2Space X]
      (p : X → ↥F), IsCoveringMap p →
    (∀ E : C(Interval,X), (∀ t, p (E t) = a t) →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        frontier U = range E ∧ frontier V = range E) →
    ∀ (E : C(Interval,X)), (∀ t, p (E t) = a t) →
    ∀ (T : C(Interval,X)), (∀ t, p (T t) ∈ B) → T 0 = E 0 → T 1 = E 1 → False := by
  intro F B β a ha haB hessential X inst hSC hT2 p hp hsep E hEp T hTB hT0 hT1
  have hai : ∀ t ∈ Ioo (0:Interval) 1, a t ∉ B := by
    intro t ht hBt
    rcases (haB t).mp hBt with he | he
    · exact (ne_of_gt ht.1) he
    · exact (ne_of_lt ht.2) he
  apply boundary_path_endpoint_connection_excluded β p hp a ha haB ?_ ?_ E hEp T hTB hT0 hT1
  · intro u v huv L hL C hCp
    obtain ⟨U,V,hU,hV,hd,hc,hfu,hfv⟩ := hsep C hCp
    refine ⟨U,V,hU,hV,hd,hc,?_⟩
    exact source_actual_affine_boundary_lift_switches_global_sides S g hg hS x R hR htarget
      a ha ((haB 0).mpr (Or.inl rfl)) ((haB 1).mpr (Or.inr rfl)) hai
      X p hp C hCp U V hU hV hd hc hfu hfv β u v huv L hL
  · exact actual_boundary_affine_clean_return_excluded S g hg hS F B β a ha haB hessential
      p hp.continuous

private theorem clean_strip_step
    {Z X : Type} [TopologicalSpace Z] [TopologicalSpace X]
    (B : Set Z) (p : X → Z) (hp : IsCoveringMap p)
    (a b : C(Interval,Z)) (ha : IsEmbedding a)
    (haB : ∀ s, a s ∈ B ↔ s=0 ∨ s=1)
    (hab : Disjoint (range a) (range b))
    (A D : C(Interval,X)) (hAp : ∀ t, p (A t) = a t) (hDp : ∀ t, p (D t) = b t)
    (L : Fin 2 → C(Interval,X)) (hL0 : ∀ i, L i 0 ∈ range A)
    (hL1 : L 0 1 = D 0 ∧ L 1 1 = D 1) (hLB : ∀ i t, p (L i t) ∈ B)
    (hfinite : ∀ i, {t : Interval | p (L i t) ∈ range a}.Finite)
    (hswitch : ∀ E : C(Interval,X), (∀ t, p (E t) = a t) →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        TrackSwitch (L 0) (range E) U V ∧ TrackSwitch (L 1) (range E) U V)
    (hno : ∀ i, ∀ E : C(Interval,X), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → L i l ∈ range E → L i r ∈ range E →
        (∀ t, l < t → t < r → p (L i t) ∉ range a) → False)
    (hNoBoundaryB : ∀ T : C(Interval,X), (∀ t, p (T t) ∈ B) →
      T 0 = D 0 → T 1 = D 1 → False) :
    ∃ (E : C(Interval,X)) (u v s t : Interval),
      (∀ t, p (E t) = a t) ∧ u < 1 ∧ v < 1 ∧
      ((s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧ L 0 u = E s ∧ L 1 v = E t ∧
      (∀ w : Interval, u < w → w ≤ 1 → p (L 0 w) ∉ range a) ∧
      (∀ w : Interval, v < w → w ≤ 1 → p (L 1 w) ∉ range a) := by
  let P : Path (L 0 0) (D 0) := ⟨L 0,rfl,hL1.1⟩
  let Q : Path (D 0) (D 1) := ⟨D,rfl,rfl⟩
  let R : Path (L 1 0) (D 1) := ⟨L 1,rfl,hL1.2⟩
  let Γ := (P.trans Q).trans R.symm
  have hQno (t) : p (Q t) ∉ range a := by
    intro ht
    exact Set.disjoint_left.mp hab ht ⟨t,(hDp t).symm⟩
  have hQf : (Q ⁻¹' (p ⁻¹' range a)).Finite := by
    have he : Q ⁻¹' (p ⁻¹' range a) = ∅ := by ext t; simp only [Set.mem_preimage,Set.mem_empty_iff_false]; exact iff_false_intro (hQno t)
    rw [he]; exact Set.finite_empty
  have hΓfinite : {t : Interval | p (Γ t) ∈ range a}.Finite :=
    finite_trans_events (p ⁻¹' range a) (P.trans Q) R.symm
      (finite_trans_events (p ⁻¹' range a) P Q (hfinite 0) hQf)
      (finite_symm_events (p ⁻¹' range a) R (hfinite 1))
  have hΓswitch (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t) :
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        TrackSwitch Γ.toContinuousMap (range E) U V := by
    obtain ⟨U,V,hU,hV,hd,hc,hP,hR⟩ := hswitch E hEp
    have hQavoid (t) : Q t ∉ range E := by
      rintro ⟨s,hs⟩
      exact hQno t ⟨s,(hEp s).symm.trans (congrArg p hs)⟩
    have hQswitch : TrackSwitch Q.toContinuousMap (range E) U V :=
      fun t _ ht => False.elim (hQavoid t ht)
    exact ⟨U,V,hU,hV,hd,hc,trackSwitch_trans _ U V (P.trans Q) R.symm
      (trackSwitch_trans _ U V P Q hP hQswitch (by simpa only [Q.source] using hQavoid 0))
      (trackSwitch_symm _ U V R hR) (by simpa only [Q.target] using hQavoid 1)⟩
  obtain ⟨E,l,r,hEp,hlr,hl,hr,hgap⟩ := free_finite_event_separating_cover_clean_return
    p hp a ha Γ.toContinuousMap hΓfinite hΓswitch A hAp 0 1 zero_lt_one
    (by simpa only [Γ,Path.coe_toContinuousMap,Path.source] using hL0 0)
    (by simpa only [Γ,Path.coe_toContinuousMap,Path.target] using hL0 1)
  obtain ⟨u,v,hu,hv,huE,hvE,hPu,hRv⟩ := clean_return_around_disjoint_middle
    p a P Q R hQno (hno 0) (hno 1) E hEp l r hlr hl hr hgap
  obtain ⟨s,hs⟩ := huE
  obtain ⟨t,ht⟩ := hvE
  have hst : s ≠ t := by
    intro he
    have heq : L 1 v = L 0 u := ht.symm.trans ((congrArg E he.symm).trans hs)
    let LP : Path (L 0 u) (D 0) :=
      ⟨arcSegment (L 0) u 1,arcSegment_zero _ _ _,
        (arcSegment_one _ _ _).trans hL1.1⟩
    let RP : Path (L 0 u) (D 1) :=
      ⟨arcSegment (L 1) v 1,(arcSegment_zero _ _ _).trans heq,
        (arcSegment_one _ _ _).trans hL1.2⟩
    let T := LP.symm.trans RP
    apply hNoBoundaryB T.toContinuousMap ?_ T.source T.target
    intro w
    change p (T w) ∈ B
    have hw : T w ∈ range LP.symm ∪ range RP := (Path.trans_range LP.symm RP) ▸ mem_range_self w
    rcases hw with ⟨z,hz⟩ | ⟨z,hz⟩
    · rw [← hz]; exact hLB 0 _
    · rw [← hz]; exact hLB 1 _
  have hsB : s=0 ∨ s=1 := (haB s).mp (by
    rw [← hEp,hs]; exact hLB 0 u)
  have htB : t=0 ∨ t=1 := (haB t).mp (by
    rw [← hEp,ht]; exact hLB 1 v)
  have horder : (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
    rcases hsB with hsB | hsB <;> rcases htB with htB | htB
    · exact False.elim (hst (hsB.trans htB.symm))
    · exact Or.inl ⟨hsB,htB⟩
    · exact Or.inr ⟨hsB,htB⟩
    · exact False.elim (hst (hsB.trans htB.symm))
  exact ⟨E,u,v,s,t,hEp,hu,hv,horder,hs.symm,ht.symm,hPu,hRv⟩

private theorem affine_projected_segment
    {Z X : Type} [TopologicalSpace Z] [TopologicalSpace X]
    {B : Set Z} (β : Circle ≃ₜ B) (p : X → Z)
    (L : C(Interval,X)) (u v : ℝ)
    (hL : ∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val)
    (l r t : Interval) :
    p (arcSegment L l r t) = (β (Circle.exp
      (affineAngle (affineAngle u v l) (affineAngle u v r) t))).val := by
  change p (L (intervalAffine l r t)) = _
  rw [hL]
  congr 3
  simp only [affineAngle,ContinuousMap.coe_mk,intervalAffine]
  ring

private theorem clean_affine_strip_step
    {Z X : Type} [TopologicalSpace Z] [TopologicalSpace X]
    {B : Set Z} (β : Circle ≃ₜ B) (p : X → Z) (hp : IsCoveringMap p)
    (a b : C(Interval,Z)) (ha : IsEmbedding a)
    (haB : ∀ s, a s ∈ B ↔ s=0 ∨ s=1)
    (hab : Disjoint (range a) (range b))
    (hsepSwitch : ∀ E : C(Interval,X), (∀ t, p (E t) = a t) →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
        ∀ u v : ℝ, u ≠ v → ∀ L : C(Interval,X),
          (∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val) →
            TrackSwitch L (range E) U V)
    (hno : ∀ u v : ℝ, u ≠ v → ∀ L : C(Interval,X),
      (∀ t, p (L t) = (β (Circle.exp (affineAngle u v t))).val) →
      ∀ E : C(Interval,X), (∀ t, p (E t) = a t) →
      ∀ l r : Interval, l < r → L l ∈ range E → L r ∈ range E →
        (∀ t, l < t → t < r → p (L t) ∉ range a) → False)
    (A D : C(Interval,X)) (hAp : ∀ t, p (A t) = a t) (hDp : ∀ t, p (D t) = b t)
    (L : Fin 2 → C(Interval,X)) (α ω : Fin 2 → ℝ) (hαω : ∀ i, α i ≠ ω i)
    (hL : ∀ i t, p (L i t) = (β (Circle.exp (affineAngle (α i) (ω i) t))).val)
    (hL0 : ∀ i, L i 0 ∈ range A) (hL1 : L 0 1 = D 0 ∧ L 1 1 = D 1)
    (hNoBoundaryB : ∀ T : C(Interval,X), (∀ t, p (T t) ∈ B) →
      T 0 = D 0 → T 1 = D 1 → False) :
    ∃ (E : C(Interval,X)) (u v s t : Interval),
      (∀ t, p (E t) = a t) ∧ u < 1 ∧ v < 1 ∧
      ((s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧ L 0 u = E s ∧ L 1 v = E t ∧
      (∀ w : Interval, u < w → w ≤ 1 → p (L 0 w) ∉ range a) ∧
      (∀ w : Interval, v < w → w ≤ 1 → p (L 1 w) ∉ range a) := by
  have hLB (i t) : p (L i t) ∈ B := by rw [hL]; exact (β _).property
  apply clean_strip_step B p hp a b ha haB hab A D hAp hDp L hL0 hL1 hLB ?_ ?_ ?_ hNoBoundaryB
  · intro i
    let ℓ : C(Interval,Z) := ⟨fun t => p (L i t),hp.continuous.comp (L i).continuous⟩
    apply (affineBoundary_finite_contacts β (hαω i) ℓ (hL i) {a 0,a 1} (Set.toFinite _)).subset
    rintro t ⟨s,hs⟩
    have hsB : a s ∈ B := hs ▸ hLB i t
    change p (L i t) ∈ ({a 0,a 1} : Set Z)
    rw [← hs]
    rcases (haB s).mp hsB with rfl | rfl <;> simp
  · intro E hEp
    obtain ⟨U,V,hU,hV,hd,hc,hSwitch⟩ := hsepSwitch E hEp
    exact ⟨U,V,hU,hV,hd,hc,hSwitch _ _ (hαω 0) _ (hL 0),hSwitch _ _ (hαω 1) _ (hL 1)⟩
  · intro i
    exact hno _ _ (hαω i) _ (hL i)

private theorem affine_circle_open_interior (u v : ℝ) (huv : u ≠ v) :
    IsOpen ((fun t : Interval => Circle.exp (affineAngle u v t)) '' Ioo 0 1) := by
  have he : (fun t : Interval => Circle.exp (affineAngle u v t)) '' Ioo 0 1 =
      Circle.exp '' Ioo (min u v) (max u v) := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨affineAngle u v t,?_,rfl⟩
      have ht0 : 0 < t.val := ht.1
      have ht1 : t.val < 1 := ht.2
      change (1-t.val)*u+t.val*v ∈ Ioo (min u v) (max u v)
      rcases lt_or_gt_of_ne huv with h | h
      · rw [min_eq_left h.le,max_eq_right h.le]
        constructor <;> nlinarith
      · rw [min_eq_right h.le,max_eq_left h.le]
        constructor <;> nlinarith
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨t,ht0,ht1,ht⟩ := affineAngle_intermediate (u:=u) (v:=v)
        (l:=(0:Interval)) (r:=1) zero_le_one (w:=w) (by
          simpa only [affineAngle,ContinuousMap.coe_mk,
            show (0:Interval).val = 0 from rfl,show (1:Interval).val = 1 from rfl,
            sub_zero,one_mul,zero_mul,add_zero,sub_self,zero_add] using
              (show w ∈ Icc (min u v) (max u v) from ⟨hw.1.le,hw.2.le⟩))
      have hw0 : w ≠ u := by
        rcases le_total u v with h | h
        · exact (ne_of_gt (by simpa [min_eq_left h] using hw.1))
        · exact (ne_of_lt (by simpa [max_eq_left h] using hw.2))
      have hw1 : w ≠ v := by
        rcases le_total u v with h | h
        · exact (ne_of_lt (by simpa [max_eq_right h] using hw.2))
        · exact (ne_of_gt (by simpa [min_eq_right h] using hw.1))
      refine ⟨t,⟨lt_of_le_of_ne ht0 ?_,lt_of_le_of_ne ht1 ?_⟩,congrArg Circle.exp ht⟩
      · intro he
        subst t
        exact hw0 (by simpa [affineAngle] using ht.symm)
      · intro he
        subst t
        exact hw1 (by simpa [affineAngle] using ht.symm)
  rw [he]
  exact Circle.isCoveringMap_exp.isOpenMap _ isOpen_Ioo

private theorem affine_boundary_arcs_disjoint_of_endpoint_avoidance
    {Z : Type} [TopologicalSpace Z] [T2Space Z]
    {B : Set Z} (β : Circle ≃ₜ B)
    (f g : C(Interval,Z)) (u v : ℝ) (huv : u ≠ v)
    (hf : ∀ t, f t = (β (Circle.exp (affineAngle u v t))).val)
    (hgB : ∀ t, g t ∈ B)
    (hfg0 : f 0 ∉ range g) (hfg1 : f 1 ∉ range g)
    (hgf0 : g 0 ∉ range f) : Disjoint (range f) (range g) := by
  let F : C(Interval,B) :=
    ⟨fun t => β (Circle.exp (affineAngle u v t)),by fun_prop⟩
  let G : C(Interval,B) := ⟨fun t => ⟨g t,hgB t⟩,g.continuous.subtype_mk _⟩
  have hFi : IsOpen (F '' Ioo (0:Interval) 1) := by
    have he : F '' Ioo (0:Interval) 1 = β ''
        ((fun t : Interval => Circle.exp (affineAngle u v t)) '' Ioo 0 1) := by
      rw [Set.image_image]; rfl
    rw [he]
    exact β.isOpenMap _ (affine_circle_open_interior u v huv)
  have hsame : G ⁻¹' range F = G ⁻¹' (F '' Ioo (0:Interval) 1) := by
    apply Set.Subset.antisymm
    · rintro t ⟨s,hs⟩
      have hs' : f s = g t := (hf s).trans (congrArg Subtype.val hs)
      have hs0 : s ≠ 0 := by
        intro he; exact hfg0 ⟨t,hs'.symm.trans (congrArg f he)⟩
      have hs1 : s ≠ 1 := by
        intro he; exact hfg1 ⟨t,hs'.symm.trans (congrArg f he)⟩
      exact ⟨s,⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩,hs⟩
    · exact Set.preimage_mono (Set.image_subset_range _ _)
  have hcl : IsClopen (G ⁻¹' range F) :=
    ⟨(isCompact_range F.continuous).isClosed.preimage G.continuous,
      hsame ▸ hFi.preimage G.continuous⟩
  have hempty : G ⁻¹' range F = ∅ := by
    rcases isClopen_iff.mp hcl with hh | hh
    · exact hh
    · have h0 : (0:Interval) ∈ G ⁻¹' range F := by rw [hh]; trivial
      obtain ⟨t,ht⟩ := h0
      exact False.elim (hgf0 ⟨t,(hf t).trans (congrArg Subtype.val ht)⟩)
  apply Set.disjoint_left.mpr
  rintro z ⟨s,hs⟩ ⟨t,ht⟩
  have hx : t ∈ G ⁻¹' range F := ⟨s,Subtype.ext ((hf s).symm.trans (hs.trans ht.symm))⟩
  rw [hempty] at hx
  exact hx

private theorem four_lifted_sides_null_curve
    {Z X : Type} [TopologicalSpace Z] [T2Space Z]
    [TopologicalSpace X] [SimplyConnectedSpace X]
    (p : X → Z) (hp : Continuous p)
    (a b f k : C(Interval,Z)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hf : IsEmbedding f) (hk : IsEmbedding k)
    (hab : Disjoint (range a) (range b)) (hfk : Disjoint (range f) (range k))
    (hfa : ∀ t : Interval, 0<t → f t ∉ range a)
    (hka : ∀ t : Interval, 0<t → k t ∉ range a)
    (hfb : ∀ t : Interval, t<1 → f t ∉ range b)
    (hkb : ∀ t : Interval, t<1 → k t ∉ range b)
    (A D L U : C(Interval,X))
    (hAp : ∀ t, p (A t) = a t) (hDp : ∀ t, p (D t) = b t)
    (hLp : ∀ t, p (L t) = f t) (hUp : ∀ t, p (U t) = k t)
    (hL0 : L 0=A 0) (hU0 : U 0=A 1) (hL1 : L 1=D 0) (hU1 : U 1=D 1) :
    ∃ c : Curve Z, c.image = (range a ∪ range b) ∪ (range f ∪ range k) ∧
      (⟨c.map,c.embedded.continuous⟩ : C(Circle,Z)).Nullhomotopic := by
  have hf0 : f 0 = a 0 := (hLp 0).symm.trans ((congrArg p hL0).trans (hAp 0))
  have hk0 : k 0 = a 1 := (hUp 0).symm.trans ((congrArg p hU0).trans (hAp 1))
  have hf1 : f 1 = b 0 := (hLp 1).symm.trans ((congrArg p hL1).trans (hDp 0))
  have hk1 : k 1 = b 1 := (hUp 1).symm.trans ((congrArg p hU1).trans (hDp 1))
  have haf : range a ∩ range f = {a 0} := by
    ext z
    constructor
    · rintro ⟨hz,⟨t,rfl⟩⟩
      by_cases ht : t=0
      · simpa only [ht,hf0,Set.mem_singleton_iff]
      · exact False.elim (hfa t (bot_lt_iff_ne_bot.mpr ht) hz)
    · rintro rfl; exact ⟨mem_range_self 0,⟨0,hf0⟩⟩
  have hak : range a ∩ range k = {a 1} := by
    ext z
    constructor
    · rintro ⟨hz,⟨t,rfl⟩⟩
      by_cases ht : t=0
      · simpa only [ht,hk0,Set.mem_singleton_iff]
      · exact False.elim (hka t (bot_lt_iff_ne_bot.mpr ht) hz)
    · rintro rfl; exact ⟨mem_range_self 1,⟨0,hk0⟩⟩
  have hfb' : range f ∩ range b = {b 0} := by
    ext z
    constructor
    · rintro ⟨⟨t,rfl⟩,hz⟩
      by_cases ht : t=1
      · simpa only [ht,hf1,Set.mem_singleton_iff]
      · exact False.elim (hfb t (lt_top_iff_ne_top.mpr ht) hz)
    · rintro rfl; exact ⟨⟨1,hf1⟩,mem_range_self 0⟩
  have hkb' : range k ∩ range b = {b 1} := by
    ext z
    constructor
    · rintro ⟨⟨t,rfl⟩,hz⟩
      by_cases ht : t=1
      · simpa only [ht,hk1,Set.mem_singleton_iff]
      · exact False.elim (hkb t (lt_top_iff_ne_top.mpr ht) hz)
    · rintro rfl; exact ⟨⟨1,hk1⟩,mem_range_self 1⟩
  let PA : Path (A 0) (A 1) := ⟨A,rfl,rfl⟩
  let PU : Path (A 1) (D 1) := ⟨U,hU0,hU1⟩
  let PL : Path (A 0) (D 0) := ⟨L,hL0,hL1⟩
  let PD : Path (D 0) (D 1) := ⟨D,rfl,rfl⟩
  let ap := PA.map hp
  let kp := PU.map hp
  let fp := PL.map hp
  let bp := PD.map hp
  have hea : (ap : Interval → Z) = a := funext hAp
  have heb : (bp : Interval → Z) = b := funext hDp
  have hef : (fp : Interval → Z) = f := funext hLp
  have hek : (kp : Interval → Z) = k := funext hUp
  let first := ap.trans kp
  let second := fp.trans bp
  have hfirst : IsEmbedding first := by
    apply isEmbedding_path_trans_of_inter_singleton_probe ap kp
    · simpa only [hea] using ha
    · simpa only [hek] using hk
    · simpa only [hea,hek,hAp] using hak
  have hsecond : IsEmbedding second := by
    apply isEmbedding_path_trans_of_inter_singleton_probe fp bp
    · simpa only [hef] using hf
    · simpa only [heb] using hb
    · simpa only [hef,heb,hLp,hf1,hDp] using hfb'
  have hfirstRange : range first = range a ∪ range k := by
    rw [Path.trans_range,hea,hek]
  have hsecondRange : range second = range f ∪ range b := by
    rw [Path.trans_range,hef,heb]
  have hcollision (s t : Interval) (hst : first s = second t) :
      (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
    have hs : first s ∈ range a ∪ range k := hfirstRange ▸ mem_range_self s
    have ht : first s ∈ range f ∪ range b := hst.symm ▸ (hsecondRange ▸ mem_range_self t)
    have hcorner : first s = a 0 ∨ first s = b 1 := by
      rcases hs with hsa | hsk <;> rcases ht with htf | htb
      · exact Or.inl (Set.mem_singleton_iff.mp (haf ▸ And.intro hsa htf))
      · exact False.elim (Set.disjoint_left.mp hab hsa htb)
      · exact False.elim (Set.disjoint_left.mp hfk htf hsk)
      · exact Or.inr (Set.mem_singleton_iff.mp (hkb' ▸ And.intro hsk htb))
    rcases hcorner with hh | hh
    · have hsrc : first 0 = a 0 := first.source.trans (hAp 0)
      have hsrc' : second 0 = a 0 := second.source.trans (hAp 0)
      exact Or.inl ⟨hfirst.injective (hh.trans hsrc.symm),
        hsecond.injective (hst.symm.trans (hh.trans hsrc'.symm))⟩
    · have hend : first 1 = b 1 := first.target.trans (hDp 1)
      have hend' : second 1 = b 1 := second.target.trans (hDp 1)
      exact Or.inr ⟨hfirst.injective (hh.trans hend.symm),
        hsecond.injective (hst.symm.trans (hh.trans hend'.symm))⟩
  have hhom : first.Homotopic second := by
    have hh := (SimplyConnectedSpace.paths_homotopic (PA.trans PU) (PL.trans PD)).map ⟨p,hp⟩
    simpa only [Path.map_trans] using hh
  obtain ⟨c,hc,hn⟩ := clean_homotopic_arcs_bound_null_curve first second hfirst hsecond hcollision hhom
  refine ⟨c,?_,hn⟩
  rw [hc,hfirstRange,hsecondRange]
  ext z
  simp only [Set.mem_union]
  tauto

end CoherentEndpointMotion.FreeBoundaryNullGeometry

namespace CoherentEndpointMotion.FreeBoundaryNullGeometry
open CurveComplex Set Topology Schoenflies
open CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex.BranchedDoubleCover
set_option maxHeartbeats 4000000

private theorem rectangle_boundary_ball_bounds_carrier (B : Interval × Interval → Plane) (hB : Topology.IsEmbedding B)
    (hb : ∀ z : Interval × Interval,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
      B z∈Metric.closedBall (0 : Plane) 1) :
    Set.range B ⊆ Metric.closedBall (0 : Plane) 1 := by
  classical
  obtain ⟨z,hz,hmax⟩ := (isCompact_univ : IsCompact (univ : Set (Interval × Interval))).exists_isMaxOn
    (Set.univ_nonempty) (continuous_norm.comp hB.continuous).continuousOn
  have hbound : ‖B z‖≤1 := by
    by_contra hn
    have hnorm : 1<‖B z‖ := lt_of_not_ge hn
    have hno : ¬(z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) := by
      intro he
      have h := hb z he
      have hle : ‖B z‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using h
      exact (not_le_of_gt hnorm) hle
    have hz10 : (0 : ℝ)<(z.1:ℝ) := lt_of_le_of_ne z.1.property.1
      (by intro he; exact hno (Or.inl (Subtype.ext he.symm)))
    have hz11 : (z.1:ℝ)<1 := lt_of_le_of_ne z.1.property.2
      (by intro he; exact hno (Or.inr (Or.inl (Subtype.ext he))))
    have hz20 : (0 : ℝ)<(z.2:ℝ) := lt_of_le_of_ne z.2.property.1
      (by intro he; exact hno (Or.inr (Or.inr (Or.inl (Subtype.ext he.symm)))))
    have hz21 : (z.2:ℝ)<1 := lt_of_le_of_ne z.2.property.2
      (by intro he; exact hno (Or.inr (Or.inr (Or.inr (Subtype.ext he)))))
    let p : Plane → Interval × Interval := fun v =>
      (Set.projIcc 0 1 zero_le_one (v 0),Set.projIcc 0 1 zero_le_one (v 1))
    have hpc : Continuous p := by dsimp [p]; fun_prop
    let O : Set Plane := {v | 0<v 0 ∧ v 0<1 ∧ 0<v 1 ∧ v 1<1}
    have hO : IsOpen O := by
      have h0 : Continuous (fun v : Plane => v 0) := by fun_prop
      have h1 : Continuous (fun v : Plane => v 1) := by fun_prop
      exact (isOpen_lt continuous_const h0).inter
        ((isOpen_lt h0 continuous_const).inter
          ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))
    have hp (v : Plane) (hv : v∈O) :
        p v=(⟨v 0,⟨hv.1.le,hv.2.1.le⟩⟩,⟨v 1,⟨hv.2.2.1.le,hv.2.2.2.le⟩⟩) := by
      dsimp [p]
      rw [Set.projIcc_of_mem zero_le_one ⟨hv.1.le,hv.2.1.le⟩,
        Set.projIcc_of_mem zero_le_one ⟨hv.2.2.1.le,hv.2.2.2.le⟩]
    have hinj : Set.InjOn (B ∘ p) O := by
      intro v hv w hw he
      have h := hB.injective he
      rw [hp v hv,hp w hw] at h
      have h0 := congrArg (fun t : Interval × Interval => (t.1:ℝ)) h
      have h1 := congrArg (fun t : Interval × Interval => (t.2:ℝ)) h
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hOpen := LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      (B ∘ p) O hO (hB.continuous.comp hpc).continuousOn hinj
    let v : Plane := Plane.mk (z.1:ℝ) (z.2:ℝ)
    have hv : v∈O := ⟨hz10,hz11,hz20,hz21⟩
    have hpv : p v=z := by
      rw [hp v hv]
      exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    have hzOpen : B z∈(B ∘ p) '' O := ⟨v,hv,by simp only [Function.comp_apply,hpv]⟩
    obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp hOpen (B z) hzOpen
    let a : ℝ := 1+ε/(2*‖B z‖)
    have hnpos : 0<‖B z‖ := zero_lt_one.trans hnorm
    have hapos : 0<a := by dsimp [a]; positivity
    have hae : (a-1)*‖B z‖=ε/2 := by dsimp [a]; field_simp; ring
    have hdist : dist (a • B z) (B z)<ε := by
      have he : a • B z-B z=(a-1) • B z := by rw [sub_smul,one_smul]
      rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs]
      have ha1 : 0<a-1 := by
        have hd : 0<ε/(2*‖B z‖) := div_pos hε (mul_pos (by norm_num) hnpos)
        dsimp [a]
        linarith only [hd]
      rw [abs_of_pos ha1,hae]
      linarith only [hε]
    obtain ⟨w,hw,he⟩ := hεsub hdist
    have hle : ‖a • B z‖≤‖B z‖ := he ▸ hmax (Set.mem_univ (p w))
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hapos] at hle
    have hprod : a*‖B z‖=‖B z‖+ε/2 := by nlinarith only [hae]
    rw [hprod] at hle
    linarith only [hle,hε]
  rintro y ⟨w,rfl⟩
  have hle : ‖B w‖≤‖B z‖ := hmax (Set.mem_univ w)
  simpa only [Metric.mem_closedBall,dist_zero_right] using hle.trans hbound

private theorem four_sides_in_disk_give_prescribed_rectangle
    {X : Type} [TopologicalSpace X] [T2Space X]
    (P Qe E Rr : C(Interval,X))
    (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Qe)
    (hE : Topology.IsEmbedding E) (hR : Topology.IsEmbedding Rr)
    (hPE : P 0=E 0) (hPR : P 1=Rr 0) (hQE : Qe 0=E 1) (hQR : Qe 1=Rr 1)
    (hPEm : ∀ s t,P s=E t → s=0 ∧ t=0)
    (hPRm : ∀ s t,P s=Rr t → s=1 ∧ t=0)
    (hQEm : ∀ s t,Qe s=E t → s=0 ∧ t=1)
    (hQRm : ∀ s t,Qe s=Rr t → s=1 ∧ t=1)
    (hPQ : Disjoint (Set.range P) (Set.range Qe))
    (hER : Disjoint (Set.range E) (Set.range Rr))
    (D : C(Metric.closedBall (0 : Plane) 1,X)) (hD : Topology.IsEmbedding D)
    (hPD : Set.range P ⊆ Set.range D) (hQD : Set.range Qe ⊆ Set.range D)
    (hED : Set.range E ⊆ Set.range D) (hRD : Set.range Rr ⊆ Set.range D) :
    ∃ B : C(Interval × Interval,X),Topology.IsEmbedding B ∧
      (∀ u,B (u,0)=P u) ∧ (∀ u,B (u,1)=Qe u) ∧
      (∀ v,B (0,v)=E v) ∧ (∀ v,B (1,v)=Rr v) ∧ Set.range B ⊆ Set.range D := by
  let e := hD.toHomeomorph
  let pull (f : C(Interval,X)) (hf : Set.range f ⊆ Set.range D) : C(Interval,Plane) :=
    ⟨fun t => (e.symm ⟨f t,hf (Set.mem_range_self t)⟩).val,
      continuous_subtype_val.comp (e.symm.continuous.comp (f.continuous.subtype_mk _))⟩
  have heq (f g : C(Interval,X))
      (hf : Set.range f ⊆ Set.range D) (hg : Set.range g ⊆ Set.range D) (s t : Interval) :
      pull f hf s=pull g hg t ↔ f s=g t := by
    constructor
    · intro he
      exact congrArg (fun y : Set.range D => y.val) (e.symm.injective (Subtype.ext he))
    · intro he
      exact congrArg (fun y : Set.range D => (e.symm y).val) (Subtype.ext he)
  have hpull (f : C(Interval,X)) (hf : Set.range f ⊆ Set.range D)
      (hfi : Topology.IsEmbedding f) : Topology.IsEmbedding (pull f hf) :=
    ((pull f hf).continuous.isClosedEmbedding (fun s t he =>
      hfi.injective ((heq f f hf hf s t).mp he))).isEmbedding
  have hdisj (f g : C(Interval,X))
      (hf : Set.range f ⊆ Set.range D) (hg : Set.range g ⊆ Set.range D)
      (hfg : Disjoint (Set.range f) (Set.range g)) :
      Disjoint (Set.range (pull f hf)) (Set.range (pull g hg)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨s,hs⟩ ⟨t,ht⟩
    have he := (heq f g hf hg s t).mp (hs.trans ht.symm)
    exact Set.disjoint_left.mp hfg (Set.mem_range_self s) ⟨t,he.symm⟩
  obtain ⟨B,hB,hBP,hBQ,hBE,hBR⟩ :=
    CurveComplex.G3Review.actual_four_arc_cycle_has_prescribed_embedded_square
      (pull P hPD) (pull Qe hQD) (pull E hED) (pull Rr hRD)
      (hpull P hPD hP) (hpull Qe hQD hQ) (hpull E hED hE) (hpull Rr hRD hR)
      ((heq P E hPD hED 0 0).mpr hPE) ((heq P Rr hPD hRD 1 0).mpr hPR)
      ((heq Qe E hQD hED 0 1).mpr hQE) ((heq Qe Rr hQD hRD 1 1).mpr hQR)
      (fun s t he => hPEm s t ((heq P E hPD hED s t).mp he))
      (fun s t he => hPRm s t ((heq P Rr hPD hRD s t).mp he))
      (fun s t he => hQEm s t ((heq Qe E hQD hED s t).mp he))
      (fun s t he => hQRm s t ((heq Qe Rr hQD hRD s t).mp he))
      (hdisj P Qe hPD hQD hPQ) (hdisj E Rr hED hRD hER)
  have hBball : Set.range B ⊆ Metric.closedBall (0 : Plane) 1 := by
    apply rectangle_boundary_ball_bounds_carrier B hB
    intro z hz
    rcases hz with h0 | h1 | h2 | h3
    · have he : z=(0,z.2) := Prod.ext h0 rfl
      rw [he,hBE]
      exact (e.symm ⟨E z.2,hED (Set.mem_range_self z.2)⟩).property
    · have he : z=(1,z.2) := Prod.ext h1 rfl
      rw [he,hBR]
      exact (e.symm ⟨Rr z.2,hRD (Set.mem_range_self z.2)⟩).property
    · have he : z=(z.1,0) := Prod.ext rfl h2
      rw [he,hBP]
      exact (e.symm ⟨P z.1,hPD (Set.mem_range_self z.1)⟩).property
    · have he : z=(z.1,1) := Prod.ext rfl h3
      rw [he,hBQ]
      exact (e.symm ⟨Qe z.1,hQD (Set.mem_range_self z.1)⟩).property
  let lift : C(Interval × Interval,Metric.closedBall (0 : Plane) 1) :=
    ⟨fun z => ⟨B z,hBball (Set.mem_range_self z)⟩,hB.continuous.subtype_mk _⟩
  have hlift : Topology.IsEmbedding lift := (lift.continuous.isClosedEmbedding (by
    intro z w he
    exact hB.injective (congrArg (fun v : Metric.closedBall (0 : Plane) 1 => v.val) he))).isEmbedding
  let F : C(Interval × Interval,X) := D.comp lift
  have hDpull (f : C(Interval,X)) (hf : Set.range f ⊆ Set.range D) (t : Interval) :
      D (e.symm ⟨f t,hf (Set.mem_range_self t)⟩)=f t :=
    congrArg (fun y : Set.range D => y.val) (e.apply_symm_apply ⟨f t,hf (Set.mem_range_self t)⟩)
  refine ⟨F,hD.comp hlift,?_,?_,?_,?_,?_⟩
  · intro u
    have he : lift (u,0)=e.symm ⟨P u,hPD (Set.mem_range_self u)⟩ := Subtype.ext (hBP u)
    change D (lift (u,0))=P u
    rw [he]; exact hDpull P hPD u
  · intro u
    have he : lift (u,1)=e.symm ⟨Qe u,hQD (Set.mem_range_self u)⟩ := Subtype.ext (hBQ u)
    change D (lift (u,1))=Qe u
    rw [he]; exact hDpull Qe hQD u
  · intro v
    have he : lift (0,v)=e.symm ⟨E v,hED (Set.mem_range_self v)⟩ := Subtype.ext (hBE v)
    change D (lift (0,v))=E v
    rw [he]; exact hDpull E hED v
  · intro v
    have he : lift (1,v)=e.symm ⟨Rr v,hRD (Set.mem_range_self v)⟩ := Subtype.ext (hBR v)
    change D (lift (1,v))=Rr v
    rw [he]; exact hDpull Rr hRD v
  · rintro z ⟨t,rfl⟩; exact ⟨lift t,rfl⟩

private theorem surface_rectangle_interior_open
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (B : C(Interval × Interval,S)) (hB : Topology.IsEmbedding B) :
    IsOpen (B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧
      0<(z.2:ℝ) ∧ (z.2:ℝ)<1}) := by
  let O : Set Schoenflies.Plane :=
    {p | 0<p 0 ∧ p 0<1 ∧ 0<p 1 ∧ p 1<1}
  have hc0 : Continuous (fun p : Schoenflies.Plane => p 0) := by fun_prop
  have hc1 : Continuous (fun p : Schoenflies.Plane => p 1) := by fun_prop
  have hO : IsOpen O := (isOpen_lt continuous_const hc0).inter
    ((isOpen_lt hc0 continuous_const).inter
      ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)))
  let q : Schoenflies.Plane → Interval × Interval := fun p =>
    (Set.projIcc 0 1 zero_le_one (p 0),Set.projIcc 0 1 zero_le_one (p 1))
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqval (p : Schoenflies.Plane) (hp : p∈O) :
      q p=(⟨p 0,⟨hp.1.le,hp.2.1.le⟩⟩,⟨p 1,⟨hp.2.2.1.le,hp.2.2.2.le⟩⟩) :=
    Prod.ext (Set.projIcc_of_mem zero_le_one ⟨hp.1.le,hp.2.1.le⟩)
      (Set.projIcc_of_mem zero_le_one ⟨hp.2.2.1.le,hp.2.2.2.le⟩)
  let F : Schoenflies.Plane → S := B ∘ q
  have hFc : Continuous F := B.continuous.comp hqc
  have hFi : Set.InjOn F O := by
    intro p hp v hv he
    have hh := hB.injective he
    change q p=q v at hh
    rw [hqval p hp,hqval v hv] at hh
    have hh0 := congrArg (fun w => (w.1:ℝ)) hh
    have hh1 := congrArg (fun w => (w.2:ℝ)) hh
    ext j
    fin_cases j <;> assumption
  have hopen : IsOpen (F '' O) :=
    surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
  have heq : F '' O = B '' {z | 0<(z.1:ℝ) ∧ (z.1:ℝ)<1 ∧
      0<(z.2:ℝ) ∧ (z.2:ℝ)<1} := by
    apply Set.Subset.antisymm
    · rintro y ⟨p,hp,rfl⟩
      refine ⟨q p,?_,rfl⟩
      rw [hqval p hp]
      exact hp
    · rintro y ⟨z,hz,rfl⟩
      let p := Schoenflies.Plane.mk z.1 z.2
      have hp : p∈O := hz
      refine ⟨p,hp,?_⟩
      change B (q p)=B z
      rw [hqval p hp]
      rfl
  rwa [heq] at hopen

private theorem arc_boundary_iff_endpoints
    {X : Type} [TopologicalSpace X] (B : Set X) (a : C(Interval,X))
    (hends : a 0 ∈ B ∧ a 1 ∈ B)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B) (s : Interval) :
    a s ∈ B ↔ s = 0 ∨ s = 1 := by
  constructor
  · intro hs
    by_cases h0 : s = 0
    · exact Or.inl h0
    by_cases h1 : s = 1
    · exact Or.inr h1
    exact False.elim (hproper s
      ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ hs)
  · rintro (rfl | rfl)
    · exact hends.1
    · exact hends.2

private theorem four_boundary_sides_with_null_curve_give_proper_rectangle
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (B : Set ↥F) (hBfront : ∀ y ∈ B, y.val ∈ frontier F)
    (a b L U : C(Interval,↥F))
    (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hL : IsEmbedding L) (hU : IsEmbedding U)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B)
    (hLB : ∀ t, L t ∈ B) (hUB : ∀ t, U t ∈ B)
    (ha0 : a 0 = L 0) (ha1 : a 1 = U 0)
    (hb0 : b 0 = L 1) (hb1 : b 1 = U 1)
    (hab : Disjoint (range a) (range b))
    (hLU : Disjoint (range L) (range U))
    (c : Curve ↥F)
    (hcImage : c.image = (range a ∪ range b) ∪ (range L ∪ range U))
    (hcNull : (⟨c.map,c.embedded.continuous⟩ : C(Circle,↥F)).Nullhomotopic) :
    ∃ D : C(Interval × Interval,↥F), IsEmbedding D ∧
      (∀ t, D (t,0) = a t) ∧ (∀ t, D (t,1) = b t) ∧
      (∀ z, D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have haB := arc_boundary_iff_endpoints B a
    ⟨ha0 ▸ hLB 0,ha1 ▸ hUB 0⟩ (fun t ht => (hproper t ht).1)
  have hbB := arc_boundary_iff_endpoints B b
    ⟨hb0 ▸ hLB 1,hb1 ▸ hUB 1⟩ (fun t ht => (hproper t ht).2)
  have hAL (s t : Interval) (he : a s = L t) : s = 0 ∧ t = 0 := by
    rcases (haB s).mp (he ▸ hLB t) with hs | hs
    · subst s
      exact ⟨rfl,hL.injective (he.symm.trans ha0)⟩
    · exact False.elim (Set.disjoint_left.mp hLU (Set.mem_range_self t)
        ⟨0,ha1.symm.trans (hs ▸ he)⟩)
  have hAU (s t : Interval) (he : a s = U t) : s = 1 ∧ t = 0 := by
    rcases (haB s).mp (he ▸ hUB t) with hs | hs
    · exact False.elim (Set.disjoint_left.mp hLU
        ⟨0,ha0.symm.trans (hs ▸ he)⟩ (Set.mem_range_self t))
    · subst s
      exact ⟨rfl,hU.injective (he.symm.trans ha1)⟩
  have hBL (s t : Interval) (he : b s = L t) : s = 0 ∧ t = 1 := by
    rcases (hbB s).mp (he ▸ hLB t) with hs | hs
    · subst s
      exact ⟨rfl,hL.injective (he.symm.trans hb0)⟩
    · exact False.elim (Set.disjoint_left.mp hLU (Set.mem_range_self t)
        ⟨1,hb1.symm.trans (hs ▸ he)⟩)
  have hBU (s t : Interval) (he : b s = U t) : s = 1 ∧ t = 1 := by
    rcases (hbB s).mp (he ▸ hUB t) with hs | hs
    · exact False.elim (Set.disjoint_left.mp hLU
        ⟨1,hb0.symm.trans (hs ▸ he)⟩ (Set.mem_range_self t))
    · subst s
      exact ⟨rfl,hU.injective (he.symm.trans hb1)⟩
  obtain ⟨d,hd,hbd⟩ := subset_nullhomotopic_curve_bounds_literal_disk
    S g hg hS F c hcNull
  have hsubset : (range a ∪ range b) ∪ (range L ∪ range U) ⊆ range d := by
    rw [← hcImage,← hbd]
    exact Set.image_subset_range d _
  obtain ⟨D,hD,hDa,hDb,hDL,hDU,hDd⟩ :=
    four_sides_in_disk_give_prescribed_rectangle a b L U ha hb hL hU
      ha0 ha1 hb0 hb1 hAL hAU hBL hBU hab hLU d hd
      (fun y hy => hsubset (Or.inl (Or.inl hy)))
      (fun y hy => hsubset (Or.inl (Or.inr hy)))
      (fun y hy => hsubset (Or.inr (Or.inl hy)))
      (fun y hy => hsubset (Or.inr (Or.inr hy)))
  refine ⟨D,hD,hDa,hDb,?_⟩
  intro z
  constructor
  · intro hzB
    by_cases hz0 : z.1 = 0
    · exact Or.inl hz0
    by_cases hz1 : z.1 = 1
    · exact Or.inr hz1
    by_cases hw0 : z.2 = 0
    · have he : D z = a z.1 := by
        rw [show z = (z.1,0) from Prod.ext rfl hw0,hDa]
      exact (haB z.1).mp (he ▸ hzB)
    by_cases hw1 : z.2 = 1
    · have he : D z = b z.1 := by
        rw [show z = (z.1,1) from Prod.ext rfl hw1,hDb]
      exact (hbB z.1).mp (he ▸ hzB)
    let Ds : C(Interval × Interval,S) :=
      ⟨fun w => (D w).val,continuous_subtype_val.comp D.continuous⟩
    have hDs : IsEmbedding Ds := IsEmbedding.subtypeVal.comp hD
    have hopen := surface_rectangle_interior_open Ds hDs
    have hzInterior : Ds z ∈ Ds ''
        {w | 0 < (w.1:ℝ) ∧ (w.1:ℝ) < 1 ∧ 0 < (w.2:ℝ) ∧ (w.2:ℝ) < 1} := by
      exact ⟨z,⟨bot_lt_iff_ne_bot.mpr hz0,lt_top_iff_ne_top.mpr hz1,
        bot_lt_iff_ne_bot.mpr hw0,lt_top_iff_ne_top.mpr hw1⟩,rfl⟩
    have hsub : Ds ''
        {w | 0 < (w.1:ℝ) ∧ (w.1:ℝ) < 1 ∧ 0 < (w.2:ℝ) ∧ (w.2:ℝ) < 1} ⊆ F := by
      rintro _ ⟨w,hw,rfl⟩
      exact (D w).property
    have hmem : (D z).val ∈ interior F := (hopen.subset_interior_iff.mpr hsub) hzInterior
    exact False.elim ((hBfront (D z) hzB).2 hmem)
  · rintro (hz | hz)
    · rw [show z = (0,z.2) from Prod.ext hz rfl,hDL]
      exact hLB z.2
    · rw [show z = (1,z.2) from Prod.ext hz rfl,hDU]
      exact hUB z.2


private theorem embedded_square_boundary_is_null_curve
    {X : Type} [TopologicalSpace X] [T2Space X]
    (V : C(Interval × Interval,X))
    (hV : Set.InjOn V {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1}) :
    ∃ c : Curve X,
      c.image = (range (fun s : Interval => V (s,0)) ∪
        range (fun s : Interval => V (s,1))) ∪
        (range (fun t : Interval => V (0,t)) ∪ range (fun t : Interval => V (1,t))) ∧
      (⟨c.map,c.embedded.continuous⟩ : C(Circle,X)).Nullhomotopic := by
  let bottom : Path ((0,0) : Interval × Interval) (1,0) :=
    ⟨⟨fun t => (t,0),by fun_prop⟩,rfl,rfl⟩
  let right : Path ((1,0) : Interval × Interval) (1,1) :=
    ⟨⟨fun t => (1,t),by fun_prop⟩,rfl,rfl⟩
  let left : Path ((0,0) : Interval × Interval) (0,1) :=
    ⟨⟨fun t => (0,t),by fun_prop⟩,rfl,rfl⟩
  let top : Path ((0,1) : Interval × Interval) (1,1) :=
    ⟨⟨fun t => (t,1),by fun_prop⟩,rfl,rfl⟩
  let p := bottom.trans right
  let q := left.trans top
  have hb : Function.Injective bottom := by
    intro s t he
    exact congrArg Prod.fst he
  have hr : Function.Injective right := by
    intro s t he
    exact congrArg Prod.snd he
  have hl : Function.Injective left := by
    intro s t he
    exact congrArg Prod.snd he
  have ht : Function.Injective top := by
    intro s t he
    exact congrArg Prod.fst he
  have hbr : range bottom ∩ range right = {((1,0) : Interval × Interval)} := by
    ext z
    constructor
    · rintro ⟨⟨s,rfl⟩,⟨t,he⟩⟩
      exact Prod.ext (congrArg Prod.fst he).symm rfl
    · intro hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨⟨1,rfl⟩,⟨0,rfl⟩⟩
  have hlt : range left ∩ range top = {((0,1) : Interval × Interval)} := by
    ext z
    constructor
    · rintro ⟨⟨s,rfl⟩,⟨t,he⟩⟩
      exact Prod.ext rfl (congrArg Prod.snd he).symm
    · intro hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨⟨1,rfl⟩,⟨0,rfl⟩⟩
  have hp : Function.Injective p :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      bottom right hb hr hbr
  have hq : Function.Injective q :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      left top hl ht hlt
  have hpbd (s : Interval) : p s ∈ {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1} := by
    have hs : p s ∈ range bottom ∪ range right :=
      (Path.trans_range bottom right) ▸ Set.mem_range_self s
    rcases hs with ⟨t,he⟩ | ⟨t,he⟩
    · rw [← he]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [← he]
      exact Or.inr (Or.inl rfl)
  have hqbd (s : Interval) : q s ∈ {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1} := by
    have hs : q s ∈ range left ∪ range top :=
      (Path.trans_range left top) ▸ Set.mem_range_self s
    rcases hs with ⟨t,he⟩ | ⟨t,he⟩
    · rw [← he]
      exact Or.inl rfl
    · rw [← he]
      exact Or.inr (Or.inr (Or.inr rfl))
  have hpq (s t : Interval) (he : p s = q t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hs : p s ∈ range bottom ∪ range right :=
      (Path.trans_range bottom right) ▸ Set.mem_range_self s
    have ht : q t ∈ range left ∪ range top :=
      (Path.trans_range left top) ▸ Set.mem_range_self t
    have hcorner : p s = (0,0) ∨ p s = (1,1) := by
      rcases hs with ⟨u,hu⟩ | ⟨u,hu⟩ <;> rcases ht with ⟨v,hv⟩ | ⟨v,hv⟩
      · have he' := hu.trans (he.trans hv.symm)
        left
        rw [← hu]
        exact Prod.ext (show u = 0 from congrArg Prod.fst he') rfl
      · have he' := congrArg Prod.snd (hu.trans (he.trans hv.symm))
        exact False.elim (zero_ne_one he')
      · have he' := congrArg Prod.fst (hu.trans (he.trans hv.symm))
        exact False.elim (one_ne_zero he')
      · have he' := hu.trans (he.trans hv.symm)
        right
        rw [← hu]
        exact Prod.ext rfl (show u = 1 from congrArg Prod.snd he')
    rcases hcorner with hc | hc
    · exact Or.inl ⟨hp (hc.trans p.source.symm),hq (he.symm.trans (hc.trans q.source.symm))⟩
    · exact Or.inr ⟨hp (hc.trans p.target.symm),hq (he.symm.trans (hc.trans q.target.symm))⟩
  let pv := p.map V.continuous
  let qv := q.map V.continuous
  have hpv : IsEmbedding pv := (pv.continuous.isClosedEmbedding (by
    intro s t he
    exact hp (hV (hpbd s) (hpbd t) he))).isEmbedding
  have hqv : IsEmbedding qv := (qv.continuous.isClosedEmbedding (by
    intro s t he
    exact hq (hV (hqbd s) (hqbd t) he))).isEmbedding
  letI : ContractibleSpace Interval :=
    (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  have hhom : pv.Homotopic qv := (SimplyConnectedSpace.paths_homotopic p q).map V
  obtain ⟨c,hc,hn⟩ := RegionalEmbeddedFamily.clean_homotopic_arcs_bound_null_curve
    pv qv hpv hqv (fun s t he => hpq s t (hV (hpbd s) (hqbd t) he)) hhom
  refine ⟨c,?_,hn⟩
  rw [hc]
  change range (V ∘ p) ∪ range (V ∘ q) = _
  rw [Set.range_comp,Set.range_comp,Path.trans_range,Path.trans_range,
    Set.image_union,Set.image_union,← Set.range_comp,← Set.range_comp,
    ← Set.range_comp,← Set.range_comp]
  change (range (fun s : Interval => V (s,0)) ∪ range (fun s : Interval => V (1,s))) ∪
    (range (fun s : Interval => V (0,s)) ∪ range (fun s : Interval => V (s,1))) = _
  ext x
  simp only [Set.mem_union]
  tauto

private theorem proper_sweep_with_simple_endpoint_tracks_has_injective_boundary
    {X : Type} [TopologicalSpace X] (B : Set X)
    (V : C(Interval × Interval,X))
    (hSlice : ∀ t, IsEmbedding (fun s => V (s,t)))
    (hB : ∀ s t, V (s,t) ∈ B ↔ s = 0 ∨ s = 1)
    (hRails : Disjoint (range (fun s : Interval => V (s,0)))
      (range (fun s : Interval => V (s,1))))
    (hLeft : IsEmbedding (fun t : Interval => V (0,t)))
    (hRight : IsEmbedding (fun t : Interval => V (1,t)))
    (hTracks : Disjoint (range (fun t : Interval => V (0,t)))
      (range (fun t : Interval => V (1,t)))) :
    Set.InjOn V {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1} := by
  intro z hz w hw he
  change V (z.1,z.2) = V (w.1,w.2) at he
  by_cases hlong : z.1 = 0 ∨ z.1 = 1
  · have hwlong : w.1 = 0 ∨ w.1 = 1 := (hB w.1 w.2).mp
      (he ▸ (hB z.1 z.2).mpr hlong)
    rcases hlong with hz0 | hz1 <;> rcases hwlong with hw0 | hw1
    · have ht := hLeft.injective (show V (0,z.2) = V (0,w.2) by simpa [hz0,hw0] using he)
      exact Prod.ext (hz0.trans hw0.symm) ht
    · exact False.elim (Set.disjoint_left.mp hTracks ⟨z.2,rfl⟩
        ⟨w.2,show V (1,w.2) = V (0,z.2) by simpa [hz0,hw1] using he.symm⟩)
    · exact False.elim (Set.disjoint_left.mp hTracks ⟨w.2,rfl⟩
        ⟨z.2,show V (1,z.2) = V (0,w.2) by simpa [hz1,hw0] using he⟩)
    · have ht := hRight.injective (show V (1,z.2) = V (1,w.2) by simpa [hz1,hw1] using he)
      exact Prod.ext (hz1.trans hw1.symm) ht
  · have hwlong : ¬ (w.1 = 0 ∨ w.1 = 1) := by
      intro hh
      exact hlong ((hB z.1 z.2).mp (he.symm ▸ (hB w.1 w.2).mpr hh))
    have hzWidth : z.2 = 0 ∨ z.2 = 1 := by
      rcases hz with h | h | h | h
      · exact (hlong (Or.inl h)).elim
      · exact (hlong (Or.inr h)).elim
      · exact Or.inl h
      · exact Or.inr h
    have hwWidth : w.2 = 0 ∨ w.2 = 1 := by
      rcases hw with h | h | h | h
      · exact (hwlong (Or.inl h)).elim
      · exact (hwlong (Or.inr h)).elim
      · exact Or.inl h
      · exact Or.inr h
    rcases hzWidth with hz0 | hz1 <;> rcases hwWidth with hw0 | hw1
    · have hs := (hSlice 0).injective (show V (z.1,0) = V (w.1,0) by simpa [hz0,hw0] using he)
      exact Prod.ext hs (hz0.trans hw0.symm)
    · exact False.elim (Set.disjoint_left.mp hRails ⟨z.1,rfl⟩
        ⟨w.1,show V (w.1,1) = V (z.1,0) by simpa [hz0,hw1] using he.symm⟩)
    · exact False.elim (Set.disjoint_left.mp hRails ⟨w.1,rfl⟩
        ⟨z.1,show V (z.1,1) = V (w.1,0) by simpa [hz1,hw0] using he⟩)
    · have hs := (hSlice 1).injective (show V (z.1,1) = V (w.1,1) by simpa [hz1,hw1] using he)
      exact Prod.ext hs (hz1.trans hw1.symm)


theorem source_actual_original_disjoint_free_boundary_class_bounds_proper_rectangle
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
    ∀ (a b : C(Interval, ↥Q)),
      IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range a ∪ range c) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range b ∪ range c) →
      Disjoint ({a 0, a 1} : Set ↥Q) {b 0, b 1} →
      (range a ∩ range b).Finite →
      (∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' range a = range b) →
      Disjoint (range a) (range b) →
      ∃ D : C(Interval × Interval,↥Q), IsEmbedding D ∧
        range (fun t : Interval => D (t,0)) = range a ∧
        range (fun t : Interval => D (t,1)) = range b ∧
        (∀ z, D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) := by
  classical
  intro Q B a b ha hb hends hproper haEssential hbEssential hendsDisjoint hfinite hclass hdisjoint
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hfront : frontier Q = (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R :=
    chart_deleted_disk_complement_frontier (chartAt Plane x)
      ((chartAt Plane x) x) R hR htarget
  have hBfront (y : Q) (hy : y ∈ B) : y.val ∈ frontier Q := by
    rw [hfront]
    exact hy
  -- The remaining source obligation is the simultaneous simple boundary:
  -- both given rails, two disjoint B sides, and nullity in the literal Q.
  have boundaryData : ∃ L U : C(Interval,↥Q),
      IsEmbedding L ∧ IsEmbedding U ∧
      (∀ t, L t ∈ B) ∧ (∀ t, U t ∈ B) ∧
      Disjoint (range L) (range U) ∧
      a 0 = L 0 ∧ a 1 = U 0 ∧
      ((b 0 = L 1 ∧ b 1 = U 1) ∨ (b 1 = L 1 ∧ b 0 = U 1)) ∧
      ∃ c : Curve ↥Q,
        c.image = (range a ∪ range b) ∪ (range L ∪ range U) ∧
        (⟨c.map,c.embedded.continuous⟩ : C(Circle,↥Q)).Nullhomotopic := by
    obtain ⟨H,hHB,hHa⟩ := hclass
    let V : C(Interval × Interval,↥Q) :=
      ⟨fun z => H.map (z.2,a z.1),
        H.map.continuous.comp (continuous_snd.prodMk (a.continuous.comp continuous_fst))⟩
    have hVzero (s : Interval) : V (s,0) = a s := H.at_zero (a s)
    have hVSlice (t : Interval) : IsEmbedding (fun s => V (s,t)) := by
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      have hfun : (fun s => V (s,t)) = e ∘ a := funext (fun s => (he (a s)).symm)
      rw [hfun]
      exact e.isEmbedding.comp ha
    have haB := arc_boundary_iff_endpoints B a ⟨hends.1,hends.2.1⟩
      (fun t ht => (hproper t ht).1)
    have hbB := arc_boundary_iff_endpoints B b ⟨hends.2.2.1,hends.2.2.2⟩
      (fun t ht => (hproper t ht).2)
    have hVB (s t : Interval) : V (s,t) ∈ B ↔ s = 0 ∨ s = 1 := by
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      have heB : e '' B = B := by
        have hefun : (e : ↥Q → ↥Q) = fun y => H.map (t,y) := funext he
        rw [hefun]
        exact hHB t
      change H.map (t,a s) ∈ B ↔ _
      rw [← he]
      exact (boundary_preserving_homeomorph_mem B e heB (a s)).trans (haB s)
    have hVoneRange : range (fun s : Interval => V (s,1)) = range b := by
      change range (H.finalMap ∘ a) = range b
      rw [Set.range_comp]
      exact hHa
    have hVzeroRange : range (fun s : Interval => V (s,0)) = range a :=
      congrArg Set.range (funext hVzero)
    have hVdisjoint : Disjoint (range (fun s : Interval => V (s,0)))
        (range (fun s : Interval => V (s,1))) := by
      simpa only [hVzeroRange,hVoneRange] using hdisjoint
    let L : C(Interval,↥Q) := ⟨fun t => V (0,t),
      V.continuous.comp (continuous_const.prodMk continuous_id)⟩
    let U : C(Interval,↥Q) := ⟨fun t => V (1,t),
      V.continuous.comp (continuous_const.prodMk continuous_id)⟩
    by_cases hSimple : IsEmbedding L ∧ IsEmbedding U ∧ Disjoint (range L) (range U)
    · have hVinj := proper_sweep_with_simple_endpoint_tracks_has_injective_boundary B V
        hVSlice hVB hVdisjoint hSimple.1 hSimple.2.1 hSimple.2.2
      obtain ⟨c,hc,hcn⟩ := embedded_square_boundary_is_null_curve V hVinj
      have hU0 : a 1 = U 0 := (hVzero 1).symm
      have hL0 : a 0 = L 0 := (hVzero 0).symm
      have hL1 : L 1 = b 0 ∨ L 1 = b 1 := by
        obtain ⟨s,hs⟩ := hVoneRange ▸ Set.mem_range_self (0 : Interval)
        have hsb : s = 0 ∨ s = 1 := (hbB s).mp (hs ▸ (hVB 0 1).mpr (Or.inl rfl))
        rcases hsb with rfl | rfl
        · exact Or.inl hs.symm
        · exact Or.inr hs.symm
      have hU1 : U 1 = b 0 ∨ U 1 = b 1 := by
        obtain ⟨s,hs⟩ := hVoneRange ▸ Set.mem_range_self (1 : Interval)
        have hsb : s = 0 ∨ s = 1 := (hbB s).mp (hs ▸ (hVB 1 1).mpr (Or.inr rfl))
        rcases hsb with rfl | rfl
        · exact Or.inl hs.symm
        · exact Or.inr hs.symm
      have hLUends : L 1 ≠ U 1 := by
        intro he
        exact zero_ne_one ((hVSlice 1).injective he)
      have hordered : (b 0 = L 1 ∧ b 1 = U 1) ∨ (b 1 = L 1 ∧ b 0 = U 1) := by
        rcases hL1 with hL1 | hL1 <;> rcases hU1 with hU1 | hU1
        · exact False.elim (hLUends (hL1.trans hU1.symm))
        · exact Or.inl ⟨hL1.symm,hU1.symm⟩
        · exact Or.inr ⟨hL1.symm,hU1.symm⟩
        · exact False.elim (hLUends (hL1.trans hU1.symm))
      exact ⟨L,U,hSimple.1,hSimple.2.1,
        fun t => (hVB 0 t).mpr (Or.inl rfl),
        fun t => (hVB 1 t).mpr (Or.inr rfl),hSimple.2.2,hL0,hU0,hordered,
        c,by simpa only [hVzeroRange,hVoneRange,L,U,ContinuousMap.coe_mk] using hc,hcn⟩
    ·
      obtain ⟨top,hSC,hT2,hcov,hsurj,hsepAll⟩ := actual_Q_all_proper_arcs_separating_cover
        S g hg hS x R hR htarget a ha hends.1 hends.2.1 (fun t ht => (hproper t ht).1)
      let X := Σ y : ↥Q, Path.Homotopic.Quotient (a 0) y
      letI : TopologicalSpace X := top
      letI : SimplyConnectedSpace X := hSC
      letI : T2Space X := hT2
      let p : X → ↥Q := Sigma.fst
      obtain ⟨ρ,A,D,W,hρ,hAp,hDp,hW0,hW1,hWemb,hWp,hWB⟩ :=
        free_boundary_ambient_sweep_lifts p hcov hsurj B a b ha hb hends hproper H hHB hHa
      obtain ⟨β⟩ := actual_boundary_circle S x R hR htarget
      have hSepSwitch (c : C(Interval,↥Q)) (hc : IsEmbedding c)
          (hcB : ∀ s, c s ∈ B ↔ s=0 ∨ s=1)
          (E : C(Interval,X)) (hEp : ∀ t, p (E t) = c t) :
          ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = (range E)ᶜ ∧
            ∀ u v : ℝ, u ≠ v → ∀ K : C(Interval,X),
              (∀ t, p (K t) = (β (Circle.exp (affineAngle u v t))).val) →
                TrackSwitch K (range E) U V := by
        have hci : ∀ t ∈ Ioo (0:Interval) 1, c t ∉ B := by
          intro t ht hcBt
          rcases (hcB t).mp hcBt with he | he
          · exact (ne_of_gt ht.1) he
          · exact (ne_of_lt ht.2) he
        obtain ⟨U,V,hU,hV,hd,hcuv,hfu,hfv⟩ := hsepAll c hc
          ((hcB 0).mpr (Or.inl rfl)) ((hcB 1).mpr (Or.inr rfl)) hci E hEp
        refine ⟨U,V,hU,hV,hd,hcuv,?_⟩
        intro u v huv K hK
        exact source_actual_affine_boundary_lift_switches_global_sides S g hg hS x R hR htarget
          c hc ((hcB 0).mpr (Or.inl rfl)) ((hcB 1).mpr (Or.inr rfl)) hci
          X p hcov E hEp U V hU hV hd hcuv hfu hfv β u v huv K hK
      have hNoA := actual_boundary_affine_clean_return_excluded S g hg hS Q B β a ha haB
        haEssential p hcov.continuous
      have hNoB := actual_boundary_affine_clean_return_excluded S g hg hS Q B β b hb hbB
        hbEssential p hcov.continuous
      have hNoBoundaryA (E : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
          (T : C(Interval,X)) (hTB : ∀ t, p (T t) ∈ B)
          (hT0 : T 0 = E 0) (hT1 : T 1 = E 1) : False := by
        apply boundary_path_endpoint_connection_excluded β p hcov a ha haB ?_ hNoA E hEp T hTB hT0 hT1
        intro u v huv K hK F hFp
        obtain ⟨U,V,hU,hV,hd,hc,hSw⟩ := hSepSwitch a ha haB F hFp
        exact ⟨U,V,hU,hV,hd,hc,hSw u v huv K hK⟩
      have hNoBoundaryB (E : C(Interval,X)) (hEp : ∀ t, p (E t) = b t)
          (T : C(Interval,X)) (hTB : ∀ t, p (T t) ∈ B)
          (hT0 : T 0 = E 0) (hT1 : T 1 = E 1) : False := by
        apply boundary_path_endpoint_connection_excluded β p hcov b hb hbB ?_ hNoB E hEp T hTB hT0 hT1
        intro u v huv K hK F hFp
        obtain ⟨U,V,hU,hV,hd,hc,hSw⟩ := hSepSwitch b hb hbB F hFp
        exact ⟨U,V,hU,hV,hd,hc,hSw u v huv K hK⟩
      let e : Fin 2 → Interval := fun i => if i=0 then 0 else 1
      have he (i : Fin 2) : e i=0 ∨ e i=1 := by simp only [e]; split <;> simp
      let q : Fin 2 → Interval := fun i => ρ.symm (e i)
      have hq (i : Fin 2) : q i=0 ∨ q i=1 := by
        rcases he i with hi | hi <;> rcases hρ with ⟨h0,h1⟩ | ⟨h0,h1⟩
        · left; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h0]
        · right; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h1]
        · right; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h1]
        · left; apply ρ.injective; simp only [q,ρ.apply_symm_apply,hi,h0]
      let T : Fin 2 → C(Interval,X) := fun i =>
        ⟨fun t => W (t,q i),W.continuous.comp (continuous_id.prodMk continuous_const)⟩
      have hTB (i t) : p (T i t) ∈ B := (hWB t (q i)).mpr (hq i)
      choose α ω K hK hK0 hK1 using fun i => single_boundary_track_affine_lift β p hcov (T i) (hTB i)
      have hKstart (i) : K i 0 ∈ range A := ⟨q i,(hW0 (q i)).symm.trans (hK0 i).symm⟩
      have hKend (i) : K i 1 = D (e i) := (hK1 i).trans (by
        change W (1,q i) = D (e i)
        rw [hW1]; simp only [q,ρ.apply_symm_apply])
      have hαω (i) : α i ≠ ω i := by
        intro hEq
        have hh : p (K i 0) = p (K i 1) := by simp [hK,hEq,affineAngle]
        have h0 : p (K i 0) ∈ range a := by
          obtain ⟨s,hs⟩ := hKstart i
          exact ⟨s,(hAp s).symm.trans (congrArg p hs)⟩
        exact Set.disjoint_left.mp hdisjoint (hh ▸ h0) ⟨e i,(hDp _).symm.trans (congrArg p (hKend i).symm)⟩
      obtain ⟨E,u,v,s,t,hEp,hu,hv,horder,hKu,hKv,hKua,hKva⟩ :=
        clean_affine_strip_step β p hcov a b ha haB hdisjoint
          (hSepSwitch a ha haB) hNoA A D hAp hDp K α ω hαω hK hKstart
          (by simpa [e] using And.intro (hKend 0) (hKend 1))
          (hNoBoundaryB D hDp)
      let cut : Fin 2 → Interval := fun i => if i=0 then u else v
      let j : Fin 2 ≃ Fin 2 := if s=0 then Equiv.refl _ else Equiv.swap 0 1
      let M : Fin 2 → C(Interval,X) := fun i => arcSegment (K (j i)) 1 (cut (j i))
      let α' : Fin 2 → ℝ := fun i => affineAngle (α (j i)) (ω (j i)) 1
      let ω' : Fin 2 → ℝ := fun i => affineAngle (α (j i)) (ω (j i)) (cut (j i))
      have hcut (i) : cut i < 1 := by fin_cases i <;> simp only [cut,if_pos rfl,if_neg (by decide : (1:Fin 2) ≠ 0)] <;> assumption
      have hαω' (i) : α' i ≠ ω' i := by
        intro hh
        have heq := affineAngle_injective (hαω (j i)) hh
        exact (hcut (j i)).ne heq.symm
      have hM (i t) : p (M i t) = (β (Circle.exp (affineAngle (α' i) (ω' i) t))).val :=
        affine_projected_segment β p (K (j i)) _ _ (hK (j i)) 1 (cut (j i)) t
      have hM0 (i) : M i 0 ∈ range D := by
        refine ⟨e (j i),?_⟩
        exact (hKend (j i)).symm.trans (arcSegment_zero _ _ _).symm
      have hM1 : M 0 1 = E 0 ∧ M 1 1 = E 1 := by
        rcases horder with ⟨hs,ht⟩ | ⟨hs,ht⟩
        · simpa [M,j,cut,hs,ht,arcSegment_one] using And.intro hKu hKv
        · simpa [M,j,cut,hs,ht,arcSegment_one] using And.intro hKv hKu
      have hMa (i) (w : Interval) (hw : w < 1) : p (M i w) ∉ range a := by
        have hz : cut (j i) < intervalAffine 1 (cut (j i)) w := by
          change (cut (j i)).val < (1-w.val)*1+w.val*(cut (j i)).val
          have hc := hcut (j i); change (cut (j i)).val < 1 at hc
          change w.val < 1 at hw
          nlinarith
        have hclean (k : Fin 2) : ∀ z : Interval, cut k < z → z ≤ 1 → p (K k z) ∉ range a := by
          fin_cases k <;> simp only [cut,if_pos rfl,if_neg (by decide : (1:Fin 2) ≠ 0)]
          · exact hKua
          · exact hKva
        exact hclean (j i) _ hz (show intervalAffine 1 (cut (j i)) w ≤ 1 from (intervalAffine _ _ _).property.2)
      obtain ⟨F,l,r,c,d,hFp,hl,hr,horderB,hMl,hMr,hMlb,hMrb⟩ :=
        clean_affine_strip_step β p hcov b a hb hbB hdisjoint.symm
          (hSepSwitch b hb hbB) hNoB D E hDp hEp M α' ω' hαω' hM hM0 hM1
          (hNoBoundaryA E hEp)
      let N₀ := arcSegment (M 0) 1 l
      let N₁ := arcSegment (M 1) 1 r
      have hN₀0 : N₀ 0 = E 0 := (arcSegment_zero _ _ _).trans hM1.1
      have hN₁0 : N₁ 0 = E 1 := (arcSegment_zero _ _ _).trans hM1.2
      have hN₀1 : N₀ 1 = F c := (arcSegment_one _ _ _).trans hMl
      have hN₁1 : N₁ 1 = F d := (arcSegment_one _ _ _).trans hMr
      have hN₀a (w : Interval) (hw : 0 < w) : p (N₀ w) ∉ range a := by
        apply hMa 0
        change (1-w.val)*1+w.val*l.val < 1
        change 0 < w.val at hw
        change l.val < 1 at hl
        nlinarith
      have hN₁a (w : Interval) (hw : 0 < w) : p (N₁ w) ∉ range a := by
        apply hMa 1
        change (1-w.val)*1+w.val*r.val < 1
        change 0 < w.val at hw
        change r.val < 1 at hr
        nlinarith
      have hN₀b (w : Interval) (hw : w < 1) : p (N₀ w) ∉ range b := by
        apply hMlb _ ?_ (intervalAffine 1 l w).property.2
        change l.val < (1-w.val)*1+w.val*l.val
        change w.val < 1 at hw
        change l.val < 1 at hl
        nlinarith
      have hN₁b (w : Interval) (hw : w < 1) : p (N₁ w) ∉ range b := by
        apply hMrb _ ?_ (intervalAffine 1 r w).property.2
        change r.val < (1-w.val)*1+w.val*r.val
        change w.val < 1 at hw
        change r.val < 1 at hr
        nlinarith
      let f : C(Interval,↥Q) := ⟨fun w => p (N₀ w),hcov.continuous.comp N₀.continuous⟩
      let k : C(Interval,↥Q) := ⟨fun w => p (N₁ w),hcov.continuous.comp N₁.continuous⟩
      let fα := affineAngle (α' 0) (ω' 0) 1
      let fω := affineAngle (α' 0) (ω' 0) l
      let kα := affineAngle (α' 1) (ω' 1) 1
      let kω := affineAngle (α' 1) (ω' 1) r
      have hfAff (w) : f w = (β (Circle.exp (affineAngle fα fω w))).val :=
        affine_projected_segment β p (M 0) _ _ (hM 0) 1 l w
      have hkAff (w) : k w = (β (Circle.exp (affineAngle kα kω w))).val :=
        affine_projected_segment β p (M 1) _ _ (hM 1) 1 r w
      have hfne : fα ≠ fω := fun hh => hl.ne (affineAngle_injective (hαω' 0) hh).symm
      have hkne : kα ≠ kω := fun hh => hr.ne (affineAngle_injective (hαω' 1) hh).symm
      have hf0 : f 0 = a 0 := (congrArg p hN₀0).trans (hEp 0)
      have hk0 : k 0 = a 1 := (congrArg p hN₁0).trans (hEp 1)
      have hf1 : f 1 = b c := (congrArg p hN₀1).trans (hFp c)
      have hk1 : k 1 = b d := (congrArg p hN₁1).trans (hFp d)
      have hfB (w) : f w ∈ B := by rw [hfAff]; exact (β _).property
      have hkB (w) : k w ∈ B := by rw [hkAff]; exact (β _).property
      have h01 (w : Interval) : intervalAffine 0 1 w = w := by
        apply Subtype.ext
        change (1-w.val)*0+w.val*1=w.val
        ring
      have h10 (w : Interval) : intervalAffine 1 0 w = unitInterval.symm w := by
        apply Subtype.ext
        change (1-w.val)*1+w.val*0=1-w.val
        ring
      have hfEmb : IsEmbedding f := by
        have he := affineBoundary_one_marker β hfne f hfAff (l:=(0:Interval)) (r:=1) zero_lt_one (by
          intro w hw _ hh
          exact hN₀a w hw ⟨0,hf0.symm.trans hh.symm⟩)
        simpa only [h01] using he
      have hkEmb : IsEmbedding k := by
        have he := affineBoundary_one_marker β hkne k hkAff (l:=(0:Interval)) (r:=1) zero_lt_one (by
          intro w hw _ hh
          exact hN₁a w hw ⟨1,hk0.symm.trans hh.symm⟩)
        simpa only [h01] using he
      have hfg0 : f 0 ∉ range k := by
        rintro ⟨w,hw⟩
        by_cases hw0 : w=0
        · have hh : a 1 = a 0 := hk0.symm.trans ((congrArg k hw0).symm.trans (hw.trans hf0))
          exact one_ne_zero (ha.injective hh)
        · exact hN₁a w (bot_lt_iff_ne_bot.mpr hw0) ⟨0,hf0.symm.trans hw.symm⟩
      have hfg1 : f 1 ∉ range k := by
        rintro ⟨w,hw⟩
        by_cases hw1 : w=1
        · have hh : d=c := hb.injective (hk1.symm.trans ((congrArg k hw1).symm.trans (hw.trans hf1)))
          rcases horderB with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;> simp [hc,hd] at hh
        · exact hN₁b w (lt_top_iff_ne_top.mpr hw1) ⟨c,hf1.symm.trans hw.symm⟩
      have hgf0 : k 0 ∉ range f := by
        rintro ⟨w,hw⟩
        by_cases hw0 : w=0
        · have hh : a 0 = a 1 := hf0.symm.trans ((congrArg f hw0).symm.trans (hw.trans hk0))
          exact zero_ne_one (ha.injective hh)
        · exact hN₀a w (bot_lt_iff_ne_bot.mpr hw0) ⟨1,hk0.symm.trans hw.symm⟩
      have hfk := affine_boundary_arcs_disjoint_of_endpoint_avoidance β f k fα fω hfne hfAff hkB hfg0 hfg1 hgf0
      let br := arcSegment b c d
      let F' := arcSegment F c d
      have hcd : c ≠ d := by
        rcases horderB with ⟨hc,hd⟩ | ⟨hc,hd⟩ <;> simp [hc,hd]
      have hbr : IsEmbedding br := arcSegment_embedding b hb c d hcd
      have hbrRange : range br = range b := by
        rcases horderB with ⟨hc,hd⟩ | ⟨hc,hd⟩
        · have heq : (br : Interval → ↥Q) = b := by
            funext w; change b (intervalAffine c d w)=b w; rw [hc,hd,h01]
          rw [heq]
        · have heq : (br : Interval → ↥Q) = b ∘ unitInterval.symm := by
            funext w; change b (intervalAffine c d w)=b (unitInterval.symm w); rw [hc,hd,h10]
          rw [heq]
          exact unitInterval.symm_bijective.surjective.range_comp b
      have hF'p (w) : p (F' w) = br w := hFp (intervalAffine c d w)
      have hN₀1' : N₀ 1 = F' 0 := hN₀1.trans (arcSegment_zero F c d).symm
      have hN₁1' : N₁ 1 = F' 1 := hN₁1.trans (arcSegment_one F c d).symm
      obtain ⟨C,hC,hCn⟩ := four_lifted_sides_null_curve p hcov.continuous
        a br f k ha hbr hfEmb hkEmb (hbrRange ▸ hdisjoint) hfk
        hN₀a hN₁a (by simpa only [hbrRange,f,ContinuousMap.coe_mk] using hN₀b)
        (by simpa only [hbrRange,k,ContinuousMap.coe_mk] using hN₁b)
        E F' N₀ N₁ hEp hF'p (fun _ => rfl) (fun _ => rfl) hN₀0 hN₁0 hN₀1' hN₁1'
      have hordered : (b 0=f 1 ∧ b 1=k 1) ∨ (b 1=f 1 ∧ b 0=k 1) := by
        rcases horderB with ⟨hc,hd⟩ | ⟨hc,hd⟩
        · exact Or.inl ⟨by simpa only [hc] using hf1.symm,by simpa only [hd] using hk1.symm⟩
        · exact Or.inr ⟨by simpa only [hc] using hf1.symm,by simpa only [hd] using hk1.symm⟩
      exact ⟨f,k,hfEmb,hkEmb,hfB,hkB,hfk,hf0.symm,hk0.symm,hordered,
        C,by simpa only [hbrRange] using hC,hCn⟩
  obtain ⟨L,U,hL,hU,hLB,hUB,hLU,ha0,ha1,hbEnds,c,hcImage,hcNull⟩ := boundaryData
  rcases hbEnds with ⟨hb0,hb1⟩ | ⟨hb1,hb0⟩
  · obtain ⟨D,hD,hDa,hDb,hDB⟩ :=
      four_boundary_sides_with_null_curve_give_proper_rectangle
        S g hg hS Q B hBfront a b L U ha hb hL hU hproper
        hLB hUB ha0 ha1 hb0 hb1 hdisjoint hLU c hcImage hcNull
    exact ⟨D,hD,congrArg Set.range (funext hDa),
      congrArg Set.range (funext hDb),hDB⟩
  · let br : C(Interval,↥Q) := b.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    have hbr : IsEmbedding br := hb.comp unitInterval.symmHomeomorph.isEmbedding
    have hbrRange : range br = range b :=
      unitInterval.symm_bijective.surjective.range_comp b
    have hbrProper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ br t ∉ B := by
      intro t ht
      refine ⟨(hproper t ht).1,?_⟩
      apply (hproper (unitInterval.symm t) ?_).2
      constructor
      · change (0:ℝ) < 1-(t:ℝ)
        exact sub_pos.mpr ht.2
      · change 1-(t:ℝ) < (1:ℝ)
        linarith [show (0:ℝ) < (t:ℝ) from ht.1]
    have hbr0 : br 0 = L 1 := by simpa [br] using hb1
    have hbr1 : br 1 = U 1 := by simpa [br] using hb0
    obtain ⟨D,hD,hDa,hDb,hDB⟩ :=
      four_boundary_sides_with_null_curve_give_proper_rectangle
        S g hg hS Q B hBfront a br L U ha hbr hL hU hbrProper
        hLB hUB ha0 ha1 hbr0 hbr1 (hbrRange ▸ hdisjoint) hLU c
        (by simpa only [hbrRange] using hcImage) hcNull
    exact ⟨D,hD,congrArg Set.range (funext hDa),
      (congrArg Set.range (funext hDb)).trans hbrRange,hDB⟩

end CoherentEndpointMotion.FreeBoundaryNullGeometry
