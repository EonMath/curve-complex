import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.LocalEndpointSlide
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip


namespace CoherentEndpointMotion.FreeBoundaryNullGeometry
open CurveComplex Set Topology
set_option maxHeartbeats 8000000

theorem source_actual_original_proper_boundary_rectangle_has_collared_extension
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
    ∀ D : C(Interval × Interval,↥Q), IsEmbedding D →
      (∀ z, D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) →
      ∃ (E : C(Interval × Icc (-1 : ℝ) 1,↥Q)) (p q : Icc (-1 : ℝ) 1),
        IsEmbedding E ∧ (-1 < p.val ∧ p.val < 1) ∧
        (-1 < q.val ∧ q.val < 1) ∧ p ≠ q ∧
        range (fun t : Interval => E (t,p)) = range (fun t : Interval => D (t,0)) ∧
        range (fun t : Interval => E (t,q)) = range (fun t : Interval => D (t,1)) ∧
        (∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
        IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have originalBoundaryBandInitialNeighborhood
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧ E (1,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R)
      (w : Set.Icc (-1 : ℝ) 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1) :
      ∃ N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R), IsOpen N ∧ E (0,w) ∈ N ∧
        N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let b : C(Interval,CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := ⟨fun t => E (t,w),
      E.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hb : Topology.IsEmbedding b := hE.comp (isEmbedding_prodMkLeft w)
    obtain ⟨U,V,hpU,h,hU,hV,hzero,hother,hdisk,hboundary,haxis⟩ :=
      CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.source_proper_arc_initial_endpoint_attached_axis_chart
        S g hg hS x R hR htarget b hb (hend w).1 (hend w).2
        (fun t ht => hproper t ht w)
    let f : C(Interval × Set.Icc (-1 : ℝ) 1,S) :=
      ⟨fun z => (E z).val,continuous_subtype_val.comp E.continuous⟩
    have hp : f (0,w) ∈ U := hpU
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
      ((hU.preimage f.continuous).mem_nhds hp)
    let a : ℝ := min (r/4) (1/2)
    have ha : 0 < a ∧ a < 1 :=
      ⟨lt_min (by positivity) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have har : a < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let η : ℝ := min (r/4) (min ((1-(w:ℝ))/2) ((1+(w:ℝ))/2))
    have hη : 0 < η := lt_min (by positivity)
      (lt_min (by linarith [hw.2]) (by linarith [hw.1]))
    have hηr : η < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηlo : η ≤ (1+(w:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hηhi : η ≤ (1-(w:ℝ))/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hwstrict (u : Set.Icc (-1 : ℝ) 1) : -1 < (w:ℝ)+η*(u:ℝ) ∧
        (w:ℝ)+η*(u:ℝ) < 1 := by
      constructor <;> nlinarith [u.property.1,u.property.2,hw.1,hw.2]
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
      (⟨a*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,ha.1,ha.2]⟩,
        ⟨(w:ℝ)+η*(z.2:ℝ),⟨(hwstrict z.2).1.le,(hwstrict z.2).2.le⟩⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z v he
      apply Prod.ext
      · apply Subtype.ext
        exact mul_left_cancel₀ ha.1.ne' (congrArg (fun p => (p.1:ℝ)) he)
      · apply Subtype.ext
        have hh := congrArg (fun p => (p.2:ℝ)) he
        change (w:ℝ)+η*(z.2:ℝ) = (w:ℝ)+η*(v.2:ℝ) at hh
        nlinarith
    have hfkU (z) : f (k z) ∈ U := by
      apply hrU
      rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      apply max_lt
      · change |a*(z.1:ℝ)-0| < r
        rw [sub_zero,abs_of_nonneg (mul_nonneg ha.1.le z.1.property.1)]
        exact (mul_le_of_le_one_right ha.1.le z.1.property.2).trans_lt har
      · change |((w:ℝ)+η*(z.2:ℝ))-(w:ℝ)| < r
        have he : ((w:ℝ)+η*(z.2:ℝ))-(w:ℝ) = η*(z.2:ℝ) := by ring
        rw [he,abs_mul,abs_of_pos hη]
        exact (mul_le_of_le_one_right hη.le (abs_le.mpr z.2.property)).trans_lt hηr
    have outside_nonneg (y : S) (hy : y ∈ U) (hQ : y ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R) :
        0 ≤ (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 := by
      by_contra hn
      have hneg : (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 < 0 := lt_of_not_ge hn
      obtain ⟨z,hz,he⟩ := (hdisk y hy).mpr hneg.le
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlo | heq
      · exact hQ ⟨z,Metric.mem_ball.mpr hlo,he⟩
      · have hB : y ∈ CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.boundary S x R :=
          ⟨z,Metric.mem_sphere.mpr heq,he⟩
        exact hneg.ne ((hboundary y hy).mp hB)
    let coord : U → Schoenflies.Plane := fun y => Schoenflies.Plane.mk
      (((h y : V) : ℝ × ℝ)).1 (((h y : V) : ℝ × ℝ)).2
    have hcoord : Continuous coord := by dsimp [coord]; fun_prop
    have hcoordi : Function.Injective coord := by
      intro y z he
      apply h.injective
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun p : Schoenflies.Plane => p 0) he
      · exact congrArg (fun p : Schoenflies.Plane => p 1) he
    let C : C(Interval × Set.Icc (-1 : ℝ) 1,Schoenflies.Plane) :=
      ⟨fun z => coord ⟨f (k z),hfkU z⟩,
        hcoord.comp ((f.continuous.comp hkc).subtype_mk _)⟩
    have hCi : Function.Injective C := by
      intro z v he
      have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
      have hEk : E (k z) = E (k v) := Subtype.ext hh
      exact hki (hE.injective hEk)
    have hC : Topology.IsEmbedding C := (C.continuous.isClosedEmbedding hCi).isEmbedding
    have hCzero (u : Set.Icc (-1 : ℝ) 1) : C (0,u) 0 = 0 := by
      apply (hboundary (f (k (0,u))) (hfkU (0,u))).mp
      have hk0 : (k (0,u)).1 = 0 := Subtype.ext (by change a*0=0; ring)
      change (E (k (0,u))).val ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryCircle S x R
      have he : k (0,u) = (0,(k (0,u)).2) := Prod.ext hk0 rfl
      rw [he]
      exact (hend _).1
    have hCpos (t : Interval) (ht : 0 < (t:ℝ)) (u : Set.Icc (-1 : ℝ) 1) :
        0 < C (t,u) 0 := by
      have hn := outside_nonneg (f (k (t,u))) (hfkU (t,u)) (E (k (t,u))).property
      apply lt_of_le_of_ne hn
      intro he
      have hB := (hboundary (f (k (t,u))) (hfkU (t,u))).mpr he.symm
      have hti : (k (t,u)).1 ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · change 0 < a*(t:ℝ); exact mul_pos ha.1 ht
        · change a*(t:ℝ) < 1
          exact (mul_le_of_le_one_right ha.1.le t.property.2).trans_lt ha.2
      exact hproper _ hti _ hB
    let P : Set {p : Schoenflies.Plane | 0 ≤ p 0} :=
      {y | y.val ∈ C '' {z | (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1}}
    have hP : IsOpen P  := CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.halfPlaneBandOpenness C hC hCzero hCpos
    let W : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := Subtype.val ⁻¹' U
    have hW : IsOpen W := hU.preimage continuous_subtype_val
    let J : W → U := fun y => ⟨y.val.val,y.property⟩
    have hJ : Continuous J := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let H : W → {p : Schoenflies.Plane | 0 ≤ p 0} := fun y =>
      ⟨coord (J y),outside_nonneg y.val.val y.property y.val.property⟩
    have hH : Continuous H := (hcoord.comp hJ).subtype_mk _
    let K : Set W := H ⁻¹' P
    have hK : IsOpen K := hP.preimage hH
    let N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := Subtype.val '' K
    have hN : IsOpen N := hW.isOpenMap_subtype_val K hK
    have hk00 : k (0,⟨0,by norm_num⟩) = (0,w) := by
      apply Prod.ext
      · apply Subtype.ext; change a*0=0; ring
      · apply Subtype.ext; change (w:ℝ)+η*0=(w:ℝ); ring
    have hpN : E (0,w) ∈ N := by
      refine ⟨⟨E (0,w),hp⟩,?_,rfl⟩
      change coord (J ⟨E (0,w),hp⟩) ∈ C '' _
      refine ⟨(0,⟨0,by norm_num⟩),⟨by norm_num,by norm_num,by norm_num⟩,?_⟩
      change coord ⟨f (k (0,⟨0,by norm_num⟩)),hfkU _⟩ =
        coord ⟨(E (0,w)).val,hp⟩
      apply congrArg coord
      apply Subtype.ext
      change (E (k (0,⟨0,by norm_num⟩))).val = (E (0,w)).val
      rw [hk00]
    refine ⟨N,hN,hpN,?_⟩
    rintro y ⟨u,hu,rfl⟩
    change coord (J u) ∈ C '' _ at hu
    obtain ⟨z,hz,he⟩ := hu
    have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
    have hEq : E (k z) = u.val := Subtype.ext hh
    exact ⟨k z,hwstrict z.2,hEq⟩
  /- Relative openness is derived for every actual original-Q embedded proper
  band, including both full boundary width edges. No openness certificate is input. -/
  have source_original_boundary_band_relative_open
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧ E (1,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R) :
      IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    have interiorNeighborhood (t : Interval) (w : Set.Icc (-1 : ℝ) 1)
        (ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1) :
        ∃ N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R), IsOpen N ∧ E (t,w) ∈ N ∧
          N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      let clip : Schoenflies.Plane → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
        (Set.projIcc 0 1 zero_le_one (z 0),Set.projIcc (-1) 1 (by norm_num) (z 1))
      let F : Schoenflies.Plane → S := fun z => (E (clip z)).val
      have hFc : Continuous F := continuous_subtype_val.comp
        (E.continuous.comp (by dsimp [clip]; fun_prop))
      let O : Set Schoenflies.Plane := {z | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1}
      have hO : IsOpen O :=
        (isOpen_lt continuous_const (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop)).inter
        ((isOpen_lt (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop) continuous_const).inter
        ((isOpen_lt continuous_const (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop)).inter
        (isOpen_lt (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop) continuous_const)))
      have hclip (z : Schoenflies.Plane) (hz : z ∈ O) :
          ((clip z).1:ℝ) = z 0 ∧ ((clip z).2:ℝ) = z 1 := by
        constructor
        · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hz.1.le,hz.2.1.le⟩)
        · exact congrArg Subtype.val (Set.projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
            ⟨hz.2.2.1.le,hz.2.2.2.le⟩)
      have hFi : Set.InjOn F O := by
        intro z hz v hv he
        have hEq : E (clip z) = E (clip v) := Subtype.ext he
        have hh := hE.injective hEq
        have h0 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.1:ℝ)) hh
        have h1 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.2:ℝ)) hh
        rw [(hclip z hz).1,(hclip v hv).1] at h0
        rw [(hclip z hz).2,(hclip v hv).2] at h1
        ext j
        fin_cases j <;> assumption
      have hFO : IsOpen (F '' O) :=
        surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
      let N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := Subtype.val ⁻¹' (F '' O)
      have hN : IsOpen N := hFO.preimage continuous_subtype_val
      have htw : Schoenflies.Plane.mk t w ∈ O := ⟨ht.1,ht.2,hw.1,hw.2⟩
      have hcliptw : clip (Schoenflies.Plane.mk t w) = (t,w) := Prod.ext
        (Subtype.ext (hclip _ htw).1) (Subtype.ext (hclip _ htw).2)
      refine ⟨N,hN,?_,?_⟩
      · refine ⟨Schoenflies.Plane.mk t w,htw,?_⟩
        change (E (clip (Schoenflies.Plane.mk t w))).val = (E (t,w)).val
        rw [hcliptw]
      · rintro y ⟨z,hz,he⟩
        refine ⟨clip z,?_,Subtype.ext he⟩
        change -1 < ((clip z).2:ℝ) ∧ ((clip z).2:ℝ) < 1
        rw [(hclip z hz).2]
        exact ⟨hz.2.2.1,hz.2.2.2⟩
    let rev : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 :=
      fun z => (unitInterval.symm z.1,z.2)
    have hrev : Topology.IsEmbedding rev :=
      unitInterval.symmHomeomorph.isEmbedding.prodMap Topology.IsEmbedding.id
    let Er : C(Interval × Set.Icc (-1 : ℝ) 1,CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) :=
      ⟨E ∘ rev,E.continuous.comp hrev.continuous⟩
    have hEr : Topology.IsEmbedding Er := hE.comp hrev
    have hEr0 (w) : Er (0,w) = E (1,w) := by
      apply congrArg E
      apply Prod.ext
      · apply Subtype.ext; norm_num [rev,unitInterval.symm]
      · rfl
    have hEr1 (w) : Er (1,w) = E (0,w) := by
      apply congrArg E
      apply Prod.ext
      · apply Subtype.ext; norm_num [rev,unitInterval.symm]
      · rfl
    have hErend (w) : Er (0,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧ Er (1,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R :=
      ⟨hEr0 w ▸ (hend w).2,hEr1 w ▸ (hend w).1⟩
    have hErproper (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1) (w) :
        Er (t,w) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R := by
      apply hproper (unitInterval.symm t) _ w
      constructor
      · change (0:ℝ) < 1-(t:ℝ)
        have hh : (t:ℝ) < 1 := ht.2
        linarith
      · change 1-(t:ℝ) < (1:ℝ)
        have hh : (0:ℝ) < t := ht.1
        linarith
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨⟨t,w⟩,hw,rfl⟩
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨N,hN,hp,hsub⟩ := originalBoundaryBandInitialNeighborhood
        g hg hS hR htarget E hE hend hproper w hw
      exact ⟨N,hsub,hN,hp⟩
    by_cases ht1 : t = 1
    · subst t
      obtain ⟨N,hN,hp,hsub⟩ := originalBoundaryBandInitialNeighborhood
        g hg hS hR htarget Er hEr hErend hErproper w hw
      refine ⟨N,?_,hN,(hEr0 w) ▸ hp⟩
      intro y hy
      obtain ⟨z,hz,he⟩ := hsub hy
      exact ⟨rev z,hz,he⟩
    · have ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)),
          lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))⟩
      obtain ⟨N,hN,hp,hsub⟩ := interiorNeighborhood t w ht hw
      exact ⟨N,hsub,hN,hp⟩
  have outsideHalf
      {X : Type} [TopologicalSpace X] [T2Space X]
      (B : Set X) (D : C(Interval × Interval,X)) (hD : IsEmbedding D)
      (E : C(Interval × Icc (-1:ℝ) 1,X)) (hE : IsEmbedding E)
      (hc : ∀ t, E (t,⟨0,by norm_num⟩) = D (t,0))
      (hEB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
      (hopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1})) :
      ∃ L : C(Interval × Interval,X), IsEmbedding L ∧
        (∀ t, L (t,0) = D (t,0)) ∧ range L ⊆ range E ∧
        range L ∩ range D = range (fun t : Interval => D (t,0)) ∧
        (∀ z, L z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) := by
    let U : Set X := E '' {z | -1 < z.2.val ∧ z.2.val < 1}
    have hprod : (univ : Set Interval) ×ˢ ({0} : Set Interval) ⊆ D ⁻¹' U := by
      rintro ⟨t,w⟩ ⟨_,hw⟩
      obtain rfl := mem_singleton_iff.mp hw
      exact ⟨(t,⟨0,by norm_num⟩),by norm_num,hc t⟩
    obtain ⟨A,V,hA,hV,hIA,h0V,hAV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton
        (hopen.preimage D.continuous) hprod
    obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton _))
    let δ : ℝ := min (r/2) (1/2)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
    let scale : Interval × Interval → Interval × Interval := fun z =>
      (z.1,⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ,hδ1]⟩)
    have hsc : Continuous scale := by dsimp [scale]; fun_prop
    have hthin (z : Interval × Interval) : D (scale z) ∈ U := by
      apply hAV
      refine ⟨hIA (mem_univ _),hrV ?_⟩
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |δ*(z.2:ℝ)-0| < r
      rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le z.2.property.1)]
      exact (mul_le_of_le_one_right hδ.le z.2.property.2).trans_lt hδr
    let e := hE.toHomeomorph
    let k : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
      ⟨fun z => e.symm ⟨D (scale z),image_subset_range E _ (hthin z)⟩,
        e.symm.continuous.comp ((D.continuous.comp hsc).subtype_mk _)⟩
    have hEk (z) : E (k z) = D (scale z) :=
      congrArg Subtype.val (e.apply_symm_apply _)
    have hn (z : Interval × Interval) (hz : 0 < z.2) : ((k z).2:ℝ) ≠ 0 := by
      intro he
      have hw : (k z).2 = (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) := Subtype.ext he
      have hm : E (k z) = D ((k z).1,0) := by
        rw [show k z = ((k z).1,⟨0,by norm_num⟩) from Prod.ext rfl hw,hc]
      have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ))
        (hD.injective (hm.symm.trans (hEk z)))
      change 0 = δ*(z.2:ℝ) at hh
      have hz' : (0:ℝ) < z.2 := hz
      exact (mul_pos hδ hz').ne' hh.symm
    have hp : IsPreconnected ((univ : Set Interval) ×ˢ Ioi (0:Interval)) :=
      isPreconnected_univ.prod isPreconnected_Ioi
    have hside := hp.mapsTo_Ioi_or_Iio
      (show Continuous (fun z => ((k z).2:ℝ)) from
        continuous_subtype_val.comp (continuous_snd.comp k.continuous)).continuousOn
      (fun z hz => hn z hz.2)
    let F : Set X := D '' {z | δ ≤ (z.2:ℝ)}
    have hF : IsClosed F := ((isClosed_le continuous_const
      (continuous_subtype_val.comp continuous_snd)).isCompact.image D.continuous).isClosed
    have hcenterF (t : Interval) : E (t,⟨0,by norm_num⟩) ∉ F := by
      rw [hc]
      rintro ⟨z,hz,he⟩
      have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ)) (hD.injective he)
      change (z.2:ℝ) = 0 at hh
      change δ ≤ (z.2:ℝ) at hz
      rw [hh] at hz
      linarith
    obtain ⟨ρ,hρ,N,hN,hNF,hNform,hNcenter⟩ :=
      source_shrink_embedded_strip_in_open E hE Fᶜ hF.isOpen_compl hcenterF
    have build (σ : ℝ) (hσ : σ = -1 ∨ σ = 1)
        (hopp : ∀ z, 0 < z.2 → σ*((k z).2:ℝ) < 0) :
        ∃ L : C(Interval × Interval,X), IsEmbedding L ∧
          (∀ t, L (t,0) = D (t,0)) ∧ range L ⊆ range E ∧
          range L ∩ range D = range (fun t : Interval => D (t,0)) ∧
          (∀ z, L z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) := by
      have hσn : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
      have hσ2 : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
      let m : Interval × Interval → Interval × Icc (-1:ℝ) 1 := fun z =>
        (z.1,⟨σ*(z.2:ℝ),by rcases hσ with rfl | rfl <;>
          constructor <;> linarith [z.2.property.1,z.2.property.2]⟩)
      have hmc : Continuous m := by dsimp [m]; fun_prop
      have hmi : Function.Injective m := by
        intro z v he
        apply Prod.ext
        · simpa only [m] using congrArg Prod.fst he
        · apply Subtype.ext
          exact mul_left_cancel₀ hσn (congrArg (fun z => (z.2:ℝ)) he)
      let L : C(Interval × Interval,X) := ⟨N ∘ m,hN.continuous.comp hmc⟩
      have hL : IsEmbedding L := hN.comp (hmc.isClosedEmbedding hmi).isEmbedding
      have hL0 (t : Interval) : L (t,0) = D (t,0) := by
        change N (m (t,0)) = _
        rw [show m (t,0) = (t,⟨0,by norm_num⟩) from Prod.ext rfl (Subtype.ext (mul_zero σ)),hNcenter,hc]
      have hform (z) : L z = E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
          rcases hσ with rfl | rfl <;> constructor <;>
          nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) := hNform (m z)
      have hmeet (z : Interval × Interval) (hz : L z ∈ range D) : z.2 = 0 := by
        obtain ⟨v,hv⟩ := hz
        have hvδ : (v.2:ℝ) < δ := lt_of_not_ge (fun hh =>
          (hNF (mem_range_self (m z))) ⟨v,hh,hv⟩)
        let w : Interval := ⟨(v.2:ℝ)/δ,⟨div_nonneg v.2.property.1 hδ.le,
          (div_le_one hδ).mpr hvδ.le⟩⟩
        have hs : scale (v.1,w) = v := by
          apply Prod.ext
          · rfl
          apply Subtype.ext
          change δ*((v.2:ℝ)/δ) = (v.2:ℝ)
          field_simp [hδ.ne']
        have he : E (k (v.1,w)) = E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
            rcases hσ with rfl | rfl <;> constructor <;>
            nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) := by
          exact (hEk _).trans ((congrArg D hs).trans (hv.trans (hform z)))
        have hk := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he)
        by_cases hw0 : v.2 = 0
        · have hv0 : v = (v.1,0) := by
            apply Prod.ext
            · rfl
            · exact hw0
          have he' : E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
              rcases hσ with rfl | rfl <;> constructor <;>
              nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) = E (v.1,⟨0,by norm_num⟩) := by
            exact (hform z).symm.trans (hv.symm.trans
              ((congrArg D hv0).trans (hc v.1).symm))
          have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he')
          apply Subtype.ext
          change (z.2:ℝ) = 0
          change ρ*(σ*(z.2:ℝ)) = 0 at hh
          exact ((mul_eq_zero.mp hh).resolve_left hρ.1.ne' |> mul_eq_zero.mp).resolve_left hσn
        · have hvpos : (0:ℝ) < v.2 := lt_of_le_of_ne v.2.property.1
            (fun he => hw0 (Subtype.ext he.symm))
          have hwpos : (0:Interval) < w := div_pos hvpos hδ
          have hh := hopp (v.1,w) hwpos
          rw [hk] at hh
          have hnon : 0 ≤ σ*(ρ*(σ*(z.2:ℝ))) := by
            rcases hσ with rfl | rfl <;> nlinarith [hρ.1,z.2.property.1]
          exact False.elim (not_lt_of_ge hnon hh)
      refine ⟨L,hL,hL0,?_,?_,?_⟩
      · rintro y ⟨z,rfl⟩
        rw [hform]
        exact mem_range_self _
      · ext y
        constructor
        · rintro ⟨⟨z,rfl⟩,hz⟩
          have h0 := hmeet z hz
          exact ⟨z.1,(hL0 z.1).symm.trans (congrArg L (Prod.ext rfl h0.symm))⟩
        · rintro ⟨t,rfl⟩
          exact ⟨⟨(t,0),hL0 t⟩,mem_range_self (t,0)⟩
      · intro z
        rw [hform,hEB]
    rcases hside with hside | hside
    · apply build (-1) (Or.inl rfl)
      intro z hz
      have hh := hside ⟨mem_univ _,hz⟩
      change 0 < ((k z).2:ℝ) at hh
      linarith
    · apply build 1 (Or.inr rfl)
      intro z hz
      have hh := hside ⟨mem_univ _,hz⟩
      change ((k z).2:ℝ) < 0 at hh
      simpa only [one_mul] using hh
  have glue
      {S W : Type} [TopologicalSpace S] [T2Space S]
      [TopologicalSpace W] [CompactSpace W]
      (L R : Interval × W → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
      (hseam : ∀ w, L (0,w) = R (0,w))
      (hmeet : Set.range L ∩ Set.range R = Set.range (fun w => L (0,w))) :
      ∃ F : Interval × W → S, IsEmbedding F ∧
        (∀ w, F (0,w) = L (1,w)) ∧
        (∀ w, F (1,w) = R (1,w)) ∧
        (∀ w, F (⟨1/2,by norm_num⟩,w) = L (0,w)) ∧
        Set.range F = Set.range L ∪ Set.range R ∧
        (∀ z, ∃ t : Interval, F z = L (t,z.2) ∨ F z = R (t,z.2)) ∧
        ∀ z, F z = if (z.1:ℝ) ≤ 1/2 then
          L (projIcc 0 1 zero_le_one (1-2*(z.1:ℝ)),z.2) else
          R (projIcc 0 1 zero_le_one (2*(z.1:ℝ)-1),z.2) := by
    let kl (z : Interval × W) : Interval × W :=
      (projIcc 0 1 zero_le_one (1-2*(z.1:ℝ)),z.2)
    let kr (z : Interval × W) : Interval × W :=
      (projIcc 0 1 zero_le_one (2*(z.1:ℝ)-1),z.2)
    let F : Interval × W → S :=
      fun z => if (z.1:ℝ) ≤ 1/2 then L (kl z) else R (kr z)
    have hklc : Continuous kl := by dsimp [kl]; fun_prop
    have hkrc : Continuous kr := by dsimp [kr]; fun_prop
    have hfc : Continuous F := by
      apply continuous_if_le (by fun_prop) continuous_const
        (hL.continuous.comp hklc).continuousOn (hR.continuous.comp hkrc).continuousOn
      intro z hz
      have hl : kl z = (0,z.2) := by
        apply Prod.ext
        · apply Subtype.ext
          simp [kl,hz]
        · rfl
      have hr : kr z = (0,z.2) := by
        apply Prod.ext
        · apply Subtype.ext
          simp [kr,hz]
        · rfl
      change L (kl z) = R (kr z)
      rw [hl,hr,hseam]
    have hleft (z : Interval × W) (hz : (z.1:ℝ) ≤ 1/2) :
        ((kl z).1:ℝ) = 1-2*(z.1:ℝ) := by
      exact congrArg Subtype.val (projIcc_of_mem zero_le_one
        (show 1-2*(z.1:ℝ) ∈ CurveComplex.Interval from ⟨by linarith,by linarith [z.1.property.1]⟩))
    have hright (z : Interval × W) (hz : 1/2 ≤ (z.1:ℝ)) :
        ((kr z).1:ℝ) = 2*(z.1:ℝ)-1 := by
      exact congrArg Subtype.val (projIcc_of_mem zero_le_one
        (show 2*(z.1:ℝ)-1 ∈ CurveComplex.Interval from ⟨by linarith,by linarith [z.1.property.2]⟩))
    have hfi : Function.Injective F := by
      intro z w he
      dsimp only [F] at he
      split_ifs at he with hz hw hw
      · have hh := hL.injective he
        apply Prod.ext
        · apply Subtype.ext
          have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) hh
          rw [hleft z hz,hleft w hw] at h1
          linarith
        · simpa [kl] using congrArg Prod.snd hh
      · have hm : L (kl z) ∈ Set.range L ∩ Set.range R :=
          ⟨Set.mem_range_self _,⟨kr w,he.symm⟩⟩
        rw [hmeet] at hm
        obtain ⟨u,hu⟩ := hm
        have hr : R (kr w) = R (0,u) := he.symm.trans (hu.symm.trans (hseam u))
        have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) (hR.injective hr)
        rw [hright w (by linarith)] at h1
        norm_num at h1
        exfalso
        linarith
      · have hm : L (kl w) ∈ Set.range L ∩ Set.range R :=
          ⟨Set.mem_range_self _,⟨kr z,he⟩⟩
        rw [hmeet] at hm
        obtain ⟨u,hu⟩ := hm
        have hr : R (kr z) = R (0,u) := he.trans (hu.symm.trans (hseam u))
        have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) (hR.injective hr)
        rw [hright z (by linarith)] at h1
        norm_num at h1
        exfalso
        linarith
      · have hh := hR.injective he
        apply Prod.ext
        · apply Subtype.ext
          have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) hh
          rw [hright z (by linarith),hright w (by linarith)] at h1
          linarith
        · simpa [kr] using congrArg Prod.snd hh
    refine ⟨F,(hfc.isClosedEmbedding hfi).isEmbedding,?_,?_,?_,?_,?_,fun _ => rfl⟩
    · intro w
      simp [F,kl]
    · intro w
      norm_num [F,kr]
    · intro w
      simp [F,kl]
    · ext x
      constructor
      · rintro ⟨z,rfl⟩
        dsimp only [F]
        split_ifs
        · exact Or.inl (Set.mem_range_self _)
        · exact Or.inr (Set.mem_range_self _)
      · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
        · let t : Interval := ⟨(1-(z.1:ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
          have ht : (t:ℝ) ≤ 1/2 := by dsimp [t]; linarith [z.1.property.1]
          refine ⟨(t,z.2),?_⟩
          rw [show F (t,z.2) = L (kl (t,z.2)) from ite_eq_left ht]
          apply congrArg L
          apply Prod.ext
          · apply Subtype.ext
            rw [hleft _ ht]
            dsimp [t]
            ring
          · rfl
        · let t : Interval := ⟨(1+(z.1:ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
          by_cases hz0 : z.1 = 0
          · have hz : z = (0,z.2) := Prod.ext hz0 rfl
            refine ⟨(⟨1/2,by norm_num⟩,z.2),?_⟩
            rw [hz]
            norm_num [F,kl,hseam]
          · have ht : 1/2 < (t:ℝ) := by
              have hp : 0 < z.1 := lt_of_le_of_ne z.1.property.1 (fun h => hz0 h.symm)
              have hp' : (0:ℝ) < z.1 := hp
              dsimp [t]
              linarith
            refine ⟨(t,z.2),?_⟩
            rw [show F (t,z.2) = R (kr (t,z.2)) from ite_eq_right (not_le.mpr ht)]
            apply congrArg R
            apply Prod.ext
            · apply Subtype.ext
              rw [hright _ (by linarith)]
              dsimp [t]
              ring
            · rfl
    · intro z
      dsimp only [F]
      split_ifs
      · exact ⟨(kl z).1,Or.inl rfl⟩
      · exact ⟨(kr z).1,Or.inr rfl⟩
  intro Q B D hD hDB
  have getCollar (w : Interval) :
      ∃ E : C(Interval × Icc (-1:ℝ) 1,↥Q), IsEmbedding E ∧
        (∀ t, E (t,⟨0,by norm_num⟩) = D (t,w)) ∧
        (∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
        IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
    let a : C(Interval,↥Q) := ⟨fun t => D (t,w),D.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have ha : IsEmbedding a := hD.comp (isEmbedding_prodMkLeft w)
    let pa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
      ⟨a,ha,(hDB (0,w)).mpr (Or.inl rfl),(hDB (1,w)).mpr (Or.inr rfl),
        fun t ht hh => by
          rcases (hDB (t,w)).mp hh with h | h
          · exact ht.1.ne' h
          · exact ht.2.ne h⟩
    obtain ⟨E,hE,hc,he,hi,ho⟩ :=
      CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
        S x R g hg hS hR htarget pa
    refine ⟨E,hE,hc,?_,ho⟩
    intro z
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      by_cases h1 : z.1 = 1
      · exact Or.inr h1
      exact False.elim (hi z.1 ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ z.2 hz)
    · rintro (h | h)
      · rw [show z = (0,z.2) from Prod.ext h rfl]
        exact (he z.2).1
      · rw [show z = (1,z.2) from Prod.ext h rfl]
        exact (he z.2).2
  obtain ⟨EL,hEL,hELc,hELB,hELo⟩ := getCollar 0
  obtain ⟨L,hL,hLc,_,hLD,hLB⟩ := outsideHalf B D hD EL hEL hELc hELB hELo
  obtain ⟨ER0,hER0,hER0c,hER0B,hER0o⟩ := getCollar 1
  let b : C(Interval,↥Q) := ⟨fun t => D (t,1),D.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hbc : range b ⊆ (range L)ᶜ := by
    rintro y ⟨t,rfl⟩ hy
    have hm : D (t,1) ∈ range L ∩ range D := ⟨hy,mem_range_self _⟩
    rw [hLD] at hm
    obtain ⟨s,hs⟩ := hm
    have he := congrArg Prod.snd (hD.injective hs)
    norm_num at he
  obtain ⟨ER,hER,hERc,hERe,hERi,hERo,hERclear⟩ :=
    proper_signed_strip_narrow_in_open B (range L)ᶜ
      (isCompact_range L.continuous).isClosed.isOpen_compl b hbc
      ER0 hER0 hER0c
      (fun w => ⟨(hER0B (0,w)).mpr (Or.inl rfl),(hER0B (1,w)).mpr (Or.inr rfl)⟩)
      (fun s hs w hh => by
        rcases (hER0B (s,w)).mp hh with h | h
        · exact hs.1.ne' h
        · exact hs.2.ne h) hER0o
  have hERB (z) : ER z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      by_cases h1 : z.1 = 1
      · exact Or.inr h1
      exact False.elim (hERi z.1 ⟨bot_lt_iff_ne_bot.mpr h0,lt_top_iff_ne_top.mpr h1⟩ z.2 hz)
    · rintro (h | h)
      · rw [show z = (0,z.2) from Prod.ext h rfl]
        exact (hERe z.2).1
      · rw [show z = (1,z.2) from Prod.ext h rfl]
        exact (hERe z.2).2
  let flip := (Homeomorph.refl Interval).prodCongr unitInterval.symmHomeomorph
  let Dr : C(Interval × Interval,↥Q) := ⟨D ∘ flip,D.continuous.comp flip.continuous⟩
  have hDr : IsEmbedding Dr := hD.comp flip.isEmbedding
  have hDrc (s : Interval) : Dr (s,0) = D (s,1) := by simp [Dr,flip,unitInterval.symm]
  have hDrange : range Dr = range D := by
    change range (D ∘ flip) = range D
    exact flip.surjective.range_comp _
  obtain ⟨R',hR',hRc,hRcarrier,hRD,hRB⟩ :=
    outsideHalf B Dr hDr ER hER (fun s => (hERc s).trans (hDrc s).symm) hERB hERo
  have hRc' (s : Interval) : R' (s,0) = D (s,1) := (hRc s).trans (hDrc s)
  have hRD' : range R' ∩ range D = range (fun s : Interval => D (s,1)) := by
    rw [←hDrange,hRD]
    congr 1
    funext s
    exact hDrc s
  have hLR : Disjoint (range L) (range R') := disjoint_left.mpr (fun y hyL hyR =>
    (hERclear (hRcarrier hyR)) hyL)
  let sw := Homeomorph.prodComm Interval Interval
  let DL := L ∘ sw
  let DD := D ∘ sw
  let RR := R' ∘ sw
  have hDL : IsEmbedding DL := hL.comp sw.isEmbedding
  have hDD : IsEmbedding DD := hD.comp sw.isEmbedding
  have hRR : IsEmbedding RR := hR'.comp sw.isEmbedding
  have hDLr : range DL = range L := sw.surjective.range_comp _
  have hDDr : range DD = range D := sw.surjective.range_comp _
  have hRRr : range RR = range R' := sw.surjective.range_comp _
  have hseam (s) : DL (0,s) = DD (0,s) := hLc s
  have hmeet : range DL ∩ range DD = range (fun s => DL (0,s)) := by
    rw [hDLr,hDDr,hLD]
    congr 1
    funext s
    exact (hLc s).symm
  obtain ⟨F,hF,hF0,hF1,hFmid,hFrange,hFcover,hFformula⟩ := glue DL DD hDL hDD hseam hmeet
  let fv := unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl Interval)
  let FR := F ∘ fv
  have hFR : IsEmbedding FR := hF.comp fv.isEmbedding
  have hFRr : range FR = range F := fv.surjective.range_comp _
  have hFR0 (s) : FR (0,s) = D (s,1) := by
    change F (unitInterval.symm 0,s) = _
    rw [unitInterval.symm_zero,hF1]
    rfl
  have hmeetR : range FR ∩ range RR = range (fun s => FR (0,s)) := by
    rw [hFRr,hRRr,hFrange,hDLr,hDDr,union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp hLR,empty_union,inter_comm,hRD']
    congr 1
    funext s
    exact (hFR0 s).symm
  obtain ⟨G,hG,hG0,hG1,hGmid,hGrange,hGcover,hGformula⟩ :=
    glue FR RR hFR hRR (fun s => (hFR0 s).trans (hRc' s).symm) hmeetR
  let u : Interval := ⟨1/4,by norm_num⟩
  let v : Interval := ⟨1/2,by norm_num⟩
  have hGu (s : Interval) : G (u,s) = D (s,0) := by
    rw [hGformula]
    have hu : (u:ℝ) ≤ 1/2 := by norm_num [u]
    rw [if_pos hu]
    have ht : projIcc 0 1 zero_le_one (1-2*(u:ℝ)) = (⟨1/2,by norm_num⟩ : Interval) := by
      have hexpr : 1-2*(u:ℝ) = 1/2 := by norm_num [u]
      rw [hexpr]
      exact projIcc_of_mem zero_le_one (by norm_num)
    rw [ht]
    change F (unitInterval.symm ⟨1/2,by norm_num⟩,s) = _
    have hh : unitInterval.symm ⟨1/2,by norm_num⟩ = (⟨1/2,by norm_num⟩ : Interval) := by
      apply Subtype.ext
      norm_num [unitInterval.symm]
    rw [hh,hFmid]
    exact hLc s
  have hGv (s : Interval) : G (v,s) = D (s,1) := (hGmid s).trans (hFR0 s)
  have hGB (z : Interval × Interval) : G z ∈ B ↔ z.2 = 0 ∨ z.2 = 1 := by
    obtain ⟨t,ht⟩ := hGcover z
    rcases ht with ht | ht
    · have ht' : FR (t,z.2) = F (unitInterval.symm t,z.2) := rfl
      obtain ⟨w,hw⟩ := hFcover (unitInterval.symm t,z.2)
      rcases hw with hw | hw
      · rw [ht,ht',hw]
        exact hLB (z.2,w)
      · rw [ht,ht',hw]
        exact hDB (z.2,w)
    · rw [ht]
      exact hRB (z.2,t)
  obtain ⟨k,hk⟩ := signed_interval_width_homeomorph
  let coord := ((Homeomorph.refl Interval).prodCongr k.symm).trans sw
  let E : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨G ∘ coord,hG.continuous.comp coord.continuous⟩
  have hE : IsEmbedding E := hG.comp coord.isEmbedding
  have hEB (z) : E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := hGB (coord z)
  have he0 (w) : E (0,w) ∈ B := (hEB (0,w)).mpr (Or.inl rfl)
  have he1 (w) : E (1,w) ∈ B := (hEB (1,w)).mpr (Or.inr rfl)
  have hei (s : Interval) (hs : s ∈ Ioo (0:Interval) 1) (w) : E (s,w) ∉ B := by
    intro hh
    rcases (hEB (s,w)).mp hh with h | h
    · exact hs.1.ne' h
    · exact hs.2.ne h
  have heo : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1}) :=
    source_original_boundary_band_relative_open g hg hS hR htarget E hE
      (fun w => ⟨he0 w,he1 w⟩) hei
  have hEu (s : Interval) : E (s,k u) = D (s,0) := by
    change G (k.symm (k u),s) = _
    rw [k.symm_apply_apply]
    exact hGu s
  have hEv (s : Interval) : E (s,k v) = D (s,1) := by
    change G (k.symm (k v),s) = _
    rw [k.symm_apply_apply]
    exact hGv s
  refine ⟨E,k u,k v,hE,?_,?_,?_,?_,?_,hEB,heo⟩
  · rw [hk]
    norm_num [u]
  · rw [hk]
    norm_num [v]
  · intro hh
    have he := congrArg Subtype.val (k.injective hh)
    norm_num [u,v] at he
  · exact congrArg range (funext hEu)
  · exact congrArg range (funext hEv)

end CoherentEndpointMotion.FreeBoundaryNullGeometry
