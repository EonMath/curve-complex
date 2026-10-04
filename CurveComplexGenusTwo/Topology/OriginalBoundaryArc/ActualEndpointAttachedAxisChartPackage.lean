import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Topology.RestrictedLink.PlanarHalfArcCompletionHeaders
import CurveComplexGenusTwo.Topology.PrescribedCrosscut
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.CapBandGeometry.BandRegularity
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapSide
import Schoenflies.PolyLocal
import Mathlib

namespace CurveComplexGenusTwo.SourceTopology.EulerThreeArcs
open CurveComplex Set Metric Schoenflies
set_option maxHeartbeats 16000000

abbrev openDisk (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ) : Set S :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
abbrev closedDisk (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ) : Set S :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
abbrev boundary (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ) : Set S :=
  (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R

/-- Proposed actual disk-boundary/proper-arc endpoint chart. Statement only,
awaiting source review. No local straightening or collar certificate is input. -/
theorem source_proper_arc_initial_endpoint_attached_axis_chart
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (a : C(Interval, ↥(openDisk S x R)ᶜ))
    (hemb : Topology.IsEmbedding a)
    (hend0 : (a ⟨0, by norm_num⟩).val ∈ boundary S x R)
    (hend1 : (a ⟨1, by norm_num⟩).val ∈ boundary S x R)
    (hproper : ∀ t, t ∈ Set.Ioo (0 : Interval) 1 →
      (a t).val ∉ boundary S x R) :
    ∃ (U : Set S) (V : Set (ℝ × ℝ)),
      ∃ hpU : (a ⟨0, by norm_num⟩).val ∈ U,
      ∃ h : U ≃ₜ V,
        IsOpen U ∧ IsOpen V ∧
        ((h ⟨(a ⟨0, by norm_num⟩).val, hpU⟩ : V) : ℝ × ℝ) = (0,0) ∧
        (a ⟨1, by norm_num⟩).val ∉ U ∧
        (∀ y hy, y ∈ closedDisk S x R ↔
          (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 ≤ 0) ∧
        (∀ y hy, y ∈ boundary S x R ↔
          (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 = 0) ∧
        (∀ y hy, y ∈ Subtype.val '' Set.range a ↔
          0 ≤ (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 ∧
          (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).2 = 0) := by
  classical
  have geometry (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      (E : OpenPartialHomeomorph S Plane) (p : Plane) (R : ℝ) (hR : 0<R)
      (htarget : closedBall p R ⊆ E.target) :
      let D := E.symm '' closedBall p R
      IsCompact D ∧ closure (interior D)=D ∧
        interior D=E.symm '' ball p R ∧ frontier D=E.symm '' sphere p R := by
    dsimp only
    let D : Set S := E.symm '' closedBall p R
    have hD : IsCompact D := (isCompact_closedBall _ _).image_of_continuousOn
      (E.continuousOn_symm.mono htarget)
    have hDs : D ⊆ E.source := by
      rintro y ⟨z,hz,rfl⟩
      exact E.map_target (htarget hz)
    have hI : E.IsImage D (closedBall p R) := by
      intro y hy
      constructor
      · intro hz
        exact ⟨E y,hz,E.left_inv hy⟩
      · rintro ⟨z,hz,rfl⟩
        rwa [E.right_inv (htarget hz)]
    have hi : interior D=E.symm '' ball p R := by
      have hh := hI.interior.symm_image_eq
      rw [interior_closedBall _ hR.ne',inter_eq_right.mpr
        (Metric.ball_subset_closedBall.trans htarget),inter_eq_right.mpr
        ((interior_subset : interior D ⊆ D).trans hDs)] at hh
      exact hh.symm
    have hf : frontier D=E.symm '' sphere p R := by
      have hh := hI.frontier.symm_image_eq
      rw [frontier_closedBall _ hR.ne',inter_eq_right.mpr
        (sphere_subset_closedBall.trans htarget),inter_eq_right.mpr
        (hD.isClosed.frontier_subset.trans hDs)] at hh
      exact hh.symm
    let f : closedBall p R → S := fun z => E.symm z.val
    have hfc : Continuous f := by
      apply E.continuousOn_symm.comp_continuous continuous_subtype_val
      intro z
      exact htarget z.property
    have hfi : Function.Injective f := by
      intro y z he
      exact Subtype.ext (E.symm.injOn (htarget y.property) (htarget z.property) he)
    have hfe : Topology.IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
    have hrange : range f = D := by
      ext y
      constructor
      · rintro ⟨z,rfl⟩
        exact ⟨z.val,z.property,rfl⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨z,hz⟩,rfl⟩
    have hreg : closure (interior D)=D := by
      rw [←hrange]
      apply embedded_planar_region_regular_closed _ (isCompact_closedBall _ _) _ f hfe
      rw [interior_closedBall _ hR.ne',closure_ball _ hR.ne']
    exact ⟨hD,hreg,hi,hf⟩
  have boundaryChart (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
      (E : OpenPartialHomeomorph S Plane) (p : Plane) (R : ℝ) (hR : 0<R)
      (htarget : closedBall p R ⊆ E.target) (y z : S)
      (hy : y∈E.symm '' sphere p R) (hzy : z≠y) :
      ∃ A : OpenPartialHomeomorph S Plane,
        y∈A.source ∧ A y=0 ∧ A.source ⊆ E.source ∧ z∉A.source ∧
        Plane.closedSquare 0 1 ⊆ A.target ∧
        ∀ w∈A.source, w∈E.symm '' sphere p R ↔ A w 1=0 := by
    classical
    have hcircle (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
        (E : OpenPartialHomeomorph S Plane) (p : Plane) (R : ℝ) (hR : 0<R)
        (htarget : closedBall p R ⊆ E.target) :
        ∃ c : Curve S, c.image=E.symm '' sphere p R := by
      classical
      let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm)
      have hnorm (z : ℂ) : ‖L z‖=‖z‖ := by
        change ‖Plane.mk z.re z.im‖=‖z‖
        simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,
          Complex.norm_def,Complex.normSq_apply,Real.norm_eq_abs,pow_two]
      let q : Circle → Plane := fun z => p+R • L (z:ℂ)
      have hqmem (z : Circle) : q z∈sphere p R := by
        rw [mem_sphere,dist_eq_norm]
        dsimp [q]
        rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hnorm,Circle.norm_coe,mul_one]
      have hqc : Continuous q := by dsimp [q]; fun_prop
      have hqi : Function.Injective q := by
        intro z w he
        have hs : R • L (z:ℂ)=R • L (w:ℂ) := add_left_cancel he
        exact Subtype.ext (L.injective ((smul_right_injective Plane hR.ne') hs))
      have hqr : range q=sphere p R := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          exact hqmem z
        · intro hy
          let v : Plane := R⁻¹ • (y-p)
          have hv : ‖v‖=1 := by
            dsimp [v]
            rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
            have hn : ‖y-p‖=R := by simpa [mem_sphere,dist_eq_norm] using hy
            rw [hn,inv_mul_cancel₀ hR.ne']
          have hz : ‖L.symm v‖=1 := by rw [←hnorm (L.symm v),L.apply_symm_apply,hv]
          let z : Circle := ⟨L.symm v,by change L.symm v∈sphere (0:ℂ) 1; simpa only [mem_sphere,dist_zero_right] using hz⟩
          refine ⟨z,?_⟩
          dsimp [q,z]
          rw [L.apply_symm_apply]
          dsimp [v]
          rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
          abel
      have hqt (z : Circle) : q z∈E.target := htarget (sphere_subset_closedBall (hqmem z))
      let f : Circle → S := E.symm ∘ q
      have hfc : Continuous f := E.continuousOn_symm.comp_continuous hqc hqt
      have hfi : Function.Injective f := by
        intro z w he
        exact hqi (E.symm.injOn (hqt z) (hqt w) he)
      let c : Curve S := ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding⟩
      refine ⟨c,?_⟩
      change range (E.symm ∘ q)=_
      rw [range_comp,hqr]
    obtain ⟨c,hc⟩ := hcircle S E p R hR htarget
    have hyc : y∈c.image := hc.symm ▸ hy
    have hyE : y∈E.source := by
      obtain ⟨u,hu,rfl⟩ := hy
      exact E.map_target (htarget (sphere_subset_closedBall hu))
    let W : Set S := E.source ∩ ({z}:Set S)ᶜ
    have hW : IsOpen W := E.open_source.inter isClosed_singleton.isOpen_compl
    have hyW : y∈W := ⟨hyE,by simpa only [mem_compl_iff,mem_singleton_iff] using Ne.symm hzy⟩
    obtain ⟨A,hyA,hAy,hAW,hAt,haxis⟩ := PositionUniverseV2.position_curve_crosscut_chart S c y hyc W hW hyW
    refine ⟨A,hyA,hAy,fun w hw => (hAW hw).1,?_,hAt,?_⟩
    · intro hz
      exact (hAW hz).2 (mem_singleton z)
    · intro w hw
      rw [←hc]
      exact haxis w hw
  have endpointChart (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      (A : OpenPartialHomeomorph S Plane) (B : Set S) (f : C(Interval,S))
      (hf : Topology.IsEmbedding f) (hsource : f 0∈A.source) (hzero : A (f 0)=0)
      (haxis : ∀ w∈A.source, w∈B ↔ A w 1=0)
      (hproper : ∀ t, t∈Ioo (0:Interval) 1 → f t∉B) :
      ∃ E : OpenPartialHomeomorph S Plane,
        f 0∈E.source ∧ E (f 0)=0 ∧ E.source⊆A.source ∧ f 1∉E.source ∧
        (∀ w∈E.source, w∈B ↔ E w 1=0) ∧
        (∀ w∈E.source, w∈range f ↔ E w 0=0 ∧ 0≤E w 1) := by
    classical
    have side (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
        (A : OpenPartialHomeomorph S Plane) (B : Set S) (f : C(Interval,S))
        (hzero : f 0∈A.source)
        (haxis : ∀ y∈A.source, y∈B ↔ A y 1=0)
        (hproper : ∀ t, t∈Ioo (0:Interval) 1 → f t∉B) :
        ∃ b : Interval, 0<(b:ℝ) ∧ (b:ℝ)<1 ∧
          (∀ t : Interval, (t:ℝ)≤b → f t∈A.source) ∧
          ((∀ t : Interval, 0<(t:ℝ) → (t:ℝ)≤b → 0<A (f t) 1) ∨
           (∀ t : Interval, 0<(t:ℝ) → (t:ℝ)≤b → A (f t) 1<0)) := by
      classical
      have hpre : IsOpen (f ⁻¹' A.source) := A.open_source.preimage f.continuous
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds hzero)
      let v : ℝ := min (r/2) (1/2)
      have hv : 0<v := by dsimp [v]; positivity
      have hv1 : v<1 := by have := min_le_right (r/2) (1/2:ℝ); dsimp [v]; linarith
      have hvr : v<r := by have := min_le_left (r/2) (1/2:ℝ); dsimp [v]; linarith
      let b : Interval := ⟨v,hv.le,hv1.le⟩
      have hsource (t : Interval) (ht : (t:ℝ)≤b) : f t∈A.source := by
        apply hball
        rw [mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |(t:ℝ)-0|<r
        rw [sub_zero,abs_of_nonneg t.property.1]
        exact ht.trans_lt hvr
      let τ : Interval → Interval := fun u => ⟨v*(u:ℝ),by
        constructor
        · exact mul_nonneg hv.le u.property.1
        · exact (mul_le_mul_of_nonneg_left u.property.2 hv.le).trans (by simpa using hv1.le)⟩
      have hτc : Continuous τ := by dsimp [τ]; fun_prop
      have hτb (u : Interval) : ((τ u):ℝ)≤b := by
        change v*(u:ℝ)≤v
        nlinarith [u.property.2]
      let n : Interval → ℝ := fun u => A (f (τ u)) 1
      have hev : Continuous (fun z : Plane => z 1) := by fun_prop
      have hnc : Continuous n := hev.comp
        (A.continuousOn_toFun.comp_continuous (f.continuous.comp hτc) (fun u => hsource _ (hτb u)))
      have hn0 (u : Interval) (hu : u∈Ioc (0:Interval) 1) : n u≠0 := by
        intro hn
        have hti : τ u∈Ioo (0:Interval) 1 := by
          constructor
          · change 0<v*(u:ℝ)
            exact mul_pos hv hu.1
          · change v*(u:ℝ)<1
            exact (hτb u).trans_lt hv1
        exact hproper _ hti ((haxis _ (hsource _ (hτb u))).mpr hn)
      have him : IsPreconnected (n '' Ioc (0:Interval) 1) :=
        isPreconnected_Ioc.image n hnc.continuousOn
      have hsplit : n '' Ioc (0:Interval) 1 ⊆ Ioi (0:ℝ) ∪ Iio (0:ℝ) := by
        rintro y ⟨u,hu,rfl⟩
        rcases lt_or_gt_of_ne (hn0 u hu) with hlt|hgt
        · exact Or.inr hlt
        · exact Or.inl hgt
      rcases him.subset_or_subset isOpen_Ioi isOpen_Iio (Set.disjoint_left.mpr (by intro y hy hz; change 0<y at hy; change y<0 at hz; linarith)) hsplit with hpos|hneg
      · refine ⟨b,hv,hv1,hsource,Or.inl ?_⟩
        intro t ht0 htb
        let u : Interval := ⟨(t:ℝ)/v,div_nonneg t.property.1 hv.le,(div_le_one hv).mpr htb⟩
        have hτu : τ u=t := by apply Subtype.ext; dsimp [τ,u]; field_simp
        have hu : u∈Ioc (0:Interval) 1 := ⟨div_pos ht0 hv,u.property.2⟩
        have hh := hpos (mem_image_of_mem n hu)
        change 0<A (f (τ u)) 1 at hh
        rwa [hτu] at hh
      · refine ⟨b,hv,hv1,hsource,Or.inr ?_⟩
        intro t ht0 htb
        let u : Interval := ⟨(t:ℝ)/v,div_nonneg t.property.1 hv.le,(div_le_one hv).mpr htb⟩
        have hτu : τ u=t := by apply Subtype.ext; dsimp [τ,u]; field_simp
        have hu : u∈Ioc (0:Interval) 1 := ⟨div_pos ht0 hv,u.property.2⟩
        have hh := hneg (mem_image_of_mem n hu)
        change A (f (τ u)) 1<0 at hh
        rwa [hτu] at hh
    have joint (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
        (A : OpenPartialHomeomorph S Plane) (B : Set S) (f : C(Interval,S))
        (hf : Topology.IsEmbedding f) (hsource : f 0∈A.source) (hzero : A (f 0)=0)
        (haxis : ∀ w∈A.source, w∈B ↔ A w 1=0)
        (b₀ : Interval) (hb₀ : 0<(b₀:ℝ))
        (hside : ∀ t : Interval, 0<(t:ℝ) → (t:ℝ)≤b₀ → 0<A (f t) 1) :
        ∃ T : Plane ≃ₜ Plane, ∃ U : Set S,
          IsOpen U ∧ f 0∈U ∧ U⊆A.source ∧ f 1∉U ∧ T 0=0 ∧
          (∀ w∈U, w∈B ↔ T (A w) 1=0) ∧
          (∀ w∈U, w∈range f ↔ T (A w) 0=0 ∧ 0≤T (A w) 1) := by
      classical
      have halfarc (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
          (A : OpenPartialHomeomorph S Plane) (f : C(Interval,S))
          (hf : Topology.IsEmbedding f) (hsource : f 0∈A.source) (hzero : A (f 0)=0)
          (b₀ : Interval) (hb₀ : 0<(b₀:ℝ))
          (hside : ∀ t : Interval, 0<(t:ℝ) → (t:ℝ)≤b₀ → 0<A (f t) 1) :
          ∃ b : Interval, 0<(b:ℝ) ∧ (b:ℝ)<1 ∧ (b:ℝ)≤b₀ ∧
            (∀ t : Interval, (t:ℝ)≤b → f t∈A.source) ∧
            ∃ p : C(Interval,Plane), Topology.IsEmbedding p ∧
              (∀ u : Interval, p u=A (f ⟨(b:ℝ)*(u:ℝ),by
                constructor
                · exact mul_nonneg b.property.1 u.property.1
                · exact (mul_le_mul_of_nonneg_left u.property.2 b.property.1).trans
                    (by simpa using b.property.2)⟩)-Plane.mk 0 1) ∧
              p 0=Plane.mk 0 (-1) ∧
              IsArcBetween (range p) (p 0) (p 1) ∧
              range p \ {p 0} ⊆ Plane.openSquare 0 1 := by
        classical
        have hAc : ContinuousAt (fun t : Interval => A (f t)) 0 :=
          (A.continuousOn_toFun.continuousAt (A.open_source.mem_nhds hsource)).comp f.continuous.continuousAt
        have he0 : Continuous (fun z : Plane => z 0) := by fun_prop
        have he1 : Continuous (fun z : Plane => z 1) := by fun_prop
        let O : Set Plane := {z | |z 0|<1/2 ∧ |z 1|<1/2}
        have hO : IsOpen O := (isOpen_lt (continuous_abs.comp he0) continuous_const).inter
          (isOpen_lt (continuous_abs.comp he1) continuous_const)
        have h0O : A (f 0)∈O := by rw [hzero]; norm_num [O]
        have hn : (f ⁻¹' A.source) ∩ ((fun t => A (f t)) ⁻¹' O)∈nhds (0:Interval) :=
          Filter.inter_mem (f.continuous.continuousAt.preimage_mem_nhds (A.open_source.mem_nhds hsource))
            (hAc.preimage_mem_nhds (hO.mem_nhds h0O))
        obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hn
        let v : ℝ := min (min (r/2) (1/2)) (b₀:ℝ)
        have hv : 0<v := by dsimp [v]; positivity
        have hv1 : v<1 := by have := min_le_right (r/2) (1/2:ℝ); have := min_le_left (min (r/2) (1/2)) (b₀:ℝ); dsimp [v]; linarith
        have hvr : v<r := by have := min_le_left (r/2) (1/2:ℝ); have := min_le_left (min (r/2) (1/2)) (b₀:ℝ); dsimp [v]; linarith
        have hvb : v≤b₀ := min_le_right _ _
        let b : Interval := ⟨v,hv.le,hv1.le⟩
        have hsmall (t : Interval) (ht : (t:ℝ)≤b) : f t∈A.source ∧ A (f t)∈O := by
          apply hball
          rw [mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |(t:ℝ)-0|<r
          rw [sub_zero,abs_of_nonneg t.property.1]
          exact ht.trans_lt hvr
        let τ : Interval → Interval := fun u => ⟨v*(u:ℝ),by
          constructor
          · exact mul_nonneg hv.le u.property.1
          · exact (mul_le_mul_of_nonneg_left u.property.2 hv.le).trans (by simpa using hv1.le)⟩
        have hτc : Continuous τ := by dsimp [τ]; fun_prop
        have hτb (u : Interval) : ((τ u):ℝ)≤b := by change v*(u:ℝ)≤v; nlinarith [u.property.2]
        have hpc : Continuous (fun u => A (f (τ u))-Plane.mk 0 1) :=
          (A.continuousOn_toFun.comp_continuous (f.continuous.comp hτc)
            (fun u => (hsmall _ (hτb u)).1)).sub continuous_const
        let p : C(Interval,Plane) := ⟨_,hpc⟩
        have hpi : Function.Injective p := by
          intro u w he
          have heA : A (f (τ u))=A (f (τ w)) := sub_left_injective he
          have heτ := hf.injective (A.injOn (hsmall _ (hτb u)).1 (hsmall _ (hτb w)).1 heA)
          apply Subtype.ext
          have heval := congrArg Subtype.val heτ
          dsimp [τ] at heval
          exact mul_left_cancel₀ hv.ne' heval
        have hp0 : p 0=Plane.mk 0 (-1) := by
          have hτ0 : τ 0=0 := by apply Subtype.ext; simp [τ]
          change A (f (τ 0))-Plane.mk 0 1=_
          rw [hτ0,hzero]
          ext i
          fin_cases i <;> simp [Plane.mk]
        have harc : IsArcBetween (range p) (p 0) (p 1) := by
          let g : ℝ → Plane := p ∘ projIcc 0 1 zero_le_one
          refine ⟨g,(p.continuous.comp continuous_projIcc).continuousOn,?_,?_,?_,?_⟩
          · intro t ht u hu he
            have he := hpi he
            simpa [g,projIcc_of_mem,ht,hu] using congrArg Subtype.val he
          · ext z
            constructor
            · rintro ⟨t,ht,rfl⟩; exact ⟨_,rfl⟩
            · rintro ⟨t,rfl⟩; refine ⟨t,t.property,?_⟩; simp [g,projIcc_of_mem]
          · simp [g,projIcc_of_mem]
          · simp [g,projIcc_of_mem]
        refine ⟨b,hv,hv1,hvb,(fun t ht => (hsmall t ht).1),p,
          ((p.continuous.isClosedEmbedding hpi).isEmbedding),
          (fun u => rfl),hp0,harc,?_⟩
        rintro z ⟨⟨u,rfl⟩,hu⟩
        have hu0 : 0<(u:ℝ) := by
          have hne : u≠0 := fun he => hu (he ▸ mem_singleton (p 0))
          exact lt_of_le_of_ne u.property.1 (fun he => hne (Subtype.ext he.symm))
        have ht0 : 0<((τ u):ℝ) := mul_pos hv hu0
        have hpos := hside (τ u) ht0 ((hτb u).trans hvb)
        have hbounds := (hsmall _ (hτb u)).2
        change |A (f (τ u)) 0|<1/2 ∧ |A (f (τ u)) 1|<1/2 at hbounds
        rw [mem_openSquare_zero_one]
        change max |(A (f (τ u))-Plane.mk 0 1) 0| |(A (f (τ u))-Plane.mk 0 1) 1|<1
        simp only [PiLp.sub_apply,Plane.mk]
        apply max_lt
        · simpa using hbounds.1.trans (by norm_num : (1/2:ℝ)<1)
        · change |A (f (τ u)) 1-1|<1
          rw [abs_lt]
          constructor
          · linarith
          · have := (abs_lt.mp hbounds.2).2; linarith
      have vertical : ∃ Q : Set Plane,
          IsArcBetween Q (Plane.mk 0 (-1)) (Plane.mk 0 1) ∧
          Plane.mk 0 (-1)∈modelCurve ∧ Plane.mk 0 1∈modelCurve ∧
          Plane.mk 0 1≠Plane.mk 0 (-1) ∧
          Q \ {Plane.mk 0 (-1),Plane.mk 0 1} ⊆ Plane.openSquare 0 1 ∧
          (∀ z : Plane, z∈Q ↔ z 0=0 ∧ -1≤z 1 ∧ z 1≤1) := by
        let p : ℝ → Plane := fun t => Plane.mk 0 (2*t-1)
        have hpc : Continuous p := by dsimp [p,Plane.mk]; fun_prop
        have hpi : Function.Injective p := by
          intro t u he
          have he1 := congrArg (fun z : Plane => z 1) he
          change 2*t-1=2*u-1 at he1
          linarith
        let Q : Set Plane := p '' Icc (0:ℝ) 1
        have hp0 : p 0=Plane.mk 0 (-1) := by simp [p]
        have hp1 : p 1=Plane.mk 0 1 := by norm_num [p]
        have hQ : IsArcBetween Q (Plane.mk 0 (-1)) (Plane.mk 0 1) :=
          ⟨p,hpc.continuousOn,hpi.injOn,rfl,hp0,hp1⟩
        have hmem (z : Plane) : z∈Q ↔ z 0=0 ∧ -1≤z 1 ∧ z 1≤1 := by
          constructor
          · rintro ⟨t,ht,rfl⟩
            change 0=0 ∧ -1≤2*t-1 ∧ 2*t-1≤1
            exact ⟨rfl,by linarith [ht.1],by linarith [ht.2]⟩
          · rintro ⟨hz0,hzlo,hzhi⟩
            refine ⟨(z 1+1)/2,⟨by linarith,by linarith⟩,?_⟩
            ext i
            fin_cases i
            · simpa [p,Plane.mk] using hz0.symm
            · change 2*((z 1+1)/2)-1=z 1
              ring
        refine ⟨Q,hQ,?_,?_,?_,?_,hmem⟩
        · norm_num [modelCurve,Plane.supNorm,Plane.mk]
        · norm_num [modelCurve,Plane.supNorm,Plane.mk]
        · intro he
          have := congrArg (fun z : Plane => z 1) he
          norm_num [Plane.mk] at this
        · rintro z ⟨hz,hends⟩
          obtain ⟨hz0,hzlo,hzhi⟩ := (hmem z).mp hz
          have hlo : -1<z 1 := by
            apply lt_of_le_of_ne hzlo
            intro he
            apply hends
            left
            apply (show z=Plane.mk 0 (-1) from ?_)
            ext i
            fin_cases i <;> simp [Plane.mk,hz0,he]
          have hhi : z 1<1 := by
            apply lt_of_le_of_ne hzhi
            intro he
            apply hends
            right
            apply (show z=Plane.mk 0 1 from ?_)
            ext i
            fin_cases i <;> simp [Plane.mk,hz0,he]
          rw [mem_openSquare_zero_one]
          change max |z 0| |z 1|<1
          rw [hz0,abs_zero,max_lt_iff]
          exact ⟨by norm_num,abs_lt.mpr ⟨hlo,hhi⟩⟩
      have relative {A Q : Set Plane} {a q b : Plane}
          (hA : IsArcBetween A a q) (hQ : IsArcBetween Q a b)
          (ha : a ∈ modelCurve) (hb : b ∈ modelCurve) (hba : b ≠ a)
          (hAi : A \ {a} ⊆ Plane.openSquare 0 1)
          (hQi : Q \ {a,b} ⊆ Plane.openSquare 0 1) :
          ∃ F : Plane ≃ₜ Plane, ∃ U : Set Plane,
            IsOpen U ∧ a ∈ U ∧ F a = a ∧
            (∀ z, z ∉ Plane.openSquare 0 1 → F z = z) ∧
            (∀ z ∈ U, z ∈ F '' A ↔ z ∈ Q) := by
        classical
        obtain ⟨B,hB,hAB,hBi⟩ := HyperellipticModel.planar_half_arc_completion
          isJordanCurve_modelCurve hA ha hb hba (by simpa only [inside_modelCurve] using hAi)
        have hP : IsArcBetween (A ∪ B) a b := hA.concatenate hB (by
          intro z hzA hzB
          exact mem_singleton_iff.mp (hAB ▸ (show z ∈ A ∩ B from ⟨hzA,hzB⟩)))
        have hPi : (A ∪ B) \ {a,b} ⊆ Plane.openSquare 0 1 := by
          rintro z ⟨hz,hends⟩
          rcases hz with hzA|hzB
          · exact hAi ⟨hzA,fun he => hends (Or.inl he)⟩
          · simpa only [inside_modelCurve] using hBi ⟨hzB,fun he => hends (Or.inr he)⟩
        obtain ⟨H⟩ := exists_arcHomeo hP hQ
        obtain ⟨F,hFH,hFQ,hfixed⟩ := prescribed_relative_crosscut_replacement
          (A ∪ B) Q a b hP hQ ha hb hPi hQi H
        have hFa : F a=a := (hFH a (Or.inl hA.left_mem)).trans H.map_left
        have haB : a ∉ B := by
          intro h
          have he : a=q := mem_singleton_iff.mp (hAB ▸ (show a∈A∩B from ⟨hA.left_mem,h⟩))
          exact hA.ne he
        have haFB : a ∉ F '' B := by
          rintro ⟨z,hz,he⟩
          exact haB (F.injective (he.trans hFa.symm) ▸ hz)
        refine ⟨F,(F '' B)ᶜ,(hB.isArc.isCompact.image F.continuous).isClosed.isOpen_compl,
          haFB,hFa,hfixed,?_⟩
        intro z hz
        constructor
        · intro hm
          rw [←hFQ]
          exact image_mono subset_union_left hm
        · intro hm
          rw [←hFQ,image_union] at hm
          exact hm.resolve_right hz
      obtain ⟨b,hb,hb1,hbb₀,hbs,p,hp,hpe,hp0,hparc,hpin⟩ := halfarc S A f hf hsource hzero b₀ hb₀ hside
      obtain ⟨Q,hQ,hbottom,htop,hne,hQi,hQmem⟩ := vertical
      obtain ⟨F,W,hW,hbottomW,hFbottom,hfixed,hgerm⟩ := relative
        (hp0 ▸ hparc) hQ hbottom htop hne (hp0 ▸ hpin) hQi
      let c : Plane := Plane.mk 0 1
      let T : Plane ≃ₜ Plane := (Homeomorph.subRight c).trans (F.trans (Homeomorph.addRight c))
      have hT (z : Plane) : T z=F (z-c)+c := rfl
      have hc : (Plane.mk 0 (-1))+c=0 := by ext i; fin_cases i <;> norm_num [c,Plane.mk]
      have h0 : T 0=0 := by
        rw [hT]
        have hh : (0:Plane)-c=Plane.mk 0 (-1) := by ext i; fin_cases i <;> norm_num [c,Plane.mk]
        rw [hh,hFbottom,hc]
      have hTaxis (z : Plane) (hz : z 1=0) : T z=z := by
        rw [hT,hfixed]
        · exact sub_add_cancel z c
        · intro hm
          have hh := (max_lt_iff.mp (mem_openSquare_zero_one.mp hm)).2
          change |(z-c) 1|<1 at hh
          have he : (z-c) 1=(-1:ℝ) := by simp [c,Plane.mk,hz]
          rw [he] at hh
          norm_num at hh
      have hline (z : Plane) : T z 1=0 ↔ z 1=0 := by
        constructor
        · intro hz
          have he := T.injective (hTaxis (T z) hz)
          have he' : T z=z := he
          rw [←he']; exact hz
        · intro hz; rw [hTaxis z hz]; exact hz
      let K : Set S := f '' Ici b
      have hK : IsClosed K := (isClosed_Ici.isCompact.image f.continuous).isClosed
      have h0K : f 0∉K := by
        rintro ⟨t,ht,he⟩
        have het := hf.injective he
        subst t
        exact not_le_of_gt hb ht
      let L : Set Plane := W ∩ {z : Plane | z 1<1}
      have hL : IsOpen L := hW.inter (isOpen_lt (by fun_prop) continuous_const)
      let U : Set S := (A.source ∩ A ⁻¹' (fun z : Plane => F (z-c)) ⁻¹' L) ∩ Kᶜ
      have hU : IsOpen U := (A.isOpen_inter_preimage
        (hL.preimage (by fun_prop : Continuous (fun z : Plane => F (z-c))))).inter hK.isOpen_compl
      have hzeroF : F (A (f 0)-c)=Plane.mk 0 (-1) := by
        rw [hzero]
        have hh : (0:Plane)-c=Plane.mk 0 (-1) := by ext i; fin_cases i <;> norm_num [c,Plane.mk]
        rw [hh,hFbottom]
      have h0U : f 0∈U := by
        refine ⟨⟨hsource,?_⟩,h0K⟩
        change F (A (f 0)-c)∈L
        rw [hzeroF]
        exact ⟨hbottomW,by norm_num [Plane.mk]⟩
      have hUsource : U⊆A.source := fun w hw => hw.1.1
      have h1U : f 1∉U := by
        intro hm
        exact hm.2 ⟨1,by exact b.property.2,rfl⟩
      refine ⟨T,U,hU,h0U,hUsource,h1U,h0,?_,?_⟩
      · intro w hw
        exact (haxis w (hUsource hw)).trans (hline (A w)).symm
      · intro w hw
        let z : Plane := F (A w-c)
        have hzW : z∈W := hw.1.2.1
        have hzhi : z 1<1 := hw.1.2.2
        have hcoord0 : T (A w) 0=z 0 := by simp [hT,z,c,Plane.mk]
        have hcoord1 : T (A w) 1=z 1+1 := by simp [hT,z,c,Plane.mk]
        have hQaxis : z∈Q ↔ T (A w) 0=0 ∧ 0≤T (A w) 1 := by
          rw [hQmem,hcoord0,hcoord1]
          constructor
          · rintro ⟨h0,hl,_⟩; exact ⟨h0,by linarith⟩
          · rintro ⟨h0,hl⟩; exact ⟨h0,by linarith,hzhi.le⟩
        rw [←hQaxis,←hgerm z hzW]
        constructor
        · rintro ⟨t,ht⟩
          have htb : (t:ℝ)<b := by
            by_contra h
            exact hw.2 ⟨t,not_lt.mp h,ht⟩
          let u : Interval := ⟨(t:ℝ)/(b:ℝ),div_nonneg t.property.1 b.property.1,
            (div_le_one hb).mpr htb.le⟩
          have hbu : (b:ℝ)*(u:ℝ)=(t:ℝ) := by dsimp [u]; field_simp
          have hpu : p u=A w-c := by
            rw [hpe]
            have he : (⟨(b:ℝ)*(u:ℝ),⟨mul_nonneg b.property.1 u.property.1, (mul_le_mul_of_nonneg_left u.property.2 b.property.1).trans (by simpa using b.property.2)⟩⟩ : Interval)=t := Subtype.ext hbu
            rw [he,ht]
          exact ⟨p u,⟨u,rfl⟩,by rw [hpu]⟩
        · rintro ⟨v,⟨u,rfl⟩,he⟩
          have he' : p u=A w-c := F.injective he
          rw [hpe] at he'
          have heA : A (f ⟨(b:ℝ)*(u:ℝ),⟨mul_nonneg b.property.1 u.property.1, (mul_le_mul_of_nonneg_left u.property.2 b.property.1).trans (by simpa using b.property.2)⟩⟩)=A w := sub_left_injective he'
          have htu : (⟨(b:ℝ)*(u:ℝ),⟨mul_nonneg b.property.1 u.property.1, (mul_le_mul_of_nonneg_left u.property.2 b.property.1).trans (by simpa using b.property.2)⟩⟩ : Interval)≤b := by
            change (b:ℝ)*(u:ℝ)≤b
            nlinarith [u.property.2,b.property.1]
          exact ⟨_,A.injOn (hbs _ htu) (hUsource hw) heA⟩
    obtain ⟨b,hb,hb1,hbs,hsgn⟩ := side S A B f hsource haxis hproper
    let N : Plane ≃ₜ Plane := {
      toFun := fun z => Plane.mk (z 0) (-z 1)
      invFun := fun z => Plane.mk (z 0) (-z 1)
      left_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
      right_inv := by intro z; ext i; fin_cases i <;> simp [Plane.mk]
      continuous_toFun := by dsimp [Plane.mk]; fun_prop
      continuous_invFun := by dsimp [Plane.mk]; fun_prop }
    have hN0 : N 0=0 := by ext i; fin_cases i <;> simp [N,Plane.mk]
    have hN1 (z : Plane) : N z 1= -z 1 := rfl
    have hchoose : ∃ A' : OpenPartialHomeomorph S Plane,
        A'.source=A.source ∧ A' (f 0)=0 ∧
        (∀ w∈A'.source, w∈B ↔ A' w 1=0) ∧
        (∀ t : Interval, 0<(t:ℝ) → (t:ℝ)≤b → 0<A' (f t) 1) := by
      rcases hsgn with hpos|hneg
      · exact ⟨A,rfl,hzero,haxis,hpos⟩
      · let A' := A.trans N.toOpenPartialHomeomorph
        have hs : A'.source=A.source := by
          simp [A',OpenPartialHomeomorph.trans_source]
        refine ⟨A',hs,?_,?_,?_⟩
        · change N (A (f 0))=0
          rw [hzero,hN0]
        · intro w hw
          change w∈B ↔ N (A w) 1=0
          rw [hN1,neg_eq_zero]
          exact haxis w (hs ▸ hw)
        · intro t ht0 htb
          change 0<N (A (f t)) 1
          rw [hN1]
          exact neg_pos.mpr (hneg t ht0 htb)
    obtain ⟨A',hAs,hAz,hAx,hAp⟩ := hchoose
    obtain ⟨T,U,hU,h0U,hUs,h1U,hT0,hUA,hUF⟩ := joint S A' B f hf
      (hAs.symm ▸ hsource) hAz hAx b hb hAp
    let E₀ := A'.trans T.toOpenPartialHomeomorph
    have hE₀s : E₀.source=A'.source := by simp [E₀,OpenPartialHomeomorph.trans_source]
    let E := E₀.restr U
    have hEs : E.source=U := by
      rw [show E.source=(E₀.restr U).source from rfl,E₀.restr_source' U hU,hE₀s]
      exact inter_eq_right.mpr hUs
    have hE (w : S) : E w=T (A' w) := rfl
    refine ⟨E,hEs.symm ▸ h0U,?_,?_,?_,?_,?_⟩
    · rw [hE,hAz,hT0]
    · intro w hw
      rw [hAs] at hUs
      exact hUs (hEs ▸ hw)
    · exact hEs.symm ▸ h1U
    · intro w hw
      rw [hE]
      exact hUA w (hEs ▸ hw)
    · intro w hw
      rw [hE]
      exact hUF w (hEs ▸ hw)
  have diskSide (S : Type) [TopologicalSpace S]
      (E : OpenPartialHomeomorph S Plane) (D : Set S)
      (hD : IsClosed D) (hreg : closure (interior D)=D)
      (y : S) (hy : y∈E.source) (hy0 : E y=0) (hyD : y∈D)
      (r : ℝ) (hr : 0<r) (htarget : Plane.openSquare 0 r ⊆ E.target)
      (hfrontier : ∀ w∈E.source, w∈frontier D ↔ E w 1=0)
      (v : Plane) (hv : v∈Plane.openSquare 0 r) (hvpos : 0<v 1)
      (hvout : E.symm v∉D) :
      ∀ w∈E.symm '' Plane.openSquare 0 r, w∈D ↔ E w 1≤0 := by
    classical
    let P : Set Plane := Plane.openSquare 0 r ∩ {z : Plane | 0<z 1}
    let M : Set Plane := Plane.openSquare 0 r ∩ {z : Plane | z 1<0}
    have hconvP : Convex ℝ P := by
      intro x hx z hz a b ha hb hab
      refine ⟨(Plane.convex_openSquare 0 r) hx.1 hz.1 ha hb hab,?_⟩
      change 0<(a • x+b • z) 1
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      have hx1 : 0<x 1 := hx.2
      have hz1 : 0<z 1 := hz.2
      by_cases ha0 : a=0
      · have hb1 : b=1 := by linarith
        simpa [ha0,hb1] using hz1
      · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx1)
          (mul_nonneg hb hz1.le)
    have hconvM : Convex ℝ M := by
      intro x hx z hz a b ha hb hab
      refine ⟨(Plane.convex_openSquare 0 r) hx.1 hz.1 ha hb hab,?_⟩
      change (a • x+b • z) 1<0
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      have hx1 : x 1<0 := hx.2
      have hz1 : z 1<0 := hz.2
      by_cases ha0 : a=0
      · have hb1 : b=1 := by linarith
        simpa [ha0,hb1] using hz1
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (lt_of_le_of_ne ha (Ne.symm ha0)) hx1)
          (mul_nonpos_of_nonneg_of_nonpos hb hz1.le)
    have hPconn : IsPreconnected (E.symm '' P) := hconvP.isPreconnected.image E.symm
      (E.continuousOn_symm.mono (fun z hz => htarget hz.1))
    have hMconn : IsPreconnected (E.symm '' M) := hconvM.isPreconnected.image E.symm
      (E.continuousOn_symm.mono (fun z hz => htarget hz.1))
    have hPavoid : Disjoint (E.symm '' P) (frontier D) := by
      apply disjoint_left.mpr
      rintro w ⟨z,hz,rfl⟩ hw
      have he := (hfrontier _ (E.map_target (htarget hz.1))).mp hw
      rw [E.right_inv (htarget hz.1)] at he
      exact (ne_of_gt hz.2) he
    have hMavoid : Disjoint (E.symm '' M) (frontier D) := by
      apply disjoint_left.mpr
      rintro w ⟨z,hz,rfl⟩ hw
      have he := (hfrontier _ (E.map_target (htarget hz.1))).mp hw
      rw [E.right_inv (htarget hz.1)] at he
      exact (ne_of_lt hz.2) he
    have hPout : E.symm '' P ⊆ interior Dᶜ := by
      rcases connected_cap_side D (E.symm '' P) hPconn hPavoid with hin|hout
      · exact False.elim (hvout (interior_subset (hin ⟨v,⟨hv,hvpos⟩,rfl⟩)))
      · exact hout
    let U : Set S := E.symm '' Plane.openSquare 0 r
    have hU : IsOpen U := E.symm.isOpen_image_of_subset_source (Plane.isOpen_openSquare 0 r) htarget
    have hyU : y∈U := by
      refine ⟨0,(by simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hr),?_⟩
      rw [←hy0,E.left_inv hy]
    have hycl : y∈closure (interior D) := hreg.symm ▸ hyD
    obtain ⟨w,hwU,hwD⟩ := (mem_closure_iff_nhds.mp hycl) U (hU.mem_nhds hyU)
    obtain ⟨z,hz,rfl⟩ := hwU
    have hz0 : z 1≠0 := by
      intro he
      have hwfront := (hfrontier _ (E.map_target (htarget hz))).mpr
        (by rw [E.right_inv (htarget hz)]; exact he)
      exact (disjoint_left.mp disjoint_interior_frontier) hwD hwfront
    have hzneg : z 1<0 := by
      rcases lt_or_gt_of_ne hz0 with hneg|hpos
      · exact hneg
      · exact False.elim ((interior_subset (hPout ⟨z,⟨hz,hpos⟩,rfl⟩)) (interior_subset hwD))
    have hMin : E.symm '' M ⊆ interior D := by
      rcases connected_cap_side D (E.symm '' M) hMconn hMavoid with hin|hout
      · exact hin
      · exact False.elim ((interior_subset (hout ⟨z,⟨hz,hzneg⟩,rfl⟩)) (interior_subset hwD))
    rintro w ⟨z,hz,rfl⟩
    rw [E.right_inv (htarget hz)]
    constructor
    · intro hw
      by_contra h
      exact (interior_subset (hPout ⟨z,⟨hz,not_le.mp h⟩,rfl⟩)) hw
    · intro hn
      rcases lt_or_eq_of_le hn with hneg|he
      · exact interior_subset (hMin ⟨z,⟨hz,hneg⟩,rfl⟩)
      · have hf := (hfrontier _ (E.map_target (htarget hz))).mpr
          (by rw [E.right_inv (htarget hz)]; exact he)
        exact hD.closure_eq ▸ frontier_subset_closure hf
  obtain ⟨hsurf⟩ := hS.2.1
  letI : ClosedSurface S := hsurf
  let C := chartAt Plane x
  let p := C x
  let D : Set S := closedDisk S x R
  let B : Set S := boundary S x R
  let f : C(Interval,S) := ⟨fun t => (a t).val,continuous_subtype_val.comp a.continuous⟩
  have hf : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp hemb
  have hne : f 1≠f 0 := by
    intro he
    have ht := hf.injective he
    have hh := congrArg Subtype.val ht
    norm_num at hh
  obtain ⟨hDc,hDreg,hDi,hDf⟩ := geometry S C p R hR htarget
  obtain ⟨A,h0A,hA0,hAs,h1A,hAt,hAb⟩ := boundaryChart S C p R hR htarget (f 0) (f 1) hend0 hne
  obtain ⟨E,h0E,hE0,hEs,h1E,hEb,hEf⟩ := endpointChart S A B f hf h0A hA0 hAb hproper
  have hEt0 : (0:Plane)∈E.target := hE0 ▸ E.map_source h0E
  obtain ⟨r,hr,_,hrE⟩ := Plane.exists_openSquare_subset E.open_target hEt0 (by norm_num : (0:ℝ)<1)
  let v : Plane := Plane.mk 0 (r/2)
  have hv : v∈Plane.openSquare 0 r := by
    change max |(v-0) 0| |(v-0) 1|<r
    simp [v,Plane.mk,abs_of_pos (half_pos hr),max_eq_right (half_pos hr).le]
    linarith
  have hvpos : 0<v 1 := by change 0<r/2; linarith
  have hvout : E.symm v∉D := by
    intro hmem
    have hvs := E.map_target (hrE hv)
    have hvf : E.symm v∈range f := (hEf _ hvs).mpr (by
      rw [E.right_inv (hrE hv)]
      exact ⟨by simp [v,Plane.mk],hvpos.le⟩)
    obtain ⟨t,ht⟩ := hvf
    have ht0 : t≠0 := by
      intro he
      subst t
      have hh := congrArg (fun w => E w 1) ht
      rw [hE0,E.right_inv (hrE hv)] at hh
      exact (ne_of_gt hvpos) hh.symm
    have ht1 : t≠1 := by intro he; subst t; exact h1E (ht.symm ▸ hvs)
    have hti : t∈Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
    have htD : f t∈D := ht.symm ▸ hmem
    obtain ⟨z,hz,hze⟩ := htD
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlo|heq
    · have ho : f t∈openDisk S x R := ⟨z,Metric.mem_ball.mpr hlo,hze⟩
      exact (a t).property ho
    · have hb : f t∈B := ⟨z,Metric.mem_sphere.mpr heq,hze⟩
      exact hproper t hti hb
  have hfront : ∀ w∈E.source, w∈frontier D ↔ E w 1=0 := by
    intro w hw
    rw [hDf]
    exact hEb w hw
  have h0D : f 0∈D := by
    obtain ⟨z,hz,hze⟩ := hend0
    exact ⟨z,Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le,hze⟩
  have hdisk := diskSide S E D hDc.isClosed hDreg (f 0) h0E hE0 h0D r hr hrE hfront v hv hvpos hvout
  let U : Set S := E.symm '' Plane.openSquare 0 r
  have hU : IsOpen U := E.symm.isOpen_image_of_subset_source (Plane.isOpen_openSquare 0 r) hrE
  have hUs : U⊆E.source := by rintro w ⟨z,hz,rfl⟩; exact E.map_target (hrE hz)
  have h0U : f 0∈U := by
    refine ⟨0,?_,?_⟩
    · simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hr
    · rw [←hE0,E.left_inv h0E]
  let E' := E.restr U
  have hE's : E'.source=U := by rw [E.restr_source' U hU]; exact inter_eq_right.mpr hUs
  let L : Plane ≃ₜ (ℝ × ℝ) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph.trans
      (Homeomorph.prodComm ℝ ℝ)
  let H := E'.trans L.toOpenPartialHomeomorph
  have hHs : H.source=U := by simp [H,OpenPartialHomeomorph.trans_source,hE's]
  have hH (w : S) : H w=(E w 1,E w 0) := rfl
  let V : Set (ℝ × ℝ) := H.target
  let hpU : f 0∈U := h0U
  let h : U ≃ₜ V := (Homeomorph.setCongr hHs.symm).trans H.toHomeomorphSourceTarget
  have hh (w : S) (hw : w∈U) : ((h ⟨w,hw⟩ : V) : ℝ × ℝ)=(E w 1,E w 0) := rfl
  refine ⟨U,V,hpU,h,hU,H.open_target,?_,?_,?_,?_,?_⟩
  · rw [hh]
    change (E (f 0) 1,E (f 0) 0)=(0,0)
    rw [hE0]; rfl
  · exact fun hw => h1E (hUs hw)
  · intro w hw
    rw [hh]
    exact hdisk w hw
  · intro w hw
    rw [hh]
    exact hEb w (hUs hw)
  · intro w hw
    rw [hh]
    have hrange : Subtype.val '' range a=range f := by
      ext z
      constructor
      · rintro ⟨u,⟨t,rfl⟩,rfl⟩; exact ⟨t,rfl⟩
      · rintro ⟨t,rfl⟩; exact ⟨a t,⟨t,rfl⟩,rfl⟩
    rw [hrange]
    exact (hEf w (hUs hw)).trans and_comm
end CurveComplexGenusTwo.SourceTopology.EulerThreeArcs
