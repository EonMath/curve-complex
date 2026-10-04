import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.GlobalArcCollar.AxisFramedStripProducerStatement
import CurveComplexGenusTwo.Dictionary.Circle24.SquarePairCylinderEdgeRanges
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 12000000

theorem circle33_disjoint_actual_downstairs_annulus
    (M : HyperellipticModel E S) (c d : Circle33 M)
    (hd : Disjoint c.val.image d.val.image) :
    ∃ q : C(Circle × Interval, S),
      Topology.IsEmbedding q ∧
      Set.range (fun z : Circle => q (z, 0)) = c.val.image ∧
      Set.range (fun z : Circle => q (z, 1)) = d.val.image ∧
      IsComplementComponent (c.val.image ∪ d.val.image)
        (q '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}) ∧
      Disjoint (Set.range q) (M.cover.branch : Set S) := by
  classical
  -- Construct the connector from metric compactness, not an input arc certificate.
  have closest_connector (C K : Set Plane) (hC : IsCompact C) (hK : IsCompact K)
      (hnC : C.Nonempty) (hnK : K.Nonempty) (hCK : Disjoint C K) :
      ∃ a ∈ C, ∃ b ∈ K, a ≠ b ∧
        Disjoint (openSegment ℝ a b) (C ∪ K) := by
    obtain ⟨p, hp, hmin⟩ := (hC.prod hK).exists_isMinOn (hnC.prod hnK)
      (continuous_fst.dist continuous_snd).continuousOn
    have hab : p.1 ≠ p.2 := hCK.ne_of_mem hp.1 hp.2
    have hpos : 0 < dist p.1 p.2 := dist_pos.mpr hab
    refine ⟨p.1,hp.1,p.2,hp.2,hab,Set.disjoint_left.mpr ?_⟩
    intro x hx hmem
    rw [openSegment_eq_image_lineMap] at hx
    obtain ⟨t,ht,rfl⟩ := hx
    rcases hmem with hc | hk
    · have hm := hmin (a := (AffineMap.lineMap p.1 p.2 t,p.2)) ⟨hc,hp.2⟩
      change dist p.1 p.2 ≤ dist (AffineMap.lineMap p.1 p.2 t) p.2 at hm
      rw [dist_lineMap_right,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ht.2)] at hm
      nlinarith [mul_pos ht.1 hpos]
    · have hm := hmin (a := (p.1,AffineMap.lineMap p.1 p.2 t)) ⟨hp.1,hk⟩
      change dist p.1 p.2 ≤ dist p.1 (AffineMap.lineMap p.1 p.2 t) at hm
      rw [dist_left_lineMap,Real.norm_eq_abs,abs_of_pos ht.1] at hm
      nlinarith [mul_pos (sub_pos.mpr ht.2) hpos]
  have nested_connector (C K : Set Plane) (hC : IsSeparating C)
      (hK : IsSeparating K) (hKC : K ⊆ inside C) (hCK : C ⊆ outside K) :
      ∃ a ∈ C, ∃ b ∈ K, IsArcBetween (segment ℝ a b) a b ∧
        openSegment ℝ a b ⊆ inside C ∩ outside K := by
    have hdisj : Disjoint C K := Set.disjoint_left.mpr fun x hxC hxK =>
      (hKC hxK).1 hxC
    obtain ⟨a,ha,b,hb,hab,havoid⟩ := closest_connector C K
      hC.isJordanCurve.isCompact hK.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty hK.isJordanCurve.nonempty hdisj
    have hcont : Continuous (AffineMap.lineMap a b : ℝ → Plane) := by fun_prop
    have harc : IsArcBetween (segment ℝ a b) a b := by
      refine ⟨AffineMap.lineMap a b,hcont.continuousOn,
        (AffineMap.lineMap_injective ℝ hab).injOn,?_,?_,?_⟩
      · exact (segment_eq_image_lineMap ℝ a b).symm
      · simp
      · simp
    have hconn : IsPreconnected (openSegment ℝ a b) := by
      rw [openSegment_eq_image_lineMap]
      exact isPreconnected_Ioo.image _ hcont.continuousOn
    have hnotC : openSegment ℝ a b ⊆ Cᶜ := fun x hx hc =>
      Set.disjoint_left.mp havoid hx (Or.inl hc)
    have hnotK : openSegment ℝ a b ⊆ Kᶜ := fun x hx hk =>
      Set.disjoint_left.mp havoid hx (Or.inr hk)
    have haClosure : a ∈ closure (openSegment ℝ a b) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ a b)
    have hbClosure : b ∈ closure (openSegment ℝ a b) :=
      segment_subset_closure_openSegment (right_mem_segment ℝ a b)
    have hinside : openSegment ℝ a b ⊆ inside C := by
      have hs : openSegment ℝ a b ⊆ inside C ∪ outside C := by
        rw [inside_union_outside];exact hnotC
      rcases hconn.subset_or_subset hC.isOpen_inside hC.isOpen_outside
        disjoint_inside_outside hs with hi | ho
      · exact hi
      · have he := closure_mono ho hbClosure
        rw [closure_eq_self_union_frontier,hC.frontier_outside] at he
        rcases he with he | he
        · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside (hKC hb) he)
        · exact False.elim ((hKC hb).1 he)
    have houtside : openSegment ℝ a b ⊆ outside K := by
      have hs : openSegment ℝ a b ⊆ inside K ∪ outside K := by
        rw [inside_union_outside];exact hnotK
      rcases hconn.subset_or_subset hK.isOpen_inside hK.isOpen_outside
        disjoint_inside_outside hs with hi | ho
      · have he := closure_mono hi haClosure
        rw [closure_eq_self_union_frontier,hK.frontier_inside] at he
        rcases he with he | he
        · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside he (hCK ha))
        · exact False.elim ((hCK ha).1 he)
      · exact ho
    exact ⟨a,ha,b,hb,harc,fun x hx => ⟨hinside hx,houtside hx⟩⟩
  have nested_proper_connector (C K : Set Plane) (hC : IsSeparating C)
      (hK : IsSeparating K) (hKC : K ⊆ inside C) (hCK : C ⊆ outside K) :
      ∃ a ∈ C, ∃ b ∈ K, IsArcBetween (segment ℝ a b) a b ∧
        segment ℝ a b ∩ C = {a} ∧ segment ℝ a b ∩ K = {b} ∧
        segment ℝ a b \ {a,b} ⊆ inside C ∩ outside K := by
    obtain ⟨a,ha,b,hb,harc,hgap⟩ := nested_connector C K hC hK hKC hCK
    have hsplit (x : Plane) (hx : x ∈ segment ℝ a b) :
        x = a ∨ x = b ∨ x ∈ openSegment ℝ a b := by
      rw [← insert_endpoints_openSegment] at hx
      exact hx
    refine ⟨a,ha,b,hb,harc,?_,?_,?_⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨hx,hxc⟩
        rcases hsplit x hx with rfl | rfl | hx
        · simp
        · exact False.elim ((hKC hb).1 hxc)
        · exact False.elim ((hgap hx).1.1 hxc)
      · intro x hx
        have he : x = a := Set.mem_singleton_iff.mp hx
        rw [he]
        exact ⟨left_mem_segment ℝ a b,ha⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨hx,hxk⟩
        rcases hsplit x hx with rfl | rfl | hx
        · exact False.elim ((hCK ha).1 hxk)
        · simp
        · exact False.elim ((hgap hx).2.1 hxk)
      · intro x hx
        have he : x = b := Set.mem_singleton_iff.mp hx
        rw [he]
        exact ⟨right_mem_segment ℝ a b,hb⟩
    · rintro x ⟨hx,hends⟩
      rcases hsplit x hx with rfl | rfl | hx
      · exact False.elim (hends (by simp))
      · exact False.elim (hends (by simp))
      · exact hgap hx
  have actual_joining_arc : ∃ j : C(Interval,S), Topology.IsEmbedding j ∧
      j 0 ∈ c.val.image ∧ j 1 ∈ d.val.image ∧
      ∀ t : Interval, 0 < (t : ℝ) → (t : ℝ) < 1 →
        j t ∉ c.val.image ∪ d.val.image := by
    let : T2Space S := M.sphere.symm.t2Space
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by rw [M.cover.branch_card];norm_num)
    have havoidw (p : PuncturedCircle M) (z : Circle) : p.curve.map z ≠ w := by
      intro he
      have hz : p.curve.map z ∈ p.curve.image := ⟨z,rfl⟩
      exact Set.disjoint_left.mp p.avoids_branch hz (he.symm ▸ hw)
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
    let chart := stereographic' 2 (M.sphere w)
    have hcsource : chart.source = {M.sphere w}ᶜ := stereographic'_source _
    have hctarget : chart.target = Set.univ := stereographic'_target _
    let es : {z : S // z ≠ w} ≃ₜ chart.source :=
      M.sphere.subtype (fun z => by simp only [hcsource,Set.mem_compl_iff,
        Set.mem_singleton_iff,M.sphere.injective.eq_iff])
    let e : {z : S // z ≠ w} ≃ₜ Plane := es.trans
      (chart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr hctarget).trans
        (Homeomorph.Set.univ _)))
    let Cmap : Circle → Plane := fun z => e ⟨c.val.curve.map z,havoidw c.val z⟩
    let Kmap : Circle → Plane := fun z => e ⟨d.val.curve.map z,havoidw d.val z⟩
    have hCc : Continuous Cmap := e.continuous.comp
      (c.val.curve.embedded.continuous.subtype_mk (havoidw c.val))
    have hKc : Continuous Kmap := e.continuous.comp
      (d.val.curve.embedded.continuous.subtype_mk (havoidw d.val))
    have hdisj : Disjoint (Set.range Cmap) (Set.range Kmap) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨z,rfl⟩ ⟨v,hv⟩
      have he := congrArg Subtype.val (e.injective hv)
      exact Set.disjoint_left.mp hd ⟨z,rfl⟩ ⟨v,he⟩
    obtain ⟨a,ha,b,hb,hab,hinter⟩ := closest_connector
      (Set.range Cmap) (Set.range Kmap) (isCompact_range hCc) (isCompact_range hKc)
      ⟨Cmap 1,1,rfl⟩ ⟨Kmap 1,1,rfl⟩ hdisj
    have hline : Continuous (AffineMap.lineMap a b : ℝ → Plane) := by fun_prop
    let j : C(Interval,S) := ⟨fun t => (e.symm (AffineMap.lineMap a b (t : ℝ))).val,
      continuous_subtype_val.comp (e.symm.continuous.comp
        (hline.comp continuous_subtype_val))⟩
    have hj : Function.Injective j := by
      intro t u he
      have he' := congrArg e (Subtype.ext he)
      apply Subtype.ext
      exact AffineMap.lineMap_injective ℝ hab (by simpa [j] using he')
    refine ⟨j,(j.continuous.isClosedEmbedding hj).isEmbedding,?_,?_,?_⟩
    · obtain ⟨z,hz⟩ := ha
      refine ⟨z,?_⟩
      change c.val.curve.map z = (e.symm (AffineMap.lineMap a b (0:ℝ))).val
      simp only [AffineMap.lineMap_apply_zero]
      rw [← hz]
      exact (congrArg Subtype.val (e.symm_apply_apply ⟨c.val.curve.map z,havoidw c.val z⟩)).symm
    · obtain ⟨z,hz⟩ := hb
      refine ⟨z,?_⟩
      change d.val.curve.map z = (e.symm (AffineMap.lineMap a b (1:ℝ))).val
      simp only [AffineMap.lineMap_apply_one]
      rw [← hz]
      exact (congrArg Subtype.val (e.symm_apply_apply ⟨d.val.curve.map z,havoidw d.val z⟩)).symm
    · intro t ht0 ht1 hmem
      have ht : AffineMap.lineMap a b (t : ℝ) ∈ openSegment ℝ a b :=
        lineMap_mem_openSegment ℝ a b ⟨ht0,ht1⟩
      apply Set.disjoint_left.mp hinter ht
      rcases hmem with ⟨z,hz⟩ | ⟨z,hz⟩
      · left;refine ⟨z,?_⟩
        have he : (⟨c.val.curve.map z,havoidw c.val z⟩ : {z : S // z ≠ w}) =
            e.symm (AffineMap.lineMap a b (t : ℝ)) := Subtype.ext hz
        exact (congrArg e he).trans (e.apply_symm_apply _)
      · right;refine ⟨z,?_⟩
        have he : (⟨d.val.curve.map z,havoidw d.val z⟩ : {z : S // z ≠ w}) =
            e.symm (AffineMap.lineMap a b (t : ℝ)) := Subtype.ext hz
        exact (congrArg e he).trans (e.apply_symm_apply _)
  have endpoint_radial_core (c : Curve S) (f : C(Interval,S))
      (hf : Topology.IsEmbedding f) (hfc : f 0 ∈ c.image)
      (hunique : ∀ t : Interval, f t ∈ c.image → t = 0)
      (E : OpenPartialHomeomorph S Plane) (hE0 : E (f 0) = 0)
      (U : Set S) (hU : IsOpen U) (hpU : f 0 ∈ U) (hUE : U ⊆ E.source) :
      ∃ γ : Option Bool → Interval → Plane,
        ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E '' U),
          R.vector (some true) = -R.vector (some false) ∧
          ∀ x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
            (x ∈ c.image ↔ R.H (E x) ∈
              segment ℝ (0:Plane) (R.vector (some false)) ∪
              segment ℝ (0:Plane) (R.vector (some true))) ∧
            (x ∈ Set.range f ↔ R.H (E x) ∈
              segment ℝ (0:Plane) (R.vector none)) := by
    let : T2Space S := M.sphere.symm.t2Space
    obtain ⟨q,hq⟩ := hfc
    let ψ : ℝ → S := fun t => c.map (q * Circle.exp t)
    have hψ : Continuous ψ := c.embedded.continuous.comp
      (continuous_const.mul Circle.exp.continuous)
    have hψ0 : ψ 0 = f 0 := by simp [ψ,hq]
    obtain ⟨rC,hrC,hballC⟩ := Metric.isOpen_iff.mp (hU.preimage hψ) 0
      (by simpa [hψ0] using hpU)
    let ε := min rC Real.pi / 2
    have hε : 0 < ε := half_pos (lt_min hrC Real.pi_pos)
    have hεr : ε < rC := by dsimp [ε];linarith [min_le_left rC Real.pi]
    have hεπ : ε < Real.pi := by dsimp [ε];linarith [min_le_right rC Real.pi,Real.pi_pos]
    have hSmall (t : ℝ) (ht : t ∈ Icc (-ε) ε) : ψ t ∈ U := by
      apply hballC
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
      constructor <;> linarith [ht.1,ht.2]
    obtain ⟨rF,hrF,hballF⟩ := Metric.isOpen_iff.mp (hU.preimage f.continuous) (0:Interval) hpU
    let r : ℝ := min rF 1 / 2
    have hr : 0 < r := half_pos (lt_min hrF zero_lt_one)
    have hrr : r < rF := by dsimp [r];linarith [min_le_left rF 1]
    have hr1 : r < 1 := by dsimp [r];linarith [min_le_right rF 1]
    let fp : Interval → Interval := fun t => ⟨r*(t:ℝ),
      ⟨mul_nonneg hr.le t.property.1,by nlinarith [t.property.2]⟩⟩
    have hfp : Continuous fp := (continuous_const.mul continuous_subtype_val).subtype_mk _
    have hfpU (t : Interval) : f (fp t) ∈ U := by
      apply hballF
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |r*(t:ℝ)-0| < rF
      rw [sub_zero,abs_of_nonneg (mul_nonneg hr.le t.property.1)]
      nlinarith [t.property.2]
    let θ : Bool → Interval → ℝ := fun b t => if b then ε*(t:ℝ) else -(ε*(t:ℝ))
    have hθ (b : Bool) (t : Interval) : θ b t ∈ Icc (-ε) ε := by
      dsimp [θ];split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2]
    let φ : Option Bool → Interval → S := fun j t =>
      match j with | none => f (fp t) | some b => ψ (θ b t)
    have hφU (j : Option Bool) (t : Interval) : φ j t ∈ U := by
      cases j with
      | none => exact hfpU t
      | some b => exact hSmall _ (hθ b t)
    have hφ0 (j : Option Bool) : φ j 0 = f 0 := by
      cases j <;> simp [φ,fp,θ,hψ0]
    have hφc (j : Option Bool) : Continuous (φ j) := by
      cases j with
      | none => exact f.continuous.comp hfp
      | some b => exact hψ.comp (by dsimp [θ];split_ifs <;> fun_prop)
    have hφi (j : Option Bool) : Function.Injective (φ j) := by
      cases j with
      | none =>
        intro t s he
        have hh := congrArg Subtype.val (hf.injective he)
        apply Subtype.ext
        change r*(t:ℝ)=r*(s:ℝ) at hh
        nlinarith
      | some b =>
        intro t s he
        have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
          (hθ b t) (hθ b s) (mul_left_cancel (c.embedded.injective he))
        apply Subtype.ext
        dsimp [θ] at hang;split_ifs at hang <;> nlinarith
    have hφmeet (i j : Option Bool) (hij : i ≠ j) (t s : Interval)
        (he : φ i t = φ j s) : φ i t = f 0 := by
      cases i with
      | none =>
        cases j with
        | none => exact False.elim (hij rfl)
        | some b =>
          have hu := hunique (fp t) ⟨q * Circle.exp (θ b s),he.symm⟩
          change f (fp t) = f 0
          rw [hu]
      | some b =>
        cases j with
        | none =>
          have hu := hunique (fp s) ⟨q * Circle.exp (θ b t),he⟩
          rw [he];change f (fp s)=f 0;rw [hu]
        | some k =>
          have hbk : b ≠ k := fun h => hij (congrArg some h)
          have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
            (hθ b t) (hθ k s) (mul_left_cancel (c.embedded.injective he))
          have ht0 : (t:ℝ)=0 := by
            cases b <;> cases k
            · exact False.elim (hbk rfl)
            · simp [θ] at hang;nlinarith [s.property.1,t.property.1]
            · simp [θ] at hang;nlinarith [s.property.1,t.property.1]
            · exact False.elim (hbk rfl)
          have ht : t=0 := Subtype.ext ht0
          rw [ht];exact hφ0 (some b)
    let γ : Option Bool → Interval → Plane := fun j t => E (φ j t)
    have hγc (j : Option Bool) : Continuous (γ j) :=
      E.continuousOn.comp_continuous (hφc j) (fun t => hUE (hφU j t))
    have hγi (j : Option Bool) : Function.Injective (γ j) := fun t s he =>
      hφi j (E.injOn (hUE (hφU j t)) (hUE (hφU j s)) he)
    have hγ0 (j : Option Bool) : γ j 0 = 0 := by simp only [γ,hφ0,hE0]
    have hγmeet (i j : Option Bool) (hij : i ≠ j) :
        Set.range (γ i) ∩ Set.range (γ j) = {0} := by
      apply Set.Subset.antisymm
      · rintro x ⟨⟨t,rfl⟩,⟨s,he⟩⟩
        have hs := E.injOn (hUE (hφU j s)) (hUE (hφU i t)) he
        change E (φ i t) = 0
        rw [hφmeet i j hij t s hs.symm,hE0]
      · rintro x rfl;exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
    let angles : Set Circle := (fun t : ℝ => q * Circle.exp t) '' Ioo (-ε) ε
    have hAngles : IsOpen angles :=
      ((isOpenMap_mul_left q).comp Circle.isCoveringMap_exp.isOpenMap) _ isOpen_Ioo
    let badC : Set S := c.map '' anglesᶜ
    let badF : Set S := f '' {t : Interval | r ≤ (t:ℝ)}
    let bad : Set S := badC ∪ badF
    have hBad : IsClosed bad :=
      ((hAngles.isClosed_compl.isCompact.image c.embedded.continuous).isClosed).union
        (((isClosed_le continuous_const continuous_subtype_val).isCompact.image f.continuous).isClosed)
    have hpBad : f 0 ∉ bad := by
      rintro (⟨z,hz,hzp⟩ | ⟨t,ht,he⟩)
      · have hzq : z=q := c.embedded.injective (hzp.trans hq.symm)
        apply hz;exact ⟨0,⟨by linarith,hε⟩,by simpa using hzq.symm⟩
      · have ht0 : t=0 := hf.injective he
        subst t;change r ≤ 0 at ht;linarith
    let W : Set S := U \ bad
    have hW : IsOpen W := hU.sdiff hBad
    have hpW : f 0 ∈ W := ⟨hpU,hpBad⟩
    have hWE : W ⊆ E.source := fun x hx => hUE hx.1
    have hPlaneW : IsOpen (E '' W) := E.isOpen_image_of_subset_source hW hWE
    obtain ⟨R₀,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero γ
      (fun j => (hγc j).isClosedEmbedding (hγi j)) hγ0 hγmeet
      (some false) (some true) (by simp) (E '' W) hPlaneW ⟨f 0,hpW,hE0⟩
    let R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E '' U) :=
      {R₀ with support_subset := R₀.support_subset.trans (Set.image_mono Set.sdiff_subset)}
    have hNotBad (x : S) (hxE : x ∈ E.source)
        (hxN : ‖R.H (E x)‖ ≤ R.coreRadius) : x ∉ bad := by
      intro hxBad
      have hxPlane : E x ∉ E '' W := by
        rintro ⟨y,hy,he⟩
        have hyx := E.injOn (hWE hy) hxE he
        exact hy.2 (hyx.symm ▸ hxBad)
      have hxOut : E x ∉ Metric.ball (0:Plane) R₀.supportRadius := by
        intro hx;exact hxPlane (R₀.support_subset (Metric.ball_subset_closedBall hx))
      have hxFix : R.H (E x)=E x := R₀.fixes_exterior _ hxOut
      rw [hxFix] at hxN
      exact hxPlane (R₀.support_subset (by
        rw [Metric.mem_closedBall,dist_zero_right];exact hxN.trans R₀.core_lt_support.le))
    have hCcover (x : S) (hx : x ∈ c.image) (hxB : x ∉ badC) :
        ∃ b : Bool, ∃ t : Interval, γ (some b) t = E x := by
      obtain ⟨z,hzx⟩ := hx
      have hz : z ∈ angles := by by_contra hn;exact hxB ⟨z,hn,hzx⟩
      obtain ⟨a,ha,haz⟩ := hz
      change q * Circle.exp a = z at haz
      by_cases hapos : 0 ≤ a
      · let t : Interval := ⟨a/ε,⟨div_nonneg hapos hε.le,(div_le_one hε).mpr ha.2.le⟩⟩
        refine ⟨true,t,?_⟩
        have hmul : ε*(t:ℝ)=a := by dsimp [t];field_simp
        change E (c.map (q * Circle.exp (ε*(t:ℝ))))=E x
        rw [hmul,haz,hzx]
      · let t : Interval := ⟨(-a)/ε,⟨div_nonneg (by linarith) hε.le,
          (div_le_one hε).mpr (by linarith [ha.1])⟩⟩
        refine ⟨false,t,?_⟩
        have hmul : -(ε*(t:ℝ))=a := by dsimp [t];field_simp
        change E (c.map (q * Circle.exp (-(ε*(t:ℝ)))))=E x
        rw [hmul,haz,hzx]
    have hFcover (x : S) (hx : x ∈ Set.range f) (hxB : x ∉ badF) :
        ∃ t : Interval, γ none t = E x := by
      obtain ⟨s,hs⟩ := hx
      have hslt : (s:ℝ)<r := by by_contra hn;exact hxB ⟨s,le_of_not_gt hn,hs⟩
      let t : Interval := ⟨(s:ℝ)/r,⟨div_nonneg s.property.1 hr.le,
        (div_le_one hr).mpr hslt.le⟩⟩
      have hfpEq : fp t=s := by apply Subtype.ext;dsimp [fp,t];field_simp
      refine ⟨t,?_⟩
      change E (f (fp t))=E x
      rw [hfpEq,hs]
    have hToRay (j : Option Bool) (x : S) (hxN : ‖R.H (E x)‖ ≤ R.coreRadius)
        (t : Interval) (htx : γ j t=E x) :
        R.H (E x) ∈ segment ℝ (0:Plane) (R.vector j) := by
      have hcut : (t:ℝ) ≤ (R.cut j:ℝ) := by
        by_contra hn
        have htail : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
          ⟨γ j t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
        exact Set.disjoint_left.mp (R.excludes_tails j) htail (by
          rw [htx,Metric.mem_closedBall,dist_zero_right];exact hxN)
      have hh : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) :=
        ⟨γ j t,⟨t,hcut,rfl⟩,rfl⟩
      simpa only [R.prefix_image,zero_add,htx] using hh
    have hFromRay (j : Option Bool) (x : S) (hxE : x ∈ E.source)
        (hx : R.H (E x) ∈ segment ℝ (0:Plane) (R.vector j)) :
        ∃ t : Interval, φ j t=x := by
      have hh : R.H (E x) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) := by
        rw [R.prefix_image,zero_add];exact hx
      obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
      exact ⟨t,E.injOn (hUE (hφU j t)) hxE (R.H.injective he)⟩
    refine ⟨γ,R,hRop,?_⟩
    intro x hxE hxN
    have hxBC : x ∉ badC := fun h => hNotBad x hxE hxN (Or.inl h)
    have hxBF : x ∉ badF := fun h => hNotBad x hxE hxN (Or.inr h)
    constructor
    · constructor
      · intro hx
        obtain ⟨b,t,htx⟩ := hCcover x hx hxBC
        have hray := hToRay (some b) x hxN t htx
        cases b
        · exact Or.inl hray
        · exact Or.inr hray
      · intro hx
        rcases hx with hx | hx
        · obtain ⟨t,ht⟩ := hFromRay (some false) x hxE hx
          exact ⟨q * Circle.exp (θ false t),ht⟩
        · obtain ⟨t,ht⟩ := hFromRay (some true) x hxE hx
          exact ⟨q * Circle.exp (θ true t),ht⟩
    · constructor
      · intro hx
        obtain ⟨t,ht⟩ := hFcover x hx hxBF
        exact hToRay none x hxN t ht
      · intro hx
        obtain ⟨t,ht⟩ := hFromRay none x hxE hx
        exact ⟨fp t,ht⟩
  have radial_three_arm_independent (γ : Option Bool → Interval → Plane)
      (V : Set Plane) (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 V)
      (hop : R.vector (some true) = -R.vector (some false)) :
      LinearIndependent ℝ ![R.vector none,R.vector (some false)] := by
    have positive_ray_contradiction (u v : Plane) (hun : u ≠ 0)
        (hdis : Disjoint (segment ℝ (0:Plane) u \ {0})
          (segment ℝ (0:Plane) v \ {0}))
        (a : ℝ) (ha : 0 < a) (he : a • v = u) : False := by
      let b : ℝ := 1/(a+1)
      have hb : 0 < b := by dsimp [b];positivity
      have hsum : b*(a+1)=1 := div_mul_cancel₀ 1 (by linarith)
      have hb1 : b ≤ 1 := by nlinarith [mul_pos hb ha]
      have hba : 0 ≤ b*a ∧ b*a ≤ 1 := by
        constructor
        · positivity
        · nlinarith
      have hu : b • u ∈ segment ℝ (0:Plane) u := by
        rw [segment_eq_image]
        exact ⟨b,⟨hb.le,hb1⟩,by simp⟩
      have hv : b • u ∈ segment ℝ (0:Plane) v := by
        rw [segment_eq_image]
        refine ⟨b*a,hba,?_⟩
        simp only [smul_zero,zero_add,mul_smul,he]
      have hn : b • u ≠ 0 := smul_ne_zero (ne_of_gt hb) hun
      exact Set.disjoint_left.mp hdis ⟨hu,by simpa using hn⟩ ⟨hv,by simpa using hn⟩
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
    refine ⟨R.vector_nonzero (some false),?_⟩
    intro a he
    rcases lt_trichotomy a 0 with ha | ha | ha
    · have hdis := R.distinct_rays none (some true) (by simp)
      simp only [zero_add] at hdis
      apply positive_ray_contradiction (R.vector none) (R.vector (some true))
        (R.vector_nonzero none) hdis (-a) (by linarith)
      rw [hop,smul_neg,neg_smul,neg_neg]
      exact he
    · subst a
      simp only [zero_smul] at he
      exact R.vector_nonzero none he.symm
    · have hdis := R.distinct_rays none (some false) (by simp)
      simp only [zero_add] at hdis
      exact positive_ray_contradiction (R.vector none) (R.vector (some false))
        (R.vector_nonzero none) hdis a ha he
  have endpoint_axis_chart (a : Curve S) (f : C(Interval,S))
      (hf : Topology.IsEmbedding f) (hfc : f 0 ∈ a.image)
      (hunique : ∀ t : Interval, f t ∈ a.image → t=0)
      (Eraw : OpenPartialHomeomorph S Plane) (hEraw0 : Eraw (f 0)=0)
      (U : Set S) (hU : IsOpen U) (hpU : f 0 ∈ U) (hUE : U ⊆ Eraw.source) :
      ∃ N : OpenPartialHomeomorph S Plane,
        f 0 ∈ N.source ∧ N (f 0)=0 ∧ N.source ⊆ U ∧
        (∀ x, x ∈ N.source → (x ∈ a.image ↔ N x 0=0)) ∧
        (∀ u : Interval, f u ∈ N.source → N (f u) 1=0) := by
    obtain ⟨γstart,Rstart,hRstartOpposite,hRstartTrace⟩ := endpoint_radial_core
      a f hf hfc hunique Eraw hEraw0 U hU hpU hUE
    have hStartIndependent := radial_three_arm_independent γstart (Eraw '' U)
      Rstart hRstartOpposite
    let Estart := Eraw
    have hpEstart : f 0 ∈ Estart.source := hUE hpU
    have hEstart0 : Estart (f 0)=0 := hEraw0
    let Bstart : Module.Basis (Fin 2) ℝ Plane :=
      basisOfLinearIndependentOfCardEqFinrank hStartIndependent (by simp)
    let Astart : Plane ≃L[ℝ] Plane := Bstart.equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
    have hBstart (i : Fin 2) : Bstart i = ![Rstart.vector none,Rstart.vector (some false)] i := by
      exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
        hStartIndependent (by simp)) i
    have hAstartNone : Astart (Rstart.vector none)=Plane.mk 1 0 := by
      have hB0 : Bstart 0=Rstart.vector none := by simpa using hBstart 0
      rw [← hB0]
      ext i
      change Bstart.equivFun (Bstart 0) i = Plane.mk 1 0 i
      rw [Module.Basis.equivFun_self]
      fin_cases i <;> rfl
    have hAstartCircle : Astart (Rstart.vector (some false))=Plane.mk 0 1 := by
      have hB1 : Bstart 1=Rstart.vector (some false) := by simpa using hBstart 1
      rw [← hB1]
      ext i
      change Bstart.equivFun (Bstart 1) i = Plane.mk 0 1 i
      rw [Module.Basis.equivFun_self]
      fin_cases i <;> rfl
    have hCoreCircleAxis (Y : Plane) (hY : ‖Y‖ ≤ Rstart.coreRadius) :
        Y ∈ segment ℝ (0:Plane) (Rstart.vector (some false)) ∪
          segment ℝ (0:Plane) (Rstart.vector (some true)) ↔ (Astart Y) 0=0 := by
      constructor
      · intro hmem
        rcases hmem with hx | hx
        · rw [segment_eq_image] at hx
          obtain ⟨t,ht,rfl⟩ := hx
          simp [map_add,map_smul,hAstartCircle]
        · rw [segment_eq_image] at hx
          obtain ⟨t,ht,rfl⟩ := hx
          simp [map_add,map_smul,hRstartOpposite,hAstartCircle]
      · intro haxis
        let y : ℝ := (Astart Y) 1
        have hYe : Y=y • Rstart.vector (some false) := by
          apply Astart.injective
          rw [map_smul,hAstartCircle]
          ext i
          fin_cases i
          · simpa using haxis
          · simp [y]
        have hn : ‖Y‖=|y| * ‖Rstart.vector (some false)‖ := by
          rw [hYe,norm_smul,Real.norm_eq_abs]
        have hvpos : 0 < ‖Rstart.vector (some false)‖ :=
          norm_pos_iff.mpr (Rstart.vector_nonzero (some false))
        have hyabs : |y| ≤ 1 := by
          by_contra hh
          have hlt := Rstart.core_lt_length (some false)
          rw [hn] at hY
          nlinarith [mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hvpos]
        by_cases hy : 0 ≤ y
        · left
          rw [segment_eq_image]
          exact ⟨y,⟨hy,(le_abs_self y).trans hyabs⟩,by simpa using hYe.symm⟩
        · right
          rw [segment_eq_image]
          refine ⟨-y,⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hy)] using hyabs⟩,?_⟩
          simp only [smul_zero,zero_add,hRstartOpposite,neg_smul,smul_neg,neg_neg]
          exact hYe.symm
    let Gstart : OpenPartialHomeomorph S Plane :=
      (Estart.trans Rstart.H.toOpenPartialHomeomorph).trans
        Astart.toHomeomorph.toOpenPartialHomeomorph
    have hGstartSource : Gstart.source=Estart.source := by
      ext x
      simp only [Gstart,OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
    let Tstart : Set S := Estart.source ∩
      Estart ⁻¹' (Rstart.H ⁻¹' Metric.ball (0:Plane) Rstart.coreRadius)
    have hTstart : IsOpen Tstart := Estart.isOpen_inter_preimage
      (Metric.isOpen_ball.preimage Rstart.H.continuous)
    have hpTstart : f 0 ∈ Tstart := by
      refine ⟨hpEstart,?_⟩
      change Rstart.H (Estart (f 0)) ∈ Metric.ball (0:Plane) Rstart.coreRadius
      rw [hEstart0,Rstart.fixes_center]
      exact Metric.mem_ball_self Rstart.core_pos
    let Nstart := Gstart.restrOpen Tstart hTstart
    have hpNstart : f 0 ∈ Nstart.source := by
      change f 0 ∈ Gstart.source ∩ Tstart
      exact ⟨hGstartSource.symm ▸ hpEstart,hpTstart⟩
    have hNstart0 : Nstart (f 0)=0 := by
      change Astart (Rstart.H (Estart (f 0)))=0
      rw [hEstart0,Rstart.fixes_center,map_zero]
    have hNstartCircle (x : S) (hx : x ∈ Nstart.source) :
        x ∈ a.image ↔ Nstart x 0=0 := by
      have hxT : x ∈ Tstart := hx.2
      have hxN : ‖Rstart.H (Estart x)‖ ≤ Rstart.coreRadius := by
        have hh : Rstart.H (Estart x) ∈ Metric.ball (0:Plane) Rstart.coreRadius := hxT.2
        rw [Metric.mem_ball,dist_zero_right] at hh
        exact hh.le
      exact (hRstartTrace x hxT.1 hxN).1.trans (hCoreCircleAxis _ hxN)
    have hNstartArc (u : Interval) (hu : f u ∈ Nstart.source) :
        Nstart (f u) 1=0 := by
      have huT : f u ∈ Tstart := hu.2
      have huN : ‖Rstart.H (Estart (f u))‖ ≤ Rstart.coreRadius := by
        have hh : Rstart.H (Estart (f u)) ∈ Metric.ball (0:Plane) Rstart.coreRadius := huT.2
        rw [Metric.mem_ball,dist_zero_right] at hh
        exact hh.le
      have hRay := (hRstartTrace (f u) huT.1 huN).2.mp (Set.mem_range_self u)
      rw [segment_eq_image] at hRay
      obtain ⟨t,ht,he⟩ := hRay
      change Astart (Rstart.H (Estart (f u))) 1=0
      rw [← he]
      simp [map_add,map_smul,hAstartNone]
    have hNU : Nstart.source ⊆ U := by
      intro x hx
      have hxT : x ∈ Tstart := hx.2
      have hxN : ‖Rstart.H (Estart x)‖ < Rstart.coreRadius := by
        have hh : Rstart.H (Estart x) ∈ Metric.ball (0:Plane) Rstart.coreRadius := hxT.2
        simpa only [Metric.mem_ball,dist_zero_right] using hh
      have hxBall : Estart x ∈ Metric.ball (0:Plane) Rstart.supportRadius := by
        by_contra hn
        have hfix := Rstart.fixes_exterior (Estart x) hn
        rw [hfix] at hxN
        have hn' : Rstart.supportRadius ≤ ‖Estart x‖ := by
          simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hn
        linarith [Rstart.core_lt_support]
      obtain ⟨y,hy,he⟩ := Rstart.support_subset (Metric.ball_subset_closedBall hxBall)
      have hyx := Estart.injOn (hUE hy) hxT.1 he
      exact hyx ▸ hy
    exact ⟨Nstart,hpNstart,hNstart0,hNU,hNstartCircle,hNstartArc⟩
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨j,hj,hj0,hj1,hjavoid⟩ := actual_joining_arc
  have hstart_unique (t : Interval) (ht : j t ∈ c.val.image) : t=0 := by
    by_cases ht0 : t=0
    · exact ht0
    by_cases ht1 : t=1
    · subst t
      exact False.elim (Set.disjoint_left.mp hd ht hj1)
    have htpos : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (by
      intro he;exact ht0 (Subtype.ext he.symm))
    have htlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by
      intro he;exact ht1 (Subtype.ext he))
    exact False.elim (hjavoid t htpos htlt (Or.inl ht))
  let atlas := M.actualSphereSmoothAtlas
  let : ChartedSpace Plane S := atlas.charts
  let : CompactSpace S := M.sphere.symm.compactSpace
  let Cstart := chartAt Plane (j 0)
  let Estart : OpenPartialHomeomorph S Plane := Cstart.trans
    (Homeomorph.addRight (-Cstart (j 0))).toOpenPartialHomeomorph
  have hEstartSource : Estart.source=Cstart.source := by
    ext x
    simp only [Estart,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
  have hpEstart : j 0 ∈ Estart.source := by
    rw [hEstartSource];exact mem_chart_source Plane (j 0)
  have hEstart0 : Estart (j 0)=0 := by
    change Cstart (j 0) + -Cstart (j 0)=0
    exact add_neg_cancel _
  have hdclosed : IsClosed d.val.image :=
    (isCompact_range d.val.curve.embedded.continuous).isClosed
  obtain ⟨Wstart,hWstart,hpWstart,hWstartClosure⟩ := normal_exists_closure_subset
    (isClosed_singleton : IsClosed ({j 0} : Set S)) hdclosed.isOpen_compl
    (Set.singleton_subset_iff.mpr (fun h => Set.disjoint_left.mp hd hj0 h))
  let Ustart : Set S := Estart.source ∩ Wstart
  have hUstart : IsOpen Ustart := Estart.open_source.inter hWstart
  have hpUstart : j 0 ∈ Ustart :=
    ⟨hpEstart,hpWstart (Set.mem_singleton _)⟩
  obtain ⟨Nstart,hpNstart,hNstart0,hNstartU,hNstartCircle,hNstartArc⟩ :=
    endpoint_axis_chart c.val.curve j hj hj0 hstart_unique Estart hEstart0
      Ustart hUstart hpUstart (fun x hx => hx.1)
  let jrev : C(Interval,S) := ⟨j ∘ unitInterval.symm,
    j.continuous.comp unitInterval.continuous_symm⟩
  have hjrev : Topology.IsEmbedding jrev :=
    hj.comp unitInterval.symmHomeomorph.isEmbedding
  have hjrev0 : jrev 0=j 1 := by simp [jrev]
  have hjrev1 : jrev 1=j 0 := by simp [jrev]
  have hfinish_unique (t : Interval) (ht : jrev t ∈ d.val.image) : t=0 := by
    by_cases ht0 : t=0
    · exact ht0
    by_cases ht1 : t=1
    · subst t
      rw [hjrev1] at ht
      exact False.elim (Set.disjoint_left.mp hd hj0 ht)
    have htpos : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (by
      intro he;exact ht0 (Subtype.ext he.symm))
    have htlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by
      intro he;exact ht1 (Subtype.ext he))
    have hsp : 0 < (unitInterval.symm t:ℝ) := by
      change 0<1-(t:ℝ);linarith
    have hsl : (unitInterval.symm t:ℝ)<1 := by
      change 1-(t:ℝ)<1;linarith
    exact False.elim (hjavoid (unitInterval.symm t) hsp hsl (Or.inr ht))
  let Cfinish := chartAt Plane (jrev 0)
  let Efinish : OpenPartialHomeomorph S Plane := Cfinish.trans
    (Homeomorph.addRight (-Cfinish (jrev 0))).toOpenPartialHomeomorph
  have hEfinishSource : Efinish.source=Cfinish.source := by
    ext x
    simp only [Efinish,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
  have hpEfinish : jrev 0 ∈ Efinish.source := by
    rw [hEfinishSource];exact mem_chart_source Plane (jrev 0)
  have hEfinish0 : Efinish (jrev 0)=0 := by
    change Cfinish (jrev 0) + -Cfinish (jrev 0)=0
    exact add_neg_cancel _
  have hcclosed : IsClosed c.val.image :=
    (isCompact_range c.val.curve.embedded.continuous).isClosed
  let Ufinish : Set S := (Efinish.source ∩ (closure Wstart)ᶜ) ∩ c.val.imageᶜ
  have hUfinish : IsOpen Ufinish :=
    (Efinish.open_source.inter isClosed_closure.isOpen_compl).inter hcclosed.isOpen_compl
  have hpUfinish : jrev 0 ∈ Ufinish := by
    refine ⟨⟨hpEfinish,?_⟩,?_⟩
    · intro hh
      have hdnot := hWstartClosure hh
      rw [hjrev0] at hdnot
      exact hdnot hj1
    · intro hhc
      rw [hjrev0] at hhc
      exact Set.disjoint_left.mp hd hhc hj1
  have hjrev0d : jrev 0 ∈ d.val.image := hjrev0.symm ▸ hj1
  obtain ⟨Nfinish,hpNfinish,hNfinish0,hNfinishU,hNfinishCircle,hNfinishArc⟩ :=
    endpoint_axis_chart d.val.curve jrev hjrev hjrev0d hfinish_unique Efinish hEfinish0
      Ufinish hUfinish hpUfinish (fun x hx => hx.1.1)
  have hNfinishOriginal (u : Interval) (hu : j u ∈ Nfinish.source) :
      Nfinish (j u) 1=0 := by
    have he : jrev (unitInterval.symm u)=j u := by simp [jrev]
    simpa only [he] using hNfinishArc (unitInterval.symm u) (he.symm ▸ hu)
  have hEndpointSourcesDisjoint : Disjoint Nstart.source Nfinish.source := by
    apply Set.disjoint_left.mpr
    intro x hx0 hx1
    have hw : x ∈ Wstart := (hNstartU hx0).2
    exact (hNfinishU hx1).1.2 (subset_closure hw)
  have hrankSphere : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]
    norm_num
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere hrankSphere 0 zero_le_one)
  let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := atlas.manifold
  let : ClosedSurface S := {}
  let θend : Bool → Interval := fun b => if b then 1 else 0
  have hθend : Function.Injective θend := by
    intro b k he
    cases b <;> cases k
    · rfl
    · have hv := congrArg (fun t : Interval => (t:ℝ)) he
      norm_num [θend] at hv
    · have hv := congrArg (fun t : Interval => (t:ℝ)) he
      norm_num [θend] at hv
    · rfl
  let Eend : Bool → OpenPartialHomeomorph S Plane := fun b => if b then Nfinish else Nstart
  have hpEend (b : Bool) : j (θend b) ∈ (Eend b).source := by
    cases b
    · exact hpNstart
    · change j 1 ∈ Nfinish.source
      rw [← hjrev0]
      exact hpNfinish
  have hEend0 (b : Bool) : Eend b (j (θend b))=0 := by
    cases b
    · exact hNstart0
    · change Nfinish (j 1)=0
      rw [← hjrev0]
      exact hNfinish0
  have hEendAxis (b : Bool) (u : Interval) (hu : j u ∈ (Eend b).source) :
      Eend b (j u) 1=0 := by
    cases b
    · exact hNstartArc u hu
    · exact hNfinishOriginal u hu
  obtain ⟨B,hB,hBU,hBcenter,σend,δend,ηend,hσend,hδηend,hBend⟩ :=
    CurveComplex.source_finite_axis_framed_arc_strip S j hj Bool θend hθend
      Eend hpEend hEend0 hEendAxis Set.univ isOpen_univ (Set.subset_univ _)
  have hBstartPort (w : Set.Icc (-1:ℝ) 1) : B (0,w) ∈ c.val.image := by
    obtain ⟨hs,hcoord⟩ := hBend false (0:Interval) w (by
      change |(0:ℝ)-0| < ηend false
      simpa using (hδηend false).2)
    apply (hNstartCircle _ hs).mpr
    have hh := congrArg (fun y : Plane => y 0) hcoord
    change Nstart (B (0,w)) 0 = Nstart (j 0) 0 at hh
    rw [hNstart0] at hh
    exact hh
  have hBfinishPort (w : Set.Icc (-1:ℝ) 1) : B (1,w) ∈ d.val.image := by
    obtain ⟨hs,hcoord⟩ := hBend true (1:Interval) w (by
      change |(1:ℝ)-1| < ηend true
      simpa using (hδηend true).2)
    apply (hNfinishCircle _ hs).mpr
    have hh := congrArg (fun y : Plane => y 0) hcoord
    change Nfinish (B (1,w)) 0 = Nfinish (j 1) 0 at hh
    rw [← hjrev0,hNfinish0] at hh
    exact hh
  let a : ℝ := min (ηend false / 4) (min (ηend true / 4) (1/4))
  have ha : 0 < a := lt_min (by linarith [(hδηend false).2])
    (lt_min (by linarith [(hδηend true).2]) (by norm_num))
  have haquarter : a ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
  have haη0 : a < ηend false := by
    have hh := min_le_left (ηend false / 4) (min (ηend true / 4) (1/4:ℝ))
    dsimp [a];linarith [(hδηend false).2]
  have haη1 : a < ηend true := by
    have hh := (min_le_right (ηend false / 4) (min (ηend true / 4) (1/4:ℝ))).trans
      (min_le_left (ηend true / 4) (1/4:ℝ))
    dsimp [a];linarith [(hδηend true).2]
  let middle : Interval → Interval := fun t => ⟨a+(1-2*a)*(t:ℝ),by
    constructor <;> nlinarith [t.property.1,t.property.2]⟩
  have hMiddleContinuous : Continuous middle :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
  have hMiddleBounds (t : Interval) : 0 < (middle t:ℝ) ∧ (middle t:ℝ)<1 := by
    change 0<a+(1-2*a)*(t:ℝ) ∧ a+(1-2*a)*(t:ℝ)<1
    constructor <;> nlinarith [t.property.1,t.property.2]
  let Bmid : Interval × Set.Icc (-1:ℝ) 1 → S := fun p => B (middle p.1,p.2)
  have hBmid : Continuous Bmid := hB.continuous.comp
    ((hMiddleContinuous.comp continuous_fst).prodMk continuous_snd)
  have hBmidCenter (t : Interval) :
      Bmid (t,⟨0,by norm_num⟩) ∈ (c.val.image ∪ d.val.image)ᶜ := by
    change B (middle t,⟨0,by norm_num⟩) ∉ c.val.image ∪ d.val.image
    rw [hBcenter]
    exact hjavoid (middle t) (hMiddleBounds t).1 (hMiddleBounds t).2
  obtain ⟨ρ,hρ,hNarrowMiddle⟩ := CurveComplex.source_continuous_strip_uniform_width
    Bmid hBmid (c.val.image ∪ d.val.image)ᶜ
      (hcclosed.union hdclosed).isOpen_compl hBmidCenter
  let width : Set.Icc (-1:ℝ) 1 → Set.Icc (-1:ℝ) 1 := fun w => ⟨ρ*(w:ℝ),by
    constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
  have hWidthContinuous : Continuous width :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _
  have hWidthInjective : Function.Injective width := by
    intro w v he
    have hv := congrArg Subtype.val he
    apply Subtype.ext
    change ρ*(w:ℝ)=ρ*(v:ℝ) at hv
    nlinarith [hρ.1]
  let Bsmall : C(Interval × Set.Icc (-1:ℝ) 1,S) :=
    ⟨fun p => B (p.1,width p.2),hB.continuous.comp
      (continuous_fst.prodMk (hWidthContinuous.comp continuous_snd))⟩
  have hBsmall : Topology.IsEmbedding Bsmall :=
    (Bsmall.continuous.isClosedEmbedding (by
      intro p q he
      have hh := hB.injective he
      apply Prod.ext
      · have hfirst := congrArg (fun r : Interval × Set.Icc (-1:ℝ) 1 => r.1) hh
        exact hfirst
      · have hsecond := congrArg (fun r : Interval × Set.Icc (-1:ℝ) 1 => r.2) hh
        exact hWidthInjective hsecond)).isEmbedding
  have hBsmallCenter (u : Interval) : Bsmall (u,⟨0,by norm_num⟩)=j u := by
    change B (u,width ⟨0,by norm_num⟩)=j u
    have hw0 : width ⟨0,by norm_num⟩=⟨0,by norm_num⟩ := by
      apply Subtype.ext;simp [width]
    rw [hw0,hBcenter]
  have hMiddleAvoid (u : Interval) (hu0 : a ≤ (u:ℝ)) (hu1 : (u:ℝ)≤1-a)
      (w : Set.Icc (-1:ℝ) 1) : Bsmall (u,w) ∉ c.val.image ∪ d.val.image := by
    have hden : 0 < 1-2*a := by linarith
    let t : Interval := ⟨((u:ℝ)-a)/(1-2*a),
      ⟨div_nonneg (by linarith) hden.le,(div_le_one hden).mpr (by linarith)⟩⟩
    have hmiddle : middle t=u := by
      apply Subtype.ext
      change a+(1-2*a)*(((u:ℝ)-a)/(1-2*a))=(u:ℝ)
      rw [mul_div_cancel₀ _ (ne_of_gt hden)];ring
    have hh := hNarrowMiddle t w
    change B (middle t,width w) ∉ c.val.image ∪ d.val.image at hh
    rw [hmiddle] at hh
    exact hh
  have hStartFrame (u : Interval) (hu : (u:ℝ)<a) (w : Set.Icc (-1:ℝ) 1) :
      Bsmall (u,w) ∈ Nstart.source ∧
        Nstart (Bsmall (u,w)) 0=Nstart (j u) 0 := by
    have hwindow : |(u:ℝ)-(θend false:ℝ)| < ηend false := by
      change |(u:ℝ)-0| < ηend false
      rw [sub_zero,abs_of_nonneg u.property.1]
      exact hu.trans haη0
    obtain ⟨hs,he⟩ := hBend false u (width w) hwindow
    have hh := congrArg (fun y : Plane => y 0) he
    change Nstart (Bsmall (u,w)) 0=Nstart (j u) 0 at hh
    exact ⟨hs,hh⟩
  have hFinishFrame (u : Interval) (hu : 1-a<(u:ℝ)) (w : Set.Icc (-1:ℝ) 1) :
      Bsmall (u,w) ∈ Nfinish.source ∧
        Nfinish (Bsmall (u,w)) 0=Nfinish (j u) 0 := by
    have hwindow : |(u:ℝ)-(θend true:ℝ)| < ηend true := by
      change |(u:ℝ)-1| < ηend true
      rw [abs_of_nonpos (by linarith [u.property.2])]
      linarith [haη1]
    obtain ⟨hs,he⟩ := hBend true u (width w) hwindow
    have hh := congrArg (fun y : Plane => y 0) he
    change Nfinish (Bsmall (u,w)) 0=Nfinish (j u) 0 at hh
    exact ⟨hs,hh⟩
  have hBsmallC (u : Interval) (w : Set.Icc (-1:ℝ) 1) :
      Bsmall (u,w) ∈ c.val.image ↔ u=0 := by
    constructor
    · intro hc
      by_cases hu : (u:ℝ)<a
      · obtain ⟨hs,he⟩ := hStartFrame u hu w
        have hzero := (hNstartCircle _ hs).mp hc
        have hju : j u ∈ Nstart.source := by
          have hh := (hStartFrame u hu ⟨0,by norm_num⟩).1
          rwa [hBsmallCenter] at hh
        apply hstart_unique u
        exact (hNstartCircle _ hju).mpr (he.symm.trans hzero)
      · by_cases hv : 1-a<(u:ℝ)
        · have hs := (hFinishFrame u hv w).1
          exact False.elim ((hNfinishU hs).2 hc)
        · exact False.elim (hMiddleAvoid u (le_of_not_gt hu) (le_of_not_gt hv) w (Or.inl hc))
    · intro he
      subst u
      exact hBstartPort (width w)
  have hBsmallD (u : Interval) (w : Set.Icc (-1:ℝ) 1) :
      Bsmall (u,w) ∈ d.val.image ↔ u=1 := by
    constructor
    · intro hdmem
      by_cases hu : (u:ℝ)<a
      · have hs := (hStartFrame u hu w).1
        have hw : Bsmall (u,w) ∈ Wstart := (hNstartU hs).2
        exact False.elim (hWstartClosure (subset_closure hw) hdmem)
      · by_cases hv : 1-a<(u:ℝ)
        · obtain ⟨hs,he⟩ := hFinishFrame u hv w
          have hzero := (hNfinishCircle _ hs).mp hdmem
          have hju : j u ∈ Nfinish.source := by
            have hh := (hFinishFrame u hv ⟨0,by norm_num⟩).1
            rwa [hBsmallCenter] at hh
          have hdu : j u ∈ d.val.image :=
            (hNfinishCircle _ hju).mpr (he.symm.trans hzero)
          have hjrevu : jrev (unitInterval.symm u) ∈ d.val.image := by simpa [jrev] using hdu
          have hh := hfinish_unique (unitInterval.symm u) hjrevu
          have hv0 := congrArg (fun t : Interval => (t:ℝ)) hh
          apply Subtype.ext
          change 1-(u:ℝ)=0 at hv0
          change (u:ℝ)=1
          linarith
        · exact False.elim (hMiddleAvoid u (le_of_not_gt hu) (le_of_not_gt hv) w (Or.inr hdmem))
    · intro he
      subst u
      exact hBfinishPort (width w)
  have circle_arc_complement (f : C(Interval,Circle)) (hf : Topology.IsEmbedding f) :
      ∃ g : C(Interval,Circle), Topology.IsEmbedding g ∧ g 0=f 0 ∧ g 1=f 1 ∧
        Set.range f ∪ Set.range g=Set.univ ∧ Set.range f ∩ Set.range g={f 0,f 1} := by
    have hne : f 0 ≠ f 1 := by
      intro he
      have hh := congrArg (fun t : Interval => (t:ℝ)) (hf.injective he)
      norm_num at hh
    let P : C(Interval,Circle) := ⟨Circle.path (f 0) (f 1),(Circle.path _ _).continuous⟩
    let Q : C(Interval,Circle) := ⟨(Circle.path (f 1) (f 0)).symm,
      (Circle.path _ _).symm.continuous⟩
    have hP : Topology.IsEmbedding P := (P.continuous.isClosedEmbedding
      (Circle.path_injective_of_ne hne)).isEmbedding
    have hQ : Topology.IsEmbedding Q := (Q.continuous.isClosedEmbedding
      ((Circle.path_injective_of_ne hne.symm).comp unitInterval.symm_involutive.injective)).isEmbedding
    have hP0 : P 0=f 0 := (Circle.path (f 0) (f 1)).source
    have hP1 : P 1=f 1 := (Circle.path (f 0) (f 1)).target
    have hQ0 : Q 0=f 0 := (Circle.path (f 1) (f 0)).symm.source
    have hQ1 : Q 1=f 1 := (Circle.path (f 1) (f 0)).symm.target
    have hcover : Set.range P ∪ Set.range Q=Set.univ := by
      change Set.range (Circle.path (f 0) (f 1)) ∪
        Set.range (Circle.path (f 1) (f 0)).symm=Set.univ
      rw [Path.symm_range,Circle.range_path_union_range_path hne]
    have hinter : Set.range P ∩ Set.range Q={f 0,f 1} := by
      change Set.range (Circle.path (f 0) (f 1)) ∩
        Set.range (Circle.path (f 1) (f 0)).symm={f 0,f 1}
      rw [Path.symm_range,Circle.range_path_inter_range_path hne]
    have hcl (g : C(Interval,Circle)) :
        closure (g '' Set.Ioo (0:Interval) 1)=Set.range g := by
      rw [g.continuous.isClosedMap.closure_image_eq_of_continuous g.continuous,
        closure_Ioo (by norm_num : (0:Interval) ≠ 1),← unitInterval.univ_eq_Icc,Set.image_univ]
    let U : Set Circle := (Set.range Q)ᶜ
    let V : Set Circle := (Set.range P)ᶜ
    have hU : IsOpen U := (isCompact_range Q.continuous).isClosed.isOpen_compl
    have hV : IsOpen V := (isCompact_range P.continuous).isClosed.isOpen_compl
    have hdisj : Disjoint U V := by
      rw [Set.disjoint_iff_inter_eq_empty,← Set.compl_union,Set.union_comm,hcover,Set.compl_univ]
    have hUV : U ∪ V=({f 0,f 1}:Set Circle)ᶜ := by
      rw [← Set.compl_inter,Set.inter_comm,hinter]
    have hclU : closure U=Set.range P := by
      change closure (Set.range (Circle.path (f 1) (f 0)).symm)ᶜ=
        Set.range (Circle.path (f 0) (f 1))
      rw [Path.symm_range,Circle.compl_range_path hne.symm]
      exact hcl P
    have hclV : closure V=Set.range Q := by
      change closure (Set.range (Circle.path (f 0) (f 1)))ᶜ=
        Set.range (Circle.path (f 1) (f 0)).symm
      rw [Path.symm_range,Circle.compl_range_path hne]
      exact hcl ⟨Circle.path (f 1) (f 0),(Circle.path _ _).continuous⟩
    have hmid : f '' Set.Ioo (0:Interval) 1 ⊆ U ∪ V := by
      rw [hUV]
      rintro x ⟨t,ht,rfl⟩ (he | he)
      · exact (ne_of_gt ht.1) (hf.injective he)
      · exact (ne_of_lt ht.2) (hf.injective he)
    have range_eq_of_subset (g : C(Interval,Circle)) (hg : Topology.IsEmbedding g)
        (hg0 : g 0=f 0) (hg1 : g 1=f 1) (hsub : Set.range f ⊆ Set.range g) :
        Set.range f=Set.range g := by
      let k : C(Interval,Interval) := ⟨fun t => hg.toHomeomorph.symm ⟨f t,hsub (Set.mem_range_self t)⟩,
        hg.toHomeomorph.symm.continuous.comp (f.continuous.subtype_mk _)⟩
      have hklift (t : Interval) : g (k t)=f t :=
        congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply ⟨f t,hsub (Set.mem_range_self t)⟩)
      have hk0 : k 0=0 := hg.injective ((hklift 0).trans hg0.symm)
      have hk1 : k 1=1 := hg.injective ((hklift 1).trans hg1.symm)
      have hkimage : Set.Icc (0:Interval) 1 ⊆ Set.range k :=
        (isPreconnected_range k.continuous).ordConnected.out ⟨0,hk0⟩ ⟨1,hk1⟩
      apply Set.Subset.antisymm hsub
      rintro x ⟨u,rfl⟩
      obtain ⟨v,hv⟩ := hkimage ⟨u.property.1,u.property.2⟩
      exact ⟨v,(hklift v).symm.trans (congrArg g hv)⟩
    rcases (isPreconnected_Ioo.image f f.continuous.continuousOn).subset_or_subset
      hU hV hdisj hmid with hsub | hsub
    · have hfull : Set.range f ⊆ Set.range P := by
        rw [← hcl f,← hclU]
        exact closure_mono hsub
      have heq := range_eq_of_subset P hP hP0 hP1 hfull
      exact ⟨Q,hQ,hQ0,hQ1,by rwa [heq],by rwa [heq]⟩
    · have hfull : Set.range f ⊆ Set.range Q := by
        rw [← hcl f,← hclV]
        exact closure_mono hsub
      have heq := range_eq_of_subset Q hQ hQ0 hQ1 hfull
      refine ⟨P,hP,hP0,hP1,?_,?_⟩
      · rw [heq,Set.union_comm,hcover]
      · rw [heq,Set.inter_comm,hinter]
  have curve_arc_complement (k : Curve S) (f : C(Interval,S))
      (hf : Topology.IsEmbedding f) (hsub : Set.range f ⊆ k.image) :
      ∃ g : C(Interval,S), Topology.IsEmbedding g ∧ g 0=f 0 ∧ g 1=f 1 ∧
        Set.range f ∪ Set.range g=k.image ∧ Set.range f ∩ Set.range g={f 0,f 1} := by
    let F : C(Interval,Circle) := ⟨fun t => k.embedded.toHomeomorph.symm ⟨f t,hsub ⟨t,rfl⟩⟩,
      k.embedded.toHomeomorph.symm.continuous.comp (f.continuous.subtype_mk _)⟩
    have hF (t : Interval) : k.map (F t)=f t :=
      congrArg Subtype.val (k.embedded.toHomeomorph.apply_symm_apply ⟨f t,hsub ⟨t,rfl⟩⟩)
    have hFemb : Topology.IsEmbedding F := (F.continuous.isClosedEmbedding (by
      intro t u he
      apply hf.injective
      exact (hF t).symm.trans ((congrArg k.map he).trans (hF u)))).isEmbedding
    obtain ⟨G,hG,hG0,hG1,hcover,hinter⟩ := circle_arc_complement F hFemb
    let g : C(Interval,S) := ⟨fun t => k.map (G t),k.embedded.continuous.comp G.continuous⟩
    have hfg : Set.range f=k.map '' Set.range F := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨F t,⟨t,rfl⟩,hF t⟩
      · rintro ⟨z,⟨t,rfl⟩,rfl⟩
        exact ⟨t,(hF t).symm⟩
    have hgg : Set.range g=k.map '' Set.range G := by
      exact Set.range_comp k.map G
    refine ⟨g,k.embedded.comp hG,?_,?_,?_,?_⟩
    · exact (congrArg k.map hG0).trans (hF 0)
    · exact (congrArg k.map hG1).trans (hF 1)
    · rw [hfg,hgg,← Set.image_union,hcover,Set.image_univ]
      rfl
    · rw [hfg,hgg,← Set.image_inter k.embedded.injective,hinter]
      simp only [Set.image_insert_eq,Set.image_singleton]
      rw [hF 0,hF 1]
  let transverse : C(Interval,Set.Icc (-1:ℝ) 1) :=
    ⟨fun t => ⟨2*(t:ℝ)-1,by constructor <;> nlinarith [t.property.1,t.property.2]⟩,
      (by fun_prop)⟩
  have htransverse : Topology.IsEmbedding transverse :=
    (transverse.continuous.isClosedEmbedding (by
      intro t u he
      have hh := congrArg Subtype.val he
      apply Subtype.ext
      change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
      linarith)).isEmbedding
  let cport : C(Interval,S) := ⟨fun t => Bsmall (0,transverse t),
    Bsmall.continuous.comp (continuous_const.prodMk transverse.continuous)⟩
  let dport : C(Interval,S) := ⟨fun t => Bsmall (1,transverse t),
    Bsmall.continuous.comp (continuous_const.prodMk transverse.continuous)⟩
  have hcport : Topology.IsEmbedding cport := (cport.continuous.isClosedEmbedding (by
    intro t u he
    apply htransverse.injective
    exact congrArg Prod.snd (hBsmall.injective he))).isEmbedding
  have hdport : Topology.IsEmbedding dport := (dport.continuous.isClosedEmbedding (by
    intro t u he
    apply htransverse.injective
    exact congrArg Prod.snd (hBsmall.injective he))).isEmbedding
  have hcportsub : Set.range cport ⊆ c.val.image := by
    rintro x ⟨t,rfl⟩
    exact (hBsmallC 0 (transverse t)).mpr rfl
  have hdportsub : Set.range dport ⊆ d.val.image := by
    rintro x ⟨t,rfl⟩
    exact (hBsmallD 1 (transverse t)).mpr rfl
  obtain ⟨ccomplement,hccomplement,hccomplement0,hccomplement1,hcpartition,hcportmeet⟩ :=
    curve_arc_complement c.val.curve cport hcport hcportsub
  obtain ⟨dcomplement,hdcomplement,hdcomplement0,hdcomplement1,hdpartition,hdportmeet⟩ :=
    curve_arc_complement d.val.curve dport hdport hdportsub
  have htransverse_surj : Function.Surjective transverse := by
    intro w
    let t : Interval := ⟨((w:ℝ)+1)/2,by constructor <;> nlinarith [w.property.1,w.property.2]⟩
    refine ⟨t,?_⟩
    apply Subtype.ext
    change 2*(((w:ℝ)+1)/2)-1=(w:ℝ)
    ring
  have hccomplementSub : Set.range ccomplement ⊆ c.val.image := by
    intro x hx
    change x ∈ c.val.curve.image
    rw [← hcpartition]
    exact Or.inr hx
  have hdcomplementSub : Set.range dcomplement ⊆ d.val.image := by
    intro x hx
    change x ∈ d.val.curve.image
    rw [← hdpartition]
    exact Or.inr hx
  have hccomplementBand : Set.range ccomplement ∩ Set.range Bsmall={cport 0,cport 1} := by
    ext x
    constructor
    · rintro ⟨hx,⟨⟨u,w⟩,rfl⟩⟩
      have hu := (hBsmallC u w).mp (hccomplementSub hx)
      subst u
      obtain ⟨t,ht⟩ := htransverse_surj w
      have hp : Bsmall (0,w) ∈ Set.range cport := ⟨t,by change Bsmall (0,transverse t)=_; rw [ht]⟩
      rw [← hcportmeet]
      exact ⟨hp,hx⟩
    · intro hx
      rw [← hcportmeet] at hx
      refine ⟨hx.2,?_⟩
      obtain ⟨t,ht⟩ := hx.1
      exact ⟨(0,transverse t),ht⟩
  have hdcomplementBand : Set.range dcomplement ∩ Set.range Bsmall={dport 0,dport 1} := by
    ext x
    constructor
    · rintro ⟨hx,⟨⟨u,w⟩,rfl⟩⟩
      have hu := (hBsmallD u w).mp (hdcomplementSub hx)
      subst u
      obtain ⟨t,ht⟩ := htransverse_surj w
      have hp : Bsmall (1,w) ∈ Set.range dport := ⟨t,by change Bsmall (1,transverse t)=_; rw [ht]⟩
      rw [← hdportmeet]
      exact ⟨hp,hx⟩
    · intro hx
      rw [← hdportmeet] at hx
      refine ⟨hx.2,?_⟩
      obtain ⟨t,ht⟩ := hx.1
      exact ⟨(1,transverse t),ht⟩
  have hcomplementsDisjoint : Disjoint (Set.range ccomplement) (Set.range dcomplement) :=
    hd.mono hccomplementSub hdcomplementSub
  let : ConnectedSpace (Set.Icc (-1:ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc (by norm_num : (-1:ℝ) ≤ 1))
  let Dband : Set S := Bsmall '' (Set.Ioo (0:Interval) 1 ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))
  have hDbandConnected : IsConnected Dband :=
    ((isConnected_Ioo (by norm_num : (0:Interval)<1)).prod isConnected_univ).image _
      Bsmall.continuous.continuousOn
  have hbandClosure (u : Interval) (w : Set.Icc (-1:ℝ) 1) :
      Bsmall (u,w) ∈ closure Dband := by
    let k : Interval → S := fun t => Bsmall (t,w)
    have hk : Continuous k := Bsmall.continuous.comp (continuous_id.prodMk continuous_const)
    have hu : u ∈ closure (Set.Ioo (0:Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
      exact ⟨u.property.1,u.property.2⟩
    have hsub : k '' Set.Ioo (0:Interval) 1 ⊆ Dband := by
      rintro x ⟨t,ht,rfl⟩
      exact ⟨(t,w),⟨ht,Set.mem_univ _⟩,rfl⟩
    exact closure_mono hsub (image_closure_subset_closure_image hk ⟨u,hu,rfl⟩)
  have hbandRangeClosure : Set.range Bsmall ⊆ closure Dband := by
    rintro x ⟨⟨u,w⟩,rfl⟩
    exact hbandClosure u w
  have hDbandAvoidC : Dband ⊆ c.val.imageᶜ := by
    rintro x ⟨⟨u,w⟩,⟨hu,hw⟩,rfl⟩ hc
    exact (ne_of_gt hu.1) ((hBsmallC u w).mp hc)
  have hDbandAvoidD : Dband ⊆ d.val.imageᶜ := by
    rintro x ⟨⟨u,w⟩,⟨hu,hw⟩,rfl⟩ hdmem
    exact (ne_of_lt hu.2) ((hBsmallD u w).mp hdmem)
  have oriented_band_sides (p : Circle33 M) (havoid : Dband ⊆ p.val.imageᶜ) :
      ∃ U V : Set S,
        IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V=p.val.imageᶜ ∧ Dband ⊆ U ∧
        closure U=U ∪ p.val.image ∧ closure V=V ∪ p.val.image := by
    obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
      M.puncturedCircle_closedSides p.val
    have hsub : Dband ⊆ U ∪ V := by rwa [hcover]
    rcases hDbandConnected.isPreconnected.subset_or_subset hUo hVo hUV hsub with hDU | hDV
    · exact ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,hDU,hclU,hclV⟩
    · exact ⟨V,U,hVo,hUo,hVc,hUc,hUV.symm,(Set.union_comm V U).trans hcover,
        hDV,hclV,hclU⟩
  obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcoverc,hDU,hclU,hclV⟩ :=
    oriented_band_sides c hDbandAvoidC
  obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWZ,hcoverd,hDW,hclW,hclZ⟩ :=
    oriented_band_sides d hDbandAvoidD
  have hdU : d.val.image ⊆ U := by
    have hsub : d.val.image ⊆ U ∪ V := by
      rw [hcoverc]
      exact fun x hx hc => Set.disjoint_left.mp hd hc hx
    have hdc : IsPreconnected d.val.image :=
      (isConnected_range d.val.curve.embedded.continuous).isPreconnected
    rcases hdc.subset_or_subset hUo hVo hUV hsub with hdU | hdV
    · exact hdU
    · have hpointD : Bsmall (1,⟨0,by norm_num⟩) ∈ d.val.image := (hBsmallD _ _).mpr rfl
      have hpointCl := closure_mono hDU (hbandClosure 1 ⟨0,by norm_num⟩)
      rw [hclU] at hpointCl
      exact False.elim (hpointCl.elim
        (fun hpU => Set.disjoint_left.mp hUV hpU (hdV hpointD))
        (fun hpC => Set.disjoint_left.mp hd hpC hpointD))
  have hcW : c.val.image ⊆ W := by
    have hsub : c.val.image ⊆ W ∪ Z := by
      rw [hcoverd]
      exact fun x hx hdmem => Set.disjoint_left.mp hd hx hdmem
    have hcc : IsPreconnected c.val.image :=
      (isConnected_range c.val.curve.embedded.continuous).isPreconnected
    rcases hcc.subset_or_subset hWo hZo hWZ hsub with hcW | hcZ
    · exact hcW
    · have hpointC : Bsmall (0,⟨0,by norm_num⟩) ∈ c.val.image := (hBsmallC _ _).mpr rfl
      have hpointCl := closure_mono hDW (hbandClosure 0 ⟨0,by norm_num⟩)
      rw [hclW] at hpointCl
      exact False.elim (hpointCl.elim
        (fun hpW => Set.disjoint_left.mp hWZ hpW (hcZ hpointC))
        (fun hpD => Set.disjoint_left.mp hd hpointC hpD))
  have hVsubW : V ⊆ W := by
    have hVavoid : V ⊆ d.val.imageᶜ :=
      fun x hx hdx => Set.disjoint_left.mp hUV (hdU hdx) hx
    have hsub : V ⊆ W ∪ Z := by rwa [hcoverd]
    rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hsub with hVW | hVZ
    · exact hVW
    · let y := c.val.curve.map 1
      have hyc : y ∈ c.val.image := Set.mem_range_self _
      have hycl : y ∈ closure V := by rw [hclV]; exact Or.inr hyc
      have hyz := closure_mono hVZ hycl
      rw [hclZ] at hyz
      exact False.elim (hyz.elim
        (fun hz => Set.disjoint_left.mp hWZ (hcW hyc) hz)
        (fun hyd => Set.disjoint_left.mp hd hyc hyd))
  have hBandDisjointV : Disjoint (Set.range Bsmall) V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    have hcl := closure_mono hDU (hbandRangeClosure hx)
    rw [hclU] at hcl
    rcases hcl with hxU | hxC
    · exact Set.disjoint_left.mp hUV hxU hxV
    · have hh : x ∈ c.val.imageᶜ := by rw [← hcoverc]; exact Or.inr hxV
      exact hh hxC
  obtain ⟨omitted,homittedV⟩ := hVc.nonempty
  have homittedC : omitted ∉ c.val.image := by
    have hh : omitted ∈ c.val.imageᶜ := by rw [← hcoverc]; exact Or.inr homittedV
    exact hh
  have homittedD : omitted ∉ d.val.image := by
    intro hmem
    exact Set.disjoint_left.mp hUV (hdU hmem) homittedV
  have homittedBand : omitted ∉ Set.range Bsmall :=
    fun hmem => Set.disjoint_left.mp hBandDisjointV hmem homittedV
  let minus : Set.Icc (-1:ℝ) 1 := ⟨-1,by norm_num⟩
  let plus : Set.Icc (-1:ℝ) 1 := ⟨1,by norm_num⟩
  have htransverse0 : transverse 0=minus := Subtype.ext (by norm_num [transverse,minus])
  have htransverse1 : transverse 1=plus := Subtype.ext (by norm_num [transverse,plus])
  have hcmeetBand : Set.range ccomplement ∩ Set.range Bsmall={Bsmall (0,minus),Bsmall (0,plus)} := by
    simpa only [cport,ContinuousMap.coe_mk,htransverse0,htransverse1] using hccomplementBand
  have hdmeetBand : Set.range dcomplement ∩ Set.range Bsmall={Bsmall (1,minus),Bsmall (1,plus)} := by
    simpa only [dport,ContinuousMap.coe_mk,htransverse0,htransverse1] using hdcomplementBand
  have band_side_meet (f : C(Interval,S)) (k : Interval)
      (hmeet : Set.range f ∩ Set.range Bsmall={Bsmall (k,minus),Bsmall (k,plus)})
      (u : Interval) (w : Set.Icc (-1:ℝ) 1) (hx : Bsmall (u,w) ∈ Set.range f) : u=k := by
    have hpoint : Bsmall (u,w) ∈ ({Bsmall (k,minus),Bsmall (k,plus)}:Set S) :=
      hmeet ▸ ⟨hx,Set.mem_range_self _⟩
    rcases hpoint with he | he
    · exact congrArg Prod.fst (hBsmall.injective he)
    · exact congrArg Prod.fst (hBsmall.injective he)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let gapChart := stereographic' 2 (M.sphere omitted)
  have hgapSource : gapChart.source={M.sphere omitted}ᶜ := stereographic'_source _
  have hgapTarget : gapChart.target=Set.univ := stereographic'_target _
  let gapSphere : {x : S // x ≠ omitted} ≃ₜ gapChart.source :=
    M.sphere.subtype (fun x => by simp only [hgapSource,Set.mem_compl_iff,
      Set.mem_singleton_iff,M.sphere.injective.eq_iff])
  let gapPlane : {x : S // x ≠ omitted} ≃ₜ Plane := gapSphere.trans
    (gapChart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr hgapTarget).trans
      (Homeomorph.Set.univ _)))
  let Pband : C(Interval × Set.Icc (-1:ℝ) 1,Plane) :=
    ⟨fun p => gapPlane ⟨Bsmall p,fun he => homittedBand (he ▸ Set.mem_range_self p)⟩,
      gapPlane.continuous.comp (Bsmall.continuous.subtype_mk _)⟩
  have hPband : Topology.IsEmbedding Pband := (Pband.continuous.isClosedEmbedding (by
    intro p q he
    apply hBsmall.injective
    exact congrArg Subtype.val (gapPlane.injective he))).isEmbedding
  let Cedge : C(Interval,Plane) :=
    ⟨fun t => gapPlane ⟨ccomplement t,fun he => homittedC (he ▸ hccomplementSub (Set.mem_range_self t))⟩,
      gapPlane.continuous.comp (ccomplement.continuous.subtype_mk _)⟩
  let Dedge : C(Interval,Plane) :=
    ⟨fun t => gapPlane ⟨dcomplement t,fun he => homittedD (he ▸ hdcomplementSub (Set.mem_range_self t))⟩,
      gapPlane.continuous.comp (dcomplement.continuous.subtype_mk _)⟩
  have hCedge : Topology.IsEmbedding Cedge := (Cedge.continuous.isClosedEmbedding (by
    intro t u he
    apply hccomplement.injective
    exact congrArg Subtype.val (gapPlane.injective he))).isEmbedding
  have hDedge : Topology.IsEmbedding Dedge := (Dedge.continuous.isClosedEmbedding (by
    intro t u he
    apply hdcomplement.injective
    exact congrArg Subtype.val (gapPlane.injective he))).isEmbedding
  let Ledge : C(Interval,Plane) := ⟨fun t => Pband (t,minus),
    Pband.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let Redge : C(Interval,Plane) := ⟨fun t => Pband (t,plus),
    Pband.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hLedge : Topology.IsEmbedding Ledge := (Ledge.continuous.isClosedEmbedding (by
    intro t u he
    exact congrArg Prod.fst (hPband.injective he))).isEmbedding
  have hRedge : Topology.IsEmbedding Redge := (Redge.continuous.isClosedEmbedding (by
    intro t u he
    exact congrArg Prod.fst (hPband.injective he))).isEmbedding
  have hCedge0 : Cedge 0=Ledge 0 := by
    apply congrArg gapPlane
    apply Subtype.ext
    change ccomplement 0=Bsmall (0,minus)
    rw [hccomplement0]
    change Bsmall (0,transverse 0)=_
    rw [htransverse0]
  have hCedge1 : Cedge 1=Redge 0 := by
    apply congrArg gapPlane
    apply Subtype.ext
    change ccomplement 1=Bsmall (0,plus)
    rw [hccomplement1]
    change Bsmall (0,transverse 1)=_
    rw [htransverse1]
  have hDedge0 : Dedge 0=Ledge 1 := by
    apply congrArg gapPlane
    apply Subtype.ext
    change dcomplement 0=Bsmall (1,minus)
    rw [hdcomplement0]
    change Bsmall (1,transverse 0)=_
    rw [htransverse0]
  have hDedge1 : Dedge 1=Redge 1 := by
    apply congrArg gapPlane
    apply Subtype.ext
    change dcomplement 1=Bsmall (1,plus)
    rw [hdcomplement1]
    change Bsmall (1,transverse 1)=_
    rw [htransverse1]
  have hCbandMeet (t u : Interval) (w : Set.Icc (-1:ℝ) 1)
      (he : Cedge t=Pband (u,w)) : u=0 := by
    have hh : ccomplement t=Bsmall (u,w) :=
      congrArg Subtype.val (gapPlane.injective he)
    exact band_side_meet ccomplement 0 hcmeetBand u w ⟨t,hh⟩
  have hDbandMeet (t u : Interval) (w : Set.Icc (-1:ℝ) 1)
      (he : Dedge t=Pband (u,w)) : u=1 := by
    have hh : dcomplement t=Bsmall (u,w) :=
      congrArg Subtype.val (gapPlane.injective he)
    exact band_side_meet dcomplement 1 hdmeetBand u w ⟨t,hh⟩
  have hCDdisjoint : Disjoint (Set.range Cedge) (Set.range Dedge) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh : dcomplement u=ccomplement t :=
      congrArg Subtype.val (gapPlane.injective he)
    exact Set.disjoint_left.mp hcomplementsDisjoint ⟨t,rfl⟩ ⟨u,hh⟩
  have hLRdisjoint : Disjoint (Set.range Ledge) (Set.range Redge) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hPband.injective he)
    change (1:ℝ)=-1 at hh
    norm_num at hh
  have hCRmeet : ∀ x ∈ Set.range Cedge, x ∈ Set.range Redge → x=Cedge 1 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hu := hCbandMeet t u plus he.symm
    exact he.symm.trans ((congrArg Redge hu).trans hCedge1.symm)
  have hCLmeet : ∀ x ∈ Set.range Cedge, x ∈ Set.range Ledge → x=Cedge 0 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hu := hCbandMeet t u minus he.symm
    exact he.symm.trans ((congrArg Ledge hu).trans hCedge0.symm)
  have hDRmeet : ∀ x ∈ Set.range Dedge, x ∈ Set.range Redge → x=Dedge 1 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hu := hDbandMeet t u plus he.symm
    exact he.symm.trans ((congrArg Redge hu).trans hDedge1.symm)
  have hDLmeet : ∀ x ∈ Set.range Dedge, x ∈ Set.range Ledge → x=Dedge 0 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hu := hDbandMeet t u minus he.symm
    exact he.symm.trans ((congrArg Ledge hu).trans hDedge0.symm)
  have interval_isArcBetween (f : C(Interval,Plane)) (hf : Topology.IsEmbedding f) :
      IsArcBetween (Set.range f) (f 0) (f 1) := by
    let F : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
    have hFc : Continuous F := f.continuous.comp continuous_projIcc
    have hval (t : Interval) : F t=f t := by
      simp [F,Set.projIcc_of_mem zero_le_one t.property]
    have hi : InjOn F Interval := by
      intro x hx y hy he
      have hh : f ⟨x,hx⟩=f ⟨y,hy⟩ := by simpa only [← hval] using he
      exact congrArg Subtype.val (hf.injective hh)
    have hr : F '' Interval=Set.range f := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,ht⟩,(hval ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩
        exact ⟨t,t.property,hval t⟩
    exact ⟨F,hFc.continuousOn,hi,hr,hval 0,hval 1⟩
  have hCarc := interval_isArcBetween Cedge hCedge
  have hDarc := interval_isArcBetween Dedge hDedge
  have hLarc := interval_isArcBetween Ledge hLedge
  have hRarc := interval_isArcBetween Redge hRedge
  have hCRarc : IsArcBetween (Set.range Cedge ∪ Set.range Redge) (Cedge 0) (Redge 1) :=
    hCarc.concatenate (by simpa only [hCedge1] using hRarc) hCRmeet
  have hDLarc : IsArcBetween (Set.range Dedge ∪ Set.range Ledge) (Redge 1) (Cedge 0) := by
    have hh := hDarc.reverse.concatenate (by simpa only [hDedge0] using hLarc.reverse) hDLmeet
    simpa only [hDedge1,hCedge0] using hh
  have hJordanBoundary : IsJordanCurve
      ((Set.range Cedge ∪ Set.range Redge) ∪ (Set.range Dedge ∪ Set.range Ledge)) := by
    apply IsJordanCurve.of_two_arcs hCRarc hDLarc
    intro x hx hy
    rcases hx with hxC | hxR <;> rcases hy with hyD | hyL
    · exact False.elim (Set.disjoint_left.mp hCDdisjoint hxC hyD)
    · exact Or.inl (hCLmeet x hxC hyL)
    · exact Or.inr ((hDRmeet x hyD hxR).trans hDedge1)
    · exact False.elim (Set.disjoint_left.mp hLRdisjoint hyL hxR)
  let Jboundary : Set Plane :=
    (Set.range Cedge ∪ Set.range Redge) ∪ (Set.range Dedge ∪ Set.range Ledge)
  have hJboundary : IsJordanCurve Jboundary := hJordanBoundary
  let back : C(Plane,S) := ⟨fun x => (gapPlane.symm x).val,
    continuous_subtype_val.comp gapPlane.symm.continuous⟩
  have hbackEmbedding : Topology.IsOpenEmbedding back := by
    have ho : IsOpen {x : S | x ≠ omitted} := isClosed_singleton.isOpen_compl
    exact ho.isOpenEmbedding_subtypeVal.comp gapPlane.symm.isOpenEmbedding
  have hbackC (t : Interval) : back (Cedge t)=ccomplement t :=
    congrArg Subtype.val (gapPlane.symm_apply_apply _)
  have hbackD (t : Interval) : back (Dedge t)=dcomplement t :=
    congrArg Subtype.val (gapPlane.symm_apply_apply _)
  have hbackBand (p : Interval × Set.Icc (-1:ℝ) 1) : back (Pband p)=Bsmall p :=
    congrArg Subtype.val (gapPlane.symm_apply_apply _)
  let Lsource : C(Interval,S) := ⟨fun t => Bsmall (t,minus),
    Bsmall.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let Rsource : C(Interval,S) := ⟨fun t => Bsmall (t,plus),
    Bsmall.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let Jsource : Set S :=
    (Set.range ccomplement ∪ Set.range Rsource) ∪ (Set.range dcomplement ∪ Set.range Lsource)
  have hbackJ : back '' Jboundary=Jsource := by
    have himage (f : C(Interval,Plane)) (g : C(Interval,S)) (he : ∀ t,back (f t)=g t) :
        back '' Set.range f=Set.range g := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext he)
    rw [Set.image_union,Set.image_union,Set.image_union,
      himage Cedge ccomplement hbackC,himage Dedge dcomplement hbackD,
      himage Redge Rsource (fun t => hbackBand (t,plus)),
      himage Ledge Lsource (fun t => hbackBand (t,minus))]
  let remainingInterior : Set S := back '' Schoenflies.inside Jboundary
  let remainingClosed : Set S := back '' closure (Schoenflies.inside Jboundary)
  have hremainingOpen : IsOpen remainingInterior :=
    hbackEmbedding.isOpenMap _ (Schoenflies.isOpen_inside hJboundary.isClosed)
  have hremainingCompact : IsCompact remainingClosed :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (jordan_curve_theorem hJboundary).isBounded_inside.closure).image back.continuous
  have hremainingClosed : IsClosed remainingClosed := hremainingCompact.isClosed
  have hremainingUnion : remainingClosed=remainingInterior ∪ Jsource := by
    have hcl : closure (Schoenflies.inside Jboundary)=Schoenflies.inside Jboundary ∪ Jboundary :=
      (Schoenflies.IsRegionOf.inside Jboundary).closure_eq (jordan_curve_theorem hJboundary)
    change back '' closure (Schoenflies.inside Jboundary)=_
    rw [hcl,Set.image_union,hbackJ]
  have hremainingInteriorSub : remainingInterior ⊆ remainingClosed := by
    exact Set.image_mono subset_closure
  have hremainingJSub : Jsource ⊆ remainingClosed := by
    rw [hremainingUnion]
    exact Set.subset_union_right
  have homittedRemaining : omitted ∉ remainingClosed := by
    rintro ⟨x,hx,he⟩
    exact (gapPlane.symm x).property he
  have hVoffJ : V ⊆ Jsourceᶜ := by
    intro x hxV hxJ
    rcases hxJ with (hxC | hxR) | (hxD | hxL)
    · have hx : x ∈ c.val.image := hccomplementSub hxC
      have hh : x ∈ c.val.imageᶜ := by rw [← hcoverc];exact Or.inr hxV
      exact hh hx
    · obtain ⟨t,ht⟩ := hxR
      exact Set.disjoint_left.mp hBandDisjointV ⟨(t,plus),ht⟩ hxV
    · exact Set.disjoint_left.mp hUV (hdU (hdcomplementSub hxD)) hxV
    · obtain ⟨t,ht⟩ := hxL
      exact Set.disjoint_left.mp hBandDisjointV ⟨(t,minus),ht⟩ hxV
  have hremainingDisjointV : Disjoint remainingClosed V := by
    have hsub : V ⊆ remainingInterior ∪ remainingClosedᶜ := by
      intro x hxV
      by_cases hxK : x ∈ remainingClosed
      · left
        rw [hremainingUnion] at hxK
        exact hxK.resolve_right (hVoffJ hxV)
      · exact Or.inr hxK
    have hdisj : Disjoint remainingInterior remainingClosedᶜ :=
      Set.disjoint_left.mpr (fun x hxI hxK => hxK (hremainingInteriorSub hxI))
    rcases hVc.isPreconnected.subset_or_subset hremainingOpen hremainingClosed.isOpen_compl
      hdisj hsub with hVI | hVoutside
    · exact False.elim (homittedRemaining (hremainingInteriorSub (hVI homittedV)))
    · exact Set.disjoint_left.mpr (fun x hxK hxV => hVoutside hxV hxK)
  have hbandCoreOffJ (u : Interval) (w : Set.Icc (-1:ℝ) 1)
      (hw0 : -1 < (w:ℝ)) (hw1 : (w:ℝ)<1) : Bsmall (u,w) ∉ Jsource := by
    intro hxJ
    rcases hxJ with (hxC | hxR) | (hxD | hxL)
    · have hpoint : Bsmall (u,w) ∈ ({Bsmall (0,minus),Bsmall (0,plus)}:Set S) :=
        hcmeetBand ▸ ⟨hxC,Set.mem_range_self _⟩
      rcases hpoint with he | he
      · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
        change (w:ℝ)=-1 at hh
        linarith
      · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
        change (w:ℝ)=1 at hh
        linarith
    · obtain ⟨t,ht⟩ := hxR
      have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective ht)
      change (1:ℝ)=(w:ℝ) at hh
      linarith
    · have hpoint : Bsmall (u,w) ∈ ({Bsmall (1,minus),Bsmall (1,plus)}:Set S) :=
        hdmeetBand ▸ ⟨hxD,Set.mem_range_self _⟩
      rcases hpoint with he | he
      · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
        change (w:ℝ)=-1 at hh
        linarith
      · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
        change (w:ℝ)=1 at hh
        linarith
    · obtain ⟨t,ht⟩ := hxL
      have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective ht)
      change (-1:ℝ)=(w:ℝ) at hh
      linarith
  let BandCore : Set S := Bsmall '' ((Set.univ : Set Interval) ×ˢ Set.Ioo minus plus)
  have hWidthCoreConnected : IsConnected (Set.Ioo minus plus) := by
    have himage : Set.projIcc (-1:ℝ) 1 (by norm_num) '' Set.Ioo (-1:ℝ) 1=Set.Ioo minus plus := by
      ext w
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hh := Set.projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1) ⟨hx.1.le,hx.2.le⟩
        change -1 < (Set.projIcc (-1:ℝ) 1 (by norm_num) x:ℝ) ∧
          (Set.projIcc (-1:ℝ) 1 (by norm_num) x:ℝ)<1
        simpa only [hh,Set.mem_Ioo] using hx
      · intro hw
        refine ⟨(w:ℝ),hw,?_⟩
        exact Set.projIcc_of_mem (by norm_num) w.property
    rw [← himage]
    exact (isConnected_Ioo (by norm_num : (-1:ℝ)<1)).image _ continuous_projIcc.continuousOn
  have hBandCoreConnected : IsConnected BandCore :=
    (isConnected_univ.prod hWidthCoreConnected).image _ Bsmall.continuous.continuousOn
  have hBandCoreOffJ : BandCore ⊆ Jsourceᶜ := by
    rintro x ⟨⟨u,w⟩,⟨hu,hw⟩,rfl⟩
    exact hbandCoreOffJ u w hw.1 hw.2
  have hBandCoreOutside : BandCore ⊆ remainingClosedᶜ := by
    have hsub : BandCore ⊆ remainingInterior ∪ remainingClosedᶜ := by
      intro x hxB
      by_cases hxK : x ∈ remainingClosed
      · left
        rw [hremainingUnion] at hxK
        exact hxK.resolve_right (hBandCoreOffJ hxB)
      · exact Or.inr hxK
    have hdisj : Disjoint remainingInterior remainingClosedᶜ :=
      Set.disjoint_left.mpr (fun x hxI hxK => hxK (hremainingInteriorSub hxI))
    rcases hBandCoreConnected.isPreconnected.subset_or_subset hremainingOpen hremainingClosed.isOpen_compl
      hdisj hsub with hBI | hBoutside
    · let wzero : Set.Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
      have hxB : Bsmall (0,wzero) ∈ BandCore := ⟨(0,wzero),⟨Set.mem_univ _,by
        constructor <;> norm_num [minus,plus,wzero]⟩,rfl⟩
      have hxC : Bsmall (0,wzero) ∈ c.val.image := (hBsmallC _ _).mpr rfl
      have hxClV : Bsmall (0,wzero) ∈ closure V := by rw [hclV];exact Or.inr hxC
      have hVnotI : V ⊆ remainingInteriorᶜ :=
        fun x hxV hxI => Set.disjoint_left.mp hremainingDisjointV (hremainingInteriorSub hxI) hxV
      have hclVnotI : closure V ⊆ remainingInteriorᶜ :=
        closure_minimal hVnotI hremainingOpen.isClosed_compl
      exact False.elim (hclVnotI hxClV (hBI hxB))
    · exact hBoutside
  have hRemainingBandSeams : remainingClosed ∩ Set.range Bsmall=
      Set.range Lsource ∪ Set.range Rsource := by
    ext x
    constructor
    · rintro ⟨hxK,⟨⟨u,w⟩,rfl⟩⟩
      by_cases hwminus : w=minus
      · left
        exact ⟨u,by change Bsmall (u,minus)=_;rw [hwminus]⟩
      · by_cases hwplus : w=plus
        · right
          exact ⟨u,by change Bsmall (u,plus)=_;rw [hwplus]⟩
        · have hw0 : minus<w := lt_of_le_of_ne w.property.1 (Ne.symm hwminus)
          have hw1 : w<plus := lt_of_le_of_ne w.property.2 hwplus
          exact False.elim (hBandCoreOutside ⟨(u,w),⟨Set.mem_univ _,⟨hw0,hw1⟩⟩,rfl⟩ hxK)
    · rintro (⟨u,rfl⟩ | ⟨u,rfl⟩)
      · exact ⟨hremainingJSub (Or.inr (Or.inr ⟨u,rfl⟩)),⟨(u,minus),rfl⟩⟩
      · exact ⟨hremainingJSub (Or.inl (Or.inr ⟨u,rfl⟩)),⟨(u,plus),rfl⟩⟩
  obtain ⟨remainingDisk,hremainingDiskBoundary,hremainingDiskInterior⟩ :=
    CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary Jboundary hJboundary
  let actualRemainingDisk : C(Metric.closedBall (0:Plane) 1,S) :=
    ⟨fun x => back (remainingDisk x),back.continuous.comp
      (continuous_subtype_val.comp remainingDisk.continuous)⟩
  have hactualRemainingDisk : Topology.IsEmbedding actualRemainingDisk :=
    hbackEmbedding.isEmbedding.comp (Topology.IsEmbedding.subtypeVal.comp remainingDisk.isEmbedding)
  have hactualRemainingRange : Set.range actualRemainingDisk=remainingClosed := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨remainingDisk z,(remainingDisk z).property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨remainingDisk.symm ⟨z,hz⟩,?_⟩
      change back (remainingDisk (remainingDisk.symm ⟨z,hz⟩))=back z
      rw [remainingDisk.apply_symm_apply]
  have hactualRemainingBandSeams : Set.range actualRemainingDisk ∩ Set.range Bsmall=
      Set.range Lsource ∪ Set.range Rsource := by
    rw [hactualRemainingRange]
    exact hRemainingBandSeams
  have four_edge_loop (C D L R : C(Interval,Plane))
      (hC : Topology.IsEmbedding C) (hD : Topology.IsEmbedding D)
      (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
      (hC0 : C 0=L 0) (hC1 : C 1=R 0) (hD0 : D 0=L 1) (hD1 : D 1=R 1)
      (hCD : Disjoint (Set.range C) (Set.range D))
      (hLR : Disjoint (Set.range L) (Set.range R))
      (hCR : ∀ x ∈ Set.range C,x ∈ Set.range R → x=C 1)
      (hCL : ∀ x ∈ Set.range C,x ∈ Set.range L → x=C 0)
      (hDR : ∀ x ∈ Set.range D,x ∈ Set.range R → x=D 1)
      (hDL : ∀ x ∈ Set.range D,x ∈ Set.range L → x=D 0) :
      ∃ f : ℝ → Plane, IsLoop f ∧
        f '' Interval=((Set.range C ∪ Set.range R) ∪ (Set.range D ∪ Set.range L)) ∧
        ∀ t : Interval, f ((t:ℝ)/4)=C t ∧ f (((t:ℝ)+1)/4)=R t ∧
          f ((3-(t:ℝ))/4)=D t ∧ f (1-(t:ℝ)/4)=L t := by
    have raw_arc (g : C(Interval,Plane)) (hg : Topology.IsEmbedding g) :
        ∃ F : ℝ → Plane, ContinuousOn F Interval ∧ InjOn F Interval ∧
          F '' Interval=Set.range g ∧ ∀ t : Interval,F (t:ℝ)=g t := by
      let F : ℝ → Plane := g ∘ Set.projIcc 0 1 zero_le_one
      have hval (t : Interval) : F (t:ℝ)=g t := by
        simp [F,Set.projIcc_of_mem zero_le_one t.property]
      refine ⟨F,(g.continuous.comp continuous_projIcc).continuousOn,?_,?_,hval⟩
      · intro x hx y hy he
        have hh : g ⟨x,hx⟩=g ⟨y,hy⟩ := by simpa only [← hval] using he
        exact congrArg Subtype.val (hg.injective hh)
      · ext x
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨⟨t,ht⟩,(hval ⟨t,ht⟩).symm⟩
        · rintro ⟨t,rfl⟩
          exact ⟨t,t.property,hval t⟩
    let Dr : C(Interval,Plane) := D.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    let Lr : C(Interval,Plane) := L.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
    have hDr : Topology.IsEmbedding Dr := (Dr.continuous.isClosedEmbedding
      (hD.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
    have hLr : Topology.IsEmbedding Lr := (Lr.continuous.isClosedEmbedding
      (hL.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
    have hDrange : Set.range Dr=Set.range D := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,by simp [Dr,Lr]⟩
    have hLrange : Set.range Lr=Set.range L := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,by simp [Dr,Lr]⟩
    obtain ⟨craw,hcc,hci,hcr,hcv⟩ := raw_arc C hC
    obtain ⟨rraw,hrc,hri,hrr,hrv⟩ := raw_arc R hR
    obtain ⟨draw,hdc,hdi,hdr,hdv⟩ := raw_arc Dr hDr
    obtain ⟨lraw,hlc,hli,hlr,hlv⟩ := raw_arc Lr hLr
    have hc0 : craw 0=C 0 := hcv 0
    have hc1 : craw 1=C 1 := hcv 1
    have hr0 : rraw 0=R 0 := hrv 0
    have hr1 : rraw 1=R 1 := hrv 1
    have hd0 : draw 0=D 1 := by simpa [Dr] using hdv 0
    have hd1 : draw 1=D 0 := by simpa [Dr] using hdv 1
    have hl0 : lraw 0=L 1 := by simpa [Lr] using hlv 0
    have hl1 : lraw 1=L 0 := by simpa [Lr] using hlv 1
    have hcmid : craw 1=rraw 0 := hc1.trans (hC1.trans hr0.symm)
    have hdmid : draw 1=lraw 0 := hd1.trans (hD0.trans hl0.symm)
    have hcmeet : ∀ x ∈ craw '' Interval,x ∈ rraw '' Interval → x=craw 1 := by
      intro x hx hy
      rw [hcr] at hx
      rw [hrr] at hy
      exact (hCR x hx hy).trans hc1.symm
    have hdmeet : ∀ x ∈ draw '' Interval,x ∈ lraw '' Interval → x=draw 1 := by
      intro x hx hy
      rw [hdr,hDrange] at hx
      rw [hlr,hLrange] at hy
      exact (hDL x hx hy).trans hd1.symm
    let F := Schoenflies.concatenate craw rraw
    let G := Schoenflies.concatenate draw lraw
    have hFc : ContinuousOn F Interval := continuousOn_concatenate hcc hrc hcmid
    have hGc : ContinuousOn G Interval := continuousOn_concatenate hdc hlc hdmid
    have hFi : InjOn F Interval := injOn_concatenate hci hri hcmid hcmeet
    have hGi : InjOn G Interval := injOn_concatenate hdi hli hdmid hdmeet
    have hFr : F '' Interval=Set.range C ∪ Set.range R := by
      rw [image_concatenate hcmid,hcr,hrr]
    have hGr : G '' Interval=Set.range D ∪ Set.range L := by
      rw [image_concatenate hdmid,hdr,hlr,hDrange,hLrange]
    have hF0 : F 0=C 0 := (concatenate_zero).trans hc0
    have hF1 : F 1=R 1 := (concatenate_one).trans hr1
    have hG0 : G 0=D 1 := (concatenate_zero).trans hd0
    have hG1 : G 1=L 0 := (concatenate_one).trans hl1
    have hmid : F 1=G 0 := hF1.trans (hD1.symm.trans hG0.symm)
    have hclose : G 1=F 0 := hG1.trans (hC0.symm.trans hF0.symm)
    have hmeet : ∀ x ∈ F '' Interval,x ∈ G '' Interval → x=F 0 ∨ x=F 1 := by
      intro x hx hy
      rw [hFr] at hx
      rw [hGr] at hy
      rcases hx with hxC | hxR <;> rcases hy with hyD | hyL
      · exact False.elim (Set.disjoint_left.mp hCD hxC hyD)
      · exact Or.inl ((hCL x hxC hyL).trans hF0.symm)
      · exact Or.inr ((hDR x hyD hxR).trans (hD1.trans hF1.symm))
      · exact False.elim (Set.disjoint_left.mp hLR hyL hxR)
    let f := Schoenflies.concatenate F G
    refine ⟨f,IsLoop.concatenate hFc hFi hGc hGi hmid hclose hmeet,?_,?_⟩
    · rw [image_concatenate hmid,hFr,hGr]
    · intro t
      refine ⟨?_,?_,?_,?_⟩
      · change Schoenflies.concatenate F G ((t:ℝ)/4)=C t
        rw [concatenate_of_le (by linarith [t.property.2])]
        change Schoenflies.concatenate craw rraw (2*((t:ℝ)/4))=C t
        rw [concatenate_of_le (by linarith [t.property.2])]
        convert hcv t using 1 <;> congr 1 <;> ring
      · change Schoenflies.concatenate F G (((t:ℝ)+1)/4)=R t
        rw [concatenate_of_le (by linarith [t.property.2])]
        change Schoenflies.concatenate craw rraw (2*(((t:ℝ)+1)/4))=R t
        rw [concatenate_upperHalf hcmid ⟨by linarith [t.property.1],by linarith [t.property.2]⟩]
        convert hrv t using 1 <;> congr 1 <;> ring
      · change Schoenflies.concatenate F G ((3-(t:ℝ))/4)=D t
        rw [concatenate_upperHalf hmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
        change Schoenflies.concatenate draw lraw (2*((3-(t:ℝ))/4)-1)=D t
        rw [concatenate_of_le (by linarith [t.property.1])]
        have hh := hdv (unitInterval.symm t)
        simpa only [Dr,ContinuousMap.comp_apply,ContinuousMap.coe_mk,unitInterval.symm_symm] using
          (show draw (2*(2*((3-(t:ℝ))/4)-1))=Dr (unitInterval.symm t) from by
            convert hh using 1 <;> congr 1 <;> change _=1-(t:ℝ) <;> ring)
      · change Schoenflies.concatenate F G (1-(t:ℝ)/4)=L t
        rw [concatenate_upperHalf hmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
        change Schoenflies.concatenate draw lraw (2*(1-(t:ℝ)/4)-1)=L t
        rw [concatenate_upperHalf hdmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
        have hh := hlv (unitInterval.symm t)
        simpa only [Lr,ContinuousMap.comp_apply,ContinuousMap.coe_mk,unitInterval.symm_symm] using
          (show lraw (2*(2*(1-(t:ℝ)/4)-1)-1)=Lr (unitInterval.symm t) from by
            convert hh using 1 <;> congr 1 <;> change _=1-(t:ℝ) <;> ring)
  obtain ⟨actualBoundaryLoop,hactualBoundaryLoop,hactualBoundaryLoopRange,hactualBoundaryQuarter⟩ :=
    four_edge_loop Cedge Dedge Ledge Redge hCedge hDedge hLedge hRedge
      hCedge0 hCedge1 hDedge0 hDedge1 hCDdisjoint hLRdisjoint hCRmeet hCLmeet hDRmeet hDLmeet
  let horizontal (a : ℝ) : C(Interval,Plane) := ⟨fun t => Plane.mk (2*(t:ℝ)-1) a,by fun_prop⟩
  let vertical (a : ℝ) : C(Interval,Plane) := ⟨fun t => Plane.mk a (2*(t:ℝ)-1),by fun_prop⟩
  have hhorizontal (a : ℝ) : Topology.IsEmbedding (horizontal a) :=
    ((horizontal a).continuous.isClosedEmbedding (by
      intro t u he
      have hh := congrArg (fun x : Plane => x 0) he
      apply Subtype.ext
      change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
      linarith)).isEmbedding
  have hvertical (a : ℝ) : Topology.IsEmbedding (vertical a) :=
    ((vertical a).continuous.isClosedEmbedding (by
      intro t u he
      have hh := congrArg (fun x : Plane => x 1) he
      apply Subtype.ext
      change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
      linarith)).isEmbedding
  have hhorizontalRange (a : ℝ) : Set.range (horizontal a)={x : Plane | x 1=a ∧ |x 0| ≤ 1} := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨rfl,?_⟩
      change |2*(t:ℝ)-1| ≤ 1
      rw [abs_le]
      constructor <;> linarith [t.property.1,t.property.2]
    · intro hx
      let t : Interval := ⟨(x 0+1)/2,by
        rcases abs_le.mp hx.2 with ⟨hl,hu⟩
        constructor <;> linarith⟩
      refine ⟨t,?_⟩
      ext i
      fin_cases i
      · change 2*((x 0+1)/2)-1=x 0
        ring
      · exact hx.1.symm
  have hverticalRange (a : ℝ) : Set.range (vertical a)={x : Plane | x 0=a ∧ |x 1| ≤ 1} := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨rfl,?_⟩
      change |2*(t:ℝ)-1| ≤ 1
      rw [abs_le]
      constructor <;> linarith [t.property.1,t.property.2]
    · intro hx
      let t : Interval := ⟨(x 1+1)/2,by
        rcases abs_le.mp hx.2 with ⟨hl,hu⟩
        constructor <;> linarith⟩
      refine ⟨t,?_⟩
      ext i
      fin_cases i
      · exact hx.1.symm
      · change 2*((x 1+1)/2)-1=x 1
        ring
  have hmC0 : horizontal (-1) 0=vertical (-1) 0 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmC1 : horizontal (-1) 1=vertical 1 0 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmD0 : horizontal 1 0=vertical (-1) 1 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmD1 : horizontal 1 1=vertical 1 1 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
  have hmCD : Disjoint (Set.range (horizontal (-1))) (Set.range (horizontal 1)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := congrArg (fun x : Plane => x 1) he
    change (1:ℝ)=-1 at hh
    norm_num at hh
  have hmLR : Disjoint (Set.range (vertical (-1))) (Set.range (vertical 1)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := congrArg (fun x : Plane => x 0) he
    change (1:ℝ)=-1 at hh
    norm_num at hh
  have horizontal_vertical_meet (a b : ℝ) (t u : Interval)
      (he : horizontal a t=vertical b u) : horizontal a t=Plane.mk b a := by
    have hh := congrArg (fun x : Plane => x 0) he
    ext i
    fin_cases i
    · exact hh
    · rfl
  have hmCR : ∀ x ∈ Set.range (horizontal (-1)),x ∈ Set.range (vertical 1) → x=horizontal (-1) 1 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet (-1) 1 t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  have hmCL : ∀ x ∈ Set.range (horizontal (-1)),x ∈ Set.range (vertical (-1)) → x=horizontal (-1) 0 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet (-1) (-1) t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  have hmDR : ∀ x ∈ Set.range (horizontal 1),x ∈ Set.range (vertical 1) → x=horizontal 1 1 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet 1 1 t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  have hmDL : ∀ x ∈ Set.range (horizontal 1),x ∈ Set.range (vertical (-1)) → x=horizontal 1 0 := by
    rintro x ⟨t,rfl⟩ ⟨u,he⟩
    have hh := horizontal_vertical_meet 1 (-1) t u he.symm
    exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
  obtain ⟨modelBoundaryLoop,hmodelBoundaryLoop,hmodelBoundaryLoopRange,hmodelBoundaryQuarter⟩ :=
    four_edge_loop (horizontal (-1)) (horizontal 1) (vertical (-1)) (vertical 1)
      (hhorizontal (-1)) (hhorizontal 1) (hvertical (-1)) (hvertical 1)
      hmC0 hmC1 hmD0 hmD1 hmCD hmLR hmCR hmCL hmDR hmDL
  have hmodelRange : modelBoundaryLoop '' Interval=Schoenflies.modelCurve := by
    rw [hmodelBoundaryLoopRange,hhorizontalRange,hhorizontalRange,hverticalRange,hverticalRange,
      Schoenflies.modelCurve_eq_sides]
    ext x
    simp only [Set.mem_union,Set.mem_setOf_eq,Schoenflies.mem_sideTop,Schoenflies.mem_sideLeft,
      Schoenflies.mem_sideBottom,Schoenflies.mem_sideRight]
    tauto
  obtain ⟨matchedBoundary,hmatchedBoundary⟩ := hmodelBoundaryLoop.exists_homeomorph hactualBoundaryLoop
  let boundaryHomeo : Schoenflies.modelCurve ≃ₜ Jboundary :=
    (Homeomorph.setCongr hmodelRange.symm).trans (matchedBoundary.trans
      (Homeomorph.setCongr hactualBoundaryLoopRange))
  have hboundaryLoop (t : ℝ) (ht : t ∈ Interval) :
      (boundaryHomeo ⟨modelBoundaryLoop t,hmodelRange ▸ Set.mem_image_of_mem _ ht⟩).val=actualBoundaryLoop t :=
    hmatchedBoundary t ht
  obtain ⟨boundaryF,boundaryG,hboundaryFG,hboundaryFvalue⟩ :=
    Schoenflies.exists_isHomeoOn_of_homeomorph boundaryHomeo
  obtain ⟨fillF,fillG,hfillFG,hfillBoundary⟩ :=
    Schoenflies.closed_interior_extension Schoenflies.squareExtension
      Schoenflies.isJordanCurve_modelCurve hJboundary hboundaryFG
  have hfillLoop (t : ℝ) (ht : t ∈ Interval) : fillF (modelBoundaryLoop t)=actualBoundaryLoop t := by
    have hx : modelBoundaryLoop t ∈ Schoenflies.modelCurve := hmodelRange ▸ Set.mem_image_of_mem _ ht
    exact (hfillBoundary hx).trans ((hboundaryFvalue _ hx).trans (hboundaryLoop t ht))
  have hclosedJordan : Jboundary ∪ Schoenflies.inside Jboundary=closure (Schoenflies.inside Jboundary) := by
    exact (Set.union_comm _ _).trans
      ((Schoenflies.IsRegionOf.inside Jboundary).closure_eq (jordan_curve_theorem hJboundary)).symm
  have hfill : Schoenflies.IsHomeoOn fillF fillG (Plane.closedSquare 0 1)
      (closure (Schoenflies.inside Jboundary)) := by
    simpa only [Schoenflies.modelCurve_union_inside,hclosedJordan] using hfillFG
  let fillSquare : Plane.closedSquare 0 1 ≃ₜ closure (Schoenflies.inside Jboundary) := {
    toFun := fun x => ⟨fillF x,hfill.mapsTo x.property⟩
    invFun := fun x => ⟨fillG x,hfill.mapsTo_inv x.property⟩
    left_inv := fun x => Subtype.ext (hfill.invOn.1 x.property)
    right_inv := fun x => Subtype.ext (hfill.invOn.2 x.property)
    continuous_toFun := hfill.continuousOn.domRestrict.subtype_mk _
    continuous_invFun := hfill.continuousOn_inv.domRestrict.subtype_mk _ }
  let RawSquare := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1
  let squarePlane : RawSquare ≃ₜ Plane.closedSquare 0 1 := {
    toFun := fun p => ⟨Plane.mk p.val.1 p.val.2,by
      apply Schoenflies.mem_closedSquare_zero_one.mpr
      exact max_le (abs_le.mpr p.property.1) (abs_le.mpr p.property.2)⟩
    invFun := fun x => ⟨(x.val 0,x.val 1),by
      have hx : max |x.val 0| |x.val 1| ≤ 1 := Schoenflies.mem_closedSquare_zero_one.mp x.property
      exact ⟨abs_le.mp (le_trans (le_max_left _ _) hx),abs_le.mp (le_trans (le_max_right _ _) hx)⟩⟩
    left_inv := by intro p;apply Subtype.ext;rfl
    right_inv := by intro x;apply Subtype.ext;ext i;fin_cases i <;> rfl
    continuous_toFun := by apply Continuous.subtype_mk;fun_prop
    continuous_invFun := by apply Continuous.subtype_mk;fun_prop }
  let : CompactSpace (closure (Schoenflies.inside Jboundary)) :=
    isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (jordan_curve_theorem hJboundary).isBounded_inside.closure)
  let backClosed : closure (Schoenflies.inside Jboundary) → remainingClosed :=
    fun x => ⟨back x,Set.mem_image_of_mem back x.property⟩
  have hbackClosed : Continuous backClosed := (back.continuous.comp continuous_subtype_val).subtype_mk _
  have hbackClosedBij : Function.Bijective backClosed := by
    constructor
    · intro x y he
      have hh : back x=back y := congrArg (fun z : remainingClosed => z.val) he
      exact Subtype.ext (hbackEmbedding.injective hh)
    · rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  let backHomeo : closure (Schoenflies.inside Jboundary) ≃ₜ remainingClosed :=
    Continuous.homeoOfEquivCompactToT2 (f:=Equiv.ofBijective backClosed hbackClosedBij) hbackClosed
  let D₁ : RawSquare ≃ₜ remainingClosed := squarePlane.trans (fillSquare.trans backHomeo)
  have hD₁value (p : RawSquare) : (D₁ p).val=back (fillF (Plane.mk p.val.1 p.val.2)) := rfl
  have hfillC (t : Interval) : fillF (horizontal (-1) t)=Cedge t := by
    have ht : (t:ℝ)/4 ∈ Interval := ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
    have hh := hfillLoop ((t:ℝ)/4) ht
    rw [(hmodelBoundaryQuarter t).1,(hactualBoundaryQuarter t).1] at hh
    exact hh
  have hfillD (t : Interval) : fillF (horizontal 1 t)=Dedge t := by
    have ht : (3-(t:ℝ))/4 ∈ Interval := ⟨by linarith [t.property.2],by linarith [t.property.1]⟩
    have hh := hfillLoop ((3-(t:ℝ))/4) ht
    rw [(hmodelBoundaryQuarter t).2.2.1,(hactualBoundaryQuarter t).2.2.1] at hh
    exact hh
  have hfillL (t : Interval) : fillF (vertical (-1) t)=Ledge t := by
    have ht : 1-(t:ℝ)/4 ∈ Interval := ⟨by linarith [t.property.2],by linarith [t.property.1]⟩
    have hh := hfillLoop (1-(t:ℝ)/4) ht
    rw [(hmodelBoundaryQuarter t).2.2.2,(hactualBoundaryQuarter t).2.2.2] at hh
    exact hh
  have hfillR (t : Interval) : fillF (vertical 1 t)=Redge t := by
    have ht : ((t:ℝ)+1)/4 ∈ Interval := ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
    have hh := hfillLoop (((t:ℝ)+1)/4) ht
    rw [(hmodelBoundaryQuarter t).2.1,(hactualBoundaryQuarter t).2.1] at hh
    exact hh
  have hD₁Left (t : Interval) : (D₁ (squareLeftSeam t)).val=Lsource t := by
    rw [hD₁value]
    change back (fillF (vertical (-1) t))=Lsource t
    rw [hfillL]
    exact hbackBand (t,minus)
  have hD₁Right (t : Interval) : (D₁ (squareRightSeam t)).val=Rsource (unitInterval.symm t) := by
    rw [hD₁value]
    have hh : Plane.mk 1 (1-2*(t:ℝ))=vertical 1 (unitInterval.symm t) := by
      ext i;fin_cases i
      · rfl
      · change 1-2*(t:ℝ)=2*(1-(t:ℝ))-1
        ring
    change back (fillF (Plane.mk 1 (1-2*(t:ℝ))))=Rsource (unitInterval.symm t)
    rw [hh,hfillR]
    exact hbackBand (unitInterval.symm t,plus)
  have hD₁Bottom (t : Interval) : (D₁ (boundaryUnitSquareRaw (t,0))).val=ccomplement t := by
    rw [hD₁value]
    change back (fillF (Plane.mk (2*(t:ℝ)-1) (2*(0:ℝ)-1)))=ccomplement t
    norm_num
    change back (fillF (horizontal (-1) t))=ccomplement t
    rw [hfillC,hbackC]
  have hD₁Top (t : Interval) : (D₁ (boundaryUnitSquareRaw (t,1))).val=dcomplement t := by
    rw [hD₁value]
    change back (fillF (Plane.mk (2*(t:ℝ)-1) (2*(1:ℝ)-1)))=dcomplement t
    norm_num
    change back (fillF (horizontal 1 t))=dcomplement t
    rw [hfillD,hbackD]
  let squareBandParams : RawSquare ≃ₜ (Interval × Set.Icc (-1:ℝ) 1) := {
    toFun := fun p => (⟨(p.val.2+1)/2,by constructor <;> linarith [p.property.2.1,p.property.2.2]⟩,
      ⟨p.val.1,p.property.1⟩)
    invFun := fun p => ⟨(p.2.val,2*p.1.val-1),⟨p.2.property,by
      constructor <;> linarith [p.1.property.1,p.1.property.2]⟩⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · dsimp;ring
    right_inv := by
      intro p
      apply Prod.ext
      · apply Subtype.ext;dsimp;ring
      · apply Subtype.ext;rfl
    continuous_toFun := by apply Continuous.prodMk <;> apply Continuous.subtype_mk <;> fun_prop
    continuous_invFun := by apply Continuous.subtype_mk;fun_prop }
  let D₀ : RawSquare ≃ₜ Set.range Bsmall := squareBandParams.trans hBsmall.toHomeomorph
  have hD₀value (p : RawSquare) : (D₀ p).val=Bsmall (squareBandParams p) := rfl
  have hD₀Left (t : Interval) : (D₀ (squareLeftSeam t)).val=Lsource t := by
    rw [hD₀value]
    apply congrArg Bsmall
    apply Prod.ext
    · apply Subtype.ext;change ((2*(t:ℝ)-1)+1)/2=(t:ℝ);ring
    · apply Subtype.ext;rfl
  have hD₀Right (t : Interval) : (D₀ (squareRightSeam t)).val=Rsource (unitInterval.symm t) := by
    rw [hD₀value]
    apply congrArg Bsmall
    apply Prod.ext
    · apply Subtype.ext;change ((1-2*(t:ℝ))+1)/2=1-(t:ℝ);ring
    · apply Subtype.ext;rfl
  have hD₀Bottom (t : Interval) : (D₀ (boundaryUnitSquareRaw (t,0))).val=cport t := by
    rw [hD₀value]
    apply congrArg Bsmall
    apply Prod.ext
    · apply Subtype.ext;norm_num [squareBandParams,boundaryUnitSquareRaw]
    · apply Subtype.ext;rfl
  have hD₀Top (t : Interval) : (D₀ (boundaryUnitSquareRaw (t,1))).val=dport t := by
    rw [hD₀value]
    apply congrArg Bsmall
    apply Prod.ext
    · apply Subtype.ext;norm_num [squareBandParams,boundaryUnitSquareRaw]
    · apply Subtype.ext;rfl
  let reversedR : Interval → S := fun t => Rsource (unitInterval.symm t)
  have hreversedRange : Set.range reversedR=Set.range Rsource := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨unitInterval.symm t,rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨unitInterval.symm t,by simp [reversedR]⟩
  have hglueIntersection : Set.range Bsmall ∩ remainingClosed=Set.range Lsource ∪ Set.range reversedR := by
    rw [Set.inter_comm,hRemainingBandSeams,hreversedRange]
  obtain ⟨annulusHomeo,hannulusLevels⟩ := square_pair_prescribed_seams_cylinder_edge_ranges
    (Set.range Bsmall) remainingClosed D₀ D₁ Lsource reversedR
      hD₀Left hD₁Left hD₀Right hD₁Right hglueIntersection
  let q : C(Circle × Interval,S) := ⟨fun p => (annulusHomeo p).val,
    continuous_subtype_val.comp annulusHomeo.continuous⟩
  have hq : Topology.IsEmbedding q := Topology.IsEmbedding.subtypeVal.comp annulusHomeo.isEmbedding
  have hq0 : Set.range (fun z : Circle => q (z,0))=c.val.image := by
    change Set.range (fun z : Circle => (annulusHomeo (z,0)).val)=c.val.image
    rw [hannulusLevels 0]
    have hfirst : Set.range (fun t : Interval => (D₀ (boundaryUnitSquareRaw (t,0))).val)=Set.range cport :=
      congrArg Set.range (funext hD₀Bottom)
    have hsecond : Set.range (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,0))).val)=Set.range ccomplement := by
      have he : (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,0))).val)=
          (fun t : Interval => ccomplement (unitInterval.symm t)) := funext (fun t => hD₁Bottom _)
      rw [he]
      ext x
      constructor
      · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,by simp⟩
    rw [hfirst,hsecond]
    exact hcpartition
  have hq1 : Set.range (fun z : Circle => q (z,1))=d.val.image := by
    change Set.range (fun z : Circle => (annulusHomeo (z,1)).val)=d.val.image
    rw [hannulusLevels 1]
    have hfirst : Set.range (fun t : Interval => (D₀ (boundaryUnitSquareRaw (t,1))).val)=Set.range dport :=
      congrArg Set.range (funext hD₀Top)
    have hsecond : Set.range (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,1))).val)=Set.range dcomplement := by
      have he : (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,1))).val)=
          (fun t : Interval => dcomplement (unitInterval.symm t)) := funext (fun t => hD₁Top _)
      rw [he]
      ext x
      constructor
      · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,rfl⟩
      · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,by simp⟩
    rw [hfirst,hsecond]
    exact hdpartition
  have hqRange : Set.range q=Set.range Bsmall ∪ remainingClosed := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact (annulusHomeo p).property
    · intro hx
      refine ⟨annulusHomeo.symm ⟨x,hx⟩,?_⟩
      exact congrArg Subtype.val (annulusHomeo.apply_symm_apply ⟨x,hx⟩)
  let Qmiddle : Set S := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  have hQmiddleConnected : IsConnected Qmiddle := by
    have he : {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}=
        (Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1 := by ext p;simp
    change IsConnected (q '' _)
    rw [he]
    exact (isConnected_univ.prod (isConnected_Ioo (by norm_num : (0:Interval)<1))).image _
      q.continuous.continuousOn
  have hQmiddleAvoid : Qmiddle ⊆ (c.val.image ∪ d.val.image)ᶜ := by
    rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩ (hc | hdmem)
    · obtain ⟨w,hw⟩ := hq0.symm ▸ hc
      have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
      change (0:ℝ)=(t:ℝ) at hh
      linarith
    · obtain ⟨w,hw⟩ := hq1.symm ▸ hdmem
      have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
      change (1:ℝ)=(t:ℝ) at hh
      linarith
  have hQmiddleDiff : Qmiddle=Set.range q \ (c.val.image ∪ d.val.image) := by
    apply Set.Subset.antisymm
    · exact fun x hx => ⟨by obtain ⟨p,hp,he⟩:=hx;exact ⟨p,he⟩,hQmiddleAvoid hx⟩
    · rintro x ⟨⟨⟨z,t⟩,rfl⟩,hx⟩
      have ht0 : (t:ℝ) ≠ 0 := by
        intro he
        have ht : t=0 := Subtype.ext he
        apply hx
        left
        rw [ht,← hq0]
        exact Set.mem_range_self z
      have ht1 : (t:ℝ) ≠ 1 := by
        intro he
        have ht : t=1 := Subtype.ext he
        apply hx
        right
        rw [ht,← hq1]
        exact Set.mem_range_self z
      exact ⟨(z,t),⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
  have hQmiddleOpen : IsOpen Qmiddle := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩
    let k : Plane → S := fun x => q (z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1))
    let O : Set Plane := {x | x 0 ∈ Set.Ioo (-1:ℝ) 1 ∧ x 1 ∈ Set.Ioo (0:ℝ) 1}
    have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hk : Continuous k := q.continuous.comp
      ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
        (continuous_projIcc.comp (by fun_prop)))
    have hki : InjOn k O := by
      intro x hx y hy he
      have hh := hq.injective he
      have h0 : Circle.exp (x 0)=Circle.exp (y 0) := mul_left_cancel (congrArg Prod.fst hh)
      have hlen : (1:ℝ)-(-1)<2*Real.pi := by linarith [Real.pi_gt_three]
      have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩ ⟨hy.1.1.le,hy.1.2.le⟩ h0
      have h1 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
      simp only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,
        Set.projIcc_of_mem zero_le_one ⟨hy.2.1.le,hy.2.2.le⟩] at h1
      ext i
      fin_cases i
      · exact h0'
      · exact h1
    have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
    have hsub : k '' O ⊆ Qmiddle := by
      rintro y ⟨x,hx,rfl⟩
      refine ⟨(z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1)),?_,rfl⟩
      change 0 < (Set.projIcc 0 1 zero_le_one (x 1):ℝ) ∧
        (Set.projIcc 0 1 zero_le_one (x 1):ℝ)<1
      simpa only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,Set.mem_Ioo] using hx.2
    refine ⟨k '' O,hsub,hopen,?_⟩
    refine ⟨Plane.mk 0 (t:ℝ),⟨by norm_num [O],⟨ht0,ht1⟩⟩,?_⟩
    simp [k,Set.projIcc_of_mem zero_le_one t.property]
  have hqRangeClosed : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
  have hQcomponent : IsComplementComponent (c.val.image ∪ d.val.image) Qmiddle := by
    refine ⟨hQmiddleConnected.nonempty,hQmiddleConnected,hQmiddleAvoid,?_⟩
    intro T hT hQT hTavoid
    have hsub : T ⊆ Qmiddle ∪ (Set.range q)ᶜ := by
      intro x hxT
      by_cases hxq : x ∈ Set.range q
      · left
        rw [hQmiddleDiff]
        exact ⟨hxq,hTavoid hxT⟩
      · exact Or.inr hxq
    have hdisj : Disjoint Qmiddle (Set.range q)ᶜ := by
      apply Set.disjoint_left.mpr
      intro x hx hxq
      rw [hQmiddleDiff] at hx
      exact hxq hx.1
    rcases hT.isPreconnected.subset_or_subset hQmiddleOpen hqRangeClosed.isOpen_compl
      hdisj hsub with hTQ | hTout
    · exact Set.Subset.antisymm hTQ hQT
    · obtain ⟨x,hx⟩ := hQmiddleConnected.nonempty
      exact False.elim (Set.disjoint_left.mp hdisj hx (hTout (hQT hx)))
  have hBandDisjointZ : Disjoint (Set.range Bsmall) Z := by
    apply Set.disjoint_left.mpr
    intro x hx hxZ
    have hcl := closure_mono hDW (hbandRangeClosure hx)
    rw [hclW] at hcl
    rcases hcl with hxW | hxD
    · exact Set.disjoint_left.mp hWZ hxW hxZ
    · have hh : x ∈ d.val.imageᶜ := by rw [← hcoverd];exact Or.inr hxZ
      exact hh hxD
  have hZoffJ : Z ⊆ Jsourceᶜ := by
    intro x hxZ hxJ
    rcases hxJ with (hxC | hxR) | (hxD | hxL)
    · exact Set.disjoint_left.mp hWZ (hcW (hccomplementSub hxC)) hxZ
    · obtain ⟨t,ht⟩ := hxR
      exact Set.disjoint_left.mp hBandDisjointZ ⟨(t,plus),ht⟩ hxZ
    · have hh : x ∈ d.val.imageᶜ := by rw [← hcoverd];exact Or.inr hxZ
      exact hh (hdcomplementSub hxD)
    · obtain ⟨t,ht⟩ := hxL
      exact Set.disjoint_left.mp hBandDisjointZ ⟨(t,minus),ht⟩ hxZ
  have hremainingDisjointZ : Disjoint remainingClosed Z := by
    have hsub : Z ⊆ remainingInterior ∪ remainingClosedᶜ := by
      intro x hxZ
      by_cases hxK : x ∈ remainingClosed
      · left
        rw [hremainingUnion] at hxK
        exact hxK.resolve_right (hZoffJ hxZ)
      · exact Or.inr hxK
    have hdisj : Disjoint remainingInterior remainingClosedᶜ :=
      Set.disjoint_left.mpr (fun x hxI hxK => hxK (hremainingInteriorSub hxI))
    rcases hZc.isPreconnected.subset_or_subset hremainingOpen hremainingClosed.isOpen_compl
      hdisj hsub with hZI | hZoutside
    · let wzero : Set.Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
      have hxD : Bsmall (1,wzero) ∈ d.val.image := (hBsmallD _ _).mpr rfl
      have hxClZ : Bsmall (1,wzero) ∈ closure Z := by rw [hclZ];exact Or.inr hxD
      have hclZK : closure Z ⊆ remainingClosed :=
        closure_minimal (fun x hxZ => hremainingInteriorSub (hZI hxZ)) hremainingClosed
      have hxB : Bsmall (1,wzero) ∈ BandCore := ⟨(1,wzero),⟨Set.mem_univ _,by
        constructor <;> norm_num [minus,plus,wzero]⟩,rfl⟩
      exact False.elim (hBandCoreOutside hxB (hclZK hxClZ))
    · exact Set.disjoint_left.mpr (fun x hxK hxZ => hZoutside hxZ hxK)
  have hqDisjointV : Disjoint (Set.range q) V := by
    rw [hqRange]
    exact hBandDisjointV.union_left hremainingDisjointV
  have hqDisjointZ : Disjoint (Set.range q) Z := by
    rw [hqRange]
    exact hBandDisjointZ.union_left hremainingDisjointZ
  have side_count (p : Circle33 M) (T O : Set S) (hTo : IsOpen T) (hOo : IsOpen O)
      (hTc : IsConnected T) (hOc : IsConnected O) (hTO : Disjoint T O)
      (hcover : T ∪ O=p.val.imageᶜ) : (M.cover.branch.filter (· ∈ T)).card=3 := by
    obtain ⟨P,Q,hPo,hQo,hPc,hQc,hPn,hQn,hPQ,hPQcover,hPcount,hQcount⟩ := p.property
    have hTsub : T ⊆ P ∪ Q := by rw [hPQcover,← hcover];exact Set.subset_union_left
    have hPsub : P ⊆ T ∪ O := by rw [hcover,← hPQcover];exact Set.subset_union_left
    have hQsub : Q ⊆ T ∪ O := by rw [hcover,← hPQcover];exact Set.subset_union_right
    have heq : T=P ∨ T=Q := by
      rcases hTc.isPreconnected.subset_or_subset hPo hQo hPQ hTsub with hTP | hTQ
      · left
        apply Set.Subset.antisymm hTP
        rcases hPc.isPreconnected.subset_or_subset hTo hOo hTO hPsub with hPT | hPO
        · exact hPT
        · obtain ⟨x,hx⟩ := hTc.nonempty
          exact False.elim (Set.disjoint_left.mp hTO hx (hPO (hTP hx)))
      · right
        apply Set.Subset.antisymm hTQ
        rcases hQc.isPreconnected.subset_or_subset hTo hOo hTO hQsub with hQT | hQO
        · exact hQT
        · obtain ⟨x,hx⟩ := hTc.nonempty
          exact False.elim (Set.disjoint_left.mp hTO hx (hQO (hTQ hx)))
    rcases heq with h | h
    · simpa only [h] using hPcount
    · simpa only [h] using hQcount
  have hVm := side_count c V U hVo hUo hVc hUc hUV.symm ((Set.union_comm V U).trans hcoverc)
  have hZm := side_count d Z W hZo hWo hZc hWc hWZ.symm ((Set.union_comm Z W).trans hcoverd)
  have hVZ : Disjoint V Z := Set.disjoint_left.mpr
    (fun x hxV hxZ => Set.disjoint_left.mp hWZ (hVsubW hxV) hxZ)
  let BV := M.cover.branch.filter (· ∈ V)
  let BZ := M.cover.branch.filter (· ∈ Z)
  have hBVZ : Disjoint BV BZ := Finset.disjoint_left.mpr (fun x hxV hxZ =>
    Set.disjoint_left.mp hVZ (Finset.mem_filter.mp hxV).2 (Finset.mem_filter.mp hxZ).2)
  have hmarkedSub : BV ∪ BZ ⊆ M.cover.branch := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hmarkedCard : (BV ∪ BZ).card=M.cover.branch.card := by
    rw [Finset.card_union_of_disjoint hBVZ]
    change (M.cover.branch.filter (· ∈ V)).card+(M.cover.branch.filter (· ∈ Z)).card=M.cover.branch.card
    rw [hVm,hZm,M.cover.branch_card]
  have hmarkedExhaust : BV ∪ BZ=M.cover.branch :=
    Finset.eq_of_subset_of_card_le hmarkedSub hmarkedCard.ge
  have hqMarks : Disjoint (Set.range q) (M.cover.branch:Set S) := by
    apply Set.disjoint_left.mpr
    intro x hxq hxmark
    have hx : x ∈ BV ∪ BZ := hmarkedExhaust.symm ▸ hxmark
    rcases Finset.mem_union.mp hx with hxV | hxZ
    · exact Set.disjoint_left.mp hqDisjointV hxq (Finset.mem_filter.mp hxV).2
    · exact Set.disjoint_left.mp hqDisjointZ hxq (Finset.mem_filter.mp hxZ).2
  exact ⟨q,hq,hq0,hq1,hQcomponent,hqMarks⟩

theorem circle33_disjoint_isotopic_full_preimages_actual_annulus
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image)
    (hd : Disjoint c.val.image d.val.image) :
    ∃ f : C(Circle × Interval, E),
      Topology.IsEmbedding f ∧
      Set.range (fun z : Circle => f (z, 0)) = a.val.image ∧
      Set.range (fun z : Circle => f (z, 1)) = b.val.image ∧
      IsComplementComponent (a.val.image ∪ b.val.image)
        (f '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}) ∧
      M.cover.deck '' Set.range f = Set.range f ∧
      (∀ x ∈ Set.range f, M.cover.deck x ≠ x) ∧
      Disjoint (M.cover.projection '' Set.range f) (M.cover.branch : Set S) := by
  classical
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let : T2Space S := M.sphere.symm.t2Space
  -- The sole sphere-annulus existence obligation has an independently approved
  -- exact producer head. It is not an additional hypothesis of this theorem.
  have hdownstairs : ∃ q : C(Circle × Interval,S),
      Topology.IsEmbedding q ∧
      Set.range (fun z : Circle => q (z,0)) = c.val.image ∧
      Set.range (fun z : Circle => q (z,1)) = d.val.image ∧
      IsComplementComponent (c.val.image ∪ d.val.image)
        (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) ∧
      Disjoint (Set.range q) (M.cover.branch : Set S) := by
    exact circle33_disjoint_actual_downstairs_annulus M c d hd
  obtain ⟨q,hq,hqc,hqd,hqcomp,hqmarks⟩ := hdownstairs
  have hpa (z : Circle) : M.cover.projection (a.val.map z) ∈ c.val.image := by
    have hh : a.val.map z ∈ a.val.image := Set.mem_range_self z
    rw [ha] at hh; exact hh
  let β : C(Circle,S) := ⟨fun z => q (z,0),q.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  have hβ : Topology.IsEmbedding β := (β.continuous.isClosedEmbedding
    (fun z w he => congrArg Prod.fst (hq.injective he))).isEmbedding
  let e : Circle ≃ₜ c.val.image := hβ.toHomeomorph.trans (Homeomorph.setCongr hqc)
  let k : Circle → Circle := fun z => e.symm ⟨M.cover.projection (a.val.map z),hpa z⟩
  have hk : Continuous k := e.symm.continuous.comp
    ((M.cover.projection_continuous.comp a.val.embedded.continuous).subtype_mk hpa)
  have hAreg (z : Circle) : a.val.map z ∉ M.cover.ramification := by
    change M.cover.projection (a.val.map z) ∉ (M.cover.branch : Set S)
    exact fun hm => Set.disjoint_left.mp c.val.avoids_branch (hpa z) hm
  let A : C(Circle,M.cover.unramifiedTotal) :=
    ⟨fun z => ⟨a.val.map z,hAreg z⟩,a.val.embedded.continuous.subtype_mk hAreg⟩
  have hQreg (p : Circle × Interval) : q p ∉ (M.cover.branch : Set S) :=
    fun hm => Set.disjoint_left.mp hqmarks (Set.mem_range_self p) hm
  let Q : C(Circle × Interval,M.cover.unramifiedBase) :=
    ⟨fun p => ⟨q p,hQreg p⟩,q.continuous.subtype_mk hQreg⟩
  let H : C(Interval × Circle,M.cover.unramifiedBase) := ⟨fun p => Q (k p.2,p.1),
    Q.continuous.comp ((hk.comp continuous_snd).prodMk continuous_fst)⟩
  let hp := M.cover.unramified_isCoveringMap
  have hzero (z : Circle) : H (0,z) = M.cover.unramifiedProjection (A z) := by
    apply Subtype.ext
    change q (k z,0) = M.cover.projection (a.val.map z)
    exact congrArg Subtype.val (e.apply_symm_apply ⟨M.cover.projection (a.val.map z),hpa z⟩)
  let K := hp.liftHomotopy H A hzero
  let f : C(Circle × Interval,E) := ⟨fun p => (K (p.2,p.1):E),
    continuous_subtype_val.comp (K.continuous.comp (continuous_snd.prodMk continuous_fst))⟩
  have hproj (z : Circle) (t : Interval) : M.cover.projection (f (z,t)) = q (k z,t) := by
    exact congrArg Subtype.val (congrFun (hp.liftHomotopy_lifts H A hzero) (t,z))
  have hfzero (z : Circle) : f (z,0) = a.val.map z := by
    exact congrArg Subtype.val (hp.liftHomotopy_zero H A hzero z)
  have hfinj : Function.Injective f := by
    rintro ⟨z,t⟩ ⟨w,s⟩ he
    have hqs := hq.injective ((hproj z t).symm.trans
      ((congrArg M.cover.projection he).trans (hproj w s)))
    have hts : t = s := congrArg Prod.snd hqs
    subst s
    have hkw : k z = k w := congrArg Prod.fst hqs
    have hpaths : (fun r : Interval => K (r,z)) = (fun r : Interval => K (r,w)) := by
      apply hp.eq_of_comp_eq
        (K.continuous.comp (continuous_id.prodMk continuous_const))
        (K.continuous.comp (continuous_id.prodMk continuous_const))
        (a := t)
      · funext r
        calc
          M.cover.unramifiedProjection (K (r,z)) = H (r,z) :=
            congrFun (hp.liftHomotopy_lifts H A hzero) (r,z)
          _ = H (r,w) := by change Q (k z,r) = Q (k w,r); rw [hkw]
          _ = M.cover.unramifiedProjection (K (r,w)) :=
            (congrFun (hp.liftHomotopy_lifts H A hzero) (r,w)).symm
      · exact Subtype.ext he
    have he0 : f (z,0) = f (w,0) :=
      congrArg (fun h : Interval → M.cover.unramifiedTotal => (h 0:E)) hpaths
    rw [hfzero,hfzero] at he0
    exact Prod.ext (a.val.embedded.injective he0) rfl
  have hf : Topology.IsEmbedding f := (f.continuous.isClosedEmbedding hfinj).isEmbedding
  -- Equivariance is derived by uniqueness of actual lifted paths, not supplied.
  have deck_lift (z w : Circle) (hw : a.val.map w = M.cover.deck (a.val.map z)) :
      ∀ t, f (w,t) = M.cover.deck (f (z,t)) := by
    have hkw : k w = k z := by
      apply congrArg e.symm
      apply Subtype.ext
      change M.cover.projection (a.val.map w) = M.cover.projection (a.val.map z)
      rw [hw,M.cover.projection_deck]
    have hZreg (r : Interval) : M.cover.deck (f (z,r)) ∉ M.cover.ramification := by
      change M.cover.projection (M.cover.deck (f (z,r))) ∉ (M.cover.branch : Set S)
      rw [M.cover.projection_deck]
      exact (K (r,z)).property
    let Z : Interval → M.cover.unramifiedTotal := fun r =>
      ⟨M.cover.deck (f (z,r)),hZreg r⟩
    have hZ : Continuous Z :=
      (M.cover.deck.continuous.comp (f.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk hZreg
    have he : (fun r : Interval => K (r,w)) = Z := by
      apply hp.eq_of_comp_eq
        (K.continuous.comp (continuous_id.prodMk continuous_const)) hZ
        (a := 0)
      · funext r
        apply Subtype.ext
        change M.cover.projection (f (w,r)) = M.cover.projection (M.cover.deck (f (z,r)))
        rw [M.cover.projection_deck,hproj,hproj,hkw]
      · apply Subtype.ext
        change f (w,0) = M.cover.deck (f (z,0))
        rw [hfzero,hfzero]; exact hw
    intro t
    exact congrArg (fun h : Interval → M.cover.unramifiedTotal => (h t:E)) he
  have hfull : Set.range f = M.cover.projection ⁻¹' Set.range q := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,t⟩,rfl⟩
      exact ⟨(k z,t),(hproj z t).symm⟩
    · intro x hx
      obtain ⟨⟨z,t⟩,hqt⟩ := hx
      obtain ⟨x0,hx0⟩ := M.cover.projection_surjective (q (z,0))
      have hx0a : x0 ∈ a.val.image := by
        rw [ha]; change M.cover.projection x0 ∈ c.val.image
        rw [hx0,←hqc]; exact Set.mem_range_self z
      obtain ⟨w,hw⟩ := hx0a
      have hkw : k w = z := by
        have he : q (k w,0) = q (z,0) := (hproj w 0).symm.trans
          (by rw [hfzero,hw,hx0])
        exact congrArg Prod.fst (hq.injective he)
      have hpx : M.cover.projection (f (w,t)) = M.cover.projection x := by
        rw [hproj,hkw]; exact hqt
      rcases (M.cover.fiber_pair (f (w,t)) x).mp hpx with he | he
      · exact ⟨(w,t),he.symm⟩
      · have hd : M.cover.deck (a.val.map w) ∈ a.val.image := by
          rw [ha]; change M.cover.projection (M.cover.deck (a.val.map w)) ∈ c.val.image
          rw [M.cover.projection_deck]; exact hpa w
        obtain ⟨v,hv⟩ := hd
        exact ⟨(v,t),(deck_lift w v hv t).trans he.symm⟩
  have hfa : Set.range (fun z : Circle => f (z,0)) = a.val.image := by
    have he : (fun z : Circle => f (z,0)) = a.val.map := funext hfzero
    rw [he]; rfl
  have hfb : Set.range (fun z : Circle => f (z,1)) = b.val.image := by
    apply Set.Subset.antisymm
    · rintro x ⟨z,rfl⟩
      rw [hb]; change M.cover.projection (f (z,1)) ∈ d.val.image
      rw [hproj,←hqd]; exact Set.mem_range_self _
    · intro x hx
      have hxd : M.cover.projection x ∈ d.val.image := by rw [hb] at hx; exact hx
      obtain ⟨w,hw⟩ := hqd.symm ▸ hxd
      have hxf : x ∈ Set.range f := by rw [hfull]; exact ⟨(w,1),hw⟩
      obtain ⟨⟨z,t⟩,ht⟩ := hxf
      have he : q (k z,t) = q (w,1) := (hproj z t).symm.trans
        ((congrArg M.cover.projection ht).trans hw.symm)
      have ht1 : t = 1 := congrArg Prod.snd (hq.injective he)
      exact ⟨z,by simpa only [ht1] using ht⟩
  let C := f '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  let D := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  have hCfull : C = M.cover.projection ⁻¹' D := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,t⟩,ht,rfl⟩
      exact ⟨(k z,t),ht,(hproj z t).symm⟩
    · intro x hx
      obtain ⟨⟨w,s⟩,hs,hw⟩ := hx
      have hxf : x ∈ Set.range f := by rw [hfull]; exact ⟨(w,s),hw⟩
      obtain ⟨⟨z,t⟩,ht⟩ := hxf
      have he : q (k z,t) = q (w,s) := (hproj z t).symm.trans
        ((congrArg M.cover.projection ht).trans hw.symm)
      have hts : t = s := congrArg Prod.snd (hq.injective he)
      refine ⟨(z,t),?_,ht⟩
      change 0 < (s:ℝ) ∧ (s:ℝ) < 1 at hs
      change 0 < (t:ℝ) ∧ (t:ℝ) < 1
      simpa only [hts] using hs
  have hπC : M.cover.projection '' C = D := by
    rw [hCfull]
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩; exact hx
    · intro y hy
      obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
      exact ⟨x,by change M.cover.projection x∈D; rwa [hxy],hxy⟩
  have hJ : IsConnected {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1} := by
    have hCircle : IsConnected (Set.univ : Set Circle) := by
      rw [←Circle.exp_surjective.range_eq]
      exact isConnected_range Circle.exp.continuous
    convert hCircle.prod (isConnected_Ioo (show (0:Interval)<1 by norm_num)) using 1
    ext p; simp
  have hCc : IsConnected C := hJ.image f f.continuous.continuousOn
  have hCcomp : IsComplementComponent (a.val.image ∪ b.val.image) C := by
    refine ⟨hCc.nonempty,hCc,?_,?_⟩
    · intro x hx hab
      have hπx : M.cover.projection x∈D := by rw [hCfull] at hx; exact hx
      apply hqcomp.2.2.1 hπx
      rcases hab with ha' | hb'
      · rw [ha] at ha'; exact Or.inl ha'
      · rw [hb] at hb'; exact Or.inr hb'
    · intro V hVc hCV hVavoid
      have hπVc := hVc.image M.cover.projection M.cover.projection_continuous.continuousOn
      have hDπV : D ⊆ M.cover.projection '' V := by
        rw [←hπC]; exact Set.image_mono hCV
      have hπVavoid : M.cover.projection '' V ⊆ (c.val.image ∪ d.val.image)ᶜ := by
        rintro y ⟨x,hx,rfl⟩ (hc | hd)
        · exact hVavoid hx (Or.inl (ha.symm ▸ hc))
        · exact hVavoid hx (Or.inr (hb.symm ▸ hd))
      have hπV : M.cover.projection '' V = D :=
        hqcomp.2.2.2 _ hπVc hDπV hπVavoid
      apply Set.Subset.antisymm
      · intro x hx
        rw [hCfull]
        exact hπV ▸ (show M.cover.projection x ∈ M.cover.projection '' V from ⟨x,hx,rfl⟩)
      · exact hCV
  have hinv : M.cover.deck '' Set.range f = Set.range f := by
    rw [hfull]
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,M.cover.projection_deck] using hy
    · intro x hx
      exact ⟨M.cover.deck x,by simpa only [Set.mem_preimage,M.cover.projection_deck] using hx,
        M.cover.deck_involution x⟩
  have hπfull : M.cover.projection '' Set.range f = Set.range q := by
    rw [hfull]
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩; exact hx
    · intro y hy
      obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
      exact ⟨x,by change M.cover.projection x∈Set.range q; rwa [hxy],hxy⟩
  have hfree : ∀ x ∈ Set.range f, M.cover.deck x ≠ x := by
    intro x hx he
    exact Set.disjoint_left.mp hqmarks
      (hπfull ▸ (show M.cover.projection x ∈ M.cover.projection '' Set.range f from ⟨x,hx,rfl⟩))
      ((M.cover.fixed_iff_branch x).mp he)
  refine ⟨f,hf,hfa,hfb,hCcomp,hinv,hfree,?_⟩
  rwa [hπfull]

theorem circle33_actual_free_annulus_extended_quotient
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (f : C(Circle × Interval, E)) (hf : Topology.IsEmbedding f)
    (hfa : Set.range (fun z : Circle => f (z, 0)) = a.val.image)
    (hfb : Set.range (fun z : Circle => f (z, 1)) = b.val.image)
    (hcomponent : IsComplementComponent (a.val.image ∪ b.val.image)
      (f '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}))
    (hinv : M.cover.deck '' Set.range f = Set.range f)
    (hfree : ∀ x ∈ Set.range f, M.cover.deck x ≠ x)
    (hmarks : Disjoint (M.cover.projection '' Set.range f) (M.cover.branch : Set S)) :
    ∃ g : C(Circle × Set.Icc (-2 : ℝ) 3, S),
      Topology.IsEmbedding g ∧
      Set.range (fun z : Circle => g (z, ⟨0, by norm_num⟩)) = c.val.image ∧
      Set.range (fun z : Circle => g (z, ⟨1, by norm_num⟩)) = d.val.image ∧
      g '' {p : Circle × Set.Icc (-2 : ℝ) 3 | 0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 1} =
        M.cover.projection '' Set.range f ∧
      Disjoint (Set.range g) (M.cover.branch : Set S) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  have hcd : Disjoint c.val.image d.val.image := by
    apply Set.disjoint_left.mpr
    intro y hyc hyd
    obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
    have hxa : x ∈ a.val.image := by
      rw [ha]; change M.cover.projection x ∈ c.val.image; rwa [hxy]
    have hxb : x ∈ b.val.image := by
      rw [hb]; change M.cover.projection x ∈ d.val.image; rwa [hxy]
    obtain ⟨z,hz⟩ := hfa.symm ▸ hxa
    obtain ⟨w,hw⟩ := hfb.symm ▸ hxb
    have he := hf.injective (hz.trans hw.symm)
    have ht := congrArg (fun p : Circle × Interval => (p.2 : ℝ)) he
    norm_num at ht
  -- Atomic remaining sphere-annulus construction obligation, now separately
  -- approved as circle33_disjoint_actual_downstairs_annulus.
  have hdownstairs : ∃ q : C(Circle × Interval, S),
      Topology.IsEmbedding q ∧
      Set.range (fun z : Circle => q (z,0)) = c.val.image ∧
      Set.range (fun z : Circle => q (z,1)) = d.val.image ∧
      IsComplementComponent (c.val.image ∪ d.val.image)
        (q '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}) ∧
      Disjoint (Set.range q) (M.cover.branch : Set S) := by
    exact circle33_disjoint_actual_downstairs_annulus M c d hcd
  obtain ⟨q,hq,hqc,hqd,hqcomp,hqmarks⟩ := hdownstairs
  let D := q '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
  have hDc : IsConnected D := hqcomp.2.1
  have hDavoidc : D ⊆ c.val.imageᶜ := by
    intro x hx hc; exact hqcomp.2.2.1 hx (Or.inl hc)
  have hDavoidd : D ⊆ d.val.imageᶜ := by
    intro x hx hd; exact hqcomp.2.2.1 hx (Or.inr hd)
  have hboundary (z : Circle) (t : Interval) : q (z,t) ∈ closure D := by
    let k : Interval → S := fun r => q (z,r)
    have hk : Continuous k := q.continuous.comp
      (continuous_const.prodMk continuous_id)
    have htcl : t ∈ closure (Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (show (0 : Interval) ≠ 1 by norm_num)]
      exact ⟨unitInterval.nonneg t,unitInterval.le_one t⟩
    have himage : k '' Ioo (0 : Interval) 1 ⊆ D := by
      rintro y ⟨r,hr,rfl⟩
      exact ⟨(z,r),hr,rfl⟩
    exact closure_mono himage (image_closure_subset_closure_image hk ⟨t,htcl,rfl⟩)
  have hqcl : Set.range q ⊆ closure D := by
    rintro y ⟨⟨z,t⟩,rfl⟩; exact hboundary z t
  have hccl : c.val.image ⊆ closure D := by
    intro y hy; obtain ⟨z,rfl⟩ := hqc.symm ▸ hy; exact hboundary z 0
  have hdcl : d.val.image ⊆ closure D := by
    intro y hy; obtain ⟨z,rfl⟩ := hqd.symm ▸ hy; exact hboundary z 1
  have oriented_sides (p : Circle33 M) (havoid : D ⊆ p.val.imageᶜ) :
      ∃ U V : Set S,
        IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = p.val.imageᶜ ∧ D ⊆ U ∧
        ∃ dV : Metric.closedBall (0 : Plane) 1 ≃ₜ closure V,
          (∀ x, (dV x:S) ∈ p.val.image ↔ ‖x.val‖=1) ∧
          (∀ x, (dV x:S) ∈ V ↔ ‖x.val‖<1) ∧
          closure U = U ∪ p.val.image ∧ closure V = V ∪ p.val.image := by
    obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
      M.puncturedCircle_closedSides p.val
    have hsub : D ⊆ U ∪ V := by rwa [hcover]
    rcases hDc.isPreconnected.subset_or_subset hUo hVo hUV hsub with hDU | hDV
    · exact ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,hDU,dV,hVb,hVi,hclU,hclV⟩
    · exact ⟨V,U,hVo,hUo,hVc,hUc,hUV.symm,(union_comm V U).trans hcover,
        hDV,dU,hUb,hUi,hclV,hclU⟩
  obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcoverc,hDU,dV,hVb,hVi,hclU,hclV⟩ :=
    oriented_sides c hDavoidc
  obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWZ,hcoverd,hDW,dZ,hZb,hZi,hclW,hclZ⟩ :=
    oriented_sides d hDavoidd
  have hdU : d.val.image ⊆ U := by
    intro y hy
    have hh := closure_mono hDU (hdcl hy)
    rw [hclU] at hh
    exact hh.resolve_right (fun hc => Set.disjoint_left.mp hcd hc hy)
  have hcW : c.val.image ⊆ W := by
    intro y hy
    have hh := closure_mono hDW (hccl hy)
    rw [hclW] at hh
    exact hh.resolve_right (fun hd => Set.disjoint_left.mp hcd hy hd)
  have hVavoid : V ⊆ d.val.imageᶜ := by
    intro y hy hd; exact Set.disjoint_left.mp hUV (hdU hd) hy
  have hVsub : V ⊆ W := by
    have hVWZ : V ⊆ W ∪ Z := by rwa [hcoverd]
    rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hVWZ with hVW | hVZ
    · exact hVW
    · let y := c.val.curve.map 1
      have hyc : y ∈ c.val.image := Set.mem_range_self _
      have hycl : y ∈ closure V := by rw [hclV]; exact Or.inr hyc
      have hyz : y ∈ closure Z := closure_mono hVZ hycl
      rw [hclZ] at hyz
      exact False.elim (hyz.elim
        (fun hyz => Set.disjoint_left.mp hWZ (hcW hyc) hyz)
        (fun hyd => Set.disjoint_left.mp hcd hyc hyd))
  have hVZ : Disjoint V Z := by
    apply Set.disjoint_left.mpr
    intro y hyV hyZ; exact Set.disjoint_left.mp hWZ (hVsub hyV) hyZ
  have hqV : Disjoint (Set.range q) V := by
    apply Set.disjoint_left.mpr
    intro y hyq hyV
    have hyU : y ∈ U ∪ c.val.image := by
      rw [←hclU]; exact closure_mono hDU (hqcl hyq)
    rcases hyU with hyU | hyc
    · exact Set.disjoint_left.mp hUV hyU hyV
    · have hycomp : y ∈ c.val.imageᶜ := by
        rw [←hcoverc]; exact Or.inr hyV
      exact hycomp hyc
  have hqZ : Disjoint (Set.range q) Z := by
    apply Set.disjoint_left.mpr
    intro y hyq hyZ
    have hyW : y ∈ W ∪ d.val.image := by
      rw [←hclW]; exact closure_mono hDW (hqcl hyq)
    rcases hyW with hyW | hyd
    · exact Set.disjoint_left.mp hWZ hyW hyZ
    · have hycomp : y ∈ d.val.imageᶜ := by
        rw [←hcoverd]; exact Or.inr hyZ
      exact hycomp hyd
  -- Finite marked set yields a genuine positive radial clearance on each
  -- exterior disk. No mark-free collar certificate is assumed.
  have clear_radius (p : Circle33 M) (T : Set S)
      (dT : Metric.closedBall (0 : Plane) 1 ≃ₜ closure T)
      (hTb : ∀ x, (dT x:S) ∈ p.val.image ↔ ‖x.val‖=1) :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        ∀ y ∈ M.cover.branch, ∀ hy : y ∈ closure T,
          ‖(dT.symm ⟨y,hy⟩).val‖ < ρ := by
    let radius : S → ℝ := fun y => if hy : y ∈ closure T then
      ‖(dT.symm ⟨y,hy⟩).val‖ else 0
    have hbranch := M.cover.branch_card
    have hnonempty : M.cover.branch.Nonempty := by
      apply Finset.card_pos.mp; omega
    have hrlt (y : S) (hy : y ∈ M.cover.branch) : radius y < 1 := by
      dsimp only [radius]
      split_ifs with ht
      · have hle : ‖(dT.symm ⟨y,ht⟩).val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall,dist_zero_right] using
            (dT.symm ⟨y,ht⟩).property
        apply lt_of_le_of_ne hle
        intro he
        have hc := (hTb (dT.symm ⟨y,ht⟩)).mpr he
        simp only [dT.apply_symm_apply] at hc
        exact Set.disjoint_left.mp p.val.avoids_branch hc hy
      · norm_num
    let m := M.cover.branch.sup' hnonempty radius
    have hm : m < 1 := by
      change M.cover.branch.sup' hnonempty radius < 1
      apply Finset.sup'_induction hnonempty radius (p := fun x : ℝ => x < 1)
      · intro x hx y hy; exact max_lt hx hy
      · exact hrlt
    refine ⟨(max m 0+1)/2,by positivity,by linarith [max_lt hm (show (0:ℝ)<1 by norm_num)],?_⟩
    intro y hy ht
    have hmle : ‖(dT.symm ⟨y,ht⟩).val‖ ≤ m := by
      have hh := Finset.le_sup' radius hy
      simpa only [radius,dite_eq_left ht] using hh
    linarith [le_max_left m 0,max_lt hm (show (0:ℝ)<1 by norm_num)]
  obtain ⟨ρV,hρVpos,hρVlt,hclearV⟩ := clear_radius c V dV hVb
  obtain ⟨ρZ,hρZpos,hρZlt,hclearZ⟩ := clear_radius d Z dZ hZb
  have half_collar (p : Circle33 M) (T : Set S)
      (dT : Metric.closedBall (0 : Plane) 1 ≃ₜ closure T)
      (hTb : ∀ x, (dT x:S) ∈ p.val.image ↔ ‖x.val‖=1)
      (hTi : ∀ x, (dT x:S) ∈ T ↔ ‖x.val‖<1)
      (β : C(Circle,S)) (hβ : Topology.IsEmbedding β)
      (hβrange : Set.range β = p.val.image)
      (hclT : closure T = T ∪ p.val.image)
      (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1)
      (hclear : ∀ y ∈ M.cover.branch, ∀ hy : y ∈ closure T,
        ‖(dT.symm ⟨y,hy⟩).val‖ < ρ) :
      ∃ L : C(Circle × Interval,S),
        Topology.IsEmbedding L ∧
        (∀ z, L (z,0) = β z) ∧
        (∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∈ T) ∧
        Disjoint (Set.range L) (M.cover.branch : Set S) := by
    have hβcl (z : Circle) : β z ∈ closure T := by
      rw [hclT]; right; rw [←hβrange]; exact Set.mem_range_self _
    let k : Circle → Metric.closedBall (0 : Plane) 1 := fun z =>
      dT.symm ⟨β z,hβcl z⟩
    have hkcont : Continuous k := dT.symm.continuous.comp
      (β.continuous.subtype_mk hβcl)
    have hknorm (z : Circle) : ‖(k z).val‖ = 1 := by
      apply (hTb (k z)).mp
      change (dT (dT.symm ⟨β z,hβcl z⟩):S) ∈ p.val.image
      simp only [dT.apply_symm_apply]
      rw [←hβrange]; exact Set.mem_range_self _
    let α : Interval → ℝ := fun t => 1-(1-ρ)*(t:ℝ)/2
    have hαpos (t : Interval) : 0 < α t := by
      dsimp [α]; nlinarith [unitInterval.nonneg t,unitInterval.le_one t]
    have hαle (t : Interval) : α t ≤ 1 := by
      dsimp [α]; nlinarith [unitInterval.nonneg t]
    have hαclear (t : Interval) : ρ < α t := by
      dsimp [α]; nlinarith [unitInterval.nonneg t,unitInterval.le_one t]
    have hαlt (t : Interval) (ht : 0 < (t:ℝ)) : α t < 1 := by
      dsimp [α]; nlinarith
    let v : Circle × Interval → Metric.closedBall (0 : Plane) 1 := fun p =>
      ⟨α p.2 • (k p.1).val,by
        simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,
          Real.norm_eq_abs,abs_of_pos (hαpos p.2),hknorm,mul_one]
        exact hαle p.2⟩
    have hv : Continuous v := by
      apply Continuous.subtype_mk
      exact ((by fun_prop : Continuous (fun p : Circle × Interval => α p.2)).smul
        (continuous_subtype_val.comp (hkcont.comp continuous_fst)))
    let L : C(Circle × Interval,S) := ⟨fun p => (dT (v p):S),
      continuous_subtype_val.comp (dT.continuous.comp hv)⟩
    have hvnorm (z : Circle) (t : Interval) : ‖(v (z,t)).val‖ = α t := by
      simp only [v,norm_smul,Real.norm_eq_abs,abs_of_pos (hαpos t),hknorm,mul_one]
    have hLinj : Function.Injective L := by
      rintro ⟨z,t⟩ ⟨w,s⟩ he
      have hvE : v (z,t) = v (w,s) :=
        dT.injective (Subtype.ext he)
      have hnorm := congrArg (fun x : Metric.closedBall (0:Plane) 1 => ‖x.val‖) hvE
      rw [hvnorm,hvnorm] at hnorm
      have hts : t = s := by
        apply Subtype.ext
        dsimp only [α] at hnorm
        nlinarith
      subst s
      have hvec := congrArg Subtype.val hvE
      change α t • (k z).val = α t • (k w).val at hvec
      have hkE : k z = k w := Subtype.ext
        ((smul_right_injective Plane (ne_of_gt (hαpos t))) hvec)
      have hβE : β z = β w := by
        have hh := congrArg (fun x => (dT x:S)) hkE
        simpa only [k,dT.apply_symm_apply] using hh
      exact Prod.ext (hβ.injective hβE) rfl
    have hLzero (z : Circle) : L (z,0) = β z := by
      have hvzero : v (z,0) = k z := by
        apply Subtype.ext
        simp [v,α]
      change (dT (v (z,0)):S) = β z
      rw [hvzero]
      exact congrArg Subtype.val (dT.apply_symm_apply ⟨β z,hβcl z⟩)
    have hLinner (z : Circle) (t : Interval) (ht : 0 < (t:ℝ)) : L (z,t) ∈ T := by
      apply (hTi (v (z,t))).mpr
      rw [hvnorm]; exact hαlt t ht
    have hLm : Disjoint (Set.range L) (M.cover.branch : Set S) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨⟨z,t⟩,rfl⟩ hy
      have hh := hclear (L (z,t)) hy (dT (v (z,t))).property
      have hvinv : dT.symm ⟨L (z,t),(dT (v (z,t))).property⟩ = v (z,t) := by
        exact dT.symm_apply_apply (v (z,t))
      rw [hvinv,hvnorm] at hh
      exact (not_lt_of_ge (hαclear t).le) hh
    exact ⟨L,L.continuous.isClosedEmbedding hLinj |>.isEmbedding,hLzero,hLinner,hLm⟩
  let β0 : C(Circle,S) := ⟨fun z => q (z,0),q.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  let β1 : C(Circle,S) := ⟨fun z => q (z,1),q.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  have hβ0 : Topology.IsEmbedding β0 := β0.continuous.isClosedEmbedding
    (fun z w he => congrArg Prod.fst (hq.injective he)) |>.isEmbedding
  have hβ1 : Topology.IsEmbedding β1 := β1.continuous.isClosedEmbedding
    (fun z w he => congrArg Prod.fst (hq.injective he)) |>.isEmbedding
  obtain ⟨L,hL,hLzero,hLinner,hLmarks⟩ :=
    half_collar c V dV hVb hVi β0 hβ0 hqc hclV ρV hρVpos hρVlt hclearV
  obtain ⟨R,hR,hRzero,hRinner,hRmarks⟩ :=
    half_collar d Z dZ hZb hZi β1 hβ1 hqd hclZ ρZ hρZpos hρZlt hclearZ
  have hLq (z : Circle) (t : Interval) (w : Circle) (s : Interval)
      (he : L (z,t) = q (w,s)) : t = 0 ∧ s = 0 ∧ z = w := by
    have ht : t = 0 := by
      apply Subtype.ext
      by_contra hn
      have htp : 0 < (t:ℝ) := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm hn)
      exact Set.disjoint_left.mp hqV (Set.mem_range_self (w,s)) (he ▸ hLinner z t htp)
    subst t
    rw [hLzero] at he
    change q (z,0) = q (w,s) at he
    have hh := hq.injective he
    exact ⟨rfl,(congrArg Prod.snd hh).symm,congrArg Prod.fst hh⟩
  have hRq (z : Circle) (t : Interval) (w : Circle) (s : Interval)
      (he : R (z,t) = q (w,s)) : t = 0 ∧ s = 1 ∧ z = w := by
    have ht : t = 0 := by
      apply Subtype.ext
      by_contra hn
      have htp : 0 < (t:ℝ) := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm hn)
      exact Set.disjoint_left.mp hqZ (Set.mem_range_self (w,s)) (he ▸ hRinner z t htp)
    subst t
    rw [hRzero] at he
    change q (z,1) = q (w,s) at he
    have hh := hq.injective he
    exact ⟨rfl,(congrArg Prod.snd hh).symm,congrArg Prod.fst hh⟩
  have hLR : Disjoint (Set.range L) (Set.range R) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨⟨z,t⟩,ht⟩ ⟨⟨w,s⟩,hs⟩
    have he : L (z,t) = R (w,s) := ht.trans hs.symm
    by_cases ht0 : t = 0
    · subst t
      rw [hLzero] at he
      change q (z,0) = R (w,s) at he
      have hh := hRq w s z 0 he.symm
      have hc := congrArg Subtype.val hh.2.1
      norm_num at hc
    · have htp : 0 < (t:ℝ) := lt_of_le_of_ne (unitInterval.nonneg t)
        (fun hn => ht0 (Subtype.ext hn.symm))
      by_cases hs0 : s = 0
      · subst s
        rw [hRzero] at he
        change L (z,t) = q (w,1) at he
        exact ht0 (hLq z t w 1 he).1
      · have hsp : 0 < (s:ℝ) := lt_of_le_of_ne (unitInterval.nonneg s)
          (fun hn => hs0 (Subtype.ext hn.symm))
        exact Set.disjoint_left.mp hVZ (hLinner z t htp) (he.symm ▸ hRinner w s hsp)
  let X := Set.Icc (-2 : ℝ) 3
  let τL : X → Interval := fun r => projIcc 0 1 zero_le_one (-(r:ℝ)/2)
  let τQ : X → Interval := fun r => projIcc 0 1 zero_le_one (r:ℝ)
  let τR : X → Interval := fun r => projIcc 0 1 zero_le_one (((r:ℝ)-1)/2)
  have hτL (r : X) (hr : (r:ℝ) ≤ 0) : (τL r:ℝ) = -(r:ℝ)/2 := by
    dsimp only [τL]
    rw [projIcc_of_mem zero_le_one (show -(r:ℝ)/2 ∈ Icc (0:ℝ) 1 by
      constructor <;> linarith [r.property.1])]
  have hτQ (r : X) (hr0 : 0 ≤ (r:ℝ)) (hr1 : (r:ℝ) ≤ 1) : (τQ r:ℝ) = r := by
    dsimp only [τQ]; rw [projIcc_of_mem zero_le_one ⟨hr0,hr1⟩]
  have hτR (r : X) (hr : 1 ≤ (r:ℝ)) : (τR r:ℝ) = ((r:ℝ)-1)/2 := by
    dsimp only [τR]
    rw [projIcc_of_mem zero_le_one (show ((r:ℝ)-1)/2 ∈ Icc (0:ℝ) 1 by
      constructor <;> linarith [r.property.2])]
  let ℓ : Circle × X → S := fun p => L (p.1,τL p.2)
  let m : Circle × X → S := fun p => q (p.1,τQ p.2)
  let r : Circle × X → S := fun p => R (p.1,τR p.2)
  have hℓcont : Continuous ℓ := L.continuous.comp
    (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  have hmcont : Continuous m := q.continuous.comp
    (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  have hrcont : Continuous r := R.continuous.comp
    (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  let k : Circle × X → S := fun p => if (p.2:ℝ) ≤ 1 then m p else r p
  have hkcont : Continuous k := by
    apply continuous_if_le (by fun_prop) continuous_const hmcont.continuousOn hrcont.continuousOn
    intro p hp
    have hq1 : τQ p.2 = 1 := Subtype.ext (by rw [hτQ p.2 (by linarith) hp.le]; exact hp)
    have hr0 : τR p.2 = 0 := Subtype.ext (by rw [hτR p.2 hp.ge]; simp [hp])
    dsimp only [m,r]
    rw [hq1,hr0,hRzero]
    rfl
  let G : Circle × X → S := fun p => if (p.2:ℝ) ≤ 0 then ℓ p else k p
  have hGcont : Continuous G := by
    apply continuous_if_le (by fun_prop) continuous_const hℓcont.continuousOn hkcont.continuousOn
    intro p hp
    have hL0 : τL p.2 = 0 := Subtype.ext (by rw [hτL p.2 hp.le]; simp [hp])
    have hq0 : τQ p.2 = 0 := Subtype.ext (by rw [hτQ p.2 hp.ge (by linarith)]; exact hp)
    dsimp only [ℓ,k]
    rw [ite_eq_left (show (p.2:ℝ) ≤ 1 by linarith)]
    dsimp only [m]
    rw [hL0,hq0,hLzero]
    rfl
  have hℓinj (p s : Circle × X) (hp : (p.2:ℝ) ≤ 0) (hs : (s.2:ℝ) ≤ 0)
      (he : ℓ p = ℓ s) : p = s := by
    have hh := hL.injective he
    have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
    apply Prod.ext hz
    apply Subtype.ext
    have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
    change (τL p.2:ℝ) = (τL s.2:ℝ) at hval
    rw [hτL p.2 hp,hτL s.2 hs] at hval
    linarith
  have hminj (p s : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1)
      (hs0 : 0 ≤ (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) (he : m p = m s) : p = s := by
    have hh := hq.injective he
    have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
    apply Prod.ext hz
    apply Subtype.ext
    have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
    change (τQ p.2:ℝ) = (τQ s.2:ℝ) at hval
    rwa [hτQ p.2 hp0 hp1,hτQ s.2 hs0 hs1] at hval
  have hrinj (p s : Circle × X) (hp : 1 ≤ (p.2:ℝ)) (hs : 1 ≤ (s.2:ℝ))
      (he : r p = r s) : p = s := by
    have hh := hR.injective he
    have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
    apply Prod.ext hz
    apply Subtype.ext
    have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
    change (τR p.2:ℝ) = (τR s.2:ℝ) at hval
    rw [hτR p.2 hp,hτR s.2 hs] at hval
    linarith
  have hℓm (p s : Circle × X) (hs0 : 0 < (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) : ℓ p ≠ m s := by
    intro he
    have hh := (hLq p.1 (τL p.2) s.1 (τQ s.2) he).2.1
    have hv := congrArg Subtype.val hh
    change (τQ s.2:ℝ) = 0 at hv
    rw [hτQ s.2 hs0.le hs1] at hv
    linarith
  have hmr (p s : Circle × X) (hs : 1 < (s.2:ℝ)) : m p ≠ r s := by
    intro he
    have hh := (hRq s.1 (τR s.2) p.1 (τQ p.2) he.symm).1
    have hv := congrArg Subtype.val hh
    change (τR s.2:ℝ) = 0 at hv
    rw [hτR s.2 hs.le] at hv
    linarith
  have hℓr (p s : Circle × X) : ℓ p ≠ r s := by
    intro he
    exact Set.disjoint_left.mp hLR (Set.mem_range_self (p.1,τL p.2))
      ⟨(s.1,τR s.2),he.symm⟩
  have hGinj : Function.Injective G := by
    intro p s he
    dsimp only [G,k] at he
    by_cases hp0 : (p.2:ℝ) ≤ 0
    · rw [ite_eq_left hp0] at he
      by_cases hs0 : (s.2:ℝ) ≤ 0
      · rw [ite_eq_left hs0] at he; exact hℓinj p s hp0 hs0 he
      · rw [ite_eq_right hs0] at he
        by_cases hs1 : (s.2:ℝ) ≤ 1
        · rw [ite_eq_left hs1] at he; exact False.elim (hℓm p s (by linarith) hs1 he)
        · rw [ite_eq_right hs1] at he; exact False.elim (hℓr p s he)
    · rw [ite_eq_right hp0] at he
      by_cases hp1 : (p.2:ℝ) ≤ 1
      · rw [ite_eq_left hp1] at he
        by_cases hs0 : (s.2:ℝ) ≤ 0
        · rw [ite_eq_left hs0] at he; exact False.elim (hℓm s p (by linarith) hp1 he.symm)
        · rw [ite_eq_right hs0] at he
          by_cases hs1 : (s.2:ℝ) ≤ 1
          · rw [ite_eq_left hs1] at he; exact hminj p s (by linarith) hp1 (by linarith) hs1 he
          · rw [ite_eq_right hs1] at he; exact False.elim (hmr p s (by linarith) he)
      · rw [ite_eq_right hp1] at he
        by_cases hs0 : (s.2:ℝ) ≤ 0
        · rw [ite_eq_left hs0] at he; exact False.elim (hℓr s p he.symm)
        · rw [ite_eq_right hs0] at he
          by_cases hs1 : (s.2:ℝ) ≤ 1
          · rw [ite_eq_left hs1] at he; exact False.elim (hmr s p (by linarith) he.symm)
          · rw [ite_eq_right hs1] at he; exact hrinj p s (by linarith) (by linarith) he
  let g : C(Circle × X,S) := ⟨G,hGcont⟩
  have hg : Topology.IsEmbedding g := (hGcont.isClosedEmbedding hGinj).isEmbedding
  have hg0 (z : Circle) : g (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0) := by
    change G (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0)
    simp only [G,le_refl,if_true,ℓ,τL,neg_zero,zero_div,
      projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
    exact hLzero z
  have hg1 (z : Circle) : g (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1) := by
    change G (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1)
    simp only [G,show ¬(1:ℝ)≤0 by norm_num,if_false,k,le_refl,if_true,m,τQ,
      projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)]
    congr 1
  have hgmid (p : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1) :
      g p = q (p.1,⟨p.2.val,hp0,hp1⟩) := by
    by_cases hp : (p.2:ℝ) = 0
    · have he : p.2 = ⟨0,by dsimp [X]; norm_num⟩ := Subtype.ext hp
      calc
        g p = g (p.1,⟨0,by dsimp [X]; norm_num⟩) := congrArg g (Prod.ext rfl he)
        _ = q (p.1,0) := hg0 p.1
        _ = q (p.1,⟨p.2.val,hp0,hp1⟩) := congrArg q (Prod.ext rfl (Subtype.ext hp.symm))
    · change G p = _
      have hpp : 0 < (p.2:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hp)
      dsimp only [G,k]
      rw [ite_eq_right (not_le_of_gt hpp),ite_eq_left hp1]
      change q (p.1,τQ p.2) = _
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext; exact hτQ p.2 hp0 hp1
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := M.sphere.symm.chartedSpace
  have hginternal (z : Circle) (s : X) (hs0 : -2 < (s:ℝ)) (hs1 : (s:ℝ) < 3) :
      g (z,s) ∈ interior (Set.range g) := by
    let k : EuclideanSpace ℝ (Fin 2) → S := fun x =>
      g (z*Circle.exp (x 0),projIcc (-2) 3 (by norm_num) (x 1))
    let O : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x 0 ∈ Ioo (-1) 1 ∧ x 1 ∈ Ioo (-2) 3}
    have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hk : Continuous k := g.continuous.comp
      ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
        (continuous_projIcc.comp (by fun_prop)))
    have hki : InjOn k O := by
      intro x hx y hy he
      have hh := hg.injective he
      have h0 : Circle.exp (x 0) = Circle.exp (y 0) :=
        mul_left_cancel (congrArg Prod.fst hh)
      have hlen : (1:ℝ)-(-1) < 2*Real.pi := by linarith [Real.pi_gt_three]
      have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩
        ⟨hy.1.1.le,hy.1.2.le⟩ h0
      have h1 := congrArg (fun p : Circle × X => (p.2:ℝ)) hh
      simp only [projIcc_of_mem (show (-2:ℝ)≤3 by norm_num) ⟨hx.2.1.le,hx.2.2.le⟩,
        projIcc_of_mem (show (-2:ℝ)≤3 by norm_num) ⟨hy.2.1.le,hy.2.2.le⟩] at h1
      ext i
      fin_cases i
      · exact h0'
      · exact h1
    have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
    have hsub : k '' O ⊆ Set.range g := by
      rintro y ⟨x,hx,rfl⟩; exact Set.mem_range_self _
    apply (hopen.subset_interior_iff.mpr hsub)
    refine ⟨Plane.mk 0 s,⟨by norm_num [O],⟨hs0,hs1⟩⟩,?_⟩
    simp [k,projIcc_of_mem (show (-2:ℝ)≤3 by norm_num) s.property]
  have hqinternal : Set.range q ⊆ interior (Set.range g) := by
    rintro y ⟨⟨z,t⟩,rfl⟩
    let s : X := ⟨t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hh := hginternal z s (by dsimp [s]; linarith [t.property.1])
      (by dsimp [s]; linarith [t.property.2])
    have he := hgmid (z,s) t.property.1 t.property.2
    exact he ▸ hh
  have hLrange : Set.range L ⊆ Set.range q ∪ V := by
    rintro y ⟨⟨z,t⟩,rfl⟩
    by_cases ht : t = 0
    · subst t; rw [hLzero]; exact Or.inl (Set.mem_range_self (z,0))
    · right
      exact hLinner z t (lt_of_le_of_ne t.property.1
        (fun he => ht (Subtype.ext he.symm)))
  have hRrange : Set.range R ⊆ Set.range q ∪ Z := by
    rintro y ⟨⟨z,t⟩,rfl⟩
    by_cases ht : t = 0
    · subst t; rw [hRzero]; exact Or.inl (Set.mem_range_self (z,1))
    · right
      exact hRinner z t (lt_of_le_of_ne t.property.1
        (fun he => ht (Subtype.ext he.symm)))
  let B : Set S := Set.range q ∪ V ∪ Z
  have hgB : Set.range g ⊆ B := by
    rintro y ⟨p,rfl⟩
    change G p ∈ B
    dsimp only [G,k]
    split_ifs with hp0 hp1
    · exact Or.inl (hLrange (Set.mem_range_self _))
    · exact Or.inl (Or.inl (Set.mem_range_self _))
    · rcases hRrange (Set.mem_range_self (p.1,τR p.2)) with hh | hh
      · exact Or.inl (Or.inl hh)
      · exact Or.inr hh
  have hcqr : c.val.image ⊆ Set.range q := by
    intro y hy; obtain ⟨z,hz⟩ := hqc.symm ▸ hy; exact ⟨(z,0),hz⟩
  have hdqr : d.val.image ⊆ Set.range q := by
    intro y hy; obtain ⟨z,hz⟩ := hqd.symm ▸ hy; exact ⟨(z,1),hz⟩
  have hBclosed : IsClosed B := by
    apply isClosed_of_closure_subset
    dsimp only [B]
    rw [closure_union,closure_union,(isCompact_range q.continuous).isClosed.closure_eq,hclV,hclZ]
    rintro y ((hyq | (hyV | hyc)) | (hyZ | hyd))
    · exact Or.inl (Or.inl hyq)
    · exact Or.inl (Or.inr hyV)
    · exact Or.inl (Or.inl (hcqr hyc))
    · exact Or.inr hyZ
    · exact Or.inl (Or.inl (hdqr hyd))
  have hBopen : IsOpen B := by
    have he : B = interior (Set.range g) ∪ V ∪ Z := by
      apply Set.Subset.antisymm
      · rintro y ((hyq | hyV) | hyZ)
        · exact Or.inl (Or.inl (hqinternal hyq))
        · exact Or.inl (Or.inr hyV)
        · exact Or.inr hyZ
      · rintro y ((hy | hyV) | hyZ)
        · exact hgB (interior_subset hy)
        · exact Or.inl (Or.inr hyV)
        · exact Or.inr hyZ
    rw [he]; exact (isOpen_interior.union hVo).union hZo
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp only [←Module.finrank_eq_rank,finrank_euclideanSpace_fin]
    norm_num
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere hrank 0 zero_le_one)
  let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  have hB : B = Set.univ := (show IsClopen B from ⟨hBclosed,hBopen⟩).eq_univ
    ⟨q (1,0),Or.inl (Or.inl (Set.mem_range_self _))⟩
  let C := f '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  let F := M.cover.projection '' C
  let P := M.cover.projection '' Set.range f
  have hFc : IsConnected F := hcomponent.2.1.image M.cover.projection
    M.cover.projection_continuous.continuousOn
  have hFavoids : F ⊆ (c.val.image ∪ d.val.image)ᶜ := by
    rintro y ⟨x,hx,rfl⟩ (hc | hd)
    · exact hcomponent.2.2.1 hx (Or.inl (ha.symm ▸ hc))
    · exact hcomponent.2.2.1 hx (Or.inr (hb.symm ▸ hd))
  have hFboundary (z : Circle) (t : Interval) : M.cover.projection (f (z,t)) ∈ closure F := by
    let k : Interval → S := fun r => M.cover.projection (f (z,r))
    have hk : Continuous k := M.cover.projection_continuous.comp
      (f.continuous.comp (continuous_const.prodMk continuous_id))
    have htcl : t ∈ closure (Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (show (0 : Interval) ≠ 1 by norm_num)]
      exact ⟨t.property.1,t.property.2⟩
    have himage : k '' Ioo (0 : Interval) 1 ⊆ F := by
      rintro y ⟨r,hr,rfl⟩; exact ⟨f (z,r),⟨(z,r),hr,rfl⟩,rfl⟩
    exact closure_mono himage (image_closure_subset_closure_image hk ⟨t,htcl,rfl⟩)
  have hcF : c.val.image ⊆ P ∩ closure F := by
    intro y hy
    obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
    have hxa : x ∈ a.val.image := by rw [ha]; change M.cover.projection x∈c.val.image; rwa [hxy]
    obtain ⟨z,hz⟩ := hfa.symm ▸ hxa
    change f (z,0) = x at hz
    refine ⟨⟨x,⟨(z,0),hz⟩,hxy⟩,?_⟩
    have hh := hFboundary z 0; rwa [hz,hxy] at hh
  have hdF : d.val.image ⊆ P ∩ closure F := by
    intro y hy
    obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
    have hxb : x ∈ b.val.image := by rw [hb]; change M.cover.projection x∈d.val.image; rwa [hxy]
    obtain ⟨z,hz⟩ := hfb.symm ▸ hxb
    change f (z,1) = x at hz
    refine ⟨⟨x,⟨(z,1),hz⟩,hxy⟩,?_⟩
    have hh := hFboundary z 1; rwa [hz,hxy] at hh
  have hFU : F ⊆ U := by
    have hsub : F ⊆ U ∪ V := by
      rw [hcoverc]; intro y hy hc; exact hFavoids hy (Or.inl hc)
    rcases hFc.isPreconnected.subset_or_subset hUo hVo hUV hsub with h | h
    · exact h
    · let y := d.val.curve.map 1
      have hyd : y ∈ d.val.image := Set.mem_range_self _
      have hyV := closure_mono h (hdF hyd).2
      rw [hclV] at hyV
      exact False.elim (hyV.elim
        (fun hv => Set.disjoint_left.mp hUV (hdU hyd) hv)
        (fun hc => Set.disjoint_left.mp hcd hc hyd))
  have hFW : F ⊆ W := by
    have hsub : F ⊆ W ∪ Z := by
      rw [hcoverd]; intro y hy hd; exact hFavoids hy (Or.inr hd)
    rcases hFc.isPreconnected.subset_or_subset hWo hZo hWZ hsub with h | h
    · exact h
    · let y := c.val.curve.map 1
      have hyc : y ∈ c.val.image := Set.mem_range_self _
      have hyZ := closure_mono h (hcF hyc).2
      rw [hclZ] at hyZ
      exact False.elim (hyZ.elim
        (fun hz => Set.disjoint_left.mp hWZ (hcW hyc) hz)
        (fun hd => Set.disjoint_left.mp hcd hyc hd))
  have hFq : F ⊆ Set.range q := by
    intro y hy
    have hyB : y ∈ B := hB.symm ▸ Set.mem_univ y
    rcases hyB with (hyq | hyV) | hyZ
    · exact hyq
    · exact False.elim (Set.disjoint_left.mp hUV (hFU hy) hyV)
    · exact False.elim (Set.disjoint_left.mp hWZ (hFW hy) hyZ)
  have hFD : F ⊆ D := by
    intro y hy
    obtain ⟨⟨z,t⟩,ht⟩ := hFq hy
    have ht0 : 0 < (t:ℝ) := by
      apply lt_of_le_of_ne t.property.1
      intro he
      have htzero : t = 0 := Subtype.ext he.symm
      have hc : y ∈ c.val.image := by rw [←hqc]; exact ⟨z,by simpa only [htzero] using ht⟩
      exact hFavoids hy (Or.inl hc)
    have ht1 : (t:ℝ) < 1 := by
      apply lt_of_le_of_ne t.property.2
      intro he
      have htone : t = 1 := Subtype.ext he
      have hd : y ∈ d.val.image := by rw [←hqd]; exact ⟨z,by simpa only [htone] using ht⟩
      exact hFavoids hy (Or.inr hd)
    exact ⟨(z,t),⟨ht0,ht1⟩,ht⟩
  have hPinter : P ∩ D = F := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨x,⟨⟨z,t⟩,ht⟩,hx⟩,hyD⟩
      have hyt : M.cover.projection (f (z,t)) = y := congrArg M.cover.projection ht |>.trans hx
      have ht0 : 0 < (t:ℝ) := by
        apply lt_of_le_of_ne t.property.1
        intro he
        have htzero : t = 0 := Subtype.ext he.symm
        have hc : y ∈ c.val.image := by
          have hh : f (z,0) ∈ a.val.image := hfa ▸ Set.mem_range_self z
          rw [ha] at hh
          change M.cover.projection (f (z,0)) ∈ c.val.image at hh
          have he := hyt; rw [htzero] at he
          rwa [he] at hh
        exact hqcomp.2.2.1 hyD (Or.inl hc)
      have ht1 : (t:ℝ) < 1 := by
        apply lt_of_le_of_ne t.property.2
        intro he
        have htone : t = 1 := Subtype.ext he
        have hd : y ∈ d.val.image := by
          have hh : f (z,1) ∈ b.val.image := hfb ▸ Set.mem_range_self z
          rw [hb] at hh
          change M.cover.projection (f (z,1)) ∈ d.val.image at hh
          have he := hyt; rw [htone] at he
          rwa [he] at hh
        exact hqcomp.2.2.1 hyD (Or.inr hd)
      exact ⟨f (z,t),⟨(z,t),⟨ht0,ht1⟩,rfl⟩,hyt⟩
    · rintro y ⟨x,hx,hxy⟩
      exact ⟨⟨x,by obtain ⟨p,hp,he⟩ := hx; exact ⟨p,he⟩,hxy⟩,hFD ⟨x,hx,hxy⟩⟩
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace Plane E
  have hCopen : IsOpen C := complementComponent_open
    ((isCompact_range a.val.embedded.continuous).isClosed.union
      (isCompact_range b.val.embedded.continuous).isClosed) hcomponent
  have hFP : F ⊆ P := by
    rintro y ⟨x,⟨p,hp,he⟩,hxy⟩; exact ⟨x,⟨p,he⟩,hxy⟩
  have hFopen : IsOpen F := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨x,hx,rfl⟩
    have hreg : M.cover.projection x ∉ (M.cover.branch : Set S) := by
      intro hb
      exact Set.disjoint_left.mp hmarks (hFP ⟨x,hx,rfl⟩) hb
    obtain ⟨e,hxe,he⟩ := M.cover.unbranched_cover.isLocalHomeomorphOn x hreg
    refine ⟨e '' (e.source ∩ C),?_,?_,?_⟩
    · rintro y ⟨x,⟨hxs,hxC⟩,hxy⟩
      exact ⟨x,hxC,by simpa only [he] using hxy⟩
    · exact e.isOpen_image_of_subset_source (e.open_source.inter hCopen) inter_subset_left
    · exact ⟨x,⟨hxe,hx⟩,by rw [←he]⟩
  have hPclosed : IsClosed P :=
    ((isCompact_range f.continuous).image M.cover.projection_continuous).isClosed
  let : ConnectedSpace D := Subtype.connectedSpace hDc
  let T : Set D := {y | y.val ∈ P}
  have hTclosed : IsClosed T := hPclosed.preimage continuous_subtype_val
  have hTopen : IsOpen T := by
    have he : T = Subtype.val ⁻¹' F := by
      ext y
      constructor
      · intro hy
        have hh : y.val ∈ P ∩ D := ⟨hy,y.property⟩
        rwa [hPinter] at hh
      · intro hy; exact hFP hy
    rw [he]; exact hFopen.preimage continuous_subtype_val
  have hTnonempty : T.Nonempty := by
    obtain ⟨y,hy⟩ := hFc.nonempty
    exact ⟨⟨y,hFD hy⟩,hFP hy⟩
  have hT : T = Set.univ := (show IsClopen T from ⟨hTclosed,hTopen⟩).eq_univ hTnonempty
  have hDP : D ⊆ P := by
    intro y hy
    exact show (⟨y,hy⟩ : D) ∈ T from hT.symm ▸ Set.mem_univ _
  have hqrange : Set.range q = P := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨z,t⟩,rfl⟩
      by_cases ht0 : t = 0
      · subst t
        exact (hcF (hqc ▸ Set.mem_range_self z)).1
      · by_cases ht1 : t = 1
        · subst t
          exact (hdF (hqd ▸ Set.mem_range_self z)).1
        · apply hDP
          exact ⟨(z,t),⟨lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)),
            lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))⟩,rfl⟩
    · rintro y ⟨x,⟨⟨z,t⟩,ht⟩,hx⟩
      have hyt : M.cover.projection (f (z,t)) = y := congrArg M.cover.projection ht |>.trans hx
      by_cases ht0 : t = 0
      · subst t
        have hh : f (z,0) ∈ a.val.image := hfa ▸ Set.mem_range_self z
        rw [ha] at hh
        change M.cover.projection (f (z,0)) ∈ c.val.image at hh
        exact hyt ▸ hcqr hh
      · by_cases ht1 : t = 1
        · subst t
          have hh : f (z,1) ∈ b.val.image := hfb ▸ Set.mem_range_self z
          rw [hb] at hh
          change M.cover.projection (f (z,1)) ∈ d.val.image at hh
          exact hyt ▸ hdqr hh
        · exact hFq ⟨f (z,t),⟨(z,t),
            ⟨lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)),
              lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))⟩,rfl⟩,hyt⟩
  refine ⟨g,hg,?_,?_,?_,?_⟩
  · convert hqc using 1
    congr 1
    funext z; exact hg0 z
  · convert hqd using 1
    congr 1
    funext z; exact hg1 z
  · change g '' {p : Circle × X | 0 ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ 1} = P
    rw [←hqrange]
    apply Set.Subset.antisymm
    · rintro y ⟨p,⟨hp0,hp1⟩,rfl⟩
      rw [hgmid p hp0 hp1]
      exact Set.mem_range_self _
    · rintro y ⟨⟨z,t⟩,rfl⟩
      let p : Circle × X := (z,⟨t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩)
      refine ⟨p,⟨t.property.1,t.property.2⟩,?_⟩
      exact hgmid p t.property.1 t.property.2
  · apply Set.disjoint_left.mpr
    rintro y ⟨p,rfl⟩ hy
    change G p ∈ M.cover.branch at hy
    dsimp only [G,k] at hy
    split_ifs at hy with hp0 hp1
    · exact Set.disjoint_left.mp hLmarks (Set.mem_range_self _) hy
    · exact Set.disjoint_left.mp hqmarks (Set.mem_range_self _) hy
    · exact Set.disjoint_left.mp hRmarks (Set.mem_range_self _) hy

theorem circle33_disjoint_isotopic_full_preimages_unique_complementary_annulus
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image)
    (hd : Disjoint c.val.image d.val.image) :
    ∃ f : C(Circle × Interval, E),
      Topology.IsEmbedding f ∧
      Set.range (fun z : Circle => f (z, 0)) = a.val.image ∧
      Set.range (fun z : Circle => f (z, 1)) = b.val.image ∧
      IsComplementComponent (a.val.image ∪ b.val.image)
        (f '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}) ∧
      ∀ h : C(Circle × Interval, E),
        Topology.IsEmbedding h →
        Set.range (fun z : Circle => h (z, 0)) = a.val.image →
        Set.range (fun z : Circle => h (z, 1)) = b.val.image →
        IsComplementComponent (a.val.image ∪ b.val.image)
          (h '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}) →
        Set.range h = Set.range f := by
  classical
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let : T2Space S := M.sphere.symm.t2Space
  -- The sole sphere-annulus existence obligation has an independently approved
  -- exact producer head. It is not an additional hypothesis of this theorem.
  have hdownstairs : ∃ q : C(Circle × Interval,S),
      Topology.IsEmbedding q ∧
      Set.range (fun z : Circle => q (z,0)) = c.val.image ∧
      Set.range (fun z : Circle => q (z,1)) = d.val.image ∧
      IsComplementComponent (c.val.image ∪ d.val.image)
        (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) ∧
      Disjoint (Set.range q) (M.cover.branch : Set S) := by
    exact circle33_disjoint_actual_downstairs_annulus M c d hd
  obtain ⟨q,hq,hqc,hqd,hqcomp,hqmarks⟩ := hdownstairs
  have hpa (z : Circle) : M.cover.projection (a.val.map z) ∈ c.val.image := by
    have hh : a.val.map z ∈ a.val.image := Set.mem_range_self z
    rw [ha] at hh; exact hh
  let β : C(Circle,S) := ⟨fun z => q (z,0),q.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  have hβ : Topology.IsEmbedding β := (β.continuous.isClosedEmbedding
    (fun z w he => congrArg Prod.fst (hq.injective he))).isEmbedding
  let e : Circle ≃ₜ c.val.image := hβ.toHomeomorph.trans (Homeomorph.setCongr hqc)
  let k : Circle → Circle := fun z => e.symm ⟨M.cover.projection (a.val.map z),hpa z⟩
  have hk : Continuous k := e.symm.continuous.comp
    ((M.cover.projection_continuous.comp a.val.embedded.continuous).subtype_mk hpa)
  have hAreg (z : Circle) : a.val.map z ∉ M.cover.ramification := by
    change M.cover.projection (a.val.map z) ∉ (M.cover.branch : Set S)
    exact fun hm => Set.disjoint_left.mp c.val.avoids_branch (hpa z) hm
  let A : C(Circle,M.cover.unramifiedTotal) :=
    ⟨fun z => ⟨a.val.map z,hAreg z⟩,a.val.embedded.continuous.subtype_mk hAreg⟩
  have hQreg (p : Circle × Interval) : q p ∉ (M.cover.branch : Set S) :=
    fun hm => Set.disjoint_left.mp hqmarks (Set.mem_range_self p) hm
  let Q : C(Circle × Interval,M.cover.unramifiedBase) :=
    ⟨fun p => ⟨q p,hQreg p⟩,q.continuous.subtype_mk hQreg⟩
  let H : C(Interval × Circle,M.cover.unramifiedBase) := ⟨fun p => Q (k p.2,p.1),
    Q.continuous.comp ((hk.comp continuous_snd).prodMk continuous_fst)⟩
  let hp := M.cover.unramified_isCoveringMap
  have hzero (z : Circle) : H (0,z) = M.cover.unramifiedProjection (A z) := by
    apply Subtype.ext
    change q (k z,0) = M.cover.projection (a.val.map z)
    exact congrArg Subtype.val (e.apply_symm_apply ⟨M.cover.projection (a.val.map z),hpa z⟩)
  let K := hp.liftHomotopy H A hzero
  let f : C(Circle × Interval,E) := ⟨fun p => (K (p.2,p.1):E),
    continuous_subtype_val.comp (K.continuous.comp (continuous_snd.prodMk continuous_fst))⟩
  have hproj (z : Circle) (t : Interval) : M.cover.projection (f (z,t)) = q (k z,t) := by
    exact congrArg Subtype.val (congrFun (hp.liftHomotopy_lifts H A hzero) (t,z))
  have hfzero (z : Circle) : f (z,0) = a.val.map z := by
    exact congrArg Subtype.val (hp.liftHomotopy_zero H A hzero z)
  have hfinj : Function.Injective f := by
    rintro ⟨z,t⟩ ⟨w,s⟩ he
    have hqs := hq.injective ((hproj z t).symm.trans
      ((congrArg M.cover.projection he).trans (hproj w s)))
    have hts : t = s := congrArg Prod.snd hqs
    subst s
    have hkw : k z = k w := congrArg Prod.fst hqs
    have hpaths : (fun r : Interval => K (r,z)) = (fun r : Interval => K (r,w)) := by
      apply hp.eq_of_comp_eq
        (K.continuous.comp (continuous_id.prodMk continuous_const))
        (K.continuous.comp (continuous_id.prodMk continuous_const))
        (a := t)
      · funext r
        calc
          M.cover.unramifiedProjection (K (r,z)) = H (r,z) :=
            congrFun (hp.liftHomotopy_lifts H A hzero) (r,z)
          _ = H (r,w) := by change Q (k z,r) = Q (k w,r); rw [hkw]
          _ = M.cover.unramifiedProjection (K (r,w)) :=
            (congrFun (hp.liftHomotopy_lifts H A hzero) (r,w)).symm
      · exact Subtype.ext he
    have he0 : f (z,0) = f (w,0) :=
      congrArg (fun h : Interval → M.cover.unramifiedTotal => (h 0:E)) hpaths
    rw [hfzero,hfzero] at he0
    exact Prod.ext (a.val.embedded.injective he0) rfl
  have hf : Topology.IsEmbedding f := (f.continuous.isClosedEmbedding hfinj).isEmbedding
  -- Equivariance is derived by uniqueness of actual lifted paths, not supplied.
  have deck_lift (z w : Circle) (hw : a.val.map w = M.cover.deck (a.val.map z)) :
      ∀ t, f (w,t) = M.cover.deck (f (z,t)) := by
    have hkw : k w = k z := by
      apply congrArg e.symm
      apply Subtype.ext
      change M.cover.projection (a.val.map w) = M.cover.projection (a.val.map z)
      rw [hw,M.cover.projection_deck]
    have hZreg (r : Interval) : M.cover.deck (f (z,r)) ∉ M.cover.ramification := by
      change M.cover.projection (M.cover.deck (f (z,r))) ∉ (M.cover.branch : Set S)
      rw [M.cover.projection_deck]
      exact (K (r,z)).property
    let Z : Interval → M.cover.unramifiedTotal := fun r =>
      ⟨M.cover.deck (f (z,r)),hZreg r⟩
    have hZ : Continuous Z :=
      (M.cover.deck.continuous.comp (f.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk hZreg
    have he : (fun r : Interval => K (r,w)) = Z := by
      apply hp.eq_of_comp_eq
        (K.continuous.comp (continuous_id.prodMk continuous_const)) hZ
        (a := 0)
      · funext r
        apply Subtype.ext
        change M.cover.projection (f (w,r)) = M.cover.projection (M.cover.deck (f (z,r)))
        rw [M.cover.projection_deck,hproj,hproj,hkw]
      · apply Subtype.ext
        change f (w,0) = M.cover.deck (f (z,0))
        rw [hfzero,hfzero]; exact hw
    intro t
    exact congrArg (fun h : Interval → M.cover.unramifiedTotal => (h t:E)) he
  have hfull : Set.range f = M.cover.projection ⁻¹' Set.range q := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,t⟩,rfl⟩
      exact ⟨(k z,t),(hproj z t).symm⟩
    · intro x hx
      obtain ⟨⟨z,t⟩,hqt⟩ := hx
      obtain ⟨x0,hx0⟩ := M.cover.projection_surjective (q (z,0))
      have hx0a : x0 ∈ a.val.image := by
        rw [ha]; change M.cover.projection x0 ∈ c.val.image
        rw [hx0,←hqc]; exact Set.mem_range_self z
      obtain ⟨w,hw⟩ := hx0a
      have hkw : k w = z := by
        have he : q (k w,0) = q (z,0) := (hproj w 0).symm.trans
          (by rw [hfzero,hw,hx0])
        exact congrArg Prod.fst (hq.injective he)
      have hpx : M.cover.projection (f (w,t)) = M.cover.projection x := by
        rw [hproj,hkw]; exact hqt
      rcases (M.cover.fiber_pair (f (w,t)) x).mp hpx with he | he
      · exact ⟨(w,t),he.symm⟩
      · have hd : M.cover.deck (a.val.map w) ∈ a.val.image := by
          rw [ha]; change M.cover.projection (M.cover.deck (a.val.map w)) ∈ c.val.image
          rw [M.cover.projection_deck]; exact hpa w
        obtain ⟨v,hv⟩ := hd
        exact ⟨(v,t),(deck_lift w v hv t).trans he.symm⟩
  have hfa : Set.range (fun z : Circle => f (z,0)) = a.val.image := by
    have he : (fun z : Circle => f (z,0)) = a.val.map := funext hfzero
    rw [he]; rfl
  have hfb : Set.range (fun z : Circle => f (z,1)) = b.val.image := by
    apply Set.Subset.antisymm
    · rintro x ⟨z,rfl⟩
      rw [hb]; change M.cover.projection (f (z,1)) ∈ d.val.image
      rw [hproj,←hqd]; exact Set.mem_range_self _
    · intro x hx
      have hxd : M.cover.projection x ∈ d.val.image := by rw [hb] at hx; exact hx
      obtain ⟨w,hw⟩ := hqd.symm ▸ hxd
      have hxf : x ∈ Set.range f := by rw [hfull]; exact ⟨(w,1),hw⟩
      obtain ⟨⟨z,t⟩,ht⟩ := hxf
      have he : q (k z,t) = q (w,1) := (hproj z t).symm.trans
        ((congrArg M.cover.projection ht).trans hw.symm)
      have ht1 : t = 1 := congrArg Prod.snd (hq.injective he)
      exact ⟨z,by simpa only [ht1] using ht⟩
  let C := f '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  let D := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  have hCfull : C = M.cover.projection ⁻¹' D := by
    apply Set.Subset.antisymm
    · rintro x ⟨⟨z,t⟩,ht,rfl⟩
      exact ⟨(k z,t),ht,(hproj z t).symm⟩
    · intro x hx
      obtain ⟨⟨w,s⟩,hs,hw⟩ := hx
      have hxf : x ∈ Set.range f := by rw [hfull]; exact ⟨(w,s),hw⟩
      obtain ⟨⟨z,t⟩,ht⟩ := hxf
      have he : q (k z,t) = q (w,s) := (hproj z t).symm.trans
        ((congrArg M.cover.projection ht).trans hw.symm)
      have hts : t = s := congrArg Prod.snd (hq.injective he)
      refine ⟨(z,t),?_,ht⟩
      change 0 < (s:ℝ) ∧ (s:ℝ) < 1 at hs
      change 0 < (t:ℝ) ∧ (t:ℝ) < 1
      simpa only [hts] using hs
  have hπC : M.cover.projection '' C = D := by
    rw [hCfull]
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩; exact hx
    · intro y hy
      obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
      exact ⟨x,by change M.cover.projection x∈D; rwa [hxy],hxy⟩
  have hJ : IsConnected {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1} := by
    have hCircle : IsConnected (Set.univ : Set Circle) := by
      rw [←Circle.exp_surjective.range_eq]
      exact isConnected_range Circle.exp.continuous
    convert hCircle.prod (isConnected_Ioo (show (0:Interval)<1 by norm_num)) using 1
    ext p; simp
  have hCc : IsConnected C := hJ.image f f.continuous.continuousOn
  have hCcomp : IsComplementComponent (a.val.image ∪ b.val.image) C := by
    refine ⟨hCc.nonempty,hCc,?_,?_⟩
    · intro x hx hab
      have hπx : M.cover.projection x∈D := by rw [hCfull] at hx; exact hx
      apply hqcomp.2.2.1 hπx
      rcases hab with ha' | hb'
      · rw [ha] at ha'; exact Or.inl ha'
      · rw [hb] at hb'; exact Or.inr hb'
    · intro V hVc hCV hVavoid
      have hπVc := hVc.image M.cover.projection M.cover.projection_continuous.continuousOn
      have hDπV : D ⊆ M.cover.projection '' V := by
        rw [←hπC]; exact Set.image_mono hCV
      have hπVavoid : M.cover.projection '' V ⊆ (c.val.image ∪ d.val.image)ᶜ := by
        rintro y ⟨x,hx,rfl⟩ (hc | hd)
        · exact hVavoid hx (Or.inl (ha.symm ▸ hc))
        · exact hVavoid hx (Or.inr (hb.symm ▸ hd))
      have hπV : M.cover.projection '' V = D :=
        hqcomp.2.2.2 _ hπVc hDπV hπVavoid
      apply Set.Subset.antisymm
      · intro x hx
        rw [hCfull]
        exact hπV ▸ (show M.cover.projection x ∈ M.cover.projection '' V from ⟨x,hx,rfl⟩)
      · exact hCV
  have hinv : M.cover.deck '' Set.range f = Set.range f := by
    rw [hfull]
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,M.cover.projection_deck] using hy
    · intro x hx
      exact ⟨M.cover.deck x,by simpa only [Set.mem_preimage,M.cover.projection_deck] using hx,
        M.cover.deck_involution x⟩
  have hπfull : M.cover.projection '' Set.range f = Set.range q := by
    rw [hfull]
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩; exact hx
    · intro y hy
      obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
      exact ⟨x,by change M.cover.projection x∈Set.range q; rwa [hxy],hxy⟩
  have hfree : ∀ x ∈ Set.range f, M.cover.deck x ≠ x := by
    intro x hx he
    exact Set.disjoint_left.mp hqmarks
      (hπfull ▸ (show M.cover.projection x ∈ M.cover.projection '' Set.range f from ⟨x,hx,rfl⟩))
      ((M.cover.fixed_iff_branch x).mp he)
  have hcd := hd
  let D := q '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
  have hDc : IsConnected D := hqcomp.2.1
  have hDavoidc : D ⊆ c.val.imageᶜ := by
    intro x hx hc; exact hqcomp.2.2.1 hx (Or.inl hc)
  have hDavoidd : D ⊆ d.val.imageᶜ := by
    intro x hx hd; exact hqcomp.2.2.1 hx (Or.inr hd)
  have hboundary (z : Circle) (t : Interval) : q (z,t) ∈ closure D := by
    let k : Interval → S := fun r => q (z,r)
    have hk : Continuous k := q.continuous.comp
      (continuous_const.prodMk continuous_id)
    have htcl : t ∈ closure (Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (show (0 : Interval) ≠ 1 by norm_num)]
      exact ⟨unitInterval.nonneg t,unitInterval.le_one t⟩
    have himage : k '' Ioo (0 : Interval) 1 ⊆ D := by
      rintro y ⟨r,hr,rfl⟩
      exact ⟨(z,r),hr,rfl⟩
    exact closure_mono himage (image_closure_subset_closure_image hk ⟨t,htcl,rfl⟩)
  have hqcl : Set.range q ⊆ closure D := by
    rintro y ⟨⟨z,t⟩,rfl⟩; exact hboundary z t
  have hccl : c.val.image ⊆ closure D := by
    intro y hy; obtain ⟨z,rfl⟩ := hqc.symm ▸ hy; exact hboundary z 0
  have hdcl : d.val.image ⊆ closure D := by
    intro y hy; obtain ⟨z,rfl⟩ := hqd.symm ▸ hy; exact hboundary z 1
  have oriented_sides (p : Circle33 M) (havoid : D ⊆ p.val.imageᶜ) :
      ∃ U V : Set S,
        IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = p.val.imageᶜ ∧ D ⊆ U ∧
        ∃ dV : Metric.closedBall (0 : Plane) 1 ≃ₜ closure V,
          (∀ x, (dV x:S) ∈ p.val.image ↔ ‖x.val‖=1) ∧
          (∀ x, (dV x:S) ∈ V ↔ ‖x.val‖<1) ∧
          closure U = U ∪ p.val.image ∧ closure V = V ∪ p.val.image := by
    obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
      M.puncturedCircle_closedSides p.val
    have hsub : D ⊆ U ∪ V := by rwa [hcover]
    rcases hDc.isPreconnected.subset_or_subset hUo hVo hUV hsub with hDU | hDV
    · exact ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,hDU,dV,hVb,hVi,hclU,hclV⟩
    · exact ⟨V,U,hVo,hUo,hVc,hUc,hUV.symm,(union_comm V U).trans hcover,
        hDV,dU,hUb,hUi,hclV,hclU⟩
  obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcoverc,hDU,dV,hVb,hVi,hclU,hclV⟩ :=
    oriented_sides c hDavoidc
  obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWZ,hcoverd,hDW,dZ,hZb,hZi,hclW,hclZ⟩ :=
    oriented_sides d hDavoidd
  have hdU : d.val.image ⊆ U := by
    intro y hy
    have hh := closure_mono hDU (hdcl hy)
    rw [hclU] at hh
    exact hh.resolve_right (fun hc => Set.disjoint_left.mp hcd hc hy)
  have hcW : c.val.image ⊆ W := by
    intro y hy
    have hh := closure_mono hDW (hccl hy)
    rw [hclW] at hh
    exact hh.resolve_right (fun hd => Set.disjoint_left.mp hcd hy hd)
  have hVavoid : V ⊆ d.val.imageᶜ := by
    intro y hy hd; exact Set.disjoint_left.mp hUV (hdU hd) hy
  have hVsub : V ⊆ W := by
    have hVWZ : V ⊆ W ∪ Z := by rwa [hcoverd]
    rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hVWZ with hVW | hVZ
    · exact hVW
    · let y := c.val.curve.map 1
      have hyc : y ∈ c.val.image := Set.mem_range_self _
      have hycl : y ∈ closure V := by rw [hclV]; exact Or.inr hyc
      have hyz : y ∈ closure Z := closure_mono hVZ hycl
      rw [hclZ] at hyz
      exact False.elim (hyz.elim
        (fun hyz => Set.disjoint_left.mp hWZ (hcW hyc) hyz)
        (fun hyd => Set.disjoint_left.mp hcd hyc hyd))
  have hVZ : Disjoint V Z := by
    apply Set.disjoint_left.mpr
    intro y hyV hyZ; exact Set.disjoint_left.mp hWZ (hVsub hyV) hyZ
  have hqV : Disjoint (Set.range q) V := by
    apply Set.disjoint_left.mpr
    intro y hyq hyV
    have hyU : y ∈ U ∪ c.val.image := by
      rw [←hclU]; exact closure_mono hDU (hqcl hyq)
    rcases hyU with hyU | hyc
    · exact Set.disjoint_left.mp hUV hyU hyV
    · have hycomp : y ∈ c.val.imageᶜ := by
        rw [←hcoverc]; exact Or.inr hyV
      exact hycomp hyc
  have hqZ : Disjoint (Set.range q) Z := by
    apply Set.disjoint_left.mpr
    intro y hyq hyZ
    have hyW : y ∈ W ∪ d.val.image := by
      rw [←hclW]; exact closure_mono hDW (hqcl hyq)
    rcases hyW with hyW | hyd
    · exact Set.disjoint_left.mp hWZ hyW hyZ
    · have hycomp : y ∈ d.val.imageᶜ := by
        rw [←hcoverd]; exact Or.inr hyZ
      exact hycomp hyd
  -- Finite marked set yields a genuine positive radial clearance on each
  -- exterior disk. No mark-free collar certificate is assumed.
  have clear_radius (p : Circle33 M) (T : Set S)
      (dT : Metric.closedBall (0 : Plane) 1 ≃ₜ closure T)
      (hTb : ∀ x, (dT x:S) ∈ p.val.image ↔ ‖x.val‖=1) :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        ∀ y ∈ M.cover.branch, ∀ hy : y ∈ closure T,
          ‖(dT.symm ⟨y,hy⟩).val‖ < ρ := by
    let radius : S → ℝ := fun y => if hy : y ∈ closure T then
      ‖(dT.symm ⟨y,hy⟩).val‖ else 0
    have hbranch := M.cover.branch_card
    have hnonempty : M.cover.branch.Nonempty := by
      apply Finset.card_pos.mp; omega
    have hrlt (y : S) (hy : y ∈ M.cover.branch) : radius y < 1 := by
      dsimp only [radius]
      split_ifs with ht
      · have hle : ‖(dT.symm ⟨y,ht⟩).val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall,dist_zero_right] using
            (dT.symm ⟨y,ht⟩).property
        apply lt_of_le_of_ne hle
        intro he
        have hc := (hTb (dT.symm ⟨y,ht⟩)).mpr he
        simp only [dT.apply_symm_apply] at hc
        exact Set.disjoint_left.mp p.val.avoids_branch hc hy
      · norm_num
    let m := M.cover.branch.sup' hnonempty radius
    have hm : m < 1 := by
      change M.cover.branch.sup' hnonempty radius < 1
      apply Finset.sup'_induction hnonempty radius (p := fun x : ℝ => x < 1)
      · intro x hx y hy; exact max_lt hx hy
      · exact hrlt
    refine ⟨(max m 0+1)/2,by positivity,by linarith [max_lt hm (show (0:ℝ)<1 by norm_num)],?_⟩
    intro y hy ht
    have hmle : ‖(dT.symm ⟨y,ht⟩).val‖ ≤ m := by
      have hh := Finset.le_sup' radius hy
      simpa only [radius,dite_eq_left ht] using hh
    linarith [le_max_left m 0,max_lt hm (show (0:ℝ)<1 by norm_num)]
  obtain ⟨ρV,hρVpos,hρVlt,hclearV⟩ := clear_radius c V dV hVb
  obtain ⟨ρZ,hρZpos,hρZlt,hclearZ⟩ := clear_radius d Z dZ hZb
  have half_collar (p : Circle33 M) (T : Set S)
      (dT : Metric.closedBall (0 : Plane) 1 ≃ₜ closure T)
      (hTb : ∀ x, (dT x:S) ∈ p.val.image ↔ ‖x.val‖=1)
      (hTi : ∀ x, (dT x:S) ∈ T ↔ ‖x.val‖<1)
      (β : C(Circle,S)) (hβ : Topology.IsEmbedding β)
      (hβrange : Set.range β = p.val.image)
      (hclT : closure T = T ∪ p.val.image)
      (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1)
      (hclear : ∀ y ∈ M.cover.branch, ∀ hy : y ∈ closure T,
        ‖(dT.symm ⟨y,hy⟩).val‖ < ρ) :
      ∃ L : C(Circle × Interval,S),
        Topology.IsEmbedding L ∧
        (∀ z, L (z,0) = β z) ∧
        (∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∈ T) ∧
        Disjoint (Set.range L) (M.cover.branch : Set S) := by
    have hβcl (z : Circle) : β z ∈ closure T := by
      rw [hclT]; right; rw [←hβrange]; exact Set.mem_range_self _
    let k : Circle → Metric.closedBall (0 : Plane) 1 := fun z =>
      dT.symm ⟨β z,hβcl z⟩
    have hkcont : Continuous k := dT.symm.continuous.comp
      (β.continuous.subtype_mk hβcl)
    have hknorm (z : Circle) : ‖(k z).val‖ = 1 := by
      apply (hTb (k z)).mp
      change (dT (dT.symm ⟨β z,hβcl z⟩):S) ∈ p.val.image
      simp only [dT.apply_symm_apply]
      rw [←hβrange]; exact Set.mem_range_self _
    let α : Interval → ℝ := fun t => 1-(1-ρ)*(t:ℝ)/2
    have hαpos (t : Interval) : 0 < α t := by
      dsimp [α]; nlinarith [unitInterval.nonneg t,unitInterval.le_one t]
    have hαle (t : Interval) : α t ≤ 1 := by
      dsimp [α]; nlinarith [unitInterval.nonneg t]
    have hαclear (t : Interval) : ρ < α t := by
      dsimp [α]; nlinarith [unitInterval.nonneg t,unitInterval.le_one t]
    have hαlt (t : Interval) (ht : 0 < (t:ℝ)) : α t < 1 := by
      dsimp [α]; nlinarith
    let v : Circle × Interval → Metric.closedBall (0 : Plane) 1 := fun p =>
      ⟨α p.2 • (k p.1).val,by
        simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,
          Real.norm_eq_abs,abs_of_pos (hαpos p.2),hknorm,mul_one]
        exact hαle p.2⟩
    have hv : Continuous v := by
      apply Continuous.subtype_mk
      exact ((by fun_prop : Continuous (fun p : Circle × Interval => α p.2)).smul
        (continuous_subtype_val.comp (hkcont.comp continuous_fst)))
    let L : C(Circle × Interval,S) := ⟨fun p => (dT (v p):S),
      continuous_subtype_val.comp (dT.continuous.comp hv)⟩
    have hvnorm (z : Circle) (t : Interval) : ‖(v (z,t)).val‖ = α t := by
      simp only [v,norm_smul,Real.norm_eq_abs,abs_of_pos (hαpos t),hknorm,mul_one]
    have hLinj : Function.Injective L := by
      rintro ⟨z,t⟩ ⟨w,s⟩ he
      have hvE : v (z,t) = v (w,s) :=
        dT.injective (Subtype.ext he)
      have hnorm := congrArg (fun x : Metric.closedBall (0:Plane) 1 => ‖x.val‖) hvE
      rw [hvnorm,hvnorm] at hnorm
      have hts : t = s := by
        apply Subtype.ext
        dsimp only [α] at hnorm
        nlinarith
      subst s
      have hvec := congrArg Subtype.val hvE
      change α t • (k z).val = α t • (k w).val at hvec
      have hkE : k z = k w := Subtype.ext
        ((smul_right_injective Plane (ne_of_gt (hαpos t))) hvec)
      have hβE : β z = β w := by
        have hh := congrArg (fun x => (dT x:S)) hkE
        simpa only [k,dT.apply_symm_apply] using hh
      exact Prod.ext (hβ.injective hβE) rfl
    have hLzero (z : Circle) : L (z,0) = β z := by
      have hvzero : v (z,0) = k z := by
        apply Subtype.ext
        simp [v,α]
      change (dT (v (z,0)):S) = β z
      rw [hvzero]
      exact congrArg Subtype.val (dT.apply_symm_apply ⟨β z,hβcl z⟩)
    have hLinner (z : Circle) (t : Interval) (ht : 0 < (t:ℝ)) : L (z,t) ∈ T := by
      apply (hTi (v (z,t))).mpr
      rw [hvnorm]; exact hαlt t ht
    have hLm : Disjoint (Set.range L) (M.cover.branch : Set S) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨⟨z,t⟩,rfl⟩ hy
      have hh := hclear (L (z,t)) hy (dT (v (z,t))).property
      have hvinv : dT.symm ⟨L (z,t),(dT (v (z,t))).property⟩ = v (z,t) := by
        exact dT.symm_apply_apply (v (z,t))
      rw [hvinv,hvnorm] at hh
      exact (not_lt_of_ge (hαclear t).le) hh
    exact ⟨L,L.continuous.isClosedEmbedding hLinj |>.isEmbedding,hLzero,hLinner,hLm⟩
  let β0 : C(Circle,S) := ⟨fun z => q (z,0),q.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  let β1 : C(Circle,S) := ⟨fun z => q (z,1),q.continuous.comp
    (continuous_id.prodMk continuous_const)⟩
  have hβ0 : Topology.IsEmbedding β0 := β0.continuous.isClosedEmbedding
    (fun z w he => congrArg Prod.fst (hq.injective he)) |>.isEmbedding
  have hβ1 : Topology.IsEmbedding β1 := β1.continuous.isClosedEmbedding
    (fun z w he => congrArg Prod.fst (hq.injective he)) |>.isEmbedding
  obtain ⟨L,hL,hLzero,hLinner,hLmarks⟩ :=
    half_collar c V dV hVb hVi β0 hβ0 hqc hclV ρV hρVpos hρVlt hclearV
  obtain ⟨R,hR,hRzero,hRinner,hRmarks⟩ :=
    half_collar d Z dZ hZb hZi β1 hβ1 hqd hclZ ρZ hρZpos hρZlt hclearZ
  have hLq (z : Circle) (t : Interval) (w : Circle) (s : Interval)
      (he : L (z,t) = q (w,s)) : t = 0 ∧ s = 0 ∧ z = w := by
    have ht : t = 0 := by
      apply Subtype.ext
      by_contra hn
      have htp : 0 < (t:ℝ) := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm hn)
      exact Set.disjoint_left.mp hqV (Set.mem_range_self (w,s)) (he ▸ hLinner z t htp)
    subst t
    rw [hLzero] at he
    change q (z,0) = q (w,s) at he
    have hh := hq.injective he
    exact ⟨rfl,(congrArg Prod.snd hh).symm,congrArg Prod.fst hh⟩
  have hRq (z : Circle) (t : Interval) (w : Circle) (s : Interval)
      (he : R (z,t) = q (w,s)) : t = 0 ∧ s = 1 ∧ z = w := by
    have ht : t = 0 := by
      apply Subtype.ext
      by_contra hn
      have htp : 0 < (t:ℝ) := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm hn)
      exact Set.disjoint_left.mp hqZ (Set.mem_range_self (w,s)) (he ▸ hRinner z t htp)
    subst t
    rw [hRzero] at he
    change q (z,1) = q (w,s) at he
    have hh := hq.injective he
    exact ⟨rfl,(congrArg Prod.snd hh).symm,congrArg Prod.fst hh⟩
  have hLR : Disjoint (Set.range L) (Set.range R) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨⟨z,t⟩,ht⟩ ⟨⟨w,s⟩,hs⟩
    have he : L (z,t) = R (w,s) := ht.trans hs.symm
    by_cases ht0 : t = 0
    · subst t
      rw [hLzero] at he
      change q (z,0) = R (w,s) at he
      have hh := hRq w s z 0 he.symm
      have hc := congrArg Subtype.val hh.2.1
      norm_num at hc
    · have htp : 0 < (t:ℝ) := lt_of_le_of_ne (unitInterval.nonneg t)
        (fun hn => ht0 (Subtype.ext hn.symm))
      by_cases hs0 : s = 0
      · subst s
        rw [hRzero] at he
        change L (z,t) = q (w,1) at he
        exact ht0 (hLq z t w 1 he).1
      · have hsp : 0 < (s:ℝ) := lt_of_le_of_ne (unitInterval.nonneg s)
          (fun hn => hs0 (Subtype.ext hn.symm))
        exact Set.disjoint_left.mp hVZ (hLinner z t htp) (he.symm ▸ hRinner w s hsp)
  let X := Set.Icc (-2 : ℝ) 3
  let τL : X → Interval := fun r => projIcc 0 1 zero_le_one (-(r:ℝ)/2)
  let τQ : X → Interval := fun r => projIcc 0 1 zero_le_one (r:ℝ)
  let τR : X → Interval := fun r => projIcc 0 1 zero_le_one (((r:ℝ)-1)/2)
  have hτL (r : X) (hr : (r:ℝ) ≤ 0) : (τL r:ℝ) = -(r:ℝ)/2 := by
    dsimp only [τL]
    rw [projIcc_of_mem zero_le_one (show -(r:ℝ)/2 ∈ Icc (0:ℝ) 1 by
      constructor <;> linarith [r.property.1])]
  have hτQ (r : X) (hr0 : 0 ≤ (r:ℝ)) (hr1 : (r:ℝ) ≤ 1) : (τQ r:ℝ) = r := by
    dsimp only [τQ]; rw [projIcc_of_mem zero_le_one ⟨hr0,hr1⟩]
  have hτR (r : X) (hr : 1 ≤ (r:ℝ)) : (τR r:ℝ) = ((r:ℝ)-1)/2 := by
    dsimp only [τR]
    rw [projIcc_of_mem zero_le_one (show ((r:ℝ)-1)/2 ∈ Icc (0:ℝ) 1 by
      constructor <;> linarith [r.property.2])]
  let ℓ : Circle × X → S := fun p => L (p.1,τL p.2)
  let m : Circle × X → S := fun p => q (p.1,τQ p.2)
  let r : Circle × X → S := fun p => R (p.1,τR p.2)
  have hℓcont : Continuous ℓ := L.continuous.comp
    (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  have hmcont : Continuous m := q.continuous.comp
    (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  have hrcont : Continuous r := R.continuous.comp
    (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
  let k : Circle × X → S := fun p => if (p.2:ℝ) ≤ 1 then m p else r p
  have hkcont : Continuous k := by
    apply continuous_if_le (by fun_prop) continuous_const hmcont.continuousOn hrcont.continuousOn
    intro p hp
    have hq1 : τQ p.2 = 1 := Subtype.ext (by rw [hτQ p.2 (by linarith) hp.le]; exact hp)
    have hr0 : τR p.2 = 0 := Subtype.ext (by rw [hτR p.2 hp.ge]; simp [hp])
    dsimp only [m,r]
    rw [hq1,hr0,hRzero]
    rfl
  let G : Circle × X → S := fun p => if (p.2:ℝ) ≤ 0 then ℓ p else k p
  have hGcont : Continuous G := by
    apply continuous_if_le (by fun_prop) continuous_const hℓcont.continuousOn hkcont.continuousOn
    intro p hp
    have hL0 : τL p.2 = 0 := Subtype.ext (by rw [hτL p.2 hp.le]; simp [hp])
    have hq0 : τQ p.2 = 0 := Subtype.ext (by rw [hτQ p.2 hp.ge (by linarith)]; exact hp)
    dsimp only [ℓ,k]
    rw [ite_eq_left (show (p.2:ℝ) ≤ 1 by linarith)]
    dsimp only [m]
    rw [hL0,hq0,hLzero]
    rfl
  have hℓinj (p s : Circle × X) (hp : (p.2:ℝ) ≤ 0) (hs : (s.2:ℝ) ≤ 0)
      (he : ℓ p = ℓ s) : p = s := by
    have hh := hL.injective he
    have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
    apply Prod.ext hz
    apply Subtype.ext
    have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
    change (τL p.2:ℝ) = (τL s.2:ℝ) at hval
    rw [hτL p.2 hp,hτL s.2 hs] at hval
    linarith
  have hminj (p s : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1)
      (hs0 : 0 ≤ (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) (he : m p = m s) : p = s := by
    have hh := hq.injective he
    have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
    apply Prod.ext hz
    apply Subtype.ext
    have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
    change (τQ p.2:ℝ) = (τQ s.2:ℝ) at hval
    rwa [hτQ p.2 hp0 hp1,hτQ s.2 hs0 hs1] at hval
  have hrinj (p s : Circle × X) (hp : 1 ≤ (p.2:ℝ)) (hs : 1 ≤ (s.2:ℝ))
      (he : r p = r s) : p = s := by
    have hh := hR.injective he
    have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
    apply Prod.ext hz
    apply Subtype.ext
    have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
    change (τR p.2:ℝ) = (τR s.2:ℝ) at hval
    rw [hτR p.2 hp,hτR s.2 hs] at hval
    linarith
  have hℓm (p s : Circle × X) (hs0 : 0 < (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) : ℓ p ≠ m s := by
    intro he
    have hh := (hLq p.1 (τL p.2) s.1 (τQ s.2) he).2.1
    have hv := congrArg Subtype.val hh
    change (τQ s.2:ℝ) = 0 at hv
    rw [hτQ s.2 hs0.le hs1] at hv
    linarith
  have hmr (p s : Circle × X) (hs : 1 < (s.2:ℝ)) : m p ≠ r s := by
    intro he
    have hh := (hRq s.1 (τR s.2) p.1 (τQ p.2) he.symm).1
    have hv := congrArg Subtype.val hh
    change (τR s.2:ℝ) = 0 at hv
    rw [hτR s.2 hs.le] at hv
    linarith
  have hℓr (p s : Circle × X) : ℓ p ≠ r s := by
    intro he
    exact Set.disjoint_left.mp hLR (Set.mem_range_self (p.1,τL p.2))
      ⟨(s.1,τR s.2),he.symm⟩
  have hGinj : Function.Injective G := by
    intro p s he
    dsimp only [G,k] at he
    by_cases hp0 : (p.2:ℝ) ≤ 0
    · rw [ite_eq_left hp0] at he
      by_cases hs0 : (s.2:ℝ) ≤ 0
      · rw [ite_eq_left hs0] at he; exact hℓinj p s hp0 hs0 he
      · rw [ite_eq_right hs0] at he
        by_cases hs1 : (s.2:ℝ) ≤ 1
        · rw [ite_eq_left hs1] at he; exact False.elim (hℓm p s (by linarith) hs1 he)
        · rw [ite_eq_right hs1] at he; exact False.elim (hℓr p s he)
    · rw [ite_eq_right hp0] at he
      by_cases hp1 : (p.2:ℝ) ≤ 1
      · rw [ite_eq_left hp1] at he
        by_cases hs0 : (s.2:ℝ) ≤ 0
        · rw [ite_eq_left hs0] at he; exact False.elim (hℓm s p (by linarith) hp1 he.symm)
        · rw [ite_eq_right hs0] at he
          by_cases hs1 : (s.2:ℝ) ≤ 1
          · rw [ite_eq_left hs1] at he; exact hminj p s (by linarith) hp1 (by linarith) hs1 he
          · rw [ite_eq_right hs1] at he; exact False.elim (hmr p s (by linarith) he)
      · rw [ite_eq_right hp1] at he
        by_cases hs0 : (s.2:ℝ) ≤ 0
        · rw [ite_eq_left hs0] at he; exact False.elim (hℓr s p he.symm)
        · rw [ite_eq_right hs0] at he
          by_cases hs1 : (s.2:ℝ) ≤ 1
          · rw [ite_eq_left hs1] at he; exact False.elim (hmr s p (by linarith) he.symm)
          · rw [ite_eq_right hs1] at he; exact hrinj p s (by linarith) (by linarith) he
  let g : C(Circle × X,S) := ⟨G,hGcont⟩
  have hg : Topology.IsEmbedding g := (hGcont.isClosedEmbedding hGinj).isEmbedding
  have hg0 (z : Circle) : g (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0) := by
    change G (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0)
    simp only [G,le_refl,if_true,ℓ,τL,neg_zero,zero_div,
      projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
    exact hLzero z
  have hg1 (z : Circle) : g (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1) := by
    change G (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1)
    simp only [G,show ¬(1:ℝ)≤0 by norm_num,if_false,k,le_refl,if_true,m,τQ,
      projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)]
    congr 1
  have hgmid (p : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1) :
      g p = q (p.1,⟨p.2.val,hp0,hp1⟩) := by
    by_cases hp : (p.2:ℝ) = 0
    · have he : p.2 = ⟨0,by dsimp [X]; norm_num⟩ := Subtype.ext hp
      calc
        g p = g (p.1,⟨0,by dsimp [X]; norm_num⟩) := congrArg g (Prod.ext rfl he)
        _ = q (p.1,0) := hg0 p.1
        _ = q (p.1,⟨p.2.val,hp0,hp1⟩) := congrArg q (Prod.ext rfl (Subtype.ext hp.symm))
    · change G p = _
      have hpp : 0 < (p.2:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hp)
      dsimp only [G,k]
      rw [ite_eq_right (not_le_of_gt hpp),ite_eq_left hp1]
      change q (p.1,τQ p.2) = _
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext; exact hτQ p.2 hp0 hp1
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := M.sphere.symm.chartedSpace
  have hginternal (z : Circle) (s : X) (hs0 : -2 < (s:ℝ)) (hs1 : (s:ℝ) < 3) :
      g (z,s) ∈ interior (Set.range g) := by
    let k : EuclideanSpace ℝ (Fin 2) → S := fun x =>
      g (z*Circle.exp (x 0),projIcc (-2) 3 (by norm_num) (x 1))
    let O : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x 0 ∈ Ioo (-1) 1 ∧ x 1 ∈ Ioo (-2) 3}
    have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hk : Continuous k := g.continuous.comp
      ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
        (continuous_projIcc.comp (by fun_prop)))
    have hki : InjOn k O := by
      intro x hx y hy he
      have hh := hg.injective he
      have h0 : Circle.exp (x 0) = Circle.exp (y 0) :=
        mul_left_cancel (congrArg Prod.fst hh)
      have hlen : (1:ℝ)-(-1) < 2*Real.pi := by linarith [Real.pi_gt_three]
      have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩
        ⟨hy.1.1.le,hy.1.2.le⟩ h0
      have h1 := congrArg (fun p : Circle × X => (p.2:ℝ)) hh
      simp only [projIcc_of_mem (show (-2:ℝ)≤3 by norm_num) ⟨hx.2.1.le,hx.2.2.le⟩,
        projIcc_of_mem (show (-2:ℝ)≤3 by norm_num) ⟨hy.2.1.le,hy.2.2.le⟩] at h1
      ext i
      fin_cases i
      · exact h0'
      · exact h1
    have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
    have hsub : k '' O ⊆ Set.range g := by
      rintro y ⟨x,hx,rfl⟩; exact Set.mem_range_self _
    apply (hopen.subset_interior_iff.mpr hsub)
    refine ⟨Plane.mk 0 s,⟨by norm_num [O],⟨hs0,hs1⟩⟩,?_⟩
    simp [k,projIcc_of_mem (show (-2:ℝ)≤3 by norm_num) s.property]
  have hqinternal : Set.range q ⊆ interior (Set.range g) := by
    rintro y ⟨⟨z,t⟩,rfl⟩
    let s : X := ⟨t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hh := hginternal z s (by dsimp [s]; linarith [t.property.1])
      (by dsimp [s]; linarith [t.property.2])
    have he := hgmid (z,s) t.property.1 t.property.2
    exact he ▸ hh
  have hLrange : Set.range L ⊆ Set.range q ∪ V := by
    rintro y ⟨⟨z,t⟩,rfl⟩
    by_cases ht : t = 0
    · subst t; rw [hLzero]; exact Or.inl (Set.mem_range_self (z,0))
    · right
      exact hLinner z t (lt_of_le_of_ne t.property.1
        (fun he => ht (Subtype.ext he.symm)))
  have hRrange : Set.range R ⊆ Set.range q ∪ Z := by
    rintro y ⟨⟨z,t⟩,rfl⟩
    by_cases ht : t = 0
    · subst t; rw [hRzero]; exact Or.inl (Set.mem_range_self (z,1))
    · right
      exact hRinner z t (lt_of_le_of_ne t.property.1
        (fun he => ht (Subtype.ext he.symm)))
  let B : Set S := Set.range q ∪ V ∪ Z
  have hgB : Set.range g ⊆ B := by
    rintro y ⟨p,rfl⟩
    change G p ∈ B
    dsimp only [G,k]
    split_ifs with hp0 hp1
    · exact Or.inl (hLrange (Set.mem_range_self _))
    · exact Or.inl (Or.inl (Set.mem_range_self _))
    · rcases hRrange (Set.mem_range_self (p.1,τR p.2)) with hh | hh
      · exact Or.inl (Or.inl hh)
      · exact Or.inr hh
  have hcqr : c.val.image ⊆ Set.range q := by
    intro y hy; obtain ⟨z,hz⟩ := hqc.symm ▸ hy; exact ⟨(z,0),hz⟩
  have hdqr : d.val.image ⊆ Set.range q := by
    intro y hy; obtain ⟨z,hz⟩ := hqd.symm ▸ hy; exact ⟨(z,1),hz⟩
  have hBclosed : IsClosed B := by
    apply isClosed_of_closure_subset
    dsimp only [B]
    rw [closure_union,closure_union,(isCompact_range q.continuous).isClosed.closure_eq,hclV,hclZ]
    rintro y ((hyq | (hyV | hyc)) | (hyZ | hyd))
    · exact Or.inl (Or.inl hyq)
    · exact Or.inl (Or.inr hyV)
    · exact Or.inl (Or.inl (hcqr hyc))
    · exact Or.inr hyZ
    · exact Or.inl (Or.inl (hdqr hyd))
  have hBopen : IsOpen B := by
    have he : B = interior (Set.range g) ∪ V ∪ Z := by
      apply Set.Subset.antisymm
      · rintro y ((hyq | hyV) | hyZ)
        · exact Or.inl (Or.inl (hqinternal hyq))
        · exact Or.inl (Or.inr hyV)
        · exact Or.inr hyZ
      · rintro y ((hy | hyV) | hyZ)
        · exact hgB (interior_subset hy)
        · exact Or.inl (Or.inr hyV)
        · exact Or.inr hyZ
    rw [he]; exact (isOpen_interior.union hVo).union hZo
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp only [←Module.finrank_eq_rank,finrank_euclideanSpace_fin]
    norm_num
  let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere hrank 0 zero_le_one)
  let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  have hB : B = Set.univ := (show IsClopen B from ⟨hBclosed,hBopen⟩).eq_univ
    ⟨q (1,0),Or.inl (Or.inl (Set.mem_range_self _))⟩
  let : LocallyConnectedSpace S := M.actualSphere_locallyConnected
  have hDopen : IsOpen D := complementComponent_open
    ((isCompact_range c.val.curve.embedded.continuous).isClosed.union
      (isCompact_range d.val.curve.embedded.continuous).isClosed) hqcomp
  have hDqr : D ⊆ Set.range q := by
    rintro y ⟨p,hp,he⟩; exact ⟨p,he⟩
  have hDext : Disjoint D (V ∪ Z) := by
    apply Set.disjoint_left.mpr
    rintro y hyD (hyV | hyZ)
    · exact Set.disjoint_left.mp hqV (hDqr hyD) hyV
    · exact Set.disjoint_left.mp hqZ (hDqr hyD) hyZ
  have hpartition : D ∪ V ∪ Z = (c.val.image ∪ d.val.image)ᶜ := by
    apply Set.Subset.antisymm
    · rintro y ((hyD | hyV) | hyZ) (hyc | hyd)
      · exact hqcomp.2.2.1 hyD (Or.inl hyc)
      · exact hqcomp.2.2.1 hyD (Or.inr hyd)
      · have hh : y ∈ c.val.imageᶜ := by rw [←hcoverc]; exact Or.inr hyV
        exact hh hyc
      · exact hVavoid hyV hyd
      · exact Set.disjoint_left.mp hWZ (hcW hyc) hyZ
      · have hh : y ∈ d.val.imageᶜ := by rw [←hcoverd]; exact Or.inr hyZ
        exact hh hyd
    · intro y hy
      have hyB : y ∈ B := hB.symm ▸ Set.mem_univ y
      rcases hyB with (hyq | hyV) | hyZ
      · obtain ⟨⟨z,t⟩,ht⟩ := hyq
        have ht0 : 0 < (t:ℝ) := by
          apply lt_of_le_of_ne t.property.1
          intro he
          have he0 : t = 0 := Subtype.ext he.symm
          apply hy
          left
          rw [←hqc]; exact ⟨z,by simpa only [he0] using ht⟩
        have ht1 : (t:ℝ) < 1 := by
          apply lt_of_le_of_ne t.property.2
          intro he
          have he1 : t = 1 := Subtype.ext he
          apply hy
          right
          rw [←hqd]; exact ⟨z,by simpa only [he1] using ht⟩
        exact Or.inl (Or.inl ⟨(z,t),⟨ht0,ht1⟩,ht⟩)
      · exact Or.inl (Or.inr hyV)
      · exact Or.inr hyZ
  have range_closure (F : C(Circle × Interval,E)) :
      Set.range F = closure (F '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
    apply Set.Subset.antisymm
    · rintro y ⟨⟨z,t⟩,rfl⟩
      let k : Interval → E := fun r => F (z,r)
      have hk : Continuous k := F.continuous.comp (continuous_const.prodMk continuous_id)
      have htcl : t ∈ closure (Ioo (0 : Interval) 1) := by
        rw [closure_Ioo (show (0 : Interval)≠1 by norm_num)]
        exact ⟨t.property.1,t.property.2⟩
      have hsub : k '' Ioo (0 : Interval) 1 ⊆
          F '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1} := by
        rintro y ⟨s,hs,rfl⟩; exact ⟨(z,s),hs,rfl⟩
      exact closure_mono hsub (image_closure_subset_closure_image hk ⟨t,htcl,rfl⟩)
    · apply closure_minimal
      · rintro y ⟨p,hp,he⟩; exact ⟨p,he⟩
      · exact (isCompact_range F.continuous).isClosed
  refine ⟨f,hf,hfa,hfb,hCcomp,?_⟩
  intro h hh hha hhb hcomp
  let H := h '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
  let R := M.cover.projection '' H
  have hRc : IsConnected R := hcomp.2.1.image M.cover.projection
    M.cover.projection_continuous.continuousOn
  have hRavoid : R ⊆ (c.val.image ∪ d.val.image)ᶜ := by
    rintro y ⟨x,hx,rfl⟩ (hc | hd)
    · exact hcomp.2.2.1 hx (Or.inl (ha.symm ▸ hc))
    · exact hcomp.2.2.1 hx (Or.inr (hb.symm ▸ hd))
  have hRboundary (z : Circle) (t : Interval) : M.cover.projection (h (z,t)) ∈ closure R := by
    let k : Interval → S := fun r => M.cover.projection (h (z,r))
    have hk : Continuous k := M.cover.projection_continuous.comp
      (h.continuous.comp (continuous_const.prodMk continuous_id))
    have htcl : t ∈ closure (Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (show (0 : Interval)≠1 by norm_num)]
      exact ⟨t.property.1,t.property.2⟩
    have hsub : k '' Ioo (0 : Interval) 1 ⊆ R := by
      rintro y ⟨s,hs,rfl⟩; exact ⟨h (z,s),⟨(z,s),hs,rfl⟩,rfl⟩
    exact closure_mono hsub (image_closure_subset_closure_image hk ⟨t,htcl,rfl⟩)
  have hcR : c.val.image ⊆ closure R := by
    intro y hy
    obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
    have hxa : x ∈ a.val.image := by rw [ha]; change M.cover.projection x∈c.val.image; rwa [hxy]
    obtain ⟨z,hz⟩ := hha.symm ▸ hxa
    change h (z,0) = x at hz
    have he := hRboundary z 0; rwa [hz,hxy] at he
  have hdR : d.val.image ⊆ closure R := by
    intro y hy
    obtain ⟨x,hxy⟩ := M.cover.projection_surjective y
    have hxb : x ∈ b.val.image := by rw [hb]; change M.cover.projection x∈d.val.image; rwa [hxy]
    obtain ⟨z,hz⟩ := hhb.symm ▸ hxb
    change h (z,1) = x at hz
    have he := hRboundary z 1; rwa [hz,hxy] at he
  have hRD : R ⊆ D := by
    have hsub : R ⊆ D ∪ (V ∪ Z) := by
      rw [←union_assoc,hpartition]; exact hRavoid
    rcases hRc.isPreconnected.subset_or_subset hDopen (hVo.union hZo) hDext hsub with h | h
    · exact h
    · rcases hRc.isPreconnected.subset_or_subset hVo hZo hVZ h with hV | hZ
      · let y := d.val.curve.map 1
        have hyd : y ∈ d.val.image := Set.mem_range_self _
        have hy := closure_mono hV (hdR hyd)
        rw [hclV] at hy
        exact False.elim (hy.elim
          (fun hv => Set.disjoint_left.mp hUV (hdU hyd) hv)
          (fun hc => Set.disjoint_left.mp hcd hc hyd))
      · let y := c.val.curve.map 1
        have hyc : y ∈ c.val.image := Set.mem_range_self _
        have hy := closure_mono hZ (hcR hyc)
        rw [hclZ] at hy
        exact False.elim (hy.elim
          (fun hz => Set.disjoint_left.mp hWZ (hcW hyc) hz)
          (fun hd => Set.disjoint_left.mp hcd hyc hd))
  have hHC : H ⊆ C := by
    intro x hx
    rw [hCfull]
    exact hRD ⟨x,hx,rfl⟩
  have hCH : C = H := hcomp.2.2.2 C hCc hHC hCcomp.2.2.1
  calc
    Set.range h = closure H := range_closure h
    _ = closure C := by rw [hCH]
    _ = Set.range f := (range_closure f).symm

theorem actual_extended_mark_free_annulus_ambient_isotopy
    (M : HyperellipticModel E S)
    (g : C(Circle × Set.Icc (-2 : ℝ) 3, S))
    (hg : Topology.IsEmbedding g)
    (hmarks : Disjoint (Set.range g) (M.cover.branch : Set S)) :
    ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ Set.range g → H.map (t, x) = x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t, x) = x) ∧
      H.finalMap '' Set.range (fun z : Circle => g (z, ⟨0, by norm_num⟩)) =
        Set.range (fun z : Circle => g (z, ⟨1, by norm_num⟩)) := by
  classical
  let R := Set.Icc (-2 : ℝ) 3
  let ν : Interval × ℝ → ℝ := fun q =>
    if q.2 ≤ 0 then q.2 + q.1.val * (q.2 + 2) / 2
    else q.2 + q.1.val * (3 - q.2) / 3
  have hνcont : Continuous ν := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_snd continuous_const
    intro q hq
    rw [hq]
    ring
  have hνlo (t : Interval) : ν (t, -2) = -2 := by simp [ν]
  have hνhi (t : Interval) : ν (t, 3) = 3 := by norm_num [ν]
  have hνzero (r : ℝ) : ν (0, r) = r := by simp [ν]
  have hνone : ν (1, 0) = 1 := by norm_num [ν]
  have hνmono (t : Interval) : StrictMono (fun r => ν (t,r)) := by
    intro x y hxy
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hleft : 0 < 1 + (t : ℝ) / 2 := by linarith
    have hright : 0 < 1 - (t : ℝ) / 3 := by linarith
    dsimp [ν]
    split_ifs with hx hy hy
    · nlinarith [mul_pos (sub_pos.mpr hxy) hleft]
    · have hypos : 0 < y := lt_of_not_ge hy
      have hxl : (1 + (t : ℝ) / 2) * x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hleft.le hx
      have hyr : 0 < (1 - (t : ℝ) / 3) * y := mul_pos hright hypos
      nlinarith
    · exact False.elim (hx (hxy.le.trans hy))
    · nlinarith [mul_pos (sub_pos.mpr hxy) hright]
  have hνmem (t : Interval) (r : R) : ν (t, r.val) ∈ R := by
    constructor
    · rw [← hνlo t]
      exact (hνmono t).monotone r.property.1
    · rw [← hνhi t]
      exact (hνmono t).monotone r.property.2
  let μ : Interval × R → R := fun q => ⟨ν (q.1,q.2.val), hνmem q.1 q.2⟩
  have hμcont : Continuous μ :=
    (hνcont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hμinj (t : Interval) : Function.Injective (fun r : R => μ (t,r)) := by
    intro r s h
    apply Subtype.ext
    exact (hνmono t).injective (congrArg Subtype.val h)
  have hμsurj (t : Interval) : Function.Surjective (fun r : R => μ (t,r)) := by
    intro s
    have hc : Continuous (fun r => ν (t,r)) :=
      hνcont.comp (continuous_const.prodMk continuous_id)
    have hh := intermediate_value_Icc (show (-2 : ℝ) ≤ 3 by norm_num) hc.continuousOn
    have hs : (s : ℝ) ∈ Set.Icc (ν (t,-2)) (ν (t,3)) := by
      rw [hνlo, hνhi]
      exact s.property
    obtain ⟨r,hr,he⟩ := hh hs
    exact ⟨⟨r,hr⟩,Subtype.ext he⟩
  let K : AmbientIsotopy (Circle × R) := {
    map := ⟨fun q => (q.2.1, μ (q.1,q.2.2)),
      (continuous_fst.comp continuous_snd).prodMk
        (hμcont.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩
    homeomorphism_at := by
      intro t
      have hcont : Continuous (fun r : R => μ (t,r)) :=
        hμcont.comp (continuous_const.prodMk continuous_id)
      have hh := (isHomeomorph_iff_continuous_bijective).mpr
        ⟨hcont,hμinj t,hμsurj t⟩
      obtain ⟨e,he⟩ := isHomeomorph_iff_exists_homeomorph.mp hh
      exact ⟨(Homeomorph.refl Circle).prodCongr e,fun q => Prod.ext rfl (congrFun he q.2)⟩
    at_zero := by
      intro q
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact hνzero q.2.val }
  have hKlo (t : Interval) (z : Circle) :
      K.map (t,(z,⟨-2,by norm_num [R]⟩)) = (z,⟨-2,by norm_num [R]⟩) := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (hνlo t)
  have hKhi (t : Interval) (z : Circle) :
      K.map (t,(z,⟨3,by norm_num [R]⟩)) = (z,⟨3,by norm_num [R]⟩) := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (hνhi t)
  have hKlevel (z : Circle) :
      K.finalMap (z,⟨0,by norm_num [R]⟩) = (z,⟨1,by norm_num [R]⟩) := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext hνone
  let : T2Space S := M.sphere.symm.t2Space
  let : CompactSpace S := M.sphere.symm.compactSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := M.sphere.symm.chartedSpace
  let A : Set S := Set.range g
  let e : (Circle × R) ≃ₜ A := hg.toHomeomorph
  have hclosed : IsClosed A := (isCompact_range g.continuous).isClosed
  have hinternal (z : Circle) (r : R) (hr0 : -2 < (r : ℝ)) (hr1 : (r : ℝ) < 3) :
      g (z,r) ∈ interior A := by
    let f : EuclideanSpace ℝ (Fin 2) → S := fun x =>
      g (z * Circle.exp (x 0),projIcc (-2) 3 (by norm_num) (x 1))
    let U : Set (EuclideanSpace ℝ (Fin 2)) :=
      {x | x 0 ∈ Ioo (-1) 1 ∧ x 1 ∈ Ioo (-2) 3}
    have hU : IsOpen U := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hf : Continuous f := by
      apply g.continuous.comp
      apply Continuous.prodMk
      · exact continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))
      · exact continuous_projIcc.comp (by fun_prop)
    have hi : InjOn f U := by
      intro x hx y hy he
      have h := hg.injective he
      have h0 : Circle.exp (x 0) = Circle.exp (y 0) :=
        mul_left_cancel (congrArg Prod.fst h)
      have hlen : (1 : ℝ) - (-1) < 2 * Real.pi := by linarith [Real.pi_gt_three]
      have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩
        ⟨hy.1.1.le,hy.1.2.le⟩ h0
      have h1 := congrArg (fun q : Circle × R => (q.2 : ℝ)) h
      simp only [projIcc_of_mem (show (-2 : ℝ) ≤ 3 by norm_num) ⟨hx.2.1.le,hx.2.2.le⟩,
        projIcc_of_mem (show (-2 : ℝ) ≤ 3 by norm_num) ⟨hy.2.1.le,hy.2.2.le⟩] at h1
      ext i
      fin_cases i
      · exact h0'
      · exact h1
    have hopen : IsOpen (f '' U) :=
      CurveComplex.surface_invariance_of_domain_probe f U hU hf.continuousOn hi
    have hsub : f '' U ⊆ A := by
      rintro x ⟨y,hy,rfl⟩
      exact Set.mem_range_self _
    apply (hopen.subset_interior_iff.mpr hsub)
    refine ⟨Plane.mk 0 r,⟨by norm_num [U],?_⟩,?_⟩
    · exact ⟨hr0,hr1⟩
    · simp [f,projIcc_of_mem (show (-2 : ℝ) ≤ 3 by norm_num) r.property]
  let F : Interval × S → S := fun q =>
    if hx : q.2 ∈ A then g (K.map (q.1,e.symm ⟨q.2,hx⟩)) else q.2
  have hFg (t : Interval) (p : Circle × R) : F (t,g p) = g (K.map (t,p)) := by
    dsimp only [F]
    split_ifs with h
    · change g (K.map (t,e.symm (e p))) = _
      rw [e.symm_apply_apply]
    · exact False.elim (h ⟨p,rfl⟩)
  have hFout (t : Interval) (x : S) (hx : x ∉ A) : F (t,x) = x := by
    simp only [F,dite_eq_right hx]
  have hFboundary (t : Interval) (x : S) (hx : x ∉ interior A) : F (t,x) = x := by
    by_cases hxa : x ∈ A
    · obtain ⟨p,rfl⟩ := hxa
      have hb : (p.2 : ℝ) = -2 ∨ (p.2 : ℝ) = 3 := by
        by_contra h
        push Not at h
        exact hx (hinternal p.1 p.2
          (lt_of_le_of_ne p.2.property.1 h.1.symm)
          (lt_of_le_of_ne p.2.property.2 h.2))
      rw [hFg]
      rcases hb with hb | hb
      · have hp : p.2 = (⟨-2,by norm_num [R]⟩ : R) := Subtype.ext hb
        rw [show p = (p.1,⟨-2,by norm_num [R]⟩) from Prod.ext rfl hp,hKlo]
      · have hp : p.2 = (⟨3,by norm_num [R]⟩ : R) := Subtype.ext hb
        rw [show p = (p.1,⟨3,by norm_num [R]⟩) from Prod.ext rfl hp,hKhi]
    · exact hFout t x hxa
  have hcontA : ContinuousOn F {q : Interval × S | q.2 ∈ A} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun q : {q : Interval × S | q.2 ∈ A} =>
        g (K.map (q.val.1,e.symm ⟨q.val.2,q.property⟩))) :=
      g.continuous.comp (K.map.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          (e.symm.continuous.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _))))
    apply hc.congr
    intro q
    dsimp only [Set.domRestrict,F]
    split_ifs with h
    · rfl
    · exact False.elim (h q.property)
  have hcontC : ContinuousOn F {q : Interval × S | q.2 ∉ interior A} := by
    apply continuous_snd.continuousOn.congr
    intro q hq
    exact hFboundary q.1 q.2 hq
  have hFcont : Continuous F := by
    have hc := hcontA.union_of_isClosed hcontC
      (hclosed.preimage continuous_snd)
      (isOpen_interior.isClosed_compl.preimage continuous_snd)
    have hu : {q : Interval × S | q.2 ∈ A} ∪ {q : Interval × S | q.2 ∉ interior A} = univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_cases hq : q.2 ∈ A
      · exact Or.inl hq
      · exact Or.inr (fun h => hq (interior_subset h))
    rw [hu] at hc
    exact continuousOn_univ.mp hc
  have hFmem (t : Interval) (x : S) : F (t,x) ∈ A ↔ x ∈ A := by
    by_cases hx : x ∈ A
    · obtain ⟨p,rfl⟩ := hx
      rw [hFg]
      exact iff_of_true (Set.mem_range_self _) (Set.mem_range_self _)
    · rw [hFout t x hx]
  let H : AmbientIsotopy S := {
    map := ⟨F,hFcont⟩
    homeomorphism_at := by
      intro t
      obtain ⟨k,hk⟩ := K.homeomorphism_at t
      have hinj : Function.Injective (fun x => F (t,x)) := by
        intro x y hxy
        change F (t,x) = F (t,y) at hxy
        by_cases hx : x ∈ A
        · have hy : y ∈ A := (hFmem t y).mp (hxy ▸ (hFmem t x).mpr hx)
          obtain ⟨p,rfl⟩ := hx
          obtain ⟨q,rfl⟩ := hy
          rw [hFg,hFg] at hxy
          have hpq := hg.injective hxy
          have hpq' : k p = k q := by simpa only [hk] using hpq
          exact congrArg g (k.injective hpq')
        · have hy : y ∉ A := by
            intro hy
            exact hx ((hFmem t x).mp (hxy.symm ▸ (hFmem t y).mpr hy))
          simpa only [hFout t x hx,hFout t y hy] using hxy
      have hsurj : Function.Surjective (fun x => F (t,x)) := by
        intro y
        by_cases hy : y ∈ A
        · obtain ⟨p,rfl⟩ := hy
          refine ⟨g (k.symm p),?_⟩
          change F (t,g (k.symm p)) = g p
          rw [hFg,← hk,k.apply_symm_apply]
        · exact ⟨y,hFout t y hy⟩
      have hh := (isHomeomorph_iff_continuous_bijective).mpr
        ⟨hFcont.comp (continuous_const.prodMk continuous_id),hinj,hsurj⟩
      obtain ⟨h,he⟩ := isHomeomorph_iff_exists_homeomorph.mp hh
      exact ⟨h,fun x => congrFun he x⟩
    at_zero := by
      intro x
      change F (0,x) = x
      by_cases hx : x ∈ A
      · obtain ⟨p,rfl⟩ := hx
        rw [hFg]
        exact congrArg g (K.at_zero p)
      · exact hFout 0 x hx }
  refine ⟨H,?_,?_,?_⟩
  · intro t x hx
    exact hFout t x hx
  · intro t x hx
    exact hFout t x (fun ha => Set.disjoint_left.mp hmarks ha hx)
  · have hfinal (z : Circle) :
        H.finalMap (g (z,⟨0,by norm_num [R]⟩)) = g (z,⟨1,by norm_num [R]⟩) := by
      change F (1,g (z,⟨0,by norm_num [R]⟩)) = _
      rw [hFg]
      exact congrArg g (hKlevel z)
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨z,(hfinal z).symm⟩
    · rintro ⟨z,rfl⟩
      exact ⟨g (z,⟨0,by norm_num [R]⟩),⟨z,rfl⟩,hfinal z⟩

theorem circle33_disjoint_isotopic_full_preimages_marked_isotopy
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c d : Circle33 M)
    (ha : a.val.image = M.cover.projection ⁻¹' c.val.image)
    (hb : b.val.image = M.cover.projection ⁻¹' d.val.image)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image)
    (hd : Disjoint c.val.image d.val.image) :
    MarkedIsotopyRel M c.val.image d.val.image := by
  obtain ⟨f,hf,hfa,hfb,hcomponent,hinv,hfree,hmarks⟩ :=
    circle33_disjoint_isotopic_full_preimages_actual_annulus M a b c d ha hb hiso hd
  obtain ⟨g,hg,hg0,hg1,hcentral,hgmarks⟩ :=
    circle33_actual_free_annulus_extended_quotient M a b c d ha hb
      f hf hfa hfb hcomponent hinv hfree hmarks
  obtain ⟨H,hsupport,hfixed,hlevels⟩ :=
    actual_extended_mark_free_annulus_ambient_isotopy M g hg hgmarks
  refine ⟨H,hfixed,?_⟩
  simpa only [hg0,hg1] using hlevels

end CurveComplex.HyperellipticModel
