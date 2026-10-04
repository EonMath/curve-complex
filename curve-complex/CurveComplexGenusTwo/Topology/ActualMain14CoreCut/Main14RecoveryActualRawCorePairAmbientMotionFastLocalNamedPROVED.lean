import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenSphereAnnulusExteriorPartitionLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualEmbeddedAnnulusComplementComponentLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCylinderExteriorShrinkLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCylinderSupportedCollarCalibrationLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualConfinedCylinderCoordinateTransportLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreConfinedComparisonSourceLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualIntervalTwoLevelCalibrationLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies Metric
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 100000000
theorem actual_raw_core_pair_supported_ambient_motion (M : HyperellipticModel E S) (V : Set E) (B : Circle × Interval ≃ₜ V)
    (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
    (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩))
    (hproper : Set.range G ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    (hSides :
      ((∀ z (u : Interval), (u:ℝ)<1/2 → ((G (z,u)).2:ℝ)<1/2) ∧
        (∀ z (u : Interval), 1/2<(u:ℝ) → 1/2<((G (z,u)).2:ℝ))) ∨
      ((∀ z (u : Interval), (u:ℝ)<1/2 → 1/2<((G (z,u)).2:ℝ)) ∧
        (∀ z (u : Interval), 1/2<(u:ℝ) → ((G (z,u)).2:ℝ)<1/2))) :
    AmbientIsotopy.Rel
      (Set.range (fun z : Circle => (B (G (z,0))).val) ∪
        Set.range (fun z : Circle => (B (G (z,1))).val))
      (Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
        Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val)) := by
  all_goals
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hMove (M : HyperellipticModel E S)
        (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
        (r : Circle ≃ₜ Circle)
        (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩))
        (b : Bool)
        (hside : ∀ z (u : Interval), 1/2 < (u:ℝ) →
          if b then ((G (z,u)).2:ℝ)<1/2 else 1/2<((G (z,u)).2:ℝ))
        (hproper : Set.range G ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        (B : C(Circle × Interval,E)) (hB : IsEmbedding B) :
        ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ hεq : ε < 1/4, ∃ H : AmbientIsotopy E,
          H.finalMap '' (Set.range (fun z : Circle => B (G (z,0))))=
            Set.range (fun z : Circle => B (z,⟨1/2+(if b then ε else -ε),by
              cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
                constructor <;> linarith⟩)) ∧
          (∀ t x, x∉B '' (if b then
              Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1 else
              Set.univ ×ˢ Set.Ioo (0:Interval) ⟨1/2,by norm_num⟩) → H.map (t,x)=x) := by
      all_goals
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        have hMotion (M : HyperellipticModel E S)
            (Φ : C(Circle × Interval,S)) (hΦ : IsEmbedding Φ)
            (R : C(Circle × Interval,Circle × Interval)) (hR : IsEmbedding R)
            (q : C(Circle × Interval,S)) (hq : IsEmbedding q)
            (hmatch : ∀ p, Φ (R p)=q p)
            (a d : Interval) (hsub : Set.range R ⊆ Set.univ ×ˢ Set.Ioo a d)
            (B : C(Circle × Interval,E)) (hB : IsEmbedding B) :
            ∃ H : AmbientIsotopy E,
              H.finalMap '' (Set.range (fun z : Circle => B (R (z,0))))=
                Set.range (fun z : Circle => B (R (z,1))) ∧
              (∀ t x, x∉B '' (Set.univ ×ˢ Set.Ioo a d) → H.map (t,x)=x) := by
          all_goals
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            letI : T2Space S := M.sphere.symm.t2Space
            letI : ChartedSpace Plane S := M.sphere.symm.chartedSpace
            have hOpenBand {X : Type} [TopologicalSpace X] [ChartedSpace Plane X]
                (B : Circle × Interval → X) (hB : IsEmbedding B) (a b : Interval) :
                IsOpen (B '' (Set.univ ×ˢ Set.Ioo a b)) := by
              rw [isOpen_iff_forall_mem_open]
              rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
              have hua : (a:ℝ) < (u:ℝ) := hu.1
              have hub : (u:ℝ) < (b:ℝ) := hu.2
              have hu0 : (0:ℝ) < (u : ℝ) := lt_of_le_of_lt a.property.1 hua
              have hu1 : (u : ℝ) < 1 := lt_of_lt_of_le hub b.property.2
              let lo : ℝ := ((a:ℝ)+(u : ℝ))/2
              let hi : ℝ := ((u : ℝ)+(b:ℝ))/2
              have hlu : lo < (u : ℝ) := by dsimp [lo]; linarith
              have huh : (u : ℝ) < hi := by dsimp [hi]; linarith
              have hla : (a:ℝ) < lo := by dsimp [lo]; linarith
              have hl0 : 0 < lo := lt_of_le_of_lt a.property.1 hla
              have hhb : hi < (b:ℝ) := by dsimp [hi]; linarith
              have hh1 : hi < 1 := lt_of_lt_of_le hhb b.property.2
              have hlh : lo ≤ hi := (hlu.trans huh).le
              let width : ℝ → Interval := fun s =>
                ⟨(Set.projIcc lo hi hlh s : ℝ),
                  ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                    le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
              have hwc : Continuous width :=
                (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
              let θ := Complex.arg (z : ℂ)
              let f : EuclideanSpace ℝ (Fin 2) → X := fun x => B (Circle.exp (x 1),width (x 0))
              have hfc : Continuous f := hB.continuous.comp
                ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
              let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
                {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
              have hΩ : IsOpen Ω :=
                (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
              have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                  (width (x 0) : ℝ) = x 0 :=
                congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
              have hfi : Set.InjOn f Ω := by
                intro x hx w hw he
                have hp := hB.injective he
                have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                  (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                  ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
                have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
                change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
                rw [hclip x hx,hclip w hw] at hwidth
                ext i
                fin_cases i
                · exact hwidth
                · exact hangle
              have hopen : IsOpen (f '' Ω) :=
                CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
              have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo a b) := by
                rintro q ⟨x,hx,rfl⟩
                refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
                · change (a:ℝ) < (width (x 0) : ℝ)
                  rw [hclip x hx]
                  exact hla.trans hx.1.1
                · change (width (x 0) : ℝ) < (b:ℝ)
                  rw [hclip x hx]
                  exact hx.1.2.trans hhb
              let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
              have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
              have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
              have hx : x ∈ Ω := by
                refine ⟨?_,?_⟩
                · rw [hx0]; exact ⟨hlu,huh⟩
                · rw [hx1]; constructor <;> linarith [Real.pi_pos]
              have hwu : width (u : ℝ) = u := by
                apply Subtype.ext
                change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
                exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
              have hpoint : f x = B (z,u) := by
                dsimp [f]
                rw [hx0,hx1,hwu,Circle.exp_arg]
              exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
            have hCollar (M : HyperellipticModel E S) (c d : Curve S)
                (q : C(Circle × Interval,S)) (hq : IsEmbedding q)
                (hqc : Set.range (fun z : Circle => q (z,0))=c.image)
                (hqd : Set.range (fun z : Circle => q (z,1))=d.image)
                (U : Set S) (hU : IsOpen U) (hsub : Set.range q ⊆ U) :
                ∃ Q : C(Circle × Interval,S), IsEmbedding Q ∧ Set.range Q ⊆ U ∧
                  Set.range (fun z : Circle => Q (z,⟨1/3,by norm_num⟩))=c.image ∧
                  Set.range (fun z : Circle => Q (z,⟨2/3,by norm_num⟩))=d.image := by
              all_goals
                have hPartition (M : HyperellipticModel E S) (c d : Curve S)
                    (hd : Disjoint c.image d.image)
                    (q : C(Circle × Interval,S)) (hq : IsEmbedding q)
                    (hqc : Set.range (fun z : Circle => q (z,0))=c.image)
                    (hqd : Set.range (fun z : Circle => q (z,1))=d.image)
                    (hqcomp : IsComplementComponent (c.image ∪ d.image)
                      (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1})) :
                    ∃ U V W Z : Set S,
                      IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ IsOpen Z ∧
                      IsConnected U ∧ IsConnected V ∧ IsConnected W ∧ IsConnected Z ∧
                      Disjoint U V ∧ Disjoint W Z ∧ Disjoint V Z ∧
                      U ∪ V=c.imageᶜ ∧ W ∪ Z=d.imageᶜ ∧
                      closure U=U ∪ c.image ∧ closure V=V ∪ c.image ∧
                      closure W=W ∪ d.image ∧ closure Z=Z ∪ d.image ∧
                      d.image ⊆ U ∧ c.image ⊆ W ∧
                      Disjoint (Set.range q) V ∧ Disjoint (Set.range q) Z ∧
                      Set.range q ∪ V ∪ Z=Set.univ ∧
                      ∃ g : C(Circle × Set.Icc (-2:ℝ) 3,S), IsEmbedding g ∧
                        ∀ p : Circle × Set.Icc (-2:ℝ) 3,
                          ∀ hp0 : 0 ≤ (p.2:ℝ), ∀ hp1 : (p.2:ℝ) ≤ 1,
                            g p=q (p.1,⟨p.2.val,hp0,hp1⟩) := by
                  all_goals
                    letI : T2Space S := M.sphere.symm.t2Space
                    have actual_curve_closedSides (a : Curve S) :
                     ∃ U V : Set S,
                     IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = a.imageᶜ ∧
                     ∃ dU : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U,
                     ∃ dV : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure V,
                     (∀ x, (dU x:S) ∈ a.image ↔ ‖x.val‖=1) ∧
                     (∀ x, (dV x:S) ∈ a.image ↔ ‖x.val‖=1) ∧
                     (∀ x, (dU x:S) ∈ U ↔ ‖x.val‖<1) ∧
                     (∀ x, (dV x:S) ∈ V ↔ ‖x.val‖<1) ∧
                     closure U = U ∪ a.image ∧ closure V = V ∪ a.image := by
                      classical
                      letI : T2Space S := M.sphere.symm.t2Space
                      have hJordan (a : Curve S) :
                       ∃ c : CurveComplex.SpherePort.JordanCurve, c.image = M.sphere '' a.image := by
                       let b : C(Interval,Circle) := ⟨fun t => Circle.exp (2 * Real.pi * t.val),
                         Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
                       have hb : Function.Surjective b := by
                         intro z
                         have hz : z ∈ Circle.exp '' Icc (0:ℝ) (2*Real.pi) := by
                           have hset := Circle.periodic_exp.image_Icc (a := (0:ℝ)) (by positivity)
                           simp only [zero_add] at hset
                           rw [hset]
                           exact ⟨z.val.arg,Circle.exp_arg z⟩
                         obtain ⟨t,ht,he⟩ := hz
                         refine ⟨⟨t/(2*Real.pi),?_⟩,?_⟩
                         · constructor
                           · exact div_nonneg ht.1 (by positivity)
                           · exact (div_le_one (by positivity)).mpr ht.2
                         · change Circle.exp (2*Real.pi*(t/(2*Real.pi))) = z
                           rw [mul_div_cancel₀ _ (by positivity)]
                           exact he
                       have hcoll : ∀ s t : Interval, b s = b t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
                         intro s t he
                         obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
                         obtain ⟨hs0,hs1⟩ := s.property
                         obtain ⟨ht0,ht1⟩ := t.property
                         have hrel : s.val = t.val + n := by nlinarith [Real.pi_pos]
                         have hnlow : (-1:ℝ) ≤ n := by linarith
                         have hnup : (n:ℝ) ≤ 1 := by linarith
                         have hnl : (-1:ℤ) ≤ n := by exact_mod_cast hnlow
                         have hnu : n ≤ (1:ℤ) := by exact_mod_cast hnup
                         have hcases : n = 0 ∨ n = -1 ∨ n = 1 := by omega
                         rcases hcases with rfl | rfl | rfl
                         · left; apply Subtype.ext; simpa using hrel
                         · simp only [Int.cast_neg,Int.cast_one] at hrel
                           right; left
                           constructor
                           · apply Subtype.ext; change s.val = 0; linarith
                           · apply Subtype.ext; change t.val = 1; linarith
                         · simp only [Int.cast_one] at hrel
                           right; right
                           constructor
                           · apply Subtype.ext; change s.val = 1; linarith
                           · apply Subtype.ext; change t.val = 0; linarith
                       let c : CurveComplex.SpherePort.JordanCurve := {
                         map := fun t => M.sphere (a.map (b t))
                         continuous := M.sphere.continuous.comp (a.embedded.continuous.comp b.continuous)
                         injective_except_ends := fun s t he => hcoll s t (a.embedded.injective (M.sphere.injective he))
                         closed := by change M.sphere (a.map (Circle.exp (2*Real.pi*0))) = M.sphere (a.map (Circle.exp (2*Real.pi*1))); simp }
                       refine ⟨c,?_⟩
                       change Set.range (M.sphere ∘ (a.map ∘ b)) = M.sphere '' Set.range a.map
                       rw [Set.range_comp, hb.range_comp]
                      obtain ⟨c,hc⟩ := hJordan a
                      let d : Curve CurveComplex.SpherePort.Sphere :=
                        ⟨M.sphere ∘ a.map,M.sphere.isEmbedding.comp a.embedded⟩
                      obtain ⟨p,hp⟩ := CurveComplex.sphere_embedded_circle_omits_point d
                      have hd : d.image = M.sphere '' a.image := by
                        change Set.range (M.sphere ∘ a.map) = M.sphere '' Set.range a.map
                        exact Set.range_comp _ _
                      let P : CurveComplex.SpherePort.Chart c := {
                        puncture := p
                        avoids := by rw [hc,← hd]; exact hp
                        plane := puncturedSpherePlane p }
                      let C := P.planeImage c
                      have hC : Schoenflies.IsJordanCurve C := CurveComplex.SpherePort.chart_image_jordan c P
                      have hsep := Schoenflies.jordan_curve_theorem hC
                      let F : OnePoint JordanPlane ≃ₜ S :=
                        (CurveComplex.SpherePort.chartOnePoint c P).trans M.sphere.symm
                      let B : Set (OnePoint JordanPlane) := OnePoint.some '' C
                      let U : Set (OnePoint JordanPlane) := OnePoint.some '' Schoenflies.inside C
                      let V : Set (OnePoint JordanPlane) :=
                        {OnePoint.infty} ∪ OnePoint.some '' Schoenflies.outside C
                      have hB0 : (CurveComplex.SpherePort.chartOnePoint c P) '' B = c.image := by
                        ext x
                        constructor
                        · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
                          obtain ⟨y, hy, hzy⟩ := hz
                          change (P.plane.symm z).val ∈ c.image
                          rw [← hzy, P.plane.symm_apply_apply]
                          exact hy
                        · intro hx
                          let y : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} :=
                            ⟨x, fun he => P.avoids (he ▸ hx)⟩
                          refine ⟨OnePoint.some (P.plane y), ⟨P.plane y, ⟨y, hx, rfl⟩, rfl⟩, ?_⟩
                          change (P.plane.symm (P.plane y)).val = x
                          rw [P.plane.symm_apply_apply]
                      have hBimage : F '' B = a.image := by
                        have hcomp : F '' B = M.sphere.symm '' ((CurveComplex.SpherePort.chartOnePoint c P) '' B) := by
                          exact (Set.image_image M.sphere.symm (CurveComplex.SpherePort.chartOnePoint c P) B).symm
                        rw [hcomp,hB0,hc,Set.image_image]
                        simp only [Homeomorph.symm_apply_apply,Set.image_id']
                      have hdisj : Disjoint U V := by
                        rw [Set.disjoint_left]
                        intro x hx hy
                        cases x with
                        | infty => simp [U] at hx
                        | coe z =>
                          have hzU : z ∈ Schoenflies.inside C := by simpa [U] using hx
                          have hzV : z ∈ Schoenflies.outside C := by simpa [V] using hy
                          exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzU hzV
                      have hcover : U ∪ V = Bᶜ := by
                        ext x
                        cases x with
                        | infty => simp [U, V, B]
                        | coe z =>
                          have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
                          simpa [U, V, B] using hz
                      have hclU0 : closure U = OnePoint.some '' closure (Schoenflies.inside C) := by
                        have hk : IsCompact (closure (Schoenflies.inside C)) :=
                          Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
                        apply Set.Subset.antisymm
                        · exact closure_minimal (Set.image_mono subset_closure) (hk.image OnePoint.continuous_coe).isClosed
                        · exact image_closure_subset_closure_image OnePoint.continuous_coe
                      have hclU : closure U = U ∪ B := by
                        rw [hclU0, (Schoenflies.IsRegionOf.inside C).closure_eq hsep, Set.image_union]
                      have hclV : closure V = V ∪ B := by
                        change closure (CurveComplex.SpherePort.compactifiedOutside (Schoenflies.outside C)) = _
                        rw [CurveComplex.SpherePort.closure_compactifiedOutside,
                          (Schoenflies.IsRegionOf.outside C).closure_eq hsep]
                        simp only [CurveComplex.SpherePort.compactifiedOutside, Set.image_union]
                        exact Set.union_assoc _ _ _ |>.symm
                      have hUcomp : closure U = Vᶜ := by
                        rw [hclU]
                        ext x
                        cases x with
                        | infty => simp [U, V, B]
                        | coe z =>
                          have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
                          have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
                            fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
                          have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
                          have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
                          have hz' : z ∈ Schoenflies.inside C ∨ z ∈ C ↔ z ∉ Schoenflies.outside C := by
                            simp only [Set.mem_union, Set.mem_compl_iff] at hz
                            tauto
                          simpa [U, V, B] using hz'
                      have hVcomp : closure V = Uᶜ := by
                        rw [hclV]
                        ext x
                        cases x with
                        | infty => simp [U, V, B]
                        | coe z =>
                          have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
                          have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
                            fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
                          have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
                          have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
                          have hz' : z ∈ Schoenflies.outside C ∨ z ∈ C ↔ z ∉ Schoenflies.inside C := by
                            simp only [Set.mem_union, Set.mem_compl_iff] at hz
                            tauto
                          simpa [U, V, B] using hz'
                      have hopenU : IsOpen U := by
                        rw [← compl_compl U, ← hVcomp]
                        exact isClosed_closure.isOpen_compl
                      have hopenV : IsOpen V := by
                        rw [← compl_compl V, ← hUcomp]
                        exact isClosed_closure.isOpen_compl
                      have hintU : interior (closure U) = U := by
                        rw [hUcomp, interior_compl, hVcomp, compl_compl]
                      have hintV : interior (closure V) = V := by
                        rw [hVcomp, interior_compl, hUcomp, compl_compl]
                      have hboundU : frontier U = B := by
                        rw [hopenU.frontier_eq, hclU]
                        ext x
                        have hn : x ∈ U → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inl hx)
                        simp only [Set.mem_sdiff, Set.mem_union]
                        tauto
                      have hboundV : frontier V = B := by
                        rw [hopenV.frontier_eq, hclV]
                        ext x
                        have hn : x ∈ V → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inr hx)
                        simp only [Set.mem_sdiff, Set.mem_union]
                        tauto
                      obtain ⟨dU, hdUb, hdUi⟩ := CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary C hC
                      let eU : JordanClosedDisk ≃ₜ closure U :=
                        dU.trans ((OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage
                          (closure (Schoenflies.inside C))).trans (Homeomorph.setCongr hclU0.symm))
                      have heUb : ∀ x : JordanClosedDisk, (eU x : OnePoint JordanPlane) ∈ B ↔ ‖(x : JordanPlane)‖ = 1 := by
                        intro x
                        change OnePoint.some (dU x : JordanPlane) ∈ OnePoint.some '' C ↔ _
                        simpa using hdUb x
                      obtain ⟨q, hq⟩ := hsep.isConnected_inside.nonempty
                      let C' := Schoenflies.invert q '' C
                      have hC' : Schoenflies.IsJordanCurve C' := hC.invert_image hq.1
                      obtain ⟨dV, hdVb, hdVi⟩ := CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary C' hC'
                      let j := CurveComplex.SphereGapFinish.exteriorToInvertedInterior C hC q hq
                      have hclV0 : CurveComplex.SphereGapFinish.compactifiedExterior C = closure V := by
                        change _ = closure (CurveComplex.SpherePort.compactifiedOutside (Schoenflies.outside C))
                        rw [CurveComplex.SpherePort.closure_compactifiedOutside]
                        rfl
                      let eV : JordanClosedDisk ≃ₜ closure V :=
                        dV.trans (j.symm.trans (Homeomorph.setCongr hclV0))
                      have hjb : ∀ z : CurveComplex.SphereGapFinish.compactifiedExterior C,
                          (j z : JordanPlane) ∈ C' ↔ (z : OnePoint JordanPlane) ∈ B := by
                        intro z
                        change CurveComplex.SphereGapFinish.invertAtInfinity q z ∈ Schoenflies.invert q '' C ↔ _
                        constructor
                        · rintro ⟨y, hy, he⟩
                          have hyext : (OnePoint.some y : OnePoint JordanPlane) ∈
                              CurveComplex.SphereGapFinish.compactifiedExterior C := by
                            change (OnePoint.some y) ∈ {OnePoint.infty} ∪ OnePoint.some '' closure (Schoenflies.outside C)
                            exact Or.inr ⟨y, (Schoenflies.IsRegionOf.outside C).subset_closure hsep hy, rfl⟩
                          have heq : OnePoint.some y = (z : OnePoint JordanPlane) :=
                            CurveComplex.SphereGapFinish.invertAtInfinity_injOn_exterior C hC q hq hyext z.property he
                          exact heq ▸ Set.mem_image_of_mem OnePoint.some hy
                        · rintro ⟨y, hy, he⟩
                          rw [← he]
                          exact Set.mem_image_of_mem (Schoenflies.invert q) hy
                      have heVb : ∀ x : JordanClosedDisk, (eV x : OnePoint JordanPlane) ∈ B ↔ ‖(x : JordanPlane)‖ = 1 := by
                        intro x
                        change (j.symm (dV x) : OnePoint JordanPlane) ∈ B ↔ _
                        rw [← hjb (j.symm (dV x)), j.apply_symm_apply]
                        exact hdVb x
                      have heUi : ∀ x : JordanClosedDisk, (eU x : OnePoint JordanPlane) ∈ U ↔ ‖(x : JordanPlane)‖ < 1 := by
                        intro x
                        change OnePoint.some (dU x : JordanPlane) ∈ OnePoint.some '' Schoenflies.inside C ↔ _
                        simpa using hdUi x
                      have heVi : ∀ x : JordanClosedDisk, (eV x : OnePoint JordanPlane) ∈ V ↔ ‖(x : JordanPlane)‖ < 1 := by
                        intro x
                        have hxle : ‖(x : JordanPlane)‖ ≤ 1 := by
                          simpa only [dist_zero_right] using Metric.mem_closedBall.mp x.property
                        have hxcl : (eV x : OnePoint JordanPlane) ∈ V ∪ B := hclV ▸ (eV x).property
                        have hxnot : (eV x : OnePoint JordanPlane) ∈ V ↔ (eV x : OnePoint JordanPlane) ∉ B := by
                          constructor
                          · intro hx hb
                            exact (Set.ext_iff.mp hcover _).mp (Or.inr hx) hb
                          · intro hn
                            exact hxcl.resolve_right hn
                        rw [hxnot, heVb]
                        exact ⟨lt_of_le_of_ne hxle, fun h => h.ne⟩
                      have openDiskOf (T : Type) [TopologicalSpace T] (W : Set T)
                          (d : JordanClosedDisk ≃ₜ closure W)
                          (hdi : ∀ x : JordanClosedDisk, (d x : T) ∈ W ↔ ‖(x : JordanPlane)‖ < 1) :
                          Nonempty (JordanOpenDisk ≃ₜ W) := by
                        let f : JordanOpenDisk → JordanClosedDisk := fun x =>
                          ⟨x, by
                            apply Metric.mem_closedBall.mpr
                            exact (Metric.mem_ball.mp x.property).le⟩
                        let k : W → closure W := fun y => ⟨y, subset_closure y.property⟩
                        have hf : Continuous f := continuous_subtype_val.subtype_mk (fun x => (f x).property)
                        have hk : Continuous k := continuous_subtype_val.subtype_mk (fun y => (k y).property)
                        refine ⟨{
                          toFun := fun x => ⟨d (f x), (hdi (f x)).mpr (by
                            simpa only [dist_zero_right] using Metric.mem_ball.mp x.property)⟩
                          invFun := fun y => ⟨(d.symm (k y) : JordanPlane), by
                            apply Metric.mem_ball.mpr
                            simpa only [dist_zero_right, Function.comp_apply] using (hdi (d.symm (k y))).mp (by
                              rw [d.apply_symm_apply]
                              exact y.property)⟩
                          left_inv := ?_
                          right_inv := ?_
                          continuous_toFun := (continuous_subtype_val.comp (d.continuous.comp hf)).subtype_mk
                            (fun x => (hdi (f x)).mpr (by
                              simpa only [dist_zero_right] using Metric.mem_ball.mp x.property))
                          continuous_invFun := (continuous_subtype_val.comp (d.symm.continuous.comp hk)).subtype_mk
                            (fun y => by
                              apply Metric.mem_ball.mpr
                              simpa only [dist_zero_right, Function.comp_apply] using (hdi (d.symm (k y))).mp (by
                                rw [d.apply_symm_apply]
                                exact y.property)) }⟩
                        · intro x
                          apply Subtype.ext
                          have hkf : k ⟨d (f x), (hdi (f x)).mpr (by
                              simpa only [dist_zero_right] using Metric.mem_ball.mp x.property)⟩ = d (f x) :=
                            Subtype.ext rfl
                          change (d.symm (k _) : JordanPlane) = x.val
                          rw [hkf, d.symm_apply_apply]
                        · intro y
                          apply Subtype.ext
                          have hfk : f ⟨(d.symm (k y) : JordanPlane), by
                              apply Metric.mem_ball.mpr
                              simpa only [dist_zero_right, Function.comp_apply] using (hdi (d.symm (k y))).mp (by
                                rw [d.apply_symm_apply]
                                exact y.property)⟩ = d.symm (k y) := Subtype.ext rfl
                          change (d (f _) : T) = y.val
                          rw [hfk, d.apply_symm_apply]
                      obtain ⟨oU⟩ := openDiskOf (OnePoint JordanPlane) U eU heUi
                      obtain ⟨oV⟩ := openDiskOf (OnePoint JordanPlane) V eV heVi
                      have hball : IsConnected (JordanOpenDisk : Set JordanPlane) :=
                        (convex_ball (0 : JordanPlane) 1).isConnected ⟨0, by simp⟩
                      letI : ConnectedSpace JordanOpenDisk := isConnected_iff_connectedSpace.mp hball
                      have hconnU : IsConnected U :=
                        isConnected_iff_connectedSpace.mpr (oU.connectedSpace_iff.mp inferInstance)
                      have hconnV : IsConnected V :=
                        isConnected_iff_connectedSpace.mpr (oV.connectedSpace_iff.mp inferInstance)
                      let SU := F '' U
                      let SV := F '' V
                      have hsopenU : IsOpen SU := F.isOpenMap U hopenU
                      have hsopenV : IsOpen SV := F.isOpenMap V hopenV
                      have hsconnU : IsConnected SU := (F.isConnected_image).mpr hconnU
                      have hsconnV : IsConnected SV := (F.isConnected_image).mpr hconnV
                      have hsdisj : Disjoint SU SV := Set.disjoint_image_of_injective F.injective hdisj
                      have hscover : SU ∪ SV = a.imageᶜ := by
                        change F '' U ∪ F '' V = _
                        rw [← Set.image_union, hcover, F.image_compl, hBimage]
                      have hsclU : closure SU = SU ∪ a.image := by
                        rw [← F.image_closure, hclU, Set.image_union, hBimage]
                      have hsclV : closure SV = SV ∪ a.image := by
                        rw [← F.image_closure, hclV, Set.image_union, hBimage]
                      have hsintU : interior (closure SU) = SU := by
                        rw [← F.image_closure, ← F.image_interior, hintU]
                      have hsintV : interior (closure SV) = SV := by
                        rw [← F.image_closure, ← F.image_interior, hintV]
                      have hsboundU : frontier SU = a.image := by
                        rw [← F.image_frontier, hboundU, hBimage]
                      have hsboundV : frontier SV = a.image := by
                        rw [← F.image_frontier, hboundV, hBimage]
                      let dsU : JordanClosedDisk ≃ₜ closure SU :=
                        eU.trans ((F.isEmbedding.homeomorphImage (closure U)).trans
                          (Homeomorph.setCongr (F.image_closure U)))
                      let dsV : JordanClosedDisk ≃ₜ closure SV :=
                        eV.trans ((F.isEmbedding.homeomorphImage (closure V)).trans
                          (Homeomorph.setCongr (F.image_closure V)))
                      have hFmem (D : Set (OnePoint JordanPlane)) (z : OnePoint JordanPlane) :
                          F z ∈ F '' D ↔ z ∈ D := by
                        constructor
                        · rintro ⟨w, hw, hwz⟩
                          exact F.injective hwz ▸ hw
                        · intro hz
                          exact Set.mem_image_of_mem F hz
                      have hsUi : ∀ x : JordanClosedDisk, (dsU x : S) ∈ SU ↔ ‖(x : JordanPlane)‖ < 1 := by
                        intro x
                        change F (eU x : OnePoint JordanPlane) ∈ F '' U ↔ _
                        rw [hFmem]
                        exact heUi x
                      have hsVi : ∀ x : JordanClosedDisk, (dsV x : S) ∈ SV ↔ ‖(x : JordanPlane)‖ < 1 := by
                        intro x
                        change F (eV x : OnePoint JordanPlane) ∈ F '' V ↔ _
                        rw [hFmem]
                        exact heVi x
                      have hsUb : ∀ x : JordanClosedDisk, (dsU x : S) ∈ a.image ↔ ‖(x : JordanPlane)‖ = 1 := by
                        intro x
                        change F (eU x : OnePoint JordanPlane) ∈ a.image ↔ _
                        rw [← hBimage, hFmem]
                        exact heUb x
                      have hsVb : ∀ x : JordanClosedDisk, (dsV x : S) ∈ a.image ↔ ‖(x : JordanPlane)‖ = 1 := by
                        intro x
                        change F (eV x : OnePoint JordanPlane) ∈ a.image ↔ _
                        rw [← hBimage, hFmem]
                        exact heVb x
                      exact ⟨SU,SV,hsopenU,hsopenV,hsconnU,hsconnV,hsdisj,hscover,dsU,dsV,hsUb,hsVb,hsUi,hsVi,hsclU,hsclV⟩
                    have hcd := hd
                    let D := q '' {p : Circle × Interval | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
                    have hDc : IsConnected D := hqcomp.2.1
                    have hDavoidc : D ⊆ c.imageᶜ := by
                      intro x hx hc; exact hqcomp.2.2.1 hx (Or.inl hc)
                    have hDavoidd : D ⊆ d.imageᶜ := by
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
                    have hccl : c.image ⊆ closure D := by
                      intro y hy; obtain ⟨z,rfl⟩ := hqc.symm ▸ hy; exact hboundary z 0
                    have hdcl : d.image ⊆ closure D := by
                      intro y hy; obtain ⟨z,rfl⟩ := hqd.symm ▸ hy; exact hboundary z 1
                    have oriented_sides (p : Curve S) (havoid : D ⊆ p.imageᶜ) :
                        ∃ U V : Set S,
                          IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
                          Disjoint U V ∧ U ∪ V = p.imageᶜ ∧ D ⊆ U ∧
                          ∃ dV : Metric.closedBall (0 : Plane) 1 ≃ₜ closure V,
                            (∀ x, (dV x:S) ∈ p.image ↔ ‖x.val‖=1) ∧
                            (∀ x, (dV x:S) ∈ V ↔ ‖x.val‖<1) ∧
                            closure U = U ∪ p.image ∧ closure V = V ∪ p.image := by
                      obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
                        actual_curve_closedSides p
                      have hsub : D ⊆ U ∪ V := by rwa [hcover]
                      rcases hDc.isPreconnected.subset_or_subset hUo hVo hUV hsub with hDU | hDV
                      · exact ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,hDU,dV,hVb,hVi,hclU,hclV⟩
                      · exact ⟨V,U,hVo,hUo,hVc,hUc,hUV.symm,(union_comm V U).trans hcover,
                          hDV,dU,hUb,hUi,hclV,hclU⟩
                    obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcoverc,hDU,dV,hVb,hVi,hclU,hclV⟩ :=
                      oriented_sides c hDavoidc
                    obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWZ,hcoverd,hDW,dZ,hZb,hZi,hclW,hclZ⟩ :=
                      oriented_sides d hDavoidd
                    have hdU : d.image ⊆ U := by
                      intro y hy
                      have hh := closure_mono hDU (hdcl hy)
                      rw [hclU] at hh
                      exact hh.resolve_right (fun hc => Set.disjoint_left.mp hcd hc hy)
                    have hcW : c.image ⊆ W := by
                      intro y hy
                      have hh := closure_mono hDW (hccl hy)
                      rw [hclW] at hh
                      exact hh.resolve_right (fun hd => Set.disjoint_left.mp hcd hy hd)
                    have hVavoid : V ⊆ d.imageᶜ := by
                      intro y hy hd; exact Set.disjoint_left.mp hUV (hdU hd) hy
                    have hVsub : V ⊆ W := by
                      have hVWZ : V ⊆ W ∪ Z := by rwa [hcoverd]
                      rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hVWZ with hVW | hVZ
                      · exact hVW
                      · let y := c.map 1
                        have hyc : y ∈ c.image := Set.mem_range_self _
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
                      have hyU : y ∈ U ∪ c.image := by
                        rw [←hclU]; exact closure_mono hDU (hqcl hyq)
                      rcases hyU with hyU | hyc
                      · exact Set.disjoint_left.mp hUV hyU hyV
                      · have hycomp : y ∈ c.imageᶜ := by
                          rw [←hcoverc]; exact Or.inr hyV
                        exact hycomp hyc
                    have hqZ : Disjoint (Set.range q) Z := by
                      apply Set.disjoint_left.mpr
                      intro y hyq hyZ
                      have hyW : y ∈ W ∪ d.image := by
                        rw [←hclW]; exact closure_mono hDW (hqcl hyq)
                      rcases hyW with hyW | hyd
                      · exact Set.disjoint_left.mp hWZ hyW hyZ
                      · have hycomp : y ∈ d.imageᶜ := by
                          rw [←hcoverd]; exact Or.inr hyZ
                        exact hycomp hyd
                    have half_collar (p : Curve S) (T : Set S)
                        (dT : Metric.closedBall (0 : Plane) 1 ≃ₜ closure T)
                        (hTb : ∀ x, (dT x:S) ∈ p.image ↔ ‖x.val‖=1)
                        (hTi : ∀ x, (dT x:S) ∈ T ↔ ‖x.val‖<1)
                        (β : C(Circle,S)) (hβ : Topology.IsEmbedding β)
                        (hβrange : Set.range β = p.image)
                        (hclT : closure T = T ∪ p.image)
                        (ρ : ℝ) (hρpos : 0 < ρ) (hρlt : ρ < 1)
                   :
                        ∃ L : C(Circle × Interval,S),
                          Topology.IsEmbedding L ∧
                          (∀ z, L (z,0) = β z) ∧
                          (∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∈ T) := by
                      have hβcl (z : Circle) : β z ∈ closure T := by
                        rw [hclT]; right; rw [←hβrange]; exact Set.mem_range_self _
                      let k : Circle → Metric.closedBall (0 : Plane) 1 := fun z =>
                        dT.symm ⟨β z,hβcl z⟩
                      have hkcont : Continuous k := dT.symm.continuous.comp
                        (β.continuous.subtype_mk hβcl)
                      have hknorm (z : Circle) : ‖(k z).val‖ = 1 := by
                        apply (hTb (k z)).mp
                        change (dT (dT.symm ⟨β z,hβcl z⟩):S) ∈ p.image
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
                      exact ⟨L,L.continuous.isClosedEmbedding hLinj |>.isEmbedding,hLzero,hLinner⟩
                    let β0 : C(Circle,S) := ⟨fun z => q (z,0),q.continuous.comp
                      (continuous_id.prodMk continuous_const)⟩
                    let β1 : C(Circle,S) := ⟨fun z => q (z,1),q.continuous.comp
                      (continuous_id.prodMk continuous_const)⟩
                    have hβ0 : Topology.IsEmbedding β0 := β0.continuous.isClosedEmbedding
                      (fun z w he => congrArg Prod.fst (hq.injective he)) |>.isEmbedding
                    have hβ1 : Topology.IsEmbedding β1 := β1.continuous.isClosedEmbedding
                      (fun z w he => congrArg Prod.fst (hq.injective he)) |>.isEmbedding
                    obtain ⟨L,hL,hLzero,hLinner⟩ :=
                      half_collar c V dV hVb hVi β0 hβ0 hqc hclV (1/2) (by norm_num) (by norm_num)
                    obtain ⟨R,hR,hRzero,hRinner⟩ :=
                      half_collar d Z dZ hZb hZi β1 hβ1 hqd hclZ (1/2) (by norm_num) (by norm_num)
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
                    have hcqr : c.image ⊆ Set.range q := by
                      intro y hy; obtain ⟨z,hz⟩ := hqc.symm ▸ hy; exact ⟨(z,0),hz⟩
                    have hdqr : d.image ⊆ Set.range q := by
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
                      ((isCompact_range c.embedded.continuous).isClosed.union
                        (isCompact_range d.embedded.continuous).isClosed) hqcomp
                    have hDqr : D ⊆ Set.range q := by
                      rintro y ⟨p,hp,he⟩; exact ⟨p,he⟩
                    have hDext : Disjoint D (V ∪ Z) := by
                      apply Set.disjoint_left.mpr
                      rintro y hyD (hyV | hyZ)
                      · exact Set.disjoint_left.mp hqV (hDqr hyD) hyV
                      · exact Set.disjoint_left.mp hqZ (hDqr hyD) hyZ
                    have hpartition : D ∪ V ∪ Z = (c.image ∪ d.image)ᶜ := by
                      apply Set.Subset.antisymm
                      · rintro y ((hyD | hyV) | hyZ) (hyc | hyd)
                        · exact hqcomp.2.2.1 hyD (Or.inl hyc)
                        · exact hqcomp.2.2.1 hyD (Or.inr hyd)
                        · have hh : y ∈ c.imageᶜ := by rw [←hcoverc]; exact Or.inr hyV
                          exact hh hyc
                        · exact hVavoid hyV hyd
                        · exact Set.disjoint_left.mp hWZ (hcW hyc) hyZ
                        · have hh : y ∈ d.imageᶜ := by rw [←hcoverd]; exact Or.inr hyZ
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
                    exact ⟨U,V,W,Z,hUo,hVo,hWo,hZo,hUc,hVc,hWc,hZc,hUV,hWZ,hVZ,
                      hcoverc,hcoverd,hclU,hclV,hclW,hclZ,hdU,hcW,hqV,hqZ,hB,g,hg,hgmid⟩
            
                have hComponent {X : Type} [TopologicalSpace X] [T2Space X] [ChartedSpace Plane X]
                    (q : C(Circle × Interval,X)) (hq : IsEmbedding q) :
                    IsComplementComponent
                      (Set.range (fun z : Circle => q (z,0)) ∪ Set.range (fun z : Circle => q (z,1)))
                      (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
                  all_goals
                    let C := Set.range (fun z : Circle => q (z,0))
                    let D := Set.range (fun z : Circle => q (z,1))
                    have hq0 : Set.range (fun z : Circle => q (z,0))=C := rfl
                    have hq1 : Set.range (fun z : Circle => q (z,1))=D := rfl
                    let Qmiddle : Set X := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
                    have hQmiddleConnected : IsConnected Qmiddle := by
                      have he : {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}=
                          (Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1 := by ext p;simp
                      change IsConnected (q '' _)
                      rw [he]
                      exact (isConnected_univ.prod (isConnected_Ioo (by norm_num : (0:Interval)<1))).image _
                        q.continuous.continuousOn
                    have hQmiddleAvoid : Qmiddle ⊆ (C ∪ D)ᶜ := by
                      rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩ (hc | hdmem)
                      · obtain ⟨w,hw⟩ := hq0.symm ▸ hc
                        have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
                        change (0:ℝ)=(t:ℝ) at hh
                        linarith
                      · obtain ⟨w,hw⟩ := hq1.symm ▸ hdmem
                        have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
                        change (1:ℝ)=(t:ℝ) at hh
                        linarith
                    have hQmiddleDiff : Qmiddle=Set.range q \ (C ∪ D) := by
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
                      let k : Plane → X := fun x => q (z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1))
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
                    have hQcomponent : IsComplementComponent (C ∪ D) Qmiddle := by
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
                    exact hQcomponent
            
                have hShrink {X : Type} [TopologicalSpace X]
                    (g : C(Circle × Set.Icc (-2:ℝ) 3,X)) (U : Set X) (hU : IsOpen U)
                    (hcentral : ∀ z (t : Set.Icc (-2:ℝ) 3), 0 ≤ (t:ℝ) → (t:ℝ) ≤ 1 → g (z,t)∈U) :
                    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
                      ∀ z (t : Set.Icc (-2:ℝ) 3), -δ ≤ (t:ℝ) → (t:ℝ)≤1+δ → g (z,t)∈U := by
                  all_goals
                    let O := g ⁻¹' U
                    have hO : IsOpen O := hU.preimage g.continuous
                    let K : Set (Set.Icc (-2:ℝ) 3) := {t | 0 ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1}
                    have hK : IsCompact K := by
                      have he : K=(Subtype.val : Set.Icc (-2:ℝ) 3 → ℝ) ⁻¹' Set.Icc 0 1 := rfl
                      rw [he]
                      exact (isClosed_Icc.preimage continuous_subtype_val).isCompact
                    have hcontain : (Set.univ : Set Circle) ×ˢ K ⊆ O := by
                      rintro ⟨z,t⟩ ⟨hz,ht⟩
                      exact hcentral z t ht.1 ht.2
                    obtain ⟨D,V,hD,hV,hall,hKV,hDV⟩ := generalized_tube_lemma
                      (isCompact_univ : IsCompact (Set.univ : Set Circle)) hK hO hcontain
                    let clip : ℝ → Set.Icc (-2:ℝ) 3 := Set.projIcc (-2) 3 (by norm_num)
                    have hclip : Continuous clip := continuous_projIcc
                    have ho : IsOpen (clip ⁻¹' V) := hV.preimage hclip
                    have hi : Set.Icc (0:ℝ) 1 ⊆ clip ⁻¹' V := by
                      intro t ht
                      let t' : Set.Icc (-2:ℝ) 3 := ⟨t,by constructor <;> linarith [ht.1,ht.2]⟩
                      have hc : clip t=t' := Set.projIcc_of_mem (by norm_num) t'.property
                      change clip t∈V
                      rw [hc]
                      exact hKV ht
                    obtain ⟨η,hη,hηV⟩ := isCompact_Icc.exists_cthickening_subset_open ho hi
                    let δ : ℝ := min (η/2) (1/2)
                    have hd : 0 < δ := lt_min (half_pos hη) (by norm_num)
                    have hdη : δ ≤ η := (min_le_left _ _).trans (by linarith)
                    refine ⟨δ,hd,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
                    intro z t ht0 ht1
                    have hthick : (t:ℝ) ∈ cthickening η (Set.Icc (0:ℝ) 1) := by
                      by_cases hlo : (t:ℝ)<0
                      · apply mem_cthickening_of_dist_le (t:ℝ) 0 η (Set.Icc 0 1) (by norm_num)
                        rw [Real.dist_eq,sub_zero,abs_of_neg hlo]
                        linarith
                      · by_cases hup : 1<(t:ℝ)
                        · apply mem_cthickening_of_dist_le (t:ℝ) 1 η (Set.Icc 0 1) (by norm_num)
                          rw [Real.dist_eq,abs_of_pos (by linarith : 0<(t:ℝ)-1)]
                          linarith
                        · exact self_subset_cthickening (Set.Icc (0:ℝ) 1) ⟨le_of_not_gt hlo,le_of_not_gt hup⟩
                    have hv : t∈V := by
                      have hh := hηV hthick
                      change clip (t:ℝ)∈V at hh
                      have hc : clip (t:ℝ)=t := Set.projIcc_of_mem (by norm_num) t.property
                      rwa [hc] at hh
                    exact hDV ⟨hall (Set.mem_univ z),hv⟩
            
                have hCalibrate {X : Type} [TopologicalSpace X] [T2Space X]
                    (g : C(Circle × Set.Icc (-2:ℝ) 3,X)) (hg : IsEmbedding g)
                    (q : C(Circle × Interval,X))
                    (hgiven : ∀ z (t : Set.Icc (-2:ℝ) 3), ∀ ht0 : 0 ≤ (t:ℝ), ∀ ht1 : (t:ℝ)≤1,
                      g (z,t)=q (z,⟨t.val,ht0,ht1⟩))
                    (U : Set X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
                    (hsub : ∀ z (t : Set.Icc (-2:ℝ) 3), -δ ≤ (t:ℝ) → (t:ℝ)≤1+δ → g (z,t)∈U) :
                    ∃ Q : C(Circle × Interval,X), IsEmbedding Q ∧ Set.range Q ⊆ U ∧
                      ∀ z (u : Interval), Q (z,⟨((u:ℝ)+1)/3,by
                        constructor <;> linarith [u.property.1,u.property.2]⟩)=q (z,u) := by
                  all_goals
                    let scale : Interval → ℝ := fun u =>
                      if (u:ℝ)≤1/3 then -δ+3*δ*(u:ℝ)
                      else if (u:ℝ)≤2/3 then 3*(u:ℝ)-1
                      else 1+3*δ*((u:ℝ)-2/3)
                    have hscalebound (u : Interval) : -δ ≤ scale u ∧ scale u ≤ 1+δ := by
                      dsimp [scale]
                      split_ifs <;> constructor <;> nlinarith [u.property.1,u.property.2]
                    have hscalemem (u : Interval) : scale u ∈ Set.Icc (-2:ℝ) 3 := by
                      obtain ⟨h0,h1⟩ := hscalebound u
                      constructor <;> linarith
                    have hc2 : Continuous (fun u : Interval =>
                        if (u:ℝ)≤2/3 then 3*(u:ℝ)-1 else 1+3*δ*((u:ℝ)-2/3)) := by
                      apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
                      intro u hu
                      rw [hu]
                      ring
                    have hscalec : Continuous scale := by
                      apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) hc2.continuousOn
                      intro u hu
                      rw [hu,if_pos (by norm_num : (1/3:ℝ)≤2/3)]
                      ring
                    have hscalemono : StrictMono scale := by
                      intro x y hxy
                      have hxyR : (x:ℝ)<(y:ℝ) := hxy
                      have hs : 0<3*δ*((y:ℝ)-(x:ℝ)) :=
                        mul_pos (mul_pos (by norm_num) hδ) (sub_pos.mpr hxyR)
                      dsimp [scale]
                      split_ifs <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
                    let k : Interval → Set.Icc (-2:ℝ) 3 := fun u => ⟨scale u,hscalemem u⟩
                    let Q : C(Circle × Interval,X) := ⟨fun p => g (p.1,k p.2),
                      g.continuous.comp (continuous_fst.prodMk ((hscalec.subtype_mk _).comp continuous_snd))⟩
                    have hQi : Function.Injective Q := by
                      intro p v he
                      have hh := hg.injective he
                      have hfirst : p.1=v.1 := congrArg (fun p : Circle × Set.Icc (-2:ℝ) 3 => p.1) hh
                      refine Prod.ext hfirst ?_
                      apply hscalemono.injective
                      exact congrArg (fun p : Circle × Set.Icc (-2:ℝ) 3 => (p.2:ℝ)) hh
                    refine ⟨Q,(Q.continuous.isClosedEmbedding hQi).isEmbedding,?_,?_⟩
                    · rintro x ⟨p,rfl⟩
                      exact hsub p.1 (k p.2) (hscalebound p.2).1 (hscalebound p.2).2
                    · intro z u
                      let v : Interval := ⟨((u:ℝ)+1)/3,by constructor <;> linarith [u.property.1,u.property.2]⟩
                      have hkv : scale v=(u:ℝ) := by
                        dsimp [scale,v]
                        split_ifs <;> nlinarith [u.property.1,u.property.2]
                      have h0 : (0:ℝ)≤(k v:ℝ) := by change 0 ≤ scale v;rw [hkv];exact u.property.1
                      have h1 : (k v:ℝ)≤1 := by change scale v≤1;rw [hkv];exact u.property.2
                      change g (z,k v)=q (z,u)
                      rw [hgiven z (k v) h0 h1]
                      congr 1
                      refine Prod.ext rfl ?_
                      exact Subtype.ext hkv
            
                letI : T2Space S := M.sphere.symm.t2Space
                letI : ChartedSpace Plane S := M.sphere.symm.chartedSpace
                have hd : Disjoint c.image d.image := by
                  rw [←hqc,←hqd]
                  apply Set.disjoint_left.mpr
                  rintro x ⟨z,rfl⟩ ⟨w,hw⟩
                  have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
                  norm_num at hh
                have hcomp : IsComplementComponent (c.image ∪ d.image)
                    (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
                  rw [←hqc,←hqd];exact hComponent q hq
                obtain ⟨V,W,Z,T,hV,hW,hZ,hT,hcV,hcW,hcZ,hcT,hVW,hZT,hWT,
                  hVWc,hZTd,hclV,hclW,hclZ,hclT,hdV,hcZ,hqW,hqT,hcover,g,hg,hgiven⟩ :=
                  hPartition M c d hd q hq hqc hqd hcomp
                have hcentral : ∀ z (t : Set.Icc (-2:ℝ) 3), 0≤(t:ℝ) → (t:ℝ)≤1 → g (z,t)∈U := by
                  intro z t ht0 ht1
                  rw [hgiven (z,t) ht0 ht1]
                  exact hsub ⟨(z,⟨t.val,ht0,ht1⟩),rfl⟩
                obtain ⟨δ,hδ,hδ1,hgU⟩ := hShrink g U hU hcentral
                obtain ⟨Q,hQ,hQU,hQold⟩ := hCalibrate g hg q
                  (fun z t ht0 ht1 => hgiven (z,t) ht0 ht1) U δ hδ hδ1 hgU
                have hQ0 : Set.range (fun z : Circle => Q (z,⟨1/3,by norm_num⟩))=c.image := by
                  rw [←hqc]
                  apply congrArg Set.range
                  funext z
                  simpa using hQold z 0
                have hQ1 : Set.range (fun z : Circle => Q (z,⟨2/3,by norm_num⟩))=d.image := by
                  rw [←hqd]
                  apply congrArg Set.range
                  funext z
                  have hh := hQold z 1
                  norm_num at hh
                  exact hh
                exact ⟨Q,hQ,hQU,hQ0,hQ1⟩
            let U := Φ '' (Set.univ ×ˢ Set.Ioo a d)
            have hU : IsOpen U := hOpenBand Φ hΦ a d
            have hqU : Set.range q ⊆ U := by
              rintro x ⟨p,rfl⟩
              exact ⟨R p,hsub ⟨p,rfl⟩,hmatch p⟩
            let cS : Curve S := ⟨fun z => q (z,0),hq.comp (isEmbedding_prodMkLeft 0)⟩
            let dS : Curve S := ⟨fun z => q (z,1),hq.comp (isEmbedding_prodMkLeft 1)⟩
            obtain ⟨P,hP,hPU,hP0,hP1⟩ := hCollar M cS dS q hq rfl rfl U hU hqU
            let idC : C(Circle × Interval,Circle × Interval) := ContinuousMap.id _
            have hPconf : Set.range P ⊆ Set.range (Φ.comp idC) := by
              rintro x ⟨p,rfl⟩
              obtain ⟨v,hv,he⟩ := hPU ⟨p,rfl⟩
              exact ⟨v,he⟩
            obtain ⟨T,Q,hT,hQ,hΦT,hQT,hTrange,hTmatch⟩ :=
              actual_confined_cylinder_coordinate_transport Φ hΦ idC P hP hPconf B hB
            have hTsub : Set.range T ⊆ Set.univ ×ˢ Set.Ioo a d := by
              rintro x ⟨p,rfl⟩
              obtain ⟨v,hv,he⟩ := hPU ⟨p,rfl⟩
              have heT : T p=v := hΦ.injective ((hΦT p).trans he.symm)
              rw [heT]
              exact hv
            have hQsub : Set.range Q ⊆ B '' (Set.univ ×ˢ Set.Ioo a d) := by
              rintro x ⟨p,rfl⟩
              exact ⟨T p,hTsub ⟨p,rfl⟩,(hQT p).symm⟩
            have hLevel (v u : Interval)
                (hlevel : Set.range (fun z : Circle => P (z,v))=
                  Set.range (fun z : Circle => q (z,u))) :
                Set.range (fun z : Circle => Q (z,v))=
                  Set.range (fun z : Circle => B (R (z,u))) := by
              ext x; constructor
              · rintro ⟨z,rfl⟩
                have hm : P (z,v)∈Set.range (fun z : Circle => q (z,u)) := hlevel ▸ ⟨z,rfl⟩
                obtain ⟨w,hw⟩ := hm
                refine ⟨w,?_⟩
                change B (R (w,u))=Q (z,v)
                rw [hQT]
                exact congrArg B (hΦ.injective (((hmatch (w,u)).trans hw).trans (hΦT (z,v)).symm))
              · rintro ⟨w,rfl⟩
                have hm : q (w,u)∈Set.range (fun z : Circle => P (z,v)) := hlevel.symm ▸ ⟨w,rfl⟩
                obtain ⟨z,hz⟩ := hm
                refine ⟨z,?_⟩
                change Q (z,v)=B (R (w,u))
                rw [hQT]
                exact congrArg B (hΦ.injective (((hΦT (z,v)).trans hz).trans (hmatch (w,u)).symm))
            let cE : Curve E := ⟨fun z => B (R (z,0)),(hB.comp hR).comp (isEmbedding_prodMkLeft 0)⟩
            let dE : Curve E := ⟨fun z => B (R (z,1)),(hB.comp hR).comp (isEmbedding_prodMkLeft 1)⟩
            have hQ0 : Set.range (fun z : Circle => Q (z,⟨1/3,by norm_num⟩))=cE.image :=
              hLevel ⟨1/3,by norm_num⟩ 0 hP0
            have hQ1 : Set.range (fun z : Circle => Q (z,⟨2/3,by norm_num⟩))=dE.image :=
              hLevel ⟨2/3,by norm_num⟩ 1 hP1
            have hopen : IsOpen (Q '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := hOpenBand Q hQ 0 1
            obtain ⟨H,J,hfinal,hfix,hleft,hright⟩ :=
              CurveComplex.G3Review.actual_collared_annulus_ambient_alignment cE dE Q hQ hQ0 hQ1 hopen
            refine ⟨H,hfinal,?_⟩
            intro t x hx
            apply hfix t x
            intro hmem
            exact hx (hQsub (Set.image_subset_range _ _ hmem))
        have hSide (R : C(Circle × Interval,Circle × Interval))
            (havoid : ∀ p, ((R p).2:ℝ) ≠ 1/2) :
            (∀ p, ((R p).2:ℝ) < 1/2) ∨ (∀ p, 1/2 < ((R p).2:ℝ)) := by
          all_goals
            let L : Set (Circle × Interval) := {p | (p.2:ℝ)<1/2}
            let U : Set (Circle × Interval) := {p | 1/2<(p.2:ℝ)}
            have hL : IsOpen L := isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
            have hU : IsOpen U := isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
            have hLU : Disjoint L U := Set.disjoint_left.mpr (by
              intro p hp hq
              change (p.2:ℝ)<1/2 at hp
              change 1/2<(p.2:ℝ) at hq
              exact (lt_asymm hp hq))
            have hsub : Set.range R ⊆ L ∪ U := by
              rintro p ⟨v,rfl⟩
              rcases lt_or_gt_of_ne (havoid v) with h | h
              · exact Or.inl h
              · exact Or.inr h
            have hc := (isConnected_range R.continuous).isPreconnected
            rcases hc.subset_or_subset hL hU hLU hsub with hl | hu
            · exact Or.inl (fun p => hl ⟨p,rfl⟩)
            · exact Or.inr (fun p => hu ⟨p,rfl⟩)
        obtain ⟨ε,hε,hεq,Φ,q,hΦ,hq,hq0,hq1,hconf,hcoreAvoid⟩ :=
          actual_given_core_confined_comparison_source M G hGe r hcore b hside
        obtain ⟨R,Q,hR,hQ,hΦR,hQR,hRrange,hRmatch⟩ :=
          actual_confined_cylinder_coordinate_transport Φ hΦ G q hq hconf B hB
        have hRproper : Set.range R ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) 1 :=
          hRrange.trans hproper
        have hRavoid : ∀ p, ((R p).2:ℝ) ≠ 1/2 := by
          intro p hp
          have hheight : (R p).2=(⟨1/2,by norm_num⟩:Interval) := Subtype.ext hp
          have hpoint : R p=((R p).1,⟨1/2,by norm_num⟩) := Prod.ext rfl hheight
          apply Set.disjoint_left.mp hcoreAvoid ⟨p,rfl⟩
          refine ⟨(R p).1,?_⟩
          rw [←hΦR,hpoint]
        let u : Interval := ⟨1/2+(if b then ε else -ε),by
          cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith⟩
        have hNearWitness : ∃ z : Circle, ((R (z,1)).2:ℝ)=(u:ℝ) := by
          have hm : Φ (1,u)∈Set.range (fun z : Circle => q (z,1)) := hq1.symm ▸ ⟨1,rfl⟩
          obtain ⟨z,hz⟩ := hm
          have he : R (z,1)=(1,u) := hΦ.injective ((hΦR (z,1)).trans hz)
          exact ⟨z,congrArg (fun p : Circle × Interval => (p.2:ℝ)) he⟩
        have hOld : Set.range (fun z : Circle => B (R (z,0)))=
            Set.range (fun z : Circle => B (G (z,0))) := by
          ext x;constructor
          · rintro ⟨z,rfl⟩
            have hm : q (z,0)∈Set.range (fun z : Circle => Φ (G (z,0))) := hq0 ▸ ⟨z,rfl⟩
            obtain ⟨v,hv⟩ := hm
            exact ⟨v,congrArg B (hRmatch (z,0) (v,0) hv).symm⟩
          · rintro ⟨v,rfl⟩
            have hm : Φ (G (v,0))∈Set.range (fun z : Circle => q (z,0)) := hq0.symm ▸ ⟨v,rfl⟩
            obtain ⟨z,hz⟩ := hm
            exact ⟨z,congrArg B (hRmatch (z,0) (v,0) hz.symm)⟩
        have hNear : Set.range (fun z : Circle => B (R (z,1)))=
            Set.range (fun z : Circle => B (z,u)) := by
          ext x;constructor
          · rintro ⟨z,rfl⟩
            have hm : q (z,1)∈Set.range (fun z : Circle => Φ (z,u)) := hq1 ▸ ⟨z,rfl⟩
            obtain ⟨v,hv⟩ := hm
            exact ⟨v,congrArg B (hΦ.injective (hv.trans (hΦR (z,1)).symm))⟩
          · rintro ⟨v,rfl⟩
            have hm : Φ (v,u)∈Set.range (fun z : Circle => q (z,1)) := hq1.symm ▸ ⟨v,rfl⟩
            obtain ⟨z,hz⟩ := hm
            exact ⟨z,congrArg B (hΦ.injective ((hΦR (z,1)).trans hz))⟩
        obtain ⟨z,hz⟩ := hNearWitness
        cases b
        · have hLow : ∀ p, ((R p).2:ℝ)<1/2 := by
            rcases hSide R hRavoid with hl | hu
            · exact hl
            · have hh := hu (z,1)
              dsimp [u] at hz
              linarith
          have hband : Set.range R ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) ⟨1/2,by norm_num⟩ := by
            rintro x ⟨p,rfl⟩
            exact ⟨Set.mem_univ _,(hRproper ⟨p,rfl⟩).2.1,hLow p⟩
          obtain ⟨H,hfinal,hfix⟩ := hMotion M Φ hΦ R hR q hq hΦR 0 ⟨1/2,by norm_num⟩ hband B hB
          refine ⟨ε,hε,hεq,H,?_,?_⟩
          · rw [hOld,hNear] at hfinal
            exact hfinal
          · simpa only [Bool.false_eq_true,ite_false] using hfix
        · have hHigh : ∀ p, 1/2<((R p).2:ℝ) := by
            rcases hSide R hRavoid with hl | hu
            · have hh := hl (z,1)
              dsimp [u] at hz
              linarith
            · exact hu
          have hband : Set.range R ⊆ Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1 := by
            rintro x ⟨p,rfl⟩
            exact ⟨Set.mem_univ _,hHigh p,(hRproper ⟨p,rfl⟩).2.2⟩
          obtain ⟨H,hfinal,hfix⟩ := hMotion M Φ hΦ R hR q hq hΦR ⟨1/2,by norm_num⟩ 1 hband B hB
          refine ⟨ε,hε,hεq,H,?_,?_⟩
          · rw [hOld,hNear] at hfinal
            exact hfinal
          · simpa only [ite_true] using hfix
    have hFinish (M : HyperellipticModel E S) (V : Set E) (T : Circle × Interval ≃ₜ V)
        (L₀ U₀ : Set E) (δL δR : ℝ)
        (hδL : 0 < δL) (hδLq : δL < 1/4) (hδR : 0 < δR) (hδRq : δR < 1/4)
        (HL HR : AmbientIsotopy E)
        (hLf : HL.finalMap '' L₀=Set.range (fun z : Circle =>
          (T (z,⟨1/2-δL,by constructor <;> linarith⟩)).val))
        (hRf : HR.finalMap '' U₀=Set.range (fun z : Circle =>
          (T (z,⟨1/2+δR,by constructor <;> linarith⟩)).val))
        (hLfix : ∀ t x, x∉(fun p : Circle × Interval => (T p).val) ''
          (Set.univ ×ˢ Set.Ioo (0:Interval) ⟨1/2,by norm_num⟩) → HL.map (t,x)=x)
        (hRfix : ∀ t x, x∉(fun p : Circle × Interval => (T p).val) ''
          (Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1) → HR.map (t,x)=x)
        (hU₀ : U₀ ⊆ (fun p : Circle × Interval => (T p).val) ''
          (Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1)) :
        AmbientIsotopy.Rel (L₀ ∪ U₀)
          (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
            Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val)) := by
      all_goals
        have hCombine (L U a₀ a₁ b₀ b₁ : Set E) (hLU : Disjoint L U)
            (ha₁ : a₁ ⊆ L) (hb₀ : b₀ ⊆ U)
            (H₀ H₁ : AmbientIsotopy E)
            (h₀ : H₀.finalMap '' a₀=a₁) (h₁ : H₁.finalMap '' b₀=b₁)
            (hfix₀ : ∀ t x, x∉L → H₀.map (t,x)=x)
            (hfix₁ : ∀ t x, x∉U → H₁.map (t,x)=x) :
            AmbientIsotopy.Rel (a₀ ∪ b₀) (a₁ ∪ b₁) := by
          all_goals
            have hFixImage (H : AmbientIsotopy E) (D : Set E)
                (hD : ∀ x ∈ D, H.finalMap x=x) : H.finalMap '' D=D := by
              ext x; constructor
              · rintro ⟨y,hy,rfl⟩
                simpa only [hD y hy] using hy
              · intro hx
                exact ⟨x,hx,hD x hx⟩
            have hfixedB : H₀.finalMap '' b₀=b₀ := hFixImage H₀ b₀ (by
              intro x hx
              change H₀.map (1,x)=x
              apply hfix₀
              intro hxL
              exact Set.disjoint_left.mp hLU hxL (hb₀ hx))
            have hfixedA : H₁.finalMap '' a₁=a₁ := hFixImage H₁ a₁ (by
              intro x hx
              change H₁.map (1,x)=x
              apply hfix₁
              intro hxU
              exact Set.disjoint_left.mp hLU (ha₁ hx) hxU)
            have hfirst : AmbientIsotopy.Rel (a₀ ∪ b₀) (a₁ ∪ b₀) := by
              refine ⟨H₀,?_⟩
              rw [Set.image_union,h₀,hfixedB]
            have hsecond : AmbientIsotopy.Rel (a₁ ∪ b₀) (a₁ ∪ b₁) := by
              refine ⟨H₁,?_⟩
              rw [Set.image_union,hfixedA,h₁]
            exact ambientIsotopy_equivalence.trans hfirst hsecond
        have hAsym (M : HyperellipticModel E S) (U : Set E)
            (T : Circle × Interval ≃ₜ U) (δL δR : ℝ) (hδL : 0 < δL) (hδLq : δL < 1/4) (hδR : 0 < δR) (hδRq : δR < 1/4) :
            ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
              H.finalMap ''
                (Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
                  Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val)) =
                Set.range (fun z : Circle => (T (z,⟨1/2-δL,by constructor <;> linarith⟩)).val) ∪
                  Set.range (fun z : Circle => (T (z,⟨1/2+δR,by constructor <;> linarith⟩)).val) ∧
              (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
                (T (z,⟨1/2,by norm_num⟩)).val) ∧
              (∀ t x, x ∉ U → H.map (t,x) = x) ∧
              (∀ t x, J (t,H.map (t,x)) = x) ∧
              (∀ t x, H.map (t,J (t,x)) = x) := by
          all_goals
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            have actual_embedded_annulus_interior_isOpen
                (B : Circle × Interval → E) (hB : IsEmbedding B) :
                IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
              rw [isOpen_iff_forall_mem_open]
              rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
              have hu0 : (0:ℝ) < (u : ℝ) := hu.1
              have hu1 : (u : ℝ) < 1 := hu.2
              let lo : ℝ := (u : ℝ)/2
              let hi : ℝ := ((u : ℝ)+1)/2
              have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
              have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
              have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
              have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
              have hlh : lo ≤ hi := (hlu.trans huh).le
              let width : ℝ → Interval := fun s =>
                ⟨(Set.projIcc lo hi hlh s : ℝ),
                  ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                    le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
              have hwc : Continuous width :=
                (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
              let θ := Complex.arg (z : ℂ)
              let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
              have hfc : Continuous f := hB.continuous.comp
                ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
              let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
                {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
              have hΩ : IsOpen Ω :=
                (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
              have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                  (width (x 0) : ℝ) = x 0 :=
                congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
              have hfi : Set.InjOn f Ω := by
                intro x hx w hw he
                have hp := hB.injective he
                have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                  (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                  ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
                have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
                change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
                rw [hclip x hx,hclip w hw] at hwidth
                ext i
                fin_cases i
                · exact hwidth
                · exact hangle
              have hopen : IsOpen (f '' Ω) :=
                CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
              have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
                rintro q ⟨x,hx,rfl⟩
                refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
                · change 0 < (width (x 0) : ℝ)
                  rw [hclip x hx]
                  exact hl0.trans hx.1.1
                · change (width (x 0) : ℝ) < 1
                  rw [hclip x hx]
                  exact hx.1.2.trans hh1
              let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
              have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
              have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
              have hx : x ∈ Ω := by
                refine ⟨?_,?_⟩
                · rw [hx0]; exact ⟨hlu,huh⟩
                · rw [hx1]; constructor <;> linarith [Real.pi_pos]
              have hwu : width (u : ℝ) = u := by
                apply Subtype.ext
                change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
                exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
              have hpoint : f x = B (z,u) := by
                dsimp [f]
                rw [hx0,hx1,hwu,Circle.exp_arg]
              exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
            have hCalibration (b : ℝ) (hb0 : 1/2 < b) (hb1 : b < 1) :
                ∃ h : Interval ≃ₜ Interval,
                  h 0 = 0 ∧ h 1 = 1 ∧
                  h ⟨1/3,by norm_num⟩ = ⟨1/2,by norm_num⟩ ∧
                  (h ⟨2/3,by norm_num⟩ : ℝ) = b := by
              all_goals
                let f : Interval → ℝ := fun u =>
                  if (u:ℝ) ≤ 1/3 then 3*(u:ℝ)/2
                  else if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
                  else b+3*(1-b)*((u:ℝ)-2/3)
                have hfmem (u : Interval) : f u ∈ Set.Icc (0:ℝ) 1 := by
                  dsimp [f]
                  split_ifs <;> constructor <;> nlinarith [u.property.1,u.property.2]
                have hc2 : Continuous (fun u : Interval =>
                    if (u:ℝ) ≤ 2/3 then 1/2+3*(b-1/2)*((u:ℝ)-1/3)
                    else b+3*(1-b)*((u:ℝ)-2/3)) := by
                  apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
                  intro u hu
                  rw [hu]
                  ring
                have hfc : Continuous f := by
                  apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) hc2.continuousOn
                  intro u hu
                  rw [hu,if_pos (by norm_num : (1/3:ℝ) ≤ 2/3)]
                  ring
                have hmono : StrictMono f := by
                  intro x y hxy
                  have hxyR : (x:ℝ) < (y:ℝ) := hxy
                  have hcentral : 0 < 3*(b-1/2)*((y:ℝ)-(x:ℝ)) :=
                    mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb0)) (sub_pos.mpr hxyR)
                  have houter : 0 < 3*(1-b)*((y:ℝ)-(x:ℝ)) :=
                    mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb1)) (sub_pos.mpr hxyR)
                  dsimp [f]
                  split_ifs <;> nlinarith [x.property.1,x.property.2,y.property.1,y.property.2]
                let F : Interval → Interval := fun u => ⟨f u,hfmem u⟩
                have hFc : Continuous F := hfc.subtype_mk _
                have hF0 : F 0 = 0 := Subtype.ext (by norm_num [F,f])
                have hF1 : F 1 = 1 := Subtype.ext (by norm_num [F,f]; ring)
                have hFs : Function.Surjective F := by
                  have hconn := (isConnected_range hFc).isPreconnected.ordConnected
                  intro u
                  exact hconn.out ⟨0,hF0⟩ ⟨1,hF1⟩ u.property
                have hFi : Function.Injective F := by
                  intro x y hxy
                  exact hmono.injective (congrArg Subtype.val hxy)
                let h : Interval ≃ₜ Interval :=
                  (Equiv.ofBijective F ⟨hFi,hFs⟩).toHomeomorphOfContinuousClosed hFc hFc.isClosedMap
                refine ⟨h,hF0,hF1,?_,?_⟩
                · apply Subtype.ext
                  change f ⟨1/3,by norm_num⟩ = 1/2
                  norm_num [f]
                · change f ⟨2/3,by norm_num⟩ = b
                  norm_num [f]
                  ring
            obtain ⟨kL,hkL0,hkL1,hkLthird,hkLtwo⟩ := hCalibration (1-2*δL) (by linarith) (by linarith)
            obtain ⟨kR,hkR0,hkR1,hkRthird,hkRtwo⟩ := hCalibration (1-2*δR) (by linarith) (by linarith)
            have hkInterior (k : Interval ≃ₜ Interval) (hk0 : k 0=0) (hk1 : k 1=1) (u : Interval) (hu : u ∈ Set.Ioo (0:Interval) 1) : k u ∈ Set.Ioo (0:Interval) 1 := by
              constructor
              · apply lt_of_le_of_ne (k u).property.1
                intro he
                have heI : k u = 0 := Subtype.ext he.symm
                have hh := k.injective (heI.trans hk0.symm)
                subst u
                exact (lt_irrefl (0:Interval)) hu.1
              · apply lt_of_le_of_ne (k u).property.2
                intro he
                have heI : k u = 1 := Subtype.ext he
                have hh := k.injective (heI.trans hk1.symm)
                subst u
                exact (lt_irrefl (1:Interval)) hu.2
            let L : Circle × Interval → E := fun p =>
              (T (p.1,⟨(kL p.2 : ℝ)/2,by constructor <;> linarith [(kL p.2).property.1,(kL p.2).property.2]⟩)).val
            let R : Circle × Interval → E := fun p =>
              (T (p.1,⟨1-(kR p.2 : ℝ)/2,by constructor <;> linarith [(kR p.2).property.1,(kR p.2).property.2]⟩)).val
            have hLc : Continuous L := by dsimp [L]; fun_prop
            have hRc : Continuous R := by dsimp [R]; fun_prop
            have hLi : Function.Injective L := by
              intro p q he
              have hh := T.injective (Subtype.ext he)
              apply Prod.ext
              · have hx := congrArg (fun x : Circle × Interval => x.1) hh
                exact hx
              · apply Subtype.ext
                have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
                change (kL p.2 : ℝ)/2 = (kL q.2 : ℝ)/2 at hc
                exact congrArg Subtype.val (kL.injective (Subtype.ext (by linarith)))
            have hRi : Function.Injective R := by
              intro p q he
              have hh := T.injective (Subtype.ext he)
              apply Prod.ext
              · have hx := congrArg (fun x : Circle × Interval => x.1) hh
                exact hx
              · apply Subtype.ext
                have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
                change 1-(kR p.2 : ℝ)/2 = 1-(kR q.2 : ℝ)/2 at hc
                exact congrArg Subtype.val (kR.injective (Subtype.ext (by linarith)))
            have hL : Topology.IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
            have hR : Topology.IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
            let UL := L '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
            let UR := R '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
            have hUL : IsOpen UL := actual_embedded_annulus_interior_isOpen L hL
            have hUR : IsOpen UR := actual_embedded_annulus_interior_isOpen R hR
            obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := CurveComplex.G3Review.actual_circle_band_ambient_motion
            have hfixL (t : Interval) (y : Circle × Interval) (hy : L y ∉ UL) : K.map (t,y) = y := by
              by_cases hy0 : y.2 = 0
              · rw [show y = (y.1,0) from Prod.ext rfl hy0]
                exact hzero t y.1
              by_cases hy1 : y.2 = 1
              · rw [show y = (y.1,1) from Prod.ext rfl hy1]
                exact hone t y.1
              have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
              have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
              exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
            have hfixR (t : Interval) (y : Circle × Interval) (hy : R y ∉ UR) : K.map (t,y) = y := by
              by_cases hy0 : y.2 = 0
              · rw [show y = (y.1,0) from Prod.ext rfl hy0]
                exact hzero t y.1
              by_cases hy1 : y.2 = 1
              · rw [show y = (y.1,1) from Prod.ext rfl hy1]
                exact hone t y.1
              have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
              have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
              exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
            obtain ⟨HL,JL,hHL,hLout,hJLleft,hJLright⟩ :=
              CurveComplex.G3Review.actual_compact_embedded_motion_extension L hL UL hUL
                (Set.image_subset_range _ _) K V hleft hright hfixL
            obtain ⟨HR,JR,hHR,hRout,hJRleft,hJRright⟩ :=
              CurveComplex.G3Review.actual_compact_embedded_motion_extension R hR UR hUR
                (Set.image_subset_range _ _) K V hleft hright hfixR
            have hLow (z : Circle) (u : Interval) (hu : (u : ℝ) ≤ 1/2) : (T (z,u)).val ∉ UR := by
              rintro ⟨p,⟨_,hp⟩,he⟩
              have hh := T.injective (Subtype.ext he)
              have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
              change 1-(kR p.2 : ℝ)/2 = (u : ℝ) at hc
              have hp1 : (kR p.2 : ℝ) < 1 := (hkInterior kR hkR0 hkR1 p.2 hp).2
              linarith
            have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
              rintro ⟨p,⟨_,hp⟩,he⟩
              have hh := T.injective (Subtype.ext he)
              have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
              change (kL p.2 : ℝ)/2 = (u : ℝ) at hc
              have hp1 : (kL p.2 : ℝ) < 1 := (hkInterior kL hkL0 hkL1 p.2 hp).2
              linarith
            let H : AmbientIsotopy E := {
              map := ⟨fun p => HR.map (p.1,HL.map (p.1,p.2)),HR.map.continuous.comp
                (continuous_fst.prodMk (HL.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
              homeomorphism_at := by
                intro t
                obtain ⟨l,hl⟩ := HL.homeomorphism_at t
                obtain ⟨r,hr⟩ := HR.homeomorphism_at t
                exact ⟨l.trans r,fun x => by change r (l x) = HR.map (t,HL.map (t,x)); rw [hl,hr]⟩
              at_zero := by
                intro x
                change HR.map (⟨0,by norm_num⟩,HL.map (⟨0,by norm_num⟩,x)) = x
                rw [HL.at_zero,HR.at_zero] }
            let J : C(Interval × E,E) := ⟨fun p => JL (p.1,JR (p.1,p.2)),JL.continuous.comp
              (continuous_fst.prodMk (JR.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
            have hLf (z : Circle) : HL.finalMap (T (z,⟨1/4,by norm_num⟩)).val =
                (T (z,⟨1/2-δL,by constructor <;> linarith⟩)).val := by
              have h := hHL 1 (z,⟨1/3,by norm_num⟩)
              have hk := hfinal z
              change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
              rw [hk] at h
              norm_num [AmbientIsotopy.finalMap,L,hkLthird,hkLtwo] at h ⊢
              have heq : (1-2*δL)/2 = 1/2-δL := by ring
              simpa only [heq] using h
            have hRf (z : Circle) : HR.finalMap (T (z,⟨3/4,by norm_num⟩)).val =
                (T (z,⟨1/2+δR,by constructor <;> linarith⟩)).val := by
              have h := hHR 1 (z,⟨1/3,by norm_num⟩)
              have hk := hfinal z
              change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
              rw [hk] at h
              norm_num [AmbientIsotopy.finalMap,R,hkRthird,hkRtwo] at h ⊢
              have heq : 1-(1-2*δR)/2 = 1/2+δR := by ring
              simpa only [heq] using h
            have hHfL (z : Circle) : H.finalMap (T (z,⟨1/4,by norm_num⟩)).val =
                (T (z,⟨1/2-δL,by constructor <;> linarith⟩)).val := by
              change HR.finalMap (HL.finalMap _) = _
              rw [hLf]
              exact hRout 1 _ (hLow z _ (by change (1/2-δL:ℝ) ≤ 1/2; linarith))
            have hHfR (z : Circle) : H.finalMap (T (z,⟨3/4,by norm_num⟩)).val =
                (T (z,⟨1/2+δR,by constructor <;> linarith⟩)).val := by
              change HR.finalMap (HL.finalMap _) = _
              rw [show HL.finalMap (T (z,⟨3/4,by norm_num⟩)).val = (T (z,⟨3/4,by norm_num⟩)).val from
                hLout 1 _ (hHigh z _ (by change (1/2:ℝ) ≤ 3/4; norm_num))]
              exact hRf z
            refine ⟨H,J,?_,?_,?_,?_,?_⟩
            · rw [Set.image_union,← Set.range_comp,← Set.range_comp]
              exact congrArg₂ Set.union (congrArg Set.range (funext hHfL)) (congrArg Set.range (funext hHfR))
            · intro t z
              change HR.map (t,HL.map (t,_)) = _
              rw [hLout t _ (hHigh z _ (by norm_num)),hRout t _ (hLow z _ (by norm_num))]
            · intro t x hx
              have hxL : x ∉ UL := by
                rintro ⟨p,hp,rfl⟩
                exact hx (T _).property
              have hxR : x ∉ UR := by
                rintro ⟨p,hp,rfl⟩
                exact hx (T _).property
              change HR.map (t,HL.map (t,x)) = x
              rw [hLout t x hxL,hRout t x hxR]
            · intro t x
              change JL (t,JR (t,HR.map (t,HL.map (t,x)))) = x
              rw [hJRleft,hJLleft]
            · intro t x
              change HR.map (t,HL.map (t,JL (t,JR (t,x)))) = x
              rw [hJLright,hJRright]
        let L := (fun p : Circle × Interval => (T p).val) ''
          (Set.univ ×ˢ Set.Ioo (0:Interval) ⟨1/2,by norm_num⟩)
        let U := (fun p : Circle × Interval => (T p).val) ''
          (Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1)
        let L₁ := Set.range (fun z : Circle => (T (z,⟨1/2-δL,by constructor <;> linarith⟩)).val)
        let U₁ := Set.range (fun z : Circle => (T (z,⟨1/2+δR,by constructor <;> linarith⟩)).val)
        have hLU : Disjoint L U := by
          apply Set.disjoint_left.mpr
          rintro x ⟨p,hp,rfl⟩ ⟨q,hq,he⟩
          have hqp : q=p := T.injective (Subtype.ext he)
          subst q
          exact lt_asymm hp.2.2 hq.2.1
        have hL₁ : L₁ ⊆ L := by
          rintro x ⟨z,rfl⟩
          refine ⟨(z,⟨1/2-δL,by constructor <;> linarith⟩),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
          · change (0:ℝ)<1/2-δL;linarith
          · change 1/2-δL<(1/2:ℝ);linarith
        have hpair : AmbientIsotopy.Rel (L₀ ∪ U₀) (L₁ ∪ U₁) :=
          hCombine L U L₀ L₁ U₀ U₁ hLU hL₁ hU₀ HL HR hLf hRf hLfix hRfix
        obtain ⟨K,J,hK,hcore,houtside,hleft,hright⟩ :=
          hAsym M V T δL δR hδL hδLq hδR hδRq
        exact ambientIsotopy_equivalence.trans hpair (ambientIsotopy_equivalence.symm ⟨K,hK⟩)
    let BActual : C(Circle × Interval,E) := ⟨fun p => (B p).val,
      continuous_subtype_val.comp B.continuous⟩
    have hBActual : IsEmbedding BActual := IsEmbedding.subtypeVal.comp B.isEmbedding
    let ρ : C(Circle × Interval,Circle × Interval) :=
      ⟨fun p => (p.1,⟨1-(p.2:ℝ),by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩),by fun_prop⟩
    have hρ (p : Circle × Interval) : ρ (ρ p)=p := by
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change 1-(1-(p.2:ℝ))=(p.2:ℝ)
      ring
    have hρe : IsEmbedding ρ := (ρ.continuous.isClosedEmbedding
      (Function.LeftInverse.injective hρ)).isEmbedding
    let GTop := G.comp ρ
    have hGTop : IsEmbedding GTop := hGe.comp hρe
    have hGTop0 (z : Circle) : GTop (z,0)=G (z,1) := by
      change G (z,⟨1-(0:ℝ),_⟩)=G (z,1)
      congr 1
      refine Prod.ext rfl ?_;apply Subtype.ext;norm_num
    have hGTopCore : ∀ z, GTop (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩) := by
      intro z
      have hc : ρ (z,⟨1/2,by norm_num⟩)=(z,⟨1/2,by norm_num⟩) := by
        refine Prod.ext rfl ?_;apply Subtype.ext;norm_num [ρ]
      change G (ρ (z,⟨1/2,_⟩))=(r z,⟨1/2,_⟩)
      rw [hc,hcore]
    have hGTopProper : Set.range GTop ⊆ Set.univ ×ˢ Set.Ioo (0:Interval) 1 := by
      rintro x ⟨p,rfl⟩
      exact hproper ⟨ρ p,rfl⟩
    change AmbientIsotopy.Rel
      (Set.range (fun z : Circle => BActual (G (z,0))) ∪
        Set.range (fun z : Circle => BActual (G (z,1))))
      (Set.range (fun z : Circle => (B (z,⟨1/4,by norm_num⟩)).val) ∪
        Set.range (fun z : Circle => (B (z,⟨3/4,by norm_num⟩)).val))
    rcases hSides with hs | hs
    · obtain ⟨δL,hδL,hδLq,HL,hLf,hLfix⟩ := hMove M G hGe r hcore false
        (by simpa using hs.2) hproper BActual hBActual
      have hTopSide : ∀ z (u : Interval), 1/2<(u:ℝ) →
          ((GTop (z,u)).2:ℝ)<1/2 := by
        intro z u hu
        exact hs.1 z (ρ (z,u)).2 (by change 1-(u:ℝ)<1/2;linarith)
      obtain ⟨δR,hδR,hδRq,HR,hRf,hRfix⟩ := hMove M GTop hGTop r hGTopCore true
        (by simpa using hTopSide) hGTopProper BActual hBActual
      simp only [Bool.false_eq_true,ite_false,sub_eq_add_neg] at hLf hLfix
      simp only [ite_true] at hRf hRfix
      have hOldHigh : Set.range (fun z : Circle => BActual (GTop (z,0))) ⊆
          BActual '' (Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1) := by
        rintro x ⟨z,rfl⟩
        change BActual (GTop (z,0)) ∈ _
        rw [hGTop0]
        refine ⟨G (z,1),⟨Set.mem_univ _,?_,(hproper ⟨(z,1),rfl⟩).2.2⟩,rfl⟩
        exact hs.2 z 1 (by norm_num)
      have hpair := hFinish M V B
        (Set.range (fun z : Circle => BActual (G (z,0))))
        (Set.range (fun z : Circle => BActual (GTop (z,0))))
        δL δR hδL hδLq hδR hδRq HL HR hLf hRf hLfix hRfix hOldHigh
      simpa only [hGTop0] using hpair
    · have hTopSide : ∀ z (u : Interval), 1/2<(u:ℝ) →
          1/2<((GTop (z,u)).2:ℝ) := by
        intro z u hu
        exact hs.1 z (ρ (z,u)).2 (by change 1-(u:ℝ)<1/2;linarith)
      obtain ⟨δL,hδL,hδLq,HL,hLf,hLfix⟩ := hMove M GTop hGTop r hGTopCore false
        (by simpa using hTopSide) hGTopProper BActual hBActual
      obtain ⟨δR,hδR,hδRq,HR,hRf,hRfix⟩ := hMove M G hGe r hcore true
        (by simpa using hs.2) hproper BActual hBActual
      simp only [Bool.false_eq_true,ite_false,sub_eq_add_neg] at hLf hLfix
      simp only [ite_true] at hRf hRfix
      have hOldHigh : Set.range (fun z : Circle => BActual (G (z,0))) ⊆
          BActual '' (Set.univ ×ˢ Set.Ioo (⟨1/2,by norm_num⟩:Interval) 1) := by
        rintro x ⟨z,rfl⟩
        refine ⟨G (z,0),⟨Set.mem_univ _,?_,(hproper ⟨(z,0),rfl⟩).2.2⟩,rfl⟩
        exact hs.1 z 0 (by norm_num)
      have hpair := hFinish M V B
        (Set.range (fun z : Circle => BActual (GTop (z,0))))
        (Set.range (fun z : Circle => BActual (G (z,0))))
        δL δR hδL hδLq hδR hδRq HL HR hLf hRf hLfix hRfix hOldHigh
      simp only [hGTop0] at hpair
      rw [Set.union_comm] at hpair
      exact hpair
end CurveComplex.HyperellipticModel
