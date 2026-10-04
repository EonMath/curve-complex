import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
open Set Topology Metric Schoenflies
open scoped NNReal
namespace CurveComplex.LocalSurgery
set_option maxHeartbeats 10000000 in
theorem exists_supported_strict_disk_enlargement {S : Type} [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : Topology.IsEmbedding d)
    (V : Set S) (hV : IsOpen V) (hdV : Set.range d ⊆ V) :
    ∃ H : AmbientIsotopy S, ∃ d' : C(Metric.closedBall (0 : Plane) 1,S),
      Topology.IsEmbedding d' ∧ Set.range d ⊆ interior (Set.range d') ∧
      Set.range d' ⊆ V ∧ Set.range d' = H.finalMap '' Set.range d ∧
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      (∀ t, H.map (t,d ⟨0,by simp⟩) = d ⟨0,by simp⟩) := by
  classical
  have hBoundaryCurve (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : Topology.IsEmbedding d) :
    ∃ c : Curve S, c.image = d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
    classical
    let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm)
    have hnorm (z : ℂ) : ‖L z‖ = ‖z‖ := by
      change ‖Plane.mk z.re z.im‖ = ‖z‖
      simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,
        Complex.norm_def,Complex.normSq_apply,Real.norm_eq_abs,pow_two]
    let q : Circle → Metric.closedBall (0 : Plane) 1 := fun z =>
      ⟨L (z : ℂ),Metric.mem_closedBall.mpr (by rw [dist_zero_right,hnorm,Circle.norm_coe])⟩
    have hq : Topology.IsEmbedding q := by
      apply (L.toHomeomorph.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict
    let c : Curve S := ⟨d ∘ q,hd.comp hq⟩
    refine ⟨c,?_⟩
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      refine ⟨q z,?_,rfl⟩
      change dist (L (z : ℂ)) 0 = 1
      rw [dist_zero_right,hnorm,Circle.norm_coe]
    · rintro ⟨x,hx,rfl⟩
      have hzN : ‖L.symm x.val‖ = 1 := by
        rw [← hnorm (L.symm x.val),L.apply_symm_apply]
        simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hx
      let z : Circle := ⟨L.symm x.val,by change L.symm x.val ∈ Metric.sphere (0 : ℂ) 1; simpa only [Metric.mem_sphere,dist_zero_right] using hzN⟩
      refine ⟨z,?_⟩
      change d (q z) = d x
      congr 1
      apply Subtype.ext
      exact L.apply_symm_apply x.val
  have hFrontierEq (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : Topology.IsEmbedding d) :
    frontier (Set.range d) = d '' {x | x.val ∈ Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    rw [(isCompact_range d.continuous).isClosed.frontier_eq,
      embedded_surface_disk_interior_eq d hd]
    ext y
    constructor
    · rintro ⟨⟨a,rfl⟩,ha⟩
      change ¬ ∃ b : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
        dist b.val 0 < 1 ∧ d b = d a at ha
      refine ⟨a,?_,rfl⟩
      change dist a.val 0 = 1
      have hle : dist a.val 0 ≤ 1 := Metric.mem_closedBall.mp a.property
      have hnlt : ¬ dist a.val 0 < 1 := by
        intro hlt
        exact ha ⟨a,hlt,rfl⟩
      exact le_antisymm hle (le_of_not_gt hnlt)
    · rintro ⟨a,ha,rfl⟩
      refine ⟨⟨a,rfl⟩,?_⟩
      rintro ⟨b,hb,hba⟩
      have hsame : b = a := hd.injective hba
      subst b
      have hlt : dist a.val 0 < 1 := Metric.mem_ball.mp hb
      have heq : dist a.val 0 = 1 := Metric.mem_sphere.mp ha
      linarith
  have hHalf (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : Topology.IsEmbedding d)
    (E : OpenPartialHomeomorph S Plane)
    (hsq : Plane.closedSquare 0 1 ⊆ E.target)
    (haxis : ∀ x ∈ E.source, x ∈ frontier (Set.range d) ↔ E x 1 = 0) :
    ((E.symm '' {x : Plane | -1 < x 0 ∧ x 0 < 1 ∧ 0 < x 1 ∧ x 1 < 1})
       ⊆ interior (Set.range d) ∧
     (E.symm '' {x : Plane | -1 < x 0 ∧ x 0 < 1 ∧ -1 < x 1 ∧ x 1 < 0})
       ⊆ (Set.range d)ᶜ) ∨
    ((E.symm '' {x : Plane | -1 < x 0 ∧ x 0 < 1 ∧ -1 < x 1 ∧ x 1 < 0})
       ⊆ interior (Set.range d) ∧
     (E.symm '' {x : Plane | -1 < x 0 ∧ x 0 < 1 ∧ 0 < x 1 ∧ x 1 < 1})
       ⊆ (Set.range d)ᶜ) := by
    classical
    have hselect
      (D P A B : Set S) (hD : IsClosed D) (hP : IsOpen P)
      (hA : IsPreconnected A) (hB : IsPreconnected B)
      (hAF : Disjoint A (frontier D)) (hBF : Disjoint B (frontier D))
      (hcover : P ⊆ (A ∪ B) ∪ frontier D)
      (p : S) (hpP : p ∈ P) (hpF : p ∈ frontier D)
      (hpcl : p ∈ closure (interior D)) :
      (A ⊆ interior D ∧ B ⊆ Dᶜ) ∨
      (B ⊆ interior D ∧ A ⊆ Dᶜ) := by
      have hclass (C : Set S) (hC : IsPreconnected C)
          (hCF : Disjoint C (frontier D)) : C ⊆ interior D ∨ C ⊆ Dᶜ := by
        apply hC.subset_or_subset isOpen_interior hD.isOpen_compl
          (Set.disjoint_left.mpr (fun x hx hx' => hx' (interior_subset hx)))
        intro x hx
        by_cases hxD : x ∈ D
        · left
          by_contra hxI
          apply Set.disjoint_left.mp hCF hx
          rw [hD.frontier_eq]
          exact ⟨hxD,hxI⟩
        · exact Or.inr hxD
      have hnotBoth : ¬ (A ⊆ interior D ∧ B ⊆ interior D) := by
        rintro ⟨ha,hb⟩
        have hPD : P ⊆ D := by
          intro x hx
          rcases hcover hx with (hx | hx) | hx
          · exact interior_subset (ha hx)
          · exact interior_subset (hb hx)
          · rw [hD.frontier_eq] at hx
            exact hx.1
        have hpI : p ∈ interior D := hP.subset_interior_iff.mpr hPD hpP
        rw [hD.frontier_eq] at hpF
        exact hpF.2 hpI
      obtain ⟨y,hyP,hyI⟩ := mem_closure_iff.mp hpcl P hP hpP
      have hyNF : y ∉ frontier D := by
        rw [hD.frontier_eq]
        exact fun h => h.2 hyI
      have hyAB : y ∈ A ∪ B := (hcover hyP).resolve_right hyNF
      rcases hclass A hA hAF with ha | ha <;>
        rcases hclass B hB hBF with hb | hb
      · exact False.elim (hnotBoth ⟨ha,hb⟩)
      · exact Or.inl ⟨ha,hb⟩
      · exact Or.inr ⟨hb,ha⟩
      · rcases hyAB with hyA | hyB
        · exact False.elim (ha hyA (interior_subset hyI))
        · exact False.elim (hb hyB (interior_subset hyI))
    have hdensity : closure (interior (Set.range d)) = Set.range d := by
      let Plane := EuclideanSpace ℝ (Fin 2)
      let A : Set (Metric.closedBall (0 : Plane) 1) :=
        {x | x.val ∈ Metric.ball (0 : Plane) 1}
      have himage : Subtype.val '' A = Metric.ball (0 : Plane) 1 := by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩; exact hy
        · intro hx; exact ⟨⟨x,Metric.ball_subset_closedBall hx⟩,hx,rfl⟩
      have hclosure : closure A = Set.univ := by
        rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himage,
          closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
        ext x
        simp only [Set.mem_preimage,Set.mem_univ,iff_true]
        exact x.property
      have hrange : Set.range d ⊆ closure (d '' A) := by
        rw [← Set.image_univ,← hclosure]
        exact image_closure_subset_closure_image d.continuous
      have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
      rw [embedded_surface_disk_interior_eq d hd]
      apply Set.Subset.antisymm
      · exact closure_minimal (Set.image_subset_range _ _) hclosed
      · exact hrange
    let A0 : Set Plane := {x | -1 < x 0 ∧ x 0 < 1 ∧ 0 < x 1 ∧ x 1 < 1}
    let B0 : Set Plane := {x | -1 < x 0 ∧ x 0 < 1 ∧ -1 < x 1 ∧ x 1 < 0}
    let P0 := Plane.openSquare 0 1
    let A := E.symm '' A0
    let B := E.symm '' B0
    let P := E.symm '' P0
    have hbox (x : Plane) : x ∈ P0 ↔
        -1 < x 0 ∧ x 0 < 1 ∧ -1 < x 1 ∧ x 1 < 1 := by
      change x ∈ Plane.openSquare 0 1 ↔ _
      rw [mem_openSquare_zero_one]
      simp only [Plane.supNorm,max_lt_iff,abs_lt]
      tauto
    have hA0 : A0 ⊆ P0 := by
      intro x hx
      exact (hbox x).mpr ⟨hx.1,hx.2.1,by linarith [hx.2.2.1],hx.2.2.2⟩
    have hB0 : B0 ⊆ P0 := by
      intro x hx
      exact (hbox x).mpr ⟨hx.1,hx.2.1,hx.2.2.1,by linarith [hx.2.2.2]⟩
    have hP0 : P0 ⊆ E.target :=
      (Plane.openSquare_subset_closedSquare 0 1).trans hsq
    have hAcvx : Convex ℝ A0 := by
      convert ((convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 1).linear_preimage (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 0)).inter
        ((convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1).linear_preimage (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 1)) using 1
      ext x
      change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
      tauto
    have hBcvx : Convex ℝ B0 := by
      convert ((convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 1).linear_preimage (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 0)).inter
        ((convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 0).linear_preimage (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 1)) using 1
      ext x
      change (_ ∧ _ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
      tauto
    have hAcon : IsPreconnected A := hAcvx.isPreconnected.image E.symm
      (E.symm.continuousOn.mono (hA0.trans hP0))
    have hBcon : IsPreconnected B := hBcvx.isPreconnected.image E.symm
      (E.symm.continuousOn.mono (hB0.trans hP0))
    have hAF : Disjoint A (frontier (Set.range d)) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨x,hx,rfl⟩ hy
      have hy' := (haxis (E.symm x) (E.symm.map_source (hP0 (hA0 hx)))).mp hy
      rw [E.right_inv (hP0 (hA0 hx))] at hy'
      linarith [hx.2.2.1]
    have hBF : Disjoint B (frontier (Set.range d)) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨x,hx,rfl⟩ hy
      have hy' := (haxis (E.symm x) (E.symm.map_source (hP0 (hB0 hx)))).mp hy
      rw [E.right_inv (hP0 (hB0 hx))] at hy'
      linarith [hx.2.2.2]
    have hcover : P ⊆ (A ∪ B) ∪ frontier (Set.range d) := by
      rintro y ⟨x,hx,rfl⟩
      have hxb := (hbox x).mp hx
      rcases lt_trichotomy (x 1) 0 with hn | hz | hp
      · exact Or.inl (Or.inr ⟨x,⟨hxb.1,hxb.2.1,hxb.2.2.1,hn⟩,rfl⟩)
      · right
        apply (haxis (E.symm x) (E.symm.map_source (hP0 hx))).mpr
        rw [E.right_inv (hP0 hx)]
        exact hz
      · exact Or.inl (Or.inl ⟨x,⟨hxb.1,hxb.2.1,hp,hxb.2.2.2⟩,rfl⟩)
    have hzP0 : (0 : Plane) ∈ P0 := by rw [hbox]; norm_num
    have hpP : E.symm 0 ∈ P := ⟨0,hzP0,rfl⟩
    have hpF : E.symm 0 ∈ frontier (Set.range d) := by
      apply (haxis (E.symm 0) (E.symm.map_source (hP0 hzP0))).mpr
      rw [E.right_inv (hP0 hzP0)]
      rfl
    have hpcl : E.symm 0 ∈ closure (interior (Set.range d)) := by
      rw [hdensity]
      exact frontier_subset_closure.trans (isCompact_range d.continuous).isClosed.closure_subset hpF
    exact hselect (Set.range d) P A B
      (isCompact_range d.continuous).isClosed
      (E.symm.isOpen_image_of_subset_source (Plane.isOpen_openSquare 0 1) hP0)
      hAcon hBcon hAF hBF hcover (E.symm 0) hpP hpF hpcl
  have hNormalize (D : Set S)
    (E : OpenPartialHomeomorph S Plane) (p : S)
    (hp : p ∈ E.source) (hEp : E p = 0)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (hboundary : ∀ x ∈ E.source, x ∈ frontier D ↔ E x 1 = 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hOut : E.symm '' {z : Plane | -1 < z 0 ∧ z 0 < 1 ∧ 0 < s*z 1 ∧ s*z 1 < 1} ⊆ Dᶜ)
    (hIn : E.symm '' {z : Plane | -1 < z 0 ∧ z 0 < 1 ∧ -1 < s*z 1 ∧ s*z 1 < 0} ⊆ D) :
    ∃ F : OpenPartialHomeomorph S Plane,
      F.source = E.source ∧ F p = 0 ∧
      Plane.closedSquare 0 1 ⊆ F.target ∧
      (∀ x ∈ F.source, x ∈ frontier D ↔ F x 0 = 0) ∧
      (F.symm '' {z : Plane | -1 < z 1 ∧ z 1 < 1 ∧ 0 < z 0 ∧ z 0 < 1} ⊆ Dᶜ) ∧
      (F.symm '' {z : Plane | -1 < z 1 ∧ z 1 < 1 ∧ -1 < z 0 ∧ z 0 < 0} ⊆ D) := by
    let T : Plane ≃ₜ Plane := {
      toEquiv := {
        toFun := fun z => Plane.mk (s*z 1) (z 0)
        invFun := fun z => Plane.mk (z 1) (s*z 0)
        left_inv := by
          intro z
          ext i
          fin_cases i <;> rcases hs with rfl | rfl <;> simp
        right_inv := by
          intro z
          ext i
          fin_cases i <;> rcases hs with rfl | rfl <;> simp }
      continuous_toFun := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> dsimp [Plane.mk] <;> fun_prop
      continuous_invFun := by
        apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
        apply continuous_pi
        intro i
        fin_cases i <;> dsimp [Plane.mk] <;> fun_prop }
    let F := E.trans T.toOpenPartialHomeomorph
    have hFs : F.source = E.source := by simp [F]
    have hEval (x : S) : F x = T (E x) := rfl
    have hInv (z : Plane) : F.symm z = E.symm (T.symm z) := rfl
    have hback (z : Plane) (hz : z ∈ Plane.closedSquare 0 1) :
        T.symm z ∈ Plane.closedSquare 0 1 := by
      rw [mem_closedSquare_zero_one] at *
      rcases hs with hs | hs <;>
        simpa [T,Plane.supNorm,Plane.mk,hs,abs_neg,max_comm] using hz
    refine ⟨F,hFs,?_,?_,?_,?_,?_⟩
    · rw [hEval,hEp]
      ext i
      fin_cases i <;> simp [T,Plane.mk]
    · intro z hz
      change z ∈ (E.trans T.toOpenPartialHomeomorph).target
      change z ∈ Set.univ ∩ T.symm ⁻¹' E.target
      exact ⟨Set.mem_univ z,hsquare (hback z hz)⟩
    · intro x hx
      rw [hboundary x (hFs ▸ hx),hEval]
      change E x 1 = 0 ↔ s*E x 1 = 0
      rcases hs with hs | hs <;> simp [hs]
    · rintro x ⟨z,hz,rfl⟩
      rw [hInv]
      apply hOut
      refine ⟨T.symm z,?_,rfl⟩
      rcases hs with hs | hs
      · simpa [T,Plane.mk,hs] using hz
      · change -1 < z 1 ∧ z 1 < 1 ∧ 0 < s*(s*z 0) ∧ s*(s*z 0) < 1
        simpa only [Set.mem_ofPred_eq,hs,neg_one_mul,neg_neg] using hz
    · rintro x ⟨z,hz,rfl⟩
      rw [hInv]
      apply hIn
      refine ⟨T.symm z,?_,rfl⟩
      rcases hs with hs | hs
      · simpa [T,Plane.mk,hs] using hz
      · change -1 < z 1 ∧ z 1 < 1 ∧ -1 < s*(s*z 0) ∧ s*(s*z 0) < 0
        simpa only [Set.mem_ofPred_eq,hs,neg_one_mul,neg_neg] using hz
  have hLocalPush (D : Set S) (hD : IsClosed D)
    (E : OpenPartialHomeomorph S Plane)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (hboundary : ∀ x ∈ E.source, x ∈ frontier D ↔ E x 0 = 0)
    (hpos : E.symm '' {z : Plane | -1 < z 1 ∧ z 1 < 1 ∧ 0 < z 0 ∧ z 0 < 1} ⊆ Dᶜ)
    (hneg : E.symm '' {z : Plane | -1 < z 1 ∧ z 1 < 1 ∧ -1 < z 0 ∧ z 0 < 0} ⊆ D) :
    ∃ G : AmbientIsotopy S,
      (∀ t x, x ∉ E.source → G.map (t,x) = x) ∧
      (∀ t x, x ∉ D → G.map (t,x) ∉ D) ∧
      (∀ t x, x ∈ frontier D → G.map (t,x) = x ∨ G.map (t,x) ∉ D) ∧
      (∀ x, x ∈ E.source → ‖E x‖ < 1/2 → x ∈ frontier D → G.finalMap x ∉ D) := by
    classical
    have hsmall (f : Plane → Plane)
          (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
          ∃ H : AmbientIsotopy Plane,
            (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
            (∀ t x, f x = 0 → H.map (t, x) = x) := by
      classical
      let F : Interval × Plane → Plane :=
        fun p => p.2 + (p.1 : ℝ) • f p.2
      have hF : Continuous F := continuous_snd.add
        ((continuous_subtype_val.comp continuous_fst).smul
          (hf.continuous.comp continuous_snd))
      refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
        fun t x => rfl, ?_⟩
      · intro t
        have happ : ApproximatesLinearOn (fun x => F (t, x))
            (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
            Set.univ c := by
          intro x _ y _
          have heq : F (t, x) - F (t, y) - (x - y) =
              (t : ℝ) • (f x - f y) := by dsimp [F]; module
          change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
          rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
          calc
            (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
              mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
            _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
        let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
        exact ⟨e, fun x => rfl⟩
      · intro x
        simp [F]
      · intro t x hx
        change x + (t : ℝ) • f x = x
        simp [hx]
    
    let v : Plane := Plane.mk (1/4) 0
    have hv : ‖v‖ < 1 := by norm_num [v,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
    let b : Plane → ℝ := fun z => max (1/2-dist z 0) 0
    have hb₀ : LipschitzWith 1 (fun z : Plane => (1/2:ℝ)-dist z 0) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm]
        using abs_dist_sub_le x y (0:Plane)
    have hb : LipschitzWith 1 b := hb₀.max_const 0
    let f : Plane → Plane := fun z => b z • v
    have hf : LipschitzWith ‖v‖₊ f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change ‖b x • v-b y • v‖ ≤ ‖v‖*dist x y
      rw [← sub_smul,norm_smul,Real.norm_eq_abs]
      have h := hb.dist_le_mul x y
      simp only [NNReal.coe_one,one_mul,Real.dist_eq] at h
      nlinarith [norm_nonneg v]
    obtain ⟨H,hH,hHfix⟩ := hsmall f ‖v‖₊ hv hf
    have hvertical (t : Interval) (z : Plane) : H.map (t,z) 1 = z 1 := by
      rw [hH]
      simp [f,v,Plane.mk]
    have hC : IsCompact (Metric.closedBall (0:Plane) (1/2)) := isCompact_closedBall _ _
    have hCt : Metric.closedBall (0:Plane) (1/2) ⊆ E.target := by
      intro z hz
      apply hsquare
      rw [mem_closedSquare_zero_one]
      have hzN : ‖z‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
      exact (Plane.supNorm_le_norm z).trans (by linarith)
    obtain ⟨K,G,hcoord,hGU,hGfix⟩ := position_surface_chart_lift S
      E.source E.target E.open_source E.toHomeomorphSourceTarget
      (Metric.closedBall 0 (1/2)) hC hCt H (by
        intro t z hz
        apply hHfix
        have hd : 1/2 ≤ dist z (0:Plane) := (not_le.mp hz).le
        simp only [f,b,max_eq_right (sub_nonpos.mpr hd),zero_smul])
  
    have hsource (t : Interval) (x : S) (hx : x ∈ E.source) : G.map (t,x) ∈ E.source := by
      rw [hGU t ⟨x,hx⟩]
      exact (K.map (t,⟨x,hx⟩)).property
    have hEq (t : Interval) (x : S) (hx : x ∈ E.source) :
        E (G.map (t,x)) = H.map (t,E x) := by
      rw [hGU t ⟨x,hx⟩]
      exact hcoord t ⟨x,hx⟩
    have hvnorm : ‖v‖ = 1/4 := by
      norm_num [v,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
    have hbnonneg (z : Plane) : 0 ≤ b z := le_max_right _ _
    have hbBound (z : Plane) : b z ≤ 1/2 :=
      max_le (by linarith [dist_nonneg (x := z) (y := (0 : Plane))]) (by norm_num)
    have hfBound (z : Plane) : ‖f z‖ ≤ 1/8 := by
      rw [show f z = b z • v from rfl,norm_smul,
        Real.norm_eq_abs,abs_of_nonneg (hbnonneg z),hvnorm]
      linarith [hbBound z]
    have hNorm (t : Interval) (z : Plane) (hz : ‖z‖ < 1/2) : ‖H.map (t,z)‖ < 1 := by
      rw [hH]
      have htN : ‖(t : ℝ) • f z‖ ≤ 1/8 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1]
        nlinarith [hfBound z,norm_nonneg (f z),t.property.1,t.property.2]
      have ht := norm_add_le z ((t : ℝ) • f z)
      linarith
    have hNormal (t : Interval) (z : Plane) : (H.map (t,z)) 0 = z 0 + t*(b z*(1/4)) := by
      rw [hH]
      rfl
    have hFixLarge (t : Interval) (x : S) (hx : x ∈ E.source) (hn : 1/2 ≤ ‖E x‖) :
        G.map (t,x) = x := by
      have hb0 : b (E x) = 0 := by
        dsimp [b]
        rw [dist_zero_right,max_eq_right (by linarith)]
      have hEx : E (G.map (t,x)) = E x := by
        rw [hEq t x hx,hH]
        simp [f,hb0]
      exact E.injOn (hsource t x hx) hx hEx
    have hSide (x : S) (hx : x ∈ E.source) (hn : ‖E x‖ < 1) :
        (0 < E x 0 → x ∉ D) ∧ (E x 0 < 0 → x ∈ D) := by
      have hc (i : Fin 2) : |E x i| < 1 := by
        have hle : |E x i| ≤ ‖E x‖ := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (E x) i
        exact hle.trans_lt hn
      constructor
      · intro hp
        exact hpos ⟨E x,⟨(abs_lt.mp (hc 1)).1,(abs_lt.mp (hc 1)).2,hp,
          (abs_lt.mp (hc 0)).2⟩,E.left_inv hx⟩
      · intro hm
        exact hneg ⟨E x,⟨(abs_lt.mp (hc 1)).1,(abs_lt.mp (hc 1)).2,
          (abs_lt.mp (hc 0)).1,hm⟩,E.left_inv hx⟩
    have hSmallOut (t : Interval) (x : S) (hx : x ∈ E.source)
        (hn : ‖E x‖ < 1/2) (hzero : E x 0 = 0) (ht : 0 < (t : ℝ)) : G.map (t,x) ∉ D := by
      have hbpos : 0 < b (E x) := by
        dsimp [b]
        rw [dist_zero_right]
        exact lt_max_iff.mpr (Or.inl (by linarith))
      have hpositive : 0 < E (G.map (t,x)) 0 := by
        rw [hEq t x hx,hNormal,hzero]
        positivity
      apply (hSide _ (hsource t x hx) ?_).1 hpositive
      rw [hEq t x hx]
      exact hNorm t (E x) hn
    refine ⟨G,hGfix,?_,?_,?_⟩
    · intro t x hxD
      by_cases hx : x ∈ E.source
      · by_cases hn : ‖E x‖ < 1/2
        · have hpositive : 0 < E x 0 := by
            rcases lt_trichotomy (E x 0) 0 with hnegX | heqX | hposX
            · exact False.elim (hxD ((hSide x hx (by linarith)).2 hnegX))
            · have hf : x ∈ frontier D := (hboundary x hx).mpr heqX
              rw [hD.frontier_eq] at hf
              exact False.elim (hxD hf.1)
            · exact hposX
          have hpNew : 0 < E (G.map (t,x)) 0 := by
            rw [hEq t x hx,hNormal]
            have hb0 := hbnonneg (E x)
            nlinarith [t.property.1]
          apply (hSide _ (hsource t x hx) ?_).1 hpNew
          rw [hEq t x hx]
          exact hNorm t (E x) hn
        · rw [hFixLarge t x hx (le_of_not_gt hn)]
          exact hxD
      · rw [hGfix t x hx]
        exact hxD
    · intro t x hxF
      by_cases hx : x ∈ E.source
      · by_cases hn : ‖E x‖ < 1/2
        · by_cases ht : 0 < (t : ℝ)
          · exact Or.inr (hSmallOut t x hx hn ((hboundary x hx).mp hxF) ht)
          · left
            have ht0 : t = ⟨0,by norm_num⟩ := Subtype.ext (by linarith [t.property.1])
            rw [ht0]
            exact G.at_zero x
        · exact Or.inl (hFixLarge t x hx (le_of_not_gt hn))
      · exact Or.inl (hGfix t x hx)
    · intro x hx hn hxF
      exact hSmallOut ⟨1,by norm_num⟩ x hx hn ((hboundary x hx).mp hxF) (by norm_num)
  have hFinitePush {J : Type} [Fintype J] (D V : Set S) (q : S) (U : J → Set S) (G : J → AmbientIsotopy S)
    (hcover : ∀ x ∈ frontier D, ∃ j, x ∈ U j)
    (hfix : ∀ j t x, x ∉ V → (G j).map (t,x) = x)
    (hqfix : ∀ j t, (G j).map (t,q) = q)
    (hout : ∀ j t x, x ∉ D → (G j).map (t,x) ∉ D)
    (hboundary : ∀ j x, x ∈ frontier D →
      (G j).finalMap x = x ∨ (G j).finalMap x ∉ D)
    (hpush : ∀ j x, x ∈ U j → x ∈ frontier D → (G j).finalMap x ∉ D) :
    ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      (∀ t, H.map (t,q) = q) ∧
      (∀ t x, x ∉ D → H.map (t,x) ∉ D) ∧
      (∀ x, x ∈ frontier D → H.finalMap x ∉ D) := by
    classical
    have hcompose (H K : AmbientIsotopy S) :
        ∃ L : AmbientIsotopy S, ∀ t x, L.map (t,x) = K.map (t,H.map (t,x)) := by
      refine ⟨{
        map := ⟨fun z => K.map (z.1,H.map z),
          K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩
        homeomorphism_at := ?_
        at_zero := ?_ },fun _ _ => rfl⟩
      · intro t
        obtain ⟨e,he⟩ := H.homeomorphism_at t
        obtain ⟨f,hf⟩ := K.homeomorphism_at t
        exact ⟨e.trans f,fun x => (hf (e x)).trans
          (congrArg (fun z => K.map (t,z)) (he x))⟩
      · intro x
        change K.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
        rw [H.at_zero,K.at_zero]
    have hbuild (P : Finset J) : ∃ H : AmbientIsotopy S,
        (∀ t x, x ∉ V → H.map (t,x) = x) ∧
        (∀ t, H.map (t,q) = q) ∧
        (∀ t x, x ∉ D → H.map (t,x) ∉ D) ∧
        (∀ x, x ∈ frontier D → H.finalMap x = x ∨ H.finalMap x ∉ D) ∧
        (∀ j ∈ P, ∀ x, x ∈ U j → x ∈ frontier D → H.finalMap x ∉ D) := by
      induction P using Finset.induction_on with
      | empty =>
        let H : AmbientIsotopy S := {
          map := ⟨Prod.snd,continuous_snd⟩
          homeomorphism_at := fun _ => ⟨Homeomorph.refl S,fun _ => rfl⟩
          at_zero := fun _ => rfl }
        exact ⟨H,fun _ _ _ => rfl,fun _ => rfl,fun _ _ hx => hx,
          fun _ _ => Or.inl rfl,by simp⟩
      | @insert j P hj ih =>
        obtain ⟨H,hHV,hHq,hHout,hHboundary,hHP⟩ := ih
        obtain ⟨L,hL⟩ := hcompose H (G j)
        have hLf (x : S) : L.finalMap x = (G j).finalMap (H.finalMap x) :=
          hL ⟨1,by norm_num⟩ x
        refine ⟨L,?_,?_,?_,?_,?_⟩
        · intro t x hx
          rw [hL,hHV t x hx,hfix j t x hx]
        · intro t
          rw [hL,hHq t,hqfix j t]
        · intro t x hx
          rw [hL]
          exact hout j t (H.map (t,x)) (hHout t x hx)
        · intro x hx
          rw [hLf]
          rcases hHboundary x hx with he | ho
          · rw [he]
            exact hboundary j x hx
          · exact Or.inr (hout j ⟨1,by norm_num⟩ (H.finalMap x) ho)
        · intro k hk x hxU hxF
          rw [hLf]
          rcases Finset.mem_insert.mp hk with he | hk
          · subst k
            rcases hHboundary x hxF with hx | hx
            · rw [hx]
              exact hpush j x hxU hxF
            · exact hout j ⟨1,by norm_num⟩ (H.finalMap x) hx
          · exact hout j ⟨1,by norm_num⟩ (H.finalMap x) (hHP k hk x hxU hxF)
    obtain ⟨H,hfixH,hqH,houtH,hboundaryH,hPH⟩ := hbuild Finset.univ
    refine ⟨H,hfixH,hqH,houtH,?_⟩
    intro x hx
    obtain ⟨j,hxU⟩ := hcover x hx
    exact hPH j (Finset.mem_univ j) x hxU hx
  have hEnlarged (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : Topology.IsEmbedding d) (V : Set S) (hdV : Set.range d ⊆ V)
    (H : AmbientIsotopy S)
    (hfix : ∀ t x, x ∉ V → H.map (t,x) = x)
    (hout : ∀ x, x ∈ frontier (Set.range d) → H.finalMap x ∉ Set.range d)
    (hcenter : H.finalMap (d ⟨0,by simp⟩) = d ⟨0,by simp⟩) :
    ∃ d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S),
      Topology.IsEmbedding d' ∧
      Set.range d ⊆ interior (Set.range d') ∧
      Set.range d' ⊆ V ∧
      Set.range d' = H.finalMap '' Set.range d := by
    classical
    obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    have hefinal (x : S) : e x = H.finalMap x := he x
    let D := Set.range d
    let D' := e '' D
    have hD : IsClosed D := (isCompact_range d.continuous).isClosed
    have hD' : IsClosed D' := e.isClosedMap D hD
    have hconn : IsPreconnected D := by
      have : PreconnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
        isPreconnected_iff_preconnectedSpace.mp isPreconnected_closedBall
      exact isPreconnected_range d.continuous
    have hNoFront : Disjoint D (frontier D') := by
      apply Set.disjoint_left.mpr
      intro x hx hxF
      change x ∈ frontier (e '' D) at hxF
      rw [← e.image_frontier D] at hxF
      obtain ⟨y,hy,rfl⟩ := hxF
      exact hout y hy (by simpa only [← hefinal] using hx)
    let q := d ⟨0,by simp⟩
    have hq : q ∈ interior D := by
      rw [embedded_surface_disk_interior_eq d hd]
      exact ⟨⟨0,by simp⟩,by simp,rfl⟩
    have hqD : q ∈ D := interior_subset hq
    have heq : e q = q := by simpa only [hefinal] using hcenter
    have hq' : q ∈ interior D' := by
      change q ∈ interior (e '' D)
      rw [← e.image_interior D]
      exact ⟨q,hq,heq⟩
    have hcover : D ⊆ interior D' ∪ D'ᶜ := by
      intro x hx
      by_cases hxI : x ∈ interior D'
      · exact Or.inl hxI
      · right
        intro hxD'
        apply Set.disjoint_left.mp hNoFront hx
        rw [hD'.frontier_eq]
        exact ⟨hxD',hxI⟩
    have hinside : D ⊆ interior D' :=
      hconn.subset_left_of_subset_union isOpen_interior hD'.isOpen_compl
        (Set.disjoint_left.mpr (fun _ hi ho => ho (interior_subset hi)))
        hcover ⟨q,hqD,hq'⟩
    have hDV : D' ⊆ V := by
      rintro x ⟨y,hy,rfl⟩
      by_contra hn
      have hefix : e (e y) = e y := by
        rw [hefinal (e y)]
        exact hfix ⟨1,by norm_num⟩ (e y) hn
      have hxy : e y = y := e.injective hefix
      exact hn (hxy.symm ▸ hdV hy)
    let d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
      ⟨e ∘ d,e.continuous.comp d.continuous⟩
    have himage : Set.range d' = D' := Set.range_comp e d
    refine ⟨d',e.isEmbedding.comp hd,?_,?_,?_⟩
    · rw [himage]; exact hinside
    · rw [himage]; exact hDV
    · rw [himage]
      exact congrArg (fun f : S → S => f '' D) (funext hefinal)
  let D := Set.range d
  let q := d ⟨0,by simp⟩
  have hD : IsClosed D := (isCompact_range d.continuous).isClosed
  have hqI : q ∈ interior D := by
    rw [embedded_surface_disk_interior_eq d hd]
    exact ⟨⟨0,by simp⟩,by simp,rfl⟩
  have hqNF : q ∉ frontier D := by
    rw [hD.frontier_eq]
    exact fun h => h.2 hqI
  let W := V \ {q}
  have hW : IsOpen W := hV.sdiff (isClosed_singleton (x := q))
  obtain ⟨c,hc⟩ := hBoundaryCurve d hd
  have hcF : c.image = frontier D := hc.trans (hFrontierEq d hd).symm
  have hcharts (p : frontier D) : ∃ E : OpenPartialHomeomorph S Plane,
      p.val ∈ E.source ∧ E p.val = 0 ∧ E.source ⊆ W ∧
      Plane.closedSquare 0 1 ⊆ E.target ∧
      (∀ x ∈ E.source, x ∈ frontier D ↔ E x 0 = 0) ∧
      (E.symm '' {z : Plane | -1 < z 1 ∧ z 1 < 1 ∧ 0 < z 0 ∧ z 0 < 1} ⊆ Dᶜ) ∧
      (E.symm '' {z : Plane | -1 < z 1 ∧ z 1 < 1 ∧ -1 < z 0 ∧ z 0 < 0} ⊆ D) := by
    have hpW : p.val ∈ W := by
      refine ⟨hdV ?_,?_⟩
      · exact frontier_subset_closure.trans hD.closure_subset p.property
      · intro hpq
        have heq : p.val = q := hpq
        exact hqNF (heq ▸ p.property)
    obtain ⟨E,hp,hzero,hEW,hsq,haxis⟩ :=
      CurveComplex.PositionUniverseV2.position_curve_crosscut_chart S c p.val
        (hcF.symm ▸ p.property) W hW hpW
    have hboundary : ∀ x ∈ E.source, x ∈ frontier D ↔ E x 1 = 0 := by
      intro x hx
      rw [← hcF]
      exact haxis x hx
    have hsign : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        (E.symm '' {z : Plane | -1 < z 0 ∧ z 0 < 1 ∧ 0 < s*z 1 ∧ s*z 1 < 1} ⊆ Dᶜ) ∧
        (E.symm '' {z : Plane | -1 < z 0 ∧ z 0 < 1 ∧ -1 < s*z 1 ∧ s*z 1 < 0} ⊆ D) := by
      rcases hHalf d hd E hsq hboundary with ⟨hUp,hDown⟩ | ⟨hDown,hUp⟩
      · refine ⟨-1,Or.inr rfl,?_,?_⟩
        · rintro x ⟨z,hz,rfl⟩
          apply hDown
          refine ⟨z,⟨hz.1,hz.2.1,?_,?_⟩,rfl⟩ <;> linarith [hz.2.2.1,hz.2.2.2]
        · rintro x ⟨z,hz,rfl⟩
          apply interior_subset
          apply hUp
          refine ⟨z,⟨hz.1,hz.2.1,?_,?_⟩,rfl⟩ <;> linarith [hz.2.2.1,hz.2.2.2]
      · refine ⟨1,Or.inl rfl,?_,?_⟩
        · simpa only [one_mul] using hUp
        · simpa only [one_mul] using hDown.trans interior_subset
    obtain ⟨s,hs,hOut,hIn⟩ := hsign
    obtain ⟨F,hFs,hFzero,hFsq,hFboundary,hFpos,hFneg⟩ :=
      hNormalize D E p.val hp hzero hsq hboundary s hs hOut hIn
    exact ⟨F,hFs.symm ▸ hp,hFzero,(fun _ hx => hEW (hFs ▸ hx)),
      hFsq,hFboundary,hFpos,hFneg⟩
  choose E hpE hEzero hEW hEsq hEboundary hEpos hEneg using hcharts
  have hlocal (p : frontier D) : ∃ G : AmbientIsotopy S,
      (∀ t x, x ∉ V → G.map (t,x) = x) ∧
      (∀ t, G.map (t,q) = q) ∧
      (∀ t x, x ∉ D → G.map (t,x) ∉ D) ∧
      (∀ x, x ∈ frontier D → G.finalMap x = x ∨ G.finalMap x ∉ D) ∧
      (∀ x, x ∈ (E p).source → ‖E p x‖ < 1/2 → x ∈ frontier D → G.finalMap x ∉ D) := by
    obtain ⟨G,hfix,hout,hboundary,hpush⟩ :=
      hLocalPush D hD (E p) (hEsq p) (hEboundary p) (hEpos p) (hEneg p)
    refine ⟨G,?_,?_,hout,hboundary ⟨1,by norm_num⟩,hpush⟩
    · intro t x hxV
      apply hfix
      exact fun hxE => hxV (hEW p hxE).1
    · intro t
      apply hfix
      intro hqE
      exact (hEW p hqE).2 (Set.mem_singleton q)
  choose G hfixG hqG houtG hboundaryG hpushG using hlocal
  let U (p : frontier D) : Set S := (E p).source ∩
    (E p) ⁻¹' ball (0 : Plane) (1/2)
  have hU (p : frontier D) : IsOpen (U p) :=
    (E p).continuousOn.isOpen_inter_preimage (E p).open_source isOpen_ball
  have hpU (p : frontier D) : p.val ∈ U p := by
    refine ⟨hpE p,?_⟩
    change E p p.val ∈ ball (0 : Plane) (1/2)
    rw [hEzero p]
    simp
  have hcompact : IsCompact (frontier D) :=
    (isCompact_range d.continuous).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans hD.closure_subset)
  obtain ⟨A,hA⟩ := hcompact.elim_finite_subcover U hU
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hpU ⟨x,hx⟩⟩)
  let J := ↥A
  let U' (j : J) := U j.val
  let G' (j : J) := G j.val
  have hcover : ∀ x ∈ frontier D, ∃ j : J, x ∈ U' j := by
    intro x hx
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp (hA hx)
    obtain ⟨hpA,hxU⟩ := Set.mem_iUnion.mp hp
    exact ⟨⟨p,hpA⟩,hxU⟩
  obtain ⟨H,hfixH,hqH,houtH,hboundaryH⟩ := hFinitePush D V q U' G' hcover
    (fun j => hfixG j.val) (fun j => hqG j.val) (fun j => houtG j.val)
    (fun j => hboundaryG j.val) (by
      intro j x hx hxF
      exact hpushG j.val x hx.1 (by
        have hh : E j.val x ∈ ball (0 : Plane) (1/2) := hx.2
        simpa only [mem_ball,dist_zero_right] using hh) hxF)
  obtain ⟨d',hd',hinside,hV',himage⟩ := hEnlarged d hd V hdV H hfixH hboundaryH
    (hqH ⟨1,by norm_num⟩)
  exact ⟨H,d',hd',hinside,hV',himage,hfixH,hqH⟩
end CurveComplex.LocalSurgery
