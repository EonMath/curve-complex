import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.RectangularSourceTailGeometry
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.SeparatedRegularTailsChordAssembly

open Set Schoenflies
namespace CurveComplex

/-- The existing proper-crosscut replacement with its actual finite original
axis-contact count retained as an upper bound. -/
theorem position_count_controlled_proper_affine_crosscut
    (E : OpenPartialHomeomorph Plane Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ E.source)
    (ha : E (Plane.mk (-1) 0) 0 ≠ 0)
    (hb : E (Plane.mk 1 0) 0 ≠ 0)
    (hf : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
      {z : Plane | z 0 = 0}).Finite) :
    ∃ B : Set Plane,
      IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      B \ {Plane.mk (-1) 0, Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
      ((E '' B) ∩ {z : Plane | z 0 = 0}).Finite ∧
      ((E '' B) ∩ {z : Plane | z 0 = 0}).ncard ≤
        ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
          {z : Plane | z 0 = 0}).ncard ∧
      (∀ p ∈ (E '' B) ∩ {z : Plane | z 0 = 0},
        ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ E '' B ↔ z 1 = p 1 + m * z 0)) := by
  classical
  generalize hcount : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
    {z : Plane | z 0=0}).ncard = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases hNonempty : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
      {z : Plane | z 0=0}).Nonempty
    · by_cases hSingle : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
        {z : Plane | z 0=0}).Subsingleton
      · simpa only [hcount] using countControlledProperCrosscutOfOneContact E hSquare ha hb hf hSingle hNonempty
      ·
        have hsegmentFinite (x y : Plane) (hx : x 0 ≠ 0) :
            (segment ℝ x y ∩ {z : Plane | z 0 = 0}).Finite := by
          apply Set.Subsingleton.finite
          intro p hp q hq
          rw [segment_eq_image_lineMap] at hp hq
          obtain ⟨s, hs, hsp⟩ := hp.1
          obtain ⟨t, ht, htq⟩ := hq.1
          have hcoord : ∀ u : ℝ, (AffineMap.lineMap x y u) 0 =
              (1-u) * x 0 + u * y 0 := by
            intro u
            simp [AffineMap.lineMap_apply_module]
          have hps : (1-s) * x 0 + s * y 0 = 0 := by
            rw [← hcoord, hsp]; exact hp.2
          have hqt : (1-t) * x 0 + t * y 0 = 0 := by
            rw [← hcoord, htq]; exact hq.2
          have hxy : y 0 - x 0 ≠ 0 := by
            intro h
            have hh := sub_eq_zero.mp h
            rw [hh] at hps
            exact hx (by nlinarith)
          have hst : s = t := by
            have hh : (s-t) * (y 0-x 0) = 0 := by nlinarith
            exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hxy)
          rw [← hsp, ← htq, hst]
        let g : ℝ → Plane := fun t => Plane.mk (2*t-1) 0
        have hg : Continuous g := by
          unfold g
          exact PiLp.continuous_toLp 2 _ |>.comp
            (continuous_pi (fun i => by fin_cases i <;> simp <;> fun_prop))
        have hgSquare (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
            g t ∈ Plane.closedSquare 0 1 := by
          change Plane.supDist (g t) 0 ≤ 1
          simp only [g, Plane.supDist, Plane.supNorm, Plane.mk, sub_zero, max_le_iff]
          constructor
          · change |2*t-1| ≤ 1
            rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
          · norm_num
        have hgOpen (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
            g t ∈ Plane.openSquare 0 1 := by
          rw [Plane.mem_openSquare_iff]
          intro i
          fin_cases i
          · simp only [g, PiLp.zero_apply, sub_zero]
            change |2*t-1| < 1
            rw [abs_lt]; constructor <;> linarith [ht.1,ht.2]
          · norm_num [g,Plane.mk]
        let D : Set Plane := E '' Plane.openSquare 0 1
        have hOpenSource : Plane.openSquare 0 1 ⊆ E.source :=
          (Plane.openSquare_subset_closedSquare 0 1).trans hSquare
        have hDopen : IsOpen D := E.isOpen_image_of_subset_source
          (Plane.isOpen_openSquare 0 1) hOpenSource
        have hDconn : IsPreconnected D := (Plane.convex_openSquare 0 1).isPreconnected.image
          E (E.continuousOn.mono hOpenSource)
        let f : ℝ → Plane := fun t => E (g t)
        have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
          E.continuousOn.comp hg.continuousOn (fun t ht => hSquare (hgSquare t ht))
        have hfinj : Set.InjOn f (Icc (0 : ℝ) 1) := by
          intro s hs t ht h
          have hh := E.injOn (hSquare (hgSquare s hs)) (hSquare (hgSquare t ht)) h
          have hh0 := congrArg (fun z : Plane => z 0) hh
          change 2*s-1 = 2*t-1 at hh0
          linarith
        have hfD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : f t ∈ D :=
          ⟨g t,hgOpen t ht,rfl⟩
        have hf0 : f 0 = E (Plane.mk (-1) 0) := by simp [f,g]
        have hf1 : f 1 = E (Plane.mk 1 0) := by norm_num [f,g]
        have hline (t : ℝ) : g t = AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t := by
          ext i
          fin_cases i <;> simp [g,Plane.mk,AffineMap.lineMap_apply_module] <;> ring
        have hgrange : g '' Icc (0:ℝ) 1 = segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := by
          rw [segment_eq_image_lineMap]
          exact congrArg (fun h : ℝ → Plane => h '' Icc (0:ℝ) 1) (funext hline)
        have hfrange : f '' Icc (0:ℝ) 1 = E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := by
          rw [← hgrange,Set.image_image]
        obtain ⟨p,hp⟩ := hNonempty
        have hpimage : p ∈ f '' Icc (0:ℝ) 1 := hfrange.symm ▸ hp.1
        obtain ⟨t,htI,htp⟩ := hpimage
        have ht0 : 0 < t := by
          apply lt_of_le_of_ne htI.1
          intro he
          have he' : t=0 := he.symm
          exact ha (by simpa [← htp,he',hf0] using hp.2)
        have ht1 : t < 1 := by
          apply lt_of_le_of_ne htI.2
          intro he
          exact hb (by simpa [← htp,he,hf1] using hp.2)
        have hpD : p ∈ D := htp ▸ hfD t ⟨ht0,ht1⟩
        let A : Set Plane := (E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩ {z : Plane | z 0=0}
        let U := D ∩ (A \ {p})ᶜ
        have hUo : IsOpen U := hDopen.inter (hf.sdiff.isClosed.isOpen_compl)
        have hpU : p ∈ U := ⟨hpD,by intro h; exact h.2 (Set.mem_singleton p)⟩
        obtain ⟨ρ,hρ,hballU⟩ := Metric.isOpen_iff.mp hUo p hpU
        have hfc : ContinuousAt f t :=
          (E.continuousAt (hSquare (hgSquare t htI))).comp hg.continuousAt
        have hnear : f ⁻¹' Metric.ball p ρ ∈ nhds t :=
          hfc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by rw [htp]; exact Metric.mem_ball_self hρ))
        obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnear
        let δ : ℝ := min ε (min t (1-t))/2
        have hδ : 0 < δ := by dsimp [δ]; positivity
        have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (min t (1-t))]
        have hδt : δ < t := by
          have hh := (min_le_right ε (min t (1-t))).trans (min_le_left t (1-t))
          dsimp [δ]; linarith
        have hδ1 : δ < 1-t := by
          have hh := (min_le_right ε (min t (1-t))).trans (min_le_right t (1-t))
          dsimp [δ]; linarith
        let s := t-δ
        let r := t+δ
        have hs0 : 0 < s := by dsimp [s]; linarith
        have hst : s < t := by dsimp [s]; linarith
        have htr : t < r := by dsimp [r]; linarith
        have hr1 : r < 1 := by dsimp [r]; linarith
        have hsI : s ∈ Icc (0:ℝ) 1 := ⟨hs0.le,(hst.trans ht1).le⟩
        have hrI : r ∈ Icc (0:ℝ) 1 := ⟨(ht0.trans htr).le,hr1.le⟩
        have hsball : f s ∈ Metric.ball p ρ := by
          apply hεsub
          rw [Metric.mem_ball,Real.dist_eq,abs_lt]
          dsimp [s]; constructor <;> linarith
        have hrball : f r ∈ Metric.ball p ρ := by
          apply hεsub
          rw [Metric.mem_ball,Real.dist_eq,abs_lt]
          dsimp [r]; constructor <;> linarith
        have hsaxis : f s 0 ≠ 0 := by
          intro he
          have hmem : f s ∈ A := ⟨hfrange ▸ ⟨s,hsI,rfl⟩,he⟩
          have hne : f s ≠ p := by
            intro heq
            have hh := hfinj hsI htI (heq.trans htp.symm)
            linarith
          exact (hballU hsball).2 ⟨hmem,by simpa using hne⟩
        have hraxis : f r 0 ≠ 0 := by
          intro he
          have hmem : f r ∈ A := ⟨hfrange ▸ ⟨r,hrI,rfl⟩,he⟩
          have hne : f r ≠ p := by
            intro heq
            have hh := hfinj hrI htI (heq.trans htp.symm)
            linarith
          exact (hballU hrball).2 ⟨hmem,by simpa using hne⟩
        have hchordBall : segment ℝ (f s) (f r) ⊆ Metric.ball p ρ :=
          (convex_ball p ρ).segment_subset hsball hrball
        have hchordD : segment ℝ (f s) (f r) ⊆ D := fun z hz => (hballU (hchordBall hz)).1
        let K := segment ℝ (f s) (f r) ∩ {z : Plane | z 0=0}
        have hKf : K.Finite := hsegmentFinite (f s) (f r) hsaxis
        have hKt : K ⊆ E.target := by
          intro z hz
          obtain ⟨x,hx,rfl⟩ := hchordD hz.1
          exact E.map_source (hOpenSource hx)
        have hKA : ∀ z ∈ K, z ∈ A → z=p := by
          intro z hz hzA
          by_contra hne
          exact (hballU (hchordBall hz.1)).2 ⟨hzA,by simpa using hne⟩
        let SL := segment ℝ (Plane.mk (-1) 0) (g s)
        let SR := segment ℝ (g r) (Plane.mk 1 0)
        have hSourceS : g s ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := hgrange ▸ ⟨s,hsI,rfl⟩
        have hSourceR : g r ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := hgrange ▸ ⟨r,hrI,rfl⟩
        have hSLsub : SL ⊆ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) :=
          (convex_segment (Plane.mk (-1) 0) (Plane.mk 1 0)).segment_subset (left_mem_segment ℝ _ _) hSourceS
        have hSRsub : SR ⊆ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) :=
          (convex_segment (Plane.mk (-1) 0) (Plane.mk 1 0)).segment_subset hSourceR (right_mem_segment ℝ _ _)
        have hCenterSquare : segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) ⊆ Plane.closedSquare 0 1 := by
          intro z hz
          obtain ⟨q,hq,rfl⟩ := hgrange.symm ▸ hz
          exact hgSquare q hq
        have hSLcoord : ∀ z ∈ SL, z 0 ≤ 2*s-1 := by
          intro z hz
          exact (Plane.convex_coord_le 0 (2*s-1)).segment_subset
            (by change -1 ≤ 2*s-1; linarith)
            (by change 2*s-1 ≤ 2*s-1; rfl) hz
        have hSRcoord : ∀ z ∈ SR, 2*r-1 ≤ z 0 := by
          intro z hz
          exact (Plane.convex_coord_ge 0 (2*r-1)).segment_subset
            (by change 2*r-1 ≤ 2*r-1; rfl)
            (by change 2*r-1 ≤ 1; linarith) hz
        have hSLavoid : ∀ z ∈ SL, E z ∉ K := by
          intro z hz hK
          have hmem : E z ∈ A := ⟨⟨z,hSLsub hz,rfl⟩,hK.2⟩
          have he : E z=p := hKA (E z) hK hmem
          have heq := E.injOn (hSquare (hCenterSquare (hSLsub hz))) (hSquare (hgSquare t htI))
            (he.trans htp.symm)
          have hc := hSLcoord z hz
          rw [heq] at hc
          change 2*t-1 ≤ 2*s-1 at hc
          linarith
        have hSRavoid : ∀ z ∈ SR, E z ∉ K := by
          intro z hz hK
          have hmem : E z ∈ A := ⟨⟨z,hSRsub hz,rfl⟩,hK.2⟩
          have he : E z=p := hKA (E z) hK hmem
          have heq := E.injOn (hSquare (hCenterSquare (hSRsub hz))) (hSquare (hgSquare t htI))
            (he.trans htp.symm)
          have hc := hSRcoord z hz
          rw [heq] at hc
          change 2*r-1 ≤ 2*t-1 at hc
          linarith
        let AL := (E '' SL) ∩ {z : Plane | z 0=0}
        let AR := (E '' SR) ∩ {z : Plane | z 0=0}
        have hALsub : AL ⊆ A := fun z hz => ⟨Set.image_mono hSLsub hz.1,hz.2⟩
        have hARsub : AR ⊆ A := fun z hz => ⟨Set.image_mono hSRsub hz.1,hz.2⟩
        have hALf : AL.Finite := hf.subset hALsub
        have hARf : AR.Finite := hf.subset hARsub
        have hALp : p ∉ AL := by
          rintro ⟨⟨z,hz,he⟩,h0⟩
          have heq := E.injOn (hSquare (hCenterSquare (hSLsub hz))) (hSquare (hgSquare t htI))
            (he.trans htp.symm)
          have hc := hSLcoord z hz
          rw [heq] at hc
          change 2*t-1 ≤ 2*s-1 at hc
          linarith
        have hARp : p ∉ AR := by
          rintro ⟨⟨z,hz,he⟩,h0⟩
          have heq := E.injOn (hSquare (hCenterSquare (hSRsub hz))) (hSquare (hgSquare t htI))
            (he.trans htp.symm)
          have hc := hSRcoord z hz
          rw [heq] at hc
          change 2*r-1 ≤ 2*t-1 at hc
          linarith
        have hALR : Disjoint AL AR := by
          apply Set.disjoint_left.mpr
          rintro q ⟨⟨x,hx,hxq⟩,hq0⟩ ⟨⟨y,hy,hyq⟩,h'q0⟩
          have heq := E.injOn (hSquare (hCenterSquare (hSLsub hx)))
            (hSquare (hCenterSquare (hSRsub hy))) (hxq.trans hyq.symm)
          have hcL := hSLcoord x hx
          have hcR := hSRcoord y hy
          rw [heq] at hcL
          linarith
        have hsum : AL.ncard+AR.ncard+1 ≤ A.ncard := by
          have hsub : AL ∪ AR ⊆ A \ {p} := by
            intro z hz
            rcases hz with h | h
            · exact ⟨hALsub h,by intro he; exact hALp (Set.mem_singleton_iff.mp he ▸ h)⟩
            · exact ⟨hARsub h,by intro he; exact hARp (Set.mem_singleton_iff.mp he ▸ h)⟩
          have hc := Set.ncard_le_ncard hsub hf.sdiff
          rw [Set.ncard_union_eq hALR hALf hARf] at hc
          have hdel := Set.ncard_sdiff_singleton_add_one hp hf
          change (A \ {p}).ncard+1=A.ncard at hdel
          omega
        have hALlt : AL.ncard < n := by change A.ncard=n at hcount; omega
        have hARlt : AR.ncard < n := by change A.ncard=n at hcount; omega
        have hsx : -1 < 2*s-1 := by linarith
        have hrx : 2*r-1 < 1 := by linarith
        obtain ⟨rL,hrL,hrL1,hHL0,hHL1,hHLSq,hHLavoid⟩ :=
          countCrosscutThinRectangleAvoidingFinite E hSquare (-1) (2*s-1) hsx (by norm_num)
            (by linarith) K hKf hKt hSLavoid
        obtain ⟨rR,hrR,hrR1,hHR0,hHR1,hHRSq,hHRavoid⟩ :=
          countCrosscutThinRectangleAvoidingFinite E hSquare (2*r-1) 1 hrx (by linarith)
            (by norm_num) K hKf hKt hSRavoid
        let HL := countCrosscutRectangleHomeomorph (-1) (2*s-1) rL hsx hrL
        let HR := countCrosscutRectangleHomeomorph (2*r-1) 1 rR hrx hrR
        let EL := HL.toOpenPartialHomeomorph.trans E
        let ER := HR.toOpenPartialHomeomorph.trans E
        have hEL (z : Plane) : EL z=E (HL z) := rfl
        have hER (z : Plane) : ER z=E (HR z) := rfl
        have hELSquare : Plane.closedSquare 0 1 ⊆ EL.source := by
          intro z hz
          simp only [EL,OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_preimage]
          exact hSquare (hHLSq ⟨z,hz,rfl⟩)
        have hERSquare : Plane.closedSquare 0 1 ⊆ ER.source := by
          intro z hz
          simp only [ER,OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_preimage]
          exact hSquare (hHRSq ⟨z,hz,rfl⟩)
        have hEL0 : EL (Plane.mk (-1) 0)=f 0 := by rw [hEL,hHL0,hf0]
        have hEL1 : EL (Plane.mk 1 0)=f s := by rw [hEL,hHL1]
        have hER0 : ER (Plane.mk (-1) 0)=f r := by rw [hER,hHR0]
        have hER1 : ER (Plane.mk 1 0)=f 1 := by rw [hER,hHR1,hf1]
        have hELCenter : EL '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)=E '' SL := by
          calc
            EL '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) =
              E '' (HL '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) :=
                (Set.image_image E HL (segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0))).symm
            _ = E '' SL := by rw [countCrosscutRectangleCenterImage]
        have hERCenter : ER '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)=E '' SR := by
          calc
            ER '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) =
              E '' (HR '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) :=
                (Set.image_image E HR (segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0))).symm
            _ = E '' SR := by rw [countCrosscutRectangleCenterImage]
        have hELf : (EL '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) ∩ {z : Plane | z 0=0}).Finite := by
          simpa only [hELCenter] using hALf
        have hERf : (ER '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) ∩ {z : Plane | z 0=0}).Finite := by
          simpa only [hERCenter] using hARf
        obtain ⟨BL,hBLarc,hBLproper,hBLfinite,hBLcount,hBLgraph⟩ := ih AL.ncard hALlt EL hELSquare
          (by simpa only [hEL0,hf0] using ha) (by simpa only [hEL1] using hsaxis) hELf
          (by rw [hELCenter])
        obtain ⟨BR,hBRarc,hBRproper,hBRfinite,hBRcount,hBRgraph⟩ := ih AR.ncard hARlt ER hERSquare
          (by simpa only [hER0] using hraxis) (by simpa only [hER1,hf1] using hb) hERf
          (by rw [hERCenter])
        have hstandardSquare (B : Set Plane)
            (hBi : B \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1) :
            B ⊆ Plane.closedSquare 0 1 := by
          intro z hz
          by_cases he : z ∈ ({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)
          · rcases he with rfl | he
            · change Plane.supDist (Plane.mk (-1) 0) 0 ≤ 1
              norm_num [Plane.supDist,Plane.supNorm,Plane.mk]
            · rw [Set.mem_singleton_iff.mp he]
              change Plane.supDist (Plane.mk 1 0) 0 ≤ 1
              norm_num [Plane.supDist,Plane.supNorm,Plane.mk]
          · exact Plane.openSquare_subset_closedSquare 0 1 (hBi ⟨hz,he⟩)
        have hBLSq : BL ⊆ Plane.closedSquare 0 1 := hstandardSquare BL hBLproper
        have hBRSq : BR ⊆ Plane.closedSquare 0 1 := hstandardSquare BR hBRproper
        let L := EL '' BL
        let T := ER '' BR
        have hLarc : IsArcBetween L (f 0) (f s) := by
          rw [← hEL0,← hEL1]
          exact hBLarc.image_of_injOn (hBLSq.trans hELSquare) EL.continuousOn EL.injOn
        have hTarc : IsArcBetween T (f r) (f 1) := by
          rw [← hER0,← hER1]
          exact hBRarc.image_of_injOn (hBRSq.trans hERSquare) ER.continuousOn ER.injOn
        have hLT : Disjoint L T := by
          apply Set.disjoint_left.mpr
          rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
          have hxSq := hBLSq hx
          have hySq := hBRSq hy
          have he : HL x=HR y := E.injOn
            (hSquare (hHLSq ⟨x,hxSq,rfl⟩)) (hSquare (hHRSq ⟨y,hySq,rfl⟩))
            (show E (HL x)=E (HR y) from hxz.trans hyz.symm)
          have hxcoord := (countCrosscutRectangleClosedCoordinates (-1) (2*s-1) rL hsx hrL x hxSq).2.1
          have hycoord := (countCrosscutRectangleClosedCoordinates (2*r-1) 1 rR hrx hrR y hySq).1
          change (HL x) 0 ≤ 2*s-1 at hxcoord
          change 2*r-1 ≤ (HR y) 0 at hycoord
          rw [he] at hxcoord
          linarith
        have hLK : ∀ z ∈ K, z ∉ L := by
          rintro z hz ⟨x,hx,hxz⟩
          apply hHLavoid x (hBLSq hx)
          exact hxz.symm ▸ hz
        have hTK : ∀ z ∈ K, z ∉ T := by
          rintro z hz ⟨x,hx,hxz⟩
          apply hHRavoid x (hBRSq hx)
          exact hxz.symm ▸ hz
        have hHLopen : HL '' Plane.openSquare 0 1 ⊆ Plane.openSquare 0 1 :=
          countCrosscutRectangleOpenSquare (-1) (2*s-1) rL hsx hrL (by norm_num) (by linarith) hrL1
        have hHRopen : HR '' Plane.openSquare 0 1 ⊆ Plane.openSquare 0 1 :=
          countCrosscutRectangleOpenSquare (2*r-1) 1 rR hrx hrR (by linarith) (by norm_num) hrR1
        have hLD : L \ {f 0,f 1} ⊆ D := by
          rintro z ⟨⟨x,hx,hxz⟩,hne⟩
          by_cases he : x ∈ ({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)
          · rcases he with rfl | he
            · exact False.elim (hne (Or.inl (hxz.symm.trans hEL0)))
            · have he1 := Set.mem_singleton_iff.mp he
              rw [he1,hEL1] at hxz
              exact hxz ▸ hfD s ⟨hs0,hst.trans ht1⟩
          · exact ⟨HL x,hHLopen ⟨x,hBLproper ⟨hx,he⟩,rfl⟩,hxz⟩
        have hTD : T \ {f 0,f 1} ⊆ D := by
          rintro z ⟨⟨x,hx,hxz⟩,hne⟩
          by_cases he : x ∈ ({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)
          · rcases he with rfl | he
            · rw [hER0] at hxz
              exact hxz ▸ hfD r ⟨ht0.trans htr,hr1⟩
            · have he1 := Set.mem_singleton_iff.mp he
              rw [he1,hER1] at hxz
              exact False.elim (hne (Or.inr (by simpa using hxz.symm)))
          · exact ⟨HR x,hHRopen ⟨x,hBRproper ⟨hx,he⟩,rfl⟩,hxz⟩
        have hLreg : ∀ q ∈ L ∩ {z : Plane | z 0=0}, ∃ W : Set Plane,
            IsOpen W ∧ q ∈ W ∧ ∃ m : ℝ, ∀ z ∈ L ∩ W, z 1=q 1+m*z 0 := by
          intro q hq
          obtain ⟨W,hWo,hqW,hWt,m,hm⟩ := hBLgraph q hq
          exact ⟨W,hWo,hqW,m,fun z hz => (hm z hz.2).mp hz.1⟩
        have hTreg : ∀ q ∈ T ∩ {z : Plane | z 0=0}, ∃ W : Set Plane,
            IsOpen W ∧ q ∈ W ∧ ∃ m : ℝ, ∀ z ∈ T ∩ W, z 1=q 1+m*z 0 := by
          intro q hq
          obtain ⟨W,hWo,hqW,hWt,m,hm⟩ := hBRgraph q hq
          exact ⟨W,hWo,hqW,m,fun z hz => (hm z hz.2).mp hz.1⟩
        have h0r : f 0 ≠ f r := by
          intro he
          have hh := hfinj (by simp) hrI he
          linarith
        have h01 : f 0 ≠ f 1 := by
          intro he
          have hh := hfinj (by simp) (by simp) he
          norm_num at hh
        have hsr : f s ≠ f r := by
          intro he
          have hh := hfinj hsI hrI he
          linarith
        obtain ⟨C,hCarc,hcover,hCproper,hCfinite,hCone,hCgraph⟩ :=
          countCrosscutArcInSeparatedRegularTailsAndChord L T D (f 0) (f s) (f r) (f 1)
            hLarc hTarc h0r h01 hsr (by simpa only [hf0] using ha) hsaxis (by simpa only [hf1] using hb)
            hLT (fun q hq hq0 => ⟨hLK q ⟨hq,hq0⟩,hTK q ⟨hq,hq0⟩⟩) hBLfinite hBRfinite
            hLreg hTreg hLD hTD hchordD hDopen
        have hCcount : (C ∩ {z : Plane | z 0=0}).ncard ≤ n := by
          change A.ncard=n at hcount
          change (L ∩ {z : Plane | z 0=0}).ncard ≤ AL.ncard at hBLcount
          change (T ∩ {z : Plane | z 0=0}).ncard ≤ AR.ncard at hBRcount
          omega
        have hCtarget : C ⊆ E.target := by
          intro z hz
          by_cases hze : z ∈ ({f 0,f 1} : Set Plane)
          · rcases hze with rfl | hz
            · exact E.map_source (hSquare (hgSquare 0 (by simp)))
            · rw [Set.mem_singleton_iff.mp hz]
              exact E.map_source (hSquare (hgSquare 1 (by simp)))
          · obtain ⟨x,hx,rfl⟩ := hCproper ⟨hz,hze⟩
            exact E.map_source (hOpenSource hx)
        have hCregular : ∀ p ∈ C ∩ {z : Plane | z 0=0},
            ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
            ∃ m : ℝ, ∀ z ∈ W, (z ∈ C ↔ z 1=p 1+m*z 0) := by
          intro q hq
          obtain ⟨W,hWo,hqW,hWD,m,hm⟩ := hCgraph q hq
          refine ⟨W,hWo,hqW,?_,m,hm⟩
          intro z hz
          obtain ⟨x,hx,rfl⟩ := hWD hz
          exact E.map_source (hOpenSource hx)
        let B : Set Plane := E.symm '' C
        have hBimage : E '' B = C := by
          ext z
          constructor
          · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
            simpa [E.right_inv (hCtarget hy)] using hy
          · intro hz
            exact ⟨E.symm z,⟨z,hz,rfl⟩,E.right_inv (hCtarget hz)⟩
        have hBsource : B ⊆ E.source := by
          rintro z ⟨x,hx,rfl⟩
          exact E.symm.map_source (hCtarget hx)
        have hB0 : E.symm (f 0) = Plane.mk (-1) 0 := by
          rw [hf0]
          exact E.left_inv (by simpa [g] using hSquare (hgSquare 0 (by simp)))
        have hB1 : E.symm (f 1) = Plane.mk 1 0 := by
          rw [hf1]
          exact E.left_inv (by convert hSquare (hgSquare 1 (by simp)) using 1 <;> norm_num [g])
        have hBarc : IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) := by
          rw [← hB0,← hB1]
          exact hCarc.image_of_injOn hCtarget E.symm.continuousOn E.symm.injOn
        refine ⟨B,hBarc,?_,by simpa [hBimage] using hCfinite,by simpa [hBimage] using hCcount,?_⟩
        · intro z hz
          obtain ⟨x,hx,hxz⟩ := hz.1
          have hxe : x ∉ ({f 0,f 1} : Set Plane) := by
            intro he
            rcases he with he | he
            · apply hz.2
              left
              rw [← hxz,he,hB0]
            · apply hz.2
              right
              rw [← hxz,Set.mem_singleton_iff.mp he,hB1]
              exact Set.mem_singleton _
          obtain ⟨y,hy,hyx⟩ := hCproper ⟨hx,hxe⟩
          have he : E.symm x = y := by rw [← hyx,E.left_inv (hOpenSource hy)]
          rwa [← hxz,he]
        · simpa [hBimage] using hCregular
    · simpa only [hcount] using countControlledProperCrosscutOfNoContact E (Set.not_nonempty_iff_eq_empty.mp hNonempty)

end CurveComplex
