import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualRadialPieceChartTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualFiniteCarrierCrossingTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualWeightedCountTools
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.IntersectionParity.HomeomorphTransport
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualRadialSupportTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualJordanDiskTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.RetainedRemainderExteriorTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualRetainedAngularDecompositionTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.Smoothing.CrossingHalfSideStatement
import CurveComplexGenusTwo.Topology.Smoothing.IncidentCircleRadialCoreStatement
import CurveComplexGenusTwo.Topology.GeometricPosition.SubarcCrosscutChartV2
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import Mathlib.Topology.Order.Compact
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import CurveComplexGenusTwo.Topology.GeometricPosition.OneCurveExtensionStatement
import CurveComplexGenusTwo.Topology.GeometricPosition.CurveCrosscutChartV2
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
open Set Topology Metric Schoenflies CurveComplex.LocalSurgery
open CurveComplex.FiniteStarGeometry
open scoped NNReal
set_option maxHeartbeats 10000000
namespace CurveComplex.FiniteMinimalCompatibility
/-- An actual paired-curve-empty bigon can be removed on the cheaper of its
 two sides, with support in any prescribed neighborhood of the actual disk.
 The entire fixed finite family stays transverse and its ordered total
 intersection count strictly decreases. -/
theorem finite_family_weighted_bigon_replacement
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (I : Type*) [Fintype I] [DecidableEq I] (r : I → EssentialCurve S)
    (hr : ∀ i j, i ≠ j → Transverse (r i).val (r j).val)
    (v w : I) (hvw : v ≠ w)
    (u z : S) (huz : u ≠ z)
    (f g : C(Interval,S))
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
    (hf0 : f 0 = u) (hg0 : g 0 = u) (hf1 : f 1 = z) (hg1 : g 1 = z)
    (hfcurve : Set.range f ⊆ (r v).val.image)
    (hgcurve : Set.range g ⊆ (r w).val.image)
    (hfmeet : Set.range f ∩ (r w).val.image = {u,z})
    (hgmeet : Set.range g ∩ (r v).val.image = {u,z})
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : Topology.IsEmbedding d)
    (hboundary : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      Set.range f ∪ Set.range g)
    (hempty : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      ((r v).val.image ∪ (r w).val.image))
    (V : Set S) (hV : IsOpen V) (hdV : Set.range d ⊆ V) :
    ∃ k : I, ∃ H : AmbientIsotopy S, ∃ r' : I → EssentialCurve S,
      (k = v ∨ k = w) ∧
      (∀ l, l ≠ k → r' l = r l) ∧
      H.finalMap '' (r k).val.image = (r' k).val.image ∧
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      (∀ l, Quotient.mk (essentialCurveSetoid S) (r' l) =
        Quotient.mk (essentialCurveSetoid S) (r l)) ∧
      (∀ i j, i ≠ j → Transverse (r' i).val (r' j).val) ∧
      (∑ i : I, ∑ j : I, if i = j then 0 else
        ((r' i).val.image ∩ (r' j).val.image).ncard) <
      (∑ i : I, ∑ j : I, if i = j then 0 else
        ((r i).val.image ∩ (r j).val.image).ncard) := by
  classical
  wlog hcheap : (∑ i : I, if i = v ∨ i = w then 0 else
      ((Set.range g \ {u,z}) ∩ (r i).val.image).ncard) ≤
    ∑ i : I, if i = v ∨ i = w then 0 else
      ((Set.range f \ {u,z}) ∩ (r i).val.image).ncard generalizing v w f g
  · have hcheap' : (∑ i : I, if i = w ∨ i = v then 0 else
          ((Set.range f \ {u,z}) ∩ (r i).val.image).ncard) ≤
        ∑ i : I, if i = w ∨ i = v then 0 else
          ((Set.range g \ {u,z}) ∩ (r i).val.image).ncard := by
      simpa only [or_comm] using le_of_lt (lt_of_not_ge hcheap)
    have hboundary' : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
        Set.range g ∪ Set.range f := hboundary.trans (Set.union_comm (Set.range f) (Set.range g))
    have hempty' : Disjoint (d '' {x | x.val ∈ Metric.ball (0 : Plane) 1})
        ((r w).val.image ∪ (r v).val.image) := by
      simpa only [Set.union_comm] using hempty
    obtain ⟨k,H,r',hkw,hfixed,himage,hfix,hclass,htrans,henergy⟩ :=
      this w v (Ne.symm hvw) g f hg hf hg0 hf0 hg1 hf1 hgcurve hfcurve
        hgmeet hfmeet hboundary' hempty' hcheap'
    exact ⟨k,H,r',hkw.elim Or.inr Or.inl,hfixed,himage,hfix,hclass,htrans,henergy⟩
  -- Remaining genuine geometric producer: supported single-component bigon
  -- surgery, preserving classes/transversality and strictly reducing its row.
  -- No minimal-representative or rank certificate is assumed.
  have hgeometry :
    ∃ k : I, ∃ H : AmbientIsotopy S, ∃ r' : I → EssentialCurve S,
      (k = v ∨ k = w) ∧
      (∀ l, l ≠ k → r' l = r l) ∧
      H.finalMap '' (r k).val.image = (r' k).val.image ∧
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      (∀ l, Quotient.mk (essentialCurveSetoid S) (r' l) =
        Quotient.mk (essentialCurveSetoid S) (r l)) ∧
      (∀ i j, i ≠ j → Transverse (r' i).val (r' j).val) ∧
      (∑ j : I, if k = j then 0 else
        ((r' k).val.image ∩ (r' j).val.image).ncard) <
      (∑ j : I, if k = j then 0 else
        ((r k).val.image ∩ (r j).val.image).ncard) := by
    have hSelectedDiskIntersection {S : Type} [TopologicalSpace S]
        (A : Set S) (u z : S) (f g : C(Interval,S))
        (hf0 : f 0 = u) (hf1 : f 1 = z) (hfA : Set.range f ⊆ A)
        (hgA : Set.range g ∩ A = {u,z})
        (d : C(Metric.closedBall (0 : Plane) 1,S))
        (hb : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = Set.range f ∪ Set.range g)
        (he : Disjoint (d '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) A) :
        Set.range d ∩ A = Set.range f := by
      ext x
      constructor
      · rintro ⟨⟨a,rfl⟩,haA⟩
        have ha : dist a.val (0 : Plane) ≤ 1 := a.property
        have has : dist a.val (0 : Plane) = 1 := by
          apply le_antisymm ha
          by_contra hn
          have hai : a ∈ {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.ball (0 : Plane) 1} := by
            change dist a.val (0 : Plane) < 1
            exact lt_of_not_ge hn
          exact Set.disjoint_left.mp he ⟨a,hai,rfl⟩ haA
        have ham : a ∈ {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.sphere (0 : Plane) 1} := by
          change dist a.val (0 : Plane) = 1
          exact has
        have hab : d a ∈ d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} :=
          ⟨a,ham,rfl⟩
        rw [hb] at hab
        rcases hab with hfa | hga
        · exact hfa
        · have hc : d a ∈ ({u,z} : Set S) := hgA ▸ ⟨hga,haA⟩
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hc
          rcases hc with hc | hc
          · exact ⟨0,hf0.trans hc.symm⟩
          · exact ⟨1,hf1.trans hc.symm⟩
      · intro hx
        refine ⟨?_,hfA hx⟩
        have hxb : x ∈ d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} :=
          hb.symm ▸ Or.inl hx
        exact Set.image_subset_range _ _ hxb
    have hActualSideAngles {S : Type} [TopologicalSpace S] [T2Space S]
        (c : Curve S) (f : C(Interval,S)) (hf : Topology.IsEmbedding f)
        (hfcurve : Set.range f ⊆ c.image) (q : Circle) (hq : c.map q ∉ Set.range f) :
        ∃ b : Circle, ∃ a z : ℝ, a < z ∧ z-a < 2*Real.pi ∧
          Set.range f = (fun t => c.map (b * Circle.exp t)) '' Icc a z := by
      classical
      let e := c.embedded.toHomeomorph
      let α : Interval → Circle := fun t => e.symm ⟨f t,hfcurve ⟨t,rfl⟩⟩
      have hα : Continuous α := e.symm.continuous.comp (f.continuous.subtype_mk _)
      have hαf (t : Interval) : c.map (α t) = f t := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨f t,hfcurve ⟨t,rfl⟩⟩)
      have hαinj : Function.Injective α := by
        intro t s he
        apply hf.injective
        exact (hαf t).symm.trans ((congrArg c.map he).trans (hαf s))
      let b : Circle := q * (Circle.exp Real.pi)⁻¹
      let β : Interval → Circle := fun t => b⁻¹ * α t
      have hβ : Continuous β := continuous_const.mul hα
      have hβnot (t : Interval) : β t ≠ Circle.exp Real.pi := by
        intro he
        apply hq
        refine ⟨t,?_⟩
        have hab : α t = q := by
          have hh := congrArg (fun x : Circle => b*x) he
          simpa [β,b,mul_assoc] using hh
        exact (hαf t).symm.trans (congrArg c.map hab)
      have hslit (t : Interval) : (β t : ℂ) ∈ Complex.slitPlane := by
        apply Complex.mem_slitPlane_iff_arg.mpr
        constructor
        · intro he
          apply hβnot t
          rw [← Circle.exp_arg (β t),he]
        · exact Circle.coe_ne_zero _
      let ψ : Interval → ℝ := fun t => Complex.arg (β t : ℂ)
      have hψ : Continuous ψ := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (Complex.continuousAt_arg (hslit t)).comp (f := fun t : Interval => (β t : ℂ))
          (continuous_subtype_val.comp hβ).continuousAt
      have hψinj : Function.Injective ψ := by
        intro t s he
        apply hαinj
        apply mul_left_cancel (a:=b⁻¹)
        change β t = β s
        rw [← Circle.exp_arg (β t),← Circle.exp_arg (β s)]
        exact congrArg Circle.exp he
      have hψbound (t : Interval) : -Real.pi < ψ t ∧ ψ t < Real.pi := by
        refine ⟨Complex.neg_pi_lt_arg _,lt_of_le_of_ne (Complex.arg_le_pi _) ?_⟩
        exact (Complex.mem_slitPlane_iff_arg.mp (hslit t)).1
      have hcompact : IsCompact (Set.range ψ) := isCompact_range hψ
      have hconnected : IsConnected (Set.range ψ) := by
        simpa using isConnected_univ.image ψ hψ.continuousOn
      let a := sInf (Set.range ψ)
      let z := sSup (Set.range ψ)
      have hRange : Set.range ψ = Icc a z := eq_Icc_of_connected_compact hconnected hcompact
      have haR : a ∈ Set.range ψ := hcompact.isClosed.csInf_mem hconnected.nonempty hcompact.bddBelow
      have hzR : z ∈ Set.range ψ := hcompact.isClosed.csSup_mem hconnected.nonempty hcompact.bddAbove
      obtain ⟨ta,hta⟩ := haR
      obtain ⟨tz,htz⟩ := hzR
      have haz : a ≤ z := by
        exact (hRange ▸ (show ψ (0 : Interval) ∈ Set.range ψ from ⟨0,rfl⟩)).1.trans
          (hRange ▸ (show ψ (0 : Interval) ∈ Set.range ψ from ⟨0,rfl⟩)).2
      have hazne : a ≠ z := by
        intro he
        have hconst (t : Interval) : ψ t = a := by
          have hh : ψ t ∈ Icc a z := hRange ▸ ⟨t,rfl⟩
          rw [← he] at hh
          exact le_antisymm hh.2 hh.1
        have ht : (0 : Interval) = 1 := hψinj ((hconst 0).trans (hconst 1).symm)
        have hh := congrArg Subtype.val ht
        norm_num at hh
      have hlen : z-a < 2*Real.pi := by
        have haB := (hψbound ta).1
        have hzB := (hψbound tz).2
        rw [hta] at haB
        rw [htz] at hzB
        linarith
      refine ⟨b,a,z,lt_of_le_of_ne haz hazne,hlen,?_⟩
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨ψ t,hRange ▸ ⟨t,rfl⟩,?_⟩
        change c.map (b * Circle.exp (Complex.arg (β t : ℂ))) = f t
        rw [Circle.exp_arg]
        simpa [β,mul_assoc] using hαf t
      · rintro ⟨θ,hθ,rfl⟩
        obtain ⟨t,ht⟩ := hRange.symm ▸ hθ
        refine ⟨t,?_⟩
        rw [← ht]
        change f t = c.map (b * Circle.exp (Complex.arg (β t : ℂ)))
        rw [Circle.exp_arg]
        simpa [β,mul_assoc] using (hαf t).symm
    have hPaddedRemainder {S : Type} [TopologicalSpace S] [T2Space S]
        (c : Curve S) (b : Circle) (a z : ℝ) (haz : a < z) (hlen : z-a < 2*Real.pi)
        (V D : Set S) (hV : IsOpen V)
        (hFV : (fun t => c.map (b * Circle.exp t)) '' Icc a z ⊆ V)
        (hD : D ∩ c.image = (fun t => c.map (b * Circle.exp t)) '' Icc a z) :
        ∃ A B : ℝ, ∃ K : Set S, A < a ∧ z < B ∧ B-A < 2*Real.pi ∧
          (fun t => c.map (b * Circle.exp t)) '' Icc A B ⊆ V ∧
          IsCompact K ∧
          c.image = (fun t => c.map (b * Circle.exp t)) '' Ioo A B ∪ K ∧
          Disjoint ((fun t => c.map (b * Circle.exp t)) '' Icc a z) K ∧ Disjoint D K := by
      classical
      let γ : ℝ → S := fun t => c.map (b * Circle.exp t)
      have hγ : Continuous γ := c.embedded.continuous.comp (continuous_const.mul Circle.exp.continuous)
      have hpre : IsOpen (γ ⁻¹' V) := hV.preimage hγ
      have haV : a ∈ γ ⁻¹' V := hFV ⟨a,⟨le_rfl,haz.le⟩,rfl⟩
      have hzV : z ∈ γ ⁻¹' V := hFV ⟨z,⟨haz.le,le_rfl⟩,rfl⟩
      obtain ⟨r,hr,hra⟩ := Metric.isOpen_iff.mp hpre a haV
      obtain ⟨s,hs,hsz⟩ := Metric.isOpen_iff.mp hpre z hzV
      let ε := min r (min s ((2*Real.pi-(z-a))/4)) / 2
      have hε : 0 < ε := half_pos (lt_min hr (lt_min hs (by linarith)))
      have hεr : ε < r := by dsimp [ε]; linarith [min_le_left r (min s ((2*Real.pi-(z-a))/4))]
      have hεs : ε < s := by
        have hh := (min_le_right r (min s ((2*Real.pi-(z-a))/4))).trans
          (min_le_left s ((2*Real.pi-(z-a))/4))
        dsimp [ε]; linarith
      have hεlen : 2*ε < 2*Real.pi-(z-a) := by
        have hh := (min_le_right r (min s ((2*Real.pi-(z-a))/4))).trans
          (min_le_right s ((2*Real.pi-(z-a))/4))
        dsimp [ε]; linarith
      let A := a-ε
      let B := z+ε
      have hAa : A < a := by dsimp [A]; linarith
      have hzB : z < B := by dsimp [B]; linarith
      have hpad : γ '' Icc A B ⊆ V := by
        rintro x ⟨t,ht,rfl⟩
        by_cases hta : t < a
        · apply hra
          rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr hta)]
          dsimp [A] at ht
          linarith [ht.1]
        · by_cases hzt : z < t
          · apply hsz
            rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hzt)]
            dsimp [B] at ht
            linarith [ht.2]
          · exact hFV ⟨t,⟨le_of_not_gt hta,le_of_not_gt hzt⟩,rfl⟩
      let T : Set Circle := (fun t : ℝ => b * Circle.exp t) '' Ioo A B
      have hT : IsOpen T := by
        exact ((isOpenMap_mul_left b).comp Circle.isCoveringMap_exp.isOpenMap) _ isOpen_Ioo
      let K : Set S := c.map '' Tᶜ
      have hK : IsCompact K := hT.isClosed_compl.isCompact.image c.embedded.continuous
      have hFK : Disjoint (γ '' Icc a z) K := by
        apply Set.disjoint_left.mpr
        rintro x ⟨t,ht,rfl⟩ ⟨q,hq,he⟩
        have heq : q = b * Circle.exp t := c.embedded.injective he
        apply hq
        exact ⟨t,⟨hAa.trans_le ht.1,ht.2.trans_lt hzB⟩,heq.symm⟩
      refine ⟨A,B,K,hAa,hzB,?_,hpad,hK,?_,hFK,?_⟩
      · dsimp [A,B]; linarith
      · ext x
        constructor
        · rintro ⟨q,rfl⟩
          by_cases hq : q ∈ T
          · obtain ⟨t,ht,rfl⟩ := hq
            exact Or.inl ⟨t,ht,rfl⟩
          · exact Or.inr ⟨q,hq,rfl⟩
        · rintro (⟨t,ht,rfl⟩ | ⟨q,hq,rfl⟩)
          · exact ⟨b * Circle.exp t,rfl⟩
          · exact ⟨q,rfl⟩
      · apply Set.disjoint_left.mpr
        intro x hxD hxK
        have hxc : x ∈ c.image := Set.image_subset_range _ _ hxK
        have hxf : x ∈ γ '' Icc a z := hD ▸ ⟨hxD,hxc⟩
        exact Set.disjoint_left.mp hFK hxf hxK
    have hDcurve : Set.range d ∩ (r v).val.image = Set.range f :=
      hSelectedDiskIntersection (r v).val.image u z f g hf0 hf1 hfcurve hgmeet d
        hboundary (hempty.mono_right Set.subset_union_left)
    have hout : ¬ (r v).val.image ⊆ Set.range d := by
      intro hc
      obtain ⟨e,he,hb,_⟩ := curve_in_embedded_disk_bounds_subdisk (r v).val d hd hc
      exact (r v).property ⟨e,he,hb⟩
    obtain ⟨x,⟨q,rfl⟩,hqD⟩ := Set.not_subset.mp hout
    have hqF : (r v).val.map q ∉ Set.range f := by
      intro hq
      have hh : (r v).val.map q ∈ Set.range d ∩ (r v).val.image := hDcurve.symm ▸ hq
      exact hqD hh.1
    obtain ⟨b,a,zangle,hazangle,hlenangle,hAngleImage⟩ :=
      hActualSideAngles (r v).val f hf hfcurve q hqF
    have hFV : (fun t => (r v).val.map (b * Circle.exp t)) '' Set.Icc a zangle ⊆ V := by
      rw [← hAngleImage]
      intro x hx
      exact hdV ((hDcurve.symm ▸ hx).1)
    have hDangle : Set.range d ∩ (r v).val.image =
        (fun t => (r v).val.map (b * Circle.exp t)) '' Set.Icc a zangle :=
      hDcurve.trans hAngleImage
    obtain ⟨A,B,K,hAa,hzB,hABlen,hPaddedV,hKcompact,hCurveDecomp,hFK,hDK⟩ :=
      hPaddedRemainder (r v).val b a zangle hazangle hlenangle V (Set.range d) hV hFV hDangle
    have hWK : IsOpen (V \ K) := hV.sdiff hKcompact.isClosed
    have hDWK : Set.range d ⊆ V \ K := by
      intro x hx
      exact ⟨hdV hx,fun hk => Set.disjoint_left.mp hDK hx hk⟩
    obtain ⟨Hdisk,dlarge,hdlarge,hDiskInside,hDiskInWK,hDiskImage,hDiskSupportWK,hDiskCenter⟩ :=
      exists_supported_strict_disk_enlargement d hd (V \ K) hWK hDWK
    have hDiskInV : Set.range dlarge ⊆ V := fun x hx => (hDiskInWK hx).1
    have hRemainderFixed : ∀ t x, x ∈ K → Hdisk.map (t,x) = x := by
      intro t x hx
      exact hDiskSupportWK t x (fun h => h.2 hx)
    have hDiskSupport : ∀ t x, x ∉ V → Hdisk.map (t,x) = x := by
      intro t x hx
      exact hDiskSupportWK t x (fun h => hx h.1)
    have hActualDiskChart {S : Type} [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
        (d : C(Metric.closedBall (0 : Plane) 1,S)) (hd : Topology.IsEmbedding d) :
        ∃ E : OpenPartialHomeomorph S Plane,
          E.source = interior (Set.range d) ∧ E.target = Metric.ball (0 : Plane) 1 ∧
          ∀ x : Metric.ball (0 : Plane) 1,
            E (d ⟨x.val,Metric.ball_subset_closedBall x.property⟩) = x.val := by
      classical
      let inclusion : Metric.ball (0 : Plane) 1 → Metric.closedBall (0 : Plane) 1 :=
        fun x => ⟨x.val,Metric.ball_subset_closedBall x.property⟩
      have hi : Topology.IsEmbedding inclusion := by
        apply Topology.IsEmbedding.codRestrict
        exact Topology.IsEmbedding.subtypeVal
      let φ : Metric.ball (0 : Plane) 1 → S := d ∘ inclusion
      have hφ : Topology.IsEmbedding φ := hd.comp hi
      have hrange : Set.range φ = interior (Set.range d) := by
        rw [embedded_surface_disk_interior_eq d hd]
        ext y
        constructor
        · rintro ⟨x,rfl⟩
          exact ⟨inclusion x,x.property,rfl⟩
        · rintro ⟨x,hx,rfl⟩
          exact ⟨⟨x.val,hx⟩,rfl⟩
      have hφopen : Topology.IsOpenEmbedding φ := ⟨hφ,hrange ▸ isOpen_interior⟩
      let U : TopologicalSpace.Opens Plane := ⟨Metric.ball (0 : Plane) 1,isOpen_ball⟩
      have hU : Nonempty U := ⟨⟨0,by simp [U]⟩⟩
      let e : OpenPartialHomeomorph (Metric.ball (0 : Plane) 1) Plane :=
        U.openPartialHomeomorphSubtypeCoe hU
      let E := e.lift_openEmbedding hφopen
      refine ⟨E,?_,?_,?_⟩
      · change φ '' Set.univ = interior (Set.range d)
        rw [Set.image_univ,hrange]
      · simp [E,e,U]
      · intro x
        change E (φ x) = x.val
        exact e.lift_openEmbedding_apply hφopen
    obtain ⟨Edisk,hEdiskSource,hEdiskTarget,hEdiskCoord⟩ := hActualDiskChart dlarge hdlarge
    have hDcurveW : Set.range d ∩ (r w).val.image = Set.range g :=
      hSelectedDiskIntersection (r w).val.image u z g f hg0 hg1 hgcurve hfmeet d
        (hboundary.trans (Set.union_comm _ _)) (hempty.mono_right Set.subset_union_right)
    have houtW : ¬ (r w).val.image ⊆ Set.range d := by
      intro hc
      obtain ⟨e,he,hb,_⟩ := curve_in_embedded_disk_bounds_subdisk (r w).val d hd hc
      exact (r w).property ⟨e,he,hb⟩
    obtain ⟨x,⟨qw,rfl⟩,hqwD⟩ := Set.not_subset.mp houtW
    have hqwG : (r w).val.map qw ∉ Set.range g := by
      intro hq
      exact hqwD ((hDcurveW.symm ▸ hq).1)
    obtain ⟨bg,ag,zg,hagzg,hglen,hGAngleImage⟩ :=
      hActualSideAngles (r w).val g hg hgcurve qw hqwG
    let cw : Curve S := ⟨fun q => (r w).val.map (bg*q),
      (r w).val.embedded.comp (Homeomorph.mulLeft bg).isEmbedding⟩
    have hcwImage : cw.image = (r w).val.image := by
      ext x
      constructor
      · rintro ⟨q,rfl⟩
        exact ⟨bg*q,rfl⟩
      · rintro ⟨q,rfl⟩
        exact ⟨bg⁻¹*q,by simp [cw]⟩
    have hGChartSub : (fun t => cw.map (Circle.exp t)) '' Set.Icc ag zg ⊆
        interior (Set.range dlarge) ∩ Edisk.source := by
      intro x hx
      have hxG : x ∈ Set.range g := hGAngleImage.symm ▸ hx
      have hxD : x ∈ Set.range d := (hDcurveW.symm ▸ hxG).1
      have hxi := hDiskInside hxD
      exact ⟨hxi,hEdiskSource.symm ▸ hxi⟩
    obtain ⟨Eopposite,hOppositeSource,hOppositeSquare,hGInOpposite,hOppositeLeft,
        hOppositeRight,hOppositeAxis,hOppositePatch⟩ :=
      CurveComplex.PositionUniverseV2.position_subarc_crosscut_chart S cw ag zg hagzg hglen
        Edisk (interior (Set.range dlarge)) isOpen_interior hGChartSub
    have hOppositePatchActual :
        {x : S | x ∈ Eopposite.source ∧ Eopposite x ∈ Plane.closedSquare 0 1} ∩
          (r w).val.image = Set.range g := by
      rw [← hcwImage,hOppositePatch]
      exact hGAngleImage.symm
    have hFirstExits {S : Type} [TopologicalSpace S] (γ : ℝ → S) (hγ : Continuous γ)
        (A a z B : ℝ) (hAa : A < a) (haz : a < z) (hzB : z < B)
        (U : Set S) (hU : IsOpen U) (hinside : γ '' Icc a z ⊆ U)
        (hAout : γ A ∉ U) (hBout : γ B ∉ U) :
        ∃ α β : ℝ, A ≤ α ∧ α < a ∧ z < β ∧ β ≤ B ∧
          γ α ∈ frontier U ∧ γ β ∈ frontier U ∧ γ '' Ioo α β ⊆ U := by
      classical
      let p : Path (γ a) (γ A) :=
        ⟨⟨fun t => γ (a+(A-a)*t.val),hγ.comp (by fun_prop)⟩,by simp,by simp⟩
      let q : Path (γ z) (γ B) :=
        ⟨⟨fun t => γ (z+(B-z)*t.val),hγ.comp (by fun_prop)⟩,by simp,by simp⟩
      obtain ⟨s,hs,hsfront,hsbefore⟩ := path_first_exit_frontier p U hU
        (hinside ⟨a,⟨le_rfl,haz.le⟩,rfl⟩) hAout
      obtain ⟨t,ht,htfront,htbefore⟩ := path_first_exit_frontier q U hU
        (hinside ⟨z,⟨haz.le,le_rfl⟩,rfl⟩) hBout
      let α := a+(A-a)*s.val
      let β := z+(B-z)*t.val
      have hspos : 0 < s.val := hs
      have htpos : 0 < t.val := ht
      have hAα : A ≤ α := by dsimp [α]; nlinarith [s.property.2]
      have hαa : α < a := by dsimp [α]; nlinarith
      have hzβ : z < β := by dsimp [β]; nlinarith
      have hβB : β ≤ B := by dsimp [β]; nlinarith [t.property.2]
      refine ⟨α,β,hAα,hαa,hzβ,hβB,hsfront,htfront,?_⟩
      rintro x ⟨θ,hθ,rfl⟩
      by_cases hθa : θ < a
      · let u : unitInterval := ⟨(a-θ)/(a-A),by
          constructor
          · exact (div_pos (by linarith) (by linarith)).le
          · apply (div_le_one (by linarith : 0 < a-A)).mpr
            linarith [hθ.1,hAα]⟩
        have hus : u < s := by
          change (a-θ)/(a-A) < s.val
          apply (div_lt_iff₀ (by linarith : 0 < a-A)).mpr
          dsimp [α] at hθ
          nlinarith [hθ.1]
        have hpθ : p u = γ θ := by
          change γ (a+(A-a)*((a-θ)/(a-A))) = γ θ
          congr 1
          field_simp [ne_of_gt (sub_pos.mpr hAa)]; ring
        rw [← hpθ]
        exact hsbefore u hus
      · by_cases hzθ : z < θ
        · let u : unitInterval := ⟨(θ-z)/(B-z),by
            constructor
            · exact (div_pos (by linarith) (by linarith)).le
            · apply (div_le_one (by linarith : 0 < B-z)).mpr
              linarith [hθ.2,hβB]⟩
          have hut : u < t := by
            change (θ-z)/(B-z) < t.val
            apply (div_lt_iff₀ (by linarith : 0 < B-z)).mpr
            dsimp [β] at hθ
            nlinarith [hθ.2]
          have hqθ : q u = γ θ := by
            change γ (z+(B-z)*((θ-z)/(B-z))) = γ θ
            congr 1
            field_simp [ne_of_gt (sub_pos.mpr hzB)]; ring
          rw [← hqθ]
          exact htbefore u hut
        · exact hinside ⟨θ,⟨le_of_not_gt hθa,le_of_not_gt hzθ⟩,rfl⟩
    have hIntervalArc {S : Type} [TopologicalSpace S] [T2Space S]
        (γ : ℝ → S) (hγ : Continuous γ) (a b : ℝ) (hab : a < b)
        (hi : Set.InjOn γ (Set.Icc a b)) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          Set.range f = γ '' Set.Icc a b ∧ f 0 = γ a ∧ f 1 = γ b := by
      let f : C(Interval,S) := ⟨fun t => γ (a+(b-a)*t.val),hγ.comp (by fun_prop)⟩
      have hparam (t : Interval) : a+(b-a)*t.val ∈ Set.Icc a b := by
        constructor <;> nlinarith [t.property.1,t.property.2]
      have hfi : Function.Injective f := by
        intro t s he
        have hh := hi (hparam t) (hparam s) he
        apply Subtype.ext
        nlinarith
      refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,?_,by simp [f],by simp [f]⟩
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨_,hparam t,rfl⟩
      · rintro ⟨θ,hθ,rfl⟩
        let t : Interval := ⟨(θ-a)/(b-a),by
          constructor
          · exact div_nonneg (sub_nonneg.mpr hθ.1) (by linarith)
          · exact (div_le_one (by linarith : 0 < b-a)).mpr (by linarith [hθ.2])⟩
        refine ⟨t,?_⟩
        change γ (a+(b-a)*((θ-a)/(b-a))) = γ θ
        congr 1
        field_simp [ne_of_gt (sub_pos.mpr hab)]
        ring
    have hDiskDensity {S : Type} [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
        (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
        (hd : Topology.IsEmbedding d) :
        closure (interior (Set.range d)) = Set.range d := by
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
    let γ : ℝ → S := fun t => (r v).val.map (b * Circle.exp t)
    have hγ : Continuous γ := (r v).val.embedded.continuous.comp
      (continuous_const.mul Circle.exp.continuous)
    have hγinj : Set.InjOn γ (Set.Icc A B) := by
      intro t ht s hs he
      exact Circle.exp_injOn_Icc hABlen ht hs
        (mul_left_cancel ((r v).val.embedded.injective he))
    have hEndNot (t : ℝ) (ht : t = A ∨ t = B) : γ t ∉ γ '' Set.Ioo A B := by
      rintro ⟨s,hs,he⟩
      have hts : t = s := hγinj (by rcases ht with rfl | rfl <;>
        exact ⟨by linarith,by linarith⟩) ⟨hs.1.le,hs.2.le⟩ he.symm
      rcases ht with ht | ht
      · rw [← hts,ht] at hs
        exact (lt_irrefl A) hs.1
      · rw [← hts,ht] at hs
        exact (lt_irrefl B) hs.2
    have hEndK (t : ℝ) (ht : t = A ∨ t = B) : γ t ∈ K := by
      have hh : γ t ∈ γ '' Set.Ioo A B ∪ K := hCurveDecomp ▸ ⟨b*Circle.exp t,rfl⟩
      exact hh.resolve_left (hEndNot t ht)
    have hEndOutside (t : ℝ) (ht : t = A ∨ t = B) : γ t ∉ interior (Set.range dlarge) := by
      intro hi
      exact (hDiskInWK (interior_subset hi)).2 (hEndK t ht)
    have hCoreInside : γ '' Set.Icc a zangle ⊆ interior (Set.range dlarge) := by
      intro x hx
      have hfX : x ∈ Set.range f := hAngleImage.symm ▸ hx
      exact hDiskInside ((hDcurve.symm ▸ hfX).1)
    obtain ⟨α,β,hAα,hαa,hzβ,hβB,hαfront,hβfront,hProperInside⟩ :=
      hFirstExits γ hγ A a zangle B hAa hazangle hzB
        (interior (Set.range dlarge)) isOpen_interior hCoreInside
        (hEndOutside A (Or.inl rfl)) (hEndOutside B (Or.inr rfl))
    have hαβ : α < β := hαa.trans (hazangle.trans hzβ)
    have hProperInjective : Set.InjOn γ (Set.Icc α β) :=
      hγinj.mono (Set.Icc_subset_Icc hAα hβB)
    obtain ⟨properArc,hProperEmbedding,hProperRange,hProperZero,hProperOne⟩ :=
      hIntervalArc γ hγ α β hαβ hProperInjective
    have hLargeClosure : closure (interior (Set.range dlarge)) = Set.range dlarge :=
      hDiskDensity dlarge hdlarge
    have hProperFrontier : frontier (interior (Set.range dlarge)) = frontier (Set.range dlarge) := by
      rw [frontier,hLargeClosure,isOpen_interior.interior_eq,
        (isCompact_range dlarge.continuous).isClosed.frontier_eq]
    have hProperEndpoints : properArc 0 ∈ frontier (Set.range dlarge) ∧
        properArc 1 ∈ frontier (Set.range dlarge) := by
      rw [hProperZero,hProperOne,← hProperFrontier]
      exact ⟨hαfront,hβfront⟩
    have hOriginalSideInProper : Set.range f ⊆ Set.range properArc := by
      rw [hAngleImage,hProperRange]
      apply Set.image_mono
      exact Set.Icc_subset_Icc hαa.le hzβ.le
    have hProperInterior : properArc '' Set.Ioo (0 : Interval) 1 ⊆ interior (Set.range dlarge) := by
      rintro x ⟨t,ht,rfl⟩
      have htRange : properArc t ∈ γ '' Set.Icc α β := hProperRange ▸ ⟨t,rfl⟩
      obtain ⟨θ,hθ,hθeq⟩ := htRange
      have hθα : θ ≠ α := by
        intro he
        subst θ
        have ht0 : t = 0 := hProperEmbedding.injective (hθeq.symm.trans hProperZero.symm)
        exact (ne_of_gt ht.1) ht0
      have hθβ : θ ≠ β := by
        intro he
        subst θ
        have ht1 : t = 1 := hProperEmbedding.injective (hθeq.symm.trans hProperOne.symm)
        exact (ne_of_lt ht.2) ht1
      exact hProperInside ⟨θ,⟨lt_of_le_of_ne hθ.1 (Ne.symm hθα),
        lt_of_le_of_ne hθ.2 hθβ⟩,hθeq⟩
    have hProperInSelected : Set.range properArc ⊆ (r v).val.image := by
      rw [hProperRange]
      rintro x ⟨θ,hθ,rfl⟩
      exact ⟨b*Circle.exp θ,rfl⟩
    have hCornerIsolation
        (r : I → EssentialCurve S)
        (hr : ∀ i j, i ≠ j → Transverse (r i).val (r j).val)
        (u z : S) (huz : u ≠ z) (V : Set S) (hV : IsOpen V)
        (huV : u ∈ V) (hzV : z ∈ V) :
        ∃ U W : Set S, IsOpen U ∧ IsOpen W ∧ u ∈ U ∧ z ∈ W ∧
          U ⊆ V ∧ W ⊆ V ∧ Disjoint U W ∧
          (∀ i, u ∉ (r i).val.image → Disjoint U (r i).val.image) ∧
          (∀ i, z ∉ (r i).val.image → Disjoint W (r i).val.image) ∧
          (∀ i j, i ≠ j → U ∩ ((r i).val.image ∩ (r j).val.image) ⊆ {u}) ∧
          (∀ i j, i ≠ j → W ∩ ((r i).val.image ∩ (r j).val.image) ⊆ {z}) := by
      classical
      let P : Set S := ⋃ i, ⋃ j, if i = j then ∅ else
        (r i).val.image ∩ (r j).val.image
      have hP : P.Finite := by
        apply Set.finite_iUnion
        intro i
        apply Set.finite_iUnion
        intro j
        split_ifs with hij
        · exact Set.finite_empty
        · exact (hr i j hij).1
      let bad (p : S) : Set S := (P \ {p}) ∪
        ⋃ i, if p ∈ (r i).val.image then ∅ else (r i).val.image
      have hbad (p : S) : IsClosed (bad p) := by
        apply (hP.sdiff (t := {p})).isClosed.union
        apply isClosed_iUnion_of_finite
        intro i
        split_ifs
        · exact isClosed_empty
        · exact (isCompact_range (r i).val.embedded.continuous).isClosed
      have hpbad (p : S) : p ∉ bad p := by
        rintro (hp | hp)
        · exact hp.2 (Set.mem_singleton p)
        · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
          by_cases hp : p ∈ (r i).val.image
          · simp only [ite_eq_left hp,Set.mem_empty_iff_false] at hi
          · exact hp (by simpa only [ite_eq_right hp] using hi)
      obtain ⟨A,B,hA,hB,huA,hzB,hAB⟩ := t2_separation huz
      let U := A ∩ (V ∩ (bad u)ᶜ)
      let W := B ∩ (V ∩ (bad z)ᶜ)
      have hlocal (p : S) (Q : Set S) (hQ : Q ⊆ (bad p)ᶜ) :
          (∀ i, p ∉ (r i).val.image → Disjoint Q (r i).val.image) ∧
          (∀ i j, i ≠ j → Q ∩ ((r i).val.image ∩ (r j).val.image) ⊆ {p}) := by
        constructor
        · intro i hp
          apply Set.disjoint_left.mpr
          intro x hx hxi
          exact hQ hx (Or.inr (Set.mem_iUnion.mpr ⟨i,by simpa only [ite_eq_right hp] using hxi⟩))
        · intro i j hij x hx
          by_contra hxp
          apply hQ hx.1
          left
          refine ⟨?_,hxp⟩
          exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,by simpa only [ite_eq_right hij] using hx.2⟩⟩
      obtain ⟨hUnon,hUint⟩ := hlocal u U (fun _ hx => hx.2.2)
      obtain ⟨hWnon,hWint⟩ := hlocal z W (fun _ hx => hx.2.2)
      exact ⟨U,W,hA.inter (hV.inter (hbad u).isOpen_compl),
        hB.inter (hV.inter (hbad z).isOpen_compl),
        ⟨huA,huV,hpbad u⟩,⟨hzB,hzV,hpbad z⟩,
        (fun _ hx => hx.2.1),(fun _ hx => hx.2.1),
        hAB.mono Set.inter_subset_left Set.inter_subset_left,
        hUnon,hWnon,hUint,hWint⟩
    have huV : u ∈ V := hdV ((hDcurve.symm ▸ (show u ∈ Set.range f from ⟨0,hf0⟩)).1)
    have hzV : z ∈ V := hdV ((hDcurve.symm ▸ (show z ∈ Set.range f from ⟨1,hf1⟩)).1)
    obtain ⟨Ucorner,Zcorner,hUcorner,hZcorner,huCorner,hzCorner,hUcornerV,hZcornerV,
        hCornersDisjoint,hUNonincident,hZNonincident,hUContacts,hZContacts⟩ :=
      hCornerIsolation r hr u z huz (V ∩ interior (Set.range dlarge))
        (hV.inter isOpen_interior)
        ⟨huV,hDiskInside ((hDcurve.symm ▸ (show u ∈ Set.range f from ⟨0,hf0⟩)).1)⟩
        ⟨hzV,hDiskInside ((hDcurve.symm ▸ (show z ∈ Set.range f from ⟨1,hf1⟩)).1)⟩
    have huSelected : u ∈ (r v).val.image := hfcurve ⟨0,hf0⟩
    have hzSelected : z ∈ (r v).val.image := hfcurve ⟨1,hf1⟩
    have hSameArcEndpoints (f g : C(Interval,S))
        (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
        (hRange : Set.range f = Set.range g) :
        (f 0 = g 0 ∧ f 1 = g 1) ∨ (f 0 = g 1 ∧ f 1 = g 0) := by
      let e : Interval ≃ₜ Interval := hf.toHomeomorph.trans
        ((Homeomorph.setCongr hRange).trans hg.toHomeomorph.symm)
      have hComm (t : Interval) : g (e t) = f t := by
        have he : hg.toHomeomorph (e t) = Homeomorph.setCongr hRange (hf.toHomeomorph t) := by
          change hg.toHomeomorph (hg.toHomeomorph.symm _) = _
          exact hg.toHomeomorph.apply_symm_apply _
        exact congrArg Subtype.val he
      have hCont : Continuous (fun t : Interval => (e t).val) := continuous_subtype_val.comp e.continuous
      have hInj : Function.Injective (fun t : Interval => (e t).val) := by
        intro s t h
        exact e.injective (Subtype.ext h)
      rcases hCont.strictMono_of_inj_boundedOrder' hInj with hm | ha
      · have h0 : e 0 = (0 : Interval) := by
          obtain ⟨t,ht⟩ := e.surjective 0
          have hn := hm.monotone (show (0 : Interval) ≤ t from t.property.1)
          rw [ht] at hn
          apply Subtype.ext
          exact le_antisymm hn (e 0).property.1
        have h1 : e 1 = (1 : Interval) := by
          obtain ⟨t,ht⟩ := e.surjective 1
          have hn := hm.monotone (show t ≤ (1 : Interval) from t.property.2)
          rw [ht] at hn
          apply Subtype.ext
          exact le_antisymm (e 1).property.2 hn
        left
        exact ⟨by simpa [h0] using (hComm 0).symm,by simpa [h1] using (hComm 1).symm⟩
      · have h0 : e 0 = (1 : Interval) := by
          obtain ⟨t,ht⟩ := e.surjective 1
          have hn := ha.antitone (show (0 : Interval) ≤ t from t.property.1)
          rw [ht] at hn
          apply Subtype.ext
          exact le_antisymm (e 0).property.2 hn
        have h1 : e 1 = (0 : Interval) := by
          obtain ⟨t,ht⟩ := e.surjective 0
          have hn := ha.antitone (show t ≤ (1 : Interval) from t.property.2)
          rw [ht] at hn
          apply Subtype.ext
          exact le_antisymm hn (e 1).property.1
        right
        exact ⟨by simpa [h0] using (hComm 0).symm,by simpa [h1] using (hComm 1).symm⟩
    have hCoreγInj : Set.InjOn γ (Set.Icc a zangle) := by
      intro t ht s hs he
      exact hγinj (by constructor <;> linarith [ht.1,ht.2])
        (by constructor <;> linarith [hs.1,hs.2]) he
    obtain ⟨selectedAngularArc,hSelectedAngularArc,hSelectedAngularRange,hSelectedAngular0,hSelectedAngular1⟩ :=
      hIntervalArc γ hγ a zangle hazangle hCoreγInj
    have hSelectedEndpointOrientation :
        (u = γ a ∧ z = γ zangle) ∨ (u = γ zangle ∧ z = γ a) := by
      have hh := hSameArcEndpoints f selectedAngularArc hf hSelectedAngularArc
        (hAngleImage.trans hSelectedAngularRange.symm)
      simpa [hf0,hf1,hSelectedAngular0,hSelectedAngular1] using hh
    have hCoreWithArms {S : Type} [TopologicalSpace S] [T2Space S]
        {J : Type} [Fintype J] (c : J → Curve S) (p : S)
        (hp : ∀ j, p ∈ (c j).image)
        (E : OpenPartialHomeomorph S Plane) (hEp : E p = 0)
        (U : Set S) (hU : IsOpen U) (hpU : p ∈ U) (hUE : U ⊆ E.source)
        (hmeet : ∀ i j, i ≠ j → U ∩ ((c i).image ∩ (c j).image) ⊆ {p})
        (j₀ : J) :
        ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi ∧
          ∃ q : J → Circle, (∀ j, (c j).map (q j) = p) ∧
          (∀ j (sign : Bool) (t : CurveComplex.Interval),
            (c j).map (q j * Circle.exp (if sign then ε*t.val else -(ε*t.val))) ∈ U) ∧
          let γ : (J × Bool) → CurveComplex.Interval → Plane := fun j t =>
            E ((c j.1).map (q j.1 * Circle.exp (if j.2 then ε*t.val else -(ε*t.val))))
          (∀ j, Topology.IsClosedEmbedding (γ j)) ∧ (∀ j, γ j zeroI = 0) ∧
          ∃ R : RadializedStar γ 0 (E '' U),
            R.vector (j₀,true) = -R.vector (j₀,false) ∧
            ∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
              (x ∈ (c j).image ↔ R.H (E x) ∈
                segment ℝ (0 : Plane) (R.vector (j,false)) ∪
                segment ℝ (0 : Plane) (R.vector (j,true))) := by
      classical
      have hex : ∀ j, ∃ q : Circle, (c j).map q = p := hp
      choose q hq using hex
      let ψ : J → ℝ → S := fun j t => (c j).map (q j * Circle.exp t)
      have hψ : ∀ j, Continuous (ψ j) := fun j =>
        (c j).embedded.continuous.comp (continuous_const.mul Circle.exp.continuous)
      have hψ0 (j : J) : ψ j 0 = p := by simp [ψ,hq]
      have hPre : IsOpen (⋂ j, ψ j ⁻¹' U) := isOpen_iInter_of_finite
        (fun j => hU.preimage (hψ j))
      have h0Pre : (0 : ℝ) ∈ ⋂ j, ψ j ⁻¹' U := by
        apply Set.mem_iInter.mpr
        intro j
        simpa [hψ0] using hpU
      obtain ⟨r,hr,hrr⟩ := Metric.isOpen_iff.mp hPre 0 h0Pre
      let ε := min r Real.pi / 2
      have hε : 0 < ε := half_pos (lt_min hr Real.pi_pos)
      have hεr : ε < r := by dsimp [ε]; linarith [min_le_left r Real.pi]
      have hεπ : ε < Real.pi := by dsimp [ε]; linarith [min_le_right r Real.pi,Real.pi_pos]
      have hSmall (j : J) (t : ℝ) (ht : t ∈ Icc (-ε) ε) : ψ j t ∈ U := by
        have htball : t ∈ Metric.ball (0 : ℝ) r := by
          rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
          constructor <;> linarith [ht.1,ht.2]
        exact Set.mem_iInter.mp (hrr htball) j
      let θ : (J × Bool) → CurveComplex.Interval → ℝ := fun j t =>
        if j.2 then ε*t.val else -(ε*t.val)
      have hθ (j : J × Bool) (t : CurveComplex.Interval) : θ j t ∈ Icc (-ε) ε := by
        dsimp [θ]
        split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2]
      let γ : (J × Bool) → CurveComplex.Interval → Plane := fun j t => E (ψ j.1 (θ j t))
      have hγU (j : J × Bool) (t : CurveComplex.Interval) : ψ j.1 (θ j t) ∈ U :=
        hSmall j.1 _ (hθ j t)
      have hγcont (j : J × Bool) : Continuous (γ j) := by
        have hc : Continuous (fun t : CurveComplex.Interval => ψ j.1 (θ j t)) :=
          (hψ j.1).comp (by dsimp [θ]; split_ifs <;> fun_prop)
        exact E.continuousOn.comp_continuous hc (fun t => hUE (hγU j t))
      have hγ0 (j : J × Bool) : γ j zeroI = 0 := by
        have hh : θ j zeroI = 0 := by simp [θ,zeroI]
        simp only [γ,hh,hψ0,hEp]
      have hγinj (j : J × Bool) : Function.Injective (γ j) := by
        intro t s he
        have hs := E.injOn (hUE (hγU j t)) (hUE (hγU j s)) he
        have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
          (hθ j t) (hθ j s) (mul_left_cancel ((c j.1).embedded.injective hs))
        apply Subtype.ext
        dsimp [θ] at hang
        split_ifs at hang <;> nlinarith
      have hγclosed (j : J × Bool) : Topology.IsClosedEmbedding (γ j) :=
        (hγcont j).isClosedEmbedding (hγinj j)
      have hγmeet (i j : J × Bool) (hij : i ≠ j) : Set.range (γ i) ∩ Set.range (γ j) = {0} := by
        apply Set.Subset.antisymm
        · rintro x ⟨⟨t,rfl⟩,⟨s,he⟩⟩
          have heS := E.injOn (hUE (hγU j s)) (hUE (hγU i t)) he
          by_cases hlabels : i.1 = j.1
          · have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
              (hθ j s) (hθ i t) (mul_left_cancel ((c i.1).embedded.injective (by simpa [hlabels] using heS)))
            have hsign : i.2 ≠ j.2 := by
              intro heq
              exact hij (Prod.ext hlabels heq)
            have ht0 : t.val = 0 := by
              dsimp [θ] at hang
              cases hi : i.2 <;> cases hj : j.2
              · exact False.elim (hsign (hi.trans hj.symm))
              · simp [hi,hj] at hang
                nlinarith [s.property.1,t.property.1]
              · simp [hi,hj] at hang
                nlinarith [s.property.1,t.property.1]
              · exact False.elim (hsign (hi.trans hj.symm))
            have htZ : t = zeroI := Subtype.ext ht0
            rw [htZ,hγ0]
            exact Set.mem_singleton 0
          · have hc : ψ i.1 (θ i t) ∈ ({p} : Set S) :=
              hmeet i.1 j.1 hlabels ⟨hγU i t,⟨⟨q i.1 * Circle.exp (θ i t),rfl⟩,
                heS ▸ ⟨q j.1 * Circle.exp (θ j s),rfl⟩⟩⟩
            change ψ i.1 (θ i t) = p at hc
            change E (ψ i.1 (θ i t)) ∈ ({0} : Set Plane)
            rw [hc,hEp]
            exact Set.mem_singleton 0
        · rintro x rfl
          exact ⟨⟨zeroI,hγ0 i⟩,⟨zeroI,hγ0 j⟩⟩
      let C : J → Set Circle := fun j => (fun t : ℝ => q j * Circle.exp t) '' Ioo (-ε) ε
      have hCopen (j : J) : IsOpen (C j) :=
        ((isOpenMap_mul_left (q j)).comp Circle.isCoveringMap_exp.isOpenMap) _ isOpen_Ioo
      let K : J → Set S := fun j => (c j).map '' (C j)ᶜ
      have hKcompact (j : J) : IsCompact (K j) :=
        (hCopen j).isClosed_compl.isCompact.image (c j).embedded.continuous
      let bad : Set S := ⋃ j, K j
      have hBadClosed : IsClosed bad := isClosed_iUnion_of_finite (fun j => (hKcompact j).isClosed)
      have hpBad : p ∉ bad := by
        intro hpB
        obtain ⟨j,z,hz,hzp⟩ := Set.mem_iUnion.mp hpB
        have hzq : z = q j := (c j).embedded.injective (hzp.trans (hq j).symm)
        apply hz
        exact ⟨0,⟨by linarith, hε⟩,by simpa using hzq.symm⟩
      let W := U \ bad
      have hW : IsOpen W := hU.sdiff hBadClosed
      have hpW : p ∈ W := ⟨hpU,hpBad⟩
      have hWE : W ⊆ E.source := fun x hx => hUE hx.1
      have hPlaneW : IsOpen (E '' W) := E.isOpen_image_of_subset_source hW hWE
      have h0PlaneW : (0 : Plane) ∈ E '' W := ⟨p,hpW,hEp⟩
      obtain ⟨R₀,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero γ hγclosed hγ0 hγmeet
        (j₀,false) (j₀,true) (by simp) (E '' W) hPlaneW h0PlaneW
      let R : RadializedStar γ 0 (E '' U) := {R₀ with
        support_subset := R₀.support_subset.trans (Set.image_mono Set.sdiff_subset)}
      have hNotK (j : J) (x : S) (hxE : x ∈ E.source)
          (hxN : ‖R.H (E x)‖ ≤ R.coreRadius) : x ∉ K j := by
        intro hxK
        have hxPlane : E x ∉ E '' W := by
          rintro ⟨y,hy,he⟩
          have hyx : y = x := E.injOn (hWE hy) hxE he
          exact hy.2 (hyx.symm ▸ Set.mem_iUnion.mpr ⟨j,hxK⟩)
        have hxOut : E x ∉ Metric.ball (0 : Plane) R₀.supportRadius := by
          intro hx
          exact hxPlane (R₀.support_subset (Metric.ball_subset_closedBall hx))
        have hxFix : R.H (E x) = E x := R₀.fixes_exterior _ hxOut
        rw [hxFix] at hxN
        have hxBall : E x ∈ Metric.closedBall (0 : Plane) R₀.supportRadius := by
          rw [Metric.mem_closedBall,dist_zero_right]
          exact hxN.trans R₀.core_lt_support.le
        exact hxPlane (R₀.support_subset hxBall)
      have hGammaCover (j : J) (x : S) (hx : x ∈ (c j).image) (hxK : x ∉ K j) :
          ∃ sign : Bool, ∃ t : CurveComplex.Interval, γ (j,sign) t = E x := by
        obtain ⟨z,hzx⟩ := hx
        have hzC : z ∈ C j := by
          by_contra hn
          exact hxK ⟨z,hn,hzx⟩
        obtain ⟨a,ha,haz⟩ := hzC
        change q j * Circle.exp a = z at haz
        by_cases hapos : 0 ≤ a
        · let t : CurveComplex.Interval := ⟨a/ε,⟨div_nonneg hapos hε.le,
            (div_le_one hε).mpr ha.2.le⟩⟩
          refine ⟨true,t,?_⟩
          have hmul : ε*t.val = a := by dsimp [t]; field_simp
          change E ((c j).map (q j * Circle.exp (ε*t.val))) = E x
          rw [hmul,haz,hzx]
        · let t : CurveComplex.Interval := ⟨(-a)/ε,⟨div_nonneg (by linarith) hε.le,
            (div_le_one hε).mpr (by linarith [ha.1])⟩⟩
          refine ⟨false,t,?_⟩
          have hmul : -(ε*t.val) = a := by dsimp [t]; field_simp
          change E ((c j).map (q j * Circle.exp (-(ε*t.val)))) = E x
          rw [hmul,haz,hzx]
      refine ⟨ε,hε,hεπ,q,hq,(fun j sign t => hγU (j,sign) t),hγclosed,hγ0,R,hRop,?_⟩
      intro j x hxE hxN
      constructor
      · intro hx
        obtain ⟨sign,t,htx⟩ := hGammaCover j x hx (hNotK j x hxE hxN)
        have hcut : t.val ≤ (R.cut (j,sign)).val := by
          by_contra hn
          have htail : R.H (γ (j,sign) t) ∈ R.H '' tail γ (j,sign) (R.cut (j,sign)) :=
            ⟨γ (j,sign) t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
          have hball : R.H (γ (j,sign) t) ∈ Metric.closedBall (0 : Plane) R.coreRadius := by
            rw [htx,Metric.mem_closedBall,dist_zero_right]
            exact hxN
          exact Set.disjoint_left.mp (R.excludes_tails (j,sign)) htail hball
        have hray : R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,sign)) := by
          have hh : R.H (γ (j,sign) t) ∈ R.H '' armPrefix γ (j,sign) (R.cut (j,sign)) :=
            ⟨γ (j,sign) t,⟨t,hcut,rfl⟩,rfl⟩
          simpa only [R.prefix_image,zero_add,htx] using hh
        cases sign
        · exact Or.inl hray
        · exact Or.inr hray
      · intro hx
        have hRecover (sign : Bool) (hray : R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,sign))) :
            x ∈ (c j).image := by
          have hh : R.H (E x) ∈ R.H '' armPrefix γ (j,sign) (R.cut (j,sign)) := by
            rw [R.prefix_image,zero_add]
            exact hray
          obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
          have hEx : γ (j,sign) t = E x := R.H.injective he
          have hsx : ψ j (θ (j,sign) t) = x := E.injOn (hUE (hγU (j,sign) t)) hxE hEx
          exact ⟨q j * Circle.exp (θ (j,sign) t),hsx⟩
        exact hx.elim (hRecover false) (hRecover true)
    have hActualCorner (r : I → EssentialCurve S) (hr : ∀ i j, i ≠ j → Transverse (r i).val (r j).val) (v : I) (p : S) (Q : Set S) (hQ : IsOpen Q) (hpQ : p ∈ Q)
        (hpv : p ∈ (r v).val.image)
        (hQcontacts : ∀ i j, i ≠ j → Q ∩ ((r i).val.image ∩ (r j).val.image) ⊆ {p}) :
        ∃ E : OpenPartialHomeomorph S Plane, ∃ ε : ℝ,
          p ∈ E.source ∧ E p = 0 ∧ E.source ⊆ Q ∧ 0 < ε ∧ ε < Real.pi ∧
          let J := {i : I // p ∈ (r i).val.image}
          let e := Fintype.equivFin J
          ∃ q : Fin (Fintype.card J) → Circle,
            (∀ j, (r (e.symm j).val).val.map (q j) = p) ∧
            (∀ j (sign : Bool) (t : Interval),
              (r (e.symm j).val).val.map (q j * Circle.exp (if sign then ε*t.val else -(ε*t.val))) ∈ E.source) ∧
            let γ : (Fin (Fintype.card J) × Bool) → Interval → Plane := fun j t =>
              E ((r (e.symm j.1).val).val.map
                (q j.1 * Circle.exp (if j.2 then ε*t.val else -(ε*t.val))))
            (∀ j, Topology.IsClosedEmbedding (γ j)) ∧ (∀ j, γ j zeroI = 0) ∧
            ∃ R : RadializedStar γ 0 (E '' E.source),
              R.vector (e ⟨v,hpv⟩,true) = -R.vector (e ⟨v,hpv⟩,false) ∧
              ∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
                (x ∈ (r (e.symm j).val).val.image ↔ R.H (E x) ∈
                  segment ℝ (0 : Plane) (R.vector (j,false)) ∪
                  segment ℝ (0 : Plane) (R.vector (j,true))) := by
      obtain ⟨E,hpE,hEp,hEQ,hEsquare,hEaxis⟩ :=
        CurveComplex.PositionUniverseV2.position_curve_crosscut_chart S (r v).val p hpv Q hQ hpQ
      let J := {i : I // p ∈ (r i).val.image}
      let e := Fintype.equivFin J
      let c : Fin (Fintype.card J) → Curve S := fun j => (r (e.symm j).val).val
      have hcpoint : ∀ j, p ∈ (c j).image := fun j => (e.symm j).property
      have hcmeet : ∀ i j, i ≠ j → E.source ∩ ((c i).image ∩ (c j).image) ⊆ {p} := by
        intro i j hij x hx
        have hlabels : (e.symm i).val ≠ (e.symm j).val := by
          intro he
          exact hij (e.symm.injective (Subtype.ext he))
        exact hQcontacts _ _ hlabels ⟨hEQ hx.1,hx.2⟩
      obtain ⟨ε,hε,hεπ,q,hq,hArms,hClosed,hZero,R,hRop,hCore⟩ := hCoreWithArms c p hcpoint E hEp
        E.source E.open_source hpE Set.Subset.rfl hcmeet (e ⟨v,hpv⟩)
      exact ⟨E,ε,hpE,hEp,hEQ,hε,hεπ,q,hq,hArms,hClosed,hZero,R,hRop,hCore⟩
    obtain ⟨EcornerU,εU,huEcornerU,hEcornerU0,hEcornerUSub,hεU,hεUπ,
        qU,hqU,hArmsUSource,hArmsUClosed,hArmsUZero,RU,hRUOpposite,hRUCore⟩ :=
      hActualCorner r hr v u Ucorner hUcorner huCorner huSelected hUContacts
    obtain ⟨EcornerZ,εZ,hzEcornerZ,hEcornerZ0,hEcornerZSub,hεZ,hεZπ,
        qZ,hqZ,hArmsZSource,hArmsZClosed,hArmsZZero,RZ,hRZOpposite,hRZCore⟩ :=
      hActualCorner r hr v z Zcorner hZcorner hzCorner hzSelected hZContacts
    have hStraightCore {S : Type} [TopologicalSpace S] [T2Space S]
        {J : Type} [Fintype J] (c : J → Curve S) (p : S)
        (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
        (γ : (J × Bool) → CurveComplex.Interval → Plane)
        (R : RadializedStar γ 0 (E '' E.source)) (j₀ : J)
        (hop : R.vector (j₀,true) = -R.vector (j₀,false)) (β : Bool)
        (hcore : ∀ j x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
          (x ∈ (c j).image ↔ R.H (E x) ∈ segment ℝ (0 : Plane) (R.vector (j,false)) ∪
            segment ℝ (0 : Plane) (R.vector (j,true)))) :
        ∃ T : Plane ≃L[ℝ] Plane, ∃ F : OpenPartialHomeomorph S Plane, ∃ ρ : ℝ,
          F.source = E.source ∧ F p = 0 ∧ 0 < ρ ∧ ρ < 1 ∧
          (∀ x, F x = T (R.H (E x))) ∧ T (R.vector (j₀,β)) = Plane.mk 1 0 ∧
          (∀ x, ‖F x‖ < ρ → ‖R.H (E x)‖ ≤ R.coreRadius) ∧
          (∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ (c j₀).image ↔ F x 1 = 0)) ∧
          (∀ j x, x ∈ F.source → ‖F x‖ < ρ →
            (x ∈ (c j).image ↔ F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,false))) ∪
              segment ℝ (0 : Plane) (T (R.vector (j,true))))) := by
      classical
      have hLinear (v : Plane) (hv : v ≠ 0) :
          ∃ T : Plane ≃L[ℝ] Plane, T v = Plane.mk 1 0 ∧
            T (-v) = Plane.mk (-1) 0 ∧ ∀ t : ℝ, T (t • v) = Plane.mk t 0 := by
        let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
          ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
            (EuclideanSpace.equiv (Fin 2) ℝ).symm)
        let ζ : ℂ := L.symm v
        have hζ : ζ ≠ 0 := by
          intro hz
          apply hv
          have hh := congrArg L hz
          simpa [ζ] using hh
        let M : ℂ ≃L[ℂ] ℂ := (LinearEquiv.smulOfNeZero ℂ ℂ ζ⁻¹ (inv_ne_zero hζ)).toContinuousLinearEquiv
        let T : Plane ≃L[ℝ] Plane := L.symm.trans ((M.restrictScalars ℝ).trans L)
        have hTv : T v = Plane.mk 1 0 := by
          change L (ζ⁻¹ * ζ) = Plane.mk 1 0
          rw [inv_mul_cancel₀ hζ]
          rfl
        refine ⟨T,hTv,?_,?_⟩
        · rw [map_neg,hTv]
          ext i
          fin_cases i <;> simp [Plane.mk]
        · intro t
          rw [map_smul,hTv]
          ext i
          fin_cases i <;> simp [Plane.mk]
      obtain ⟨T,hTv,hTneg,hTline⟩ := hLinear (R.vector (j₀,β)) (R.vector_nonzero (j₀,β))
      let F := E.transHomeomorph (R.H.trans T.toHomeomorph)
      have hFp : F p = 0 := by
        change T (R.H (E p)) = 0
        rw [hEp,R.fixes_center,map_zero]
      have hOpen : IsOpen (T.symm ⁻¹' Metric.ball (0 : Plane) R.coreRadius) :=
        isOpen_ball.preimage T.symm.continuous
      have h0 : (0 : Plane) ∈ T.symm ⁻¹' Metric.ball (0 : Plane) R.coreRadius := by
        change T.symm 0 ∈ Metric.ball (0 : Plane) R.coreRadius
        rw [map_zero]
        simpa using R.core_pos
      obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hOpen 0 h0
      let ρ := min r 1 / 2
      have hρ : 0 < ρ := half_pos (lt_min hr zero_lt_one)
      have hρr : ρ < r := by dsimp [ρ]; linarith [min_le_left r 1]
      have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [min_le_right r 1]
      have hCoreNorm (x : S) (hx : ‖F x‖ < ρ) : ‖R.H (E x)‖ ≤ R.coreRadius := by
        have hh : T.symm (F x) ∈ Metric.ball (0 : Plane) R.coreRadius :=
          hBall (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hx.trans hρr))
        change T.symm (T (R.H (E x))) ∈ Metric.ball (0 : Plane) R.coreRadius at hh
        rw [T.symm_apply_apply,Metric.mem_ball,dist_zero_right] at hh
        exact hh.le
      have hSegment (v z : Plane) : z ∈ segment ℝ (0 : Plane) v ↔
          T z ∈ segment ℝ (0 : Plane) (T v) := by
        have hi := image_segment ℝ T.toLinearMap.toAffineMap (0 : Plane) v
        change T '' segment ℝ (0 : Plane) v = segment ℝ (T 0) (T v) at hi
        rw [map_zero] at hi
        rw [← hi]
        exact ⟨fun hz => ⟨z,hz,rfl⟩,fun ⟨w,hw,he⟩ => (T.injective he) ▸ hw⟩
      have hModel (j : J) (x : S) (hxE : x ∈ F.source) (hxN : ‖F x‖ < ρ) :
          x ∈ (c j).image ↔ F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,false))) ∪
            segment ℝ (0 : Plane) (T (R.vector (j,true))) := by
        rw [hcore j x hxE (hCoreNorm x hxN)]
        exact or_congr (hSegment _ _) (hSegment _ _)
      have hAxisModel (z : Plane) (hz : ‖z‖ < 1) :
          z ∈ segment ℝ (0 : Plane) (Plane.mk 1 0) ∪ segment ℝ (0 : Plane) (Plane.mk (-1) 0) ↔ z 1 = 0 := by
        constructor
        · intro hseg
          have hzero (v : Plane) (hv : v 1 = 0) (hz : z ∈ segment ℝ (0 : Plane) v) : z 1 = 0 := by
            rw [segment_eq_image'] at hz
            obtain ⟨t,ht,he⟩ := hz
            have hh := congrArg (fun z : Plane => z 1) he
            change 0+t*(v 1-0) = z 1 at hh
            rw [hv] at hh
            simpa using hh.symm
          exact hseg.elim (hzero _ rfl) (hzero _ rfl)
        · intro hz1
          have hxabs : |z 0| < 1 := (show ‖z 0‖ ≤ ‖z‖ from PiLp.norm_apply_le z 0).trans_lt hz
          by_cases hx : 0 ≤ z 0
          · left
            rw [segment_eq_image']
            refine ⟨z 0,⟨hx,(abs_lt.mp hxabs).2.le⟩,?_⟩
            ext i
            fin_cases i <;> simp [Plane.mk,hz1]
          · right
            rw [segment_eq_image']
            refine ⟨-z 0,⟨by linarith,(by linarith [(abs_lt.mp hxabs).1])⟩,?_⟩
            ext i
            fin_cases i <;> simp [Plane.mk,hz1]
      refine ⟨T,F,ρ,rfl,hFp,hρ,hρ1,(fun _ => rfl),hTv,hCoreNorm,?_,hModel⟩
      intro x hxE hxN
      cases β
      · rw [hModel j₀ x hxE hxN,hop,hTv,hTneg]
        exact hAxisModel _ (hxN.trans hρ1)
      · have hrev : R.vector (j₀,false) = -R.vector (j₀,true) := by rw [hop,neg_neg]
        rw [hModel j₀ x hxE hxN,hrev,hTneg,hTv,Set.union_comm]
        exact hAxisModel _ (hxN.trans hρ1)
    have hCrossingSigns {S : Type} [TopologicalSpace S] [T2Space S]
        (c d : Curve S) (p : S) (hc : CrossesAt c d p)
        (E : OpenPartialHomeomorph S Plane) (hpE : p ∈ E.source) (hEp : E p = 0)
        (ρ : ℝ) (hρ : 0 < ρ) (a b : Plane)
        (haxis : ∀ x ∈ E.source, ‖E x‖ < ρ → (x ∈ c.image ↔ E x 1 = 0))
        (hmeet : ∀ x ∈ E.source, x ∈ c.image ∩ d.image → x = p)
        (hmodel : ∀ x ∈ E.source, ‖E x‖ < ρ → x ∈ d.image →
          E x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) : a 1 * b 1 < 0 := by
      by_contra hn
      have hprod : 0 ≤ a 1 * b 1 := le_of_not_gt hn
      have hchoice : ∃ σ : ℝ, σ ≠ 0 ∧ 0 ≤ σ*a 1 ∧ 0 ≤ σ*b 1 := by
        by_cases ha : 0 ≤ a 1
        · by_cases hb : 0 ≤ b 1
          · exact ⟨1,one_ne_zero,by simpa,by simpa⟩
          · have hblt : b 1 < 0 := lt_of_not_ge hb
            have hale : a 1 ≤ 0 := by nlinarith
            exact ⟨-1,neg_ne_zero.mpr one_ne_zero,by nlinarith,by nlinarith⟩
        · have halt : a 1 < 0 := lt_of_not_ge ha
          have hble : b 1 ≤ 0 := by nlinarith
          exact ⟨-1,neg_ne_zero.mpr one_ne_zero,by nlinarith,by nlinarith⟩
      obtain ⟨σ,hσ,ha,hb⟩ := hchoice
      apply crossing_cannot_stay_in_one_half c d p hc E hpE hEp ρ σ hρ haxis
      intro x hxE hxρ hxd hxp
      have hRayNN (v : Plane) (hv : 0 ≤ σ*v 1) (hx : E x ∈ segment ℝ (0 : Plane) v) :
          0 ≤ σ*E x 1 := by
        rw [segment_eq_image'] at hx
        obtain ⟨t,ht,he⟩ := hx
        have hh := congrArg (fun z : Plane => z 1) he
        change 0 + t*(v 1-0) = E x 1 at hh
        have hmul := mul_nonneg ht.1 hv
        calc
          0 ≤ t*(σ*v 1) := hmul
          _ = σ*E x 1 := by rw [← hh]; ring
      have hxNN : 0 ≤ σ*E x 1 := (hmodel x hxE hxρ hxd).elim (hRayNN a ha) (hRayNN b hb)
      apply lt_of_le_of_ne hxNN
      intro he
      have hx0 : E x 1 = 0 := (mul_eq_zero.mp he.symm).resolve_left hσ
      have hxc : x ∈ c.image := (haxis x hxE hxρ).mpr hx0
      exact hxp (hmeet x hxE ⟨hxc,hxd⟩)
    let JU := {i : I // u ∈ (r i).val.image}
    let eU := Fintype.equivFin JU
    let JZ := {i : I // z ∈ (r i).val.image}
    let eZ := Fintype.equivFin JZ
    let βU : Bool := decide (u = γ a)
    let βZ : Bool := decide (z = γ a)
    obtain ⟨TU,FU,ρU,hFUSource,hFU0,hρU,hρU1,hFUFormula,hTUVector,hFUCoreNorm,hFUAxis,hFUModel⟩ :=
      hStraightCore (fun j => (r (eU.symm j).val).val) u EcornerU huEcornerU hEcornerU0
        _ RU (eU ⟨v,huSelected⟩) hRUOpposite βU hRUCore
    obtain ⟨TZ,FZ,ρZ,hFZSource,hFZ0,hρZ,hρZ1,hFZFormula,hTZVector,hFZCoreNorm,hFZAxis,hFZModel⟩ :=
      hStraightCore (fun j => (r (eZ.symm j).val).val) z EcornerZ hzEcornerZ hEcornerZ0
        _ RZ (eZ ⟨v,hzSelected⟩) hRZOpposite βZ hRZCore
    have hUArmSigns (j : Fin (Fintype.card JU)) (hj : (eU.symm j).val ≠ v) :
        (TU (RU.vector (j,false))) 1 * (TU (RU.vector (j,true))) 1 < 0 := by
      apply hCrossingSigns (r v).val (r (eU.symm j).val).val u
        ((hr v (eU.symm j).val hj.symm).2 u ⟨huSelected,(eU.symm j).property⟩)
        FU (by rwa [hFUSource]) hFU0 ρU hρU _ _
      · simpa [eU] using hFUAxis
      · intro x hx hxd
        have hxU : x ∈ Ucorner := hEcornerUSub (hFUSource ▸ hx)
        exact Set.mem_singleton_iff.mp (hUContacts v (eU.symm j).val hj.symm ⟨hxU,hxd⟩)
      · intro x hx hxN hxd
        exact (hFUModel j x hx hxN).mp hxd
    have hZArmSigns (j : Fin (Fintype.card JZ)) (hj : (eZ.symm j).val ≠ v) :
        (TZ (RZ.vector (j,false))) 1 * (TZ (RZ.vector (j,true))) 1 < 0 := by
      apply hCrossingSigns (r v).val (r (eZ.symm j).val).val z
        ((hr v (eZ.symm j).val hj.symm).2 z ⟨hzSelected,(eZ.symm j).property⟩)
        FZ (by rwa [hFZSource]) hFZ0 ρZ hρZ _ _
      · simpa [eZ] using hFZAxis
      · intro x hx hxd
        have hxZ : x ∈ Zcorner := hEcornerZSub (hFZSource ▸ hx)
        exact Set.mem_singleton_iff.mp (hZContacts v (eZ.symm j).val hj.symm ⟨hxZ,hxd⟩)
      · intro x hx hxN hxd
        exact (hFZModel j x hx hxN).mp hxd
    have hOrientPair (a b : Plane) (h : a 1*b 1 < 0) :
        ∃ a' b' : Plane, 0 < a' 1 ∧ b' 1 < 0 ∧
          segment ℝ (0 : Plane) a' ∪ segment ℝ (0 : Plane) b' =
          segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b := by
      rcases mul_neg_iff.mp h with h | h
      · exact ⟨a,b,h.1,h.2,rfl⟩
      · exact ⟨b,a,h.2,h.1,Set.union_comm _ _⟩
    let KU := {j : Fin (Fintype.card JU) // (eU.symm j).val ≠ v}
    let KZ := {j : Fin (Fintype.card JZ) // (eZ.symm j).val ≠ v}
    have hUOriented : ∀ j : KU, ∃ a b : Plane, 0 < a 1 ∧ b 1 < 0 ∧
        segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b =
        segment ℝ (0 : Plane) (TU (RU.vector (j.val,false))) ∪
        segment ℝ (0 : Plane) (TU (RU.vector (j.val,true))) := by
      intro j
      exact hOrientPair _ _ (hUArmSigns j.val j.property)
    have hZOriented : ∀ j : KZ, ∃ a b : Plane, 0 < a 1 ∧ b 1 < 0 ∧
        segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b =
        segment ℝ (0 : Plane) (TZ (RZ.vector (j.val,false))) ∪
        segment ℝ (0 : Plane) (TZ (RZ.vector (j.val,true))) := by
      intro j
      exact hOrientPair _ _ (hZArmSigns j.val j.property)
    choose aU bU haU hbU hUnionU using hUOriented
    choose aZ bZ haZ hbZ hUnionZ using hZOriented
    have hFiniteConnector {J : Type} [Fintype J] (a b : J → Plane)
        (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
        (δ ξ H : ℝ) (hδ : 0 < δ) (hξ : ξ < 0) (hH : 0 < H) :
        ∃ h : ℝ, 0 < h ∧ h < H ∧
          let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h)
          IsArcBetween C (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
          Disjoint C {x | x 0 = 0} ∧
          (∀ j, Plane.mk (-δ) 0 ∉ segment ℝ (0 : Plane) (a j) ∪
            segment ℝ (0 : Plane) (b j)) ∧
          (∀ j, Plane.mk ξ h ∉ segment ℝ (0 : Plane) (a j) ∪
            segment ℝ (0 : Plane) (b j)) ∧
          (∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪
              segment ℝ (0 : Plane) (b j))).Finite ∧
            (C ∩ (segment ℝ (0 : Plane) (a j) ∪
              segment ℝ (0 : Plane) (b j))).ncard ≤ 1) := by
      classical
      have hbuild (δ ξ h : ℝ) (hδ : 0 < δ) (hξ : ξ < 0) (hh : 0 < h) :
        ∃ C : Set Plane,
            C = segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
            IsArcBetween C (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
            C ⊆ {x | x 0 < 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ h} ∧
            Disjoint C {x | x 0 = 0} ∧
            ∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪
              segment ℝ (0 : Plane) (b j))).Finite ∧
              (C ∩ (segment ℝ (0 : Plane) (a j) ∪
                segment ℝ (0 : Plane) (b j))).ncard ≤ 1 := by
        classical
        let p := Plane.mk (-δ) 0
        let q := Plane.mk ξ h
        let C := segment ℝ p q
        have hpq : p ≠ q := by
          intro he
          have hy := congrArg (fun x : Plane => x 1) he
          change (0 : ℝ) = h at hy
          linarith
        have hC (x : Plane) (hx : x ∈ C) : x 0 < 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ h := by
          obtain ⟨t,ht,rfl⟩ := (show x ∈ (fun t : ℝ => p + t • (q-p)) '' Icc 0 1 from
            (segment_eq_image' ℝ p q) ▸ hx)
          simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply]
          change -δ + t * (ξ - -δ) < 0 ∧
            0 ≤ 0 + t * (h-0) ∧ 0 + t * (h-0) ≤ h
          constructor
          · by_cases ht0 : t = 0
            · simp only [ht0,zero_mul,add_zero]
              linarith
            · have htx : t * ξ < 0 := mul_neg_of_pos_of_neg (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hξ
              have htd : 0 ≤ (1-t)*δ := mul_nonneg (sub_nonneg.mpr ht.2) hδ.le
              nlinarith
          · constructor <;> nlinarith [ht.1,ht.2]
        have hLine (x : Plane) (hx : x ∈ C) :
            h * x 0 - (ξ + δ) * x 1 = -δ * h := by
          obtain ⟨t,ht,rfl⟩ := (show x ∈ (fun t : ℝ => p + t • (q-p)) '' Icc 0 1 from
            (segment_eq_image' ℝ p q) ▸ hx)
          change h * (-δ + t * (ξ - -δ)) - (ξ + δ) * (0 + t * (h-0)) = -δ*h
          ring
        have hRadial (x v : Plane) (hx : x ∈ segment ℝ (0 : Plane) v) :
            ∃ t ∈ Icc (0 : ℝ) 1, x = t • v := by
          rw [segment_eq_image'] at hx
          obtain ⟨t,ht,he⟩ := hx
          exact ⟨t,ht,by simpa only [zero_add,sub_zero] using he.symm⟩
        have hLower (j : J) : Disjoint C (segment ℝ (0 : Plane) (b j)) := by
          apply Set.disjoint_left.mpr
          intro x hx hxB
          obtain ⟨t,ht,hxt⟩ := hRadial x (b j) hxB
          have hcy := (hC x hx).2.1
          have hxY : x 1 = t * b j 1 := by rw [hxt]; rfl
          have htzero : t = 0 := by nlinarith [hb j,ht.1]
          have hxzero : x = 0 := by rw [hxt,htzero,zero_smul]
          have hcx := (hC x hx).1
          rw [hxzero] at hcx
          change (0 : ℝ) < 0 at hcx
          exact (lt_irrefl 0) hcx
        have hSingle (j : J) : (C ∩ segment ℝ (0 : Plane) (a j)).Subsingleton := by
          intro x hx y hy
          obtain ⟨t,ht,hxt⟩ := hRadial x (a j) hx.2
          obtain ⟨s,hs,hys⟩ := hRadial y (a j) hy.2
          let L : ℝ := h * a j 0 - (ξ + δ) * a j 1
          have htX : t * L = -δ * h := by
            have hxX := hLine x hx.1
            rw [hxt] at hxX
            change h * (t * a j 0) - (ξ + δ) * (t * a j 1) = -δ*h at hxX
            dsimp [L]
            nlinarith [hxX]
          have hsX : s * L = -δ * h := by
            have hyX := hLine y hy.1
            rw [hys] at hyX
            change h * (s * a j 0) - (ξ + δ) * (s * a j 1) = -δ*h at hyX
            dsimp [L]
            nlinarith [hyX]
          have haX : L ≠ 0 := by
            intro hz
            rw [hz,mul_zero] at htX
            nlinarith
          have hts : t = s := mul_right_cancel₀ haX (htX.trans hsX.symm)
          rw [hxt,hys,hts]
        refine ⟨C,rfl,isArcBetween_segment hpq,?_,?_,?_⟩
        · intro x hx
          obtain ⟨hxX,hxY,hxh⟩ := hC x hx
          exact ⟨by linarith,hxY,hxh⟩
        · apply Set.disjoint_left.mpr
          intro x hx hxaxis
          have hxX := (hC x hx).1
          change x 0 = 0 at hxaxis
          linarith
        · intro j
          have heq : C ∩ (segment ℝ (0 : Plane) (a j) ∪
              segment ℝ (0 : Plane) (b j)) = C ∩ segment ℝ (0 : Plane) (a j) := by
            rw [Set.inter_union_distrib_left,Set.disjoint_iff_inter_eq_empty.mp (hLower j),Set.union_empty]
          rw [heq]
          exact ⟨(hSingle j).finite,(Set.ncard_le_one (hSingle j).finite).mpr (hSingle j)⟩
    
      obtain ⟨CH,hCH,hArcH,hRectH,hAxisH,hCountsH⟩ := hbuild (-ξ) ξ H (by linarith) hξ hH
      let T : Set Plane := ⋃ j, CH ∩ (segment ℝ (0 : Plane) (a j) ∪
        segment ℝ (0 : Plane) (b j))
      have hT : T.Finite := Set.finite_iUnion (fun j => (hCountsH j).1)
      have hBad : ((fun x : Plane => x 1) '' T).Finite := hT.image _
      obtain ⟨h,hh,havoid⟩ := (Set.Ioo_infinite hH).exists_notMem_finite hBad
      have hEndCH : Plane.mk ξ h ∈ CH := by
        rw [hCH,segment_eq_image']
        refine ⟨h/H,⟨(div_pos hh.1 hH).le,(div_le_one hH).mpr hh.2.le⟩,?_⟩
        ext i
        fin_cases i
        · simp [Plane.mk]
        · simp [Plane.mk]
          field_simp
      have hEnd (j : J) : Plane.mk ξ h ∉ segment ℝ (0 : Plane) (a j) ∪
          segment ℝ (0 : Plane) (b j) := by
        intro hx
        apply havoid
        exact ⟨Plane.mk ξ h,Set.mem_iUnion.mpr ⟨j,⟨hEndCH,hx⟩⟩,rfl⟩
      have hStart (j : J) : Plane.mk (-δ) 0 ∉ segment ℝ (0 : Plane) (a j) ∪
          segment ℝ (0 : Plane) (b j) := by
        intro hx
        have hRad (v : Plane) (hv : v 1 ≠ 0)
            (hx : Plane.mk (-δ) 0 ∈ segment ℝ (0 : Plane) v) : False := by
          rw [segment_eq_image'] at hx
          obtain ⟨t,ht,he⟩ := hx
          have he' : t • v = Plane.mk (-δ) 0 := by
            simpa only [zero_add,sub_zero] using he
          have hy := congrArg (fun z : Plane => z 1) he'
          change t * v 1 = 0 at hy
          have ht0 : t = 0 := (mul_eq_zero.mp hy).resolve_right hv
          rw [ht0,zero_smul] at he'
          have hx0 := congrArg (fun z : Plane => z 0) he'
          change 0 = -δ at hx0
          linarith
        exact hx.elim (hRad (a j) (ne_of_gt (ha j))) (hRad (b j) (ne_of_lt (hb j)))
      obtain ⟨C,hC,hArc,hRect,hAxis,hCounts⟩ := hbuild δ ξ h hδ hξ hh.1
      refine ⟨h,hh.1,hh.2,?_⟩
      dsimp only
      rw [← hC]
      exact ⟨hArc,hAxis,hStart,hEnd,hCounts⟩
    have hSmallConnector {J : Type} [Fintype J] (a b : J → Plane)
        (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
        (η : ℝ) (hη : 0 < η) (k : J) :
        ∃ δ h : ℝ, 0 < δ ∧ 0 < h ∧
          let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h)
          C ⊆ Metric.ball (0 : Plane) η ∧
          Disjoint C (segment ℝ (0 : Plane) (a k) ∪ segment ℝ (0 : Plane) (b k)) ∧
          IsArcBetween C (Plane.mk (-δ) 0) (Plane.mk (-δ) h) ∧
          (∀ j, Plane.mk (-δ) h ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ∧
          (∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).Finite ∧
            (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).ncard ≤ 1) := by
      classical
      have hConnector (a b : J → Plane)
          (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
          (δ ξ H : ℝ) (hδ : 0 < δ) (hξ : ξ < 0) (hH : 0 < H) :
          ∃ h : ℝ, 0 < h ∧ h < H ∧
            let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h)
            IsArcBetween C (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
            Disjoint C {x | x 0 = 0} ∧
            (∀ j, Plane.mk (-δ) 0 ∉ segment ℝ (0 : Plane) (a j) ∪
              segment ℝ (0 : Plane) (b j)) ∧
            (∀ j, Plane.mk ξ h ∉ segment ℝ (0 : Plane) (a j) ∪
              segment ℝ (0 : Plane) (b j)) ∧
            (∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪
                segment ℝ (0 : Plane) (b j))).Finite ∧
              (C ∩ (segment ℝ (0 : Plane) (a j) ∪
                segment ℝ (0 : Plane) (b j))).ncard ≤ 1) := by
        classical
        have hbuild (δ ξ h : ℝ) (hδ : 0 < δ) (hξ : ξ < 0) (hh : 0 < h) :
          ∃ C : Set Plane,
              C = segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
              IsArcBetween C (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
              C ⊆ {x | x 0 < 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ h} ∧
              Disjoint C {x | x 0 = 0} ∧
              ∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪
                segment ℝ (0 : Plane) (b j))).Finite ∧
                (C ∩ (segment ℝ (0 : Plane) (a j) ∪
                  segment ℝ (0 : Plane) (b j))).ncard ≤ 1 := by
          classical
          let p := Plane.mk (-δ) 0
          let q := Plane.mk ξ h
          let C := segment ℝ p q
          have hpq : p ≠ q := by
            intro he
            have hy := congrArg (fun x : Plane => x 1) he
            change (0 : ℝ) = h at hy
            linarith
          have hC (x : Plane) (hx : x ∈ C) : x 0 < 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ h := by
            obtain ⟨t,ht,rfl⟩ := (show x ∈ (fun t : ℝ => p + t • (q-p)) '' Icc 0 1 from
              (segment_eq_image' ℝ p q) ▸ hx)
            simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply]
            change -δ + t * (ξ - -δ) < 0 ∧
              0 ≤ 0 + t * (h-0) ∧ 0 + t * (h-0) ≤ h
            constructor
            · by_cases ht0 : t = 0
              · simp only [ht0,zero_mul,add_zero]
                linarith
              · have htx : t * ξ < 0 := mul_neg_of_pos_of_neg (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hξ
                have htd : 0 ≤ (1-t)*δ := mul_nonneg (sub_nonneg.mpr ht.2) hδ.le
                nlinarith
            · constructor <;> nlinarith [ht.1,ht.2]
          have hLine (x : Plane) (hx : x ∈ C) :
              h * x 0 - (ξ + δ) * x 1 = -δ * h := by
            obtain ⟨t,ht,rfl⟩ := (show x ∈ (fun t : ℝ => p + t • (q-p)) '' Icc 0 1 from
              (segment_eq_image' ℝ p q) ▸ hx)
            change h * (-δ + t * (ξ - -δ)) - (ξ + δ) * (0 + t * (h-0)) = -δ*h
            ring
          have hRadial (x v : Plane) (hx : x ∈ segment ℝ (0 : Plane) v) :
              ∃ t ∈ Icc (0 : ℝ) 1, x = t • v := by
            rw [segment_eq_image'] at hx
            obtain ⟨t,ht,he⟩ := hx
            exact ⟨t,ht,by simpa only [zero_add,sub_zero] using he.symm⟩
          have hLower (j : J) : Disjoint C (segment ℝ (0 : Plane) (b j)) := by
            apply Set.disjoint_left.mpr
            intro x hx hxB
            obtain ⟨t,ht,hxt⟩ := hRadial x (b j) hxB
            have hcy := (hC x hx).2.1
            have hxY : x 1 = t * b j 1 := by rw [hxt]; rfl
            have htzero : t = 0 := by nlinarith [hb j,ht.1]
            have hxzero : x = 0 := by rw [hxt,htzero,zero_smul]
            have hcx := (hC x hx).1
            rw [hxzero] at hcx
            change (0 : ℝ) < 0 at hcx
            exact (lt_irrefl 0) hcx
          have hSingle (j : J) : (C ∩ segment ℝ (0 : Plane) (a j)).Subsingleton := by
            intro x hx y hy
            obtain ⟨t,ht,hxt⟩ := hRadial x (a j) hx.2
            obtain ⟨s,hs,hys⟩ := hRadial y (a j) hy.2
            let L : ℝ := h * a j 0 - (ξ + δ) * a j 1
            have htX : t * L = -δ * h := by
              have hxX := hLine x hx.1
              rw [hxt] at hxX
              change h * (t * a j 0) - (ξ + δ) * (t * a j 1) = -δ*h at hxX
              dsimp [L]
              nlinarith [hxX]
            have hsX : s * L = -δ * h := by
              have hyX := hLine y hy.1
              rw [hys] at hyX
              change h * (s * a j 0) - (ξ + δ) * (s * a j 1) = -δ*h at hyX
              dsimp [L]
              nlinarith [hyX]
            have haX : L ≠ 0 := by
              intro hz
              rw [hz,mul_zero] at htX
              nlinarith
            have hts : t = s := mul_right_cancel₀ haX (htX.trans hsX.symm)
            rw [hxt,hys,hts]
          refine ⟨C,rfl,isArcBetween_segment hpq,?_,?_,?_⟩
          · intro x hx
            obtain ⟨hxX,hxY,hxh⟩ := hC x hx
            exact ⟨by linarith,hxY,hxh⟩
          · apply Set.disjoint_left.mpr
            intro x hx hxaxis
            have hxX := (hC x hx).1
            change x 0 = 0 at hxaxis
            linarith
          · intro j
            have heq : C ∩ (segment ℝ (0 : Plane) (a j) ∪
                segment ℝ (0 : Plane) (b j)) = C ∩ segment ℝ (0 : Plane) (a j) := by
              rw [Set.inter_union_distrib_left,Set.disjoint_iff_inter_eq_empty.mp (hLower j),Set.union_empty]
            rw [heq]
            exact ⟨(hSingle j).finite,(Set.ncard_le_one (hSingle j).finite).mpr (hSingle j)⟩
      
        obtain ⟨CH,hCH,hArcH,hRectH,hAxisH,hCountsH⟩ := hbuild (-ξ) ξ H (by linarith) hξ hH
        let T : Set Plane := ⋃ j, CH ∩ (segment ℝ (0 : Plane) (a j) ∪
          segment ℝ (0 : Plane) (b j))
        have hT : T.Finite := Set.finite_iUnion (fun j => (hCountsH j).1)
        have hBad : ((fun x : Plane => x 1) '' T).Finite := hT.image _
        obtain ⟨h,hh,havoid⟩ := (Set.Ioo_infinite hH).exists_notMem_finite hBad
        have hEndCH : Plane.mk ξ h ∈ CH := by
          rw [hCH,segment_eq_image']
          refine ⟨h/H,⟨(div_pos hh.1 hH).le,(div_le_one hH).mpr hh.2.le⟩,?_⟩
          ext i
          fin_cases i
          · simp [Plane.mk]
          · simp [Plane.mk]
            field_simp
        have hEnd (j : J) : Plane.mk ξ h ∉ segment ℝ (0 : Plane) (a j) ∪
            segment ℝ (0 : Plane) (b j) := by
          intro hx
          apply havoid
          exact ⟨Plane.mk ξ h,Set.mem_iUnion.mpr ⟨j,⟨hEndCH,hx⟩⟩,rfl⟩
        have hStart (j : J) : Plane.mk (-δ) 0 ∉ segment ℝ (0 : Plane) (a j) ∪
            segment ℝ (0 : Plane) (b j) := by
          intro hx
          have hRad (v : Plane) (hv : v 1 ≠ 0)
              (hx : Plane.mk (-δ) 0 ∈ segment ℝ (0 : Plane) v) : False := by
            rw [segment_eq_image'] at hx
            obtain ⟨t,ht,he⟩ := hx
            have he' : t • v = Plane.mk (-δ) 0 := by
              simpa only [zero_add,sub_zero] using he
            have hy := congrArg (fun z : Plane => z 1) he'
            change t * v 1 = 0 at hy
            have ht0 : t = 0 := (mul_eq_zero.mp hy).resolve_right hv
            rw [ht0,zero_smul] at he'
            have hx0 := congrArg (fun z : Plane => z 0) he'
            change 0 = -δ at hx0
            linarith
          exact hx.elim (hRad (a j) (ne_of_gt (ha j))) (hRad (b j) (ne_of_lt (hb j)))
        obtain ⟨C,hC,hArc,hRect,hAxis,hCounts⟩ := hbuild δ ξ h hδ hξ hh.1
        refine ⟨h,hh.1,hh.2,?_⟩
        dsimp only
        rw [← hC]
        exact ⟨hArc,hAxis,hStart,hEnd,hCounts⟩
      have hUpperAvoid (a : Plane) (δ ξ h : ℝ) (hδ : 0 < δ)
          (ha : 0 < a 1) (hq : ξ * a 1 - h * a 0 < 0) :
          Disjoint (segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h))
            (segment ℝ (0 : Plane) a) := by
        apply Set.disjoint_left.mpr
        intro x hx hxa
        obtain ⟨t,ht,rfl⟩ := (show x ∈ (fun t : ℝ =>
            Plane.mk (-δ) 0 + t • (Plane.mk ξ h - Plane.mk (-δ) 0)) '' Icc 0 1 from
          (segment_eq_image' ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h)) ▸ hx)
        obtain ⟨s,hs,he⟩ := (show
          Plane.mk (-δ) 0 + t • (Plane.mk ξ h - Plane.mk (-δ) 0) ∈
            (fun s : ℝ => (0 : Plane) + s • (a-0)) '' Icc 0 1 from
          (segment_eq_image' ℝ (0 : Plane) a) ▸ hxa)
        have hx0 := congrArg (fun x : Plane => x 0) he
        have hx1 := congrArg (fun x : Plane => x 1) he
        change 0 + s * (a 0-0) = -δ + t * (ξ - -δ) at hx0
        simp only [sub_zero,zero_add,sub_neg_eq_add] at hx0
        change 0 + s * (a 1-0) = 0 + t * (h-0) at hx1
        simp only [sub_zero,zero_add] at hx1
        have hp : -δ * a 1 < 0 := mul_neg_of_neg_of_pos (by linarith) ha
        have hz : (-δ + t*(ξ+δ))*a 1 - (t*h)*a 0 = 0 := by
          rw [← hx0,← hx1]
          ring
        by_cases ht0 : t = 0
        · subst t
          simp only [zero_mul,add_zero,sub_zero] at hz
          linarith
        · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
          have hn1 := mul_neg_of_pos_of_neg htpos hq
          have hn2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) hp.le
          nlinarith
      have hBase : Continuous (fun t : ℝ => Plane.mk (-t) 0) := by fun_prop
      have hOpen : IsOpen ((fun t : ℝ => Plane.mk (-t) 0) ⁻¹' Metric.ball (0 : Plane) η) := Metric.isOpen_ball.preimage hBase
      have hZero : (0 : ℝ) ∈ (fun t : ℝ => Plane.mk (-t) 0) ⁻¹' Metric.ball (0 : Plane) η := by
        have hm : Plane.mk (-(0 : ℝ)) 0 = (0 : Plane) := by
          ext i
          fin_cases i <;> simp [Plane.mk]
        change Plane.mk (-(0 : ℝ)) 0 ∈ Metric.ball (0 : Plane) η
        rw [hm]
        simpa using hη
      obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hOpen 0 hZero
      let δ := r / 2
      have hδ : 0 < δ := half_pos hr
      have hP : Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η := hBall (by
        rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ]
        dsimp [δ]; linarith)
      have hVert : Continuous (fun t : ℝ => Plane.mk (-δ) t) := by fun_prop
      obtain ⟨s,hs,hEndBall⟩ := Metric.isOpen_iff.mp (show IsOpen ((fun t : ℝ => Plane.mk (-δ) t) ⁻¹' Metric.ball (0 : Plane) η) from Metric.isOpen_ball.preimage hVert) 0 hP
      let H := min (s/2) (δ*(a k) 1/(2*(|(a k) 0|+1)))
      have hden : 0 < 2*(|(a k) 0|+1) := by positivity
      have hH : 0 < H := lt_min (half_pos hs) (div_pos (mul_pos hδ (ha k)) hden)
      obtain ⟨h,hh,hhH,hArc,hAxis,hStart,hEnd,hCounts⟩ :=
        hConnector a b ha hb δ (-δ) H hδ (neg_neg_of_pos hδ) hH
      have hhS : h < s/2 := hhH.trans_le (min_le_left _ _)
      have hbound : h*(2*(|(a k) 0|+1)) < δ*(a k) 1 :=
        (lt_div_iff₀ hden).mp (hhH.trans_le (min_le_right _ _))
      have hdet : (-δ)*(a k) 1-h*(a k) 0 < 0 := by
        have habs := neg_abs_le ((a k) 0)
        nlinarith [mul_nonneg hh.le (sub_nonneg.mpr habs)]
      have hQ : Plane.mk (-δ) h ∈ Metric.ball (0 : Plane) η := hEndBall (by
        rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hh]
        linarith)
      have hLowerAvoid : Disjoint (segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h))
          (segment ℝ (0 : Plane) (b k)) := by
        apply Set.disjoint_left.mpr
        intro x hx hxB
        rw [segment_eq_image'] at hx hxB
        obtain ⟨t,ht,he⟩ := hx
        obtain ⟨q,hq,hqe⟩ := hxB
        have hx0 := congrArg (fun z : Plane => z 0) he
        have hx1 := congrArg (fun z : Plane => z 1) he
        have hy0 := congrArg (fun z : Plane => z 0) hqe
        have hy1 := congrArg (fun z : Plane => z 1) hqe
        change -δ+t*(-δ-(-δ)) = x 0 at hx0
        change 0+t*(h-0) = x 1 at hx1
        change 0+q*((b k) 0-0) = x 0 at hy0
        change 0+q*((b k) 1-0) = x 1 at hy1
        have hq0 : q = 0 := by nlinarith [hb k,hq.1,mul_nonneg ht.1 hh.le]
        rw [hq0] at hy0
        nlinarith
      have hAvoid := Set.disjoint_union_right.mpr ⟨hUpperAvoid (a k) δ (-δ) h hδ (ha k) hdet,hLowerAvoid⟩
      exact ⟨δ,h,hδ,hh,(convex_ball (0 : Plane) η).segment_subset hP hQ,hAvoid,hArc,hEnd,hCounts⟩
    have h0TargetU : (0 : Plane) ∈ FU.target := by
      rw [← hFU0]
      exact FU.map_source (by rwa [hFUSource])
    have h0TargetZ : (0 : Plane) ∈ FZ.target := by
      rw [← hFZ0]
      exact FZ.map_source (by rwa [hFZSource])
    have hShortTailClearance {J : Type} [Fintype J] (γ : J → Interval → Plane) (V : Set Plane)
        (R : RadializedStar γ 0 V) (j : J)
        (hγ : Topology.IsClosedEmbedding (γ j)) (hγ0 : γ j zeroI = 0)
        (T : Plane ≃L[ℝ] Plane) (τ : ℝ) (hτ : 0 < τ)
        (O : Set Plane) (hO : IsOpen O) (h0 : (0 : Plane) ∈ O) :
        ∃ η : ℝ, 0 < η ∧ Metric.ball (0 : Plane) η ⊆ O ∧
          Disjoint (Metric.ball (0 : Plane) η)
            ((fun t => T (R.H (γ j t))) '' {t : Interval | τ ≤ t.val}) := by
      let K := (fun t => T (R.H (γ j t))) '' {t : Interval | τ ≤ t.val}
      have hK : IsCompact K :=
        (isClosed_le continuous_const continuous_subtype_val).isCompact.image
          (T.continuous.comp (R.H.continuous.comp hγ.continuous))
      have hNot : (0 : Plane) ∉ K := by
        rintro ⟨t,ht,he⟩
        have h1 : R.H (γ j t) = 0 := by
          have hh := congrArg T.symm he
          simpa using hh
        have h2 : γ j t = 0 := R.H.injective (h1.trans R.fixes_center.symm)
        have hh : γ j t = γ j zeroI := h2.trans hγ0.symm
        have ht0 := hγ.injective hh
        have hv := congrArg Subtype.val ht0
        change t.val = 0 at hv
        change τ ≤ t.val at ht
        linarith
      obtain ⟨η,hη,hBall⟩ := Metric.isOpen_iff.mp (hO.inter hK.isClosed.isOpen_compl) 0 ⟨h0,hNot⟩
      refine ⟨η,hη,(fun x hx => (hBall hx).1),?_⟩
      exact Set.disjoint_left.mpr (fun x hx hk => (hBall hx).2 hk)
    let gap := 2*Real.pi-(zangle-a)
    have hGap : 0 < gap := by dsimp [gap]; linarith [hlenangle]
    let τU := min (gap/(2*εU)) 1 / 2
    let τZ := min (gap/(2*εZ)) 1 / 2
    have hτU : 0 < τU := half_pos (lt_min (div_pos hGap (by positivity)) zero_lt_one)
    have hτZ : 0 < τZ := half_pos (lt_min (div_pos hGap (by positivity)) zero_lt_one)
    have hετU : εU*τU < gap := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2*εU)).mp (min_le_left (gap/(2*εU)) 1)
      dsimp [τU]
      nlinarith
    have hετZ : εZ*τZ < gap := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2*εZ)).mp (min_le_left (gap/(2*εZ)) 1)
      dsimp [τZ]
      nlinarith
    obtain ⟨ηU,hηU,hBallU,hSelectedTailU⟩ := hShortTailClearance _ _ RU
      (eU ⟨v,huSelected⟩,!βU) (hArmsUClosed _) (hArmsUZero _) TU τU hτU
      (FU.target ∩ Metric.ball (0 : Plane) ρU) (FU.open_target.inter Metric.isOpen_ball)
      ⟨h0TargetU,by simpa using hρU⟩
    obtain ⟨ηZ,hηZ,hBallZ,hSelectedTailZ⟩ := hShortTailClearance _ _ RZ
      (eZ ⟨v,hzSelected⟩,!βZ) (hArmsZClosed _) (hArmsZZero _) TZ τZ hτZ
      (FZ.target ∩ Metric.ball (0 : Plane) ρZ) (FZ.open_target.inter Metric.isOpen_ball)
      ⟨h0TargetZ,by simpa using hρZ⟩
    have huOpposite : u ∈ (r w).val.image := hgcurve ⟨0,hg0⟩
    have hzOpposite : z ∈ (r w).val.image := hgcurve ⟨1,hg1⟩
    let kwU : KU := ⟨eU ⟨w,huOpposite⟩,by simpa using hvw.symm⟩
    let kwZ : KZ := ⟨eZ ⟨w,hzOpposite⟩,by simpa using hvw.symm⟩
    obtain ⟨δU,heightU,hδU,hHeightU,hConnectorBallU,hConnectorAvoidWU,hConnectorArcU,hConnectorEndpointU,hConnectorCountsU⟩ :=
      hSmallConnector aU bU haU hbU ηU hηU kwU
    obtain ⟨δZ,heightZ,hδZ,hHeightZ,hConnectorBallZ,hConnectorAvoidWZ,hConnectorArcZ,hConnectorEndpointZ,hConnectorCountsZ⟩ :=
      hSmallConnector aZ bZ haZ hbZ ηZ hηZ kwZ
    let connectorU := segment ℝ (Plane.mk (-δU) 0) (Plane.mk (-δU) heightU)
    let connectorZ := segment ℝ (Plane.mk (-δZ) 0) (Plane.mk (-δZ) heightZ)
    have hConnectorCoreU : connectorU ⊆ FU.target ∩ Metric.ball (0 : Plane) ρU :=
      hConnectorBallU.trans hBallU
    have hConnectorCoreZ : connectorZ ⊆ FZ.target ∩ Metric.ball (0 : Plane) ρZ :=
      hConnectorBallZ.trans hBallZ
    have hTransportCounts {J : Type} [Fintype J]
        (F : OpenPartialHomeomorph S Plane) (ρ : ℝ) (C : Set Plane)
        (hc : C ⊆ F.target ∩ Metric.ball (0 : Plane) ρ)
        (c : J → Curve S) (a b : J → Plane)
        (hmodel : ∀ j x, x ∈ F.source → ‖F x‖ < ρ →
          (x ∈ (c j).image ↔ F x ∈ segment ℝ (0 : Plane) (a j) ∪
            segment ℝ (0 : Plane) (b j)))
        (hcounts : ∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪
          segment ℝ (0 : Plane) (b j))).Finite ∧
          (C ∩ (segment ℝ (0 : Plane) (a j) ∪
          segment ℝ (0 : Plane) (b j))).ncard ≤ 1) :
        ∀ j, ((F.symm '' C) ∩ (c j).image).Finite ∧
          ((F.symm '' C) ∩ (c j).image).ncard ≤ 1 := by
      intro j
      have hset : (F.symm '' C) ∩ (c j).image = F.symm ''
          (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))) := by
        ext x
        constructor
        · rintro ⟨⟨y,hy,rfl⟩,hx⟩
          have hys := F.map_target (hc hy).1
          have hyn : ‖F (F.symm y)‖ < ρ := by
            rw [F.right_inv (hc hy).1]
            simpa using (hc hy).2
          refine ⟨y,⟨hy,?_⟩,rfl⟩
          have hm := (hmodel j (F.symm y) hys hyn).mp hx
          rwa [F.right_inv (hc hy).1] at hm
        · rintro ⟨y,⟨hy,hm⟩,rfl⟩
          refine ⟨⟨y,hy,rfl⟩,?_⟩
          have hys := F.map_target (hc hy).1
          have hyn : ‖F (F.symm y)‖ < ρ := by
            rw [F.right_inv (hc hy).1]
            simpa using (hc hy).2
          apply (hmodel j (F.symm y) hys hyn).mpr
          rwa [F.right_inv (hc hy).1]
      rw [hset]
      exact ⟨(hcounts j).1.image F.symm,(Set.ncard_image_le (hcounts j).1).trans (hcounts j).2⟩
    have hSurfaceConnectorCountsU : ∀ j : KU,
        ((FU.symm '' connectorU) ∩ (r (eU.symm j.val).val).val.image).Finite ∧
        ((FU.symm '' connectorU) ∩ (r (eU.symm j.val).val).val.image).ncard ≤ 1 := by
      apply hTransportCounts FU ρU connectorU hConnectorCoreU
        (fun j : KU => (r (eU.symm j.val).val).val) aU bU
      · intro j x hx hxN
        rw [hUnionU j]
        exact hFUModel j.val x hx hxN
      · exact hConnectorCountsU
    have hSurfaceConnectorCountsZ : ∀ j : KZ,
        ((FZ.symm '' connectorZ) ∩ (r (eZ.symm j.val).val).val.image).Finite ∧
        ((FZ.symm '' connectorZ) ∩ (r (eZ.symm j.val).val).val.image).ncard ≤ 1 := by
      apply hTransportCounts FZ ρZ connectorZ hConnectorCoreZ
        (fun j : KZ => (r (eZ.symm j.val).val).val) aZ bZ
      · intro j x hx hxN
        rw [hUnionZ j]
        exact hFZModel j.val x hx hxN
      · exact hConnectorCountsZ
    let surfaceConnectorU := FU.symm '' connectorU
    let surfaceConnectorZ := FZ.symm '' connectorZ
    have hSurfaceConnectorUSub : surfaceConnectorU ⊆ Ucorner := by
      rintro x ⟨y,hy,rfl⟩
      exact hEcornerUSub (hFUSource ▸ FU.map_target (hConnectorCoreU hy).1)
    have hSurfaceConnectorZSub : surfaceConnectorZ ⊆ Zcorner := by
      rintro x ⟨y,hy,rfl⟩
      exact hEcornerZSub (hFZSource ▸ FZ.map_target (hConnectorCoreZ hy).1)
    have hSurfaceConnectorsDisjoint : Disjoint surfaceConnectorU surfaceConnectorZ :=
      hCornersDisjoint.mono hSurfaceConnectorUSub hSurfaceConnectorZSub
    have hWholeFamilyConnectorU (i : I) (hi : i ≠ v) :
        (surfaceConnectorU ∩ (r i).val.image).Finite ∧
        (surfaceConnectorU ∩ (r i).val.image).ncard ≤ 1 := by
      by_cases hp : u ∈ (r i).val.image
      · let j : KU := ⟨eU ⟨i,hp⟩,by simpa using hi⟩
        simpa [j,surfaceConnectorU] using hSurfaceConnectorCountsU j
      · have hd := (hUNonincident i hp).mono_left hSurfaceConnectorUSub
        rw [Set.disjoint_iff_inter_eq_empty.mp hd]
        exact ⟨Set.finite_empty,by simp⟩
    have hWholeFamilyConnectorZ (i : I) (hi : i ≠ v) :
        (surfaceConnectorZ ∩ (r i).val.image).Finite ∧
        (surfaceConnectorZ ∩ (r i).val.image).ncard ≤ 1 := by
      by_cases hp : z ∈ (r i).val.image
      · let j : KZ := ⟨eZ ⟨i,hp⟩,by simpa using hi⟩
        simpa [j,surfaceConnectorZ] using hSurfaceConnectorCountsZ j
      · have hd := (hZNonincident i hp).mono_left hSurfaceConnectorZSub
        rw [Set.disjoint_iff_inter_eq_empty.mp hd]
        exact ⟨Set.finite_empty,by simp⟩
    have hSurfaceConnectorAvoidWU : Disjoint surfaceConnectorU (r w).val.image := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y,hy,rfl⟩ hxw
      have hys := FU.map_target (hConnectorCoreU hy).1
      have hyn : ‖FU (FU.symm y)‖ < ρU := by
        rw [FU.right_inv (hConnectorCoreU hy).1]
        simpa using (hConnectorCoreU hy).2
      have hxw' : FU.symm y ∈ (r (eU.symm kwU.val).val).val.image := by
        simpa [kwU] using hxw
      have hm := (hFUModel kwU.val (FU.symm y) hys hyn).mp hxw'
      rw [FU.right_inv (hConnectorCoreU hy).1] at hm
      have hd := hConnectorAvoidWU
      rw [hUnionU kwU] at hd
      exact Set.disjoint_left.mp hd hy hm
    have hSurfaceConnectorAvoidWZ : Disjoint surfaceConnectorZ (r w).val.image := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y,hy,rfl⟩ hxw
      have hys := FZ.map_target (hConnectorCoreZ hy).1
      have hyn : ‖FZ (FZ.symm y)‖ < ρZ := by
        rw [FZ.right_inv (hConnectorCoreZ hy).1]
        simpa using (hConnectorCoreZ hy).2
      have hxw' : FZ.symm y ∈ (r (eZ.symm kwZ.val).val).val.image := by
        simpa [kwZ] using hxw
      have hm := (hFZModel kwZ.val (FZ.symm y) hys hyn).mp hxw'
      rw [FZ.right_inv (hConnectorCoreZ hy).1] at hm
      have hd := hConnectorAvoidWZ
      rw [hUnionZ kwZ] at hd
      exact Set.disjoint_left.mp hd hy hm
    have hChartConnectorArc
        (F : OpenPartialHomeomorph S Plane) (δ h : ℝ) (hh : 0 < h)
        (hTarget : segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h) ⊆ F.target) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          Set.range f = F.symm '' segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h) ∧
          f 0 = F.symm (Plane.mk (-δ) 0) ∧ f 1 = F.symm (Plane.mk (-δ) h) := by
      let γ : Interval → Plane := fun t => Plane.mk (-δ) (h*t.val)
      have hγ : Continuous γ := by fun_prop
      have hγSeg (t : Interval) : γ t ∈ segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h) := by
        rw [segment_eq_image']
        refine ⟨t.val,t.property,?_⟩
        ext i
        fin_cases i <;> simp [γ,Plane.mk,mul_comm]
      let f : C(Interval,S) := ⟨fun t => F.symm (γ t),
        F.symm.continuousOn.comp_continuous hγ (fun t => hTarget (hγSeg t))⟩
      have hinj : Function.Injective f := by
        intro t s he
        have hg : γ t = γ s := F.symm.injOn (hTarget (hγSeg t)) (hTarget (hγSeg s)) he
        have hv := congrArg (fun z : Plane => z 1) hg
        change h*t.val = h*s.val at hv
        exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hh) hv)
      refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_⟩
      · ext x
        constructor
        · rintro ⟨t,rfl⟩
          exact ⟨γ t,hγSeg t,rfl⟩
        · rintro ⟨y,hy,rfl⟩
          rw [segment_eq_image'] at hy
          obtain ⟨t,ht,he⟩ := hy
          refine ⟨⟨t,ht⟩,?_⟩
          apply congrArg F.symm
          change Plane.mk (-δ) (h*t) = y
          rw [← he]
          ext i
          fin_cases i <;> simp [Plane.mk,mul_comm]
      · change F.symm (γ 0) = F.symm (Plane.mk (-δ) 0)
        apply congrArg F.symm
        ext i
        fin_cases i <;> simp [γ,Plane.mk]
      · change F.symm (γ 1) = F.symm (Plane.mk (-δ) h)
        apply congrArg F.symm
        ext i
        fin_cases i <;> simp [γ,Plane.mk]
    obtain ⟨cornerArcU,hCornerArcU,hCornerRangeU,hCornerStartU,hCornerEndU⟩ :=
      hChartConnectorArc FU δU heightU hHeightU (fun x hx => (hConnectorCoreU hx).1)
    obtain ⟨cornerArcZ,hCornerArcZ,hCornerRangeZ,hCornerStartZ,hCornerEndZ⟩ :=
      hChartConnectorArc FZ δZ heightZ hHeightZ (fun x hx => (hConnectorCoreZ hx).1)
    have hCornerArcWholeCountsU (i : I) (hi : i ≠ v) :
        (Set.range cornerArcU ∩ (r i).val.image).Finite ∧
        (Set.range cornerArcU ∩ (r i).val.image).ncard ≤ 1 := by
      rw [hCornerRangeU]
      exact hWholeFamilyConnectorU i hi
    have hCornerArcWholeCountsZ (i : I) (hi : i ≠ v) :
        (Set.range cornerArcZ ∩ (r i).val.image).Finite ∧
        (Set.range cornerArcZ ∩ (r i).val.image).ncard ≤ 1 := by
      rw [hCornerRangeZ]
      exact hWholeFamilyConnectorZ i hi
    have hCornerArcOppositeAvoidU : Disjoint (Set.range cornerArcU) (r w).val.image := by
      rw [hCornerRangeU]
      exact hSurfaceConnectorAvoidWU
    have hCornerArcOppositeAvoidZ : Disjoint (Set.range cornerArcZ) (r w).val.image := by
      rw [hCornerRangeZ]
      exact hSurfaceConnectorAvoidWZ
    have hNegativeAxisActualArm {J : Type} [Fintype J]
        (c : Curve S) (p : S) (q : Circle) (hq : c.map q = p) (ε : ℝ)
        (E F : OpenPartialHomeomorph S Plane) (hFSource : F.source = E.source)
        (hFp : F p = 0) (γ : (J × Bool) → Interval → Plane) (V : Set Plane)
        (R : RadializedStar γ 0 V) (j : J) (β : Bool)
        (hγ : ∀ sign t, γ (j,sign) t = E (c.map (q * Circle.exp (if sign then ε*t.val else -(ε*t.val)))))
        (hsource : ∀ (sign : Bool) (t : Interval), c.map (q * Circle.exp (if sign then ε*t.val else -(ε*t.val))) ∈ E.source)
        (T : Plane ≃L[ℝ] Plane) (hFormula : ∀ x, F x = T (R.H (E x)))
        (hTv : T (R.vector (j,β)) = Plane.mk 1 0)
        (hop : R.vector (j,true) = -R.vector (j,false))
        (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hTarget : Plane.mk (-δ) 0 ∈ F.target) :
        ∃ t : Interval, 0 < t.val ∧ t.val ≤ (R.cut (j,!β)).val ∧
          F.symm (Plane.mk (-δ) 0) = c.map (q * Circle.exp (if !β then ε*t.val else -(ε*t.val))) := by
      have hOther : R.vector (j,!β) = -R.vector (j,β) := by
        cases β
        · exact hop
        · simp only [Bool.not_true]
          rw [hop,neg_neg]
      have hTδ : T (δ • R.vector (j,!β)) = Plane.mk (-δ) 0 := by
        rw [hOther,map_smul,map_neg,hTv]
        ext i
        fin_cases i <;> simp [Plane.mk]
      have hseg : δ • R.vector (j,!β) ∈ segment ℝ (0 : Plane) (R.vector (j,!β)) := by
        rw [segment_eq_image']
        exact ⟨δ,⟨hδ.le,hδ1⟩,by simp⟩
      have hPrefix : δ • R.vector (j,!β) ∈ R.H '' armPrefix γ (j,!β) (R.cut (j,!β)) := by
        rw [R.prefix_image,zero_add]
        exact hseg
      obtain ⟨y,⟨t,ht,heγ⟩,heH⟩ := hPrefix
      have hPoint : F (c.map (q * Circle.exp (if !β then ε*t.val else -(ε*t.val)))) = Plane.mk (-δ) 0 := by
        rw [hFormula,← hγ (!β) t,heγ,heH,hTδ]
      have hInv : F.symm (Plane.mk (-δ) 0) = c.map (q * Circle.exp (if !β then ε*t.val else -(ε*t.val))) := by
        rw [← hPoint]
        exact F.left_inv (hFSource.symm ▸ hsource (!β) t)
      have htpos : 0 < t.val := by
        by_contra hn
        have htzero : t.val = 0 := le_antisymm (le_of_not_gt hn) t.property.1
        have hpzero : c.map (q * Circle.exp (if !β then ε*t.val else -(ε*t.val))) = p := by
          simp [htzero,hq]
        rw [hpzero,hFp] at hPoint
        have hh := congrArg (fun z : Plane => z 0) hPoint
        change (0 : ℝ) = -δ at hh
        linarith
      exact ⟨t,htpos,ht,hInv⟩
    have hStartTargetU : Plane.mk (-δU) 0 ∈ FU.target :=
      (hConnectorCoreU (left_mem_segment ℝ _ _)).1
    have hStartTargetZ : Plane.mk (-δZ) 0 ∈ FZ.target :=
      (hConnectorCoreZ (left_mem_segment ℝ _ _)).1
    have hδU1 : δU ≤ 1 := by
      have hn : ‖Plane.mk (-δU) 0‖ < ρU := by
        simpa using (hConnectorCoreU (left_mem_segment ℝ _ _)).2
      have hh := PiLp.norm_apply_le (Plane.mk (-δU) 0) 0
      change |-δU| ≤ ‖Plane.mk (-δU) 0‖ at hh
      rw [abs_neg,abs_of_pos hδU] at hh
      linarith
    have hδZ1 : δZ ≤ 1 := by
      have hn : ‖Plane.mk (-δZ) 0‖ < ρZ := by
        simpa using (hConnectorCoreZ (left_mem_segment ℝ _ _)).2
      have hh := PiLp.norm_apply_le (Plane.mk (-δZ) 0) 0
      change |-δZ| ≤ ‖Plane.mk (-δZ) 0‖ at hh
      rw [abs_neg,abs_of_pos hδZ] at hh
      linarith
    obtain ⟨tU,htUPos,htUCut,hStartParameterU⟩ :=
      hNegativeAxisActualArm (r v).val u (qU (eU ⟨v,huSelected⟩))
        (by simpa [eU,JU] using hqU (eU ⟨v,huSelected⟩)) εU EcornerU FU hFUSource hFU0
        _ _ RU (eU ⟨v,huSelected⟩) βU
        (by intro sign t; simp [eU,JU])
        (by intro sign t; simpa [eU,JU] using hArmsUSource (eU ⟨v,huSelected⟩) sign t)
        TU hFUFormula hTUVector hRUOpposite δU hδU hδU1 hStartTargetU
    obtain ⟨tZ,htZPos,htZCut,hStartParameterZ⟩ :=
      hNegativeAxisActualArm (r v).val z (qZ (eZ ⟨v,hzSelected⟩))
        (by simpa [eZ,JZ] using hqZ (eZ ⟨v,hzSelected⟩)) εZ EcornerZ FZ hFZSource hFZ0
        _ _ RZ (eZ ⟨v,hzSelected⟩) βZ
        (by intro sign t; simp [eZ,JZ])
        (by intro sign t; simpa [eZ,JZ] using hArmsZSource (eZ ⟨v,hzSelected⟩) sign t)
        TZ hFZFormula hTZVector hRZOpposite δZ hδZ hδZ1 hStartTargetZ
    have htUShort : tU.val < τU := by
      by_contra hn
      apply Set.disjoint_left.mp hSelectedTailU (hConnectorBallU (left_mem_segment ℝ _ _))
      refine ⟨tU,le_of_not_gt hn,?_⟩
      change TU (RU.H (EcornerU ((r (eU.symm (eU ⟨v,huSelected⟩)).val).val.map
        (qU (eU ⟨v,huSelected⟩) * Circle.exp (if !βU then εU*tU.val else -(εU*tU.val)))))) = _
      simp only [Equiv.symm_apply_apply]
      rw [← hFUFormula,← hStartParameterU,FU.right_inv hStartTargetU]
    have htZShort : tZ.val < τZ := by
      by_contra hn
      apply Set.disjoint_left.mp hSelectedTailZ (hConnectorBallZ (left_mem_segment ℝ _ _))
      refine ⟨tZ,le_of_not_gt hn,?_⟩
      change TZ (RZ.H (EcornerZ ((r (eZ.symm (eZ ⟨v,hzSelected⟩)).val).val.map
        (qZ (eZ ⟨v,hzSelected⟩) * Circle.exp (if !βZ then εZ*tZ.val else -(εZ*tZ.val)))))) = _
      simp only [Equiv.symm_apply_apply]
      rw [← hFZFormula,← hStartParameterZ,FZ.right_inv hStartTargetZ]
    have hAngularExteriorArm (c : Curve S) (b : Circle)
        (a z : ℝ) (haz : a < z) (p : S) (q : Circle) (hq : c.map q = p)
        (hp : p = c.map (b*Circle.exp a) ∨ p = c.map (b*Circle.exp z))
        (h : ℝ) (hh : 0 < h) (hlen : z-a+h < 2*Real.pi) :
        c.map (q*Circle.exp (if !(decide (p = c.map (b*Circle.exp a))) then h else -h)) ∉
          (fun t : ℝ => c.map (b*Circle.exp t)) '' Icc a z := by
      classical
      have hExt : c.map (b * Circle.exp (a-h)) ∉ (fun t : ℝ => c.map (b * Circle.exp t)) '' Icc a z ∧
          c.map (b * Circle.exp (z+h)) ∉ (fun t : ℝ => c.map (b * Circle.exp t)) '' Icc a z := by
        constructor
        · rintro ⟨t,ht,he⟩
          have hExp : Circle.exp t = Circle.exp (a-h) := mul_left_cancel (c.embedded.injective he)
          have hi := Circle.exp_injOn_Icc (a := a-h) (b := z) (by linarith)
            (show t ∈ Icc (a-h) z by constructor <;> linarith [ht.1,ht.2])
            (show a-h ∈ Icc (a-h) z by constructor <;> linarith) hExp
          linarith [ht.1]
        · rintro ⟨t,ht,he⟩
          have hExp : Circle.exp t = Circle.exp (z+h) := mul_left_cancel (c.embedded.injective he)
          have hi := Circle.exp_injOn_Icc (a := a) (b := z+h) (by linarith)
            (show t ∈ Icc a (z+h) by constructor <;> linarith [ht.1,ht.2])
            (show z+h ∈ Icc a (z+h) by constructor <;> linarith) hExp
          linarith [ht.2]
      by_cases hpa : p = c.map (b*Circle.exp a)
      · simp only [hpa,decide_true,Bool.not_true,Bool.false_eq_true,if_false]
        have hq' : q = b*Circle.exp a := c.embedded.injective (hq.trans hpa)
        have hmul : q * Circle.exp (-h) = b*Circle.exp (a-h) := by
          rw [hq',sub_eq_add_neg,Circle.exp_add,mul_assoc]
        rw [hmul]
        exact hExt.1
      · have hpz : p = c.map (b*Circle.exp z) := hp.resolve_left hpa
        simp only [hpa,decide_false,Bool.not_false,if_true]
        have hq' : q = b*Circle.exp z := c.embedded.injective (hq.trans hpz)
        have hmul : q*Circle.exp h = b*Circle.exp (z+h) := by
          rw [hq',Circle.exp_add,mul_assoc]
        rw [hmul]
        exact hExt.2
    have hUAngleEndpoint : u = (r v).val.map (b*Circle.exp a) ∨
        u = (r v).val.map (b*Circle.exp zangle) :=
      hSelectedEndpointOrientation.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    have hZAngleEndpoint : z = (r v).val.map (b*Circle.exp a) ∨
        z = (r v).val.map (b*Circle.exp zangle) :=
      hSelectedEndpointOrientation.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
    have hCornerStartExteriorU : cornerArcU 0 ∉ Set.range f := by
      rw [hCornerStartU,hStartParameterU,hAngleImage]
      have hsmall : zangle-a+εU*tU.val < 2*Real.pi := by
        have hh := (mul_lt_mul_of_pos_left htUShort hεU).trans hετU
        dsimp [gap] at hh
        linarith
      simpa [βU,γ] using hAngularExteriorArm (r v).val b a zangle hazangle u
        (qU (eU ⟨v,huSelected⟩)) (by simpa [eU,JU] using hqU (eU ⟨v,huSelected⟩)) hUAngleEndpoint
        (εU*tU.val) (mul_pos hεU htUPos) hsmall
    have hCornerStartExteriorZ : cornerArcZ 0 ∉ Set.range f := by
      rw [hCornerStartZ,hStartParameterZ,hAngleImage]
      have hsmall : zangle-a+εZ*tZ.val < 2*Real.pi := by
        have hh := (mul_lt_mul_of_pos_left htZShort hεZ).trans hετZ
        dsimp [gap] at hh
        linarith
      simpa [βZ,γ] using hAngularExteriorArm (r v).val b a zangle hazangle z
        (qZ (eZ ⟨v,hzSelected⟩)) (by simpa [eZ,JZ] using hqZ (eZ ⟨v,hzSelected⟩)) hZAngleEndpoint
        (εZ*tZ.val) (mul_pos hεZ htZPos) hsmall
    have hCornerStartCurveU : cornerArcU 0 ∈ (r v).val.image := by
      rw [hCornerStartU,hStartParameterU]
      exact ⟨_,rfl⟩
    have hCornerStartCurveZ : cornerArcZ 0 ∈ (r v).val.image := by
      rw [hCornerStartZ,hStartParameterZ]
      exact ⟨_,rfl⟩
    have hCornerStartOutsideDiskU : cornerArcU 0 ∉ Set.range d := by
      intro hx
      exact hCornerStartExteriorU (hDcurve ▸ ⟨hx,hCornerStartCurveU⟩)
    have hCornerStartOutsideDiskZ : cornerArcZ 0 ∉ Set.range d := by
      intro hx
      exact hCornerStartExteriorZ (hDcurve ▸ ⟨hx,hCornerStartCurveZ⟩)
    have hDisjointNeighborhoods {J : Type} [Fintype J]
        (p : J → S) (hp : Function.Injective p)
        (O : J → Set S) (hO : ∀ j, IsOpen (O j)) (hmem : ∀ j, p j ∈ O j) :
        ∃ W : J → Set S, (∀ j, IsOpen (W j) ∧ p j ∈ W j ∧ W j ⊆ O j) ∧
          ∀ i j, i ≠ j → Disjoint (W i) (W j) := by
      classical
      have hSep : ∀ i j : J, ∃ A B : Set S, IsOpen A ∧ IsOpen B ∧ p i ∈ A ∧ p j ∈ B ∧
          (i ≠ j → Disjoint A B) := by
        intro i j
        by_cases hij : i = j
        · exact ⟨Set.univ,Set.univ,isOpen_univ,isOpen_univ,Set.mem_univ _,Set.mem_univ _,fun hn => False.elim (hn hij)⟩
        · obtain ⟨A,B,hA,hB,hi,hj,hDis⟩ := t2_separation (fun he => hij (hp he))
          exact ⟨A,B,hA,hB,hi,hj,fun _ => hDis⟩
      choose A B hA hB hiA hjB hDis using hSep
      let W : J → Set S := fun i => O i ∩ ⋂ j, A i j ∩ B j i
      refine ⟨W,?_,?_⟩
      · intro i
        refine ⟨(hO i).inter (isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i))),?_,Set.inter_subset_left⟩
        exact ⟨hmem i,Set.mem_iInter.mpr (fun j => ⟨hiA i j,hjB j i⟩)⟩
      · intro i j hij
        exact (hDis i j hij).mono
          (fun x hx => (Set.mem_iInter.mp hx.2 j).1)
          (fun x hx => (Set.mem_iInter.mp hx.2 i).2)
    let Pg : Set S := ⋃ i : I, if i = w then ∅ else (Set.range g \ {u,z}) ∩ (r i).val.image
    have hPg : Pg.Finite := by
      apply Set.finite_iUnion
      intro i
      split_ifs with hi
      · exact Set.finite_empty
      · exact (hr w i (Ne.symm hi)).1.subset (fun x hx => ⟨hgcurve hx.1.1,hx.2⟩)
    have hPgFacts (p : S) (hp : p ∈ Pg) :
        p ∈ Set.range g ∧ p ≠ u ∧ p ≠ z ∧ p ∈ (r w).val.image ∧ p ∉ (r v).val.image := by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      by_cases hiw : i = w
      · simp [Pg,hiw] at hi
      · simp only [hiw,ite_false,Set.mem_inter_iff,Set.mem_diff,Set.mem_insert_iff,
          Set.mem_singleton_iff] at hi
        have hne : p ≠ u ∧ p ≠ z := not_or.mp hi.1.2
        refine ⟨hi.1.1,hne.1,hne.2,hgcurve hi.1.1,?_⟩
        intro hv
        have hm : p ∈ ({u,z} : Set S) := hgmeet ▸ ⟨hi.1.1,hv⟩
        exact hi.1.2 hm
    letI : Fintype Pg := hPg.fintype
    have hCornersClosed : IsClosed (Set.range cornerArcU ∪ Set.range cornerArcZ) :=
      (isCompact_range cornerArcU.continuous).isClosed.union (isCompact_range cornerArcZ.continuous).isClosed
    have hEachInteriorNeighborhood (p : Pg) : ∃ Q : Set S,
        IsOpen Q ∧ p.val ∈ Q ∧ Q ⊆ V ∩ Eopposite.source ∧
        Disjoint Q (r v).val.image ∧ Disjoint Q (Set.range cornerArcU ∪ Set.range cornerArcZ) ∧
        (∀ i, p.val ∉ (r i).val.image → Disjoint Q (r i).val.image) ∧
        (∀ i j, i ≠ j → Q ∩ ((r i).val.image ∩ (r j).val.image) ⊆ {p.val}) := by
      have hp := hPgFacts p.val p.property
      have hpV : p.val ∈ V := hdV ((hDcurveW.symm ▸ hp.1).1)
      obtain ⟨N,N',hN,hN',hpN,huN,hNV,hN'V,hNN',hNNon,hN'Non,hNContacts,hN'Contacts⟩ :=
        hCornerIsolation r hr p.val u hp.2.1 V hV hpV huV
      have hpE : p.val ∈ Eopposite.source := hGInOpposite (hGAngleImage ▸ hp.1)
      have hpNotCorners : p.val ∉ Set.range cornerArcU ∪ Set.range cornerArcZ := by
        rintro (hU | hZ)
        · exact Set.disjoint_left.mp hCornerArcOppositeAvoidU hU hp.2.2.2.1
        · exact Set.disjoint_left.mp hCornerArcOppositeAvoidZ hZ hp.2.2.2.1
      let Q := (N ∩ Eopposite.source) ∩ (Set.range cornerArcU ∪ Set.range cornerArcZ)ᶜ
      have hQN : Q ⊆ N := fun x hx => hx.1.1
      refine ⟨Q,(hN.inter Eopposite.open_source).inter hCornersClosed.isOpen_compl,
        ⟨⟨hpN,hpE⟩,hpNotCorners⟩,(fun x hx => ⟨hNV hx.1.1,hx.1.2⟩),
        (hNNon v hp.2.2.2.2).mono_left hQN,?_,?_,?_⟩
      · exact Set.disjoint_left.mpr (fun x hx hc => hx.2 hc)
      · intro i hi
        exact (hNNon i hi).mono_left hQN
      · intro i j hij x hx
        exact hNContacts i j hij ⟨hQN hx.1,hx.2⟩
    choose Q hQ hpQ hQSub hQSelected hQCorners hQNon hQContacts using hEachInteriorNeighborhood
    obtain ⟨W,hW,hWDisjoint⟩ := hDisjointNeighborhoods (fun p : Pg => p.val)
      Subtype.val_injective Q hQ hpQ
    have hInteriorContactStars := fun (p : Pg) => hActualCorner r hr w p.val (W p)
      (hW p).1 (hW p).2.1 (hPgFacts p.val p.property).2.2.2.1
      (fun i j hij x hx => hQContacts p i j hij ⟨(hW p).2.2 hx.1,hx.2⟩)
    have hInteriorContactSupportsAvoidSelected (p : Pg) : Disjoint (W p) (r v).val.image :=
      (hQSelected p).mono_left (hW p).2.2
    have hInteriorContactSupportsAvoidCorners (p : Pg) :
        Disjoint (W p) (Set.range cornerArcU ∪ Set.range cornerArcZ) :=
      (hQCorners p).mono_left (hW p).2.2
    have hInteriorContactModels (p : Pg) :
        let J := {i : I // p.val ∈ (r i).val.image}
        let e := Fintype.equivFin J
        let K := {j : Fin (Fintype.card J) // (e.symm j).val ≠ w}
        ∃ F : OpenPartialHomeomorph S Plane, ∃ ρ : ℝ, ∃ a b : K → Plane,
          F.source ⊆ W p ∧ p.val ∈ F.source ∧ F p.val = 0 ∧ 0 < ρ ∧
          (∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ (r w).val.image ↔ F x 1 = 0)) ∧
          (∀ j, 0 < a j 1) ∧ (∀ j, b j 1 < 0) ∧
          (∀ j x, x ∈ F.source → ‖F x‖ < ρ →
            (x ∈ (r (e.symm j.val).val).val.image ↔
              F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))) ∧
          (∀ i, p.val ∉ (r i).val.image → Disjoint F.source (r i).val.image) := by
      let J := {i : I // p.val ∈ (r i).val.image}
      let e := Fintype.equivFin J
      let K := {j : Fin (Fintype.card J) // (e.symm j).val ≠ w}
      have hpw := (hPgFacts p.val p.property).2.2.2.1
      obtain ⟨E,ε,hpE,hEp,hEW,hε,hεπ,q,hq,hArms,hClosed,hZero,R,hROpp,hRCore⟩ := hInteriorContactStars p
      obtain ⟨T,F,ρ,hSource,hF0,hρ,hρ1,hFormula,hTv,hNorm,hAxis,hModel⟩ :=
        hStraightCore (fun j => (r (e.symm j).val).val) p.val E hpE hEp _ R
          (e ⟨w,hpw⟩) hROpp false hRCore
      have hAxisW : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ (r w).val.image ↔ F x 1 = 0) := by
        simpa [e,J] using hAxis
      have hSigns (j : K) :
          (T (R.vector (j.val,false))) 1 * (T (R.vector (j.val,true))) 1 < 0 := by
        apply hCrossingSigns (r w).val (r (e.symm j.val).val).val p.val
          ((hr w (e.symm j.val).val j.property.symm).2 p.val ⟨hpw,(e.symm j.val).property⟩)
          F (hSource.symm ▸ hpE) hF0 ρ hρ _ _ hAxisW
        · intro x hx hc
          have hxQ : x ∈ Q p := (hW p).2.2 (hEW (hSource ▸ hx))
          exact Set.mem_singleton_iff.mp (hQContacts p w (e.symm j.val).val j.property.symm ⟨hxQ,hc⟩)
        · intro x hx hxN hxc
          exact (hModel j.val x hx hxN).mp hxc
      have hOriented : ∀ j : K, ∃ a b : Plane, 0 < a 1 ∧ b 1 < 0 ∧
          segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b =
          segment ℝ (0 : Plane) (T (R.vector (j.val,false))) ∪
          segment ℝ (0 : Plane) (T (R.vector (j.val,true))) := by
        intro j
        exact hOrientPair _ _ (hSigns j)
      choose a b ha hb hUnion using hOriented
      refine ⟨F,ρ,a,b,(fun x hx => hEW (hSource ▸ hx)),(hSource.symm ▸ hpE),hF0,hρ,hAxisW,ha,hb,?_,?_⟩
      · intro j x hx hxN
        rw [hUnion j]
        exact hModel j.val x hx hxN
      · intro i hi
        exact (hQNon p i hi).mono_left (fun x hx => (hW p).2.2 (hEW (hSource ▸ hx)))
    have hPositiveHalfChoice
        (c : Curve S) (p : S) (E F : OpenPartialHomeomorph S Plane)
        (hFE : F.source ⊆ E.source) (hpF : p ∈ F.source) (hFp : F p = 0) (hEp : E p 1 = 0)
        (ρ η : ℝ) (hη : 0 < η)
        (hBall : Metric.ball (0 : Plane) η ⊆ F.target ∩ Metric.ball (0 : Plane) ρ)
        (hEaxis : ∀ x ∈ E.source, x ∈ c.image ↔ E x 1 = 0)
        (hFaxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.image ↔ F x 1 = 0)) :
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∀ y ∈ Metric.ball (0 : Plane) η, 0 < σ*y 1 → 0 < E (F.symm y) 1 := by
      classical
      let C := F.source ∩ F ⁻¹' Metric.ball (0 : Plane) η
      have hC : IsOpen C := F.isOpen_inter_preimage isOpen_ball
      have hEC : IsOpen (E '' C) := E.isOpen_image_of_subset_source hC (fun x hx => hFE hx.1)
      have hpEC : E p ∈ E '' C := ⟨p,⟨hpF,by change F p ∈ Metric.ball (0 : Plane) η; rw [hFp]; simpa using hη⟩,rfl⟩
      let v : ℝ → Plane := fun t => E p + Plane.mk 0 t
      have hv : Continuous v := by fun_prop
      have hOpen : IsOpen (v ⁻¹' (E '' C)) := hEC.preimage hv
      have h0 : (0 : ℝ) ∈ v ⁻¹' (E '' C) := by
        have hz : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
        simpa [v,hz] using hpEC
      obtain ⟨r,hr,hvr⟩ := Metric.isOpen_iff.mp hOpen 0 h0
      let τ := r/2
      have hτ : 0 < τ := half_pos hr
      obtain ⟨x,hx,hEx⟩ := hvr (show τ ∈ Metric.ball (0 : ℝ) r by
        rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hτ]; dsimp [τ]; linarith)
      have hExy : E x 1 = τ := by
        have hh := congrArg (fun z : Plane => z 1) hEx
        change E x 1 = E p 1 + τ at hh
        simpa [hEp] using hh
      let q := F x
      have hqBall : q ∈ Metric.ball (0 : Plane) η := hx.2
      have hqx : F.symm q = x := F.left_inv hx.1
      have hqN : ‖F x‖ < ρ := by simpa using (hBall hqBall).2
      have hqNe : q 1 ≠ 0 := by
        intro he
        have hc := (hFaxis x hx.1 hqN).mpr he
        have hh := (hEaxis x (hFE hx.1)).mp hc
        linarith
      let σ : ℝ := if 0 < q 1 then 1 else -1
      have hσ : σ = 1 ∨ σ = -1 := by dsimp [σ]; split_ifs <;> simp
      have hqSign : 0 < σ*q 1 := by
        dsimp [σ]
        split_ifs with hq
        · simpa using hq
        · have hn : q 1 < 0 := lt_of_le_of_ne (le_of_not_gt hq) hqNe
          simpa using neg_pos.mpr hn
      let P : Set Plane := Metric.ball (0 : Plane) η ∩ {y | 0 < σ*y 1}
      have hP : IsPreconnected P := (convex_ball (0 : Plane) η).inter
        (convex_halfSpace_gt (𝕜 := ℝ) (f := fun y : Plane => σ*y 1)
          ⟨by intros x y; change σ*(x 1+y 1)=σ*x 1+σ*y 1; ring,
           by intros a x; change σ*(a*x 1)=a*(σ*x 1); ring⟩ 0) |>.isPreconnected
      let G : P → ℝ := fun y => E (F.symm y.val) 1
      have hFS : Continuous (fun y : P => F.symm y.val) :=
        F.symm.continuousOn.comp_continuous continuous_subtype_val (fun y => (hBall y.property.1).1)
      have hEFS : Continuous (fun y : P => E (F.symm y.val)) :=
        E.continuousOn.comp_continuous hFS (fun y => hFE (F.map_target (hBall y.property.1).1))
      have hG : Continuous G := (show Continuous (fun z : Plane => z 1) by fun_prop).comp hEFS
      have hGNe (y : P) : G y ≠ 0 := by
        intro he
        have hyS := F.map_target (hBall y.property.1).1
        have hyE := hFE hyS
        have hc := (hEaxis _ hyE).mpr he
        have hyN : ‖F (F.symm y.val)‖ < ρ := by
          rw [F.right_inv (hBall y.property.1).1]
          simpa using (hBall y.property.1).2
        have hh := (hFaxis _ hyS hyN).mp hc
        rw [F.right_inv (hBall y.property.1).1] at hh
        have hp := y.property.2
        change 0 < σ*y.val 1 at hp
        rw [hh,mul_zero] at hp
        exact (lt_irrefl 0) hp
      have hRangeConn : IsPreconnected (Set.range G) := by
        have : PreconnectedSpace P := isPreconnected_iff_preconnectedSpace.mp hP
        exact isPreconnected_range hG
      have hRangeSub : Set.range G ⊆ Set.Ioi 0 ∪ Set.Iio 0 := by
        rintro z ⟨y,rfl⟩
        exact (lt_or_gt_of_ne (hGNe y)).symm
      let qp : P := ⟨q,⟨hqBall,hqSign⟩⟩
      have hqp : 0 < G qp := by
        change 0 < E (F.symm q) 1
        rw [hqx,hExy]
        exact hτ
      have hPositive : Set.range G ⊆ Set.Ioi 0 :=
        hRangeConn.subset_left_of_subset_union isOpen_Ioi isOpen_Iio
          (Set.disjoint_left.mpr (by intro z hz hz'; change 0 < z at hz; change z < 0 at hz'; linarith))
          hRangeSub ⟨G qp,⟨⟨qp,rfl⟩,hqp⟩⟩
      refine ⟨σ,hσ,?_⟩
      intro y hy hys
      exact hPositive ⟨⟨y,⟨hy,hys⟩⟩,rfl⟩
    have hMirrorPositiveCore {J : Type}
        (E F : OpenPartialHomeomorph S Plane) (c : Curve S) (p : S)
        (hFp : F p = 0) (ρ η : ℝ) (a b : J → Plane)
        (hBall : Metric.ball (0 : Plane) η ⊆ F.target ∩ Metric.ball (0 : Plane) ρ)
        (haxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.image ↔ F x 1 = 0))
        (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
        (d : J → Curve S)
        (hmodel : ∀ j x, x ∈ F.source → ‖F x‖ < ρ →
          (x ∈ (d j).image ↔ F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)))
        (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
        (hPositive : ∀ y ∈ Metric.ball (0 : Plane) η, 0 < σ*y 1 → 0 < E (F.symm y) 1) :
        ∃ F' : OpenPartialHomeomorph S Plane, ∃ a' b' : J → Plane,
          F'.source = F.source ∧ F' p = 0 ∧
          (Metric.ball (0 : Plane) η ⊆ F'.target ∩ Metric.ball (0 : Plane) ρ) ∧
          (∀ x ∈ F'.source, ‖F' x‖ < ρ → (x ∈ c.image ↔ F' x 1 = 0)) ∧
          (∀ j, 0 < a' j 1) ∧ (∀ j, b' j 1 < 0) ∧
          (∀ j x, x ∈ F'.source → ‖F' x‖ < ρ →
            (x ∈ (d j).image ↔ F' x ∈ segment ℝ (0 : Plane) (a' j) ∪ segment ℝ (0 : Plane) (b' j))) ∧
          (∀ y ∈ Metric.ball (0 : Plane) η, 0 < y 1 → 0 < E (F'.symm y) 1) := by
      rcases hσ with rfl | rfl
      · exact ⟨F,a,b,rfl,hFp,hBall,haxis,ha,hb,hmodel,by simpa using hPositive⟩
      · let N : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.neg ℝ
        let F' := F.transHomeomorph N.toHomeomorph
        have hFormula (x : S) : F' x = -F x := rfl
        have hInvFormula (y : Plane) : F'.symm y = F.symm (-y) := rfl
        have hSegment (v z : Plane) : z ∈ segment ℝ (0 : Plane) v ↔
            -z ∈ segment ℝ (0 : Plane) (-v) := by
          have hi := image_segment ℝ N.toLinearMap.toAffineMap (0 : Plane) v
          change N '' segment ℝ (0 : Plane) v = segment ℝ (N 0) (N v) at hi
          rw [map_zero] at hi
          change z ∈ segment ℝ (0 : Plane) v ↔ N z ∈ segment ℝ (0 : Plane) (N v)
          rw [← hi]
          exact ⟨fun hz => ⟨z,hz,rfl⟩,fun ⟨w,hw,he⟩ => N.injective he ▸ hw⟩
        refine ⟨F',fun j => -b j,fun j => -a j,rfl,?_,?_,?_,?_,?_,?_,?_⟩
        · rw [hFormula,hFp,neg_zero]
        · intro y hy
          have hyneg : -y ∈ Metric.ball (0 : Plane) η := by simpa [Metric.mem_ball,dist_zero_right] using hy
          have hyF := (hBall hyneg).1
          refine ⟨?_,(hBall hy).2⟩
          change N.symm y ∈ F.target
          exact hyF
        · intro x hx hxN
          have hxNorm : ‖F x‖ < ρ := by simpa [hFormula] using hxN
          rw [haxis x hx hxNorm,hFormula]
          change (F x 1 = 0 ↔ (-F x) 1 = 0)
          simp
        · intro j
          change 0 < -(b j) 1
          exact neg_pos.mpr (hb j)
        · intro j
          change -(a j) 1 < 0
          exact neg_neg_of_pos (ha j)
        · intro j x hx hxN
          have hxNorm : ‖F x‖ < ρ := by simpa [hFormula] using hxN
          rw [hmodel j x hx hxNorm,hFormula]
          change (F x ∈ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ↔
            (-F x ∈ segment ℝ (0 : Plane) (-b j) ∪ segment ℝ (0 : Plane) (-a j))
          simp only [Set.mem_union]
          exact (or_congr (hSegment (a j) (F x)) (hSegment (b j) (F x))).trans or_comm
        · intro y hy hyPos
          rw [hInvFormula]
          apply hPositive (-y) (by simpa [Metric.mem_ball,dist_zero_right] using hy)
          simpa using hyPos
    have hFiniteParallelArc {J : Type} [Fintype J] (a b : J → Plane)
        (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
        (η : ℝ) (hη : 0 < η) :
        ∃ δ h : ℝ, 0 < δ ∧ 0 < h ∧
          let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
          C ⊆ Metric.ball (0 : Plane) η ∧ IsArcBetween C (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          Disjoint C {x | x 1 = 0} ∧
          (∀ j, Plane.mk (-δ) h ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ∧
          (∀ j, Plane.mk δ h ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ∧
          (∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).Finite ∧
            (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).ncard ≤ 1) := by
      classical
      have hCounts (a b : Plane) (ha : 0 < a 1) (hb : b 1 < 0) (δ h : ℝ) (hh : 0 < h) :
          let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
          Disjoint C {x | x 1 = 0} ∧
          (C ∩ (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b)).Finite ∧
          (C ∩ (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b)).ncard ≤ 1 := by
        let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
        have hCy (x : Plane) (hx : x ∈ C) : x 1 = h := by
          change x ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) at hx
          rw [segment_eq_image'] at hx
          obtain ⟨t,ht,he⟩ := hx
          have hy := congrArg (fun z : Plane => z 1) he
          change h+t*(h-h) = x 1 at hy
          simpa using hy.symm
        have hLower : Disjoint C (segment ℝ (0 : Plane) b) := by
          apply Set.disjoint_left.mpr
          intro x hx hxB
          rw [segment_eq_image'] at hxB
          obtain ⟨t,ht,he⟩ := hxB
          have hy := congrArg (fun z : Plane => z 1) he
          change 0+t*(b 1-0) = x 1 at hy
          rw [hCy x hx] at hy
          nlinarith [ht.1]
        have hSingle : (C ∩ segment ℝ (0 : Plane) a).Subsingleton := by
          intro x hx y hy
          rw [segment_eq_image'] at hx hy
          obtain ⟨t,ht,he⟩ := hx.2
          obtain ⟨s,hs,hse⟩ := hy.2
          have hxt := congrArg (fun z : Plane => z 1) he
          have hys := congrArg (fun z : Plane => z 1) hse
          change 0+t*(a 1-0) = x 1 at hxt
          change 0+s*(a 1-0) = y 1 at hys
          rw [hCy x hx.1] at hxt
          rw [hCy y hy.1] at hys
          have hts : t = s := by nlinarith
          exact he.symm.trans (hts ▸ hse)
        have hset : C ∩ (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) = C ∩ segment ℝ (0 : Plane) a := by
          rw [Set.inter_union_distrib_left,Set.disjoint_iff_inter_eq_empty.mp hLower,Set.union_empty]
        refine ⟨Set.disjoint_left.mpr (fun x hx hx0 => ?_),?_,?_⟩
        · have hy := hCy x hx
          change x 1 = 0 at hx0
          linarith
        · rw [hset]
          exact hSingle.finite
        · rw [hset]
          exact (Set.ncard_le_one hSingle.finite).mpr hSingle
      have hZero : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
      have hOpen : IsOpen {t : ℝ | Plane.mk (-t) 0 ∈ ball (0 : Plane) η ∧ Plane.mk t 0 ∈ ball (0 : Plane) η} := by
        exact (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop))
      have h0 : (0 : ℝ) ∈ {t : ℝ | Plane.mk (-t) 0 ∈ ball (0 : Plane) η ∧ Plane.mk t 0 ∈ ball (0 : Plane) η} := by
        constructor <;> simpa [neg_zero,hZero] using hη
      obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hOpen 0 h0
      let δ := r/2
      have hδ : 0 < δ := half_pos hr
      have hBase := hBall (show δ ∈ ball (0 : ℝ) r by
        rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ]; dsimp [δ]; linarith)
      have hOpenH : IsOpen {t : ℝ | Plane.mk (-δ) t ∈ ball (0 : Plane) η ∧ Plane.mk δ t ∈ ball (0 : Plane) η} := by
        exact (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop))
      obtain ⟨s,hs,hEndBall⟩ := Metric.isOpen_iff.mp hOpenH 0 hBase
      let bad : Set ℝ := Set.range (fun j => (-δ)*(a j) 1/(a j) 0) ∪
        Set.range (fun j => δ*(a j) 1/(a j) 0)
      have hBad : bad.Finite := (Set.finite_range _).union (Set.finite_range _)
      obtain ⟨h,hh,hAvoid⟩ := (Set.Ioo_infinite (half_pos hs)).exists_notMem_finite hBad
      have hEnds := hEndBall (show h ∈ ball (0 : ℝ) s by
        rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hh.1]; linarith [hh.2])
      have hEnd (ξ : ℝ) (hξ : ξ ≠ 0) (hBadξ : Set.range (fun j => ξ*(a j) 1/(a j) 0) ⊆ bad) :
          ∀ j, Plane.mk ξ h ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j) := by
        intro j hj
        have hUpper (hx : Plane.mk ξ h ∈ segment ℝ (0 : Plane) (a j)) : False := by
          rw [segment_eq_image'] at hx
          obtain ⟨t,ht,he⟩ := hx
          have hx0 := congrArg (fun z : Plane => z 0) he
          have hx1 := congrArg (fun z : Plane => z 1) he
          change 0+t*((a j) 0-0) = ξ at hx0
          change 0+t*((a j) 1-0) = h at hx1
          simp only [zero_add,sub_zero] at hx0 hx1
          have ha0 : (a j) 0 ≠ 0 := by intro hz; rw [hz,mul_zero] at hx0; exact hξ hx0.symm
          apply hAvoid
          apply hBadξ
          refine ⟨j,(div_eq_iff ha0).mpr ?_⟩
          rw [← hx0,← hx1]
          ring
        have hLower (hx : Plane.mk ξ h ∈ segment ℝ (0 : Plane) (b j)) : False := by
          rw [segment_eq_image'] at hx
          obtain ⟨t,ht,he⟩ := hx
          have hy := congrArg (fun z : Plane => z 1) he
          change 0+t*((b j) 1-0) = h at hy
          nlinarith [ht.1,hb j,hh.1]
        exact hj.elim hUpper hLower
      have hArc : IsArcBetween (segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)) (Plane.mk (-δ) h) (Plane.mk δ h) := by
        apply isArcBetween_segment
        intro he
        have hc := congrArg (fun z : Plane => z 0) he
        change -δ = δ at hc
        linarith
      refine ⟨δ,h,hδ,hh.1,(convex_ball (0 : Plane) η).segment_subset hEnds.1 hEnds.2,hArc,?_,?_,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro x hx hx0
        rw [segment_eq_image'] at hx
        obtain ⟨t,ht,he⟩ := hx
        have hy := congrArg (fun z : Plane => z 1) he
        change h+t*(h-h) = x 1 at hy
        change x 1 = 0 at hx0
        nlinarith [hh.1]
      · exact hEnd (-δ) (neg_ne_zero.mpr (ne_of_gt hδ)) Set.subset_union_left
      · exact hEnd δ (ne_of_gt hδ) Set.subset_union_right
      · intro j
        exact (hCounts (a j) (b j) (ha j) (hb j) δ h hh.1).2
    have hHorizontalChartArc
        (F : OpenPartialHomeomorph S Plane) (δ h : ℝ) (hh : 0 < δ)
        (hTarget : segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          Set.range f = F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
          f 0 = F.symm (Plane.mk (-δ) h) ∧ f 1 = F.symm (Plane.mk δ h) := by
      let γ : Interval → Plane := fun t => Plane.mk (-δ+2*δ*t.val) h
      have hγ : Continuous γ := by fun_prop
      have hγSeg (t : Interval) : γ t ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) := by
        rw [segment_eq_image']
        refine ⟨t.val,t.property,?_⟩
        ext i
        fin_cases i <;> simp [γ,Plane.mk] <;> ring
      let f : C(Interval,S) := ⟨fun t => F.symm (γ t),
        F.symm.continuousOn.comp_continuous hγ (fun t => hTarget (hγSeg t))⟩
      have hinj : Function.Injective f := by
        intro t s he
        have hg : γ t = γ s := F.symm.injOn (hTarget (hγSeg t)) (hTarget (hγSeg s)) he
        have hv := congrArg (fun z : Plane => z 0) hg
        change -δ+2*δ*t.val = -δ+2*δ*s.val at hv
        apply Subtype.ext
        nlinarith
      refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_⟩
      · ext x
        constructor
        · rintro ⟨t,rfl⟩
          exact ⟨γ t,hγSeg t,rfl⟩
        · rintro ⟨y,hy,rfl⟩
          rw [segment_eq_image'] at hy
          obtain ⟨t,ht,he⟩ := hy
          refine ⟨⟨t,ht⟩,?_⟩
          apply congrArg F.symm
          change Plane.mk (-δ+2*δ*t) h = y
          rw [← he]
          ext i
          fin_cases i <;> simp [Plane.mk] <;> ring
      · change F.symm (γ 0) = F.symm (Plane.mk (-δ) h)
        apply congrArg F.symm
        ext i
        fin_cases i <;> simp [γ,Plane.mk] <;> ring
      · change F.symm (γ 1) = F.symm (Plane.mk δ h)
        apply congrArg F.symm
        ext i
        fin_cases i <;> simp [γ,Plane.mk] <;> ring
    have hOppositeAxisEntire : ∀ x ∈ Eopposite.source,
        x ∈ (r w).val.image ↔ Eopposite x 1 = 0 := by
      intro x hx
      rw [← hcwImage]
      exact hOppositeAxis x hx
    have hInteriorParallelArcs (p : Pg) : ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
        Set.range f ⊆ W p ∧ (∀ x ∈ Set.range f, 0 < Eopposite x 1) ∧
        Disjoint (Set.range f) (r w).val.image ∧
        (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
          (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      let J := {i : I // p.val ∈ (r i).val.image}
      let e := Fintype.equivFin J
      let K := {j : Fin (Fintype.card J) // (e.symm j).val ≠ w}
      obtain ⟨F,ρ,a,b,hFW,hpF,hF0,hρ,hAxis,ha,hb,hModel,hNon⟩ := hInteriorContactModels p
      have hFE : F.source ⊆ Eopposite.source := fun x hx => (hQSub p ((hW p).2.2 (hFW hx))).2
      have h0Target : (0 : Plane) ∈ F.target := hF0 ▸ F.map_source hpF
      obtain ⟨η,hη,hBall⟩ := Metric.isOpen_iff.mp
        (show IsOpen (F.target ∩ Metric.ball (0 : Plane) ρ) from F.open_target.inter Metric.isOpen_ball)
        0 ⟨h0Target,by simpa using hρ⟩
      have hpw := (hPgFacts p.val p.property).2.2.2.1
      have hE0 : Eopposite p.val 1 = 0 := (hOppositeAxisEntire p.val (hFE hpF)).mp hpw
      obtain ⟨σ,hσ,hPositive⟩ := hPositiveHalfChoice (r w).val p.val Eopposite F
        hFE hpF hF0 hE0 ρ η hη hBall hOppositeAxisEntire hAxis
      obtain ⟨F',a',b',hF'Source,hF'0,hBall',hAxis',ha',hb',hModel',hPositive'⟩ :=
        hMirrorPositiveCore Eopposite F (r w).val p.val hF0 ρ η a b hBall hAxis ha hb
          (fun j : K => (r (e.symm j.val).val).val) hModel σ hσ hPositive
      obtain ⟨δ,h,hδ,hh,hCBall,hCArc,hCAxis,hEndL,hEndR,hCounts⟩ :=
        hFiniteParallelArc a' b' ha' hb' η hη
      let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
      have hCCore : C ⊆ F'.target ∩ Metric.ball (0 : Plane) ρ := hCBall.trans hBall'
      obtain ⟨f,hf,hRange,hf0,hf1⟩ := hHorizontalChartArc F' δ h hδ (fun x hx => (hCCore hx).1)
      have hSurfaceSub : F'.symm '' C ⊆ W p := by
        rintro x ⟨y,hy,rfl⟩
        exact hFW (hF'Source ▸ F'.map_target (hCCore hy).1)
      have hCy (y : Plane) (hy : y ∈ C) : y 1 = h := by
        change y ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) at hy
        rw [segment_eq_image'] at hy
        obtain ⟨t,ht,he⟩ := hy
        have hy1 := congrArg (fun z : Plane => z 1) he
        change h+t*(h-h) = y 1 at hy1
        simpa using hy1.symm
      have hSurfacePositive : ∀ x ∈ F'.symm '' C, 0 < Eopposite x 1 := by
        rintro x ⟨y,hy,rfl⟩
        exact hPositive' y (hCBall hy) (by rw [hCy y hy]; exact hh)
      have hSurfaceAvoid : Disjoint (F'.symm '' C) (r w).val.image := by
        apply Set.disjoint_left.mpr
        rintro x ⟨y,hy,rfl⟩ hxw
        have hxF := F'.map_target (hCCore hy).1
        have hxN : ‖F' (F'.symm y)‖ < ρ := by
          rw [F'.right_inv (hCCore hy).1]
          simpa using (hCCore hy).2
        have hzero := (hAxis' _ hxF hxN).mp hxw
        rw [F'.right_inv (hCCore hy).1,hCy y hy] at hzero
        linarith
      have hSurfaceCounts := hTransportCounts F' ρ C hCCore
        (fun j : K => (r (e.symm j.val).val).val) a' b' hModel' hCounts
      refine ⟨f,hf,?_,?_,?_,?_⟩
      · rw [hRange]
        exact hSurfaceSub
      · rw [hRange]
        exact hSurfacePositive
      · rw [hRange]
        exact hSurfaceAvoid
      · intro i hi
        rw [hRange]
        by_cases hp : p.val ∈ (r i).val.image
        · let j : K := ⟨e ⟨i,hp⟩,by simpa using hi⟩
          simpa [j,e,J,hp] using hSurfaceCounts j
        · have hDis : Disjoint (F'.symm '' C) (r i).val.image := (hNon i hp).mono_left (by
            rintro x ⟨y,hy,rfl⟩
            exact hF'Source ▸ F'.map_target (hCCore hy).1)
          rw [Set.disjoint_iff_inter_eq_empty.mp hDis]
          exact ⟨Set.finite_empty,by simp [hp]⟩
    have hActualUniformInteriorContactProducer (p : Pg)
        (E : OpenPartialHomeomorph S Plane) (hESource : E.source = Eopposite.source)
        (hEAxis : ∀ x ∈ E.source, x ∈ (r w).val.image ↔ E x 1 = 0) :
        ∃ F' : OpenPartialHomeomorph S Plane, ∃ η δ H : ℝ,
          0 < η ∧ 0 < δ ∧ 0 < H ∧ p.val ∈ F'.source ∧ F' p.val = 0 ∧
          (F'.source ⊆ W p ∩ Eopposite.source) ∧
          Plane.mk (-δ) 0 ∈ F'.target ∧ Plane.mk δ 0 ∈ F'.target ∧
          (∀ x ∈ Set.Icc (-δ) δ,
            Plane.mk x 0 ∈ F'.target ∧
            F'.symm (Plane.mk x 0) ∈ Eopposite.source ∧
            Eopposite (F'.symm (Plane.mk x 0)) 1 = 0 ∧
            ∀ i, i ≠ w → (F'.symm (Plane.mk x 0) ∈ (r i).val.image ↔
              x = 0 ∧ p.val ∈ (r i).val.image)) ∧
          ((Eopposite (F'.symm (Plane.mk (-δ) 0)) 0 < Eopposite p.val 0 ∧
            Eopposite p.val 0 < Eopposite (F'.symm (Plane.mk δ 0)) 0) ∨
           (Eopposite (F'.symm (Plane.mk δ 0)) 0 < Eopposite p.val 0 ∧
            Eopposite p.val 0 < Eopposite (F'.symm (Plane.mk (-δ) 0)) 0)) ∧
          (∀ h : ℝ, 0 < h → h < H →
            (segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F'.target) ∧
            ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
              Set.range f = F'.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ∧
              f 0 = F'.symm (Plane.mk (-δ) h) ∧ f 1 = F'.symm (Plane.mk δ h) ∧
              Set.range f ⊆ W p ∧ (∀ x ∈ Set.range f, 0 < E x 1) ∧
              Disjoint (Set.range f) (r w).val.image ∧
              (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
                (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0)) ∧
          (∀ i : I, i ≠ w → p.val ∈ (r i).val.image →
            ∃ a b : Plane, 0 < a 1 ∧ b 1 < 0 ∧
              ∀ x ∈ F'.source, ‖F' x‖ < η →
                (x ∈ (r i).val.image ↔ F' x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b)) ∧
          (∀ h : ℝ, 0 < h → h < H → segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ Metric.ball (0 : Plane) η) := by
      let J := {i : I // p.val ∈ (r i).val.image}
      let e := Fintype.equivFin J
      let K := {j : Fin (Fintype.card J) // (e.symm j).val ≠ w}
      obtain ⟨F,ρ,a,b,hFW,hpF,hF0,hρ,hAxis,ha,hb,hModel,hNon⟩ := hInteriorContactModels p
      have hFEoriginal : F.source ⊆ Eopposite.source := fun x hx => (hQSub p ((hW p).2.2 (hFW hx))).2
      have hFE : F.source ⊆ E.source := fun x hx => hESource.symm ▸ hFEoriginal hx
      have h0Target : (0 : Plane) ∈ F.target := hF0 ▸ F.map_source hpF
      obtain ⟨η,hη,hBall⟩ := Metric.isOpen_iff.mp
        (show IsOpen (F.target ∩ Metric.ball (0 : Plane) ρ) from F.open_target.inter Metric.isOpen_ball)
        0 ⟨h0Target,by simpa using hρ⟩
      have hpw := (hPgFacts p.val p.property).2.2.2.1
      have hE0 : E p.val 1 = 0 := (hEAxis p.val (hFE hpF)).mp hpw
      obtain ⟨σ,hσ,hPositive⟩ := hPositiveHalfChoice (r w).val p.val E F
        hFE hpF hF0 hE0 ρ η hη hBall hEAxis hAxis
      obtain ⟨F',a',b',hF'Source,hF'0,hBall',hAxis',ha',hb',hModel',hPositive'⟩ :=
        hMirrorPositiveCore E F (r w).val p.val hF0 ρ η a b hBall hAxis ha hb
          (fun j : K => (r (e.symm j.val).val).val) hModel σ hσ hPositive
      obtain ⟨δ,H,hδ,hH,hBaseL,hBaseR,hUniform⟩ :=
        actual_uniform_radial_contact_patch a' b' ha' hb' η hη
      have hAxisBall : ∀ x ∈ Set.Icc (-δ) δ, Plane.mk x 0 ∈ Metric.ball (0 : Plane) η :=
        actual_axis_interval_in_ball δ η hδ hBaseL hBaseR
      have hAxisTarget (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) : Plane.mk x 0 ∈ F'.target :=
        (hBall' (hAxisBall x hx)).1
      have hActualAxisOriginal (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) :
          Eopposite (F'.symm (Plane.mk x 0)) 1 = 0 := by
        have ht := hAxisTarget x hx
        have hs := F'.map_target ht
        have hn : ‖F' (F'.symm (Plane.mk x 0))‖ < ρ := by
          rw [F'.right_inv ht]
          simpa using (hBall' (hAxisBall x hx)).2
        have hw : F'.symm (Plane.mk x 0) ∈ (r w).val.image :=
          (hAxis' _ hs hn).mpr (by rw [F'.right_inv ht]; rfl)
        exact (hOppositeAxisEntire _ (hFEoriginal (hF'Source ▸ hs))).mp hw
      have hActualAxisFamily (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) (i : I) (hi : i ≠ w) :
          F'.symm (Plane.mk x 0) ∈ (r i).val.image ↔ x = 0 ∧ p.val ∈ (r i).val.image := by
        have ht := hAxisTarget x hx
        have hs := F'.map_target ht
        have hn : ‖F' (F'.symm (Plane.mk x 0))‖ < ρ := by
          rw [F'.right_inv ht]
          simpa using (hBall' (hAxisBall x hx)).2
        by_cases hpi : p.val ∈ (r i).val.image
        · let j : K := ⟨e ⟨i,hpi⟩,by simpa using hi⟩
          have hm := hModel' j (F'.symm (Plane.mk x 0)) hs hn
          have hc : (r (e.symm j.val).val).val.image = (r i).val.image := by simp [j]
          rw [hc,F'.right_inv ht,actual_radial_star_axis_membership _ _
            (ne_of_gt (ha' j)) (ne_of_lt (hb' j))] at hm
          simpa [hpi] using hm
        · have hd := (hNon i hpi).mono_left (by
            intro y hy
            exact hF'Source ▸ hy : F'.source ⊆ F.source)
          have hnot : F'.symm (Plane.mk x 0) ∉ (r i).val.image :=
            fun hiCurve => Set.disjoint_left.mp hd hs hiCurve
          simp [hnot,hpi]

      have hAxisOrder := actual_contact_axis_transition_order F' Eopposite p.val δ hδ
        (hF'Source.symm ▸ hpF) hF'0 hAxisTarget
        (fun x hx => hFEoriginal (hF'Source ▸ hx)) hActualAxisOriginal
      refine ⟨F',η,δ,H,hη,hδ,hH,hF'Source.symm ▸ hpF,hF'0,?_,?_,?_,?_,hAxisOrder,?_,?_,?_⟩
      · intro x hx
        exact ⟨hFW (hF'Source ▸ hx),hFEoriginal (hF'Source ▸ hx)⟩
      · exact (hBall' hBaseL).1
      · exact (hBall' hBaseR).1
      · intro x hx
        exact ⟨hAxisTarget x hx,hFEoriginal (hF'Source ▸ F'.map_target (hAxisTarget x hx)),
          hActualAxisOriginal x hx,hActualAxisFamily x hx⟩
      · intro h hh hhH
        obtain ⟨hCBall,hEndL,hEndR,hCAxis,hCounts⟩ := hUniform h hh hhH
        let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
        have hCCore : C ⊆ F'.target ∩ Metric.ball (0 : Plane) ρ := hCBall.trans hBall'
        refine ⟨fun y hy => (hCCore hy).1,?_⟩
        obtain ⟨f,hf,hRange,hf0,hf1⟩ := hHorizontalChartArc F' δ h hδ (fun x hx => (hCCore hx).1)
        have hSurfaceSub : F'.symm '' C ⊆ W p := by
          rintro x ⟨y,hy,rfl⟩
          exact hFW (hF'Source ▸ F'.map_target (hCCore hy).1)
        have hCy (y : Plane) (hy : y ∈ C) : y 1 = h := by
          change y ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) at hy
          rw [segment_eq_image'] at hy
          obtain ⟨t,ht,he⟩ := hy
          have hy1 := congrArg (fun z : Plane => z 1) he
          change h+t*(h-h) = y 1 at hy1
          simpa using hy1.symm
        have hSurfacePositive : ∀ x ∈ F'.symm '' C, 0 < E x 1 := by
          rintro x ⟨y,hy,rfl⟩
          exact hPositive' y (hCBall hy) (by rw [hCy y hy]; exact hh)
        have hSurfaceAvoid : Disjoint (F'.symm '' C) (r w).val.image := by
          apply Set.disjoint_left.mpr
          rintro x ⟨y,hy,rfl⟩ hxw
          have hxF := F'.map_target (hCCore hy).1
          have hxN : ‖F' (F'.symm y)‖ < ρ := by
            rw [F'.right_inv (hCCore hy).1]
            simpa using (hCCore hy).2
          have hzero := (hAxis' _ hxF hxN).mp hxw
          rw [F'.right_inv (hCCore hy).1,hCy y hy] at hzero
          linarith
        have hSurfaceCounts := hTransportCounts F' ρ C hCCore
          (fun j : K => (r (e.symm j.val).val).val) a' b' hModel' hCounts
        refine ⟨f,hf,hRange,hf0,hf1,?_,?_,?_,?_⟩
        · rw [hRange]
          exact hSurfaceSub
        · rw [hRange]
          exact hSurfacePositive
        · rw [hRange]
          exact hSurfaceAvoid
        · intro i hi
          rw [hRange]
          by_cases hp : p.val ∈ (r i).val.image
          · let j : K := ⟨e ⟨i,hp⟩,by simpa using hi⟩
            simpa [j,e,J,hp] using hSurfaceCounts j
          · have hDis : Disjoint (F'.symm '' C) (r i).val.image := (hNon i hp).mono_left (by
              rintro x ⟨y,hy,rfl⟩
              exact hF'Source ▸ F'.map_target (hCCore hy).1)
            rw [Set.disjoint_iff_inter_eq_empty.mp hDis]
            exact ⟨Set.finite_empty,by simp [hp]⟩

      · intro i hi hpi
        let j : K := ⟨e ⟨i,hpi⟩,by simpa using hi⟩
        refine ⟨a' j,b' j,ha' j,hb' j,?_⟩
        intro x hx hxn
        have hbX : F' x ∈ Metric.ball (0 : Plane) η := by
          simpa only [Metric.mem_ball,dist_zero_right] using hxn
        have hxnρ : ‖F' x‖ < ρ := by
          simpa only [Metric.mem_ball,dist_zero_right] using (hBall' hbX).2
        simpa [j,e,J] using hModel' j x hx hxnρ
      · intro h hh hhH
        exact (hUniform h hh hhH).1
    -- Actual source application: all constructed contact/corner supports
    -- lie inside the enlarged disk, which was PRODUCED avoiding the actual K.
    have hActualCornerSupportAvoidK :
        Disjoint (Set.range cornerArcU ∪ Set.range cornerArcZ) K := by
      apply Set.disjoint_left.mpr
      intro x hx hk
      have hxLarge : x ∈ Set.range dlarge := by
        rcases hx with hx | hx
        · have hxS : x ∈ surfaceConnectorU := by
            rw [hCornerRangeU] at hx
            exact hx
          exact interior_subset ((hUcornerV (hSurfaceConnectorUSub hxS)).2)
        · have hxS : x ∈ surfaceConnectorZ := by
            rw [hCornerRangeZ] at hx
            exact hx
          exact interior_subset ((hZcornerV (hSurfaceConnectorZSub hxS)).2)
      exact (hDiskInWK hxLarge).2 hk
    have hActualInteriorSupportAvoidK (p : Pg) : Disjoint (W p) K := by
      apply Set.disjoint_left.mpr
      intro x hx hk
      have hxE : x ∈ Eopposite.source := (hQSub p ((hW p).2.2 hx)).2
      have hxLarge : x ∈ Set.range dlarge :=
        interior_subset (hOppositeSource hxE).1
      exact (hDiskInWK hxLarge).2 hk
    have hActualInteriorArcAvoidK (p : Pg) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          (∀ x ∈ Set.range f, 0 < Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤
              if p.val ∈ (r i).val.image then 1 else 0) := by
      obtain ⟨f,hf,hsub,hpos,havoid,hcounts⟩ := hInteriorParallelArcs p
      exact ⟨f,hf,hsub,(hActualInteriorSupportAvoidK p).mono_left hsub,
        hpos,havoid,hcounts⟩
    let contactX : Pg → ℝ := fun p => Eopposite p.val 0
    have hContactXInjective : Function.Injective contactX := by
      intro p q he
      have hp := hPgFacts p.val p.property
      have hq := hPgFacts q.val q.property
      have hpE : p.val ∈ Eopposite.source := hGInOpposite (hGAngleImage ▸ hp.1)
      have hqE : q.val ∈ Eopposite.source := hGInOpposite (hGAngleImage ▸ hq.1)
      have hp0 : Eopposite p.val 1 = 0 := (hOppositeAxisEntire p.val hpE).mp hp.2.2.2.1
      have hq0 : Eopposite q.val 1 = 0 := (hOppositeAxisEntire q.val hqE).mp hq.2.2.2.1
      apply Subtype.ext
      apply Eopposite.injOn hpE hqE
      ext i
      fin_cases i
      · exact he
      · exact hp0.trans hq0.symm
    let contactCoordinates : Finset ℝ := Finset.univ.image contactX
    have hActualContactCoordinates :
        ∀ x : ℝ, x ∈ contactCoordinates ↔ ∃ p : Pg, contactX p = x := by
      intro x
      simp only [contactCoordinates,Finset.mem_image,Finset.mem_univ,true_and]
    have hActualContactOrder : StrictMono (contactCoordinates.orderEmbOfFin rfl) :=
      (contactCoordinates.orderEmbOfFin rfl).strictMono
    have hActualAxisPointOnSide (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
        ∃ y : S, y ∈ Eopposite.source ∧ y ∈ Set.range g ∧
          Eopposite y = Plane.mk x 0 := by
      have hxSq : Plane.mk x 0 ∈ Plane.closedSquare 0 1 := by
        apply mem_closedSquare_zero_one.mpr
        change max |x| |(0 : ℝ)| ≤ 1
        exact max_le (abs_le.mpr hx) (by norm_num)
      have hxT : Plane.mk x 0 ∈ Eopposite.target := hOppositeSquare hxSq
      let y := Eopposite.symm (Plane.mk x 0)
      have hyE : y ∈ Eopposite.source := Eopposite.map_target hxT
      have hEy : Eopposite y = Plane.mk x 0 := Eopposite.right_inv hxT
      have hyW : y ∈ (r w).val.image := (hOppositeAxisEntire y hyE).mpr (by
        rw [hEy]; rfl)
      have hyG : y ∈ Set.range g := hOppositePatchActual ▸
        ⟨⟨hyE,hEy ▸ hxSq⟩,hyW⟩
      exact ⟨y,hyE,hyG,hEy⟩
    let γg : ℝ → S := fun θ => cw.map (Circle.exp θ)
    have hγg : Continuous γg := cw.embedded.continuous.comp Circle.exp.continuous
    have hγgInj : Set.InjOn γg (Set.Icc ag zg) := by
      intro θ hθ ψ hψ he
      exact Circle.exp_injOn_Icc hglen hθ hψ (cw.embedded.injective he)
    obtain ⟨gAngularArc,hGAngularArc,hGAngularRange,hGAngularZero,hGAngularOne⟩ :=
      hIntervalArc γg hγg ag zg hagzg hγgInj
    have hGEndpointOrientation :
        (u = γg ag ∧ z = γg zg) ∨ (u = γg zg ∧ z = γg ag) := by
      have hh := hSameArcEndpoints g gAngularArc hg hGAngularArc
        (hGAngleImage.trans hGAngularRange.symm)
      simpa [hg0,hg1,hGAngularZero,hGAngularOne] using hh
    have hActualContactCoordinateBounds (p : Pg) :
        -1 < contactX p ∧ contactX p < 1 := by
      have hp := hPgFacts p.val p.property
      have hpPatch : p.val ∈
          {x : S | x ∈ Eopposite.source ∧ Eopposite x ∈ Plane.closedSquare 0 1} ∩
          (r w).val.image := hOppositePatchActual.symm ▸ hp.1
      have hp0 : Eopposite p.val 1 = 0 :=
        (hOppositeAxisEntire p.val hpPatch.1.1).mp hpPatch.2
      have hcoord : Eopposite p.val = Plane.mk (contactX p) 0 := by
        ext i
        fin_cases i
        · rfl
        · exact hp0
      have hbound : |contactX p| ≤ 1 := by
        have hh := mem_closedSquare_zero_one.mp hpPatch.1.2
        rw [hcoord] at hh
        change max |contactX p| |(0 : ℝ)| ≤ 1 at hh
        exact le_trans (le_max_left _ _) hh
      have hNotEndpoint (θ : ℝ) (hθ : θ = ag ∨ θ = zg) : p.val ≠ γg θ := by
        intro he
        rcases hθ with rfl | rfl <;> rcases hGEndpointOrientation with hOr | hOr
        · exact hp.2.1 (he.trans hOr.1.symm)
        · exact hp.2.2.1 (he.trans hOr.2.symm)
        · exact hp.2.2.1 (he.trans hOr.2.symm)
        · exact hp.2.1 (he.trans hOr.1.symm)
      have hEndAg : γg ag ∈ Eopposite.source := hGInOpposite
        ⟨ag,⟨le_rfl,hagzg.le⟩,rfl⟩
      have hEndZg : γg zg ∈ Eopposite.source := hGInOpposite
        ⟨zg,⟨hagzg.le,le_rfl⟩,rfl⟩
      have hnLeft : contactX p ≠ -1 := by
        intro he
        apply hNotEndpoint ag (Or.inl rfl)
        apply Eopposite.injOn hpPatch.1.1 hEndAg
        rw [hcoord,he]
        exact hOppositeLeft.symm
      have hnRight : contactX p ≠ 1 := by
        intro he
        apply hNotEndpoint zg (Or.inr rfl)
        apply Eopposite.injOn hpPatch.1.1 hEndZg
        rw [hcoord,he]
        exact hOppositeRight.symm
      exact ⟨lt_of_le_of_ne (abs_le.mp hbound).1 (Ne.symm hnLeft),
        lt_of_le_of_ne (abs_le.mp hbound).2 hnRight⟩
    have hActualContactFreeAxis (x : ℝ) (hx : -1 < x ∧ x < 1)
        (hxc : x ∉ contactCoordinates) :
        ∃ y : S, y ∈ Eopposite.source ∧ y ∈ Set.range g ∧
          Eopposite y = Plane.mk x 0 ∧
          ∀ i : I, i ≠ w → y ∉ (r i).val.image := by
      obtain ⟨y,hyE,hyG,hEy⟩ := hActualAxisPointOnSide x ⟨hx.1.le,hx.2.le⟩
      have hyU : y ≠ u := by
        intro he
        rcases hGEndpointOrientation with hOr | hOr
        · have hleft : Eopposite y = Plane.mk (-1) 0 := by rw [he,hOr.1]; exact hOppositeLeft
          have hh := congrArg (fun q : Plane => q 0) (hEy.symm.trans hleft)
          change x = -1 at hh
          linarith [hx.1]
        · have hright : Eopposite y = Plane.mk 1 0 := by rw [he,hOr.1]; exact hOppositeRight
          have hh := congrArg (fun q : Plane => q 0) (hEy.symm.trans hright)
          change x = 1 at hh
          linarith [hx.2]
      have hyZ : y ≠ z := by
        intro he
        rcases hGEndpointOrientation with hOr | hOr
        · have hright : Eopposite y = Plane.mk 1 0 := by rw [he,hOr.2]; exact hOppositeRight
          have hh := congrArg (fun q : Plane => q 0) (hEy.symm.trans hright)
          change x = 1 at hh
          linarith [hx.2]
        · have hleft : Eopposite y = Plane.mk (-1) 0 := by rw [he,hOr.2]; exact hOppositeLeft
          have hh := congrArg (fun q : Plane => q 0) (hEy.symm.trans hleft)
          change x = -1 at hh
          linarith [hx.1]
      refine ⟨y,hyE,hyG,hEy,?_⟩
      intro i hi hyi
      have hyPg : y ∈ Pg := Set.mem_iUnion.mpr ⟨i,by
        simp only [Pg,ite_eq_right hi,Set.mem_inter_iff,Set.mem_diff,
          Set.mem_insert_iff,Set.mem_singleton_iff]
        exact ⟨⟨hyG,not_or.mpr ⟨hyU,hyZ⟩⟩,hyi⟩⟩
      apply hxc
      apply (hActualContactCoordinates x).mpr
      refine ⟨⟨y,hyPg⟩,?_⟩
      change Eopposite y 0 = x
      rw [hEy]
      rfl
    have hSelectedCornerConnectorMeet
        (c : Curve S) (F : OpenPartialHomeomorph S Plane) (δ h ρ : ℝ)
        (hh : 0 < h) (arc : C(Interval,S))
        (hrange : Set.range arc = F.symm ''
          segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h))
        (hstart : arc 0 = F.symm (Plane.mk (-δ) 0))
        (hstartc : arc 0 ∈ c.image)
        (hcore : segment ℝ (Plane.mk (-δ) 0) (Plane.mk (-δ) h) ⊆
          F.target ∩ Metric.ball (0 : Plane) ρ)
        (haxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.image ↔ F x 1 = 0)) :
        Set.range arc ∩ c.image = {arc 0} := by
      ext x
      constructor
      · rintro ⟨hx,hxc⟩
        rw [hrange] at hx
        obtain ⟨q,hq,rfl⟩ := hx
        have hqs := F.map_target (hcore hq).1
        have hqn : ‖F (F.symm q)‖ < ρ := by
          rw [F.right_inv (hcore hq).1]
          simpa only [Metric.mem_ball,dist_zero_right] using (hcore hq).2
        have hq0 := (haxis (F.symm q) hqs hqn).mp hxc
        rw [F.right_inv (hcore hq).1] at hq0
        rw [segment_eq_image'] at hq
        obtain ⟨t,ht,he⟩ := hq
        have hy := congrArg (fun z : Plane => z 1) he
        change 0+t*(h-0) = q 1 at hy
        have ht0 : t = 0 := by nlinarith
        have heq : q = Plane.mk (-δ) 0 := by
          rw [ht0] at he
          simpa using he.symm
        rw [heq,← hstart]
        exact Set.mem_singleton _
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨⟨0,rfl⟩,hstartc⟩
    have hActualCornerSelectedMeetU :
        Set.range cornerArcU ∩ (r v).val.image = {cornerArcU 0} := by
      apply hSelectedCornerConnectorMeet (r v).val FU δU heightU ρU hHeightU
        cornerArcU hCornerRangeU hCornerStartU hCornerStartCurveU hConnectorCoreU
      simpa [eU] using hFUAxis
    have hActualCornerSelectedMeetZ :
        Set.range cornerArcZ ∩ (r v).val.image = {cornerArcZ 0} := by
      apply hSelectedCornerConnectorMeet (r v).val FZ δZ heightZ ρZ hHeightZ
        cornerArcZ hCornerRangeZ hCornerStartZ hCornerStartCurveZ hConnectorCoreZ
      simpa [eZ] using hFZAxis
    have hActualCornerAvoidOldSideU : Disjoint (Set.range cornerArcU) (Set.range f) := by
      apply Set.disjoint_left.mpr
      intro x hx hxf
      have he : x = cornerArcU 0 := Set.mem_singleton_iff.mp
        (hActualCornerSelectedMeetU ▸ ⟨hx,hfcurve hxf⟩)
      exact hCornerStartExteriorU (he ▸ hxf)
    have hActualCornerAvoidOldSideZ : Disjoint (Set.range cornerArcZ) (Set.range f) := by
      apply Set.disjoint_left.mpr
      intro x hx hxf
      have he : x = cornerArcZ 0 := Set.mem_singleton_iff.mp
        (hActualCornerSelectedMeetZ ▸ ⟨hx,hfcurve hxf⟩)
      exact hCornerStartExteriorZ (he ▸ hxf)
    have hActualCornerIncidenceBoundU (i : I) (hi : i ≠ v) :
        (Set.range cornerArcU ∩ (r i).val.image).ncard ≤
          if u ∈ (r i).val.image then 1 else 0 := by
      by_cases hui : u ∈ (r i).val.image
      · rw [ite_eq_left hui]
        exact (hCornerArcWholeCountsU i hi).2
      · rw [ite_eq_right hui]
        have hdis : Disjoint (Set.range cornerArcU) (r i).val.image :=
          (hUNonincident i hui).mono_left (by
          intro x hx
          rw [hCornerRangeU] at hx
          exact hSurfaceConnectorUSub hx)
        rw [Set.disjoint_iff_inter_eq_empty.mp hdis]
        simp
    have hActualCornerIncidenceBoundZ (i : I) (hi : i ≠ v) :
        (Set.range cornerArcZ ∩ (r i).val.image).ncard ≤
          if z ∈ (r i).val.image then 1 else 0 := by
      by_cases hzi : z ∈ (r i).val.image
      · rw [ite_eq_left hzi]
        exact (hCornerArcWholeCountsZ i hi).2
      · rw [ite_eq_right hzi]
        have hdis : Disjoint (Set.range cornerArcZ) (r i).val.image :=
          (hZNonincident i hzi).mono_left (by
          intro x hx
          rw [hCornerRangeZ] at hx
          exact hSurfaceConnectorZSub hx)
        rw [Set.disjoint_iff_inter_eq_empty.mp hdis]
        simp
    have hActualOriginalDiskFrontier :
        frontier (Set.range d) = Set.range f ∪ Set.range g := by
      have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
      rw [hclosed.frontier_eq,embedded_surface_disk_interior_eq d hd,← hboundary]
      ext p
      constructor
      · rintro ⟨⟨x,rfl⟩,hxnot⟩
        refine ⟨x,?_,rfl⟩
        have hxle : dist x.val (0 : Plane) ≤ 1 := x.property
        have hxge : 1 ≤ dist x.val (0 : Plane) := by
          by_contra hn
          apply hxnot
          exact ⟨x,lt_of_not_ge hn,rfl⟩
        exact le_antisymm hxle hxge
      · rintro ⟨x,hx,rfl⟩
        refine ⟨⟨x,rfl⟩,?_⟩
        rintro ⟨y,hy,he⟩
        have hxy := hd.injective he
        subst y
        change dist x.val (0 : Plane) < 1 at hy
        change dist x.val (0 : Plane) = 1 at hx
        linarith
    have hActualCornerOutsideDisk
        (arc : C(Interval,S))
        (hAvoidF : Disjoint (Set.range arc) (Set.range f))
        (hAvoidG : Disjoint (Set.range arc) (r w).val.image)
        (hstart : arc 0 ∉ Set.range d) : Set.range arc ⊆ (Set.range d)ᶜ := by
      have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
      have hconn : IsPreconnected (Set.range arc) := isPreconnected_range arc.continuous
      have hcover : Set.range arc ⊆ interior (Set.range d) ∪ (Set.range d)ᶜ := by
        intro x hx
        by_cases hxd : x ∈ Set.range d
        · left
          by_contra hxi
          have hxf : x ∈ frontier (Set.range d) :=
            hclosed.frontier_eq ▸ ⟨hxd,hxi⟩
          rw [hActualOriginalDiskFrontier] at hxf
          rcases hxf with hxf | hxg
          · exact Set.disjoint_left.mp hAvoidF hx hxf
          · exact Set.disjoint_left.mp hAvoidG hx (hgcurve hxg)
        · exact Or.inr hxd
      have hdis : Disjoint (interior (Set.range d)) (Set.range d)ᶜ :=
        Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))
      rcases hconn.subset_or_subset isOpen_interior hclosed.isOpen_compl hdis hcover with hi | ho
      · exact False.elim (hstart (interior_subset (hi ⟨0,rfl⟩)))
      · exact ho
    have hActualCornerArcOutsideDiskU : Set.range cornerArcU ⊆ (Set.range d)ᶜ :=
      hActualCornerOutsideDisk cornerArcU hActualCornerAvoidOldSideU
        hCornerArcOppositeAvoidU hCornerStartOutsideDiskU
    have hActualCornerArcOutsideDiskZ : Set.range cornerArcZ ⊆ (Set.range d)ᶜ :=
      hActualCornerOutsideDisk cornerArcZ hActualCornerAvoidOldSideZ
        hCornerArcOppositeAvoidZ hCornerStartOutsideDiskZ
    have hActualGapConnector (L R : ℝ) (hL : -1 < L) (hLR : L < R) (hR : R < 1)
        (hgap : Disjoint (Set.Icc L R) (contactCoordinates : Set ℝ)) :
        ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h < ε →
          ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧
            (∀ t, arc t ∈ Eopposite.source ∧
              Eopposite (arc t) = Plane.mk (L+t.val*(R-L)) h) ∧
            Disjoint (Set.range arc) K ∧
            (∀ i : I, Disjoint (Set.range arc) (r i).val.image) := by
      let xy : Plane ≃ₜ ℝ × ℝ := {
        toFun := fun z => (z 0,z 1)
        invFun := fun z => Plane.mk z.1 z.2
        left_inv := by intro z; ext i; fin_cases i <;> rfl
        right_inv := by intro z; rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let e := Eopposite.toHomeomorphSourceTarget.trans (xy.image Eopposite.target)
      have hVprod : IsOpen (xy '' Eopposite.target) := xy.isOpenMap _ Eopposite.open_target
      let J := {i : I // i ≠ w}
      let c : J → Curve S := fun i => (r i.val).val
      have haxisprod : ∀ x ∈ Set.Icc L R, ∃ y : xy '' Eopposite.target,
          y.val = (x,0) ∧ ∀ j : J, (e.symm y : S) ∉ (c j).image := by
        intro x hx
        have hxc : x ∉ contactCoordinates := fun hc => Set.disjoint_left.mp hgap hx hc
        obtain ⟨y,hyE,hyG,hEy,havoid⟩ := hActualContactFreeAxis x
          ⟨by linarith [hx.1],by linarith [hx.2]⟩ hxc
        let yU : Eopposite.source := ⟨y,hyE⟩
        refine ⟨e yU,?_,?_⟩
        · change (Eopposite y 0,Eopposite y 1) = (x,0)
          rw [hEy]
          rfl
        · intro j
          simpa only [Homeomorph.symm_apply_apply] using havoid j.val j.property
      have hgaxisprod : ∀ x : Eopposite.source,
          (x : S) ∈ (r w).val.image ↔ (e x : ℝ × ℝ).2 = 0 := by
        intro x
        exact hOppositeAxisEntire x.val x.property
      obtain ⟨ε,hε,hpaths⟩ := CurveComplex.actual_contact_free_gap_connector
        c (r w).val Eopposite.source (xy '' Eopposite.target) hVprod e L R hLR
        haxisprod hgaxisprod
      refine ⟨ε,hε,?_⟩
      intro h hh hhε
      obtain ⟨arc,hArc,hcoords,havoidW,havoidJ⟩ := hpaths h hh hhε
      have hcoordsActual : ∀ t : Interval, arc t ∈ Eopposite.source ∧
          Eopposite (arc t) = Plane.mk (L+t.val*(R-L)) h := by
        intro t
        obtain ⟨u,hu,hcoord⟩ := hcoords t
        refine ⟨hu ▸ u.property,?_⟩
        rw [← hu]
        ext i
        fin_cases i
        · exact congrArg Prod.fst hcoord
        · exact congrArg Prod.snd hcoord
      refine ⟨arc,hArc,hcoordsActual,?_,?_⟩
      · apply Set.disjoint_left.mpr
        rintro x ⟨t,rfl⟩ hk
        have hxLarge : arc t ∈ Set.range dlarge :=
          interior_subset (hOppositeSource (hcoordsActual t).1).1
        exact (hDiskInWK hxLarge).2 hk
      · intro i
        by_cases hi : i = w
        · subst i
          exact havoidW
        · exact havoidJ ⟨i,hi⟩
    -- Identify the REAL opposite-side arm entering the bigon boundary.
    -- This is an endpoint/parameter classification, not event alternation.
    have hActualAngularInteriorArm (c : Curve S) (b : Circle)
        (a z : ℝ) (haz : a < z) (hlen : z-a < 2*Real.pi)
        (p : S) (q : Circle) (hq : c.map q = p)
        (hp : p = c.map (b*Circle.exp a) ∨ p = c.map (b*Circle.exp z))
        (h : ℝ) (hh : 0 < h) (hhz : h < z-a) :
        c.map (q*Circle.exp (if decide (p = c.map (b*Circle.exp a)) then h else -h)) ∈
          (fun t => c.map (b*Circle.exp t)) '' Set.Ioo a z := by
      by_cases hpa : p = c.map (b*Circle.exp a)
      · have hqeq : q = b*Circle.exp a := c.embedded.injective (hq.trans hpa)
        refine ⟨a+h,⟨by linarith,by linarith⟩,?_⟩
        change c.map (b*Circle.exp (a+h)) =
          c.map (q*Circle.exp (if decide (p = c.map (b*Circle.exp a)) then h else -h))
        rw [if_pos (by simpa using hpa),hqeq,Circle.exp_add]
        simp only [mul_assoc]
      · have hpz : p = c.map (b*Circle.exp z) := hp.resolve_left hpa
        have hqeq : q = b*Circle.exp z := c.embedded.injective (hq.trans hpz)
        refine ⟨z-h,⟨by linarith,by linarith⟩,?_⟩
        change c.map (b*Circle.exp (z-h)) =
          c.map (q*Circle.exp (if decide (p = c.map (b*Circle.exp a)) then h else -h))
        rw [if_neg (by simpa using hpa),hqeq,sub_eq_add_neg,Circle.exp_add]
        simp only [mul_assoc]
    let wgU := eU ⟨w,huOpposite⟩
    let wgZ := eZ ⟨w,hzOpposite⟩
    let βgU : Bool := decide (u = γg ag)
    let βgZ : Bool := decide (z = γg ag)
    have hActualOppositeSideArmU (t : Interval) (ht : 0 < t.val)
        (hshort : εU*t.val < zg-ag) :
        (r w).val.map (qU wgU * Circle.exp (if βgU then εU*t.val else -(εU*t.val))) ∈
          Set.range g \ {u,z} := by
      have hp : u = (r w).val.map (bg*Circle.exp ag) ∨
          u = (r w).val.map (bg*Circle.exp zg) := by
        rcases hGEndpointOrientation with hOr | hOr
        · exact Or.inl hOr.1
        · exact Or.inr hOr.1
      have hm := hActualAngularInteriorArm (r w).val bg ag zg hagzg hglen
        u (qU wgU) (by simpa [wgU,eU,JU] using hqU wgU) hp
        (εU*t.val) (mul_pos hεU ht) hshort
      obtain ⟨θ,hθ,heθ⟩ := hm
      have hwhole : (r w).val.map (qU wgU * Circle.exp
          (if βgU then εU*t.val else -(εU*t.val))) ∈ Set.range g :=
        hGAngleImage.symm ▸ ⟨θ,⟨hθ.1.le,hθ.2.le⟩,heθ⟩
      refine ⟨hwhole,?_⟩
      intro hcorner
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hcorner
      have hθEnds : θ ≠ ag ∧ θ ≠ zg := ⟨ne_of_gt hθ.1,ne_of_lt hθ.2⟩
      have hno (ψ : ℝ) (hψ : ψ = ag ∨ ψ = zg)
          (he : (r w).val.map (qU wgU * Circle.exp
            (if βgU then εU*t.val else -(εU*t.val))) = γg ψ) : False := by
        have hh : γg θ = γg ψ := heθ.trans he
        have hψRange : ψ ∈ Set.Icc ag zg := by
          rcases hψ with rfl | rfl
          · exact ⟨le_rfl,hagzg.le⟩
          · exact ⟨hagzg.le,le_rfl⟩
        have hsame := hγgInj ⟨hθ.1.le,hθ.2.le⟩ hψRange hh
        rcases hψ with rfl | rfl
        · exact hθEnds.1 hsame
        · exact hθEnds.2 hsame
      rcases hcorner with he | he <;> rcases hGEndpointOrientation with hOr | hOr
      · exact hno ag (Or.inl rfl) (he.trans hOr.1)
      · exact hno zg (Or.inr rfl) (he.trans hOr.1)
      · exact hno zg (Or.inr rfl) (he.trans hOr.2)
      · exact hno ag (Or.inl rfl) (he.trans hOr.2)
    have hActualOppositeSideArmZ (t : Interval) (ht : 0 < t.val)
        (hshort : εZ*t.val < zg-ag) :
        (r w).val.map (qZ wgZ * Circle.exp (if βgZ then εZ*t.val else -(εZ*t.val))) ∈
          Set.range g \ {u,z} := by
      have hp : z = (r w).val.map (bg*Circle.exp ag) ∨
          z = (r w).val.map (bg*Circle.exp zg) := by
        rcases hGEndpointOrientation with hOr | hOr
        · exact Or.inr hOr.2
        · exact Or.inl hOr.2
      have hm := hActualAngularInteriorArm (r w).val bg ag zg hagzg hglen
        z (qZ wgZ) (by simpa [wgZ,eZ,JZ] using hqZ wgZ) hp
        (εZ*t.val) (mul_pos hεZ ht) hshort
      obtain ⟨θ,hθ,heθ⟩ := hm
      have hwhole : (r w).val.map (qZ wgZ * Circle.exp
          (if βgZ then εZ*t.val else -(εZ*t.val))) ∈ Set.range g :=
        hGAngleImage.symm ▸ ⟨θ,⟨hθ.1.le,hθ.2.le⟩,heθ⟩
      refine ⟨hwhole,?_⟩
      intro hcorner
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hcorner
      have hno (ψ : ℝ) (hψ : ψ = ag ∨ ψ = zg)
          (he : (r w).val.map (qZ wgZ * Circle.exp
            (if βgZ then εZ*t.val else -(εZ*t.val))) = γg ψ) : False := by
        have hh : γg θ = γg ψ := heθ.trans he
        have hψRange : ψ ∈ Set.Icc ag zg := by
          rcases hψ with rfl | rfl
          · exact ⟨le_rfl,hagzg.le⟩
          · exact ⟨hagzg.le,le_rfl⟩
        have hsame := hγgInj ⟨hθ.1.le,hθ.2.le⟩ hψRange hh
        rcases hψ with rfl | rfl
        · exact (ne_of_gt hθ.1) hsame
        · exact (ne_of_lt hθ.2) hsame
      rcases hcorner with he | he <;> rcases hGEndpointOrientation with hOr | hOr
      · exact hno ag (Or.inl rfl) (he.trans hOr.1)
      · exact hno zg (Or.inr rfl) (he.trans hOr.1)
      · exact hno zg (Or.inr rfl) (he.trans hOr.2)
      · exact hno ag (Or.inl rfl) (he.trans hOr.2)
    have hActualEnteringArmCorePoint {J : Type} [Fintype J]
        (c : Curve S) (p : S) (q : Circle) (hq : c.map q = p)
        (ε η len : ℝ) (hε : 0 < ε) (hη : 0 < η) (hlen : 0 < len)
        (E F : OpenPartialHomeomorph S Plane) (hFSource : F.source = E.source)
        (hFp : F p = 0) (T : Plane ≃L[ℝ] Plane)
        (γ : (J × Bool) → Interval → Plane) (O : Set Plane)
        (R : RadializedStar γ 0 O) (j : J) (β : Bool)
        (hPhase : ∀ t, γ (j,β) t = E (c.map (q*Circle.exp
          (if β then ε*t.val else -(ε*t.val)))))
        (hSource : ∀ t : Interval, c.map (q*Circle.exp
          (if β then ε*t.val else -(ε*t.val))) ∈ E.source)
        (hFormula : ∀ x, F x = T (R.H (E x)))
        (hVector : T (R.vector (j,β)) 1 ≠ 0)
        (G : Set S) (hInside : ∀ t : Interval, 0 < t.val → ε*t.val < len →
          c.map (q*Circle.exp (if β then ε*t.val else -(ε*t.val))) ∈ G ∧
          c.map (q*Circle.exp (if β then ε*t.val else -(ε*t.val))) ≠ p) :
        ∃ t : Interval, 0 < t.val ∧ t.val < (R.cut (j,β)).val ∧ ε*t.val < len ∧
          let x := c.map (q*Circle.exp (if β then ε*t.val else -(ε*t.val)))
          x ∈ G ∧ F x ∈ Metric.ball (0 : Plane) η ∧
            F x ∈ segment ℝ (0 : Plane) (T (R.vector (j,β))) ∧ F x 1 ≠ 0 := by
      let phase : Interval → S := fun t =>
        c.map (q*Circle.exp (if β then ε*t.val else -(ε*t.val)))
      have hphase : Continuous phase := by
        cases β <;> dsimp [phase] <;> exact c.embedded.continuous.comp (by fun_prop)
      have hFphase : Continuous (fun t : Interval => F (phase t)) :=
        F.continuousOn.comp_continuous hphase (fun t => hFSource.symm ▸ hSource t)
      have hPhase0 : phase 0 = p := by simp [phase,hq]
      have hOpen : IsOpen {t : Interval | F (phase t) ∈ Metric.ball (0 : Plane) η} :=
        Metric.isOpen_ball.preimage hFphase
      have hZero : (0 : Interval) ∈ {t : Interval | F (phase t) ∈ Metric.ball (0 : Plane) η} := by
        rw [Set.mem_setOf_eq,hPhase0,hFp]
        simpa using hη
      obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hOpen 0 hZero
      let s := min r (min (R.cut (j,β)).val (min 1 (len/(2*ε))))/2
      have hs : 0 < s := half_pos (lt_min hr (lt_min (R.cut_pos _) (lt_min zero_lt_one
        (div_pos hlen (by positivity)))))
      have hsr : s < r := by
        dsimp [s]
        linarith [min_le_left r (min (R.cut (j,β)).val (min 1 (len/(2*ε))))]
      have hscut : s < (R.cut (j,β)).val := by
        have hb := (min_le_right r (min (R.cut (j,β)).val (min 1 (len/(2*ε))))).trans
          (min_le_left (R.cut (j,β)).val (min 1 (len/(2*ε))))
        dsimp [s]
        linarith [R.cut_pos (j,β)]
      have hs1 : s ≤ 1 := by
        have hb := ((min_le_right r (min (R.cut (j,β)).val (min 1 (len/(2*ε))))).trans
          (min_le_right (R.cut (j,β)).val (min 1 (len/(2*ε))))).trans
          (min_le_left 1 (len/(2*ε)))
        dsimp [s]
        linarith
      have hshort : ε*s < len := by
        have hb := ((min_le_right r (min (R.cut (j,β)).val (min 1 (len/(2*ε))))).trans
          (min_le_right (R.cut (j,β)).val (min 1 (len/(2*ε))))).trans
          (min_le_right 1 (len/(2*ε)))
        have hh := (le_div_iff₀ (by positivity : 0 < 2*ε)).mp hb
        dsimp [s]
        nlinarith
      let t : Interval := ⟨s,⟨hs.le,hs1⟩⟩
      have hin := hInside t hs hshort
      have hFball : F (phase t) ∈ Metric.ball (0 : Plane) η := hball (by
        change dist t (0 : Interval) < r
        simpa [t,Subtype.dist_eq,Real.dist_eq,abs_of_pos hs] using hsr)
      have hRaw : R.H (E (phase t)) ∈ segment ℝ (0 : Plane) (R.vector (j,β)) := by
        have hpref : R.H (E (phase t)) ∈ R.H '' armPrefix γ (j,β) (R.cut (j,β)) := by
          refine ⟨γ (j,β) t,?_,?_⟩
          · exact ⟨t,hscut.le,rfl⟩
          · rw [hPhase]
        simpa only [R.prefix_image,zero_add] using hpref
      have hSeg : F (phase t) ∈ segment ℝ (0 : Plane) (T (R.vector (j,β))) := by
        rw [hFormula]
        have hi := image_segment ℝ T.toLinearMap.toAffineMap (0 : Plane) (R.vector (j,β))
        change T '' segment ℝ (0 : Plane) (R.vector (j,β)) =
          segment ℝ (T 0) (T (R.vector (j,β))) at hi
        rw [map_zero] at hi
        exact hi ▸ ⟨R.H (E (phase t)),hRaw,rfl⟩
      have hFne : F (phase t) ≠ 0 := by
        intro he
        have hpF : p ∈ F.source := by
          have hm : phase 0 ∈ F.source := hFSource.symm ▸ hSource 0
          rwa [hPhase0] at hm
        have hpeq : phase t = p := F.injOn (hFSource.symm ▸ hSource t) hpF
          (he.trans hFp.symm)
        exact hin.2 hpeq
      have hyne : F (phase t) 1 ≠ 0 := by
        intro hy
        rw [segment_eq_image'] at hSeg
        obtain ⟨a,ha,hea⟩ := hSeg
        have heay := congrArg (fun z : Plane => z 1) hea
        change 0+a*(T (R.vector (j,β)) 1-0) = F (phase t) 1 at heay
        have ha0 : a = 0 := (mul_eq_zero.mp (by simpa [hy] using heay)).resolve_right hVector
        apply hFne
        rw [ha0] at hea
        simpa using hea.symm
      exact ⟨t,hs,hscut,hshort,hin.1,hFball,hSeg,hyne⟩
    have hEnteringVectorUNe : TU (RU.vector (wgU,βgU)) 1 ≠ 0 := by
      have hprod : TU (RU.vector (wgU,false)) 1 * TU (RU.vector (wgU,true)) 1 ≠ 0 :=
        ne_of_lt (hUArmSigns wgU (by simpa [wgU,eU,JU] using hvw.symm))
      cases βgU
      · exact (mul_ne_zero_iff.mp hprod).1
      · exact (mul_ne_zero_iff.mp hprod).2
    have hEnteringVectorZNe : TZ (RZ.vector (wgZ,βgZ)) 1 ≠ 0 := by
      have hprod : TZ (RZ.vector (wgZ,false)) 1 * TZ (RZ.vector (wgZ,true)) 1 ≠ 0 :=
        ne_of_lt (hZArmSigns wgZ (by simpa [wgZ,eZ,JZ] using hvw.symm))
      cases βgZ
      · exact (mul_ne_zero_iff.mp hprod).1
      · exact (mul_ne_zero_iff.mp hprod).2
    obtain ⟨sideTU,hSideTU,hSideTUCut,hSideTUShort,hSideUInG,hSideUCore,hSideURay,hSideUYNe⟩ :=
      hActualEnteringArmCorePoint (r w).val u (qU wgU)
        (by simpa [wgU,eU,JU] using hqU wgU) εU ηU (zg-ag) hεU hηU
        (sub_pos.mpr hagzg) EcornerU FU hFUSource hFU0 TU _ _ RU wgU βgU
        (by intro t; simp [wgU,eU,JU])
        (by intro t; simpa [wgU,eU,JU] using hArmsUSource wgU βgU t)
        hFUFormula hEnteringVectorUNe (Set.range g \ {u,z}) (by
          intro t ht hshort
          have hin := hActualOppositeSideArmU t ht hshort
          refine ⟨hin,?_⟩
          intro he
          apply hin.2
          simp [he])
    obtain ⟨sideTZ,hSideTZ,hSideTZCut,hSideTZShort,hSideZInG,hSideZCore,hSideZRay,hSideZYNe⟩ :=
      hActualEnteringArmCorePoint (r w).val z (qZ wgZ)
        (by simpa [wgZ,eZ,JZ] using hqZ wgZ) εZ ηZ (zg-ag) hεZ hηZ
        (sub_pos.mpr hagzg) EcornerZ FZ hFZSource hFZ0 TZ _ _ RZ wgZ βgZ
        (by intro t; simp [wgZ,eZ,JZ])
        (by intro t; simpa [wgZ,eZ,JZ] using hArmsZSource wgZ βgZ t)
        hFZFormula hEnteringVectorZNe (Set.range g \ {u,z}) (by
          intro t ht hshort
          have hin := hActualOppositeSideArmZ t ht hshort
          refine ⟨hin,?_⟩
          intro he
          apply hin.2
          simp [he])


    let otherCurveUnion : Set S := ⋃ i : I, if i = w then ∅ else (r i).val.image
    have hOtherCurveUnionClosed : IsClosed otherCurveUnion := by
      apply isClosed_iUnion_of_finite
      intro i
      split_ifs
      · exact isClosed_empty
      · exact (isCompact_range (r i).val.embedded.continuous).isClosed


    have hActualOriginalSideGapAtPoint (y : S)
        (hyG : y ∈ Set.range g \ {u,z}) (hySafe : y ∉ otherCurveUnion) :
        ∃ L R : ℝ, -1 < L ∧ L < Eopposite y 0 ∧ Eopposite y 0 < R ∧ R < 1 ∧
          Disjoint (Set.Icc L R) (contactCoordinates : Set ℝ) := by
      have hyPatch := hOppositePatchActual.symm ▸ hyG.1
      have hyE : y ∈ Eopposite.source := hyPatch.1.1
      have hy0 : Eopposite y 1 = 0 :=
        (hOppositeAxisEntire y hyE).mp (hgcurve hyG.1)
      have hcoord : Eopposite y = Plane.mk (Eopposite y 0) 0 := by
        ext i
        fin_cases i
        · rfl
        · exact hy0
      have hbound : |Eopposite y 0| ≤ 1 := by
        have hh := mem_closedSquare_zero_one.mp hyPatch.1.2
        rw [hcoord] at hh
        change max |Eopposite y 0| |(0 : ℝ)| ≤ 1 at hh
        exact le_trans (le_max_left _ _) hh
      have hNotEndpoint (θ : ℝ) (hθ : θ = ag ∨ θ = zg) : y ≠ γg θ := by
        intro he
        apply hyG.2
        rcases hθ with rfl | rfl <;> rcases hGEndpointOrientation with hOr | hOr
        · simp [he,hOr.1]
        · simp [he,hOr.2]
        · simp [he,hOr.2]
        · simp [he,hOr.1]
      have hnLeft : Eopposite y 0 ≠ -1 := by
        intro he
        apply hNotEndpoint ag (Or.inl rfl)
        apply Eopposite.injOn hyE (hGInOpposite ⟨ag,⟨le_rfl,hagzg.le⟩,rfl⟩)
        rw [hcoord,he]
        exact hOppositeLeft.symm
      have hnRight : Eopposite y 0 ≠ 1 := by
        intro he
        apply hNotEndpoint zg (Or.inr rfl)
        apply Eopposite.injOn hyE (hGInOpposite ⟨zg,⟨hagzg.le,le_rfl⟩,rfl⟩)
        rw [hcoord,he]
        exact hOppositeRight.symm
      have hleft : -1 < Eopposite y 0 :=
        lt_of_le_of_ne (abs_le.mp hbound).1 (Ne.symm hnLeft)
      have hright : Eopposite y 0 < 1 :=
        lt_of_le_of_ne (abs_le.mp hbound).2 hnRight
      have hnotContact : Eopposite y 0 ∉ contactCoordinates := by
        intro hc
        obtain ⟨p,hp⟩ := (hActualContactCoordinates _).mp hc
        have hpFacts := hPgFacts p.val p.property
        have hpE := hGInOpposite (hGAngleImage ▸ hpFacts.1)
        have hp0 := (hOppositeAxisEntire p.val hpE).mp hpFacts.2.2.2.1
        have heq : p.val = y := by
          apply Eopposite.injOn hpE hyE
          ext i
          fin_cases i
          · exact hp
          · exact hp0.trans hy0.symm
        apply hySafe
        rw [← heq]
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp p.property
        refine Set.mem_iUnion.mpr ⟨i,?_⟩
        by_cases hiw : i = w
        · simpa [hiw] using hi
        · rw [ite_eq_right hiw] at hi ⊢
          exact hi.2
      have hopen : IsOpen ((Set.Ioo (-1 : ℝ) 1) ∩ (contactCoordinates : Set ℝ)ᶜ) :=
        isOpen_Ioo.inter contactCoordinates.finite_toSet.isClosed.isOpen_compl
      obtain ⟨a,ha,hball⟩ := Metric.isOpen_iff.mp hopen (Eopposite y 0)
        ⟨⟨hleft,hright⟩,hnotContact⟩
      let L := Eopposite y 0-a/2
      let R := Eopposite y 0+a/2
      have hgap (x : ℝ) (hx : x ∈ Set.Icc L R) :
          x ∈ Set.Ioo (-1 : ℝ) 1 ∩ (contactCoordinates : Set ℝ)ᶜ := by
        apply hball
        change dist x (Eopposite y 0) < a
        rw [Real.dist_eq,abs_lt]
        dsimp [L,R] at hx
        constructor <;> linarith only [ha,hx.1,hx.2]
      refine ⟨L,R,(hgap L (by constructor <;> dsimp [L,R] <;> linarith only [ha])).1.1,
        ?_,?_,(hgap R (by constructor <;> dsimp [L,R] <;> linarith only [ha])).1.2,?_⟩
      · dsimp [L]; linarith only [ha]
      · dsimp [R]; linarith only [ha]
      · exact Set.disjoint_left.mpr (fun x hx hc => (hgap x hx).2 hc)

    let germU := (r w).val.map ((qU wgU)*Circle.exp
      (if βgU then εU*sideTU.val else -(εU*sideTU.val)))
    have hGermUInG : germU ∈ Set.range g \ {u,z} := hSideUInG
    have hGermUBall : FU germU ∈ Metric.ball (0 : Plane) ηU := hSideUCore
    have hGermURay : FU germU ∈ segment ℝ (0 : Plane) (TU (RU.vector (wgU,βgU))) := hSideURay
    have hGermUY : FU germU 1 ≠ 0 := hSideUYNe
    have hGermUPairSign : TU (RU.vector (wgU,βgU)) 1 *
        TU (RU.vector (wgU,!βgU)) 1 < 0 := by
      have hs := hUArmSigns wgU (by simpa [wgU,eU,JU] using hvw.symm)
      cases βgU <;> simpa [mul_comm] using hs
    have hNewCornerStartBallU : Plane.mk (-δU) 0 ∈ Metric.ball (0 : Plane) ηU :=
      hConnectorBallU (left_mem_segment ℝ _ _)

    have hGermUSource : germU ∈ FU.source := by
      rw [hFUSource]
      simpa [germU,wgU,eU,JU] using hArmsUSource wgU βgU sideTU
    have hGermUAvoidOthers : germU ∉ otherCurveUnion := by
      intro hbad
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hbad
      by_cases hiw : i = w
      · simpa [hiw] using hi
      · rw [ite_eq_right hiw] at hi
        have hmeet := hUContacts w i (Ne.symm hiw)
          ⟨hEcornerUSub (hFUSource ▸ hGermUSource),hgcurve hGermUInG.1,hi⟩
        have he : germU = u := Set.mem_singleton_iff.mp hmeet
        exact hGermUInG.2 (by simp [he])
    let actualCornerSafeFaceU := FU '' (FU.source ∩ otherCurveUnionᶜ)
    have hActualCornerSafeFaceUOpen : IsOpen actualCornerSafeFaceU :=
      FU.isOpen_image_source_inter hOtherCurveUnionClosed.isOpen_compl
    have hActualGermSafeFaceU : FU germU ∈ actualCornerSafeFaceU :=
      ⟨germU,⟨hGermUSource,hGermUAvoidOthers⟩,rfl⟩

    obtain ⟨cornerToleranceU,hCornerToleranceU,hNearCornerPlaneU⟩ :=
      actual_near_entering_ray_corner_family δU ηU hδU (FU germU)
        (TU (RU.vector (wgU,βgU))) (TU (RU.vector (wgU,!βgU)))
        hGermURay hGermUY hGermUPairSign actualCornerSafeFaceU hActualCornerSafeFaceUOpen hActualGermSafeFaceU
        hNewCornerStartBallU hGermUBall
    let nearCornerPlaneU (ε : ℝ) := segment ℝ (Plane.mk (-δU) 0)
      (Plane.mk (FU germU 0-ε) (FU germU 1))
    let nearCornerSurfaceU (ε : ℝ) := FU.symm '' nearCornerPlaneU ε
    have hNearCornerCoreU (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceU) :
        nearCornerPlaneU ε ⊆ FU.target ∩ Metric.ball (0 : Plane) ρU :=
      (hNearCornerPlaneU ε hε hεsmall).2.1.trans hBallU
    have hNearCornerSubU (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceU) :
        nearCornerSurfaceU ε ⊆ Ucorner := by
      rintro x ⟨y,hy,rfl⟩
      exact hEcornerUSub (hFUSource ▸ FU.map_target (hNearCornerCoreU ε hε hεsmall hy).1)
    have hNearCornerRemainderAvoidU (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceU) :
        Disjoint (nearCornerSurfaceU ε) K := by
      apply Set.disjoint_left.mpr
      intro x hx hxK
      have hxLarge := (hUcornerV (hNearCornerSubU ε hε hεsmall hx)).2
      have hxNotK := (hDiskInWK (interior_subset hxLarge)).2
      exact hxNotK hxK
    have hNearCornerIncidentCountsU (ε : ℝ) (hε : 0 < ε)
        (hεsmall : ε < cornerToleranceU) : ∀ j : KU,
        ((nearCornerSurfaceU ε) ∩ (r (eU.symm j.val).val).val.image).Finite ∧
        ((nearCornerSurfaceU ε) ∩ (r (eU.symm j.val).val).val.image).ncard ≤ 1 := by
      apply hTransportCounts FU ρU (nearCornerPlaneU ε) (hNearCornerCoreU ε hε hεsmall)
        (fun j : KU => (r (eU.symm j.val).val).val) aU bU
      · intro j x hx hxN
        rw [hUnionU j]
        exact hFUModel j.val x hx hxN
      · exact actual_signed_corner_segment_counts aU bU haU hbU δU
          (FU germU 0-ε) (FU germU 1) hδU hGermUY
    have hNearCornerWholeCountsU (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceU)
        (i : I) (hi : i ≠ v) :
        ((nearCornerSurfaceU ε) ∩ (r i).val.image).Finite ∧
        ((nearCornerSurfaceU ε) ∩ (r i).val.image).ncard ≤ if u ∈ (r i).val.image then 1 else 0 := by
      by_cases hpi : u ∈ (r i).val.image
      · rw [ite_eq_left hpi]
        let j : KU := ⟨eU ⟨i,hpi⟩,by simpa using hi⟩
        simpa [j] using hNearCornerIncidentCountsU ε hε hεsmall j
      · rw [ite_eq_right hpi]
        have hd : Disjoint (nearCornerSurfaceU ε) (r i).val.image :=
          (hUNonincident i hpi).mono_left (hNearCornerSubU ε hε hεsmall)
        rw [Set.disjoint_iff_inter_eq_empty.mp hd]
        exact ⟨Set.finite_empty,by simp⟩

    let germZ := (r w).val.map ((qZ wgZ)*Circle.exp
      (if βgZ then εZ*sideTZ.val else -(εZ*sideTZ.val)))
    have hGermZInG : germZ ∈ Set.range g \ {u,z} := hSideZInG
    have hGermZBall : FZ germZ ∈ Metric.ball (0 : Plane) ηZ := hSideZCore
    have hGermZRay : FZ germZ ∈ segment ℝ (0 : Plane) (TZ (RZ.vector (wgZ,βgZ))) := hSideZRay
    have hGermZY : FZ germZ 1 ≠ 0 := hSideZYNe
    have hGermZPairSign : TZ (RZ.vector (wgZ,βgZ)) 1 *
        TZ (RZ.vector (wgZ,!βgZ)) 1 < 0 := by
      have hs := hZArmSigns wgZ (by simpa [wgZ,eZ,JZ] using hvw.symm)
      cases βgZ <;> simpa [mul_comm] using hs
    have hNewCornerStartBallZ : Plane.mk (-δZ) 0 ∈ Metric.ball (0 : Plane) ηZ :=
      hConnectorBallZ (left_mem_segment ℝ _ _)

    have hGermZSource : germZ ∈ FZ.source := by
      rw [hFZSource]
      simpa [germZ,wgZ,eZ,JZ] using hArmsZSource wgZ βgZ sideTZ
    have hGermZAvoidOthers : germZ ∉ otherCurveUnion := by
      intro hbad
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hbad
      by_cases hiw : i = w
      · simpa [hiw] using hi
      · rw [ite_eq_right hiw] at hi
        have hmeet := hZContacts w i (Ne.symm hiw)
          ⟨hEcornerZSub (hFZSource ▸ hGermZSource),hgcurve hGermZInG.1,hi⟩
        have he : germZ = z := Set.mem_singleton_iff.mp hmeet
        exact hGermZInG.2 (by simp [he])
    let actualCornerSafeFaceZ := FZ '' (FZ.source ∩ otherCurveUnionᶜ)
    have hActualCornerSafeFaceZOpen : IsOpen actualCornerSafeFaceZ :=
      FZ.isOpen_image_source_inter hOtherCurveUnionClosed.isOpen_compl
    have hActualGermSafeFaceZ : FZ germZ ∈ actualCornerSafeFaceZ :=
      ⟨germZ,⟨hGermZSource,hGermZAvoidOthers⟩,rfl⟩

    obtain ⟨cornerToleranceZ,hCornerToleranceZ,hNearCornerPlaneZ⟩ :=
      actual_near_entering_ray_corner_family δZ ηZ hδZ (FZ germZ)
        (TZ (RZ.vector (wgZ,βgZ))) (TZ (RZ.vector (wgZ,!βgZ)))
        hGermZRay hGermZY hGermZPairSign actualCornerSafeFaceZ hActualCornerSafeFaceZOpen hActualGermSafeFaceZ
        hNewCornerStartBallZ hGermZBall
    let nearCornerPlaneZ (ε : ℝ) := segment ℝ (Plane.mk (-δZ) 0)
      (Plane.mk (FZ germZ 0-ε) (FZ germZ 1))
    let nearCornerSurfaceZ (ε : ℝ) := FZ.symm '' nearCornerPlaneZ ε
    have hNearCornerCoreZ (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceZ) :
        nearCornerPlaneZ ε ⊆ FZ.target ∩ Metric.ball (0 : Plane) ρZ :=
      (hNearCornerPlaneZ ε hε hεsmall).2.1.trans hBallZ
    have hNearCornerSubZ (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceZ) :
        nearCornerSurfaceZ ε ⊆ Zcorner := by
      rintro x ⟨y,hy,rfl⟩
      exact hEcornerZSub (hFZSource ▸ FZ.map_target (hNearCornerCoreZ ε hε hεsmall hy).1)
    have hNearCornerRemainderAvoidZ (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceZ) :
        Disjoint (nearCornerSurfaceZ ε) K := by
      apply Set.disjoint_left.mpr
      intro x hx hxK
      have hxLarge := (hZcornerV (hNearCornerSubZ ε hε hεsmall hx)).2
      have hxNotK := (hDiskInWK (interior_subset hxLarge)).2
      exact hxNotK hxK
    have hNearCornerIncidentCountsZ (ε : ℝ) (hε : 0 < ε)
        (hεsmall : ε < cornerToleranceZ) : ∀ j : KZ,
        ((nearCornerSurfaceZ ε) ∩ (r (eZ.symm j.val).val).val.image).Finite ∧
        ((nearCornerSurfaceZ ε) ∩ (r (eZ.symm j.val).val).val.image).ncard ≤ 1 := by
      apply hTransportCounts FZ ρZ (nearCornerPlaneZ ε) (hNearCornerCoreZ ε hε hεsmall)
        (fun j : KZ => (r (eZ.symm j.val).val).val) aZ bZ
      · intro j x hx hxN
        rw [hUnionZ j]
        exact hFZModel j.val x hx hxN
      · exact actual_signed_corner_segment_counts aZ bZ haZ hbZ δZ
          (FZ germZ 0-ε) (FZ germZ 1) hδZ hGermZY
    have hNearCornerWholeCountsZ (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceZ)
        (i : I) (hi : i ≠ v) :
        ((nearCornerSurfaceZ ε) ∩ (r i).val.image).Finite ∧
        ((nearCornerSurfaceZ ε) ∩ (r i).val.image).ncard ≤ if z ∈ (r i).val.image then 1 else 0 := by
      by_cases hpi : z ∈ (r i).val.image
      · rw [ite_eq_left hpi]
        let j : KZ := ⟨eZ ⟨i,hpi⟩,by simpa using hi⟩
        simpa [j] using hNearCornerIncidentCountsZ ε hε hεsmall j
      · rw [ite_eq_right hpi]
        have hd : Disjoint (nearCornerSurfaceZ ε) (r i).val.image :=
          (hZNonincident i hpi).mono_left (hNearCornerSubZ ε hε hεsmall)
        rw [Set.disjoint_iff_inter_eq_empty.mp hd]
        exact ⟨Set.finite_empty,by simp⟩



    have hActualNearCornerEndpointAvoidOthersU (ε : ℝ) (hε : 0 < ε)
        (hεsmall : ε < cornerToleranceU) :
        FU.symm (Plane.mk (FU germU 0-ε) (FU germU 1)) ∉ otherCurveUnion := by
      obtain ⟨x,⟨hxS,hxSafe⟩,hxEq⟩ := (hNearCornerPlaneU ε hε hεsmall).1
      rwa [← hxEq,FU.left_inv hxS]

    have hNearCornerOppositeAvoidU (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceU) :
        Disjoint (nearCornerSurfaceU ε) (r w).val.image := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y,hy,rfl⟩ hxw
      have hys := FU.map_target (hNearCornerCoreU ε hε hεsmall hy).1
      have hyn : ‖FU (FU.symm y)‖ < ρU := by
        rw [FU.right_inv (hNearCornerCoreU ε hε hεsmall hy).1]
        simpa using (hNearCornerCoreU ε hε hεsmall hy).2
      have hxw' : FU.symm y ∈ (r (eU.symm wgU).val).val.image := by
        simpa [wgU] using hxw
      have hm := (hFUModel wgU (FU.symm y) hys hyn).mp hxw'
      rw [FU.right_inv (hNearCornerCoreU ε hε hεsmall hy).1] at hm
      have hd : Disjoint (nearCornerPlaneU ε)
          (segment ℝ (0 : Plane) (TU (RU.vector (wgU,false))) ∪
            segment ℝ (0 : Plane) (TU (RU.vector (wgU,true)))) := by
        have hh := (hNearCornerPlaneU ε hε hεsmall).2.2
        cases hβ : βgU <;> simpa only [hβ,Bool.not_false,Bool.not_true,nearCornerPlaneU,Set.union_comm] using hh
      exact Set.disjoint_left.mp hd hy hm
    have hActualExteriorCornerProducerU (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceU) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧
          Set.range arc = nearCornerSurfaceU ε ∧ arc 0 = cornerArcU 0 ∧
          arc 1 = FU.symm (Plane.mk (FU germU 0-ε) (FU germU 1)) ∧
          Set.range arc ⊆ (Set.range d)ᶜ ∧ Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if u ∈ (r i).val.image then 1 else 0) := by
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hCoords⟩ :=
        actual_signed_chart_connector_arc FU δU (FU germU 0-ε) (FU germU 1)
          hGermUY (fun y hy => (hNearCornerCoreU ε hε hεsmall hy).1)
      have hStartOld : arc 0 = cornerArcU 0 := hStart.trans hCornerStartU.symm
      have hMeet : Set.range arc ∩ (r v).val.image = {arc 0} := by
        apply actual_signed_chart_connector_selected_meet (r v).val FU δU
          (FU germU 0-ε) (FU germU 1) ρU hGermUY arc hRange hStart
          (hStartOld.symm ▸ hCornerStartCurveU) (hNearCornerCoreU ε hε hεsmall)
        simpa [eU] using hFUAxis
      have hAvoidF : Disjoint (Set.range arc) (Set.range f) := by
        apply Set.disjoint_left.mpr
        intro x hx hxf
        have he : x = arc 0 := Set.mem_singleton_iff.mp (hMeet ▸ ⟨hx,hfcurve hxf⟩)
        exact hCornerStartExteriorU ((he.trans hStartOld) ▸ hxf)
      have hAvoidG : Disjoint (Set.range arc) (r w).val.image := by
        rw [hRange]
        exact hNearCornerOppositeAvoidU ε hε hεsmall
      refine ⟨arc,hEmb,hRange,hStartOld,hEnd,?_,?_,?_⟩
      · exact hActualCornerOutsideDisk arc hAvoidF hAvoidG
          (hStartOld.symm ▸ hCornerStartOutsideDiskU)
      · rw [hRange]
        exact hNearCornerRemainderAvoidU ε hε hεsmall
      · intro i hi
        rw [hRange]
        exact hNearCornerWholeCountsU ε hε hεsmall i hi


    have hActualNearCornerEndpointAvoidOthersZ (ε : ℝ) (hε : 0 < ε)
        (hεsmall : ε < cornerToleranceZ) :
        FZ.symm (Plane.mk (FZ germZ 0-ε) (FZ germZ 1)) ∉ otherCurveUnion := by
      obtain ⟨x,⟨hxS,hxSafe⟩,hxEq⟩ := (hNearCornerPlaneZ ε hε hεsmall).1
      rwa [← hxEq,FZ.left_inv hxS]

    have hNearCornerOppositeAvoidZ (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceZ) :
        Disjoint (nearCornerSurfaceZ ε) (r w).val.image := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y,hy,rfl⟩ hxw
      have hys := FZ.map_target (hNearCornerCoreZ ε hε hεsmall hy).1
      have hyn : ‖FZ (FZ.symm y)‖ < ρZ := by
        rw [FZ.right_inv (hNearCornerCoreZ ε hε hεsmall hy).1]
        simpa using (hNearCornerCoreZ ε hε hεsmall hy).2
      have hxw' : FZ.symm y ∈ (r (eZ.symm wgZ).val).val.image := by
        simpa [wgZ] using hxw
      have hm := (hFZModel wgZ (FZ.symm y) hys hyn).mp hxw'
      rw [FZ.right_inv (hNearCornerCoreZ ε hε hεsmall hy).1] at hm
      have hd : Disjoint (nearCornerPlaneZ ε)
          (segment ℝ (0 : Plane) (TZ (RZ.vector (wgZ,false))) ∪
            segment ℝ (0 : Plane) (TZ (RZ.vector (wgZ,true)))) := by
        have hh := (hNearCornerPlaneZ ε hε hεsmall).2.2
        cases hβ : βgZ <;> simpa only [hβ,Bool.not_false,Bool.not_true,nearCornerPlaneZ,Set.union_comm] using hh
      exact Set.disjoint_left.mp hd hy hm
    have hActualExteriorCornerProducerZ (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < cornerToleranceZ) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧
          Set.range arc = nearCornerSurfaceZ ε ∧ arc 0 = cornerArcZ 0 ∧
          arc 1 = FZ.symm (Plane.mk (FZ germZ 0-ε) (FZ germZ 1)) ∧
          Set.range arc ⊆ (Set.range d)ᶜ ∧ Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if z ∈ (r i).val.image then 1 else 0) := by
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hCoords⟩ :=
        actual_signed_chart_connector_arc FZ δZ (FZ germZ 0-ε) (FZ germZ 1)
          hGermZY (fun y hy => (hNearCornerCoreZ ε hε hεsmall hy).1)
      have hStartOld : arc 0 = cornerArcZ 0 := hStart.trans hCornerStartZ.symm
      have hMeet : Set.range arc ∩ (r v).val.image = {arc 0} := by
        apply actual_signed_chart_connector_selected_meet (r v).val FZ δZ
          (FZ germZ 0-ε) (FZ germZ 1) ρZ hGermZY arc hRange hStart
          (hStartOld.symm ▸ hCornerStartCurveZ) (hNearCornerCoreZ ε hε hεsmall)
        simpa [eZ] using hFZAxis
      have hAvoidF : Disjoint (Set.range arc) (Set.range f) := by
        apply Set.disjoint_left.mpr
        intro x hx hxf
        have he : x = arc 0 := Set.mem_singleton_iff.mp (hMeet ▸ ⟨hx,hfcurve hxf⟩)
        exact hCornerStartExteriorZ ((he.trans hStartOld) ▸ hxf)
      have hAvoidG : Disjoint (Set.range arc) (r w).val.image := by
        rw [hRange]
        exact hNearCornerOppositeAvoidZ ε hε hεsmall
      refine ⟨arc,hEmb,hRange,hStartOld,hEnd,?_,?_,?_⟩
      · exact hActualCornerOutsideDisk arc hAvoidF hAvoidG
          (hStartOld.symm ▸ hCornerStartOutsideDiskZ)
      · rw [hRange]
        exact hNearCornerRemainderAvoidZ ε hε hεsmall
      · intro i hi
        rw [hRange]
        exact hNearCornerWholeCountsZ ε hε hεsmall i hi


    have hGermUOppositeSource : germU ∈ Eopposite.source :=
      hGInOpposite (hGAngleImage ▸ hGermUInG.1)
    obtain ⟨gapLU,gapRU,hGapLU,hGermGapLeftU,hGermGapRightU,hGapRU,hGermGapFreeU⟩ :=
      hActualOriginalSideGapAtPoint germU hGermUInG hGermUAvoidOthers
    obtain ⟨endpointScaleU,hEndpointScaleU,hEndpointScaleBoundU,actualCornerEndpointU,
        hActualCornerEndpointUZero,hActualCornerEndpointUCoordinates⟩ :=
      actual_corner_endpoint_common_chart_family FU Eopposite germU
        hGermUSource hGermUOppositeSource cornerToleranceU hCornerToleranceU
    have hActualCornerEndpointUProducer (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧ arc 0 = cornerArcU 0 ∧
          arc 1 = actualCornerEndpointU t ∧ Set.range arc ⊆ (Set.range d)ᶜ ∧
          Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if u ∈ (r i).val.image then 1 else 0) := by
      have hε : 0 < endpointScaleU*t.val := mul_pos hEndpointScaleU ht
      have hεsmall : endpointScaleU*t.val < cornerToleranceU :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleU.le t.property.2) hEndpointScaleBoundU
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hOut,hK,hCounts⟩ :=
        hActualExteriorCornerProducerU (endpointScaleU*t.val) hε hεsmall
      refine ⟨arc,hEmb,hStart,?_,hOut,hK,hCounts⟩
      exact hEnd.trans (hActualCornerEndpointUCoordinates t).2.2.symm


    have hGermZOppositeSource : germZ ∈ Eopposite.source :=
      hGInOpposite (hGAngleImage ▸ hGermZInG.1)
    obtain ⟨gapLZ,gapRZ,hGapLZ,hGermGapLeftZ,hGermGapRightZ,hGapRZ,hGermGapFreeZ⟩ :=
      hActualOriginalSideGapAtPoint germZ hGermZInG hGermZAvoidOthers
    obtain ⟨endpointScaleZ,hEndpointScaleZ,hEndpointScaleBoundZ,actualCornerEndpointZ,
        hActualCornerEndpointZZero,hActualCornerEndpointZCoordinates⟩ :=
      actual_corner_endpoint_common_chart_family FZ Eopposite germZ
        hGermZSource hGermZOppositeSource cornerToleranceZ hCornerToleranceZ
    have hActualCornerEndpointZProducer (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧ arc 0 = cornerArcZ 0 ∧
          arc 1 = actualCornerEndpointZ t ∧ Set.range arc ⊆ (Set.range d)ᶜ ∧
          Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if z ∈ (r i).val.image then 1 else 0) := by
      have hε : 0 < endpointScaleZ*t.val := mul_pos hEndpointScaleZ ht
      have hεsmall : endpointScaleZ*t.val < cornerToleranceZ :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleZ.le t.property.2) hEndpointScaleBoundZ
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hOut,hK,hCounts⟩ :=
        hActualExteriorCornerProducerZ (endpointScaleZ*t.val) hε hεsmall
      refine ⟨arc,hEmb,hStart,?_,hOut,hK,hCounts⟩
      exact hEnd.trans (hActualCornerEndpointZCoordinates t).2.2.symm


    let actualCornerEndpointHeightU : C(Interval,ℝ) :=
      ⟨fun t => Eopposite (actualCornerEndpointU t) 1,
        (show Continuous (fun z : Plane => z 1) from by fun_prop).comp (Eopposite.continuousOn.comp_continuous
          actualCornerEndpointU.continuous (fun t => (hActualCornerEndpointUCoordinates t).2.1))⟩
    have hActualCornerEndpointHeightUZero : actualCornerEndpointHeightU 0 = 0 := by
      change Eopposite (actualCornerEndpointU 0) 1 = 0
      rw [hActualCornerEndpointUZero]
      exact (hOppositeAxisEntire germU hGermUOppositeSource).mp (hgcurve hGermUInG.1)
    have hActualCornerEndpointHeightUNe (t : Interval) (ht : 0 < t.val) :
        actualCornerEndpointHeightU t ≠ 0 := by
      intro he
      have hε : 0 < endpointScaleU*t.val := mul_pos hEndpointScaleU ht
      have hεsmall : endpointScaleU*t.val < cornerToleranceU :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleU.le t.property.2) hEndpointScaleBoundU
      have hmem : actualCornerEndpointU t ∈ nearCornerSurfaceU (endpointScaleU*t.val) := by
        rw [(hActualCornerEndpointUCoordinates t).2.2]
        exact ⟨_,right_mem_segment ℝ _ _,rfl⟩
      have hw : actualCornerEndpointU t ∈ (r w).val.image :=
        (hOppositeAxisEntire _ (hActualCornerEndpointUCoordinates t).2.1).mpr he
      exact Set.disjoint_left.mp (hNearCornerOppositeAvoidU _ hε hεsmall) hmem hw
    obtain ⟨actualCornerHalfSignU,hActualCornerHalfSignU,hActualCornerHalfSideU⟩ :=
      actual_continuous_positive_parameter_sign actualCornerEndpointHeightU hActualCornerEndpointHeightUNe

    let actualCornerEndpointHeightZ : C(Interval,ℝ) :=
      ⟨fun t => Eopposite (actualCornerEndpointZ t) 1,
        (show Continuous (fun z : Plane => z 1) from by fun_prop).comp (Eopposite.continuousOn.comp_continuous
          actualCornerEndpointZ.continuous (fun t => (hActualCornerEndpointZCoordinates t).2.1))⟩
    have hActualCornerEndpointHeightZZero : actualCornerEndpointHeightZ 0 = 0 := by
      change Eopposite (actualCornerEndpointZ 0) 1 = 0
      rw [hActualCornerEndpointZZero]
      exact (hOppositeAxisEntire germZ hGermZOppositeSource).mp (hgcurve hGermZInG.1)
    have hActualCornerEndpointHeightZNe (t : Interval) (ht : 0 < t.val) :
        actualCornerEndpointHeightZ t ≠ 0 := by
      intro he
      have hε : 0 < endpointScaleZ*t.val := mul_pos hEndpointScaleZ ht
      have hεsmall : endpointScaleZ*t.val < cornerToleranceZ :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleZ.le t.property.2) hEndpointScaleBoundZ
      have hmem : actualCornerEndpointZ t ∈ nearCornerSurfaceZ (endpointScaleZ*t.val) := by
        rw [(hActualCornerEndpointZCoordinates t).2.2]
        exact ⟨_,right_mem_segment ℝ _ _,rfl⟩
      have hw : actualCornerEndpointZ t ∈ (r w).val.image :=
        (hOppositeAxisEntire _ (hActualCornerEndpointZCoordinates t).2.1).mpr he
      exact Set.disjoint_left.mp (hNearCornerOppositeAvoidZ _ hε hεsmall) hmem hw
    obtain ⟨actualCornerHalfSignZ,hActualCornerHalfSignZ,hActualCornerHalfSideZ⟩ :=
      actual_continuous_positive_parameter_sign actualCornerEndpointHeightZ hActualCornerEndpointHeightZNe


    have hActualAxisCornerCoordinates :
        (Eopposite u 0 = -1 ∧ Eopposite z 0 = 1) ∨
        (Eopposite u 0 = 1 ∧ Eopposite z 0 = -1) := by
      rcases hGEndpointOrientation with ho | ho
      · left
        constructor
        · rw [ho.1]
          exact congrArg (fun p : Plane => p 0) hOppositeLeft
        · rw [ho.2]
          exact congrArg (fun p : Plane => p 0) hOppositeRight
      · right
        constructor
        · rw [ho.1]
          exact congrArg (fun p : Plane => p 0) hOppositeRight
        · rw [ho.2]
          exact congrArg (fun p : Plane => p 0) hOppositeLeft
    have hActualSourceExteriorStrip (L R : ℝ) (hL : -1 < L) (hLR : L < R) (hR : R < 1) :
        ∃ ε σ : ℝ, 0 < ε ∧ (σ = -1 ∨ σ = 1) ∧
          (∀ q : Plane, L < q 0 → q 0 < R → -ε < q 1 → q 1 < ε →
            q ∈ Eopposite.target ∧ Eopposite.symm q ∉ (r v).val.image ∧
              Eopposite.symm q ∉ K) ∧
          (∀ q : Plane, L < q 0 → q 0 < R → -ε < q 1 → q 1 < ε → q 1 ≠ 0 →
            (Eopposite.symm q ∉ Set.range d ↔ 0 < σ*q 1)) := by
      have haxis : ∀ x ∈ Set.Icc L R, ∃ y : S, y ∈ Eopposite.source ∧
          Eopposite y = Plane.mk x 0 ∧ y ∉ (r v).val.image := by
        intro x hx
        obtain ⟨y,hyE,hyG,hEy⟩ := hActualAxisPointOnSide x
          ⟨hL.le.trans hx.1,hx.2.trans hR.le⟩
        refine ⟨y,hyE,hEy,?_⟩
        intro hyV
        have hmeet : y ∈ ({u,z} : Set S) := hgmeet ▸ ⟨hyG,hyV⟩
        rcases Set.mem_insert_iff.mp hmeet with he | he
        · have hxx := congrArg (fun p : Plane => p 0) hEy
          rw [he] at hxx
          change Eopposite u 0 = x at hxx
          rcases hActualAxisCornerCoordinates with hc | hc <;>
            linarith only [hL,hR,hx.1,hx.2,hxx,hc.1]
        · have he' : y = z := Set.mem_singleton_iff.mp he
          have hxx := congrArg (fun p : Plane => p 0) hEy
          rw [he'] at hxx
          change Eopposite z 0 = x at hxx
          rcases hActualAxisCornerCoordinates with hc | hc <;>
            linarith only [hL,hR,hx.1,hx.2,hxx,hc.2]
      obtain ⟨ε,hε,hclear⟩ := actual_original_axis_selected_curve_clearance
        Eopposite (r v).val L R haxis
      have hTarget : {q : Plane | L < q 0 ∧ q 0 < R ∧ -ε < q 1 ∧ q 1 < ε} ⊆
          Eopposite.target := fun q hq =>
        (hclear q ⟨hq.1.le,hq.2.1.le⟩ (abs_lt.mpr hq.2.2)).1
      have hFrontier (q : Plane) (hqL : L < q 0) (hqR : q 0 < R)
          (hqlo : -ε < q 1) (hqhi : q 1 < ε) :
          Eopposite.symm q ∈ frontier (Set.range d) ↔ q 1 = 0 := by
        have hqT := hTarget ⟨hqL,hqR,hqlo,hqhi⟩
        have hqE := Eopposite.map_target hqT
        have hcoord := Eopposite.right_inv hqT
        constructor
        · intro hfD
          rw [hActualOriginalDiskFrontier] at hfD
          rcases hfD with hqF | hqG
          · exact False.elim ((hclear q ⟨hqL.le,hqR.le⟩ (abs_lt.mpr ⟨hqlo,hqhi⟩)).2 (hfcurve hqF))
          · have hy := (hOppositeAxisEntire _ hqE).mp (hgcurve hqG)
            rwa [hcoord] at hy
        · intro hy
          have hqW : Eopposite.symm q ∈ (r w).val.image :=
            (hOppositeAxisEntire _ hqE).mpr (by rw [hcoord]; exact hy)
          have hqSq : q ∈ Plane.closedSquare 0 1 := by
            apply mem_closedSquare_zero_one.mpr
            change max |q 0| |q 1| ≤ 1
            rw [hy,abs_zero]
            exact max_le (abs_le.mpr ⟨(hL.trans hqL).le,(hqR.trans hR).le⟩) (by norm_num)
          have hqG : Eopposite.symm q ∈ Set.range g := hOppositePatchActual ▸
            ⟨⟨hqE,by rwa [hcoord]⟩,hqW⟩
          rw [hActualOriginalDiskFrontier]
          exact Or.inr hqG
      have hDclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
      have hregular : Set.range d ⊆ closure (interior (Set.range d)) := by
        rw [hDiskDensity d hd]
      obtain ⟨σ,hσ,hside⟩ := actual_chart_strip_exterior_half Eopposite (Set.range d)
        hDclosed hregular L R ε hLR hε hTarget hFrontier
      refine ⟨ε,σ,hε,hσ,?_,hside⟩
      intro q hqL hqR hqlo hqhi
      have hc := hclear q ⟨hqL.le,hqR.le⟩ (abs_lt.mpr ⟨hqlo,hqhi⟩)
      refine ⟨hc.1,hc.2,?_⟩
      have hxLarge := (hOppositeSource (Eopposite.map_target hc.1)).1
      exact (hDiskInWK (interior_subset hxLarge)).2


    have hActualSignedExteriorChart (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
        ∃ E : OpenPartialHomeomorph S Plane, E.source = Eopposite.source ∧
          (∀ x : S, E x 1 = σ*Eopposite x 1) ∧
          (∀ x ∈ E.source, x ∈ (r w).val.image ↔ E x 1 = 0) := by
      rcases hσ with rfl | rfl
      · let N : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.neg ℝ
        let E := Eopposite.transHomeomorph N.toHomeomorph
        refine ⟨E,rfl,?_,?_⟩
        · intro x
          change -(Eopposite x) 1 = -1*Eopposite x 1
          simp
        · intro x hx
          rw [hOppositeAxisEntire x hx]
          change Eopposite x 1 = 0 ↔ -(Eopposite x) 1 = 0
          simp
      · exact ⟨Eopposite,rfl,(by intro x; simp),hOppositeAxisEntire⟩


    let actualBoundaryPositions := insert (Eopposite germU 0)
      (insert (Eopposite germZ 0) contactCoordinates)
    have hActualBoundaryPositionsNonempty : actualBoundaryPositions.Nonempty :=
      ⟨Eopposite germU 0,Finset.mem_insert_self _ _⟩
    have hActualBoundaryPositionsInterior : ∀ x ∈ actualBoundaryPositions, -1 < x ∧ x < 1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with he | hx
      · subst x
        exact ⟨hGapLU.trans hGermGapLeftU,hGermGapRightU.trans hGapRU⟩
      · rcases Finset.mem_insert.mp hx with he | hx
        · subst x
          exact ⟨hGapLZ.trans hGermGapLeftZ,hGermGapRightZ.trans hGapRZ⟩
        · obtain ⟨p,hp⟩ := (hActualContactCoordinates x).mp hx
          rw [← hp]
          exact hActualContactCoordinateBounds p
    obtain ⟨actualStripL,actualStripR,hActualStripL,hActualStripLR,hActualStripR,hActualStripContains⟩ :=
      actual_finite_boundary_coordinate_enclosing_interval actualBoundaryPositions
        hActualBoundaryPositionsNonempty hActualBoundaryPositionsInterior
    obtain ⟨actualStripWidth,actualExteriorSign,hActualStripWidth,hActualExteriorSign,
        hActualStripSupport,hActualStripSide⟩ :=
      hActualSourceExteriorStrip actualStripL actualStripR hActualStripL hActualStripLR hActualStripR
    obtain ⟨actualExteriorChart,hActualExteriorChartSource,hActualExteriorChartFormula,hActualExteriorChartAxis⟩ :=
      hActualSignedExteriorChart actualExteriorSign hActualExteriorSign
    have hActualExteriorContactPatches (p : Pg) :=
      hActualUniformInteriorContactProducer p actualExteriorChart
        hActualExteriorChartSource hActualExteriorChartAxis
    choose contactPatchChart contactPatchRadius contactPatchHalfWidth contactPatchHeight
      hContactPatchRadius hContactPatchHalfWidth hContactPatchHeight hContactPatchCenterSource hContactPatchCenter
      hContactPatchSource hContactPatchLeftTarget hContactPatchRightTarget
      hContactPatchOriginalAxis hContactPatchAxisOrder hContactPatchProducer
      hContactPatchActualRadialModel hContactPatchActualBallContainment using hActualExteriorContactPatches
    have hActualContactPatchRetainedRemainderAvoid (p : Pg) (h : ℝ)
        (hh : 0 < h) (hhSmall : h < contactPatchHeight p) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          f 0 = (contactPatchChart p).symm (Plane.mk (-contactPatchHalfWidth p) h) ∧
          f 1 = (contactPatchChart p).symm (Plane.mk (contactPatchHalfWidth p) h) ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      obtain ⟨f,hf,hRange,hf0,hf1,hSub,hPos,hAvoid,hCounts⟩ := (hContactPatchProducer p h hh hhSmall).2
      refine ⟨f,hf,hf0,hf1,hSub,(hActualInteriorSupportAvoidK p).mono_left hSub,?_,hAvoid,hCounts⟩
      intro x hx
      have hp := hPos x hx
      rwa [hActualExteriorChartFormula x] at hp


    let actualContactAxis (p : Pg) (x : ℝ) :=
      Eopposite ((contactPatchChart p).symm (Plane.mk x 0)) 0
    have hActualContactAxisContinuous (p : Pg) :
        ContinuousOn (actualContactAxis p) (Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p)) := by
      have hFpath : ContinuousOn (fun x : ℝ => (contactPatchChart p).symm (Plane.mk x 0))
          (Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p)) :=
        (contactPatchChart p).symm.continuousOn.comp (by fun_prop)
          (fun x hx => (hContactPatchOriginalAxis p x hx).1)
      have hEpath := Eopposite.continuousOn.comp hFpath
        (fun x hx => (hContactPatchOriginalAxis p x hx).2.1)
      exact (show Continuous (fun z : Plane => z 0) from by fun_prop).continuousOn.comp
        hEpath (fun _ _ => Set.mem_univ _)
    have hActualContactAxisZero (p : Pg) : actualContactAxis p 0 = contactX p := by
      have hz : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
      have hpSource := hContactPatchCenterSource p
      dsimp [actualContactAxis,contactX]
      rw [hz,← hContactPatchCenter p,(contactPatchChart p).left_inv hpSource]
    have hActualContactAxisSelectedAvoid (p : Pg) (x : ℝ)
        (hx : x ∈ Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p)) :
        (contactPatchChart p).symm (Plane.mk x 0) ∉ (r v).val.image := by
      intro hv
      have hh := ((hContactPatchOriginalAxis p x hx).2.2.2 v hvw).mp hv
      exact (hPgFacts p.val p.property).2.2.2.2 hh.2
    have hActualContactAxisEndpointAvoid (p : Pg) :
        (-1 : ℝ) ∉ actualContactAxis p '' Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p) ∧
        (1 : ℝ) ∉ actualContactAxis p '' Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p) := by
      have hNo (θ : ℝ) (hθ : θ = ag ∨ θ = zg) (e : ℝ)
          (he : Eopposite (γg θ) = Plane.mk e 0) :
          e ∉ actualContactAxis p '' Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p) := by
        rintro ⟨x,hx,hxe⟩
        let y := (contactPatchChart p).symm (Plane.mk x 0)
        have hdata := hContactPatchOriginalAxis p x hx
        have hγE := hGInOpposite ⟨θ,by rcases hθ with rfl | rfl <;> exact ⟨by linarith only [hagzg],by linarith only [hagzg]⟩,rfl⟩
        have hEy : Eopposite y = Plane.mk e 0 := by
          ext i
          fin_cases i
          · exact hxe
          · exact hdata.2.2.1
        have hyeq : y = γg θ := Eopposite.injOn hdata.2.1 hγE (hEy.trans he.symm)
        have hγV : γg θ ∈ (r v).val.image := by
          rcases hθ with rfl | rfl <;> rcases hGEndpointOrientation with ho | ho
          · rw [← ho.1]; exact huSelected
          · rw [← ho.2]; exact hzSelected
          · rw [← ho.2]; exact hzSelected
          · rw [← ho.1]; exact huSelected
        exact hActualContactAxisSelectedAvoid p x hx (by
          change y ∈ (r v).val.image
          rw [hyeq]
          exact hγV)
      exact ⟨hNo ag (Or.inl rfl) (-1) hOppositeLeft,hNo zg (Or.inr rfl) 1 hOppositeRight⟩
    have hActualContactAxisBounds (p : Pg) :
        actualContactAxis p '' Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p) ⊆
          Set.Ioo (-1 : ℝ) 1 := by
      apply actual_connected_axis_coordinate_bounds _
        (isPreconnected_Icc.image (actualContactAxis p) (hActualContactAxisContinuous p))
        (-1) 1 (contactX p)
      · exact ⟨0,⟨by linarith only [hContactPatchHalfWidth p],(hContactPatchHalfWidth p).le⟩,
          hActualContactAxisZero p⟩
      · exact (hActualContactCoordinateBounds p).1
      · exact (hActualContactCoordinateBounds p).2
      · exact (hActualContactAxisEndpointAvoid p).1
      · exact (hActualContactAxisEndpointAvoid p).2


    have hActualContactAxisInjective (p : Pg) :
        Set.InjOn (actualContactAxis p) (Set.Icc (-contactPatchHalfWidth p) (contactPatchHalfWidth p)) := by
      intro x hx y hy hxy
      have hdx := hContactPatchOriginalAxis p x hx
      have hdy := hContactPatchOriginalAxis p y hy
      have hEEq : Eopposite ((contactPatchChart p).symm (Plane.mk x 0)) =
          Eopposite ((contactPatchChart p).symm (Plane.mk y 0)) := by
        ext i
        fin_cases i
        · exact hxy
        · exact hdx.2.2.1.trans hdy.2.2.1.symm
      have hFEq := Eopposite.injOn hdx.2.1 hdy.2.1 hEEq
      have hPlane := (contactPatchChart p).symm.injOn hdx.1 hdy.1 hFEq
      exact congrArg (fun z : Plane => z 0) hPlane
    have hActualContactAxisImage (p : Pg) :=
      actual_continuous_injective_axis_image (actualContactAxis p) (contactPatchHalfWidth p)
        (hContactPatchHalfWidth p) (hActualContactAxisContinuous p) (hActualContactAxisInjective p)
    choose actualContactLeft actualContactRight hActualContactLeft hActualContactRight
      hActualContactAxisImageEq hActualContactAxisOrientation using hActualContactAxisImage
    have hActualContactAxisSourceMatching (p : Pg) :
        (contactCoordinates : Set ℝ) ∩ Set.Icc (actualContactLeft p) (actualContactRight p) = {contactX p} := by
      ext c
      constructor
      · rintro ⟨hc,hcI⟩
        obtain ⟨q,hq⟩ := (hActualContactCoordinates c).mp hc
        rw [← hActualContactAxisImageEq p] at hcI
        obtain ⟨x,hx,hxc⟩ := hcI
        have hd := hContactPatchOriginalAxis p x hx
        have hqFacts := hPgFacts q.val q.property
        have hqE := hGInOpposite (hGAngleImage ▸ hqFacts.1)
        have hqY := (hOppositeAxisEntire q.val hqE).mp hqFacts.2.2.2.1
        have hEq : (contactPatchChart p).symm (Plane.mk x 0) = q.val := by
          apply Eopposite.injOn hd.2.1 hqE
          ext i
          fin_cases i
          · exact hxc.trans hq.symm
          · exact hd.2.2.1.trans hqY.symm
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp q.property
        have hiw : i ≠ w := by
          intro he
          simp [he] at hi
        rw [ite_eq_right hiw] at hi
        have hqx : (contactPatchChart p).symm (Plane.mk x 0) ∈ (r i).val.image :=
          hEq.symm ▸ hi.2
        have hzero := ((hd.2.2.2 i hiw).mp hqx).1
        have hcEq : c = contactX p := by
          rw [hzero,hActualContactAxisZero p] at hxc
          exact hxc.symm
        exact hcEq
      · intro hc
        rw [Set.mem_singleton_iff] at hc
        subst c
        refine ⟨(hActualContactCoordinates _).mpr ⟨p,rfl⟩,?_⟩
        rw [← hActualContactAxisZero p]
        exact ⟨(hActualContactLeft p).le,(hActualContactRight p).le⟩


    have hActualCornerExteriorFaceU : ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
        actualStripL < Eopposite (actualCornerEndpointU t) 0 ∧
        Eopposite (actualCornerEndpointU t) 0 < actualStripR ∧
        0 < actualExteriorSign*Eopposite (actualCornerEndpointU t) 1 ∧
        Eopposite (actualCornerEndpointU t) 1 < actualStripWidth ∧
        -actualStripWidth < Eopposite (actualCornerEndpointU t) 1 := by
      have hmap : Continuous (fun t : Interval => Eopposite (actualCornerEndpointU t)) :=
        Eopposite.continuousOn.comp_continuous actualCornerEndpointU.continuous
          (fun t => (hActualCornerEndpointUCoordinates t).2.1)
      have hx : Continuous (fun t : Interval => Eopposite (actualCornerEndpointU t) 0) :=
        (show Continuous (fun z : Plane => z 0) from by fun_prop).comp hmap
      have hy : Continuous (fun t : Interval => Eopposite (actualCornerEndpointU t) 1) :=
        (show Continuous (fun z : Plane => z 1) from by fun_prop).comp hmap
      let O : Set Interval := {t | actualStripL < Eopposite (actualCornerEndpointU t) 0 ∧
        Eopposite (actualCornerEndpointU t) 0 < actualStripR ∧
        -actualStripWidth < Eopposite (actualCornerEndpointU t) 1 ∧
        Eopposite (actualCornerEndpointU t) 1 < actualStripWidth}
      have hO : IsOpen O := (isOpen_lt continuous_const hx).inter
        ((isOpen_lt hx continuous_const).inter
          ((isOpen_lt continuous_const hy).inter (isOpen_lt hy continuous_const)))
      have hGermBounds := hActualStripContains (Eopposite germU 0) (by
        simp [actualBoundaryPositions])
      have hy0 : Eopposite (actualCornerEndpointU 0) 1 = 0 := hActualCornerEndpointHeightUZero
      have hmem : (0 : Interval) ∈ O := by
        change actualStripL < Eopposite (actualCornerEndpointU 0) 0 ∧ _
        rw [hActualCornerEndpointUZero]
        have hzero : Eopposite germU 1 = 0 := by
          rw [hActualCornerEndpointUZero] at hy0
          exact hy0
        rw [hzero]
        exact ⟨hGermBounds.1,hGermBounds.2,neg_neg_of_pos hActualStripWidth,hActualStripWidth⟩
      obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hO 0 hmem
      refine ⟨ρ,hρ,?_⟩
      intro t ht htρ
      have hrect := hball (show t ∈ Metric.ball (0 : Interval) ρ by
        simpa [Subtype.dist_eq,Real.dist_eq,abs_of_pos ht] using htρ)
      have hpointOutside : actualCornerEndpointU t ∉ Set.range d := by
        obtain ⟨arc,hEmb,hStart,hEnd,hOut,hK,hCounts⟩ := hActualCornerEndpointUProducer t ht
        exact hOut ⟨1,hEnd⟩
      have hyNe := hActualCornerEndpointHeightUNe t ht
      have hSide := hActualStripSide (Eopposite (actualCornerEndpointU t))
        hrect.1 hrect.2.1 hrect.2.2.1 hrect.2.2.2 hyNe
      have hσy : 0 < actualExteriorSign*Eopposite (actualCornerEndpointU t) 1 := by
        apply hSide.mp
        rwa [Eopposite.left_inv (hActualCornerEndpointUCoordinates t).2.1]
      exact ⟨hrect.1,hrect.2.1,hσy,hrect.2.2.2,hrect.2.2.1⟩

    have hActualCornerExteriorFaceZ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
        actualStripL < Eopposite (actualCornerEndpointZ t) 0 ∧
        Eopposite (actualCornerEndpointZ t) 0 < actualStripR ∧
        0 < actualExteriorSign*Eopposite (actualCornerEndpointZ t) 1 ∧
        Eopposite (actualCornerEndpointZ t) 1 < actualStripWidth ∧
        -actualStripWidth < Eopposite (actualCornerEndpointZ t) 1 := by
      have hmap : Continuous (fun t : Interval => Eopposite (actualCornerEndpointZ t)) :=
        Eopposite.continuousOn.comp_continuous actualCornerEndpointZ.continuous
          (fun t => (hActualCornerEndpointZCoordinates t).2.1)
      have hx : Continuous (fun t : Interval => Eopposite (actualCornerEndpointZ t) 0) :=
        (show Continuous (fun z : Plane => z 0) from by fun_prop).comp hmap
      have hy : Continuous (fun t : Interval => Eopposite (actualCornerEndpointZ t) 1) :=
        (show Continuous (fun z : Plane => z 1) from by fun_prop).comp hmap
      let O : Set Interval := {t | actualStripL < Eopposite (actualCornerEndpointZ t) 0 ∧
        Eopposite (actualCornerEndpointZ t) 0 < actualStripR ∧
        -actualStripWidth < Eopposite (actualCornerEndpointZ t) 1 ∧
        Eopposite (actualCornerEndpointZ t) 1 < actualStripWidth}
      have hO : IsOpen O := (isOpen_lt continuous_const hx).inter
        ((isOpen_lt hx continuous_const).inter
          ((isOpen_lt continuous_const hy).inter (isOpen_lt hy continuous_const)))
      have hGermBounds := hActualStripContains (Eopposite germZ 0) (by
        simp [actualBoundaryPositions])
      have hy0 : Eopposite (actualCornerEndpointZ 0) 1 = 0 := hActualCornerEndpointHeightZZero
      have hmem : (0 : Interval) ∈ O := by
        change actualStripL < Eopposite (actualCornerEndpointZ 0) 0 ∧ _
        rw [hActualCornerEndpointZZero]
        have hzero : Eopposite germZ 1 = 0 := by
          rw [hActualCornerEndpointZZero] at hy0
          exact hy0
        rw [hzero]
        exact ⟨hGermBounds.1,hGermBounds.2,neg_neg_of_pos hActualStripWidth,hActualStripWidth⟩
      obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hO 0 hmem
      refine ⟨ρ,hρ,?_⟩
      intro t ht htρ
      have hrect := hball (show t ∈ Metric.ball (0 : Interval) ρ by
        simpa [Subtype.dist_eq,Real.dist_eq,abs_of_pos ht] using htρ)
      have hpointOutside : actualCornerEndpointZ t ∉ Set.range d := by
        obtain ⟨arc,hEmb,hStart,hEnd,hOut,hK,hCounts⟩ := hActualCornerEndpointZProducer t ht
        exact hOut ⟨1,hEnd⟩
      have hyNe := hActualCornerEndpointHeightZNe t ht
      have hSide := hActualStripSide (Eopposite (actualCornerEndpointZ t))
        hrect.1 hrect.2.1 hrect.2.2.1 hrect.2.2.2 hyNe
      have hσy : 0 < actualExteriorSign*Eopposite (actualCornerEndpointZ t) 1 := by
        apply hSide.mp
        rwa [Eopposite.left_inv (hActualCornerEndpointZCoordinates t).2.1]
      exact ⟨hrect.1,hrect.2.1,hσy,hrect.2.2.2,hrect.2.2.1⟩


    have hActualContactEndpointFamilies (p : Pg) :=
      actual_horizontal_contact_endpoint_families (contactPatchChart p)
        (contactPatchHalfWidth p) (contactPatchHeight p) (hContactPatchHeight p)
        (hContactPatchLeftTarget p) (hContactPatchRightTarget p)
        (fun h hh hhH => (hContactPatchProducer p h hh hhH).1)
    choose contactEndpointRawLeft contactEndpointRawRight hContactEndpointRawLeftZero
      hContactEndpointRawRightZero hContactEndpointRawLeftFormula hContactEndpointRawRightFormula
      using hActualContactEndpointFamilies
    have hActualParameterizedContactPatches (p : Pg) (t : Interval) (ht : 0 < t.val) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          f 0 = contactEndpointRawLeft p t ∧ f 1 = contactEndpointRawRight p t ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      have hh : 0 < (contactPatchHeight p/2)*t.val := mul_pos (half_pos (hContactPatchHeight p)) ht
      have hhH : (contactPatchHeight p/2)*t.val < contactPatchHeight p := by
        nlinarith only [t.property.2,hContactPatchHeight p]
      obtain ⟨f,hf,hf0,hf1,hSub,hK,hSign,hAvoid,hCount⟩ :=
        hActualContactPatchRetainedRemainderAvoid p _ hh hhH
      exact ⟨f,hf,hf0.trans (hContactEndpointRawLeftFormula p t).2.symm,
        hf1.trans (hContactEndpointRawRightFormula p t).2.symm,hSub,hK,hSign,hAvoid,hCount⟩


    have hActualContactOrderedEndpointFamilies (p : Pg) :
        ∃ L R : C(Interval,S), Eopposite (L 0) 0 = actualContactLeft p ∧
          Eopposite (R 0) 0 = actualContactRight p ∧
          Eopposite (L 0) 1 = 0 ∧ Eopposite (R 0) 1 = 0 ∧
          (∀ t, L t ∈ Eopposite.source ∧ R t ∈ Eopposite.source) ∧
          ∀ t : Interval, 0 < t.val →
            ∃ f : C(Interval,S), Topology.IsEmbedding f ∧ f 0 = L t ∧ f 1 = R t ∧
              Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
              (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
              Disjoint (Set.range f) (r w).val.image ∧
              (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
                (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      have hRawLeft : Eopposite (contactEndpointRawLeft p 0) 0 =
          actualContactAxis p (-contactPatchHalfWidth p) := by
        rw [hContactEndpointRawLeftZero p]
      have hRawRight : Eopposite (contactEndpointRawRight p 0) 0 =
          actualContactAxis p (contactPatchHalfWidth p) := by
        rw [hContactEndpointRawRightZero p]
      have hRawLeftY : Eopposite (contactEndpointRawLeft p 0) 1 = 0 := by
        rw [hContactEndpointRawLeftZero p]
        exact (hContactPatchOriginalAxis p (-contactPatchHalfWidth p)
          ⟨le_rfl,by linarith only [hContactPatchHalfWidth p]⟩).2.2.1
      have hRawRightY : Eopposite (contactEndpointRawRight p 0) 1 = 0 := by
        rw [hContactEndpointRawRightZero p]
        exact (hContactPatchOriginalAxis p (contactPatchHalfWidth p)
          ⟨by linarith only [hContactPatchHalfWidth p],le_rfl⟩).2.2.1

      have hSource (t : Interval) : contactEndpointRawLeft p t ∈ Eopposite.source ∧
          contactEndpointRawRight p t ∈ Eopposite.source :=
        ⟨(hContactPatchSource p (hContactEndpointRawLeftFormula p t).1).2,
          (hContactPatchSource p (hContactEndpointRawRightFormula p t).1).2⟩
      rcases hActualContactAxisOrientation p with hl | hr
      · refine ⟨contactEndpointRawLeft p,contactEndpointRawRight p,
          hRawLeft.trans hl.1.symm,hRawRight.trans hl.2.symm,hRawLeftY,hRawRightY,hSource,?_⟩
        exact hActualParameterizedContactPatches p
      · refine ⟨contactEndpointRawRight p,contactEndpointRawLeft p,
          hRawRight.trans hr.1.symm,hRawLeft.trans hr.2.symm,hRawRightY,hRawLeftY,(fun t => (hSource t).symm),?_⟩
        intro t ht
        obtain ⟨f,hf,hf0,hf1,hSub,hK,hPos,hAvoid,hCount⟩ := hActualParameterizedContactPatches p t ht
        obtain ⟨g,hg,hRange,hg0,hg1⟩ := actual_reverse_embedded_continuous_arc f hf
        refine ⟨g,hg,hg0.trans hf1,hg1.trans hf0,?_,?_,?_,?_,?_⟩
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
    choose actualContactEndpointLeft actualContactEndpointRight hActualContactEndpointLeftZero
      hActualContactEndpointRightZero hActualContactEndpointLeftYZero hActualContactEndpointRightYZero hActualContactEndpointsSource hActualOrderedContactProducer
      using hActualContactOrderedEndpointFamilies


    have hActualContactAxisIntervalsDisjoint (p q : Pg) (hpq : p ≠ q) :
        Disjoint (Set.Icc (actualContactLeft p) (actualContactRight p))
          (Set.Icc (actualContactLeft q) (actualContactRight q)) := by
      apply Set.disjoint_left.mpr
      intro c hcp hcq
      rw [← hActualContactAxisImageEq p] at hcp
      rw [← hActualContactAxisImageEq q] at hcq
      obtain ⟨x,hx,hxc⟩ := hcp
      obtain ⟨y,hy,hyc⟩ := hcq
      have hdx := hContactPatchOriginalAxis p x hx
      have hdy := hContactPatchOriginalAxis q y hy
      have hEq : (contactPatchChart p).symm (Plane.mk x 0) =
          (contactPatchChart q).symm (Plane.mk y 0) := by
        apply Eopposite.injOn hdx.2.1 hdy.2.1
        ext i
        fin_cases i
        · exact hxc.trans hyc.symm
        · exact hdx.2.2.1.trans hdy.2.2.1.symm
      have hWp := (hContactPatchSource p ((contactPatchChart p).map_target hdx.1)).1
      have hWq := (hContactPatchSource q ((contactPatchChart q).map_target hdy.1)).1
      rw [hEq] at hWp
      exact Set.disjoint_left.mp (hWDisjoint p q hpq) hWp hWq
    have hActualContactIntervalsOrdered (p q : Pg) (hpq : contactX p < contactX q) :
        actualContactRight p < actualContactLeft q := by
      have hpL : actualContactLeft p < contactX p := by
        simpa [hActualContactAxisZero p] using hActualContactLeft p
      have hpR : contactX p < actualContactRight p := by
        simpa [hActualContactAxisZero p] using hActualContactRight p
      have hqL : actualContactLeft q < contactX q := by
        simpa [hActualContactAxisZero q] using hActualContactLeft q
      have hqR : contactX q < actualContactRight q := by
        simpa [hActualContactAxisZero q] using hActualContactRight q
      have hdis := hActualContactAxisIntervalsDisjoint p q (fun he => by rw [he] at hpq; exact lt_irrefl _ hpq)
      by_contra hn
      have hnle : actualContactLeft q ≤ actualContactRight p := le_of_not_gt hn
      let c := max (actualContactLeft p) (actualContactLeft q)
      have hcp : c ∈ Set.Icc (actualContactLeft p) (actualContactRight p) :=
        ⟨le_max_left _ _,max_le (by linarith only [hpL,hpR]) hnle⟩
      have hcq : c ∈ Set.Icc (actualContactLeft q) (actualContactRight q) :=
        ⟨le_max_right _ _,max_le (by linarith only [hpL,hpq,hqR]) (by linarith only [hqL,hqR])⟩
      exact Set.disjoint_left.mp hdis hcp hcq
    let actualContactOrder := contactCoordinates.orderEmbOfFin rfl
    have hActualSourceOrderLabels (j : Fin contactCoordinates.card) :
        ∃ p : Pg, contactX p = actualContactOrder j :=
      (hActualContactCoordinates _).mp (contactCoordinates.orderEmbOfFin_mem rfl j)
    choose actualSourceContactLabel hActualSourceContactLabel using hActualSourceOrderLabels
    have hActualSourceContactLabelInjective : Function.Injective actualSourceContactLabel := by
      intro i j hij
      apply actualContactOrder.injective
      rw [← hActualSourceContactLabel i,← hActualSourceContactLabel j,hij]
    have hActualSourceAdjacentContactGap (i j : Fin contactCoordinates.card) (hij : j.val = i.val+1) :
        Disjoint (Set.Icc (actualContactRight (actualSourceContactLabel i))
          (actualContactLeft (actualSourceContactLabel j))) (contactCoordinates : Set ℝ) := by
      have hfree := actual_finite_boundary_adjacent_contact_gap contactCoordinates i j hij
      apply hfree.mono_left
      intro x hx
      have hiR : actualContactOrder i < actualContactRight (actualSourceContactLabel i) := by
        rw [← hActualSourceContactLabel i,← hActualContactAxisZero (actualSourceContactLabel i)]
        exact hActualContactRight _
      have hjL : actualContactLeft (actualSourceContactLabel j) < actualContactOrder j := by
        rw [← hActualSourceContactLabel j,← hActualContactAxisZero (actualSourceContactLabel j)]
        exact hActualContactLeft _
      exact ⟨lt_of_lt_of_le hiR hx.1,lt_of_le_of_lt hx.2 hjL⟩


    have hActualSignedSourceGapMatching (A l rightLimit B : ℝ)
        (hA : -1 < A) (hAl : A < l) (hlr : l < rightLimit) (hrB : rightLimit < B) (hB : B < 1)
        (hgap : Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ))
        (L R : C(Interval,S))
        (hLS : ∀ t, L t ∈ Eopposite.source) (hRS : ∀ t, R t ∈ Eopposite.source)
        (hL0 : Eopposite (L 0) = Plane.mk l 0) (hR0 : Eopposite (R 0) = Plane.mk rightLimit 0)
        (hPos : ∀ t : Interval, 0 < t.val →
          0 < actualExteriorSign*Eopposite (L t) 1 ∧
          0 < actualExteriorSign*Eopposite (R t) 1) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (L t) (R t), Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ i : I, Disjoint (Set.range f) (r i).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (L t) 0+s.val*Eopposite (R t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      have hσne : actualExteriorSign ≠ 0 := by rcases hActualExteriorSign with he | he <;> simp [he]
      have hσσ : actualExteriorSign*actualExteriorSign = 1 := by
        rcases hActualExteriorSign with he | he <;> simp [he]
      let xy : Plane ≃ₜ ℝ × ℝ := {
        toFun := fun z => (z 0,actualExteriorSign*z 1)
        invFun := fun z => Plane.mk z.1 (actualExteriorSign*z.2)
        left_inv := by
          intro z
          ext i
          fin_cases i
          · rfl
          · change actualExteriorSign*(actualExteriorSign*z 1) = z 1
            rw [← mul_assoc,hσσ,one_mul]
        right_inv := by
          intro z
          apply Prod.ext
          · rfl
          · change actualExteriorSign*(actualExteriorSign*z.2) = z.2
            rw [← mul_assoc,hσσ,one_mul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let e := Eopposite.toHomeomorphSourceTarget.trans (xy.image Eopposite.target)
      let J := {i : I // i ≠ w}
      let c : J → Curve S := fun j => (r j.val).val
      have hVprod : IsOpen (xy '' Eopposite.target) := xy.isOpenMap _ Eopposite.open_target
      have haxisprod : ∀ x ∈ Set.Icc A B, ∃ y : xy '' Eopposite.target,
          y.val = (x,0) ∧ ∀ j : J, (e.symm y : S) ∉ (c j).image := by
        intro x hx
        have hxc : x ∉ contactCoordinates := fun hc => Set.disjoint_left.mp hgap hx hc
        obtain ⟨y,hyE,hyG,hEy,havoid⟩ := hActualContactFreeAxis x
          ⟨lt_of_lt_of_le hA hx.1,lt_of_le_of_lt hx.2 hB⟩ hxc
        let yU : Eopposite.source := ⟨y,hyE⟩
        refine ⟨e yU,?_,?_⟩
        · change (Eopposite y 0,actualExteriorSign*Eopposite y 1) = (x,0)
          rw [hEy]
          simp
        · intro j
          simpa only [Homeomorph.symm_apply_apply] using havoid j.val j.property
      have hgaxisprod : ∀ x : Eopposite.source,
          (x : S) ∈ (r w).val.image ↔ (e x : ℝ × ℝ).2 = 0 := by
        intro x
        change x.val ∈ (r w).val.image ↔ actualExteriorSign*Eopposite x.val 1 = 0
        rw [hOppositeAxisEntire x.val x.property,mul_eq_zero]
        simp [hσne]
      let LU : C(Interval,Eopposite.source) := ⟨fun t => ⟨L t,hLS t⟩,L.continuous.subtype_mk _⟩
      let RU : C(Interval,Eopposite.source) := ⟨fun t => ⟨R t,hRS t⟩,R.continuous.subtype_mk _⟩
      have hLU0 : (e (LU 0) : ℝ × ℝ) = (l,0) := by
        change (Eopposite (L 0) 0,actualExteriorSign*Eopposite (L 0) 1) = (l,0)
        rw [hL0]
        simp
      have hRU0 : (e (RU 0) : ℝ × ℝ) = (rightLimit,0) := by
        change (Eopposite (R 0) 0,actualExteriorSign*Eopposite (R 0) 1) = (rightLimit,0)
        rw [hR0]
        simp
      have hside : ∀ t : Interval, t ≠ 0 →
          0 < (e (LU t) : ℝ × ℝ).2 ∧ 0 < (e (RU t) : ℝ × ℝ).2 := by
        intro t ht
        exact hPos t (lt_of_le_of_ne t.property.1 (by intro he; exact ht (Subtype.ext he.symm)))
      obtain ⟨ρ,hρ,hpaths⟩ := actual_contact_gap_matching c (r w).val
        Eopposite.source (xy '' Eopposite.target) hVprod e A l rightLimit B hAl hlr hrB
        haxisprod hgaxisprod LU RU hLU0 hRU0 hside
      refine ⟨ρ,hρ,?_⟩
      intro t ht htρ
      obtain ⟨f,hEmb,hW,hJ,hCoord⟩ := hpaths t ht htρ
      have hData (s : Interval) : f s ∈ Eopposite.source ∧
          Eopposite (f s) 0 = (1-s.val)*Eopposite (L t) 0+s.val*Eopposite (R t) 0 ∧
          0 < actualExteriorSign*Eopposite (f s) 1 := by
        obtain ⟨u,hu,hEq⟩ := hCoord s
        refine ⟨hu ▸ u.property,?_,?_⟩
        · have hh := congrArg Prod.fst hEq
          change Eopposite u.val 0 = (1-s.val)*Eopposite (L t) 0+s.val*Eopposite (R t) 0 at hh
          rw [hu] at hh
          exact hh
        · have hh := congrArg Prod.snd hEq
          change actualExteriorSign*Eopposite u.val 1 =
            (1-s.val)*(actualExteriorSign*Eopposite (L t) 1)+
            s.val*(actualExteriorSign*Eopposite (R t) 1) at hh
          rw [hu] at hh
          have hP := hPos t ht
          change actualExteriorSign*Eopposite (f s) 1 =
            (1-s.val)*(actualExteriorSign*Eopposite (L t) 1)+
            s.val*(actualExteriorSign*Eopposite (R t) 1) at hh
          rw [hh]
          have hN1 := mul_nonneg (sub_nonneg.mpr s.property.2) hP.1.le
          have hN2 := mul_nonneg s.property.1 hP.2.le
          rcases eq_or_lt_of_le s.property.1 with he | hp
          · rw [← he]
            simpa using hP.1
          · exact lt_of_le_of_lt hN1 (lt_add_of_pos_right _ (mul_pos hp hP.2))
      refine ⟨f,hEmb,?_,?_,hData⟩
      · apply Set.disjoint_left.mpr
        rintro x ⟨s,rfl⟩ hxK
        have hxLarge := (hOppositeSource (hData s).1).1
        exact (hDiskInWK (interior_subset hxLarge)).2 hxK
      · intro i
        by_cases hi : i = w
        · subst i
          exact hW
        · exact hJ ⟨i,hi⟩


    have hActualAdjacentSourceGapConnector (i j : Fin contactCoordinates.card)
        (hij : j.val = i.val+1) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (actualContactEndpointRight (actualSourceContactLabel i) t)
              (actualContactEndpointLeft (actualSourceContactLabel j) t),
            Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ k : I, Disjoint (Set.range f) (r k).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (actualContactEndpointRight (actualSourceContactLabel i) t) 0+
                s.val*Eopposite (actualContactEndpointLeft (actualSourceContactLabel j) t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      let p := actualSourceContactLabel i
      let q := actualSourceContactLabel j
      have hpq : contactX p < contactX q := by
        rw [hActualSourceContactLabel i,hActualSourceContactLabel j]
        exact actualContactOrder.strictMono (by change i.val < j.val; omega)
      have hgapLR := hActualContactIntervalsOrdered p q hpq
      have hpR : contactX p < actualContactRight p := by
        simpa [hActualContactAxisZero p] using hActualContactRight p
      have hqL : actualContactLeft q < contactX q := by
        simpa [hActualContactAxisZero q] using hActualContactLeft q
      let A := (contactX p+actualContactRight p)/2
      let B := (actualContactLeft q+contactX q)/2
      have hA : -1 < A := by
        dsimp [A]
        have hb := (hActualContactCoordinateBounds p).1
        linarith only [hb,hpR]
      have hAl : A < actualContactRight p := by dsimp [A]; linarith only [hpR]
      have hrB : actualContactLeft q < B := by dsimp [B]; linarith only [hqL]
      have hB : B < 1 := by
        dsimp [B]
        have hb := (hActualContactCoordinateBounds q).2
        linarith only [hb,hqL]
      have hgap : Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ) := by
        have hf := actual_finite_boundary_adjacent_contact_gap contactCoordinates i j hij
        apply hf.mono_left
        intro x hx
        change actualContactOrder i < x ∧ x < actualContactOrder j
        rw [← hActualSourceContactLabel i,← hActualSourceContactLabel j]
        dsimp [A,B,p,q] at hx ⊢
        dsimp [p,q] at hpR hqL
        constructor <;> linarith only [hx.1,hx.2,hpR,hqL]
      apply hActualSignedSourceGapMatching A (actualContactRight p) (actualContactLeft q) B
        hA hAl hgapLR hrB hB hgap
        (actualContactEndpointRight p) (actualContactEndpointLeft q)
        (fun t => (hActualContactEndpointsSource p t).2)
        (fun t => (hActualContactEndpointsSource q t).1)
      · ext n
        fin_cases n
        · exact hActualContactEndpointRightZero p
        · exact hActualContactEndpointRightYZero p
      · ext n
        fin_cases n
        · exact hActualContactEndpointLeftZero q
        · exact hActualContactEndpointLeftYZero q
      · intro t ht
        obtain ⟨fp,hfp,hfp0,hfp1,hSubp,hKp,hSignp,hWp,hCountp⟩ := hActualOrderedContactProducer p t ht
        obtain ⟨fq,hfq,hfq0,hfq1,hSubq,hKq,hSignq,hWq,hCountq⟩ := hActualOrderedContactProducer q t ht
        exact ⟨hSignp _ ⟨1,hfp1⟩,hSignq _ ⟨0,hfq0⟩⟩


    let actualOriginalSideCoordinate (θ : ℝ) := Eopposite (γg θ) 0
    have hActualOriginalSideCoordinateContinuous :
        ContinuousOn actualOriginalSideCoordinate (Set.Icc ag zg) := by
      have hEpath := Eopposite.continuousOn.comp hγg.continuousOn
        (fun θ hθ => hGInOpposite ⟨θ,hθ,rfl⟩)
      exact (show Continuous (fun z : Plane => z 0) from by fun_prop).continuousOn.comp
        hEpath (fun _ _ => Set.mem_univ _)
    have hActualOriginalSideCoordinateInjective :
        Set.InjOn actualOriginalSideCoordinate (Set.Icc ag zg) := by
      intro θ hθ ψ hψ hEq
      have hθE := hGInOpposite ⟨θ,hθ,rfl⟩
      have hψE := hGInOpposite ⟨ψ,hψ,rfl⟩
      have hθW : γg θ ∈ (r w).val.image := hgcurve (hGAngleImage.symm ▸ ⟨θ,hθ,rfl⟩)
      have hψW : γg ψ ∈ (r w).val.image := hgcurve (hGAngleImage.symm ▸ ⟨ψ,hψ,rfl⟩)
      have hθY := (hOppositeAxisEntire _ hθE).mp hθW
      have hψY := (hOppositeAxisEntire _ hψE).mp hψW
      apply hγgInj hθ hψ
      apply Eopposite.injOn hθE hψE
      ext n
      fin_cases n
      · exact hEq
      · exact hθY.trans hψY.symm
    have hActualOriginalSideCoordinateOrder :
        StrictMonoOn actualOriginalSideCoordinate (Set.Icc ag zg) := by
      apply hActualOriginalSideCoordinateContinuous.strictMonoOn_of_injOn_Icc hagzg.le
        (hf_i := hActualOriginalSideCoordinateInjective)
      have hl : actualOriginalSideCoordinate ag = -1 := congrArg (fun z : Plane => z 0) hOppositeLeft
      have hr : actualOriginalSideCoordinate zg = 1 := congrArg (fun z : Plane => z 0) hOppositeRight
      rw [hl,hr]
      norm_num
    have hActualSourceContactParameters (p : Pg) :
        ∃ θ : ℝ, θ ∈ Set.Ioo ag zg ∧ γg θ = p.val := by
      obtain ⟨θ,hθ,hImage⟩ := hGAngleImage ▸ (hPgFacts p.val p.property).1
      have hNot (e : ℝ) (he : e = ag ∨ e = zg) : θ ≠ e := by
        intro hEq
        have hFacts := hPgFacts p.val p.property
        subst θ
        rcases he with rfl | rfl <;> rcases hGEndpointOrientation with ho | ho
        · exact hFacts.2.1 (hImage.symm.trans ho.1.symm)
        · exact hFacts.2.2.1 (hImage.symm.trans ho.2.symm)
        · exact hFacts.2.2.1 (hImage.symm.trans ho.2.symm)
        · exact hFacts.2.1 (hImage.symm.trans ho.1.symm)
      exact ⟨θ,⟨lt_of_le_of_ne hθ.1 (Ne.symm (hNot ag (Or.inl rfl))),
        lt_of_le_of_ne hθ.2 (hNot zg (Or.inr rfl))⟩,hImage⟩
    choose actualSourceContactParameter hActualSourceContactParameterInterior hActualSourceContactParameterImage
      using hActualSourceContactParameters

    have hActualContactsAvoidCornerU (p : Pg) : p.val ∉ Ucorner := by
      intro hpU
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp p.property
      have hiw : i ≠ w := by intro he; simp [he] at hi
      rw [ite_eq_right hiw] at hi
      have hMeet := hUContacts w i (Ne.symm hiw)
        ⟨hpU,(hPgFacts p.val p.property).2.2.2.1,hi.2⟩
      exact (hPgFacts p.val p.property).2.1
        (Set.mem_singleton_iff.mp hMeet)
    let actualCornerParameterU := if βgU then ag+εU*sideTU.val else zg-εU*sideTU.val
    have hActualCornerParameterU : actualCornerParameterU ∈ Set.Ioo ag zg ∧
        γg actualCornerParameterU = germU := by
      have hp : u = (r w).val.map (bg*Circle.exp ag) ∨
          u = (r w).val.map (bg*Circle.exp zg) := by
        rcases hGEndpointOrientation with ho | ho
        · exact Or.inl ho.1
        · exact Or.inr ho.1
      have hh := actual_original_corner_entering_parameter (r w).val bg (qU wgU)
        ag zg (εU*sideTU.val) (mul_pos hεU hSideTU) hSideTUShort u
        (by simpa [wgU,eU,JU] using hqU wgU) hp
      simpa only [actualCornerParameterU,βgU,γg,cw,germU] using hh
    have hActualCornerPrefixU : ∀ θ : ℝ,
        θ ∈ (if βgU then Set.Ioc ag actualCornerParameterU else Set.Ico actualCornerParameterU zg) →
          γg θ ∈ Ucorner := by
      have hqeq : (r w).val.map (qU wgU) =
          (r w).val.map (bg*Circle.exp (if βgU then ag else zg)) := by
        have hq := hqU wgU
        have hqp : (r w).val.map (qU wgU) = u := by simpa [wgU,eU,JU] using hq
        by_cases hstart : u = γg ag
        · simpa [βgU,hstart,γg,cw] using hqp.trans hstart
        · have hend : u = γg zg := by
            rcases hGEndpointOrientation with ho | ho
            · exact False.elim (hstart ho.1)
            · exact ho.1
          simpa [βgU,hstart,γg,cw] using hqp.trans hend
      have harms : ∀ t : Interval,
          (r w).val.map (qU wgU*Circle.exp (if βgU then εU*t.val else -(εU*t.val))) ∈ Ucorner := by
        intro t
        exact hEcornerUSub (by simpa [wgU,eU,JU] using hArmsUSource wgU βgU t)
      have hprefix := actual_original_corner_angular_prefix (r w).val bg (qU wgU)
        ag zg εU hεU sideTU βgU Ucorner hqeq harms
      intro θ hθ
      apply hprefix θ
      cases hβ : βgU <;>
        simpa only [actualCornerParameterU,hβ,Bool.false_eq_true,ite_false,ite_true] using hθ
    have hActualContactCornerOrderU (p : Pg) :
        if βgU then Eopposite germU 0 < contactX p else contactX p < Eopposite germU 0 := by
      let θ := actualSourceContactParameter p
      have hθ := hActualSourceContactParameterInterior p
      have hθImage := hActualSourceContactParameterImage p
      have hcorner := hActualCornerParameterU
      cases hβ : βgU
      · change contactX p < Eopposite germU 0
        by_contra hn
        have hle : actualCornerParameterU ≤ θ := by
          by_contra hnot
          have hθlt : θ < actualCornerParameterU := lt_of_not_ge hnot
          have hh := hActualOriginalSideCoordinateOrder ⟨hθ.1.le,hθ.2.le⟩
            ⟨hcorner.1.1.le,hcorner.1.2.le⟩ hθlt
          change Eopposite (γg θ) 0 < Eopposite (γg actualCornerParameterU) 0 at hh
          rw [hθImage,hcorner.2] at hh
          exact hn hh
        have hin := hActualCornerPrefixU θ (by simp only [hβ,Bool.false_eq_true,ite_false]; exact ⟨hle,hθ.2⟩)
        rw [hθImage] at hin
        exact hActualContactsAvoidCornerU p hin
      · change Eopposite germU 0 < contactX p
        by_contra hn
        have hle : θ ≤ actualCornerParameterU := by
          by_contra hnot
          have hθgt : actualCornerParameterU < θ := lt_of_not_ge hnot
          have hh := hActualOriginalSideCoordinateOrder ⟨hcorner.1.1.le,hcorner.1.2.le⟩
            ⟨hθ.1.le,hθ.2.le⟩ hθgt
          change Eopposite (γg actualCornerParameterU) 0 < Eopposite (γg θ) 0 at hh
          rw [hcorner.2,hθImage] at hh
          exact hn hh
        have hin := hActualCornerPrefixU θ (by simp only [hβ,ite_true]; exact ⟨hθ.1,hle⟩)
        rw [hθImage] at hin
        exact hActualContactsAvoidCornerU p hin

    have hActualContactsAvoidCornerZ (p : Pg) : p.val ∉ Zcorner := by
      intro hpZ
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp p.property
      have hiw : i ≠ w := by intro he; simp [he] at hi
      rw [ite_eq_right hiw] at hi
      have hMeet := hZContacts w i (Ne.symm hiw)
        ⟨hpZ,(hPgFacts p.val p.property).2.2.2.1,hi.2⟩
      exact (hPgFacts p.val p.property).2.2.1
        (Set.mem_singleton_iff.mp hMeet)
    let actualCornerParameterZ := if βgZ then ag+εZ*sideTZ.val else zg-εZ*sideTZ.val
    have hActualCornerParameterZ : actualCornerParameterZ ∈ Set.Ioo ag zg ∧
        γg actualCornerParameterZ = germZ := by
      have hp : z = (r w).val.map (bg*Circle.exp ag) ∨
          z = (r w).val.map (bg*Circle.exp zg) := by
        rcases hGEndpointOrientation with ho | ho
        · exact Or.inr ho.2
        · exact Or.inl ho.2
      have hh := actual_original_corner_entering_parameter (r w).val bg (qZ wgZ)
        ag zg (εZ*sideTZ.val) (mul_pos hεZ hSideTZ) hSideTZShort z
        (by simpa [wgZ,eZ,JZ] using hqZ wgZ) hp
      simpa only [actualCornerParameterZ,βgZ,γg,cw,germZ] using hh
    have hActualCornerPrefixZ : ∀ θ : ℝ,
        θ ∈ (if βgZ then Set.Ioc ag actualCornerParameterZ else Set.Ico actualCornerParameterZ zg) →
          γg θ ∈ Zcorner := by
      have hqeq : (r w).val.map (qZ wgZ) =
          (r w).val.map (bg*Circle.exp (if βgZ then ag else zg)) := by
        have hq := hqZ wgZ
        have hqp : (r w).val.map (qZ wgZ) = z := by simpa [wgZ,eZ,JZ] using hq
        by_cases hstart : z = γg ag
        · simpa [βgZ,hstart,γg,cw] using hqp.trans hstart
        · have hend : z = γg zg := by
            rcases hGEndpointOrientation with ho | ho
            · exact ho.2
            · exact False.elim (hstart ho.2)
          simpa [βgZ,hstart,γg,cw] using hqp.trans hend
      have harms : ∀ t : Interval,
          (r w).val.map (qZ wgZ*Circle.exp (if βgZ then εZ*t.val else -(εZ*t.val))) ∈ Zcorner := by
        intro t
        exact hEcornerZSub (by simpa [wgZ,eZ,JZ] using hArmsZSource wgZ βgZ t)
      have hprefix := actual_original_corner_angular_prefix (r w).val bg (qZ wgZ)
        ag zg εZ hεZ sideTZ βgZ Zcorner hqeq harms
      intro θ hθ
      apply hprefix θ
      cases hβ : βgZ <;>
        simpa only [actualCornerParameterZ,hβ,Bool.false_eq_true,ite_false,ite_true] using hθ
    have hActualContactCornerOrderZ (p : Pg) :
        if βgZ then Eopposite germZ 0 < contactX p else contactX p < Eopposite germZ 0 := by
      let θ := actualSourceContactParameter p
      have hθ := hActualSourceContactParameterInterior p
      have hθImage := hActualSourceContactParameterImage p
      have hcorner := hActualCornerParameterZ
      cases hβ : βgZ
      · change contactX p < Eopposite germZ 0
        by_contra hn
        have hle : actualCornerParameterZ ≤ θ := by
          by_contra hnot
          have hθlt : θ < actualCornerParameterZ := lt_of_not_ge hnot
          have hh := hActualOriginalSideCoordinateOrder ⟨hθ.1.le,hθ.2.le⟩
            ⟨hcorner.1.1.le,hcorner.1.2.le⟩ hθlt
          change Eopposite (γg θ) 0 < Eopposite (γg actualCornerParameterZ) 0 at hh
          rw [hθImage,hcorner.2] at hh
          exact hn hh
        have hin := hActualCornerPrefixZ θ (by simp only [hβ,Bool.false_eq_true,ite_false]; exact ⟨hle,hθ.2⟩)
        rw [hθImage] at hin
        exact hActualContactsAvoidCornerZ p hin
      · change Eopposite germZ 0 < contactX p
        by_contra hn
        have hle : θ ≤ actualCornerParameterZ := by
          by_contra hnot
          have hθgt : actualCornerParameterZ < θ := lt_of_not_ge hnot
          have hh := hActualOriginalSideCoordinateOrder ⟨hcorner.1.1.le,hcorner.1.2.le⟩
            ⟨hθ.1.le,hθ.2.le⟩ hθgt
          change Eopposite (γg actualCornerParameterZ) 0 < Eopposite (γg θ) 0 at hh
          rw [hcorner.2,hθImage] at hh
          exact hn hh
        have hin := hActualCornerPrefixZ θ (by simp only [hβ,ite_true]; exact ⟨hθ.1,hle⟩)
        rw [hθImage] at hin
        exact hActualContactsAvoidCornerZ p hin


    have hActualOriginalSideEndsNe : γg ag ≠ γg zg := by
      intro he
      exact (ne_of_lt hagzg) (hγgInj ⟨le_rfl,hagzg.le⟩ ⟨hagzg.le,le_rfl⟩ he)
    have hActualCornerSidesOpposite : βgZ = !βgU := by
      rcases hGEndpointOrientation with ho | ho <;>
        simp [βgU,βgZ,ho.1,ho.2,hActualOriginalSideEndsNe,hActualOriginalSideEndsNe.symm]
    have hActualContactsBetweenCornerGerms (p : Pg) :
        min (Eopposite germU 0) (Eopposite germZ 0) < contactX p ∧
        contactX p < max (Eopposite germU 0) (Eopposite germZ 0) := by
      have hU := hActualContactCornerOrderU p
      have hZ := hActualContactCornerOrderZ p
      cases hβ : βgU
      · have hzβ : βgZ = true := by rw [hActualCornerSidesOpposite,hβ]; rfl
        simp only [hβ,hzβ,Bool.false_eq_true,ite_false,ite_true] at hU hZ
        exact ⟨lt_of_le_of_lt (min_le_right _ _) hZ,lt_of_lt_of_le hU (le_max_left _ _)⟩
      · have hzβ : βgZ = false := by rw [hActualCornerSidesOpposite,hβ]; rfl
        simp only [hβ,hzβ,Bool.false_eq_true,ite_false,ite_true] at hU hZ
        exact ⟨lt_of_le_of_lt (min_le_left _ _) hU,lt_of_lt_of_le hZ (le_max_right _ _)⟩
    have hActualCornerGermParameterOrder :
        if βgU then actualCornerParameterU < actualCornerParameterZ
          else actualCornerParameterZ < actualCornerParameterU := by
      have hGU : germU ∈ Ucorner := hEcornerUSub (hFUSource ▸ hGermUSource)
      have hGZ : germZ ∈ Zcorner := hEcornerZSub (hFZSource ▸ hGermZSource)
      cases hβ : βgU
      · change actualCornerParameterZ < actualCornerParameterU
        have hzβ : βgZ = true := by rw [hActualCornerSidesOpposite,hβ]; rfl
        by_contra hn
        have hin := hActualCornerPrefixZ actualCornerParameterU (by
          simp only [hzβ,ite_true]
          exact ⟨hActualCornerParameterU.1.1,le_of_not_gt hn⟩)
        rw [hActualCornerParameterU.2] at hin
        exact Set.disjoint_left.mp hCornersDisjoint hGU hin
      · change actualCornerParameterU < actualCornerParameterZ
        by_contra hn
        have hin := hActualCornerPrefixU actualCornerParameterZ (by
          simp only [hβ,ite_true]
          exact ⟨hActualCornerParameterZ.1.1,le_of_not_gt hn⟩)
        rw [hActualCornerParameterZ.2] at hin
        exact Set.disjoint_left.mp hCornersDisjoint hin hGZ
    have hActualCornerGermCoordinateOrder :
        if βgU then Eopposite germU 0 < Eopposite germZ 0
          else Eopposite germZ 0 < Eopposite germU 0 := by
      have hp := hActualCornerGermParameterOrder
      cases hβ : βgU
      · simp only [hβ,Bool.false_eq_true,ite_false] at hp ⊢
        have hh := hActualOriginalSideCoordinateOrder
          ⟨hActualCornerParameterZ.1.1.le,hActualCornerParameterZ.1.2.le⟩
          ⟨hActualCornerParameterU.1.1.le,hActualCornerParameterU.1.2.le⟩ hp
        change Eopposite (γg actualCornerParameterZ) 0 < Eopposite (γg actualCornerParameterU) 0 at hh
        rwa [hActualCornerParameterZ.2,hActualCornerParameterU.2] at hh
      · simp only [hβ,ite_true] at hp ⊢
        have hh := hActualOriginalSideCoordinateOrder
          ⟨hActualCornerParameterU.1.1.le,hActualCornerParameterU.1.2.le⟩
          ⟨hActualCornerParameterZ.1.1.le,hActualCornerParameterZ.1.2.le⟩ hp
        change Eopposite (γg actualCornerParameterU) 0 < Eopposite (γg actualCornerParameterZ) 0 at hh
        rwa [hActualCornerParameterU.2,hActualCornerParameterZ.2] at hh
    let actualContactSlotLeft (p : Pg) := max (actualContactLeft p)
      (min (Eopposite germU 0) (Eopposite germZ 0))
    let actualContactSlotRight (p : Pg) := min (actualContactRight p)
      (max (Eopposite germU 0) (Eopposite germZ 0))
    have hActualContactSlotBounds (p : Pg) :
        actualContactSlotLeft p < contactX p ∧ contactX p < actualContactSlotRight p := by
      have hLeft : actualContactLeft p < contactX p := by
        simpa [hActualContactAxisZero p] using hActualContactLeft p
      have hRight : contactX p < actualContactRight p := by
        simpa [hActualContactAxisZero p] using hActualContactRight p
      exact ⟨max_lt hLeft (hActualContactsBetweenCornerGerms p).1,
        lt_min hRight (hActualContactsBetweenCornerGerms p).2⟩
    have hActualCroppedSourceWidths (p : Pg) : ∃ d : ℝ, 0 < d ∧ d < contactPatchHalfWidth p ∧
        ∀ x ∈ Set.Icc (-d) d,
          actualContactSlotLeft p < actualContactAxis p x ∧
          actualContactAxis p x < actualContactSlotRight p := by
      apply actual_contact_axis_choose_inner_width (actualContactAxis p) (contactPatchHalfWidth p)
        (actualContactSlotLeft p) (actualContactSlotRight p) (hContactPatchHalfWidth p)
        (hActualContactAxisContinuous p)
      · rw [hActualContactAxisZero p]
        exact (hActualContactSlotBounds p).1
      · rw [hActualContactAxisZero p]
        exact (hActualContactSlotBounds p).2
    choose actualCroppedWidth hActualCroppedWidth hActualCroppedWidthBound hActualCroppedAxisSlot
      using hActualCroppedSourceWidths
    have hActualCroppedContactProducer (p : Pg) (h : ℝ) (hh : 0 < h) (hhH : h < contactPatchHeight p) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          Set.range f = (contactPatchChart p).symm ''
            segment ℝ (Plane.mk (-actualCroppedWidth p) h) (Plane.mk (actualCroppedWidth p) h) ∧
          f 0 = (contactPatchChart p).symm (Plane.mk (-actualCroppedWidth p) h) ∧
          f 1 = (contactPatchChart p).symm (Plane.mk (actualCroppedWidth p) h) ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      have hSubPlane := actual_horizontal_contact_subsegment (contactPatchHalfWidth p)
        (actualCroppedWidth p) h (hContactPatchHalfWidth p) (hActualCroppedWidth p)
        (hActualCroppedWidthBound p)
      have hTarget := hSubPlane.trans (hContactPatchProducer p h hh hhH).1
      obtain ⟨old,hOld,hOldRange,hOld0,hOld1,hOldSub,hOldPos,hOldW,hOldCounts⟩ :=
        (hContactPatchProducer p h hh hhH).2
      obtain ⟨f,hf,hRange,hf0,hf1⟩ := hHorizontalChartArc (contactPatchChart p)
        (actualCroppedWidth p) h (hActualCroppedWidth p) hTarget
      have hSub : Set.range f ⊆ Set.range old := by
        rw [hRange,hOldRange]
        exact Set.image_mono hSubPlane
      refine ⟨f,hf,hRange,hf0,hf1,hSub.trans hOldSub,
        (hActualInteriorSupportAvoidK p).mono_left (hSub.trans hOldSub),?_,hOldW.mono_left hSub,?_⟩
      · intro x hx
        have hPos := hOldPos x (hSub hx)
        rwa [hActualExteriorChartFormula x] at hPos
      · intro i hi
        have hOld := hOldCounts i hi
        have hContactSub : Set.range f ∩ (r i).val.image ⊆ Set.range old ∩ (r i).val.image :=
          fun x hx => ⟨hSub hx.1,hx.2⟩
        exact ⟨hOld.1.subset hContactSub,(Set.ncard_le_ncard hContactSub hOld.1).trans hOld.2⟩

    have hActualCroppedContactAxisTarget (p : Pg) (x : ℝ)
        (hx : x ∈ Set.Icc (-actualCroppedWidth p) (actualCroppedWidth p)) :
        Plane.mk x 0 ∈ (contactPatchChart p).target := by
      exact (hContactPatchOriginalAxis p x
        ⟨by linarith only [hx.1,hActualCroppedWidthBound p],
          by linarith only [hx.2,hActualCroppedWidthBound p]⟩).1
    have hActualCroppedContactEndpointFamilies (p : Pg) :=
      actual_horizontal_contact_endpoint_families (contactPatchChart p)
        (actualCroppedWidth p) (contactPatchHeight p) (hContactPatchHeight p)
        (hActualCroppedContactAxisTarget p _ ⟨le_rfl,by linarith only [hActualCroppedWidth p]⟩)
        (hActualCroppedContactAxisTarget p _ ⟨by linarith only [hActualCroppedWidth p],le_rfl⟩)
        (fun h hh hhH =>
          (actual_horizontal_contact_subsegment (contactPatchHalfWidth p)
            (actualCroppedWidth p) h (hContactPatchHalfWidth p) (hActualCroppedWidth p)
            (hActualCroppedWidthBound p)).trans (hContactPatchProducer p h hh hhH).1)
    choose croppedEndpointRawLeft croppedEndpointRawRight hCroppedEndpointRawLeftZero
      hCroppedEndpointRawRightZero hCroppedEndpointRawLeftFormula hCroppedEndpointRawRightFormula
      using hActualCroppedContactEndpointFamilies
    have hActualCroppedParameterizedContactProducer (p : Pg) (t : Interval) (ht : 0 < t.val) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          f 0 = croppedEndpointRawLeft p t ∧ f 1 = croppedEndpointRawRight p t ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      have hh : 0 < (contactPatchHeight p/2)*t.val := mul_pos (half_pos (hContactPatchHeight p)) ht
      have hhH : (contactPatchHeight p/2)*t.val < contactPatchHeight p := by
        nlinarith only [t.property.2,hContactPatchHeight p]
      obtain ⟨f,hf,hRange,hf0,hf1,hSub,hK,hSign,hAvoid,hCount⟩ :=
        hActualCroppedContactProducer p _ hh hhH
      exact ⟨f,hf,hf0.trans (hCroppedEndpointRawLeftFormula p t).2.symm,
        hf1.trans (hCroppedEndpointRawRightFormula p t).2.symm,hSub,hK,hSign,hAvoid,hCount⟩

    have hActualCroppedAxisContinuous (p : Pg) : ContinuousOn (actualContactAxis p)
        (Set.Icc (-actualCroppedWidth p) (actualCroppedWidth p)) :=
      (hActualContactAxisContinuous p).mono (fun x hx =>
        ⟨by linarith only [hx.1,hActualCroppedWidthBound p],
          by linarith only [hx.2,hActualCroppedWidthBound p]⟩)
    have hActualCroppedAxisInjective (p : Pg) : Set.InjOn (actualContactAxis p)
        (Set.Icc (-actualCroppedWidth p) (actualCroppedWidth p)) := by
      intro x hx y hy hxy
      exact hActualContactAxisInjective p
        ⟨by linarith only [hx.1,hActualCroppedWidthBound p],by linarith only [hx.2,hActualCroppedWidthBound p]⟩
        ⟨by linarith only [hy.1,hActualCroppedWidthBound p],by linarith only [hy.2,hActualCroppedWidthBound p]⟩ hxy
    have hActualCroppedAxisImage (p : Pg) :=
      actual_continuous_injective_axis_image (actualContactAxis p) (actualCroppedWidth p)
        (hActualCroppedWidth p) (hActualCroppedAxisContinuous p) (hActualCroppedAxisInjective p)
    choose actualCroppedLeft actualCroppedRight hActualCroppedLeft hActualCroppedRight
      hActualCroppedAxisImageEq hActualCroppedAxisOrientation using hActualCroppedAxisImage
    have hActualCroppedOrderedEndpointFamilies (p : Pg) :
        ∃ L R : C(Interval,S), Eopposite (L 0) 0 = actualCroppedLeft p ∧
          Eopposite (R 0) 0 = actualCroppedRight p ∧
          Eopposite (L 0) 1 = 0 ∧ Eopposite (R 0) 1 = 0 ∧
          (∀ t, L t ∈ Eopposite.source ∧ R t ∈ Eopposite.source) ∧
          ∀ t : Interval, 0 < t.val →
            ∃ f : C(Interval,S), Topology.IsEmbedding f ∧ f 0 = L t ∧ f 1 = R t ∧
              Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
              (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
              Disjoint (Set.range f) (r w).val.image ∧
              (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
                (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      have hRawLeft : Eopposite (croppedEndpointRawLeft p 0) 0 =
          actualContactAxis p (-actualCroppedWidth p) := by
        rw [hCroppedEndpointRawLeftZero p]
      have hRawRight : Eopposite (croppedEndpointRawRight p 0) 0 =
          actualContactAxis p (actualCroppedWidth p) := by
        rw [hCroppedEndpointRawRightZero p]
      have hRawLeftY : Eopposite (croppedEndpointRawLeft p 0) 1 = 0 := by
        rw [hCroppedEndpointRawLeftZero p]
        exact (hContactPatchOriginalAxis p (-actualCroppedWidth p)
          ⟨by linarith only [hActualCroppedWidthBound p],by linarith only [hActualCroppedWidth p,hContactPatchHalfWidth p]⟩).2.2.1
      have hRawRightY : Eopposite (croppedEndpointRawRight p 0) 1 = 0 := by
        rw [hCroppedEndpointRawRightZero p]
        exact (hContactPatchOriginalAxis p (actualCroppedWidth p)
          ⟨by linarith only [hActualCroppedWidth p,hContactPatchHalfWidth p],(hActualCroppedWidthBound p).le⟩).2.2.1

      have hSource (t : Interval) : croppedEndpointRawLeft p t ∈ Eopposite.source ∧
          croppedEndpointRawRight p t ∈ Eopposite.source :=
        ⟨(hContactPatchSource p (hCroppedEndpointRawLeftFormula p t).1).2,
          (hContactPatchSource p (hCroppedEndpointRawRightFormula p t).1).2⟩
      rcases hActualCroppedAxisOrientation p with hl | hr
      · refine ⟨croppedEndpointRawLeft p,croppedEndpointRawRight p,
          hRawLeft.trans hl.1.symm,hRawRight.trans hl.2.symm,hRawLeftY,hRawRightY,hSource,?_⟩
        exact hActualCroppedParameterizedContactProducer p
      · refine ⟨croppedEndpointRawRight p,croppedEndpointRawLeft p,
          hRawRight.trans hr.1.symm,hRawLeft.trans hr.2.symm,hRawRightY,hRawLeftY,(fun t => (hSource t).symm),?_⟩
        intro t ht
        obtain ⟨f,hf,hf0,hf1,hSub,hK,hPos,hAvoid,hCount⟩ := hActualCroppedParameterizedContactProducer p t ht
        obtain ⟨g,hg,hRange,hg0,hg1⟩ := actual_reverse_embedded_continuous_arc f hf
        refine ⟨g,hg,hg0.trans hf1,hg1.trans hf0,?_,?_,?_,?_,?_⟩
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
    choose actualCroppedEndpointLeft actualCroppedEndpointRight hActualCroppedEndpointLeftZero
      hActualCroppedEndpointRightZero hActualCroppedEndpointLeftYZero hActualCroppedEndpointRightYZero hActualCroppedEndpointsSource hActualCroppedOrderedContactProducer
      using hActualCroppedOrderedEndpointFamilies


    have hActualCroppedIntervalSubset (p : Pg) :
        Set.Icc (actualCroppedLeft p) (actualCroppedRight p) ⊆
          Set.Icc (actualContactLeft p) (actualContactRight p) := by
      rw [←hActualCroppedAxisImageEq p,←hActualContactAxisImageEq p]
      exact Set.image_mono (fun x hx =>
        ⟨by linarith only [hx.1,hActualCroppedWidthBound p],
          by linarith only [hx.2,hActualCroppedWidthBound p]⟩)
    have hActualCroppedLimitsInsideSlots (p : Pg) :
        actualContactSlotLeft p < actualCroppedLeft p ∧
        actualCroppedRight p < actualContactSlotRight p := by
      have hl : actualCroppedLeft p ∈ actualContactAxis p ''
          Set.Icc (-actualCroppedWidth p) (actualCroppedWidth p) := by
        rw [hActualCroppedAxisImageEq p]
        exact ⟨le_rfl,(hActualCroppedLeft p).le.trans (hActualCroppedRight p).le⟩
      have hr : actualCroppedRight p ∈ actualContactAxis p ''
          Set.Icc (-actualCroppedWidth p) (actualCroppedWidth p) := by
        rw [hActualCroppedAxisImageEq p]
        exact ⟨(hActualCroppedLeft p).le.trans (hActualCroppedRight p).le,le_rfl⟩
      obtain ⟨x,hx,hxeq⟩ := hl
      obtain ⟨y,hy,hyeq⟩ := hr
      exact ⟨hxeq ▸ (hActualCroppedAxisSlot p x hx).1,
        hyeq ▸ (hActualCroppedAxisSlot p y hy).2⟩
    have hActualCroppedLimitsBetweenCornerGerms (p : Pg) :
        min (Eopposite germU 0) (Eopposite germZ 0) < actualCroppedLeft p ∧
        actualCroppedRight p < max (Eopposite germU 0) (Eopposite germZ 0) :=
      ⟨lt_of_le_of_lt (le_max_right _ _) (hActualCroppedLimitsInsideSlots p).1,
        lt_of_lt_of_le (hActualCroppedLimitsInsideSlots p).2 (min_le_right _ _)⟩
    have hActualCroppedLimitsOrdered (p q : Pg) (hpq : contactX p < contactX q) :
        actualCroppedRight p < actualCroppedLeft q := by
      have hp := hActualCroppedIntervalSubset p
        (show actualCroppedRight p ∈ Set.Icc (actualCroppedLeft p) (actualCroppedRight p) from
          ⟨(hActualCroppedLeft p).le.trans (hActualCroppedRight p).le,le_rfl⟩)
      have hq := hActualCroppedIntervalSubset q
        (show actualCroppedLeft q ∈ Set.Icc (actualCroppedLeft q) (actualCroppedRight q) from
          ⟨le_rfl,(hActualCroppedLeft q).le.trans (hActualCroppedRight q).le⟩)
      exact lt_of_le_of_lt hp.2 (lt_of_lt_of_le (hActualContactIntervalsOrdered p q hpq) hq.1)
    have hActualCroppedAdjacentSourceGapConnector (i j : Fin contactCoordinates.card)
        (hij : j.val = i.val+1) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (actualCroppedEndpointRight (actualSourceContactLabel i) t)
              (actualCroppedEndpointLeft (actualSourceContactLabel j) t),
            Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ k : I, Disjoint (Set.range f) (r k).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (actualCroppedEndpointRight (actualSourceContactLabel i) t) 0+
                s.val*Eopposite (actualCroppedEndpointLeft (actualSourceContactLabel j) t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      let p := actualSourceContactLabel i
      let q := actualSourceContactLabel j
      have hpq : contactX p < contactX q := by
        rw [hActualSourceContactLabel i,hActualSourceContactLabel j]
        exact actualContactOrder.strictMono (by change i.val < j.val; omega)
      have hgapLR := hActualCroppedLimitsOrdered p q hpq
      have hpR : contactX p < actualCroppedRight p := by
        simpa [hActualContactAxisZero p] using hActualCroppedRight p
      have hqL : actualCroppedLeft q < contactX q := by
        simpa [hActualContactAxisZero q] using hActualCroppedLeft q
      let A := (contactX p+actualCroppedRight p)/2
      let B := (actualCroppedLeft q+contactX q)/2
      have hA : -1 < A := by
        dsimp [A]
        have hb := (hActualContactCoordinateBounds p).1
        linarith only [hb,hpR]
      have hAl : A < actualCroppedRight p := by dsimp [A]; linarith only [hpR]
      have hrB : actualCroppedLeft q < B := by dsimp [B]; linarith only [hqL]
      have hB : B < 1 := by
        dsimp [B]
        have hb := (hActualContactCoordinateBounds q).2
        linarith only [hb,hqL]
      have hgap : Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ) := by
        have hf := actual_finite_boundary_adjacent_contact_gap contactCoordinates i j hij
        apply hf.mono_left
        intro x hx
        change actualContactOrder i < x ∧ x < actualContactOrder j
        rw [← hActualSourceContactLabel i,← hActualSourceContactLabel j]
        dsimp [A,B,p,q] at hx ⊢
        dsimp [p,q] at hpR hqL
        constructor <;> linarith only [hx.1,hx.2,hpR,hqL]
      apply hActualSignedSourceGapMatching A (actualCroppedRight p) (actualCroppedLeft q) B
        hA hAl hgapLR hrB hB hgap
        (actualCroppedEndpointRight p) (actualCroppedEndpointLeft q)
        (fun t => (hActualCroppedEndpointsSource p t).2)
        (fun t => (hActualCroppedEndpointsSource q t).1)
      · ext n
        fin_cases n
        · exact hActualCroppedEndpointRightZero p
        · exact hActualCroppedEndpointRightYZero p
      · ext n
        fin_cases n
        · exact hActualCroppedEndpointLeftZero q
        · exact hActualCroppedEndpointLeftYZero q
      · intro t ht
        obtain ⟨fp,hfp,hfp0,hfp1,hSubp,hKp,hSignp,hWp,hCountp⟩ := hActualCroppedOrderedContactProducer p t ht
        obtain ⟨fq,hfq,hfq0,hfq1,hSubq,hKq,hSignq,hWq,hCountq⟩ := hActualCroppedOrderedContactProducer q t ht
        exact ⟨hSignp _ ⟨1,hfp1⟩,hSignq _ ⟨0,hfq0⟩⟩


    have hActualSelectedEndsNe : γ a ≠ γ zangle := by
      intro he
      rcases hSelectedEndpointOrientation with ho | ho
      · exact huz (ho.1.trans (he.trans ho.2.symm))
      · exact huz (ho.1.trans (he.symm.trans ho.2.symm))
    have hActualSelectedCornerSidesOpposite : βZ = !βU := by
      rcases hSelectedEndpointOrientation with ho | ho <;>
        simp [βU,βZ,ho.1,ho.2,hActualSelectedEndsNe,hActualSelectedEndsNe.symm]
    have hActualSelectedExternalStartU :
        cornerArcU 0 = γ (if βU then a-εU*tU.val else zangle+εU*tU.val) := by
      have hp : u = (r v).val.map (b*Circle.exp a) ∨
          u = (r v).val.map (b*Circle.exp zangle) := by
        rcases hSelectedEndpointOrientation with ho | ho
        · exact Or.inl ho.1
        · exact Or.inr ho.1
      have hh := actual_original_corner_external_parameter (r v).val b
        (qU (eU ⟨v,huSelected⟩)) a zangle (εU*tU.val) u
        (by simpa [eU,JU] using hqU (eU ⟨v,huSelected⟩)) hp
      rw [hCornerStartU,hStartParameterU]
      simpa only [γ,βU] using hh.symm
    have hActualSelectedExternalStartZ :
        cornerArcZ 0 = γ (if βZ then a-εZ*tZ.val else zangle+εZ*tZ.val) := by
      have hp : z = (r v).val.map (b*Circle.exp a) ∨
          z = (r v).val.map (b*Circle.exp zangle) := by
        rcases hSelectedEndpointOrientation with ho | ho
        · exact Or.inr ho.2
        · exact Or.inl ho.2
      have hh := actual_original_corner_external_parameter (r v).val b
        (qZ (eZ ⟨v,hzSelected⟩)) a zangle (εZ*tZ.val) z
        (by simpa [eZ,JZ] using hqZ (eZ ⟨v,hzSelected⟩)) hp
      rw [hCornerStartZ,hStartParameterZ]
      simpa only [γ,βZ] using hh.symm
    have hActualExternalQuarterU : εU*tU.val < gap/4 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2*εU)).mp
        (min_le_left (gap/(2*εU)) 1)
      have hs := mul_lt_mul_of_pos_left htUShort hεU
      dsimp [τU] at hs
      nlinarith only [hh,hs]
    have hActualExternalQuarterZ : εZ*tZ.val < gap/4 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2*εZ)).mp
        (min_le_left (gap/(2*εZ)) 1)
      have hs := mul_lt_mul_of_pos_left htZShort hεZ
      dsimp [τZ] at hs
      nlinarith only [hh,hs]
    let actualSelectedExtensionLeft := a-(if βU then εU*tU.val else εZ*tZ.val)
    let actualSelectedExtensionRight := zangle+(if βU then εZ*tZ.val else εU*tU.val)
    have hActualSelectedExtensionBounds :
        actualSelectedExtensionLeft < a ∧ zangle < actualSelectedExtensionRight := by
      cases hβ : βU <;>
        simp only [actualSelectedExtensionLeft,actualSelectedExtensionRight,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;>
        constructor <;> linarith only [mul_pos hεU htUPos,mul_pos hεZ htZPos]
    have hActualSelectedExtensionLength :
        actualSelectedExtensionRight-actualSelectedExtensionLeft < 2*Real.pi := by
      cases hβ : βU <;>
        simp only [actualSelectedExtensionLeft,actualSelectedExtensionRight,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;>
        dsimp [gap] at hActualExternalQuarterU hActualExternalQuarterZ <;>
        linarith only [hActualExternalQuarterU,hActualExternalQuarterZ,hlenangle]
    obtain ⟨actualExtendedOldArc,actualRetainedRemainder,
      hActualExtendedOldArc,hActualRetainedRemainder,hActualExtendedOldArcRange,
      hActualRetainedRemainderRange,hActualSelectedExactDecomposition,
      hActualSelectedRemainderMeet,hActualRetainedRemainderEnd⟩ :=
      actual_original_circle_subarc_and_retained_remainder (r v).val b
        actualSelectedExtensionLeft actualSelectedExtensionRight
        ((hActualSelectedExtensionBounds.1.trans hazangle).trans hActualSelectedExtensionBounds.2)
        hActualSelectedExtensionLength
    have hActualSelectedExternalStartsOrdered :
        (if βU then cornerArcU 0 else cornerArcZ 0) = γ actualSelectedExtensionLeft ∧
        (if βU then cornerArcZ 0 else cornerArcU 0) = γ actualSelectedExtensionRight := by
      rw [hActualSelectedExternalStartU,hActualSelectedExternalStartZ,hActualSelectedCornerSidesOpposite]
      cases hβ : βU <;>
        simp only [actualSelectedExtensionLeft,actualSelectedExtensionRight,hβ,
          Bool.false_eq_true,Bool.not_false,Bool.not_true,ite_false,ite_true] <;>
        constructor <;> trivial
    have hActualSourceContactLabelSurjective : Function.Surjective actualSourceContactLabel := by
      intro p
      have hm : contactX p ∈ Set.range actualContactOrder := by
        rw [Finset.range_orderEmbOfFin]
        exact (hActualContactCoordinates _).mpr ⟨p,rfl⟩
      obtain ⟨i,hi⟩ := hm
      exact ⟨i,hContactXInjective ((hActualSourceContactLabel i).trans hi)⟩
    have hActualFirstContactLeast (i : Fin contactCoordinates.card) (hi : i.val = 0)
        (p : Pg) : contactX (actualSourceContactLabel i) ≤ contactX p := by
      obtain ⟨j,rfl⟩ := hActualSourceContactLabelSurjective p
      rw [hActualSourceContactLabel i,hActualSourceContactLabel j]
      exact actualContactOrder.monotone (by change i.val ≤ j.val; omega)
    have hActualLastContactGreatest (i : Fin contactCoordinates.card)
        (hi : i.val+1 = contactCoordinates.card) (p : Pg) :
        contactX p ≤ contactX (actualSourceContactLabel i) := by
      obtain ⟨j,rfl⟩ := hActualSourceContactLabelSurjective p
      rw [hActualSourceContactLabel i,hActualSourceContactLabel j]
      exact actualContactOrder.monotone (by change j.val ≤ i.val; omega)
    have hActualFirstContactFreeInterval (i : Fin contactCoordinates.card) (hi : i.val = 0)
        (A B : ℝ) (hB : B < contactX (actualSourceContactLabel i)) :
        Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ) := by
      apply Set.disjoint_left.mpr
      intro x hx hc
      obtain ⟨p,hp⟩ := (hActualContactCoordinates x).mp hc
      have hh := hActualFirstContactLeast i hi p
      rw [hp] at hh
      linarith only [hh,hx.2,hB]
    have hActualLastContactFreeInterval (i : Fin contactCoordinates.card)
        (hi : i.val+1 = contactCoordinates.card) (A B : ℝ)
        (hA : contactX (actualSourceContactLabel i) < A) :
        Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ) := by
      apply Set.disjoint_left.mpr
      intro x hx hc
      obtain ⟨p,hp⟩ := (hActualContactCoordinates x).mp hc
      have hh := hActualLastContactGreatest i hi p
      rw [hp] at hh
      linarith only [hh,hx.1,hA]
    have hActualCornerEndpointFullProducerU (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧ Set.range arc = nearCornerSurfaceU (endpointScaleU*t.val) ∧
          arc 0 = cornerArcU 0 ∧
          arc 1 = actualCornerEndpointU t ∧ Set.range arc ⊆ Ucorner ∧
          Set.range arc ∩ (r v).val.image = {cornerArcU 0} ∧
          Disjoint (Set.range arc) (r w).val.image ∧
          Set.range arc ⊆ (Set.range d)ᶜ ∧ Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if u ∈ (r i).val.image then 1 else 0) := by
      have hε : 0 < endpointScaleU*t.val := mul_pos hEndpointScaleU ht
      have hεsmall : endpointScaleU*t.val < cornerToleranceU :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleU.le t.property.2) hEndpointScaleBoundU
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hOut,hK,hCounts⟩ :=
        hActualExteriorCornerProducerU (endpointScaleU*t.val) hε hεsmall
      refine ⟨arc,hEmb,hRange,hStart,hEnd.trans (hActualCornerEndpointUCoordinates t).2.2.symm,
        (by rw [hRange]; exact hNearCornerSubU _ hε hεsmall),?_,?_,hOut,hK,hCounts⟩
      · have hStartChart : arc 0 = FU.symm (Plane.mk (-δU) 0) := hStart.trans hCornerStartU
        have hm := actual_signed_chart_connector_selected_meet (r v).val FU δU
          (FU germU 0-endpointScaleU*t.val) (FU germU 1) ρU hGermUY arc hRange hStartChart
          (hStart.symm ▸ hCornerStartCurveU) (hNearCornerCoreU _ hε hεsmall)
          (by simpa [eU] using hFUAxis)
        rwa [hStart] at hm
      · rw [hRange]
        exact hNearCornerOppositeAvoidU _ hε hεsmall
    have hActualCornerEndpointFullProducerZ (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧ Set.range arc = nearCornerSurfaceZ (endpointScaleZ*t.val) ∧
          arc 0 = cornerArcZ 0 ∧
          arc 1 = actualCornerEndpointZ t ∧ Set.range arc ⊆ Zcorner ∧
          Set.range arc ∩ (r v).val.image = {cornerArcZ 0} ∧
          Disjoint (Set.range arc) (r w).val.image ∧
          Set.range arc ⊆ (Set.range d)ᶜ ∧ Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if z ∈ (r i).val.image then 1 else 0) := by
      have hε : 0 < endpointScaleZ*t.val := mul_pos hEndpointScaleZ ht
      have hεsmall : endpointScaleZ*t.val < cornerToleranceZ :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleZ.le t.property.2) hEndpointScaleBoundZ
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hOut,hK,hCounts⟩ :=
        hActualExteriorCornerProducerZ (endpointScaleZ*t.val) hε hεsmall
      refine ⟨arc,hEmb,hRange,hStart,hEnd.trans (hActualCornerEndpointZCoordinates t).2.2.symm,
        (by rw [hRange]; exact hNearCornerSubZ _ hε hεsmall),?_,?_,hOut,hK,hCounts⟩
      · have hStartChart : arc 0 = FZ.symm (Plane.mk (-δZ) 0) := hStart.trans hCornerStartZ
        have hm := actual_signed_chart_connector_selected_meet (r v).val FZ δZ
          (FZ germZ 0-endpointScaleZ*t.val) (FZ germZ 1) ρZ hGermZY arc hRange hStartChart
          (hStart.symm ▸ hCornerStartCurveZ) (hNearCornerCoreZ _ hε hεsmall)
          (by simpa [eZ] using hFZAxis)
        rwa [hStart] at hm
      · rw [hRange]
        exact hNearCornerOppositeAvoidZ _ hε hεsmall
    let actualCompactCornerPlaneU (s : Interval × Interval) : Plane :=
      Plane.mk (-δU) 0 + s.2.val •
        (Plane.mk (FU germU 0-(cornerToleranceU/2)*s.1.val) (FU germU 1)-Plane.mk (-δU) 0)
    have hActualCompactCornerPlaneContinuousU : Continuous actualCompactCornerPlaneU := by
      dsimp [actualCompactCornerPlaneU]
      fun_prop
    have hActualCompactCornerPlaneCoreU (s : Interval × Interval) :
        actualCompactCornerPlaneU s ∈ FU.target ∩ Metric.ball (0 : Plane) ρU := by
      let ε := (cornerToleranceU/2)*s.1.val
      have hSeg : actualCompactCornerPlaneU s ∈ nearCornerPlaneU ε := by
        change actualCompactCornerPlaneU s ∈ segment ℝ (Plane.mk (-δU) 0)
          (Plane.mk (FU germU 0-ε) (FU germU 1))
        rw [segment_eq_image']
        exact ⟨s.2.val,s.2.property,rfl⟩
      by_cases hs : s.1.val = 0
      · have hEndpoint : Plane.mk (FU germU 0-ε) (FU germU 1) = FU germU := by
          ext i
          fin_cases i <;> simp [ε,hs,Plane.mk]
        have hb : actualCompactCornerPlaneU s ∈ Metric.ball (0 : Plane) ηU := by
          have hsubset := (convex_ball (0 : Plane) ηU).segment_subset
            hNewCornerStartBallU hGermUBall
          apply hsubset
          simpa only [nearCornerPlaneU,hEndpoint] using hSeg
        exact hBallU hb
      · have hsp : 0 < s.1.val := lt_of_le_of_ne s.1.property.1 (Ne.symm hs)
        have hε : 0 < ε := mul_pos (half_pos hCornerToleranceU) hsp
        have hεsmall : ε < cornerToleranceU := by
          have hh := mul_le_of_le_one_right (half_pos hCornerToleranceU).le s.1.property.2
          dsimp [ε]
          linarith only [hh,hCornerToleranceU]
        exact hNearCornerCoreU ε hε hεsmall hSeg
    let actualCompactCornerMapU : C(Interval × Interval,S) :=
      ⟨fun s => FU.symm (actualCompactCornerPlaneU s),
        FU.symm.continuousOn.comp_continuous hActualCompactCornerPlaneContinuousU
          (fun s => (hActualCompactCornerPlaneCoreU s).1)⟩
    let actualCompactCornerSupportU := Set.range actualCompactCornerMapU
    have hActualCompactCornerSupportCompactU : IsCompact actualCompactCornerSupportU :=
      isCompact_range actualCompactCornerMapU.continuous
    have hActualCompactCornerSupportSubsetU : actualCompactCornerSupportU ⊆ Ucorner := by
      rintro x ⟨s,rfl⟩
      exact hEcornerUSub (hFUSource ▸ FU.map_target (hActualCompactCornerPlaneCoreU s).1)
    have hActualContactsAvoidCompactCornerU (p : Pg) : p.val ∉ actualCompactCornerSupportU :=
      fun hp => hActualContactsAvoidCornerU p (hActualCompactCornerSupportSubsetU hp)
    let actualCompactCornerPlaneZ (s : Interval × Interval) : Plane :=
      Plane.mk (-δZ) 0 + s.2.val •
        (Plane.mk (FZ germZ 0-(cornerToleranceZ/2)*s.1.val) (FZ germZ 1)-Plane.mk (-δZ) 0)
    have hActualCompactCornerPlaneContinuousZ : Continuous actualCompactCornerPlaneZ := by
      dsimp [actualCompactCornerPlaneZ]
      fun_prop
    have hActualCompactCornerPlaneCoreZ (s : Interval × Interval) :
        actualCompactCornerPlaneZ s ∈ FZ.target ∩ Metric.ball (0 : Plane) ρZ := by
      let ε := (cornerToleranceZ/2)*s.1.val
      have hSeg : actualCompactCornerPlaneZ s ∈ nearCornerPlaneZ ε := by
        change actualCompactCornerPlaneZ s ∈ segment ℝ (Plane.mk (-δZ) 0)
          (Plane.mk (FZ germZ 0-ε) (FZ germZ 1))
        rw [segment_eq_image']
        exact ⟨s.2.val,s.2.property,rfl⟩
      by_cases hs : s.1.val = 0
      · have hEndpoint : Plane.mk (FZ germZ 0-ε) (FZ germZ 1) = FZ germZ := by
          ext i
          fin_cases i <;> simp [ε,hs,Plane.mk]
        have hb : actualCompactCornerPlaneZ s ∈ Metric.ball (0 : Plane) ηZ := by
          have hsubset := (convex_ball (0 : Plane) ηZ).segment_subset
            hNewCornerStartBallZ hGermZBall
          apply hsubset
          simpa only [nearCornerPlaneZ,hEndpoint] using hSeg
        exact hBallZ hb
      · have hsp : 0 < s.1.val := lt_of_le_of_ne s.1.property.1 (Ne.symm hs)
        have hε : 0 < ε := mul_pos (half_pos hCornerToleranceZ) hsp
        have hεsmall : ε < cornerToleranceZ := by
          have hh := mul_le_of_le_one_right (half_pos hCornerToleranceZ).le s.1.property.2
          dsimp [ε]
          linarith only [hh,hCornerToleranceZ]
        exact hNearCornerCoreZ ε hε hεsmall hSeg
    let actualCompactCornerMapZ : C(Interval × Interval,S) :=
      ⟨fun s => FZ.symm (actualCompactCornerPlaneZ s),
        FZ.symm.continuousOn.comp_continuous hActualCompactCornerPlaneContinuousZ
          (fun s => (hActualCompactCornerPlaneCoreZ s).1)⟩
    let actualCompactCornerSupportZ := Set.range actualCompactCornerMapZ
    have hActualCompactCornerSupportCompactZ : IsCompact actualCompactCornerSupportZ :=
      isCompact_range actualCompactCornerMapZ.continuous
    have hActualCompactCornerSupportSubsetZ : actualCompactCornerSupportZ ⊆ Zcorner := by
      rintro x ⟨s,rfl⟩
      exact hEcornerZSub (hFZSource ▸ FZ.map_target (hActualCompactCornerPlaneCoreZ s).1)
    have hActualContactsAvoidCompactCornerZ (p : Pg) : p.val ∉ actualCompactCornerSupportZ :=
      fun hp => hActualContactsAvoidCornerZ p (hActualCompactCornerSupportSubsetZ hp)
    let actualCompactCorners := actualCompactCornerSupportU ∪ actualCompactCornerSupportZ
    have hActualCompactCornersCompact : IsCompact actualCompactCorners :=
      hActualCompactCornerSupportCompactU.union hActualCompactCornerSupportCompactZ
    have hActualContactSafePlaneCores (p : Pg) : ∃ η : ℝ, 0 < η ∧
        ∀ q ∈ Metric.ball (0 : Plane) η,
          q ∈ (contactPatchChart p).target ∧
          (contactPatchChart p).symm q ∉ actualCompactCorners := by
      let O := (contactPatchChart p) '' ((contactPatchChart p).source ∩ actualCompactCornersᶜ)
      have hO : IsOpen O := (contactPatchChart p).isOpen_image_source_inter
        hActualCompactCornersCompact.isClosed.isOpen_compl
      have hpAvoid : p.val ∉ actualCompactCorners := by
        rintro (hp | hp)
        · exact hActualContactsAvoidCompactCornerU p hp
        · exact hActualContactsAvoidCompactCornerZ p hp
      have hzero : (0 : Plane) ∈ O :=
        ⟨p.val,⟨hContactPatchCenterSource p,hpAvoid⟩,hContactPatchCenter p⟩
      obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hO 0 hzero
      refine ⟨η,hη,?_⟩
      intro q hq
      obtain ⟨x,⟨hx,havoid⟩,heq⟩ := hball hq
      refine ⟨heq ▸ (contactPatchChart p).map_source hx,?_⟩
      rw [←heq,(contactPatchChart p).left_inv hx]
      exact havoid
    choose actualContactSafeRadius hActualContactSafeRadius hActualContactSafePlane
      using hActualContactSafePlaneCores
    have hActualContactCornerSafeRectangles (p : Pg) : ∃ δ H : ℝ,
        0 < δ ∧ δ < actualCroppedWidth p ∧ 0 < H ∧ H < contactPatchHeight p ∧
        ∀ h : ℝ, 0 < h → h < H →
          segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆
            {q | q ∈ (contactPatchChart p).target ∧
              (contactPatchChart p).symm q ∉ actualCompactCorners} := by
      obtain ⟨d,H,hd,hH,hl,hr,hstrips⟩ := actual_uniform_radial_contact_patch
        (J := Fin 0) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
        (actualContactSafeRadius p) (hActualContactSafeRadius p)
      let δ := min d (actualCroppedWidth p)/2
      let T := min H (contactPatchHeight p)/2
      have hδ : 0 < δ := half_pos (lt_min hd (hActualCroppedWidth p))
      have hδd : δ < d := by dsimp [δ]; have hm := min_le_left d (actualCroppedWidth p); linarith only [hm,hd]
      have hδold : δ < actualCroppedWidth p := by
        dsimp [δ]; have hm := min_le_right d (actualCroppedWidth p); linarith only [hm,hActualCroppedWidth p]
      have hT : 0 < T := half_pos (lt_min hH (hContactPatchHeight p))
      have hTH : T < H := by dsimp [T]; have hm := min_le_left H (contactPatchHeight p); linarith only [hm,hH]
      have hTold : T < contactPatchHeight p := by
        dsimp [T]; have hm := min_le_right H (contactPatchHeight p); linarith only [hm,hContactPatchHeight p]
      refine ⟨δ,T,hδ,hδold,hT,hTold,?_⟩
      intro h hh hhT q hq
      have hball := (hstrips h hh (hhT.trans hTH)).1
        (actual_horizontal_contact_subsegment d δ h hd hδ hδd hq)
      exact hActualContactSafePlane p q hball
    choose actualCornerSafeContactWidth actualCornerSafeContactHeight
      hActualCornerSafeContactWidth hActualCornerSafeContactWidthBound
      hActualCornerSafeContactHeight hActualCornerSafeContactHeightBound hActualCornerSafeContactPlane
      using hActualContactCornerSafeRectangles
    have hActualCornerSafeContactProducer (p : Pg) (h : ℝ) (hh : 0 < h)
        (hhH : h < actualCornerSafeContactHeight p) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          Set.range f = (contactPatchChart p).symm '' segment ℝ
            (Plane.mk (-actualCornerSafeContactWidth p) h) (Plane.mk (actualCornerSafeContactWidth p) h) ∧
          f 0 = (contactPatchChart p).symm (Plane.mk (-actualCornerSafeContactWidth p) h) ∧
          f 1 = (contactPatchChart p).symm (Plane.mk (actualCornerSafeContactWidth p) h) ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          Disjoint (Set.range f) actualCompactCorners ∧
          (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) := by
      have hSubPlane := actual_horizontal_contact_subsegment (actualCroppedWidth p)
        (actualCornerSafeContactWidth p) h (hActualCroppedWidth p)
        (hActualCornerSafeContactWidth p) (hActualCornerSafeContactWidthBound p)
      obtain ⟨old,hOld,hOldRange,hOld0,hOld1,hOldSub,hOldK,hOldSign,hOldW,hOldCounts⟩ :=
        hActualCroppedContactProducer p h hh (hhH.trans (hActualCornerSafeContactHeightBound p))
      obtain ⟨f,hf,hRange,hf0,hf1⟩ := hHorizontalChartArc (contactPatchChart p)
        (actualCornerSafeContactWidth p) h (hActualCornerSafeContactWidth p)
        (fun q hq => (hActualCornerSafeContactPlane p h hh hhH hq).1)
      have hSub : Set.range f ⊆ Set.range old := by
        rw [hRange,hOldRange]
        exact Set.image_mono hSubPlane
      refine ⟨f,hf,hRange,hf0,hf1,hSub.trans hOldSub,hOldK.mono_left hSub,?_,
        (fun x hx => hOldSign x (hSub hx)),hOldW.mono_left hSub,?_⟩
      · apply Set.disjoint_left.mpr
        intro x hx hxC
        rw [hRange] at hx
        obtain ⟨q,hq,rfl⟩ := hx
        exact (hActualCornerSafeContactPlane p h hh hhH hq).2 hxC
      · intro i hi
        have hs : Set.range f ∩ (r i).val.image ⊆ Set.range old ∩ (r i).val.image :=
          fun x hx => ⟨hSub hx.1,hx.2⟩
        have ho := hOldCounts i hi
        exact ⟨ho.1.subset hs,(Set.ncard_le_ncard hs ho.1).trans ho.2⟩
    obtain ⟨actualCornerFaceRadiusU,hActualCornerFaceRadiusU,hActualCornerFaceSmallU⟩ :=
      hActualCornerExteriorFaceU
    let actualSafeCornerScaleU := min actualCornerFaceRadiusU
      (min 1 (cornerToleranceU/(2*endpointScaleU))) / 2
    have hActualSafeCornerScaleU : 0 < actualSafeCornerScaleU :=
      half_pos (lt_min hActualCornerFaceRadiusU
        (lt_min zero_lt_one (div_pos hCornerToleranceU (by positivity))))
    have hActualSafeCornerScaleFaceU : actualSafeCornerScaleU < actualCornerFaceRadiusU := by
      have hm := min_le_left actualCornerFaceRadiusU (min 1 (cornerToleranceU/(2*endpointScaleU)))
      dsimp [actualSafeCornerScaleU]
      linarith only [hm,hActualCornerFaceRadiusU]
    have hActualSafeCornerScaleOneU : actualSafeCornerScaleU ≤ 1 := by
      have hm := (min_le_right actualCornerFaceRadiusU
        (min 1 (cornerToleranceU/(2*endpointScaleU)))).trans
        (min_le_left 1 (cornerToleranceU/(2*endpointScaleU)))
      dsimp [actualSafeCornerScaleU]
      linarith only [hm]
    have hActualSafeCornerScaleToleranceU :
        endpointScaleU*actualSafeCornerScaleU ≤ cornerToleranceU/2 := by
      have hm := (min_le_right actualCornerFaceRadiusU
        (min 1 (cornerToleranceU/(2*endpointScaleU)))).trans
        (min_le_right 1 (cornerToleranceU/(2*endpointScaleU)))
      have hh := (le_div_iff₀ (by positivity : 0 < 2*endpointScaleU)).mp hm
      dsimp [actualSafeCornerScaleU]
      nlinarith only [hh,hCornerToleranceU]
    let actualSafeCornerParameterU : C(Interval,Interval) :=
      ⟨fun t => ⟨actualSafeCornerScaleU*t.val,
        ⟨mul_nonneg hActualSafeCornerScaleU.le t.property.1,
          (mul_le_of_le_one_right hActualSafeCornerScaleU.le t.property.2).trans hActualSafeCornerScaleOneU⟩⟩,
        by fun_prop⟩
    let actualSafeCornerEndpointU := actualCornerEndpointU.comp actualSafeCornerParameterU
    have hActualSafeCornerEndpointZeroU : actualSafeCornerEndpointU 0 = germU := by
      change actualCornerEndpointU (actualSafeCornerParameterU 0) = germU
      have hp : actualSafeCornerParameterU 0 = 0 := by apply Subtype.ext; simp [actualSafeCornerParameterU]
      rw [hp,hActualCornerEndpointUZero]
    have hActualSafeCornerEndpointPositiveU (t : Interval) (ht : 0 < t.val) :
        0 < actualExteriorSign*Eopposite (actualSafeCornerEndpointU t) 1 := by
      exact (hActualCornerFaceSmallU (actualSafeCornerParameterU t)
        (mul_pos hActualSafeCornerScaleU ht)
        (lt_of_le_of_lt (mul_le_of_le_one_right hActualSafeCornerScaleU.le t.property.2)
          hActualSafeCornerScaleFaceU)).2.2.1
    have hActualSafeCornerArcRangeU (t : Interval) :
        nearCornerSurfaceU (endpointScaleU*(actualSafeCornerParameterU t).val) ⊆
          actualCompactCornerSupportU := by
      let ε := endpointScaleU*(actualSafeCornerParameterU t).val
      have hε0 : 0 ≤ ε := mul_nonneg hEndpointScaleU.le (actualSafeCornerParameterU t).property.1
      have hεκ : ε ≤ cornerToleranceU/2 := by
        change endpointScaleU*(actualSafeCornerScaleU*t.val) ≤ cornerToleranceU/2
        rw [←mul_assoc]
        exact (mul_le_of_le_one_right (mul_pos hEndpointScaleU hActualSafeCornerScaleU).le
          t.property.2).trans hActualSafeCornerScaleToleranceU
      let a : Interval := ⟨ε/(cornerToleranceU/2),
        ⟨div_nonneg hε0 (half_pos hCornerToleranceU).le,
          (div_le_one (half_pos hCornerToleranceU)).mpr hεκ⟩⟩
      have hεeq : (cornerToleranceU/2)*a.val = ε :=
        mul_div_cancel₀ ε (ne_of_gt (half_pos hCornerToleranceU))
      rintro x ⟨q,hq,rfl⟩
      change q ∈ segment ℝ (Plane.mk (-δU) 0)
        (Plane.mk (FU germU 0-ε) (FU germU 1)) at hq
      rw [segment_eq_image'] at hq
      obtain ⟨b,hb,rfl⟩ := hq
      refine ⟨(a,⟨b,hb⟩),?_⟩
      change FU.symm (actualCompactCornerPlaneU (a,⟨b,hb⟩)) = _
      dsimp only [actualCompactCornerPlaneU]
      rw [hεeq]
    obtain ⟨actualCornerFaceRadiusZ,hActualCornerFaceRadiusZ,hActualCornerFaceSmallZ⟩ :=
      hActualCornerExteriorFaceZ
    let actualSafeCornerScaleZ := min actualCornerFaceRadiusZ
      (min 1 (cornerToleranceZ/(2*endpointScaleZ))) / 2
    have hActualSafeCornerScaleZ : 0 < actualSafeCornerScaleZ :=
      half_pos (lt_min hActualCornerFaceRadiusZ
        (lt_min zero_lt_one (div_pos hCornerToleranceZ (by positivity))))
    have hActualSafeCornerScaleFaceZ : actualSafeCornerScaleZ < actualCornerFaceRadiusZ := by
      have hm := min_le_left actualCornerFaceRadiusZ (min 1 (cornerToleranceZ/(2*endpointScaleZ)))
      dsimp [actualSafeCornerScaleZ]
      linarith only [hm,hActualCornerFaceRadiusZ]
    have hActualSafeCornerScaleOneZ : actualSafeCornerScaleZ ≤ 1 := by
      have hm := (min_le_right actualCornerFaceRadiusZ
        (min 1 (cornerToleranceZ/(2*endpointScaleZ)))).trans
        (min_le_left 1 (cornerToleranceZ/(2*endpointScaleZ)))
      dsimp [actualSafeCornerScaleZ]
      linarith only [hm]
    have hActualSafeCornerScaleToleranceZ :
        endpointScaleZ*actualSafeCornerScaleZ ≤ cornerToleranceZ/2 := by
      have hm := (min_le_right actualCornerFaceRadiusZ
        (min 1 (cornerToleranceZ/(2*endpointScaleZ)))).trans
        (min_le_right 1 (cornerToleranceZ/(2*endpointScaleZ)))
      have hh := (le_div_iff₀ (by positivity : 0 < 2*endpointScaleZ)).mp hm
      dsimp [actualSafeCornerScaleZ]
      nlinarith only [hh,hCornerToleranceZ]
    let actualSafeCornerParameterZ : C(Interval,Interval) :=
      ⟨fun t => ⟨actualSafeCornerScaleZ*t.val,
        ⟨mul_nonneg hActualSafeCornerScaleZ.le t.property.1,
          (mul_le_of_le_one_right hActualSafeCornerScaleZ.le t.property.2).trans hActualSafeCornerScaleOneZ⟩⟩,
        by fun_prop⟩
    let actualSafeCornerEndpointZ := actualCornerEndpointZ.comp actualSafeCornerParameterZ
    have hActualSafeCornerEndpointZeroZ : actualSafeCornerEndpointZ 0 = germZ := by
      change actualCornerEndpointZ (actualSafeCornerParameterZ 0) = germZ
      have hp : actualSafeCornerParameterZ 0 = 0 := by apply Subtype.ext; simp [actualSafeCornerParameterZ]
      rw [hp,hActualCornerEndpointZZero]
    have hActualSafeCornerEndpointPositiveZ (t : Interval) (ht : 0 < t.val) :
        0 < actualExteriorSign*Eopposite (actualSafeCornerEndpointZ t) 1 := by
      exact (hActualCornerFaceSmallZ (actualSafeCornerParameterZ t)
        (mul_pos hActualSafeCornerScaleZ ht)
        (lt_of_le_of_lt (mul_le_of_le_one_right hActualSafeCornerScaleZ.le t.property.2)
          hActualSafeCornerScaleFaceZ)).2.2.1
    have hActualSafeCornerArcRangeZ (t : Interval) :
        nearCornerSurfaceZ (endpointScaleZ*(actualSafeCornerParameterZ t).val) ⊆
          actualCompactCornerSupportZ := by
      let ε := endpointScaleZ*(actualSafeCornerParameterZ t).val
      have hε0 : 0 ≤ ε := mul_nonneg hEndpointScaleZ.le (actualSafeCornerParameterZ t).property.1
      have hεκ : ε ≤ cornerToleranceZ/2 := by
        change endpointScaleZ*(actualSafeCornerScaleZ*t.val) ≤ cornerToleranceZ/2
        rw [←mul_assoc]
        exact (mul_le_of_le_one_right (mul_pos hEndpointScaleZ hActualSafeCornerScaleZ).le
          t.property.2).trans hActualSafeCornerScaleToleranceZ
      let a : Interval := ⟨ε/(cornerToleranceZ/2),
        ⟨div_nonneg hε0 (half_pos hCornerToleranceZ).le,
          (div_le_one (half_pos hCornerToleranceZ)).mpr hεκ⟩⟩
      have hεeq : (cornerToleranceZ/2)*a.val = ε :=
        mul_div_cancel₀ ε (ne_of_gt (half_pos hCornerToleranceZ))
      rintro x ⟨q,hq,rfl⟩
      change q ∈ segment ℝ (Plane.mk (-δZ) 0)
        (Plane.mk (FZ germZ 0-ε) (FZ germZ 1)) at hq
      rw [segment_eq_image'] at hq
      obtain ⟨b,hb,rfl⟩ := hq
      refine ⟨(a,⟨b,hb⟩),?_⟩
      change FZ.symm (actualCompactCornerPlaneZ (a,⟨b,hb⟩)) = _
      dsimp only [actualCompactCornerPlaneZ]
      rw [hεeq]
    have hActualCornerSafeContactAxisTarget (p : Pg) (x : ℝ)
        (hx : x ∈ Set.Icc (-actualCornerSafeContactWidth p) (actualCornerSafeContactWidth p)) :
        Plane.mk x 0 ∈ (contactPatchChart p).target :=
      hActualCroppedContactAxisTarget p x
        ⟨by linarith only [hx.1,hActualCornerSafeContactWidthBound p],
          by linarith only [hx.2,hActualCornerSafeContactWidthBound p]⟩
    have hActualCornerSafeContactEndpointFamilies (p : Pg) :=
      actual_horizontal_contact_endpoint_families (contactPatchChart p)
        (actualCornerSafeContactWidth p) (actualCornerSafeContactHeight p)
        (hActualCornerSafeContactHeight p)
        (hActualCornerSafeContactAxisTarget p _ ⟨le_rfl,by linarith only [hActualCornerSafeContactWidth p]⟩)
        (hActualCornerSafeContactAxisTarget p _ ⟨by linarith only [hActualCornerSafeContactWidth p],le_rfl⟩)
        (fun h hh hhH q hq => (hActualCornerSafeContactPlane p h hh hhH hq).1)
    choose cornerSafeEndpointRawLeft cornerSafeEndpointRawRight hCornerSafeEndpointRawLeftZero
      hCornerSafeEndpointRawRightZero hCornerSafeEndpointRawLeftFormula hCornerSafeEndpointRawRightFormula
      using hActualCornerSafeContactEndpointFamilies
    let actualSafeContactCore (p : Pg) (t : Interval) :=
      (contactPatchChart p).symm '' segment ℝ
        (Plane.mk (-actualCornerSafeContactWidth p) ((actualCornerSafeContactHeight p/2)*t.val))
        (Plane.mk (actualCornerSafeContactWidth p) ((actualCornerSafeContactHeight p/2)*t.val))
    have hActualCornerSafeParameterizedContactProducer (p : Pg) (t : Interval) (ht : 0 < t.val) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
          f 0 = cornerSafeEndpointRawLeft p t ∧ f 1 = cornerSafeEndpointRawRight p t ∧
          Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
          Disjoint (Set.range f) actualCompactCorners ∧
          (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
          Disjoint (Set.range f) (r w).val.image ∧
          (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) ∧ Set.range f = actualSafeContactCore p t := by
      have hh : 0 < (actualCornerSafeContactHeight p/2)*t.val :=
        mul_pos (half_pos (hActualCornerSafeContactHeight p)) ht
      have hhH : (actualCornerSafeContactHeight p/2)*t.val < actualCornerSafeContactHeight p := by
        nlinarith only [t.property.2,hActualCornerSafeContactHeight p]
      obtain ⟨f,hf,hRange,hf0,hf1,hSub,hK,hCorner,hSign,hAvoid,hCount⟩ :=
        hActualCornerSafeContactProducer p _ hh hhH
      exact ⟨f,hf,hf0.trans (hCornerSafeEndpointRawLeftFormula p t).2.symm,
        hf1.trans (hCornerSafeEndpointRawRightFormula p t).2.symm,hSub,hK,hCorner,hSign,hAvoid,hCount,hRange⟩
    have hActualCornerSafeContactOriginalWidthBound (p : Pg) :
        actualCornerSafeContactWidth p < contactPatchHalfWidth p :=
      (hActualCornerSafeContactWidthBound p).trans (hActualCroppedWidthBound p)
    have hActualCornerSafeAxisContinuous (p : Pg) : ContinuousOn (actualContactAxis p)
        (Set.Icc (-actualCornerSafeContactWidth p) (actualCornerSafeContactWidth p)) :=
      (hActualContactAxisContinuous p).mono (fun x hx =>
        ⟨by linarith only [hx.1,hActualCornerSafeContactOriginalWidthBound p],
          by linarith only [hx.2,hActualCornerSafeContactOriginalWidthBound p]⟩)
    have hActualCornerSafeAxisInjective (p : Pg) : Set.InjOn (actualContactAxis p)
        (Set.Icc (-actualCornerSafeContactWidth p) (actualCornerSafeContactWidth p)) := by
      intro x hx y hy hxy
      exact hActualContactAxisInjective p
        ⟨by linarith only [hx.1,hActualCornerSafeContactOriginalWidthBound p],by linarith only [hx.2,hActualCornerSafeContactOriginalWidthBound p]⟩
        ⟨by linarith only [hy.1,hActualCornerSafeContactOriginalWidthBound p],by linarith only [hy.2,hActualCornerSafeContactOriginalWidthBound p]⟩ hxy
    have hActualCornerSafeAxisImage (p : Pg) :=
      actual_continuous_injective_axis_image (actualContactAxis p) (actualCornerSafeContactWidth p)
        (hActualCornerSafeContactWidth p) (hActualCornerSafeAxisContinuous p) (hActualCornerSafeAxisInjective p)
    choose actualCornerSafeLeft actualCornerSafeRight hActualCornerSafeLeft hActualCornerSafeRight
      hActualCornerSafeAxisImageEq hActualCornerSafeAxisOrientation using hActualCornerSafeAxisImage
    have hActualCornerSafeOrderedEndpointFamilies (p : Pg) :
        ∃ L R : C(Interval,S), Eopposite (L 0) 0 = actualCornerSafeLeft p ∧
          Eopposite (R 0) 0 = actualCornerSafeRight p ∧
          Eopposite (L 0) 1 = 0 ∧ Eopposite (R 0) 1 = 0 ∧
          (∀ t, L t ∈ Eopposite.source ∧ R t ∈ Eopposite.source) ∧
          ∀ t : Interval, 0 < t.val →
            ∃ f : C(Interval,S), Topology.IsEmbedding f ∧ f 0 = L t ∧ f 1 = R t ∧
              Set.range f ⊆ W p ∧ Disjoint (Set.range f) K ∧
              Disjoint (Set.range f) actualCompactCorners ∧
              (∀ x ∈ Set.range f, 0 < actualExteriorSign*Eopposite x 1) ∧
              Disjoint (Set.range f) (r w).val.image ∧
              (∀ i, i ≠ w → (Set.range f ∩ (r i).val.image).Finite ∧
                (Set.range f ∩ (r i).val.image).ncard ≤ if p.val ∈ (r i).val.image then 1 else 0) ∧ Set.range f = actualSafeContactCore p t := by
      have hRawLeft : Eopposite (cornerSafeEndpointRawLeft p 0) 0 =
          actualContactAxis p (-actualCornerSafeContactWidth p) := by
        rw [hCornerSafeEndpointRawLeftZero p]
      have hRawRight : Eopposite (cornerSafeEndpointRawRight p 0) 0 =
          actualContactAxis p (actualCornerSafeContactWidth p) := by
        rw [hCornerSafeEndpointRawRightZero p]
      have hRawLeftY : Eopposite (cornerSafeEndpointRawLeft p 0) 1 = 0 := by
        rw [hCornerSafeEndpointRawLeftZero p]
        exact (hContactPatchOriginalAxis p (-actualCornerSafeContactWidth p)
          ⟨by linarith only [hActualCornerSafeContactOriginalWidthBound p],by linarith only [hActualCornerSafeContactWidth p,hContactPatchHalfWidth p]⟩).2.2.1
      have hRawRightY : Eopposite (cornerSafeEndpointRawRight p 0) 1 = 0 := by
        rw [hCornerSafeEndpointRawRightZero p]
        exact (hContactPatchOriginalAxis p (actualCornerSafeContactWidth p)
          ⟨by linarith only [hActualCornerSafeContactWidth p,hContactPatchHalfWidth p],(hActualCornerSafeContactOriginalWidthBound p).le⟩).2.2.1

      have hSource (t : Interval) : cornerSafeEndpointRawLeft p t ∈ Eopposite.source ∧
          cornerSafeEndpointRawRight p t ∈ Eopposite.source :=
        ⟨(hContactPatchSource p (hCornerSafeEndpointRawLeftFormula p t).1).2,
          (hContactPatchSource p (hCornerSafeEndpointRawRightFormula p t).1).2⟩
      rcases hActualCornerSafeAxisOrientation p with hl | hr
      · refine ⟨cornerSafeEndpointRawLeft p,cornerSafeEndpointRawRight p,
          hRawLeft.trans hl.1.symm,hRawRight.trans hl.2.symm,hRawLeftY,hRawRightY,hSource,?_⟩
        exact hActualCornerSafeParameterizedContactProducer p
      · refine ⟨cornerSafeEndpointRawRight p,cornerSafeEndpointRawLeft p,
          hRawRight.trans hr.1.symm,hRawLeft.trans hr.2.symm,hRawRightY,hRawLeftY,(fun t => (hSource t).symm),?_⟩
        intro t ht
        obtain ⟨f,hf,hf0,hf1,hSub,hK,hCorner,hPos,hAvoid,hCount,hExactRange⟩ := hActualCornerSafeParameterizedContactProducer p t ht
        obtain ⟨g,hg,hRange,hg0,hg1⟩ := actual_reverse_embedded_continuous_arc f hf
        refine ⟨g,hg,hg0.trans hf1,hg1.trans hf0,?_,?_,?_,?_,?_,?_,?_⟩
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rwa [hRange]
        · rw [hRange]
          exact hExactRange
    choose actualCornerSafeEndpointLeft actualCornerSafeEndpointRight hActualCornerSafeEndpointLeftZero
      hActualCornerSafeEndpointRightZero hActualCornerSafeEndpointLeftYZero hActualCornerSafeEndpointRightYZero hActualCornerSafeEndpointsSource hActualCornerSafeOrderedContactProducer
      using hActualCornerSafeOrderedEndpointFamilies


    have hActualCornerSafeIntervalSubset (p : Pg) :
        Set.Icc (actualCornerSafeLeft p) (actualCornerSafeRight p) ⊆
          Set.Icc (actualCroppedLeft p) (actualCroppedRight p) := by
      rw [←hActualCornerSafeAxisImageEq p,←hActualCroppedAxisImageEq p]
      exact Set.image_mono (fun x hx =>
        ⟨by linarith only [hx.1,hActualCornerSafeContactWidthBound p],
          by linarith only [hx.2,hActualCornerSafeContactWidthBound p]⟩)
    have hActualCornerSafeLimitsInsideCorners (p : Pg) :
        min (Eopposite germU 0) (Eopposite germZ 0) < actualCornerSafeLeft p ∧
        actualCornerSafeRight p < max (Eopposite germU 0) (Eopposite germZ 0) := by
      have hl := hActualCornerSafeIntervalSubset p
        (show actualCornerSafeLeft p ∈ Set.Icc (actualCornerSafeLeft p) (actualCornerSafeRight p) from
          ⟨le_rfl,(hActualCornerSafeLeft p).le.trans (hActualCornerSafeRight p).le⟩)
      have hr := hActualCornerSafeIntervalSubset p
        (show actualCornerSafeRight p ∈ Set.Icc (actualCornerSafeLeft p) (actualCornerSafeRight p) from
          ⟨(hActualCornerSafeLeft p).le.trans (hActualCornerSafeRight p).le,le_rfl⟩)
      exact ⟨lt_of_lt_of_le (hActualCroppedLimitsBetweenCornerGerms p).1 hl.1,
        lt_of_le_of_lt hr.2 (hActualCroppedLimitsBetweenCornerGerms p).2⟩
    have hActualCornerSafeLimitsOrdered (p q : Pg) (hpq : contactX p < contactX q) :
        actualCornerSafeRight p < actualCornerSafeLeft q := by
      have hp := hActualCornerSafeIntervalSubset p
        (show actualCornerSafeRight p ∈ Set.Icc (actualCornerSafeLeft p) (actualCornerSafeRight p) from
          ⟨(hActualCornerSafeLeft p).le.trans (hActualCornerSafeRight p).le,le_rfl⟩)
      have hq := hActualCornerSafeIntervalSubset q
        (show actualCornerSafeLeft q ∈ Set.Icc (actualCornerSafeLeft q) (actualCornerSafeRight q) from
          ⟨le_rfl,(hActualCornerSafeLeft q).le.trans (hActualCornerSafeRight q).le⟩)
      exact lt_of_le_of_lt hp.2 (lt_of_lt_of_le (hActualCroppedLimitsOrdered p q hpq) hq.1)
    have hActualCornerSafeAdjacentSourceGapConnector (i j : Fin contactCoordinates.card)
        (hij : j.val = i.val+1) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (actualCornerSafeEndpointRight (actualSourceContactLabel i) t)
              (actualCornerSafeEndpointLeft (actualSourceContactLabel j) t),
            Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ k : I, Disjoint (Set.range f) (r k).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (actualCornerSafeEndpointRight (actualSourceContactLabel i) t) 0+
                s.val*Eopposite (actualCornerSafeEndpointLeft (actualSourceContactLabel j) t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      let p := actualSourceContactLabel i
      let q := actualSourceContactLabel j
      have hpq : contactX p < contactX q := by
        rw [hActualSourceContactLabel i,hActualSourceContactLabel j]
        exact actualContactOrder.strictMono (by change i.val < j.val; omega)
      have hgapLR := hActualCornerSafeLimitsOrdered p q hpq
      have hpR : contactX p < actualCornerSafeRight p := by
        simpa [hActualContactAxisZero p] using hActualCornerSafeRight p
      have hqL : actualCornerSafeLeft q < contactX q := by
        simpa [hActualContactAxisZero q] using hActualCornerSafeLeft q
      let A := (contactX p+actualCornerSafeRight p)/2
      let B := (actualCornerSafeLeft q+contactX q)/2
      have hA : -1 < A := by
        dsimp [A]
        have hb := (hActualContactCoordinateBounds p).1
        linarith only [hb,hpR]
      have hAl : A < actualCornerSafeRight p := by dsimp [A]; linarith only [hpR]
      have hrB : actualCornerSafeLeft q < B := by dsimp [B]; linarith only [hqL]
      have hB : B < 1 := by
        dsimp [B]
        have hb := (hActualContactCoordinateBounds q).2
        linarith only [hb,hqL]
      have hgap : Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ) := by
        have hf := actual_finite_boundary_adjacent_contact_gap contactCoordinates i j hij
        apply hf.mono_left
        intro x hx
        change actualContactOrder i < x ∧ x < actualContactOrder j
        rw [← hActualSourceContactLabel i,← hActualSourceContactLabel j]
        dsimp [A,B,p,q] at hx ⊢
        dsimp [p,q] at hpR hqL
        constructor <;> linarith only [hx.1,hx.2,hpR,hqL]
      apply hActualSignedSourceGapMatching A (actualCornerSafeRight p) (actualCornerSafeLeft q) B
        hA hAl hgapLR hrB hB hgap
        (actualCornerSafeEndpointRight p) (actualCornerSafeEndpointLeft q)
        (fun t => (hActualCornerSafeEndpointsSource p t).2)
        (fun t => (hActualCornerSafeEndpointsSource q t).1)
      · ext n
        fin_cases n
        · exact hActualCornerSafeEndpointRightZero p
        · exact hActualCornerSafeEndpointRightYZero p
      · ext n
        fin_cases n
        · exact hActualCornerSafeEndpointLeftZero q
        · exact hActualCornerSafeEndpointLeftYZero q
      · intro t ht
        obtain ⟨fp,hfp,hfp0,hfp1,hSubp,hKp,hCornerp,hSignp,hWp,hCountp⟩ := hActualCornerSafeOrderedContactProducer p t ht
        obtain ⟨fq,hfq,hfq0,hfq1,hSubq,hKq,hCornerq,hSignq,hWq,hCountq⟩ := hActualCornerSafeOrderedContactProducer q t ht
        exact ⟨hSignp _ ⟨1,hfp1⟩,hSignq _ ⟨0,hfq0⟩⟩


    have hActualGermCoordinateBoundsU : -1 < Eopposite germU 0 ∧ Eopposite germU 0 < 1 := by
      have hl := hActualOriginalSideCoordinateOrder
        (show ag ∈ Set.Icc ag zg from ⟨le_rfl,hagzg.le⟩)
        ⟨hActualCornerParameterU.1.1.le,hActualCornerParameterU.1.2.le⟩ hActualCornerParameterU.1.1
      have hr := hActualOriginalSideCoordinateOrder
        ⟨hActualCornerParameterU.1.1.le,hActualCornerParameterU.1.2.le⟩
        (show zg ∈ Set.Icc ag zg from ⟨hagzg.le,le_rfl⟩) hActualCornerParameterU.1.2
      change Eopposite (γg ag) 0 < Eopposite (γg actualCornerParameterU) 0 at hl
      change Eopposite (γg actualCornerParameterU) 0 < Eopposite (γg zg) 0 at hr
      rw [hActualCornerParameterU.2,hOppositeLeft] at hl
      rw [hActualCornerParameterU.2,hOppositeRight] at hr
      exact ⟨hl,hr⟩
    have hActualGermCoordinateBoundsZ : -1 < Eopposite germZ 0 ∧ Eopposite germZ 0 < 1 := by
      have hl := hActualOriginalSideCoordinateOrder
        (show ag ∈ Set.Icc ag zg from ⟨le_rfl,hagzg.le⟩)
        ⟨hActualCornerParameterZ.1.1.le,hActualCornerParameterZ.1.2.le⟩ hActualCornerParameterZ.1.1
      have hr := hActualOriginalSideCoordinateOrder
        ⟨hActualCornerParameterZ.1.1.le,hActualCornerParameterZ.1.2.le⟩
        (show zg ∈ Set.Icc ag zg from ⟨hagzg.le,le_rfl⟩) hActualCornerParameterZ.1.2
      change Eopposite (γg ag) 0 < Eopposite (γg actualCornerParameterZ) 0 at hl
      change Eopposite (γg actualCornerParameterZ) 0 < Eopposite (γg zg) 0 at hr
      rw [hActualCornerParameterZ.2,hOppositeLeft] at hl
      rw [hActualCornerParameterZ.2,hOppositeRight] at hr
      exact ⟨hl,hr⟩
    let actualSourceLeftCornerEndpoint := if βgU then actualSafeCornerEndpointU else actualSafeCornerEndpointZ
    let actualSourceRightCornerEndpoint := if βgU then actualSafeCornerEndpointZ else actualSafeCornerEndpointU
    let actualSourceLeftGerm := if βgU then germU else germZ
    let actualSourceRightGerm := if βgU then germZ else germU
    have hActualSourceLeftCornerZero : actualSourceLeftCornerEndpoint 0 = actualSourceLeftGerm := by
      cases hβ : βgU <;> simp only [actualSourceLeftCornerEndpoint,actualSourceLeftGerm,hβ,
        Bool.false_eq_true,ite_false,ite_true,hActualSafeCornerEndpointZeroU,hActualSafeCornerEndpointZeroZ]
    have hActualSourceRightCornerZero : actualSourceRightCornerEndpoint 0 = actualSourceRightGerm := by
      cases hβ : βgU <;> simp only [actualSourceRightCornerEndpoint,actualSourceRightGerm,hβ,
        Bool.false_eq_true,ite_false,ite_true,hActualSafeCornerEndpointZeroU,hActualSafeCornerEndpointZeroZ]
    have hActualSourceCornerMinMax : Eopposite actualSourceLeftGerm 0 =
        min (Eopposite germU 0) (Eopposite germZ 0) ∧
        Eopposite actualSourceRightGerm 0 = max (Eopposite germU 0) (Eopposite germZ 0) := by
      have ho := hActualCornerGermCoordinateOrder
      cases hβ : βgU <;>
        simp only [hβ,Bool.false_eq_true,ite_false,ite_true] at ho <;>
        simp only [actualSourceLeftGerm,actualSourceRightGerm,hβ,Bool.false_eq_true,ite_false,ite_true,
          min_eq_left ho.le,min_eq_right ho.le,max_eq_left ho.le,max_eq_right ho.le] <;>
        constructor <;> trivial
    have hActualSourceCornerEndpointSource (t : Interval) :
        actualSourceLeftCornerEndpoint t ∈ Eopposite.source ∧
        actualSourceRightCornerEndpoint t ∈ Eopposite.source := by
      have hU := (hActualCornerEndpointUCoordinates (actualSafeCornerParameterU t)).2.1
      have hZ := (hActualCornerEndpointZCoordinates (actualSafeCornerParameterZ t)).2.1
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerEndpoint,actualSourceRightCornerEndpoint,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;> first | exact ⟨hU,hZ⟩ | exact ⟨hZ,hU⟩
    have hActualSourceCornerEndpointPositive (t : Interval) (ht : 0 < t.val) :
        0 < actualExteriorSign*Eopposite (actualSourceLeftCornerEndpoint t) 1 ∧
        0 < actualExteriorSign*Eopposite (actualSourceRightCornerEndpoint t) 1 := by
      have hU := hActualSafeCornerEndpointPositiveU t ht
      have hZ := hActualSafeCornerEndpointPositiveZ t ht
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerEndpoint,actualSourceRightCornerEndpoint,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;> first | exact ⟨hU,hZ⟩ | exact ⟨hZ,hU⟩
    have hActualSourceCornerGermBounds :
        -1 < Eopposite actualSourceLeftGerm 0 ∧ Eopposite actualSourceRightGerm 0 < 1 := by
      cases hβ : βgU <;>
        simp only [actualSourceLeftGerm,actualSourceRightGerm,hβ,Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact ⟨hActualGermCoordinateBoundsU.1,hActualGermCoordinateBoundsZ.2⟩
              | exact ⟨hActualGermCoordinateBoundsZ.1,hActualGermCoordinateBoundsU.2⟩
    have hActualSourceCornerGermYZero : Eopposite actualSourceLeftGerm 1 = 0 ∧
        Eopposite actualSourceRightGerm 1 = 0 := by
      have hU := (hOppositeAxisEntire germU hGermUOppositeSource).mp (hgcurve hGermUInG.1)
      have hZ := (hOppositeAxisEntire germZ hGermZOppositeSource).mp (hgcurve hGermZInG.1)
      cases hβ : βgU <;>
        simp only [actualSourceLeftGerm,actualSourceRightGerm,hβ,Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact ⟨hU,hZ⟩ | exact ⟨hZ,hU⟩
    have hActualFirstSourceCornerGapConnector (i : Fin contactCoordinates.card) (hi : i.val = 0) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (actualSourceLeftCornerEndpoint t)
              (actualCornerSafeEndpointLeft (actualSourceContactLabel i) t),
            Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ k : I, Disjoint (Set.range f) (r k).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (actualSourceLeftCornerEndpoint t) 0+
                s.val*Eopposite (actualCornerSafeEndpointLeft (actualSourceContactLabel i) t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      let p := actualSourceContactLabel i
      let l := Eopposite actualSourceLeftGerm 0
      let rr := actualCornerSafeLeft p
      have hlr : l < rr := by
        dsimp only [l,rr]
        rw [hActualSourceCornerMinMax.1]
        exact (hActualCornerSafeLimitsInsideCorners p).1
      have hrc : rr < contactX p := by
        simpa [hActualContactAxisZero p] using hActualCornerSafeLeft p
      let A := (-1+l)/2
      let B := (rr+contactX p)/2
      have hA : -1 < A := by dsimp [A,l]; linarith only [hActualSourceCornerGermBounds.1]
      have hAl : A < l := by dsimp [A,l]; linarith only [hActualSourceCornerGermBounds.1]
      have hrB : rr < B := by dsimp [B]; linarith only [hrc]
      have hB : B < 1 := by
        dsimp [B]
        have hc := (hActualContactCoordinateBounds p).2
        linarith only [hrc,hc]
      have hBc : B < contactX p := by dsimp [B]; linarith only [hrc]
      have hgap := hActualFirstContactFreeInterval i hi A B hBc
      apply hActualSignedSourceGapMatching A l rr B hA hAl hlr hrB hB hgap
        actualSourceLeftCornerEndpoint (actualCornerSafeEndpointLeft p)
        (fun t => (hActualSourceCornerEndpointSource t).1)
        (fun t => (hActualCornerSafeEndpointsSource p t).1)
      · rw [hActualSourceLeftCornerZero]
        ext n
        fin_cases n
        · rfl
        · exact hActualSourceCornerGermYZero.1
      · ext n
        fin_cases n
        · exact hActualCornerSafeEndpointLeftZero p
        · exact hActualCornerSafeEndpointLeftYZero p
      · intro t ht
        obtain ⟨f,hf,hf0,hf1,hSub,hK,hCorner,hSign,hW,hCounts⟩ :=
          hActualCornerSafeOrderedContactProducer p t ht
        exact ⟨(hActualSourceCornerEndpointPositive t ht).1,hSign _ ⟨0,hf0⟩⟩
    have hActualLastSourceCornerGapConnector (i : Fin contactCoordinates.card)
        (hi : i.val+1 = contactCoordinates.card) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (actualCornerSafeEndpointRight (actualSourceContactLabel i) t)
              (actualSourceRightCornerEndpoint t),
            Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ k : I, Disjoint (Set.range f) (r k).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (actualCornerSafeEndpointRight (actualSourceContactLabel i) t) 0+
                s.val*Eopposite (actualSourceRightCornerEndpoint t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      let p := actualSourceContactLabel i
      let l := actualCornerSafeRight p
      let rr := Eopposite actualSourceRightGerm 0
      have hlr : l < rr := by
        dsimp only [l,rr]
        rw [hActualSourceCornerMinMax.2]
        exact (hActualCornerSafeLimitsInsideCorners p).2
      have hcl : contactX p < l := by
        simpa [hActualContactAxisZero p] using hActualCornerSafeRight p
      let A := (contactX p+l)/2
      let B := (rr+1)/2
      have hA : -1 < A := by
        dsimp [A]
        have hc := (hActualContactCoordinateBounds p).1
        linarith only [hcl,hc]
      have hAl : A < l := by dsimp [A]; linarith only [hcl]
      have hrB : rr < B := by dsimp [B,rr]; linarith only [hActualSourceCornerGermBounds.2]
      have hB : B < 1 := by dsimp [B,rr]; linarith only [hActualSourceCornerGermBounds.2]
      have hcA : contactX p < A := by dsimp [A]; linarith only [hcl]
      have hgap := hActualLastContactFreeInterval i hi A B hcA
      apply hActualSignedSourceGapMatching A l rr B hA hAl hlr hrB hB hgap
        (actualCornerSafeEndpointRight p) actualSourceRightCornerEndpoint
        (fun t => (hActualCornerSafeEndpointsSource p t).2)
        (fun t => (hActualSourceCornerEndpointSource t).2)
      · ext n
        fin_cases n
        · exact hActualCornerSafeEndpointRightZero p
        · exact hActualCornerSafeEndpointRightYZero p
      · rw [hActualSourceRightCornerZero]
        ext n
        fin_cases n
        · rfl
        · exact hActualSourceCornerGermYZero.2
      · intro t ht
        obtain ⟨f,hf,hf0,hf1,hSub,hK,hCorner,hSign,hW,hCounts⟩ :=
          hActualCornerSafeOrderedContactProducer p t ht
        exact ⟨hSign _ ⟨1,hf1⟩,(hActualSourceCornerEndpointPositive t ht).2⟩
    have hActualSourceCornerGermOrder : Eopposite actualSourceLeftGerm 0 <
        Eopposite actualSourceRightGerm 0 := by
      have ho := hActualCornerGermCoordinateOrder
      cases hβ : βgU <;>
        simpa only [actualSourceLeftGerm,actualSourceRightGerm,hβ,Bool.false_eq_true,ite_false,ite_true] using ho
    have hActualEmptySourceCornerGapConnector (hemptyContact : contactCoordinates.card = 0) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : Interval, 0 < t.val → t.val < ρ →
          ∃ f : Path (actualSourceLeftCornerEndpoint t) (actualSourceRightCornerEndpoint t),
            Topology.IsEmbedding f ∧ Disjoint (Set.range f) K ∧
            (∀ k : I, Disjoint (Set.range f) (r k).val.image) ∧
            (∀ s, f s ∈ Eopposite.source ∧
              Eopposite (f s) 0 = (1-s.val)*Eopposite (actualSourceLeftCornerEndpoint t) 0+
                s.val*Eopposite (actualSourceRightCornerEndpoint t) 0 ∧
              0 < actualExteriorSign*Eopposite (f s) 1) := by
      let l := Eopposite actualSourceLeftGerm 0
      let rr := Eopposite actualSourceRightGerm 0
      let A := (-1+l)/2
      let B := (rr+1)/2
      have hA : -1 < A := by dsimp [A,l]; linarith only [hActualSourceCornerGermBounds.1]
      have hAl : A < l := by dsimp [A,l]; linarith only [hActualSourceCornerGermBounds.1]
      have hrB : rr < B := by dsimp [B,rr]; linarith only [hActualSourceCornerGermBounds.2]
      have hB : B < 1 := by dsimp [B,rr]; linarith only [hActualSourceCornerGermBounds.2]
      have hgap : Disjoint (Set.Icc A B) (contactCoordinates : Set ℝ) := by
        have he : contactCoordinates = ∅ := Finset.card_eq_zero.mp hemptyContact
        simp [he]
      apply hActualSignedSourceGapMatching A l rr B hA hAl hActualSourceCornerGermOrder hrB hB hgap
        actualSourceLeftCornerEndpoint actualSourceRightCornerEndpoint
        (fun t => (hActualSourceCornerEndpointSource t).1)
        (fun t => (hActualSourceCornerEndpointSource t).2)
      · rw [hActualSourceLeftCornerZero]
        ext n
        fin_cases n
        · rfl
        · exact hActualSourceCornerGermYZero.1
      · rw [hActualSourceRightCornerZero]
        ext n
        fin_cases n
        · rfl
        · exact hActualSourceCornerGermYZero.2
      · exact hActualSourceCornerEndpointPositive
    let actualSafeCornerCoreU (t : Interval) :=
      nearCornerSurfaceU (endpointScaleU*(actualSafeCornerParameterU t).val)
    let actualSafeCornerCoreZ (t : Interval) :=
      nearCornerSurfaceZ (endpointScaleZ*(actualSafeCornerParameterZ t).val)
    have hActualSafeCornerFullProducerU (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧ arc 0 = cornerArcU 0 ∧
          arc 1 = actualSafeCornerEndpointU t ∧
          Set.range arc ⊆ actualCompactCornerSupportU ∧
          Set.range arc ∩ (r v).val.image = {cornerArcU 0} ∧
          Disjoint (Set.range arc) (r w).val.image ∧
          Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if u ∈ (r i).val.image then 1 else 0) ∧ Set.range arc = actualSafeCornerCoreU t := by
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hSub,hMeet,hW,hOut,hK,hCounts⟩ :=
        hActualCornerEndpointFullProducerU (actualSafeCornerParameterU t)
          (mul_pos hActualSafeCornerScaleU ht)
      refine ⟨arc,hEmb,hStart,hEnd,?_,hMeet,hW,hK,hCounts,hRange⟩
      rw [hRange]
      exact hActualSafeCornerArcRangeU t
    have hActualSafeCornerFullProducerZ (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧ arc 0 = cornerArcZ 0 ∧
          arc 1 = actualSafeCornerEndpointZ t ∧
          Set.range arc ⊆ actualCompactCornerSupportZ ∧
          Set.range arc ∩ (r v).val.image = {cornerArcZ 0} ∧
          Disjoint (Set.range arc) (r w).val.image ∧
          Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if z ∈ (r i).val.image then 1 else 0) ∧ Set.range arc = actualSafeCornerCoreZ t := by
      obtain ⟨arc,hEmb,hRange,hStart,hEnd,hSub,hMeet,hW,hOut,hK,hCounts⟩ :=
        hActualCornerEndpointFullProducerZ (actualSafeCornerParameterZ t)
          (mul_pos hActualSafeCornerScaleZ ht)
      refine ⟨arc,hEmb,hStart,hEnd,?_,hMeet,hW,hK,hCounts,hRange⟩
      rw [hRange]
      exact hActualSafeCornerArcRangeZ t
    let actualSourceLeftCornerStart := if βgU then cornerArcU 0 else cornerArcZ 0
    let actualSourceRightCornerStart := if βgU then cornerArcZ 0 else cornerArcU 0
    let actualSourceLeftCornerPoint := if βgU then u else z
    let actualSourceRightCornerPoint := if βgU then z else u
    let actualSourceLeftCornerCore (t : Interval) :=
      if βgU then actualSafeCornerCoreU t else actualSafeCornerCoreZ t
    let actualSourceRightCornerCore (t : Interval) :=
      if βgU then actualSafeCornerCoreZ t else actualSafeCornerCoreU t
    have hActualSourceLeftCornerArcProducer (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧
          arc 0 = actualSourceLeftCornerStart ∧ arc 1 = actualSourceLeftCornerEndpoint t ∧
          Set.range arc ⊆ actualCompactCorners ∧
          Set.range arc ∩ (r v).val.image = {actualSourceLeftCornerStart} ∧
          Disjoint (Set.range arc) (r w).val.image ∧ Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if actualSourceLeftCornerPoint ∈ (r i).val.image then 1 else 0) ∧ Set.range arc = actualSourceLeftCornerCore t := by
      cases hβ : βgU
      · obtain ⟨arc,hEmb,hStart,hEnd,hSub,hMeet,hW,hK,hCounts,hExactRange⟩ := hActualSafeCornerFullProducerZ t ht
        simp only [actualSourceLeftCornerStart,actualSourceLeftCornerEndpoint,actualSourceLeftCornerPoint,actualSourceLeftCornerCore,
          hβ,Bool.false_eq_true,ite_false]
        exact ⟨arc,hEmb,hStart,hEnd,hSub.trans (show actualCompactCornerSupportZ ⊆ actualCompactCorners from
          Set.subset_union_right),hMeet,hW,hK,hCounts,hExactRange⟩
      · obtain ⟨arc,hEmb,hStart,hEnd,hSub,hMeet,hW,hK,hCounts,hExactRange⟩ := hActualSafeCornerFullProducerU t ht
        simp only [actualSourceLeftCornerStart,actualSourceLeftCornerEndpoint,actualSourceLeftCornerPoint,actualSourceLeftCornerCore,
          hβ,ite_true]
        exact ⟨arc,hEmb,hStart,hEnd,hSub.trans (show actualCompactCornerSupportU ⊆ actualCompactCorners from
          Set.subset_union_left),hMeet,hW,hK,hCounts,hExactRange⟩
    have hActualSourceRightCornerArcProducer (t : Interval) (ht : 0 < t.val) :
        ∃ arc : C(Interval,S), Topology.IsEmbedding arc ∧
          arc 0 = actualSourceRightCornerStart ∧ arc 1 = actualSourceRightCornerEndpoint t ∧
          Set.range arc ⊆ actualCompactCorners ∧
          Set.range arc ∩ (r v).val.image = {actualSourceRightCornerStart} ∧
          Disjoint (Set.range arc) (r w).val.image ∧ Disjoint (Set.range arc) K ∧
          (∀ i : I, i ≠ v → (Set.range arc ∩ (r i).val.image).Finite ∧
            (Set.range arc ∩ (r i).val.image).ncard ≤ if actualSourceRightCornerPoint ∈ (r i).val.image then 1 else 0) ∧ Set.range arc = actualSourceRightCornerCore t := by
      cases hβ : βgU
      · obtain ⟨arc,hEmb,hStart,hEnd,hSub,hMeet,hW,hK,hCounts,hExactRange⟩ := hActualSafeCornerFullProducerU t ht
        simp only [actualSourceRightCornerStart,actualSourceRightCornerEndpoint,actualSourceRightCornerPoint,actualSourceRightCornerCore,
          hβ,Bool.false_eq_true,ite_false]
        exact ⟨arc,hEmb,hStart,hEnd,hSub.trans (show actualCompactCornerSupportU ⊆ actualCompactCorners from
          Set.subset_union_left),hMeet,hW,hK,hCounts,hExactRange⟩
      · obtain ⟨arc,hEmb,hStart,hEnd,hSub,hMeet,hW,hK,hCounts,hExactRange⟩ := hActualSafeCornerFullProducerZ t ht
        simp only [actualSourceRightCornerStart,actualSourceRightCornerEndpoint,actualSourceRightCornerPoint,actualSourceRightCornerCore,
          hβ,ite_true]
        exact ⟨arc,hEmb,hStart,hEnd,hSub.trans (show actualCompactCornerSupportZ ⊆ actualCompactCorners from
          Set.subset_union_right),hMeet,hW,hK,hCounts,hExactRange⟩
    have hActualSelectedExternalPrefixU : ∀ θ : ℝ,
        θ ∈ (if βU then Set.Ico (a-εU*tU.val) a
          else Set.Ioc zangle (zangle+εU*tU.val)) → γ θ ∈ Ucorner := by
      have hqeq : (r v).val.map (qU (eU ⟨v,huSelected⟩)) =
          (r v).val.map (b*Circle.exp (if !βU then zangle else a)) := by
        have hqp : (r v).val.map (qU (eU ⟨v,huSelected⟩)) = u :=
          by simpa [eU,JU] using hqU (eU ⟨v,huSelected⟩)
        by_cases hstart : u = γ a
        · simpa [βU,hstart,γ] using hqp.trans hstart
        · have hend : u = γ zangle := by
            rcases hSelectedEndpointOrientation with ho | ho
            · exact False.elim (hstart ho.1)
            · exact ho.1
          simpa [βU,hstart,γ] using hqp.trans hend
      have harms : ∀ t : Interval,
          (r v).val.map (qU (eU ⟨v,huSelected⟩)*Circle.exp
            (if !βU then εU*t.val else -(εU*t.val))) ∈ Ucorner := by
        intro t
        exact hEcornerUSub (by simpa [eU,JU] using (hArmsUSource (eU ⟨v,huSelected⟩) (!βU) t))
      have hp := actual_original_corner_angular_prefix (r v).val b
        (qU (eU ⟨v,huSelected⟩)) zangle a εU hεU tU (!βU) Ucorner hqeq harms
      cases hβ : βU <;>
        simpa only [γ,hβ,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using hp
    have hActualSelectedExternalPrefixZ : ∀ θ : ℝ,
        θ ∈ (if βZ then Set.Ico (a-εZ*tZ.val) a
          else Set.Ioc zangle (zangle+εZ*tZ.val)) → γ θ ∈ Zcorner := by
      have hqeq : (r v).val.map (qZ (eZ ⟨v,hzSelected⟩)) =
          (r v).val.map (b*Circle.exp (if !βZ then zangle else a)) := by
        have hqp : (r v).val.map (qZ (eZ ⟨v,hzSelected⟩)) = z :=
          by simpa [eZ,JZ] using hqZ (eZ ⟨v,hzSelected⟩)
        by_cases hstart : z = γ a
        · simpa [βZ,hstart,γ] using hqp.trans hstart
        · have hend : z = γ zangle := by
            rcases hSelectedEndpointOrientation with ho | ho
            · exact ho.2
            · exact False.elim (hstart ho.2)
          simpa [βZ,hstart,γ] using hqp.trans hend
      have harms : ∀ t : Interval,
          (r v).val.map (qZ (eZ ⟨v,hzSelected⟩)*Circle.exp
            (if !βZ then εZ*t.val else -(εZ*t.val))) ∈ Zcorner := by
        intro t
        exact hEcornerZSub (by simpa [eZ,JZ] using (hArmsZSource (eZ ⟨v,hzSelected⟩) (!βZ) t))
      have hp := actual_original_corner_angular_prefix (r v).val b
        (qZ (eZ ⟨v,hzSelected⟩)) zangle a εZ hεZ tZ (!βZ) Zcorner hqeq harms
      cases hβ : βZ <;>
        simpa only [γ,hβ,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] using hp
    have hActualExtendedOldArcPieces : Set.range actualExtendedOldArc ⊆
        Ucorner ∪ (Set.range f ∪ Zcorner) := by
      intro x hx
      rw [hActualExtendedOldArcRange] at hx
      obtain ⟨θ,hθ,rfl⟩ := hx
      by_cases hθa : θ < a
      · cases hβ : βU
        · have hβZ : βZ = true := by rw [hActualSelectedCornerSidesOpposite,hβ]; rfl
          right; right
          apply hActualSelectedExternalPrefixZ θ
          simp only [hβZ,ite_true]
          exact ⟨by simpa only [actualSelectedExtensionLeft,hβ,Bool.false_eq_true,ite_false] using hθ.1,hθa⟩
        · left
          apply hActualSelectedExternalPrefixU θ
          simp only [hβ,ite_true]
          exact ⟨by simpa only [actualSelectedExtensionLeft,hβ,ite_true] using hθ.1,hθa⟩
      · by_cases hzθ : zangle < θ
        · cases hβ : βU
          · left
            apply hActualSelectedExternalPrefixU θ
            simp only [hβ,Bool.false_eq_true,ite_false]
            exact ⟨hzθ,by simpa only [actualSelectedExtensionRight,hβ,Bool.false_eq_true,ite_false] using hθ.2⟩
          · have hβZ : βZ = false := by rw [hActualSelectedCornerSidesOpposite,hβ]; rfl
            right; right
            apply hActualSelectedExternalPrefixZ θ
            simp only [hβZ,Bool.false_eq_true,ite_false]
            exact ⟨hzθ,by simpa only [actualSelectedExtensionRight,hβ,ite_true] using hθ.2⟩
        · right; left
          rw [hAngleImage]
          exact ⟨θ,⟨le_of_not_gt hθa,le_of_not_gt hzθ⟩,rfl⟩
    have hActualExtendedOldArcSelected : Set.range actualExtendedOldArc ⊆ (r v).val.image := by
      intro x hx
      rw [hActualExtendedOldArcRange] at hx
      obtain ⟨θ,hθ,rfl⟩ := hx
      exact ⟨b*Circle.exp θ,rfl⟩
    have hActualOldSideInExtendedArc : Set.range f ⊆ Set.range actualExtendedOldArc := by
      rw [hAngleImage,hActualExtendedOldArcRange]
      exact Set.image_mono (Set.Icc_subset_Icc hActualSelectedExtensionBounds.1.le
        hActualSelectedExtensionBounds.2.le)
    have hActualExtendedOldArcThirdExact (i : I) (hi : i ≠ v) :
        Set.range actualExtendedOldArc ∩ (r i).val.image = Set.range f ∩ (r i).val.image := by
      apply Set.Subset.antisymm
      · intro x hx
        have hv := hActualExtendedOldArcSelected hx.1
        rcases hActualExtendedOldArcPieces hx.1 with hxU | hxf | hxZ
        · have he : x = u := Set.mem_singleton_iff.mp
            (hUContacts v i (Ne.symm hi) ⟨hxU,hv,hx.2⟩)
          exact ⟨⟨0,hf0.trans he.symm⟩,hx.2⟩
        · exact ⟨hxf,hx.2⟩
        · have he : x = z := Set.mem_singleton_iff.mp
            (hZContacts v i (Ne.symm hi) ⟨hxZ,hv,hx.2⟩)
          exact ⟨⟨1,hf1.trans he.symm⟩,hx.2⟩
      · exact fun x hx => ⟨hActualOldSideInExtendedArc hx.1,hx.2⟩
    have hActualExtendedOldArcInLarge : Set.range actualExtendedOldArc ⊆
        interior (Set.range dlarge) := by
      intro x hx
      rcases hActualExtendedOldArcPieces hx with hxU | hxf | hxZ
      · exact (hUcornerV hxU).2
      · exact hDiskInside (hDcurve.symm ▸ hxf).1
      · exact (hZcornerV hxZ).2
    have hActualExtendedOldArcChartSource : Set.range actualExtendedOldArc ⊆ Edisk.source :=
      hEdiskSource.symm ▸ hActualExtendedOldArcInLarge
    have hActualCompactCornersInChart : actualCompactCorners ⊆ Edisk.source := by
      intro x hx
      rw [hEdiskSource]
      rcases hx with hxU | hxZ
      · exact (hUcornerV (hActualCompactCornerSupportSubsetU hxU)).2
      · exact (hZcornerV (hActualCompactCornerSupportSubsetZ hxZ)).2
    have hActualSourceCornerStartsSelected : actualSourceLeftCornerStart ∈ (r v).val.image ∧
        actualSourceRightCornerStart ∈ (r v).val.image := by
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerStart,actualSourceRightCornerStart,hβ,Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact ⟨hCornerStartCurveU,hCornerStartCurveZ⟩ | exact ⟨hCornerStartCurveZ,hCornerStartCurveU⟩
    have hActualSourceCornerStartsNe : actualSourceLeftCornerStart ≠ actualSourceRightCornerStart := by
      have hu : cornerArcU 0 ∈ Ucorner := hSurfaceConnectorUSub
        (by
          have hx : cornerArcU 0 ∈ Set.range cornerArcU := ⟨0,rfl⟩
          rw [hCornerRangeU] at hx
          exact hx)
      have hz : cornerArcZ 0 ∈ Zcorner := hSurfaceConnectorZSub
        (by
          have hx : cornerArcZ 0 ∈ Set.range cornerArcZ := ⟨0,rfl⟩
          rw [hCornerRangeZ] at hx
          exact hx)
      have hne : cornerArcU 0 ≠ cornerArcZ 0 := by
        intro he
        exact Set.disjoint_left.mp hCornersDisjoint hu (he.symm ▸ hz)
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerStart,actualSourceRightCornerStart,hβ,Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact hne | exact hne.symm
    let actualGeometricCoreCarrier (t : Interval) :=
      actualSourceLeftCornerCore t ∪ ((⋃ j : Fin contactCoordinates.card,
        actualSafeContactCore (actualSourceContactLabel j) t) ∪ actualSourceRightCornerCore t)
    let actualGeometricCover (f : C(Interval,S)) : Prop :=
      ∃ t : Interval, 0 < t.val ∧ ∃ G : Set S, IsClosed G ∧
        (∀ i : I, Disjoint G (r i).val.image) ∧ Set.range f ⊆ actualGeometricCoreCarrier t ∪ G
    have hActualEmptySourceSimpleReplacement (hemptyContact : contactCoordinates.card = 0) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧ f 0 = actualSourceLeftCornerStart ∧
          f 1 = actualSourceRightCornerStart ∧ Set.range f ⊆ Edisk.source ∧
          Set.range f ∩ (r v).val.image ⊆ {actualSourceLeftCornerStart,actualSourceRightCornerStart} ∧
          Disjoint (Set.range f) (r w).val.image ∧ Disjoint (Set.range f) K ∧
          (∀ i : I, i ≠ v → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤
              (if actualSourceLeftCornerPoint ∈ (r i).val.image then 1 else 0)+
              (if actualSourceRightCornerPoint ∈ (r i).val.image then 1 else 0)) ∧ actualGeometricCover f := by
      obtain ⟨ρ,hρ,hGap⟩ := hActualEmptySourceCornerGapConnector hemptyContact
      let t : Interval := ⟨min ρ 1 / 2,
        ⟨(half_pos (lt_min hρ zero_lt_one)).le,by have hm := min_le_right ρ 1; linarith only [hm]⟩⟩
      have ht : 0 < t.val := half_pos (lt_min hρ zero_lt_one)
      have htρ : t.val < ρ := by have hm := min_le_left ρ 1; dsimp [t]; linarith only [hm,hρ]
      obtain ⟨left,hLeft,hLeft0,hLeft1,hLeftSub,hLeftMeet,hLeftW,hLeftK,hLeftCounts,hLeftExactRange⟩ :=
        hActualSourceLeftCornerArcProducer t ht
      obtain ⟨right,hRight,hRight0,hRight1,hRightSub,hRightMeet,hRightW,hRightK,hRightCounts,hRightExactRange⟩ :=
        hActualSourceRightCornerArcProducer t ht
      obtain ⟨gap,hGapEmb,hGapK,hGapAvoid,hGapData⟩ := hGap t ht htρ
      let gapC : C(Interval,S) := ⟨gap,gap.continuous⟩
      have hLeftS (s : Interval) : left s ∈ Edisk.source := hActualCompactCornersInChart (hLeftSub ⟨s,rfl⟩)
      have hRightS (s : Interval) : right s ∈ Edisk.source := hActualCompactCornersInChart (hRightSub ⟨s,rfl⟩)
      have hGapS (s : Interval) : gapC s ∈ Edisk.source :=
        hEdiskSource.symm ▸ (hOppositeSource (hGapData s).1).1
      have hStartS : actualSourceLeftCornerStart ∈ Edisk.source := hLeft0 ▸ hLeftS 0
      have hEndS : actualSourceRightCornerStart ∈ Edisk.source := hRight0 ▸ hRightS 0
      have hGapEndS : actualSourceRightCornerEndpoint t ∈ Edisk.source := gap.target ▸ hGapS 1
      have hLA := actual_chart_continuous_arc Edisk left hLeft hLeftS
      have hRA := actual_chart_continuous_arc Edisk right hRight hRightS
      have hGA := actual_chart_continuous_arc Edisk gapC hGapEmb hGapS
      have hGap0 : gapC 0 = actualSourceLeftCornerEndpoint t := gap.source
      have hGap1 : gapC 1 = actualSourceRightCornerEndpoint t := gap.target
      rw [hLeft0,hLeft1] at hLA
      rw [hRight0,hRight1] at hRA
      rw [hGap0,hGap1] at hGA
      have hStartGapEndNe : Edisk actualSourceLeftCornerStart ≠ Edisk (actualSourceRightCornerEndpoint t) := by
        intro he
        have hs := Edisk.injOn hStartS hGapEndS he
        exact Set.disjoint_left.mp (hGapAvoid v) ⟨1,gap.target⟩
          (hs ▸ hActualSourceCornerStartsSelected.1)
      have hStartsPlaneNe : Edisk actualSourceLeftCornerStart ≠ Edisk actualSourceRightCornerStart :=
        fun he => hActualSourceCornerStartsNe (Edisk.injOn hStartS hEndS he)
      obtain ⟨A,hAsub,hA⟩ := Schoenflies.exists_arc_in_union_of_arcs hLA hGA hStartGapEndNe
      obtain ⟨B,hBsub,hB⟩ := Schoenflies.exists_arc_in_union_of_arcs hA hRA.reverse hStartsPlaneNe
      have hBU : B ⊆ Edisk '' Set.range left ∪ (Edisk '' Set.range gapC ∪ Edisk '' Set.range right) := by
        intro q hq
        rcases hBsub hq with hqA | hqR
        · rcases hAsub hqA with hqL | hqG
          · exact Or.inl hqL
          · exact Or.inr (Or.inl hqG)
        · exact Or.inr (Or.inr hqR)
      have hPieceTarget (arc : C(Interval,S)) (hs : ∀ t, arc t ∈ Edisk.source) :
          Edisk '' Set.range arc ⊆ Edisk.target := by
        rintro q ⟨_,⟨s,rfl⟩,rfl⟩
        exact Edisk.map_source (hs s)
      have hBt : B ⊆ Edisk.target := by
        intro q hq
        rcases hBU hq with hqL | hqG | hqR
        · exact hPieceTarget left hLeftS hqL
        · exact hPieceTarget gapC hGapS hqG
        · exact hPieceTarget right hRightS hqR
      obtain ⟨f,hf,hRange,hf0,hf1⟩ :=
        actual_pullback_chart_arc Edisk actualSourceLeftCornerStart actualSourceRightCornerStart hStartS hEndS B hB hBt
      have hPullPiece (arc : C(Interval,S)) (hs : ∀ t, arc t ∈ Edisk.source)
          (q : Plane) (hq : q ∈ Edisk '' Set.range arc) : Edisk.symm q ∈ Set.range arc := by
        obtain ⟨y,hy,he⟩ := hq
        have hyS : y ∈ Edisk.source := by obtain ⟨s,rfl⟩ := hy; exact hs s
        rw [←he,Edisk.left_inv hyS]
        exact hy
      have hSub : Set.range f ⊆ Set.range left ∪ (Set.range gapC ∪ Set.range right) := by
        intro x hx
        rw [hRange] at hx
        obtain ⟨q,hq,rfl⟩ := hx
        rcases hBU hq with hqL | hqG | hqR
        · exact Or.inl (hPullPiece left hLeftS q hqL)
        · exact Or.inr (Or.inl (hPullPiece gapC hGapS q hqG))
        · exact Or.inr (Or.inr (hPullPiece right hRightS q hqR))
      have hGeometry : actualGeometricCover f := by
        refine ⟨t,ht,Set.range gapC,(isCompact_range gapC.continuous).isClosed,hGapAvoid,?_⟩
        intro x hx
        rcases hSub hx with hxL | hxG | hxR
        · left; left; exact hLeftExactRange ▸ hxL
        · right; exact hxG
        · left; right; right; exact hRightExactRange ▸ hxR
      refine ⟨f,hf,hf0,hf1,?_,?_,?_,?_,?_,hGeometry⟩
      · intro x hx
        rw [hRange] at hx
        obtain ⟨q,hq,rfl⟩ := hx
        exact Edisk.map_target (hBt hq)
      · intro x hx
        rcases hSub hx.1 with hxL | hxG | hxR
        · exact Or.inl (Set.mem_singleton_iff.mp (hLeftMeet ▸ ⟨hxL,hx.2⟩))
        · exact False.elim (Set.disjoint_left.mp (hGapAvoid v) hxG hx.2)
        · exact Or.inr (Set.mem_singleton_iff.mp (hRightMeet ▸ ⟨hxR,hx.2⟩))
      · apply Set.disjoint_left.mpr
        intro x hx hxW
        rcases hSub hx with hxL | hxG | hxR
        · exact Set.disjoint_left.mp hLeftW hxL hxW
        · exact Set.disjoint_left.mp (hGapAvoid w) hxG hxW
        · exact Set.disjoint_left.mp hRightW hxR hxW
      · apply Set.disjoint_left.mpr
        intro x hx hxK
        rcases hSub hx with hxL | hxG | hxR
        · exact Set.disjoint_left.mp hLeftK hxL hxK
        · exact Set.disjoint_left.mp hGapK hxG hxK
        · exact Set.disjoint_left.mp hRightK hxR hxK
      · intro i hi
        have hLC := hLeftCounts i hi
        have hRC := hRightCounts i hi
        have hs : Set.range f ∩ (r i).val.image ⊆
            (Set.range left ∩ (r i).val.image) ∪ (Set.range right ∩ (r i).val.image) := by
          intro x hx
          rcases hSub hx.1 with hxL | hxG | hxR
          · exact Or.inl ⟨hxL,hx.2⟩
          · exact False.elim (Set.disjoint_left.mp (hGapAvoid i) hxG hx.2)
          · exact Or.inr ⟨hxR,hx.2⟩
        have hfin := hLC.1.union hRC.1
        exact ⟨hfin.subset hs,(Set.ncard_le_ncard hs hfin).trans
          ((Set.ncard_union_le _ _).trans (Nat.add_le_add hLC.2 hRC.2))⟩
    let actualAdjacentContactPairs := {ij : Fin contactCoordinates.card × Fin contactCoordinates.card // ij.2.val = ij.1.val+1}
    have hActualAllAdjacentContactGaps (ij : actualAdjacentContactPairs) :=
      hActualCornerSafeAdjacentSourceGapConnector ij.val.1 ij.val.2 ij.property
    choose actualAdjacentGapRadius hActualAdjacentGapRadius hActualAdjacentGapProducer
      using hActualAllAdjacentContactGaps
    have hActualCommonSourceGapParameter (hN : 0 < contactCoordinates.card) :
        ∃ t : Interval, 0 < t.val ∧
          (∀ ij : actualAdjacentContactPairs, t.val < actualAdjacentGapRadius ij) ∧
          (∃ first : Path (actualSourceLeftCornerEndpoint t)
              (actualCornerSafeEndpointLeft (actualSourceContactLabel ⟨0,hN⟩) t),
            Topology.IsEmbedding first ∧ Disjoint (Set.range first) K ∧
            (∀ k : I, Disjoint (Set.range first) (r k).val.image) ∧
            (∀ s, first s ∈ Eopposite.source ∧
              Eopposite (first s) 0 = (1-s.val)*Eopposite (actualSourceLeftCornerEndpoint t) 0+
                s.val*Eopposite (actualCornerSafeEndpointLeft (actualSourceContactLabel ⟨0,hN⟩) t) 0 ∧
              0 < actualExteriorSign*Eopposite (first s) 1)) ∧
          (∃ last : Path (actualCornerSafeEndpointRight
                (actualSourceContactLabel ⟨contactCoordinates.card-1,by omega⟩) t)
              (actualSourceRightCornerEndpoint t),
            Topology.IsEmbedding last ∧ Disjoint (Set.range last) K ∧
            (∀ k : I, Disjoint (Set.range last) (r k).val.image) ∧
            (∀ s, last s ∈ Eopposite.source ∧
              Eopposite (last s) 0 = (1-s.val)*Eopposite (actualCornerSafeEndpointRight
                (actualSourceContactLabel ⟨contactCoordinates.card-1,by omega⟩) t) 0+
                s.val*Eopposite (actualSourceRightCornerEndpoint t) 0 ∧
              0 < actualExteriorSign*Eopposite (last s) 1)) := by
      obtain ⟨ρFirst,hρFirst,hFirst⟩ := hActualFirstSourceCornerGapConnector ⟨0,hN⟩ rfl
      obtain ⟨ρLast,hρLast,hLast⟩ := hActualLastSourceCornerGapConnector
        ⟨contactCoordinates.card-1,by omega⟩ (by change contactCoordinates.card-1+1 = _; omega)
      let radius : Option actualAdjacentContactPairs → ℝ := fun j => j.elim 1 actualAdjacentGapRadius
      let radii := Finset.univ.image radius
      have hradii : radii.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
      let μ := radii.min' hradii
      have hμ : 0 < μ := by
        obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.min'_mem radii hradii)
        change 0 < radii.min' hradii
        rw [←he]
        cases j
        · exact zero_lt_one
        · exact hActualAdjacentGapRadius _
      have hμle (ij : actualAdjacentContactPairs) : μ ≤ actualAdjacentGapRadius ij :=
        Finset.min'_le radii _ (Finset.mem_image.mpr ⟨some ij,Finset.mem_univ _,rfl⟩)
      let τ := min 1 (min ρFirst (min ρLast μ))/2
      have hτ : 0 < τ := half_pos (lt_min zero_lt_one (lt_min hρFirst (lt_min hρLast hμ)))
      have hτ1 : τ ≤ 1 := by have hm := min_le_left 1 (min ρFirst (min ρLast μ)); dsimp [τ]; linarith only [hm]
      have hτF : τ < ρFirst := by
        have hm := (min_le_right 1 (min ρFirst (min ρLast μ))).trans (min_le_left ρFirst (min ρLast μ))
        dsimp [τ]; linarith only [hm,hρFirst]
      have hτL : τ < ρLast := by
        have hm := ((min_le_right 1 (min ρFirst (min ρLast μ))).trans
          (min_le_right ρFirst (min ρLast μ))).trans (min_le_left ρLast μ)
        dsimp [τ]; linarith only [hm,hρLast]
      have hτμ : τ < μ := by
        have hm := ((min_le_right 1 (min ρFirst (min ρLast μ))).trans
          (min_le_right ρFirst (min ρLast μ))).trans (min_le_right ρLast μ)
        dsimp [τ]; linarith only [hm,hμ]
      let t : Interval := ⟨τ,⟨hτ.le,hτ1⟩⟩
      exact ⟨t,hτ,(fun ij => hτμ.trans_le (hμle ij)),hFirst t hτ hτF,hLast t hτ hτL⟩
    have hActualNonemptySourcePlanarReplacement (hN : 0 < contactCoordinates.card) :
        ∃ t : Interval, 0 < t.val ∧ ∃ left right : C(Interval,S),
          ∃ contacts : Fin contactCoordinates.card → C(Interval,S),
          ∃ first last : C(Interval,S), ∃ gaps : actualAdjacentContactPairs → C(Interval,S),
          ∃ B : Set Plane,
            IsArcBetween B (Edisk actualSourceLeftCornerStart) (Edisk actualSourceRightCornerStart) ∧
            B ⊆ Edisk '' (Set.range left ∪ (Set.range first ∪
              ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
                (Set.range last ∪ Set.range right))))) ∧
            (∀ x ∈ Set.range left ∪ (Set.range first ∪
              ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
                (Set.range last ∪ Set.range right)))), x ∈ Edisk.source) ∧
            Disjoint (Set.range left ∪ (Set.range first ∪
              ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
                (Set.range last ∪ Set.range right))))) K ∧
            Disjoint (Set.range left ∪ (Set.range first ∪
              ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
                (Set.range last ∪ Set.range right))))) (r w).val.image ∧
            (Set.range left ∪ (Set.range first ∪
              ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
                (Set.range last ∪ Set.range right))))) ∩ (r v).val.image ⊆ {actualSourceLeftCornerStart,actualSourceRightCornerStart} ∧
            (∀ i : I, i ≠ v →
              (Set.range left ∩ (r i).val.image).Finite ∧
              (Set.range right ∩ (r i).val.image).Finite ∧
              (Set.range left ∩ (r i).val.image).ncard ≤
                (if actualSourceLeftCornerPoint ∈ (r i).val.image then 1 else 0) ∧
              (Set.range right ∩ (r i).val.image).ncard ≤
                (if actualSourceRightCornerPoint ∈ (r i).val.image then 1 else 0)) ∧
            (∀ j i, i ≠ w → (Set.range (contacts j) ∩ (r i).val.image).Finite ∧
              (Set.range (contacts j) ∩ (r i).val.image).ncard ≤
                if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0) ∧
            (∀ i : I, Disjoint (Set.range first ∪ ((⋃ ij, Set.range (gaps ij)) ∪ Set.range last))
              (r i).val.image) ∧
            Set.range left = actualSourceLeftCornerCore t ∧
            Set.range right = actualSourceRightCornerCore t ∧
            (∀ j, Set.range (contacts j) = actualSafeContactCore (actualSourceContactLabel j) t) := by
      obtain ⟨t,ht,hAdjSmall,hFirst,hLast⟩ := hActualCommonSourceGapParameter hN
      obtain ⟨first,hFirstEmb,hFirstK,hFirstAvoid,hFirstData⟩ := hFirst
      obtain ⟨last,hLastEmb,hLastK,hLastAvoid,hLastData⟩ := hLast
      let firstC : C(Interval,S) := ⟨first,first.continuous⟩
      let lastC : C(Interval,S) := ⟨last,last.continuous⟩
      obtain ⟨left,hLeft,hLeft0,hLeft1,hLeftSub,hLeftMeet,hLeftW,hLeftK,hLeftCounts,hLeftExactRange⟩ :=
        hActualSourceLeftCornerArcProducer t ht
      obtain ⟨right,hRight,hRight0,hRight1,hRightSub,hRightMeet,hRightW,hRightK,hRightCounts,hRightExactRange⟩ :=
        hActualSourceRightCornerArcProducer t ht
      have hContactPieces (j : Fin contactCoordinates.card) :=
        hActualCornerSafeOrderedContactProducer (actualSourceContactLabel j) t ht
      choose contacts hContactEmb hContact0 hContact1 hContactSub hContactK hContactCorners
        hContactSign hContactW hContactCounts hContactExactRange using hContactPieces
      have hGapPieces (ij : actualAdjacentContactPairs) :=
        hActualAdjacentGapProducer ij t ht (hAdjSmall ij)
      choose gapPaths hGapEmb hGapK hGapAvoid hGapData using hGapPieces
      let gaps : actualAdjacentContactPairs → C(Interval,S) := fun ij => ⟨gapPaths ij,(gapPaths ij).continuous⟩
      let carrier := Set.range left ∪ (Set.range firstC ∪
        ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
          (Set.range lastC ∪ Set.range right))))
      have hLeftS (s : Interval) : left s ∈ Edisk.source := hActualCompactCornersInChart (hLeftSub ⟨s,rfl⟩)
      have hRightS (s : Interval) : right s ∈ Edisk.source := hActualCompactCornersInChart (hRightSub ⟨s,rfl⟩)
      have hFirstS (s : Interval) : firstC s ∈ Edisk.source :=
        hEdiskSource.symm ▸ (hOppositeSource (hFirstData s).1).1
      have hLastS (s : Interval) : lastC s ∈ Edisk.source :=
        hEdiskSource.symm ▸ (hOppositeSource (hLastData s).1).1
      have hContactS (j : Fin contactCoordinates.card) (s : Interval) : contacts j s ∈ Edisk.source := by
        have hE := (hQSub (actualSourceContactLabel j)
          ((hW (actualSourceContactLabel j)).2.2 (hContactSub j ⟨s,rfl⟩))).2
        exact hEdiskSource.symm ▸ (hOppositeSource hE).1
      have hGapS (ij : actualAdjacentContactPairs) (s : Interval) : gaps ij s ∈ Edisk.source :=
        hEdiskSource.symm ▸ (hOppositeSource (hGapData ij s).1).1
      have hCarrierS : carrier ⊆ Edisk.source := by
        intro x hx
        rcases hx with hxL | hxF | hxC | hxG | hxT | hxR
        · obtain ⟨s,rfl⟩ := hxL; exact hLeftS s
        · obtain ⟨s,rfl⟩ := hxF; exact hFirstS s
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
          obtain ⟨s,rfl⟩ := hj; exact hContactS j s
        · obtain ⟨ij,hij⟩ := Set.mem_iUnion.mp hxG
          obtain ⟨s,rfl⟩ := hij; exact hGapS ij s
        · obtain ⟨s,rfl⟩ := hxT; exact hLastS s
        · obtain ⟨s,rfl⟩ := hxR; exact hRightS s
      have hCarrierK : Disjoint carrier K := by
        apply Set.disjoint_left.mpr
        intro x hx hxK
        rcases hx with hxL | hxF | hxC | hxG | hxT | hxR
        · exact Set.disjoint_left.mp hLeftK hxL hxK
        · exact Set.disjoint_left.mp hFirstK hxF hxK
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
          exact Set.disjoint_left.mp (hContactK j) hj hxK
        · obtain ⟨ij,hij⟩ := Set.mem_iUnion.mp hxG
          exact Set.disjoint_left.mp (hGapK ij) hij hxK
        · exact Set.disjoint_left.mp hLastK hxT hxK
        · exact Set.disjoint_left.mp hRightK hxR hxK
      have hCarrierW : Disjoint carrier (r w).val.image := by
        apply Set.disjoint_left.mpr
        intro x hx hxW
        rcases hx with hxL | hxF | hxC | hxG | hxT | hxR
        · exact Set.disjoint_left.mp hLeftW hxL hxW
        · exact Set.disjoint_left.mp (hFirstAvoid w) hxF hxW
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
          exact Set.disjoint_left.mp (hContactW j) hj hxW
        · obtain ⟨ij,hij⟩ := Set.mem_iUnion.mp hxG
          exact Set.disjoint_left.mp (hGapAvoid ij w) hij hxW
        · exact Set.disjoint_left.mp (hLastAvoid w) hxT hxW
        · exact Set.disjoint_left.mp hRightW hxR hxW
      have hCarrierV : carrier ∩ (r v).val.image ⊆
          {actualSourceLeftCornerStart,actualSourceRightCornerStart} := by
        intro x hx
        rcases hx.1 with hxL | hxF | hxC | hxG | hxT | hxR
        · exact Or.inl (Set.mem_singleton_iff.mp (hLeftMeet ▸ ⟨hxL,hx.2⟩))
        · exact False.elim (Set.disjoint_left.mp (hFirstAvoid v) hxF hx.2)
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
          exact False.elim (Set.disjoint_left.mp
            (hInteriorContactSupportsAvoidSelected (actualSourceContactLabel j)) (hContactSub j hj) hx.2)
        · obtain ⟨ij,hij⟩ := Set.mem_iUnion.mp hxG
          exact False.elim (Set.disjoint_left.mp (hGapAvoid ij v) hij hx.2)
        · exact False.elim (Set.disjoint_left.mp (hLastAvoid v) hxT hx.2)
        · exact Or.inr (Set.mem_singleton_iff.mp (hRightMeet ▸ ⟨hxR,hx.2⟩))
      have hContactSubCarrier (j : Fin contactCoordinates.card) : Set.range (contacts j) ⊆ carrier :=
        fun x hx => Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j,hx⟩)))
      have hGapSubCarrier (ij : actualAdjacentContactPairs) : Set.range (gaps ij) ⊆ carrier :=
        fun x hx => Or.inr (Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨ij,hx⟩))))
      have hLeftSubCarrier : Set.range left ⊆ carrier := Set.subset_union_left
      have hFirstSubCarrier : Set.range firstC ⊆ carrier :=
        fun x hx => Or.inr (Or.inl hx)
      have hRightSubCarrier : Set.range right ⊆ carrier :=
        fun x hx => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))
      have hLastSubCarrier : Set.range lastC ⊆ carrier :=
        fun x hx => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
      have hContactPlaneArc (j : Fin contactCoordinates.card) :
          IsArcBetween (Edisk '' Set.range (contacts j))
            (Edisk (actualCornerSafeEndpointLeft (actualSourceContactLabel j) t))
            (Edisk (actualCornerSafeEndpointRight (actualSourceContactLabel j) t)) := by
        have ha := actual_chart_continuous_arc Edisk (contacts j) (hContactEmb j) (hContactS j)
        rwa [hContact0 j,hContact1 j] at ha
      have hGapPlaneArc (ij : actualAdjacentContactPairs) :
          IsArcBetween (Edisk '' Set.range (gaps ij))
            (Edisk (actualCornerSafeEndpointRight (actualSourceContactLabel ij.val.1) t))
            (Edisk (actualCornerSafeEndpointLeft (actualSourceContactLabel ij.val.2) t)) := by
        have ha := actual_chart_continuous_arc Edisk (gaps ij) (hGapEmb ij) (hGapS ij)
        have h0 : gaps ij 0 = _ := (gapPaths ij).source
        have h1 : gaps ij 1 = _ := (gapPaths ij).target
        rwa [h0,h1] at ha
      have hStartS : actualSourceLeftCornerStart ∈ Edisk.source := hLeft0 ▸ hLeftS 0
      have hEndS : actualSourceRightCornerStart ∈ Edisk.source := hRight0 ▸ hRightS 0
      have hContactEndpointAvoid (j : Fin contactCoordinates.card) (s : Interval) :
          contacts j s ∉ (r v).val.image :=
        fun hx => Set.disjoint_left.mp (hInteriorContactSupportsAvoidSelected (actualSourceContactLabel j))
          (hContactSub j ⟨s,rfl⟩) hx
      have hLeftEndpointNe (j : Fin contactCoordinates.card) :
          Edisk actualSourceLeftCornerStart ≠ Edisk (actualCornerSafeEndpointLeft (actualSourceContactLabel j) t) := by
        intro he
        have hs : actualCornerSafeEndpointLeft (actualSourceContactLabel j) t ∈ Edisk.source :=
          hContact0 j ▸ hContactS j 0
        have hh := Edisk.injOn hStartS hs he
        exact hContactEndpointAvoid j 0 ((hContact0 j).symm ▸ (hh ▸ hActualSourceCornerStartsSelected.1))
      have hRightEndpointNe (j : Fin contactCoordinates.card) :
          Edisk actualSourceLeftCornerStart ≠ Edisk (actualCornerSafeEndpointRight (actualSourceContactLabel j) t) := by
        intro he
        have hs : actualCornerSafeEndpointRight (actualSourceContactLabel j) t ∈ Edisk.source :=
          hContact1 j ▸ hContactS j 1
        have hh := Edisk.injOn hStartS hs he
        exact hContactEndpointAvoid j 1 ((hContact1 j).symm ▸ (hh ▸ hActualSourceCornerStartsSelected.1))
      have hJoin {A D : Set Plane} {a b c : Plane}
          (hA : IsArcBetween A a b) (hD : IsArcBetween D b c)
          (hAS : A ⊆ Edisk '' carrier) (hDS : D ⊆ Edisk '' carrier) (hne : a ≠ c) :
          ∃ B ⊆ Edisk '' carrier, IsArcBetween B a c := by
        obtain ⟨B,hBS,hB⟩ := Schoenflies.exists_arc_in_union_of_arcs hA hD hne
        exact ⟨B,hBS.trans (Set.union_subset hAS hDS),hB⟩
      have hPrefix (j : Fin contactCoordinates.card) : ∃ A ⊆ Edisk '' carrier,
          IsArcBetween A (Edisk actualSourceLeftCornerStart)
            (Edisk (actualCornerSafeEndpointLeft (actualSourceContactLabel j) t)) := by
        induction j using Fin.strong_induction_on with
        | h j ih =>
          by_cases hj : j.val = 0
          · have hj0 : j = ⟨0,hN⟩ := Fin.ext hj
            subst j
            have hLA := actual_chart_continuous_arc Edisk left hLeft hLeftS
            rw [hLeft0,hLeft1] at hLA
            have hFA := actual_chart_continuous_arc Edisk firstC hFirstEmb hFirstS
            have hF0 : firstC 0 = actualSourceLeftCornerEndpoint t := first.source
            have hF1 : firstC 1 = actualCornerSafeEndpointLeft (actualSourceContactLabel ⟨0,hN⟩) t := first.target
            rw [hF0,hF1] at hFA
            exact hJoin hLA hFA (Set.image_mono hLeftSubCarrier) (Set.image_mono hFirstSubCarrier) (hLeftEndpointNe _)
          · let k : Fin contactCoordinates.card := ⟨j.val-1,by omega⟩
            have hkj : k < j := by change j.val-1 < j.val; omega
            let ij : actualAdjacentContactPairs := ⟨(k,j),by dsimp [k]; omega⟩
            obtain ⟨A,hAS,hA⟩ := ih k hkj
            obtain ⟨D,hDS,hD⟩ := hJoin hA (hContactPlaneArc k) hAS
              (Set.image_mono (hContactSubCarrier k)) (hRightEndpointNe k)
            exact hJoin hD (hGapPlaneArc ij) hDS
              (Set.image_mono (hGapSubCarrier ij)) (hLeftEndpointNe j)
      let jLast : Fin contactCoordinates.card := ⟨contactCoordinates.card-1,by omega⟩
      obtain ⟨A,hAS,hA⟩ := hPrefix jLast
      obtain ⟨D,hDS,hD⟩ := hJoin hA (hContactPlaneArc jLast) hAS
        (Set.image_mono (hContactSubCarrier jLast)) (hRightEndpointNe jLast)
      have hTA := actual_chart_continuous_arc Edisk lastC hLastEmb hLastS
      have hT0 : lastC 0 = actualCornerSafeEndpointRight (actualSourceContactLabel jLast) t := last.source
      have hT1 : lastC 1 = actualSourceRightCornerEndpoint t := last.target
      rw [hT0,hT1] at hTA
      have hStartLastEndNe : Edisk actualSourceLeftCornerStart ≠ Edisk (actualSourceRightCornerEndpoint t) := by
        intro he
        have hs : actualSourceRightCornerEndpoint t ∈ Edisk.source := hT1 ▸ hLastS 1
        have hh := Edisk.injOn hStartS hs he
        exact Set.disjoint_left.mp (hLastAvoid v) ⟨1,last.target⟩ (hh ▸ hActualSourceCornerStartsSelected.1)
      obtain ⟨Z,hZS,hZ⟩ := hJoin hD hTA hDS (Set.image_mono hLastSubCarrier) hStartLastEndNe
      have hRA := actual_chart_continuous_arc Edisk right hRight hRightS
      rw [hRight0,hRight1] at hRA
      have hStartEndNe : Edisk actualSourceLeftCornerStart ≠ Edisk actualSourceRightCornerStart :=
        fun he => hActualSourceCornerStartsNe (Edisk.injOn hStartS hEndS he)
      obtain ⟨B,hBS,hB⟩ := hJoin hZ hRA.reverse hZS (Set.image_mono hRightSubCarrier) hStartEndNe
      refine ⟨t,ht,left,right,contacts,firstC,lastC,gaps,B,hB,hBS,hCarrierS,hCarrierK,hCarrierW,hCarrierV,?_,hContactCounts,?_,hLeftExactRange,hRightExactRange,hContactExactRange⟩
      · intro i hi
        exact ⟨(hLeftCounts i hi).1,(hRightCounts i hi).1,(hLeftCounts i hi).2,(hRightCounts i hi).2⟩
      · intro i
        apply Set.disjoint_left.mpr
        intro x hx hxi
        rcases hx with hxF | hxG | hxT
        · exact Set.disjoint_left.mp (hFirstAvoid i) hxF hxi
        · obtain ⟨ij,hij⟩ := Set.mem_iUnion.mp hxG
          exact Set.disjoint_left.mp (hGapAvoid ij i) hij hxi
        · exact Set.disjoint_left.mp (hLastAvoid i) hxT hxi
    have hActualSourceCornerStartsInChart : actualSourceLeftCornerStart ∈ Edisk.source ∧
        actualSourceRightCornerStart ∈ Edisk.source := by
      have hu : cornerArcU 0 ∈ Ucorner := hSurfaceConnectorUSub
        (by
          have hx : cornerArcU 0 ∈ Set.range cornerArcU := ⟨0,rfl⟩
          rw [hCornerRangeU] at hx
          exact hx)
      have hz : cornerArcZ 0 ∈ Zcorner := hSurfaceConnectorZSub
        (by
          have hx : cornerArcZ 0 ∈ Set.range cornerArcZ := ⟨0,rfl⟩
          rw [hCornerRangeZ] at hx
          exact hx)
      have hUS : cornerArcU 0 ∈ Edisk.source := hEdiskSource.symm ▸ (hUcornerV hu).2
      have hZS : cornerArcZ 0 ∈ Edisk.source := hEdiskSource.symm ▸ (hZcornerV hz).2
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerStart,actualSourceRightCornerStart,hβ,Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact ⟨hUS,hZS⟩ | exact ⟨hZS,hUS⟩
    have hActualNonemptySourceSimpleReplacement (hN : 0 < contactCoordinates.card) :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧ f 0 = actualSourceLeftCornerStart ∧
          f 1 = actualSourceRightCornerStart ∧ Set.range f ⊆ Edisk.source ∧
          Set.range f ∩ (r v).val.image ⊆ {actualSourceLeftCornerStart,actualSourceRightCornerStart} ∧
          Disjoint (Set.range f) (r w).val.image ∧ Disjoint (Set.range f) K ∧
          (∀ i : I, i ≠ v → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤
              (∑ j : Fin contactCoordinates.card,
                if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0)+
              (if actualSourceLeftCornerPoint ∈ (r i).val.image then 1 else 0)+
              (if actualSourceRightCornerPoint ∈ (r i).val.image then 1 else 0)) ∧ actualGeometricCover f := by
      obtain ⟨t,ht,left,right,contacts,first,last,gaps,B,hB,hBS,hCS,hCK,hCW,hCV,hCornerCounts,hContactCounts,hGFree,hLeftExactRange,hRightExactRange,hContactExactRange⟩ :=
        hActualNonemptySourcePlanarReplacement hN
      let carrier := Set.range left ∪ (Set.range first ∪
        ((⋃ i, Set.range (contacts i)) ∪ ((⋃ ij, Set.range (gaps ij)) ∪
          (Set.range last ∪ Set.range right))))
      have hBt : B ⊆ Edisk.target := by
        intro q hq
        obtain ⟨x,hx,rfl⟩ := hBS hq
        exact Edisk.map_source (hCS x hx)
      obtain ⟨f,hf,hRange,hf0,hf1⟩ := actual_pullback_chart_arc Edisk
        actualSourceLeftCornerStart actualSourceRightCornerStart
        hActualSourceCornerStartsInChart.1 hActualSourceCornerStartsInChart.2 B hB hBt
      have hSub : Set.range f ⊆ carrier := by
        intro x hx
        rw [hRange] at hx
        obtain ⟨q,hq,rfl⟩ := hx
        obtain ⟨y,hy,he⟩ := hBS hq
        rw [←he,Edisk.left_inv (hCS y hy)]
        exact hy
      have hGeometry : actualGeometricCover f := by
        let G := Set.range first ∪ ((⋃ ij,Set.range (gaps ij)) ∪ Set.range last)
        have hGClosed : IsClosed G := (isCompact_range first.continuous).isClosed.union
          ((isClosed_iUnion_of_finite (fun ij => (isCompact_range (gaps ij).continuous).isClosed)).union
            (isCompact_range last.continuous).isClosed)
        refine ⟨t,ht,G,hGClosed,hGFree,?_⟩
        intro x hx
        rcases hSub hx with hxL | hxF | hxC | hxG | hxT | hxR
        · left; left; exact hLeftExactRange ▸ hxL
        · right; left; exact hxF
        · left; right; left
          obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
          exact Set.mem_iUnion.mpr ⟨j,hContactExactRange j ▸ hj⟩
        · right; right; left; exact hxG
        · right; right; right; exact hxT
        · left; right; right; exact hRightExactRange ▸ hxR
      have hfW := hCW.mono_left hSub
      refine ⟨f,hf,hf0,hf1,(fun x hx => hCS x (hSub hx)),
        (fun x hx => hCV ⟨hSub hx.1,hx.2⟩),hfW,hCK.mono_left hSub,?_,hGeometry⟩
      intro i hi
      by_cases hiw : i = w
      · subst i
        rw [Set.disjoint_iff_inter_eq_empty.mp hfW]
        exact ⟨Set.finite_empty,by simp⟩
      · have hLC := (hCornerCounts i hi).1
        have hRC := (hCornerCounts i hi).2.1
        have hLeftBound := (hCornerCounts i hi).2.2.1
        have hRightBound := (hCornerCounts i hi).2.2.2
        let C := ⋃ j : Fin contactCoordinates.card, Set.range (contacts j) ∩ (r i).val.image
        have hC := actual_finite_union_card_bound
          (fun j : Fin contactCoordinates.card => Set.range (contacts j) ∩ (r i).val.image)
          (fun j => (hContactCounts j i hiw).1)
        have hCB : C.ncard ≤ ∑ j : Fin contactCoordinates.card,
            if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0 :=
          hC.2.trans (Finset.sum_le_sum (fun j hj => (hContactCounts j i hiw).2))
        have hs : Set.range f ∩ (r i).val.image ⊆
            (Set.range left ∩ (r i).val.image) ∪ (C ∪ (Set.range right ∩ (r i).val.image)) := by
          intro x hx
          rcases hSub hx.1 with hxL | hxF | hxC | hxG | hxT | hxR
          · exact Or.inl ⟨hxL,hx.2⟩
          · exact False.elim (Set.disjoint_left.mp (hGFree i) (Or.inl hxF) hx.2)
          · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
            exact Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨j,⟨hj,hx.2⟩⟩))
          · exact False.elim (Set.disjoint_left.mp (hGFree i) (Or.inr (Or.inl hxG)) hx.2)
          · exact False.elim (Set.disjoint_left.mp (hGFree i) (Or.inr (Or.inr hxT)) hx.2)
          · exact Or.inr (Or.inr ⟨hxR,hx.2⟩)
        have hfin := hLC.union (hC.1.union hRC)
        have hcard : (Set.range f ∩ (r i).val.image).ncard ≤
            (Set.range left ∩ (r i).val.image).ncard +
              (C.ncard+(Set.range right ∩ (r i).val.image).ncard) :=
          (Set.ncard_le_ncard hs hfin).trans ((Set.ncard_union_le _ _).trans
            (Nat.add_le_add_left (Set.ncard_union_le _ _) _))
        exact ⟨hfin.subset hs,by omega⟩
    have hActualSourceSimpleReplacement :
        ∃ f : C(Interval,S), Topology.IsEmbedding f ∧ f 0 = actualSourceLeftCornerStart ∧
          f 1 = actualSourceRightCornerStart ∧ Set.range f ⊆ Edisk.source ∧
          Set.range f ∩ (r v).val.image ⊆ {actualSourceLeftCornerStart,actualSourceRightCornerStart} ∧
          Disjoint (Set.range f) (r w).val.image ∧ Disjoint (Set.range f) K ∧
          (∀ i : I, i ≠ v → (Set.range f ∩ (r i).val.image).Finite ∧
            (Set.range f ∩ (r i).val.image).ncard ≤
              (∑ j : Fin contactCoordinates.card,
                if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0)+
              (if actualSourceLeftCornerPoint ∈ (r i).val.image then 1 else 0)+
              (if actualSourceRightCornerPoint ∈ (r i).val.image then 1 else 0)) ∧ actualGeometricCover f := by
      by_cases hN : 0 < contactCoordinates.card
      · exact hActualNonemptySourceSimpleReplacement hN
      · have he : contactCoordinates.card = 0 := Nat.eq_zero_of_not_pos hN
        obtain ⟨f,hf,hf0,hf1,hS,hV,hW,hK,hCounts,hGeometry⟩ := hActualEmptySourceSimpleReplacement he
        refine ⟨f,hf,hf0,hf1,hS,hV,hW,hK,?_,hGeometry⟩
        intro i hi
        have hsum : (∑ j : Fin contactCoordinates.card,
            if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          exact False.elim (Nat.not_lt_zero j.val (he ▸ j.isLt))
        simpa only [hsum,zero_add] using hCounts i hi
    have hActualSourceContactIncidenceCount (i : I) (hi : i ≠ w) :
        (∑ j : Fin contactCoordinates.card,
          if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0) =
        ((Set.range g \ {u,z}) ∩ (r i).val.image).ncard := by
      let J := {j : Fin contactCoordinates.card // (actualSourceContactLabel j).val ∈ (r i).val.image}
      let P := (Set.range g \ {u,z}) ∩ (r i).val.image
      let toPoint : J → P := fun j => ⟨(actualSourceContactLabel j.val).val,
        ⟨⟨(hPgFacts _ (actualSourceContactLabel j.val).property).1,by
          simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
          exact not_or.mpr ⟨(hPgFacts _ (actualSourceContactLabel j.val).property).2.1,
            (hPgFacts _ (actualSourceContactLabel j.val).property).2.2.1⟩⟩,j.property⟩⟩
      have hInj : Function.Injective toPoint := by
        intro j k he
        apply Subtype.ext
        apply hActualSourceContactLabelInjective
        apply Subtype.ext
        have hv := congrArg (fun x : P => x.val) he
        change (actualSourceContactLabel j.val).val = (actualSourceContactLabel k.val).val at hv
        exact hv
      have hSurj : Function.Surjective toPoint := by
        intro x
        have hxPg : x.val ∈ Pg := Set.mem_iUnion.mpr ⟨i,by
          rw [ite_eq_right hi]
          exact x.property⟩
        let p : Pg := ⟨x.val,hxPg⟩
        obtain ⟨j,hj⟩ := hActualSourceContactLabelSurjective p
        have hji : (actualSourceContactLabel j).val ∈ (r i).val.image := by
          rw [hj]
          exact x.property.2
        refine ⟨⟨j,hji⟩,?_⟩
        apply Subtype.ext
        change (actualSourceContactLabel j).val = x.val
        rw [hj]
      have hCard : Nat.card J = Nat.card P := Nat.card_congr (Equiv.ofBijective toPoint ⟨hInj,hSurj⟩)
      have hSum : (∑ j : Fin contactCoordinates.card,
          if (actualSourceContactLabel j).val ∈ (r i).val.image then 1 else 0) = Nat.card J := by
        exact actual_filter_indicator_card (fun j : Fin contactCoordinates.card =>
          (actualSourceContactLabel j).val ∈ (r i).val.image)
      exact hSum.trans hCard
    obtain ⟨actualReplacementArc,hActualReplacementArc,hActualReplacementArc0,hActualReplacementArc1,
      hActualReplacementArcSource,hActualReplacementSelectedMeet,hActualReplacementAvoidW,
      hActualReplacementAvoidK,hActualReplacementCounts,hActualReplacementGeometryCover⟩ := hActualSourceSimpleReplacement
    have hActualSourceReplacementEndpointOrientation :
        (actualSourceLeftCornerStart = γ actualSelectedExtensionLeft ∧
          actualSourceRightCornerStart = γ actualSelectedExtensionRight) ∨
        (actualSourceLeftCornerStart = γ actualSelectedExtensionRight ∧
          actualSourceRightCornerStart = γ actualSelectedExtensionLeft) := by
      have ho := hActualSelectedExternalStartsOrdered
      cases hβv : βU <;> cases hβg : βgU <;>
        simp only [hβv,Bool.false_eq_true,ite_false,ite_true] at ho <;>
        simp only [actualSourceLeftCornerStart,actualSourceRightCornerStart,hβg,
          Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact Or.inl ho | exact Or.inr ho.symm
    have hActualReplacementPathProducer : ∃ B : Path (γ actualSelectedExtensionLeft)
        (γ actualSelectedExtensionRight), Topology.IsEmbedding B ∧ Set.range B = Set.range actualReplacementArc := by
      rcases hActualSourceReplacementEndpointOrientation with ho | ho
      · exact ⟨⟨actualReplacementArc,
          hActualReplacementArc0.trans ho.1,hActualReplacementArc1.trans ho.2⟩,hActualReplacementArc,rfl⟩
      · obtain ⟨reverse,hReverse,hRange,h0,h1⟩ :=
          actual_reverse_embedded_continuous_arc actualReplacementArc hActualReplacementArc
        exact ⟨⟨reverse,h0.trans (hActualReplacementArc1.trans ho.2),
          h1.trans (hActualReplacementArc0.trans ho.1)⟩,hReverse,hRange⟩
    obtain ⟨actualReplacementPath,hActualReplacementPath,hActualReplacementPathRange⟩ := hActualReplacementPathProducer
    have hActualReplacementStartSet : ({actualSourceLeftCornerStart,actualSourceRightCornerStart} : Set S) =
        {γ actualSelectedExtensionLeft,γ actualSelectedExtensionRight} := by
      rcases hActualSourceReplacementEndpointOrientation with ho | ho
      · rw [ho.1,ho.2]
      · rw [ho.1,ho.2,Set.pair_comm]
    have hActualOldNewArcMeet : Set.range actualExtendedOldArc ∩ Set.range actualReplacementPath =
        {γ actualSelectedExtensionLeft,γ actualSelectedExtensionRight} := by
      apply Set.Subset.antisymm
      · intro x hx
        rw [hActualReplacementPathRange] at hx
        have he := hActualReplacementSelectedMeet ⟨hx.2,hActualExtendedOldArcSelected hx.1⟩
        rwa [hActualReplacementStartSet] at he
      · intro x hx
        rcases hx with rfl | rfl
        · exact ⟨⟨0,actualExtendedOldArc.source⟩,⟨0,actualReplacementPath.source⟩⟩
        · exact ⟨⟨1,actualExtendedOldArc.target⟩,⟨1,actualReplacementPath.target⟩⟩
    let actualOldContinuousArc : C(Interval,S) := ⟨actualExtendedOldArc,actualExtendedOldArc.continuous⟩
    let actualNewContinuousArc : C(Interval,S) := ⟨actualReplacementPath,actualReplacementPath.continuous⟩
    have hActualNewSource (t : Interval) : actualNewContinuousArc t ∈ Edisk.source :=
      hActualReplacementArcSource (hActualReplacementPathRange ▸ ⟨t,rfl⟩)
    have hActualOldSource (t : Interval) : actualOldContinuousArc t ∈ Edisk.source :=
      hActualExtendedOldArcChartSource ⟨t,rfl⟩
    have hActualOldPlanarArc := actual_chart_continuous_arc Edisk actualOldContinuousArc
      hActualExtendedOldArc hActualOldSource
    have hActualNewPlanarArc := actual_chart_continuous_arc Edisk actualNewContinuousArc
      hActualReplacementPath hActualNewSource
    have hActualOldPlanar0 : actualOldContinuousArc 0 = γ actualSelectedExtensionLeft := actualExtendedOldArc.source
    have hActualOldPlanar1 : actualOldContinuousArc 1 = γ actualSelectedExtensionRight := actualExtendedOldArc.target
    have hActualNewPlanar0 : actualNewContinuousArc 0 = γ actualSelectedExtensionLeft := actualReplacementPath.source
    have hActualNewPlanar1 : actualNewContinuousArc 1 = γ actualSelectedExtensionRight := actualReplacementPath.target
    rw [hActualOldPlanar0,hActualOldPlanar1] at hActualOldPlanarArc
    rw [hActualNewPlanar0,hActualNewPlanar1] at hActualNewPlanarArc
    have hActualOldNewPlanarMeet :
        (Edisk '' Set.range actualExtendedOldArc) ∩ (Edisk '' Set.range actualReplacementPath) =
          {Edisk (γ actualSelectedExtensionLeft),Edisk (γ actualSelectedExtensionRight)} := by
      apply Set.Subset.antisymm
      · rintro q ⟨⟨x,hx,rfl⟩,⟨y,hy,he⟩⟩
        have hxy : y = x := Edisk.injOn (hActualReplacementArcSource
          (hActualReplacementPathRange ▸ hy)) (hActualExtendedOldArcChartSource hx) he
        have hm := hActualOldNewArcMeet ▸ (show x ∈ Set.range actualExtendedOldArc ∩ Set.range actualReplacementPath from
          ⟨hx,hxy ▸ hy⟩)
        rcases hm with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · intro q hq
        rcases hq with rfl | rfl
        · exact ⟨⟨_,⟨0,actualExtendedOldArc.source⟩,rfl⟩,⟨_,⟨0,actualReplacementPath.source⟩,rfl⟩⟩
        · exact ⟨⟨_,⟨1,actualExtendedOldArc.target⟩,rfl⟩,⟨_,⟨1,actualReplacementPath.target⟩,rfl⟩⟩
    have hActualOldNewPlanarJordan : Schoenflies.IsJordanCurve
        ((Edisk '' Set.range actualExtendedOldArc) ∪ (Edisk '' Set.range actualReplacementPath)) := by
      apply Schoenflies.IsJordanCurve.of_two_arcs hActualOldPlanarArc hActualNewPlanarArc.reverse
      intro q hqA hqB
      have hm := hActualOldNewPlanarMeet ▸ (show q ∈
        (Edisk '' Set.range actualExtendedOldArc) ∩ (Edisk '' Set.range actualReplacementPath) from ⟨hqA,hqB⟩)
      simpa using hm
    let actualOldNewPlanarBoundary := (Edisk '' Set.range actualExtendedOldArc) ∪
      (Edisk '' Set.range actualReplacementPath)
    have hActualOldNewPlanarBoundaryInBall : actualOldNewPlanarBoundary ⊆ Metric.ball (0 : Plane) 1 := by
      intro q hq
      rw [←hEdiskTarget]
      rcases hq with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
      · exact Edisk.map_source (hActualExtendedOldArcChartSource hx)
      · exact Edisk.map_source (hActualReplacementArcSource (hActualReplacementPathRange ▸ hx))
    obtain ⟨actualPlanarSurgeryDisk,hActualPlanarSurgeryDisk,hActualPlanarSurgeryBoundary,
      hActualPlanarSurgeryInBall⟩ := actual_jordan_disc_in_open_unit_ball
        actualOldNewPlanarBoundary hActualOldNewPlanarJordan hActualOldNewPlanarBoundaryInBall
    have hActualPlanarSurgeryTarget (t : Metric.closedBall (0 : Plane) 1) :
        actualPlanarSurgeryDisk t ∈ Edisk.target :=
      hEdiskTarget.symm ▸ hActualPlanarSurgeryInBall ⟨t,rfl⟩
    let actualSurgeryDisk : C(Metric.closedBall (0 : Plane) 1,S) :=
      ⟨fun t => Edisk.symm (actualPlanarSurgeryDisk t),
        Edisk.symm.continuousOn.comp_continuous actualPlanarSurgeryDisk.continuous hActualPlanarSurgeryTarget⟩
    have hActualSurgeryDisk : Topology.IsEmbedding actualSurgeryDisk := by
      have hi : Function.Injective actualSurgeryDisk := by
        intro t u he
        exact hActualPlanarSurgeryDisk.injective (Edisk.symm.injOn
          (hActualPlanarSurgeryTarget t) (hActualPlanarSurgeryTarget u) he)
      exact (actualSurgeryDisk.continuous.isClosedEmbedding hi).isEmbedding
    have hActualSurgeryBoundary : actualSurgeryDisk '' {t | t.val ∈ Metric.sphere (0 : Plane) 1} =
        Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        have hq : actualPlanarSurgeryDisk t ∈ actualOldNewPlanarBoundary :=
          hActualPlanarSurgeryBoundary ▸ Set.mem_image_of_mem actualPlanarSurgeryDisk ht
        rcases hq with ⟨y,hy,he⟩ | ⟨y,hy,he⟩
        · left
          change Edisk.symm (actualPlanarSurgeryDisk t) ∈ Set.range actualExtendedOldArc
          rw [←he,Edisk.left_inv (hActualExtendedOldArcChartSource hy)]
          exact hy
        · right
          change Edisk.symm (actualPlanarSurgeryDisk t) ∈ Set.range actualReplacementPath
          rw [←he,Edisk.left_inv (hActualReplacementArcSource (hActualReplacementPathRange ▸ hy))]
          exact hy
      · intro hx
        have hxS : x ∈ Edisk.source := by
          rcases hx with hx | hx
          · exact hActualExtendedOldArcChartSource hx
          · exact hActualReplacementArcSource (hActualReplacementPathRange ▸ hx)
        have hq : Edisk x ∈ actualOldNewPlanarBoundary := by
          rcases hx with hx | hx
          · exact Or.inl ⟨x,hx,rfl⟩
          · exact Or.inr ⟨x,hx,rfl⟩
        rw [←hActualPlanarSurgeryBoundary] at hq
        obtain ⟨t,ht,he⟩ := hq
        refine ⟨t,ht,?_⟩
        change Edisk.symm (actualPlanarSurgeryDisk t) = x
        rw [he,Edisk.left_inv hxS]
    have hActualSurgeryDiskInLarge : Set.range actualSurgeryDisk ⊆ interior (Set.range dlarge) := by
      rintro x ⟨t,rfl⟩
      rw [←hEdiskSource]
      exact Edisk.map_target (hActualPlanarSurgeryTarget t)
    have hActualSurgeryFrontier : frontier (Set.range actualSurgeryDisk) =
        Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath := by
      have hc : IsClosed (Set.range actualSurgeryDisk) := (isCompact_range actualSurgeryDisk.continuous).isClosed
      rw [hc.frontier_eq,embedded_surface_disk_interior_eq actualSurgeryDisk hActualSurgeryDisk,←hActualSurgeryBoundary]
      ext x
      constructor
      · rintro ⟨⟨t,rfl⟩,htnot⟩
        refine ⟨t,?_,rfl⟩
        have htge : 1 ≤ dist t.val (0 : Plane) := by
          by_contra hn
          exact htnot ⟨t,lt_of_not_ge hn,rfl⟩
        exact le_antisymm t.property htge
      · rintro ⟨t,ht,rfl⟩
        refine ⟨⟨t,rfl⟩,?_⟩
        rintro ⟨u,hu,he⟩
        have htu := hActualSurgeryDisk.injective he
        subst u
        change dist t.val (0 : Plane) < 1 at hu
        change dist t.val (0 : Plane) = 1 at ht
        linarith only [hu,ht]
    have hActualRetainedSelected : Set.range actualRetainedRemainder ⊆ (r v).val.image := by
      intro x hx
      rw [hActualRetainedRemainderRange] at hx
      obtain ⟨θ,hθ,rfl⟩ := hx
      exact ⟨b*Circle.exp θ,rfl⟩
    let actualRetainedContinuousArc : C(Interval,S) := ⟨actualRetainedRemainder,actualRetainedRemainder.continuous⟩
    have hActualSurgeryRetainedExterior : Disjoint (Set.range actualRetainedRemainder)
        (interior (Set.range actualSurgeryDisk)) := by
      apply actual_surgery_disk_retained_remainder_exterior (r v)
        (Set.range actualExtendedOldArc) (Set.range actualReplacementPath) actualRetainedContinuousArc
        hActualRetainedRemainder hActualSelectedExactDecomposition
      · exact ⟨⟨1,actualExtendedOldArc.target.trans actualRetainedRemainder.source.symm⟩,
          ⟨0,actualExtendedOldArc.source.trans hActualRetainedRemainderEnd.symm⟩⟩
      · intro x hx
        have hm := hActualSelectedRemainderMeet ▸ hx
        change x ∈ {actualRetainedRemainder 0,actualRetainedRemainder 1}
        rw [actualRetainedRemainder.source,hActualRetainedRemainderEnd]
        rcases hm with hm | hm
        · exact Or.inr hm
        · exact Or.inl hm
      · intro x hx
        have hm := hActualReplacementSelectedMeet
          ⟨hActualReplacementPathRange ▸ hx.1,hActualRetainedSelected hx.2⟩
        rw [hActualReplacementStartSet] at hm
        change x ∈ {actualRetainedRemainder 0,actualRetainedRemainder 1}
        rw [actualRetainedRemainder.source,hActualRetainedRemainderEnd]
        rcases hm with hm | hm
        · exact Or.inr hm
        · exact Or.inl hm
      · exact hActualSurgeryDisk
      · exact hActualSurgeryFrontier
    obtain ⟨actualJordanGlobal,hActualJordanGlobalBoundary⟩ :=
      actual_jordan_global_unit_circle_chart actualOldNewPlanarBoundary hActualOldNewPlanarJordan
    have hActualJordanGlobalClosedRange : actualJordanGlobal '' Metric.closedBall (0 : Plane) 1 =
        Set.range actualPlanarSurgeryDisk := by
      rw [actual_global_jordan_closed_disk_range actualOldNewPlanarBoundary
        hActualOldNewPlanarJordan actualJordanGlobal hActualJordanGlobalBoundary]
      exact (embedded_disc_range_eq_closed_inside actualPlanarSurgeryDisk
        hActualPlanarSurgeryDisk actualOldNewPlanarBoundary hActualOldNewPlanarJordan
        hActualPlanarSurgeryBoundary).symm
    let actualNormalizedChartDomain : Set Plane := actualJordanGlobal ⁻¹' Edisk.target
    let actualNormalizedRetainedFreeDomain : Set Plane :=
      actualJordanGlobal ⁻¹' (Edisk '' (Edisk.source \ Set.range actualRetainedRemainder))
    have hActualNormalizedDomainOpen : IsOpen actualNormalizedRetainedFreeDomain := by
      apply actualJordanGlobal.continuous.isOpen_preimage
      apply Edisk.isOpen_image_of_subset_source
      · exact Edisk.open_source.inter (isCompact_range actualRetainedRemainder.continuous).isClosed.isOpen_compl
      · exact Set.diff_subset
    have hActualNormalizedFreeSubChart : actualNormalizedRetainedFreeDomain ⊆ actualNormalizedChartDomain := by
      rintro x ⟨y,hy,he⟩
      change actualJordanGlobal x ∈ Edisk.target
      rw [←he]
      exact Edisk.map_source hy.1
    have hActualNormalizedClosedChart : Metric.closedBall (0 : Plane) 1 ⊆ actualNormalizedChartDomain := by
      intro x hx
      have hq : actualJordanGlobal x ∈ Set.range actualPlanarSurgeryDisk := by
        rw [←hActualJordanGlobalClosedRange]
        exact Set.mem_image_of_mem actualJordanGlobal hx
      change actualJordanGlobal x ∈ Edisk.target
      exact hEdiskTarget.symm ▸ hActualPlanarSurgeryInBall hq
    have hActualNormalizedOpenRetainedFree : Metric.ball (0 : Plane) 1 ⊆ actualNormalizedRetainedFreeDomain := by
      intro x hx
      have hq : actualJordanGlobal x ∈ Set.range actualPlanarSurgeryDisk := by
        rw [←hActualJordanGlobalClosedRange]
        exact Set.mem_image_of_mem actualJordanGlobal (Metric.ball_subset_closedBall hx)
      obtain ⟨t,ht⟩ := hq
      have htInt : t.val ∈ Metric.ball (0 : Plane) 1 := by
        by_contra hn
        have htBoundary : t.val ∈ Metric.sphere (0 : Plane) 1 :=
          le_antisymm t.property (le_of_not_gt hn)
        have hb : actualPlanarSurgeryDisk t ∈ actualOldNewPlanarBoundary :=
          hActualPlanarSurgeryBoundary ▸ Set.mem_image_of_mem actualPlanarSurgeryDisk htBoundary
        rw [ht,←hActualJordanGlobalBoundary] at hb
        obtain ⟨q,hq,hqx⟩ := hb
        have hqx' : q = x := actualJordanGlobal.injective hqx
        rw [hqx'] at hq
        have hxn : dist x (0 : Plane) < 1 := hx
        have hqn : dist x (0 : Plane) = 1 := hq
        linarith only [hxn,hqn]
      have hxTarget : actualJordanGlobal x ∈ Edisk.target :=
        hActualNormalizedClosedChart (Metric.ball_subset_closedBall hx)
      refine ⟨Edisk.symm (actualJordanGlobal x),⟨Edisk.map_target hxTarget,?_⟩,
        Edisk.right_inv hxTarget⟩
      intro hR
      have hInt : Edisk.symm (actualJordanGlobal x) ∈ interior (Set.range actualSurgeryDisk) := by
        rw [embedded_surface_disk_interior_eq actualSurgeryDisk hActualSurgeryDisk]
        refine ⟨t,htInt,?_⟩
        change Edisk.symm (actualPlanarSurgeryDisk t) = Edisk.symm (actualJordanGlobal x)
        rw [ht]
      exact Set.disjoint_left.mp hActualSurgeryRetainedExterior hR hInt
    obtain ⟨actualRadialSupport,hActualRadialSupport,hActualRadialFixedForbidden⟩ :=
      actual_distance_radial_homeomorphism actualNormalizedRetainedFreeDomain
    have hActualRadialOpenAvoidance : actualRadialSupport '' Metric.ball (0 : Plane) 1 ⊆
        actualNormalizedRetainedFreeDomain := by
      have he : (actualRadialSupport : Plane → Plane) =
          (fun x => (1 + min 1 (Metric.infDist (NormedSpace.normalize x)
            actualNormalizedRetainedFreeDomainᶜ / 2)) • x) := funext hActualRadialSupport
      rw [he]
      exact actual_distance_radial_open_support actualNormalizedRetainedFreeDomain
        hActualNormalizedOpenRetainedFree
    have hActualRadialClosedChart : actualRadialSupport '' Metric.closedBall (0 : Plane) 1 ⊆
        actualNormalizedChartDomain := by
      have he : (actualRadialSupport : Plane → Plane) =
          (fun x => (1 + min 1 (Metric.infDist (NormedSpace.normalize x)
            actualNormalizedRetainedFreeDomainᶜ / 2)) • x) := funext hActualRadialSupport
      rw [he]
      exact actual_distance_radial_closed_support actualNormalizedRetainedFreeDomain
        actualNormalizedChartDomain hActualNormalizedFreeSubChart hActualNormalizedOpenRetainedFree
        (fun x hx => hActualNormalizedClosedChart (Metric.sphere_subset_closedBall hx))
    let actualProperSupportDisk : C(Metric.closedBall (0 : Plane) 1,S) :=
      ⟨fun t => Edisk.symm (actualJordanGlobal (actualRadialSupport t.val)),
        Edisk.symm.continuousOn.comp_continuous
          (actualJordanGlobal.continuous.comp (actualRadialSupport.continuous.comp continuous_subtype_val))
          (fun t => hActualRadialClosedChart ⟨t.val,t.property,rfl⟩)⟩
    have hActualProperSupportDisk : Topology.IsEmbedding actualProperSupportDisk := by
      have hi : Function.Injective actualProperSupportDisk := by
        intro t u he
        apply Subtype.ext
        apply actualRadialSupport.injective
        apply actualJordanGlobal.injective
        exact Edisk.symm.injOn
          (hActualRadialClosedChart ⟨t.val,t.property,rfl⟩)
          (hActualRadialClosedChart ⟨u.val,u.property,rfl⟩) he
      exact (actualProperSupportDisk.continuous.isClosedEmbedding hi).isEmbedding
    have hActualProperSupportInteriorAvoidsRetained : Disjoint
        (interior (Set.range actualProperSupportDisk)) (Set.range actualRetainedRemainder) := by
      rw [embedded_surface_disk_interior_eq actualProperSupportDisk hActualProperSupportDisk]
      apply Set.disjoint_left.mpr
      rintro x ⟨t,ht,rfl⟩ hR
      have hfree := hActualRadialOpenAvoidance ⟨t.val,ht,rfl⟩
      obtain ⟨y,hy,he⟩ := hfree
      have hyEq : Edisk.symm (actualJordanGlobal (actualRadialSupport t.val)) = y := by
        rw [←he,Edisk.left_inv hy.1]
      exact hy.2 (hyEq ▸ hR)
    have hActualProperSupportInLarge : Set.range actualProperSupportDisk ⊆ interior (Set.range dlarge) := by
      rintro x ⟨t,rfl⟩
      rw [←hEdiskSource]
      exact Edisk.map_target (hActualRadialClosedChart ⟨t.val,t.property,rfl⟩)
    let actualNormalizedLeftEnd := actualJordanGlobal.symm (Edisk (γ actualSelectedExtensionLeft))
    let actualNormalizedRightEnd := actualJordanGlobal.symm (Edisk (γ actualSelectedExtensionRight))
    have hActualOldNewBoundarySource : Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath ⊆ Edisk.source := by
      intro x hx
      rcases hx with hx | hx
      · exact hActualExtendedOldArcChartSource hx
      · exact hActualReplacementArcSource (hActualReplacementPathRange ▸ hx)
    have hActualBoundaryNormalizedSphere (x : S)
        (hx : x ∈ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath) :
        actualJordanGlobal.symm (Edisk x) ∈ Metric.sphere (0 : Plane) 1 := by
      have hm : Edisk x ∈ actualOldNewPlanarBoundary := by
        rcases hx with hx | hx
        · exact Or.inl ⟨x,hx,rfl⟩
        · exact Or.inr ⟨x,hx,rfl⟩
      rw [←hActualJordanGlobalBoundary] at hm
      obtain ⟨q,hq,he⟩ := hm
      rw [←he,actualJordanGlobal.symm_apply_apply]
      exact hq
    have hActualLeftEndOld : γ actualSelectedExtensionLeft ∈ Set.range actualExtendedOldArc :=
      ⟨0,actualExtendedOldArc.source⟩
    have hActualRightEndOld : γ actualSelectedExtensionRight ∈ Set.range actualExtendedOldArc :=
      ⟨1,actualExtendedOldArc.target⟩
    have hActualLeftEndRetained : γ actualSelectedExtensionLeft ∈ Set.range actualRetainedRemainder :=
      ⟨1,hActualRetainedRemainderEnd⟩
    have hActualRightEndRetained : γ actualSelectedExtensionRight ∈ Set.range actualRetainedRemainder :=
      ⟨0,actualRetainedRemainder.source⟩
    have hActualRetainedBoundaryForbidden (x : S)
        (hxS : x ∈ Edisk.source) (hxR : x ∈ Set.range actualRetainedRemainder) :
        actualJordanGlobal.symm (Edisk x) ∉ actualNormalizedRetainedFreeDomain := by
      rintro ⟨y,hy,he⟩
      rw [actualJordanGlobal.apply_symm_apply] at he
      have hyx : y = x := Edisk.injOn hy.1 hxS he
      exact hy.2 (hyx.symm ▸ hxR)
    have hActualNormalizedForbiddenNonempty : actualNormalizedRetainedFreeDomainᶜ.Nonempty :=
      ⟨actualNormalizedLeftEnd,hActualRetainedBoundaryForbidden _
        (hActualExtendedOldArcChartSource hActualLeftEndOld) hActualLeftEndRetained⟩
    have hActualProperEndFixed (x : S)
        (hx : x ∈ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath)
        (hxR : x ∈ Set.range actualRetainedRemainder) :
        actualRadialSupport (actualJordanGlobal.symm (Edisk x)) =
          actualJordanGlobal.symm (Edisk x) := by
      apply hActualRadialFixedForbidden
      · exact hActualRetainedBoundaryForbidden x (hActualOldNewBoundarySource hx) hxR
      · simpa only [Metric.mem_sphere,dist_zero_right] using hActualBoundaryNormalizedSphere x hx
    have hActualBoundaryOffEndsRetainedFree (x : S)
        (hx : x ∈ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath)
        (hxe : x ∉ ({γ actualSelectedExtensionLeft,γ actualSelectedExtensionRight} : Set S)) :
        x ∉ Set.range actualRetainedRemainder := by
      intro hxR
      rcases hx with hx | hx
      · exact hxe (hActualSelectedRemainderMeet ▸ ⟨hx,hxR⟩)
      · have hm := hActualReplacementSelectedMeet
          ⟨hActualReplacementPathRange ▸ hx,hActualRetainedSelected hxR⟩
        rw [hActualReplacementStartSet] at hm
        exact hxe hm
    have hActualProperCrosscutInterior (x : S)
        (hx : x ∈ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath)
        (hxe : x ∉ ({γ actualSelectedExtensionLeft,γ actualSelectedExtensionRight} : Set S)) :
        x ∈ interior (Set.range actualProperSupportDisk) := by
      let q := actualJordanGlobal.symm (Edisk x)
      have hqSphere : q ∈ Metric.sphere (0 : Plane) 1 := hActualBoundaryNormalizedSphere x hx
      have hxS := hActualOldNewBoundarySource hx
      have hqO : q ∈ actualNormalizedRetainedFreeDomain :=
        ⟨x,⟨hxS,hActualBoundaryOffEndsRetainedFree x hx hxe⟩,
          (actualJordanGlobal.apply_symm_apply (Edisk x)).symm⟩
      have hqInt : actualRadialSupport.symm q ∈ Metric.ball (0 : Plane) 1 :=
        actual_distance_radial_boundary_inside actualNormalizedRetainedFreeDomain
          hActualNormalizedDomainOpen hActualNormalizedForbiddenNonempty actualRadialSupport
          hActualRadialSupport q hqO (by simpa only [Metric.mem_sphere,dist_zero_right] using hqSphere)
      rw [embedded_surface_disk_interior_eq actualProperSupportDisk hActualProperSupportDisk]
      refine ⟨⟨actualRadialSupport.symm q,Metric.ball_subset_closedBall hqInt⟩,hqInt,?_⟩
      change Edisk.symm (actualJordanGlobal (actualRadialSupport (actualRadialSupport.symm q))) = x
      rw [actualRadialSupport.apply_symm_apply]
      dsimp only [q]
      rw [actualJordanGlobal.apply_symm_apply,Edisk.left_inv hxS]
    obtain ⟨actualSquareBallGauge,hActualSquareGaugeInterior,hActualSquareGaugeClosed,hActualSquareGaugeFrontier⟩ :=
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall
        (Plane.convex_closedSquare 0 1)
        (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
        (Plane.isBounded_closedSquare 0 1)
    have hActualSquareGaugeOpen : actualSquareBallGauge '' Plane.openSquare 0 1 =
        Metric.ball (0 : Plane) 1 := by
      simpa only [Plane.interior_closedSquare] using hActualSquareGaugeInterior
    have hActualSquareGaugeClosedBall : actualSquareBallGauge '' Plane.closedSquare 0 1 =
        Metric.closedBall (0 : Plane) 1 := by
      simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hActualSquareGaugeClosed
    have hActualSquareGaugeBoundary : actualSquareBallGauge '' modelCurve = Metric.sphere (0 : Plane) 1 := by
      simpa only [←modelCurve_eq_frontier] using hActualSquareGaugeFrontier
    let actualSquarePlaneCoordinates :=
      (actualSquareBallGauge.trans actualRadialSupport).trans actualJordanGlobal
    let actualSurgerySquareChart := Edisk.trans actualSquarePlaneCoordinates.symm.toOpenPartialHomeomorph
    have hActualSurgerySquareSource : actualSurgerySquareChart.source = Edisk.source := by
      simp [actualSurgerySquareChart,OpenPartialHomeomorph.trans_source]
    have hActualSurgerySquareTarget : actualSurgerySquareChart.target =
        actualSquarePlaneCoordinates ⁻¹' Edisk.target := by
      simp [actualSurgerySquareChart,OpenPartialHomeomorph.trans_target]
    have hActualSurgerySquareClosed : Plane.closedSquare 0 1 ⊆ actualSurgerySquareChart.target := by
      rw [hActualSurgerySquareTarget]
      intro q hq
      have hb : actualSquareBallGauge q ∈ Metric.closedBall (0 : Plane) 1 := by
        rw [←hActualSquareGaugeClosedBall]
        exact Set.mem_image_of_mem actualSquareBallGauge hq
      exact hActualRadialClosedChart ⟨actualSquareBallGauge q,hb,rfl⟩
    have hActualSurgerySquareValue (x : S) : actualSurgerySquareChart x =
        actualSquareBallGauge.symm (actualRadialSupport.symm (actualJordanGlobal.symm (Edisk x))) := rfl
    have hActualSurgerySquareOffEnds (x : S)
        (hx : x ∈ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath)
        (hxe : x ∉ ({γ actualSelectedExtensionLeft,γ actualSelectedExtensionRight} : Set S)) :
        actualSurgerySquareChart x ∈ Plane.openSquare 0 1 := by
      let q := actualJordanGlobal.symm (Edisk x)
      have hqSphere : q ∈ Metric.sphere (0 : Plane) 1 := hActualBoundaryNormalizedSphere x hx
      have hqO : q ∈ actualNormalizedRetainedFreeDomain :=
        ⟨x,⟨hActualOldNewBoundarySource hx,hActualBoundaryOffEndsRetainedFree x hx hxe⟩,
          (actualJordanGlobal.apply_symm_apply (Edisk x)).symm⟩
      have hqInt := actual_distance_radial_boundary_inside actualNormalizedRetainedFreeDomain
        hActualNormalizedDomainOpen hActualNormalizedForbiddenNonempty actualRadialSupport
        hActualRadialSupport q hqO (by simpa only [Metric.mem_sphere,dist_zero_right] using hqSphere)
      rw [←hActualSquareGaugeOpen] at hqInt
      obtain ⟨z,hz,he⟩ := hqInt
      rw [hActualSurgerySquareValue]
      change actualSquareBallGauge.symm (actualRadialSupport.symm q) ∈ Plane.openSquare 0 1
      rw [←he,actualSquareBallGauge.symm_apply_apply]
      exact hz
    have hActualSurgerySquareRetainedAvoidance (x : S) (hxR : x ∈ Set.range actualRetainedRemainder)
        (hxS : x ∈ actualSurgerySquareChart.source) :
        actualSurgerySquareChart x ∉ Plane.openSquare 0 1 := by
      intro hxO
      have hxES : x ∈ Edisk.source := hActualSurgerySquareSource ▸ hxS
      have hqBall : actualSquareBallGauge (actualSurgerySquareChart x) ∈ Metric.ball (0 : Plane) 1 := by
        rw [←hActualSquareGaugeOpen]
        exact Set.mem_image_of_mem actualSquareBallGauge hxO
      rw [hActualSurgerySquareValue,actualSquareBallGauge.apply_symm_apply] at hqBall
      have hfree := hActualRadialOpenAvoidance
        ⟨actualRadialSupport.symm (actualJordanGlobal.symm (Edisk x)),hqBall,rfl⟩
      rw [actualRadialSupport.apply_symm_apply] at hfree
      exact hActualRetainedBoundaryForbidden x hxES hxR hfree
    let actualSquareOldArc : Set Plane := actualSurgerySquareChart '' Set.range actualExtendedOldArc
    let actualSquareNewArc : Set Plane := actualSurgerySquareChart '' Set.range actualReplacementPath
    let actualSquareLeftEnd := actualSurgerySquareChart (γ actualSelectedExtensionLeft)
    let actualSquareRightEnd := actualSurgerySquareChart (γ actualSelectedExtensionRight)
    have hActualSquareOldArc : IsArcBetween actualSquareOldArc actualSquareLeftEnd actualSquareRightEnd := by
      let A : C(Interval,S) := ⟨actualExtendedOldArc,actualExtendedOldArc.continuous⟩
      have hh := actual_chart_continuous_arc actualSurgerySquareChart A hActualExtendedOldArc
        (fun t => hActualSurgerySquareSource.symm ▸ hActualExtendedOldArcChartSource ⟨t,rfl⟩)
      change IsArcBetween (actualSurgerySquareChart '' Set.range actualExtendedOldArc)
        (actualSurgerySquareChart (actualExtendedOldArc 0))
        (actualSurgerySquareChart (actualExtendedOldArc 1)) at hh
      rw [actualExtendedOldArc.source,actualExtendedOldArc.target] at hh
      exact hh
    have hActualSquareNewArc : IsArcBetween actualSquareNewArc actualSquareLeftEnd actualSquareRightEnd := by
      let B : C(Interval,S) := ⟨actualReplacementPath,actualReplacementPath.continuous⟩
      have hh := actual_chart_continuous_arc actualSurgerySquareChart B hActualReplacementPath
        (fun t => hActualSurgerySquareSource.symm ▸
          hActualReplacementArcSource (hActualReplacementPathRange ▸ (show actualReplacementPath t ∈ Set.range actualReplacementPath from ⟨t,rfl⟩)))
      change IsArcBetween (actualSurgerySquareChart '' Set.range actualReplacementPath)
        (actualSurgerySquareChart (actualReplacementPath 0))
        (actualSurgerySquareChart (actualReplacementPath 1)) at hh
      rw [actualReplacementPath.source,actualReplacementPath.target] at hh
      exact hh
    have hActualSquareEndBoundary (x : S)
        (hx : x ∈ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath)
        (hxR : x ∈ Set.range actualRetainedRemainder) :
        actualSurgerySquareChart x ∈ modelCurve := by
      have he := hActualProperEndFixed x hx hxR
      have he' := congrArg actualRadialSupport.symm he
      simp only [actualRadialSupport.symm_apply_apply] at he'
      rw [hActualSurgerySquareValue,←he']
      have hs := hActualBoundaryNormalizedSphere x hx
      rw [←hActualSquareGaugeBoundary] at hs
      obtain ⟨q,hq,heq⟩ := hs
      rw [←heq,actualSquareBallGauge.symm_apply_apply]
      exact hq
    have hActualSquareLeftBoundary : actualSquareLeftEnd ∈ modelCurve :=
      hActualSquareEndBoundary _ (Or.inl hActualLeftEndOld) hActualLeftEndRetained
    have hActualSquareRightBoundary : actualSquareRightEnd ∈ modelCurve :=
      hActualSquareEndBoundary _ (Or.inl hActualRightEndOld) hActualRightEndRetained
    have hActualSquareArcProper (A : Set S)
        (hA : A ⊆ Set.range actualExtendedOldArc ∪ Set.range actualReplacementPath) :
        actualSurgerySquareChart '' A \ {actualSquareLeftEnd,actualSquareRightEnd} ⊆ Plane.openSquare 0 1 := by
      rintro y ⟨⟨x,hx,rfl⟩,hye⟩
      apply hActualSurgerySquareOffEnds x (hA hx)
      intro hxe
      apply hye
      rcases hxe with hxe | hxe
      · left; rw [hxe]
      · right; rw [hxe]; rfl
    let actualSquareSurfaceHomeomorph := actualSurgerySquareChart.toHomeomorphSourceTarget
    obtain ⟨actualSourceSurgeryIsotopy,hActualSourceSquareMove,hActualSourceSquareFix⟩ :=
      position_crosscut_surface_square_support S actualSurgerySquareChart.source
        actualSurgerySquareChart.target actualSurgerySquareChart.open_source actualSquareSurfaceHomeomorph
        hActualSurgerySquareClosed actualSquareOldArc actualSquareNewArc
        actualSquareLeftEnd actualSquareRightEnd hActualSquareOldArc hActualSquareNewArc
        hActualSquareLeftBoundary hActualSquareRightBoundary
        (hActualSquareArcProper _ Set.subset_union_left)
        (hActualSquareArcProper _ Set.subset_union_right)
    have hActualSourceSurgeryFixRetained : ∀ t x, x ∈ Set.range actualRetainedRemainder →
        actualSourceSurgeryIsotopy.map (t,x) = x := by
      intro t x hx
      apply hActualSourceSquareFix t x
      rintro ⟨u,hu,hui⟩
      subst x
      exact hActualSurgerySquareRetainedAvoidance u.val hx u.property hui
    have hActualSourceSurgeryFixOutsideV : ∀ t x, x ∉ V →
        actualSourceSurgeryIsotopy.map (t,x) = x := by
      intro t x hx
      apply hActualSourceSquareFix t x
      rintro ⟨u,hu,hui⟩
      apply hx
      rw [←hu]
      have hs : u.val ∈ interior (Set.range dlarge) := by
        rw [←hEdiskSource,←hActualSurgerySquareSource]
        exact u.property
      exact (hDiskInWK (interior_subset hs)).1
    have hActualSquareSurfaceOldRange :
        {x : S | ∃ u : actualSurgerySquareChart.source, u.val = x ∧
          (actualSquareSurfaceHomeomorph u : Plane) ∈ actualSquareOldArc} = Set.range actualExtendedOldArc := by
      ext x; constructor
      · rintro ⟨u,rfl,y,hy,he⟩
        have hs := hActualOldNewBoundarySource (Or.inl hy)
        have hyu : y = u.val := actualSurgerySquareChart.injOn
          (hActualSurgerySquareSource.symm ▸ hs) u.property he
        exact hyu ▸ hy
      · intro hx
        exact ⟨⟨x,hActualSurgerySquareSource.symm ▸ hActualExtendedOldArcChartSource hx⟩,rfl,x,hx,rfl⟩
    have hActualSquareSurfaceNewRange :
        {x : S | ∃ u : actualSurgerySquareChart.source, u.val = x ∧
          (actualSquareSurfaceHomeomorph u : Plane) ∈ actualSquareNewArc} = Set.range actualReplacementPath := by
      ext x; constructor
      · rintro ⟨u,rfl,y,hy,he⟩
        have hs := hActualOldNewBoundarySource (Or.inr hy)
        have hyu : y = u.val := actualSurgerySquareChart.injOn
          (hActualSurgerySquareSource.symm ▸ hs) u.property he
        exact hyu ▸ hy
      · intro hx
        exact ⟨⟨x,hActualSurgerySquareSource.symm ▸ hActualOldNewBoundarySource (Or.inr hx)⟩,rfl,x,hx,rfl⟩
    rw [hActualSquareSurfaceOldRange,hActualSquareSurfaceNewRange] at hActualSourceSquareMove
    obtain ⟨actualSourceFinalHomeomorph,hActualSourceFinalHomeomorph⟩ :=
      actualSourceSurgeryIsotopy.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    let actualChangedCurve := homeomorphCurve actualSourceFinalHomeomorph (r v).val
    have hActualSourceFinalMap : (actualSourceFinalHomeomorph : S → S) = actualSourceSurgeryIsotopy.finalMap :=
      funext hActualSourceFinalHomeomorph
    have hActualChangedImageTransport : actualChangedCurve.image =
        actualSourceSurgeryIsotopy.finalMap '' (r v).val.image := by
      change Set.range (actualSourceFinalHomeomorph ∘ (r v).val.map) = _
      rw [Set.range_comp,hActualSourceFinalMap]
      rfl
    have hActualRetainedFinalImage : actualSourceSurgeryIsotopy.finalMap '' Set.range actualRetainedRemainder =
        Set.range actualRetainedRemainder := by
      ext x; constructor
      · rintro ⟨y,hy,rfl⟩
        change actualSourceSurgeryIsotopy.map ((⟨1,by norm_num⟩ : Interval),y) ∈ Set.range actualRetainedRemainder
        rw [hActualSourceSurgeryFixRetained (⟨1,by norm_num⟩ : Interval) y hy]
        exact hy
      · intro hx
        exact ⟨x,hx,hActualSourceSurgeryFixRetained (⟨1,by norm_num⟩ : Interval) x hx⟩
    have hActualChangedSourceImage : actualChangedCurve.image =
        Set.range actualReplacementPath ∪ Set.range actualRetainedRemainder := by
      rw [hActualChangedImageTransport,hActualSelectedExactDecomposition,Set.image_union,
        hActualSourceSquareMove,hActualRetainedFinalImage]
    have hActualChangedEssential : Essential actualChangedCurve := by
      apply (essential_isotopy_invariant (show AmbientIsotopy.Rel (r v).val.image actualChangedCurve.image from
        ⟨actualSourceSurgeryIsotopy,hActualChangedImageTransport.symm⟩)).mp
      exact (r v).property
    have hActualCornerStartsAvoidFamily (i : I) (hi : i ≠ v) :
        cornerArcU 0 ∉ (r i).val.image ∧ cornerArcZ 0 ∉ (r i).val.image := by
      have hu : cornerArcU 0 ∈ Ucorner := hSurfaceConnectorUSub (by
        have hm : cornerArcU 0 ∈ Set.range cornerArcU := ⟨0,rfl⟩
        rw [hCornerRangeU] at hm
        exact hm)
      have hz : cornerArcZ 0 ∈ Zcorner := hSurfaceConnectorZSub (by
        have hm : cornerArcZ 0 ∈ Set.range cornerArcZ := ⟨0,rfl⟩
        rw [hCornerRangeZ] at hm
        exact hm)
      constructor
      · intro hui
        have he : cornerArcU 0 = u := Set.mem_singleton_iff.mp
          (hUContacts v i (Ne.symm hi) ⟨hu,hCornerStartCurveU,hui⟩)
        exact hCornerStartExteriorU ⟨0,hf0.trans he.symm⟩
      · intro hzi
        have he : cornerArcZ 0 = z := Set.mem_singleton_iff.mp
          (hZContacts v i (Ne.symm hi) ⟨hz,hCornerStartCurveZ,hzi⟩)
        exact hCornerStartExteriorZ ⟨1,hf1.trans he.symm⟩
    have hActualSourceStartsAvoidFamily (i : I) (hi : i ≠ v) :
        actualSourceLeftCornerStart ∉ (r i).val.image ∧
          actualSourceRightCornerStart ∉ (r i).val.image := by
      have hh := hActualCornerStartsAvoidFamily i hi
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerStart,actualSourceRightCornerStart,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;> first | exact hh | exact hh.symm
    have hActualExtendedEndsAvoidFamily (i : I) (hi : i ≠ v) :
        γ actualSelectedExtensionLeft ∉ (r i).val.image ∧
          γ actualSelectedExtensionRight ∉ (r i).val.image := by
      have hh := hActualSourceStartsAvoidFamily i hi
      rcases hActualSourceReplacementEndpointOrientation with ho | ho
      · simpa only [ho.1,ho.2] using hh
      · simpa only [ho.1,ho.2] using hh.symm
    have hActualRetainedThirdFinite (i : I) (hi : i ≠ v) :
        (Set.range actualRetainedRemainder ∩ (r i).val.image).Finite :=
      (hr v i (Ne.symm hi)).1.subset (fun x hx => ⟨hActualRetainedSelected hx.1,hx.2⟩)
    have hActualOldRetainedThirdDisjoint (i : I) (hi : i ≠ v) :
        Disjoint (Set.range actualExtendedOldArc ∩ (r i).val.image)
          (Set.range actualRetainedRemainder ∩ (r i).val.image) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hm := hActualSelectedRemainderMeet ▸ (show x ∈
        Set.range actualExtendedOldArc ∩ Set.range actualRetainedRemainder from ⟨hx.1,hy.1⟩)
      change x ∈ ({γ actualSelectedExtensionLeft,γ actualSelectedExtensionRight} : Set S) at hm
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hm
      rcases hm with hm | hm
      · exact (hActualExtendedEndsAvoidFamily i hi).1 (hm ▸ hx.2)
      · exact (hActualExtendedEndsAvoidFamily i hi).2 (hm ▸ hx.2)
    have hActualNewRetainedThirdDisjoint (i : I) (hi : i ≠ v) :
        Disjoint (Set.range actualReplacementPath ∩ (r i).val.image)
          (Set.range actualRetainedRemainder ∩ (r i).val.image) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hm := hActualReplacementSelectedMeet
        ⟨hActualReplacementPathRange ▸ hx.1,hActualRetainedSelected hy.1⟩
      rcases hm with hm | hm
      · exact (hActualSourceStartsAvoidFamily i hi).1 (hm ▸ hx.2)
      · exact (hActualSourceStartsAvoidFamily i hi).2 (hm ▸ hx.2)
    have hActualOldIntersectionSplit (i : I) (hi : i ≠ v) :
        ((r v).val.image ∩ (r i).val.image).ncard =
          (Set.range f ∩ (r i).val.image).ncard +
          (Set.range actualRetainedRemainder ∩ (r i).val.image).ncard := by
      rw [hActualSelectedExactDecomposition,Set.union_inter_distrib_right,
        Set.ncard_union_eq (hActualOldRetainedThirdDisjoint i hi)
          ((hr v i (Ne.symm hi)).1.subset (fun x hx =>
            ⟨hActualExtendedOldArcSelected hx.1,hx.2⟩)) (hActualRetainedThirdFinite i hi),
        hActualExtendedOldArcThirdExact i hi]
    have hActualNewIntersectionSplit (i : I) (hi : i ≠ v) :
        (actualChangedCurve.image ∩ (r i).val.image).ncard =
          (Set.range actualReplacementArc ∩ (r i).val.image).ncard +
          (Set.range actualRetainedRemainder ∩ (r i).val.image).ncard := by
      have hfinite : (Set.range actualReplacementPath ∩ (r i).val.image).Finite := by
        rw [hActualReplacementPathRange]
        exact (hActualReplacementCounts i hi).1
      rw [hActualChangedSourceImage,Set.union_inter_distrib_right,
        Set.ncard_union_eq (hActualNewRetainedThirdDisjoint i hi) hfinite (hActualRetainedThirdFinite i hi),
        hActualReplacementPathRange]
    have hActualChangedThirdFinite (i : I) (hi : i ≠ v) :
        (actualChangedCurve.image ∩ (r i).val.image).Finite := by
      rw [hActualChangedSourceImage,Set.union_inter_distrib_right,hActualReplacementPathRange]
      exact ((hActualReplacementCounts i hi).1).union (hActualRetainedThirdFinite i hi)
    have hActualOppositePairDropTwo :
        (actualChangedCurve.image ∩ (r w).val.image).ncard + 2 =
          ((r v).val.image ∩ (r w).val.image).ncard := by
      rw [hActualOldIntersectionSplit w (Ne.symm hvw),hfmeet,Set.ncard_pair huz,
        hActualNewIntersectionSplit w (Ne.symm hvw)]
      have he : Set.range actualReplacementArc ∩ (r w).val.image = ∅ :=
        Set.disjoint_iff_inter_eq_empty.mp hActualReplacementAvoidW
      rw [he,Set.ncard_empty]
      omega
    have hActualCornerIndicatorOrientation (i : I) :
        (if actualSourceLeftCornerPoint ∈ (r i).val.image then 1 else 0)+
          (if actualSourceRightCornerPoint ∈ (r i).val.image then 1 else 0) =
        (if u ∈ (r i).val.image then 1 else 0)+(if z ∈ (r i).val.image then 1 else 0) := by
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerPoint,actualSourceRightCornerPoint,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;> omega
    have hActualChangedThirdCountBound (i : I) (hi : i ≠ v) (hiw : i ≠ w) :
        (actualChangedCurve.image ∩ (r i).val.image).ncard ≤
          ((Set.range g \ {u,z}) ∩ (r i).val.image).ncard +
          (if u ∈ (r i).val.image then 1 else 0)+(if z ∈ (r i).val.image then 1 else 0)+
          (Set.range actualRetainedRemainder ∩ (r i).val.image).ncard := by
      rw [hActualNewIntersectionSplit i hi]
      have hb := (hActualReplacementCounts i hi).2
      rw [hActualSourceContactIncidenceCount i hiw] at hb
      have hc := hActualCornerIndicatorOrientation i
      omega
    let actualChangedEssentialCurve : EssentialCurve S := ⟨actualChangedCurve,hActualChangedEssential⟩
    let actualChangedFamily : I → EssentialCurve S := fun i => if i = v then actualChangedEssentialCurve else r i
    have hActualChangedFamilySelected : actualChangedFamily v = actualChangedEssentialCurve := by simp [actualChangedFamily]
    have hActualChangedFamilyFixed (i : I) (hi : i ≠ v) : actualChangedFamily i = r i := by
      simp [actualChangedFamily,hi]
    have hActualChangedFamilyClasses (i : I) :
        Quotient.mk (essentialCurveSetoid S) (actualChangedFamily i) =
          Quotient.mk (essentialCurveSetoid S) (r i) := by
      by_cases hi : i = v
      · subst i
        rw [hActualChangedFamilySelected]
        apply Quotient.sound
        change AmbientIsotopy.Rel actualChangedCurve.image (r v).val.image
        exact ambientIsotopy_equivalence.symm ⟨actualSourceSurgeryIsotopy,hActualChangedImageTransport.symm⟩
      · rw [hActualChangedFamilyFixed i hi]
    have hActualChangedFamilyImage : actualSourceSurgeryIsotopy.finalMap '' (r v).val.image =
        (actualChangedFamily v).val.image := by
      rw [hActualChangedFamilySelected]
      exact hActualChangedImageTransport.symm
    have hActualOneSidedSourceRowDecrease
        (hcheap : (∑ i : I, if i = v ∨ i = w then 0 else
            ((Set.range g \ {u,z}) ∩ (r i).val.image).ncard) ≤
          ∑ i : I, if i = v ∨ i = w then 0 else
            ((Set.range f \ {u,z}) ∩ (r i).val.image).ncard) :
        (∑ i : I, if v = i then 0 else
          ((actualChangedFamily v).val.image ∩ (actualChangedFamily i).val.image).ncard) <
        ∑ i : I, if v = i then 0 else ((r v).val.image ∩ (r i).val.image).ncard := by
      have hRows : (∑ i : I, if v = i then 0 else
          ((actualChangedFamily v).val.image ∩ (actualChangedFamily i).val.image).ncard) =
          ∑ i : I, if v = i then 0 else (actualChangedCurve.image ∩ (r i).val.image).ncard := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hiv : i = v
        · subst i; simp
        · rw [hActualChangedFamilySelected,hActualChangedFamilyFixed i hiv]
      rw [hRows]
      let offset : I → ℕ := fun i => (if u ∈ (r i).val.image then 1 else 0)+
        (if z ∈ (r i).val.image then 1 else 0)+
        (Set.range actualRetainedRemainder ∩ (r i).val.image).ncard
      apply actual_cheaper_side_row_drop v w hvw
        (fun i => ((r v).val.image ∩ (r i).val.image).ncard)
        (fun i => (actualChangedCurve.image ∩ (r i).val.image).ncard)
        (fun i => ((Set.range f \ {u,z}) ∩ (r i).val.image).ncard)
        (fun i => ((Set.range g \ {u,z}) ∩ (r i).val.image).ncard) offset
        hActualOppositePairDropTwo
      · intro i hiv hiw
        rw [hActualOldIntersectionSplit i hiv]
        have hFinite : (Set.range f ∩ (r i).val.image).Finite :=
          (hr v i (Ne.symm hiv)).1.subset (fun x hx => ⟨hfcurve hx.1,hx.2⟩)
        have hsplit := actual_arc_endpoint_incidence_split (Set.range f) (r i).val.image u z huz
          (show u ∈ Set.range f from ⟨0,hf0⟩) (show z ∈ Set.range f from ⟨1,hf1⟩) hFinite
        dsimp [offset]
        omega
      · intro i hiv hiw
        have hb := hActualChangedThirdCountBound i hiv hiw
        dsimp [offset]
        omega
      · exact hcheap
    obtain ⟨actualCoreParameter,hActualCoreParameter,actualConnectorSet,hActualConnectorClosed,
      hActualConnectorFree,hActualReplacementCoreCover⟩ := hActualReplacementGeometryCover
    have hActualContactCoreWitness (p : Pg) :=
      hActualCornerSafeParameterizedContactProducer p actualCoreParameter hActualCoreParameter
    choose actualCoreContactArcs hActualCoreContactEmb hActualCoreContact0 hActualCoreContact1
      hActualCoreContactSub hActualCoreContactK hActualCoreContactCorners hActualCoreContactSign
      hActualCoreContactW hActualCoreContactCounts hActualCoreContactRange using hActualContactCoreWitness
    have hActualContactCoreClosed (p : Pg) : IsClosed (actualSafeContactCore p actualCoreParameter) := by
      rw [←hActualCoreContactRange p]
      exact (isCompact_range (actualCoreContactArcs p).continuous).isClosed
    have hActualContactCoreSupport (p : Pg) : actualSafeContactCore p actualCoreParameter ⊆ W p := by
      rw [←hActualCoreContactRange p]
      exact hActualCoreContactSub p
    have hActualContactCoreCornerAvoid (p : Pg) :
        Disjoint (actualSafeContactCore p actualCoreParameter) actualCompactCorners := by
      rw [←hActualCoreContactRange p]
      exact hActualCoreContactCorners p
    obtain ⟨actualCoreLeft,hActualCoreLeft,hActualCoreLeft0,hActualCoreLeft1,hActualCoreLeftSub,
      hActualCoreLeftMeet,hActualCoreLeftW,hActualCoreLeftK,hActualCoreLeftCounts,hActualCoreLeftRange⟩ :=
      hActualSourceLeftCornerArcProducer actualCoreParameter hActualCoreParameter
    obtain ⟨actualCoreRight,hActualCoreRight,hActualCoreRight0,hActualCoreRight1,hActualCoreRightSub,
      hActualCoreRightMeet,hActualCoreRightW,hActualCoreRightK,hActualCoreRightCounts,hActualCoreRightRange⟩ :=
      hActualSourceRightCornerArcProducer actualCoreParameter hActualCoreParameter
    have hActualLeftCoreClosed : IsClosed (actualSourceLeftCornerCore actualCoreParameter) := by
      rw [←hActualCoreLeftRange]
      exact (isCompact_range actualCoreLeft.continuous).isClosed
    have hActualRightCoreClosed : IsClosed (actualSourceRightCornerCore actualCoreParameter) := by
      rw [←hActualCoreRightRange]
      exact (isCompact_range actualCoreRight.continuous).isClosed
    have hActualLeftCoreCompactSupport : actualSourceLeftCornerCore actualCoreParameter ⊆ actualCompactCorners := by
      rw [←hActualCoreLeftRange]
      exact hActualCoreLeftSub
    have hActualRightCoreCompactSupport : actualSourceRightCornerCore actualCoreParameter ⊆ actualCompactCorners := by
      rw [←hActualCoreRightRange]
      exact hActualCoreRightSub
    have hActualCornerCoreDisjoint : Disjoint (actualSourceLeftCornerCore actualCoreParameter)
        (actualSourceRightCornerCore actualCoreParameter) := by
      have hCompactDisjoint := hCornersDisjoint.mono
        hActualCompactCornerSupportSubsetU hActualCompactCornerSupportSubsetZ
      have hU := hActualSafeCornerArcRangeU actualCoreParameter
      have hZ := hActualSafeCornerArcRangeZ actualCoreParameter
      cases hβ : βgU <;>
        simp only [actualSourceLeftCornerCore,actualSourceRightCornerCore,hβ,
          Bool.false_eq_true,ite_false,ite_true] <;>
        first | exact hCompactDisjoint.mono hU hZ | exact hCompactDisjoint.symm.mono hZ hU
    have hActualContactCorePairwiseDisjoint (j k : Fin contactCoordinates.card) (hjk : j ≠ k) :
        Disjoint (actualSafeContactCore (actualSourceContactLabel j) actualCoreParameter)
          (actualSafeContactCore (actualSourceContactLabel k) actualCoreParameter) := by
      apply (hWDisjoint (actualSourceContactLabel j) (actualSourceContactLabel k)
        (fun he => hjk (hActualSourceContactLabelInjective he))).mono
        (hActualContactCoreSupport _) (hActualContactCoreSupport _)
    let actualCorePieceIndex := Option (Bool ⊕ Fin contactCoordinates.card)
    let actualCorePiece : actualCorePieceIndex → Set S := fun j => match j with
      | none => actualConnectorSet
      | some (Sum.inl false) => actualSourceLeftCornerCore actualCoreParameter
      | some (Sum.inl true) => actualSourceRightCornerCore actualCoreParameter
      | some (Sum.inr j) => actualSafeContactCore (actualSourceContactLabel j) actualCoreParameter
    have hActualCorePieceClosed (j : actualCorePieceIndex) : IsClosed (actualCorePiece j) := by
      cases j with
      | none => exact hActualConnectorClosed
      | some j => cases j with
        | inl j => cases j <;> first | exact hActualLeftCoreClosed | exact hActualRightCoreClosed
        | inr j => exact hActualContactCoreClosed _
    have hActualCorePieceCover : Set.range actualReplacementArc ⊆ ⋃ j,actualCorePiece j := by
      intro x hx
      rcases hActualReplacementCoreCover hx with hxCore | hxGap
      · rcases hxCore with hxL | hxC | hxR
        · exact Set.mem_iUnion.mpr ⟨some (Sum.inl false),hxL⟩
        · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hxC
          exact Set.mem_iUnion.mpr ⟨some (Sum.inr j),hj⟩
        · exact Set.mem_iUnion.mpr ⟨some (Sum.inl true),hxR⟩
      · exact Set.mem_iUnion.mpr ⟨none,hxGap⟩
    have hActualCorePieceUnique (i : I) (p : S) (hp : p ∈ (r i).val.image)
        (j k : actualCorePieceIndex) (hj : p ∈ actualCorePiece j) (hk : p ∈ actualCorePiece k) : j = k := by
      cases j with
      | none => exact False.elim (Set.disjoint_left.mp (hActualConnectorFree i) hj hp)
      | some j => cases k with
        | none => exact False.elim (Set.disjoint_left.mp (hActualConnectorFree i) hk hp)
        | some k =>
          congr 1
          cases j with
          | inl j => cases k with
            | inl k =>
              cases j <;> cases k <;> first
                | rfl
                | exact False.elim (Set.disjoint_left.mp hActualCornerCoreDisjoint hj hk)
                | exact False.elim (Set.disjoint_left.mp hActualCornerCoreDisjoint hk hj)
            | inr k =>
              have hpCorner : p ∈ actualCompactCorners := by
                cases j <;> first | exact hActualLeftCoreCompactSupport hj | exact hActualRightCoreCompactSupport hj
              exact False.elim (Set.disjoint_left.mp (hActualContactCoreCornerAvoid _) hk hpCorner)
          | inr j => cases k with
            | inl k =>
              have hpCorner : p ∈ actualCompactCorners := by
                cases k <;> first | exact hActualLeftCoreCompactSupport hk | exact hActualRightCoreCompactSupport hk
              exact False.elim (Set.disjoint_left.mp (hActualContactCoreCornerAvoid _) hj hpCorner)
            | inr k =>
              by_cases he : j = k
              · exact congrArg Sum.inr he
              · exact False.elim (Set.disjoint_left.mp (hActualContactCorePairwiseDisjoint j k he) hj hk)
    have hActualSourceContactCoreCrossingChart (j : Fin contactCoordinates.card) (i : I)
        (hiw : i ≠ w) (p : S)
        (hp : p ∈ actualSafeContactCore (actualSourceContactLabel j) actualCoreParameter ∩ (r i).val.image) :
        ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), ∃ t α k : ℝ,
          p ∈ E.source ∧
          (∀ x ∈ actualSafeContactCore (actualSourceContactLabel j) actualCoreParameter ∩ E.source, (E x).2 = t) ∧
          (∀ x ∈ E.source, x ∈ (r i).val.image ↔ (E x).1 = α+k*((E x).2-t)) := by
      let label := actualSourceContactLabel j
      have hIncident : label.val ∈ (r i).val.image := by
        by_contra hn
        exact Set.disjoint_left.mp (hQNon label i hn)
          ((hW label).2.2 (hActualContactCoreSupport label hp.1)) hp.2
      obtain ⟨a,b,ha,hb,hModel⟩ := hContactPatchActualRadialModel label i hiw hIncident
      let h := (actualCornerSafeContactHeight label/2)*actualCoreParameter.val
      have hh : 0 < h := mul_pos (half_pos (hActualCornerSafeContactHeight label)) hActualCoreParameter
      have hhSafe : h < actualCornerSafeContactHeight label := by
        dsimp [h]
        nlinarith only [actualCoreParameter.property.2,hActualCornerSafeContactHeight label]
      have hhOriginal : h < contactPatchHeight label :=
        hhSafe.trans (hActualCornerSafeContactHeightBound label)
      let seg := segment ℝ (Plane.mk (-actualCornerSafeContactWidth label) h)
        (Plane.mk (actualCornerSafeContactWidth label) h)
      have hTarget : seg ⊆ (contactPatchChart label).target :=
        fun q hq => (hActualCornerSafeContactPlane label h hh hhSafe hq).1
      have hBall : seg ⊆ Metric.ball (0 : Plane) (contactPatchRadius label) := by
        apply Set.Subset.trans (actual_horizontal_contact_subsegment (contactPatchHalfWidth label)
          (actualCornerSafeContactWidth label) h (hContactPatchHalfWidth label)
          (hActualCornerSafeContactWidth label) (hActualCornerSafeContactOriginalWidthBound label))
        exact hContactPatchActualBallContainment label h hh hhOriginal
      have hpCore : p ∈ (contactPatchChart label).symm '' seg := hp.1
      have hpn : ‖(contactPatchChart label) p‖ < contactPatchRadius label := by
        obtain ⟨q,hq,he⟩ := hpCore
        rw [←he,(contactPatchChart label).right_inv (hTarget hq)]
        simpa only [Metric.mem_ball,dist_zero_right] using hBall hq
      obtain ⟨E,hpE,hES,hValue,hLine,hAxis⟩ := actual_positive_radial_horizontal_piece_chart
        (contactPatchChart label) (r i).val a b (contactPatchRadius label) ha hb hModel
        (actualCornerSafeContactWidth label) h hh hTarget p hpCore hp.2 hpn
      exact ⟨E,h,(a 0/a 1)*h,a 0/a 1,hpE,hLine,hAxis⟩
    have hActualSourceUCornerCoreCrossingChart (i : I) (hiv : i ≠ v) (p : S)
        (hp : p ∈ actualSafeCornerCoreU actualCoreParameter ∩ (r i).val.image) :
        ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), ∃ t α k : ℝ,
          p ∈ E.source ∧
          (∀ x ∈ actualSafeCornerCoreU actualCoreParameter ∩ E.source, (E x).2 = t) ∧
          (∀ x ∈ E.source, x ∈ (r i).val.image ↔ (E x).1 = α+k*((E x).2-t)) := by
      let ε := endpointScaleU*(actualSafeCornerParameterU actualCoreParameter).val
      have hε : 0 < ε := by
        change 0 < endpointScaleU*(actualSafeCornerScaleU*actualCoreParameter.val)
        exact mul_pos hEndpointScaleU (mul_pos hActualSafeCornerScaleU hActualCoreParameter)
      have hεsmall : ε < cornerToleranceU :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleU.le
          (actualSafeCornerParameterU actualCoreParameter).property.2) hEndpointScaleBoundU
      have hpCore : p ∈ nearCornerSurfaceU ε := hp.1
      have hpU : p ∈ Ucorner := hNearCornerSubU ε hε hεsmall hpCore
      have hIncident : u ∈ (r i).val.image := by
        by_contra hn
        exact Set.disjoint_left.mp (hUNonincident i hn) hpU hp.2
      let j : KU := ⟨eU ⟨i,hIncident⟩,by simpa using hiv⟩
      have hModel : ∀ x ∈ FU.source, ‖FU x‖ < ρU →
          (x ∈ (r i).val.image ↔ FU x ∈ segment ℝ (0 : Plane) (aU j) ∪ segment ℝ (0 : Plane) (bU j)) := by
        intro x hx hn
        rw [hUnionU j]
        simpa [j] using hFUModel j.val x hx hn
      obtain ⟨q,hq,hqp⟩ := hpCore
      have hTarget := (hNearCornerCoreU ε hε hεsmall hq).1
      have hpF : p ∈ FU.source := hqp ▸ FU.map_target hTarget
      have hFp : FU p = q := by rw [←hqp,FU.right_inv hTarget]
      have hpn : ‖FU p‖ < ρU := by
        rw [hFp]
        simpa only [Metric.mem_ball,dist_zero_right] using (hNearCornerCoreU ε hε hεsmall hq).2
      have hpy : FU p 1 ≠ 0 := by
        intro hy0
        have hqy : q 1 = 0 := by rw [←hFp]; exact hy0
        change q ∈ segment ℝ (Plane.mk (-δU) 0) (Plane.mk (FU germU 0-ε) (FU germU 1)) at hq
        rw [segment_eq_image'] at hq
        obtain ⟨s,hs,he⟩ := hq
        have hsy := congrArg (fun q : Plane => q 1) he
        change 0+s*(FU germU 1-0) = q 1 at hsy
        rw [hqy] at hsy
        have hs0 : s = 0 := (mul_eq_zero.mp (by simpa using hsy)).resolve_right hGermUY
        have hqstart : q = Plane.mk (-δU) 0 := by
          rw [hs0] at he
          simpa using he.symm
        have hpstart : p = cornerArcU 0 := by
          rw [←hqp,hqstart,←hCornerStartU]
        exact (hActualCornerStartsAvoidFamily i hiv).1 (hpstart ▸ hp.2)
      obtain ⟨E,α,k,hpE,hES,hValue,hLine,hAxis⟩ := actual_signed_radial_fan_piece_chart
        FU (r i).val (aU j) (bU j) ρU (haU j) (hbU j) hModel
        (-δU) (FU germU 0-ε) (FU germU 1) (neg_ne_zero.mpr (ne_of_gt hδU)) hGermUY
        (fun q hq => (hNearCornerCoreU ε hε hεsmall hq).1) p hp.1 hp.2 hpn hpy
      refine ⟨E,0,α,k,hpE,hLine,?_⟩
      intro x hx
      simpa only [sub_zero] using hAxis x hx
    have hActualSourceZCornerCoreCrossingChart (i : I) (hiv : i ≠ v) (p : S)
        (hp : p ∈ actualSafeCornerCoreZ actualCoreParameter ∩ (r i).val.image) :
        ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), ∃ t α k : ℝ,
          p ∈ E.source ∧
          (∀ x ∈ actualSafeCornerCoreZ actualCoreParameter ∩ E.source, (E x).2 = t) ∧
          (∀ x ∈ E.source, x ∈ (r i).val.image ↔ (E x).1 = α+k*((E x).2-t)) := by
      let ε := endpointScaleZ*(actualSafeCornerParameterZ actualCoreParameter).val
      have hε : 0 < ε := by
        change 0 < endpointScaleZ*(actualSafeCornerScaleZ*actualCoreParameter.val)
        exact mul_pos hEndpointScaleZ (mul_pos hActualSafeCornerScaleZ hActualCoreParameter)
      have hεsmall : ε < cornerToleranceZ :=
        lt_of_le_of_lt (mul_le_of_le_one_right hEndpointScaleZ.le
          (actualSafeCornerParameterZ actualCoreParameter).property.2) hEndpointScaleBoundZ
      have hpCore : p ∈ nearCornerSurfaceZ ε := hp.1
      have hpZ : p ∈ Zcorner := hNearCornerSubZ ε hε hεsmall hpCore
      have hIncident : z ∈ (r i).val.image := by
        by_contra hn
        exact Set.disjoint_left.mp (hZNonincident i hn) hpZ hp.2
      let j : KZ := ⟨eZ ⟨i,hIncident⟩,by simpa using hiv⟩
      have hModel : ∀ x ∈ FZ.source, ‖FZ x‖ < ρZ →
          (x ∈ (r i).val.image ↔ FZ x ∈ segment ℝ (0 : Plane) (aZ j) ∪ segment ℝ (0 : Plane) (bZ j)) := by
        intro x hx hn
        rw [hUnionZ j]
        simpa [j] using hFZModel j.val x hx hn
      obtain ⟨q,hq,hqp⟩ := hpCore
      have hTarget := (hNearCornerCoreZ ε hε hεsmall hq).1
      have hpF : p ∈ FZ.source := hqp ▸ FZ.map_target hTarget
      have hFp : FZ p = q := by rw [←hqp,FZ.right_inv hTarget]
      have hpn : ‖FZ p‖ < ρZ := by
        rw [hFp]
        simpa only [Metric.mem_ball,dist_zero_right] using (hNearCornerCoreZ ε hε hεsmall hq).2
      have hpy : FZ p 1 ≠ 0 := by
        intro hy0
        have hqy : q 1 = 0 := by rw [←hFp]; exact hy0
        change q ∈ segment ℝ (Plane.mk (-δZ) 0) (Plane.mk (FZ germZ 0-ε) (FZ germZ 1)) at hq
        rw [segment_eq_image'] at hq
        obtain ⟨s,hs,he⟩ := hq
        have hsy := congrArg (fun q : Plane => q 1) he
        change 0+s*(FZ germZ 1-0) = q 1 at hsy
        rw [hqy] at hsy
        have hs0 : s = 0 := (mul_eq_zero.mp (by simpa using hsy)).resolve_right hGermZY
        have hqstart : q = Plane.mk (-δZ) 0 := by
          rw [hs0] at he
          simpa using he.symm
        have hpstart : p = cornerArcZ 0 := by
          rw [←hqp,hqstart,←hCornerStartZ]
        exact (hActualCornerStartsAvoidFamily i hiv).2 (hpstart ▸ hp.2)
      obtain ⟨E,α,k,hpE,hES,hValue,hLine,hAxis⟩ := actual_signed_radial_fan_piece_chart
        FZ (r i).val (aZ j) (bZ j) ρZ (haZ j) (hbZ j) hModel
        (-δZ) (FZ germZ 0-ε) (FZ germZ 1) (neg_ne_zero.mpr (ne_of_gt hδZ)) hGermZY
        (fun q hq => (hNearCornerCoreZ ε hε hεsmall hq).1) p hp.1 hp.2 hpn hpy
      refine ⟨E,0,α,k,hpE,hLine,?_⟩
      intro x hx
      simpa only [sub_zero] using hAxis x hx
    have hActualReplacementCarrierCrossing (i : I) (hiv : i ≠ v) (hiw : i ≠ w)
        (p : S) (hp : p ∈ Set.range actualReplacementArc ∩ (r i).val.image) :
        CrossesAt actualChangedCurve (r i).val p := by
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hActualCorePieceCover hp.1)
      have hGeometry : ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), ∃ t α k : ℝ,
          p ∈ E.source ∧ (∀ x ∈ actualCorePiece j ∩ E.source, (E x).2 = t) ∧
          (∀ x ∈ E.source, x ∈ (r i).val.image ↔ (E x).1 = α+k*((E x).2-t)) := by
        cases j with
        | none => exact False.elim (Set.disjoint_left.mp (hActualConnectorFree i) hj hp.2)
        | some j => cases j with
          | inr j => exact hActualSourceContactCoreCrossingChart j i hiw p ⟨hj,hp.2⟩
          | inl side =>
            cases side <;> cases hβ : βgU <;>
              simp only [actualCorePiece,actualSourceLeftCornerCore,actualSourceRightCornerCore,
                hβ,Bool.false_eq_true,ite_false,ite_true] at hj ⊢ <;>
              first
                | exact hActualSourceUCornerCoreCrossingChart i hiv p ⟨hj,hp.2⟩
                | exact hActualSourceZCornerCoreCrossingChart i hiv p ⟨hj,hp.2⟩
      obtain ⟨E,t,α,k,hpE,hLine,hAxis⟩ := hGeometry
      have hpR : p ∉ Set.range actualRetainedRemainder := by
        intro hR
        have hpPath : p ∈ Set.range actualReplacementPath := by
          rw [hActualReplacementPathRange]
          exact hp.1
        exact Set.disjoint_left.mp (hActualNewRetainedThirdDisjoint i hiv)
          ⟨hpPath,hp.2⟩ ⟨hR,hp.2⟩
      have hImage : actualChangedCurve.image = Set.range actualReplacementArc ∪ Set.range actualRetainedRemainder := by
        rw [hActualChangedSourceImage,hActualReplacementPathRange]
      have hEnds : actualReplacementArc 0 ∉ (r i).val.image ∧
          actualReplacementArc 1 ∉ (r i).val.image := by
        rw [hActualReplacementArc0,hActualReplacementArc1]
        exact hActualSourceStartsAvoidFamily i hiv
      exact actual_finite_carrier_replacement_crossing actualReplacementArc hActualReplacementArc
        actualChangedCurve (r i).val (Set.range actualRetainedRemainder)
        (isCompact_range actualRetainedRemainder.continuous).isClosed hImage actualCorePiece
        hActualCorePieceClosed hActualCorePieceCover p hp hpR hEnds j hj
        (fun l hl hpl => hl (hActualCorePieceUnique i p hp.2 l j hpl hj))
        E hpE t α k hLine hAxis
    have hActualChangedCurveTransverse (i : I) (hiv : i ≠ v) :
        Transverse actualChangedCurve (r i).val := by
      refine ⟨hActualChangedThirdFinite i hiv,?_⟩
      intro p hp
      have hPart : p ∈ Set.range actualReplacementPath ∪ Set.range actualRetainedRemainder :=
        hActualChangedSourceImage ▸ hp.1
      rcases hPart with hpB | hpR
      · have hpArc : p ∈ Set.range actualReplacementArc := hActualReplacementPathRange ▸ hpB
        by_cases hiw : i = w
        · subst i
          exact False.elim (Set.disjoint_left.mp hActualReplacementAvoidW hpArc hp.2)
        · exact hActualReplacementCarrierCrossing i hiv hiw p ⟨hpArc,hp.2⟩
      · have hpA : p ∉ Set.range actualExtendedOldArc := by
          intro hA
          exact Set.disjoint_left.mp (hActualOldRetainedThirdDisjoint i hiv)
            ⟨hA,hp.2⟩ ⟨hpR,hp.2⟩
        have hpB : p ∉ Set.range actualReplacementPath := by
          intro hB
          exact Set.disjoint_left.mp (hActualNewRetainedThirdDisjoint i hiv)
            ⟨hB,hp.2⟩ ⟨hpR,hp.2⟩
        exact actual_retained_replacement_crossing (r v).val actualChangedCurve (r i).val
          (Set.range actualExtendedOldArc) (Set.range actualReplacementPath) (Set.range actualRetainedRemainder)
          (isCompact_range actualExtendedOldArc.continuous).isClosed
          (isCompact_range actualReplacementPath.continuous).isClosed
          hActualSelectedExactDecomposition hActualChangedSourceImage p ⟨hpR,hp.2⟩ hpA hpB
          ((hr v i (Ne.symm hiv)).2 p ⟨hActualRetainedSelected hpR,hp.2⟩)
    have hActualChangedFamilyTransverse : ∀ i j : I, i ≠ j →
        Transverse (actualChangedFamily i).val (actualChangedFamily j).val := by
      intro i j hij
      by_cases hiv : i = v
      · subst i
        have hjv : j ≠ v := Ne.symm hij
        rw [hActualChangedFamilySelected,hActualChangedFamilyFixed j hjv]
        exact hActualChangedCurveTransverse j hjv
      · by_cases hjv : j = v
        · subst j
          rw [hActualChangedFamilySelected,hActualChangedFamilyFixed i hiv]
          exact transverse_symm_of_chart (hActualChangedCurveTransverse i hiv)
        · rw [hActualChangedFamilyFixed i hiv,hActualChangedFamilyFixed j hjv]
          exact hr i j hij
    exact ⟨v,actualSourceSurgeryIsotopy,actualChangedFamily,Or.inl rfl,
      hActualChangedFamilyFixed,hActualChangedFamilyImage,hActualSourceSurgeryFixOutsideV,
      hActualChangedFamilyClasses,hActualChangedFamilyTransverse,hActualOneSidedSourceRowDecrease hcheap⟩
  have henergy
    (A B : I → I → ℕ) (k : I)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hAkk : A k k = 0) (hBkk : B k k = 0)
    (hfixed : ∀ i j, i ≠ k → j ≠ k → B i j = A i j)
    (hrow : (∑ j, B k j) < ∑ j, A k j) :
    (∑ i, ∑ j, B i j) < ∑ i, ∑ j, A i j := by
    have hdecomp (C : I → I → ℕ) (hCsym : ∀ i j, C i j = C j i)
        (hCkk : C k k = 0) :
        (∑ i, ∑ j, C i j) =
        2 * (∑ j, C k j) + ∑ i, ∑ j, if i = k ∨ j = k then 0 else C i j := by
      have hpoint (i j : I) : C i j =
          (if i = k then C k j else 0) + (if j = k then C i k else 0) +
          (if i = k ∨ j = k then 0 else C i j) := by
        by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi,hj,hCkk]
      calc
        (∑ i, ∑ j, C i j) = ∑ i, ∑ j,
            ((if i = k then C k j else 0) + (if j = k then C i k else 0) +
            (if i = k ∨ j = k then 0 else C i j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i j
        _ = (∑ j, C k j) + (∑ i, C i k) +
            ∑ i, ∑ j, if i = k ∨ j = k then 0 else C i j := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j => if i = k then C k j else 0)]
          simp
        _ = 2 * (∑ j, C k j) + ∑ i, ∑ j, if i = k ∨ j = k then 0 else C i j := by
          have hcols : (∑ i, C i k) = ∑ i, C k i := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hCsym i k
          rw [hcols]
          omega
    have hothers : (∑ i, ∑ j, if i = k ∨ j = k then 0 else B i j) =
        ∑ i, ∑ j, if i = k ∨ j = k then 0 else A i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs with h
      · rfl
      · exact hfixed i j (fun hi => h (Or.inl hi)) (fun hj => h (Or.inr hj))
    rw [hdecomp A hAsym hAkk,hdecomp B hBsym hBkk,hothers]
    omega

  obtain ⟨k,H,r',hkw,hfixed,himage,hfix,hclass,htrans,hrow⟩ := hgeometry
  refine ⟨k,H,r',hkw,hfixed,himage,hfix,hclass,htrans,?_⟩
  let A : I → I → ℕ := fun i j => if i = j then 0 else
    ((r i).val.image ∩ (r j).val.image).ncard
  let B : I → I → ℕ := fun i j => if i = j then 0 else
    ((r' i).val.image ∩ (r' j).val.image).ncard
  have hAsym : ∀ i j, A i j = A j i := by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp only [A,ite_eq_right hij,ite_eq_right (Ne.symm hij),Set.inter_comm]
  have hBsym : ∀ i j, B i j = B j i := by
    intro i j
    by_cases hij : i = j
    · subst j; rfl
    · simp only [B,ite_eq_right hij,ite_eq_right (Ne.symm hij),Set.inter_comm]
  have hfixedCounts : ∀ i j, i ≠ k → j ≠ k → B i j = A i j := by
    intro i j hi hj
    simp only [A,B,hfixed i hi,hfixed j hj]
  exact henergy A B k hAsym hBsym (by simp [A]) (by simp [B]) hfixedCounts hrow
end CurveComplex.FiniteMinimalCompatibility
