import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualBranchCoordinateSquareFiber
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.IsolatedInvolutionStrictDerivativeNegative
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.HolomorphicInvolutionBiholomorphicBranchCoordinate
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Separation.Basic
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualLocalNegationQuotientLiteralSquareChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import CurveComplexGenusTwo.Hyperbolic.ActualConformalFoundations.ActualInvolutionGlobalSixBranchQuotientAssembly
import CurveComplexGenusTwo.Dictionary.BranchedCover
open Set Filter Topology CurveComplex
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false

theorem actual_holomorphic_six_fixed_involution_compatible_branched_double_cover {E : Type} [TopologicalSpace E] [T2Space E] [CompactSpace E]
    [ConnectedSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (f : E ≃ₜ E) (hinv : Function.Involutive f)
    (hmap : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f)
    (F : Finset E) (hfixset : (F : Set E) = {x | f x = x}) (hcard : F.card = 6) :
    ∃ (B : Type) (t : TopologicalSpace B),
      letI : TopologicalSpace B := t
      T2Space B ∧ CompactSpace B ∧ ConnectedSpace B ∧
      ∃ Q : BranchedDoubleCover E B, Q.deck = f ∧
      ∀ x (hx : Q.projection x ∈ Q.branch),
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (Q.branch_chart x hx).upstairs
          (Q.branch_chart x hx).upstairs.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (Q.branch_chart x hx).upstairs.symm
          (Q.branch_chart x hx).upstairs.target := by
  classical
  have hfinite : {x : E | f x = x}.Finite := by
    rw [← hfixset]
    exact F.finite_toSet
  obtain ⟨B,t,p,hT,hCompact,hConnected,hp,hfiber,hregular,D,hDcard,hDimage,hDfix,hDsingle,hDtwo⟩ :=
    actual_involution_global_six_branch_quotient_assembly f hinv F hfixset hcard
  letI : TopologicalSpace B := t
  letI : T2Space B := hT
  have branch_producer (q : E) (hfix : f q = q) :
    ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E)
      (c : OpenPartialHomeomorph B ℂ),
      IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧ e q = 0 ∧
      Set.MapsTo f U U ∧
      (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
      (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
      c.source = p '' U ∧ p q ∈ c.source ∧
      c.target = (fun z : ℂ => z ^ 2) '' (e '' U) ∧
      (∀ x ∈ U, c (p x) = (e x) ^ 2) := by
    have hnormal :
      ∃ (e : OpenPartialHomeomorph E ℂ) (U : Set E),
        IsOpen U ∧ q ∈ U ∧ U ⊆ e.source ∧ e q = 0 ∧
        Set.MapsTo f U U ∧
        (∀ x ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x) ∧
        (∀ w ∈ e '' U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w) ∧
        (∀ x ∈ U, e (f x) = -e x) ∧
        (∀ x ∈ U, ∀ y ∈ U,
          (e y) ^ 2 = (e x) ^ 2 ↔ y = x ∨ y = f x) := by
      let c := chartAt ℂ q
      have hq : q ∈ c.source := mem_chart_source ℂ q
      have hhol : ContDiffAt ℂ 1 (fun w => c (f (c.symm w))) (c q) := by
        have hf := (contMDiffAt_iff_of_mem_source
          (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (n := ∞)
          (x := q) (y := q) (mem_chart_source ℂ q)
          (hfix.symm ▸ mem_chart_source ℂ q)).mp (hmap q)
        have hc := hf.2
        simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ, Function.comp_def]
          using hc.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
      let G : ℂ → ℂ := fun w => c (f (c.symm w))
      have hGfix : G (c q) = c q := by simp [G, c.left_inv hq, hfix]
      have ht : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
        simpa only [c.left_inv hq] using
          (c.symm.continuousAt (c.map_source hq)).tendsto
      have hsource : ∀ᶠ w in 𝓝 (c q), c.symm w ∈ c.source :=
        ht.eventually (c.open_source.mem_nhds hq)
      have hfsource : ∀ᶠ w in 𝓝 (c q), f (c.symm w) ∈ c.source := by
        have hfq : Tendsto f (𝓝 q) (𝓝 q) := by
          simpa [hfix] using (f.continuous.continuousAt (x := q)).tendsto
        exact (hfq.comp ht).eventually (c.open_source.mem_nhds hq)
      have htarget : ∀ᶠ w in 𝓝 (c q), w ∈ c.target :=
        c.open_target.mem_nhds (c.map_source hq)
      have hGinv : ∀ᶠ w in 𝓝 (c q), G (G w) = w := by
        filter_upwards [hfsource, htarget] with w hw ht
        dsimp [G]
        rw [c.left_inv hw, hinv, c.right_inv ht]
      have hqnot : q ∉ ({x : E | f x = x} \ {q}) := by simp
      have haven : ∀ᶠ w in 𝓝 (c q),
          c.symm w ∉ ({x : E | f x = x} \ {q}) :=
        ht.eventually ((hfinite.diff (t := {q})).isClosed.isOpen_compl.mem_nhds hqnot)
      have hisolated : ∀ᶠ w in 𝓝[≠] (c q), G w ≠ w := by
        have hmem : ∀ᶠ w in 𝓝[≠] (c q), w ≠ c q := self_mem_nhdsWithin
        filter_upwards [hsource.filter_mono nhdsWithin_le_nhds,
          hfsource.filter_mono nhdsWithin_le_nhds,
          htarget.filter_mono nhdsWithin_le_nhds,
          haven.filter_mono nhdsWithin_le_nhds,hmem] with w hs hfs htg hav hn
        intro heq
        have hfx : f (c.symm w) = c.symm w :=
          c.injOn hfs hs (by change G w = c (c.symm w); rw [c.right_inv htg]; exact heq)
        have hxq : c.symm w = q := by
          by_contra hne
          exact hav ⟨hfx,hne⟩
        exact hn (by rw [← c.right_inv htg, hxq])
      have hd := hhol.hasStrictDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      have hminus : deriv G (c q) = -1 :=
        isolated_involution_strict_derivative_negative G (c q) _ hGfix hGinv hisolated hd
      have hdneg : HasStrictDerivAt G (-1) (c q) := hd.congr_deriv hminus
      obtain ⟨d,hdsource,hdzero,hdhol,hdinv,hdneg,hdsquare⟩ :=
        holomorphic_involution_biholomorphic_branch_coordinate G (c q) hGfix hGinv hdneg hhol
      let e := c.trans d
      have hzero : e q = 0 := hdzero
      have hesource : q ∈ e.source := ⟨hq,hdsource⟩
      have hcchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 c q :=
        (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ))
          (n := ∞) (IsManifold.chart_mem_maximalAtlas q) hq).of_le (by simp)
      have hehol : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e q :=
        hdhol.self_of_nhds.contMDiffAt.comp q hcchart
      have hcchartinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 c.symm (c q) :=
        (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ))
          (n := ∞) (IsManifold.chart_mem_maximalAtlas q) (c.map_source hq)).of_le (by simp)
      have hdinvzero : d.symm 0 = c q := by
        rw [← hdzero,d.left_inv hdsource]
      have heinv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm 0 := by
        have h := (hdinvzero.symm ▸ hcchartinv).comp (0 : ℂ)
          hdinv.self_of_nhds.contMDiffAt
        exact h
      have htc : Tendsto c (𝓝 q) (𝓝 (c q)) := (c.continuousAt hq).tendsto
      have heneg : ∀ᶠ x in 𝓝 q, e (f x) = -e x := by
        filter_upwards [htc.eventually hdneg,c.open_source.mem_nhds hq] with x hx hxs
        simpa [G,e,c.left_inv hxs] using hx
      have hmapnear : ∀ᶠ x in 𝓝 q, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x :=
        (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hehol
      have hinvnear : ∀ᶠ w in 𝓝 (0 : ℂ), ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm w :=
        (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp heinv
      have hemap : Tendsto e (𝓝 q) (𝓝 (0 : ℂ)) := by
        simpa [hzero] using (e.continuousAt hesource).tendsto
      have hall : ∀ᶠ x in 𝓝 q, x ∈ e.source ∧
          ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e x ∧
          ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) 1 e.symm (e x) ∧ e (f x) = -e x := by
        filter_upwards [e.open_source.mem_nhds hesource,hmapnear,
          hemap.eventually hinvnear,heneg] with x hs hm hi hn
        exact ⟨hs,hm,hi,hn⟩
      obtain ⟨O,hOsub,hOopen,hqO⟩ := eventually_nhds_iff.mp hall
      let U := O ∩ f ⁻¹' O
      have hU : IsOpen U := hOopen.inter (hOopen.preimage f.continuous)
      have hqU : q ∈ U := ⟨hqO,by change f q ∈ O; rw [hfix]; exact hqO⟩
      have hsourceU : U ⊆ e.source := fun x hx => (hOsub x hx.1).1
      have hstableU : Set.MapsTo f U U := by
        intro x hx
        exact ⟨hx.2,by change f (f x) ∈ O; rw [hinv x]; exact hx.1⟩
      have hnegU : ∀ x ∈ U, e (f x) = -e x := fun x hx => (hOsub x hx.1).2.2.2
      refine ⟨e,U,hU,hqU,hsourceU,hzero,hstableU,?_,?_,hnegU,?_⟩
      · exact fun x hx => (hOsub x hx.1).2.1
      · rintro w ⟨x,hx,rfl⟩
        exact (hOsub x hx.1).2.2.1
      · exact actual_branch_coordinate_square_fiber f e U hsourceU hstableU hnegU
    obtain ⟨e,U,hU,hq,hsource,hzero,hstable,hhol,hinvhol,hneg,hsquare⟩ := hnormal
    have hdesc :
      ∃ c : OpenPartialHomeomorph B ℂ,
        c.source = p '' U ∧ p q ∈ c.source ∧
        c.target = (fun z : ℂ => z ^ 2) '' (e '' U) ∧
        (∀ x ∈ U, c (p x) = (e x) ^ 2) := by
      let P := p '' U
      let V := e '' U
      have hP : IsOpen P := hp.isOpenMap U hU
      have hV : IsOpen V := e.isOpen_image_of_subset_source hU hsource
      let e0 : U ≃ₜ V := e.homeomorphOfImageSubsetSource hsource rfl
      let p0 : U → P := fun x => ⟨p x, ⟨x,x.property,rfl⟩⟩
      letI : Nonempty U := ⟨⟨q,hq⟩⟩
      have hp0 : IsOpenQuotientMap p0 := by
        refine ⟨?_,hp.continuous.subtype_map (q := fun y => y ∈ P) (fun x hx => ⟨x,hx,rfl⟩),
          hp.isOpenMap.subtype_map (t := P) hU (fun x hx => ⟨x,hx,rfl⟩)⟩
        intro y
        obtain ⟨x,hx,hpx⟩ := y.property
        exact ⟨⟨x,hx⟩,Subtype.ext hpx⟩
      have hker : ∀ x y : U, p0 x = p0 y ↔
          (e0 x : ℂ) = (e0 y : ℂ) ∨ (e0 x : ℂ) = -(e0 y : ℂ) := by
        intro x y
        rw [Subtype.ext_iff]
        change p x = p y ↔ e x = e y ∨ e x = -e y
        rw [hfiber y x]
        exact ((actual_branch_coordinate_square_fiber f e U hsource hstable hneg)
          y y.property x x.property).symm.trans sq_eq_sq_iff_eq_or_eq_neg
      obtain ⟨c0,hcsource,hctarget,hcformula⟩ :=
        actual_local_negation_quotient_literal_square_chart V hV e0 p0 hp0 hker
      let c := c0.lift_openEmbedding hP.isOpenEmbedding_subtypeVal
      have hcs : c.source = P := by
        rw [c0.lift_openEmbedding_source, hcsource]
        simp
      refine ⟨c,hcs,?_,hctarget,?_⟩
      · rw [hcs]
        exact ⟨q,hq,rfl⟩
      · intro x hx
        change c (Subtype.val (p0 ⟨x,hx⟩)) = (e x) ^ 2
        rw [c0.lift_openEmbedding_apply]
        exact hcformula ⟨x,hx⟩
    obtain ⟨c,hcs,hcq,hct,hcf⟩ := hdesc
    exact ⟨e,U,c,hU,hq,hsource,hzero,hstable,hhol,hinvhol,hcs,hcq,hct,hcf⟩
  have hcover : IsCoveringMapOn p (D : Set B)ᶜ := by
    apply IsCoveringMapOn.of_isLocalHomeomorphOn hp.continuous
    intro x hx
    apply hregular x
    intro hxf
    exact hx ((hDfix x).mpr hxf)
  have hbranch : ∀ x, p x ∈ D →
      ∃ R : SquareBranchChart E B p x,
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 R.upstairs R.upstairs.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 R.upstairs.symm R.upstairs.target := by
    intro x hxb
    obtain ⟨e,U,c,hU,hxU,hsource,hzero,hstable,hhol,hinvhol,hcs,hcq,hct,hcf⟩ :=
      branch_producer x ((hDfix x).mp hxb)
    have heu : (e.restr U).source = U := by
      rw [e.restr_source' U hU]
      exact inter_eq_right.mpr hsource
    refine ⟨{
      upstairs := e.restr U
      downstairs := c
      upstairs_mem := heu.symm ▸ hxU
      downstairs_mem := hcq
      upstairs_center := hzero
      downstairs_center := ?_
      image_mem := ?_
      square := ?_ }, ?_, ?_⟩
    · rw [hcf x hxU,hzero]
      simp
    · intro y hy
      rw [heu] at hy
      rw [hcs]
      exact ⟨y,hy,rfl⟩
    · intro y hy
      rw [heu] at hy
      exact hcf y hy
    · intro y hy
      rw [heu] at hy
      exact (hhol y hy).contMDiffWithinAt
    · intro w hw
      have htarget : (e.restr U).target = e '' U := by
        rw [← (e.restr U).image_source_eq_target,heu]
        rfl
      have hwV : w ∈ e '' U := htarget ▸ hw
      exact (hinvhol w hwV).contMDiffWithinAt
  let Q : BranchedDoubleCover E B := {
    projection := p
    projection_continuous := hp.continuous
    projection_surjective := hp.surjective
    deck := f
    deck_involution := hinv
    branch := D
    branch_card := hDcard
    fixed_iff_branch := fun x => (hDfix x).symm
    projection_deck := fun x => (hfiber x (f x)).mpr (Or.inr rfl)
    fiber_pair := fun x y => by
      rw [eq_comm (a := p x)]
      exact hfiber x y
    unbranched_cover := hcover
    branch_chart := fun x hxb => Classical.choose (hbranch x hxb) }
  refine ⟨B,t,hT,hCompact,hConnected,Q,rfl,?_⟩
  intro x hx
  exact Classical.choose_spec (hbranch x hx)
