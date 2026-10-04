import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.SmoothJetTopology
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.Pi

open Filter Topology
open scoped Manifold ContDiff

namespace SameAtlasAnalyticCohomology

universe u

variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- All real jets in a finite family of original preferred charts covering E
induce exactly the existing all-preferred-chart topology on actual (0,1) forms. -/
theorem smoothZeroOne_finiteChartJets_isInducing
    (A : Finset E)
    (hA : ∀ x : E, ∃ a ∈ A, x ∈ (extChartAt 𝓘(ℂ) a).source) :
    Topology.IsInducing (fun α : SmoothZeroOne E =>
      fun (a : A) (n : ℕ) => smoothZeroOneJet a.1 n α) := by
  classical
  have hTransfer {X : Type u} [TopologicalSpace X]
      (F : X → ℂ → ℂ) (T S : Set ℂ)
      (hT : IsOpen T) (hS : IsOpen S)
      (hF : ∀ x, ContDiffOn ℝ ∞ (F x) T)
      (hJ : ∀ n, ContinuousOn (fun xz : X × ℂ => iteratedFDeriv ℝ n (F xz.1) xz.2)
        (Set.univ ×ˢ T))
      (g c : ℂ → ℂ) (hg : ContDiffOn ℝ ∞ g S)
      (hcg : Set.MapsTo g S T) (hc : ContDiffOn ℝ ∞ c S) :
      ∀ n, ContinuousOn (fun xz : X × ℂ =>
        iteratedFDeriv ℝ n (fun z => c z * F xz.1 (g z)) xz.2) (Set.univ ×ˢ S) := by
    classical
    have hTaylor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        {Y : Type u} [TopologicalSpace Y] {D : Set Y}
        (q : Y → FormalMultilinearSeries ℝ V ℂ)
        (p : Y → FormalMultilinearSeries ℝ ℂ V)
        (hq : ∀ n, ContinuousOn (fun x => q x n) D)
        (hp : ∀ n, ContinuousOn (fun x => p x n) D) (n : ℕ) :
        ContinuousOn (fun x => (q x).taylorComp (p x) n) D := by
      apply continuousOn_finsetSum _ (fun d _ => ?_)
      let B := d.compAlongOrderedFinpartitionL ℝ ℂ V ℂ
      change ContinuousOn
        ((fun v => B v.1 v.2) ∘ (fun x => (q x d.length, fun i => p x (d.partSize i)))) D
      exact B.continuous_uncurry_of_multilinear.comp_continuousOn
        ((hq d.length).prodMk (continuousOn_pi.mpr (fun i => hp (d.partSize i))))
    have hcomp : ∀ n, ContinuousOn (fun xz : X × ℂ =>
        iteratedFDeriv ℝ n (F xz.1 ∘ g) xz.2) (Set.univ ×ˢ S) := by
      intro n
      have hq : ∀ k, ContinuousOn (fun xz : X × ℂ =>
          ftaylorSeries ℝ (F xz.1) (g xz.2) k) (Set.univ ×ˢ S) := by
        intro k
        exact (hJ k).comp (continuousOn_fst.prodMk (hg.continuousOn.comp continuousOn_snd
          (fun _ hz => hz.2))) (fun xz hz => ⟨Set.mem_univ _, hcg hz.2⟩)
      have hp : ∀ k, ContinuousOn (fun xz : X × ℂ =>
          ftaylorSeries ℝ g xz.2 k) (Set.univ ×ˢ S) := by
        intro k
        exact (ContinuousOn.continuousOn_iteratedFDeriv hg hS (by simp)).comp continuousOn_snd
          (fun _ hz => hz.2)
      refine (hTaylor _ _ hq hp n).congr ?_
      intro xz hz
      exact (iteratedFDeriv_comp ((hF xz.1).contDiffAt (hT.mem_nhds (hcg hz.2)))
        (hg.contDiffAt (hS.mem_nhds hz.2)) (by simp))
    have hpair : ∀ n, ContinuousOn (fun xz : X × ℂ =>
        iteratedFDeriv ℝ n (fun z => (c z, F xz.1 (g z))) xz.2) (Set.univ ×ˢ S) := by
      intro n
      have hp := ((ContinuousOn.continuousOn_iteratedFDeriv (k := n) hc hS (by simp)).comp continuousOn_snd
        (fun _ hz => hz.2)).prodMk (hcomp n)
      have hp' := (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin n => ℂ) ℂ ℂ).continuous
        |>.comp_continuousOn hp
      refine hp'.congr ?_
      intro xz hz
      exact (iteratedFDeriv_prodMk (hc.contDiffAt (hS.mem_nhds hz.2))
        (((hF xz.1).contDiffAt (hT.mem_nhds (hcg hz.2))).comp _
          (hg.contDiffAt (hS.mem_nhds hz.2))) (by simp))
    let M : ℂ × ℂ → ℂ := fun v => v.1 * v.2
    have hM : ContDiff ℝ ∞ M := contDiff_fst.mul contDiff_snd
    have hzero : ContinuousOn (fun xz : X × ℂ => (c xz.2, F xz.1 (g xz.2)))
        (Set.univ ×ˢ S) := by
      have := (continuousMultilinearCurryFin0 ℝ ℂ (ℂ × ℂ)).continuous.comp_continuousOn
        (hpair 0)
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
        LinearIsometryEquiv.apply_symm_apply] using this
    intro n
    have hq : ∀ k, ContinuousOn (fun xz : X × ℂ =>
        ftaylorSeries ℝ M (c xz.2, F xz.1 (g xz.2)) k) (Set.univ ×ˢ S) := by
      intro k
      exact (hM.continuous_iteratedFDeriv (by simp)).comp_continuousOn hzero
    have h := hTaylor _ _ hq hpair n
    refine h.congr ?_
    intro xz hz
    exact (iteratedFDeriv_comp hM.contDiffAt
      ((hc.contDiffAt (hS.mem_nhds hz.2)).prodMk
        (((hF xz.1).contDiffAt (hT.mem_nhds (hcg hz.2))).comp _
          (hg.contDiffAt (hS.mem_nhds hz.2)))) (by simp))
  let R : SmoothZeroOne E → (∀ (a : A) (n : ℕ), C(ChartTarget a.1, RealJet n)) :=
    fun α a n => smoothZeroOneJet a.1 n α
  let J : SmoothZeroOne E → (∀ (a : E) (n : ℕ), C(ChartTarget a, RealJet n)) :=
    fun α a n => smoothZeroOneJet a n α
  have hR : Continuous R := by
    have hJ : Continuous J := continuous_induced_dom
    exact continuous_pi (fun a => continuous_pi (fun n =>
      (continuous_apply n).comp ((continuous_apply a.1).comp hJ)))
  have hleR : smoothZeroOneTopology (E := E) ≤ TopologicalSpace.induced R inferInstance :=
    continuous_iff_le_induced.mp hR
  let tFinite : TopologicalSpace (SmoothZeroOne E) := TopologicalSpace.induced R inferInstance
  have hJ : @Continuous _ _ tFinite inferInstance J := by
    let : TopologicalSpace (SmoothZeroOne E) := tFinite
    apply continuous_pi
    intro b
    apply continuous_pi
    intro n
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨a, haA, ha⟩ := hA ((extChartAt 𝓘(ℂ) b).symm p.2.1)
    let T := (extChartAt 𝓘(ℂ) a).target
    let S := ((extChartAt 𝓘(ℂ) b).symm ≫ extChartAt 𝓘(ℂ) a).source
    let g : ℂ → ℂ := (extChartAt 𝓘(ℂ) a) ∘ (extChartAt 𝓘(ℂ) b).symm
    let c : ℂ → ℂ := fun z => star ((fderiv ℂ g z) 1)
    have hS : IsOpen S := by
      exact (continuousOn_extChartAt_symm b).isOpen_inter_preimage
        (isOpen_extChartAt_target b) (isOpen_extChartAt_source a)
    have hgC : ContDiffOn ℂ ∞ g S := contDiffOn_ext_coord_change a b
    have hg : ContDiffOn ℝ ∞ g S := hgC.restrict_scalars ℝ
    have hc : ContDiffOn ℝ ∞ c S := by
      have hd := (hgC.fderiv_of_isOpen hS (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := (1 : ℂ)))
      exact Complex.conjCLE.contDiff.comp_contDiffOn (hd.restrict_scalars ℝ)
    have hcg : Set.MapsTo g S T := fun z hz =>
      (extChartAt 𝓘(ℂ) a).map_source hz.2
    let F : SmoothZeroOne E → ℂ → ℂ := fun α z => α.1 a ((extChartAt 𝓘(ℂ) a).symm z)
    have hF : ∀ α, ContDiffOn ℝ ∞ (F α) T := fun α => α.property.2.1 a
    have hFJ : ∀ k, ContinuousOn (fun q : SmoothZeroOne E × ℂ =>
        iteratedFDeriv ℝ k (F q.1) q.2) (Set.univ ×ˢ T) := by
      intro k
      let : LocallyCompactSpace (ChartTarget a) := (isOpen_extChartAt_target a).locallyCompactSpace
      have hR' : Continuous R := continuous_induced_dom
      have he : Continuous (fun α : SmoothZeroOne E => smoothZeroOneJet a k α) :=
        (continuous_apply k).comp ((continuous_apply (⟨a, haA⟩ : A)).comp hR')
      apply continuousOn_iff_continuous_domRestrict.mpr
      have hp : Continuous (fun q : (Set.univ ×ˢ T : Set (SmoothZeroOne E × ℂ)) =>
          (q.1.1, (⟨q.1.2, q.2.2⟩ : ChartTarget a))) :=
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
      exact (continuous_eval.comp (he.prodMap continuous_id)).comp hp
    have hOn := hTransfer F T S (isOpen_extChartAt_target a) hS hF hFJ g c hg hcg hc n
    have hOn' : ContinuousOn (fun q : SmoothZeroOne E × ℂ =>
        iteratedFDeriv ℝ n (fun z => q.1.1 b ((extChartAt 𝓘(ℂ) b).symm z)) q.2)
        (Set.univ ×ˢ S) := by
      refine hOn.congr ?_
      intro q hq
      have heq : (fun z => q.1.1 b ((extChartAt 𝓘(ℂ) b).symm z)) =ᶠ[𝓝 q.2]
          (fun z => c z * F q.1 (g z)) := by
        filter_upwards [hS.mem_nhds hq.2] with z hz
        have hzb := (extChartAt 𝓘(ℂ) b).map_target hz.1
        have hza := hz.2
        have h := q.1.property.2.2 b a ((extChartAt 𝓘(ℂ) b).symm z) hzb hza
        have hd : chartTransitionDerivative b a ((extChartAt 𝓘(ℂ) b).symm z) ≠ 0 := by
          intro hzero
          have hzero' : tangentCoordChange 𝓘(ℂ) b a ((extChartAt 𝓘(ℂ) b).symm z) 1 = 0 := by
            simpa [tangentCoordChange_def, chartTransitionDerivative, mfld_simps] using hzero
          have hcc := tangentCoordChange_comp (I := 𝓘(ℂ))
            (w := b) (x := a) (y := b) (z := (extChartAt 𝓘(ℂ) b).symm z) (v := (1 : ℂ))
            ⟨⟨hzb, hza⟩, hzb⟩
          rw [hzero', map_zero, tangentCoordChange_self hzb] at hcc
          exact zero_ne_one hcc
        have hc' : c z = star (chartTransitionDerivative b a ((extChartAt 𝓘(ℂ) b).symm z)) := by
          change star ((fderiv ℂ g z) 1) =
            star ((fderiv ℂ g ((extChartAt 𝓘(ℂ) b) ((extChartAt 𝓘(ℂ) b).symm z))) 1)
          rw [(extChartAt 𝓘(ℂ) b).right_inv hz.1]
        have hF' : F q.1 (g z) = q.1.1 a ((extChartAt 𝓘(ℂ) b).symm z) := by
          exact congrArg (q.1.1 a) ((extChartAt 𝓘(ℂ) a).left_inv hza)
        rw [hc', hF', mul_comm]
        exact (div_eq_iff (star_ne_zero.mpr hd)).mp h.symm
      exact (heq.iteratedFDeriv ℝ n).eq_of_nhds
    have hpS : p.2.1 ∈ S := ⟨p.2.2, ha⟩
    have hAt : ContinuousAt (fun q : SmoothZeroOne E × ℂ =>
        iteratedFDeriv ℝ n (fun z => q.1.1 b ((extChartAt 𝓘(ℂ) b).symm z)) q.2)
        (p.1, p.2.1) :=
      hOn'.continuousAt ((isOpen_univ.prod hS).mem_nhds ⟨Set.mem_univ _, hpS⟩)
    exact hAt.comp_of_eq
      ((continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd) :
        Continuous (fun q : SmoothZeroOne E × ChartTarget b => (q.1, q.2.1))).continuousAt) rfl
  exact @Topology.IsInducing.mk _ _ (smoothZeroOneTopology (E := E)) inferInstance R
    (le_antisymm hleR (continuous_iff_le_induced.mp hJ))

/-- On a compact Hausdorff surface, the existing all-jets topology on actual
(0,1) forms has a countable neighborhood basis at each form. -/
theorem smoothZeroOne_firstCountableTopology
    [T2Space E] [CompactSpace E] :
    FirstCountableTopology (SmoothZeroOne E) := by
  let : ∀ (a : E) (n : ℕ), FirstCountableTopology C(ChartTarget a, RealJet n) :=
    fun a n => by
      let : LocallyCompactSpace (ChartTarget a) :=
        (isOpen_extChartAt_target a).locallyCompactSpace
      have : SigmaCompactSpace (ChartTarget a) := inferInstance
      have : WeaklyLocallyCompactSpace (ChartTarget a) := inferInstance
      have : Filter.IsCountablyGenerated
          (@uniformity (RealJet n) inferInstance) := inferInstance
      have h : Filter.IsCountablyGenerated
          (@uniformity C(ChartTarget a, RealJet n) inferInstance) := inferInstance
      exact @UniformSpace.firstCountableTopology _ _ h
  classical
  obtain ⟨A, hA⟩ := isCompact_univ.elim_finite_subcover
    (fun a : E => (extChartAt 𝓘(ℂ) a).source)
    (fun a => isOpen_extChartAt_source a) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
  apply (smoothZeroOne_finiteChartJets_isInducing A ?_).firstCountableTopology
  intro x
  simpa only [Set.mem_iUnion, exists_prop] using hA (Set.mem_univ x)

end SameAtlasAnalyticCohomology
