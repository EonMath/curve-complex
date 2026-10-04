import ClosedHyperbolicCanonicalBridge
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

open Set
open scoped MatrixGroups
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
namespace CurveComplex.Hyperbolic

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]

theorem positive_hyperbolic_chart_family_complex_manifold (c : E → SmoothHyperbolicChart E)
    (hc : ∀ x : E, x ∈ (c x).chart.source)
    (hpositive : ∀ a b : E, ((c a).chart.source ∩ (c b).chart.source).Nonempty →
      ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧
        ∀ x (ha : x ∈ (c a).chart.source) (hb : x ∈ (c b).chart.source),
          g • (⟨(c a).chart x,(c a).upper x ha⟩ : H2) =
            (⟨(c b).chart x,(c b).upper x hb⟩ : H2)) :
    ∃ A : ChartedSpace ℂ E, @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ∞ E _ A := by
  classical
  have transition_holomorphic (c d : SmoothHyperbolicChart E) (g : GL (Fin 2) ℝ)
      (hpos : 0 < g.val.det)
      (hcoord : ∀ x (hc : x ∈ c.chart.source) (hd : x ∈ d.chart.source),
        g • (⟨c.chart x,c.upper x hc⟩ : H2) =
          (⟨d.chart x,d.upper x hd⟩ : H2)) :
      ContDiffOn ℂ ∞ (c.chart.toOpenPartialHomeomorph.symm.trans
        d.chart.toOpenPartialHomeomorph)
          (c.chart.toOpenPartialHomeomorph.symm.trans
            d.chart.toOpenPartialHomeomorph).source := by
    let e := c.chart.toOpenPartialHomeomorph.symm.trans d.chart.toOpenPartialHomeomorph
    intro z hz
    have hc : z ∈ c.chart.target := hz.1
    have hxc : c.chart.symm z ∈ c.chart.source :=
      c.chart.toOpenPartialHomeomorph.map_target hc
    have hcz : c.chart (c.chart.symm z) = z :=
      c.chart.toOpenPartialHomeomorph.right_inv hc
    have him : 0 < z.im := hcz ▸ c.upper (c.chart.symm z) hxc
    let τ : H2 := ⟨z,him⟩
    have hs : ContDiffAt ℂ ∞ (fun w : ℂ => ((g • UpperHalfPlane.ofComplex w : H2) : ℂ)) z := by
      exact UpperHalfPlane.contMDiffAt_iff.mp
        ((UpperHalfPlane.contMDiff_coe.comp (UpperHalfPlane.contMDiff_smul hpos)) τ)
    apply (hs.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [e.open_source.mem_nhds hz] with w hw
    have hcw : w ∈ c.chart.target := hw.1
    have hxw : c.chart.symm w ∈ c.chart.source :=
      c.chart.toOpenPartialHomeomorph.map_target hcw
    have hww : c.chart (c.chart.symm w) = w :=
      c.chart.toOpenPartialHomeomorph.right_inv hcw
    have hiw : 0 < w.im := hww ▸ c.upper (c.chart.symm w) hxw
    have hH : (⟨c.chart (c.chart.symm w),c.upper (c.chart.symm w) hxw⟩ : H2) =
        (⟨w,hiw⟩ : H2) := UpperHalfPlane.coe_injective hww
    have hh := hcoord (c.chart.symm w) hxw hw.2
    rw [hH] at hh
    change d.chart (c.chart.symm w) = ((g • UpperHalfPlane.ofComplex w : H2) : ℂ)
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hiw]
    exact congrArg UpperHalfPlane.coe hh.symm
  let A : ChartedSpace ℂ E := {
    atlas := Set.range (fun x : E => (c x).chart.toOpenPartialHomeomorph)
    chartAt := fun x => (c x).chart.toOpenPartialHomeomorph
    mem_chart_source := hc
    chart_mem_atlas := fun x => ⟨x,rfl⟩ }
  letI : ChartedSpace ℂ E := A
  refine ⟨A,?_⟩
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a,rfl⟩ := he
  obtain ⟨b,rfl⟩ := he'
  intro z hz
  have hz' : z ∈ ((c a).chart.toOpenPartialHomeomorph.symm.trans
      (c b).chart.toOpenPartialHomeomorph).source := hz.1
  have ha : (c a).chart.symm z ∈ (c a).chart.source :=
    (c a).chart.toOpenPartialHomeomorph.map_target hz'.1
  obtain ⟨g,hg,hcoord⟩ := hpositive a b ⟨(c a).chart.symm z,ha,hz'.2⟩
  have h := transition_holomorphic (c a) (c b) g hg hcoord
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.comp_def,id_eq,Set.range_id,Set.preimage_id,Set.inter_univ] using h z hz'

end CurveComplex.Hyperbolic
