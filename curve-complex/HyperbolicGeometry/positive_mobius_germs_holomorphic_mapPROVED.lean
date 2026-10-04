import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
open Set
open scoped MatrixGroups Manifold ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem positive_mobius_germs_holomorphic_map {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    (f : C(E,E))
    (hcoords : ∀ x : E, ∃ (U : Set E) (g : GL (Fin 2) ℝ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ (chartAt ℂ x).source ∧
        MapsTo f U (chartAt ℂ (f x)).source ∧ 0 < g.val.det ∧
          ∀ y ∈ U, ∃ hy : 0 < (chartAt ℂ x y).im,
            ((g • (⟨chartAt ℂ x y,hy⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
              chartAt ℂ (f x) (f y)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f := by
  intro x
  obtain ⟨U,g,hU,hxU,hc,hd,hpos,hg⟩ := hcoords x
  obtain ⟨hp,_⟩ := hg x hxU
  let p : UpperHalfPlane := ⟨chartAt ℂ x x,hp⟩
  apply contMDiffAt_iff.mpr
  refine ⟨f.continuous.continuousAt,?_⟩
  have hs : ContDiffAt ℂ ∞
      (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
        (chartAt ℂ x x) :=
    (UpperHalfPlane.analyticAt_smul hpos p).contDiffAt
  have hV : IsOpen ((chartAt ℂ x) '' U) :=
    (chartAt ℂ x).isOpen_image_of_subset_source hU hc
  have hpV : chartAt ℂ x x ∈ (chartAt ℂ x) '' U := ⟨x,hxU,rfl⟩
  have heq : (fun z : ℂ => chartAt ℂ (f x) (f ((chartAt ℂ x).symm z))) =ᶠ[
      𝓝 (chartAt ℂ x x)]
      (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ)) := by
    filter_upwards [hV.mem_nhds hpV] with z hz
    obtain ⟨y,hy,hz⟩ := hz
    rw [←hz,(chartAt ℂ x).left_inv (hc hy)]
    obtain ⟨hiy,hgy⟩ := hg y hy
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hiy]
    exact hgy.symm
  have ht := (hs.congr_of_eventuallyEq heq).contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt,OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq] using ht

