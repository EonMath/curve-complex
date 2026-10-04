import Mathlib
import Schoenflies.Plane
import ClassificationOfSurfaces.Moise.Brouwer

open Set Topology
namespace CurveComplex
private abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem surface_invariance_of_domain_probe
    {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    (f : Plane → S) (U : Set Plane) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hi : InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨x,hx,rfl⟩
  let e := chartAt Plane (f x)
  let V := U ∩ f ⁻¹' e.source
  have hV : IsOpen V := hf.isOpen_inter_preimage hU e.open_source
  have hxV : x ∈ V := ⟨hx,mem_chart_source _ _⟩
  have hcomp : ContinuousOn (e ∘ f) V :=
    e.continuousOn.comp (hf.mono inter_subset_left) (fun _ hz => hz.2)
  have hcompI : InjOn (e ∘ f) V := by
    intro a ha b hb he
    exact hi ha.1 hb.1 (e.injOn ha.2 hb.2 he)
  have hopen : IsOpen ((e ∘ f) '' V) :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      (e ∘ f) V hV hcomp hcompI
  have htarget : (e ∘ f) '' V ⊆ e.target := by
    rintro z ⟨y,hy,rfl⟩
    exact e.map_source hy.2
  have heq : e.symm '' ((e ∘ f) '' V) = f '' V := by
    rw [Set.image_image]
    apply Set.image_congr
    intro y hy
    exact e.left_inv hy.2
  have hfv : IsOpen (f '' V) := by
    rw [← heq]
    exact e.symm.isOpen_image_of_subset_source hopen htarget
  exact ⟨f '' V,Set.image_mono inter_subset_left,hfv,⟨x,hxV,rfl⟩⟩

/-- Every embedded planar region in a surface sends its ordinary interior
into the ambient interior of its image. No collar assumption is used. -/
theorem embedded_planar_region_interior_probe
    {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    (K : Set Plane) (f : K → S) (hf : IsEmbedding f) :
    f '' {x : K | (x:Plane) ∈ interior K} ⊆ interior (Set.range f) := by
  classical
  by_cases hK : K.Nonempty
  · obtain ⟨x,hx⟩ := hK
    let g : Plane → S := Function.extend Subtype.val f (fun _ => f ⟨x,hx⟩)
    have hgf (z : K) : g z = f z := Subtype.val_injective.extend_apply _ _ z
    have hgc : ContinuousOn g K := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : K.domRestrict g = f := funext hgf
      rw [heq]
      exact hf.continuous
    have hgi : InjOn g K := by
      intro a ha b hb he
      have he' : f ⟨a,ha⟩ = f ⟨b,hb⟩ := by
        rw [← hgf ⟨a,ha⟩,← hgf ⟨b,hb⟩]
        exact he
      exact congrArg Subtype.val (hf.injective he')
    have hopen : IsOpen (g '' interior K) := surface_invariance_of_domain_probe
      g (interior K) isOpen_interior (hgc.mono interior_subset) (hgi.mono interior_subset)
    have hsubset : g '' interior K ⊆ Set.range f := by
      rintro z ⟨w,hw,rfl⟩
      exact ⟨⟨w,interior_subset hw⟩,(hgf ⟨w,interior_subset hw⟩).symm⟩
    rintro z ⟨w,hw,rfl⟩
    exact (hopen.subset_interior_iff.mpr hsubset) ⟨w,hw,hgf w⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact (hK ⟨w,w.property⟩).elim

/-- The converse interior inclusion follows by applying invariance of domain
to the actual inverse on an ambient chart inside the image. -/
theorem embedded_planar_region_interior_iff_probe
    {S : Type*} [TopologicalSpace S] [ChartedSpace Plane S]
    (K : Set Plane) (f : K → S) (hf : IsEmbedding f) (x : K) :
    f x ∈ interior (Set.range f) ↔ (x:Plane) ∈ interior K := by
  classical
  constructor
  · intro hx
    let e := chartAt Plane (f x)
    let V := e.target ∩ e.symm ⁻¹' interior (Set.range f)
    have hV : IsOpen V := e.isOpen_inter_preimage_symm isOpen_interior
    have hzV : e (f x) ∈ V := ⟨e.map_source (mem_chart_source _ _),by
      change e.symm (e (f x)) ∈ interior (Set.range f)
      rwa [e.left_inv (mem_chart_source _ _)]⟩
    let k : V → Plane := fun z =>
      ((hf.toHomeomorph.symm ⟨e.symm z,interior_subset z.property.2⟩ : K) : Plane)
    have hec : Continuous (fun z : V => e.symm z) :=
      continuousOn_iff_continuous_domRestrict.mp (e.symm.continuousOn.mono inter_subset_left)
    have hkc : Continuous k := continuous_subtype_val.comp
      (hf.toHomeomorph.symm.continuous.comp (hec.subtype_mk _))
    have hki : Function.Injective k := by
      intro z w he
      have hi : (hf.toHomeomorph.symm ⟨e.symm z,interior_subset z.property.2⟩ : K) =
          hf.toHomeomorph.symm ⟨e.symm w,interior_subset w.property.2⟩ := Subtype.ext he
      have hi' := congrArg Subtype.val (hf.toHomeomorph.symm.injective hi)
      exact Subtype.ext (e.symm.injOn z.property.1 w.property.1 hi')
    let g : Plane → Plane := Function.extend Subtype.val k (fun _ => 0)
    have hgk (z : V) : g z = k z := Subtype.val_injective.extend_apply _ _ z
    have hgc : ContinuousOn g V := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : V.domRestrict g = k := funext hgk
      rw [heq]
      exact hkc
    have hgi : InjOn g V := by
      intro a ha b hb he
      have he' : k ⟨a,ha⟩ = k ⟨b,hb⟩ := by
        rw [← hgk ⟨a,ha⟩,← hgk ⟨b,hb⟩]
        exact he
      exact congrArg Subtype.val (hki he')
    have hopen : IsOpen (g '' V) :=
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
        g V hV hgc hgi
    have hsubset : g '' V ⊆ K := by
      rintro z ⟨w,hw,rfl⟩
      rw [hgk ⟨w,hw⟩]
      exact (hf.toHomeomorph.symm ⟨e.symm w,interior_subset hw.2⟩).property
    apply (hopen.subset_interior_iff.mpr hsubset)
    refine ⟨e (f x),hzV,?_⟩
    rw [hgk ⟨e (f x),hzV⟩]
    change ((hf.toHomeomorph.symm ⟨e.symm (e (f x)),_⟩ : K) : Plane) = x
    have hh : (⟨e.symm (e (f x)),interior_subset hzV.2⟩ : Set.range f) =
        hf.toHomeomorph x := by
      apply Subtype.ext
      exact e.left_inv (mem_chart_source _ _)
    rw [hh,hf.toHomeomorph.symm_apply_apply]
  · intro hx
    exact embedded_planar_region_interior_probe K f hf ⟨x,hx,rfl⟩

/-- For a compact planar region, its parameter frontier maps EXACTLY to the
ambient frontier of its embedded image in a surface. -/
theorem embedded_compact_planar_region_frontier_probe
    {S : Type*} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (K : Set Plane) (hK : IsCompact K) (f : K → S) (hf : IsEmbedding f) :
    f '' {x : K | (x:Plane) ∈ frontier K} = frontier (Set.range f) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [(isCompact_range hf.continuous).isClosed.frontier_eq,hK.isClosed.frontier_eq]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨Set.mem_range_self _,?_⟩
    intro hi
    exact hx.2 ((embedded_planar_region_interior_iff_probe K f hf x).mp hi)
  · rintro ⟨⟨x,rfl⟩,hx⟩
    exact ⟨x,⟨x.property,fun hi => hx
      ((embedded_planar_region_interior_iff_probe K f hf x).mpr hi)⟩,rfl⟩

#print axioms embedded_planar_region_interior_iff_probe
#print axioms embedded_compact_planar_region_frontier_probe
#print axioms surface_invariance_of_domain_probe
#print axioms embedded_planar_region_interior_probe
end CurveComplex
