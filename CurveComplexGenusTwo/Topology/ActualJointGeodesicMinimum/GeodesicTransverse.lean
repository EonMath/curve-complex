import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.H2CrossingChart
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.FixedCoverTrace
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.Providers
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery
open scoped Manifold UpperHalfPlane

private theorem finite_intersection_of_crossings
    {E : Type} [TopologicalSpace E] [T2Space E]
    (a b : Curve E) (hc : ∀ x ∈ a.image ∩ b.image, CrossesAt a b x) :
    (a.image ∩ b.image).Finite := by
  let K : Set E := a.image ∩ b.image
  have hK : IsCompact K :=
    (isCompact_range a.embedded.continuous).inter (isCompact_range b.embedded.continuous)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : DiscreteTopology K := discreteTopology_iff_isOpen_singleton.mpr (by
    intro x
    obtain ⟨U,V,hxU,h,hU,hV,hzero,haxes⟩ := hc x.val x.property
    have heq : (Subtype.val : K → E) ⁻¹' U = {x} := by
      ext y
      constructor
      · intro hy
        have hcoords : ((h ⟨y.val,hy⟩ : V) : ℝ × ℝ) = (0,0) := by
          apply Prod.ext
          · exact (haxes y.val hy).1.mp y.property.1
          · exact (haxes y.val hy).2.mp y.property.2
        have he : (⟨y.val,hy⟩ : U) = ⟨x.val,hxU⟩ :=
          h.injective (Subtype.ext (hcoords.trans hzero.symm))
        exact Set.mem_singleton_iff.mpr (Subtype.ext (congrArg (fun w : U => (w : E)) he))
      · rintro rfl
        exact hxU
    rw [←heq]
    exact hU.preimage continuous_subtype_val)
  have : Finite K := finite_of_compact_of_discrete
  exact Set.toFinite K

private theorem descend_crossing_chart
    {P E : Type} [TopologicalSpace P] [TopologicalSpace E]
    (q : P → E) (hq : IsLocalHomeomorph q) (a b : Curve E)
    (A B : Set P) (z : P)
    (Ua Ub : Set P) (hUa : IsOpen Ua) (hUb : IsOpen Ub)
    (hzUa : z ∈ Ua) (hzUb : z ∈ Ub)
    (ha : ∀ y ∈ Ua, q y ∈ a.image ↔ y ∈ A)
    (hb : ∀ y ∈ Ub, q y ∈ b.image ↔ y ∈ B)
    (U : Set P) (V : Set (ℝ × ℝ)) (hzU : z ∈ U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (hzero : ((h ⟨z,hzU⟩ : V) : ℝ × ℝ) = (0,0))
    (haxes : ∀ y (hy : y ∈ U),
      (y ∈ A ↔ ((h ⟨y,hy⟩ : V) : ℝ × ℝ).1 = 0) ∧
      (y ∈ B ↔ ((h ⟨y,hy⟩ : V) : ℝ × ℝ).2 = 0)) :
    CrossesAt a b (q z) := by
  classical
  let C := crossingPartialChart U V hU hV ⟨z,hzU⟩ h
  have hCs : C.source = U := by simp [C, crossingPartialChart]
  have hCval (y : P) (hy : y ∈ U) : C y = (h ⟨y,hy⟩ : ℝ × ℝ) := by
    simp only [C,crossingPartialChart,OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    change (h (((⟨U,hU⟩ : TopologicalSpace.Opens P).openPartialHomeomorphSubtypeCoe
      ⟨⟨z,hzU⟩⟩).symm y) : ℝ × ℝ) = (h ⟨y,hy⟩ : ℝ × ℝ)
    have hinv := ((⟨U,hU⟩ : TopologicalSpace.Opens P).openPartialHomeomorphSubtypeCoe
      ⟨⟨z,hzU⟩⟩).left_inv (show (⟨y,hy⟩ : U) ∈ Set.univ from trivial)
    change ((⟨U,hU⟩ : TopologicalSpace.Opens P).openPartialHomeomorphSubtypeCoe
      ⟨⟨z,hzU⟩⟩).symm y=⟨y,hy⟩ at hinv
    rw [hinv]
  obtain ⟨e,hze,he⟩ := hq z
  let Cr := C.restr (Ua ∩ Ub)
  have hCrs : Cr.source = U ∩ (Ua ∩ Ub) := by
    simp [Cr, (hUa.inter hUb).interior_eq, hCs]
  let K := e.symm.trans Cr
  have hzK : q z ∈ K.source := by
    change q z ∈ e.target ∧ e.symm (q z) ∈ Cr.source
    rw [he, e.left_inv hze, hCrs]
    exact ⟨e.map_source hze, hzU, hzUa, hzUb⟩
  refine ⟨K.source,K.target,hzK,K.toHomeomorphSourceTarget,K.open_source,K.open_target,?_,?_⟩
  · change Cr (e.symm (q z)) = (0,0)
    rw [he, e.left_inv hze]
    change C z = (0,0)
    rw [hCval z hzU]
    exact hzero
  · intro y hy
    have hyv : e.symm y ∈ U ∩ (Ua ∩ Ub) := hCrs ▸ hy.2
    have hqy : q (e.symm y) = y := by rw [he]; exact e.right_inv hy.1
    have hky : K y = C (e.symm y) := rfl
    change (y ∈ a.image ↔ (K y).1 = 0) ∧ (y ∈ b.image ↔ (K y).2 = 0)
    rw [hky, hCval _ hyv.1]
    have hya : y ∈ a.image ↔ e.symm y ∈ A := by simpa only [hqy] using ha _ hyv.2.1
    have hyb : y ∈ b.image ↔ e.symm y ∈ B := by simpa only [hqy] using hb _ hyv.2.2
    exact ⟨hya.trans (haxes _ hyv.1).1, hyb.trans (haxes _ hyv.1).2⟩

private theorem crosses_of_line_lifts
    {E : Type} [TopologicalSpace E]
    (q : H2 → E) (hq : IsLocalHomeomorph q) (a b : Curve E)
    (f g : ℝ → H2) (hf : Isometry f) (hg : Isometry g)
    (hne : Set.range f ≠ Set.range g)
    (z : H2) (hz : z ∈ Set.range f ∩ Set.range g)
    (hta : ∃ Ua : Set H2, IsOpen Ua ∧ z ∈ Ua ∧
      ∀ y ∈ Ua, q y ∈ a.image ↔ y ∈ Set.range f)
    (htb : ∃ Ub : Set H2, IsOpen Ub ∧ z ∈ Ub ∧
      ∀ y ∈ Ub, q y ∈ b.image ↔ y ∈ Set.range g) :
    CrossesAt a b (q z) := by
  obtain ⟨Ua,hUa,hza,ha⟩ := hta
  obtain ⟨Ub,hUb,hzb,hb⟩ := htb
  obtain ⟨U,V,hzU,h,hU,hV,hzero,haxes⟩ :=
    distinct_h2_isometric_lines_have_crossing_chart f g hf hg hne z hz
  exact descend_crossing_chart q hq a b (Set.range f) (Set.range g) z
    Ua Ub hUa hUb hza hzb ha hb U V hzU h hU hV hzero haxes

private theorem crosses_from_fixed_cover
    {E : Type} [TopologicalSpace E] [LocallyConnectedSpace E]
    (a b : Curve E) (hne : a.image ≠ b.image) (x : E)
    (hxa : x ∈ a.image) (hxb : x ∈ b.image)
    (p : H2 → connectedComponent x) (hp : IsCoveringMap p) (hps : Function.Surjective p)
    (γa γb : C(ℝ, connectedComponent x))
    (hia : Subtype.val '' Set.range γa = a.image)
    (hib : Subtype.val '' Set.range γb = b.image)
    (fa : {z : H2 // p z ∈ Set.range γa} → ℝ → H2)
    (fia : ∀ z, Isometry (fa z)) (fpa : ∀ z t, p (fa z t) = γa t)
    (fza : ∀ z, z.val ∈ Set.range (fa z))
    (fb : {z : H2 // p z ∈ Set.range γb} → ℝ → H2)
    (fib : ∀ z, Isometry (fb z)) (fpb : ∀ z t, p (fb z t) = γb t)
    (fzb : ∀ z, z.val ∈ Set.range (fb z))
    (htrace : ∀ (c : Curve E) (L : ℝ → H2), Isometry L →
      Set.range (fun t => (p (L t)).val) = c.image →
      ∀ z ∈ Set.range L, ∃ U : Set H2, IsOpen U ∧ z ∈ U ∧
        ∀ y ∈ U, (p y).val ∈ c.image ↔ y ∈ Set.range L) :
    CrossesAt a b x := by
  obtain ⟨z,hz⟩ := hps ⟨x, mem_connectedComponent⟩
  have hza : p z ∈ Set.range γa := by
    rw [←hia] at hxa
    obtain ⟨w,hw,hwx⟩ := hxa
    have hwz : w = p z := by apply Subtype.ext; simpa only [hz] using hwx
    exact hwz ▸ hw
  have hzb : p z ∈ Set.range γb := by
    rw [←hib] at hxb
    obtain ⟨w,hw,hwx⟩ := hxb
    have hwz : w = p z := by apply Subtype.ext; simpa only [hz] using hwx
    exact hwz ▸ hw
  let f := fa ⟨z,hza⟩
  let g := fb ⟨z,hzb⟩
  have hfp : Set.range (fun t => (p (f t)).val) = a.image := by
    rw [←hia]
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨γa t, Set.mem_range_self t, congrArg Subtype.val (fpa ⟨z,hza⟩ t).symm⟩
    · rintro ⟨w,⟨t,rfl⟩,rfl⟩
      exact ⟨t, congrArg Subtype.val (fpa ⟨z,hza⟩ t)⟩
  have hgp : Set.range (fun t => (p (g t)).val) = b.image := by
    rw [←hib]
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨γb t, Set.mem_range_self t, congrArg Subtype.val (fpb ⟨z,hzb⟩ t).symm⟩
    · rintro ⟨w,⟨t,rfl⟩,rfl⟩
      exact ⟨t, congrArg Subtype.val (fpb ⟨z,hzb⟩ t)⟩
  have hfg : Set.range f ≠ Set.range g := by
    intro heq
    apply hne
    rw [←hfp, ←hgp]
    change Set.range ((fun w : H2 => (p w).val) ∘ f) =
      Set.range ((fun w : H2 => (p w).val) ∘ g)
    rw [Set.range_comp, Set.range_comp, heq]
  let q : H2 → E := fun w => (p w).val
  have hq : IsLocalHomeomorph q :=
    isOpen_connectedComponent.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp hp.isLocalHomeomorph
  have hh := crosses_of_line_lifts q hq a b f g (fia ⟨z,hza⟩) (fib ⟨z,hzb⟩)
    hfg z ⟨fza ⟨z,hza⟩,fzb ⟨z,hzb⟩⟩
    (htrace a f (fia ⟨z,hza⟩) hfp z (fza ⟨z,hza⟩))
    (htrace b g (fib ⟨z,hzb⟩) hgp z (fzb ⟨z,hzb⟩))
  simpa only [q, hz] using hh

section Surface

variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem distinct_closed_geodesic_curves_transverse
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (hageo : letI : MetricSpace E := H.metric; IsClosedGeodesic a.image)
    (hbgeo : letI : MetricSpace E := H.metric; IsClosedGeodesic b.image)
    (hne : a.image ≠ b.image) :
    Transverse a b := by
  have hT2metric : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    let : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at hT2metric
  let : T2Space E := hT2metric
  let : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
  have hc : ∀ x ∈ a.image ∩ b.image, CrossesAt a b x := by
    intro x hx
    obtain ⟨p, γa, γb, _hq, hp, hps, hlocal, hia, hib, _hpa, _hpb,
      ⟨fa, fia, fpa, fza, _fra⟩, ⟨fb, fib, fpb, fzb, _frb⟩⟩ :=
      two_closed_geodesics_have_common_developed_lines H a b hageo hbgeo x hx.1 hx.2
    exact crosses_from_fixed_cover a b hne x hx.1 hx.2 p hp hps γa γb hia hib
      fa fia fpa fza fb fib fpb fzb (fixed_cover_geodesic_local_single_line_trace H x p hp hlocal)
  exact ⟨finite_intersection_of_crossings a b hc, hc⟩

end Surface
end CurveComplex.Hyperbolic.JointMinimum
