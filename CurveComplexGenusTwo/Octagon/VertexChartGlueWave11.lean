import CurveComplexGenusTwo.Octagon.SectorUnfold
import CurveComplexGenusTwo.Octagon.OctagonChartGlueWave10

namespace CurveComplex.Octagon

/-! Continuity needed to descend the explicit eight-sector unfolding. -/

theorem continuous_sectorLocalComplex :
    Continuous (fun p : unitInterval × unitInterval =>
      sectorLocalComplex p.1 p.2) := by
  unfold sectorLocalComplex
  fun_prop

theorem continuous_sectorLocalRadius :
    Continuous (fun p : unitInterval × unitInterval =>
      sectorLocalRadius p.1 p.2) := by
  unfold sectorLocalRadius
  exact continuous_norm.comp continuous_sectorLocalComplex

private def upperNonzero : Set ℂ :=
  {z | 0 ≤ z.im ∧ z ≠ 0}

private theorem continuousOn_arg_upperNonzero :
    ContinuousOn Complex.arg upperNonzero := by
  intro z hz
  rcases hz with ⟨him, hzero⟩
  by_cases hpi : Complex.arg z = Real.pi
  · have hp := Complex.arg_eq_pi_iff.mp hpi
    have hupper : upperNonzero ⊆ {z : ℂ | 0 ≤ z.im} :=
      fun _ h => h.1
    exact (Complex.continuousWithinAt_arg_of_re_neg_of_im_zero hp.1 hp.2).mono hupper
  · have hslit : z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff_arg.mpr ⟨hpi, hzero⟩
    exact (Complex.continuousAt_arg hslit).continuousWithinAt

theorem continuousOn_sectorLocalAngle_nonzero :
    ContinuousOn (fun p : unitInterval × unitInterval =>
      sectorLocalAngle p.1 p.2)
      {p | sectorLocalComplex p.1 p.2 ≠ 0} := by
  let f : unitInterval × unitInterval → ℂ :=
    fun p => sectorLocalComplex p.1 p.2
  have hmap : Set.MapsTo f {p | f p ≠ 0} upperNonzero := by
    intro p hp
    exact ⟨by simpa [f, sectorLocalComplex_im] using p.1.property.1, hp⟩
  exact continuousOn_arg_upperNonzero.comp
    (continuous_sectorLocalComplex.continuousOn) hmap

theorem continuousOn_sectorUnfoldPoint_nonzero (k : Fin 8) :
    ContinuousOn (fun p : unitInterval × unitInterval =>
      sectorUnfoldPoint k p.1 p.2)
      {p | sectorLocalComplex p.1 p.2 ≠ 0} := by
  have hangle : ContinuousOn (fun p : unitInterval × unitInterval =>
      sectorUnfoldAngle k p.1 p.2)
      {p | sectorLocalComplex p.1 p.2 ≠ 0} := by
    unfold sectorUnfoldAngle
    have hbase : ContinuousOn (fun _ : unitInterval × unitInterval =>
        (k.val : ℝ) + 1) {p | sectorLocalComplex p.1 p.2 ≠ 0} :=
      continuousOn_const
    have hpi : ContinuousOn (fun _ : unitInterval × unitInterval => Real.pi)
        {p | sectorLocalComplex p.1 p.2 ≠ 0} := continuousOn_const
    have hquot := (continuousOn_sectorLocalAngle_nonzero).div hpi
      (fun _ _ => Real.pi_ne_zero)
    exact (continuousOn_const.mul (hbase.sub hquot)).div continuousOn_const
      (fun _ _ => by norm_num)
  unfold sectorUnfoldPoint
  have hcircle : ContinuousOn (fun p : unitInterval × unitInterval =>
      (Circle.exp (sectorUnfoldAngle k p.1 p.2) : ℂ))
      {p | sectorLocalComplex p.1 p.2 ≠ 0} :=
    continuous_subtype_val.comp_continuousOn
      (Circle.exp.continuous.comp_continuousOn hangle)
  exact continuous_sectorLocalRadius.continuousOn.smul hcircle

theorem continuous_sectorUnfoldPoint (k : Fin 8) :
    Continuous (fun p : unitInterval × unitInterval =>
      sectorUnfoldPoint k p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : sectorLocalComplex p.1 p.2 = 0
  · have hρ0 : sectorLocalRadius p.1 p.2 = 0 := by
      simp [sectorLocalRadius, hp]
    have hpoint : sectorUnfoldPoint k p.1 p.2 = 0 := by
      simp [sectorUnfoldPoint, hρ0]
    rw [ContinuousAt, hpoint, tendsto_zero_iff_norm_tendsto_zero]
    have hρ := continuous_sectorLocalRadius.continuousAt (x := p)
    simpa only [sectorUnfoldPoint_norm, hρ0] using hρ.tendsto
  · have hopen : IsOpen {q : unitInterval × unitInterval |
        sectorLocalComplex q.1 q.2 ≠ 0} := by
      have hne : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
      exact hne.preimage continuous_sectorLocalComplex
    exact (continuousOn_sectorUnfoldPoint_nonzero k).continuousAt
      (hopen.mem_nhds hp)

/-! Each shallow source sector is compact, so the source and planar maps are
    homeomorphisms onto their respective images. -/

def shallowParams : Set (unitInterval × unitInterval) :=
  {p | (p.1 : ℝ) ≤ 1 / 2}

theorem shallowParams_isClosed : IsClosed shallowParams := by
  have hc : Continuous (fun p : unitInterval × unitInterval => (p.1 : ℝ)) := by
    fun_prop
  exact isClosed_Iic.preimage hc

instance : CompactSpace shallowParams :=
  shallowParams_isClosed.isClosedEmbedding_subtypeVal.compactSpace

noncomputable def shallowSource (i : Side) (p : shallowParams) : Disk :=
  radialSector i p.1.1 p.1.2

theorem continuous_shallowSource (i : Side) : Continuous (shallowSource i) :=
  (continuous_radialSector i).comp continuous_subtype_val

theorem shallowSource_injective (i : Side) : Function.Injective (shallowSource i) := by
  intro p q hpq
  have hrne : p.1.1 ≠ (1 : unitInterval) := by
    intro h
    have hp := p.2
    change (p.1.1 : ℝ) ≤ 1 / 2 at hp
    rw [h] at hp
    norm_num at hp
  obtain ⟨hr, ht⟩ := radialSector_injective_fixed_side i
    p.1.1 q.1.1 p.1.2 q.1.2 hrne hpq
  exact Subtype.ext (Prod.ext hr ht)

theorem shallowSource_isClosedEmbedding (i : Side) :
    Topology.IsClosedEmbedding (shallowSource i) :=
  (continuous_shallowSource i).isClosedEmbedding (shallowSource_injective i)

noncomputable def shallowPlane (k : Fin 8) (p : shallowParams) : ℂ :=
  sectorUnfoldPoint k p.1.1 p.1.2

theorem continuous_shallowPlane (k : Fin 8) : Continuous (shallowPlane k) :=
  (continuous_sectorUnfoldPoint k).comp continuous_subtype_val

theorem shallowPlane_injective (k : Fin 8) : Function.Injective (shallowPlane k) := by
  intro p q hpq
  obtain ⟨hr, ht⟩ := sectorUnfoldPoint_injective_fixed_sector k
    p.1.1 q.1.1 p.1.2 q.1.2 hpq
  exact Subtype.ext (Prod.ext hr ht)

theorem shallowPlane_isClosedEmbedding (k : Fin 8) :
    Topology.IsClosedEmbedding (shallowPlane k) :=
  (continuous_shallowPlane k).isClosedEmbedding (shallowPlane_injective k)

/-- A compact parameter space gives the same topology to two images whenever
    their continuous maps identify exactly the same fibers. -/
noncomputable def compactImagesHomeomorph
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Z] [T2Space Z]
    (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g)
    (hfiber : ∀ x y, f x = f y ↔ g x = g y) :
    Set.range f ≃ₜ Set.range g := by
  let f' : X → Set.range f := fun x => ⟨f x, ⟨x, rfl⟩⟩
  let g' : X → Set.range g := fun x => ⟨g x, ⟨x, rfl⟩⟩
  have hfc : Continuous f' := hf.subtype_mk _
  have hgc : Continuous g' := hg.subtype_mk _
  have hfs : Function.Surjective f' := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hgs : Function.Surjective g' := by
    rintro ⟨z, x, rfl⟩
    exact ⟨x, rfl⟩
  have hfq : Topology.IsQuotientMap f' :=
    hfc.isClosedMap.isQuotientMap hfc hfs
  have hgq : Topology.IsQuotientMap g' :=
    hgc.isClosedMap.isQuotientMap hgc hgs
  let F : Set.range f → Set.range g := fun y =>
    ⟨g (Classical.choose y.property),
      ⟨Classical.choose y.property, rfl⟩⟩
  let G : Set.range g → Set.range f := fun z =>
    ⟨f (Classical.choose z.property),
      ⟨Classical.choose z.property, rfl⟩⟩
  have hFcomp : F ∘ f' = g' := by
    funext x
    apply Subtype.ext
    apply (hfiber _ _).mp
    exact Classical.choose_spec (f' x).property
  have hGcomp : G ∘ g' = f' := by
    funext x
    apply Subtype.ext
    apply (hfiber _ _).mpr
    exact Classical.choose_spec (g' x).property
  have hFc : Continuous F := by
    apply (hfq.continuous_iff).mpr
    simpa only [hFcomp] using hgc
  have hGc : Continuous G := by
    apply (hgq.continuous_iff).mpr
    simpa only [hGcomp] using hfc
  let e : Set.range f ≃ Set.range g := {
    toFun := F
    invFun := G
    left_inv := by
      intro y
      obtain ⟨x, rfl⟩ := hfs y
      have h1 : F (f' x) = g' x := congrFun hFcomp x
      have h2 : G (g' x) = f' x := congrFun hGcomp x
      rw [h1]
      exact h2
    right_inv := by
      intro z
      obtain ⟨x, rfl⟩ := hgs z
      have h1 : F (f' x) = g' x := congrFun hFcomp x
      have h2 : G (g' x) = f' x := congrFun hGcomp x
      rw [h2]
      exact h1 }
  exact {
    toEquiv := e
    continuous_toFun := hFc
    continuous_invFun := hGc }

/-! The compact eight-piece model excludes the spurious overlap of adjacent
    source radial rectangles along polygon side midpoints. -/

def quarterParams : Set (unitInterval × unitInterval) :=
  {p | sectorLocalRadius p.1 p.2 ≤ 1 / 4}

theorem quarterParams_isClosed : IsClosed quarterParams := by
  exact isClosed_Iic.preimage continuous_sectorLocalRadius

instance : CompactSpace quarterParams :=
  quarterParams_isClosed.isClosedEmbedding_subtypeVal.compactSpace

theorem quarterParams_bounds (p : quarterParams) :
    (p.1.1 : ℝ) ≤ 1 / 4 ∧
      1 / 4 ≤ (p.1.2 : ℝ) ∧ (p.1.2 : ℝ) ≤ 3 / 4 := by
  have hrad : sectorLocalRadius p.1.1 p.1.2 ≤ 1 / 4 := p.2
  have him := Complex.im_le_norm (sectorLocalComplex p.1.1 p.1.2)
  have hre := Complex.abs_re_le_norm (sectorLocalComplex p.1.1 p.1.2)
  rw [sectorLocalComplex_im] at him
  rw [sectorLocalComplex_re] at hre
  change (p.1.1 : ℝ) ≤ sectorLocalRadius p.1.1 p.1.2 at him
  change |(p.1.2 : ℝ) - 1 / 2| ≤
    sectorLocalRadius p.1.1 p.1.2 at hre
  rcases abs_le.mp hre with ⟨hlo, hhi⟩
  constructor
  · linarith
  constructor <;> linarith

theorem radialSector_eq_of_quarter_bounds
    (i j : Side) (r s t u : unitInterval)
    (hr : (r : ℝ) ≤ 1 / 4)
    (htlo : (1 : ℝ) / 4 ≤ t) (hthi : (t : ℝ) ≤ 3 / 4)
    (hulo : (1 : ℝ) / 4 ≤ u) (huhi : (u : ℝ) ≤ 3 / 4)
    (heq : radialSector i r t = radialSector j s u) :
    i = j ∧ r = s ∧ t = u := by
  have hrs := radialSector_eq_implies_radial_eq i j r s t u heq
  subst s
  have hpos : 0 < sectorRadial r := by
    unfold sectorRadial
    linarith
  have hcomplex :
      (Circle.exp (2 * Real.pi * sectorSourceAngle i t / 8) : ℂ) =
        (Circle.exp (2 * Real.pi * sectorSourceAngle j u / 8) : ℂ) := by
    have hh := congrArg (fun x : Disk => (x : ℂ)) heq
    change (1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * sectorSourceAngle i t / 8) : ℂ) =
      (1 - (r : ℝ)) •
      (Circle.exp (2 * Real.pi * sectorSourceAngle j u / 8) : ℂ) at hh
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul, smul_eq_mul] at hh
    have hreal : (1 - (r : ℝ)) ≠ 0 := by
      simpa [sectorRadial] using ne_of_gt hpos
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hreal) hh
  have hcircle : Circle.exp (2 * Real.pi * sectorSourceAngle i t / 8) =
      Circle.exp (2 * Real.pi * sectorSourceAngle j u / 8) :=
    Circle.ext hcomplex
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
  have hang : (i.val : ℝ) + t = (j.val : ℝ) + u + 8 * (m : ℝ) := by
    have h' := hm
    dsimp [sectorSourceAngle] at h'
    field_simp [Real.pi_ne_zero] at h'
    nlinarith [h']
  have hi0 : (0 : ℝ) ≤ i.val := by exact_mod_cast (Nat.zero_le i.val)
  have hj0 : (0 : ℝ) ≤ j.val := by exact_mod_cast (Nat.zero_le j.val)
  have hi7 : (i.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hj7 : (j.val : ℝ) ≤ 7 := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hm0 : m = 0 := by
    by_contra hmne
    rcases lt_or_gt_of_ne hmne with hneg | hpos
    · have hmle : (m : ℝ) ≤ -1 := by
        exact_mod_cast (show m ≤ -1 by omega)
      linarith
    · have hmge : (m : ℝ) ≥ 1 := by
        exact_mod_cast (show m ≥ 1 by omega)
      linarith
  simp only [hm0, Int.cast_zero, mul_zero, add_zero] at hang
  have hij : i = j := by
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · have hgap : (i.val : ℝ) + 1 ≤ j.val := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      exfalso
      linarith
    · exact Fin.ext heq
    · have hgap : (j.val : ℝ) + 1 ≤ i.val := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      exfalso
      linarith
  subst j
  have htu : t = u := Subtype.ext (by linarith)
  exact ⟨rfl, rfl, htu⟩

abbrev vertexModel := Fin 8 × quarterParams

private theorem continuous_fin8_product {Y : Type*} [TopologicalSpace Y]
    (f : Fin 8 → quarterParams → Y)
    (hf : ∀ k, Continuous (f k)) :
    Continuous (fun p : vertexModel => f p.1 p.2) := by
  apply continuous_of_continuousOn_iUnion_of_isOpen
    (s := fun k : Fin 8 => {p : vertexModel | p.1 = k})
  · intro k
    have hc : Continuous (fun p : vertexModel => f k p.2) :=
      (hf k).comp continuous_snd
    apply hc.continuousOn.congr
    intro p hp
    exact congrArg (fun i => f i p.2) hp
  · intro k
    have hs : IsOpen ({k} : Set (Fin 8)) := isOpen_discrete _
    change IsOpen ((fun p : vertexModel => p.1) ⁻¹' ({k} : Set (Fin 8)))
    exact hs.preimage
      (continuous_fst : Continuous (fun p : vertexModel => p.1))
  · ext p
    simp

noncomputable def vertexModelSource (p : vertexModel) : Surface :=
  mk (radialSector (vertexCycle p.1) p.2.1.1 p.2.1.2)

noncomputable def vertexModelPlane (p : vertexModel) : ℂ :=
  sectorUnfoldPoint p.1 p.2.1.1 p.2.1.2

theorem continuous_vertexModelSource : Continuous vertexModelSource := by
  unfold vertexModelSource
  apply continuous_mk.comp
  have hpiece : ∀ k : Fin 8, Continuous (fun p : quarterParams =>
      radialSector (vertexCycle k) p.1.1 p.1.2) := by
    intro k
    exact (continuous_radialSector _).comp continuous_subtype_val
  exact continuous_fin8_product _ hpiece

theorem continuous_vertexModelPlane : Continuous vertexModelPlane := by
  unfold vertexModelPlane
  have hpiece : ∀ k : Fin 8, Continuous (fun p : quarterParams =>
      sectorUnfoldPoint k p.1.1 p.1.2) := by
    intro k
    exact (continuous_sectorUnfoldPoint k).comp continuous_subtype_val
  exact continuous_fin8_product _ hpiece

private noncomputable def centerHalf : unitInterval :=
  ⟨1 / 2, by constructor <;> norm_num⟩

theorem quarterParams_vertex_iff_radius_zero (k : Fin 8) (p : quarterParams) :
    mk (radialSector (vertexCycle k) p.1.1 p.1.2) = mk (vertexPoint 0) ↔
      sectorLocalRadius p.1.1 p.1.2 = 0 := by
  constructor
  · intro hmk
    have hx : radialSector (vertexCycle k) p.1.1 p.1.2 ∈ vertexSet := by
      rw [← vertex_fiber_eq_vertexSet 0]
      exact hmk
    obtain ⟨j, hj⟩ := hx
    have hsource : radialSector (vertexCycle k) p.1.1 p.1.2 =
        radialSector j 0 centerHalf := by
      exact hj.symm.trans (by simpa [centerHalf] using (radialSector_center j).symm)
    obtain ⟨hrb, htl, htu⟩ := quarterParams_bounds p
    obtain ⟨_, hr, ht⟩ := radialSector_eq_of_quarter_bounds
      (vertexCycle k) j p.1.1 0 p.1.2 centerHalf hrb htl htu
      (by norm_num [centerHalf]) (by norm_num [centerHalf]) hsource
    rw [hr, ht]
    simp [sectorLocalRadius, sectorLocalComplex, centerHalf]
  · intro hρ
    have hr : p.1.1 = (0 : unitInterval) := by
      apply Subtype.ext
      have h := sectorLocal_radius_sin p.1.1 p.1.2
      rw [hρ] at h
      simpa using h.symm
    have ht : p.1.2 = centerHalf := by
      apply Subtype.ext
      have h := sectorLocal_radius_cos p.1.1 p.1.2
      rw [hρ] at h
      dsimp [centerHalf]
      linarith
    rw [hr, ht]
    change mk (radialSector (vertexCycle k) 0
      (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) =
      mk (vertexPoint 0)
    exact radialSector_center_quotient (vertexCycle k)

theorem vertexModel_vertex_iff_plane_zero (p : vertexModel) :
    vertexModelSource p = mk (vertexPoint 0) ↔ vertexModelPlane p = 0 := by
  rw [vertexModelSource, quarterParams_vertex_iff_radius_zero]
  constructor
  · intro hρ
    simp [vertexModelPlane, sectorUnfoldPoint, hρ]
  · intro hp
    have hn := congrArg (fun z : ℂ => ‖z‖) hp
    rw [vertexModelPlane, sectorUnfoldPoint_norm] at hn
    simpa using hn

/-- Once the remaining cross-sector fiber comparison is established, compact
    quotient descent supplies the closed vertex chart with continuous inverse. -/
noncomputable def vertexClosedChart
    (hfiber : ∀ p q : vertexModel,
      vertexModelSource p = vertexModelSource q ↔
        vertexModelPlane p = vertexModelPlane q) :
    Set.range vertexModelSource ≃ₜ Set.range vertexModelPlane := by
  letI : T2Space Surface := quotient_t2
  exact compactImagesHomeomorph vertexModelSource vertexModelPlane
    continuous_vertexModelSource continuous_vertexModelPlane hfiber

end CurveComplex.Octagon
