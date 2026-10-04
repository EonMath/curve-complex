import CurveComplexGenusTwo.Foundations.SourceNonseparating
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualInternalSurfaceSides
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture

namespace CurveComplex
open Set Topology Schoenflies CategoryTheory
open CurveComplexGenusTwo.CWHurewicz

-- Ephemeral construction of the actual two complementary regions of an
-- original separating curve; no component or collar certificate is assumed.
theorem source_separating_curve_actual_complementary_regions
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (c : Curve S) (hc : ¬ Nonseparating c) :
    ∃ L R : Set S, IsOpen L ∧ IsOpen R ∧ IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧ L ∪ R = c.imageᶜ ∧
      homologyInclusion S L 2 = 0 ∧ homologyInclusion S R 2 = 0 := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  let : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
  have hlocal (p : S) (hp : p ∈ c.image) :
      ∃ C : SurfaceLocalSides (Set.univ : Set S) c.image, p ∈ C.nbhd := by
    obtain ⟨U,V,hpU,h,hU,hV,hzero,haxis⟩ := LocalSurgery.embedded_curve_has_local_axis_chart c p hp
    have h0V : ((0,0) : ℝ × ℝ) ∈ V := hzero ▸ (h ⟨p,hpU⟩).property
    obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV (0,0) h0V
    let δ : ℝ := r/2
    have hδ : 0 < δ := half_pos hr
    let J := Set.Icc (-δ) δ
    have hqV (z : J × J) : ((z.2:ℝ),(z.1:ℝ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
      have hz0 : |(z.1:ℝ)| ≤ δ := abs_le.mpr z.1.property
      have hz1 : |(z.2:ℝ)| ≤ δ := abs_le.mpr z.2.property
      constructor <;> dsimp [δ] at * <;> linarith
    let q : J × J → V := fun z => ⟨((z.2:ℝ),(z.1:ℝ)),hqV z⟩
    have hq : Continuous q := (by fun_prop : Continuous (fun z : J × J => ((z.2:ℝ),(z.1:ℝ)))).subtype_mk _
    have hqi : Function.Injective q := by
      intro x y he
      have hh := congrArg Subtype.val he
      exact Prod.ext (Subtype.ext (congrArg Prod.snd hh)) (Subtype.ext (congrArg Prod.fst hh))
    let B : J × J → S := fun z => (h.symm (q z)).val
    have hB : IsEmbedding B := by
      have hcont : Continuous B := continuous_subtype_val.comp (h.symm.continuous.comp hq)
      have hinj : Function.Injective B :=
        Subtype.val_injective.comp (h.symm.injective.comp hqi)
      exact (hcont.isClosedEmbedding hinj).isEmbedding
    have hBP (z : J × J) : B z ∈ c.image ↔ (z.2:ℝ) = 0 := by
      have hh := haxis (B z) (h.symm (q z)).property
      have he : h ⟨B z,(h.symm (q z)).property⟩ = q z := h.apply_symm_apply (q z)
      rw [he] at hh
      exact hh
    obtain ⟨C,hcenter⟩ := source_embedded_rectangle_local_sides
      (by linarith : -δ < δ) (neg_lt_zero.mpr hδ) hδ B hB
      Set.univ c.image (Set.subset_univ _) hBP
    let z : J := ⟨0,⟨by linarith,by linarith⟩⟩
    have hBp : B (z,z) = p := by
      have he : q (z,z) = h ⟨p,hpU⟩ := by
        apply Subtype.ext
        exact hzero.symm
      dsimp [B]
      rw [he,h.symm_apply_apply]
    exact ⟨C,hBp ▸ hcenter z (by dsimp [z]; linarith) (by dsimp [z]; linarith)⟩
  have hclosed : IsClosed c.image := (isCompact_range c.embedded.continuous).isClosed
  have hconn : IsConnected ((Set.univ : Set S) ∩ c.image) := by
    rw [Set.univ_inter]
    exact isConnected_range c.embedded.continuous
  obtain ⟨l,hl,r,hr,hcover⟩ := theta_at_most_two_of_local_sides
    isOpen_univ isPreconnected_univ hclosed hconn (fun p hp => hlocal p hp.2)
  let L := connectedComponentIn (c.imageᶜ) l
  let R := connectedComponentIn (c.imageᶜ) r
  have hl' : l ∈ c.imageᶜ := hl.2
  have hr' : r ∈ c.imageᶜ := hr.2
  have hcover' : L ∪ R = c.imageᶜ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
    · intro x hx
      have hh := hcover x ⟨Set.mem_univ _,hx⟩
      change x ∈ connectedComponentIn c.imageᶜ l ∨ x ∈ connectedComponentIn c.imageᶜ r
      simpa only [← Set.compl_eq_univ_sdiff] using hh
  have hL : IsConnected L := isConnected_connectedComponentIn_iff.mpr hl'
  have hR : IsConnected R := isConnected_connectedComponentIn_iff.mpr hr'
  have hne : L ≠ R := by
    intro he
    have hall : L = c.imageᶜ := by simpa only [he,Set.union_self] using hcover'
    apply hc
    change IsConnected c.imageᶜ
    exact hall ▸ hL
  have hdis : Disjoint L R := by
    rw [Set.disjoint_left]
    intro x hxL hxR
    exact hne ((connectedComponentIn_eq hxL).trans (connectedComponentIn_eq hxR).symm)
  have hproper (A : Set S) (x : S) (hx : x ∉ A) : homologyInclusion S A 2 = 0 := by
    let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ ℤ)
    let j : TopCat.of A ⟶ TopCat.of ↥({x}ᶜ : Set S) :=
      TopCat.ofHom ⟨fun a => ⟨a.val,fun he => hx (he ▸ a.property)⟩,
        continuous_subtype_val.subtype_mk _⟩
    have he : j ≫ pairInclusion S ({x}ᶜ : Set S) = pairInclusion S A := by
      ext a
      rfl
    change F.map (pairInclusion S A) = 0
    rw [← he,F.map_comp]
    change F.map j ≫ homologyInclusion S ({x}ᶜ : Set S) 2 = 0
    rw [GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x,
      CategoryTheory.Limits.comp_zero]
  have hLzero : homologyInclusion S L 2 = 0 := hproper L r
    (fun hh => Set.disjoint_left.mp hdis hh (mem_connectedComponentIn hr'))
  have hRzero : homologyInclusion S R 2 = 0 := hproper R l
    (fun hh => Set.disjoint_left.mp hdis (mem_connectedComponentIn hl') hh)
  exact ⟨L,R,hclosed.isOpen_compl.connectedComponentIn,
    hclosed.isOpen_compl.connectedComponentIn,hL,hR,hdis,hcover',hLzero,hRzero⟩

end CurveComplex
