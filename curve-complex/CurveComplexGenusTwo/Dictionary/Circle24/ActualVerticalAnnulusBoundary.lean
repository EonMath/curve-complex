import CurveComplexGenusTwo.Dictionary.Circle24.RectanglePrescribedOuterEdges
import CurveComplexGenusTwo.Dictionary.Circle24.LateBoundaryFiberRange
import CurveComplexGenusTwo.Dictionary.Circle24.RectangleExteriorBoundaryLoops
import CurveComplexGenusTwo.Dictionary.Circle24.SquarePairCylinderEdgeRanges
import CurveComplexGenusTwo.Dictionary.Circle24.UnbranchedRectangle
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 15000000

/-- Construct the actual full annulus above a two-mark rectangle by filling
both one-mark cells from the common seam lift, then proving the complete
crossed-edge collision relation. No upstairs cell or annulus is assumed. -/
theorem two_mark_rectangle_actual_annulus_vertical_boundary
    (M : HyperellipticModel E S)
    (f : C(Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1,S)) (hf : IsEmbedding f)
    (p q : Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)
    (hmarks : ∀ z, f z ∈ M.cover.branch ↔ z=p ∨ z=q)
    (hp : p.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
    (hq : q.val ∈ interior (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
    (k : ℝ) (hk0 : -1<k) (hk1 : k<1) (hpk : p.val.1<k) (hkq : k<q.val.1) :
    ∃ H : Circle × Interval ≃ₜ M.cover.projection ⁻¹' Set.range f,
      Set.range (fun z : Circle => (H (z,0)).val) ∪
        Set.range (fun z : Circle => (H (z,1)).val)=
        M.cover.projection ⁻¹' (f '' {z | z.val ∈ frontier (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)}) := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : LocallyPathConnectedSpace Interval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  let L := Icc (-1:ℝ) k ×ˢ Icc (-1:ℝ) 1
  let R := Icc k (1:ℝ) ×ˢ Icc (-1:ℝ) 1
  let K := Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  have hsubL : L ⊆ K := by
    rintro z ⟨hx,hy⟩; exact ⟨⟨hx.1,hx.2.trans hk1.le⟩,hy⟩
  have hsubR : R ⊆ K := by
    rintro z ⟨hx,hy⟩; exact ⟨⟨hk0.le.trans hx.1,hx.2⟩,hy⟩
  let f₀ : C(L,S) := f.comp ⟨Set.inclusion hsubL,continuous_inclusion hsubL⟩
  let f₁ : C(R,S) := f.comp ⟨Set.inclusion hsubR,continuous_inclusion hsubR⟩
  have hpb : (-1<p.val.1 ∧ p.val.1<1) ∧ (-1<p.val.2 ∧ p.val.2<1) := by
    simpa only [interior_prod_eq,interior_Icc,mem_prod,mem_Ioo] using hp
  have hqb : (-1<q.val.1 ∧ q.val.1<1) ∧ (-1<q.val.2 ∧ q.val.2<1) := by
    simpa only [interior_prod_eq,interior_Icc,mem_prod,mem_Ioo] using hq
  let m₀ : L := ⟨p.val,⟨⟨hpb.1.1.le,hpk.le⟩,⟨hpb.2.1.le,hpb.2.2.le⟩⟩⟩
  let m₁ : R := ⟨q.val,⟨⟨hkq.le,hqb.1.2.le⟩,⟨hqb.2.1.le,hqb.2.2.le⟩⟩⟩
  have hm₀ : m₀.val ∈ interior L := by
    simp only [L,interior_prod_eq,interior_Icc,mem_prod,mem_Ioo]
    exact ⟨⟨hpb.1.1,hpk⟩,hpb.2⟩
  have hm₁ : m₁.val ∈ interior R := by
    simp only [R,interior_prod_eq,interior_Icc,mem_prod,mem_Ioo]
    exact ⟨⟨hkq,hqb.1.2⟩,hqb.2⟩
  have hc₀ (z : L) : f₀ z ∈ M.cover.branch ↔ z=m₀ := by
    change f ⟨z.val,hsubL z.property⟩ ∈ M.cover.branch ↔ z=m₀
    rw [hmarks]
    constructor
    · rintro (he | he)
      · apply Subtype.ext; exact congrArg (fun z : K => z.val) he
      · have hx := congrArg (fun z : K => z.val.1) he
        exact False.elim ((not_le_of_gt hkq) (hx ▸ z.property.1.2))
    · intro he; left
      apply Subtype.ext; exact congrArg (fun z : L => z.val) he
  have hc₁ (z : R) : f₁ z ∈ M.cover.branch ↔ z=m₁ := by
    change f ⟨z.val,hsubR z.property⟩ ∈ M.cover.branch ↔ z=m₁
    rw [hmarks]
    constructor
    · rintro (he | he)
      · have hx := congrArg (fun z : K => z.val.1) he
        exact False.elim ((not_le_of_gt hpk) (hx ▸ z.property.1.1))
      · apply Subtype.ext; exact congrArg (fun z : K => z.val) he
    · intro he; right
      apply Subtype.ext; exact congrArg (fun z : R => z.val) he
  let θ : C(Interval,K) := ⟨fun t => ⟨(k,2*t.val-1),⟨⟨hk0.le,hk1.le⟩,
    ⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩⟩,by
      apply Continuous.subtype_mk
      exact continuous_const.prodMk ((continuous_subtype_val.const_mul 2).sub continuous_const)⟩
  let g : C(Interval,S) := f.comp θ
  have hθinj : Function.Injective θ := by
    intro s t he
    have h := congrArg (fun z : K => z.val.2) he
    apply Subtype.ext
    dsimp [θ] at h
    linarith
  have hg : IsEmbedding g := hf.comp (θ.continuous.isClosedEmbedding hθinj).isEmbedding
  have havoid (t) : g t ∉ M.cover.branch := by
    change f (θ t) ∉ M.cover.branch
    rw [hmarks]
    rintro (he | he)
    · have hx := congrArg (fun z : K => z.val.1) he
      change k=p.val.1 at hx
      linarith
    · have hx := congrArg (fun z : K => z.val.1) he
      change k=q.val.1 at hx
      linarith
  obtain ⟨η,δ,hη,hδ,hηπ,hδπ,hδdeck,hdisj,hcover⟩ :=
    M.cover.compact_simplyConnected_two_sheet_lifts g hg havoid 0
  obtain ⟨β₀,β₁,he₀,he₁,hcoll₀,hcoll₁,hr₀,hr₁,hhalf₀,hhalf₁,houterloops⟩ :=
    rectangle_cut_boundary_loops_exterior (-1) k 1 (-1) 1 hk0 hk1 (by norm_num)
  have hseg (t : Interval) : Path.segment (k,(-1:ℝ)) (k,1) t=(k,2*t.val-1) := by
    simp [Path.segment_apply,AffineMap.lineMap_apply,smul_eq_mul]
    ring
  have hp₀ (t) : M.cover.projection (η t)=f₀ (β₀ (halfInterval t)) := by
    rw [hηπ]
    change f (θ t)=f ⟨(β₀ (halfInterval t)).val,hsubL (β₀ (halfInterval t)).property⟩
    apply congrArg f
    apply Subtype.ext
    rw [hhalf₀,hseg]
    rfl
  have hp₁ (t) : M.cover.projection (η t)=f₁ (β₁ (halfInterval t)) := by
    rw [hηπ]
    change f (θ t)=f ⟨(β₁ (halfInterval t)).val,hsubR (β₁ (halfInterval t)).property⟩
    apply congrArg f
    apply Subtype.ext
    rw [hhalf₁,hseg]
    rfl
  obtain ⟨D₀,hD₀L,hD₀R,γ₀,hγ₀π,hTop₀,hBottom₀⟩ := M.one_mark_rectangle_square_prescribed_outer_edges
    (-1) k (-1) 1 hk0 (by norm_num) f₀ (hf.comp (Topology.IsEmbedding.inclusion hsubL))
      m₀ hm₀ hc₀ β₀ he₀ hcoll₀ hr₀ η hp₀
  obtain ⟨D₁,hD₁L,hD₁R,γ₁,hγ₁π,hTop₁,hBottom₁⟩ := M.one_mark_rectangle_square_prescribed_outer_edges
    k 1 (-1) 1 hk1 (by norm_num) f₁ (hf.comp (Topology.IsEmbedding.inclusion hsubR))
      m₁ hm₁ hc₁ β₁ he₁ hcoll₁ hr₁ η hp₁
  have hbaseInter : Set.range f₀ ∩ Set.range f₁=Set.range g := by
    ext y
    constructor
    · rintro ⟨⟨x,hx⟩,⟨z,hz⟩⟩
      have hev : x.val=z.val := congrArg (fun z : K => z.val) (hf.injective (hx.trans hz.symm))
      have hxk : x.val.1=k := by
        have he1 := congrArg Prod.fst hev
        linarith [x.property.1.2,z.property.1.1]
      let t : Interval := ⟨(x.val.2+1)/2,⟨by linarith [x.property.2.1],by linarith [x.property.2.2]⟩⟩
      refine ⟨t,?_⟩
      change f (θ t)=y
      trans f₀ x
      · apply congrArg f
        apply Subtype.ext
        apply Prod.ext
        · exact hxk.symm
        · dsimp [θ,t]; ring
      · exact hx
    · rintro ⟨t,rfl⟩
      have hl : (θ t).val ∈ L := ⟨⟨hk0.le,le_rfl⟩,(θ t).property.2⟩
      have hr : (θ t).val ∈ R := ⟨⟨le_rfl,hk1.le⟩,(θ t).property.2⟩
      exact ⟨⟨⟨(θ t).val,hl⟩,rfl⟩,⟨⟨(θ t).val,hr⟩,rfl⟩⟩
  have hbaseUnion : Set.range f₀ ∪ Set.range f₁=Set.range f := by
    ext y
    constructor
    · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
      · exact ⟨⟨x.val,hsubL x.property⟩,rfl⟩
      · exact ⟨⟨x.val,hsubR x.property⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      rcases le_total x.val.1 k with h | h
      · exact Or.inl ⟨⟨x.val,⟨⟨x.property.1.1,h⟩,x.property.2⟩⟩,rfl⟩
      · exact Or.inr ⟨⟨x.val,⟨⟨h,x.property.1.2⟩,x.property.2⟩⟩,rfl⟩
  have hinter : (M.cover.projection ⁻¹' Set.range f₀) ∩
      (M.cover.projection ⁻¹' Set.range f₁)=Set.range η ∪ Set.range δ := by
    rw [← Set.preimage_inter,hbaseInter,← hcover]
  obtain ⟨H,hHr⟩ := square_pair_prescribed_seams_cylinder_edge_ranges
    (M.cover.projection ⁻¹' Set.range f₀) (M.cover.projection ⁻¹' Set.range f₁)
    D₀ D₁ η δ hD₀L hD₁L (fun t => (hD₀R t).trans (hδdeck t).symm)
    (fun t => (hD₁R t).trans (hδdeck t).symm) hinter
  have hu : (M.cover.projection ⁻¹' Set.range f₀) ∪
      (M.cover.projection ⁻¹' Set.range f₁)=M.cover.projection ⁻¹' Set.range f := by
    rw [← Set.preimage_union,hbaseUnion]
  let HT := H.trans (Homeomorph.setCongr hu)
  have he₀ : Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,1))).val) ∪
      Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,0))).val)=
      M.cover.projection ⁻¹' Set.range (fun t : Interval => f₀ (β₀ (lateInterval t))) := by
    have hbot : Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,0))).val)=
      Set.range (fun t : Interval => M.cover.deck (γ₀ (lateInterval t))) := by
      ext e
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,by simpa only [unitInterval.symm_symm] using (hBottom₀ (unitInterval.symm t)).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,hBottom₀ t⟩
    simp_rw [hTop₀]
    rw [hbot]
    exact M.cover.late_boundary_fiber_range (f₀.comp β₀) γ₀ hγ₀π
  have he₁ : Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,1))).val) ∪
      Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,0))).val)=
      M.cover.projection ⁻¹' Set.range (fun t : Interval => f₁ (β₁ (lateInterval t))) := by
    have htop : Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,1))).val)=
      Set.range (fun t : Interval => γ₁ (lateInterval t)) := by
      ext e
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,(hTop₁ _).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,by simpa only [unitInterval.symm_symm] using hTop₁ t⟩
    rw [htop]
    simp_rw [hBottom₁]
    exact M.cover.late_boundary_fiber_range (f₁.comp β₁) γ₁ hγ₁π
  have hout : Set.range (fun t : Interval => f₀ (β₀ (lateInterval t))) ∪
      Set.range (fun t : Interval => f₁ (β₁ (lateInterval t)))=
      f '' {z | z.val ∈ frontier K} := by
    ext y
    constructor
    · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
      · refine ⟨⟨(β₀ (lateInterval t)).val,hsubL (β₀ _).property⟩,?_,rfl⟩
        exact houterloops ▸ Or.inl ⟨t,rfl⟩
      · refine ⟨⟨(β₁ (lateInterval t)).val,hsubR (β₁ _).property⟩,?_,rfl⟩
        exact houterloops ▸ Or.inr ⟨t,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      have hz' : z.val ∈ Set.range (fun t : Interval => (β₀ (lateInterval t)).val) ∪
          Set.range (fun t : Interval => (β₁ (lateInterval t)).val) := houterloops.symm ▸ hz
      rcases hz' with ⟨t,ht⟩ | ⟨t,ht⟩
      · left; refine ⟨t,?_⟩
        apply congrArg f; exact Subtype.ext ht
      · right; refine ⟨t,?_⟩
        apply congrArg f; exact Subtype.ext ht
  refine ⟨HT,?_⟩
  change Set.range (fun z : Circle => (H (z,0)).val) ∪
    Set.range (fun z : Circle => (H (z,1)).val)=_
  rw [hHr 0,hHr 1]
  have hshuffle (A B C D : Set E) : (A ∪ B) ∪ (C ∪ D)=(C ∪ A) ∪ (D ∪ B) := by
    ext x; simp only [mem_union]; tauto
  change ((Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,0))).val)) ∪ Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,0))).val)) ∪
    ((Set.range (fun t : Interval => (D₀ (unitSquareRaw (t,1))).val)) ∪ Set.range (fun t : Interval => (D₁ (unitSquareRaw (unitInterval.symm t,1))).val))=_
  rw [hshuffle,he₀,he₁,← Set.preimage_union,hout]

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.two_mark_rectangle_actual_annulus_vertical_boundary
