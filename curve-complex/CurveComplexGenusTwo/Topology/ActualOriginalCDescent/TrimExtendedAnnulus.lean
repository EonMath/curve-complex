import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.UniformBranchFreeStrip

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem trim_extended_annulus_away_from_closed_set
    {S : Type} [TopologicalSpace S] [T2Space S]
    (B : Set S) (hBclosed : IsClosed B)
    (g : C(Circle × Set.Icc (-2:ℝ) 3,S)) (hg : Topology.IsEmbedding g)
    (hcentral : ∀ (z : Circle) (t : Set.Icc (-2:ℝ) 3),
      0 ≤ (t:ℝ) → (t:ℝ) ≤ 1 → g (z,t) ∉ B) :
    ∃ g' : C(Circle × Set.Icc (-2:ℝ) 3,S),
      Topology.IsEmbedding g' ∧
      (∀ z : Circle, g' (z,⟨0,by norm_num⟩) = g (z,⟨0,by norm_num⟩)) ∧
      (∀ z : Circle, g' (z,⟨1,by norm_num⟩) = g (z,⟨1,by norm_num⟩)) ∧
      Disjoint (Set.range g') B := by
  obtain ⟨δ,hδpos,hδle,hstrip⟩ := uniform_branch_free_strip B hBclosed g hcentral
  let lam : ℝ := δ/4
  have hlamPos : 0 < lam := by dsimp [lam]; positivity
  have hlamLe : lam ≤ 1 := by dsimp [lam]; linarith
  let clamp : ℝ → ℝ := fun t => min (max t 0) 1
  have hclampMono : Monotone clamp := by
    intro a b hab
    exact min_le_min (max_le_max hab le_rfl) le_rfl
  have hclampBounds (t : ℝ) : 0 ≤ clamp t ∧ clamp t ≤ 1 := by
    dsimp [clamp]
    constructor
    · exact le_min (le_max_right _ _) zero_le_one
    · exact min_le_right _ _
  let rReal : ℝ → ℝ := fun t => lam*t + (1-lam)*clamp t
  have hrStrict : StrictMono rReal := by
    intro a b hab
    dsimp [rReal]
    have hlt : lam*a < lam*b := mul_lt_mul_of_pos_left hab hlamPos
    have hle : (1-lam)*clamp a ≤ (1-lam)*clamp b :=
      mul_le_mul_of_nonneg_left (hclampMono hab.le) (by linarith)
    linarith
  have hrCont : Continuous rReal := by
    dsimp [rReal,clamp]
    fun_prop
  have hrBounds (t : ℝ) (ht : t ∈ Set.Icc (-2:ℝ) 3) :
      rReal t ∈ Set.Icc (-2:ℝ) 3 := by
    obtain ⟨htL,htR⟩ := ht
    obtain ⟨hcL,hcR⟩ := hclampBounds t
    dsimp [rReal]
    constructor
    · have hmul : (-2:ℝ)*lam ≤ t*lam := mul_le_mul_of_nonneg_right htL hlamPos.le
      nlinarith
    · have hmul : t*lam ≤ (3:ℝ)*lam := mul_le_mul_of_nonneg_right htR hlamPos.le
      nlinarith
  let r : Set.Icc (-2:ℝ) 3 → Set.Icc (-2:ℝ) 3 :=
    fun t => ⟨rReal t.val,hrBounds t.val t.property⟩
  have hrCont' : Continuous r :=
    (hrCont.comp continuous_subtype_val).subtype_mk _
  have hrInj : Function.Injective r := by
    intro a b hab
    apply Subtype.ext
    exact hrStrict.injective (congrArg Subtype.val hab)
  have hr0 : r (⟨0,by norm_num⟩ : Set.Icc (-2:ℝ) 3) =
      ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    norm_num [r,rReal,clamp]
  have hr1 : r (⟨1,by norm_num⟩ : Set.Icc (-2:ℝ) 3) =
      ⟨1,by norm_num⟩ := by
    apply Subtype.ext
    norm_num [r,rReal,clamp]
  have hrStrip (t : Set.Icc (-2:ℝ) 3) :
      -δ ≤ (r t:ℝ) ∧ (r t:ℝ) ≤ 1+δ := by
    obtain ⟨htL,htR⟩ := t.property
    obtain ⟨hcL,hcR⟩ := hclampBounds t.val
    change -δ ≤ rReal t.val ∧ rReal t.val ≤ 1+δ
    dsimp [rReal]
    constructor
    · have hmul : (-2:ℝ)*lam ≤ t.val*lam := mul_le_mul_of_nonneg_right htL hlamPos.le
      dsimp [lam] at *
      nlinarith
    · have hmul : t.val*lam ≤ (3:ℝ)*lam := mul_le_mul_of_nonneg_right htR hlamPos.le
      dsimp [lam] at *
      nlinarith
  let f : Circle × Set.Icc (-2:ℝ) 3 → S := fun p => g (p.1,r p.2)
  have hfCont : Continuous f := g.continuous.comp
    (continuous_fst.prodMk (hrCont'.comp continuous_snd))
  let g' : C(Circle × Set.Icc (-2:ℝ) 3,S) := ⟨f,hfCont⟩
  have hg' : Topology.IsEmbedding g' := by
    have hinj : Function.Injective g' := by
      intro a b hab
      have hp := hg.injective hab
      have hfirst' := congrArg Prod.fst hp
      have hsecond' := congrArg Prod.snd hp
      have hfirst : a.1 = b.1 := hfirst'
      have hsecond : a.2 = b.2 := hrInj hsecond'
      exact Prod.ext hfirst hsecond
    exact (g'.continuous.isClosedEmbedding hinj).isEmbedding
  refine ⟨g',hg',?_,?_,?_⟩
  · intro z
    change g (z,r ⟨0,by norm_num⟩) = g (z,⟨0,by norm_num⟩)
    rw [hr0]
  · intro z
    change g (z,r ⟨1,by norm_num⟩) = g (z,⟨1,by norm_num⟩)
    rw [hr1]
  · apply Set.disjoint_left.mpr
    rintro y ⟨⟨z,t⟩,rfl⟩ hy
    exact hstrip z (r t) (hrStrip t).1 (hrStrip t).2 hy

end CurveComplex.HyperellipticModel
