import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierGeometry
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceCircleGluingProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.BandNeighborhoodProbe
open Set Topology unitInterval
namespace CurveComplex.FrontierHeaders
set_option maxHeartbeats 2000000

theorem compatibleOutsideBands_first_side_square {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (u : BandWidth) :
    Set.range (fun t : I => B.first (t,u)) ∩ Set.range D.square =
      {B.first (0,u), B.first (1,u)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t,rfl⟩,hx⟩
    have hm : B.first (t,u) ∈ Set.range B.first ∩ Set.range D.square :=
      ⟨Set.mem_range_self _,hx⟩
    rw [B.first_square] at hm
    rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
    · dsimp only at hv
      rw [← B.first_bottom] at hv
      have he := B.first_embedded.injective hv
      have ht : t = 0 := (congrArg Prod.fst he).symm
      simp only [ht, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
    · dsimp only at hv
      rw [← B.first_top] at hv
      have he := B.first_embedded.injective hv
      have ht : t = 1 := (congrArg Prod.fst he).symm
      simp only [ht, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  · intro x hx
    rcases hx with hx | hx
    · subst x
      exact ⟨⟨0,rfl⟩, by rw [B.first_bottom]; exact Set.mem_range_self _⟩
    · subst x
      exact ⟨⟨1,rfl⟩, by rw [B.first_top]; exact Set.mem_range_self _⟩

theorem compatibleOutsideBands_second_side_square {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (B : CompatibleOutsideBands D) (u : BandWidth) :
    Set.range (fun t : I => B.second (t,u)) ∩ Set.range D.square =
      {B.second (0,u), B.second (1,u)} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨t,rfl⟩,hx⟩
    have hm : B.second (t,u) ∈ Set.range B.second ∩ Set.range D.square :=
      ⟨Set.mem_range_self _,hx⟩
    rw [B.second_square] at hm
    rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
    · dsimp only at hv
      rw [← B.second_left] at hv
      have he := B.second_embedded.injective hv
      have ht : t = 0 := (congrArg Prod.fst he).symm
      simp only [ht, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
    · dsimp only at hv
      rw [← B.second_right] at hv
      have he := B.second_embedded.injective hv
      have ht : t = 1 := (congrArg Prod.fst he).symm
      simp only [ht, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  · intro x hx
    rcases hx with hx | hx
    · subst x
      exact ⟨⟨0,rfl⟩, by rw [B.second_left]; exact Set.mem_range_self _⟩
    · subst x
      exact ⟨⟨1,rfl⟩, by rw [B.second_right]; exact Set.mem_range_self _⟩

theorem squareGap01_disjoint_squareGap30 {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Disjoint (Set.range (squareGap01 D)) (Set.range (squareGap30 D)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t,rfl⟩ ⟨u,he⟩
  change D.square (_) = D.square (_) at he
  have h := D.square_embedded.injective he
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 3)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 3)
      (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩))) u =
    ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 0)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 0)
      (squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩))) t at h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hu ht ht
  all_goals
    have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) h
    dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,
      squarePort,crossingEndRectangle,crossingSquareCorner] at hh
    dsimp [DFunLike.coe,Path.instFunLike] at hh
    ring_nf at hh
    nlinarith only [hh, D.radius_pos,
      mul_nonneg D.radius_pos.le t.property.1,
      mul_nonneg D.radius_pos.le u.property.1,
      mul_le_mul_of_nonneg_left t.property.2 D.radius_pos.le,
      mul_le_mul_of_nonneg_left u.property.2 D.radius_pos.le]

theorem squareGap01_disjoint_squareGap23 {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Disjoint (Set.range (squareGap01 D)) (Set.range (squareGap23 D)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t,rfl⟩ ⟨u,he⟩
  change D.square (_) = D.square (_) at he
  have h := D.square_embedded.injective he
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 2)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 2)
      (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩))) u =
    ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 0)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 0)
      (squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩))) t at h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hu ht ht
  all_goals
    have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) h
    dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,
      squarePort,crossingEndRectangle,crossingSquareCorner] at hh
    dsimp [DFunLike.coe,Path.instFunLike] at hh
    ring_nf at hh
    nlinarith only [hh, D.radius_pos,
      mul_nonneg D.radius_pos.le t.property.1,
      mul_nonneg D.radius_pos.le u.property.1,
      mul_le_mul_of_nonneg_left t.property.2 D.radius_pos.le,
      mul_le_mul_of_nonneg_left u.property.2 D.radius_pos.le]

theorem squareGap01_disjoint_squareGap12 {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Disjoint (Set.range (squareGap01 D)) (Set.range (squareGap12 D)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t,rfl⟩ ⟨u,he⟩
  change D.square (_) = D.square (_) at he
  have h := D.square_embedded.injective he
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 1)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 1)
      (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩))) u =
    ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 0 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 0)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 0)
      (squarePort D.radius D.radius_pos 1 ⟨1, by norm_num⟩))) t at h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hu ht ht
  all_goals
    have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.2) h
    dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,
      squarePort,crossingEndRectangle,crossingSquareCorner] at hh
    dsimp [DFunLike.coe,Path.instFunLike] at hh
    ring_nf at hh
    nlinarith only [hh, D.radius_pos,
      mul_nonneg D.radius_pos.le t.property.1,
      mul_nonneg D.radius_pos.le u.property.1,
      mul_le_mul_of_nonneg_left t.property.2 D.radius_pos.le,
      mul_le_mul_of_nonneg_left u.property.2 D.radius_pos.le]

theorem squareGap30_disjoint_squareGap23 {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Disjoint (Set.range (squareGap30 D)) (Set.range (squareGap23 D)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t,rfl⟩ ⟨u,he⟩
  change D.square (_) = D.square (_) at he
  have h := D.square_embedded.injective he
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 2)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 2)
      (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩))) u =
    ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 3)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 3)
      (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩))) t at h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hu ht ht
  all_goals
    have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.2) h
    dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,
      squarePort,crossingEndRectangle,crossingSquareCorner] at hh
    dsimp [DFunLike.coe,Path.instFunLike] at hh
    ring_nf at hh
    nlinarith only [hh, D.radius_pos,
      mul_nonneg D.radius_pos.le t.property.1,
      mul_nonneg D.radius_pos.le u.property.1,
      mul_le_mul_of_nonneg_left t.property.2 D.radius_pos.le,
      mul_le_mul_of_nonneg_left u.property.2 D.radius_pos.le]

theorem squareGap30_disjoint_squareGap12 {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Disjoint (Set.range (squareGap30 D)) (Set.range (squareGap12 D)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t,rfl⟩ ⟨u,he⟩
  change D.square (_) = D.square (_) at he
  have h := D.square_embedded.injective he
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 1)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 1)
      (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩))) u =
    ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 3)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 3)
      (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩))) t at h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hu ht ht
  all_goals
    have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) h
    dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,
      squarePort,crossingEndRectangle,crossingSquareCorner] at hh
    dsimp [DFunLike.coe,Path.instFunLike] at hh
    ring_nf at hh
    nlinarith only [hh, D.radius_pos,
      mul_nonneg D.radius_pos.le t.property.1,
      mul_nonneg D.radius_pos.le u.property.1,
      mul_le_mul_of_nonneg_left t.property.2 D.radius_pos.le,
      mul_le_mul_of_nonneg_left u.property.2 D.radius_pos.le]

theorem squareGap23_disjoint_squareGap12 {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    Disjoint (Set.range (squareGap23 D)) (Set.range (squareGap12 D)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t,rfl⟩ ⟨u,he⟩
  change D.square (_) = D.square (_) at he
  have h := D.square_embedded.injective he
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 1)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 1)
      (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩))) u =
    ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 2)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 2)
      (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩))) t at h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hu ht ht
  all_goals
    have hh := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) h
    dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,
      squarePort,crossingEndRectangle,crossingSquareCorner] at hh
    dsimp [DFunLike.coe,Path.instFunLike] at hh
    ring_nf at hh
    nlinarith only [hh, D.radius_pos,
      mul_nonneg D.radius_pos.le t.property.1,
      mul_nonneg D.radius_pos.le u.property.1,
      mul_le_mul_of_nonneg_left t.property.2 D.radius_pos.le,
      mul_le_mul_of_nonneg_left u.property.2 D.radius_pos.le]

theorem crossingSquareSegment_mem_range_iff {r : ℝ} (p q z : Metric.closedBall ((0,0):ℝ×ℝ) r) :
    z ∈ Set.range (crossingSquareSegment r p q) ↔
    (z : ℝ × ℝ) ∈ segment ℝ (p : ℝ × ℝ) (q : ℝ × ℝ) := by
  rw [← Path.range_segment]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,Subtype.ext ht⟩

theorem horizontal_segment_mem_iff (x₁ x₂ y : ℝ) (h : x₁ ≤ x₂) (z : ℝ × ℝ) :
    z ∈ segment ℝ (x₁,y) (x₂,y) ↔ x₁ ≤ z.1 ∧ z.1 ≤ x₂ ∧ z.2 = y := by
  rw [← Prod.image_mk_segment_left, segment_eq_Icc h]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx.1,hx.2,rfl⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨z.1,⟨h1,h2⟩,by ext <;> simp [h3]⟩

theorem squareGap01_port_restriction {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (i : Fin 4) (u : BandWidth)
    (hmem : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap01 D)) :
    (i = 0 ∨ i = 1) ∧ (u : ℝ) = 1 := by
  rcases hmem with ⟨t,ht⟩
  have he := D.square_embedded.injective ht
  change ((crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 0 ⟨1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 0)).trans
      (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 0)
        (squarePort D.radius D.radius_pos 1 ⟨1,by norm_num⟩))) t =
        squarePort D.radius D.radius_pos i u at he
  rw [Path.trans_apply] at he
  split_ifs at he with ht
  all_goals
    have hx := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) he
    have hy := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.2) he
    fin_cases i
    all_goals
      dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,squarePort,
        crossingEndRectangle,crossingSquareCorner,DFunLike.coe,Path.instFunLike] at hx hy
      norm_num [Fin.ext_iff]
      nlinarith [D.radius_pos,u.property.1,u.property.2,t.property.1,t.property.2]

theorem squareGap30_port_restriction {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (i : Fin 4) (u : BandWidth)
    (hmem : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap30 D)) :
    (i = 3 ∧ (u : ℝ) = 1) ∨ (i = 0 ∧ (u : ℝ) = -1) := by
  rcases hmem with ⟨t,ht⟩
  have he := D.square_embedded.injective ht
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 3 ⟨1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 3)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 3)
      (squarePort D.radius D.radius_pos 0 ⟨-1, by norm_num⟩))) t =
        squarePort D.radius D.radius_pos i u at he
  rw [Path.trans_apply] at he
  split_ifs at he with ht
  all_goals
    have hx := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) he
    have hy := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.2) he
    fin_cases i
    all_goals
      dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,squarePort,
        crossingEndRectangle,crossingSquareCorner,DFunLike.coe,Path.instFunLike] at hx hy
      norm_num [Fin.ext_iff]
      nlinarith [D.radius_pos,u.property.1,u.property.2,t.property.1,t.property.2]

theorem squareGap23_port_restriction {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (i : Fin 4) (u : BandWidth)
    (hmem : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap23 D)) :
    (i = 2 ∧ (u : ℝ) = -1) ∨ (i = 3 ∧ (u : ℝ) = -1) := by
  rcases hmem with ⟨t,ht⟩
  have he := D.square_embedded.injective ht
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 2 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 2)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 2)
      (squarePort D.radius D.radius_pos 3 ⟨-1, by norm_num⟩))) t =
        squarePort D.radius D.radius_pos i u at he
  rw [Path.trans_apply] at he
  split_ifs at he with ht
  all_goals
    have hx := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) he
    have hy := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.2) he
    fin_cases i
    all_goals
      dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,squarePort,
        crossingEndRectangle,crossingSquareCorner,DFunLike.coe,Path.instFunLike] at hx hy
      norm_num [Fin.ext_iff]
      nlinarith [D.radius_pos,u.property.1,u.property.2,t.property.1,t.property.2]

theorem squareGap12_port_restriction {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) (i : Fin 4) (u : BandWidth)
    (hmem : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap12 D)) :
    (i = 1 ∧ (u : ℝ) = -1) ∨ (i = 2 ∧ (u : ℝ) = 1) := by
  rcases hmem with ⟨t,ht⟩
  have he := D.square_embedded.injective ht
  change ((crossingSquareSegment D.radius
    (squarePort D.radius D.radius_pos 1 ⟨-1, by norm_num⟩)
    (crossingSquareCorner D.radius D.radius_pos 1)).trans
    (crossingSquareSegment D.radius
      (crossingSquareCorner D.radius D.radius_pos 1)
      (squarePort D.radius D.radius_pos 2 ⟨1, by norm_num⟩))) t =
        squarePort D.radius D.radius_pos i u at he
  rw [Path.trans_apply] at he
  split_ifs at he with ht
  all_goals
    have hx := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.1) he
    have hy := congrArg (fun z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius => z.val.2) he
    fin_cases i
    all_goals
      dsimp [crossingSquareSegment,Path.segment,AffineMap.lineMap,squarePort,
        crossingEndRectangle,crossingSquareCorner,DFunLike.coe,Path.instFunLike] at hx hy
      norm_num [Fin.ext_iff]
      nlinarith [D.radius_pos,u.property.1,u.property.2,t.property.1,t.property.2]

theorem squareGap01_mem_iff_coordinates {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap01 D) ↔
    (D.radius / 4 ≤ z.val.1 ∧ z.val.1 ≤ D.radius ∧ z.val.2 = D.radius) ∨
    (D.radius / 4 ≤ z.val.2 ∧ z.val.2 ≤ D.radius ∧ z.val.1 = D.radius) := by
  have hs (p q : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
      z ∈ Set.range (crossingSquareSegment D.radius p q) ↔
      (z : ℝ×ℝ) ∈ segment ℝ (p : ℝ×ℝ) (q : ℝ×ℝ) := by
    rw [← Path.range_segment]
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t,rfl⟩
    · rintro ⟨t,ht⟩; exact ⟨t,Subtype.ext ht⟩
  have hh (x₁ x₂ y : ℝ) (h : x₁ ≤ x₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x₁,y) (x₂,y) ↔
      x₁ ≤ z.val.1 ∧ z.val.1 ≤ x₂ ∧ z.val.2 = y := by
    rw [← Prod.image_mk_segment_left, segment_eq_Icc h]
    constructor
    · rintro ⟨x,hx,hz⟩; rw [← hz]; exact ⟨hx.1,hx.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.1,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hv (x y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x,y₁) (x,y₂) ↔
      y₁ ≤ z.val.2 ∧ z.val.2 ≤ y₂ ∧ z.val.1 = x := by
    rw [← Prod.image_mk_segment_right, segment_eq_Icc h]
    constructor
    · rintro ⟨y,hy,hz⟩; rw [← hz]; exact ⟨hy.1,hy.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.2,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hg : D.square z ∈ Set.range (squareGap01 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 0 ⟨1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 0)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 0)
        (squarePort D.radius D.radius_pos 1 ⟨1,by norm_num⟩)) := by
    rw [← Path.trans_range]
    constructor
    · rintro ⟨t,ht⟩; exact ⟨t,D.square_embedded.injective ht⟩
    · rintro ⟨t,rfl⟩; exact ⟨t,rfl⟩
  rw [hg,Set.mem_union,hs,hs]
  dsimp [squarePort,crossingEndRectangle,crossingSquareCorner]
  simp only [mul_one,mul_zero,add_zero]
  rw [hh _ _ _ (by linarith [D.radius_pos]),segment_symm, hv _ _ _ (by linarith [D.radius_pos])]

theorem squareGap30_mem_iff_coordinates {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap30 D) ↔
    (D.radius / 4 ≤ z.val.2 ∧ z.val.2 ≤ D.radius ∧ z.val.1 = -D.radius) ∨
    (-D.radius ≤ z.val.1 ∧ z.val.1 ≤ -D.radius / 4 ∧ z.val.2 = D.radius) := by
  have hs (p q : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
      z ∈ Set.range (crossingSquareSegment D.radius p q) ↔
      (z : ℝ×ℝ) ∈ segment ℝ (p : ℝ×ℝ) (q : ℝ×ℝ) := by
    rw [← Path.range_segment]
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t,rfl⟩
    · rintro ⟨t,ht⟩; exact ⟨t,Subtype.ext ht⟩
  have hh (x₁ x₂ y : ℝ) (h : x₁ ≤ x₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x₁,y) (x₂,y) ↔
      x₁ ≤ z.val.1 ∧ z.val.1 ≤ x₂ ∧ z.val.2 = y := by
    rw [← Prod.image_mk_segment_left, segment_eq_Icc h]
    constructor
    · rintro ⟨x,hx,hz⟩; rw [← hz]; exact ⟨hx.1,hx.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.1,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hv (x y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x,y₁) (x,y₂) ↔
      y₁ ≤ z.val.2 ∧ z.val.2 ≤ y₂ ∧ z.val.1 = x := by
    rw [← Prod.image_mk_segment_right, segment_eq_Icc h]
    constructor
    · rintro ⟨y,hy,hz⟩; rw [← hz]; exact ⟨hy.1,hy.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.2,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hg : D.square z ∈ Set.range (squareGap30 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 3 ⟨1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 3)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 3)
        (squarePort D.radius D.radius_pos 0 ⟨-1,by norm_num⟩)) := by
    rw [← Path.trans_range]
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t, D.square_embedded.injective ht⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,rfl⟩
  rw [hg,Set.mem_union,hs,hs]
  dsimp [squarePort,crossingEndRectangle,crossingSquareCorner]
  simp only [mul_one,mul_zero,add_zero,mul_neg_one,neg_div]
  rw [hv _ _ _ (by linarith [D.radius_pos]), hh _ _ _ (by linarith [D.radius_pos])]

theorem squareGap23_mem_iff_coordinates {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap23 D) ↔
    (-D.radius ≤ z.val.1 ∧ z.val.1 ≤ -D.radius / 4 ∧ z.val.2 = -D.radius) ∨
    (-D.radius ≤ z.val.2 ∧ z.val.2 ≤ -D.radius / 4 ∧ z.val.1 = -D.radius) := by
  have hs (p q : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
      z ∈ Set.range (crossingSquareSegment D.radius p q) ↔
      (z : ℝ×ℝ) ∈ segment ℝ (p : ℝ×ℝ) (q : ℝ×ℝ) := by
    rw [← Path.range_segment]
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t,rfl⟩
    · rintro ⟨t,ht⟩; exact ⟨t,Subtype.ext ht⟩
  have hh (x₁ x₂ y : ℝ) (h : x₁ ≤ x₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x₁,y) (x₂,y) ↔
      x₁ ≤ z.val.1 ∧ z.val.1 ≤ x₂ ∧ z.val.2 = y := by
    rw [← Prod.image_mk_segment_left, segment_eq_Icc h]
    constructor
    · rintro ⟨x,hx,hz⟩; rw [← hz]; exact ⟨hx.1,hx.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.1,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hv (x y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x,y₁) (x,y₂) ↔
      y₁ ≤ z.val.2 ∧ z.val.2 ≤ y₂ ∧ z.val.1 = x := by
    rw [← Prod.image_mk_segment_right, segment_eq_Icc h]
    constructor
    · rintro ⟨y,hy,hz⟩; rw [← hz]; exact ⟨hy.1,hy.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.2,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hg : D.square z ∈ Set.range (squareGap23 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 2 ⟨-1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 2)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 2)
        (squarePort D.radius D.radius_pos 3 ⟨-1,by norm_num⟩)) := by
    rw [← Path.trans_range]
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t, D.square_embedded.injective ht⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,rfl⟩
  rw [hg,Set.mem_union,hs,hs]
  dsimp [squarePort,crossingEndRectangle,crossingSquareCorner]
  simp only [mul_one,mul_zero,add_zero,mul_neg_one,neg_div]
  conv_lhs => arg 1; rw [segment_symm]
  rw [hh _ _ _ (by linarith [D.radius_pos]),hv _ _ _ (by linarith [D.radius_pos])]

theorem squareGap12_mem_iff_coordinates {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap12 D) ↔
    (-D.radius ≤ z.val.2 ∧ z.val.2 ≤ -D.radius / 4 ∧ z.val.1 = D.radius) ∨
    (D.radius / 4 ≤ z.val.1 ∧ z.val.1 ≤ D.radius ∧ z.val.2 = -D.radius) := by
  have hs (p q : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
      z ∈ Set.range (crossingSquareSegment D.radius p q) ↔
      (z : ℝ×ℝ) ∈ segment ℝ (p : ℝ×ℝ) (q : ℝ×ℝ) := by
    rw [← Path.range_segment]
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨t,rfl⟩
    · rintro ⟨t,ht⟩; exact ⟨t,Subtype.ext ht⟩
  have hh (x₁ x₂ y : ℝ) (h : x₁ ≤ x₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x₁,y) (x₂,y) ↔
      x₁ ≤ z.val.1 ∧ z.val.1 ≤ x₂ ∧ z.val.2 = y := by
    rw [← Prod.image_mk_segment_left, segment_eq_Icc h]
    constructor
    · rintro ⟨x,hx,hz⟩; rw [← hz]; exact ⟨hx.1,hx.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.1,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hv (x y₁ y₂ : ℝ) (h : y₁ ≤ y₂) :
      (z : ℝ×ℝ) ∈ segment ℝ (x,y₁) (x,y₂) ↔
      y₁ ≤ z.val.2 ∧ z.val.2 ≤ y₂ ∧ z.val.1 = x := by
    rw [← Prod.image_mk_segment_right, segment_eq_Icc h]
    constructor
    · rintro ⟨y,hy,hz⟩; rw [← hz]; exact ⟨hy.1,hy.2,rfl⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨z.val.2,⟨h1,h2⟩,by ext <;> simp [h3]⟩
  have hg : D.square z ∈ Set.range (squareGap12 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 1 ⟨-1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 1)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 1)
        (squarePort D.radius D.radius_pos 2 ⟨1,by norm_num⟩)) := by
    rw [← Path.trans_range]
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨t, D.square_embedded.injective ht⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,rfl⟩
  rw [hg,Set.mem_union,hs,hs]
  dsimp [squarePort,crossingEndRectangle,crossingSquareCorner]
  simp only [mul_one,mul_zero,add_zero,mul_neg_one,neg_div]
  conv_lhs => arg 1; rw [segment_symm]
  conv_lhs => arg 2; rw [segment_symm]
  rw [hv _ _ _ (by linarith [D.radius_pos]),hh _ _ _ (by linarith [D.radius_pos])]

theorem squareGap01_mem_iff_segment_ranges {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap01 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 0 ⟨1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 0)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 0)
        (squarePort D.radius D.radius_pos 1 ⟨1,by norm_num⟩)) := by
  rw [← Path.trans_range]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t, D.square_embedded.injective ht⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

theorem squareGap30_mem_iff_segment_ranges {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap30 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 3 ⟨1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 3)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 3)
        (squarePort D.radius D.radius_pos 0 ⟨-1,by norm_num⟩)) := by
  rw [← Path.trans_range]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t, D.square_embedded.injective ht⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

theorem squareGap23_mem_iff_segment_ranges {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap23 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 2 ⟨-1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 2)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 2)
        (squarePort D.radius D.radius_pos 3 ⟨-1,by norm_num⟩)) := by
  rw [← Path.trans_range]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t, D.square_embedded.injective ht⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

theorem squareGap12_mem_iff_segment_ranges {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
    D.square z ∈ Set.range (squareGap12 D) ↔
    z ∈ Set.range (crossingSquareSegment D.radius
      (squarePort D.radius D.radius_pos 1 ⟨-1,by norm_num⟩)
      (crossingSquareCorner D.radius D.radius_pos 1)) ∪
      Set.range (crossingSquareSegment D.radius
        (crossingSquareCorner D.radius D.radius_pos 1)
        (squarePort D.radius D.radius_pos 2 ⟨1,by norm_num⟩)) := by
  rw [← Path.trans_range]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t, D.square_embedded.injective ht⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

theorem exists_frontier_circle_of_compatibleOutsideBands
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    IsCompact N ∧ IsConnected N ∧ a.image ∪ b.image ⊆ interior N ∧
      ∃ c : Curve S, frontier N = c.image := by
  have hcoverage : frontier (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) =
      Set.range (compatibleBoundaryLoop D B) := by
    have hr := D.radius_pos
    have hport0 (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
        z ∈ Set.range (squarePort D.radius D.radius_pos 0) ↔
          -(D.radius/4) ≤ z.val.1 ∧ z.val.1 ≤ D.radius/4 ∧ z.val.2 = D.radius := by
      constructor
      · rintro ⟨u,rfl⟩
        dsimp [squarePort,crossingEndRectangle]
        have hu := u.property
        constructor
        · nlinarith [hu.1]
        constructor
        · nlinarith [hu.2]
        · ring
      · rintro ⟨hx0,hx1,hy⟩
        have hr4 : 0 < D.radius/4 := by positivity
        let u : BandWidth := ⟨z.val.1 / (D.radius/4), by
          constructor
          · apply (le_div_iff₀ hr4).2
            nlinarith
          · apply (div_le_iff₀ hr4).2
            nlinarith⟩
        refine ⟨u,Subtype.ext ?_⟩
        change (D.radius/4*(z.val.1/(D.radius/4)),D.radius+D.radius/4*0) = z.val
        ext
        · exact mul_div_cancel₀ _ (ne_of_gt hr4)
        · simpa using hy.symm
    
    have hport1 (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
        z ∈ Set.range (squarePort D.radius D.radius_pos 1) ↔
          -(D.radius/4) ≤ z.val.2 ∧ z.val.2 ≤ D.radius/4 ∧ z.val.1 = D.radius := by
      constructor
      · rintro ⟨u,rfl⟩
        dsimp [squarePort,crossingEndRectangle]
        have hu := u.property
        constructor
        · nlinarith [hu.1]
        constructor
        · nlinarith [hu.2]
        · ring
      · rintro ⟨hx0,hx1,hy⟩
        have hr4 : 0 < D.radius/4 := by positivity
        let u : BandWidth := ⟨z.val.2 / (D.radius/4), by
          constructor
          · apply (le_div_iff₀ hr4).2
            nlinarith
          · apply (div_le_iff₀ hr4).2
            nlinarith⟩
        refine ⟨u,Subtype.ext ?_⟩
        change (D.radius+D.radius/4*0,D.radius/4*(z.val.2/(D.radius/4))) = z.val
        ext
        · simpa using hy.symm
        · exact mul_div_cancel₀ _ (ne_of_gt hr4)
    
    have hport2 (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
        z ∈ Set.range (squarePort D.radius D.radius_pos 2) ↔
          -(D.radius/4) ≤ z.val.1 ∧ z.val.1 ≤ D.radius/4 ∧ z.val.2 = -D.radius := by
      constructor
      · rintro ⟨u,rfl⟩
        dsimp [squarePort,crossingEndRectangle]
        have hu := u.property
        constructor
        · nlinarith [hu.1]
        constructor
        · nlinarith [hu.2]
        · ring
      · rintro ⟨hx0,hx1,hy⟩
        have hr4 : 0 < D.radius/4 := by positivity
        let u : BandWidth := ⟨z.val.1 / (D.radius/4), by
          constructor
          · apply (le_div_iff₀ hr4).2
            nlinarith
          · apply (div_le_iff₀ hr4).2
            nlinarith⟩
        refine ⟨u,Subtype.ext ?_⟩
        change (D.radius/4*(z.val.1/(D.radius/4)),-(D.radius+D.radius/4*0)) = z.val
        ext
        · exact mul_div_cancel₀ _ (ne_of_gt hr4)
        · simpa using hy.symm
    
    have hport3 (z : Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :
        z ∈ Set.range (squarePort D.radius D.radius_pos 3) ↔
          -(D.radius/4) ≤ z.val.2 ∧ z.val.2 ≤ D.radius/4 ∧ z.val.1 = -D.radius := by
      constructor
      · rintro ⟨u,rfl⟩
        dsimp [squarePort,crossingEndRectangle]
        have hu := u.property
        constructor
        · nlinarith [hu.1]
        constructor
        · nlinarith [hu.2]
        · ring
      · rintro ⟨hx0,hx1,hy⟩
        have hr4 : 0 < D.radius/4 := by positivity
        let u : BandWidth := ⟨z.val.2 / (D.radius/4), by
          constructor
          · apply (le_div_iff₀ hr4).2
            nlinarith
          · apply (div_le_iff₀ hr4).2
            nlinarith⟩
        refine ⟨u,Subtype.ext ?_⟩
        change (-(D.radius+D.radius/4*0),D.radius/4*(z.val.2/(D.radius/4))) = z.val
        ext
        · simpa using hy.symm
        · exact mul_div_cancel₀ _ (ne_of_gt hr4)
    rw [compatibleOutsideBands_frontier_eq_exposed_square_union_laterals,compatibleBoundaryLoop_range]
    apply Set.Subset.antisymm
    · rintro x ((⟨z,rfl,hz,hb1,hb2⟩ | hx) | hx)
      · have hn0 : z ∉ Set.range (squarePort D.radius D.radius_pos 0) := by
          rintro ⟨u,hu⟩
          apply hb1
          exact ⟨(1,u),by rw [B.first_top,hu]⟩
        have hn2 : z ∉ Set.range (squarePort D.radius D.radius_pos 2) := by
          rintro ⟨u,hu⟩
          apply hb1
          exact ⟨(0,u),by rw [B.first_bottom,hu]⟩
        have hn1 : z ∉ Set.range (squarePort D.radius D.radius_pos 1) := by
          rintro ⟨u,hu⟩
          apply hb2
          exact ⟨(1,u),by rw [B.second_right,hu]⟩
        have hn3 : z ∉ Set.range (squarePort D.radius D.radius_pos 3) := by
          rintro ⟨u,hu⟩
          apply hb2
          exact ⟨(0,u),by rw [B.second_left,hu]⟩
        have hb := z.property
        simp only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs,max_le_iff,abs_le] at hb
        rw [frontier_closedBall _ (ne_of_gt D.radius_pos)] at hz
        simp only [Metric.mem_sphere,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs] at hz
        have hside : z.val.1 = D.radius ∨ z.val.1 = -D.radius ∨ z.val.2 = D.radius ∨ z.val.2 = -D.radius := by
          rcases max_eq_iff.mp hz with h | h
          · rcases (abs_eq D.radius_pos.le).mp h.1 with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          · rcases (abs_eq D.radius_pos.le).mp h.1 with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
        apply Or.inl
        apply Or.inl
        simp only [Set.mem_union,squareGap01_mem_iff_coordinates,squareGap30_mem_iff_coordinates,squareGap23_mem_iff_coordinates,squareGap12_mem_iff_coordinates]
        rcases hside with hs | hs | hs | hs
        · have ht : D.radius/4 ≤ z.val.2 ∨ z.val.2 ≤ -D.radius/4 := by
            by_contra ht
            push_neg at ht
            apply hn1
            rw [hport1]
            exact ⟨by linarith,by linarith,hs⟩
          rcases ht with ht | ht
          · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ht,hb.2.2,hs⟩)))
          · exact Or.inr (Or.inl ⟨hb.2.1,ht,hs⟩)
        · have ht : D.radius/4 ≤ z.val.2 ∨ z.val.2 ≤ -D.radius/4 := by
            by_contra ht
            push_neg at ht
            apply hn3
            rw [hport3]
            exact ⟨by linarith,by linarith,hs⟩
          rcases ht with ht | ht
          · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨ht,hb.2.2,hs⟩)))
          · exact Or.inl (Or.inr (Or.inr ⟨hb.2.1,ht,hs⟩))
        · have ht : D.radius/4 ≤ z.val.1 ∨ z.val.1 ≤ -D.radius/4 := by
            by_contra ht
            push_neg at ht
            apply hn0
            rw [hport0]
            exact ⟨by linarith,by linarith,hs⟩
          rcases ht with ht | ht
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨ht,hb.1.2,hs⟩)))
          · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨hb.1.1,ht,hs⟩)))
        · have ht : D.radius/4 ≤ z.val.1 ∨ z.val.1 ≤ -D.radius/4 := by
            by_contra ht
            push_neg at ht
            apply hn2
            rw [hport2]
            exact ⟨by linarith,by linarith,hs⟩
          rcases ht with ht | ht
          · exact Or.inr (Or.inr ⟨ht,hb.1.2,hs⟩)
          · exact Or.inl (Or.inr (Or.inl ⟨hb.1.1,ht,hs⟩))
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
    · rintro x (((((hx | hx) | hx) | hx) | hx) | hx)
      · have hsq : x ∈ Set.range D.square := by
          rcases hx with ⟨t,rfl⟩
          exact Set.mem_range_self _
        obtain ⟨z,rfl⟩ := hsq
        have hcoords := (squareGap01_mem_iff_coordinates D z).mp hx
        have hz : (z : ℝ×ℝ) ∈ frontier (Metric.closedBall ((0,0):ℝ×ℝ) D.radius) := by
          rw [frontier_closedBall _ (ne_of_gt hr)]
          simp only [Metric.mem_sphere,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs]
          have hb : max |z.val.1| |z.val.2| ≤ D.radius := by
            have hb := z.property
            simp only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs] at hb
            exact hb
          apply le_antisymm hb
          rcases hcoords with h | h
          all_goals
            have hh := h.2.2
            try simp only [Prod.fst_zero,Prod.snd_zero] at *
            first
            | have ha : |z.val.1| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_left _ _)
            | have ha : |z.val.2| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_right _ _)
        have hrest (i : Fin 4) (u : BandWidth)
            (hu : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap01 D)) :
            (u : ℝ) = -1 ∨ (u : ℝ) = 1 := by
          have hh := squareGap01_port_restriction D i u hu
          exact Or.inr hh.2
        by_cases hb1 : D.square z ∈ Set.range B.first
        · have hm : D.square z ∈ Set.range B.first ∩ Set.range D.square := ⟨hb1,Set.mem_range_self _⟩
          rw [B.first_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
        by_cases hb2 : D.square z ∈ Set.range B.second
        · have hm : D.square z ∈ Set.range B.second ∩ Set.range D.square := ⟨hb2,Set.mem_range_self _⟩
          rw [B.second_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
        exact Or.inl (Or.inl ⟨z,rfl,hz,hb1,hb2⟩)
      · have hsq : x ∈ Set.range D.square := by
          rcases hx with ⟨t,rfl⟩
          exact Set.mem_range_self _
        obtain ⟨z,rfl⟩ := hsq
        have hcoords := (squareGap30_mem_iff_coordinates D z).mp hx
        have hz : (z : ℝ×ℝ) ∈ frontier (Metric.closedBall ((0,0):ℝ×ℝ) D.radius) := by
          rw [frontier_closedBall _ (ne_of_gt hr)]
          simp only [Metric.mem_sphere,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs]
          have hb : max |z.val.1| |z.val.2| ≤ D.radius := by
            have hb := z.property
            simp only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs] at hb
            exact hb
          apply le_antisymm hb
          rcases hcoords with h | h
          all_goals
            have hh := h.2.2
            try simp only [Prod.fst_zero,Prod.snd_zero] at *
            first
            | have ha : |z.val.1| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_left _ _)
            | have ha : |z.val.2| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_right _ _)
        have hrest (i : Fin 4) (u : BandWidth)
            (hu : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap30 D)) :
            (u : ℝ) = -1 ∨ (u : ℝ) = 1 := by
          have hh := squareGap30_port_restriction D i u hu
          rcases hh with hh | hh
          · exact Or.inr hh.2
          · exact Or.inl hh.2
        by_cases hb1 : D.square z ∈ Set.range B.first
        · have hm : D.square z ∈ Set.range B.first ∩ Set.range D.square := ⟨hb1,Set.mem_range_self _⟩
          rw [B.first_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
        by_cases hb2 : D.square z ∈ Set.range B.second
        · have hm : D.square z ∈ Set.range B.second ∩ Set.range D.square := ⟨hb2,Set.mem_range_self _⟩
          rw [B.second_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
        exact Or.inl (Or.inl ⟨z,rfl,hz,hb1,hb2⟩)
      · have hsq : x ∈ Set.range D.square := by
          rcases hx with ⟨t,rfl⟩
          exact Set.mem_range_self _
        obtain ⟨z,rfl⟩ := hsq
        have hcoords := (squareGap23_mem_iff_coordinates D z).mp hx
        have hz : (z : ℝ×ℝ) ∈ frontier (Metric.closedBall ((0,0):ℝ×ℝ) D.radius) := by
          rw [frontier_closedBall _ (ne_of_gt hr)]
          simp only [Metric.mem_sphere,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs]
          have hb : max |z.val.1| |z.val.2| ≤ D.radius := by
            have hb := z.property
            simp only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs] at hb
            exact hb
          apply le_antisymm hb
          rcases hcoords with h | h
          all_goals
            have hh := h.2.2
            try simp only [Prod.fst_zero,Prod.snd_zero] at *
            first
            | have ha : |z.val.1| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_left _ _)
            | have ha : |z.val.2| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_right _ _)
        have hrest (i : Fin 4) (u : BandWidth)
            (hu : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap23 D)) :
            (u : ℝ) = -1 ∨ (u : ℝ) = 1 := by
          have hh := squareGap23_port_restriction D i u hu
          rcases hh with hh | hh
          · exact Or.inl hh.2
          · exact Or.inl hh.2
        by_cases hb1 : D.square z ∈ Set.range B.first
        · have hm : D.square z ∈ Set.range B.first ∩ Set.range D.square := ⟨hb1,Set.mem_range_self _⟩
          rw [B.first_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
        by_cases hb2 : D.square z ∈ Set.range B.second
        · have hm : D.square z ∈ Set.range B.second ∩ Set.range D.square := ⟨hb2,Set.mem_range_self _⟩
          rw [B.second_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
        exact Or.inl (Or.inl ⟨z,rfl,hz,hb1,hb2⟩)
      · have hsq : x ∈ Set.range D.square := by
          rcases hx with ⟨t,rfl⟩
          exact Set.mem_range_self _
        obtain ⟨z,rfl⟩ := hsq
        have hcoords := (squareGap12_mem_iff_coordinates D z).mp hx
        have hz : (z : ℝ×ℝ) ∈ frontier (Metric.closedBall ((0,0):ℝ×ℝ) D.radius) := by
          rw [frontier_closedBall _ (ne_of_gt hr)]
          simp only [Metric.mem_sphere,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs]
          have hb : max |z.val.1| |z.val.2| ≤ D.radius := by
            have hb := z.property
            simp only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_zero,Real.norm_eq_abs] at hb
            exact hb
          apply le_antisymm hb
          rcases hcoords with h | h
          all_goals
            have hh := h.2.2
            try simp only [Prod.fst_zero,Prod.snd_zero] at *
            first
            | have ha : |z.val.1| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_left _ _)
            | have ha : |z.val.2| = D.radius := by rw [hh]; simp [abs_of_pos hr]
              exact ha.symm.trans_le (le_max_right _ _)
        have hrest (i : Fin 4) (u : BandWidth)
            (hu : D.square (squarePort D.radius D.radius_pos i u) ∈ Set.range (squareGap12 D)) :
            (u : ℝ) = -1 ∨ (u : ℝ) = 1 := by
          have hh := squareGap12_port_restriction D i u hu
          rcases hh with hh | hh
          · exact Or.inl hh.2
          · exact Or.inr hh.2
        by_cases hb1 : D.square z ∈ Set.range B.first
        · have hm : D.square z ∈ Set.range B.first ∩ Set.range D.square := ⟨hb1,Set.mem_range_self _⟩
          rw [B.first_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_bottom,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inl ∘ Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.first_top,← hue]
              exact hu
        by_cases hb2 : D.square z ∈ Set.range B.second
        · have hm : D.square z ∈ Set.range B.second ∩ Set.range D.square := ⟨hb2,Set.mem_range_self _⟩
          rw [B.second_square] at hm
          rcases hm with ⟨u,hu⟩ | ⟨u,hu⟩
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨0,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
            · apply Or.inr
              refine ⟨0,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_left,← hue]
              exact hu
          · have hup := hrest _ u (by simpa only [← hu] using hx)
            apply Or.inr
            rcases hup with hup | hup
            · apply Or.inl
              refine ⟨1,?_⟩
              have hue : u = ⟨-1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
            · apply Or.inr
              refine ⟨1,?_⟩
              have hue : u = ⟨1,by norm_num⟩ := Subtype.ext hup
              dsimp only at hu ⊢
              rw [B.second_right,← hue]
              exact hu
        exact Or.inl (Or.inl ⟨z,rfl,hz,hb1,hb2⟩)
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  have hcircle : ∃ r : C(Circle,S), IsEmbedding r ∧ Set.range r = Set.range (compatibleBoundaryLoop D B) := by
    let p0 := squareGap01 D
    let p1 := boundarySecondPlusReverse D B
    let p2 := squareGap30 D
    let p3 := boundaryFirstMinusReverse D B
    let p4 := squareGap23 D
    let p5 := boundarySecondMinus D B
    let p6 := squareGap12 D
    let p7 := boundaryFirstPlus D B
    let Q := Set.range D.square
    have hs0 : Set.range p0 ⊆ Q := by
      rintro x ⟨t,rfl⟩; exact Set.mem_range_self _
    have hs2 : Set.range p2 ⊆ Q := by
      rintro x ⟨t,rfl⟩; exact Set.mem_range_self _
    have hs4 : Set.range p4 ⊆ Q := by
      rintro x ⟨t,rfl⟩; exact Set.mem_range_self _
    have hs6 : Set.range p6 ⊆ Q := by
      rintro x ⟨t,rfl⟩; exact Set.mem_range_self _
    have hc1 : Set.range p1 ∩ Q = {p1 0,p1 1} := by
      dsimp [p1,Q]
      rw [boundarySecondPlusReverse_range,compatibleOutsideBands_second_side_square]
      simp [boundarySecondPlusReverse,B.second_left,B.second_right,Set.pair_comm]
    have hc3 : Set.range p3 ∩ Q = {p3 0,p3 1} := by
      dsimp [p3,Q]
      rw [boundaryFirstMinusReverse_range,compatibleOutsideBands_first_side_square]
      simp [boundaryFirstMinusReverse,B.first_bottom,B.first_top,Set.pair_comm]
    have hc5 : Set.range p5 ∩ Q = {p5 0,p5 1} := by
      dsimp [p5,Q]
      rw [boundarySecondMinus_range,compatibleOutsideBands_second_side_square]
      simp [boundarySecondMinus,B.second_left,B.second_right]
    have hc7 : Set.range p7 ∩ Q = {p7 0,p7 1} := by
      dsimp [p7,Q]
      rw [boundaryFirstPlus_range,compatibleOutsideBands_first_side_square]
      simp [boundaryFirstPlus,B.first_bottom,B.first_top]
    have hd02 : Disjoint (Set.range p0) (Set.range p2) := squareGap01_disjoint_squareGap30 D
    have hd04 : Disjoint (Set.range p0) (Set.range p4) := squareGap01_disjoint_squareGap23 D
    have hd06 : Disjoint (Set.range p0) (Set.range p6) := squareGap01_disjoint_squareGap12 D
    have hd24 : Disjoint (Set.range p2) (Set.range p4) := squareGap30_disjoint_squareGap23 D
    have hd26 : Disjoint (Set.range p2) (Set.range p6) := squareGap30_disjoint_squareGap12 D
    have hd46 : Disjoint (Set.range p4) (Set.range p6) := squareGap23_disjoint_squareGap12 D
    have hd13 : Disjoint (Set.range p1) (Set.range p3) := by
      apply Set.disjoint_of_subset (s₂ := bandLateralSides B.second) (t₂ := bandLateralSides B.first)
      · rw [show Set.range p1 = _ from boundarySecondPlusReverse_range D B]
        exact Set.subset_union_right
      · rw [show Set.range p3 = _ from boundaryFirstMinusReverse_range D B]
        exact Set.subset_union_left
      · exact (compatibleOutsideBands_laterals_disjoint D B).symm
    have hd15 : Disjoint (Set.range p1) (Set.range p5) := by
      dsimp [p1,p5]
      rw [boundarySecondPlusReverse_range,boundarySecondMinus_range]
      exact (band_lateral_sides_disjoint B.second B.second_embedded).symm
    have hd17 : Disjoint (Set.range p1) (Set.range p7) := by
      dsimp [p1,p7]
      rw [boundarySecondPlusReverse_range,boundaryFirstPlus_range]
      exact Set.disjoint_of_subset (s₂ := Set.range B.second) (t₂ := Set.range B.first) (fun _ ⟨t,ht⟩ => ⟨(t,_),ht⟩)
        (fun _ ⟨t,ht⟩ => ⟨(t,_),ht⟩) B.bands_disjoint.symm
    have hd35 : Disjoint (Set.range p3) (Set.range p5) := by
      dsimp [p3,p5]
      rw [boundaryFirstMinusReverse_range,boundarySecondMinus_range]
      exact Set.disjoint_of_subset (s₂ := Set.range B.first) (t₂ := Set.range B.second) (fun _ ⟨t,ht⟩ => ⟨(t,_),ht⟩)
        (fun _ ⟨t,ht⟩ => ⟨(t,_),ht⟩) B.bands_disjoint
    have hd37 : Disjoint (Set.range p3) (Set.range p7) := by
      dsimp [p3,p7]
      rw [boundaryFirstMinusReverse_range,boundaryFirstPlus_range]
      exact band_lateral_sides_disjoint B.first B.first_embedded
    have hd57 : Disjoint (Set.range p5) (Set.range p7) := by
      dsimp [p5,p7]
      rw [boundarySecondMinus_range,boundaryFirstPlus_range]
      exact Set.disjoint_of_subset (s₂ := Set.range B.second) (t₂ := Set.range B.first) (fun _ ⟨t,ht⟩ => ⟨(t,_),ht⟩)
        (fun _ ⟨t,ht⟩ => ⟨(t,_),ht⟩) B.bands_disjoint.symm
    have hi01 : Set.range p0 ∩ Set.range p1 = {p1 0} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p1 0,p1 1} : Set S) := by
          rw [← hc1]
          exact ⟨hzb,hs0 hzg⟩
        rcases hm with hz | hz
        · exact hz
        · exfalso
          apply Set.disjoint_left.mp hd02 hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · rintro z rfl
        exact ⟨⟨1,by simp⟩,⟨0,rfl⟩⟩
    have hi03 : Set.range p0 ∩ Set.range p3 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p3 0,p3 1} : Set S) := by
          rw [← hc3]
          exact ⟨hzb,hs0 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd02 hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd04 hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi05 : Set.range p0 ∩ Set.range p5 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p5 0,p5 1} : Set S) := by
          rw [← hc5]
          exact ⟨hzb,hs0 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd04 hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd06 hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi07 : Set.range p0 ∩ Set.range p7 = {p7 1} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p7 0,p7 1} : Set S) := by
          rw [← hc7]
          exact ⟨hzb,hs0 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd06 hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exact hz
      · rintro z rfl
        exact ⟨⟨0,by simp⟩,⟨1,rfl⟩⟩
    have hi21 : Set.range p2 ∩ Set.range p1 = {p1 1} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p1 0,p1 1} : Set S) := by
          rw [← hc1]
          exact ⟨hzb,hs2 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd02.symm hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exact hz
      · rintro z rfl
        exact ⟨⟨0,by simp⟩,⟨1,rfl⟩⟩
    have hi23 : Set.range p2 ∩ Set.range p3 = {p3 0} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p3 0,p3 1} : Set S) := by
          rw [← hc3]
          exact ⟨hzb,hs2 hzg⟩
        rcases hm with hz | hz
        · exact hz
        · exfalso
          apply Set.disjoint_left.mp hd24 hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · rintro z rfl
        exact ⟨⟨1,by simp⟩,⟨0,rfl⟩⟩
    have hi25 : Set.range p2 ∩ Set.range p5 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p5 0,p5 1} : Set S) := by
          rw [← hc5]
          exact ⟨hzb,hs2 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd24 hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd26 hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi27 : Set.range p2 ∩ Set.range p7 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p7 0,p7 1} : Set S) := by
          rw [← hc7]
          exact ⟨hzb,hs2 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd26 hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd02.symm hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi41 : Set.range p4 ∩ Set.range p1 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p1 0,p1 1} : Set S) := by
          rw [← hc1]
          exact ⟨hzb,hs4 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd04.symm hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd24.symm hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi43 : Set.range p4 ∩ Set.range p3 = {p3 1} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p3 0,p3 1} : Set S) := by
          rw [← hc3]
          exact ⟨hzb,hs4 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd24.symm hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exact hz
      · rintro z rfl
        exact ⟨⟨0,by simp⟩,⟨1,rfl⟩⟩
    have hi45 : Set.range p4 ∩ Set.range p5 = {p5 0} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p5 0,p5 1} : Set S) := by
          rw [← hc5]
          exact ⟨hzb,hs4 hzg⟩
        rcases hm with hz | hz
        · exact hz
        · exfalso
          apply Set.disjoint_left.mp hd46 hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · rintro z rfl
        exact ⟨⟨1,by simp⟩,⟨0,rfl⟩⟩
    have hi47 : Set.range p4 ∩ Set.range p7 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p7 0,p7 1} : Set S) := by
          rw [← hc7]
          exact ⟨hzb,hs4 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd46 hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd04.symm hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi61 : Set.range p6 ∩ Set.range p1 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p1 0,p1 1} : Set S) := by
          rw [← hc1]
          exact ⟨hzb,hs6 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd06.symm hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd26.symm hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi63 : Set.range p6 ∩ Set.range p3 = ∅ := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p3 0,p3 1} : Set S) := by
          rw [← hc3]
          exact ⟨hzb,hs6 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd26.symm hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exfalso
          apply Set.disjoint_left.mp hd46.symm hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · exact Set.empty_subset _
    have hi65 : Set.range p6 ∩ Set.range p5 = {p5 1} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p5 0,p5 1} : Set S) := by
          rw [← hc5]
          exact ⟨hzb,hs6 hzg⟩
        rcases hm with hz | hz
        · exfalso
          apply Set.disjoint_left.mp hd46.symm hzg
          rw [hz]
          exact ⟨1,by simp⟩
        · exact hz
      · rintro z rfl
        exact ⟨⟨0,by simp⟩,⟨1,rfl⟩⟩
    have hi67 : Set.range p6 ∩ Set.range p7 = {p7 0} := by
      apply Set.Subset.antisymm
      · rintro z ⟨hzg,hzb⟩
        have hm : z ∈ ({p7 0,p7 1} : Set S) := by
          rw [← hc7]
          exact ⟨hzb,hs6 hzg⟩
        rcases hm with hz | hz
        · exact hz
        · exfalso
          apply Set.disjoint_left.mp hd06.symm hzg
          rw [hz]
          exact ⟨0,by simp⟩
      · rintro z rfl
        exact ⟨⟨1,by simp⟩,⟨0,rfl⟩⟩
    have he02 : Set.range p0 ∩ Set.range p2 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd02
    have he04 : Set.range p0 ∩ Set.range p4 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd04
    have he06 : Set.range p0 ∩ Set.range p6 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd06
    have hi12 := (Set.inter_comm (Set.range p1) (Set.range p2)).trans hi21
    have he13 : Set.range p1 ∩ Set.range p3 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd13
    have hi14 := (Set.inter_comm (Set.range p1) (Set.range p4)).trans hi41
    have he15 : Set.range p1 ∩ Set.range p5 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd15
    have hi16 := (Set.inter_comm (Set.range p1) (Set.range p6)).trans hi61
    have he17 : Set.range p1 ∩ Set.range p7 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd17
    have he24 : Set.range p2 ∩ Set.range p4 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd24
    have he26 : Set.range p2 ∩ Set.range p6 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd26
    have hi34 := (Set.inter_comm (Set.range p3) (Set.range p4)).trans hi43
    have he35 : Set.range p3 ∩ Set.range p5 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd35
    have hi36 := (Set.inter_comm (Set.range p3) (Set.range p6)).trans hi63
    have he37 : Set.range p3 ∩ Set.range p7 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd37
    have he46 : Set.range p4 ∩ Set.range p6 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd46
    have hi56 := (Set.inter_comm (Set.range p5) (Set.range p6)).trans hi65
    have he57 : Set.range p5 ∩ Set.range p7 = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd57
    have hp0 : IsEmbedding p0 := squareGap01_embedded D
    have hp1 : IsEmbedding p1 := boundarySecondPlusReverse_embedded D B
    have hp2 : IsEmbedding p2 := squareGap30_embedded D
    have hp3 : IsEmbedding p3 := boundaryFirstMinusReverse_embedded D B
    have hp4 : IsEmbedding p4 := squareGap23_embedded D
    have hp5 : IsEmbedding p5 := boundarySecondMinus_embedded D B
    have hp6 : IsEmbedding p6 := squareGap12_embedded D
    have hp7 : IsEmbedding p7 := boundaryFirstPlus_embedded D B
    let q1 := p0.trans p1
    have hq1 : IsEmbedding q1 := isEmbedding_path_trans_of_inter_singleton_probe p0 p1 hp0 hp1 (by simpa using hi01)
    let q2 := q1.trans p2
    have hq2 : IsEmbedding q2 := by
      apply isEmbedding_path_trans_of_inter_singleton_probe _ _ hq1 hp2
      dsimp [q1]
      simp only [Path.trans_range, Set.union_inter_distrib_right, he02,hi12, Set.union_empty,Set.empty_union]
      simp
    let q3 := q2.trans p3
    have hq3 : IsEmbedding q3 := by
      apply isEmbedding_path_trans_of_inter_singleton_probe _ _ hq2 hp3
      dsimp [q2,q1]
      simp only [Path.trans_range, Set.union_inter_distrib_right, hi03,he13,hi23, Set.union_empty,Set.empty_union]
      simp
    let q4 := q3.trans p4
    have hq4 : IsEmbedding q4 := by
      apply isEmbedding_path_trans_of_inter_singleton_probe _ _ hq3 hp4
      dsimp [q3,q2,q1]
      simp only [Path.trans_range, Set.union_inter_distrib_right, he04,hi14,he24,hi34, Set.union_empty,Set.empty_union]
      simp
    let q5 := q4.trans p5
    have hq5 : IsEmbedding q5 := by
      apply isEmbedding_path_trans_of_inter_singleton_probe _ _ hq4 hp5
      dsimp [q4,q3,q2,q1]
      simp only [Path.trans_range, Set.union_inter_distrib_right, hi05,he15,hi25,he35,hi45, Set.union_empty,Set.empty_union]
      simp
    let q6 := q5.trans p6
    have hq6 : IsEmbedding q6 := by
      apply isEmbedding_path_trans_of_inter_singleton_probe _ _ hq5 hp6
      dsimp [q5,q4,q3,q2,q1]
      simp only [Path.trans_range, Set.union_inter_distrib_right, he06,hi16,he26,hi36,he46,hi56, Set.union_empty,Set.empty_union]
      simp
    obtain ⟨r,hr,hrange⟩ := exists_embedded_circle_of_two_paths_probe q6 p7 hq6 hp7 (by
      dsimp [q6,q5,q4,q3,q2,q1]
      simp only [Path.trans_range,Set.union_inter_distrib_right,hi07,he17,hi27,he37,hi47,he57,hi67,Set.union_empty,Set.empty_union]
      simp [Set.pair_comm])
    refine ⟨r,hr,?_⟩
    rw [hrange]
    exact (q6.trans_range p7).symm
  obtain ⟨r,hr,hrange⟩ := hcircle
  obtain ⟨hc,hconn,hcover⟩ := compatibleOutsideBands_compact_connected_neighborhood_probe D B
  exact ⟨hc,hconn,hcover,⟨⟨r,hr⟩,hcoverage.trans hrange.symm⟩⟩


end CurveComplex.FrontierHeaders

#print axioms CurveComplex.FrontierHeaders.exists_frontier_circle_of_compatibleOutsideBands
