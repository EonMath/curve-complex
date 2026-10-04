import CurveComplexGenusTwo.Topology.FrontierCircle.BandAttachments
import CurveComplexGenusTwo.Dictionary.Genus

open Set Topology unitInterval
namespace CurveComplex

abbrev BandWidth := Icc (-1:ℝ) 1

noncomputable def squarePort (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : BandWidth) :
    Metric.closedBall ((0,0):ℝ×ℝ) ε :=
  ⟨crossingEndRectangle ε i (t,⟨0,by norm_num⟩),
    (crossingEndRectangle_square_iff hε i _).mpr (by simp)⟩

/-- All data use this single square and these exact signed ports. -/
structure OneCrossingBandBase {S : Type} [TopologicalSpace S] (a b : Curve S) where
  radius : ℝ
  radius_pos : 0 < radius
  square : Metric.closedBall ((0,0):ℝ×ℝ) radius → S
  square_embedded : IsEmbedding square
  openSquare : Set S
  openSquare_open : IsOpen openSquare
  openSquare_eq : openSquare = square '' {z | z.val ∈ Metric.ball ((0,0):ℝ×ℝ) radius}
  firstArc : Path (square (squarePort radius radius_pos 2 ⟨0,by norm_num⟩))
    (square (squarePort radius radius_pos 0 ⟨0,by norm_num⟩))
  secondArc : Path (square (squarePort radius radius_pos 3 ⟨0,by norm_num⟩))
    (square (squarePort radius radius_pos 1 ⟨0,by norm_num⟩))
  firstArc_embedded : IsEmbedding firstArc
  secondArc_embedded : IsEmbedding secondArc
  firstArc_range : Set.range firstArc = a.image \ openSquare
  secondArc_range : Set.range secondArc = b.image \ openSquare
  arcs_disjoint : Disjoint (Set.range firstArc) (Set.range secondArc)
  first_axis : ∀ z, square z ∈ a.image ↔ z.val.1 = 0
  second_axis : ∀ z, square z ∈ b.image ↔ z.val.2 = 0
  ends : Fin 4 → EndRectangle → S
  ends_embedded : ∀ i, IsEmbedding (ends i)
  ends_disjoint : Pairwise (fun i j => Disjoint (Set.range (ends i)) (Set.range (ends j)))
  ends_square : ∀ i z, ends i z ∈ Set.range square ↔ (z.2:ℝ) ≤ 0
  ends_seam : ∀ i t, ends i (t,⟨0,by norm_num⟩) = square (squarePort radius radius_pos i t)
  ends_axes : ∀ i z,
    (ends i z ∈ a.image ↔ (i = 0 ∨ i = 2) ∧ (z.1:ℝ) = 0) ∧
    (ends i z ∈ b.image ↔ (i = 1 ∨ i = 3) ∧ (z.1:ℝ) = 0)

/-- The two bands have the SAME transverse sign at each end. That is the
untwistedness requirement to be derived from genus, not assumed of the surface. -/
structure CompatibleOutsideBands {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) where
  first : I × BandWidth → S
  second : I × BandWidth → S
  first_embedded : IsEmbedding first
  second_embedded : IsEmbedding second
  first_center : ∀ t, first (t,⟨0,by norm_num⟩) = D.firstArc t
  second_center : ∀ t, second (t,⟨0,by norm_num⟩) = D.secondArc t
  first_bottom : ∀ t, first (0,t) = D.square (squarePort D.radius D.radius_pos 2 t)
  first_top : ∀ t, first (1,t) = D.square (squarePort D.radius D.radius_pos 0 t)
  second_left : ∀ t, second (0,t) = D.square (squarePort D.radius D.radius_pos 3 t)
  second_right : ∀ t, second (1,t) = D.square (squarePort D.radius D.radius_pos 1 t)
  bands_disjoint : Disjoint (Set.range first) (Set.range second)
  first_square : Set.range first ∩ Set.range D.square =
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 2 t)) ∪
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 0 t))
  second_square : Set.range second ∩ Set.range D.square =
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 3 t)) ∪
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 1 t))


end CurveComplex
