import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Set Topology unitInterval
namespace CurveComplex

def flipBandWidth (flip : Bool) (t : BandWidth) : BandWidth :=
  if flip then ⟨-(t:ℝ),by constructor <;> linarith [t.property.1,t.property.2]⟩ else t

structure UnorientedOutsideBands {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) where
  firstFlip : Bool
  secondFlip : Bool
  first : I × BandWidth → S
  second : I × BandWidth → S
  first_embedded : IsEmbedding first
  second_embedded : IsEmbedding second
  first_center : ∀ t, first (t,⟨0,by norm_num⟩) = D.firstArc t
  second_center : ∀ t, second (t,⟨0,by norm_num⟩) = D.secondArc t
  first_bottom : ∀ t, first (0,t) = D.square (squarePort D.radius D.radius_pos 2 t)
  first_top : ∀ t, first (1,t) = D.square (squarePort D.radius D.radius_pos 0 (flipBandWidth firstFlip t))
  second_left : ∀ t, second (0,t) = D.square (squarePort D.radius D.radius_pos 3 t)
  second_right : ∀ t, second (1,t) = D.square (squarePort D.radius D.radius_pos 1 (flipBandWidth secondFlip t))
  bands_disjoint : Disjoint (Set.range first) (Set.range second)
  first_square : Set.range first ∩ Set.range D.square =
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 2 t)) ∪
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 0 t))
  second_square : Set.range second ∩ Set.range D.square =
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 3 t)) ∪
    Set.range (fun t => D.square (squarePort D.radius D.radius_pos 1 t))

end CurveComplex
