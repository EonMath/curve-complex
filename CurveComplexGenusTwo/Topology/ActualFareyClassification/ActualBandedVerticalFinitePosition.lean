import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOpenFinitePositionRetention
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBoundaryFixedMarkedBandedSourceLift
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualEssentialMarkedWindingFinitePosition
open Set Topology Schoenflies CurveComplex
/-- Produce vertical finite position by genuine moves confined to the actual
horizontal annulus with the marked point removed. The original parametrization,
all deck collisions and the SAME physical band are retained. -/
theorem actual_banded_source_has_marked_vertical_finite_position
    [ChartedSpace Plane (Circle×Circle)] [ClosedSurface (Circle×Circle)]
    (a b : EssentialCurve (Circle×Circle)) (F : C(ℝ,ℝ×ℝ))
    (d : ℝ) (p : ℝ×ℝ)
    (hproj : ∀ x, (Circle.exp (F x).1,Circle.exp (F x).2)=b.val.map (Circle.exp x))
    (hp : ∀ (k : ℤ) x, F (x+(k:ℝ)*(2*Real.pi))=
      ((F x).1+(k:ℝ)*(2*Real.pi),(F x).2))
    (hband : ∀ x, d < (F x).2 ∧ (F x).2 < d+2*Real.pi)
    (hAvoid : (Circle.exp p.1,Circle.exp p.2)∉b.val.image) :
    ∃ H : AmbientIsotopy (Circle×Circle), ∃ c : EssentialCurve (Circle×Circle),
    ∃ F' : C(ℝ,ℝ×ℝ),
      (∀ t, H.map (t,(Circle.exp p.1,Circle.exp p.2))=
        (Circle.exp p.1,Circle.exp p.2)) ∧
      (∀ (t : Interval) (z : Circle×Circle), z.2=Circle.exp d → H.map (t,z)=z) ∧
      (∀ z, c.val.map z=H.finalMap (b.val.map z)) ∧
      H.finalMap '' b.val.image=c.val.image ∧
      Transverse a.val c.val ∧
      (∀ x, (Circle.exp (F' x).1,Circle.exp (F' x).2)=c.val.map (Circle.exp x)) ∧
      (∀ (k : ℤ) x, F' (x+(k:ℝ)*(2*Real.pi))=
        ((F' x).1+(k:ℝ)*(2*Real.pi),(F' x).2)) ∧
      (∀ x, d < (F' x).2 ∧ (F' x).2 < d+2*Real.pi) ∧
      IsClosedEmbedding F' ∧
      (∀ (x y : ℝ) (i j : ℤ),
        F' x=((F' y).1+(i:ℝ)*(2*Real.pi),(F' y).2+(j:ℝ)*(2*Real.pi)) →
        ∃ k : ℤ, x=y+(k:ℝ)*(2*Real.pi) ∧ i=k ∧ j=0) ∧
      Disjoint (range F') (⋃ i : ℤ×ℤ,
        {(p.1+(i.1:ℝ)*(2*Real.pi),p.2+(i.2:ℝ)*(2*Real.pi))}) := by
  let W : Set (Circle×Circle) :=
    {z | z.2≠Circle.exp d} ∩ {(Circle.exp p.1,Circle.exp p.2)}ᶜ
  have hW : IsOpen W :=
    ((isClosed_singleton.preimage continuous_snd).isOpen_compl).inter
      isClosed_singleton.isOpen_compl
  have hbW : b.val.image ⊆ W := by
    rintro z ⟨w,rfl⟩
    obtain ⟨x,rfl⟩ := Circle.exp_surjective w
    constructor
    · change (b.val.map (Circle.exp x)).2≠Circle.exp d
      rw [← hproj]
      intro he
      obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp he
      have hl : (0:ℝ)<(k:ℝ) := by nlinarith [(hband x).1,Real.pi_pos]
      have hu : (k:ℝ)<1 := by nlinarith [(hband x).2,Real.pi_pos]
      have hlZ : (0:ℤ)<k := by exact_mod_cast hl
      have huZ : k<1 := by exact_mod_cast hu
      omega
    · intro he
      apply hAvoid
      exact he ▸ mem_range_self (Circle.exp x)
  obtain ⟨H,b',hfix,_,himage,_,_,htrans⟩ :=
    actual_open_finite_position_retains_source (Circle×Circle) a b W hW hbW
  have hmark : ∀ t, H.map (t,(Circle.exp p.1,Circle.exp p.2))=
      (Circle.exp p.1,Circle.exp p.2) := by
    intro t
    exact hfix t _ (fun h => h.2 rfl)
  have hboundary : ∀ (t : Interval) (z : Circle×Circle), z.2=Circle.exp d → H.map (t,z)=z := by
    intro t z hz
    exact hfix t z (fun h => h.1 hz)
  obtain ⟨c,F',hparam,hcimage,hFproj,hFperiod,hFband,hClosed,hCollision,hOrbit⟩ :=
    actual_boundary_fixed_marked_move_has_banded_source_lift H b F 1 0
      (Or.inl (by norm_num)) hproj (fun k x => by simpa using hp k x)
      d hband hboundary p hmark hAvoid
  have ht : Transverse a.val c.val :=
    actual_transverse_of_literal_equal_images a.val b'.val a.val c.val rfl
      (himage.trans hcimage) htrans
  refine ⟨H,c,F',hmark,hboundary,hparam,hcimage,ht,hFproj,?_,hFband,hClosed,?_,hOrbit⟩
  · intro k x
    simpa using hFperiod k x
  · intro x y i j hxy
    simpa using hCollision x y i j hxy
