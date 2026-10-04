import SectorCoordinates

open Set Topology CurveComplex
open LeanEval.Topology.ClassificationOfSurfaces

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry

/-- Radius and the unnormalized affine coordinate along the entire ordered link. -/
def OrderedBoundaryFan.sectorDomain {V : Type} [Fintype V] [DecidableEq V]
    {F : Finset (Finset V)} {v : V} (fan : OrderedBoundaryFan F v) (ε : ℝ) :
    Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ (fan.length : ℝ) * p.1 ∧ p.1 < ε}

/-- The same actual realization, restricted to the complete positive-center star. -/
def OrderedBoundaryFan.sectorTarget {V : Type} [Fintype V] [DecidableEq V]
    {F : Finset (Finset V)} {v : V} (_fan : OrderedBoundaryFan F v) (ε : ℝ) :
    Set (GeometricRealization V F) := {q | 1 - ε < q.val v}

/-- A chart of the WHOLE finite ordered fan with two specified extreme-triangle ports.
Neither the chart nor its inverse hides a successful-band selector. -/
structure OrderedBoundaryFan.WholeSector {V : Type} [Fintype V] [DecidableEq V]
    {F : Finset (Finset V)} {v : V} (fan : OrderedBoundaryFan F v)
    (ε : ℝ) (left right : Interval) where
  chart : ↥(fan.sectorDomain ε) ≃ₜ ↥(fan.sectorTarget ε)
  inverse_coordinates : ∀ q : ↥(fan.sectorTarget ε),
    (chart.symm q).val = (1 - q.val.val v, fan.linkMoment q.val)
  triangle_chart : ∀ (i : Fin fan.length) (r s : Interval)
    (hp : ((r : ℝ), (r : ℝ) * ((i.val : ℝ) + (s : ℝ))) ∈ fan.sectorDomain ε),
    (chart ⟨((r : ℝ), (r : ℝ) * ((i.val : ℝ) + (s : ℝ))), hp⟩).val =
      fan.trianglePoint i r s
  open_embedding : IsOpenEmbedding (fun p : ↥(fan.sectorDomain ε) => (chart p).val)
  boundary_exact : ∀ p : ↥(fan.sectorDomain ε),
    (chart p).val ∈ boundaryLocus F ↔
      p.val.2 = 0 ∨ p.val.2 = (fan.length : ℝ) * p.val.1
  left_port : ∀ (r : Interval)
    (hp : ((r : ℝ), (r : ℝ) * (left : ℝ)) ∈ fan.sectorDomain ε),
    (chart ⟨((r : ℝ), (r : ℝ) * (left : ℝ)), hp⟩).val =
      fan.trianglePoint ⟨0, by have := fan.positive; omega⟩ r left ∧
    (chart ⟨((r : ℝ), (r : ℝ) * (left : ℝ)), hp⟩).val.val ∈
      GeometricFace V {v, fan.vertex 0, fan.vertex ⟨1, by have := fan.positive; omega⟩} ∧
    ((chart ⟨((r : ℝ), (r : ℝ) * (left : ℝ)), hp⟩).val ∈ boundaryLocus F ↔ r = 0)
  right_port : ∀ (r : Interval)
    (hp : ((r : ℝ), (r : ℝ) * (((fan.length-1 : ℕ) : ℝ) + (right : ℝ))) ∈
      fan.sectorDomain ε),
    (chart ⟨((r : ℝ), (r : ℝ) * (((fan.length-1 : ℕ) : ℝ) + (right : ℝ))), hp⟩).val =
      fan.trianglePoint ⟨fan.length-1, by have := fan.positive; omega⟩ r right ∧
    (chart ⟨((r : ℝ), (r : ℝ) * (((fan.length-1 : ℕ) : ℝ) + (right : ℝ))), hp⟩).val.val ∈
      GeometricFace V {v, fan.vertex ⟨fan.length-1, by omega⟩,
        fan.vertex (Fin.last fan.length)} ∧
    ((chart ⟨((r : ℝ), (r : ℝ) * (((fan.length-1 : ℕ) : ℝ) + (right : ℝ))), hp⟩).val ∈
      boundaryLocus F ↔ r = 0)
  ports_collision : ∀ (r r' : Interval)
    (hp : ((r : ℝ), (r : ℝ) * (left : ℝ)) ∈ fan.sectorDomain ε)
    (hp' : ((r' : ℝ), (r' : ℝ) * (((fan.length-1 : ℕ) : ℝ) + (right : ℝ))) ∈
      fan.sectorDomain ε),
    (chart ⟨((r : ℝ), (r : ℝ) * (left : ℝ)), hp⟩).val =
      (chart ⟨((r' : ℝ), (r' : ℝ) * (((fan.length-1 : ℕ) : ℝ) + (right : ℝ))), hp'⟩).val ↔
      r = 0 ∧ r' = 0

/-- Whole-fan chart and both prescribed radial ports, including the apex and every
positive radius below the supplied width. A single-triangle fan is allowed. -/
theorem whole_ordered_boundary_fan_sector_two_ports
    (V : Type) [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (hfaces : ∀ t ∈ F, t.card = 3)
    (v : V) (fan : OrderedBoundaryFan F v)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε < (1 : ℝ)/2)
    (left right : Interval) (hleft : 0 < (left : ℝ)) (hleft_one : (left : ℝ) < 1)
    (hright : 0 < (right : ℝ)) (hright_one : (right : ℝ) < 1)
    (hports : (left : ℝ) < ((fan.length-1 : ℕ) : ℝ) + (right : ℝ)) :
    Nonempty (fan.WholeSector ε left right) := by
  classical
  have hcenter : ∀ q : ↥(fan.sectorTarget ε), 0 < q.val.val v := by
    intro q; have := q.property; dsimp [OrderedBoundaryFan.sectorTarget] at this; linarith
  have hcoords : ∀ q : ↥(fan.sectorTarget ε),
      (1 - q.val.val v, fan.linkMoment q.val) ∈ fan.sectorDomain ε := by
    intro q
    have hb := WholeFanProof.coordinate_bounds fan q.val (hcenter q)
    refine ⟨hb.1, hb.2.1, hb.2.2, ?_⟩
    have := q.property; dsimp [OrderedBoundaryFan.sectorTarget] at this; linarith
  let f : ↥(fan.sectorTarget ε) → ↥(fan.sectorDomain ε) :=
    fun q => ⟨(1 - q.val.val v, fan.linkMoment q.val), hcoords q⟩
  have hf : IsEmbedding f :=
    (WholeFanProof.coordinate_embedding fan ε hεsmall).codRestrict _ hcoords
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨q, he⟩ := WholeFanProof.coordinate_surjective fan p.val.1 p.val.2
      p.property.1 (by have := p.property.2.2.2; linarith) p.property.2.1 p.property.2.2.1
    have hq : q ∈ fan.sectorTarget ε := by
      have hc := congrArg Prod.fst he
      have := p.property.2.2.2
      change 1 - ε < q.val v
      dsimp at hc; linarith
    exact ⟨⟨q, hq⟩, Subtype.ext he⟩
  let e : ↥(fan.sectorTarget ε) ≃ₜ ↥(fan.sectorDomain ε) :=
    hf.toHomeomorphOfSurjective hsurj
  let chart : ↥(fan.sectorDomain ε) ≃ₜ ↥(fan.sectorTarget ε) := e.symm
  have hinverse : ∀ q : ↥(fan.sectorTarget ε),
      (chart.symm q).val = (1 - q.val.val v, fan.linkMoment q.val) := by
    intro q; rfl
  have htriangle : ∀ (i : Fin fan.length) (r s : Interval)
      (hp : ((r : ℝ), (r : ℝ) * ((i.val : ℝ) + (s : ℝ))) ∈ fan.sectorDomain ε),
      (chart ⟨((r : ℝ), (r : ℝ) * ((i.val : ℝ) + (s : ℝ))), hp⟩).val =
        fan.trianglePoint i r s := by
    intro i r s hp
    have hq : fan.trianglePoint i r s ∈ fan.sectorTarget ε := by
      change 1 - ε < (fan.trianglePoint i r s).val v
      rw [fan.trianglePoint_center]
      have := hp.2.2.2; linarith
    let q : ↥(fan.sectorTarget ε) := ⟨fan.trianglePoint i r s, hq⟩
    have heq : e q = ⟨((r : ℝ), (r : ℝ) * ((i.val : ℝ) + (s : ℝ))), hp⟩ := by
      apply Subtype.ext
      change (1 - (fan.trianglePoint i r s).val v,
        fan.linkMoment (fan.trianglePoint i r s)) = _
      rw [fan.trianglePoint_center, fan.trianglePoint_linkMoment, sub_sub_cancel]
    change (e.symm _).val = q.val
    rw [← heq, e.symm_apply_apply]
  have hboundary : ∀ p : ↥(fan.sectorDomain ε),
      (chart p).val ∈ boundaryLocus F ↔
        p.val.2 = 0 ∨ p.val.2 = (fan.length : ℝ) * p.val.1 := by
    intro p
    have he := hinverse (chart p)
    rw [chart.symm_apply_apply] at he
    have hc := congrArg Prod.fst he
    have hm := congrArg Prod.snd he
    dsimp at hc hm
    rw [WholeFanProof.coordinate_boundary fan (chart p).val (hcenter (chart p)), ← hm, ← hc]
  refine ⟨{
    chart := chart
    inverse_coordinates := hinverse
    triangle_chart := htriangle
    open_embedding := ?_
    boundary_exact := hboundary
    left_port := ?_
    right_port := ?_
    ports_collision := ?_
  }⟩
  · have hopen : IsOpen (fan.sectorTarget ε) :=
      isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)
    exact hopen.isOpenEmbedding_subtypeVal.comp chart.isOpenEmbedding
  · intro r hp
    let i : Fin fan.length := ⟨0, fan.positive⟩
    have heq : (chart ⟨((r : ℝ), (r : ℝ) * (left : ℝ)), hp⟩).val =
        fan.trianglePoint i r left := by
      simpa only [i, Fin.val_mk, Nat.cast_zero, zero_add] using
        htriangle i r left (by simpa [i] using hp)
    refine ⟨heq, ?_, ?_⟩
    · rw [heq]
      have hi0 : i.castSucc = 0 := by apply Fin.ext; rfl
      have hi1 : i.succ = ⟨1, by have := fan.positive; omega⟩ := by apply Fin.ext; rfl
      simpa only [hi0, hi1] using WholeFanProof.trianglePoint_face fan i r left
    · rw [hboundary]
      change ((r : ℝ) * (left : ℝ) = 0 ∨
        (r : ℝ) * (left : ℝ) = (fan.length : ℝ) * (r : ℝ)) ↔ r = 0
      have hn : (1 : ℝ) ≤ (fan.length : ℝ) := by exact_mod_cast fan.positive
      rw [WholeFanProof.interior_ray_boundary _ _ _ hleft (by linarith)]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · intro r hp
    let i : Fin fan.length := ⟨fan.length - 1, by have := fan.positive; omega⟩
    have heq := htriangle i r right hp
    have hi : i.succ = Fin.last fan.length := by
      apply Fin.ext; dsimp [i]; have := fan.positive; omega
    have hi' : i.castSucc = ⟨fan.length - 1, by omega⟩ := by apply Fin.ext; rfl
    refine ⟨heq, ?_, ?_⟩
    · rw [heq]
      simpa only [hi, hi'] using WholeFanProof.trianglePoint_face fan i r right
    · rw [hboundary]
      change ((r : ℝ) * (((fan.length - 1 : ℕ) : ℝ) + (right : ℝ)) = 0 ∨
        (r : ℝ) * (((fan.length - 1 : ℕ) : ℝ) + (right : ℝ)) =
          (fan.length : ℝ) * (r : ℝ)) ↔ r = 0
      have hn : ((fan.length - 1 : ℕ) : ℝ) + 1 = (fan.length : ℝ) := by
        have hn : fan.length - 1 + 1 = fan.length := by have := fan.positive; omega
        exact_mod_cast hn
      rw [WholeFanProof.interior_ray_boundary _ _ _ (by positivity) (by linarith)]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · intro r r' hp hp'
    have hc : (chart ⟨((r : ℝ), (r : ℝ) * (left : ℝ)), hp⟩).val =
        (chart ⟨((r' : ℝ), (r' : ℝ) * (((fan.length - 1 : ℕ) : ℝ) + (right : ℝ))), hp'⟩).val ↔
        ((r : ℝ), (r : ℝ) * (left : ℝ)) =
          ((r' : ℝ), (r' : ℝ) * (((fan.length - 1 : ℕ) : ℝ) + (right : ℝ))) := by
      constructor
      · intro h
        exact congrArg Subtype.val (chart.injective (Subtype.ext h))
      · intro h
        exact congrArg (fun p : ↥(fan.sectorDomain ε) => (chart p).val) (Subtype.ext h)
    rw [hc, WholeFanProof.distinct_ray_collision _ _ _ _ hports]
    exact ⟨fun h => ⟨Subtype.ext h.1, Subtype.ext h.2⟩,
      fun h => ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩⟩

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut.FiniteBoundaryGeometry
