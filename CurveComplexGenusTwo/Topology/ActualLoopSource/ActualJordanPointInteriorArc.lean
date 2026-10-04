import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPlaneArcIntervalProducer
import Schoenflies.GeneralCrosscut
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
/-- A literal point of an actual Jordan curve, away from two chosen cuts,
constructs an embedded ORIGINAL boundary arc with that point internal.
No local axis chart or arc around the point is supplied. -/
theorem actual_jordan_point_interior_arc
    {C : Set Plane} {p q m : Plane} (hC : IsJordanCurve C)
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p≠q)
    (hm : m ∈ C) (hmp : m≠p) (hmq : m≠q) :
    ∃ R T : Set Plane, IsCutPair C p q R T ∧
    ∃ f : C(unitInterval,Plane), IsEmbedding f ∧ range f=R ∧ f 0=p ∧ f 1=q ∧
    ∃ t : unitInterval, 0<t ∧ t<1 ∧ f t=m := by
  obtain ⟨A,B,hcut⟩ := exists_isCutPair hC hp hq hpq
  have hmAB : m ∈ A ∪ B := hcut.union_eq ▸ hm
  have chooseSide : ∃ R T, IsCutPair C p q R T ∧ m ∈ R := by
    rcases hmAB with hma | hmb
    · exact ⟨A,B,hcut,hma⟩
    · exact ⟨B,A,hcut.symm,hmb⟩
  obtain ⟨R,T,hRT,hmR⟩ := chooseSide
  obtain ⟨f,hf,hr,hf0,hf1⟩ := actual_plane_arc_interval_producer hRT.1
  obtain ⟨t,ht⟩ := hr.symm ▸ hmR
  have ht0 : t≠0 := by intro h; subst t; exact hmp (ht.symm.trans hf0)
  have ht1 : t≠1 := by intro h; subst t; exact hmq (ht.symm.trans hf1)
  exact ⟨R,T,hRT,f,hf,hr,hf0,hf1,t,
    lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1,ht⟩
end CurveComplex.HyperellipticModel
