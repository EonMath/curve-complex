import CurveComplexGenusTwo.Cover.ActualWholeBankSectorSide
import CurveComplexGenusTwo.Topology.TwoClosedSquaresActualSeamMerger
import Mathlib
open Set Metric Bornology
open scoped Topology
namespace AlternatingSphereCover
set_option maxHeartbeats 1600000
theorem actual_same_chart_eighteen_perimeter_intervals :
let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
    fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
      closedArcSector (0 : Fin 6) p ∧
      a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
  let Q0 := Quotient (Relation.EqvGen.setoid R0)
  let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
    ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
      a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
      b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
  let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
    (if sheet then Sum.inr v else Sum.inl v)
  let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
    (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
  ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
  ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
  ∃ M0 : Q0 ≃ₜ (unitInterval × unitInterval),
    (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
    (∀ v : StandardDisk, (H v).val=gaugeRescale
      (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
    (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).1.val=
        ((H v).val.1+1)/4 ∧
      (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
    (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).1.val=
        1-((H v).val.1+1)/4 ∧
      (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).2.val=((H v).val.2+1)/2) ∧
  ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
    (∀ v, (G v).val = gaugeRescale
      (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
      (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
  ∃ M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval),
    (∀ u, (M3 (Quotient.mk _ (Sum.inl u))).1.val=((G (M0 u)).val.1+1)/4 ∧
      (M3 (Quotient.mk _ (Sum.inl u))).2.val=((G (M0 u)).val.2+1)/2) ∧
    (∀ v, (M3 (Quotient.mk _ (Sum.inr v))).1.val=
        1-((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.1+1)/4 ∧
      (M3 (Quotient.mk _ (Sum.inr v))).2.val=
        ((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.2+1)/2) ∧
    (∀ i : Fin 6,
      H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
      {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
      | 0 => z.val.1=1
      | 1 => z.val.2=1 ∧ 0≤z.val.1
      | 2 => z.val.2=1 ∧ z.val.1≤0
      | 3 => z.val.1= -1
      | 4 => z.val.2= -1 ∧ z.val.1≤0
      | _ => z.val.2= -1 ∧ 0≤z.val.1}) ∧
    (∀ k : Fin 4, ∀ right : Bool,
      M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector (![(4 : Fin 6),5,4,5] k) p ∧
        q=qFace right (![false,false,true,true] k) (diskBoundaryPoint p hp)} =
      {z : unitInterval × unitInterval | z.1.val=(if right then 1 else 0) ∧
        (![(2/7 : ℝ),3/7,5/7,4/7] k)≤z.2.val ∧
        z.2.val≤(![(3/7 : ℝ),4/7,6/7,5/7] k)}) ∧
    M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
      closedArcSector (2 : Fin 6) p ∧ q=Quotient.mk (Relation.EqvGen.setoid R1)
        (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))))} =
    {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/3 : ℝ)≤z.1.val ∧ z.1.val≤1/2} ∧
    M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
      closedArcSector (2 : Fin 6) p ∧ q=qFace true false (diskBoundaryPoint p hp)} =
    {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/2 : ℝ)≤z.1.val ∧ z.1.val≤2/3} ∧
    (∀ k : Fin 2, ∀ right : Bool,
      M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector (![(1 : Fin 6),2] k) p ∧ q=qFace right true (diskBoundaryPoint p hp)} =
      {z : unitInterval × unitInterval | z.2.val=1 ∧
        (if right then 1-(![(1/2 : ℝ),1/3] k) else (![(1/3 : ℝ),3/10] k))≤z.1.val ∧
        z.1.val≤(if right then 1-(![(1/3 : ℝ),3/10] k) else (![(1/2 : ℝ),1/3] k))}) ∧
    (∀ right sheet : Bool,
      let width : ℝ := if sheet then 3/10 else 1/3
      let flat : ℝ := if sheet then 1 else 0
      let lower : ℝ := if sheet then 6/7 else 0
      let upper : ℝ := if sheet then 1 else 2/7
      M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector (3 : Fin 6) p ∧ q=qFace right sheet (diskBoundaryPoint p hp)} =
      {z : unitInterval × unitInterval |
        (z.2.val=flat ∧ (if right then 1-width else 0)≤z.1.val ∧
          z.1.val≤(if right then 1 else width)) ∨
        (z.1.val=(if right then 1 else 0) ∧ lower≤z.2.val ∧ z.2.val≤upper)}) := by
  classical
  let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
    fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
      closedArcSector (0 : Fin 6) p ∧
      a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
  let Q0 := Quotient (Relation.EqvGen.setoid R0)
  let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
    ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
      a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
      b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
  let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
    (if sheet then Sum.inr v else Sum.inl v)
  let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
    (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
  have data :
    let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
          closedArcSector (0 : Fin 6) p ∧
          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
      let Q0 := Quotient (Relation.EqvGen.setoid R0)
      let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
        ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
          a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
          b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
      let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
        (if sheet then Sum.inr v else Sum.inl v)
      let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
        (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
      ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
      ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
      ∃ M0 : Q0 ≃ₜ (unitInterval × unitInterval),
        (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
        (∀ v : StandardDisk, (H v).val=gaugeRescale
          (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
          (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
        (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).1.val=
            ((H v).val.1+1)/4 ∧
          (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
        (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).1.val=
            1-((H v).val.1+1)/4 ∧
          (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).2.val=((H v).val.2+1)/2) ∧
      ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
        (∀ v, (G v).val = gaugeRescale
          (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
          (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
      ∃ M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval),
        (∀ u, (M3 (Quotient.mk _ (Sum.inl u))).1.val=((G (M0 u)).val.1+1)/4 ∧
          (M3 (Quotient.mk _ (Sum.inl u))).2.val=((G (M0 u)).val.2+1)/2) ∧
        (∀ v, (M3 (Quotient.mk _ (Sum.inr v))).1.val=
            1-((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.1+1)/4 ∧
          (M3 (Quotient.mk _ (Sum.inr v))).2.val=
            ((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.2+1)/2) ∧
        (∀ i : Fin 6,
          H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
            closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
          {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
          | 0 => z.val.1=1
          | 1 => z.val.2=1 ∧ 0≤z.val.1
          | 2 => z.val.2=1 ∧ z.val.1≤0
          | 3 => z.val.1= -1
          | 4 => z.val.2= -1 ∧ z.val.1≤0
          | _ => z.val.2= -1 ∧ 0≤z.val.1}) ∧
        (∀ k : Fin 4, ∀ right : Bool,
          M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
            closedArcSector (![(4 : Fin 6),5,4,5] k) p ∧
            q=qFace right (![false,false,true,true] k) (diskBoundaryPoint p hp)} =
          {z : unitInterval × unitInterval | z.1.val=(if right then 1 else 0) ∧
            (![(2/7 : ℝ),3/7,5/7,4/7] k)≤z.2.val ∧
            z.2.val≤(![(3/7 : ℝ),4/7,6/7,5/7] k)}) ∧
        M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
          closedArcSector (2 : Fin 6) p ∧ q=Quotient.mk (Relation.EqvGen.setoid R1)
            (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))))} =
        {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/3 : ℝ)≤z.1.val ∧ z.1.val≤1/2} ∧
        M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
          closedArcSector (2 : Fin 6) p ∧ q=qFace true false (diskBoundaryPoint p hp)} =
        {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/2 : ℝ)≤z.1.val ∧ z.1.val≤2/3} ∧
        (∀ k : Fin 2, ∀ right : Bool,
          M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
            closedArcSector (![(1 : Fin 6),2] k) p ∧ q=qFace right true (diskBoundaryPoint p hp)} =
          {z : unitInterval × unitInterval | z.2.val=1 ∧
            (if right then 1-(![(1/2 : ℝ),1/3] k) else (![(1/3 : ℝ),3/10] k))≤z.1.val ∧
            z.1.val≤(if right then 1-(![(1/3 : ℝ),3/10] k) else (![(1/2 : ℝ),1/3] k))})
      := by
      classical
      let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
          closedArcSector (0 : Fin 6) p ∧
          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
      let Q0 := Quotient (Relation.EqvGen.setoid R0)
      let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
        ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
          a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
          b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
      let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
        (if sheet then Sum.inr v else Sum.inl v)
      let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
        (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
      have data :
        let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
            fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
              closedArcSector (0 : Fin 6) p ∧
              a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
          let Q0 := Quotient (Relation.EqvGen.setoid R0)
          let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
            ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
              a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
              b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
          let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
            (if sheet then Sum.inr v else Sum.inl v)
          let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
            (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
          ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
          ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
          ∃ M0 : Q0 ≃ₜ (unitInterval × unitInterval),
            (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
            (∀ v : StandardDisk, (H v).val=gaugeRescale
              (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
              (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
            (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).1.val=
                ((H v).val.1+1)/4 ∧
              (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
            (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).1.val=
                1-((H v).val.1+1)/4 ∧
              (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).2.val=((H v).val.2+1)/2) ∧
          ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
            (∀ v, (G v).val = gaugeRescale
              (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
              (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
          ∃ M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval),
            (∀ u, (M3 (Quotient.mk _ (Sum.inl u))).1.val=((G (M0 u)).val.1+1)/4 ∧
              (M3 (Quotient.mk _ (Sum.inl u))).2.val=((G (M0 u)).val.2+1)/2) ∧
            (∀ v, (M3 (Quotient.mk _ (Sum.inr v))).1.val=
                1-((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.1+1)/4 ∧
              (M3 (Quotient.mk _ (Sum.inr v))).2.val=
                ((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.2+1)/2) ∧
            (∀ i : Fin 6,
              H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
              {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
              | 0 => z.val.1=1
              | 1 => z.val.2=1 ∧ 0≤z.val.1
              | 2 => z.val.2=1 ∧ z.val.1≤0
              | 3 => z.val.1= -1
              | 4 => z.val.2= -1 ∧ z.val.1≤0
              | _ => z.val.2= -1 ∧ 0≤z.val.1}) ∧
            (∀ k : Fin 4, ∀ right : Bool,
              M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
                closedArcSector (![(4 : Fin 6),5,4,5] k) p ∧
                q=qFace right (![false,false,true,true] k) (diskBoundaryPoint p hp)} =
              {z : unitInterval × unitInterval | z.1.val=(if right then 1 else 0) ∧
                (![(2/7 : ℝ),3/7,5/7,4/7] k)≤z.2.val ∧
                z.2.val≤(![(3/7 : ℝ),4/7,6/7,5/7] k)}) ∧
            M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
              closedArcSector (2 : Fin 6) p ∧ q=Quotient.mk (Relation.EqvGen.setoid R1)
                (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))))} =
            {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/3 : ℝ)≤z.1.val ∧ z.1.val≤1/2} ∧
            M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
              closedArcSector (2 : Fin 6) p ∧ q=qFace true false (diskBoundaryPoint p hp)} =
            {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/2 : ℝ)≤z.1.val ∧ z.1.val≤2/3}
          := by
          classical
          let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
            fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
              closedArcSector (0 : Fin 6) p ∧
              a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
          let Q0 := Quotient (Relation.EqvGen.setoid R0)
          let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
            ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
              a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
              b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
          let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
            (if sheet then Sum.inr v else Sum.inl v)
          let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
            (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
          have data :
            let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                  closedArcSector (0 : Fin 6) p ∧
                  a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
              let Q0 := Quotient (Relation.EqvGen.setoid R0)
              let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
                ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
                  a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
                  b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
              let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
                (if sheet then Sum.inr v else Sum.inl v)
              let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
                (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
              ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
              ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
              ∃ M0 : Q0 ≃ₜ (unitInterval × unitInterval),
                (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
                (∀ v : StandardDisk, (H v).val=gaugeRescale
                  (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                  (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
                (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).1.val=
                    ((H v).val.1+1)/4 ∧
                  (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
                (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).1.val=
                    1-((H v).val.1+1)/4 ∧
                  (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).2.val=((H v).val.2+1)/2) ∧
              ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                (∀ v, (G v).val = gaugeRescale
                  (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
                  (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
              ∃ M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval),
                (∀ u, (M3 (Quotient.mk _ (Sum.inl u))).1.val=((G (M0 u)).val.1+1)/4 ∧
                  (M3 (Quotient.mk _ (Sum.inl u))).2.val=((G (M0 u)).val.2+1)/2) ∧
                (∀ v, (M3 (Quotient.mk _ (Sum.inr v))).1.val=
                    1-((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.1+1)/4 ∧
                  (M3 (Quotient.mk _ (Sum.inr v))).2.val=
                    ((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.2+1)/2) ∧
                (∀ i : Fin 6,
                  H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                    closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
                  {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
                  | 0 => z.val.1=1
                  | 1 => z.val.2=1 ∧ 0≤z.val.1
                  | 2 => z.val.2=1 ∧ z.val.1≤0
                  | 3 => z.val.1= -1
                  | 4 => z.val.2= -1 ∧ z.val.1≤0
                  | _ => z.val.2= -1 ∧ 0≤z.val.1}) ∧
                (∀ k : Fin 4, ∀ right : Bool,
                  M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
                    closedArcSector (![(4 : Fin 6),5,4,5] k) p ∧
                    q=qFace right (![false,false,true,true] k) (diskBoundaryPoint p hp)} =
                  {z : unitInterval × unitInterval | z.1.val=(if right then 1 else 0) ∧
                    (![(2/7 : ℝ),3/7,5/7,4/7] k)≤z.2.val ∧
                    z.2.val≤(![(3/7 : ℝ),4/7,6/7,5/7] k)})
              := by
              classical
              let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                  closedArcSector (0 : Fin 6) p ∧
                  a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
              let Q0 := Quotient (Relation.EqvGen.setoid R0)
              let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
                ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
                  a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
                  b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
              let q0 (sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R0)
                (if sheet then Sum.inr v else Sum.inl v)
              let qFace (right sheet : Bool) (v : StandardDisk) := Quotient.mk (Relation.EqvGen.setoid R1)
                (if right then Sum.inr (q0 (!sheet) v) else Sum.inl (q0 sheet v))
              have data :
                let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                    fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                      closedArcSector (0 : Fin 6) p ∧
                      a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
                  let Q0 := Quotient (Relation.EqvGen.setoid R0)
                  let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
                    ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
                      a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
                      b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
                  ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
                  ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                  ∃ M0 : Q0 ≃ₜ (unitInterval × unitInterval),
                    (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
                    (∀ v : StandardDisk, (H v).val=gaugeRescale
                      (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                      (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
                    (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).1.val=
                        ((H v).val.1+1)/4 ∧
                      (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
                    (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).1.val=
                        1-((H v).val.1+1)/4 ∧
                      (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).2.val=((H v).val.2+1)/2) ∧
                  ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                    (∀ v, (G v).val = gaugeRescale
                      (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
                      (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
                  ∃ M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval),
                    (∀ u, (M3 (Quotient.mk _ (Sum.inl u))).1.val=((G (M0 u)).val.1+1)/4 ∧
                      (M3 (Quotient.mk _ (Sum.inl u))).2.val=((G (M0 u)).val.2+1)/2) ∧
                    (∀ v, (M3 (Quotient.mk _ (Sum.inr v))).1.val=
                        1-((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.1+1)/4 ∧
                      (M3 (Quotient.mk _ (Sum.inr v))).2.val=
                        ((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.2+1)/2) ∧
                    (∀ i : Fin 6,
                      H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                        closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
                      {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
                      | 0 => z.val.1=1
                      | 1 => z.val.2=1 ∧ 0≤z.val.1
                      | 2 => z.val.2=1 ∧ z.val.1≤0
                      | 3 => z.val.1= -1
                      | 4 => z.val.2= -1 ∧ z.val.1≤0
                      | _ => z.val.2= -1 ∧ 0≤z.val.1})
                  := by
                  classical
                  let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                    fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                      closedArcSector (0 : Fin 6) p ∧
                      a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
                  let Q0 := Quotient (Relation.EqvGen.setoid R0)
                  let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
                    ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
                      a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
                      b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
                  have chartData :
                    let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                          closedArcSector (0 : Fin 6) p ∧
                          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
                      let Q0 := Quotient (Relation.EqvGen.setoid R0)
                      let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
                        ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
                          a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
                          b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
                      ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
                      ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                      ∃ M0 : Q0 ≃ₜ (unitInterval × unitInterval),
                        (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
                        (∀ v : StandardDisk, (H v).val=gaugeRescale
                          (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                          (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
                        (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).1.val=
                            ((H v).val.1+1)/4 ∧
                          (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
                        (∀ v, (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).1.val=
                            1-((H v).val.1+1)/4 ∧
                          (M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr v))).2.val=((H v).val.2+1)/2) ∧
                      ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                        (∀ v, (G v).val = gaugeRescale
                          (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
                          (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
                      ∃ M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ (unitInterval × unitInterval),
                        (∀ u, (M3 (Quotient.mk _ (Sum.inl u))).1.val=((G (M0 u)).val.1+1)/4 ∧
                          (M3 (Quotient.mk _ (Sum.inl u))).2.val=((G (M0 u)).val.2+1)/2) ∧
                        (∀ v, (M3 (Quotient.mk _ (Sum.inr v))).1.val=
                            1-((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.1+1)/4 ∧
                          (M3 (Quotient.mk _ (Sum.inr v))).2.val=
                            ((G (unitInterval.symmHomeomorph (M0 v).1,(M0 v).2)).val.2+1)/2)
                      := by
                      classical
                      let R0 : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                          closedArcSector (0 : Fin 6) p ∧
                          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
                      let Q0 := Quotient (Relation.EqvGen.setoid R0)
                      let R1 : (Q0 ⊕ Q0) → (Q0 ⊕ Q0) → Prop := fun a b =>
                        ∃ p : Sphere, ∃ hp : height p = 0, closedArcSector (1 : Fin 6) p ∧
                          a = Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))) ∧
                          b = Sum.inr (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)))
                      let D := unitInterval × unitInterval
                      have cutData : let R : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                        fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                          closedArcSector (0 : Fin 6) p ∧
                          a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
                      ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
                      ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                      ∃ M : Quotient (Relation.EqvGen.setoid R) ≃ₜ (unitInterval × unitInterval),
                        (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
                        (∀ v : StandardDisk, (H v).val=gaugeRescale
                          (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                          (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
                        (∀ p : Sphere, ∀ hp : height p=0,
                          closedArcSector (0 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).1=1) ∧
                        (∀ p : Sphere, ∀ hp : height p=0,
                          closedArcSector (1 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).2=1 ∧
                            0 ≤ ((H (diskBoundaryPoint p hp)).val).1) ∧
                        (∀ v, (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inl v))).1.val=
                            ((H v).val.1+1)/4 ∧
                          (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inl v))).2.val=((H v).val.2+1)/2) ∧
                        (∀ v, (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inr v))).1.val=
                            1-((H v).val.1+1)/4 ∧
                          (M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inr v))).2.val=((H v).val.2+1)/2) := by
                        classical
                        let R : (StandardDisk ⊕ StandardDisk) → (StandardDisk ⊕ StandardDisk) → Prop :=
                          fun a b => ∃ p : Sphere, ∃ hp : height p = 0,
                            closedArcSector (0 : Fin 6) p ∧
                            a = Sum.inl (diskBoundaryPoint p hp) ∧ b = Sum.inr (diskBoundaryPoint p hp)
                        let D := unitInterval × unitInterval
                        have chData : ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
                          ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                          ∃ N : Set.range (northDiskFace false) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                          ∃ S : Set.range (southDiskFace true) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                            (∀ x, L x=(x 0+x 1/Real.sqrt 3,-x 0+Real.sqrt 3*x 1)) ∧
                            (∀ v : StandardDisk, (H v).val=gaugeRescale
                              (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                              (Metric.closedBall (0 : ℝ × ℝ) 1) (L v.val)) ∧
                            (∀ v : StandardDisk, N ⟨northDiskFace false v,⟨v,rfl⟩⟩=H v) ∧
                            (∀ v : StandardDisk, S ⟨southDiskFace true v,⟨v,rfl⟩⟩=H v) ∧
                            (∀ p : Sphere, ∀ hp : height p=0,
                              closedArcSector (0 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).1=1) ∧
                            (∀ p : Sphere, ∀ hp : height p=0,
                              closedArcSector (1 : Fin 6) p ↔
                                ((H (diskBoundaryPoint p hp)).val).2=1 ∧
                                0 ≤ ((H (diskBoundaryPoint p hp)).val).1) := by
                          obtain ⟨L,H,hL,hcone,hH,⟨N,S,hN,hS⟩,hside⟩ := actual_whole_bank_exact_sector_square_side
                          have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
                              gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
                            have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                                {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
                              ext r
                              simp only [mem_setOf_eq]
                              constructor
                              · rintro ⟨hr,z,hz,hzx⟩
                                have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
                                exact ⟨hr,hz' ▸ hz⟩
                              · rintro ⟨hr,hx⟩
                                exact ⟨hr,r⁻¹ • x,hx,by simp⟩
                            rw [gauge_def',he,← gauge_def']
                            simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0  ≤  (1 : ℝ)) x
                          have hs : 0<Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
                          have hs2 : Real.sqrt (3 : ℝ)^2=3 := Real.sq_sqrt (by norm_num)
                          have cone (p : Sphere) (hp : height p=0) :
                              closedArcSector (1 : Fin 6) p ↔
                                0 ≤ (L (horizontal p)).1 ∧ (L (horizontal p)).1 ≤ (L (horizontal p)).2 := by
                            have eX : Real.sqrt 3*(L (horizontal p)).1=seamB p := by
                              rw [hL]
                              dsimp [horizontal,seamB]
                              field_simp [hs.ne']
                            have eYX : Real.sqrt 3*((L (horizontal p)).2-(L (horizontal p)).1)=-2*seamA p := by
                              rw [hL]
                              dsimp [horizontal,seamA]
                              field_simp [hs.ne']
                              ring_nf
                              rw [hs2]
                              ring
                            change (height p=0 ∧ 0 ≤ p.val 1 ∧ seamA p ≤ 0 ∧ 0 ≤ seamB p) ↔ _
                            rw [hp]
                            simp only [true_and]
                            constructor
                            · rintro ⟨hy,hA,hB⟩
                              have hx : 0 ≤ (L (horizontal p)).1 :=
                                nonneg_of_mul_nonneg_left (by rw [mul_comm,eX];exact hB) hs
                              have hxy : 0 ≤ (L (horizontal p)).2-(L (horizontal p)).1 :=
                                nonneg_of_mul_nonneg_left (by rw [mul_comm,eYX];linarith) hs
                              exact ⟨hx,by linarith⟩
                            · rintro ⟨hx,hxy⟩
                              have hB : 0 ≤ seamB p := eX ▸ mul_nonneg hs.le hx
                              have hA : seamA p ≤ 0 := by
                                have h := mul_nonneg hs.le (sub_nonneg.mpr hxy)
                                rw [eYX] at h
                                linarith
                              refine ⟨?_,hA,hB⟩
                              dsimp [seamA,seamB] at hA hB
                              linarith
                          refine ⟨L,H,N,S,hL,hH,hN,hS,hside,?_⟩
                          intro p hp
                          have hn : ‖horizontal p‖=1 := by
                            have hc := sphere_coordinate_squares p
                            have hn2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (horizontal p)
                            simp [Fin.sum_univ_succ,horizontal,Real.norm_eq_abs,sq_abs] at hn2
                            change ‖horizontal p‖^2=(p.val 0)^2+(p.val 1)^2 at hn2
                            have hp2 : p.val 2=0 := hp
                            rw [hp2] at hc
                            nlinarith only [hc,hn2,norm_nonneg (horizontal p)]
                          have hz : L (horizontal p)≠0 := by
                            intro hz
                            have hh : horizontal p=0 := L.injective (by simpa using hz)
                            rw [hh,norm_zero] at hn
                            norm_num at hn
                          have hnpos : 0<‖L (horizontal p)‖ := norm_pos_iff.mpr hz
                          have hvalue : (H (diskBoundaryPoint p hp)).val=
                              (1/‖L (horizontal p)‖) • L (horizontal p) := by
                            rw [hH]
                            change gaugeRescale (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                              (closedBall (0 : ℝ × ℝ) 1) (L (horizontal p))=_
                            rw [gaugeRescale_def,hgauge,hn,gauge_closedBall (by norm_num : (0 : ℝ) ≤ 1),div_one]
                          rw [hvalue]
                          change closedArcSector (1 : Fin 6) p ↔
                            (1/‖L (horizontal p)‖)*(L (horizontal p)).2=1 ∧
                              0 ≤ (1/‖L (horizontal p)‖)*(L (horizontal p)).1
                          rw [one_div_mul_eq_div,div_eq_one_iff_eq hnpos.ne',
                            one_div_mul_eq_div,le_div_iff₀ hnpos,zero_mul,cone p hp]
                          constructor
                          · rintro ⟨hx,hxy⟩
                            have hy : 0 ≤ (L (horizontal p)).2 := hx.trans hxy
                            refine ⟨?_,hx⟩
                            rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,
                              abs_of_nonneg hx,abs_of_nonneg hy,max_eq_right hxy]
                          · rintro ⟨hy,hx⟩
                            refine ⟨hx,?_⟩
                            rw [hy,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hx]
                            exact le_max_left _ _
                        obtain ⟨L,H,N,S,hL,hH,hN,hS,hside,hsector1⟩ := chData
                        have mData : let D := unitInterval × unitInterval
                          ∃ f : C(D ⊕ D,D), Function.Surjective f ∧
                            Function.Injective (fun x => f (Sum.inl x)) ∧
                            Function.Injective (fun y => f (Sum.inr y)) ∧
                            (∀ x y, f (Sum.inl x)=f (Sum.inr y) ↔
                              x.1=1 ∧ y.1=0 ∧ x.2=y.2) ∧
                            ∃ H : Quotient (Setoid.ker f) ≃ₜ D,
                              (∀ x, (f (Sum.inl x)).1.val=x.1.val/2 ∧ (f (Sum.inl x)).2=x.2) ∧
                              (∀ y, (f (Sum.inr y)).1.val=(y.1.val+1)/2 ∧ (f (Sum.inr y)).2=y.2) ∧
                              (∀ r, H (Quotient.mk (Setoid.ker f) r)=f r) := by
                          classical
                          let D := unitInterval × unitInterval
                          let L : D → D := fun x =>
                            (⟨x.1.val / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
                          let R : D → D := fun x =>
                            (⟨(x.1.val + 1) / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
                          have hL : Continuous L := by
                            apply Continuous.prodMk
                            · apply Continuous.subtype_mk
                              exact (continuous_subtype_val.comp continuous_fst).div_const 2
                            · exact continuous_snd
                          have hR : Continuous R := by
                            apply Continuous.prodMk
                            · apply Continuous.subtype_mk
                              exact ((continuous_subtype_val.comp continuous_fst).add_const 1).div_const 2
                            · exact continuous_snd
                          let f : C(D ⊕ D,D) := ⟨Sum.elim L R, hL.sumElim hR⟩
                          have hs : Function.Surjective f := by
                            intro x
                            by_cases hx : x.1.val ≤ 1/2
                            · refine ⟨Sum.inl (⟨2*x.1.val, ⟨by linarith [x.1.property.1], by linarith⟩⟩,x.2), ?_⟩
                              apply Prod.ext
                              · apply Subtype.ext
                                dsimp [f,L]
                                ring
                              · rfl
                            · refine ⟨Sum.inr (⟨2*x.1.val-1, ⟨by linarith, by linarith [x.1.property.2]⟩⟩,x.2), ?_⟩
                              apply Prod.ext
                              · apply Subtype.ext
                                dsimp [f,R]
                                ring
                              · rfl
                          have hiL : Function.Injective (fun x => f (Sum.inl x)) := by
                            intro x y h
                            apply Prod.ext
                            · apply Subtype.ext
                              have h₁ := congrArg (fun z : D => z.1.val) h
                              dsimp [f,L] at h₁
                              linarith
                            · simpa [f,L,R] using congrArg (fun z : D => z.2) h
                          have hiR : Function.Injective (fun x => f (Sum.inr x)) := by
                            intro x y h
                            apply Prod.ext
                            · apply Subtype.ext
                              have h₁ := congrArg (fun z : D => z.1.val) h
                              dsimp [f,R] at h₁
                              linarith
                            · simpa [f,L,R] using congrArg (fun z : D => z.2) h
                          have hseam (x y : D) : f (Sum.inl x) = f (Sum.inr y) ↔
                              x.1 = 1 ∧ y.1 = 0 ∧ x.2 = y.2 := by
                            constructor
                            · intro h
                              have h₁ := congrArg (fun z : D => z.1.val) h
                              dsimp [f,L,R] at h₁
                              refine ⟨Subtype.ext ?_, Subtype.ext ?_, by simpa [f,L,R] using congrArg (fun z : D => z.2) h⟩
                              · change x.1.val = 1
                                linarith [x.1.property.2,y.1.property.1]
                              · change y.1.val = 0
                                linarith [x.1.property.2,y.1.property.1]
                            · rintro ⟨hx,hy,h₂⟩
                              apply Prod.ext
                              · apply Subtype.ext
                                dsimp [f,L,R]
                                rw [hx,hy]
                                norm_num
                              · exact h₂
                          let q : Quotient (Setoid.ker f) → D := Quotient.lift f (fun x y h => h)
                          have hq : Continuous q := f.continuous.quotient_lift _
                          have hiq : Function.Injective q := by
                            intro x y h
                            induction x using Quotient.inductionOn with
                            | _ x =>
                              induction y using Quotient.inductionOn with
                              | _ y => exact Quotient.sound h
                          have hsq : Function.Surjective q := by
                            intro y
                            obtain ⟨x,hx⟩ := hs y
                            exact ⟨Quotient.mk (Setoid.ker f) x,hx⟩
                          let e := Equiv.ofBijective q ⟨hiq,hsq⟩
                          let H : Quotient (Setoid.ker f) ≃ₜ D :=
                            (show Continuous (e : Quotient (Setoid.ker f) → D) from hq).homeoOfEquivCompactToT2
                          exact ⟨f,hs,hiL,hiR,hseam,H,fun _ => ⟨rfl,rfl⟩,
                            fun _ => ⟨rfl,rfl⟩,fun _ => rfl⟩
                        obtain ⟨m,hm,hml,hmr,hseam,He,hmL,hmR,hmpin⟩ := mData
                        have qData : ∃ Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval),
                          ∀ z, (Q z).1.val = (z.val.1 + 1)/2 ∧ (Q z).2.val = (z.val.2 + 1)/2 := by
                          have bounds (z : Metric.closedBall (0 : ℝ × ℝ) 1) :
                              (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
                            have h := z.property
                            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using h
                          let F : Metric.closedBall (0 : ℝ × ℝ) 1 → unitInterval × unitInterval :=
                            fun z => (⟨(z.val.1+1)/2,⟨by linarith [(bounds z).1.1],by linarith [(bounds z).1.2]⟩⟩,
                              ⟨(z.val.2+1)/2,⟨by linarith [(bounds z).2.1],by linarith [(bounds z).2.2]⟩⟩)
                          let G : unitInterval × unitInterval → Metric.closedBall (0 : ℝ × ℝ) 1 :=
                            fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
                              simp only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
                              exact ⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
                                ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩⟩
                          have hF : Continuous F := by
                            apply Continuous.prodMk
                            · apply Continuous.subtype_mk
                              exact ((continuous_fst.comp continuous_subtype_val).add_const 1).div_const 2
                            · apply Continuous.subtype_mk
                              exact ((continuous_snd.comp continuous_subtype_val).add_const 1).div_const 2
                          have hG : Continuous G := by
                            apply Continuous.subtype_mk
                            apply Continuous.prodMk
                            · exact ((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const
                            · exact ((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const
                          let Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval) := {
                            toFun := F
                            invFun := G
                            left_inv := by
                              intro z
                              apply Subtype.ext
                              apply Prod.ext
                              all_goals (dsimp [F,G]; ring)
                            right_inv := by
                              intro z
                              apply Prod.ext
                              all_goals (apply Subtype.ext; dsimp [F,G]; ring)
                            continuous_toFun := hF
                            continuous_invFun := hG }
                          exact ⟨Q,fun _ => ⟨rfl,rfl⟩⟩
                        obtain ⟨Q,hQ⟩ := qData
                        let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph
                          (Homeomorph.refl unitInterval)
                        let n := H.trans Q
                        let s := n.trans flip
                        let B := Homeomorph.sumCongr n s
                        let F : C(StandardDisk ⊕ StandardDisk,D) := m.comp ⟨B,B.continuous⟩
                        have hFl : Function.Injective (fun v => F (Sum.inl v)) := hml.comp n.injective
                        have hFr : Function.Injective (fun v => F (Sum.inr v)) := hmr.comp s.injective
                        have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
                            gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
                          have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                              {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
                            ext r
                            simp only [mem_setOf_eq]
                            constructor
                            · rintro ⟨hr,z,hz,hzx⟩
                              have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
                              exact ⟨hr,hz' ▸ hz⟩
                            · rintro ⟨hr,hx⟩
                              exact ⟨hr,r⁻¹ • x,hx,by simp⟩
                          rw [gauge_def',he,← gauge_def']
                          simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0 ≤ (1 : ℝ)) x
                        have hboundary (v : StandardDisk) (hv : ((H v).val).1 = 1) : ‖v.val‖ = 1 := by
                          have hnorm : ‖(H v).val‖ = 1 := by
                            have hle : ‖(H v).val‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using (H v).property
                            rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                            have hle' : |(H v).val.2| ≤ 1 := by
                              have ha : |(H v).val.1| ≤ 1 ∧ |(H v).val.2| ≤ 1 := by
                                simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using hle
                              exact ha.2
                            rw [hv]
                            simpa using max_eq_left hle'
                          have hne : L v.val ≠ 0 := by
                            intro he
                            have hz : (H v).val = 0 := by rw [hH v,he,gaugeRescale_zero]
                            have := congrArg Prod.fst hz
                            simpa [hv] using this
                          have ht : gauge (closedBall (0 : ℝ × ℝ) 1) (L v.val) ≠ 0 := by
                            simpa [gauge_closedBall, norm_ne_zero_iff] using hne
                          have h := gauge_gaugeRescale' (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ht
                          rw [← hH v,hgauge] at h
                          simpa [gauge_closedBall,hnorm] using h.symm
                        have hparam (v : StandardDisk) (hv : ((H v).val).1 = 1) :
                            ∃ p : Sphere, ∃ hp : height p = 0,
                              closedArcSector (0 : Fin 6) p ∧ v = diskBoundaryPoint p hp := by
                          have hnorm := hboundary v hv
                          let p := northHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)
                          have hv' : v = coordinateDiskClosedBallHomeomorph (northHemisphereDiskHomeomorph p) := by
                            dsimp [p]
                            simp
                          have hhor : v.val = horizontal p.val := congrArg Subtype.val hv'
                          have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hhor
                          have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hhor
                          change v.val 0 = p.val.val 0 at h0
                          change v.val 1 = p.val.val 1 at h1
                          have hs := sphere_coordinate_squares p.val
                          have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) v.val
                          simp only [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,Fin.sum_univ_zero,add_zero] at hn
                          change ‖v.val‖ ^ 2 = (v.val 0)^2 + (v.val 1)^2 at hn
                          rw [hnorm,h0,h1] at hn
                          have hp : height p.val = 0 := by
                            change p.val.val 2 = 0
                            nlinarith only [hs,hn]
                          have hparam : v = diskBoundaryPoint p.val hp := hv'
                          refine ⟨p.val,hp,?_,hparam⟩
                          apply (hside p.val hp).mpr
                          rw [← hparam]
                          exact hv
                        have hcross (v w : StandardDisk) : F (Sum.inl v)=F (Sum.inr w) ↔
                            ∃ p : Sphere, ∃ hp : height p=0,
                              closedArcSector (0 : Fin 6) p ∧ v=diskBoundaryPoint p hp ∧ w=diskBoundaryPoint p hp := by
                          change m (Sum.inl (n v))=m (Sum.inr (s w)) ↔ _
                          rw [hseam]
                          constructor
                          · rintro ⟨hv,hw,hvw⟩
                            have hv' := congrArg Subtype.val hv
                            have hw' := congrArg Subtype.val hw
                            have hvw' := congrArg Subtype.val hvw
                            change (Q (H v)).1.val=1 at hv'
                            change 1-(Q (H w)).1.val=0 at hw'
                            change (Q (H v)).2.val=(Q (H w)).2.val at hvw'
                            rw [(hQ (H v)).1] at hv'
                            rw [(hQ (H w)).1] at hw'
                            rw [(hQ (H v)).2,(hQ (H w)).2] at hvw'
                            have hvside : (H v).val.1=1 := by linarith
                            have hwside : (H w).val.1=1 := by linarith
                            have he : v=w := by
                              apply H.injective
                              apply Subtype.ext
                              apply Prod.ext
                              · exact hvside.trans hwside.symm
                              · linarith
                            obtain ⟨p,hp,hi,hvparam⟩ := hparam v hvside
                            exact ⟨p,hp,hi,hvparam,he.symm.trans hvparam⟩
                          · rintro ⟨p,hp,hi,rfl,rfl⟩
                            have hright := (hside p hp).mp hi
                            refine ⟨?_,?_,?_⟩ <;> apply Subtype.ext
                            · change (Q (H (diskBoundaryPoint p hp))).1.val=1
                              rw [(hQ _).1,hright];norm_num
                            · change 1-(Q (H (diskBoundaryPoint p hp))).1.val=0
                              rw [(hQ _).1,hright];norm_num
                            · rfl
                        have hgenerated (a b : StandardDisk ⊕ StandardDisk) :
                            F a = F b ↔ Relation.EqvGen R a b := by
                          constructor
                          · intro hab
                            cases a with
                            | inl v =>
                              cases b with
                              | inl w =>
                                have he := hFl hab
                                subst w
                                exact .refl _
                              | inr w =>
                                obtain ⟨p,hp,hi,hv,hw⟩ := (hcross v w).mp hab
                                exact .rel _ _ ⟨p,hp,hi,congrArg Sum.inl hv,congrArg Sum.inr hw⟩
                            | inr v =>
                              cases b with
                              | inl w =>
                                obtain ⟨p,hp,hi,hw,hv⟩ := (hcross w v).mp hab.symm
                                exact .symm _ _ (.rel _ _ ⟨p,hp,hi,congrArg Sum.inl hw,congrArg Sum.inr hv⟩)
                              | inr w =>
                                have he := hFr hab
                                subst w
                                exact .refl _
                          · intro hab
                            induction hab with
                            | rel a b h =>
                              rcases h with ⟨p,hp,hi,rfl,rfl⟩
                              exact (hcross _ _).mpr ⟨p,hp,hi,rfl,rfl⟩
                            | refl a => rfl
                            | symm a b h ih => exact ih.symm
                            | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
                        let HF : Quotient (Setoid.ker F) ≃ₜ D :=
                          (Homeomorph.Quotient.congr B (by intros;rfl)).trans He
                        let M : Quotient (Relation.EqvGen.setoid R) ≃ₜ D :=
                          (Homeomorph.Quotient.congr (Homeomorph.refl (StandardDisk ⊕ StandardDisk))
                            (fun a b => (hgenerated a b).symm)).trans HF
                        have hpinL (v : StandardDisk) : M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inl v))=
                            m (Sum.inl (n v)) := by
                          change He (Quotient.mk (Setoid.ker m) (Sum.inl (n v)))=_
                          exact hmpin _
                        have hpinR (v : StandardDisk) : M (Quotient.mk (Relation.EqvGen.setoid R) (Sum.inr v))=
                            m (Sum.inr (s v)) := by
                          change He (Quotient.mk (Setoid.ker m) (Sum.inr (s v)))=_
                          exact hmpin _
                        refine ⟨L,H,M,hL,hH,hside,hsector1,?_,?_⟩
                        · intro v
                          rw [hpinL]
                          constructor
                          · rw [(hmL (n v)).1]
                            change (Q (H v)).1.val/2=((H v).val.1+1)/4
                            rw [(hQ _).1];ring
                          · rw [(hmL (n v)).2]
                            exact (hQ _).2
                        · intro v
                          rw [hpinR]
                          constructor
                          · rw [(hmR (s v)).1]
                            change ((1-(Q (H v)).1.val)+1)/2=1-((H v).val.1+1)/4
                            rw [(hQ _).1];ring
                          · rw [(hmR (s v)).2]
                            exact (hQ _).2
                      obtain ⟨L,H,M,hL,hH,hside,hsector1,hML,hMR⟩ := cutData
                      have quarterData :
                        let D := unitInterval × unitInterval
                            ∃ G : D ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                              (∀ v, (G v).val = gaugeRescale
                                (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
                                (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) ∧
                            ∃ f : C(D ⊕ D,D), Function.Surjective f ∧
                              Function.Injective (fun x => f (Sum.inl x)) ∧
                              Function.Injective (fun y => f (Sum.inr y)) ∧
                              (∀ x y, f (Sum.inl x)=f (Sum.inr y) ↔
                                x.2.val=1 ∧ y.2.val=1 ∧ x.1.val+y.1.val=1 ∧
                                (1/4 : ℝ)≤x.1.val ∧ x.1.val≤1/2) ∧
                              (∀ x, (f (Sum.inl x)).1.val=((G x).val.1+1)/4 ∧
                                (f (Sum.inl x)).2.val=((G x).val.2+1)/2) ∧
                              (∀ y, (f (Sum.inr y)).1.val=1-((G ((unitInterval.symmHomeomorph y.1),y.2)).val.1+1)/4 ∧
                                (f (Sum.inr y)).2.val=((G ((unitInterval.symmHomeomorph y.1),y.2)).val.2+1)/2) ∧
                              ∃ He : Quotient (Setoid.ker f) ≃ₜ D,
                                ∀ r, He (Quotient.mk (Setoid.ker f) r)=f r
                          := by
                        classical
                        let D := unitInterval × unitInterval
                        have gData : ∃ G : (unitInterval × unitInterval) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
                          (∀ v, ((G v).val).1 = 1 ↔
                            v.2.val = 1 ∧ (1/4 : ℝ) ≤ v.1.val ∧ v.1.val ≤ 1/2) ∧
                          (∀ v, v.2.val = 1 → (1/4 : ℝ) ≤ v.1.val → v.1.val ≤ 1/2 →
                            ((G v).val).2 = 8*v.1.val-3) ∧
                          (∀ v, (G v).val = gaugeRescale
                            (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8))
                            (Metric.closedBall (0 : ℝ × ℝ) 1) (v.2.val-7/8,v.1.val-3/8)) := by
                          let s : Set (ℝ × ℝ) := Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)
                          let t : Set (ℝ × ℝ) := closedBall 0 1
                          have hsc : Convex ℝ s := (convex_Icc _ _).prod (convex_Icc _ _)
                          have hscompact : IsCompact s := isCompact_Icc.prod isCompact_Icc
                          have hs0 : s ∈ 𝓝 (0 : ℝ × ℝ) := by
                            have h := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
                              (show (0 : ℝ × ℝ) ∈ Ioo (-7/8 : ℝ) (1/8) ×ˢ Ioo (-3/8 : ℝ) (5/8) from by norm_num)
                            exact Filter.mem_of_superset h (by rintro z ⟨hz,hw⟩; exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
                          have hsb : IsVonNBounded ℝ s := NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
                          have htc : Convex ℝ t := convex_closedBall _ _
                          have ht0 : t ∈ 𝓝 (0 : ℝ × ℝ) := closedBall_mem_nhds _ (by norm_num)
                          have htb : IsVonNBounded ℝ t := NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall
                          let g := gaugeRescaleHomeomorph s t hsc hs0 hsb htc ht0 htb
                          have himage : g '' s = t := by
                            have h := image_gaugeRescaleHomeomorph_closure hsc hs0 hsb htc ht0 htb
                            rw [hscompact.isClosed.closure_eq,isClosed_closedBall.closure_eq] at h
                            exact h
                          let f : (unitInterval × unitInterval) → ↥s := fun v =>
                            ⟨(v.2.val-7/8,v.1.val-3/8),by
                              exact ⟨⟨by linarith [v.2.property.1],by linarith [v.2.property.2]⟩,
                                ⟨by linarith [v.1.property.1],by linarith [v.1.property.2]⟩⟩⟩
                          let fi : ↥s → (unitInterval × unitInterval) := fun z =>
                            (⟨z.val.2+3/8,⟨by linarith [z.property.2.1],by linarith [z.property.2.2]⟩⟩,
                              ⟨z.val.1+7/8,⟨by linarith [z.property.1.1],by linarith [z.property.1.2]⟩⟩)
                          let e : (unitInterval × unitInterval) ≃ₜ ↥s := {
                            toFun := f
                            invFun := fi
                            left_inv := by
                              intro v
                              apply Prod.ext <;> apply Subtype.ext
                              all_goals (dsimp [f,fi];ring)
                            right_inv := by
                              intro z
                              apply Subtype.ext
                              apply Prod.ext
                              all_goals (dsimp [f,fi];ring)
                            continuous_toFun := by
                              apply Continuous.subtype_mk
                              apply Continuous.prodMk
                              · exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
                              · exact (continuous_subtype_val.comp continuous_fst).sub continuous_const
                            continuous_invFun := by
                              apply Continuous.prodMk
                              · apply Continuous.subtype_mk
                                exact (continuous_snd.comp continuous_subtype_val).add_const _
                              · apply Continuous.subtype_mk
                                exact (continuous_fst.comp continuous_subtype_val).add_const _ }
                          let G := e.trans ((g.image s).trans (Homeomorph.setCongr himage))
                          have hval (v : unitInterval × unitInterval) :
                              (G v).val = gaugeRescale s t (v.2.val-7/8,v.1.val-3/8) := rfl
                          have hfront (v : unitInterval × unitInterval) (hv : v.2.val=1) :
                              (v.2.val-7/8,v.1.val-3/8) ∈ frontier s := by
                            change _ ∈ closure s ∧ _ ∉ interior s
                            refine ⟨?_,?_⟩
                            · rw [hscompact.isClosed.closure_eq]
                              exact (f v).property
                            · intro hi
                              have hfst : v.2.val-7/8 ∈ interior (Icc (-7/8 : ℝ) (1/8)) := by
                                change _ ∈ interior (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)) at hi
                                rw [interior_prod_eq] at hi
                                exact hi.1
                              rw [interior_Icc] at hfst
                              rw [hv] at hfst
                              norm_num at hfst
                          have htopgauge (v : unitInterval × unitInterval) (hv : v.2.val=1) :
                              gauge s (v.2.val-7/8,v.1.val-3/8)=1 :=
                            (gauge_eq_one_iff_mem_frontier hsc hs0).mpr (hfront v hv)
                          have hnorm (v : unitInterval × unitInterval)
                              (hv : v.2.val=1) (hl : (1/4 : ℝ) ≤ v.1.val) (hr : v.1.val≤1/2) :
                              ‖(v.2.val-7/8,v.1.val-3/8)‖ = (1/8 : ℝ) := by
                            rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hv]
                            norm_num
                            rw [abs_le]
                            constructor <;> linarith
                          have hright (v : unitInterval × unitInterval)
                              (hv : v.2.val=1) (hl : (1/4 : ℝ) ≤ v.1.val) (hr : v.1.val≤1/2) :
                              (G v).val=(1,8*v.1.val-3) := by
                            rw [hval,gaugeRescale_def,htopgauge v hv]
                            have hgt : gauge t (v.2.val-7/8,v.1.val-3/8) = (1/8 : ℝ) := by
                              simpa only [t,gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)),div_one] using hnorm v hv hl hr
                            rw [hgt]
                            apply Prod.ext <;> dsimp
                            · rw [hv]; norm_num
                            · ring
                          refine ⟨G,?_,?_,hval⟩
                          · intro v
                            constructor
                            · intro hv
                              let z : ℝ × ℝ := (v.2.val-7/8,v.1.val-3/8)
                              have hle : ‖(G v).val‖≤1 := by
                                simpa only [t,mem_closedBall,dist_zero_right] using (G v).property
                              have hnG : ‖(G v).val‖=1 := by
                                have h2 : |(G v).val.2|≤1 := by
                                  have h' : |(G v).val.1|≤1 ∧ |(G v).val.2|≤1 := by
                                    simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using hle
                                  exact h'.2
                                rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hv]
                                simpa using max_eq_left h2
                              have hz : z ≠ 0 := by
                                intro he
                                have hh : (G v).val=0 := by rw [hval]; change gaugeRescale s t z=0; rw [he,gaugeRescale_zero]
                                have hf := congrArg Prod.fst hh
                                simpa [hv] using hf
                              have hgt : gauge t z=‖z‖ := by simp only [t,gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)),div_one]
                              have hgs : gauge s z=1 := by
                                have h := gauge_gaugeRescale' s (show gauge t z≠0 from by rw [hgt]; exact norm_ne_zero_iff.mpr hz)
                                change gauge t (gaugeRescale s t z)=gauge s z at h
                                rw [← hval v] at h
                                simpa only [t,gauge_closedBall (by norm_num : 0 ≤ (1 : ℝ)),div_one,hnG] using h.symm
                              have hfirst : z.1=‖z‖ := by
                                have hf := congrArg Prod.fst (hval v)
                                change (G v).val.1=(gauge s z/gauge t z)*z.1 at hf
                                rw [hv,hgs,hgt,one_div_mul_eq_div] at hf
                                exact ((div_eq_one_iff_eq (norm_ne_zero_iff.mpr hz)).mp hf.symm)
                              have hcone : 0≤z.1 ∧ |z.2|≤z.1 := by
                                refine ⟨hfirst.symm ▸ norm_nonneg z,?_⟩
                                rw [hfirst,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                                exact le_max_right _ _
                              have hmem : z∈s := (f v).property
                              have hzfirst : z.1=1/8 := by
                                by_contra hne
                                have hlt : z.1<1/8 := lt_of_le_of_ne hmem.1.2 hne
                                have hinter : z∈interior s := by
                                  rw [interior_prod_eq,interior_Icc,interior_Icc]
                                  have hcone' := abs_le.mp hcone.2
                                  constructor
                                  · exact ⟨by linarith [hcone.1],hlt⟩
                                  · exact ⟨by linarith [hcone'.1],by linarith [hcone'.2]⟩
                                have hglt := (gauge_lt_one_iff_mem_interior hsc hs0).mpr hinter
                                linarith
                              have hc := abs_le.mp hcone.2
                              change v.2.val-7/8=1/8 at hzfirst
                              change -(v.2.val-7/8)≤v.1.val-3/8 ∧ v.1.val-3/8≤v.2.val-7/8 at hc
                              exact ⟨by linarith,by linarith [hc.1],by linarith [hc.2]⟩
                            · rintro ⟨hv,hl,hr⟩
                              exact congrArg Prod.fst (hright v hv hl hr)
                          · intro v hv hl hr
                            exact congrArg Prod.snd (hright v hv hl hr)
                        obtain ⟨G,hside,hparam,hGformula⟩ := gData
                        have qData : ∃ Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ D,
                            ∀ z, (Q z).1.val=(z.val.1+1)/2 ∧ (Q z).2.val=(z.val.2+1)/2 := by
                          have bounds (z : Metric.closedBall (0 : ℝ × ℝ) 1) :
                              (-1 ≤ z.val.1 ∧ z.val.1 ≤ 1) ∧ (-1 ≤ z.val.2 ∧ z.val.2 ≤ 1) := by
                            have h := z.property
                            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using h
                          let F : Metric.closedBall (0 : ℝ × ℝ) 1 → unitInterval × unitInterval :=
                            fun z => (⟨(z.val.1+1)/2,⟨by linarith [(bounds z).1.1],by linarith [(bounds z).1.2]⟩⟩,
                              ⟨(z.val.2+1)/2,⟨by linarith [(bounds z).2.1],by linarith [(bounds z).2.2]⟩⟩)
                          let G : unitInterval × unitInterval → Metric.closedBall (0 : ℝ × ℝ) 1 :=
                            fun z => ⟨(2*z.1.val-1,2*z.2.val-1),by
                              simp only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
                              exact ⟨⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩,
                                ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩⟩
                          have hF : Continuous F := by
                            apply Continuous.prodMk
                            · apply Continuous.subtype_mk
                              exact ((continuous_fst.comp continuous_subtype_val).add_const 1).div_const 2
                            · apply Continuous.subtype_mk
                              exact ((continuous_snd.comp continuous_subtype_val).add_const 1).div_const 2
                          have hG : Continuous G := by
                            apply Continuous.subtype_mk
                            apply Continuous.prodMk
                            · exact ((continuous_subtype_val.comp continuous_fst).const_mul 2).sub continuous_const
                            · exact ((continuous_subtype_val.comp continuous_snd).const_mul 2).sub continuous_const
                          let Q : Metric.closedBall (0 : ℝ × ℝ) 1 ≃ₜ (unitInterval × unitInterval) := {
                            toFun := F
                            invFun := G
                            left_inv := by
                              intro z
                              apply Subtype.ext
                              apply Prod.ext
                              all_goals (dsimp [F,G]; ring)
                            right_inv := by
                              intro z
                              apply Prod.ext
                              all_goals (apply Subtype.ext; dsimp [F,G]; ring)
                            continuous_toFun := hF
                            continuous_invFun := hG }
                          exact ⟨Q,fun _ => ⟨rfl,rfl⟩⟩
                        obtain ⟨Q,hQ⟩ := qData
                        let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph
                          (Homeomorph.refl unitInterval)
                        let n := G.trans Q
                        let s := ((flip.trans G).trans Q).trans flip
                        let B := Homeomorph.sumCongr n s
                        have mData :
                          let D := unitInterval × unitInterval
                              ∃ f : C(D ⊕ D,D), Function.Surjective f ∧
                                Function.Injective (fun x => f (Sum.inl x)) ∧
                                Function.Injective (fun y => f (Sum.inr y)) ∧
                                (∀ x y, f (Sum.inl x)=f (Sum.inr y) ↔
                                  x.1=1 ∧ y.1=0 ∧ x.2=y.2) ∧
                                ∃ H : Quotient (Setoid.ker f) ≃ₜ D,
                                  (∀ x, (f (Sum.inl x)).1.val=x.1.val/2 ∧ (f (Sum.inl x)).2=x.2) ∧
                                  (∀ y, (f (Sum.inr y)).1.val=(y.1.val+1)/2 ∧ (f (Sum.inr y)).2=y.2) ∧
                                  (∀ r, H (Quotient.mk (Setoid.ker f) r)=f r)
                            := by
                            classical
                            let D := unitInterval × unitInterval
                            let L : D → D := fun x =>
                              (⟨x.1.val / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
                            let R : D → D := fun x =>
                              (⟨(x.1.val + 1) / 2, ⟨by linarith [x.1.property.1], by linarith [x.1.property.2]⟩⟩, x.2)
                            have hL : Continuous L := by
                              apply Continuous.prodMk
                              · apply Continuous.subtype_mk
                                exact (continuous_subtype_val.comp continuous_fst).div_const 2
                              · exact continuous_snd
                            have hR : Continuous R := by
                              apply Continuous.prodMk
                              · apply Continuous.subtype_mk
                                exact ((continuous_subtype_val.comp continuous_fst).add_const 1).div_const 2
                              · exact continuous_snd
                            let f : C(D ⊕ D,D) := ⟨Sum.elim L R, hL.sumElim hR⟩
                            have hs : Function.Surjective f := by
                              intro x
                              by_cases hx : x.1.val ≤ 1/2
                              · refine ⟨Sum.inl (⟨2*x.1.val, ⟨by linarith [x.1.property.1], by linarith⟩⟩,x.2), ?_⟩
                                apply Prod.ext
                                · apply Subtype.ext
                                  dsimp [f,L]
                                  ring
                                · rfl
                              · refine ⟨Sum.inr (⟨2*x.1.val-1, ⟨by linarith, by linarith [x.1.property.2]⟩⟩,x.2), ?_⟩
                                apply Prod.ext
                                · apply Subtype.ext
                                  dsimp [f,R]
                                  ring
                                · rfl
                            have hiL : Function.Injective (fun x => f (Sum.inl x)) := by
                              intro x y h
                              apply Prod.ext
                              · apply Subtype.ext
                                have h₁ := congrArg (fun z : D => z.1.val) h
                                dsimp [f,L] at h₁
                                linarith
                              · simpa [f,L,R] using congrArg (fun z : D => z.2) h
                            have hiR : Function.Injective (fun x => f (Sum.inr x)) := by
                              intro x y h
                              apply Prod.ext
                              · apply Subtype.ext
                                have h₁ := congrArg (fun z : D => z.1.val) h
                                dsimp [f,R] at h₁
                                linarith
                              · simpa [f,L,R] using congrArg (fun z : D => z.2) h
                            have hseam (x y : D) : f (Sum.inl x) = f (Sum.inr y) ↔
                                x.1 = 1 ∧ y.1 = 0 ∧ x.2 = y.2 := by
                              constructor
                              · intro h
                                have h₁ := congrArg (fun z : D => z.1.val) h
                                dsimp [f,L,R] at h₁
                                refine ⟨Subtype.ext ?_, Subtype.ext ?_, by simpa [f,L,R] using congrArg (fun z : D => z.2) h⟩
                                · change x.1.val = 1
                                  linarith [x.1.property.2,y.1.property.1]
                                · change y.1.val = 0
                                  linarith [x.1.property.2,y.1.property.1]
                              · rintro ⟨hx,hy,h₂⟩
                                apply Prod.ext
                                · apply Subtype.ext
                                  dsimp [f,L,R]
                                  rw [hx,hy]
                                  norm_num
                                · exact h₂
                            let q : Quotient (Setoid.ker f) → D := Quotient.lift f (fun x y h => h)
                            have hq : Continuous q := f.continuous.quotient_lift _
                            have hiq : Function.Injective q := by
                              intro x y h
                              induction x using Quotient.inductionOn with
                              | _ x =>
                                induction y using Quotient.inductionOn with
                                | _ y => exact Quotient.sound h
                            have hsq : Function.Surjective q := by
                              intro y
                              obtain ⟨x,hx⟩ := hs y
                              exact ⟨Quotient.mk (Setoid.ker f) x,hx⟩
                            let e := Equiv.ofBijective q ⟨hiq,hsq⟩
                            let H : Quotient (Setoid.ker f) ≃ₜ D :=
                              (show Continuous (e : Quotient (Setoid.ker f) → D) from hq).homeoOfEquivCompactToT2
                            exact ⟨f,hs,hiL,hiR,hseam,H,fun _ => ⟨rfl,rfl⟩,
                              fun _ => ⟨rfl,rfl⟩,fun _ => rfl⟩
                        obtain ⟨m,hm,hml,hmr,hseam,He,hmL,hmR,hmHe⟩ := mData
                        let f : C(D ⊕ D,D) := m.comp ⟨B,B.continuous⟩
                        refine ⟨G,hGformula,f,hm.comp B.surjective,hml.comp n.injective,hmr.comp s.injective,?_,?_,?_,?_⟩
                        · intro x y
                          change m (Sum.inl (n x))=m (Sum.inr (s y)) ↔ _
                          rw [hseam]
                          constructor
                          · rintro ⟨hx,hy,hxy⟩
                            have hx' := congrArg Subtype.val hx
                            have hy' := congrArg Subtype.val hy
                            have hxy' := congrArg Subtype.val hxy
                            change (Q (G x)).1.val=1 at hx'
                            change 1-(Q (G (flip y))).1.val=0 at hy'
                            change (Q (G x)).2.val=(Q (G (flip y))).2.val at hxy'
                            rw [(hQ (G x)).1] at hx'
                            rw [(hQ (G (flip y))).1] at hy'
                            rw [(hQ (G x)).2,(hQ (G (flip y))).2] at hxy'
                            have hxside : (G x).val.1=1 := by linarith
                            have hyside : (G (flip y)).val.1=1 := by linarith
                            obtain ⟨hx2,hxl,hxr⟩ := (hside x).mp hxside
                            obtain ⟨hy2,hyl,hyr⟩ := (hside (flip y)).mp hyside
                            rw [hparam x hx2 hxl hxr,hparam (flip y) hy2 hyl hyr] at hxy'
                            change y.2.val=1 at hy2
                            change 1/4≤1-y.1.val at hyl
                            change 1-y.1.val≤1/2 at hyr
                            change (8*x.1.val-3+1)/2=(8*(1-y.1.val)-3+1)/2 at hxy'
                            exact ⟨hx2,hy2,by linarith,hxl,hxr⟩
                          · rintro ⟨hx2,hy2,hxy,hxl,hxr⟩
                            have hy2' : (flip y).2.val=1 := hy2
                            have hyl : (1/4 : ℝ)≤(flip y).1.val := by change 1/4≤1-y.1.val;linarith
                            have hyr : (flip y).1.val≤(1/2 : ℝ) := by change 1-y.1.val≤1/2;linarith
                            have hxside := (hside x).mpr ⟨hx2,hxl,hxr⟩
                            have hyside := (hside (flip y)).mpr ⟨hy2',hyl,hyr⟩
                            refine ⟨?_,?_,?_⟩ <;> apply Subtype.ext
                            · change (Q (G x)).1.val=1
                              rw [(hQ (G x)).1,hxside];norm_num
                            · change 1-(Q (G (flip y))).1.val=0
                              rw [(hQ (G (flip y))).1,hyside];norm_num
                            · change (Q (G x)).2.val=(Q (G (flip y))).2.val
                              rw [(hQ (G x)).2,(hQ (G (flip y))).2,
                                hparam x hx2 hxl hxr,hparam (flip y) hy2' hyl hyr]
                              change (8*x.1.val-3+1)/2=(8*(1-y.1.val)-3+1)/2
                              linarith
                        · intro x
                          change (m (Sum.inl (n x))).1.val=_ ∧ (m (Sum.inl (n x))).2.val=_
                          rw [(hmL (n x)).1]
                          have hy := congrArg Subtype.val (hmL (n x)).2
                          change (m (Sum.inl (n x))).2.val=(Q (G x)).2.val at hy
                          rw [hy]
                          change (Q (G x)).1.val/2=_ ∧ (Q (G x)).2.val=_
                          rw [(hQ (G x)).1,(hQ (G x)).2]
                          constructor
                          · ring
                          · rfl
                        · intro y
                          change (m (Sum.inr (s y))).1.val=_ ∧ (m (Sum.inr (s y))).2.val=_
                          rw [(hmR (s y)).1]
                          have hy := congrArg Subtype.val (hmR (s y)).2
                          change (m (Sum.inr (s y))).2.val=(Q (G (flip y))).2.val at hy
                          rw [hy]
                          change ((1-(Q (G (flip y))).1.val)+1)/2=_ ∧ (Q (G (flip y))).2.val=_
                          rw [(hQ (G (flip y))).1,(hQ (G (flip y))).2]
                          change ((1-((G (flip y)).val.1+1)/2)+1)/2=1-((G (flip y)).val.1+1)/4 ∧
                            ((G (flip y)).val.2+1)/2=((G (flip y)).val.2+1)/2
                          constructor
                          · ring
                          · rfl
                        · let HF : Quotient (Setoid.ker f) ≃ₜ D := (Homeomorph.Quotient.congr B (by intros;rfl)).trans He
                          refine ⟨HF,?_⟩
                          intro r
                          exact hmHe (B r)
                      obtain ⟨G,hGformula,m,hm,hml,hmr,hseam,hmL,hmR,He,hmpin⟩ := quarterData
                      have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
                          gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
                        have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                            {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
                          ext r
                          simp only [mem_setOf_eq]
                          constructor
                          · rintro ⟨hr,z,hz,hzx⟩
                            have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
                            exact ⟨hr,hz' ▸ hz⟩
                          · rintro ⟨hr,hx⟩
                            exact ⟨hr,r⁻¹ • x,hx,by simp⟩
                        rw [gauge_def',he,← gauge_def']
                        simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0 ≤ (1 : ℝ)) x
                      have hboundary (v : StandardDisk) (hv : ‖(H v).val‖=1) :
                          ∃ p : Sphere, ∃ hp : height p=0, v=diskBoundaryPoint p hp := by
                        have hz : L v.val≠0 := by
                          intro hz
                          have hh : (H v).val=0 := by rw [hH v,hz,gaugeRescale_zero]
                          rw [hh,norm_zero] at hv
                          norm_num at hv
                        have ht : gauge (closedBall (0 : ℝ × ℝ) 1) (L v.val)≠0 := by
                          simpa [gauge_closedBall,norm_ne_zero_iff] using hz
                        have hg := gauge_gaugeRescale' (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ht
                        rw [← hH v,hgauge] at hg
                        have hnorm : ‖v.val‖=1 := by simpa [gauge_closedBall,hv] using hg.symm
                        let p := northHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)
                        have hv' : v = coordinateDiskClosedBallHomeomorph (northHemisphereDiskHomeomorph p) := by
                          dsimp [p]
                          simp
                        have hhor : v.val = horizontal p.val := congrArg Subtype.val hv'
                        have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hhor
                        have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hhor
                        change v.val 0 = p.val.val 0 at h0
                        change v.val 1 = p.val.val 1 at h1
                        have hs := sphere_coordinate_squares p.val
                        have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) v.val
                        simp only [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,Fin.sum_univ_zero,add_zero] at hn
                        change ‖v.val‖ ^ 2 = (v.val 0)^2 + (v.val 1)^2 at hn
                        rw [hnorm,h0,h1] at hn
                        have hp : height p.val = 0 := by
                          change p.val.val 2 = 0
                          nlinarith only [hs,hn]
                        have hparam : v = diskBoundaryPoint p.val hp := hv'
                        exact ⟨p.val,hp,hparam⟩
                      have hupper (v : StandardDisk) : (H v).val.1≤1 := by
                        have h : |(H v).val.1|≤1 ∧ |(H v).val.2|≤1 := by
                          simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff]
                            using (H v).property
                        exact (abs_le.mp h.1).2
                      have hleft (u : Q0) (hy : (M u).2.val=1)
                          (hl : (1/4 : ℝ)≤(M u).1.val) (hr : (M u).1.val≤1/2) :
                          ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (1 : Fin 6) p ∧
                            u=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp)) := by
                        let z : Metric.closedBall (0 : ℝ × ℝ) 1 := ⟨(4*(M u).1.val-1,1),by
                          rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
                          exact ⟨⟨by linarith,by linarith⟩,⟨by norm_num,by norm_num⟩⟩⟩
                        let v := H.symm z
                        have hv : H v=z := H.apply_symm_apply z
                        have hnorm : ‖(H v).val‖=1 := by
                          rw [hv]
                          change ‖(4*(M u).1.val-1,(1 : ℝ))‖=1
                          rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                          norm_num
                          rw [abs_le]
                          exact ⟨by linarith,by linarith⟩
                        obtain ⟨p,hp,hparam⟩ := hboundary v hnorm
                        have hi : closedArcSector (1 : Fin 6) p := by
                          apply (hsector1 p hp).mpr
                          rw [← hparam,hv]
                          exact ⟨rfl,by change 0≤4*(M u).1.val-1;linarith⟩
                        have hu : u=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v) := by
                          apply M.injective
                          apply Prod.ext <;> apply Subtype.ext
                          · rw [(hML v).1,hv]
                            change (M u).1.val=((4*(M u).1.val-1)+1)/4
                            ring
                          · rw [(hML v).2,hv]
                            change (M u).2.val=((1 : ℝ)+1)/2
                            rw [hy];norm_num
                        exact ⟨p,hp,hi,hu.trans (congrArg (fun v => Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v)) hparam)⟩
                      let B := Homeomorph.sumCongr M M
                      let F : C(Q0 ⊕ Q0,D) := m.comp ⟨B,B.continuous⟩
                      have hFl : Function.Injective (fun u => F (Sum.inl u)) := hml.comp M.injective
                      have hFr : Function.Injective (fun v => F (Sum.inr v)) := hmr.comp M.injective
                      have hcross (u v : Q0) : F (Sum.inl u)=F (Sum.inr v) ↔
                          ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (1 : Fin 6) p ∧
                            u=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp)) ∧
                            v=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)) := by
                        change m (Sum.inl (M u))=m (Sum.inr (M v)) ↔ _
                        rw [hseam]
                        constructor
                        · rintro ⟨hu2,hv2,huv,hul,hur⟩
                          obtain ⟨p,hp,hi,hu⟩ := hleft u hu2 hul hur
                          have hv : v=Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inr (diskBoundaryPoint p hp)) := by
                            apply M.injective
                            apply Prod.ext <;> apply Subtype.ext
                            · have he := (hML (diskBoundaryPoint p hp)).1
                              rw [← hu] at he
                              rw [(hMR (diskBoundaryPoint p hp)).1]
                              linarith
                            · rw [(hMR (diskBoundaryPoint p hp)).2,(hsector1 p hp).mp hi |>.1,hv2]
                              norm_num
                          exact ⟨p,hp,hi,hu,hv⟩
                        · rintro ⟨p,hp,hi,rfl,rfl⟩
                          obtain ⟨hy,hx⟩ := (hsector1 p hp).mp hi
                          have hxu := hupper (diskBoundaryPoint p hp)
                          rw [(hML _).1,(hML _).2,(hMR _).1,(hMR _).2,hy]
                          exact ⟨by norm_num,by norm_num,by ring,by linarith,by linarith⟩
                      have hgenerated (a b : Q0 ⊕ Q0) : F a=F b ↔ Relation.EqvGen R1 a b := by
                        constructor
                        · intro hab
                          cases a with
                          | inl u =>
                            cases b with
                            | inl v =>
                              have he := hFl hab
                              subst v
                              exact .refl _
                            | inr v =>
                              obtain ⟨p,hp,hi,hu,hv⟩ := (hcross u v).mp hab
                              exact .rel _ _ ⟨p,hp,hi,congrArg Sum.inl hu,congrArg Sum.inr hv⟩
                          | inr u =>
                            cases b with
                            | inl v =>
                              obtain ⟨p,hp,hi,hv,hu⟩ := (hcross v u).mp hab.symm
                              exact .symm _ _ (.rel _ _ ⟨p,hp,hi,congrArg Sum.inl hv,congrArg Sum.inr hu⟩)
                            | inr v =>
                              have he := hFr hab
                              subst v
                              exact .refl _
                        · intro hab
                          induction hab with
                          | rel a b h =>
                            rcases h with ⟨p,hp,hi,rfl,rfl⟩
                            exact (hcross _ _).mpr ⟨p,hp,hi,rfl,rfl⟩
                          | refl a => rfl
                          | symm a b h ih => exact ih.symm
                          | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
                      let HF : Quotient (Setoid.ker F) ≃ₜ D :=
                        (Homeomorph.Quotient.congr B (by intros;rfl)).trans He
                      let M3 : Quotient (Relation.EqvGen.setoid R1) ≃ₜ D := (Homeomorph.Quotient.congr (Homeomorph.refl (Q0 ⊕ Q0))
                        (fun a b => (hgenerated a b).symm)).trans HF
                      have hM3 (r : Q0 ⊕ Q0) : M3 (Quotient.mk (Relation.EqvGen.setoid R1) r)=F r := hmpin (B r)
                      refine ⟨L,H,M,hL,hH,hML,hMR,G,hGformula,M3,?_,?_⟩
                      · intro u
                        rw [hM3]
                        exact hmL (M u)
                      · intro v
                        rw [hM3]
                        exact hmR (M v)
                  obtain ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R⟩ := chartData
                  have hsector :
                        (∀ i : Fin 6, ∀ p : Sphere, ∀ hp : height p=0,
                          let z := (H (diskBoundaryPoint p hp)).val
                          closedArcSector i p ↔ match i.val with
                          | 0 => z.1=1
                          | 1 => z.2=1 ∧ 0≤z.1
                          | 2 => z.2=1 ∧ z.1≤0
                          | 3 => z.1= -1
                          | 4 => z.2= -1 ∧ z.1≤0
                          | _ => z.2= -1 ∧ 0≤z.1)
                      := by
                      have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
                          gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x)=‖x‖ := by
                        have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                            {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
                          ext r
                          simp only [mem_setOf_eq]
                          constructor
                          · rintro ⟨hr,z,hz,hzx⟩
                            have hz' : z=r⁻¹ • x := L.injective (by simpa using hzx)
                            exact ⟨hr,hz' ▸ hz⟩
                          · rintro ⟨hr,hx⟩
                            exact ⟨hr,r⁻¹ • x,hx,by simp⟩
                        rw [gauge_def',he,←gauge_def']
                        simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0≤(1:ℝ)) x
                      intro i p hp
                      have hs : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
                      have hs2 : Real.sqrt (3:ℝ)^2=3 := Real.sq_sqrt (by norm_num)
                      have hn : ‖horizontal p‖=1 := by
                        have hc := sphere_coordinate_squares p
                        have hn2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (horizontal p)
                        simp [Fin.sum_univ_succ,horizontal,Real.norm_eq_abs,sq_abs] at hn2
                        change ‖horizontal p‖^2=(p.val 0)^2+(p.val 1)^2 at hn2
                        have hp2 : p.val 2=0 := hp
                        rw [hp2] at hc
                        nlinarith only [hc,hn2,norm_nonneg (horizontal p)]
                      have hz : L (horizontal p)≠0 := by
                        intro h
                        have hh : horizontal p=0 := L.injective (by simpa using h)
                        rw [hh,norm_zero] at hn
                        norm_num at hn
                      let n := ‖L (horizontal p)‖
                      have hnp : 0<n := norm_pos_iff.mpr hz
                      have hval : (H (diskBoundaryPoint p hp)).val=(1/n) • L (horizontal p) := by
                        rw [hH]
                        change gaugeRescale (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
                          (closedBall (0 : ℝ × ℝ) 1) (L (horizontal p))=_
                        rw [gaugeRescale_def,hgauge,hn,gauge_closedBall (by norm_num : (0:ℝ)≤1),div_one]
                      let a := (H (diskBoundaryPoint p hp)).val.1
                      let b := (H (diskBoundaryPoint p hp)).val.2
                      have hx : n*a=(L (horizontal p)).1 := by
                        dsimp [a];rw [hval];dsimp;field_simp [hnp.ne']
                      have hy : n*b=(L (horizontal p)).2 := by
                        dsimp [b];rw [hval];dsimp;field_simp [hnp.ne']
                      have hnorm : max |a| |b|=1 := by
                        have hh : ‖(H (diskBoundaryPoint p hp)).val‖=1 := by
                          rw [hval,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos zero_lt_one hnp)]
                          change (1/n)*n=1
                          field_simp [hnp.ne']
                        simpa only [Prod.norm_def,Real.norm_eq_abs] using hh
                      have haBounds : -1≤a ∧ a≤1 := abs_le.mp ((le_max_left _ _).trans_eq hnorm)
                      have hbBounds : -1≤b ∧ b≤1 := abs_le.mp ((le_max_right _ _).trans_eq hnorm)
                      have eB : Real.sqrt 3*(L (horizontal p)).1=seamB p := by
                        rw [hL];dsimp [horizontal,seamB];field_simp [hs.ne']
                      have eA : Real.sqrt 3*((L (horizontal p)).2-(L (horizontal p)).1)= -2*seamA p := by
                        rw [hL];dsimp [horizontal,seamA];field_simp [hs.ne'];ring_nf;rw [hs2];ring
                      have eY : Real.sqrt 3*((L (horizontal p)).1+(L (horizontal p)).2)=4*p.val 1 := by
                        rw [hL];dsimp [horizontal];field_simp [hs.ne'];ring_nf;rw [hs2];ring
                      have hB : seamB p=(Real.sqrt 3*n)*a := by rw [←eB,←hx];ring
                      have hA : seamA p=(Real.sqrt 3*n/2)*(a-b) := by rw [←hx,←hy] at eA;nlinarith [eA]
                      have hY : p.val 1=(Real.sqrt 3*n/4)*(a+b) := by rw [←hx,←hy] at eY;nlinarith [eY]
                      have hc : 0<Real.sqrt 3*n := mul_pos hs hnp
                      have hc2 : 0<Real.sqrt 3*n/2 := div_pos hc (by norm_num)
                      have hc4 : 0<Real.sqrt 3*n/4 := div_pos hc (by norm_num)
                      have hmulnonpos (c : ℝ) (hc : 0<c) (x : ℝ) : c*x≤0 ↔ x≤0 := by
                        simpa only [mul_zero] using (mul_le_mul_iff_right₀ hc : c*x≤c*0 ↔ x≤0)
                      dsimp only
                      change closedArcSector i p ↔ _
                      fin_cases i
                      all_goals simp only [closedArcSector,hp,true_and,hY,hA,hB]
                      all_goals simp only [mul_nonneg_iff_of_pos_left hc,mul_nonneg_iff_of_pos_left hc2,
                        mul_nonneg_iff_of_pos_left hc4,hmulnonpos _ hc,
                        hmulnonpos _ hc2,hmulnonpos _ hc4]
                      · change (0≤a+b ∧ 0≤a-b ∧ 0≤a) ↔ a=1
                        constructor
                        · rintro ⟨h1,h2,h3⟩
                          have he : max |a| |b|=a := by rw [abs_of_nonneg h3,max_eq_left];rw [abs_le];constructor <;> linarith
                          linarith
                        · intro h;subst a;exact ⟨by linarith [hbBounds.1],by linarith [hbBounds.2],by linarith⟩
                      · change (0≤a+b ∧ a-b≤0 ∧ 0≤a) ↔ b=1 ∧ 0≤a
                        constructor
                        · rintro ⟨h1,h2,h3⟩
                          have hb : 0≤b := by linarith
                          have he : max |a| |b|=b := by rw [abs_of_nonneg h3,abs_of_nonneg hb,max_eq_right (by linarith)]
                          exact ⟨by linarith,h3⟩
                        · rintro ⟨h,hx⟩;subst b;exact ⟨by linarith,by linarith [haBounds.2],hx⟩
                      · change (0≤a+b ∧ a-b≤0 ∧ a≤0) ↔ b=1 ∧ a≤0
                        constructor
                        · rintro ⟨h1,h2,h3⟩
                          have hb : 0≤b := by linarith
                          have he : max |a| |b|=b := by rw [abs_of_nonpos h3,abs_of_nonneg hb,max_eq_right (by linarith)]
                          exact ⟨by linarith,h3⟩
                        · rintro ⟨h,hx⟩;subst b;exact ⟨by linarith [haBounds.1],by linarith,hx⟩
                      · change (a+b≤0 ∧ a-b≤0 ∧ a≤0) ↔ a= -1
                        constructor
                        · rintro ⟨h1,h2,h3⟩
                          have he : max |a| |b|= -a := by rw [abs_of_nonpos h3,max_eq_left];rw [abs_le];constructor <;> linarith
                          linarith
                        · intro h;subst a;exact ⟨by linarith [hbBounds.2],by linarith [hbBounds.1],by linarith⟩
                      · change (a+b≤0 ∧ 0≤a-b ∧ a≤0) ↔ b= -1 ∧ a≤0
                        constructor
                        · rintro ⟨h1,h2,h3⟩
                          have hb : b≤0 := by linarith
                          have he : max |a| |b|= -b := by rw [abs_of_nonpos h3,abs_of_nonpos hb,max_eq_right (by linarith)]
                          exact ⟨by linarith,h3⟩
                        · rintro ⟨h,hx⟩;subst b;exact ⟨by linarith,by linarith [haBounds.1],hx⟩
                      · change (a+b≤0 ∧ 0≤a-b ∧ 0≤a) ↔ b= -1 ∧ 0≤a
                        constructor
                        · rintro ⟨h1,h2,h3⟩
                          have hb : b≤0 := by linarith
                          have he : max |a| |b|= -b := by rw [abs_of_nonneg h3,abs_of_nonpos hb,max_eq_right (by linarith)]
                          exact ⟨by linarith,h3⟩
                        · rintro ⟨h,hx⟩;subst b;exact ⟨by linarith [haBounds.2],by linarith,hx⟩
                  have himages :
                        (∀ i : Fin 6,
                          H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                            closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
                          {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
                          | 0 => z.val.1=1
                          | 1 => z.val.2=1 ∧ 0≤z.val.1
                          | 2 => z.val.2=1 ∧ z.val.1≤0
                          | 3 => z.val.1= -1
                          | 4 => z.val.2= -1 ∧ z.val.1≤0
                          | _ => z.val.2= -1 ∧ 0≤z.val.1})
                      := by
                      have hgauge (x : EuclideanSpace ℝ (Fin 2)) :
                          gauge (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (L x) = ‖x‖ := by
                        have he : {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • L x ∈ L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                            {r : ℝ | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
                          ext r
                          simp only [mem_setOf_eq]
                          constructor
                          · rintro ⟨hr,z,hz,hzx⟩
                            have hz' : z = r⁻¹ • x := L.injective (by simpa using hzx)
                            exact ⟨hr,hz' ▸ hz⟩
                          · rintro ⟨hr,hx⟩
                            exact ⟨hr,r⁻¹ • x,hx,by simp⟩
                        rw [gauge_def',he,← gauge_def']
                        simpa using gauge_closedBall (E := EuclideanSpace ℝ (Fin 2)) (by norm_num : 0 ≤ (1 : ℝ)) x
                      have hboundary (v : StandardDisk) (hv : ‖(H v).val‖=1) :
                          ∃ p : Sphere, ∃ hp : height p=0, v=diskBoundaryPoint p hp := by
                        have hz : L v.val≠0 := by
                          intro hz
                          have hh : (H v).val=0 := by rw [hH v,hz,gaugeRescale_zero]
                          rw [hh,norm_zero] at hv
                          norm_num at hv
                        have ht : gauge (closedBall (0 : ℝ × ℝ) 1) (L v.val)≠0 := by
                          simpa [gauge_closedBall,norm_ne_zero_iff] using hz
                        have hg := gauge_gaugeRescale' (L '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) ht
                        rw [← hH v,hgauge] at hg
                        have hnorm : ‖v.val‖=1 := by simpa [gauge_closedBall,hv] using hg.symm
                        let p := northHemisphereDiskHomeomorph.symm (coordinateDiskClosedBallHomeomorph.symm v)
                        have hv' : v = coordinateDiskClosedBallHomeomorph (northHemisphereDiskHomeomorph p) := by
                          dsimp [p]
                          simp
                        have hhor : v.val = horizontal p.val := congrArg Subtype.val hv'
                        have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hhor
                        have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hhor
                        change v.val 0 = p.val.val 0 at h0
                        change v.val 1 = p.val.val 1 at h1
                        have hs := sphere_coordinate_squares p.val
                        have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) v.val
                        simp only [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,Fin.sum_univ_zero,add_zero] at hn
                        change ‖v.val‖ ^ 2 = (v.val 0)^2 + (v.val 1)^2 at hn
                        rw [hnorm,h0,h1] at hn
                        have hp : height p.val = 0 := by
                          change p.val.val 2 = 0
                          nlinarith only [hs,hn]
                        have hparam : v = diskBoundaryPoint p.val hp := hv'
                        exact ⟨p.val,hp,hparam⟩
                      intro i
                      ext z
                      constructor
                      · rintro ⟨v,⟨p,hp,hi,rfl⟩,rfl⟩
                        exact (hsector i p hp).mp hi
                      · intro hz
                        change match i.val with
                          | 0 => z.val.1=1
                          | 1 => z.val.2=1 ∧ 0≤z.val.1
                          | 2 => z.val.2=1 ∧ z.val.1≤0
                          | 3 => z.val.1= -1
                          | 4 => z.val.2= -1 ∧ z.val.1≤0
                          | _ => z.val.2= -1 ∧ 0≤z.val.1 at hz
                        have hn : ‖z.val‖=1 := by
                          have hle : |z.val.1|≤1 ∧ |z.val.2|≤1 := by
                            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff] using z.property
                          rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                          fin_cases i
                          · rw [hz];norm_num;exact hle.2
                          · rw [hz.1];norm_num;exact hle.1
                          · rw [hz.1];norm_num;exact hle.1
                          · rw [hz];norm_num;exact hle.2
                          · rw [hz.1];norm_num;exact hle.1
                          · rw [hz.1];norm_num;exact hle.1
                        obtain ⟨v,hv⟩ := H.surjective z
                        obtain ⟨p,hp,hparam⟩ := hboundary v (by rw [hv];exact hn)
                        refine ⟨v,⟨p,hp,?_,hparam⟩,hv⟩
                        apply (hsector i p hp).mpr
                        rw [←hparam,hv]
                        exact hz
                  exact ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages⟩
              obtain ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages⟩ := data
              let D := unitInterval × unitInterval
              let ss : Set (ℝ × ℝ) := Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)
              have hsc : Convex ℝ ss := (convex_Icc _ _).prod (convex_Icc _ _)
              have hs0 : ss ∈ 𝓝 (0 : ℝ × ℝ) := by
                have hh := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
                  (show (0 : ℝ × ℝ) ∈ Ioo (-7/8 : ℝ) (1/8) ×ˢ Ioo (-3/8 : ℝ) (5/8) from by norm_num)
                exact Filter.mem_of_superset hh (by rintro z ⟨hz,hw⟩;exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
              have hbottom (u : D) (huy : u.2.val=0) : (G u).val.1= -1 ∧ (G u).val.2=(8*u.1.val-3)/7 := by
                have hf : (u.2.val-7/8,u.1.val-3/8) ∈ frontier ss := by
                  change _ ∈ closure ss ∧ _ ∉ interior ss
                  constructor
                  · rw [(isCompact_Icc.prod isCompact_Icc).isClosed.closure_eq]
                    exact ⟨⟨by linarith [u.2.property.1],by linarith [u.2.property.2]⟩,
                      ⟨by linarith [u.1.property.1],by linarith [u.1.property.2]⟩⟩
                  · intro hi
                    change _ ∈ interior (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)) at hi
                    rw [interior_prod_eq,interior_Icc,interior_Icc] at hi
                    linarith [hi.1.1]
                have hg1 := (gauge_eq_one_iff_mem_frontier hsc hs0).mpr hf
                have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=(7/8 : ℝ) := by
                  rw [huy,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                  norm_num
                  rw [abs_le]
                  constructor <;> linarith [u.1.property.1,u.1.property.2]
                rw [hG,gaugeRescale_def]
                change (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) * _ = _ ∧
                  (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) * _ = _
                rw [hg1,gauge_closedBall (by norm_num : 0≤(1:ℝ)),div_one,hn,huy]
                constructor <;> ring
              let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph (Homeomorph.refl unitInterval)
              have htrace (r s : Bool) (v : StandardDisk) (hy : (H v).val.2= -1) :
                  (M3 (qFace r s v)).1.val=(if r then 1 else 0) ∧
                  (M3 (qFace r s v)).2.val=(if s then (5-(H v).val.1)/7 else ((H v).val.1+3)/7) := by
                have hny : (M0 (q0 false v)).2.val=0 := by change (M0 (Quotient.mk _ (Sum.inl v))).2.val=0;rw [(hML v).2,hy];norm_num
                have hsy : (M0 (q0 true v)).2.val=0 := by change (M0 (Quotient.mk _ (Sum.inr v))).2.val=0;rw [(hMR v).2,hy];norm_num
                have hn := hbottom (M0 (q0 false v)) hny
                have hs := hbottom (M0 (q0 true v)) hsy
                have hnf := hbottom (flip (M0 (q0 false v))) hny
                have hsf := hbottom (flip (M0 (q0 true v))) hsy
                cases r <;> cases s <;> simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
                · change _=0 ∧ _=((H v).val.1+3)/7
                  rw [(h3L (q0 false v)).1,(h3L (q0 false v)).2,hn.1,hn.2]
                  change _=0 ∧ _=((H v).val.1+3)/7
                  simp only [q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
                  rw [(hML v).1]
                  constructor <;> ring
                · change _=0 ∧ _=(5-(H v).val.1)/7
                  rw [(h3L (q0 true v)).1,(h3L (q0 true v)).2,hs.1,hs.2]
                  simp only [q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
                  rw [(hMR v).1]
                  constructor <;> ring
                · change _=1 ∧ _=((H v).val.1+3)/7
                  rw [(h3R (q0 true v)).1,(h3R (q0 true v)).2]
                  change 1-((G (flip (M0 (q0 true v)))).val.1+1)/4=1 ∧ ((G (flip (M0 (q0 true v)))).val.2+1)/2=((H v).val.1+3)/7
                  rw [hsf.1,hsf.2]
                  change _=1 ∧ ((8*(1-(M0 (Quotient.mk _ (Sum.inr v))).1.val)-3)/7+1)/2=((H v).val.1+3)/7
                  rw [(hMR v).1]
                  constructor <;> ring
                · change _=1 ∧ _=(5-(H v).val.1)/7
                  rw [(h3R (q0 false v)).1,(h3R (q0 false v)).2]
                  change 1-((G (flip (M0 (q0 false v)))).val.1+1)/4=1 ∧ ((G (flip (M0 (q0 false v)))).val.2+1)/2=(5-(H v).val.1)/7
                  rw [hnf.1,hnf.2]
                  change _=1 ∧ ((8*(1-(M0 (Quotient.mk _ (Sum.inl v))).1.val)-3)/7+1)/2=(5-(H v).val.1)/7
                  rw [(hML v).1]
                  constructor <;> ring
              refine ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,?_⟩
              intro k right
              ext z
              constructor
              · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
                let v := diskBoundaryPoint p hp
                have hv : H v ∈ H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                    closedArcSector (![(4 : Fin 6),5,4,5] k) p ∧ v=diskBoundaryPoint p hp} := ⟨v,⟨p,hp,hi,rfl⟩,rfl⟩
                rw [himages] at hv
                have hb : -1≤(H v).val.1 ∧ (H v).val.1≤1 := by
                  have hh : |(H v).val.1|≤1 ∧ |(H v).val.2|≤1 := by
                    simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff] using (H v).property
                  exact abs_le.mp hh.1
                fin_cases k <;> norm_num at hv ⊢
                · obtain ⟨hx,hy⟩ := htrace right false v hv.1
                  simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true] at hx hy
                  rw [hx,hy]
                  norm_num
                  constructor <;> linarith [hb.1,hb.2,hv.2]
                · obtain ⟨hx,hy⟩ := htrace right false v hv.1
                  simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true] at hx hy
                  rw [hx,hy]
                  norm_num
                  constructor <;> linarith [hb.1,hb.2,hv.2]
                · obtain ⟨hx,hy⟩ := htrace right true v hv.1
                  simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true] at hx hy
                  rw [hx,hy]
                  norm_num
                  constructor <;> linarith [hb.1,hb.2,hv.2]
                · obtain ⟨hx,hy⟩ := htrace right true v hv.1
                  simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true] at hx hy
                  rw [hx,hy]
                  norm_num
                  constructor <;> linarith [hb.1,hb.2,hv.2]
              · rintro ⟨hzX,hzL,hzR⟩
                let sheet : Bool := ![false,false,true,true] k
                let x : ℝ := if sheet then 5-7*z.2.val else 7*z.2.val-3
                have hxb : -1≤x ∧ x≤1 := by
                  fin_cases k <;> dsimp [x,sheet] <;> norm_num at hzL hzR ⊢ <;> constructor <;> linarith
                let w : closedBall (0 : ℝ × ℝ) 1 := ⟨(x,-1),by
                  rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
                  exact ⟨hxb,⟨by norm_num,by norm_num⟩⟩⟩
                have hw : w ∈ {z : closedBall (0 : ℝ × ℝ) 1 | match (![ (4 : Fin 6),5,4,5] k).val with
                  | 0 => z.val.1=1 | 1 => z.val.2=1 ∧ 0≤z.val.1 | 2 => z.val.2=1 ∧ z.val.1≤0
                  | 3 => z.val.1= -1 | 4 => z.val.2= -1 ∧ z.val.1≤0 | _ => z.val.2= -1 ∧ 0≤z.val.1} := by
                  fin_cases k <;> dsimp [w,x,sheet] <;> norm_num at hzL hzR ⊢ <;> linarith
                rw [←himages] at hw
                obtain ⟨v,⟨p,hp,hi,hparam⟩,hv⟩ := hw
                subst v
                let q := qFace right sheet (diskBoundaryPoint p hp)
                refine ⟨q,⟨p,hp,hi,rfl⟩,?_⟩
                have hyH : (H (diskBoundaryPoint p hp)).val.2= -1 := by rw [hv]
                obtain ⟨hx,hy⟩ := htrace right sheet (diskBoundaryPoint p hp) hyH
                apply Prod.ext <;> apply Subtype.ext
                · exact hx.trans hzX.symm
                · rw [hy,hv]
                  change (if sheet then (5-x)/7 else (x+3)/7)=z.2.val
                  cases hs : sheet <;> simp only [x,hs,Bool.false_eq_true,ite_false,ite_true] <;> ring
          obtain ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,hEight⟩ := data
          have hNorthTwo :
                M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
                  closedArcSector (2 : Fin 6) p ∧ q=Quotient.mk (Relation.EqvGen.setoid R1)
                    (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))))} =
                {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/3 : ℝ)≤z.1.val ∧ z.1.val≤1/2}
              := by
            let D := unitInterval × unitInterval
            let ss : Set (ℝ × ℝ) := Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)
            have hsc : Convex ℝ ss := (convex_Icc _ _).prod (convex_Icc _ _)
            have hs0 : ss ∈ 𝓝 (0 : ℝ × ℝ) := by
              have hh := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
                (show (0 : ℝ × ℝ) ∈ Ioo (-7/8 : ℝ) (1/8) ×ˢ Ioo (-3/8 : ℝ) (5/8) from by norm_num)
              exact Filter.mem_of_superset hh (by rintro z ⟨hz,hw⟩;exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
            have hsegment (u : D) (huy : u.2.val=1) (hu0 : 0≤u.1.val) (hu1 : u.1.val≤1/4) :
                (G u).val.1=1/(8*(3/8-u.1.val)) ∧ (G u).val.2= -1 := by
              have hd : 0<(3/8 : ℝ)-u.1.val := by linarith
              have hf : (u.2.val-7/8,u.1.val-3/8) ∈ frontier ss := by
                change _ ∈ closure ss ∧ _ ∉ interior ss
                constructor
                · rw [(isCompact_Icc.prod isCompact_Icc).isClosed.closure_eq]
                  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
                · intro hi
                  change _ ∈ interior (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)) at hi
                  rw [interior_prod_eq,interior_Icc,interior_Icc] at hi
                  linarith [hi.1.2]
              have hg1 := (gauge_eq_one_iff_mem_frontier hsc hs0).mpr hf
              have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=3/8-u.1.val := by
                rw [huy,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
                norm_num
                rw [abs_of_nonpos (by linarith : u.1.val-3/8≤0),max_eq_right (by linarith)]
                ring
              rw [hG,gaugeRescale_def]
              change (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) * _ = _ ∧
                (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) * _ = _
              rw [hg1,gauge_closedBall (by norm_num : 0≤(1:ℝ)),div_one,hn,huy]
              have h8 : (3 : ℝ)-u.1.val*8≠0 := by linarith
              constructor
              · field_simp [hd.ne'];ring
              · have he : u.1.val-3/8= -(3/8-u.1.val) := by ring
                rw [he,mul_neg,one_div_mul_eq_div,div_self hd.ne']
            have hpoint (p : Sphere) (hp : height p=0) (hi : closedArcSector (2 : Fin 6) p) :
                let v := diskBoundaryPoint p hp
                let u := M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))
                let z := M3 (Quotient.mk (Relation.EqvGen.setoid R1) (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))))
                z.1.val=(1/(8*(3/8-u.1.val))+1)/4 ∧ z.2.val=0 ∧
                0≤u.1.val ∧ u.1.val≤1/4 := by
              dsimp only
              let v := diskBoundaryPoint p hp
              let u := M0 (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))
              have hv : H v ∈ H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                  closedArcSector (2 : Fin 6) p ∧ v=diskBoundaryPoint p hp} := ⟨v,⟨p,hp,hi,rfl⟩,rfl⟩
              rw [himages] at hv
              change (H v).val.2=1 ∧ (H v).val.1≤0 at hv
              have hu0 : 0≤u.1.val := u.1.property.1
              have hu1 : u.1.val≤1/4 := by dsimp [u];rw [(hML v).1];linarith [hv.2]
              have huy : u.2.val=1 := by dsimp [u];rw [(hML v).2,hv.1];norm_num
              have hg := hsegment u huy hu0 hu1
              have hc := h3L (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl v))
              change _=_ ∧ _=0 ∧ 0≤u.1.val ∧ u.1.val≤1/4
              rw [hc.1,hc.2]
              change ((G u).val.1+1)/4=_ ∧ ((G u).val.2+1)/2=0 ∧ _
              rw [hg.1,hg.2]
              exact ⟨rfl,by norm_num,hu0,hu1⟩
            ext z
            constructor
            · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
              obtain ⟨hx,hy,hu0,hu1⟩ := hpoint p hp hi
              refine ⟨hy,?_,?_⟩
              · rw [hx]
                have hd : 0<(3/8 : ℝ)-(M0 (Quotient.mk _ (Sum.inl (diskBoundaryPoint p hp)))).1.val := by linarith
                have hf : (1/3 : ℝ)≤1/(8*(3/8-(M0 (Quotient.mk _ (Sum.inl (diskBoundaryPoint p hp)))).1.val)) :=
                  (le_div_iff₀ (mul_pos (by norm_num) hd)).mpr (by linarith)
                linarith
              · rw [hx]
                have hd : 0<(3/8 : ℝ)-(M0 (Quotient.mk _ (Sum.inl (diskBoundaryPoint p hp)))).1.val := by linarith
                have hf : 1/(8*(3/8-(M0 (Quotient.mk _ (Sum.inl (diskBoundaryPoint p hp)))).1.val))≤(1:ℝ) :=
                  (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr (by linarith)
                linarith
            · rintro ⟨hzY,hzL,hzR⟩
              let t : ℝ := 4*z.1.val-1
              have ht0 : 0<t := by dsimp [t];linarith
              have htL : (1/3 : ℝ)≤t := by dsimp [t];linarith
              have htR : t≤1 := by dsimp [t];linarith
              let u : ℝ := 3/8-1/(8*t)
              have hu0 : 0≤u := by
                have hf : 1/(8*t)≤(3/8 : ℝ) := (div_le_iff₀ (mul_pos (by norm_num) ht0)).mpr (by linarith)
                dsimp [u];linarith
              have hu1 : u≤1/4 := by
                have hf : (1/8 : ℝ)≤1/(8*t) := (le_div_iff₀ (mul_pos (by norm_num) ht0)).mpr (by linarith)
                dsimp [u];linarith
              let w : closedBall (0 : ℝ × ℝ) 1 := ⟨(4*u-1,1),by
                rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
                exact ⟨⟨by linarith,by linarith⟩,⟨by norm_num,by norm_num⟩⟩⟩
              have hw : w ∈ {z : closedBall (0 : ℝ × ℝ) 1 | z.val.2=1 ∧ z.val.1≤0} := ⟨rfl,by change 4*u-1≤0;linarith⟩
              change w ∈ {z : closedBall (0 : ℝ × ℝ) 1 | match (2 : Fin 6).val with
                | 0 => z.val.1=1 | 1 => z.val.2=1 ∧ 0≤z.val.1 | 2 => z.val.2=1 ∧ z.val.1≤0
                | 3 => z.val.1= -1 | 4 => z.val.2= -1 ∧ z.val.1≤0 | _ => z.val.2= -1 ∧ 0≤z.val.1} at hw
              rw [←himages (2 : Fin 6)] at hw
              obtain ⟨v,⟨p,hp,hi,hparam⟩,hv⟩ := hw
              subst v
              let q := Quotient.mk (Relation.EqvGen.setoid R1) (Sum.inl (Quotient.mk (Relation.EqvGen.setoid R0) (Sum.inl (diskBoundaryPoint p hp))))
              refine ⟨q,⟨p,hp,hi,rfl⟩,?_⟩
              obtain ⟨hx,hy,_,_⟩ := hpoint p hp hi
              have hux : (M0 (Quotient.mk _ (Sum.inl (diskBoundaryPoint p hp)))).1.val=u := by
                rw [(hML _).1,hv]
                change ((4*u-1)+1)/4=u
                ring
              have hf : 1/(8*(3/8-u))=t := by dsimp [u];field_simp [ht0.ne'];ring
              apply Prod.ext <;> apply Subtype.ext
              · change (M3 q).1.val=z.1.val
                rw [hx,hux,hf]
                dsimp [t];ring
              · change (M3 q).2.val=z.2.val
                rw [hy,hzY]
          let D := unitInterval × unitInterval
          let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph (Homeomorph.refl unitInterval)
          have hreflection (s : Bool) (v : StandardDisk) :
              M3 (qFace true s v)=flip (M3 (qFace false s v)) := by
            have hc : (unitInterval.symmHomeomorph (M0 (q0 (!s) v)).1,(M0 (q0 (!s) v)).2)=M0 (q0 s v) := by
              cases s <;> apply Prod.ext <;> apply Subtype.ext
              all_goals simp only [q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
              · change 1-(M0 (Quotient.mk _ (Sum.inr v))).1.val=(M0 (Quotient.mk _ (Sum.inl v))).1.val
                rw [(hMR v).1,(hML v).1] <;> ring
              · rw [(hMR v).2,(hML v).2]
              · change 1-(M0 (Quotient.mk _ (Sum.inl v))).1.val=(M0 (Quotient.mk _ (Sum.inr v))).1.val
                rw [(hML v).1,(hMR v).1] <;> ring
              · rw [(hML v).2,(hMR v).2]
            simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
            apply Prod.ext <;> apply Subtype.ext
            · change (M3 (Quotient.mk _ (Sum.inr (q0 (!s) v)))).1.val=
                1-(M3 (Quotient.mk _ (Sum.inl (q0 s v)))).1.val
              rw [(h3R (q0 (!s) v)).1,(h3L (q0 s v)).1,hc]
            · change (M3 (Quotient.mk _ (Sum.inr (q0 (!s) v)))).2.val=
                (M3 (Quotient.mk _ (Sum.inl (q0 s v)))).2.val
              rw [(h3R (q0 (!s) v)).2,(h3L (q0 s v)).2,hc]
          have hSouthTwo :
                M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
                  closedArcSector (2 : Fin 6) p ∧ q=qFace true false (diskBoundaryPoint p hp)} =
                {z : unitInterval × unitInterval | z.2.val=0 ∧ (1/2 : ℝ)≤z.1.val ∧ z.1.val≤2/3}
              := by
            ext z
            constructor
            · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
              let v := diskBoundaryPoint p hp
              have hn : M3 (qFace false false v) ∈ {z : D | z.2.val=0 ∧ (1/3 : ℝ)≤z.1.val ∧ z.1.val≤1/2} := by
                rw [←hNorthTwo]
                simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
                exact ⟨_,⟨p,hp,hi,rfl⟩,rfl⟩
              rw [hreflection]
              change (M3 (qFace false false v)).2.val=0 ∧
                1/2≤1-(M3 (qFace false false v)).1.val ∧ 1-(M3 (qFace false false v)).1.val≤2/3
              exact ⟨hn.1,by linarith [hn.2.2],by linarith [hn.2.1]⟩
            · rintro ⟨hy,hl,hr⟩
              have hw : flip z ∈ {z : D | z.2.val=0 ∧ (1/3 : ℝ)≤z.1.val ∧ z.1.val≤1/2} :=
                ⟨hy,by change 1/3≤1-z.1.val;linarith,by change 1-z.1.val≤1/2;linarith⟩
              rw [←hNorthTwo] at hw
              obtain ⟨q,⟨p,hp,hi,rfl⟩,hq⟩ := hw
              let v := diskBoundaryPoint p hp
              have hq' : M3 (qFace false false v)=flip z := by
                simpa only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true] using hq
              refine ⟨qFace true false v,⟨p,hp,hi,rfl⟩,?_⟩
              rw [hreflection,hq']
              apply Prod.ext <;> apply Subtype.ext
              · change 1-(1-z.1.val)=z.1.val;ring
              · rfl
          exact ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,hEight,hNorthTwo,hSouthTwo⟩
      obtain ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,hEight,hNorthTwo,hSouthTwo⟩ := data
      let D := unitInterval × unitInterval
      let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph (Homeomorph.refl unitInterval)
      have hreflection (s : Bool) (v : StandardDisk) :
          M3 (qFace true s v)=flip (M3 (qFace false s v)) := by
        have hc : (unitInterval.symmHomeomorph (M0 (q0 (!s) v)).1,(M0 (q0 (!s) v)).2)=M0 (q0 s v) := by
          cases s <;> apply Prod.ext <;> apply Subtype.ext
          all_goals simp only [q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
          · change 1-(M0 (Quotient.mk _ (Sum.inr v))).1.val=(M0 (Quotient.mk _ (Sum.inl v))).1.val
            rw [(hMR v).1,(hML v).1] <;> ring
          · rw [(hMR v).2,(hML v).2]
          · change 1-(M0 (Quotient.mk _ (Sum.inl v))).1.val=(M0 (Quotient.mk _ (Sum.inr v))).1.val
            rw [(hML v).1,(hMR v).1] <;> ring
          · rw [(hML v).2,(hMR v).2]
        simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
        apply Prod.ext <;> apply Subtype.ext
        · change (M3 (Quotient.mk _ (Sum.inr (q0 (!s) v)))).1.val=
            1-(M3 (Quotient.mk _ (Sum.inl (q0 s v)))).1.val
          rw [(h3R (q0 (!s) v)).1,(h3L (q0 s v)).1,hc]
        · change (M3 (Quotient.mk _ (Sum.inr (q0 (!s) v)))).2.val=
            (M3 (Quotient.mk _ (Sum.inl (q0 s v)))).2.val
          rw [(h3R (q0 (!s) v)).2,(h3L (q0 s v)).2,hc]
      let ss : Set (ℝ × ℝ) := Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)
      have hsc : Convex ℝ ss := (convex_Icc _ _).prod (convex_Icc _ _)
      have hs0 : ss ∈ 𝓝 (0 : ℝ × ℝ) := by
        have hh := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
          (show (0 : ℝ × ℝ) ∈ Ioo (-7/8 : ℝ) (1/8) ×ˢ Ioo (-3/8 : ℝ) (5/8) from by norm_num)
        exact Filter.mem_of_superset hh (by rintro z ⟨hz,hw⟩;exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
      have htop (u : D) (huy : u.2.val=1) (hux : (1/2 : ℝ)≤u.1.val) :
          (G u).val.1=1/(8*(u.1.val-3/8)) ∧ (G u).val.2=1 := by
        have hd : 0<u.1.val-(3/8 : ℝ) := by linarith
        have hf : (u.2.val-7/8,u.1.val-3/8) ∈ frontier ss := by
          change _ ∈ closure ss ∧ _ ∉ interior ss
          constructor
          · rw [(isCompact_Icc.prod isCompact_Icc).isClosed.closure_eq]
            exact ⟨⟨by linarith [u.2.property.1],by linarith [u.2.property.2]⟩,
              ⟨by linarith [u.1.property.1],by linarith [u.1.property.2]⟩⟩
          · intro hi
            change _ ∈ interior (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)) at hi
            rw [interior_prod_eq,interior_Icc,interior_Icc] at hi
            linarith [hi.1.2]
        have hg1 := (gauge_eq_one_iff_mem_frontier hsc hs0).mpr hf
        have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=u.1.val-3/8 := by
          rw [huy,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
          norm_num
          rw [abs_of_nonneg hd.le,max_eq_right (by linarith)]
        rw [hG,gaugeRescale_def]
        change (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) * _ = _ ∧
          (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) * _ = _
        rw [hg1,gauge_closedBall (by norm_num : 0≤(1:ℝ)),div_one,hn,huy]
        constructor
        · field_simp [hd.ne'];ring
        · rw [one_div_mul_eq_div,div_self hd.ne']
      have htrace (v : StandardDisk) (hyH : (H v).val.2=1) :
          (M3 (qFace false true v)).1.val=(1/(3-2*(H v).val.1)+1)/4 ∧
          (M3 (qFace false true v)).2.val=1 := by
        let u := M0 (q0 true v)
        have huy : u.2.val=1 := by change (M0 (Quotient.mk _ (Sum.inr v))).2.val=1;rw [(hMR v).2,hyH];norm_num
        have hb : (H v).val.1≤1 := by
          have hh : |(H v).val.1|≤1 ∧ |(H v).val.2|≤1 := by
            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff] using (H v).property
          exact (abs_le.mp hh.1).2
        have hu : (1/2 : ℝ)≤u.1.val := by
          simp only [u,q0,eq_self_iff_true,ite_true]
          rw [(hMR v).1];linarith
        have hg := htop u huy hu
        simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
        rw [(h3L (Quotient.mk _ (Sum.inr v))).1,(h3L (Quotient.mk _ (Sum.inr v))).2]
        change ((G u).val.1+1)/4=_ ∧ ((G u).val.2+1)/2=1
        rw [hg.1,hg.2]
        have hd : 8*(u.1.val-3/8)=3-2*(H v).val.1 := by
          simp only [u,q0,eq_self_iff_true,ite_true]
          rw [(hMR v).1];ring
        rw [hd]
        exact ⟨rfl,by norm_num⟩
      have hLeft (k : Fin 2) :
          M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
            closedArcSector (![(1 : Fin 6),2] k) p ∧ q=qFace false true (diskBoundaryPoint p hp)} =
          {z : D | z.2.val=1 ∧ (![(1/3 : ℝ),3/10] k)≤z.1.val ∧ z.1.val≤(![(1/2 : ℝ),1/3] k)} := by
        ext z
        constructor
        · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
          let v := diskBoundaryPoint p hp
          have hv : H v ∈ H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
            closedArcSector (![(1 : Fin 6),2] k) p ∧ v=diskBoundaryPoint p hp} := ⟨v,⟨p,hp,hi,rfl⟩,rfl⟩
          rw [himages] at hv
          have hb : -1≤(H v).val.1 ∧ (H v).val.1≤1 := by
            have hh : |(H v).val.1|≤1 ∧ |(H v).val.2|≤1 := by
              simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff] using (H v).property
            exact abs_le.mp hh.1
          have hd : 0<3-2*(H v).val.1 := by linarith [hb.2]
          fin_cases k <;> norm_num at hv
          · obtain ⟨hx,hy⟩ := htrace v hv.1
            simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true] at hx hy
            change (M3 (qFace false true v)).2.val=1 ∧ (1/3:ℝ)≤(M3 (qFace false true v)).1.val ∧ (M3 (qFace false true v)).1.val≤1/2
            simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
            rw [hy,hx];norm_num
            constructor
            · have hf : (1/3 : ℝ)≤1/(3-2*(H v).val.1) := (le_div_iff₀ hd).mpr (by linarith [hv.2])
              simp only [one_div] at hf
              linarith
            · have hf : 1/(3-2*(H v).val.1)≤(1:ℝ) := (div_le_iff₀ hd).mpr (by linarith [hb.2])
              simp only [one_div] at hf
              linarith
          · obtain ⟨hx,hy⟩ := htrace v hv.1
            simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true] at hx hy
            change (M3 (qFace false true v)).2.val=1 ∧ (3/10:ℝ)≤(M3 (qFace false true v)).1.val ∧ (M3 (qFace false true v)).1.val≤1/3
            simp only [qFace,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
            rw [hy,hx];norm_num
            constructor
            · have hf : (1/5 : ℝ)≤1/(3-2*(H v).val.1) := (le_div_iff₀ hd).mpr (by linarith [hb.1])
              simp only [one_div] at hf
              linarith
            · have hf : 1/(3-2*(H v).val.1)≤(1/3:ℝ) := (div_le_iff₀ hd).mpr (by linarith [hv.2])
              simp only [one_div] at hf
              linarith
        · rintro ⟨hzY,hzL,hzR⟩
          let t : ℝ := 4*z.1.val-1
          have ht0 : 0<t := by fin_cases k <;> dsimp [t] <;> norm_num at hzL hzR <;> linarith
          have htL : (1/5 : ℝ)≤t := by fin_cases k <;> dsimp [t] <;> norm_num at hzL hzR <;> linarith
          have htR : t≤1 := by fin_cases k <;> dsimp [t] <;> norm_num at hzL hzR <;> linarith
          let x : ℝ := (3-1/t)/2
          have hxL : -1≤x := by
            have hh : 1/t≤(5:ℝ) := (div_le_iff₀ ht0).mpr (by linarith)
            dsimp [x];linarith
          have hxR : x≤1 := by
            have hh : (1:ℝ)≤1/t := (le_div_iff₀ ht0).mpr (by linarith)
            dsimp [x];linarith
          let w : closedBall (0 : ℝ × ℝ) 1 := ⟨(x,1),by
            rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
            exact ⟨⟨hxL,hxR⟩,⟨by norm_num,by norm_num⟩⟩⟩
          have hw : w ∈ {z : closedBall (0 : ℝ × ℝ) 1 | match (![(1 : Fin 6),2] k).val with
            | 0 => z.val.1=1 | 1 => z.val.2=1 ∧ 0≤z.val.1 | 2 => z.val.2=1 ∧ z.val.1≤0
            | 3 => z.val.1= -1 | 4 => z.val.2= -1 ∧ z.val.1≤0 | _ => z.val.2= -1 ∧ 0≤z.val.1} := by
            fin_cases k <;> norm_num at hzL hzR ⊢
            · have hh : 1/t≤(3:ℝ) := (div_le_iff₀ ht0).mpr (by dsimp [t];linarith)
              change 0≤x
              dsimp [x];linarith
            · have hh : (3:ℝ)≤1/t := (le_div_iff₀ ht0).mpr (by dsimp [t];linarith)
              change x≤0
              dsimp [x];linarith
          rw [←himages] at hw
          obtain ⟨v,⟨p,hp,hi,hparam⟩,hv⟩ := hw
          subst v
          let q := qFace false true (diskBoundaryPoint p hp)
          refine ⟨q,⟨p,hp,hi,rfl⟩,?_⟩
          have hyH : (H (diskBoundaryPoint p hp)).val.2=1 := by rw [hv]
          obtain ⟨hx,hy⟩ := htrace (diskBoundaryPoint p hp) hyH
          have hf : 1/(3-2*x)=t := by
            have he : 3-2*x=1/t := by dsimp [x];ring
            rw [he];simp
          apply Prod.ext <;> apply Subtype.ext
          · rw [hx,hv]
            change (1/(3-2*x)+1)/4=z.1.val
            rw [hf];dsimp [t];ring
          · exact hy.trans hzY.symm
      have hTopFour :
            (∀ k : Fin 2, ∀ right : Bool,
              M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
                closedArcSector (![(1 : Fin 6),2] k) p ∧ q=qFace right true (diskBoundaryPoint p hp)} =
              {z : unitInterval × unitInterval | z.2.val=1 ∧
                (if right then 1-(![(1/2 : ℝ),1/3] k) else (![(1/3 : ℝ),3/10] k))≤z.1.val ∧
                z.1.val≤(if right then 1-(![(1/3 : ℝ),3/10] k) else (![(1/2 : ℝ),1/3] k))})
          := by
        intro k r
        cases r
        · simpa only [Bool.false_eq_true,ite_false] using hLeft k
        · ext z
          constructor
          · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
            have hn : M3 (qFace false true (diskBoundaryPoint p hp)) ∈
                {z : D | z.2.val=1 ∧ (![(1/3 : ℝ),3/10] k)≤z.1.val ∧ z.1.val≤(![(1/2 : ℝ),1/3] k)} := by
              rw [←hLeft k]
              exact ⟨_,⟨p,hp,hi,rfl⟩,rfl⟩
            rw [hreflection]
            change _=1 ∧ 1-(![(1/2 : ℝ),1/3] k)≤1-(M3 (qFace false true (diskBoundaryPoint p hp))).1.val ∧
              1-(M3 (qFace false true (diskBoundaryPoint p hp))).1.val≤1-(![(1/3 : ℝ),3/10] k)
            exact ⟨hn.1,by linarith [hn.2.2],by linarith [hn.2.1]⟩
          · rintro ⟨hy,hl,hr⟩
            simp only [eq_self_iff_true,ite_true] at hl hr
            have hw : flip z ∈ {z : D | z.2.val=1 ∧ (![(1/3 : ℝ),3/10] k)≤z.1.val ∧ z.1.val≤(![(1/2 : ℝ),1/3] k)} := by
              refine ⟨hy,?_,?_⟩
              · change (![(1/3 : ℝ),3/10] k)≤1-z.1.val;linarith
              · change 1-z.1.val≤(![(1/2 : ℝ),1/3] k);linarith
            rw [←hLeft k] at hw
            obtain ⟨q,⟨p,hp,hi,rfl⟩,hq⟩ := hw
            refine ⟨qFace true true (diskBoundaryPoint p hp),⟨p,hp,hi,rfl⟩,?_⟩
            rw [hreflection,hq]
            apply Prod.ext <;> apply Subtype.ext
            · change 1-(1-z.1.val)=z.1.val;ring
            · rfl
      exact ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,hEight,hNorthTwo,hSouthTwo,hTopFour⟩
  obtain ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,hEight,hNorthTwo,hSouthTwo,hTopFour⟩ := data
  let D := unitInterval × unitInterval
  let flip : D ≃ₜ D := Homeomorph.prodCongr unitInterval.symmHomeomorph (Homeomorph.refl unitInterval)
  have hreflection (s : Bool) (v : StandardDisk) :
      M3 (qFace true s v)=flip (M3 (qFace false s v)) := by
    have hc : (unitInterval.symmHomeomorph (M0 (q0 (!s) v)).1,(M0 (q0 (!s) v)).2)=M0 (q0 s v) := by
      cases s <;> apply Prod.ext <;> apply Subtype.ext
      all_goals simp only [q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true,Bool.not_false,Bool.not_true]
      · change 1-(M0 (Quotient.mk _ (Sum.inr v))).1.val=(M0 (Quotient.mk _ (Sum.inl v))).1.val
        rw [(hMR v).1,(hML v).1] <;> ring
      · rw [(hMR v).2,(hML v).2]
      · change 1-(M0 (Quotient.mk _ (Sum.inl v))).1.val=(M0 (Quotient.mk _ (Sum.inr v))).1.val
        rw [(hML v).1,(hMR v).1] <;> ring
      · rw [(hML v).2,(hMR v).2]
    simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
    apply Prod.ext <;> apply Subtype.ext
    · change (M3 (Quotient.mk _ (Sum.inr (q0 (!s) v)))).1.val=
        1-(M3 (Quotient.mk _ (Sum.inl (q0 s v)))).1.val
      rw [(h3R (q0 (!s) v)).1,(h3L (q0 s v)).1,hc]
    · change (M3 (Quotient.mk _ (Sum.inr (q0 (!s) v)))).2.val=
        (M3 (Quotient.mk _ (Sum.inl (q0 s v)))).2.val
      rw [(h3R (q0 (!s) v)).2,(h3L (q0 s v)).2,hc]
  let ss : Set (ℝ × ℝ) := Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)
  have hsc : Convex ℝ ss := (convex_Icc _ _).prod (convex_Icc _ _)
  have hs0 : ss ∈ 𝓝 (0 : ℝ × ℝ) := by
    have hh := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      (show (0 : ℝ × ℝ) ∈ Ioo (-7/8 : ℝ) (1/8) ×ˢ Ioo (-3/8 : ℝ) (5/8) from by norm_num)
    exact Filter.mem_of_superset hh (by rintro z ⟨hz,hw⟩;exact ⟨⟨hz.1.le,hz.2.le⟩,⟨hw.1.le,hw.2.le⟩⟩)
  have hvertical (u : D) (hux : u.1.val=0 ∨ u.1.val=1) :
      (G u).val=((u.2.val-7/8)/‖(u.2.val-7/8,u.1.val-3/8)‖,
        (u.1.val-3/8)/‖(u.2.val-7/8,u.1.val-3/8)‖) := by
    have hf : (u.2.val-7/8,u.1.val-3/8) ∈ frontier ss := by
      change _ ∈ closure ss ∧ _ ∉ interior ss
      constructor
      · rw [(isCompact_Icc.prod isCompact_Icc).isClosed.closure_eq]
        exact ⟨⟨by linarith [u.2.property.1],by linarith [u.2.property.2]⟩,
          ⟨by linarith [u.1.property.1],by linarith [u.1.property.2]⟩⟩
      · intro hi
        change _ ∈ interior (Icc (-7/8 : ℝ) (1/8) ×ˢ Icc (-3/8 : ℝ) (5/8)) at hi
        rw [interior_prod_eq,interior_Icc,interior_Icc] at hi
        rcases hux with h|h <;> linarith [hi.2.1,hi.2.2]
    have hg1 := (gauge_eq_one_iff_mem_frontier hsc hs0).mpr hf
    rw [hG,gaugeRescale_def]
    change (gauge ss _ / gauge (closedBall (0 : ℝ × ℝ) 1) _) • _ = _
    rw [hg1,gauge_closedBall (by norm_num : 0≤(1:ℝ)),div_one]
    apply Prod.ext <;> dsimp <;> exact one_div_mul_eq_div _ _
  have hBounds (v : StandardDisk) : -1≤(H v).val.2 ∧ (H v).val.2≤1 := by
    have hh : |(H v).val.1|≤1 ∧ |(H v).val.2|≤1 := by
      simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff] using (H v).property
    exact abs_le.mp hh.2
  have recover (t : ℝ) (hl : -1≤t) (hr : t≤1) :
      ∃ p : Sphere, ∃ hp : height p=0, closedArcSector (3 : Fin 6) p ∧
        (H (diskBoundaryPoint p hp)).val=(-1,t) := by
    let w : closedBall (0 : ℝ × ℝ) 1 := ⟨(-1,t),by
      rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
      exact ⟨⟨by norm_num,by norm_num⟩,⟨hl,hr⟩⟩⟩
    have hw : w ∈ {z : closedBall (0 : ℝ × ℝ) 1 | match (3 : Fin 6).val with
      | 0 => z.val.1=1 | 1 => z.val.2=1 ∧ 0≤z.val.1 | 2 => z.val.2=1 ∧ z.val.1≤0
      | 3 => z.val.1= -1 | 4 => z.val.2= -1 ∧ z.val.1≤0 | _ => z.val.2= -1 ∧ 0≤z.val.1} := rfl
    rw [←himages] at hw
    obtain ⟨v,⟨p,hp,hi,hparam⟩,hv⟩ := hw
    subst v
    exact ⟨p,hp,hi,congrArg Subtype.val hv⟩
  have hNorthHigh (v : StandardDisk) (hxH : (H v).val.1= -1) (ht : 0≤(H v).val.2) :
      (M3 (qFace false false v)).1.val=(H v).val.2/3 ∧ (M3 (qFace false false v)).2.val=0 := by
    let u := M0 (q0 false v)
    have hux : u.1.val=0 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      rw [(hML v).1,hxH];norm_num
    have huy : u.2.val=((H v).val.2+1)/2 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      exact (hML v).2
    have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=(3/8 : ℝ) := by
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hux,huy]
      norm_num
      rw [abs_le]
      constructor <;> linarith [hBounds v |>.2]
    have hgv := hvertical u (Or.inl hux)
    rw [hn] at hgv
    have hgf : (G u).val.1=(4*(H v).val.2-3)/3 := by
      rw [hgv];dsimp;rw [huy];ring
    have hgs : (G u).val.2=(-1 : ℝ) := by
      rw [hgv];dsimp;rw [hux];norm_num
    simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
    rw [(h3L (q0 false v)).1,(h3L (q0 false v)).2]
    change ((G u).val.1+1)/4=_ ∧ ((G u).val.2+1)/2=_
    rw [hgf,hgs]
    constructor <;> ring
  have hNorthLow (v : StandardDisk) (hxH : (H v).val.1= -1) (ht : (H v).val.2≤0) :
      (M3 (qFace false false v)).1.val=0 ∧ (M3 (qFace false false v)).2.val=(-2*(H v).val.2)/(3-4*(H v).val.2) := by
    let u := M0 (q0 false v)
    have hux : u.1.val=0 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      rw [(hML v).1,hxH];norm_num
    have huy : u.2.val=((H v).val.2+1)/2 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      exact (hML v).2
    have hd : 0<3-4*(H v).val.2 := by linarith
    have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=(3-4*(H v).val.2)/8 := by
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hux,huy]
      rw [abs_of_nonpos (by linarith : ((H v).val.2+1)/2-7/8≤0)]
      norm_num
      rw [max_eq_left (by linarith)]
      ring
    have hgv := hvertical u (Or.inl hux)
    rw [hn] at hgv
    have hgf : (G u).val.1= -1 := by
      rw [hgv];dsimp;rw [huy]
      apply (div_eq_iff (div_ne_zero hd.ne' (by norm_num : (8:ℝ)≠0))).mpr
      ring
    have hgs : (G u).val.2=(-3 : ℝ)/(3-4*(H v).val.2) := by
      rw [hgv];dsimp;rw [hux];field_simp [hd.ne'];ring
    simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
    rw [(h3L (q0 false v)).1,(h3L (q0 false v)).2]
    change ((G u).val.1+1)/4=0 ∧ ((G u).val.2+1)/2=_
    rw [hgf,hgs]
    constructor
    · norm_num
    · field_simp [hd.ne'];ring
  have hSouthHigh (v : StandardDisk) (hxH : (H v).val.1= -1) (ht : -1/2≤(H v).val.2) :
      (M3 (qFace false true v)).1.val=(2*(H v).val.2+1)/10 ∧ (M3 (qFace false true v)).2.val=1 := by
    let u := M0 (q0 true v)
    have hux : u.1.val=1 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      rw [(hMR v).1,hxH];norm_num
    have huy : u.2.val=((H v).val.2+1)/2 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      exact (hMR v).2
    have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=(5/8 : ℝ) := by
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hux,huy]
      norm_num
      rw [abs_le]
      constructor <;> linarith [hBounds v |>.2]
    have hgv := hvertical u (Or.inr hux)
    rw [hn] at hgv
    have hgf : (G u).val.1=(4*(H v).val.2-3)/5 := by
      rw [hgv];dsimp;rw [huy];ring
    have hgs : (G u).val.2=(1 : ℝ) := by
      rw [hgv];dsimp;rw [hux];norm_num
    simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
    rw [(h3L (q0 true v)).1,(h3L (q0 true v)).2]
    change ((G u).val.1+1)/4=_ ∧ ((G u).val.2+1)/2=_
    rw [hgf,hgs]
    constructor <;> ring
  have hSouthLow (v : StandardDisk) (hxH : (H v).val.1= -1) (ht : (H v).val.2≤-1/2) :
      (M3 (qFace false true v)).1.val=0 ∧ (M3 (qFace false true v)).2.val=(4-2*(H v).val.2)/(3-4*(H v).val.2) := by
    let u := M0 (q0 true v)
    have hux : u.1.val=1 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      rw [(hMR v).1,hxH];norm_num
    have huy : u.2.val=((H v).val.2+1)/2 := by
      simp only [u,q0,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
      exact (hMR v).2
    have hd : 0<3-4*(H v).val.2 := by linarith
    have hn : ‖(u.2.val-7/8,u.1.val-3/8)‖=(3-4*(H v).val.2)/8 := by
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,hux,huy]
      rw [abs_of_nonpos (by linarith : ((H v).val.2+1)/2-7/8≤0)]
      norm_num
      rw [max_eq_left (by linarith)]
      ring
    have hgv := hvertical u (Or.inr hux)
    rw [hn] at hgv
    have hgf : (G u).val.1= -1 := by
      rw [hgv];dsimp;rw [huy]
      apply (div_eq_iff (div_ne_zero hd.ne' (by norm_num : (8:ℝ)≠0))).mpr
      ring
    have hgs : (G u).val.2=(5 : ℝ)/(3-4*(H v).val.2) := by
      rw [hgv];dsimp;rw [hux];field_simp [hd.ne'];ring
    simp only [qFace,Bool.false_eq_true,eq_self_iff_true,ite_false,ite_true]
    rw [(h3L (q0 true v)).1,(h3L (q0 true v)).2]
    change ((G u).val.1+1)/4=0 ∧ ((G u).val.2+1)/2=_
    rw [hgf,hgs]
    constructor
    · norm_num
    · field_simp [hd.ne'];ring
  have hNorthCorner :
      M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector (3 : Fin 6) p ∧ q=qFace false false (diskBoundaryPoint p hp)} =
      {z : D | (z.2.val=0 ∧ 0≤z.1.val ∧ z.1.val≤1/3) ∨
        (z.1.val=0 ∧ 0≤z.2.val ∧ z.2.val≤2/7)} := by
    ext z
    constructor
    · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
      let v := diskBoundaryPoint p hp
      have hv : H v ∈ H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
          closedArcSector (3 : Fin 6) p ∧ v=diskBoundaryPoint p hp} := ⟨v,⟨p,hp,hi,rfl⟩,rfl⟩
      rw [himages] at hv
      change (H v).val.1= -1 at hv
      have hb := hBounds v
      by_cases ht : 0≤(H v).val.2
      · obtain ⟨hx,hy⟩ := hNorthHigh v hv ht
        left
        exact ⟨hy,by rw [hx];linarith,by rw [hx];linarith [hb.2]⟩
      · have ht' : (H v).val.2≤0 := le_of_not_ge ht
        obtain ⟨hx,hy⟩ := hNorthLow v hv ht'
        have hd : 0<3-4*(H v).val.2 := by linarith
        right
        refine ⟨hx,?_,?_⟩
        · rw [hy];exact (le_div_iff₀ hd).mpr (by linarith)
        · rw [hy];exact (div_le_iff₀ hd).mpr (by linarith [hb.1])
    · rintro (⟨hzY,hzL,hzR⟩|⟨hzX,hzL,hzR⟩)
      · let t : ℝ := 3*z.1.val
        have hl : -1≤t := by dsimp [t];linarith
        have hr : t≤1 := by dsimp [t];linarith
        obtain ⟨p,hp,hi,hv⟩ := recover t hl hr
        let v := diskBoundaryPoint p hp
        have hxH : (H v).val.1= -1 := congrArg Prod.fst hv
        have hyH : (H v).val.2=t := congrArg Prod.snd hv
        obtain ⟨hx,hy⟩ := hNorthHigh v hxH (by rw [hyH];dsimp [t];linarith)
        refine ⟨qFace false false v,⟨p,hp,hi,rfl⟩,?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · rw [hx,hyH];dsimp [t];ring
        · exact hy.trans hzY.symm
      · have hdY : 0<2-4*z.2.val := by linarith
        let t : ℝ := (-3*z.2.val)/(2-4*z.2.val)
        have htL : -1≤t := (le_div_iff₀ hdY).mpr (by linarith)
        have htR : t≤0 := (div_le_iff₀ hdY).mpr (by linarith)
        obtain ⟨p,hp,hi,hv⟩ := recover t htL (htR.trans (by norm_num))
        let v := diskBoundaryPoint p hp
        have hxH : (H v).val.1= -1 := congrArg Prod.fst hv
        have hyH : (H v).val.2=t := congrArg Prod.snd hv
        obtain ⟨hx,hy⟩ := hNorthLow v hxH (by rw [hyH];exact htR)
        have he : t*(2-4*z.2.val)= -3*z.2.val := div_mul_cancel₀ _ hdY.ne'
        have hd : 0<3-4*t := by linarith
        have hf : (-2*t)/(3-4*t)=z.2.val := (div_eq_iff hd.ne').mpr (by nlinarith [he])
        refine ⟨qFace false false v,⟨p,hp,hi,rfl⟩,?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · exact hx.trans hzX.symm
        · rw [hy,hyH,hf]
  have hSouthCorner :
      M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector (3 : Fin 6) p ∧ q=qFace false true (diskBoundaryPoint p hp)} =
      {z : D | (z.2.val=1 ∧ 0≤z.1.val ∧ z.1.val≤3/10) ∨
        (z.1.val=0 ∧ 6/7≤z.2.val ∧ z.2.val≤1)} := by
    ext z
    constructor
    · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
      let v := diskBoundaryPoint p hp
      have hv : H v ∈ H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
          closedArcSector (3 : Fin 6) p ∧ v=diskBoundaryPoint p hp} := ⟨v,⟨p,hp,hi,rfl⟩,rfl⟩
      rw [himages] at hv
      change (H v).val.1= -1 at hv
      have hb := hBounds v
      by_cases ht : (-1/2 : ℝ)≤(H v).val.2
      · obtain ⟨hx,hy⟩ := hSouthHigh v hv ht
        left
        exact ⟨hy,by rw [hx];linarith,by rw [hx];linarith [hb.2]⟩
      · have ht' : (H v).val.2≤(-1/2 : ℝ) := le_of_not_ge ht
        obtain ⟨hx,hy⟩ := hSouthLow v hv ht'
        have hd : 0<3-4*(H v).val.2 := by linarith
        right
        refine ⟨hx,?_,?_⟩
        · rw [hy];exact (le_div_iff₀ hd).mpr (by linarith [hb.1])
        · rw [hy];exact (div_le_iff₀ hd).mpr (by linarith)
    · rintro (⟨hzY,hzL,hzR⟩|⟨hzX,hzL,hzR⟩)
      · let t : ℝ := 5*z.1.val-1/2
        have hl : -1≤t := by dsimp [t];linarith
        have hr : t≤1 := by dsimp [t];linarith
        obtain ⟨p,hp,hi,hv⟩ := recover t hl hr
        let v := diskBoundaryPoint p hp
        have hxH : (H v).val.1= -1 := congrArg Prod.fst hv
        have hyH : (H v).val.2=t := congrArg Prod.snd hv
        obtain ⟨hx,hy⟩ := hSouthHigh v hxH (by rw [hyH];dsimp [t];linarith)
        refine ⟨qFace false true v,⟨p,hp,hi,rfl⟩,?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · rw [hx,hyH];dsimp [t];ring
        · exact hy.trans hzY.symm
      · have hdY : 0<4*z.2.val-2 := by linarith
        let t : ℝ := (3*z.2.val-4)/(4*z.2.val-2)
        have htL : -1≤t := (le_div_iff₀ hdY).mpr (by linarith)
        have htR : t≤(-1/2 : ℝ) := (div_le_iff₀ hdY).mpr (by linarith)
        obtain ⟨p,hp,hi,hv⟩ := recover t htL (htR.trans (by norm_num))
        let v := diskBoundaryPoint p hp
        have hxH : (H v).val.1= -1 := congrArg Prod.fst hv
        have hyH : (H v).val.2=t := congrArg Prod.snd hv
        obtain ⟨hx,hy⟩ := hSouthLow v hxH (by rw [hyH];exact htR)
        have he : t*(4*z.2.val-2)=3*z.2.val-4 := div_mul_cancel₀ _ hdY.ne'
        have hd : 0<3-4*t := by linarith
        have hf : (4-2*t)/(3-4*t)=z.2.val := (div_eq_iff hd.ne').mpr (by nlinarith [he])
        refine ⟨qFace false true v,⟨p,hp,hi,rfl⟩,?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · exact hx.trans hzX.symm
        · rw [hy,hyH,hf]
  have hLeftCorner (sheet : Bool) :
      let width : ℝ := if sheet then 3/10 else 1/3
      let flat : ℝ := if sheet then 1 else 0
      let lower : ℝ := if sheet then 6/7 else 0
      let upper : ℝ := if sheet then 1 else 2/7
      M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector (3 : Fin 6) p ∧ q=qFace false sheet (diskBoundaryPoint p hp)} =
      {z : D | (z.2.val=flat ∧ 0≤z.1.val ∧ z.1.val≤width) ∨
        (z.1.val=0 ∧ lower≤z.2.val ∧ z.2.val≤upper)} := by
    cases sheet
    · simpa only [Bool.false_eq_true,ite_false] using hNorthCorner
    · simpa only [eq_self_iff_true,ite_true] using hSouthCorner
  have hCorners :
        (∀ right sheet : Bool,
          let width : ℝ := if sheet then 3/10 else 1/3
          let flat : ℝ := if sheet then 1 else 0
          let lower : ℝ := if sheet then 6/7 else 0
          let upper : ℝ := if sheet then 1 else 2/7
          M3 '' {q | ∃ p : Sphere, ∃ hp : height p=0,
            closedArcSector (3 : Fin 6) p ∧ q=qFace right sheet (diskBoundaryPoint p hp)} =
          {z : unitInterval × unitInterval |
            (z.2.val=flat ∧ (if right then 1-width else 0)≤z.1.val ∧
              z.1.val≤(if right then 1 else width)) ∨
            (z.1.val=(if right then 1 else 0) ∧ lower≤z.2.val ∧ z.2.val≤upper)})
      := by
    intro right sheet
    dsimp only
    cases right
    · simpa only [Bool.false_eq_true,ite_false] using hLeftCorner sheet
    · ext z
      constructor
      · rintro ⟨q,⟨p,hp,hi,rfl⟩,rfl⟩
        have hn : M3 (qFace false sheet (diskBoundaryPoint p hp)) ∈
            {z : D | (z.2.val=(if sheet then 1 else 0) ∧ 0≤z.1.val ∧ z.1.val≤(if sheet then 3/10 else 1/3)) ∨
              (z.1.val=0 ∧ (if sheet then 6/7 else 0)≤z.2.val ∧ z.2.val≤(if sheet then 1 else 2/7))} := by
          rw [←hLeftCorner sheet]
          exact ⟨_,⟨p,hp,hi,rfl⟩,rfl⟩
        rw [hreflection]
        rcases hn with ⟨hy,hl,hr⟩|⟨hx,hl,hr⟩
        · left
          change _=(if sheet then 1 else 0) ∧ 1-(if sheet then 3/10 else 1/3)≤1-(M3 (qFace false sheet (diskBoundaryPoint p hp))).1.val ∧
            1-(M3 (qFace false sheet (diskBoundaryPoint p hp))).1.val≤1
          exact ⟨hy,by linarith,by linarith⟩
        · right
          change 1-(M3 (qFace false sheet (diskBoundaryPoint p hp))).1.val=1 ∧ _
          exact ⟨by rw [hx];norm_num,hl,hr⟩
      · rintro (⟨hy,hl,hr⟩|⟨hx,hl,hr⟩)
        · have hw : flip z ∈ {z : D | (z.2.val=(if sheet then 1 else 0) ∧ 0≤z.1.val ∧ z.1.val≤(if sheet then 3/10 else 1/3)) ∨
              (z.1.val=0 ∧ (if sheet then 6/7 else 0)≤z.2.val ∧ z.2.val≤(if sheet then 1 else 2/7))} := by
            left
            refine ⟨hy,?_,?_⟩
            · change 0≤1-z.1.val;simp only [eq_self_iff_true,ite_true] at hr;linarith
            · change 1-z.1.val≤(if sheet then 3/10 else 1/3);simp only [eq_self_iff_true,ite_true] at hl;linarith
          rw [←hLeftCorner sheet] at hw
          obtain ⟨q,⟨p,hp,hi,rfl⟩,hq⟩ := hw
          refine ⟨qFace true sheet (diskBoundaryPoint p hp),⟨p,hp,hi,rfl⟩,?_⟩
          rw [hreflection,hq]
          apply Prod.ext <;> apply Subtype.ext
          · change 1-(1-z.1.val)=z.1.val;ring
          · rfl
        · have hw : flip z ∈ {z : D | (z.2.val=(if sheet then 1 else 0) ∧ 0≤z.1.val ∧ z.1.val≤(if sheet then 3/10 else 1/3)) ∨
              (z.1.val=0 ∧ (if sheet then 6/7 else 0)≤z.2.val ∧ z.2.val≤(if sheet then 1 else 2/7))} := by
            right
            refine ⟨?_,hl,hr⟩
            change 1-z.1.val=0
            simp only [eq_self_iff_true,ite_true] at hx
            linarith
          rw [←hLeftCorner sheet] at hw
          obtain ⟨q,⟨p,hp,hi,rfl⟩,hq⟩ := hw
          refine ⟨qFace true sheet (diskBoundaryPoint p hp),⟨p,hp,hi,rfl⟩,?_⟩
          rw [hreflection,hq]
          apply Prod.ext <;> apply Subtype.ext
          · change 1-(1-z.1.val)=z.1.val;ring
          · rfl
  exact ⟨L,H,M0,hL,hH,hML,hMR,G,hG,M3,h3L,h3R,himages,hEight,hNorthTwo,hSouthTwo,hTopFour,hCorners⟩
end AlternatingSphereCover
