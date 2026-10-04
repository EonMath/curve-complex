import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTranslatedCapTrackAttachment
namespace CurveComplex
open Set Topology Schoenflies
/-- Attach a genuine cap on the translated whole curve, including the strict
open neighborhood needed to transfer actual transverse crossing charts. -/
theorem source_translated_cap_attaches_with_open_neighborhood
    {S : Type} [TopologicalSpace S] [T2Space S]
    (d : Curve S) (E : OpenPartialHomeomorph S Plane)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (f g : C(Interval,S))
    (N M : Interval × Set.Icc (-1:ℝ) 1 → S)
    (θf θg : Interval) (ηf ηg α β : ℝ)
    (hN : ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1), |(u:ℝ)-(θf:ℝ)|<ηf →
      N (u,w) ∈ E.source ∧ E (N (u,w))=Plane.mk (α*(w:ℝ)) (E (f u) 1))
    (hM : ∀ (u : Interval) (w : Set.Icc (-1:ℝ) 1), |(u:ℝ)-(θg:ℝ)|<ηg →
      M (u,w) ∈ E.source ∧ E (M (u,w))=Plane.mk (E (g u) 0) (β*(w:ℝ)))
    (u t : Interval) (hu : |(u:ℝ)-(θf:ℝ)|<ηf) (ht : |(t:ℝ)-(θg:ℝ)|<ηg)
    (w z : Set.Icc (-1:ℝ) 1)
    (hhf : 0<E (f u) 1 ∧ E (f u) 1≤1/8)
    (hhg : 0<E (g t) 0 ∧ E (g t) 0≤1/8)
    (hv : ‖Plane.mk (α*(w:ℝ)) (β*(z:ℝ))‖ < min (E (f u) 1) (E (g t) 0)/4)
    (hd : ∀ x ∈ E.source, ‖E x-Plane.mk (α*(w:ℝ)) (β*(z:ℝ))‖≤1/4 →
      (x ∈ d.image ↔
        (E x 0=α*(w:ℝ) ∧ β*(z:ℝ)≤E x 1) ∨
        (α*(w:ℝ)≤E x 0 ∧ E x 1=β*(z:ℝ)))) :
    ∃ C : C(Interval,S), IsEmbedding C ∧ Set.range C ⊆ E.source ∩ d.image ∧
      C 0=N (u,w) ∧ C 1=M (t,z) ∧
      (∀ x ∈ Set.range C, ‖E x-Plane.mk (α*(w:ℝ)) (β*(z:ℝ))‖<1/4) ∧
      Set.range C=
        {x : S | x ∈ E.source ∧ E x 0=α*(w:ℝ) ∧ β*(z:ℝ)≤E x 1 ∧ E x 1≤E (f u) 1} ∪
        {x : S | x ∈ E.source ∧ α*(w:ℝ)≤E x 0 ∧ E x 0≤E (g t) 0 ∧ E x 1=β*(z:ℝ)} := by
  obtain ⟨C,hC,hCs,hCnorm,hC0,hC1,hCv,hCimage⟩ :=
    source_translated_corner_embedded_cap_with_heights d E hsquare
      (E (f u) 1) (E (g t) 0) hhf hhg
      (Plane.mk (α*(w:ℝ)) (β*(z:ℝ))) hv hd
  have hNport := hN u w hu
  have hMport := hM t z ht
  refine ⟨C,hC,hCs,?_,?_,hCnorm,hCimage⟩
  · exact E.injOn (hCs (Set.mem_range_self 0)).1 hNport.1 (hC0.trans hNport.2.symm)
  · exact E.injOn (hCs (Set.mem_range_self 1)).1 hMport.1 (hC1.trans hMport.2.symm)
end CurveComplex
#print axioms CurveComplex.source_translated_cap_attaches_with_open_neighborhood
