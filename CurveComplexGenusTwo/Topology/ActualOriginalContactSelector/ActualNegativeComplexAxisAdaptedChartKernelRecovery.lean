import Mathlib
namespace CurveComplex.LocalSurgery
open Set Topology

theorem actualNegativeComplexAxisHasAdaptedRealChart
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (C : OpenPartialHomeomorph X ℂ) (p : X) (hp : p∈C.source)
    (hn : ‖C p‖<1) (hneg : (C p).re<0)
    (hA : ∀ x∈C.source,‖C x‖<1 → (x∈A ↔ C x∉Complex.slitPlane)) :
    ∃ K : OpenPartialHomeomorph X (ℝ × ℝ),p∈K.source ∧
      (∀ x∈K.source,x∈A ↔ (K x).1=0) ∧
      (∀ x,(K x).1=(C x).im) ∧
      ∀ x∈K.source,x∈C.source ∧ ‖C x‖<1 ∧ (C x).re<0 := by
  let V : Set ℂ := {z | ‖z‖<1 ∧ z.re<0}
  have hV : IsOpen V := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  let U := C.source∩C ⁻¹' V
  have hU : IsOpen U := C.isOpen_inter_preimage hV
  let H := Complex.equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ)
  let K := (C.restrOpen U hU).trans H.toOpenPartialHomeomorph
  have hKs : K.source=C.source∩U := by
    simp only [K,OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ,inter_univ,OpenPartialHomeomorph.restrOpen_source]
  have hKfirst (x : X) : (K x).1=(C x).im := rfl
  have hsource (x : X) (hx : x∈K.source) :
      x∈C.source ∧ ‖C x‖<1 ∧ (C x).re<0 := by
    rw [hKs] at hx
    exact ⟨hx.1,hx.2.2.1,hx.2.2.2⟩
  refine ⟨K,?_,?_,hKfirst,hsource⟩
  · rw [hKs]
    exact ⟨hp,hp,hn,hneg⟩
  · intro x hx
    obtain ⟨hCx,hunit,hreal⟩ := hsource x hx
    rw [hKfirst,hA x hCx hunit]
    simp [Complex.slitPlane,not_lt.mpr hreal.le]
end CurveComplex.LocalSurgery
