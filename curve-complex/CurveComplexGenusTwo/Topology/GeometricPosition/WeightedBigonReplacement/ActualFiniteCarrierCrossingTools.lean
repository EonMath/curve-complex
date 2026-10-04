import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualEmbeddedLocalLineTools
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
open Set Topology
namespace CurveComplex

/-- The crossing at a real finite-carrier piece is inherited by the actual
simple replacement. Other pieces and the retained arc are removed by closed
set separation, and embedded-arc geometry derives the missing trace equality. -/
theorem actual_finite_carrier_replacement_crossing
    {S J : Type*} [TopologicalSpace S] [T2Space S] [Fintype J] [DecidableEq J]
    (f : C(Interval,S)) (hf : Topology.IsEmbedding f) (c d : Curve S)
    (R : Set S) (hR : IsClosed R) (hc : c.image = Set.range f ∪ R)
    (A : J → Set S) (hA : ∀ j, IsClosed (A j)) (hcover : Set.range f ⊆ ⋃ j,A j)
    (p : S) (hp : p ∈ Set.range f ∩ d.image) (hpR : p ∉ R)
    (hends : f 0 ∉ d.image ∧ f 1 ∉ d.image)
    (i : J) (hpi : p ∈ A i) (hunique : ∀ j, j ≠ i → p ∉ A j)
    (E : OpenPartialHomeomorph S (ℝ × ℝ)) (hpE : p ∈ E.source)
    (t α k : ℝ)
    (hline : ∀ x ∈ A i ∩ E.source, (E x).2 = t)
    (hdaxis : ∀ x ∈ E.source, x ∈ d.image ↔ (E x).1 = α+k*((E x).2-t)) :
    CrossesAt c d p := by
  classical
  let other := ⋃ j : {j : J // j ≠ i}, A j.val
  have hOther : IsClosed other := isClosed_iUnion_of_finite (fun j => hA j.val)
  let O := Rᶜ ∩ otherᶜ
  have hO : IsOpen O := hR.isOpen_compl.inter hOther.isOpen_compl
  have hpO : p ∈ O := by
    refine ⟨hpR,?_⟩
    intro hpOther
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hpOther
    exact hunique j.val j.property hj
  let E' := E.restrOpen O hO
  have hpE' : p ∈ E'.source := ⟨hpE,hpO⟩
  have hline' : ∀ x ∈ Set.range f ∩ E'.source, (E' x).2 = t := by
    rintro x ⟨hxf,hxE⟩
    have hxO : x ∈ O := hxE.2
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hcover hxf)
    by_cases hji : j = i
    · subst j
      exact hline x ⟨hj,hxE.1⟩
    · exact False.elim (hxO.2 (Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩))
  obtain ⟨s,hs⟩ := hp.1
  have hs0 : 0 < s.val := by
    have hsne : s ≠ 0 := by intro he; subst s; exact hends.1 (hs ▸ hp.2)
    exact lt_of_le_of_ne s.property.1 (by intro he; apply hsne; apply Subtype.ext; exact he.symm)
  have hs1 : s.val < 1 := by
    have hsne : s ≠ 1 := by intro he; subst s; exact hends.2 (hs ▸ hp.2)
    exact lt_of_le_of_ne s.property.2 (by intro he; apply hsne; apply Subtype.ext; exact he)
  obtain ⟨ε,hε,hεtarget,htrace⟩ := actual_embedded_arc_local_chart_horizontal_trace
    f hf s hs0 hs1 E' (hs.symm ▸ hpE') t hline'
  rw [hs] at hεtarget htrace
  let W := Metric.ball (E' p) ε
  let G := E'.restrOpen (E'.source ∩ E' ⁻¹' W) (E'.isOpen_inter_preimage Metric.isOpen_ball)
  have hpG : p ∈ G.source := ⟨hpE',hpE',by simp [W,hε]⟩
  have haxes : ∀ x ∈ G.source,
      (x ∈ c.image ↔ (G x).2 = t) ∧
      (x ∈ d.image ↔ (G x).1 = α+k*((G x).2-t)) := by
    intro x hx
    have hxE' : x ∈ E'.source := hx.1
    have hdist : dist (E' x) (E' p) < ε := hx.2.2
    have hxR : x ∉ R := hxE'.2.1
    constructor
    · rw [hc]
      simpa only [G,OpenPartialHomeomorph.coe_restrOpen,Set.mem_union,hxR,or_false] using htrace x hxE' hdist
    · exact hdaxis x hxE'.1
  let shear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toFun := fun q => (q.2-t,q.1-α-k*(q.2-t))
    invFun := fun q => (q.2+α+k*q.1,q.1+t)
    left_inv := by intro q; ext <;> dsimp <;> ring
    right_inv := by intro q; ext <;> dsimp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let H := G.toHomeomorphSourceTarget.trans (shear.image G.target)
  have hpt : (G p).2 = t := (haxes p hpG).1.mp (hc.symm ▸ Or.inl hp.1)
  have hpd : (G p).1 = α+k*((G p).2-t) := (haxes p hpG).2.mp hp.2
  refine ⟨G.source,shear '' G.target,hpG,H,G.open_source,
    shear.isOpenMap _ G.open_target,?_,?_⟩
  · change shear (G p) = (0,0)
    ext <;> dsimp [shear] <;> rw [hpt] <;> simp_all
  · intro x hx
    change (x ∈ c.image ↔ (shear (G x)).1 = 0) ∧
      (x ∈ d.image ↔ (shear (G x)).2 = 0)
    dsimp [shear]
    constructor
    · exact (haxes x hx).1.trans sub_eq_zero.symm
    · rw [(haxes x hx).2]
      constructor <;> intro he <;> linarith

theorem actual_retained_replacement_crossing
    {S : Type*} [TopologicalSpace S]
    (a a' b : Curve S) (A B R : Set S) (hA : IsClosed A) (hB : IsClosed B)
    (ha : a.image = A ∪ R) (ha' : a'.image = B ∪ R)
    (p : S) (hp : p ∈ R ∩ b.image) (hpA : p ∉ A) (hpB : p ∉ B)
    (hc : CrossesAt a b p) : CrossesAt a' b p := by
  obtain ⟨U,V,hpU,h,hU,hV,hzero,haxes⟩ := hc
  let O := Aᶜ ∩ Bᶜ
  have hO : IsOpen O := hA.isOpen_compl.inter hB.isOpen_compl
  let W := U ∩ O
  let d : W → U := fun x => ⟨x.val,x.property.1⟩
  have hd : IsEmbedding d := IsEmbedding.of_comp (by fun_prop)
    continuous_subtype_val (by
      change IsEmbedding (fun x : W => x.val)
      exact IsEmbedding.subtypeVal)
  let f : W → ℝ × ℝ := fun x => ((h (d x) : V) : ℝ × ℝ)
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp (h.isEmbedding.comp hd)
  have hdopen : IsOpenMap d := (hU.inter hO).isOpenMap_subtype_val.subtype_mk
    (fun x : W => x.property.1)
  have hfopen : IsOpenMap f := hV.isOpenMap_subtype_val.comp (h.isOpenMap.comp hdopen)
  have hpW : p ∈ W := ⟨hpU,hpA,hpB⟩
  refine ⟨W,Set.range f,hpW,hf.toHomeomorph,hU.inter hO,?_,hzero,?_⟩
  · simpa only [Set.image_univ] using hfopen Set.univ isOpen_univ
  · intro x hx
    change (x ∈ a'.image ↔ (f ⟨x,hx⟩).1 = 0) ∧
      (x ∈ b.image ↔ (f ⟨x,hx⟩).2 = 0)
    obtain ⟨hax,hbx⟩ := haxes x hx.1
    have heq : x ∈ a.image ↔ x ∈ a'.image := by
      rw [ha,ha']
      have hxa : x ∉ A := hx.2.1
      have hxb : x ∉ B := hx.2.2
      simp only [Set.mem_union,hxa,hxb,false_or]
    exact ⟨heq.symm.trans hax,hbx⟩

end CurveComplex
