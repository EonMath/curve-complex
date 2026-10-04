import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools
import Mathlib.Topology.Order.IntermediateValue
namespace CurveComplex
open Set Topology Schoenflies
set_option maxHeartbeats 5000000

theorem actual_chart_cone_interior_sector
    {S : Type} [TopologicalSpace S]
    (F : OpenPartialHomeomorph S Plane) (D : Set S) (hD : IsClosed D)
    (hregular : D ⊆ closure (interior D))
    (R κ : ℝ) (hR : 0 < R) (hκ : 0 < κ)
    (hTarget : ∀ z : Plane, 0 < z 0 → z 0 < R →
      -κ*z 0 < z 1 → z 1 < κ*z 0 → z ∈ F.target)
    (hFrontier : ∀ z : Plane, 0 < z 0 → z 0 < R →
      -κ*z 0 < z 1 → z 1 < κ*z 0 → (F.symm z ∈ frontier D ↔ z 1 = 0)) :
    ∃ τ : ℝ, (τ = -1 ∨ τ = 1) ∧ ∀ z : Plane,
      0 < z 0 → z 0 < R → -κ*z 0 < z 1 → z 1 < κ*z 0 →
        (F.symm z ∈ interior D ↔ 0 < τ*z 1) := by
  let pos : Set Plane := {z | 0 < z 0 ∧ z 0 < R ∧ 0 < z 1 ∧ z 1 < κ*z 0}
  let neg : Set Plane := {z | 0 < z 0 ∧ z 0 < R ∧ -κ*z 0 < z 1 ∧ z 1 < 0}
  have hPosTarget : pos ⊆ F.target := by
    intro z hz
    exact hTarget z hz.1 hz.2.1 (by have hm := mul_pos hκ hz.1; nlinarith [hz.2.2.1]) hz.2.2.2
  have hNegTarget : neg ⊆ F.target := by
    intro z hz
    exact hTarget z hz.1 hz.2.1 hz.2.2.1 (by have hm := mul_pos hκ hz.1; nlinarith [hz.2.2.2])
  have hPosConn : IsPreconnected pos := by
    have hc : IsPreconnected (Ioo (0:ℝ) R ×ˢ Ioo (0:ℝ) κ) :=
      isPreconnected_Ioo.prod isPreconnected_Ioo
    have hi := hc.image (fun p : ℝ × ℝ => Plane.mk p.1 (p.1*p.2)) (by fun_prop)
    have he : (fun p : ℝ × ℝ => Plane.mk p.1 (p.1*p.2)) ''
        (Ioo (0:ℝ) R ×ˢ Ioo (0:ℝ) κ) = pos := by
      ext z
      constructor
      · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
        change 0 < x ∧ x < R ∧ 0 < x*y ∧ x*y < κ*x
        exact ⟨hx.1,hx.2,mul_pos hx.1 hy.1,by nlinarith [mul_pos hx.1 (sub_pos.mpr hy.2)]⟩
      · intro hz
        refine ⟨(z 0,z 1/z 0),⟨⟨hz.1,hz.2.1⟩,?_,?_⟩,?_⟩
        · exact div_pos hz.2.2.1 hz.1
        · exact (div_lt_iff₀ hz.1).mpr (by have hm := mul_pos hκ hz.1; nlinarith [hz.2.2.2])
        · ext i
          fin_cases i
          · rfl
          · change z 0*(z 1/z 0)=z 1
            field_simp [ne_of_gt hz.1]
    rwa [he] at hi
  have hNegConn : IsPreconnected neg := by
    have hi := hPosConn.image (fun z : Plane => Plane.mk (z 0) (-z 1)) (by fun_prop)
    have he : (fun z : Plane => Plane.mk (z 0) (-z 1)) '' pos = neg := by
      ext z
      constructor
      · rintro ⟨q,hq,rfl⟩
        change 0 < q 0 ∧ q 0 < R ∧ -κ*q 0 < -q 1 ∧ -q 1 < 0
        exact ⟨hq.1,hq.2.1,by linarith [hq.2.2.2],neg_neg_of_pos hq.2.2.1⟩
      · intro hz
        refine ⟨Plane.mk (z 0) (-z 1),⟨hz.1,hz.2.1,neg_pos.mpr hz.2.2.2,by change -z 1 < κ*z 0; linarith [hz.2.2.1]⟩,?_⟩
        ext i
        fin_cases i <;> simp
    rwa [he] at hi
  let P := F.symm '' pos
  let N := F.symm '' neg
  have hPConn : IsPreconnected P := hPosConn.image F.symm (F.symm.continuousOn.mono hPosTarget)
  have hNConn : IsPreconnected N := hNegConn.image F.symm (F.symm.continuousOn.mono hNegTarget)
  have hPAvoid : Disjoint P (frontier D) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    have hy := (hFrontier z hz.1 hz.2.1 (by have hm := mul_pos hκ hz.1; nlinarith [hz.2.2.1]) hz.2.2.2).mp hx
    linarith [hz.2.2.1]
  have hNAvoid : Disjoint N (frontier D) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    have hy := (hFrontier z hz.1 hz.2.1 hz.2.2.1 (by have hm := mul_pos hκ hz.1; nlinarith [hz.2.2.2])).mp hx
    linarith [hz.2.2.2]
  have hClassify (C : Set S) (hc : IsPreconnected C) (ha : Disjoint C (frontier D)) :
      C ⊆ interior D ∨ C ⊆ Dᶜ := by
    have hcover : C ⊆ interior D ∪ Dᶜ := by
      intro x hx
      by_cases hxD : x ∈ D
      · left
        by_contra hn
        exact Set.disjoint_left.mp ha hx (hD.frontier_eq ▸ ⟨hxD,hn⟩)
      · exact Or.inr hxD
    exact hc.subset_or_subset isOpen_interior hD.isOpen_compl
      (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))) hcover
  let ε := κ*R/8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hRect (z : Plane) (hlo : R/4 < z 0) (hhi : z 0 < 3*R/4)
      (hylo : -ε < z 1) (hyhi : z 1 < ε) :
      0 < z 0 ∧ z 0 < R ∧ -κ*z 0 < z 1 ∧ z 1 < κ*z 0 := by
    dsimp [ε] at hylo hyhi
    have hm : κ*(R/4) < κ*z 0 := mul_lt_mul_of_pos_left hlo hκ
    exact ⟨by linarith,by linarith,by nlinarith,by nlinarith⟩
  obtain ⟨σ,hσ,hside⟩ := actual_chart_strip_exterior_half F D hD hregular
    (R/4) (3*R/4) ε (by linarith) hε
    (fun z hz => let hh := hRect z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
      hTarget z hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)
    (fun z hL hR hlo hhi => let hh := hRect z hL hR hlo hhi
      hFrontier z hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)
  let qP := Plane.mk (R/2) (ε/2)
  let qN := Plane.mk (R/2) (-ε/2)
  have hqP : qP ∈ pos := by
    change 0 < R/2 ∧ R/2 < R ∧ 0 < ε/2 ∧ ε/2 < κ*(R/2)
    dsimp [ε]
    have hm := mul_pos hκ hR
    exact ⟨by linarith,by linarith,by positivity,by nlinarith⟩
  have hqN : qN ∈ neg := by
    change 0 < R/2 ∧ R/2 < R ∧ -κ*(R/2) < -ε/2 ∧ -ε/2 < 0
    have hh : ε/2 < κ*(R/2) := hqP.2.2.2
    have hhpos : 0 < ε/2 := hqP.2.2.1
    exact ⟨hqP.1,hqP.2.1,by linarith,by linarith⟩
  have hSideP : F.symm qP ∉ D ↔ 0 < σ*(ε/2) := by
    exact hside qP (by change R/4<R/2; linarith) (by change R/2<3*R/4; linarith)
      (by change -ε<ε/2; linarith) (by change ε/2<ε; linarith)
      (by change ε/2≠0; positivity)
  have hSideN : F.symm qN ∉ D ↔ 0 < σ*(-ε/2) := by
    exact hside qN (by change R/4<R/2; linarith) (by change R/2<3*R/4; linarith)
      (by change -ε< -ε/2; linarith) (by change -ε/2<ε; linarith)
      (by change -ε/2≠0; linarith)
  have hNotBothIn (hp : P ⊆ interior D) (hn : N ⊆ interior D) : False := by
    rcases hσ with rfl|rfl
    · exact (hSideN.mpr (by linarith)) (interior_subset (hn ⟨qN,hqN,rfl⟩))
    · exact (hSideP.mpr (by linarith)) (interior_subset (hp ⟨qP,hqP,rfl⟩))
  have hNotBothOut (hp : P ⊆ Dᶜ) (hn : N ⊆ Dᶜ) : False := by
    rcases hσ with rfl|rfl
    · have hh := hSideP.mp (hp ⟨qP,hqP,rfl⟩)
      linarith
    · have hh := hSideN.mp (hn ⟨qN,hqN,rfl⟩)
      linarith
  rcases hClassify P hPConn hPAvoid with hp|hp <;>
    rcases hClassify N hNConn hNAvoid with hn|hn
  · exact False.elim (hNotBothIn hp hn)
  · refine ⟨1,Or.inr rfl,?_⟩
    intro z hx hxr hlo hhi
    simp only [one_mul]
    constructor
    · intro hz
      by_contra hh
      rcases eq_or_lt_of_le (le_of_not_gt hh) with hy|hy
      · have hf := (hFrontier z hx hxr hlo hhi).mpr hy
        exact (hD.frontier_eq ▸ hf).2 hz
      · exact hn ⟨z,⟨hx,hxr,hlo,hy⟩,rfl⟩ (interior_subset hz)
    · intro hy
      exact hp ⟨z,⟨hx,hxr,hy,hhi⟩,rfl⟩
  · refine ⟨-1,Or.inl rfl,?_⟩
    intro z hx hxr hlo hhi
    simp only [neg_one_mul]
    constructor
    · intro hz
      by_contra hh
      rcases eq_or_lt_of_le (by linarith : 0 ≤ z 1) with hy|hy
      · have hf := (hFrontier z hx hxr hlo hhi).mpr hy.symm
        exact (hD.frontier_eq ▸ hf).2 hz
      · exact hp ⟨z,⟨hx,hxr,hy,hhi⟩,rfl⟩ (interior_subset hz)
    · intro hy
      exact hn ⟨z,⟨hx,hxr,hlo,by linarith⟩,rfl⟩
  · exact False.elim (hNotBothOut hp hn)
end CurveComplex

namespace CurveComplex
open Set Topology Schoenflies

theorem actual_interior_corner_endpoint_family
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : OpenPartialHomeomorph S Plane) (D : Set S) (p : S)
    (hpF : p ∈ F.source) (hFp : F p = 0)
    (R κ ell τ : ℝ) (hR : 0 < R) (hκ : 0 < κ)
    (hell : 0 < ell) (hellR : ell < R) (hτ : τ = -1 ∨ τ = 1)
    (hTarget : ∀ z : Plane, 0 < z 0 → z 0 < R →
      -κ*z 0 < z 1 → z 1 < κ*z 0 → z ∈ F.target)
    (hSector : ∀ z : Plane, 0 < z 0 → z 0 < R →
      -κ*z 0 < z 1 → z 1 < κ*z 0 →
      (F.symm z ∈ interior D ↔ 0 < τ*z 1)) :
    ∃ L : C(Interval,S),
      (∀ t, L t = F.symm (Plane.mk ell (ell*(τ*((κ/4)*t.val))))) ∧
      L 0 = F.symm (Plane.mk ell 0) ∧
      (∀ t, L t ∈ F.source) ∧
      ∀ t : Interval, 0 < t.val →
        ∃ f : C(Interval,S), IsEmbedding f ∧ f 0 = p ∧ f 1 = L t ∧
          range f ⊆ F.source ∧ range f \ {p} ⊆ interior D ∧
          (∀ s : Interval, 0 < s.val → 0 < F (f s) 0 ∧ F (f s) 0 < R ∧
            -κ*F (f s) 0 < F (f s) 1 ∧ F (f s) 1 < κ*F (f s) 0) ∧
          ∀ s, F (f s) = Plane.mk (ell*s.val) ((ell*s.val)*(τ*((κ/4)*t.val))) := by
  classical
  let q (t s : Interval) : Plane :=
    Plane.mk (ell*s.val) ((ell*s.val)*(τ*((κ/4)*t.val)))
  have hcone (t s : Interval) (hs : 0 < s.val) :
      0 < (q t s) 0 ∧ (q t s) 0 < R ∧
      -κ*(q t s) 0 < (q t s) 1 ∧ (q t s) 1 < κ*(q t s) 0 := by
    have hx : 0 < ell*s.val := mul_pos hell hs
    have hxR : ell*s.val < R := lt_of_le_of_lt
      (mul_le_of_le_one_right hell.le s.property.2) hellR
    have hh : 0 ≤ (κ/4)*t.val ∧ (κ/4)*t.val < κ := by
      constructor
      · exact mul_nonneg (by positivity) t.property.1
      · nlinarith [t.property.2]
    have hhl : -κ < τ*((κ/4)*t.val) ∧ τ*((κ/4)*t.val) < κ := by
      rcases hτ with rfl|rfl <;> simp only [neg_one_mul,one_mul] <;> constructor <;> linarith
    change 0 < ell*s.val ∧ ell*s.val < R ∧
      -κ*(ell*s.val) < (ell*s.val)*(τ*((κ/4)*t.val)) ∧
      (ell*s.val)*(τ*((κ/4)*t.val)) < κ*(ell*s.val)
    exact ⟨hx,hxR,by nlinarith [mul_pos hx (sub_pos.mpr hhl.1)],
      by nlinarith [mul_pos hx (sub_pos.mpr hhl.2)]⟩
  have hq0 (t : Interval) : q t 0 = (0:Plane) := by
    ext i
    fin_cases i <;> simp [q]
  have htarget (t s : Interval) : q t s ∈ F.target := by
    by_cases hs : s.val = 0
    · have hs0 : s = 0 := Subtype.ext hs
      rw [hs0,hq0,← hFp]
      exact F.map_source hpF
    · have hh := hcone t s (lt_of_le_of_ne s.property.1 (Ne.symm hs))
      exact hTarget (q t s) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  let L : C(Interval,S) := ⟨fun t => F.symm (q t 1),
    F.symm.continuousOn.comp_continuous (by dsimp [q]; fun_prop) (fun t => htarget t 1)⟩
  refine ⟨L,?_,?_,fun t => F.map_target (htarget t 1),?_⟩
  · intro t
    simp [L,q]
  · simp [L,q]
  · intro t ht
    let f : C(Interval,S) := ⟨fun s => F.symm (q t s),
      F.symm.continuousOn.comp_continuous (by dsimp [q]; fun_prop) (htarget t)⟩
    have hfcoord (s : Interval) : F (f s) = q t s := F.right_inv (htarget t s)
    have hfi : Function.Injective f := by
      intro s u he
      have hh := congrArg (fun x : S => F x 0) he
      rw [hfcoord,hfcoord] at hh
      change ell*s.val=ell*u.val at hh
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hell) hh)
    have hf0 : f 0 = p := by
      change F.symm (q t 0)=p
      rw [hq0,← hFp,F.left_inv hpF]
    refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,hf0,rfl,
      (by rintro x ⟨s,rfl⟩; exact F.map_target (htarget t s)),?_,?_,hfcoord⟩
    swap
    · intro s hs
      rw [hfcoord]
      exact hcone t s hs
    rintro x ⟨⟨s,rfl⟩,hnp⟩
    have hs0 : s ≠ 0 := by intro he; subst s; exact hnp (Set.mem_singleton_iff.mpr hf0)
    have hs : 0 < s.val := lt_of_le_of_ne s.property.1
      (by intro he; exact hs0 (Subtype.ext he.symm))
    have hc := hcone t s hs
    apply (hSector (q t s) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2).mpr
    change 0 < τ*((ell*s.val)*(τ*((κ/4)*t.val)))
    have hh := mul_pos (mul_pos hell hs) (mul_pos (by positivity : 0 < κ/4) ht)
    rcases hτ with rfl|rfl <;> simpa using hh
end CurveComplex
