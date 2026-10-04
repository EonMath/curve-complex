import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopPreparedMovieBoundary
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAffineWindowLocalBounds
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLiteralWindowBottomContactFinite
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualOriginalCrossingFreeTailCornerGeometry
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1000000
/-- Bounded SOURCE producer review request. Its input is only original data;
actual produced bottom corners are clear OUTPUTS. This does not assert that
arbitrarily prescribed relative-drawing corners are clear. -/
theorem actual_same_class_loop_prepared_movie_corner_boundary
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (hfinite : (crossings M a b).Finite) (p : S) (hp : p ∈ crossings M a b) :
    ∃ φ : C(Interval,Interval),IsEmbedding φ ∧
      (∀ t,0<(φ t:ℝ) ∧ (φ t:ℝ)<1) ∧
      (∀ t,b.val.map t ∈ crossings M a b → ∃ s,φ s=t) ∧
    ∃ G : C(Interval × Interval,S),
      (∀ t,G (0,t)=b.val.map (φ t)) ∧ IsEmbedding (fun t => G (0,t)) ∧
      (∀ z,G z ∉ (M.cover.branch : Set S)) ∧
      G (0,0) ∉ a.val.image ∧ G (0,1) ∉ a.val.image ∧
      (∀ t,G (1,t) ∉ a.val.image) ∧
      {t : Interval | G (0,t) ∈ a.val.image}.Finite ∧
      {t : Interval | G (1,t) ∈ a.val.image}.Finite ∧
      {τ : Interval | G (τ,0) ∈ a.val.image}.Finite ∧
      {τ : Interval | G (τ,1) ∈ a.val.image}.Finite ∧
    ∃ BC : Interval × Set.Icc (-1:ℝ) 1 → S, ∃ hBC : IsEmbedding BC,
      (∀ z,BC z ∉ (M.cover.branch : Set S)) ∧
      (∀ z,BC z ∈ a.val.image ↔ z.2.val=0) ∧
    ∃ T : Set (Interval × Interval),IsOpen T ∧ G ⁻¹' a.val.image ⊆ T ∧
    ∃ Q : C(T,Set.range BC),(∀ z : T,(Q z).val=G z.val) ∧
    ∃ ψ : C(T,ℝ),
      (∀ z : T,ψ z=((hBC.toHomeomorph.symm (Q z)).2:ℝ)) ∧
      (∀ z : T,0<((hBC.toHomeomorph.symm (Q z)).1:ℝ) ∧
        ((hBC.toHomeomorph.symm (Q z)).1:ℝ)<1 ∧ -1<ψ z ∧ ψ z<1) ∧
      (∀ z : T,ψ z=0 ↔ G z.val ∈ a.val.image) ∧
      (∀ z : T,z.val.1=1 → ψ z≠0) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,hPzero,hPstart,hPouter,hPboundary,hPV,hPinner,hPcontacts,hPnz,
    J₀,J₁,hJU,hcoord,hJbase,hJmarks,hJstart,hJouter,hJcontacts,hJboundary,
    A,B,hAeq,hBeq,hA,hB,hAB,q₀,q₁,hq₀,hq₁,W,hwleft,hwright,hwmiddle,
    hwstart,hwbase,hwmarks,hwbottom,hwtop,hWinner₀,hWinner₁,
    r₀,r₁,hr₀eq,hr₁eq,hr₀,horder,hr₁,φ,hφ,hφeq,G,hGeq,hGmarks,hGtop,hfiniteLeft,hfiniteRight,
    BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hψbounds,hψzero,hψtop⟩ :=
      actual_same_class_loop_patched_central_contact_core M a b ha hclass hfinite p hp
  have hφbounds := actual_affine_window_strict_interior r₀ r₁ hr₀ horder hr₁ φ hφeq
  have hGbottom (t : Interval) : G (0,t)=b.val.map (φ t) := by
    as_aux_lemma =>
      rw [hGeq,hwbottom]
  obtain ⟨hbottomEmbedding,hfiniteBottom⟩ := actual_literal_window_bottom_contact_finite
    M a b K G hzero (hcollision 0) φ hφ hφbounds hGbottom (fun t => hGmarks (0,t)) hfinite
  have hfiniteTop : {t : Interval | G (1,t) ∈ a.val.image}.Finite := by
    as_aux_lemma =>
      apply Set.finite_empty.subset
      intro t ht
      exact False.elim (hGtop (1,t) rfl ht)
  have hr₀ε : r₀<ε := by
    as_aux_lemma =>
      rw [hr₀eq,hAeq]
      exact actual_small_weighted_quarter_margin ε d₀ hε hh₀
  have hεr₁ : 1-ε<r₁ := by
    as_aux_lemma =>
      rw [hr₁eq,hBeq]
      have hh := actual_small_weighted_quarter_margin ε d₁ hε hh₁
      linarith only [hh]
  have hcapture (t : Interval) (ht : b.val.map t ∈ crossings M a b) : ∃ s,φ s=t := by
    as_aux_lemma =>
      have hlo : ε<(t:ℝ) := lt_of_not_ge (fun hh => htails t (Or.inl hh) ht)
      have hhi : (t:ℝ)<1-ε := lt_of_not_ge (fun hh => htails t (Or.inr hh) ht)
      exact actual_affine_window_contains_middle r₀ r₁ ε horder hr₀ε hεr₁ φ hφeq t hlo hhi
  have hcorner := actual_original_crossing_free_tail_corner_geometry
    M a b ε r₀ r₁ htails hr₀ε.le hεr₁.le φ hφeq G hGbottom hGmarks
  exact ⟨φ,hφ,hφbounds,hcapture,G,hGbottom,
    hbottomEmbedding,
    hGmarks,hcorner.1,hcorner.2,(fun t => hGtop (1,t) rfl),hfiniteBottom,hfiniteTop,hfiniteLeft,hfiniteRight,
    BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hψbounds,hψzero,hψtop⟩
end CurveComplex.HyperellipticModel
