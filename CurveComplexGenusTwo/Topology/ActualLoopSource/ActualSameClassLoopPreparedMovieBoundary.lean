import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopPatchedCentralContactCore
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- ORIGINAL same-class loop source produces an actual prepared filling movie:
ALL four boundary contact sets are finite, the bottom is an embedded literal
original-b window capturing every original crossing, the top avoids the old
loop, and every central old-loop contact has an actual exact strip coordinate.
No movie, boundary word, finite preparation, or contact certificate is supplied. -/
theorem actual_same_class_loop_prepared_movie_boundary
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
  have hφbounds (t : Interval) : 0<(φ t:ℝ) ∧ (φ t:ℝ)<1 := by
    rw [hφeq]
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hGbottom (t : Interval) : G (0,t)=b.val.map (φ t) := by
    rw [hGeq,hwbottom]
  have hbottomInj : Function.Injective (fun t => G (0,t)) := by
    intro s t he
    have hK : K (0,φ s)=K (0,φ t) := by rw [hzero,hzero,← hGbottom,← hGbottom]; exact he
    rcases hcollision 0 (φ s) (φ t) hK with he | he | he
    · exact hφ.injective he
    · have hh := congrArg Subtype.val he.1
      change (φ s:ℝ)=0 at hh
      linarith [(hφbounds s).1]
    · have hh := congrArg Subtype.val he.1
      change (φ s:ℝ)=1 at hh
      linarith [(hφbounds s).2]
  have hpreFinite : ((fun t => G (0,t)) ⁻¹' crossings M a b).Finite :=
    Set.Finite.preimage (fun s _ t _ he => hbottomInj he) hfinite
  have hfiniteBottom : {t : Interval | G (0,t) ∈ a.val.image}.Finite := by
    apply hpreFinite.subset
    intro t ht
    have hm := hGmarks (0,t)
    change G (0,t) ∈ crossings M a b
    refine ⟨⟨ht,hm⟩,?_,hm⟩
    rw [hGbottom]
    exact mem_range_self (φ t)
  have hfiniteTop : {t : Interval | G (1,t) ∈ a.val.image}.Finite := by
    apply Set.finite_empty.subset
    intro t ht
    exact False.elim (hGtop (1,t) rfl ht)
  have hr₀ε : r₀<ε := by
    have hh := mul_pos hε (show 0<1-d₀/4 by linarith)
    rw [hr₀eq,hAeq]
    nlinarith
  have hεr₁ : 1-ε<r₁ := by
    have hh := mul_pos hε (show 0<1-d₁/4 by linarith)
    rw [hr₁eq,hBeq]
    nlinarith
  have hcapture (t : Interval) (ht : b.val.map t ∈ crossings M a b) : ∃ s,φ s=t := by
    have hlo : ε<(t:ℝ) := lt_of_not_ge (fun hh => htails t (Or.inl hh) ht)
    have hhi : (t:ℝ)<1-ε := lt_of_not_ge (fun hh => htails t (Or.inr hh) ht)
    have hd : 0<r₁-r₀ := sub_pos.mpr horder
    let s : Interval := ⟨((t:ℝ)-r₀)/(r₁-r₀),by
      constructor
      · exact div_nonneg (by linarith) hd.le
      · exact (div_le_one hd).mpr (by linarith)⟩
    refine ⟨s,Subtype.ext ?_⟩
    rw [hφeq]
    dsimp [s]
    field_simp
    ring
  exact ⟨φ,hφ,hφbounds,hcapture,G,hGbottom,
    ((G.continuous.comp (continuous_const.prodMk continuous_id)).isClosedEmbedding hbottomInj).isEmbedding,
    hGmarks,(fun t => hGtop (1,t) rfl),hfiniteBottom,hfiniteTop,hfiniteLeft,hfiniteRight,
    BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hψbounds,hψzero,hψtop⟩
end CurveComplex.HyperellipticModel
