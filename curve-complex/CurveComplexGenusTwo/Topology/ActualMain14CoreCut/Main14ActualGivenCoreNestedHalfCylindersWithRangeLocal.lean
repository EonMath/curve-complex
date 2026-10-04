import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreHalfBandPullbackLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
-- Actual old G half and actual terminal straight subband, sharing its literal core.
example (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
    (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩))
    (ε : ℝ) (hε : 0 < ε) (hεq : ε < 1/4)
    (hband : ∀ z (u : Interval), |(u:ℝ)-1/2| ≤ ε →
      ∃ p : Circle × Interval, 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1 ∧ G p=(z,u))
    (hgap : ∀ z, ε < |((G (z,0)).2:ℝ)-1/2|)
    (b : Bool)
    (hside : ∀ z (u : Interval), 1/2 < (u:ℝ) →
      if b then ((G (z,u)).2:ℝ)<1/2 else 1/2<((G (z,u)).2:ℝ)) :
    ∃ f g : C(Circle × Interval,Circle × Interval), IsEmbedding f ∧ IsEmbedding g ∧
      (∀ z, f (z,0)=G (z,0)) ∧
      (∀ z, f (z,1)=(r z,⟨1/2,by norm_num⟩)) ∧
      (∀ z, g (z,0)=(z,⟨1/2+(if b then ε else -ε),by
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith⟩)) ∧
      (∀ z, g (z,1)=(z,⟨1/2,by norm_num⟩)) ∧
      Set.range f ⊆ Set.range G ∧ Set.range g ⊆ Set.range f ∧
      Disjoint (Set.range (fun z : Circle => G (z,0))) (Set.range g) := by
  audit_main14_base3
    have hPullback (G : C(Circle × Interval,Circle × Interval))
    (ε : ℝ) (hε : 0 < ε) (hεq : ε < 1/4)
    (hband : ∀ z (u : Interval), |(u:ℝ)-1/2| ≤ ε →
      ∃ p : Circle × Interval, 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1 ∧ G p=(z,u))
    (hgap : ∀ z, ε < |((G (z,0)).2:ℝ)-1/2|)
    (b : Bool)
    (hside : ∀ z (u : Interval), 1/2 < (u:ℝ) →
      if b then ((G (z,u)).2:ℝ)<1/2 else 1/2<((G (z,u)).2:ℝ)) :
    (∀ z (t : Interval), ∃ p : Circle × Interval,
      (p.2:ℝ) ≤ 1/2 ∧
      G p=(z,⟨1/2+(if b then ε else -ε)*(1-(t:ℝ)),by
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> nlinarith [t.property.1,t.property.2]⟩)) ∧
    Disjoint (Set.range (fun z : Circle => G (z,0)))
      (Set.range (fun p : Circle × Interval =>
        ((p.1,⟨1/2+(if b then ε else -ε)*(1-(p.2:ℝ)),by
          cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> nlinarith [p.2.property.1,p.2.property.2]⟩) : Circle × Interval))) := by
      have habs (t : Interval) : |(if b then ε else -ε)*(1-(t:ℝ))| ≤ ε := by
        cases b
        · simp only [Bool.false_eq_true,if_false]
          rw [abs_mul,abs_neg,abs_of_pos hε,abs_of_nonneg (by linarith [t.property.2])]
          nlinarith [t.property.1]
        · simp only [if_true]
          rw [abs_mul,abs_of_pos hε,abs_of_nonneg (by linarith [t.property.2])]
          nlinarith [t.property.1]
      constructor
      · intro z t
        let u : Interval := ⟨1/2+(if b then ε else -ε)*(1-(t:ℝ)),by
          cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> nlinarith [t.property.1,t.property.2]⟩
        have hu : |(u:ℝ)-1/2| ≤ ε := by
          change |1/2+(if b then ε else -ε)*(1-(t:ℝ))-1/2| ≤ ε
          have he : (1/2:ℝ)+(if b then ε else -ε)*(1-(t:ℝ))-1/2 =
              (if b then ε else -ε)*(1-(t:ℝ)) := by ring
          rw [he]
          exact habs t
        obtain ⟨p,hp0,hp1,he⟩ := hband z u hu
        refine ⟨p,?_,he⟩
        by_contra hn
        have hs := hside p.1 p.2 (lt_of_not_ge hn)
        have hv := congrArg (fun x : Circle × Interval => (x.2:ℝ)) he
        cases b
        · simp only [Bool.false_eq_true,if_false] at hs hv
          change ((G p).2:ℝ)=1/2+-ε*(1-(t:ℝ)) at hv
          nlinarith [t.property.2]
        · simp only [if_true] at hs hv
          change ((G p).2:ℝ)=1/2+ε*(1-(t:ℝ)) at hv
          nlinarith [t.property.2]
      · apply Set.disjoint_left.mpr
        rintro x ⟨z,rfl⟩ ⟨p,he⟩
        have hv := congrArg (fun x : Circle × Interval => (x.2:ℝ)) he
        have hh : ((G (z,0)).2:ℝ)-1/2=(if b then ε else -ε)*(1-(p.2:ℝ)) := by
          change 1/2+(if b then ε else -ε)*(1-(p.2:ℝ))=((G (z,0)).2:ℝ) at hv
          linarith
        have hg := hgap z
        rw [hh] at hg
        exact (not_lt_of_ge (habs p.2)) hg

    obtain ⟨hpull,havoid⟩ := hPullback G ε hε hεq hband hgap b hside
    let τ : C(Circle × Interval,Circle × Interval) :=
      ⟨fun p => (p.1,⟨(p.2:ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩),by fun_prop⟩
    let f : C(Circle × Interval,Circle × Interval) := G.comp τ
    let g : C(Circle × Interval,Circle × Interval) :=
      ⟨fun p => (p.1,⟨1/2+(if b then ε else -ε)*(1-(p.2:ℝ)),by
        cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
          constructor <;> nlinarith [p.2.property.1,p.2.property.2]⟩),by fun_prop⟩
    have hf : IsEmbedding f := by
      refine (f.continuous.isClosedEmbedding ?_).isEmbedding
      intro p q he
      have hh := hGe.injective he
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
      refine Prod.ext ?_ ?_
      · exact h1
      apply Subtype.ext
      change (p.2:ℝ)/2=(q.2:ℝ)/2 at h2
      linarith
    have hg : IsEmbedding g := by
      refine (g.continuous.isClosedEmbedding ?_).isEmbedding
      intro p q he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) he
      refine Prod.ext ?_ ?_
      · exact h1
      apply Subtype.ext
      change 1/2+(if b then ε else -ε)*(1-(p.2:ℝ)) =
        1/2+(if b then ε else -ε)*(1-(q.2:ℝ)) at h2
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h2 <;> nlinarith
    refine ⟨f,g,hf,hg,?_,?_,?_,?_,?_,?_,havoid⟩
    · intro z
      change G (z,⟨(0:ℝ)/2,_⟩)=G (z,0)
      congr 1
      refine Prod.ext rfl ?_
      apply Subtype.ext
      norm_num
    · intro z
      change G (z,⟨(1:ℝ)/2,_⟩)=(r z,⟨1/2,_⟩)
      exact hcore z
    · intro z
      dsimp [g]
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change 1/2+(if b then ε else -ε)*(1-(0:ℝ))=1/2+(if b then ε else -ε)
      ring
    · intro z
      dsimp [g]
      refine Prod.ext rfl ?_
      apply Subtype.ext
      change 1/2+(if b then ε else -ε)*(1-(1:ℝ))=1/2
      ring
    · rintro x ⟨p,rfl⟩
      exact ⟨τ p,rfl⟩
    · rintro x ⟨p,rfl⟩
      obtain ⟨q,hq,he⟩ := hpull p.1 p.2
      refine ⟨(q.1,⟨2*(q.2:ℝ),by constructor <;> linarith [q.2.property.1]⟩),?_⟩
      change G (q.1,⟨(2*(q.2:ℝ))/2,_⟩)=g p
      have hh : (⟨(2*(q.2:ℝ))/2,by constructor <;> linarith [q.2.property.1]⟩ : Interval)=q.2 := by
        apply Subtype.ext;ring
      rw [hh]
      exact he
end CurveComplex.HyperellipticModel
