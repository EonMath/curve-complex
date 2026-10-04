import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.IntersectionParity.SubarcCircleCoordinates
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates

namespace CurveComplex.LocalSurgery

/-- The clean lifted side of an innermost disk projects to an embedded original
curve subarc when its projected corners are distinct. This is the side-injectivity
step in the source lifted-boundary argument; cleanliness is an actual set equality. -/
theorem clean_lifted_side_projects_to_embedding
    {E S : Type} [TopologicalSpace E] [T2Space E] [TopologicalSpace S] [T2Space S]
    (p : E → S) (cov : IsCoveringMap p) (a b : Curve S)
    (α : C(Interval,E)) (hα : Topology.IsEmbedding α)
    (hαa : Set.range α ⊆ p ⁻¹' a.image)
    (hclean : Set.range α ∩ p ⁻¹' b.image = {α 0,α 1})
    (hcorners : p (α 0) ≠ p (α 1)) :
    Topology.IsEmbedding ((⟨p,cov.continuous⟩ : C(E,S)).comp α) := by
  classical
  let f : C(Interval,S) := (⟨p,cov.continuous⟩ : C(E,S)).comp α
  have hfa : Set.range f ⊆ a.image := by
    rintro x ⟨t,rfl⟩
    exact hαa ⟨t,rfl⟩
  let q := subarcCircleCoordinates a f hfa
  let θ := subarcAngleCoordinates a f hfa
  have hq (t : Interval) : a.map (q t) = f t :=
    congrArg Subtype.val (a.embedded.toHomeomorph.apply_symm_apply ⟨f t,hfa ⟨t,rfl⟩⟩)
  have hθ : Circle.exp ∘ θ = q := Circle.isCoveringMap_exp.liftPath_lifts q
    (q 0).val.arg (Circle.exp_arg _).symm
  have hθp (t : Interval) : Circle.exp (θ t) = q t := congrFun hθ t
  let A : C(ℝ,S) := ⟨fun x => a.map (Circle.exp x), a.embedded.continuous.comp Circle.exp.continuous⟩
  have hbase : p (α 0) = A (θ 0) := by
    change f 0 = a.map (Circle.exp (θ 0))
    rw [hθp 0,hq]
  obtain ⟨L,⟨hL0,hL⟩,_⟩ := cov.existsUnique_continuousMap_lifts A (θ 0) (α 0) hbase
  have hident : (L.comp θ : Interval → E) = α := by
    apply cov.eq_of_comp_eq (L.comp θ).continuous α.continuous
    · funext t
      change p (L (θ t)) = p (α t)
      rw [show p (L (θ t)) = A (θ t) from congrFun hL (θ t)]
      change a.map (Circle.exp (θ t)) = f t
      rw [hθp t,hq]
    · exact hL0
  have hinj : Function.Injective θ := by
    intro t u h
    apply hα.injective
    rw [← congrFun hident t,← congrFun hident u]
    exact congrArg L h
  have hreturn (t : Interval) (he : Circle.exp (θ t) = Circle.exp (θ 0)) : t = 0 := by
    have hp : p (α t) = p (α 0) := by
      change f t = f 0
      rw [← hq t,← hq 0,← hθp t,← hθp 0,he]
    have hb : p (α 0) ∈ b.image := by
      have : α 0 ∈ Set.range α ∩ p ⁻¹' b.image := by
        rw [hclean]
        simp
      exact this.2
    have hm : α t ∈ ({α 0,α 1} : Set E) := by
      rw [← hclean]
      exact ⟨⟨t,rfl⟩,show p (α t) ∈ b.image from hp.symm ▸ hb⟩
    rcases Set.mem_insert_iff.mp hm with heq | heq
    · exact hα.injective heq
    · have heq' : α t = α 1 := Set.mem_singleton_iff.mp heq
      exact False.elim (hcorners (hp.symm.trans (congrArg p heq')))
  let r := realIntervalPath θ
  have hr (t : Interval) : r t.val = θ t := by
    change θ (Set.projIcc 0 1 (by norm_num) t.val) = θ t
    rw [Set.projIcc_of_mem _ t.property]
  have hr0 : r 0 = θ 0 := by simpa using hr 0
  have hr1 : r 1 = θ 1 := by simpa using hr 1
  have hri : Set.InjOn r (Set.Icc (0 : ℝ) 1) := by
    intro t ht u hu he
    apply congrArg Subtype.val (hinj (show θ ⟨t,ht⟩ = θ ⟨u,hu⟩ from by
      rw [← hr ⟨t,ht⟩,← hr ⟨u,hu⟩]; exact he))
  have hm := r.continuous.continuousOn.strictMonoOn_of_injOn_Icc'
    (show (0 : ℝ) ≤ 1 by norm_num) hri
  have hpipos : 0 < 2 * Real.pi := by positivity
  have hspan : max (θ 0) (θ 1) - min (θ 0) (θ 1) < 2 * Real.pi := by
    rcases hm with hm | hm
    · have hle : θ 0 ≤ θ 1 := by
        simpa only [hr0,hr1] using hm.monotoneOn (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
      rw [max_eq_right hle,min_eq_left hle]
      by_contra hn
      have hv : θ 0 + 2 * Real.pi ∈ Set.Icc (r 0) (r 1) := by
        rw [hr0,hr1]; constructor <;> linarith
      obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) r.continuous.continuousOn hv
      have he' : θ ⟨t,ht⟩ = θ 0 + 2 * Real.pi := (hr ⟨t,ht⟩).symm.trans he
      have hz := hreturn ⟨t,ht⟩ (by rw [he',Circle.exp_add_two_pi])
      rw [hz] at he'
      linarith
    · have hle : θ 1 ≤ θ 0 := by
        simpa only [hr0,hr1] using hm.antitoneOn (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
      rw [max_eq_left hle,min_eq_right hle]
      by_contra hn
      have hv : θ 0 - 2 * Real.pi ∈ Set.Icc (r 1) (r 0) := by
        rw [hr0,hr1]; constructor <;> linarith
      obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) r.continuous.continuousOn hv
      have he' : θ ⟨t,ht⟩ = θ 0 - 2 * Real.pi := (hr ⟨t,ht⟩).symm.trans he
      have hz := hreturn ⟨t,ht⟩ (by rw [he',Circle.exp_sub_two_pi])
      rw [hz] at he'
      linarith
  have hbounds (t : Interval) : θ t ∈ Set.Icc (min (θ 0) (θ 1)) (max (θ 0) (θ 1)) := by
    rcases hm with hm | hm
    · have hl := hm.monotoneOn (by norm_num) t.property t.property.1
      have hu := hm.monotoneOn t.property (by norm_num) t.property.2
      rw [hr0,hr t] at hl
      rw [hr t,hr1] at hu
      exact ⟨(min_le_left _ _).trans hl,hu.trans (le_max_right _ _)⟩
    · have hl := hm.antitoneOn t.property (by norm_num) t.property.2
      have hu := hm.antitoneOn (by norm_num) t.property t.property.1
      rw [hr t,hr1] at hl
      rw [hr0,hr t] at hu
      exact ⟨(min_le_right _ _).trans hl,hu.trans (le_max_left _ _)⟩
  apply f.continuous.isClosedEmbedding _ |>.isEmbedding
  intro t u he
  apply hinj
  apply Circle.exp_injOn_Icc hspan (hbounds t) (hbounds u)
  apply a.embedded.injective
  rw [hθp t,hθp u,hq,hq]
  exact he

end CurveComplex.LocalSurgery
