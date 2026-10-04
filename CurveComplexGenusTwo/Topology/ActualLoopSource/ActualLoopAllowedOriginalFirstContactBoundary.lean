import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopAllowedFiniteContactParameters
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- In the shared-start case, fixed-pair finite contacts produce an actual
original two-side Jordan boundary. The terminal corner is unmarked. No
puncture-free region or cancellation is asserted before it is constructed. -/
theorem actual_loop_allowed_shared_start_first_contact_jordan_boundary
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hstart : a.val.map 0 = b.val.map 0)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) :
    ∃ (f g : C(Interval,S)) (v : S) (c : Curve S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = b.val.map 0 ∧ g 0 = b.val.map 0 ∧ f 1 = v ∧ g 1 = v ∧
      b.val.map 0 ≠ v ∧ v ∈ ArcSurgery.crossings M a b ∧
      range f ∩ range g = {b.val.map 0,v} ∧ c.image = range f ∪ range g := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let A : Set Interval := {t | b.val.map t ∈ a.val.image} ∩ Ioi 0
  have hAf : A.Finite :=
    (actual_loop_allowed_all_contact_parameters_finite M a b hfinite).subset inter_subset_left
  obtain ⟨t,ht⟩ := hp.2.1
  have ht0 : t ≠ 0 := by intro he; subst t; exact hp.2.2 (ht ▸ b.val.start_marked)
  have htpos : (0 : Interval) < t := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
  have hAt : t ∈ A := by
    refine ⟨?_,htpos⟩
    change b.val.map t ∈ a.val.image
    rw [ht]
    exact hp.1.1
  obtain ⟨s,hs,hsmin⟩ := hAf.isCompact.exists_isLeast ⟨t,hAt⟩
  have ht1 : t≠1 := by intro he; subst t; exact hp.2.2 (ht ▸ b.val.end_marked)
  have htlt : t<(1:Interval) := lt_of_le_of_ne t.property.2 ht1
  have hslt : s<(1:Interval) := lt_of_le_of_lt (hsmin hAt) htlt
  have hsmarked : b.val.map s ∉ (M.cover.branch : Set S) := by
    intro hm
    exact (b.val.marked_only_at_ends s hm).elim hs.2.ne' hslt.ne
  have hscontact : b.val.map s ∈ ArcSurgery.crossings M a b :=
    ⟨⟨hs.1,hsmarked⟩,Set.mem_range_self s,hsmarked⟩
  obtain ⟨r,hr⟩ := hs.1
  have hr0 : r ≠ 0 := by
    intro he; subst r
    exact hsmarked (hr ▸ a.val.start_marked)
  have hr1 : r≠1 := by intro he; subst r; exact hsmarked (hr ▸ a.val.end_marked)
  have hrl : r<(1:Interval) := lt_of_le_of_ne r.property.2 hr1
  have hrpos : (0 : Interval) < r := lt_of_le_of_ne r.property.1 (Ne.symm hr0)
  let α : Interval → Interval := fun t => ⟨r.val*t.val,by constructor <;>
    nlinarith [r.property.1,r.property.2,t.property.1,t.property.2]⟩
  let β : Interval → Interval := fun t => ⟨s.val*t.val,by constructor <;>
    nlinarith [s.property.1,s.property.2,t.property.1,t.property.2]⟩
  let f : C(Interval,S) := ⟨a.val.map ∘ α,a.val.continuous.comp (by fun_prop)⟩
  let g : C(Interval,S) := ⟨b.val.map ∘ β,b.val.continuous.comp (by fun_prop)⟩
  have hf0 : f 0 = b.val.map 0 := by
    change a.val.map (α 0) = b.val.map 0
    have hα : α 0 = 0 := by apply Subtype.ext; simp [α]
    rw [hα,hstart]
  have hg0 : g 0 = b.val.map 0 := by
    apply congrArg b.val.map; apply Subtype.ext; simp [β]
  have hf1 : f 1 = b.val.map s := by
    change a.val.map (α 1) = b.val.map s
    have hα : α 1 = r := by apply Subtype.ext; simp [α]
    rw [hα]; exact hr
  have hg1 : g 1 = b.val.map s := by
    apply congrArg b.val.map; apply Subtype.ext; simp [β]
  have hfi : Function.Injective f := by
    intro t u he
    have hαlt (z : Interval) : α z<(1:Interval) := by
      change r.val*z.val<1
      have hrl' : r.val<1 := hrl
      nlinarith [z.property.1,z.property.2,r.property.1]
    have heα : α t=α u := by
      rcases a.val.injective_except_loop_closure _ _ he with h | h | h
      · exact h
      · exact False.elim ((hαlt u).ne h.2)
      · exact False.elim ((hαlt t).ne h.1)
    have hv := congrArg Subtype.val heα
    apply Subtype.ext
    have hrp : 0 < r.val := hrpos
    dsimp [α] at hv
    nlinarith
  have hgi : Function.Injective g := by
    intro t u he
    have hβlt (z : Interval) : β z<(1:Interval) := by
      change s.val*z.val<1
      have hsl' : s.val<1 := hslt
      nlinarith [z.property.1,z.property.2,s.property.1]
    have heβ : β t=β u := by
      rcases b.val.injective_except_loop_closure _ _ he with h | h | h
      · exact h
      · exact False.elim ((hβlt u).ne h.2)
      · exact False.elim ((hβlt t).ne h.1)
    have hv := congrArg Subtype.val heβ
    apply Subtype.ext
    have hsp : 0 < s.val := hs.2
    dsimp [β] at hv
    nlinarith
  have hfe : IsEmbedding f := (f.continuous.isClosedEmbedding hfi).isEmbedding
  have hge : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
  have hfon : range f ⊆ a.val.image := by rintro x ⟨t,rfl⟩; exact ⟨α t,rfl⟩
  have hgon : range g ⊆ b.val.image := by rintro x ⟨t,rfl⟩; exact ⟨β t,rfl⟩
  have hcross (u v : Interval) (he : f u = g v) :
      (u=0 ∧ v=0) ∨ (u=1 ∧ v=1) := by
    by_cases hv0 : v=0
    · left; refine ⟨hfi ?_,hv0⟩; rw [hf0,← hg0,← hv0,← he]
    by_cases hv1 : v=1
    · right; refine ⟨hfi ?_,hv1⟩; rw [hf1,← hg1,← hv1,← he]
    have hvpos : 0 < v.val := lt_of_le_of_ne v.property.1 (fun h => hv0 (Subtype.ext h.symm))
    have hvlt : v.val < 1 := lt_of_le_of_ne v.property.2 (fun h => hv1 (Subtype.ext h))
    have hsp : 0 < s.val := hs.2
    have hβpos : (0 : Interval) < β v := by change 0 < s.val*v.val; positivity
    have hβlt : β v < s := by change s.val*v.val < s.val; nlinarith
    have hhit : b.val.map (β v) ∈ a.val.image := by
      change g v ∈ a.val.image
      rw [← he]
      exact hfon ⟨u,rfl⟩
    exact False.elim ((not_lt_of_ge (hsmin ⟨hhit,hβpos⟩)) hβlt)
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hfi hgi
    (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcross
  have hsides : range f ∩ range g = {b.val.map 0,b.val.map s} := by
    ext x
    constructor
    · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
      rcases hcross u v (hu.trans hv.symm) with ⟨hu0,_⟩ | ⟨hu1,_⟩
      · exact Or.inl (hu.symm.trans (hu0 ▸ hf0))
      · exact Or.inr (mem_singleton_iff.mpr (hu.symm.trans (hu1 ▸ hf1)))
    · intro hx
      rcases mem_insert_iff.mp hx with he | he
      · subst x; exact ⟨⟨0,hf0⟩,⟨0,hg0⟩⟩
      · have he' := mem_singleton_iff.mp he
        subst x; exact ⟨⟨1,hf1⟩,⟨1,hg1⟩⟩
  have hcorners : b.val.map 0 ≠ b.val.map s := fun he =>
    hsmarked (he ▸ b.val.start_marked)
  exact ⟨f,g,b.val.map s,c,hfe,hge,hfon,hgon,hf0,hg0,hf1,hg1,hcorners,hscontact,hsides,hc⟩

end CurveComplex.HyperellipticModel
