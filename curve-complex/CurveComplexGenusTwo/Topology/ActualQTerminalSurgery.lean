import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripGluing
import CurveComplexGenusTwo.Topology.ActualPrescribedFourArcRectangle
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.HalfPlaneBandOpenness
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualEndpointAttachedAxisChartPackage
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip
import ClassificationOfSurfaces.Moise.Brouwer
import CurveComplexGenusTwo.Foundations.PlanarDiscRecognition
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import CurveComplexGenusTwo.Topology.IntersectionParity.DiscRangeCoordinates
import CurveComplexGenusTwo.Topology.IntersectionParity.SurfaceDiskInterior
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview

set_option maxHeartbeats 4000000

namespace CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
open CurveComplex Set Schoenflies Bornology

variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

def arcRel (a b : EssentialProperArc S x R) : Prop :=
  ∃ H : AmbientIsotopy (Q S x R),
    (∀ t, (fun y => H.map (t,y)) '' boundaryQ S x R = boundaryQ S x R) ∧
    H.finalMap '' Set.range a.val.val = Set.range b.val.val

abbrev ArcVertex := Quot (arcRel S x R)

noncomputable local instance : DecidableEq (ArcVertex S x R) := Classical.decEq _

/-- Exact actual arc-system complex used locally in the original filling body.
These structural simplicial laws copy its already compiled restriction proof. -/
noncomputable def arcComplex : AbstractSimplicialComplex (ArcVertex S x R) := by
  classical
  let arcFaces : Set (Finset (ArcVertex S x R)) := {σ | σ.Nonempty ∧
    ∃ rep : ↥σ → EssentialProperArc S x R,
      (∀ w, Quot.mk (arcRel S x R) (rep w) = w.val) ∧
      ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
  exact {
    faces := arcFaces
    isRelLowerSet_faces := by
      intro σ hσ
      refine ⟨hσ.1, ?_⟩
      intro τ hτσ hne
      obtain ⟨rep, hr, hd⟩ := hσ.2
      refine ⟨hne, (fun w => rep ⟨w.val, hτσ w.property⟩), ?_, ?_⟩
      · intro w
        exact hr ⟨w.val, hτσ w.property⟩
      · intro u w huw
        apply hd
        intro he
        exact huw (Subtype.ext (congrArg (fun z : ↥σ => z.val) he))
    singleton_mem := by
      intro w
      obtain ⟨a, ha⟩ := Quot.exists_rep w
      refine ⟨Finset.singleton_nonempty w, (fun _ => a), ?_, ?_⟩
      · intro z
        exact ha.trans (Finset.mem_singleton.mp z.property).symm
      · intro u z huz
        exact False.elim (huz (Subtype.ext
          ((Finset.mem_singleton.mp u.property).trans
            (Finset.mem_singleton.mp z.property).symm))) }

variable {S x R} in
private def properPath (a : ProperArc S x R) : Path (a.val 0) (a.val 1)  := {
    toContinuousMap := a.val
    source' := rfl
    target' := rfl }

private theorem actual_original_essential_terminal_surgery_branches_cannot_both_be_parallel_isolated
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (a0 : EssentialProperArc S x R)
      (b : EssentialProperArc S x R) (d e : ProperArc S x R) (u v : Interval)
      (hu0 : 0<u) (hu1 : u<1) (hv0 : 0<v) (hv1 : v<1)
      (hcross : b.val.val u=a0.val.val v)
      (htail : ∀ s t : Interval,v≤t → b.val.val s=a0.val.val t → s=u ∧ t=v)
      (hd0 : d.val 0=b.val.val 0) (he0 : e.val 0=b.val.val 1)
      (hd1 : d.val 1=a0.val.val 1) (he1 : e.val 1=a0.val.val 1)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) :
      ¬boundaryParallel S x R d ∨ ¬boundaryParallel S x R e := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have boundary_mem_iff (h : Q S x R ≃ₜ Q S x R)
      (hh : h '' boundaryQ S x R = boundaryQ S x R) (y : Q S x R) :
      h y ∈ boundaryQ S x R ↔ y ∈ boundaryQ S x R := by
    constructor
    · intro hy
      rw [← hh] at hy
      obtain ⟨z, hz, he⟩ := hy
      exact h.injective he ▸ hz
    · intro hy
      rw [← hh]
      exact ⟨y, hy, rfl⟩
  let transportProper (h : Q S x R ≃ₜ Q S x R)
      (hh : h '' boundaryQ S x R = boundaryQ S x R)
      (a : ProperArc S x R) : ProperArc S x R :=
    ⟨(⟨h, h.continuous⟩ : C(Q S x R, Q S x R)).comp a.val,
      h.isEmbedding.comp a.property.1,
      (boundary_mem_iff h hh _).2 a.property.2.1,
      (boundary_mem_iff h hh _).2 a.property.2.2.1,
      fun t ht hm => a.property.2.2.2 t ht
        ((boundary_mem_iff h hh _).1 hm)⟩
  have parallel_transport (h : Q S x R ≃ₜ Q S x R)
      (hh : h '' boundaryQ S x R = boundaryQ S x R)
      (a : ProperArc S x R) (ha : boundaryParallel S x R a) :
      boundaryParallel S x R (transportProper h hh a) := by
    obtain ⟨b, hb, hbb, d, hd, he⟩ := ha
    refine ⟨(⟨h, h.continuous⟩ : C(Q S x R, Q S x R)).comp b, h.isEmbedding.comp hb,
      (fun t => (boundary_mem_iff h hh _).2 (hbb t)),
      (⟨h, h.continuous⟩ : C(Q S x R, Q S x R)).comp d, h.isEmbedding.comp hd, ?_⟩
    change (fun z => h (d z)) '' _ =
      Set.range (fun t => h (a.val t)) ∪ Set.range (fun t => h (b t))
    rw [← Set.image_image, he, Set.image_union]
    exact congrArg₂ (fun A B : Set (Q S x R) => A ∪ B)
      (Set.range_comp' h a.val).symm (Set.range_comp' h b).symm
  have essential_transport (h : Q S x R ≃ₜ Q S x R)
      (hh : h '' boundaryQ S x R = boundaryQ S x R)
      (a : EssentialProperArc S x R) :
      ¬ boundaryParallel S x R (transportProper h hh a.val) := by
    have hinv : h.symm '' boundaryQ S x R = boundaryQ S x R := by
      calc
        h.symm '' boundaryQ S x R = h.symm '' (h '' boundaryQ S x R) :=
          congrArg (fun A => h.symm '' A) hh.symm
        _ = boundaryQ S x R := by simp [Set.image_image]
    intro ha
    have hb := parallel_transport h.symm hinv (transportProper h hh a.val) ha
    have he : transportProper h.symm hinv (transportProper h hh a.val) = a.val := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      change h.symm (h (a.val.val t)) = a.val.val t
      exact h.symm_apply_apply _
    rw [he] at hb
    exact a.property hb
  let transportEssential (h : Q S x R ≃ₜ Q S x R)
      (hh : h '' boundaryQ S x R = boundaryQ S x R)
      (a : EssentialProperArc S x R) : EssentialProperArc S x R :=
    ⟨transportProper h hh a.val, essential_transport h hh a⟩
  have transport_disjoint (h : Q S x R ≃ₜ Q S x R)
      (hh : h '' boundaryQ S x R = boundaryQ S x R)
      (a b : EssentialProperArc S x R)
      (hab : Disjoint (Set.range a.val.val) (Set.range b.val.val)) :
      Disjoint (Set.range (transportEssential h hh a).val.val)
        (Set.range (transportEssential h hh b).val.val) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t, rfl⟩ ⟨u, hu⟩
    exact Set.disjoint_left.mp hab ⟨t, rfl⟩
      ⟨u, h.injective hu⟩
  have transport_class (H : AmbientIsotopy (Q S x R))
      (hH : ∀ t, (fun y => H.map (t, y)) '' boundaryQ S x R = boundaryQ S x R)
      (h : Q S x R ≃ₜ Q S x R) (hh : ∀ y, h y = H.finalMap y)
      (a : EssentialProperArc S x R) :
      Quot.mk (arcRel S x R)
        (transportEssential h (by
          rw [show (h : Q S x R → Q S x R) = H.finalMap from funext hh]
          exact hH ⟨1, by norm_num⟩) a) =
      Quot.mk (arcRel S x R) a := by
    apply Eq.symm
    apply Quot.sound
    refine ⟨H, hH, ?_⟩
    change H.finalMap '' Set.range a.val.val = Set.range (fun t => h (a.val.val t))
    rw [← show (h : Q S x R → Q S x R) = H.finalMap from funext hh]
    exact (Set.range_comp' h a.val.val).symm
  have transport_system (σ : Finset (ArcVertex S x R))
      (rep : ↥σ → EssentialProperArc S x R)
      (hr : ∀ w, Quot.mk (arcRel S x R) (rep w) = w.val)
      (hd : ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val)
        (Set.range (rep w).val.val))
      (H : AmbientIsotopy (Q S x R))
      (hH : ∀ t, (fun y => H.map (t, y)) '' boundaryQ S x R = boundaryQ S x R) :
      ∃ rep' : ↥σ → EssentialProperArc S x R,
        (∀ w, Quot.mk (arcRel S x R) (rep' w) = w.val) ∧
        (∀ u w, u ≠ w → Disjoint (Set.range (rep' u).val.val)
          (Set.range (rep' w).val.val)) ∧
        (∀ w, Set.range (rep' w).val.val = H.finalMap '' Set.range (rep w).val.val) := by
    obtain ⟨h, hh⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    have hb : h '' boundaryQ S x R = boundaryQ S x R := by
      simpa only [hh] using hH ⟨1, by norm_num⟩
    refine ⟨fun w => transportEssential h hb (rep w), ?_, ?_, ?_⟩
    · intro w
      exact (transport_class H hH h hh (rep w)).trans (hr w)
    · intro u w huw
      exact transport_disjoint h hb (rep u) (rep w) (hd u w huw)
    · intro w
      change Set.range (fun t => h ((rep w).val.val t)) =
        H.finalMap '' Set.range (rep w).val.val
      rw [← show (h : Q S x R → Q S x R) = H.finalMap from funext hh]
      exact Set.range_comp' h (rep w).val.val
  have proper_boundary_parameters (a : ProperArc S x R) (t : Interval) :
      a.val t ∈ boundaryQ S x R ↔ t = 0 ∨ t = 1 := by
    constructor
    · intro ht
      by_contra hne
      have h0 : t ≠ 0 := fun he => hne (Or.inl he)
      have h1 : t ≠ 1 := fun he => hne (Or.inr he)
      have ht0 : 0 < t := lt_of_le_of_ne (by exact t.property.1) (Ne.symm h0)
      have ht1 : t < 1 := lt_of_le_of_ne (by exact t.property.2) h1
      exact a.property.2.2.2 t ⟨ht0, ht1⟩ ht
    · rintro (rfl | rfl)
      · exact a.property.2.1
      · exact a.property.2.2.1
  have proper_boundary_trace (a : ProperArc S x R) :
      Set.range a.val ∩ boundaryQ S x R = {a.val 0, a.val 1} := by
    ext y
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      obtain h0 | h1 := (proper_boundary_parameters a t).1 ht
      · simp [h0]
      · simp [h1]
    · intro hy
      rcases Set.mem_insert_iff.mp hy with he | he
      · subst y
        exact ⟨⟨0, rfl⟩, a.property.2.1⟩
      · have he' : y = a.val 1 := Set.mem_singleton_iff.mp he
        subst y
        exact ⟨⟨1, rfl⟩, a.property.2.2.1⟩
  have proper_endpoints_distinct (a : ProperArc S x R) : a.val 0 ≠ a.val 1 := by
    intro he
    have h01 : (0 : Interval) = 1 := a.property.1.injective he
    have : (0 : ℝ) = 1 := congrArg Subtype.val h01
    norm_num at this
  have system_endpoints_distinct (a b : ProperArc S x R)
      (hd : Disjoint (Set.range a.val) (Set.range b.val)) (t u : Interval) :
      a.val t ≠ b.val u := by
    intro he
    exact Set.disjoint_left.mp hd ⟨t, rfl⟩ ⟨u, he.symm⟩
  have relation_reflexive (a : EssentialProperArc S x R) : arcRel S x R a a := by
    let H : AmbientIsotopy (Q S x R) := {
      map := ⟨fun p => p.2, continuous_snd⟩
      homeomorphism_at := fun _ => ⟨Homeomorph.refl _, fun _ => rfl⟩
      at_zero := fun _ => rfl }
    refine ⟨H, ?_, ?_⟩
    · intro t
      exact Set.image_id _
    · exact Set.image_id _
  have relation_transitive (a b c : EssentialProperArc S x R)
      (hab : arcRel S x R a b) (hbc : arcRel S x R b c) : arcRel S x R a c := by
    obtain ⟨H, hH, hHab⟩ := hab
    obtain ⟨K, hK, hKbc⟩ := hbc
    let L : AmbientIsotopy (Q S x R) := {
      map := ⟨fun p => K.map (p.1, H.map p),
        K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩
      homeomorphism_at := by
        intro t
        obtain ⟨h, hh⟩ := H.homeomorphism_at t
        obtain ⟨k, hk⟩ := K.homeomorphism_at t
        exact ⟨h.trans k, fun y => by
          change k (h y) = K.map (t, H.map (t, y))
          rw [hk, hh]⟩
      at_zero := by
        intro y
        change K.map (⟨0, by norm_num⟩, H.map (⟨0, by norm_num⟩, y)) = y
        rw [H.at_zero, K.at_zero] }
    refine ⟨L, ?_, ?_⟩
    · intro t
      change (fun y => K.map (t, H.map (t, y))) '' _ = _
      rw [← Set.image_image (fun y => K.map (t, y)) (fun y => H.map (t, y)), hH t, hK t]
    · change (fun y => K.finalMap (H.finalMap y)) '' _ = _
      rw [← Set.image_image, hHab, hKbc]
  have relation_symmetric (a b : EssentialProperArc S x R)
      (hab : arcRel S x R a b) : arcRel S x R b a := by
    obtain ⟨H, hH, hHab⟩ := hab
    obtain ⟨h, hh⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    let reverse : Interval → Interval := unitInterval.symmHomeomorph
    have hrev0 : reverse 0 = 1 := by apply Subtype.ext; norm_num [reverse]
    have hrev1 : reverse 1 = 0 := by apply Subtype.ext; norm_num [reverse]
    have hc : Continuous reverse := unitInterval.symmHomeomorph.continuous
    have hinv : h.symm '' boundaryQ S x R = boundaryQ S x R := by
      have hb : h '' boundaryQ S x R = boundaryQ S x R := by
        simpa only [hh] using hH ⟨1, by norm_num⟩
      calc
        h.symm '' boundaryQ S x R = h.symm '' (h '' boundaryQ S x R) :=
          congrArg (fun A => h.symm '' A) hb.symm
        _ = boundaryQ S x R := by simp [Set.image_image]
    let K : AmbientIsotopy (Q S x R) := {
      map := ⟨fun p => H.map (reverse p.1, h.symm p.2),
        H.map.continuous.comp ((hc.comp continuous_fst).prodMk
          (h.symm.continuous.comp continuous_snd))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨k, hk⟩ := H.homeomorphism_at (reverse t)
        exact ⟨h.symm.trans k, fun y => by
          change k (h.symm y) = H.map (reverse t, h.symm y)
          exact hk _⟩
      at_zero := by
        intro y
        change H.map (reverse 0, h.symm y) = y
        rw [hrev0]
        change H.map (⟨1, by norm_num⟩, h.symm y) = y
        rw [← hh]
        exact h.apply_symm_apply y }
    refine ⟨K, ?_, ?_⟩
    · intro t
      change (fun y => H.map (reverse t, h.symm y)) '' _ = _
      rw [← Set.image_image (fun y => H.map (reverse t, y)) h.symm, hinv, hH (reverse t)]
    · have hk : K.finalMap = h.symm := by
        funext y
        change H.map (reverse 1, h.symm y) = h.symm y
        rw [hrev1]
        exact H.at_zero _
      rw [hk, ← hHab]
      have hf : H.finalMap = h := (funext hh).symm
      rw [hf]
      simp [Set.image_image]
  have embedded_arcs_concat_injective
      {S : Type} [TopologicalSpace S] {a b c : S}
      (p : Path a b) (q : Path b c)
      (hp : Function.Injective p) (hq : Function.Injective q)
      (hcross : ∀ s t : unitInterval, p s = q t → s = 1 ∧ t = 0) :
      Function.Injective (p.trans q) := by
    intro s t he
    rw [Path.trans_apply, Path.trans_apply] at he
    split_ifs at he with hs ht ht
    · have hh := congrArg Subtype.val (hp he)
      apply Subtype.ext
      dsimp at hh
      linarith
    · have hh := (hcross _ _ he).2
      have hv := congrArg Subtype.val hh
      dsimp at hv
      have htt : (1 : ℝ) / 2 < t := lt_of_not_ge ht
      linarith
    · have hh := (hcross _ _ he.symm).2
      have hv := congrArg Subtype.val hh
      dsimp at hv
      have hss : (1 : ℝ) / 2 < s := lt_of_not_ge hs
      linarith
    · have hh := congrArg Subtype.val (hq he)
      apply Subtype.ext
      dsimp at hh
      linarith
  
  have actual_cut_subpath_injective
      {S : Type} [TopologicalSpace S] {x y : S} (p : Path x y)
      (hp : Function.Injective p) (a b : unitInterval) (hab : a < b) :
      Function.Injective (CurveComplex.BranchedDoubleCover.actualSubpath p a b) ∧ p a ≠ p b := by
    constructor
    · intro s t heq
      have he := congrArg (fun u : unitInterval => (u : ℝ)) (hp heq)
      change (1-(s:ℝ))*(a:ℝ)+(s:ℝ)*(b:ℝ) =
        (1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ) at he
      have hlt : (a : ℝ) < (b : ℝ) := hab
      apply Subtype.ext
      nlinarith
    · exact fun he => hab.ne (hp he)
  have splice_proper {a z c : Q S x R} (p : Path a z) (q : Path z c)
      (hp : Function.Injective p) (hq : Function.Injective q)
      (hmeet : ∀ s t : Interval, p s = q t → s = 1 ∧ t = 0)
      (ha : a ∈ boundaryQ S x R) (hc : c ∈ boundaryQ S x R)
      (hpb : ∀ t, p t ∈ boundaryQ S x R → t = 0)
      (hqb : ∀ t, q t ∈ boundaryQ S x R → t = 1) :
      ∃ b : ProperArc S x R,
        Set.range b.val = Set.range p ∪ Set.range q ∧ b.val 0 = a ∧ b.val 1 = c := by
    let r := p.trans q
    have hr : Function.Injective r :=
      embedded_arcs_concat_injective p q hp hq hmeet
    have hri : Topology.IsEmbedding r := r.continuous.isClosedEmbedding hr |>.isEmbedding
    have hproper (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1) :
        r t ∉ boundaryQ S x R := by
      intro hb
      change (p.trans q) t ∈ boundaryQ S x R at hb
      rw [Path.trans_apply] at hb
      split_ifs at hb with he
      · have hv := congrArg Subtype.val (hpb _ hb)
        change 2 * (t : ℝ) = 0 at hv
        have ht0 : (0 : ℝ) < t := ht.1
        linarith
      · have hv := congrArg Subtype.val (hqb _ hb)
        change 2 * (t : ℝ) - 1 = 1 at hv
        have ht1 : (t : ℝ) < 1 := ht.2
        linarith
    refine ⟨⟨r.toContinuousMap, hri, ?_, ?_, hproper⟩, ?_, r.source, r.target⟩
    · change r 0 ∈ boundaryQ S x R
      rwa [r.source]
    · change r 1 ∈ boundaryQ S x R
      rwa [r.target]
    · exact Path.trans_range p q
  have terminal_left_branch (b : ProperArc S x R) (u v : Interval)
      (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
      (hcross : b.val u = a0.val.val v)
      (htail : ∀ s t : Interval, v ≤ t → b.val s = a0.val.val t → s = u ∧ t = v) :
      ∃ d : ProperArc S x R,
        d.val 0 = b.val 0 ∧ d.val 1 = a0.val.val 1 ∧
        Set.range d.val =
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1) := by
    let p := (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u).cast
      rfl hcross.symm
    let q := CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1
    have hp : Function.Injective p :=
      (actual_cut_subpath_injective
        (properPath b) b.property.1.injective 0 u hu0).1
    have hq : Function.Injective q :=
      (actual_cut_subpath_injective
        (properPath a0.val) a0.val.property.1.injective v 1 hv1).1
    have hmeet (s t : Interval) (he : p s = q t) : s = 1 ∧ t = 0 := by
      have hvle := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hv1.le t).1
      have hh := htail _ _ hvle he
      have hs := congrArg Subtype.val hh.1
      have ht := congrArg Subtype.val hh.2
      change (1-(s:ℝ))*0+(s:ℝ)*(u:ℝ) = (u:ℝ) at hs
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1 = (v:ℝ) at ht
      have hupos : (0:ℝ) < u := hu0
      have hvlt : (v:ℝ) < 1 := hv1
      constructor
      · apply Subtype.ext
        change (s:ℝ) = 1
        nlinarith
      · apply Subtype.ext
        change (t:ℝ) = 0
        nlinarith
    have hpb (s : Interval) (hb : p s ∈ boundaryQ S x R) : s = 0 := by
      have hh := (proper_boundary_parameters b
        (CurveComplex.BranchedDoubleCover.intervalAffine 0 u s)).1 hb
      have hupos : (0:ℝ) < u := hu0
      have hult : (u:ℝ) < 1 := hu1
      rcases hh with hh | hh
      · have he := congrArg Subtype.val hh
        change (1-(s:ℝ))*0+(s:ℝ)*(u:ℝ) = 0 at he
        apply Subtype.ext
        change (s:ℝ) = 0
        nlinarith
      · have he := congrArg Subtype.val hh
        change (1-(s:ℝ))*0+(s:ℝ)*(u:ℝ) = 1 at he
        have hsle : (s:ℝ) ≤ 1 := s.property.2
        have hs0 : (0:ℝ) ≤ s := s.property.1
        nlinarith
    have hqb (t : Interval) (hb : q t ∈ boundaryQ S x R) : t = 1 := by
      have hh := (proper_boundary_parameters a0.val
        (CurveComplex.BranchedDoubleCover.intervalAffine v 1 t)).1 hb
      have hvpos : (0:ℝ) < v := hv0
      have hvlt : (v:ℝ) < 1 := hv1
      rcases hh with hh | hh
      · have he := congrArg Subtype.val hh
        change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1 = 0 at he
        have ht0 : (0:ℝ) ≤ t := t.property.1
        have ht1 : (t:ℝ) ≤ 1 := t.property.2
        nlinarith
      · have he := congrArg Subtype.val hh
        change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1 = 1 at he
        apply Subtype.ext
        change (t:ℝ) = 1
        nlinarith
    obtain ⟨d, himage, hd0, hd1⟩ := splice_proper p q hp hq hmeet
      b.property.2.1 a0.val.property.2.2.1 hpb hqb
    exact ⟨d, hd0, hd1, himage⟩
  have actual_terminal_crossing (σ : Finset (ArcVertex S x R))
      (rep : ↥σ → EssentialProperArc S x R)
      (hfinite : ∀ w, (Set.range a0.val.val ∩ Set.range (rep w).val.val).Finite)
      (hends : ∀ w, a0.val.val 0 ∉ Set.range (rep w).val.val ∧
        a0.val.val 1 ∉ Set.range (rep w).val.val)
      (hcontact : ∃ w t, a0.val.val t ∈ Set.range (rep w).val.val) :
      ∃ (w : ↥σ) (u v : Interval),
        0 < u ∧ u < 1 ∧ 0 < v ∧ v < 1 ∧
        (rep w).val.val u = a0.val.val v ∧
        (∀ w' t, v < t → a0.val.val t ∉ Set.range (rep w').val.val) ∧
        (∀ s t : Interval, v ≤ t → (rep w).val.val s = a0.val.val t →
          s = u ∧ t = v) := by
    let C : Set Interval := {t | ∃ w, a0.val.val t ∈ Set.range (rep w).val.val}
    have hf : C.Finite := by
      have hsingle (w : ↥σ) : {t : Interval | a0.val.val t ∈
          Set.range (rep w).val.val}.Finite := by
        have hh := (hfinite w).preimage a0.val.property.1.injective.injOn
        have he : a0.val.val ⁻¹' (Set.range a0.val.val ∩ Set.range (rep w).val.val) =
            {t | a0.val.val t ∈ Set.range (rep w).val.val} := by
          ext t
          simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_range_self, true_and]
        rwa [he] at hh
      have hh := Set.finite_iUnion hsingle
      exact hh.subset (fun t ht => Set.mem_iUnion.mpr ht)
    let T := hf.toFinset
    have hn : T.Nonempty := by
      obtain ⟨w,t,ht⟩ := hcontact
      exact ⟨t, hf.mem_toFinset.mpr ⟨w,ht⟩⟩
    let v := T.max' hn
    have hvC : v ∈ C := hf.mem_toFinset.mp (Finset.max'_mem T hn)
    obtain ⟨w,u,hu⟩ := hvC
    have hv0ne : v ≠ 0 := by
      intro he
      exact (hends w).1 ⟨u,hu.trans (congrArg a0.val.val he)⟩
    have hv1ne : v ≠ 1 := by
      intro he
      exact (hends w).2 ⟨u,hu.trans (congrArg a0.val.val he)⟩
    have hv0 : 0 < v := lt_of_le_of_ne v.property.1 hv0ne.symm
    have hv1 : v < 1 := lt_of_le_of_ne v.property.2 hv1ne
    have hu0ne : u ≠ 0 := by
      intro he
      have hbi : (rep w).val.val u = (rep w).val.val 0 := congrArg (rep w).val.val he
      have hb : (rep w).val.val u ∈ boundaryQ S x R :=
        hbi.symm ▸ (rep w).val.property.2.1
      exact a0.val.property.2.2.2 v ⟨hv0,hv1⟩ (hu ▸ hb)
    have hu1ne : u ≠ 1 := by
      intro he
      have hbi : (rep w).val.val u = (rep w).val.val 1 := congrArg (rep w).val.val he
      have hb : (rep w).val.val u ∈ boundaryQ S x R :=
        hbi.symm ▸ (rep w).val.property.2.2.1
      exact a0.val.property.2.2.2 v ⟨hv0,hv1⟩ (hu ▸ hb)
    have hbound (w' : ↥σ) (t : Interval)
        (ht : a0.val.val t ∈ Set.range (rep w').val.val) : t ≤ v :=
      Finset.le_max' T t (hf.mem_toFinset.mpr ⟨w',ht⟩)
    refine ⟨w,u,v,lt_of_le_of_ne u.property.1 hu0ne.symm,
      lt_of_le_of_ne u.property.2 hu1ne,hv0,hv1,hu,?_,?_⟩
    · intro w' t ht hm
      exact (not_le_of_gt ht) (hbound w' t hm)
    · intro s t ht he
      have htv : t = v := le_antisymm (hbound w t ⟨s,he⟩) ht
      refine ⟨(rep w).val.property.1.injective ?_, htv⟩
      exact he.trans ((congrArg a0.val.val htv).trans hu.symm)
  have reverse_proper (b : ProperArc S x R) :
      ∃ r : ProperArc S x R, ∀ t, r.val t = b.val (unitInterval.symmHomeomorph t) := by
    let f := b.val.comp (⟨unitInterval.symmHomeomorph,
      unitInterval.symmHomeomorph.continuous⟩ : C(Interval,Interval))
    have hr0 : unitInterval.symmHomeomorph 0 = 1 := by apply Subtype.ext; norm_num
    have hr1 : unitInterval.symmHomeomorph 1 = 0 := by apply Subtype.ext; norm_num
    refine ⟨⟨f,b.property.1.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_,?_⟩,
      fun _ => rfl⟩
    · change b.val (unitInterval.symmHomeomorph 0) ∈ boundaryQ S x R
      rw [hr0]
      exact b.property.2.2.1
    · change b.val (unitInterval.symmHomeomorph 1) ∈ boundaryQ S x R
      rw [hr1]
      exact b.property.2.1
    · intro t ht hb
      have hh := (proper_boundary_parameters b (unitInterval.symmHomeomorph t)).1 hb
      have ht0 : (0:ℝ) < t := ht.1
      have ht1 : (t:ℝ) < 1 := ht.2
      rcases hh with hh | hh
      · have he := congrArg Subtype.val hh
        change 1-(t:ℝ) = 0 at he
        linarith
      · have he := congrArg Subtype.val hh
        change 1-(t:ℝ) = 1 at he
        linarith
  have terminal_two_branches_exact (b : ProperArc S x R) (u v : Interval)
      (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
      (hcross : b.val u = a0.val.val v)
      (htail : ∀ s t : Interval, v ≤ t → b.val s = a0.val.val t → s = u ∧ t = v) :
      ∃ d e : ProperArc S x R,
        d.val 0 = b.val 0 ∧ e.val 0 = b.val 1 ∧
        d.val 1 = a0.val.val 1 ∧ e.val 1 = a0.val.val 1 ∧
        (Set.range d.val =
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) ∧
        (Set.range e.val =
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) := by
    obtain ⟨d,hd0,hd1,hdimage⟩ := terminal_left_branch b u v hu0 hu1 hv0 hv1 hcross htail
    obtain ⟨r,hr⟩ := reverse_proper b
    let u' := unitInterval.symmHomeomorph u
    have hu'0 : 0 < u' := by
      change (0:ℝ) < 1-(u:ℝ)
      have hu : (u:ℝ) < 1 := hu1
      linarith
    have hu'1 : u' < 1 := by
      change 1-(u:ℝ) < (1:ℝ)
      have hu : (0:ℝ) < u := hu0
      linarith
    have hrev (t : Interval) : unitInterval.symmHomeomorph
        (unitInterval.symmHomeomorph t) = t := by
      apply Subtype.ext
      change 1-(1-(t:ℝ)) = (t:ℝ)
      ring
    have hrCross : r.val u' = a0.val.val v := by
      rw [hr, hrev]
      exact hcross
    have hrTail (s t : Interval) (ht : v ≤ t) (he : r.val s = a0.val.val t) :
        s = u' ∧ t = v := by
      rw [hr] at he
      have hh := htail _ _ ht he
      refine ⟨?_,hh.2⟩
      exact (hrev s).symm.trans (congrArg unitInterval.symmHomeomorph hh.1)
    obtain ⟨e,he0,he1,heimage⟩ := terminal_left_branch r u' v hu'0 hu'1 hv0 hv1
      hrCross hrTail
    have hr0 : r.val 0 = b.val 1 := by
      rw [hr]
      congr 1
      apply Subtype.ext
      norm_num
    have hreversecut :
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath r) 0 u') =
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symmHomeomorph t,?_⟩
        change b.val (CurveComplex.BranchedDoubleCover.intervalAffine u 1
          (unitInterval.symmHomeomorph t)) =
          r.val (CurveComplex.BranchedDoubleCover.intervalAffine 0 u' t)
        rw [hr]
        apply congrArg b.val
        apply Subtype.ext
        change (1-(1-(t:ℝ)))*(u:ℝ)+(1-(t:ℝ))*1 =
          1-((1-(t:ℝ))*0+(t:ℝ)*(1-(u:ℝ)))
        ring
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symmHomeomorph t,?_⟩
        change r.val (CurveComplex.BranchedDoubleCover.intervalAffine 0 u'
          (unitInterval.symmHomeomorph t)) =
          b.val (CurveComplex.BranchedDoubleCover.intervalAffine u 1 t)
        rw [hr]
        apply congrArg b.val
        apply Subtype.ext
        change 1-((1-(1-(t:ℝ)))*0+(1-(t:ℝ))*(1-(u:ℝ))) =
          (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*1
        ring
    refine ⟨d,e,hd0,he0.trans hr0,hd1,he1,hdimage,?_⟩
    rwa [hreversecut] at heimage
  /- The two raw branches share EXACTLY the actual anchor terminal tail.
  This is the geometry available to disk cancellation; their disk fillings
  must not be presumed disjoint merely because the old-b cuts are disjoint. -/
  have actual_embedded_square_boundary_in_closed_ball_bounds_entire_square (B : Interval × Interval → Plane) (hB : Topology.IsEmbedding B)
      (hb : ∀ z : Interval × Interval,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
        B z∈Metric.closedBall (0 : Plane) 1) :
      Set.range B ⊆ Metric.closedBall (0 : Plane) 1 := by
    clear * - B hB hb
    classical
    obtain ⟨z,hz,hmax⟩ := (isCompact_univ : IsCompact (univ : Set (Interval × Interval))).exists_isMaxOn
      (Set.univ_nonempty) (continuous_norm.comp hB.continuous).continuousOn
    have hbound : ‖B z‖≤1 := by
      by_contra hn
      have hnorm : 1<‖B z‖ := lt_of_not_ge hn
      have hno : ¬(z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) := by
        intro he
        have h := hb z he
        have hle : ‖B z‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using h
        exact (not_le_of_gt hnorm) hle
      have hz10 : (0 : ℝ)<(z.1:ℝ) := lt_of_le_of_ne z.1.property.1
        (by intro he; exact hno (Or.inl (Subtype.ext he.symm)))
      have hz11 : (z.1:ℝ)<1 := lt_of_le_of_ne z.1.property.2
        (by intro he; exact hno (Or.inr (Or.inl (Subtype.ext he))))
      have hz20 : (0 : ℝ)<(z.2:ℝ) := lt_of_le_of_ne z.2.property.1
        (by intro he; exact hno (Or.inr (Or.inr (Or.inl (Subtype.ext he.symm)))))
      have hz21 : (z.2:ℝ)<1 := lt_of_le_of_ne z.2.property.2
        (by intro he; exact hno (Or.inr (Or.inr (Or.inr (Subtype.ext he)))))
      let p : Plane → Interval × Interval := fun v =>
        (Set.projIcc 0 1 zero_le_one (v 0),Set.projIcc 0 1 zero_le_one (v 1))
      have hpc : Continuous p := by dsimp [p]; fun_prop
      let O : Set Plane := {v | 0<v 0 ∧ v 0<1 ∧ 0<v 1 ∧ v 1<1}
      have hO : IsOpen O := by
        have h0 : Continuous (fun v : Plane => v 0) := by fun_prop
        have h1 : Continuous (fun v : Plane => v 1) := by fun_prop
        exact (isOpen_lt continuous_const h0).inter
          ((isOpen_lt h0 continuous_const).inter
            ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))
      have hp (v : Plane) (hv : v∈O) :
          p v=(⟨v 0,⟨hv.1.le,hv.2.1.le⟩⟩,⟨v 1,⟨hv.2.2.1.le,hv.2.2.2.le⟩⟩) := by
        dsimp [p]
        rw [Set.projIcc_of_mem zero_le_one ⟨hv.1.le,hv.2.1.le⟩,
          Set.projIcc_of_mem zero_le_one ⟨hv.2.2.1.le,hv.2.2.2.le⟩]
      have hinj : Set.InjOn (B ∘ p) O := by
        intro v hv w hw he
        have h := hB.injective he
        rw [hp v hv,hp w hw] at h
        have h0 := congrArg (fun t : Interval × Interval => (t.1:ℝ)) h
        have h1 := congrArg (fun t : Interval × Interval => (t.2:ℝ)) h
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have hOpen := LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
        (B ∘ p) O hO (hB.continuous.comp hpc).continuousOn hinj
      let v : Plane := Plane.mk (z.1:ℝ) (z.2:ℝ)
      have hv : v∈O := ⟨hz10,hz11,hz20,hz21⟩
      have hpv : p v=z := by
        rw [hp v hv]
        exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
      have hzOpen : B z∈(B ∘ p) '' O := ⟨v,hv,by simp only [Function.comp_apply,hpv]⟩
      obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp hOpen (B z) hzOpen
      let a : ℝ := 1+ε/(2*‖B z‖)
      have hnpos : 0<‖B z‖ := zero_lt_one.trans hnorm
      have hapos : 0<a := by dsimp [a]; positivity
      have hae : (a-1)*‖B z‖=ε/2 := by dsimp [a]; field_simp; ring
      have hdist : dist (a • B z) (B z)<ε := by
        have he : a • B z-B z=(a-1) • B z := by rw [sub_smul,one_smul]
        rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs]
        have ha1 : 0<a-1 := by
          have hd : 0<ε/(2*‖B z‖) := div_pos hε (mul_pos (by norm_num) hnpos)
          dsimp [a]
          linarith only [hd]
        rw [abs_of_pos ha1,hae]
        linarith only [hε]
      obtain ⟨w,hw,he⟩ := hεsub hdist
      have hle : ‖a • B z‖≤‖B z‖ := he ▸ hmax (Set.mem_univ (p w))
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hapos] at hle
      have hprod : a*‖B z‖=‖B z‖+ε/2 := by nlinarith only [hae]
      rw [hprod] at hle
      linarith only [hle,hε]
    rintro y ⟨w,rfl⟩
    have hle : ‖B w‖≤‖B z‖ := hmax (Set.mem_univ w)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hle.trans hbound
  have actual_prescribed_four_arc_square_inside_actual_originalQ_disk
      (P Qe E Rr : C(Interval,Q S x R))
      (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Qe)
      (hE : Topology.IsEmbedding E) (hR : Topology.IsEmbedding Rr)
      (hPE : P 0=E 0) (hPR : P 1=Rr 0) (hQE : Qe 0=E 1) (hQR : Qe 1=Rr 1)
      (hPEm : ∀ s t,P s=E t → s=0 ∧ t=0)
      (hPRm : ∀ s t,P s=Rr t → s=1 ∧ t=0)
      (hQEm : ∀ s t,Qe s=E t → s=0 ∧ t=1)
      (hQRm : ∀ s t,Qe s=Rr t → s=1 ∧ t=1)
      (hPQ : Disjoint (Set.range P) (Set.range Qe))
      (hER : Disjoint (Set.range E) (Set.range Rr))
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hPD : Set.range P ⊆ Set.range D) (hQD : Set.range Qe ⊆ Set.range D)
      (hED : Set.range E ⊆ Set.range D) (hRD : Set.range Rr ⊆ Set.range D) :
      ∃ B : C(Interval × Interval,Q S x R),Topology.IsEmbedding B ∧
        (∀ u,B (u,0)=P u) ∧ (∀ u,B (u,1)=Qe u) ∧
        (∀ v,B (0,v)=E v) ∧ (∀ v,B (1,v)=Rr v) ∧ Set.range B ⊆ Set.range D := by
    let e := hD.toHomeomorph
    let pull (f : C(Interval,Q S x R)) (hf : Set.range f ⊆ Set.range D) : C(Interval,Plane) :=
      ⟨fun t => (e.symm ⟨f t,hf (Set.mem_range_self t)⟩).val,
        continuous_subtype_val.comp (e.symm.continuous.comp (f.continuous.subtype_mk _))⟩
    have heq (f g : C(Interval,Q S x R))
        (hf : Set.range f ⊆ Set.range D) (hg : Set.range g ⊆ Set.range D) (s t : Interval) :
        pull f hf s=pull g hg t ↔ f s=g t := by
      constructor
      · intro he
        exact congrArg (fun y : Set.range D => y.val) (e.symm.injective (Subtype.ext he))
      · intro he
        exact congrArg (fun y : Set.range D => (e.symm y).val) (Subtype.ext he)
    have hpull (f : C(Interval,Q S x R)) (hf : Set.range f ⊆ Set.range D)
        (hfi : Topology.IsEmbedding f) : Topology.IsEmbedding (pull f hf) :=
      ((pull f hf).continuous.isClosedEmbedding (fun s t he =>
        hfi.injective ((heq f f hf hf s t).mp he))).isEmbedding
    have hdisj (f g : C(Interval,Q S x R))
        (hf : Set.range f ⊆ Set.range D) (hg : Set.range g ⊆ Set.range D)
        (hfg : Disjoint (Set.range f) (Set.range g)) :
        Disjoint (Set.range (pull f hf)) (Set.range (pull g hg)) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs⟩ ⟨t,ht⟩
      have he := (heq f g hf hg s t).mp (hs.trans ht.symm)
      exact Set.disjoint_left.mp hfg (Set.mem_range_self s) ⟨t,he.symm⟩
    obtain ⟨B,hB,hBP,hBQ,hBE,hBR⟩ :=
      CurveComplex.G3Review.actual_four_arc_cycle_has_prescribed_embedded_square
        (pull P hPD) (pull Qe hQD) (pull E hED) (pull Rr hRD)
        (hpull P hPD hP) (hpull Qe hQD hQ) (hpull E hED hE) (hpull Rr hRD hR)
        ((heq P E hPD hED 0 0).mpr hPE) ((heq P Rr hPD hRD 1 0).mpr hPR)
        ((heq Qe E hQD hED 0 1).mpr hQE) ((heq Qe Rr hQD hRD 1 1).mpr hQR)
        (fun s t he => hPEm s t ((heq P E hPD hED s t).mp he))
        (fun s t he => hPRm s t ((heq P Rr hPD hRD s t).mp he))
        (fun s t he => hQEm s t ((heq Qe E hQD hED s t).mp he))
        (fun s t he => hQRm s t ((heq Qe Rr hQD hRD s t).mp he))
        (hdisj P Qe hPD hQD hPQ) (hdisj E Rr hED hRD hER)
    have hBball : Set.range B ⊆ Metric.closedBall (0 : Plane) 1 := by
      apply actual_embedded_square_boundary_in_closed_ball_bounds_entire_square B hB
      intro z hz
      rcases hz with h0 | h1 | h2 | h3
      · have he : z=(0,z.2) := Prod.ext h0 rfl
        rw [he,hBE]
        exact (e.symm ⟨E z.2,hED (Set.mem_range_self z.2)⟩).property
      · have he : z=(1,z.2) := Prod.ext h1 rfl
        rw [he,hBR]
        exact (e.symm ⟨Rr z.2,hRD (Set.mem_range_self z.2)⟩).property
      · have he : z=(z.1,0) := Prod.ext rfl h2
        rw [he,hBP]
        exact (e.symm ⟨P z.1,hPD (Set.mem_range_self z.1)⟩).property
      · have he : z=(z.1,1) := Prod.ext rfl h3
        rw [he,hBQ]
        exact (e.symm ⟨Qe z.1,hQD (Set.mem_range_self z.1)⟩).property
    let lift : C(Interval × Interval,Metric.closedBall (0 : Plane) 1) :=
      ⟨fun z => ⟨B z,hBball (Set.mem_range_self z)⟩,hB.continuous.subtype_mk _⟩
    have hlift : Topology.IsEmbedding lift := (lift.continuous.isClosedEmbedding (by
      intro z w he
      exact hB.injective (congrArg (fun v : Metric.closedBall (0 : Plane) 1 => v.val) he))).isEmbedding
    let F : C(Interval × Interval,Q S x R) := D.comp lift
    have hDpull (f : C(Interval,Q S x R)) (hf : Set.range f ⊆ Set.range D) (t : Interval) :
        D (e.symm ⟨f t,hf (Set.mem_range_self t)⟩)=f t :=
      congrArg (fun y : Set.range D => y.val) (e.apply_symm_apply ⟨f t,hf (Set.mem_range_self t)⟩)
    refine ⟨F,hD.comp hlift,?_,?_,?_,?_,?_⟩
    · intro u
      have he : lift (u,0)=e.symm ⟨P u,hPD (Set.mem_range_self u)⟩ := Subtype.ext (hBP u)
      change D (lift (u,0))=P u
      rw [he]; exact hDpull P hPD u
    · intro u
      have he : lift (u,1)=e.symm ⟨Qe u,hQD (Set.mem_range_self u)⟩ := Subtype.ext (hBQ u)
      change D (lift (u,1))=Qe u
      rw [he]; exact hDpull Qe hQD u
    · intro v
      have he : lift (0,v)=e.symm ⟨E v,hED (Set.mem_range_self v)⟩ := Subtype.ext (hBE v)
      change D (lift (0,v))=E v
      rw [he]; exact hDpull E hED v
    · intro v
      have he : lift (1,v)=e.symm ⟨Rr v,hRD (Set.mem_range_self v)⟩ := Subtype.ext (hBR v)
      change D (lift (1,v))=Rr v
      rw [he]; exact hDpull Rr hRD v
    · rintro z ⟨t,rfl⟩; exact ⟨lift t,rfl⟩
  have actual_three_arc_boundary_cycle_has_prescribed_rectangle_in_actual_disk
      (P T q : C(Interval,Q S x R))
      (hP : Topology.IsEmbedding P) (hT : Topology.IsEmbedding T) (hq : Topology.IsEmbedding q)
      (hPT : P 1=T 0) (hq0 : q 0=P 0) (hq1 : q 1=T 1)
      (hPTm : ∀ s t,P s=T t → s=1 ∧ t=0)
      (hPqm : ∀ s t,P s=q t → s=0 ∧ t=0)
      (hTqm : ∀ s t,T s=q t → s=1 ∧ t=1)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hPD : Set.range P ⊆ Set.range D) (hTD : Set.range T ⊆ Set.range D)
      (hqD : Set.range q ⊆ Set.range D) :
      ∃ B : C(Interval × Interval,Q S x R),Topology.IsEmbedding B ∧
        (∀ u,B (u,0)=P u) ∧ (∀ v,B (1,v)=T v) ∧
        Set.range B ⊆ Set.range D ∧
        (∀ v,B (0,v)∈Set.range q) ∧ (∀ u,B (u,1)∈Set.range q) := by
    let m : Interval := ⟨1/2,by constructor <;> norm_num⟩
    have hm0 : (0 : Interval) < m := by change (0 : ℝ)<1/2; norm_num
    have hm1 : m < (1 : Interval) := by change (1/2 : ℝ)<1; norm_num
    let qp : Path (q 0) (q 1) := { toContinuousMap := q, source' := rfl, target' := rfl }
    let ep := CurveComplex.BranchedDoubleCover.actualSubpath qp 0 m
    let fp := CurveComplex.BranchedDoubleCover.actualSubpath qp m 1
    let E := ep.toContinuousMap
    let F := fp.toContinuousMap
    have hE : Topology.IsEmbedding E :=
      (ep.continuous.isClosedEmbedding (actual_cut_subpath_injective qp hq.injective 0 m hm0).1).isEmbedding
    have hF : Topology.IsEmbedding F :=
      (fp.continuous.isClosedEmbedding (actual_cut_subpath_injective qp hq.injective m 1 hm1).1).isEmbedding
    have hPE : P 0=E 0 := hq0.symm.trans ep.source'.symm
    have hFE : F 0=E 1 := fp.source'.trans ep.target'.symm
    have hFT : F 1=T 1 := fp.target'.trans hq1
    have hPEm (s t : Interval) (he : P s=E t) : s=0 ∧ t=0 := by
      have hm := hPqm s (CurveComplex.BranchedDoubleCover.intervalAffine 0 m t) he
      refine ⟨hm.1,Subtype.ext ?_⟩
      have h := congrArg Subtype.val hm.2
      change (1-(t:ℝ))*0+(t:ℝ)*(1/2)=0 at h
      change (t:ℝ)=0
      linarith only [h]
    have hFEm (s t : Interval) (he : F s=E t) : s=0 ∧ t=1 := by
      have hc := congrArg Subtype.val (hq.injective he)
      change (1-(s:ℝ))*(1/2)+(s:ℝ)*1=(1-(t:ℝ))*0+(t:ℝ)*(1/2) at hc
      constructor
      · apply Subtype.ext
        change (s:ℝ)=0
        nlinarith only [hc,s.property.1,t.property.2]
      · apply Subtype.ext
        change (t:ℝ)=1
        nlinarith only [hc,s.property.1,t.property.2]
    have hFTm (s t : Interval) (he : F s=T t) : s=1 ∧ t=1 := by
      have hm := hTqm t (CurveComplex.BranchedDoubleCover.intervalAffine m 1 s) he.symm
      refine ⟨Subtype.ext ?_,hm.1⟩
      have h := congrArg Subtype.val hm.2
      change (1-(s:ℝ))*(1/2)+(s:ℝ)*1=1 at h
      change (s:ℝ)=1
      linarith only [h]
    have hPF : Disjoint (Set.range P) (Set.range F) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs⟩ ⟨t,ht⟩
      have hm := hPqm s (CurveComplex.BranchedDoubleCover.intervalAffine m 1 t) (hs.trans ht.symm)
      have h := congrArg Subtype.val hm.2
      change (1-(t:ℝ))*(1/2)+(t:ℝ)*1=0 at h
      nlinarith only [h,t.property.1]
    have hET : Disjoint (Set.range E) (Set.range T) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨s,hs⟩ ⟨t,ht⟩
      have hm := hTqm t (CurveComplex.BranchedDoubleCover.intervalAffine 0 m s) (ht.trans hs.symm)
      have h := congrArg Subtype.val hm.2
      change (1-(s:ℝ))*0+(s:ℝ)*(1/2)=1 at h
      nlinarith only [h,s.property.2]
    have hEq : Set.range E ⊆ Set.range q := by
      rintro z ⟨t,rfl⟩; exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine 0 m t,rfl⟩
    have hFq : Set.range F ⊆ Set.range q := by
      rintro z ⟨t,rfl⟩; exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine m 1 t,rfl⟩
    obtain ⟨B,hB,hBP,hBF,hBE,hBT,hBD⟩ := actual_prescribed_four_arc_square_inside_actual_originalQ_disk
      P F E T hP hF hE hT hPE hPT hFE hFT hPEm hPTm hFEm hFTm hPF hET
      D hD hPD (hFq.trans hqD) (hEq.trans hqD) hTD
    refine ⟨B,hB,hBP,hBT,hBD,?_,?_⟩
    · intro v; rw [hBE]; exact hEq (Set.mem_range_self v)
    · intro u; rw [hBF]; exact hFq (Set.mem_range_self u)
  have actual_unit_disk_square_homeomorph_preserves_boundary : ∃ e : Metric.closedBall (0 : Plane) 1 ≃ₜ Interval × Interval,
      e '' {z | z.val∈Metric.sphere (0 : Plane) 1}=
        {z | z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1} := by
    classical
    have bound (z : Plane.closedSquare 0 1) : |z.val 0|≤1 ∧ |z.val 1|≤1 := by
      have hz : max |z.val 0| |z.val 1|≤1 := mem_closedSquare_zero_one.mp z.property
      exact ⟨(le_max_left _ _).trans hz,(le_max_right _ _).trans hz⟩
    let f : Plane.closedSquare 0 1 → Interval × Interval := fun z =>
      (⟨(z.val 0+1)/2,by have h := abs_le.mp (bound z).1; constructor <;> linarith only [h.1,h.2]⟩,
       ⟨(z.val 1+1)/2,by have h := abs_le.mp (bound z).2; constructor <;> linarith only [h.1,h.2]⟩)
    let k : Interval × Interval → Plane.closedSquare 0 1 := fun z =>
      ⟨Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1),by
        apply mem_closedSquare_zero_one.mpr
        change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1|≤1
        apply max_le
        · apply abs_le.mpr; constructor <;> linarith only [z.1.property.1,z.1.property.2]
        · apply abs_le.mpr; constructor <;> linarith only [z.2.property.1,z.2.property.2]⟩
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hk : Continuous k := by dsimp [k]; fun_prop
    let c : Plane.closedSquare 0 1 ≃ₜ Interval × Interval :=
      { toFun := f, invFun := k,
        left_inv := by
          intro z
          apply Subtype.ext
          ext i
          fin_cases i
          · change 2*((z.val 0+1)/2)-1=z.val 0; ring
          · change 2*((z.val 1+1)/2)-1=z.val 1; ring,
        right_inv := by
          intro z
          apply Prod.ext <;> apply Subtype.ext
          · change (2*(z.1:ℝ)-1+1)/2=(z.1:ℝ); ring
          · change (2*(z.2:ℝ)-1+1)/2=(z.2:ℝ); ring,
        continuous_toFun := hf, continuous_invFun := hk }
    have hcb (z : Plane.closedSquare 0 1) : z.val∈modelCurve ↔
        (c z).1=0 ∨ (c z).1=1 ∨ (c z).2=0 ∨ (c z).2=1 := by
      have hz0 := abs_le.mp (bound z).1
      have hz1 := abs_le.mp (bound z).2
      constructor
      · intro he
        by_contra hn
        have hnone := not_or.mp hn
        have hnone2 := not_or.mp hnone.2
        have hnone3 := not_or.mp hnone2.2
        have h0a : (z.val 0+1)/2≠0 := fun h => hnone.1 (Subtype.ext h)
        have h0b : (z.val 0+1)/2≠1 := fun h => hnone2.1 (Subtype.ext h)
        have h1a : (z.val 1+1)/2≠0 := fun h => hnone3.1 (Subtype.ext h)
        have h1b : (z.val 1+1)/2≠1 := fun h => hnone3.2 (Subtype.ext h)
        have h0 : |z.val 0|<1 := abs_lt.mpr ⟨by
          apply lt_of_le_of_ne hz0.1
          intro h; apply h0a; linarith only [h],by
          apply lt_of_le_of_ne hz0.2
          intro h; apply h0b; linarith only [h]⟩
        have h1 : |z.val 1|<1 := abs_lt.mpr ⟨by
          apply lt_of_le_of_ne hz1.1
          intro h; apply h1a; linarith only [h],by
          apply lt_of_le_of_ne hz1.2
          intro h; apply h1b; linarith only [h]⟩
        have hlt := max_lt h0 h1
        change max |z.val 0| |z.val 1|=1 at he
        exact (ne_of_lt hlt) he
      · intro he
        change max |z.val 0| |z.val 1|=1
        apply le_antisymm (max_le (bound z).1 (bound z).2)
        rcases he with he | he | he | he
        · have he0 := congrArg Subtype.val he
          change (z.val 0+1)/2=0 at he0
          have hez : z.val 0=-1 := by linarith only [he0]
          rw [hez,abs_neg,abs_one]; exact le_max_left _ _
        · have he0 := congrArg Subtype.val he
          change (z.val 0+1)/2=1 at he0
          have hez : z.val 0=1 := by linarith only [he0]
          rw [hez,abs_one]; exact le_max_left _ _
        · have he0 := congrArg Subtype.val he
          change (z.val 1+1)/2=0 at he0
          have hez : z.val 1=-1 := by linarith only [he0]
          rw [hez,abs_neg,abs_one]; exact le_max_right _ _
        · have he0 := congrArg Subtype.val he
          change (z.val 1+1)/2=1 at he0
          have hez : z.val 1=1 := by linarith only [he0]
          rw [hez,abs_one]; exact le_max_right _ _
    obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Plane.convex_closedSquare 0 1)
      (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
      (Plane.isBounded_closedSquare 0 1)
    have hcl' : h '' Plane.closedSquare 0 1=Metric.closedBall (0 : Plane) 1 := by
      simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hcl
    have hfront' : h '' modelCurve=Metric.sphere (0 : Plane) 1 := by
      simpa only [←modelCurve_eq_frontier] using hfront
    let a : Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Plane) 1 :=
      (h.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hcl')
    have hab (z : Plane.closedSquare 0 1) : (a z).val∈Metric.sphere (0 : Plane) 1 ↔ z.val∈modelCurve := by
      change h z.val∈Metric.sphere (0 : Plane) 1 ↔ z.val∈modelCurve
      rw [←hfront']
      exact h.injective.mem_set_image
    let e := a.symm.trans c
    refine ⟨e,?_⟩
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hcb (a.symm w)).mp ((hab (a.symm w)).mp (by simpa using hw))
    · intro hz
      refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
      have hx : (c.symm z).val∈modelCurve := (hcb (c.symm z)).mpr (by simpa using hz)
      exact (hab (c.symm z)).mpr hx
  have actual_square_three_boundary_edges_form_embedded_arc :
      ∃ q : C(Interval,Interval × Interval),Topology.IsEmbedding q ∧
        q 0=(0,0) ∧ q 1=(1,0) ∧
        Set.range q={z | z.1=0 ∨ z.1=1 ∨ z.2=1} := by
    let L : Path ((0 : Interval), (0 : Interval)) (0,1) :=
      { toFun := fun t => (0,t), continuous_toFun := by fun_prop, source' := rfl, target' := rfl }
    let U : Path ((0 : Interval), (1 : Interval)) (1,1) :=
      { toFun := fun t => (t,1), continuous_toFun := by fun_prop, source' := rfl, target' := rfl }
    let Rr : Path ((1 : Interval), (1 : Interval)) (1,0) :=
      { toFun := fun t => (1,unitInterval.symm t),
        continuous_toFun := by fun_prop, source' := by simp, target' := by simp }
    have hL : Function.Injective L := fun s t he => congrArg Prod.snd he
    have hU : Function.Injective U := fun s t he => congrArg Prod.fst he
    have hR : Function.Injective Rr := fun s t he =>
      unitInterval.symm_involutive.injective (congrArg Prod.snd he)
    have hLU : Function.Injective (L.trans U) := embedded_arcs_concat_injective L U hL hU (by
      intro s t he
      exact ⟨congrArg Prod.snd he,(congrArg Prod.fst he).symm⟩)
    let LU := L.trans U
    have hLUR : Function.Injective (LU.trans Rr) := embedded_arcs_concat_injective LU Rr hLU hR (by
      intro s t he
      have hmem : LU s∈Set.range L ∪ Set.range U := Path.trans_range L U ▸ Set.mem_range_self s
      rcases hmem with hleft | htop
      · obtain ⟨u,hu⟩ := hleft
        have hf : (0 : Interval)=1 := congrArg Prod.fst (hu.trans he)
        exact False.elim ((show (0 : Interval)≠1 by norm_num) hf)
      · obtain ⟨u,hu⟩ := htop
        have hu1 : u=(1 : Interval) := congrArg Prod.fst (hu.trans he)
        have ht : t=0 := by
          have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ)) (hu.trans he)
          change (1 : ℝ)=1-(t:ℝ) at hh
          apply Subtype.ext
          change (t:ℝ)=0
          linarith only [hh]
        refine ⟨hLU ?_,ht⟩
        exact hu.symm.trans ((congrArg U hu1).trans LU.target'.symm))
    let q := (LU.trans Rr).toContinuousMap
    refine ⟨q,(q.continuous.isClosedEmbedding hLUR).isEmbedding,
      (LU.trans Rr).source',(LU.trans Rr).target',?_⟩
    change Set.range (LU.trans Rr)={z | z.1=0 ∨ z.1=1 ∨ z.2=1}
    rw [Path.trans_range,Path.trans_range]
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · obtain ⟨t,ht⟩ := hz; exact Or.inl (congrArg Prod.fst ht).symm
      · obtain ⟨t,ht⟩ := hz; exact Or.inr (Or.inr (congrArg Prod.snd ht).symm)
      · obtain ⟨t,ht⟩ := hz; exact Or.inr (Or.inl (congrArg Prod.fst ht).symm)
    · rintro (hz | hz | hz)
      · exact Or.inl (Or.inl ⟨z.2,Prod.ext hz.symm rfl⟩)
      · exact Or.inr ⟨unitInterval.symm z.2,Prod.ext hz.symm (unitInterval.symm_involutive z.2)⟩
      · exact Or.inl (Or.inr ⟨z.1,Prod.ext rfl hz.symm⟩)
  have actual_original_proper_arc_square_with_three_boundary_edges_is_parallel
      (b : ProperArc S x R) (F : C(Interval × Interval,Q S x R))
      (hF : Topology.IsEmbedding F)
      (hbottom : Set.range (fun t : Interval => F (t,0))=Set.range b.val)
      (hleft : ∀ t,F (0,t)∈boundaryQ S x R)
      (hright : ∀ t,F (1,t)∈boundaryQ S x R)
      (htop : ∀ t,F (t,1)∈boundaryQ S x R) : boundaryParallel S x R b := by
    obtain ⟨q,hq,hq0,hq1,hqrange⟩ := actual_square_three_boundary_edges_form_embedded_arc
    obtain ⟨e,he⟩ := actual_unit_disk_square_homeomorph_preserves_boundary
    let bd : C(Interval,Q S x R) := F.comp q
    have hbd : Topology.IsEmbedding bd := hF.comp hq
    have hbdB (t : Interval) : bd t∈boundaryQ S x R := by
      have hqt : q t∈{z : Interval × Interval | z.1=0 ∨ z.1=1 ∨ z.2=1} :=
        hqrange ▸ Set.mem_range_self t
      change F (q t)∈boundaryQ S x R
      rcases hqt with h0 | h1 | h2
      · have hz : q t=(0,(q t).2) := Prod.ext h0 rfl
        rw [hz]; exact hleft _
      · have hz : q t=(1,(q t).2) := Prod.ext h1 rfl
        rw [hz]; exact hright _
      · have hz : q t=((q t).1,1) := Prod.ext rfl h2
        rw [hz]; exact htop _
    let D : C(Metric.closedBall (0 : Plane) 1,Q S x R) :=
      F.comp ⟨e,e.continuous⟩
    refine ⟨bd,hbd,hbdB,D,hF.comp e.isEmbedding,?_⟩
    change (F ∘ e) '' {z | z.val∈Metric.sphere (0 : Plane) 1}=
      Set.range b.val ∪ Set.range bd
    rw [Set.image_comp,he]
    apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      rcases hz with h0 | h1 | h2 | h3
      · right
        have hzq : z∈Set.range q := hqrange.symm ▸ (show z.1=0 ∨ z.1=1 ∨ z.2=1 from Or.inl h0)
        obtain ⟨t,ht⟩ := hzq
        exact ⟨t,congrArg F ht⟩
      · right
        have hzq : z∈Set.range q := hqrange.symm ▸ (show z.1=0 ∨ z.1=1 ∨ z.2=1 from Or.inr (Or.inl h1))
        obtain ⟨t,ht⟩ := hzq
        exact ⟨t,congrArg F ht⟩
      · left
        rw [←hbottom]
        exact ⟨z.1,congrArg F (Prod.ext rfl h2.symm)⟩
      · right
        have hzq : z∈Set.range q := hqrange.symm ▸ (show z.1=0 ∨ z.1=1 ∨ z.2=1 from Or.inr (Or.inr h3))
        obtain ⟨t,ht⟩ := hzq
        exact ⟨t,congrArg F ht⟩
    · rintro y (hy | hy)
      · rw [←hbottom] at hy
        obtain ⟨t,ht⟩ := hy
        exact ⟨(t,0),Or.inr (Or.inr (Or.inl rfl)),ht⟩
      · obtain ⟨t,rfl⟩ := hy
        have hqt : (q t).1=0 ∨ (q t).1=1 ∨ (q t).2=1 := by
          have hx : q t∈{z : Interval × Interval | z.1=0 ∨ z.1=1 ∨ z.2=1} :=
            hqrange ▸ Set.mem_range_self t
          exact hx
        refine ⟨q t,?_,rfl⟩
        rcases hqt with h0 | h1 | h2
        · exact Or.inl h0
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inr h2))
  have actual_two_square_gluing_preserves_lower_edge_union
      (L Rr : C(Interval × Interval,Q S x R))
      (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding Rr)
      (hseam : ∀ w,L (0,w)=Rr (0,w))
      (hmeet : Set.range L ∩ Set.range Rr=Set.range (fun w => L (0,w))) :
      ∃ F : C(Interval × Interval,Q S x R),Topology.IsEmbedding F ∧
        (∀ w,F (0,w)=L (1,w)) ∧ (∀ w,F (1,w)=Rr (1,w)) ∧
        (∀ z,∃ t : Interval,F z=L (t,z.2) ∨ F z=Rr (t,z.2)) ∧
        Set.range (fun t : Interval => F (t,0))=
          Set.range (fun t : Interval => L (t,0)) ∪ Set.range (fun t : Interval => Rr (t,0)) := by
    obtain ⟨f,hf,hf0,hf1,hfmid,hfrange,hfiber⟩ :=
      source_glue_two_surface_strips L Rr hL hR hseam hmeet
    let F : C(Interval × Interval,Q S x R) := ⟨f,hf.continuous⟩
    refine ⟨F,hf,hf0,hf1,hfiber,?_⟩
    apply Set.Subset.antisymm
    · rintro y ⟨s,rfl⟩
      obtain ⟨t,ht | ht⟩ := hfiber (s,0)
      · exact Or.inl ⟨t,ht.symm⟩
      · exact Or.inr ⟨t,ht.symm⟩
    · rintro y (⟨s,rfl⟩ | ⟨s,rfl⟩)
      · have hym : L (s,0)∈Set.range f := hfrange.symm ▸ (Or.inl (Set.mem_range_self (s,0)))
        obtain ⟨z,hz⟩ := hym
        obtain ⟨t,ht | ht⟩ := hfiber z
        · have he := hL.injective (ht.symm.trans hz)
          have hw : z.2=0 := congrArg Prod.snd he
          exact ⟨z.1,(congrArg f (show (z.1,0)=z from Prod.ext rfl hw.symm)).trans hz⟩
        · have hint : L (s,0)∈Set.range L ∩ Set.range Rr :=
            ⟨Set.mem_range_self (s,0),⟨(t,z.2),ht.symm.trans hz⟩⟩
          obtain ⟨w,hw⟩ := hmeet ▸ hint
          have hw0 : w=0 := congrArg Prod.snd (hL.injective hw)
          have he : Rr (t,z.2)=Rr (0,w) := (ht.symm.trans hz).trans (hw.symm.trans (hseam w))
          have hz0 : z.2=0 := (congrArg Prod.snd (hR.injective he)).trans hw0
          exact ⟨z.1,(congrArg f (show (z.1,0)=z from Prod.ext rfl hz0.symm)).trans hz⟩
      · have hym : Rr (s,0)∈Set.range f := hfrange.symm ▸ (Or.inr (Set.mem_range_self (s,0)))
        obtain ⟨z,hz⟩ := hym
        obtain ⟨t,ht | ht⟩ := hfiber z
        · have hint : Rr (s,0)∈Set.range L ∩ Set.range Rr :=
            ⟨⟨(t,z.2),ht.symm.trans hz⟩,Set.mem_range_self (s,0)⟩
          obtain ⟨w,hw⟩ := hmeet ▸ hint
          have hw0 : w=0 := congrArg Prod.snd (hR.injective ((hseam w).symm.trans hw))
          have he : L (t,z.2)=L (0,w) := (ht.symm.trans hz).trans hw.symm
          have hz0 : z.2=0 := (congrArg Prod.snd (hL.injective he)).trans hw0
          exact ⟨z.1,(congrArg f (show (z.1,0)=z from Prod.ext rfl hz0.symm)).trans hz⟩
        · have he := hR.injective (ht.symm.trans hz)
          have hw : z.2=0 := congrArg Prod.snd he
          exact ⟨z.1,(congrArg f (show (z.1,0)=z from Prod.ext rfl hw.symm)).trans hz⟩
  have actual_jordan_disk_in_closed_unit_ball
      (C : Set Plane) (hC : Schoenflies.IsJordanCurve C)
      (hball : C ⊆ Metric.closedBall (0 : Plane) 1) :
      ∃ d : C(Metric.closedBall (0 : Plane) 1,Plane), Topology.IsEmbedding d ∧
        d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C ∧
        Set.range d ⊆ Metric.closedBall (0 : Plane) 1 := by
    classical
    obtain ⟨square,hSquare,hBoundary⟩ := exists_embedded_square_disc_of_jordan hC
    obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Plane.convex_closedSquare 0 1)
      (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
      (Plane.isBounded_closedSquare 0 1)
    have hcl' : h '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
      simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hcl
    have hfront' : h '' Schoenflies.modelCurve = Metric.sphere (0 : Plane) 1 := by
      simpa only [← Schoenflies.modelCurve_eq_frontier] using hfront
    let e : Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Plane) 1 :=
      (h.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hcl')
    have he (x : Plane.closedSquare 0 1) : (e x).val = h x.val := rfl
    have heB : e.symm '' {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.sphere (0 : Plane) 1} =
        {x : Plane.closedSquare 0 1 | x.val ∈ Schoenflies.modelCurve} := by
      ext x
      constructor
      · rintro ⟨y,hy,hxy⟩
        have hy' : (e x).val ∈ Metric.sphere (0 : Plane) 1 := by
          rw [←hxy,e.apply_symm_apply]; exact hy
        rw [he,←hfront'] at hy'
        obtain ⟨z,hz,hzx⟩ := hy'
        change x.val ∈ Schoenflies.modelCurve
        rw [←h.injective hzx]
        exact hz
      · intro hx
        refine ⟨e x,?_,e.symm_apply_apply x⟩
        change (e x).val ∈ Metric.sphere (0 : Plane) 1
        rw [he,←hfront']
        exact Set.mem_image_of_mem h hx
    let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
      ⟨fun x => square (e.symm x),square.continuous.comp e.symm.continuous⟩
    have hd : Topology.IsEmbedding d := hSquare.comp e.symm.isEmbedding
    have hdB : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C := by
      change (square ∘ e.symm) '' _ = C
      rw [Set.image_comp,heB]
      exact hBoundary
    have hinside : Schoenflies.inside C ⊆ Metric.closedBall (0 : Plane) 1 := by
      intro x hx
      by_contra hxnot
      have hnorm : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hxnot
      let ray := (fun t : ℝ => t • x) '' Set.Ici (1 : ℝ)
      have hray : IsPreconnected ray := isPreconnected_Ici.image _
        (continuous_id.smul continuous_const).continuousOn
      have hxray : x ∈ ray := ⟨1,by simp,one_smul ℝ x⟩
      have hRayOff : ray ⊆ Cᶜ := by
        rintro y ⟨t,ht,rfl⟩ hy
        have hb : ‖t • x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hball hy
        change 1 ≤ t at ht
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by exact zero_le_one.trans ht : 0 ≤ t)] at hb
        nlinarith only [hb,ht,hnorm]
      have hRayCC := hray.subset_connectedComponentIn hxray hRayOff
      obtain ⟨R,hR⟩ := hx.2.exists_norm_le
      let t := max 1 ((R+1)/‖x‖)
      have ht : 1 ≤ t := le_max_left _ _
      have hbound := hR (t • x) (hRayCC ⟨t,ht,rfl⟩)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by exact zero_le_one.trans ht : 0 ≤ t)] at hbound
      have hdiv : (R+1)/‖x‖ ≤ t := le_max_right _ _
      have hmul := (div_le_iff₀ (by exact zero_lt_one.trans hnorm : 0 < ‖x‖)).mp hdiv
      linarith only [hmul,hbound]
    have hrange : Set.range d = Schoenflies.inside C ∪ C :=
      embedded_disc_range_eq_closed_inside d hd C hC hdB
    refine ⟨d,hd,hdB,?_⟩
    rw [hrange]
    exact Set.union_subset hinside hball
  have actual_embedded_plane_path_is_arc_between
      (f : C(Interval,Plane)) (hf : Topology.IsEmbedding f) :
      IsArcBetween (Set.range f) (f 0) (f 1) := by
    let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
    have hfc : Continuous fc := f.continuous.comp continuous_projIcc
    have he (t : Interval) : fc t=f t := by
      simp only [fc,Function.comp_apply,Set.projIcc_of_mem zero_le_one t.property]
    refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
    · intro t ht u hu h
      exact congrArg Subtype.val (hf.injective (by
        simpa only [← he] using h : f ⟨t,ht⟩=f ⟨u,hu⟩))
    · ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩
        exact ⟨t,t.property,he t⟩
  have actual_unit_sphere_puncture_preconnected
      (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
      IsPreconnected ({p}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
    have hn : ‖p.val‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
    let e := stereographic hn
    have htarget : IsPreconnected e.target := by
      change IsPreconnected (Set.univ : Set ((ℝ ∙ p.val)ᗮ))
      exact isPreconnected_univ
    have hsrc := htarget.image e.symm e.continuousOn_symm
    rw [e.symm_image_target_eq_source] at hsrc
    simpa only [e,stereographic_source] using hsrc
  have actual_originalQ_disk_boundary_puncture_preconnected
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (y : Q S x R)
      (hy : y∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
      IsPreconnected ((D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) \ {y}) := by
    obtain ⟨z,hz,hzy⟩ := hy
    let q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨z.val,hz⟩
    let inc : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
      fun p => ⟨p.val,Metric.sphere_subset_closedBall p.property⟩
    have hinc : Continuous inc := by dsimp [inc]; fun_prop
    let f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R) :=
      ⟨D ∘ inc,D.continuous.comp hinc⟩
    have hfi : Function.Injective f := by
      intro p q he
      exact Subtype.ext (congrArg (fun z : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 => z.val) (hD.injective he))
    have hfq : f q=y := hzy
    have heq : f '' ({q}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))=
        (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) \ {y} := by
      apply Set.Subset.antisymm
      · rintro v ⟨p,hp,rfl⟩
        refine ⟨⟨inc p,p.property,rfl⟩,?_⟩
        intro he
        have hpeq : p=q := hfi (he.trans hfq.symm)
        exact hp hpeq
      · rintro v ⟨⟨w,hw,hwv⟩,hne⟩
        let p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨w.val,hw⟩
        have hfp : f p=v := hwv
        refine ⟨p,?_,hfp⟩
        intro he
        exact hne (hfp.symm.trans ((congrArg f he).trans hfq))
    rw [← heq]
    exact (actual_unit_sphere_puncture_preconnected q).image f f.continuous.continuousOn
  have actual_original_proper_arc_boundary_contact_parameters
      (b : ProperArc S x R) (t : Interval) (hboundary : b.val t∈boundaryQ S x R) :
      t=0 ∨ t=1 := by
    by_cases ht0 : t=0
    · exact Or.inl ht0
    by_cases ht1 : t=1
    · exact Or.inr ht1
    have hti : t∈Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne (show (0 : Interval)≤t from t.property.1) (Ne.symm ht0),
       lt_of_le_of_ne (show t≤(1 : Interval) from t.property.2) ht1⟩
    exact False.elim (b.property.2.2.2 t hti hboundary)
  have actual_boundary_parallel_disk_initial_endpoint_attached
      (b : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range b.val ∪ Set.range bd) : b.val 0∈Set.range bd := by
    by_contra hn
    let K := (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) \ {b.val 1}
    have hb1 : b.val 1∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [hDb]; exact Or.inl (Set.mem_range_self _)
    have hK := actual_originalQ_disk_boundary_puncture_preconnected D hD (b.val 1) hb1
    have hcover : K ⊆ Set.range b.val ∪ Set.range bd := by
      intro y hy
      exact hDb ▸ hy.1
    have hA : (K ∩ Set.range b.val).Nonempty := by
      refine ⟨b.val 0,⟨?_,?_⟩,Set.mem_range_self _⟩
      · rw [hDb]; exact Or.inl (Set.mem_range_self _)
      · intro he
        exact (show (0 : Interval)≠1 by norm_num) (b.property.1.injective he)
    have hB : (K ∩ Set.range bd).Nonempty := by
      have mk (t : Interval) (ht : bd t≠b.val 1) : (K ∩ Set.range bd).Nonempty := by
        refine ⟨bd t,⟨?_,ht⟩,Set.mem_range_self _⟩
        rw [hDb]; exact Or.inr (Set.mem_range_self _)
      by_cases h0 : bd 0=b.val 1
      · apply mk 1
        intro h1
        exact (show (1 : Interval)≠0 by norm_num) (hbd.injective (h1.trans h0.symm))
      · exact mk 0 h0
    obtain ⟨y,hyK,hyA,hyB⟩ := (isPreconnected_closed_iff.mp hK)
      (Set.range b.val) (Set.range bd) (isCompact_range b.val.continuous).isClosed
      (isCompact_range bd.continuous).isClosed hcover hA hB
    obtain ⟨t,ht⟩ := hyA
    obtain ⟨j,hj⟩ := hyB
    have hby : b.val t∈boundaryQ S x R := ht.symm ▸ (hj ▸ hbdB j)
    rcases actual_original_proper_arc_boundary_contact_parameters b t hby with ht0 | ht1
    · apply hn
      rw [ht0] at ht
      exact ht.symm ▸ ⟨j,hj⟩
    · apply hyK.2
      exact ht.symm.trans (congrArg b.val ht1)
  have actual_boundary_parallel_disk_terminal_endpoint_attached
      (b : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range b.val ∪ Set.range bd) : b.val 1∈Set.range bd := by
    by_contra hn
    let K := (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) \ {b.val 0}
    have hb1 : b.val 0∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [hDb]; exact Or.inl (Set.mem_range_self _)
    have hK := actual_originalQ_disk_boundary_puncture_preconnected D hD (b.val 0) hb1
    have hcover : K ⊆ Set.range b.val ∪ Set.range bd := by
      intro y hy
      exact hDb ▸ hy.1
    have hA : (K ∩ Set.range b.val).Nonempty := by
      refine ⟨b.val 1,⟨?_,?_⟩,Set.mem_range_self _⟩
      · rw [hDb]; exact Or.inl (Set.mem_range_self _)
      · intro he
        exact (show (1 : Interval)≠0 by norm_num) (b.property.1.injective he)
    have hB : (K ∩ Set.range bd).Nonempty := by
      have mk (t : Interval) (ht : bd t≠b.val 0) : (K ∩ Set.range bd).Nonempty := by
        refine ⟨bd t,⟨?_,ht⟩,Set.mem_range_self _⟩
        rw [hDb]; exact Or.inr (Set.mem_range_self _)
      by_cases h0 : bd 0=b.val 0
      · apply mk 1
        intro h1
        exact (show (1 : Interval)≠0 by norm_num) (hbd.injective (h1.trans h0.symm))
      · exact mk 0 h0
    obtain ⟨y,hyK,hyA,hyB⟩ := (isPreconnected_closed_iff.mp hK)
      (Set.range b.val) (Set.range bd) (isCompact_range b.val.continuous).isClosed
      (isCompact_range bd.continuous).isClosed hcover hA hB
    obtain ⟨t,ht⟩ := hyA
    obtain ⟨j,hj⟩ := hyB
    have hby : b.val t∈boundaryQ S x R := ht.symm ▸ (hj ▸ hbdB j)
    rcases actual_original_proper_arc_boundary_contact_parameters b t hby with ht0 | ht1
    · apply hyK.2
      exact ht.symm.trans (congrArg b.val ht0)
    · apply hn
      rw [ht1] at ht
      exact ht.symm ▸ ⟨j,hj⟩
  have actual_original_boundary_subarc_between_old_endpoints
      (b : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (hb0 : b.val 0∈Set.range bd) (hb1 : b.val 1∈Set.range bd) :
      ∃ q : C(Interval,Q S x R), Topology.IsEmbedding q ∧ q 0=b.val 0 ∧ q 1=b.val 1 ∧
        (∀ t,q t∈boundaryQ S x R) ∧ Set.range q ⊆ Set.range bd ∧
        Set.range b.val ∩ Set.range q={b.val 0,b.val 1} := by
    obtain ⟨p0,hp0⟩ := hb0
    obtain ⟨p1,hp1⟩ := hb1
    have hpn : p0≠p1 := by
      intro he
      have hb01 := b.property.1.injective (hp0.symm.trans ((congrArg bd he).trans hp1))
      exact (show (0 : Interval)≠1 by norm_num) hb01
    let pbd : Path (bd 0) (bd 1) := { toContinuousMap := bd, source' := rfl, target' := rfl }
    let pathq := CurveComplex.BranchedDoubleCover.actualSubpath pbd p0 p1
    let q : C(Interval,Q S x R) := pathq.toContinuousMap
    have hqi : Function.Injective q := by
      intro v w he
      have hclock := congrArg Subtype.val (hbd.injective he)
      change (1-(v:ℝ))*(p0:ℝ)+(v:ℝ)*(p1:ℝ)=
        (1-(w:ℝ))*(p0:ℝ)+(w:ℝ)*(p1:ℝ) at hclock
      have hdiff : (p1:ℝ)-(p0:ℝ)≠0 := by
        intro heq
        exact hpn (Subtype.ext (sub_eq_zero.mp heq).symm)
      have hmul : ((p1:ℝ)-(p0:ℝ))*((v:ℝ)-(w:ℝ))=0 := by
        nlinarith only [hclock]
      exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hdiff))
    have hq : Topology.IsEmbedding q := (q.continuous.isClosedEmbedding hqi).isEmbedding
    have hq0 : q 0=b.val 0 := pathq.source'.trans hp0
    have hq1 : q 1=b.val 1 := pathq.target'.trans hp1
    have hqB : ∀ t,q t∈boundaryQ S x R :=
      fun t => hbdB (CurveComplex.BranchedDoubleCover.intervalAffine p0 p1 t)
    have hqsub : Set.range q ⊆ Set.range bd := by
      rintro y ⟨t,rfl⟩
      exact ⟨CurveComplex.BranchedDoubleCover.intervalAffine p0 p1 t,rfl⟩
    refine ⟨q,hq,hq0,hq1,hqB,hqsub,?_⟩
    apply Set.Subset.antisymm
    · rintro y ⟨⟨t,ht⟩,⟨v,hv⟩⟩
      have hby : b.val t∈boundaryQ S x R := ht.symm ▸ (hv ▸ hqB v)
      rcases actual_original_proper_arc_boundary_contact_parameters b t hby with ht0 | ht1
      · exact Or.inl (ht.symm.trans (congrArg b.val ht0))
      · exact Or.inr (ht.symm.trans (congrArg b.val ht1))
    · intro y hy
      rcases hy with hy | hy
      · subst y
        exact ⟨Set.mem_range_self _,⟨0,hq0⟩⟩
      · subst y
        exact ⟨Set.mem_range_self _,⟨1,hq1⟩⟩
  have actual_two_piece_boundary_parallel_arc_has_rectangle_inside_actual_disk
      (d : ProperArc S x R) (P T bd : C(Interval,Q S x R))
      (hP : Topology.IsEmbedding P) (hT : Topology.IsEmbedding T)
      (hd0 : d.val 0=P 0) (hd1 : d.val 1=T 1)
      (hPT : P 1=T 0) (hPTm : ∀ s t,P s=T t → s=1 ∧ t=0)
      (hPbd : ∀ s,P s∈boundaryQ S x R → s=0)
      (hTbd : ∀ s,T s∈boundaryQ S x R → s=1)
      (hdimage : Set.range d.val=Set.range P ∪ Set.range T)
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd) :
      ∃ B : C(Interval × Interval,Q S x R),Topology.IsEmbedding B ∧
        (∀ u,B (u,0)=P u) ∧ (∀ v,B (1,v)=T v) ∧
        Set.range B ⊆ Set.range D ∧
        (∀ v,B (0,v)∈boundaryQ S x R) ∧ (∀ u,B (u,1)∈boundaryQ S x R) := by
    have hdD : Set.range d.val ⊆ Set.range D := by
      intro y hy
      exact Set.image_subset_range _ _
        (hDb.symm ▸ (show y∈Set.range d.val ∪ Set.range bd from Or.inl hy))
    have hbdD : Set.range bd ⊆ Set.range D := by
      intro y hy
      exact Set.image_subset_range _ _
        (hDb.symm ▸ (show y∈Set.range d.val ∪ Set.range bd from Or.inr hy))
    obtain ⟨q,hq,hq0,hq1,hqB,hqbd,hqdmeet⟩ := actual_original_boundary_subarc_between_old_endpoints
      d bd hbd hbdB
      (actual_boundary_parallel_disk_initial_endpoint_attached d bd hbd hbdB D hD hDb)
      (actual_boundary_parallel_disk_terminal_endpoint_attached d bd hbd hbdB D hD hDb)
    have hqP : q 0=P 0 := hq0.trans hd0
    have hqT : q 1=T 1 := hq1.trans hd1
    have hPqm (s t : Interval) (he : P s=q t) : s=0 ∧ t=0 := by
      have hs : s=0 := hPbd s (he.symm ▸ hqB t)
      exact ⟨hs,hq.injective (he.symm.trans ((congrArg P hs).trans hqP.symm))⟩
    have hTqm (s t : Interval) (he : T s=q t) : s=1 ∧ t=1 := by
      have hs : s=1 := hTbd s (he.symm ▸ hqB t)
      exact ⟨hs,hq.injective (he.symm.trans ((congrArg T hs).trans hqT.symm))⟩
    have hPD : Set.range P ⊆ Set.range D := by
      intro y hy
      exact hdD (hdimage.symm ▸ (show y∈Set.range P ∪ Set.range T from Or.inl hy))
    have hTD : Set.range T ⊆ Set.range D := by
      intro y hy
      exact hdD (hdimage.symm ▸ (show y∈Set.range P ∪ Set.range T from Or.inr hy))
    obtain ⟨B,hB,hBP,hBT,hBD,hBleft,hBtop⟩ :=
      actual_three_arc_boundary_cycle_has_prescribed_rectangle_in_actual_disk
        P T q hP hT hq hPT hqP hqT hPTm hPqm hTqm D hD hPD hTD (hqbd.trans hbdD)
    refine ⟨B,hB,hBP,hBT,hBD,?_,?_⟩
    · intro v; obtain ⟨t,ht⟩ := hBleft v; exact ht ▸ hqB t
    · intro u; obtain ⟨t,ht⟩ := hBtop u; exact ht ▸ hqB t
  have actual_two_parallel_surgery_disks_with_actual_common_tail_cancel_old_arc
      (b d e : ProperArc S x R) (P Qe T bd be : C(Interval,Q S x R))
      (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Qe) (hT : Topology.IsEmbedding T)
      (hd0 : d.val 0=P 0) (he0 : e.val 0=Qe 0)
      (hd1 : d.val 1=T 1) (he1 : e.val 1=T 1)
      (hPT : P 1=T 0) (hQT : Qe 1=T 0)
      (hPTm : ∀ s t,P s=T t → s=1 ∧ t=0)
      (hQTm : ∀ s t,Qe s=T t → s=1 ∧ t=0)
      (hPbd : ∀ s,P s∈boundaryQ S x R → s=0)
      (hQbd : ∀ s,Qe s∈boundaryQ S x R → s=0)
      (hTbd : ∀ s,T s∈boundaryQ S x R → s=1)
      (hdimage : Set.range d.val=Set.range P ∪ Set.range T)
      (heimage : Set.range e.val=Set.range Qe ∪ Set.range T)
      (hbimage : Set.range b.val=Set.range P ∪ Set.range Qe)
      (hbd : Topology.IsEmbedding bd) (hbe : Topology.IsEmbedding be)
      (hbdB : ∀ t,bd t∈boundaryQ S x R) (hbeB : ∀ t,be t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : Plane) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (hE : Topology.IsEmbedding E)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range e.val ∪ Set.range be)
      (hDE : Set.range D ∩ Set.range E=Set.range T) : boundaryParallel S x R b := by
    obtain ⟨BL,hBL,hBLP,hBLT,hBLD,hBLL,hBLU⟩ :=
      actual_two_piece_boundary_parallel_arc_has_rectangle_inside_actual_disk
        d P T bd hP hT hd0 hd1 hPT hPTm hPbd hTbd hdimage hbd hbdB D hD hDb
    obtain ⟨BR,hBR,hBRQ,hBRT,hBRE,hBRL,hBRU⟩ :=
      actual_two_piece_boundary_parallel_arc_has_rectangle_inside_actual_disk
        e Qe T be hQ hT he0 he1 hQT hQTm hQbd hTbd heimage hbe hbeB E hE hEb
    let flip : Interval × Interval → Interval × Interval := fun z => (unitInterval.symm z.1,z.2)
    have hflipc : Continuous flip := by dsimp [flip]; fun_prop
    have hflipi : Function.Injective flip := by
      intro z v he
      have h1 := congrArg (fun w : Interval × Interval => w.1) he
      have h2 := congrArg (fun w : Interval × Interval => w.2) he
      change unitInterval.symm z.1=unitInterval.symm v.1 at h1
      change z.2=v.2 at h2
      exact Prod.ext (unitInterval.symm_involutive.injective h1) h2
    have hflip : Topology.IsEmbedding flip := (hflipc.isClosedEmbedding hflipi).isEmbedding
    let L : C(Interval × Interval,Q S x R) := BL.comp ⟨flip,hflipc⟩
    let Rr : C(Interval × Interval,Q S x R) := BR.comp ⟨flip,hflipc⟩
    have hL : Topology.IsEmbedding L := hBL.comp hflip
    have hR : Topology.IsEmbedding Rr := hBR.comp hflip
    have hLT (w : Interval) : L (0,w)=T w := by
      change BL (unitInterval.symm 0,w)=T w
      rw [unitInterval.symm_zero]; exact hBLT w
    have hRT (w : Interval) : Rr (0,w)=T w := by
      change BR (unitInterval.symm 0,w)=T w
      rw [unitInterval.symm_zero]; exact hBRT w
    have hseam (w : Interval) : L (0,w)=Rr (0,w) := (hLT w).trans (hRT w).symm
    have hmeet : Set.range L ∩ Set.range Rr=Set.range (fun w => L (0,w)) := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨z,hz⟩,⟨v,hv⟩⟩
        have hyD : y∈Set.range D := hBLD ⟨flip z,hz⟩
        have hyE : y∈Set.range E := hBRE ⟨flip v,hv⟩
        have hyT : y∈Set.range T := hDE ▸ (show y∈Set.range D ∩ Set.range E from ⟨hyD,hyE⟩)
        obtain ⟨w,hw⟩ := hyT
        exact ⟨w,(hLT w).trans hw⟩
      · rintro y ⟨w,rfl⟩
        exact ⟨Set.mem_range_self (0,w),⟨(0,w),(hseam w).symm⟩⟩
    obtain ⟨F,hF,hF0,hF1,hfiber,hFlow⟩ :=
      actual_two_square_gluing_preserves_lower_edge_union L Rr hL hR hseam hmeet
    have hLlow : Set.range (fun t : Interval => L (t,0))=Set.range P := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,(hBLP _).symm⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symm t,?_⟩
        change BL (unitInterval.symm (unitInterval.symm t),0)=P t
        rw [unitInterval.symm_involutive]; exact hBLP t
    have hRlow : Set.range (fun t : Interval => Rr (t,0))=Set.range Qe := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨unitInterval.symm t,(hBRQ _).symm⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symm t,?_⟩
        change BR (unitInterval.symm (unitInterval.symm t),0)=Qe t
        rw [unitInterval.symm_involutive]; exact hBRQ t
    have hbottom : Set.range (fun t : Interval => F (t,0))=Set.range b.val := by
      rw [hFlow,hLlow,hRlow,←hbimage]
    apply actual_original_proper_arc_square_with_three_boundary_edges_is_parallel b F hF hbottom
    · intro w
      rw [hF0]
      change BL (unitInterval.symm 1,w)∈boundaryQ S x R
      rw [unitInterval.symm_one]; exact hBLL w
    · intro w
      rw [hF1]
      change BR (unitInterval.symm 1,w)∈boundaryQ S x R
      rw [unitInterval.symm_one]; exact hBRL w
    · intro u
      obtain ⟨t,ht | ht⟩ := hfiber (u,1)
      · rw [ht]; exact hBLU (unitInterval.symm t)
      · rw [ht]; exact hBRU (unitInterval.symm t)
  have actual_originalQ_arc_and_boundary_subarc_in_actual_disk_parallel
      (b : ProperArc S x R) (q : C(Interval,Q S x R))
      (hq : Topology.IsEmbedding q) (hq0 : q 0=b.val 0) (hq1 : q 1=b.val 1)
      (hqB : ∀ t,q t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hbD : Set.range b.val ⊆ Set.range D) (hqD : Set.range q ⊆ Set.range D)
      (hmeet : Set.range b.val ∩ Set.range q={b.val 0,b.val 1}) :
      boundaryParallel S x R b := by
    let e := hD.toHomeomorph
    let fa : C(Interval,Set.range D) :=
      ⟨fun t => ⟨b.val t,hbD (Set.mem_range_self t)⟩,b.val.continuous.subtype_mk _⟩
    let fb : C(Interval,Set.range D) :=
      ⟨fun t => ⟨q t,hqD (Set.mem_range_self t)⟩,q.continuous.subtype_mk _⟩
    have hfa : Topology.IsEmbedding fa := (fa.continuous.isClosedEmbedding (by
      intro s t he
      exact b.property.1.injective (congrArg (fun y : Set.range D => y.val) he))).isEmbedding
    have hfb : Topology.IsEmbedding fb := (fb.continuous.isClosedEmbedding (by
      intro s t he
      exact hq.injective (congrArg (fun y : Set.range D => y.val) he))).isEmbedding
    let PA : C(Interval,Plane) := ⟨fun t => (e.symm (fa t)).val,
      continuous_subtype_val.comp (e.symm.continuous.comp fa.continuous)⟩
    let PB : C(Interval,Plane) := ⟨fun t => (e.symm (fb t)).val,
      continuous_subtype_val.comp (e.symm.continuous.comp fb.continuous)⟩
    have hPA : Topology.IsEmbedding PA :=
      Topology.IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hfa)
    have hPB : Topology.IsEmbedding PB :=
      Topology.IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hfb)
    have hDPA (t : Interval) : D (e.symm (fa t))=b.val t :=
      congrArg (fun y : Set.range D => y.val) (e.apply_symm_apply (fa t))
    have hDPB (t : Interval) : D (e.symm (fb t))=q t :=
      congrArg (fun y : Set.range D => y.val) (e.apply_symm_apply (fb t))
    have hPB0 : PB 0=PA 0 := congrArg (fun y : Set.range D => (e.symm y).val)
      (show fb 0=fa 0 from Subtype.ext hq0)
    have hPB1 : PB 1=PA 1 := congrArg (fun y : Set.range D => (e.symm y).val)
      (show fb 1=fa 1 from Subtype.ext hq1)
    have hAarc := actual_embedded_plane_path_is_arc_between PA hPA
    have hBarc := actual_embedded_plane_path_is_arc_between PB hPB
    rw [hPB0,hPB1] at hBarc
    have hJ : IsJordanCurve (Set.range PA ∪ Set.range PB) := by
      apply IsJordanCurve.of_two_arcs hAarc hBarc.reverse
      intro y hyA hyB
      obtain ⟨s,hs⟩ := hyA
      obtain ⟨t,ht⟩ := hyB
      have heBall : e.symm (fa s)=e.symm (fb t) := Subtype.ext (hs.trans ht.symm)
      have heOld : b.val s=q t :=
        congrArg (fun y : Set.range D => y.val) (e.symm.injective heBall)
      have hOrig : b.val s∈Set.range b.val ∩ Set.range q :=
        ⟨Set.mem_range_self s,⟨t,heOld.symm⟩⟩
      rw [hmeet] at hOrig
      rcases hOrig with h0 | h1
      · left
        exact hs.symm.trans (congrArg (fun y : Set.range D => (e.symm y).val)
          (show fa s=fa 0 from Subtype.ext h0))
      · right
        exact hs.symm.trans (congrArg (fun y : Set.range D => (e.symm y).val)
          (show fa s=fa 1 from Subtype.ext h1))
    have hball : Set.range PA ∪ Set.range PB ⊆ Metric.closedBall (0 : Plane) 1 := by
      rintro y (hy | hy)
      · obtain ⟨t,rfl⟩ := hy
        exact (e.symm (fa t)).property
      · obtain ⟨t,rfl⟩ := hy
        exact (e.symm (fb t)).property
    obtain ⟨d,hd,hdB,hdsub⟩ := actual_jordan_disk_in_closed_unit_ball _ hJ hball
    let lifted : C(Metric.closedBall (0 : Plane) 1,Metric.closedBall (0 : Plane) 1) :=
      ⟨fun z => ⟨d z,hdsub (Set.mem_range_self z)⟩,d.continuous.subtype_mk _⟩
    have hlifted : Topology.IsEmbedding lifted := (lifted.continuous.isClosedEmbedding (by
      intro z w he
      exact hd.injective (congrArg (fun p : Metric.closedBall (0 : Plane) 1 => p.val) he))).isEmbedding
    let newD : C(Metric.closedBall (0 : Plane) 1,Q S x R) :=
      ⟨D ∘ lifted,D.continuous.comp lifted.continuous⟩
    have hnewD : Topology.IsEmbedding newD := hD.comp hlifted
    refine ⟨q,hq,hqB,newD,hnewD,?_⟩
    apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      have hdC : d z∈Set.range PA ∪ Set.range PB := hdB ▸ ⟨z,hz,rfl⟩
      rcases hdC with hA | hB
      · obtain ⟨t,ht⟩ := hA
        left
        refine ⟨t,?_⟩
        have hLiftz : lifted z=e.symm (fa t) := Subtype.ext ht.symm
        change b.val t=D (lifted z)
        rw [hLiftz]
        exact (hDPA t).symm
      · obtain ⟨t,ht⟩ := hB
        right
        refine ⟨t,?_⟩
        have hLiftz : lifted z=e.symm (fb t) := Subtype.ext ht.symm
        change q t=D (lifted z)
        rw [hLiftz]
        exact (hDPB t).symm
    · rintro y (hy | hy)
      · obtain ⟨t,rfl⟩ := hy
        have hPa : PA t∈d '' {z | z.val∈Metric.sphere (0 : Plane) 1} :=
          hdB.symm ▸ Or.inl (Set.mem_range_self t)
        obtain ⟨z,hz,hzt⟩ := hPa
        refine ⟨z,hz,?_⟩
        have hLiftz : lifted z=e.symm (fa t) := Subtype.ext hzt
        change D (lifted z)=b.val t
        rw [hLiftz]
        exact hDPA t
      · obtain ⟨t,rfl⟩ := hy
        have hPb : PB t∈d '' {z | z.val∈Metric.sphere (0 : Plane) 1} :=
          hdB.symm ▸ Or.inr (Set.mem_range_self t)
        obtain ⟨z,hz,hzt⟩ := hPb
        refine ⟨z,hz,?_⟩
        have hLiftz : lifted z=e.symm (fb t) := Subtype.ext hzt
        change D (lifted z)=q t
        rw [hLiftz]
        exact hDPB t
  have actual_original_boundary_circle_in_closed_open_disk :
      boundaryCircle S x R ⊆ closure (openDisk S x R) := by
    let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
    have hcont : ContinuousOn E.symm
        (closure (Metric.ball (E x) R)) := by
      rw [closure_ball _ (ne_of_gt hR)]
      exact E.continuousOn_symm.mono htarget
    have hsub := hcont.image_closure
    rintro y ⟨z,hz,rfl⟩
    apply hsub
    refine ⟨z,?_,rfl⟩
    rw [closure_ball _ (ne_of_gt hR)]
    exact Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le
  have actual_original_embedded_disk_interior_boundary_clearance
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hd : Topology.IsEmbedding d) :
      Disjoint (d '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (boundaryQ S x R) := by
    let dS : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
      ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
    have hdS : Topology.IsEmbedding dS := Topology.IsEmbedding.subtypeVal.comp hd
    let O := dS '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    have hO : IsOpen O := CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen dS hdS
    have hOdis : Disjoint O (openDisk S x R) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨z,hz,rfl⟩ hy
      exact (d z).property hy
    have hOc : Disjoint O (closure (openDisk S x R)) := hOdis.closure_right hO
    apply Set.disjoint_left.mpr
    rintro y ⟨z,hz,rfl⟩ hy
    exact Set.disjoint_left.mp hOc ⟨z,hz,rfl⟩
      (actual_original_boundary_circle_in_closed_open_disk hy)
  have actual_boundary_parallel_disk_with_original_boundary_clearance
      (a : ProperArc S x R) (ha : boundaryParallel S x R a) :
      ∃ b : C(Interval,Q S x R), Topology.IsEmbedding b ∧
        (∀ t,b t∈boundaryQ S x R) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R),
        Topology.IsEmbedding d ∧
        d '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
          Set.range a.val ∪ Set.range b ∧
        Disjoint (d '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
          (boundaryQ S x R) := by
    obtain ⟨b,hb,hbb,d,hd,hbd⟩ := ha
    exact ⟨b,hb,hbb,d,hd,hbd,
      actual_original_embedded_disk_interior_boundary_clearance d hd⟩
  have actual_connected_originalQ_set_disk_side_dichotomy
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hd : Topology.IsEmbedding d) (K : Set (Q S x R)) (hK : IsPreconnected K)
      (hboundary : Disjoint K
        (d '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1})) :
      K ⊆ d '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ∨
        Disjoint K (Set.range d) := by
    let O := d '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    let dS : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
      ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
    have hdS : Topology.IsEmbedding dS := Topology.IsEmbedding.subtypeVal.comp hd
    have hOS : IsOpen (dS '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :=
      CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen dS hdS
    have hOeq : O=Subtype.val ⁻¹'
        (dS '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩; exact ⟨z,hz,rfl⟩
      · rintro ⟨z,hz,he⟩; exact ⟨z,hz,Subtype.ext he⟩
    have hO : IsOpen O := hOeq ▸ hOS.preimage continuous_subtype_val
    have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
    have hcover : K ⊆ O ∪ (Set.range d)ᶜ := by
      intro y hy
      by_cases hr : y∈Set.range d
      · obtain ⟨z,rfl⟩ := hr
        have hballs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∪ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
          rw [Metric.ball_union_sphere]
        have hz := hballs z.property
        rcases hz with hlt | heq
        · exact Or.inl ⟨z,hlt,rfl⟩
        · exact False.elim (Set.disjoint_left.mp hboundary hy ⟨z,heq,rfl⟩)
      · exact Or.inr hr
    have hdis : Disjoint O (Set.range d)ᶜ := Set.disjoint_left.mpr (by
      rintro y ⟨z,hz,rfl⟩ hy
      exact hy (Set.mem_range_self z))
    by_cases hin : (K ∩ O).Nonempty
    · exact Or.inl (hK.subset_left_of_subset_union hO hclosed.isOpen_compl hdis hcover hin)
    · right
      apply Set.disjoint_left.mpr
      intro y hy hr
      rcases hcover hy with ho | hn
      · exact hin ⟨y,hy,ho⟩
      · exact hn hr
  have actual_terminal_left_disk_right_branch_side_dichotomy
      (b d : ProperArc S x R) (u v : Interval) (hu1 : u<1) (hv1 : v<1)
      (htail : ∀ s t : Interval,v≤t → b.val s=a0.val.val t → s=u ∧ t=v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (hdparallel : boundaryParallel S x R d) :
      ∃ bd : C(Interval,Q S x R), Topology.IsEmbedding bd ∧ (∀ t,bd t∈boundaryQ S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R),
        Topology.IsEmbedding D ∧
        D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
          Set.range d.val ∪ Set.range bd ∧
        ((b.val '' Ioo u 1) ⊆ D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ∨
          Disjoint (b.val '' Ioo u 1) (Set.range D)) := by
    obtain ⟨bd,hbd,hbdB,D,hD,hDb,hDi⟩ :=
      actual_boundary_parallel_disk_with_original_boundary_clearance d hdparallel
    let K := b.val '' Ioo u 1
    have hK : IsPreconnected K := isPreconnected_Ioo.image b.val b.val.continuous.continuousOn
    have hKbd : Disjoint K (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      rw [hDb]
      apply Set.disjoint_left.mpr
      rintro y ⟨t,ht,rfl⟩ hy
      rcases hy with hy | ⟨s,hs⟩
      · rw [hdimage] at hy
        rcases hy with ⟨s,hs⟩ | ⟨s,hs⟩
        · change b.val (CurveComplex.BranchedDoubleCover.intervalAffine 0 u s)=b.val t at hs
          have he := b.property.1.injective hs
          have hup := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc
            (show (0:Interval)≤u from u.property.1) s).2
          exact (not_lt_of_ge (he ▸ hup)) ht.1
        · change a0.val.val (CurveComplex.BranchedDoubleCover.intervalAffine v 1 s)=b.val t at hs
          have hv := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hv1.le s).1
          have he := (htail t _ hv hs.symm).1
          exact ht.1.ne' he
      · exact b.property.2.2.2 t ⟨lt_of_le_of_lt u.property.1 ht.1,ht.2⟩
          (hs ▸ hbdB s)
    exact ⟨bd,hbd,hbdB,D,hD,hDb,
      actual_connected_originalQ_set_disk_side_dichotomy D hD K hK hKbd⟩
  have actual_terminal_right_disk_left_branch_side_dichotomy
      (b e : ProperArc S x R) (u v : Interval) (hu0 : 0<u) (hv1 : v<1)
      (htail : ∀ s t : Interval,v≤t → b.val s=a0.val.val t → s=u ∧ t=v)
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heparallel : boundaryParallel S x R e) :
      ∃ be : C(Interval,Q S x R), Topology.IsEmbedding be ∧ (∀ t,be t∈boundaryQ S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R),
        Topology.IsEmbedding D ∧
        D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
          Set.range e.val ∪ Set.range be ∧
        ((b.val '' Ioo 0 u) ⊆ D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ∨
          Disjoint (b.val '' Ioo 0 u) (Set.range D)) := by
    obtain ⟨be,hbe,hbeB,D,hD,hDb,hDi⟩ :=
      actual_boundary_parallel_disk_with_original_boundary_clearance e heparallel
    let K := b.val '' Ioo 0 u
    have hK : IsPreconnected K := isPreconnected_Ioo.image b.val b.val.continuous.continuousOn
    have hKbe : Disjoint K (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      rw [hDb]
      apply Set.disjoint_left.mpr
      rintro y ⟨t,ht,rfl⟩ hy
      rcases hy with hy | ⟨s,hs⟩
      · rw [heimage] at hy
        rcases hy with ⟨s,hs⟩ | ⟨s,hs⟩
        · change b.val (CurveComplex.BranchedDoubleCover.intervalAffine u 1 s)=b.val t at hs
          have he := b.property.1.injective hs
          have hup := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc
            (show u≤(1:Interval) from u.property.2) s).1
          exact (not_lt_of_ge (he ▸ hup)) ht.2
        · change a0.val.val (CurveComplex.BranchedDoubleCover.intervalAffine v 1 s)=b.val t at hs
          have hv := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hv1.le s).1
          have he := (htail t _ hv hs.symm).1
          exact ht.2.ne he
      · exact b.property.2.2.2 t ⟨ht.1,lt_of_lt_of_le ht.2 u.property.2⟩
          (hs ▸ hbeB s)
    exact ⟨be,hbe,hbeB,D,hD,hDb,
      actual_connected_originalQ_set_disk_side_dichotomy D hD K hK hKbe⟩
  have actual_original_open_branch_disk_containment_closes
      (b : ProperArc S x R) (l r : Interval) (hlr : l<r)
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hinside : b.val '' Ioo l r ⊆
        D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
      b.val '' Icc l r ⊆ Set.range D := by
    have hclosed : IsClosed (Set.range D) := (isCompact_range D.continuous).isClosed
    have hsub : b.val '' Ioo l r ⊆ Set.range D :=
      hinside.trans (Set.image_subset_range _ _)
    have hcl := b.val.continuous.continuousOn.image_closure (s := Ioo l r)
    rw [closure_Ioo hlr.ne] at hcl
    exact hcl.trans (closure_minimal hsub hclosed)
  have actual_original_disk_boundary_point_is_actual_disk_boundary
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (y : Q S x R)
      (hy : y∈boundaryQ S x R) (hyrange : y∈Set.range D) :
      y∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    obtain ⟨z,rfl⟩ := hyrange
    have hballs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∪ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.ball_union_sphere]
    rcases hballs z.property with hball | hsphere
    · exact False.elim (Set.disjoint_left.mp
        (actual_original_embedded_disk_interior_boundary_clearance D hD) ⟨z,hball,rfl⟩ hy)
    · exact ⟨z,hsphere,rfl⟩
  have actual_boundary_parallel_disk_original_boundary_contacts
      (d : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (y : Q S x R) (hyB : y∈boundaryQ S x R) (hyD : y∈Set.range D) :
      y∈Set.range bd := by
    have hycircle := actual_original_disk_boundary_point_is_actual_disk_boundary D hD y hyB hyD
    rw [hDb] at hycircle
    rcases hycircle with hd | hbdmem
    · obtain ⟨t,ht⟩ := hd
      have hdB : d.val t∈boundaryQ S x R := ht.symm ▸ hyB
      rcases actual_original_proper_arc_boundary_contact_parameters d t hdB with ht0 | ht1
      · have h0 := actual_boundary_parallel_disk_initial_endpoint_attached d bd hbd hbdB D hD hDb
        rw [ht0] at ht
        exact ht ▸ h0
      · have h1 := actual_boundary_parallel_disk_terminal_endpoint_attached d bd hbd hbdB D hD hDb
        rw [ht1] at ht
        exact ht ▸ h1
    · exact hbdmem
  have actual_old_proper_arc_contained_in_boundary_parallel_disk_is_parallel
      (b d : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (hbD : Set.range b.val ⊆ Set.range D) : boundaryParallel S x R b := by
    have hb0 := actual_boundary_parallel_disk_original_boundary_contacts d bd hbd hbdB D hD hDb
      (b.val 0) b.property.2.1 (hbD (Set.mem_range_self 0))
    have hb1 := actual_boundary_parallel_disk_original_boundary_contacts d bd hbd hbdB D hD hDb
      (b.val 1) b.property.2.2.1 (hbD (Set.mem_range_self 1))
    obtain ⟨q,hq,hq0,hq1,hqB,hqsub,hmeet⟩ :=
      actual_original_boundary_subarc_between_old_endpoints b bd hbd hbdB hb0 hb1
    have hbdD : Set.range bd ⊆ Set.range D := by
      intro y hy
      have hycircle : y∈D '' {z | z.val∈Metric.sphere (0 : Plane) 1} := hDb.symm ▸ Or.inr hy
      exact Set.image_subset_range _ _ hycircle
    exact actual_originalQ_arc_and_boundary_subarc_in_actual_disk_parallel
      b q hq hq0 hq1 hqB D hD hbD (hqsub.trans hbdD) hmeet
  have actual_boundary_parallel_disk_boundary_point_has_internal_chord
      (d : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (s : Interval) (hs : s≠0) :
      ∃ c : ProperArc S x R,c.val 0=bd s ∧ c.val 1=bd 0 ∧ Set.range c.val ⊆ Set.range D := by
    have hsphere (t : Interval) : bd t∈D '' {z | z.val∈Metric.sphere (0 : Plane) 1} := by
      rw [hDb]; exact Or.inr (Set.mem_range_self t)
    obtain ⟨p,hpSphere,hpD⟩ := hsphere s
    obtain ⟨q,hqSphere,hqD⟩ := hsphere 0
    have hpq : p.val≠q.val := by
      intro he
      have hpq' : p=q := Subtype.ext he
      exact hs (hbd.injective (hpD.symm.trans ((congrArg D hpq').trans hqD)))
    let line := Path.segment p.val q.val
    have hline (t : Interval) : line t∈Metric.closedBall (0 : Plane) 1 := by
      rw [Path.segment_apply,AffineMap.lineMap_apply_module]
      exact (convex_closedBall (0 : Plane) 1) p.property q.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have hlineInterior (t : Interval) (ht : t∈Ioo (0 : Interval) 1) :
        line t∈Metric.ball (0 : Plane) 1 := by
      rw [Path.segment_apply,AffineMap.lineMap_apply_module]
      exact combo_mem_ball_of_ne p.property q.property hpq
        (sub_pos.mpr ht.2) ht.1 (by ring)
    let c : C(Interval,Q S x R) :=
      ⟨fun t => D ⟨line t,hline t⟩,D.continuous.comp (line.continuous.subtype_mk _)⟩
    have hci : Function.Injective c := by
      intro v w he
      have hclock := congrArg (fun z : Metric.closedBall (0 : Plane) 1 => z.val) (hD.injective he)
      exact Path.segment_injective_of_ne hpq hclock
    have hc : Topology.IsEmbedding c := (c.continuous.isClosedEmbedding hci).isEmbedding
    have hc0 : c 0=bd s := by
      have he : (⟨line 0,hline 0⟩ : Metric.closedBall (0 : Plane) 1)=p := Subtype.ext line.source'
      change D ⟨line 0,hline 0⟩=bd s
      rw [he]; exact hpD
    have hc1 : c 1=bd 0 := by
      have he : (⟨line 1,hline 1⟩ : Metric.closedBall (0 : Plane) 1)=q := Subtype.ext line.target'
      change D ⟨line 1,hline 1⟩=bd 0
      rw [he]; exact hqD
    have hcB (t : Interval) (ht : t∈Ioo (0 : Interval) 1) : c t∉boundaryQ S x R := by
      intro hB
      exact Set.disjoint_left.mp (actual_original_embedded_disk_interior_boundary_clearance D hD)
        ⟨⟨line t,hline t⟩,hlineInterior t ht,rfl⟩ hB
    let cProper : ProperArc S x R := ⟨c,hc,hc0.symm ▸ hbdB s,hc1.symm ▸ hbdB 0,hcB⟩
    refine ⟨cProper,hc0,hc1,?_⟩
    rintro y ⟨t,rfl⟩
    exact ⟨⟨line t,hline t⟩,rfl⟩
  have actual_boundary_parallel_disk_two_boundary_points_have_internal_chord
      (d : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (s r : Interval) (hs : s≠r) :
      ∃ c : ProperArc S x R,c.val 0=bd s ∧ c.val 1=bd r ∧ Set.range c.val ⊆ Set.range D := by
    have hsphere (t : Interval) : bd t∈D '' {z | z.val∈Metric.sphere (0 : Plane) 1} := by
      rw [hDb]; exact Or.inr (Set.mem_range_self t)
    obtain ⟨p,hpSphere,hpD⟩ := hsphere s
    obtain ⟨q,hqSphere,hqD⟩ := hsphere r
    have hpq : p.val≠q.val := by
      intro he
      have hpq' : p=q := Subtype.ext he
      exact hs (hbd.injective (hpD.symm.trans ((congrArg D hpq').trans hqD)))
    let line := Path.segment p.val q.val
    have hline (t : Interval) : line t∈Metric.closedBall (0 : Plane) 1 := by
      rw [Path.segment_apply,AffineMap.lineMap_apply_module]
      exact (convex_closedBall (0 : Plane) 1) p.property q.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have hlineInterior (t : Interval) (ht : t∈Ioo (0 : Interval) 1) :
        line t∈Metric.ball (0 : Plane) 1 := by
      rw [Path.segment_apply,AffineMap.lineMap_apply_module]
      exact combo_mem_ball_of_ne p.property q.property hpq
        (sub_pos.mpr ht.2) ht.1 (by ring)
    let c : C(Interval,Q S x R) :=
      ⟨fun t => D ⟨line t,hline t⟩,D.continuous.comp (line.continuous.subtype_mk _)⟩
    have hci : Function.Injective c := by
      intro v w he
      have hclock := congrArg (fun z : Metric.closedBall (0 : Plane) 1 => z.val) (hD.injective he)
      exact Path.segment_injective_of_ne hpq hclock
    have hc : Topology.IsEmbedding c := (c.continuous.isClosedEmbedding hci).isEmbedding
    have hc0 : c 0=bd s := by
      have he : (⟨line 0,hline 0⟩ : Metric.closedBall (0 : Plane) 1)=p := Subtype.ext line.source'
      change D ⟨line 0,hline 0⟩=bd s
      rw [he]; exact hpD
    have hc1 : c 1=bd r := by
      have he : (⟨line 1,hline 1⟩ : Metric.closedBall (0 : Plane) 1)=q := Subtype.ext line.target'
      change D ⟨line 1,hline 1⟩=bd r
      rw [he]; exact hqD
    have hcB (t : Interval) (ht : t∈Ioo (0 : Interval) 1) : c t∉boundaryQ S x R := by
      intro hB
      exact Set.disjoint_left.mp (actual_original_embedded_disk_interior_boundary_clearance D hD)
        ⟨⟨line t,hline t⟩,hlineInterior t ht,rfl⟩ hB
    let cProper : ProperArc S x R := ⟨c,hc,hc0.symm ▸ hbdB s,hc1.symm ▸ hbdB r,hcB⟩
    refine ⟨cProper,hc0,hc1,?_⟩
    rintro y ⟨t,rfl⟩
    exact ⟨⟨line t,hline t⟩,rfl⟩
  have actual_original_boundary_endpoint_seed_for_disk_clearance
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
      (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (a : ProperArc S x R) :
        ∃ b : ℝ, ∃ hb : 0 < b ∧ b < 1,
        ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
          Topology.IsEmbedding E ∧
          (∀ t, E (t,⟨0,by norm_num⟩) =
            a.val ⟨b*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩) ∧
          (∀ w, E (0,w) ∈ boundaryQ S x R) ∧
          (∀ t : Interval, 0 < (t:ℝ) → ∀ w, E (t,w) ∉ boundaryQ S x R) ∧
          (∀ z, E z ∈ Set.range a.val ↔ (z.2 : ℝ) = 0) := by
      clear * - S x R g hg hS hR htarget a
      classical
      letI : ClosedSurface S := Classical.choice hS.2.1
      obtain ⟨U,V,hpU,h,hU,hV,hzero,hother,hdisk,hboundary,haxis⟩ :=
        CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.source_proper_arc_initial_endpoint_attached_axis_chart
          S g hg hS x R hR htarget a.val a.property.1 a.property.2.1
          a.property.2.2.1 (fun t ht => a.property.2.2.2 t ht)
      let f : C(Interval,S) := ⟨fun t => (a.val t).val,
        continuous_subtype_val.comp a.val.continuous⟩
      have hzeroF : ((h ⟨f 0,hpU⟩ : V) : ℝ × ℝ) = (0,0) := by
        simpa [f] using hzero
      have h0V : (0,0) ∈ V := hzeroF ▸ (h ⟨f 0,hpU⟩).property
      obtain ⟨ε,hε,hεV⟩ := Metric.isOpen_iff.mp hV (0,0) h0V
      let K : Set U := (fun y : U => (h y : ℝ × ℝ)) ⁻¹' Metric.ball (0,0) (ε/2)
      have hK : IsOpen K := Metric.isOpen_ball.preimage
        (continuous_subtype_val.comp h.continuous)
      let W : Set S := Subtype.val '' K
      have hW : IsOpen W := hU.isOpenMap_subtype_val K hK
      have hf0W : f 0 ∈ W := by
        refine ⟨⟨f 0,hpU⟩,?_,rfl⟩
        change dist ((h ⟨f 0,hpU⟩ : V) : ℝ × ℝ) (0,0) < ε/2
        rw [hzeroF,dist_self]
        positivity
      obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp
        ((hW.preimage f.continuous).mem_nhds hf0W)
      let b : ℝ := min (r/2) (1/2)
      have hb : 0 < b ∧ b < 1 := by
        constructor
        · exact lt_min (half_pos hr) (by norm_num)
        · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hbr : b < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      let τ : Interval → Interval := fun t => ⟨b*(t:ℝ),by
        constructor <;> nlinarith [t.property.1,t.property.2,hb.1,hb.2]⟩
      have hτc : Continuous τ := by dsimp [τ]; fun_prop
      have hτi : Function.Injective τ := by
        intro t u he
        apply Subtype.ext
        exact mul_left_cancel₀ hb.1.ne' (congrArg Subtype.val he)
      have hfW (t : Interval) : f (τ t) ∈ W := by
        apply hrW
        change dist (b*(t:ℝ)) (0:ℝ) < r
        rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hb.1.le t.property.1)]
        exact (mul_le_of_le_one_right hb.1.le t.property.2).trans_lt hbr
      have hfU (t : Interval) : f (τ t) ∈ U := by
        obtain ⟨y,hy,he⟩ := hfW t
        exact he ▸ y.property
      let c : Interval → ℝ × ℝ := fun t => (h ⟨f (τ t),hfU t⟩ : V)
      have hcc : Continuous c := continuous_subtype_val.comp
        (h.continuous.comp ((f.continuous.comp hτc).subtype_mk _))
      have hcsmall (t : Interval) : dist (c t) (0,0) < ε/2 := by
        obtain ⟨y,hy,he⟩ := hfW t
        have hey : y = ⟨f (τ t),hfU t⟩ := Subtype.ext he
        have hy' : dist ((h y : V) : ℝ × ℝ) (0,0) < ε/2 := hy
        change dist ((h ⟨f (τ t),hfU t⟩ : V) : ℝ × ℝ) (0,0) < ε/2
        simpa only [hey] using hy'
      have hcaxis (t : Interval) : 0 ≤ (c t).1 ∧ (c t).2 = 0 :=
        (haxis (f (τ t)) (hfU t)).mp ⟨a.val (τ t),Set.mem_range_self _,rfl⟩
      have hc0 : c 0 = (0,0) := by
        have hτ0 : τ 0 = 0 := Subtype.ext (by change b*0=0; ring)
        change ((h ⟨f (τ 0),hfU 0⟩ : V) : ℝ × ℝ) = _
        simpa only [hτ0] using hzeroF
      have hcpos (t : Interval) (ht : 0 < (t:ℝ)) : 0 < (c t).1 := by
        apply lt_of_le_of_ne (hcaxis t).1
        intro he
        have hcB := (hboundary (f (τ t)) (hfU t)).mpr he.symm
        have hτint : τ t ∈ Set.Ioo (0 : Interval) 1 := by
          constructor
          · change 0 < b*(t:ℝ); exact mul_pos hb.1 ht
          · change b*(t:ℝ) < 1
            exact (mul_le_of_le_one_right hb.1.le t.property.2).trans_lt hb.2
        exact a.property.2.2.2 (τ t) hτint hcB
      let k : Interval × Set.Icc (-1 : ℝ) 1 → ℝ × ℝ :=
        fun z => ((c z.1).1,(ε/2)*(z.2:ℝ))
      have hkc : Continuous k := by dsimp [k]; fun_prop
      have hkV (z : Interval × Set.Icc (-1 : ℝ) 1) : k z ∈ V := by
        apply hεV
        change dist (k z) (0,0) < ε
        rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero]
        apply max_lt
        · have hc := (max_lt_iff.mp (by simpa only [Prod.dist_eq,Real.dist_eq,sub_zero] using hcsmall z.1)).1
          exact hc.trans (by linarith)
        · change |(ε/2)*(z.2:ℝ)| < ε
          rw [abs_mul,abs_of_pos (half_pos hε)]
          exact (mul_le_of_le_one_right (half_pos hε).le (abs_le.mpr z.2.property)).trans_lt (by linarith)
      let F : Interval × Set.Icc (-1 : ℝ) 1 → S :=
        fun z => (h.symm ⟨k z,hkV z⟩ : U)
      have hFc : Continuous F := continuous_subtype_val.comp
        (h.symm.continuous.comp (hkc.subtype_mk _))
      have hFk (z) : ((h ⟨F z,(h.symm ⟨k z,hkV z⟩).property⟩ : V) : ℝ × ℝ) = k z := by
        exact congrArg Subtype.val (h.apply_symm_apply ⟨k z,hkV z⟩)
      have hFi : Function.Injective F := by
        intro z w he
        have hh : k z = k w := (hFk z).symm.trans
          ((congrArg (fun y : U => ((h y : V) : ℝ × ℝ)) (Subtype.ext he)).trans (hFk w))
        have hwidth : (z.2:ℝ) = (w.2:ℝ) :=
          mul_left_cancel₀ (half_pos hε).ne' (congrArg Prod.snd hh)
        have hfirstK := congrArg (fun v : ℝ × ℝ => v.1) hh
        have hfirst : (c z.1).1 = (c w.1).1 := hfirstK
        have hcent : c z.1 = c w.1 := Prod.ext hfirst
          ((hcaxis z.1).2.trans (hcaxis w.1).2.symm)
        have hpoint : f (τ z.1) = f (τ w.1) := congrArg (fun y : U => (y : S))
          (h.injective (Subtype.ext hcent))
        have hparam : τ z.1 = τ w.1 := a.property.1.injective (Subtype.ext hpoint)
        exact Prod.ext (hτi hparam) (Subtype.ext hwidth)
      have boundary_avoids_disk (y : S) (hy : y ∈ boundaryCircle S x R) : y ∉ openDisk S x R := by
        rintro ⟨u,hu,heu⟩
        obtain ⟨v,hv,hev⟩ := hy
        have huv : u = v := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.injOn
          (htarget (Metric.ball_subset_closedBall hu))
          (htarget (Metric.sphere_subset_closedBall hv)) (heu.trans hev.symm)
        exact (ne_of_lt (Metric.mem_ball.mp hu)) (huv ▸ Metric.mem_sphere.mp hv)
      have hFQ (z : Interval × Set.Icc (-1 : ℝ) 1) : F z ∉ openDisk S x R := by
        intro ho
        have hD : F z ∈ CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.closedDisk S x R :=
          Set.image_mono Metric.ball_subset_closedBall ho
        have hnonpos := (hdisk (F z) (h.symm ⟨k z,hkV z⟩).property).mp hD
        rw [hFk] at hnonpos
        change (c z.1).1 ≤ 0 at hnonpos
        have hzeroX : (c z.1).1 = 0 := le_antisymm hnonpos (hcaxis z.1).1
        have hB : F z ∈ boundaryCircle S x R :=
          (hboundary (F z) (h.symm ⟨k z,hkV z⟩).property).mpr (by rw [hFk]; exact hzeroX)
        exact boundary_avoids_disk (F z) hB ho
      let E : C(Interval × Set.Icc (-1 : ℝ) 1,Q S x R) :=
        ⟨fun z => ⟨F z,hFQ z⟩,hFc.subtype_mk _⟩
      have hE : Topology.IsEmbedding E := (E.continuous.isClosedEmbedding (by
        intro z w he
        exact hFi (congrArg (fun y : Q S x R => (y : S)) he))).isEmbedding
      have hcenter (t : Interval) : E (t,⟨0,by norm_num⟩) = a.val (τ t) := by
        apply Subtype.ext
        change F (t,⟨0,by norm_num⟩) = f (τ t)
        have hh : h ⟨F (t,⟨0,by norm_num⟩),(h.symm ⟨k (t,⟨0,by norm_num⟩),hkV _⟩).property⟩ =
            h ⟨f (τ t),hfU t⟩ := by
          apply Subtype.ext
          rw [hFk]
          change ((c t).1,(ε/2)*0) = c t
          exact Prod.ext (by rfl) (by simpa only [mul_zero] using (hcaxis t).2.symm)
        exact congrArg (fun y : U => (y : S)) (h.injective hh)
      refine ⟨b,hb,E,hE,hcenter,?_,?_,?_⟩
      · intro w
        change F (0,w) ∈ boundaryCircle S x R
        apply (hboundary _ _).mpr
        rw [hFk]
        change (c 0).1 = 0
        rw [hc0]
      · intro t ht w hB
        have hh := (hboundary (F (t,w)) (h.symm ⟨k (t,w),hkV (t,w)⟩).property).mp hB
        rw [hFk] at hh
        exact (hcpos t ht).ne' hh
      · intro z
        constructor
        · rintro ⟨t,ht⟩
          have htrace : F z ∈ Subtype.val '' Set.range a.val :=
            ⟨a.val t,Set.mem_range_self t,congrArg Subtype.val ht⟩
          have hh := ((haxis (F z) (h.symm ⟨k z,hkV z⟩).property).mp htrace).2
          rw [hFk] at hh
          change (ε/2)*(z.2:ℝ) = 0 at hh
          exact (mul_eq_zero.mp hh).resolve_left (half_pos hε).ne'
        · intro hw
          have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hw)
          refine ⟨τ z.1,?_⟩
          rw [he,hcenter]
  
  have actual_original_boundary_half_band_initial_neighborhood
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ boundaryQ S x R)
      (w : Set.Icc (-1 : ℝ) 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1)
      (anchor : ProperArc S x R) (hanchor : E (0,w)=anchor.val 0) :
      ∃ N : Set (Q S x R), IsOpen N ∧ E (0,w) ∈ N ∧
        N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    clear * - S x R g hg hS hR htarget E hE hend hproper w hw anchor hanchor
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨U,V,hpU,h,hU,hV,hzero,hother,hdisk,hboundary,haxis⟩ :=
      CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.source_proper_arc_initial_endpoint_attached_axis_chart
        S g hg hS x R hR htarget anchor.val anchor.property.1 anchor.property.2.1
        anchor.property.2.2.1 (fun t ht => anchor.property.2.2.2 t ht)
    have hpU0 : (E (0,w)).val∈U := (congrArg Subtype.val hanchor.symm) ▸ hpU
    let f : C(Interval × Set.Icc (-1 : ℝ) 1,S) :=
      ⟨fun z => (E z).val,continuous_subtype_val.comp E.continuous⟩
    have hp : f (0,w) ∈ U := hpU0
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
      ((hU.preimage f.continuous).mem_nhds hp)
    let a : ℝ := min (r/4) (1/2)
    have ha : 0 < a ∧ a < 1 :=
      ⟨lt_min (by positivity) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have har : a < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let η : ℝ := min (r/4) (min ((1-(w:ℝ))/2) ((1+(w:ℝ))/2))
    have hη : 0 < η := lt_min (by positivity)
      (lt_min (by linarith [hw.2]) (by linarith [hw.1]))
    have hηr : η < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηlo : η ≤ (1+(w:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hηhi : η ≤ (1-(w:ℝ))/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hwstrict (u : Set.Icc (-1 : ℝ) 1) : -1 < (w:ℝ)+η*(u:ℝ) ∧
        (w:ℝ)+η*(u:ℝ) < 1 := by
      constructor <;> nlinarith [u.property.1,u.property.2,hw.1,hw.2]
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
      (⟨a*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,ha.1,ha.2]⟩,
        ⟨(w:ℝ)+η*(z.2:ℝ),⟨(hwstrict z.2).1.le,(hwstrict z.2).2.le⟩⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z v he
      apply Prod.ext
      · apply Subtype.ext
        exact mul_left_cancel₀ ha.1.ne' (congrArg (fun p => (p.1:ℝ)) he)
      · apply Subtype.ext
        have hh := congrArg (fun p => (p.2:ℝ)) he
        change (w:ℝ)+η*(z.2:ℝ) = (w:ℝ)+η*(v.2:ℝ) at hh
        nlinarith
    have hfkU (z) : f (k z) ∈ U := by
      apply hrU
      rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      apply max_lt
      · change |a*(z.1:ℝ)-0| < r
        rw [sub_zero,abs_of_nonneg (mul_nonneg ha.1.le z.1.property.1)]
        exact (mul_le_of_le_one_right ha.1.le z.1.property.2).trans_lt har
      · change |((w:ℝ)+η*(z.2:ℝ))-(w:ℝ)| < r
        have he : ((w:ℝ)+η*(z.2:ℝ))-(w:ℝ) = η*(z.2:ℝ) := by ring
        rw [he,abs_mul,abs_of_pos hη]
        exact (mul_le_of_le_one_right hη.le (abs_le.mpr z.2.property)).trans_lt hηr
    have outside_nonneg (y : S) (hy : y ∈ U) (hQ : y ∉ openDisk S x R) :
        0 ≤ (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 := by
      by_contra hn
      have hneg : (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 < 0 := lt_of_not_ge hn
      obtain ⟨z,hz,he⟩ := (hdisk y hy).mpr hneg.le
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlo | heq
      · exact hQ ⟨z,Metric.mem_ball.mpr hlo,he⟩
      · have hB : y ∈ CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.boundary S x R :=
          ⟨z,Metric.mem_sphere.mpr heq,he⟩
        exact hneg.ne ((hboundary y hy).mp hB)
    let coord : U → Schoenflies.Plane := fun y => Schoenflies.Plane.mk
      (((h y : V) : ℝ × ℝ)).1 (((h y : V) : ℝ × ℝ)).2
    have hcoord : Continuous coord := by dsimp [coord]; fun_prop
    have hcoordi : Function.Injective coord := by
      intro y z he
      apply h.injective
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun p : Schoenflies.Plane => p 0) he
      · exact congrArg (fun p : Schoenflies.Plane => p 1) he
    let C : C(Interval × Set.Icc (-1 : ℝ) 1,Schoenflies.Plane) :=
      ⟨fun z => coord ⟨f (k z),hfkU z⟩,
        hcoord.comp ((f.continuous.comp hkc).subtype_mk _)⟩
    have hCi : Function.Injective C := by
      intro z v he
      have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
      have hEk : E (k z) = E (k v) := Subtype.ext hh
      exact hki (hE.injective hEk)
    have hC : Topology.IsEmbedding C := (C.continuous.isClosedEmbedding hCi).isEmbedding
    have hCzero (u : Set.Icc (-1 : ℝ) 1) : C (0,u) 0 = 0 := by
      apply (hboundary (f (k (0,u))) (hfkU (0,u))).mp
      have hk0 : (k (0,u)).1 = 0 := Subtype.ext (by change a*0=0; ring)
      change (E (k (0,u))).val ∈ boundaryCircle S x R
      have he : k (0,u) = (0,(k (0,u)).2) := Prod.ext hk0 rfl
      rw [he]
      exact hend _
    have hCpos (t : Interval) (ht : 0 < (t:ℝ)) (u : Set.Icc (-1 : ℝ) 1) :
        0 < C (t,u) 0 := by
      have hn := outside_nonneg (f (k (t,u))) (hfkU (t,u)) (E (k (t,u))).property
      apply lt_of_le_of_ne hn
      intro he
      have hB := (hboundary (f (k (t,u))) (hfkU (t,u))).mpr he.symm
      have hti : (k (t,u)).1 ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · change 0 < a*(t:ℝ); exact mul_pos ha.1 ht
        · change a*(t:ℝ) < 1
          exact (mul_le_of_le_one_right ha.1.le t.property.2).trans_lt ha.2
      exact hproper _ hti _ hB
    let P : Set {p : Schoenflies.Plane | 0 ≤ p 0} :=
      {y | y.val ∈ C '' {z | (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1}}
    have hP : IsOpen P := halfPlaneBandOpenness C hC hCzero hCpos
    let W : Set (Q S x R) := Subtype.val ⁻¹' U
    have hW : IsOpen W := hU.preimage continuous_subtype_val
    let J : W → U := fun y => ⟨y.val.val,y.property⟩
    have hJ : Continuous J := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let H : W → {p : Schoenflies.Plane | 0 ≤ p 0} := fun y =>
      ⟨coord (J y),outside_nonneg y.val.val y.property y.val.property⟩
    have hH : Continuous H := (hcoord.comp hJ).subtype_mk _
    let K : Set W := H ⁻¹' P
    have hK : IsOpen K := hP.preimage hH
    let N : Set (Q S x R) := Subtype.val '' K
    have hN : IsOpen N := hW.isOpenMap_subtype_val K hK
    have hk00 : k (0,⟨0,by norm_num⟩) = (0,w) := by
      apply Prod.ext
      · apply Subtype.ext; change a*0=0; ring
      · apply Subtype.ext; change (w:ℝ)+η*0=(w:ℝ); ring
    have hpN : E (0,w) ∈ N := by
      refine ⟨⟨E (0,w),hp⟩,?_,rfl⟩
      change coord (J ⟨E (0,w),hp⟩) ∈ C '' _
      refine ⟨(0,⟨0,by norm_num⟩),⟨by norm_num,by norm_num,by norm_num⟩,?_⟩
      change coord ⟨f (k (0,⟨0,by norm_num⟩)),hfkU _⟩ =
        coord ⟨(E (0,w)).val,hp⟩
      apply congrArg coord
      apply Subtype.ext
      change (E (k (0,⟨0,by norm_num⟩))).val = (E (0,w)).val
      rw [hk00]
    refine ⟨N,hN,hpN,?_⟩
    rintro y ⟨u,hu,rfl⟩
    change coord (J u) ∈ C '' _ at hu
    obtain ⟨z,hz,he⟩ := hu
    have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
    have hEq : E (k z) = u.val := Subtype.ext hh
    exact ⟨k z,hwstrict z.2,hEq⟩
  have actual_originalQ_embedded_disk_interior_dense
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R)) :
      Set.range D ⊆ closure (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    let A : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    have hAimage : Subtype.val '' A=Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      apply Set.Subset.antisymm
      · rintro y ⟨z,hz,rfl⟩; exact hz
      · intro y hy
        exact ⟨⟨y,Metric.ball_subset_closedBall hy⟩,hy,rfl⟩
    have hAdense : closure A=Set.univ := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hAimage,
        closure_ball _ (by norm_num : (1 : ℝ)≠0)]
      ext z
      simp only [Set.mem_preimage,Set.mem_univ,iff_true]
      exact z.property
    have hcl := D.continuous.continuousOn.image_closure (s := A)
    rintro y ⟨z,rfl⟩
    apply hcl
    exact ⟨z,hAdense.symm ▸ Set.mem_univ z,rfl⟩
  have actual_originalQ_embedded_disk_interior_preconnected
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R)) :
      IsPreconnected (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    let A : Set (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    have hAimage : Subtype.val '' A=Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      apply Set.Subset.antisymm
      · rintro y ⟨z,hz,rfl⟩; exact hz
      · intro y hy
        exact ⟨⟨y,Metric.ball_subset_closedBall hy⟩,hy,rfl⟩
    have hA : IsPreconnected A :=
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        (hAimage.symm ▸ (convex_ball (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ)).isPreconnected)
    exact hA.image D D.continuous.continuousOn
  have actual_originalQ_disk_interior_containment_closes
      (D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hinside : D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ Set.range E) :
      Set.range D ⊆ Set.range E := by
    exact (actual_originalQ_embedded_disk_interior_dense D).trans
      (closure_minimal hinside (isCompact_range E.continuous).isClosed)
  have actual_originalQ_disk_interior_clearance_from_exterior_witness
      (D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D)
      (hboundary : Disjoint
        (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}))
      (y : Q S x R) (hyE : y∈Set.range E) (hyD : y∉Set.range D) :
      Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (Set.range D) := by
    rcases actual_connected_originalQ_set_disk_side_dichotomy D hD
      (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (actual_originalQ_embedded_disk_interior_preconnected E) hboundary with hinside | houtside
    · have hwhole := actual_originalQ_disk_interior_containment_closes E D
        (hinside.trans (Set.image_subset_range _ _))
      exact False.elim (hyD (hwhole hyE))
    · exact houtside
  have actual_boundary_parallel_disk_has_relative_neighborhood_away_from_old_arc
      (d : ProperArc S x R) (bd : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbdB : ∀ t,bd t∈boundaryQ S x R)
      (D : C(Metric.closedBall (0 : Plane) 1,Q S x R)) (hD : Topology.IsEmbedding D)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (y : Q S x R) (hybd : y∈Set.range bd) (hyd : y∉Set.range d.val) :
      ∃ U : Set (Q S x R),IsOpen U ∧ y∈U ∧ U ⊆ Set.range D ∧
        U \ boundaryQ S x R ⊆ D '' {z | z.val∈Metric.ball (0 : Plane) 1} := by
    obtain ⟨s,hsy⟩ := hybd
    have hChord : ∃ c : ProperArc S x R,c.val 0=y ∧ Set.range c.val ⊆ Set.range D := by
      by_cases hs : s=0
      · have hs1 : s≠1 := fun he => (show (0 : Interval)≠1 by norm_num) (hs.symm.trans he)
        obtain ⟨c,hc0,hc1,hcD⟩ := actual_boundary_parallel_disk_two_boundary_points_have_internal_chord
          d bd hbd hbdB D hD hDb s 1 hs1
        exact ⟨c,hc0.trans hsy,hcD⟩
      · obtain ⟨c,hc0,hc1,hcD⟩ := actual_boundary_parallel_disk_two_boundary_points_have_internal_chord
          d bd hbd hbdB D hD hDb s 0 hs
        exact ⟨c,hc0.trans hsy,hcD⟩
    obtain ⟨c,hc0,hcD⟩ := hChord
    obtain ⟨b,hb,E,hE,hEc,hEb,hEi,hEa⟩ :=
      actual_original_boundary_endpoint_seed_for_disk_clearance g hg hS hR htarget c
    let zero : Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    have hE00 : E (0,zero)=y := by
      have h0 : E (0,zero)=c.val 0 := by
        have ht : (⟨b*(↑(0 : Interval) : ℝ), by constructor <;> simp⟩ : Interval)=0 :=
          Subtype.ext (by simp)
        simpa only [ht] using hEc 0
      exact h0.trans hc0
    let O := (Set.range d.val)ᶜ
    have hO : IsOpen O := (isCompact_range d.val.continuous).isClosed.isOpen_compl
    have hEO : E (0,zero)∈O := hE00.symm ▸ hyd
    obtain ⟨r,hr,hrO⟩ := Metric.mem_nhds_iff.mp
      ((hO.preimage E.continuous).mem_nhds hEO)
    let δ : ℝ := min (r/2) (1/2)
    have hδ : 0<δ := lt_min (half_pos hr) (by norm_num)
    have hδ1 : δ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hδr : δ<r := (min_le_left _ _).trans_lt (by linarith only [hr])
    let k : Interval × Icc (-1 : ℝ) 1 → Interval × Icc (-1 : ℝ) 1 := fun z =>
      (⟨δ*(z.1:ℝ),⟨mul_nonneg hδ.le z.1.property.1,
        (mul_le_of_le_one_right hδ.le z.1.property.2).trans hδ1.le⟩⟩,
       ⟨δ*(z.2:ℝ),by constructor <;>
        nlinarith only [hδ,hδ1,z.2.property.1,z.2.property.2]⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z v he
      have h1 := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => (p.1:ℝ)) he
      have h2 := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => (p.2:ℝ)) he
      exact Prod.ext (Subtype.ext (mul_left_cancel₀ hδ.ne' h1))
        (Subtype.ext (mul_left_cancel₀ hδ.ne' h2))
    let N : C(Interval × Icc (-1 : ℝ) 1,Q S x R) := ⟨E ∘ k,E.continuous.comp hkc⟩
    have hN : Topology.IsEmbedding N := hE.comp ((hkc.isClosedEmbedding hki).isEmbedding)
    have hNavoid (z : Interval × Icc (-1 : ℝ) 1) : N z∉Set.range d.val := by
      apply hrO
      rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      apply max_lt
      · change |δ*(z.1:ℝ)-0|<r
        rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le z.1.property.1)]
        exact (mul_le_of_le_one_right hδ.le z.1.property.2).trans_lt hδr
      · change |δ*(z.2:ℝ)-0|<r
        rw [sub_zero,abs_mul,abs_of_pos hδ]
        exact (mul_le_of_le_one_right hδ.le (abs_le.mpr z.2.property)).trans_lt hδr
    have hNstart (w : Icc (-1 : ℝ) 1) : N (0,w)∈boundaryQ S x R := by
      have hk0 : (k (0,w)).1=0 := Subtype.ext (by change δ*0=0; ring)
      have he : k (0,w)=(0,(k (0,w)).2) := Prod.ext hk0 rfl
      change E (k (0,w))∈boundaryQ S x R
      rw [he]; exact hEb _
    have hNpositive (t : Interval) (ht : 0<(t:ℝ)) (w : Icc (-1 : ℝ) 1) :
        N (t,w)∉boundaryQ S x R :=
      hEi (k (t,w)).1 (mul_pos hδ ht) (k (t,w)).2
    have hk00 : k (0,zero)=(0,zero) := by
      apply Prod.ext
      · apply Subtype.ext; change δ*0=0; ring
      · apply Subtype.ext; change δ*0=0; ring
    have hN00 : N (0,zero)=y := by change E (k (0,zero))=y; rw [hk00,hE00]
    have hanchor : N (0,zero)=c.val 0 := hN00.trans hc0.symm
    obtain ⟨U,hU,hNU,hUsub⟩ := actual_original_boundary_half_band_initial_neighborhood
      g hg hS hR htarget N hN hNstart (fun t ht w => hNpositive t ht.1 w)
      zero (by constructor <;> norm_num [zero]) c hanchor
    let K := N '' (Ioi (0 : Interval) ×ˢ (Set.univ : Set (Icc (-1 : ℝ) 1)))
    letI : PreconnectedSpace (Icc (-1 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
    have hK : IsPreconnected K := (isPreconnected_Ioi.prod isPreconnected_univ).image N N.continuous.continuousOn
    have hKbd : Disjoint K (D '' {z | z.val∈Metric.sphere (0 : Plane) 1}) := by
      rw [hDb]
      apply Set.disjoint_left.mpr
      rintro z ⟨v,hv,rfl⟩ (hz | hz)
      · exact hNavoid v hz
      · obtain ⟨t,ht⟩ := hz
        exact hNpositive v.1 hv.1 v.2 (ht ▸ hbdB t)
    have hNK : N (1,zero)∈K := ⟨(1,zero),⟨by norm_num,Set.mem_univ _⟩,rfl⟩
    have hND : N (1,zero)∈Set.range D := by
      have hw0 : (k (1,zero)).2=zero := Subtype.ext (by change δ*0=0; ring)
      have he : k (1,zero)=((k (1,zero)).1,zero) := Prod.ext rfl hw0
      change E (k (1,zero))∈Set.range D
      rw [he,hEc]
      exact hcD (Set.mem_range_self _)
    have hKinside : K ⊆ D '' {z | z.val∈Metric.ball (0 : Plane) 1} := by
      rcases actual_connected_originalQ_set_disk_side_dichotomy D hD K hK hKbd with hi | ho
      · exact hi
      · exact False.elim (Set.disjoint_left.mp ho hNK hND)
    have hclosed : IsClosed (N ⁻¹' Set.range D) :=
      (isCompact_range D.continuous).isClosed.preimage N.continuous
    have hprod : Ioo (0 : Interval) 1 ×ˢ (Set.univ : Set (Icc (-1 : ℝ) 1)) ⊆ N ⁻¹' Set.range D := by
      intro z hz
      exact Set.image_subset_range _ _ (hKinside ⟨z,⟨hz.1.1,Set.mem_univ _⟩,rfl⟩)
    have hprodcl : closure (Ioo (0 : Interval) 1 ×ˢ (Set.univ : Set (Icc (-1 : ℝ) 1)))=Set.univ := by
      rw [closure_prod_eq,closure_Ioo (show (0 : Interval)≠1 by norm_num),closure_univ]
      apply Set.eq_univ_iff_forall.mpr
      intro z
      exact ⟨⟨z.1.property.1,z.1.property.2⟩,Set.mem_univ _⟩
    have hfull := hclosed.closure_subset_iff.mpr hprod
    rw [hprodcl] at hfull
    have hNsub : Set.range N ⊆ Set.range D := by
      rintro z ⟨v,rfl⟩; exact hfull (Set.mem_univ v)
    refine ⟨U,hU,hN00 ▸ hNU,?_,?_⟩
    · exact (hUsub.trans (Set.image_subset_range _ _)).trans hNsub
    · rintro z ⟨hz,hzB⟩
      obtain ⟨v,hv,hvz⟩ := hUsub hz
      have ht0 : v.1≠0 := by
        intro he
        have hv0 : v=(0,v.2) := Prod.ext he rfl
        exact hzB (hvz ▸ (hv0.symm ▸ hNstart v.2))
      have htv : (0 : Interval)<v.1 := lt_of_le_of_ne v.1.property.1 (Ne.symm ht0)
      exact hKinside ⟨v,⟨htv,Set.mem_univ _⟩,hvz⟩
  have actual_exterior_parallel_disk_boundary_arcs_meet_only_on_old_arcs
      (d e : ProperArc S x R) (bd be : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbe : Topology.IsEmbedding be)
      (hbdB : ∀ t,bd t∈boundaryQ S x R) (hbeB : ∀ t,be t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : Plane) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (hE : Topology.IsEmbedding E)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range e.val ∪ Set.range be)
      (hDE : Disjoint (D '' {z | z.val∈Metric.ball (0 : Plane) 1}) (Set.range E)) :
      Set.range bd ∩ Set.range be ⊆ Set.range d.val ∪ Set.range e.val := by
    intro y hy
    by_contra hnot
    have hyd : y∉Set.range d.val := fun h => hnot (Or.inl h)
    have hye : y∉Set.range e.val := fun h => hnot (Or.inr h)
    obtain ⟨U,hU,hyU,hUD,hUi⟩ :=
      actual_boundary_parallel_disk_has_relative_neighborhood_away_from_old_arc
        d bd hbd hbdB D hD hDb y hy.1 hyd
    obtain ⟨V,hV,hyV,hVE,hVi⟩ :=
      actual_boundary_parallel_disk_has_relative_neighborhood_away_from_old_arc
        e be hbe hbeB E hE hEb y hy.2 hye
    obtain ⟨s,hsy⟩ := hy.1
    have hChord : ∃ c : ProperArc S x R,c.val 0=y := by
      by_cases hs : s=0
      · have hs1 : s≠1 := fun he => (show (0 : Interval)≠1 by norm_num) (hs.symm.trans he)
        obtain ⟨c,hc0,hc1,hcD⟩ := actual_boundary_parallel_disk_two_boundary_points_have_internal_chord
          d bd hbd hbdB D hD hDb s 1 hs1
        exact ⟨c,hc0.trans hsy⟩
      · obtain ⟨c,hc0,hc1,hcD⟩ := actual_boundary_parallel_disk_two_boundary_points_have_internal_chord
          d bd hbd hbdB D hD hDb s 0 hs
        exact ⟨c,hc0.trans hsy⟩
    obtain ⟨c,hc0⟩ := hChord
    have hzero : (0 : Interval)∈c.val ⁻¹' (U ∩ V) := by
      change c.val 0∈U ∩ V
      rw [hc0]
      exact ⟨hyU,hyV⟩
    obtain ⟨r,hr,hrUV⟩ := Metric.mem_nhds_iff.mp
      (((hU.inter hV).preimage c.val.continuous).mem_nhds hzero)
    let τ : ℝ := min (r/2) (1/2)
    have hτ : 0<τ := lt_min (half_pos hr) (by norm_num)
    have hτ1 : τ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hτr : τ<r := (min_le_left _ _).trans_lt (by linarith only [hr])
    let t : Interval := ⟨τ,⟨hτ.le,hτ1.le⟩⟩
    have htUV : c.val t∈U ∩ V := by
      apply hrUV
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |τ-0|<r
      simpa only [sub_zero,abs_of_pos hτ] using hτr
    have htB : c.val t∉boundaryQ S x R := c.property.2.2.2 t ⟨hτ,hτ1⟩
    exact Set.disjoint_left.mp hDE (hUi ⟨htUV.1,htB⟩) (hVE htUV.2)
  have actual_exterior_parallel_disk_old_arc_meets_other_boundary_arc_only_on_other_old_arc
      (d e : ProperArc S x R) (be : C(Interval,Q S x R))
      (hbe : Topology.IsEmbedding be) (hbeB : ∀ t,be t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : Plane) 1,Q S x R))
      (hE : Topology.IsEmbedding E)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range e.val ∪ Set.range be)
      (hdD : Set.range d.val ⊆ Set.range D)
      (hED : Disjoint (E '' {z | z.val∈Metric.ball (0 : Plane) 1}) (Set.range D)) :
      Set.range d.val ∩ Set.range be ⊆ Set.range e.val := by
    intro y hy
    by_contra hye
    obtain ⟨U,hU,hyU,hUE,hUi⟩ :=
      actual_boundary_parallel_disk_has_relative_neighborhood_away_from_old_arc
        e be hbe hbeB E hE hEb y hy.2 hye
    obtain ⟨s,hsy⟩ := hy.1
    have hscl : s∈closure (Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (show (0 : Interval)≠1 by norm_num)]
      exact s.property
    obtain ⟨t,htU,ht⟩ := mem_closure_iff.mp hscl (d.val ⁻¹' U)
      (hU.preimage d.val.continuous) (show s∈d.val ⁻¹' U from by change d.val s∈U; rw [hsy]; exact hyU)
    have htB := d.property.2.2.2 t ht
    exact Set.disjoint_left.mp hED (hUi ⟨htU,htB⟩) (hdD (Set.mem_range_self t))
  have actual_exterior_parallel_disks_intersection_is_old_arcs_intersection
      (d e : ProperArc S x R) (bd be : C(Interval,Q S x R))
      (hbd : Topology.IsEmbedding bd) (hbe : Topology.IsEmbedding be)
      (hbdB : ∀ t,bd t∈boundaryQ S x R) (hbeB : ∀ t,be t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : Plane) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (hE : Topology.IsEmbedding E)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range e.val ∪ Set.range be)
      (hED : Disjoint (E '' {z | z.val∈Metric.ball (0 : Plane) 1}) (Set.range D))
      (hDE : Disjoint (D '' {z | z.val∈Metric.ball (0 : Plane) 1}) (Set.range E)) :
      Set.range D ∩ Set.range E=Set.range d.val ∩ Set.range e.val := by
    have hdD : Set.range d.val ⊆ Set.range D := by
      intro y hy
      exact Set.image_subset_range _ _ (hDb.symm ▸ (show y∈Set.range d.val ∪ Set.range bd from Or.inl hy))
    have heE : Set.range e.val ⊆ Set.range E := by
      intro y hy
      exact Set.image_subset_range _ _ (hEb.symm ▸ (show y∈Set.range e.val ∪ Set.range be from Or.inl hy))
    have hde := actual_exterior_parallel_disk_old_arc_meets_other_boundary_arc_only_on_other_old_arc
      d e be hbe hbeB D E hE hEb hdD hED
    have hed := actual_exterior_parallel_disk_old_arc_meets_other_boundary_arc_only_on_other_old_arc
      e d bd hbd hbdB E D hD hDb heE hDE
    have hbdbe := actual_exterior_parallel_disk_boundary_arcs_meet_only_on_old_arcs
      d e bd be hbd hbe hbdB hbeB D E hD hE hDb hEb hDE
    apply Set.Subset.antisymm
    · intro y hy
      have hballs : Metric.closedBall (0 : Plane) 1 ⊆
          Metric.ball (0 : Plane) 1 ∪ Metric.sphere (0 : Plane) 1 := by
        rw [Metric.ball_union_sphere]
      obtain ⟨z,hz⟩ := hy.1
      obtain ⟨w,hw⟩ := hy.2
      have hzS : z.val∈Metric.sphere (0 : Plane) 1 := by
        rcases hballs z.property with hi | hs
        · exact False.elim (Set.disjoint_left.mp hDE ⟨z,hi,hz⟩ hy.2)
        · exact hs
      have hwS : w.val∈Metric.sphere (0 : Plane) 1 := by
        rcases hballs w.property with hi | hs
        · exact False.elim (Set.disjoint_left.mp hED ⟨w,hi,hw⟩ hy.1)
        · exact hs
      have hd := hDb ▸ (show y∈D '' {z | z.val∈Metric.sphere (0 : Plane) 1} from ⟨z,hzS,hz⟩)
      have he := hEb ▸ (show y∈E '' {z | z.val∈Metric.sphere (0 : Plane) 1} from ⟨w,hwS,hw⟩)
      rcases hd with hd | hbdY
      · rcases he with he | hbeY
        · exact ⟨hd,he⟩
        · exact ⟨hd,hde ⟨hd,hbeY⟩⟩
      · rcases he with he | hbeY
        · exact ⟨hed ⟨he,hbdY⟩,he⟩
        · rcases hbdbe ⟨hbdY,hbeY⟩ with hd | he
          · exact ⟨hd,hde ⟨hd,hbeY⟩⟩
          · exact ⟨hed ⟨he,hbdY⟩,he⟩
    · intro y hy; exact ⟨hdD hy.1,heE hy.2⟩
  have actual_terminal_left_disk_boundary_avoids_right_disk_interior
      (b d e : ProperArc S x R) (u v : Interval) (hu0 : 0<u)
      (hcross : b.val u=a0.val.val v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (bd be : C(Interval,Q S x R)) (hbd : ∀ t,bd t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hE : Topology.IsEmbedding E)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range d.val ∪ Set.range bd)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range e.val ∪ Set.range be)
      (houtside : Disjoint (b.val '' Ioo 0 u) (Set.range E)) :
      Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    have hEintbd : Disjoint
        (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨z,hz,rfl⟩ ⟨w,hw,he⟩
      have hzw := hE.injective he
      have hwz : z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := hzw ▸ hw
      have hlt : dist z.val (0 : EuclideanSpace ℝ (Fin 2))<1 := hz
      have heq : dist z.val (0 : EuclideanSpace ℝ (Fin 2))=1 := hwz
      exact (ne_of_lt hlt) heq
    have hEintQbd := actual_original_embedded_disk_interior_boundary_clearance E hE
    have hepart : Set.range e.val ⊆
        E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      intro y hy
      rw [hEb]
      exact Or.inl hy
    have htailpart : Set.range (CurveComplex.BranchedDoubleCover.actualSubpath
        (properPath a0.val) v 1) ⊆ Set.range e.val := by
      rw [heimage]
      exact Set.subset_union_right
    apply Set.disjoint_left.mpr
    intro y hy hDy
    rw [hDb] at hDy
    rcases hDy with hd | hbdy
    · rw [hdimage] at hd
      rcases hd with hprefix | htail
      · obtain ⟨q,hq⟩ := hprefix
        let t := CurveComplex.BranchedDoubleCover.intervalAffine 0 u q
        have ht : b.val t=y := hq
        have htu : t≤u :=
          (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu0.le q).2
        by_cases ht0 : t=0
        · have hby : y∈boundaryQ S x R := by rw [← ht,ht0]; exact b.property.2.1
          exact Set.disjoint_left.mp hEintQbd hy hby
        by_cases htuEq : t=u
        · have hycut : y=a0.val.val v := by rw [← ht,htuEq,hcross]
          have htailzero : CurveComplex.BranchedDoubleCover.intervalAffine v 1 0=v := by
            apply Subtype.ext
            change (1-(0:ℝ))*(v:ℝ)+0*1=(v:ℝ)
            ring
          apply Set.disjoint_left.mp hEintbd hy
          apply hepart
          apply htailpart
          refine ⟨0,?_⟩
          change a0.val.val (CurveComplex.BranchedDoubleCover.intervalAffine v 1 0)=y
          rw [htailzero,hycut]
        have hto : t∈Ioo 0 u := ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
          lt_of_le_of_ne htu htuEq⟩
        exact Set.disjoint_left.mp houtside ⟨t,hto,ht⟩
          (Set.image_subset_range _ _ hy)
      · exact Set.disjoint_left.mp hEintbd hy (hepart (htailpart htail))
    · obtain ⟨t,rfl⟩ := hbdy
      exact Set.disjoint_left.mp hEintQbd hy (hbd t)
  have actual_terminal_right_disk_boundary_avoids_left_disk_interior
      (b e d : ProperArc S x R) (u v : Interval) (hu1 : u<1)
      (hcross : b.val u=a0.val.val v)
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (be bd : C(Interval,Q S x R)) (hbe : ∀ t,be t∈boundaryQ S x R)
      (E D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range e.val ∪ Set.range be)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range d.val ∪ Set.range bd)
      (houtside : Disjoint (b.val '' Ioo u 1) (Set.range D)) :
      Disjoint (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    have hDintbd : Disjoint
        (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨z,hz,rfl⟩ ⟨w,hw,he⟩
      have hzw := hD.injective he
      have hwz : z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := hzw ▸ hw
      have hlt : dist z.val (0 : EuclideanSpace ℝ (Fin 2))<1 := hz
      have heq : dist z.val (0 : EuclideanSpace ℝ (Fin 2))=1 := hwz
      exact (ne_of_lt hlt) heq
    have hDintQbd := actual_original_embedded_disk_interior_boundary_clearance D hD
    have hdpart : Set.range d.val ⊆
        D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      intro y hy
      rw [hDb]
      exact Or.inl hy
    have htailpart : Set.range (CurveComplex.BranchedDoubleCover.actualSubpath
        (properPath a0.val) v 1) ⊆ Set.range d.val := by
      rw [hdimage]
      exact Set.subset_union_right
    apply Set.disjoint_left.mpr
    intro y hy hDy
    rw [hEb] at hDy
    rcases hDy with hd | hbdy
    · rw [heimage] at hd
      rcases hd with hprefix | htail
      · obtain ⟨q,hq⟩ := hprefix
        let t := CurveComplex.BranchedDoubleCover.intervalAffine u 1 q
        have ht : b.val t=y := hq
        have htu : u≤t :=
          (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu1.le q).1
        by_cases ht0 : t=1
        · have hby : y∈boundaryQ S x R := by rw [← ht,ht0]; exact b.property.2.2.1
          exact Set.disjoint_left.mp hDintQbd hy hby
        by_cases htuEq : t=u
        · have hycut : y=a0.val.val v := by rw [← ht,htuEq,hcross]
          have htailzero : CurveComplex.BranchedDoubleCover.intervalAffine v 1 0=v := by
            apply Subtype.ext
            change (1-(0:ℝ))*(v:ℝ)+0*1=(v:ℝ)
            ring
          apply Set.disjoint_left.mp hDintbd hy
          apply hdpart
          apply htailpart
          refine ⟨0,?_⟩
          change a0.val.val (CurveComplex.BranchedDoubleCover.intervalAffine v 1 0)=y
          rw [htailzero,hycut]
        have hto : t∈Ioo u 1 := ⟨lt_of_le_of_ne htu (Ne.symm htuEq),
          lt_of_le_of_ne t.property.2 ht0⟩
        exact Set.disjoint_left.mp houtside ⟨t,hto,ht⟩
          (Set.image_subset_range _ _ hy)
      · exact Set.disjoint_left.mp hDintbd hy (hdpart (htailpart htail))
    · obtain ⟨t,rfl⟩ := hbdy
      exact Set.disjoint_left.mp hDintQbd hy (hbe t)
  have actual_terminal_two_outside_cases_force_whole_disk_clearance
      (b d e : ProperArc S x R) (u v : Interval) (hu0 : 0<u) (hu1 : u<1)
      (hcross : b.val u=a0.val.val v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (bd be : C(Interval,Q S x R)) (hbd : ∀ t,bd t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (hE : Topology.IsEmbedding E)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range d.val ∪ Set.range bd)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range e.val ∪ Set.range be)
      (houtsideLeft : Disjoint (b.val '' Ioo 0 u) (Set.range E))
      (houtsideRight : Disjoint (b.val '' Ioo u 1) (Set.range D)) :
      Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (Set.range D) := by
    have hboundary := actual_terminal_left_disk_boundary_avoids_right_disk_interior
      b d e u v hu0 hcross hdimage heimage bd be hbd D E hE hDb hEb houtsideLeft
    let q : Interval := ⟨(1:ℝ)/2,by norm_num⟩
    let t := CurveComplex.BranchedDoubleCover.intervalAffine u 1 q
    have htu : t∈Ioo u 1 := by
      change (u:ℝ)<(1-(q:ℝ))*(u:ℝ)+(q:ℝ)*1 ∧
        (1-(q:ℝ))*(u:ℝ)+(q:ℝ)*1<1
      dsimp [q]
      constructor <;> nlinarith only [show (u:ℝ)<1 from hu1]
    have hyE : b.val t∈Set.range E := by
      have hysphere : b.val t∈E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [hEb]
        left
        rw [heimage]
        left
        exact ⟨q,rfl⟩
      exact Set.image_subset_range E _ hysphere
    have hyD : b.val t∉Set.range D :=
      fun hy => Set.disjoint_left.mp houtsideRight ⟨t,htu,rfl⟩ hy
    exact actual_originalQ_disk_interior_clearance_from_exterior_witness
      D E hD hboundary (b.val t) hyE hyD
  have actual_terminal_two_outside_cases_force_both_whole_disk_clearances
      (b d e : ProperArc S x R) (u v : Interval) (hu0 : 0<u) (hu1 : u<1)
      (hcross : b.val u=a0.val.val v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (bd be : C(Interval,Q S x R)) (hbd : ∀ t,bd t∈boundaryQ S x R) (hbe : ∀ t,be t∈boundaryQ S x R)
      (D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hD : Topology.IsEmbedding D) (hE : Topology.IsEmbedding E)
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range d.val ∪ Set.range bd)
      (hEb : E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range e.val ∪ Set.range be)
      (houtsideLeft : Disjoint (b.val '' Ioo 0 u) (Set.range E))
      (houtsideRight : Disjoint (b.val '' Ioo u 1) (Set.range D)) :
      Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (Set.range D) ∧
      Disjoint (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (Set.range E) := by
    have hED := actual_terminal_two_outside_cases_force_whole_disk_clearance
      b d e u v hu0 hu1 hcross hdimage heimage bd be hbd D E hD hE hDb hEb houtsideLeft houtsideRight
    have hboundary := actual_terminal_right_disk_boundary_avoids_left_disk_interior
      b e d u v hu1 hcross heimage hdimage be bd hbe E D hD hEb hDb houtsideRight
    let q : Interval := ⟨(1:ℝ)/2,by norm_num⟩
    let t := CurveComplex.BranchedDoubleCover.intervalAffine 0 u q
    have htu : t∈Ioo 0 u := by
      change 0<(1-(q:ℝ))*0+(q:ℝ)*(u:ℝ) ∧
        (1-(q:ℝ))*0+(q:ℝ)*(u:ℝ)<(u:ℝ)
      dsimp [q]
      constructor <;> nlinarith only [show 0<(u:ℝ) from hu0]
    have hyD : b.val t∈Set.range D := by
      have hysphere : b.val t∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [hDb]
        left
        rw [hdimage]
        left
        exact ⟨q,rfl⟩
      exact Set.image_subset_range D _ hysphere
    have hyE : b.val t∉Set.range E :=
      fun hy => Set.disjoint_left.mp houtsideLeft ⟨t,htu,rfl⟩ hy
    exact ⟨hED,actual_originalQ_disk_interior_clearance_from_exterior_witness
      E D hE hboundary (b.val t) hyD hyE⟩
  have actual_originalQ_closed_disks_meet_only_on_both_boundaries
      (D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hDE : Disjoint (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) (Set.range E))
      (hED : Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) (Set.range D)) :
      Set.range D ∩ Set.range E=
        (D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) ∩
        (E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    have hballs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆
        Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∪ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [Metric.ball_union_sphere]
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨z,hz⟩ := hy.1
      obtain ⟨w,hw⟩ := hy.2
      constructor
      · rcases hballs z.property with hball | hsphere
        · exact False.elim (Set.disjoint_left.mp hDE ⟨z,hball,hz⟩ hy.2)
        · exact ⟨z,hsphere,hz⟩
      · rcases hballs w.property with hball | hsphere
        · exact False.elim (Set.disjoint_left.mp hED ⟨w,hball,hw⟩ hy.1)
        · exact ⟨w,hsphere,hw⟩
    · exact Set.inter_subset_inter (Set.image_subset_range _ _) (Set.image_subset_range _ _)
  have actual_terminal_left_disk_inside_case_contains_entire_old_arc
      (b d : ProperArc S x R) (u v : Interval) (hu0 : 0<u) (hu1 : u<1)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (bd : C(Interval,Q S x R))
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range d.val ∪ Set.range bd)
      (hinside : b.val '' Ioo u 1 ⊆
        D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
      Set.range b.val ⊆ Set.range D := by
    have hraw : Set.range d.val ⊆ Set.range D := by
      intro y hy
      have hh : y∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
        hDb.symm ▸ Or.inl hy
      exact Set.image_subset_range _ _ hh
    have hright := actual_original_open_branch_disk_containment_closes b u 1 hu1 D hinside
    rintro y ⟨t,rfl⟩
    by_cases ht : t≤u
    · have hu : 0<(u:ℝ) := hu0
      let q : Interval := ⟨(t:ℝ)/(u:ℝ),⟨div_nonneg t.property.1 hu.le,
        (div_le_one hu).mpr ht⟩⟩
      have hclock : CurveComplex.BranchedDoubleCover.intervalAffine 0 u q=t := by
        apply Subtype.ext
        change (1-(q:ℝ))*0+(q:ℝ)*(u:ℝ)=(t:ℝ)
        dsimp [q]
        field_simp [ne_of_gt hu] <;> ring
      apply hraw
      rw [hdimage]
      left
      refine ⟨q,?_⟩
      change b.val (CurveComplex.BranchedDoubleCover.intervalAffine 0 u q)=b.val t
      rw [hclock]
    · exact hright ⟨t,⟨(lt_of_not_ge ht).le,t.property.2⟩,rfl⟩
  have actual_terminal_right_disk_inside_case_contains_entire_old_arc
      (b e : ProperArc S x R) (u v : Interval) (hu0 : 0<u) (hu1 : u<1)
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (bd : C(Interval,Q S x R))
      (D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R))
      (hDb : D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=
        Set.range e.val ∪ Set.range bd)
      (hinside : b.val '' Ioo 0 u ⊆
        D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) :
      Set.range b.val ⊆ Set.range D := by
    have hraw : Set.range e.val ⊆ Set.range D := by
      intro y hy
      have hh : y∈D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
        hDb.symm ▸ Or.inl hy
      exact Set.image_subset_range _ _ hh
    have hleft := actual_original_open_branch_disk_containment_closes b 0 u hu0 D hinside
    rintro y ⟨t,rfl⟩
    by_cases ht : u≤t
    · have hu : 0<1-(u:ℝ) := sub_pos.mpr hu1
      let q : Interval := ⟨((t:ℝ)-(u:ℝ))/(1-(u:ℝ)),⟨div_nonneg (sub_nonneg.mpr ht) hu.le,
        (div_le_one hu).mpr (sub_le_sub_right t.property.2 _)⟩⟩
      have hclock : CurveComplex.BranchedDoubleCover.intervalAffine u 1 q=t := by
        apply Subtype.ext
        change (1-(q:ℝ))*(u:ℝ)+(q:ℝ)*1=(t:ℝ)
        dsimp [q]
        field_simp [ne_of_gt hu] <;> ring
      apply hraw
      rw [heimage]
      left
      refine ⟨q,?_⟩
      change b.val (CurveComplex.BranchedDoubleCover.intervalAffine u 1 q)=b.val t
      rw [hclock]
    · exact hleft ⟨t,⟨t.property.1,(lt_of_not_ge ht).le⟩,rfl⟩
  have actual_terminal_two_parallel_disks_original_geometry_trichotomy
      (b d e : ProperArc S x R) (u v : Interval)
      (hu0 : 0<u) (hu1 : u<1) (hv1 : v<1)
      (hcross : b.val u=a0.val.val v)
      (htail : ∀ s t : Interval,v≤t → b.val s=a0.val.val t → s=u ∧ t=v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (hdparallel : boundaryParallel S x R d) (heparallel : boundaryParallel S x R e) :
      ∃ bd be : C(Interval,Q S x R), Topology.IsEmbedding bd ∧ Topology.IsEmbedding be ∧
        (∀ t,bd t∈boundaryQ S x R ∧ be t∈boundaryQ S x R) ∧
      ∃ D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R),
        Topology.IsEmbedding D ∧ Topology.IsEmbedding E ∧
        D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=Set.range d.val ∪ Set.range bd ∧
        E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=Set.range e.val ∪ Set.range be ∧
        (Set.range b.val ⊆ Set.range D ∨ Set.range b.val ⊆ Set.range E ∨
          (Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) (Set.range D) ∧
           Disjoint (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) (Set.range E))) := by
    obtain ⟨bd,hbd,hbdB,D,hD,hDb,hDside⟩ :=
      actual_terminal_left_disk_right_branch_side_dichotomy b d u v hu1 hv1 htail hdimage hdparallel
    obtain ⟨be,hbe,hbeB,E,hE,hEb,hEside⟩ :=
      actual_terminal_right_disk_left_branch_side_dichotomy b e u v hu0 hv1 htail heimage heparallel
    refine ⟨bd,be,hbd,hbe,(fun t => ⟨hbdB t,hbeB t⟩),D,E,hD,hE,hDb,hEb,?_⟩
    rcases hDside with hDinside | hDoutside
    · left
      exact actual_terminal_left_disk_inside_case_contains_entire_old_arc
        b d u v hu0 hu1 hdimage bd D hDb hDinside
    · rcases hEside with hEinside | hEoutside
      · right; left
        exact actual_terminal_right_disk_inside_case_contains_entire_old_arc
          b e u v hu0 hu1 heimage be E hEb hEinside
      · right; right
        exact actual_terminal_two_outside_cases_force_both_whole_disk_clearances
          b d e u v hu0 hu1 hcross hdimage heimage bd be hbdB hbeB D E hD hE hDb hEb hEoutside hDoutside
  have actual_essential_old_arc_two_parallel_disks_force_exterior_clearance
      (b : EssentialProperArc S x R) (d e : ProperArc S x R) (u v : Interval)
      (hu0 : 0<u) (hu1 : u<1) (hv1 : v<1)
      (hcross : b.val.val u=a0.val.val v)
      (htail : ∀ s t : Interval,v≤t → b.val.val s=a0.val.val t → s=u ∧ t=v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (hdparallel : boundaryParallel S x R d) (heparallel : boundaryParallel S x R e) :
      ∃ bd be : C(Interval,Q S x R), Topology.IsEmbedding bd ∧ Topology.IsEmbedding be ∧
        (∀ t,bd t∈boundaryQ S x R ∧ be t∈boundaryQ S x R) ∧
      ∃ D E : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q S x R),
        Topology.IsEmbedding D ∧ Topology.IsEmbedding E ∧
        D '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=Set.range d.val ∪ Set.range bd ∧
        E '' {z | z.val∈Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}=Set.range e.val ∪ Set.range be ∧
        Disjoint (E '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) (Set.range D) ∧
        Disjoint (D '' {z | z.val∈Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) (Set.range E) := by
    obtain ⟨bd,be,hbd,hbe,hbdbe,D,E,hD,hE,hDb,hEb,hcases⟩ :=
      actual_terminal_two_parallel_disks_original_geometry_trichotomy
        b.val d e u v hu0 hu1 hv1 hcross htail hdimage heimage hdparallel heparallel
    refine ⟨bd,be,hbd,hbe,hbdbe,D,E,hD,hE,hDb,hEb,?_⟩
    rcases hcases with hinsideD | hinsideE | houtside
    · exact False.elim (b.property
        (actual_old_proper_arc_contained_in_boundary_parallel_disk_is_parallel
          b.val d bd hbd (fun t => (hbdbe t).1) D hD hDb hinsideD))
    · exact False.elim (b.property
        (actual_old_proper_arc_contained_in_boundary_parallel_disk_is_parallel
          b.val e be hbe (fun t => (hbdbe t).2) E hE hEb hinsideE))
    · exact houtside
  have terminal_two_branches_shared_tail (b : ProperArc S x R) (u v : Interval)
      (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
      (hcross : b.val u = a0.val.val v)
      (htail : ∀ s t : Interval, v ≤ t → b.val s = a0.val.val t → s = u ∧ t = v) :
      ∃ d e : ProperArc S x R,
        (Set.range d.val =
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) ∧
        (Set.range e.val =
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) ∧
        Set.range d.val ∩ Set.range e.val =
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1) := by
    obtain ⟨d,e,hd0,he0,hd1,he1,hdimage,heimage⟩ :=
      terminal_two_branches_exact b u v hu0 hu1 hv0 hv1 hcross htail
    refine ⟨d,e,hdimage,heimage,?_⟩
    ext y
    rw [Set.mem_inter_iff,hdimage,heimage]
    constructor
    · rintro ⟨hd,he⟩
      rcases hd with hd | hd
      · rcases he with he | he
        · obtain ⟨s,hs⟩ := hd
          obtain ⟨t,ht⟩ := he
          have heq := b.property.1.injective (hs.trans ht.symm)
          have hlow := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu0.le s).2
          have hhigh := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu1.le t).1
          have hcut : CurveComplex.BranchedDoubleCover.intervalAffine 0 u s = u :=
            le_antisymm hlow (heq ▸ hhigh)
          refine ⟨0,?_⟩
          change a0.val.val (CurveComplex.BranchedDoubleCover.intervalAffine v 1 0) = y
          have hzero : CurveComplex.BranchedDoubleCover.intervalAffine v 1 0 = v := by
            apply Subtype.ext
            change (1-(0:ℝ))*(v:ℝ)+0*1=(v:ℝ)
            ring
          rw [hzero,← hcross]
          exact (congrArg b.val hcut).symm.trans hs
        · exact he
      · exact hd
    · intro hy
      exact ⟨Or.inr hy,Or.inr hy⟩
  have actual_terminal_two_branch_images_intersect_exactly_in_actual_shared_tail
      (b : ProperArc S x R) (d e : ProperArc S x R) (u v : Interval)
      (hu0 : 0<u) (hu1 : u<1)
      (hcross : b.val u=a0.val.val v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) :
      Set.range d.val ∩ Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1) := by
    ext y
    rw [Set.mem_inter_iff,hdimage,heimage]
    constructor
    · rintro ⟨hd,he⟩
      rcases hd with hd | hd
      · rcases he with he | he
        · obtain ⟨s,hs⟩ := hd
          obtain ⟨t,ht⟩ := he
          have heq := b.property.1.injective (hs.trans ht.symm)
          have hlow := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu0.le s).2
          have hhigh := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu1.le t).1
          have hcut : CurveComplex.BranchedDoubleCover.intervalAffine 0 u s = u :=
            le_antisymm hlow (heq ▸ hhigh)
          refine ⟨0,?_⟩
          change a0.val.val (CurveComplex.BranchedDoubleCover.intervalAffine v 1 0) = y
          have hzero : CurveComplex.BranchedDoubleCover.intervalAffine v 1 0 = v := by
            apply Subtype.ext
            change (1-(0:ℝ))*(v:ℝ)+0*1=(v:ℝ)
            ring
          rw [hzero,← hcross]
          exact (congrArg b.val hcut).symm.trans hs
        · exact he
      · exact hd
    · intro hy
      exact ⟨Or.inr hy,Or.inr hy⟩
  have actual_essential_old_arc_two_parallel_disks_have_actual_shared_tail_intersection
      (b : EssentialProperArc S x R) (d e : ProperArc S x R) (u v : Interval)
      (hu0 : 0<u) (hu1 : u<1) (hv1 : v<1)
      (hcross : b.val.val u=a0.val.val v)
      (htail : ∀ s t : Interval,v≤t → b.val.val s=a0.val.val t → s=u ∧ t=v)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (hdparallel : boundaryParallel S x R d) (heparallel : boundaryParallel S x R e) :
      ∃ bd be : C(Interval,Q S x R), Topology.IsEmbedding bd ∧ Topology.IsEmbedding be ∧
        (∀ t,bd t∈boundaryQ S x R ∧ be t∈boundaryQ S x R) ∧
      ∃ D E : C(Metric.closedBall (0 : Plane) 1,Q S x R),
        Topology.IsEmbedding D ∧ Topology.IsEmbedding E ∧
        D '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range d.val ∪ Set.range bd ∧
        E '' {z | z.val∈Metric.sphere (0 : Plane) 1}=Set.range e.val ∪ Set.range be ∧
        Disjoint (E '' {z | z.val∈Metric.ball (0 : Plane) 1}) (Set.range D) ∧
        Disjoint (D '' {z | z.val∈Metric.ball (0 : Plane) 1}) (Set.range E) ∧
        Set.range D ∩ Set.range E=
          Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1) := by
    obtain ⟨bd,be,hbd,hbe,hbdbe,D,E,hD,hE,hDb,hEb,hED,hDE⟩ :=
      actual_essential_old_arc_two_parallel_disks_force_exterior_clearance
        b d e u v hu0 hu1 hv1 hcross htail hdimage heimage hdparallel heparallel
    refine ⟨bd,be,hbd,hbe,hbdbe,D,E,hD,hE,hDb,hEb,hED,hDE,?_⟩
    exact (actual_exterior_parallel_disks_intersection_is_old_arcs_intersection
      d e bd be hbd hbe (fun t => (hbdbe t).1) (fun t => (hbdbe t).2)
      D E hD hE hDb hEb hED hDE).trans
        (actual_terminal_two_branch_images_intersect_exactly_in_actual_shared_tail
          b.val d e u v hu0 hu1 hcross hdimage heimage)
  have actual_original_essential_terminal_surgery_branches_cannot_both_be_parallel
      (b : EssentialProperArc S x R) (d e : ProperArc S x R) (u v : Interval)
      (hu0 : 0<u) (hu1 : u<1) (hv0 : 0<v) (hv1 : v<1)
      (hcross : b.val.val u=a0.val.val v)
      (htail : ∀ s t : Interval,v≤t → b.val.val s=a0.val.val t → s=u ∧ t=v)
      (hd0 : d.val 0=b.val.val 0) (he0 : e.val 0=b.val.val 1)
      (hd1 : d.val 1=a0.val.val 1) (he1 : e.val 1=a0.val.val 1)
      (hdimage : Set.range d.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) 0 u) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1))
      (heimage : Set.range e.val=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) u 1) ∪
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1)) :
      ¬boundaryParallel S x R d ∨ ¬boundaryParallel S x R e := by
    by_contra hn
    obtain ⟨hdparallel,heparallel⟩ := not_or.mp hn
    have hdpar : boundaryParallel S x R d := not_not.mp hdparallel
    have hepar : boundaryParallel S x R e := not_not.mp heparallel
    obtain ⟨bd,be,hbd,hbe,hbdbe,D,E,hD,hE,hDb,hEb,hED,hDE,hmeet⟩ :=
      actual_essential_old_arc_two_parallel_disks_have_actual_shared_tail_intersection
        b d e u v hu0 hu1 hv1 hcross htail hdimage heimage hdpar hepar
    let pp := CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) 0 u
    let qp := CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) 1 u
    let tp := CurveComplex.BranchedDoubleCover.actualSubpath (properPath a0.val) v 1
    let P := pp.toContinuousMap
    let Qe := qp.toContinuousMap
    let T := tp.toContinuousMap
    have piece_embedding {z w : Q S x R} (p : Path z w) (hp : Function.Injective p)
        (l r : Interval) (hlr : l≠r) :
        Topology.IsEmbedding (CurveComplex.BranchedDoubleCover.actualSubpath p l r) := by
      have hi : Function.Injective (CurveComplex.BranchedDoubleCover.actualSubpath p l r) := by
        intro s t he
        have hc := congrArg Subtype.val (hp he)
        change (1-(s:ℝ))*(l:ℝ)+(s:ℝ)*(r:ℝ)=
          (1-(t:ℝ))*(l:ℝ)+(t:ℝ)*(r:ℝ) at hc
        have hneq : (r:ℝ)-(l:ℝ)≠0 := by
          intro he; exact hlr (Subtype.ext (sub_eq_zero.mp he).symm)
        have hm : ((r:ℝ)-(l:ℝ))*((s:ℝ)-(t:ℝ))=0 := by nlinarith only [hc]
        exact Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hneq))
      exact ((CurveComplex.BranchedDoubleCover.actualSubpath p l r).continuous.isClosedEmbedding hi).isEmbedding
    have hP : Topology.IsEmbedding P := piece_embedding (properPath b.val) b.val.property.1.injective 0 u hu0.ne
    have hQ : Topology.IsEmbedding Qe := piece_embedding (properPath b.val) b.val.property.1.injective 1 u hu1.ne.symm
    have hT : Topology.IsEmbedding T := piece_embedding (properPath a0.val) a0.val.property.1.injective v 1 hv1.ne
    have hQrange : Set.range Qe=
        Set.range (CurveComplex.BranchedDoubleCover.actualSubpath (properPath b.val) u 1) := by
      have hclock (t : Interval) : CurveComplex.BranchedDoubleCover.intervalAffine 1 u t=
          CurveComplex.BranchedDoubleCover.intervalAffine u 1 (unitInterval.symm t) := by
        apply Subtype.ext
        change (1-(t:ℝ))*1+(t:ℝ)*(u:ℝ)=(1-(1-(t:ℝ)))*(u:ℝ)+(1-(t:ℝ))*1
        ring
      ext y
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨unitInterval.symm t,congrArg b.val.val (hclock t).symm⟩
      · rintro ⟨t,rfl⟩
        refine ⟨unitInterval.symm t,?_⟩
        change b.val.val (CurveComplex.BranchedDoubleCover.intervalAffine 1 u (unitInterval.symm t))=
          b.val.val (CurveComplex.BranchedDoubleCover.intervalAffine u 1 t)
        rw [hclock,unitInterval.symm_involutive]
    have hdd : Set.range d.val=Set.range P ∪ Set.range T := hdimage
    have hee : Set.range e.val=Set.range Qe ∪ Set.range T := by rw [hQrange]; exact heimage
    have hbdold : Set.range b.val.val=Set.range P ∪ Set.range Qe := by
      apply Set.Subset.antisymm
      · rintro y ⟨s,rfl⟩
        by_cases hs : s≤u
        · left
          have hus : (0 : ℝ)<(u:ℝ) := hu0
          let t : Interval := ⟨(s:ℝ)/(u:ℝ),⟨div_nonneg s.property.1 hus.le,
            (div_le_one hus).mpr hs⟩⟩
          refine ⟨t,congrArg b.val.val (Subtype.ext ?_)⟩
          change (1-(s:ℝ)/(u:ℝ))*0+((s:ℝ)/(u:ℝ))*(u:ℝ)=(s:ℝ)
          field_simp [ne_of_gt hus]
          <;> ring
        · right
          have hu : 0<1-(u:ℝ) := by exact sub_pos.mpr hu1
          have hsU : (u:ℝ)≤(s:ℝ) := (le_of_not_ge hs)
          let t : Interval := ⟨(1-(s:ℝ))/(1-(u:ℝ)),⟨div_nonneg (sub_nonneg.mpr s.property.2) hu.le,
            (div_le_one hu).mpr (by linarith only [hsU])⟩⟩
          refine ⟨t,congrArg b.val.val (Subtype.ext ?_)⟩
          change (1-(1-(s:ℝ))/(1-(u:ℝ)))*1+((1-(s:ℝ))/(1-(u:ℝ)))*(u:ℝ)=(s:ℝ)
          field_simp [ne_of_gt hu]
          <;> ring
      · rintro y (⟨t,rfl⟩ | ⟨t,rfl⟩)
        · exact Set.mem_range_self _
        · exact Set.mem_range_self _
    have hPT : P 1=T 0 := pp.target'.trans (hcross.trans tp.source'.symm)
    have hQT : Qe 1=T 0 := qp.target'.trans (hcross.trans tp.source'.symm)
    have hPTm (s t : Interval) (he : P s=T t) : s=1 ∧ t=0 := by
      have hc := htail (CurveComplex.BranchedDoubleCover.intervalAffine 0 u s)
        (CurveComplex.BranchedDoubleCover.intervalAffine v 1 t)
        (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hv1.le t).1 he
      have h1 := congrArg Subtype.val hc.1
      have h2 := congrArg Subtype.val hc.2
      change (1-(s:ℝ))*0+(s:ℝ)*(u:ℝ)=(u:ℝ) at h1
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1=(v:ℝ) at h2
      exact ⟨Subtype.ext (by change (s:ℝ)=1; nlinarith only [h1,show (0:ℝ)<(u:ℝ) from hu0]),
        Subtype.ext (by change (t:ℝ)=0; nlinarith only [h2,show (v:ℝ)<1 from hv1])⟩
    have hQTm (s t : Interval) (he : Qe s=T t) : s=1 ∧ t=0 := by
      have hc := htail (CurveComplex.BranchedDoubleCover.intervalAffine 1 u s)
        (CurveComplex.BranchedDoubleCover.intervalAffine v 1 t)
        (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hv1.le t).1 he
      have h1 := congrArg Subtype.val hc.1
      have h2 := congrArg Subtype.val hc.2
      change (1-(s:ℝ))*1+(s:ℝ)*(u:ℝ)=(u:ℝ) at h1
      change (1-(t:ℝ))*(v:ℝ)+(t:ℝ)*1=(v:ℝ) at h2
      exact ⟨Subtype.ext (by change (s:ℝ)=1; nlinarith only [h1,show (u:ℝ)<1 from hu1]),
        Subtype.ext (by change (t:ℝ)=0; nlinarith only [h2,show (v:ℝ)<1 from hv1])⟩
    have hPbd (s : Interval) (he : P s∈boundaryQ S x R) : s=0 := by
      rcases actual_original_proper_arc_boundary_contact_parameters b.val
        (CurveComplex.BranchedDoubleCover.intervalAffine 0 u s) he with h0 | h1
      · have h := congrArg Subtype.val h0
        change (1-(s:ℝ))*0+(s:ℝ)*(u:ℝ)=0 at h
        apply Subtype.ext
        change (s:ℝ)=0
        nlinarith only [h,show (0:ℝ)<(u:ℝ) from hu0]
      · have hle := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hu0.le s).2
        rw [h1] at hle
        exact False.elim ((not_le_of_gt hu1) hle)
    have hQbd (s : Interval) (he : Qe s∈boundaryQ S x R) : s=0 := by
      rcases actual_original_proper_arc_boundary_contact_parameters b.val
        (CurveComplex.BranchedDoubleCover.intervalAffine 1 u s) he with h0 | h1
      · have hlow : u≤CurveComplex.BranchedDoubleCover.intervalAffine 1 u s := by
          change (u:ℝ)≤(1-(s:ℝ))*1+(s:ℝ)*(u:ℝ)
          nlinarith only [s.property.2,show (u:ℝ)<1 from hu1]
        rw [h0] at hlow
        exact False.elim ((not_le_of_gt hu0) hlow)
      · have h := congrArg Subtype.val h1
        change (1-(s:ℝ))*1+(s:ℝ)*(u:ℝ)=1 at h
        apply Subtype.ext
        change (s:ℝ)=0
        nlinarith only [h,show (u:ℝ)<1 from hu1]
    have hTbd (s : Interval) (he : T s∈boundaryQ S x R) : s=1 := by
      rcases actual_original_proper_arc_boundary_contact_parameters a0.val
        (CurveComplex.BranchedDoubleCover.intervalAffine v 1 s) he with h0 | h1
      · have hlow := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hv1.le s).1
        rw [h0] at hlow
        exact False.elim ((not_le_of_gt hv0) hlow)
      · have h := congrArg Subtype.val h1
        change (1-(s:ℝ))*(v:ℝ)+(s:ℝ)*1=1 at h
        apply Subtype.ext
        change (s:ℝ)=1
        nlinarith only [h,show (v:ℝ)<1 from hv1]
    exact b.property (actual_two_parallel_surgery_disks_with_actual_common_tail_cancel_old_arc
      b.val d e P Qe T bd be hP hQ hT (hd0.trans pp.source'.symm) (he0.trans qp.source'.symm)
      (hd1.trans tp.target'.symm) (he1.trans tp.target'.symm)
      hPT hQT hPTm hQTm hPbd hQbd hTbd hdd hee hbdold
      hbd hbe (fun t => (hbdbe t).1) (fun t => (hbdbe t).2)
      D E hD hE hDb hEb hmeet)
  exact actual_original_essential_terminal_surgery_branches_cannot_both_be_parallel b d e u v hu0 hu1 hv0 hv1 hcross htail hd0 he0 hd1 he1 hdimage heimage

#print axioms actual_original_essential_terminal_surgery_branches_cannot_both_be_parallel_isolated
end CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
