import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualOldFirstPorts
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualOldClosingPorts
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAttachedCapHeightBounds
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualAttachedCapExactImage
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualFirstReturnPortSourceOrder
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualClosingPortSourceOrder
set_option maxHeartbeats 3000000
namespace CurveComplex
open Set Topology Schoenflies
/-- Construct the ACTUAL two embedded OLD middle arcs of the whole translated
surgery boundary, retaining original source parameters, all four exact nonzero
ports and the ENTIRE closed curve decomposition with the two existing caps. -/
theorem source_framed_first_return_old_middle_decomposition
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (i : Bool)
    (F : SourceFirstReturnFramedStrips D B i) :
    ∃ r : ℝ, 0<r ∧ ∀ A : SourceFirstReturnAttachedCaps F,
      (∀ k, ‖A.v k‖<r) → ∃ uf ug : Bool → Interval,
        ((uf false:ℝ)<uf true ∧ (ug false:ℝ)<ug true) ∧
        (∀ k, 0<(uf k:ℝ) ∧ (uf k:ℝ)<1 ∧
        |(uf k:ℝ)-(F.θf k:ℝ)|<F.ηf k ∧
        D.first (uf k) ∈ (F.E k).source ∧
        F.E k (D.first (uf k))=Plane.mk 0 (F.E k (D.first (F.θf k)) 1-A.v k 1) ∧
        A.H.finalMap (D.first (uf k))=F.N (F.θf k,A.w)) ∧
        (∀ k, 0<(ug k:ℝ) ∧ (ug k:ℝ)<1 ∧
        |(ug k:ℝ)-(F.θg k:ℝ)|<F.ηg k ∧
        B.closing i (ug k) ∈ (F.E k).source ∧
        F.E k (B.closing i (ug k))=Plane.mk (F.E k (B.closing i (F.θg k)) 0-A.v k 0) 0 ∧
        A.H.finalMap (B.closing i (ug k))=F.M (F.θg k,A.z)) ∧
        ∃ f g : C(Interval,S), IsEmbedding f ∧ IsEmbedding g ∧
        f 0=F.N (F.θf false,A.w) ∧ f 1=F.N (F.θf true,A.w) ∧
        g 0=F.M (F.θg false,A.z) ∧ g 1=F.M (F.θg true,A.z) ∧
        Set.range f=A.H.finalMap '' (D.first '' Set.Icc (uf false) (uf true)) ∧
        Set.range g=A.H.finalMap '' (B.closing i '' Set.Icc (ug false) (ug true)) ∧
        A.d.image=Set.range f ∪ Set.range g ∪ Set.range (A.C false) ∪ Set.range (A.C true) ∧
        Disjoint (Set.range f) (Set.range g) := by
  have hOldFirstPorts := source_first_return_actual_old_first_ports S D B i
  have hOldClosingPorts := source_first_return_actual_old_closing_ports S D B i
  have hCapExact (F : SourceFirstReturnFramedStrips D B i)
      (A : SourceFirstReturnAttachedCaps F) := source_attached_cap_truncation_exact_image A
  have hFirstPrefixSource
      (F : SourceFirstReturnFramedStrips D B i) (k : Bool) (u : Interval)
      (hunear : |(u:ℝ)-(F.θf k:ℝ)|<F.ηf k) :
      ∀ t : Interval, (if k then u≤t else t≤u) → D.first t ∈ (F.E k).source := by
    intro t ht
    cases k
    · by_cases htheta : t≤F.θf false
      · exact ((source_first_return_first_ports_exact_source_order D B i F false t).mp htheta).1
      · have hnear : |(t:ℝ)-(F.θf false:ℝ)|<F.ηf false := by
          change (t:ℝ)≤(u:ℝ) at ht
          rw [abs_lt] at hunear ⊢
          have hb : (F.θf false:ℝ)<(t:ℝ) := lt_of_not_ge htheta
          constructor <;> linarith [(F.corner_positive false).2.2.1]
        have hh := F.first_framing false t ⟨0,by norm_num⟩ hnear
        rw [F.first_center] at hh
        exact hh.1
    · by_cases htheta : F.θf true≤t
      · exact ((source_first_return_first_ports_exact_source_order D B i F true t).mp htheta).1
      · have hnear : |(t:ℝ)-(F.θf true:ℝ)|<F.ηf true := by
          change (u:ℝ)≤(t:ℝ) at ht
          rw [abs_lt] at hunear ⊢
          have hb : (t:ℝ)<(F.θf true:ℝ) := lt_of_not_ge htheta
          constructor <;> linarith [(F.corner_positive true).2.2.1]
        have hh := F.first_framing true t ⟨0,by norm_num⟩ hnear
        rw [F.first_center] at hh
        exact hh.1
  have hClosingPrefixSource
      (F : SourceFirstReturnFramedStrips D B i) (k : Bool) (u : Interval)
      (hunear : |(u:ℝ)-(F.θg k:ℝ)|<F.ηg k) :
      ∀ t : Interval, (if k then u≤t else t≤u) → (B.closing i) t ∈ (F.E k).source := by
    intro t ht
    cases k
    · by_cases htheta : t≤F.θg false
      · exact ((source_first_return_closing_ports_exact_source_order D B i F false t).mp htheta).1
      · have hnear : |(t:ℝ)-(F.θg false:ℝ)|<F.ηg false := by
          change (t:ℝ)≤(u:ℝ) at ht
          rw [abs_lt] at hunear ⊢
          have hb : (F.θg false:ℝ)<(t:ℝ) := lt_of_not_ge htheta
          constructor <;> linarith [(F.corner_positive false).2.2.2]
        have hh := F.closing_framing false t ⟨0,by norm_num⟩ hnear
        rw [F.closing_center] at hh
        exact hh.1
    · by_cases htheta : F.θg true≤t
      · exact ((source_first_return_closing_ports_exact_source_order D B i F true t).mp htheta).1
      · have hnear : |(t:ℝ)-(F.θg true:ℝ)|<F.ηg true := by
          change (u:ℝ)≤(t:ℝ) at ht
          rw [abs_lt] at hunear ⊢
          have hb : (t:ℝ)<(F.θg true:ℝ) := lt_of_not_ge htheta
          constructor <;> linarith [(F.corner_positive true).2.2.2]
        have hh := F.closing_framing true t ⟨0,by norm_num⟩ hnear
        rw [F.closing_center] at hh
        exact hh.1
  have hFirstPrefixBounds
      (F : SourceFirstReturnFramedStrips D B i) (k : Bool) (u : Interval)
      (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1)
      (hunear : |(u:ℝ)-(F.θf k:ℝ)|<F.ηf k)
      (hpos : 0<F.E k (D.first u) 1) :
      ∀ t : Interval, (if k then u≤t else t≤u) →
        D.first t ∈ (F.E k).source ∧ F.E k (D.first t) 0=0 ∧
        0≤F.E k (D.first t) 1 ∧ F.E k (D.first t) 1≤F.E k (D.first u) 1 := by
    cases k
    · have hs (t : Interval) (ht : t≤u) := hFirstPrefixSource F false u hunear t ht
      have hz : F.E false (D.first 0)=0 := by rw [D.first_zero]; exact (F.point false).2
      have ha (t : Interval) (ht : t≤u) := (F.target_axis false _ (hs t ht)).mp
        (D.first_subset (Set.mem_range_self t))
      have hp := source_initial_axis_port_exact_image D.first D.first_embedded (F.E false) u hu0 hs hz ha hpos
      intro t ht
      have hx : D.first t ∈ D.first '' Set.Icc (0:Interval) u := ⟨t,⟨t.property.1,ht⟩,rfl⟩
      rw [hp.1] at hx
      exact hx
    · let rev : C(Interval,Interval) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
      let f : C(Interval,S) := D.first.comp rev
      let v : Interval := unitInterval.symmHomeomorph u
      have hfv : f v=D.first u := by
        change D.first (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph u))=D.first u
        congr 1
        apply Subtype.ext
        change 1-(1-(u:ℝ))=(u:ℝ)
        ring
      have hft (t : Interval) : f (unitInterval.symmHomeomorph t)=D.first t := by
        change D.first (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph t))=D.first t
        congr 1
        apply Subtype.ext
        change 1-(1-(t:ℝ))=(t:ℝ)
        ring
      have hs (t : Interval) (ht : t≤v) : f t ∈ (F.E true).source := by
        apply hFirstPrefixSource F true u hunear (unitInterval.symmHomeomorph t)
        change (u:ℝ)≤1-(t:ℝ)
        change (t:ℝ)≤1-(u:ℝ) at ht
        linarith
      have hf : IsEmbedding f := D.first_embedded.comp unitInterval.symmHomeomorph.isEmbedding
      have hz : F.E true (f 0)=0 := by
        simpa [f,rev,D.first_one] using (F.point true).2
      have ha (t : Interval) (ht : t≤v) : F.E true (f t) 0=0 := by
        apply (F.target_axis true _ (hs t ht)).mp
        exact D.first_subset (Set.mem_range_self (unitInterval.symmHomeomorph t))
      have hv : 0<(v:ℝ) := by change 0<1-(u:ℝ); linarith
      have hp := source_initial_axis_port_exact_image f hf (F.E true) v hv hs hz ha (by rw [hfv]; exact hpos)
      intro t ht
      have horder : unitInterval.symmHomeomorph t≤v := by
        change 1-(t:ℝ)≤1-(u:ℝ)
        change (u:ℝ)≤(t:ℝ) at ht
        linarith
      have hx : f (unitInterval.symmHomeomorph t) ∈ f '' Set.Icc (0:Interval) v :=
        ⟨unitInterval.symmHomeomorph t,⟨(unitInterval.symmHomeomorph t).property.1,horder⟩,rfl⟩
      rw [hp.1,hfv,hft] at hx
      exact hx
  have hInitialHorizontalExact
      (f : C(Interval,S)) (hf : IsEmbedding f)
      (E : OpenPartialHomeomorph S Plane) (u : Interval) (hu : 0<(u:ℝ))
      (hsource : ∀ t : Interval, t≤u → f t ∈ E.source)
      (hzero : E (f 0)=0)
      (haxis : ∀ t : Interval, t≤u → E (f t) 1=0)
      (hport : 0<E (f u) 0) :
      f '' Set.Icc (0:Interval) u =
        {x : S | x ∈ E.source ∧ E x 1=0 ∧ 0≤E x 0 ∧ E x 0≤E (f u) 0} := by
    let J : Plane ≃ₜ Plane := {
      toEquiv := {
        toFun := fun x=>Plane.mk (x 1) (x 0)
        invFun := fun x=>Plane.mk (x 1) (x 0)
        left_inv := by intro x; ext j; fin_cases j <;> rfl
        right_inv := by intro x; ext j; fin_cases j <;> rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let G : OpenPartialHomeomorph S Plane := E.trans J.toOpenPartialHomeomorph
    have hGs : G.source=E.source := by simp [G]
    have hs (t : Interval) (ht : t≤u) : f t ∈ G.source := hGs.symm ▸ hsource t ht
    have hz : G (f 0)=0 := by
      change J (E (f 0))=0
      rw [hzero]
      ext j
      fin_cases j <;> rfl
    have ha (t : Interval) (ht : t≤u) : G (f t) 0=0 := haxis t ht
    have hp := source_initial_axis_port_exact_image f hf G u hu hs hz ha hport
    apply hp.1.trans
    ext x
    rw [hGs]
    rfl
  have hClosingPrefixBounds
      (F : SourceFirstReturnFramedStrips D B i) (k : Bool) (u : Interval)
      (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1)
      (hunear : |(u:ℝ)-(F.θg k:ℝ)|<F.ηg k)
      (hpos : 0<F.E k ((B.closing i) u) 0) :
      ∀ t : Interval, (if k then u≤t else t≤u) →
        (B.closing i) t ∈ (F.E k).source ∧ F.E k ((B.closing i) t) 1=0 ∧
        0≤F.E k ((B.closing i) t) 0 ∧ F.E k ((B.closing i) t) 0≤F.E k ((B.closing i) u) 0 := by
    have hClosingInB (t : Interval) : (B.closing i) t ∈ b.image := by
      rw [← B.closing_cover]
      cases i
      · exact Or.inl (Set.mem_range_self t)
      · exact Or.inr (Set.mem_range_self t)
    cases k
    · have hs (t : Interval) (ht : t≤u) := hClosingPrefixSource F false u hunear t ht
      have hz : F.E false ((B.closing i) 0)=0 := by rw [B.closing_zero i]; exact (F.point false).2
      have ha (t : Interval) (ht : t≤u) := (F.current_axis false _ (hs t ht)).mp
        (hClosingInB t)
      have hp := hInitialHorizontalExact (B.closing i) (B.closing_embedded i) (F.E false) u hu0 hs hz ha hpos
      intro t ht
      have hx : (B.closing i) t ∈ (B.closing i) '' Set.Icc (0:Interval) u := ⟨t,⟨t.property.1,ht⟩,rfl⟩
      rw [hp] at hx
      exact hx
    · let rev : C(Interval,Interval) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
      let f : C(Interval,S) := (B.closing i).comp rev
      let v : Interval := unitInterval.symmHomeomorph u
      have hfv : f v=(B.closing i) u := by
        change (B.closing i) (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph u))=(B.closing i) u
        congr 1
        apply Subtype.ext
        change 1-(1-(u:ℝ))=(u:ℝ)
        ring
      have hft (t : Interval) : f (unitInterval.symmHomeomorph t)=(B.closing i) t := by
        change (B.closing i) (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph t))=(B.closing i) t
        congr 1
        apply Subtype.ext
        change 1-(1-(t:ℝ))=(t:ℝ)
        ring
      have hs (t : Interval) (ht : t≤v) : f t ∈ (F.E true).source := by
        apply hClosingPrefixSource F true u hunear (unitInterval.symmHomeomorph t)
        change (u:ℝ)≤1-(t:ℝ)
        change (t:ℝ)≤1-(u:ℝ) at ht
        linarith
      have hf : IsEmbedding f := (B.closing_embedded i).comp unitInterval.symmHomeomorph.isEmbedding
      have hz : F.E true (f 0)=0 := by
        simpa [f,rev,B.closing_one i] using (F.point true).2
      have ha (t : Interval) (ht : t≤v) : F.E true (f t) 1=0 := by
        apply (F.current_axis true _ (hs t ht)).mp
        exact hClosingInB (unitInterval.symmHomeomorph t)
      have hv : 0<(v:ℝ) := by change 0<1-(u:ℝ); linarith
      have hp := hInitialHorizontalExact f hf (F.E true) v hv hs hz ha (by rw [hfv]; exact hpos)
      intro t ht
      have horder : unitInterval.symmHomeomorph t≤v := by
        change 1-(t:ℝ)≤1-(u:ℝ)
        change (u:ℝ)≤(t:ℝ) at ht
        linarith
      have hx : f (unitInterval.symmHomeomorph t) ∈ f '' Set.Icc (0:Interval) v :=
        ⟨unitInterval.symmHomeomorph t,⟨(unitInterval.symmHomeomorph t).property.1,horder⟩,rfl⟩
      rw [hp,hfv,hft] at hx
      exact hx
  have hFirstPrefixToCap
      (F : SourceFirstReturnFramedStrips D B i) (A : SourceFirstReturnAttachedCaps F)
      (k : Bool) (u : Interval) (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1)
      (hunear : |(u:ℝ)-(F.θf k:ℝ)|<F.ηf k)
      (hucoord : F.E k (D.first u)=Plane.mk 0 (F.E k (D.first (F.θf k)) 1-A.v k 1)) :
      ∀ t : Interval, (if k then u≤t else t≤u) →
        A.H.finalMap (D.first t) ∈ Set.range (A.C k) := by
    have huE := hFirstPrefixSource F k u hunear u (by cases k <;> exact le_rfl)
    have hraw : D.first u ∈ (B.boundary i).image := by
      rw [B.boundary_image]
      exact Or.inl (Set.mem_range_self u)
    have hu0' : u≠0 := by intro he; have hh := congrArg Subtype.val he; change (u:ℝ)=0 at hh; linarith
    have hu1' : u≠1 := by intro he; have hh := congrArg Subtype.val he; change (u:ℝ)=1 at hh; linarith
    have hynonzero : F.E k (D.first u) 1≠0 := fun he=>
      D.first_interior_avoids u hu0' hu1' ((F.current_axis k _ huE).mpr he)
    have hynonnegative : 0≤F.E k (D.first u) 1 := by
      rcases (F.branch_trace k _ huE).mp hraw with hh|hh
      · exact hh.2
      · exact (hynonzero hh.2).elim
    have hpos : 0<F.E k (D.first u) 1 := lt_of_le_of_ne hynonnegative (Ne.symm hynonzero)
    obtain ⟨hportE,hportcoord⟩ := F.first_framing k (F.θf k) A.w
      (by simpa using (F.corner_positive k).2.2.1)
    have hportC : F.N (F.θf k,A.w) ∈ Set.range (A.C k) := by
      rw [← A.first_port k]
      exact Set.mem_range_self 0
    have hrawnorm : ‖F.E k (D.first u)‖<1/4 := by
      have hn := A.open_ball k _ hportC
      have he : F.E k (D.first u)=F.E k (F.N (F.θf k,A.w))-A.v k := by
        rw [hucoord,hportcoord,A.displacement k]
        ext j
        fin_cases j
        · change 0=F.α k*(A.w:ℝ)-F.α k*(A.w:ℝ); ring
        · rfl
      rw [he]
      exact hn
    intro t ht
    have hp := hFirstPrefixBounds F k u hu0 hu1 hunear hpos t ht
    have he_t : F.E k (D.first t)=Plane.mk 0 (F.E k (D.first t) 1) := by
      ext j
      fin_cases j
      · exact hp.2.1
      · rfl
    have he_u : F.E k (D.first u)=Plane.mk 0 (F.E k (D.first u) 1) := by
      ext j
      fin_cases j
      · exact (F.target_axis k _ huE).mp (D.first_subset (Set.mem_range_self u))
      · rfl
    have hnormle : ‖F.E k (D.first t)‖≤‖F.E k (D.first u)‖ := by
      rw [he_t,he_u]
      simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
      rw [Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,abs_of_nonneg hp.2.2.1,abs_of_pos hpos]
      exact hp.2.2.2
    have hcoords : F.E k (A.H.finalMap (D.first t))=F.E k (D.first t)+A.v k := by
      simpa only [AmbientIsotopy.finalMap,one_smul] using A.affine k ⟨1,by norm_num⟩ _ hp.1 (hnormle.trans hrawnorm.le)
    rw [hCapExact F A k]
    refine ⟨A.source_preserved k ⟨1,by norm_num⟩ _ hp.1,Or.inl ?_⟩
    rw [hcoords]
    have hold1 : F.E k (D.first u) 1=F.E k (D.first (F.θf k)) 1-A.v k 1 := by
      have hh := congrArg (fun q : Plane=>q 1) hucoord
      exact hh
    change F.E k (D.first t) 0+A.v k 0=A.v k 0 ∧
      A.v k 1≤F.E k (D.first t) 1+A.v k 1 ∧
      F.E k (D.first t) 1+A.v k 1≤F.E k (D.first (F.θf k)) 1
    constructor
    · linarith [hp.2.1]
    · constructor <;> linarith [hp.2.2.1,hp.2.2.2]
  have hClosingPrefixToCap
      (F : SourceFirstReturnFramedStrips D B i) (A : SourceFirstReturnAttachedCaps F)
      (k : Bool) (u : Interval) (hu0 : 0<(u:ℝ)) (hu1 : (u:ℝ)<1)
      (hunear : |(u:ℝ)-(F.θg k:ℝ)|<F.ηg k)
      (hucoord : F.E k (B.closing i u)=Plane.mk (F.E k (B.closing i (F.θg k)) 0-A.v k 0) 0) :
      ∀ t : Interval, (if k then u≤t else t≤u) →
        A.H.finalMap (B.closing i t) ∈ Set.range (A.C k) := by
    have huE := hClosingPrefixSource F k u hunear u (by cases k <;> exact le_rfl)
    have hraw : B.closing i u ∈ (B.boundary i).image := by
      rw [B.boundary_image]
      exact Or.inr (Set.mem_range_self u)
    have hunormal : F.E k (B.closing i u) 1=0 := by
      have hh := congrArg (fun q : Plane=>q 1) hucoord
      exact hh
    have hxnonzero : F.E k (B.closing i u) 0≠0 := by
      intro hxzero
      have hzero : F.E k (B.closing i u)=0 := by
        ext j
        fin_cases j
        · exact hxzero
        · exact hunormal
      have hp : B.closing i u=(if k then D.finish else D.start) :=
        (F.E k).injOn huE (F.point k).1 (hzero.trans (F.point k).2.symm)
      cases k
      · have hu : u=0 := (B.closing_embedded i).injective (hp.trans (B.closing_zero i).symm)
        subst u
        norm_num at hu0
      · have hu : u=1 := (B.closing_embedded i).injective (hp.trans (B.closing_one i).symm)
        subst u
        norm_num at hu1
    have hxnonnegative : 0≤F.E k (B.closing i u) 0 := by
      rcases (F.branch_trace k _ huE).mp hraw with hh|hh
      · exact (hxnonzero hh.1).elim
      · exact hh.1
    have hpos : 0<F.E k (B.closing i u) 0 := lt_of_le_of_ne hxnonnegative (Ne.symm hxnonzero)
    obtain ⟨hportE,hportcoord⟩ := F.closing_framing k (F.θg k) A.z
      (by simpa using (F.corner_positive k).2.2.2)
    have hportC : F.M (F.θg k,A.z) ∈ Set.range (A.C k) := by
      rw [← A.closing_port k]
      exact Set.mem_range_self 1
    have hrawnorm : ‖F.E k (B.closing i u)‖<1/4 := by
      have hn := A.open_ball k _ hportC
      have he : F.E k (B.closing i u)=F.E k (F.M (F.θg k,A.z))-A.v k := by
        rw [hucoord,hportcoord,A.displacement k]
        ext j
        fin_cases j
        · rfl
        · change 0=F.β k*(A.z:ℝ)-F.β k*(A.z:ℝ); ring
      rw [he]
      exact hn
    intro t ht
    have hp := hClosingPrefixBounds F k u hu0 hu1 hunear hpos t ht
    have he_t : F.E k (B.closing i t)=Plane.mk (F.E k (B.closing i t) 0) 0 := by
      ext j
      fin_cases j
      · rfl
      · exact hp.2.1
    have he_u : F.E k (B.closing i u)=Plane.mk (F.E k (B.closing i u) 0) 0 := by
      ext j
      fin_cases j
      · rfl
      · exact hunormal
    have hnormle : ‖F.E k (B.closing i t)‖≤‖F.E k (B.closing i u)‖ := by
      rw [he_t,he_u]
      simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
      rw [Real.sqrt_sq_eq_abs,Real.sqrt_sq_eq_abs,abs_of_nonneg hp.2.2.1,abs_of_pos hpos]
      exact hp.2.2.2
    have hcoords : F.E k (A.H.finalMap (B.closing i t))=F.E k (B.closing i t)+A.v k := by
      simpa only [AmbientIsotopy.finalMap,one_smul] using A.affine k ⟨1,by norm_num⟩ _ hp.1 (hnormle.trans hrawnorm.le)
    rw [hCapExact F A k]
    refine ⟨A.source_preserved k ⟨1,by norm_num⟩ _ hp.1,Or.inr ?_⟩
    rw [hcoords]
    have hold0 : F.E k (B.closing i u) 0=F.E k (B.closing i (F.θg k)) 0-A.v k 0 := by
      have hh := congrArg (fun q : Plane=>q 0) hucoord
      exact hh
    change A.v k 0≤F.E k (B.closing i t) 0+A.v k 0 ∧
      F.E k (B.closing i t) 0+A.v k 0≤F.E k (B.closing i (F.θg k)) 0 ∧
      F.E k (B.closing i t) 1+A.v k 1=A.v k 1
    constructor
    · linarith [hp.2.2.1]
    · constructor
      · linarith [hp.2.2.2]
      · linarith [hp.2.1]
  obtain ⟨rf,hrf,hfirst⟩ := hOldFirstPorts F
  obtain ⟨rg,hrg,hclosing⟩ := hOldClosingPorts F
  refine ⟨min rf rg,lt_min hrf hrg,?_⟩
  intro A hv
  obtain ⟨uf,huforder,huf⟩ := hfirst A (fun k=>(hv k).trans_le (min_le_left _ _))
  obtain ⟨ug,hugorder,hug⟩ := hclosing A (fun k=>(hv k).trans_le (min_le_right _ _))
  obtain ⟨qf,hqf,hqf0,hqf1,hqfrange,_hqfval⟩ := source_affine_subinterval (uf false) (uf true) huforder
  obtain ⟨qg,hqg,hqg0,hqg1,hqgrange,_hqgval⟩ := source_affine_subinterval (ug false) (ug true) hugorder
  obtain ⟨e,he⟩ := A.H.homeomorphism_at ⟨1,by norm_num⟩
  let f : C(Interval,S) := ⟨fun t=>e (D.first (qf t)),e.continuous.comp (D.first.continuous.comp qf.continuous)⟩
  let g : C(Interval,S) := ⟨fun t=>e (B.closing i (qg t)),e.continuous.comp ((B.closing i).continuous.comp qg.continuous)⟩
  have hf : IsEmbedding f := e.isEmbedding.comp (D.first_embedded.comp hqf)
  have hg : IsEmbedding g := e.isEmbedding.comp ((B.closing_embedded i).comp hqg)
  have hfe (t : Interval) : f t=A.H.finalMap (D.first (qf t)) := he _
  have hge (t : Interval) : g t=A.H.finalMap (B.closing i (qg t)) := he _
  have hf0 : f 0=F.N (F.θf false,A.w) := by rw [hfe,hqf0]; exact (huf false).2.2.2.2.2
  have hf1 : f 1=F.N (F.θf true,A.w) := by rw [hfe,hqf1]; exact (huf true).2.2.2.2.2
  have hg0 : g 0=F.M (F.θg false,A.z) := by rw [hge,hqg0]; exact (hug false).2.2.2.2.2
  have hg1 : g 1=F.M (F.θg true,A.z) := by rw [hge,hqg1]; exact (hug true).2.2.2.2.2
  have hfR : Set.range f=A.H.finalMap '' (D.first '' Set.Icc (uf false) (uf true)) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨D.first (qf t),⟨qf t,hqfrange ▸ Set.mem_range_self t,rfl⟩,(hfe t).symm⟩
    · rintro ⟨y,⟨u,hu,rfl⟩,hy⟩
      obtain ⟨t,ht⟩ := hqfrange.symm ▸ hu
      refine ⟨t,?_⟩
      rw [hfe,ht]
      exact hy
  have hgR : Set.range g=A.H.finalMap '' (B.closing i '' Set.Icc (ug false) (ug true)) := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨B.closing i (qg t),⟨qg t,hqgrange ▸ Set.mem_range_self t,rfl⟩,(hge t).symm⟩
    · rintro ⟨y,⟨u,hu,rfl⟩,hy⟩
      obtain ⟨t,ht⟩ := hqgrange.symm ▸ hu
      refine ⟨t,?_⟩
      rw [hge,ht]
      exact hy
  have hfirstcap (k : Bool) (t : Interval) (ht : if k then uf k≤t else t≤uf k) :
      A.H.finalMap (D.first t) ∈ Set.range (A.C k) :=
    hFirstPrefixToCap F A k (uf k) (huf k).1 (huf k).2.1 (huf k).2.2.1 (huf k).2.2.2.2.1 t ht
  have hclosingcap (k : Bool) (t : Interval) (ht : if k then ug k≤t else t≤ug k) :
      A.H.finalMap (B.closing i t) ∈ Set.range (A.C k) :=
    hClosingPrefixToCap F A k (ug k) (hug k).1 (hug k).2.1 (hug k).2.2.1 (hug k).2.2.2.2.1 t ht
  have hforward : A.d.image ⊆ Set.range f ∪ Set.range g ∪ Set.range (A.C false) ∪ Set.range (A.C true) := by
    intro x hx
    rw [A.image] at hx
    rcases hx with ⟨y,hy,rfl⟩
    rw [B.boundary_image] at hy
    rcases hy with ⟨t,rfl⟩|⟨t,rfl⟩
    · by_cases hleft : t≤uf false
      · have hh := hfirstcap false t hleft
        simp only [Set.mem_union]
        tauto
      · by_cases hright : uf true≤t
        · have hh := hfirstcap true t hright
          simp only [Set.mem_union]
          tauto
        · have hh : A.H.finalMap (D.first t) ∈ Set.range f := by
            rw [hfR]
            exact ⟨D.first t,⟨t,⟨(lt_of_not_ge hleft).le,(lt_of_not_ge hright).le⟩,rfl⟩,rfl⟩
          simp only [Set.mem_union]
          tauto
    · by_cases hleft : t≤ug false
      · have hh := hclosingcap false t hleft
        simp only [Set.mem_union]
        tauto
      · by_cases hright : ug true≤t
        · have hh := hclosingcap true t hright
          simp only [Set.mem_union]
          tauto
        · have hh : A.H.finalMap (B.closing i t) ∈ Set.range g := by
            rw [hgR]
            exact ⟨B.closing i t,⟨t,⟨(lt_of_not_ge hleft).le,(lt_of_not_ge hright).le⟩,rfl⟩,rfl⟩
          simp only [Set.mem_union]
          tauto
  have hFsub : Set.range f ⊆ A.d.image := by
    intro x hx
    rw [A.image]
    rw [hfR] at hx
    rcases hx with ⟨y,⟨u,_hu,rfl⟩,hy⟩
    exact ⟨D.first u,by rw [B.boundary_image]; exact Or.inl (Set.mem_range_self u),hy⟩
  have hGsub : Set.range g ⊆ A.d.image := by
    intro x hx
    rw [A.image]
    rw [hgR] at hx
    rcases hx with ⟨y,⟨u,_hu,rfl⟩,hy⟩
    exact ⟨B.closing i u,by rw [B.boundary_image]; exact Or.inr (Set.mem_range_self u),hy⟩
  have hwhole : A.d.image=Set.range f ∪ Set.range g ∪ Set.range (A.C false) ∪ Set.range (A.C true) :=
    Set.Subset.antisymm hforward (Set.union_subset (Set.union_subset (Set.union_subset hFsub hGsub)
      ((A.subset false).trans Set.inter_subset_right)) ((A.subset true).trans Set.inter_subset_right))
  have hHi : Function.Injective A.H.finalMap := by
    intro x y hh
    exact e.injective ((he x).trans (hh.trans (he y).symm))
  have hdis : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    intro x hxf hxg
    rw [hfR] at hxf
    rw [hgR] at hxg
    rcases hxf with ⟨y,⟨u,hu,rfl⟩,hy⟩
    rcases hxg with ⟨z,⟨v,_hv,rfl⟩,hz⟩
    have heq : D.first u=B.closing i v := hHi (hy.trans hz.symm)
    have hu0 : 0<(u:ℝ) := lt_of_lt_of_le (huf false).1 hu.1
    have hu1 : (u:ℝ)<1 := lt_of_le_of_lt hu.2 (huf true).2.1
    have hu0' : u≠0 := by intro hh; have he := congrArg Subtype.val hh; change (u:ℝ)=0 at he; linarith
    have hu1' : u≠1 := by intro hh; have he := congrArg Subtype.val hh; change (u:ℝ)=1 at he; linarith
    apply D.first_interior_avoids u hu0' hu1'
    rw [heq,← B.closing_cover]
    cases i
    · exact Or.inl (Set.mem_range_self v)
    · exact Or.inr (Set.mem_range_self v)
  exact ⟨uf,ug,⟨huforder,hugorder⟩,huf,hug,f,g,hf,hg,hf0,hf1,hg0,hg1,hfR,hgR,hwhole,hdis⟩
end CurveComplex
