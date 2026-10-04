import CurveComplexGenusTwo.Dictionary.JordanDiscHelper
import CurveComplexGenusTwo.Dictionary.PuncturedCircleBounds
import CurveComplexGenusTwo.Intersection.SphereRegionTransport
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
open Set Topology Metric
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option linter.style.haveILetI false
set_option maxHeartbeats 2500000
theorem two_marked_rectangle_disc_cells : (by
 classical
 exact
   let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
     (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
   let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
   ∀ f : C(K,S), IsEmbedding f →
   (∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch) →
   (M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K})).card = 2 →
   ∃ lo hi : Fin 2 → ℝ × ℝ,
   ∃ F : Fin 2 → C(Metric.closedBall (0 : Schoenflies.Plane) 1,S),
   ∃ m : Fin 2 → Metric.closedBall (0 : Schoenflies.Plane) 1,
   (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
   (e '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2)) ∪
   (e '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2)) = K ∧
   ((∃ k : ℝ, lo = ![(-1,-1),(k,-1)] ∧ hi = ![(k,1),(1,1)] ∧ -1<k ∧ k<1) ∨
   (∃ k : ℝ, lo = ![(-1,-1),(-1,k)] ∧ hi = ![(1,k),(1,1)] ∧ -1<k ∧ k<1)) ∧
   (∀ i, IsEmbedding (F i) ∧ ‖(m i).val‖ < 1 ∧
    (∀ z, F i z ∈ M.cover.branch ↔ z=m i) ∧
    F i '' {z | ‖z.val‖=1} = f '' {z : K | z.val ∈ frontier
     (e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2))})) := by
  have hCells : (by
   classical
   exact
     let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
       (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
     let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
     ∀ f : C(K,S), IsEmbedding f →
     (∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch) →
     (M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K})).card = 2 →
     ∃ p lo hi : Fin 2 → ℝ × ℝ,
     (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
     (e '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2)) ∪
     (e '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2)) = K ∧
     ((∃ k : ℝ, lo = ![(-1,-1),(k,-1)] ∧ hi = ![(k,1),(1,1)] ∧ -1<k ∧ k<1) ∨
     (∃ k : ℝ, lo = ![(-1,-1),(-1,k)] ∧ hi = ![(1,k),(1,1)] ∧ -1<k ∧ k<1)) ∧
     (∀ i, ∃ hsub : (e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)) ⊆ K,
      ∃ fc : C(e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2),S),
      IsEmbedding fc ∧ (∀ z, fc z = f ⟨z.val,hsub z.property⟩) ∧
      ∃ m, m.val=e (p i) ∧ m.val ∈ interior (e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)) ∧
      (∀ z, fc z ∈ M.cover.branch ↔ z=m))) := by
    have hCoords (a b c d : ℝ) : (by
    classical
    exact
      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
      let K := e '' (Icc a b ×ˢ Icc c d)
      ∀ (f : C(K,S)), IsEmbedding f →
        (∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch) →
        (M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K})).card = 2 →
        ∃ s : Finset (ℝ × ℝ), s.card = 2 ∧
          (∀ z : K, f z ∈ M.cover.branch ↔ e.symm z.val ∈ s) ∧
          (∀ z ∈ s, a < z.1 ∧ z.1 < b ∧ c < z.2 ∧ z.2 < d)) := by
      have hparameters {X : Type} [TopologicalSpace X] (K : Set X) (hK : IsClosed K) (f : C(K,S)) (hf : IsEmbedding f)
        (hboundary : ∀ z : K, z.val ∈ frontier K → f z ∉ M.cover.branch)
        (hcard : (by classical exact
          (M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K})).card = 2)) :
        ∃ s : Finset K, s.card = 2 ∧ (∀ z, f z ∈ M.cover.branch ↔ z ∈ s) ∧
          (∀ z ∈ s, z.val ∈ interior K) := by
        classical
        have hInterior (z : K) (hz : f z ∈ M.cover.branch) : z.val ∈ interior K := by
          by_contra hnot
          apply hboundary z _ hz
          exact ⟨hK.closure_eq.symm ▸ z.property,hnot⟩
        let s := M.cover.branch.preimage f hf.injective.injOn
        have hrange : M.cover.branch.filter (fun b => b ∈ Set.range f) =
            M.cover.branch.filter (fun b => b ∈ f '' {z : K | z.val ∈ interior K}) := by
          apply Finset.ext
          intro b
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hb,z,rfl⟩
            exact ⟨hb,z,hInterior z hb,rfl⟩
          · rintro ⟨hb,z,hz,rfl⟩
            exact ⟨hb,z,rfl⟩
        refine ⟨s,?_,?_,?_⟩
        · rw [Finset.card_preimage,hrange]
          exact hcard
        · intro z
          simp [s]
        · intro z hz
          apply hInterior
          simpa [s] using hz
      classical
      dsimp only
      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
          (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
            (EuclideanSpace.equiv (Fin 2) ℝ).symm
      let K := e '' (Icc a b ×ˢ Icc c d)
      change ∀ (f : C(K,S)), _
      intro f hf hboundary hcard
      have hKcompact : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image e.continuous
      obtain ⟨t,htcard,htiff,htInterior⟩ := hparameters K hKcompact.isClosed f hf hboundary hcard
      let toPair : K → ℝ × ℝ := fun z => e.symm z.val
      have htoPairinj : Function.Injective toPair := by
        intro z w h
        exact Subtype.ext (e.symm.injective h)
      let s := t.image toPair
      refine ⟨s,?_,?_,?_⟩
      · rw [Finset.card_image_of_injective _ htoPairinj]
        exact htcard
      · intro z
        rw [htiff]
        constructor
        · intro hz
          exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
        · intro hz
          rcases Finset.mem_image.mp hz with ⟨w,hw,hwe⟩
          exact htoPairinj hwe ▸ hw
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨w,hw,rfl⟩
        have hwi := htInterior w hw
        change w.val ∈ interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d)) at hwi
        rw [← e.toHomeomorph.image_interior] at hwi
        rcases hwi with ⟨v,hv,hvw⟩
        have hvEq : v = toPair w := by
          apply e.injective
          change e v = e (e.symm w.val)
          rw [e.apply_symm_apply]
          exact hvw
        rw [hvEq,interior_prod_eq,interior_Icc,interior_Icc] at hv
        exact ⟨hv.1.1,hv.1.2,hv.2.1,hv.2.2⟩
    have hSort (a b c d : ℝ) (s : Finset (ℝ × ℝ)) (hs : s.card = 2)
      (hbounds : ∀ z ∈ s, a < z.1 ∧ z.1 < b ∧ c < z.2 ∧ z.2 < d) :
      ∃ p : Fin 2 → ℝ × ℝ, Set.range p = (s : Set (ℝ × ℝ)) ∧
        toLex (p 0) < toLex (p 1) ∧
        (∀ i, a < (p i).1 ∧ (p i).1 < b ∧ c < (p i).2 ∧ (p i).2 < d) := by
      classical
      let t := s.map toLex.toEmbedding
      have ht : t.card = 2 := by simpa [t] using hs
      let e := t.orderEmbOfFin ht
      let p : Fin 2 → ℝ × ℝ := fun i => ofLex (e i)
      have hrange : Set.range p = (s : Set (ℝ × ℝ)) := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          have hi := t.orderEmbOfFin_mem ht i
          rcases Finset.mem_map.mp hi with ⟨w, hw, he⟩
          have : w = p i := by
            simpa [p, e] using congrArg ofLex he
          simpa [← this] using hw
        · intro hz
          have htz : toLex z ∈ t := Finset.mem_map.mpr ⟨z, hz, rfl⟩
          have htrange := t.range_orderEmbOfFin ht
          change toLex z ∈ (t : Set (Lex (ℝ × ℝ))) at htz
          rw [← htrange] at htz
          rcases htz with ⟨i, hi⟩
          exact ⟨i, by simpa [p, e] using congrArg ofLex hi⟩
      refine ⟨p,hrange,?_,?_⟩
      · exact e.strictMono (by decide : (0 : Fin 2) < 1)
      · intro i
        apply hbounds
        have hpi : p i ∈ Set.range p := Set.mem_range_self i
        rw [hrange] at hpi
        exact hpi
    have hPartition (a b c d : ℝ) (p : Fin 2 → ℝ × ℝ)
     (h01 : toLex (p 0) < toLex (p 1))
     (hbound : ∀ i, a < (p i).1 ∧ (p i).1 < b ∧ c < (p i).2 ∧ (p i).2 < d) :
     ∃ lo hi : Fin 2 → ℝ × ℝ,
     (∀ i, (lo i).1 < (hi i).1 ∧ (lo i).2 < (hi i).2) ∧
     (∀ i j, p j ∈ Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2 ↔ i=j) ∧
     (∀ i, (lo i).1 < (p i).1 ∧ (p i).1 < (hi i).1 ∧ (lo i).2 < (p i).2 ∧ (p i).2 < (hi i).2) ∧
     (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2) ∪
     (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2) = Icc a b ×ˢ Icc c d ∧
     ((∃ k : ℝ, lo = ![(a,c),(k,c)] ∧ hi = ![(k,d),(b,d)] ∧ a<k ∧ k<b) ∨
     (∃ k : ℝ, lo = ![(a,c),(a,k)] ∧ hi = ![(b,k),(b,d)] ∧ c<k ∧ k<d)) := by
     have hb0 := hbound 0
     have hb1 := hbound 1
     rw [Prod.Lex.toLex_lt_toLex] at h01
     rcases h01 with hx | ⟨hx,hy⟩
     · let k := ((p 0).1+(p 1).1)/2
       have hk : (p 0).1 < k ∧ k < (p 1).1 := ⟨by dsimp [k]; linarith,by dsimp [k]; linarith⟩
       refine ⟨![(a,c),(k,c)],![(k,d),(b,d)],?_,?_,?_,?_,Or.inl ⟨k,rfl,rfl,by linarith,by linarith⟩⟩
       · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
       · intro i j; fin_cases i <;> fin_cases j <;> norm_num <;> simp only [Prod.le_def] <;> grind only
       · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
       · change (Icc a k ×ˢ Icc c d) ∪ (Icc k b ×ˢ Icc c d) = _
         rw [← union_prod,Icc_union_Icc_eq_Icc (by linarith : a≤k) (by linarith : k≤b)]
     · let k := ((p 0).2+(p 1).2)/2
       have hk : (p 0).2 < k ∧ k < (p 1).2 := ⟨by dsimp [k]; linarith,by dsimp [k]; linarith⟩
       refine ⟨![(a,c),(a,k)],![(b,k),(b,d)],?_,?_,?_,?_,Or.inr ⟨k,rfl,rfl,by linarith,by linarith⟩⟩
       · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
       · intro i j; fin_cases i <;> fin_cases j <;> norm_num <;> simp only [Prod.le_def] <;> grind only
       · intro i; fin_cases i <;> norm_num <;> and_intros <;> linarith
       · change (Icc a b ×ˢ Icc c k) ∪ (Icc a b ×ˢ Icc k d) = _
         rw [← prod_union,Icc_union_Icc_eq_Icc (by linarith : c≤k) (by linarith : k≤d)]
    have hRestrict {X : Type} [TopologicalSpace X] (K C : Set X) (hCK : C ⊆ K) (hCcompact : IsCompact C)
      (f : C(K,S)) (hf : IsEmbedding f) (p : Fin 2 → X) (i : Fin 2)
      (hmarks : ∀ z : K, f z ∈ M.cover.branch ↔ ∃ j, z.val = p j)
      (hincidence : ∀ j, p j ∈ C ↔ j = i) (hinside : p i ∈ interior C) :
      ∃ fc : C(C,S), IsEmbedding fc ∧
        (∀ x : C, fc x = f ⟨x.val,hCK x.property⟩) ∧
        ∃ m : C, m.val ∈ interior C ∧
          (∀ x : C, fc x ∈ M.cover.branch ↔ x = m) := by
      letI : T2Space S := M.sphere.symm.t2Space
      letI : CompactSpace C := isCompact_iff_compactSpace.mp hCcompact
      let inc : C → K := fun x => ⟨x.val,hCK x.property⟩
      have hinccont : Continuous inc := continuous_subtype_val.subtype_mk _
      let fc : C(C,S) := ⟨f ∘ inc,f.continuous.comp hinccont⟩
      have hfcinj : Function.Injective fc := hf.injective.comp (by
        intro x y h
        exact Subtype.ext (congrArg (fun z : K => z.val) h))
      let m : C := ⟨p i,(hincidence i).mpr rfl⟩
      refine ⟨fc,(fc.continuous.isClosedEmbedding hfcinj).isEmbedding,fun _ => rfl,m,hinside,?_⟩
      intro x
      change f (inc x) ∈ M.cover.branch ↔ x = m
      rw [hmarks]
      constructor
      · rintro ⟨j,hj⟩
        have hjC : p j ∈ C := hj ▸ x.property
        have hji := (hincidence j).mp hjC
        apply Subtype.ext
        simpa [inc,m,hji] using hj
      · intro hx
        refine ⟨i,?_⟩
        exact congrArg Subtype.val hx
    classical
    dsimp only
    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
    let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
    change ∀ f : C(K,S), _
    intro f hf hboundary hfcard
    obtain ⟨s,hscard,hsiff,hsinside⟩ := hCoords (-1) 1 (-1) 1 f hf hboundary hfcard
    obtain ⟨p,hprange,hp01,hpinside⟩ := hSort (-1) 1 (-1) 1 s hscard hsinside
    obtain ⟨lo,hi,hdims,hincidence,hpCell,hcover,hshape⟩ := hPartition (-1) 1 (-1) 1 p hp01 hpinside
    have hmarks : ∀ z : K, f z ∈ M.cover.branch ↔ ∃ j, z.val = e (p j) := by
      intro z
      rw [hsiff]
      change e.symm z.val ∈ (s : Set (ℝ × ℝ)) ↔ ∃ j, z.val = e (p j)
      rw [← hprange]
      constructor
      · rintro ⟨j,hj⟩
        refine ⟨j,?_⟩
        rw [hj,e.apply_symm_apply]
      · rintro ⟨j,hj⟩
        refine ⟨j,?_⟩
        rw [hj,e.symm_apply_apply]
    have hCellCover : (e '' (Icc (lo 0).1 (hi 0).1 ×ˢ Icc (lo 0).2 (hi 0).2)) ∪
        (e '' (Icc (lo 1).1 (hi 1).1 ×ˢ Icc (lo 1).2 (hi 1).2)) = K := by
      rw [← Set.image_union,hcover]
    refine ⟨p,lo,hi,hdims,hCellCover,hshape,?_⟩
    intro i
    let R := Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2
    let Cell := e '' R
    have hRsub : R ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
      rw [← hcover]
      fin_cases i
      · exact Set.subset_union_left
      · exact Set.subset_union_right
    have hsub : Cell ⊆ K := Set.image_mono hRsub
    have hcompact : IsCompact Cell := (isCompact_Icc.prod isCompact_Icc).image e.continuous
    have hCellIncidence : ∀ j, e (p j) ∈ Cell ↔ j = i := by
      intro j
      have hmem : e (p j) ∈ Cell ↔ p j ∈ R := by
        constructor
        · rintro ⟨v,hv,he⟩
          exact e.injective he ▸ hv
        · intro hj
          exact ⟨p j,hj,rfl⟩
      rw [hmem,hincidence]
      exact eq_comm
    have hCellInside : e (p i) ∈ interior Cell := by
      change e.toHomeomorph (p i) ∈ interior (e.toHomeomorph '' R)
      rw [← e.toHomeomorph.image_interior]
      refine ⟨p i,?_,rfl⟩
      change p i ∈ interior (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)
      rw [interior_prod_eq,interior_Icc,interior_Icc]
      exact ⟨⟨(hpCell i).1,(hpCell i).2.1⟩,⟨(hpCell i).2.2.1,(hpCell i).2.2.2⟩⟩
    obtain ⟨fc,hfc,hfcmap,m,hm,hmonly⟩ := hRestrict K Cell hsub hcompact f hf
      (fun j => e (p j)) i hmarks hCellIncidence hCellInside
    have hmval : m.val = e (p i) := by
      have hmbranch : fc m ∈ M.cover.branch := (hmonly m).mpr rfl
      rw [hfcmap] at hmbranch
      rcases (hmarks _).mp hmbranch with ⟨j,hj⟩
      have hji : j = i := (hCellIncidence j).mp (hj ▸ m.property)
      simpa [hji] using hj
    exact ⟨hsub,fc,hfc,hfcmap,m,hmval,hm,hmonly⟩
  have hAdapter (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
      let K := e '' (Icc a b ×ˢ Icc c d)
      ∀ (f : C(K,S)), IsEmbedding f →
      ∀ (m : K), m.val ∈ interior K → (∀ z, f z ∈ M.cover.branch ↔ z = m) →
      ∃ fd : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S),
        ∃ md : Metric.closedBall (0 : Schoenflies.Plane) 1,
          IsEmbedding fd ∧ ‖md.val‖ < 1 ∧ (∀ z, fd z ∈ M.cover.branch ↔ z = md) ∧
          fd '' {z | ‖z.val‖ = 1} = f '' {z : K | z.val ∈ frontier K} := by
    have hrect (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
      let K := e '' (Icc a b ×ˢ Icc c d)
      ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K,
        (∀ x, (h x : Schoenflies.Plane) ∈ interior K ↔ ‖x.val‖ < 1) ∧
        (∀ x, (h x : Schoenflies.Plane) ∈ frontier K ↔ ‖x.val‖ = 1) := by
      dsimp only
      let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
          (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
            (EuclideanSpace.equiv (Fin 2) ℝ).symm
      let K := e '' (Icc a b ×ˢ Icc c d)
      change ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K, _
      have hcompact : IsCompact K :=
        (isCompact_Icc.prod isCompact_Icc).image e.continuous
      have hconvex : Convex ℝ K :=
        ((convex_Icc a b).prod (convex_Icc c d)).linear_image e.toLinearEquiv.toLinearMap
      have hne : (interior K).Nonempty := by
        have hm : ((a + b) / 2, (c + d) / 2) ∈ interior (Icc a b ×ˢ Icc c d) := by
          rw [interior_prod_eq, interior_Icc, interior_Icc]
          exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        refine ⟨e ((a + b) / 2, (c + d) / 2), ?_⟩
        change e.toHomeomorph ((a + b) / 2, (c + d) / 2) ∈
          interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d))
        rw [← e.toHomeomorph.image_interior]
        exact mem_image_of_mem e hm
      obtain ⟨g, hgi, hgc, hgf⟩ :=
        exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hne hcompact.isBounded
      have hgK : g '' K = Metric.closedBall (0 : Schoenflies.Plane) 1 := by
        simpa [hcompact.isClosed.closure_eq] using hgc
      let h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K :=
        (Homeomorph.sets g (by
          ext x
          constructor
          · intro hx
            rw [← hgK]
            exact mem_image_of_mem g hx
          · intro hx
            rw [← hgK] at hx
            rcases hx with ⟨y, hy, hxy⟩
            exact g.injective hxy ▸ hy)).symm
      refine ⟨h, ?_, ?_⟩
      · intro x
        change g.symm x.val ∈ interior K ↔ ‖x.val‖ < 1
        rw [← mem_ball_zero_iff]
        constructor
        · intro hx
          rw [← hgi]
          exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
        · intro hx
          rw [← hgi] at hx
          rcases hx with ⟨y, hy, hyx⟩
          simpa [← hyx] using hy
      · intro x
        change g.symm x.val ∈ frontier K ↔ ‖x.val‖ = 1
        rw [← dist_zero_right x.val]
        change g.symm x.val ∈ frontier K ↔ x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1
        constructor
        · intro hx
          rw [← hgf]
          exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
        · intro hx
          rw [← hgf] at hx
          rcases hx with ⟨y, hy, hyx⟩
          simpa [← hyx] using hy
    dsimp only
    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
    let K := e '' (Icc a b ×ˢ Icc c d)
    change ∀ (f : C(K,S)), _
    intro f hf m hm honly
    obtain ⟨h,hi,hb⟩ := hrect a b c d hab hcd
    let fd : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
    let md := h.symm m
    have hmd : ‖md.val‖ < 1 := by
      apply (hi md).mp
      change ((h (h.symm m)) : Schoenflies.Plane) ∈ interior K
      rw [h.apply_symm_apply]
      exact hm
    have hmdonly : ∀ z, fd z ∈ M.cover.branch ↔ z = md := by
      intro z
      change f (h z) ∈ M.cover.branch ↔ z = h.symm m
      rw [honly]
      exact h.eq_symm_apply.symm
    refine ⟨fd,md,hf.comp h.isEmbedding,hmd,hmdonly,?_⟩
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨h z,(hb z).mpr hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨h.symm z,?_,?_⟩
      · apply (hb _).mp
        change ((h (h.symm z)) : Schoenflies.Plane) ∈ frontier K
        rw [h.apply_symm_apply]
        exact hz
      · change f (h (h.symm z)) = f z
        rw [h.apply_symm_apply]
  classical
  dsimp only
  let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let K := e '' (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
  change ∀ f : C(K,S), _
  intro f hf hboundary hcard
  obtain ⟨p,lo,hi,hdims,hcover,hshape,hCellFamily⟩ := hCells f hf hboundary hcard
  choose hsub fc hfc hfcmap mc hmcval hmcinside hmconly using hCellFamily
  have hAdapters (i : Fin 2) := hAdapter (lo i).1 (hi i).1 (lo i).2 (hi i).2
    (hdims i).1 (hdims i).2 (fc i) (hfc i) (mc i) (hmcinside i) (hmconly i)
  choose F m hF hm hFonly hFboundary using hAdapters
  refine ⟨lo,hi,F,m,hdims,hcover,hshape,?_⟩
  intro i
  refine ⟨hF i,hm i,hFonly i,?_⟩
  rw [hFboundary]
  let Cell := e '' (Icc (lo i).1 (hi i).1 ×ˢ Icc (lo i).2 (hi i).2)
  have hCellcompact : IsCompact Cell := (isCompact_Icc.prod isCompact_Icc).image e.continuous
  have hFrontSub : frontier Cell ⊆ Cell := by
    intro z hz
    exact hCellcompact.isClosed.closure_eq ▸ (frontier_subset_closure hz)
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨z.val,hsub i z.property⟩,hz,?_⟩
    exact (hfcmap i z).symm
  · rintro ⟨z,hz,rfl⟩
    let zc : Cell := ⟨z.val,hFrontSub hz⟩
    refine ⟨zc,hz,?_⟩
    rw [hfcmap]
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.two_marked_rectangle_disc_cells
