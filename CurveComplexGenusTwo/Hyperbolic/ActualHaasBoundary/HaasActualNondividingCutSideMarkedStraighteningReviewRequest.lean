import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusSurface
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalMarkedPrimitiveTorusStraightening
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
set_option maxHeartbeats 2000000
theorem actual_original_nondividing_cut_side_marked_primitive_straightening {E : Type} [TopologicalSpace E] [T2Space E]
    (U : Set E) (hU : IsOpen U) (houtside : Uᶜ.Nonempty)
    (e : U ≃ₜ {z : Circle×Circle // z ≠ (1,1)})
    (d : Curve E) (hdU : d.image ⊆ U) (hdconn : IsConnected d.imageᶜ) :
    ∃ dY : Curve (Circle×Circle),
      dY.image=(fun x : U => (e x).val) '' {x : U | x.val∈d.image} ∧
      Essential dY ∧ (1,1)∉dY.image ∧
      ∃ m n : ℤ,m.gcd n=1 ∧ ∃ a : Circle×Circle,∃ H : AmbientIsotopy (Circle×Circle),
        (∀ t,H.map (t,(1,1))=(1,1)) ∧
        H.finalMap '' dY.image=range (fun z : Circle => a*torusWindingMap m n z) := by
  obtain ⟨C,hC⟩ := actual_standard_torus_has_closed_surface_structure
  letI : ChartedSpace Plane (Circle×Circle) := C
  letI : ClosedSurface (Circle×Circle) := hC
  have hfilled : ∃ dY : Curve (Circle×Circle),
      dY.image=(fun x : U => (e x).val) '' {x : U | x.val∈d.image} ∧
      Essential dY ∧ (1,1)∉dY.image := by
    let Y := Circle×Circle
    let y : Y := (1,1)
    classical
    have hcollapse : ∃ f : C(E,Y), (∀ x : U, f x.val = (e x).val) ∧
        (∀ x : E, x ∉ U → f x = y) ∧ Function.Surjective f := by
      have hcollapse : ∃ f : C(E,OnePoint U),
          (∀ x : U,f x.val=(x : OnePoint U)) ∧
          ∀ x : E,x∉U → f x=OnePoint.infty := by
        classical
        let f : E → OnePoint U := fun x => if hx : x∈U then ((⟨x,hx⟩ : U) : OnePoint U) else OnePoint.infty
        have hcont : Continuous f := by
          rw [continuous_def]
          intro O hO
          by_cases hinf : (OnePoint.infty : OnePoint U)∈O
          · let K : Set U := (((↑) : U → OnePoint U) ⁻¹' O)ᶜ
            have hK : IsCompact K := ((OnePoint.isOpen_iff_of_mem hinf).mp hO).2
            have heq : f ⁻¹' O=(Subtype.val '' K)ᶜ := by
              ext x
              by_cases hx : x∈U
              · change f x∈O ↔ x∉Subtype.val '' K
                rw [show f x=((⟨x,hx⟩ : U) : OnePoint U) by simp [f,hx]]
                constructor
                · intro hf hmem
                  obtain ⟨u,hu,hux⟩ := hmem
                  have he : u=⟨x,hx⟩ := Subtype.ext hux
                  exact hu (he.symm ▸ hf)
                · intro hn
                  by_contra hf
                  exact hn ⟨⟨x,hx⟩,hf,rfl⟩
              · have hf : f x=OnePoint.infty := by simp [f,hx]
                simp only [mem_preimage,hf]
                constructor
                · intro _ hmem
                  obtain ⟨u,hu,hux⟩ := hmem
                  exact hx (hux ▸ u.property)
                · intro _
                  exact hinf
            rw [heq]
            exact (hK.image continuous_subtype_val).isClosed.isOpen_compl
          · let V : Set U := ((↑) : U → OnePoint U) ⁻¹' O
            have hV : IsOpen V := (OnePoint.isOpen_iff_of_notMem hinf).mp hO
            have heq : f ⁻¹' O=Subtype.val '' V := by
              ext x
              constructor
              · intro hxO
                have hx : x∈U := by
                  by_contra hx
                  apply hinf
                  simpa [f,hx] using hxO
                refine ⟨⟨x,hx⟩,?_,rfl⟩
                change ((⟨x,hx⟩ : U) : OnePoint U)∈O
                simpa [f,hx] using hxO
              · rintro ⟨x,hx,rfl⟩
                change f x.val∈O
                simpa [f,x.property,V] using hx
            rw [heq]
            exact hU.isOpenMap_subtype_val V hV
        refine ⟨⟨f,hcont⟩,?_,?_⟩
        · intro x
          simp [f,x.property]
        · intro x hx
          simp [f,hx]
      obtain ⟨q,hq,hout⟩ := hcollapse
      let j : U → Y := fun x => (e x).val
      have hj : IsEmbedding j := IsEmbedding.subtypeVal.comp e.isEmbedding
      have hr : range j = {y}ᶜ := by
        ext z
        constructor
        · rintro ⟨x,rfl⟩
          exact (e x).property
        · intro hz
          refine ⟨e.symm ⟨z,hz⟩,?_⟩
          exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
      let k := OnePoint.equivOfIsEmbeddingOfRangeEq y j hj hr
      refine ⟨(⟨k,k.continuous⟩ : C(OnePoint U,Y)).comp q,?_,?_,?_⟩
      · intro x
        change k (q x.val) = (e x).val
        rw [hq]
        rfl
      · intro x hx
        change k (q x) = y
        rw [hout x hx]
        rfl
      · intro z
        by_cases hz : z=y
        · subst z
          obtain ⟨x,hx⟩ := houtside
          refine ⟨x,?_⟩
          change k (q x)=y
          rw [hout x hx]
          rfl
        · refine ⟨(e.symm ⟨z,hz⟩).val,?_⟩
          change k (q (e.symm ⟨z,hz⟩).val)=z
          rw [hq]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
    obtain ⟨f,hin,hout,hsurj⟩ := hcollapse
    let dU : Circle → U := fun z => ⟨d.map z,hdU ⟨z,rfl⟩⟩
    have hdUemb : IsEmbedding dU := IsEmbedding.subtypeVal.of_comp_iff.mp d.embedded
    let dY : Curve Y := ⟨fun z => (e (dU z)).val,
      IsEmbedding.subtypeVal.comp (e.isEmbedding.comp hdUemb)⟩
    let D : Set U := {x | x.val∈d.image}
    have hD : Subtype.val '' D=d.image := by
      ext x
      constructor
      · rintro ⟨u,hu,rfl⟩;exact hu
      · intro hx;exact ⟨⟨x,hdU hx⟩,hx,rfl⟩
    have him : dY.image=(fun x : U => (e x).val) '' D := by
      ext z
      constructor
      · rintro ⟨w,rfl⟩;exact ⟨dU w,⟨w,rfl⟩,rfl⟩
      · rintro ⟨u,⟨w,hw⟩,rfl⟩
        refine ⟨w,?_⟩
        have he : dU w=u := Subtype.ext hw
        exact congrArg (fun x : U => (e x).val) he
    have hconn : IsConnected (Subtype.val '' D)ᶜ := hD.symm ▸ hdconn
    have hfilled : IsConnected ((fun x : U => (e x).val) '' D)ᶜ := by
      classical
      let j : U → Y := fun x => (e x).val
      have hpre : f ⁻¹' (j '' D)=Subtype.val '' D := by
        ext x
        constructor
        · rintro ⟨u,hu,he⟩
          have hx : x∈U := by
            by_contra hn
            have he' : (e u).val=y := he.trans (hout x hn)
            exact (e u).property he'
          have hsame : u=⟨x,hx⟩ := e.injective (Subtype.ext (he.trans (hin ⟨x,hx⟩)))
          exact ⟨u,hu,congrArg Subtype.val hsame⟩
        · rintro ⟨u,hu,rfl⟩
          exact ⟨u,hu,(hin u).symm⟩
      have himage : f '' (Subtype.val '' D)ᶜ=(j '' D)ᶜ := by
        ext z
        constructor
        · rintro ⟨x,hx,rfl⟩ hz
          exact hx (hpre ▸ hz)
        · intro hz
          obtain ⟨x,rfl⟩ := hsurj z
          refine ⟨x,?_,rfl⟩
          intro hx
          apply hz
          change x∈f ⁻¹' (j '' D)
          rw [hpre]
          exact hx
      rw [←himage]
      exact hconn.image f f.continuous.continuousOn
    have hdisc : ∀ (c : Curve Y),BoundsDisc c → ¬IsConnected c.imageᶜ := by
      intro c hc
      classical
      obtain ⟨f,hf,hboundary⟩ := hc
      let A := f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        x.val ∈ Metric.ball 0 1}
      let K := range f
      have hA : IsOpen A := LocalSurgery.embedded_surface_disk_interior_isOpen f hf
      have hi : interior K=A := LocalSurgery.embedded_surface_disk_interior_eq f hf
      have hK : IsClosed K := (isCompact_range f.continuous).isClosed
      have hd : Disjoint A Kᶜ := by
        apply disjoint_left.mpr
        rintro x ⟨u,hu,rfl⟩ hn
        exact hn ⟨u,rfl⟩
      have haNotBoundary : ∀ x∈A,x∉c.image := by
        rintro x ⟨u,hu,rfl⟩ hb
        rw [←hboundary] at hb
        obtain ⟨v,hv,he⟩ := hb
        have hvu : v=u := hf.injective he
        subst v
        have hu' : dist u.val 0 < 1 := hu
        have hv' : dist u.val 0 = 1 := hv
        linarith
      have hAne : A.Nonempty := by
        refine ⟨f ⟨0,by simp⟩,⟨⟨0,by simp⟩,by simp,rfl⟩⟩
      have hbne : Kᶜ.Nonempty := by
        by_contra hn
        have hfull : K=univ := by simpa using Set.not_nonempty_iff_eq_empty.mp hn
        have hp : c.map 1 ∈ c.image := ⟨1,rfl⟩
        rw [←hboundary] at hp
        obtain ⟨v,hv,hvp⟩ := hp
        have hvA : f v∈A := by rw [←hi,hfull];simp
        obtain ⟨u,hu,he⟩ := hvA
        have huv : u=v := hf.injective he
        subst u
        have hu' : dist v.val 0 < 1 := hu
        have hv' : dist v.val 0 = 1 := hv
        linarith
      have hcover : c.imageᶜ ⊆ A∪Kᶜ := by
        intro x hx
        by_cases hxK : x∈K
        · left
          obtain ⟨u,rfl⟩ := hxK
          refine ⟨u,?_,rfl⟩
          have hle : dist u.val 0 ≤ 1 := u.property
          have hne : dist u.val 0 ≠ 1 := by
            intro he
            apply hx
            rw [←hboundary]
            exact ⟨u,he,rfl⟩
          exact lt_of_le_of_ne hle hne
        · exact Or.inr hxK
      intro hconn
      have hleft : c.imageᶜ ⊆ A := hconn.isPreconnected.subset_left_of_subset_union
        hA hK.isOpen_compl hd hcover (by
          obtain ⟨x,hx⟩ := hAne
          exact ⟨x,haNotBoundary x hx,hx⟩)
      obtain ⟨x,hx⟩ := hbne
      have hxComp : x∈c.imageᶜ := by
        intro hb
        rw [←hboundary] at hb
        obtain ⟨u,hu,he⟩ := hb
        exact hx ⟨u,he⟩
      exact disjoint_left.mp hd (hleft hxComp) hx
    refine ⟨dY,him,?_,?_⟩
    · intro hbound
      exact hdisc dY hbound (him.symm ▸ hfilled)
    · rw [him]
      rintro ⟨u,hu,he⟩
      exact (e u).property he
  obtain ⟨dY,him,hess,havoid⟩ := hfilled
  refine ⟨dY,him,hess,havoid,?_⟩
  simpa using actual_original_marked_essential_torus_has_translated_primitive_straightening
    dY hess (0 : Plane) (by simpa using havoid)
