import CurveComplexGenusTwo.Topology.ActualFareyClassification.ShortArcUniformSupport
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalReturningParameters

open Set Topology Schoenflies CurveComplex

/-- The finite horizontal quotient event set generates ALL spatial full-family
horizontal-grid contacts under the full lattice orbit. Consequently every
actual compact support contains only finitely many contacts. -/
theorem actual_horizontal_full_family_grid_contacts_finite_in_compact
    (G : C(ℝ,Plane)) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite)
    (K : Set Plane) (hK : IsCompact K) :
    (((⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))∩
      {z : Plane | ∃ i : ℤ, z 1=c+(i:ℝ)*T})∩K).Finite := by
  let E := {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}
  let E0 : Set Plane := (fun t : Ico 0 (0+T) => G t.val) '' E
  have hE0 : E0.Finite := hfinite.image _
  let F := fun i : ℤ×ℤ => (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' E0
  have hlf : LocallyFinite F := CurveComplex.ActualFareyClassification.compact_lattice_translates_locally_finite E0 hE0.isCompact T hT
  have hOne (i : ℤ×ℤ) : (F i).Finite := hE0.image _
  have hAll : ((⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))∩
      {z : Plane | ∃ i : ℤ, z 1=c+(i:ℝ)*T})⊆⋃ i : ℤ×ℤ,F i := by
    rintro z ⟨hz,⟨i,hi⟩⟩
    obtain ⟨j,x,he⟩ := mem_iUnion.mp hz
    obtain ⟨k,t,ht,hxt⟩ := actual_parameter_has_fundamental_window T 0 x hT
    have hGx : G x=G t+Plane.mk ((k:ℝ)*T) 0 := by rw [hxt,hp]
    have hheight : G t 1=c+((i-j:ℤ):ℝ)*T := by
      have he1 := congrArg (fun z : Plane => z 1) he
      change G x 1+(j:ℝ)*T=z 1 at he1
      rw [hGx] at he1
      change G t 1+0+(j:ℝ)*T=z 1 at he1
      change z 1=c+(i:ℝ)*T at hi
      push_cast
      linarith
    refine mem_iUnion.mpr ⟨(k,j),G t,⟨⟨t,ht⟩,⟨i-j,hheight⟩,rfl⟩,?_⟩
    rw [← he]
    change G t+Plane.mk ((k:ℝ)*T) ((j:ℝ)*T)=G x+Plane.mk 0 ((j:ℝ)*T)
    rw [hGx]
    ext q
    fin_cases q <;> change _=_ <;> simp [Plane.mk]
  have hI : {i : ℤ×ℤ | (F i∩K).Nonempty}.Finite := hlf.finite_nonempty_inter_compact hK
  have hUnion := hI.biUnion (fun i _ => (hOne i).inter_of_left K)
  apply hUnion.subset
  rintro z ⟨hz,hzK⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hAll hz)
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨z,hi,hzK⟩,hi,hzK⟩⟩

/-- Actual compact-parameter horizontal fiber contacts are finite, although
one entire real horizontal-fiber event set is typically infinite. -/
theorem actual_horizontal_fiber_contacts_finite_on_compact_interval
    (G : C(ℝ,Plane)) (hinj : Function.Injective G) (T c a b : ℝ) (i : ℤ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite) :
    {x : ℝ | x∈Icc a b ∧ G x 1=c+(i:ℝ)*T}.Finite := by
  have hSpatial := actual_horizontal_full_family_grid_contacts_finite_in_compact
    G T c hT hp hfinite (G '' Icc a b) (isCompact_Icc.image G.continuous)
  apply (hSpatial.preimage hinj.injOn).subset
  intro x hx
  refine ⟨⟨?_,⟨i,hx.2⟩⟩,x,hx.1,rfl⟩
  refine mem_iUnion.mpr ⟨0,x,?_⟩
  ext q
  fin_cases q <;> simp [Plane.mk]

#print axioms actual_horizontal_full_family_grid_contacts_finite_in_compact
#print axioms actual_horizontal_fiber_contacts_finite_on_compact_interval
