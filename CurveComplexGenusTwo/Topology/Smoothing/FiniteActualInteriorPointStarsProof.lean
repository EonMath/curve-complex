import CurveComplexGenusTwo.Topology.Smoothing.ActualSurfaceInteriorPointStarProof
import CurveComplexGenusTwo.Topology.Smoothing.FiniteSupportedPatchAssemblyProof
open Set Metric Schoenflies CurveComplex CurveComplex.FiniteStarGeometry
theorem finite_actual_surface_interval_point_stars {S J : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [Fintype J]
    (η : J → I → S) (hη : ∀ j, Topology.IsClosedEmbedding (η j))
    (hdis : ∀ i j, i ≠ j → Disjoint (range (η i)) (range (η j)))
    (e : J → OpenPartialHomeomorph S Plane) (hsource : ∀ j t, η j t ∈ (e j).source)
    (τ : J → I) (hτ0 : ∀ j, 0 < (τ j).val) (hτ1 : ∀ j, (τ j).val < 1)
    (W : Set S) (hW : IsOpen W) (hpW : ∀ j, η j (τ j) ∈ W) :
    ∃ (V : J → Set S), (∀ j, IsOpen (V j)) ∧ (∀ j, V j ⊆ W) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
      ∃ (γ : J → Bool → I → Plane),
        (∀ j t, γ j false t=(e j) (η j ⟨(τ j).val*(1-t.val),by
          constructor <;> nlinarith [(τ j).property.1,(τ j).property.2,t.property.1,t.property.2]⟩)) ∧
        (∀ j t, γ j true t=(e j) (η j ⟨(τ j).val+(1-(τ j).val)*t.val,by
          constructor <;> nlinarith [(τ j).property.1,(τ j).property.2,t.property.1,t.property.2]⟩)) ∧
        ∃ (R : ∀ j, RadializedStar (γ j) ((e j) (η j (τ j))) ((e j) '' ((e j).source ∩ V j))),
          ∃ q : J → ℝ, (∀ j, 0 < q j ∧ (R j).vector true = -(q j) • (R j).vector false) ∧
          ∃ (P : J → AmbientIsotopy Plane) (H : AmbientIsotopy S),
            (∀ j, (P j).finalMap=(R j).H) ∧
            (∀ j t, H.map (t,η j (τ j))=η j (τ j)) ∧
            (∀ t x, x ∉ W → H.map (t,x)=x) ∧
            (∀ j t s, (e j) (H.map (t,η j s))=(P j).map (t,(e j) (η j s))) := by
  classical
  have hc (j : J) : IsCompact (range (η j)) := isCompact_range (hη j).continuous
  have hpairs (i j : J) : ∃ A B : Set S,
      IsOpen A ∧ IsOpen B ∧ range (η i) ⊆ A ∧ range (η j) ⊆ B ∧
        (i ≠ j → Disjoint A B) := by
    by_cases hij : i=j
    · exact ⟨univ,univ,isOpen_univ,isOpen_univ,subset_univ _,subset_univ _,fun h => (h hij).elim⟩
    · obtain ⟨A,B,hA,hB,hi,hj,hAB⟩ := normal_separation (hc i).isClosed (hc j).isClosed (hdis i j hij)
      exact ⟨A,B,hA,hB,hi,hj,fun _ => hAB⟩
  choose A B hA hB hi hj hAB using hpairs
  let N : J → Set S := fun i => ⋂ j, A i j ∩ B j i
  have hN (i : J) : IsOpen (N i) := isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i))
  have hrange (i : J) : range (η i) ⊆ N i := by
    intro x hx
    exact mem_iInter.mpr (fun j => ⟨hi i j hx,hj j i hx⟩)
  have hNN (i j : J) (hij : i ≠ j) : Disjoint (N i) (N j) := by
    apply (hAB i j hij).mono
    · intro x hx; exact ((mem_iInter.mp hx) j).1
    · intro x hx; exact ((mem_iInter.mp hx) i).2
  let V : J → Set S := fun j => N j ∩ W
  have hV (j : J) : IsOpen (V j) := (hN j).inter hW
  have hlocal (j : J) := actual_surface_interior_interval_point_star_normalization
    (e j) (η j) (hη j) (hsource j) (τ j) (hτ0 j) (hτ1 j)
    (V j) (hV j) ⟨hrange j (mem_range_self _),hpW j⟩
  choose γ hl hr R q hq hop P moves hP hcenter hfix hcoord using hlocal
  obtain ⟨H,houtside,hinside⟩ := finite_supported_patch_assembly N hNN moves
    (fun j t x hx => hfix j t x (fun hv => hx hv.1))
  have hsame (j : J) (t : I) (s : I) : H.map (t,η j s)=(moves j).map (t,η j s) :=
    hinside j t (η j s) (hrange j (mem_range_self _))
  refine ⟨V,hV,fun j x hx => hx.2,fun i j hij => (hNN i j hij).mono inter_subset_left inter_subset_left,
    γ,hl,hr,R,q,fun j => ⟨hq j,hop j⟩,P,H,hP,?_,?_,?_⟩
  · intro j t; rw [hsame]; exact hcenter j t
  · intro t x hx
    by_cases hn : x ∈ ⋃ j, N j
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hn
      rw [hinside j t x hj]
      exact hfix j t x (fun hv => hx hv.2)
    · exact houtside t x hn
  · intro j t s; rw [hsame]; exact hcoord j t s

#print axioms finite_actual_surface_interval_point_stars
