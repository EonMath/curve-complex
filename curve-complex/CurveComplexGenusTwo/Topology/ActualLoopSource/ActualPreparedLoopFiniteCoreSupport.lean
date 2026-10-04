import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import Mathlib.Topology.UrysohnsLemma
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual loop movie's complete contact set produces a finite uniform
cell support in its existing common-strip domain and an actual cutoff. No
finite support, subdivision or cutoff certificate is an input. -/
theorem actual_prepared_loop_finite_core_support
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (G : C(Interval × Interval,S))
    (T : Set (Interval × Interval)) (hT : IsOpen T)
    (hcontacts : G ⁻¹' a.val.image ⊆ T) :
    ∃ n : ℕ, ∃ hn : 0<n,
    ∃ cell : (Fin n × Fin n) → Set (Interval × Interval),
      (∀ k,cell k=range (fun z : Interval × Interval =>
        (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2))) ∧
      (∀ k,IsClosed (cell k)) ∧ (∀ z,∃ k,z ∈ cell k) ∧
    ∃ label : (Fin n × Fin n) → Bool,
      (∀ k,label k=true → cell k ⊆ T) ∧
      (∀ k,label k=false → ∀ z ∈ cell k,G z ∉ a.val.image) ∧
    ∃ support : Set (Interval × Interval),
      support=(⋃ k,if label k=true then cell k else ∅) ∧
      IsClosed support ∧ support ⊆ T ∧ G ⁻¹' a.val.image ⊆ interior support ∧
    ∃ cutoff : C(Interval × Interval,ℝ),
      (∀ z,cutoff z ∈ Icc (0:ℝ) 1) ∧
      (∀ z,z ∉ interior support → cutoff z=0) ∧
      (∀ z,G z ∈ a.val.image → cutoff z=1) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let Z : Set (Interval × Interval) := G ⁻¹' a.val.image
  have hZ : IsClosed Z := (isCompact_range a.val.continuous).isClosed.preimage G.continuous
  let V : Bool → Set (Interval × Interval) := fun b => if b then T else Zᶜ
  have hV (b) : IsOpen (V b) := by cases b <;> simp [V,hT,hZ.isOpen_compl]
  have hcover : (univ : Set (Interval × Interval)) ⊆ ⋃ b,V b := by
    intro z _
    by_cases hz : z ∈ T
    · exact mem_iUnion.mpr ⟨true,hz⟩
    · exact mem_iUnion.mpr ⟨false,fun h => hz (hcontacts h)⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hcover
  obtain ⟨n,hn,hnδ⟩ := Real.exists_nat_pos_inv_lt hδ
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let anchor (k : Fin n × Fin n) : Interval × Interval :=
    (ArcFinitePosition.intervalMeshParameter n hn k.1 0,
      ArcFinitePosition.intervalMeshParameter n hn k.2 0)
  have hanchor (k) : ∃ b,Metric.ball (anchor k) δ ⊆ V b := hball _ (mem_univ _)
  choose label hlabel using hanchor
  let cell (k : Fin n × Fin n) : Set (Interval × Interval) :=
    range (fun z : Interval × Interval =>
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2))
  have hcell (k) : cell k ⊆ V (label k) := by
    rintro _ ⟨z,rfl⟩
    apply hlabel k
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    have hc (j : Fin n) (t : Interval) :
        dist (ArcFinitePosition.intervalMeshParameter n hn j t)
          (ArcFinitePosition.intervalMeshParameter n hn j 0)<δ := by
      rw [Subtype.dist_eq,Real.dist_eq]
      change |((j.val:ℝ)+(t:ℝ))/n-((j.val:ℝ)+0)/n|<δ
      have he : ((j.val:ℝ)+(t:ℝ))/n-((j.val:ℝ)+0)/n=(t:ℝ)/n := by ring
      rw [he,abs_of_nonneg (div_nonneg t.property.1 hnR.le)]
      exact (div_le_div_of_nonneg_right t.property.2 hnR.le).trans_lt (by simpa only [one_div] using hnδ)
    exact ⟨hc k.1 z.1,hc k.2 z.2⟩
  have hcellClosed (k) : IsClosed (cell k) :=
    (isCompact_range ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.1).comp continuous_fst |>.prodMk
      ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.2).comp continuous_snd))).isClosed
  have hcellCover (z : Interval × Interval) : ∃ k,z ∈ cell k := by
    obtain ⟨i,s,hs⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
    obtain ⟨j,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
    exact ⟨(i,j),(s,t),Prod.ext hs ht⟩
  have hcellT (k) (hk : label k=true) : cell k ⊆ T := by
    simpa [hk,V] using hcell k
  have hcellOff (k) (hk : label k=false) : cell k ⊆ Zᶜ := by
    simpa [hk,V] using hcell k
  let support : Set (Interval × Interval) := ⋃ k,if label k=true then cell k else ∅
  let off : Set (Interval × Interval) := ⋃ k,if label k=false then cell k else ∅
  have hsupportClosed : IsClosed support := by
    apply isClosed_iUnion_of_finite
    intro k
    split_ifs
    · exact hcellClosed k
    · exact isClosed_empty
  have hoffClosed : IsClosed off := by
    apply isClosed_iUnion_of_finite
    intro k
    split_ifs
    · exact hcellClosed k
    · exact isClosed_empty
  have hsupportT : support ⊆ T := by
    intro z hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    by_cases hb : label k=true
    · exact hcellT k hb (by simpa only [ite_eq_left hb] using hk)
    · simp only [ite_eq_right hb,mem_empty_iff_false] at hk
  have hZoff : Z ⊆ offᶜ := by
    intro z hz hoff
    obtain ⟨k,hk⟩ := mem_iUnion.mp hoff
    by_cases hb : label k=false
    · exact hcellOff k hb (by simpa only [ite_eq_left hb] using hk) hz
    · simp only [ite_eq_right hb,mem_empty_iff_false] at hk
  have hoffSupport : offᶜ ⊆ support := by
    intro z hz
    obtain ⟨k,hk⟩ := hcellCover z
    have hb : label k=true := by
      cases he : label k
      · exact False.elim (hz (mem_iUnion.mpr ⟨k,by simpa [he] using hk⟩))
      · rfl
    exact mem_iUnion.mpr ⟨k,by simpa only [ite_eq_left hb] using hk⟩
  have hZinterior : Z ⊆ interior support :=
    hZoff.trans (interior_maximal hoffSupport hoffClosed.isOpen_compl)
  have hsep : Disjoint (interior support)ᶜ Z :=
    Set.disjoint_left.mpr (fun z hz hcontact => hz (hZinterior hcontact))
  obtain ⟨cutoff,hcutoffOutside,hcutoffZeros,hcutoffRange⟩ :=
    exists_continuous_zero_one_of_isClosed isOpen_interior.isClosed_compl hZ hsep
  exact ⟨n,hn,cell,(fun _ => rfl),hcellClosed,hcellCover,label,hcellT,
    (fun k hk z hz => hcellOff k hk hz),support,rfl,hsupportClosed,hsupportT,hZinterior,
    cutoff,hcutoffRange,(fun z hz => hcutoffOutside hz),(fun z hz => hcutoffZeros hz)⟩
end CurveComplex.HyperellipticModel
