import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedSquareSupportedNormalShift
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Source movie and its actual common-strip coordinate produce selected finite
mesh centres and a single boundary-relative shift clearing every selected
centre. No selected points, cutoff or perturbation is assumed. -/
theorem actual_prepared_loop_mesh_center_perturbation
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (G : C(Interval × Interval,S))
    (T : Set (Interval × Interval)) (hT : IsOpen T)
    (hcontacts : G ⁻¹' a.val.image ⊆ T)
    (ψ : C(T,ℝ)) (hψ : ∀ x,ψ x<1)
    (hψzero : ∀ x : T,ψ x=0 ↔ G x.val ∈ a.val.image) :
    ∃ n : ℕ, ∃ hn : 0<n, ∃ label : (Fin n × Fin n) → Bool,
    ∃ point : {k : Fin n × Fin n // label k=true} → T,
      (∀ k,(point k).val=
        (ArcFinitePosition.intervalMeshParameter n hn k.val.1 ⟨1/2,by norm_num⟩,
         ArcFinitePosition.intervalMeshParameter n hn k.val.2 ⟨1/2,by norm_num⟩)) ∧
    ∃ support : Set (Interval × Interval),IsClosed support ∧ ∃ hST : support ⊆ T,
      G ⁻¹' a.val.image ⊆ interior support ∧
    ∃ (δ : ℝ) (weight : C(Interval × Interval,ℝ)),0<δ ∧
      (∀ z,weight z ∈ Icc (0:ℝ) 1) ∧
      (∀ z,z ∉ support → weight z=0) ∧
      (∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → weight z=0) ∧
      (∀ k,ψ (point k)+δ*weight (point k).val≠0) ∧
      (∀ z (hz : z ∈ support),ψ ⟨z,hST hz⟩+δ*weight z<1) := by
  classical
  obtain ⟨n,hn,cell,hcell,hcellClosed,hcellCover,label,hcellT,hcellOff,
    support,hsupport,hsupportClosed,hsupportT,hcontactsSupport,
    cutoff,hcutoffRange,hcutoffOutside,hcutoffContacts⟩ :=
    actual_prepared_loop_finite_core_support M a G T hT hcontacts
  let mid : Interval := ⟨1/2,by norm_num⟩
  let center (k : Fin n × Fin n) : Interval × Interval :=
    (ArcFinitePosition.intervalMeshParameter n hn k.1 mid,
      ArcFinitePosition.intervalMeshParameter n hn k.2 mid)
  have hcenter (k) : center k ∈ cell k := by
    rw [hcell k]
    exact mem_range_self (mid,mid)
  let point : {k : Fin n × Fin n // label k=true} → T :=
    fun k => ⟨center k.val,hcellT k.val k.property (hcenter k.val)⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hcoordinate (j : Fin n) :
      0<(ArcFinitePosition.intervalMeshParameter n hn j mid:ℝ) ∧
        (ArcFinitePosition.intervalMeshParameter n hn j mid:ℝ)<1 := by
    change 0<((j.val:ℝ)+1/2)/n ∧ ((j.val:ℝ)+1/2)/n<1
    have hj0 : (0:ℝ)≤j.val := Nat.cast_nonneg _
    have hj1 : (j.val:ℝ)+1≤n := by exact_mod_cast j.isLt
    constructor
    · exact div_pos (by linarith only [hj0]) hnR
    · apply (div_lt_one hnR).mpr
      linarith only [hj1]
  have hpoint : ∀ k,0<(point k).val.1.val ∧ (point k).val.1.val<1 ∧
      0<(point k).val.2.val ∧ (point k).val.2.val<1 := by
    intro k
    exact ⟨(hcoordinate k.val.1).1,(hcoordinate k.val.1).2,
      (hcoordinate k.val.2).1,(hcoordinate k.val.2).2⟩
  have hzero : ∀ k,ψ (point k)=0 → cutoff (point k).val=1 := by
    intro k hk
    exact hcutoffContacts _ ((hψzero (point k)).mp hk)
  obtain ⟨δ,weight,hδ,hweightEq,hweightRange,hboundary,hclear,hbound⟩ :=
    actual_prepared_square_supported_normal_shift T support hsupportClosed hsupportT
      ψ hψ cutoff hcutoffRange point hpoint hzero
  have hoff : ∀ z,z ∉ support → weight z=0 := by
    intro z hz
    rw [hweightEq z,hcutoffOutside z (fun hi => hz (interior_subset hi)),zero_mul]
  exact ⟨n,hn,label,point,(fun _ => rfl),support,hsupportClosed,hsupportT,
    hcontactsSupport,δ,weight,hδ,hweightRange,hoff,hboundary,hclear,hbound⟩
end CurveComplex.HyperellipticModel
