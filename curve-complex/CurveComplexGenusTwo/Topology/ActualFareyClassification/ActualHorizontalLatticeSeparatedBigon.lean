import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalGridFamilyEmptyBigon
import CurveComplexGenusTwo.Topology.ActualFareyClassification.FullLatticeBigonSeparation

open Set Topology Schoenflies CurveComplex

/-- Actual zero-drift source contacts produce full lattice open-disk separation,
using the constructed grid-free, whole-family-empty bigon. -/
theorem actual_horizontal_positive_count_has_lattice_separated_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite)
    (hcount : 0<{t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 1=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    : ∃ (k : ℤ) (r s : ℝ), r<s ∧ G r 1=c+(k:ℝ)*T ∧ G s 1=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ∧
      Pairwise (fun i j : ℤ×ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      (∀ (i : ℤ) (t : ℝ),Plane.mk t (c+(i:ℝ)*T) ∉
        inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) := by
  obtain ⟨k,r,s,hrs,hr,hs,hJ,he,hgrid⟩ :=
    actual_horizontal_positive_count_has_grid_family_empty_bigon G hG T c hT hp hc hfinite hcount htrans
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  have havoid (n : ℤ×ℤ) : Disjoint (inside C)
      ((fun z : Plane => z+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) '' C) := by
    apply disjoint_left.mpr
    rintro z hz ⟨w,hw,rfl⟩
    rcases hw with ⟨x,hx,rfl⟩ | hw
    · apply disjoint_left.mp he hz
      refine mem_iUnion.mpr ⟨n.2,x+(n.1:ℝ)*T,?_⟩
      change G (x+(n.1:ℝ)*T)+Plane.mk 0 ((n.2:ℝ)*T)=G x+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)
      rw [hp]
      ext q
      fin_cases q <;> simp [Plane.mk]
    · have hw1 : w 1=c+(k:ℝ)*T := by
        rw [segment_eq_image_lineMap] at hw
        obtain ⟨u,hu,rfl⟩ := hw
        simp only [AffineMap.lineMap_apply]
        change u*(G s 1-G r 1)+G r 1=c+(k:ℝ)*T
        rw [hr,hs]
        ring
      have hh : w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)=
          Plane.mk (w 0+(n.1:ℝ)*T) (c+((k+n.2:ℤ):ℝ)*T) := by
        ext q
        fin_cases q
        · rfl
        · change w 1+(n.2:ℝ)*T=c+((k+n.2:ℤ):ℝ)*T
          rw [hw1]
          push_cast
          ring
      change w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)∈inside C at hz
      rw [hh] at hz
      exact hgrid (k+n.2) _ hz
  have hvert := vertical_row_disjoint_of_boundary_avoidance C hJ T hT (fun j => by
    change Disjoint (inside C) ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) '' C)
    simpa only [Int.cast_zero,zero_mul] using havoid (0,j))
  exact ⟨k,r,s,hrs,hr,hs,hJ,he,
    full_lattice_separation_of_vertical_and_other_columns C hJ T hT hvert
      (fun n _ => havoid n),hgrid⟩

#print axioms actual_horizontal_positive_count_has_lattice_separated_bigon
