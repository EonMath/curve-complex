import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedTwoSideDisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_closed_piece_replacement_decreases_fixed_family_total
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hfinite : ∀ k, (ArcSurgery.crossings M (old k) a).Finite ∧
      ∀ p ∈ ArcSurgery.crossings M (old k) a, ArcSurgery.CrossesInDisk M (old k) a p)
      (H : CurveComplex.AmbientIsotopy S)
      (hm : ∀ t p, p ∈ M.cover.branch → H.map (t,p)=p)
      (C B R : Set S) (hC : IsCompact C) (hB : IsCompact B)
      (hOld : a.val.image=C ∪ R) (hNew : H.finalMap '' a.val.image=B ∪ R)
      (hBfree : ∀ k, Disjoint B (arcInterior M (old k)))
      (hRfree : ∀ k, Disjoint (R ∩ arcInterior M (old k)) C)
      (j : ι) (hremoved : (ArcSurgery.crossings M (old j) a ∩ C).Nonempty) :
      ∃ c : EssentialMarkedArc M,
        Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) a ∧
        (∀ k, (ArcSurgery.crossings M (old k) c).Finite ∧
          ∀ p ∈ ArcSurgery.crossings M (old k) c,
            ArcSurgery.CrossesInDisk M (old k) c p) ∧
        (∑ k, (ArcSurgery.crossings M (old k) c).ncard) <
          ∑ k, (ArcSurgery.crossings M (old k) a).ncard := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨g,hg⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
  have hgfix : ∀ p, p ∈ M.cover.branch → g p=p :=
    fun p hp => (hg p).trans (hm _ p hp)
  let c : EssentialMarkedArc M := a.transport g hgfix
  have hcimage : c.val.image=H.finalMap '' a.val.image := by
    change (a.val.transport g hgfix).image=_
    rw [MarkedArc.transport_image]
    exact congrArg (fun f : S → S => f '' a.val.image) (funext hg)
  have hclass : Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) a := by
    symm
    apply Quotient.sound
    exact ⟨H,hm,hcimage.symm⟩
  have hdecomp : c.val.image=B ∪ R := hcimage.trans hNew
  have hretain (k : ι) (p : S) (hp : p ∈ ArcSurgery.crossings M (old k) c) :
      p ∈ R ∧ p ∉ C ∪ B := by
    have hpR : p ∈ R := (hdecomp ▸ hp.2.1).resolve_left
      (fun hpB => disjoint_left.mp (hBfree k) hpB hp.1)
    refine ⟨hpR,?_⟩
    rintro (hpC | hpB)
    · exact disjoint_left.mp (hRfree k) ⟨hpR,hp.1⟩ hpC
    · exact disjoint_left.mp (hBfree k) hpB hp.1
  have hsub (k : ι) : ArcSurgery.crossings M (old k) c ⊆
      ArcSurgery.crossings M (old k) a := by
    intro p hp
    exact ⟨hp.1,⟨hOld.symm ▸ Or.inr (hretain k p hp).1,hp.2.2⟩⟩
  have htrans (k : ι) : ∀ p ∈ ArcSurgery.crossings M (old k) c,
      ArcSurgery.CrossesInDisk M (old k) c p := by
    intro p hp
    have hsource : ArcSurgery.CrossesInDisk M a (old k) p :=
      actual_marked_crossesInDisk_symm M (old k) a p ((hfinite k).2 p (hsub k hp))
    have hchanged : ArcSurgery.CrossesInDisk M c (old k) p :=
      actual_closed_replacement_retained_marked_crossing M a c (old k)
        C B R hC.isClosed hB.isClosed hOld hdecomp p hsource (hretain k p hp).2
    exact actual_marked_crossesInDisk_symm M c (old k) p hchanged
  refine ⟨c,hclass,fun k => ⟨(hfinite k).1.subset (hsub k),htrans k⟩,?_⟩
  apply Finset.sum_lt_sum
  · intro k _
    exact ncard_le_ncard (hsub k) (hfinite k).1
  · refine ⟨j,Finset.mem_univ j,?_⟩
    apply ncard_lt_ncard _ (hfinite j).1
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hsub j,?_⟩
    intro heq
    obtain ⟨p,hp,hpC⟩ := hremoved
    have hpnew : p ∈ ArcSurgery.crossings M (old j) c := heq.symm ▸ hp
    exact (hretain j p hpnew).2 (Or.inl hpC)

end CurveComplex.HyperellipticModel
