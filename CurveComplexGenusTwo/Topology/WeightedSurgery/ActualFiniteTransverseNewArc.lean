import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedPreparedNewArc
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedTrimmedCrosscutAssembly
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteTransverseCrosscutRedrawing

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Actual source arcs produce representatives with finitely many new interior
contacts against the entire old system. Endpoint collars, finite mesh, seam
repair, square supports and proper affine targets are all constructed. -/
theorem actual_finite_transverse_new_arc_contacts
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hclasses : ∀ i, ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (old i)))
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a)) :
    ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
      (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
      (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      ∀ i, (arcInterior M b ∩ (old' i).val.image).Finite ∧
        ∀ p ∈ arcInterior M b ∩ (old' i).val.image, ArcSurgery.CrossesInDisk M (old' i) b p := by
  obtain ⟨old',a1,δ,hδ,hδhalf,hclassesOld,hdisOld,hclassA,hclear,
    η,hη,hi,n,hn,e,label,hemarks,hlabel,hchart,hends⟩ :=
    actual_finite_prepared_new_arc M (actualSphereSmoothAtlas M) old hclasses hd a
      (actualRepresentative_nonloop M a ha)
  have hlu : δ < 1-δ := by linarith
  have hu : 1-δ < 1 := by linarith
  have hη' (t : Interval) : η t = a1.val.map
      ⟨δ+((1-δ)-δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by
    rw [hη]
    apply congrArg a1.val.map; apply Subtype.ext
    change δ+(1-2*δ)*(t:ℝ) = δ+((1-δ)-δ)*(t:ℝ)
    ring
  obtain ⟨α,β,F,hbounds,hFsub,hFdis,hFmarks,hFsq,hFends,hFflat,hFexact,hFoff,houtside⟩ :=
    actual_trimmed_marked_crosscut_assembly M old' a1 δ (1-δ) hδ hlu hu η hη'
      hi.injective n hn e hemarks hchart hends hclear
  have hcentral (k : Fin n) :
      (a1.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source := by
    intro x hx
    rw [← hFexact k] at hx
    exact hx.1.1
  obtain ⟨b,hbclass,hfinite⟩ := actual_finite_transverse_crosscut_redrawing M old' a1
    e F label α β hbounds hFsub hFdis hFmarks hFsq hcentral hFends hFflat hFexact
    hlabel hFoff houtside
  exact ⟨old',b,hclassesOld,hdisOld,hbclass.trans hclassA,hfinite⟩

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The constructed finite-transverse extension in the existing surgery API. -/
theorem actual_finite_transverse_arc_insertion
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hclasses : ∀ i, ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (old i)))
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a)) :
    ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
      (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
      (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      ∀ i, (ArcSurgery.crossings M (old' i) b).Finite ∧
        ∀ p ∈ ArcSurgery.crossings M (old' i) b, ArcSurgery.CrossesInDisk M (old' i) b p := by
  obtain ⟨old',b,hclassesOld,hdisOld,hclassB,hcontacts⟩ :=
    actual_finite_transverse_new_arc_contacts M old hclasses hd a ha
  refine ⟨old',b,hclassesOld,hdisOld,hclassB,?_⟩
  intro i
  have hsub : ArcSurgery.crossings M (old' i) b ⊆ arcInterior M b ∩ (old' i).val.image := by
    intro p hp
    exact ⟨hp.2,hp.1.1⟩
  exact ⟨(hcontacts i).1.subset hsub,fun p hp => (hcontacts i).2 p (hsub hp)⟩

end CurveComplex.HyperellipticModel
