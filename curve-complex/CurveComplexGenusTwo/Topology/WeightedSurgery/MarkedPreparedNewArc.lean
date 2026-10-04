import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedBothEndpointClearance
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedInteriorSeamAssembly
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects

namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source-only preparation of the new actual arc: both exterior collars are
clear, every mesh endpoint is off the old system, and every entire closed mesh
piece remains inside its prepared marked-free old-axis chart. -/
theorem actual_finite_prepared_new_arc
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
    (hclasses : ∀ i, ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (old i)))
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (ha : a.val.map 0 ≠ a.val.map 1) :
    ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδhalf : δ < 1/2,
      (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
      (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      (∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 → (t:ℝ) ≤ δ ∨ 1-δ ≤ (t:ℝ) →
        ∀ i, b.val.map t ∉ (old' i).val.image) ∧
      ∃ η : C(Interval,S),
      (∀ t, η t = b.val.map ⟨δ+(1-2*δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
      Topology.IsClosedEmbedding η ∧ ∃ n : ℕ, ∃ hn : 0 < n,
      ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
        (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
        (∀ k j x, x ∈ (e k).source →
          (x ∈ (old' j).val.image ↔ label k = some j ∧ e k x 0 = 0)) ∧
        (∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source) ∧
        ∀ k j, η (intervalMeshParameter n hn k 0) ∉ (old' j).val.image ∧
          η (intervalMeshParameter n hn k 1) ∉ (old' j).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨old',a0,d,hdpos,hdhalf,hclassOld,hdisOld,hclassA,hA0,hA1,hclear⟩ :=
    actual_finite_system_both_endpoint_clearance M C old hd a ha
  have hneOld (i : ι) : (old' i).val.map 0 ≠ (old' i).val.map 1 :=
    actualRepresentative_nonloop M (old' i) (by rw [hclassOld i]; exact hclasses i)
  have hneA : a0.val.map 0 ≠ a0.val.map 1 := by rw [hA0,hA1]; exact ha
  let δ : ℝ := d/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ < 1/2 := by dsimp [δ]; linarith
  have hlu : δ < 1-δ := by linarith
  have hu : 1-δ < 1 := by linarith
  obtain ⟨η,hη,hi,n,hn,e,label,H,b,hemarks,hlabel,hclassB,hb,htails,hpiece,hseam⟩ :=
    actual_new_arc_internal_mesh_seam_repair M old' hneOld hdisOld a0 hneA
      δ (1-δ) hδ hlu hu
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  let ν : C(Interval,S) := ⟨g ∘ η,g.continuous.comp η.continuous⟩
  have hν (t : Interval) : ν t = H.finalMap (η t) := by change g (η t) = _; rw [hfinal]
  have hνliteral (t : Interval) :
      ν t = b.val.map ⟨δ+(1-2*δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by
    rw [hν,hη,← hb]
    apply congrArg b.val.map
    apply Subtype.ext
    change δ+((1-δ)-δ)*(t:ℝ) = δ+(1-2*δ)*(t:ℝ)
    ring
  have hνembed : Topology.IsClosedEmbedding ν := ν.continuous.isClosedEmbedding
    (g.injective.comp hi.injective)
  have hends := actual_interval_mesh_all_ends_off η H (fun i => (old' i).val.image) n hn
    (by
      intro i
      have ht : (⟨δ,⟨hδ.le,by linarith⟩⟩ : Interval).val ≤ δ := le_rfl
      have hh := hclear ⟨δ,⟨hδ.le,by linarith⟩⟩ hδ (by linarith) (Or.inl (by dsimp [δ]; linarith)) i
      have hη0 : η 0 = a0.val.map ⟨δ,⟨hδ.le,by linarith⟩⟩ := by simpa using hη 0
      rw [hη0,← hb,htails _ (Or.inl ht)]
      exact hh)
    (by
      intro i
      have ht : 1-δ ≤ (⟨1-δ,⟨by linarith,hu.le⟩⟩ : Interval).val := le_rfl
      have hh := hclear ⟨1-δ,⟨by linarith,hu.le⟩⟩ (by linarith) hu
        (Or.inr (by dsimp [δ]; linarith)) i
      have hη1 : η 1 = a0.val.map ⟨1-δ,⟨by linarith,hu.le⟩⟩ := by
        rw [hη]
        apply congrArg a0.val.map; apply Subtype.ext
        change δ+((1-δ)-δ)*1 = 1-δ
        ring
      rw [hη1,← hb,htails _ (Or.inr ht)]
      exact hh) hseam
  refine ⟨old',b,δ,hδ,hδhalf,hclassOld,hdisOld,hclassB.trans hclassA,?_,
    ν,hνliteral,hνembed,n,hn,e,label,hemarks,hlabel,?_,?_⟩
  · intro t ht0 ht1 hcol i
    rw [htails t hcol]
    apply hclear t ht0 ht1
    rcases hcol with hc | hc
    · exact Or.inl (hc.trans (by dsimp [δ]; linarith))
    · exact Or.inr (by dsimp [δ] at hc; linarith)
  · intro k t; rw [hν]; exact hpiece k t
  · intro k j
    simpa only [hν] using hends k j

end CurveComplex.HyperellipticModel
