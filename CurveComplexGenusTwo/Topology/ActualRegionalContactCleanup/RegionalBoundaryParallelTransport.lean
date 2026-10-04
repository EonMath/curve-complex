import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

theorem regional_boundary_parallel_disk_ambient_transport
    {S : Type} [TopologicalSpace S] (F B : Set S)
    (a b : C(Interval,↥F)) (H : AmbientIsotopy ↥F)
    (hB : (fun y => H.finalMap y) '' {y : ↥F | y.val ∈ B} =
      {y : ↥F | y.val ∈ B})
    (hmove : H.finalMap '' Set.range a = Set.range b)
    (hparallel :
      ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
        (∀ t, (v t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a ∪ Set.range v) :
      ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
        (∀ t, (v t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range b ∪ Set.range v := by
  obtain ⟨h,hh⟩ := H.homeomorphism_at 1
  have hfinal : ∀ y, h y = H.finalMap y := hh
  obtain ⟨v,hv,hvB,d,hd,hdimage⟩ := hparallel
  let v' : C(Interval,↥F) :=
    ⟨fun t => h (v t),h.continuous.comp v.continuous⟩
  let d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F) :=
    ⟨fun z => h (d z),h.continuous.comp d.continuous⟩
  have hv' : Topology.IsEmbedding v' := h.isEmbedding.comp hv
  have hd' : Topology.IsEmbedding d' := h.isEmbedding.comp hd
  refine ⟨v',hv',?_,d',hd',?_⟩
  · intro t
    have hvt : v t ∈ {y : ↥F | y.val ∈ B} := hvB t
    have hmap : H.finalMap (v t) ∈ {y : ↥F | y.val ∈ B} := by
      rw [← hB]
      exact ⟨v t,hvt,rfl⟩
    change (h (v t)).val ∈ B
    rw [hfinal]
    exact hmap
  · change (h ∘ d) ''
      {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range b ∪ Set.range v'
    have hA : h '' Set.range a = Set.range b := by
      simpa only [hfinal] using hmove
    have hV : h '' Set.range v = Set.range v' := by
      ext y
      simp only [Set.mem_image,Set.mem_range]
      constructor
      · rintro ⟨z,⟨t,rfl⟩,rfl⟩
        exact ⟨t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨v t,⟨t,rfl⟩,rfl⟩
    calc
      (h ∘ d) ''
          {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          h '' (d ''
            {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
            simpa only [Function.comp_def] using
              (Set.image_image h d
                {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}).symm
      _ = Set.range b ∪ Set.range v' := by rw [hdimage,Set.image_union,hA,hV]

theorem regional_boundary_parallel_disk_ambient_reflect
    {S : Type} [TopologicalSpace S] (F B : Set S)
    (a b : C(Interval,↥F)) (H : AmbientIsotopy ↥F)
    (hB : H.finalMap '' {y : ↥F | y.val ∈ B} =
      {y : ↥F | y.val ∈ B})
    (hmove : H.finalMap '' Set.range a = Set.range b)
    (hparallel :
      ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
        (∀ t, (v t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range b ∪ Set.range v) :
      ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
        (∀ t, (v t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a ∪ Set.range v := by
  obtain ⟨h,hh⟩ := H.homeomorphism_at 1
  have hfinal : ∀ y, h y = H.finalMap y := hh
  have hB' : (fun y => h.symm y) '' {y : ↥F | y.val ∈ B} =
      {y : ↥F | y.val ∈ B} := by
    have hBh : h '' {y : ↥F | y.val ∈ B} =
        {y : ↥F | y.val ∈ B} := by simpa only [hfinal] using hB
    calc
      h.symm '' {y : ↥F | y.val ∈ B} =
          h.symm '' (h '' {y : ↥F | y.val ∈ B}) := by rw [hBh]
      _ = {y : ↥F | y.val ∈ B} := by
        simp [Set.image_image]
  have hmove' : (fun y => h.symm y) '' Set.range b = Set.range a := by
    have he : h '' Set.range a = Set.range b := by
      simpa only [hfinal] using hmove
    rw [← he]
    simp [Set.image_image]
  obtain ⟨v,hv,hvB,d,hd,hdimage⟩ := hparallel
  let v' : C(Interval,↥F) :=
    ⟨fun t => h.symm (v t),h.symm.continuous.comp v.continuous⟩
  let d' : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F) :=
    ⟨fun z => h.symm (d z),h.symm.continuous.comp d.continuous⟩
  have hv' : Topology.IsEmbedding v' := h.symm.isEmbedding.comp hv
  have hd' : Topology.IsEmbedding d' := h.symm.isEmbedding.comp hd
  refine ⟨v',hv',?_,d',hd',?_⟩
  · intro t
    change (h.symm (v t)).val ∈ B
    have ht : h.symm (v t) ∈ {y : ↥F | y.val ∈ B} := by
      rw [← hB']
      exact ⟨v t,hvB t,rfl⟩
    exact ht
  · change (h.symm ∘ d) ''
      {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range a ∪ Set.range v'
    have hV : (fun y => h.symm y) '' Set.range v = Set.range v' := by
      ext y
      simp only [Set.mem_image,Set.mem_range]
      constructor
      · rintro ⟨z,⟨t,rfl⟩,rfl⟩
        exact ⟨t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨v t,⟨t,rfl⟩,rfl⟩
    calc
      (h.symm ∘ d) ''
          {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          h.symm '' (d ''
            {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
            simpa only [Function.comp_def] using
              (Set.image_image h.symm d
                {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}).symm
      _ = Set.range a ∪ Set.range v' := by
        rw [hdimage,Set.image_union,hmove',hV]

theorem regional_essential_arc_ambient_transport
    {S : Type} [TopologicalSpace S] (F B : Set S)
    (a b : C(Interval,↥F)) (H : AmbientIsotopy ↥F)
    (hB : H.finalMap '' {y : ↥F | y.val ∈ B} =
      {y : ↥F | y.val ∈ B})
    (hmove : H.finalMap '' Set.range a = Set.range b) :
    (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range a ∪ Set.range v) ↔
    (¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range b ∪ Set.range v) := by
  constructor
  · intro ha hb
    exact ha (regional_boundary_parallel_disk_ambient_reflect F B a b H hB hmove hb)
  · intro hb ha
    exact hb (regional_boundary_parallel_disk_ambient_transport F B a b H hB hmove ha)

#print axioms regional_boundary_parallel_disk_ambient_transport
#print axioms regional_boundary_parallel_disk_ambient_reflect
#print axioms regional_essential_arc_ambient_transport
