import FiniteCyclicLayeredDiskLayout

open Set
open scoped BigOperators

namespace CurveComplex.FiniteArcDisk

theorem finite_label_descent_triangulated_disk
    {ι W : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq W]
    (A : AbstractSimplicialComplex ι) (K : AbstractSimplicialComplex W)
    (initial : ι → W) (word : CyclicAffineWord A K initial)
    (labels : ℕ → ι → W) (steps : ℕ) (anchor : W)
    (hzero : labels 0 = initial)
    (hfaces : ∀ t ≤ steps, ∀ σ : Finset ι, σ ∈ A.faces →
      σ.image (labels t) ∈ K.faces)
    (hcommon : ∀ t < steps, ∀ σ : Finset ι, σ ∈ A.faces →
      σ.image (labels t) ∪ σ.image (labels (t + 1)) ∈ K.faces)
    (hterminal : ∀ σ : Finset ι, σ ∈ A.faces →
      insert anchor (σ.image (labels steps)) ∈ K.faces) :
    Nonempty (LabelledDisk A K initial word
      (fun w => w = anchor ∨ ∃ t ≤ steps, ∃ i : ι, labels t i = w)) := by
  classical
  have timing :
      ∀ (n : ℕ) (p : Fin (n + 1) → RealizationPoint K)
        (e : (k : Fin n) → Path (p k.castSucc) (p k.succ)),
        ∃ τ : Fin (n + 2) → EdgeTime,
          StrictMono (fun k => (τ k : ℝ)) ∧
          τ 0 = 0 ∧ τ (Fin.last (n + 1)) = 1 ∧
          (∀ t : EdgeTime,
            (Path.concat p e) (Icc.convexComb (τ 0) (τ 1) t) = p 0) ∧
          ∀ (k : Fin n) (t : EdgeTime),
            (Path.concat p e)
              (Icc.convexComb (τ k.succ.castSucc) (τ k.succ.succ) t) = e k t := by
    let half : EdgeTime → EdgeTime := fun t =>
      ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
    have half_affine (a b t : EdgeTime) :
        Icc.convexComb (half a) (half b) t = half (Icc.convexComb a b t) := by
      apply Subtype.ext
      dsimp [half, Icc.convexComb]
      ring
    have first_half {a b c : RealizationPoint K} (f : Path a b) (g : Path b c) (t : EdgeTime) :
        (f.trans g) (half t) = f t := by
      rw [← Path.extend_extends' (f.trans g) (half t)]
      rw [Path.extend_trans_of_le_half _ _ (by dsimp [half]; linarith [t.property.2])]
      have he : (2 : ℝ) * (half t : ℝ) = (t : ℝ) := by dsimp [half]; ring
      rw [he, Path.extend_extends']
    have second_half {a b c : RealizationPoint K} (f : Path a b) (g : Path b c) (t : EdgeTime) :
        (f.trans g) (Icc.convexComb (half 1) 1 t) = g t := by
      rw [← Path.extend_extends' (f.trans g) (Icc.convexComb (half 1) 1 t)]
      rw [Path.extend_trans_of_half_le _ _ (by
        dsimp [half, Icc.convexComb]; norm_num; linarith [t.property.1])]
      have he : (2 : ℝ) * (Icc.convexComb (half 1) 1 t : ℝ) - 1 = (t : ℝ) := by
        dsimp [half, Icc.convexComb]
        norm_num
        ring
      rw [he, Path.extend_extends']
    intro n
    induction n with
    | zero =>
        intro p e
        refine ⟨fun k => if k = 0 then 0 else 1, ?_, by simp, by simp, ?_, ?_⟩
        · intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all
        · intro t
          simp
        · intro k
          exact Fin.elim0 k
    | succ n ih =>
        intro p e
        obtain ⟨τ, hmono, hz, ho, hc, he⟩ :=
          ih (p ∘ Fin.castSucc) (fun k => e k.castSucc)
        let τ' : Fin (n + 3) → EdgeTime := Fin.lastCases 1 (fun k => half (τ k))
        have hcast (k : Fin (n + 2)) : τ' k.castSucc = half (τ k) := by
          simp [τ']
        have hlast : τ' (Fin.last (n + 2)) = 1 := by simp [τ']
        refine ⟨τ', ?_, ?_, hlast, ?_, ?_⟩
        · apply Fin.strictMono_iff_lt_succ.mpr
          intro k
          refine Fin.lastCases ?_ (fun j => ?_) k
          · rw [hcast, show (Fin.last (n + 1)).succ = Fin.last (n + 2) from rfl,
              hlast, ho]
            norm_num [half]
          · simp only [← Fin.castSucc_succ, hcast]
            dsimp [half]
            exact div_lt_div_of_pos_right (hmono (Fin.castSucc_lt_succ (i := j))) (by norm_num)
        · rw [show (0 : Fin (n + 3)) = (0 : Fin (n + 2)).castSucc from rfl,
              hcast, hz]
          apply Subtype.ext
          dsimp [half]
          norm_num
        · intro t
          have hfirst0 : τ' 0 = half (τ 0) := hcast 0
          have hfirst1 : τ' 1 = half (τ 1) := hcast 1
          rw [hfirst0, hfirst1, half_affine, Path.concat_succ]
          exact (first_half (Path.concat (p ∘ Fin.castSucc) (fun k => e k.castSucc))
            (e (Fin.last n)) _).trans (hc t)
        · intro k t
          refine Fin.lastCases ?_ (fun j => ?_) k
          · simp only [Fin.succ_last, hcast, hlast, ho]
            rw [Path.concat_succ]
            exact second_half (Path.concat (p ∘ Fin.castSucc) (fun k => e k.castSucc))
              (e (Fin.last n)) t
          · simp only [← Fin.castSucc_succ, hcast]
            rw [half_affine, Path.concat_succ]
            exact (first_half (Path.concat (p ∘ Fin.castSucc) (fun k => e k.castSucc))
              (e (Fin.last n)) _).trans (he j t)
  have cover : ∀ (n : ℕ) (τ : Fin (n + 2) → EdgeTime)
      (t : EdgeTime), τ 0 ≤ t → t ≤ τ (Fin.last (n + 1)) →
      ∃ (k : Fin (n + 1)) (u : EdgeTime),
        t = Icc.convexComb (τ k.castSucc) (τ k.succ) u := by
    have segment (a b t : EdgeTime) (hat : a ≤ t) (htb : t ≤ b) :
        ∃ u : EdgeTime, t = Icc.convexComb a b u := by
      exact ⟨_, Icc.eq_convexComb hat htb⟩
    intro n
    induction n with
    | zero =>
        intro τ t hz ho
        obtain ⟨u, hu⟩ := segment (τ 0) (τ 1) t hz ho
        exact ⟨0, u, hu⟩
    | succ n ih =>
        intro τ t hz ho
        by_cases hmid : t ≤ τ (Fin.last (n + 1)).castSucc
        · obtain ⟨k, u, hu⟩ := ih (τ ∘ Fin.castSucc) t hz hmid
          refine ⟨k.castSucc, u, ?_⟩
          simpa only [Function.comp_apply, ← Fin.castSucc_succ] using hu
        · obtain ⟨u, hu⟩ := segment (τ (Fin.last (n + 1)).castSucc)
            (τ (Fin.last (n + 2))) t (le_of_not_ge hmid) ho
          exact ⟨Fin.last (n + 1), u, hu⟩
  obtain ⟨times, hmono, hzeroTime, honeTime, hconstant, hedge⟩ :=
    timing word.edgeCount word.point word.edge
  let phase : Fin (steps + 1) → ι → Option (Fin (steps + 1) × ι) :=
    fun t i => some (t, i)
  let phaseZero := phase 0
  let evaluate : Option (Fin (steps + 1) × ι) → W :=
    fun a => a.elim anchor (fun z => labels z.1.val z.2)
  have evaluate_zero (i : ι) : evaluate (phaseZero i) = initial i := by
    exact congrFun hzero i
  -- Exact missing geometric producer. This is K/W/label-independent.
  -- A future named helper needs Formalizer/F-Reviewer approval first.
  have geometry :
      ∃ (D : FiniteDiskModel)
        (address : Fin D.vertexCount → Option (Fin (steps + 1) × ι))
        (param : C(EdgeTime, RealizationPoint D.boundary))
        (blocks : Fin (word.edgeCount + 1) → Finset (Finset ↥D.boundaryVertices)),
        (∀ σ, σ ∈ D.complex.faces → ∃ τ : Finset ι, τ ∈ A.faces ∧
          ((∃ t : Fin (steps + 1), σ.image address ⊆ τ.image (phase t)) ∨
           (∃ t : Fin steps, σ.image address ⊆
             τ.image (phase t.castSucc) ∪ τ.image (phase t.succ)) ∨
           σ.image address ⊆ insert none (τ.image (phase (Fin.last steps))))) ∧
        Function.Surjective param ∧
        (∀ t u : EdgeTime, param t = param u ↔
          t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)) ∧
        (∀ (f : Option (Fin (steps + 1) × ι) → ℝ) (u : EdgeTime),
          (∑ v : Fin D.vertexCount, f (address v) *
            (D.boundaryInclusion (param
              (Icc.convexComb (times 0) (times 1) u))).weight v) =
            f (phaseZero (word.vertex 0))) ∧
        (∀ (f : Option (Fin (steps + 1) × ι) → ℝ)
            (k : Fin word.edgeCount) (u : EdgeTime),
          (∑ v : Fin D.vertexCount, f (address v) *
            (D.boundaryInclusion (param
              (Icc.convexComb (times k.succ.castSucc) (times k.succ.succ) u))).weight v) =
            (1 - (u : ℝ)) * f (phaseZero (word.vertex k.castSucc)) +
            (u : ℝ) * f (phaseZero (word.vertex k.succ))) ∧
        (∀ k σ, σ ∈ blocks k → σ ∈ D.boundary.faces) ∧
        (∀ σ, σ ∈ blocks 0 →
          σ.image (fun b => address b.val) ⊆ {phaseZero (word.vertex 0)}) ∧
        (∀ (k : Fin word.edgeCount) σ, σ ∈ blocks k.succ →
          σ.image (fun b => address b.val) ⊆
            {phaseZero (word.vertex k.castSucc), phaseZero (word.vertex k.succ)}) ∧
        (∀ k : Fin (word.edgeCount + 1),
          (⋃ σ ∈ blocks k, faceCarrier D.boundary σ) =
            Set.range (fun u : EdgeTime =>
              param (Icc.convexComb (times k.castSucc) (times k.succ) u))) ∧
        (∀ σ, σ ∈ D.boundary.faces →
          (σ.image (fun b => address b.val)) ⊆ {phaseZero (word.vertex 0)} ∨
          ∃ k : Fin word.edgeCount,
            (σ.image (fun b => address b.val)) ⊆
              {phaseZero (word.vertex k.castSucc), phaseZero (word.vertex k.succ)}) := by
    exact finite_cyclic_layered_disk_layout A word.edgeCount word.vertex
      word.vertex_closed word.edge_face steps times hmono hzeroTime honeTime
  obtain ⟨D, address, param, blocks, hshape, hsurj, hfibers, hbc, hbe,
    hbfaces, hbconstant, hbedge, hbexact, hbword⟩ := geometry
  let label : Fin D.vertexCount → W := evaluate ∘ address
  have hallowed (v : Fin D.vertexCount) :
      label v = anchor ∨ ∃ t ≤ steps, ∃ i : ι, labels t i = label v := by
    cases ha : address v with
    | none => exact Or.inl (by simp [label, evaluate, ha])
    | some z =>
        exact Or.inr ⟨z.1.val, Nat.le_of_lt_succ z.1.isLt, z.2,
          by simp [label, evaluate, ha]⟩
  have hface (σ : Finset (Fin D.vertexCount)) (hσ : σ ∈ D.complex.faces) :
      σ.image label ∈ K.faces := by
    obtain ⟨τ, hτ, hst | hco | hte⟩ := hshape σ hσ
    · obtain ⟨t, ht⟩ := hst
      have hsub : σ.image label ⊆ τ.image (labels t.val) := by
        simpa [Finset.image_image, label, Function.comp_def, evaluate, phase] using
          Finset.image_subset_image (f := evaluate) ht
      exact (K.isRelLowerSet_faces (hfaces t.val (Nat.le_of_lt_succ t.isLt) τ hτ)).2
        hsub ((D.complex.isRelLowerSet_faces hσ).1.image label)
    · obtain ⟨t, ht⟩ := hco
      have hsub : σ.image label ⊆
          τ.image (labels t.val) ∪ τ.image (labels (t.val + 1)) := by
        simpa [Finset.image_image, Finset.image_union, label, Function.comp_def,
          evaluate, phase] using Finset.image_subset_image (f := evaluate) ht
      exact (K.isRelLowerSet_faces (hcommon t.val t.isLt τ hτ)).2
        hsub ((D.complex.isRelLowerSet_faces hσ).1.image label)
    · have hsub : σ.image label ⊆ insert anchor (τ.image (labels steps)) := by
        simpa [Finset.image_image, label, Function.comp_def, evaluate, phase] using
          Finset.image_subset_image (f := evaluate) hte
      exact (K.isRelLowerSet_faces (hterminal τ hτ)).2
        hsub ((D.complex.isRelLowerSet_faces hσ).1.image label)
  obtain ⟨M, hM⟩ := regional_finite_label_realization_map D.complex K label hface
  have loopconstant (u : EdgeTime) :
      word.loop (Icc.convexComb (times 0) (times 1) u) = word.point 0 := by
    rw [word.loop_eq]
    exact hconstant u
  have loopedge (k : Fin word.edgeCount) (u : EdgeTime) :
      word.loop (Icc.convexComb (times k.succ.castSucc) (times k.succ.succ) u) =
        word.edge k u := by
    rw [word.loop_eq]
    exact hedge k u
  have boundary_eq (t : EdgeTime) : M (D.boundaryInclusion (param t)) = word.loop t := by
    obtain ⟨k, u, hu⟩ := cover word.edgeCount times t
      (by rw [hzeroTime]; exact t.property.1)
      (by rw [honeTime]; exact t.property.2)
    rw [hu]
    apply RealizationPoint.ext
    funext w
    rw [hM]
    let f : Option (Fin (steps + 1) × ι) → ℝ :=
      fun a => if evaluate a = w then 1 else 0
    have project (x : RealizationPoint D.complex) :
        (∑ v : Fin D.vertexCount, if label v = w then x.weight v else 0) =
          ∑ v : Fin D.vertexCount, f (address v) * x.weight v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [label, Function.comp_apply, f]
      split_ifs <;> ring
    rw [project]
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      rw [hbc, loopconstant, word.point_eq, realizationVertex_weight]
      simp [f, evaluate_zero, eq_comm]
    · rw [hbe, loopedge, word.edge_weight]
      simp [f, evaluate_zero]
  have mapped_constant (σ : Finset ↥D.boundaryVertices) (hσ : σ ∈ blocks 0) :
      σ.image (fun b => label b.val) ⊆ {initial (word.vertex 0)} := by
    simpa [Finset.image_image, label, Function.comp_def, evaluate_zero] using
      Finset.image_subset_image (f := evaluate) (hbconstant σ hσ)
  have mapped_edge (k : Fin word.edgeCount) (σ : Finset ↥D.boundaryVertices)
      (hσ : σ ∈ blocks k.succ) :
      σ.image (fun b => label b.val) ⊆
        {initial (word.vertex k.castSucc), initial (word.vertex k.succ)} := by
    simpa [Finset.image_image, label, Function.comp_def, evaluate_zero] using
      Finset.image_subset_image (f := evaluate) (hbedge k σ hσ)
  refine ⟨{
    disk := D
    label := label
    label_allowed := hallowed
    label_faces := hface
    label_image_card := fun σ hσ => (Finset.card_image_le).trans (D.face_card σ hσ)
    realizationMap := M
    realizationMap_weight := hM
    boundaryParam := param
    boundaryParam_surjective := hsurj
    boundaryParam_fibers := hfibers
    boundary_seam := (hfibers 0 1).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    reparam := Homeomorph.refl EdgeTime
    reparam_zero := rfl
    reparam_one := rfl
    reparamHomotopy := ContinuousMap.HomotopyRel.refl (ContinuousMap.id EdgeTime) _
    boundary_word := boundary_eq
    wordTimes := times
    wordTimes_strict := hmono
    wordTimes_zero := hzeroTime
    wordTimes_one := honeTime
    wordPieceTime := fun k => {
      toFun := Icc.convexComb (times k.castSucc) (times k.succ)
      continuous_toFun := Icc.continuous_convexComb _ _
      source' := Icc.convexComb_zero _ _
      target' := Icc.convexComb_one _ _ }
    wordPieceTime_affine := fun k u => rfl
    wordPiece_constant := loopconstant
    wordPiece_edge := loopedge
    boundaryBlock := blocks
    boundaryBlock_faces := hbfaces
    boundaryBlock_constant := mapped_constant
    boundaryBlock_edge := mapped_edge
    boundaryBlock_exact := hbexact
    boundary_face_word := ?_ }⟩
  intro σ hσ
  rcases hbword σ hσ with hc | ⟨k, hk⟩
  · exact Or.inl (by
      simpa [Finset.image_image, label, Function.comp_def, evaluate_zero] using
        Finset.image_subset_image (f := evaluate) hc)
  · exact Or.inr ⟨k, by
      simpa [Finset.image_image, label, Function.comp_def, evaluate_zero] using
        Finset.image_subset_image (f := evaluate) hk⟩

end CurveComplex.FiniteArcDisk
