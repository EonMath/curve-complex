import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeActualZeroRadials
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual zero radial set in the filled square is embedded, including its
boundary contacts. Compactness is proved from the actual square boundary. -/
theorem actual_square_cone_embedded_zero_radials
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V) (hc : center.val.2≠0) :
    ∃ G : C({z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ z : {z : ℝ × ℝ // ‖z‖=1},G ⟨z.val,z.property.le⟩=f z) ∧
    ∃ q : C({z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0},
      {z : ℝ × ℝ // ‖z‖≤1}),
      IsEmbedding q ∧
      (∀ z,(q z).val=(1/(1-(f z.val).val.2/center.val.2)) • z.val.val) ∧
      (∀ z,(G (q z)).val.2=0) := by
  have hQ : IsCompact {z : ℝ × ℝ | ‖z‖≤1} := by
    convert (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)) using 1
    ext z
    simp only [mem_ofPred_eq,mem_prod,mem_Icc,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
  have hB : IsClosed {z : ℝ × ℝ | ‖z‖=1} :=
    isClosed_eq (continuous_fst.norm.max continuous_snd.norm) continuous_const
  let : CompactSpace {z : ℝ × ℝ // ‖z‖=1} :=
    isCompact_iff_compactSpace.mp (hQ.of_isClosed_subset hB (fun z hz => hz.le))
  have hN : IsClosed {z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0} :=
    isClosed_le (by fun_prop) continuous_const
  let : CompactSpace {z : {z : ℝ × ℝ // ‖z‖=1} | (f z).val.2/center.val.2≤0} :=
    isCompact_iff_compactSpace.mp hN.isCompact
  obtain ⟨G,hboundary,q,hinj,hq,hzero⟩ := actual_square_cone_actual_zero_radials V hV f center hc
  exact ⟨G,hboundary,q,(q.continuous.isClosedEmbedding hinj).isEmbedding,hq,hzero⟩
end CurveComplex.HyperellipticModel
