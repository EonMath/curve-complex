import ClassificationOfSurfaces.Moise.LineSubdivision
import ClassificationOfSurfaces.TriangleCell
import ClassificationOfSurfaces.DiskSquare
import CurveComplexGenusTwo.Topology.ActualGenusZeroPlanarity.ActualZeroHandleTwoBoundaryCutRectangle
import CurveComplexGenusTwo.Topology.ActualDiskFan.ActualDiskFan
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.ZeroHandleClosedDisc
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib
open Set Topology Filter
set_option maxHeartbeats 1000000

namespace CurveComplex.Hyperbolic
open LeanEval.Topology.ClassificationOfSurfaces

/-- Actual raw compact genus-zero model with a nonempty boundary embeds in the plane. -/
theorem actual_genus_zero_boundary_model_embeds_plane (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : Quot (OrientableRel 0 n) → EuclideanSpace ℝ (Fin 2),
      Topology.IsEmbedding f := by
  by_cases hn1 : n=1
  · subst n
    obtain ⟨d,hd⟩ := actual_zero_handle_one_boundary_model_closed_disc
    exact ⟨Subtype.val ∘ d.symm, Topology.IsEmbedding.subtypeVal.comp d.symm.isEmbedding⟩
  · have hn2 : 2 ≤ n := by omega
    let sector (i : Fin n) (x y : unitInterval) : ℂ × ℝ :=
      (Real.sqrt ((y : ℝ)*(1-(y : ℝ))) *
        (Real.fourierChar (((i.val : ℝ)+(x : ℝ))/(n : ℝ)) : ℂ), (y : ℝ))
    have hCont (i : Fin n) : Continuous (fun z : unitInterval × unitInterval =>
        sector i z.1 z.2) := by
      apply Continuous.prodMk
      · exact (Complex.continuous_ofReal.comp
          (Real.continuous_sqrt.comp (by fun_prop))).mul
          (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop)))
      · exact continuous_subtype_val.comp continuous_snd
    have hRadius (y : unitInterval) :
        0 ≤ (y : ℝ)*(1-(y : ℝ)) := mul_nonneg y.property.1 (by linarith [y.property.2])
    have hSphere (i : Fin n) (x y : unitInterval) :
        ‖(sector i x y).1‖^2 + ((sector i x y).2 - 1/2)^2 = 1/4 := by
      simp only [sector, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt (hRadius y)]
      ring
    have hKernel (i j : Fin n) (x u y v : unitInterval) :
        sector i x y = sector j u v ↔
        y=v ∧ ((y : ℝ)=0 ∨ (y : ℝ)=1 ∨
          ∃ k : ℤ, (i.val : ℝ)+(x : ℝ) =
            (j.val : ℝ)+(u : ℝ)+(k : ℝ)*(n : ℝ)) := by
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0< n by omega)
      constructor
      · intro he
        have hy : y=v := Subtype.ext (congrArg Prod.snd he)
        subst v
        refine ⟨rfl,?_⟩
        by_cases hy0 : (y : ℝ)=0
        · exact Or.inl hy0
        by_cases hy1 : (y : ℝ)=1
        · exact Or.inr (Or.inl hy1)
        have hpos : 0 < Real.sqrt ((y : ℝ)*(1-(y : ℝ))) := by
          apply Real.sqrt_pos.2
          exact mul_pos (lt_of_le_of_ne y.property.1 (Ne.symm hy0))
            (sub_pos.mpr (lt_of_le_of_ne y.property.2 hy1))
        have hc : Real.fourierChar (((i.val : ℝ)+(x : ℝ))/(n : ℝ)) =
            Real.fourierChar (((j.val : ℝ)+(u : ℝ))/(n : ℝ)) := by
          apply Subtype.ext
          exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne') (congrArg Prod.fst he)
        rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
        obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hc
        refine Or.inr (Or.inr ⟨k,?_⟩)
        have heq : ((i.val : ℝ)+(x : ℝ))/(n : ℝ) =
            ((j.val : ℝ)+(u : ℝ))/(n : ℝ)+(k : ℝ) := by
          nlinarith [Real.pi_pos]
        have hm := congrArg (fun r : ℝ => r*(n : ℝ)) heq
        rw [add_mul,div_mul_cancel₀ _ hnpos.ne',div_mul_cancel₀ _ hnpos.ne'] at hm
        exact hm
      · rintro ⟨rfl,hy0|hy1|⟨k,hk⟩⟩
        · apply Prod.ext <;> simp [sector,hy0]
        · apply Prod.ext <;> simp [sector,hy1]
        · apply Prod.ext
          · dsimp only [sector]
            congr 1
            have heq : ((i.val : ℝ)+(x : ℝ))/(n : ℝ) =
                ((j.val : ℝ)+(u : ℝ))/(n : ℝ)+(k : ℝ) := by
              apply (div_eq_iff hnpos.ne').2
              rw [add_mul,div_mul_cancel₀ _ hnpos.ne']
              exact hk
            rw [heq]
            apply congrArg (fun z : Circle => (z : ℂ))
            rw [Real.fourierChar_apply',Real.fourierChar_apply']
            apply Circle.exp_eq_exp.mpr
            exact ⟨k,by ring⟩
          · rfl
    have hSectorAdjacent (i j : Fin n) (y : unitInterval)
        (hij : j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0)) :
        sector i 1 y=sector j 0 y := by
      apply (hKernel i j 1 0 y y).mpr
      refine ⟨rfl,Or.inr (Or.inr ?_)⟩
      rcases hij with hij|⟨hin,hj⟩
      · refine ⟨0,?_⟩
        have he : (j.val : ℝ)=(i.val : ℝ)+1 := by exact_mod_cast hij
        norm_num
        linarith
      · refine ⟨1,?_⟩
        have he : (i.val : ℝ)+1=(n : ℝ) := by exact_mod_cast hin
        norm_num [hj]
        exact he
    have hSectorEdgeKernel (i j : Fin n) (y : unitInterval)
        (hy0 : 0<(y : ℝ)) (hy1 : (y : ℝ)<1)
        (he : sector i 1 y=sector j 0 y) :
        j.val=i.val+1 ∨ (i.val+1=n ∧ j.val=0) := by
      obtain ⟨_,hzero|hone|⟨k,hk⟩⟩ := (hKernel i j 1 0 y y).mp he
      · linarith
      · linarith
      · norm_num at hk
        have hi : (i.val : ℝ)+1≤ n := by exact_mod_cast i.isLt
        have hj : (j.val : ℝ)+1≤ n := by exact_mod_cast j.isLt
        have hinon := Nat.cast_nonneg (α:=ℝ) i.val
        have hjnon := Nat.cast_nonneg (α:=ℝ) j.val
        have hnreal : (2 : ℝ)≤ n := by exact_mod_cast hn2
        have hklo : (-1 : ℝ)<(k : ℝ) := by nlinarith
        have hkhi : (k : ℝ)≤1 := by nlinarith
        have hklo' : (-1 : ℤ)< k := by exact_mod_cast hklo
        have hkhi' : k≤(1 : ℤ) := by exact_mod_cast hkhi
        have hkc : k=0 ∨ k=1 := by omega
        rcases hkc with hkc|hkc
        · simp only [hkc,Int.cast_zero,zero_mul,add_zero] at hk
          left
          exact_mod_cast hk.symm
        · simp only [hkc,Int.cast_one,one_mul] at hk
          have hjzero : (j.val : ℝ)=0 := by linarith
          right
          constructor
          · exact_mod_cast (show (i.val : ℝ)+1=(n : ℝ) by linarith)
          · exact_mod_cast hjzero
    have hInteriorInjective (i j : Fin n) (x u y v : unitInterval)
        (hx0 : 0<(x : ℝ)) (hx1 : (x : ℝ)<1)
        (hu0 : 0<(u : ℝ)) (hu1 : (u : ℝ)<1)
        (hy0 : 0<(y : ℝ)) (hy1 : (y : ℝ)<1)
        (he : sector i x y=sector j u v) : i=j ∧ x=u ∧ y=v := by
      obtain ⟨hy,hendpoint|hendpoint|⟨k,hk⟩⟩ := (hKernel i j x u y v).mp he
      · linarith
      · linarith
      · have hi : (i.val : ℝ)+1 ≤ n := by exact_mod_cast i.isLt
        have hj : (j.val : ℝ)+1 ≤ n := by exact_mod_cast j.isLt
        have hinon := Nat.cast_nonneg (α:=ℝ) i.val
        have hjnon := Nat.cast_nonneg (α:=ℝ) j.val
        have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0< n by omega)
        have hk0 : (-1 : ℝ)<(k : ℝ) := by nlinarith
        have hk1 : (k : ℝ)<1 := by nlinarith
        have hk0' : (-1 : ℤ)< k := by exact_mod_cast hk0
        have hk1' : k<(1 : ℤ) := by exact_mod_cast hk1
        have hke : k=0 := by omega
        simp only [hke,Int.cast_zero,zero_mul,add_zero] at hk
        have hd0 : (-1 : ℝ)<(i.val : ℝ)-(j.val : ℝ) := by linarith
        have hd1 : (i.val : ℝ)-(j.val : ℝ)<1 := by linarith
        have hd0' : (-1 : ℤ)<(i.val : ℤ)-(j.val : ℤ) := by exact_mod_cast hd0
        have hd1' : (i.val : ℤ)-(j.val : ℤ)<1 := by exact_mod_cast hd1
        have hij : i=j := Fin.ext (by omega)
        subst j
        exact ⟨rfl,Subtype.ext (by linarith),hy⟩
    let inner (t : unitInterval) : unitInterval :=
      ⟨1/4+(t : ℝ)/2, by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hInnerCont : Continuous inner := by
      exact Continuous.subtype_mk (by fun_prop) _
    have hInnerBounds (t : unitInterval) : 0<(inner t : ℝ) ∧ (inner t : ℝ)<1 := by
      dsimp [inner]
      constructor <;> linarith [t.property.1,t.property.2]
    have hInnerInj : Function.Injective inner := by
      intro t u he
      apply Subtype.ext
      have hv := congrArg (fun z : unitInterval => (z : ℝ)) he
      dsimp [inner] at hv
      linarith
    let hole (i : Fin n) (z : unitInterval × unitInterval) :=
      sector i (inner z.1) (inner z.2)
    have hHoleCont (i : Fin n) : Continuous (hole i) :=
      (hCont i).comp ((hInnerCont.comp continuous_fst).prodMk
        (hInnerCont.comp continuous_snd))
    have hHoleInj (i : Fin n) : Function.Injective (hole i) := by
      rintro ⟨x,y⟩ ⟨u,v⟩ he
      obtain ⟨_,hxu,hyv⟩ := hInteriorInjective i i (inner x) (inner u) (inner y) (inner v)
        (hInnerBounds x).1 (hInnerBounds x).2 (hInnerBounds u).1 (hInnerBounds u).2
        (hInnerBounds y).1 (hInnerBounds y).2 he
      exact Prod.ext (hInnerInj hxu) (hInnerInj hyv)
    have hHoleEmbedding (i : Fin n) : Topology.IsClosedEmbedding (hole i) :=
      (hHoleCont i).isClosedEmbedding (hHoleInj i)
    have hHoleDisjoint : Pairwise (fun i j : Fin n =>
        Disjoint (Set.range (hole i)) (Set.range (hole j))) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      rintro z ⟨⟨x,y⟩,hx⟩ ⟨⟨u,v⟩,hu⟩
      have he : hole i (x,y)=hole j (u,v) := hx.trans hu.symm
      exact hij (hInteriorInjective i j (inner x) (inner u) (inner y) (inner v)
        (hInnerBounds x).1 (hInnerBounds x).2 (hInnerBounds u).1 (hInnerBounds u).2
        (hInnerBounds y).1 (hInnerBounds y).2 he).1
    let weights : List ℕ := [1,2,2,2,1]
    have hw : ∀ w ∈ weights, 0< w := by simp [weights]
    have hne : weights ≠ [] := by simp [weights]
    let rot : Circle ≃ₜ Circle := Homeomorph.mulLeft (Circle.exp (Real.pi/2))
    let b : Circle ≃ₜ DiskSquare.boundary :=
      (WeightedCircle.circleHomeomorph weights hw hne).trans
        (rot.trans DiskSquare.circleBoundaryHomeomorph)
    let d : PolygonCell 5 ≃ₜ DiskSquare.square := DiskSquare.cellSquareHomeomorph b
    have hSide (i : Fin 5) (t : unitInterval) :
        (d (PolygonCell.side i t)).val =
        (DiskSquare.circleBoundaryHomeomorph
          (Circle.exp (Real.pi/2 + 2*Real.pi/8 *
            (((weights.take i.val).sum : ℕ) + (weights[i.val]'(by simpa [weights] using i.isLt) : ℝ)*(t : ℝ))))).val := by
      rw [show d (PolygonCell.side i t) = DiskSquare.boundaryInclusion
        (b (Circle.exp (PolygonCell.sideAngle i t))) from
        DiskSquare.cellSquareHomeomorph_ofCircle b _]
      change (DiskSquare.circleBoundaryHomeomorph
        (Circle.exp (Real.pi/2) *
          WeightedCircle.circleHomeomorph weights hw hne
            (Circle.exp (PolygonCell.sideAngle i t)))).val = _
      have h := WeightedCircle.circleHomeomorph_exp_index_add' weights hw hne
        (⟨i.val,by simpa [weights] using i.isLt⟩ : Fin weights.length) t
      have he : PolygonCell.sideAngle i t =
          2*Real.pi/(weights.length : ℝ)*((i.val : ℝ)+(t : ℝ)) := by
        simp [PolygonCell.sideAngle,weights]
        ring
      rw [he,h,← Circle.exp_add]
      congr 3 <;> norm_num [weights]
    have hReflect (a : ℝ) :
        (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi-a))).val =
        -starRingEnd ℂ ((DiskSquare.circleBoundaryHomeomorph (Circle.exp a)).val) := by
      have he : (Circle.exp (Real.pi-a) : ℂ) =
          -starRingEnd ℂ (Circle.exp a : ℂ) := by
        rw [sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,Circle.coe_mul,
          Circle.coe_inv_eq_conj,Circle.coe_exp,Complex.exp_pi_mul_I]
        simp
      simp only [DiskSquare.circleBoundaryHomeomorph_val,DiskSquare.radialToBoundary,he]
      have hm (z : ℂ) : DiskSquare.maxAbs (-starRingEnd ℂ z)=DiskSquare.maxAbs z := by
        simp [DiskSquare.maxAbs]
      rw [hm]
      simp [neg_div]
    have hSeam (t : unitInterval) :
        (d (PolygonCell.side (3 : Fin 5) (unitInterval.symm t))).val =
          -starRingEnd ℂ ((d (PolygonCell.side (1 : Fin 5) t)).val) := by
      rw [hSide,hSide]
      have hleft : Real.pi/2+2*Real.pi/8*
          (((weights.take (1 : Fin 5).val).sum : ℕ)+
            (weights[(1 : Fin 5).val]'(by decide) : ℝ)*(t : ℝ)) =
          3*Real.pi/4+Real.pi/2*(t : ℝ) := by norm_num [weights] <;> ring <;> simp
      have hright : Real.pi/2+2*Real.pi/8*
          (((weights.take (3 : Fin 5).val).sum : ℕ)+
            (weights[(3 : Fin 5).val]'(by decide) : ℝ)*(unitInterval.symm t : ℝ)) =
          Real.pi-(3*Real.pi/4+Real.pi/2*(t : ℝ))+2*Real.pi := by
        norm_num [weights,unitInterval.symm]; ring
      rw [hleft,hright]
      have hp : Circle.exp (Real.pi-(3*Real.pi/4+Real.pi/2*(t : ℝ))+2*Real.pi) =
          Circle.exp (Real.pi-(3*Real.pi/4+Real.pi/2*(t : ℝ))) := by
        apply Circle.exp_eq_exp.mpr
        exact ⟨1,by push_cast; ring⟩
      rw [hp]
      exact hReflect _
    have hOuterReflect (t : unitInterval) :
        (d (PolygonCell.side (4 : Fin 5) (unitInterval.symm t))).val =
          -starRingEnd ℂ ((d (PolygonCell.side (0 : Fin 5) t)).val) := by
      rw [hSide,hSide]
      have hl : Real.pi/2+2*Real.pi/8*
          (((weights.take (0 : Fin 5).val).sum : ℕ)+
            (weights[(0 : Fin 5).val]'(by decide) : ℝ)*(t : ℝ)) =
          Real.pi/2+Real.pi/4*(t : ℝ) := by norm_num [weights] <;> ring <;> simp
      have hr : Real.pi/2+2*Real.pi/8*
          (((weights.take (4 : Fin 5).val).sum : ℕ)+
            (weights[(4 : Fin 5).val]'(by decide) : ℝ)*(unitInterval.symm t : ℝ)) =
          Real.pi-(Real.pi/2+Real.pi/4*(t : ℝ))+2*Real.pi := by
        norm_num [weights,unitInterval.symm]; ring
      rw [hl,hr]
      have hp : Circle.exp (Real.pi-(Real.pi/2+Real.pi/4*(t : ℝ))+2*Real.pi) =
          Circle.exp (Real.pi-(Real.pi/2+Real.pi/4*(t : ℝ))) := by
        apply Circle.exp_eq_exp.mpr
        exact ⟨1,by push_cast; ring⟩
      rw [hp]
      exact hReflect _
    have hQuarter (a : ℝ) :
        (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi/2+a))).val =
          Complex.I*(DiskSquare.circleBoundaryHomeomorph (Circle.exp a)).val := by
      have he : (Circle.exp (Real.pi/2+a) : ℂ)=Complex.I*(Circle.exp a : ℂ) := by
        rw [Circle.exp_add,Circle.coe_mul,Circle.coe_exp]
        push_cast
        rw [Complex.exp_pi_div_two_mul_I]
      simp only [DiskSquare.circleBoundaryHomeomorph_val,DiskSquare.radialToBoundary,he]
      have hm (z : ℂ) : DiskSquare.maxAbs (Complex.I*z)=DiskSquare.maxAbs z := by
        simp [DiskSquare.maxAbs,Complex.mul_re,Complex.mul_im,max_comm]
      rw [hm,mul_div_assoc]
    have hOuterTop (t : unitInterval) :
        (d (PolygonCell.side (0 : Fin 5) t)).val.im=1 := by
      rw [hSide]
      have hl : Real.pi/2+2*Real.pi/8*
          (((weights.take (0 : Fin 5).val).sum : ℕ)+
            (weights[(0 : Fin 5).val]'(by decide) : ℝ)*(t : ℝ)) =
          Real.pi/2+Real.pi/4*(t : ℝ) := by norm_num [weights] <;> ring <;> simp
      rw [hl,hQuarter]
      simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
        DiskSquare.circleBoundaryHomeomorph_val]
      apply DiskSquare.radialToBoundary_re_eq_one_of_angle
      constructor <;> nlinarith [t.property.1,t.property.2,Real.pi_pos]
    have hOuterReNonpos (t : unitInterval) :
        (d (PolygonCell.side (0 : Fin 5) t)).val.re≤0 := by
      rw [hSide]
      have hl : Real.pi/2+2*Real.pi/8*
          (((weights.take (0 : Fin 5).val).sum : ℕ)+
            (weights[(0 : Fin 5).val]'(by decide) : ℝ)*(t : ℝ)) =
          Real.pi/2+Real.pi/4*(t : ℝ) := by norm_num [weights] <;> ring <;> simp
      rw [hl,hQuarter]
      simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
      apply neg_nonpos.mpr
      rw [DiskSquare.circleBoundaryHomeomorph_val]
      dsimp only [DiskSquare.radialToBoundary]
      rw [Complex.div_ofReal_im]
      apply div_nonneg _ (DiskSquare.maxAbs_pos (Circle.exp _).coe_ne_zero).le
      simp only [Circle.coe_exp,Complex.exp_im,Complex.mul_re,Complex.ofReal_re,
        Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,zero_mul,sub_self,
        Real.exp_zero,Complex.mul_im,one_mul,mul_one,zero_add]
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
        nlinarith [t.property.1,t.property.2,Real.pi_pos]
    have hNeg (a : ℝ) :
        (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi+a))).val =
        -(DiskSquare.circleBoundaryHomeomorph (Circle.exp a)).val := by
      have he : (Circle.exp (Real.pi+a) : ℂ) = -(Circle.exp a : ℂ) := by
        rw [Circle.exp_add,Circle.coe_mul,Circle.coe_exp,Complex.exp_pi_mul_I]
        simp
      simp only [DiskSquare.circleBoundaryHomeomorph_val,DiskSquare.radialToBoundary,he]
      have hm (z : ℂ) : DiskSquare.maxAbs (-z)=DiskSquare.maxAbs z := by
        simp [DiskSquare.maxAbs]
      rw [hm,neg_div]
    have hLeftRe (t : unitInterval) : (d (PolygonCell.side (1 : Fin 5) t)).val.re= -1 := by
      rw [hSide]
      have ha : Real.pi/2+2*Real.pi/8*
          (((weights.take (1 : Fin 5).val).sum : ℕ)+
            (weights[(1 : Fin 5).val]'(by decide) : ℝ)*(t : ℝ)) =
          Real.pi+(-Real.pi/4+Real.pi/2*(t : ℝ)) := by norm_num [weights] <;> ring <;> simp
      rw [ha,hNeg,Complex.neg_re]
      rw [DiskSquare.circleBoundaryHomeomorph_val,
        DiskSquare.radialToBoundary_re_eq_one_of_angle]
      constructor <;> nlinarith [t.property.1,t.property.2,Real.pi_pos]
    have hLeftTop : (d (PolygonCell.side (1 : Fin 5) 0)).val.im=1 := by
      have he : PolygonCell.side (0 : Fin 5) 1=PolygonCell.side (1 : Fin 5) 0 := by
        simpa using PolygonCell.side_one_eq_rotate_zero (0 : Fin 5)
      rw [←he]
      exact hOuterTop 1
    have hOuterReStart : (d (PolygonCell.side (0 : Fin 5) 0)).val.re=0 := by
      rw [hSide]
      norm_num [weights]
      rw [show Real.pi/2 = Real.pi/2+0 by ring,hQuarter]
      simp [DiskSquare.circleBoundaryHomeomorph_val,DiskSquare.radialToBoundary]
    have hOuterReEnd : (d (PolygonCell.side (0 : Fin 5) 1)).val.re= -1 := by
      have he : PolygonCell.side (0 : Fin 5) 1=PolygonCell.side (1 : Fin 5) 0 := by
        simpa using PolygonCell.side_one_eq_rotate_zero (0 : Fin 5)
      rw [he]
      exact hLeftRe 0
    have hOuterRightAll (z : PolygonCell 5)
        (hz : (d z).val.im=1) (hr : (d z).val.re≤0) :
        ∃ t : unitInterval, z=PolygonCell.side (0 : Fin 5) t := by
      have hc : Continuous (fun t : unitInterval => (d (PolygonCell.side (0 : Fin 5) t)).val.re) :=
        Complex.continuous_re.comp (continuous_subtype_val.comp
          (d.continuous.comp (PolygonCell.side (0 : Fin 5)).continuous))
      have hy : (d z).val.re ∈ Set.Icc
          ((d (PolygonCell.side (0 : Fin 5) 1)).val.re)
          ((d (PolygonCell.side (0 : Fin 5) 0)).val.re) := by
        rw [hOuterReEnd,hOuterReStart]
        exact ⟨(abs_le.mp ((DiskSquare.abs_re_le_maxAbs _).trans (d z).property)).1,hr⟩
      obtain ⟨t,ht⟩ := intermediate_value_univ (1 : unitInterval) 0 hc hy
      refine ⟨t,d.injective (Subtype.ext (Complex.ext ht.symm ?_))⟩
      rw [hz,hOuterTop]
    have hOuterLeftAll (z : PolygonCell 5)
        (hz : (d z).val.im=1) (hr : 0≤(d z).val.re) :
        ∃ t : unitInterval, z=PolygonCell.side (4 : Fin 5) (unitInterval.symm t) := by
      have hc : Continuous (fun t : unitInterval => (d (PolygonCell.side (0 : Fin 5) t)).val.re) :=
        Complex.continuous_re.comp (continuous_subtype_val.comp
          (d.continuous.comp (PolygonCell.side (0 : Fin 5)).continuous))
      have hy : -(d z).val.re ∈ Set.Icc
          ((d (PolygonCell.side (0 : Fin 5) 1)).val.re)
          ((d (PolygonCell.side (0 : Fin 5) 0)).val.re) := by
        rw [hOuterReEnd,hOuterReStart]
        constructor
        · linarith [(abs_le.mp ((DiskSquare.abs_re_le_maxAbs _).trans (d z).property)).2]
        · linarith
      obtain ⟨t,ht⟩ := intermediate_value_univ (1 : unitInterval) 0 hc hy
      refine ⟨t,d.injective (Subtype.ext (Complex.ext ?_ ?_))⟩
      · rw [hOuterReflect]
        simp only [Complex.neg_re,Complex.conj_re]
        linarith
      · rw [hOuterReflect]
        simp only [Complex.neg_im,Complex.conj_im,neg_neg]
        rw [hz,hOuterTop]
    have hLeftBottom : (d (PolygonCell.side (1 : Fin 5) 1)).val.im= -1 := by
      have h0 : (d (PolygonCell.side (1 : Fin 5) 0)).val =
          (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi/2+Real.pi/4))).val := by
        rw [hSide]
        congr 3 <;> norm_num [weights] <;> ring
      have h1 : (d (PolygonCell.side (1 : Fin 5) 1)).val =
          (DiskSquare.circleBoundaryHomeomorph (Circle.exp (Real.pi+Real.pi/4))).val := by
        rw [hSide]
        congr 3 <;> norm_num [weights] <;> ring
      have hh := hLeftRe 0
      rw [h0,hQuarter] at hh
      simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hh
      rw [h1,hNeg,Complex.neg_im]
      linarith
    have hLeftSideAll (z : PolygonCell 5) (hz : (d z).val.re= -1) :
        ∃ t : unitInterval, z=PolygonCell.side (1 : Fin 5) t := by
      have hc : Continuous (fun t : unitInterval => (d (PolygonCell.side (1 : Fin 5) t)).val.im) := by
        exact Complex.continuous_im.comp (continuous_subtype_val.comp
          (d.continuous.comp (PolygonCell.side (1 : Fin 5)).continuous))
      have hy : (d z).val.im ∈ Set.Icc
          ((d (PolygonCell.side (1 : Fin 5) 1)).val.im)
          ((d (PolygonCell.side (1 : Fin 5) 0)).val.im) := by
        rw [hLeftBottom,hLeftTop]
        exact abs_le.mp ((DiskSquare.abs_im_le_maxAbs _).trans (d z).property)
      obtain ⟨t,ht⟩ := intermediate_value_univ (1 : unitInterval) 0 hc hy
      refine ⟨t,d.injective (Subtype.ext (Complex.ext ?_ ?_))⟩
      · rw [hz,hLeftRe]
      · exact ht.symm
    have hOppositeSideFiber (z w : PolygonCell 5)
        (hz : (d z).val.re= -1) (hw : (d w).val.re=1)
        (hy : (d z).val.im=(d w).val.im) :
        ∃ t : unitInterval, z=PolygonCell.side (1 : Fin 5) t ∧
          w=PolygonCell.side (3 : Fin 5) (unitInterval.symm t) := by
      obtain ⟨t,rfl⟩ := hLeftSideAll z hz
      refine ⟨t,rfl,d.injective (Subtype.ext (Complex.ext ?_ ?_))⟩
      · rw [hSeam]
        simp only [Complex.neg_re,Complex.conj_re,hLeftRe]
        simpa using hw
      · rw [hSeam]
        simp only [Complex.neg_im,Complex.conj_im,neg_neg]
        exact hy.symm
    let strip (z : PolygonCell 5) : ℂ :=
      (((3+(d z).val.im)/4 : ℝ):ℂ)*
        (Circle.exp (Real.pi*((d z).val.re+1)-Real.pi/2) : ℂ)
    have hStripCont : Continuous strip := by
      exact (by fun_prop : Continuous (fun z : PolygonCell 5 =>
        (((3+(d z).val.im)/4 : ℝ):ℂ))).mul
        (continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop)))
    have hStripSeam (t : unitInterval) : strip (PolygonCell.side (1 : Fin 5) t)=
        strip (PolygonCell.side (3 : Fin 5) (unitInterval.symm t)) := by
      have he := hSeam t
      have hr := hLeftRe t
      have hr' : (d (PolygonCell.side (3 : Fin 5) (unitInterval.symm t))).val.re=1 := by
        rw [he]; simp [hr]
      have hi : (d (PolygonCell.side (3 : Fin 5) (unitInterval.symm t))).val.im =
          (d (PolygonCell.side (1 : Fin 5) t)).val.im := by rw [he]; simp
      dsimp only [strip]
      rw [hr,hr',hi]
      congr 1
      apply congrArg (fun c : Circle => (c : ℂ))
      apply Circle.exp_eq_exp.mpr
      exact ⟨-1,by push_cast; ring⟩
    let gauge (z : ℂ) : ℝ := |z.re|+|z.im|
    have hGaugeCont : Continuous gauge := by fun_prop
    have hGaugePos (c : Circle) : 0< gauge (c : ℂ) := by
      have hn := c.coe_ne_zero
      have hg0 : 0≤ gauge (c : ℂ) := add_nonneg (abs_nonneg _) (abs_nonneg _)
      apply lt_of_le_of_ne hg0
      intro he
      have hre : (c : ℂ).re=0 := abs_eq_zero.mp (by dsimp [gauge] at he; nlinarith [abs_nonneg (c : ℂ).re,abs_nonneg (c : ℂ).im])
      have him : (c : ℂ).im=0 := abs_eq_zero.mp (by dsimp [gauge] at he; nlinarith [abs_nonneg (c : ℂ).re,abs_nonneg (c : ℂ).im])
      exact hn (Complex.ext hre him)
    let diamond (r : ℝ) (c : Circle) : ℂ := (r/gauge (c : ℂ) : ℝ) * (c : ℂ)
    have hDiamondCont : Continuous (fun z : ℝ × Circle => diamond z.1 z.2) := by
      exact (Complex.continuous_ofReal.comp
        (continuous_fst.div (hGaugeCont.comp (continuous_subtype_val.comp continuous_snd))
          (fun z => (hGaugePos z.2).ne'))).mul
          (continuous_subtype_val.comp continuous_snd)
    have hGaugeDiamond (r : ℝ) (hr : 0≤ r) (c : Circle) : gauge (diamond r c)=r := by
      have hgn := (hGaugePos c).le
      dsimp only [diamond,gauge]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
        Complex.mul_im,add_zero]
      change |(r/gauge (c : ℂ))*(c : ℂ).re| +
        |(r/gauge (c : ℂ))*(c : ℂ).im| = r
      rw [abs_mul,abs_mul,abs_of_nonneg (div_nonneg hr hgn),← mul_add]
      change r/gauge (c : ℂ)*gauge (c : ℂ)=r
      exact div_mul_cancel₀ _ (hGaugePos c).ne'
    have hDiamondKernel (r s : ℝ) (hr : 0< r) (hs : 0< s) (c d : Circle)
        (he : diamond r c=diamond s d) : r=s ∧ c=d := by
      have hrad := congrArg gauge he
      rw [hGaugeDiamond r hr.le,hGaugeDiamond s hs.le] at hrad
      subst s
      have hc := congrArg norm he
      have hnorm (e : Circle) : ‖diamond r e‖=r/gauge (e : ℂ) := by
        simp only [diamond,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos (div_pos hr (hGaugePos e))]
      rw [hnorm,hnorm] at hc
      have hg : gauge (c : ℂ)=gauge (d : ℂ) := by
        have hc' := (div_eq_div_iff (hGaugePos c).ne' (hGaugePos d).ne').mp hc
        nlinarith
      refine ⟨rfl,Subtype.ext ?_⟩
      apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (div_pos hr (hGaugePos c)).ne')
      simpa only [diamond,hg] using he
    let D := {z : ℂ | |z.re|+|z.im|≤1}
    let lat (z : D) : ℝ := (z.val.im+1)/2
    let phase (i : Fin n) (z : D) : ℝ :=
      ((i.val : ℝ)+(z.val.re/(1-|z.val.im|)+1)/2)/(n : ℝ)
    let lune (i : Fin n) (z : D) : ℂ × ℝ :=
      (Real.sqrt (lat z*(1-lat z))*(Real.fourierChar (phase i z) : ℂ),lat z)
    have hCoords (z : D) : -1≤ z.val.im ∧ z.val.im≤1 := by
      have hz : |z.val.re|+|z.val.im|≤1 := z.property
      have hi : |z.val.im|≤1 := by linarith [hz,abs_nonneg z.val.re]
      exact abs_le.mp hi
    have hLat (z : D) : 0≤ lat z ∧ lat z≤1 := by
      dsimp [lat]; constructor <;> linarith [(hCoords z).1,(hCoords z).2]
    have hLatCont : Continuous lat := by fun_prop
    have hNorm (i : Fin n) (z : D) : ‖(lune i z).1‖=Real.sqrt (lat z*(1-lat z)) := by
      simp only [lune,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have hLuneCont (i : Fin n) : Continuous (lune i) := by
      apply Continuous.prodMk _ hLatCont
      apply continuous_iff_continuousAt.mpr
      intro z
      by_cases hz : 1-|z.val.im|=0
      · have ha : |z.val.im|=1 := by linarith
        have he : z.val.im=1 ∨ z.val.im= -1 := (abs_eq (by norm_num : (0:ℝ)≤1)).mp ha
        have hzero : lat z*(1-lat z)=0 := by
          rcases he with he|he <;> simp [lat,he]
        have hlzero : (lune i z).1=0 := by simp [lune,hzero]
        change Tendsto (fun w : D => (lune i w).1) (𝓝 z) (𝓝 ((lune i z).1))
        rw [hlzero,tendsto_zero_iff_norm_tendsto_zero]
        simp only [hNorm]
        have hc : Continuous (fun w : D => Real.sqrt (lat w*(1-lat w))) := by fun_prop
        simpa [hzero] using (hc.continuousAt (x := z)).tendsto
      · have hp : ContinuousAt (phase i) z := by
          dsimp [phase]
          have ha : ContinuousAt (fun w : D => w.val.re/(1-|w.val.im|)) z :=
            (Complex.continuous_re.comp continuous_subtype_val).continuousAt.div
              (continuousAt_const.sub
                ((Complex.continuous_im.comp continuous_subtype_val).continuousAt.abs)) hz
          have hb : ContinuousAt (fun w : D => (w.val.re/(1-|w.val.im|)+1)/2) z :=
            (ha.add continuousAt_const).div_const 2
          exact (continuousAt_const.add hb).div_const (n : ℝ)
        exact (Complex.continuous_ofReal.comp
          (Real.continuous_sqrt.comp (hLatCont.mul (continuous_const.sub hLatCont)))).continuousAt.mul
            (continuous_subtype_val.continuousAt.comp
              ((Real.continuous_fourierChar.continuousAt).comp hp))
    have hGridBounds (z : D) :
        0≤(z.val.re/(1-|z.val.im|)+1)/2 ∧ (z.val.re/(1-|z.val.im|)+1)/2≤1 := by
      have hz : |z.val.re|+|z.val.im|≤1 := z.property
      have hd : 0≤1-|z.val.im| := by linarith [abs_nonneg z.val.re]
      by_cases he : 1-|z.val.im|=0
      · simp [he]
        norm_num
      · have hp := lt_of_le_of_ne hd (Ne.symm he)
        have hr : -(1-|z.val.im|)≤ z.val.re ∧ z.val.re≤1-|z.val.im| :=
          abs_le.mp (by linarith)
        have hlo : -1≤ z.val.re/(1-|z.val.im|) := (le_div_iff₀ hp).mpr (by linarith [hr.1])
        have hhi : z.val.re/(1-|z.val.im|)≤1 := (div_le_iff₀ hp).mpr (by linarith [hr.2])
        constructor <;> linarith
    let gridX (z : D) : unitInterval := ⟨(z.val.re/(1-|z.val.im|)+1)/2,hGridBounds z⟩
    let gridY (z : D) : unitInterval := ⟨lat z,hLat z⟩
    have hAsSector (i : Fin n) (z : D) : lune i z=sector i (gridX z) (gridY z) := rfl
    have hSectorStrictIndex (i j : Fin n) (x u y v : unitInterval)
        (hx0 : 0<(x:ℝ)) (hx1 : (x:ℝ)<1)
        (hy0 : 0<(y:ℝ)) (hy1 : (y:ℝ)<1)
        (he : sector i x y=sector j u v) : i=j := by
      obtain ⟨hy,hh⟩ := (hKernel i j x u y v).mp he
      rcases hh with hp|hp|⟨k,hk⟩
      · linarith
      · linarith
      · have hin : (i.val:ℝ)≤(n:ℝ)-1 := by
          have h : (i.val:ℝ)+1≤ n := by exact_mod_cast (show i.val+1≤ n by omega)
          linarith
        have hjn : (j.val:ℝ)≤(n:ℝ)-1 := by
          have h : (j.val:ℝ)+1≤ n := by exact_mod_cast (show j.val+1≤ n by omega)
          linarith
        have hi0 : (0:ℝ)≤ i.val := by positivity
        have hj0 : (0:ℝ)≤ j.val := by positivity
        have hnpos : (0:ℝ)< n := by exact_mod_cast (show 0< n by omega)
        have hklo : (-1:ℝ)<(k:ℝ) := by nlinarith [u.property.1,u.property.2]
        have hkhi : (k:ℝ)<1 := by nlinarith [u.property.1,u.property.2]
        have hki0 : (-1:ℤ)< k := by exact_mod_cast hklo
        have hki1 : k<(1:ℤ) := by exact_mod_cast hkhi
        have hkzero : k=0 := by omega
        subst k
        norm_num at hk
        have hij : i.val< j.val+1 := by
          have hh : (i.val:ℝ)<(j.val:ℝ)+1 := by linarith [u.property.2]
          exact_mod_cast hh
        have hji : j.val< i.val+1 := by
          have hh : (j.val:ℝ)<(i.val:ℝ)+1 := by linarith [u.property.1]
          exact_mod_cast hh
        exact Fin.ext (by omega)
    have hSectorSameEdgeIndex (i j : Fin n) (y v : unitInterval)
        (hy0 : 0<(y:ℝ)) (hy1 : (y:ℝ)<1)
        (he : sector i 1 y=sector j 1 v) : i=j := by
      obtain ⟨hy,hh⟩ := (hKernel i j 1 1 y v).mp he
      rcases hh with hp|hp|⟨k,hk⟩
      · linarith
      · linarith
      · have hin : (i.val:ℝ)<n := by exact_mod_cast i.isLt
        have hjn : (j.val:ℝ)<n := by exact_mod_cast j.isLt
        have hi0 : (0:ℝ)≤ i.val := by positivity
        have hj0 : (0:ℝ)≤ j.val := by positivity
        have hnpos : (0:ℝ)< n := by exact_mod_cast (show 0<n by omega)
        have hklo : (-1:ℝ)< (k:ℝ) := by norm_num at hk; nlinarith
        have hkhi : (k:ℝ)<1 := by norm_num at hk; nlinarith
        have hki0 : (-1:ℤ)< k := by exact_mod_cast hklo
        have hki1 : k<(1:ℤ) := by exact_mod_cast hkhi
        have hkzero : k=0 := by omega
        subst k
        norm_num at hk
        exact Fin.ext hk
    have hDiamondInteriorIndex (i j : Fin n) (z w : D)
        (hz : gauge z.val<1) (he : lune i z=lune j w) : i=j := by
      have habs : |z.val.re|+|z.val.im|<1 := hz
      have him : |z.val.im|<1 := by linarith [abs_nonneg z.val.re]
      have hden : 0<1-|z.val.im| := by linarith
      have hr : -(1-|z.val.im|)< z.val.re ∧ z.val.re<1-|z.val.im| :=
        abs_lt.mp (by linarith)
      have hx0 : 0<(gridX z:ℝ) := by
        have hh : -1< z.val.re/(1-|z.val.im|) := (lt_div_iff₀ hden).mpr (by linarith [hr.1])
        dsimp [gridX]; linarith
      have hx1 : (gridX z:ℝ)<1 := by
        have hh : z.val.re/(1-|z.val.im|)<1 := (div_lt_iff₀ hden).mpr (by linarith [hr.2])
        dsimp [gridX]; linarith
      have hy : -1< z.val.im ∧ z.val.im<1 := abs_lt.mp him
      apply hSectorStrictIndex i j (gridX z) (gridX w) (gridY z) (gridY w) hx0 hx1
      · dsimp [gridY,lat]; linarith [hy.1]
      · dsimp [gridY,lat]; linarith [hy.2]
      · exact he
    have hDistinctLuneBoundary (i j : Fin n) (hij : i≠j) (z w : D)
        (he : lune i z=lune j w) : gauge z.val=1 ∧ gauge w.val=1 := by
      constructor
      · apply le_antisymm z.property
        by_contra hh
        have hl : gauge z.val<1 := lt_of_not_ge hh
        exact hij (hDiamondInteriorIndex i j z w hl he)
      · apply le_antisymm w.property
        by_contra hh
        have hl : gauge w.val<1 := lt_of_not_ge hh
        exact hij (hDiamondInteriorIndex j i w z hl he.symm).symm
    have hGridInj : Function.Injective (fun z : D => (gridX z,gridY z)) := by
      intro z w he
      have hy := congrArg (fun a : unitInterval × unitInterval => (a.2 : ℝ)) he
      have hym : z.val.im=w.val.im := by dsimp [gridY,lat] at hy; linarith
      have hx := congrArg (fun a : unitInterval × unitInterval => (a.1 : ℝ)) he
      dsimp [gridX] at hx
      rw [← hym] at hx
      apply Subtype.ext
      apply Complex.ext _ hym
      by_cases hd : 1-|z.val.im|=0
      · have hz : |z.val.re|+|z.val.im|≤1 := z.property
        have hw : |w.val.re|+|w.val.im|≤1 := w.property
        rw [← hym] at hw
        have hzr : z.val.re=0 := abs_eq_zero.mp (by linarith [abs_nonneg z.val.re])
        have hwr : w.val.re=0 := abs_eq_zero.mp (by linarith [abs_nonneg w.val.re])
        rw [hzr,hwr]
      · have hdiv : z.val.re/(1-|z.val.im|)=w.val.re/(1-|z.val.im|) := by linarith
        exact (div_left_inj' hd).mp hdiv
    have hPoleGrid (z : D) (h : (gridY z : ℝ)=0 ∨ (gridY z : ℝ)=1) :
        (gridX z : ℝ)=1/2 := by
      have hi : z.val.im= -1 ∨ z.val.im=1 := by
        dsimp [gridY,lat] at h
        rcases h with h|h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      rcases hi with hi|hi <;> simp [gridX,hi]
    have hLuneInj (i : Fin n) : Function.Injective (lune i) := by
      intro z w he
      rw [hAsSector,hAsSector] at he
      obtain ⟨hy,hzero|hone|⟨k,hk⟩⟩ := (hKernel i i (gridX z) (gridX w) (gridY z) (gridY w)).mp he
      · apply hGridInj
        apply Prod.ext _ hy
        apply Subtype.ext
        rw [hPoleGrid z (Or.inl hzero),hPoleGrid w (Or.inl (by rw [← hy]; exact hzero))]
      · apply hGridInj
        apply Prod.ext _ hy
        apply Subtype.ext
        rw [hPoleGrid z (Or.inr hone),hPoleGrid w (Or.inr (by rw [← hy]; exact hone))]
      · have hnreal : (2 : ℝ)≤ n := by exact_mod_cast hn2
        have hklo : (-1 : ℝ)<(k : ℝ) := by
          nlinarith [(gridX z).property.1,(gridX z).property.2,
            (gridX w).property.1,(gridX w).property.2]
        have hkhi : (k : ℝ)<1 := by
          nlinarith [(gridX z).property.1,(gridX z).property.2,
            (gridX w).property.1,(gridX w).property.2]
        have hklo' : (-1 : ℤ)< k := by exact_mod_cast hklo
        have hkhi' : k<(1 : ℤ) := by exact_mod_cast hkhi
        have hkzero : k=0 := by omega
        simp only [hkzero,Int.cast_zero,zero_mul,add_zero] at hk
        apply hGridInj
        exact Prod.ext (Subtype.ext (by linarith)) hy
    have hDcompact : IsCompact D := by
      have hc : IsClosed D := isClosed_le (by fun_prop) continuous_const
      apply (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hc
      intro z hz
      rw [Metric.mem_closedBall,dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans hz
    letI : CompactSpace D := isCompact_iff_compactSpace.mp hDcompact
    have hLuneEmbedding (i : Fin n) : Topology.IsClosedEmbedding (lune i) :=
      (hLuneCont i).isClosedEmbedding (hLuneInj i)
    have hSquareCoords (z : PolygonCell 5) :
        -1≤(d z).val.im ∧ (d z).val.im≤1 := by
      have hz : DiskSquare.maxAbs (d z).val≤1 := (d z).property
      exact abs_le.mp ((DiskSquare.abs_im_le_maxAbs _).trans hz)
    let pieceRadius (z : PolygonCell 5) : ℝ := (3+(d z).val.im)/4
    let pieceAngle (z : PolygonCell 5) : Circle :=
      Circle.exp (Real.pi*((d z).val.re+1)-Real.pi/2)
    have hPieceRadius (z : PolygonCell 5) : 1/2≤ pieceRadius z ∧ pieceRadius z≤1 := by
      dsimp [pieceRadius]
      constructor <;> linarith [(hSquareCoords z).1,(hSquareCoords z).2]
    let piecePoint (z : PolygonCell 5) : D :=
      ⟨diamond (pieceRadius z) (pieceAngle z),by
        change gauge (diamond (pieceRadius z) (pieceAngle z))≤1
        rw [hGaugeDiamond _ (by linarith [(hPieceRadius z).1])]
        exact (hPieceRadius z).2⟩
    have hPiecePointCont : Continuous piecePoint := by
      apply Continuous.subtype_mk
      change Continuous ((fun z : ℝ × Circle => diamond z.1 z.2) ∘
        (fun z : PolygonCell 5 => (pieceRadius z,pieceAngle z)))
      apply hDiamondCont.comp
      apply Continuous.prodMk
      · dsimp [pieceRadius]; fun_prop
      · exact Circle.exp.continuous.comp (by fun_prop)
    have hPiecePointShell (z : PolygonCell 5) : 1/2≤ gauge (piecePoint z).val := by
      dsimp only [piecePoint]
      rw [hGaugeDiamond _ (by linarith [(hPieceRadius z).1])]
      exact (hPieceRadius z).1
    have hOuterPointReflect (t : unitInterval) :
        (piecePoint (PolygonCell.side (4 : Fin 5) (unitInterval.symm t))).val =
          -starRingEnd ℂ ((piecePoint (PolygonCell.side (0 : Fin 5) t)).val) := by
      have hv := hOuterReflect t
      have hr : pieceRadius (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) =
          pieceRadius (PolygonCell.side (0 : Fin 5) t) := by
        dsimp [pieceRadius]; rw [hv]; simp
      have ha : (pieceAngle (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) : ℂ) =
          -starRingEnd ℂ (pieceAngle (PolygonCell.side (0 : Fin 5) t) : ℂ) := by
        dsimp only [pieceAngle]
        rw [hv]
        simp only [Complex.neg_re,Complex.conj_re]
        have he : Real.pi * (-((d (PolygonCell.side (0 : Fin 5) t)).val.re)+1)-Real.pi/2 =
            Real.pi-(Real.pi*(((d (PolygonCell.side (0 : Fin 5) t)).val.re)+1)-Real.pi/2) := by ring
        rw [he,sub_eq_add_neg,Circle.exp_add,Circle.exp_neg,Circle.coe_mul,
          Circle.coe_inv_eq_conj,Circle.coe_exp,Complex.exp_pi_mul_I]
        simp
      change diamond _ _ = -starRingEnd ℂ (diamond _ _)
      dsimp [diamond]
      rw [hr,ha]
      have hg (c : ℂ) : gauge (-starRingEnd ℂ c)=gauge c := by simp [gauge]
      rw [hg]
      simp
    have hOuterPointRadius (t : unitInterval) :
        gauge (piecePoint (PolygonCell.side (0 : Fin 5) t)).val=1 := by
      change gauge (diamond _ _)=1
      rw [hGaugeDiamond _ (by linarith [(hPieceRadius (PolygonCell.side (0 : Fin 5) t)).1])]
      dsimp [pieceRadius]
      rw [hOuterTop]
      norm_num
    have hOuterPointRe (t : unitInterval) :
        0≤(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.re := by
      let z := PolygonCell.side (0 : Fin 5) t
      have hz : -1≤(d z).val.re :=
        (abs_le.mp ((DiskSquare.abs_re_le_maxAbs _).trans (d z).property)).1
      have hc : 0≤(pieceAngle z : ℂ).re := by
        have hcos : 0≤ Real.cos (Real.pi*((d z).val.re+1)-Real.pi/2) := by
          apply Real.cos_nonneg_of_mem_Icc
          constructor <;> nlinarith [hOuterReNonpos t,Real.pi_pos]
        simpa only [pieceAngle,Circle.coe_exp,Complex.exp_re,Complex.mul_re,
          Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
          mul_zero,zero_mul,one_mul,mul_one,zero_add,add_zero,sub_self,Real.exp_zero] using hcos
      change 0≤(diamond (pieceRadius z) (pieceAngle z)).re
      dsimp only [diamond]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact mul_nonneg (div_nonneg (by linarith [(hPieceRadius z).1])
        (by dsimp [gauge]; positivity)) hc
    have hOuterDiamondStart : (piecePoint (PolygonCell.side (0 : Fin 5) 0)).val=Complex.I := by
      simp only [piecePoint,diamond,pieceRadius,pieceAngle,hOuterTop,hOuterReStart]
      norm_num [gauge,Circle.coe_exp,Complex.exp_re,Complex.exp_im]
    have hOuterDiamondEnd : (piecePoint (PolygonCell.side (0 : Fin 5) 1)).val= -Complex.I := by
      simp only [piecePoint,diamond,pieceRadius,pieceAngle,hOuterTop,hOuterReEnd]
      norm_num [gauge,Circle.coe_exp,Complex.exp_re,Complex.exp_im]
    let piece (i : Fin n) : PolygonCell 5 → ℂ × ℝ := lune i ∘ piecePoint
    have hPieceCont (i : Fin n) : Continuous (piece i) := (hLuneCont i).comp hPiecePointCont
    have hPieceEndpointLat (i : Fin n) :
        (piece i (PolygonCell.side (0 : Fin 5) 0)).2=1 ∧
        (piece i (PolygonCell.side (0 : Fin 5) 1)).2=0 := by
      constructor
      · change ((piecePoint (PolygonCell.side (0 : Fin 5) 0)).val.im+1)/2=1
        rw [hOuterDiamondStart]; norm_num
      · change ((piecePoint (PolygonCell.side (0 : Fin 5) 1)).val.im+1)/2=0
        rw [hOuterDiamondEnd]; norm_num
    have hPieceSamePole (i j : Fin n) (z w : PolygonCell 5)
        (hy : (piece i z).2=(piece j w).2)
        (hp : (piece i z).2=0 ∨ (piece i z).2=1) : piece i z=piece j w := by
      change lune i (piecePoint z)=lune j (piecePoint w)
      rw [hAsSector,hAsSector]
      apply (hKernel _ _ _ _ _ _).mpr
      have hy' : gridY (piecePoint z)=gridY (piecePoint w) := Subtype.ext hy
      refine ⟨hy',?_⟩
      rcases hp with hp|hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    have hReversedAdj (i : Fin n) :
        (Fin.rev i).val=(Fin.rev (finRotate n i)).val+1 ∨
          (Fin.rev (finRotate n i)).val+1=n ∧ (Fin.rev i).val=0 := by
      letI : NeZero n := ⟨by omega⟩
      have hnone : 1< n := by omega
      have hi : i.val< n := i.isLt
      simp only [Fin.rev,finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt hnone]
      by_cases hlast : i.val+1< n
      · rw [Nat.mod_eq_of_lt hlast]
        left; omega
      · have he : i.val+1=n := by omega
        rw [he,Nat.mod_self]
        right; constructor <;> omega
    have hOuterGrid (t : unitInterval) :
        gridY (piecePoint (PolygonCell.side (4 : Fin 5) (unitInterval.symm t))) =
          gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)) ∧
        ((gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)) : ℝ)=0 ∨
         (gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)) : ℝ)=1 ∨
         gridX (piecePoint (PolygonCell.side (0 : Fin 5) t))=1 ∧
         gridX (piecePoint (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)))=0) := by
      have hv := hOuterPointReflect t
      have hy : (piecePoint (PolygonCell.side (4 : Fin 5) (unitInterval.symm t))).val.im =
          (piecePoint (PolygonCell.side (0 : Fin 5) t)).val.im := by rw [hv]; simp
      refine ⟨Subtype.ext (by dsimp [gridY,lat]; rw [hy]),?_⟩
      have hg := hOuterPointRadius t
      have hp := hOuterPointRe t
      change |(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.re|+
          |(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.im|=1 at hg
      rw [abs_of_nonneg hp] at hg
      by_cases hd : 1-|(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.im|=0
      · have ha : |(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.im|=1 := by linarith
        rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp ha with ha|ha
        · right; left; dsimp [gridY,lat]; rw [ha]; norm_num
        · left; dsimp [gridY,lat]; rw [ha]; norm_num
      · right; right; constructor
        · apply Subtype.ext
          change (_/(1-|_|)+1)/2=1
          have hr : (piecePoint (PolygonCell.side (0 : Fin 5) t)).val.re =
              1-|(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.im| := by linarith
          rw [hr,div_self hd]; norm_num
        · apply Subtype.ext
          change (_/(1-|_|)+1)/2=0
          rw [hv]
          simp only [Complex.neg_re,Complex.conj_re,Complex.neg_im,Complex.conj_im,neg_neg]
          have hr : (piecePoint (PolygonCell.side (0 : Fin 5) t)).val.re =
              1-|(piecePoint (PolygonCell.side (0 : Fin 5) t)).val.im| := by linarith
          rw [hr,neg_div,div_self hd]; norm_num
    have hPieceRadialSeam (i : Fin n) (t : unitInterval) :
        piece (Fin.rev i) (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) =
          piece (Fin.rev (finRotate n i)) (PolygonCell.side (0 : Fin 5) t) := by
      change lune _ _=lune _ _
      rw [hAsSector,hAsSector]
      obtain ⟨hy,hh⟩ := hOuterGrid t
      rw [hy]
      rcases hh with hp|hp|⟨hx,hx'⟩
      · exact (hKernel _ _ _ _ _ _).mpr ⟨rfl,Or.inl hp⟩
      · exact (hKernel _ _ _ _ _ _).mpr ⟨rfl,Or.inr (Or.inl hp)⟩
      · rw [hx,hx']
        exact (hSectorAdjacent _ _ _ (hReversedAdj i)).symm
    have hPieceKernel (i : Fin n) (z w : PolygonCell 5) :
        piece i z=piece i w ↔ pieceRadius z=pieceRadius w ∧ pieceAngle z=pieceAngle w := by
      constructor
      · intro he
        have hd := congrArg Subtype.val (hLuneInj i he)
        exact hDiamondKernel _ _ (by linarith [(hPieceRadius z).1])
          (by linarith [(hPieceRadius w).1]) _ _ hd
      · rintro ⟨hr,hc⟩
        apply congrArg (lune i)
        apply Subtype.ext
        dsimp only [piecePoint]
        rw [hr,hc]
    have hPieceSquareKernel (i : Fin n) (z w : PolygonCell 5)
        (he : piece i z=piece i w) :
        (d z).val.im=(d w).val.im ∧ ((d z).val.re=(d w).val.re ∨
          ((d z).val.re= -1 ∧ (d w).val.re=1) ∨
          ((d z).val.re=1 ∧ (d w).val.re= -1)) := by
      obtain ⟨hr,ha⟩ := (hPieceKernel i z w).mp he
      have hy : (d z).val.im=(d w).val.im := by dsimp [pieceRadius] at hr; linarith
      have hz : -1≤(d z).val.re ∧ (d z).val.re≤1 :=
        abs_le.mp ((DiskSquare.abs_re_le_maxAbs _).trans (d z).property)
      have hw : -1≤(d w).val.re ∧ (d w).val.re≤1 :=
        abs_le.mp ((DiskSquare.abs_re_le_maxAbs _).trans (d w).property)
      obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp ha
      change Real.pi*((d z).val.re+1)-Real.pi/2 =
        Real.pi*((d w).val.re+1)-Real.pi/2+(k:ℝ)*(2*Real.pi) at hk
      have hx : (d z).val.re=(d w).val.re+2*(k:ℝ) := by nlinarith [Real.pi_pos]
      have hkLo : (-1:ℤ)≤ k := by
        have hh : (-1:ℝ)≤(k:ℝ) := by linarith [hz.1,hw.2]
        exact_mod_cast hh
      have hkHi : k≤(1:ℤ) := by
        have hh : (k:ℝ)≤1 := by linarith [hz.2,hw.1]
        exact_mod_cast hh
      have hkCases : k=0 ∨ k= -1 ∨ k=1 := by omega
      refine ⟨hy,?_⟩
      rcases hkCases with rfl | rfl | rfl
      · left; simpa using hx
      · right; left; norm_num at hx
        constructor <;> linarith [hz.1,hw.2]
      · right; right; norm_num at hx
        constructor <;> linarith [hz.2,hw.1]
    have hPieceDistinctOuter (i j : Fin n) (hij : i≠j) (z w : PolygonCell 5)
        (he : piece i z=piece j w) : (d z).val.im=1 ∧ (d w).val.im=1 := by
      obtain ⟨hz,hw⟩ := hDistinctLuneBoundary i j hij (piecePoint z) (piecePoint w) he
      have hrad (u : PolygonCell 5) (hu : gauge (piecePoint u).val=1) : (d u).val.im=1 := by
        change gauge (diamond (pieceRadius u) (pieceAngle u))=1 at hu
        rw [hGaugeDiamond _ (by linarith [(hPieceRadius u).1])] at hu
        dsimp [pieceRadius] at hu
        linarith
      exact ⟨hrad z hz,hrad w hw⟩
    have hPieceSameFiber (i : Fin n) (z w : PolygonCell 5)
        (he : piece i z=piece i w) : Relation.EqvGen
        (fun a b : PolygonCell 5 => ∃ t : unitInterval,
          a=PolygonCell.side (1 : Fin 5) t ∧
          b=PolygonCell.side (3 : Fin 5) (unitInterval.symm t)) z w := by
      obtain ⟨hy,hx⟩ := hPieceSquareKernel i z w he
      rcases hx with hx | ⟨hz,hw⟩ | ⟨hz,hw⟩
      · have hzw : z=w := d.injective (Subtype.ext (Complex.ext hx hy))
        rw [hzw]
        exact Relation.EqvGen.refl _
      · obtain ⟨t,hz,hw⟩ := hOppositeSideFiber z w hz hw hy
        exact Relation.EqvGen.rel _ _ ⟨t,hz,hw⟩
      · obtain ⟨t,hw,hz⟩ := hOppositeSideFiber w z hw hz hy.symm
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨t,hw,hz⟩)
    have hPieceSeam (i : Fin n) (t : unitInterval) :
        piece i (PolygonCell.side (1 : Fin 5) t)=
          piece i (PolygonCell.side (3 : Fin 5) (unitInterval.symm t)) := by
      apply (hPieceKernel i _ _).mpr
      have hSeamVal := hSeam t
      have him : (d (PolygonCell.side (3 : Fin 5) (unitInterval.symm t))).val.im =
          (d (PolygonCell.side (1 : Fin 5) t)).val.im := by rw [hSeamVal]; simp
      have hr : pieceRadius (PolygonCell.side (1 : Fin 5) t)=
          pieceRadius (PolygonCell.side (3 : Fin 5) (unitInterval.symm t)) := by
        dsimp [pieceRadius]; rw [him]
      refine ⟨hr,Subtype.ext ?_⟩
      have hc := hStripSeam t
      change ((pieceRadius (PolygonCell.side (1 : Fin 5) t) : ℝ):ℂ)*
        (pieceAngle (PolygonCell.side (1 : Fin 5) t) : ℂ) =
        ((pieceRadius (PolygonCell.side (3 : Fin 5) (unitInterval.symm t)) : ℝ):ℂ)*
        (pieceAngle (PolygonCell.side (3 : Fin 5) (unitInterval.symm t)) : ℂ) at hc
      rw [← hr] at hc
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
        (by linarith [(hPieceRadius (PolygonCell.side (1 : Fin 5) t)).1])) hc
    let proj (z : ℂ × ℝ) : ℝ × ℝ :=
      (z.1.im/(1/2-z.1.re),(z.2-1/2)/(1/2-z.1.re))
    have hProjInj (z w : ℂ × ℝ)
        (hz : z.1.re^2+z.1.im^2+(z.2-1/2)^2=1/4)
        (hw : w.1.re^2+w.1.im^2+(w.2-1/2)^2=1/4)
        (hdz : 1/2-z.1.re ≠ 0) (hdw : 1/2-w.1.re ≠ 0)
        (he : proj z=proj w) : z=w := by
      let A := 1/2-z.1.re
      let B := 1/2-w.1.re
      have hA : A≠0 := hdz
      have hB : B≠0 := hdw
      have hy : z.1.im*B=w.1.im*A := by
        exact (div_eq_div_iff hA hB).mp (congrArg Prod.fst he)
      have ht : (z.2-1/2)*B=(w.2-1/2)*A := by
        exact (div_eq_div_iff hA hB).mp (congrArg Prod.snd he)
      have hz' : z.1.im^2+(z.2-1/2)^2=A-A^2 := by dsimp [A]; nlinarith [hz]
      have hw' : w.1.im^2+(w.2-1/2)^2=B-B^2 := by dsimp [B]; nlinarith [hw]
      have hysq := congrArg (fun r : ℝ => r^2) hy
      have htsq := congrArg (fun r : ℝ => r^2) ht
      have hsum : (A-A^2)*B^2=(B-B^2)*A^2 := by
        calc
          _ = (z.1.im^2+(z.2-1/2)^2)*B^2 := by rw [hz']
          _ = (w.1.im^2+(w.2-1/2)^2)*A^2 := by nlinarith [hysq,htsq]
          _ = _ := by rw [hw']
      have hf : A*B*(B-A)=0 := by nlinarith [hsum]
      have hAB : A=B := by
        have hd := (mul_eq_zero.mp hf).resolve_left (mul_ne_zero hA hB)
        linarith
      have hre : z.1.re=w.1.re := by dsimp [A,B] at hAB; linarith
      have him : z.1.im=w.1.im := by
        rw [hAB] at hy
        exact mul_right_cancel₀ hB hy
      have hlat : z.2=w.2 := by
        rw [hAB] at ht
        have hh := mul_right_cancel₀ hB ht
        linarith
      exact Prod.ext (Complex.ext (by simpa using hre) (by simpa using him)) hlat
    let SphereCut := {z : ℂ × ℝ // z.1.re^2+z.1.im^2+(z.2-1/2)^2=1/4 ∧
      1/2-z.1.re ≠ 0}
    have hProjectionCont : Continuous (fun z : SphereCut => proj z.val) := by
      apply Continuous.prodMk
      · exact (Complex.continuous_im.comp (continuous_fst.comp continuous_subtype_val)).div
          (continuous_const.sub (Complex.continuous_re.comp
            (continuous_fst.comp continuous_subtype_val))) (fun z => z.property.2)
      · exact ((continuous_snd.comp continuous_subtype_val).sub continuous_const).div
          (continuous_const.sub (Complex.continuous_re.comp
            (continuous_fst.comp continuous_subtype_val))) (fun z => z.property.2)
    have hProjectionInjective : Function.Injective (fun z : SphereCut => proj z.val) := by
      intro z w he
      exact Subtype.ext (hProjInj z.val w.val z.property.1 w.property.1
        z.property.2 w.property.2 he)
    have hSectorSphere (i : Fin n) (x y : unitInterval) :
        (sector i x y).1.re^2+(sector i x y).1.im^2+((sector i x y).2-1/2)^2=1/4 := by
      have hh := hSphere i x y
      rw [Complex.sq_norm,Complex.normSq_apply] at hh
      nlinarith [hh]
    have hPieceSphere (i : Fin n) (z : PolygonCell 5) :
        (piece i z).1.re^2+(piece i z).1.im^2+((piece i z).2-1/2)^2=1/4 := by
      change (lune i (piecePoint z)).1.re^2+(lune i (piecePoint z)).1.im^2+
        ((lune i (piecePoint z)).2-1/2)^2=1/4
      rw [hAsSector]
      exact hSectorSphere _ _ _
    let mid : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
    let cutCenter : ℂ × ℝ := sector (⟨0,by omega⟩ : Fin n) mid mid
    have hCutCenterOmitted (i : Fin n) (z : PolygonCell 5) : piece i z≠cutCenter := by
      intro he
      rw [show piece i z=sector i (gridX (piecePoint z)) (gridY (piecePoint z)) from hAsSector _ _] at he
      obtain ⟨hy,hzero|hone|⟨k,hk⟩⟩ :=
        (hKernel i (⟨0,by omega⟩ : Fin n) (gridX (piecePoint z)) mid
          (gridY (piecePoint z)) mid).mp he
      · have hh : (gridY (piecePoint z) : ℝ)=1/2 := by simpa [mid] using congrArg Subtype.val hy
        norm_num at hh
        linarith
      · have hh : (gridY (piecePoint z) : ℝ)=1/2 := by simpa [mid] using congrArg Subtype.val hy
        norm_num at hh
        linarith
      · have hlat : (piecePoint z).val.im=0 := by
          have hh := by simpa [mid] using congrArg Subtype.val hy
          dsimp [gridY,lat,mid] at hh
          norm_num at hh
          linarith
        have hi : (i.val : ℝ)+1≤ n := by exact_mod_cast i.isLt
        have hinon := Nat.cast_nonneg (α:=ℝ) i.val
        have hnreal : (2 : ℝ)≤ n := by exact_mod_cast hn2
        norm_num [mid] at hk
        have hklo : (-1 : ℝ)<(k : ℝ) := by
          nlinarith [(gridX (piecePoint z)).property.1,(gridX (piecePoint z)).property.2]
        have hkhi : (k : ℝ)<1 := by
          nlinarith [(gridX (piecePoint z)).property.1,(gridX (piecePoint z)).property.2]
        have hklo' : (-1 : ℤ)< k := by exact_mod_cast hklo
        have hkhi' : k<(1 : ℤ) := by exact_mod_cast hkhi
        have hkzero : k=0 := by omega
        simp only [hkzero,Int.cast_zero,zero_mul,add_zero] at hk
        have hi0 : (i.val : ℝ)=0 := by
          have hixhi : (i.val : ℝ)<1 := by nlinarith [(gridX (piecePoint z)).property.1]
          have hixhi' : i.val<1 := by exact_mod_cast hixhi
          have hii : i.val=0 := by omega
          simp [hii]
        have hx : (gridX (piecePoint z) : ℝ)=1/2 := by linarith
        have hreal : (piecePoint z).val.re=0 := by
          dsimp [gridX] at hx
          rw [hlat] at hx
          norm_num at hx
          linarith
        have hshell := hPiecePointShell z
        dsimp [gauge] at hshell
        rw [hreal,hlat] at hshell
        norm_num at hshell
    let centerDir : Circle := Real.fourierChar ((1/2)/(n : ℝ))
    let rotateSphere (z : ℂ × ℝ) : ℂ × ℝ := ((centerDir⁻¹ : Circle)*z.1,z.2)
    have hRotateCont : Continuous rotateSphere := by fun_prop
    have hRotateInj : Function.Injective rotateSphere := by
      intro z w he
      apply Prod.ext
      · exact mul_left_cancel₀ (centerDir⁻¹).coe_ne_zero (congrArg Prod.fst he)
      · simpa only [rotateSphere] using congrArg Prod.snd he
    have hRotateCenter : rotateSphere cutCenter=((1/2 : ℂ),(1/2 : ℝ)) := by
      apply Prod.ext
      · dsimp only [rotateSphere,cutCenter,sector,mid]
        norm_num only [Fin.val_zero,Nat.cast_zero,zero_add]
        change ((centerDir⁻¹ : Circle) : ℂ)*(((1/2 : ℝ) : ℂ)*(centerDir : ℂ))=1/2
        calc
          _ = ((1/2 : ℝ) : ℂ)*(((centerDir⁻¹ : Circle) : ℂ)*(centerDir : ℂ)) := by ring
          _ = _ := by rw [← Circle.coe_mul,inv_mul_cancel,Circle.coe_one,mul_one]; norm_num
      · rfl
    have hRotateSphere (z : ℂ × ℝ)
        (hz : z.1.re^2+z.1.im^2+(z.2-1/2)^2=1/4) :
        (rotateSphere z).1.re^2+(rotateSphere z).1.im^2+
          ((rotateSphere z).2-1/2)^2=1/4 := by
      have hn : ‖(rotateSphere z).1‖=‖z.1‖ := by simp [rotateSphere,norm_mul]
      have he := congrArg (fun x : ℝ => x^2) hn
      rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply] at he
      change (rotateSphere z).1.re^2+(rotateSphere z).1.im^2+(z.2-1/2)^2=1/4
      nlinarith [hz,he]
    have hRotateDenominator (q : ℂ × ℝ)
        (hq : q.1.re^2+q.1.im^2+(q.2-1/2)^2=1/4) (havoid : q≠cutCenter) :
        1/2-(rotateSphere q).1.re≠0 := by
      intro hzero
      have hs := hRotateSphere q hq
      have hre : (rotateSphere q).1.re=1/2 := by linarith
      rw [hre] at hs
      have him : (rotateSphere q).1.im=0 := by nlinarith [sq_nonneg ((rotateSphere q).2-1/2)]
      have hlat : (rotateSphere q).2=1/2 := by nlinarith [sq_nonneg ((rotateSphere q).1.im)]
      have he : rotateSphere q=rotateSphere cutCenter := by
        rw [hRotateCenter]
        exact Prod.ext (Complex.ext (by simpa using hre) (by simpa using him)) hlat
      exact havoid (hRotateInj he)
    have hPieceDenominator (i : Fin n) (z : PolygonCell 5) :
        1/2-(rotateSphere (piece i z)).1.re≠0 :=
      hRotateDenominator _ (hPieceSphere i z) (hCutCenterOmitted i z)
    let planePiece (i : Fin n) (z : PolygonCell 5) : ℝ × ℝ := proj (rotateSphere (piece i z))
    have hPlanePieceCont (i : Fin n) : Continuous (planePiece i) := by
      let toCut (z : PolygonCell 5) : SphereCut :=
        ⟨rotateSphere (piece i z),hRotateSphere _ (hPieceSphere i z),hPieceDenominator i z⟩
      have hc : Continuous toCut := (hRotateCont.comp (hPieceCont i)).subtype_mk _
      exact hProjectionCont.comp hc
    have hPlanePieceKernel (i : Fin n) (z w : PolygonCell 5) :
        planePiece i z=planePiece i w ↔ pieceRadius z=pieceRadius w ∧ pieceAngle z=pieceAngle w := by
      constructor
      · intro he
        apply (hPieceKernel i z w).mp
        apply hRotateInj
        exact hProjInj _ _ (hRotateSphere _ (hPieceSphere i z))
          (hRotateSphere _ (hPieceSphere i w)) (hPieceDenominator i z)
          (hPieceDenominator i w) he
      · intro he
        exact congrArg (proj ∘ rotateSphere) ((hPieceKernel i z w).mpr he)
    let weightsFan : List ℕ := [3,1,1,1,3]
    have hwFan : ∀ w∈weightsFan,0< w := by simp [weightsFan]
    have hneFan : weightsFan≠[] := by simp [weightsFan]
    let ew := WeightedCircle.circleHomeomorph weightsFan hwFan hneFan
    let triChart : PolygonCell 5 ≃ₜ TriangleCell.StandardTriangle :=
      (PolygonCell.radialHomeomorph (n:=5) (m:=3) ew).trans TriangleCell.cellHomeomorph
    have hFanAngle (i : Fin 5) (t : unitInterval) :
        ew (Circle.exp (PolygonCell.sideAngle i t)) =
          Circle.exp (2*Real.pi/9*
            (((weightsFan.take i.val).sum : ℕ)+(weightsFan[i.val]'(by simpa [weightsFan] using i.isLt) : ℝ)*(t : ℝ))) := by
      have he : PolygonCell.sideAngle i t =
          2*Real.pi/(weightsFan.length : ℝ)*((i.val : ℝ)+(t : ℝ)) := by
        simp [PolygonCell.sideAngle,weightsFan]; ring
      rw [he]
      exact WeightedCircle.circleHomeomorph_exp_index_add' weightsFan hwFan hneFan
        (⟨i.val,by simpa [weightsFan] using i.isLt⟩ : Fin weightsFan.length) t
    have hMiddleTriangle (k : Fin 3) (t : unitInterval) :
        triChart (PolygonCell.side (⟨k.val+1,by omega⟩ : Fin 5) t) =
        TriangleCell.cellHomeomorph (PolygonCell.side (1 : Fin 3)
          ⟨((k.val : ℝ)+(t : ℝ))/3, by
            have hk : (k.val : ℝ)≤2 := by exact_mod_cast (show k.val≤2 by omega)
            constructor <;> linarith [t.property.1,t.property.2,Nat.cast_nonneg (α:=ℝ) k.val]⟩) := by
      dsimp only [triChart,Homeomorph.trans_apply]
      apply congrArg TriangleCell.cellHomeomorph
      change PolygonCell.radialHomeomorph ew
        (PolygonCell.ofCircle 5 (Circle.exp (PolygonCell.sideAngle ⟨k.val+1,by omega⟩ t))) = _
      rw [PolygonCell.radialHomeomorph_ofCircle,hFanAngle]
      apply congrArg (PolygonCell.ofCircle 3)
      congr 1
      fin_cases k <;> norm_num [weightsFan,PolygonCell.sideAngle] <;> ring
    have hFirstTriangle (t : unitInterval) :
        triChart (PolygonCell.side (0 : Fin 5) t)=
          TriangleCell.cellHomeomorph (PolygonCell.side (0 : Fin 3) t) := by
      dsimp only [triChart,Homeomorph.trans_apply]
      apply congrArg TriangleCell.cellHomeomorph
      change PolygonCell.radialHomeomorph ew
        (PolygonCell.ofCircle 5 (Circle.exp (PolygonCell.sideAngle 0 t))) = _
      rw [PolygonCell.radialHomeomorph_ofCircle,hFanAngle]
      apply congrArg (PolygonCell.ofCircle 3)
      congr 1
      norm_num [weightsFan,PolygonCell.sideAngle]
      ring
    have hLastTriangle (t : unitInterval) :
        triChart (PolygonCell.side (4 : Fin 5) t)=
          TriangleCell.cellHomeomorph (PolygonCell.side (2 : Fin 3) t) := by
      dsimp only [triChart,Homeomorph.trans_apply]
      apply congrArg TriangleCell.cellHomeomorph
      change PolygonCell.radialHomeomorph ew
        (PolygonCell.ofCircle 5 (Circle.exp (PolygonCell.sideAngle 4 t))) = _
      rw [PolygonCell.radialHomeomorph_ofCircle,hFanAngle]
      apply congrArg (PolygonCell.ofCircle 3)
      congr 1
      norm_num [weightsFan,PolygonCell.sideAngle]
      ring
    let T := {z : ℝ × ℝ | 0≤ z.1 ∧ 0≤ z.2 ∧ z.1+z.2≤1}
    let rad (z : T) : ℝ := z.val.1+z.val.2
    let frac (z : T) : ℝ := z.val.2/rad z
    have hRad (z : T) : 0≤ rad z ∧ rad z≤1 := ⟨add_nonneg z.property.1 z.property.2.1,z.property.2.2⟩
    have hFrac (z : T) : 0≤ frac z ∧ frac z≤1 := by
      by_cases hr : rad z=0
      · simp [frac,hr]
      · have hp := lt_of_le_of_ne (hRad z).1 (Ne.symm hr)
        exact ⟨div_nonneg z.property.2.1 hp.le,
          (div_le_iff₀ hp).mpr (by dsimp [rad]; linarith [z.property.1])⟩
    let fan (i : Fin n) (z : T) : ℂ :=
      ((rad z : ℝ):ℂ)*(Real.fourierChar (-((i.val : ℝ)+frac z)/(n : ℝ)) : ℂ)
    have hFanNorm (i : Fin n) (z : T) : ‖fan i z‖=rad z := by
      simp only [fan,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (hRad z).1]
    have hRadCont : Continuous rad := by fun_prop
    have hFanCont (i : Fin n) : Continuous (fan i) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      by_cases hr : rad z=0
      · have hzero : fan i z=0 := by simp [fan,hr]
        change Tendsto (fan i) (𝓝 z) (𝓝 (fan i z))
        rw [hzero,tendsto_zero_iff_norm_tendsto_zero]
        simp only [hFanNorm]
        simpa [hr] using (hRadCont.continuousAt (x:=z)).tendsto
      · have hc : ContinuousAt frac z :=
          (continuous_snd.comp continuous_subtype_val).continuousAt.div hRadCont.continuousAt hr
        exact (Complex.continuous_ofReal.comp hRadCont).continuousAt.mul
          (continuous_subtype_val.continuousAt.comp
            (Real.continuous_fourierChar.continuousAt.comp
              (((continuousAt_const.add hc).neg).div_const (n : ℝ))))
    have hFanInj (i : Fin n) : Function.Injective (fan i) := by
      intro z w he
      have hr : rad z=rad w := by
        have hh := congrArg norm he
        rwa [hFanNorm,hFanNorm] at hh
      by_cases hzero : rad z=0
      · have hz0 : z.val.1=0 ∧ z.val.2=0 := by
          dsimp [rad] at hzero
          constructor <;> linarith [z.property.1,z.property.2.1]
        have hwzero : rad w=0 := hr ▸ hzero
        have hw0 : w.val.1=0 ∧ w.val.2=0 := by
          dsimp [rad] at hwzero
          constructor <;> linarith [w.property.1,w.property.2.1]
        apply Subtype.ext
        apply Prod.ext <;> linarith [hz0.1,hz0.2,hw0.1,hw0.2]
      · have hnreal : (2 : ℝ)≤ n := by exact_mod_cast hn2
        have hnp : 0<(n : ℝ) := by linarith
        have hc : Real.fourierChar (-((i.val : ℝ)+frac z)/(n : ℝ)) =
            Real.fourierChar (-((i.val : ℝ)+frac w)/(n : ℝ)) := by
          apply Subtype.ext
          apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hzero)
          simpa only [fan,← hr] using he
        rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
        obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hc
        have hf : frac z=frac w-(k : ℝ)*(n : ℝ) := by
          have hh : -((i.val : ℝ)+frac z)/(n : ℝ) =
              -((i.val : ℝ)+frac w)/(n : ℝ)+(k : ℝ) := by nlinarith [Real.pi_pos]
          have hm := congrArg (fun t : ℝ => t*(n : ℝ)) hh
          rw [add_mul,div_mul_cancel₀ _ hnp.ne',div_mul_cancel₀ _ hnp.ne'] at hm
          linarith
        have hklo : (-1 : ℝ)<(k : ℝ) := by nlinarith [(hFrac z).1,(hFrac z).2,(hFrac w).1,(hFrac w).2]
        have hkhi : (k : ℝ)<1 := by nlinarith [(hFrac z).1,(hFrac z).2,(hFrac w).1,(hFrac w).2]
        have hklo' : (-1 : ℤ)< k := by exact_mod_cast hklo
        have hkhi' : k<(1 : ℤ) := by exact_mod_cast hkhi
        have hk0 : k=0 := by omega
        simp only [hk0,Int.cast_zero,zero_mul,sub_zero] at hf
        have hy : z.val.2=w.val.2 := by
          dsimp [frac] at hf
          rw [← hr] at hf
          exact (div_left_inj' hzero).mp hf
        apply Subtype.ext
        apply Prod.ext _ hy
        dsimp [rad] at hr
        linarith
    have hTriCoords (z : TriangleCell.StandardTriangle) :
        0≤ z.val 0 ∧ 0≤ z.val 1 ∧ z.val 0+z.val 1≤1 := by
      have hz : z.val∈convexHull ℝ (Set.range Moise.standardTriangleVertex) := by
        rw [← Moise.standardTrianglePlaneComplex_support]
        exact z.property
      apply (Moise.mem_standardTriangle_iff z.val).mp
      simpa [Moise.standardTriangleVertex,Moise.planePoint] using hz
    let toTriangleCoords (z : TriangleCell.StandardTriangle) : T :=
      ⟨(z.val 0,z.val 1),hTriCoords z⟩
    have hTriCoordsCont : Continuous toTriangleCoords := by
      apply Continuous.subtype_mk
      exact ((PiLp.continuous_apply (p:=2) (β:=fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val).prodMk
        ((PiLp.continuous_apply (p:=2) (β:=fun _ : Fin 2 => ℝ) 1).comp continuous_subtype_val)
    have hTriCoordsInj : Function.Injective toTriangleCoords := by
      intro z w he
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · exact congrArg (fun a : T => a.val.1) he
      · exact congrArg (fun a : T => a.val.2) he
    let rawCut (i : Fin n) (z : PolygonCell 5) : Complex.ClosedUnitDisc :=
      ⟨fan i (toTriangleCoords (triChart z)),by
        rw [Metric.mem_closedBall,dist_zero_right]
        rw [hFanNorm]
        exact (hRad _).2⟩
    have hRawCutCont (i : Fin n) : Continuous (rawCut i) :=
      ((hFanCont i).comp (hTriCoordsCont.comp triChart.continuous)).subtype_mk _
    have hRawCutInj (i : Fin n) : Function.Injective (rawCut i) := by
      intro z w he
      apply triChart.injective
      apply hTriCoordsInj
      exact hFanInj i (congrArg Subtype.val he)
    letI : CompactSpace (PolygonCell 5) :=
      (PolygonCell.closedUnitDiscHomeomorph 5).symm.compactSpace
    have hRawCutEmbedding (i : Fin n) : Topology.IsClosedEmbedding (rawCut i) :=
      (hRawCutCont i).isClosedEmbedding (hRawCutInj i)
    have hRawCutOldBoundary (i : Fin n) (k : Fin 3) (t : unitInterval) :
        rawCut i (PolygonCell.side (⟨k.val+1,by omega⟩ : Fin 5) t)=
          Complex.ClosedUnitDisc.bdyPtOfReal
            (-((3*(i.val : ℝ))+(k.val : ℝ)+(t : ℝ))/(3*(n : ℝ))) := by
      apply Subtype.ext
      change fan i (toTriangleCoords (triChart (PolygonCell.side ⟨k.val+1,by omega⟩ t))) = _
      rw [hMiddleTriangle,TriangleCell.cellHomeomorph_side]
      dsimp [fan,toTriangleCoords,rad,frac,Moise.standardTriangleVertex]
      simp only [Fin.isValue,finRotate_apply,Fin.val_one,Nat.reduceAdd,Nat.reduceMod]
      norm_num [AffineMap.lineMap_apply,AffineMap.lineMap,Moise.planePoint]
      apply congrArg (fun c : Circle => (c : ℂ))
      congr 1
      ring
    have hRawCutFirst (i : Fin n) (t : unitInterval) :
        (rawCut i (PolygonCell.side (0 : Fin 5) t)).val =
          ((t : ℝ):ℂ)*(Real.fourierChar (-(i.val : ℝ)/(n : ℝ)) : ℂ) := by
      change fan i (toTriangleCoords (triChart (PolygonCell.side 0 t))) = _
      rw [hFirstTriangle,TriangleCell.cellHomeomorph_side]
      dsimp [fan,toTriangleCoords,rad,frac,Moise.standardTriangleVertex]
      norm_num [AffineMap.lineMap_apply,AffineMap.lineMap,Moise.planePoint]
    have hRawCutLast (i : Fin n) (t : unitInterval) :
        (rawCut i (PolygonCell.side (4 : Fin 5) (unitInterval.symm t))).val =
          ((t : ℝ):ℂ)*(Real.fourierChar (-((i.val : ℝ)+1)/(n : ℝ)) : ℂ) := by
      change fan i (toTriangleCoords (triChart (PolygonCell.side 4 (unitInterval.symm t)))) = _
      rw [hLastTriangle,TriangleCell.cellHomeomorph_side]
      dsimp [fan,toTriangleCoords,rad,frac,Moise.standardTriangleVertex]
      norm_num [AffineMap.lineMap_apply,AffineMap.lineMap,Moise.planePoint,unitInterval.symm]
      by_cases ht : (t : ℝ)=0
      · simp [ht]
        right
        exact Subtype.ext ht
      · simp [ht]
    have hRawCutRadialSeam (i : Fin n) (t : unitInterval) :
        rawCut i (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) =
          rawCut (finRotate n i) (PolygonCell.side (0 : Fin 5) t) := by
      apply Subtype.ext
      rw [hRawCutLast,hRawCutFirst]
      congr 1
      apply congrArg (fun c : Circle => (c : ℂ))
      by_cases hi : i.val+1< n
      · have hnext : (finRotate n i).val=i.val+1 := by
          letI : NeZero n := ⟨by omega⟩
          rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1< n by omega),Nat.mod_eq_of_lt hi]
        rw [hnext]
        push_cast
        rfl
      · have hlast : i.val+1=n := by omega
        have hnext : (finRotate n i).val=0 := by
          letI : NeZero n := ⟨by omega⟩
          rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1< n by omega),hlast,Nat.mod_self]
        have he : (i.val : ℝ)+1=(n : ℝ) := by exact_mod_cast hlast
        have hnzero : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
        rw [hnext,he]
        rw [Real.fourierChar_apply',Real.fourierChar_apply']
        apply Circle.exp_eq_exp.mpr
        refine ⟨-1,?_⟩
        simp [hnzero]
    let R := Metric.closedBall ((0,0):ℝ×ℝ) 1
    have hCoords (z : R) : -1 ≤ z.val.1 ∧ z.val.1 ≤ 1 ∧ -1 ≤ z.val.2 ∧ z.val.2 ≤ 1 := by
      have hh : |z.val.1|≤1 ∧ |z.val.2|≤1 := by
        simpa only [R,Metric.mem_closedBall,Prod.dist_eq,Real.dist_eq,sub_zero,max_le_iff] using z.property
      exact ⟨(abs_le.mp hh.1).1,(abs_le.mp hh.1).2,(abs_le.mp hh.2).1,(abs_le.mp hh.2).2⟩
    let ann : R → ℂ := fun z => ((2+z.val.2 : ℝ):ℂ)*(Circle.exp (Real.pi*z.val.1):ℂ)
    have hAnnContinuous : Continuous ann := by
      exact (by fun_prop : Continuous (fun z : R => ((2+z.val.2 : ℝ):ℂ))).mul
        (continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop)))
    have hAnnNorm (z : R) : ‖ann z‖=2+z.val.2 := by
      have hh : 0 ≤ 2+z.val.2 := by linarith [(hCoords z).2.2.1]
      simp only [ann,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hh]
    have hAnnKernel (z w : R) : ann z=ann w ↔
        z.val.2=w.val.2 ∧ (z.val.1=w.val.1 ∨
          (z.val.1= -1 ∧ w.val.1=1) ∨ (z.val.1=1 ∧ w.val.1= -1)) := by
      constructor
      · intro he
        have heNorm := congrArg norm he
        rw [hAnnNorm,hAnnNorm] at heNorm
        have hy : z.val.2=w.val.2 := by linarith
        have hn : (2+z.val.2 : ℝ) ≠ 0 := by linarith [(hCoords z).2.2.1]
        have heCircle : Circle.exp (Real.pi*z.val.1)=Circle.exp (Real.pi*w.val.1) := by
          apply Subtype.ext
          apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hn)
          change ((2+z.val.2 : ℝ):ℂ)*(Circle.exp (Real.pi*z.val.1):ℂ)=
            ((2+z.val.2 : ℝ):ℂ)*(Circle.exp (Real.pi*w.val.1):ℂ)
          simpa only [ann,hy] using he
        obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp heCircle
        have hx : z.val.1=w.val.1+2*(k:ℝ) := by nlinarith [Real.pi_pos]
        have hkLo : (-1:ℤ)≤ k := by
          have hh : (-1:ℝ)≤(k:ℝ) := by linarith [(hCoords z).1,(hCoords w).2.1]
          exact_mod_cast hh
        have hkHi : k≤(1:ℤ) := by
          have hh : (k:ℝ)≤1 := by linarith [(hCoords z).2.1,(hCoords w).1]
          exact_mod_cast hh
        have hkCases : k=0 ∨ k= -1 ∨ k=1 := by omega
        refine ⟨hy,?_⟩
        rcases hkCases with rfl | rfl | rfl
        · left; simpa using hx
        · right; left; norm_num at hx
          constructor <;> linarith [(hCoords z).1,(hCoords w).2.1]
        · right; right; norm_num at hx
          constructor <;> linarith [(hCoords z).2.1,(hCoords w).1]
      · rintro ⟨hy,hx⟩
        have heCircle : Circle.exp (Real.pi*z.val.1)=Circle.exp (Real.pi*w.val.1) := by
          rcases hx with hx | ⟨hz,hw⟩ | ⟨hz,hw⟩
          · rw [hx]
          · apply Circle.exp_eq_exp.mpr
            refine ⟨-1,?_⟩
            rw [hz,hw]
            norm_num
            ring
          · apply Circle.exp_eq_exp.mpr
            refine ⟨1,?_⟩
            rw [hz,hw]
            norm_num
            ring
        change ((2+z.val.2 : ℝ):ℂ)*(Circle.exp (Real.pi*z.val.1):ℂ)=
          ((2+w.val.2 : ℝ):ℂ)*(Circle.exp (Real.pi*w.val.1):ℂ)
        rw [hy,heCircle]
    have hTwoBoundary (hnTwo : n=2) :
        ∃ F : Complex.ClosedUnitDisc → EuclideanSpace ℝ (Fin 2),
          Continuous F ∧
          (∀ z w, OrientableRel 0 n z w → F z=F w) ∧
          (∀ z w, F z=F w → Relation.EqvGen (OrientableRel 0 n) z w) := by
      subst n
      obtain ⟨d,hd⟩ : ∃ d : Complex.ClosedUnitDisc ≃ₜ R,
          ∀ t : unitInterval,
            (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(t:ℝ)/6))).val = (-1,-(t:ℝ)) ∧
            (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3-(t:ℝ))/6))).val = (1,-(t:ℝ)) ∧
            (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3+(t:ℝ))/6))).val = (1,(t:ℝ)) ∧
            (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(6-(t:ℝ))/6))).val = (-1,(t:ℝ)) := by
        exact actual_zero_handle_two_boundary_cut_rectangle
      let G : Complex.ClosedUnitDisc → ℂ := ann ∘ d
      have hGc : Continuous G := hAnnContinuous.comp d.continuous
      have hRespectG {z w : Complex.ClosedUnitDisc} (h : OrientableRel 0 2 z w) : G z=G w := by
        cases h with
        | a t i => exact Fin.elim0 i
        | b t i => exact Fin.elim0 i
        | c t i =>
          fin_cases i
          · apply (hAnnKernel _ _).mpr
            have h0 := (hd t).1
            have h1 := (hd t).2.1
            norm_num only [Fin.val_zero,Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,zero_add]
            change (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(t:ℝ)/6))).val.2=
              (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3-(t:ℝ))/6))).val.2 ∧ _
            rw [h0,h1]
            exact ⟨rfl,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
          · apply (hAnnKernel _ _).mpr
            have h0 := (hd t).2.2.1
            have h1 := (hd t).2.2.2
            norm_num only [Fin.val_one,Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,zero_add]
            change (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(3+(t:ℝ))/6))).val.2=
              (d (Complex.ClosedUnitDisc.bdyPtOfReal (-(6-(t:ℝ))/6))).val.2 ∧ _
            rw [h0,h1]
            exact ⟨rfl,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩
      have hSeam {z w : Complex.ClosedUnitDisc}
          (hz : (d z).val.1= -1) (hw : (d w).val.1=1) (hy : (d z).val.2=(d w).val.2) :
          Relation.EqvGen (OrientableRel 0 2) z w := by
        by_cases hs : (d z).val.2 ≤ 0
        · let t : unitInterval := ⟨-(d z).val.2,⟨by linarith,by linarith [(hCoords (d z)).2.2.1]⟩⟩
          have hzt : z=Complex.ClosedUnitDisc.bdyPtOfReal (-(t:ℝ)/6) := by
            apply d.injective
            apply Subtype.ext
            rw [(hd t).1]
            apply Prod.ext
            · exact hz
            · dsimp [t]; ring
          have hwt : w=Complex.ClosedUnitDisc.bdyPtOfReal (-(3-(t:ℝ))/6) := by
            apply d.injective
            apply Subtype.ext
            rw [(hd t).2.1]
            apply Prod.ext
            · exact hw
            · dsimp [t]; linarith
          rw [hzt,hwt]
          have hh := Relation.EqvGen.rel _ _ (OrientableRel.c (p:=0) (n:=2) t (0:Fin 2))
          norm_num at hh ⊢
          exact hh
        · let t : unitInterval := ⟨(d z).val.2,⟨(not_le.mp hs).le,(hCoords (d z)).2.2.2⟩⟩
          have hzt : z=Complex.ClosedUnitDisc.bdyPtOfReal (-(6-(t:ℝ))/6) := by
            apply d.injective
            apply Subtype.ext
            rw [(hd t).2.2.2]
            exact Prod.ext hz rfl
          have hwt : w=Complex.ClosedUnitDisc.bdyPtOfReal (-(3+(t:ℝ))/6) := by
            apply d.injective
            apply Subtype.ext
            rw [(hd t).2.2.1]
            exact Prod.ext hw hy.symm
          rw [hzt,hwt]
          have hh := Relation.EqvGen.symm _ _
            (Relation.EqvGen.rel _ _ (OrientableRel.c (p:=0) (n:=2) t (1:Fin 2)))
          norm_num at hh ⊢
          exact hh
      have hKernelG (z w : Complex.ClosedUnitDisc) (he : G z=G w) :
          Relation.EqvGen (OrientableRel 0 2) z w := by
        rcases (hAnnKernel (d z) (d w)).mp he with ⟨hy,hx⟩
        rcases hx with hx | ⟨hz,hw⟩ | ⟨hz,hw⟩
        · have he' : z=w := d.injective (Subtype.ext (Prod.ext hx hy))
          rw [he']
          exact Relation.EqvGen.refl _
        · exact hSeam hz hw hy
        · exact (hSeam hw hz hy.symm).symm
      let e := Complex.orthonormalBasisOneI.repr
      refine ⟨e ∘ G,e.continuous.comp hGc,?_,?_⟩
      · intro z w h
        exact congrArg e (hRespectG h)
      · intro z w h
        exact hKernelG z w (e.injective h)
    obtain ⟨F,hFc,hRespect,hKernel⟩ :
        ∃ F : Complex.ClosedUnitDisc → EuclideanSpace ℝ (Fin 2),
          Continuous F ∧
          (∀ z w, OrientableRel 0 n z w → F z=F w) ∧
          (∀ z w, F z=F w → Relation.EqvGen (OrientableRel 0 n) z w) := by
      by_cases hnTwo : n=2
      · exact hTwoBoundary hnTwo
      · have hnThree : 3 ≤ n := by omega
        obtain ⟨fanCut,hFanCutEmbedding,hFanCover,hFanSeams,hFanBoundary,hFanFibers⟩ :=
          actual_zero_handle_boundary_disk_fan n hnThree
        have hFanPairedSeam (i : Fin n) (t : unitInterval) :
            Relation.EqvGen (OrientableRel 0 n)
              (fanCut i (PolygonCell.side (1 : Fin 5) t))
              (fanCut i (PolygonCell.side (3 : Fin 5) (unitInterval.symm t))) := by
          have h0 := hFanBoundary i (0 : Fin 3) t
          have h2 := hFanBoundary i (2 : Fin 3) (unitInterval.symm t)
          norm_num at h0 h2
          have hi0 : (⟨1,by decide⟩ : Fin 5)=(1 : Fin 5) := by decide
          have hi2 : (⟨3,by decide⟩ : Fin 5)=(3 : Fin 5) := by decide
          try rw [hi0] at h0
          try rw [hi2] at h2
          rw [h0,h2]
          have hh := Relation.EqvGen.rel _ _ (OrientableRel.c (p:=0) (n:=n) t i)
          convert hh using 1 <;> congr 1 <;>
            norm_num [unitInterval.symm] <;> ring
        have hFanEndpointStep (i : Fin n) (t : unitInterval) (ht : t=0 ∨ t=1) :
            Relation.EqvGen (OrientableRel 0 n)
              (fanCut i (PolygonCell.side (0 : Fin 5) t))
              (fanCut (finRotate n i) (PolygonCell.side (0 : Fin 5) t)) := by
          have hsym0 : unitInterval.symm (0 : unitInterval)=1 := by
            apply Subtype.ext; norm_num [unitInterval.symm]
          have hsym1 : unitInterval.symm (1 : unitInterval)=0 := by
            apply Subtype.ext; norm_num [unitInterval.symm]
          have hw : PolygonCell.side (4 : Fin 5) 1=PolygonCell.side (0 : Fin 5) 0 := by
            simpa using PolygonCell.side_one_eq_rotate_zero (4 : Fin 5)
          rcases ht with rfl|rfl
          · have h := hFanSeams i 0
            rw [hsym0,hw] at h
            rw [h]
            exact Relation.EqvGen.refl _
          · have h := hFanPairedSeam i 0
            have h01 : PolygonCell.side (0 : Fin 5) 1=PolygonCell.side (1 : Fin 5) 0 := by
              simpa using PolygonCell.side_one_eq_rotate_zero (0 : Fin 5)
            have h34 : PolygonCell.side (3 : Fin 5) 1=PolygonCell.side (4 : Fin 5) 0 := by
              simpa using PolygonCell.side_one_eq_rotate_zero (3 : Fin 5)
            rw [hsym0,←h01,h34] at h
            have hs := hFanSeams i 1
            rw [hsym1] at hs
            rwa [hs] at h
        have hFanEndpointAll (i j : Fin n) (t : unitInterval) (ht : t=0 ∨ t=1) :
            Relation.EqvGen (OrientableRel 0 n)
              (fanCut i (PolygonCell.side (0 : Fin 5) t))
              (fanCut j (PolygonCell.side (0 : Fin 5) t)) := by
          have hNext (a b : Fin n) (ha : a.val+1=b.val) : finRotate n a=b := by
            apply Fin.ext
            letI : NeZero n := ⟨by omega⟩
            rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<n by omega),
              ha,Nat.mod_eq_of_lt b.isLt]
          have hzero (j : Fin n) : Relation.EqvGen (OrientableRel 0 n)
              (fanCut ⟨0,by omega⟩ (PolygonCell.side (0 : Fin 5) t))
              (fanCut j (PolygonCell.side (0 : Fin 5) t)) := by
            induction hv : j.val generalizing j with
            | zero =>
              have hj : j=(⟨0,by omega⟩ : Fin n) := Fin.ext hv
              rw [hj]
              exact Relation.EqvGen.refl _
            | succ k ih =>
              let a : Fin n := ⟨k,by omega⟩
              have ha := ih a (show a.val=k from rfl)
              have hs := hFanEndpointStep a t ht
              rw [hNext a j (by dsimp [a]; omega)] at hs
              exact Relation.EqvGen.trans _ _ _ ha hs
          exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hzero i)) (hzero j)
        have hFanSameCellFiber (i : Fin n) (z w : PolygonCell 5)
            (he : piece (Fin.rev i) z=piece (Fin.rev i) w) :
            Relation.EqvGen (OrientableRel 0 n) (fanCut i z) (fanCut i w) := by
          have h := hPieceSameFiber (Fin.rev i) z w he
          clear he
          induction h with
          | rel a b h =>
            obtain ⟨t,rfl,rfl⟩ := h
            exact hFanPairedSeam i t
          | refl a => exact Relation.EqvGen.refl _
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
        have hFanPoleFiber (i j : Fin n) (z w : PolygonCell 5)
            (he : piece (Fin.rev i) z=piece (Fin.rev j) w)
            (hp : (piece (Fin.rev i) z).2=0 ∨ (piece (Fin.rev i) z).2=1) :
            Relation.EqvGen (OrientableRel 0 n) (fanCut i z) (fanCut j w) := by
          have hy := congrArg Prod.snd he
          have hwp : (piece (Fin.rev j) w).2=0 ∨ (piece (Fin.rev j) w).2=1 := by rwa [hy] at hp
          rcases hp with hp|hp
          · have hz := hFanSameCellFiber i z (PolygonCell.side (0 : Fin 5) 1)
              (hPieceSamePole _ _ _ _ (by rw [(hPieceEndpointLat _).2]; exact hp) (Or.inl hp))
            have hw := hFanSameCellFiber j w (PolygonCell.side (0 : Fin 5) 1)
              (hPieceSamePole _ _ _ _ (by rw [(hPieceEndpointLat _).2]; exact hy.symm.trans hp)
                (Or.inl (hy.symm.trans hp)))
            exact Relation.EqvGen.trans _ _ _ hz
              (Relation.EqvGen.trans _ _ _ (hFanEndpointAll i j 1 (Or.inr rfl))
                (Relation.EqvGen.symm _ _ hw))
          · have hz := hFanSameCellFiber i z (PolygonCell.side (0 : Fin 5) 0)
              (hPieceSamePole _ _ _ _ (by rw [(hPieceEndpointLat _).1]; exact hp) (Or.inr hp))
            have hw := hFanSameCellFiber j w (PolygonCell.side (0 : Fin 5) 0)
              (hPieceSamePole _ _ _ _ (by rw [(hPieceEndpointLat _).1]; exact hy.symm.trans hp)
                (Or.inr (hy.symm.trans hp)))
            exact Relation.EqvGen.trans _ _ _ hz
              (Relation.EqvGen.trans _ _ _ (hFanEndpointAll i j 0 (Or.inl rfl))
                (Relation.EqvGen.symm _ _ hw))
        have hFanOuterCanonical (i : Fin n) (z : PolygonCell 5)
            (hz : (d z).val.im=1) :
            ∃ (j : Fin n) (t : unitInterval),
              fanCut i z=fanCut j (PolygonCell.side (0 : Fin 5) t) ∧
              piece (Fin.rev i) z=piece (Fin.rev j) (PolygonCell.side (0 : Fin 5) t) := by
          by_cases hr : (d z).val.re≤0
          · obtain ⟨t,rfl⟩ := hOuterRightAll z hz hr
            exact ⟨i,t,rfl,rfl⟩
          · obtain ⟨t,rfl⟩ := hOuterLeftAll z hz (not_le.mp hr).le
            exact ⟨finRotate n i,t,hFanSeams i t,hPieceRadialSeam i t⟩
        have hFanFullFiber (i j : Fin n) (z w : PolygonCell 5)
            (he : piece (Fin.rev i) z=piece (Fin.rev j) w) :
            Relation.EqvGen (OrientableRel 0 n) (fanCut i z) (fanCut j w) := by
          by_cases hij : i=j
          · subst j; exact hFanSameCellFiber i z w he
          by_cases hp0 : (piece (Fin.rev i) z).2=0
          · exact hFanPoleFiber i j z w he (Or.inl hp0)
          by_cases hp1 : (piece (Fin.rev i) z).2=1
          · exact hFanPoleFiber i j z w he (Or.inr hp1)
          have hrev : Fin.rev i≠Fin.rev j := fun h => hij (Fin.rev_injective h)
          obtain ⟨hz,hw⟩ := hPieceDistinctOuter _ _ hrev z w he
          obtain ⟨a,t,hza,hzt⟩ := hFanOuterCanonical i z hz
          obtain ⟨b,u,hwb,hwu⟩ := hFanOuterCanonical j w hw
          have hab : piece (Fin.rev a) (PolygonCell.side (0 : Fin 5) t)=
              piece (Fin.rev b) (PolygonCell.side (0 : Fin 5) u) := hzt.symm.trans (he.trans hwu)
          have htlat : (gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)):ℝ)=
              (piece (Fin.rev i) z).2 := (congrArg Prod.snd hzt).symm
          have hulat : (gridY (piecePoint (PolygonCell.side (0 : Fin 5) u)):ℝ)=
              (piece (Fin.rev i) z).2 := (congrArg Prod.snd (he.trans hwu)).symm
          have hx (v : unitInterval)
              (hv : (gridY (piecePoint (PolygonCell.side (0 : Fin 5) v)):ℝ)=
                (piece (Fin.rev i) z).2) : gridX (piecePoint (PolygonCell.side (0 : Fin 5) v))=1 := by
            obtain ⟨_,hh⟩ := hOuterGrid v
            rcases hh with hh|hh|⟨hh,_⟩
            · exact False.elim (hp0 (hv.symm.trans hh))
            · exact False.elim (hp1 (hv.symm.trans hh))
            · exact hh
          have hxt := hx t htlat
          have hxu := hx u hulat
          have hy0 : 0<(gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)):ℝ) := by
            have hh := (hLat (piecePoint (PolygonCell.side (0 : Fin 5) t))).1
            change 0≤(gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)):ℝ) at hh
            rw [htlat] at hh ⊢
            exact lt_of_le_of_ne hh (Ne.symm hp0)
          have hy1 : (gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)):ℝ)<1 := by
            have hh := (hLat (piecePoint (PolygonCell.side (0 : Fin 5) t))).2
            change (gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)):ℝ)≤1 at hh
            rw [htlat] at hh ⊢
            exact lt_of_le_of_ne hh hp1
          have hsec : sector (Fin.rev a) 1 (gridY (piecePoint (PolygonCell.side (0 : Fin 5) t)))=
              sector (Fin.rev b) 1 (gridY (piecePoint (PolygonCell.side (0 : Fin 5) u))) := by
            change lune _ _=lune _ _ at hab
            rw [hAsSector,hAsSector,hxt,hxu] at hab
            exact hab
          have habIndex : a=b := Fin.rev_injective (hSectorSameEdgeIndex _ _ _ _ hy0 hy1 hsec)
          subst b
          rw [hza,hwb]
          exact hFanSameCellFiber a _ _ hab
        let E : Fin n × PolygonCell 5 → Complex.ClosedUnitDisc := fun u => fanCut u.1 u.2
        let P : Fin n × PolygonCell 5 → ℂ × ℝ := fun u => piece (Fin.rev u.1) u.2
        have hEc : Continuous E := continuous_prod_of_discrete_left.mpr
          (fun i => (hFanCutEmbedding i).continuous)
        have hPc : Continuous P := continuous_prod_of_discrete_left.mpr
          (fun i => hPieceCont (Fin.rev i))
        have hEs : Function.Surjective E := by
          rw [←Set.range_eq_univ]
          exact hFanCover
        have hEq : Topology.IsQuotientMap E := by
          apply IsClosedMap.isQuotientMap _ hEc hEs
          intro S hS
          exact (hS.isCompact.image hEc).isClosed
        have hPFiber (u v : Fin n × PolygonCell 5) (h : E u=E v) : P u=P v := by
          have hh := (hFanFibers u v).mp h
          clear h
          induction hh with
          | rel a b h =>
            obtain ⟨i,t,rfl,rfl⟩ := h
            exact hPieceRadialSeam i t
          | refl a => rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
        let pick : Complex.ClosedUnitDisc → Fin n × PolygonCell 5 :=
          fun z => Classical.choose (hEs z)
        have hPick (z : Complex.ClosedUnitDisc) : E (pick z)=z := Classical.choose_spec (hEs z)
        let assembled : Complex.ClosedUnitDisc → ℂ × ℝ := P ∘ pick
        have hAssembled (u : Fin n × PolygonCell 5) : assembled (E u)=P u := by
          exact hPFiber _ _ (hPick (E u))
        have hAssembledCont : Continuous assembled := hEq.continuous_iff.mpr (by
          convert hPc using 1
          funext u
          exact hAssembled u)
        have hAssembledSphere (z : Complex.ClosedUnitDisc) :
            (assembled z).1.re^2+(assembled z).1.im^2+((assembled z).2-1/2)^2=1/4 :=
          hPieceSphere (Fin.rev (pick z).1) (pick z).2
        have hAssembledOmit (z : Complex.ClosedUnitDisc) : assembled z≠cutCenter :=
          hCutCenterOmitted (Fin.rev (pick z).1) (pick z).2
        have hAssembledRel (z w : Complex.ClosedUnitDisc)
            (h : OrientableRel 0 n z w) : assembled z=assembled w := by
          cases h with
          | a t i => exact Fin.elim0 i
          | b t i => exact Fin.elim0 i
          | c t i =>
            have h0 := hFanBoundary i (0 : Fin 3) t
            have h2 := hFanBoundary i (2 : Fin 3) (unitInterval.symm t)
            norm_num at h0 h2
            have hi0 : (⟨1,by decide⟩ : Fin 5)=(1 : Fin 5) := by decide
            have hi2 : (⟨3,by decide⟩ : Fin 5)=(3 : Fin 5) := by decide
            try rw [hi0] at h0
            try rw [hi2] at h2
            have hp : assembled (fanCut i (PolygonCell.side (1 : Fin 5) t))=
                assembled (fanCut i (PolygonCell.side (3 : Fin 5) (unitInterval.symm t))) :=
              (hAssembled (i,PolygonCell.side (1 : Fin 5) t)).trans
                ((hPieceSeam (Fin.rev i) t).trans
                  (hAssembled (i,PolygonCell.side (3 : Fin 5) (unitInterval.symm t))).symm)
            rw [h0,h2] at hp
            convert hp using 1 <;> congr 2 <;>
              norm_num [unitInterval.symm] <;> ring
        obtain ⟨A,hAc,hARel,hAKernel,hASphere,hAOmit⟩ :
            ∃ A : Complex.ClosedUnitDisc → ℂ × ℝ,
              Continuous A ∧
              (∀ z w, OrientableRel 0 n z w → A z=A w) ∧
              (∀ z w, A z=A w → Relation.EqvGen (OrientableRel 0 n) z w) ∧
              (∀ z, (A z).1.re^2+(A z).1.im^2+((A z).2-1/2)^2=1/4) ∧
              (∀ z, A z≠cutCenter) := by
          refine ⟨assembled,hAssembledCont,hAssembledRel,?_,hAssembledSphere,hAssembledOmit⟩
          intro z w he
          have hh := hFanFullFiber (pick z).1 (pick w).1 (pick z).2 (pick w).2 he
          change Relation.EqvGen (OrientableRel 0 n) (E (pick z)) (E (pick w)) at hh
          simpa only [hPick] using hh
        let toCut (z : Complex.ClosedUnitDisc) : SphereCut :=
          ⟨rotateSphere (A z),hRotateSphere _ (hASphere z),
            hRotateDenominator _ (hASphere z) (hAOmit z)⟩
        have hToCut : Continuous toCut := (hRotateCont.comp hAc).subtype_mk _
        let G : Complex.ClosedUnitDisc → ℝ × ℝ := fun z => proj (rotateSphere (A z))
        have hGc : Continuous G := hProjectionCont.comp hToCut
        let e := Complex.orthonormalBasisOneI.repr
        let ce := Complex.equivRealProdCLM.symm
        refine ⟨e ∘ ce ∘ G,e.continuous.comp (ce.continuous.comp hGc),?_,?_⟩
        · intro z w hr
          exact congrArg (e ∘ ce ∘ proj ∘ rotateSphere) (hARel z w hr)
        · intro z w he
          apply hAKernel z w
          apply hRotateInj
          exact hProjInj _ _ (hRotateSphere _ (hASphere z))
            (hRotateSphere _ (hASphere w))
            (hRotateDenominator _ (hASphere z) (hAOmit z))
            (hRotateDenominator _ (hASphere w) (hAOmit w))
            (ce.injective (e.injective he))
    let f : Quot (OrientableRel 0 n) → EuclideanSpace ℝ (Fin 2) := Quot.lift F hRespect
    have hfc : Continuous f := continuous_quot_lift _ hFc
    have hfi : Function.Injective f := by
      intro x y he
      induction x using Quot.inductionOn with
      | _ z =>
        induction y using Quot.inductionOn with
        | _ w => exact Quot.eqvGen_sound (hKernel z w he)
    exact ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding⟩

end CurveComplex.Hyperbolic
