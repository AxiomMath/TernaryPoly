module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.BoundedSchur

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def cuspPairAction (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    WithLp 2 (cusp.H × cusp.H) →L[ℂ] WithLp 2 (cusp.H × cusp.H) :=
  let equiv := WithLp.prodContinuousLinearEquiv 2 ℂ cusp.H cusp.H
  equiv.symm.toContinuousLinearMap.comp
    (((cuspUnitaryAction cusp matrix).toContinuousLinearMap.prodMap
      (cuspUnitaryAction cusp matrix).toContinuousLinearMap).comp equiv.toContinuousLinearMap)

noncomputable def cuspPairInclusion (cusp : CuspidalRepresentation) :
    cusp.H →L[ℂ] WithLp 2 (cusp.H × cusp.H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ cusp.H cusp.H).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ cusp.H cusp.H)

noncomputable def cuspPairFirst (cusp : CuspidalRepresentation) :
    WithLp 2 (cusp.H × cusp.H) →L[ℂ] cusp.H :=
  (ContinuousLinearMap.fst ℂ cusp.H cusp.H).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ cusp.H cusp.H).toContinuousLinearMap

noncomputable def cuspPairSecond (cusp : CuspidalRepresentation) :
    WithLp 2 (cusp.H × cusp.H) →L[ℂ] cusp.H :=
  (ContinuousLinearMap.snd ℂ cusp.H cusp.H).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ cusp.H cusp.H).toContinuousLinearMap

theorem cuspPairAction_apply (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (pair : WithLp 2 (cusp.H × cusp.H)) :
    (cuspPairAction cusp matrix pair).ofLp =
      (cusp.π matrix pair.ofLp.1, cusp.π matrix pair.ofLp.2) := rfl

theorem cuspPairAction_inv (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (pair : WithLp 2 (cusp.H × cusp.H)) :
    cuspPairAction cusp matrix (cuspPairAction cusp matrix⁻¹ pair) = pair := by
  apply WithLp.ofLp_injective
  simp only [cuspPairAction_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply, Prod.mk.eta]

theorem cuspPairAction_inner (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (first second : WithLp 2 (cusp.H × cusp.H)) :
    inner ℂ (cuspPairAction cusp matrix first) (cuspPairAction cusp matrix second) = inner ℂ first second := by
  simp only [WithLp.prod_inner_apply, cuspPairAction_apply]
  exact congrArg₂ (· + ·) ((cuspUnitaryAction cusp matrix).inner_map_map _ _)
    ((cuspUnitaryAction cusp matrix).inner_map_map _ _)

theorem cuspPairFirst_inner (cusp : CuspidalRepresentation)
    (pair : WithLp 2 (cusp.H × cusp.H)) (vector : cusp.H) :
    inner ℂ (cuspPairFirst cusp pair) vector = inner ℂ pair (cuspPairInclusion cusp vector) := by
  simp only [WithLp.prod_inner_apply]
  change inner ℂ pair.ofLp.1 vector = inner ℂ pair.ofLp.1 vector + inner ℂ pair.ofLp.2 0
  rw [inner_zero_right, add_zero]

theorem cuspPairInclusion_covariance (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (vector : cusp.H) :
    cuspPairInclusion cusp (cusp.π matrix vector) = cuspPairAction cusp matrix (cuspPairInclusion cusp vector) := by
  apply WithLp.ofLp_injective
  change (cusp.π matrix vector, 0) = (cusp.π matrix vector, cusp.π matrix 0)
  rw [map_zero]

theorem cuspPairInclusion_inner (cusp : CuspidalRepresentation)
    (vector : cusp.H) (pair : WithLp 2 (cusp.H × cusp.H)) :
    inner ℂ vector (cuspPairFirst cusp pair) = inner ℂ (cuspPairInclusion cusp vector) pair := by
  simp only [WithLp.prod_inner_apply]
  change inner ℂ vector pair.ofLp.1 = inner ℂ vector pair.ofLp.1 + inner ℂ 0 pair.ofLp.2
  rw [inner_zero_left, add_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
