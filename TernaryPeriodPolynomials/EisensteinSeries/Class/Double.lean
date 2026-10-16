module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamParametricIntegral

@[expose] public section


/-!
# Iterated interval integrals over the unit square: smoothness and differentiation under the integral

(averaging
each coefficient over the compact fiber `Nℤ² \\ ℝ²`, "each invariant vector field has integral zero on a
derivative": the average is a cochain map).

For `f` smooth on `(U × ℝ) × ℝ` (`U` open in a finite-dimensional space), the iterated integral
`x ↦ ∫₀¹∫₀¹ f((x, a), b) db da` is smooth on `U` (`contDiffOn_iteratedIntegral`) and its derivative is the
iterated integral of the derivatives (`hasFDerivAt_iteratedIntegral`). Both follow from two applications of
`TernaryPoly.SmoothLocalDeRham.parameterIntegral_smooth` / `hasFDerivAt_parameterIntegral`.

Formalized by Claude Sonnet 5.5.
-/

open TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem sliceDomain_prod (U : Set E) :
    sliceDomain (((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) : Set ((E × ℝ) × ℝ))) =
      U ×ˢ (univ : Set ℝ) :=
  Set.ext fun _ => ⟨fun h => ⟨(h 0 ⟨le_refl _, zero_le_one⟩).1.1, trivial⟩,
    fun h _ _ => ⟨⟨h.1, trivial⟩, trivial⟩⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem sliceDomain_prod' (U : Set E) :
    sliceDomain ((U ×ˢ (univ : Set ℝ) : Set (E × ℝ))) = U :=
  Set.ext fun _ => ⟨fun h => (h 0 ⟨le_refl _, zero_le_one⟩).1, fun h _ _ => ⟨h, trivial⟩⟩

/-- **Smoothness of an iterated interval integral** over the unit square. -/
theorem contDiffOn_iteratedIntegral {U : Set E} (hU : IsOpen U) (f : (E × ℝ) × ℝ → G)
    (hf : ContDiffOn ℝ ∞ f ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (fun x => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, f ((x, a), b)) U := by
  have hD : IsOpen (((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) : Set ((E × ℝ) × ℝ))) :=
    (hU.prod isOpen_univ).prod isOpen_univ
  have h1 := parameterIntegral_smooth hD hf
  rw [sliceDomain_prod] at h1
  have hD' : IsOpen ((U ×ˢ (univ : Set ℝ) : Set (E × ℝ))) := hU.prod isOpen_univ
  have h2 := parameterIntegral_smooth hD' h1
  rw [sliceDomain_prod'] at h2
  exact h2

/-- The inclusion `x ↦ ((x, 0), 0)`. -/
def inl2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : E →L[ℝ] (E × ℝ) × ℝ :=
  (ContinuousLinearMap.inl ℝ (E × ℝ) ℝ).comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- **The derivative of an iterated interval integral is the iterated integral of the derivative.** -/
theorem hasFDerivAt_iteratedIntegral [CompleteSpace G] {U : Set E} (hU : IsOpen U) (f : (E × ℝ) × ℝ → G)
    (hf : ContDiffOn ℝ ∞ f ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ))) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, f ((y, a), b))
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, (fderiv ℝ f ((x, a), b)).comp (inl2 E)) x := by
  have hD : IsOpen (((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ) : Set ((E × ℝ) × ℝ))) :=
    (hU.prod isOpen_univ).prod isOpen_univ
  have hD' : IsOpen ((U ×ˢ (univ : Set ℝ) : Set (E × ℝ))) := hU.prod isOpen_univ
  have h1 := parameterIntegral_smooth hD hf
  rw [sliceDomain_prod] at h1
  -- the inner derivative
  have hin : ∀ q ∈ U ×ˢ (univ : Set ℝ),
      HasFDerivAt (fun p : E × ℝ => ∫ b in (0:ℝ)..1, f (p, b))
        (∫ b in (0:ℝ)..1, parameterDerivative f (q, b)) q := by
    intro q hq
    exact hasFDerivAt_parameterIntegral hD hf (by rw [sliceDomain_prod]; exact hq)
  have hout := hasFDerivAt_parameterIntegral hD' h1 (x := x) (by rw [sliceDomain_prod']; exact hx)
  convert hout using 1
  refine intervalIntegral.integral_congr fun a _ => ?_
  have hq : (x, a) ∈ U ×ˢ (univ : Set ℝ) := ⟨hx, trivial⟩
  have hfd := (hin (x, a) hq).fderiv
  have hint : IntervalIntegrable (fun b : ℝ => parameterDerivative f ((x, a), b)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    refine (parameterDerivative_smooth hD hf).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn fun b _ => ?_
    exact ⟨⟨hx, trivial⟩, trivial⟩
  let L : ((E × ℝ) →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) :=
    (ContinuousLinearMap.compL ℝ E (E × ℝ) G).flip (ContinuousLinearMap.inl ℝ E ℝ)
  have hL := L.intervalIntegral_comp_comm hint
  show _ = (fderiv ℝ (fun p : E × ℝ => ∫ b in (0:ℝ)..1, f (p, b)) (x, a)).comp
      (ContinuousLinearMap.inl ℝ E ℝ)
  rw [hfd]
  have e : (∫ b in (0:ℝ)..1, parameterDerivative f ((x, a), b)).comp (ContinuousLinearMap.inl ℝ E ℝ) =
      L (∫ b in (0:ℝ)..1, parameterDerivative f ((x, a), b)) := rfl
  rw [e, ← hL]
  refine intervalIntegral.integral_congr fun b _ => ?_
  rfl

end TernaryPeriodPolynomials.Argument.EisensteinClass
