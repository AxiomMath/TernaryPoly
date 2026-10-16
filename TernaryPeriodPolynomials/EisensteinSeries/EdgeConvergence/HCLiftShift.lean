module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Inputs
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersFlat
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliersXiSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FamilyCuspTaylor
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.LinearFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ParabolicInvariance

@[expose] public section


/-!
# The parameter shift of the flat family of a plane section

Original work by Claude Sonnet 5.5.

The flat family of a plane section `f` (the section at the cohomological point `s₀`) is
`Ξ^{s - s₀} f` (`SectionMultipliersFlat.linearFlatExtension_eq_xi`). Consequently its plane cusp
lift vector at the parameter `s` is the scalar multiple `Ξ(y)^{s - s₀}` of the vector at `s₀`
(`vector_shift`), and the orbit functions of the family at `s` are scalar multiples of the orbit
functions at `s₀` (`matrixOrbit_twistedAt`). We also allow an extra *weight*: a smooth real function
`τ` of the vertices, and consider the family `exp ((s - s₀) τ(vertices)) · Ξ^{s - s₀} f_vertices`
(`twistedAt`): a family of plane sections at the parameter `s`, with a smooth cusp lift
(`twistedAt_hasSmoothCuspLift`). Weight `0` is the flat family itself.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

/-- The logarithm of the plane height `Ξ`. -/
abbrev heightLog : AdelicGL → ℝ := SectionMultipliersXi.logXi

theorem heightLog_law : HeightLaw heightLog := SectionMultipliersXiSmooth.heightLaw

/-- Smoothness of a function of one coordinate of a tuple of real matrices. -/
theorem smooth_comp_coordinate {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (index : Fin k) (function : (Fin 1 → RealGL3) → E) (smooth : Smooth function) :
    Smooth (fun x : Fin k → RealGL3 => function (fun _ => x index)) := by
  have projection : ContDiff ℝ ⊤ (fun matrices : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      fun _ : Fin 1 => matrices index) :=
    contDiff_pi.mpr (fun _ => contDiff_apply ℝ _ index)
  have maps : Set.MapsTo (fun matrices : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      fun _ : Fin 1 => matrices index)
      {matrices | ∀ i, (matrices i).det ≠ 0} {matrices | ∀ i, (matrices i).det ≠ 0} := by
    intro matrices membership _
    exact membership index
  apply (smooth.comp projection.contDiffOn maps).congr
  intro matrices membership
  rfl

/-- Smoothness of a function of the first `k` vertices of a tuple of `k + 1` real matrices. -/
theorem smooth_comp_castSucc {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin k → RealGL3) → E) (smooth : Smooth function) :
    Smooth (fun x : Fin (k + 1) → RealGL3 => function (fun i => x i.castSucc)) := by
  have projection : ContDiff ℝ ⊤ (fun matrices : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ =>
      fun i : Fin k => matrices i.castSucc) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ _ i.castSucc)
  have maps : Set.MapsTo (fun matrices : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ =>
      fun i : Fin k => matrices i.castSucc)
      {matrices | ∀ i, (matrices i).det ≠ 0} {matrices | ∀ i, (matrices i).det ≠ 0} := by
    intro matrices membership i
    exact membership i.castSucc
  apply (smooth.comp projection.contDiffOn maps).congr
  intro matrices membership
  rfl

/-- The algebra behind the parameter shift: the Levi weights of `exp ((s - s₀) log Ξ)` and of the
normalized vector exponent cancel. -/
theorem shift_identity (degree : ℕ) (parameter : ℂ) (binary : BinaryAdelicGL) (y : AdelicGL)
    (value : ℂ) :
    normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane parameter) *
        (Complex.exp ((parameter - cohomologicalPoint) * (heightLog (planeLevi binary 1 * y) : ℂ)) *
          value) =
      Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ)) *
        (normPower (GeneralLinearGroup.det binary)
          (-binaryInductionExponent degree .plane cohomologicalPoint) * value) := by
  have exponent : binaryInductionExponent degree .plane parameter =
      binaryInductionExponent degree .plane cohomologicalPoint +
        (parameter - cohomologicalPoint) / 3 := by
    simp only [binaryInductionExponent, inductionExponent]
    ring
  have shift := SectionMultipliersFlat.normPower_shift (GeneralLinearGroup.det binary)
    (parameter - cohomologicalPoint) (binaryInductionExponent degree .plane cohomologicalPoint)
  rw [exponent, SectionMultipliersFlat.exp_levi_factor heightLog_law (parameter - cohomologicalPoint)
    binary 1 y, ParabolicInvariance.normPower_one]
  linear_combination
    (Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ)) * value) * shift

/-- The plane cusp lift vector of a section of the form `c · Ξ^{s - s₀} f` is the corresponding
multiple of the vector of `f`. -/
theorem vector_shift {degree : ℕ} (data : InducingData degree) (function extended : AdelicGL → ℂ)
    (scalar : ℂ) (original : IsInduced data .plane cohomologicalPoint function) (parameter : ℂ)
    (shifted : IsInduced data .plane parameter extended)
    (equation : ∀ y, extended y = scalar *
      (Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ)) * function y))
    (y : AdelicGL) :
    (CuspLift.vector data .plane parameter extended shifted y).val =
      (scalar * Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ))) •
        (CuspLift.vector data .plane cohomologicalPoint function original y).val := by
  have equality : CuspLift.vector data .plane parameter extended shifted y =
      (scalar * Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ))) •
        CuspLift.vector data .plane cohomologicalPoint function original y := by
    apply data.cusp.injective
    funext binary
    rw [CuspLift.realizes, map_smul, Pi.smul_apply, smul_eq_mul, CuspLift.realizes]
    simp only [binaryLevi]
    rw [equation (planeLevi binary 1 * y)]
    have core := shift_identity degree parameter binary y (function (planeLevi binary 1 * y))
    linear_combination scalar * core
  exact congrArg Subtype.val equality

section Families

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))

/-- The flat family, at the parameter `parameter`, of the plane sections `family vertices`. -/
def flatAt (parameter : ℂ) : (Fin arity → RealGL3) → AdelicGL → ℂ :=
  fun vertices =>
    EdgeInputs.flatFamily data holomorphic ⟨family vertices, induced vertices⟩ parameter

theorem flatAt_induced (parameter : ℂ) (vertices : Fin arity → RealGL3) :
    IsInduced data .plane parameter (flatAt data holomorphic family induced parameter vertices) :=
  (EdgeInputs.flatFamily_flat data holomorphic ⟨family vertices, induced vertices⟩).1 parameter

/-- The flat family of a plane section is `Ξ^{s - s₀}` times the section. -/
theorem flatAt_apply (parameter : ℂ) (vertices : Fin arity → RealGL3) (y : AdelicGL) :
    flatAt data holomorphic family induced parameter vertices y =
      Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ)) * family vertices y :=
  SectionMultipliersFlat.linearFlatExtension_eq_xi data holomorphic heightLog_law
    ⟨family vertices, induced vertices⟩ parameter y

variable (weight : (Fin arity → RealGL3) → ℝ)

/-- The flat family multiplied by `exp ((s - s₀) * weight vertices)`. -/
def twistedAt (parameter : ℂ) : (Fin arity → RealGL3) → AdelicGL → ℂ :=
  fun vertices argument =>
    Complex.exp ((parameter - cohomologicalPoint) * (weight vertices : ℂ)) *
      flatAt data holomorphic family induced parameter vertices argument

theorem twistedAt_induced (parameter : ℂ) (vertices : Fin arity → RealGL3) :
    IsInduced data .plane parameter
      (twistedAt data holomorphic family induced weight parameter vertices) :=
  LinearFamilies.induced_smul data .plane parameter
    (Complex.exp ((parameter - cohomologicalPoint) * (weight vertices : ℂ)))
    (flatAt data holomorphic family induced parameter vertices)
    (flatAt_induced data holomorphic family induced parameter vertices)

theorem twistedAt_apply (parameter : ℂ) (vertices : Fin arity → RealGL3) (y : AdelicGL) :
    twistedAt data holomorphic family induced weight parameter vertices y =
      Complex.exp ((parameter - cohomologicalPoint) * (weight vertices : ℂ)) *
        (Complex.exp ((parameter - cohomologicalPoint) * (heightLog y : ℂ)) *
          family vertices y) := by
  unfold twistedAt
  rw [flatAt_apply]

/-- The orbit function of the twisted family at the parameter `s` is a scalar multiple of the
orbit function of the family at the cohomological point. -/
theorem matrixOrbit_twistedAt (parameter : ℂ) (argument : AdelicGL)
    (matrices : SmoothJets.MatrixTuples 3 arity.succ) :
    FamilyCuspTaylor.matrixOrbit data .plane parameter
        (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter) argument matrices =
      (Complex.exp ((parameter - cohomologicalPoint) *
          (weight (fun i => invertibleMatrix (matrices i.castSucc)) : ℂ)) *
        Complex.exp ((parameter - cohomologicalPoint) *
          (heightLog (argument * atInfinity (invertibleMatrix (matrices (Fin.last arity)))) : ℂ))) •
      FamilyCuspTaylor.matrixOrbit data .plane cohomologicalPoint family induced argument
        matrices :=
  vector_shift data (family (fun i => invertibleMatrix (matrices i.castSucc)))
    (twistedAt data holomorphic family induced weight parameter
      (fun i => invertibleMatrix (matrices i.castSucc)))
    (Complex.exp ((parameter - cohomologicalPoint) *
      (weight (fun i => invertibleMatrix (matrices i.castSucc)) : ℂ)))
    (induced (fun i => invertibleMatrix (matrices i.castSucc))) parameter
    (twistedAt_induced data holomorphic family induced weight parameter
      (fun i => invertibleMatrix (matrices i.castSucc)))
    (twistedAt_apply data holomorphic family induced weight parameter
      (fun i => invertibleMatrix (matrices i.castSucc)))
    (argument * atInfinity (invertibleMatrix (matrices (Fin.last arity))))

/-- The twisted family has a smooth cusp lift at every parameter. -/
theorem twistedAt_hasSmoothCuspLift (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (parameter : ℂ) :
    HasSmoothCuspLift data .plane parameter
      (twistedAt data holomorphic family induced weight parameter) := by
  intro argument
  obtain ⟨vectors, vectorsSmooth, realizes⟩ := lift argument
  refine ⟨fun x => (Complex.exp ((parameter - cohomologicalPoint) *
      (weight (fun i => x i.castSucc) : ℂ)) *
    Complex.exp ((parameter - cohomologicalPoint) *
      (heightLog (argument * atInfinity (x (Fin.last arity))) : ℂ))) • vectors x, ?_, ?_⟩
  · have first : Smooth (fun x : Fin (arity + 1) → RealGL3 =>
        Complex.exp ((parameter - cohomologicalPoint) * (weight (fun i => x i.castSucc) : ℂ))) :=
      smooth_cexp_mul _ (fun x : Fin (arity + 1) → RealGL3 => weight (fun i => x i.castSucc))
        (smooth_comp_castSucc weight weightSmooth)
    have second : Smooth (fun x : Fin (arity + 1) → RealGL3 =>
        Complex.exp ((parameter - cohomologicalPoint) *
          (heightLog (argument * atInfinity (x (Fin.last arity))) : ℂ))) :=
      smooth_cexp_mul _ (fun x : Fin (arity + 1) → RealGL3 =>
        heightLog (argument * atInfinity (x (Fin.last arity))))
        (smooth_comp_coordinate (Fin.last arity)
          (fun x : Fin 1 → RealGL3 => heightLog (argument * atInfinity (x 0)))
          (heightLog_law.smooth argument))
    show Smooth (fun x : Fin (arity + 1) → RealGL3 =>
      (Complex.exp ((parameter - cohomologicalPoint) * (weight (fun i => x i.castSucc) : ℂ)) *
        Complex.exp ((parameter - cohomologicalPoint) *
          (heightLog (argument * atInfinity (x (Fin.last arity))) : ℂ))) • (vectors x).val)
    exact ContDiffOn.smul (first.mul second) vectorsSmooth
  · intro x binary
    have realization := realizes x binary
    have core := shift_identity degree parameter binary (argument * atInfinity (x (Fin.last arity)))
      (family (fun i => x i.castSucc)
        (planeLevi binary 1 * (argument * atInfinity (x (Fin.last arity)))))
    simp only [binaryLevi] at realization ⊢
    rw [map_smul, Pi.smul_apply, smul_eq_mul, realization]
    unfold twistedAt
    rw [flatAt_apply]
    linear_combination
      (-(Complex.exp ((parameter - cohomologicalPoint) * (weight (fun i => x i.castSucc) : ℂ)))) *
        core

end Families

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
