module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.SectionMultipliers
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.EndpointLift

@[expose] public section


/-!
# Analytic inputs of the `n = 3` totality argument

Original work by Claude Sonnet 5.5.

This file defines the objects and the *named inputs* of `EdgeAssembly`. Everything that is
only algebra, complex analysis in one variable, or formal bookkeeping is proved elsewhere
(`EdgeTransport`, `EdgeCircle`, `EdgeFactorization`, `EdgeAssembly`); the four statements below are
the genuinely analytic facts about the *local Hilbert standard integral* at the places `{∞, 3}`:

* `LocalVectorsSmooth` : the local standard integral of a flat family is a smooth vector of the cusp
  representation (so that its automorphic realization exists), for integral arguments and
  `Re s > -n/2 - 1`;
* `LocalScalarAnalytic` : its realization at a fixed binary adele is holomorphic in `s`;
* `LocalLiftVector` and `LocalLiftRealization` (together `LocalCircleLift`) : the Cauchy circle
  average of the local vectors against any scalar function continuous on the circle is a smooth
  vector, jointly smooth in the real argument and in vertex families (`LocalLiftVector`), and it
  realizes the circle average of the realizations (`LocalLiftRealization`);
* `LocalLiftScalarSmooth` : for a single section, that circle average of the local scalars is a
  smooth function of the real translation of the argument;
* `TwistedLocalContinuity` : joint continuity of the local scalar in `(s, z)` for the twisted
  sections `ρ_h^z · R(h) f` of the right-translation argument.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Metric Filter Topology
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EdgeInputs

/-- The half plane `Re s > -n/2 - 1` of absolute convergence of the local standard integral at
integral arguments. -/
def localHalfPlane (degree : ℕ) : Set ℂ := {parameter | -(degree : ℝ) / 2 - 1 < parameter.re}

/-- The half plane `Re s > -n/2` of absolute convergence of the global standard integral. -/
def globalHalfPlane (degree : ℕ) : Set ℂ := {parameter | -(degree : ℝ) / 2 < parameter.re}

/-- The arguments whose finite part is integral at every place (the arguments of the local
majorants; same set as `integralArguments`). -/
def IsIntegralArgument (argument : AdelicGL) : Prop :=
  ∃ integral : Matrix.GeneralLinearGroup (Fin 3) IntegralAdeles,
    finiteGroup argument = Matrix.GeneralLinearGroup.map integralEmbedding integral

theorem cohomologicalPoint_re : cohomologicalPoint.re = -3 / 2 := by
  norm_num [cohomologicalPoint]

section Objects

variable {degree : ℕ} (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)

/-- The flat family attached to a plane section at the cohomological point. -/
def flatFamily (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    ℂ → AdelicGL → ℂ :=
  (SectionSpace.linearFlatExtension data holomorphic sectionValue).val

theorem flatFamily_flat
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    IsFlatSection data (flatFamily data holomorphic sectionValue) :=
  (SectionSpace.linearFlatExtension data holomorphic sectionValue).property

/-- The local Hilbert standard integral of the flat family of a section, at a parameter and an
argument. -/
def localVector (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (parameter : ℂ) (argument : AdelicGL) : data.cusp.H :=
  localValue data parameter (flatFamily data holomorphic sectionValue parameter)
    ((flatFamily_flat data holomorphic sectionValue).1 parameter) argument

open Classical in
/-- The realization of a vector of the cusp representation at a binary adele, `0` if the vector is
not smooth. -/
def vecScalar (vector : data.cusp.H) (binary : BinaryAdelicGL) : ℂ :=
  if smooth : vector ∈ data.cusp.smooth then data.cusp.realize ⟨vector, smooth⟩ binary else 0

theorem vecScalar_of_mem {vector : data.cusp.H} (smooth : vector ∈ data.cusp.smooth)
    (binary : BinaryAdelicGL) :
    vecScalar data vector binary = data.cusp.realize ⟨vector, smooth⟩ binary := by
  unfold vecScalar
  rw [dite_eq_left smooth]

/-- The realization at `binary` of the local Hilbert standard integral of the flat family of a
section. -/
def localScalar (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (parameter : ℂ) (argument : AdelicGL) (binary : BinaryAdelicGL) : ℂ :=
  vecScalar data (localVector data holomorphic sectionValue parameter argument) binary

end Objects

section Inputs

variable {degree : ℕ} (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)

/-- **Input 1 (`LocalVectorsSmooth`).** For every plane section `f`, every parameter with
`Re s > -n/2 - 1` and every argument with integral finite part, the local Hilbert standard integral
`∫_{(ℝ × ℚ₃)²} v_s(w⁻¹ n(u) g) du` of the flat family of `f` is a *smooth* vector of the cusp
representation: its orbit under `GL₂(ℝ)` is smooth and it is fixed by an open compact subgroup of
`GL₂(𝔸_f)`. (Local analogue of `HilbertStandardSmooth.value_mem_smooth`; the proof is the real
orbit analyticity of `LocalAnalyticTaylor` together with finite-level invariance.) -/
def LocalVectorsSmooth : Prop :=
  ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (parameter : ℂ),
    parameter ∈ localHalfPlane degree → ∀ argument : AdelicGL, IsIntegralArgument argument →
      localVector data holomorphic sectionValue parameter argument ∈ data.cusp.smooth

/-- **Input 2 (`LocalScalarAnalytic`).** The realization at a fixed binary adele of the local
Hilbert standard integral of the flat family of a plane section, at an argument with integral finite
part, is a holomorphic function of the parameter on `Re s > -n/2 - 1`. -/
def LocalScalarAnalytic : Prop :=
  ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL), IsIntegralArgument argument → ∀ binary : BinaryAdelicGL,
      AnalyticOnNhd ℂ (fun parameter => localScalar data holomorphic sectionValue parameter
        argument binary) (localHalfPlane degree)

/-- **Input 3a (`LocalLiftVector`).** The Cauchy lift of the local vectors, as vectors. Let
`lam` be any scalar function continuous on a circle `|s - s₀| = r` whose closed disc lies in the half
plane `Re s > -n/2 - 1`. For a family `x' ↦ f_{x'}` of plane sections with smooth cusp lift (arity `0`
is a single section) and a maximal compact `κ`, the vectors
`W(x', y) = (2πi)⁻¹ ∮_{|s-s₀|=r} (s-s₀)⁻¹ • (lam(s) • L_s)` (`EndpointLift.endpointLift`), where `L_s`
is the local standard integral of the flat family of `f_{x'}` at `κ · y`, are *smooth vectors* of the
cusp representation, and form a map smooth for the topology of the cusp Hilbert space as a function
of `(x', y)`. (Taylor majorants of the local integrand uniform on the circle: `EndpointLiftTaylor`,
`LocalTaylorProducerFamily`; the criterion `IsSmoothVector` for membership.) -/
def LocalLiftVector : Prop :=
  ∀ (lam : ℂ → ℂ) (radius : ℝ), 0 < radius →
    closedBall cohomologicalPoint radius ⊆ localHalfPlane degree →
    ContinuousOn lam (sphere cohomologicalPoint radius) →
    ∀ {arity : ℕ} (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
      (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices)),
      HasSmoothCuspLift data .plane cohomologicalPoint family →
      ∀ compact : AdelicGL, inMaximalCompact compact →
        ∃ lift : (Fin (arity + 1) → RealGL3) → data.cusp.smooth,
          Smooth (fun x => (lift x).val) ∧
          ∀ x, (lift x).val = EndpointLift.endpointLift cohomologicalPoint radius lam
            (fun parameter => localVector data holomorphic
              ⟨family (fun index => x index.castSucc), induced _⟩ parameter
              (compact * atInfinity (x (Fin.last arity))))

/-- **Input 3b (`LocalLiftRealization`).** The Cauchy lift of `LocalLiftVector` realizes the
circle average of the realizations of the local vectors: for every family of smooth vectors `W(x)`
that is smooth in `x` and equal to the circle average (`EndpointLift.endpointLift`) of the local
vectors, `realize (W x) B = (2πi)⁻¹ ∮ (s-s₀)⁻¹ • (lam(s) • localScalar f_{x'} s (κ · y) B) ds`.
(Realization commutes with the circle integral of the analytic family of smooth vectors: compact
boxes of the local radical and `FixedRealizationLimit.principal_limit_unique`, as in
`localValue_realizes`.) -/
def LocalLiftRealization : Prop :=
  ∀ (lam : ℂ → ℂ) (radius : ℝ), 0 < radius →
    closedBall cohomologicalPoint radius ⊆ localHalfPlane degree →
    ContinuousOn lam (sphere cohomologicalPoint radius) →
    ∀ {arity : ℕ} (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
      (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices)),
      HasSmoothCuspLift data .plane cohomologicalPoint family →
      ∀ compact : AdelicGL, inMaximalCompact compact →
        ∀ lift : (Fin (arity + 1) → RealGL3) → data.cusp.smooth,
          Smooth (fun x => (lift x).val) →
          (∀ x, (lift x).val = EndpointLift.endpointLift cohomologicalPoint radius lam
            (fun parameter => localVector data holomorphic
              ⟨family (fun index => x index.castSucc), induced _⟩ parameter
              (compact * atInfinity (x (Fin.last arity))))) →
          ∀ x binary, data.cusp.realize (lift x) binary =
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
              (parameter - cohomologicalPoint)⁻¹ • (lam parameter • localScalar data holomorphic
                ⟨family (fun index => x index.castSucc), induced _⟩ parameter
                (compact * atInfinity (x (Fin.last arity))) binary)

/-- **Input 3c (`LocalLiftScalarSmooth`).** For a single plane section `f`, a maximal compact
`κ` and a binary adele `B`, the circle average of the local scalars
`(2πi)⁻¹ ∮ (s-s₀)⁻¹ • (lam(s) • localScalar f s (κ · y) B) ds` is a smooth function of the real
translation `y`, for `lam` continuous on a circle inside `Re s > -n/2 - 1`. (Scalar Taylor
expansions of the local scalar integrand in `y` with majorants uniform on the circle; the
analogue of `LocalLiftVector` for the realization. For vertex families this scalar smoothness does
not follow from the Hilbert-space smoothness `HasSmoothCuspLift` and is not needed.) -/
def LocalLiftScalarSmooth : Prop :=
  ∀ (lam : ℂ → ℂ) (radius : ℝ), 0 < radius →
    closedBall cohomologicalPoint radius ⊆ localHalfPlane degree →
    ContinuousOn lam (sphere cohomologicalPoint radius) →
    ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
      (compact : AdelicGL), inMaximalCompact compact → ∀ binary : BinaryAdelicGL,
        Smooth (fun x : Fin 1 → RealGL3 =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
            (parameter - cohomologicalPoint)⁻¹ • (lam parameter • localScalar data holomorphic
              sectionValue parameter (compact * atInfinity (x 0)) binary))

/-- The Cauchy lift of the local vectors is a family of smooth vectors, smooth in the argument,
realizing the circle average of the local scalars (the conjunction of the inputs 3a and 3b). -/
def LocalCircleLift : Prop :=
  ∀ (lam : ℂ → ℂ) (radius : ℝ), 0 < radius →
    closedBall cohomologicalPoint radius ⊆ localHalfPlane degree →
    ContinuousOn lam (sphere cohomologicalPoint radius) →
    ∀ {arity : ℕ} (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
      (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices)),
      HasSmoothCuspLift data .plane cohomologicalPoint family →
      ∀ compact : AdelicGL, inMaximalCompact compact →
        ∃ lift : (Fin (arity + 1) → RealGL3) → data.cusp.smooth,
          Smooth (fun x => (lift x).val) ∧
          ∀ x binary, data.cusp.realize (lift x) binary =
            (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
              (parameter - cohomologicalPoint)⁻¹ • (lam parameter • localScalar data holomorphic
                ⟨family (fun index => x index.castSucc), induced _⟩ parameter
                (compact * atInfinity (x (Fin.last arity))) binary)

theorem localCircleLift_of_parts (vector : LocalLiftVector data holomorphic)
    (realization : LocalLiftRealization data holomorphic) : LocalCircleLift data holomorphic := by
  intro lam radius radius_pos ball continuous arity family induced lift compact compactMembership
  obtain ⟨liftVectors, liftSmooth, liftEquation⟩ :=
    vector lam radius radius_pos ball continuous family induced lift compact compactMembership
  exact ⟨liftVectors, liftSmooth, realization lam radius radius_pos ball continuous family induced
    lift compact compactMembership liftVectors liftSmooth liftEquation⟩

/-- **Input 4 (`TwistedLocalContinuity`).** For a plane section `f`, a real element `h`, a
maximal compact `κ` and a binary adele `B`, the realization of the local standard integral of the flat
family of the twisted section `Φ_z = ρ_h^z · R(h) f` (`SectionMultipliers.twist`) at `κ` is jointly
continuous in `(s, z)` on `{|s - s₀| ≤ r} × {|z| < w}`, whenever the closed disc lies in
`Re s > -n/2 - 1`. (The flat family of `Φ_z` is `Ξ^{s-s₀} ρ_h^z R(h) f`, so the local integrand is
dominated uniformly in `(s, z)` on the compact parameter sets, as `ρ_h` is bounded above and below.) -/
def TwistedLocalContinuity {logXi : AdelicGL → ℝ} (law : SectionMultipliers.HeightLaw logXi) :
    Prop :=
  ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (real : RealGL3)
    (compact : AdelicGL), inMaximalCompact compact → ∀ (binary : BinaryAdelicGL) (radius width : ℝ),
      closedBall cohomologicalPoint radius ⊆ localHalfPlane degree →
      ContinuousOn (fun p : ℂ × ℂ => localScalar data holomorphic
        ⟨SectionMultipliers.twist logXi real p.2 sectionValue.val,
          SectionMultipliers.isInduced_twist data cohomologicalPoint law real p.2
            sectionValue.val sectionValue.property⟩ p.1 compact binary)
        (closedBall cohomologicalPoint radius ×ˢ ball (0 : ℂ) width)

end Inputs

end EdgeInputs

end TernaryPeriodPolynomials.EdgeConvergence
