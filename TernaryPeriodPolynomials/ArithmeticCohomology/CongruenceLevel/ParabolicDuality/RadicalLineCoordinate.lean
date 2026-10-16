module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalFaceDet
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChain
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.RadicalDualIso

@[expose] public section


/-!
# The binary coordinate of the line cusps of `Γ(N)`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, and
Lemma C.3 (`ar:lem:seed`), whose plane version is `SeedC3S4c.gammaNCoordinateIso`.

`H¹(N_Q, E_n) ≅ Sym^{n+1}` (determinant twist `0`, the plane has `-1`) as `Γ(N)`-modules, for the line group `Γ(N) ∩ Q(ℤ)` with radical
`Nℤ²` in the top row: the matrix `G = diag(1, 1, 3/N) · (cyclic permutation) ∈ GL₃(ℚ)` (`lineG`) conjugates the radical onto the library's
bottom-row radical `3ℤ²` (`lineG_radical`) and `diag(1, A)` to `diag(A, 1)` (`lineG_levi`) with no reversal of the Levi block;
`lineThetaEquiv` is the induced `H¹(Nℤ², E_n) ≅ H¹(3ℤ², E_n)` and `lineCoordinateIso` composes it with the library's coordinate
`lowerRadicalH1Coordinate` (degree zero: `lowerRadicalH1CoordinateZero`), equivariant for the whole of `GL₂(ℤ)` (there the determinant
twist matters; on `Γ(N) ≤ SL₂(ℤ)` it is invisible).  Conjugate line cusps: `lineFaceBinaryIso`, `lineFaceLitBinaryIso` (the literal
contragredient), `lineFaceCuspidalBinaryEquiv`, `lineFaceCuspidal_binary_pairing`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c (ambRep)
open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open scoped MatrixGroups
open Matrix

section Matrices

theorem lineG_aux (N : ℕ) (hN : (N : ℚ) ≠ 0) :
    (!![0, 1, 0; 0, 0, 1; (3 : ℚ) / N, 0, 0] : Matrix (Fin 3) (Fin 3) ℚ) *
      !![0, 0, (N : ℚ) / 3; 1, 0, 0; 0, 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  exact_mod_cast hN

theorem lineG_aux' (N : ℕ) (hN : (N : ℚ) ≠ 0) :
    (!![0, 0, (N : ℚ) / 3; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℚ) *
      !![0, 1, 0; 0, 0, 1; (3 : ℚ) / N, 0, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

variable (N : ℕ) [NeZero N]

/-- **The conjugating matrix** `G = diag(1, 1, 3/N) · (cyclic permutation) ∈ GL₃(ℚ)` carrying the top-row radical `Nℤ²` of the line
group `Γ(N) ∩ Q(ℤ)` onto the bottom-row radical `3ℤ²` of the library's lower radical lattice, and `diag(1, A)` to `diag(A, 1)`. -/
def lineG : RationalGL3 :=
  ⟨!![0, 1, 0; 0, 0, 1; (3 : ℚ) / N, 0, 0], !![0, 0, (N : ℚ) / 3; 1, 0, 0; 0, 1, 0],
    lineG_aux N (by exact_mod_cast NeZero.ne N), lineG_aux' N (by exact_mod_cast NeZero.ne N)⟩

/-- The rational image of an element of `SL₃(ℤ)`. -/
def ratGL (g : SL(3, ℤ)) : RationalGL3 := GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL g)

theorem ratGL_apply (g : SL(3, ℤ)) (i j : Fin 3) : (ratGL g).val i j = (((g : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ℚ) := rfl

theorem arithmeticLevi_apply (M : GeneralLinearGroup (Fin 2) ℤ) :
    (arithmeticLevi M).val = !![(M.val 0 0 : ℚ), (M.val 0 1 : ℚ), 0; (M.val 1 0 : ℚ), (M.val 1 1 : ℚ), 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lowerRadicalLattice_apply (r : RadicalLattice) :
    (lowerRadicalLattice r).val = !![1, 0, 0; 0, 1, 0; 3 * (r.toAdd.1 : ℚ), 3 * (r.toAdd.2 : ℚ), 1] := rfl

omit [NeZero N] in
theorem ratGL_radEltQ (r : RadicalLattice) :
    (ratGL (radEltQ N r)).val = !![1, (N : ℚ) * (r.toAdd.1 : ℚ), (N : ℚ) * (r.toAdd.2 : ℚ); 0, 1, 0; 0, 0, 1] := by
  ext i j
  rw [ratGL_apply]
  fin_cases i <;> fin_cases j <;> simp [radEltQ]

theorem ratGL_blockDiagQ (A : SL(2, ℤ)) :
    (ratGL (blockDiagQ A)).val = !![1, 0, 0; 0, ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ), ((A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ);
      0, ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ), ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ)] := by
  ext i j
  rw [ratGL_apply]
  fin_cases i <;> fin_cases j <;> simp [blockDiagQ]

theorem lineG_radical (r : RadicalLattice) :
    lineG N * ratGL (radEltQ N r) = lowerRadicalLattice r * lineG N := by
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, lowerRadicalLattice_apply, ratGL_radEltQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineG, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem lineG_levi (A : SL(2, ℤ)) :
    lineG N * ratGL (blockDiagQ A) = arithmeticLevi (Matrix.SpecialLinearGroup.toGL A) * lineG N := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, arithmeticLevi_apply, ratGL_blockDiagQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineG, Matrix.mul_apply, Fin.sum_univ_three]

theorem ambRep_rational (n : ℕ) (g : SL(3, ℤ)) (v : HomogeneousPoly n) :
    ambRep n g v = rationalCoefficientComponent n trivialCharacter (ratGL g) v := by
  have h := rationalCoefficient_integer n (Matrix.SpecialLinearGroup.toGL g) v
  change _ = rationalCoefficientComponent n trivialCharacter
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL g)) v
  rw [h]
  change realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ g) v = _
  unfold realCoefficient
  change homogeneousAction n (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (Matrix.SpecialLinearGroup.mapGL ℝ g)) v = _
  congr 2
  apply Units.ext
  funext i j
  simp [GeneralLinearGroup.map_apply]

end Matrices

section Transport

open CategoryTheory
open TernaryPeriodPolynomials.Argument.FacePairing (lowerRadicalH1CoordinateZero lowerRadicalH1CoordinateZero_apply
  lowerRadicalH1CoordinateZero_equivariant)

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- The radical lattice representation of the line group `Γ(N) ∩ Q(ℤ)`: `Nℤ²` acting on `E_n`. -/
abbrev lineRadRep : Rep ℂ RadicalLattice := Rep.res (lineExt N).inl (lineStdRep N n)

theorem lineRadRep_rho (r : RadicalLattice) (v : HomogeneousPoly n) :
    (lineRadRep N n).ρ r v = ambRep n (radEltQ N r) v := rfl

/-- The conjugating operator `T = ρ(G)` of the line group. -/
def lineT : Module.End ℂ (HomogeneousPoly n) := rationalCoefficientComponent n trivialCharacter (lineG N)

/-- Its inverse. -/
def lineTInv : Module.End ℂ (HomogeneousPoly n) := rationalCoefficientComponent n trivialCharacter (lineG N)⁻¹

theorem lineTInv_lineT (v : HomogeneousPoly n) : lineTInv N n (lineT N n v) = v := by
  change (rationalCoefficientComponent n trivialCharacter (lineG N)⁻¹ *
    rationalCoefficientComponent n trivialCharacter (lineG N)) v = v
  rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem lineT_lineTInv (v : HomogeneousPoly n) : lineT N n (lineTInv N n v) = v := by
  change (rationalCoefficientComponent n trivialCharacter (lineG N) *
    rationalCoefficientComponent n trivialCharacter (lineG N)⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem lineT_rad (r : RadicalLattice) (v : HomogeneousPoly n) :
    lineT N n ((lineRadRep N n).ρ r v) = (lowerRadicalLatticeRep n).ρ r (lineT N n v) := by
  rw [lineRadRep_rho, ambRep_rational]
  change (rationalCoefficientComponent n trivialCharacter (lineG N) *
      rationalCoefficientComponent n trivialCharacter (ratGL (radEltQ N r))) v =
    (rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r) *
      rationalCoefficientComponent n trivialCharacter (lineG N)) v
  rw [← map_mul, ← map_mul, lineG_radical]

theorem lineT_rad_intertwines (r : RadicalLattice) :
    ((lowerRadicalLatticeRep n).ρ r).comp (lineT N n) = (lineT N n).comp ((lineRadRep N n).ρ r) := by
  apply LinearMap.ext
  intro v
  exact (lineT_rad N n r v).symm

theorem lineTInv_rad_intertwines (r : RadicalLattice) :
    ((lineRadRep N n).ρ r).comp (lineTInv N n) = (lineTInv N n).comp ((lowerRadicalLatticeRep n).ρ r) := by
  apply LinearMap.ext
  intro v
  have h := lineT_rad N n r (lineTInv N n v)
  rw [lineT_lineTInv] at h
  have h2 := congrArg (lineTInv N n) h
  have h3 : lineTInv N n (lineT N n (((lineRadRep N n).ρ r) (lineTInv N n v))) =
      ((lineRadRep N n).ρ r) (lineTInv N n v) := lineTInv_lineT N n _
  exact h3.symm.trans h2

end Transport

section Coordinate

open CategoryTheory
open TernaryPeriodPolynomials.Argument.FacePairing (lowerRadicalH1CoordinateZero lowerRadicalH1CoordinateZero_apply
  lowerRadicalH1CoordinateZero_equivariant)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (lowerRadicalH1Coordinate lowerRadicalH1Coordinate_apply
  lowerRadicalH1Coordinate_equivariant lowerRadicalH1Levi lowerRadicalH1Levi_apply lowerRadicalCocycleLevi
  lowerRadicalCocycleCoordinate arithmeticLeviCoefficient lowerLeviLatticeInput oneCocyclePullbackH1 oneCocyclePullback
  oneCocyclePullbackH1_apply oneCocycle_H1_surjective splitRadicalH1Action splitRadicalH1Action_apply
  splitRadicalCocycleAction splitRadicalCocycleAction_apply)

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **The binary coordinate of the bottom-row radical cohomology in every degree** (positive degrees: the library's
`lowerRadicalH1Coordinate`; degree zero: `lowerRadicalH1CoordinateZero`). -/
def lowerCoordAll : (n : ℕ) → groupCohomology.H1 (lowerRadicalLatticeRep n) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1)
  | 0 => lowerRadicalH1CoordinateZero
  | k + 1 => lowerRadicalH1Coordinate (k + 1) (Nat.succ_pos k)

theorem lowerCoordAll_apply (n : ℕ) (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) :
    lowerCoordAll n (groupCohomology.H1π (lowerRadicalLatticeRep n) cycle) = lowerRadicalCocycleCoordinate n cycle := by
  cases n with
  | zero => exact lowerRadicalH1CoordinateZero_apply cycle
  | succ k => exact lowerRadicalH1Coordinate_apply (Nat.succ_pos k) cycle

theorem lowerCoordAll_equivariant (n : ℕ) (M : GeneralLinearGroup (Fin 2) ℤ)
    (x : groupCohomology.H1 (lowerRadicalLatticeRep n)) :
    lowerCoordAll n (lowerRadicalH1Levi n M x) =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) M) (lowerCoordAll n x) := by
  cases n with
  | zero => exact lowerRadicalH1CoordinateZero_equivariant M x
  | succ k => exact lowerRadicalH1Coordinate_equivariant (Nat.succ_pos k) M x

/-- The comparison `H¹(Nℤ², E_n) → H¹(3ℤ², E_n)` of the top-row radical of the line group with the library's bottom-row radical. -/
def lineThetaH1 : groupCohomology.H1 (lineRadRep N n) →ₗ[ℂ] groupCohomology.H1 (lowerRadicalLatticeRep n) :=
  oneCocyclePullbackH1 (lineRadRep N n) (lowerRadicalLatticeRep n) (MonoidHom.id _) (lineT N n) (lineT_rad_intertwines N n)

/-- Its inverse. -/
def lineThetaH1Inv : groupCohomology.H1 (lowerRadicalLatticeRep n) →ₗ[ℂ] groupCohomology.H1 (lineRadRep N n) :=
  oneCocyclePullbackH1 (lowerRadicalLatticeRep n) (lineRadRep N n) (MonoidHom.id _) (lineTInv N n)
    (lineTInv_rad_intertwines N n)

theorem lineThetaH1_π (c : groupCohomology.cocycles₁ (lineRadRep N n)) :
    lineThetaH1 N n (groupCohomology.H1π (lineRadRep N n) c) =
      groupCohomology.H1π (lowerRadicalLatticeRep n)
        (oneCocyclePullback (lineRadRep N n) (lowerRadicalLatticeRep n) (MonoidHom.id _) (lineT N n)
          (lineT_rad_intertwines N n) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

theorem lineThetaH1Inv_π (c : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) :
    lineThetaH1Inv N n (groupCohomology.H1π (lowerRadicalLatticeRep n) c) =
      groupCohomology.H1π (lineRadRep N n)
        (oneCocyclePullback (lowerRadicalLatticeRep n) (lineRadRep N n) (MonoidHom.id _) (lineTInv N n)
          (lineTInv_rad_intertwines N n) c) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ c

/-- **`H¹(Nℤ², E_n) ≅ H¹(3ℤ², E_n)`** for the line group. -/
def lineThetaEquiv : groupCohomology.H1 (lineRadRep N n) ≃ₗ[ℂ] groupCohomology.H1 (lowerRadicalLatticeRep n) :=
  LinearEquiv.ofLinearMap (lineThetaH1 N n) (lineThetaH1Inv N n)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (lowerRadicalLatticeRep n) x
      change lineThetaH1 N n (lineThetaH1Inv N n (groupCohomology.H1π _ c)) = _
      rw [lineThetaH1Inv_π, lineThetaH1_π]
      refine congrArg (fun z => groupCohomology.H1π _ z) ?_
      apply groupCohomology.cocycles₁_ext
      intro r
      exact lineT_lineTInv N n _)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (lineRadRep N n) x
      change lineThetaH1Inv N n (lineThetaH1 N n (groupCohomology.H1π _ c)) = _
      rw [lineThetaH1_π, lineThetaH1Inv_π]
      refine congrArg (fun z => groupCohomology.H1π _ z) ?_
      apply groupCohomology.cocycles₁_ext
      intro r
      exact lineTInv_lineT N n _)

/-- The binary coordinate of the radical cohomology of the line group `Γ(N) ∩ Q(ℤ)`. -/
def lineRadicalCoordinate : groupCohomology.H1 (lineRadRep N n) ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (lineThetaEquiv N n).trans (lowerCoordAll n)

theorem lineRadicalCoordinate_π (c : groupCohomology.cocycles₁ (lineRadRep N n)) :
    lineRadicalCoordinate N n (groupCohomology.H1π (lineRadRep N n) c) =
      lowerRadicalCocycleCoordinate n
        (oneCocyclePullback (lineRadRep N n) (lowerRadicalLatticeRep n) (MonoidHom.id _) (lineT N n)
          (lineT_rad_intertwines N n) c) := by
  change lowerCoordAll n (lineThetaH1 N n (groupCohomology.H1π _ c)) = _
  rw [lineThetaH1_π, lowerCoordAll_apply]

theorem lineT_sect (A : ↥(CongruenceSubgroup.Gamma N)) (v : HomogeneousPoly n) :
    lineT N n ((lineStdRep N n).ρ ((lineSplitting N) A) v) =
      arithmeticLeviCoefficient n (Matrix.SpecialLinearGroup.toGL A.1) (lineT N n v) := by
  have e : (lineStdRep N n).ρ ((lineSplitting N) A) v = ambRep n (blockDiagQ A.1) v := rfl
  rw [e, ambRep_rational]
  change (rationalCoefficientComponent n trivialCharacter (lineG N) *
      rationalCoefficientComponent n trivialCharacter (ratGL (blockDiagQ A.1))) v =
    (rationalCoefficientComponent n trivialCharacter (arithmeticLevi (Matrix.SpecialLinearGroup.toGL A.1)) *
      rationalCoefficientComponent n trivialCharacter (lineG N)) v
  rw [← map_mul, ← map_mul, lineG_levi]

/-- **The radical cohomology `H¹(Nℤ², E_n)` of the line group `Γ(N) ∩ Q(ℤ)` is `Sym^{n+1}` (determinant twist `0`) as a
`Γ₂(N)`-representation.** -/
def lineCoordinateIso :
    splitRadicalH1Representation (lineSplitting N) (lineStdRep N n) ≅
      Rep.res (CongruenceSubgroup.Gamma N).subtype (modularBinaryRep (n + 1) 0) :=
  Rep.mkIso (Representation.Equiv.mk (lineRadicalCoordinate N n) (by
    intro A
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := oneCocycle_H1_surjective (Rep.res (lineExt N).inl (lineStdRep N n)) x
    have h1 := splitRadicalH1Action_apply (lineSplitting N) (lineStdRep N n) A c
    have hcyc : oneCocyclePullback (lineRadRep N n) (lowerRadicalLatticeRep n) (MonoidHom.id _)
        (lineT N n) (lineT_rad_intertwines N n)
        (splitRadicalCocycleAction (lineSplitting N) (lineStdRep N n) A c) =
        lowerRadicalCocycleLevi n (Matrix.SpecialLinearGroup.toGL A.1)
          (oneCocyclePullback (lineRadRep N n) (lowerRadicalLatticeRep n) (MonoidHom.id _)
            (lineT N n) (lineT_rad_intertwines N n) c) := by
      apply groupCohomology.cocycles₁_ext
      intro r
      change lineT N n ((lineStdRep N n).ρ ((lineSplitting N) A)
          (c (splitRadicalInput (lineSplitting N) A r))) = _
      have hin : splitRadicalInput (lineSplitting N) A r =
          lowerLeviLatticeInput (Matrix.SpecialLinearGroup.toGL A.1) r := by
        apply Multiplicative.toAdd.injective
        obtain ⟨a1, a2⟩ := lineRadicalInput_toAdd N A r
        apply Prod.ext
        · exact a1
        · exact a2
      refine (lineT_sect N n A (c (splitRadicalInput (lineSplitting N) A r))).trans ?_
      rw [hin]
      rfl
    have h2 := lineRadicalCoordinate_π N n
      (splitRadicalCocycleAction (lineSplitting N) (lineStdRep N n) A c)
    have h3 := lineRadicalCoordinate_π N n c
    have h4 := lowerCoordAll_equivariant n (Matrix.SpecialLinearGroup.toGL A.1)
      (groupCohomology.H1π (lowerRadicalLatticeRep n)
        (oneCocyclePullback (lineRadRep N n) (lowerRadicalLatticeRep n) (MonoidHom.id _)
          (lineT N n) (lineT_rad_intertwines N n) c))
    rw [lowerRadicalH1Levi_apply, lowerCoordAll_apply, lowerCoordAll_apply] at h4
    change lineRadicalCoordinate N n
        (splitRadicalH1Action (lineSplitting N) (lineStdRep N n) A
          (groupCohomology.H1π (Rep.res (lineExt N).inl (lineStdRep N n)) c)) =
      Binary.homogeneousAction (n + 1) 0
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (Matrix.SpecialLinearGroup.toGL A.1))
        (lineRadicalCoordinate N n (groupCohomology.H1π (lineRadRep N n) c))
    refine (congrArg (lineRadicalCoordinate N n) h1).trans (h2.trans ?_)
    rw [hcyc, h3]
    exact h4))

end Coordinate

section Faces

open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open CongruenceSubgroup

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

/-- **Every line cusp in binary coordinates**: `H¹(N_{Q'}, E_n) ≅ Sym^{n+1}` as `Γ(N)`-modules for the conjugate line cusp
`Q' = h⁻¹ Q h` (the conjugation `lineFaceModIso` followed by `lineCoordinateIso`). -/
def lineFaceBinaryIso : lineFaceRadH1 N h n ≅ symRep N (n + 1) 0 := (lineFaceModIso N h n).symm ≪≫ lineCoordinateIso N n

/-- **Every line cusp, literal contragredient, in binary coordinates**: `H¹(N_{Q'}, E_n^*) ≅ Sym^{n+1}` as `Γ(N)`-modules. -/
def lineFaceLitBinaryIso : lineFaceRadH1Lit N n h ≅ symRep N (n + 1) 0 :=
  have : FiniteDimensional ℂ (lineFaceRadH1 N h n) := inferInstance
  have : FiniteDimensional ℂ (lineFaceRadH1Lit N n h) :=
    finiteDimensional_H1 (Rep.res (lineFaceExt N h).inl (lineFaceRepLit N n h))
  have hB := Classical.choose_spec (symRep_pairing (N := N) (n + 1) 0 0)
  isoOfTwoPerfect (V := lineFaceRadH1 N h n)
    (leviPerfect (lineFaceSplitting N h) (lineFaceRadicalInput_det N h) (lineFaceRep N h n))
    (PerfectInv.comp_iso (V := symRep N (n + 1) 0) (W := symRep N (n + 1) 0)
      (e := Classical.choose (symRep_pairing (N := N) (n + 1) 0 0)) ⟨hB.1, hB.2.1, hB.2.2⟩ (lineFaceBinaryIso N n h))

/-- The mixed cuspidal group of the line cusp `Q'` is the cuspidal group of `Sym^{n+1}` for `Γ(N)`. -/
def lineFaceCuspidalBinaryEquiv : lineFaceCuspidal N h n ≃ₗ[ℂ] cuspidalSubspace (Gamma N) (symRep N (n + 1) 0) :=
  cuspEquivOfIso (lineFaceBinaryIso N n h)

variable {N}

/-- **The base pairing of every line cusp of `Γ(N)` in binary coordinates**: the apolar pairing of binary forms perfectly pairs the
mixed cuspidal group `𝒞_{Q'}(E_n)` with the cuspidal group of `Sym^{n+1}`. -/
theorem lineFaceCuspidal_binary_pairing (hN : 3 ≤ N) (e' : ℤ) :
    ∃ B : lineFaceCuspidal N h n →ₗ[ℂ] cuspidalSubspace (Gamma N) (symRep N (n + 1) e') →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  obtain ⟨e, hinv, hL, hR⟩ := symRep_pairing (N := N) (n + 1) 0 e'
  obtain ⟨B', hl, hr⟩ := cuspidal_pairing_gammaN hN (symRep N (n + 1) 0) (symRep N (n + 1) e') e hinv hL hR
  obtain ⟨B, h1, h2, -⟩ := exists_transport (X := lineFaceCuspidal N h n) B' hl hr
    (lineFaceCuspidalBinaryEquiv N n h) (LinearEquiv.refl ℂ _)
  exact ⟨B, h1, h2⟩

end Faces

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
