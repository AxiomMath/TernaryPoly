module

public import TernaryPeriodPolynomials.Building.RankTwo.AugmentedFrames
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.RepresentationTheory.Subrepresentation

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryModularSymbol
open RankTwoAugmentedFrames

abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) ℚ
abbrev Line := RationalLine2
abbrev Divisors := Line →₀ ℚ

def integral : IntegralGL →* GL2 := Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)

def vectorAction : GL2 →* (Space ≃ₗ[ℚ] Space) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Space).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

@[simp] theorem vectorAction_integral (g : IntegralGL) :
    vectorAction (integral g) = rationalRepresentation g := rfl

/-- Rational projective lines are actual one-dimensional rational subspaces. -/
def lineAction (g : GL2) (L : Line) : Line :=
  ⟨L.val.map (vectorAction g).toLinearMap,
    ((vectorAction g).submoduleMap L.val).finrank_eq.symm.trans L.property⟩

@[simp] theorem lineAction_one (L : Line) : lineAction 1 L = L := by
  apply Subtype.ext
  simp [lineAction]

theorem lineAction_mul (g h : GL2) (L : Line) :
    lineAction (g*h) L = lineAction g (lineAction h L) := by
  apply Subtype.ext
  simpa only [lineAction,map_mul,LinearEquiv.coe_toLinearMap_mul,Module.End.mul_eq_comp] using
    Submodule.map_comp (vectorAction h).toLinearMap (vectorAction g).toLinearMap L.val

/-- Transport of finite rational divisors along the literal projective action. -/
def divisorAction : Representation ℚ GL2 Divisors where
  toFun g := Finsupp.lmapDomain ℚ ℚ (lineAction g)
  map_one' := by
    ext L q
    simp [Finsupp.lmapDomain_apply]
  map_mul' g h := by
    ext L q
    simp [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,lineAction_mul]

@[simp] theorem divisorAction_single (g : GL2) (L : Line) (q : ℚ) :
    divisorAction g (Finsupp.single L q) = Finsupp.single (lineAction g L) q :=
  Finsupp.mapDomain_single

/-- The augmentation is the sum of the finitely many rational coefficients. -/
def augmentation : Divisors →ₗ[ℚ] ℚ := Finsupp.lsum ℚ (fun _ => LinearMap.id)

@[simp] theorem augmentation_single (L : Line) (q : ℚ) :
    augmentation (Finsupp.single L q) = q := by simp [augmentation]

theorem augmentation_action (g : GL2) (c : Divisors) :
    augmentation (divisorAction g c) = augmentation c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single L q => simp

/-- The actual rank-two Steinberg module is the augmentation kernel. -/
abbrev St := LinearMap.ker augmentation

def symbol (L M : Line) : St :=
  ⟨Finsupp.single M 1 - Finsupp.single L 1, by simp⟩

@[simp] theorem symbol_val (L M : Line) :
    (symbol L M).val = Finsupp.single M 1 - Finsupp.single L 1 := rfl

@[simp] theorem symbol_self (L : Line) : symbol L L = 0 := by
  apply Subtype.ext
  simp

theorem symbol_reverse (L M : Line) : symbol M L = -symbol L M := by
  apply Subtype.ext
  change _ = -(_ - _)
  simp

theorem symbol_triangle (L M N : Line) : symbol L M + symbol M N = symbol L N := by
  apply Subtype.ext
  change (_ - _) + (_ - _) = _ - _
  abel

/-- The genuine rational action preserves the augmentation kernel. -/
def action : Representation ℚ GL2 St := divisorAction.subrepresentation St
  (fun g c hc => by
    change augmentation (divisorAction g c) = 0
    rw [augmentation_action]
    exact hc)

@[simp] theorem action_symbol (g : GL2) (L M : Line) :
    action g (symbol L M) = symbol (lineAction g L) (lineAction g M) := by
  apply Subtype.ext
  change divisorAction g (_ - _) = _ - _
  simp

/-- All differences with one fixed base point span the actual augmentation kernel. -/
theorem span_symbols (L : Line) : Submodule.span ℚ (Set.range (symbol L)) = ⊤ := by
  apply top_unique
  intro c _
  let F : Divisors →ₗ[ℚ] St := Finsupp.lsum ℚ (fun M => LinearMap.toSpanSingleton ℚ St (symbol L M))
  have hF (x : Divisors) : (F x).val = x - augmentation x • Finsupp.single L 1 := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add,Submodule.coe_add,hx,hy,add_smul]
      abel
    | single M q =>
      simp [F,LinearMap.toSpanSingleton_apply,smul_sub,Finsupp.smul_single]
  have he : F c.val = c := by
    apply Subtype.ext
    rw [hF,c.property,zero_smul,sub_zero]
  rw [←he]
  have hx : ∀ x : Divisors, F x ∈ Submodule.span ℚ (Set.range (symbol L)) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simpa only [map_zero] using (Submodule.span ℚ (Set.range (symbol L))).zero_mem
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | single M q =>
      simpa [F] using (Submodule.span ℚ (Set.range (symbol L))).smul_mem q
        (Submodule.subset_span (Set.mem_range_self M))
  exact hx c.val

end TernaryPoly.BinaryModularSymbol
