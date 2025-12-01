import Mathlib.RingTheory.Derivation.Lie

section Defs

class LieRinehartRing (L : Type*) [LieRing L] (A : Type*) [Ring A] extends LieRingModule L A where
  lier_one : ∀ x : L, ⁅x, (1 : A)⁆ = 0
  lier_mul : ∀ (x : L) (a b : A), ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b

variable (R A L M : Type*)
variable [CommRing R]
variable [CommRing A] [LieRing L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M]

-- Corresponds to tangent bundle
class LieRinehartPair extends Module A L, LieRinehartRing L A where
  lier_smul : ∀ (x : L) (a : A) (y : L), ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

-- Corresponds to lift vector bundles (infinitesimal version of vector bundle functors or natural vector bundles)
class LieRinehartModule [LieRinehartPair A L] : Prop where
  lier_smul' : ∀ (x : L) (a : A) (m : M), ⁅x, a • m⁆ = a • ⁅x, m⁆ + ⁅x, a⁆ • m

instance[LieRinehartPair A L] : LieRinehartModule A L A where
  lier_smul' := LieRinehartRing.lier_mul

instance [LieRinehartPair A L] : LieRinehartModule A L L where
  lier_smul' := LieRinehartPair.lier_smul

-- Semilinear modules precisely are those with symbol A-linear in the M argument.
class LieRinehartModule.IsSemilinear [LieRinehartPair A L] [LieRinehartModule A L M] : Prop where
  smul_lier_smul : ∀ (a : A) (x : L) (b : A) (m : M),
    ⁅a • x, b⁆ • m = (a * ⁅x, b⁆) • m

def LieRinehartModule.symbol [LieRinehartPair A L] [LieRinehartModule A L M] [LieRinehartModule.IsSemilinear A L M] :
  L →+ A →+ M →ₗ[A] M := {
    toFun x := {
      toFun a := {
        toFun m := ⁅a • x, m⁆ - a • ⁅x, m⁆
        map_add' := by intros; simp; abel
        map_smul' := by intros; simp [lier_smul', IsSemilinear.smul_lier_smul, smul_sub, ←smul_assoc, mul_comm a]
      }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_smul]; abel
    }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp; abel
  }

-- This describes the tensor bundles
class LieRinehartModule.IsLinear [LieRinehartPair A L]
  [LieRinehartModule A L M] : Prop extends IsSemilinear A L M where
  symbol_smul : ∀ (a : A) (x : L), symbol A L M (a • x) = a • symbol A L M x

-- Corresponds to trivial vector bundles
class LieRinehartModule.IsTrivial [LieRinehartPair A L] [LieRinehartModule A L M] : Prop where
  smul_lier : ∀ (x : L) (a : A) (m : M), ⁅a • x, m⁆ = a • ⁅x, m⁆

open LieRinehartModule

instance [LieRinehartPair A L] [LieRinehartModule A L M] [IsTrivial A L M] : IsLinear A L M where
  smul_lier_smul a x b m := by
    have := lier_smul' (a • x) b m
    simp [IsTrivial.smul_lier] at this
    simp [lier_smul', ←smul_assoc] at this
    rw [←sub_eq_zero] at this
    ring_nf at this
    abel_nf at this
    simp [←sub_eq_add_neg, sub_eq_zero] at this
    rw [this]
  symbol_smul := by intros; ext; simp [LieRinehartModule.symbol, IsTrivial.smul_lier]

instance [LieRinehartPair A L] [IsTrivial A L A] [LieRinehartModule A L M] : IsSemilinear A L M where
  smul_lier_smul := by
    intros
    simp [IsTrivial.smul_lier]

class LieRinehartAlgebra [LieRinehartPair A L] [Algebra R A] [LieAlgebra R L] : Prop
  extends IsScalarTower R A L, LieModule R L A

end Defs

open LieRinehartModule

section LieRinehartModule

section

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartRing L A]

@[simp]
theorem lier_one : ∀ x : L, ⁅x, (1 : A)⁆ = 0 :=
  LieRinehartRing.lier_one

@[simp]
theorem lier_mul : ∀ (x : L) (a b : A), ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b :=
  LieRinehartRing.lier_mul

end

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [LieRinehartModule A L M]

theorem lier_smul : ∀ (x : L) (a : A) (m : M), ⁅x, a • m⁆ = a • ⁅x, m⁆ + ⁅x, a⁆ • m :=
  lier_smul'

@[simp]
theorem smul_lier_smul [IsSemilinear A L M] : ∀ (a : A) (x : L) (b : A) (m : M), ⁅a • x, b⁆ • m = (a * ⁅x, b⁆) • m :=
  IsSemilinear.smul_lier_smul

@[simp]
theorem trivial_smul_lier [IsTrivial A L M] : ∀ (x : L) (a : A) (m : M), ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  IsTrivial.smul_lier

@[simp]
theorem lieRingSelfModule_smul_lier (a : A) (x y : L) : ⁅a • x, y⁆ = a • ⁅x, y⁆ - ⁅y, a⁆ • x := by
  rw [←lie_skew, lier_smul, ←lie_skew]
  simp [-lie_skew]
  abel

end LieRinehartModule

section IsSemilinear

variable {R A L M : Type*}
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [Module R M] [IsScalarTower R A M] [LieModule R L M]

variable [LieRinehartModule A L M] [IsSemilinear A L M]

@[simp]
theorem symbol_apply_one (x : L) : symbol A L M x 1 = 0 := by
  ext; simp [symbol]

theorem symbol_apply_mul (a b : A) (x : L) : symbol A L M x (a * b) = a • symbol A L M x b + symbol A L M (b • x) a := by
  ext; simp [symbol, smul_smul, smul_sub]

theorem symbol_smul_apply (a b : A) (x : L) : symbol A L M (a • x) b = symbol A L M x (a * b) - b • symbol A L M x a := by
  rw [mul_comm]
  simp [symbol_apply_mul]

theorem smul_lier (a : A) (x : L) (m : M) : ⁅a • x, m⁆ = a • ⁅x, m⁆ + symbol A L M x a m := by
  simp [symbol]

@[simp]
theorem symbol_apply_smul (r : R) (x : L) (a : A) : symbol A L M x (r • a) = r • symbol A L M x a := by
  ext m
  simp [symbol, smul_sub]

@[simp]
theorem symbol_apply_algebraMap (r : R) (x : L) : symbol A L M x (algebraMap R A r) = 0 := by
  rw [←mul_one (algebraMap R A r), ←Algebra.smul_def, symbol_apply_smul, symbol_apply_one, smul_zero]

@[simp]
theorem symbol_eq_zero [IsTrivial A L M] : symbol A L M = 0 := by
  ext
  simp [symbol]

@[simp]
theorem symbol_smul [IsLinear A L M] : ∀ (a : A) (x : L), symbol A L M (a • x) = a • symbol A L M x :=
  IsLinear.symbol_smul

end IsSemilinear

section IsLinear

variable (R A L M : Type*)
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [Module R M] [IsScalarTower R A M] [LieModule R L M]

variable [LieRinehartModule A L M] [IsLinear A L M]

def LieRinehartModule.symbolLinearMap : L →ₗ[A] Derivation R A (M →ₗ[A] M) where
  toFun x := {
    toFun a := {
      toFun m := symbol A L M x a m
      map_add' := by simp
      map_smul' := by simp
    }
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp [Algebra.smul_def, symbol_apply_mul]
    map_one_eq_zero' := by ext; simp
    leibniz' := by intros; ext; simp [symbol_apply_mul]
  }
  map_smul' := by intros; ext; simp
  map_add' := by intros; ext; simp

theorem LieRinehartModule.symbolLinearMap_eq_symbol (x : L) (a : A) : symbolLinearMap R A L M x a = symbol A L M x a := rfl

end IsLinear
