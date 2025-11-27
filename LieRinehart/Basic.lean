import Mathlib.RingTheory.Derivation.Lie

section Defs

variable (R A L M : Type*)
variable [CommRing R]
variable [CommRing A] [LieRing L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M]

-- Corresponds to tangent bundle
class LieRinehartPair extends Module A L, LieRingModule L A where
  lier_one : ∀ x : L, ⁅x, (1 : A)⁆ = 0
  lier_mul : ∀ (x : L) (a b : A), ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b
  lier_smul : ∀ (x : L) (a : A) (y : L), ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

-- Corresponds to lift vector bundles (infinitesimal version of vector bundle functors or natural vector bundles)
class LieRinehartModule [LieRinehartPair A L] : Prop where
  lier_smul' : ∀ (x : L) (a : A) (m : M), ⁅x, a • m⁆ = a • ⁅x, m⁆ + ⁅x, a⁆ • m

instance[LieRinehartPair A L] : LieRinehartModule A L A where
  lier_smul' := LieRinehartPair.lier_mul

instance [LieRinehartPair A L] : LieRinehartModule A L L where
  lier_smul' := LieRinehartPair.lier_smul

-- Corresponds to trivial vector bundles
class LieRinehartModule.IsTrivial [LieRinehartPair A L] [LieRinehartModule A L M] : Prop where
  smul_lier : ∀ (x : L) (a : A) (m : M),
    ⁅a • x, m⁆ = a • ⁅x, m⁆

class LieRinehartRing extends LieRinehartPair A L, LieRinehartModule.IsTrivial A L A

class LieRinehartAlgebra [LieRinehartRing A L] [Algebra R A] [LieAlgebra R L] : Prop
  extends IsScalarTower R A L, LieModule R L A

def LieRinehartModule.symbol [LieRinehartRing A L] [LieRinehartModule A L M] :
  L →+ A →+ M →ₗ[A] M := {
    toFun x := {
      toFun a := {
        toFun m := ⁅a • x, m⁆ - a • ⁅x, m⁆
        map_add' := by intros; simp; abel
        map_smul' := by intros; simp [lier_smul', IsTrivial.smul_lier, smul_sub, ←smul_assoc]; rw [mul_comm]
      }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [add_smul]; abel
    }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp; abel
  }

-- This describes the tensor bundles
class LieRinehartModule.IsLinear [LieRinehartRing A L]
  [LieRinehartModule A L M] : Prop where
  symbol_smul (a : A) (x : L) :
    symbol A L M (a • x) = a • symbol A L M x

instance [LieRinehartRing A L] [LieRinehartModule A L M] [LieRinehartModule.IsTrivial A L M] : LieRinehartModule.IsLinear A L M where
  symbol_smul := by intros; ext; simp [LieRinehartModule.symbol, LieRinehartModule.IsTrivial.smul_lier]

end Defs

open LieRinehartModule

section LieRinehartPair

variable {A L M : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [LieRinehartModule A L M]

@[simp]
theorem lier_one : ∀ x : L, ⁅x, (1 : A)⁆ = 0 :=
  LieRinehartPair.lier_one

theorem lier_smul : ∀ (x : L) (a : A) (m : M), ⁅x, a • m⁆ = a • ⁅x, m⁆ + ⁅x, a⁆ • m :=
  lier_smul'

@[simp]
theorem trivial_smul_lier [IsTrivial A L M] : ∀ (x : L) (a : A) (m : M), ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  IsTrivial.smul_lier

end LieRinehartPair

section LieRinehartRing

variable {R A L M : Type*}
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartRing A L]
variable [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [Module R M] [IsScalarTower R A M] [LieModule R L M]

variable [LieRinehartModule A L M]

@[simp]
theorem symbol_apply_one (x : L) : symbol A L M x 1 = 0 := by
  ext; simp [symbol]

theorem symbol_apply_mul (a b : A) (x : L) : symbol A L M x (a * b) = a • symbol A L M x b + symbol A L M (b • x) a := by
  ext; simp [symbol, smul_smul, smul_sub]

theorem symbol_smul_apply (a b : A) (x : L) : symbol A L M (a • x) b = symbol A L M x (a * b) - b • symbol A L M x a := by
  rw [mul_comm]
  simp [symbol_apply_mul]

theorem smul_lier (x : L) (a : A) (m : M) : ⁅a • x, m⁆ = a • ⁅x, m⁆ + symbol A L M x a m := by
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

end LieRinehartRing

variable (R A L M : Type*)
variable [CommRing R]

variable [CommRing A] [LieRing L] [LieRinehartRing A L]
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
