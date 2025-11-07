import LieRinehart.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import LieRinehart.Utilities.Alternating

open AlternatingMap
open Function

section Aux

variable (A L M N : Type*)
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [NoContrLRModule A L M]
variable [AddCommGroup N] [Module A N] [LieRingModule L N] [NoContrLRModule A L N]

structure LieAuxSystem (n : ℕ) where
  lie : L →+ (M [⋀^Fin n]→ₗ[A] N) →+ (M [⋀^Fin n]→ₗ[A] N)
  lie' : L →+ (M [⋀^Fin (n - 1)]→ₗ[A] N) →+ (M [⋀^Fin (n - 1)]→ₗ[A] N)
  h : match n with
    | 0 => True
    | _ + 1 => ∀ x y f, (lie y f).curryLeft x + (f.curryLeft ⁅y, x⁆) = lie' y (f.curryLeft x)
  lier_smul : ∀ x (r : A) f,
    lie x (r • f) = r • lie x f + (anchor _ _ x r) • f

@[simp]
def lie_aux_zero : LieAuxSystem A L M N 0 := {
  lie := {
    toFun x := {
      toFun f := constOfIsEmpty A _ _ (⁅x, f ![]⁆)
      map_zero' := by
        simp
        rfl
      map_add' := by
        intros
        simp
        rfl
    }
    map_zero' := by
      ext1
      simp [constOfIsEmpty]
      ext1
      rfl
    map_add' := by
      intros
      ext1
      simp [constOfIsEmpty]
      congr
  }
  lie' := 0
  h := by simp
  lier_smul := by
    intros
    ext v
    simp [constOfIsEmpty]
    rw [lier_smul]
    congr
    apply Subsingleton.elim
}

@[simp]
def lie_aux_succ (n : ℕ) (sys : LieAuxSystem A L M N n) : LieAuxSystem A L M N (n + 1) := {
  lie := {
    toFun x := {
      toFun f := uncurryLeft {
          toFun v := sys.lie x (f.curryLeft v) - f.curryLeft ⁅x, v⁆
          map_add' := by intros; simp; abel
          map_smul' := by simp [smul_sub, sys.lier_smul, lier_smul]
        } <| by
          cases n
          case zero => simp
          case succ n =>
            intro y
            have := sys.h y x (f.curryLeft y)
            simp at *
            rw [curryLeft_skew] at this
            rw [sub_eq_add_neg]
            simp
            exact this
      map_zero' := by
        simp
        rfl
      map_add' := by
        intros
        ext
        simp
        abel
    }
    map_zero' := by
      simp
      ext1
      simp
      ext1
      simp
    map_add' := by
      intros
      ext1
      simp
      ext1
      simp
      abel
  }
  lie' := sys.lie
  h := by
    simp
    intros
    ext
    simp [Matrix.vecCons]
  lier_smul := by
    intros
    ext v
    simp [sys.lier_smul, smul_sub, Matrix.vecCons]
    abel
}

@[simp]
def lie_aux (n : ℕ) : LieAuxSystem A L M N n := by
  induction n with
  | zero => exact lie_aux_zero A L M N
  | succ n ih => exact lie_aux_succ A L M N n ih

end Aux

section NoContrLRModule

variable {A L M N : Type*}
variable [CommRing A] [LieRing L] [LieRinehartPair A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [NoContrLRModule A L M]
variable [AddCommGroup N] [Module A N] [LieRingModule L N] [NoContrLRModule A L N]

namespace AlternatingMap

def lieAddMonoidHom (n) : L →+ (M [⋀^Fin n]→ₗ[A] N) →+ (M [⋀^Fin n]→ₗ[A] N) := {
  toFun x := {
    toFun f := (lie_aux A L M N n).lie x f
    map_zero' := by simp
    map_add' := by simp
  }
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp
}

instance : Bracket L (M [⋀^Fin n]→ₗ[A] N) where
  bracket x f := lieAddMonoidHom n x f

@[simp]
theorem lie_curryLeft (x : L) (f : M [⋀^Fin (n+1)]→ₗ[A] N) (y : M) :
  (⁅x, f⁆).curryLeft y = ⁅x, (f.curryLeft y)⁆ - f.curryLeft ⁅x, y⁆ := by
  simp [Bracket.bracket, lieAddMonoidHom]
  rfl

@[simp]
theorem lie_apply_zero (x : L) (f : M [⋀^Fin 0]→ₗ[A] N) (v : Fin 0 → M) :
  ⁅x, f⁆ v = ⁅x, f ![]⁆ := rfl

theorem lie_apply_succ (x : L) (f : M [⋀^Fin (n+1)]→ₗ[A] N) (v : Fin (n + 1) → M) :
  ⁅x, f⁆ v = ⁅x, f.curryLeft (v 0)⁆ (Fin.tail v) - f (update v 0 ⁅x, v 0⁆) := by
  simp [Bracket.bracket, lieAddMonoidHom]
  congr
  ext i
  cases i using Fin.cases
  rfl
  rfl

theorem lie_apply (x : L) (f : M [⋀^Fin n]→ₗ[A] N) (v : Fin n → M) :
  (⁅x, f⁆) v = ⁅x, (f v)⁆ - ∑ i : Fin n, f (update v i ⁅x, v i⁆) := by
  induction n with
  | zero =>
    simp [Bracket.bracket, lieAddMonoidHom]
    congr
    apply Subsingleton.elim
  | succ n ih =>
    rw [lie_apply_succ, ih]
    simp [sub_sub]
    congr
    . ext i
      cases i using Fin.cases
      rfl
      rfl
    . conv_rhs =>
        rw [Fin.sum_univ_succ, add_comm]
      congr
      ext i
      congr
      ext j
      cases j using Fin.cases
      case zero => rfl
      case succ j =>
        by_cases h : i = j
        case pos =>
          cases h
          simp [Fin.tail]
        case neg =>
          simp [Ne.symm h, Fin.tail]

instance : LieRingModule L (M [⋀^Fin n]→ₗ[A] N) where
  add_lie x y f := by ext; simp [Bracket.bracket]
  lie_add x f g := by ext; simp [Bracket.bracket]
  leibniz_lie X Y a := by
    induction n with
    | zero =>
      ext v
      simp [Bracket.bracket, lieAddMonoidHom]
    | succ n ih =>
      apply eq_of_curryLeft
      intro m
      have lie_sub (n : ℕ) (x : L) (f g : M [⋀^Fin n]→ₗ[A] N) : ⁅x, f - g⁆ = ⁅x, f⁆ - ⁅x, g⁆ := by ext; simp [Bracket.bracket]
      simp [lie_curryLeft, lie_sub]
      rw [ih ((curryLeft a) m)]
      abel

instance : NoContrLRModule A L (M [⋀^Fin n]→ₗ[A] N) where
  lier_smul x r f := by
    ext v
    simp [lie_apply, lier_smul, smul_sub, Finset.smul_sum]
    abel

end AlternatingMap

end NoContrLRModule

section LRModule

open Finset

variable {A L M N : Type*}
variable [CommRing A] [LieRing L] [LRAlgebra A L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M] [LRModule A L M]
variable [AddCommGroup N] [Module A N] [LieRingModule L N] [LRModule A L N]

instance : LRModule A L (M [⋀^Fin n]→ₗ[A] N) :=
  let contr₁ (α : L →ₗ[A] A) (x : L) : (M [⋀^Fin n]→ₗ[A] N) →ₗ[A] (M [⋀^Fin n]→ₗ[A] N) := LinearMap.compAlternatingMapₗ A (contr A L N α x) - AlternatingMap.compLinearMapLeibnizₗ (contr A L M α x)
  let contr₂ (α : L →ₗ[A] A) : L →ₗ[A] (M [⋀^Fin n]→ₗ[A] N) →ₗ[A] (M [⋀^Fin n]→ₗ[A] N) := {
    toFun x := contr₁ α x
    map_add' := by
      intros
      ext
      simp [contr₁]
      abel_nf
      congr
      rw [←smul_add, ←sum_add_distrib]
    map_smul' := by
      intros
      ext
      simp [contr₁, Finset.smul_sum, smul_sub]
  }
  let contr₃ : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] (M [⋀^Fin n]→ₗ[A] N) →ₗ[A] (M [⋀^Fin n]→ₗ[A] N) := {
    toFun α := contr₂ α
    map_add' := by
      intros
      ext
      simp [contr₂, contr₁]
      abel_nf
      congr
      rw [←smul_add, ←sum_add_distrib]
    map_smul' := by
      intros
      ext
      simp [contr₂, contr₁, Finset.smul_sum, smul_sub]
  }
  {
    contr := contr₃
    smul_lier := by
      intros x a m
      ext v
      simp [lie_apply, smul_lier, smul_sub, smul_sum, sum_add_distrib, contr₃, contr₂, contr₁]
      abel
  }

namespace AlternatingMap

@[simp]
theorem contr_apply_zero (α : L →ₗ[A] A) (x : L) (f : M [⋀^Fin 0]→ₗ[A] N) (v : Fin 0 → M) :
  contr A L (M [⋀^Fin 0]→ₗ[A] N) α x f v = contr A L N α x (f ![]) := by
  simp [contr, LRModule.contr]
  congr
  apply Subsingleton.elim

theorem contr_apply_succ (α : L →ₗ[A] A) (x : L) (f : M [⋀^Fin (n + 1)]→ₗ[A] N) (v : Fin (n + 1) → M) :
  contr A L _ α x f v =
  contr A L _ α x (f.curryLeft (v 0)) (Fin.tail v) - f (update v 0 (contr A L M α x (v 0))) := by
  induction n
  case zero =>
    simp [contr, LRModule.contr, Matrix.vecCons]
  case succ n ih =>
    simp [contr, LRModule.contr, Matrix.vecCons]
    abel_nf
    rw [←smul_add]
    congr
    rw [Fin.sum_univ_succAbove _ 0]
    abel

theorem contr_apply (α : L →ₗ[A] A) (x : L) (f : M [⋀^Fin n]→ₗ[A] N) (v : Fin n → M) :
  contr A L _ α x f v =
  contr A L N α x (f v) - ∑ i : Fin n, f (update v i (contr A L M α x (v i))) := rfl

end AlternatingMap

end LRModule
