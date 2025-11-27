import LieRinehart.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

open LieRinehartModule
open TensorProduct

variable (A L M N : Type*)
variable [CommRing A] [LieRing L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [AddCommGroup N] [Module A N] [LieRingModule L N]

instance [LieRinehartPair A L] [LieRinehartModule A L M]
  [LieRinehartModule A L N] : LieRingModule L (M ⊗[A] N) :=
  let bracket' (x : L) : M ⊗[A] N →+ M ⊗[A] N := liftAddHom {
    toFun m := {
      toFun n := ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆
      map_zero' := by simp
      map_add' := by intros; simp [tmul_add]; abel
    }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp [add_tmul]; abel
  } <| by
    intros a m n
    simp [lier_smul, tmul_add, add_tmul, smul_tmul]
    abel
  {
  bracket x := bracket' x
  add_lie x y t := by
    induction t
    case zero => simp [bracket']
    case tmul m n =>
      simp [bracket', tmul_add, add_tmul]
      abel
    case add t1 t2 ht1 ht2 =>
      simp [ht1, ht2]
      abel
  lie_add x t1 t2 := by simp
  leibniz_lie x y t := by
    induction t
    case zero => simp
    case tmul m n =>
      simp [bracket', tmul_sub, sub_tmul]
      abel
    case add t1 t2 ht1 ht2 =>
      simp [ht1, ht2]
      abel
  }

instance [LieRinehartPair A L] [LieRinehartModule A L M] [LieRinehartModule A L N] : LieRinehartModule A L (M ⊗[A] N) where
  lier_smul' x a t := by
    induction t with
    | zero => simp
    | tmul m n =>
      simp [Bracket.bracket, smul_tmul', lier_smul, add_tmul]
      abel
    | add t1 t2 ht1 ht2 =>
      simp [*]
      abel


instance [LieRinehartRing A L] [LieRinehartModule A L M] [LieRinehartModule A L N]
  [IsTrivial A L M] [IsTrivial A L N] : IsTrivial A L (M ⊗[A] N) where
  smul_lier x a t := by
    induction t with
    | zero => simp
    | tmul m n =>
      simp [Bracket.bracket]
      rfl
    | add t1 t2 ht1 ht2 =>
      simp [*]

@[simp]
private lemma LieRinehartModule.symbol_tmul [LieRinehartRing A L] [LieRinehartModule A L M] [LieRinehartModule A L N] (x : L) (a : A) (m : M) (n : N) :
  symbol A L (M ⊗[A] N) x a (m ⊗ₜ n) = (symbol A L M x a m) ⊗ₜ n + m ⊗ₜ (symbol A L N x a n) := by
  simp [symbol, Bracket.bracket, sub_tmul, tmul_sub, smul_tmul]
  abel

instance [LieRinehartRing A L] [LieRinehartModule A L M] [LieRinehartModule A L N] [IsLinear A L M] [IsLinear A L N] : IsLinear A L (M ⊗[A] N) where
  symbol_smul x a := by
    ext b t
    induction t with
    | zero => simp
    | tmul m n =>
      simp [smul_tmul]
    | add t1 t2 ht1 ht2 =>
      simp [*]
