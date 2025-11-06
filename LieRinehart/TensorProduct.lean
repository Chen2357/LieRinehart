import LieRinehart.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

open TensorProduct

instance (A L M N : Type*)
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M] [NoContrLRModule A L M]
  [AddCommGroup N] [Module A N] [LieRingModule L N] [NoContrLRModule A L N]
  : LieRingModule L (M ⊗[A] N) :=
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

instance (A L M N : Type*)
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M] [NoContrLRModule A L M]
  [AddCommGroup N] [Module A N] [LieRingModule L N] [NoContrLRModule A L N] :
  NoContrLRModule A L (M ⊗[A] N) where
  lier_smul x a t := by
    induction t with
    | zero => simp
    | tmul m n =>
      simp [Bracket.bracket, smul_tmul', lier_smul, add_tmul]
      abel
    | add t1 t2 ht1 ht2 =>
      simp [ht1, ht2]
      abel

instance (A L M N : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M] [LRModule A L M]
  [AddCommGroup N] [Module A N] [LieRingModule L N] [LRModule A L N] :
  LRModule A L (M ⊗[A] N) :=
  let contr₁ (α : L →ₗ[A] A) (x : L) : (M ⊗[A] N) →ₗ[A] (M ⊗[A] N) := lift {
      toFun m := {
        toFun n := (contr _ _ _ α x m) ⊗ₜ n + m ⊗ₜ (contr _ _ _ α x n)
        map_add' := by intros; simp [tmul_add]; abel
        map_smul' := by intros; simp
      }
      map_add' := by intros; ext; simp [add_tmul]; abel
      map_smul' := by intros; ext; simp [smul_tmul']
  }
  let contr₂ (α : L →ₗ[A] A) : L →ₗ[A] (M ⊗[A] N) →ₗ[A] (M ⊗[A] N) := {
      toFun x := contr₁ α x
      map_add' x y := by
        ext t
        induction t
        case zero => simp
        case tmul m n =>
          simp [contr₁, tmul_add, add_tmul]
          abel
        case add t1 t2 ht1 ht2 =>
          simp [ht1, ht2]
          abel
      map_smul' a x := by
        ext t
        induction t
        case zero => simp
        case tmul m n =>
          simp [contr₁, smul_tmul']
        case add t1 t2 ht1 ht2 =>
          simp [ht1, ht2]
  }
  let contr₃ : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] (M ⊗[A] N) →ₗ[A] (M ⊗[A] N) := {
    toFun α := contr₂ α
    map_add' α β := by
      ext x t
      induction t
      case zero => simp
      case tmul m n =>
        simp [contr₂, contr₁, add_tmul, tmul_add]
        abel
      case add t1 t2 ht1 ht2 =>
        simp [ht1, ht2]
        abel
    map_smul' a α := by
      ext x t
      induction t
      case zero => simp
      case tmul m n =>
        simp [contr₂, contr₁, smul_tmul']
      case add t1 t2 ht1 ht2 =>
        simp [ht1, ht2]
  }
  {
    contr := contr₃
    smul_lier x a t := by
      induction t
      case zero => simp
      case tmul m n =>
        simp [Bracket.bracket, contr₃, contr₂, contr₁, smul_lier, add_tmul, tmul_add, smul_tmul']
        abel
      case add t1 t2 ht1 ht2 =>
        simp [ht1, ht2]
        abel
  }
