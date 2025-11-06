import LieRinehart.Basic

variable (A L M N : Type*)
variable [CommRing A] [LieRing L]
variable [AddCommGroup M] [Module A M] [LieRingModule L M]
variable [AddCommGroup N] [Module A N] [LieRingModule L N]

instance [LieRinehartPair A L] [NoContrLRModule A L M] [NoContrLRModule A L N] :
  LieRingModule L (M →ₗ[A] N) :=
  let bracket' : L →+ (M →ₗ[A] N) →+ (M →ₗ[A] N) := {
    toFun x := {
      toFun f := {
        toFun m := ⁅x, f m⁆ - f ⁅x, m⁆
        map_add' := by intros; simp [lie_add]; abel
        map_smul' := by intros; simp [lier_smul, smul_sub]
      }
      map_add' := by intros; ext; simp [lie_add]; abel
      map_zero' := by ext; simp
    }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp [add_lie]; abel
  }
  {
    bracket x f := bracket' x f
    add_lie := by simp
    lie_add := by simp
    leibniz_lie := by
      intros x y f
      ext m
      simp [bracket']
      abel
  }

instance [LieRinehartPair A L] [NoContrLRModule A L M] [NoContrLRModule A L N] : NoContrLRModule A L (M →ₗ[A] N) where
  lier_smul x a f := by
    ext m
    simp [Bracket.bracket, lier_smul, smul_sub]
    abel

instance [LRAlgebra A L] [LRModule A L M] [LRModule A L N] : LRModule A L (M →ₗ[A] N) :=
  let contr₁ (α : L →ₗ[A] A) (x : L) : (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] N) := {
    toFun f := {
      toFun m := contr _ _ _ α x (f m) - f (contr _ _ _ α x m)
      map_add' := by intros; simp; abel
      map_smul' := by intros; simp [smul_sub]
    }
    map_add' := by intros; ext; simp; abel
    map_smul' := by intros; ext; simp [smul_sub]
  }
  let contr₂ (α : L →ₗ[A] A) : L →ₗ[A] (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] N) := {
    toFun x := contr₁ α x
    map_add' := by intros; ext; simp [contr₁]; abel
    map_smul' := by intros; ext; simp [contr₁, smul_sub]
  }
  let contr₃ : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] N) := {
    toFun α := contr₂ α
    map_add' := by intros; ext; simp [contr₂, contr₁]; abel
    map_smul' := by intros; ext; simp [contr₂, contr₁, smul_sub]
  }
  {
    contr := contr₃
    smul_lier x a f := by
      ext m
      simp [Bracket.bracket, contr₃, contr₂, contr₁, smul_lier, smul_sub]
      abel
  }
