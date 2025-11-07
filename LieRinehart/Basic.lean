import Mathlib.RingTheory.Derivation.Lie

class LieRinehartPair (A L : Type*) [CommRing A] [LieRing L] extends Module A L where
  anchor : L →+ Derivation ℤ A A
  anchor_lie : ∀ (x y : L), anchor ⁅x, y⁆ = ⁅anchor x, anchor y⁆
  lier_smul (x : L) (a : A) (y : L) :
    ⁅x, a • y⁆ = a • ⁅x, y⁆ + (anchor x a) • y

def anchor (A L) [CommRing A] [LieRing L] [LieRinehartPair A L] : L →+ Derivation ℤ A A :=
  LieRinehartPair.anchor

-- Also consider make FunLike notation for anchor
-- @[inherit_doc]
-- notation "⁅" x ";" a "⁆" => anchor _ _ x a

@[simp]
theorem anchor_lie {A L : Type*}
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  (x y : L) :
  anchor A L ⁅x, y⁆ = ⁅anchor A L x, anchor A L y⁆ :=
  LieRinehartPair.anchor_lie x y

-- Perhaps should be LRAlgebra R A L and anchor_smul should be anchor (r • x) a = r • (anchor x a)
class LRAlgebra (A L : Type*)
  [CommRing A] [LieRing L]
  extends LieRinehartPair A L where
  anchor_smul : ∀ (x : L) (a b : A),
    anchor (a • x) b = a • (anchor x b)

@[simp]
theorem anchor_smul {A L : Type*}
  [CommRing A] [LieRing L] [LRAlgebra A L]
  (x : L) (a b : A) :
  anchor A L (a • x) b = a • (anchor A L x b) :=
  LRAlgebra.anchor_smul x a b

def d₀ (A L : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L] : A →+ (L →ₗ[A] A) := {
    toFun a := {
      toFun f := anchor _ _ f a
      map_add' := by simp
      map_smul' := by simp
    }
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp
  }

class NoContrLRModule (A L M : Type*)
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M] : Prop where
  lier_smul (x : L) (a : A) (m : M) :
    ⁅x, a • m⁆ = a • ⁅x, m⁆ + (anchor A L x a) • m

theorem lier_smul {A L M : Type*}
  [CommRing A] [LieRing L] [LieRinehartPair A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M]
  [NoContrLRModule A L M]
  (x : L) (a : A) (m : M) :
  ⁅x, a • m⁆ = a • ⁅x, m⁆ + (anchor A L x a) • m :=
  NoContrLRModule.lier_smul x a m

class LRModule (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M]
  extends NoContrLRModule A L M where
  contr : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] M →ₗ[A] M
  smul_lier : ∀ (x : L) (a : A) (m : M),
    ⁅a • x, m⁆ = a • ⁅x, m⁆ + contr (d₀ A L a) x m

def contr (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M]
  [LRModule A L M] : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] M →ₗ[A] M :=
  LRModule.contr

class LRModule.IsTrivial (A L M : Type*)
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M]
  [LRModule A L M] : Prop where
  contr_eq_zero : contr (A:=A) (L:=L) (M:=M) = 0

@[simp]
theorem contr_eq_zero {A L M : Type*}
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M]
  [LRModule A L M] [LRModule.IsTrivial A L M] :
  contr (A:=A) (L:=L) (M:=M) = 0 :=
  LRModule.IsTrivial.contr_eq_zero

theorem smul_lier {A L M : Type*}
  [CommRing A] [LieRing L] [LRAlgebra A L]
  [AddCommGroup M] [Module A M] [LieRingModule L M]
  [LRModule A L M]
  (x : L) (a : A) (m : M) :
  ⁅a • x, m⁆ = a • ⁅x, m⁆ + contr A L M (d₀ A L a) x m :=
  LRModule.smul_lier x a m

instance (A L : Type*) [CommRing A] [LieRing L] [LieRinehartPair A L] : NoContrLRModule A L L where
  lier_smul := LieRinehartPair.lier_smul

instance (A L : Type*) [CommRing A] [LieRing L] [LRAlgebra A L] : LRModule A L L :=
  let contr' : (L →ₗ[A] A) →ₗ[A] L →ₗ[A] L →ₗ[A] L := {
    toFun α := {
      toFun x := {
        toFun y := -α y • x
        map_add' := by intros; simp [add_smul]; abel
        map_smul' := by intros; simp [smul_neg, mul_smul]
      }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp; rw [smul_comm]
    }
    map_add' := by intros; ext; simp [add_smul]; abel
    map_smul' := by intros; ext; simp [smul_smul]
  }
  {
  contr := contr'
  smul_lier x a y := by
    rw [←lie_skew, lier_smul]
    simp [d₀, contr']
    conv_lhs => arg 2; rw [←smul_neg, lie_skew]
    abel
  }

@[simp]
theorem LRAlgebra.contr_apply {A L : Type*}
  [CommRing A] [LieRing L] [LRAlgebra A L]
  (α : L →ₗ[A] A) (x y : L) :
  contr _ _ _ α x y = -α y • x := rfl

instance (A L : Type*) [CommRing A] [LieRing L] [LieRinehartPair A L] : LieRingModule L A where
  bracket x a := anchor A L x a
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp [Bracket.bracket]

instance (A L : Type*) [CommRing A] [LieRing L] [LieRinehartPair A L] : NoContrLRModule A L A where
  lier_smul x a m := by
    simp [Bracket.bracket]
    ring

instance (A L : Type*) [CommRing A] [LieRing L] [LRAlgebra A L] : LRModule A L A where
  contr := 0
  smul_lier x a m := by
    simp [Bracket.bracket]

instance (A L : Type*) [CommRing A] [LieRing L] [LRAlgebra A L] : LRModule.IsTrivial A L A where
  contr_eq_zero := rfl

instance (A L : Type*) [CommRing A] [LieRing L] [LieAlgebra A L] : LRAlgebra A L where
  anchor := 0
  anchor_lie := by simp
  lier_smul := by simp
  anchor_smul := by simp
