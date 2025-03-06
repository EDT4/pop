import Mathlib.Order.Category.Preord
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Final

open CategoryTheory

def Nat.le_of_addl_le_addl {k x y : ℕ} (o : x ≤ y) : (k + x ≤ k + y) := match x , y , o with
| Nat.zero   , Nat.zero   , _ => by simp
| Nat.zero   , Nat.succ _ , _ => by simp
| Nat.succ _ , Nat.succ _ , o => Nat.succ_le_succ (Nat.le_of_addl_le_addl (Nat.le_of_succ_le_succ o))

def Nat.le_of_addr_le_addr {k x y : ℕ} (o : x ≤ y) : (x + k ≤ y + k) := by
  rewrite [Nat.add_comm x k , Nat.add_comm y k]
  exact Nat.le_of_addl_le_addl o

def Nat.le_of_mull_le_mull {k x y : ℕ} (o : x ≤ y) : (k * x ≤ k * y) := match x , y , o with
| Nat.zero   , Nat.zero   , _ => by simp
| Nat.zero   , Nat.succ y , _ => by simp
| Nat.succ x , Nat.succ y , o => Nat.le_of_addr_le_addr (Nat.le_of_mull_le_mull (Nat.le_of_succ_le_succ o))

def Nat.le_of_monr_le_monr {k x y : ℕ} (o : x ≤ y) : (x - k ≤ y - k) := by
  sorry

def Nat.le_of_divr_le_divr {k x y : ℕ} (o : x ≤ y) : (x / k ≤ y / k) := by -- TODO: Maybe not like this
  sorry

namespace Nat.Functor
  def succ : ℕ ⥤ ℕ where
    obj := Nat.succ
    map f := homOfLE (Nat.succ_le_succ (leOfHom f))

  def add (k : ℕ) : ℕ ⥤ ℕ where
    obj n := k + n
    map f := homOfLE (Nat.le_of_addl_le_addl (leOfHom f))

  def mul (k : ℕ) : ℕ ⥤ ℕ where
    obj n := k * n
    map f := homOfLE (Nat.le_of_mull_le_mull (leOfHom f))

  def pred : ℕ ⥤ ℕ where
    obj := Nat.pred
    map f := homOfLE (Nat.pred_le_pred (leOfHom f))

  def mon (k : ℕ) : ℕ ⥤ ℕ where
    obj n := n - k
    map f := homOfLE (Nat.le_of_monr_le_monr (leOfHom f))

  def div (k : ℕ) : ℕ ⥤ ℕ where
    obj n := n / k
    map f := homOfLE (Nat.le_of_divr_le_divr (leOfHom f))

  def pred_succ_adjunction : pred ⊣ succ where
    counit := .mk fun n => homOfLE (by simp [pred,succ])
    unit   := .mk fun n => homOfLE (by induction n <;> simp [pred,succ])

  def mon_add_adjunction : ∀{k}, mon k ⊣ add k where
    counit := .mk fun n => homOfLE (by simp [mon,add])
    unit   := .mk fun n => homOfLE (by induction n <;> simp [mon,add] ; sorry)

  def div_mul_adjunction : ∀{k}, div k ⊣ mul k := sorry

  instance succ_final : Functor.Final succ := Functor.final_of_adjunction pred_succ_adjunction
  instance add_final : ∀{k}, Functor.Final (add k) := Functor.final_of_adjunction mon_add_adjunction
  instance mul_final : ∀{k}, Functor.Final (mul k) := Functor.final_of_adjunction div_mul_adjunction
end Nat.Functor
