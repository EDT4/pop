import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Category.Preord
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.SuccPred.Basic

open CategoryTheory

-- instance Preorder.opposite {C : Type _} [Preorder C] : Preorder Cᵒᵖ where
--   le x y := y.unop ≤ x.unop
--   le_refl x := le_refl x.unop
--   le_trans := sorry

namespace Nat.Functor
  variable (k : ℕ)

  def succ : ℕ ⥤ ℕ := Monotone.functor Order.succ_mono
  def pred : ℕ ⥤ ℕ := Monotone.functor Order.pred_mono
  def addl : ℕ ⥤ ℕ := Monotone.functor (f := (k + ·)) (Monotone.const_add monotone_id k)
  def addr : ℕ ⥤ ℕ := Monotone.functor (f := (· + k)) (Monotone.add_const monotone_id k)
  def mull : ℕ ⥤ ℕ := Monotone.functor (f := (k * ·)) (Monotone.const_mul' monotone_id k)
  def mulr : ℕ ⥤ ℕ := Monotone.functor (f := (· * k)) (Monotone.mul_const' monotone_id k)
  def powr : ℕ ⥤ ℕ := Monotone.functor (f := (· ^ k)) (Monotone.pow_const monotone_id k)
  def subl : ℕ ⥤ ℕ := Monotone.functor (f := (· - k)) fun _ _ p => Nat.sub_le_sub_right p k
  def divfr : ℕ ⥤ ℕ := Monotone.functor (f := (· / k)) fun _ _ => Nat.div_le_div_right
  -- def divcr : ℕ ⥤ ℕ := Monotone.functor (f := (· ⌈/⌉ k)) fun _ _ => sorry -- the monotonicity from the Galois connection require 0 < k, but not this

  def powl (o : 1 ≤ k) : ℕ ⥤ ℕ := Monotone.functor (f := (k ^ ·)) fun _ _ => pow_le_pow_right' (a := k) o
  -- def subr (k : ℕ) : ℕᵒᵖ ⥤ ℕ := Monotone.functor (f := (k - Opposite.unop ·)) (fun a b p => Nat.sub_le_sub_left p k)

  variable {k}
  variable (o : 0 < k := by decide)

  def pred_succ_adjunction : pred ⊣ succ where
    counit := .mk fun n => homOfLE $ by simp [pred,succ]
    unit   := .mk fun n => homOfLE $ by induction n <;> simp [pred,succ]

  def subl_addl_adjunction : subl k ⊣ addl k where
    counit := .mk fun n => homOfLE $ by simp [subl,addl]
    unit   := .mk fun n => homOfLE $ le_add_tsub

  def subl_addr_adjunction : subl k ⊣ addr k where
    counit := .mk fun n => homOfLE $ by simp [subl,addr]
    unit   := .mk fun n => homOfLE $ by simp [subl,addr] ; rewrite [Nat.add_comm] ; exact le_add_tsub

  def mull_divr_adjunction : mull k ⊣ divfr k := GaloisConnection.adjunction $ by intro _ _ ; simp [GaloisConnection] ; rewrite [Nat.mul_comm] ; exact (Nat.le_div_iff_mul_le o).symm
  def mulr_divr_adjunction : mulr k ⊣ divfr k := GaloisConnection.adjunction $ fun _ _ => (Nat.le_div_iff_mul_le o).symm

  instance succ_final : Functor.Final succ     := Functor.final_of_adjunction pred_succ_adjunction
  instance addl_final : Functor.Final (addl k) := Functor.final_of_adjunction subl_addl_adjunction
  instance addr_final : Functor.Final (addr k) := Functor.final_of_adjunction subl_addr_adjunction
  instance mull_final : Functor.Final (mull k) := Functor.final_of_adjunction $ GaloisConnection.adjunction $ gc_mul_ceilDiv o
  instance mulr_final : Functor.Final (mulr k) := Functor.final_of_adjunction $ GaloisConnection.adjunction $ by intro _ _ ; simp [GaloisConnection] ; rewrite [Nat.mul_comm] ; apply gc_smul_ceilDiv o
  instance divr_final : Functor.Final (divfr k) := Functor.final_of_adjunction (mull_divr_adjunction o)
end Nat.Functor
