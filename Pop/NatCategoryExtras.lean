import Init.WF
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Category.Preord
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Defs

open CategoryTheory
open CategoryTheory.Limits

namespace Nat.StrictMono
  variable (f : ℕ → ℕ)
  variable (smono : StrictMono f)
  include f smono

  abbrev condition (n : ℕ) : Set ℕ := fun x : ℕ => f x ≥ n

  lemma condition_existence {n : ℕ} : ∃ x, x ∈ condition f n :=
    ⟨n , StrictMono.id_le smono n⟩

  local instance dec_pred {n : ℕ} : DecidablePred (fun x ↦ (x ∈ condition f n) ∧ (∀ y ∈ condition f n, ¬Nat.lt_wfRel.rel y x)) := by
    intro x
    -- TODO: There must be a better way. Did not find the right tactics for this
    let imp_dist {p₁ q₁ p₂ q₂ : Prop} : (p₁ ↔ p₂) → (q₁ ↔ q₂) → ((p₁ → q₁) ↔ (p₂ → q₂)) := by aesop
    let all_dist {A : Type _}{p q : A → Prop} : (∀ x, p x ↔ q x) → ((∀ x, p x) ↔ (∀ x, q x)) := by aesop
    let contrapos {p q : Prop} : (p → q) ↔ (¬q → ¬p) := by aesop
    let e n (P : ℕ → Prop) : (∀(k : Fin n), P k) ↔ (∀ k, (k < n) → P k) := Iff.intro (fun a b c => a (.mk b c)) (fun a b => a b.val b.isLt)
    let _ : Decidable (∀(y : Fin x), f y < n)      := Fintype.decidableForallFintype
    let _ : Decidable (∀ y, (y < x) → (f y < n))   := by rw [← e] ; apply_assumption
    let _ : Decidable (∀ y, ¬(x ≤ y) → ¬(f y ≥ n)) := by rw [all_dist (fun _ => imp_dist not_le not_le)] ; apply_assumption
    let _ : Decidable (∀ y, (f y ≥ n) → (x ≤ y))   := by rw [all_dist (fun _ => contrapos)] ; apply_assumption
    simp [Membership.mem,Set.Mem,Nat.lt_wfRel]
    apply instDecidableAnd

  def inv (n : ℕ) : ℕ :=
    let h := Nat.lt_wfRel
    Encodable.choose (h.wf.has_min (condition f n) (condition_existence f smono))

  lemma inv_order_inverse_r {y : ℕ} : f (inv f smono y) ≥ y := by
    have p := Encodable.choose_spec (Nat.lt_wfRel.wf.has_min (condition f y) (condition_existence f smono))
    revert p
    simp [Nat.lt_wfRel]
    intros
    assumption

  lemma inv_adj_l {y : ℕ} : ∀{x}, (f x ≥ y) → (x ≥ inv f smono y) := by
    have p := Encodable.choose_spec (Nat.lt_wfRel.wf.has_min (condition f y) (condition_existence f smono))
    revert p
    simp [Nat.lt_wfRel]
    intro _ _
    assumption

  lemma inv_order_inverse_l {x : ℕ} : inv f smono (f x) ≤ x := by
    apply inv_adj_l f smono
    omega

  lemma inv_adj_r {x y : ℕ} (p : x ≥ inv f smono y) : (f x ≥ y)
    := (inv_order_inverse_r f smono).trans (smono.monotone p)

  lemma inv_monotone : Monotone (inv f smono)
    := fun _ _ p => inv_adj_l f smono (p.trans (inv_order_inverse_r f smono))

  def inv_galoisConnection : GaloisConnection (inv f smono) f :=
    GaloisConnection.monotone_intro (l := inv f smono)
      smono.monotone
      (inv_monotone f smono)
      (fun _ => inv_order_inverse_r f smono)
      (fun _ => inv_order_inverse_l f smono)

  instance functor_final : Functor.Final smono.monotone.functor
    := Functor.final_of_adjunction (GaloisConnection.adjunction (inv_galoisConnection f smono))

  noncomputable def comp_seqColim_iso
    {C : Type _} [Category C]
    {F : ℕ ⥤ C} [HasColimit F] [HasColimit (smono.monotone.functor ⋙ F)] -- TODO: Cannot find Functor.Final.comp_hasColimit?
    : colimit (smono.monotone.functor ⋙ F) ≅ colimit F
    :=
      let _ := functor_final f smono
      Functor.Final.colimitIso smono.monotone.functor F

end Nat.StrictMono

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
