import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Data.Set.Defs
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.NatCategoryExtras
import Pop.NatExtras
import Pop.Util

set_option pp.proofs true

section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

variable {C : Type _}
variable [Category C]
  -- TODO: Change these later
variable [HasPullbacks C]
variable [HasPushouts C]
variable [HasSeqColimits C]

namespace Adjunction.CoreHom
  variable {C₁ C₂ : Type _}
  variable [Category C₁]
  variable [Category C₂]
  variable {F : Functor C₁ C₂}
  variable {G : Functor C₂ C₁}
  variable (η : 𝟭 C₁ ⟶ F ⋙ G)

  abbrev hom {c₁ : C₁} {c₂ : C₂} : (F.obj c₁ ⟶ c₂) → (c₁ ⟶ G.obj c₂)
    := fun f => η.app c₁ ≫ G.map f

  -- variable (e : (c₁ : C₁) → (c₂ : C₂) → (F.obj c₁ ⟶ c₂) ≃ (c₁ ⟶ G.obj c₂))

  def mk
    (invHom : ∀{c₁ : C₁}{c₂ : C₂}, (c₁ ⟶ G.obj c₂) → (F.obj c₁ ⟶ c₂))
    (left_inv  : ∀{c₁}{c₂}, Function.LeftInverse  invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    (right_inv : ∀{c₁}{c₂}, Function.RightInverse invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    : F ⊣ G
    :=
      Adjunction.mkOfHomEquiv {
        homEquiv := fun _ _ => .mk (hom η) invHom left_inv right_inv
        homEquiv_naturality_left_symm := by
          intro c₁₁ c₁₂ c₂ f g
          simp
          apply_fun hom η
          . rw [right_inv]
            simp [hom]
            rewrite [← Category.assoc , ← Functor.comp_map , ← η.naturality f]
            simp
            congr
            change g = hom η (invHom g)
            rw [right_inv]
          . exact Function.LeftInverse.injective left_inv
        homEquiv_naturality_right := by simp [hom]
      }
      -- let e d := invHom (𝟙 (G.obj d))
      -- let ε : (G ⋙ F) ⟶ 𝟭 C₂ := {
      --   app := e
      --   naturality := by
      --     intro d₁ d₂ f
      --     simp
      --     let eq : ∀{d}, hom η (e d) = 𝟙 (G.obj d) := by aesop_cat
      --     repeat rewrite [← eq,left_inv]
      --     simp [e]
      --     sorry
      -- }
      -- Adjunction.mk' {
      --   homEquiv := fun _ _ => .mk (hom η) invHom left_inv right_inv
      --   unit := η
      --   counit := ε
      --   -- .mk fun d => (e (G.obj d) d).symm.toFun (𝟙 (G.obj d))
      -- }
end Adjunction.CoreHom

local instance temp : (Nat.Functor.mulr 2).Final := Nat.Functor.mulr_final -- TODO: Cannot find this instance?

noncomputable def lem1
  -- TODO: Reflective includes full and faithful, but it is already implied by F and G. Maybe not a problem?
  (A : Set C)
  [IsClosedUnderIsomorphisms A]
  [Reflective (fullSubcategoryInclusion A)]
  (closed_a : ClosedUnderColimitsOfShape ℕ A)
  (B : Set C)
  [IsClosedUnderIsomorphisms B]
  [Reflective (fullSubcategoryInclusion B)]
  (closed_b : ClosedUnderColimitsOfShape ℕ B)
  : Reflective (fullSubcategoryInclusion (A ∩ B : Set C))
  :=
    let TA : Monad C := (reflectorAdjunction (fullSubcategoryInclusion A)).toMonad
    let TB : Monad C := (reflectorAdjunction (fullSubcategoryInclusion B)).toMonad
    let M : Limits.Seq (C ⥤ C) := (Seq.iterate2 (c := Cat.of C) TA.toFunctor TB.toFunctor TA.η TB.η) -- TODO: step should probably not be here, but on the subset
    let Minf : C ⥤ C := seqColim M -- TODO: Change later to computable
    let inA : ∀(c : C), A (Minf.obj c) := by -- TODO: inA and inB uses the same argument and should be generalised in the future
      intro c
      apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
      apply IsClosedUnderIsomorphisms.of_iso (Functor.Final.colimitIso (Nat.Functor.mulr 2 ⋙ Nat.Functor.succ) _)
      apply ClosedUnderColimitsOfShape.colimit closed_a
      simp [Nat.Functor.mulr]
      intro n
      induction n generalizing A closed_a B closed_b c
      . exact FullSubcategory.property _
      . rw [Nat.add_mul] ; apply_assumption <;> assumption

    let inB : ∀(c : C), B (Minf.obj c) := by
      intro c
      apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
      apply IsClosedUnderIsomorphisms.of_iso (Functor.Final.colimitIso (Nat.Functor.mulr 2 ⋙ Nat.Functor.succ ⋙ Nat.Functor.succ) _)
      apply ClosedUnderColimitsOfShape.colimit closed_b
      simp [Nat.Functor.mulr]
      intro n
      induction n generalizing A closed_a B closed_b c
      . exact FullSubcategory.property _
      . rw [Nat.add_mul] ; apply_assumption <;> assumption

    let L := FullSubcategory.lift (A ∩ B : Set C) Minf (fun c => .intro (inA c) (inB c))
    let l {c} : L.obj ((fullSubcategoryInclusion (A ∩ B : Set C)).obj c) ⟶ c
      := by simp [L] ; sorry
    {
      L := L
      adj := Adjunction.CoreHom.mk
        (seqColim.ι M 0)
        (fun f => L.map f ≫ l) -- TODO: Either construct this directly or just prove that Adjunction.CoreHom.hom is bijective from the full faithful functors
        sorry
        sorry
    }



end
