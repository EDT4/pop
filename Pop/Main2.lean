import Init.Core
import Init.Prelude
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Algebra.Ring.Parity
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout
-- import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.FullSubcategory

import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.NatExtras

open CategoryTheory
open CategoryTheory.Limits

set_option autoImplicit true

section
  variable {A B C : Type u}
  variable [Category.{v, u} A]
  variable [Category.{v, u} B]
  variable [Category.{v, u} C]

  variable [∀{X Y Z : C}{f : X ⟶ Z}{g : Y ⟶ Z}, HasPullback f g]
  variable [∀{X Y Z : C}{f : X ⟶ Y}{g : X ⟶ Z}, HasPushout f g]
  variable [∀{s : Seq C}, HasSeqColimit s]

  -- TODO: Is this true?
  instance instHasSeqColimitEndofunctor
    : [∀{s : Seq C}, HasSeqColimit s]
    → (∀{s : Seq (Functor C C)}, HasSeqColimit s)
    := sorry

  -- TODO: Maybe reflective subcategories preserve the property of having limits?
  -- TODO: But now it is currently unused
  -- theorem instHasSeqColimit_of_reflective
  --   {F : Functor A B} [Reflective F]
  --   : [∀{f : SeqDiagram B}, HasSeqColimit f]
  --   → (∀{f : SeqDiagram A}, HasSeqColimit f)
  --   := hasColimitsOfShape_of_reflective _

  section
    variable [∀{s : Seq A}, HasSeqColimit s]
    variable [∀{s : Seq B}, HasSeqColimit s]
    variable [HasLimits Cat] -- TODO: CategoryTheory.Cat.instHasLimits? Maybe check universes?

    -- TODO: 2-categories later. Correct using Mathlib.CategoryTheory.Bicategory.Basic and Mathlib.CategoryTheory.Bicategory.Functor.Oplax? (https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Basic.html#CategoryTheory.Bicategory)
    def lem1
      [∀{s : Seq C}, HasSeqColimit s]
      (F : Functor A C) [Reflective F] [PreservesColimitsOfShape ℕ F]
      (G : Functor B C) [Reflective G] [PreservesColimitsOfShape ℕ G]
      : Σ H : Functor (pullback (C := Cat) (X := Cat.of A) (Y := Cat.of B) (Z := Cat.of C) F G) C, Reflective H :=
        let TA : Functor C C := Adjunction.toMonad (reflectorAdjunction F)
        let TB : Functor C C := Adjunction.toMonad (reflectorAdjunction G)

        let Minf (x : C) : C :=
          let ηA := (Adjunction.toMonad (reflectorAdjunction F)).η.app
          let ηB := (Adjunction.toMonad (reflectorAdjunction G)).η.app
          let M : ℕ → C := Nat.rec2 x (fun _ _ => TA.obj) (fun _ _ => TB.obj)
          let Mmap (n : ℕ) : M n ⟶ M (n + 1) :=
            Decidable.casesOn (Nat.instDecidablePredEven n)
              (fun (p : ¬Even n) => by
                simp [M]
                rewrite [Nat.rec2_odd_step p]
                exact ηB (M n)
              )
              (fun (p :  Even n) => by
                simp [M]
                rewrite [Nat.rec2_even_step p]
                exact ηA (M n)
              )
          let Mseq : Seq C := .mk M Mmap
          let Minf := seqColim Mseq
          let ι := seqColim.ι Mseq
          let testA n := ι n ≫ ηA Minf = ηA (M n) ≫ TA.map (ι n)
          let testB n := ι n ≫ ηB Minf = ηB (M n) ≫ TB.map (ι n)
          Minf

        .mk
          (.mk
            (.mk
              (fun p => sorry)
              sorry
            )
            sorry
            sorry
          )
          sorry
  end
end
