import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Combinatorics.Quiver.Basic
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout

import Pop.CategoryTheory.Limits.Shapes.SeqColimit

open CategoryTheory
open CategoryTheory.Limits

set_option autoImplicit true

-- TODO: cleanup and organise later
section
  variable {A B C : Type u}
  variable [Category.{v, u} A]
  variable [Category.{v, u} B]
  variable [Category.{v, u} C]

  variable [∀{X Y Z : C}{f : X ⟶ Z}{g : Y ⟶ Z}, HasPullback f g]
  variable [∀{X Y Z : C}{f : X ⟶ Y}{g : X ⟶ Z}, HasPushout f g]
  variable [∀{f : SeqDiagram C}, HasSeqColimit f]

  instance instHasSeqColimitEndofunctor
    : [∀{f : SeqDiagram C}, HasSeqColimit f]
    → (∀{f : SeqDiagram (Functor C C)}, HasSeqColimit f)
    := sorry

  -- TODO: Reflective subcategories probably preserve the property of having limits?
  -- theorem instHasSeqColimit_of_reflective
  --   {F : Functor A B} [Reflective F]
  --   : [∀{f : SeqDiagram B}, HasSeqColimit f]
  --   → (∀{f : SeqDiagram A}, HasSeqColimit f)
  --   := hasColimitsOfShape_of_reflective _

  section
    variable [∀{f : SeqDiagram C}, HasSeqColimit f]
    -- variable [∀{f : SeqDiagram A}, HasSeqColimit f]
    -- variable [∀{f : SeqDiagram B}, HasSeqColimit f]
    variable [HasLimits Cat] -- TODO: CategoryTheory.Cat.instHasLimits?

    -- ∀{f : SeqDiagram C}, (∀{x}, f x in A) → (seqColim f in A)
    -- ∀{f : SeqDiagram A}, F.obj (seqColim f) = seqColim (Functor.comp f F)
    def lem1
      (F : Functor A C) [Reflective F]
      (G : Functor B C) [Reflective G]
      : Σ H : Functor (pullback (C := Cat) (X := Cat.of A) (Y := Cat.of B) (Z := Cat.of C) F G) C, Reflective H :=
        let TA : Functor C C := Adjunction.toMonad (reflectorAdjunction F)
        let TB : Functor C C := Adjunction.toMonad (reflectorAdjunction G)
        let Mzero  := Functor.id C
        let MsuccA := (whiskeringRight C C C).obj TA
        let MsuccB := (whiskeringRight C C C).obj TB
        let Msucc  := Functor.comp MsuccB MsuccA
        let Minf   := seqColim (SeqDiagram.byRepeat' Msucc (.mk sorry) Mzero)

        .mk
          (.mk
            (.mk
              sorry
              sorry
            )
            sorry
            sorry
          )
          sorry
  end
end

-- TODO: Old references before code removal: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Basic.html https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Basic.html#CategoryTheory.Comma
