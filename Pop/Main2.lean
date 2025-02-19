import Init.Core
import Init.Prelude
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Combinatorics.Quiver.Basic
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout

import Pop.CategoryTheory.Limits.Shapes.SeqColimit

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

  instance instHasSeqColimitEndofunctor
    : [∀{s : Seq C}, HasSeqColimit s]
    → (∀{s : Seq (Functor C C)}, HasSeqColimit s)
    := sorry

  -- TODO: Maybe reflective subcategories preserve the property of having limits?
  -- theorem instHasSeqColimit_of_reflective
  --   {F : Functor A B} [Reflective F]
  --   : [∀{f : SeqDiagram B}, HasSeqColimit f]
  --   → (∀{f : SeqDiagram A}, HasSeqColimit f)
  --   := hasColimitsOfShape_of_reflective _

  section
    variable [∀{s : Seq A}, HasSeqColimit s]
    variable [∀{s : Seq B}, HasSeqColimit s]
    variable [HasLimits Cat] -- TODO: CategoryTheory.Cat.instHasLimits?

    -- ∀{f : SeqDiagram C}, (∀{x}, f x in A) → (seqColim f in A)
    -- ∀{f : SeqDiagram A}, F.obj (seqColim f) = seqColim (Functor.comp f F)
    -- (pa : ∀{s : Seq A}, F.obj (colimit s.diagram) = colimit (Functor.comp s.diagram F))
    -- TODO: 2-categories later. Correct using Mathlib.CategoryTheory.Bicategory.Basic and Mathlib.CategoryTheory.Bicategory.Functor.Oplax? (https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Basic.html#CategoryTheory.Bicategory)
    def lem1
      [∀{s : Seq C}, HasSeqColimit s]
      (F : Functor A C) [Reflective F] [PreservesColimitsOfShape ℕ F]
      (G : Functor B C) [Reflective G] [PreservesColimitsOfShape ℕ G]
      : Σ H : Functor (pullback (C := Cat) (X := Cat.of A) (Y := Cat.of B) (Z := Cat.of C) F G) C, Reflective H :=
        let TA : Functor C C := Adjunction.toMonad (reflectorAdjunction F)
        let TB : Functor C C := Adjunction.toMonad (reflectorAdjunction G)

        -- let Mzero  := Functor.id C
        -- let MsuccA := (whiskeringRight C C C).obj TA
        -- let MsuccB := (whiskeringRight C C C).obj TB
        -- let Msucc  := MsuccA ⋙ MsuccB
        -- let Mseq   := Seq.byRepeat' Msucc (.mk (by dsimp [Msucc , MsuccA , MsuccB , TA , TB] ; sorry)) Mzero
        -- let Minf   := seqColim Mseq

        -- let test := Minf ⋙ reflector F
        -- let test2 := pullback (C := Cat) (X := Cat.of A) (Y := Cat.of B) (Z := Cat.of C) F G
        -- let test3 := seqColim.desc (W := Minf) Mseq sorry sorry
        -- let test4 := seqColim.ι Mseq
        -- let test5 := test2.str.id

        let Minf (x : C) : C :=
          let ηA := (Adjunction.toMonad (reflectorAdjunction F)).η.app
          let ηB := (Adjunction.toMonad (reflectorAdjunction G)).η.app -- (reflectorAdjunction G).unit
          let rec M (n : ℕ) : C := Nat.rec (fun _ _ => x) (fun _ r T1 T2 => T1 (r T2 T1)) n TA.obj TB.obj
          -- let rec M (n : ℕ) : C := match n with
          -- | 0     => x
          -- | n + 1 => TA.obj (M n)
          let MeqA {n : ℕ} (p :  Even n) : M n.succ = TA.obj (M n) := sorry -- TODO: How to reduce M?
          let MeqB {n : ℕ} (p : ¬Even n) : M n.succ = TB.obj (M n) := sorry
          let Mmap (n : ℕ) : M n ⟶ M (n + 1) :=
            Decidable.casesOn (Nat.instDecidablePredEven n)
              (fun (p : ¬Even n) => by
                rewrite [MeqB p]
                exact ηB (M n)
              )
              (fun (p :  Even n) => by
                rewrite [MeqA p]
                exact ηA (M n)
              )
            -- if decide (Even n)
            -- then (by
            --   rewrite [MeqA]
            --   exact ηA (M n)
            -- ) else (by
            --   rewrite [MeqB sorry]
            --   exact ηB (M n)
            -- )
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

-- TODO: Old references before code removal: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Basic.html https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Basic.html#CategoryTheory.Comma
