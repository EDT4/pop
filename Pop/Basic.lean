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

  section
    -- 2.9
    -- See Mathlib.CategoryTheory.Shapes.Pullback.Pasting
  end

  section
    -- 3.1
    abbrev Span (C : Type u) [Category.{v, u} C] := Functor WalkingSpan C

    variable {p q r : C} {pq : p ⟶ q} {pr : p ⟶ r}
    variable {a b c : C} {ab : a ⟶ b} {ac : a ⟶ c}
    variable {s s1 s2 : Span C}
    variable {m : s1 ⟶ s2}

    -- TODO: For convenience at the moment
    -- TODO: Is it possible to just auto import these?
    abbrev SpanMap.left  (m : s1 ⟶ s2) := m.app WalkingCospan.left
    abbrev SpanMap.one   (m : s1 ⟶ s2) := m.app WalkingCospan.one
    abbrev SpanMap.right (m : s1 ⟶ s2) := m.app WalkingCospan.right

    -- TODO: There should probably be some nice shorter category theoretical way of expressing this
    structure Factor (f : a ⟶ b) where
      common : C
      left : a ⟶ common
      right : common ⟶ b
      correct : left ≫ right = f

    -- TODO: Able to specify the limits => computable
    noncomputable def factor_l (m : s1 ⟶ s2) : Factor m :=
      let p := s1.obj WalkingSpan.zero
      let q := s1.obj WalkingSpan.left
      let r := s1.obj WalkingSpan.right

      let a := s2.obj WalkingSpan.zero
      let b := s2.obj WalkingSpan.left
      let c := s2.obj WalkingSpan.right

      let pq : p ⟶ q := s1.map WalkingSpan.Hom.fst
      let pr : p ⟶ r := s1.map WalkingSpan.Hom.snd
      let ab : a ⟶ b := s2.map WalkingSpan.Hom.fst
      let ac : a ⟶ c := s2.map WalkingSpan.Hom.snd

      -- let test := s1.map

      let qb : q ⟶ b := SpanMap.left  m
      let pa : p ⟶ a := SpanMap.one   m
      let rc : r ⟶ c := SpanMap.right m

      let x := pullback qb ab
      let y := q

      let pqb_pab : pq ≫ qb = pa ≫ ab := by aesop_cat
      let px : p ⟶ x := pullback.lift pq pa pqb_pab
      let qy : q ⟶ y := CategoryStruct.id q

      let z := pushout px pr
      let rz : r ⟶ z := pushout.inr px pr

      let xy : x ⟶ y := pullback.fst qb ab
      let xz : x ⟶ z := pushout.inl px pr

      let xa : x ⟶ a := pullback.snd qb ab
      let yb : y ⟶ b := qb
      let pac_prc : px ≫ (xa ≫ ac) = pr ≫ rc := by aesop_cat
      let zc : z ⟶ c := pushout.desc (xa ≫ ac) rc pac_prc

      { common := span xy xz
      , left := .mk
          (by rintro (_ | _ | _) <;> assumption)
          (by
            rintro (_ | _ | _) (_ | _ | _) _
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
            . simp ; sorry
          )
      , right := .mk
          (by rintro (_ | _ | _) <;> assumption)
          sorry
      , correct := sorry
      }

    noncomputable def factor_l' (o1 : Over s) : Σ o2, o1 ⟶ o2 :=
      let fa := factor_l o1.hom
      Sigma.mk (Over.mk fa.right) (Over.homMk fa.left fa.correct)

    -- TODO: Not sure if this is helping. How is it an endofunctor?
    noncomputable def factor_l'' (o : Over s) : Under o :=
      let fa := factor_l o.hom
      Under.mk (Y := Over.mk fa.right) (Over.homMk fa.left fa.correct)

    -- TODO: Like this?
    -- def factor_l'' : Functor (Over s) (Over s) :=
    --   { obj := fun o ↦ (factor_l' C o).fst
    --   , map := sorry
    --   , map_id := sorry
    --   , map_comp := sorry
    --   }
    -- by
    -- -- let fa := factor_l' s
    --   constructor
    --   . sorry
    --   . sorry
    --   . constructor
    --     . sorry
    --     . exact fun o => (factor_l' C o).1

    -- TODO: Similar to factor_l but find some more structure before writing this one
    noncomputable def factor_r (m : s1 ⟶ s2) : Factor m := sorry

    -- 3.4
    -- TODO: Finish graph morphisms above and make use of it here instead
    def zigzag (m : s1 ⟶ s2) : SeqDiagram (Over s2) :=
      SeqDiagram.byRepeat (C := Over s2) (Over.map sorry) sorry -- TODO: give this some thought
  end







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
