import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Whiskering
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout

open CategoryTheory
open CategoryTheory.Limits

set_option autoImplicit true

-- TODO: cleanup and organise later
section
  -- TODO: Look up if it is possible to specify implicit args and also if it is possible positionally
  variable {A B C : Type u} [Category.{v, u} C]

  -- TODO: Is this correct? It will probably be clear later
  -- TODO: Lookup cofiltered category and tower diagrams
  section SequentialColimits
    abbrev SeqDiagram (C : Type u) [Category.{v, u} C] := Functor ℕ C

    def seqByRepeat (f : Functor C C) (z : C) (zm : z ⟶ f.obj z) : SeqDiagram C :=
      let o (n : ℕ) : C := Nat.repeat f.obj n z
      let rec m (n : ℕ) : o n ⟶ o (n + 1) := match n with
        | Nat.zero   => zm
        | Nat.succ n => f.map (m n)
      Functor.ofSequence m

    -- TODO: Pointed endofunctor (NatTrans (Functor.id C) f) instead of zm, but what would the naturality give?
    def seqByRepeat' (f : Functor C C) (m : NatTrans (Functor.id C) f) (z : C) : SeqDiagram C :=
      seqByRepeat f z (m.app z)

    abbrev HasSequentialColimit(f : SeqDiagram C) := HasColimit f
    noncomputable abbrev seqColim (f : SeqDiagram C) [HasSequentialColimit f] := colimit f
  end SequentialColimits

  variable [∀{X Y Z : C}{f : X ⟶ Z}{g : Y ⟶ Z}, HasPullback f g]
  variable [∀{X Y Z : C}{f : X ⟶ Y}{g : X ⟶ Z}, HasPushout f g]
  variable [∀{f : SeqDiagram C}, HasSequentialColimit f]

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
      seqByRepeat (C := Over s2) (Over.map sorry) sorry sorry -- TODO: give this some thought
  end





  section
    -- variable [∀{f : SeqDiagram C}, HasSequentialColimit f]
    variable [∀{f : SeqDiagram (Functor C C)}, HasSequentialColimit f] -- TODO: temporary
    variable [Category.{v, u} A]
    variable [Category.{v, u} B]

    def lem1
      (F : Functor A C) [Reflective F]
      (G : Functor B C) [Reflective G]
      : sorry := -- TODO: ?    Σ S : Type u, Σ Category S, Σ H : Functor S C, Reflective H
        let ηA := (reflectorAdjunction F).unit
        let ηB := (reflectorAdjunction G).unit
        let TA : Functor C C := Adjunction.toMonad (reflectorAdjunction F)
        let TB : Functor C C := Adjunction.toMonad (reflectorAdjunction G)
        -- (Functor.comp (Functor.comp TB TA))
        let Mzero := Functor.id C
        -- let Msucc := .mk
        --   (.mk
        --     (fun f => Functor.comp f (Functor.comp TB TA))
        --     (fun f => by simp ; sorry)
        --   )
        --   sorry
        --   sorry
        -- let test := whiskerRight ηA TA
        -- let Msucc := .mk
        --   (.mk
        --     (fun f => Functor.comp f TA)
        --     (fun f => whiskerRight f TA)
        --   )
        --   sorry
        --   sorry
        let MsuccA := (whiskeringRight C C C).obj TA
        let MsuccB := (whiskeringRight C C C).obj TB
        let Minf := seqColim (C := Functor C C) (seqByRepeat (C := Functor C C) (Functor.comp MsuccB MsuccA) Mzero (.mk sorry))
        sorry
  end
end
