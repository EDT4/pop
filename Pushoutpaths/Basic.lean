import Init.Core
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout

namespace CategoryTheory

set_option autoImplicit true

-- TODO: cleanup later
section
  variable (C : Type u) [Category.{v, u} C]
  variable [∀{X Y Z : C}{f : X ⟶ Z}{g : Y ⟶ Z}, Limits.HasPullback f g]
  variable [∀{X Y Z : C}{f : X ⟶ Y}{g : X ⟶ Z}, Limits.HasPushout f g]

  section
    -- 2.9
    -- See Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
  end

  section
    -- 3.1
    abbrev Span := Functor Limits.WalkingSpan C

    variable {p q r : C} {pq : p ⟶ q} {pr : p ⟶ r}
    variable {a b c : C} {ab : a ⟶ b} {ac : a ⟶ c}
    variable {s1 s2 : Span C}
    variable {m : s1 ⟶ s2}

    -- TODO: For convenience at the moment
    -- TODO: Is it possible to just auto import these?
    abbrev SpanMap.left  (m : s1 ⟶ s2) := m.app Limits.WalkingCospan.left
    abbrev SpanMap.one   (m : s1 ⟶ s2) := m.app Limits.WalkingCospan.one
    abbrev SpanMap.right (m : s1 ⟶ s2) := m.app Limits.WalkingCospan.right

    -- TODO: Probably no need to make this so explicit.
    -- TODO: Also, there should probably be some nice shorter category theoretical way of expressing this
    structure Fact31 (m : s1 ⟶ s2) where
      span : Span C

      -- x := span.obj Limits.WalkingSpan.zero
      -- y := span.obj Limits.WalkingSpan.left
      -- z := span.obj Limits.WalkingSpan.right
      -- xy := span.map Limits.WalkingSpan.Hom.fst
      -- xz := span.map Limits.WalkingSpan.Hom.snd

      m1 : s1 ⟶ span
      m2 : span ⟶ s2
      correct : NatTrans.vcomp m1 m2 = m

    -- TODO: not nice. improve later. maybe using something like squares
    -- TODO: Also, look up if it is possible to specify implicit args and if it is possible positionally also
    def factor_l (m : s1 ⟶ s2) : Fact31 C m :=
      let pq := s1.map Limits.WalkingSpan.Hom.fst
      let pr := s1.map Limits.WalkingSpan.Hom.snd
      let ab := s2.map Limits.WalkingSpan.Hom.fst
      let ac := s2.map Limits.WalkingSpan.Hom.snd

      let qb := SpanMap.left  C m
      let pa := SpanMap.one   C m
      let rc := SpanMap.right C m

      let pqb_pab : pq ≫ qb = pa ≫ ab := sorry
      let px := Limits.pullback.lift pq pa pqb_pab
      let qy := CategoryStruct.id q
      -- let rz := sorry

      let xy := Limits.pullback.fst qb ab
      let xz := Limits.pushout.inl px pr

      let x := Limits.pullback qb ab
      let y := q
      let z := Limits.pushout px pr
      Fact31.mk
        (Limits.span xy xz)
        sorry
        sorry
        sorry

    -- TODO: Similar to factor_l but find some more structure before writing this one
    def factor_r (m : s1 ⟶ s2) : Fact31 C m := sorry

    -- 3.4
    -- TODO: inefficient implementation
    -- TODO: Maybe not useful to define it like this?
    def zigzag : (m : s1 ⟶ s2) → Nat → Fact31 C m
      | m , Nat.zero   => m
      | m , Nat.succ n => factor_l ((factor_r ((zigzag m n).m2)).m2)
  end
end
