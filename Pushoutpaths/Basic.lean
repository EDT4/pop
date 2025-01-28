import Init.Core
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout

namespace CategoryTheory

set_option autoImplicit true

-- TODO: cleanup later
section
  variable {C : Type u} [Category.{v, u} C]
  variable [∀{X Y Z : C}{f : X ⟶ Z}{g : Y ⟶ Z}, Limits.HasPullback f g]
  variable [∀{X Y Z : C}{f : X ⟶ Y}{g : X ⟶ Z}, Limits.HasPushout f g]

  section
    -- 2.9
    -- pasteHorizIsPullbackEquiv or leftSquareIsPullback ?
  end

  section
    -- 3.1
    section
      variable {a1 b1 c1 : C} {a2 b2 c2 : C}
      variable {l1 : a1 ⟶ b1} {r1 : a1 ⟶ c1} {l2 : a2 ⟶ b2} {r2 : a2 ⟶ c2}

      -- TODO: Just for convenience at the moment
      abbrev SpanMap(l1 : a1 ⟶ b1) (r1 : a1 ⟶ c1) (l2 : a2 ⟶ b2) (r2 : a2 ⟶ c2)
        := NatTrans (Limits.span l1 r1) (Limits.span l2 r2)
      -- TODO: Is it possible to just auto import these?
      abbrev SpanMap.left  (m : SpanMap l1 r1 l2 r2) := m.app Limits.WalkingCospan.left
      abbrev SpanMap.one   (m : SpanMap l1 r1 l2 r2) := m.app Limits.WalkingCospan.one
      abbrev SpanMap.right (m : SpanMap l1 r1 l2 r2) := m.app Limits.WalkingCospan.right
    end

    variable {p q r : C} {pq : p ⟶ q} {pr : p ⟶ r}
    variable {a b c : C} {ab : a ⟶ b} {ac : a ⟶ c}
    variable {m : SpanMap pq pr ab ac}

    -- TODO: Probably no need to make this so explicit.
    -- TODO: Also, there should probably be some nice shorter category theoretical way of expressing this
    -- TODO: There must be a better way to refer to a span bundle or do we have to write our own? The params are getting ridiculous
    structure Fact31 (m : SpanMap pq pr ab ac) where
      x : C
      y : C
      z : C
      xy : x ⟶ y
      xz : x ⟶ z
      m1 : SpanMap xy xz ab ac
      m2 : SpanMap pq pr xy xz
      correct : NatTrans.vcomp m2 m1 = m

    -- TODO: not nice. improve later. maybe using something like squares
    -- TODO: Also, look up if it is possible to specify implicit args and if it is possible positionally also
    def factor_l (m : SpanMap pq pr ab ac) : Fact31 m :=
      let qb := SpanMap.left  m
      let pa := SpanMap.one   m
      let rc := SpanMap.right m

      let pqb_pab : pq ≫ qb = pa ≫ ab := sorry
      let px := Limits.pullback.lift pq pa pqb_pab
      let qy := CategoryStruct.id q
      -- let rz := sorry

      let xy := Limits.pullback.fst qb ab
      let xz := Limits.pushout.inl px pr

      let x := Limits.pullback qb ab
      let y := q
      let z := Limits.pushout px pr
      Fact31.mk x y z xy xz
        sorry
        sorry
        sorry

    -- TODO: Similar to factor_l but find some more structure before writing this one
    def factor_r (m : SpanMap pq pr ab ac) : Fact31 m := sorry


    -- 3.4
    -- TODO: inefficient implementation
    -- TODO: Maybe not useful to define it like this?
    def zigzag : (m : SpanMap pq pr ab ac) → Nat → Fact31 m
      | m , Nat.zero   => m
      | m , Nat.succ n => factor_l ((factor_r ((zigzag m n).m2)).m2)
  end
end
