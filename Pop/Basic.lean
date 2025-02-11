import Init.Core
import Init.Prelude
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Whiskering
-- import Mathlib.CategoryTheory.Limits.Shapes.Pushout.HasPushout

namespace CategoryTheory

set_option autoImplicit true

-- TODO: cleanup and organise later
section
  -- TODO: Look up if it is possible to specify implicit args and also if it is possible positionally
  variable (C : Type u) [Category.{v, u} C]

  -- TODO: Is this correct? It will probably be clear later
  section SequentialColimits
    abbrev Seq := Functor ℕ C -- TODO: What should this be called? Some kind of shape?
    -- TODO: Does using an endofunctor work?
    -- TODO: Wait, is this not just reproving that the reflexive-transitive closure of a graph is a category?
    def seqByRepeat (z : C) (f : Functor C C) : Seq C :=
      let o (n : ℕ) : C := Nat.repeat f.obj n z
      let rec m {a b : ℕ} (ord : a ⟶ b) : o a ⟶ o b := match a , b with
        | Nat.zero   , Nat.zero   => CategoryStruct.id z
        | Nat.zero   , Nat.succ y => sorry
        | Nat.succ x , Nat.succ y => f.map (m (CategoryTheory.homOfLE (Nat.le_of_succ_le_succ ord.le)))
      Functor.mk (Prefunctor.mk o m) sorry sorry

    -- TODO: And how are the functors related to each other? Something related to `Factor` probably, but is this approach working?
    def seqByAlternating (z : C) (f g : Functor C C) : Seq C := sorry

    abbrev HasSequentialColimit(f : Seq C) := Limits.HasColimit f
    abbrev seqColim (f : Seq C) [HasSequentialColimit C f] := Limits.colimit f
  end SequentialColimits

  variable [∀{X Y Z : C}{f : X ⟶ Z}{g : Y ⟶ Z}, Limits.HasPullback f g]
  variable [∀{X Y Z : C}{f : X ⟶ Y}{g : X ⟶ Z}, Limits.HasPushout f g]
  variable [∀{f}, HasSequentialColimit C f]

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

    -- TODO: There should probably be some nice shorter category theoretical way of expressing this
    structure Factor (f : a ⟶ b) where
      common : C
      left : a ⟶ common
      right : common ⟶ b
      correct : left ≫ right = f

    -- TODO: But wait, is this correctly formalised?
    -- TODO: not nice. improve later. maybe using something like squares?
    def factor_l (m : s1 ⟶ s2) : Factor (Span C) m := by
      let p := s1.obj Limits.WalkingSpan.zero
      let q := s1.obj Limits.WalkingSpan.left
      let r := s1.obj Limits.WalkingSpan.right

      let a := s2.obj Limits.WalkingSpan.zero
      let b := s2.obj Limits.WalkingSpan.left
      let c := s2.obj Limits.WalkingSpan.right

      let pq : p ⟶ q := s1.map Limits.WalkingSpan.Hom.fst
      let pr : p ⟶ r := s1.map Limits.WalkingSpan.Hom.snd
      let ab : a ⟶ b := s2.map Limits.WalkingSpan.Hom.fst
      let ac : a ⟶ c := s2.map Limits.WalkingSpan.Hom.snd

      let qb : q ⟶ b := SpanMap.left  C m
      let pa : p ⟶ a := SpanMap.one   C m
      let rc : r ⟶ c := SpanMap.right C m

      let x := Limits.pullback qb ab
      let y := q

      let pqb_pab : pq ≫ qb = pa ≫ ab := sorry
      let px : p ⟶ x := Limits.pullback.lift pq pa pqb_pab
      let qy : q ⟶ y := CategoryStruct.id q

      let z := Limits.pushout px pr
      let rz : r ⟶ z := Limits.pushout.inr px pr

      let xy : x ⟶ y := Limits.pullback.fst qb ab
      let xz : x ⟶ z := Limits.pushout.inl px pr

      let xa : x ⟶ a := Limits.pullback.snd qb ab
      let yb : y ⟶ b := qb
      let pac_prc : px ≫ (xa ≫ ac) = pr ≫ rc := sorry
      let zc : z ⟶ c := Limits.pushout.desc (xa ≫ ac) rc pac_prc

      constructor
      . sorry
      . exact Limits.span xy xz
      . constructor
        · sorry
        · intro i
          cases i with
          | none => assumption
          | some j => cases j <;> assumption
      . constructor
        · sorry
        · intro i
          cases i with
          | none => assumption
          | some j => cases j <;> assumption

    -- TODO: Similar to factor_l but find some more structure before writing this one
    def factor_r (m : s1 ⟶ s2) : Factor (Span C) m := sorry

    -- 3.4
    -- TODO: Finish graph morphisms above and make use of it here instead
    def zigzag (m : s1 ⟶ s2) : Seq (Span C) :=
      seqByAlternating (Span C) s1 (Functor.mk _ _ _) sorry -- TODO: give this some thought
  end




  -- variable (A B : Type u) [Category.{v, u} A] [Category.{v, u} B]
  -- variable {F : Functor A C} {G : Functor B C}
  -- variable [Reflective F] [Reflective G]

  -- TODO: Something is probably incorrect here
  def lem1 -- TODO: Universes? Use variable instead later
    {C A B : Type u} [Category.{v, u} C] [Category.{v, u} A] [Category.{v, u} B]
    (F : Functor A C) [Reflective F]
    (G : Functor B C) [Reflective G]
    [∀{f}, HasSequentialColimit C f]
    : sorry := -- Σ S : Type u, Σ Category S, Σ H : Functor S C, Reflective H
      let ηA := (reflectorAdjunction F).unit
      let ηB := (reflectorAdjunction G).unit
      let TA : Functor C C := Adjunction.toMonad (reflectorAdjunction F)
      let TB : Functor C C := Adjunction.toMonad (reflectorAdjunction G)
      -- TODO: Is M a functor? But maybe that would not help
      let rec M : ℕ → Functor C C := fun n => match n with -- TODO: Is this ok or is it easier with even/odd?
        | 0     => Functor.id C
        | 1     => TB
        | n + 2 => Functor.comp TB (Functor.comp TA (M n))
      -- TODO: should probably try to define M and Msucc simultaneously in some way?
      let Msucc (n : ℕ) := whiskerRight ηA (M n) -- TODO: ?   -- : M n ⟶ M (Nat.succ n)
      -- let Minf := seqColim C (seqByRepeat C _ _) -- TODO: Something about the definition of seqcolim is probably weird?
      sorry
end
