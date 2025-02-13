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

open CategoryTheory
open CategoryTheory.Limits

set_option autoImplicit true

-- TODO: cleanup and organise later
section
  -- TODO: Look up if it is possible to specify implicit args and also if it is possible positionally
  variable {A B C : Type u}
  variable [Category.{v, u} A]
  variable [Category.{v, u} B]
  variable [Category.{v, u} C]

  -- TODO: Is this correct? It will probably be more clear later
  -- TODO: Lookup cofiltered category and tower diagrams
  section namespace CategoryTheory.Limits.Shapes.SeqColimit
    abbrev SeqDiagram (C : Type u) [Category.{v, u} C] := Functor ℕ C

    def SeqDiagram.bySequence (f : ℕ → C) (m : (n : ℕ) → f n ⟶ f (Nat.succ n)) : SeqDiagram C
      := Functor.ofSequence m

    def SeqDiagram.byRepeat (f : Functor C C) (z : C) (zm : z ⟶ f.obj z) : SeqDiagram C :=
      let o (n : ℕ) : C := Nat.repeat f.obj n z
      let rec m (n : ℕ) : o n ⟶ o (n + 1) := match n with
        | Nat.zero   => zm
        | Nat.succ n => f.map (m n)
      SeqDiagram.bySequence o m

    -- TODO: Pointed endofunctor (NatTrans (Functor.id C) f) instead of zm, but what would the naturality give?
    def SeqDiagram.byRepeat' (f : Functor C C) (m : NatTrans (Functor.id C) f) (z : C) : SeqDiagram C :=
      SeqDiagram.byRepeat f z (m.app z)

    section namespace BySequence
      variable (so : ℕ → C)
      variable (sm : (n : ℕ) → so n ⟶ so (Nat.succ n))

      lemma map_id (n : ℕ) (o : n ⟶ n) : (SeqDiagram.bySequence so sm).map o = CategoryStruct.id (so n)
        := by
          rewrite [Subsingleton.elim o (homOfLE (by omega))]
          exact Functor.OfSequence.map_id sm n

      lemma map_comp (a b c : ℕ) (o1 : a ⟶ b) (o2 : b ⟶ c) (o3 : a ⟶ c) : (SeqDiagram.bySequence so sm).map o3 = (SeqDiagram.bySequence so sm).map o1 ≫ (SeqDiagram.bySequence so sm).map o2
        := Functor.OfSequence.map_comp sm a b c (leOfHom o1) (leOfHom o2)

      lemma map_succ (n : ℕ) (o : n ⟶ Nat.succ n) : (SeqDiagram.bySequence so sm).map o = sm n
        := by
          rewrite [Subsingleton.elim o (homOfLE (Nat.le_add_right n 1))]
          exact Functor.OfSequence.map_le_succ sm n

      abbrev SeqColimCocone := Cocone (SeqDiagram.bySequence so sm)
      def SeqColimCocone.mk
        {W : C}
        (p : (n : ℕ) → so n ⟶ W)
        (eq : ∀(n : ℕ), sm n ≫ p (Nat.succ n) = p n)
        : SeqColimCocone so sm where
        pt := W
        ι :=
          let e := by
            intro n
            simp
            rewrite [map_succ so sm n (homOfLE (by omega))]
            exact eq n
          NatTrans.ofSequence (F := SeqDiagram.bySequence so sm) (G := (Functor.const ℕ).obj W) p e
        -- ι := {
        --   app := p
        --   naturality :=
        --     let rec impl
        --     | Nat.zero   , Nat.zero   , o => by
        --       -- simp_all!
        --       rewrite [map_id so sm Nat.zero o]
        --       rewrite [Category.id_comp (p 0)]
        --       simp
        --     | Nat.zero   , Nat.succ b , o => by
        --       let o' : 0 ⟶ b     := homOfLE (by omega)
        --       let os : b ⟶ b + 1 := homOfLE (by omega)
        --       rewrite [map_comp so sm 0 b (b + 1) o' os o]
        --       rewrite [Category.assoc ((SeqDiagram.bySequence so sm).map o') ((SeqDiagram.bySequence so sm).map os) (p (b + 1))]
        --       rewrite [map_succ so sm b os]
        --       rewrite [eq b]
        --       rewrite [impl Nat.zero b o']
        --       simp
        --     | Nat.succ a , Nat.succ b , o => by
        --       simp
        --       let test := impl a b sorry
        --       -- let test2 := (NatTrans.ofSequence (C := C) (F := sorry) (G := sorry) sorry sorry)
        --       sorry
        --     impl
        -- }
    end BySequence

    abbrev HasSeqColimit(f : SeqDiagram C) := HasColimit f
    noncomputable abbrev seqColim (f : SeqDiagram C) [HasSeqColimit f] := colimit f

    noncomputable abbrev seqColim.ι (f : SeqDiagram C) [HasSeqColimit f] (n : ℕ)
      : f.obj n ⟶ seqColim f
      := colimit.ι f n

    noncomputable abbrev seqColim.desc (f : SeqDiagram C) [HasSeqColimit f] (n : ℕ)
      : seqColim f ⟶ _
      := colimit.desc f (Cocone.mk f _)

  end




  open CategoryTheory.Limits.Shapes.SeqColimit

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
      SeqDiagram.byRepeat (C := Over s2) (Over.map sorry) sorry sorry -- TODO: give this some thought
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
        let Minf   := seqColim (seqByRepeat' Msucc (.mk sorry) Mzero)

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
