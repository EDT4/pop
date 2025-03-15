import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Pop.CategoryTheory.Adjunction.MkExtras
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.NatCategoryExtras
import Pop.NatExtras
import Pop.Util

set_option pp.proofs true

section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

local instance temp : (Nat.Functor.mulr 2).Final := Nat.Functor.mulr_final -- TODO: Cannot find this instance?

variable {C : Type _}
variable [cat : Category C]
variable [hsc : HasSeqColimits C] -- TODO: Reason for noncomputable. Maybe change later? It seems like most stuff is built on using limit/colimit instead of the cones directly though.
variable (A : Set C)
variable (B : Set C)
variable [ra : Reflective (fullSubcategoryInclusion A)] -- TODO: Reflective includes full and faithful, but it is already implied by the full subcategory.
variable [rb : Reflective (fullSubcategoryInclusion B)]
variable (closed_a : ClosedUnderColimitsOfShape ℕ A)
variable (closed_b : ClosedUnderColimitsOfShape ℕ B)
variable [cia : IsClosedUnderIsomorphisms A]
variable [cib : IsClosedUnderIsomorphisms B]
omit [_]

def fullSubcategoryMonad := (reflectorAdjunction (fullSubcategoryInclusion A)).toMonad

-- TODO: Rename stuff when the proof is finished
namespace IntersectionReflective
  def sequence : Limits.Seq (C ⥤ C) :=
    let TA := fullSubcategoryMonad A
    let TB := fullSubcategoryMonad B
    Seq.iterate2 (c := Cat.of C) (.mk TA.toFunctor TA.η) (.mk TB.toFunctor TB.η)

  section include C cat A B ra rb
  lemma sequence_odd {n} : ∀{c}, A (((sequence A B).obj (n * 2 + 1)).obj c) := by
    induction n
    . exact FullSubcategory.property _
    . rw [Nat.add_mul]
      intro
      apply_assumption
  lemma sequence_even {n} : ∀{c}, B (((sequence A B).obj (n * 2 + 2)).obj c) := sequence_odd B A
  end

  noncomputable abbrev Minf : C ⥤ C := colimit (sequence A B).diagram
  notation "M∞" => Minf

  variable {A B}

  -- TODO: Almost uses the same arguments. Maybe possible to generalise?
  section include C cat A B ra rb hsc cia closed_a
  lemma Minf_in_left (c : C) : A ((M∞ A B).obj c) := by
    apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
    apply IsClosedUnderIsomorphisms.of_iso (Functor.Final.colimitIso (Nat.Functor.mulr 2 ⋙ Nat.Functor.succ) _)
    apply ClosedUnderColimitsOfShape.colimit closed_a
    intro
    apply sequence_odd
  end

  section include C cat A B ra rb hsc cib closed_b
  lemma Minf_in_right (c : C) : B ((M∞ A B).obj c) := by
    apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
    apply IsClosedUnderIsomorphisms.of_iso (Functor.Final.colimitIso (Nat.Functor.mulr 2 ⋙ Nat.Functor.succ ⋙ Nat.Functor.succ) _)
    apply ClosedUnderColimitsOfShape.colimit closed_b
    intro
    apply sequence_even
  end

  noncomputable abbrev L := FullSubcategory.lift
    (A ∩ B : Set C)
    (M∞ A B)
    (fun c => .intro (Minf_in_left closed_a c) (Minf_in_right closed_b c))

  def ta' : (sequence A B).obj 1 ⟶ (sequence A B).obj 0 := by
    simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r,fullSubcategoryMonad]
    constructor
    . sorry
    . intro ; simp ; sorry

  def ta {n} : (sequence A B).obj n ⟶ (sequence A B).obj n.succ
    := (sequence A B).map n

  def test2 {n} : (sequence A B).obj (n + 2) ⟶ (sequence A B).obj n := by
    simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r]
    rewrite [← Category.assoc]
    rewrite [← Category.id_comp]
    exact whiskerRight sorry ((sequence A B).obj n)

  def test {n} : (sequence A B).obj (n + 1) ⟶ (sequence A B).obj n := by
    simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r]
    sorry

  noncomputable abbrev l : M∞ A B ⟶ 𝟭 C :=
    colimit.desc
      (sequence A B).diagram
      (.mk (𝟭 C) (NatTrans.ofSequence
        (Nat.rec (𝟙 (𝟭 C)) (fun _ => (test ≫·)))
        (by simp ; sorry)
      ))

  -- noncomputable abbrev l {c} : (M∞ A B).obj c ⟶ c :=
  --     -- TODO: Organise
  --   let a := ((colimitIsoFlipCompColim (sequence A B).diagram).app c).hom
  --   let b := colimit.desc ((sequence A B).diagram.flip.obj c) (.mk c (NatTrans.ofSequence
  --     (by -- TODO: generalise and separate
  --       simp
  --       intro n
  --       induction n generalizing A B c with
  --       | zero => exact 𝟙 c
  --       | succ n r =>
  --         apply (·≫·)
  --         . apply r (A := A) (B:= B)
  --         . sorry
  --       -- induction n
  --       -- . exact 𝟙 c
  --       -- . apply (·≫·)
  --       --   . assumption
  --       --   . simp [sequence,Seq.iterate2,Seq.Iterate2.obj,Nat.rec2r]
  --       --     sorry
  --     )
  --     (by simp ; sorry)
  --   ))
  --   a ≫ b
end IntersectionReflective

noncomputable def intersectionReflective : Reflective (fullSubcategoryInclusion (A ∩ B : Set C)) :=
  let L := IntersectionReflective.L closed_a closed_b
  {
    L := L
    adj := Adjunction.CoreEtaInvertibleHom.mk
      (seqColim.ι (IntersectionReflective.sequence A B) 0)
      (fun f => L.map f ≫ IntersectionReflective.l.app _) -- TODO: Either construct this directly or just prove that Adjunction.CoreHom.hom is bijective from the full faithful functors
      (fun f => sorry)
      (fun f => sorry)
  }

end
