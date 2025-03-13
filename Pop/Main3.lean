import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.Data.Set.Defs
import Pop.CategoryTheory.Limits.Shapes.SeqColimit
import Pop.NatCategoryExtras
import Pop.NatExtras
import Pop.Util

set_option pp.proofs true

section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

variable {C : Type _}
variable [Category C]
-- TODO: Change these later
-- variable [HasPullbacks C]
-- variable [HasPushouts C]
variable [HasSeqColimits C]

namespace Adjunction.CoreEtaInvertibleHom
  variable {C₁ C₂ : Type _}
  variable [Category C₁]
  variable [Category C₂]
  variable {F : Functor C₁ C₂}
  variable {G : Functor C₂ C₁}
  variable (η : 𝟭 C₁ ⟶ F ⋙ G)

  abbrev hom {c₁ : C₁} {c₂ : C₂} : (F.obj c₁ ⟶ c₂) → (c₁ ⟶ G.obj c₂)
    := fun f => η.app c₁ ≫ G.map f

  def mk
    (invHom : ∀{c₁ : C₁}{c₂ : C₂}, (c₁ ⟶ G.obj c₂) → (F.obj c₁ ⟶ c₂))
    (left_inv  : ∀{c₁}{c₂}, Function.LeftInverse  invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    (right_inv : ∀{c₁}{c₂}, Function.RightInverse invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    : F ⊣ G
    :=
      Adjunction.mkOfHomEquiv {
        homEquiv := fun _ _ => .mk (hom η) invHom left_inv right_inv
        homEquiv_naturality_left_symm := by
          intro c₁₁ c₁₂ c₂ f g
          simp
          apply_fun hom η
          . rw [right_inv]
            simp [hom]
            rewrite [← Category.assoc , ← Functor.comp_map , ← η.naturality f]
            simp
            congr
            change g = hom η (invHom g)
            rw [right_inv]
          . exact Function.LeftInverse.injective left_inv
        homEquiv_naturality_right := by simp [hom]
      }
end Adjunction.CoreEtaInvertibleHom

local instance temp : (Nat.Functor.mulr 2).Final := Nat.Functor.mulr_final -- TODO: Cannot find this instance?

section
  variable (A : Set C)
  variable [IsClosedUnderIsomorphisms A]
  variable [Reflective (fullSubcategoryInclusion A)] -- TODO: Reflective includes full and faithful, but it is already implied by the full subcategory.
  variable (closed_a : ClosedUnderColimitsOfShape ℕ A)
  variable (B : Set C)
  variable [IsClosedUnderIsomorphisms B]
  variable [Reflective (fullSubcategoryInclusion B)]
  variable (closed_b : ClosedUnderColimitsOfShape ℕ B)

  def fullSubcategoryMonad := (reflectorAdjunction (fullSubcategoryInclusion A)).toMonad

  -- TODO: This is just temporary and is very unorganised. Not proper. Also rename stuff when the proof is finished
  namespace IntersectionReflective
    def sequence : Limits.Seq (C ⥤ C) :=
      let TA := fullSubcategoryMonad A
      let TB := fullSubcategoryMonad B
      Seq.iterate2 (c := Cat.of C) TA.toFunctor TB.toFunctor TA.η TB.η

    noncomputable abbrev Minf : C ⥤ C := seqColim (sequence A B) -- TODO: Change later to computable
    notation "M∞" => Minf

    variable {A B}

    -- TODO: inA and inB almost uses the same arguments and should be generalised in the future
    -- TODO: Also split this into smaller stuff
    lemma inA (closed_a : ClosedUnderColimitsOfShape ℕ A) : ∀(c : C), A ((M∞ A B).obj c) := by
      intro c
      apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
      apply IsClosedUnderIsomorphisms.of_iso (Functor.Final.colimitIso (Nat.Functor.mulr 2 ⋙ Nat.Functor.succ) _)
      apply ClosedUnderColimitsOfShape.colimit closed_a
      simp [Nat.Functor.mulr]
      intro n
      induction n generalizing A B c
      . exact FullSubcategory.property _
      . rw [Nat.add_mul] ; apply_assumption ; assumption

    lemma inB (closed_b : ClosedUnderColimitsOfShape ℕ B) : ∀(c : C), B ((M∞ A B).obj c) := by
      intro c
      apply IsClosedUnderIsomorphisms.of_iso ((colimitIsoFlipCompColim _).app c).symm
      apply IsClosedUnderIsomorphisms.of_iso (Functor.Final.colimitIso (Nat.Functor.mulr 2 ⋙ Nat.Functor.succ ⋙ Nat.Functor.succ) _)
      apply ClosedUnderColimitsOfShape.colimit closed_b
      simp [Nat.Functor.mulr]
      intro n
      induction n generalizing A B c
      . exact FullSubcategory.property _
      . rw [Nat.add_mul] ; apply_assumption ; assumption

    noncomputable abbrev L := FullSubcategory.lift (A ∩ B : Set C) (M∞ A B) (fun c => .intro (inA closed_a c) (inB closed_b c))
    abbrev l {c} : (L closed_a closed_b).obj ((fullSubcategoryInclusion (A ∩ B : Set C)).obj c) ⟶ c
      := by simp [L] ; sorry
  end IntersectionReflective

  noncomputable def intersectionReflective : Reflective (fullSubcategoryInclusion (A ∩ B : Set C)) :=
    let L := IntersectionReflective.L closed_a closed_b
    let l := IntersectionReflective.l closed_a closed_b
    {
      L := L
      adj := Adjunction.CoreEtaInvertibleHom.mk
        (seqColim.ι (IntersectionReflective.sequence A B) 0)
        (fun f => L.map f ≫ l) -- TODO: Either construct this directly or just prove that Adjunction.CoreHom.hom is bijective from the full faithful functors
        sorry
        sorry
    }
end

end
