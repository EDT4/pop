import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.ApplyFun

open CategoryTheory

namespace CategoryTheory.Adjunction.CoreEtaInvertibleHom
  variable {C₁ C₂ : Type _}
  variable [Category C₁]
  variable [Category C₂]
  variable {L : Functor C₁ C₂}
  variable {R : Functor C₂ C₁}
  variable (η : 𝟭 C₁ ⟶ L ⋙ R)

  abbrev hom {c₁ : C₁} {c₂ : C₂} : (L.obj c₁ ⟶ c₂) → (c₁ ⟶ R.obj c₂)
    := fun f => η.app c₁ ≫ R.map f

  def mk
    -- TODO: So, to construct such an invHom: let L, R be fully faithful, but the functors are not bijective? So...
    -- TODO: The assumptions here is Function.Bijective but using inverses and Mathlib.Logic.Equiv.Defs.Equiv but with a parameter. There is no "IsEquiv"?
    (invHom : ∀{c₁ : C₁}{c₂ : C₂}, (c₁ ⟶ R.obj c₂) → (L.obj c₁ ⟶ c₂))
    (left_inv  : ∀{c₁}{c₂}, Function.LeftInverse  invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    (right_inv : ∀{c₁}{c₂}, Function.RightInverse invHom (hom η (c₁ := c₁) (c₂ := c₂)))
    : L ⊣ R
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

  -- TODO: temporary
  noncomputable def mkBijective (bij : ∀{c₁}{c₂}, Function.Bijective (hom η (c₁ := c₁) (c₂ := c₂))) : L ⊣ R :=
    let e {c₁}{c₂} := Equiv.ofBijective (hom η (c₁ := c₁) (c₂ := c₂)) bij
    mk η e.invFun e.left_inv e.right_inv
end CategoryTheory.Adjunction.CoreEtaInvertibleHom

-- namespace CategoryTheory.Adjunction.FullCategory
--   variable {C : Type _}
--   variable [Category C]
--   variable {A : Set C}
--
--   noncomputable def mk
--     (L : C ⥤ FullSubcategory A)
--     (η : 𝟭 C ⟶ L ⋙ fullSubcategoryInclusion A)
--     -- [i : ∀(c : C), IsIso (η.app c)]
--     [i : ∀(a : FullSubcategory A), IsIso (η.app a.obj)]
--     : L ⊣ fullSubcategoryInclusion A
--     where
--       unit := η
--       counit := .mk
--         (fun a => have y := inv (η.app a.obj) ; y)
--         (by
--           intro X Y f
--           simp_all only [Functor.comp_obj, fullSubcategoryInclusion.obj, Functor.id_obj, Functor.comp_map, fullSubcategoryInclusion.map, Functor.id_map]
--           apply (IsIso.comp_inv_eq (η.app Y.obj)).mpr
--           apply (Eq.trans · (Category.assoc _ _ _).symm)
--           apply (IsIso.eq_inv_comp (η.app X.obj)).mpr
--           apply (Eq.trans · (η.naturality (X := X.obj) (Y := Y.obj) f).symm)
--           apply congr_arg (η.app X.obj ≫ ·)
--           simp only [Functor.comp_map, fullSubcategoryInclusion.map]
--         )
--       left_triangle_components := by
--         intro c
--         simp
--         apply (comp_inv_eq_id (η.app (L.obj c).obj)).mpr
--         -- apply_fun (η.app c ≫ ·)
--         -- . exact (η.naturality (η.app c)).symm
--         -- . sorry
--         sorry
-- end CategoryTheory.Adjunction.FullCategory
