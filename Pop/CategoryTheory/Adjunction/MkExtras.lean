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
end Adjunction.CoreEtaInvertibleHom
