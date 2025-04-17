import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.ApplyFun

open CategoryTheory

variable {C₁ : Type _} [Category C₁]
variable {C₂ : Type _} [Category C₂]

namespace CategoryTheory.Adjunction.CoreEtaInvertibleHom
  variable {L : C₁ ⥤ C₂}
  variable {R : C₂ ⥤ C₁}
  variable (η : 𝟭 C₁ ⟶ L ⋙ R)

  abbrev hom {c₁ : C₁} {c₂ : C₂} : (L.obj c₁ ⟶ c₂) → (c₁ ⟶ R.obj c₂)
    := fun f => η.app c₁ ≫ R.map f

  -- Note: The assumptions here are what would be the definition of an "IsEquiv" if it would exist. A definition similar to `Mathlib.Logic.Equiv.Defs.Equiv` but with a parameter for the function similar to `Function.Bijective`.
  def mk
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

  noncomputable def mkBijective (bij : ∀{c₁}{c₂}, Function.Bijective (hom η (c₁ := c₁) (c₂ := c₂))) : L ⊣ R :=
    let e {c₁}{c₂} := Equiv.ofBijective (hom η (c₁ := c₁) (c₂ := c₂)) bij
    mk η e.invFun e.left_inv e.right_inv

end CategoryTheory.Adjunction.CoreEtaInvertibleHom

noncomputable def CategoryTheory.Adjunction.CoreFullyFaithfulEpiIsoRight.mk
  (L : C₁ ⥤ C₂)
  (R : C₂ ⥤ C₁)
  [fu : R.Full]
  [ff : R.Faithful]
  (η : 𝟭 C₁ ⟶ L ⋙ R)
  [epi : ∀{c}, Epi (η.app c)]
  [iso : ∀(d : C₂), IsIso (η.app (R.obj d))]
  : L ⊣ R :=
  let ε := {
    app d := R.preimage (inv (η.app (R.obj d)))
    naturality := by
      intro X Y f
      simp_all
      apply_fun R.map
      . simp only [Functor.map_comp, Functor.map_preimage, IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
        apply (Eq.trans · (η.naturality (R.map f)).symm)
        apply congr_arg (η.app (R.obj X) ≫ ·)
        simp only [Functor.comp_obj, Functor.comp_map]
      . exact ff.map_injective
  }
  {
    unit := η
    counit := ε
    left_triangle_components := by
      intro c
      simp only [Functor.id_obj, Functor.comp_obj]
      apply_fun R.map
      . simp only [Functor.map_comp, Functor.map_preimage, Functor.map_id, IsIso.comp_inv_eq, Category.id_comp, ε]
        apply_fun (η.app c ≫ ·)
        . exact (η.naturality (η.app c)).symm
        . exact Epi.left_cancellation
      . exact ff.map_injective
    right_triangle_components := by simp only [Functor.id_obj, Functor.map_preimage, IsIso.hom_inv_id, implies_true, ε]
  }
