
set_option autoImplicit true

@[reducible, inline]
def Function.pointwise₂ (o : B₁ → B₂ → C) (f : A → B₁) (g : A → B₂) (a : A) : C
  := o (f a) (g a)

notation (name := pw2) "❪" o:arg "❫₂" f:arg g:arg => Function.pointwise₂ o f g
