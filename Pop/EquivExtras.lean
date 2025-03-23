import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs

variable {A : Sort _}
variable {B : Sort _}
variable {f : A → B}

class IsEquivFun (f : A → B) where
  inv : B → A
  left_inv  : Function.LeftInverse  inv f
  right_inv : Function.RightInverse inv f

def Equiv.isEquiv (e : Equiv A B) : IsEquivFun e.toFun where
  inv := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv

def Equiv.invIsEquiv (e : Equiv A B) : IsEquivFun e.invFun where
  inv := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

namespace IsEquivFun
  def toEquiv (e : IsEquivFun f) : Equiv A B where
    toFun := f
    invFun := e.inv
    left_inv := e.left_inv
    right_inv := e.right_inv
end IsEquivFun
