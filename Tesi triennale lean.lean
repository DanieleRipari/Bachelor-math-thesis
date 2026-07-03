import «Tesi triennale lean».Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Data.Nat.Pairing
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits
open CategoryTheory Limits


universe u
variable (C : Type u) [Category C] [HasTerminal C] 

def HasNNO C [Category C] [HasTerminal C] :=
    ∃ N : C, ∃ zero : (⊤_ C) ⟶ N, ∃ s : N ⟶ N,
    ∀ X : C, ∀ f : (⊤_ C) ⟶  X, ∀ g : X ⟶  X, 
    ∃ h : N ⟶  X, (zero ≫ h = f ∧ s ≫ h = h ≫ g) ∧
    (∀ h1 : N ⟶ X, ∀ h2 : N ⟶ X, (zero ≫ h1 = f ∧ s ≫ h1 = h1 ≫ g
    ∧ zero ≫ h2 = f ∧ s ≫ h2 = h2 ≫ g) → h1 = h2)



example : HasTerminal (Type) := inferInstance

class CategoryTheory.Category_with_NNO (C : Type u) [Category C]
[HasTerminal C] where 
N : C  
zero : ⊤_ C ⟶ N 
s : N ⟶ N 
recursion {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : N ⟶  X
fac_zero {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : zero ≫ recursion f g = f
fac_succ {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : s ≫ recursion f g = recursion f g ≫ g
uniq {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) (h : N ⟶ X) (hyp_zero : zero ≫ h = f)
              (hyp_succ : s ≫ h = h ≫ g) : h = recursion f g 

noncomputable def RecFun {X : Type} (f : (⊤_ Type) → X) (g : X → X) := 
    fun n => match n with 
    |0 => f ((terminal.from PUnit).hom PUnit.unit)
    |Nat.succ n => g (RecFun f g n)

noncomputable instance : Category_with_NNO (Type) where 
N := Nat
zero := TypeCat.ofHom fun (_ : ⊤_ Type) => Nat.zero 
s := TypeCat.ofHom Nat.succ 
recursion f g := TypeCat.ofHom (RecFun f g) 
fac_zero f g := by sorry 
fac_succ f g := by sorry
uniq {X} f g h hyp_zero hyp_succ := by
  let (φ : Nat → X) := g.hom 
  have h2 : ∀ (n : Nat), h n = (RecFun f g) n := by 
    intro n
    induction n with
  
  | zero =>
    unfold RecFun
    simp
    rw [← h1_zero]
    rfl
 
  | succ n ih =>
    simp 
    unfold RecFun
    rw [ih]
  --apply DFunLike.ext

