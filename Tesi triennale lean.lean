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
open CategoryTheory Limits
open Finset
open WalkingPair

universe u
variable (C : Type u) [Category C] [HasTerminal C] 

def HasNNO C [Category C] [HasTerminal C] :=
    ∃ N : C, ∃ zero : (⊤_ C) ⟶ N, ∃ s : N ⟶ N,
    ∀ X : C, ∀ f : (⊤_ C) ⟶  X, ∀ g : X ⟶  X, 
    ∃ h : N ⟶  X, (zero ≫ h = f ∧ s ≫ h = h ≫ g) ∧
    (∀ h1 : N ⟶ X, ∀ h2 : N ⟶ X, (zero ≫ h1 = f ∧ s ≫ h1 = h1 ≫ g
    ∧ zero ≫ h2 = f ∧ s ≫ h2 = h2 ≫ g) → h1 = h2)

instance : HasTerminal (Type) := by sorry 

 

class CategoryTheory.Category_with_NNO (C : Type u) [Category C]
[HasTerminal C] where 
N : C  
zero : ⊤_ C ⟶ N 
s : N ⟶ N 
recursion {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : N ⟶  X
fac {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : (zero ≫ recursion f g = f ∧ 
            s ≫ recursion f g = recursion f g ≫ g)
uniq {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) (h : N ⟶ X): 
            (zero ≫ h = f ∧ s ≫ h = h ≫ g) → h = recursion f g 

def RecFun {X : Type} (f : (⊤_ Type) → X) (g : X → X) := 
    fun n => match n with 
    |0 => f (by exact sorry)
    |Nat.succ n => g (RecFun f g n)
instance : Category_with_NNO (Type) where 
N := Nat
zero := fun (_ : ⊤_ Type) => (0 : Nat) 
s := ↑(Nat.succ) 
recursion f g := RecFun f g 
fac f g := by sorry 
uniq f g h := by 
    intro h1 
    obtain ⟨h1_zero, h1_succ⟩ := h1
    dsimp only [CategoryTheory.types_comp] at h1_succ
    funext n 
    
    induction n with

    | zero =>

    simp only [types_comp] at h1_zero

    unfold RecFun

    simp

    rw [← h1_zero]

    rfl

    | succ n ih =>

    simp only [types_comp] at h1_succ 

    unfold RecFun
    #check h1_succ
    simp


    rw [← ih]

    sorry

