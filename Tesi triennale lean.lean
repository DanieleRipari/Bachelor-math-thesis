--import «Tesi triennale lean».Basic
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
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
open CategoryTheory Limits WalkingPair

set_option autoImplicit false

universe u
 ----------------------------------------------------------------------

--Proof that Finset is Cartesian closed

variable (α : Type u) [Inhabited α]
def IsFinsetType (α : Type u) : ObjectProperty (Type u) :=
  fun X => ∃ s : Finset α, Nonempty (X ≃ (s : Type u))

--Finset has a terminal object

instance : (IsFinsetType α).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  constructor
  intro X hX
  obtain ⟨hlim⟩ := hX
  have hterm : Limits.IsTerminal X :=
    { lift := fun s => hlim.isLimit.lift ⟨s.pt, ⟨nofun, nofun⟩⟩
      fac  := nofun
      uniq := fun s m _ => hlim.isLimit.uniq ⟨s.pt, ⟨nofun, nofun⟩⟩ m nofun }
  have huniq : Unique X := Limits.Types.isTerminalEquivUnique X hterm
  use {default}
  exact ⟨{ toFun := fun _ => ⟨default, Finset.mem_singleton_self _⟩
           invFun := fun _ => default
           left_inv := fun x => Subsingleton.elim _ _
           right_inv := fun ⟨y, hy⟩ => by
             simp only [Finset.mem_singleton] at hy; subst hy; rfl }⟩

 --Finset has binary products (to be fixed)

instance : (IsFinsetType α).IsClosedUnderLimitsOfShape (Discrete Limits.WalkingPair) := by
  constructor
  intro X hX
  obtain ⟨hlim⟩ := hX
  -- The two fibers of the diagram satisfy IsFinsetType α:
  obtain ⟨s, ⟨eL⟩⟩ := hlim.prop_diag_obj ⟨left⟩
  obtain ⟨t, ⟨eR⟩⟩ := hlim.prop_diag_obj ⟨right⟩
  -- Abbreviations for the two diagram objects and the projections:
  let A := hlim.diag.obj ⟨left⟩
  let B := hlim.diag.obj ⟨right⟩
  let πA : X ⟶ A := hlim.π.app ⟨left⟩
  let πB : X ⟶ B := hlim.π.app ⟨right⟩
  -- Pairing: given a point in A × B, build a cone over the diagram and lift it.
  -- A cone with point P assigns a map P ⟶ diag.obj j for each j.
  let mkCone : ∀ (P : Type u), (P ⟶ A) → (P ⟶ B) → Cone hlim.diag :=
    fun P f g => ⟨P, Discrete.natTrans (fun j => match j with
        | ⟨left⟩  => f
        | ⟨right⟩ => g)⟩
  -- The equivalence X ≃ A × B:
  let e : X ≃ (A × B) :=
    { toFun := fun x => (πA x, πB x)
      invFun := fun p =>
        let c : Cone hlim.diag := mkCone PUnit (TypeCat.ofHom (fun _ => p.1)) (TypeCat.ofHom (fun _ => p.2))
        hlim.isLimit.lift c PUnit.unit
      left_inv := fun x => by
        -- uniqueness: the identity-ish map and the lift agree
        have := hlim.isLimit.uniq (mkCone PUnit (TypeCat.ofHom (fun _ => πA x)) (TypeCat.ofHom (fun _ => πB x)))
                  (TypeCat.ofHom (fun _ => x)) (by rintro ⟨_|_⟩ <;> rfl)
        exact congrFun this.symm PUnit.unit
      right_inv := fun p => by
        have hfac := hlim.isLimit.fac (mkCone PUnit (TypeCat.ofHom (fun _ => p.1)) (TypeCat.ofHom (fun _ => p.2)))
        have h1 := congrFun (hfac ⟨left⟩) PUnit.unit
        have h2 := congrFun (hfac ⟨right⟩) PUnit.unit
        exact Prod.ext h1 h2 }
  -- The witness finset is the product finset s ×ˢ t:
  refine ⟨s ×ˢ t, ⟨e.trans (eL.prodCongr eR).trans ?_⟩⟩
  -- ↥s × ↥t ≃ ↥(s ×ˢ t):
  exact { toFun := fun p => ⟨(p.1, p.2), Finset.mem_product.mpr ⟨p.1.2, p.2.2⟩⟩
          invFun := fun q => (⟨q.1.1, (Finset.mem_product.mp q.2).1⟩,
                              ⟨q.1.2, (Finset.mem_product.mp q.2).2⟩)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
-------------------------------------------------------------------------

--Definition of NNO and of category with NNO

variable (C : Type u) [Category C] [HasTerminal C]

example : HasTerminal (Type) := inferInstance

structure IsNNO {C : Type u} [Category C]
[HasTerminal C] (N : C) where

zero : ⊤_ C ⟶ N

s : N ⟶ N

recursion {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : N ⟶  X

fac_zero {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : zero ≫ recursion f g = f

fac_succ {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) : s ≫ recursion f g = recursion f g ≫ g

uniq {X : C} (f : ⊤_ C ⟶ X) (g : X ⟶ X) (h : N ⟶ X) (hyp_zero : zero ≫ h = f)
              (hyp_succ : s ≫ h = h ≫ g) : h = recursion f g

class HasNNO (C : Type u) [Category C]
[HasTerminal C] where
N : C
isNNO : IsNNO N

abbrev NNO (C : Type u) [Category C] [HasTerminal C] [HasNNO C] : IsNNO (HasNNO.N (C := C)) :=
  HasNNO.isNNO (C := C)
--------------------------------------------------------------------------

--Proof that Nat is an NNO in the Type category

noncomputable def RecFun {X : Type} (f : (⊤_ Type) → X) (g : X → X) :=
    fun n => match n with
    |0 => f ((terminal.from PUnit).hom PUnit.unit)
    |Nat.succ n => g (RecFun f g n)

noncomputable def Nat_NNO_Type : IsNNO (Nat) where

zero := TypeCat.ofHom fun (_ : ⊤_ Type) => Nat.zero

s := TypeCat.ofHom Nat.succ

recursion f g := TypeCat.ofHom (RecFun f g)

fac_zero f g := by
  rw[CategoryTheory.ConcreteCategory.hom]
  simp only [Nat.zero_eq]
  ext x
  change (ConcreteCategory.hom (↾RecFun ⇑(instConcreteCategoryTypeFun.1 f)
    ⇑(instConcreteCategoryTypeFun.1 g))).toFun 0
   = (ConcreteCategory.hom f).toFun x
  have h1 : (↾(fun _ : PUnit => x) : PUnit ⟶ (⊤_ Type)) = terminal.from PUnit :=
  Subsingleton.elim _ _
  have : x = (TypeCat.Hom.hom (terminal.from PUnit)) PUnit.unit :=
  congrFun (congrArg (fun m => ⇑(TypeCat.Hom.hom m)) h1) PUnit.unit
  rw [this]
  rfl

fac_succ f g := by
  rw[CategoryTheory.ConcreteCategory.hom]
  simp only
  ext n
  rfl

uniq f g h hyp_zero hyp_succ := by
  rw[CategoryTheory.ConcreteCategory.hom]
  ext n
  simp only [TypeCat.Fun.toFun_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
  induction n with

  | zero =>
    unfold RecFun
    rw [← hyp_zero]
    rfl

  | succ n ih =>
    have : h.hom (n+1) = (↾Nat.succ ≫ h).hom n := by
      exact types_congr_hom rfl (n + 1)
    rw [hyp_succ] at this
    simp [this, RecFun, ih]
    rfl

-----------------------------------------------------------------------------

--some theorems about NNOs

--NNO is unique up to isomorphism

def NNO_unique_up_to_iso {C : Type u} [Category C] [HasTerminal C]
    {N1 N2 : C} (n1 : IsNNO N1) (n2 : IsNNO N2) : Iso N1 N2 :=
  let hom := n1.recursion n2.zero n2.s
  let inv := n2.recursion n1.zero n1.s
  { hom := hom
    inv := inv
    hom_inv_id := by
      have hyp1_zero : n1.zero ≫ (hom ≫ inv) = n1.zero := by
        rw [← Category.assoc, n1.fac_zero, n2.fac_zero]
      have hyp1_succ : n1.s ≫ (hom ≫ inv) = (hom ≫ inv) ≫ n1.s := by
        rw [← Category.assoc, n1.fac_succ, Category.assoc, n2.fac_succ,
            ← Category.assoc]
      have hyp2_zero : n1.zero ≫ 𝟙 N1 = n1.zero := by
        rw[Category.comp_id]
      have hyp2_succ : n1.s ≫ 𝟙 N1 = 𝟙 N1 ≫ n1.s := by
        rw [Category.comp_id, Category.id_comp]
      exact (n1.uniq (n1.zero) (n1.s) (hom ≫ inv) hyp1_zero hyp1_succ).trans
            (n1.uniq (n1.zero) (n1.s) (𝟙 N1) hyp2_zero hyp2_succ).symm

    inv_hom_id := by
       have hyp1_zero : n2.zero ≫ (inv ≫ hom) = n2.zero := by
        rw [← Category.assoc, n2.fac_zero, n1.fac_zero]
       have hyp1_succ : n2.s ≫ (inv ≫ hom) = (inv ≫ hom) ≫ n2.s := by
        rw [← Category.assoc, n2.fac_succ, Category.assoc, n1.fac_succ,
            ← Category.assoc]
       have hyp2_zero : n2.zero ≫ 𝟙 N2 = n2.zero := by
        rw[Category.comp_id]
       have hyp2_succ : n2.s ≫ 𝟙 N2 = 𝟙 N2 ≫ n2.s := by
        rw [Category.comp_id, Category.id_comp]
       exact (n2.uniq (n2.zero) (n2.s) (inv ≫ hom) hyp1_zero hyp1_succ).trans
            (n2.uniq (n2.zero) (n2.s) (𝟙 N2) hyp2_zero hyp2_succ).symm
  }


--Peano's fourth axiom

lemma aux1_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [HasNNO C] {x : ⊤_ C ⟶ HasNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) (g : HasNNO.N ⟶ HasNNO.N) :
  ∃ (y : ⊤_ C ⟶ HasNNO.N), y ≫ g = (NNO C).zero := by
    let h := (NNO C).recursion (NNO C).zero g
    use x ≫ h
    rw[Category.assoc, ← (NNO C).fac_succ,
    ← Category.assoc, h1, (NNO C).fac_zero]

lemma aux2_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [HasNNO C] {x : ⊤_ C ⟶ HasNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) : (NNO C).s = 𝟙 (HasNNO.N) := by
  obtain ⟨ y, hy ⟩ := (aux1_fourth_axiom h1
                    (Limits.terminal.from (HasNNO.N) ≫ (NNO C).zero ≫ (NNO C).s))
  have hyp1_zero : (NNO C).zero ≫ (NNO C).s = (NNO C).zero := by
    rw[← Category.assoc] at hy
    conv_lhs => rw [← Category.id_comp ((NNO C).zero), Category.assoc,
     Limits.terminal.hom_ext (𝟙 (⊤_ C)) (y ≫ Limits.terminal.from (HasNNO.N)),
     hy]
  have hyp1_succ : (NNO C).s ≫ (NNO C).s = (NNO C).s ≫ (NNO C).s := by rfl
  have hyp2_zero : (NNO C).zero ≫ 𝟙 (HasNNO.N) = (NNO C).zero := by
    rw[Category.comp_id]
  have hyp2_succ : (NNO C).s ≫ 𝟙 (HasNNO.N) = 𝟙 (HasNNO.N) ≫ (NNO C).s := by
    rw[Category.id_comp, Category.comp_id]
  exact ((NNO C).uniq (NNO C).zero (NNO C).s (NNO C).s hyp1_zero hyp1_succ).trans
      ((NNO C).uniq (NNO C).zero (NNO C).s (𝟙 (HasNNO.N)) hyp2_zero hyp2_succ).symm

lemma aux3_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [HasNNO C] {x : ⊤_ C ⟶ HasNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) (g : HasNNO.N ⟶ HasNNO.N) :
   g = 𝟙 (HasNNO.N (C := C)) := by
   let h := (NNO C).recursion (NNO C).zero g
   have hyp1_zero : (NNO C).zero ≫ g = (NNO C).zero := by
    conv_lhs => rw[← (NNO C).fac_zero (NNO C).zero g, Category.assoc,
    ← (NNO C).fac_succ (NNO C).zero g, aux2_fourth_axiom h1, Category.id_comp,
    (NNO C).fac_zero (NNO C).zero g]
   have hyp1_succ : (NNO C).s ≫ g = g ≫ 𝟙 (HasNNO.N) := by
    rw[aux2_fourth_axiom h1, Category.id_comp, Category.comp_id]
   have hyp2_zero : (NNO C).zero ≫ 𝟙 (HasNNO.N) = (NNO C).zero := by
    rw[Category.comp_id]
   have hyp2_succ : (NNO C).s ≫ 𝟙 (HasNNO.N) = 𝟙 (HasNNO.N) ≫ 𝟙 (HasNNO.N) := by
    repeat rw[aux2_fourth_axiom h1]
   exact ((NNO C).uniq (NNO C).zero (𝟙 (HasNNO.N (C := C))) g hyp1_zero hyp1_succ).trans
      ((NNO C).uniq (NNO C).zero (𝟙 (HasNNO.N)) (𝟙 (HasNNO.N)) hyp2_zero hyp2_succ).symm


noncomputable def fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [HasNNO C] {x : ⊤_ C ⟶ HasNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) : Iso (HasNNO.N) (⊤_ C) where
  hom := Limits.terminal.from (HasNNO.N)
  inv := (NNO C).zero
  hom_inv_id := by
    rw[aux3_fourth_axiom h1 (terminal.from HasNNO.N ≫ (NNO C).zero)]
  inv_hom_id := by
    rw[Limits.terminal.hom_ext (𝟙 (⊤_ C))]

-------------------------------------------------------------------

--Theorems that only hold in a Cartesian closed category

--Recursion theorem

structure Rec_Par_with_NNO_Aterm (C : Type u) [Category C] [HasTerminal C]
      [HasNNO C] [HasBinaryProducts C] where

RecPar {B : C} (f : ⊤_ C ⟶ B)
    (g : Limits.prod (Limits.prod (⊤_ C) HasNNO.N) B ⟶ B) :
    Limits.prod (⊤_ C) HasNNO.N ⟶ B

RecPar_fac_zero {B : C} (f : ⊤_ C ⟶ B)
    (g : Limits.prod (Limits.prod (⊤_ C) HasNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 (⊤_ C)) (NNO C).zero ≫ RecPar f g = Limits.prod.fst ≫ f

RecPar_fac_succ {B : C} (f : ⊤_ C ⟶ B)
    (g : Limits.prod (Limits.prod (⊤_ C) HasNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 (⊤_ C)) (NNO C).s ≫ RecPar f g =
    Limits.prod.lift (𝟙 (Limits.prod (⊤_ C) HasNNO.N)) (RecPar f g) ≫ g

uniq {B : C} (f : ⊤_ C ⟶ B)
    (g : Limits.prod (Limits.prod (⊤_ C) HasNNO.N) B ⟶ B) (h : Limits.prod (⊤_ C) HasNNO.N ⟶ B )
    (hyp_zero : Limits.prod.map (𝟙 (⊤_ C)) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
    (hyp_succ : Limits.prod.map (𝟙 (⊤_ C)) (NNO C).s ≫ h =
    Limits.prod.lift (𝟙 (Limits.prod (⊤_ C) HasNNO.N)) h ≫ g) : h = RecPar f g

structure Rec_Par_with_NNO {C : Type u} [Category C] [HasTerminal C]
      [HasNNO C] [HasBinaryProducts C] where

RecPar {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A HasNNO.N) B ⟶ B) :
    Limits.prod A HasNNO.N ⟶ B

RecPar_fac_zero {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A HasNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 A) (NNO C).zero ≫ RecPar f g = Limits.prod.fst ≫ f

RecPar_fac_succ {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A HasNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 A) (NNO C).s ≫ RecPar f g =
    Limits.prod.lift (𝟙 (Limits.prod A HasNNO.N)) (RecPar f g) ≫ g

uniq {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A HasNNO.N) B ⟶ B) (h : Limits.prod A HasNNO.N ⟶ B )
    (hyp_zero : Limits.prod.map (𝟙 A) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
    (hyp_succ : Limits.prod.map (𝟙 A) (NNO C).s ≫ h =
    Limits.prod.lift (𝟙 (Limits.prod A HasNNO.N)) h ≫ g) : h = RecPar f g


def Recursion_Theorem {C : Type u} [Category C]
  [HasTerminal C] [HasNNO C] [HasBinaryProducts C] :
  Rec_Par_with_NNO_Aterm C where

  Rec_Par f g :=
#check prod.rightUnitor
--Peano's third axiom

theorem third_axiom {C : Type u} [Category C]
    [HasTerminal C] [HasNNO C] :
    Mono (NNO C).s := by sorry
