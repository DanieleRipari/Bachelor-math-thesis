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
import Mathlib.SetTheory.Cardinal.Arithmetic
open CategoryTheory Limits WalkingPair

set_option autoImplicit false

universe u
 ----------------------------------------------------------------------

--Proof that Finset is Cartesian closed

variable (α : Type u) [Inhabited α] [Infinite α]
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
  -- A cone with point P assigns a map P ⟶ diag.obj j for each j.
  let mkCone : ∀ (P : Type u), (P ⟶ A) → (P ⟶ B) → Cone hlim.diag :=
    fun P f g => ⟨P, Discrete.natTrans (fun j => match j with
        | ⟨left⟩  => f
        | ⟨right⟩ => g)⟩
  -- The equivalence X ≃ A × B:
  let e : X ≃ (A × B) :=
    { toFun := fun x => (πA x, πB x)
      invFun := fun p =>
        hlim.isLimit.lift
          (mkCone PUnit (show PUnit ⟶ A from TypeCat.ofHom.{u} fun _ : PUnit.{u+1}=> p.1)
                      (show PUnit ⟶ B from TypeCat.ofHom.{u} fun _ : PUnit.{u+1}=> p.2)) PUnit.unit
      left_inv := fun x => by 
        have := hlim.isLimit.uniq
                  (mkCone PUnit (TypeCat.ofHom.{u} fun _ : PUnit.{u+1} => πA x) 
                  (TypeCat.ofHom.{u} fun _ : PUnit.{u+1} => πB x))
                  (TypeCat.ofHom.{u} fun _ : PUnit.{u+1} => x) (by rintro ⟨_|_⟩ <;> rfl)
       -- rw [← TypeCat.hom_ofHom (hlim.isLimit.lift _)] at this
        exact congrArg (fun m => (ConcreteCategory.hom m) PUnit.unit) this.symm
      right_inv := fun p => by
        have hfac := hlim.isLimit.fac
          (mkCone PUnit (TypeCat.ofHom.{u} fun _ : PUnit.{u+1} => p.1) 
          (TypeCat.ofHom.{u} fun _ : PUnit.{u+1} => p.2))
        have h1 := congrArg (fun m => (ConcreteCategory.hom m) PUnit.unit) (hfac ⟨left⟩)
        have h2 := congrArg (fun m => (ConcreteCategory.hom m) PUnit.unit) (hfac ⟨right⟩)
        exact Prod.ext h1 h2 }
  -- The witness finset is the product finset s ×ˢ t:
  classical
  obtain ⟨e₀⟩ : Nonempty (α × α ≃ α) := by 
    have h : Cardinal.mk (α × α) = Cardinal.mk α := by
      simp [Cardinal.mk_prod, Cardinal.mul_mk_eq_max]
    exact Quotient.exact h
  refine ⟨(s ×ˢ t).map e₀.toEmbedding, ⟨(e.trans (eL.prodCongr eR)).trans ?_⟩⟩
  refine Equiv.trans ?_ (Finset.equivOfCardEq (s := s ×ˢ t) (t := (s ×ˢ t).map e₀.toEmbedding) ?_)
  · exact { toFun := fun p => ⟨(p.1, p.2), Finset.mem_product.mpr ⟨p.1.2, p.2.2⟩⟩
            invFun := fun q => (⟨q.1.1, (Finset.mem_product.mp q.2).1⟩,
                                ⟨q.1.2, (Finset.mem_product.mp q.2).2⟩)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  · rw [Finset.card_map]
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

class WithNNO (C : Type u) [Category C]
[HasTerminal C] where
N : C
isNNO : IsNNO N

abbrev NNO (C : Type u) [Category C] [HasTerminal C] [WithNNO C] : IsNNO (WithNNO.N (C := C)) :=
  WithNNO.isNNO (C := C)
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

noncomputable instance : WithNNO (Type) :=
{
  N := Nat
  isNNO := Nat_NNO_Type
}
-----------------------------------------------------------------------------

--some theorems about NNOs

--NNO is unique up to isomorphism

def NNO_unique_up_to_iso {C : Type u} [Category C] [HasTerminal C]
    {N1 N2 : C} (n1 : IsNNO N1) (n2 : IsNNO N2) : Iso N1 N2 :=
  letI hom := n1.recursion n2.zero n2.s
  letI inv := n2.recursion n1.zero n1.s
  { hom := n1.recursion n2.zero n2.s
    inv := n2.recursion n1.zero n1.s
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
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) (g : WithNNO.N ⟶ WithNNO.N) :
  ∃ (y : ⊤_ C ⟶ WithNNO.N), y ≫ g = (NNO C).zero := by
    let h := (NNO C).recursion (NNO C).zero g
    use x ≫ h
    rw[Category.assoc, ← (NNO C).fac_succ,
    ← Category.assoc, h1, (NNO C).fac_zero]

lemma aux2_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) : (NNO C).s = 𝟙 (WithNNO.N) := by
  obtain ⟨ y, hy ⟩ := (aux1_fourth_axiom h1
                    (Limits.terminal.from (WithNNO.N) ≫ (NNO C).zero ≫ (NNO C).s))
  have hyp1_zero : (NNO C).zero ≫ (NNO C).s = (NNO C).zero := by
    rw[← Category.assoc] at hy
    conv_lhs => rw [← Category.id_comp ((NNO C).zero), Category.assoc,
     Limits.terminal.hom_ext (𝟙 (⊤_ C)) (y ≫ Limits.terminal.from (WithNNO.N)),
     hy]
  have hyp1_succ : (NNO C).s ≫ (NNO C).s = (NNO C).s ≫ (NNO C).s := by rfl
  have hyp2_zero : (NNO C).zero ≫ 𝟙 (WithNNO.N) = (NNO C).zero := by
    rw[Category.comp_id]
  have hyp2_succ : (NNO C).s ≫ 𝟙 (WithNNO.N) = 𝟙 (WithNNO.N) ≫ (NNO C).s := by
    rw[Category.id_comp, Category.comp_id]
  exact ((NNO C).uniq (NNO C).zero (NNO C).s (NNO C).s hyp1_zero hyp1_succ).trans
      ((NNO C).uniq (NNO C).zero (NNO C).s (𝟙 (WithNNO.N)) hyp2_zero hyp2_succ).symm

lemma aux3_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) (g : WithNNO.N ⟶ WithNNO.N) :
   g = 𝟙 (WithNNO.N (C := C)) := by
   letI h := (NNO C).recursion (NNO C).zero g
   have hyp1_zero : (NNO C).zero ≫ g = (NNO C).zero := by
    conv_lhs => rw[← (NNO C).fac_zero (NNO C).zero g, Category.assoc,
    ← (NNO C).fac_succ (NNO C).zero g, aux2_fourth_axiom h1, Category.id_comp,
    (NNO C).fac_zero (NNO C).zero g]
   have hyp1_succ : (NNO C).s ≫ g = g ≫ 𝟙 (WithNNO.N) := by
    rw[aux2_fourth_axiom h1, Category.id_comp, Category.comp_id]
   have hyp2_zero : (NNO C).zero ≫ 𝟙 (WithNNO.N) = (NNO C).zero := by
    rw[Category.comp_id]
   have hyp2_succ : (NNO C).s ≫ 𝟙 (WithNNO.N) = 𝟙 (WithNNO.N) ≫ 𝟙 (WithNNO.N) := by
    repeat rw[aux2_fourth_axiom h1]
   exact ((NNO C).uniq (NNO C).zero (𝟙 (WithNNO.N (C := C))) g hyp1_zero hyp1_succ).trans
      ((NNO C).uniq (NNO C).zero (𝟙 (WithNNO.N)) (𝟙 (WithNNO.N)) hyp2_zero hyp2_succ).symm


noncomputable def fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) : Iso (WithNNO.N) (⊤_ C) where
  hom := Limits.terminal.from (WithNNO.N)
  inv := (NNO C).zero
  hom_inv_id := by
    rw[aux3_fourth_axiom h1 (terminal.from WithNNO.N ≫ (NNO C).zero)]
  inv_hom_id := by
    rw[Limits.terminal.hom_ext (𝟙 (⊤_ C))]

-------------------------------------------------------------------

--Theorems that only hold in a Cartesian closed category

--Recursion theorem (case of A = ⊤)


structure Rec_Par_with_NNO {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] where

RecPar {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    Limits.prod A WithNNO.N ⟶ B

RecPar_fac_zero {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 A) (NNO C).zero ≫ RecPar f g = Limits.prod.fst ≫ f

RecPar_fac_succ {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 A) (NNO C).s ≫ RecPar f g =
    Limits.prod.lift (𝟙 (Limits.prod A WithNNO.N)) (RecPar f g) ≫ g

uniq {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) (h : Limits.prod A WithNNO.N ⟶ B )
    (hyp_zero : Limits.prod.map (𝟙 A) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
    (hyp_succ : Limits.prod.map (𝟙 A) (NNO C).s ≫ h =
    Limits.prod.lift (𝟙 (Limits.prod A WithNNO.N)) h ≫ g) : h = RecPar f g



noncomputable def aux_function1 {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) : 
  Limits.prod WithNNO.N B ⟶ B:= 
    (Limits.prod.leftUnitor (Limits.prod WithNNO.N B)).inv ≫
    (Limits.prod.associator (⊤_ C) (WithNNO.N) (B)).inv ≫ g


noncomputable def aux_function2 {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) : 
  WithNNO.N ⟶ Limits.prod WithNNO.N B := 
    (NNO C).recursion (Limits.prod.lift (NNO C).zero f) (Limits.prod.lift
    ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1 g))



noncomputable def Rec_Par_with_NNO_Aterm {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
    Limits.prod (⊤_ C) WithNNO.N ⟶ B :=
    (Limits.prod.leftUnitor WithNNO.N).hom ≫ aux_function2 f g ≫ Limits.prod.snd

lemma aux_Rec_Par {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  aux_function2 f g = Limits.prod.lift (𝟙 (WithNNO.N)) (aux_function2 f g ≫ Limits.prod.snd) := by
    apply Limits.prod.hom_ext 
    
    · rw[Limits.prod.lift_fst]  
      have hyp1_zero : (NNO C).zero ≫ aux_function2 f g ≫ Limits.prod.fst = (NNO C).zero := by 
        rw[← Category.assoc, aux_function2, (NNO C).fac_zero, Limits.prod.lift_fst] 
      have hyp1_succ : (NNO C).s ≫ aux_function2 f g ≫ Limits.prod.fst = 
      (aux_function2 f g ≫ Limits.prod.fst) ≫ (NNO C).s := by 
        conv_lhs => rw[← Category.assoc, aux_function2, (NNO C).fac_succ, Category.assoc,
         Limits.prod.lift_fst, ← Category.assoc, ← aux_function2] 
      have hyp2_zero : (NNO C).zero ≫ 𝟙 (WithNNO.N) = (NNO C).zero := by
        rw[Category.comp_id]
      have hyp2_succ : (NNO C).s ≫ 𝟙 (WithNNO.N) = 𝟙 (WithNNO.N) ≫ (NNO C).s := by 
        rw[Category.comp_id, Category.id_comp]
      exact ((NNO C).uniq (NNO C).zero (NNO C).s 
            (aux_function2 f g ≫ Limits.prod.fst) hyp1_zero hyp1_succ).trans 
            ((NNO C).uniq (NNO C).zero (NNO C).s (𝟙 (WithNNO.N)) hyp2_zero hyp2_succ).symm
    
    · rw[Limits.prod.lift_snd]
    
 

theorem Rec_Par_with_NNO_Aterm_fac_zero {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  Limits.prod.map (𝟙 (⊤_ C)) (NNO C).zero ≫ Rec_Par_with_NNO_Aterm f g = 
  (Limits.prod.leftUnitor (⊤_ C)).hom ≫ f := by
    unfold Rec_Par_with_NNO_Aterm
    letI ρ := ((NNO C).recursion (prod.lift (NNO C).zero f) 
    (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1 g)))
    rw[← Category.assoc, 
    Limits.terminal.hom_ext (Limits.prod.leftUnitor (⊤_ C)).hom Limits.prod.snd,
    Limits.prod.leftUnitor_hom, Limits.prod.map_snd, Category.assoc, aux_function2,
    ← Category.assoc ((NNO C).zero) (ρ) (prod.snd), (NNO C).fac_zero, Limits.prod.lift_snd] 

theorem Rec_Par_with_NNO_Aterm_fac_succ {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  Limits.prod.map (𝟙 (⊤_ C)) (NNO C).s ≫ Rec_Par_with_NNO_Aterm f g = 
  Limits.prod.lift (𝟙 (Limits.prod (⊤_ C) WithNNO.N)) (Rec_Par_with_NNO_Aterm f g) ≫ g := by
    unfold Rec_Par_with_NNO_Aterm
    letI ρ := ((NNO C).recursion (prod.lift (NNO C).zero f) 
    (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1 g)))
    rw[← Category.assoc,
    Limits.prod.leftUnitor_hom, Limits.prod.map_snd, Category.assoc, aux_function2, 
    ← Category.assoc ((NNO C).s), (NNO C).fac_succ,
    Category.assoc ρ, Limits.prod.lift_snd, aux_function1]
    
    have : prod.snd ≫ ρ ≫ (Limits.prod.leftUnitor (WithNNO.N ⨯ B)).inv ≫ 
    (prod.associator (⊤_ C) WithNNO.N B).inv =
      prod.lift (𝟙 ((⊤_ C) ⨯ WithNNO.N)) (prod.snd ≫ ρ ≫ prod.snd) := by 
        apply Limits.prod.hom_ext 
        · rw[Limits.prod.lift_fst, Limits.prod.associator_inv, Category.assoc, Category.assoc, 
          Category.assoc, Limits.prod.lift_fst] 
          apply Limits.prod.hom_ext
          · exact Limits.terminal.hom_ext (
            (prod.snd ≫ ρ ≫ (Limits.prod.leftUnitor (WithNNO.N ⨯ B)).inv ≫ 
                    prod.lift prod.fst (prod.snd ≫ prod.fst)) ≫ prod.fst) 
                    (𝟙 ((⊤_ C) ⨯ WithNNO.N) ≫ prod.fst)
          · rw[Category.assoc, Category.assoc, Category.assoc,
             Limits.prod.lift_snd, Category.id_comp,
            ← Category.assoc ((Limits.prod.leftUnitor (WithNNO.N ⨯ B)).inv),
            Limits.prod.leftUnitor_inv, Limits.prod.lift_snd, Category.id_comp]
            dsimp only [ρ]
            rw[← aux_function2, aux_Rec_Par, Limits.prod.lift_fst, Category.comp_id]
        · rw[Limits.prod.lift_snd, Limits.prod.associator_inv, Category.assoc, Category.assoc, 
          Category.assoc, Limits.prod.lift_snd, Limits.prod.leftUnitor_inv,
          ← Category.assoc (prod.lift (terminal.from (WithNNO.N ⨯ B)) (𝟙 (WithNNO.N ⨯ B))),
          Limits.prod.lift_snd, Category.id_comp]
    
    rw[← Category.assoc ((Limits.prod.leftUnitor (WithNNO.N ⨯ B)).inv), ← Category.assoc ρ,
    ← Category.assoc prod.snd, this]
    dsimp only [ρ] 
    rw[aux_function1]
    simp only [Category.assoc]  

theorem Rec_Par_with_NNO_Aterm_unique {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B)
  (h : Limits.prod (⊤_ C) WithNNO.N ⟶ B)
  (hyp_zero : Limits.prod.map (𝟙 (⊤_ C)) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
  (hyp_succ : Limits.prod.map (𝟙 (⊤_ C)) (NNO C).s ≫ h =
  Limits.prod.lift (𝟙 (Limits.prod (⊤_ C) WithNNO.N)) h ≫ g) : 
  h = Rec_Par_with_NNO_Aterm f g := by 
    unfold Rec_Par_with_NNO_Aterm
    conv_lhs => rw[← Category.id_comp h, ← (Limits.prod.leftUnitor WithNNO.N).hom_inv_id,
    Limits.prod.leftUnitor_inv, Category.assoc]
      
    have : Limits.prod.lift (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h) = 
      aux_function2 f g := by 
        
        have hyp1_zero : ((NNO C).zero ≫ Limits.prod.lift 
        (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h)) = 
        Limits.prod.lift (NNO C).zero f := by 
          rw[Limits.prod.leftUnitor_inv, Limits.prod.comp_lift, Category.comp_id,
          ← Category.assoc, Limits.prod.comp_lift,
          Limits.terminal.hom_ext (((NNO C).zero ≫ terminal.from WithNNO.N)) (𝟙 (⊤_ C)),
          Category.comp_id]
          have : prod.lift (𝟙 (⊤_ C)) (NNO C).zero = 
            prod.lift (𝟙 (⊤_ C)) (𝟙 (⊤_ C)) ≫ prod.map (𝟙 (⊤_ C)) (NNO C).zero := by 
            conv_lhs => rw[← Category.id_comp (𝟙 (⊤_ C)), ← Category.id_comp (NNO C).zero,
            ← Limits.prod.lift_map]
          rw[this, Category.assoc, hyp_zero, ← Category.assoc, 
          Limits.prod.lift_fst, Category.id_comp]
        
        have hyp1_succ : ((NNO C).s ≫ Limits.prod.lift 
        (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h)) = 
        (Limits.prod.lift (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h)) ≫ 
         (Limits.prod.lift ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1 g)) := by 
          conv_lhs => rw[Limits.prod.leftUnitor_inv, Limits.prod.comp_lift, Category.comp_id,
          ← Category.assoc, Limits.prod.comp_lift,
          Limits.terminal.hom_ext (((NNO C).s ≫ terminal.from WithNNO.N)) (terminal.from WithNNO.N),
          Category.comp_id]
          
          have : prod.lift (terminal.from WithNNO.N) (NNO C).s = 
                prod.lift (terminal.from WithNNO.N) (𝟙 WithNNO.N) ≫ 
                prod.map (𝟙 (⊤_ C)) (NNO C).s := by 
              conv_lhs => rw[← Category.comp_id (terminal.from WithNNO.N), 
              ← Category.id_comp (NNO C).s, ← Limits.prod.lift_map]
          conv_lhs => rw[this, Category.assoc, hyp_succ]
          conv_rhs => rw[Limits.prod.leftUnitor_inv, Limits.prod.comp_lift, ← Category.assoc,
          Limits.prod.lift_fst, Category.id_comp, aux_function1, Limits.prod.leftUnitor_inv,
          Limits.prod.associator_inv]
          
          have : prod.lift (terminal.from WithNNO.N) (𝟙 WithNNO.N) ≫ 
                  prod.lift (𝟙 ((⊤_ C) ⨯ WithNNO.N)) h =
                 prod.lift (𝟙 WithNNO.N) (prod.lift (terminal.from WithNNO.N) (𝟙 WithNNO.N) ≫ h) ≫
                  prod.lift (terminal.from (WithNNO.N ⨯ B)) (𝟙 (WithNNO.N ⨯ B)) ≫
                  prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd) := by 
            apply Limits.prod.hom_ext 
            · rw[Category.assoc, Limits.prod.lift_fst, Category.comp_id,
              Category.assoc, Category.assoc, Limits.prod.lift_fst, Limits.prod.comp_lift,
              ← Category.assoc, Limits.prod.lift_snd, Limits.prod.lift_fst, Category.id_comp]
              apply Limits.prod.hom_ext 
              · exact (Limits.terminal.hom_ext 
                    (prod.lift (terminal.from WithNNO.N) (𝟙 WithNNO.N) ≫ prod.fst)
                  ((prod.lift (𝟙 WithNNO.N) 
                    (prod.lift (terminal.from WithNNO.N) (𝟙 WithNNO.N) ≫ h) ≫
                    prod.lift (terminal.from (WithNNO.N ⨯ B)) prod.fst) ≫ prod.fst)) 
              · rw[Limits.prod.lift_snd, Category.assoc, Limits.prod.lift_snd, Limits.prod.lift_fst]
            · rw[Category.assoc, Limits.prod.lift_snd, Category.assoc, Category.assoc,
              Limits.prod.lift_snd, 
              ← Category.assoc (prod.lift (terminal.from (WithNNO.N ⨯ B)) (𝟙 (WithNNO.N ⨯ B))),
              Limits.prod.lift_snd, Category.id_comp, Limits.prod.lift_snd]
        
          rw[← Category.assoc, this]
          simp only [Category.assoc]
        
        have hyp2_zero : (NNO C).zero ≫ aux_function2 f g = Limits.prod.lift (NNO C).zero f := by 
          rw[aux_function2, (NNO C).fac_zero]
        
        have hyp2_succ : (NNO C).s ≫ aux_function2 f g = aux_function2 f g ≫
                (Limits.prod.lift ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1 g)) := by 
                rw[aux_function2, (NNO C).fac_succ]
        
        exact (((NNO C).uniq 
        (Limits.prod.lift (NNO C).zero f) (Limits.prod.lift
    ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1 g)) 
    (Limits.prod.lift (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h)) 
        hyp1_zero hyp1_succ).trans 
    ((NNO C).uniq (Limits.prod.lift (NNO C).zero f) (Limits.prod.lift
    ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1 g)) (aux_function2 f g) 
    hyp2_zero hyp2_succ).symm)  
    rw[← this, Limits.prod.lift_snd, ← Limits.prod.leftUnitor_inv]             

--------------------------------------------------------------------------------------------

-- Recursion theorem (general case)



--Peano's third axiom

noncomputable def prec {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] : WithNNO.N (C := C) ⟶ WithNNO.N := 
      (Limits.prod.leftUnitor WithNNO.N).inv ≫ 
      Rec_Par_with_NNO_Aterm (NNO C).zero (prod.fst ≫ prod.snd) 

lemma succ_prec_id {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] : (NNO C).s ≫ prec = 𝟙 WithNNO.N := by 
      rw[prec, Limits.prod.leftUnitor_inv, ← Category.assoc, Limits.prod.comp_lift,
      Limits.terminal.hom_ext ((NNO C).s ≫ terminal.from WithNNO.N) (terminal.from WithNNO.N),
      Category.comp_id, ← Category.comp_id (terminal.from WithNNO.N),
      ← Category.id_comp (NNO C).s, ← Limits.prod.lift_map, Category.assoc,
      Rec_Par_with_NNO_Aterm_fac_succ, ← Category.assoc (prod.lift 
      (𝟙 ((⊤_ C) ⨯ WithNNO.N)) (Rec_Par_with_NNO_Aterm (NNO C).zero (prod.fst ≫ prod.snd))),
      Limits.prod.lift_fst, Category.id_comp, Limits.prod.lift_snd]

instance {C : Type u} [Category C]
    [HasTerminal C] [WithNNO C] [HasBinaryProducts C] :
    Mono (NNO C).s :=  
    {
      right_cancellation g h := by 
        intro hyp1 
        have hyp2 : (g ≫ (NNO C).s) ≫ prec = (h ≫ (NNO C).s) ≫ prec := congr_arg (· ≫ prec) hyp1 
        rw[Category.assoc, Category.assoc, succ_prec_id, Category.comp_id, Category.comp_id] at hyp2
        exact hyp2 
    }

