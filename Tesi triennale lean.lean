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
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
open CategoryTheory Limits WalkingPair ObjectProperty

set_option autoImplicit false
set_option checkBinderAnnotations false

universe u
 ----------------------------------------------------------------------

--Section 1: Proof that Finset is Cartesian closed

variable (α : Type u) [Inhabited α] [Infinite α]

-- Definition of the Finset category (described as the subcategory of the Type u category
-- which contains all the objects isomorphic to an object in Finset α)

def IsFinsetType (α : Type u) : ObjectProperty (Type u) :=
  fun X => ∃ s : Finset α, Nonempty (X ≃ (s : Type u))

--Proof that Finset has a terminal object

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

 --Proof that Finset has binary products

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

--Inferring the instances

example : HasTerminal (IsFinsetType α).FullSubcategory := inferInstance
example : HasBinaryProducts (IsFinsetType α).FullSubcategory := inferInstance


-------------------------------------------------------------------------

--Section 2: Definition of NNO and of category with NNO

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

--Section 3: Proof that Nat is an NNO in the Type category

example : HasTerminal (Type) := inferInstance

--Definition of the recursion function

noncomputable def RecFun {X : Type} (f : (⊤_ Type) → X) (g : X → X) :=
    fun n => match n with
    |0 => f ((terminal.from PUnit).hom PUnit.unit)
    |Nat.succ n => g (RecFun f g n)

--Key result

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

--Section 4: Some theorems about NNOs

--Useful lemma which will be used in several proofs

lemma banal_recursion {C : Type u} [Category C] [HasTerminal C]
        [WithNNO C] (f : WithNNO.N ⟶ WithNNO.N) (hyp_zero : (NNO C).zero ≫ f = (NNO C).zero)
        (hyp_succ : (NNO C).s ≫ f = f ≫ (NNO C).s) : f = 𝟙 WithNNO.N := by
        have eq_1 : f = (NNO C).recursion (NNO C).zero (NNO C).s := by
          apply (NNO C).uniq
          · rw[hyp_zero]
          · rw[hyp_succ]
        have eq_2 : 𝟙 WithNNO.N = (NNO C).recursion (NNO C).zero (NNO C).s := by
          apply (NNO C).uniq
          · rw[Category.comp_id]
          · rw[Category.comp_id, Category.id_comp]
        exact eq_1.trans eq_2.symm

--Proof that the NNO is unique up to isomorphism

def NNO_unique_up_to_iso {C : Type u} [Category C] [HasTerminal C]
    {N1 N2 : C} (n1 : IsNNO N1) (n2 : IsNNO N2) : Iso N1 N2 :=
  letI hom := n1.recursion n2.zero n2.s
  letI inv := n2.recursion n1.zero n1.s
  { hom := n1.recursion n2.zero n2.s
    inv := n2.recursion n1.zero n1.s
    hom_inv_id := by
      have eq_1 : hom ≫ inv = n1.recursion n1.zero n1.s := by
        apply n1.uniq
        · rw [← Category.assoc, n1.fac_zero, n2.fac_zero]
        · rw [← Category.assoc, n1.fac_succ, Category.assoc, n2.fac_succ,
            ← Category.assoc]
      have eq_2 : 𝟙 N1 = n1.recursion n1.zero n1.s := by
        apply n1.uniq
        · rw[Category.comp_id]
        · rw [Category.comp_id, Category.id_comp]
      exact eq_1.trans eq_2.symm

    inv_hom_id := by
      have eq_1 : inv ≫ hom = n2.recursion n2.zero n2.s := by
        apply n2.uniq
        · rw [← Category.assoc, n2.fac_zero, n1.fac_zero]
        · rw [← Category.assoc, n2.fac_succ, Category.assoc, n1.fac_succ,
            ← Category.assoc]
      have eq_2 : 𝟙 N2 = n2.recursion n2.zero n2.s := by
        apply n2.uniq
        · rw[Category.comp_id]
        · rw [Category.comp_id, Category.id_comp]
      exact eq_1.trans eq_2.symm
  }

------------------------------------------------------------------------------------

--Section 5: Peano's fourth axiom

--Proof that, if Peano's fourth axiom fails, zero factors into any morphism g : N ⟶ N

lemma aux1_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) (g : WithNNO.N ⟶ WithNNO.N) :
  ∃ (y : ⊤_ C ⟶ WithNNO.N), y ≫ g = (NNO C).zero := by
    let h := (NNO C).recursion (NNO C).zero g
    use x ≫ h
    rw[Category.assoc, ← (NNO C).fac_succ,
    ← Category.assoc, h1, (NNO C).fac_zero]

--Proof that, with the same hypothesis, s is the identity

lemma aux2_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) : (NNO C).s = 𝟙 (WithNNO.N) := by
  obtain ⟨ y, hy ⟩ := (aux1_fourth_axiom h1
    (Limits.terminal.from (WithNNO.N) ≫ (NNO C).zero ≫ (NNO C).s))
  apply banal_recursion
  · rw[← Category.assoc] at hy
    conv_lhs => rw [← Category.id_comp ((NNO C).zero), Category.assoc,
      Limits.terminal.hom_ext (𝟙 (⊤_ C)) (y ≫ Limits.terminal.from (WithNNO.N)),
      hy]
  · rfl

--Proof that, with the same hypothesis, the only morphism N ⟶ N is the identity

lemma aux3_fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) (g : WithNNO.N ⟶ WithNNO.N) :
   g = 𝟙 (WithNNO.N (C := C)) := by
   apply banal_recursion
   · conv_lhs => rw[← (NNO C).fac_zero (NNO C).zero g, Category.assoc,
    ← (NNO C).fac_succ (NNO C).zero g, aux2_fourth_axiom h1, Category.id_comp,
    (NNO C).fac_zero (NNO C).zero g]
   · rw[aux2_fourth_axiom h1, Category.id_comp, Category.comp_id]

--Proof that, if Peano's fourth axiom fails, N is terminal

noncomputable def not_fourth_axiom_Nterm {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {x : ⊤_ C ⟶ WithNNO.N}
  (h1 : x ≫ (NNO C).s = (NNO C).zero) : Iso (WithNNO.N) (⊤_ C) where
  hom := Limits.terminal.from (WithNNO.N)
  inv := (NNO C).zero
  hom_inv_id := by
    rw[aux3_fourth_axiom h1 (terminal.from WithNNO.N ≫ (NNO C).zero)]
  inv_hom_id := by
    rw[Limits.terminal.hom_ext (𝟙 (⊤_ C))]

--Alternative definition of NNO where the fourth axiom holds

structure Is_My_NNO {C : Type u} [Category C]
      [HasTerminal C] (N : C) extends IsNNO N where

non_term : ¬ Nonempty (IsTerminal N)

class With_My_NNO (C : Type u) [Category C] [HasTerminal C] extends WithNNO C where

non_term : ¬ Nonempty (IsTerminal N)

abbrev My_NNO (C : Type u) [Category C] [HasTerminal C] [With_My_NNO C] :
    Is_My_NNO (WithNNO.N (C := C)) where
  toIsNNO := WithNNO.isNNO
  non_term := With_My_NNO.non_term

--Proof that, with the new definition, Peano's fourth axiom holds

theorem fourth_axiom {C : Type u} [Category C]
  [HasTerminal C] [With_My_NNO C] : ¬ ∃ x : ⊤_ C ⟶ WithNNO.N,
  x ≫ (My_NNO C).s = (My_NNO C).zero := by
  by_contra h1
  rcases h1 with ⟨x, hx⟩
  have Nterm : IsTerminal (WithNNO.N (C := C)) := by
    exact (Limits.IsTerminal.ofIso (terminalIsTerminal) (not_fourth_axiom_Nterm hx).symm)
  exact ((My_NNO C).non_term) (Nonempty.intro Nterm)

----------------------------------------------------------------------------------------------

--Section 6: Peano's fifth axiom

--Auxiliary result

lemma aux_fifth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {M : C} {m : M ⟶ WithNNO.N} [Mono m]
  {zero' : ⊤_ C ⟶ M} {s' : M ⟶ M} (hyp_zero' : zero' ≫ m = (NNO C).zero)
  (hyp_s' : s' ≫ m = m ≫ (NNO C).s) : (NNO C).recursion zero' s' ≫ m = 𝟙 WithNNO.N := by
  apply banal_recursion
  · rw[← Category.assoc, (NNO C).fac_zero, hyp_zero']
  · rw[← Category.assoc, (NNO C).fac_succ, Category.assoc, hyp_s', Category.assoc]

--Proof of Peano's fifth axiom

noncomputable def fifth_axiom {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] {M : C} {m : M ⟶ WithNNO.N} [Mono m]
  {zero' : ⊤_ C ⟶ M} {s' : M ⟶ M} (hyp_zero' : zero' ≫ m = (NNO C).zero)
  (hyp_s' : s' ≫ m = m ≫ (NNO C).s) : Iso M WithNNO.N where
    hom := m
    inv := (NNO C).recursion zero' s'
    hom_inv_id := by
      have : (m ≫ (NNO C).recursion zero' s' ) ≫ m = (𝟙 M) ≫ m := by
        rw[Category.assoc, aux_fifth_axiom hyp_zero' hyp_s', Category.comp_id, Category.id_comp]
      rw[cancel_mono m] at this
      exact this
    inv_hom_id := aux_fifth_axiom hyp_zero' hyp_s'


-------------------------------------------------------------------

--Theorems that only hold in a Cartesian closed category

--Section 8a: Recursion theorem (case of A = ⊤)




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


--Definition that extracts a morphism N x B ⟶ B
-- from a morphism ⊤ x N x B ⟶ B in the canonical way

noncomputable def aux_function1_Aterm {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  Limits.prod WithNNO.N B ⟶ B:=
    (Limits.prod.leftUnitor (Limits.prod WithNNO.N B)).inv ≫
    (Limits.prod.associator (⊤_ C) (WithNNO.N) (B)).inv ≫ g

--Intermediate definition of ρ useful for the theorem

noncomputable def aux_function2_Aterm {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  WithNNO.N ⟶ Limits.prod WithNNO.N B :=
    (NNO C).recursion (Limits.prod.lift (NNO C).zero f) (Limits.prod.lift
    ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1_Aterm g))

--Definition of the seeked morphism in the recursion theorem

noncomputable def Rec_Par_with_NNO_Aterm {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
    Limits.prod (⊤_ C) WithNNO.N ⟶ B :=
    (Limits.prod.leftUnitor WithNNO.N).hom ≫ aux_function2_Aterm f g ≫ Limits.prod.snd

--Proof of an intermediate result for the commutativity of the left part of the diagram

lemma aux_Rec_Par {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  aux_function2_Aterm f g =
  Limits.prod.lift (𝟙 (WithNNO.N)) (aux_function2_Aterm f g ≫ Limits.prod.snd) := by
    apply Limits.prod.hom_ext
    · rw[Limits.prod.lift_fst]
      have eq_1 : aux_function2_Aterm f g ≫ Limits.prod.fst =
          (NNO C).recursion (NNO C).zero (NNO C).s := by
        apply (NNO C).uniq
        · rw[← Category.assoc, aux_function2_Aterm, (NNO C).fac_zero, Limits.prod.lift_fst]
        · conv_lhs => rw[← Category.assoc, aux_function2_Aterm, (NNO C).fac_succ, Category.assoc,
         Limits.prod.lift_fst, ← Category.assoc, ← aux_function2_Aterm]
      have eq_2 : 𝟙 WithNNO.N = (NNO C).recursion (NNO C).zero (NNO C).s := by
        apply (NNO C).uniq
        · rw[Category.comp_id]
        · rw[Category.comp_id, Category.id_comp]
      exact eq_1.trans eq_2.symm
    · rw[Limits.prod.lift_snd]

--Proof that the left part of the diagram commutes

theorem Rec_Par_with_NNO_Aterm_fac_zero {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  Limits.prod.map (𝟙 (⊤_ C)) (NNO C).zero ≫ Rec_Par_with_NNO_Aterm f g =
  (Limits.prod.leftUnitor (⊤_ C)).hom ≫ f := by
    unfold Rec_Par_with_NNO_Aterm
    letI ρ := ((NNO C).recursion (prod.lift (NNO C).zero f)
    (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1_Aterm g)))
    rw[← Category.assoc,
    Limits.terminal.hom_ext (Limits.prod.leftUnitor (⊤_ C)).hom Limits.prod.snd,
    Limits.prod.leftUnitor_hom, Limits.prod.map_snd, Category.assoc, aux_function2_Aterm,
    ← Category.assoc ((NNO C).zero) (ρ) (prod.snd), (NNO C).fac_zero, Limits.prod.lift_snd]

--Technical result used in the next proof

lemma aux_Rec_Par_Aterm_fac_succ {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  prod.snd ≫ (((NNO C).recursion (prod.lift (NNO C).zero f)
          (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1_Aterm g)))) ≫
          (Limits.prod.leftUnitor (WithNNO.N ⨯ B)).inv ≫
    (prod.associator (⊤_ C) WithNNO.N B).inv =
      prod.lift (𝟙 ((⊤_ C) ⨯ WithNNO.N)) (prod.snd ≫ ((NNO C).recursion (prod.lift (NNO C).zero f)
          (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1_Aterm g))) ≫ prod.snd) := by
        letI ρ := ((NNO C).recursion (prod.lift (NNO C).zero f)
          (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1_Aterm g)))
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
            rw[← aux_function2_Aterm, aux_Rec_Par, Limits.prod.lift_fst, Category.comp_id]
        · rw[Limits.prod.lift_snd, Limits.prod.associator_inv, Category.assoc, Category.assoc,
          Category.assoc, Limits.prod.lift_snd, Limits.prod.leftUnitor_inv,
          ← Category.assoc (prod.lift (terminal.from (WithNNO.N ⨯ B)) (𝟙 (WithNNO.N ⨯ B))),
          Limits.prod.lift_snd, Category.id_comp]

--Proof that the right part of the diagram commutes

theorem Rec_Par_with_NNO_Aterm_fac_succ {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B) :
  Limits.prod.map (𝟙 (⊤_ C)) (NNO C).s ≫ Rec_Par_with_NNO_Aterm f g =
  Limits.prod.lift (𝟙 (Limits.prod (⊤_ C) WithNNO.N)) (Rec_Par_with_NNO_Aterm f g) ≫ g := by
    unfold Rec_Par_with_NNO_Aterm
    letI ρ := ((NNO C).recursion (prod.lift (NNO C).zero f)
    (prod.lift (prod.fst ≫ (NNO C).s) (aux_function1_Aterm g)))
    rw[← Category.assoc,
    Limits.prod.leftUnitor_hom, Limits.prod.map_snd, Category.assoc, aux_function2_Aterm,
    ← Category.assoc ((NNO C).s), (NNO C).fac_succ,
    Category.assoc ρ, Limits.prod.lift_snd, aux_function1_Aterm,
    ← Category.assoc ((Limits.prod.leftUnitor (WithNNO.N ⨯ B)).inv), ← Category.assoc ρ,
    ← Category.assoc prod.snd, aux_Rec_Par_Aterm_fac_succ f g, aux_function1_Aterm]
    simp only [Category.assoc]

--Technical result used in the uniqueness proof

lemma aux1_Rec_Par_Aterm_unique {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C] {B : C}
  (h : Limits.prod (⊤_ C) WithNNO.N ⟶ B) : prod.lift (terminal.from WithNNO.N) (𝟙 WithNNO.N) ≫
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

--Technical result used in the uniqueness proof

lemma aux2_Rec_Par_Aterm_unique {C : Type u} [Category C]
  [HasTerminal C] [WithNNO C] [HasBinaryProducts C]
  {B : C} (f : ⊤_ C ⟶ B) (g : Limits.prod (Limits.prod (⊤_ C) WithNNO.N) B ⟶ B)
  (h : Limits.prod (⊤_ C) WithNNO.N ⟶ B)
  (hyp_zero : Limits.prod.map (𝟙 (⊤_ C)) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
  (hyp_succ : Limits.prod.map (𝟙 (⊤_ C)) (NNO C).s ≫ h =
  Limits.prod.lift (𝟙 (Limits.prod (⊤_ C) WithNNO.N)) h ≫ g) :
  Limits.prod.lift (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h) =
  aux_function2_Aterm f g := by
    have eq_1 : Limits.prod.lift (𝟙 WithNNO.N) ((Limits.prod.leftUnitor WithNNO.N).inv ≫ h) =
            (NNO C).recursion (Limits.prod.lift (NNO C).zero f) (Limits.prod.lift
    ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1_Aterm g)) := by
      apply (NNO C).uniq
      · rw[Limits.prod.leftUnitor_inv, Limits.prod.comp_lift, Category.comp_id,
          ← Category.assoc, Limits.prod.comp_lift,
          Limits.terminal.hom_ext (((NNO C).zero ≫ terminal.from WithNNO.N)) (𝟙 (⊤_ C)),
          Category.comp_id]
        have : prod.lift (𝟙 (⊤_ C)) (NNO C).zero =
            prod.lift (𝟙 (⊤_ C)) (𝟙 (⊤_ C)) ≫ prod.map (𝟙 (⊤_ C)) (NNO C).zero := by
          conv_lhs => rw[← Category.id_comp (𝟙 (⊤_ C)), ← Category.id_comp (NNO C).zero,
            ← Limits.prod.lift_map]
        rw[this, Category.assoc, hyp_zero, ← Category.assoc,
          Limits.prod.lift_fst, Category.id_comp]
      · conv_lhs => rw[Limits.prod.leftUnitor_inv, Limits.prod.comp_lift, Category.comp_id,
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
          Limits.prod.lift_fst, Category.id_comp, aux_function1_Aterm, Limits.prod.leftUnitor_inv,
          Limits.prod.associator_inv]
        rw[← Category.assoc, aux1_Rec_Par_Aterm_unique]
        simp only [Category.assoc]
    have eq_2 : aux_function2_Aterm f g =
    (NNO C).recursion (Limits.prod.lift (NNO C).zero f) (Limits.prod.lift
    ((Limits.prod.fst) ≫ (NNO C).s) (aux_function1_Aterm g)) := by
      apply (NNO C).uniq
      · rw[aux_function2_Aterm, (NNO C).fac_zero]
      · rw[aux_function2_Aterm, (NNO C).fac_succ]
    exact eq_1.trans eq_2.symm

--Proof of the uniqueness of the seeked morphism

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
    rw[← aux2_Rec_Par_Aterm_unique f g h hyp_zero hyp_succ,
    Limits.prod.lift_snd, ← Limits.prod.leftUnitor_inv]

--------------------------------------------------------------------------------------------

-- Section 8b: Recursion theorem (general case)

--noncomputable def aux_function1_Rec_Par {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] [MonoidalCategory C] [CartesianClosed C]
      {A B : C} (f : A ⟶ B) (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :=
      CartesianClosed.curry ((Limits.prod.leftUnitor A).hom ≫ f)


--------------------------------------------------------------------------------------------

--Section 9: Peano's third axiom

--Definition of the left inverse of s (namely, the function precedent)
noncomputable def prec {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] : WithNNO.N (C := C) ⟶ WithNNO.N :=
      (Limits.prod.leftUnitor WithNNO.N).inv ≫
      Rec_Par_with_NNO_Aterm (NNO C).zero (prod.fst ≫ prod.snd)

--Proof that prec is a left inverse for s

lemma succ_prec_id {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] : (NNO C).s ≫ prec = 𝟙 WithNNO.N := by
      rw[prec, Limits.prod.leftUnitor_inv, ← Category.assoc, Limits.prod.comp_lift,
      Limits.terminal.hom_ext ((NNO C).s ≫ terminal.from WithNNO.N) (terminal.from WithNNO.N),
      Category.comp_id, ← Category.comp_id (terminal.from WithNNO.N),
      ← Category.id_comp (NNO C).s, ← Limits.prod.lift_map, Category.assoc,
      Rec_Par_with_NNO_Aterm_fac_succ, ← Category.assoc (prod.lift
      (𝟙 ((⊤_ C) ⨯ WithNNO.N)) (Rec_Par_with_NNO_Aterm (NNO C).zero (prod.fst ≫ prod.snd))),
      Limits.prod.lift_fst, Category.id_comp, Limits.prod.lift_snd]

--Proof of Peano's third axiom

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

------------------------------------------------------------------------------------------------

--Section 10: Proof that Finset does not have an NNO

--Proof that Fin 2 (= {0,1}) has an isomorphic equivalent in Finset

theorem isFinsetType_fin_two : IsFinsetType α (ULift (Fin 2)) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine ⟨{a, b}, ⟨?_⟩⟩
  apply Fintype.equivOfCardEq
  rw [Fintype.card_ulift, Fintype.card_fin, Fintype.card_coe, Finset.card_pair hab]

--Definition of Fin 2 embedded in Finset

def finTwoObj : (IsFinsetType α).FullSubcategory :=
  ⟨ULift (Fin 2), isFinsetType_fin_two α⟩

-- Proof that, if Finset has an NNO, the function s is not surjective

lemma Finset_NNO_s_not_surj (NatObj : WithNNO (IsFinsetType α).FullSubcategory) :
    ¬ Function.Surjective (NatObj.isNNO.s) := by
    unfold Function.Surjective
    by_contra h1
    have hterm : Nonempty (⊤_ (IsFinsetType α).FullSubcategory).obj := by
      have hPUnit : IsFinsetType α PUnit :=
        ⟨{default}, ⟨{ toFun := fun _ => ⟨default, Finset.mem_singleton_self _⟩
                       invFun := fun _ => PUnit.unit
                       left_inv := fun _ => by rfl
                       right_inv := fun q => by
                         obtain ⟨y, hy⟩ := q
                         simp only [Finset.mem_singleton] at hy
                         subst hy; rfl }⟩⟩
      let PUnitObj : (IsFinsetType α).FullSubcategory := ⟨PUnit, hPUnit⟩
      let φ : PUnitObj ⟶ ⊤_ (IsFinsetType α).FullSubcategory :=
        Limits.terminalIsTerminal.from PUnitObj
      exact ⟨(ConcreteCategory.hom φ) PUnit.unit⟩
    obtain ⟨pt⟩ := hterm
    set m := (ConcreteCategory.hom NatObj.isNNO.zero) pt with hm
    obtain ⟨k, hk⟩ := h1 m
    let f : ⊤_ (IsFinsetType α).FullSubcategory ⟶ finTwoObj α :=
        ⟨TypeCat.ofHom (fun _ => ULift.up (0 : Fin 2))⟩
    let g : finTwoObj α ⟶ finTwoObj α :=
        ⟨TypeCat.ofHom (fun _ => ULift.up (1 : Fin 2))⟩
    let h : NatObj.N ⟶ finTwoObj α := NatObj.isNNO.recursion f g
    have hf : f pt = ULift.up (0 : Fin 2) := by rfl
    have hg : g (h k) = ULift.up (1 : Fin 2) := by rfl
    have : f pt = g (h k) := by
      simp only [h]
      rw[← NatObj.isNNO.fac_zero f, ConcreteCategory.comp_apply, ← hm,
      ← hk, ← ConcreteCategory.comp_apply, NatObj.isNNO.fac_succ f g,
      ConcreteCategory.comp_apply, NatObj.isNNO.fac_zero]
    exact absurd (ULift.up.inj ((hf.symm.trans this).trans hg)) (by decide)

--Proof that the inclusion functor Finset ⥤ Type u maps monomorphisms into monomorphisms

instance : Functor.PreservesMonomorphisms ((IsFinsetType α).ι) :=
{
  preserves {X Y} f := by
    intro mono_f; dsimp
    apply (CategoryTheory.mono_iff_injective f.hom).mpr
    unfold Function.Injective
    intro x1 x2 hf
    let oneFinset : Finset α := {default}
    let oneObj : (IsFinsetType α).FullSubcategory :=
      FullSubcategory.mk (oneFinset : Type u) ⟨oneFinset, ⟨Equiv.refl _⟩⟩
    let g : oneObj ⟶ X := homMk (TypeCat.ofHom (fun _ : (oneFinset : Type u) => x1))
    let h : oneObj ⟶ X := homMk (TypeCat.ofHom (fun _ : (oneFinset : Type u) => x2))
    have : g ≫ f = h ≫ f := by
      ext z
      simp [g, h, hf]
    have : g = h := mono_f.right_cancellation g h this
    have hpoint :
        ⇑(ConcreteCategory.hom g) default = ⇑(ConcreteCategory.hom h) default := by
      simpa using congrArg (fun k => ⇑(ConcreteCategory.hom k) default) this
    change x1 = x2
    dsimp [g, h] at hpoint
    exact hpoint
}

example : Functor.PreservesMonomorphisms ((IsFinsetType α).ι) := inferInstance

-- Proof that, with the same hypothesis, the function s is injective

lemma Finset_NNO_s_inj (NatObj : WithNNO (IsFinsetType α).FullSubcategory) :
    Function.Injective (NatObj.isNNO.s) := by
    apply (CategoryTheory.mono_iff_injective ((IsFinsetType α).ι.map NatObj.isNNO.s)).mp
    apply (CategoryTheory.Functor.mono_map_iff_mono (IsFinsetType α).ι NatObj.isNNO.s).mpr
    exact inferInstance

--Key result

lemma Finset_without_NNO : ¬ Nonempty (WithNNO (IsFinsetType α).FullSubcategory) := by
  by_contra h1
  have NatObj : WithNNO (IsFinsetType α).FullSubcategory := Classical.choice h1
  have : Finite ((IsFinsetType α).ι.obj WithNNO.N) := by
    dsimp
    rcases NatObj.N.property with ⟨s, ⟨e⟩⟩
    exact Finite.of_equiv (s : Type u) e.symm
  exact (Finset_NNO_s_not_surj α NatObj) ((Function.Injective.surjective_of_finite
          (Equiv.refl ((IsFinsetType α).ι.obj NatObj.N))) (Finset_NNO_s_inj α NatObj))

-----------------------------------------------------------------------------------------

--Section 11: NNO as initial algebra

--Definition of the functor T on which the algebra is built

noncomputable def T {C : Type u} [Category C] [HasTerminal C]
      [HasBinaryCoproducts C] : Functor C C where

obj X := Limits.coprod (⊤_ C) X
map f := Limits.coprod.map (𝟙 (⊤_ C)) f

--Definition of the NNO as an initial algebra (equipped with the [0,s] morphism)

noncomputable def Nalg {C : Type u} [Category C] [HasTerminal C] [WithNNO C]
      [HasBinaryCoproducts C] : Endofunctor.Algebra (T : Functor C C) where

a := WithNNO.N
str := Limits.coprod.desc (NNO C).zero (NNO C).s

--Definition of a morphism of T-algebras Nalg ⟶ A (with A a generic T-algebra)

noncomputable def aux1_init_alg {C : Type u} [Category C] [HasTerminal C] [WithNNO C]
      [HasBinaryCoproducts C] (A : Endofunctor.Algebra (T : Functor C C)) : WithNNO.N ⟶ A.a :=
      (NNO C).recursion (Limits.coprod.inl ≫ A.str) (Limits.coprod.inr ≫ A.str)

--Banal result about coproduct diagrams

lemma aux_lemma_init_alg {C : Type u} [Category C] [HasTerminal C] [WithNNO C]
      [HasBinaryCoproducts C] (A : Endofunctor.Algebra (T : Functor C C)) :
      coprod.desc (coprod.inl ≫ A.str) (coprod.inr ≫ A.str) = A.str := by
      apply Limits.coprod.hom_ext
      · rw[Limits.coprod.inl_desc]
      · rw[Limits.coprod.inr_desc]

--Proof that aux1_init_alg is a morphism of T-algebras

noncomputable def init_mor {C : Type u} [Category C] [HasTerminal C] [WithNNO C]
      [HasBinaryCoproducts C] (A : Endofunctor.Algebra (T : Functor C C)) :
      Endofunctor.Algebra.Hom Nalg A where

f := aux1_init_alg A
h := by
    dsimp [T, Nalg, aux1_init_alg]
    rw[Limits.coprod.desc_comp, (NNO C).fac_zero, (NNO C).fac_succ]
    conv_rhs => rw[← Category.id_comp (Limits.coprod.inl ≫ A.str), ← Limits.coprod.map_desc,
    Category.id_comp, aux_lemma_init_alg]

--Proof that it is the only morphism of T-algebras Nalg ⟶ A

lemma init_mor_uniq {C : Type u} [Category C] [HasTerminal C] [WithNNO C]
      [HasBinaryCoproducts C] (A : Endofunctor.Algebra (T : Functor C C))
      (g : Endofunctor.Algebra.Hom Nalg A) : g = init_mor A := by
      have : T.map g.f ≫ A.str = Nalg.str ≫ g.f := g.h
      dsimp [T, Nalg, aux1_init_alg] at this
      rw[Limits.coprod.desc_comp, ← aux_lemma_init_alg,
      Limits.coprod.map_desc, Category.id_comp] at this
      apply Endofunctor.Algebra.Hom.ext
      dsimp [init_mor, aux1_init_alg]
      apply (NNO C).uniq
      · have helper : coprod.inl ≫ coprod.desc (coprod.inl ≫ A.str) (g.f ≫ coprod.inr ≫ A.str)
         = coprod.inl ≫ coprod.desc ((NNO C).zero ≫ g.f) ((NNO C).s ≫ g.f) := by
          exact (Limits.coprod.hom_ext_iff.mp this).left
        rw[Limits.coprod.inl_desc, Limits.coprod.inl_desc] at helper
        exact helper.symm
      · have helper : coprod.inr ≫ coprod.desc (coprod.inl ≫ A.str) (g.f ≫ coprod.inr ≫ A.str)
         = coprod.inr ≫ coprod.desc ((NNO C).zero ≫ g.f) ((NNO C).s ≫ g.f) := by
          exact (Limits.coprod.hom_ext_iff.mp this).right
        rw[Limits.coprod.inr_desc, Limits.coprod.inr_desc] at helper
        exact helper.symm

--Proof that Nalg is an initial object in the category of T-algebras

noncomputable def NNO_init_alg {C : Type u} [Category C] [HasTerminal C] [WithNNO C]
      [HasBinaryCoproducts C] : IsInitial (Nalg : Endofunctor.Algebra (T : Functor C C)) := by
      unfold IsInitial
      exact {
        desc s := init_mor s.pt
        fac s j := j.as.elim
        uniq s m := by
          intros
          exact init_mor_uniq s.pt m
            }

-----------------------------------------------------------------------------------------------
