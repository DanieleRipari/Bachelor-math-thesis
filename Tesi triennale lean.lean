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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
open CategoryTheory Limits WalkingPair ObjectProperty

set_option autoImplicit false


/-
Main definitions

WithNNO
WithMyNNO
Rec_Par_with_NNO
NNO_sum
NNO_product

Main results

NNO_unique_up_to_iso
not_fourth_axiom_Nterm
fourth_axiom
fifth_axiom
Rec_Par_with_NNO_fac_zero
Rec_Par_with_NNO_fac_succ
Rec_Par_with_NNO_unique
Finset_without_NNO
NNO_init_alg
-/
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

omit [Infinite α] in
theorem Finset_has_terminal : HasTerminal (IsFinsetType α).FullSubcategory := inferInstance
omit [Inhabited α] in
theorem Finset_has_binary_products : HasBinaryProducts (IsFinsetType α).FullSubcategory :=
        inferInstance


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

noncomputable def IsNNO.ofIso {C : Type u} [Category C] [HasTerminal C]
    {N1 N2 : C} (n1 : IsNNO N1) (Equiv : Iso N1 N2) : IsNNO N2 :=
    {
      zero := n1.zero ≫ Equiv.hom
      s := Equiv.inv ≫ n1.s ≫ Equiv.hom
      recursion f g := Equiv.inv ≫ n1.recursion f g
      fac_zero f g := by
        rw[Category.assoc, ← Category.assoc (Equiv.hom), Equiv.hom_inv_id,
        Category.id_comp, n1.fac_zero]
      fac_succ f g := by
        rw[Category.assoc, Category.assoc, ← Category.assoc (Equiv.hom),
        Equiv.hom_inv_id, Category.id_comp, n1.fac_succ, Category.assoc]
      uniq f g h hyp_zero hyp_succ := by
        rw[Category.assoc] at hyp_zero
        have hyp_succ' : Equiv.hom ≫ (Equiv.inv ≫ n1.s ≫ Equiv.hom) ≫ h =
        Equiv.hom ≫ h ≫ g := congr_arg (Equiv.hom ≫ ·) hyp_succ
        rw[← Category.assoc, ← Category.assoc (Equiv.hom) (Equiv.inv),
        Equiv.hom_inv_id, Category.id_comp, Category.assoc] at hyp_succ'
        nth_rewrite 2 [← Category.assoc] at hyp_succ'
        have goal : Equiv.hom ≫ h = n1.recursion f g :=
        n1.uniq f g (Equiv.hom ≫ h) hyp_zero hyp_succ'
        have goal' : Equiv.inv ≫ Equiv.hom ≫ h = Equiv.inv ≫ n1.recursion f g :=
          congr_arg (Equiv.inv ≫ ·) goal
        rw[← Category.assoc, Equiv.inv_hom_id, Category.id_comp] at goal'
        exact goal'
    }

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

/- Definition that extracts a morphism N x B ⟶ B
 from a morphism ⊤ x N x B ⟶ B in the canonical way -/

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

instance (C : Type u) [Category C] [HasTerminal C] [HasBinaryProducts C] :
    HasFiniteProducts C :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts

--Definition of a morphism ⊤ ⟶ (A ⟹ B) extracted from the morphism f : A ⟶ B

noncomputable def aux_function1_Rec_Par {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C]
      {A B : C} (f : A ⟶ B) : ⊤_ C ⟶ (ihom A).obj B :=
      MonoidalClosed.curry ((Limits.prod.rightUnitor A).hom ≫ f)

--Definition of a morphism A x N x (A ⟹ B) ⟶ B from the morphism g : A x N x B ⟶ B

noncomputable def aux_function2_Rec_Par {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C]
      {A B : C} (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
      Limits.prod A (Limits.prod WithNNO.N ((ihom A).obj B)) ⟶ B :=
      (Limits.prod.lift
      ((Limits.prod.associator A WithNNO.N ((ihom A).obj B)).inv ≫ Limits.prod.fst)
      (Limits.prod.lift (Limits.prod.fst) (Limits.prod.snd ≫ Limits.prod.snd)
      ≫ (ihom.ev A).app B)) ≫ g

--Definition of the exponential transpose of the previous morphism

noncomputable def aux_function3_Rec_Par {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C]
      {A B : C} (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
      Limits.prod (Limits.prod (⊤_ C) (WithNNO.N)) ((ihom A).obj B) ⟶ (ihom A).obj B :=
      (Limits.prod.associator (⊤_ C) (WithNNO.N) ((ihom A).obj B)).hom ≫
      (Limits.prod.leftUnitor (Limits.prod WithNNO.N ((ihom A).obj B))).hom ≫
      MonoidalClosed.curry (aux_function2_Rec_Par g)

--Definition of the recursion morphism (in the case A = ⊤) with aux1 and aux3

noncomputable def aux_function4_Rec_Par {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C]
      {A B : C} (f : A ⟶ B) (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
      WithNNO.N ⟶ (ihom A).obj B :=
      (Limits.prod.leftUnitor WithNNO.N).inv ≫
      Rec_Par_with_NNO_Aterm (aux_function1_Rec_Par f) (aux_function3_Rec_Par g)

--Definition of the seeked recursion morphism (in the general case)

noncomputable def Rec_Par_with_NNO {C : Type u} [Category C] [HasTerminal C]
      [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C]
      {A B : C} (f : A ⟶ B) (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
      Limits.prod A WithNNO.N ⟶ B :=
      Limits.prod.map (𝟙 A) (aux_function4_Rec_Par f g) ≫ (ihom.ev A).app B

--Proof of the universal property of the exponential

theorem expon_univ_prop {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {X Y Z : C}
    (f : Limits.prod X Y ⟶ Z) :
    Limits.prod.map (𝟙 X) (MonoidalClosed.curry f) ≫ (ihom.ev X).app Z = f := by
    have h1 := MonoidalClosed.uncurry_curry f
    rw[MonoidalClosed.uncurry_eq] at h1
    have h2 : MonoidalCategoryStruct.whiskerLeft X (MonoidalClosed.curry f) =
    Limits.prod.map (𝟙 X) (MonoidalClosed.curry f) := by
        apply Limits.prod.hom_ext
        · exact ((CartesianMonoidalCategory.whiskerLeft_fst _ _).trans
          ((Limits.prod.map_fst _ _).trans (Category.comp_id _)).symm)
        · exact (CartesianMonoidalCategory.whiskerLeft_snd _ _).trans (Limits.prod.map_snd _ _).symm
    rw [h2] at h1
    exact h1

--Proof of the identity between the structures MonoidalCategory.whisker and Limits.prod.map

lemma whiskerLeft_eq_prod_map {C : Type u} [Category C] [HasTerminal C]
    [HasBinaryProducts C] {A X Y : C} (f : X ⟶ Y) :
    MonoidalCategoryStruct.whiskerLeft A f = Limits.prod.map (𝟙 A) f := by
    apply Limits.prod.hom_ext
    · exact ((CartesianMonoidalCategory.whiskerLeft_fst _ _).trans
      ((Limits.prod.map_fst _ _).trans (Category.comp_id _)).symm)
    · exact (CartesianMonoidalCategory.whiskerLeft_snd _ _).trans (Limits.prod.map_snd _ _).symm

--Proof of the commutativity of the left side of the diagram

theorem Rec_Par_with_NNO_fac_zero {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 A) (NNO C).zero ≫ Rec_Par_with_NNO f g = Limits.prod.fst ≫ f := by
    rw[Rec_Par_with_NNO, Limits.prod.map_map_assoc, Category.id_comp, aux_function4_Rec_Par,
    Rec_Par_with_NNO_Aterm, ← Category.assoc ((Limits.prod.leftUnitor WithNNO.N).inv)
    ((Limits.prod.leftUnitor WithNNO.N).hom)
    (aux_function2_Aterm (aux_function1_Rec_Par f) (aux_function3_Rec_Par g) ≫ prod.snd),
    (Limits.prod.leftUnitor WithNNO.N).inv_hom_id, Category.id_comp, aux_function2_Aterm,
    ← Category.assoc, (NNO C).fac_zero, Limits.prod.lift_snd,
    aux_function1_Rec_Par, Limits.prod.rightUnitor_hom]
    exact expon_univ_prop (Limits.prod.fst ≫ f)

--Technical results needed in the proof that the right side commutes

theorem aux1_Rec_Par_fac_succ {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    (NNO C).recursion (prod.lift (NNO C).zero (aux_function1_Rec_Par f))
    (prod.lift (prod.fst ≫ (NNO C).s)
    (MonoidalClosed.curry (prod.lift (prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.snd ≫ prod.snd) ≫ prod.fst)
    (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ (ihom.ev A).app B) ≫ g))) ≫ prod.fst =
     𝟙 WithNNO.N := by
      apply banal_recursion
      · rw[← Category.assoc, (NNO C).fac_zero, Limits.prod.lift_fst]
      · conv_lhs => rw[← Category.assoc, (NNO C).fac_succ, Category.assoc, Limits.prod.lift_fst,
        Limits.prod.lift_fst]
        conv_rhs => rw[Limits.prod.lift_fst]
        simp only [Category.assoc]

theorem aux2_Rec_Par_fac_succ {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    prod.map (𝟙 A)
        ((NNO C).recursion (prod.lift (NNO C).zero (aux_function1_Rec_Par f))
        (prod.lift (prod.fst ≫ (NNO C).s) (MonoidalClosed.curry
        (prod.lift ((prod.associator A WithNNO.N ((ihom A).obj B)).inv ≫ prod.fst)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ (ihom.ev A).app B) ≫ g)))) ≫
      prod.lift prod.fst (prod.snd ≫ prod.snd) =
      prod.map (𝟙 A)
      ((NNO C).recursion (prod.lift (NNO C).zero (aux_function1_Rec_Par f))
      (prod.lift (prod.fst ≫ (NNO C).s) (MonoidalClosed.curry
      (prod.lift ((prod.associator A WithNNO.N ((ihom A).obj B)).inv ≫ prod.fst)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ (ihom.ev A).app B) ≫ g))) ≫ prod.snd) := by
        apply Limits.prod.hom_ext
        · rw[Category.assoc, Limits.prod.lift_fst, Limits.prod.map_fst, Limits.prod.map_fst]
        · rw[Category.assoc, Limits.prod.lift_snd, ← Category.assoc, Limits.prod.map_snd,
          Limits.prod.map_snd]
          simp only [Category.assoc]

theorem aux3_Rec_Par_fac_succ {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    (prod.map (𝟙 A)
      ((NNO C).recursion (prod.lift (NNO C).zero (aux_function1_Rec_Par f))
        (prod.lift (prod.fst ≫ (NNO C).s)
          (MonoidalClosed.curry
            (prod.lift ((prod.associator A WithNNO.N ((ihom A).obj B)).inv ≫ prod.fst)
                (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ (ihom.ev A).app B) ≫
              g)))) ≫
    prod.lift ((prod.associator A WithNNO.N ((ihom A).obj B)).inv ≫ prod.fst)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ (ihom.ev A).app B)) =
      prod.lift (𝟙 (A ⨯ WithNNO.N))
      (prod.map (𝟙 A ≫ 𝟙 A)
          ((NNO C).recursion (prod.lift (NNO C).zero (aux_function1_Rec_Par f))
              (prod.lift (prod.fst ≫ (NNO C).s) (MonoidalClosed.curry (aux_function2_Rec_Par g))) ≫
            prod.snd) ≫
        (ihom.ev A).app B) := by
        apply Limits.prod.hom_ext
        · rw[Category.assoc, Limits.prod.lift_fst, Limits.prod.lift_fst,
          Limits.prod.associator_inv, Limits.prod.lift_fst, Limits.prod.comp_lift]
          apply Limits.prod.hom_ext
          · rw[Limits.prod.lift_fst, Limits.prod.map_fst, Category.comp_id, Category.id_comp]
          · rw[Limits.prod.lift_snd, ← Category.assoc, Limits.prod.map_snd, Category.assoc]
            erw[aux1_Rec_Par_fac_succ]
            rw[Category.comp_id, Category.id_comp]
        · rw[Limits.prod.lift_snd, Category.assoc, Limits.prod.lift_snd, Category.comp_id,
          aux_function2_Rec_Par, ← Category.assoc, aux2_Rec_Par_fac_succ]
          rfl

--Proof of the commutativity of the right side of the diagram

theorem Rec_Par_with_NNO_fac_succ {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    Limits.prod.map (𝟙 A) (NNO C).s ≫ Rec_Par_with_NNO f g =
    Limits.prod.lift (𝟙 (Limits.prod A WithNNO.N)) (Rec_Par_with_NNO f g) ≫ g := by
    rw[Rec_Par_with_NNO, Limits.prod.map_map_assoc, Category.id_comp, aux_function4_Rec_Par,
    Rec_Par_with_NNO_Aterm, ← Category.assoc ((Limits.prod.leftUnitor WithNNO.N).inv)
    ((Limits.prod.leftUnitor WithNNO.N).hom)
    (aux_function2_Aterm (aux_function1_Rec_Par f) (aux_function3_Rec_Par g) ≫ prod.snd),
    (Limits.prod.leftUnitor WithNNO.N).inv_hom_id, Category.id_comp, aux_function2_Aterm,
    ← Category.assoc, (NNO C).fac_succ, ← Category.comp_id (𝟙 A),
    Category.assoc, ← Limits.prod.map_map_assoc, Limits.prod.lift_snd,
    aux_function1_Aterm, aux_function3_Rec_Par]
    have : ((Limits.prod.leftUnitor (Limits.prod WithNNO.N ((ihom A).obj B))).inv ≫
    (Limits.prod.associator (⊤_ C) WithNNO.N ((ihom A).obj B)).inv ≫
            (Limits.prod.associator (⊤_ C) WithNNO.N ((ihom A).obj B)).hom ≫
              (Limits.prod.leftUnitor (Limits.prod WithNNO.N ((ihom A).obj B))).hom ≫
              MonoidalClosed.curry (aux_function2_Rec_Par g)) =
              (((Limits.prod.leftUnitor (Limits.prod WithNNO.N ((ihom A).obj B))).inv ≫
              ((Limits.prod.associator (⊤_ C) WithNNO.N ((ihom A).obj B)).inv ≫
            (Limits.prod.associator (⊤_ C) WithNNO.N ((ihom A).obj B)).hom) ≫
              (Limits.prod.leftUnitor (Limits.prod WithNNO.N ((ihom A).obj B))).hom) ≫
              MonoidalClosed.curry (aux_function2_Rec_Par g))
             := by
             simp only [Category.assoc]
    rw[this, (Limits.prod.associator (⊤_ C) WithNNO.N ((ihom A).obj B)).inv_hom_id,
    Category.id_comp, (Limits.prod.leftUnitor (Limits.prod WithNNO.N ((ihom A).obj B))).inv_hom_id,
    Category.id_comp]
    erw [expon_univ_prop (aux_function2_Rec_Par g)]
    conv_lhs => rw[aux_function2_Rec_Par, ← Category.assoc]
    erw [aux3_Rec_Par_fac_succ]
    rfl

--Technical results used in the uniqueness proof

theorem aux1_Rec_Par_unique {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (h : Limits.prod A WithNNO.N ⟶ B)
    (hyp_zero : Limits.prod.map (𝟙 A) (NNO C).zero ≫ h = Limits.prod.fst ≫ f) :
    (NNO C).zero ≫ MonoidalClosed.curry h =
      MonoidalClosed.curry ((Limits.prod.rightUnitor A).hom ≫ f) := by
        apply MonoidalClosed.uncurry_injective
        rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
        MonoidalClosed.uncurry_curry]
        have h1 : MonoidalCategoryStruct.whiskerLeft A (NNO C).zero =
        Limits.prod.map (𝟙 A) (NNO C).zero := by
          apply Limits.prod.hom_ext
          · exact ((CartesianMonoidalCategory.whiskerLeft_fst _ _).trans
            ((Limits.prod.map_fst _ _).trans (Category.comp_id _)).symm)
          · exact ((CartesianMonoidalCategory.whiskerLeft_snd _ _).trans
            (Limits.prod.map_snd _ _).symm)
        erw [h1, hyp_zero]
        rw [Limits.prod.rightUnitor_hom]
        rfl

theorem aux2_Rec_Par_unique {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) (h : Limits.prod A WithNNO.N ⟶ B)
    (hyp_zero : Limits.prod.map (𝟙 A) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
    (hyp_succ : Limits.prod.map (𝟙 A) (NNO C).s ≫ h =
    Limits.prod.lift (𝟙 (Limits.prod A WithNNO.N)) h ≫ g) :
    (Limits.prod.leftUnitor WithNNO.N).hom ≫ MonoidalClosed.curry h =
    Rec_Par_with_NNO_Aterm (aux_function1_Rec_Par f) (aux_function3_Rec_Par g) := by
    apply Rec_Par_with_NNO_Aterm_unique
    · rw[Limits.prod.leftUnitor_hom, ← Category.assoc, Limits.prod.map_snd,
      aux_function1_Rec_Par, Limits.terminal.hom_ext (prod.fst) (prod.snd),
      Category.assoc, aux1_Rec_Par_unique f h hyp_zero]
    · rw[Limits.prod.leftUnitor_hom, ← Category.assoc, Limits.prod.map_snd,
      aux_function3_Rec_Par, Limits.prod.associator_hom, Limits.prod.leftUnitor_hom,
      ← Category.assoc (prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)),
      Limits.prod.lift_snd, ← Category.assoc, Limits.prod.comp_lift,
      ← Category.assoc (prod.lift (𝟙 ((⊤_ C) ⨯ WithNNO.N)) (prod.snd ≫ MonoidalClosed.curry h)),
      Limits.prod.lift_fst, Limits.prod.lift_snd, Category.id_comp]
      apply MonoidalClosed.uncurry_injective
      rw [Category.assoc, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      whiskerLeft_eq_prod_map, whiskerLeft_eq_prod_map, whiskerLeft_eq_prod_map]
      erw [hyp_succ, aux_function2_Rec_Par, ← Category.assoc, ← Category.assoc]
      congr 1
      apply Limits.prod.hom_ext
      · erw [Category.assoc, Limits.prod.lift_fst, Category.comp_id, Category.assoc,
        Limits.prod.lift_fst, Limits.prod.associator_inv, ← Category.assoc,
        Limits.prod.comp_lift, Limits.prod.lift_fst]
        apply Limits.prod.hom_ext
        · erw [Limits.prod.map_fst, Category.assoc, Limits.prod.lift_fst, Limits.prod.map_fst]
        · erw [Limits.prod.map_snd, Category.assoc, Limits.prod.lift_snd, ← Category.assoc,
          Limits.prod.map_snd, Category.assoc, Limits.prod.lift_fst]
      · erw [Category.assoc, Limits.prod.lift_snd, Category.assoc, Limits.prod.lift_snd,
         ← Category.assoc, Limits.prod.comp_lift, Limits.prod.map_fst,
         ← Category.assoc (prod.map (𝟙 A)
         (prod.lift prod.snd (prod.snd ≫ MonoidalClosed.curry h))), Limits.prod.map_snd,
         Category.comp_id, ← Category.assoc, Category.assoc (prod.snd), Limits.prod.lift_snd]
        have : (Limits.prod.lift (Limits.prod.fst :
        Limits.prod A (Limits.prod (⊤_ C) WithNNO.N) ⟶ A)
        (Limits.prod.snd ≫ Limits.prod.snd ≫ MonoidalClosed.curry h) =
        Limits.prod.map (𝟙 A) Limits.prod.snd ≫
        Limits.prod.map (𝟙 A) (MonoidalClosed.curry h)) := by
          rw [Limits.prod.map_map, Category.id_comp]
          apply Limits.prod.hom_ext
          · rw [Limits.prod.lift_fst, Limits.prod.map_fst, Category.comp_id]
          · rw [Limits.prod.lift_snd, Limits.prod.map_snd]
        rw[CategoryTheory.ihom.ihom_adjunction_unit, Category.assoc (prod.snd)]
        erw[← MonoidalClosed.curry_eq, this, Category.assoc, expon_univ_prop h]
        rfl

--Proof that h is the exponential transpose of the aux_function4

theorem h_eq_expon_transp {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) (h : Limits.prod A WithNNO.N ⟶ B)
    (hyp_zero : Limits.prod.map (𝟙 A) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
    (hyp_succ : Limits.prod.map (𝟙 A) (NNO C).s ≫ h =
    Limits.prod.lift (𝟙 (Limits.prod A WithNNO.N)) h ≫ g) :
    MonoidalClosed.curry h = (aux_function4_Rec_Par f g) := by
    rw[aux_function4_Rec_Par, ← Category.id_comp (MonoidalClosed.curry h),
    ← (Limits.prod.leftUnitor (WithNNO.N)).inv_hom_id, Category.assoc,
    aux2_Rec_Par_unique f g h hyp_zero hyp_succ]

--Proof that Rec_Par_with_NNO is the exponential transpose of aux_function4

theorem Rec_Par_eq_expon_transp {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) :
    MonoidalClosed.curry (Rec_Par_with_NNO f g) = (aux_function4_Rec_Par f g) := by
    apply MonoidalClosed.uncurry_injective
    rw[MonoidalClosed.uncurry_curry, Rec_Par_with_NNO, MonoidalClosed.uncurry_eq,
    whiskerLeft_eq_prod_map]
    rfl

--Main result

theorem Rec_Par_with_NNO_unique {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {A B : C} (f : A ⟶ B)
    (g : Limits.prod (Limits.prod A WithNNO.N) B ⟶ B) (h : Limits.prod A WithNNO.N ⟶ B)
    (hyp_zero : Limits.prod.map (𝟙 A) (NNO C).zero ≫ h = Limits.prod.fst ≫ f)
    (hyp_succ : Limits.prod.map (𝟙 A) (NNO C).s ≫ h =
    Limits.prod.lift (𝟙 (Limits.prod A WithNNO.N)) h ≫ g) : h = Rec_Par_with_NNO f g := by
    apply MonoidalClosed.curry_injective
    exact (h_eq_expon_transp f g h hyp_zero hyp_succ).trans (Rec_Par_eq_expon_transp f g).symm
------------------------------------------------------------------------------------------------

--Section 9: Definition and properties of the sum

--Definition of the sum in the context of NNO

noncomputable def NNO_sum {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    Limits.prod (WithNNO.N (C := C)) (WithNNO.N) ⟶ WithNNO.N :=
    Rec_Par_with_NNO (𝟙 (WithNNO.N)) (Limits.prod.snd ≫ (NNO C).s)

--Proof that the sum is associative

--Technical result

theorem aux1_NNO_sum_assoc {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] (A : C) (f : A ⟶ WithNNO.N) :
    (prod.map (𝟙 (WithNNO.N ⨯ WithNNO.N)) f ≫
    (prod.associator WithNNO.N WithNNO.N WithNNO.N).hom) =
      (Limits.prod.associator (WithNNO.N) (WithNNO.N) (A)).hom ≫
      Limits.prod.map (𝟙 WithNNO.N) (Limits.prod.map (𝟙 WithNNO.N) f) := by
        apply Limits.prod.hom_ext
        · rw[Category.assoc, Limits.prod.associator_hom, Limits.prod.associator_hom,
          Limits.prod.lift_fst, ← Category.assoc, Limits.prod.map_fst,
          Category.comp_id, Category.assoc, Limits.prod.map_fst,
          Category.comp_id, Limits.prod.lift_fst]
        · rw[Category.assoc, Limits.prod.associator_hom,
          Limits.prod.associator_hom, Limits.prod.lift_snd,
          Category.assoc, Limits.prod.map_snd, ← Category.assoc, Limits.prod.lift_snd]
          apply Limits.prod.hom_ext
          · rw[Category.assoc, Category.assoc, Limits.prod.lift_fst, Limits.prod.map_fst,
            Category.comp_id, ← Category.assoc, Limits.prod.lift_fst,
             Limits.prod.map_fst, Category.comp_id]
          · rw[Category.assoc, Category.assoc, Limits.prod.lift_snd, Limits.prod.map_snd,
            Limits.prod.map_snd, ← Category.assoc, Limits.prod.lift_snd]

--Proof that the first function satisfies the recursion property

theorem NNO_sum_assoc_part1 {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    Limits.prod.map NNO_sum (𝟙 (WithNNO.N (C := C)) ) ≫ NNO_sum =
    Rec_Par_with_NNO (NNO_sum) (Limits.prod.snd ≫ (NNO C).s) := by
      apply Rec_Par_with_NNO_unique
      · rw[Limits.prod.map_map_assoc, Category.id_comp, Category.comp_id,
        ← Category.comp_id (NNO_sum), ← Category.id_comp ((NNO C).zero),
        ← Limits.prod.map_map_assoc, Category.comp_id]
        rw[NNO_sum, Rec_Par_with_NNO_fac_zero, ← Category.assoc,
        Limits.prod.map_fst, Category.comp_id]
      · conv_lhs => rw[Limits.prod.map_map_assoc, Category.id_comp, Category.comp_id,
        ← Category.comp_id (NNO_sum), ← Category.id_comp ((NNO C).s),
        ← Limits.prod.map_map_assoc, Category.comp_id, NNO_sum, Rec_Par_with_NNO_fac_succ,
        ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
        (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))),
        Limits.prod.lift_snd]
        conv_rhs => rw[← Category.assoc (prod.lift (𝟙 ((WithNNO.N ⨯ WithNNO.N) ⨯ WithNNO.N))
        (prod.map NNO_sum (𝟙 WithNNO.N) ≫ NNO_sum)),
        Limits.prod.lift_snd, NNO_sum]
        simp only [Category.assoc]

--Proof that the second function satisfies the recursion property

theorem NNO_sum_assoc_part2 {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    (Limits.prod.associator WithNNO.N WithNNO.N WithNNO.N).hom ≫
    Limits.prod.map (𝟙 WithNNO.N) NNO_sum ≫ NNO_sum =
    Rec_Par_with_NNO (NNO_sum) (Limits.prod.snd ≫ (NNO C).s) := by
    apply Rec_Par_with_NNO_unique
    · rw[← Category.assoc, aux1_NNO_sum_assoc, Category.assoc,
      ← Category.assoc (prod.map (𝟙 WithNNO.N) (prod.map (𝟙 WithNNO.N) (NNO C).zero)),
      Limits.prod.map_map, NNO_sum, Rec_Par_with_NNO_fac_zero,
      Limits.prod.associator_hom, ← Category.assoc, Limits.prod.lift_map,
      Category.comp_id, Category.comp_id, Category.comp_id]
      have : (prod.lift (Limits.prod.fst ≫ Limits.prod.fst)
      (prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd ≫ Limits.prod.fst)) =
      (Limits.prod.fst : Limits.prod (Limits.prod WithNNO.N WithNNO.N) (⊤_ C) ⟶
      Limits.prod WithNNO.N WithNNO.N):= by
        apply Limits.prod.hom_ext
        · rw[Limits.prod.lift_fst]
        · rw[Limits.prod.lift_snd, Limits.prod.lift_fst]
      rw[this]
    · rw[← Category.assoc, aux1_NNO_sum_assoc, Category.assoc,
      ← Category.assoc (prod.map (𝟙 WithNNO.N) (prod.map (𝟙 WithNNO.N) (NNO C).s)),
      Limits.prod.map_map, NNO_sum, Rec_Par_with_NNO_fac_succ,
      ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
      (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))), Limits.prod.lift_snd]
      conv_rhs => rw[← Category.assoc, Limits.prod.lift_snd]
      rw[Category.assoc, ← Limits.prod.map_map, Category.assoc, Rec_Par_with_NNO_fac_succ,
      ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
      (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))), Limits.prod.lift_snd]
      simp only [Category.assoc]

--Main result

theorem NNO_sum_assoc {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    Limits.prod.map NNO_sum (𝟙 (WithNNO.N (C := C)) ) ≫ NNO_sum =
    (Limits.prod.associator WithNNO.N WithNNO.N WithNNO.N).hom ≫
    Limits.prod.map (𝟙 WithNNO.N) NNO_sum ≫ NNO_sum := by
    exact NNO_sum_assoc_part1.trans NNO_sum_assoc_part2.symm

--Proof that the sum is commutative

/- For the zero part of the main theorem, proof that the first function
satisfies the recursion property
-/

theorem NNO_sum_comm_fac_zero1 {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    prod.map (NNO C).zero (𝟙 WithNNO.N) ≫ NNO_sum =
    Rec_Par_with_NNO (NNO C).zero (Limits.prod.snd ≫ (NNO C).s) := by
    apply Rec_Par_with_NNO_unique
    · rw[← Category.assoc, Limits.prod.map_map, Category.comp_id, Category.id_comp]
      have : prod.map (NNO C).zero (NNO C).zero =
      Limits.prod.map (NNO C).zero (𝟙 (⊤_ C)) ≫ Limits.prod.map (𝟙 WithNNO.N) (NNO C).zero := by
        simp only [Limits.prod.map_map, Category.comp_id, Category.id_comp]
      rw[this, Category.assoc, NNO_sum, Rec_Par_with_NNO_fac_zero,
      Category.comp_id, Limits.prod.map_fst]
    · rw[← Category.assoc, Limits.prod.map_map, Category.comp_id, Category.id_comp,
      ← Category.comp_id (NNO C).zero, ← Category.id_comp (NNO C).s, ← Limits.prod.map_map,
      Category.assoc, NNO_sum, Rec_Par_with_NNO_fac_succ,
      ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
      (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))),
      Limits.prod.lift_snd, Category.comp_id, Category.id_comp,
      ← Category.assoc (prod.lift (𝟙 ((⊤_ C) ⨯ WithNNO.N)) (prod.map (NNO C).zero (𝟙 WithNNO.N) ≫
      Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))),
      Limits.prod.lift_snd, Category.assoc]

/- For the zero part of the main theorem, proof that the second function
satisfies the recursion property
-/

theorem NNO_sum_comm_fac_zero2 {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    (Limits.prod.braiding (WithNNO.N) (⊤_ C)).inv
    ≫ prod.fst = Rec_Par_with_NNO (NNO C).zero (Limits.prod.snd ≫ (NNO C).s) := by
    rw[Limits.prod.braiding_inv, Limits.prod.lift_fst]
    apply Rec_Par_with_NNO_unique
    · rw[Limits.prod.map_snd,
      Limits.terminal.hom_ext (Limits.prod.snd) (Limits.prod.fst)]
    · rw[← Category.assoc, Limits.prod.map_snd, Limits.prod.lift_snd]

/- For the succ part of the main theorem, proof that the first function
satisfies the recursion property
-/

theorem NNO_sum_comm_fac_succ1 {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    prod.map (NNO C).s (𝟙 WithNNO.N) ≫ NNO_sum =
    Rec_Par_with_NNO (NNO C).s (Limits.prod.snd ≫ (NNO C).s) := by
      apply Rec_Par_with_NNO_unique
      · rw[← Category.assoc, Limits.prod.map_map, Category.comp_id, Category.id_comp,
        ← Category.comp_id (NNO C).s, ← Category.id_comp (NNO C).zero,
        ← Limits.prod.map_map, Category.assoc, NNO_sum, Rec_Par_with_NNO_fac_zero,
        Category.comp_id, Limits.prod.map_fst, Category.comp_id]
      · conv_lhs => rw[← Category.assoc, Limits.prod.map_map, Category.comp_id, Category.id_comp]
        have : prod.map (NNO C).s (NNO C).s =
        prod.map (NNO C).s (𝟙 WithNNO.N) ≫ prod.map (𝟙 WithNNO.N) (NNO C).s := by
          simp only [Limits.prod.map_map, Category.comp_id, Category.id_comp]
        rw[this, Category.assoc, NNO_sum, Rec_Par_with_NNO_fac_succ,
        ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
        (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))),
        Limits.prod.lift_snd,
        ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
        (prod.map (NNO C).s (𝟙 WithNNO.N) ≫ Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))),
        Limits.prod.lift_snd]
        simp only [Category.assoc]

/- For the succ part of the main theorem, proof that the second function
satisfies the recursion property
-/

theorem NNO_sum_comm_fac_succ2 {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] : NNO_sum ≫ (NNO C).s =
    Rec_Par_with_NNO (NNO C).s (Limits.prod.snd ≫ (NNO C).s) := by
    apply Rec_Par_with_NNO_unique
    · rw[← Category.assoc, NNO_sum, Rec_Par_with_NNO_fac_zero, Category.comp_id]
    · rw[← Category.assoc, NNO_sum, Rec_Par_with_NNO_fac_succ,
      ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
      (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s))), Limits.prod.lift_snd,
      ← Category.assoc (prod.lift (𝟙 (WithNNO.N ⨯ WithNNO.N))
      (Rec_Par_with_NNO (𝟙 WithNNO.N) (prod.snd ≫ (NNO C).s) ≫ (NNO C).s)), Limits.prod.lift_snd]

--Main result

theorem NNO_sum_comm {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] :
    (Limits.prod.braiding (WithNNO.N) (WithNNO.N)).hom ≫ NNO_sum (C := C) = NNO_sum := by
    conv_rhs => rw[NNO_sum]
    apply Rec_Par_with_NNO_unique
    · rw[← Category.assoc, Limits.braid_natural, Category.comp_id,
      ← Category.id_comp (prod.fst), ← (Limits.prod.braiding WithNNO.N (⊤_ C)).hom_inv_id,
      Category.assoc, Category.assoc]
      have : prod.map (NNO C).zero (𝟙 WithNNO.N) ≫ NNO_sum =
      (Limits.prod.braiding (WithNNO.N) (⊤_ C)).inv ≫ prod.fst := by
        exact NNO_sum_comm_fac_zero1.trans NNO_sum_comm_fac_zero2.symm
      rw[this]
    · rw[← Category.assoc, Limits.braid_natural, ← Category.assoc, Limits.prod.lift_snd,
      Category.assoc, Category.assoc]
      have : prod.map (NNO C).s (𝟙 WithNNO.N) ≫ NNO_sum = NNO_sum ≫ (NNO C).s := by
        exact NNO_sum_comm_fac_succ1.trans NNO_sum_comm_fac_succ2.symm
      rw[this]

--------------------------------------------------------------------------------------------

--Section 10: Peano's third axiom

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

/-Addition: proof that, in a Cartesian closed category, if Peano's fourth axiom fails
then there is at most one morphism between any two objects of the category
-/

theorem not_fourth_axiom_uniq_mor {C : Type u} [Category C] [HasTerminal C]
    [WithNNO C] [HasBinaryProducts C] [MonoidalClosed C] {x : ⊤_ C ⟶ WithNNO.N}
    (h1 : x ≫ (NNO C).s = (NNO C).zero) {A B : C}
    (f : A ⟶ B) (g : A ⟶ B) : f = g := by
    have T_NNO : IsNNO (⊤_ C) :=
    IsNNO.ofIso (WithNNO.isNNO) (not_fourth_axiom_Nterm h1)
    sorry



------------------------------------------------------------------------------------------------

--Section 11: Proof that Finset does not have an NNO

--Proof that Fin 2 (= {0,1}) has an isomorphic equivalent in Finset

omit [Inhabited α] in
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

--Section 12: NNO as initial algebra

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

----------------------------------------------------------------------------------------------
