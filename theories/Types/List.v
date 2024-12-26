From Coq.Logic Require Import FunctionalExtensionality.
From Coq.Logic Require Import ProofIrrelevance.
From Coq.Setoids Require Import Setoid.

From Categories.Category Require Import Category Functor.
From Categories.Algebra Require Import Algebra.
From Categories.Instances Require Import CategoryType.
From Categories.Types Require Import Data.

(* We define the endofunctor [Fₙ] over the category of types as 
    F X = 1 + X *)

Instance Fₗ (A : Type): Functor Typ Typ := 
    (FunctorSum unit : Cat _ _) ∘ (FunctorProduct A).

(* We define the Fₙ-algebra [nat_algebra] and prove that it is an
    initial Fₙ-algebra, i.e. it is an initial object for the category of Fₙ-algebra *)

Instance list_Algebra (A : Type) : Algebra (Fₗ A)  := 
{
    carrier := list A;
    operation p := match p with inl _ => nil | inr (a,n) => cons a n end
}.

Definition list_to_algebra (A : Type) (B : Algebra (Fₗ A)) : Typ (carrier (list_Algebra A)) (carrier B) :=
    fix f n := match n with nil => operation B (inl tt) 
        | cons a n => operation B (inr (a,f n)) end.    
  
Definition list_to_algebra_m (A : Type) (B : Algebra (Fₗ A)) : AlgebraMorphism (list_Algebra A) B.
    refine ({|
        f := list_to_algebra A B
    |}).
Proof.
    apply functional_extensionality; intro x.
    destruct x; simpl.
    -   destruct u; reflexivity.
    -   destruct f; reflexivity.
Defined.

#[refine] Instance initial_ (A : Type): initial (AlgebraCat (Fₗ A)) (list_Algebra A) := 
{
    umorph := list_to_algebra_m A
}.
Proof.
    intros b [f H_f].
    assert (list_to_algebra A b = f).
    {
        apply functional_extensionality.
        intro x.
        induction x.
        -   generalize (equal_f H_f (inl tt)); intro; simpl in *.
            assumption.
        -   generalize (equal_f H_f (inr (a,x))); intro; simpl in *.
            congruence.
    }
    subst.
    unfold list_to_algebra_m; simpl.
    f_equal.
    apply proof_irrelevance.
Defined.

(* The functor defines the structure of the type, if the type is parameterized. Generalizing
    gives rise to another functor *)