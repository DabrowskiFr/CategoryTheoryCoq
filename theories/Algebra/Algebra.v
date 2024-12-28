From Categories.Category Require Import Category MorphismTheory Functor.

(** ** Algebra *)
(** Given a endofunctor F of a category C, a F-algebra [Algebra F]
    is given by an object [carrier : C] and a morphism 
    [operation : C carrier carrier]
*)

Section Algebra.

    Variable C : Category.

    Class Algebra (F : Functor C C) : Type := {
        carrier : C; 
        operation : C (F carrier) carrier
    }.

    Arguments carrier {F} _.
    Arguments operation {F} _.

    Record AlgebraMorphism {F : Functor C C} (A B : Algebra F) : Type := 
    {
        f : C (carrier A) (carrier B);
        H_f : (operation B) ∘ (fmap F f) = f ∘ (operation A)
}.

End Algebra.

Arguments Algebra {C} F.
Arguments carrier {C F} _.
Arguments operation {C F} _.
Arguments AlgebraMorphism {C F} _ _.
(* Coercion f : AlgebraMorphism >-> hom. *)

(* morphisms are simply morphism of the category *)

Definition aid {C : Category} (F : Functor C C) 
    (a : Algebra F): AlgebraMorphism a a.
    refine ({|f := idty _ |}).
Proof.
    rewrite functors_preserve_identities.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
Defined.

Definition acompose {C : Category} (F : Functor C C) 
    (a b c : Algebra F) : 
        AlgebraMorphism b c -> AlgebraMorphism a b -> AlgebraMorphism a c.
        intros g f.     
        destruct g as [g Hg].
        destruct f as [f Hf].
        refine ({|f := g ∘ f |}).
        rewrite functors_preserve_composition.
        simpl.
        rewrite compose_assoc.
        rewrite Hg.
        rewrite <- compose_assoc.
        rewrite Hf.
        rewrite compose_assoc.
        reflexivity.
    Defined.

Lemma acat_a : forall (C : Category) (F : Functor C C) (a b : Algebra F)
(f : AlgebraMorphism a b),
acompose F a a b f (aid F a) = f.
Admitted.

Lemma acat_b : forall (C : Category) (F : Functor C C) (a b : Algebra F)
(f : AlgebraMorphism a b),
acompose F a b b (aid F b) f = f.
Admitted.

Lemma acat_c : forall (C : Category) (F : Functor C C) (a b c d : Algebra F)
(f : AlgebraMorphism a b)
(g : AlgebraMorphism b c)
(h : AlgebraMorphism c d),
acompose F a c d h (acompose F a b c g f) =
acompose F a b d (acompose F b c d h g) f.
Admitted.


#[refine] Instance AlgebraCat {C : Category} (F : Functor C C) : Category := 
{
    obj := Algebra F;
    hom := AlgebraMorphism;
    idty := aid F;
    compose := acompose F
}.

Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined.

(* Definition lift_obj {C : Category} 
    (F G : Functor C C) : AlgebraCat F -> AlgebraCat F := 
        fun A => {| 
            carrier := F (carrier A); 
            operation := fmap G (operation A)|}. *)


(* Definition lift_obj {C : Category} 
    (F G : Functor C C) : AlgebraCat F -> AlgebraCat F := 
        fun A => {| 
            carrier := G (carrier A); 
            operation := fmap G (operation A)|}. *)


(* generalize to other functors ??? *)
Definition lift_obj {C : Category} 
    (F : Functor C C) : AlgebraCat F -> AlgebraCat F := 
        fun A => {| 
            carrier := F (carrier A); 
            operation := fmap F (operation A)|}.

Definition lift_morph {C : Category} (F : Functor C C)
    (A B : AlgebraCat F) : 
        AlgebraCat F A B ->
            AlgebraCat F (lift_obj F A) (lift_obj F B).
    intro.
    destruct X.
    refine ({| f := (fmap F f0 : C (carrier (lift_obj F A)) (carrier (lift_obj F B)))|}).
    simpl in *.
    rewrite <- functors_preserve_composition.
    rewrite H_f0.
    rewrite <- functors_preserve_composition.
    reflexivity.
Defined.

Lemma initial_fix :
    forall (C : Category) (F : Functor C C) (A : AlgebraCat F),
        initial (AlgebraCat F) A -> isomorphic (F (carrier A)) (carrier A).
Proof.
    intros C F A Ha.
    set (B := {| carrier := F (carrier A); operation := fmap F (operation A)|}).
    assert (AlgebraCat F A B) as f.
    {
        exact (umorph B).
    }
    set (g := {|f := operation A : C (carrier B) (carrier A); H_f := eq_refl|} : AlgebraCat F B A).
    assert (g ∘ f = idty A).
    {
        destruct Ha.
        rewrite umorph_prop.
        exact (umorph_prop _ ((g : AlgebraCat F B A) ∘ f)).
    }
    assert (f ∘ g = idty _).
Abort.


Lemma a : forall (C : Category) (F : Functor C C) (A : AlgebraCat F),
    fmap F (idty (carrier A)) = idty (carrier (lift_obj F A)).
Proof.
    intros.
    simpl.
    rewrite functors_preserve_identities.
    reflexivity.
Qed.

#[refine] Instance FunctorAlgebra {C : Category} (F : Functor C C) : 
    Functor (AlgebraCat F) (AlgebraCat F) := 
    {
        fobj := lift_obj F;
        fmap := lift_morph F
    }.
Proof.
Admitted.

Definition mkmorphism0 (C : Category) 
    (F : Functor C C) (A : Algebra F) : 
    initial (AlgebraCat F) A -> C (carrier A) (F (carrier A)).
Proof.
    intro H.
    destruct H.
    generalize (umorph (lift_obj F A)); intro.
    destruct X as [ f _ ]; simpl in *.
    exact f.
Defined.


Definition mkmorphism1 (C : Category) 
    (F : Functor C C) (A : Algebra F) : 
    initial (AlgebraCat F) A -> AlgebraCat F A A.
Proof.
Admitted.

(* #[refine] Instance mkmorphism1 (C : Category) 
    (F : Functor C C) (A : Algebra F) : 
    Functor C (AlgebraCat F) := 
    {
    }.
    intro a.
    exact A.
Admitted.
 *)



(* Check carrier.


    Arguments carrier {C F}.
    Arguments operation {C F}.


Record AlgebraMorphism {C : Category} {F : Functor C C}
    (A B : Algebra F) : Type := 
    {
        f : C (carrier A) (carrier B);
        H_f : (operation B) ∘ (fmap F f) = f ∘ (operation A)
}.
 *)
