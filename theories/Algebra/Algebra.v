From Categories.Category Require Import Category Functor.

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
Coercion f : AlgebraMorphism >-> hom.

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
    intros.
        refine ({|f:=compose X X0 |}).
        rewrite <- functors_preserve_composition.
        destruct X, X0.
        simpl.
        rewrite compose_assoc.
        rewrite H_f0.
        rewrite <- compose_assoc.
        rewrite H_f1.
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

(* Lemma initial_fix :
    forall (C : Category) (F : Functor C C) (A : AlgebraCat F),
    initial (AlgebraCat F) A -> F (carrier A) = (carrier A).
Proof.
    intros.
    destruct X.
    generalize (umorph_prop A (idty A)); intro.
Admitted. *)

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
