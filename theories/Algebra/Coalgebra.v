From Categories.Category Require Import Category Functor.

Section CoAlgebra.

    Variable C : Category.

    Class CoAlgebra (F : Functor C C) : Type :=
    {
        carrier : C;
        operation : C carrier (F carrier)
    }.

    Arguments carrier {F} _.
    Arguments operation {F} _.

    Record CoAlgebraMorphism {F : Functor C C} 
        (A B : CoAlgebra F) : Type := {
        f : C (carrier A) (carrier B);
        H_f : (fmap F f) ∘ (operation A) = (operation B) ∘ f }.

End CoAlgebra.

Arguments CoAlgebra {C} F.
Arguments carrier {C F} _.
Arguments operation {C F} _.
Arguments CoAlgebraMorphism {C F} _ _.
Coercion f : CoAlgebraMorphism >-> hom.


(* morphisms are simply morphism of the category *)

Definition aid {C : Category} (F : Functor C C) 
    (a : CoAlgebra F): CoAlgebraMorphism a a.
    refine ({|f := idty _ |}).
Proof.
    rewrite functors_preserve_identities.
    rewrite compose_left_idty.
    rewrite compose_right_idty.
    reflexivity.
Defined.

Definition acompose {C : Category} (F : Functor C C) 
    (a b c : CoAlgebra F) : 
        CoAlgebraMorphism b c -> CoAlgebraMorphism a b -> CoAlgebraMorphism a c.
    intros.
        refine ({|f:=compose X X0 |}).
        rewrite <- functors_preserve_composition.
        destruct X, X0.
        simpl.
        rewrite compose_assoc.
        rewrite <- H_f0.
        rewrite <- compose_assoc.
        rewrite H_f1.
        rewrite compose_assoc.
        reflexivity.
    Defined.

Lemma acat_a : forall (C : Category) (F : Functor C C) (a b : CoAlgebra F)
(f : CoAlgebraMorphism a b),
acompose F a a b f (aid F a) = f.
Admitted.

Lemma acat_b : forall (C : Category) (F : Functor C C) (a b : CoAlgebra F)
(f : CoAlgebraMorphism a b),
acompose F a b b (aid F b) f = f.
Admitted.

Lemma acat_c : forall (C : Category) (F : Functor C C) (a b c d : CoAlgebra F)
(f : CoAlgebraMorphism a b)
(g : CoAlgebraMorphism b c)
(h : CoAlgebraMorphism c d),
acompose F a c d h (acompose F a b c g f) =
acompose F a b d (acompose F b c d h g) f.
Admitted.


#[refine] Instance CoAlgebraCat {C : Category} (F : Functor C C) : Category := 
{
    obj := CoAlgebra F;
    hom := CoAlgebraMorphism;
    idty := aid F;
    compose := acompose F
}.

Proof.
- apply acat_a.
- apply acat_b.
- apply acat_c.
Defined. 