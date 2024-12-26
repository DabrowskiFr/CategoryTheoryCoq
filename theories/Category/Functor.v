From Coq.Logic Require Import ProofIrrelevance.

From Categories.Category Require Import Category.

(** ** Functor *)
(** 
  A functor [F : Functor C D] is a mapping between the categories [C] and [D]. 
  - each object [a : C] is mapped to an object [fobj F a : D] and 
  - each morphism [f : C a b] is mapped to  a morphism [fmap F f : C (F a) (F b)] 
  This mapping must preserve identities and composition.
  The object mapping [fobj F a] is denoted by [F a].
  *)

Class Functor (C : Category) (D : Category) : Type := {
  fobj : C -> D;
  fmap {a b : C} : C a b -> D (fobj a) (fobj b);
  functors_preserve_identities {a : C} : 
    fmap (idty a) = idty (fobj a);
  functors_preserve_composition {a b c : C} : 
      forall (g : C b c) (h : C a b),
        (fmap g ∘ fmap h) = fmap (g ∘ h) }.

Arguments fmap { _ _ } Functor { _ _ }.

Coercion fobj : Functor >-> Funclass.

(** ** Category of small categories *)
(** We can form the category [Cat] whose objects are small categories  
    and morphisms are functors. *)

#[refine] Instance FunctorId (C : Category) : Functor C C := {
    fobj x := x;
    fmap _ _ f := f }.
Proof.
  - reflexivity.
  - reflexivity.
Defined.

#[refine] Instance FunctorComp {C D E : Category}
  (G : Functor D E) (F : Functor C D)  : Functor C E := {
    fobj x := G (F x);
    fmap _ _ f := fmap G (fmap F f) }.
Proof.
    -   intros.
        do 2 rewrite functors_preserve_identities; reflexivity.
    -   intros.
        do 2 rewrite functors_preserve_composition; reflexivity.
Defined.

#[refine] Instance Cat : Category := {
    obj := Category;
    hom := Functor;
    idty := FunctorId;
    compose _ _ _ := FunctorComp }.
Proof.
    - unfold FunctorId, FunctorComp.
      destruct f.
      f_equal; apply proof_irrelevance.
    - unfold FunctorId, FunctorComp.
      destruct f.
      f_equal; apply proof_irrelevance.
    - unfold FunctorComp; simpl.
      destruct f, g, h.
      f_equal; apply proof_irrelevance.
Defined.

