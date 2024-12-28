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
      fmap (g ∘ h) = (fmap g ∘ fmap h)}.

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
        rewrite functors_preserve_identities.
        rewrite functors_preserve_identities. 
        reflexivity.
    -   intros.
        rewrite functors_preserve_composition.
        rewrite functors_preserve_composition.
        reflexivity.
Defined.

Definition ax : 
  forall (C D : Category) (F G : Functor C D) (H : @fobj C D F = @fobj C D G)
    (f : forall a b : C, C a b -> D (G a) (G b)), 
    forall a b : C, C a b -> D (F a) (F b).
Proof.
  intros.
  rewrite H.
  exact (f a b X).
Defined.




(* functional equality *)

Lemma proof_irrelevance_in_functors : forall (C D : Category) (F G : Functor C D)
  (H : @fobj C D F = @fobj C D G) 
  (H1 : @fmap C D F = ax C D F G H (@fmap C D G)),
  F = G.
Proof.
  intros C D F G Heq1 Heq2.
  destruct F, G.
  unfold ax in *.
  simpl in *.
  subst.
  f_equal; apply proof_irrelevance.
Qed.

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

(* TODO : 
  (1) prove Cat with lemma ax 
  (2) try to obtain functor equality using directly eq_rect_r*)
Check (forall (C D : Category) (F G : Functor C D) (a b : C) (f : C a b) (H : @fobj C D F = @fobj C D G), 
  eq_rect_r (fun o : C -> D => D (o a) (o b)) (@fmap C D G a b f) H = 
    @fmap C D F a b f).
