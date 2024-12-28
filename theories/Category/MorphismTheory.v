From Categories.Category Require Import Category.

(** ** Monomorphisms, Epimorphisms and Isomorphisms *)

(** A monomorphism (or monic) is a left-cancellative morphism.
    Monomorphisms are the categorical generalization of injective functions *)

    Definition monomorphism {C : Category} {a b : C} (f : C a b) :=
        forall c (g1 g2 : C c a), f ∘ g1 = f ∘ g2 -> g1 = g2.
    
    (** An epimorphism (or epic) is a right-cancellative morphism.
        Epimorphisms are the categorical generalization of surjective functions 
        An epic is the categorical dual of a monic *)
    
    Definition epimorphism {C : Category} {a b : C} (f : C a b) :=
        forall c (g1 g2 : C b c), g1 ∘ f = g2 ∘ f  -> g1 = g2.
        
    
    Definition isomorphism {C : Category} {a b : C} (f : C a b) :=
        exists g, g ∘ f = idty a /\ f ∘ g = idty b.
    
    Definition isomorphic {C : Category} (a b : C) : Type :=  
            exists (f : C a b), isomorphism f.
        
    (* A retraction is the left inverse of a morphism *)
    Definition retraction {C : Category} {a b : C} (f : C a b) (g : C b a) : Prop :=
        g ∘ f = idty a.
    
    (* A section is the right inverse of a morphism *)
    Definition section {C : Category} {a b : C} (f : C a b) (g : C b a) : Prop :=
        f ∘ g = idty b.
    
        
    Lemma section_monic : forall (C : Category) (a b : C) (f : C a b) (g : C b a),
        section f g -> monomorphism g.
    Proof.
        unfold section, monomorphism.
        intros C a b f g Ha c g1 g2 Hb.
        replace g2 with (f ∘ (g ∘ g2)) by
            now rewrite <- compose_right_idty, <- Ha, <- compose_assoc.
        rewrite <- Hb.
        now replace (f ∘ (g ∘ g1)) with g1 by
            now rewrite compose_assoc, Ha, compose_right_idty.
    Qed.
    
    Lemma retractation_epic : forall (C : Category) (a b : C) (f : C a b) (g : C b a),
        retraction f g -> epimorphism g.
    Proof.
        unfold retraction, epimorphism.
        intros C a b f g Ha c g1 g2 Hb.
        replace g2 with ((g2 ∘ g) ∘ f) by
            now rewrite <- compose_left_idty, <- Ha, compose_assoc.
        rewrite <- Hb.
        now replace ((g1 ∘ g) ∘ f) with g1 by 
            now rewrite <- compose_assoc, Ha, compose_left_idty. 
    Qed.
    
    Lemma isomorphism_monic : forall (C : Category) (a b : C) (f : C a b),
        isomorphism f -> monomorphism f.
    Proof.
        unfold isomorphism, monomorphism.
        intros C a b f [f' [H_left_inv _ ]] c g1 g2 H_eq.
        replace g1 with (f' ∘ (f ∘ g1)) by
            now rewrite compose_assoc, H_left_inv, compose_right_idty.
        replace (f ∘ g1) with (f ∘ g2) by now rewrite H_eq.
        now replace (f' ∘ (f ∘ g2)) with g2 by 
            now rewrite compose_assoc, H_left_inv, compose_right_idty.
    Qed.
    
    Lemma isomorphism_epic : forall (C : Category) (a b : C) (f : C a b),
        isomorphism f -> epimorphism f.
    Proof.
        unfold isomorphism, epimorphism.
        intros C a b f [f' [_ H_right_inv]] c g1 g2 H_eq.
        replace g1 with (g1 ∘ f ∘ f') by 
           now rewrite <- compose_assoc, H_right_inv, compose_left_idty.
        replace (g1 ∘ f) with (g2 ∘ f) by now rewrite <- H_eq.
        now replace (g2 ∘ f ∘ f') with g2 by 
            now rewrite <- compose_assoc, H_right_inv, compose_left_idty.
    Qed.
    
    Lemma retractation_mono_iso : forall (C : Category) (a b : C) (f : C a b) (g : C b a),
        retraction f g -> monomorphism g -> isomorphism g.
    Proof.
        unfold retraction, monomorphism, isomorphism.
        intros C a b f g H_left_inv H_mono.
        exists f; split; [ | assumption].
        assert (g ∘ (f ∘ g) = g ∘ idty b).
        {
            replace (g ∘ (f ∘ g)) with (idty a ∘ g) by 
                now rewrite compose_assoc, H_left_inv.
            now rewrite compose_left_idty, compose_right_idty.
        }
        now apply H_mono.
    Qed.
    
    Lemma section_epi_iso : forall (C : Category) (a b : C) (f : C a b) (g : C b a),
        section f g -> epimorphism g -> isomorphism g.
    Proof.
        unfold section, epimorphism, isomorphism.
        intros C a b f g H_right_inv H_epi.
        exists f; split; [assumption | ].
        assert (g ∘ f ∘ g = idty a ∘ g).
        {
            replace (g ∘ f ∘ g) with (g ∘ idty b) by
                now rewrite <- compose_assoc, H_right_inv.
            now rewrite compose_left_idty, compose_right_idty.            
        }
        now apply H_epi.
    Qed.