Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_IDEMP_term_abbrevs.
Require Import RESTRICTION_FIXPOINT_spec.
Require Import RESTRICTION_IN_EXTENSIONAL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4390548 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4387232 A B s). Qed.
Lemma lem4390549 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4390550 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4390549 A B s) (@lem4390548 A B s)). Qed.
Lemma lem4390551 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4390550 A B s f). Qed.
Lemma lem4390552 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term2 A B s f) = (term3 A B f s).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4390553 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (EQ_MP (@lem4390552 A B f s) (@lem4390551 A B s f)). Qed.
Lemma lem4390554 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = ((term3 A B f s) = True).
Proof. exact (@lem7 (term3 A B f s)). Qed.
Lemma lem4390556 {A B : Type'} (s : A -> Prop) : term4 A B s.
Proof. exact (@lem4389660 A B s). Qed.
Lemma lem4390557 {A B : Type'} (s : A -> Prop) : (term4 A B s) = (term5 A B s).
Proof. exact (eq_refl (term4 A B s)). Qed.
Lemma lem4390558 {A B : Type'} (s : A -> Prop) : term5 A B s.
Proof. exact (EQ_MP (@lem4390557 A B s) (@lem4390556 A B s)). Qed.
Lemma lem4390559 {A B : Type'} (s : A -> Prop) (f : A -> B) : term6 A B s f.
Proof. exact (@lem4390558 A B s f). Qed.
Lemma lem4390560 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term6 A B s f) = (((@RESTRICTION A B s f) = f) = (term7 A B f s)).
Proof. exact (eq_refl (term6 A B s f)). Qed.
Lemma lem4390571 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((@RESTRICTION A B s f) = f) = (term7 A B f s).
Proof. exact (EQ_MP (@lem4390560 A B f s) (@lem4390559 A B s f)). Qed.
Lemma lem4390572 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((@RESTRICTION A B s f) = f) = (term7 A B f s).
Proof. exact (@lem4390571 A B f s). Qed.
Lemma lem4390573 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term8 A B s f) = (@RESTRICTION A B s f)) = (term3 A B f s).
Proof. exact (@lem4390572 A B (@RESTRICTION A B s f) s). Qed.
Lemma lem4390575 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = True.
Proof. exact (EQ_MP (@lem4390554 A B f s) (@lem4390553 A B f s)). Qed.
Lemma lem4390576 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = True.
Proof. exact (@lem4390575 A B f s). Qed.
Lemma lem4390577 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term8 A B s f) = (@RESTRICTION A B s f)) = True.
Proof. exact (TRANS (@lem4390573 A B f s) (@lem4390576 A B f s)). Qed.
Lemma lem4390578 {A B : Type'} (s : A -> Prop) : (term9 A B s) = (term10 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem4390577 A B s f)). Qed.
Lemma lem4390579 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4390580 {A B : Type'} (s : A -> Prop) : (term11 A B s) = (term12 A B).
Proof. exact (MK_COMB (@lem4390579 A B) (@lem4390578 A B s)). Qed.
Lemma lem4390582 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4390583 {A B : Type'} (t : Prop) : (term14 A B t) = t.
Proof. exact (@lem4390582 (A -> B) t). Qed.
Lemma lem4390584 {A B : Type'} : (term12 A B) = True.
Proof. exact (@lem4390583 A B True). Qed.
Lemma lem4390585 {A B : Type'} (s : A -> Prop) : (term11 A B s) = True.
Proof. exact (TRANS (@lem4390580 A B s) (@lem4390584 A B)). Qed.
Lemma lem4390586 {A B : Type'} : (term15 A B) = (term16 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4390585 A B s)). Qed.
Lemma lem4390587 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4390588 {A B : Type'} : (term17 A B) = (term18 A).
Proof. exact (MK_COMB (@lem4390587 A) (@lem4390586 A B)). Qed.
Lemma lem4390590 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4390591 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (@lem4390590 (A -> Prop) t). Qed.
Lemma lem4390592 {A : Type'} : (term18 A) = True.
Proof. exact (@lem4390591 A True). Qed.
Lemma lem4390593 {A B : Type'} : (term17 A B) = True.
Proof. exact (TRANS (@lem4390588 A B) (@lem4390592 A)). Qed.
Lemma lem4390594 {A B : Type'} : True = (term17 A B).
Proof. exact (SYM (@lem4390593 A B)). Qed.
Lemma lem4390595 {A B : Type'} : term17 A B.
Proof. exact (EQ_MP (@lem4390594 A B) (@lem0)). Qed.
