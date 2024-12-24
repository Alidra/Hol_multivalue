Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_EMPTY_term_abbrevs.
Require Import FINITE_EMPTY_spec.
Require Import INTERSECTION_OF_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4876661 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4876663 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4851880 A P). Qed.
Lemma lem4876664 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4876665 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4876664 A P) (@lem4876663 A P)). Qed.
Lemma lem4876666 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4876665 A P Q). Qed.
Lemma lem4876667 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = (term3 A P Q).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4876668 {A : Type'} (P : type180 A) (Q : type686 A) : term3 A P Q.
Proof. exact (EQ_MP (@lem4876667 A P Q) (@lem4876666 A P Q)). Qed.
Lemma lem4876669 {A : Type'} (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : P (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem4876670 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : @INTERSECTION_OF A P Q (@UNIV A).
Proof. exact (@lem4876668 A P Q (@lem4876669 A P h1)). Qed.
Lemma lem4876671 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q (@UNIV A)) = ((@INTERSECTION_OF A P Q (@UNIV A)) = True).
Proof. exact (@lem7 (@INTERSECTION_OF A P Q (@UNIV A))). Qed.
Lemma lem4876672 {A : Type'} (Q : type686 A) (P : type180 A) (h1 : P (@EMPTY (A -> Prop))) : (@INTERSECTION_OF A P Q (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4876671 A P Q) (@lem4876670 A Q P h1)). Qed.
Lemma lem4876683 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (fun h0 : P (@EMPTY (A -> Prop)) => @lem4876672 A Q P h0). Qed.
Lemma lem4876684 {A : Type'} (P : type180 A) (Q : type686 A) : term4 A P Q.
Proof. exact (@lem4876683 A P Q). Qed.
Lemma lem4876685 {A : Type'} (P : type686 A) : term5 A P.
Proof. exact (@lem4876684 A (@FINITE (A -> Prop)) P). Qed.
Lemma lem4876687 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4876661 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4876688 {A : Type'} : (@FINITE (A -> Prop) (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem4876687 (A -> Prop)). Qed.
Lemma lem4876689 {A : Type'} : True = (@FINITE (A -> Prop) (@EMPTY (A -> Prop))).
Proof. exact (SYM (@lem4876688 A)). Qed.
Lemma lem4876690 {A : Type'} : @FINITE (A -> Prop) (@EMPTY (A -> Prop)).
Proof. exact (EQ_MP (@lem4876689 A) (@lem0)). Qed.
Lemma lem4876691 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P (@UNIV A)) = True.
Proof. exact (@lem4876685 A P (@lem4876690 A)). Qed.
Lemma lem4876692 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876691 A P)). Qed.
Lemma lem4876693 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876694 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem4876693 A) (@lem4876692 A)). Qed.
Lemma lem4876696 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4876697 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (@lem4876696 (type686 A) t). Qed.
Lemma lem4876698 {A : Type'} : (term9 A) = True.
Proof. exact (@lem4876697 A True). Qed.
Lemma lem4876699 {A : Type'} : (term8 A) = True.
Proof. exact (TRANS (@lem4876694 A) (@lem4876698 A)). Qed.
Lemma lem4876700 {A : Type'} : True = (term8 A).
Proof. exact (SYM (@lem4876699 A)). Qed.
Lemma lem4876701 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4876700 A) (@lem0)). Qed.
