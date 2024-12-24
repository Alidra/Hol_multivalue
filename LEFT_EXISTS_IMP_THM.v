Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_EXISTS_IMP_THM_term_abbrevs.
Require Import LEFT_IMP_FORALL_THM_spec.
Lemma lem11986 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (h1). Qed.
Lemma lem11987 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (SYM (@lem11986 A P Q h1)). Qed.
Lemma lem11988 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (h1). Qed.
Lemma lem11989 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (SYM (@lem11988 A P Q h1)). Qed.
Lemma lem11990 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term0 A P Q) = (term1 A P Q)) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (prop_ext (fun h1 : (term0 A P Q) = (term1 A P Q) => @lem11987 A P Q h1) (fun h1 : (term1 A P Q) = (term0 A P Q) => @lem11989 A P Q h1)). Qed.
Lemma lem11991 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (fun_ext (fun Q : Prop => @lem11990 A P Q)). Qed.
Lemma lem11992 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem11993 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (MK_COMB (@lem11992) (@lem11991 A P)). Qed.
Lemma lem11994 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem11993 A P)). Qed.
Lemma lem11995 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem11996 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem11995 A) (@lem11994 A)). Qed.
Lemma lem11997 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem11996 A) (@lem11983 A)). Qed.
Lemma lem11998 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem11997 A P). Qed.
Lemma lem11999 {A : Type'} (P : A -> Prop) : (term10 A P) = (term5 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem12000 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (EQ_MP (@lem11999 A P) (@lem11998 A P)). Qed.
Lemma lem12001 {A : Type'} (P : A -> Prop) (Q : Prop) : term11 A P Q.
Proof. exact (@lem12000 A P Q). Qed.
Lemma lem12002 {A : Type'} (P : A -> Prop) (Q : Prop) : (term11 A P Q) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem12005 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (EQ_MP (@lem12002 A P Q) (@lem12001 A P Q)). Qed.
Lemma lem12006 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (@lem12005 A P Q). Qed.
Lemma lem12011 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (fun Q : Prop => @lem12006 A P Q). Qed.
Lemma lem12016 {A : Type'} : term9 A.
Proof. exact (fun P : A -> Prop => @lem12011 A P). Qed.
