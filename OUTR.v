Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import OUTR_term_abbrevs.
Require Import thm1068659_spec.
Require Import thm1068987_spec.
Lemma lem1068988 {A B : Type'} : (term0 A B) = (term1 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem1068989 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem1068988 A B) (@lem1068659 A B)). Qed.
Lemma lem1068990 {A B : Type'} : term2 A B.
Proof. exact (@lem1068989 A B term3). Qed.
Lemma lem1068991 {A B : Type'} : (term2 A B) = (term4 A B).
Proof. exact (eq_refl (term2 A B)). Qed.
Lemma lem1068992 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem1068991 A B) (@lem1068990 A B)). Qed.
Lemma lem1068993 {A B : Type'} (h1 : (@OUTR A B) = (term5 A B)) : (@OUTR A B) = (term5 A B).
Proof. exact (h1). Qed.
Lemma lem1068994 {A B : Type'} (h1 : (@OUTR A B) = (term5 A B)) : (term5 A B) = (@OUTR A B).
Proof. exact (SYM (@lem1068993 A B h1)). Qed.
Lemma lem1068995 {A B : Type'} (h1 : (term5 A B) = (@OUTR A B)) : (term5 A B) = (@OUTR A B).
Proof. exact (h1). Qed.
Lemma lem1068996 {A B : Type'} (h1 : (term5 A B) = (@OUTR A B)) : (@OUTR A B) = (term5 A B).
Proof. exact (SYM (@lem1068995 A B h1)). Qed.
Lemma lem1068997 {A B : Type'} : ((@OUTR A B) = (term5 A B)) = ((term5 A B) = (@OUTR A B)).
Proof. exact (prop_ext (fun h1 : (@OUTR A B) = (term5 A B) => @lem1068994 A B h1) (fun h1 : (term5 A B) = (@OUTR A B) => @lem1068996 A B h1)). Qed.
Lemma lem1069000 {A B : Type'} : (term5 A B) = (@OUTR A B).
Proof. exact (EQ_MP (@lem1068997 A B) (@lem1068987 A B)). Qed.
Lemma lem1069001 {A B : Type'} : (term5 A B) = (@OUTR A B).
Proof. exact (@lem1069000 A B). Qed.
Lemma lem1069002 {A B : Type'} (y : B) : (@inr A B y) = (@inr A B y).
Proof. exact (eq_refl (@inr A B y)). Qed.
Lemma lem1069003 {A B : Type'} (y : B) : (term6 A B y) = (term7 A B y).
Proof. exact (MK_COMB (@lem1069001 A B) (@lem1069002 A B y)). Qed.
Lemma lem1069004 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem1069005 {A B : Type'} (y : B) : (term8 A B y) = (term9 A B y).
Proof. exact (MK_COMB (@lem1069004 B) (@lem1069003 A B y)). Qed.
Lemma lem1069006 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1069007 {A B : Type'} (y : B) : ((term6 A B y) = y) = ((term7 A B y) = y).
Proof. exact (MK_COMB (@lem1069005 A B y) (@lem1069006 B y)). Qed.
Lemma lem1069008 {A B : Type'} : (term10 A B) = (term11 A B).
Proof. exact (fun_ext (fun y : B => @lem1069007 A B y)). Qed.
Lemma lem1069009 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1069010 {A B : Type'} : (term4 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem1069009 B) (@lem1069008 A B)). Qed.
Lemma lem1069011 {A B : Type'} : term12 A B.
Proof. exact (EQ_MP (@lem1069010 A B) (@lem1068992 A B)). Qed.
Lemma lem1069012 {A B : Type'} (y : B) : term13 A B y.
Proof. exact (@lem1069011 A B y). Qed.
Lemma lem1069013 {A B : Type'} (y : B) : (term13 A B y) = ((term7 A B y) = y).
Proof. exact (eq_refl (term13 A B y)). Qed.
Lemma lem1069014 {A B : Type'} (y : B) : (term7 A B y) = y.
Proof. exact (EQ_MP (@lem1069013 A B y) (@lem1069012 A B y)). Qed.
