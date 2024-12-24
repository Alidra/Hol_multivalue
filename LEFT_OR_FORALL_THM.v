Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LEFT_OR_FORALL_THM_term_abbrevs.
Require Import LEFT_FORALL_OR_THM_spec.
Lemma lem11703 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (h1). Qed.
Lemma lem11704 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (SYM (@lem11703 A P Q h1)). Qed.
Lemma lem11705 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (h1). Qed.
Lemma lem11706 {A : Type'} (P : A -> Prop) (Q : Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (SYM (@lem11705 A P Q h1)). Qed.
Lemma lem11707 {A : Type'} (P : A -> Prop) (Q : Prop) : ((term0 A P Q) = (term1 A P Q)) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (prop_ext (fun h1 : (term0 A P Q) = (term1 A P Q) => @lem11704 A P Q h1) (fun h1 : (term1 A P Q) = (term0 A P Q) => @lem11706 A P Q h1)). Qed.
Lemma lem11708 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (fun_ext (fun Q : Prop => @lem11707 A P Q)). Qed.
Lemma lem11709 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem11710 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (MK_COMB (@lem11709) (@lem11708 A P)). Qed.
Lemma lem11711 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem11710 A P)). Qed.
Lemma lem11712 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem11713 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem11712 A) (@lem11711 A)). Qed.
Lemma lem11714 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem11713 A) (@lem11454 A)). Qed.
Lemma lem11715 {A : Type'} (P : A -> Prop) : term10 A P.
Proof. exact (@lem11714 A P). Qed.
Lemma lem11716 {A : Type'} (P : A -> Prop) : (term10 A P) = (term5 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem11717 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (EQ_MP (@lem11716 A P) (@lem11715 A P)). Qed.
Lemma lem11718 {A : Type'} (P : A -> Prop) (Q : Prop) : term11 A P Q.
Proof. exact (@lem11717 A P Q). Qed.
Lemma lem11719 {A : Type'} (P : A -> Prop) (Q : Prop) : (term11 A P Q) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem11722 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (EQ_MP (@lem11719 A P Q) (@lem11718 A P Q)). Qed.
Lemma lem11723 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (@lem11722 A P Q). Qed.
Lemma lem11728 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (fun Q : Prop => @lem11723 A P Q). Qed.
Lemma lem11733 {A : Type'} : term9 A.
Proof. exact (fun P : A -> Prop => @lem11728 A P). Qed.
