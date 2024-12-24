Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RIGHT_OR_FORALL_THM_term_abbrevs.
Require Import RIGHT_FORALL_OR_THM_spec.
Lemma lem11736 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (h1). Qed.
Lemma lem11737 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term0 A P Q) = (term1 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (SYM (@lem11736 A P Q h1)). Qed.
Lemma lem11738 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term1 A P Q) = (term0 A P Q).
Proof. exact (h1). Qed.
Lemma lem11739 {A : Type'} (P : Prop) (Q : A -> Prop) (h1 : (term1 A P Q) = (term0 A P Q)) : (term0 A P Q) = (term1 A P Q).
Proof. exact (SYM (@lem11738 A P Q h1)). Qed.
Lemma lem11740 {A : Type'} (P : Prop) (Q : A -> Prop) : ((term0 A P Q) = (term1 A P Q)) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (prop_ext (fun h1 : (term0 A P Q) = (term1 A P Q) => @lem11737 A P Q h1) (fun h1 : (term1 A P Q) = (term0 A P Q) => @lem11739 A P Q h1)). Qed.
Lemma lem11741 {A : Type'} (P : Prop) : (term2 A P) = (term3 A P).
Proof. exact (fun_ext (fun Q : A -> Prop => @lem11740 A P Q)). Qed.
Lemma lem11742 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem11743 {A : Type'} (P : Prop) : (term4 A P) = (term5 A P).
Proof. exact (MK_COMB (@lem11742 A) (@lem11741 A P)). Qed.
Lemma lem11744 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun P : Prop => @lem11743 A P)). Qed.
Lemma lem11745 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem11746 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem11745) (@lem11744 A)). Qed.
Lemma lem11747 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem11746 A) (@lem11700 A)). Qed.
Lemma lem11748 {A : Type'} (P : Prop) : term10 A P.
Proof. exact (@lem11747 A P). Qed.
Lemma lem11749 {A : Type'} (P : Prop) : (term10 A P) = (term5 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem11750 {A : Type'} (P : Prop) : term5 A P.
Proof. exact (EQ_MP (@lem11749 A P) (@lem11748 A P)). Qed.
Lemma lem11751 {A : Type'} (P : Prop) (Q : A -> Prop) : term11 A P Q.
Proof. exact (@lem11750 A P Q). Qed.
Lemma lem11752 {A : Type'} (P : Prop) (Q : A -> Prop) : (term11 A P Q) = ((term1 A P Q) = (term0 A P Q)).
Proof. exact (eq_refl (term11 A P Q)). Qed.
Lemma lem11755 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (EQ_MP (@lem11752 A P Q) (@lem11751 A P Q)). Qed.
Lemma lem11756 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1 A P Q) = (term0 A P Q).
Proof. exact (@lem11755 A P Q). Qed.
Lemma lem11761 {A : Type'} (P : Prop) : term5 A P.
Proof. exact (fun Q : A -> Prop => @lem11756 A P Q). Qed.
Lemma lem11766 {A : Type'} : term9 A.
Proof. exact (fun P : Prop => @lem11761 A P). Qed.
