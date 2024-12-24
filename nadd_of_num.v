Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import nadd_of_num_term_abbrevs.
Lemma lem1268699 : nadd_of_num = term0.
Proof. exact (@nadd_of_num_def). Qed.
Lemma lem1268700 (_23161 : nat) : _23161 = _23161.
Proof. exact (eq_refl _23161). Qed.
Lemma lem1268701 (_23161 : nat) : (nadd_of_num _23161) = (term1 _23161).
Proof. exact (MK_COMB (@lem1268699) (@lem1268700 _23161)). Qed.
Lemma lem1268702 (_23161 : nat) : (term1 _23161) = (term2 _23161).
Proof. exact (eq_refl (term1 _23161)). Qed.
Lemma lem1268703 (_23161 : nat) : (nadd_of_num _23161) = (term2 _23161).
Proof. exact (TRANS (@lem1268701 _23161) (@lem1268702 _23161)). Qed.
Lemma lem1268704 : term3.
Proof. exact (fun _23161 : nat => @lem1268703 _23161). Qed.
Lemma lem1268705 (_23161 : nat) : term4 _23161.
Proof. exact (@lem1268704 _23161). Qed.
Lemma lem1268706 (_23161 : nat) : (term4 _23161) = ((nadd_of_num _23161) = (term2 _23161)).
Proof. exact (eq_refl (term4 _23161)). Qed.
Lemma lem1268707 (_23161 : nat) : (nadd_of_num _23161) = (term2 _23161).
Proof. exact (EQ_MP (@lem1268706 _23161) (@lem1268705 _23161)). Qed.
Lemma lem1268737 (k : nat) : (nadd_of_num k) = (term2 k).
Proof. exact (@lem1268707 k). Qed.
Lemma lem1268738 : term3.
Proof. exact (fun k : nat => @lem1268737 k). Qed.
