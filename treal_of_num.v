Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_of_num_term_abbrevs.
Lemma lem1322703 : treal_of_num = term0.
Proof. exact (@treal_of_num_def). Qed.
Lemma lem1322704 (_23594 : nat) : _23594 = _23594.
Proof. exact (eq_refl _23594). Qed.
Lemma lem1322705 (_23594 : nat) : (treal_of_num _23594) = (term1 _23594).
Proof. exact (MK_COMB (@lem1322703) (@lem1322704 _23594)). Qed.
Lemma lem1322706 (_23594 : nat) : (term1 _23594) = (term2 _23594).
Proof. exact (eq_refl (term1 _23594)). Qed.
Lemma lem1322707 (_23594 : nat) : (treal_of_num _23594) = (term2 _23594).
Proof. exact (TRANS (@lem1322705 _23594) (@lem1322706 _23594)). Qed.
Lemma lem1322708 : term3.
Proof. exact (fun _23594 : nat => @lem1322707 _23594). Qed.
Lemma lem1322709 (_23594 : nat) : term4 _23594.
Proof. exact (@lem1322708 _23594). Qed.
Lemma lem1322710 (_23594 : nat) : (term4 _23594) = ((treal_of_num _23594) = (term2 _23594)).
Proof. exact (eq_refl (term4 _23594)). Qed.
Lemma lem1322711 (_23594 : nat) : (treal_of_num _23594) = (term2 _23594).
Proof. exact (EQ_MP (@lem1322710 _23594) (@lem1322709 _23594)). Qed.
Lemma lem1322741 (n : nat) : (treal_of_num n) = (term2 n).
Proof. exact (@lem1322711 n). Qed.
Lemma lem1322742 : term3.
Proof. exact (fun n : nat => @lem1322741 n). Qed.
