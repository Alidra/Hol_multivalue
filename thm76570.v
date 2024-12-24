Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm76570_term_abbrevs.
Lemma lem76531 : BIT1 = term0.
Proof. exact (@BIT1_def). Qed.
Lemma lem76532 (_2143 : nat) : _2143 = _2143.
Proof. exact (eq_refl _2143). Qed.
Lemma lem76533 (_2143 : nat) : (BIT1 _2143) = (term1 _2143).
Proof. exact (MK_COMB (@lem76531) (@lem76532 _2143)). Qed.
Lemma lem76534 (_2143 : nat) : (term1 _2143) = (term2 _2143).
Proof. exact (eq_refl (term1 _2143)). Qed.
Lemma lem76535 (_2143 : nat) : (BIT1 _2143) = (term2 _2143).
Proof. exact (TRANS (@lem76533 _2143) (@lem76534 _2143)). Qed.
Lemma lem76536 : term3.
Proof. exact (fun _2143 : nat => @lem76535 _2143). Qed.
Lemma lem76537 (_2143 : nat) : term4 _2143.
Proof. exact (@lem76536 _2143). Qed.
Lemma lem76538 (_2143 : nat) : (term4 _2143) = ((BIT1 _2143) = (term2 _2143)).
Proof. exact (eq_refl (term4 _2143)). Qed.
Lemma lem76539 (_2143 : nat) : (BIT1 _2143) = (term2 _2143).
Proof. exact (EQ_MP (@lem76538 _2143) (@lem76537 _2143)). Qed.
Lemma lem76569 (n : nat) : (BIT1 n) = (term2 n).
Proof. exact (@lem76539 n). Qed.
Lemma lem76570 : term3.
Proof. exact (fun n : nat => @lem76569 n). Qed.
