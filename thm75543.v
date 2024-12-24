Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm75543_term_abbrevs.
Lemma lem75504 : NUMERAL = term0.
Proof. exact (@NUMERAL_def). Qed.
Lemma lem75505 (_2128 : nat) : _2128 = _2128.
Proof. exact (eq_refl _2128). Qed.
Lemma lem75506 (_2128 : nat) : (NUMERAL _2128) = (term1 _2128).
Proof. exact (MK_COMB (@lem75504) (@lem75505 _2128)). Qed.
Lemma lem75507 (_2128 : nat) : (term1 _2128) = _2128.
Proof. exact (eq_refl (term1 _2128)). Qed.
Lemma lem75508 (_2128 : nat) : (NUMERAL _2128) = _2128.
Proof. exact (TRANS (@lem75506 _2128) (@lem75507 _2128)). Qed.
Lemma lem75509 : term2.
Proof. exact (fun _2128 : nat => @lem75508 _2128). Qed.
Lemma lem75510 (_2128 : nat) : term3 _2128.
Proof. exact (@lem75509 _2128). Qed.
Lemma lem75511 (_2128 : nat) : (term3 _2128) = ((NUMERAL _2128) = _2128).
Proof. exact (eq_refl (term3 _2128)). Qed.
Lemma lem75512 (_2128 : nat) : (NUMERAL _2128) = _2128.
Proof. exact (EQ_MP (@lem75511 _2128) (@lem75510 _2128)). Qed.
Lemma lem75542 (n : nat) : (NUMERAL n) = n.
Proof. exact (@lem75512 n). Qed.
Lemma lem75543 : term2.
Proof. exact (fun n : nat => @lem75542 n). Qed.
