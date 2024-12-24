Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2530600_term_abbrevs.
Require Import thm2530575_spec.
Lemma lem2530595 (m : int) (n : int) : term0 m n.
Proof. exact (fun p : int => @lem2530575 p m n). Qed.
Lemma lem2530600 (m : int) : term1 m.
Proof. exact (fun n : int => @lem2530595 m n). Qed.
