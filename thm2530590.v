Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2530590_term_abbrevs.
Require Import thm2530574_spec.
Lemma lem2530580 (n : int) (m : int) : term0 n m.
Proof. exact (fun p : int => @lem2530574 n m p). Qed.
Lemma lem2530585 (m : int) : term1 m.
Proof. exact (fun n : int => @lem2530580 n m). Qed.
Lemma lem2530590 : term2.
Proof. exact (fun m : int => @lem2530585 m). Qed.
