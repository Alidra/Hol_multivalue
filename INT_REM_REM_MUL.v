Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_REM_MUL_term_abbrevs.
Require Import thm2530590_spec.
Require Import thm2530600_spec.
Lemma lem2530605 : term0.
Proof. exact (fun m : int => @lem2530600 m). Qed.
Lemma lem2530606 : term1.
Proof. exact (conj (@lem2530605) (@lem2530590)). Qed.
