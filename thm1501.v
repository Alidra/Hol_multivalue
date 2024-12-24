Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1501_term_abbrevs.
Require Import thm0_spec.
Require Import thm69_spec.
Lemma lem1494 : term0.
Proof. exact (fun h0 : ~ False => @lem0). Qed.
Lemma lem1496 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem1497 : False -> False.
Proof. exact (fun h0 : False => @lem1496 h0). Qed.
Lemma lem1498 : (False -> False) = (~ False).
Proof. exact (@lem69 False). Qed.
Lemma lem1499 : ~ False.
Proof. exact (EQ_MP (@lem1498) (@lem1497)). Qed.
Lemma lem1500 : term1.
Proof. exact (fun h0 : True => @lem1499). Qed.
Lemma lem1501 : term2.
Proof. exact (conj (@lem1494) (@lem1500)). Qed.
