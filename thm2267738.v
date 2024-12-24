Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267738_term_abbrevs.
Require Import thm2267726_spec.
Require Import thm2267735_spec.
Lemma lem2267736 : term0.
Proof. exact (fun r : real => @lem2267735 r). Qed.
Lemma lem2267737 : term1.
Proof. exact (fun a : int => @lem2267726 a). Qed.
Lemma lem2267738 : term2.
Proof. exact (conj (@lem2267737) (@lem2267736)). Qed.
