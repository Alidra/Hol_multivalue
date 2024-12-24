Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_CLAUSES_term_abbrevs.
Require Import thm10164_spec.
Require Import thm10186_spec.
Lemma lem10191 : term0.
Proof. exact (fun t : Prop => @lem10164 t). Qed.
Lemma lem10192 : term1.
Proof. exact (conj (@lem10191) (@lem10186)). Qed.
