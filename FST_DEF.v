Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FST_DEF_term_abbrevs.
Lemma lem45467 {A B : Type'} : (@fst A B) = (term0 A B).
Proof. exact (@FST_def A B). Qed.
Lemma lem45468 {A B : Type'} (p : prod A B) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem45469 {A B : Type'} (p : prod A B) : (@fst A B p) = (term1 A B p).
Proof. exact (MK_COMB (@lem45467 A B) (@lem45468 A B p)). Qed.
Lemma lem45470 {A B : Type'} (p : prod A B) : (term1 A B p) = (term2 A B p).
Proof. exact (eq_refl (term1 A B p)). Qed.
Lemma lem45471 {A B : Type'} (p : prod A B) : (@fst A B p) = (term2 A B p).
Proof. exact (TRANS (@lem45469 A B p) (@lem45470 A B p)). Qed.
Lemma lem45472 {A B : Type'} : term3 A B.
Proof. exact (fun p : prod A B => @lem45471 A B p). Qed.
