Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3453893_term_abbrevs.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Lemma lem3453889 {_83064 : Type'} : term0 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem3453890 {_83064 : Type'} (P : type919 _83064) : term1 _83064 P.
Proof. exact (@lem3453889 _83064 P). Qed.
Lemma lem3453891 {_83064 : Type'} (P : type919 _83064) : (term1 _83064 P) = (term2 _83064 P).
Proof. exact (eq_refl (term1 _83064 P)). Qed.
Lemma lem3453892 {_83064 : Type'} (P : type919 _83064) : term2 _83064 P.
Proof. exact (EQ_MP (@lem3453891 _83064 P) (@lem3453890 _83064 P)). Qed.
Lemma lem3453893 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term3 _83064 P x.
Proof. exact (@lem3453892 _83064 P x). Qed.
