Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3459022_term_abbrevs.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Lemma lem3459018 {_83064 : Type'} : term0 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem3459019 {_83064 : Type'} (P : type919 _83064) : term1 _83064 P.
Proof. exact (@lem3459018 _83064 P). Qed.
Lemma lem3459020 {_83064 : Type'} (P : type919 _83064) : (term1 _83064 P) = (term2 _83064 P).
Proof. exact (eq_refl (term1 _83064 P)). Qed.
Lemma lem3459021 {_83064 : Type'} (P : type919 _83064) : term2 _83064 P.
Proof. exact (EQ_MP (@lem3459020 _83064 P) (@lem3459019 _83064 P)). Qed.
Lemma lem3459022 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term3 _83064 P x.
Proof. exact (@lem3459021 _83064 P x). Qed.
