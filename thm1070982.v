Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070982_term_abbrevs.
Require Import thm1070961_spec.
Lemma lem1070981 {A : Type'} (r : recspace A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1070982 {A : Type'} (r : recspace A) (list' : type1338 A) (CONS' : type1399 A) (NIL' : recspace A) (h1 : CONS' = (term0 A)) (h2 : list' = (term1 A NIL' CONS')) (h3 : NIL' = (term2 A)) : (list' r) = (term3 A r).
Proof. exact (MK_COMB (@lem1070961 A list' CONS' NIL' h1 h2 h3) (@lem1070981 A r)). Qed.
