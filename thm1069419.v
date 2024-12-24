Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069419_term_abbrevs.
Require Import thm1069398_spec.
Lemma lem1069418 {A : Type'} (r : recspace A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1069419 {A : Type'} (r : recspace A) (option' : type1338 A) (SOME' : type1432 A) (NONE' : recspace A) (h1 : SOME' = (term0 A)) (h2 : option' = (term1 A NONE' SOME')) (h3 : NONE' = (term2 A)) : (option' r) = (term3 A r).
Proof. exact (MK_COMB (@lem1069398 A option' SOME' NONE' h1 h2 h3) (@lem1069418 A r)). Qed.
