Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066993_term_abbrevs.
Require Import thm1066972_spec.
Lemma lem1066992 {A B : Type'} (r : type1677 A B) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1066993 {A B : Type'} (r : type1677 A B) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term0 A B)) (h2 : INR' = (term1 A B)) (h3 : sum' = (term2 A B INL' INR')) : (sum' r) = (term3 A B r).
Proof. exact (MK_COMB (@lem1066972 A B sum' INL' INR' h1 h2 h3) (@lem1066992 A B r)). Qed.
