Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240298_term_abbrevs.
Require Import thm1240281_spec.
Lemma lem1240297 (r : type1678) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1240298 (r : type1678) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term0) (h2 : char' = (term1 _22730')) : (char' r) = (term2 r).
Proof. exact (MK_COMB (@lem1240281 char' _22730' h1 h2) (@lem1240297 r)). Qed.
