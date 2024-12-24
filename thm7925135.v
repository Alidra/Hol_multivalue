Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925135_term_abbrevs.
Require Import thm7925118_spec.
Lemma lem7925134 {A : Type'} (r : type1676 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem7925135 {A : Type'} (r : type1676 A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) (h2 : tybit0' = (term1 A _103783')) : (tybit0' r) = (term2 A r).
Proof. exact (MK_COMB (@lem7925118 A tybit0' _103783' h1 h2) (@lem7925134 A r)). Qed.
