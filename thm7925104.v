Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925104_term_abbrevs.
Require Import thm7925100_spec.
Lemma lem7925102 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term1 A tybit0' _103783' a.
Proof. exact (@lem7925100 A tybit0' _103783' h1 a). Qed.
Lemma lem7925103 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (a : finite_sum A A) : (term1 A tybit0' _103783' a) = (term2 A tybit0' _103783' a).
Proof. exact (eq_refl (term1 A tybit0' _103783' a)). Qed.
Lemma lem7925104 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term2 A tybit0' _103783' a.
Proof. exact (EQ_MP (@lem7925103 A tybit0' _103783' a) (@lem7925102 A a tybit0' _103783' h1)). Qed.
