Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928423_term_abbrevs.
Require Import thm7928419_spec.
Lemma lem7928421 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term1 A tybit1' _103802' a.
Proof. exact (@lem7928419 A tybit1' _103802' h1 a). Qed.
Lemma lem7928422 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (a : type6 A) : (term1 A tybit1' _103802' a) = (term2 A tybit1' _103802' a).
Proof. exact (eq_refl (term1 A tybit1' _103802' a)). Qed.
Lemma lem7928423 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term2 A tybit1' _103802' a.
Proof. exact (EQ_MP (@lem7928422 A tybit1' _103802' a) (@lem7928421 A a tybit1' _103802' h1)). Qed.
