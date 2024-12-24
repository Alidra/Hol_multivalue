Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928448_term_abbrevs.
Require Import thm7928423_spec.
Require Import thm7928437_spec.
Lemma lem7928438 {A : Type'} (_103802' : type39 A) (a : type6 A) : (_103802' a) = (_103802' a).
Proof. exact (eq_refl (_103802' a)). Qed.
Lemma lem7928439 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) (h2 : tybit1' = (term1 A _103802')) : (term2 A tybit1' _103802' a) = (term3 A _103802' a).
Proof. exact (MK_COMB (@lem7928437 A tybit1' _103802' h1 h2) (@lem7928438 A _103802' a)). Qed.
Lemma lem7928440 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) (h2 : tybit1' = (term1 A _103802')) : term3 A _103802' a.
Proof. exact (EQ_MP (@lem7928439 A a tybit1' _103802' h1 h2) (@lem7928423 A a tybit1' _103802' h2)). Qed.
Lemma lem7928441 {A : Type'} (_103802' : type39 A) : (term1 A _103802') = (term1 A _103802').
Proof. exact (eq_refl (term1 A _103802')). Qed.
Lemma lem7928442 {A : Type'} (tybit1' : type1329 A) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) : term4 A tybit1' _103802' a.
Proof. exact (fun h0 : tybit1' = (term1 A _103802') => @lem7928440 A a tybit1' _103802' h1 h0). Qed.
Lemma lem7928443 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) : term5 A _103802' a.
Proof. exact (@lem7928442 A (term1 A _103802') a _103802' h1). Qed.
Lemma lem7928444 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) : term3 A _103802' a.
Proof. exact (@lem7928443 A a _103802' h1 (@lem7928441 A _103802')). Qed.
Lemma lem7928445 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7928446 {A : Type'} (_103802' : type39 A) (a : type6 A) : term6 A _103802' a.
Proof. exact (fun h0 : _103802' = (term0 A) => @lem7928444 A a _103802' h0). Qed.
Lemma lem7928447 {A : Type'} (a : type6 A) : term7 A a.
Proof. exact (@lem7928446 A (term0 A) a). Qed.
Lemma lem7928448 {A : Type'} (a : type6 A) : term8 A a.
Proof. exact (@lem7928447 A a (@lem7928445 A)). Qed.
