Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925129_term_abbrevs.
Require Import thm7925104_spec.
Require Import thm7925118_spec.
Lemma lem7925119 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : (_103783' a) = (_103783' a).
Proof. exact (eq_refl (_103783' a)). Qed.
Lemma lem7925120 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) (h2 : tybit0' = (term1 A _103783')) : (term2 A tybit0' _103783' a) = (term3 A _103783' a).
Proof. exact (MK_COMB (@lem7925118 A tybit0' _103783' h1 h2) (@lem7925119 A _103783' a)). Qed.
Lemma lem7925121 {A : Type'} (a : finite_sum A A) (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) (h2 : tybit0' = (term1 A _103783')) : term3 A _103783' a.
Proof. exact (EQ_MP (@lem7925120 A a tybit0' _103783' h1 h2) (@lem7925104 A a tybit0' _103783' h2)). Qed.
Lemma lem7925122 {A : Type'} (_103783' : type45 A) : (term1 A _103783') = (term1 A _103783').
Proof. exact (eq_refl (term1 A _103783')). Qed.
Lemma lem7925123 {A : Type'} (tybit0' : type1331 A) (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) : term4 A tybit0' _103783' a.
Proof. exact (fun h0 : tybit0' = (term1 A _103783') => @lem7925121 A a tybit0' _103783' h1 h0). Qed.
Lemma lem7925124 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) : term5 A _103783' a.
Proof. exact (@lem7925123 A (term1 A _103783') a _103783' h1). Qed.
Lemma lem7925125 {A : Type'} (a : finite_sum A A) (_103783' : type45 A) (h1 : _103783' = (term0 A)) : term3 A _103783' a.
Proof. exact (@lem7925124 A a _103783' h1 (@lem7925122 A _103783')). Qed.
Lemma lem7925126 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7925127 {A : Type'} (_103783' : type45 A) (a : finite_sum A A) : term6 A _103783' a.
Proof. exact (fun h0 : _103783' = (term0 A) => @lem7925125 A a _103783' h0). Qed.
Lemma lem7925128 {A : Type'} (a : finite_sum A A) : term7 A a.
Proof. exact (@lem7925127 A (term0 A) a). Qed.
Lemma lem7925129 {A : Type'} (a : finite_sum A A) : term8 A a.
Proof. exact (@lem7925128 A a (@lem7925126 A)). Qed.
