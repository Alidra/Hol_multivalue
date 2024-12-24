Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925148_term_abbrevs.
Require Import thm7924817_spec.
Lemma lem7925137 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem7925138 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term1 A)) : (term2 A _103783') = (term3 A).
Proof. exact (MK_COMB (@lem7925137 A) (@lem7924817 A _103783' h1)). Qed.
Lemma lem7925139 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem7925140 {A : Type'} (_103783' : type45 A) : (term5 A _103783') = (term5 A _103783').
Proof. exact (eq_refl (term5 A _103783')). Qed.
Lemma lem7925141 {A : Type'} (_103783' : type45 A) : ((term2 A _103783') = (term3 A)) = ((term2 A _103783') = (term4 A)).
Proof. exact (MK_COMB (@lem7925140 A _103783') (@lem7925139 A)). Qed.
Lemma lem7925142 {A : Type'} (_103783' : type45 A) : (term2 A _103783') = (term6 A _103783').
Proof. exact (eq_refl (term2 A _103783')). Qed.
Lemma lem7925143 {A : Type'} : (@eq ((finite_sum A A) -> tybit0 A)) = (@eq ((finite_sum A A) -> tybit0 A)).
Proof. exact (eq_refl (@eq ((finite_sum A A) -> tybit0 A))). Qed.
Lemma lem7925144 {A : Type'} (_103783' : type45 A) : (term5 A _103783') = (term7 A _103783').
Proof. exact (MK_COMB (@lem7925143 A) (@lem7925142 A _103783')). Qed.
Lemma lem7925145 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7925146 {A : Type'} (_103783' : type45 A) : ((term2 A _103783') = (term4 A)) = ((term6 A _103783') = (term4 A)).
Proof. exact (MK_COMB (@lem7925144 A _103783') (@lem7925145 A)). Qed.
Lemma lem7925147 {A : Type'} (_103783' : type45 A) : ((term2 A _103783') = (term3 A)) = ((term6 A _103783') = (term4 A)).
Proof. exact (TRANS (@lem7925141 A _103783') (@lem7925146 A _103783')). Qed.
Lemma lem7925148 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term1 A)) : (term6 A _103783') = (term4 A).
Proof. exact (EQ_MP (@lem7925147 A _103783') (@lem7925138 A _103783' h1)). Qed.
