Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925118_term_abbrevs.
Require Import thm7924817_spec.
Lemma lem7925105 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : tybit0' = (term0 A _103783').
Proof. exact (h1). Qed.
Lemma lem7925106 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7925107 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term2 A)) : (term3 A _103783') = (term4 A).
Proof. exact (MK_COMB (@lem7925106 A) (@lem7924817 A _103783' h1)). Qed.
Lemma lem7925108 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem7925109 {A : Type'} (_103783' : type45 A) : (term6 A _103783') = (term6 A _103783').
Proof. exact (eq_refl (term6 A _103783')). Qed.
Lemma lem7925110 {A : Type'} (_103783' : type45 A) : ((term3 A _103783') = (term4 A)) = ((term3 A _103783') = (term5 A)).
Proof. exact (MK_COMB (@lem7925109 A _103783') (@lem7925108 A)). Qed.
Lemma lem7925111 {A : Type'} (_103783' : type45 A) : (term3 A _103783') = (term0 A _103783').
Proof. exact (eq_refl (term3 A _103783')). Qed.
Lemma lem7925112 {A : Type'} : (@eq ((recspace (finite_sum A A)) -> Prop)) = (@eq ((recspace (finite_sum A A)) -> Prop)).
Proof. exact (eq_refl (@eq ((recspace (finite_sum A A)) -> Prop))). Qed.
Lemma lem7925113 {A : Type'} (_103783' : type45 A) : (term6 A _103783') = (term7 A _103783').
Proof. exact (MK_COMB (@lem7925112 A) (@lem7925111 A _103783')). Qed.
Lemma lem7925114 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (eq_refl (term5 A)). Qed.
Lemma lem7925115 {A : Type'} (_103783' : type45 A) : ((term3 A _103783') = (term5 A)) = ((term0 A _103783') = (term5 A)).
Proof. exact (MK_COMB (@lem7925113 A _103783') (@lem7925114 A)). Qed.
Lemma lem7925116 {A : Type'} (_103783' : type45 A) : ((term3 A _103783') = (term4 A)) = ((term0 A _103783') = (term5 A)).
Proof. exact (TRANS (@lem7925110 A _103783') (@lem7925115 A _103783')). Qed.
Lemma lem7925117 {A : Type'} (_103783' : type45 A) (h1 : _103783' = (term2 A)) : (term0 A _103783') = (term5 A).
Proof. exact (EQ_MP (@lem7925116 A _103783') (@lem7925107 A _103783' h1)). Qed.
Lemma lem7925118 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : _103783' = (term2 A)) (h2 : tybit0' = (term0 A _103783')) : tybit0' = (term5 A).
Proof. exact (TRANS (@lem7925105 A tybit0' _103783' h2) (@lem7925117 A _103783' h1)). Qed.
