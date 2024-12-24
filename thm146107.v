Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm146107_term_abbrevs.
Require Import thm145847_spec.
Require Import thm146068_spec.
Lemma lem146069 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem146070 : term1.
Proof. exact (EQ_MP (@lem146069) (@lem145847)). Qed.
Lemma lem146071 : term2.
Proof. exact (@lem146070 term3). Qed.
Lemma lem146072 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem146073 : term4.
Proof. exact (EQ_MP (@lem146072) (@lem146071)). Qed.
Lemma lem146074 (h1 : Factorial.fact = term5) : Factorial.fact = term5.
Proof. exact (h1). Qed.
Lemma lem146075 (h1 : Factorial.fact = term5) : term5 = Factorial.fact.
Proof. exact (SYM (@lem146074 h1)). Qed.
Lemma lem146076 (h1 : term5 = Factorial.fact) : term5 = Factorial.fact.
Proof. exact (h1). Qed.
Lemma lem146077 (h1 : term5 = Factorial.fact) : Factorial.fact = term5.
Proof. exact (SYM (@lem146076 h1)). Qed.
Lemma lem146078 : (Factorial.fact = term5) = (term5 = Factorial.fact).
Proof. exact (prop_ext (fun h1 : Factorial.fact = term5 => @lem146075 h1) (fun h1 : term5 = Factorial.fact => @lem146077 h1)). Qed.
Lemma lem146081 : term5 = Factorial.fact.
Proof. exact (EQ_MP (@lem146078) (@lem146068)). Qed.
Lemma lem146082 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem146083 : term6 = term7.
Proof. exact (MK_COMB (@lem146081) (@lem146082)). Qed.
Lemma lem146084 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem146085 : term8 = term9.
Proof. exact (MK_COMB (@lem146084) (@lem146083)). Qed.
Lemma lem146086 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem146087 : (term6 = term10) = (term7 = term10).
Proof. exact (MK_COMB (@lem146085) (@lem146086)). Qed.
Lemma lem146088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem146089 : term11 = term12.
Proof. exact (MK_COMB (@lem146088) (@lem146087)). Qed.
Lemma lem146091 : term5 = Factorial.fact.
Proof. exact (EQ_MP (@lem146078) (@lem146068)). Qed.
Lemma lem146092 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem146093 (n : nat) : (term13 n) = (term14 n).
Proof. exact (MK_COMB (@lem146091) (@lem146092 n)). Qed.
Lemma lem146094 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem146095 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem146094) (@lem146093 n)). Qed.
Lemma lem146097 : term5 = Factorial.fact.
Proof. exact (EQ_MP (@lem146078) (@lem146068)). Qed.
Lemma lem146098 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem146099 (n : nat) : (term17 n) = (Factorial.fact n).
Proof. exact (MK_COMB (@lem146097) (@lem146098 n)). Qed.
Lemma lem146100 (n : nat) : (term18 n) = (term18 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem146101 (n : nat) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem146100 n) (@lem146099 n)). Qed.
Lemma lem146102 (n : nat) : ((term13 n) = (term19 n)) = ((term14 n) = (term20 n)).
Proof. exact (MK_COMB (@lem146095 n) (@lem146101 n)). Qed.
Lemma lem146103 : term21 = term22.
Proof. exact (fun_ext (fun n : nat => @lem146102 n)). Qed.
Lemma lem146104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146105 : term23 = term24.
Proof. exact (MK_COMB (@lem146104) (@lem146103)). Qed.
Lemma lem146106 : term4 = term25.
Proof. exact (MK_COMB (@lem146089) (@lem146105)). Qed.
Lemma lem146107 : term25.
Proof. exact (EQ_MP (@lem146106) (@lem146073)). Qed.
