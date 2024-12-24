Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import char_INDUCT_term_abbrevs.
Require Import thm1240885_spec.
Require Import thm1242354_spec.
Lemma lem1242355 : term0 = term0.
Proof. exact (eq_refl term0). Qed.
Lemma lem1242356 : term1 = term2.
Proof. exact (MK_COMB (@lem1242355) (@lem1242354)). Qed.
Lemma lem1242357 : term2 = term3.
Proof. exact (eq_refl term2). Qed.
Lemma lem1242358 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1242359 : (term1 = term2) = (term1 = term3).
Proof. exact (MK_COMB (@lem1242358) (@lem1242357)). Qed.
Lemma lem1242360 : term1 = term5.
Proof. exact (eq_refl term1). Qed.
Lemma lem1242361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1242362 : term4 = term6.
Proof. exact (MK_COMB (@lem1242361) (@lem1242360)). Qed.
Lemma lem1242363 : term3 = term3.
Proof. exact (eq_refl term3). Qed.
Lemma lem1242364 : (term1 = term3) = (term5 = term3).
Proof. exact (MK_COMB (@lem1242362) (@lem1242363)). Qed.
Lemma lem1242365 : (term1 = term2) = (term5 = term3).
Proof. exact (TRANS (@lem1242359) (@lem1242364)). Qed.
Lemma lem1242366 : term5 = term3.
Proof. exact (EQ_MP (@lem1242365) (@lem1242356)). Qed.
Lemma lem1242367 : term3.
Proof. exact (EQ_MP (@lem1242366) (@lem1240885)). Qed.
