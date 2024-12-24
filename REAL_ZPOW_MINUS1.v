Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_MINUS1_term_abbrevs.
Require Import REAL_ZPOW_1_spec.
Require Import REAL_ZPOW_NEG_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3173053 (x : real) : term0 x.
Proof. exact (@lem3169385 x). Qed.
Lemma lem3173054 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3173056 (x : real) : term2 x.
Proof. exact (@lem3173052 x). Qed.
Lemma lem3173057 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem3173058 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem3173057 x) (@lem3173056 x)). Qed.
Lemma lem3173059 (x : real) (n : int) : term4 x n.
Proof. exact (@lem3173058 x n). Qed.
Lemma lem3173060 (x : real) (n : int) : (term4 x n) = ((term5 x n) = (term6 x n)).
Proof. exact (eq_refl (term4 x n)). Qed.
Lemma lem3173069 (x : real) (n : int) : (term5 x n) = (term6 x n).
Proof. exact (EQ_MP (@lem3173060 x n) (@lem3173059 x n)). Qed.
Lemma lem3173070 (x : real) : (term7 x) = (term8 x).
Proof. exact (@lem3173069 x term9). Qed.
Lemma lem3173072 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem3173054 x) (@lem3173053 x)). Qed.
Lemma lem3173073 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem3173074 (x : real) : (term8 x) = (real_inv x).
Proof. exact (MK_COMB (@lem3173073) (@lem3173072 x)). Qed.
Lemma lem3173075 (x : real) : (term7 x) = (real_inv x).
Proof. exact (TRANS (@lem3173070 x) (@lem3173074 x)). Qed.
Lemma lem3173076 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3173077 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem3173076) (@lem3173075 x)). Qed.
Lemma lem3173078 (x : real) : (real_inv x) = (real_inv x).
Proof. exact (eq_refl (real_inv x)). Qed.
Lemma lem3173079 (x : real) : ((term7 x) = (real_inv x)) = ((real_inv x) = (real_inv x)).
Proof. exact (MK_COMB (@lem3173077 x) (@lem3173078 x)). Qed.
Lemma lem3173081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3173082 (x : real) : (x = x) = True.
Proof. exact (@lem3173081 real x). Qed.
Lemma lem3173083 (x : real) : ((real_inv x) = (real_inv x)) = True.
Proof. exact (@lem3173082 (real_inv x)). Qed.
Lemma lem3173084 (x : real) : ((term7 x) = (real_inv x)) = True.
Proof. exact (TRANS (@lem3173079 x) (@lem3173083 x)). Qed.
Lemma lem3173085 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem3173084 x)). Qed.
Lemma lem3173086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3173087 : term14 = term15.
Proof. exact (MK_COMB (@lem3173086) (@lem3173085)). Qed.
Lemma lem3173089 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3173090 (t : Prop) : (term17 t) = t.
Proof. exact (@lem3173089 real t). Qed.
Lemma lem3173091 : term15 = True.
Proof. exact (@lem3173090 True). Qed.
Lemma lem3173092 : term14 = True.
Proof. exact (TRANS (@lem3173087) (@lem3173091)). Qed.
Lemma lem3173093 : True = term14.
Proof. exact (SYM (@lem3173092)). Qed.
Lemma lem3173094 : term14.
Proof. exact (EQ_MP (@lem3173093) (@lem0)). Qed.
