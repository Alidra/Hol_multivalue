Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_POW_2_term_abbrevs.
Require Import REAL_LE_SQUARE_spec.
Require Import REAL_POW_2_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1646032 (x : real) : term0 x.
Proof. exact (@lem1382902 x). Qed.
Lemma lem1646033 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1646034 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1646033 x) (@lem1646032 x)). Qed.
Lemma lem1646035 (x : real) : (term1 x) = ((term1 x) = True).
Proof. exact (@lem7 (term1 x)). Qed.
Lemma lem1646037 (x : real) : term2 x.
Proof. exact (@lem1383497 x). Qed.
Lemma lem1646038 (x : real) : (term2 x) = ((term3 x) = (real_mul x x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1646045 (x : real) : (term3 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1646038 x) (@lem1646037 x)). Qed.
Lemma lem1646046 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1646047 (x : real) : (term5 x) = (term1 x).
Proof. exact (MK_COMB (@lem1646046) (@lem1646045 x)). Qed.
Lemma lem1646049 (x : real) : (term1 x) = True.
Proof. exact (EQ_MP (@lem1646035 x) (@lem1646034 x)). Qed.
Lemma lem1646050 (x : real) : (term5 x) = True.
Proof. exact (TRANS (@lem1646047 x) (@lem1646049 x)). Qed.
Lemma lem1646051 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1646050 x)). Qed.
Lemma lem1646052 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1646053 : term8 = term9.
Proof. exact (MK_COMB (@lem1646052) (@lem1646051)). Qed.
Lemma lem1646055 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1646056 (t : Prop) : (term11 t) = t.
Proof. exact (@lem1646055 real t). Qed.
Lemma lem1646057 : term9 = True.
Proof. exact (@lem1646056 True). Qed.
Lemma lem1646058 : term8 = True.
Proof. exact (TRANS (@lem1646053) (@lem1646057)). Qed.
Lemma lem1646059 : True = term8.
Proof. exact (SYM (@lem1646058)). Qed.
Lemma lem1646060 : term8.
Proof. exact (EQ_MP (@lem1646059) (@lem0)). Qed.
