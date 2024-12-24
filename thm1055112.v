Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1055112_term_abbrevs.
Require Import thm1054820_spec.
Require Import thm1055084_spec.
Lemma lem1055085 : term0 = term1.
Proof. exact (eq_refl term0). Qed.
Lemma lem1055086 : term1.
Proof. exact (EQ_MP (@lem1055085) (@lem1054820)). Qed.
Lemma lem1055087 : term2.
Proof. exact (@lem1055086 term3). Qed.
Lemma lem1055088 : term2 = term4.
Proof. exact (eq_refl term2). Qed.
Lemma lem1055089 : term4.
Proof. exact (EQ_MP (@lem1055088) (@lem1055087)). Qed.
Lemma lem1055090 (h1 : NUMRIGHT = term5) : NUMRIGHT = term5.
Proof. exact (h1). Qed.
Lemma lem1055091 (h1 : NUMRIGHT = term5) : term5 = NUMRIGHT.
Proof. exact (SYM (@lem1055090 h1)). Qed.
Lemma lem1055092 (h1 : term5 = NUMRIGHT) : term5 = NUMRIGHT.
Proof. exact (h1). Qed.
Lemma lem1055093 (h1 : term5 = NUMRIGHT) : NUMRIGHT = term5.
Proof. exact (SYM (@lem1055092 h1)). Qed.
Lemma lem1055094 : (NUMRIGHT = term5) = (term5 = NUMRIGHT).
Proof. exact (prop_ext (fun h1 : NUMRIGHT = term5 => @lem1055091 h1) (fun h1 : term5 = NUMRIGHT => @lem1055093 h1)). Qed.
Lemma lem1055097 : term5 = NUMRIGHT.
Proof. exact (EQ_MP (@lem1055094) (@lem1055084)). Qed.
Lemma lem1055098 (x : Prop) (y : nat) : (NUMSUM x y) = (NUMSUM x y).
Proof. exact (eq_refl (NUMSUM x y)). Qed.
Lemma lem1055099 (x : Prop) (y : nat) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem1055097) (@lem1055098 x y)). Qed.
Lemma lem1055100 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1055101 (x : Prop) (y : nat) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem1055100) (@lem1055099 x y)). Qed.
Lemma lem1055102 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1055103 (x : Prop) (y : nat) : ((term6 x y) = y) = ((term7 x y) = y).
Proof. exact (MK_COMB (@lem1055101 x y) (@lem1055102 y)). Qed.
Lemma lem1055104 (y : nat) (x : Prop) : (term10 y x) = (term10 y x).
Proof. exact (eq_refl (term10 y x)). Qed.
Lemma lem1055105 (x : Prop) (y : nat) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1055104 y x) (@lem1055103 x y)). Qed.
Lemma lem1055106 (x : Prop) : (term13 x) = (term14 x).
Proof. exact (fun_ext (fun y : nat => @lem1055105 x y)). Qed.
Lemma lem1055107 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1055108 (x : Prop) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1055107) (@lem1055106 x)). Qed.
Lemma lem1055109 : term17 = term18.
Proof. exact (fun_ext (fun x : Prop => @lem1055108 x)). Qed.
Lemma lem1055110 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1055111 : term4 = term19.
Proof. exact (MK_COMB (@lem1055110) (@lem1055109)). Qed.
Lemma lem1055112 : term19.
Proof. exact (EQ_MP (@lem1055111) (@lem1055089)). Qed.
