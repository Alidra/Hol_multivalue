Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_0_term_abbrevs.
Require Import REAL_ZPOW_NUM_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3169310 (x : real) : term0 x.
Proof. exact (@lem3169304 x). Qed.
Lemma lem3169311 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3169312 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3169311 x) (@lem3169310 x)). Qed.
Lemma lem3169313 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem3169312 x n). Qed.
Lemma lem3169314 (x : real) (n : nat) : (term2 x n) = ((term3 x n) = (real_pow x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem3169323 (x : real) (n : nat) : (term3 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3169314 x n) (@lem3169313 x n)). Qed.
Lemma lem3169324 (x : real) : (term4 x) = (term5 x).
Proof. exact (@lem3169323 x (NUMERAL 0)). Qed.
Lemma lem3169326 (x : real) : (term5 x) = term6.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem3169327 (x : real) : (term4 x) = term6.
Proof. exact (TRANS (@lem3169324 x) (@lem3169326 x)). Qed.
Lemma lem3169328 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3169329 (x : real) : (term7 x) = term8.
Proof. exact (MK_COMB (@lem3169328) (@lem3169327 x)). Qed.
Lemma lem3169330 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem3169331 (x : real) : ((term4 x) = term6) = (term6 = term6).
Proof. exact (MK_COMB (@lem3169329 x) (@lem3169330)). Qed.
Lemma lem3169333 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3169334 (x : real) : (x = x) = True.
Proof. exact (@lem3169333 real x). Qed.
Lemma lem3169335 : (term6 = term6) = True.
Proof. exact (@lem3169334 term6). Qed.
Lemma lem3169336 (x : real) : ((term4 x) = term6) = True.
Proof. exact (TRANS (@lem3169331 x) (@lem3169335)). Qed.
Lemma lem3169337 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem3169336 x)). Qed.
Lemma lem3169338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3169339 : term11 = term12.
Proof. exact (MK_COMB (@lem3169338) (@lem3169337)). Qed.
Lemma lem3169341 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3169342 (t : Prop) : (term14 t) = t.
Proof. exact (@lem3169341 real t). Qed.
Lemma lem3169343 : term12 = True.
Proof. exact (@lem3169342 True). Qed.
Lemma lem3169344 : term11 = True.
Proof. exact (TRANS (@lem3169339) (@lem3169343)). Qed.
Lemma lem3169345 : True = term11.
Proof. exact (SYM (@lem3169344)). Qed.
Lemma lem3169346 : term11.
Proof. exact (EQ_MP (@lem3169345) (@lem0)). Qed.
