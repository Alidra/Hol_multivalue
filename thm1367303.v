Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367303_term_abbrevs.
Require Import REAL_ADD_RINV_spec.
Require Import thm0_spec.
Require Import thm1338588_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1367259 (x : real) : term0 x.
Proof. exact (@lem1353037 x). Qed.
Lemma lem1367260 (x : real) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367262 (x : real) : term3 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1367263 (x : real) : (term3 x) = ((term4 x) = term2).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1367270 (x : real) : (term4 x) = term2.
Proof. exact (EQ_MP (@lem1367263 x) (@lem1367262 x)). Qed.
Lemma lem1367271 (m : nat) : (term5 m) = term2.
Proof. exact (@lem1367270 (real_of_num m)). Qed.
Lemma lem1367272 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367273 (m : nat) : (term6 m) = term7.
Proof. exact (MK_COMB (@lem1367272) (@lem1367271 m)). Qed.
Lemma lem1367274 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1367275 (m : nat) : ((term5 m) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1367273 m) (@lem1367274)). Qed.
Lemma lem1367277 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367278 (x : real) : (x = x) = True.
Proof. exact (@lem1367277 real x). Qed.
Lemma lem1367279 : (term2 = term2) = True.
Proof. exact (@lem1367278 term2). Qed.
Lemma lem1367280 (m : nat) : ((term5 m) = term2) = True.
Proof. exact (TRANS (@lem1367275 m) (@lem1367279)). Qed.
Lemma lem1367281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367282 (m : nat) : (term8 m) = (and True).
Proof. exact (MK_COMB (@lem1367281) (@lem1367280 m)). Qed.
Lemma lem1367286 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1367260 x) (@lem1367259 x)). Qed.
Lemma lem1367287 (m : nat) : (term9 m) = term2.
Proof. exact (@lem1367286 (real_of_num m)). Qed.
Lemma lem1367288 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367289 (m : nat) : (term10 m) = term7.
Proof. exact (MK_COMB (@lem1367288) (@lem1367287 m)). Qed.
Lemma lem1367290 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1367291 (m : nat) : ((term9 m) = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1367289 m) (@lem1367290)). Qed.
Lemma lem1367293 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367294 (x : real) : (x = x) = True.
Proof. exact (@lem1367293 real x). Qed.
Lemma lem1367295 : (term2 = term2) = True.
Proof. exact (@lem1367294 term2). Qed.
Lemma lem1367296 (m : nat) : ((term9 m) = term2) = True.
Proof. exact (TRANS (@lem1367291 m) (@lem1367295)). Qed.
Lemma lem1367297 (m : nat) : (term11 m) = (True /\ True).
Proof. exact (MK_COMB (@lem1367282 m) (@lem1367296 m)). Qed.
Lemma lem1367299 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367300 : (True /\ True) = True.
Proof. exact (@lem1367299 True). Qed.
Lemma lem1367301 (m : nat) : (term11 m) = True.
Proof. exact (TRANS (@lem1367297 m) (@lem1367300)). Qed.
Lemma lem1367302 (m : nat) : True = (term11 m).
Proof. exact (SYM (@lem1367301 m)). Qed.
Lemma lem1367303 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem1367302 m) (@lem0)). Qed.
