Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1339379_term_abbrevs.
Require Import TREAL_LE_ANTISYM_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1339284 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339285 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_le x y) = (term0 x y).
Proof. exact (@lem1339284 x y). Qed.
Lemma lem1339286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1339287 (x : prod hreal hreal) (y : prod hreal hreal) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1339286) (@lem1339285 x y)). Qed.
Lemma lem1339289 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1339290 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_le y x) = (term0 y x).
Proof. exact (@lem1339289 y x). Qed.
Lemma lem1339291 (y : prod hreal hreal) (x : prod hreal hreal) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1339287 x y) (@lem1339290 y x)). Qed.
Lemma lem1339294 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339295 (y : prod hreal hreal) (x : prod hreal hreal) : (term5 y x) = (term6 y x).
Proof. exact (MK_COMB (@lem1339294) (@lem1339291 y x)). Qed.
Lemma lem1339297 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term7 x) = (term7 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1339300 (x : prod hreal hreal) (y : prod hreal hreal) : ((term3 y x) = (treal_eq x y)) = ((term4 y x) = ((term7 x) = (term7 y))).
Proof. exact (MK_COMB (@lem1339295 y x) (@lem1339297 x y)). Qed.
Lemma lem1339303 (x : prod hreal hreal) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339300 x y)). Qed.
Lemma lem1339304 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339305 (x : prod hreal hreal) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1339304) (@lem1339303 x)). Qed.
Lemma lem1339311 (P : real -> Prop) : (term12 P) = (term13 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339312 (x : prod hreal hreal) : (term14 x) = (term15 x).
Proof. exact (@lem1339311 (term16 x)). Qed.
Lemma lem1339313 (x : prod hreal hreal) (y : prod hreal hreal) : (term17 x y) = ((term4 y x) = ((term7 x) = (term7 y))).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1339314 (x : prod hreal hreal) : (term18 x) = (term9 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1339313 x y)). Qed.
Lemma lem1339315 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339316 (x : prod hreal hreal) : (term14 x) = (term11 x).
Proof. exact (MK_COMB (@lem1339315) (@lem1339314 x)). Qed.
Lemma lem1339317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339318 (x : prod hreal hreal) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1339317) (@lem1339316 x)). Qed.
Lemma lem1339319 (x : prod hreal hreal) (y : real) : (term21 x y) = ((term22 y x) = ((term7 x) = y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1339320 (x : prod hreal hreal) : (term23 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1339319 x y)). Qed.
Lemma lem1339321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339322 (x : prod hreal hreal) : (term15 x) = (term24 x).
Proof. exact (MK_COMB (@lem1339321) (@lem1339320 x)). Qed.
Lemma lem1339323 (x : prod hreal hreal) : ((term14 x) = (term15 x)) = ((term11 x) = (term24 x)).
Proof. exact (MK_COMB (@lem1339318 x) (@lem1339322 x)). Qed.
Lemma lem1339324 (x : prod hreal hreal) : (term11 x) = (term24 x).
Proof. exact (EQ_MP (@lem1339323 x) (@lem1339312 x)). Qed.
Lemma lem1339337 (x : prod hreal hreal) : (term10 x) = (term24 x).
Proof. exact (TRANS (@lem1339305 x) (@lem1339324 x)). Qed.
Lemma lem1339338 : term25 = term26.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339337 x)). Qed.
Lemma lem1339339 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339340 : term27 = term28.
Proof. exact (MK_COMB (@lem1339339) (@lem1339338)). Qed.
Lemma lem1339346 (P : real -> Prop) : (term12 P) = (term13 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1339347 : term29 = term30.
Proof. exact (@lem1339346 term31). Qed.
Lemma lem1339348 (x : prod hreal hreal) : (term32 x) = (term24 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1339349 : term33 = term26.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1339348 x)). Qed.
Lemma lem1339350 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1339351 : term29 = term28.
Proof. exact (MK_COMB (@lem1339350) (@lem1339349)). Qed.
Lemma lem1339352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1339353 : term34 = term35.
Proof. exact (MK_COMB (@lem1339352) (@lem1339351)). Qed.
Lemma lem1339354 (x : real) : (term36 x) = (term37 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1339355 : term38 = term31.
Proof. exact (fun_ext (fun x : real => @lem1339354 x)). Qed.
Lemma lem1339356 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1339357 : term30 = term39.
Proof. exact (MK_COMB (@lem1339356) (@lem1339355)). Qed.
Lemma lem1339358 : (term29 = term30) = (term28 = term39).
Proof. exact (MK_COMB (@lem1339353) (@lem1339357)). Qed.
Lemma lem1339359 : term28 = term39.
Proof. exact (EQ_MP (@lem1339358) (@lem1339347)). Qed.
Lemma lem1339378 : term27 = term39.
Proof. exact (TRANS (@lem1339340) (@lem1339359)). Qed.
Lemma lem1339379 : term39.
Proof. exact (EQ_MP (@lem1339378) (@lem1330142)). Qed.
