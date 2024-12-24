Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_mul_th_term_abbrevs.
Require Import EXISTS_OR_THM_spec.
Require Import EXISTS_REFL_spec.
Require Import REAL_EQ_NEG2_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import dest_int_rep_spec.
Require Import int_mul_spec.
Require Import thm0_spec.
Require Import thm1340231_spec.
Require Import thm1340396_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm2259383_spec.
Require Import thm2267613_spec.
Require Import thm2267742_spec.
Require Import thm7_spec.
Lemma lem2286310 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem2286311 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem2286310 A x a h1)). Qed.
Lemma lem2286312 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem2286313 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem2286312 A a x h1)). Qed.
Lemma lem2286314 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem2286311 A x a h1) (fun h1 : a = x => @lem2286313 A a x h1)). Qed.
Lemma lem2286315 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem2286314 A a x)). Qed.
Lemma lem2286316 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2286317 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem2286316 A) (@lem2286315 A a)). Qed.
Lemma lem2286318 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem2286317 A a)). Qed.
Lemma lem2286319 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2286320 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem2286319 A) (@lem2286318 A)). Qed.
Lemma lem2286321 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem2286320 A) (@lem4363 A)). Qed.
Lemma lem2286322 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem2286321 A a). Qed.
Lemma lem2286323 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem2286324 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem2286323 A a) (@lem2286322 A a)). Qed.
Lemma lem2286325 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem2286327 (m : nat) : term9 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem2286328 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem2286329 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem2286328 m) (@lem2286327 m)). Qed.
Lemma lem2286330 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem2286329 m n). Qed.
Lemma lem2286331 (m : nat) (n : nat) : (term11 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem2286333 (x : real) : term12 x.
Proof. exact (@lem1525370 x). Qed.
Lemma lem2286334 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2286335 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem2286334 x) (@lem2286333 x)). Qed.
Lemma lem2286336 (x : real) (y : real) : term14 x y.
Proof. exact (@lem2286335 x y). Qed.
Lemma lem2286337 (x : real) (y : real) : (term14 x y) = (((real_neg x) = (real_neg y)) = (x = y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem2286339 (m : nat) : term15 m.
Proof. exact (@lem1340396 m). Qed.
Lemma lem2286340 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem2286341 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem2286340 m) (@lem2286339 m)). Qed.
Lemma lem2286342 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem2286341 m n). Qed.
Lemma lem2286343 (m : nat) (n : nat) : (term17 m n) = ((term18 m n) = (term19 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem2286345 (x : real) : term20 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem2286346 (x : real) : (term20 x) = ((term21 x) = x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem2286348 (x : real) : term22 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem2286349 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem2286350 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem2286349 x) (@lem2286348 x)). Qed.
Lemma lem2286351 (x : real) (y : real) : term24 x y.
Proof. exact (@lem2286350 x y). Qed.
Lemma lem2286352 (x : real) (y : real) : (term24 x y) = ((term25 x y) = (term26 x y)).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem2286354 (x : real) : term27 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem2286355 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem2286356 (x : real) : term28 x.
Proof. exact (EQ_MP (@lem2286355 x) (@lem2286354 x)). Qed.
Lemma lem2286357 (x : real) (y : real) : term29 x y.
Proof. exact (@lem2286356 x y). Qed.
Lemma lem2286358 (x : real) (y : real) : (term29 x y) = ((term30 x y) = (term26 x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem2286360 (y : int) : term31 y.
Proof. exact (@lem2267790 y). Qed.
Lemma lem2286361 (y : int) : (term31 y) = (term32 y).
Proof. exact (eq_refl (term31 y)). Qed.
Lemma lem2286362 (y : int) : term32 y.
Proof. exact (EQ_MP (@lem2286361 y) (@lem2286360 y)). Qed.
Lemma lem2286363 (y : int) (n : nat) (h1 : term33 y n) : term33 y n.
Proof. exact (h1). Qed.
Lemma lem2286364 (x : int) : term31 x.
Proof. exact (@lem2267790 x). Qed.
Lemma lem2286365 (x : int) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2286366 (x : int) : term32 x.
Proof. exact (EQ_MP (@lem2286365 x) (@lem2286364 x)). Qed.
Lemma lem2286367 (x : int) (m : nat) (h1 : term33 x m) : term33 x m.
Proof. exact (h1). Qed.
Lemma lem2286368 (r : real) (h1 : (integer r) = ((term34 r) = r)) : (integer r) = ((term34 r) = r).
Proof. exact (h1). Qed.
Lemma lem2286369 (r : real) (h1 : (integer r) = ((term34 r) = r)) : ((term34 r) = r) = (integer r).
Proof. exact (SYM (@lem2286368 r h1)). Qed.
Lemma lem2286370 (r : real) (h1 : ((term34 r) = r) = (integer r)) : ((term34 r) = r) = (integer r).
Proof. exact (h1). Qed.
Lemma lem2286371 (r : real) (h1 : ((term34 r) = r) = (integer r)) : (integer r) = ((term34 r) = r).
Proof. exact (SYM (@lem2286370 r h1)). Qed.
Lemma lem2286372 (r : real) : ((integer r) = ((term34 r) = r)) = (((term34 r) = r) = (integer r)).
Proof. exact (prop_ext (fun h1 : (integer r) = ((term34 r) = r) => @lem2286369 r h1) (fun h1 : ((term34 r) = r) = (integer r) => @lem2286371 r h1)). Qed.
Lemma lem2286374 (x : int) : term35 x.
Proof. exact (@lem2286307 x). Qed.
Lemma lem2286375 (x : int) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem2286376 (x : int) : term36 x.
Proof. exact (EQ_MP (@lem2286375 x) (@lem2286374 x)). Qed.
Lemma lem2286377 (x : int) (y : int) : term37 x y.
Proof. exact (@lem2286376 x y). Qed.
Lemma lem2286378 (x : int) (y : int) : (term37 x y) = ((int_mul x y) = (term38 x y)).
Proof. exact (eq_refl (term37 x y)). Qed.
Lemma lem2286383 (x : int) (y : int) : (int_mul x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2286378 x y) (@lem2286377 x y)). Qed.
Lemma lem2286384 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2286385 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem2286384) (@lem2286383 x y)). Qed.
Lemma lem2286386 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286387 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem2286386) (@lem2286385 x y)). Qed.
Lemma lem2286388 (x : int) (y : int) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem2286389 (x : int) (y : int) : ((term39 x y) = (term43 x y)) = ((term40 x y) = (term43 x y)).
Proof. exact (MK_COMB (@lem2286387 x y) (@lem2286388 x y)). Qed.
Lemma lem2286391 (r : real) : ((term34 r) = r) = (integer r).
Proof. exact (EQ_MP (@lem2286372 r) (@lem2267742 r)). Qed.
Lemma lem2286392 (x : int) (y : int) : ((term40 x y) = (term43 x y)) = (term44 x y).
Proof. exact (@lem2286391 (term43 x y)). Qed.
Lemma lem2286394 (x : real) : (integer x) = (term45 x).
Proof. exact (EQ_MP (@lem2259383 x) (@lem2267613 x)). Qed.
Lemma lem2286395 (x : int) (y : int) : (term44 x y) = (term46 x y).
Proof. exact (@lem2286394 (term43 x y)). Qed.
Lemma lem2286406 (x : int) (y : int) : ((term40 x y) = (term43 x y)) = (term46 x y).
Proof. exact (TRANS (@lem2286392 x y) (@lem2286395 x y)). Qed.
Lemma lem2286407 (x : int) (y : int) : ((term39 x y) = (term43 x y)) = (term46 x y).
Proof. exact (TRANS (@lem2286389 x y) (@lem2286406 x y)). Qed.
Lemma lem2286408 (x : int) (y : int) : (term46 x y) = ((term39 x y) = (term43 x y)).
Proof. exact (SYM (@lem2286407 x y)). Qed.
Lemma lem2286415 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2286416 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem2286417 {A : Type'} (P : A -> Prop) : term48 A P.
Proof. exact (EQ_MP (@lem2286416 A P) (@lem2286415 A P)). Qed.
Lemma lem2286418 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term49 A P Q.
Proof. exact (@lem2286417 A P Q). Qed.
Lemma lem2286419 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = ((term50 A P Q) = (term51 A P Q)).
Proof. exact (eq_refl (term49 A P Q)). Qed.
Lemma lem2286434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem2286419 A P Q) (@lem2286418 A P Q)). Qed.
Lemma lem2286435 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem2286434 nat P Q). Qed.
Lemma lem2286436 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (@lem2286435 (term56 x y) (term57 x y)). Qed.
Lemma lem2286437 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286439 (x : int) (y : int) (n : nat) : (term59 x y n) = (term60 x y n).
Proof. exact (MK_COMB (@lem2286438) (@lem2286437 x y n)). Qed.
Lemma lem2286440 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286441 (x : int) (y : int) (n : nat) : (term63 x y n) = (term64 x y n).
Proof. exact (MK_COMB (@lem2286439 x y n) (@lem2286440 x y n)). Qed.
Lemma lem2286442 (x : int) (y : int) : (term65 x y) = (term66 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286441 x y n)). Qed.
Lemma lem2286443 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286444 (x : int) (y : int) : (term54 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem2286443) (@lem2286442 x y)). Qed.
Lemma lem2286445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2286446 (x : int) (y : int) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem2286445) (@lem2286444 x y)). Qed.
Lemma lem2286447 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286448 (x : int) (y : int) : (term69 x y) = (term56 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286447 x y n)). Qed.
Lemma lem2286449 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286450 (x : int) (y : int) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem2286449) (@lem2286448 x y)). Qed.
Lemma lem2286451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286452 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem2286451) (@lem2286450 x y)). Qed.
Lemma lem2286453 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286454 (x : int) (y : int) : (term74 x y) = (term57 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286453 x y n)). Qed.
Lemma lem2286455 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286456 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2286455) (@lem2286454 x y)). Qed.
Lemma lem2286457 (x : int) (y : int) : (term55 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem2286452 x y) (@lem2286456 x y)). Qed.
Lemma lem2286458 (x : int) (y : int) : ((term54 x y) = (term55 x y)) = ((term46 x y) = (term77 x y)).
Proof. exact (MK_COMB (@lem2286446 x y) (@lem2286457 x y)). Qed.
Lemma lem2286459 (x : int) (y : int) : (term46 x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2286458 x y) (@lem2286436 x y)). Qed.
Lemma lem2286484 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2286485 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286486 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term78 x) = (term79 m).
Proof. exact (MK_COMB (@lem2286485) (@lem2286484 x m h1)). Qed.
Lemma lem2286488 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2286489 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term43 x y) = (term18 m n).
Proof. exact (MK_COMB (@lem2286486 x m h1) (@lem2286488 y n h2)). Qed.
Lemma lem2286490 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286491 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term80 x y) = (term81 m n).
Proof. exact (MK_COMB (@lem2286490) (@lem2286489 x m y n h1 h2)). Qed.
Lemma lem2286492 (_28732 : nat) : (real_of_num _28732) = (real_of_num _28732).
Proof. exact (eq_refl (real_of_num _28732)). Qed.
Lemma lem2286493 (_28732 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term43 x y) = (real_of_num _28732)) = ((term18 m n) = (real_of_num _28732)).
Proof. exact (MK_COMB (@lem2286491 x m y n h1 h2) (@lem2286492 _28732)). Qed.
Lemma lem2286498 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term56 x y) = (term82 m n).
Proof. exact (fun_ext (fun _28732 : nat => @lem2286493 _28732 x m y n h1 h2)). Qed.
Lemma lem2286499 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286500 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term83 m n).
Proof. exact (MK_COMB (@lem2286499) (@lem2286498 x m y n h1 h2)). Qed.
Lemma lem2286505 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286506 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term73 x y) = (term84 m n).
Proof. exact (MK_COMB (@lem2286505) (@lem2286500 x m y n h1 h2)). Qed.
Lemma lem2286529 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2286530 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286531 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term78 x) = (term79 m).
Proof. exact (MK_COMB (@lem2286530) (@lem2286529 x m h1)). Qed.
Lemma lem2286533 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2286534 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term43 x y) = (term18 m n).
Proof. exact (MK_COMB (@lem2286531 x m h1) (@lem2286533 y n h2)). Qed.
Lemma lem2286535 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286536 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term80 x y) = (term81 m n).
Proof. exact (MK_COMB (@lem2286535) (@lem2286534 x m y n h1 h2)). Qed.
Lemma lem2286537 (_28733 : nat) : (term62 _28733) = (term62 _28733).
Proof. exact (eq_refl (term62 _28733)). Qed.
Lemma lem2286538 (_28733 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term43 x y) = (term62 _28733)) = ((term18 m n) = (term62 _28733)).
Proof. exact (MK_COMB (@lem2286536 x m y n h1 h2) (@lem2286537 _28733)). Qed.
Lemma lem2286543 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term57 x y) = (term85 m n).
Proof. exact (fun_ext (fun _28733 : nat => @lem2286538 _28733 x m y n h1 h2)). Qed.
Lemma lem2286544 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286545 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term76 x y) = (term86 m n).
Proof. exact (MK_COMB (@lem2286544) (@lem2286543 x m y n h1 h2)). Qed.
Lemma lem2286550 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term77 x y) = (term87 m n).
Proof. exact (MK_COMB (@lem2286506 x m y n h1 h2) (@lem2286545 x m y n h1 h2)). Qed.
Lemma lem2286553 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term46 x y) = (term87 m n).
Proof. exact (TRANS (@lem2286459 x y) (@lem2286550 x m y n h1 h2)). Qed.
Lemma lem2286554 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : (term87 m n) = (term46 x y).
Proof. exact (SYM (@lem2286553 x m y n h1 h2)). Qed.
Lemma lem2286555 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2286556 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem2286557 {A : Type'} (P : A -> Prop) : term48 A P.
Proof. exact (EQ_MP (@lem2286556 A P) (@lem2286555 A P)). Qed.
Lemma lem2286558 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term49 A P Q.
Proof. exact (@lem2286557 A P Q). Qed.
Lemma lem2286559 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = ((term50 A P Q) = (term51 A P Q)).
Proof. exact (eq_refl (term49 A P Q)). Qed.
Lemma lem2286574 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem2286559 A P Q) (@lem2286558 A P Q)). Qed.
Lemma lem2286575 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem2286574 nat P Q). Qed.
Lemma lem2286576 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (@lem2286575 (term56 x y) (term57 x y)). Qed.
Lemma lem2286577 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286579 (x : int) (y : int) (n : nat) : (term59 x y n) = (term60 x y n).
Proof. exact (MK_COMB (@lem2286578) (@lem2286577 x y n)). Qed.
Lemma lem2286580 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286581 (x : int) (y : int) (n : nat) : (term63 x y n) = (term64 x y n).
Proof. exact (MK_COMB (@lem2286579 x y n) (@lem2286580 x y n)). Qed.
Lemma lem2286582 (x : int) (y : int) : (term65 x y) = (term66 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286581 x y n)). Qed.
Lemma lem2286583 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286584 (x : int) (y : int) : (term54 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem2286583) (@lem2286582 x y)). Qed.
Lemma lem2286585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2286586 (x : int) (y : int) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem2286585) (@lem2286584 x y)). Qed.
Lemma lem2286587 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286588 (x : int) (y : int) : (term69 x y) = (term56 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286587 x y n)). Qed.
Lemma lem2286589 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286590 (x : int) (y : int) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem2286589) (@lem2286588 x y)). Qed.
Lemma lem2286591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286592 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem2286591) (@lem2286590 x y)). Qed.
Lemma lem2286593 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286594 (x : int) (y : int) : (term74 x y) = (term57 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286593 x y n)). Qed.
Lemma lem2286595 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286596 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2286595) (@lem2286594 x y)). Qed.
Lemma lem2286597 (x : int) (y : int) : (term55 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem2286592 x y) (@lem2286596 x y)). Qed.
Lemma lem2286598 (x : int) (y : int) : ((term54 x y) = (term55 x y)) = ((term46 x y) = (term77 x y)).
Proof. exact (MK_COMB (@lem2286586 x y) (@lem2286597 x y)). Qed.
Lemma lem2286599 (x : int) (y : int) : (term46 x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2286598 x y) (@lem2286576 x y)). Qed.
Lemma lem2286624 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2286625 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286626 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term78 x) = (term79 m).
Proof. exact (MK_COMB (@lem2286625) (@lem2286624 x m h1)). Qed.
Lemma lem2286628 (y : int) (n : nat) (h1 : (real_of_int y) = (term62 n)) : (real_of_int y) = (term62 n).
Proof. exact (h1). Qed.
Lemma lem2286629 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term43 x y) = (term88 m n).
Proof. exact (MK_COMB (@lem2286626 x m h1) (@lem2286628 y n h2)). Qed.
Lemma lem2286630 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286631 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term80 x y) = (term89 m n).
Proof. exact (MK_COMB (@lem2286630) (@lem2286629 x m y n h1 h2)). Qed.
Lemma lem2286632 (_28734 : nat) : (real_of_num _28734) = (real_of_num _28734).
Proof. exact (eq_refl (real_of_num _28734)). Qed.
Lemma lem2286633 (_28734 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : ((term43 x y) = (real_of_num _28734)) = ((term88 m n) = (real_of_num _28734)).
Proof. exact (MK_COMB (@lem2286631 x m y n h1 h2) (@lem2286632 _28734)). Qed.
Lemma lem2286638 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term56 x y) = (term90 m n).
Proof. exact (fun_ext (fun _28734 : nat => @lem2286633 _28734 x m y n h1 h2)). Qed.
Lemma lem2286639 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286640 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term71 x y) = (term91 m n).
Proof. exact (MK_COMB (@lem2286639) (@lem2286638 x m y n h1 h2)). Qed.
Lemma lem2286645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286646 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term73 x y) = (term92 m n).
Proof. exact (MK_COMB (@lem2286645) (@lem2286640 x m y n h1 h2)). Qed.
Lemma lem2286669 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (real_of_int x) = (real_of_num m).
Proof. exact (h1). Qed.
Lemma lem2286670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286671 (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : (term78 x) = (term79 m).
Proof. exact (MK_COMB (@lem2286670) (@lem2286669 x m h1)). Qed.
Lemma lem2286673 (y : int) (n : nat) (h1 : (real_of_int y) = (term62 n)) : (real_of_int y) = (term62 n).
Proof. exact (h1). Qed.
Lemma lem2286674 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term43 x y) = (term88 m n).
Proof. exact (MK_COMB (@lem2286671 x m h1) (@lem2286673 y n h2)). Qed.
Lemma lem2286675 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286676 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term80 x y) = (term89 m n).
Proof. exact (MK_COMB (@lem2286675) (@lem2286674 x m y n h1 h2)). Qed.
Lemma lem2286677 (_28735 : nat) : (term62 _28735) = (term62 _28735).
Proof. exact (eq_refl (term62 _28735)). Qed.
Lemma lem2286678 (_28735 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : ((term43 x y) = (term62 _28735)) = ((term88 m n) = (term62 _28735)).
Proof. exact (MK_COMB (@lem2286676 x m y n h1 h2) (@lem2286677 _28735)). Qed.
Lemma lem2286683 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term57 x y) = (term93 m n).
Proof. exact (fun_ext (fun _28735 : nat => @lem2286678 _28735 x m y n h1 h2)). Qed.
Lemma lem2286684 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286685 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term76 x y) = (term94 m n).
Proof. exact (MK_COMB (@lem2286684) (@lem2286683 x m y n h1 h2)). Qed.
Lemma lem2286690 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term77 x y) = (term95 m n).
Proof. exact (MK_COMB (@lem2286646 x m y n h1 h2) (@lem2286685 x m y n h1 h2)). Qed.
Lemma lem2286693 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term46 x y) = (term95 m n).
Proof. exact (TRANS (@lem2286599 x y) (@lem2286690 x m y n h1 h2)). Qed.
Lemma lem2286694 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : (term95 m n) = (term46 x y).
Proof. exact (SYM (@lem2286693 x m y n h1 h2)). Qed.
Lemma lem2286695 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2286696 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem2286697 {A : Type'} (P : A -> Prop) : term48 A P.
Proof. exact (EQ_MP (@lem2286696 A P) (@lem2286695 A P)). Qed.
Lemma lem2286698 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term49 A P Q.
Proof. exact (@lem2286697 A P Q). Qed.
Lemma lem2286699 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = ((term50 A P Q) = (term51 A P Q)).
Proof. exact (eq_refl (term49 A P Q)). Qed.
Lemma lem2286714 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem2286699 A P Q) (@lem2286698 A P Q)). Qed.
Lemma lem2286715 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem2286714 nat P Q). Qed.
Lemma lem2286716 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (@lem2286715 (term56 x y) (term57 x y)). Qed.
Lemma lem2286717 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286719 (x : int) (y : int) (n : nat) : (term59 x y n) = (term60 x y n).
Proof. exact (MK_COMB (@lem2286718) (@lem2286717 x y n)). Qed.
Lemma lem2286720 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286721 (x : int) (y : int) (n : nat) : (term63 x y n) = (term64 x y n).
Proof. exact (MK_COMB (@lem2286719 x y n) (@lem2286720 x y n)). Qed.
Lemma lem2286722 (x : int) (y : int) : (term65 x y) = (term66 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286721 x y n)). Qed.
Lemma lem2286723 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286724 (x : int) (y : int) : (term54 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem2286723) (@lem2286722 x y)). Qed.
Lemma lem2286725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2286726 (x : int) (y : int) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem2286725) (@lem2286724 x y)). Qed.
Lemma lem2286727 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286728 (x : int) (y : int) : (term69 x y) = (term56 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286727 x y n)). Qed.
Lemma lem2286729 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286730 (x : int) (y : int) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem2286729) (@lem2286728 x y)). Qed.
Lemma lem2286731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286732 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem2286731) (@lem2286730 x y)). Qed.
Lemma lem2286733 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286734 (x : int) (y : int) : (term74 x y) = (term57 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286733 x y n)). Qed.
Lemma lem2286735 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286736 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2286735) (@lem2286734 x y)). Qed.
Lemma lem2286737 (x : int) (y : int) : (term55 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem2286732 x y) (@lem2286736 x y)). Qed.
Lemma lem2286738 (x : int) (y : int) : ((term54 x y) = (term55 x y)) = ((term46 x y) = (term77 x y)).
Proof. exact (MK_COMB (@lem2286726 x y) (@lem2286737 x y)). Qed.
Lemma lem2286739 (x : int) (y : int) : (term46 x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2286738 x y) (@lem2286716 x y)). Qed.
Lemma lem2286764 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (real_of_int x) = (term62 m).
Proof. exact (h1). Qed.
Lemma lem2286765 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286766 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (term78 x) = (term96 m).
Proof. exact (MK_COMB (@lem2286765) (@lem2286764 x m h1)). Qed.
Lemma lem2286768 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2286769 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term43 x y) = (term97 m n).
Proof. exact (MK_COMB (@lem2286766 x m h1) (@lem2286768 y n h2)). Qed.
Lemma lem2286770 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286771 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term80 x y) = (term98 m n).
Proof. exact (MK_COMB (@lem2286770) (@lem2286769 x m y n h1 h2)). Qed.
Lemma lem2286772 (_28736 : nat) : (real_of_num _28736) = (real_of_num _28736).
Proof. exact (eq_refl (real_of_num _28736)). Qed.
Lemma lem2286773 (_28736 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term43 x y) = (real_of_num _28736)) = ((term97 m n) = (real_of_num _28736)).
Proof. exact (MK_COMB (@lem2286771 x m y n h1 h2) (@lem2286772 _28736)). Qed.
Lemma lem2286778 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term56 x y) = (term99 m n).
Proof. exact (fun_ext (fun _28736 : nat => @lem2286773 _28736 x m y n h1 h2)). Qed.
Lemma lem2286779 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286780 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term71 x y) = (term100 m n).
Proof. exact (MK_COMB (@lem2286779) (@lem2286778 x m y n h1 h2)). Qed.
Lemma lem2286785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286786 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term73 x y) = (term101 m n).
Proof. exact (MK_COMB (@lem2286785) (@lem2286780 x m y n h1 h2)). Qed.
Lemma lem2286809 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (real_of_int x) = (term62 m).
Proof. exact (h1). Qed.
Lemma lem2286810 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286811 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (term78 x) = (term96 m).
Proof. exact (MK_COMB (@lem2286810) (@lem2286809 x m h1)). Qed.
Lemma lem2286813 (y : int) (n : nat) (h1 : (real_of_int y) = (real_of_num n)) : (real_of_int y) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem2286814 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term43 x y) = (term97 m n).
Proof. exact (MK_COMB (@lem2286811 x m h1) (@lem2286813 y n h2)). Qed.
Lemma lem2286815 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286816 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term80 x y) = (term98 m n).
Proof. exact (MK_COMB (@lem2286815) (@lem2286814 x m y n h1 h2)). Qed.
Lemma lem2286817 (_28737 : nat) : (term62 _28737) = (term62 _28737).
Proof. exact (eq_refl (term62 _28737)). Qed.
Lemma lem2286818 (_28737 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : ((term43 x y) = (term62 _28737)) = ((term97 m n) = (term62 _28737)).
Proof. exact (MK_COMB (@lem2286816 x m y n h1 h2) (@lem2286817 _28737)). Qed.
Lemma lem2286823 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term57 x y) = (term102 m n).
Proof. exact (fun_ext (fun _28737 : nat => @lem2286818 _28737 x m y n h1 h2)). Qed.
Lemma lem2286824 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286825 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term76 x y) = (term103 m n).
Proof. exact (MK_COMB (@lem2286824) (@lem2286823 x m y n h1 h2)). Qed.
Lemma lem2286830 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term77 x y) = (term104 m n).
Proof. exact (MK_COMB (@lem2286786 x m y n h1 h2) (@lem2286825 x m y n h1 h2)). Qed.
Lemma lem2286833 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term46 x y) = (term104 m n).
Proof. exact (TRANS (@lem2286739 x y) (@lem2286830 x m y n h1 h2)). Qed.
Lemma lem2286834 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : (term104 m n) = (term46 x y).
Proof. exact (SYM (@lem2286833 x m y n h1 h2)). Qed.
Lemma lem2286835 {A : Type'} (P : A -> Prop) : term47 A P.
Proof. exact (@lem5418 A P). Qed.
Lemma lem2286836 {A : Type'} (P : A -> Prop) : (term47 A P) = (term48 A P).
Proof. exact (eq_refl (term47 A P)). Qed.
Lemma lem2286837 {A : Type'} (P : A -> Prop) : term48 A P.
Proof. exact (EQ_MP (@lem2286836 A P) (@lem2286835 A P)). Qed.
Lemma lem2286838 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term49 A P Q.
Proof. exact (@lem2286837 A P Q). Qed.
Lemma lem2286839 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = ((term50 A P Q) = (term51 A P Q)).
Proof. exact (eq_refl (term49 A P Q)). Qed.
Lemma lem2286854 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem2286839 A P Q) (@lem2286838 A P Q)). Qed.
Lemma lem2286855 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem2286854 nat P Q). Qed.
Lemma lem2286856 (x : int) (y : int) : (term54 x y) = (term55 x y).
Proof. exact (@lem2286855 (term56 x y) (term57 x y)). Qed.
Lemma lem2286857 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286859 (x : int) (y : int) (n : nat) : (term59 x y n) = (term60 x y n).
Proof. exact (MK_COMB (@lem2286858) (@lem2286857 x y n)). Qed.
Lemma lem2286860 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286861 (x : int) (y : int) (n : nat) : (term63 x y n) = (term64 x y n).
Proof. exact (MK_COMB (@lem2286859 x y n) (@lem2286860 x y n)). Qed.
Lemma lem2286862 (x : int) (y : int) : (term65 x y) = (term66 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286861 x y n)). Qed.
Lemma lem2286863 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286864 (x : int) (y : int) : (term54 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem2286863) (@lem2286862 x y)). Qed.
Lemma lem2286865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2286866 (x : int) (y : int) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem2286865) (@lem2286864 x y)). Qed.
Lemma lem2286867 (x : int) (y : int) (n : nat) : (term58 x y n) = ((term43 x y) = (real_of_num n)).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem2286868 (x : int) (y : int) : (term69 x y) = (term56 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286867 x y n)). Qed.
Lemma lem2286869 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286870 (x : int) (y : int) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem2286869) (@lem2286868 x y)). Qed.
Lemma lem2286871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286872 (x : int) (y : int) : (term72 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem2286871) (@lem2286870 x y)). Qed.
Lemma lem2286873 (x : int) (y : int) (n : nat) : (term61 x y n) = ((term43 x y) = (term62 n)).
Proof. exact (eq_refl (term61 x y n)). Qed.
Lemma lem2286874 (x : int) (y : int) : (term74 x y) = (term57 x y).
Proof. exact (fun_ext (fun n : nat => @lem2286873 x y n)). Qed.
Lemma lem2286875 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286876 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2286875) (@lem2286874 x y)). Qed.
Lemma lem2286877 (x : int) (y : int) : (term55 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem2286872 x y) (@lem2286876 x y)). Qed.
Lemma lem2286878 (x : int) (y : int) : ((term54 x y) = (term55 x y)) = ((term46 x y) = (term77 x y)).
Proof. exact (MK_COMB (@lem2286866 x y) (@lem2286877 x y)). Qed.
Lemma lem2286879 (x : int) (y : int) : (term46 x y) = (term77 x y).
Proof. exact (EQ_MP (@lem2286878 x y) (@lem2286856 x y)). Qed.
Lemma lem2286904 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (real_of_int x) = (term62 m).
Proof. exact (h1). Qed.
Lemma lem2286905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286906 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (term78 x) = (term96 m).
Proof. exact (MK_COMB (@lem2286905) (@lem2286904 x m h1)). Qed.
Lemma lem2286908 (y : int) (n : nat) (h1 : (real_of_int y) = (term62 n)) : (real_of_int y) = (term62 n).
Proof. exact (h1). Qed.
Lemma lem2286909 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term43 x y) = (term105 m n).
Proof. exact (MK_COMB (@lem2286906 x m h1) (@lem2286908 y n h2)). Qed.
Lemma lem2286910 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286911 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term80 x y) = (term106 m n).
Proof. exact (MK_COMB (@lem2286910) (@lem2286909 x m y n h1 h2)). Qed.
Lemma lem2286912 (_28738 : nat) : (real_of_num _28738) = (real_of_num _28738).
Proof. exact (eq_refl (real_of_num _28738)). Qed.
Lemma lem2286913 (_28738 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : ((term43 x y) = (real_of_num _28738)) = ((term105 m n) = (real_of_num _28738)).
Proof. exact (MK_COMB (@lem2286911 x m y n h1 h2) (@lem2286912 _28738)). Qed.
Lemma lem2286918 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term56 x y) = (term107 m n).
Proof. exact (fun_ext (fun _28738 : nat => @lem2286913 _28738 x m y n h1 h2)). Qed.
Lemma lem2286919 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286920 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term71 x y) = (term108 m n).
Proof. exact (MK_COMB (@lem2286919) (@lem2286918 x m y n h1 h2)). Qed.
Lemma lem2286925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286926 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term73 x y) = (term109 m n).
Proof. exact (MK_COMB (@lem2286925) (@lem2286920 x m y n h1 h2)). Qed.
Lemma lem2286949 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (real_of_int x) = (term62 m).
Proof. exact (h1). Qed.
Lemma lem2286950 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2286951 (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : (term78 x) = (term96 m).
Proof. exact (MK_COMB (@lem2286950) (@lem2286949 x m h1)). Qed.
Lemma lem2286953 (y : int) (n : nat) (h1 : (real_of_int y) = (term62 n)) : (real_of_int y) = (term62 n).
Proof. exact (h1). Qed.
Lemma lem2286954 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term43 x y) = (term105 m n).
Proof. exact (MK_COMB (@lem2286951 x m h1) (@lem2286953 y n h2)). Qed.
Lemma lem2286955 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286956 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term80 x y) = (term106 m n).
Proof. exact (MK_COMB (@lem2286955) (@lem2286954 x m y n h1 h2)). Qed.
Lemma lem2286957 (_28739 : nat) : (term62 _28739) = (term62 _28739).
Proof. exact (eq_refl (term62 _28739)). Qed.
Lemma lem2286958 (_28739 : nat) (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : ((term43 x y) = (term62 _28739)) = ((term105 m n) = (term62 _28739)).
Proof. exact (MK_COMB (@lem2286956 x m y n h1 h2) (@lem2286957 _28739)). Qed.
Lemma lem2286963 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term57 x y) = (term110 m n).
Proof. exact (fun_ext (fun _28739 : nat => @lem2286958 _28739 x m y n h1 h2)). Qed.
Lemma lem2286964 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286965 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term76 x y) = (term111 m n).
Proof. exact (MK_COMB (@lem2286964) (@lem2286963 x m y n h1 h2)). Qed.
Lemma lem2286970 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term77 x y) = (term112 m n).
Proof. exact (MK_COMB (@lem2286926 x m y n h1 h2) (@lem2286965 x m y n h1 h2)). Qed.
Lemma lem2286973 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term46 x y) = (term112 m n).
Proof. exact (TRANS (@lem2286879 x y) (@lem2286970 x m y n h1 h2)). Qed.
Lemma lem2286974 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : (term112 m n) = (term46 x y).
Proof. exact (SYM (@lem2286973 x m y n h1 h2)). Qed.
Lemma lem2286984 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2286985 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2286986 (m : nat) (n : nat) : (term81 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem2286985) (@lem2286984 m n)). Qed.
Lemma lem2286987 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2286988 (m : nat) (n : nat) (n' : nat) : ((term18 m n) = (real_of_num n')) = ((term19 m n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2286986 m n) (@lem2286987 n')). Qed.
Lemma lem2286991 (m : nat) (n : nat) : (term82 m n) = (term114 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2286988 m n n')). Qed.
Lemma lem2286992 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2286993 (m : nat) (n : nat) : (term83 m n) = (term115 m n).
Proof. exact (MK_COMB (@lem2286992) (@lem2286991 m n)). Qed.
Lemma lem2286998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2286999 (m : nat) (n : nat) : (term84 m n) = (term116 m n).
Proof. exact (MK_COMB (@lem2286998) (@lem2286993 m n)). Qed.
Lemma lem2287007 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287008 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287009 (m : nat) (n : nat) : (term81 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem2287008) (@lem2287007 m n)). Qed.
Lemma lem2287010 (n' : nat) : (term62 n') = (term62 n').
Proof. exact (eq_refl (term62 n')). Qed.
Lemma lem2287011 (m : nat) (n : nat) (n' : nat) : ((term18 m n) = (term62 n')) = ((term19 m n) = (term62 n')).
Proof. exact (MK_COMB (@lem2287009 m n) (@lem2287010 n')). Qed.
Lemma lem2287014 (m : nat) (n : nat) : (term85 m n) = (term117 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287011 m n n')). Qed.
Lemma lem2287015 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287016 (m : nat) (n : nat) : (term86 m n) = (term118 m n).
Proof. exact (MK_COMB (@lem2287015) (@lem2287014 m n)). Qed.
Lemma lem2287021 (m : nat) (n : nat) : (term87 m n) = (term119 m n).
Proof. exact (MK_COMB (@lem2286999 m n) (@lem2287016 m n)). Qed.
Lemma lem2287024 (m : nat) (n : nat) : (term119 m n) = (term87 m n).
Proof. exact (SYM (@lem2287021 m n)). Qed.
Lemma lem2287034 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286352 x y) (@lem2286351 x y)). Qed.
Lemma lem2287035 (m : nat) (n : nat) : (term88 m n) = (term120 m n).
Proof. exact (@lem2287034 (real_of_num m) (real_of_num n)). Qed.
Lemma lem2287037 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287038 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287039 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2287038) (@lem2287037 m n)). Qed.
Lemma lem2287040 (m : nat) (n : nat) : (term88 m n) = (term121 m n).
Proof. exact (TRANS (@lem2287035 m n) (@lem2287039 m n)). Qed.
Lemma lem2287041 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287042 (m : nat) (n : nat) : (term89 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem2287041) (@lem2287040 m n)). Qed.
Lemma lem2287043 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2287044 (m : nat) (n : nat) (n' : nat) : ((term88 m n) = (real_of_num n')) = ((term121 m n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2287042 m n) (@lem2287043 n')). Qed.
Lemma lem2287047 (m : nat) (n : nat) : (term90 m n) = (term123 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287044 m n n')). Qed.
Lemma lem2287048 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287049 (m : nat) (n : nat) : (term91 m n) = (term124 m n).
Proof. exact (MK_COMB (@lem2287048) (@lem2287047 m n)). Qed.
Lemma lem2287054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2287055 (m : nat) (n : nat) : (term92 m n) = (term125 m n).
Proof. exact (MK_COMB (@lem2287054) (@lem2287049 m n)). Qed.
Lemma lem2287063 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286352 x y) (@lem2286351 x y)). Qed.
Lemma lem2287064 (m : nat) (n : nat) : (term88 m n) = (term120 m n).
Proof. exact (@lem2287063 (real_of_num m) (real_of_num n)). Qed.
Lemma lem2287066 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287067 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287068 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2287067) (@lem2287066 m n)). Qed.
Lemma lem2287069 (m : nat) (n : nat) : (term88 m n) = (term121 m n).
Proof. exact (TRANS (@lem2287064 m n) (@lem2287068 m n)). Qed.
Lemma lem2287070 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287071 (m : nat) (n : nat) : (term89 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem2287070) (@lem2287069 m n)). Qed.
Lemma lem2287072 (n' : nat) : (term62 n') = (term62 n').
Proof. exact (eq_refl (term62 n')). Qed.
Lemma lem2287073 (m : nat) (n : nat) (n' : nat) : ((term88 m n) = (term62 n')) = ((term121 m n) = (term62 n')).
Proof. exact (MK_COMB (@lem2287071 m n) (@lem2287072 n')). Qed.
Lemma lem2287076 (m : nat) (n : nat) : (term93 m n) = (term126 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287073 m n n')). Qed.
Lemma lem2287077 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287078 (m : nat) (n : nat) : (term94 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem2287077) (@lem2287076 m n)). Qed.
Lemma lem2287083 (m : nat) (n : nat) : (term95 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem2287055 m n) (@lem2287078 m n)). Qed.
Lemma lem2287086 (m : nat) (n : nat) : (term128 m n) = (term95 m n).
Proof. exact (SYM (@lem2287083 m n)). Qed.
Lemma lem2287096 (x : real) (y : real) : (term30 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286358 x y) (@lem2286357 x y)). Qed.
Lemma lem2287097 (m : nat) (n : nat) : (term97 m n) = (term120 m n).
Proof. exact (@lem2287096 (real_of_num m) (real_of_num n)). Qed.
Lemma lem2287099 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287100 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287101 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2287100) (@lem2287099 m n)). Qed.
Lemma lem2287102 (m : nat) (n : nat) : (term97 m n) = (term121 m n).
Proof. exact (TRANS (@lem2287097 m n) (@lem2287101 m n)). Qed.
Lemma lem2287103 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287104 (m : nat) (n : nat) : (term98 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem2287103) (@lem2287102 m n)). Qed.
Lemma lem2287105 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2287106 (m : nat) (n : nat) (n' : nat) : ((term97 m n) = (real_of_num n')) = ((term121 m n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2287104 m n) (@lem2287105 n')). Qed.
Lemma lem2287109 (m : nat) (n : nat) : (term99 m n) = (term123 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287106 m n n')). Qed.
Lemma lem2287110 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287111 (m : nat) (n : nat) : (term100 m n) = (term124 m n).
Proof. exact (MK_COMB (@lem2287110) (@lem2287109 m n)). Qed.
Lemma lem2287116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2287117 (m : nat) (n : nat) : (term101 m n) = (term125 m n).
Proof. exact (MK_COMB (@lem2287116) (@lem2287111 m n)). Qed.
Lemma lem2287125 (x : real) (y : real) : (term30 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286358 x y) (@lem2286357 x y)). Qed.
Lemma lem2287126 (m : nat) (n : nat) : (term97 m n) = (term120 m n).
Proof. exact (@lem2287125 (real_of_num m) (real_of_num n)). Qed.
Lemma lem2287128 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287129 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287130 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2287129) (@lem2287128 m n)). Qed.
Lemma lem2287131 (m : nat) (n : nat) : (term97 m n) = (term121 m n).
Proof. exact (TRANS (@lem2287126 m n) (@lem2287130 m n)). Qed.
Lemma lem2287132 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287133 (m : nat) (n : nat) : (term98 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem2287132) (@lem2287131 m n)). Qed.
Lemma lem2287134 (n' : nat) : (term62 n') = (term62 n').
Proof. exact (eq_refl (term62 n')). Qed.
Lemma lem2287135 (m : nat) (n : nat) (n' : nat) : ((term97 m n) = (term62 n')) = ((term121 m n) = (term62 n')).
Proof. exact (MK_COMB (@lem2287133 m n) (@lem2287134 n')). Qed.
Lemma lem2287138 (m : nat) (n : nat) : (term102 m n) = (term126 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287135 m n n')). Qed.
Lemma lem2287139 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287140 (m : nat) (n : nat) : (term103 m n) = (term127 m n).
Proof. exact (MK_COMB (@lem2287139) (@lem2287138 m n)). Qed.
Lemma lem2287145 (m : nat) (n : nat) : (term104 m n) = (term128 m n).
Proof. exact (MK_COMB (@lem2287117 m n) (@lem2287140 m n)). Qed.
Lemma lem2287148 (m : nat) (n : nat) : (term128 m n) = (term104 m n).
Proof. exact (SYM (@lem2287145 m n)). Qed.
Lemma lem2287158 (x : real) (y : real) : (term30 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286358 x y) (@lem2286357 x y)). Qed.
Lemma lem2287159 (m : nat) (n : nat) : (term105 m n) = (term129 m n).
Proof. exact (@lem2287158 (real_of_num m) (term62 n)). Qed.
Lemma lem2287161 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286352 x y) (@lem2286351 x y)). Qed.
Lemma lem2287162 (m : nat) (n : nat) : (term88 m n) = (term120 m n).
Proof. exact (@lem2287161 (real_of_num m) (real_of_num n)). Qed.
Lemma lem2287164 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287165 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287166 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2287165) (@lem2287164 m n)). Qed.
Lemma lem2287167 (m : nat) (n : nat) : (term88 m n) = (term121 m n).
Proof. exact (TRANS (@lem2287162 m n) (@lem2287166 m n)). Qed.
Lemma lem2287168 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287169 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem2287168) (@lem2287167 m n)). Qed.
Lemma lem2287171 (x : real) : (term21 x) = x.
Proof. exact (EQ_MP (@lem2286346 x) (@lem2286345 x)). Qed.
Lemma lem2287172 (m : nat) (n : nat) : (term130 m n) = (term19 m n).
Proof. exact (@lem2287171 (term19 m n)). Qed.
Lemma lem2287173 (m : nat) (n : nat) : (term129 m n) = (term19 m n).
Proof. exact (TRANS (@lem2287169 m n) (@lem2287172 m n)). Qed.
Lemma lem2287174 (m : nat) (n : nat) : (term105 m n) = (term19 m n).
Proof. exact (TRANS (@lem2287159 m n) (@lem2287173 m n)). Qed.
Lemma lem2287175 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287176 (m : nat) (n : nat) : (term106 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem2287175) (@lem2287174 m n)). Qed.
Lemma lem2287177 (n' : nat) : (real_of_num n') = (real_of_num n').
Proof. exact (eq_refl (real_of_num n')). Qed.
Lemma lem2287178 (m : nat) (n : nat) (n' : nat) : ((term105 m n) = (real_of_num n')) = ((term19 m n) = (real_of_num n')).
Proof. exact (MK_COMB (@lem2287176 m n) (@lem2287177 n')). Qed.
Lemma lem2287181 (m : nat) (n : nat) : (term107 m n) = (term114 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287178 m n n')). Qed.
Lemma lem2287182 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287183 (m : nat) (n : nat) : (term108 m n) = (term115 m n).
Proof. exact (MK_COMB (@lem2287182) (@lem2287181 m n)). Qed.
Lemma lem2287188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2287189 (m : nat) (n : nat) : (term109 m n) = (term116 m n).
Proof. exact (MK_COMB (@lem2287188) (@lem2287183 m n)). Qed.
Lemma lem2287197 (x : real) (y : real) : (term30 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286358 x y) (@lem2286357 x y)). Qed.
Lemma lem2287198 (m : nat) (n : nat) : (term105 m n) = (term129 m n).
Proof. exact (@lem2287197 (real_of_num m) (term62 n)). Qed.
Lemma lem2287200 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2286352 x y) (@lem2286351 x y)). Qed.
Lemma lem2287201 (m : nat) (n : nat) : (term88 m n) = (term120 m n).
Proof. exact (@lem2287200 (real_of_num m) (real_of_num n)). Qed.
Lemma lem2287203 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem2286343 m n) (@lem2286342 m n)). Qed.
Lemma lem2287204 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287205 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2287204) (@lem2287203 m n)). Qed.
Lemma lem2287206 (m : nat) (n : nat) : (term88 m n) = (term121 m n).
Proof. exact (TRANS (@lem2287201 m n) (@lem2287205 m n)). Qed.
Lemma lem2287207 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2287208 (m : nat) (n : nat) : (term129 m n) = (term130 m n).
Proof. exact (MK_COMB (@lem2287207) (@lem2287206 m n)). Qed.
Lemma lem2287210 (x : real) : (term21 x) = x.
Proof. exact (EQ_MP (@lem2286346 x) (@lem2286345 x)). Qed.
Lemma lem2287211 (m : nat) (n : nat) : (term130 m n) = (term19 m n).
Proof. exact (@lem2287210 (term19 m n)). Qed.
Lemma lem2287212 (m : nat) (n : nat) : (term129 m n) = (term19 m n).
Proof. exact (TRANS (@lem2287208 m n) (@lem2287211 m n)). Qed.
Lemma lem2287213 (m : nat) (n : nat) : (term105 m n) = (term19 m n).
Proof. exact (TRANS (@lem2287198 m n) (@lem2287212 m n)). Qed.
Lemma lem2287214 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2287215 (m : nat) (n : nat) : (term106 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem2287214) (@lem2287213 m n)). Qed.
Lemma lem2287216 (n' : nat) : (term62 n') = (term62 n').
Proof. exact (eq_refl (term62 n')). Qed.
Lemma lem2287217 (m : nat) (n : nat) (n' : nat) : ((term105 m n) = (term62 n')) = ((term19 m n) = (term62 n')).
Proof. exact (MK_COMB (@lem2287215 m n) (@lem2287216 n')). Qed.
Lemma lem2287220 (m : nat) (n : nat) : (term110 m n) = (term117 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287217 m n n')). Qed.
Lemma lem2287221 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287222 (m : nat) (n : nat) : (term111 m n) = (term118 m n).
Proof. exact (MK_COMB (@lem2287221) (@lem2287220 m n)). Qed.
Lemma lem2287227 (m : nat) (n : nat) : (term112 m n) = (term119 m n).
Proof. exact (MK_COMB (@lem2287189 m n) (@lem2287222 m n)). Qed.
Lemma lem2287230 (m : nat) (n : nat) : (term119 m n) = (term112 m n).
Proof. exact (SYM (@lem2287227 m n)). Qed.
Lemma lem2287240 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2286331 m n) (@lem2286330 m n)). Qed.
Lemma lem2287241 (m : nat) (n : nat) (n' : nat) : ((term19 m n) = (real_of_num n')) = ((Nat.mul m n) = n').
Proof. exact (@lem2287240 (Nat.mul m n) n'). Qed.
Lemma lem2287244 (m : nat) (n : nat) : (term114 m n) = (term131 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287241 m n n')). Qed.
Lemma lem2287245 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287246 (m : nat) (n : nat) : (term115 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem2287245) (@lem2287244 m n)). Qed.
Lemma lem2287248 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2286325 A a) (@lem2286324 A a)). Qed.
Lemma lem2287249 (a : nat) : (term133 a) = True.
Proof. exact (@lem2287248 nat a). Qed.
Lemma lem2287250 (m : nat) (n : nat) : (term132 m n) = True.
Proof. exact (@lem2287249 (Nat.mul m n)). Qed.
Lemma lem2287251 (m : nat) (n : nat) : (term115 m n) = True.
Proof. exact (TRANS (@lem2287246 m n) (@lem2287250 m n)). Qed.
Lemma lem2287252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2287253 (m : nat) (n : nat) : (term116 m n) = (or True).
Proof. exact (MK_COMB (@lem2287252) (@lem2287251 m n)). Qed.
Lemma lem2287262 (m : nat) (n : nat) : (term118 m n) = (term118 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem2287263 (m : nat) (n : nat) : (term119 m n) = (term134 m n).
Proof. exact (MK_COMB (@lem2287253 m n) (@lem2287262 m n)). Qed.
Lemma lem2287265 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2287266 (m : nat) (n : nat) : (term134 m n) = True.
Proof. exact (@lem2287265 (term118 m n)). Qed.
Lemma lem2287267 (m : nat) (n : nat) : (term119 m n) = True.
Proof. exact (TRANS (@lem2287263 m n) (@lem2287266 m n)). Qed.
Lemma lem2287268 (m : nat) (n : nat) : True = (term119 m n).
Proof. exact (SYM (@lem2287267 m n)). Qed.
Lemma lem2287269 (m : nat) (n : nat) : term119 m n.
Proof. exact (EQ_MP (@lem2287268 m n) (@lem0)). Qed.
Lemma lem2287287 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2286337 x y) (@lem2286336 x y)). Qed.
Lemma lem2287288 (m : nat) (n : nat) (n' : nat) : ((term121 m n) = (term62 n')) = ((term19 m n) = (real_of_num n')).
Proof. exact (@lem2287287 (term19 m n) (real_of_num n')). Qed.
Lemma lem2287290 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2286331 m n) (@lem2286330 m n)). Qed.
Lemma lem2287291 (m : nat) (n : nat) (n' : nat) : ((term19 m n) = (real_of_num n')) = ((Nat.mul m n) = n').
Proof. exact (@lem2287290 (Nat.mul m n) n'). Qed.
Lemma lem2287294 (m : nat) (n : nat) (n' : nat) : ((term121 m n) = (term62 n')) = ((Nat.mul m n) = n').
Proof. exact (TRANS (@lem2287288 m n n') (@lem2287291 m n n')). Qed.
Lemma lem2287295 (m : nat) (n : nat) : (term126 m n) = (term131 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287294 m n n')). Qed.
Lemma lem2287296 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287297 (m : nat) (n : nat) : (term127 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem2287296) (@lem2287295 m n)). Qed.
Lemma lem2287299 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2286325 A a) (@lem2286324 A a)). Qed.
Lemma lem2287300 (a : nat) : (term133 a) = True.
Proof. exact (@lem2287299 nat a). Qed.
Lemma lem2287301 (m : nat) (n : nat) : (term132 m n) = True.
Proof. exact (@lem2287300 (Nat.mul m n)). Qed.
Lemma lem2287302 (m : nat) (n : nat) : (term127 m n) = True.
Proof. exact (TRANS (@lem2287297 m n) (@lem2287301 m n)). Qed.
Lemma lem2287303 (m : nat) (n : nat) : (term125 m n) = (term125 m n).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem2287304 (m : nat) (n : nat) : (term128 m n) = (term135 m n).
Proof. exact (MK_COMB (@lem2287303 m n) (@lem2287302 m n)). Qed.
Lemma lem2287306 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem2287307 (m : nat) (n : nat) : (term135 m n) = True.
Proof. exact (@lem2287306 (term124 m n)). Qed.
Lemma lem2287308 (m : nat) (n : nat) : (term128 m n) = True.
Proof. exact (TRANS (@lem2287304 m n) (@lem2287307 m n)). Qed.
Lemma lem2287309 (m : nat) (n : nat) : True = (term128 m n).
Proof. exact (SYM (@lem2287308 m n)). Qed.
Lemma lem2287310 (m : nat) (n : nat) : term128 m n.
Proof. exact (EQ_MP (@lem2287309 m n) (@lem0)). Qed.
Lemma lem2287328 (x : real) (y : real) : ((real_neg x) = (real_neg y)) = (x = y).
Proof. exact (EQ_MP (@lem2286337 x y) (@lem2286336 x y)). Qed.
Lemma lem2287329 (m : nat) (n : nat) (n' : nat) : ((term121 m n) = (term62 n')) = ((term19 m n) = (real_of_num n')).
Proof. exact (@lem2287328 (term19 m n) (real_of_num n')). Qed.
Lemma lem2287331 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2286331 m n) (@lem2286330 m n)). Qed.
Lemma lem2287332 (m : nat) (n : nat) (n' : nat) : ((term19 m n) = (real_of_num n')) = ((Nat.mul m n) = n').
Proof. exact (@lem2287331 (Nat.mul m n) n'). Qed.
Lemma lem2287335 (m : nat) (n : nat) (n' : nat) : ((term121 m n) = (term62 n')) = ((Nat.mul m n) = n').
Proof. exact (TRANS (@lem2287329 m n n') (@lem2287332 m n n')). Qed.
Lemma lem2287336 (m : nat) (n : nat) : (term126 m n) = (term131 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287335 m n n')). Qed.
Lemma lem2287337 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287338 (m : nat) (n : nat) : (term127 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem2287337) (@lem2287336 m n)). Qed.
Lemma lem2287340 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2286325 A a) (@lem2286324 A a)). Qed.
Lemma lem2287341 (a : nat) : (term133 a) = True.
Proof. exact (@lem2287340 nat a). Qed.
Lemma lem2287342 (m : nat) (n : nat) : (term132 m n) = True.
Proof. exact (@lem2287341 (Nat.mul m n)). Qed.
Lemma lem2287343 (m : nat) (n : nat) : (term127 m n) = True.
Proof. exact (TRANS (@lem2287338 m n) (@lem2287342 m n)). Qed.
Lemma lem2287344 (m : nat) (n : nat) : (term125 m n) = (term125 m n).
Proof. exact (eq_refl (term125 m n)). Qed.
Lemma lem2287345 (m : nat) (n : nat) : (term128 m n) = (term135 m n).
Proof. exact (MK_COMB (@lem2287344 m n) (@lem2287343 m n)). Qed.
Lemma lem2287347 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem2287348 (m : nat) (n : nat) : (term135 m n) = True.
Proof. exact (@lem2287347 (term124 m n)). Qed.
Lemma lem2287349 (m : nat) (n : nat) : (term128 m n) = True.
Proof. exact (TRANS (@lem2287345 m n) (@lem2287348 m n)). Qed.
Lemma lem2287350 (m : nat) (n : nat) : True = (term128 m n).
Proof. exact (SYM (@lem2287349 m n)). Qed.
Lemma lem2287351 (m : nat) (n : nat) : term128 m n.
Proof. exact (EQ_MP (@lem2287350 m n) (@lem0)). Qed.
Lemma lem2287361 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2286331 m n) (@lem2286330 m n)). Qed.
Lemma lem2287362 (m : nat) (n : nat) (n' : nat) : ((term19 m n) = (real_of_num n')) = ((Nat.mul m n) = n').
Proof. exact (@lem2287361 (Nat.mul m n) n'). Qed.
Lemma lem2287365 (m : nat) (n : nat) : (term114 m n) = (term131 m n).
Proof. exact (fun_ext (fun n' : nat => @lem2287362 m n n')). Qed.
Lemma lem2287366 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2287367 (m : nat) (n : nat) : (term115 m n) = (term132 m n).
Proof. exact (MK_COMB (@lem2287366) (@lem2287365 m n)). Qed.
Lemma lem2287369 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem2286325 A a) (@lem2286324 A a)). Qed.
Lemma lem2287370 (a : nat) : (term133 a) = True.
Proof. exact (@lem2287369 nat a). Qed.
Lemma lem2287371 (m : nat) (n : nat) : (term132 m n) = True.
Proof. exact (@lem2287370 (Nat.mul m n)). Qed.
Lemma lem2287372 (m : nat) (n : nat) : (term115 m n) = True.
Proof. exact (TRANS (@lem2287367 m n) (@lem2287371 m n)). Qed.
Lemma lem2287373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2287374 (m : nat) (n : nat) : (term116 m n) = (or True).
Proof. exact (MK_COMB (@lem2287373) (@lem2287372 m n)). Qed.
Lemma lem2287383 (m : nat) (n : nat) : (term118 m n) = (term118 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem2287384 (m : nat) (n : nat) : (term119 m n) = (term134 m n).
Proof. exact (MK_COMB (@lem2287374 m n) (@lem2287383 m n)). Qed.
Lemma lem2287386 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem2287387 (m : nat) (n : nat) : (term134 m n) = True.
Proof. exact (@lem2287386 (term118 m n)). Qed.
Lemma lem2287388 (m : nat) (n : nat) : (term119 m n) = True.
Proof. exact (TRANS (@lem2287384 m n) (@lem2287387 m n)). Qed.
Lemma lem2287389 (m : nat) (n : nat) : True = (term119 m n).
Proof. exact (SYM (@lem2287388 m n)). Qed.
Lemma lem2287390 (m : nat) (n : nat) : term119 m n.
Proof. exact (EQ_MP (@lem2287389 m n) (@lem0)). Qed.
Lemma lem2287391 (m : nat) (n : nat) : term112 m n.
Proof. exact (EQ_MP (@lem2287230 m n) (@lem2287390 m n)). Qed.
Lemma lem2287392 (m : nat) (n : nat) : term104 m n.
Proof. exact (EQ_MP (@lem2287148 m n) (@lem2287351 m n)). Qed.
Lemma lem2287393 (m : nat) (n : nat) : term95 m n.
Proof. exact (EQ_MP (@lem2287086 m n) (@lem2287310 m n)). Qed.
Lemma lem2287394 (m : nat) (n : nat) : term87 m n.
Proof. exact (EQ_MP (@lem2287024 m n) (@lem2287269 m n)). Qed.
Lemma lem2287395 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (term62 n)) : term46 x y.
Proof. exact (EQ_MP (@lem2286974 x m y n h1 h2) (@lem2287391 m n)). Qed.
Lemma lem2287396 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : (real_of_int y) = (real_of_num n)) : term46 x y.
Proof. exact (EQ_MP (@lem2286834 x m y n h1 h2) (@lem2287392 m n)). Qed.
Lemma lem2287397 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (term62 n)) : term46 x y.
Proof. exact (EQ_MP (@lem2286694 x m y n h1 h2) (@lem2287393 m n)). Qed.
Lemma lem2287398 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : (real_of_int y) = (real_of_num n)) : term46 x y.
Proof. exact (EQ_MP (@lem2286554 x m y n h1 h2) (@lem2287394 m n)). Qed.
Lemma lem2287399 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (term62 m)) (h2 : term33 y n) : term46 x y.
Proof. exact (or_elim (@lem2286363 y n h2) (fun h0 : (real_of_int y) = (real_of_num n) => @lem2287396 x m y n h1 h0) (fun h0 : (real_of_int y) = (term62 n) => @lem2287395 x m y n h1 h0)). Qed.
Lemma lem2287400 (y : int) (x : int) (m : nat) (h1 : (real_of_int x) = (term62 m)) : term46 x y.
Proof. exact (ex_elim (@lem2286362 y) (fun n : nat => fun h0 : term136 y n => @lem2287399 x m y n h1 h0)). Qed.
Lemma lem2287401 (x : int) (m : nat) (y : int) (n : nat) (h1 : (real_of_int x) = (real_of_num m)) (h2 : term33 y n) : term46 x y.
Proof. exact (or_elim (@lem2286363 y n h2) (fun h0 : (real_of_int y) = (real_of_num n) => @lem2287398 x m y n h1 h0) (fun h0 : (real_of_int y) = (term62 n) => @lem2287397 x m y n h1 h0)). Qed.
Lemma lem2287402 (y : int) (x : int) (m : nat) (h1 : (real_of_int x) = (real_of_num m)) : term46 x y.
Proof. exact (ex_elim (@lem2286362 y) (fun n : nat => fun h0 : term136 y n => @lem2287401 x m y n h1 h0)). Qed.
Lemma lem2287403 (y : int) (x : int) (m : nat) (h1 : term33 x m) : term46 x y.
Proof. exact (or_elim (@lem2286367 x m h1) (fun h0 : (real_of_int x) = (real_of_num m) => @lem2287402 y x m h0) (fun h0 : (real_of_int x) = (term62 m) => @lem2287400 y x m h0)). Qed.
Lemma lem2287404 (x : int) (y : int) : term46 x y.
Proof. exact (ex_elim (@lem2286366 x) (fun m : nat => fun h0 : term136 x m => @lem2287403 y x m h0)). Qed.
Lemma lem2287405 (x : int) (y : int) : (term39 x y) = (term43 x y).
Proof. exact (EQ_MP (@lem2286408 x y) (@lem2287404 x y)). Qed.
Lemma lem2287410 (x : int) : term137 x.
Proof. exact (fun y : int => @lem2287405 x y). Qed.
Lemma lem2287415 : term138.
Proof. exact (fun x : int => @lem2287410 x). Qed.
