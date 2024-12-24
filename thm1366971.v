Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1366971_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import LE_0_spec.
Require Import LE_ANTISYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1365403_spec.
Require Import thm1365404_spec.
Require Import thm1365406_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm89498_spec.
Lemma lem1366277 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1366278 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1366279 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1366278 n) (@lem1366277 n)). Qed.
Lemma lem1366280 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1366289 : term2.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1366290 (m : nat) : term3 m.
Proof. exact (@lem1366289 m). Qed.
Lemma lem1366291 (m : nat) : (term3 m) = ((term4 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1366295 (m : nat) (n : nat) (h1 : (term5 n m) = (m = n)) : (term5 n m) = (m = n).
Proof. exact (h1). Qed.
Lemma lem1366296 (m : nat) (n : nat) (h1 : (term5 n m) = (m = n)) : (m = n) = (term5 n m).
Proof. exact (SYM (@lem1366295 m n h1)). Qed.
Lemma lem1366297 (n : nat) (m : nat) (h1 : (m = n) = (term5 n m)) : (m = n) = (term5 n m).
Proof. exact (h1). Qed.
Lemma lem1366298 (n : nat) (m : nat) (h1 : (m = n) = (term5 n m)) : (term5 n m) = (m = n).
Proof. exact (SYM (@lem1366297 n m h1)). Qed.
Lemma lem1366299 (n : nat) (m : nat) : ((term5 n m) = (m = n)) = ((m = n) = (term5 n m)).
Proof. exact (prop_ext (fun h1 : (term5 n m) = (m = n) => @lem1366296 m n h1) (fun h1 : (m = n) = (term5 n m) => @lem1366298 n m h1)). Qed.
Lemma lem1366300 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1366299 n m)). Qed.
Lemma lem1366301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1366302 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1366301) (@lem1366300 m)). Qed.
Lemma lem1366303 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1366302 m)). Qed.
Lemma lem1366304 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1366305 : term12 = term13.
Proof. exact (MK_COMB (@lem1366304) (@lem1366303)). Qed.
Lemma lem1366306 : term13.
Proof. exact (EQ_MP (@lem1366305) (@lem92426)). Qed.
Lemma lem1366309 (x : real) (y : real) (h1 : (term14 y x) = (x = y)) : (term14 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1366310 (x : real) (y : real) (h1 : (term14 y x) = (x = y)) : (x = y) = (term14 y x).
Proof. exact (SYM (@lem1366309 x y h1)). Qed.
Lemma lem1366311 (y : real) (x : real) (h1 : (x = y) = (term14 y x)) : (x = y) = (term14 y x).
Proof. exact (h1). Qed.
Lemma lem1366312 (y : real) (x : real) (h1 : (x = y) = (term14 y x)) : (term14 y x) = (x = y).
Proof. exact (SYM (@lem1366311 y x h1)). Qed.
Lemma lem1366313 (y : real) (x : real) : ((term14 y x) = (x = y)) = ((x = y) = (term14 y x)).
Proof. exact (prop_ext (fun h1 : (term14 y x) = (x = y) => @lem1366310 x y h1) (fun h1 : (x = y) = (term14 y x) => @lem1366312 y x h1)). Qed.
Lemma lem1366314 (x : real) : (term15 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1366313 y x)). Qed.
Lemma lem1366315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1366316 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1366315) (@lem1366314 x)). Qed.
Lemma lem1366317 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1366316 x)). Qed.
Lemma lem1366318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1366319 : term21 = term22.
Proof. exact (MK_COMB (@lem1366318) (@lem1366317)). Qed.
Lemma lem1366320 : term22.
Proof. exact (EQ_MP (@lem1366319) (@lem1339379)). Qed.
Lemma lem1366321 (m : nat) : term23 m.
Proof. exact (@lem1366306 m). Qed.
Lemma lem1366322 (m : nat) : (term23 m) = (term9 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem1366323 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1366322 m) (@lem1366321 m)). Qed.
Lemma lem1366324 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem1366323 m n). Qed.
Lemma lem1366325 (n : nat) (m : nat) : (term24 m n) = ((m = n) = (term5 n m)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1366327 (x : real) : term25 x.
Proof. exact (@lem1366320 x). Qed.
Lemma lem1366328 (x : real) : (term25 x) = (term18 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1366329 (x : real) : term18 x.
Proof. exact (EQ_MP (@lem1366328 x) (@lem1366327 x)). Qed.
Lemma lem1366330 (x : real) (y : real) : term26 x y.
Proof. exact (@lem1366329 x y). Qed.
Lemma lem1366331 (y : real) (x : real) : (term26 x y) = ((x = y) = (term14 y x)).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1366346 (y : real) (x : real) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem1366331 y x) (@lem1366330 x y)). Qed.
Lemma lem1366347 (n : nat) (m : nat) : ((real_of_num m) = (real_of_num n)) = (term27 n m).
Proof. exact (@lem1366346 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1366350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366351 (n : nat) (m : nat) : (term28 m n) = (term29 n m).
Proof. exact (MK_COMB (@lem1366350) (@lem1366347 n m)). Qed.
Lemma lem1366355 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366325 n m) (@lem1366324 m n)). Qed.
Lemma lem1366358 (n : nat) (m : nat) : (((real_of_num m) = (real_of_num n)) = (m = n)) = ((term27 n m) = (term5 n m)).
Proof. exact (MK_COMB (@lem1366351 n m) (@lem1366355 n m)). Qed.
Lemma lem1366365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366366 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (MK_COMB (@lem1366365) (@lem1366358 n m)). Qed.
Lemma lem1366380 (y : real) (x : real) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem1366331 y x) (@lem1366330 x y)). Qed.
Lemma lem1366381 (n : nat) (m : nat) : ((term32 m) = (term32 n)) = (term33 n m).
Proof. exact (@lem1366380 (term32 n) (term32 m)). Qed.
Lemma lem1366384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366385 (n : nat) (m : nat) : (term34 m n) = (term35 n m).
Proof. exact (MK_COMB (@lem1366384) (@lem1366381 n m)). Qed.
Lemma lem1366389 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366325 n m) (@lem1366324 m n)). Qed.
Lemma lem1366392 (n : nat) (m : nat) : (((term32 m) = (term32 n)) = (m = n)) = ((term33 n m) = (term5 n m)).
Proof. exact (MK_COMB (@lem1366385 n m) (@lem1366389 n m)). Qed.
Lemma lem1366399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366400 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (MK_COMB (@lem1366399) (@lem1366392 n m)). Qed.
Lemma lem1366414 (y : real) (x : real) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem1366331 y x) (@lem1366330 x y)). Qed.
Lemma lem1366415 (n : nat) (m : nat) : ((term32 m) = (real_of_num n)) = (term38 n m).
Proof. exact (@lem1366414 (real_of_num n) (term32 m)). Qed.
Lemma lem1366418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366419 (n : nat) (m : nat) : (term39 m n) = (term40 n m).
Proof. exact (MK_COMB (@lem1366418) (@lem1366415 n m)). Qed.
Lemma lem1366425 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366325 n m) (@lem1366324 m n)). Qed.
Lemma lem1366426 (m : nat) : (m = (NUMERAL 0)) = (term41 m).
Proof. exact (@lem1366425 (NUMERAL 0) m). Qed.
Lemma lem1366429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366430 (m : nat) : (term42 m) = (term43 m).
Proof. exact (MK_COMB (@lem1366429) (@lem1366426 m)). Qed.
Lemma lem1366434 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366325 n m) (@lem1366324 m n)). Qed.
Lemma lem1366435 (n : nat) : (n = (NUMERAL 0)) = (term41 n).
Proof. exact (@lem1366434 (NUMERAL 0) n). Qed.
Lemma lem1366438 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem1366430 m) (@lem1366435 n)). Qed.
Lemma lem1366441 (m : nat) (n : nat) : (((term32 m) = (real_of_num n)) = (term44 m n)) = ((term38 n m) = (term45 m n)).
Proof. exact (MK_COMB (@lem1366419 n m) (@lem1366438 m n)). Qed.
Lemma lem1366448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366449 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem1366448) (@lem1366441 m n)). Qed.
Lemma lem1366461 (y : real) (x : real) : (x = y) = (term14 y x).
Proof. exact (EQ_MP (@lem1366331 y x) (@lem1366330 x y)). Qed.
Lemma lem1366462 (n : nat) (m : nat) : ((real_of_num m) = (term32 n)) = (term48 n m).
Proof. exact (@lem1366461 (term32 n) (real_of_num m)). Qed.
Lemma lem1366465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366466 (n : nat) (m : nat) : (term49 m n) = (term50 n m).
Proof. exact (MK_COMB (@lem1366465) (@lem1366462 n m)). Qed.
Lemma lem1366472 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366325 n m) (@lem1366324 m n)). Qed.
Lemma lem1366473 (m : nat) : (m = (NUMERAL 0)) = (term41 m).
Proof. exact (@lem1366472 (NUMERAL 0) m). Qed.
Lemma lem1366476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366477 (m : nat) : (term42 m) = (term43 m).
Proof. exact (MK_COMB (@lem1366476) (@lem1366473 m)). Qed.
Lemma lem1366481 (n : nat) (m : nat) : (m = n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366325 n m) (@lem1366324 m n)). Qed.
Lemma lem1366482 (n : nat) : (n = (NUMERAL 0)) = (term41 n).
Proof. exact (@lem1366481 (NUMERAL 0) n). Qed.
Lemma lem1366485 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem1366477 m) (@lem1366482 n)). Qed.
Lemma lem1366488 (m : nat) (n : nat) : (((real_of_num m) = (term32 n)) = (term44 m n)) = ((term48 n m) = (term45 m n)).
Proof. exact (MK_COMB (@lem1366466 n m) (@lem1366485 m n)). Qed.
Lemma lem1366495 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem1366449 m n) (@lem1366488 m n)). Qed.
Lemma lem1366498 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem1366400 n m) (@lem1366495 m n)). Qed.
Lemma lem1366501 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem1366366 n m) (@lem1366498 m n)). Qed.
Lemma lem1366504 (m : nat) (n : nat) : (term56 m n) = (term55 m n).
Proof. exact (SYM (@lem1366501 m n)). Qed.
Lemma lem1366512 (m : nat) (n : nat) : (term57 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem1365404 m n)). Qed.
Lemma lem1366513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366514 (m : nat) (n : nat) : (term58 m n) = (term59 m n).
Proof. exact (MK_COMB (@lem1366513) (@lem1366512 m n)). Qed.
Lemma lem1366516 (m : nat) (n : nat) : (term57 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem1365404 m n)). Qed.
Lemma lem1366517 (n : nat) (m : nat) : (term57 n m) = (Peano.le n m).
Proof. exact (@lem1366516 n m). Qed.
Lemma lem1366518 (n : nat) (m : nat) : (term27 n m) = (term5 n m).
Proof. exact (MK_COMB (@lem1366514 m n) (@lem1366517 n m)). Qed.
Lemma lem1366521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366522 (n : nat) (m : nat) : (term29 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem1366521) (@lem1366518 n m)). Qed.
Lemma lem1366525 (n : nat) (m : nat) : (term5 n m) = (term5 n m).
Proof. exact (eq_refl (term5 n m)). Qed.
Lemma lem1366526 (n : nat) (m : nat) : ((term27 n m) = (term5 n m)) = ((term5 n m) = (term5 n m)).
Proof. exact (MK_COMB (@lem1366522 n m) (@lem1366525 n m)). Qed.
Lemma lem1366528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366529 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366528 Prop x). Qed.
Lemma lem1366530 (n : nat) (m : nat) : ((term5 n m) = (term5 n m)) = True.
Proof. exact (@lem1366529 (term5 n m)). Qed.
Lemma lem1366531 (n : nat) (m : nat) : ((term27 n m) = (term5 n m)) = True.
Proof. exact (TRANS (@lem1366526 n m) (@lem1366530 n m)). Qed.
Lemma lem1366532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366533 (n : nat) (m : nat) : (term31 n m) = (and True).
Proof. exact (MK_COMB (@lem1366532) (@lem1366531 n m)). Qed.
Lemma lem1366541 (n : nat) (m : nat) : (term61 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem1365406 m n)). Qed.
Lemma lem1366542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366543 (n : nat) (m : nat) : (term62 m n) = (term59 n m).
Proof. exact (MK_COMB (@lem1366542) (@lem1366541 n m)). Qed.
Lemma lem1366545 (n : nat) (m : nat) : (term61 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem1365406 m n)). Qed.
Lemma lem1366546 (m : nat) (n : nat) : (term61 n m) = (Peano.le m n).
Proof. exact (@lem1366545 m n). Qed.
Lemma lem1366547 (m : nat) (n : nat) : (term33 n m) = (term5 m n).
Proof. exact (MK_COMB (@lem1366543 n m) (@lem1366546 m n)). Qed.
Lemma lem1366550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366551 (m : nat) (n : nat) : (term35 n m) = (term60 m n).
Proof. exact (MK_COMB (@lem1366550) (@lem1366547 m n)). Qed.
Lemma lem1366554 (n : nat) (m : nat) : (term5 n m) = (term5 n m).
Proof. exact (eq_refl (term5 n m)). Qed.
Lemma lem1366555 (n : nat) (m : nat) : ((term33 n m) = (term5 n m)) = ((term5 m n) = (term5 n m)).
Proof. exact (MK_COMB (@lem1366551 m n) (@lem1366554 n m)). Qed.
Lemma lem1366558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366559 (n : nat) (m : nat) : (term37 n m) = (term63 n m).
Proof. exact (MK_COMB (@lem1366558) (@lem1366555 n m)). Qed.
Lemma lem1366567 (m : nat) (n : nat) : (term64 m n) = True.
Proof. exact (proj1 (@lem1365403 m n)). Qed.
Lemma lem1366568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366569 (m : nat) (n : nat) : (term65 m n) = (and True).
Proof. exact (MK_COMB (@lem1366568) (@lem1366567 m n)). Qed.
Lemma lem1366571 (m : nat) (n : nat) : (term66 m n) = (term44 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem1366572 (n : nat) (m : nat) : (term66 n m) = (term44 n m).
Proof. exact (@lem1366571 n m). Qed.
Lemma lem1366579 (n : nat) (m : nat) : (term38 n m) = (term67 n m).
Proof. exact (MK_COMB (@lem1366569 m n) (@lem1366572 n m)). Qed.
Lemma lem1366581 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366582 (n : nat) (m : nat) : (term67 n m) = (term44 n m).
Proof. exact (@lem1366581 (term44 n m)). Qed.
Lemma lem1366589 (n : nat) (m : nat) : (term38 n m) = (term44 n m).
Proof. exact (TRANS (@lem1366579 n m) (@lem1366582 n m)). Qed.
Lemma lem1366590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366591 (n : nat) (m : nat) : (term40 n m) = (term68 n m).
Proof. exact (MK_COMB (@lem1366590) (@lem1366589 n m)). Qed.
Lemma lem1366597 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1366291 m) (@lem1366290 m)). Qed.
Lemma lem1366600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366601 (m : nat) : (term69 m) = (term42 m).
Proof. exact (MK_COMB (@lem1366600) (@lem1366597 m)). Qed.
Lemma lem1366603 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1366280 n) (@lem1366279 n)). Qed.
Lemma lem1366604 (m : nat) : (term1 m) = True.
Proof. exact (@lem1366603 m). Qed.
Lemma lem1366605 (m : nat) : (term41 m) = (term70 m).
Proof. exact (MK_COMB (@lem1366601 m) (@lem1366604 m)). Qed.
Lemma lem1366607 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366608 (m : nat) : (term70 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1366607 (m = (NUMERAL 0))). Qed.
Lemma lem1366611 (m : nat) : (term41 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem1366605 m) (@lem1366608 m)). Qed.
Lemma lem1366612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366613 (m : nat) : (term43 m) = (term42 m).
Proof. exact (MK_COMB (@lem1366612) (@lem1366611 m)). Qed.
Lemma lem1366617 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1366291 m) (@lem1366290 m)). Qed.
Lemma lem1366618 (n : nat) : (term4 n) = (n = (NUMERAL 0)).
Proof. exact (@lem1366617 n). Qed.
Lemma lem1366621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366622 (n : nat) : (term69 n) = (term42 n).
Proof. exact (MK_COMB (@lem1366621) (@lem1366618 n)). Qed.
Lemma lem1366624 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1366280 n) (@lem1366279 n)). Qed.
Lemma lem1366625 (n : nat) : (term41 n) = (term70 n).
Proof. exact (MK_COMB (@lem1366622 n) (@lem1366624 n)). Qed.
Lemma lem1366627 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366628 (n : nat) : (term70 n) = (n = (NUMERAL 0)).
Proof. exact (@lem1366627 (n = (NUMERAL 0))). Qed.
Lemma lem1366631 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem1366625 n) (@lem1366628 n)). Qed.
Lemma lem1366632 (m : nat) (n : nat) : (term45 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem1366613 m) (@lem1366631 n)). Qed.
Lemma lem1366635 (m : nat) (n : nat) : ((term38 n m) = (term45 m n)) = ((term44 n m) = (term44 m n)).
Proof. exact (MK_COMB (@lem1366591 n m) (@lem1366632 m n)). Qed.
Lemma lem1366638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366639 (m : nat) (n : nat) : (term47 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem1366638) (@lem1366635 m n)). Qed.
Lemma lem1366645 (m : nat) (n : nat) : (term66 m n) = (term44 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem1366652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366653 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem1366652) (@lem1366645 m n)). Qed.
Lemma lem1366655 (m : nat) (n : nat) : (term64 m n) = True.
Proof. exact (proj1 (@lem1365403 m n)). Qed.
Lemma lem1366656 (n : nat) (m : nat) : (term64 n m) = True.
Proof. exact (@lem1366655 n m). Qed.
Lemma lem1366657 (m : nat) (n : nat) : (term48 n m) = (term74 m n).
Proof. exact (MK_COMB (@lem1366653 m n) (@lem1366656 n m)). Qed.
Lemma lem1366659 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366660 (m : nat) (n : nat) : (term74 m n) = (term44 m n).
Proof. exact (@lem1366659 (term44 m n)). Qed.
Lemma lem1366667 (m : nat) (n : nat) : (term48 n m) = (term44 m n).
Proof. exact (TRANS (@lem1366657 m n) (@lem1366660 m n)). Qed.
Lemma lem1366668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366669 (m : nat) (n : nat) : (term50 n m) = (term68 m n).
Proof. exact (MK_COMB (@lem1366668) (@lem1366667 m n)). Qed.
Lemma lem1366675 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1366291 m) (@lem1366290 m)). Qed.
Lemma lem1366678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366679 (m : nat) : (term69 m) = (term42 m).
Proof. exact (MK_COMB (@lem1366678) (@lem1366675 m)). Qed.
Lemma lem1366681 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1366280 n) (@lem1366279 n)). Qed.
Lemma lem1366682 (m : nat) : (term1 m) = True.
Proof. exact (@lem1366681 m). Qed.
Lemma lem1366683 (m : nat) : (term41 m) = (term70 m).
Proof. exact (MK_COMB (@lem1366679 m) (@lem1366682 m)). Qed.
Lemma lem1366685 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366686 (m : nat) : (term70 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1366685 (m = (NUMERAL 0))). Qed.
Lemma lem1366689 (m : nat) : (term41 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem1366683 m) (@lem1366686 m)). Qed.
Lemma lem1366690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366691 (m : nat) : (term43 m) = (term42 m).
Proof. exact (MK_COMB (@lem1366690) (@lem1366689 m)). Qed.
Lemma lem1366695 (m : nat) : (term4 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1366291 m) (@lem1366290 m)). Qed.
Lemma lem1366696 (n : nat) : (term4 n) = (n = (NUMERAL 0)).
Proof. exact (@lem1366695 n). Qed.
Lemma lem1366699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366700 (n : nat) : (term69 n) = (term42 n).
Proof. exact (MK_COMB (@lem1366699) (@lem1366696 n)). Qed.
Lemma lem1366702 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1366280 n) (@lem1366279 n)). Qed.
Lemma lem1366703 (n : nat) : (term41 n) = (term70 n).
Proof. exact (MK_COMB (@lem1366700 n) (@lem1366702 n)). Qed.
Lemma lem1366705 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366706 (n : nat) : (term70 n) = (n = (NUMERAL 0)).
Proof. exact (@lem1366705 (n = (NUMERAL 0))). Qed.
Lemma lem1366709 (n : nat) : (term41 n) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem1366703 n) (@lem1366706 n)). Qed.
Lemma lem1366710 (m : nat) (n : nat) : (term45 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem1366691 m) (@lem1366709 n)). Qed.
Lemma lem1366713 (m : nat) (n : nat) : ((term48 n m) = (term45 m n)) = ((term44 m n) = (term44 m n)).
Proof. exact (MK_COMB (@lem1366669 m n) (@lem1366710 m n)). Qed.
Lemma lem1366715 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366716 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366715 Prop x). Qed.
Lemma lem1366717 (m : nat) (n : nat) : ((term44 m n) = (term44 m n)) = True.
Proof. exact (@lem1366716 (term44 m n)). Qed.
Lemma lem1366718 (m : nat) (n : nat) : ((term48 n m) = (term45 m n)) = True.
Proof. exact (TRANS (@lem1366713 m n) (@lem1366717 m n)). Qed.
Lemma lem1366719 (m : nat) (n : nat) : (term52 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem1366639 m n) (@lem1366718 m n)). Qed.
Lemma lem1366721 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366722 (m : nat) (n : nat) : (term75 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (@lem1366721 ((term44 n m) = (term44 m n))). Qed.
Lemma lem1366737 (m : nat) (n : nat) : (term52 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (TRANS (@lem1366719 m n) (@lem1366722 m n)). Qed.
Lemma lem1366738 (m : nat) (n : nat) : (term54 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem1366559 n m) (@lem1366737 m n)). Qed.
Lemma lem1366741 (m : nat) (n : nat) : (term56 m n) = (term77 m n).
Proof. exact (MK_COMB (@lem1366533 n m) (@lem1366738 m n)). Qed.
Lemma lem1366743 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366744 (m : nat) (n : nat) : (term77 m n) = (term76 m n).
Proof. exact (@lem1366743 (term76 m n)). Qed.
Lemma lem1366767 (m : nat) (n : nat) : (term56 m n) = (term76 m n).
Proof. exact (TRANS (@lem1366741 m n) (@lem1366744 m n)). Qed.
Lemma lem1366768 (m : nat) (n : nat) : (term76 m n) = (term56 m n).
Proof. exact (SYM (@lem1366767 m n)). Qed.
Lemma lem1366777 (n : nat) (m : nat) : term78 n m.
Proof. exact (@lem9851 (Peano.le n m)). Qed.
Lemma lem1366778 (n : nat) (m : nat) : (term78 n m) = (term79 n m).
Proof. exact (eq_refl (term78 n m)). Qed.
Lemma lem1366779 (n : nat) (m : nat) : term79 n m.
Proof. exact (EQ_MP (@lem1366778 n m) (@lem1366777 n m)). Qed.
Lemma lem1366780 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : (Peano.le n m) = True.
Proof. exact (h1). Qed.
Lemma lem1366781 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : (Peano.le n m) = False.
Proof. exact (h1). Qed.
Lemma lem1366790 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem1366791 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : (term81 n m) = (term82 m n).
Proof. exact (MK_COMB (@lem1366790 m n) (@lem1366780 n m h1)). Qed.
Lemma lem1366792 (m : nat) (n : nat) : (term82 m n) = ((term83 m n) = (term84 m n)).
Proof. exact (eq_refl (term82 m n)). Qed.
Lemma lem1366793 (n : nat) (m : nat) : (term85 n m) = (term85 n m).
Proof. exact (eq_refl (term85 n m)). Qed.
Lemma lem1366794 (m : nat) (n : nat) : ((term81 n m) = (term82 m n)) = ((term81 n m) = ((term83 m n) = (term84 m n))).
Proof. exact (MK_COMB (@lem1366793 n m) (@lem1366792 m n)). Qed.
Lemma lem1366795 (n : nat) (m : nat) : (term81 n m) = ((term5 m n) = (term5 n m)).
Proof. exact (eq_refl (term81 n m)). Qed.
Lemma lem1366796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366797 (n : nat) (m : nat) : (term85 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem1366796) (@lem1366795 n m)). Qed.
Lemma lem1366798 (m : nat) (n : nat) : ((term83 m n) = (term84 m n)) = ((term83 m n) = (term84 m n)).
Proof. exact (eq_refl ((term83 m n) = (term84 m n))). Qed.
Lemma lem1366799 (m : nat) (n : nat) : ((term81 n m) = ((term83 m n) = (term84 m n))) = (((term5 m n) = (term5 n m)) = ((term83 m n) = (term84 m n))).
Proof. exact (MK_COMB (@lem1366797 n m) (@lem1366798 m n)). Qed.
Lemma lem1366800 (m : nat) (n : nat) : ((term81 n m) = (term82 m n)) = (((term5 m n) = (term5 n m)) = ((term83 m n) = (term84 m n))).
Proof. exact (TRANS (@lem1366794 m n) (@lem1366799 m n)). Qed.
Lemma lem1366801 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : ((term5 m n) = (term5 n m)) = ((term83 m n) = (term84 m n)).
Proof. exact (EQ_MP (@lem1366800 m n) (@lem1366791 n m h1)). Qed.
Lemma lem1366802 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : ((term83 m n) = (term84 m n)) = ((term5 m n) = (term5 n m)).
Proof. exact (SYM (@lem1366801 n m h1)). Qed.
Lemma lem1366803 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem1366804 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : (term81 n m) = (term87 m n).
Proof. exact (MK_COMB (@lem1366803 m n) (@lem1366781 n m h1)). Qed.
Lemma lem1366805 (m : nat) (n : nat) : (term87 m n) = ((term88 m n) = (term89 m n)).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem1366806 (n : nat) (m : nat) : (term85 n m) = (term85 n m).
Proof. exact (eq_refl (term85 n m)). Qed.
Lemma lem1366807 (m : nat) (n : nat) : ((term81 n m) = (term87 m n)) = ((term81 n m) = ((term88 m n) = (term89 m n))).
Proof. exact (MK_COMB (@lem1366806 n m) (@lem1366805 m n)). Qed.
Lemma lem1366808 (n : nat) (m : nat) : (term81 n m) = ((term5 m n) = (term5 n m)).
Proof. exact (eq_refl (term81 n m)). Qed.
Lemma lem1366809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366810 (n : nat) (m : nat) : (term85 n m) = (term86 n m).
Proof. exact (MK_COMB (@lem1366809) (@lem1366808 n m)). Qed.
Lemma lem1366811 (m : nat) (n : nat) : ((term88 m n) = (term89 m n)) = ((term88 m n) = (term89 m n)).
Proof. exact (eq_refl ((term88 m n) = (term89 m n))). Qed.
Lemma lem1366812 (m : nat) (n : nat) : ((term81 n m) = ((term88 m n) = (term89 m n))) = (((term5 m n) = (term5 n m)) = ((term88 m n) = (term89 m n))).
Proof. exact (MK_COMB (@lem1366810 n m) (@lem1366811 m n)). Qed.
Lemma lem1366813 (m : nat) (n : nat) : ((term81 n m) = (term87 m n)) = (((term5 m n) = (term5 n m)) = ((term88 m n) = (term89 m n))).
Proof. exact (TRANS (@lem1366807 m n) (@lem1366812 m n)). Qed.
Lemma lem1366814 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : ((term5 m n) = (term5 n m)) = ((term88 m n) = (term89 m n)).
Proof. exact (EQ_MP (@lem1366813 m n) (@lem1366804 n m h1)). Qed.
Lemma lem1366815 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : ((term88 m n) = (term89 m n)) = ((term5 m n) = (term5 n m)).
Proof. exact (SYM (@lem1366814 n m h1)). Qed.
Lemma lem1366819 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366820 (m : nat) (n : nat) : (term83 m n) = (Peano.le m n).
Proof. exact (@lem1366819 (Peano.le m n)). Qed.
Lemma lem1366821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366822 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem1366821) (@lem1366820 m n)). Qed.
Lemma lem1366824 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366825 (m : nat) (n : nat) : (term84 m n) = (Peano.le m n).
Proof. exact (@lem1366824 (Peano.le m n)). Qed.
Lemma lem1366826 (m : nat) (n : nat) : ((term83 m n) = (term84 m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1366822 m n) (@lem1366825 m n)). Qed.
Lemma lem1366828 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366829 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366828 Prop x). Qed.
Lemma lem1366830 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem1366829 (Peano.le m n)). Qed.
Lemma lem1366831 (m : nat) (n : nat) : ((term83 m n) = (term84 m n)) = True.
Proof. exact (TRANS (@lem1366826 m n) (@lem1366830 m n)). Qed.
Lemma lem1366832 (m : nat) (n : nat) : True = ((term83 m n) = (term84 m n)).
Proof. exact (SYM (@lem1366831 m n)). Qed.
Lemma lem1366833 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (EQ_MP (@lem1366832 m n) (@lem0)). Qed.
Lemma lem1366837 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1366838 (m : nat) (n : nat) : (term88 m n) = False.
Proof. exact (@lem1366837 (Peano.le m n)). Qed.
Lemma lem1366839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366840 (m : nat) (n : nat) : (term92 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1366839) (@lem1366838 m n)). Qed.
Lemma lem1366842 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1366843 (m : nat) (n : nat) : (term89 m n) = False.
Proof. exact (@lem1366842 (Peano.le m n)). Qed.
Lemma lem1366844 (m : nat) (n : nat) : ((term88 m n) = (term89 m n)) = (False = False).
Proof. exact (MK_COMB (@lem1366840 m n) (@lem1366843 m n)). Qed.
Lemma lem1366846 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1366847 : (False = False) = (~ False).
Proof. exact (@lem1366846 False). Qed.
Lemma lem1366849 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1366850 : (False = False) = True.
Proof. exact (TRANS (@lem1366847) (@lem1366849)). Qed.
Lemma lem1366851 (m : nat) (n : nat) : ((term88 m n) = (term89 m n)) = True.
Proof. exact (TRANS (@lem1366844 m n) (@lem1366850)). Qed.
Lemma lem1366852 (m : nat) (n : nat) : True = ((term88 m n) = (term89 m n)).
Proof. exact (SYM (@lem1366851 m n)). Qed.
Lemma lem1366853 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (EQ_MP (@lem1366852 m n) (@lem0)). Qed.
Lemma lem1366854 (n : nat) (m : nat) (h1 : (Peano.le n m) = False) : (term5 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366815 n m h1) (@lem1366853 m n)). Qed.
Lemma lem1366855 (n : nat) (m : nat) (h1 : (Peano.le n m) = True) : (term5 m n) = (term5 n m).
Proof. exact (EQ_MP (@lem1366802 n m h1) (@lem1366833 m n)). Qed.
Lemma lem1366858 (n : nat) (m : nat) : (term5 m n) = (term5 n m).
Proof. exact (or_elim (@lem1366779 n m) (fun h0 : (Peano.le n m) = True => @lem1366855 n m h0) (fun h0 : (Peano.le n m) = False => @lem1366854 n m h0)). Qed.
Lemma lem1366875 (n : nat) : term93 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem1366876 (n : nat) : (term93 n) = (term94 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem1366877 (n : nat) : term94 n.
Proof. exact (EQ_MP (@lem1366876 n) (@lem1366875 n)). Qed.
Lemma lem1366878 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem1366879 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem1366896 (m : nat) : (term95 m) = (term95 m).
Proof. exact (eq_refl (term95 m)). Qed.
Lemma lem1366897 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term96 m n) = (term97 m).
Proof. exact (MK_COMB (@lem1366896 m) (@lem1366878 n h1)). Qed.
Lemma lem1366898 (m : nat) : (term97 m) = ((term98 m) = (term70 m)).
Proof. exact (eq_refl (term97 m)). Qed.
Lemma lem1366899 (m : nat) (n : nat) : (term99 m n) = (term99 m n).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem1366900 (n : nat) (m : nat) : ((term96 m n) = (term97 m)) = ((term96 m n) = ((term98 m) = (term70 m))).
Proof. exact (MK_COMB (@lem1366899 m n) (@lem1366898 m)). Qed.
Lemma lem1366901 (m : nat) (n : nat) : (term96 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem1366902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366903 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem1366902) (@lem1366901 m n)). Qed.
Lemma lem1366904 (m : nat) : ((term98 m) = (term70 m)) = ((term98 m) = (term70 m)).
Proof. exact (eq_refl ((term98 m) = (term70 m))). Qed.
Lemma lem1366905 (n : nat) (m : nat) : ((term96 m n) = ((term98 m) = (term70 m))) = (((term44 n m) = (term44 m n)) = ((term98 m) = (term70 m))).
Proof. exact (MK_COMB (@lem1366903 m n) (@lem1366904 m)). Qed.
Lemma lem1366906 (n : nat) (m : nat) : ((term96 m n) = (term97 m)) = (((term44 n m) = (term44 m n)) = ((term98 m) = (term70 m))).
Proof. exact (TRANS (@lem1366900 n m) (@lem1366905 n m)). Qed.
Lemma lem1366907 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term44 n m) = (term44 m n)) = ((term98 m) = (term70 m)).
Proof. exact (EQ_MP (@lem1366906 n m) (@lem1366897 m n h1)). Qed.
Lemma lem1366908 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term98 m) = (term70 m)) = ((term44 n m) = (term44 m n)).
Proof. exact (SYM (@lem1366907 m n h1)). Qed.
Lemma lem1366909 (m : nat) : (term95 m) = (term95 m).
Proof. exact (eq_refl (term95 m)). Qed.
Lemma lem1366910 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term96 m n) = (term101 m).
Proof. exact (MK_COMB (@lem1366909 m) (@lem1366879 n h1)). Qed.
Lemma lem1366911 (m : nat) : (term101 m) = ((term102 m) = (term103 m)).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem1366912 (m : nat) (n : nat) : (term99 m n) = (term99 m n).
Proof. exact (eq_refl (term99 m n)). Qed.
Lemma lem1366913 (n : nat) (m : nat) : ((term96 m n) = (term101 m)) = ((term96 m n) = ((term102 m) = (term103 m))).
Proof. exact (MK_COMB (@lem1366912 m n) (@lem1366911 m)). Qed.
Lemma lem1366914 (m : nat) (n : nat) : (term96 m n) = ((term44 n m) = (term44 m n)).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem1366915 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366916 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem1366915) (@lem1366914 m n)). Qed.
Lemma lem1366917 (m : nat) : ((term102 m) = (term103 m)) = ((term102 m) = (term103 m)).
Proof. exact (eq_refl ((term102 m) = (term103 m))). Qed.
Lemma lem1366918 (n : nat) (m : nat) : ((term96 m n) = ((term102 m) = (term103 m))) = (((term44 n m) = (term44 m n)) = ((term102 m) = (term103 m))).
Proof. exact (MK_COMB (@lem1366916 m n) (@lem1366917 m)). Qed.
Lemma lem1366919 (n : nat) (m : nat) : ((term96 m n) = (term101 m)) = (((term44 n m) = (term44 m n)) = ((term102 m) = (term103 m))).
Proof. exact (TRANS (@lem1366913 n m) (@lem1366918 n m)). Qed.
Lemma lem1366920 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term44 n m) = (term44 m n)) = ((term102 m) = (term103 m)).
Proof. exact (EQ_MP (@lem1366919 n m) (@lem1366910 m n h1)). Qed.
Lemma lem1366921 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term102 m) = (term103 m)) = ((term44 n m) = (term44 m n)).
Proof. exact (SYM (@lem1366920 m n h1)). Qed.
Lemma lem1366925 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366926 (m : nat) : (term98 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1366925 (m = (NUMERAL 0))). Qed.
Lemma lem1366929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366930 (m : nat) : (term104 m) = (term105 m).
Proof. exact (MK_COMB (@lem1366929) (@lem1366926 m)). Qed.
Lemma lem1366932 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366933 (m : nat) : (term70 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1366932 (m = (NUMERAL 0))). Qed.
Lemma lem1366936 (m : nat) : ((term98 m) = (term70 m)) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1366930 m) (@lem1366933 m)). Qed.
Lemma lem1366938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366939 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366938 Prop x). Qed.
Lemma lem1366940 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem1366939 (m = (NUMERAL 0))). Qed.
Lemma lem1366941 (m : nat) : ((term98 m) = (term70 m)) = True.
Proof. exact (TRANS (@lem1366936 m) (@lem1366940 m)). Qed.
Lemma lem1366942 (m : nat) : True = ((term98 m) = (term70 m)).
Proof. exact (SYM (@lem1366941 m)). Qed.
Lemma lem1366943 (m : nat) : (term98 m) = (term70 m).
Proof. exact (EQ_MP (@lem1366942 m) (@lem0)). Qed.
Lemma lem1366947 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1366948 (m : nat) : (term102 m) = False.
Proof. exact (@lem1366947 (m = (NUMERAL 0))). Qed.
Lemma lem1366949 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366950 (m : nat) : (term106 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1366949) (@lem1366948 m)). Qed.
Lemma lem1366952 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1366953 (m : nat) : (term103 m) = False.
Proof. exact (@lem1366952 (m = (NUMERAL 0))). Qed.
Lemma lem1366954 (m : nat) : ((term102 m) = (term103 m)) = (False = False).
Proof. exact (MK_COMB (@lem1366950 m) (@lem1366953 m)). Qed.
Lemma lem1366956 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1366957 : (False = False) = (~ False).
Proof. exact (@lem1366956 False). Qed.
Lemma lem1366959 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1366960 : (False = False) = True.
Proof. exact (TRANS (@lem1366957) (@lem1366959)). Qed.
Lemma lem1366961 (m : nat) : ((term102 m) = (term103 m)) = True.
Proof. exact (TRANS (@lem1366954 m) (@lem1366960)). Qed.
Lemma lem1366962 (m : nat) : True = ((term102 m) = (term103 m)).
Proof. exact (SYM (@lem1366961 m)). Qed.
Lemma lem1366963 (m : nat) : (term102 m) = (term103 m).
Proof. exact (EQ_MP (@lem1366962 m) (@lem0)). Qed.
Lemma lem1366964 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term44 n m) = (term44 m n).
Proof. exact (EQ_MP (@lem1366921 m n h1) (@lem1366963 m)). Qed.
Lemma lem1366965 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term44 n m) = (term44 m n).
Proof. exact (EQ_MP (@lem1366908 m n h1) (@lem1366943 m)). Qed.
Lemma lem1366968 (m : nat) (n : nat) : (term44 n m) = (term44 m n).
Proof. exact (or_elim (@lem1366877 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem1366965 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem1366964 m n h0)). Qed.
Lemma lem1366969 (m : nat) (n : nat) : term76 m n.
Proof. exact (conj (@lem1366858 n m) (@lem1366968 m n)). Qed.
Lemma lem1366970 (m : nat) (n : nat) : term56 m n.
Proof. exact (EQ_MP (@lem1366768 m n) (@lem1366969 m n)). Qed.
Lemma lem1366971 (m : nat) (n : nat) : term55 m n.
Proof. exact (EQ_MP (@lem1366504 m n) (@lem1366970 m n)). Qed.
