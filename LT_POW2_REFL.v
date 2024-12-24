Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_POW2_REFL_term_abbrevs.
Require Import ADD1_spec.
Require Import DISJ_ACI_spec.
Require Import EXP_EQ_0_spec.
Require Import LE_1_spec.
Require Import LE_SUC_LT_spec.
Require Import LTE_ADD2_spec.
Require Import MULT_2_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm1831_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80360_spec.
Require Import thm80550_spec.
Require Import thm86199_spec.
Require Import thm89994_spec.
Lemma lem106293 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem106294 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem106293 h1 m). Qed.
Lemma lem106295 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem106296 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem106295 m) (@lem106294 m h1)). Qed.
Lemma lem106297 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem106296 m h1 n). Qed.
Lemma lem106298 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem106299 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem106298 m n) (@lem106297 m n h1)). Qed.
Lemma lem106300 (m : nat) (n : nat) (p : nat) (h1 : term0) : term5 m n p.
Proof. exact (@lem106299 m n h1 p). Qed.
Lemma lem106301 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem106302 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (EQ_MP (@lem106301 m n p) (@lem106300 m n p h1)). Qed.
Lemma lem106303 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term7 m n p q.
Proof. exact (@lem106302 m n p h1 q). Qed.
Lemma lem106304 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem106305 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (EQ_MP (@lem106304 m n p q) (@lem106303 m n p q h1)). Qed.
Lemma lem106306 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term9 m p n q.
Proof. exact (h1). Qed.
Lemma lem106307 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem106305 m n p q h1 (@lem106306 m p n q h2)). Qed.
Lemma lem106308 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term9 m p n q) : term11 m n p q.
Proof. exact (fun h0 : term0 => @lem106307 m p n q h0 h1). Qed.
Lemma lem106309 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem106310 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term0) (h2 : term9 m p n q) : term10 m n p q.
Proof. exact (@lem106308 m p n q h2 (@lem106309 h1)). Qed.
Lemma lem106311 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term0) : term8 m n p q.
Proof. exact (fun h0 : term9 m p n q => @lem106310 m p n q h1 h0). Qed.
Lemma lem106312 (m : nat) (n : nat) (p : nat) (h1 : term0) : term6 m n p.
Proof. exact (fun q : nat => @lem106311 m n p q h1). Qed.
Lemma lem106313 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun p : nat => @lem106312 m n p h1). Qed.
Lemma lem106314 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem106313 m n h1). Qed.
Lemma lem106315 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem106314 m h1). Qed.
Lemma lem106316 : term12.
Proof. exact (fun h0 : term0 => @lem106315 h0). Qed.
Lemma lem106317 : term0.
Proof. exact (@lem106316 (@lem101790)). Qed.
Lemma lem106318 (m : nat) : term1 m.
Proof. exact (@lem106317 m). Qed.
Lemma lem106319 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem106320 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem106319 m) (@lem106318 m)). Qed.
Lemma lem106321 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem106320 m n). Qed.
Lemma lem106322 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem106323 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem106322 m n) (@lem106321 m n)). Qed.
Lemma lem106324 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem106323 m n p). Qed.
Lemma lem106325 (m : nat) (n : nat) (p : nat) : (term5 m n p) = (term6 m n p).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem106326 (m : nat) (n : nat) (p : nat) : term6 m n p.
Proof. exact (EQ_MP (@lem106325 m n p) (@lem106324 m n p)). Qed.
Lemma lem106327 (m : nat) (n : nat) (p : nat) (q : nat) : term7 m n p q.
Proof. exact (@lem106326 m n p q). Qed.
Lemma lem106328 (m : nat) (n : nat) (p : nat) (q : nat) : (term7 m n p q) = (term8 m n p q).
Proof. exact (eq_refl (term7 m n p q)). Qed.
Lemma lem106330 : term13.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem106331 (m : nat) : term14 m.
Proof. exact (@lem106330 m). Qed.
Lemma lem106332 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem106333 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem106332 m) (@lem106331 m)). Qed.
Lemma lem106334 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem106333 m n). Qed.
Lemma lem106335 (m : nat) (n : nat) : (term16 m n) = ((term17 m n) = (term18 m n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem106337 : term19.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem106338 (m : nat) : term20 m.
Proof. exact (@lem106337 m). Qed.
Lemma lem106339 (m : nat) : (term20 m) = ((term21 m) = False).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem106341 (m : nat) : term22 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem106342 (m : nat) : (term22 m) = ((S m) = (term23 m)).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem106344 (n : nat) : term24 n.
Proof. exact (@lem84996 n). Qed.
Lemma lem106345 (n : nat) : (term24 n) = ((term25 n) = (Nat.add n n)).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem106347 : term26.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem106348 (m : nat) : term27 m.
Proof. exact (@lem106347 m). Qed.
Lemma lem106349 (m : nat) : (term27 m) = (term28 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem106350 (m : nat) : term28 m.
Proof. exact (EQ_MP (@lem106349 m) (@lem106348 m)). Qed.
Lemma lem106351 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem106350 m n). Qed.
Lemma lem106352 (m : nat) (n : nat) : (term29 m n) = ((term30 m n) = (term31 m n)).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem106354 : term32.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem106355 (m : nat) : term33 m.
Proof. exact (@lem106354 m). Qed.
Lemma lem106356 (m : nat) : (term33 m) = ((term34 m) = term35).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem106359 (P : nat -> Prop) : term36 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem106360 : term37.
Proof. exact (@lem106359 term38). Qed.
Lemma lem106361 : term39 = term40.
Proof. exact (eq_refl term39). Qed.
Lemma lem106362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106363 : term41 = term42.
Proof. exact (MK_COMB (@lem106362) (@lem106361)). Qed.
Lemma lem106364 (n : nat) : (term43 n) = (term44 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem106365 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem106366 (n : nat) : (term45 n) = (term46 n).
Proof. exact (MK_COMB (@lem106365) (@lem106364 n)). Qed.
Lemma lem106367 (n : nat) : (term47 n) = (term48 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem106368 (n : nat) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem106366 n) (@lem106367 n)). Qed.
Lemma lem106369 : term51 = term52.
Proof. exact (fun_ext (fun n : nat => @lem106368 n)). Qed.
Lemma lem106370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106371 : term53 = term54.
Proof. exact (MK_COMB (@lem106370) (@lem106369)). Qed.
Lemma lem106372 : term55 = term56.
Proof. exact (MK_COMB (@lem106363) (@lem106371)). Qed.
Lemma lem106373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem106374 : term57 = term58.
Proof. exact (MK_COMB (@lem106373) (@lem106372)). Qed.
Lemma lem106375 (n : nat) : (term43 n) = (term44 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem106376 : term59 = term38.
Proof. exact (fun_ext (fun n : nat => @lem106375 n)). Qed.
Lemma lem106377 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106378 : term60 = term61.
Proof. exact (MK_COMB (@lem106377) (@lem106376)). Qed.
Lemma lem106379 : term37 = term62.
Proof. exact (MK_COMB (@lem106374) (@lem106378)). Qed.
Lemma lem106380 : term62.
Proof. exact (EQ_MP (@lem106379) (@lem106360)). Qed.
Lemma lem106381 (n : nat) (h1 : term44 n) : term44 n.
Proof. exact (h1). Qed.
Lemma lem106383 (m : nat) : (term34 m) = term35.
Proof. exact (EQ_MP (@lem106356 m) (@lem106355 m)). Qed.
Lemma lem106384 : term63 = term35.
Proof. exact (@lem106383 term64). Qed.
Lemma lem106385 : term65 = term65.
Proof. exact (eq_refl term65). Qed.
Lemma lem106386 : term40 = term66.
Proof. exact (MK_COMB (@lem106385) (@lem106384)). Qed.
Lemma lem106387 : term66 = term40.
Proof. exact (SYM (@lem106386)). Qed.
Lemma lem106389 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (EQ_MP (@lem106352 m n) (@lem106351 m n)). Qed.
Lemma lem106390 (n : nat) : (term67 n) = (term68 n).
Proof. exact (@lem106389 term64 n). Qed.
Lemma lem106391 (n : nat) : (term69 n) = (term69 n).
Proof. exact (eq_refl (term69 n)). Qed.
Lemma lem106392 (n : nat) : (term48 n) = (term70 n).
Proof. exact (MK_COMB (@lem106391 n) (@lem106390 n)). Qed.
Lemma lem106393 (n : nat) : (term70 n) = (term48 n).
Proof. exact (SYM (@lem106392 n)). Qed.
Lemma lem106397 (m : nat) : (S m) = (term23 m).
Proof. exact (EQ_MP (@lem106342 m) (@lem106341 m)). Qed.
Lemma lem106398 (n : nat) : (S n) = (term23 n).
Proof. exact (@lem106397 n). Qed.
Lemma lem106399 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem106400 (n : nat) : (term69 n) = (term71 n).
Proof. exact (MK_COMB (@lem106399) (@lem106398 n)). Qed.
Lemma lem106402 (n : nat) : (term25 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem106345 n) (@lem106344 n)). Qed.
Lemma lem106403 (n : nat) : (term68 n) = (term72 n).
Proof. exact (@lem106402 (term73 n)). Qed.
Lemma lem106404 (n : nat) : (term70 n) = (term74 n).
Proof. exact (MK_COMB (@lem106400 n) (@lem106403 n)). Qed.
Lemma lem106405 (n : nat) : (term74 n) = (term70 n).
Proof. exact (SYM (@lem106404 n)). Qed.
Lemma lem106407 : term35 = term75.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem106408 : term65 = term65.
Proof. exact (eq_refl term65). Qed.
Lemma lem106409 : term66 = term76.
Proof. exact (MK_COMB (@lem106408) (@lem106407)). Qed.
Lemma lem106411 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem106335 m n) (@lem106334 m n)). Qed.
Lemma lem106412 : term76 = term77.
Proof. exact (@lem106411 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem106416 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem106417 (x : nat) : (x = x) = True.
Proof. exact (@lem106416 nat x). Qed.
Lemma lem106418 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem106417 (NUMERAL 0)). Qed.
Lemma lem106419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem106420 : term78 = (or True).
Proof. exact (MK_COMB (@lem106419) (@lem106418)). Qed.
Lemma lem106422 (m : nat) : (term21 m) = False.
Proof. exact (EQ_MP (@lem106339 m) (@lem106338 m)). Qed.
Lemma lem106423 : term79 = False.
Proof. exact (@lem106422 (NUMERAL 0)). Qed.
Lemma lem106424 : term77 = (True \/ False).
Proof. exact (MK_COMB (@lem106420) (@lem106423)). Qed.
Lemma lem106426 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem106427 : (True \/ False) = True.
Proof. exact (@lem106426 False). Qed.
Lemma lem106428 : term77 = True.
Proof. exact (TRANS (@lem106424) (@lem106427)). Qed.
Lemma lem106429 : term76 = True.
Proof. exact (TRANS (@lem106412) (@lem106428)). Qed.
Lemma lem106430 : term66 = True.
Proof. exact (TRANS (@lem106409) (@lem106429)). Qed.
Lemma lem106431 : True = term66.
Proof. exact (SYM (@lem106430)). Qed.
Lemma lem106434 : term35 = term75.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem106435 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem106436 (n : nat) : (term23 n) = (term80 n).
Proof. exact (MK_COMB (@lem106435 n) (@lem106434)). Qed.
Lemma lem106437 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem106438 (n : nat) : (term71 n) = (term81 n).
Proof. exact (MK_COMB (@lem106437) (@lem106436 n)). Qed.
Lemma lem106439 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem106440 (n : nat) : (term74 n) = (term82 n).
Proof. exact (MK_COMB (@lem106438 n) (@lem106439 n)). Qed.
Lemma lem106441 (n : nat) : (term82 n) = (term74 n).
Proof. exact (SYM (@lem106440 n)). Qed.
Lemma lem106443 (m : nat) (n : nat) (p : nat) (q : nat) : term8 m n p q.
Proof. exact (EQ_MP (@lem106328 m n p q) (@lem106327 m n p q)). Qed.
Lemma lem106444 (n : nat) : term83 n.
Proof. exact (@lem106443 n term75 (term73 n) (term73 n)). Qed.
Lemma lem106445 (m : nat) : term84 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem106446 (m : nat) : (term84 m) = (term85 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem106447 (m : nat) : term85 m.
Proof. exact (EQ_MP (@lem106446 m) (@lem106445 m)). Qed.
Lemma lem106448 (m : nat) (n : nat) : term86 m n.
Proof. exact (@lem106447 m n). Qed.
Lemma lem106449 (m : nat) (n : nat) : (term86 m n) = ((term87 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem106451 (n : nat) : (term44 n) = ((term44 n) = True).
Proof. exact (@lem7 (term44 n)). Qed.
Lemma lem106456 (n : nat) (h1 : term44 n) : (term44 n) = True.
Proof. exact (EQ_MP (@lem106451 n) (@lem106381 n h1)). Qed.
Lemma lem106457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106458 (n : nat) (h1 : term44 n) : (term88 n) = (and True).
Proof. exact (MK_COMB (@lem106457) (@lem106456 n h1)). Qed.
Lemma lem106460 (m : nat) (n : nat) : (term87 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem106449 m n) (@lem106448 m n)). Qed.
Lemma lem106461 (n : nat) : (term89 n) = (term90 n).
Proof. exact (@lem106460 (NUMERAL 0) (term73 n)). Qed.
Lemma lem106463 : term64 = term91.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem106464 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem106465 : term92 = term93.
Proof. exact (MK_COMB (@lem106464) (@lem106463)). Qed.
Lemma lem106466 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem106467 (n : nat) : (term73 n) = (term94 n).
Proof. exact (MK_COMB (@lem106465) (@lem106466 n)). Qed.
Lemma lem106468 : term65 = term65.
Proof. exact (eq_refl term65). Qed.
Lemma lem106469 (n : nat) : (term90 n) = (term95 n).
Proof. exact (MK_COMB (@lem106468) (@lem106467 n)). Qed.
Lemma lem106470 (n : nat) : (term89 n) = (term95 n).
Proof. exact (TRANS (@lem106461 n) (@lem106469 n)). Qed.
Lemma lem106471 (n : nat) (h1 : term44 n) : (term96 n) = (term97 n).
Proof. exact (MK_COMB (@lem106458 n h1) (@lem106470 n)). Qed.
Lemma lem106473 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem106474 (n : nat) : (term97 n) = (term95 n).
Proof. exact (@lem106473 (term95 n)). Qed.
Lemma lem106475 (n : nat) (h1 : term44 n) : (term96 n) = (term95 n).
Proof. exact (TRANS (@lem106471 n h1) (@lem106474 n)). Qed.
Lemma lem106476 (n : nat) (h1 : term44 n) : (term95 n) = (term96 n).
Proof. exact (SYM (@lem106475 n h1)). Qed.
Lemma lem106478 (p : Prop) : p = (term98 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem106479 (n : nat) : (term95 n) = (term99 n).
Proof. exact (@lem106478 (term95 n)). Qed.
Lemma lem106480 (n : nat) : (term99 n) = (term95 n).
Proof. exact (SYM (@lem106479 n)). Qed.
Lemma lem106481 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (h1). Qed.
Lemma lem106484 (n : nat) (h1 : term101 n) : term101 n.
Proof. exact (h1). Qed.
Lemma lem106485 (n : nat) : term102 n.
Proof. exact (fun h0 : term101 n => @lem106484 n h0). Qed.
Lemma lem106486 (n : nat) (h1 : term102 n) : term102 n.
Proof. exact (h1). Qed.
Lemma lem106487 (n : nat) (h1 : term101 n) : term101 n.
Proof. exact (h1). Qed.
Lemma lem106488 (n : nat) (h1 : term101 n) (h2 : term102 n) : term101 n.
Proof. exact (@lem106486 n h2 (@lem106487 n h1)). Qed.
Lemma lem106489 (n : nat) (h1 : term101 n) : term103 n.
Proof. exact (fun h0 : term102 n => @lem106488 n h1 h0). Qed.
Lemma lem106490 (n : nat) (h1 : term102 n) : term102 n.
Proof. exact (h1). Qed.
Lemma lem106491 (n : nat) (h1 : term101 n) (h2 : term102 n) : term101 n.
Proof. exact (@lem106489 n h1 (@lem106490 n h2)). Qed.
Lemma lem106492 (n : nat) (h1 : term102 n) : term102 n.
Proof. exact (fun h0 : term101 n => @lem106491 n h0 h1). Qed.
Lemma lem106493 (n : nat) : term104 n.
Proof. exact (fun h0 : term102 n => @lem106492 n h0). Qed.
Lemma lem106496 (n : nat) : term102 n.
Proof. exact (@lem106493 n (@lem106485 n)). Qed.
Lemma lem106558 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem106559 : term105 = term106.
Proof. exact (@lem106558 term107). Qed.
Lemma lem106570 : term108 = term108.
Proof. exact (eq_refl term108). Qed.
Lemma lem106571 : term109 = term110.
Proof. exact (MK_COMB (@lem106570) (@lem106559)). Qed.
Lemma lem106574 : term111 = term111.
Proof. exact (eq_refl term111). Qed.
Lemma lem106575 : term112 = term113.
Proof. exact (MK_COMB (@lem106574) (@lem106571)). Qed.
Lemma lem106578 (n : nat) : (term114 n) = (term114 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem106579 (n : nat) : (term101 n) = (term115 n).
Proof. exact (MK_COMB (@lem106578 n) (@lem106575)). Qed.
Lemma lem106582 : term116 = term117.
Proof. exact (fun_ext (fun n : nat => @lem106579 n)). Qed.
Lemma lem106583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106592 : term118 = term119.
Proof. exact (MK_COMB (@lem106583) (@lem106582)). Qed.
Lemma lem106603 (m : nat) (n : nat) : (((Nat.pow m n) = (NUMERAL 0)) = (term120 m n)) = (((Nat.pow m n) = (NUMERAL 0)) = (term120 m n)).
Proof. exact (eq_refl (((Nat.pow m n) = (NUMERAL 0)) = (term120 m n))). Qed.
Lemma lem106604 (m : nat) : (term121 m) = (term121 m).
Proof. exact (fun_ext (fun n : nat => @lem106603 m n)). Qed.
Lemma lem106605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106606 (m : nat) : (term122 m) = (term122 m).
Proof. exact (MK_COMB (@lem106605) (@lem106604 m)). Qed.
Lemma lem106607 : term123 = term123.
Proof. exact (fun_ext (fun m : nat => @lem106606 m)). Qed.
Lemma lem106608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106609 : term107 = term107.
Proof. exact (MK_COMB (@lem106608) (@lem106607)). Qed.
Lemma lem106610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem106611 : term106 = term106.
Proof. exact (MK_COMB (@lem106610) (@lem106609)). Qed.
Lemma lem106618 (n : nat) : (term124 n) = (term124 n).
Proof. exact (eq_refl (term124 n)). Qed.
Lemma lem106619 : term125 = term125.
Proof. exact (fun_ext (fun n : nat => @lem106618 n)). Qed.
Lemma lem106620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106621 : term126 = term126.
Proof. exact (MK_COMB (@lem106620) (@lem106619)). Qed.
Lemma lem106626 (n : nat) : (term127 n) = (term127 n).
Proof. exact (eq_refl (term127 n)). Qed.
Lemma lem106627 : term128 = term128.
Proof. exact (fun_ext (fun n : nat => @lem106626 n)). Qed.
Lemma lem106628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106629 : term129 = term129.
Proof. exact (MK_COMB (@lem106628) (@lem106627)). Qed.
Lemma lem106630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106631 : term130 = term130.
Proof. exact (MK_COMB (@lem106630) (@lem106629)). Qed.
Lemma lem106632 : term131 = term131.
Proof. exact (MK_COMB (@lem106631) (@lem106621)). Qed.
Lemma lem106637 (n : nat) : (term132 n) = (term132 n).
Proof. exact (eq_refl (term132 n)). Qed.
Lemma lem106638 : term133 = term133.
Proof. exact (fun_ext (fun n : nat => @lem106637 n)). Qed.
Lemma lem106639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106640 : term134 = term134.
Proof. exact (MK_COMB (@lem106639) (@lem106638)). Qed.
Lemma lem106641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106642 : term135 = term135.
Proof. exact (MK_COMB (@lem106641) (@lem106640)). Qed.
Lemma lem106643 : term136 = term136.
Proof. exact (MK_COMB (@lem106642) (@lem106632)). Qed.
Lemma lem106650 (n : nat) : (term137 n) = (term137 n).
Proof. exact (eq_refl (term137 n)). Qed.
Lemma lem106651 : term138 = term138.
Proof. exact (fun_ext (fun n : nat => @lem106650 n)). Qed.
Lemma lem106652 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106653 : term139 = term139.
Proof. exact (MK_COMB (@lem106652) (@lem106651)). Qed.
Lemma lem106654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106655 : term140 = term140.
Proof. exact (MK_COMB (@lem106654) (@lem106653)). Qed.
Lemma lem106656 : term141 = term141.
Proof. exact (MK_COMB (@lem106655) (@lem106643)). Qed.
Lemma lem106663 (n : nat) : (term142 n) = (term142 n).
Proof. exact (eq_refl (term142 n)). Qed.
Lemma lem106664 : term143 = term143.
Proof. exact (fun_ext (fun n : nat => @lem106663 n)). Qed.
Lemma lem106665 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106666 : term144 = term144.
Proof. exact (MK_COMB (@lem106665) (@lem106664)). Qed.
Lemma lem106667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106668 : term145 = term145.
Proof. exact (MK_COMB (@lem106667) (@lem106666)). Qed.
Lemma lem106669 : term146 = term146.
Proof. exact (MK_COMB (@lem106668) (@lem106656)). Qed.
Lemma lem106676 (n : nat) : (term147 n) = (term147 n).
Proof. exact (eq_refl (term147 n)). Qed.
Lemma lem106677 : term148 = term148.
Proof. exact (fun_ext (fun n : nat => @lem106676 n)). Qed.
Lemma lem106678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106679 : term149 = term149.
Proof. exact (MK_COMB (@lem106678) (@lem106677)). Qed.
Lemma lem106680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106681 : term150 = term150.
Proof. exact (MK_COMB (@lem106680) (@lem106679)). Qed.
Lemma lem106682 : term151 = term151.
Proof. exact (MK_COMB (@lem106681) (@lem106669)). Qed.
Lemma lem106683 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem106684 : term108 = term108.
Proof. exact (MK_COMB (@lem106683) (@lem106682)). Qed.
Lemma lem106685 : term110 = term110.
Proof. exact (MK_COMB (@lem106684) (@lem106611)). Qed.
Lemma lem106688 (n : nat) : (term152 n) = (term152 n).
Proof. exact (eq_refl (term152 n)). Qed.
Lemma lem106689 : term153 = term153.
Proof. exact (fun_ext (fun n : nat => @lem106688 n)). Qed.
Lemma lem106690 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106691 : term154 = term154.
Proof. exact (MK_COMB (@lem106690) (@lem106689)). Qed.
Lemma lem106692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem106693 : term111 = term111.
Proof. exact (MK_COMB (@lem106692) (@lem106691)). Qed.
Lemma lem106694 : term113 = term113.
Proof. exact (MK_COMB (@lem106693) (@lem106685)). Qed.
Lemma lem106699 (n : nat) : (term114 n) = (term114 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem106700 (n : nat) : (term115 n) = (term115 n).
Proof. exact (MK_COMB (@lem106699 n) (@lem106694)). Qed.
Lemma lem106701 : term117 = term117.
Proof. exact (fun_ext (fun n : nat => @lem106700 n)). Qed.
Lemma lem106702 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106703 : term119 = term119.
Proof. exact (MK_COMB (@lem106702) (@lem106701)). Qed.
Lemma lem106796 : term118 = term119.
Proof. exact (TRANS (@lem106592) (@lem106703)). Qed.
Lemma lem106797 : term119 = term118.
Proof. exact (SYM (@lem106796)). Qed.
Lemma lem106799 (h1 : term154) : term154.
Proof. exact (h1). Qed.
Lemma lem106800 (h1 : term151) : term151.
Proof. exact (h1). Qed.
Lemma lem106801 (h1 : term107) : term107.
Proof. exact (h1). Qed.
Lemma lem106807 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (h1). Qed.
Lemma lem106808 (n : nat) : (term152 n) = (term152 n).
Proof. exact (eq_refl (term152 n)). Qed.
Lemma lem106809 : term153 = term153.
Proof. exact (fun_ext (fun n : nat => @lem106808 n)). Qed.
Lemma lem106810 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106819 : term154 = term154.
Proof. exact (MK_COMB (@lem106810) (@lem106809)). Qed.
Lemma lem106820 (h1 : term154) : term154.
Proof. exact (EQ_MP (@lem106819) (@lem106799 h1)). Qed.
Lemma lem106823 (n : nat) : (term155 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem106824 (n : nat) : (term156 n) = (term156 n).
Proof. exact (eq_refl (term156 n)). Qed.
Lemma lem106825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem106826 (n : nat) : (term157 n) = (term158 n).
Proof. exact (MK_COMB (@lem106825) (@lem106823 n)). Qed.
Lemma lem106827 (n : nat) : (term159 n) = (term160 n).
Proof. exact (MK_COMB (@lem106826 n) (@lem106824 n)). Qed.
Lemma lem106828 (n : nat) : (term147 n) = (term159 n).
Proof. exact (@lem17265 (term161 n) (term156 n)). Qed.
Lemma lem106829 (n : nat) : (term147 n) = (term160 n).
Proof. exact (TRANS (@lem106828 n) (@lem106827 n)). Qed.
Lemma lem106830 : term148 = term162.
Proof. exact (fun_ext (fun n : nat => @lem106829 n)). Qed.
Lemma lem106831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106832 : term149 = term163.
Proof. exact (MK_COMB (@lem106831) (@lem106830)). Qed.
Lemma lem106835 (n : nat) : (term155 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem106836 (n : nat) : (term164 n) = (term164 n).
Proof. exact (eq_refl (term164 n)). Qed.
Lemma lem106837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem106838 (n : nat) : (term157 n) = (term158 n).
Proof. exact (MK_COMB (@lem106837) (@lem106835 n)). Qed.
Lemma lem106839 (n : nat) : (term165 n) = (term166 n).
Proof. exact (MK_COMB (@lem106838 n) (@lem106836 n)). Qed.
Lemma lem106840 (n : nat) : (term142 n) = (term165 n).
Proof. exact (@lem17265 (term161 n) (term164 n)). Qed.
Lemma lem106841 (n : nat) : (term142 n) = (term166 n).
Proof. exact (TRANS (@lem106840 n) (@lem106839 n)). Qed.
Lemma lem106842 : term143 = term167.
Proof. exact (fun_ext (fun n : nat => @lem106841 n)). Qed.
Lemma lem106843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106844 : term144 = term168.
Proof. exact (MK_COMB (@lem106843) (@lem106842)). Qed.
Lemma lem106851 (n : nat) : (term137 n) = (term169 n).
Proof. exact (@lem17265 (term156 n) (term161 n)). Qed.
Lemma lem106852 : term138 = term170.
Proof. exact (fun_ext (fun n : nat => @lem106851 n)). Qed.
Lemma lem106853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106854 : term139 = term171.
Proof. exact (MK_COMB (@lem106853) (@lem106852)). Qed.
Lemma lem106861 (n : nat) : (term132 n) = (term172 n).
Proof. exact (@lem17265 (term156 n) (term164 n)). Qed.
Lemma lem106862 : term133 = term173.
Proof. exact (fun_ext (fun n : nat => @lem106861 n)). Qed.
Lemma lem106863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106864 : term134 = term174.
Proof. exact (MK_COMB (@lem106863) (@lem106862)). Qed.
Lemma lem106871 (n : nat) : (term127 n) = (term175 n).
Proof. exact (@lem17265 (term164 n) (term156 n)). Qed.
Lemma lem106872 : term128 = term176.
Proof. exact (fun_ext (fun n : nat => @lem106871 n)). Qed.
Lemma lem106873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106874 : term129 = term177.
Proof. exact (MK_COMB (@lem106873) (@lem106872)). Qed.
Lemma lem106881 (n : nat) : (term124 n) = (term178 n).
Proof. exact (@lem17265 (term164 n) (term161 n)). Qed.
Lemma lem106882 : term125 = term179.
Proof. exact (fun_ext (fun n : nat => @lem106881 n)). Qed.
Lemma lem106883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem106884 : term126 = term180.
Proof. exact (MK_COMB (@lem106883) (@lem106882)). Qed.
Lemma lem106885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106886 : term130 = term181.
Proof. exact (MK_COMB (@lem106885) (@lem106874)). Qed.
Lemma lem106887 : term131 = term182.
Proof. exact (MK_COMB (@lem106886) (@lem106884)). Qed.
Lemma lem106888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106889 : term135 = term183.
Proof. exact (MK_COMB (@lem106888) (@lem106864)). Qed.
Lemma lem106890 : term136 = term184.
Proof. exact (MK_COMB (@lem106889) (@lem106887)). Qed.
Lemma lem106891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106892 : term140 = term185.
Proof. exact (MK_COMB (@lem106891) (@lem106854)). Qed.
Lemma lem106893 : term141 = term186.
Proof. exact (MK_COMB (@lem106892) (@lem106890)). Qed.
Lemma lem106894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106895 : term145 = term187.
Proof. exact (MK_COMB (@lem106894) (@lem106844)). Qed.
Lemma lem106896 : term146 = term188.
Proof. exact (MK_COMB (@lem106895) (@lem106893)). Qed.
Lemma lem106897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem106898 : term150 = term189.
Proof. exact (MK_COMB (@lem106897) (@lem106832)). Qed.
Lemma lem107191 : term151 = term190.
Proof. exact (MK_COMB (@lem106898) (@lem106896)). Qed.
Lemma lem107192 (h1 : term151) : term190.
Proof. exact (EQ_MP (@lem107191) (@lem106800 h1)). Qed.
Lemma lem107200 (n : nat) : (term155 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem107202 (m : nat) : (term191 m) = (term191 m).
Proof. exact (eq_refl (term191 m)). Qed.
Lemma lem107203 (m : nat) (n : nat) : (term192 m n) = (term193 m n).
Proof. exact (MK_COMB (@lem107202 m) (@lem107200 n)). Qed.
Lemma lem107204 (m : nat) (n : nat) : (term194 m n) = (term192 m n).
Proof. exact (@lem17045 (m = (NUMERAL 0)) (term161 n)). Qed.
Lemma lem107205 (m : nat) (n : nat) : (term194 m n) = (term193 m n).
Proof. exact (TRANS (@lem107204 m n) (@lem107203 m n)). Qed.
Lemma lem107211 (m : nat) (n : nat) : (term195 m n) = (term195 m n).
Proof. exact (eq_refl (term195 m n)). Qed.
Lemma lem107213 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem107214 (m : nat) (n : nat) : (term197 m n) = (term198 m n).
Proof. exact (MK_COMB (@lem107213 m n) (@lem107205 m n)). Qed.
Lemma lem107215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107216 (m : nat) (n : nat) : (term199 m n) = (term200 m n).
Proof. exact (MK_COMB (@lem107215) (@lem107214 m n)). Qed.
Lemma lem107217 (m : nat) (n : nat) : (term201 m n) = (term202 m n).
Proof. exact (MK_COMB (@lem107216 m n) (@lem107211 m n)). Qed.
Lemma lem107218 (m : nat) (n : nat) : (((Nat.pow m n) = (NUMERAL 0)) = (term120 m n)) = (term201 m n).
Proof. exact (@lem17784 ((Nat.pow m n) = (NUMERAL 0)) (term120 m n)). Qed.
Lemma lem107219 (m : nat) (n : nat) : (((Nat.pow m n) = (NUMERAL 0)) = (term120 m n)) = (term202 m n).
Proof. exact (TRANS (@lem107218 m n) (@lem107217 m n)). Qed.
Lemma lem107220 (m : nat) : (term121 m) = (term203 m).
Proof. exact (fun_ext (fun n : nat => @lem107219 m n)). Qed.
Lemma lem107221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107222 (m : nat) : (term122 m) = (term204 m).
Proof. exact (MK_COMB (@lem107221) (@lem107220 m)). Qed.
Lemma lem107223 : term123 = term205.
Proof. exact (fun_ext (fun m : nat => @lem107222 m)). Qed.
Lemma lem107224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107225 : term107 = term206.
Proof. exact (MK_COMB (@lem107224) (@lem107223)). Qed.
Lemma lem107231 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem107232 (P : nat -> Prop) (Q : nat -> Prop) : (term209 P Q) = (term210 P Q).
Proof. exact (@lem107231 nat P Q). Qed.
Lemma lem107233 (m : nat) : (term211 m) = (term212 m).
Proof. exact (@lem107232 (term213 m) (term214 m)). Qed.
Lemma lem107234 (m : nat) (n : nat) : (term215 m n) = (term198 m n).
Proof. exact (eq_refl (term215 m n)). Qed.
Lemma lem107235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107236 (m : nat) (n : nat) : (term216 m n) = (term200 m n).
Proof. exact (MK_COMB (@lem107235) (@lem107234 m n)). Qed.
Lemma lem107237 (m : nat) (n : nat) : (term217 m n) = (term195 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem107238 (m : nat) (n : nat) : (term218 m n) = (term202 m n).
Proof. exact (MK_COMB (@lem107236 m n) (@lem107237 m n)). Qed.
Lemma lem107239 (m : nat) : (term219 m) = (term203 m).
Proof. exact (fun_ext (fun n : nat => @lem107238 m n)). Qed.
Lemma lem107240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107241 (m : nat) : (term211 m) = (term204 m).
Proof. exact (MK_COMB (@lem107240) (@lem107239 m)). Qed.
Lemma lem107242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem107243 (m : nat) : (term220 m) = (term221 m).
Proof. exact (MK_COMB (@lem107242) (@lem107241 m)). Qed.
Lemma lem107244 (m : nat) (n : nat) : (term215 m n) = (term198 m n).
Proof. exact (eq_refl (term215 m n)). Qed.
Lemma lem107245 (m : nat) : (term222 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem107244 m n)). Qed.
Lemma lem107246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107247 (m : nat) : (term223 m) = (term224 m).
Proof. exact (MK_COMB (@lem107246) (@lem107245 m)). Qed.
Lemma lem107248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107249 (m : nat) : (term225 m) = (term226 m).
Proof. exact (MK_COMB (@lem107248) (@lem107247 m)). Qed.
Lemma lem107250 (m : nat) (n : nat) : (term217 m n) = (term195 m n).
Proof. exact (eq_refl (term217 m n)). Qed.
Lemma lem107251 (m : nat) : (term227 m) = (term214 m).
Proof. exact (fun_ext (fun n : nat => @lem107250 m n)). Qed.
Lemma lem107252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107253 (m : nat) : (term228 m) = (term229 m).
Proof. exact (MK_COMB (@lem107252) (@lem107251 m)). Qed.
Lemma lem107254 (m : nat) : (term212 m) = (term230 m).
Proof. exact (MK_COMB (@lem107249 m) (@lem107253 m)). Qed.
Lemma lem107255 (m : nat) : ((term211 m) = (term212 m)) = ((term204 m) = (term230 m)).
Proof. exact (MK_COMB (@lem107243 m) (@lem107254 m)). Qed.
Lemma lem107256 (m : nat) : (term204 m) = (term230 m).
Proof. exact (EQ_MP (@lem107255 m) (@lem107233 m)). Qed.
Lemma lem107353 : term205 = term231.
Proof. exact (fun_ext (fun m : nat => @lem107256 m)). Qed.
Lemma lem107354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107355 : term206 = term232.
Proof. exact (MK_COMB (@lem107354) (@lem107353)). Qed.
Lemma lem107357 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem107358 (P : nat -> Prop) (Q : nat -> Prop) : (term209 P Q) = (term210 P Q).
Proof. exact (@lem107357 nat P Q). Qed.
Lemma lem107359 : term233 = term234.
Proof. exact (@lem107358 term235 term236). Qed.
Lemma lem107360 (m : nat) : (term237 m) = (term224 m).
Proof. exact (eq_refl (term237 m)). Qed.
Lemma lem107361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107362 (m : nat) : (term238 m) = (term226 m).
Proof. exact (MK_COMB (@lem107361) (@lem107360 m)). Qed.
Lemma lem107363 (m : nat) : (term239 m) = (term229 m).
Proof. exact (eq_refl (term239 m)). Qed.
Lemma lem107364 (m : nat) : (term240 m) = (term230 m).
Proof. exact (MK_COMB (@lem107362 m) (@lem107363 m)). Qed.
Lemma lem107365 : term241 = term231.
Proof. exact (fun_ext (fun m : nat => @lem107364 m)). Qed.
Lemma lem107366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107367 : term233 = term232.
Proof. exact (MK_COMB (@lem107366) (@lem107365)). Qed.
Lemma lem107368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem107369 : term242 = term243.
Proof. exact (MK_COMB (@lem107368) (@lem107367)). Qed.
Lemma lem107370 (m : nat) : (term237 m) = (term224 m).
Proof. exact (eq_refl (term237 m)). Qed.
Lemma lem107371 : term244 = term235.
Proof. exact (fun_ext (fun m : nat => @lem107370 m)). Qed.
Lemma lem107372 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107373 : term245 = term246.
Proof. exact (MK_COMB (@lem107372) (@lem107371)). Qed.
Lemma lem107374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107375 : term247 = term248.
Proof. exact (MK_COMB (@lem107374) (@lem107373)). Qed.
Lemma lem107376 (m : nat) : (term239 m) = (term229 m).
Proof. exact (eq_refl (term239 m)). Qed.
Lemma lem107377 : term249 = term236.
Proof. exact (fun_ext (fun m : nat => @lem107376 m)). Qed.
Lemma lem107378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107379 : term250 = term251.
Proof. exact (MK_COMB (@lem107378) (@lem107377)). Qed.
Lemma lem107380 : term234 = term252.
Proof. exact (MK_COMB (@lem107375) (@lem107379)). Qed.
Lemma lem107381 : (term233 = term234) = (term232 = term252).
Proof. exact (MK_COMB (@lem107369) (@lem107380)). Qed.
Lemma lem107382 : term232 = term252.
Proof. exact (EQ_MP (@lem107381) (@lem107359)). Qed.
Lemma lem107489 : term206 = term252.
Proof. exact (TRANS (@lem107355) (@lem107382)). Qed.
Lemma lem107490 : term107 = term252.
Proof. exact (TRANS (@lem107225) (@lem107489)). Qed.
Lemma lem107491 (h1 : term107) : term252.
Proof. exact (EQ_MP (@lem107490) (@lem106801 h1)). Qed.
Lemma lem107511 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (h1). Qed.
Lemma lem107522 (n : nat) : (term152 n) = (term152 n).
Proof. exact (eq_refl (term152 n)). Qed.
Lemma lem107523 : term153 = term153.
Proof. exact (fun_ext (fun n : nat => @lem107522 n)). Qed.
Lemma lem107524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107525 : term154 = term154.
Proof. exact (MK_COMB (@lem107524) (@lem107523)). Qed.
Lemma lem107526 (h1 : term154) : term154.
Proof. exact (EQ_MP (@lem107525) (@lem106820 h1)). Qed.
Lemma lem107549 (n : nat) : (term178 n) = (term178 n).
Proof. exact (eq_refl (term178 n)). Qed.
Lemma lem107550 : term179 = term179.
Proof. exact (fun_ext (fun n : nat => @lem107549 n)). Qed.
Lemma lem107551 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107552 : term180 = term180.
Proof. exact (MK_COMB (@lem107551) (@lem107550)). Qed.
Lemma lem107573 (n : nat) : (term175 n) = (term175 n).
Proof. exact (eq_refl (term175 n)). Qed.
Lemma lem107574 : term176 = term176.
Proof. exact (fun_ext (fun n : nat => @lem107573 n)). Qed.
Lemma lem107575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107576 : term177 = term177.
Proof. exact (MK_COMB (@lem107575) (@lem107574)). Qed.
Lemma lem107577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107578 : term181 = term181.
Proof. exact (MK_COMB (@lem107577) (@lem107576)). Qed.
Lemma lem107579 : term182 = term182.
Proof. exact (MK_COMB (@lem107578) (@lem107552)). Qed.
Lemma lem107600 (n : nat) : (term172 n) = (term172 n).
Proof. exact (eq_refl (term172 n)). Qed.
Lemma lem107601 : term173 = term173.
Proof. exact (fun_ext (fun n : nat => @lem107600 n)). Qed.
Lemma lem107602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107603 : term174 = term174.
Proof. exact (MK_COMB (@lem107602) (@lem107601)). Qed.
Lemma lem107604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107605 : term183 = term183.
Proof. exact (MK_COMB (@lem107604) (@lem107603)). Qed.
Lemma lem107606 : term184 = term184.
Proof. exact (MK_COMB (@lem107605) (@lem107579)). Qed.
Lemma lem107627 (n : nat) : (term169 n) = (term169 n).
Proof. exact (eq_refl (term169 n)). Qed.
Lemma lem107628 : term170 = term170.
Proof. exact (fun_ext (fun n : nat => @lem107627 n)). Qed.
Lemma lem107629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107630 : term171 = term171.
Proof. exact (MK_COMB (@lem107629) (@lem107628)). Qed.
Lemma lem107631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107632 : term185 = term185.
Proof. exact (MK_COMB (@lem107631) (@lem107630)). Qed.
Lemma lem107633 : term186 = term186.
Proof. exact (MK_COMB (@lem107632) (@lem107606)). Qed.
Lemma lem107652 (n : nat) : (term166 n) = (term166 n).
Proof. exact (eq_refl (term166 n)). Qed.
Lemma lem107653 : term167 = term167.
Proof. exact (fun_ext (fun n : nat => @lem107652 n)). Qed.
Lemma lem107654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107655 : term168 = term168.
Proof. exact (MK_COMB (@lem107654) (@lem107653)). Qed.
Lemma lem107656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107657 : term187 = term187.
Proof. exact (MK_COMB (@lem107656) (@lem107655)). Qed.
Lemma lem107658 : term188 = term188.
Proof. exact (MK_COMB (@lem107657) (@lem107633)). Qed.
Lemma lem107675 (n : nat) : (term160 n) = (term160 n).
Proof. exact (eq_refl (term160 n)). Qed.
Lemma lem107676 : term162 = term162.
Proof. exact (fun_ext (fun n : nat => @lem107675 n)). Qed.
Lemma lem107677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107678 : term163 = term163.
Proof. exact (MK_COMB (@lem107677) (@lem107676)). Qed.
Lemma lem107679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107680 : term189 = term189.
Proof. exact (MK_COMB (@lem107679) (@lem107678)). Qed.
Lemma lem107681 : term190 = term190.
Proof. exact (MK_COMB (@lem107680) (@lem107658)). Qed.
Lemma lem107682 (h1 : term151) : term190.
Proof. exact (EQ_MP (@lem107681) (@lem107192 h1)). Qed.
Lemma lem107717 (m : nat) (n : nat) : (term195 m n) = (term195 m n).
Proof. exact (eq_refl (term195 m n)). Qed.
Lemma lem107718 (m : nat) : (term214 m) = (term214 m).
Proof. exact (fun_ext (fun n : nat => @lem107717 m n)). Qed.
Lemma lem107719 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107720 (m : nat) : (term229 m) = (term229 m).
Proof. exact (MK_COMB (@lem107719) (@lem107718 m)). Qed.
Lemma lem107721 : term236 = term236.
Proof. exact (fun_ext (fun m : nat => @lem107720 m)). Qed.
Lemma lem107722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107723 : term251 = term251.
Proof. exact (MK_COMB (@lem107722) (@lem107721)). Qed.
Lemma lem107756 (m : nat) (n : nat) : (term198 m n) = (term198 m n).
Proof. exact (eq_refl (term198 m n)). Qed.
Lemma lem107757 (m : nat) : (term213 m) = (term213 m).
Proof. exact (fun_ext (fun n : nat => @lem107756 m n)). Qed.
Lemma lem107758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107759 (m : nat) : (term224 m) = (term224 m).
Proof. exact (MK_COMB (@lem107758) (@lem107757 m)). Qed.
Lemma lem107760 : term235 = term235.
Proof. exact (fun_ext (fun m : nat => @lem107759 m)). Qed.
Lemma lem107761 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107762 : term246 = term246.
Proof. exact (MK_COMB (@lem107761) (@lem107760)). Qed.
Lemma lem107763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem107764 : term248 = term248.
Proof. exact (MK_COMB (@lem107763) (@lem107762)). Qed.
Lemma lem107765 : term252 = term252.
Proof. exact (MK_COMB (@lem107764) (@lem107723)). Qed.
Lemma lem107766 (h1 : term107) : term252.
Proof. exact (EQ_MP (@lem107765) (@lem107491 h1)). Qed.
Lemma lem107767 (h1 : term107) : term251.
Proof. exact (proj2 (@lem107766 h1)). Qed.
Lemma lem107770 (h1 : term151) : term163.
Proof. exact (proj1 (@lem107682 h1)). Qed.
Lemma lem107782 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (h1). Qed.
Lemma lem107784 (n : nat) : (term152 n) = (term152 n).
Proof. exact (eq_refl (term152 n)). Qed.
Lemma lem107785 : term153 = term153.
Proof. exact (fun_ext (fun n : nat => @lem107784 n)). Qed.
Lemma lem107786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107788 : term154 = term154.
Proof. exact (MK_COMB (@lem107786) (@lem107785)). Qed.
Lemma lem107789 (h1 : term154) : term154.
Proof. exact (EQ_MP (@lem107788) (@lem107526 h1)). Qed.
Lemma lem107829 (m : nat) (n : nat) : (term195 m n) = (term253 m n).
Proof. exact (@lem19490 (m = (NUMERAL 0)) (term254 m n) (term161 n)). Qed.
Lemma lem107830 (m : nat) : (term214 m) = (term255 m).
Proof. exact (fun_ext (fun n : nat => @lem107829 m n)). Qed.
Lemma lem107831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107832 (m : nat) : (term229 m) = (term256 m).
Proof. exact (MK_COMB (@lem107831) (@lem107830 m)). Qed.
Lemma lem107833 : term236 = term257.
Proof. exact (fun_ext (fun m : nat => @lem107832 m)). Qed.
Lemma lem107834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107836 : term251 = term258.
Proof. exact (MK_COMB (@lem107834) (@lem107833)). Qed.
Lemma lem107837 (h1 : term107) : term258.
Proof. exact (EQ_MP (@lem107836) (@lem107767 h1)). Qed.
Lemma lem107845 (n : nat) : (term160 n) = (term160 n).
Proof. exact (eq_refl (term160 n)). Qed.
Lemma lem107846 : term162 = term162.
Proof. exact (fun_ext (fun n : nat => @lem107845 n)). Qed.
Lemma lem107847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem107849 : term163 = term163.
Proof. exact (MK_COMB (@lem107847) (@lem107846)). Qed.
Lemma lem107850 (h1 : term151) : term163.
Proof. exact (EQ_MP (@lem107849) (@lem107770 h1)). Qed.
Lemma lem107916 (_2328 : nat) (h1 : term154) : term259 _2328.
Proof. exact (@lem107789 h1 _2328). Qed.
Lemma lem107917 (_2328 : nat) : (term259 _2328) = (term152 _2328).
Proof. exact (eq_refl (term259 _2328)). Qed.
Lemma lem107925 (_2331 : nat) (h1 : term107) : term260 _2331.
Proof. exact (@lem107837 h1 _2331). Qed.
Lemma lem107926 (_2331 : nat) : (term260 _2331) = (term256 _2331).
Proof. exact (eq_refl (term260 _2331)). Qed.
Lemma lem107927 (_2331 : nat) (h1 : term107) : term256 _2331.
Proof. exact (EQ_MP (@lem107926 _2331) (@lem107925 _2331 h1)). Qed.
Lemma lem107928 (_2331 : nat) (_2332 : nat) (h1 : term107) : term261 _2331 _2332.
Proof. exact (@lem107927 _2331 h1 _2332). Qed.
Lemma lem107929 (_2331 : nat) (_2332 : nat) : (term261 _2331 _2332) = (term253 _2331 _2332).
Proof. exact (eq_refl (term261 _2331 _2332)). Qed.
Lemma lem107930 (_2331 : nat) (_2332 : nat) (h1 : term107) : term253 _2331 _2332.
Proof. exact (EQ_MP (@lem107929 _2331 _2332) (@lem107928 _2331 _2332 h1)). Qed.
Lemma lem107931 (_2333 : nat) (h1 : term151) : term262 _2333.
Proof. exact (@lem107850 h1 _2333). Qed.
Lemma lem107932 (_2333 : nat) : (term262 _2333) = (term160 _2333).
Proof. exact (eq_refl (term262 _2333)). Qed.
Lemma lem107952 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (h1). Qed.
Lemma lem107954 (_2328 : nat) (h1 : term154) : term152 _2328.
Proof. exact (EQ_MP (@lem107917 _2328) (@lem107916 _2328 h1)). Qed.
Lemma lem107970 (_2333 : nat) (h1 : term151) : term160 _2333.
Proof. exact (EQ_MP (@lem107932 _2333) (@lem107931 _2333 h1)). Qed.
Lemma lem108006 (_2332 : nat) (_2331 : nat) (h1 : term107) : term263 _2332 _2331.
Proof. exact (proj1 (@lem107930 _2331 _2332 h1)). Qed.
Lemma lem108093 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (h1). Qed.
Lemma lem108094 (n : nat) (h1 : term100 n) : term264 n.
Proof. exact (fun h0 : term95 n => @lem108093 n h1). Qed.
Lemma lem108096 (p : Prop) : (term265 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem108097 (n : nat) : (term264 n) = (term100 n).
Proof. exact (@lem108096 (term95 n)). Qed.
Lemma lem108098 (n : nat) (h1 : term100 n) : term100 n.
Proof. exact (EQ_MP (@lem108097 n) (@lem108094 n h1)). Qed.
Lemma lem108100 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem108103 (_2333 : nat) : (term160 _2333) = (term267 _2333).
Proof. exact (@lem108100 (term156 _2333) (_2333 = (NUMERAL 0))). Qed.
Lemma lem108106 (_2333 : nat) (h1 : term151) : term267 _2333.
Proof. exact (EQ_MP (@lem108103 _2333) (@lem107970 _2333 h1)). Qed.
Lemma lem108107 (n : nat) (h1 : term151) : term268 n.
Proof. exact (@lem108106 (term94 n) h1). Qed.
Lemma lem108110 (n : nat) (h1 : term100 n) (h2 : term151) : (term94 n) = (NUMERAL 0).
Proof. exact (@lem108107 n h2 (@lem108098 n h1)). Qed.
Lemma lem108111 (n : nat) (h1 : term100 n) (h2 : term151) : term269 n.
Proof. exact (fun h0 : term270 n => @lem108110 n h1 h2). Qed.
Lemma lem108113 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem108114 (n : nat) : (term269 n) = ((term94 n) = (NUMERAL 0)).
Proof. exact (@lem108113 ((term94 n) = (NUMERAL 0))). Qed.
Lemma lem108115 (n : nat) (h1 : term100 n) (h2 : term151) : (term94 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem108114 n) (@lem108111 n h1 h2)). Qed.
Lemma lem108121 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem108122 (_2331 : nat) (_2332 : nat) : (term263 _2332 _2331) = (term272 _2331 _2332).
Proof. exact (@lem108121 (_2331 = (NUMERAL 0)) (term254 _2331 _2332)). Qed.
Lemma lem108132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem108133 (_2331 : nat) (_2332 : nat) : (term273 _2332 _2331) = (term274 _2331 _2332).
Proof. exact (MK_COMB (@lem108132) (@lem108122 _2331 _2332)). Qed.
Lemma lem108143 (_2331 : nat) (_2332 : nat) : (term272 _2331 _2332) = (term272 _2331 _2332).
Proof. exact (eq_refl (term272 _2331 _2332)). Qed.
Lemma lem108144 (_2331 : nat) (_2332 : nat) : ((term263 _2332 _2331) = (term272 _2331 _2332)) = ((term272 _2331 _2332) = (term272 _2331 _2332)).
Proof. exact (MK_COMB (@lem108133 _2331 _2332) (@lem108143 _2331 _2332)). Qed.
Lemma lem108146 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem108147 (x : Prop) : (x = x) = True.
Proof. exact (@lem108146 Prop x). Qed.
Lemma lem108148 (_2331 : nat) (_2332 : nat) : ((term272 _2331 _2332) = (term272 _2331 _2332)) = True.
Proof. exact (@lem108147 (term272 _2331 _2332)). Qed.
Lemma lem108149 (_2331 : nat) (_2332 : nat) : ((term263 _2332 _2331) = (term272 _2331 _2332)) = True.
Proof. exact (TRANS (@lem108144 _2331 _2332) (@lem108148 _2331 _2332)). Qed.
Lemma lem108150 (_2331 : nat) (_2332 : nat) : True = ((term263 _2332 _2331) = (term272 _2331 _2332)).
Proof. exact (SYM (@lem108149 _2331 _2332)). Qed.
Lemma lem108151 (_2331 : nat) (_2332 : nat) : (term263 _2332 _2331) = (term272 _2331 _2332).
Proof. exact (EQ_MP (@lem108150 _2331 _2332) (@lem0)). Qed.
Lemma lem108152 (_2331 : nat) (_2332 : nat) (h1 : term107) : term272 _2331 _2332.
Proof. exact (EQ_MP (@lem108151 _2331 _2332) (@lem108006 _2332 _2331 h1)). Qed.
Lemma lem108154 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem108155 (_2332 : nat) (_2331 : nat) : (term272 _2331 _2332) = (term275 _2332 _2331).
Proof. exact (@lem108154 (term254 _2331 _2332) (_2331 = (NUMERAL 0))). Qed.
Lemma lem108157 (a : Prop) : (term276 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem108158 (_2331 : nat) (_2332 : nat) : (term277 _2331 _2332) = ((Nat.pow _2331 _2332) = (NUMERAL 0)).
Proof. exact (@lem108157 ((Nat.pow _2331 _2332) = (NUMERAL 0))). Qed.
Lemma lem108159 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem108160 (_2331 : nat) (_2332 : nat) : (term278 _2331 _2332) = (term279 _2331 _2332).
Proof. exact (MK_COMB (@lem108159) (@lem108158 _2331 _2332)). Qed.
Lemma lem108161 (_2331 : nat) : (_2331 = (NUMERAL 0)) = (_2331 = (NUMERAL 0)).
Proof. exact (eq_refl (_2331 = (NUMERAL 0))). Qed.
Lemma lem108162 (_2332 : nat) (_2331 : nat) : (term275 _2332 _2331) = (term280 _2332 _2331).
Proof. exact (MK_COMB (@lem108160 _2331 _2332) (@lem108161 _2331)). Qed.
Lemma lem108163 (_2332 : nat) (_2331 : nat) : (term272 _2331 _2332) = (term280 _2332 _2331).
Proof. exact (TRANS (@lem108155 _2332 _2331) (@lem108162 _2332 _2331)). Qed.
Lemma lem108166 (_2332 : nat) (_2331 : nat) (h1 : term107) : term280 _2332 _2331.
Proof. exact (EQ_MP (@lem108163 _2332 _2331) (@lem108152 _2331 _2332 h1)). Qed.
Lemma lem108167 (n : nat) (h1 : term107) : term281 n.
Proof. exact (@lem108166 n term91 h1). Qed.
Lemma lem108170 (n : nat) (h1 : term107) (h2 : term100 n) (h3 : term151) : term91 = (NUMERAL 0).
Proof. exact (@lem108167 n h1 (@lem108115 n h2 h3)). Qed.
Lemma lem108171 (n : nat) (h1 : term107) (h2 : term100 n) (h3 : term151) : term282.
Proof. exact (fun h0 : term283 => @lem108170 n h1 h2 h3). Qed.
Lemma lem108173 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem108174 : term282 = (term91 = (NUMERAL 0)).
Proof. exact (@lem108173 (term91 = (NUMERAL 0))). Qed.
Lemma lem108175 (n : nat) (h1 : term107) (h2 : term100 n) (h3 : term151) : term91 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem108174) (@lem108171 n h1 h2 h3)). Qed.
Lemma lem108178 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem108180 (_2328 : nat) : (term152 _2328) = (term284 _2328).
Proof. exact (@lem108178 ((S _2328) = (NUMERAL 0))). Qed.
Lemma lem108183 (_2328 : nat) (h1 : term154) : term284 _2328.
Proof. exact (EQ_MP (@lem108180 _2328) (@lem107954 _2328 h1)). Qed.
Lemma lem108184 (h1 : term154) : term285.
Proof. exact (@lem108183 term35 h1). Qed.
Lemma lem108187 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (@lem108184 h2 (@lem108175 n h1 h3 h4)). Qed.
Lemma lem108188 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : term286.
Proof. exact (fun h0 : ~ False => @lem108187 n h1 h2 h3 h4). Qed.
Lemma lem108190 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem108191 : term286 = False.
Proof. exact (@lem108190 False). Qed.
Lemma lem108192 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108191) (@lem108188 n h1 h2 h3 h4)). Qed.
Lemma lem108193 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : (term100 n) = False.
Proof. exact (prop_ext (fun h5 : term100 n => @lem108192 n h1 h2 h3 h4) (fun h5 : False => @lem107952 n h3)). Qed.
Lemma lem108194 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108193 n h1 h2 h3 h4) (@lem107952 n h3)). Qed.
Lemma lem108195 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : (term100 n) = False.
Proof. exact (prop_ext (fun h5 : term100 n => @lem108194 n h1 h2 h3 h4) (fun h5 : False => @lem107782 n h3)). Qed.
Lemma lem108196 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108195 n h1 h2 h3 h4) (@lem107782 n h3)). Qed.
Lemma lem108197 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : term154 = False.
Proof. exact (prop_ext (fun h5 : term154 => @lem108196 n h1 h2 h3 h4) (fun h5 : False => @lem107789 h2)). Qed.
Lemma lem108198 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108197 n h1 h2 h3 h4) (@lem107789 h2)). Qed.
Lemma lem108199 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : (term100 n) = False.
Proof. exact (prop_ext (fun h5 : term100 n => @lem108198 n h1 h2 h3 h4) (fun h5 : False => @lem107782 n h3)). Qed.
Lemma lem108200 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108199 n h1 h2 h3 h4) (@lem107782 n h3)). Qed.
Lemma lem108201 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : term154 = False.
Proof. exact (prop_ext (fun h5 : term154 => @lem108200 n h1 h2 h3 h4) (fun h5 : False => @lem107526 h2)). Qed.
Lemma lem108202 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108201 n h1 h2 h3 h4) (@lem107526 h2)). Qed.
Lemma lem108203 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : (term100 n) = False.
Proof. exact (prop_ext (fun h5 : term100 n => @lem108202 n h1 h2 h3 h4) (fun h5 : False => @lem107511 n h3)). Qed.
Lemma lem108204 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108203 n h1 h2 h3 h4) (@lem107511 n h3)). Qed.
Lemma lem108205 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : term154 = False.
Proof. exact (prop_ext (fun h5 : term154 => @lem108204 n h1 h2 h3 h4) (fun h5 : False => @lem106820 h2)). Qed.
Lemma lem108206 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108205 n h1 h2 h3 h4) (@lem106820 h2)). Qed.
Lemma lem108207 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : (term100 n) = False.
Proof. exact (prop_ext (fun h5 : term100 n => @lem108206 n h1 h2 h3 h4) (fun h5 : False => @lem106807 n h3)). Qed.
Lemma lem108208 (n : nat) (h1 : term107) (h2 : term154) (h3 : term100 n) (h4 : term151) : False.
Proof. exact (EQ_MP (@lem108207 n h1 h2 h3 h4) (@lem106807 n h3)). Qed.
Lemma lem108209 (n : nat) (h1 : term154) (h2 : term100 n) (h3 : term151) : term105.
Proof. exact (fun h0 : term107 => @lem108208 n h0 h1 h2 h3). Qed.
Lemma lem108210 : term105 = term106.
Proof. exact (@lem69 term107). Qed.
Lemma lem108211 (n : nat) (h1 : term154) (h2 : term100 n) (h3 : term151) : term106.
Proof. exact (EQ_MP (@lem108210) (@lem108209 n h1 h2 h3)). Qed.
Lemma lem108212 (n : nat) (h1 : term154) (h2 : term100 n) : term110.
Proof. exact (fun h0 : term151 => @lem108211 n h1 h2 h0). Qed.
Lemma lem108213 (n : nat) (h1 : term100 n) : term113.
Proof. exact (fun h0 : term154 => @lem108212 n h0 h1). Qed.
Lemma lem108214 (n : nat) : term115 n.
Proof. exact (fun h0 : term100 n => @lem108213 n h0). Qed.
Lemma lem108219 : term119.
Proof. exact (fun n : nat => @lem108214 n). Qed.
Lemma lem108220 : term118.
Proof. exact (EQ_MP (@lem106797) (@lem108219)). Qed.
Lemma lem108221 (n : nat) : term287 n.
Proof. exact (@lem108220 n). Qed.
Lemma lem108222 (n : nat) : (term287 n) = (term101 n).
Proof. exact (eq_refl (term287 n)). Qed.
Lemma lem108223 (n : nat) : term101 n.
Proof. exact (EQ_MP (@lem108222 n) (@lem108221 n)). Qed.
Lemma lem108225 (n : nat) : term101 n.
Proof. exact (@lem106496 n (@lem108223 n)). Qed.
Lemma lem108226 (n : nat) (h1 : term100 n) : term112.
Proof. exact (@lem108225 n (@lem106481 n h1)). Qed.
Lemma lem108227 (n : nat) (h1 : term100 n) : term109.
Proof. exact (@lem108226 n h1 (@lem75570)). Qed.
Lemma lem108228 (n : nat) (h1 : term100 n) : term105.
Proof. exact (@lem108227 n h1 (@lem99082)). Qed.
Lemma lem108229 (n : nat) (h1 : term100 n) : False.
Proof. exact (@lem108228 n h1 (@lem86997)). Qed.
Lemma lem108230 (n : nat) (h1 : term100 n) : (term100 n) = False.
Proof. exact (prop_ext (fun h2 : term100 n => @lem108229 n h1) (fun h2 : False => @lem106481 n h1)). Qed.
Lemma lem108231 (n : nat) (h1 : term100 n) : False.
Proof. exact (EQ_MP (@lem108230 n h1) (@lem106481 n h1)). Qed.
Lemma lem108232 (n : nat) : term99 n.
Proof. exact (fun h0 : term100 n => @lem108231 n h0). Qed.
Lemma lem108233 (n : nat) : term95 n.
Proof. exact (EQ_MP (@lem106480 n) (@lem108232 n)). Qed.
Lemma lem108234 (n : nat) (h1 : term44 n) : term96 n.
Proof. exact (EQ_MP (@lem106476 n h1) (@lem108233 n)). Qed.
Lemma lem108235 (n : nat) (h1 : term44 n) : term82 n.
Proof. exact (@lem106444 n (@lem108234 n h1)). Qed.
Lemma lem108236 (n : nat) (h1 : term44 n) : term74 n.
Proof. exact (EQ_MP (@lem106441 n) (@lem108235 n h1)). Qed.
Lemma lem108237 (n : nat) (h1 : term44 n) : term70 n.
Proof. exact (EQ_MP (@lem106405 n) (@lem108236 n h1)). Qed.
Lemma lem108238 : term66.
Proof. exact (EQ_MP (@lem106431) (@lem0)). Qed.
Lemma lem108239 (n : nat) (h1 : term44 n) : term48 n.
Proof. exact (EQ_MP (@lem106393 n) (@lem108237 n h1)). Qed.
Lemma lem108240 : term40.
Proof. exact (EQ_MP (@lem106387) (@lem108238)). Qed.
Lemma lem108241 (n : nat) : term50 n.
Proof. exact (fun h0 : term44 n => @lem108239 n h0). Qed.
Lemma lem108246 : term54.
Proof. exact (fun n : nat => @lem108241 n). Qed.
Lemma lem108247 : term56.
Proof. exact (conj (@lem108240) (@lem108246)). Qed.
Lemma lem108248 : term61.
Proof. exact (@lem106380 (@lem108247)). Qed.
