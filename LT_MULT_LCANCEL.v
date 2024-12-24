Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_MULT_LCANCEL_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import LT_0_spec.
Require Import LT_ADD_LCANCEL_spec.
Require Import LT_REFL_spec.
Require Import LT_SUC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem104290 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem104292 : term1.
Proof. exact (proj2 (@lem104290)). Qed.
Lemma lem104294 : term2.
Proof. exact (proj2 (@lem104292)). Qed.
Lemma lem104296 : term3.
Proof. exact (proj2 (@lem104294)). Qed.
Lemma lem104299 : term4.
Proof. exact (proj1 (@lem104296)). Qed.
Lemma lem104302 (m : nat) (n : nat) (h1 : (term5 m n) = (term6 m n)) : (term5 m n) = (term6 m n).
Proof. exact (h1). Qed.
Lemma lem104303 (m : nat) (n : nat) (h1 : (term5 m n) = (term6 m n)) : (term6 m n) = (term5 m n).
Proof. exact (SYM (@lem104302 m n h1)). Qed.
Lemma lem104304 (m : nat) (n : nat) (h1 : (term6 m n) = (term5 m n)) : (term6 m n) = (term5 m n).
Proof. exact (h1). Qed.
Lemma lem104305 (m : nat) (n : nat) (h1 : (term6 m n) = (term5 m n)) : (term5 m n) = (term6 m n).
Proof. exact (SYM (@lem104304 m n h1)). Qed.
Lemma lem104306 (m : nat) (n : nat) : ((term5 m n) = (term6 m n)) = ((term6 m n) = (term5 m n)).
Proof. exact (prop_ext (fun h1 : (term5 m n) = (term6 m n) => @lem104303 m n h1) (fun h1 : (term6 m n) = (term5 m n) => @lem104305 m n h1)). Qed.
Lemma lem104307 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem104306 m n)). Qed.
Lemma lem104308 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104309 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem104308) (@lem104307 m)). Qed.
Lemma lem104310 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem104309 m)). Qed.
Lemma lem104311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104312 : term4 = term13.
Proof. exact (MK_COMB (@lem104311) (@lem104310)). Qed.
Lemma lem104313 : term13.
Proof. exact (EQ_MP (@lem104312) (@lem104299)). Qed.
Lemma lem104317 (m : nat) (n : nat) (p : nat) (h1 : (term14 m n p) = (term15 m n p)) : (term14 m n p) = (term15 m n p).
Proof. exact (h1). Qed.
Lemma lem104318 (m : nat) (n : nat) (p : nat) (h1 : (term14 m n p) = (term15 m n p)) : (term15 m n p) = (term14 m n p).
Proof. exact (SYM (@lem104317 m n p h1)). Qed.
Lemma lem104319 (m : nat) (n : nat) (p : nat) (h1 : (term15 m n p) = (term14 m n p)) : (term15 m n p) = (term14 m n p).
Proof. exact (h1). Qed.
Lemma lem104320 (m : nat) (n : nat) (p : nat) (h1 : (term15 m n p) = (term14 m n p)) : (term14 m n p) = (term15 m n p).
Proof. exact (SYM (@lem104319 m n p h1)). Qed.
Lemma lem104321 (m : nat) (n : nat) (p : nat) : ((term14 m n p) = (term15 m n p)) = ((term15 m n p) = (term14 m n p)).
Proof. exact (prop_ext (fun h1 : (term14 m n p) = (term15 m n p) => @lem104318 m n p h1) (fun h1 : (term15 m n p) = (term14 m n p) => @lem104320 m n p h1)). Qed.
Lemma lem104322 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (fun_ext (fun p : nat => @lem104321 m n p)). Qed.
Lemma lem104323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104324 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem104323) (@lem104322 m n)). Qed.
Lemma lem104325 (m : nat) : (term20 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem104324 m n)). Qed.
Lemma lem104326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104327 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem104326) (@lem104325 m)). Qed.
Lemma lem104328 : term24 = term25.
Proof. exact (fun_ext (fun m : nat => @lem104327 m)). Qed.
Lemma lem104329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104330 : term26 = term27.
Proof. exact (MK_COMB (@lem104329) (@lem104328)). Qed.
Lemma lem104331 : term27.
Proof. exact (EQ_MP (@lem104330) (@lem77960)). Qed.
Lemma lem104332 (m : nat) : term28 m.
Proof. exact (@lem104331 m). Qed.
Lemma lem104333 (m : nat) : (term28 m) = (term23 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem104334 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem104333 m) (@lem104332 m)). Qed.
Lemma lem104335 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem104334 m n). Qed.
Lemma lem104336 (m : nat) (n : nat) : (term29 m n) = (term19 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem104337 (m : nat) (n : nat) : term19 m n.
Proof. exact (EQ_MP (@lem104336 m n) (@lem104335 m n)). Qed.
Lemma lem104338 (m : nat) (n : nat) (p : nat) : term30 m n p.
Proof. exact (@lem104337 m n p). Qed.
Lemma lem104339 (m : nat) (n : nat) (p : nat) : (term30 m n p) = ((term15 m n p) = (term14 m n p)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem104341 (m : nat) : term31 m.
Proof. exact (@lem101108 m). Qed.
Lemma lem104342 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem104343 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem104342 m) (@lem104341 m)). Qed.
Lemma lem104344 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem104343 m n). Qed.
Lemma lem104345 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem104346 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem104345 m n) (@lem104344 m n)). Qed.
Lemma lem104347 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (@lem104346 m n p). Qed.
Lemma lem104348 (m : nat) (n : nat) (p : nat) : (term35 m n p) = ((term36 n m p) = (Peano.lt n p)).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem104357 : term37.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem104358 (m : nat) : term38 m.
Proof. exact (@lem104357 m). Qed.
Lemma lem104359 (m : nat) : (term38 m) = ((term39 m) = False).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem104361 (m : nat) : term40 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem104362 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem104363 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem104362 m) (@lem104361 m)). Qed.
Lemma lem104364 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem104363 m n). Qed.
Lemma lem104365 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem104368 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104369 : term45.
Proof. exact (@lem104368 term46). Qed.
Lemma lem104370 : term47 = term48.
Proof. exact (eq_refl term47). Qed.
Lemma lem104371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104372 : term49 = term50.
Proof. exact (MK_COMB (@lem104371) (@lem104370)). Qed.
Lemma lem104373 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem104374 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104375 (m : nat) : (term53 m) = (term54 m).
Proof. exact (MK_COMB (@lem104374) (@lem104373 m)). Qed.
Lemma lem104376 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem104377 (m : nat) : (term57 m) = (term58 m).
Proof. exact (MK_COMB (@lem104375 m) (@lem104376 m)). Qed.
Lemma lem104378 : term59 = term60.
Proof. exact (fun_ext (fun m : nat => @lem104377 m)). Qed.
Lemma lem104379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104380 : term61 = term62.
Proof. exact (MK_COMB (@lem104379) (@lem104378)). Qed.
Lemma lem104381 : term63 = term64.
Proof. exact (MK_COMB (@lem104372) (@lem104380)). Qed.
Lemma lem104382 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104383 : term65 = term66.
Proof. exact (MK_COMB (@lem104382) (@lem104381)). Qed.
Lemma lem104384 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem104385 : term67 = term46.
Proof. exact (fun_ext (fun m : nat => @lem104384 m)). Qed.
Lemma lem104386 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104387 : term68 = term69.
Proof. exact (MK_COMB (@lem104386) (@lem104385)). Qed.
Lemma lem104388 : term45 = term70.
Proof. exact (MK_COMB (@lem104383) (@lem104387)). Qed.
Lemma lem104389 : term70.
Proof. exact (EQ_MP (@lem104388) (@lem104369)). Qed.
Lemma lem104392 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104393 : term71.
Proof. exact (@lem104392 term72). Qed.
Lemma lem104394 : term73 = term74.
Proof. exact (eq_refl term73). Qed.
Lemma lem104395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104396 : term75 = term76.
Proof. exact (MK_COMB (@lem104395) (@lem104394)). Qed.
Lemma lem104397 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem104398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104399 (n : nat) : (term79 n) = (term80 n).
Proof. exact (MK_COMB (@lem104398) (@lem104397 n)). Qed.
Lemma lem104400 (n : nat) : (term81 n) = (term82 n).
Proof. exact (eq_refl (term81 n)). Qed.
Lemma lem104401 (n : nat) : (term83 n) = (term84 n).
Proof. exact (MK_COMB (@lem104399 n) (@lem104400 n)). Qed.
Lemma lem104402 : term85 = term86.
Proof. exact (fun_ext (fun n : nat => @lem104401 n)). Qed.
Lemma lem104403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104404 : term87 = term88.
Proof. exact (MK_COMB (@lem104403) (@lem104402)). Qed.
Lemma lem104405 : term89 = term90.
Proof. exact (MK_COMB (@lem104396) (@lem104404)). Qed.
Lemma lem104406 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104407 : term91 = term92.
Proof. exact (MK_COMB (@lem104406) (@lem104405)). Qed.
Lemma lem104408 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem104409 : term93 = term72.
Proof. exact (fun_ext (fun n : nat => @lem104408 n)). Qed.
Lemma lem104410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104411 : term94 = term48.
Proof. exact (MK_COMB (@lem104410) (@lem104409)). Qed.
Lemma lem104412 : term71 = term95.
Proof. exact (MK_COMB (@lem104407) (@lem104411)). Qed.
Lemma lem104413 : term95.
Proof. exact (EQ_MP (@lem104412) (@lem104393)). Qed.
Lemma lem104416 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104417 : term96.
Proof. exact (@lem104416 term97). Qed.
Lemma lem104418 : term98 = (term99 = term100).
Proof. exact (eq_refl term98). Qed.
Lemma lem104419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104420 : term101 = term102.
Proof. exact (MK_COMB (@lem104419) (@lem104418)). Qed.
Lemma lem104421 (p : nat) : (term103 p) = ((term104 p) = (term105 p)).
Proof. exact (eq_refl (term103 p)). Qed.
Lemma lem104422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104423 (p : nat) : (term106 p) = (term107 p).
Proof. exact (MK_COMB (@lem104422) (@lem104421 p)). Qed.
Lemma lem104424 (p : nat) : (term108 p) = ((term109 p) = (term110 p)).
Proof. exact (eq_refl (term108 p)). Qed.
Lemma lem104425 (p : nat) : (term111 p) = (term112 p).
Proof. exact (MK_COMB (@lem104423 p) (@lem104424 p)). Qed.
Lemma lem104426 : term113 = term114.
Proof. exact (fun_ext (fun p : nat => @lem104425 p)). Qed.
Lemma lem104427 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104428 : term115 = term116.
Proof. exact (MK_COMB (@lem104427) (@lem104426)). Qed.
Lemma lem104429 : term117 = term118.
Proof. exact (MK_COMB (@lem104420) (@lem104428)). Qed.
Lemma lem104430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104431 : term119 = term120.
Proof. exact (MK_COMB (@lem104430) (@lem104429)). Qed.
Lemma lem104432 (p : nat) : (term103 p) = ((term104 p) = (term105 p)).
Proof. exact (eq_refl (term103 p)). Qed.
Lemma lem104433 : term121 = term97.
Proof. exact (fun_ext (fun p : nat => @lem104432 p)). Qed.
Lemma lem104434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104435 : term122 = term74.
Proof. exact (MK_COMB (@lem104434) (@lem104433)). Qed.
Lemma lem104436 : term96 = term123.
Proof. exact (MK_COMB (@lem104431) (@lem104435)). Qed.
Lemma lem104437 : term123.
Proof. exact (EQ_MP (@lem104436) (@lem104417)). Qed.
Lemma lem104444 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104445 (n : nat) : term124 n.
Proof. exact (@lem104444 (term125 n)). Qed.
Lemma lem104446 (n : nat) : (term126 n) = ((term127 n) = (term128 n)).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem104447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104448 (n : nat) : (term129 n) = (term130 n).
Proof. exact (MK_COMB (@lem104447) (@lem104446 n)). Qed.
Lemma lem104449 (n : nat) (p : nat) : (term131 n p) = ((term132 n p) = (term133 n p)).
Proof. exact (eq_refl (term131 n p)). Qed.
Lemma lem104450 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104451 (n : nat) (p : nat) : (term134 n p) = (term135 n p).
Proof. exact (MK_COMB (@lem104450) (@lem104449 n p)). Qed.
Lemma lem104452 (n : nat) (p : nat) : (term136 n p) = ((term137 n p) = (term138 n p)).
Proof. exact (eq_refl (term136 n p)). Qed.
Lemma lem104453 (n : nat) (p : nat) : (term139 n p) = (term140 n p).
Proof. exact (MK_COMB (@lem104451 n p) (@lem104452 n p)). Qed.
Lemma lem104454 (n : nat) : (term141 n) = (term142 n).
Proof. exact (fun_ext (fun p : nat => @lem104453 n p)). Qed.
Lemma lem104455 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104456 (n : nat) : (term143 n) = (term144 n).
Proof. exact (MK_COMB (@lem104455) (@lem104454 n)). Qed.
Lemma lem104457 (n : nat) : (term145 n) = (term146 n).
Proof. exact (MK_COMB (@lem104448 n) (@lem104456 n)). Qed.
Lemma lem104458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104459 (n : nat) : (term147 n) = (term148 n).
Proof. exact (MK_COMB (@lem104458) (@lem104457 n)). Qed.
Lemma lem104460 (n : nat) (p : nat) : (term131 n p) = ((term132 n p) = (term133 n p)).
Proof. exact (eq_refl (term131 n p)). Qed.
Lemma lem104461 (n : nat) : (term149 n) = (term125 n).
Proof. exact (fun_ext (fun p : nat => @lem104460 n p)). Qed.
Lemma lem104462 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104463 (n : nat) : (term150 n) = (term82 n).
Proof. exact (MK_COMB (@lem104462) (@lem104461 n)). Qed.
Lemma lem104464 (n : nat) : (term124 n) = (term151 n).
Proof. exact (MK_COMB (@lem104459 n) (@lem104463 n)). Qed.
Lemma lem104465 (n : nat) : term151 n.
Proof. exact (EQ_MP (@lem104464 n) (@lem104445 n)). Qed.
Lemma lem104472 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104473 (m : nat) : term152 m.
Proof. exact (@lem104472 (term153 m)). Qed.
Lemma lem104474 (m : nat) : (term154 m) = (term155 m).
Proof. exact (eq_refl (term154 m)). Qed.
Lemma lem104475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104476 (m : nat) : (term156 m) = (term157 m).
Proof. exact (MK_COMB (@lem104475) (@lem104474 m)). Qed.
Lemma lem104477 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem104478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104479 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (MK_COMB (@lem104478) (@lem104477 m n)). Qed.
Lemma lem104480 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem104481 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem104479 m n) (@lem104480 m n)). Qed.
Lemma lem104482 (m : nat) : (term166 m) = (term167 m).
Proof. exact (fun_ext (fun n : nat => @lem104481 m n)). Qed.
Lemma lem104483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104484 (m : nat) : (term168 m) = (term169 m).
Proof. exact (MK_COMB (@lem104483) (@lem104482 m)). Qed.
Lemma lem104485 (m : nat) : (term170 m) = (term171 m).
Proof. exact (MK_COMB (@lem104476 m) (@lem104484 m)). Qed.
Lemma lem104486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104487 (m : nat) : (term172 m) = (term173 m).
Proof. exact (MK_COMB (@lem104486) (@lem104485 m)). Qed.
Lemma lem104488 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem104489 (m : nat) : (term174 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem104488 m n)). Qed.
Lemma lem104490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104491 (m : nat) : (term175 m) = (term56 m).
Proof. exact (MK_COMB (@lem104490) (@lem104489 m)). Qed.
Lemma lem104492 (m : nat) : (term152 m) = (term176 m).
Proof. exact (MK_COMB (@lem104487 m) (@lem104491 m)). Qed.
Lemma lem104493 (m : nat) : term176 m.
Proof. exact (EQ_MP (@lem104492 m) (@lem104473 m)). Qed.
Lemma lem104494 (m : nat) (n : nat) (h1 : term159 m n) : term159 m n.
Proof. exact (h1). Qed.
Lemma lem104496 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104497 (m : nat) : term177 m.
Proof. exact (@lem104496 (term178 m)). Qed.
Lemma lem104498 (m : nat) : (term179 m) = ((term180 m) = (term181 m)).
Proof. exact (eq_refl (term179 m)). Qed.
Lemma lem104499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104500 (m : nat) : (term182 m) = (term183 m).
Proof. exact (MK_COMB (@lem104499) (@lem104498 m)). Qed.
Lemma lem104501 (m : nat) (p : nat) : (term184 m p) = ((term185 m p) = (term186 m p)).
Proof. exact (eq_refl (term184 m p)). Qed.
Lemma lem104502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104503 (m : nat) (p : nat) : (term187 m p) = (term188 m p).
Proof. exact (MK_COMB (@lem104502) (@lem104501 m p)). Qed.
Lemma lem104504 (m : nat) (p : nat) : (term189 m p) = ((term190 m p) = (term191 m p)).
Proof. exact (eq_refl (term189 m p)). Qed.
Lemma lem104505 (m : nat) (p : nat) : (term192 m p) = (term193 m p).
Proof. exact (MK_COMB (@lem104503 m p) (@lem104504 m p)). Qed.
Lemma lem104506 (m : nat) : (term194 m) = (term195 m).
Proof. exact (fun_ext (fun p : nat => @lem104505 m p)). Qed.
Lemma lem104507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104508 (m : nat) : (term196 m) = (term197 m).
Proof. exact (MK_COMB (@lem104507) (@lem104506 m)). Qed.
Lemma lem104509 (m : nat) : (term198 m) = (term199 m).
Proof. exact (MK_COMB (@lem104500 m) (@lem104508 m)). Qed.
Lemma lem104510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104511 (m : nat) : (term200 m) = (term201 m).
Proof. exact (MK_COMB (@lem104510) (@lem104509 m)). Qed.
Lemma lem104512 (m : nat) (p : nat) : (term184 m p) = ((term185 m p) = (term186 m p)).
Proof. exact (eq_refl (term184 m p)). Qed.
Lemma lem104513 (m : nat) : (term202 m) = (term178 m).
Proof. exact (fun_ext (fun p : nat => @lem104512 m p)). Qed.
Lemma lem104514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104515 (m : nat) : (term203 m) = (term155 m).
Proof. exact (MK_COMB (@lem104514) (@lem104513 m)). Qed.
Lemma lem104516 (m : nat) : (term177 m) = (term204 m).
Proof. exact (MK_COMB (@lem104511 m) (@lem104515 m)). Qed.
Lemma lem104517 (m : nat) : term204 m.
Proof. exact (EQ_MP (@lem104516 m) (@lem104497 m)). Qed.
Lemma lem104524 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem104525 (m : nat) (n : nat) : term205 m n.
Proof. exact (@lem104524 (term206 m n)). Qed.
Lemma lem104526 (m : nat) (n : nat) : (term207 m n) = ((term208 n m) = (term209 m n)).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem104527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104528 (m : nat) (n : nat) : (term210 m n) = (term211 m n).
Proof. exact (MK_COMB (@lem104527) (@lem104526 m n)). Qed.
Lemma lem104529 (m : nat) (n : nat) (p : nat) : (term212 m n p) = ((term213 n m p) = (term214 m n p)).
Proof. exact (eq_refl (term212 m n p)). Qed.
Lemma lem104530 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104531 (m : nat) (n : nat) (p : nat) : (term215 m n p) = (term216 m n p).
Proof. exact (MK_COMB (@lem104530) (@lem104529 m n p)). Qed.
Lemma lem104532 (m : nat) (n : nat) (p : nat) : (term217 m n p) = ((term218 n m p) = (term219 m n p)).
Proof. exact (eq_refl (term217 m n p)). Qed.
Lemma lem104533 (m : nat) (n : nat) (p : nat) : (term220 m n p) = (term221 m n p).
Proof. exact (MK_COMB (@lem104531 m n p) (@lem104532 m n p)). Qed.
Lemma lem104534 (m : nat) (n : nat) : (term222 m n) = (term223 m n).
Proof. exact (fun_ext (fun p : nat => @lem104533 m n p)). Qed.
Lemma lem104535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104536 (m : nat) (n : nat) : (term224 m n) = (term225 m n).
Proof. exact (MK_COMB (@lem104535) (@lem104534 m n)). Qed.
Lemma lem104537 (m : nat) (n : nat) : (term226 m n) = (term227 m n).
Proof. exact (MK_COMB (@lem104528 m n) (@lem104536 m n)). Qed.
Lemma lem104538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem104539 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (MK_COMB (@lem104538) (@lem104537 m n)). Qed.
Lemma lem104540 (m : nat) (n : nat) (p : nat) : (term212 m n p) = ((term213 n m p) = (term214 m n p)).
Proof. exact (eq_refl (term212 m n p)). Qed.
Lemma lem104541 (m : nat) (n : nat) : (term230 m n) = (term206 m n).
Proof. exact (fun_ext (fun p : nat => @lem104540 m n p)). Qed.
Lemma lem104542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem104543 (m : nat) (n : nat) : (term231 m n) = (term163 m n).
Proof. exact (MK_COMB (@lem104542) (@lem104541 m n)). Qed.
Lemma lem104544 (m : nat) (n : nat) : (term205 m n) = (term232 m n).
Proof. exact (MK_COMB (@lem104539 m n) (@lem104543 m n)). Qed.
Lemma lem104545 (m : nat) (n : nat) : term232 m n.
Proof. exact (EQ_MP (@lem104544 m n) (@lem104525 m n)). Qed.
Lemma lem104572 (n : nat) : term233 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem104573 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem104574 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem104573 n) (@lem104572 n)). Qed.
Lemma lem104575 (n : nat) : term235 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem104638 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem104575 n (@lem104574 n)). Qed.
Lemma lem104639 : term99 = False.
Proof. exact (@lem104638 term236). Qed.
Lemma lem104640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104641 : term237 = (@eq Prop False).
Proof. exact (MK_COMB (@lem104640) (@lem104639)). Qed.
Lemma lem104645 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem104646 (x : nat) : (x = x) = True.
Proof. exact (@lem104645 nat x). Qed.
Lemma lem104647 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem104646 (NUMERAL 0)). Qed.
Lemma lem104648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem104649 : term238 = (~ True).
Proof. exact (MK_COMB (@lem104648) (@lem104647)). Qed.
Lemma lem104651 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem104652 : term238 = False.
Proof. exact (TRANS (@lem104649) (@lem104651)). Qed.
Lemma lem104653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104654 : term239 = (and False).
Proof. exact (MK_COMB (@lem104653) (@lem104652)). Qed.
Lemma lem104656 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem104575 n (@lem104574 n)). Qed.
Lemma lem104657 : term240 = False.
Proof. exact (@lem104656 (NUMERAL 0)). Qed.
Lemma lem104658 : term100 = (False /\ False).
Proof. exact (MK_COMB (@lem104654) (@lem104657)). Qed.
Lemma lem104660 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem104661 : (False /\ False) = False.
Proof. exact (@lem104660 False). Qed.
Lemma lem104662 : term100 = False.
Proof. exact (TRANS (@lem104658) (@lem104661)). Qed.
Lemma lem104663 : (term99 = term100) = (False = False).
Proof. exact (MK_COMB (@lem104641) (@lem104662)). Qed.
Lemma lem104665 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem104666 : (False = False) = (~ False).
Proof. exact (@lem104665 False). Qed.
Lemma lem104668 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem104669 : (False = False) = True.
Proof. exact (TRANS (@lem104666) (@lem104668)). Qed.
Lemma lem104670 : (term99 = term100) = True.
Proof. exact (TRANS (@lem104663) (@lem104669)). Qed.
Lemma lem104671 : True = (term99 = term100).
Proof. exact (SYM (@lem104670)). Qed.
Lemma lem104672 : term99 = term100.
Proof. exact (EQ_MP (@lem104671) (@lem0)). Qed.
Lemma lem104689 (n : nat) : term241 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem104690 (n : nat) : (term241 n) = (term242 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem104691 (n : nat) : term242 n.
Proof. exact (EQ_MP (@lem104690 n) (@lem104689 n)). Qed.
Lemma lem104692 (n : nat) : (term242 n) = ((term242 n) = True).
Proof. exact (@lem7 (term242 n)). Qed.
Lemma lem104694 (n : nat) : term233 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem104695 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem104696 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem104695 n) (@lem104694 n)). Qed.
Lemma lem104697 (n : nat) : term235 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem104753 : term243.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem104754 (n : nat) : term244 n.
Proof. exact (@lem104753 n). Qed.
Lemma lem104755 (n : nat) : (term244 n) = ((term245 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term244 n)). Qed.
Lemma lem104762 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem104755 n) (@lem104754 n)). Qed.
Lemma lem104763 : term236 = (NUMERAL 0).
Proof. exact (@lem104762 (NUMERAL 0)). Qed.
Lemma lem104764 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem104765 : term246 = term247.
Proof. exact (MK_COMB (@lem104764) (@lem104763)). Qed.
Lemma lem104767 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem104755 n) (@lem104754 n)). Qed.
Lemma lem104768 (p : nat) : (term248 p) = (NUMERAL 0).
Proof. exact (@lem104767 (S p)). Qed.
Lemma lem104769 (p : nat) : (term109 p) = term240.
Proof. exact (MK_COMB (@lem104765) (@lem104768 p)). Qed.
Lemma lem104771 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem104697 n (@lem104696 n)). Qed.
Lemma lem104772 : term240 = False.
Proof. exact (@lem104771 (NUMERAL 0)). Qed.
Lemma lem104773 (p : nat) : (term109 p) = False.
Proof. exact (TRANS (@lem104769 p) (@lem104772)). Qed.
Lemma lem104774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104775 (p : nat) : (term249 p) = (@eq Prop False).
Proof. exact (MK_COMB (@lem104774) (@lem104773 p)). Qed.
Lemma lem104779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem104780 (x : nat) : (x = x) = True.
Proof. exact (@lem104779 nat x). Qed.
Lemma lem104781 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem104780 (NUMERAL 0)). Qed.
Lemma lem104782 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem104783 : term238 = (~ True).
Proof. exact (MK_COMB (@lem104782) (@lem104781)). Qed.
Lemma lem104785 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem104786 : term238 = False.
Proof. exact (TRANS (@lem104783) (@lem104785)). Qed.
Lemma lem104787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104788 : term239 = (and False).
Proof. exact (MK_COMB (@lem104787) (@lem104786)). Qed.
Lemma lem104790 (n : nat) : (term242 n) = True.
Proof. exact (EQ_MP (@lem104692 n) (@lem104691 n)). Qed.
Lemma lem104791 (p : nat) : (term242 p) = True.
Proof. exact (@lem104790 p). Qed.
Lemma lem104792 (p : nat) : (term110 p) = (False /\ True).
Proof. exact (MK_COMB (@lem104788) (@lem104791 p)). Qed.
Lemma lem104794 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem104795 : (False /\ True) = False.
Proof. exact (@lem104794 True). Qed.
Lemma lem104796 (p : nat) : (term110 p) = False.
Proof. exact (TRANS (@lem104792 p) (@lem104795)). Qed.
Lemma lem104797 (p : nat) : ((term109 p) = (term110 p)) = (False = False).
Proof. exact (MK_COMB (@lem104775 p) (@lem104796 p)). Qed.
Lemma lem104799 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem104800 : (False = False) = (~ False).
Proof. exact (@lem104799 False). Qed.
Lemma lem104802 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem104803 : (False = False) = True.
Proof. exact (TRANS (@lem104800) (@lem104802)). Qed.
Lemma lem104804 (p : nat) : ((term109 p) = (term110 p)) = True.
Proof. exact (TRANS (@lem104797 p) (@lem104803)). Qed.
Lemma lem104805 (p : nat) : True = ((term109 p) = (term110 p)).
Proof. exact (SYM (@lem104804 p)). Qed.
Lemma lem104806 (p : nat) : (term109 p) = (term110 p).
Proof. exact (EQ_MP (@lem104805 p) (@lem0)). Qed.
Lemma lem104828 (n : nat) : term233 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem104829 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem104830 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem104829 n) (@lem104828 n)). Qed.
Lemma lem104831 (n : nat) : term235 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem104887 : term243.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem104888 (n : nat) : term244 n.
Proof. exact (@lem104887 n). Qed.
Lemma lem104889 (n : nat) : (term244 n) = ((term245 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term244 n)). Qed.
Lemma lem104899 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem104889 n) (@lem104888 n)). Qed.
Lemma lem104900 (n : nat) : (term248 n) = (NUMERAL 0).
Proof. exact (@lem104899 (S n)). Qed.
Lemma lem104901 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem104902 (n : nat) : (term250 n) = term247.
Proof. exact (MK_COMB (@lem104901) (@lem104900 n)). Qed.
Lemma lem104904 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem104889 n) (@lem104888 n)). Qed.
Lemma lem104905 : term236 = (NUMERAL 0).
Proof. exact (@lem104904 (NUMERAL 0)). Qed.
Lemma lem104906 (n : nat) : (term127 n) = term240.
Proof. exact (MK_COMB (@lem104902 n) (@lem104905)). Qed.
Lemma lem104908 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem104831 n (@lem104830 n)). Qed.
Lemma lem104909 : term240 = False.
Proof. exact (@lem104908 (NUMERAL 0)). Qed.
Lemma lem104910 (n : nat) : (term127 n) = False.
Proof. exact (TRANS (@lem104906 n) (@lem104909)). Qed.
Lemma lem104911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104912 (n : nat) : (term251 n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem104911) (@lem104910 n)). Qed.
Lemma lem104916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem104917 (x : nat) : (x = x) = True.
Proof. exact (@lem104916 nat x). Qed.
Lemma lem104918 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem104917 (NUMERAL 0)). Qed.
Lemma lem104919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem104920 : term238 = (~ True).
Proof. exact (MK_COMB (@lem104919) (@lem104918)). Qed.
Lemma lem104922 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem104923 : term238 = False.
Proof. exact (TRANS (@lem104920) (@lem104922)). Qed.
Lemma lem104924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem104925 : term239 = (and False).
Proof. exact (MK_COMB (@lem104924) (@lem104923)). Qed.
Lemma lem104928 (n : nat) : (term252 n) = (term252 n).
Proof. exact (eq_refl (term252 n)). Qed.
Lemma lem104929 (n : nat) : (term128 n) = (term253 n).
Proof. exact (MK_COMB (@lem104925) (@lem104928 n)). Qed.
Lemma lem104931 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem104932 (n : nat) : (term253 n) = False.
Proof. exact (@lem104931 (term252 n)). Qed.
Lemma lem104933 (n : nat) : (term128 n) = False.
Proof. exact (TRANS (@lem104929 n) (@lem104932 n)). Qed.
Lemma lem104934 (n : nat) : ((term127 n) = (term128 n)) = (False = False).
Proof. exact (MK_COMB (@lem104912 n) (@lem104933 n)). Qed.
Lemma lem104936 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem104937 : (False = False) = (~ False).
Proof. exact (@lem104936 False). Qed.
Lemma lem104939 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem104940 : (False = False) = True.
Proof. exact (TRANS (@lem104937) (@lem104939)). Qed.
Lemma lem104941 (n : nat) : ((term127 n) = (term128 n)) = True.
Proof. exact (TRANS (@lem104934 n) (@lem104940)). Qed.
Lemma lem104942 (n : nat) : True = ((term127 n) = (term128 n)).
Proof. exact (SYM (@lem104941 n)). Qed.
Lemma lem104943 (n : nat) : (term127 n) = (term128 n).
Proof. exact (EQ_MP (@lem104942 n) (@lem0)). Qed.
Lemma lem104965 (n : nat) : term233 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem104966 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem104967 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem104966 n) (@lem104965 n)). Qed.
Lemma lem104968 (n : nat) : term235 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem105024 : term243.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem105025 (n : nat) : term244 n.
Proof. exact (@lem105024 n). Qed.
Lemma lem105026 (n : nat) : (term244 n) = ((term245 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term244 n)). Qed.
Lemma lem105036 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem105026 n) (@lem105025 n)). Qed.
Lemma lem105037 (n : nat) : (term248 n) = (NUMERAL 0).
Proof. exact (@lem105036 (S n)). Qed.
Lemma lem105038 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105039 (n : nat) : (term250 n) = term247.
Proof. exact (MK_COMB (@lem105038) (@lem105037 n)). Qed.
Lemma lem105041 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem105026 n) (@lem105025 n)). Qed.
Lemma lem105042 (p : nat) : (term248 p) = (NUMERAL 0).
Proof. exact (@lem105041 (S p)). Qed.
Lemma lem105043 (n : nat) (p : nat) : (term137 n p) = term240.
Proof. exact (MK_COMB (@lem105039 n) (@lem105042 p)). Qed.
Lemma lem105045 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem104968 n (@lem104967 n)). Qed.
Lemma lem105046 : term240 = False.
Proof. exact (@lem105045 (NUMERAL 0)). Qed.
Lemma lem105047 (n : nat) (p : nat) : (term137 n p) = False.
Proof. exact (TRANS (@lem105043 n p) (@lem105046)). Qed.
Lemma lem105048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105049 (n : nat) (p : nat) : (term254 n p) = (@eq Prop False).
Proof. exact (MK_COMB (@lem105048) (@lem105047 n p)). Qed.
Lemma lem105053 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem105054 (x : nat) : (x = x) = True.
Proof. exact (@lem105053 nat x). Qed.
Lemma lem105055 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem105054 (NUMERAL 0)). Qed.
Lemma lem105056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem105057 : term238 = (~ True).
Proof. exact (MK_COMB (@lem105056) (@lem105055)). Qed.
Lemma lem105059 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem105060 : term238 = False.
Proof. exact (TRANS (@lem105057) (@lem105059)). Qed.
Lemma lem105061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem105062 : term239 = (and False).
Proof. exact (MK_COMB (@lem105061) (@lem105060)). Qed.
Lemma lem105065 (n : nat) (p : nat) : (term43 n p) = (term43 n p).
Proof. exact (eq_refl (term43 n p)). Qed.
Lemma lem105066 (n : nat) (p : nat) : (term138 n p) = (term255 n p).
Proof. exact (MK_COMB (@lem105062) (@lem105065 n p)). Qed.
Lemma lem105068 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem105069 (n : nat) (p : nat) : (term255 n p) = False.
Proof. exact (@lem105068 (term43 n p)). Qed.
Lemma lem105070 (n : nat) (p : nat) : (term138 n p) = False.
Proof. exact (TRANS (@lem105066 n p) (@lem105069 n p)). Qed.
Lemma lem105071 (n : nat) (p : nat) : ((term137 n p) = (term138 n p)) = (False = False).
Proof. exact (MK_COMB (@lem105049 n p) (@lem105070 n p)). Qed.
Lemma lem105073 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem105074 : (False = False) = (~ False).
Proof. exact (@lem105073 False). Qed.
Lemma lem105076 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105077 : (False = False) = True.
Proof. exact (TRANS (@lem105074) (@lem105076)). Qed.
Lemma lem105078 (n : nat) (p : nat) : ((term137 n p) = (term138 n p)) = True.
Proof. exact (TRANS (@lem105071 n p) (@lem105077)). Qed.
Lemma lem105079 (n : nat) (p : nat) : True = ((term137 n p) = (term138 n p)).
Proof. exact (SYM (@lem105078 n p)). Qed.
Lemma lem105080 (n : nat) (p : nat) : (term137 n p) = (term138 n p).
Proof. exact (EQ_MP (@lem105079 n p) (@lem0)). Qed.
Lemma lem105081 (n : nat) : term256 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem105082 (n : nat) : (term256 n) = (term257 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem105083 (n : nat) : term257 n.
Proof. exact (EQ_MP (@lem105082 n) (@lem105081 n)). Qed.
Lemma lem105084 (n : nat) : term258 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem105102 (n : nat) : term233 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem105103 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem105104 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem105103 n) (@lem105102 n)). Qed.
Lemma lem105105 (n : nat) : term235 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem105174 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem105105 n (@lem105104 n)). Qed.
Lemma lem105175 (m : nat) : (term180 m) = False.
Proof. exact (@lem105174 (term259 m)). Qed.
Lemma lem105176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105177 (m : nat) : (term260 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem105176) (@lem105175 m)). Qed.
Lemma lem105181 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem105084 n (@lem105083 n)). Qed.
Lemma lem105182 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem105181 m). Qed.
Lemma lem105183 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem105184 (m : nat) : (term257 m) = (~ False).
Proof. exact (MK_COMB (@lem105183) (@lem105182 m)). Qed.
Lemma lem105186 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105187 (m : nat) : (term257 m) = True.
Proof. exact (TRANS (@lem105184 m) (@lem105186)). Qed.
Lemma lem105188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem105189 (m : nat) : (term261 m) = (and True).
Proof. exact (MK_COMB (@lem105188) (@lem105187 m)). Qed.
Lemma lem105191 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem105105 n (@lem105104 n)). Qed.
Lemma lem105192 : term240 = False.
Proof. exact (@lem105191 (NUMERAL 0)). Qed.
Lemma lem105193 (m : nat) : (term181 m) = (True /\ False).
Proof. exact (MK_COMB (@lem105189 m) (@lem105192)). Qed.
Lemma lem105195 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem105196 : (True /\ False) = False.
Proof. exact (@lem105195 False). Qed.
Lemma lem105197 (m : nat) : (term181 m) = False.
Proof. exact (TRANS (@lem105193 m) (@lem105196)). Qed.
Lemma lem105198 (m : nat) : ((term180 m) = (term181 m)) = (False = False).
Proof. exact (MK_COMB (@lem105177 m) (@lem105197 m)). Qed.
Lemma lem105200 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem105201 : (False = False) = (~ False).
Proof. exact (@lem105200 False). Qed.
Lemma lem105203 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105204 : (False = False) = True.
Proof. exact (TRANS (@lem105201) (@lem105203)). Qed.
Lemma lem105205 (m : nat) : ((term180 m) = (term181 m)) = True.
Proof. exact (TRANS (@lem105198 m) (@lem105204)). Qed.
Lemma lem105206 (m : nat) : True = ((term180 m) = (term181 m)).
Proof. exact (SYM (@lem105205 m)). Qed.
Lemma lem105207 (m : nat) : (term180 m) = (term181 m).
Proof. exact (EQ_MP (@lem105206 m) (@lem0)). Qed.
Lemma lem105208 (n : nat) : term256 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem105209 (n : nat) : (term256 n) = (term257 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem105210 (n : nat) : term257 n.
Proof. exact (EQ_MP (@lem105209 n) (@lem105208 n)). Qed.
Lemma lem105211 (n : nat) : term258 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem105224 (n : nat) : term241 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem105225 (n : nat) : (term241 n) = (term242 n).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem105226 (n : nat) : term242 n.
Proof. exact (EQ_MP (@lem105225 n) (@lem105224 n)). Qed.
Lemma lem105227 (n : nat) : (term242 n) = ((term242 n) = True).
Proof. exact (@lem7 (term242 n)). Qed.
Lemma lem105234 : term262.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem105235 : term263.
Proof. exact (proj2 (@lem105234)). Qed.
Lemma lem105236 : term264.
Proof. exact (proj2 (@lem105235)). Qed.
Lemma lem105237 (m : nat) : term265 m.
Proof. exact (@lem105236 m). Qed.
Lemma lem105238 (m : nat) : (term265 m) = (term266 m).
Proof. exact (eq_refl (term265 m)). Qed.
Lemma lem105239 (m : nat) : term266 m.
Proof. exact (EQ_MP (@lem105238 m) (@lem105237 m)). Qed.
Lemma lem105240 (m : nat) (n : nat) : term267 m n.
Proof. exact (@lem105239 m n). Qed.
Lemma lem105241 (m : nat) (n : nat) : (term267 m n) = ((term268 m n) = (term269 m n)).
Proof. exact (eq_refl (term267 m n)). Qed.
Lemma lem105250 : term270.
Proof. exact (proj1 (@lem105234)). Qed.
Lemma lem105251 (m : nat) : term271 m.
Proof. exact (@lem105250 m). Qed.
Lemma lem105252 (m : nat) : (term271 m) = ((term272 m) = m).
Proof. exact (eq_refl (term271 m)). Qed.
Lemma lem105258 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem105259 : term1.
Proof. exact (proj2 (@lem105258)). Qed.
Lemma lem105260 : term2.
Proof. exact (proj2 (@lem105259)). Qed.
Lemma lem105261 : term3.
Proof. exact (proj2 (@lem105260)). Qed.
Lemma lem105262 : term273.
Proof. exact (proj2 (@lem105261)). Qed.
Lemma lem105263 (m : nat) : term274 m.
Proof. exact (@lem105262 m). Qed.
Lemma lem105264 (m : nat) : (term274 m) = (term275 m).
Proof. exact (eq_refl (term274 m)). Qed.
Lemma lem105265 (m : nat) : term275 m.
Proof. exact (EQ_MP (@lem105264 m) (@lem105263 m)). Qed.
Lemma lem105266 (m : nat) (n : nat) : term276 m n.
Proof. exact (@lem105265 m n). Qed.
Lemma lem105267 (m : nat) (n : nat) : (term276 m n) = ((term277 m n) = (term278 m n)).
Proof. exact (eq_refl (term276 m n)). Qed.
Lemma lem105269 : term4.
Proof. exact (proj1 (@lem105261)). Qed.
Lemma lem105270 (m : nat) : term279 m.
Proof. exact (@lem105269 m). Qed.
Lemma lem105271 (m : nat) : (term279 m) = (term9 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem105272 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem105271 m) (@lem105270 m)). Qed.
Lemma lem105273 (m : nat) (n : nat) : term280 m n.
Proof. exact (@lem105272 m n). Qed.
Lemma lem105274 (m : nat) (n : nat) : (term280 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term280 m n)). Qed.
Lemma lem105284 : term281.
Proof. exact (proj1 (@lem105258)). Qed.
Lemma lem105285 (m : nat) : term282 m.
Proof. exact (@lem105284 m). Qed.
Lemma lem105286 (m : nat) : (term282 m) = ((term283 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term282 m)). Qed.
Lemma lem105303 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem105274 m n) (@lem105273 m n)). Qed.
Lemma lem105304 (m : nat) : (term259 m) = (term284 m).
Proof. exact (@lem105303 m (NUMERAL 0)). Qed.
Lemma lem105306 (m : nat) : (term272 m) = m.
Proof. exact (EQ_MP (@lem105252 m) (@lem105251 m)). Qed.
Lemma lem105307 (m : nat) : (term284 m) = (term283 m).
Proof. exact (@lem105306 (term283 m)). Qed.
Lemma lem105309 (m : nat) : (term283 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem105286 m) (@lem105285 m)). Qed.
Lemma lem105310 (m : nat) : (term284 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem105307 m) (@lem105309 m)). Qed.
Lemma lem105311 (m : nat) : (term259 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem105304 m) (@lem105310 m)). Qed.
Lemma lem105312 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105313 (m : nat) : (term285 m) = term247.
Proof. exact (MK_COMB (@lem105312) (@lem105311 m)). Qed.
Lemma lem105315 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem105274 m n) (@lem105273 m n)). Qed.
Lemma lem105316 (m : nat) (p : nat) : (term286 m p) = (term287 m p).
Proof. exact (@lem105315 m (S p)). Qed.
Lemma lem105318 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (EQ_MP (@lem105241 m n) (@lem105240 m n)). Qed.
Lemma lem105319 (m : nat) (p : nat) : (term287 m p) = (term288 m p).
Proof. exact (@lem105318 (term277 m p) p). Qed.
Lemma lem105320 (m : nat) (p : nat) : (term286 m p) = (term288 m p).
Proof. exact (TRANS (@lem105316 m p) (@lem105319 m p)). Qed.
Lemma lem105322 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (EQ_MP (@lem105267 m n) (@lem105266 m n)). Qed.
Lemma lem105323 (m : nat) (p : nat) : (term277 m p) = (term278 m p).
Proof. exact (@lem105322 m p). Qed.
Lemma lem105324 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem105325 (m : nat) (p : nat) : (term289 m p) = (term290 m p).
Proof. exact (MK_COMB (@lem105324) (@lem105323 m p)). Qed.
Lemma lem105326 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem105327 (m : nat) (p : nat) : (term291 m p) = (term292 m p).
Proof. exact (MK_COMB (@lem105325 m p) (@lem105326 p)). Qed.
Lemma lem105328 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem105329 (m : nat) (p : nat) : (term288 m p) = (term293 m p).
Proof. exact (MK_COMB (@lem105328) (@lem105327 m p)). Qed.
Lemma lem105330 (m : nat) (p : nat) : (term286 m p) = (term293 m p).
Proof. exact (TRANS (@lem105320 m p) (@lem105329 m p)). Qed.
Lemma lem105331 (m : nat) (p : nat) : (term190 m p) = (term294 m p).
Proof. exact (MK_COMB (@lem105313 m) (@lem105330 m p)). Qed.
Lemma lem105333 (n : nat) : (term242 n) = True.
Proof. exact (EQ_MP (@lem105227 n) (@lem105226 n)). Qed.
Lemma lem105334 (m : nat) (p : nat) : (term294 m p) = True.
Proof. exact (@lem105333 (term292 m p)). Qed.
Lemma lem105335 (m : nat) (p : nat) : (term190 m p) = True.
Proof. exact (TRANS (@lem105331 m p) (@lem105334 m p)). Qed.
Lemma lem105336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105337 (m : nat) (p : nat) : (term295 m p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem105336) (@lem105335 m p)). Qed.
Lemma lem105341 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem105211 n (@lem105210 n)). Qed.
Lemma lem105342 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem105341 m). Qed.
Lemma lem105343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem105344 (m : nat) : (term257 m) = (~ False).
Proof. exact (MK_COMB (@lem105343) (@lem105342 m)). Qed.
Lemma lem105346 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105347 (m : nat) : (term257 m) = True.
Proof. exact (TRANS (@lem105344 m) (@lem105346)). Qed.
Lemma lem105348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem105349 (m : nat) : (term261 m) = (and True).
Proof. exact (MK_COMB (@lem105348) (@lem105347 m)). Qed.
Lemma lem105351 (n : nat) : (term242 n) = True.
Proof. exact (EQ_MP (@lem105227 n) (@lem105226 n)). Qed.
Lemma lem105352 (p : nat) : (term242 p) = True.
Proof. exact (@lem105351 p). Qed.
Lemma lem105353 (m : nat) (p : nat) : (term191 m p) = (True /\ True).
Proof. exact (MK_COMB (@lem105349 m) (@lem105352 p)). Qed.
Lemma lem105355 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem105356 : (True /\ True) = True.
Proof. exact (@lem105355 True). Qed.
Lemma lem105357 (m : nat) (p : nat) : (term191 m p) = True.
Proof. exact (TRANS (@lem105353 m p) (@lem105356)). Qed.
Lemma lem105358 (m : nat) (p : nat) : ((term190 m p) = (term191 m p)) = (True = True).
Proof. exact (MK_COMB (@lem105337 m p) (@lem105357 m p)). Qed.
Lemma lem105360 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem105361 : (True = True) = True.
Proof. exact (@lem105360 True). Qed.
Lemma lem105362 (m : nat) (p : nat) : ((term190 m p) = (term191 m p)) = True.
Proof. exact (TRANS (@lem105358 m p) (@lem105361)). Qed.
Lemma lem105363 (m : nat) (p : nat) : True = ((term190 m p) = (term191 m p)).
Proof. exact (SYM (@lem105362 m p)). Qed.
Lemma lem105364 (m : nat) (p : nat) : (term190 m p) = (term191 m p).
Proof. exact (EQ_MP (@lem105363 m p) (@lem0)). Qed.
Lemma lem105365 (n : nat) : term256 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem105366 (n : nat) : (term256 n) = (term257 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem105367 (n : nat) : term257 n.
Proof. exact (EQ_MP (@lem105366 n) (@lem105365 n)). Qed.
Lemma lem105368 (n : nat) : term258 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem105391 : term262.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem105392 : term263.
Proof. exact (proj2 (@lem105391)). Qed.
Lemma lem105393 : term264.
Proof. exact (proj2 (@lem105392)). Qed.
Lemma lem105394 (m : nat) : term265 m.
Proof. exact (@lem105393 m). Qed.
Lemma lem105395 (m : nat) : (term265 m) = (term266 m).
Proof. exact (eq_refl (term265 m)). Qed.
Lemma lem105396 (m : nat) : term266 m.
Proof. exact (EQ_MP (@lem105395 m) (@lem105394 m)). Qed.
Lemma lem105397 (m : nat) (n : nat) : term267 m n.
Proof. exact (@lem105396 m n). Qed.
Lemma lem105398 (m : nat) (n : nat) : (term267 m n) = ((term268 m n) = (term269 m n)).
Proof. exact (eq_refl (term267 m n)). Qed.
Lemma lem105407 : term270.
Proof. exact (proj1 (@lem105391)). Qed.
Lemma lem105408 (m : nat) : term271 m.
Proof. exact (@lem105407 m). Qed.
Lemma lem105409 (m : nat) : (term271 m) = ((term272 m) = m).
Proof. exact (eq_refl (term271 m)). Qed.
Lemma lem105415 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem105416 : term1.
Proof. exact (proj2 (@lem105415)). Qed.
Lemma lem105417 : term2.
Proof. exact (proj2 (@lem105416)). Qed.
Lemma lem105418 : term3.
Proof. exact (proj2 (@lem105417)). Qed.
Lemma lem105419 : term273.
Proof. exact (proj2 (@lem105418)). Qed.
Lemma lem105420 (m : nat) : term274 m.
Proof. exact (@lem105419 m). Qed.
Lemma lem105421 (m : nat) : (term274 m) = (term275 m).
Proof. exact (eq_refl (term274 m)). Qed.
Lemma lem105422 (m : nat) : term275 m.
Proof. exact (EQ_MP (@lem105421 m) (@lem105420 m)). Qed.
Lemma lem105423 (m : nat) (n : nat) : term276 m n.
Proof. exact (@lem105422 m n). Qed.
Lemma lem105424 (m : nat) (n : nat) : (term276 m n) = ((term277 m n) = (term278 m n)).
Proof. exact (eq_refl (term276 m n)). Qed.
Lemma lem105426 : term4.
Proof. exact (proj1 (@lem105418)). Qed.
Lemma lem105427 (m : nat) : term279 m.
Proof. exact (@lem105426 m). Qed.
Lemma lem105428 (m : nat) : (term279 m) = (term9 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem105429 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem105428 m) (@lem105427 m)). Qed.
Lemma lem105430 (m : nat) (n : nat) : term280 m n.
Proof. exact (@lem105429 m n). Qed.
Lemma lem105431 (m : nat) (n : nat) : (term280 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term280 m n)). Qed.
Lemma lem105441 : term281.
Proof. exact (proj1 (@lem105415)). Qed.
Lemma lem105442 (m : nat) : term282 m.
Proof. exact (@lem105441 m). Qed.
Lemma lem105443 (m : nat) : (term282 m) = ((term283 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term282 m)). Qed.
Lemma lem105463 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem105431 m n) (@lem105430 m n)). Qed.
Lemma lem105464 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (@lem105463 m (S n)). Qed.
Lemma lem105466 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (EQ_MP (@lem105398 m n) (@lem105397 m n)). Qed.
Lemma lem105467 (m : nat) (n : nat) : (term287 m n) = (term288 m n).
Proof. exact (@lem105466 (term277 m n) n). Qed.
Lemma lem105468 (m : nat) (n : nat) : (term286 m n) = (term288 m n).
Proof. exact (TRANS (@lem105464 m n) (@lem105467 m n)). Qed.
Lemma lem105470 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (EQ_MP (@lem105424 m n) (@lem105423 m n)). Qed.
Lemma lem105471 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem105472 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (MK_COMB (@lem105471) (@lem105470 m n)). Qed.
Lemma lem105473 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem105474 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (MK_COMB (@lem105472 m n) (@lem105473 n)). Qed.
Lemma lem105475 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem105476 (m : nat) (n : nat) : (term288 m n) = (term293 m n).
Proof. exact (MK_COMB (@lem105475) (@lem105474 m n)). Qed.
Lemma lem105477 (m : nat) (n : nat) : (term286 m n) = (term293 m n).
Proof. exact (TRANS (@lem105468 m n) (@lem105476 m n)). Qed.
Lemma lem105478 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105479 (m : nat) (n : nat) : (term296 m n) = (term297 m n).
Proof. exact (MK_COMB (@lem105478) (@lem105477 m n)). Qed.
Lemma lem105481 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem105431 m n) (@lem105430 m n)). Qed.
Lemma lem105482 (m : nat) : (term259 m) = (term284 m).
Proof. exact (@lem105481 m (NUMERAL 0)). Qed.
Lemma lem105484 (m : nat) : (term272 m) = m.
Proof. exact (EQ_MP (@lem105409 m) (@lem105408 m)). Qed.
Lemma lem105485 (m : nat) : (term284 m) = (term283 m).
Proof. exact (@lem105484 (term283 m)). Qed.
Lemma lem105487 (m : nat) : (term283 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem105443 m) (@lem105442 m)). Qed.
Lemma lem105488 (m : nat) : (term284 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem105485 m) (@lem105487 m)). Qed.
Lemma lem105489 (m : nat) : (term259 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem105482 m) (@lem105488 m)). Qed.
Lemma lem105490 (m : nat) (n : nat) : (term208 n m) = (term298 m n).
Proof. exact (MK_COMB (@lem105479 m n) (@lem105489 m)). Qed.
Lemma lem105493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105494 (m : nat) (n : nat) : (term299 n m) = (term300 m n).
Proof. exact (MK_COMB (@lem105493) (@lem105490 m n)). Qed.
Lemma lem105498 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem105368 n (@lem105367 n)). Qed.
Lemma lem105499 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem105498 m). Qed.
Lemma lem105500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem105501 (m : nat) : (term257 m) = (~ False).
Proof. exact (MK_COMB (@lem105500) (@lem105499 m)). Qed.
Lemma lem105503 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105504 (m : nat) : (term257 m) = True.
Proof. exact (TRANS (@lem105501 m) (@lem105503)). Qed.
Lemma lem105505 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem105506 (m : nat) : (term261 m) = (and True).
Proof. exact (MK_COMB (@lem105505) (@lem105504 m)). Qed.
Lemma lem105509 (n : nat) : (term252 n) = (term252 n).
Proof. exact (eq_refl (term252 n)). Qed.
Lemma lem105510 (m : nat) (n : nat) : (term209 m n) = (term301 n).
Proof. exact (MK_COMB (@lem105506 m) (@lem105509 n)). Qed.
Lemma lem105512 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem105513 (n : nat) : (term301 n) = (term252 n).
Proof. exact (@lem105512 (term252 n)). Qed.
Lemma lem105516 (m : nat) (n : nat) : (term209 m n) = (term252 n).
Proof. exact (TRANS (@lem105510 m n) (@lem105513 n)). Qed.
Lemma lem105517 (m : nat) (n : nat) : ((term208 n m) = (term209 m n)) = ((term298 m n) = (term252 n)).
Proof. exact (MK_COMB (@lem105494 m n) (@lem105516 m n)). Qed.
Lemma lem105520 (m : nat) (n : nat) : ((term298 m n) = (term252 n)) = ((term208 n m) = (term209 m n)).
Proof. exact (SYM (@lem105517 m n)). Qed.
Lemma lem105521 (n : nat) : term256 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem105522 (n : nat) : (term256 n) = (term257 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem105523 (n : nat) : term257 n.
Proof. exact (EQ_MP (@lem105522 n) (@lem105521 n)). Qed.
Lemma lem105524 (n : nat) : term258 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem105547 : term262.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem105548 : term263.
Proof. exact (proj2 (@lem105547)). Qed.
Lemma lem105549 : term264.
Proof. exact (proj2 (@lem105548)). Qed.
Lemma lem105550 (m : nat) : term265 m.
Proof. exact (@lem105549 m). Qed.
Lemma lem105551 (m : nat) : (term265 m) = (term266 m).
Proof. exact (eq_refl (term265 m)). Qed.
Lemma lem105552 (m : nat) : term266 m.
Proof. exact (EQ_MP (@lem105551 m) (@lem105550 m)). Qed.
Lemma lem105553 (m : nat) (n : nat) : term267 m n.
Proof. exact (@lem105552 m n). Qed.
Lemma lem105554 (m : nat) (n : nat) : (term267 m n) = ((term268 m n) = (term269 m n)).
Proof. exact (eq_refl (term267 m n)). Qed.
Lemma lem105571 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem105572 : term1.
Proof. exact (proj2 (@lem105571)). Qed.
Lemma lem105573 : term2.
Proof. exact (proj2 (@lem105572)). Qed.
Lemma lem105574 : term3.
Proof. exact (proj2 (@lem105573)). Qed.
Lemma lem105575 : term273.
Proof. exact (proj2 (@lem105574)). Qed.
Lemma lem105576 (m : nat) : term274 m.
Proof. exact (@lem105575 m). Qed.
Lemma lem105577 (m : nat) : (term274 m) = (term275 m).
Proof. exact (eq_refl (term274 m)). Qed.
Lemma lem105578 (m : nat) : term275 m.
Proof. exact (EQ_MP (@lem105577 m) (@lem105576 m)). Qed.
Lemma lem105579 (m : nat) (n : nat) : term276 m n.
Proof. exact (@lem105578 m n). Qed.
Lemma lem105580 (m : nat) (n : nat) : (term276 m n) = ((term277 m n) = (term278 m n)).
Proof. exact (eq_refl (term276 m n)). Qed.
Lemma lem105582 : term4.
Proof. exact (proj1 (@lem105574)). Qed.
Lemma lem105583 (m : nat) : term279 m.
Proof. exact (@lem105582 m). Qed.
Lemma lem105584 (m : nat) : (term279 m) = (term9 m).
Proof. exact (eq_refl (term279 m)). Qed.
Lemma lem105585 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem105584 m) (@lem105583 m)). Qed.
Lemma lem105586 (m : nat) (n : nat) : term280 m n.
Proof. exact (@lem105585 m n). Qed.
Lemma lem105587 (m : nat) (n : nat) : (term280 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term280 m n)). Qed.
Lemma lem105619 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem105587 m n) (@lem105586 m n)). Qed.
Lemma lem105620 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (@lem105619 m (S n)). Qed.
Lemma lem105622 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (EQ_MP (@lem105554 m n) (@lem105553 m n)). Qed.
Lemma lem105623 (m : nat) (n : nat) : (term287 m n) = (term288 m n).
Proof. exact (@lem105622 (term277 m n) n). Qed.
Lemma lem105624 (m : nat) (n : nat) : (term286 m n) = (term288 m n).
Proof. exact (TRANS (@lem105620 m n) (@lem105623 m n)). Qed.
Lemma lem105626 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (EQ_MP (@lem105580 m n) (@lem105579 m n)). Qed.
Lemma lem105627 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem105628 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (MK_COMB (@lem105627) (@lem105626 m n)). Qed.
Lemma lem105629 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem105630 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (MK_COMB (@lem105628 m n) (@lem105629 n)). Qed.
Lemma lem105631 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem105632 (m : nat) (n : nat) : (term288 m n) = (term293 m n).
Proof. exact (MK_COMB (@lem105631) (@lem105630 m n)). Qed.
Lemma lem105633 (m : nat) (n : nat) : (term286 m n) = (term293 m n).
Proof. exact (TRANS (@lem105624 m n) (@lem105632 m n)). Qed.
Lemma lem105634 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105635 (m : nat) (n : nat) : (term296 m n) = (term297 m n).
Proof. exact (MK_COMB (@lem105634) (@lem105633 m n)). Qed.
Lemma lem105637 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem105587 m n) (@lem105586 m n)). Qed.
Lemma lem105638 (m : nat) (p : nat) : (term286 m p) = (term287 m p).
Proof. exact (@lem105637 m (S p)). Qed.
Lemma lem105640 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (EQ_MP (@lem105554 m n) (@lem105553 m n)). Qed.
Lemma lem105641 (m : nat) (p : nat) : (term287 m p) = (term288 m p).
Proof. exact (@lem105640 (term277 m p) p). Qed.
Lemma lem105642 (m : nat) (p : nat) : (term286 m p) = (term288 m p).
Proof. exact (TRANS (@lem105638 m p) (@lem105641 m p)). Qed.
Lemma lem105644 (m : nat) (n : nat) : (term277 m n) = (term278 m n).
Proof. exact (EQ_MP (@lem105580 m n) (@lem105579 m n)). Qed.
Lemma lem105645 (m : nat) (p : nat) : (term277 m p) = (term278 m p).
Proof. exact (@lem105644 m p). Qed.
Lemma lem105646 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem105647 (m : nat) (p : nat) : (term289 m p) = (term290 m p).
Proof. exact (MK_COMB (@lem105646) (@lem105645 m p)). Qed.
Lemma lem105648 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem105649 (m : nat) (p : nat) : (term291 m p) = (term292 m p).
Proof. exact (MK_COMB (@lem105647 m p) (@lem105648 p)). Qed.
Lemma lem105650 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem105651 (m : nat) (p : nat) : (term288 m p) = (term293 m p).
Proof. exact (MK_COMB (@lem105650) (@lem105649 m p)). Qed.
Lemma lem105652 (m : nat) (p : nat) : (term286 m p) = (term293 m p).
Proof. exact (TRANS (@lem105642 m p) (@lem105651 m p)). Qed.
Lemma lem105653 (n : nat) (m : nat) (p : nat) : (term218 n m p) = (term302 n m p).
Proof. exact (MK_COMB (@lem105635 m n) (@lem105652 m p)). Qed.
Lemma lem105656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105657 (n : nat) (m : nat) (p : nat) : (term303 n m p) = (term304 n m p).
Proof. exact (MK_COMB (@lem105656) (@lem105653 n m p)). Qed.
Lemma lem105661 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem105524 n (@lem105523 n)). Qed.
Lemma lem105662 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem105661 m). Qed.
Lemma lem105663 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem105664 (m : nat) : (term257 m) = (~ False).
Proof. exact (MK_COMB (@lem105663) (@lem105662 m)). Qed.
Lemma lem105666 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105667 (m : nat) : (term257 m) = True.
Proof. exact (TRANS (@lem105664 m) (@lem105666)). Qed.
Lemma lem105668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem105669 (m : nat) : (term261 m) = (and True).
Proof. exact (MK_COMB (@lem105668) (@lem105667 m)). Qed.
Lemma lem105672 (n : nat) (p : nat) : (term43 n p) = (term43 n p).
Proof. exact (eq_refl (term43 n p)). Qed.
Lemma lem105673 (m : nat) (n : nat) (p : nat) : (term219 m n p) = (term305 n p).
Proof. exact (MK_COMB (@lem105669 m) (@lem105672 n p)). Qed.
Lemma lem105675 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem105676 (n : nat) (p : nat) : (term305 n p) = (term43 n p).
Proof. exact (@lem105675 (term43 n p)). Qed.
Lemma lem105679 (m : nat) (n : nat) (p : nat) : (term219 m n p) = (term43 n p).
Proof. exact (TRANS (@lem105673 m n p) (@lem105676 n p)). Qed.
Lemma lem105680 (m : nat) (n : nat) (p : nat) : ((term218 n m p) = (term219 m n p)) = ((term302 n m p) = (term43 n p)).
Proof. exact (MK_COMB (@lem105657 n m p) (@lem105679 m n p)). Qed.
Lemma lem105683 (m : nat) (n : nat) (p : nat) : ((term302 n m p) = (term43 n p)) = ((term218 n m p) = (term219 m n p)).
Proof. exact (SYM (@lem105680 m n p)). Qed.
Lemma lem105691 (m : nat) (n : nat) : (term43 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem104365 m n) (@lem104364 m n)). Qed.
Lemma lem105692 (n : nat) (m : nat) (p : nat) : (term302 n m p) = (term306 n m p).
Proof. exact (@lem105691 (term292 m n) (term292 m p)). Qed.
Lemma lem105693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105694 (n : nat) (m : nat) (p : nat) : (term304 n m p) = (term307 n m p).
Proof. exact (MK_COMB (@lem105693) (@lem105692 n m p)). Qed.
Lemma lem105696 (m : nat) (n : nat) : (term43 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem104365 m n) (@lem104364 m n)). Qed.
Lemma lem105697 (n : nat) (p : nat) : (term43 n p) = (Peano.lt n p).
Proof. exact (@lem105696 n p). Qed.
Lemma lem105698 (m : nat) (n : nat) (p : nat) : ((term302 n m p) = (term43 n p)) = ((term306 n m p) = (Peano.lt n p)).
Proof. exact (MK_COMB (@lem105694 n m p) (@lem105697 n p)). Qed.
Lemma lem105701 (m : nat) (n : nat) (p : nat) : ((term306 n m p) = (Peano.lt n p)) = ((term302 n m p) = (term43 n p)).
Proof. exact (SYM (@lem105698 m n p)). Qed.
Lemma lem105705 (m : nat) : (term39 m) = False.
Proof. exact (EQ_MP (@lem104359 m) (@lem104358 m)). Qed.
Lemma lem105706 (m : nat) (n : nat) : (term298 m n) = False.
Proof. exact (@lem105705 (term293 m n)). Qed.
Lemma lem105707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105708 (m : nat) (n : nat) : (term300 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem105707) (@lem105706 m n)). Qed.
Lemma lem105710 (m : nat) : (term39 m) = False.
Proof. exact (EQ_MP (@lem104359 m) (@lem104358 m)). Qed.
Lemma lem105711 (n : nat) : (term252 n) = False.
Proof. exact (@lem105710 (S n)). Qed.
Lemma lem105712 (m : nat) (n : nat) : ((term298 m n) = (term252 n)) = (False = False).
Proof. exact (MK_COMB (@lem105708 m n) (@lem105711 n)). Qed.
Lemma lem105714 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem105715 : (False = False) = (~ False).
Proof. exact (@lem105714 False). Qed.
Lemma lem105717 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105718 : (False = False) = True.
Proof. exact (TRANS (@lem105715) (@lem105717)). Qed.
Lemma lem105719 (m : nat) (n : nat) : ((term298 m n) = (term252 n)) = True.
Proof. exact (TRANS (@lem105712 m n) (@lem105718)). Qed.
Lemma lem105720 (m : nat) (n : nat) : True = ((term298 m n) = (term252 n)).
Proof. exact (SYM (@lem105719 m n)). Qed.
Lemma lem105727 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem104339 m n p) (@lem104338 m n p)). Qed.
Lemma lem105728 (m : nat) (n : nat) : (term292 m n) = (term308 m n).
Proof. exact (@lem105727 m (Nat.mul m n) n). Qed.
Lemma lem105729 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105730 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (MK_COMB (@lem105729) (@lem105728 m n)). Qed.
Lemma lem105732 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem104339 m n p) (@lem104338 m n p)). Qed.
Lemma lem105733 (m : nat) (p : nat) : (term292 m p) = (term308 m p).
Proof. exact (@lem105732 m (Nat.mul m p) p). Qed.
Lemma lem105734 (n : nat) (m : nat) (p : nat) : (term306 n m p) = (term311 n m p).
Proof. exact (MK_COMB (@lem105730 m n) (@lem105733 m p)). Qed.
Lemma lem105736 (m : nat) (n : nat) (p : nat) : (term36 n m p) = (Peano.lt n p).
Proof. exact (EQ_MP (@lem104348 m n p) (@lem104347 m n p)). Qed.
Lemma lem105737 (n : nat) (m : nat) (p : nat) : (term311 n m p) = (term312 n m p).
Proof. exact (@lem105736 m (term6 m n) (term6 m p)). Qed.
Lemma lem105740 (n : nat) (m : nat) (p : nat) : (term306 n m p) = (term312 n m p).
Proof. exact (TRANS (@lem105734 n m p) (@lem105737 n m p)). Qed.
Lemma lem105741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105742 (n : nat) (m : nat) (p : nat) : (term307 n m p) = (term313 n m p).
Proof. exact (MK_COMB (@lem105741) (@lem105740 n m p)). Qed.
Lemma lem105743 (n : nat) (p : nat) : (Peano.lt n p) = (Peano.lt n p).
Proof. exact (eq_refl (Peano.lt n p)). Qed.
Lemma lem105744 (m : nat) (n : nat) (p : nat) : ((term306 n m p) = (Peano.lt n p)) = ((term312 n m p) = (Peano.lt n p)).
Proof. exact (MK_COMB (@lem105742 n m p) (@lem105743 n p)). Qed.
Lemma lem105747 (m : nat) (n : nat) (p : nat) : ((term312 n m p) = (Peano.lt n p)) = ((term306 n m p) = (Peano.lt n p)).
Proof. exact (SYM (@lem105744 m n p)). Qed.
Lemma lem105748 (n : nat) : term256 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem105749 (n : nat) : (term256 n) = (term257 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem105750 (n : nat) : term257 n.
Proof. exact (EQ_MP (@lem105749 n) (@lem105748 n)). Qed.
Lemma lem105751 (n : nat) : term258 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem105764 (m : nat) : term314 m.
Proof. exact (@lem104313 m). Qed.
Lemma lem105765 (m : nat) : (term314 m) = (term10 m).
Proof. exact (eq_refl (term314 m)). Qed.
Lemma lem105766 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem105765 m) (@lem105764 m)). Qed.
Lemma lem105767 (m : nat) (n : nat) : term315 m n.
Proof. exact (@lem105766 m n). Qed.
Lemma lem105768 (m : nat) (n : nat) : (term315 m n) = ((term6 m n) = (term5 m n)).
Proof. exact (eq_refl (term315 m n)). Qed.
Lemma lem105776 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : term316 m n p.
Proof. exact (@lem104494 m n h1 p). Qed.
Lemma lem105777 (m : nat) (n : nat) (p : nat) : (term316 m n p) = ((term317 n m p) = (term318 m n p)).
Proof. exact (eq_refl (term316 m n p)). Qed.
Lemma lem105782 (m : nat) (n : nat) : (term6 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem105768 m n) (@lem105767 m n)). Qed.
Lemma lem105783 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem105784 (m : nat) (n : nat) : (term319 m n) = (term320 m n).
Proof. exact (MK_COMB (@lem105783) (@lem105782 m n)). Qed.
Lemma lem105786 (m : nat) (n : nat) : (term6 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem105768 m n) (@lem105767 m n)). Qed.
Lemma lem105787 (m : nat) (p : nat) : (term6 m p) = (term5 m p).
Proof. exact (@lem105786 m p). Qed.
Lemma lem105788 (n : nat) (m : nat) (p : nat) : (term312 n m p) = (term317 n m p).
Proof. exact (MK_COMB (@lem105784 m n) (@lem105787 m p)). Qed.
Lemma lem105790 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term317 n m p) = (term318 m n p).
Proof. exact (EQ_MP (@lem105777 m n p) (@lem105776 p m n h1)). Qed.
Lemma lem105794 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem105751 n (@lem105750 n)). Qed.
Lemma lem105795 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem105794 m). Qed.
Lemma lem105796 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem105797 (m : nat) : (term257 m) = (~ False).
Proof. exact (MK_COMB (@lem105796) (@lem105795 m)). Qed.
Lemma lem105799 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem105800 (m : nat) : (term257 m) = True.
Proof. exact (TRANS (@lem105797 m) (@lem105799)). Qed.
Lemma lem105801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem105802 (m : nat) : (term261 m) = (and True).
Proof. exact (MK_COMB (@lem105801) (@lem105800 m)). Qed.
Lemma lem105803 (n : nat) (p : nat) : (Peano.lt n p) = (Peano.lt n p).
Proof. exact (eq_refl (Peano.lt n p)). Qed.
Lemma lem105804 (m : nat) (n : nat) (p : nat) : (term318 m n p) = (term321 n p).
Proof. exact (MK_COMB (@lem105802 m) (@lem105803 n p)). Qed.
Lemma lem105806 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem105807 (n : nat) (p : nat) : (term321 n p) = (Peano.lt n p).
Proof. exact (@lem105806 (Peano.lt n p)). Qed.
Lemma lem105808 (m : nat) (n : nat) (p : nat) : (term318 m n p) = (Peano.lt n p).
Proof. exact (TRANS (@lem105804 m n p) (@lem105807 n p)). Qed.
Lemma lem105809 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term317 n m p) = (Peano.lt n p).
Proof. exact (TRANS (@lem105790 p m n h1) (@lem105808 m n p)). Qed.
Lemma lem105810 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term312 n m p) = (Peano.lt n p).
Proof. exact (TRANS (@lem105788 n m p) (@lem105809 p m n h1)). Qed.
Lemma lem105811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem105812 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term313 n m p) = (term322 n p).
Proof. exact (MK_COMB (@lem105811) (@lem105810 p m n h1)). Qed.
Lemma lem105813 (n : nat) (p : nat) : (Peano.lt n p) = (Peano.lt n p).
Proof. exact (eq_refl (Peano.lt n p)). Qed.
Lemma lem105814 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : ((term312 n m p) = (Peano.lt n p)) = ((Peano.lt n p) = (Peano.lt n p)).
Proof. exact (MK_COMB (@lem105812 p m n h1) (@lem105813 n p)). Qed.
Lemma lem105816 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem105817 (x : Prop) : (x = x) = True.
Proof. exact (@lem105816 Prop x). Qed.
Lemma lem105818 (n : nat) (p : nat) : ((Peano.lt n p) = (Peano.lt n p)) = True.
Proof. exact (@lem105817 (Peano.lt n p)). Qed.
Lemma lem105819 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : ((term312 n m p) = (Peano.lt n p)) = True.
Proof. exact (TRANS (@lem105814 p m n h1) (@lem105818 n p)). Qed.
Lemma lem105820 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : True = ((term312 n m p) = (Peano.lt n p)).
Proof. exact (SYM (@lem105819 p m n h1)). Qed.
Lemma lem105821 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term312 n m p) = (Peano.lt n p).
Proof. exact (EQ_MP (@lem105820 p m n h1) (@lem0)). Qed.
Lemma lem105822 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term306 n m p) = (Peano.lt n p).
Proof. exact (EQ_MP (@lem105747 m n p) (@lem105821 p m n h1)). Qed.
Lemma lem105823 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term302 n m p) = (term43 n p).
Proof. exact (EQ_MP (@lem105701 m n p) (@lem105822 p m n h1)). Qed.
Lemma lem105824 (m : nat) (n : nat) : (term298 m n) = (term252 n).
Proof. exact (EQ_MP (@lem105720 m n) (@lem0)). Qed.
Lemma lem105825 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term218 n m p) = (term219 m n p).
Proof. exact (EQ_MP (@lem105683 m n p) (@lem105823 p m n h1)). Qed.
Lemma lem105826 (m : nat) (n : nat) : (term208 n m) = (term209 m n).
Proof. exact (EQ_MP (@lem105520 m n) (@lem105824 m n)). Qed.
Lemma lem105827 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : term221 m n p.
Proof. exact (fun h0 : (term213 n m p) = (term214 m n p) => @lem105825 p m n h1). Qed.
Lemma lem105832 (m : nat) (n : nat) (h1 : term159 m n) : term225 m n.
Proof. exact (fun p : nat => @lem105827 p m n h1). Qed.
Lemma lem105833 (m : nat) (n : nat) (h1 : term159 m n) : term227 m n.
Proof. exact (conj (@lem105826 m n) (@lem105832 m n h1)). Qed.
Lemma lem105834 (m : nat) (n : nat) (h1 : term159 m n) : term163 m n.
Proof. exact (@lem104545 m n (@lem105833 m n h1)). Qed.
Lemma lem105835 (m : nat) (p : nat) : term193 m p.
Proof. exact (fun h0 : (term185 m p) = (term186 m p) => @lem105364 m p). Qed.
Lemma lem105840 (m : nat) : term197 m.
Proof. exact (fun p : nat => @lem105835 m p). Qed.
Lemma lem105841 (m : nat) : term199 m.
Proof. exact (conj (@lem105207 m) (@lem105840 m)). Qed.
Lemma lem105842 (m : nat) : term155 m.
Proof. exact (@lem104517 m (@lem105841 m)). Qed.
Lemma lem105843 (m : nat) (n : nat) : term165 m n.
Proof. exact (fun h0 : term159 m n => @lem105834 m n h0). Qed.
Lemma lem105848 (m : nat) : term169 m.
Proof. exact (fun n : nat => @lem105843 m n). Qed.
Lemma lem105849 (m : nat) : term171 m.
Proof. exact (conj (@lem105842 m) (@lem105848 m)). Qed.
Lemma lem105850 (m : nat) : term56 m.
Proof. exact (@lem104493 m (@lem105849 m)). Qed.
Lemma lem105851 (n : nat) (p : nat) : term140 n p.
Proof. exact (fun h0 : (term132 n p) = (term133 n p) => @lem105080 n p). Qed.
Lemma lem105856 (n : nat) : term144 n.
Proof. exact (fun p : nat => @lem105851 n p). Qed.
Lemma lem105857 (n : nat) : term146 n.
Proof. exact (conj (@lem104943 n) (@lem105856 n)). Qed.
Lemma lem105858 (n : nat) : term82 n.
Proof. exact (@lem104465 n (@lem105857 n)). Qed.
Lemma lem105859 (p : nat) : term112 p.
Proof. exact (fun h0 : (term104 p) = (term105 p) => @lem104806 p). Qed.
Lemma lem105864 : term116.
Proof. exact (fun p : nat => @lem105859 p). Qed.
Lemma lem105865 : term118.
Proof. exact (conj (@lem104672) (@lem105864)). Qed.
Lemma lem105866 : term74.
Proof. exact (@lem104437 (@lem105865)). Qed.
Lemma lem105867 (n : nat) : term84 n.
Proof. exact (fun h0 : term78 n => @lem105858 n). Qed.
Lemma lem105872 : term88.
Proof. exact (fun n : nat => @lem105867 n). Qed.
Lemma lem105873 : term90.
Proof. exact (conj (@lem105866) (@lem105872)). Qed.
Lemma lem105874 : term48.
Proof. exact (@lem104413 (@lem105873)). Qed.
Lemma lem105875 (m : nat) : term58 m.
Proof. exact (fun h0 : term52 m => @lem105850 m). Qed.
Lemma lem105880 : term62.
Proof. exact (fun m : nat => @lem105875 m). Qed.
Lemma lem105881 : term64.
Proof. exact (conj (@lem105874) (@lem105880)). Qed.
Lemma lem105882 : term69.
Proof. exact (@lem104389 (@lem105881)). Qed.
