Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm994716_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem993174 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem993175 (n : nat) (m : nat) : (term1 n m) = (term2 n m).
Proof. exact (@lem993174 (term1 n m)). Qed.
Lemma lem993176 (n : nat) (m : nat) : (term2 n m) = (term1 n m).
Proof. exact (SYM (@lem993175 n m)). Qed.
Lemma lem993177 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem993180 (n : nat) (m : nat) (h1 : term4 n m) : term4 n m.
Proof. exact (h1). Qed.
Lemma lem993181 (n : nat) (m : nat) : term5 n m.
Proof. exact (fun h0 : term4 n m => @lem993180 n m h0). Qed.
Lemma lem993182 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (h1). Qed.
Lemma lem993183 (n : nat) (m : nat) (h1 : term4 n m) : term4 n m.
Proof. exact (h1). Qed.
Lemma lem993184 (n : nat) (m : nat) (h1 : term4 n m) (h2 : term5 n m) : term4 n m.
Proof. exact (@lem993182 n m h2 (@lem993183 n m h1)). Qed.
Lemma lem993185 (n : nat) (m : nat) (h1 : term4 n m) : term6 n m.
Proof. exact (fun h0 : term5 n m => @lem993184 n m h1 h0). Qed.
Lemma lem993186 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (h1). Qed.
Lemma lem993187 (n : nat) (m : nat) (h1 : term4 n m) (h2 : term5 n m) : term4 n m.
Proof. exact (@lem993185 n m h1 (@lem993186 n m h2)). Qed.
Lemma lem993188 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (fun h0 : term4 n m => @lem993187 n m h0 h1). Qed.
Lemma lem993189 (n : nat) (m : nat) : term7 n m.
Proof. exact (fun h0 : term5 n m => @lem993188 n m h0). Qed.
Lemma lem993192 (n : nat) (m : nat) : term5 n m.
Proof. exact (@lem993189 n m (@lem993181 n m)). Qed.
Lemma lem993250 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem993251 : term8 = term9.
Proof. exact (@lem993250 term10). Qed.
Lemma lem993256 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem993257 : term12 = term13.
Proof. exact (MK_COMB (@lem993256) (@lem993251)). Qed.
Lemma lem993260 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem993261 (n : nat) (m : nat) : (term4 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem993260 n m) (@lem993257)). Qed.
Lemma lem993264 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem993261 n m)). Qed.
Lemma lem993265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993266 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem993265) (@lem993264 m)). Qed.
Lemma lem993271 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem993266 m)). Qed.
Lemma lem993272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993281 : term22 = term23.
Proof. exact (MK_COMB (@lem993272) (@lem993271)). Qed.
Lemma lem993282 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem993283 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem993282 n)). Qed.
Lemma lem993284 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993285 : term10 = term10.
Proof. exact (MK_COMB (@lem993284) (@lem993283)). Qed.
Lemma lem993286 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem993287 : term9 = term9.
Proof. exact (MK_COMB (@lem993286) (@lem993285)). Qed.
Lemma lem993288 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl ((term25 m n) = (term26 m n))). Qed.
Lemma lem993289 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem993288 m n)). Qed.
Lemma lem993290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993291 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem993290) (@lem993289 m)). Qed.
Lemma lem993292 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem993291 m)). Qed.
Lemma lem993293 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993294 : term30 = term30.
Proof. exact (MK_COMB (@lem993293) (@lem993292)). Qed.
Lemma lem993295 (m : nat) (n : nat) : ((term31 m n) = (term32 m n)) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl ((term31 m n) = (term32 m n))). Qed.
Lemma lem993296 (m : nat) : (term33 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem993295 m n)). Qed.
Lemma lem993297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993298 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem993297) (@lem993296 m)). Qed.
Lemma lem993299 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem993298 m)). Qed.
Lemma lem993300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993301 : term36 = term36.
Proof. exact (MK_COMB (@lem993300) (@lem993299)). Qed.
Lemma lem993302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993303 : term37 = term37.
Proof. exact (MK_COMB (@lem993302) (@lem993301)). Qed.
Lemma lem993304 : term38 = term38.
Proof. exact (MK_COMB (@lem993303) (@lem993294)). Qed.
Lemma lem993305 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem993306 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem993305 m)). Qed.
Lemma lem993307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993308 : term41 = term41.
Proof. exact (MK_COMB (@lem993307) (@lem993306)). Qed.
Lemma lem993309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993310 : term42 = term42.
Proof. exact (MK_COMB (@lem993309) (@lem993308)). Qed.
Lemma lem993311 : term43 = term43.
Proof. exact (MK_COMB (@lem993310) (@lem993304)). Qed.
Lemma lem993312 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem993313 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem993312 n)). Qed.
Lemma lem993314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993315 : term46 = term46.
Proof. exact (MK_COMB (@lem993314) (@lem993313)). Qed.
Lemma lem993316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993317 : term47 = term47.
Proof. exact (MK_COMB (@lem993316) (@lem993315)). Qed.
Lemma lem993318 : term48 = term48.
Proof. exact (MK_COMB (@lem993317) (@lem993311)). Qed.
Lemma lem993319 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem993320 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem993319 m)). Qed.
Lemma lem993321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993322 : term51 = term51.
Proof. exact (MK_COMB (@lem993321) (@lem993320)). Qed.
Lemma lem993323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993324 : term52 = term52.
Proof. exact (MK_COMB (@lem993323) (@lem993322)). Qed.
Lemma lem993325 : term53 = term53.
Proof. exact (MK_COMB (@lem993324) (@lem993318)). Qed.
Lemma lem993326 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem993327 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem993326 n)). Qed.
Lemma lem993328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993329 : term56 = term56.
Proof. exact (MK_COMB (@lem993328) (@lem993327)). Qed.
Lemma lem993330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993331 : term57 = term57.
Proof. exact (MK_COMB (@lem993330) (@lem993329)). Qed.
Lemma lem993332 : term58 = term58.
Proof. exact (MK_COMB (@lem993331) (@lem993325)). Qed.
Lemma lem993333 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem993334 : term11 = term11.
Proof. exact (MK_COMB (@lem993333) (@lem993332)). Qed.
Lemma lem993335 : term13 = term13.
Proof. exact (MK_COMB (@lem993334) (@lem993287)). Qed.
Lemma lem993344 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem993345 (n : nat) (m : nat) : (term15 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem993344 n m) (@lem993335)). Qed.
Lemma lem993346 (m : nat) : (term17 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem993345 n m)). Qed.
Lemma lem993347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993348 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem993347) (@lem993346 m)). Qed.
Lemma lem993349 : term21 = term21.
Proof. exact (fun_ext (fun m : nat => @lem993348 m)). Qed.
Lemma lem993350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993351 : term23 = term23.
Proof. exact (MK_COMB (@lem993350) (@lem993349)). Qed.
Lemma lem993436 : term22 = term23.
Proof. exact (TRANS (@lem993281) (@lem993351)). Qed.
Lemma lem993437 : term23 = term22.
Proof. exact (SYM (@lem993436)). Qed.
Lemma lem993438 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem993439 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem993440 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem993451 (n : nat) (m : nat) : (term3 n m) = (term59 n m).
Proof. exact (@lem17045 ((Nat.mul 0 n) = 0) ((Nat.mul m 0) = 0)). Qed.
Lemma lem993453 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem993454 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem993453 n)). Qed.
Lemma lem993455 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993456 : term56 = term56.
Proof. exact (MK_COMB (@lem993455) (@lem993454)). Qed.
Lemma lem993457 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem993458 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem993457 m)). Qed.
Lemma lem993459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993460 : term51 = term51.
Proof. exact (MK_COMB (@lem993459) (@lem993458)). Qed.
Lemma lem993461 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem993462 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem993461 n)). Qed.
Lemma lem993463 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993464 : term46 = term46.
Proof. exact (MK_COMB (@lem993463) (@lem993462)). Qed.
Lemma lem993465 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem993466 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem993465 m)). Qed.
Lemma lem993467 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993468 : term41 = term41.
Proof. exact (MK_COMB (@lem993467) (@lem993466)). Qed.
Lemma lem993469 (m : nat) (n : nat) : ((term31 m n) = (term32 m n)) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl ((term31 m n) = (term32 m n))). Qed.
Lemma lem993470 (m : nat) : (term33 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem993469 m n)). Qed.
Lemma lem993471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993472 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem993471) (@lem993470 m)). Qed.
Lemma lem993473 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem993472 m)). Qed.
Lemma lem993474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993475 : term36 = term36.
Proof. exact (MK_COMB (@lem993474) (@lem993473)). Qed.
Lemma lem993476 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl ((term25 m n) = (term26 m n))). Qed.
Lemma lem993477 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem993476 m n)). Qed.
Lemma lem993478 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993479 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem993478) (@lem993477 m)). Qed.
Lemma lem993480 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem993479 m)). Qed.
Lemma lem993481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993482 : term30 = term30.
Proof. exact (MK_COMB (@lem993481) (@lem993480)). Qed.
Lemma lem993483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993484 : term37 = term37.
Proof. exact (MK_COMB (@lem993483) (@lem993475)). Qed.
Lemma lem993485 : term38 = term38.
Proof. exact (MK_COMB (@lem993484) (@lem993482)). Qed.
Lemma lem993486 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993487 : term42 = term42.
Proof. exact (MK_COMB (@lem993486) (@lem993468)). Qed.
Lemma lem993488 : term43 = term43.
Proof. exact (MK_COMB (@lem993487) (@lem993485)). Qed.
Lemma lem993489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993490 : term47 = term47.
Proof. exact (MK_COMB (@lem993489) (@lem993464)). Qed.
Lemma lem993491 : term48 = term48.
Proof. exact (MK_COMB (@lem993490) (@lem993488)). Qed.
Lemma lem993492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993493 : term52 = term52.
Proof. exact (MK_COMB (@lem993492) (@lem993460)). Qed.
Lemma lem993494 : term53 = term53.
Proof. exact (MK_COMB (@lem993493) (@lem993491)). Qed.
Lemma lem993495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993496 : term57 = term57.
Proof. exact (MK_COMB (@lem993495) (@lem993456)). Qed.
Lemma lem993533 : term58 = term58.
Proof. exact (MK_COMB (@lem993496) (@lem993494)). Qed.
Lemma lem993534 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem993533) (@lem993439 h1)). Qed.
Lemma lem993535 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem993536 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem993535 n)). Qed.
Lemma lem993537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993546 : term10 = term10.
Proof. exact (MK_COMB (@lem993537) (@lem993536)). Qed.
Lemma lem993547 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem993546) (@lem993440 h1)). Qed.
Lemma lem993573 (n : nat) (m : nat) (h1 : term3 n m) : term59 n m.
Proof. exact (EQ_MP (@lem993451 n m) (@lem993438 n m h1)). Qed.
Lemma lem993592 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl ((term25 m n) = (term26 m n))). Qed.
Lemma lem993593 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem993592 m n)). Qed.
Lemma lem993594 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993595 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem993594) (@lem993593 m)). Qed.
Lemma lem993596 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem993595 m)). Qed.
Lemma lem993597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993598 : term30 = term30.
Proof. exact (MK_COMB (@lem993597) (@lem993596)). Qed.
Lemma lem993617 (m : nat) (n : nat) : ((term31 m n) = (term32 m n)) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl ((term31 m n) = (term32 m n))). Qed.
Lemma lem993618 (m : nat) : (term33 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem993617 m n)). Qed.
Lemma lem993619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993620 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem993619) (@lem993618 m)). Qed.
Lemma lem993621 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem993620 m)). Qed.
Lemma lem993622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993623 : term36 = term36.
Proof. exact (MK_COMB (@lem993622) (@lem993621)). Qed.
Lemma lem993624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993625 : term37 = term37.
Proof. exact (MK_COMB (@lem993624) (@lem993623)). Qed.
Lemma lem993626 : term38 = term38.
Proof. exact (MK_COMB (@lem993625) (@lem993598)). Qed.
Lemma lem993639 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem993640 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem993639 m)). Qed.
Lemma lem993641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993642 : term41 = term41.
Proof. exact (MK_COMB (@lem993641) (@lem993640)). Qed.
Lemma lem993643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993644 : term42 = term42.
Proof. exact (MK_COMB (@lem993643) (@lem993642)). Qed.
Lemma lem993645 : term43 = term43.
Proof. exact (MK_COMB (@lem993644) (@lem993626)). Qed.
Lemma lem993658 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem993659 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem993658 n)). Qed.
Lemma lem993660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993661 : term46 = term46.
Proof. exact (MK_COMB (@lem993660) (@lem993659)). Qed.
Lemma lem993662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993663 : term47 = term47.
Proof. exact (MK_COMB (@lem993662) (@lem993661)). Qed.
Lemma lem993664 : term48 = term48.
Proof. exact (MK_COMB (@lem993663) (@lem993645)). Qed.
Lemma lem993677 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem993678 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem993677 m)). Qed.
Lemma lem993679 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993680 : term51 = term51.
Proof. exact (MK_COMB (@lem993679) (@lem993678)). Qed.
Lemma lem993681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993682 : term52 = term52.
Proof. exact (MK_COMB (@lem993681) (@lem993680)). Qed.
Lemma lem993683 : term53 = term53.
Proof. exact (MK_COMB (@lem993682) (@lem993664)). Qed.
Lemma lem993696 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem993697 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem993696 n)). Qed.
Lemma lem993698 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993699 : term56 = term56.
Proof. exact (MK_COMB (@lem993698) (@lem993697)). Qed.
Lemma lem993700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem993701 : term57 = term57.
Proof. exact (MK_COMB (@lem993700) (@lem993699)). Qed.
Lemma lem993702 : term58 = term58.
Proof. exact (MK_COMB (@lem993701) (@lem993683)). Qed.
Lemma lem993703 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem993702) (@lem993534 h1)). Qed.
Lemma lem993710 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem993711 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem993710 n)). Qed.
Lemma lem993712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993713 : term10 = term10.
Proof. exact (MK_COMB (@lem993712) (@lem993711)). Qed.
Lemma lem993714 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem993713) (@lem993547 h1)). Qed.
Lemma lem993715 (h1 : term58) : term53.
Proof. exact (proj2 (@lem993703 h1)). Qed.
Lemma lem993716 (h1 : term58) : term56.
Proof. exact (proj1 (@lem993703 h1)). Qed.
Lemma lem993717 (h1 : term58) : term48.
Proof. exact (proj2 (@lem993715 h1)). Qed.
Lemma lem993718 (h1 : term58) : term51.
Proof. exact (proj1 (@lem993715 h1)). Qed.
Lemma lem993719 (h1 : term58) : term43.
Proof. exact (proj2 (@lem993717 h1)). Qed.
Lemma lem993722 (h1 : term58) : term41.
Proof. exact (proj1 (@lem993719 h1)). Qed.
Lemma lem993728 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem993729 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem993728 n)). Qed.
Lemma lem993730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993732 : term10 = term10.
Proof. exact (MK_COMB (@lem993730) (@lem993729)). Qed.
Lemma lem993733 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem993732) (@lem993714 h1)). Qed.
Lemma lem993735 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem993736 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem993735 n)). Qed.
Lemma lem993737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993739 : term56 = term56.
Proof. exact (MK_COMB (@lem993737) (@lem993736)). Qed.
Lemma lem993740 (h1 : term58) : term56.
Proof. exact (EQ_MP (@lem993739) (@lem993716 h1)). Qed.
Lemma lem993756 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem993757 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem993756 m)). Qed.
Lemma lem993758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993760 : term41 = term41.
Proof. exact (MK_COMB (@lem993758) (@lem993757)). Qed.
Lemma lem993761 (h1 : term58) : term41.
Proof. exact (EQ_MP (@lem993760) (@lem993722 h1)). Qed.
Lemma lem993785 (n : nat) (h1 : term60 n) : term60 n.
Proof. exact (h1). Qed.
Lemma lem993787 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem993788 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem993787 n)). Qed.
Lemma lem993789 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993791 : term10 = term10.
Proof. exact (MK_COMB (@lem993789) (@lem993788)). Qed.
Lemma lem993792 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem993791) (@lem993714 h1)). Qed.
Lemma lem993801 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem993802 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem993801 m)). Qed.
Lemma lem993803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993805 : term51 = term51.
Proof. exact (MK_COMB (@lem993803) (@lem993802)). Qed.
Lemma lem993806 (h1 : term58) : term51.
Proof. exact (EQ_MP (@lem993805) (@lem993718 h1)). Qed.
Lemma lem993815 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem993816 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem993815 m)). Qed.
Lemma lem993817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem993819 : term41 = term41.
Proof. exact (MK_COMB (@lem993817) (@lem993816)). Qed.
Lemma lem993820 (h1 : term58) : term41.
Proof. exact (EQ_MP (@lem993819) (@lem993722 h1)). Qed.
Lemma lem993844 (m : nat) (h1 : term61 m) : term61 m.
Proof. exact (h1). Qed.
Lemma lem993845 (_16088 : nat) (h1 : term10) : term62 _16088.
Proof. exact (@lem993733 h1 _16088). Qed.
Lemma lem993846 (_16088 : nat) : (term62 _16088) = ((NUMERAL _16088) = _16088).
Proof. exact (eq_refl (term62 _16088)). Qed.
Lemma lem993848 (_16089 : nat) (h1 : term58) : term63 _16089.
Proof. exact (@lem993740 h1 _16089). Qed.
Lemma lem993849 (_16089 : nat) : (term63 _16089) = ((term54 _16089) = (NUMERAL 0)).
Proof. exact (eq_refl (term63 _16089)). Qed.
Lemma lem993857 (_16092 : nat) (h1 : term58) : term64 _16092.
Proof. exact (@lem993761 h1 _16092). Qed.
Lemma lem993858 (_16092 : nat) : (term64 _16092) = ((term39 _16092) = _16092).
Proof. exact (eq_refl (term64 _16092)). Qed.
Lemma lem993872 (_16097 : nat) (h1 : term10) : term62 _16097.
Proof. exact (@lem993792 h1 _16097). Qed.
Lemma lem993873 (_16097 : nat) : (term62 _16097) = ((NUMERAL _16097) = _16097).
Proof. exact (eq_refl (term62 _16097)). Qed.
Lemma lem993878 (_16099 : nat) (h1 : term58) : term65 _16099.
Proof. exact (@lem993806 h1 _16099). Qed.
Lemma lem993879 (_16099 : nat) : (term65 _16099) = ((term49 _16099) = (NUMERAL 0)).
Proof. exact (eq_refl (term65 _16099)). Qed.
Lemma lem993884 (_16101 : nat) (h1 : term58) : term64 _16101.
Proof. exact (@lem993820 h1 _16101). Qed.
Lemma lem993885 (_16101 : nat) : (term64 _16101) = ((term39 _16101) = _16101).
Proof. exact (eq_refl (term64 _16101)). Qed.
Lemma lem993914 (n : nat) (h1 : term60 n) : term60 n.
Proof. exact (h1). Qed.
Lemma lem993930 (m : nat) (h1 : term61 m) : term61 m.
Proof. exact (h1). Qed.
Lemma lem993962 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem993963 (_16114 : nat) (_16116 : nat) (h1 : _16114 = _16116) : _16114 = _16116.
Proof. exact (h1). Qed.
Lemma lem993964 (_16115 : nat) (_16117 : nat) (h1 : _16115 = _16117) : _16115 = _16117.
Proof. exact (h1). Qed.
Lemma lem993965 (_16114 : nat) (_16116 : nat) (h1 : _16114 = _16116) : (Nat.mul _16114) = (Nat.mul _16116).
Proof. exact (MK_COMB (@lem993962) (@lem993963 _16114 _16116 h1)). Qed.
Lemma lem993966 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) (h1 : _16114 = _16116) (h2 : _16115 = _16117) : (Nat.mul _16114 _16115) = (Nat.mul _16116 _16117).
Proof. exact (MK_COMB (@lem993965 _16114 _16116 h1) (@lem993964 _16115 _16117 h2)). Qed.
Lemma lem993967 (_16115 : nat) (_16117 : nat) (_16114 : nat) (_16116 : nat) (h1 : _16114 = _16116) : term66 _16114 _16115 _16116 _16117.
Proof. exact (fun h0 : _16115 = _16117 => @lem993966 _16114 _16116 _16115 _16117 h1 h0). Qed.
Lemma lem993969 (a : Prop) (b : Prop) : (a -> b) = (term67 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem993970 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : (term66 _16114 _16115 _16116 _16117) = (term68 _16114 _16115 _16116 _16117).
Proof. exact (@lem993969 (_16115 = _16117) ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117))). Qed.
Lemma lem993971 (_16115 : nat) (_16117 : nat) (_16114 : nat) (_16116 : nat) (h1 : _16114 = _16116) : term68 _16114 _16115 _16116 _16117.
Proof. exact (EQ_MP (@lem993970 _16114 _16115 _16116 _16117) (@lem993967 _16115 _16117 _16114 _16116 h1)). Qed.
Lemma lem993972 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : term69 _16114 _16115 _16116 _16117.
Proof. exact (fun h0 : _16114 = _16116 => @lem993971 _16115 _16117 _16114 _16116 h0). Qed.
Lemma lem993974 (a : Prop) (b : Prop) : (a -> b) = (term67 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem993975 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : (term69 _16114 _16115 _16116 _16117) = (term70 _16114 _16115 _16116 _16117).
Proof. exact (@lem993974 (_16114 = _16116) (term68 _16114 _16115 _16116 _16117)). Qed.
Lemma lem993976 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : term70 _16114 _16115 _16116 _16117.
Proof. exact (EQ_MP (@lem993975 _16114 _16115 _16116 _16117) (@lem993972 _16114 _16115 _16116 _16117)). Qed.
Lemma lem993986 (x : nat) (y : nat) (z : nat) : term71 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem993988 (_16089 : nat) (h1 : term58) : (term54 _16089) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem993849 _16089) (@lem993848 _16089 h1)). Qed.
Lemma lem993989 (n : nat) (h1 : term58) : (term72 n) = (NUMERAL 0).
Proof. exact (@lem993988 (term39 n) h1). Qed.
Lemma lem993990 (n : nat) (h1 : term58) : term73 n.
Proof. exact (fun h0 : term74 n => @lem993989 n h1). Qed.
Lemma lem993992 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem993993 (n : nat) : (term73 n) = ((term72 n) = (NUMERAL 0)).
Proof. exact (@lem993992 ((term72 n) = (NUMERAL 0))). Qed.
Lemma lem993994 (n : nat) (h1 : term58) : (term72 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem993993 n) (@lem993990 n h1)). Qed.
Lemma lem993996 (_16088 : nat) (h1 : term10) : (NUMERAL _16088) = _16088.
Proof. exact (EQ_MP (@lem993846 _16088) (@lem993845 _16088 h1)). Qed.
Lemma lem993997 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (@lem993996 0 h1). Qed.
Lemma lem993998 (h1 : term10) : term76.
Proof. exact (fun h0 : term77 => @lem993997 h1). Qed.
Lemma lem994000 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994001 : term76 = ((NUMERAL 0) = 0).
Proof. exact (@lem994000 ((NUMERAL 0) = 0)). Qed.
Lemma lem994002 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem994001) (@lem993998 h1)). Qed.
Lemma lem994004 (_16092 : nat) (h1 : term58) : (term39 _16092) = _16092.
Proof. exact (EQ_MP (@lem993858 _16092) (@lem993857 _16092 h1)). Qed.
Lemma lem994005 (n : nat) (h1 : term58) : (term39 n) = n.
Proof. exact (@lem994004 n h1). Qed.
Lemma lem994006 (n : nat) (h1 : term58) : term78 n.
Proof. exact (fun h0 : term79 n => @lem994005 n h1). Qed.
Lemma lem994008 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994009 (n : nat) : (term78 n) = ((term39 n) = n).
Proof. exact (@lem994008 ((term39 n) = n)). Qed.
Lemma lem994010 (n : nat) (h1 : term58) : (term39 n) = n.
Proof. exact (EQ_MP (@lem994009 n) (@lem994006 n h1)). Qed.
Lemma lem994028 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem994029 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term68 _16114 _16115 _16116 _16117) = (term80 _16114 _16116 _16115 _16117).
Proof. exact (@lem994028 ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117)) (term81 _16115 _16117)). Qed.
Lemma lem994039 (_16114 : nat) (_16116 : nat) : (term82 _16114 _16116) = (term82 _16114 _16116).
Proof. exact (eq_refl (term82 _16114 _16116)). Qed.
Lemma lem994040 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term70 _16114 _16115 _16116 _16117) = (term83 _16114 _16116 _16115 _16117).
Proof. exact (MK_COMB (@lem994039 _16114 _16116) (@lem994029 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994044 (q : Prop) (p : Prop) (r : Prop) : (term84 p q r) = (term84 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem994045 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term83 _16114 _16116 _16115 _16117) = (term85 _16114 _16116 _16115 _16117).
Proof. exact (@lem994044 ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117)) (term81 _16114 _16116) (term81 _16115 _16117)). Qed.
Lemma lem994067 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term70 _16114 _16115 _16116 _16117) = (term85 _16114 _16116 _16115 _16117).
Proof. exact (TRANS (@lem994040 _16114 _16116 _16115 _16117) (@lem994045 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem994069 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term86 _16114 _16115 _16116 _16117) = (term87 _16114 _16116 _16115 _16117).
Proof. exact (MK_COMB (@lem994068) (@lem994067 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994091 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term85 _16114 _16116 _16115 _16117) = (term85 _16114 _16116 _16115 _16117).
Proof. exact (eq_refl (term85 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994092 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : ((term70 _16114 _16115 _16116 _16117) = (term85 _16114 _16116 _16115 _16117)) = ((term85 _16114 _16116 _16115 _16117) = (term85 _16114 _16116 _16115 _16117)).
Proof. exact (MK_COMB (@lem994069 _16114 _16116 _16115 _16117) (@lem994091 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994094 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem994095 (x : Prop) : (x = x) = True.
Proof. exact (@lem994094 Prop x). Qed.
Lemma lem994096 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : ((term85 _16114 _16116 _16115 _16117) = (term85 _16114 _16116 _16115 _16117)) = True.
Proof. exact (@lem994095 (term85 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994097 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : ((term70 _16114 _16115 _16116 _16117) = (term85 _16114 _16116 _16115 _16117)) = True.
Proof. exact (TRANS (@lem994092 _16114 _16116 _16115 _16117) (@lem994096 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994098 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : True = ((term70 _16114 _16115 _16116 _16117) = (term85 _16114 _16116 _16115 _16117)).
Proof. exact (SYM (@lem994097 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994099 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term70 _16114 _16115 _16116 _16117) = (term85 _16114 _16116 _16115 _16117).
Proof. exact (EQ_MP (@lem994098 _16114 _16116 _16115 _16117) (@lem0)). Qed.
Lemma lem994100 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : term85 _16114 _16116 _16115 _16117.
Proof. exact (EQ_MP (@lem994099 _16114 _16116 _16115 _16117) (@lem993976 _16114 _16115 _16116 _16117)). Qed.
Lemma lem994102 (b : Prop) (a : Prop) : (a \/ b) = (term88 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem994103 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : (term85 _16114 _16116 _16115 _16117) = (term89 _16114 _16115 _16116 _16117).
Proof. exact (@lem994102 (term90 _16114 _16116 _16115 _16117) ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117))). Qed.
Lemma lem994105 (a : Prop) (b : Prop) : (term91 a b) = (term92 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem994106 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term93 _16114 _16116 _16115 _16117) = (term94 _16114 _16116 _16115 _16117).
Proof. exact (@lem994105 (term81 _16114 _16116) (term81 _16115 _16117)). Qed.
Lemma lem994108 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994109 (_16114 : nat) (_16116 : nat) : (term96 _16114 _16116) = (_16114 = _16116).
Proof. exact (@lem994108 (_16114 = _16116)). Qed.
Lemma lem994110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994111 (_16114 : nat) (_16116 : nat) : (term97 _16114 _16116) = (term98 _16114 _16116).
Proof. exact (MK_COMB (@lem994110) (@lem994109 _16114 _16116)). Qed.
Lemma lem994113 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994114 (_16115 : nat) (_16117 : nat) : (term96 _16115 _16117) = (_16115 = _16117).
Proof. exact (@lem994113 (_16115 = _16117)). Qed.
Lemma lem994115 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term94 _16114 _16116 _16115 _16117) = (term99 _16114 _16116 _16115 _16117).
Proof. exact (MK_COMB (@lem994111 _16114 _16116) (@lem994114 _16115 _16117)). Qed.
Lemma lem994116 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term93 _16114 _16116 _16115 _16117) = (term99 _16114 _16116 _16115 _16117).
Proof. exact (TRANS (@lem994106 _16114 _16116 _16115 _16117) (@lem994115 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem994118 (_16114 : nat) (_16116 : nat) (_16115 : nat) (_16117 : nat) : (term100 _16114 _16116 _16115 _16117) = (term101 _16114 _16116 _16115 _16117).
Proof. exact (MK_COMB (@lem994117) (@lem994116 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994119 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117)) = ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117)).
Proof. exact (eq_refl ((Nat.mul _16114 _16115) = (Nat.mul _16116 _16117))). Qed.
Lemma lem994120 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : (term89 _16114 _16115 _16116 _16117) = (term102 _16114 _16115 _16116 _16117).
Proof. exact (MK_COMB (@lem994118 _16114 _16116 _16115 _16117) (@lem994119 _16114 _16115 _16116 _16117)). Qed.
Lemma lem994121 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : (term85 _16114 _16116 _16115 _16117) = (term102 _16114 _16115 _16116 _16117).
Proof. exact (TRANS (@lem994103 _16114 _16115 _16116 _16117) (@lem994120 _16114 _16115 _16116 _16117)). Qed.
Lemma lem994123 (n : nat) (h1 : term10) (h2 : term58) : term103 n.
Proof. exact (conj (@lem994002 h1) (@lem994010 n h2)). Qed.
Lemma lem994125 (_16114 : nat) (_16115 : nat) (_16116 : nat) (_16117 : nat) : term102 _16114 _16115 _16116 _16117.
Proof. exact (EQ_MP (@lem994121 _16114 _16115 _16116 _16117) (@lem994100 _16114 _16116 _16115 _16117)). Qed.
Lemma lem994126 (n : nat) : term104 n.
Proof. exact (@lem994125 (NUMERAL 0) (term39 n) 0 n). Qed.
Lemma lem994129 (n : nat) (h1 : term10) (h2 : term58) : (term72 n) = (Nat.mul 0 n).
Proof. exact (@lem994126 n (@lem994123 n h1 h2)). Qed.
Lemma lem994130 (n : nat) (h1 : term10) (h2 : term58) : term105 n.
Proof. exact (fun h0 : term106 n => @lem994129 n h1 h2). Qed.
Lemma lem994132 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994133 (n : nat) : (term105 n) = ((term72 n) = (Nat.mul 0 n)).
Proof. exact (@lem994132 ((term72 n) = (Nat.mul 0 n))). Qed.
Lemma lem994134 (n : nat) (h1 : term10) (h2 : term58) : (term72 n) = (Nat.mul 0 n).
Proof. exact (EQ_MP (@lem994133 n) (@lem994130 n h1 h2)). Qed.
Lemma lem994152 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem994153 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term108 y x z).
Proof. exact (@lem994152 (y = z) (term81 x z)). Qed.
Lemma lem994163 (x : nat) (y : nat) : (term82 x y) = (term82 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem994164 (y : nat) (x : nat) (z : nat) : (term71 x y z) = (term109 y x z).
Proof. exact (MK_COMB (@lem994163 x y) (@lem994153 y x z)). Qed.
Lemma lem994168 (q : Prop) (p : Prop) (r : Prop) : (term84 p q r) = (term84 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem994169 (y : nat) (x : nat) (z : nat) : (term109 y x z) = (term110 y x z).
Proof. exact (@lem994168 (y = z) (term81 x y) (term81 x z)). Qed.
Lemma lem994191 (y : nat) (x : nat) (z : nat) : (term71 x y z) = (term110 y x z).
Proof. exact (TRANS (@lem994164 y x z) (@lem994169 y x z)). Qed.
Lemma lem994192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem994193 (y : nat) (x : nat) (z : nat) : (term111 x y z) = (term112 y x z).
Proof. exact (MK_COMB (@lem994192) (@lem994191 y x z)). Qed.
Lemma lem994215 (y : nat) (x : nat) (z : nat) : (term110 y x z) = (term110 y x z).
Proof. exact (eq_refl (term110 y x z)). Qed.
Lemma lem994216 (y : nat) (x : nat) (z : nat) : ((term71 x y z) = (term110 y x z)) = ((term110 y x z) = (term110 y x z)).
Proof. exact (MK_COMB (@lem994193 y x z) (@lem994215 y x z)). Qed.
Lemma lem994218 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem994219 (x : Prop) : (x = x) = True.
Proof. exact (@lem994218 Prop x). Qed.
Lemma lem994220 (y : nat) (x : nat) (z : nat) : ((term110 y x z) = (term110 y x z)) = True.
Proof. exact (@lem994219 (term110 y x z)). Qed.
Lemma lem994221 (y : nat) (x : nat) (z : nat) : ((term71 x y z) = (term110 y x z)) = True.
Proof. exact (TRANS (@lem994216 y x z) (@lem994220 y x z)). Qed.
Lemma lem994222 (y : nat) (x : nat) (z : nat) : True = ((term71 x y z) = (term110 y x z)).
Proof. exact (SYM (@lem994221 y x z)). Qed.
Lemma lem994223 (y : nat) (x : nat) (z : nat) : (term71 x y z) = (term110 y x z).
Proof. exact (EQ_MP (@lem994222 y x z) (@lem0)). Qed.
Lemma lem994224 (y : nat) (x : nat) (z : nat) : term110 y x z.
Proof. exact (EQ_MP (@lem994223 y x z) (@lem993986 x y z)). Qed.
Lemma lem994226 (b : Prop) (a : Prop) : (a \/ b) = (term88 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem994227 (x : nat) (y : nat) (z : nat) : (term110 y x z) = (term113 x y z).
Proof. exact (@lem994226 (term114 y x z) (y = z)). Qed.
Lemma lem994229 (a : Prop) (b : Prop) : (term91 a b) = (term92 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem994230 (y : nat) (x : nat) (z : nat) : (term115 y x z) = (term116 y x z).
Proof. exact (@lem994229 (term81 x y) (term81 x z)). Qed.
Lemma lem994232 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994233 (x : nat) (y : nat) : (term96 x y) = (x = y).
Proof. exact (@lem994232 (x = y)). Qed.
Lemma lem994234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994235 (x : nat) (y : nat) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem994234) (@lem994233 x y)). Qed.
Lemma lem994237 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994238 (x : nat) (z : nat) : (term96 x z) = (x = z).
Proof. exact (@lem994237 (x = z)). Qed.
Lemma lem994239 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term117 y x z).
Proof. exact (MK_COMB (@lem994235 x y) (@lem994238 x z)). Qed.
Lemma lem994240 (y : nat) (x : nat) (z : nat) : (term115 y x z) = (term117 y x z).
Proof. exact (TRANS (@lem994230 y x z) (@lem994239 y x z)). Qed.
Lemma lem994241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem994242 (y : nat) (x : nat) (z : nat) : (term118 y x z) = (term119 y x z).
Proof. exact (MK_COMB (@lem994241) (@lem994240 y x z)). Qed.
Lemma lem994243 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem994244 (x : nat) (y : nat) (z : nat) : (term113 x y z) = (term120 x y z).
Proof. exact (MK_COMB (@lem994242 y x z) (@lem994243 y z)). Qed.
Lemma lem994245 (x : nat) (y : nat) (z : nat) : (term110 y x z) = (term120 x y z).
Proof. exact (TRANS (@lem994227 x y z) (@lem994244 x y z)). Qed.
Lemma lem994247 (n : nat) (h1 : term10) (h2 : term58) : term121 n.
Proof. exact (conj (@lem993994 n h2) (@lem994134 n h1 h2)). Qed.
Lemma lem994249 (x : nat) (y : nat) (z : nat) : term120 x y z.
Proof. exact (EQ_MP (@lem994245 x y z) (@lem994224 y x z)). Qed.
Lemma lem994250 (n : nat) : term122 n.
Proof. exact (@lem994249 (term72 n) (NUMERAL 0) (Nat.mul 0 n)). Qed.
Lemma lem994253 (n : nat) (h1 : term10) (h2 : term58) : (NUMERAL 0) = (Nat.mul 0 n).
Proof. exact (@lem994250 n (@lem994247 n h1 h2)). Qed.
Lemma lem994254 (n : nat) (h1 : term10) (h2 : term58) : term123 n.
Proof. exact (fun h0 : term124 n => @lem994253 n h1 h2). Qed.
Lemma lem994256 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994257 (n : nat) : (term123 n) = ((NUMERAL 0) = (Nat.mul 0 n)).
Proof. exact (@lem994256 ((NUMERAL 0) = (Nat.mul 0 n))). Qed.
Lemma lem994258 (n : nat) (h1 : term10) (h2 : term58) : (NUMERAL 0) = (Nat.mul 0 n).
Proof. exact (EQ_MP (@lem994257 n) (@lem994254 n h1 h2)). Qed.
Lemma lem994260 (_16088 : nat) (h1 : term10) : (NUMERAL _16088) = _16088.
Proof. exact (EQ_MP (@lem993846 _16088) (@lem993845 _16088 h1)). Qed.
Lemma lem994261 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (@lem994260 0 h1). Qed.
Lemma lem994262 (h1 : term10) : term76.
Proof. exact (fun h0 : term77 => @lem994261 h1). Qed.
Lemma lem994264 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994265 : term76 = ((NUMERAL 0) = 0).
Proof. exact (@lem994264 ((NUMERAL 0) = 0)). Qed.
Lemma lem994266 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem994265) (@lem994262 h1)). Qed.
Lemma lem994267 (n : nat) (h1 : term10) (h2 : term58) : term125 n.
Proof. exact (conj (@lem994258 n h1 h2) (@lem994266 h1)). Qed.
Lemma lem994269 (x : nat) (y : nat) (z : nat) : term120 x y z.
Proof. exact (EQ_MP (@lem994245 x y z) (@lem994224 y x z)). Qed.
Lemma lem994270 (n : nat) : term126 n.
Proof. exact (@lem994269 (NUMERAL 0) (Nat.mul 0 n) 0). Qed.
Lemma lem994273 (n : nat) (h1 : term10) (h2 : term58) : (Nat.mul 0 n) = 0.
Proof. exact (@lem994270 n (@lem994267 n h1 h2)). Qed.
Lemma lem994274 (n : nat) (h1 : term10) (h2 : term58) : term127 n.
Proof. exact (fun h0 : term60 n => @lem994273 n h1 h2). Qed.
Lemma lem994276 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994277 (n : nat) : (term127 n) = ((Nat.mul 0 n) = 0).
Proof. exact (@lem994276 ((Nat.mul 0 n) = 0)). Qed.
Lemma lem994278 (n : nat) (h1 : term10) (h2 : term58) : (Nat.mul 0 n) = 0.
Proof. exact (EQ_MP (@lem994277 n) (@lem994274 n h1 h2)). Qed.
Lemma lem994281 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem994283 (n : nat) : (term60 n) = (term128 n).
Proof. exact (@lem994281 ((Nat.mul 0 n) = 0)). Qed.
Lemma lem994286 (n : nat) (h1 : term60 n) : term128 n.
Proof. exact (EQ_MP (@lem994283 n) (@lem993914 n h1)). Qed.
Lemma lem994289 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : False.
Proof. exact (@lem994286 n h2 (@lem994278 n h1 h3)). Qed.
Lemma lem994290 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : term129.
Proof. exact (fun h0 : ~ False => @lem994289 n h1 h2 h3). Qed.
Lemma lem994292 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994293 : term129 = False.
Proof. exact (@lem994292 False). Qed.
Lemma lem994294 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994293) (@lem994290 n h1 h2 h3)). Qed.
Lemma lem994326 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem994327 (_16128 : nat) (_16130 : nat) (h1 : _16128 = _16130) : _16128 = _16130.
Proof. exact (h1). Qed.
Lemma lem994328 (_16129 : nat) (_16131 : nat) (h1 : _16129 = _16131) : _16129 = _16131.
Proof. exact (h1). Qed.
Lemma lem994329 (_16128 : nat) (_16130 : nat) (h1 : _16128 = _16130) : (Nat.mul _16128) = (Nat.mul _16130).
Proof. exact (MK_COMB (@lem994326) (@lem994327 _16128 _16130 h1)). Qed.
Lemma lem994330 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) (h1 : _16128 = _16130) (h2 : _16129 = _16131) : (Nat.mul _16128 _16129) = (Nat.mul _16130 _16131).
Proof. exact (MK_COMB (@lem994329 _16128 _16130 h1) (@lem994328 _16129 _16131 h2)). Qed.
Lemma lem994331 (_16129 : nat) (_16131 : nat) (_16128 : nat) (_16130 : nat) (h1 : _16128 = _16130) : term66 _16128 _16129 _16130 _16131.
Proof. exact (fun h0 : _16129 = _16131 => @lem994330 _16128 _16130 _16129 _16131 h1 h0). Qed.
Lemma lem994333 (a : Prop) (b : Prop) : (a -> b) = (term67 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem994334 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : (term66 _16128 _16129 _16130 _16131) = (term68 _16128 _16129 _16130 _16131).
Proof. exact (@lem994333 (_16129 = _16131) ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131))). Qed.
Lemma lem994335 (_16129 : nat) (_16131 : nat) (_16128 : nat) (_16130 : nat) (h1 : _16128 = _16130) : term68 _16128 _16129 _16130 _16131.
Proof. exact (EQ_MP (@lem994334 _16128 _16129 _16130 _16131) (@lem994331 _16129 _16131 _16128 _16130 h1)). Qed.
Lemma lem994336 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : term69 _16128 _16129 _16130 _16131.
Proof. exact (fun h0 : _16128 = _16130 => @lem994335 _16129 _16131 _16128 _16130 h0). Qed.
Lemma lem994338 (a : Prop) (b : Prop) : (a -> b) = (term67 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem994339 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : (term69 _16128 _16129 _16130 _16131) = (term70 _16128 _16129 _16130 _16131).
Proof. exact (@lem994338 (_16128 = _16130) (term68 _16128 _16129 _16130 _16131)). Qed.
Lemma lem994340 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : term70 _16128 _16129 _16130 _16131.
Proof. exact (EQ_MP (@lem994339 _16128 _16129 _16130 _16131) (@lem994336 _16128 _16129 _16130 _16131)). Qed.
Lemma lem994350 (x : nat) (y : nat) (z : nat) : term71 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem994352 (_16099 : nat) (h1 : term58) : (term49 _16099) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem993879 _16099) (@lem993878 _16099 h1)). Qed.
Lemma lem994353 (m : nat) (h1 : term58) : (term130 m) = (NUMERAL 0).
Proof. exact (@lem994352 (term39 m) h1). Qed.
Lemma lem994354 (m : nat) (h1 : term58) : term131 m.
Proof. exact (fun h0 : term132 m => @lem994353 m h1). Qed.
Lemma lem994356 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994357 (m : nat) : (term131 m) = ((term130 m) = (NUMERAL 0)).
Proof. exact (@lem994356 ((term130 m) = (NUMERAL 0))). Qed.
Lemma lem994358 (m : nat) (h1 : term58) : (term130 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem994357 m) (@lem994354 m h1)). Qed.
Lemma lem994360 (_16101 : nat) (h1 : term58) : (term39 _16101) = _16101.
Proof. exact (EQ_MP (@lem993885 _16101) (@lem993884 _16101 h1)). Qed.
Lemma lem994361 (m : nat) (h1 : term58) : (term39 m) = m.
Proof. exact (@lem994360 m h1). Qed.
Lemma lem994362 (m : nat) (h1 : term58) : term78 m.
Proof. exact (fun h0 : term79 m => @lem994361 m h1). Qed.
Lemma lem994364 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994365 (m : nat) : (term78 m) = ((term39 m) = m).
Proof. exact (@lem994364 ((term39 m) = m)). Qed.
Lemma lem994366 (m : nat) (h1 : term58) : (term39 m) = m.
Proof. exact (EQ_MP (@lem994365 m) (@lem994362 m h1)). Qed.
Lemma lem994368 (_16097 : nat) (h1 : term10) : (NUMERAL _16097) = _16097.
Proof. exact (EQ_MP (@lem993873 _16097) (@lem993872 _16097 h1)). Qed.
Lemma lem994369 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (@lem994368 0 h1). Qed.
Lemma lem994370 (h1 : term10) : term76.
Proof. exact (fun h0 : term77 => @lem994369 h1). Qed.
Lemma lem994372 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994373 : term76 = ((NUMERAL 0) = 0).
Proof. exact (@lem994372 ((NUMERAL 0) = 0)). Qed.
Lemma lem994374 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem994373) (@lem994370 h1)). Qed.
Lemma lem994392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem994393 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term68 _16128 _16129 _16130 _16131) = (term80 _16128 _16130 _16129 _16131).
Proof. exact (@lem994392 ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131)) (term81 _16129 _16131)). Qed.
Lemma lem994403 (_16128 : nat) (_16130 : nat) : (term82 _16128 _16130) = (term82 _16128 _16130).
Proof. exact (eq_refl (term82 _16128 _16130)). Qed.
Lemma lem994404 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term70 _16128 _16129 _16130 _16131) = (term83 _16128 _16130 _16129 _16131).
Proof. exact (MK_COMB (@lem994403 _16128 _16130) (@lem994393 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994408 (q : Prop) (p : Prop) (r : Prop) : (term84 p q r) = (term84 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem994409 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term83 _16128 _16130 _16129 _16131) = (term85 _16128 _16130 _16129 _16131).
Proof. exact (@lem994408 ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131)) (term81 _16128 _16130) (term81 _16129 _16131)). Qed.
Lemma lem994431 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term70 _16128 _16129 _16130 _16131) = (term85 _16128 _16130 _16129 _16131).
Proof. exact (TRANS (@lem994404 _16128 _16130 _16129 _16131) (@lem994409 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem994433 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term86 _16128 _16129 _16130 _16131) = (term87 _16128 _16130 _16129 _16131).
Proof. exact (MK_COMB (@lem994432) (@lem994431 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994455 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term85 _16128 _16130 _16129 _16131) = (term85 _16128 _16130 _16129 _16131).
Proof. exact (eq_refl (term85 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994456 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : ((term70 _16128 _16129 _16130 _16131) = (term85 _16128 _16130 _16129 _16131)) = ((term85 _16128 _16130 _16129 _16131) = (term85 _16128 _16130 _16129 _16131)).
Proof. exact (MK_COMB (@lem994433 _16128 _16130 _16129 _16131) (@lem994455 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994458 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem994459 (x : Prop) : (x = x) = True.
Proof. exact (@lem994458 Prop x). Qed.
Lemma lem994460 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : ((term85 _16128 _16130 _16129 _16131) = (term85 _16128 _16130 _16129 _16131)) = True.
Proof. exact (@lem994459 (term85 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994461 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : ((term70 _16128 _16129 _16130 _16131) = (term85 _16128 _16130 _16129 _16131)) = True.
Proof. exact (TRANS (@lem994456 _16128 _16130 _16129 _16131) (@lem994460 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994462 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : True = ((term70 _16128 _16129 _16130 _16131) = (term85 _16128 _16130 _16129 _16131)).
Proof. exact (SYM (@lem994461 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994463 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term70 _16128 _16129 _16130 _16131) = (term85 _16128 _16130 _16129 _16131).
Proof. exact (EQ_MP (@lem994462 _16128 _16130 _16129 _16131) (@lem0)). Qed.
Lemma lem994464 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : term85 _16128 _16130 _16129 _16131.
Proof. exact (EQ_MP (@lem994463 _16128 _16130 _16129 _16131) (@lem994340 _16128 _16129 _16130 _16131)). Qed.
Lemma lem994466 (b : Prop) (a : Prop) : (a \/ b) = (term88 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem994467 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : (term85 _16128 _16130 _16129 _16131) = (term89 _16128 _16129 _16130 _16131).
Proof. exact (@lem994466 (term90 _16128 _16130 _16129 _16131) ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131))). Qed.
Lemma lem994469 (a : Prop) (b : Prop) : (term91 a b) = (term92 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem994470 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term93 _16128 _16130 _16129 _16131) = (term94 _16128 _16130 _16129 _16131).
Proof. exact (@lem994469 (term81 _16128 _16130) (term81 _16129 _16131)). Qed.
Lemma lem994472 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994473 (_16128 : nat) (_16130 : nat) : (term96 _16128 _16130) = (_16128 = _16130).
Proof. exact (@lem994472 (_16128 = _16130)). Qed.
Lemma lem994474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994475 (_16128 : nat) (_16130 : nat) : (term97 _16128 _16130) = (term98 _16128 _16130).
Proof. exact (MK_COMB (@lem994474) (@lem994473 _16128 _16130)). Qed.
Lemma lem994477 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994478 (_16129 : nat) (_16131 : nat) : (term96 _16129 _16131) = (_16129 = _16131).
Proof. exact (@lem994477 (_16129 = _16131)). Qed.
Lemma lem994479 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term94 _16128 _16130 _16129 _16131) = (term99 _16128 _16130 _16129 _16131).
Proof. exact (MK_COMB (@lem994475 _16128 _16130) (@lem994478 _16129 _16131)). Qed.
Lemma lem994480 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term93 _16128 _16130 _16129 _16131) = (term99 _16128 _16130 _16129 _16131).
Proof. exact (TRANS (@lem994470 _16128 _16130 _16129 _16131) (@lem994479 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994481 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem994482 (_16128 : nat) (_16130 : nat) (_16129 : nat) (_16131 : nat) : (term100 _16128 _16130 _16129 _16131) = (term101 _16128 _16130 _16129 _16131).
Proof. exact (MK_COMB (@lem994481) (@lem994480 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994483 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131)) = ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131)).
Proof. exact (eq_refl ((Nat.mul _16128 _16129) = (Nat.mul _16130 _16131))). Qed.
Lemma lem994484 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : (term89 _16128 _16129 _16130 _16131) = (term102 _16128 _16129 _16130 _16131).
Proof. exact (MK_COMB (@lem994482 _16128 _16130 _16129 _16131) (@lem994483 _16128 _16129 _16130 _16131)). Qed.
Lemma lem994485 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : (term85 _16128 _16130 _16129 _16131) = (term102 _16128 _16129 _16130 _16131).
Proof. exact (TRANS (@lem994467 _16128 _16129 _16130 _16131) (@lem994484 _16128 _16129 _16130 _16131)). Qed.
Lemma lem994487 (m : nat) (h1 : term10) (h2 : term58) : term133 m.
Proof. exact (conj (@lem994366 m h2) (@lem994374 h1)). Qed.
Lemma lem994489 (_16128 : nat) (_16129 : nat) (_16130 : nat) (_16131 : nat) : term102 _16128 _16129 _16130 _16131.
Proof. exact (EQ_MP (@lem994485 _16128 _16129 _16130 _16131) (@lem994464 _16128 _16130 _16129 _16131)). Qed.
Lemma lem994490 (m : nat) : term134 m.
Proof. exact (@lem994489 (term39 m) (NUMERAL 0) m 0). Qed.
Lemma lem994493 (m : nat) (h1 : term10) (h2 : term58) : (term130 m) = (Nat.mul m 0).
Proof. exact (@lem994490 m (@lem994487 m h1 h2)). Qed.
Lemma lem994494 (m : nat) (h1 : term10) (h2 : term58) : term135 m.
Proof. exact (fun h0 : term136 m => @lem994493 m h1 h2). Qed.
Lemma lem994496 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994497 (m : nat) : (term135 m) = ((term130 m) = (Nat.mul m 0)).
Proof. exact (@lem994496 ((term130 m) = (Nat.mul m 0))). Qed.
Lemma lem994498 (m : nat) (h1 : term10) (h2 : term58) : (term130 m) = (Nat.mul m 0).
Proof. exact (EQ_MP (@lem994497 m) (@lem994494 m h1 h2)). Qed.
Lemma lem994516 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem994517 (y : nat) (x : nat) (z : nat) : (term107 x y z) = (term108 y x z).
Proof. exact (@lem994516 (y = z) (term81 x z)). Qed.
Lemma lem994527 (x : nat) (y : nat) : (term82 x y) = (term82 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem994528 (y : nat) (x : nat) (z : nat) : (term71 x y z) = (term109 y x z).
Proof. exact (MK_COMB (@lem994527 x y) (@lem994517 y x z)). Qed.
Lemma lem994532 (q : Prop) (p : Prop) (r : Prop) : (term84 p q r) = (term84 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem994533 (y : nat) (x : nat) (z : nat) : (term109 y x z) = (term110 y x z).
Proof. exact (@lem994532 (y = z) (term81 x y) (term81 x z)). Qed.
Lemma lem994555 (y : nat) (x : nat) (z : nat) : (term71 x y z) = (term110 y x z).
Proof. exact (TRANS (@lem994528 y x z) (@lem994533 y x z)). Qed.
Lemma lem994556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem994557 (y : nat) (x : nat) (z : nat) : (term111 x y z) = (term112 y x z).
Proof. exact (MK_COMB (@lem994556) (@lem994555 y x z)). Qed.
Lemma lem994579 (y : nat) (x : nat) (z : nat) : (term110 y x z) = (term110 y x z).
Proof. exact (eq_refl (term110 y x z)). Qed.
Lemma lem994580 (y : nat) (x : nat) (z : nat) : ((term71 x y z) = (term110 y x z)) = ((term110 y x z) = (term110 y x z)).
Proof. exact (MK_COMB (@lem994557 y x z) (@lem994579 y x z)). Qed.
Lemma lem994582 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem994583 (x : Prop) : (x = x) = True.
Proof. exact (@lem994582 Prop x). Qed.
Lemma lem994584 (y : nat) (x : nat) (z : nat) : ((term110 y x z) = (term110 y x z)) = True.
Proof. exact (@lem994583 (term110 y x z)). Qed.
Lemma lem994585 (y : nat) (x : nat) (z : nat) : ((term71 x y z) = (term110 y x z)) = True.
Proof. exact (TRANS (@lem994580 y x z) (@lem994584 y x z)). Qed.
Lemma lem994586 (y : nat) (x : nat) (z : nat) : True = ((term71 x y z) = (term110 y x z)).
Proof. exact (SYM (@lem994585 y x z)). Qed.
Lemma lem994587 (y : nat) (x : nat) (z : nat) : (term71 x y z) = (term110 y x z).
Proof. exact (EQ_MP (@lem994586 y x z) (@lem0)). Qed.
Lemma lem994588 (y : nat) (x : nat) (z : nat) : term110 y x z.
Proof. exact (EQ_MP (@lem994587 y x z) (@lem994350 x y z)). Qed.
Lemma lem994590 (b : Prop) (a : Prop) : (a \/ b) = (term88 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem994591 (x : nat) (y : nat) (z : nat) : (term110 y x z) = (term113 x y z).
Proof. exact (@lem994590 (term114 y x z) (y = z)). Qed.
Lemma lem994593 (a : Prop) (b : Prop) : (term91 a b) = (term92 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem994594 (y : nat) (x : nat) (z : nat) : (term115 y x z) = (term116 y x z).
Proof. exact (@lem994593 (term81 x y) (term81 x z)). Qed.
Lemma lem994596 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994597 (x : nat) (y : nat) : (term96 x y) = (x = y).
Proof. exact (@lem994596 (x = y)). Qed.
Lemma lem994598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994599 (x : nat) (y : nat) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem994598) (@lem994597 x y)). Qed.
Lemma lem994601 (a : Prop) : (term95 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem994602 (x : nat) (z : nat) : (term96 x z) = (x = z).
Proof. exact (@lem994601 (x = z)). Qed.
Lemma lem994603 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term117 y x z).
Proof. exact (MK_COMB (@lem994599 x y) (@lem994602 x z)). Qed.
Lemma lem994604 (y : nat) (x : nat) (z : nat) : (term115 y x z) = (term117 y x z).
Proof. exact (TRANS (@lem994594 y x z) (@lem994603 y x z)). Qed.
Lemma lem994605 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem994606 (y : nat) (x : nat) (z : nat) : (term118 y x z) = (term119 y x z).
Proof. exact (MK_COMB (@lem994605) (@lem994604 y x z)). Qed.
Lemma lem994607 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem994608 (x : nat) (y : nat) (z : nat) : (term113 x y z) = (term120 x y z).
Proof. exact (MK_COMB (@lem994606 y x z) (@lem994607 y z)). Qed.
Lemma lem994609 (x : nat) (y : nat) (z : nat) : (term110 y x z) = (term120 x y z).
Proof. exact (TRANS (@lem994591 x y z) (@lem994608 x y z)). Qed.
Lemma lem994611 (m : nat) (h1 : term10) (h2 : term58) : term137 m.
Proof. exact (conj (@lem994358 m h2) (@lem994498 m h1 h2)). Qed.
Lemma lem994613 (x : nat) (y : nat) (z : nat) : term120 x y z.
Proof. exact (EQ_MP (@lem994609 x y z) (@lem994588 y x z)). Qed.
Lemma lem994614 (m : nat) : term138 m.
Proof. exact (@lem994613 (term130 m) (NUMERAL 0) (Nat.mul m 0)). Qed.
Lemma lem994617 (m : nat) (h1 : term10) (h2 : term58) : (NUMERAL 0) = (Nat.mul m 0).
Proof. exact (@lem994614 m (@lem994611 m h1 h2)). Qed.
Lemma lem994618 (m : nat) (h1 : term10) (h2 : term58) : term139 m.
Proof. exact (fun h0 : term140 m => @lem994617 m h1 h2). Qed.
Lemma lem994620 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994621 (m : nat) : (term139 m) = ((NUMERAL 0) = (Nat.mul m 0)).
Proof. exact (@lem994620 ((NUMERAL 0) = (Nat.mul m 0))). Qed.
Lemma lem994622 (m : nat) (h1 : term10) (h2 : term58) : (NUMERAL 0) = (Nat.mul m 0).
Proof. exact (EQ_MP (@lem994621 m) (@lem994618 m h1 h2)). Qed.
Lemma lem994624 (_16097 : nat) (h1 : term10) : (NUMERAL _16097) = _16097.
Proof. exact (EQ_MP (@lem993873 _16097) (@lem993872 _16097 h1)). Qed.
Lemma lem994625 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (@lem994624 0 h1). Qed.
Lemma lem994626 (h1 : term10) : term76.
Proof. exact (fun h0 : term77 => @lem994625 h1). Qed.
Lemma lem994628 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994629 : term76 = ((NUMERAL 0) = 0).
Proof. exact (@lem994628 ((NUMERAL 0) = 0)). Qed.
Lemma lem994630 (h1 : term10) : (NUMERAL 0) = 0.
Proof. exact (EQ_MP (@lem994629) (@lem994626 h1)). Qed.
Lemma lem994631 (m : nat) (h1 : term10) (h2 : term58) : term141 m.
Proof. exact (conj (@lem994622 m h1 h2) (@lem994630 h1)). Qed.
Lemma lem994633 (x : nat) (y : nat) (z : nat) : term120 x y z.
Proof. exact (EQ_MP (@lem994609 x y z) (@lem994588 y x z)). Qed.
Lemma lem994634 (m : nat) : term142 m.
Proof. exact (@lem994633 (NUMERAL 0) (Nat.mul m 0) 0). Qed.
Lemma lem994637 (m : nat) (h1 : term10) (h2 : term58) : (Nat.mul m 0) = 0.
Proof. exact (@lem994634 m (@lem994631 m h1 h2)). Qed.
Lemma lem994638 (m : nat) (h1 : term10) (h2 : term58) : term143 m.
Proof. exact (fun h0 : term61 m => @lem994637 m h1 h2). Qed.
Lemma lem994640 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994641 (m : nat) : (term143 m) = ((Nat.mul m 0) = 0).
Proof. exact (@lem994640 ((Nat.mul m 0) = 0)). Qed.
Lemma lem994642 (m : nat) (h1 : term10) (h2 : term58) : (Nat.mul m 0) = 0.
Proof. exact (EQ_MP (@lem994641 m) (@lem994638 m h1 h2)). Qed.
Lemma lem994645 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem994647 (m : nat) : (term61 m) = (term144 m).
Proof. exact (@lem994645 ((Nat.mul m 0) = 0)). Qed.
Lemma lem994650 (m : nat) (h1 : term61 m) : term144 m.
Proof. exact (EQ_MP (@lem994647 m) (@lem993930 m h1)). Qed.
Lemma lem994653 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : False.
Proof. exact (@lem994650 m h2 (@lem994642 m h1 h3)). Qed.
Lemma lem994654 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : term129.
Proof. exact (fun h0 : ~ False => @lem994653 m h1 h2 h3). Qed.
Lemma lem994656 (p : Prop) : (term75 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem994657 : term129 = False.
Proof. exact (@lem994656 False). Qed.
Lemma lem994658 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994657) (@lem994654 m h1 h2 h3)). Qed.
Lemma lem994659 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : (term61 m) = False.
Proof. exact (prop_ext (fun h4 : term61 m => @lem994658 m h1 h2 h3) (fun h4 : False => @lem993930 m h2)). Qed.
Lemma lem994660 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994659 m h1 h2 h3) (@lem993930 m h2)). Qed.
Lemma lem994661 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : (term60 n) = False.
Proof. exact (prop_ext (fun h4 : term60 n => @lem994294 n h1 h2 h3) (fun h4 : False => @lem993914 n h2)). Qed.
Lemma lem994662 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994661 n h1 h2 h3) (@lem993914 n h2)). Qed.
Lemma lem994663 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : (term61 m) = False.
Proof. exact (prop_ext (fun h4 : term61 m => @lem994660 m h1 h2 h3) (fun h4 : False => @lem993844 m h2)). Qed.
Lemma lem994664 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994663 m h1 h2 h3) (@lem993844 m h2)). Qed.
Lemma lem994665 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : (term60 n) = False.
Proof. exact (prop_ext (fun h4 : term60 n => @lem994662 n h1 h2 h3) (fun h4 : False => @lem993785 n h2)). Qed.
Lemma lem994666 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994665 n h1 h2 h3) (@lem993785 n h2)). Qed.
Lemma lem994667 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : (term61 m) = False.
Proof. exact (prop_ext (fun h4 : term61 m => @lem994664 m h1 h2 h3) (fun h4 : False => @lem993844 m h2)). Qed.
Lemma lem994668 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994667 m h1 h2 h3) (@lem993844 m h2)). Qed.
Lemma lem994669 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem994668 m h1 h2 h3) (fun h4 : False => @lem993792 h1)). Qed.
Lemma lem994670 (m : nat) (h1 : term10) (h2 : term61 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994669 m h1 h2 h3) (@lem993792 h1)). Qed.
Lemma lem994671 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : (term60 n) = False.
Proof. exact (prop_ext (fun h4 : term60 n => @lem994666 n h1 h2 h3) (fun h4 : False => @lem993785 n h2)). Qed.
Lemma lem994672 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994671 n h1 h2 h3) (@lem993785 n h2)). Qed.
Lemma lem994673 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem994672 n h1 h2 h3) (fun h4 : False => @lem993733 h1)). Qed.
Lemma lem994674 (n : nat) (h1 : term10) (h2 : term60 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994673 n h1 h2 h3) (@lem993733 h1)). Qed.
Lemma lem994675 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (or_elim (@lem993573 n m h2) (fun h0 : term60 n => @lem994674 n h1 h0 h3) (fun h0 : term61 m => @lem994670 m h1 h0 h3)). Qed.
Lemma lem994676 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem994675 n m h1 h2 h3) (fun h4 : False => @lem993714 h1)). Qed.
Lemma lem994677 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994676 n m h1 h2 h3) (@lem993714 h1)). Qed.
Lemma lem994678 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem994677 n m h1 h2 h3) (fun h4 : False => @lem993703 h3)). Qed.
Lemma lem994679 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994678 n m h1 h2 h3) (@lem993703 h3)). Qed.
Lemma lem994680 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem994679 n m h1 h2 h3) (fun h4 : False => @lem993547 h1)). Qed.
Lemma lem994681 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994680 n m h1 h2 h3) (@lem993547 h1)). Qed.
Lemma lem994682 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem994681 n m h1 h2 h3) (fun h4 : False => @lem993534 h3)). Qed.
Lemma lem994683 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem994682 n m h1 h2 h3) (@lem993534 h3)). Qed.
Lemma lem994684 (n : nat) (m : nat) (h1 : term3 n m) (h2 : term58) : term8.
Proof. exact (fun h0 : term10 => @lem994683 n m h0 h1 h2). Qed.
Lemma lem994685 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem994686 (n : nat) (m : nat) (h1 : term3 n m) (h2 : term58) : term9.
Proof. exact (EQ_MP (@lem994685) (@lem994684 n m h1 h2)). Qed.
Lemma lem994687 (n : nat) (m : nat) (h1 : term3 n m) : term13.
Proof. exact (fun h0 : term58 => @lem994686 n m h1 h0). Qed.
Lemma lem994688 (n : nat) (m : nat) : term15 n m.
Proof. exact (fun h0 : term3 n m => @lem994687 n m h0). Qed.
Lemma lem994693 (m : nat) : term19 m.
Proof. exact (fun n : nat => @lem994688 n m). Qed.
Lemma lem994698 : term23.
Proof. exact (fun m : nat => @lem994693 m). Qed.
Lemma lem994699 : term22.
Proof. exact (EQ_MP (@lem993437) (@lem994698)). Qed.
Lemma lem994700 (m : nat) : term145 m.
Proof. exact (@lem994699 m). Qed.
Lemma lem994701 (m : nat) : (term145 m) = (term18 m).
Proof. exact (eq_refl (term145 m)). Qed.
Lemma lem994702 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem994701 m) (@lem994700 m)). Qed.
Lemma lem994703 (m : nat) (n : nat) : term146 m n.
Proof. exact (@lem994702 m n). Qed.
Lemma lem994704 (n : nat) (m : nat) : (term146 m n) = (term4 n m).
Proof. exact (eq_refl (term146 m n)). Qed.
Lemma lem994705 (n : nat) (m : nat) : term4 n m.
Proof. exact (EQ_MP (@lem994704 n m) (@lem994703 m n)). Qed.
Lemma lem994707 (n : nat) (m : nat) : term4 n m.
Proof. exact (@lem993192 n m (@lem994705 n m)). Qed.
Lemma lem994708 (n : nat) (m : nat) (h1 : term3 n m) : term12.
Proof. exact (@lem994707 n m (@lem993177 n m h1)). Qed.
Lemma lem994709 (n : nat) (m : nat) (h1 : term3 n m) : term8.
Proof. exact (@lem994708 n m h1 (@lem81645)). Qed.
Lemma lem994710 (n : nat) (m : nat) (h1 : term3 n m) : False.
Proof. exact (@lem994709 n m h1 (@lem75543)). Qed.
Lemma lem994711 (n : nat) (m : nat) (h1 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h2 : term3 n m => @lem994710 n m h1) (fun h2 : False => @lem993177 n m h1)). Qed.
Lemma lem994712 (n : nat) (m : nat) (h1 : term3 n m) : False.
Proof. exact (EQ_MP (@lem994711 n m h1) (@lem993177 n m h1)). Qed.
Lemma lem994713 (n : nat) (m : nat) : term2 n m.
Proof. exact (fun h0 : term3 n m => @lem994712 n m h0). Qed.
Lemma lem994716 (n : nat) (m : nat) : term1 n m.
Proof. exact (EQ_MP (@lem993176 n m) (@lem994713 n m)). Qed.
