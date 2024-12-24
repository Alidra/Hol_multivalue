Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_EXISTS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SUP_SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem5301273 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5301274 : term1 = term2.
Proof. exact (@lem5301273 term1). Qed.
Lemma lem5301275 : term2 = term1.
Proof. exact (SYM (@lem5301274)). Qed.
Lemma lem5301276 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem5301279 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem5301280 : term5.
Proof. exact (fun h0 : term4 => @lem5301279 h0). Qed.
Lemma lem5301281 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem5301282 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem5301283 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem5301281 h2 (@lem5301282 h1)). Qed.
Lemma lem5301284 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem5301283 h1 h0). Qed.
Lemma lem5301285 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem5301286 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem5301284 h1 (@lem5301285 h2)). Qed.
Lemma lem5301287 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem5301286 h0 h1). Qed.
Lemma lem5301288 : term7.
Proof. exact (fun h0 : term5 => @lem5301287 h0). Qed.
Lemma lem5301291 : term5.
Proof. exact (@lem5301288 (@lem5301280)). Qed.
Lemma lem5301315 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5301316 : term8 = term9.
Proof. exact (@lem5301315 term10). Qed.
Lemma lem5301339 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem5301346 : term4 = term12.
Proof. exact (MK_COMB (@lem5301339) (@lem5301316)). Qed.
Lemma lem5301347 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5301352 (s : real -> Prop) (x : real) (b : real) : (term13 s x b) = (term13 s x b).
Proof. exact (eq_refl (term13 s x b)). Qed.
Lemma lem5301353 (s : real -> Prop) (b : real) : (term14 s b) = (term14 s b).
Proof. exact (fun_ext (fun x : real => @lem5301352 s x b)). Qed.
Lemma lem5301354 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301355 (s : real -> Prop) (b : real) : (term15 s b) = (term15 s b).
Proof. exact (MK_COMB (@lem5301354) (@lem5301353 s b)). Qed.
Lemma lem5301356 (s : real -> Prop) : (term16 s) = (term16 s).
Proof. exact (fun_ext (fun b : real => @lem5301355 s b)). Qed.
Lemma lem5301357 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301358 (s : real -> Prop) : (term17 s) = (term17 s).
Proof. exact (MK_COMB (@lem5301357) (@lem5301356 s)). Qed.
Lemma lem5301359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5301360 (s : real -> Prop) : (term18 s) = (term18 s).
Proof. exact (MK_COMB (@lem5301359) (@lem5301358 s)). Qed.
Lemma lem5301361 (s : real -> Prop) (l : real) : (term19 s l) = (term19 s l).
Proof. exact (MK_COMB (@lem5301360 s) (@lem5301347 s l)). Qed.
Lemma lem5301366 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5301367 (s : real -> Prop) (l : real) : (term21 s l) = (term21 s l).
Proof. exact (MK_COMB (@lem5301366 s) (@lem5301361 s l)). Qed.
Lemma lem5301370 (s : real -> Prop) (l : real) : (term22 s l) = (term22 s l).
Proof. exact (eq_refl (term22 s l)). Qed.
Lemma lem5301371 (s : real -> Prop) (l : real) : ((has_sup s l) = (term21 s l)) = ((has_sup s l) = (term21 s l)).
Proof. exact (MK_COMB (@lem5301370 s l) (@lem5301367 s l)). Qed.
Lemma lem5301372 (s : real -> Prop) : (term23 s) = (term23 s).
Proof. exact (fun_ext (fun l : real => @lem5301371 s l)). Qed.
Lemma lem5301373 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301374 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (MK_COMB (@lem5301373) (@lem5301372 s)). Qed.
Lemma lem5301375 : term25 = term25.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301374 s)). Qed.
Lemma lem5301376 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5301377 : term10 = term10.
Proof. exact (MK_COMB (@lem5301376) (@lem5301375)). Qed.
Lemma lem5301378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5301379 : term9 = term9.
Proof. exact (MK_COMB (@lem5301378) (@lem5301377)). Qed.
Lemma lem5301384 (s : real -> Prop) (x : real) (b : real) : (term13 s x b) = (term13 s x b).
Proof. exact (eq_refl (term13 s x b)). Qed.
Lemma lem5301385 (s : real -> Prop) (b : real) : (term14 s b) = (term14 s b).
Proof. exact (fun_ext (fun x : real => @lem5301384 s x b)). Qed.
Lemma lem5301386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301387 (s : real -> Prop) (b : real) : (term15 s b) = (term15 s b).
Proof. exact (MK_COMB (@lem5301386) (@lem5301385 s b)). Qed.
Lemma lem5301388 (s : real -> Prop) : (term16 s) = (term16 s).
Proof. exact (fun_ext (fun b : real => @lem5301387 s b)). Qed.
Lemma lem5301389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301390 (s : real -> Prop) : (term17 s) = (term17 s).
Proof. exact (MK_COMB (@lem5301389) (@lem5301388 s)). Qed.
Lemma lem5301395 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5301396 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (MK_COMB (@lem5301395 s) (@lem5301390 s)). Qed.
Lemma lem5301397 (s : real -> Prop) (l : real) : (has_sup s l) = (has_sup s l).
Proof. exact (eq_refl (has_sup s l)). Qed.
Lemma lem5301398 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (fun_ext (fun l : real => @lem5301397 s l)). Qed.
Lemma lem5301399 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301400 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (MK_COMB (@lem5301399) (@lem5301398 s)). Qed.
Lemma lem5301401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301402 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5301401) (@lem5301400 s)). Qed.
Lemma lem5301403 (s : real -> Prop) : ((term28 s) = (term26 s)) = ((term28 s) = (term26 s)).
Proof. exact (MK_COMB (@lem5301402 s) (@lem5301396 s)). Qed.
Lemma lem5301404 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301403 s)). Qed.
Lemma lem5301405 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5301406 : term1 = term1.
Proof. exact (MK_COMB (@lem5301405) (@lem5301404)). Qed.
Lemma lem5301407 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5301408 : term3 = term3.
Proof. exact (MK_COMB (@lem5301407) (@lem5301406)). Qed.
Lemma lem5301409 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5301410 : term11 = term11.
Proof. exact (MK_COMB (@lem5301409) (@lem5301408)). Qed.
Lemma lem5301411 : term12 = term12.
Proof. exact (MK_COMB (@lem5301410) (@lem5301379)). Qed.
Lemma lem5301474 : term4 = term12.
Proof. exact (TRANS (@lem5301346) (@lem5301411)). Qed.
Lemma lem5301475 : term12 = term4.
Proof. exact (SYM (@lem5301474)). Qed.
Lemma lem5301476 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem5301477 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5301479 (s : real -> Prop) (l : real) : (has_sup s l) = (has_sup s l).
Proof. exact (eq_refl (has_sup s l)). Qed.
Lemma lem5301480 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5301481 (s : real -> Prop) : (term33 s) = (term34 s).
Proof. exact (@lem5301480 (term27 s)). Qed.
Lemma lem5301482 (s : real -> Prop) (l : real) : (term35 s l) = (has_sup s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5301483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5301485 (s : real -> Prop) (l : real) : (term36 s l) = (term37 s l).
Proof. exact (MK_COMB (@lem5301483) (@lem5301482 s l)). Qed.
Lemma lem5301486 (s : real -> Prop) : (term38 s) = (term39 s).
Proof. exact (fun_ext (fun l : real => @lem5301485 s l)). Qed.
Lemma lem5301487 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301488 (s : real -> Prop) : (term34 s) = (term40 s).
Proof. exact (MK_COMB (@lem5301487) (@lem5301486 s)). Qed.
Lemma lem5301489 (s : real -> Prop) : (term33 s) = (term40 s).
Proof. exact (TRANS (@lem5301481 s) (@lem5301488 s)). Qed.
Lemma lem5301490 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (fun_ext (fun l : real => @lem5301479 s l)). Qed.
Lemma lem5301491 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301492 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (MK_COMB (@lem5301491) (@lem5301490 s)). Qed.
Lemma lem5301496 (s : real -> Prop) : (term41 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5301505 (s : real -> Prop) (x : real) (b : real) : (term42 s x b) = (term43 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5301510 (s : real -> Prop) (x : real) (b : real) : (term13 s x b) = (term44 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5301511 (P : real -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5301512 (s : real -> Prop) (b : real) : (term47 s b) = (term48 s b).
Proof. exact (@lem5301511 (term14 s b)). Qed.
Lemma lem5301513 (s : real -> Prop) (x : real) (b : real) : (term49 s b x) = (term13 s x b).
Proof. exact (eq_refl (term49 s b x)). Qed.
Lemma lem5301514 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5301515 (s : real -> Prop) (x : real) (b : real) : (term50 s b x) = (term42 s x b).
Proof. exact (MK_COMB (@lem5301514) (@lem5301513 s x b)). Qed.
Lemma lem5301516 (s : real -> Prop) (x : real) (b : real) : (term50 s b x) = (term43 s x b).
Proof. exact (TRANS (@lem5301515 s x b) (@lem5301505 s x b)). Qed.
Lemma lem5301517 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5301516 s x b)). Qed.
Lemma lem5301518 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301519 (s : real -> Prop) (b : real) : (term48 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5301518) (@lem5301517 s b)). Qed.
Lemma lem5301520 (s : real -> Prop) (b : real) : (term47 s b) = (term53 s b).
Proof. exact (TRANS (@lem5301512 s b) (@lem5301519 s b)). Qed.
Lemma lem5301521 (s : real -> Prop) (b : real) : (term14 s b) = (term54 s b).
Proof. exact (fun_ext (fun x : real => @lem5301510 s x b)). Qed.
Lemma lem5301522 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301523 (s : real -> Prop) (b : real) : (term15 s b) = (term55 s b).
Proof. exact (MK_COMB (@lem5301522) (@lem5301521 s b)). Qed.
Lemma lem5301524 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5301525 (s : real -> Prop) : (term56 s) = (term57 s).
Proof. exact (@lem5301524 (term16 s)). Qed.
Lemma lem5301526 (s : real -> Prop) (b : real) : (term58 s b) = (term15 s b).
Proof. exact (eq_refl (term58 s b)). Qed.
Lemma lem5301527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5301528 (s : real -> Prop) (b : real) : (term59 s b) = (term47 s b).
Proof. exact (MK_COMB (@lem5301527) (@lem5301526 s b)). Qed.
Lemma lem5301529 (s : real -> Prop) (b : real) : (term59 s b) = (term53 s b).
Proof. exact (TRANS (@lem5301528 s b) (@lem5301520 s b)). Qed.
Lemma lem5301530 (s : real -> Prop) : (term60 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5301529 s b)). Qed.
Lemma lem5301531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301532 (s : real -> Prop) : (term57 s) = (term62 s).
Proof. exact (MK_COMB (@lem5301531) (@lem5301530 s)). Qed.
Lemma lem5301533 (s : real -> Prop) : (term56 s) = (term62 s).
Proof. exact (TRANS (@lem5301525 s) (@lem5301532 s)). Qed.
Lemma lem5301534 (s : real -> Prop) : (term16 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5301523 s b)). Qed.
Lemma lem5301535 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301536 (s : real -> Prop) : (term17 s) = (term64 s).
Proof. exact (MK_COMB (@lem5301535) (@lem5301534 s)). Qed.
Lemma lem5301537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301538 (s : real -> Prop) : (term65 s) = (term66 s).
Proof. exact (MK_COMB (@lem5301537) (@lem5301496 s)). Qed.
Lemma lem5301539 (s : real -> Prop) : (term67 s) = (term68 s).
Proof. exact (MK_COMB (@lem5301538 s) (@lem5301533 s)). Qed.
Lemma lem5301540 (s : real -> Prop) : (term69 s) = (term67 s).
Proof. exact (@lem17045 (term70 s) (term17 s)). Qed.
Lemma lem5301541 (s : real -> Prop) : (term69 s) = (term68 s).
Proof. exact (TRANS (@lem5301540 s) (@lem5301539 s)). Qed.
Lemma lem5301543 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5301544 (s : real -> Prop) : (term26 s) = (term71 s).
Proof. exact (MK_COMB (@lem5301543 s) (@lem5301536 s)). Qed.
Lemma lem5301545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5301546 (s : real -> Prop) : (term72 s) = (term73 s).
Proof. exact (MK_COMB (@lem5301545) (@lem5301489 s)). Qed.
Lemma lem5301547 (s : real -> Prop) : (term74 s) = (term75 s).
Proof. exact (MK_COMB (@lem5301546 s) (@lem5301544 s)). Qed.
Lemma lem5301548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5301549 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (MK_COMB (@lem5301548) (@lem5301492 s)). Qed.
Lemma lem5301550 (s : real -> Prop) : (term77 s) = (term78 s).
Proof. exact (MK_COMB (@lem5301549 s) (@lem5301541 s)). Qed.
Lemma lem5301551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301552 (s : real -> Prop) : (term79 s) = (term80 s).
Proof. exact (MK_COMB (@lem5301551) (@lem5301550 s)). Qed.
Lemma lem5301553 (s : real -> Prop) : (term81 s) = (term82 s).
Proof. exact (MK_COMB (@lem5301552 s) (@lem5301547 s)). Qed.
Lemma lem5301554 (s : real -> Prop) : (term83 s) = (term81 s).
Proof. exact (@lem17646 (term28 s) (term26 s)). Qed.
Lemma lem5301555 (s : real -> Prop) : (term83 s) = (term82 s).
Proof. exact (TRANS (@lem5301554 s) (@lem5301553 s)). Qed.
Lemma lem5301556 (P : type1022) : (term84 P) = (term85 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5301557 : term3 = term86.
Proof. exact (@lem5301556 term30). Qed.
Lemma lem5301558 (s : real -> Prop) : (term87 s) = ((term28 s) = (term26 s)).
Proof. exact (eq_refl (term87 s)). Qed.
Lemma lem5301559 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5301560 (s : real -> Prop) : (term88 s) = (term83 s).
Proof. exact (MK_COMB (@lem5301559) (@lem5301558 s)). Qed.
Lemma lem5301561 (s : real -> Prop) : (term88 s) = (term82 s).
Proof. exact (TRANS (@lem5301560 s) (@lem5301555 s)). Qed.
Lemma lem5301562 : term89 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301561 s)). Qed.
Lemma lem5301563 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301564 : term86 = term91.
Proof. exact (MK_COMB (@lem5301563) (@lem5301562)). Qed.
Lemma lem5301565 : term3 = term91.
Proof. exact (TRANS (@lem5301557) (@lem5301564)). Qed.
Lemma lem5301567 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5301568 (P : type1022) (Q : type1022) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem5301567 (real -> Prop) P Q). Qed.
Lemma lem5301569 : term96 = term97.
Proof. exact (@lem5301568 term98 term99). Qed.
Lemma lem5301570 (s : real -> Prop) : (term100 s) = (term78 s).
Proof. exact (eq_refl (term100 s)). Qed.
Lemma lem5301571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301572 (s : real -> Prop) : (term101 s) = (term80 s).
Proof. exact (MK_COMB (@lem5301571) (@lem5301570 s)). Qed.
Lemma lem5301573 (s : real -> Prop) : (term102 s) = (term75 s).
Proof. exact (eq_refl (term102 s)). Qed.
Lemma lem5301574 (s : real -> Prop) : (term103 s) = (term82 s).
Proof. exact (MK_COMB (@lem5301572 s) (@lem5301573 s)). Qed.
Lemma lem5301575 : term104 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301574 s)). Qed.
Lemma lem5301576 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301577 : term96 = term91.
Proof. exact (MK_COMB (@lem5301576) (@lem5301575)). Qed.
Lemma lem5301578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301579 : term105 = term106.
Proof. exact (MK_COMB (@lem5301578) (@lem5301577)). Qed.
Lemma lem5301580 (s : real -> Prop) : (term100 s) = (term78 s).
Proof. exact (eq_refl (term100 s)). Qed.
Lemma lem5301581 : term107 = term98.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301580 s)). Qed.
Lemma lem5301582 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301583 : term108 = term109.
Proof. exact (MK_COMB (@lem5301582) (@lem5301581)). Qed.
Lemma lem5301584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301585 : term110 = term111.
Proof. exact (MK_COMB (@lem5301584) (@lem5301583)). Qed.
Lemma lem5301586 (s : real -> Prop) : (term102 s) = (term75 s).
Proof. exact (eq_refl (term102 s)). Qed.
Lemma lem5301587 : term112 = term99.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301586 s)). Qed.
Lemma lem5301588 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301589 : term113 = term114.
Proof. exact (MK_COMB (@lem5301588) (@lem5301587)). Qed.
Lemma lem5301590 : term97 = term115.
Proof. exact (MK_COMB (@lem5301585) (@lem5301589)). Qed.
Lemma lem5301591 : (term96 = term97) = (term91 = term115).
Proof. exact (MK_COMB (@lem5301579) (@lem5301590)). Qed.
Lemma lem5301592 : term91 = term115.
Proof. exact (EQ_MP (@lem5301591) (@lem5301569)). Qed.
Lemma lem5301802 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5301803 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (@lem5301802 real real P). Qed.
Lemma lem5301804 (s : real -> Prop) : (term120 s) = (term121 s).
Proof. exact (@lem5301803 (term122 s)). Qed.
Lemma lem5301805 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5301806 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5301807 (s : real -> Prop) (b : real) (x : real) : (term124 s b x) = (term125 s b x).
Proof. exact (MK_COMB (@lem5301805 s b) (@lem5301806 x)). Qed.
Lemma lem5301808 (s : real -> Prop) (x : real) (b : real) : (term125 s b x) = (term43 s x b).
Proof. exact (eq_refl (term125 s b x)). Qed.
Lemma lem5301809 (s : real -> Prop) (x : real) (b : real) : (term124 s b x) = (term43 s x b).
Proof. exact (TRANS (@lem5301807 s b x) (@lem5301808 s x b)). Qed.
Lemma lem5301810 (s : real -> Prop) (b : real) : (term126 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5301809 s x b)). Qed.
Lemma lem5301811 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301812 (s : real -> Prop) (b : real) : (term127 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5301811) (@lem5301810 s b)). Qed.
Lemma lem5301813 (s : real -> Prop) : (term128 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5301812 s b)). Qed.
Lemma lem5301814 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301815 (s : real -> Prop) : (term120 s) = (term62 s).
Proof. exact (MK_COMB (@lem5301814) (@lem5301813 s)). Qed.
Lemma lem5301816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301817 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5301816) (@lem5301815 s)). Qed.
Lemma lem5301818 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5301819 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5301820 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term132 s x b).
Proof. exact (MK_COMB (@lem5301818 s b) (@lem5301819 x b)). Qed.
Lemma lem5301821 (s : real -> Prop) (x : real -> real) (b : real) : (term132 s x b) = (term133 s x b).
Proof. exact (eq_refl (term132 s x b)). Qed.
Lemma lem5301822 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term133 s x b).
Proof. exact (TRANS (@lem5301820 s x b) (@lem5301821 s x b)). Qed.
Lemma lem5301823 (s : real -> Prop) (x : real -> real) : (term134 s x) = (term135 s x).
Proof. exact (fun_ext (fun b : real => @lem5301822 s x b)). Qed.
Lemma lem5301824 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5301825 (s : real -> Prop) (x : real -> real) : (term136 s x) = (term137 s x).
Proof. exact (MK_COMB (@lem5301824) (@lem5301823 s x)). Qed.
Lemma lem5301826 (s : real -> Prop) : (term138 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5301825 s x)). Qed.
Lemma lem5301827 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5301828 (s : real -> Prop) : (term121 s) = (term140 s).
Proof. exact (MK_COMB (@lem5301827) (@lem5301826 s)). Qed.
Lemma lem5301829 (s : real -> Prop) : ((term120 s) = (term121 s)) = ((term62 s) = (term140 s)).
Proof. exact (MK_COMB (@lem5301817 s) (@lem5301828 s)). Qed.
Lemma lem5301830 (s : real -> Prop) : (term62 s) = (term140 s).
Proof. exact (EQ_MP (@lem5301829 s) (@lem5301804 s)). Qed.
Lemma lem5301831 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5301832 (s : real -> Prop) : (term68 s) = (term141 s).
Proof. exact (MK_COMB (@lem5301831 s) (@lem5301830 s)). Qed.
Lemma lem5301834 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5301835 (P : Prop) (Q : type1028) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5301834 (real -> real) P Q). Qed.
Lemma lem5301836 (s : real -> Prop) : (term146 s) = (term147 s).
Proof. exact (@lem5301835 (s = (@EMPTY real)) (term139 s)). Qed.
Lemma lem5301837 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5301838 (s : real -> Prop) : (term149 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5301837 s x)). Qed.
Lemma lem5301839 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5301840 (s : real -> Prop) : (term150 s) = (term140 s).
Proof. exact (MK_COMB (@lem5301839) (@lem5301838 s)). Qed.
Lemma lem5301841 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5301842 (s : real -> Prop) : (term146 s) = (term141 s).
Proof. exact (MK_COMB (@lem5301841 s) (@lem5301840 s)). Qed.
Lemma lem5301843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301844 (s : real -> Prop) : (term151 s) = (term152 s).
Proof. exact (MK_COMB (@lem5301843) (@lem5301842 s)). Qed.
Lemma lem5301845 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5301846 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5301847 (s : real -> Prop) (x : real -> real) : (term153 s x) = (term154 s x).
Proof. exact (MK_COMB (@lem5301846 s) (@lem5301845 s x)). Qed.
Lemma lem5301848 (s : real -> Prop) : (term155 s) = (term156 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5301847 s x)). Qed.
Lemma lem5301849 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5301850 (s : real -> Prop) : (term147 s) = (term157 s).
Proof. exact (MK_COMB (@lem5301849) (@lem5301848 s)). Qed.
Lemma lem5301851 (s : real -> Prop) : ((term146 s) = (term147 s)) = ((term141 s) = (term157 s)).
Proof. exact (MK_COMB (@lem5301844 s) (@lem5301850 s)). Qed.
Lemma lem5301852 (s : real -> Prop) : (term141 s) = (term157 s).
Proof. exact (EQ_MP (@lem5301851 s) (@lem5301836 s)). Qed.
Lemma lem5301853 (s : real -> Prop) : (term68 s) = (term157 s).
Proof. exact (TRANS (@lem5301832 s) (@lem5301852 s)). Qed.
Lemma lem5301854 (s : real -> Prop) : (term76 s) = (term76 s).
Proof. exact (eq_refl (term76 s)). Qed.
Lemma lem5301855 (s : real -> Prop) : (term78 s) = (term158 s).
Proof. exact (MK_COMB (@lem5301854 s) (@lem5301853 s)). Qed.
Lemma lem5301857 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5301858 (P : real -> Prop) (Q : Prop) : (term161 P Q) = (term162 P Q).
Proof. exact (@lem5301857 real P Q). Qed.
Lemma lem5301859 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (@lem5301858 (term27 s) (term157 s)). Qed.
Lemma lem5301860 (s : real -> Prop) (l : real) : (term35 s l) = (has_sup s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5301861 (s : real -> Prop) : (term165 s) = (term27 s).
Proof. exact (fun_ext (fun l : real => @lem5301860 s l)). Qed.
Lemma lem5301862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301863 (s : real -> Prop) : (term166 s) = (term28 s).
Proof. exact (MK_COMB (@lem5301862) (@lem5301861 s)). Qed.
Lemma lem5301864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5301865 (s : real -> Prop) : (term167 s) = (term76 s).
Proof. exact (MK_COMB (@lem5301864) (@lem5301863 s)). Qed.
Lemma lem5301866 (s : real -> Prop) : (term157 s) = (term157 s).
Proof. exact (eq_refl (term157 s)). Qed.
Lemma lem5301867 (s : real -> Prop) : (term163 s) = (term158 s).
Proof. exact (MK_COMB (@lem5301865 s) (@lem5301866 s)). Qed.
Lemma lem5301868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301869 (s : real -> Prop) : (term168 s) = (term169 s).
Proof. exact (MK_COMB (@lem5301868) (@lem5301867 s)). Qed.
Lemma lem5301870 (s : real -> Prop) (l : real) : (term35 s l) = (has_sup s l).
Proof. exact (eq_refl (term35 s l)). Qed.
Lemma lem5301871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5301872 (s : real -> Prop) (l : real) : (term170 s l) = (term171 s l).
Proof. exact (MK_COMB (@lem5301871) (@lem5301870 s l)). Qed.
Lemma lem5301873 (s : real -> Prop) : (term157 s) = (term157 s).
Proof. exact (eq_refl (term157 s)). Qed.
Lemma lem5301874 (l : real) (s : real -> Prop) : (term172 l s) = (term173 l s).
Proof. exact (MK_COMB (@lem5301872 s l) (@lem5301873 s)). Qed.
Lemma lem5301875 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (fun_ext (fun l : real => @lem5301874 l s)). Qed.
Lemma lem5301876 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301877 (s : real -> Prop) : (term164 s) = (term176 s).
Proof. exact (MK_COMB (@lem5301876) (@lem5301875 s)). Qed.
Lemma lem5301878 (s : real -> Prop) : ((term163 s) = (term164 s)) = ((term158 s) = (term176 s)).
Proof. exact (MK_COMB (@lem5301869 s) (@lem5301877 s)). Qed.
Lemma lem5301879 (s : real -> Prop) : (term158 s) = (term176 s).
Proof. exact (EQ_MP (@lem5301878 s) (@lem5301859 s)). Qed.
Lemma lem5301881 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5301882 (P : Prop) (Q : type1028) : (term179 P Q) = (term180 P Q).
Proof. exact (@lem5301881 (real -> real) P Q). Qed.
Lemma lem5301883 (l : real) (s : real -> Prop) : (term181 l s) = (term182 l s).
Proof. exact (@lem5301882 (has_sup s l) (term156 s)). Qed.
Lemma lem5301884 (s : real -> Prop) (x : real -> real) : (term183 s x) = (term154 s x).
Proof. exact (eq_refl (term183 s x)). Qed.
Lemma lem5301885 (s : real -> Prop) : (term184 s) = (term156 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5301884 s x)). Qed.
Lemma lem5301886 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5301887 (s : real -> Prop) : (term185 s) = (term157 s).
Proof. exact (MK_COMB (@lem5301886) (@lem5301885 s)). Qed.
Lemma lem5301888 (s : real -> Prop) (l : real) : (term171 s l) = (term171 s l).
Proof. exact (eq_refl (term171 s l)). Qed.
Lemma lem5301889 (l : real) (s : real -> Prop) : (term181 l s) = (term173 l s).
Proof. exact (MK_COMB (@lem5301888 s l) (@lem5301887 s)). Qed.
Lemma lem5301890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301891 (l : real) (s : real -> Prop) : (term186 l s) = (term187 l s).
Proof. exact (MK_COMB (@lem5301890) (@lem5301889 l s)). Qed.
Lemma lem5301892 (s : real -> Prop) (x : real -> real) : (term183 s x) = (term154 s x).
Proof. exact (eq_refl (term183 s x)). Qed.
Lemma lem5301893 (s : real -> Prop) (l : real) : (term171 s l) = (term171 s l).
Proof. exact (eq_refl (term171 s l)). Qed.
Lemma lem5301894 (l : real) (s : real -> Prop) (x : real -> real) : (term188 l s x) = (term189 l s x).
Proof. exact (MK_COMB (@lem5301893 s l) (@lem5301892 s x)). Qed.
Lemma lem5301895 (l : real) (s : real -> Prop) : (term190 l s) = (term191 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5301894 l s x)). Qed.
Lemma lem5301896 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5301897 (l : real) (s : real -> Prop) : (term182 l s) = (term192 l s).
Proof. exact (MK_COMB (@lem5301896) (@lem5301895 l s)). Qed.
Lemma lem5301898 (l : real) (s : real -> Prop) : ((term181 l s) = (term182 l s)) = ((term173 l s) = (term192 l s)).
Proof. exact (MK_COMB (@lem5301891 l s) (@lem5301897 l s)). Qed.
Lemma lem5301899 (l : real) (s : real -> Prop) : (term173 l s) = (term192 l s).
Proof. exact (EQ_MP (@lem5301898 l s) (@lem5301883 l s)). Qed.
Lemma lem5301900 (s : real -> Prop) : (term175 s) = (term193 s).
Proof. exact (fun_ext (fun l : real => @lem5301899 l s)). Qed.
Lemma lem5301901 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301902 (s : real -> Prop) : (term176 s) = (term194 s).
Proof. exact (MK_COMB (@lem5301901) (@lem5301900 s)). Qed.
Lemma lem5301903 (s : real -> Prop) : (term158 s) = (term194 s).
Proof. exact (TRANS (@lem5301879 s) (@lem5301902 s)). Qed.
Lemma lem5301904 (s : real -> Prop) : (term78 s) = (term194 s).
Proof. exact (TRANS (@lem5301855 s) (@lem5301903 s)). Qed.
Lemma lem5301905 : term98 = term195.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301904 s)). Qed.
Lemma lem5301906 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301907 : term109 = term196.
Proof. exact (MK_COMB (@lem5301906) (@lem5301905)). Qed.
Lemma lem5301908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301909 : term111 = term197.
Proof. exact (MK_COMB (@lem5301908) (@lem5301907)). Qed.
Lemma lem5301911 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5301912 (P : Prop) (Q : real -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5301911 real P Q). Qed.
Lemma lem5301913 (s : real -> Prop) : (term200 s) = (term201 s).
Proof. exact (@lem5301912 (term70 s) (term63 s)). Qed.
Lemma lem5301914 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5301915 (s : real -> Prop) : (term203 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5301914 s b)). Qed.
Lemma lem5301916 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301917 (s : real -> Prop) : (term204 s) = (term64 s).
Proof. exact (MK_COMB (@lem5301916) (@lem5301915 s)). Qed.
Lemma lem5301918 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5301919 (s : real -> Prop) : (term200 s) = (term71 s).
Proof. exact (MK_COMB (@lem5301918 s) (@lem5301917 s)). Qed.
Lemma lem5301920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301921 (s : real -> Prop) : (term205 s) = (term206 s).
Proof. exact (MK_COMB (@lem5301920) (@lem5301919 s)). Qed.
Lemma lem5301922 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5301923 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5301924 (s : real -> Prop) (b : real) : (term207 s b) = (term208 s b).
Proof. exact (MK_COMB (@lem5301923 s) (@lem5301922 s b)). Qed.
Lemma lem5301925 (s : real -> Prop) : (term209 s) = (term210 s).
Proof. exact (fun_ext (fun b : real => @lem5301924 s b)). Qed.
Lemma lem5301926 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301927 (s : real -> Prop) : (term201 s) = (term211 s).
Proof. exact (MK_COMB (@lem5301926) (@lem5301925 s)). Qed.
Lemma lem5301928 (s : real -> Prop) : ((term200 s) = (term201 s)) = ((term71 s) = (term211 s)).
Proof. exact (MK_COMB (@lem5301921 s) (@lem5301927 s)). Qed.
Lemma lem5301929 (s : real -> Prop) : (term71 s) = (term211 s).
Proof. exact (EQ_MP (@lem5301928 s) (@lem5301913 s)). Qed.
Lemma lem5301930 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (eq_refl (term73 s)). Qed.
Lemma lem5301931 (s : real -> Prop) : (term75 s) = (term212 s).
Proof. exact (MK_COMB (@lem5301930 s) (@lem5301929 s)). Qed.
Lemma lem5301933 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5301934 (P : Prop) (Q : real -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5301933 real P Q). Qed.
Lemma lem5301935 (s : real -> Prop) : (term213 s) = (term214 s).
Proof. exact (@lem5301934 (term40 s) (term210 s)). Qed.
Lemma lem5301936 (s : real -> Prop) (b : real) : (term215 s b) = (term208 s b).
Proof. exact (eq_refl (term215 s b)). Qed.
Lemma lem5301937 (s : real -> Prop) : (term216 s) = (term210 s).
Proof. exact (fun_ext (fun b : real => @lem5301936 s b)). Qed.
Lemma lem5301938 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301939 (s : real -> Prop) : (term217 s) = (term211 s).
Proof. exact (MK_COMB (@lem5301938) (@lem5301937 s)). Qed.
Lemma lem5301940 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (eq_refl (term73 s)). Qed.
Lemma lem5301941 (s : real -> Prop) : (term213 s) = (term212 s).
Proof. exact (MK_COMB (@lem5301940 s) (@lem5301939 s)). Qed.
Lemma lem5301942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301943 (s : real -> Prop) : (term218 s) = (term219 s).
Proof. exact (MK_COMB (@lem5301942) (@lem5301941 s)). Qed.
Lemma lem5301944 (s : real -> Prop) (b : real) : (term215 s b) = (term208 s b).
Proof. exact (eq_refl (term215 s b)). Qed.
Lemma lem5301945 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (eq_refl (term73 s)). Qed.
Lemma lem5301946 (s : real -> Prop) (b : real) : (term220 s b) = (term221 s b).
Proof. exact (MK_COMB (@lem5301945 s) (@lem5301944 s b)). Qed.
Lemma lem5301947 (s : real -> Prop) : (term222 s) = (term223 s).
Proof. exact (fun_ext (fun b : real => @lem5301946 s b)). Qed.
Lemma lem5301948 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301949 (s : real -> Prop) : (term214 s) = (term224 s).
Proof. exact (MK_COMB (@lem5301948) (@lem5301947 s)). Qed.
Lemma lem5301950 (s : real -> Prop) : ((term213 s) = (term214 s)) = ((term212 s) = (term224 s)).
Proof. exact (MK_COMB (@lem5301943 s) (@lem5301949 s)). Qed.
Lemma lem5301951 (s : real -> Prop) : (term212 s) = (term224 s).
Proof. exact (EQ_MP (@lem5301950 s) (@lem5301935 s)). Qed.
Lemma lem5301952 (s : real -> Prop) : (term75 s) = (term224 s).
Proof. exact (TRANS (@lem5301931 s) (@lem5301951 s)). Qed.
Lemma lem5301953 : term99 = term225.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301952 s)). Qed.
Lemma lem5301954 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301955 : term114 = term226.
Proof. exact (MK_COMB (@lem5301954) (@lem5301953)). Qed.
Lemma lem5301956 : term115 = term227.
Proof. exact (MK_COMB (@lem5301909) (@lem5301955)). Qed.
Lemma lem5301958 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5301959 (P : type1022) (Q : type1022) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5301958 (real -> Prop) P Q). Qed.
Lemma lem5301960 : term228 = term229.
Proof. exact (@lem5301959 term195 term225). Qed.
Lemma lem5301961 (s : real -> Prop) : (term230 s) = (term194 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5301962 : term231 = term195.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301961 s)). Qed.
Lemma lem5301963 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301964 : term232 = term196.
Proof. exact (MK_COMB (@lem5301963) (@lem5301962)). Qed.
Lemma lem5301965 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301966 : term233 = term197.
Proof. exact (MK_COMB (@lem5301965) (@lem5301964)). Qed.
Lemma lem5301967 (s : real -> Prop) : (term234 s) = (term224 s).
Proof. exact (eq_refl (term234 s)). Qed.
Lemma lem5301968 : term235 = term225.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301967 s)). Qed.
Lemma lem5301969 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301970 : term236 = term226.
Proof. exact (MK_COMB (@lem5301969) (@lem5301968)). Qed.
Lemma lem5301971 : term228 = term227.
Proof. exact (MK_COMB (@lem5301966) (@lem5301970)). Qed.
Lemma lem5301972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5301973 : term237 = term238.
Proof. exact (MK_COMB (@lem5301972) (@lem5301971)). Qed.
Lemma lem5301974 (s : real -> Prop) : (term230 s) = (term194 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5301975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301976 (s : real -> Prop) : (term239 s) = (term240 s).
Proof. exact (MK_COMB (@lem5301975) (@lem5301974 s)). Qed.
Lemma lem5301977 (s : real -> Prop) : (term234 s) = (term224 s).
Proof. exact (eq_refl (term234 s)). Qed.
Lemma lem5301978 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (MK_COMB (@lem5301976 s) (@lem5301977 s)). Qed.
Lemma lem5301979 : term243 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5301978 s)). Qed.
Lemma lem5301980 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5301981 : term229 = term245.
Proof. exact (MK_COMB (@lem5301980) (@lem5301979)). Qed.
Lemma lem5301982 : (term228 = term229) = (term227 = term245).
Proof. exact (MK_COMB (@lem5301973) (@lem5301981)). Qed.
Lemma lem5301983 : term227 = term245.
Proof. exact (EQ_MP (@lem5301982) (@lem5301960)). Qed.
Lemma lem5301985 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5301986 (P : real -> Prop) (Q : real -> Prop) : (term246 P Q) = (term247 P Q).
Proof. exact (@lem5301985 real P Q). Qed.
Lemma lem5301987 (s : real -> Prop) : (term248 s) = (term249 s).
Proof. exact (@lem5301986 (term193 s) (term223 s)). Qed.
Lemma lem5301988 (l : real) (s : real -> Prop) : (term250 s l) = (term192 l s).
Proof. exact (eq_refl (term250 s l)). Qed.
Lemma lem5301989 (s : real -> Prop) : (term251 s) = (term193 s).
Proof. exact (fun_ext (fun l : real => @lem5301988 l s)). Qed.
Lemma lem5301990 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301991 (s : real -> Prop) : (term252 s) = (term194 s).
Proof. exact (MK_COMB (@lem5301990) (@lem5301989 s)). Qed.
Lemma lem5301992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5301993 (s : real -> Prop) : (term253 s) = (term240 s).
Proof. exact (MK_COMB (@lem5301992) (@lem5301991 s)). Qed.
Lemma lem5301994 (s : real -> Prop) (l : real) : (term254 s l) = (term221 s l).
Proof. exact (eq_refl (term254 s l)). Qed.
Lemma lem5301995 (s : real -> Prop) : (term255 s) = (term223 s).
Proof. exact (fun_ext (fun l : real => @lem5301994 s l)). Qed.
Lemma lem5301996 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5301997 (s : real -> Prop) : (term256 s) = (term224 s).
Proof. exact (MK_COMB (@lem5301996) (@lem5301995 s)). Qed.
Lemma lem5301998 (s : real -> Prop) : (term248 s) = (term242 s).
Proof. exact (MK_COMB (@lem5301993 s) (@lem5301997 s)). Qed.
Lemma lem5301999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302000 (s : real -> Prop) : (term257 s) = (term258 s).
Proof. exact (MK_COMB (@lem5301999) (@lem5301998 s)). Qed.
Lemma lem5302001 (l : real) (s : real -> Prop) : (term250 s l) = (term192 l s).
Proof. exact (eq_refl (term250 s l)). Qed.
Lemma lem5302002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302003 (l : real) (s : real -> Prop) : (term259 s l) = (term260 l s).
Proof. exact (MK_COMB (@lem5302002) (@lem5302001 l s)). Qed.
Lemma lem5302004 (s : real -> Prop) (l : real) : (term254 s l) = (term221 s l).
Proof. exact (eq_refl (term254 s l)). Qed.
Lemma lem5302005 (s : real -> Prop) (l : real) : (term261 s l) = (term262 s l).
Proof. exact (MK_COMB (@lem5302003 l s) (@lem5302004 s l)). Qed.
Lemma lem5302006 (s : real -> Prop) : (term263 s) = (term264 s).
Proof. exact (fun_ext (fun l : real => @lem5302005 s l)). Qed.
Lemma lem5302007 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302008 (s : real -> Prop) : (term249 s) = (term265 s).
Proof. exact (MK_COMB (@lem5302007) (@lem5302006 s)). Qed.
Lemma lem5302009 (s : real -> Prop) : ((term248 s) = (term249 s)) = ((term242 s) = (term265 s)).
Proof. exact (MK_COMB (@lem5302000 s) (@lem5302008 s)). Qed.
Lemma lem5302010 (s : real -> Prop) : (term242 s) = (term265 s).
Proof. exact (EQ_MP (@lem5302009 s) (@lem5301987 s)). Qed.
Lemma lem5302013 (s : real -> Prop) : (term266 s) = (term266 s).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5302014 (s : real -> Prop) : (term266 s) = ((term242 s) = (term265 s)).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5302015 (s : real -> Prop) : (term267 s) = (term267 s).
Proof. exact (eq_refl (term267 s)). Qed.
Lemma lem5302016 (s : real -> Prop) : ((term266 s) = (term266 s)) = ((term266 s) = ((term242 s) = (term265 s))).
Proof. exact (MK_COMB (@lem5302015 s) (@lem5302014 s)). Qed.
Lemma lem5302017 (s : real -> Prop) : (term266 s) = ((term242 s) = (term265 s)).
Proof. exact (eq_refl (term266 s)). Qed.
Lemma lem5302018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302019 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (MK_COMB (@lem5302018) (@lem5302017 s)). Qed.
Lemma lem5302020 (s : real -> Prop) : ((term242 s) = (term265 s)) = ((term242 s) = (term265 s)).
Proof. exact (eq_refl ((term242 s) = (term265 s))). Qed.
Lemma lem5302021 (s : real -> Prop) : ((term266 s) = ((term242 s) = (term265 s))) = (((term242 s) = (term265 s)) = ((term242 s) = (term265 s))).
Proof. exact (MK_COMB (@lem5302019 s) (@lem5302020 s)). Qed.
Lemma lem5302022 (s : real -> Prop) : ((term266 s) = (term266 s)) = (((term242 s) = (term265 s)) = ((term242 s) = (term265 s))).
Proof. exact (TRANS (@lem5302016 s) (@lem5302021 s)). Qed.
Lemma lem5302023 (s : real -> Prop) : ((term242 s) = (term265 s)) = ((term242 s) = (term265 s)).
Proof. exact (EQ_MP (@lem5302022 s) (@lem5302013 s)). Qed.
Lemma lem5302024 (s : real -> Prop) : (term242 s) = (term265 s).
Proof. exact (EQ_MP (@lem5302023 s) (@lem5302010 s)). Qed.
Lemma lem5302026 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5302027 (P : type1028) (Q : Prop) : (term271 P Q) = (term272 P Q).
Proof. exact (@lem5302026 (real -> real) P Q). Qed.
Lemma lem5302028 (s : real -> Prop) (l : real) : (term273 s l) = (term274 s l).
Proof. exact (@lem5302027 (term191 l s) (term221 s l)). Qed.
Lemma lem5302029 (l : real) (s : real -> Prop) (x : real -> real) : (term275 l s x) = (term189 l s x).
Proof. exact (eq_refl (term275 l s x)). Qed.
Lemma lem5302030 (l : real) (s : real -> Prop) : (term276 l s) = (term191 l s).
Proof. exact (fun_ext (fun x : real -> real => @lem5302029 l s x)). Qed.
Lemma lem5302031 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302032 (l : real) (s : real -> Prop) : (term277 l s) = (term192 l s).
Proof. exact (MK_COMB (@lem5302031) (@lem5302030 l s)). Qed.
Lemma lem5302033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302034 (l : real) (s : real -> Prop) : (term278 l s) = (term260 l s).
Proof. exact (MK_COMB (@lem5302033) (@lem5302032 l s)). Qed.
Lemma lem5302035 (s : real -> Prop) (l : real) : (term221 s l) = (term221 s l).
Proof. exact (eq_refl (term221 s l)). Qed.
Lemma lem5302036 (s : real -> Prop) (l : real) : (term273 s l) = (term262 s l).
Proof. exact (MK_COMB (@lem5302034 l s) (@lem5302035 s l)). Qed.
Lemma lem5302037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302038 (s : real -> Prop) (l : real) : (term279 s l) = (term280 s l).
Proof. exact (MK_COMB (@lem5302037) (@lem5302036 s l)). Qed.
Lemma lem5302039 (l : real) (s : real -> Prop) (x : real -> real) : (term275 l s x) = (term189 l s x).
Proof. exact (eq_refl (term275 l s x)). Qed.
Lemma lem5302040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302041 (l : real) (s : real -> Prop) (x : real -> real) : (term281 l s x) = (term282 l s x).
Proof. exact (MK_COMB (@lem5302040) (@lem5302039 l s x)). Qed.
Lemma lem5302042 (s : real -> Prop) (l : real) : (term221 s l) = (term221 s l).
Proof. exact (eq_refl (term221 s l)). Qed.
Lemma lem5302043 (x : real -> real) (s : real -> Prop) (l : real) : (term283 x s l) = (term284 x s l).
Proof. exact (MK_COMB (@lem5302041 l s x) (@lem5302042 s l)). Qed.
Lemma lem5302044 (s : real -> Prop) (l : real) : (term285 s l) = (term286 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302043 x s l)). Qed.
Lemma lem5302045 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302046 (s : real -> Prop) (l : real) : (term274 s l) = (term287 s l).
Proof. exact (MK_COMB (@lem5302045) (@lem5302044 s l)). Qed.
Lemma lem5302047 (s : real -> Prop) (l : real) : ((term273 s l) = (term274 s l)) = ((term262 s l) = (term287 s l)).
Proof. exact (MK_COMB (@lem5302038 s l) (@lem5302046 s l)). Qed.
Lemma lem5302048 (s : real -> Prop) (l : real) : (term262 s l) = (term287 s l).
Proof. exact (EQ_MP (@lem5302047 s l) (@lem5302028 s l)). Qed.
Lemma lem5302049 (s : real -> Prop) : (term264 s) = (term288 s).
Proof. exact (fun_ext (fun l : real => @lem5302048 s l)). Qed.
Lemma lem5302050 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302051 (s : real -> Prop) : (term265 s) = (term289 s).
Proof. exact (MK_COMB (@lem5302050) (@lem5302049 s)). Qed.
Lemma lem5302052 (s : real -> Prop) : (term242 s) = (term289 s).
Proof. exact (TRANS (@lem5302024 s) (@lem5302051 s)). Qed.
Lemma lem5302053 : term244 = term290.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302052 s)). Qed.
Lemma lem5302054 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5302055 : term245 = term291.
Proof. exact (MK_COMB (@lem5302054) (@lem5302053)). Qed.
Lemma lem5302056 : term227 = term291.
Proof. exact (TRANS (@lem5301983) (@lem5302055)). Qed.
Lemma lem5302057 : term115 = term291.
Proof. exact (TRANS (@lem5301956) (@lem5302056)). Qed.
Lemma lem5302058 : term91 = term291.
Proof. exact (TRANS (@lem5301592) (@lem5302057)). Qed.
Lemma lem5302059 : term3 = term291.
Proof. exact (TRANS (@lem5301565) (@lem5302058)). Qed.
Lemma lem5302060 (h1 : term3) : term291.
Proof. exact (EQ_MP (@lem5302059) (@lem5301476 h1)). Qed.
Lemma lem5302066 (s : real -> Prop) : (term41 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5302075 (s : real -> Prop) (x : real) (b : real) : (term42 s x b) = (term43 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5302080 (s : real -> Prop) (x : real) (b : real) : (term13 s x b) = (term44 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5302081 (P : real -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5302082 (s : real -> Prop) (b : real) : (term47 s b) = (term48 s b).
Proof. exact (@lem5302081 (term14 s b)). Qed.
Lemma lem5302083 (s : real -> Prop) (x : real) (b : real) : (term49 s b x) = (term13 s x b).
Proof. exact (eq_refl (term49 s b x)). Qed.
Lemma lem5302084 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5302085 (s : real -> Prop) (x : real) (b : real) : (term50 s b x) = (term42 s x b).
Proof. exact (MK_COMB (@lem5302084) (@lem5302083 s x b)). Qed.
Lemma lem5302086 (s : real -> Prop) (x : real) (b : real) : (term50 s b x) = (term43 s x b).
Proof. exact (TRANS (@lem5302085 s x b) (@lem5302075 s x b)). Qed.
Lemma lem5302087 (s : real -> Prop) (b : real) : (term51 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5302086 s x b)). Qed.
Lemma lem5302088 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302089 (s : real -> Prop) (b : real) : (term48 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5302088) (@lem5302087 s b)). Qed.
Lemma lem5302090 (s : real -> Prop) (b : real) : (term47 s b) = (term53 s b).
Proof. exact (TRANS (@lem5302082 s b) (@lem5302089 s b)). Qed.
Lemma lem5302091 (s : real -> Prop) (b : real) : (term14 s b) = (term54 s b).
Proof. exact (fun_ext (fun x : real => @lem5302080 s x b)). Qed.
Lemma lem5302092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302093 (s : real -> Prop) (b : real) : (term15 s b) = (term55 s b).
Proof. exact (MK_COMB (@lem5302092) (@lem5302091 s b)). Qed.
Lemma lem5302094 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5302095 (s : real -> Prop) : (term56 s) = (term57 s).
Proof. exact (@lem5302094 (term16 s)). Qed.
Lemma lem5302096 (s : real -> Prop) (b : real) : (term58 s b) = (term15 s b).
Proof. exact (eq_refl (term58 s b)). Qed.
Lemma lem5302097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5302098 (s : real -> Prop) (b : real) : (term59 s b) = (term47 s b).
Proof. exact (MK_COMB (@lem5302097) (@lem5302096 s b)). Qed.
Lemma lem5302099 (s : real -> Prop) (b : real) : (term59 s b) = (term53 s b).
Proof. exact (TRANS (@lem5302098 s b) (@lem5302090 s b)). Qed.
Lemma lem5302100 (s : real -> Prop) : (term60 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5302099 s b)). Qed.
Lemma lem5302101 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302102 (s : real -> Prop) : (term57 s) = (term62 s).
Proof. exact (MK_COMB (@lem5302101) (@lem5302100 s)). Qed.
Lemma lem5302103 (s : real -> Prop) : (term56 s) = (term62 s).
Proof. exact (TRANS (@lem5302095 s) (@lem5302102 s)). Qed.
Lemma lem5302104 (s : real -> Prop) : (term16 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5302093 s b)). Qed.
Lemma lem5302105 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302106 (s : real -> Prop) : (term17 s) = (term64 s).
Proof. exact (MK_COMB (@lem5302105) (@lem5302104 s)). Qed.
Lemma lem5302107 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5302108 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5302109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302110 (s : real -> Prop) : (term293 s) = (term294 s).
Proof. exact (MK_COMB (@lem5302109) (@lem5302103 s)). Qed.
Lemma lem5302111 (s : real -> Prop) (l : real) : (term295 s l) = (term296 s l).
Proof. exact (MK_COMB (@lem5302110 s) (@lem5302107 s l)). Qed.
Lemma lem5302112 (s : real -> Prop) (l : real) : (term297 s l) = (term295 s l).
Proof. exact (@lem17045 (term17 s) ((sup s) = l)). Qed.
Lemma lem5302113 (s : real -> Prop) (l : real) : (term297 s l) = (term296 s l).
Proof. exact (TRANS (@lem5302112 s l) (@lem5302111 s l)). Qed.
Lemma lem5302114 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302115 (s : real -> Prop) : (term18 s) = (term298 s).
Proof. exact (MK_COMB (@lem5302114) (@lem5302106 s)). Qed.
Lemma lem5302116 (s : real -> Prop) (l : real) : (term19 s l) = (term299 s l).
Proof. exact (MK_COMB (@lem5302115 s) (@lem5302108 s l)). Qed.
Lemma lem5302117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302118 (s : real -> Prop) : (term65 s) = (term66 s).
Proof. exact (MK_COMB (@lem5302117) (@lem5302066 s)). Qed.
Lemma lem5302119 (s : real -> Prop) (l : real) : (term300 s l) = (term301 s l).
Proof. exact (MK_COMB (@lem5302118 s) (@lem5302113 s l)). Qed.
Lemma lem5302120 (s : real -> Prop) (l : real) : (term302 s l) = (term300 s l).
Proof. exact (@lem17045 (term70 s) (term19 s l)). Qed.
Lemma lem5302121 (s : real -> Prop) (l : real) : (term302 s l) = (term301 s l).
Proof. exact (TRANS (@lem5302120 s l) (@lem5302119 s l)). Qed.
Lemma lem5302123 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5302124 (s : real -> Prop) (l : real) : (term21 s l) = (term303 s l).
Proof. exact (MK_COMB (@lem5302123 s) (@lem5302116 s l)). Qed.
Lemma lem5302126 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5302127 (s : real -> Prop) (l : real) : (term305 s l) = (term306 s l).
Proof. exact (MK_COMB (@lem5302126 s l) (@lem5302124 s l)). Qed.
Lemma lem5302129 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5302130 (s : real -> Prop) (l : real) : (term308 s l) = (term309 s l).
Proof. exact (MK_COMB (@lem5302129 s l) (@lem5302121 s l)). Qed.
Lemma lem5302131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302132 (s : real -> Prop) (l : real) : (term310 s l) = (term311 s l).
Proof. exact (MK_COMB (@lem5302131) (@lem5302130 s l)). Qed.
Lemma lem5302133 (s : real -> Prop) (l : real) : (term312 s l) = (term313 s l).
Proof. exact (MK_COMB (@lem5302132 s l) (@lem5302127 s l)). Qed.
Lemma lem5302134 (s : real -> Prop) (l : real) : ((has_sup s l) = (term21 s l)) = (term312 s l).
Proof. exact (@lem17784 (has_sup s l) (term21 s l)). Qed.
Lemma lem5302135 (s : real -> Prop) (l : real) : ((has_sup s l) = (term21 s l)) = (term313 s l).
Proof. exact (TRANS (@lem5302134 s l) (@lem5302133 s l)). Qed.
Lemma lem5302136 (s : real -> Prop) : (term23 s) = (term314 s).
Proof. exact (fun_ext (fun l : real => @lem5302135 s l)). Qed.
Lemma lem5302137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302138 (s : real -> Prop) : (term24 s) = (term315 s).
Proof. exact (MK_COMB (@lem5302137) (@lem5302136 s)). Qed.
Lemma lem5302139 : term25 = term316.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302138 s)). Qed.
Lemma lem5302140 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302141 : term10 = term317.
Proof. exact (MK_COMB (@lem5302140) (@lem5302139)). Qed.
Lemma lem5302147 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5302148 (P : real -> Prop) (Q : real -> Prop) : (term320 P Q) = (term321 P Q).
Proof. exact (@lem5302147 real P Q). Qed.
Lemma lem5302149 (s : real -> Prop) : (term322 s) = (term323 s).
Proof. exact (@lem5302148 (term324 s) (term325 s)). Qed.
Lemma lem5302150 (s : real -> Prop) (l : real) : (term326 s l) = (term309 s l).
Proof. exact (eq_refl (term326 s l)). Qed.
Lemma lem5302151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302152 (s : real -> Prop) (l : real) : (term327 s l) = (term311 s l).
Proof. exact (MK_COMB (@lem5302151) (@lem5302150 s l)). Qed.
Lemma lem5302153 (s : real -> Prop) (l : real) : (term328 s l) = (term306 s l).
Proof. exact (eq_refl (term328 s l)). Qed.
Lemma lem5302154 (s : real -> Prop) (l : real) : (term329 s l) = (term313 s l).
Proof. exact (MK_COMB (@lem5302152 s l) (@lem5302153 s l)). Qed.
Lemma lem5302155 (s : real -> Prop) : (term330 s) = (term314 s).
Proof. exact (fun_ext (fun l : real => @lem5302154 s l)). Qed.
Lemma lem5302156 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302157 (s : real -> Prop) : (term322 s) = (term315 s).
Proof. exact (MK_COMB (@lem5302156) (@lem5302155 s)). Qed.
Lemma lem5302158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302159 (s : real -> Prop) : (term331 s) = (term332 s).
Proof. exact (MK_COMB (@lem5302158) (@lem5302157 s)). Qed.
Lemma lem5302160 (s : real -> Prop) (l : real) : (term326 s l) = (term309 s l).
Proof. exact (eq_refl (term326 s l)). Qed.
Lemma lem5302161 (s : real -> Prop) : (term333 s) = (term324 s).
Proof. exact (fun_ext (fun l : real => @lem5302160 s l)). Qed.
Lemma lem5302162 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302163 (s : real -> Prop) : (term334 s) = (term335 s).
Proof. exact (MK_COMB (@lem5302162) (@lem5302161 s)). Qed.
Lemma lem5302164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302165 (s : real -> Prop) : (term336 s) = (term337 s).
Proof. exact (MK_COMB (@lem5302164) (@lem5302163 s)). Qed.
Lemma lem5302166 (s : real -> Prop) (l : real) : (term328 s l) = (term306 s l).
Proof. exact (eq_refl (term328 s l)). Qed.
Lemma lem5302167 (s : real -> Prop) : (term338 s) = (term325 s).
Proof. exact (fun_ext (fun l : real => @lem5302166 s l)). Qed.
Lemma lem5302168 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302169 (s : real -> Prop) : (term339 s) = (term340 s).
Proof. exact (MK_COMB (@lem5302168) (@lem5302167 s)). Qed.
Lemma lem5302170 (s : real -> Prop) : (term323 s) = (term341 s).
Proof. exact (MK_COMB (@lem5302165 s) (@lem5302169 s)). Qed.
Lemma lem5302171 (s : real -> Prop) : ((term322 s) = (term323 s)) = ((term315 s) = (term341 s)).
Proof. exact (MK_COMB (@lem5302159 s) (@lem5302170 s)). Qed.
Lemma lem5302172 (s : real -> Prop) : (term315 s) = (term341 s).
Proof. exact (EQ_MP (@lem5302171 s) (@lem5302149 s)). Qed.
Lemma lem5302373 : term316 = term342.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302172 s)). Qed.
Lemma lem5302374 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302375 : term317 = term343.
Proof. exact (MK_COMB (@lem5302374) (@lem5302373)). Qed.
Lemma lem5302377 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term318 A P Q) = (term319 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5302378 (P : type1022) (Q : type1022) : (term344 P Q) = (term345 P Q).
Proof. exact (@lem5302377 (real -> Prop) P Q). Qed.
Lemma lem5302379 : term346 = term347.
Proof. exact (@lem5302378 term348 term349). Qed.
Lemma lem5302380 (s : real -> Prop) : (term350 s) = (term335 s).
Proof. exact (eq_refl (term350 s)). Qed.
Lemma lem5302381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302382 (s : real -> Prop) : (term351 s) = (term337 s).
Proof. exact (MK_COMB (@lem5302381) (@lem5302380 s)). Qed.
Lemma lem5302383 (s : real -> Prop) : (term352 s) = (term340 s).
Proof. exact (eq_refl (term352 s)). Qed.
Lemma lem5302384 (s : real -> Prop) : (term353 s) = (term341 s).
Proof. exact (MK_COMB (@lem5302382 s) (@lem5302383 s)). Qed.
Lemma lem5302385 : term354 = term342.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302384 s)). Qed.
Lemma lem5302386 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302387 : term346 = term343.
Proof. exact (MK_COMB (@lem5302386) (@lem5302385)). Qed.
Lemma lem5302388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302389 : term355 = term356.
Proof. exact (MK_COMB (@lem5302388) (@lem5302387)). Qed.
Lemma lem5302390 (s : real -> Prop) : (term350 s) = (term335 s).
Proof. exact (eq_refl (term350 s)). Qed.
Lemma lem5302391 : term357 = term348.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302390 s)). Qed.
Lemma lem5302392 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302393 : term358 = term359.
Proof. exact (MK_COMB (@lem5302392) (@lem5302391)). Qed.
Lemma lem5302394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302395 : term360 = term361.
Proof. exact (MK_COMB (@lem5302394) (@lem5302393)). Qed.
Lemma lem5302396 (s : real -> Prop) : (term352 s) = (term340 s).
Proof. exact (eq_refl (term352 s)). Qed.
Lemma lem5302397 : term362 = term349.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302396 s)). Qed.
Lemma lem5302398 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302399 : term363 = term364.
Proof. exact (MK_COMB (@lem5302398) (@lem5302397)). Qed.
Lemma lem5302400 : term347 = term365.
Proof. exact (MK_COMB (@lem5302395) (@lem5302399)). Qed.
Lemma lem5302401 : (term346 = term347) = (term343 = term365).
Proof. exact (MK_COMB (@lem5302389) (@lem5302400)). Qed.
Lemma lem5302402 : term343 = term365.
Proof. exact (EQ_MP (@lem5302401) (@lem5302379)). Qed.
Lemma lem5302611 : term317 = term365.
Proof. exact (TRANS (@lem5302375) (@lem5302402)). Qed.
Lemma lem5302613 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5302614 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (@lem5302613 real real P). Qed.
Lemma lem5302615 (s : real -> Prop) : (term120 s) = (term121 s).
Proof. exact (@lem5302614 (term122 s)). Qed.
Lemma lem5302616 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5302617 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5302618 (s : real -> Prop) (b : real) (x : real) : (term124 s b x) = (term125 s b x).
Proof. exact (MK_COMB (@lem5302616 s b) (@lem5302617 x)). Qed.
Lemma lem5302619 (s : real -> Prop) (x : real) (b : real) : (term125 s b x) = (term43 s x b).
Proof. exact (eq_refl (term125 s b x)). Qed.
Lemma lem5302620 (s : real -> Prop) (x : real) (b : real) : (term124 s b x) = (term43 s x b).
Proof. exact (TRANS (@lem5302618 s b x) (@lem5302619 s x b)). Qed.
Lemma lem5302621 (s : real -> Prop) (b : real) : (term126 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5302620 s x b)). Qed.
Lemma lem5302622 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302623 (s : real -> Prop) (b : real) : (term127 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5302622) (@lem5302621 s b)). Qed.
Lemma lem5302624 (s : real -> Prop) : (term128 s) = (term61 s).
Proof. exact (fun_ext (fun b : real => @lem5302623 s b)). Qed.
Lemma lem5302625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302626 (s : real -> Prop) : (term120 s) = (term62 s).
Proof. exact (MK_COMB (@lem5302625) (@lem5302624 s)). Qed.
Lemma lem5302627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302628 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5302627) (@lem5302626 s)). Qed.
Lemma lem5302629 (s : real -> Prop) (b : real) : (term123 s b) = (term52 s b).
Proof. exact (eq_refl (term123 s b)). Qed.
Lemma lem5302630 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5302631 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term132 s x b).
Proof. exact (MK_COMB (@lem5302629 s b) (@lem5302630 x b)). Qed.
Lemma lem5302632 (s : real -> Prop) (x : real -> real) (b : real) : (term132 s x b) = (term133 s x b).
Proof. exact (eq_refl (term132 s x b)). Qed.
Lemma lem5302633 (s : real -> Prop) (x : real -> real) (b : real) : (term131 s x b) = (term133 s x b).
Proof. exact (TRANS (@lem5302631 s x b) (@lem5302632 s x b)). Qed.
Lemma lem5302634 (s : real -> Prop) (x : real -> real) : (term134 s x) = (term135 s x).
Proof. exact (fun_ext (fun b : real => @lem5302633 s x b)). Qed.
Lemma lem5302635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302636 (s : real -> Prop) (x : real -> real) : (term136 s x) = (term137 s x).
Proof. exact (MK_COMB (@lem5302635) (@lem5302634 s x)). Qed.
Lemma lem5302637 (s : real -> Prop) : (term138 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5302636 s x)). Qed.
Lemma lem5302638 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302639 (s : real -> Prop) : (term121 s) = (term140 s).
Proof. exact (MK_COMB (@lem5302638) (@lem5302637 s)). Qed.
Lemma lem5302640 (s : real -> Prop) : ((term120 s) = (term121 s)) = ((term62 s) = (term140 s)).
Proof. exact (MK_COMB (@lem5302628 s) (@lem5302639 s)). Qed.
Lemma lem5302641 (s : real -> Prop) : (term62 s) = (term140 s).
Proof. exact (EQ_MP (@lem5302640 s) (@lem5302615 s)). Qed.
Lemma lem5302642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302643 (s : real -> Prop) : (term294 s) = (term366 s).
Proof. exact (MK_COMB (@lem5302642) (@lem5302641 s)). Qed.
Lemma lem5302644 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5302645 (s : real -> Prop) (l : real) : (term296 s l) = (term367 s l).
Proof. exact (MK_COMB (@lem5302643 s) (@lem5302644 s l)). Qed.
Lemma lem5302647 {A : Type'} (P : A -> Prop) (Q : Prop) : (term269 A P Q) = (term270 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5302648 (P : type1028) (Q : Prop) : (term271 P Q) = (term272 P Q).
Proof. exact (@lem5302647 (real -> real) P Q). Qed.
Lemma lem5302649 (s : real -> Prop) (l : real) : (term368 s l) = (term369 s l).
Proof. exact (@lem5302648 (term139 s) (term292 s l)). Qed.
Lemma lem5302650 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5302651 (s : real -> Prop) : (term149 s) = (term139 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5302650 s x)). Qed.
Lemma lem5302652 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302653 (s : real -> Prop) : (term150 s) = (term140 s).
Proof. exact (MK_COMB (@lem5302652) (@lem5302651 s)). Qed.
Lemma lem5302654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302655 (s : real -> Prop) : (term370 s) = (term366 s).
Proof. exact (MK_COMB (@lem5302654) (@lem5302653 s)). Qed.
Lemma lem5302656 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5302657 (s : real -> Prop) (l : real) : (term368 s l) = (term367 s l).
Proof. exact (MK_COMB (@lem5302655 s) (@lem5302656 s l)). Qed.
Lemma lem5302658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302659 (s : real -> Prop) (l : real) : (term371 s l) = (term372 s l).
Proof. exact (MK_COMB (@lem5302658) (@lem5302657 s l)). Qed.
Lemma lem5302660 (s : real -> Prop) (x : real -> real) : (term148 s x) = (term137 s x).
Proof. exact (eq_refl (term148 s x)). Qed.
Lemma lem5302661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5302662 (s : real -> Prop) (x : real -> real) : (term373 s x) = (term374 s x).
Proof. exact (MK_COMB (@lem5302661) (@lem5302660 s x)). Qed.
Lemma lem5302663 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5302664 (x : real -> real) (s : real -> Prop) (l : real) : (term375 x s l) = (term376 x s l).
Proof. exact (MK_COMB (@lem5302662 s x) (@lem5302663 s l)). Qed.
Lemma lem5302665 (s : real -> Prop) (l : real) : (term377 s l) = (term378 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302664 x s l)). Qed.
Lemma lem5302666 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302667 (s : real -> Prop) (l : real) : (term369 s l) = (term379 s l).
Proof. exact (MK_COMB (@lem5302666) (@lem5302665 s l)). Qed.
Lemma lem5302668 (s : real -> Prop) (l : real) : ((term368 s l) = (term369 s l)) = ((term367 s l) = (term379 s l)).
Proof. exact (MK_COMB (@lem5302659 s l) (@lem5302667 s l)). Qed.
Lemma lem5302669 (s : real -> Prop) (l : real) : (term367 s l) = (term379 s l).
Proof. exact (EQ_MP (@lem5302668 s l) (@lem5302649 s l)). Qed.
Lemma lem5302670 (s : real -> Prop) (l : real) : (term296 s l) = (term379 s l).
Proof. exact (TRANS (@lem5302645 s l) (@lem5302669 s l)). Qed.
Lemma lem5302671 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5302672 (s : real -> Prop) (l : real) : (term301 s l) = (term380 s l).
Proof. exact (MK_COMB (@lem5302671 s) (@lem5302670 s l)). Qed.
Lemma lem5302674 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5302675 (P : Prop) (Q : type1028) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5302674 (real -> real) P Q). Qed.
Lemma lem5302676 (s : real -> Prop) (l : real) : (term381 s l) = (term382 s l).
Proof. exact (@lem5302675 (s = (@EMPTY real)) (term378 s l)). Qed.
Lemma lem5302677 (x : real -> real) (s : real -> Prop) (l : real) : (term383 s l x) = (term376 x s l).
Proof. exact (eq_refl (term383 s l x)). Qed.
Lemma lem5302678 (s : real -> Prop) (l : real) : (term384 s l) = (term378 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302677 x s l)). Qed.
Lemma lem5302679 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302680 (s : real -> Prop) (l : real) : (term385 s l) = (term379 s l).
Proof. exact (MK_COMB (@lem5302679) (@lem5302678 s l)). Qed.
Lemma lem5302681 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5302682 (s : real -> Prop) (l : real) : (term381 s l) = (term380 s l).
Proof. exact (MK_COMB (@lem5302681 s) (@lem5302680 s l)). Qed.
Lemma lem5302683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302684 (s : real -> Prop) (l : real) : (term386 s l) = (term387 s l).
Proof. exact (MK_COMB (@lem5302683) (@lem5302682 s l)). Qed.
Lemma lem5302685 (x : real -> real) (s : real -> Prop) (l : real) : (term383 s l x) = (term376 x s l).
Proof. exact (eq_refl (term383 s l x)). Qed.
Lemma lem5302686 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5302687 (x : real -> real) (s : real -> Prop) (l : real) : (term388 s l x) = (term389 x s l).
Proof. exact (MK_COMB (@lem5302686 s) (@lem5302685 x s l)). Qed.
Lemma lem5302688 (s : real -> Prop) (l : real) : (term390 s l) = (term391 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302687 x s l)). Qed.
Lemma lem5302689 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302690 (s : real -> Prop) (l : real) : (term382 s l) = (term392 s l).
Proof. exact (MK_COMB (@lem5302689) (@lem5302688 s l)). Qed.
Lemma lem5302691 (s : real -> Prop) (l : real) : ((term381 s l) = (term382 s l)) = ((term380 s l) = (term392 s l)).
Proof. exact (MK_COMB (@lem5302684 s l) (@lem5302690 s l)). Qed.
Lemma lem5302692 (s : real -> Prop) (l : real) : (term380 s l) = (term392 s l).
Proof. exact (EQ_MP (@lem5302691 s l) (@lem5302676 s l)). Qed.
Lemma lem5302693 (s : real -> Prop) (l : real) : (term301 s l) = (term392 s l).
Proof. exact (TRANS (@lem5302672 s l) (@lem5302692 s l)). Qed.
Lemma lem5302694 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5302695 (s : real -> Prop) (l : real) : (term309 s l) = (term393 s l).
Proof. exact (MK_COMB (@lem5302694 s l) (@lem5302693 s l)). Qed.
Lemma lem5302697 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5302698 (P : Prop) (Q : type1028) : (term144 P Q) = (term145 P Q).
Proof. exact (@lem5302697 (real -> real) P Q). Qed.
Lemma lem5302699 (s : real -> Prop) (l : real) : (term394 s l) = (term395 s l).
Proof. exact (@lem5302698 (has_sup s l) (term391 s l)). Qed.
Lemma lem5302700 (x : real -> real) (s : real -> Prop) (l : real) : (term396 s l x) = (term389 x s l).
Proof. exact (eq_refl (term396 s l x)). Qed.
Lemma lem5302701 (s : real -> Prop) (l : real) : (term397 s l) = (term391 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302700 x s l)). Qed.
Lemma lem5302702 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302703 (s : real -> Prop) (l : real) : (term398 s l) = (term392 s l).
Proof. exact (MK_COMB (@lem5302702) (@lem5302701 s l)). Qed.
Lemma lem5302704 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5302705 (s : real -> Prop) (l : real) : (term394 s l) = (term393 s l).
Proof. exact (MK_COMB (@lem5302704 s l) (@lem5302703 s l)). Qed.
Lemma lem5302706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302707 (s : real -> Prop) (l : real) : (term399 s l) = (term400 s l).
Proof. exact (MK_COMB (@lem5302706) (@lem5302705 s l)). Qed.
Lemma lem5302708 (x : real -> real) (s : real -> Prop) (l : real) : (term396 s l x) = (term389 x s l).
Proof. exact (eq_refl (term396 s l x)). Qed.
Lemma lem5302709 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5302710 (x : real -> real) (s : real -> Prop) (l : real) : (term401 s l x) = (term402 x s l).
Proof. exact (MK_COMB (@lem5302709 s l) (@lem5302708 x s l)). Qed.
Lemma lem5302711 (s : real -> Prop) (l : real) : (term403 s l) = (term404 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302710 x s l)). Qed.
Lemma lem5302712 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302713 (s : real -> Prop) (l : real) : (term395 s l) = (term405 s l).
Proof. exact (MK_COMB (@lem5302712) (@lem5302711 s l)). Qed.
Lemma lem5302714 (s : real -> Prop) (l : real) : ((term394 s l) = (term395 s l)) = ((term393 s l) = (term405 s l)).
Proof. exact (MK_COMB (@lem5302707 s l) (@lem5302713 s l)). Qed.
Lemma lem5302715 (s : real -> Prop) (l : real) : (term393 s l) = (term405 s l).
Proof. exact (EQ_MP (@lem5302714 s l) (@lem5302699 s l)). Qed.
Lemma lem5302716 (s : real -> Prop) (l : real) : (term309 s l) = (term405 s l).
Proof. exact (TRANS (@lem5302695 s l) (@lem5302715 s l)). Qed.
Lemma lem5302717 (s : real -> Prop) : (term324 s) = (term406 s).
Proof. exact (fun_ext (fun l : real => @lem5302716 s l)). Qed.
Lemma lem5302718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302719 (s : real -> Prop) : (term335 s) = (term407 s).
Proof. exact (MK_COMB (@lem5302718) (@lem5302717 s)). Qed.
Lemma lem5302721 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5302722 (P : type1618) : (term408 P) = (term409 P).
Proof. exact (@lem5302721 real (real -> real) P). Qed.
Lemma lem5302723 (s : real -> Prop) : (term410 s) = (term411 s).
Proof. exact (@lem5302722 (term412 s)). Qed.
Lemma lem5302724 (s : real -> Prop) (l : real) : (term413 s l) = (term404 s l).
Proof. exact (eq_refl (term413 s l)). Qed.
Lemma lem5302725 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5302726 (s : real -> Prop) (l : real) (x : real -> real) : (term414 s l x) = (term415 s l x).
Proof. exact (MK_COMB (@lem5302724 s l) (@lem5302725 x)). Qed.
Lemma lem5302727 (x : real -> real) (s : real -> Prop) (l : real) : (term415 s l x) = (term402 x s l).
Proof. exact (eq_refl (term415 s l x)). Qed.
Lemma lem5302728 (x : real -> real) (s : real -> Prop) (l : real) : (term414 s l x) = (term402 x s l).
Proof. exact (TRANS (@lem5302726 s l x) (@lem5302727 x s l)). Qed.
Lemma lem5302729 (s : real -> Prop) (l : real) : (term416 s l) = (term404 s l).
Proof. exact (fun_ext (fun x : real -> real => @lem5302728 x s l)). Qed.
Lemma lem5302730 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302731 (s : real -> Prop) (l : real) : (term417 s l) = (term405 s l).
Proof. exact (MK_COMB (@lem5302730) (@lem5302729 s l)). Qed.
Lemma lem5302732 (s : real -> Prop) : (term418 s) = (term406 s).
Proof. exact (fun_ext (fun l : real => @lem5302731 s l)). Qed.
Lemma lem5302733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302734 (s : real -> Prop) : (term410 s) = (term407 s).
Proof. exact (MK_COMB (@lem5302733) (@lem5302732 s)). Qed.
Lemma lem5302735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302736 (s : real -> Prop) : (term419 s) = (term420 s).
Proof. exact (MK_COMB (@lem5302735) (@lem5302734 s)). Qed.
Lemma lem5302737 (s : real -> Prop) (l : real) : (term413 s l) = (term404 s l).
Proof. exact (eq_refl (term413 s l)). Qed.
Lemma lem5302738 (x : type1627) (l : real) : (x l) = (x l).
Proof. exact (eq_refl (x l)). Qed.
Lemma lem5302739 (s : real -> Prop) (x : type1627) (l : real) : (term421 s x l) = (term422 s x l).
Proof. exact (MK_COMB (@lem5302737 s l) (@lem5302738 x l)). Qed.
Lemma lem5302740 (x : type1627) (s : real -> Prop) (l : real) : (term422 s x l) = (term423 x s l).
Proof. exact (eq_refl (term422 s x l)). Qed.
Lemma lem5302741 (x : type1627) (s : real -> Prop) (l : real) : (term421 s x l) = (term423 x s l).
Proof. exact (TRANS (@lem5302739 s x l) (@lem5302740 x s l)). Qed.
Lemma lem5302742 (x : type1627) (s : real -> Prop) : (term424 s x) = (term425 x s).
Proof. exact (fun_ext (fun l : real => @lem5302741 x s l)). Qed.
Lemma lem5302743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302744 (x : type1627) (s : real -> Prop) : (term426 s x) = (term427 x s).
Proof. exact (MK_COMB (@lem5302743) (@lem5302742 x s)). Qed.
Lemma lem5302745 (s : real -> Prop) : (term428 s) = (term429 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5302744 x s)). Qed.
Lemma lem5302746 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5302747 (s : real -> Prop) : (term411 s) = (term430 s).
Proof. exact (MK_COMB (@lem5302746) (@lem5302745 s)). Qed.
Lemma lem5302748 (s : real -> Prop) : ((term410 s) = (term411 s)) = ((term407 s) = (term430 s)).
Proof. exact (MK_COMB (@lem5302736 s) (@lem5302747 s)). Qed.
Lemma lem5302749 (s : real -> Prop) : (term407 s) = (term430 s).
Proof. exact (EQ_MP (@lem5302748 s) (@lem5302723 s)). Qed.
Lemma lem5302750 (s : real -> Prop) : (term335 s) = (term430 s).
Proof. exact (TRANS (@lem5302719 s) (@lem5302749 s)). Qed.
Lemma lem5302751 : term348 = term431.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302750 s)). Qed.
Lemma lem5302752 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302753 : term359 = term432.
Proof. exact (MK_COMB (@lem5302752) (@lem5302751)). Qed.
Lemma lem5302755 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5302756 (P : type1016) : (term433 P) = (term434 P).
Proof. exact (@lem5302755 (real -> Prop) type1627 P). Qed.
Lemma lem5302757 : term435 = term436.
Proof. exact (@lem5302756 term437). Qed.
Lemma lem5302758 (s : real -> Prop) : (term438 s) = (term429 s).
Proof. exact (eq_refl (term438 s)). Qed.
Lemma lem5302759 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5302760 (s : real -> Prop) (x : type1627) : (term439 s x) = (term440 s x).
Proof. exact (MK_COMB (@lem5302758 s) (@lem5302759 x)). Qed.
Lemma lem5302761 (x : type1627) (s : real -> Prop) : (term440 s x) = (term427 x s).
Proof. exact (eq_refl (term440 s x)). Qed.
Lemma lem5302762 (x : type1627) (s : real -> Prop) : (term439 s x) = (term427 x s).
Proof. exact (TRANS (@lem5302760 s x) (@lem5302761 x s)). Qed.
Lemma lem5302763 (s : real -> Prop) : (term441 s) = (term429 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5302762 x s)). Qed.
Lemma lem5302764 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5302765 (s : real -> Prop) : (term442 s) = (term430 s).
Proof. exact (MK_COMB (@lem5302764) (@lem5302763 s)). Qed.
Lemma lem5302766 : term443 = term431.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302765 s)). Qed.
Lemma lem5302767 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302768 : term435 = term432.
Proof. exact (MK_COMB (@lem5302767) (@lem5302766)). Qed.
Lemma lem5302769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302770 : term444 = term445.
Proof. exact (MK_COMB (@lem5302769) (@lem5302768)). Qed.
Lemma lem5302771 (s : real -> Prop) : (term438 s) = (term429 s).
Proof. exact (eq_refl (term438 s)). Qed.
Lemma lem5302772 (x : type1019) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5302773 (x : type1019) (s : real -> Prop) : (term446 x s) = (term447 x s).
Proof. exact (MK_COMB (@lem5302771 s) (@lem5302772 x s)). Qed.
Lemma lem5302774 (x : type1019) (s : real -> Prop) : (term447 x s) = (term448 x s).
Proof. exact (eq_refl (term447 x s)). Qed.
Lemma lem5302775 (x : type1019) (s : real -> Prop) : (term446 x s) = (term448 x s).
Proof. exact (TRANS (@lem5302773 x s) (@lem5302774 x s)). Qed.
Lemma lem5302776 (x : type1019) : (term449 x) = (term450 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302775 x s)). Qed.
Lemma lem5302777 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302778 (x : type1019) : (term451 x) = (term452 x).
Proof. exact (MK_COMB (@lem5302777) (@lem5302776 x)). Qed.
Lemma lem5302779 : term453 = term454.
Proof. exact (fun_ext (fun x : type1019 => @lem5302778 x)). Qed.
Lemma lem5302780 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5302781 : term436 = term455.
Proof. exact (MK_COMB (@lem5302780) (@lem5302779)). Qed.
Lemma lem5302782 : (term435 = term436) = (term432 = term455).
Proof. exact (MK_COMB (@lem5302770) (@lem5302781)). Qed.
Lemma lem5302783 : term432 = term455.
Proof. exact (EQ_MP (@lem5302782) (@lem5302757)). Qed.
Lemma lem5302784 : term359 = term455.
Proof. exact (TRANS (@lem5302753) (@lem5302783)). Qed.
Lemma lem5302785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302786 : term361 = term456.
Proof. exact (MK_COMB (@lem5302785) (@lem5302784)). Qed.
Lemma lem5302788 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5302789 (P : real -> Prop) (Q : Prop) : (term161 P Q) = (term162 P Q).
Proof. exact (@lem5302788 real P Q). Qed.
Lemma lem5302790 (s : real -> Prop) (l : real) : (term457 s l) = (term458 s l).
Proof. exact (@lem5302789 (term63 s) ((sup s) = l)). Qed.
Lemma lem5302791 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5302792 (s : real -> Prop) : (term203 s) = (term63 s).
Proof. exact (fun_ext (fun b : real => @lem5302791 s b)). Qed.
Lemma lem5302793 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302794 (s : real -> Prop) : (term204 s) = (term64 s).
Proof. exact (MK_COMB (@lem5302793) (@lem5302792 s)). Qed.
Lemma lem5302795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302796 (s : real -> Prop) : (term459 s) = (term298 s).
Proof. exact (MK_COMB (@lem5302795) (@lem5302794 s)). Qed.
Lemma lem5302797 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5302798 (s : real -> Prop) (l : real) : (term457 s l) = (term299 s l).
Proof. exact (MK_COMB (@lem5302796 s) (@lem5302797 s l)). Qed.
Lemma lem5302799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302800 (s : real -> Prop) (l : real) : (term460 s l) = (term461 s l).
Proof. exact (MK_COMB (@lem5302799) (@lem5302798 s l)). Qed.
Lemma lem5302801 (s : real -> Prop) (b : real) : (term202 s b) = (term55 s b).
Proof. exact (eq_refl (term202 s b)). Qed.
Lemma lem5302802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302803 (s : real -> Prop) (b : real) : (term462 s b) = (term463 s b).
Proof. exact (MK_COMB (@lem5302802) (@lem5302801 s b)). Qed.
Lemma lem5302804 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5302805 (b : real) (s : real -> Prop) (l : real) : (term464 b s l) = (term465 b s l).
Proof. exact (MK_COMB (@lem5302803 s b) (@lem5302804 s l)). Qed.
Lemma lem5302806 (s : real -> Prop) (l : real) : (term466 s l) = (term467 s l).
Proof. exact (fun_ext (fun b : real => @lem5302805 b s l)). Qed.
Lemma lem5302807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302808 (s : real -> Prop) (l : real) : (term458 s l) = (term468 s l).
Proof. exact (MK_COMB (@lem5302807) (@lem5302806 s l)). Qed.
Lemma lem5302809 (s : real -> Prop) (l : real) : ((term457 s l) = (term458 s l)) = ((term299 s l) = (term468 s l)).
Proof. exact (MK_COMB (@lem5302800 s l) (@lem5302808 s l)). Qed.
Lemma lem5302810 (s : real -> Prop) (l : real) : (term299 s l) = (term468 s l).
Proof. exact (EQ_MP (@lem5302809 s l) (@lem5302790 s l)). Qed.
Lemma lem5302811 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5302812 (s : real -> Prop) (l : real) : (term303 s l) = (term469 s l).
Proof. exact (MK_COMB (@lem5302811 s) (@lem5302810 s l)). Qed.
Lemma lem5302814 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5302815 (P : Prop) (Q : real -> Prop) : (term198 P Q) = (term199 P Q).
Proof. exact (@lem5302814 real P Q). Qed.
Lemma lem5302816 (s : real -> Prop) (l : real) : (term470 s l) = (term471 s l).
Proof. exact (@lem5302815 (term70 s) (term467 s l)). Qed.
Lemma lem5302817 (b : real) (s : real -> Prop) (l : real) : (term472 s l b) = (term465 b s l).
Proof. exact (eq_refl (term472 s l b)). Qed.
Lemma lem5302818 (s : real -> Prop) (l : real) : (term473 s l) = (term467 s l).
Proof. exact (fun_ext (fun b : real => @lem5302817 b s l)). Qed.
Lemma lem5302819 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302820 (s : real -> Prop) (l : real) : (term474 s l) = (term468 s l).
Proof. exact (MK_COMB (@lem5302819) (@lem5302818 s l)). Qed.
Lemma lem5302821 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5302822 (s : real -> Prop) (l : real) : (term470 s l) = (term469 s l).
Proof. exact (MK_COMB (@lem5302821 s) (@lem5302820 s l)). Qed.
Lemma lem5302823 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302824 (s : real -> Prop) (l : real) : (term475 s l) = (term476 s l).
Proof. exact (MK_COMB (@lem5302823) (@lem5302822 s l)). Qed.
Lemma lem5302825 (b : real) (s : real -> Prop) (l : real) : (term472 s l b) = (term465 b s l).
Proof. exact (eq_refl (term472 s l b)). Qed.
Lemma lem5302826 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5302827 (b : real) (s : real -> Prop) (l : real) : (term477 s l b) = (term478 b s l).
Proof. exact (MK_COMB (@lem5302826 s) (@lem5302825 b s l)). Qed.
Lemma lem5302828 (s : real -> Prop) (l : real) : (term479 s l) = (term480 s l).
Proof. exact (fun_ext (fun b : real => @lem5302827 b s l)). Qed.
Lemma lem5302829 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302830 (s : real -> Prop) (l : real) : (term471 s l) = (term481 s l).
Proof. exact (MK_COMB (@lem5302829) (@lem5302828 s l)). Qed.
Lemma lem5302831 (s : real -> Prop) (l : real) : ((term470 s l) = (term471 s l)) = ((term469 s l) = (term481 s l)).
Proof. exact (MK_COMB (@lem5302824 s l) (@lem5302830 s l)). Qed.
Lemma lem5302832 (s : real -> Prop) (l : real) : (term469 s l) = (term481 s l).
Proof. exact (EQ_MP (@lem5302831 s l) (@lem5302816 s l)). Qed.
Lemma lem5302833 (s : real -> Prop) (l : real) : (term303 s l) = (term481 s l).
Proof. exact (TRANS (@lem5302812 s l) (@lem5302832 s l)). Qed.
Lemma lem5302834 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5302835 (s : real -> Prop) (l : real) : (term306 s l) = (term482 s l).
Proof. exact (MK_COMB (@lem5302834 s l) (@lem5302833 s l)). Qed.
Lemma lem5302837 {A : Type'} (P : Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5302838 (P : Prop) (Q : real -> Prop) : (term483 P Q) = (term484 P Q).
Proof. exact (@lem5302837 real P Q). Qed.
Lemma lem5302839 (s : real -> Prop) (l : real) : (term485 s l) = (term486 s l).
Proof. exact (@lem5302838 (term37 s l) (term480 s l)). Qed.
Lemma lem5302840 (b : real) (s : real -> Prop) (l : real) : (term487 s l b) = (term478 b s l).
Proof. exact (eq_refl (term487 s l b)). Qed.
Lemma lem5302841 (s : real -> Prop) (l : real) : (term488 s l) = (term480 s l).
Proof. exact (fun_ext (fun b : real => @lem5302840 b s l)). Qed.
Lemma lem5302842 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302843 (s : real -> Prop) (l : real) : (term489 s l) = (term481 s l).
Proof. exact (MK_COMB (@lem5302842) (@lem5302841 s l)). Qed.
Lemma lem5302844 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5302845 (s : real -> Prop) (l : real) : (term485 s l) = (term482 s l).
Proof. exact (MK_COMB (@lem5302844 s l) (@lem5302843 s l)). Qed.
Lemma lem5302846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302847 (s : real -> Prop) (l : real) : (term490 s l) = (term491 s l).
Proof. exact (MK_COMB (@lem5302846) (@lem5302845 s l)). Qed.
Lemma lem5302848 (b : real) (s : real -> Prop) (l : real) : (term487 s l b) = (term478 b s l).
Proof. exact (eq_refl (term487 s l b)). Qed.
Lemma lem5302849 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5302850 (b : real) (s : real -> Prop) (l : real) : (term492 s l b) = (term493 b s l).
Proof. exact (MK_COMB (@lem5302849 s l) (@lem5302848 b s l)). Qed.
Lemma lem5302851 (s : real -> Prop) (l : real) : (term494 s l) = (term495 s l).
Proof. exact (fun_ext (fun b : real => @lem5302850 b s l)). Qed.
Lemma lem5302852 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302853 (s : real -> Prop) (l : real) : (term486 s l) = (term496 s l).
Proof. exact (MK_COMB (@lem5302852) (@lem5302851 s l)). Qed.
Lemma lem5302854 (s : real -> Prop) (l : real) : ((term485 s l) = (term486 s l)) = ((term482 s l) = (term496 s l)).
Proof. exact (MK_COMB (@lem5302847 s l) (@lem5302853 s l)). Qed.
Lemma lem5302855 (s : real -> Prop) (l : real) : (term482 s l) = (term496 s l).
Proof. exact (EQ_MP (@lem5302854 s l) (@lem5302839 s l)). Qed.
Lemma lem5302856 (s : real -> Prop) (l : real) : (term306 s l) = (term496 s l).
Proof. exact (TRANS (@lem5302835 s l) (@lem5302855 s l)). Qed.
Lemma lem5302857 (s : real -> Prop) : (term325 s) = (term497 s).
Proof. exact (fun_ext (fun l : real => @lem5302856 s l)). Qed.
Lemma lem5302858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302859 (s : real -> Prop) : (term340 s) = (term498 s).
Proof. exact (MK_COMB (@lem5302858) (@lem5302857 s)). Qed.
Lemma lem5302861 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5302862 (P : type1626) : (term118 P) = (term119 P).
Proof. exact (@lem5302861 real real P). Qed.
Lemma lem5302863 (s : real -> Prop) : (term499 s) = (term500 s).
Proof. exact (@lem5302862 (term501 s)). Qed.
Lemma lem5302864 (s : real -> Prop) (l : real) : (term502 s l) = (term495 s l).
Proof. exact (eq_refl (term502 s l)). Qed.
Lemma lem5302865 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5302866 (s : real -> Prop) (l : real) (b : real) : (term503 s l b) = (term504 s l b).
Proof. exact (MK_COMB (@lem5302864 s l) (@lem5302865 b)). Qed.
Lemma lem5302867 (b : real) (s : real -> Prop) (l : real) : (term504 s l b) = (term493 b s l).
Proof. exact (eq_refl (term504 s l b)). Qed.
Lemma lem5302868 (b : real) (s : real -> Prop) (l : real) : (term503 s l b) = (term493 b s l).
Proof. exact (TRANS (@lem5302866 s l b) (@lem5302867 b s l)). Qed.
Lemma lem5302869 (s : real -> Prop) (l : real) : (term505 s l) = (term495 s l).
Proof. exact (fun_ext (fun b : real => @lem5302868 b s l)). Qed.
Lemma lem5302870 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5302871 (s : real -> Prop) (l : real) : (term506 s l) = (term496 s l).
Proof. exact (MK_COMB (@lem5302870) (@lem5302869 s l)). Qed.
Lemma lem5302872 (s : real -> Prop) : (term507 s) = (term497 s).
Proof. exact (fun_ext (fun l : real => @lem5302871 s l)). Qed.
Lemma lem5302873 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302874 (s : real -> Prop) : (term499 s) = (term498 s).
Proof. exact (MK_COMB (@lem5302873) (@lem5302872 s)). Qed.
Lemma lem5302875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302876 (s : real -> Prop) : (term508 s) = (term509 s).
Proof. exact (MK_COMB (@lem5302875) (@lem5302874 s)). Qed.
Lemma lem5302877 (s : real -> Prop) (l : real) : (term502 s l) = (term495 s l).
Proof. exact (eq_refl (term502 s l)). Qed.
Lemma lem5302878 (b : real -> real) (l : real) : (b l) = (b l).
Proof. exact (eq_refl (b l)). Qed.
Lemma lem5302879 (s : real -> Prop) (b : real -> real) (l : real) : (term510 s b l) = (term511 s b l).
Proof. exact (MK_COMB (@lem5302877 s l) (@lem5302878 b l)). Qed.
Lemma lem5302880 (b : real -> real) (s : real -> Prop) (l : real) : (term511 s b l) = (term512 b s l).
Proof. exact (eq_refl (term511 s b l)). Qed.
Lemma lem5302881 (b : real -> real) (s : real -> Prop) (l : real) : (term510 s b l) = (term512 b s l).
Proof. exact (TRANS (@lem5302879 s b l) (@lem5302880 b s l)). Qed.
Lemma lem5302882 (b : real -> real) (s : real -> Prop) : (term513 s b) = (term514 b s).
Proof. exact (fun_ext (fun l : real => @lem5302881 b s l)). Qed.
Lemma lem5302883 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5302884 (b : real -> real) (s : real -> Prop) : (term515 s b) = (term516 b s).
Proof. exact (MK_COMB (@lem5302883) (@lem5302882 b s)). Qed.
Lemma lem5302885 (s : real -> Prop) : (term517 s) = (term518 s).
Proof. exact (fun_ext (fun b : real -> real => @lem5302884 b s)). Qed.
Lemma lem5302886 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302887 (s : real -> Prop) : (term500 s) = (term519 s).
Proof. exact (MK_COMB (@lem5302886) (@lem5302885 s)). Qed.
Lemma lem5302888 (s : real -> Prop) : ((term499 s) = (term500 s)) = ((term498 s) = (term519 s)).
Proof. exact (MK_COMB (@lem5302876 s) (@lem5302887 s)). Qed.
Lemma lem5302889 (s : real -> Prop) : (term498 s) = (term519 s).
Proof. exact (EQ_MP (@lem5302888 s) (@lem5302863 s)). Qed.
Lemma lem5302890 (s : real -> Prop) : (term340 s) = (term519 s).
Proof. exact (TRANS (@lem5302859 s) (@lem5302889 s)). Qed.
Lemma lem5302891 : term349 = term520.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302890 s)). Qed.
Lemma lem5302892 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302893 : term364 = term521.
Proof. exact (MK_COMB (@lem5302892) (@lem5302891)). Qed.
Lemma lem5302895 {A B : Type'} (P : type1413 A B) : (term116 A B P) = (term117 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5302896 (P : type1017) : (term522 P) = (term523 P).
Proof. exact (@lem5302895 (real -> Prop) (real -> real) P). Qed.
Lemma lem5302897 : term524 = term525.
Proof. exact (@lem5302896 term526). Qed.
Lemma lem5302898 (s : real -> Prop) : (term527 s) = (term518 s).
Proof. exact (eq_refl (term527 s)). Qed.
Lemma lem5302899 (b : real -> real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem5302900 (s : real -> Prop) (b : real -> real) : (term528 s b) = (term529 s b).
Proof. exact (MK_COMB (@lem5302898 s) (@lem5302899 b)). Qed.
Lemma lem5302901 (b : real -> real) (s : real -> Prop) : (term529 s b) = (term516 b s).
Proof. exact (eq_refl (term529 s b)). Qed.
Lemma lem5302902 (b : real -> real) (s : real -> Prop) : (term528 s b) = (term516 b s).
Proof. exact (TRANS (@lem5302900 s b) (@lem5302901 b s)). Qed.
Lemma lem5302903 (s : real -> Prop) : (term530 s) = (term518 s).
Proof. exact (fun_ext (fun b : real -> real => @lem5302902 b s)). Qed.
Lemma lem5302904 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5302905 (s : real -> Prop) : (term531 s) = (term519 s).
Proof. exact (MK_COMB (@lem5302904) (@lem5302903 s)). Qed.
Lemma lem5302906 : term532 = term520.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302905 s)). Qed.
Lemma lem5302907 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302908 : term524 = term521.
Proof. exact (MK_COMB (@lem5302907) (@lem5302906)). Qed.
Lemma lem5302909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302910 : term533 = term534.
Proof. exact (MK_COMB (@lem5302909) (@lem5302908)). Qed.
Lemma lem5302911 (s : real -> Prop) : (term527 s) = (term518 s).
Proof. exact (eq_refl (term527 s)). Qed.
Lemma lem5302912 (b : type1021) (s : real -> Prop) : (b s) = (b s).
Proof. exact (eq_refl (b s)). Qed.
Lemma lem5302913 (b : type1021) (s : real -> Prop) : (term535 b s) = (term536 b s).
Proof. exact (MK_COMB (@lem5302911 s) (@lem5302912 b s)). Qed.
Lemma lem5302914 (b : type1021) (s : real -> Prop) : (term536 b s) = (term537 b s).
Proof. exact (eq_refl (term536 b s)). Qed.
Lemma lem5302915 (b : type1021) (s : real -> Prop) : (term535 b s) = (term537 b s).
Proof. exact (TRANS (@lem5302913 b s) (@lem5302914 b s)). Qed.
Lemma lem5302916 (b : type1021) : (term538 b) = (term539 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5302915 b s)). Qed.
Lemma lem5302917 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5302918 (b : type1021) : (term540 b) = (term541 b).
Proof. exact (MK_COMB (@lem5302917) (@lem5302916 b)). Qed.
Lemma lem5302919 : term542 = term543.
Proof. exact (fun_ext (fun b : type1021 => @lem5302918 b)). Qed.
Lemma lem5302920 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5302921 : term525 = term544.
Proof. exact (MK_COMB (@lem5302920) (@lem5302919)). Qed.
Lemma lem5302922 : (term524 = term525) = (term521 = term544).
Proof. exact (MK_COMB (@lem5302910) (@lem5302921)). Qed.
Lemma lem5302923 : term521 = term544.
Proof. exact (EQ_MP (@lem5302922) (@lem5302897)). Qed.
Lemma lem5302924 : term364 = term544.
Proof. exact (TRANS (@lem5302893) (@lem5302923)). Qed.
Lemma lem5302925 : term365 = term545.
Proof. exact (MK_COMB (@lem5302786) (@lem5302924)). Qed.
Lemma lem5302927 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5302928 (P : type255) (Q : Prop) : (term546 P Q) = (term547 P Q).
Proof. exact (@lem5302927 type1019 P Q). Qed.
Lemma lem5302929 : term548 = term549.
Proof. exact (@lem5302928 term454 term544). Qed.
Lemma lem5302930 (x : type1019) : (term550 x) = (term452 x).
Proof. exact (eq_refl (term550 x)). Qed.
Lemma lem5302931 : term551 = term454.
Proof. exact (fun_ext (fun x : type1019 => @lem5302930 x)). Qed.
Lemma lem5302932 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5302933 : term552 = term455.
Proof. exact (MK_COMB (@lem5302932) (@lem5302931)). Qed.
Lemma lem5302934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302935 : term553 = term456.
Proof. exact (MK_COMB (@lem5302934) (@lem5302933)). Qed.
Lemma lem5302936 : term544 = term544.
Proof. exact (eq_refl term544). Qed.
Lemma lem5302937 : term548 = term545.
Proof. exact (MK_COMB (@lem5302935) (@lem5302936)). Qed.
Lemma lem5302938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302939 : term554 = term555.
Proof. exact (MK_COMB (@lem5302938) (@lem5302937)). Qed.
Lemma lem5302940 (x : type1019) : (term550 x) = (term452 x).
Proof. exact (eq_refl (term550 x)). Qed.
Lemma lem5302941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5302942 (x : type1019) : (term556 x) = (term557 x).
Proof. exact (MK_COMB (@lem5302941) (@lem5302940 x)). Qed.
Lemma lem5302943 : term544 = term544.
Proof. exact (eq_refl term544). Qed.
Lemma lem5302944 (x : type1019) : (term558 x) = (term559 x).
Proof. exact (MK_COMB (@lem5302942 x) (@lem5302943)). Qed.
Lemma lem5302945 : term560 = term561.
Proof. exact (fun_ext (fun x : type1019 => @lem5302944 x)). Qed.
Lemma lem5302946 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5302947 : term549 = term562.
Proof. exact (MK_COMB (@lem5302946) (@lem5302945)). Qed.
Lemma lem5302948 : (term548 = term549) = (term545 = term562).
Proof. exact (MK_COMB (@lem5302939) (@lem5302947)). Qed.
Lemma lem5302949 : term545 = term562.
Proof. exact (EQ_MP (@lem5302948) (@lem5302929)). Qed.
Lemma lem5302951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5302952 (P : Prop) (Q : type256) : (term563 P Q) = (term564 P Q).
Proof. exact (@lem5302951 type1021 P Q). Qed.
Lemma lem5302953 (x : type1019) : (term565 x) = (term566 x).
Proof. exact (@lem5302952 (term452 x) term543). Qed.
Lemma lem5302954 (b : type1021) : (term567 b) = (term541 b).
Proof. exact (eq_refl (term567 b)). Qed.
Lemma lem5302955 : term568 = term543.
Proof. exact (fun_ext (fun b : type1021 => @lem5302954 b)). Qed.
Lemma lem5302956 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5302957 : term569 = term544.
Proof. exact (MK_COMB (@lem5302956) (@lem5302955)). Qed.
Lemma lem5302958 (x : type1019) : (term557 x) = (term557 x).
Proof. exact (eq_refl (term557 x)). Qed.
Lemma lem5302959 (x : type1019) : (term565 x) = (term559 x).
Proof. exact (MK_COMB (@lem5302958 x) (@lem5302957)). Qed.
Lemma lem5302960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5302961 (x : type1019) : (term570 x) = (term571 x).
Proof. exact (MK_COMB (@lem5302960) (@lem5302959 x)). Qed.
Lemma lem5302962 (b : type1021) : (term567 b) = (term541 b).
Proof. exact (eq_refl (term567 b)). Qed.
Lemma lem5302963 (x : type1019) : (term557 x) = (term557 x).
Proof. exact (eq_refl (term557 x)). Qed.
Lemma lem5302964 (x : type1019) (b : type1021) : (term572 x b) = (term573 x b).
Proof. exact (MK_COMB (@lem5302963 x) (@lem5302962 b)). Qed.
Lemma lem5302965 (x : type1019) : (term574 x) = (term575 x).
Proof. exact (fun_ext (fun b : type1021 => @lem5302964 x b)). Qed.
Lemma lem5302966 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5302967 (x : type1019) : (term566 x) = (term576 x).
Proof. exact (MK_COMB (@lem5302966) (@lem5302965 x)). Qed.
Lemma lem5302968 (x : type1019) : ((term565 x) = (term566 x)) = ((term559 x) = (term576 x)).
Proof. exact (MK_COMB (@lem5302961 x) (@lem5302967 x)). Qed.
Lemma lem5302969 (x : type1019) : (term559 x) = (term576 x).
Proof. exact (EQ_MP (@lem5302968 x) (@lem5302953 x)). Qed.
Lemma lem5302970 : term561 = term577.
Proof. exact (fun_ext (fun x : type1019 => @lem5302969 x)). Qed.
Lemma lem5302971 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5302972 : term562 = term578.
Proof. exact (MK_COMB (@lem5302971) (@lem5302970)). Qed.
Lemma lem5302973 : term545 = term578.
Proof. exact (TRANS (@lem5302949) (@lem5302972)). Qed.
Lemma lem5302974 : term365 = term578.
Proof. exact (TRANS (@lem5302925) (@lem5302973)). Qed.
Lemma lem5302975 : term317 = term578.
Proof. exact (TRANS (@lem5302611) (@lem5302974)). Qed.
Lemma lem5302976 : term10 = term578.
Proof. exact (TRANS (@lem5302141) (@lem5302975)). Qed.
Lemma lem5302977 (h1 : term10) : term578.
Proof. exact (EQ_MP (@lem5302976) (@lem5301477 h1)). Qed.
Lemma lem5302978 (x : type1019) (h1 : term576 x) : term576 x.
Proof. exact (h1). Qed.
Lemma lem5302979 (x : type1019) (b : type1021) (h1 : term573 x b) : term573 x b.
Proof. exact (h1). Qed.
Lemma lem5302980 (s : real -> Prop) (h1 : term289 s) : term289 s.
Proof. exact (h1). Qed.
Lemma lem5302981 (s : real -> Prop) (l : real) (h1 : term287 s l) : term287 s l.
Proof. exact (h1). Qed.
Lemma lem5302982 (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term284 x' s l) : term284 x' s l.
Proof. exact (h1). Qed.
Lemma lem5302989 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5303008 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term579 x b s l) = (term579 x b s l).
Proof. exact (eq_refl (term579 x b s l)). Qed.
Lemma lem5303009 (b : type1021) (s : real -> Prop) (l : real) : (term580 b s l) = (term580 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303008 x b s l)). Qed.
Lemma lem5303010 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303011 (b : type1021) (s : real -> Prop) (l : real) : (term581 b s l) = (term581 b s l).
Proof. exact (MK_COMB (@lem5303010) (@lem5303009 b s l)). Qed.
Lemma lem5303012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303013 (b : type1021) (s : real -> Prop) (l : real) : (term582 b s l) = (term582 b s l).
Proof. exact (MK_COMB (@lem5303012) (@lem5303011 b s l)). Qed.
Lemma lem5303014 (b : type1021) (s : real -> Prop) (l : real) : (term583 b s l) = (term583 b s l).
Proof. exact (MK_COMB (@lem5303013 b s l) (@lem5302989 s l)). Qed.
Lemma lem5303023 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303024 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term584 b s l).
Proof. exact (MK_COMB (@lem5303023 s) (@lem5303014 b s l)). Qed.
Lemma lem5303033 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303034 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term585 b s l).
Proof. exact (MK_COMB (@lem5303033 s l) (@lem5303024 b s l)). Qed.
Lemma lem5303035 (b : type1021) (s : real -> Prop) : (term586 b s) = (term586 b s).
Proof. exact (fun_ext (fun l : real => @lem5303034 b s l)). Qed.
Lemma lem5303036 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303037 (b : type1021) (s : real -> Prop) : (term537 b s) = (term537 b s).
Proof. exact (MK_COMB (@lem5303036) (@lem5303035 b s)). Qed.
Lemma lem5303038 (b : type1021) : (term539 b) = (term539 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303037 b s)). Qed.
Lemma lem5303039 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303040 (b : type1021) : (term541 b) = (term541 b).
Proof. exact (MK_COMB (@lem5303039) (@lem5303038 b)). Qed.
Lemma lem5303049 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5303076 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term587 x s l b) = (term587 x s l b).
Proof. exact (eq_refl (term587 x s l b)). Qed.
Lemma lem5303077 (x : type1019) (s : real -> Prop) (l : real) : (term588 x s l) = (term588 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303076 x s l b)). Qed.
Lemma lem5303078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303079 (x : type1019) (s : real -> Prop) (l : real) : (term589 x s l) = (term589 x s l).
Proof. exact (MK_COMB (@lem5303078) (@lem5303077 x s l)). Qed.
Lemma lem5303080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5303081 (x : type1019) (s : real -> Prop) (l : real) : (term590 x s l) = (term590 x s l).
Proof. exact (MK_COMB (@lem5303080) (@lem5303079 x s l)). Qed.
Lemma lem5303082 (x : type1019) (s : real -> Prop) (l : real) : (term591 x s l) = (term591 x s l).
Proof. exact (MK_COMB (@lem5303081 x s l) (@lem5303049 s l)). Qed.
Lemma lem5303089 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5303090 (x : type1019) (s : real -> Prop) (l : real) : (term592 x s l) = (term592 x s l).
Proof. exact (MK_COMB (@lem5303089 s) (@lem5303082 x s l)). Qed.
Lemma lem5303097 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5303098 (x : type1019) (s : real -> Prop) (l : real) : (term593 x s l) = (term593 x s l).
Proof. exact (MK_COMB (@lem5303097 s l) (@lem5303090 x s l)). Qed.
Lemma lem5303099 (x : type1019) (s : real -> Prop) : (term594 x s) = (term594 x s).
Proof. exact (fun_ext (fun l : real => @lem5303098 x s l)). Qed.
Lemma lem5303100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303101 (x : type1019) (s : real -> Prop) : (term448 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5303100) (@lem5303099 x s)). Qed.
Lemma lem5303102 (x : type1019) : (term450 x) = (term450 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303101 x s)). Qed.
Lemma lem5303103 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303104 (x : type1019) : (term452 x) = (term452 x).
Proof. exact (MK_COMB (@lem5303103) (@lem5303102 x)). Qed.
Lemma lem5303105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303106 (x : type1019) : (term557 x) = (term557 x).
Proof. exact (MK_COMB (@lem5303105) (@lem5303104 x)). Qed.
Lemma lem5303107 (x : type1019) (b : type1021) : (term573 x b) = (term573 x b).
Proof. exact (MK_COMB (@lem5303106 x) (@lem5303040 b)). Qed.
Lemma lem5303108 (x : type1019) (b : type1021) (h1 : term573 x b) : term573 x b.
Proof. exact (EQ_MP (@lem5303107 x b) (@lem5302979 x b h1)). Qed.
Lemma lem5303123 (s : real -> Prop) (x : real) (l : real) : (term44 s x l) = (term44 s x l).
Proof. exact (eq_refl (term44 s x l)). Qed.
Lemma lem5303124 (s : real -> Prop) (l : real) : (term54 s l) = (term54 s l).
Proof. exact (fun_ext (fun x : real => @lem5303123 s x l)). Qed.
Lemma lem5303125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303126 (s : real -> Prop) (l : real) : (term55 s l) = (term55 s l).
Proof. exact (MK_COMB (@lem5303125) (@lem5303124 s l)). Qed.
Lemma lem5303135 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303136 (s : real -> Prop) (l : real) : (term208 s l) = (term208 s l).
Proof. exact (MK_COMB (@lem5303135 s) (@lem5303126 s l)). Qed.
Lemma lem5303143 (s : real -> Prop) (l : real) : (term37 s l) = (term37 s l).
Proof. exact (eq_refl (term37 s l)). Qed.
Lemma lem5303144 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (fun_ext (fun l : real => @lem5303143 s l)). Qed.
Lemma lem5303145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303146 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5303145) (@lem5303144 s)). Qed.
Lemma lem5303147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303148 (s : real -> Prop) : (term73 s) = (term73 s).
Proof. exact (MK_COMB (@lem5303147) (@lem5303146 s)). Qed.
Lemma lem5303149 (s : real -> Prop) (l : real) : (term221 s l) = (term221 s l).
Proof. exact (MK_COMB (@lem5303148 s) (@lem5303136 s l)). Qed.
Lemma lem5303168 (s : real -> Prop) (x' : real -> real) (b : real) : (term133 s x' b) = (term133 s x' b).
Proof. exact (eq_refl (term133 s x' b)). Qed.
Lemma lem5303169 (s : real -> Prop) (x' : real -> real) : (term135 s x') = (term135 s x').
Proof. exact (fun_ext (fun b : real => @lem5303168 s x' b)). Qed.
Lemma lem5303170 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303171 (s : real -> Prop) (x' : real -> real) : (term137 s x') = (term137 s x').
Proof. exact (MK_COMB (@lem5303170) (@lem5303169 s x')). Qed.
Lemma lem5303178 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5303179 (s : real -> Prop) (x' : real -> real) : (term154 s x') = (term154 s x').
Proof. exact (MK_COMB (@lem5303178 s) (@lem5303171 s x')). Qed.
Lemma lem5303186 (s : real -> Prop) (l : real) : (term171 s l) = (term171 s l).
Proof. exact (eq_refl (term171 s l)). Qed.
Lemma lem5303187 (l : real) (s : real -> Prop) (x' : real -> real) : (term189 l s x') = (term189 l s x').
Proof. exact (MK_COMB (@lem5303186 s l) (@lem5303179 s x')). Qed.
Lemma lem5303188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5303189 (l : real) (s : real -> Prop) (x' : real -> real) : (term282 l s x') = (term282 l s x').
Proof. exact (MK_COMB (@lem5303188) (@lem5303187 l s x')). Qed.
Lemma lem5303190 (x' : real -> real) (s : real -> Prop) (l : real) : (term284 x' s l) = (term284 x' s l).
Proof. exact (MK_COMB (@lem5303189 l s x') (@lem5303149 s l)). Qed.
Lemma lem5303191 (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term284 x' s l) : term284 x' s l.
Proof. exact (EQ_MP (@lem5303190 x' s l) (@lem5302982 x' s l h1)). Qed.
Lemma lem5303192 (x : type1019) (b : type1021) (h1 : term573 x b) : term541 b.
Proof. exact (proj2 (@lem5303108 x b h1)). Qed.
Lemma lem5303193 (x : type1019) (b : type1021) (h1 : term573 x b) : term452 x.
Proof. exact (proj1 (@lem5303108 x b h1)). Qed.
Lemma lem5303194 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : term189 l s x'.
Proof. exact (h1). Qed.
Lemma lem5303195 (s : real -> Prop) (l : real) (h1 : term221 s l) : term221 s l.
Proof. exact (h1). Qed.
Lemma lem5303196 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : term154 s x'.
Proof. exact (proj2 (@lem5303194 l s x' h1)). Qed.
Lemma lem5303199 (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term137 s x'.
Proof. exact (h1). Qed.
Lemma lem5303200 (s : real -> Prop) (l : real) (h1 : term221 s l) : term208 s l.
Proof. exact (proj2 (@lem5303195 s l h1)). Qed.
Lemma lem5303201 (s : real -> Prop) (l : real) (h1 : term221 s l) : term40 s.
Proof. exact (proj1 (@lem5303195 s l h1)). Qed.
Lemma lem5303202 (s : real -> Prop) (l : real) (h1 : term221 s l) : term55 s l.
Proof. exact (proj2 (@lem5303200 s l h1)). Qed.
Lemma lem5303333 {A : Type'} (P : A -> Prop) (Q : Prop) : (term595 A P Q) = (term596 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5303334 (P : real -> Prop) (Q : Prop) : (term597 P Q) = (term598 P Q).
Proof. exact (@lem5303333 real P Q). Qed.
Lemma lem5303335 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term600 b s l).
Proof. exact (@lem5303334 (term580 b s l) ((sup s) = l)). Qed.
Lemma lem5303336 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term601 b s l x) = (term579 x b s l).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5303337 (b : type1021) (s : real -> Prop) (l : real) : (term602 b s l) = (term580 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303336 x b s l)). Qed.
Lemma lem5303338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303339 (b : type1021) (s : real -> Prop) (l : real) : (term603 b s l) = (term581 b s l).
Proof. exact (MK_COMB (@lem5303338) (@lem5303337 b s l)). Qed.
Lemma lem5303340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303341 (b : type1021) (s : real -> Prop) (l : real) : (term604 b s l) = (term582 b s l).
Proof. exact (MK_COMB (@lem5303340) (@lem5303339 b s l)). Qed.
Lemma lem5303342 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5303343 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term583 b s l).
Proof. exact (MK_COMB (@lem5303341 b s l) (@lem5303342 s l)). Qed.
Lemma lem5303344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303345 (b : type1021) (s : real -> Prop) (l : real) : (term605 b s l) = (term606 b s l).
Proof. exact (MK_COMB (@lem5303344) (@lem5303343 b s l)). Qed.
Lemma lem5303346 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term601 b s l x) = (term579 x b s l).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5303347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303348 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term607 b s l x) = (term608 x b s l).
Proof. exact (MK_COMB (@lem5303347) (@lem5303346 x b s l)). Qed.
Lemma lem5303349 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5303350 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term609 b x s l) = (term610 x b s l).
Proof. exact (MK_COMB (@lem5303348 x b s l) (@lem5303349 s l)). Qed.
Lemma lem5303351 (b : type1021) (s : real -> Prop) (l : real) : (term611 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303350 x b s l)). Qed.
Lemma lem5303352 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303353 (b : type1021) (s : real -> Prop) (l : real) : (term600 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5303352) (@lem5303351 b s l)). Qed.
Lemma lem5303354 (b : type1021) (s : real -> Prop) (l : real) : ((term599 b s l) = (term600 b s l)) = ((term583 b s l) = (term613 b s l)).
Proof. exact (MK_COMB (@lem5303345 b s l) (@lem5303353 b s l)). Qed.
Lemma lem5303355 (b : type1021) (s : real -> Prop) (l : real) : (term583 b s l) = (term613 b s l).
Proof. exact (EQ_MP (@lem5303354 b s l) (@lem5303335 b s l)). Qed.
Lemma lem5303356 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303357 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5303356 s) (@lem5303355 b s l)). Qed.
Lemma lem5303359 {A : Type'} (P : Prop) (Q : A -> Prop) : (term615 A P Q) = (term616 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5303360 (P : Prop) (Q : real -> Prop) : (term617 P Q) = (term618 P Q).
Proof. exact (@lem5303359 real P Q). Qed.
Lemma lem5303361 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term620 b s l).
Proof. exact (@lem5303360 (term70 s) (term612 b s l)). Qed.
Lemma lem5303362 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 x b s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5303363 (b : type1021) (s : real -> Prop) (l : real) : (term622 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303362 x b s l)). Qed.
Lemma lem5303364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303365 (b : type1021) (s : real -> Prop) (l : real) : (term623 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5303364) (@lem5303363 b s l)). Qed.
Lemma lem5303366 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303367 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5303366 s) (@lem5303365 b s l)). Qed.
Lemma lem5303368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303369 (b : type1021) (s : real -> Prop) (l : real) : (term624 b s l) = (term625 b s l).
Proof. exact (MK_COMB (@lem5303368) (@lem5303367 b s l)). Qed.
Lemma lem5303370 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 x b s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5303371 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303372 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term626 b s l x) = (term627 x b s l).
Proof. exact (MK_COMB (@lem5303371 s) (@lem5303370 x b s l)). Qed.
Lemma lem5303373 (b : type1021) (s : real -> Prop) (l : real) : (term628 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303372 x b s l)). Qed.
Lemma lem5303374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303375 (b : type1021) (s : real -> Prop) (l : real) : (term620 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5303374) (@lem5303373 b s l)). Qed.
Lemma lem5303376 (b : type1021) (s : real -> Prop) (l : real) : ((term619 b s l) = (term620 b s l)) = ((term614 b s l) = (term630 b s l)).
Proof. exact (MK_COMB (@lem5303369 b s l) (@lem5303375 b s l)). Qed.
Lemma lem5303377 (b : type1021) (s : real -> Prop) (l : real) : (term614 b s l) = (term630 b s l).
Proof. exact (EQ_MP (@lem5303376 b s l) (@lem5303361 b s l)). Qed.
Lemma lem5303378 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term630 b s l).
Proof. exact (TRANS (@lem5303357 b s l) (@lem5303377 b s l)). Qed.
Lemma lem5303379 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303380 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5303379 s l) (@lem5303378 b s l)). Qed.
Lemma lem5303382 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5303383 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5303382 real P Q). Qed.
Lemma lem5303384 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term637 b s l).
Proof. exact (@lem5303383 (term37 s l) (term629 b s l)). Qed.
Lemma lem5303385 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 x b s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5303386 (b : type1021) (s : real -> Prop) (l : real) : (term639 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303385 x b s l)). Qed.
Lemma lem5303387 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303388 (b : type1021) (s : real -> Prop) (l : real) : (term640 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5303387) (@lem5303386 b s l)). Qed.
Lemma lem5303389 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303390 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5303389 s l) (@lem5303388 b s l)). Qed.
Lemma lem5303391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303392 (b : type1021) (s : real -> Prop) (l : real) : (term641 b s l) = (term642 b s l).
Proof. exact (MK_COMB (@lem5303391) (@lem5303390 b s l)). Qed.
Lemma lem5303393 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 x b s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5303394 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303395 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term643 b s l x) = (term644 x b s l).
Proof. exact (MK_COMB (@lem5303394 s l) (@lem5303393 x b s l)). Qed.
Lemma lem5303396 (b : type1021) (s : real -> Prop) (l : real) : (term645 b s l) = (term646 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303395 x b s l)). Qed.
Lemma lem5303397 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303398 (b : type1021) (s : real -> Prop) (l : real) : (term637 b s l) = (term647 b s l).
Proof. exact (MK_COMB (@lem5303397) (@lem5303396 b s l)). Qed.
Lemma lem5303399 (b : type1021) (s : real -> Prop) (l : real) : ((term636 b s l) = (term637 b s l)) = ((term631 b s l) = (term647 b s l)).
Proof. exact (MK_COMB (@lem5303392 b s l) (@lem5303398 b s l)). Qed.
Lemma lem5303400 (b : type1021) (s : real -> Prop) (l : real) : (term631 b s l) = (term647 b s l).
Proof. exact (EQ_MP (@lem5303399 b s l) (@lem5303384 b s l)). Qed.
Lemma lem5303401 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term647 b s l).
Proof. exact (TRANS (@lem5303380 b s l) (@lem5303400 b s l)). Qed.
Lemma lem5303402 (b : type1021) (s : real -> Prop) : (term586 b s) = (term648 b s).
Proof. exact (fun_ext (fun l : real => @lem5303401 b s l)). Qed.
Lemma lem5303403 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303404 (b : type1021) (s : real -> Prop) : (term537 b s) = (term649 b s).
Proof. exact (MK_COMB (@lem5303403) (@lem5303402 b s)). Qed.
Lemma lem5303405 (b : type1021) : (term539 b) = (term650 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303404 b s)). Qed.
Lemma lem5303406 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303407 (b : type1021) : (term541 b) = (term651 b).
Proof. exact (MK_COMB (@lem5303406) (@lem5303405 b)). Qed.
Lemma lem5303427 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term644 x b s l) = (term652 x b s l).
Proof. exact (@lem19490 (term70 s) (term37 s l) (term610 x b s l)). Qed.
Lemma lem5303434 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term653 x b s l) = (term654 x b s l).
Proof. exact (@lem19490 (term579 x b s l) (term37 s l) ((sup s) = l)). Qed.
Lemma lem5303437 (l : real) (s : real -> Prop) : (term655 l s) = (term655 l s).
Proof. exact (eq_refl (term655 l s)). Qed.
Lemma lem5303438 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term652 x b s l) = (term656 x b s l).
Proof. exact (MK_COMB (@lem5303437 l s) (@lem5303434 x b s l)). Qed.
Lemma lem5303440 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term644 x b s l) = (term656 x b s l).
Proof. exact (TRANS (@lem5303427 x b s l) (@lem5303438 x b s l)). Qed.
Lemma lem5303441 (b : type1021) (s : real -> Prop) (l : real) : (term646 b s l) = (term657 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303440 x b s l)). Qed.
Lemma lem5303442 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303443 (b : type1021) (s : real -> Prop) (l : real) : (term647 b s l) = (term658 b s l).
Proof. exact (MK_COMB (@lem5303442) (@lem5303441 b s l)). Qed.
Lemma lem5303444 (b : type1021) (s : real -> Prop) : (term648 b s) = (term659 b s).
Proof. exact (fun_ext (fun l : real => @lem5303443 b s l)). Qed.
Lemma lem5303445 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303446 (b : type1021) (s : real -> Prop) : (term649 b s) = (term660 b s).
Proof. exact (MK_COMB (@lem5303445) (@lem5303444 b s)). Qed.
Lemma lem5303447 (b : type1021) : (term650 b) = (term661 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303446 b s)). Qed.
Lemma lem5303448 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303449 (b : type1021) : (term651 b) = (term662 b).
Proof. exact (MK_COMB (@lem5303448) (@lem5303447 b)). Qed.
Lemma lem5303450 (b : type1021) : (term541 b) = (term662 b).
Proof. exact (TRANS (@lem5303407 b) (@lem5303449 b)). Qed.
Lemma lem5303451 (x : type1019) (b : type1021) (h1 : term573 x b) : term662 b.
Proof. exact (EQ_MP (@lem5303450 b) (@lem5303192 x b h1)). Qed.
Lemma lem5303459 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5303589 {A : Type'} (P : A -> Prop) (Q : Prop) : (term595 A P Q) = (term596 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem5303590 (P : real -> Prop) (Q : Prop) : (term597 P Q) = (term598 P Q).
Proof. exact (@lem5303589 real P Q). Qed.
Lemma lem5303591 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term600 b s l).
Proof. exact (@lem5303590 (term580 b s l) ((sup s) = l)). Qed.
Lemma lem5303592 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term601 b s l x) = (term579 x b s l).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5303593 (b : type1021) (s : real -> Prop) (l : real) : (term602 b s l) = (term580 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303592 x b s l)). Qed.
Lemma lem5303594 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303595 (b : type1021) (s : real -> Prop) (l : real) : (term603 b s l) = (term581 b s l).
Proof. exact (MK_COMB (@lem5303594) (@lem5303593 b s l)). Qed.
Lemma lem5303596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303597 (b : type1021) (s : real -> Prop) (l : real) : (term604 b s l) = (term582 b s l).
Proof. exact (MK_COMB (@lem5303596) (@lem5303595 b s l)). Qed.
Lemma lem5303598 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5303599 (b : type1021) (s : real -> Prop) (l : real) : (term599 b s l) = (term583 b s l).
Proof. exact (MK_COMB (@lem5303597 b s l) (@lem5303598 s l)). Qed.
Lemma lem5303600 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303601 (b : type1021) (s : real -> Prop) (l : real) : (term605 b s l) = (term606 b s l).
Proof. exact (MK_COMB (@lem5303600) (@lem5303599 b s l)). Qed.
Lemma lem5303602 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term601 b s l x) = (term579 x b s l).
Proof. exact (eq_refl (term601 b s l x)). Qed.
Lemma lem5303603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5303604 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term607 b s l x) = (term608 x b s l).
Proof. exact (MK_COMB (@lem5303603) (@lem5303602 x b s l)). Qed.
Lemma lem5303605 (s : real -> Prop) (l : real) : ((sup s) = l) = ((sup s) = l).
Proof. exact (eq_refl ((sup s) = l)). Qed.
Lemma lem5303606 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term609 b x s l) = (term610 x b s l).
Proof. exact (MK_COMB (@lem5303604 x b s l) (@lem5303605 s l)). Qed.
Lemma lem5303607 (b : type1021) (s : real -> Prop) (l : real) : (term611 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303606 x b s l)). Qed.
Lemma lem5303608 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303609 (b : type1021) (s : real -> Prop) (l : real) : (term600 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5303608) (@lem5303607 b s l)). Qed.
Lemma lem5303610 (b : type1021) (s : real -> Prop) (l : real) : ((term599 b s l) = (term600 b s l)) = ((term583 b s l) = (term613 b s l)).
Proof. exact (MK_COMB (@lem5303601 b s l) (@lem5303609 b s l)). Qed.
Lemma lem5303611 (b : type1021) (s : real -> Prop) (l : real) : (term583 b s l) = (term613 b s l).
Proof. exact (EQ_MP (@lem5303610 b s l) (@lem5303591 b s l)). Qed.
Lemma lem5303612 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303613 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5303612 s) (@lem5303611 b s l)). Qed.
Lemma lem5303615 {A : Type'} (P : Prop) (Q : A -> Prop) : (term615 A P Q) = (term616 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5303616 (P : Prop) (Q : real -> Prop) : (term617 P Q) = (term618 P Q).
Proof. exact (@lem5303615 real P Q). Qed.
Lemma lem5303617 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term620 b s l).
Proof. exact (@lem5303616 (term70 s) (term612 b s l)). Qed.
Lemma lem5303618 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 x b s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5303619 (b : type1021) (s : real -> Prop) (l : real) : (term622 b s l) = (term612 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303618 x b s l)). Qed.
Lemma lem5303620 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303621 (b : type1021) (s : real -> Prop) (l : real) : (term623 b s l) = (term613 b s l).
Proof. exact (MK_COMB (@lem5303620) (@lem5303619 b s l)). Qed.
Lemma lem5303622 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303623 (b : type1021) (s : real -> Prop) (l : real) : (term619 b s l) = (term614 b s l).
Proof. exact (MK_COMB (@lem5303622 s) (@lem5303621 b s l)). Qed.
Lemma lem5303624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303625 (b : type1021) (s : real -> Prop) (l : real) : (term624 b s l) = (term625 b s l).
Proof. exact (MK_COMB (@lem5303624) (@lem5303623 b s l)). Qed.
Lemma lem5303626 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term621 b s l x) = (term610 x b s l).
Proof. exact (eq_refl (term621 b s l x)). Qed.
Lemma lem5303627 (s : real -> Prop) : (term20 s) = (term20 s).
Proof. exact (eq_refl (term20 s)). Qed.
Lemma lem5303628 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term626 b s l x) = (term627 x b s l).
Proof. exact (MK_COMB (@lem5303627 s) (@lem5303626 x b s l)). Qed.
Lemma lem5303629 (b : type1021) (s : real -> Prop) (l : real) : (term628 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303628 x b s l)). Qed.
Lemma lem5303630 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303631 (b : type1021) (s : real -> Prop) (l : real) : (term620 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5303630) (@lem5303629 b s l)). Qed.
Lemma lem5303632 (b : type1021) (s : real -> Prop) (l : real) : ((term619 b s l) = (term620 b s l)) = ((term614 b s l) = (term630 b s l)).
Proof. exact (MK_COMB (@lem5303625 b s l) (@lem5303631 b s l)). Qed.
Lemma lem5303633 (b : type1021) (s : real -> Prop) (l : real) : (term614 b s l) = (term630 b s l).
Proof. exact (EQ_MP (@lem5303632 b s l) (@lem5303617 b s l)). Qed.
Lemma lem5303634 (b : type1021) (s : real -> Prop) (l : real) : (term584 b s l) = (term630 b s l).
Proof. exact (TRANS (@lem5303613 b s l) (@lem5303633 b s l)). Qed.
Lemma lem5303635 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303636 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5303635 s l) (@lem5303634 b s l)). Qed.
Lemma lem5303638 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5303639 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5303638 real P Q). Qed.
Lemma lem5303640 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term637 b s l).
Proof. exact (@lem5303639 (term37 s l) (term629 b s l)). Qed.
Lemma lem5303641 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 x b s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5303642 (b : type1021) (s : real -> Prop) (l : real) : (term639 b s l) = (term629 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303641 x b s l)). Qed.
Lemma lem5303643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303644 (b : type1021) (s : real -> Prop) (l : real) : (term640 b s l) = (term630 b s l).
Proof. exact (MK_COMB (@lem5303643) (@lem5303642 b s l)). Qed.
Lemma lem5303645 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303646 (b : type1021) (s : real -> Prop) (l : real) : (term636 b s l) = (term631 b s l).
Proof. exact (MK_COMB (@lem5303645 s l) (@lem5303644 b s l)). Qed.
Lemma lem5303647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303648 (b : type1021) (s : real -> Prop) (l : real) : (term641 b s l) = (term642 b s l).
Proof. exact (MK_COMB (@lem5303647) (@lem5303646 b s l)). Qed.
Lemma lem5303649 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term638 b s l x) = (term627 x b s l).
Proof. exact (eq_refl (term638 b s l x)). Qed.
Lemma lem5303650 (s : real -> Prop) (l : real) : (term304 s l) = (term304 s l).
Proof. exact (eq_refl (term304 s l)). Qed.
Lemma lem5303651 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term643 b s l x) = (term644 x b s l).
Proof. exact (MK_COMB (@lem5303650 s l) (@lem5303649 x b s l)). Qed.
Lemma lem5303652 (b : type1021) (s : real -> Prop) (l : real) : (term645 b s l) = (term646 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303651 x b s l)). Qed.
Lemma lem5303653 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303654 (b : type1021) (s : real -> Prop) (l : real) : (term637 b s l) = (term647 b s l).
Proof. exact (MK_COMB (@lem5303653) (@lem5303652 b s l)). Qed.
Lemma lem5303655 (b : type1021) (s : real -> Prop) (l : real) : ((term636 b s l) = (term637 b s l)) = ((term631 b s l) = (term647 b s l)).
Proof. exact (MK_COMB (@lem5303648 b s l) (@lem5303654 b s l)). Qed.
Lemma lem5303656 (b : type1021) (s : real -> Prop) (l : real) : (term631 b s l) = (term647 b s l).
Proof. exact (EQ_MP (@lem5303655 b s l) (@lem5303640 b s l)). Qed.
Lemma lem5303657 (b : type1021) (s : real -> Prop) (l : real) : (term585 b s l) = (term647 b s l).
Proof. exact (TRANS (@lem5303636 b s l) (@lem5303656 b s l)). Qed.
Lemma lem5303658 (b : type1021) (s : real -> Prop) : (term586 b s) = (term648 b s).
Proof. exact (fun_ext (fun l : real => @lem5303657 b s l)). Qed.
Lemma lem5303659 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303660 (b : type1021) (s : real -> Prop) : (term537 b s) = (term649 b s).
Proof. exact (MK_COMB (@lem5303659) (@lem5303658 b s)). Qed.
Lemma lem5303661 (b : type1021) : (term539 b) = (term650 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303660 b s)). Qed.
Lemma lem5303662 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303663 (b : type1021) : (term541 b) = (term651 b).
Proof. exact (MK_COMB (@lem5303662) (@lem5303661 b)). Qed.
Lemma lem5303683 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term644 x b s l) = (term652 x b s l).
Proof. exact (@lem19490 (term70 s) (term37 s l) (term610 x b s l)). Qed.
Lemma lem5303690 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term653 x b s l) = (term654 x b s l).
Proof. exact (@lem19490 (term579 x b s l) (term37 s l) ((sup s) = l)). Qed.
Lemma lem5303693 (l : real) (s : real -> Prop) : (term655 l s) = (term655 l s).
Proof. exact (eq_refl (term655 l s)). Qed.
Lemma lem5303694 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term652 x b s l) = (term656 x b s l).
Proof. exact (MK_COMB (@lem5303693 l s) (@lem5303690 x b s l)). Qed.
Lemma lem5303696 (x : real) (b : type1021) (s : real -> Prop) (l : real) : (term644 x b s l) = (term656 x b s l).
Proof. exact (TRANS (@lem5303683 x b s l) (@lem5303694 x b s l)). Qed.
Lemma lem5303697 (b : type1021) (s : real -> Prop) (l : real) : (term646 b s l) = (term657 b s l).
Proof. exact (fun_ext (fun x : real => @lem5303696 x b s l)). Qed.
Lemma lem5303698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303699 (b : type1021) (s : real -> Prop) (l : real) : (term647 b s l) = (term658 b s l).
Proof. exact (MK_COMB (@lem5303698) (@lem5303697 b s l)). Qed.
Lemma lem5303700 (b : type1021) (s : real -> Prop) : (term648 b s) = (term659 b s).
Proof. exact (fun_ext (fun l : real => @lem5303699 b s l)). Qed.
Lemma lem5303701 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303702 (b : type1021) (s : real -> Prop) : (term649 b s) = (term660 b s).
Proof. exact (MK_COMB (@lem5303701) (@lem5303700 b s)). Qed.
Lemma lem5303703 (b : type1021) : (term650 b) = (term661 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303702 b s)). Qed.
Lemma lem5303704 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303705 (b : type1021) : (term651 b) = (term662 b).
Proof. exact (MK_COMB (@lem5303704) (@lem5303703 b)). Qed.
Lemma lem5303706 (b : type1021) : (term541 b) = (term662 b).
Proof. exact (TRANS (@lem5303663 b) (@lem5303705 b)). Qed.
Lemma lem5303707 (x : type1019) (b : type1021) (h1 : term573 x b) : term662 b.
Proof. exact (EQ_MP (@lem5303706 b) (@lem5303192 x b h1)). Qed.
Lemma lem5303717 (s : real -> Prop) (x' : real -> real) (b : real) : (term133 s x' b) = (term133 s x' b).
Proof. exact (eq_refl (term133 s x' b)). Qed.
Lemma lem5303718 (s : real -> Prop) (x' : real -> real) : (term135 s x') = (term135 s x').
Proof. exact (fun_ext (fun b : real => @lem5303717 s x' b)). Qed.
Lemma lem5303719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303721 (s : real -> Prop) (x' : real -> real) : (term137 s x') = (term137 s x').
Proof. exact (MK_COMB (@lem5303719) (@lem5303718 s x')). Qed.
Lemma lem5303722 (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term137 s x'.
Proof. exact (EQ_MP (@lem5303721 s x') (@lem5303199 s x' h1)). Qed.
Lemma lem5303724 {A : Type'} (P : A -> Prop) (Q : Prop) : (term663 A P Q) = (term664 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5303725 (P : real -> Prop) (Q : Prop) : (term665 P Q) = (term666 P Q).
Proof. exact (@lem5303724 real P Q). Qed.
Lemma lem5303726 (x : type1019) (s : real -> Prop) (l : real) : (term667 x s l) = (term668 x s l).
Proof. exact (@lem5303725 (term588 x s l) (term292 s l)). Qed.
Lemma lem5303727 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term669 x s l b) = (term587 x s l b).
Proof. exact (eq_refl (term669 x s l b)). Qed.
Lemma lem5303728 (x : type1019) (s : real -> Prop) (l : real) : (term670 x s l) = (term588 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303727 x s l b)). Qed.
Lemma lem5303729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303730 (x : type1019) (s : real -> Prop) (l : real) : (term671 x s l) = (term589 x s l).
Proof. exact (MK_COMB (@lem5303729) (@lem5303728 x s l)). Qed.
Lemma lem5303731 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5303732 (x : type1019) (s : real -> Prop) (l : real) : (term672 x s l) = (term590 x s l).
Proof. exact (MK_COMB (@lem5303731) (@lem5303730 x s l)). Qed.
Lemma lem5303733 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5303734 (x : type1019) (s : real -> Prop) (l : real) : (term667 x s l) = (term591 x s l).
Proof. exact (MK_COMB (@lem5303732 x s l) (@lem5303733 s l)). Qed.
Lemma lem5303735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303736 (x : type1019) (s : real -> Prop) (l : real) : (term673 x s l) = (term674 x s l).
Proof. exact (MK_COMB (@lem5303735) (@lem5303734 x s l)). Qed.
Lemma lem5303737 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term669 x s l b) = (term587 x s l b).
Proof. exact (eq_refl (term669 x s l b)). Qed.
Lemma lem5303738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5303739 (x : type1019) (s : real -> Prop) (l : real) (b : real) : (term675 x s l b) = (term676 x s l b).
Proof. exact (MK_COMB (@lem5303738) (@lem5303737 x s l b)). Qed.
Lemma lem5303740 (s : real -> Prop) (l : real) : (term292 s l) = (term292 s l).
Proof. exact (eq_refl (term292 s l)). Qed.
Lemma lem5303741 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term677 x b s l) = (term678 x b s l).
Proof. exact (MK_COMB (@lem5303739 x s l b) (@lem5303740 s l)). Qed.
Lemma lem5303742 (x : type1019) (s : real -> Prop) (l : real) : (term679 x s l) = (term680 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303741 x b s l)). Qed.
Lemma lem5303743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303744 (x : type1019) (s : real -> Prop) (l : real) : (term668 x s l) = (term681 x s l).
Proof. exact (MK_COMB (@lem5303743) (@lem5303742 x s l)). Qed.
Lemma lem5303745 (x : type1019) (s : real -> Prop) (l : real) : ((term667 x s l) = (term668 x s l)) = ((term591 x s l) = (term681 x s l)).
Proof. exact (MK_COMB (@lem5303736 x s l) (@lem5303744 x s l)). Qed.
Lemma lem5303746 (x : type1019) (s : real -> Prop) (l : real) : (term591 x s l) = (term681 x s l).
Proof. exact (EQ_MP (@lem5303745 x s l) (@lem5303726 x s l)). Qed.
Lemma lem5303747 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5303748 (x : type1019) (s : real -> Prop) (l : real) : (term592 x s l) = (term682 x s l).
Proof. exact (MK_COMB (@lem5303747 s) (@lem5303746 x s l)). Qed.
Lemma lem5303750 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5303751 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5303750 real P Q). Qed.
Lemma lem5303752 (x : type1019) (s : real -> Prop) (l : real) : (term683 x s l) = (term684 x s l).
Proof. exact (@lem5303751 (s = (@EMPTY real)) (term680 x s l)). Qed.
Lemma lem5303753 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term685 x s l b) = (term678 x b s l).
Proof. exact (eq_refl (term685 x s l b)). Qed.
Lemma lem5303754 (x : type1019) (s : real -> Prop) (l : real) : (term686 x s l) = (term680 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303753 x b s l)). Qed.
Lemma lem5303755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303756 (x : type1019) (s : real -> Prop) (l : real) : (term687 x s l) = (term681 x s l).
Proof. exact (MK_COMB (@lem5303755) (@lem5303754 x s l)). Qed.
Lemma lem5303757 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5303758 (x : type1019) (s : real -> Prop) (l : real) : (term683 x s l) = (term682 x s l).
Proof. exact (MK_COMB (@lem5303757 s) (@lem5303756 x s l)). Qed.
Lemma lem5303759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303760 (x : type1019) (s : real -> Prop) (l : real) : (term688 x s l) = (term689 x s l).
Proof. exact (MK_COMB (@lem5303759) (@lem5303758 x s l)). Qed.
Lemma lem5303761 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term685 x s l b) = (term678 x b s l).
Proof. exact (eq_refl (term685 x s l b)). Qed.
Lemma lem5303762 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5303763 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term690 x s l b) = (term691 x b s l).
Proof. exact (MK_COMB (@lem5303762 s) (@lem5303761 x b s l)). Qed.
Lemma lem5303764 (x : type1019) (s : real -> Prop) (l : real) : (term692 x s l) = (term693 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303763 x b s l)). Qed.
Lemma lem5303765 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303766 (x : type1019) (s : real -> Prop) (l : real) : (term684 x s l) = (term694 x s l).
Proof. exact (MK_COMB (@lem5303765) (@lem5303764 x s l)). Qed.
Lemma lem5303767 (x : type1019) (s : real -> Prop) (l : real) : ((term683 x s l) = (term684 x s l)) = ((term682 x s l) = (term694 x s l)).
Proof. exact (MK_COMB (@lem5303760 x s l) (@lem5303766 x s l)). Qed.
Lemma lem5303768 (x : type1019) (s : real -> Prop) (l : real) : (term682 x s l) = (term694 x s l).
Proof. exact (EQ_MP (@lem5303767 x s l) (@lem5303752 x s l)). Qed.
Lemma lem5303769 (x : type1019) (s : real -> Prop) (l : real) : (term592 x s l) = (term694 x s l).
Proof. exact (TRANS (@lem5303748 x s l) (@lem5303768 x s l)). Qed.
Lemma lem5303770 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5303771 (x : type1019) (s : real -> Prop) (l : real) : (term593 x s l) = (term695 x s l).
Proof. exact (MK_COMB (@lem5303770 s l) (@lem5303769 x s l)). Qed.
Lemma lem5303773 {A : Type'} (P : Prop) (Q : A -> Prop) : (term632 A P Q) = (term633 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5303774 (P : Prop) (Q : real -> Prop) : (term634 P Q) = (term635 P Q).
Proof. exact (@lem5303773 real P Q). Qed.
Lemma lem5303775 (x : type1019) (s : real -> Prop) (l : real) : (term696 x s l) = (term697 x s l).
Proof. exact (@lem5303774 (has_sup s l) (term693 x s l)). Qed.
Lemma lem5303776 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term698 x s l b) = (term691 x b s l).
Proof. exact (eq_refl (term698 x s l b)). Qed.
Lemma lem5303777 (x : type1019) (s : real -> Prop) (l : real) : (term699 x s l) = (term693 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303776 x b s l)). Qed.
Lemma lem5303778 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303779 (x : type1019) (s : real -> Prop) (l : real) : (term700 x s l) = (term694 x s l).
Proof. exact (MK_COMB (@lem5303778) (@lem5303777 x s l)). Qed.
Lemma lem5303780 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5303781 (x : type1019) (s : real -> Prop) (l : real) : (term696 x s l) = (term695 x s l).
Proof. exact (MK_COMB (@lem5303780 s l) (@lem5303779 x s l)). Qed.
Lemma lem5303782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5303783 (x : type1019) (s : real -> Prop) (l : real) : (term701 x s l) = (term702 x s l).
Proof. exact (MK_COMB (@lem5303782) (@lem5303781 x s l)). Qed.
Lemma lem5303784 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term698 x s l b) = (term691 x b s l).
Proof. exact (eq_refl (term698 x s l b)). Qed.
Lemma lem5303785 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5303786 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term703 x s l b) = (term704 x b s l).
Proof. exact (MK_COMB (@lem5303785 s l) (@lem5303784 x b s l)). Qed.
Lemma lem5303787 (x : type1019) (s : real -> Prop) (l : real) : (term705 x s l) = (term706 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303786 x b s l)). Qed.
Lemma lem5303788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303789 (x : type1019) (s : real -> Prop) (l : real) : (term697 x s l) = (term707 x s l).
Proof. exact (MK_COMB (@lem5303788) (@lem5303787 x s l)). Qed.
Lemma lem5303790 (x : type1019) (s : real -> Prop) (l : real) : ((term696 x s l) = (term697 x s l)) = ((term695 x s l) = (term707 x s l)).
Proof. exact (MK_COMB (@lem5303783 x s l) (@lem5303789 x s l)). Qed.
Lemma lem5303791 (x : type1019) (s : real -> Prop) (l : real) : (term695 x s l) = (term707 x s l).
Proof. exact (EQ_MP (@lem5303790 x s l) (@lem5303775 x s l)). Qed.
Lemma lem5303792 (x : type1019) (s : real -> Prop) (l : real) : (term593 x s l) = (term707 x s l).
Proof. exact (TRANS (@lem5303771 x s l) (@lem5303791 x s l)). Qed.
Lemma lem5303793 (x : type1019) (s : real -> Prop) : (term594 x s) = (term708 x s).
Proof. exact (fun_ext (fun l : real => @lem5303792 x s l)). Qed.
Lemma lem5303794 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303795 (x : type1019) (s : real -> Prop) : (term448 x s) = (term709 x s).
Proof. exact (MK_COMB (@lem5303794) (@lem5303793 x s)). Qed.
Lemma lem5303796 (x : type1019) : (term450 x) = (term710 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303795 x s)). Qed.
Lemma lem5303797 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303798 (x : type1019) : (term452 x) = (term711 x).
Proof. exact (MK_COMB (@lem5303797) (@lem5303796 x)). Qed.
Lemma lem5303815 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term678 x b s l) = (term712 x b s l).
Proof. exact (@lem19699 (term713 x l b s) (term714 x s l b) (term292 s l)). Qed.
Lemma lem5303818 (s : real -> Prop) : (term66 s) = (term66 s).
Proof. exact (eq_refl (term66 s)). Qed.
Lemma lem5303819 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term691 x b s l) = (term715 x b s l).
Proof. exact (MK_COMB (@lem5303818 s) (@lem5303815 x b s l)). Qed.
Lemma lem5303826 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term715 x b s l) = (term716 x b s l).
Proof. exact (@lem19490 (term717 x b s l) (s = (@EMPTY real)) (term718 x b s l)). Qed.
Lemma lem5303827 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term691 x b s l) = (term716 x b s l).
Proof. exact (TRANS (@lem5303819 x b s l) (@lem5303826 x b s l)). Qed.
Lemma lem5303830 (s : real -> Prop) (l : real) : (term307 s l) = (term307 s l).
Proof. exact (eq_refl (term307 s l)). Qed.
Lemma lem5303831 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term704 x b s l) = (term719 x b s l).
Proof. exact (MK_COMB (@lem5303830 s l) (@lem5303827 x b s l)). Qed.
Lemma lem5303838 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term719 x b s l) = (term720 x b s l).
Proof. exact (@lem19490 (term721 x b s l) (has_sup s l) (term722 x b s l)). Qed.
Lemma lem5303839 (x : type1019) (b : real) (s : real -> Prop) (l : real) : (term704 x b s l) = (term720 x b s l).
Proof. exact (TRANS (@lem5303831 x b s l) (@lem5303838 x b s l)). Qed.
Lemma lem5303840 (x : type1019) (s : real -> Prop) (l : real) : (term706 x s l) = (term723 x s l).
Proof. exact (fun_ext (fun b : real => @lem5303839 x b s l)). Qed.
Lemma lem5303841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303842 (x : type1019) (s : real -> Prop) (l : real) : (term707 x s l) = (term724 x s l).
Proof. exact (MK_COMB (@lem5303841) (@lem5303840 x s l)). Qed.
Lemma lem5303843 (x : type1019) (s : real -> Prop) : (term708 x s) = (term725 x s).
Proof. exact (fun_ext (fun l : real => @lem5303842 x s l)). Qed.
Lemma lem5303844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303845 (x : type1019) (s : real -> Prop) : (term709 x s) = (term726 x s).
Proof. exact (MK_COMB (@lem5303844) (@lem5303843 x s)). Qed.
Lemma lem5303846 (x : type1019) : (term710 x) = (term727 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5303845 x s)). Qed.
Lemma lem5303847 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5303848 (x : type1019) : (term711 x) = (term728 x).
Proof. exact (MK_COMB (@lem5303847) (@lem5303846 x)). Qed.
Lemma lem5303849 (x : type1019) : (term452 x) = (term728 x).
Proof. exact (TRANS (@lem5303798 x) (@lem5303848 x)). Qed.
Lemma lem5303850 (x : type1019) (b : type1021) (h1 : term573 x b) : term728 x.
Proof. exact (EQ_MP (@lem5303849 x) (@lem5303193 x b h1)). Qed.
Lemma lem5303972 (s : real -> Prop) (l : real) : (term37 s l) = (term37 s l).
Proof. exact (eq_refl (term37 s l)). Qed.
Lemma lem5303973 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (fun_ext (fun l : real => @lem5303972 s l)). Qed.
Lemma lem5303974 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303976 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5303974) (@lem5303973 s)). Qed.
Lemma lem5303977 (s : real -> Prop) (l : real) (h1 : term221 s l) : term40 s.
Proof. exact (EQ_MP (@lem5303976 s) (@lem5303201 s l h1)). Qed.
Lemma lem5303989 (s : real -> Prop) (x : real) (l : real) : (term44 s x l) = (term44 s x l).
Proof. exact (eq_refl (term44 s x l)). Qed.
Lemma lem5303990 (s : real -> Prop) (l : real) : (term54 s l) = (term54 s l).
Proof. exact (fun_ext (fun x : real => @lem5303989 s x l)). Qed.
Lemma lem5303991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5303993 (s : real -> Prop) (l : real) : (term55 s l) = (term55 s l).
Proof. exact (MK_COMB (@lem5303991) (@lem5303990 s l)). Qed.
Lemma lem5303994 (s : real -> Prop) (l : real) (h1 : term221 s l) : term55 s l.
Proof. exact (EQ_MP (@lem5303993 s l) (@lem5303202 s l h1)). Qed.
Lemma lem5304004 (_69474 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term729 b _69474.
Proof. exact (@lem5303451 x b h1 _69474). Qed.
Lemma lem5304005 (b : type1021) (_69474 : real -> Prop) : (term729 b _69474) = (term660 b _69474).
Proof. exact (eq_refl (term729 b _69474)). Qed.
Lemma lem5304006 (_69474 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term660 b _69474.
Proof. exact (EQ_MP (@lem5304005 b _69474) (@lem5304004 _69474 x b h1)). Qed.
Lemma lem5304007 (_69474 : real -> Prop) (_69475 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term730 b _69474 _69475.
Proof. exact (@lem5304006 _69474 x b h1 _69475). Qed.
Lemma lem5304008 (b : type1021) (_69474 : real -> Prop) (_69475 : real) : (term730 b _69474 _69475) = (term658 b _69474 _69475).
Proof. exact (eq_refl (term730 b _69474 _69475)). Qed.
Lemma lem5304009 (_69474 : real -> Prop) (_69475 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term658 b _69474 _69475.
Proof. exact (EQ_MP (@lem5304008 b _69474 _69475) (@lem5304007 _69474 _69475 x b h1)). Qed.
Lemma lem5304010 (_69474 : real -> Prop) (_69475 : real) (_69476 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term731 b _69474 _69475 _69476.
Proof. exact (@lem5304009 _69474 _69475 x b h1 _69476). Qed.
Lemma lem5304011 (_69476 : real) (b : type1021) (_69474 : real -> Prop) (_69475 : real) : (term731 b _69474 _69475 _69476) = (term656 _69476 b _69474 _69475).
Proof. exact (eq_refl (term731 b _69474 _69475 _69476)). Qed.
Lemma lem5304012 (_69476 : real) (_69474 : real -> Prop) (_69475 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term656 _69476 b _69474 _69475.
Proof. exact (EQ_MP (@lem5304011 _69476 b _69474 _69475) (@lem5304010 _69474 _69475 _69476 x b h1)). Qed.
Lemma lem5304022 (_69480 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term729 b _69480.
Proof. exact (@lem5303707 x b h1 _69480). Qed.
Lemma lem5304023 (b : type1021) (_69480 : real -> Prop) : (term729 b _69480) = (term660 b _69480).
Proof. exact (eq_refl (term729 b _69480)). Qed.
Lemma lem5304024 (_69480 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term660 b _69480.
Proof. exact (EQ_MP (@lem5304023 b _69480) (@lem5304022 _69480 x b h1)). Qed.
Lemma lem5304025 (_69480 : real -> Prop) (_69481 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term730 b _69480 _69481.
Proof. exact (@lem5304024 _69480 x b h1 _69481). Qed.
Lemma lem5304026 (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term730 b _69480 _69481) = (term658 b _69480 _69481).
Proof. exact (eq_refl (term730 b _69480 _69481)). Qed.
Lemma lem5304027 (_69480 : real -> Prop) (_69481 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term658 b _69480 _69481.
Proof. exact (EQ_MP (@lem5304026 b _69480 _69481) (@lem5304025 _69480 _69481 x b h1)). Qed.
Lemma lem5304028 (_69480 : real -> Prop) (_69481 : real) (_69482 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term731 b _69480 _69481 _69482.
Proof. exact (@lem5304027 _69480 _69481 x b h1 _69482). Qed.
Lemma lem5304029 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term731 b _69480 _69481 _69482) = (term656 _69482 b _69480 _69481).
Proof. exact (eq_refl (term731 b _69480 _69481 _69482)). Qed.
Lemma lem5304030 (_69482 : real) (_69480 : real -> Prop) (_69481 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term656 _69482 b _69480 _69481.
Proof. exact (EQ_MP (@lem5304029 _69482 b _69480 _69481) (@lem5304028 _69480 _69481 _69482 x b h1)). Qed.
Lemma lem5304031 (_69483 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term732 s x' _69483.
Proof. exact (@lem5303722 s x' h1 _69483). Qed.
Lemma lem5304032 (s : real -> Prop) (x' : real -> real) (_69483 : real) : (term732 s x' _69483) = (term133 s x' _69483).
Proof. exact (eq_refl (term732 s x' _69483)). Qed.
Lemma lem5304033 (_69483 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term133 s x' _69483.
Proof. exact (EQ_MP (@lem5304032 s x' _69483) (@lem5304031 _69483 s x' h1)). Qed.
Lemma lem5304034 (_69484 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term733 x _69484.
Proof. exact (@lem5303850 x b h1 _69484). Qed.
Lemma lem5304035 (x : type1019) (_69484 : real -> Prop) : (term733 x _69484) = (term726 x _69484).
Proof. exact (eq_refl (term733 x _69484)). Qed.
Lemma lem5304036 (_69484 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term726 x _69484.
Proof. exact (EQ_MP (@lem5304035 x _69484) (@lem5304034 _69484 x b h1)). Qed.
Lemma lem5304037 (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term734 x _69484 _69485.
Proof. exact (@lem5304036 _69484 x b h1 _69485). Qed.
Lemma lem5304038 (x : type1019) (_69484 : real -> Prop) (_69485 : real) : (term734 x _69484 _69485) = (term724 x _69484 _69485).
Proof. exact (eq_refl (term734 x _69484 _69485)). Qed.
Lemma lem5304039 (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term724 x _69484 _69485.
Proof. exact (EQ_MP (@lem5304038 x _69484 _69485) (@lem5304037 _69484 _69485 x b h1)). Qed.
Lemma lem5304040 (_69484 : real -> Prop) (_69485 : real) (_69486 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term735 x _69484 _69485 _69486.
Proof. exact (@lem5304039 _69484 _69485 x b h1 _69486). Qed.
Lemma lem5304041 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term735 x _69484 _69485 _69486) = (term720 x _69486 _69484 _69485).
Proof. exact (eq_refl (term735 x _69484 _69485 _69486)). Qed.
Lemma lem5304042 (_69486 : real) (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term720 x _69486 _69484 _69485.
Proof. exact (EQ_MP (@lem5304041 x _69486 _69484 _69485) (@lem5304040 _69484 _69485 _69486 x b h1)). Qed.
Lemma lem5304052 (_69490 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term736 s _69490.
Proof. exact (@lem5303977 s l h1 _69490). Qed.
Lemma lem5304053 (s : real -> Prop) (_69490 : real) : (term736 s _69490) = (term37 s _69490).
Proof. exact (eq_refl (term736 s _69490)). Qed.
Lemma lem5304055 (_69491 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term737 s l _69491.
Proof. exact (@lem5303994 s l h1 _69491). Qed.
Lemma lem5304056 (s : real -> Prop) (_69491 : real) (l : real) : (term737 s l _69491) = (term44 s _69491 l).
Proof. exact (eq_refl (term737 s l _69491)). Qed.
Lemma lem5304066 (_69482 : real) (_69480 : real -> Prop) (_69481 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term654 _69482 b _69480 _69481.
Proof. exact (proj2 (@lem5304030 _69482 _69480 _69481 x b h1)). Qed.
Lemma lem5304079 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : has_sup s l.
Proof. exact (proj1 (@lem5303194 l s x' h1)). Qed.
Lemma lem5304081 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5304137 (_69483 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term738 x' _69483.
Proof. exact (proj2 (@lem5304033 _69483 s x' h1)). Qed.
Lemma lem5304153 (_69482 : real) (_69480 : real -> Prop) (_69481 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term739 _69482 b _69480 _69481.
Proof. exact (proj1 (@lem5304066 _69482 _69480 _69481 x b h1)). Qed.
Lemma lem5304191 (s : real -> Prop) (l : real) (h1 : term221 s l) : term70 s.
Proof. exact (proj1 (@lem5303200 s l h1)). Qed.
Lemma lem5304197 (_69491 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term44 s _69491 l.
Proof. exact (EQ_MP (@lem5304056 s _69491 l) (@lem5304055 _69491 s l h1)). Qed.
Lemma lem5304233 (_69486 : real) (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term740 x _69486 _69484 _69485.
Proof. exact (proj1 (@lem5304042 _69486 _69484 _69485 x b h1)). Qed.
Lemma lem5304247 (_69486 : real) (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term741 x _69486 _69484 _69485.
Proof. exact (proj2 (@lem5304042 _69486 _69484 _69485 x b h1)). Qed.
Lemma lem5304262 (l : real) : (term742 l) = (term742 l).
Proof. exact (eq_refl (term742 l)). Qed.
Lemma lem5304263 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term743 l s) = (term744 l).
Proof. exact (MK_COMB (@lem5304262 l) (@lem5304081 s h1)). Qed.
Lemma lem5304264 (l : real) : (term744 l) = (has_sup (@EMPTY real) l).
Proof. exact (eq_refl (term744 l)). Qed.
Lemma lem5304265 (l : real) (s : real -> Prop) : (term745 l s) = (term745 l s).
Proof. exact (eq_refl (term745 l s)). Qed.
Lemma lem5304266 (s : real -> Prop) (l : real) : ((term743 l s) = (term744 l)) = ((term743 l s) = (has_sup (@EMPTY real) l)).
Proof. exact (MK_COMB (@lem5304265 l s) (@lem5304264 l)). Qed.
Lemma lem5304267 (s : real -> Prop) (l : real) : (term743 l s) = (has_sup s l).
Proof. exact (eq_refl (term743 l s)). Qed.
Lemma lem5304268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5304269 (s : real -> Prop) (l : real) : (term745 l s) = (term22 s l).
Proof. exact (MK_COMB (@lem5304268) (@lem5304267 s l)). Qed.
Lemma lem5304270 (l : real) : (has_sup (@EMPTY real) l) = (has_sup (@EMPTY real) l).
Proof. exact (eq_refl (has_sup (@EMPTY real) l)). Qed.
Lemma lem5304271 (s : real -> Prop) (l : real) : ((term743 l s) = (has_sup (@EMPTY real) l)) = ((has_sup s l) = (has_sup (@EMPTY real) l)).
Proof. exact (MK_COMB (@lem5304269 s l) (@lem5304270 l)). Qed.
Lemma lem5304272 (s : real -> Prop) (l : real) : ((term743 l s) = (term744 l)) = ((has_sup s l) = (has_sup (@EMPTY real) l)).
Proof. exact (TRANS (@lem5304266 s l) (@lem5304271 s l)). Qed.
Lemma lem5304273 (l : real) (s : real -> Prop) (h1 : s = (@EMPTY real)) : (has_sup s l) = (has_sup (@EMPTY real) l).
Proof. exact (EQ_MP (@lem5304272 s l) (@lem5304263 l s h1)). Qed.
Lemma lem5304288 (_69475 : real) (_69474 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term746 _69475 _69474.
Proof. exact (proj1 (@lem5304012 (@el real) _69474 _69475 x b h1)). Qed.
Lemma lem5304452 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : has_sup (@EMPTY real) l.
Proof. exact (EQ_MP (@lem5304273 l s h2) (@lem5304079 l s x' h1)). Qed.
Lemma lem5304453 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : term747 l.
Proof. exact (fun h0 : term748 l => @lem5304452 l x' s h1 h2). Qed.
Lemma lem5304455 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304456 (l : real) : (term747 l) = (has_sup (@EMPTY real) l).
Proof. exact (@lem5304455 (has_sup (@EMPTY real) l)). Qed.
Lemma lem5304457 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : has_sup (@EMPTY real) l.
Proof. exact (EQ_MP (@lem5304456 l) (@lem5304453 l x' s h1 h2)). Qed.
Lemma lem5304459 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5304460 : (@EMPTY real) = (@EMPTY real).
Proof. exact (@lem5304459 (@EMPTY real)). Qed.
Lemma lem5304461 : term750.
Proof. exact (fun h0 : term751 => @lem5304460). Qed.
Lemma lem5304463 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304464 : term750 = ((@EMPTY real) = (@EMPTY real)).
Proof. exact (@lem5304463 ((@EMPTY real) = (@EMPTY real))). Qed.
Lemma lem5304465 : (@EMPTY real) = (@EMPTY real).
Proof. exact (EQ_MP (@lem5304464) (@lem5304461)). Qed.
Lemma lem5304467 (a : Prop) (b : Prop) : (term752 a b) = (term753 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5304468 (_69475 : real) (_69474 : real -> Prop) : (term746 _69475 _69474) = (term754 _69475 _69474).
Proof. exact (@lem5304467 (has_sup _69474 _69475) (_69474 = (@EMPTY real))). Qed.
Lemma lem5304470 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5304471 (_69475 : real) (_69474 : real -> Prop) : (term754 _69475 _69474) = (term755 _69475 _69474).
Proof. exact (@lem5304470 (term756 _69475 _69474)). Qed.
Lemma lem5304472 (_69475 : real) (_69474 : real -> Prop) : (term746 _69475 _69474) = (term755 _69475 _69474).
Proof. exact (TRANS (@lem5304468 _69475 _69474) (@lem5304471 _69475 _69474)). Qed.
Lemma lem5304474 (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term189 l s x') (h2 : s = (@EMPTY real)) : term757 l.
Proof. exact (conj (@lem5304457 l x' s h1 h2) (@lem5304465)). Qed.
Lemma lem5304476 (_69475 : real) (_69474 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term755 _69475 _69474.
Proof. exact (EQ_MP (@lem5304472 _69475 _69474) (@lem5304288 _69475 _69474 x b h1)). Qed.
Lemma lem5304477 (l : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term758 l.
Proof. exact (@lem5304476 l (@EMPTY real) x b h1). Qed.
Lemma lem5304480 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (@lem5304477 l x b h1 (@lem5304474 l x' s h2 h3)). Qed.
Lemma lem5304481 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : term759.
Proof. exact (fun h0 : ~ False => @lem5304480 x b l x' s h1 h2 h3). Qed.
Lemma lem5304483 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304484 : term759 = False.
Proof. exact (@lem5304483 False). Qed.
Lemma lem5304601 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : has_sup s l.
Proof. exact (proj1 (@lem5303194 l s x' h1)). Qed.
Lemma lem5304602 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : term760 s l.
Proof. exact (fun h0 : term37 s l => @lem5304601 l s x' h1). Qed.
Lemma lem5304604 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304605 (s : real -> Prop) (l : real) : (term760 s l) = (has_sup s l).
Proof. exact (@lem5304604 (has_sup s l)). Qed.
Lemma lem5304606 (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term189 l s x') : has_sup s l.
Proof. exact (EQ_MP (@lem5304605 s l) (@lem5304602 l s x' h1)). Qed.
Lemma lem5304608 (_69483 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term761 x' _69483 s.
Proof. exact (proj1 (@lem5304033 _69483 s x' h1)). Qed.
Lemma lem5304609 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term762 x' b l s.
Proof. exact (@lem5304608 (b s l) s x' h1). Qed.
Lemma lem5304610 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term763 x' b l s.
Proof. exact (fun h0 : term764 x' b l s => @lem5304609 b l s x' h1). Qed.
Lemma lem5304612 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304613 (x' : real -> real) (b : type1021) (l : real) (s : real -> Prop) : (term763 x' b l s) = (term762 x' b l s).
Proof. exact (@lem5304612 (term762 x' b l s)). Qed.
Lemma lem5304614 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term762 x' b l s.
Proof. exact (EQ_MP (@lem5304613 x' b l s) (@lem5304610 b l s x' h1)). Qed.
Lemma lem5304620 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5304621 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term739 _69482 b _69480 _69481) = (term766 _69482 b _69480 _69481).
Proof. exact (@lem5304620 (term767 _69482 _69480) (term37 _69480 _69481) (term768 _69482 b _69480 _69481)). Qed.
Lemma lem5304635 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5304636 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term769 _69482 b _69480 _69481) = (term770 _69482 b _69480 _69481).
Proof. exact (@lem5304635 (term768 _69482 b _69480 _69481) (term37 _69480 _69481)). Qed.
Lemma lem5304642 (_69482 : real) (_69480 : real -> Prop) : (term771 _69482 _69480) = (term771 _69482 _69480).
Proof. exact (eq_refl (term771 _69482 _69480)). Qed.
Lemma lem5304643 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term766 _69482 b _69480 _69481) = (term772 _69482 b _69480 _69481).
Proof. exact (MK_COMB (@lem5304642 _69482 _69480) (@lem5304636 _69482 b _69480 _69481)). Qed.
Lemma lem5304647 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5304648 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : (term772 _69482 b _69480 _69481) = (term773 b _69482 _69480 _69481).
Proof. exact (@lem5304647 (term768 _69482 b _69480 _69481) (term767 _69482 _69480) (term37 _69480 _69481)). Qed.
Lemma lem5304664 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : (term766 _69482 b _69480 _69481) = (term773 b _69482 _69480 _69481).
Proof. exact (TRANS (@lem5304643 _69482 b _69480 _69481) (@lem5304648 b _69482 _69480 _69481)). Qed.
Lemma lem5304665 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : (term739 _69482 b _69480 _69481) = (term773 b _69482 _69480 _69481).
Proof. exact (TRANS (@lem5304621 _69482 b _69480 _69481) (@lem5304664 b _69482 _69480 _69481)). Qed.
Lemma lem5304666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5304667 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : (term774 _69482 b _69480 _69481) = (term775 b _69482 _69480 _69481).
Proof. exact (MK_COMB (@lem5304666) (@lem5304665 b _69482 _69480 _69481)). Qed.
Lemma lem5304681 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5304682 (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : (term776 _69481 _69482 _69480) = (term777 _69482 _69480 _69481).
Proof. exact (@lem5304681 (term767 _69482 _69480) (term37 _69480 _69481)). Qed.
Lemma lem5304688 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term778 _69482 b _69480 _69481) = (term778 _69482 b _69480 _69481).
Proof. exact (eq_refl (term778 _69482 b _69480 _69481)). Qed.
Lemma lem5304689 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : (term779 b _69481 _69482 _69480) = (term773 b _69482 _69480 _69481).
Proof. exact (MK_COMB (@lem5304688 _69482 b _69480 _69481) (@lem5304682 _69482 _69480 _69481)). Qed.
Lemma lem5304700 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : ((term739 _69482 b _69480 _69481) = (term779 b _69481 _69482 _69480)) = ((term773 b _69482 _69480 _69481) = (term773 b _69482 _69480 _69481)).
Proof. exact (MK_COMB (@lem5304667 b _69482 _69480 _69481) (@lem5304689 b _69482 _69480 _69481)). Qed.
Lemma lem5304702 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5304703 (x : Prop) : (x = x) = True.
Proof. exact (@lem5304702 Prop x). Qed.
Lemma lem5304704 (b : type1021) (_69482 : real) (_69480 : real -> Prop) (_69481 : real) : ((term773 b _69482 _69480 _69481) = (term773 b _69482 _69480 _69481)) = True.
Proof. exact (@lem5304703 (term773 b _69482 _69480 _69481)). Qed.
Lemma lem5304705 (b : type1021) (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : ((term739 _69482 b _69480 _69481) = (term779 b _69481 _69482 _69480)) = True.
Proof. exact (TRANS (@lem5304700 b _69482 _69480 _69481) (@lem5304704 b _69482 _69480 _69481)). Qed.
Lemma lem5304706 (b : type1021) (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : True = ((term739 _69482 b _69480 _69481) = (term779 b _69481 _69482 _69480)).
Proof. exact (SYM (@lem5304705 b _69481 _69482 _69480)). Qed.
Lemma lem5304707 (b : type1021) (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : (term739 _69482 b _69480 _69481) = (term779 b _69481 _69482 _69480).
Proof. exact (EQ_MP (@lem5304706 b _69481 _69482 _69480) (@lem0)). Qed.
Lemma lem5304708 (_69481 : real) (_69482 : real) (_69480 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term779 b _69481 _69482 _69480.
Proof. exact (EQ_MP (@lem5304707 b _69481 _69482 _69480) (@lem5304153 _69482 _69480 _69481 x b h1)). Qed.
Lemma lem5304710 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5304711 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term779 b _69481 _69482 _69480) = (term781 _69482 b _69480 _69481).
Proof. exact (@lem5304710 (term776 _69481 _69482 _69480) (term768 _69482 b _69480 _69481)). Qed.
Lemma lem5304713 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5304714 (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : (term784 _69481 _69482 _69480) = (term785 _69481 _69482 _69480).
Proof. exact (@lem5304713 (term37 _69480 _69481) (term767 _69482 _69480)). Qed.
Lemma lem5304716 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5304717 (_69480 : real -> Prop) (_69481 : real) : (term787 _69480 _69481) = (has_sup _69480 _69481).
Proof. exact (@lem5304716 (has_sup _69480 _69481)). Qed.
Lemma lem5304718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5304719 (_69480 : real -> Prop) (_69481 : real) : (term788 _69480 _69481) = (term171 _69480 _69481).
Proof. exact (MK_COMB (@lem5304718) (@lem5304717 _69480 _69481)). Qed.
Lemma lem5304721 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5304722 (_69482 : real) (_69480 : real -> Prop) : (term789 _69482 _69480) = (@IN real _69482 _69480).
Proof. exact (@lem5304721 (@IN real _69482 _69480)). Qed.
Lemma lem5304723 (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : (term785 _69481 _69482 _69480) = (term790 _69481 _69482 _69480).
Proof. exact (MK_COMB (@lem5304719 _69480 _69481) (@lem5304722 _69482 _69480)). Qed.
Lemma lem5304724 (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : (term784 _69481 _69482 _69480) = (term790 _69481 _69482 _69480).
Proof. exact (TRANS (@lem5304714 _69481 _69482 _69480) (@lem5304723 _69481 _69482 _69480)). Qed.
Lemma lem5304725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5304726 (_69481 : real) (_69482 : real) (_69480 : real -> Prop) : (term791 _69481 _69482 _69480) = (term792 _69481 _69482 _69480).
Proof. exact (MK_COMB (@lem5304725) (@lem5304724 _69481 _69482 _69480)). Qed.
Lemma lem5304727 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term768 _69482 b _69480 _69481) = (term768 _69482 b _69480 _69481).
Proof. exact (eq_refl (term768 _69482 b _69480 _69481)). Qed.
Lemma lem5304728 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term781 _69482 b _69480 _69481) = (term793 _69482 b _69480 _69481).
Proof. exact (MK_COMB (@lem5304726 _69481 _69482 _69480) (@lem5304727 _69482 b _69480 _69481)). Qed.
Lemma lem5304729 (_69482 : real) (b : type1021) (_69480 : real -> Prop) (_69481 : real) : (term779 b _69481 _69482 _69480) = (term793 _69482 b _69480 _69481).
Proof. exact (TRANS (@lem5304711 _69482 b _69480 _69481) (@lem5304728 _69482 b _69480 _69481)). Qed.
Lemma lem5304731 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term189 l s x') : term794 x' b l s.
Proof. exact (conj (@lem5304606 l s x' h2) (@lem5304614 b l s x' h1)). Qed.
Lemma lem5304733 (_69482 : real) (_69480 : real -> Prop) (_69481 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term793 _69482 b _69480 _69481.
Proof. exact (EQ_MP (@lem5304729 _69482 b _69480 _69481) (@lem5304708 _69481 _69482 _69480 x b h1)). Qed.
Lemma lem5304734 (x' : real -> real) (s : real -> Prop) (l : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term795 x' b s l.
Proof. exact (@lem5304733 (term796 x' b s l) s l x b h1). Qed.
Lemma lem5304737 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term797 x' b s l.
Proof. exact (@lem5304734 x' s l x b h2 (@lem5304731 b l s x' h1 h3)). Qed.
Lemma lem5304738 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term798 x' b s l.
Proof. exact (fun h0 : term799 x' b s l => @lem5304737 x b l s x' h1 h2 h3). Qed.
Lemma lem5304740 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304741 (x' : real -> real) (b : type1021) (s : real -> Prop) (l : real) : (term798 x' b s l) = (term797 x' b s l).
Proof. exact (@lem5304740 (term797 x' b s l)). Qed.
Lemma lem5304742 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term797 x' b s l.
Proof. exact (EQ_MP (@lem5304741 x' b s l) (@lem5304738 x b l s x' h1 h2 h3)). Qed.
Lemma lem5304745 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5304747 (x' : real -> real) (_69483 : real) : (term738 x' _69483) = (term800 x' _69483).
Proof. exact (@lem5304745 (term801 x' _69483)). Qed.
Lemma lem5304750 (_69483 : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term800 x' _69483.
Proof. exact (EQ_MP (@lem5304747 x' _69483) (@lem5304137 _69483 s x' h1)). Qed.
Lemma lem5304751 (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') : term802 x' b s l.
Proof. exact (@lem5304750 (b s l) s x' h1). Qed.
Lemma lem5304754 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : False.
Proof. exact (@lem5304751 b l s x' h1 (@lem5304742 x b l s x' h1 h2 h3)). Qed.
Lemma lem5304755 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : term759.
Proof. exact (fun h0 : ~ False => @lem5304754 x b l s x' h1 h2 h3). Qed.
Lemma lem5304757 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304758 : term759 = False.
Proof. exact (@lem5304757 False). Qed.
Lemma lem5304759 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : False.
Proof. exact (EQ_MP (@lem5304758) (@lem5304755 x b l s x' h1 h2 h3)). Qed.
Lemma lem5304867 (_69490 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term37 s _69490.
Proof. exact (EQ_MP (@lem5304053 s _69490) (@lem5304052 _69490 s l h1)). Qed.
Lemma lem5304868 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (@lem5304867 (sup s) s l h1). Qed.
Lemma lem5304869 (s : real -> Prop) (l : real) (h1 : term221 s l) : term804 s.
Proof. exact (fun h0 : term805 s => @lem5304868 s l h1). Qed.
Lemma lem5304871 (p : Prop) : (term806 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5304872 (s : real -> Prop) : (term804 s) = (term803 s).
Proof. exact (@lem5304871 (term805 s)). Qed.
Lemma lem5304873 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (EQ_MP (@lem5304872 s) (@lem5304869 s l h1)). Qed.
Lemma lem5304875 (_69490 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term37 s _69490.
Proof. exact (EQ_MP (@lem5304053 s _69490) (@lem5304052 _69490 s l h1)). Qed.
Lemma lem5304876 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (@lem5304875 (sup s) s l h1). Qed.
Lemma lem5304877 (s : real -> Prop) (l : real) (h1 : term221 s l) : term804 s.
Proof. exact (fun h0 : term805 s => @lem5304876 s l h1). Qed.
Lemma lem5304879 (p : Prop) : (term806 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5304880 (s : real -> Prop) : (term804 s) = (term803 s).
Proof. exact (@lem5304879 (term805 s)). Qed.
Lemma lem5304881 (s : real -> Prop) (l : real) (h1 : term221 s l) : term803 s.
Proof. exact (EQ_MP (@lem5304880 s) (@lem5304877 s l h1)). Qed.
Lemma lem5304884 (s : real -> Prop) (h1 : term70 s) : term70 s.
Proof. exact (h1). Qed.
Lemma lem5304885 (s : real -> Prop) (h1 : term70 s) : term807 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5304884 s h1). Qed.
Lemma lem5304887 (p : Prop) : (term806 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5304888 (s : real -> Prop) : (term807 s) = (term70 s).
Proof. exact (@lem5304887 (s = (@EMPTY real))). Qed.
Lemma lem5304889 (s : real -> Prop) (h1 : term70 s) : term70 s.
Proof. exact (EQ_MP (@lem5304888 s) (@lem5304885 s h1)). Qed.
Lemma lem5304891 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5304892 (s : real -> Prop) : (sup s) = (sup s).
Proof. exact (@lem5304891 (sup s)). Qed.
Lemma lem5304893 (s : real -> Prop) : term808 s.
Proof. exact (fun h0 : term809 s => @lem5304892 s). Qed.
Lemma lem5304895 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5304896 (s : real -> Prop) : (term808 s) = ((sup s) = (sup s)).
Proof. exact (@lem5304895 ((sup s) = (sup s))). Qed.
Lemma lem5304897 (s : real -> Prop) : (sup s) = (sup s).
Proof. exact (EQ_MP (@lem5304896 s) (@lem5304893 s)). Qed.
Lemma lem5304903 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5304904 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term740 x _69486 _69484 _69485) = (term810 x _69486 _69484 _69485).
Proof. exact (@lem5304903 (_69484 = (@EMPTY real)) (has_sup _69484 _69485) (term717 x _69486 _69484 _69485)). Qed.
Lemma lem5304920 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5304921 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term811 x _69486 _69484 _69485) = (term812 x _69486 _69484 _69485).
Proof. exact (@lem5304920 (term713 x _69485 _69486 _69484) (has_sup _69484 _69485) (term292 _69484 _69485)). Qed.
Lemma lem5304939 (_69484 : real -> Prop) : (term66 _69484) = (term66 _69484).
Proof. exact (eq_refl (term66 _69484)). Qed.
Lemma lem5304940 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term810 x _69486 _69484 _69485) = (term813 x _69486 _69484 _69485).
Proof. exact (MK_COMB (@lem5304939 _69484) (@lem5304921 x _69486 _69484 _69485)). Qed.
Lemma lem5304951 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term740 x _69486 _69484 _69485) = (term813 x _69486 _69484 _69485).
Proof. exact (TRANS (@lem5304904 x _69486 _69484 _69485) (@lem5304940 x _69486 _69484 _69485)). Qed.
Lemma lem5304952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5304953 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term814 x _69486 _69484 _69485) = (term815 x _69486 _69484 _69485).
Proof. exact (MK_COMB (@lem5304952) (@lem5304951 x _69486 _69484 _69485)). Qed.
Lemma lem5304967 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5304968 (_69484 : real -> Prop) (_69485 : real) : (term816 _69484 _69485) = (term817 _69484 _69485).
Proof. exact (@lem5304967 (_69484 = (@EMPTY real)) (has_sup _69484 _69485) (term292 _69484 _69485)). Qed.
Lemma lem5304988 (x : type1019) (_69485 : real) (_69486 : real) (_69484 : real -> Prop) : (term818 x _69485 _69486 _69484) = (term818 x _69485 _69486 _69484).
Proof. exact (eq_refl (term818 x _69485 _69486 _69484)). Qed.
Lemma lem5304989 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term819 x _69486 _69484 _69485) = (term820 x _69486 _69484 _69485).
Proof. exact (MK_COMB (@lem5304988 x _69485 _69486 _69484) (@lem5304968 _69484 _69485)). Qed.
Lemma lem5304993 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5304994 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term820 x _69486 _69484 _69485) = (term813 x _69486 _69484 _69485).
Proof. exact (@lem5304993 (_69484 = (@EMPTY real)) (term713 x _69485 _69486 _69484) (term821 _69484 _69485)). Qed.
Lemma lem5305024 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term819 x _69486 _69484 _69485) = (term813 x _69486 _69484 _69485).
Proof. exact (TRANS (@lem5304989 x _69486 _69484 _69485) (@lem5304994 x _69486 _69484 _69485)). Qed.
Lemma lem5305025 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : ((term740 x _69486 _69484 _69485) = (term819 x _69486 _69484 _69485)) = ((term813 x _69486 _69484 _69485) = (term813 x _69486 _69484 _69485)).
Proof. exact (MK_COMB (@lem5304953 x _69486 _69484 _69485) (@lem5305024 x _69486 _69484 _69485)). Qed.
Lemma lem5305027 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5305028 (x : Prop) : (x = x) = True.
Proof. exact (@lem5305027 Prop x). Qed.
Lemma lem5305029 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : ((term813 x _69486 _69484 _69485) = (term813 x _69486 _69484 _69485)) = True.
Proof. exact (@lem5305028 (term813 x _69486 _69484 _69485)). Qed.
Lemma lem5305030 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : ((term740 x _69486 _69484 _69485) = (term819 x _69486 _69484 _69485)) = True.
Proof. exact (TRANS (@lem5305025 x _69486 _69484 _69485) (@lem5305029 x _69486 _69484 _69485)). Qed.
Lemma lem5305031 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : True = ((term740 x _69486 _69484 _69485) = (term819 x _69486 _69484 _69485)).
Proof. exact (SYM (@lem5305030 x _69486 _69484 _69485)). Qed.
Lemma lem5305032 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term740 x _69486 _69484 _69485) = (term819 x _69486 _69484 _69485).
Proof. exact (EQ_MP (@lem5305031 x _69486 _69484 _69485) (@lem0)). Qed.
Lemma lem5305033 (_69486 : real) (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term819 x _69486 _69484 _69485.
Proof. exact (EQ_MP (@lem5305032 x _69486 _69484 _69485) (@lem5304233 _69486 _69484 _69485 x b h1)). Qed.
Lemma lem5305035 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5305036 (x : type1019) (_69485 : real) (_69486 : real) (_69484 : real -> Prop) : (term819 x _69486 _69484 _69485) = (term822 x _69485 _69486 _69484).
Proof. exact (@lem5305035 (term816 _69484 _69485) (term713 x _69485 _69486 _69484)). Qed.
Lemma lem5305038 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5305039 (_69484 : real -> Prop) (_69485 : real) : (term823 _69484 _69485) = (term824 _69484 _69485).
Proof. exact (@lem5305038 (has_sup _69484 _69485) (term825 _69484 _69485)). Qed.
Lemma lem5305041 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5305042 (_69484 : real -> Prop) (_69485 : real) : (term826 _69484 _69485) = (term827 _69484 _69485).
Proof. exact (@lem5305041 (_69484 = (@EMPTY real)) (term292 _69484 _69485)). Qed.
Lemma lem5305044 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5305045 (_69484 : real -> Prop) (_69485 : real) : (term828 _69484 _69485) = ((sup _69484) = _69485).
Proof. exact (@lem5305044 ((sup _69484) = _69485)). Qed.
Lemma lem5305046 (_69484 : real -> Prop) : (term20 _69484) = (term20 _69484).
Proof. exact (eq_refl (term20 _69484)). Qed.
Lemma lem5305047 (_69484 : real -> Prop) (_69485 : real) : (term827 _69484 _69485) = (term829 _69484 _69485).
Proof. exact (MK_COMB (@lem5305046 _69484) (@lem5305045 _69484 _69485)). Qed.
Lemma lem5305048 (_69484 : real -> Prop) (_69485 : real) : (term826 _69484 _69485) = (term829 _69484 _69485).
Proof. exact (TRANS (@lem5305042 _69484 _69485) (@lem5305047 _69484 _69485)). Qed.
Lemma lem5305049 (_69484 : real -> Prop) (_69485 : real) : (term830 _69484 _69485) = (term830 _69484 _69485).
Proof. exact (eq_refl (term830 _69484 _69485)). Qed.
Lemma lem5305050 (_69484 : real -> Prop) (_69485 : real) : (term824 _69484 _69485) = (term831 _69484 _69485).
Proof. exact (MK_COMB (@lem5305049 _69484 _69485) (@lem5305048 _69484 _69485)). Qed.
Lemma lem5305051 (_69484 : real -> Prop) (_69485 : real) : (term823 _69484 _69485) = (term831 _69484 _69485).
Proof. exact (TRANS (@lem5305039 _69484 _69485) (@lem5305050 _69484 _69485)). Qed.
Lemma lem5305052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305053 (_69484 : real -> Prop) (_69485 : real) : (term832 _69484 _69485) = (term833 _69484 _69485).
Proof. exact (MK_COMB (@lem5305052) (@lem5305051 _69484 _69485)). Qed.
Lemma lem5305054 (x : type1019) (_69485 : real) (_69486 : real) (_69484 : real -> Prop) : (term713 x _69485 _69486 _69484) = (term713 x _69485 _69486 _69484).
Proof. exact (eq_refl (term713 x _69485 _69486 _69484)). Qed.
Lemma lem5305055 (x : type1019) (_69485 : real) (_69486 : real) (_69484 : real -> Prop) : (term822 x _69485 _69486 _69484) = (term834 x _69485 _69486 _69484).
Proof. exact (MK_COMB (@lem5305053 _69484 _69485) (@lem5305054 x _69485 _69486 _69484)). Qed.
Lemma lem5305056 (x : type1019) (_69485 : real) (_69486 : real) (_69484 : real -> Prop) : (term819 x _69486 _69484 _69485) = (term834 x _69485 _69486 _69484).
Proof. exact (TRANS (@lem5305036 x _69485 _69486 _69484) (@lem5305055 x _69485 _69486 _69484)). Qed.
Lemma lem5305058 (s : real -> Prop) (h1 : term70 s) : term835 s.
Proof. exact (conj (@lem5304889 s h1) (@lem5304897 s)). Qed.
Lemma lem5305059 (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term221 s l) : term836 s.
Proof. exact (conj (@lem5304881 s l h2) (@lem5305058 s h1)). Qed.
Lemma lem5305061 (_69485 : real) (_69486 : real) (_69484 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term834 x _69485 _69486 _69484.
Proof. exact (EQ_MP (@lem5305056 x _69485 _69486 _69484) (@lem5305033 _69486 _69484 _69485 x b h1)). Qed.
Lemma lem5305062 (_69486 : real) (s : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term837 x _69486 s.
Proof. exact (@lem5305061 (sup s) _69486 s x b h1). Qed.
Lemma lem5305065 (_69486 : real) (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term838 x _69486 s.
Proof. exact (@lem5305062 _69486 s x b h2 (@lem5305059 s l h1 h3)). Qed.
Lemma lem5305066 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term838 x l s.
Proof. exact (@lem5305065 l x b s l h1 h2 h3). Qed.
Lemma lem5305067 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term839 x l s.
Proof. exact (fun h0 : term840 x l s => @lem5305066 x b s l h1 h2 h3). Qed.
Lemma lem5305069 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5305070 (x : type1019) (l : real) (s : real -> Prop) : (term839 x l s) = (term838 x l s).
Proof. exact (@lem5305069 (term838 x l s)). Qed.
Lemma lem5305071 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term838 x l s.
Proof. exact (EQ_MP (@lem5305070 x l s) (@lem5305067 x b s l h1 h2 h3)). Qed.
Lemma lem5305077 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5305078 (l : real) (_69491 : real) (s : real -> Prop) : (term44 s _69491 l) = (term841 l _69491 s).
Proof. exact (@lem5305077 (real_le _69491 l) (term767 _69491 s)). Qed.
Lemma lem5305084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5305085 (l : real) (_69491 : real) (s : real -> Prop) : (term842 s _69491 l) = (term843 l _69491 s).
Proof. exact (MK_COMB (@lem5305084) (@lem5305078 l _69491 s)). Qed.
Lemma lem5305091 (l : real) (_69491 : real) (s : real -> Prop) : (term841 l _69491 s) = (term841 l _69491 s).
Proof. exact (eq_refl (term841 l _69491 s)). Qed.
Lemma lem5305092 (l : real) (_69491 : real) (s : real -> Prop) : ((term44 s _69491 l) = (term841 l _69491 s)) = ((term841 l _69491 s) = (term841 l _69491 s)).
Proof. exact (MK_COMB (@lem5305085 l _69491 s) (@lem5305091 l _69491 s)). Qed.
Lemma lem5305094 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5305095 (x : Prop) : (x = x) = True.
Proof. exact (@lem5305094 Prop x). Qed.
Lemma lem5305096 (l : real) (_69491 : real) (s : real -> Prop) : ((term841 l _69491 s) = (term841 l _69491 s)) = True.
Proof. exact (@lem5305095 (term841 l _69491 s)). Qed.
Lemma lem5305097 (l : real) (_69491 : real) (s : real -> Prop) : ((term44 s _69491 l) = (term841 l _69491 s)) = True.
Proof. exact (TRANS (@lem5305092 l _69491 s) (@lem5305096 l _69491 s)). Qed.
Lemma lem5305098 (l : real) (_69491 : real) (s : real -> Prop) : True = ((term44 s _69491 l) = (term841 l _69491 s)).
Proof. exact (SYM (@lem5305097 l _69491 s)). Qed.
Lemma lem5305099 (l : real) (_69491 : real) (s : real -> Prop) : (term44 s _69491 l) = (term841 l _69491 s).
Proof. exact (EQ_MP (@lem5305098 l _69491 s) (@lem0)). Qed.
Lemma lem5305100 (_69491 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term841 l _69491 s.
Proof. exact (EQ_MP (@lem5305099 l _69491 s) (@lem5304197 _69491 s l h1)). Qed.
Lemma lem5305102 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5305103 (s : real -> Prop) (_69491 : real) (l : real) : (term841 l _69491 s) = (term844 s _69491 l).
Proof. exact (@lem5305102 (term767 _69491 s) (real_le _69491 l)). Qed.
Lemma lem5305105 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5305106 (_69491 : real) (s : real -> Prop) : (term789 _69491 s) = (@IN real _69491 s).
Proof. exact (@lem5305105 (@IN real _69491 s)). Qed.
Lemma lem5305107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305108 (_69491 : real) (s : real -> Prop) : (term845 _69491 s) = (term846 _69491 s).
Proof. exact (MK_COMB (@lem5305107) (@lem5305106 _69491 s)). Qed.
Lemma lem5305109 (_69491 : real) (l : real) : (real_le _69491 l) = (real_le _69491 l).
Proof. exact (eq_refl (real_le _69491 l)). Qed.
Lemma lem5305110 (s : real -> Prop) (_69491 : real) (l : real) : (term844 s _69491 l) = (term13 s _69491 l).
Proof. exact (MK_COMB (@lem5305108 _69491 s) (@lem5305109 _69491 l)). Qed.
Lemma lem5305111 (s : real -> Prop) (_69491 : real) (l : real) : (term841 l _69491 s) = (term13 s _69491 l).
Proof. exact (TRANS (@lem5305103 s _69491 l) (@lem5305110 s _69491 l)). Qed.
Lemma lem5305114 (_69491 : real) (s : real -> Prop) (l : real) (h1 : term221 s l) : term13 s _69491 l.
Proof. exact (EQ_MP (@lem5305111 s _69491 l) (@lem5305100 _69491 s l h1)). Qed.
Lemma lem5305115 (x : type1019) (s : real -> Prop) (l : real) (h1 : term221 s l) : term847 x s l.
Proof. exact (@lem5305114 (term848 x s l) s l h1). Qed.
Lemma lem5305118 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term849 x s l.
Proof. exact (@lem5305115 x s l h3 (@lem5305071 x b s l h1 h2 h3)). Qed.
Lemma lem5305119 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term850 x s l.
Proof. exact (fun h0 : term851 x s l => @lem5305118 x b s l h1 h2 h3). Qed.
Lemma lem5305121 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5305122 (x : type1019) (s : real -> Prop) (l : real) : (term850 x s l) = (term849 x s l).
Proof. exact (@lem5305121 (term849 x s l)). Qed.
Lemma lem5305123 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term849 x s l.
Proof. exact (EQ_MP (@lem5305122 x s l) (@lem5305119 x b s l h1 h2 h3)). Qed.
Lemma lem5305125 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem5305126 (s : real -> Prop) : (sup s) = (sup s).
Proof. exact (@lem5305125 (sup s)). Qed.
Lemma lem5305127 (s : real -> Prop) : term808 s.
Proof. exact (fun h0 : term809 s => @lem5305126 s). Qed.
Lemma lem5305129 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5305130 (s : real -> Prop) : (term808 s) = ((sup s) = (sup s)).
Proof. exact (@lem5305129 ((sup s) = (sup s))). Qed.
Lemma lem5305131 (s : real -> Prop) : (sup s) = (sup s).
Proof. exact (EQ_MP (@lem5305130 s) (@lem5305127 s)). Qed.
Lemma lem5305137 (q : Prop) (p : Prop) (r : Prop) : (term765 p q r) = (term765 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5305138 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term741 x _69486 _69484 _69485) = (term852 x _69486 _69484 _69485).
Proof. exact (@lem5305137 (_69484 = (@EMPTY real)) (has_sup _69484 _69485) (term718 x _69486 _69484 _69485)). Qed.
Lemma lem5305164 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5305165 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term718 x _69486 _69484 _69485) = (term853 x _69484 _69485 _69486).
Proof. exact (@lem5305164 (term292 _69484 _69485) (term714 x _69484 _69485 _69486)). Qed.
Lemma lem5305173 (_69484 : real -> Prop) (_69485 : real) : (term307 _69484 _69485) = (term307 _69484 _69485).
Proof. exact (eq_refl (term307 _69484 _69485)). Qed.
Lemma lem5305174 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term854 x _69486 _69484 _69485) = (term855 x _69484 _69485 _69486).
Proof. exact (MK_COMB (@lem5305173 _69484 _69485) (@lem5305165 x _69484 _69485 _69486)). Qed.
Lemma lem5305185 (_69484 : real -> Prop) : (term66 _69484) = (term66 _69484).
Proof. exact (eq_refl (term66 _69484)). Qed.
Lemma lem5305186 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term852 x _69486 _69484 _69485) = (term856 x _69484 _69485 _69486).
Proof. exact (MK_COMB (@lem5305185 _69484) (@lem5305174 x _69484 _69485 _69486)). Qed.
Lemma lem5305197 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term741 x _69486 _69484 _69485) = (term856 x _69484 _69485 _69486).
Proof. exact (TRANS (@lem5305138 x _69486 _69484 _69485) (@lem5305186 x _69484 _69485 _69486)). Qed.
Lemma lem5305198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5305199 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term857 x _69486 _69484 _69485) = (term858 x _69484 _69485 _69486).
Proof. exact (MK_COMB (@lem5305198) (@lem5305197 x _69484 _69485 _69486)). Qed.
Lemma lem5305225 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5305226 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term718 x _69486 _69484 _69485) = (term853 x _69484 _69485 _69486).
Proof. exact (@lem5305225 (term292 _69484 _69485) (term714 x _69484 _69485 _69486)). Qed.
Lemma lem5305234 (_69484 : real -> Prop) (_69485 : real) : (term307 _69484 _69485) = (term307 _69484 _69485).
Proof. exact (eq_refl (term307 _69484 _69485)). Qed.
Lemma lem5305235 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term854 x _69486 _69484 _69485) = (term855 x _69484 _69485 _69486).
Proof. exact (MK_COMB (@lem5305234 _69484 _69485) (@lem5305226 x _69484 _69485 _69486)). Qed.
Lemma lem5305246 (_69484 : real -> Prop) : (term66 _69484) = (term66 _69484).
Proof. exact (eq_refl (term66 _69484)). Qed.
Lemma lem5305247 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term852 x _69486 _69484 _69485) = (term856 x _69484 _69485 _69486).
Proof. exact (MK_COMB (@lem5305246 _69484) (@lem5305235 x _69484 _69485 _69486)). Qed.
Lemma lem5305258 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : ((term741 x _69486 _69484 _69485) = (term852 x _69486 _69484 _69485)) = ((term856 x _69484 _69485 _69486) = (term856 x _69484 _69485 _69486)).
Proof. exact (MK_COMB (@lem5305199 x _69484 _69485 _69486) (@lem5305247 x _69484 _69485 _69486)). Qed.
Lemma lem5305260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5305261 (x : Prop) : (x = x) = True.
Proof. exact (@lem5305260 Prop x). Qed.
Lemma lem5305262 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : ((term856 x _69484 _69485 _69486) = (term856 x _69484 _69485 _69486)) = True.
Proof. exact (@lem5305261 (term856 x _69484 _69485 _69486)). Qed.
Lemma lem5305263 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : ((term741 x _69486 _69484 _69485) = (term852 x _69486 _69484 _69485)) = True.
Proof. exact (TRANS (@lem5305258 x _69484 _69485 _69486) (@lem5305262 x _69484 _69485 _69486)). Qed.
Lemma lem5305264 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : True = ((term741 x _69486 _69484 _69485) = (term852 x _69486 _69484 _69485)).
Proof. exact (SYM (@lem5305263 x _69486 _69484 _69485)). Qed.
Lemma lem5305265 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term741 x _69486 _69484 _69485) = (term852 x _69486 _69484 _69485).
Proof. exact (EQ_MP (@lem5305264 x _69486 _69484 _69485) (@lem0)). Qed.
Lemma lem5305266 (_69486 : real) (_69484 : real -> Prop) (_69485 : real) (x : type1019) (b : type1021) (h1 : term573 x b) : term852 x _69486 _69484 _69485.
Proof. exact (EQ_MP (@lem5305265 x _69486 _69484 _69485) (@lem5304247 _69486 _69484 _69485 x b h1)). Qed.
Lemma lem5305268 (b : Prop) (a : Prop) : (a \/ b) = (term780 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5305269 (x : type1019) (_69486 : real) (_69485 : real) (_69484 : real -> Prop) : (term852 x _69486 _69484 _69485) = (term859 x _69486 _69485 _69484).
Proof. exact (@lem5305268 (term854 x _69486 _69484 _69485) (_69484 = (@EMPTY real))). Qed.
Lemma lem5305271 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5305272 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term860 x _69486 _69484 _69485) = (term861 x _69486 _69484 _69485).
Proof. exact (@lem5305271 (has_sup _69484 _69485) (term718 x _69486 _69484 _69485)). Qed.
Lemma lem5305274 (a : Prop) (b : Prop) : (term782 a b) = (term783 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5305275 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term862 x _69486 _69484 _69485) = (term863 x _69486 _69484 _69485).
Proof. exact (@lem5305274 (term714 x _69484 _69485 _69486) (term292 _69484 _69485)). Qed.
Lemma lem5305277 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5305278 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term864 x _69484 _69485 _69486) = (term865 x _69484 _69485 _69486).
Proof. exact (@lem5305277 (term865 x _69484 _69485 _69486)). Qed.
Lemma lem5305279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305280 (x : type1019) (_69484 : real -> Prop) (_69485 : real) (_69486 : real) : (term866 x _69484 _69485 _69486) = (term867 x _69484 _69485 _69486).
Proof. exact (MK_COMB (@lem5305279) (@lem5305278 x _69484 _69485 _69486)). Qed.
Lemma lem5305282 (a : Prop) : (term786 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5305283 (_69484 : real -> Prop) (_69485 : real) : (term828 _69484 _69485) = ((sup _69484) = _69485).
Proof. exact (@lem5305282 ((sup _69484) = _69485)). Qed.
Lemma lem5305284 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term863 x _69486 _69484 _69485) = (term868 x _69486 _69484 _69485).
Proof. exact (MK_COMB (@lem5305280 x _69484 _69485 _69486) (@lem5305283 _69484 _69485)). Qed.
Lemma lem5305285 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term862 x _69486 _69484 _69485) = (term868 x _69486 _69484 _69485).
Proof. exact (TRANS (@lem5305275 x _69486 _69484 _69485) (@lem5305284 x _69486 _69484 _69485)). Qed.
Lemma lem5305286 (_69484 : real -> Prop) (_69485 : real) : (term830 _69484 _69485) = (term830 _69484 _69485).
Proof. exact (eq_refl (term830 _69484 _69485)). Qed.
Lemma lem5305287 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term861 x _69486 _69484 _69485) = (term869 x _69486 _69484 _69485).
Proof. exact (MK_COMB (@lem5305286 _69484 _69485) (@lem5305285 x _69486 _69484 _69485)). Qed.
Lemma lem5305288 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term860 x _69486 _69484 _69485) = (term869 x _69486 _69484 _69485).
Proof. exact (TRANS (@lem5305272 x _69486 _69484 _69485) (@lem5305287 x _69486 _69484 _69485)). Qed.
Lemma lem5305289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305290 (x : type1019) (_69486 : real) (_69484 : real -> Prop) (_69485 : real) : (term870 x _69486 _69484 _69485) = (term871 x _69486 _69484 _69485).
Proof. exact (MK_COMB (@lem5305289) (@lem5305288 x _69486 _69484 _69485)). Qed.
Lemma lem5305291 (_69484 : real -> Prop) : (_69484 = (@EMPTY real)) = (_69484 = (@EMPTY real)).
Proof. exact (eq_refl (_69484 = (@EMPTY real))). Qed.
Lemma lem5305292 (x : type1019) (_69486 : real) (_69485 : real) (_69484 : real -> Prop) : (term859 x _69486 _69485 _69484) = (term872 x _69486 _69485 _69484).
Proof. exact (MK_COMB (@lem5305290 x _69486 _69484 _69485) (@lem5305291 _69484)). Qed.
Lemma lem5305293 (x : type1019) (_69486 : real) (_69485 : real) (_69484 : real -> Prop) : (term852 x _69486 _69484 _69485) = (term872 x _69486 _69485 _69484).
Proof. exact (TRANS (@lem5305269 x _69486 _69485 _69484) (@lem5305292 x _69486 _69485 _69484)). Qed.
Lemma lem5305295 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term873 x l s.
Proof. exact (conj (@lem5305123 x b s l h1 h2 h3) (@lem5305131 s)). Qed.
Lemma lem5305296 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : term874 x l s.
Proof. exact (conj (@lem5304873 s l h3) (@lem5305295 x b s l h1 h2 h3)). Qed.
Lemma lem5305298 (_69486 : real) (_69485 : real) (_69484 : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term872 x _69486 _69485 _69484.
Proof. exact (EQ_MP (@lem5305293 x _69486 _69485 _69484) (@lem5305266 _69486 _69484 _69485 x b h1)). Qed.
Lemma lem5305299 (l : real) (s : real -> Prop) (x : type1019) (b : type1021) (h1 : term573 x b) : term875 x l s.
Proof. exact (@lem5305298 l (sup s) s x b h1). Qed.
Lemma lem5305302 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term70 s) (h2 : term573 x b) (h3 : term221 s l) : s = (@EMPTY real).
Proof. exact (@lem5305299 l s x b h2 (@lem5305296 x b s l h1 h2 h3)). Qed.
Lemma lem5305303 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : term876 s.
Proof. exact (fun h0 : term70 s => @lem5305302 x b s l h0 h1 h2). Qed.
Lemma lem5305305 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5305306 (s : real -> Prop) : (term876 s) = (s = (@EMPTY real)).
Proof. exact (@lem5305305 (s = (@EMPTY real))). Qed.
Lemma lem5305307 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5305306 s) (@lem5305303 x b s l h1 h2)). Qed.
Lemma lem5305310 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5305312 (s : real -> Prop) : (term70 s) = (term877 s).
Proof. exact (@lem5305310 (s = (@EMPTY real))). Qed.
Lemma lem5305315 (s : real -> Prop) (l : real) (h1 : term221 s l) : term877 s.
Proof. exact (EQ_MP (@lem5305312 s) (@lem5304191 s l h1)). Qed.
Lemma lem5305318 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : False.
Proof. exact (@lem5305315 s l h2 (@lem5305307 x b s l h1 h2)). Qed.
Lemma lem5305319 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : term759.
Proof. exact (fun h0 : ~ False => @lem5305318 x b s l h1 h2). Qed.
Lemma lem5305321 (p : Prop) : (term749 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5305322 : term759 = False.
Proof. exact (@lem5305321 False). Qed.
Lemma lem5305323 (x : type1019) (b : type1021) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term221 s l) : False.
Proof. exact (EQ_MP (@lem5305322) (@lem5305319 x b s l h1 h2)). Qed.
Lemma lem5305324 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5304484) (@lem5304481 x b l x' s h1 h2 h3)). Qed.
Lemma lem5305325 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY real) => @lem5305324 x b l x' s h1 h2 h3) (fun h4 : False => @lem5304081 s h3)). Qed.
Lemma lem5305326 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5305325 x b l x' s h1 h2 h3) (@lem5304081 s h3)). Qed.
Lemma lem5305327 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY real) => @lem5305326 x b l x' s h1 h2 h3) (fun h4 : False => @lem5303459 s h3)). Qed.
Lemma lem5305328 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5305327 x b l x' s h1 h2 h3) (@lem5303459 s h3)). Qed.
Lemma lem5305329 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : (term137 s x') = False.
Proof. exact (prop_ext (fun h4 : term137 s x' => @lem5304759 x b l s x' h1 h2 h3) (fun h4 : False => @lem5303722 s x' h1)). Qed.
Lemma lem5305330 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term137 s x') (h2 : term573 x b) (h3 : term189 l s x') : False.
Proof. exact (EQ_MP (@lem5305329 x b l s x' h1 h2 h3) (@lem5303722 s x' h1)). Qed.
Lemma lem5305331 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY real) => @lem5305328 x b l x' s h1 h2 h3) (fun h4 : False => @lem5303459 s h3)). Qed.
Lemma lem5305332 (x : type1019) (b : type1021) (l : real) (x' : real -> real) (s : real -> Prop) (h1 : term573 x b) (h2 : term189 l s x') (h3 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5305331 x b l x' s h1 h2 h3) (@lem5303459 s h3)). Qed.
Lemma lem5305333 (x : type1019) (b : type1021) (l : real) (s : real -> Prop) (x' : real -> real) (h1 : term573 x b) (h2 : term189 l s x') : False.
Proof. exact (or_elim (@lem5303196 l s x' h2) (fun h0 : s = (@EMPTY real) => @lem5305332 x b l x' s h1 h2 h0) (fun h0 : term137 s x' => @lem5305330 x b l s x' h0 h1 h2)). Qed.
Lemma lem5305334 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : False.
Proof. exact (or_elim (@lem5303191 x' s l h2) (fun h0 : term189 l s x' => @lem5305333 x b l s x' h1 h0) (fun h0 : term221 s l => @lem5305323 x b s l h1 h0)). Qed.
Lemma lem5305335 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : (term284 x' s l) = False.
Proof. exact (prop_ext (fun h3 : term284 x' s l => @lem5305334 x b x' s l h1 h2) (fun h3 : False => @lem5303191 x' s l h2)). Qed.
Lemma lem5305336 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : False.
Proof. exact (EQ_MP (@lem5305335 x b x' s l h1 h2) (@lem5303191 x' s l h2)). Qed.
Lemma lem5305337 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : (term573 x b) = False.
Proof. exact (prop_ext (fun h3 : term573 x b => @lem5305336 x b x' s l h1 h2) (fun h3 : False => @lem5303108 x b h1)). Qed.
Lemma lem5305338 (x : type1019) (b : type1021) (x' : real -> real) (s : real -> Prop) (l : real) (h1 : term573 x b) (h2 : term284 x' s l) : False.
Proof. exact (EQ_MP (@lem5305337 x b x' s l h1 h2) (@lem5303108 x b h1)). Qed.
Lemma lem5305339 (s : real -> Prop) (l : real) (x : type1019) (b : type1021) (h1 : term287 s l) (h2 : term573 x b) : False.
Proof. exact (ex_elim (@lem5302981 s l h1) (fun x' : real -> real => fun h0 : term286 s l x' => @lem5305338 x b x' s l h2 h0)). Qed.
Lemma lem5305340 (s : real -> Prop) (x : type1019) (b : type1021) (h1 : term289 s) (h2 : term573 x b) : False.
Proof. exact (ex_elim (@lem5302980 s h1) (fun l : real => fun h0 : term288 s l => @lem5305339 s l x b h0 h2)). Qed.
Lemma lem5305341 (x : type1019) (b : type1021) (h1 : term3) (h2 : term573 x b) : False.
Proof. exact (ex_elim (@lem5302060 h1) (fun s : real -> Prop => fun h0 : term290 s => @lem5305340 s x b h0 h2)). Qed.
Lemma lem5305342 (x : type1019) (h1 : term576 x) (h2 : term3) : False.
Proof. exact (ex_elim (@lem5302978 x h1) (fun b : type1021 => fun h0 : term575 x b => @lem5305341 x b h2 h0)). Qed.
Lemma lem5305343 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem5302977 h1) (fun x : type1019 => fun h0 : term577 x => @lem5305342 x h0 h2)). Qed.
Lemma lem5305344 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem5305343 h0 h1). Qed.
Lemma lem5305345 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem5305346 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem5305345) (@lem5305344 h1)). Qed.
Lemma lem5305347 : term12.
Proof. exact (fun h0 : term3 => @lem5305346 h0). Qed.
Lemma lem5305348 : term4.
Proof. exact (EQ_MP (@lem5301475) (@lem5305347)). Qed.
Lemma lem5305350 : term4.
Proof. exact (@lem5301291 (@lem5305348)). Qed.
Lemma lem5305351 (h1 : term3) : term8.
Proof. exact (@lem5305350 (@lem5301276 h1)). Qed.
Lemma lem5305352 (h1 : term3) : False.
Proof. exact (@lem5305351 h1 (@lem5297166)). Qed.
Lemma lem5305353 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem5305352 h1) (fun h2 : False => @lem5301276 h1)). Qed.
Lemma lem5305354 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem5305353 h1) (@lem5301276 h1)). Qed.
Lemma lem5305355 : term2.
Proof. exact (fun h0 : term3 => @lem5305354 h0). Qed.
Lemma lem5305356 : term1.
Proof. exact (EQ_MP (@lem5301275) (@lem5305355)). Qed.
