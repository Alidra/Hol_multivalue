Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ELEMENT_LE_SUP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LE_SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339240_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5197252 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5197253 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5197254 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5197253 t1) (@lem5197252 t1)). Qed.
Lemma lem5197255 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5197254 t1 t2). Qed.
Lemma lem5197256 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5197257 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5197256 t1 t2) (@lem5197255 t1 t2)). Qed.
Lemma lem5197258 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5197257 t1 t2 t3). Qed.
Lemma lem5197259 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5197260 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5197259 t1 t2 t3) (@lem5197258 t1 t2 t3)). Qed.
Lemma lem5197261 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5197260 t1 t2 t3)). Qed.
Lemma lem5197263 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5197264 : term8 = term9.
Proof. exact (@lem5197263 term8). Qed.
Lemma lem5197265 : term9 = term8.
Proof. exact (SYM (@lem5197264)). Qed.
Lemma lem5197266 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5197269 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5197270 : term12.
Proof. exact (fun h0 : term11 => @lem5197269 h0). Qed.
Lemma lem5197271 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5197272 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5197273 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5197271 h2 (@lem5197272 h1)). Qed.
Lemma lem5197274 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5197273 h1 h0). Qed.
Lemma lem5197275 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5197276 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5197274 h1 (@lem5197275 h2)). Qed.
Lemma lem5197277 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5197276 h0 h1). Qed.
Lemma lem5197278 : term14.
Proof. exact (fun h0 : term12 => @lem5197277 h0). Qed.
Lemma lem5197281 : term12.
Proof. exact (@lem5197278 (@lem5197270)). Qed.
Lemma lem5197313 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5197314 : term15 = term16.
Proof. exact (@lem5197313 term17). Qed.
Lemma lem5197343 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5197344 : term19 = term20.
Proof. exact (MK_COMB (@lem5197343) (@lem5197314)). Qed.
Lemma lem5197347 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5197354 : term11 = term22.
Proof. exact (MK_COMB (@lem5197347) (@lem5197344)). Qed.
Lemma lem5197355 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197360 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term24 s x b).
Proof. exact (eq_refl (term24 s x b)). Qed.
Lemma lem5197361 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5197360 s x b)). Qed.
Lemma lem5197362 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197363 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5197362) (@lem5197361 s b)). Qed.
Lemma lem5197366 (a : real) (y : real) : (term27 a y) = (term27 a y).
Proof. exact (eq_refl (term27 a y)). Qed.
Lemma lem5197367 (a : real) (y : real) (s : real -> Prop) (b : real) : (term28 a y s b) = (term28 a y s b).
Proof. exact (MK_COMB (@lem5197366 a y) (@lem5197363 s b)). Qed.
Lemma lem5197370 (y : real) (s : real -> Prop) : (term29 y s) = (term29 y s).
Proof. exact (eq_refl (term29 y s)). Qed.
Lemma lem5197371 (a : real) (y : real) (s : real -> Prop) (b : real) : (term30 a y s b) = (term30 a y s b).
Proof. exact (MK_COMB (@lem5197370 y s) (@lem5197367 a y s b)). Qed.
Lemma lem5197372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5197373 (a : real) (y : real) (s : real -> Prop) (b : real) : (term31 a y s b) = (term31 a y s b).
Proof. exact (MK_COMB (@lem5197372) (@lem5197371 a y s b)). Qed.
Lemma lem5197374 (y : real) (b : real) (a : real) (s : real -> Prop) : (term32 y b a s) = (term32 y b a s).
Proof. exact (MK_COMB (@lem5197373 a y s b) (@lem5197355 a s)). Qed.
Lemma lem5197375 (b : real) (a : real) (s : real -> Prop) : (term33 b a s) = (term33 b a s).
Proof. exact (fun_ext (fun y : real => @lem5197374 y b a s)). Qed.
Lemma lem5197376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197377 (b : real) (a : real) (s : real -> Prop) : (term34 b a s) = (term34 b a s).
Proof. exact (MK_COMB (@lem5197376) (@lem5197375 b a s)). Qed.
Lemma lem5197378 (a : real) (s : real -> Prop) : (term35 a s) = (term35 a s).
Proof. exact (fun_ext (fun b : real => @lem5197377 b a s)). Qed.
Lemma lem5197379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197380 (a : real) (s : real -> Prop) : (term36 a s) = (term36 a s).
Proof. exact (MK_COMB (@lem5197379) (@lem5197378 a s)). Qed.
Lemma lem5197381 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (fun_ext (fun a : real => @lem5197380 a s)). Qed.
Lemma lem5197382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197383 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5197382) (@lem5197381 s)). Qed.
Lemma lem5197384 : term39 = term39.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5197383 s)). Qed.
Lemma lem5197385 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5197386 : term17 = term17.
Proof. exact (MK_COMB (@lem5197385) (@lem5197384)). Qed.
Lemma lem5197387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5197388 : term16 = term16.
Proof. exact (MK_COMB (@lem5197387) (@lem5197386)). Qed.
Lemma lem5197389 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5197390 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5197389 x)). Qed.
Lemma lem5197391 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197392 : term41 = term41.
Proof. exact (MK_COMB (@lem5197391) (@lem5197390)). Qed.
Lemma lem5197393 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5197394 : term18 = term18.
Proof. exact (MK_COMB (@lem5197393) (@lem5197392)). Qed.
Lemma lem5197395 : term20 = term20.
Proof. exact (MK_COMB (@lem5197394) (@lem5197388)). Qed.
Lemma lem5197396 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197397 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5197402 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term24 s x b).
Proof. exact (eq_refl (term24 s x b)). Qed.
Lemma lem5197403 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5197402 s x b)). Qed.
Lemma lem5197404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197405 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5197404) (@lem5197403 s b)). Qed.
Lemma lem5197406 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (fun_ext (fun b : real => @lem5197405 s b)). Qed.
Lemma lem5197407 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197408 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (MK_COMB (@lem5197407) (@lem5197406 s)). Qed.
Lemma lem5197409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197410 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (MK_COMB (@lem5197409) (@lem5197408 s)). Qed.
Lemma lem5197411 (a : real) (s : real -> Prop) : (term45 a s) = (term45 a s).
Proof. exact (MK_COMB (@lem5197410 s) (@lem5197397 a s)). Qed.
Lemma lem5197412 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5197413 (a : real) (s : real -> Prop) : (term46 a s) = (term46 a s).
Proof. exact (MK_COMB (@lem5197412) (@lem5197411 a s)). Qed.
Lemma lem5197414 (a : real) (s : real -> Prop) : (term47 a s) = (term47 a s).
Proof. exact (MK_COMB (@lem5197413 a s) (@lem5197396 a s)). Qed.
Lemma lem5197415 (s : real -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun a : real => @lem5197414 a s)). Qed.
Lemma lem5197416 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197417 (s : real -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem5197416) (@lem5197415 s)). Qed.
Lemma lem5197418 : term50 = term50.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5197417 s)). Qed.
Lemma lem5197419 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5197420 : term8 = term8.
Proof. exact (MK_COMB (@lem5197419) (@lem5197418)). Qed.
Lemma lem5197421 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5197422 : term10 = term10.
Proof. exact (MK_COMB (@lem5197421) (@lem5197420)). Qed.
Lemma lem5197423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5197424 : term21 = term21.
Proof. exact (MK_COMB (@lem5197423) (@lem5197422)). Qed.
Lemma lem5197425 : term22 = term22.
Proof. exact (MK_COMB (@lem5197424) (@lem5197395)). Qed.
Lemma lem5197506 : term11 = term22.
Proof. exact (TRANS (@lem5197354) (@lem5197425)). Qed.
Lemma lem5197507 : term22 = term11.
Proof. exact (SYM (@lem5197506)). Qed.
Lemma lem5197508 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5197509 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem5197510 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5197517 (s : real -> Prop) (x : real) (b : real) : (term24 s x b) = (term51 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5197518 (s : real -> Prop) (b : real) : (term25 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5197517 s x b)). Qed.
Lemma lem5197519 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197520 (s : real -> Prop) (b : real) : (term26 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5197519) (@lem5197518 s b)). Qed.
Lemma lem5197521 (s : real -> Prop) : (term42 s) = (term54 s).
Proof. exact (fun_ext (fun b : real => @lem5197520 s b)). Qed.
Lemma lem5197522 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197523 (s : real -> Prop) : (term43 s) = (term55 s).
Proof. exact (MK_COMB (@lem5197522) (@lem5197521 s)). Qed.
Lemma lem5197524 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5197525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197526 (s : real -> Prop) : (term44 s) = (term56 s).
Proof. exact (MK_COMB (@lem5197525) (@lem5197523 s)). Qed.
Lemma lem5197527 (a : real) (s : real -> Prop) : (term45 a s) = (term57 a s).
Proof. exact (MK_COMB (@lem5197526 s) (@lem5197524 a s)). Qed.
Lemma lem5197528 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5197529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197530 (a : real) (s : real -> Prop) : (term59 a s) = (term60 a s).
Proof. exact (MK_COMB (@lem5197529) (@lem5197527 a s)). Qed.
Lemma lem5197531 (a : real) (s : real -> Prop) : (term61 a s) = (term62 a s).
Proof. exact (MK_COMB (@lem5197530 a s) (@lem5197528 a s)). Qed.
Lemma lem5197532 (a : real) (s : real -> Prop) : (term63 a s) = (term61 a s).
Proof. exact (@lem17362 (term45 a s) (term23 a s)). Qed.
Lemma lem5197533 (a : real) (s : real -> Prop) : (term63 a s) = (term62 a s).
Proof. exact (TRANS (@lem5197532 a s) (@lem5197531 a s)). Qed.
Lemma lem5197534 (P : real -> Prop) : (term64 P) = (term65 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5197535 (s : real -> Prop) : (term66 s) = (term67 s).
Proof. exact (@lem5197534 (term48 s)). Qed.
Lemma lem5197536 (a : real) (s : real -> Prop) : (term68 s a) = (term47 a s).
Proof. exact (eq_refl (term68 s a)). Qed.
Lemma lem5197537 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5197538 (a : real) (s : real -> Prop) : (term69 s a) = (term63 a s).
Proof. exact (MK_COMB (@lem5197537) (@lem5197536 a s)). Qed.
Lemma lem5197539 (a : real) (s : real -> Prop) : (term69 s a) = (term62 a s).
Proof. exact (TRANS (@lem5197538 a s) (@lem5197533 a s)). Qed.
Lemma lem5197540 (s : real -> Prop) : (term70 s) = (term71 s).
Proof. exact (fun_ext (fun a : real => @lem5197539 a s)). Qed.
Lemma lem5197541 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197542 (s : real -> Prop) : (term67 s) = (term72 s).
Proof. exact (MK_COMB (@lem5197541) (@lem5197540 s)). Qed.
Lemma lem5197543 (s : real -> Prop) : (term66 s) = (term72 s).
Proof. exact (TRANS (@lem5197535 s) (@lem5197542 s)). Qed.
Lemma lem5197544 (P : type1022) : (term73 P) = (term74 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5197545 : term10 = term75.
Proof. exact (@lem5197544 term50). Qed.
Lemma lem5197546 (s : real -> Prop) : (term76 s) = (term49 s).
Proof. exact (eq_refl (term76 s)). Qed.
Lemma lem5197547 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5197548 (s : real -> Prop) : (term77 s) = (term66 s).
Proof. exact (MK_COMB (@lem5197547) (@lem5197546 s)). Qed.
Lemma lem5197549 (s : real -> Prop) : (term77 s) = (term72 s).
Proof. exact (TRANS (@lem5197548 s) (@lem5197543 s)). Qed.
Lemma lem5197550 : term78 = term79.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5197549 s)). Qed.
Lemma lem5197551 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5197552 : term75 = term80.
Proof. exact (MK_COMB (@lem5197551) (@lem5197550)). Qed.
Lemma lem5197553 : term10 = term80.
Proof. exact (TRANS (@lem5197545) (@lem5197552)). Qed.
Lemma lem5197660 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5197661 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem5197660 real P Q). Qed.
Lemma lem5197662 (a : real) (s : real -> Prop) : (term85 a s) = (term86 a s).
Proof. exact (@lem5197661 (term54 s) (@IN real a s)). Qed.
Lemma lem5197663 (s : real -> Prop) (b : real) : (term87 s b) = (term53 s b).
Proof. exact (eq_refl (term87 s b)). Qed.
Lemma lem5197664 (s : real -> Prop) : (term88 s) = (term54 s).
Proof. exact (fun_ext (fun b : real => @lem5197663 s b)). Qed.
Lemma lem5197665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197666 (s : real -> Prop) : (term89 s) = (term55 s).
Proof. exact (MK_COMB (@lem5197665) (@lem5197664 s)). Qed.
Lemma lem5197667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197668 (s : real -> Prop) : (term90 s) = (term56 s).
Proof. exact (MK_COMB (@lem5197667) (@lem5197666 s)). Qed.
Lemma lem5197669 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5197670 (a : real) (s : real -> Prop) : (term85 a s) = (term57 a s).
Proof. exact (MK_COMB (@lem5197668 s) (@lem5197669 a s)). Qed.
Lemma lem5197671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5197672 (a : real) (s : real -> Prop) : (term91 a s) = (term92 a s).
Proof. exact (MK_COMB (@lem5197671) (@lem5197670 a s)). Qed.
Lemma lem5197673 (s : real -> Prop) (b : real) : (term87 s b) = (term53 s b).
Proof. exact (eq_refl (term87 s b)). Qed.
Lemma lem5197674 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197675 (s : real -> Prop) (b : real) : (term93 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5197674) (@lem5197673 s b)). Qed.
Lemma lem5197676 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5197677 (b : real) (a : real) (s : real -> Prop) : (term95 b a s) = (term96 b a s).
Proof. exact (MK_COMB (@lem5197675 s b) (@lem5197676 a s)). Qed.
Lemma lem5197678 (a : real) (s : real -> Prop) : (term97 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5197677 b a s)). Qed.
Lemma lem5197679 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197680 (a : real) (s : real -> Prop) : (term86 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5197679) (@lem5197678 a s)). Qed.
Lemma lem5197681 (a : real) (s : real -> Prop) : ((term85 a s) = (term86 a s)) = ((term57 a s) = (term99 a s)).
Proof. exact (MK_COMB (@lem5197672 a s) (@lem5197680 a s)). Qed.
Lemma lem5197682 (a : real) (s : real -> Prop) : (term57 a s) = (term99 a s).
Proof. exact (EQ_MP (@lem5197681 a s) (@lem5197662 a s)). Qed.
Lemma lem5197683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197684 (a : real) (s : real -> Prop) : (term60 a s) = (term100 a s).
Proof. exact (MK_COMB (@lem5197683) (@lem5197682 a s)). Qed.
Lemma lem5197685 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5197686 (a : real) (s : real -> Prop) : (term62 a s) = (term101 a s).
Proof. exact (MK_COMB (@lem5197684 a s) (@lem5197685 a s)). Qed.
Lemma lem5197688 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5197689 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem5197688 real P Q). Qed.
Lemma lem5197690 (a : real) (s : real -> Prop) : (term102 a s) = (term103 a s).
Proof. exact (@lem5197689 (term98 a s) (term58 a s)). Qed.
Lemma lem5197691 (b : real) (a : real) (s : real -> Prop) : (term104 a s b) = (term96 b a s).
Proof. exact (eq_refl (term104 a s b)). Qed.
Lemma lem5197692 (a : real) (s : real -> Prop) : (term105 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5197691 b a s)). Qed.
Lemma lem5197693 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197694 (a : real) (s : real -> Prop) : (term106 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5197693) (@lem5197692 a s)). Qed.
Lemma lem5197695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197696 (a : real) (s : real -> Prop) : (term107 a s) = (term100 a s).
Proof. exact (MK_COMB (@lem5197695) (@lem5197694 a s)). Qed.
Lemma lem5197697 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5197698 (a : real) (s : real -> Prop) : (term102 a s) = (term101 a s).
Proof. exact (MK_COMB (@lem5197696 a s) (@lem5197697 a s)). Qed.
Lemma lem5197699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5197700 (a : real) (s : real -> Prop) : (term108 a s) = (term109 a s).
Proof. exact (MK_COMB (@lem5197699) (@lem5197698 a s)). Qed.
Lemma lem5197701 (b : real) (a : real) (s : real -> Prop) : (term104 a s b) = (term96 b a s).
Proof. exact (eq_refl (term104 a s b)). Qed.
Lemma lem5197702 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5197703 (b : real) (a : real) (s : real -> Prop) : (term110 a s b) = (term111 b a s).
Proof. exact (MK_COMB (@lem5197702) (@lem5197701 b a s)). Qed.
Lemma lem5197704 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5197705 (b : real) (a : real) (s : real -> Prop) : (term112 b a s) = (term113 b a s).
Proof. exact (MK_COMB (@lem5197703 b a s) (@lem5197704 a s)). Qed.
Lemma lem5197706 (a : real) (s : real -> Prop) : (term114 a s) = (term115 a s).
Proof. exact (fun_ext (fun b : real => @lem5197705 b a s)). Qed.
Lemma lem5197707 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197708 (a : real) (s : real -> Prop) : (term103 a s) = (term116 a s).
Proof. exact (MK_COMB (@lem5197707) (@lem5197706 a s)). Qed.
Lemma lem5197709 (a : real) (s : real -> Prop) : ((term102 a s) = (term103 a s)) = ((term101 a s) = (term116 a s)).
Proof. exact (MK_COMB (@lem5197700 a s) (@lem5197708 a s)). Qed.
Lemma lem5197710 (a : real) (s : real -> Prop) : (term101 a s) = (term116 a s).
Proof. exact (EQ_MP (@lem5197709 a s) (@lem5197690 a s)). Qed.
Lemma lem5197711 (a : real) (s : real -> Prop) : (term62 a s) = (term116 a s).
Proof. exact (TRANS (@lem5197686 a s) (@lem5197710 a s)). Qed.
Lemma lem5197712 (s : real -> Prop) : (term71 s) = (term117 s).
Proof. exact (fun_ext (fun a : real => @lem5197711 a s)). Qed.
Lemma lem5197713 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197714 (s : real -> Prop) : (term72 s) = (term118 s).
Proof. exact (MK_COMB (@lem5197713) (@lem5197712 s)). Qed.
Lemma lem5197715 : term79 = term119.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5197714 s)). Qed.
Lemma lem5197716 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5197718 : term80 = term120.
Proof. exact (MK_COMB (@lem5197716) (@lem5197715)). Qed.
Lemma lem5197719 : term10 = term120.
Proof. exact (TRANS (@lem5197553) (@lem5197718)). Qed.
Lemma lem5197720 (h1 : term10) : term120.
Proof. exact (EQ_MP (@lem5197719) (@lem5197508 h1)). Qed.
Lemma lem5197721 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5197722 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5197721 x)). Qed.
Lemma lem5197723 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197732 : term41 = term41.
Proof. exact (MK_COMB (@lem5197723) (@lem5197722)). Qed.
Lemma lem5197733 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem5197732) (@lem5197509 h1)). Qed.
Lemma lem5197742 (s : real -> Prop) (x : real) (b : real) : (term121 s x b) = (term122 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5197743 (P : real -> Prop) : (term64 P) = (term65 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5197744 (s : real -> Prop) (b : real) : (term123 s b) = (term124 s b).
Proof. exact (@lem5197743 (term25 s b)). Qed.
Lemma lem5197745 (s : real -> Prop) (x : real) (b : real) : (term125 s b x) = (term24 s x b).
Proof. exact (eq_refl (term125 s b x)). Qed.
Lemma lem5197746 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5197747 (s : real -> Prop) (x : real) (b : real) : (term126 s b x) = (term121 s x b).
Proof. exact (MK_COMB (@lem5197746) (@lem5197745 s x b)). Qed.
Lemma lem5197748 (s : real -> Prop) (x : real) (b : real) : (term126 s b x) = (term122 s x b).
Proof. exact (TRANS (@lem5197747 s x b) (@lem5197742 s x b)). Qed.
Lemma lem5197749 (s : real -> Prop) (b : real) : (term127 s b) = (term128 s b).
Proof. exact (fun_ext (fun x : real => @lem5197748 s x b)). Qed.
Lemma lem5197750 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5197751 (s : real -> Prop) (b : real) : (term124 s b) = (term129 s b).
Proof. exact (MK_COMB (@lem5197750) (@lem5197749 s b)). Qed.
Lemma lem5197752 (s : real -> Prop) (b : real) : (term123 s b) = (term129 s b).
Proof. exact (TRANS (@lem5197744 s b) (@lem5197751 s b)). Qed.
Lemma lem5197754 (a : real) (y : real) : (term130 a y) = (term130 a y).
Proof. exact (eq_refl (term130 a y)). Qed.
Lemma lem5197755 (a : real) (y : real) (s : real -> Prop) (b : real) : (term131 a y s b) = (term132 a y s b).
Proof. exact (MK_COMB (@lem5197754 a y) (@lem5197752 s b)). Qed.
Lemma lem5197756 (a : real) (y : real) (s : real -> Prop) (b : real) : (term133 a y s b) = (term131 a y s b).
Proof. exact (@lem17045 (real_le a y) (term26 s b)). Qed.
Lemma lem5197757 (a : real) (y : real) (s : real -> Prop) (b : real) : (term133 a y s b) = (term132 a y s b).
Proof. exact (TRANS (@lem5197756 a y s b) (@lem5197755 a y s b)). Qed.
Lemma lem5197759 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5197760 (a : real) (y : real) (s : real -> Prop) (b : real) : (term135 a y s b) = (term136 a y s b).
Proof. exact (MK_COMB (@lem5197759 y s) (@lem5197757 a y s b)). Qed.
Lemma lem5197761 (a : real) (y : real) (s : real -> Prop) (b : real) : (term137 a y s b) = (term135 a y s b).
Proof. exact (@lem17045 (@IN real y s) (term28 a y s b)). Qed.
Lemma lem5197762 (a : real) (y : real) (s : real -> Prop) (b : real) : (term137 a y s b) = (term136 a y s b).
Proof. exact (TRANS (@lem5197761 a y s b) (@lem5197760 a y s b)). Qed.
Lemma lem5197763 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197764 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5197765 (a : real) (y : real) (s : real -> Prop) (b : real) : (term138 a y s b) = (term139 a y s b).
Proof. exact (MK_COMB (@lem5197764) (@lem5197762 a y s b)). Qed.
Lemma lem5197766 (y : real) (b : real) (a : real) (s : real -> Prop) : (term140 y b a s) = (term141 y b a s).
Proof. exact (MK_COMB (@lem5197765 a y s b) (@lem5197763 a s)). Qed.
Lemma lem5197767 (y : real) (b : real) (a : real) (s : real -> Prop) : (term32 y b a s) = (term140 y b a s).
Proof. exact (@lem17265 (term30 a y s b) (term23 a s)). Qed.
Lemma lem5197768 (y : real) (b : real) (a : real) (s : real -> Prop) : (term32 y b a s) = (term141 y b a s).
Proof. exact (TRANS (@lem5197767 y b a s) (@lem5197766 y b a s)). Qed.
Lemma lem5197769 (b : real) (a : real) (s : real -> Prop) : (term33 b a s) = (term142 b a s).
Proof. exact (fun_ext (fun y : real => @lem5197768 y b a s)). Qed.
Lemma lem5197770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197771 (b : real) (a : real) (s : real -> Prop) : (term34 b a s) = (term143 b a s).
Proof. exact (MK_COMB (@lem5197770) (@lem5197769 b a s)). Qed.
Lemma lem5197772 (a : real) (s : real -> Prop) : (term35 a s) = (term144 a s).
Proof. exact (fun_ext (fun b : real => @lem5197771 b a s)). Qed.
Lemma lem5197773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197774 (a : real) (s : real -> Prop) : (term36 a s) = (term145 a s).
Proof. exact (MK_COMB (@lem5197773) (@lem5197772 a s)). Qed.
Lemma lem5197775 (s : real -> Prop) : (term37 s) = (term146 s).
Proof. exact (fun_ext (fun a : real => @lem5197774 a s)). Qed.
Lemma lem5197776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197777 (s : real -> Prop) : (term38 s) = (term147 s).
Proof. exact (MK_COMB (@lem5197776) (@lem5197775 s)). Qed.
Lemma lem5197778 : term39 = term148.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5197777 s)). Qed.
Lemma lem5197779 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5197780 : term17 = term149.
Proof. exact (MK_COMB (@lem5197779) (@lem5197778)). Qed.
Lemma lem5197814 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5197815 (P : real -> Prop) (Q : Prop) : (term152 P Q) = (term153 P Q).
Proof. exact (@lem5197814 real P Q). Qed.
Lemma lem5197816 (b : real) (a : real) (s : real -> Prop) : (term154 b a s) = (term155 b a s).
Proof. exact (@lem5197815 (term156 a s b) (term23 a s)). Qed.
Lemma lem5197817 (a : real) (y : real) (s : real -> Prop) (b : real) : (term157 a s b y) = (term136 a y s b).
Proof. exact (eq_refl (term157 a s b y)). Qed.
Lemma lem5197818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5197819 (a : real) (y : real) (s : real -> Prop) (b : real) : (term158 a s b y) = (term139 a y s b).
Proof. exact (MK_COMB (@lem5197818) (@lem5197817 a y s b)). Qed.
Lemma lem5197820 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197821 (y : real) (b : real) (a : real) (s : real -> Prop) : (term159 b y a s) = (term141 y b a s).
Proof. exact (MK_COMB (@lem5197819 a y s b) (@lem5197820 a s)). Qed.
Lemma lem5197822 (b : real) (a : real) (s : real -> Prop) : (term160 b a s) = (term142 b a s).
Proof. exact (fun_ext (fun y : real => @lem5197821 y b a s)). Qed.
Lemma lem5197823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197824 (b : real) (a : real) (s : real -> Prop) : (term154 b a s) = (term143 b a s).
Proof. exact (MK_COMB (@lem5197823) (@lem5197822 b a s)). Qed.
Lemma lem5197825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5197826 (b : real) (a : real) (s : real -> Prop) : (term161 b a s) = (term162 b a s).
Proof. exact (MK_COMB (@lem5197825) (@lem5197824 b a s)). Qed.
Lemma lem5197827 (a : real) (y : real) (s : real -> Prop) (b : real) : (term157 a s b y) = (term136 a y s b).
Proof. exact (eq_refl (term157 a s b y)). Qed.
Lemma lem5197828 (a : real) (s : real -> Prop) (b : real) : (term163 a s b) = (term156 a s b).
Proof. exact (fun_ext (fun y : real => @lem5197827 a y s b)). Qed.
Lemma lem5197829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197830 (a : real) (s : real -> Prop) (b : real) : (term164 a s b) = (term165 a s b).
Proof. exact (MK_COMB (@lem5197829) (@lem5197828 a s b)). Qed.
Lemma lem5197831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5197832 (a : real) (s : real -> Prop) (b : real) : (term166 a s b) = (term167 a s b).
Proof. exact (MK_COMB (@lem5197831) (@lem5197830 a s b)). Qed.
Lemma lem5197833 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197834 (b : real) (a : real) (s : real -> Prop) : (term155 b a s) = (term168 b a s).
Proof. exact (MK_COMB (@lem5197832 a s b) (@lem5197833 a s)). Qed.
Lemma lem5197835 (b : real) (a : real) (s : real -> Prop) : ((term154 b a s) = (term155 b a s)) = ((term143 b a s) = (term168 b a s)).
Proof. exact (MK_COMB (@lem5197826 b a s) (@lem5197834 b a s)). Qed.
Lemma lem5197836 (b : real) (a : real) (s : real -> Prop) : (term143 b a s) = (term168 b a s).
Proof. exact (EQ_MP (@lem5197835 b a s) (@lem5197816 b a s)). Qed.
Lemma lem5197933 (a : real) (s : real -> Prop) : (term144 a s) = (term169 a s).
Proof. exact (fun_ext (fun b : real => @lem5197836 b a s)). Qed.
Lemma lem5197934 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197935 (a : real) (s : real -> Prop) : (term145 a s) = (term170 a s).
Proof. exact (MK_COMB (@lem5197934) (@lem5197933 a s)). Qed.
Lemma lem5197957 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5197958 (P : real -> Prop) (Q : Prop) : (term152 P Q) = (term153 P Q).
Proof. exact (@lem5197957 real P Q). Qed.
Lemma lem5197959 (a : real) (s : real -> Prop) : (term171 a s) = (term172 a s).
Proof. exact (@lem5197958 (term173 a s) (term23 a s)). Qed.
Lemma lem5197960 (a : real) (s : real -> Prop) (b : real) : (term174 a s b) = (term165 a s b).
Proof. exact (eq_refl (term174 a s b)). Qed.
Lemma lem5197961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5197962 (a : real) (s : real -> Prop) (b : real) : (term175 a s b) = (term167 a s b).
Proof. exact (MK_COMB (@lem5197961) (@lem5197960 a s b)). Qed.
Lemma lem5197963 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197964 (b : real) (a : real) (s : real -> Prop) : (term176 b a s) = (term168 b a s).
Proof. exact (MK_COMB (@lem5197962 a s b) (@lem5197963 a s)). Qed.
Lemma lem5197965 (a : real) (s : real -> Prop) : (term177 a s) = (term169 a s).
Proof. exact (fun_ext (fun b : real => @lem5197964 b a s)). Qed.
Lemma lem5197966 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197967 (a : real) (s : real -> Prop) : (term171 a s) = (term170 a s).
Proof. exact (MK_COMB (@lem5197966) (@lem5197965 a s)). Qed.
Lemma lem5197968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5197969 (a : real) (s : real -> Prop) : (term178 a s) = (term179 a s).
Proof. exact (MK_COMB (@lem5197968) (@lem5197967 a s)). Qed.
Lemma lem5197970 (a : real) (s : real -> Prop) (b : real) : (term174 a s b) = (term165 a s b).
Proof. exact (eq_refl (term174 a s b)). Qed.
Lemma lem5197971 (a : real) (s : real -> Prop) : (term180 a s) = (term173 a s).
Proof. exact (fun_ext (fun b : real => @lem5197970 a s b)). Qed.
Lemma lem5197972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5197973 (a : real) (s : real -> Prop) : (term181 a s) = (term182 a s).
Proof. exact (MK_COMB (@lem5197972) (@lem5197971 a s)). Qed.
Lemma lem5197974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5197975 (a : real) (s : real -> Prop) : (term183 a s) = (term184 a s).
Proof. exact (MK_COMB (@lem5197974) (@lem5197973 a s)). Qed.
Lemma lem5197976 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5197977 (a : real) (s : real -> Prop) : (term172 a s) = (term185 a s).
Proof. exact (MK_COMB (@lem5197975 a s) (@lem5197976 a s)). Qed.
Lemma lem5197978 (a : real) (s : real -> Prop) : ((term171 a s) = (term172 a s)) = ((term170 a s) = (term185 a s)).
Proof. exact (MK_COMB (@lem5197969 a s) (@lem5197977 a s)). Qed.
Lemma lem5197979 (a : real) (s : real -> Prop) : (term170 a s) = (term185 a s).
Proof. exact (EQ_MP (@lem5197978 a s) (@lem5197959 a s)). Qed.
Lemma lem5198080 (a : real) (s : real -> Prop) : (term145 a s) = (term185 a s).
Proof. exact (TRANS (@lem5197935 a s) (@lem5197979 a s)). Qed.
Lemma lem5198081 (s : real -> Prop) : (term146 s) = (term186 s).
Proof. exact (fun_ext (fun a : real => @lem5198080 a s)). Qed.
Lemma lem5198082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198083 (s : real -> Prop) : (term147 s) = (term187 s).
Proof. exact (MK_COMB (@lem5198082) (@lem5198081 s)). Qed.
Lemma lem5198132 : term148 = term188.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198083 s)). Qed.
Lemma lem5198133 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198134 : term149 = term189.
Proof. exact (MK_COMB (@lem5198133) (@lem5198132)). Qed.
Lemma lem5198140 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5198141 (P : Prop) (Q : real -> Prop) : (term192 P Q) = (term193 P Q).
Proof. exact (@lem5198140 real P Q). Qed.
Lemma lem5198142 (a : real) (y : real) (s : real -> Prop) (b : real) : (term194 a y s b) = (term195 a y s b).
Proof. exact (@lem5198141 (term196 a y) (term128 s b)). Qed.
Lemma lem5198143 (s : real -> Prop) (x : real) (b : real) : (term197 s b x) = (term122 s x b).
Proof. exact (eq_refl (term197 s b x)). Qed.
Lemma lem5198144 (s : real -> Prop) (b : real) : (term198 s b) = (term128 s b).
Proof. exact (fun_ext (fun x : real => @lem5198143 s x b)). Qed.
Lemma lem5198145 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5198146 (s : real -> Prop) (b : real) : (term199 s b) = (term129 s b).
Proof. exact (MK_COMB (@lem5198145) (@lem5198144 s b)). Qed.
Lemma lem5198147 (a : real) (y : real) : (term130 a y) = (term130 a y).
Proof. exact (eq_refl (term130 a y)). Qed.
Lemma lem5198148 (a : real) (y : real) (s : real -> Prop) (b : real) : (term194 a y s b) = (term132 a y s b).
Proof. exact (MK_COMB (@lem5198147 a y) (@lem5198146 s b)). Qed.
Lemma lem5198149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198150 (a : real) (y : real) (s : real -> Prop) (b : real) : (term200 a y s b) = (term201 a y s b).
Proof. exact (MK_COMB (@lem5198149) (@lem5198148 a y s b)). Qed.
Lemma lem5198151 (s : real -> Prop) (x : real) (b : real) : (term197 s b x) = (term122 s x b).
Proof. exact (eq_refl (term197 s b x)). Qed.
Lemma lem5198152 (a : real) (y : real) : (term130 a y) = (term130 a y).
Proof. exact (eq_refl (term130 a y)). Qed.
Lemma lem5198153 (a : real) (y : real) (s : real -> Prop) (x : real) (b : real) : (term202 a y s b x) = (term203 a y s x b).
Proof. exact (MK_COMB (@lem5198152 a y) (@lem5198151 s x b)). Qed.
Lemma lem5198154 (a : real) (y : real) (s : real -> Prop) (b : real) : (term204 a y s b) = (term205 a y s b).
Proof. exact (fun_ext (fun x : real => @lem5198153 a y s x b)). Qed.
Lemma lem5198155 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5198156 (a : real) (y : real) (s : real -> Prop) (b : real) : (term195 a y s b) = (term206 a y s b).
Proof. exact (MK_COMB (@lem5198155) (@lem5198154 a y s b)). Qed.
Lemma lem5198157 (a : real) (y : real) (s : real -> Prop) (b : real) : ((term194 a y s b) = (term195 a y s b)) = ((term132 a y s b) = (term206 a y s b)).
Proof. exact (MK_COMB (@lem5198150 a y s b) (@lem5198156 a y s b)). Qed.
Lemma lem5198158 (a : real) (y : real) (s : real -> Prop) (b : real) : (term132 a y s b) = (term206 a y s b).
Proof. exact (EQ_MP (@lem5198157 a y s b) (@lem5198142 a y s b)). Qed.
Lemma lem5198159 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5198160 (a : real) (y : real) (s : real -> Prop) (b : real) : (term136 a y s b) = (term207 a y s b).
Proof. exact (MK_COMB (@lem5198159 y s) (@lem5198158 a y s b)). Qed.
Lemma lem5198162 {A : Type'} (P : Prop) (Q : A -> Prop) : (term190 A P Q) = (term191 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5198163 (P : Prop) (Q : real -> Prop) : (term192 P Q) = (term193 P Q).
Proof. exact (@lem5198162 real P Q). Qed.
Lemma lem5198164 (a : real) (y : real) (s : real -> Prop) (b : real) : (term208 a y s b) = (term209 a y s b).
Proof. exact (@lem5198163 (term210 y s) (term205 a y s b)). Qed.
Lemma lem5198165 (a : real) (y : real) (s : real -> Prop) (x : real) (b : real) : (term211 a y s b x) = (term203 a y s x b).
Proof. exact (eq_refl (term211 a y s b x)). Qed.
Lemma lem5198166 (a : real) (y : real) (s : real -> Prop) (b : real) : (term212 a y s b) = (term205 a y s b).
Proof. exact (fun_ext (fun x : real => @lem5198165 a y s x b)). Qed.
Lemma lem5198167 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5198168 (a : real) (y : real) (s : real -> Prop) (b : real) : (term213 a y s b) = (term206 a y s b).
Proof. exact (MK_COMB (@lem5198167) (@lem5198166 a y s b)). Qed.
Lemma lem5198169 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5198170 (a : real) (y : real) (s : real -> Prop) (b : real) : (term208 a y s b) = (term207 a y s b).
Proof. exact (MK_COMB (@lem5198169 y s) (@lem5198168 a y s b)). Qed.
Lemma lem5198171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198172 (a : real) (y : real) (s : real -> Prop) (b : real) : (term214 a y s b) = (term215 a y s b).
Proof. exact (MK_COMB (@lem5198171) (@lem5198170 a y s b)). Qed.
Lemma lem5198173 (a : real) (y : real) (s : real -> Prop) (x : real) (b : real) : (term211 a y s b x) = (term203 a y s x b).
Proof. exact (eq_refl (term211 a y s b x)). Qed.
Lemma lem5198174 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5198175 (a : real) (y : real) (s : real -> Prop) (x : real) (b : real) : (term216 a y s b x) = (term217 a y s x b).
Proof. exact (MK_COMB (@lem5198174 y s) (@lem5198173 a y s x b)). Qed.
Lemma lem5198176 (a : real) (y : real) (s : real -> Prop) (b : real) : (term218 a y s b) = (term219 a y s b).
Proof. exact (fun_ext (fun x : real => @lem5198175 a y s x b)). Qed.
Lemma lem5198177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5198178 (a : real) (y : real) (s : real -> Prop) (b : real) : (term209 a y s b) = (term220 a y s b).
Proof. exact (MK_COMB (@lem5198177) (@lem5198176 a y s b)). Qed.
Lemma lem5198179 (a : real) (y : real) (s : real -> Prop) (b : real) : ((term208 a y s b) = (term209 a y s b)) = ((term207 a y s b) = (term220 a y s b)).
Proof. exact (MK_COMB (@lem5198172 a y s b) (@lem5198178 a y s b)). Qed.
Lemma lem5198180 (a : real) (y : real) (s : real -> Prop) (b : real) : (term207 a y s b) = (term220 a y s b).
Proof. exact (EQ_MP (@lem5198179 a y s b) (@lem5198164 a y s b)). Qed.
Lemma lem5198181 (a : real) (y : real) (s : real -> Prop) (b : real) : (term136 a y s b) = (term220 a y s b).
Proof. exact (TRANS (@lem5198160 a y s b) (@lem5198180 a y s b)). Qed.
Lemma lem5198182 (a : real) (s : real -> Prop) (b : real) : (term156 a s b) = (term221 a s b).
Proof. exact (fun_ext (fun y : real => @lem5198181 a y s b)). Qed.
Lemma lem5198183 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198184 (a : real) (s : real -> Prop) (b : real) : (term165 a s b) = (term222 a s b).
Proof. exact (MK_COMB (@lem5198183) (@lem5198182 a s b)). Qed.
Lemma lem5198186 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5198187 (P : type1626) : (term225 P) = (term226 P).
Proof. exact (@lem5198186 real real P). Qed.
Lemma lem5198188 (a : real) (s : real -> Prop) (b : real) : (term227 a s b) = (term228 a s b).
Proof. exact (@lem5198187 (term229 a s b)). Qed.
Lemma lem5198189 (a : real) (y : real) (s : real -> Prop) (b : real) : (term230 a s b y) = (term219 a y s b).
Proof. exact (eq_refl (term230 a s b y)). Qed.
Lemma lem5198190 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5198191 (a : real) (y : real) (s : real -> Prop) (b : real) (x : real) : (term231 a s b y x) = (term232 a y s b x).
Proof. exact (MK_COMB (@lem5198189 a y s b) (@lem5198190 x)). Qed.
Lemma lem5198192 (a : real) (y : real) (s : real -> Prop) (x : real) (b : real) : (term232 a y s b x) = (term217 a y s x b).
Proof. exact (eq_refl (term232 a y s b x)). Qed.
Lemma lem5198193 (a : real) (y : real) (s : real -> Prop) (x : real) (b : real) : (term231 a s b y x) = (term217 a y s x b).
Proof. exact (TRANS (@lem5198191 a y s b x) (@lem5198192 a y s x b)). Qed.
Lemma lem5198194 (a : real) (y : real) (s : real -> Prop) (b : real) : (term233 a s b y) = (term219 a y s b).
Proof. exact (fun_ext (fun x : real => @lem5198193 a y s x b)). Qed.
Lemma lem5198195 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5198196 (a : real) (y : real) (s : real -> Prop) (b : real) : (term234 a s b y) = (term220 a y s b).
Proof. exact (MK_COMB (@lem5198195) (@lem5198194 a y s b)). Qed.
Lemma lem5198197 (a : real) (s : real -> Prop) (b : real) : (term235 a s b) = (term221 a s b).
Proof. exact (fun_ext (fun y : real => @lem5198196 a y s b)). Qed.
Lemma lem5198198 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198199 (a : real) (s : real -> Prop) (b : real) : (term227 a s b) = (term222 a s b).
Proof. exact (MK_COMB (@lem5198198) (@lem5198197 a s b)). Qed.
Lemma lem5198200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198201 (a : real) (s : real -> Prop) (b : real) : (term236 a s b) = (term237 a s b).
Proof. exact (MK_COMB (@lem5198200) (@lem5198199 a s b)). Qed.
Lemma lem5198202 (a : real) (y : real) (s : real -> Prop) (b : real) : (term230 a s b y) = (term219 a y s b).
Proof. exact (eq_refl (term230 a s b y)). Qed.
Lemma lem5198203 (x : real -> real) (y : real) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5198204 (a : real) (s : real -> Prop) (b : real) (x : real -> real) (y : real) : (term238 a s b x y) = (term239 a s b x y).
Proof. exact (MK_COMB (@lem5198202 a y s b) (@lem5198203 x y)). Qed.
Lemma lem5198205 (a : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term239 a s b x y) = (term240 a s x y b).
Proof. exact (eq_refl (term239 a s b x y)). Qed.
Lemma lem5198206 (a : real) (s : real -> Prop) (x : real -> real) (y : real) (b : real) : (term238 a s b x y) = (term240 a s x y b).
Proof. exact (TRANS (@lem5198204 a s b x y) (@lem5198205 a s x y b)). Qed.
Lemma lem5198207 (a : real) (s : real -> Prop) (x : real -> real) (b : real) : (term241 a s b x) = (term242 a s x b).
Proof. exact (fun_ext (fun y : real => @lem5198206 a s x y b)). Qed.
Lemma lem5198208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198209 (a : real) (s : real -> Prop) (x : real -> real) (b : real) : (term243 a s b x) = (term244 a s x b).
Proof. exact (MK_COMB (@lem5198208) (@lem5198207 a s x b)). Qed.
Lemma lem5198210 (a : real) (s : real -> Prop) (b : real) : (term245 a s b) = (term246 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5198209 a s x b)). Qed.
Lemma lem5198211 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5198212 (a : real) (s : real -> Prop) (b : real) : (term228 a s b) = (term247 a s b).
Proof. exact (MK_COMB (@lem5198211) (@lem5198210 a s b)). Qed.
Lemma lem5198213 (a : real) (s : real -> Prop) (b : real) : ((term227 a s b) = (term228 a s b)) = ((term222 a s b) = (term247 a s b)).
Proof. exact (MK_COMB (@lem5198201 a s b) (@lem5198212 a s b)). Qed.
Lemma lem5198214 (a : real) (s : real -> Prop) (b : real) : (term222 a s b) = (term247 a s b).
Proof. exact (EQ_MP (@lem5198213 a s b) (@lem5198188 a s b)). Qed.
Lemma lem5198215 (a : real) (s : real -> Prop) (b : real) : (term165 a s b) = (term247 a s b).
Proof. exact (TRANS (@lem5198184 a s b) (@lem5198214 a s b)). Qed.
Lemma lem5198216 (a : real) (s : real -> Prop) : (term173 a s) = (term248 a s).
Proof. exact (fun_ext (fun b : real => @lem5198215 a s b)). Qed.
Lemma lem5198217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198218 (a : real) (s : real -> Prop) : (term182 a s) = (term249 a s).
Proof. exact (MK_COMB (@lem5198217) (@lem5198216 a s)). Qed.
Lemma lem5198220 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5198221 (P : type1618) : (term250 P) = (term251 P).
Proof. exact (@lem5198220 real (real -> real) P). Qed.
Lemma lem5198222 (a : real) (s : real -> Prop) : (term252 a s) = (term253 a s).
Proof. exact (@lem5198221 (term254 a s)). Qed.
Lemma lem5198223 (a : real) (s : real -> Prop) (b : real) : (term255 a s b) = (term246 a s b).
Proof. exact (eq_refl (term255 a s b)). Qed.
Lemma lem5198224 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5198225 (a : real) (s : real -> Prop) (b : real) (x : real -> real) : (term256 a s b x) = (term257 a s b x).
Proof. exact (MK_COMB (@lem5198223 a s b) (@lem5198224 x)). Qed.
Lemma lem5198226 (a : real) (s : real -> Prop) (x : real -> real) (b : real) : (term257 a s b x) = (term244 a s x b).
Proof. exact (eq_refl (term257 a s b x)). Qed.
Lemma lem5198227 (a : real) (s : real -> Prop) (x : real -> real) (b : real) : (term256 a s b x) = (term244 a s x b).
Proof. exact (TRANS (@lem5198225 a s b x) (@lem5198226 a s x b)). Qed.
Lemma lem5198228 (a : real) (s : real -> Prop) (b : real) : (term258 a s b) = (term246 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5198227 a s x b)). Qed.
Lemma lem5198229 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5198230 (a : real) (s : real -> Prop) (b : real) : (term259 a s b) = (term247 a s b).
Proof. exact (MK_COMB (@lem5198229) (@lem5198228 a s b)). Qed.
Lemma lem5198231 (a : real) (s : real -> Prop) : (term260 a s) = (term248 a s).
Proof. exact (fun_ext (fun b : real => @lem5198230 a s b)). Qed.
Lemma lem5198232 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198233 (a : real) (s : real -> Prop) : (term252 a s) = (term249 a s).
Proof. exact (MK_COMB (@lem5198232) (@lem5198231 a s)). Qed.
Lemma lem5198234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198235 (a : real) (s : real -> Prop) : (term261 a s) = (term262 a s).
Proof. exact (MK_COMB (@lem5198234) (@lem5198233 a s)). Qed.
Lemma lem5198236 (a : real) (s : real -> Prop) (b : real) : (term255 a s b) = (term246 a s b).
Proof. exact (eq_refl (term255 a s b)). Qed.
Lemma lem5198237 (x : type1627) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5198238 (a : real) (s : real -> Prop) (x : type1627) (b : real) : (term263 a s x b) = (term264 a s x b).
Proof. exact (MK_COMB (@lem5198236 a s b) (@lem5198237 x b)). Qed.
Lemma lem5198239 (a : real) (s : real -> Prop) (x : type1627) (b : real) : (term264 a s x b) = (term265 a s x b).
Proof. exact (eq_refl (term264 a s x b)). Qed.
Lemma lem5198240 (a : real) (s : real -> Prop) (x : type1627) (b : real) : (term263 a s x b) = (term265 a s x b).
Proof. exact (TRANS (@lem5198238 a s x b) (@lem5198239 a s x b)). Qed.
Lemma lem5198241 (a : real) (s : real -> Prop) (x : type1627) : (term266 a s x) = (term267 a s x).
Proof. exact (fun_ext (fun b : real => @lem5198240 a s x b)). Qed.
Lemma lem5198242 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198243 (a : real) (s : real -> Prop) (x : type1627) : (term268 a s x) = (term269 a s x).
Proof. exact (MK_COMB (@lem5198242) (@lem5198241 a s x)). Qed.
Lemma lem5198244 (a : real) (s : real -> Prop) : (term270 a s) = (term271 a s).
Proof. exact (fun_ext (fun x : type1627 => @lem5198243 a s x)). Qed.
Lemma lem5198245 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5198246 (a : real) (s : real -> Prop) : (term253 a s) = (term272 a s).
Proof. exact (MK_COMB (@lem5198245) (@lem5198244 a s)). Qed.
Lemma lem5198247 (a : real) (s : real -> Prop) : ((term252 a s) = (term253 a s)) = ((term249 a s) = (term272 a s)).
Proof. exact (MK_COMB (@lem5198235 a s) (@lem5198246 a s)). Qed.
Lemma lem5198248 (a : real) (s : real -> Prop) : (term249 a s) = (term272 a s).
Proof. exact (EQ_MP (@lem5198247 a s) (@lem5198222 a s)). Qed.
Lemma lem5198249 (a : real) (s : real -> Prop) : (term182 a s) = (term272 a s).
Proof. exact (TRANS (@lem5198218 a s) (@lem5198248 a s)). Qed.
Lemma lem5198250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198251 (a : real) (s : real -> Prop) : (term184 a s) = (term273 a s).
Proof. exact (MK_COMB (@lem5198250) (@lem5198249 a s)). Qed.
Lemma lem5198252 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198253 (a : real) (s : real -> Prop) : (term185 a s) = (term274 a s).
Proof. exact (MK_COMB (@lem5198251 a s) (@lem5198252 a s)). Qed.
Lemma lem5198255 {A : Type'} (P : A -> Prop) (Q : Prop) : (term275 A P Q) = (term276 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5198256 (P : type1014) (Q : Prop) : (term277 P Q) = (term278 P Q).
Proof. exact (@lem5198255 type1627 P Q). Qed.
Lemma lem5198257 (a : real) (s : real -> Prop) : (term279 a s) = (term280 a s).
Proof. exact (@lem5198256 (term271 a s) (term23 a s)). Qed.
Lemma lem5198258 (a : real) (s : real -> Prop) (x : type1627) : (term281 a s x) = (term269 a s x).
Proof. exact (eq_refl (term281 a s x)). Qed.
Lemma lem5198259 (a : real) (s : real -> Prop) : (term282 a s) = (term271 a s).
Proof. exact (fun_ext (fun x : type1627 => @lem5198258 a s x)). Qed.
Lemma lem5198260 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5198261 (a : real) (s : real -> Prop) : (term283 a s) = (term272 a s).
Proof. exact (MK_COMB (@lem5198260) (@lem5198259 a s)). Qed.
Lemma lem5198262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198263 (a : real) (s : real -> Prop) : (term284 a s) = (term273 a s).
Proof. exact (MK_COMB (@lem5198262) (@lem5198261 a s)). Qed.
Lemma lem5198264 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198265 (a : real) (s : real -> Prop) : (term279 a s) = (term274 a s).
Proof. exact (MK_COMB (@lem5198263 a s) (@lem5198264 a s)). Qed.
Lemma lem5198266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198267 (a : real) (s : real -> Prop) : (term285 a s) = (term286 a s).
Proof. exact (MK_COMB (@lem5198266) (@lem5198265 a s)). Qed.
Lemma lem5198268 (a : real) (s : real -> Prop) (x : type1627) : (term281 a s x) = (term269 a s x).
Proof. exact (eq_refl (term281 a s x)). Qed.
Lemma lem5198269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198270 (a : real) (s : real -> Prop) (x : type1627) : (term287 a s x) = (term288 a s x).
Proof. exact (MK_COMB (@lem5198269) (@lem5198268 a s x)). Qed.
Lemma lem5198271 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198272 (x : type1627) (a : real) (s : real -> Prop) : (term289 x a s) = (term290 x a s).
Proof. exact (MK_COMB (@lem5198270 a s x) (@lem5198271 a s)). Qed.
Lemma lem5198273 (a : real) (s : real -> Prop) : (term291 a s) = (term292 a s).
Proof. exact (fun_ext (fun x : type1627 => @lem5198272 x a s)). Qed.
Lemma lem5198274 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5198275 (a : real) (s : real -> Prop) : (term280 a s) = (term293 a s).
Proof. exact (MK_COMB (@lem5198274) (@lem5198273 a s)). Qed.
Lemma lem5198276 (a : real) (s : real -> Prop) : ((term279 a s) = (term280 a s)) = ((term274 a s) = (term293 a s)).
Proof. exact (MK_COMB (@lem5198267 a s) (@lem5198275 a s)). Qed.
Lemma lem5198277 (a : real) (s : real -> Prop) : (term274 a s) = (term293 a s).
Proof. exact (EQ_MP (@lem5198276 a s) (@lem5198257 a s)). Qed.
Lemma lem5198278 (a : real) (s : real -> Prop) : (term185 a s) = (term293 a s).
Proof. exact (TRANS (@lem5198253 a s) (@lem5198277 a s)). Qed.
Lemma lem5198279 (s : real -> Prop) : (term186 s) = (term294 s).
Proof. exact (fun_ext (fun a : real => @lem5198278 a s)). Qed.
Lemma lem5198280 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198281 (s : real -> Prop) : (term187 s) = (term295 s).
Proof. exact (MK_COMB (@lem5198280) (@lem5198279 s)). Qed.
Lemma lem5198283 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5198284 (P : type1617) : (term296 P) = (term297 P).
Proof. exact (@lem5198283 real type1627 P). Qed.
Lemma lem5198285 (s : real -> Prop) : (term298 s) = (term299 s).
Proof. exact (@lem5198284 (term300 s)). Qed.
Lemma lem5198286 (a : real) (s : real -> Prop) : (term301 s a) = (term292 a s).
Proof. exact (eq_refl (term301 s a)). Qed.
Lemma lem5198287 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5198288 (a : real) (s : real -> Prop) (x : type1627) : (term302 s a x) = (term303 a s x).
Proof. exact (MK_COMB (@lem5198286 a s) (@lem5198287 x)). Qed.
Lemma lem5198289 (x : type1627) (a : real) (s : real -> Prop) : (term303 a s x) = (term290 x a s).
Proof. exact (eq_refl (term303 a s x)). Qed.
Lemma lem5198290 (x : type1627) (a : real) (s : real -> Prop) : (term302 s a x) = (term290 x a s).
Proof. exact (TRANS (@lem5198288 a s x) (@lem5198289 x a s)). Qed.
Lemma lem5198291 (a : real) (s : real -> Prop) : (term304 s a) = (term292 a s).
Proof. exact (fun_ext (fun x : type1627 => @lem5198290 x a s)). Qed.
Lemma lem5198292 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5198293 (a : real) (s : real -> Prop) : (term305 s a) = (term293 a s).
Proof. exact (MK_COMB (@lem5198292) (@lem5198291 a s)). Qed.
Lemma lem5198294 (s : real -> Prop) : (term306 s) = (term294 s).
Proof. exact (fun_ext (fun a : real => @lem5198293 a s)). Qed.
Lemma lem5198295 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198296 (s : real -> Prop) : (term298 s) = (term295 s).
Proof. exact (MK_COMB (@lem5198295) (@lem5198294 s)). Qed.
Lemma lem5198297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198298 (s : real -> Prop) : (term307 s) = (term308 s).
Proof. exact (MK_COMB (@lem5198297) (@lem5198296 s)). Qed.
Lemma lem5198299 (a : real) (s : real -> Prop) : (term301 s a) = (term292 a s).
Proof. exact (eq_refl (term301 s a)). Qed.
Lemma lem5198300 (x : type1625) (a : real) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem5198301 (s : real -> Prop) (x : type1625) (a : real) : (term309 s x a) = (term310 s x a).
Proof. exact (MK_COMB (@lem5198299 a s) (@lem5198300 x a)). Qed.
Lemma lem5198302 (x : type1625) (a : real) (s : real -> Prop) : (term310 s x a) = (term311 x a s).
Proof. exact (eq_refl (term310 s x a)). Qed.
Lemma lem5198303 (x : type1625) (a : real) (s : real -> Prop) : (term309 s x a) = (term311 x a s).
Proof. exact (TRANS (@lem5198301 s x a) (@lem5198302 x a s)). Qed.
Lemma lem5198304 (x : type1625) (s : real -> Prop) : (term312 s x) = (term313 x s).
Proof. exact (fun_ext (fun a : real => @lem5198303 x a s)). Qed.
Lemma lem5198305 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198306 (x : type1625) (s : real -> Prop) : (term314 s x) = (term315 x s).
Proof. exact (MK_COMB (@lem5198305) (@lem5198304 x s)). Qed.
Lemma lem5198307 (s : real -> Prop) : (term316 s) = (term317 s).
Proof. exact (fun_ext (fun x : type1625 => @lem5198306 x s)). Qed.
Lemma lem5198308 : (@ex (real -> real -> real -> real)) = (@ex (real -> real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real -> real))). Qed.
Lemma lem5198309 (s : real -> Prop) : (term299 s) = (term318 s).
Proof. exact (MK_COMB (@lem5198308) (@lem5198307 s)). Qed.
Lemma lem5198310 (s : real -> Prop) : ((term298 s) = (term299 s)) = ((term295 s) = (term318 s)).
Proof. exact (MK_COMB (@lem5198298 s) (@lem5198309 s)). Qed.
Lemma lem5198311 (s : real -> Prop) : (term295 s) = (term318 s).
Proof. exact (EQ_MP (@lem5198310 s) (@lem5198285 s)). Qed.
Lemma lem5198312 (s : real -> Prop) : (term187 s) = (term318 s).
Proof. exact (TRANS (@lem5198281 s) (@lem5198311 s)). Qed.
Lemma lem5198313 : term188 = term319.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198312 s)). Qed.
Lemma lem5198314 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198315 : term189 = term320.
Proof. exact (MK_COMB (@lem5198314) (@lem5198313)). Qed.
Lemma lem5198317 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5198318 (P : type1015) : (term321 P) = (term322 P).
Proof. exact (@lem5198317 (real -> Prop) type1625 P). Qed.
Lemma lem5198319 : term323 = term324.
Proof. exact (@lem5198318 term325). Qed.
Lemma lem5198320 (s : real -> Prop) : (term326 s) = (term317 s).
Proof. exact (eq_refl (term326 s)). Qed.
Lemma lem5198321 (x : type1625) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5198322 (s : real -> Prop) (x : type1625) : (term327 s x) = (term328 s x).
Proof. exact (MK_COMB (@lem5198320 s) (@lem5198321 x)). Qed.
Lemma lem5198323 (x : type1625) (s : real -> Prop) : (term328 s x) = (term315 x s).
Proof. exact (eq_refl (term328 s x)). Qed.
Lemma lem5198324 (x : type1625) (s : real -> Prop) : (term327 s x) = (term315 x s).
Proof. exact (TRANS (@lem5198322 s x) (@lem5198323 x s)). Qed.
Lemma lem5198325 (s : real -> Prop) : (term329 s) = (term317 s).
Proof. exact (fun_ext (fun x : type1625 => @lem5198324 x s)). Qed.
Lemma lem5198326 : (@ex (real -> real -> real -> real)) = (@ex (real -> real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real -> real))). Qed.
Lemma lem5198327 (s : real -> Prop) : (term330 s) = (term318 s).
Proof. exact (MK_COMB (@lem5198326) (@lem5198325 s)). Qed.
Lemma lem5198328 : term331 = term319.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198327 s)). Qed.
Lemma lem5198329 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198330 : term323 = term320.
Proof. exact (MK_COMB (@lem5198329) (@lem5198328)). Qed.
Lemma lem5198331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198332 : term332 = term333.
Proof. exact (MK_COMB (@lem5198331) (@lem5198330)). Qed.
Lemma lem5198333 (s : real -> Prop) : (term326 s) = (term317 s).
Proof. exact (eq_refl (term326 s)). Qed.
Lemma lem5198334 (x : type1018) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5198335 (x : type1018) (s : real -> Prop) : (term334 x s) = (term335 x s).
Proof. exact (MK_COMB (@lem5198333 s) (@lem5198334 x s)). Qed.
Lemma lem5198336 (x : type1018) (s : real -> Prop) : (term335 x s) = (term336 x s).
Proof. exact (eq_refl (term335 x s)). Qed.
Lemma lem5198337 (x : type1018) (s : real -> Prop) : (term334 x s) = (term336 x s).
Proof. exact (TRANS (@lem5198335 x s) (@lem5198336 x s)). Qed.
Lemma lem5198338 (x : type1018) : (term337 x) = (term338 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198337 x s)). Qed.
Lemma lem5198339 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198340 (x : type1018) : (term339 x) = (term340 x).
Proof. exact (MK_COMB (@lem5198339) (@lem5198338 x)). Qed.
Lemma lem5198341 : term341 = term342.
Proof. exact (fun_ext (fun x : type1018 => @lem5198340 x)). Qed.
Lemma lem5198342 : (@ex ((real -> Prop) -> real -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real -> real))). Qed.
Lemma lem5198343 : term324 = term343.
Proof. exact (MK_COMB (@lem5198342) (@lem5198341)). Qed.
Lemma lem5198344 : (term323 = term324) = (term320 = term343).
Proof. exact (MK_COMB (@lem5198332) (@lem5198343)). Qed.
Lemma lem5198345 : term320 = term343.
Proof. exact (EQ_MP (@lem5198344) (@lem5198319)). Qed.
Lemma lem5198346 : term189 = term343.
Proof. exact (TRANS (@lem5198315) (@lem5198345)). Qed.
Lemma lem5198347 : term149 = term343.
Proof. exact (TRANS (@lem5198134) (@lem5198346)). Qed.
Lemma lem5198348 : term17 = term343.
Proof. exact (TRANS (@lem5197780) (@lem5198347)). Qed.
Lemma lem5198349 (h1 : term17) : term343.
Proof. exact (EQ_MP (@lem5198348) (@lem5197510 h1)). Qed.
Lemma lem5198350 (x : type1018) (h1 : term340 x) : term340 x.
Proof. exact (h1). Qed.
Lemma lem5198351 (s : real -> Prop) (h1 : term118 s) : term118 s.
Proof. exact (h1). Qed.
Lemma lem5198352 (a : real) (s : real -> Prop) (h1 : term116 a s) : term116 a s.
Proof. exact (h1). Qed.
Lemma lem5198353 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term113 b a s.
Proof. exact (h1). Qed.
Lemma lem5198358 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5198359 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5198358 x)). Qed.
Lemma lem5198360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198361 : term41 = term41.
Proof. exact (MK_COMB (@lem5198360) (@lem5198359)). Qed.
Lemma lem5198362 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem5198361) (@lem5197733 h1)). Qed.
Lemma lem5198369 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198420 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term344 x s a y b) = (term344 x s a y b).
Proof. exact (eq_refl (term344 x s a y b)). Qed.
Lemma lem5198421 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term345 x s a b) = (term345 x s a b).
Proof. exact (fun_ext (fun y : real => @lem5198420 x s a y b)). Qed.
Lemma lem5198422 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198423 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term346 x s a b) = (term346 x s a b).
Proof. exact (MK_COMB (@lem5198422) (@lem5198421 x s a b)). Qed.
Lemma lem5198424 (x : type1018) (s : real -> Prop) (a : real) : (term347 x s a) = (term347 x s a).
Proof. exact (fun_ext (fun b : real => @lem5198423 x s a b)). Qed.
Lemma lem5198425 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198426 (x : type1018) (s : real -> Prop) (a : real) : (term348 x s a) = (term348 x s a).
Proof. exact (MK_COMB (@lem5198425) (@lem5198424 x s a)). Qed.
Lemma lem5198427 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198428 (x : type1018) (s : real -> Prop) (a : real) : (term349 x s a) = (term349 x s a).
Proof. exact (MK_COMB (@lem5198427) (@lem5198426 x s a)). Qed.
Lemma lem5198429 (x : type1018) (a : real) (s : real -> Prop) : (term350 x a s) = (term350 x a s).
Proof. exact (MK_COMB (@lem5198428 x s a) (@lem5198369 a s)). Qed.
Lemma lem5198430 (x : type1018) (s : real -> Prop) : (term351 x s) = (term351 x s).
Proof. exact (fun_ext (fun a : real => @lem5198429 x a s)). Qed.
Lemma lem5198431 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198432 (x : type1018) (s : real -> Prop) : (term336 x s) = (term336 x s).
Proof. exact (MK_COMB (@lem5198431) (@lem5198430 x s)). Qed.
Lemma lem5198433 (x : type1018) : (term338 x) = (term338 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198432 x s)). Qed.
Lemma lem5198434 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198435 (x : type1018) : (term340 x) = (term340 x).
Proof. exact (MK_COMB (@lem5198434) (@lem5198433 x)). Qed.
Lemma lem5198436 (x : type1018) (h1 : term340 x) : term340 x.
Proof. exact (EQ_MP (@lem5198435 x) (@lem5198350 x h1)). Qed.
Lemma lem5198445 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5198450 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5198465 (s : real -> Prop) (x : real) (b : real) : (term51 s x b) = (term51 s x b).
Proof. exact (eq_refl (term51 s x b)). Qed.
Lemma lem5198466 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5198465 s x b)). Qed.
Lemma lem5198467 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198468 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5198467) (@lem5198466 s b)). Qed.
Lemma lem5198469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5198470 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5198469) (@lem5198468 s b)). Qed.
Lemma lem5198471 (b : real) (a : real) (s : real -> Prop) : (term96 b a s) = (term96 b a s).
Proof. exact (MK_COMB (@lem5198470 s b) (@lem5198450 a s)). Qed.
Lemma lem5198472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5198473 (b : real) (a : real) (s : real -> Prop) : (term111 b a s) = (term111 b a s).
Proof. exact (MK_COMB (@lem5198472) (@lem5198471 b a s)). Qed.
Lemma lem5198474 (b : real) (a : real) (s : real -> Prop) : (term113 b a s) = (term113 b a s).
Proof. exact (MK_COMB (@lem5198473 b a s) (@lem5198445 a s)). Qed.
Lemma lem5198475 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term113 b a s.
Proof. exact (EQ_MP (@lem5198474 b a s) (@lem5198353 b a s h1)). Qed.
Lemma lem5198477 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term96 b a s.
Proof. exact (proj1 (@lem5198475 b a s h1)). Qed.
Lemma lem5198479 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term53 s b.
Proof. exact (proj1 (@lem5198477 b a s h1)). Qed.
Lemma lem5198481 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5198482 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5198481 x)). Qed.
Lemma lem5198483 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198485 : term41 = term41.
Proof. exact (MK_COMB (@lem5198483) (@lem5198482)). Qed.
Lemma lem5198486 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem5198485) (@lem5198362 h1)). Qed.
Lemma lem5198488 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5198489 (P : real -> Prop) (Q : Prop) : (term153 P Q) = (term152 P Q).
Proof. exact (@lem5198488 real P Q). Qed.
Lemma lem5198490 (x : type1018) (a : real) (s : real -> Prop) : (term352 x a s) = (term353 x a s).
Proof. exact (@lem5198489 (term347 x s a) (term23 a s)). Qed.
Lemma lem5198491 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term354 x s a b) = (term346 x s a b).
Proof. exact (eq_refl (term354 x s a b)). Qed.
Lemma lem5198492 (x : type1018) (s : real -> Prop) (a : real) : (term355 x s a) = (term347 x s a).
Proof. exact (fun_ext (fun b : real => @lem5198491 x s a b)). Qed.
Lemma lem5198493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198494 (x : type1018) (s : real -> Prop) (a : real) : (term356 x s a) = (term348 x s a).
Proof. exact (MK_COMB (@lem5198493) (@lem5198492 x s a)). Qed.
Lemma lem5198495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198496 (x : type1018) (s : real -> Prop) (a : real) : (term357 x s a) = (term349 x s a).
Proof. exact (MK_COMB (@lem5198495) (@lem5198494 x s a)). Qed.
Lemma lem5198497 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198498 (x : type1018) (a : real) (s : real -> Prop) : (term352 x a s) = (term350 x a s).
Proof. exact (MK_COMB (@lem5198496 x s a) (@lem5198497 a s)). Qed.
Lemma lem5198499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198500 (x : type1018) (a : real) (s : real -> Prop) : (term358 x a s) = (term359 x a s).
Proof. exact (MK_COMB (@lem5198499) (@lem5198498 x a s)). Qed.
Lemma lem5198501 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term354 x s a b) = (term346 x s a b).
Proof. exact (eq_refl (term354 x s a b)). Qed.
Lemma lem5198502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198503 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term360 x s a b) = (term361 x s a b).
Proof. exact (MK_COMB (@lem5198502) (@lem5198501 x s a b)). Qed.
Lemma lem5198504 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198505 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term362 x b a s) = (term363 x b a s).
Proof. exact (MK_COMB (@lem5198503 x s a b) (@lem5198504 a s)). Qed.
Lemma lem5198506 (x : type1018) (a : real) (s : real -> Prop) : (term364 x a s) = (term365 x a s).
Proof. exact (fun_ext (fun b : real => @lem5198505 x b a s)). Qed.
Lemma lem5198507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198508 (x : type1018) (a : real) (s : real -> Prop) : (term353 x a s) = (term366 x a s).
Proof. exact (MK_COMB (@lem5198507) (@lem5198506 x a s)). Qed.
Lemma lem5198509 (x : type1018) (a : real) (s : real -> Prop) : ((term352 x a s) = (term353 x a s)) = ((term350 x a s) = (term366 x a s)).
Proof. exact (MK_COMB (@lem5198500 x a s) (@lem5198508 x a s)). Qed.
Lemma lem5198510 (x : type1018) (a : real) (s : real -> Prop) : (term350 x a s) = (term366 x a s).
Proof. exact (EQ_MP (@lem5198509 x a s) (@lem5198490 x a s)). Qed.
Lemma lem5198512 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5198513 (P : real -> Prop) (Q : Prop) : (term153 P Q) = (term152 P Q).
Proof. exact (@lem5198512 real P Q). Qed.
Lemma lem5198514 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term367 x b a s) = (term368 x b a s).
Proof. exact (@lem5198513 (term345 x s a b) (term23 a s)). Qed.
Lemma lem5198515 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term369 x s a b y) = (term344 x s a y b).
Proof. exact (eq_refl (term369 x s a b y)). Qed.
Lemma lem5198516 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term370 x s a b) = (term345 x s a b).
Proof. exact (fun_ext (fun y : real => @lem5198515 x s a y b)). Qed.
Lemma lem5198517 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198518 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term371 x s a b) = (term346 x s a b).
Proof. exact (MK_COMB (@lem5198517) (@lem5198516 x s a b)). Qed.
Lemma lem5198519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198520 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term372 x s a b) = (term361 x s a b).
Proof. exact (MK_COMB (@lem5198519) (@lem5198518 x s a b)). Qed.
Lemma lem5198521 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198522 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term367 x b a s) = (term363 x b a s).
Proof. exact (MK_COMB (@lem5198520 x s a b) (@lem5198521 a s)). Qed.
Lemma lem5198523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198524 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term373 x b a s) = (term374 x b a s).
Proof. exact (MK_COMB (@lem5198523) (@lem5198522 x b a s)). Qed.
Lemma lem5198525 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term369 x s a b y) = (term344 x s a y b).
Proof. exact (eq_refl (term369 x s a b y)). Qed.
Lemma lem5198526 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198527 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term375 x s a b y) = (term376 x s a y b).
Proof. exact (MK_COMB (@lem5198526) (@lem5198525 x s a y b)). Qed.
Lemma lem5198528 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198529 (x : type1018) (y : real) (b : real) (a : real) (s : real -> Prop) : (term377 x b y a s) = (term378 x y b a s).
Proof. exact (MK_COMB (@lem5198527 x s a y b) (@lem5198528 a s)). Qed.
Lemma lem5198530 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term379 x b a s) = (term380 x b a s).
Proof. exact (fun_ext (fun y : real => @lem5198529 x y b a s)). Qed.
Lemma lem5198531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198532 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term368 x b a s) = (term381 x b a s).
Proof. exact (MK_COMB (@lem5198531) (@lem5198530 x b a s)). Qed.
Lemma lem5198533 (x : type1018) (b : real) (a : real) (s : real -> Prop) : ((term367 x b a s) = (term368 x b a s)) = ((term363 x b a s) = (term381 x b a s)).
Proof. exact (MK_COMB (@lem5198524 x b a s) (@lem5198532 x b a s)). Qed.
Lemma lem5198534 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term363 x b a s) = (term381 x b a s).
Proof. exact (EQ_MP (@lem5198533 x b a s) (@lem5198514 x b a s)). Qed.
Lemma lem5198535 (x : type1018) (a : real) (s : real -> Prop) : (term365 x a s) = (term382 x a s).
Proof. exact (fun_ext (fun b : real => @lem5198534 x b a s)). Qed.
Lemma lem5198536 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198537 (x : type1018) (a : real) (s : real -> Prop) : (term366 x a s) = (term383 x a s).
Proof. exact (MK_COMB (@lem5198536) (@lem5198535 x a s)). Qed.
Lemma lem5198538 (x : type1018) (a : real) (s : real -> Prop) : (term350 x a s) = (term383 x a s).
Proof. exact (TRANS (@lem5198510 x a s) (@lem5198537 x a s)). Qed.
Lemma lem5198539 (x : type1018) (s : real -> Prop) : (term351 x s) = (term384 x s).
Proof. exact (fun_ext (fun a : real => @lem5198538 x a s)). Qed.
Lemma lem5198540 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198541 (x : type1018) (s : real -> Prop) : (term336 x s) = (term385 x s).
Proof. exact (MK_COMB (@lem5198540) (@lem5198539 x s)). Qed.
Lemma lem5198542 (x : type1018) : (term338 x) = (term386 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198541 x s)). Qed.
Lemma lem5198543 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198544 (x : type1018) : (term340 x) = (term387 x).
Proof. exact (MK_COMB (@lem5198543) (@lem5198542 x)). Qed.
Lemma lem5198545 (a : real) (s : real -> Prop) : (term23 a s) = (term23 a s).
Proof. exact (eq_refl (term23 a s)). Qed.
Lemma lem5198562 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term388 x s a y b) = (term389 x s a y b).
Proof. exact (@lem19490 (term390 x a b y s) (term196 a y) (term391 x s a y b)). Qed.
Lemma lem5198565 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5198566 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term344 x s a y b) = (term392 x s a y b).
Proof. exact (MK_COMB (@lem5198565 y s) (@lem5198562 x s a y b)). Qed.
Lemma lem5198573 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term392 x s a y b) = (term393 x s a y b).
Proof. exact (@lem19490 (term394 x a b y s) (term210 y s) (term395 x s a y b)). Qed.
Lemma lem5198574 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term344 x s a y b) = (term393 x s a y b).
Proof. exact (TRANS (@lem5198566 x s a y b) (@lem5198573 x s a y b)). Qed.
Lemma lem5198575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5198576 (x : type1018) (s : real -> Prop) (a : real) (y : real) (b : real) : (term376 x s a y b) = (term396 x s a y b).
Proof. exact (MK_COMB (@lem5198575) (@lem5198574 x s a y b)). Qed.
Lemma lem5198577 (x : type1018) (y : real) (b : real) (a : real) (s : real -> Prop) : (term378 x y b a s) = (term397 x y b a s).
Proof. exact (MK_COMB (@lem5198576 x s a y b) (@lem5198545 a s)). Qed.
Lemma lem5198584 (x : type1018) (y : real) (b : real) (a : real) (s : real -> Prop) : (term397 x y b a s) = (term398 x y b a s).
Proof. exact (@lem19699 (term399 x a b y s) (term400 x s a y b) (term23 a s)). Qed.
Lemma lem5198585 (x : type1018) (y : real) (b : real) (a : real) (s : real -> Prop) : (term378 x y b a s) = (term398 x y b a s).
Proof. exact (TRANS (@lem5198577 x y b a s) (@lem5198584 x y b a s)). Qed.
Lemma lem5198586 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term380 x b a s) = (term401 x b a s).
Proof. exact (fun_ext (fun y : real => @lem5198585 x y b a s)). Qed.
Lemma lem5198587 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198588 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term381 x b a s) = (term402 x b a s).
Proof. exact (MK_COMB (@lem5198587) (@lem5198586 x b a s)). Qed.
Lemma lem5198589 (x : type1018) (a : real) (s : real -> Prop) : (term382 x a s) = (term403 x a s).
Proof. exact (fun_ext (fun b : real => @lem5198588 x b a s)). Qed.
Lemma lem5198590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198591 (x : type1018) (a : real) (s : real -> Prop) : (term383 x a s) = (term404 x a s).
Proof. exact (MK_COMB (@lem5198590) (@lem5198589 x a s)). Qed.
Lemma lem5198592 (x : type1018) (s : real -> Prop) : (term384 x s) = (term405 x s).
Proof. exact (fun_ext (fun a : real => @lem5198591 x a s)). Qed.
Lemma lem5198593 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198594 (x : type1018) (s : real -> Prop) : (term385 x s) = (term406 x s).
Proof. exact (MK_COMB (@lem5198593) (@lem5198592 x s)). Qed.
Lemma lem5198595 (x : type1018) : (term386 x) = (term407 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5198594 x s)). Qed.
Lemma lem5198596 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5198597 (x : type1018) : (term387 x) = (term408 x).
Proof. exact (MK_COMB (@lem5198596) (@lem5198595 x)). Qed.
Lemma lem5198598 (x : type1018) : (term340 x) = (term408 x).
Proof. exact (TRANS (@lem5198544 x) (@lem5198597 x)). Qed.
Lemma lem5198599 (x : type1018) (h1 : term340 x) : term408 x.
Proof. exact (EQ_MP (@lem5198598 x) (@lem5198436 x h1)). Qed.
Lemma lem5198611 (s : real -> Prop) (x : real) (b : real) : (term51 s x b) = (term51 s x b).
Proof. exact (eq_refl (term51 s x b)). Qed.
Lemma lem5198612 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5198611 s x b)). Qed.
Lemma lem5198613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5198615 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5198613) (@lem5198612 s b)). Qed.
Lemma lem5198616 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term53 s b.
Proof. exact (EQ_MP (@lem5198615 s b) (@lem5198479 b a s h1)). Qed.
Lemma lem5198621 (_67854 : real) (h1 : term41) : term409 _67854.
Proof. exact (@lem5198486 h1 _67854). Qed.
Lemma lem5198622 (_67854 : real) : (term409 _67854) = (real_le _67854 _67854).
Proof. exact (eq_refl (term409 _67854)). Qed.
Lemma lem5198624 (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term410 x _67855.
Proof. exact (@lem5198599 x h1 _67855). Qed.
Lemma lem5198625 (x : type1018) (_67855 : real -> Prop) : (term410 x _67855) = (term406 x _67855).
Proof. exact (eq_refl (term410 x _67855)). Qed.
Lemma lem5198626 (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term406 x _67855.
Proof. exact (EQ_MP (@lem5198625 x _67855) (@lem5198624 _67855 x h1)). Qed.
Lemma lem5198627 (_67855 : real -> Prop) (_67856 : real) (x : type1018) (h1 : term340 x) : term411 x _67855 _67856.
Proof. exact (@lem5198626 _67855 x h1 _67856). Qed.
Lemma lem5198628 (x : type1018) (_67856 : real) (_67855 : real -> Prop) : (term411 x _67855 _67856) = (term404 x _67856 _67855).
Proof. exact (eq_refl (term411 x _67855 _67856)). Qed.
Lemma lem5198629 (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term404 x _67856 _67855.
Proof. exact (EQ_MP (@lem5198628 x _67856 _67855) (@lem5198627 _67855 _67856 x h1)). Qed.
Lemma lem5198630 (_67856 : real) (_67855 : real -> Prop) (_67857 : real) (x : type1018) (h1 : term340 x) : term412 x _67856 _67855 _67857.
Proof. exact (@lem5198629 _67856 _67855 x h1 _67857). Qed.
Lemma lem5198631 (x : type1018) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term412 x _67856 _67855 _67857) = (term402 x _67857 _67856 _67855).
Proof. exact (eq_refl (term412 x _67856 _67855 _67857)). Qed.
Lemma lem5198632 (_67857 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term402 x _67857 _67856 _67855.
Proof. exact (EQ_MP (@lem5198631 x _67857 _67856 _67855) (@lem5198630 _67856 _67855 _67857 x h1)). Qed.
Lemma lem5198633 (_67857 : real) (_67856 : real) (_67855 : real -> Prop) (_67858 : real) (x : type1018) (h1 : term340 x) : term413 x _67857 _67856 _67855 _67858.
Proof. exact (@lem5198632 _67857 _67856 _67855 x h1 _67858). Qed.
Lemma lem5198634 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term413 x _67857 _67856 _67855 _67858) = (term398 x _67858 _67857 _67856 _67855).
Proof. exact (eq_refl (term413 x _67857 _67856 _67855 _67858)). Qed.
Lemma lem5198635 (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term398 x _67858 _67857 _67856 _67855.
Proof. exact (EQ_MP (@lem5198634 x _67858 _67857 _67856 _67855) (@lem5198633 _67857 _67856 _67855 _67858 x h1)). Qed.
Lemma lem5198636 (_67859 : real) (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term414 s b _67859.
Proof. exact (@lem5198616 b a s h1 _67859). Qed.
Lemma lem5198637 (s : real -> Prop) (_67859 : real) (b : real) : (term414 s b _67859) = (term51 s _67859 b).
Proof. exact (eq_refl (term414 s b _67859)). Qed.
Lemma lem5198639 (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term415 x _67858 _67857 _67856 _67855.
Proof. exact (proj2 (@lem5198635 _67858 _67857 _67856 _67855 x h1)). Qed.
Lemma lem5198640 (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term416 x _67857 _67858 _67856 _67855.
Proof. exact (proj1 (@lem5198635 _67858 _67857 _67856 _67855 x h1)). Qed.
Lemma lem5198644 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term58 a s.
Proof. exact (proj2 (@lem5198475 b a s h1)). Qed.
Lemma lem5198650 (_67859 : real) (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term51 s _67859 b.
Proof. exact (EQ_MP (@lem5198637 s _67859 b) (@lem5198636 _67859 b a s h1)). Qed.
Lemma lem5198656 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term416 x _67857 _67858 _67856 _67855) = (term417 x _67857 _67858 _67856 _67855).
Proof. exact (@lem5197261 (term210 _67858 _67855) (term394 x _67856 _67857 _67858 _67855) (term23 _67856 _67855)). Qed.
Lemma lem5198663 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term418 x _67857 _67858 _67856 _67855) = (term419 x _67857 _67858 _67856 _67855).
Proof. exact (@lem5197261 (term196 _67856 _67858) (term390 x _67856 _67857 _67858 _67855) (term23 _67856 _67855)). Qed.
Lemma lem5198664 (_67858 : real) (_67855 : real -> Prop) : (term134 _67858 _67855) = (term134 _67858 _67855).
Proof. exact (eq_refl (term134 _67858 _67855)). Qed.
Lemma lem5198667 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term417 x _67857 _67858 _67856 _67855) = (term420 x _67857 _67858 _67856 _67855).
Proof. exact (MK_COMB (@lem5198664 _67858 _67855) (@lem5198663 x _67857 _67858 _67856 _67855)). Qed.
Lemma lem5198669 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term416 x _67857 _67858 _67856 _67855) = (term420 x _67857 _67858 _67856 _67855).
Proof. exact (TRANS (@lem5198656 x _67857 _67858 _67856 _67855) (@lem5198667 x _67857 _67858 _67856 _67855)). Qed.
Lemma lem5198670 (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term420 x _67857 _67858 _67856 _67855.
Proof. exact (EQ_MP (@lem5198669 x _67857 _67858 _67856 _67855) (@lem5198640 _67857 _67858 _67856 _67855 x h1)). Qed.
Lemma lem5198674 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term415 x _67858 _67857 _67856 _67855) = (term421 x _67858 _67857 _67856 _67855).
Proof. exact (@lem5197261 (term210 _67858 _67855) (term395 x _67855 _67856 _67858 _67857) (term23 _67856 _67855)). Qed.
Lemma lem5198681 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term422 x _67858 _67857 _67856 _67855) = (term423 x _67858 _67857 _67856 _67855).
Proof. exact (@lem5197261 (term196 _67856 _67858) (term391 x _67855 _67856 _67858 _67857) (term23 _67856 _67855)). Qed.
Lemma lem5198682 (_67858 : real) (_67855 : real -> Prop) : (term134 _67858 _67855) = (term134 _67858 _67855).
Proof. exact (eq_refl (term134 _67858 _67855)). Qed.
Lemma lem5198685 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term421 x _67858 _67857 _67856 _67855) = (term424 x _67858 _67857 _67856 _67855).
Proof. exact (MK_COMB (@lem5198682 _67858 _67855) (@lem5198681 x _67858 _67857 _67856 _67855)). Qed.
Lemma lem5198687 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term415 x _67858 _67857 _67856 _67855) = (term424 x _67858 _67857 _67856 _67855).
Proof. exact (TRANS (@lem5198674 x _67858 _67857 _67856 _67855) (@lem5198685 x _67858 _67857 _67856 _67855)). Qed.
Lemma lem5198688 (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term424 x _67858 _67857 _67856 _67855.
Proof. exact (EQ_MP (@lem5198687 x _67858 _67857 _67856 _67855) (@lem5198639 _67858 _67857 _67856 _67855 x h1)). Qed.
Lemma lem5198690 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : @IN real a s.
Proof. exact (proj2 (@lem5198477 b a s h1)). Qed.
Lemma lem5198691 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term425 a s.
Proof. exact (fun h0 : term210 a s => @lem5198690 b a s h1). Qed.
Lemma lem5198693 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5198694 (a : real) (s : real -> Prop) : (term425 a s) = (@IN real a s).
Proof. exact (@lem5198693 (@IN real a s)). Qed.
Lemma lem5198695 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : @IN real a s.
Proof. exact (EQ_MP (@lem5198694 a s) (@lem5198691 b a s h1)). Qed.
Lemma lem5198697 (_67854 : real) (h1 : term41) : real_le _67854 _67854.
Proof. exact (EQ_MP (@lem5198622 _67854) (@lem5198621 _67854 h1)). Qed.
Lemma lem5198698 (a : real) (h1 : term41) : real_le a a.
Proof. exact (@lem5198697 a h1). Qed.
Lemma lem5198699 (a : real) (h1 : term41) : term427 a.
Proof. exact (fun h0 : term428 a => @lem5198698 a h1). Qed.
Lemma lem5198701 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5198702 (a : real) : (term427 a) = (real_le a a).
Proof. exact (@lem5198701 (real_le a a)). Qed.
Lemma lem5198703 (a : real) (h1 : term41) : real_le a a.
Proof. exact (EQ_MP (@lem5198702 a) (@lem5198699 a h1)). Qed.
Lemma lem5198705 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : @IN real a s.
Proof. exact (proj2 (@lem5198477 b a s h1)). Qed.
Lemma lem5198706 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term425 a s.
Proof. exact (fun h0 : term210 a s => @lem5198705 b a s h1). Qed.
Lemma lem5198708 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5198709 (a : real) (s : real -> Prop) : (term425 a s) = (@IN real a s).
Proof. exact (@lem5198708 (@IN real a s)). Qed.
Lemma lem5198710 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : @IN real a s.
Proof. exact (EQ_MP (@lem5198709 a s) (@lem5198706 b a s h1)). Qed.
Lemma lem5198712 (_67854 : real) (h1 : term41) : real_le _67854 _67854.
Proof. exact (EQ_MP (@lem5198622 _67854) (@lem5198621 _67854 h1)). Qed.
Lemma lem5198713 (a : real) (h1 : term41) : real_le a a.
Proof. exact (@lem5198712 a h1). Qed.
Lemma lem5198714 (a : real) (h1 : term41) : term427 a.
Proof. exact (fun h0 : term428 a => @lem5198713 a h1). Qed.
Lemma lem5198716 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5198717 (a : real) : (term427 a) = (real_le a a).
Proof. exact (@lem5198716 (real_le a a)). Qed.
Lemma lem5198718 (a : real) (h1 : term41) : real_le a a.
Proof. exact (EQ_MP (@lem5198717 a) (@lem5198714 a h1)). Qed.
Lemma lem5198721 (a : real) (s : real -> Prop) (h1 : term58 a s) : term58 a s.
Proof. exact (h1). Qed.
Lemma lem5198722 (a : real) (s : real -> Prop) (h1 : term58 a s) : term429 a s.
Proof. exact (fun h0 : term23 a s => @lem5198721 a s h1). Qed.
Lemma lem5198724 (p : Prop) : (term430 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5198725 (a : real) (s : real -> Prop) : (term429 a s) = (term58 a s).
Proof. exact (@lem5198724 (term23 a s)). Qed.
Lemma lem5198726 (a : real) (s : real -> Prop) (h1 : term58 a s) : term58 a s.
Proof. exact (EQ_MP (@lem5198725 a s) (@lem5198722 a s h1)). Qed.
Lemma lem5198742 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5198743 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term419 x _67857 _67858 _67856 _67855) = (term431 x _67857 _67858 _67856 _67855).
Proof. exact (@lem5198742 (term390 x _67856 _67857 _67858 _67855) (term196 _67856 _67858) (term23 _67856 _67855)). Qed.
Lemma lem5198757 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5198758 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term432 _67858 _67856 _67855) = (term433 _67855 _67856 _67858).
Proof. exact (@lem5198757 (term23 _67856 _67855) (term196 _67856 _67858)). Qed.
Lemma lem5198764 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term434 x _67856 _67857 _67858 _67855) = (term434 x _67856 _67857 _67858 _67855).
Proof. exact (eq_refl (term434 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198765 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term431 x _67857 _67858 _67856 _67855) = (term435 x _67857 _67855 _67856 _67858).
Proof. exact (MK_COMB (@lem5198764 x _67856 _67857 _67858 _67855) (@lem5198758 _67855 _67856 _67858)). Qed.
Lemma lem5198776 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term419 x _67857 _67858 _67856 _67855) = (term435 x _67857 _67855 _67856 _67858).
Proof. exact (TRANS (@lem5198743 x _67857 _67858 _67856 _67855) (@lem5198765 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198777 (_67858 : real) (_67855 : real -> Prop) : (term134 _67858 _67855) = (term134 _67858 _67855).
Proof. exact (eq_refl (term134 _67858 _67855)). Qed.
Lemma lem5198778 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term420 x _67857 _67858 _67856 _67855) = (term436 x _67857 _67855 _67856 _67858).
Proof. exact (MK_COMB (@lem5198777 _67858 _67855) (@lem5198776 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198782 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5198783 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term436 x _67857 _67855 _67856 _67858) = (term437 x _67857 _67855 _67856 _67858).
Proof. exact (@lem5198782 (term390 x _67856 _67857 _67858 _67855) (term210 _67858 _67855) (term433 _67855 _67856 _67858)). Qed.
Lemma lem5198797 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5198798 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term438 _67855 _67856 _67858) = (term439 _67855 _67856 _67858).
Proof. exact (@lem5198797 (term23 _67856 _67855) (term210 _67858 _67855) (term196 _67856 _67858)). Qed.
Lemma lem5198814 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term434 x _67856 _67857 _67858 _67855) = (term434 x _67856 _67857 _67858 _67855).
Proof. exact (eq_refl (term434 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198815 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term437 x _67857 _67855 _67856 _67858) = (term440 x _67857 _67855 _67856 _67858).
Proof. exact (MK_COMB (@lem5198814 x _67856 _67857 _67858 _67855) (@lem5198798 _67855 _67856 _67858)). Qed.
Lemma lem5198826 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term436 x _67857 _67855 _67856 _67858) = (term440 x _67857 _67855 _67856 _67858).
Proof. exact (TRANS (@lem5198783 x _67857 _67855 _67856 _67858) (@lem5198815 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198827 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term420 x _67857 _67858 _67856 _67855) = (term440 x _67857 _67855 _67856 _67858).
Proof. exact (TRANS (@lem5198778 x _67857 _67855 _67856 _67858) (@lem5198826 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198829 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term441 x _67857 _67858 _67856 _67855) = (term442 x _67857 _67855 _67856 _67858).
Proof. exact (MK_COMB (@lem5198828) (@lem5198827 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198853 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5198854 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term432 _67858 _67856 _67855) = (term433 _67855 _67856 _67858).
Proof. exact (@lem5198853 (term23 _67856 _67855) (term196 _67856 _67858)). Qed.
Lemma lem5198860 (_67858 : real) (_67855 : real -> Prop) : (term134 _67858 _67855) = (term134 _67858 _67855).
Proof. exact (eq_refl (term134 _67858 _67855)). Qed.
Lemma lem5198861 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term443 _67858 _67856 _67855) = (term438 _67855 _67856 _67858).
Proof. exact (MK_COMB (@lem5198860 _67858 _67855) (@lem5198854 _67855 _67856 _67858)). Qed.
Lemma lem5198865 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5198866 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term438 _67855 _67856 _67858) = (term439 _67855 _67856 _67858).
Proof. exact (@lem5198865 (term23 _67856 _67855) (term210 _67858 _67855) (term196 _67856 _67858)). Qed.
Lemma lem5198882 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term443 _67858 _67856 _67855) = (term439 _67855 _67856 _67858).
Proof. exact (TRANS (@lem5198861 _67855 _67856 _67858) (@lem5198866 _67855 _67856 _67858)). Qed.
Lemma lem5198883 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term434 x _67856 _67857 _67858 _67855) = (term434 x _67856 _67857 _67858 _67855).
Proof. exact (eq_refl (term434 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198884 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : (term444 x _67857 _67858 _67856 _67855) = (term440 x _67857 _67855 _67856 _67858).
Proof. exact (MK_COMB (@lem5198883 x _67856 _67857 _67858 _67855) (@lem5198882 _67855 _67856 _67858)). Qed.
Lemma lem5198895 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : ((term420 x _67857 _67858 _67856 _67855) = (term444 x _67857 _67858 _67856 _67855)) = ((term440 x _67857 _67855 _67856 _67858) = (term440 x _67857 _67855 _67856 _67858)).
Proof. exact (MK_COMB (@lem5198829 x _67857 _67855 _67856 _67858) (@lem5198884 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198897 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5198898 (x : Prop) : (x = x) = True.
Proof. exact (@lem5198897 Prop x). Qed.
Lemma lem5198899 (x : type1018) (_67857 : real) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) : ((term440 x _67857 _67855 _67856 _67858) = (term440 x _67857 _67855 _67856 _67858)) = True.
Proof. exact (@lem5198898 (term440 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198900 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : ((term420 x _67857 _67858 _67856 _67855) = (term444 x _67857 _67858 _67856 _67855)) = True.
Proof. exact (TRANS (@lem5198895 x _67857 _67855 _67856 _67858) (@lem5198899 x _67857 _67855 _67856 _67858)). Qed.
Lemma lem5198901 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : True = ((term420 x _67857 _67858 _67856 _67855) = (term444 x _67857 _67858 _67856 _67855)).
Proof. exact (SYM (@lem5198900 x _67857 _67858 _67856 _67855)). Qed.
Lemma lem5198902 (x : type1018) (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term420 x _67857 _67858 _67856 _67855) = (term444 x _67857 _67858 _67856 _67855).
Proof. exact (EQ_MP (@lem5198901 x _67857 _67858 _67856 _67855) (@lem0)). Qed.
Lemma lem5198903 (_67857 : real) (_67858 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term444 x _67857 _67858 _67856 _67855.
Proof. exact (EQ_MP (@lem5198902 x _67857 _67858 _67856 _67855) (@lem5198670 _67857 _67858 _67856 _67855 x h1)). Qed.
Lemma lem5198905 (b : Prop) (a : Prop) : (a \/ b) = (term445 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5198906 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term444 x _67857 _67858 _67856 _67855) = (term446 x _67856 _67857 _67858 _67855).
Proof. exact (@lem5198905 (term443 _67858 _67856 _67855) (term390 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198908 (a : Prop) (b : Prop) : (term447 a b) = (term448 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5198909 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term449 _67858 _67856 _67855) = (term450 _67858 _67856 _67855).
Proof. exact (@lem5198908 (term210 _67858 _67855) (term432 _67858 _67856 _67855)). Qed.
Lemma lem5198911 (a : Prop) : (term451 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5198912 (_67858 : real) (_67855 : real -> Prop) : (term452 _67858 _67855) = (@IN real _67858 _67855).
Proof. exact (@lem5198911 (@IN real _67858 _67855)). Qed.
Lemma lem5198913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5198914 (_67858 : real) (_67855 : real -> Prop) : (term453 _67858 _67855) = (term29 _67858 _67855).
Proof. exact (MK_COMB (@lem5198913) (@lem5198912 _67858 _67855)). Qed.
Lemma lem5198916 (a : Prop) (b : Prop) : (term447 a b) = (term448 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5198917 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term454 _67858 _67856 _67855) = (term455 _67858 _67856 _67855).
Proof. exact (@lem5198916 (term196 _67856 _67858) (term23 _67856 _67855)). Qed.
Lemma lem5198919 (a : Prop) : (term451 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5198920 (_67856 : real) (_67858 : real) : (term456 _67856 _67858) = (real_le _67856 _67858).
Proof. exact (@lem5198919 (real_le _67856 _67858)). Qed.
Lemma lem5198921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5198922 (_67856 : real) (_67858 : real) : (term457 _67856 _67858) = (term27 _67856 _67858).
Proof. exact (MK_COMB (@lem5198921) (@lem5198920 _67856 _67858)). Qed.
Lemma lem5198923 (_67856 : real) (_67855 : real -> Prop) : (term58 _67856 _67855) = (term58 _67856 _67855).
Proof. exact (eq_refl (term58 _67856 _67855)). Qed.
Lemma lem5198924 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term455 _67858 _67856 _67855) = (term458 _67858 _67856 _67855).
Proof. exact (MK_COMB (@lem5198922 _67856 _67858) (@lem5198923 _67856 _67855)). Qed.
Lemma lem5198925 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term454 _67858 _67856 _67855) = (term458 _67858 _67856 _67855).
Proof. exact (TRANS (@lem5198917 _67858 _67856 _67855) (@lem5198924 _67858 _67856 _67855)). Qed.
Lemma lem5198926 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term450 _67858 _67856 _67855) = (term459 _67858 _67856 _67855).
Proof. exact (MK_COMB (@lem5198914 _67858 _67855) (@lem5198925 _67858 _67856 _67855)). Qed.
Lemma lem5198927 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term449 _67858 _67856 _67855) = (term459 _67858 _67856 _67855).
Proof. exact (TRANS (@lem5198909 _67858 _67856 _67855) (@lem5198926 _67858 _67856 _67855)). Qed.
Lemma lem5198928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5198929 (_67858 : real) (_67856 : real) (_67855 : real -> Prop) : (term460 _67858 _67856 _67855) = (term461 _67858 _67856 _67855).
Proof. exact (MK_COMB (@lem5198928) (@lem5198927 _67858 _67856 _67855)). Qed.
Lemma lem5198930 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term390 x _67856 _67857 _67858 _67855) = (term390 x _67856 _67857 _67858 _67855).
Proof. exact (eq_refl (term390 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198931 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term446 x _67856 _67857 _67858 _67855) = (term462 x _67856 _67857 _67858 _67855).
Proof. exact (MK_COMB (@lem5198929 _67858 _67856 _67855) (@lem5198930 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198932 (x : type1018) (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) : (term444 x _67857 _67858 _67856 _67855) = (term462 x _67856 _67857 _67858 _67855).
Proof. exact (TRANS (@lem5198906 x _67856 _67857 _67858 _67855) (@lem5198931 x _67856 _67857 _67858 _67855)). Qed.
Lemma lem5198934 (a : real) (s : real -> Prop) (h1 : term41) (h2 : term58 a s) : term463 a s.
Proof. exact (conj (@lem5198718 a h1) (@lem5198726 a s h2)). Qed.
Lemma lem5198935 (b : real) (a : real) (s : real -> Prop) (h1 : term41) (h2 : term58 a s) (h3 : term113 b a s) : term464 a s.
Proof. exact (conj (@lem5198710 b a s h3) (@lem5198934 a s h1 h2)). Qed.
Lemma lem5198937 (_67856 : real) (_67857 : real) (_67858 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term462 x _67856 _67857 _67858 _67855.
Proof. exact (EQ_MP (@lem5198932 x _67856 _67857 _67858 _67855) (@lem5198903 _67857 _67858 _67856 _67855 x h1)). Qed.
Lemma lem5198938 (_67857 : real) (a : real) (s : real -> Prop) (x : type1018) (h1 : term340 x) : term465 x _67857 a s.
Proof. exact (@lem5198937 a _67857 a s x h1). Qed.
Lemma lem5198941 (_67857 : real) (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term466 x _67857 a s.
Proof. exact (@lem5198938 _67857 a s x h1 (@lem5198935 b a s h2 h3 h4)). Qed.
Lemma lem5198942 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term466 x b a s.
Proof. exact (@lem5198941 b x b a s h1 h2 h3 h4). Qed.
Lemma lem5198943 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term467 x b a s.
Proof. exact (fun h0 : term468 x b a s => @lem5198942 x b a s h1 h2 h3 h4). Qed.
Lemma lem5198945 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5198946 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term467 x b a s) = (term466 x b a s).
Proof. exact (@lem5198945 (term466 x b a s)). Qed.
Lemma lem5198947 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term466 x b a s.
Proof. exact (EQ_MP (@lem5198946 x b a s) (@lem5198943 x b a s h1 h2 h3 h4)). Qed.
Lemma lem5198953 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5198954 (b : real) (_67859 : real) (s : real -> Prop) : (term51 s _67859 b) = (term469 b _67859 s).
Proof. exact (@lem5198953 (real_le _67859 b) (term210 _67859 s)). Qed.
Lemma lem5198960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5198961 (b : real) (_67859 : real) (s : real -> Prop) : (term470 s _67859 b) = (term471 b _67859 s).
Proof. exact (MK_COMB (@lem5198960) (@lem5198954 b _67859 s)). Qed.
Lemma lem5198967 (b : real) (_67859 : real) (s : real -> Prop) : (term469 b _67859 s) = (term469 b _67859 s).
Proof. exact (eq_refl (term469 b _67859 s)). Qed.
Lemma lem5198968 (b : real) (_67859 : real) (s : real -> Prop) : ((term51 s _67859 b) = (term469 b _67859 s)) = ((term469 b _67859 s) = (term469 b _67859 s)).
Proof. exact (MK_COMB (@lem5198961 b _67859 s) (@lem5198967 b _67859 s)). Qed.
Lemma lem5198970 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5198971 (x : Prop) : (x = x) = True.
Proof. exact (@lem5198970 Prop x). Qed.
Lemma lem5198972 (b : real) (_67859 : real) (s : real -> Prop) : ((term469 b _67859 s) = (term469 b _67859 s)) = True.
Proof. exact (@lem5198971 (term469 b _67859 s)). Qed.
Lemma lem5198973 (b : real) (_67859 : real) (s : real -> Prop) : ((term51 s _67859 b) = (term469 b _67859 s)) = True.
Proof. exact (TRANS (@lem5198968 b _67859 s) (@lem5198972 b _67859 s)). Qed.
Lemma lem5198974 (b : real) (_67859 : real) (s : real -> Prop) : True = ((term51 s _67859 b) = (term469 b _67859 s)).
Proof. exact (SYM (@lem5198973 b _67859 s)). Qed.
Lemma lem5198975 (b : real) (_67859 : real) (s : real -> Prop) : (term51 s _67859 b) = (term469 b _67859 s).
Proof. exact (EQ_MP (@lem5198974 b _67859 s) (@lem0)). Qed.
Lemma lem5198976 (_67859 : real) (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term469 b _67859 s.
Proof. exact (EQ_MP (@lem5198975 b _67859 s) (@lem5198650 _67859 b a s h1)). Qed.
Lemma lem5198978 (b : Prop) (a : Prop) : (a \/ b) = (term445 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5198979 (s : real -> Prop) (_67859 : real) (b : real) : (term469 b _67859 s) = (term472 s _67859 b).
Proof. exact (@lem5198978 (term210 _67859 s) (real_le _67859 b)). Qed.
Lemma lem5198981 (a : Prop) : (term451 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5198982 (_67859 : real) (s : real -> Prop) : (term452 _67859 s) = (@IN real _67859 s).
Proof. exact (@lem5198981 (@IN real _67859 s)). Qed.
Lemma lem5198983 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5198984 (_67859 : real) (s : real -> Prop) : (term473 _67859 s) = (term474 _67859 s).
Proof. exact (MK_COMB (@lem5198983) (@lem5198982 _67859 s)). Qed.
Lemma lem5198985 (_67859 : real) (b : real) : (real_le _67859 b) = (real_le _67859 b).
Proof. exact (eq_refl (real_le _67859 b)). Qed.
Lemma lem5198986 (s : real -> Prop) (_67859 : real) (b : real) : (term472 s _67859 b) = (term24 s _67859 b).
Proof. exact (MK_COMB (@lem5198984 _67859 s) (@lem5198985 _67859 b)). Qed.
Lemma lem5198987 (s : real -> Prop) (_67859 : real) (b : real) : (term469 b _67859 s) = (term24 s _67859 b).
Proof. exact (TRANS (@lem5198979 s _67859 b) (@lem5198986 s _67859 b)). Qed.
Lemma lem5198990 (_67859 : real) (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term24 s _67859 b.
Proof. exact (EQ_MP (@lem5198987 s _67859 b) (@lem5198976 _67859 b a s h1)). Qed.
Lemma lem5198991 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term475 x s a b.
Proof. exact (@lem5198990 (x s a b a) b a s h1). Qed.
Lemma lem5198994 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term476 x s a b.
Proof. exact (@lem5198991 x b a s h4 (@lem5198947 x b a s h1 h2 h3 h4)). Qed.
Lemma lem5198995 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term477 x s a b.
Proof. exact (fun h0 : term478 x s a b => @lem5198994 x b a s h1 h2 h3 h4). Qed.
Lemma lem5198997 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5198998 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term477 x s a b) = (term476 x s a b).
Proof. exact (@lem5198997 (term476 x s a b)). Qed.
Lemma lem5198999 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term476 x s a b.
Proof. exact (EQ_MP (@lem5198998 x s a b) (@lem5198995 x b a s h1 h2 h3 h4)). Qed.
Lemma lem5199025 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5199026 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term479 x _67858 _67857 _67856 _67855) = (term480 x _67855 _67856 _67858 _67857).
Proof. exact (@lem5199025 (term23 _67856 _67855) (term391 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199032 (_67856 : real) (_67858 : real) : (term130 _67856 _67858) = (term130 _67856 _67858).
Proof. exact (eq_refl (term130 _67856 _67858)). Qed.
Lemma lem5199033 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term423 x _67858 _67857 _67856 _67855) = (term481 x _67855 _67856 _67858 _67857).
Proof. exact (MK_COMB (@lem5199032 _67856 _67858) (@lem5199026 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199037 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5199038 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term481 x _67855 _67856 _67858 _67857) = (term482 x _67855 _67856 _67858 _67857).
Proof. exact (@lem5199037 (term23 _67856 _67855) (term196 _67856 _67858) (term391 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199054 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term423 x _67858 _67857 _67856 _67855) = (term482 x _67855 _67856 _67858 _67857).
Proof. exact (TRANS (@lem5199033 x _67855 _67856 _67858 _67857) (@lem5199038 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199055 (_67858 : real) (_67855 : real -> Prop) : (term134 _67858 _67855) = (term134 _67858 _67855).
Proof. exact (eq_refl (term134 _67858 _67855)). Qed.
Lemma lem5199056 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term424 x _67858 _67857 _67856 _67855) = (term483 x _67855 _67856 _67858 _67857).
Proof. exact (MK_COMB (@lem5199055 _67858 _67855) (@lem5199054 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199060 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5199061 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term483 x _67855 _67856 _67858 _67857) = (term484 x _67855 _67856 _67858 _67857).
Proof. exact (@lem5199060 (term23 _67856 _67855) (term210 _67858 _67855) (term395 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199087 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term424 x _67858 _67857 _67856 _67855) = (term484 x _67855 _67856 _67858 _67857).
Proof. exact (TRANS (@lem5199056 x _67855 _67856 _67858 _67857) (@lem5199061 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5199089 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term485 x _67858 _67857 _67856 _67855) = (term486 x _67855 _67856 _67858 _67857).
Proof. exact (MK_COMB (@lem5199088) (@lem5199087 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199115 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term484 x _67855 _67856 _67858 _67857) = (term484 x _67855 _67856 _67858 _67857).
Proof. exact (eq_refl (term484 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199116 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : ((term424 x _67858 _67857 _67856 _67855) = (term484 x _67855 _67856 _67858 _67857)) = ((term484 x _67855 _67856 _67858 _67857) = (term484 x _67855 _67856 _67858 _67857)).
Proof. exact (MK_COMB (@lem5199089 x _67855 _67856 _67858 _67857) (@lem5199115 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199118 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5199119 (x : Prop) : (x = x) = True.
Proof. exact (@lem5199118 Prop x). Qed.
Lemma lem5199120 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : ((term484 x _67855 _67856 _67858 _67857) = (term484 x _67855 _67856 _67858 _67857)) = True.
Proof. exact (@lem5199119 (term484 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199121 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : ((term424 x _67858 _67857 _67856 _67855) = (term484 x _67855 _67856 _67858 _67857)) = True.
Proof. exact (TRANS (@lem5199116 x _67855 _67856 _67858 _67857) (@lem5199120 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199122 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : True = ((term424 x _67858 _67857 _67856 _67855) = (term484 x _67855 _67856 _67858 _67857)).
Proof. exact (SYM (@lem5199121 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199123 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term424 x _67858 _67857 _67856 _67855) = (term484 x _67855 _67856 _67858 _67857).
Proof. exact (EQ_MP (@lem5199122 x _67855 _67856 _67858 _67857) (@lem0)). Qed.
Lemma lem5199124 (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) (x : type1018) (h1 : term340 x) : term484 x _67855 _67856 _67858 _67857.
Proof. exact (EQ_MP (@lem5199123 x _67855 _67856 _67858 _67857) (@lem5198688 _67858 _67857 _67856 _67855 x h1)). Qed.
Lemma lem5199126 (b : Prop) (a : Prop) : (a \/ b) = (term445 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5199127 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term484 x _67855 _67856 _67858 _67857) = (term487 x _67858 _67857 _67856 _67855).
Proof. exact (@lem5199126 (term400 x _67855 _67856 _67858 _67857) (term23 _67856 _67855)). Qed.
Lemma lem5199129 (a : Prop) (b : Prop) : (term447 a b) = (term448 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5199130 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term488 x _67855 _67856 _67858 _67857) = (term489 x _67855 _67856 _67858 _67857).
Proof. exact (@lem5199129 (term210 _67858 _67855) (term395 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199132 (a : Prop) : (term451 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5199133 (_67858 : real) (_67855 : real -> Prop) : (term452 _67858 _67855) = (@IN real _67858 _67855).
Proof. exact (@lem5199132 (@IN real _67858 _67855)). Qed.
Lemma lem5199134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5199135 (_67858 : real) (_67855 : real -> Prop) : (term453 _67858 _67855) = (term29 _67858 _67855).
Proof. exact (MK_COMB (@lem5199134) (@lem5199133 _67858 _67855)). Qed.
Lemma lem5199137 (a : Prop) (b : Prop) : (term447 a b) = (term448 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5199138 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term490 x _67855 _67856 _67858 _67857) = (term491 x _67855 _67856 _67858 _67857).
Proof. exact (@lem5199137 (term196 _67856 _67858) (term391 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199140 (a : Prop) : (term451 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5199141 (_67856 : real) (_67858 : real) : (term456 _67856 _67858) = (real_le _67856 _67858).
Proof. exact (@lem5199140 (real_le _67856 _67858)). Qed.
Lemma lem5199142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5199143 (_67856 : real) (_67858 : real) : (term457 _67856 _67858) = (term27 _67856 _67858).
Proof. exact (MK_COMB (@lem5199142) (@lem5199141 _67856 _67858)). Qed.
Lemma lem5199145 (a : Prop) : (term451 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5199146 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term492 x _67855 _67856 _67858 _67857) = (term493 x _67855 _67856 _67858 _67857).
Proof. exact (@lem5199145 (term493 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199147 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term491 x _67855 _67856 _67858 _67857) = (term494 x _67855 _67856 _67858 _67857).
Proof. exact (MK_COMB (@lem5199143 _67856 _67858) (@lem5199146 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199148 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term490 x _67855 _67856 _67858 _67857) = (term494 x _67855 _67856 _67858 _67857).
Proof. exact (TRANS (@lem5199138 x _67855 _67856 _67858 _67857) (@lem5199147 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199149 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term489 x _67855 _67856 _67858 _67857) = (term495 x _67855 _67856 _67858 _67857).
Proof. exact (MK_COMB (@lem5199135 _67858 _67855) (@lem5199148 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199150 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term488 x _67855 _67856 _67858 _67857) = (term495 x _67855 _67856 _67858 _67857).
Proof. exact (TRANS (@lem5199130 x _67855 _67856 _67858 _67857) (@lem5199149 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5199152 (x : type1018) (_67855 : real -> Prop) (_67856 : real) (_67858 : real) (_67857 : real) : (term496 x _67855 _67856 _67858 _67857) = (term497 x _67855 _67856 _67858 _67857).
Proof. exact (MK_COMB (@lem5199151) (@lem5199150 x _67855 _67856 _67858 _67857)). Qed.
Lemma lem5199153 (_67856 : real) (_67855 : real -> Prop) : (term23 _67856 _67855) = (term23 _67856 _67855).
Proof. exact (eq_refl (term23 _67856 _67855)). Qed.
Lemma lem5199154 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term487 x _67858 _67857 _67856 _67855) = (term498 x _67858 _67857 _67856 _67855).
Proof. exact (MK_COMB (@lem5199152 x _67855 _67856 _67858 _67857) (@lem5199153 _67856 _67855)). Qed.
Lemma lem5199155 (x : type1018) (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) : (term484 x _67855 _67856 _67858 _67857) = (term498 x _67858 _67857 _67856 _67855).
Proof. exact (TRANS (@lem5199127 x _67858 _67857 _67856 _67855) (@lem5199154 x _67858 _67857 _67856 _67855)). Qed.
Lemma lem5199157 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term499 x s a b.
Proof. exact (conj (@lem5198703 a h2) (@lem5198999 x b a s h1 h2 h3 h4)). Qed.
Lemma lem5199158 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term500 x s a b.
Proof. exact (conj (@lem5198695 b a s h4) (@lem5199157 x b a s h1 h2 h3 h4)). Qed.
Lemma lem5199160 (_67858 : real) (_67857 : real) (_67856 : real) (_67855 : real -> Prop) (x : type1018) (h1 : term340 x) : term498 x _67858 _67857 _67856 _67855.
Proof. exact (EQ_MP (@lem5199155 x _67858 _67857 _67856 _67855) (@lem5199124 _67855 _67856 _67858 _67857 x h1)). Qed.
Lemma lem5199161 (b : real) (a : real) (s : real -> Prop) (x : type1018) (h1 : term340 x) : term501 x b a s.
Proof. exact (@lem5199160 a b a s x h1). Qed.
Lemma lem5199164 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term58 a s) (h4 : term113 b a s) : term23 a s.
Proof. exact (@lem5199161 b a s x h1 (@lem5199158 x b a s h1 h2 h3 h4)). Qed.
Lemma lem5199165 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : term502 a s.
Proof. exact (fun h0 : term58 a s => @lem5199164 x b a s h1 h2 h0 h3). Qed.
Lemma lem5199167 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5199168 (a : real) (s : real -> Prop) : (term502 a s) = (term23 a s).
Proof. exact (@lem5199167 (term23 a s)). Qed.
Lemma lem5199169 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : term23 a s.
Proof. exact (EQ_MP (@lem5199168 a s) (@lem5199165 x b a s h1 h2 h3)). Qed.
Lemma lem5199172 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5199174 (a : real) (s : real -> Prop) : (term58 a s) = (term503 a s).
Proof. exact (@lem5199172 (term23 a s)). Qed.
Lemma lem5199177 (b : real) (a : real) (s : real -> Prop) (h1 : term113 b a s) : term503 a s.
Proof. exact (EQ_MP (@lem5199174 a s) (@lem5198644 b a s h1)). Qed.
Lemma lem5199180 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : False.
Proof. exact (@lem5199177 b a s h3 (@lem5199169 x b a s h1 h2 h3)). Qed.
Lemma lem5199181 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : term504.
Proof. exact (fun h0 : ~ False => @lem5199180 x b a s h1 h2 h3). Qed.
Lemma lem5199183 (p : Prop) : (term426 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5199184 : term504 = False.
Proof. exact (@lem5199183 False). Qed.
Lemma lem5199185 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : False.
Proof. exact (EQ_MP (@lem5199184) (@lem5199181 x b a s h1 h2 h3)). Qed.
Lemma lem5199186 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem5199185 x b a s h1 h2 h3) (fun h4 : False => @lem5198486 h2)). Qed.
Lemma lem5199187 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : False.
Proof. exact (EQ_MP (@lem5199186 x b a s h1 h2 h3) (@lem5198486 h2)). Qed.
Lemma lem5199188 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : (term113 b a s) = False.
Proof. exact (prop_ext (fun h4 : term113 b a s => @lem5199187 x b a s h1 h2 h3) (fun h4 : False => @lem5198475 b a s h3)). Qed.
Lemma lem5199189 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : False.
Proof. exact (EQ_MP (@lem5199188 x b a s h1 h2 h3) (@lem5198475 b a s h3)). Qed.
Lemma lem5199190 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : (term340 x) = False.
Proof. exact (prop_ext (fun h4 : term340 x => @lem5199189 x b a s h1 h2 h3) (fun h4 : False => @lem5198436 x h1)). Qed.
Lemma lem5199191 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : False.
Proof. exact (EQ_MP (@lem5199190 x b a s h1 h2 h3) (@lem5198436 x h1)). Qed.
Lemma lem5199192 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem5199191 x b a s h1 h2 h3) (fun h4 : False => @lem5198362 h2)). Qed.
Lemma lem5199193 (x : type1018) (b : real) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term113 b a s) : False.
Proof. exact (EQ_MP (@lem5199192 x b a s h1 h2 h3) (@lem5198362 h2)). Qed.
Lemma lem5199194 (x : type1018) (a : real) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term116 a s) : False.
Proof. exact (ex_elim (@lem5198352 a s h3) (fun b : real => fun h0 : term115 a s b => @lem5199193 x b a s h1 h2 h0)). Qed.
Lemma lem5199195 (x : type1018) (s : real -> Prop) (h1 : term340 x) (h2 : term41) (h3 : term118 s) : False.
Proof. exact (ex_elim (@lem5198351 s h3) (fun a : real => fun h0 : term117 s a => @lem5199194 x a s h1 h2 h0)). Qed.
Lemma lem5199196 (x : type1018) (h1 : term340 x) (h2 : term41) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5197720 h3) (fun s : real -> Prop => fun h0 : term119 s => @lem5199195 x s h1 h2 h0)). Qed.
Lemma lem5199197 (h1 : term17) (h2 : term41) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5198349 h1) (fun x : type1018 => fun h0 : term342 x => @lem5199196 x h0 h2 h3)). Qed.
Lemma lem5199198 (h1 : term17) (h2 : term41) (h3 : term10) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem5199197 h1 h2 h3) (fun h4 : False => @lem5197733 h2)). Qed.
Lemma lem5199199 (h1 : term17) (h2 : term41) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem5199198 h1 h2 h3) (@lem5197733 h2)). Qed.
Lemma lem5199200 (h1 : term41) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5199199 h0 h1 h2). Qed.
Lemma lem5199201 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5199202 (h1 : term41) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5199201) (@lem5199200 h1 h2)). Qed.
Lemma lem5199203 (h1 : term10) : term20.
Proof. exact (fun h0 : term41 => @lem5199202 h0 h1). Qed.
Lemma lem5199204 : term22.
Proof. exact (fun h0 : term10 => @lem5199203 h0). Qed.
Lemma lem5199205 : term11.
Proof. exact (EQ_MP (@lem5197507) (@lem5199204)). Qed.
Lemma lem5199207 : term11.
Proof. exact (@lem5197281 (@lem5199205)). Qed.
Lemma lem5199208 (h1 : term10) : term19.
Proof. exact (@lem5199207 (@lem5197266 h1)). Qed.
Lemma lem5199209 (h1 : term10) : term15.
Proof. exact (@lem5199208 h1 (@lem1339240)). Qed.
Lemma lem5199210 (h1 : term10) : False.
Proof. exact (@lem5199209 h1 (@lem5184172)). Qed.
Lemma lem5199211 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5199210 h1) (fun h2 : False => @lem5197266 h1)). Qed.
Lemma lem5199212 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5199211 h1) (@lem5197266 h1)). Qed.
Lemma lem5199213 : term9.
Proof. exact (fun h0 : term10 => @lem5199212 h0). Qed.
Lemma lem5199214 : term8.
Proof. exact (EQ_MP (@lem5197265) (@lem5199213)). Qed.
