Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_IMP_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Lemma lem1368159 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1368160 : term1 = term2.
Proof. exact (@lem1368159 term1). Qed.
Lemma lem1368161 : term2 = term1.
Proof. exact (SYM (@lem1368160)). Qed.
Lemma lem1368162 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1368165 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1368166 : term5.
Proof. exact (fun h0 : term4 => @lem1368165 h0). Qed.
Lemma lem1368167 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1368168 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1368169 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1368167 h2 (@lem1368168 h1)). Qed.
Lemma lem1368170 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1368169 h1 h0). Qed.
Lemma lem1368171 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1368172 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1368170 h1 (@lem1368171 h2)). Qed.
Lemma lem1368173 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1368172 h0 h1). Qed.
Lemma lem1368174 : term7.
Proof. exact (fun h0 : term5 => @lem1368173 h0). Qed.
Lemma lem1368177 : term5.
Proof. exact (@lem1368174 (@lem1368166)). Qed.
Lemma lem1368247 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1368248 : term8 = term9.
Proof. exact (@lem1368247 term10). Qed.
Lemma lem1368257 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1368258 : term12 = term13.
Proof. exact (MK_COMB (@lem1368257) (@lem1368248)). Qed.
Lemma lem1368261 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1368268 : term4 = term15.
Proof. exact (MK_COMB (@lem1368261) (@lem1368258)). Qed.
Lemma lem1368275 (y : real) (x : real) : ((real_lt x y) = (term16 y x)) = ((real_lt x y) = (term16 y x)).
Proof. exact (eq_refl ((real_lt x y) = (term16 y x))). Qed.
Lemma lem1368276 (y : real) : (term17 y) = (term17 y).
Proof. exact (fun_ext (fun x : real => @lem1368275 y x)). Qed.
Lemma lem1368277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368278 (y : real) : (term18 y) = (term18 y).
Proof. exact (MK_COMB (@lem1368277) (@lem1368276 y)). Qed.
Lemma lem1368279 : term19 = term19.
Proof. exact (fun_ext (fun y : real => @lem1368278 y)). Qed.
Lemma lem1368280 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368281 : term10 = term10.
Proof. exact (MK_COMB (@lem1368280) (@lem1368279)). Qed.
Lemma lem1368282 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1368283 : term9 = term9.
Proof. exact (MK_COMB (@lem1368282) (@lem1368281)). Qed.
Lemma lem1368288 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1368289 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1368288 y x)). Qed.
Lemma lem1368290 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368291 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1368290) (@lem1368289 x)). Qed.
Lemma lem1368292 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1368291 x)). Qed.
Lemma lem1368293 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368294 : term24 = term24.
Proof. exact (MK_COMB (@lem1368293) (@lem1368292)). Qed.
Lemma lem1368295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1368296 : term11 = term11.
Proof. exact (MK_COMB (@lem1368295) (@lem1368294)). Qed.
Lemma lem1368297 : term13 = term13.
Proof. exact (MK_COMB (@lem1368296) (@lem1368283)). Qed.
Lemma lem1368302 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1368303 (x : real) : (term26 x) = (term26 x).
Proof. exact (fun_ext (fun y : real => @lem1368302 x y)). Qed.
Lemma lem1368304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368305 (x : real) : (term27 x) = (term27 x).
Proof. exact (MK_COMB (@lem1368304) (@lem1368303 x)). Qed.
Lemma lem1368306 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1368305 x)). Qed.
Lemma lem1368307 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368308 : term1 = term1.
Proof. exact (MK_COMB (@lem1368307) (@lem1368306)). Qed.
Lemma lem1368309 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1368310 : term3 = term3.
Proof. exact (MK_COMB (@lem1368309) (@lem1368308)). Qed.
Lemma lem1368311 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1368312 : term14 = term14.
Proof. exact (MK_COMB (@lem1368311) (@lem1368310)). Qed.
Lemma lem1368313 : term15 = term15.
Proof. exact (MK_COMB (@lem1368312) (@lem1368297)). Qed.
Lemma lem1368360 : term4 = term15.
Proof. exact (TRANS (@lem1368268) (@lem1368313)). Qed.
Lemma lem1368361 : term15 = term4.
Proof. exact (SYM (@lem1368360)). Qed.
Lemma lem1368362 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1368363 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem1368364 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1368371 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (@lem17362 (real_lt x y) (real_le x y)). Qed.
Lemma lem1368372 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1368373 (x : real) : (term33 x) = (term34 x).
Proof. exact (@lem1368372 (term26 x)). Qed.
Lemma lem1368374 (x : real) (y : real) : (term35 x y) = (term25 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem1368375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1368376 (x : real) (y : real) : (term36 x y) = (term29 x y).
Proof. exact (MK_COMB (@lem1368375) (@lem1368374 x y)). Qed.
Lemma lem1368377 (x : real) (y : real) : (term36 x y) = (term30 x y).
Proof. exact (TRANS (@lem1368376 x y) (@lem1368371 x y)). Qed.
Lemma lem1368378 (x : real) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1368377 x y)). Qed.
Lemma lem1368379 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1368380 (x : real) : (term34 x) = (term39 x).
Proof. exact (MK_COMB (@lem1368379) (@lem1368378 x)). Qed.
Lemma lem1368381 (x : real) : (term33 x) = (term39 x).
Proof. exact (TRANS (@lem1368373 x) (@lem1368380 x)). Qed.
Lemma lem1368382 (P : real -> Prop) : (term31 P) = (term32 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1368383 : term3 = term40.
Proof. exact (@lem1368382 term28). Qed.
Lemma lem1368384 (x : real) : (term41 x) = (term27 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1368385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1368386 (x : real) : (term42 x) = (term33 x).
Proof. exact (MK_COMB (@lem1368385) (@lem1368384 x)). Qed.
Lemma lem1368387 (x : real) : (term42 x) = (term39 x).
Proof. exact (TRANS (@lem1368386 x) (@lem1368381 x)). Qed.
Lemma lem1368388 : term43 = term44.
Proof. exact (fun_ext (fun x : real => @lem1368387 x)). Qed.
Lemma lem1368389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1368390 : term40 = term45.
Proof. exact (MK_COMB (@lem1368389) (@lem1368388)). Qed.
Lemma lem1368447 : term3 = term45.
Proof. exact (TRANS (@lem1368383) (@lem1368390)). Qed.
Lemma lem1368448 (h1 : term3) : term45.
Proof. exact (EQ_MP (@lem1368447) (@lem1368362 h1)). Qed.
Lemma lem1368453 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1368454 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1368453 y x)). Qed.
Lemma lem1368455 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368456 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1368455) (@lem1368454 x)). Qed.
Lemma lem1368457 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1368456 x)). Qed.
Lemma lem1368458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368515 : term24 = term24.
Proof. exact (MK_COMB (@lem1368458) (@lem1368457)). Qed.
Lemma lem1368516 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem1368515) (@lem1368363 h1)). Qed.
Lemma lem1368522 (y : real) (x : real) : (term46 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1368525 (y : real) (x : real) : (term47 y x) = (term47 y x).
Proof. exact (eq_refl (term47 y x)). Qed.
Lemma lem1368527 (x : real) (y : real) : (term48 x y) = (term48 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1368528 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (MK_COMB (@lem1368527 x y) (@lem1368522 y x)). Qed.
Lemma lem1368529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1368530 (y : real) (x : real) : (term51 y x) = (term52 y x).
Proof. exact (MK_COMB (@lem1368529) (@lem1368528 y x)). Qed.
Lemma lem1368531 (y : real) (x : real) : (term53 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1368530 y x) (@lem1368525 y x)). Qed.
Lemma lem1368532 (y : real) (x : real) : ((real_lt x y) = (term16 y x)) = (term53 y x).
Proof. exact (@lem17784 (real_lt x y) (term16 y x)). Qed.
Lemma lem1368533 (y : real) (x : real) : ((real_lt x y) = (term16 y x)) = (term54 y x).
Proof. exact (TRANS (@lem1368532 y x) (@lem1368531 y x)). Qed.
Lemma lem1368534 (y : real) : (term17 y) = (term55 y).
Proof. exact (fun_ext (fun x : real => @lem1368533 y x)). Qed.
Lemma lem1368535 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368536 (y : real) : (term18 y) = (term56 y).
Proof. exact (MK_COMB (@lem1368535) (@lem1368534 y)). Qed.
Lemma lem1368537 : term19 = term57.
Proof. exact (fun_ext (fun y : real => @lem1368536 y)). Qed.
Lemma lem1368538 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368539 : term10 = term58.
Proof. exact (MK_COMB (@lem1368538) (@lem1368537)). Qed.
Lemma lem1368545 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1368546 (P : real -> Prop) (Q : real -> Prop) : (term61 P Q) = (term62 P Q).
Proof. exact (@lem1368545 real P Q). Qed.
Lemma lem1368547 (y : real) : (term63 y) = (term64 y).
Proof. exact (@lem1368546 (term65 y) (term66 y)). Qed.
Lemma lem1368548 (y : real) (x : real) : (term67 y x) = (term50 y x).
Proof. exact (eq_refl (term67 y x)). Qed.
Lemma lem1368549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1368550 (y : real) (x : real) : (term68 y x) = (term52 y x).
Proof. exact (MK_COMB (@lem1368549) (@lem1368548 y x)). Qed.
Lemma lem1368551 (y : real) (x : real) : (term69 y x) = (term47 y x).
Proof. exact (eq_refl (term69 y x)). Qed.
Lemma lem1368552 (y : real) (x : real) : (term70 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem1368550 y x) (@lem1368551 y x)). Qed.
Lemma lem1368553 (y : real) : (term71 y) = (term55 y).
Proof. exact (fun_ext (fun x : real => @lem1368552 y x)). Qed.
Lemma lem1368554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368555 (y : real) : (term63 y) = (term56 y).
Proof. exact (MK_COMB (@lem1368554) (@lem1368553 y)). Qed.
Lemma lem1368556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1368557 (y : real) : (term72 y) = (term73 y).
Proof. exact (MK_COMB (@lem1368556) (@lem1368555 y)). Qed.
Lemma lem1368558 (y : real) (x : real) : (term67 y x) = (term50 y x).
Proof. exact (eq_refl (term67 y x)). Qed.
Lemma lem1368559 (y : real) : (term74 y) = (term65 y).
Proof. exact (fun_ext (fun x : real => @lem1368558 y x)). Qed.
Lemma lem1368560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368561 (y : real) : (term75 y) = (term76 y).
Proof. exact (MK_COMB (@lem1368560) (@lem1368559 y)). Qed.
Lemma lem1368562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1368563 (y : real) : (term77 y) = (term78 y).
Proof. exact (MK_COMB (@lem1368562) (@lem1368561 y)). Qed.
Lemma lem1368564 (y : real) (x : real) : (term69 y x) = (term47 y x).
Proof. exact (eq_refl (term69 y x)). Qed.
Lemma lem1368565 (y : real) : (term79 y) = (term66 y).
Proof. exact (fun_ext (fun x : real => @lem1368564 y x)). Qed.
Lemma lem1368566 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368567 (y : real) : (term80 y) = (term81 y).
Proof. exact (MK_COMB (@lem1368566) (@lem1368565 y)). Qed.
Lemma lem1368568 (y : real) : (term64 y) = (term82 y).
Proof. exact (MK_COMB (@lem1368563 y) (@lem1368567 y)). Qed.
Lemma lem1368569 (y : real) : ((term63 y) = (term64 y)) = ((term56 y) = (term82 y)).
Proof. exact (MK_COMB (@lem1368557 y) (@lem1368568 y)). Qed.
Lemma lem1368570 (y : real) : (term56 y) = (term82 y).
Proof. exact (EQ_MP (@lem1368569 y) (@lem1368547 y)). Qed.
Lemma lem1368667 : term57 = term83.
Proof. exact (fun_ext (fun y : real => @lem1368570 y)). Qed.
Lemma lem1368668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368669 : term58 = term84.
Proof. exact (MK_COMB (@lem1368668) (@lem1368667)). Qed.
Lemma lem1368671 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1368672 (P : real -> Prop) (Q : real -> Prop) : (term61 P Q) = (term62 P Q).
Proof. exact (@lem1368671 real P Q). Qed.
Lemma lem1368673 : term85 = term86.
Proof. exact (@lem1368672 term87 term88). Qed.
Lemma lem1368674 (y : real) : (term89 y) = (term76 y).
Proof. exact (eq_refl (term89 y)). Qed.
Lemma lem1368675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1368676 (y : real) : (term90 y) = (term78 y).
Proof. exact (MK_COMB (@lem1368675) (@lem1368674 y)). Qed.
Lemma lem1368677 (y : real) : (term91 y) = (term81 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1368678 (y : real) : (term92 y) = (term82 y).
Proof. exact (MK_COMB (@lem1368676 y) (@lem1368677 y)). Qed.
Lemma lem1368679 : term93 = term83.
Proof. exact (fun_ext (fun y : real => @lem1368678 y)). Qed.
Lemma lem1368680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368681 : term85 = term84.
Proof. exact (MK_COMB (@lem1368680) (@lem1368679)). Qed.
Lemma lem1368682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1368683 : term94 = term95.
Proof. exact (MK_COMB (@lem1368682) (@lem1368681)). Qed.
Lemma lem1368684 (y : real) : (term89 y) = (term76 y).
Proof. exact (eq_refl (term89 y)). Qed.
Lemma lem1368685 : term96 = term87.
Proof. exact (fun_ext (fun y : real => @lem1368684 y)). Qed.
Lemma lem1368686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368687 : term97 = term98.
Proof. exact (MK_COMB (@lem1368686) (@lem1368685)). Qed.
Lemma lem1368688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1368689 : term99 = term100.
Proof. exact (MK_COMB (@lem1368688) (@lem1368687)). Qed.
Lemma lem1368690 (y : real) : (term91 y) = (term81 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem1368691 : term101 = term88.
Proof. exact (fun_ext (fun y : real => @lem1368690 y)). Qed.
Lemma lem1368692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368693 : term102 = term103.
Proof. exact (MK_COMB (@lem1368692) (@lem1368691)). Qed.
Lemma lem1368694 : term86 = term104.
Proof. exact (MK_COMB (@lem1368689) (@lem1368693)). Qed.
Lemma lem1368695 : (term85 = term86) = (term84 = term104).
Proof. exact (MK_COMB (@lem1368683) (@lem1368694)). Qed.
Lemma lem1368696 : term84 = term104.
Proof. exact (EQ_MP (@lem1368695) (@lem1368673)). Qed.
Lemma lem1368803 : term58 = term104.
Proof. exact (TRANS (@lem1368669) (@lem1368696)). Qed.
Lemma lem1368804 : term10 = term104.
Proof. exact (TRANS (@lem1368539) (@lem1368803)). Qed.
Lemma lem1368805 (h1 : term10) : term104.
Proof. exact (EQ_MP (@lem1368804) (@lem1368364 h1)). Qed.
Lemma lem1368806 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1368820 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1368821 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1368820 y x)). Qed.
Lemma lem1368822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368823 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1368822) (@lem1368821 x)). Qed.
Lemma lem1368824 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1368823 x)). Qed.
Lemma lem1368825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368826 : term24 = term24.
Proof. exact (MK_COMB (@lem1368825) (@lem1368824)). Qed.
Lemma lem1368827 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem1368826) (@lem1368516 h1)). Qed.
Lemma lem1368844 (y : real) (x : real) : (term47 y x) = (term47 y x).
Proof. exact (eq_refl (term47 y x)). Qed.
Lemma lem1368845 (y : real) : (term66 y) = (term66 y).
Proof. exact (fun_ext (fun x : real => @lem1368844 y x)). Qed.
Lemma lem1368846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368847 (y : real) : (term81 y) = (term81 y).
Proof. exact (MK_COMB (@lem1368846) (@lem1368845 y)). Qed.
Lemma lem1368848 : term88 = term88.
Proof. exact (fun_ext (fun y : real => @lem1368847 y)). Qed.
Lemma lem1368849 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368850 : term103 = term103.
Proof. exact (MK_COMB (@lem1368849) (@lem1368848)). Qed.
Lemma lem1368863 (y : real) (x : real) : (term50 y x) = (term50 y x).
Proof. exact (eq_refl (term50 y x)). Qed.
Lemma lem1368864 (y : real) : (term65 y) = (term65 y).
Proof. exact (fun_ext (fun x : real => @lem1368863 y x)). Qed.
Lemma lem1368865 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368866 (y : real) : (term76 y) = (term76 y).
Proof. exact (MK_COMB (@lem1368865) (@lem1368864 y)). Qed.
Lemma lem1368867 : term87 = term87.
Proof. exact (fun_ext (fun y : real => @lem1368866 y)). Qed.
Lemma lem1368868 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368869 : term98 = term98.
Proof. exact (MK_COMB (@lem1368868) (@lem1368867)). Qed.
Lemma lem1368870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1368871 : term100 = term100.
Proof. exact (MK_COMB (@lem1368870) (@lem1368869)). Qed.
Lemma lem1368872 : term104 = term104.
Proof. exact (MK_COMB (@lem1368871) (@lem1368850)). Qed.
Lemma lem1368873 (h1 : term10) : term104.
Proof. exact (EQ_MP (@lem1368872) (@lem1368805 h1)). Qed.
Lemma lem1368889 (x : real) (y : real) (h1 : term30 x y) : term30 x y.
Proof. exact (h1). Qed.
Lemma lem1368892 (h1 : term10) : term103.
Proof. exact (proj2 (@lem1368873 h1)). Qed.
Lemma lem1368901 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1368902 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1368901 y x)). Qed.
Lemma lem1368903 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368904 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1368903) (@lem1368902 x)). Qed.
Lemma lem1368905 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1368904 x)). Qed.
Lemma lem1368906 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368908 : term24 = term24.
Proof. exact (MK_COMB (@lem1368906) (@lem1368905)). Qed.
Lemma lem1368909 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem1368908) (@lem1368827 h1)). Qed.
Lemma lem1368941 (y : real) (x : real) : (term47 y x) = (term47 y x).
Proof. exact (eq_refl (term47 y x)). Qed.
Lemma lem1368942 (y : real) : (term66 y) = (term66 y).
Proof. exact (fun_ext (fun x : real => @lem1368941 y x)). Qed.
Lemma lem1368943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368944 (y : real) : (term81 y) = (term81 y).
Proof. exact (MK_COMB (@lem1368943) (@lem1368942 y)). Qed.
Lemma lem1368945 : term88 = term88.
Proof. exact (fun_ext (fun y : real => @lem1368944 y)). Qed.
Lemma lem1368946 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1368948 : term103 = term103.
Proof. exact (MK_COMB (@lem1368946) (@lem1368945)). Qed.
Lemma lem1368949 (h1 : term10) : term103.
Proof. exact (EQ_MP (@lem1368948) (@lem1368892 h1)). Qed.
Lemma lem1368950 (_24288 : real) (h1 : term24) : term105 _24288.
Proof. exact (@lem1368909 h1 _24288). Qed.
Lemma lem1368951 (_24288 : real) : (term105 _24288) = (term22 _24288).
Proof. exact (eq_refl (term105 _24288)). Qed.
Lemma lem1368952 (_24288 : real) (h1 : term24) : term22 _24288.
Proof. exact (EQ_MP (@lem1368951 _24288) (@lem1368950 _24288 h1)). Qed.
Lemma lem1368953 (_24288 : real) (_24289 : real) (h1 : term24) : term106 _24288 _24289.
Proof. exact (@lem1368952 _24288 h1 _24289). Qed.
Lemma lem1368954 (_24289 : real) (_24288 : real) : (term106 _24288 _24289) = (term20 _24289 _24288).
Proof. exact (eq_refl (term106 _24288 _24289)). Qed.
Lemma lem1368962 (_24292 : real) (h1 : term10) : term91 _24292.
Proof. exact (@lem1368949 h1 _24292). Qed.
Lemma lem1368963 (_24292 : real) : (term91 _24292) = (term81 _24292).
Proof. exact (eq_refl (term91 _24292)). Qed.
Lemma lem1368964 (_24292 : real) (h1 : term10) : term81 _24292.
Proof. exact (EQ_MP (@lem1368963 _24292) (@lem1368962 _24292 h1)). Qed.
Lemma lem1368965 (_24292 : real) (_24293 : real) (h1 : term10) : term69 _24292 _24293.
Proof. exact (@lem1368964 _24292 h1 _24293). Qed.
Lemma lem1368966 (_24292 : real) (_24293 : real) : (term69 _24292 _24293) = (term47 _24292 _24293).
Proof. exact (eq_refl (term69 _24292 _24293)). Qed.
Lemma lem1368973 (_24289 : real) (_24288 : real) (h1 : term24) : term20 _24289 _24288.
Proof. exact (EQ_MP (@lem1368954 _24289 _24288) (@lem1368953 _24288 _24289 h1)). Qed.
Lemma lem1368977 (x : real) (y : real) (h1 : term30 x y) : term16 x y.
Proof. exact (proj2 (@lem1368889 x y h1)). Qed.
Lemma lem1368989 (_24292 : real) (_24293 : real) (h1 : term10) : term47 _24292 _24293.
Proof. exact (EQ_MP (@lem1368966 _24292 _24293) (@lem1368965 _24292 _24293 h1)). Qed.
Lemma lem1368991 (x : real) (y : real) (h1 : term30 x y) : real_lt x y.
Proof. exact (proj1 (@lem1368889 x y h1)). Qed.
Lemma lem1368992 (x : real) (y : real) (h1 : term30 x y) : term107 x y.
Proof. exact (fun h0 : term108 x y => @lem1368991 x y h1). Qed.
Lemma lem1368994 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1368995 (x : real) (y : real) : (term107 x y) = (real_lt x y).
Proof. exact (@lem1368994 (real_lt x y)). Qed.
Lemma lem1368996 (x : real) (y : real) (h1 : term30 x y) : real_lt x y.
Proof. exact (EQ_MP (@lem1368995 x y) (@lem1368992 x y h1)). Qed.
Lemma lem1369002 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1369003 (_24293 : real) (_24292 : real) : (term47 _24292 _24293) = (term110 _24293 _24292).
Proof. exact (@lem1369002 (term16 _24292 _24293) (term108 _24293 _24292)). Qed.
Lemma lem1369009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1369010 (_24293 : real) (_24292 : real) : (term111 _24292 _24293) = (term112 _24293 _24292).
Proof. exact (MK_COMB (@lem1369009) (@lem1369003 _24293 _24292)). Qed.
Lemma lem1369016 (_24293 : real) (_24292 : real) : (term110 _24293 _24292) = (term110 _24293 _24292).
Proof. exact (eq_refl (term110 _24293 _24292)). Qed.
Lemma lem1369017 (_24293 : real) (_24292 : real) : ((term47 _24292 _24293) = (term110 _24293 _24292)) = ((term110 _24293 _24292) = (term110 _24293 _24292)).
Proof. exact (MK_COMB (@lem1369010 _24293 _24292) (@lem1369016 _24293 _24292)). Qed.
Lemma lem1369019 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1369020 (x : Prop) : (x = x) = True.
Proof. exact (@lem1369019 Prop x). Qed.
Lemma lem1369021 (_24293 : real) (_24292 : real) : ((term110 _24293 _24292) = (term110 _24293 _24292)) = True.
Proof. exact (@lem1369020 (term110 _24293 _24292)). Qed.
Lemma lem1369022 (_24293 : real) (_24292 : real) : ((term47 _24292 _24293) = (term110 _24293 _24292)) = True.
Proof. exact (TRANS (@lem1369017 _24293 _24292) (@lem1369021 _24293 _24292)). Qed.
Lemma lem1369023 (_24293 : real) (_24292 : real) : True = ((term47 _24292 _24293) = (term110 _24293 _24292)).
Proof. exact (SYM (@lem1369022 _24293 _24292)). Qed.
Lemma lem1369024 (_24293 : real) (_24292 : real) : (term47 _24292 _24293) = (term110 _24293 _24292).
Proof. exact (EQ_MP (@lem1369023 _24293 _24292) (@lem0)). Qed.
Lemma lem1369025 (_24293 : real) (_24292 : real) (h1 : term10) : term110 _24293 _24292.
Proof. exact (EQ_MP (@lem1369024 _24293 _24292) (@lem1368989 _24292 _24293 h1)). Qed.
Lemma lem1369027 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1369028 (_24292 : real) (_24293 : real) : (term110 _24293 _24292) = (term114 _24292 _24293).
Proof. exact (@lem1369027 (term108 _24293 _24292) (term16 _24292 _24293)). Qed.
Lemma lem1369030 (a : Prop) : (term115 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1369031 (_24293 : real) (_24292 : real) : (term116 _24293 _24292) = (real_lt _24293 _24292).
Proof. exact (@lem1369030 (real_lt _24293 _24292)). Qed.
Lemma lem1369032 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1369033 (_24293 : real) (_24292 : real) : (term117 _24293 _24292) = (term118 _24293 _24292).
Proof. exact (MK_COMB (@lem1369032) (@lem1369031 _24293 _24292)). Qed.
Lemma lem1369034 (_24292 : real) (_24293 : real) : (term16 _24292 _24293) = (term16 _24292 _24293).
Proof. exact (eq_refl (term16 _24292 _24293)). Qed.
Lemma lem1369035 (_24292 : real) (_24293 : real) : (term114 _24292 _24293) = (term119 _24292 _24293).
Proof. exact (MK_COMB (@lem1369033 _24293 _24292) (@lem1369034 _24292 _24293)). Qed.
Lemma lem1369036 (_24292 : real) (_24293 : real) : (term110 _24293 _24292) = (term119 _24292 _24293).
Proof. exact (TRANS (@lem1369028 _24292 _24293) (@lem1369035 _24292 _24293)). Qed.
Lemma lem1369039 (_24292 : real) (_24293 : real) (h1 : term10) : term119 _24292 _24293.
Proof. exact (EQ_MP (@lem1369036 _24292 _24293) (@lem1369025 _24293 _24292 h1)). Qed.
Lemma lem1369040 (y : real) (x : real) (h1 : term10) : term119 y x.
Proof. exact (@lem1369039 y x h1). Qed.
Lemma lem1369043 (x : real) (y : real) (h1 : term10) (h2 : term30 x y) : term16 y x.
Proof. exact (@lem1369040 y x h1 (@lem1368996 x y h2)). Qed.
Lemma lem1369044 (x : real) (y : real) (h1 : term10) (h2 : term30 x y) : term120 y x.
Proof. exact (fun h0 : real_le y x => @lem1369043 x y h1 h2). Qed.
Lemma lem1369046 (p : Prop) : (term121 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1369047 (y : real) (x : real) : (term120 y x) = (term16 y x).
Proof. exact (@lem1369046 (real_le y x)). Qed.
Lemma lem1369048 (x : real) (y : real) (h1 : term10) (h2 : term30 x y) : term16 y x.
Proof. exact (EQ_MP (@lem1369047 y x) (@lem1369044 x y h1 h2)). Qed.
Lemma lem1369059 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1369060 (_24289 : real) (_24288 : real) : (term20 _24288 _24289) = (term20 _24289 _24288).
Proof. exact (@lem1369059 (real_le _24288 _24289) (real_le _24289 _24288)). Qed.
Lemma lem1369066 (_24289 : real) (_24288 : real) : (term122 _24289 _24288) = (term122 _24289 _24288).
Proof. exact (eq_refl (term122 _24289 _24288)). Qed.
Lemma lem1369067 (_24289 : real) (_24288 : real) : ((term20 _24289 _24288) = (term20 _24288 _24289)) = ((term20 _24289 _24288) = (term20 _24289 _24288)).
Proof. exact (MK_COMB (@lem1369066 _24289 _24288) (@lem1369060 _24289 _24288)). Qed.
Lemma lem1369069 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1369070 (x : Prop) : (x = x) = True.
Proof. exact (@lem1369069 Prop x). Qed.
Lemma lem1369071 (_24289 : real) (_24288 : real) : ((term20 _24289 _24288) = (term20 _24289 _24288)) = True.
Proof. exact (@lem1369070 (term20 _24289 _24288)). Qed.
Lemma lem1369072 (_24288 : real) (_24289 : real) : ((term20 _24289 _24288) = (term20 _24288 _24289)) = True.
Proof. exact (TRANS (@lem1369067 _24289 _24288) (@lem1369071 _24289 _24288)). Qed.
Lemma lem1369073 (_24288 : real) (_24289 : real) : True = ((term20 _24289 _24288) = (term20 _24288 _24289)).
Proof. exact (SYM (@lem1369072 _24288 _24289)). Qed.
Lemma lem1369074 (_24288 : real) (_24289 : real) : (term20 _24289 _24288) = (term20 _24288 _24289).
Proof. exact (EQ_MP (@lem1369073 _24288 _24289) (@lem0)). Qed.
Lemma lem1369075 (_24288 : real) (_24289 : real) (h1 : term24) : term20 _24288 _24289.
Proof. exact (EQ_MP (@lem1369074 _24288 _24289) (@lem1368973 _24289 _24288 h1)). Qed.
Lemma lem1369077 (b : Prop) (a : Prop) : (a \/ b) = (term113 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1369080 (_24289 : real) (_24288 : real) : (term20 _24288 _24289) = (term123 _24289 _24288).
Proof. exact (@lem1369077 (real_le _24288 _24289) (real_le _24289 _24288)). Qed.
Lemma lem1369083 (_24289 : real) (_24288 : real) (h1 : term24) : term123 _24289 _24288.
Proof. exact (EQ_MP (@lem1369080 _24289 _24288) (@lem1369075 _24288 _24289 h1)). Qed.
Lemma lem1369084 (x : real) (y : real) (h1 : term24) : term123 x y.
Proof. exact (@lem1369083 x y h1). Qed.
Lemma lem1369087 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : real_le x y.
Proof. exact (@lem1369084 x y h2 (@lem1369048 x y h1 h3)). Qed.
Lemma lem1369088 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term124 x y.
Proof. exact (fun h0 : term16 x y => @lem1369087 x y h1 h2 h3). Qed.
Lemma lem1369090 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1369091 (x : real) (y : real) : (term124 x y) = (real_le x y).
Proof. exact (@lem1369090 (real_le x y)). Qed.
Lemma lem1369092 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1369091 x y) (@lem1369088 x y h1 h2 h3)). Qed.
Lemma lem1369095 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1369097 (x : real) (y : real) : (term16 x y) = (term125 x y).
Proof. exact (@lem1369095 (real_le x y)). Qed.
Lemma lem1369100 (x : real) (y : real) (h1 : term30 x y) : term125 x y.
Proof. exact (EQ_MP (@lem1369097 x y) (@lem1368977 x y h1)). Qed.
Lemma lem1369103 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (@lem1369100 x y h3 (@lem1369092 x y h1 h2 h3)). Qed.
Lemma lem1369104 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term126.
Proof. exact (fun h0 : ~ False => @lem1369103 x y h1 h2 h3). Qed.
Lemma lem1369106 (p : Prop) : (term109 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1369107 : term126 = False.
Proof. exact (@lem1369106 False). Qed.
Lemma lem1369108 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (EQ_MP (@lem1369107) (@lem1369104 x y h1 h2 h3)). Qed.
Lemma lem1369109 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem1369108 x y h1 h2 h3) (fun h4 : False => @lem1368909 h2)). Qed.
Lemma lem1369110 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (EQ_MP (@lem1369109 x y h1 h2 h3) (@lem1368909 h2)). Qed.
Lemma lem1369111 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : (term30 x y) = False.
Proof. exact (prop_ext (fun h4 : term30 x y => @lem1369110 x y h1 h2 h3) (fun h4 : False => @lem1368889 x y h3)). Qed.
Lemma lem1369112 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (EQ_MP (@lem1369111 x y h1 h2 h3) (@lem1368889 x y h3)). Qed.
Lemma lem1369113 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem1369112 x y h1 h2 h3) (fun h4 : False => @lem1368827 h2)). Qed.
Lemma lem1369114 (x : real) (y : real) (h1 : term10) (h2 : term24) (h3 : term30 x y) : False.
Proof. exact (EQ_MP (@lem1369113 x y h1 h2 h3) (@lem1368827 h2)). Qed.
Lemma lem1369115 (x : real) (h1 : term10) (h2 : term24) (h3 : term39 x) : False.
Proof. exact (ex_elim (@lem1368806 x h3) (fun y : real => fun h0 : term38 x y => @lem1369114 x y h1 h2 h0)). Qed.
Lemma lem1369116 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1368448 h3) (fun x : real => fun h0 : term44 x => @lem1369115 x h1 h2 h0)). Qed.
Lemma lem1369117 (h1 : term10) (h2 : term24) (h3 : term3) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem1369116 h1 h2 h3) (fun h4 : False => @lem1368516 h2)). Qed.
Lemma lem1369118 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1369117 h1 h2 h3) (@lem1368516 h2)). Qed.
Lemma lem1369119 (h1 : term24) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1369118 h0 h1 h2). Qed.
Lemma lem1369120 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1369121 (h1 : term24) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1369120) (@lem1369119 h1 h2)). Qed.
Lemma lem1369122 (h1 : term3) : term13.
Proof. exact (fun h0 : term24 => @lem1369121 h0 h1). Qed.
Lemma lem1369123 : term15.
Proof. exact (fun h0 : term3 => @lem1369122 h0). Qed.
Lemma lem1369124 : term4.
Proof. exact (EQ_MP (@lem1368361) (@lem1369123)). Qed.
Lemma lem1369126 : term4.
Proof. exact (@lem1368177 (@lem1369124)). Qed.
Lemma lem1369127 (h1 : term3) : term12.
Proof. exact (@lem1369126 (@lem1368162 h1)). Qed.
Lemma lem1369128 (h1 : term3) : term8.
Proof. exact (@lem1369127 h1 (@lem1339697)). Qed.
Lemma lem1369129 (h1 : term3) : False.
Proof. exact (@lem1369128 h1 (@lem1341566)). Qed.
Lemma lem1369130 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1369129 h1) (fun h2 : False => @lem1368162 h1)). Qed.
Lemma lem1369131 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1369130 h1) (@lem1368162 h1)). Qed.
Lemma lem1369132 : term2.
Proof. exact (fun h0 : term3 => @lem1369131 h0). Qed.
Lemma lem1369133 : term1.
Proof. exact (EQ_MP (@lem1368161) (@lem1369132)). Qed.
