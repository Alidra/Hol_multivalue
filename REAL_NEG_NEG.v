Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_NEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_EQ_ADD_RCANCEL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338238_spec.
Require Import thm1338588_spec.
Require Import thm16474_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Lemma lem1357255 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1357256 : term1 = term2.
Proof. exact (@lem1357255 term1). Qed.
Lemma lem1357257 : term2 = term1.
Proof. exact (SYM (@lem1357256)). Qed.
Lemma lem1357258 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1357261 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1357262 : term5.
Proof. exact (fun h0 : term4 => @lem1357261 h0). Qed.
Lemma lem1357263 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1357264 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1357265 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1357263 h2 (@lem1357264 h1)). Qed.
Lemma lem1357266 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1357265 h1 h0). Qed.
Lemma lem1357267 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1357268 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1357266 h1 (@lem1357267 h2)). Qed.
Lemma lem1357269 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1357268 h0 h1). Qed.
Lemma lem1357270 : term7.
Proof. exact (fun h0 : term5 => @lem1357269 h0). Qed.
Lemma lem1357273 : term5.
Proof. exact (@lem1357270 (@lem1357262)). Qed.
Lemma lem1357297 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1357298 : term8 = term9.
Proof. exact (@lem1357297 term10). Qed.
Lemma lem1357311 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1357312 : term12 = term13.
Proof. exact (MK_COMB (@lem1357311) (@lem1357298)). Qed.
Lemma lem1357315 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1357316 : term15 = term16.
Proof. exact (MK_COMB (@lem1357315) (@lem1357312)). Qed.
Lemma lem1357319 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1357326 : term4 = term18.
Proof. exact (MK_COMB (@lem1357319) (@lem1357316)). Qed.
Lemma lem1357331 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (((real_add x z) = (real_add y z)) = (x = y)).
Proof. exact (eq_refl (((real_add x z) = (real_add y z)) = (x = y))). Qed.
Lemma lem1357332 (x : real) (y : real) : (term19 x y) = (term19 x y).
Proof. exact (fun_ext (fun z : real => @lem1357331 z x y)). Qed.
Lemma lem1357333 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357334 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1357333) (@lem1357332 x y)). Qed.
Lemma lem1357335 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1357334 x y)). Qed.
Lemma lem1357336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357337 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1357336) (@lem1357335 x)). Qed.
Lemma lem1357338 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1357337 x)). Qed.
Lemma lem1357339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357340 : term10 = term10.
Proof. exact (MK_COMB (@lem1357339) (@lem1357338)). Qed.
Lemma lem1357341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1357342 : term9 = term9.
Proof. exact (MK_COMB (@lem1357341) (@lem1357340)). Qed.
Lemma lem1357343 (x : real) : ((term24 x) = term25) = ((term24 x) = term25).
Proof. exact (eq_refl ((term24 x) = term25)). Qed.
Lemma lem1357344 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1357343 x)). Qed.
Lemma lem1357345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357346 : term27 = term27.
Proof. exact (MK_COMB (@lem1357345) (@lem1357344)). Qed.
Lemma lem1357347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1357348 : term11 = term11.
Proof. exact (MK_COMB (@lem1357347) (@lem1357346)). Qed.
Lemma lem1357349 : term13 = term13.
Proof. exact (MK_COMB (@lem1357348) (@lem1357342)). Qed.
Lemma lem1357350 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1357351 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1357350 y x)). Qed.
Lemma lem1357352 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357353 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1357352) (@lem1357351 x)). Qed.
Lemma lem1357354 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1357353 x)). Qed.
Lemma lem1357355 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357356 : term31 = term31.
Proof. exact (MK_COMB (@lem1357355) (@lem1357354)). Qed.
Lemma lem1357357 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1357358 : term14 = term14.
Proof. exact (MK_COMB (@lem1357357) (@lem1357356)). Qed.
Lemma lem1357359 : term16 = term16.
Proof. exact (MK_COMB (@lem1357358) (@lem1357349)). Qed.
Lemma lem1357360 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1357361 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1357360 x)). Qed.
Lemma lem1357362 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357363 : term1 = term1.
Proof. exact (MK_COMB (@lem1357362) (@lem1357361)). Qed.
Lemma lem1357364 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1357365 : term3 = term3.
Proof. exact (MK_COMB (@lem1357364) (@lem1357363)). Qed.
Lemma lem1357366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1357367 : term17 = term17.
Proof. exact (MK_COMB (@lem1357366) (@lem1357365)). Qed.
Lemma lem1357368 : term18 = term18.
Proof. exact (MK_COMB (@lem1357367) (@lem1357359)). Qed.
Lemma lem1357419 : term4 = term18.
Proof. exact (TRANS (@lem1357326) (@lem1357368)). Qed.
Lemma lem1357420 : term18 = term4.
Proof. exact (SYM (@lem1357419)). Qed.
Lemma lem1357421 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1357422 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1357423 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1357424 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1357426 (P : real -> Prop) : (term34 P) = (term35 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1357427 : term3 = term36.
Proof. exact (@lem1357426 term33). Qed.
Lemma lem1357428 (x : real) : (term37 x) = ((term32 x) = x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1357429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1357431 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1357429) (@lem1357428 x)). Qed.
Lemma lem1357432 : term40 = term41.
Proof. exact (fun_ext (fun x : real => @lem1357431 x)). Qed.
Lemma lem1357433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1357434 : term36 = term42.
Proof. exact (MK_COMB (@lem1357433) (@lem1357432)). Qed.
Lemma lem1357443 : term3 = term42.
Proof. exact (TRANS (@lem1357427) (@lem1357434)). Qed.
Lemma lem1357444 (h1 : term3) : term42.
Proof. exact (EQ_MP (@lem1357443) (@lem1357421 h1)). Qed.
Lemma lem1357445 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1357446 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1357445 y x)). Qed.
Lemma lem1357447 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357448 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1357447) (@lem1357446 x)). Qed.
Lemma lem1357449 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1357448 x)). Qed.
Lemma lem1357450 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357463 : term31 = term31.
Proof. exact (MK_COMB (@lem1357450) (@lem1357449)). Qed.
Lemma lem1357464 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem1357463) (@lem1357422 h1)). Qed.
Lemma lem1357465 (x : real) : ((term24 x) = term25) = ((term24 x) = term25).
Proof. exact (eq_refl ((term24 x) = term25)). Qed.
Lemma lem1357466 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1357465 x)). Qed.
Lemma lem1357467 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357476 : term27 = term27.
Proof. exact (MK_COMB (@lem1357467) (@lem1357466)). Qed.
Lemma lem1357477 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1357476) (@lem1357423 h1)). Qed.
Lemma lem1357492 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (term43 z x y).
Proof. exact (@lem17784 ((real_add x z) = (real_add y z)) (x = y)). Qed.
Lemma lem1357493 (x : real) (y : real) : (term19 x y) = (term44 x y).
Proof. exact (fun_ext (fun z : real => @lem1357492 z x y)). Qed.
Lemma lem1357494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357495 (x : real) (y : real) : (term20 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1357494) (@lem1357493 x y)). Qed.
Lemma lem1357496 (x : real) : (term21 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1357495 x y)). Qed.
Lemma lem1357497 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357498 (x : real) : (term22 x) = (term47 x).
Proof. exact (MK_COMB (@lem1357497) (@lem1357496 x)). Qed.
Lemma lem1357499 : term23 = term48.
Proof. exact (fun_ext (fun x : real => @lem1357498 x)). Qed.
Lemma lem1357500 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357501 : term10 = term49.
Proof. exact (MK_COMB (@lem1357500) (@lem1357499)). Qed.
Lemma lem1357511 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1357512 (P : real -> Prop) (Q : real -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem1357511 real P Q). Qed.
Lemma lem1357513 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (@lem1357512 (term56 x y) (term57 x y)). Qed.
Lemma lem1357514 (z : real) (x : real) (y : real) : (term58 x y z) = (term59 z x y).
Proof. exact (eq_refl (term58 x y z)). Qed.
Lemma lem1357515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357516 (z : real) (x : real) (y : real) : (term60 x y z) = (term61 z x y).
Proof. exact (MK_COMB (@lem1357515) (@lem1357514 z x y)). Qed.
Lemma lem1357517 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1357518 (z : real) (x : real) (y : real) : (term64 x y z) = (term43 z x y).
Proof. exact (MK_COMB (@lem1357516 z x y) (@lem1357517 z x y)). Qed.
Lemma lem1357519 (x : real) (y : real) : (term65 x y) = (term44 x y).
Proof. exact (fun_ext (fun z : real => @lem1357518 z x y)). Qed.
Lemma lem1357520 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357521 (x : real) (y : real) : (term54 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem1357520) (@lem1357519 x y)). Qed.
Lemma lem1357522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1357523 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (MK_COMB (@lem1357522) (@lem1357521 x y)). Qed.
Lemma lem1357524 (z : real) (x : real) (y : real) : (term58 x y z) = (term59 z x y).
Proof. exact (eq_refl (term58 x y z)). Qed.
Lemma lem1357525 (x : real) (y : real) : (term68 x y) = (term56 x y).
Proof. exact (fun_ext (fun z : real => @lem1357524 z x y)). Qed.
Lemma lem1357526 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357527 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1357526) (@lem1357525 x y)). Qed.
Lemma lem1357528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357529 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1357528) (@lem1357527 x y)). Qed.
Lemma lem1357530 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1357531 (x : real) (y : real) : (term73 x y) = (term57 x y).
Proof. exact (fun_ext (fun z : real => @lem1357530 z x y)). Qed.
Lemma lem1357532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357533 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1357532) (@lem1357531 x y)). Qed.
Lemma lem1357534 (x : real) (y : real) : (term55 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1357529 x y) (@lem1357533 x y)). Qed.
Lemma lem1357535 (x : real) (y : real) : ((term54 x y) = (term55 x y)) = ((term45 x y) = (term76 x y)).
Proof. exact (MK_COMB (@lem1357523 x y) (@lem1357534 x y)). Qed.
Lemma lem1357536 (x : real) (y : real) : (term45 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem1357535 x y) (@lem1357513 x y)). Qed.
Lemma lem1357558 {A : Type'} (P : A -> Prop) (Q : Prop) : (term77 A P Q) = (term78 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1357559 (P : real -> Prop) (Q : Prop) : (term79 P Q) = (term80 P Q).
Proof. exact (@lem1357558 real P Q). Qed.
Lemma lem1357560 (x : real) (y : real) : (term81 x y) = (term82 x y).
Proof. exact (@lem1357559 (term83 x y) (term84 x y)). Qed.
Lemma lem1357561 (x : real) (y : real) (z : real) : (term85 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term85 x y z)). Qed.
Lemma lem1357562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1357563 (x : real) (y : real) (z : real) : (term86 x y z) = (term87 x y z).
Proof. exact (MK_COMB (@lem1357562) (@lem1357561 x y z)). Qed.
Lemma lem1357564 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1357565 (z : real) (x : real) (y : real) : (term88 z x y) = (term59 z x y).
Proof. exact (MK_COMB (@lem1357563 x y z) (@lem1357564 x y)). Qed.
Lemma lem1357566 (x : real) (y : real) : (term89 x y) = (term56 x y).
Proof. exact (fun_ext (fun z : real => @lem1357565 z x y)). Qed.
Lemma lem1357567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357568 (x : real) (y : real) : (term81 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1357567) (@lem1357566 x y)). Qed.
Lemma lem1357569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1357570 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1357569) (@lem1357568 x y)). Qed.
Lemma lem1357571 (x : real) (y : real) (z : real) : (term85 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term85 x y z)). Qed.
Lemma lem1357572 (x : real) (y : real) : (term92 x y) = (term83 x y).
Proof. exact (fun_ext (fun z : real => @lem1357571 x y z)). Qed.
Lemma lem1357573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357574 (x : real) (y : real) : (term93 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1357573) (@lem1357572 x y)). Qed.
Lemma lem1357575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1357576 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1357575) (@lem1357574 x y)). Qed.
Lemma lem1357577 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1357578 (x : real) (y : real) : (term82 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1357576 x y) (@lem1357577 x y)). Qed.
Lemma lem1357579 (x : real) (y : real) : ((term81 x y) = (term82 x y)) = ((term70 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1357570 x y) (@lem1357578 x y)). Qed.
Lemma lem1357580 (x : real) (y : real) : (term70 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1357579 x y) (@lem1357560 x y)). Qed.
Lemma lem1357585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357586 (x : real) (y : real) : (term72 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1357585) (@lem1357580 x y)). Qed.
Lemma lem1357608 {A : Type'} (P : A -> Prop) (Q : Prop) : (term77 A P Q) = (term78 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1357609 (P : real -> Prop) (Q : Prop) : (term79 P Q) = (term80 P Q).
Proof. exact (@lem1357608 real P Q). Qed.
Lemma lem1357610 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (@lem1357609 (term101 x y) (x = y)). Qed.
Lemma lem1357611 (x : real) (y : real) (z : real) : (term102 x y z) = (term103 x y z).
Proof. exact (eq_refl (term102 x y z)). Qed.
Lemma lem1357612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1357613 (x : real) (y : real) (z : real) : (term104 x y z) = (term105 x y z).
Proof. exact (MK_COMB (@lem1357612) (@lem1357611 x y z)). Qed.
Lemma lem1357614 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1357615 (z : real) (x : real) (y : real) : (term106 z x y) = (term63 z x y).
Proof. exact (MK_COMB (@lem1357613 x y z) (@lem1357614 x y)). Qed.
Lemma lem1357616 (x : real) (y : real) : (term107 x y) = (term57 x y).
Proof. exact (fun_ext (fun z : real => @lem1357615 z x y)). Qed.
Lemma lem1357617 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357618 (x : real) (y : real) : (term99 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1357617) (@lem1357616 x y)). Qed.
Lemma lem1357619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1357620 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1357619) (@lem1357618 x y)). Qed.
Lemma lem1357621 (x : real) (y : real) (z : real) : (term102 x y z) = (term103 x y z).
Proof. exact (eq_refl (term102 x y z)). Qed.
Lemma lem1357622 (x : real) (y : real) : (term110 x y) = (term101 x y).
Proof. exact (fun_ext (fun z : real => @lem1357621 x y z)). Qed.
Lemma lem1357623 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357624 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1357623) (@lem1357622 x y)). Qed.
Lemma lem1357625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1357626 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1357625) (@lem1357624 x y)). Qed.
Lemma lem1357627 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1357628 (x : real) (y : real) : (term100 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1357626 x y) (@lem1357627 x y)). Qed.
Lemma lem1357629 (x : real) (y : real) : ((term99 x y) = (term100 x y)) = ((term75 x y) = (term115 x y)).
Proof. exact (MK_COMB (@lem1357620 x y) (@lem1357628 x y)). Qed.
Lemma lem1357630 (x : real) (y : real) : (term75 x y) = (term115 x y).
Proof. exact (EQ_MP (@lem1357629 x y) (@lem1357610 x y)). Qed.
Lemma lem1357635 (x : real) (y : real) : (term76 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1357586 x y) (@lem1357630 x y)). Qed.
Lemma lem1357636 (x : real) (y : real) : (term45 x y) = (term116 x y).
Proof. exact (TRANS (@lem1357536 x y) (@lem1357635 x y)). Qed.
Lemma lem1357637 (x : real) : (term46 x) = (term117 x).
Proof. exact (fun_ext (fun y : real => @lem1357636 x y)). Qed.
Lemma lem1357638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357639 (x : real) : (term47 x) = (term118 x).
Proof. exact (MK_COMB (@lem1357638) (@lem1357637 x)). Qed.
Lemma lem1357641 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1357642 (P : real -> Prop) (Q : real -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem1357641 real P Q). Qed.
Lemma lem1357643 (x : real) : (term119 x) = (term120 x).
Proof. exact (@lem1357642 (term121 x) (term122 x)). Qed.
Lemma lem1357644 (x : real) (y : real) : (term123 x y) = (term97 x y).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1357645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357646 (x : real) (y : real) : (term124 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1357645) (@lem1357644 x y)). Qed.
Lemma lem1357647 (x : real) (y : real) : (term125 x y) = (term115 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1357648 (x : real) (y : real) : (term126 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1357646 x y) (@lem1357647 x y)). Qed.
Lemma lem1357649 (x : real) : (term127 x) = (term117 x).
Proof. exact (fun_ext (fun y : real => @lem1357648 x y)). Qed.
Lemma lem1357650 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357651 (x : real) : (term119 x) = (term118 x).
Proof. exact (MK_COMB (@lem1357650) (@lem1357649 x)). Qed.
Lemma lem1357652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1357653 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1357652) (@lem1357651 x)). Qed.
Lemma lem1357654 (x : real) (y : real) : (term123 x y) = (term97 x y).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem1357655 (x : real) : (term130 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1357654 x y)). Qed.
Lemma lem1357656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357657 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem1357656) (@lem1357655 x)). Qed.
Lemma lem1357658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357659 (x : real) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1357658) (@lem1357657 x)). Qed.
Lemma lem1357660 (x : real) (y : real) : (term125 x y) = (term115 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1357661 (x : real) : (term135 x) = (term122 x).
Proof. exact (fun_ext (fun y : real => @lem1357660 x y)). Qed.
Lemma lem1357662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357663 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1357662) (@lem1357661 x)). Qed.
Lemma lem1357664 (x : real) : (term120 x) = (term138 x).
Proof. exact (MK_COMB (@lem1357659 x) (@lem1357663 x)). Qed.
Lemma lem1357665 (x : real) : ((term119 x) = (term120 x)) = ((term118 x) = (term138 x)).
Proof. exact (MK_COMB (@lem1357653 x) (@lem1357664 x)). Qed.
Lemma lem1357666 (x : real) : (term118 x) = (term138 x).
Proof. exact (EQ_MP (@lem1357665 x) (@lem1357643 x)). Qed.
Lemma lem1357771 (x : real) : (term47 x) = (term138 x).
Proof. exact (TRANS (@lem1357639 x) (@lem1357666 x)). Qed.
Lemma lem1357772 : term48 = term139.
Proof. exact (fun_ext (fun x : real => @lem1357771 x)). Qed.
Lemma lem1357773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357774 : term49 = term140.
Proof. exact (MK_COMB (@lem1357773) (@lem1357772)). Qed.
Lemma lem1357776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1357777 (P : real -> Prop) (Q : real -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem1357776 real P Q). Qed.
Lemma lem1357778 : term141 = term142.
Proof. exact (@lem1357777 term143 term144). Qed.
Lemma lem1357779 (x : real) : (term145 x) = (term132 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem1357780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357781 (x : real) : (term146 x) = (term134 x).
Proof. exact (MK_COMB (@lem1357780) (@lem1357779 x)). Qed.
Lemma lem1357782 (x : real) : (term147 x) = (term137 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1357783 (x : real) : (term148 x) = (term138 x).
Proof. exact (MK_COMB (@lem1357781 x) (@lem1357782 x)). Qed.
Lemma lem1357784 : term149 = term139.
Proof. exact (fun_ext (fun x : real => @lem1357783 x)). Qed.
Lemma lem1357785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357786 : term141 = term140.
Proof. exact (MK_COMB (@lem1357785) (@lem1357784)). Qed.
Lemma lem1357787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1357788 : term150 = term151.
Proof. exact (MK_COMB (@lem1357787) (@lem1357786)). Qed.
Lemma lem1357789 (x : real) : (term145 x) = (term132 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem1357790 : term152 = term143.
Proof. exact (fun_ext (fun x : real => @lem1357789 x)). Qed.
Lemma lem1357791 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357792 : term153 = term154.
Proof. exact (MK_COMB (@lem1357791) (@lem1357790)). Qed.
Lemma lem1357793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1357794 : term155 = term156.
Proof. exact (MK_COMB (@lem1357793) (@lem1357792)). Qed.
Lemma lem1357795 (x : real) : (term147 x) = (term137 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1357796 : term157 = term144.
Proof. exact (fun_ext (fun x : real => @lem1357795 x)). Qed.
Lemma lem1357797 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357798 : term158 = term159.
Proof. exact (MK_COMB (@lem1357797) (@lem1357796)). Qed.
Lemma lem1357799 : term142 = term160.
Proof. exact (MK_COMB (@lem1357794) (@lem1357798)). Qed.
Lemma lem1357800 : (term141 = term142) = (term140 = term160).
Proof. exact (MK_COMB (@lem1357788) (@lem1357799)). Qed.
Lemma lem1357801 : term140 = term160.
Proof. exact (EQ_MP (@lem1357800) (@lem1357778)). Qed.
Lemma lem1357916 : term49 = term160.
Proof. exact (TRANS (@lem1357774) (@lem1357801)). Qed.
Lemma lem1357917 : term10 = term160.
Proof. exact (TRANS (@lem1357501) (@lem1357916)). Qed.
Lemma lem1357918 (h1 : term10) : term160.
Proof. exact (EQ_MP (@lem1357917) (@lem1357424 h1)). Qed.
Lemma lem1357932 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1357933 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1357932 y x)). Qed.
Lemma lem1357934 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357935 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1357934) (@lem1357933 x)). Qed.
Lemma lem1357936 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1357935 x)). Qed.
Lemma lem1357937 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357938 : term31 = term31.
Proof. exact (MK_COMB (@lem1357937) (@lem1357936)). Qed.
Lemma lem1357939 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem1357938) (@lem1357464 h1)). Qed.
Lemma lem1357954 (x : real) : ((term24 x) = term25) = ((term24 x) = term25).
Proof. exact (eq_refl ((term24 x) = term25)). Qed.
Lemma lem1357955 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1357954 x)). Qed.
Lemma lem1357956 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357957 : term27 = term27.
Proof. exact (MK_COMB (@lem1357956) (@lem1357955)). Qed.
Lemma lem1357958 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1357957) (@lem1357477 h1)). Qed.
Lemma lem1357963 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1357978 (x : real) (y : real) (z : real) : (term103 x y z) = (term103 x y z).
Proof. exact (eq_refl (term103 x y z)). Qed.
Lemma lem1357979 (x : real) (y : real) : (term101 x y) = (term101 x y).
Proof. exact (fun_ext (fun z : real => @lem1357978 x y z)). Qed.
Lemma lem1357980 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357981 (x : real) (y : real) : (term112 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1357980) (@lem1357979 x y)). Qed.
Lemma lem1357982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1357983 (x : real) (y : real) : (term114 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1357982) (@lem1357981 x y)). Qed.
Lemma lem1357984 (x : real) (y : real) : (term115 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1357983 x y) (@lem1357963 x y)). Qed.
Lemma lem1357985 (x : real) : (term122 x) = (term122 x).
Proof. exact (fun_ext (fun y : real => @lem1357984 x y)). Qed.
Lemma lem1357986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357987 (x : real) : (term137 x) = (term137 x).
Proof. exact (MK_COMB (@lem1357986) (@lem1357985 x)). Qed.
Lemma lem1357988 : term144 = term144.
Proof. exact (fun_ext (fun x : real => @lem1357987 x)). Qed.
Lemma lem1357989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1357990 : term159 = term159.
Proof. exact (MK_COMB (@lem1357989) (@lem1357988)). Qed.
Lemma lem1357997 (x : real) (y : real) : (term84 x y) = (term84 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1358010 (x : real) (y : real) (z : real) : ((real_add x z) = (real_add y z)) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl ((real_add x z) = (real_add y z))). Qed.
Lemma lem1358011 (x : real) (y : real) : (term83 x y) = (term83 x y).
Proof. exact (fun_ext (fun z : real => @lem1358010 x y z)). Qed.
Lemma lem1358012 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358013 (x : real) (y : real) : (term94 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1358012) (@lem1358011 x y)). Qed.
Lemma lem1358014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1358015 (x : real) (y : real) : (term96 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1358014) (@lem1358013 x y)). Qed.
Lemma lem1358016 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1358015 x y) (@lem1357997 x y)). Qed.
Lemma lem1358017 (x : real) : (term121 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1358016 x y)). Qed.
Lemma lem1358018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358019 (x : real) : (term132 x) = (term132 x).
Proof. exact (MK_COMB (@lem1358018) (@lem1358017 x)). Qed.
Lemma lem1358020 : term143 = term143.
Proof. exact (fun_ext (fun x : real => @lem1358019 x)). Qed.
Lemma lem1358021 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358022 : term154 = term154.
Proof. exact (MK_COMB (@lem1358021) (@lem1358020)). Qed.
Lemma lem1358023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1358024 : term156 = term156.
Proof. exact (MK_COMB (@lem1358023) (@lem1358022)). Qed.
Lemma lem1358025 : term160 = term160.
Proof. exact (MK_COMB (@lem1358024) (@lem1357990)). Qed.
Lemma lem1358026 (h1 : term10) : term160.
Proof. exact (EQ_MP (@lem1358025) (@lem1357918 h1)). Qed.
Lemma lem1358038 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1358039 (h1 : term10) : term159.
Proof. exact (proj2 (@lem1358026 h1)). Qed.
Lemma lem1358042 (y : real) (x : real) : ((real_add x y) = (real_add y x)) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl ((real_add x y) = (real_add y x))). Qed.
Lemma lem1358043 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1358042 y x)). Qed.
Lemma lem1358044 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358045 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1358044) (@lem1358043 x)). Qed.
Lemma lem1358046 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1358045 x)). Qed.
Lemma lem1358047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358049 : term31 = term31.
Proof. exact (MK_COMB (@lem1358047) (@lem1358046)). Qed.
Lemma lem1358050 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem1358049) (@lem1357939 h1)). Qed.
Lemma lem1358052 (x : real) : ((term24 x) = term25) = ((term24 x) = term25).
Proof. exact (eq_refl ((term24 x) = term25)). Qed.
Lemma lem1358053 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1358052 x)). Qed.
Lemma lem1358054 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358056 : term27 = term27.
Proof. exact (MK_COMB (@lem1358054) (@lem1358053)). Qed.
Lemma lem1358057 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1358056) (@lem1357958 h1)). Qed.
Lemma lem1358061 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1358111 {A : Type'} (P : A -> Prop) (Q : Prop) : (term78 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1358112 (P : real -> Prop) (Q : Prop) : (term80 P Q) = (term79 P Q).
Proof. exact (@lem1358111 real P Q). Qed.
Lemma lem1358113 (x : real) (y : real) : (term100 x y) = (term99 x y).
Proof. exact (@lem1358112 (term101 x y) (x = y)). Qed.
Lemma lem1358114 (x : real) (y : real) (z : real) : (term102 x y z) = (term103 x y z).
Proof. exact (eq_refl (term102 x y z)). Qed.
Lemma lem1358115 (x : real) (y : real) : (term110 x y) = (term101 x y).
Proof. exact (fun_ext (fun z : real => @lem1358114 x y z)). Qed.
Lemma lem1358116 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358117 (x : real) (y : real) : (term111 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1358116) (@lem1358115 x y)). Qed.
Lemma lem1358118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1358119 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1358118) (@lem1358117 x y)). Qed.
Lemma lem1358120 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1358121 (x : real) (y : real) : (term100 x y) = (term115 x y).
Proof. exact (MK_COMB (@lem1358119 x y) (@lem1358120 x y)). Qed.
Lemma lem1358122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1358123 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (MK_COMB (@lem1358122) (@lem1358121 x y)). Qed.
Lemma lem1358124 (x : real) (y : real) (z : real) : (term102 x y z) = (term103 x y z).
Proof. exact (eq_refl (term102 x y z)). Qed.
Lemma lem1358125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1358126 (x : real) (y : real) (z : real) : (term104 x y z) = (term105 x y z).
Proof. exact (MK_COMB (@lem1358125) (@lem1358124 x y z)). Qed.
Lemma lem1358127 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1358128 (z : real) (x : real) (y : real) : (term106 z x y) = (term63 z x y).
Proof. exact (MK_COMB (@lem1358126 x y z) (@lem1358127 x y)). Qed.
Lemma lem1358129 (x : real) (y : real) : (term107 x y) = (term57 x y).
Proof. exact (fun_ext (fun z : real => @lem1358128 z x y)). Qed.
Lemma lem1358130 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358131 (x : real) (y : real) : (term99 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1358130) (@lem1358129 x y)). Qed.
Lemma lem1358132 (x : real) (y : real) : ((term100 x y) = (term99 x y)) = ((term115 x y) = (term75 x y)).
Proof. exact (MK_COMB (@lem1358123 x y) (@lem1358131 x y)). Qed.
Lemma lem1358133 (x : real) (y : real) : (term115 x y) = (term75 x y).
Proof. exact (EQ_MP (@lem1358132 x y) (@lem1358113 x y)). Qed.
Lemma lem1358134 (x : real) : (term122 x) = (term163 x).
Proof. exact (fun_ext (fun y : real => @lem1358133 x y)). Qed.
Lemma lem1358135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358136 (x : real) : (term137 x) = (term164 x).
Proof. exact (MK_COMB (@lem1358135) (@lem1358134 x)). Qed.
Lemma lem1358137 : term144 = term165.
Proof. exact (fun_ext (fun x : real => @lem1358136 x)). Qed.
Lemma lem1358138 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358139 : term159 = term166.
Proof. exact (MK_COMB (@lem1358138) (@lem1358137)). Qed.
Lemma lem1358146 (z : real) (x : real) (y : real) : (term63 z x y) = (term63 z x y).
Proof. exact (eq_refl (term63 z x y)). Qed.
Lemma lem1358147 (x : real) (y : real) : (term57 x y) = (term57 x y).
Proof. exact (fun_ext (fun z : real => @lem1358146 z x y)). Qed.
Lemma lem1358148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358149 (x : real) (y : real) : (term75 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1358148) (@lem1358147 x y)). Qed.
Lemma lem1358150 (x : real) : (term163 x) = (term163 x).
Proof. exact (fun_ext (fun y : real => @lem1358149 x y)). Qed.
Lemma lem1358151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358152 (x : real) : (term164 x) = (term164 x).
Proof. exact (MK_COMB (@lem1358151) (@lem1358150 x)). Qed.
Lemma lem1358153 : term165 = term165.
Proof. exact (fun_ext (fun x : real => @lem1358152 x)). Qed.
Lemma lem1358154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358155 : term166 = term166.
Proof. exact (MK_COMB (@lem1358154) (@lem1358153)). Qed.
Lemma lem1358156 : term159 = term166.
Proof. exact (TRANS (@lem1358139) (@lem1358155)). Qed.
Lemma lem1358157 (h1 : term10) : term166.
Proof. exact (EQ_MP (@lem1358156) (@lem1358039 h1)). Qed.
Lemma lem1358158 (_24151 : real) (h1 : term31) : term167 _24151.
Proof. exact (@lem1358050 h1 _24151). Qed.
Lemma lem1358159 (_24151 : real) : (term167 _24151) = (term29 _24151).
Proof. exact (eq_refl (term167 _24151)). Qed.
Lemma lem1358160 (_24151 : real) (h1 : term31) : term29 _24151.
Proof. exact (EQ_MP (@lem1358159 _24151) (@lem1358158 _24151 h1)). Qed.
Lemma lem1358161 (_24151 : real) (_24152 : real) (h1 : term31) : term168 _24151 _24152.
Proof. exact (@lem1358160 _24151 h1 _24152). Qed.
Lemma lem1358162 (_24152 : real) (_24151 : real) : (term168 _24151 _24152) = ((real_add _24151 _24152) = (real_add _24152 _24151)).
Proof. exact (eq_refl (term168 _24151 _24152)). Qed.
Lemma lem1358164 (_24153 : real) (h1 : term27) : term169 _24153.
Proof. exact (@lem1358057 h1 _24153). Qed.
Lemma lem1358165 (_24153 : real) : (term169 _24153) = ((term24 _24153) = term25).
Proof. exact (eq_refl (term169 _24153)). Qed.
Lemma lem1358176 (_24157 : real) (h1 : term10) : term170 _24157.
Proof. exact (@lem1358157 h1 _24157). Qed.
Lemma lem1358177 (_24157 : real) : (term170 _24157) = (term164 _24157).
Proof. exact (eq_refl (term170 _24157)). Qed.
Lemma lem1358178 (_24157 : real) (h1 : term10) : term164 _24157.
Proof. exact (EQ_MP (@lem1358177 _24157) (@lem1358176 _24157 h1)). Qed.
Lemma lem1358179 (_24157 : real) (_24158 : real) (h1 : term10) : term171 _24157 _24158.
Proof. exact (@lem1358178 _24157 h1 _24158). Qed.
Lemma lem1358180 (_24157 : real) (_24158 : real) : (term171 _24157 _24158) = (term75 _24157 _24158).
Proof. exact (eq_refl (term171 _24157 _24158)). Qed.
Lemma lem1358181 (_24157 : real) (_24158 : real) (h1 : term10) : term75 _24157 _24158.
Proof. exact (EQ_MP (@lem1358180 _24157 _24158) (@lem1358179 _24157 _24158 h1)). Qed.
Lemma lem1358182 (_24157 : real) (_24158 : real) (_24159 : real) (h1 : term10) : term62 _24157 _24158 _24159.
Proof. exact (@lem1358181 _24157 _24158 h1 _24159). Qed.
Lemma lem1358183 (_24159 : real) (_24157 : real) (_24158 : real) : (term62 _24157 _24158 _24159) = (term63 _24159 _24157 _24158).
Proof. exact (eq_refl (term62 _24157 _24158 _24159)). Qed.
Lemma lem1358190 (x : real) (h1 : term39 x) : term39 x.
Proof. exact (h1). Qed.
Lemma lem1358202 (_24159 : real) (_24157 : real) (_24158 : real) (h1 : term10) : term63 _24159 _24157 _24158.
Proof. exact (EQ_MP (@lem1358183 _24159 _24157 _24158) (@lem1358182 _24157 _24158 _24159 h1)). Qed.
Lemma lem1358227 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1358228 (_24166 : real) (_24168 : real) (h1 : _24166 = _24168) : _24166 = _24168.
Proof. exact (h1). Qed.
Lemma lem1358229 (_24167 : real) (_24169 : real) (h1 : _24167 = _24169) : _24167 = _24169.
Proof. exact (h1). Qed.
Lemma lem1358230 (_24166 : real) (_24168 : real) (h1 : _24166 = _24168) : (real_add _24166) = (real_add _24168).
Proof. exact (MK_COMB (@lem1358227) (@lem1358228 _24166 _24168 h1)). Qed.
Lemma lem1358231 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) (h1 : _24166 = _24168) (h2 : _24167 = _24169) : (real_add _24166 _24167) = (real_add _24168 _24169).
Proof. exact (MK_COMB (@lem1358230 _24166 _24168 h1) (@lem1358229 _24167 _24169 h2)). Qed.
Lemma lem1358232 (_24167 : real) (_24169 : real) (_24166 : real) (_24168 : real) (h1 : _24166 = _24168) : term172 _24166 _24167 _24168 _24169.
Proof. exact (fun h0 : _24167 = _24169 => @lem1358231 _24166 _24168 _24167 _24169 h1 h0). Qed.
Lemma lem1358234 (a : Prop) (b : Prop) : (a -> b) = (term173 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1358235 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : (term172 _24166 _24167 _24168 _24169) = (term174 _24166 _24167 _24168 _24169).
Proof. exact (@lem1358234 (_24167 = _24169) ((real_add _24166 _24167) = (real_add _24168 _24169))). Qed.
Lemma lem1358236 (_24167 : real) (_24169 : real) (_24166 : real) (_24168 : real) (h1 : _24166 = _24168) : term174 _24166 _24167 _24168 _24169.
Proof. exact (EQ_MP (@lem1358235 _24166 _24167 _24168 _24169) (@lem1358232 _24167 _24169 _24166 _24168 h1)). Qed.
Lemma lem1358237 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : term175 _24166 _24167 _24168 _24169.
Proof. exact (fun h0 : _24166 = _24168 => @lem1358236 _24167 _24169 _24166 _24168 h0). Qed.
Lemma lem1358239 (a : Prop) (b : Prop) : (a -> b) = (term173 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1358240 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : (term175 _24166 _24167 _24168 _24169) = (term176 _24166 _24167 _24168 _24169).
Proof. exact (@lem1358239 (_24166 = _24168) (term174 _24166 _24167 _24168 _24169)). Qed.
Lemma lem1358241 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : term176 _24166 _24167 _24168 _24169.
Proof. exact (EQ_MP (@lem1358240 _24166 _24167 _24168 _24169) (@lem1358237 _24166 _24167 _24168 _24169)). Qed.
Lemma lem1358243 (x : real) (y : real) (z : real) : term177 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1358247 (_24152 : real) (_24151 : real) (h1 : term31) : (real_add _24151 _24152) = (real_add _24152 _24151).
Proof. exact (EQ_MP (@lem1358162 _24152 _24151) (@lem1358161 _24151 _24152 h1)). Qed.
Lemma lem1358248 (x : real) (h1 : term31) : (term178 x) = (term179 x).
Proof. exact (@lem1358247 (term180 x) term25 h1). Qed.
Lemma lem1358249 (x : real) (h1 : term31) : term181 x.
Proof. exact (fun h0 : term182 x => @lem1358248 x h1). Qed.
Lemma lem1358251 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358252 (x : real) : (term181 x) = ((term178 x) = (term179 x)).
Proof. exact (@lem1358251 ((term178 x) = (term179 x))). Qed.
Lemma lem1358253 (x : real) (h1 : term31) : (term178 x) = (term179 x).
Proof. exact (EQ_MP (@lem1358252 x) (@lem1358249 x h1)). Qed.
Lemma lem1358255 (_24153 : real) (h1 : term27) : (term24 _24153) = term25.
Proof. exact (EQ_MP (@lem1358165 _24153) (@lem1358164 _24153 h1)). Qed.
Lemma lem1358256 (x : real) (h1 : term27) : (term24 x) = term25.
Proof. exact (@lem1358255 x h1). Qed.
Lemma lem1358257 (x : real) (h1 : term27) : term184 x.
Proof. exact (fun h0 : term185 x => @lem1358256 x h1). Qed.
Lemma lem1358259 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358260 (x : real) : (term184 x) = ((term24 x) = term25).
Proof. exact (@lem1358259 ((term24 x) = term25)). Qed.
Lemma lem1358261 (x : real) (h1 : term27) : (term24 x) = term25.
Proof. exact (EQ_MP (@lem1358260 x) (@lem1358257 x h1)). Qed.
Lemma lem1358263 (_24152 : real) (_24151 : real) (h1 : term31) : (real_add _24151 _24152) = (real_add _24152 _24151).
Proof. exact (EQ_MP (@lem1358162 _24152 _24151) (@lem1358161 _24151 _24152 h1)). Qed.
Lemma lem1358264 (x : real) (h1 : term31) : (term24 x) = (term186 x).
Proof. exact (@lem1358263 x (real_neg x) h1). Qed.
Lemma lem1358265 (x : real) (h1 : term31) : term187 x.
Proof. exact (fun h0 : term188 x => @lem1358264 x h1). Qed.
Lemma lem1358267 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358268 (x : real) : (term187 x) = ((term24 x) = (term186 x)).
Proof. exact (@lem1358267 ((term24 x) = (term186 x))). Qed.
Lemma lem1358269 (x : real) (h1 : term31) : (term24 x) = (term186 x).
Proof. exact (EQ_MP (@lem1358268 x) (@lem1358265 x h1)). Qed.
Lemma lem1358287 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1358288 (y : real) (x : real) (z : real) : (term189 x y z) = (term190 y x z).
Proof. exact (@lem1358287 (y = z) (term84 x z)). Qed.
Lemma lem1358298 (x : real) (y : real) : (term191 x y) = (term191 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1358299 (y : real) (x : real) (z : real) : (term177 x y z) = (term192 y x z).
Proof. exact (MK_COMB (@lem1358298 x y) (@lem1358288 y x z)). Qed.
Lemma lem1358303 (q : Prop) (p : Prop) (r : Prop) : (term193 p q r) = (term193 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1358304 (y : real) (x : real) (z : real) : (term192 y x z) = (term194 y x z).
Proof. exact (@lem1358303 (y = z) (term84 x y) (term84 x z)). Qed.
Lemma lem1358326 (y : real) (x : real) (z : real) : (term177 x y z) = (term194 y x z).
Proof. exact (TRANS (@lem1358299 y x z) (@lem1358304 y x z)). Qed.
Lemma lem1358327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1358328 (y : real) (x : real) (z : real) : (term195 x y z) = (term196 y x z).
Proof. exact (MK_COMB (@lem1358327) (@lem1358326 y x z)). Qed.
Lemma lem1358350 (y : real) (x : real) (z : real) : (term194 y x z) = (term194 y x z).
Proof. exact (eq_refl (term194 y x z)). Qed.
Lemma lem1358351 (y : real) (x : real) (z : real) : ((term177 x y z) = (term194 y x z)) = ((term194 y x z) = (term194 y x z)).
Proof. exact (MK_COMB (@lem1358328 y x z) (@lem1358350 y x z)). Qed.
Lemma lem1358353 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1358354 (x : Prop) : (x = x) = True.
Proof. exact (@lem1358353 Prop x). Qed.
Lemma lem1358355 (y : real) (x : real) (z : real) : ((term194 y x z) = (term194 y x z)) = True.
Proof. exact (@lem1358354 (term194 y x z)). Qed.
Lemma lem1358356 (y : real) (x : real) (z : real) : ((term177 x y z) = (term194 y x z)) = True.
Proof. exact (TRANS (@lem1358351 y x z) (@lem1358355 y x z)). Qed.
Lemma lem1358357 (y : real) (x : real) (z : real) : True = ((term177 x y z) = (term194 y x z)).
Proof. exact (SYM (@lem1358356 y x z)). Qed.
Lemma lem1358358 (y : real) (x : real) (z : real) : (term177 x y z) = (term194 y x z).
Proof. exact (EQ_MP (@lem1358357 y x z) (@lem0)). Qed.
Lemma lem1358359 (y : real) (x : real) (z : real) : term194 y x z.
Proof. exact (EQ_MP (@lem1358358 y x z) (@lem1358243 x y z)). Qed.
Lemma lem1358361 (b : Prop) (a : Prop) : (a \/ b) = (term197 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1358362 (x : real) (y : real) (z : real) : (term194 y x z) = (term198 x y z).
Proof. exact (@lem1358361 (term199 y x z) (y = z)). Qed.
Lemma lem1358364 (a : Prop) (b : Prop) : (term200 a b) = (term201 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1358365 (y : real) (x : real) (z : real) : (term202 y x z) = (term203 y x z).
Proof. exact (@lem1358364 (term84 x y) (term84 x z)). Qed.
Lemma lem1358367 (a : Prop) : (term204 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1358368 (x : real) (y : real) : (term205 x y) = (x = y).
Proof. exact (@lem1358367 (x = y)). Qed.
Lemma lem1358369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1358370 (x : real) (y : real) : (term206 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1358369) (@lem1358368 x y)). Qed.
Lemma lem1358372 (a : Prop) : (term204 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1358373 (x : real) (z : real) : (term205 x z) = (x = z).
Proof. exact (@lem1358372 (x = z)). Qed.
Lemma lem1358374 (y : real) (x : real) (z : real) : (term203 y x z) = (term208 y x z).
Proof. exact (MK_COMB (@lem1358370 x y) (@lem1358373 x z)). Qed.
Lemma lem1358375 (y : real) (x : real) (z : real) : (term202 y x z) = (term208 y x z).
Proof. exact (TRANS (@lem1358365 y x z) (@lem1358374 y x z)). Qed.
Lemma lem1358376 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358377 (y : real) (x : real) (z : real) : (term209 y x z) = (term210 y x z).
Proof. exact (MK_COMB (@lem1358376) (@lem1358375 y x z)). Qed.
Lemma lem1358378 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1358379 (x : real) (y : real) (z : real) : (term198 x y z) = (term211 x y z).
Proof. exact (MK_COMB (@lem1358377 y x z) (@lem1358378 y z)). Qed.
Lemma lem1358380 (x : real) (y : real) (z : real) : (term194 y x z) = (term211 x y z).
Proof. exact (TRANS (@lem1358362 x y z) (@lem1358379 x y z)). Qed.
Lemma lem1358382 (x : real) (h1 : term31) (h2 : term27) : term212 x.
Proof. exact (conj (@lem1358261 x h2) (@lem1358269 x h1)). Qed.
Lemma lem1358384 (x : real) (y : real) (z : real) : term211 x y z.
Proof. exact (EQ_MP (@lem1358380 x y z) (@lem1358359 y x z)). Qed.
Lemma lem1358385 (x : real) : term213 x.
Proof. exact (@lem1358384 (term24 x) term25 (term186 x)). Qed.
Lemma lem1358388 (x : real) (h1 : term31) (h2 : term27) : term25 = (term186 x).
Proof. exact (@lem1358385 x (@lem1358382 x h1 h2)). Qed.
Lemma lem1358389 (x : real) (h1 : term31) (h2 : term27) : term214 x.
Proof. exact (fun h0 : term215 x => @lem1358388 x h1 h2). Qed.
Lemma lem1358391 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358392 (x : real) : (term214 x) = (term25 = (term186 x)).
Proof. exact (@lem1358391 (term25 = (term186 x))). Qed.
Lemma lem1358393 (x : real) (h1 : term31) (h2 : term27) : term25 = (term186 x).
Proof. exact (EQ_MP (@lem1358392 x) (@lem1358389 x h1 h2)). Qed.
Lemma lem1358395 (_24153 : real) (h1 : term27) : (term24 _24153) = term25.
Proof. exact (EQ_MP (@lem1358165 _24153) (@lem1358164 _24153 h1)). Qed.
Lemma lem1358396 (x : real) (h1 : term27) : (term180 x) = term25.
Proof. exact (@lem1358395 (real_neg x) h1). Qed.
Lemma lem1358397 (x : real) (h1 : term27) : term216 x.
Proof. exact (fun h0 : term217 x => @lem1358396 x h1). Qed.
Lemma lem1358399 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358400 (x : real) : (term216 x) = ((term180 x) = term25).
Proof. exact (@lem1358399 ((term180 x) = term25)). Qed.
Lemma lem1358401 (x : real) (h1 : term27) : (term180 x) = term25.
Proof. exact (EQ_MP (@lem1358400 x) (@lem1358397 x h1)). Qed.
Lemma lem1358419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1358420 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term174 _24166 _24167 _24168 _24169) = (term218 _24166 _24168 _24167 _24169).
Proof. exact (@lem1358419 ((real_add _24166 _24167) = (real_add _24168 _24169)) (term84 _24167 _24169)). Qed.
Lemma lem1358430 (_24166 : real) (_24168 : real) : (term191 _24166 _24168) = (term191 _24166 _24168).
Proof. exact (eq_refl (term191 _24166 _24168)). Qed.
Lemma lem1358431 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term176 _24166 _24167 _24168 _24169) = (term219 _24166 _24168 _24167 _24169).
Proof. exact (MK_COMB (@lem1358430 _24166 _24168) (@lem1358420 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358435 (q : Prop) (p : Prop) (r : Prop) : (term193 p q r) = (term193 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1358436 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term219 _24166 _24168 _24167 _24169) = (term220 _24166 _24168 _24167 _24169).
Proof. exact (@lem1358435 ((real_add _24166 _24167) = (real_add _24168 _24169)) (term84 _24166 _24168) (term84 _24167 _24169)). Qed.
Lemma lem1358458 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term176 _24166 _24167 _24168 _24169) = (term220 _24166 _24168 _24167 _24169).
Proof. exact (TRANS (@lem1358431 _24166 _24168 _24167 _24169) (@lem1358436 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1358460 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term221 _24166 _24167 _24168 _24169) = (term222 _24166 _24168 _24167 _24169).
Proof. exact (MK_COMB (@lem1358459) (@lem1358458 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358482 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term220 _24166 _24168 _24167 _24169) = (term220 _24166 _24168 _24167 _24169).
Proof. exact (eq_refl (term220 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358483 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : ((term176 _24166 _24167 _24168 _24169) = (term220 _24166 _24168 _24167 _24169)) = ((term220 _24166 _24168 _24167 _24169) = (term220 _24166 _24168 _24167 _24169)).
Proof. exact (MK_COMB (@lem1358460 _24166 _24168 _24167 _24169) (@lem1358482 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358485 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1358486 (x : Prop) : (x = x) = True.
Proof. exact (@lem1358485 Prop x). Qed.
Lemma lem1358487 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : ((term220 _24166 _24168 _24167 _24169) = (term220 _24166 _24168 _24167 _24169)) = True.
Proof. exact (@lem1358486 (term220 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358488 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : ((term176 _24166 _24167 _24168 _24169) = (term220 _24166 _24168 _24167 _24169)) = True.
Proof. exact (TRANS (@lem1358483 _24166 _24168 _24167 _24169) (@lem1358487 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358489 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : True = ((term176 _24166 _24167 _24168 _24169) = (term220 _24166 _24168 _24167 _24169)).
Proof. exact (SYM (@lem1358488 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358490 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term176 _24166 _24167 _24168 _24169) = (term220 _24166 _24168 _24167 _24169).
Proof. exact (EQ_MP (@lem1358489 _24166 _24168 _24167 _24169) (@lem0)). Qed.
Lemma lem1358491 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : term220 _24166 _24168 _24167 _24169.
Proof. exact (EQ_MP (@lem1358490 _24166 _24168 _24167 _24169) (@lem1358241 _24166 _24167 _24168 _24169)). Qed.
Lemma lem1358493 (b : Prop) (a : Prop) : (a \/ b) = (term197 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1358494 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : (term220 _24166 _24168 _24167 _24169) = (term223 _24166 _24167 _24168 _24169).
Proof. exact (@lem1358493 (term224 _24166 _24168 _24167 _24169) ((real_add _24166 _24167) = (real_add _24168 _24169))). Qed.
Lemma lem1358496 (a : Prop) (b : Prop) : (term200 a b) = (term201 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1358497 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term225 _24166 _24168 _24167 _24169) = (term226 _24166 _24168 _24167 _24169).
Proof. exact (@lem1358496 (term84 _24166 _24168) (term84 _24167 _24169)). Qed.
Lemma lem1358499 (a : Prop) : (term204 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1358500 (_24166 : real) (_24168 : real) : (term205 _24166 _24168) = (_24166 = _24168).
Proof. exact (@lem1358499 (_24166 = _24168)). Qed.
Lemma lem1358501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1358502 (_24166 : real) (_24168 : real) : (term206 _24166 _24168) = (term207 _24166 _24168).
Proof. exact (MK_COMB (@lem1358501) (@lem1358500 _24166 _24168)). Qed.
Lemma lem1358504 (a : Prop) : (term204 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1358505 (_24167 : real) (_24169 : real) : (term205 _24167 _24169) = (_24167 = _24169).
Proof. exact (@lem1358504 (_24167 = _24169)). Qed.
Lemma lem1358506 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term226 _24166 _24168 _24167 _24169) = (term227 _24166 _24168 _24167 _24169).
Proof. exact (MK_COMB (@lem1358502 _24166 _24168) (@lem1358505 _24167 _24169)). Qed.
Lemma lem1358507 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term225 _24166 _24168 _24167 _24169) = (term227 _24166 _24168 _24167 _24169).
Proof. exact (TRANS (@lem1358497 _24166 _24168 _24167 _24169) (@lem1358506 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358508 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358509 (_24166 : real) (_24168 : real) (_24167 : real) (_24169 : real) : (term228 _24166 _24168 _24167 _24169) = (term229 _24166 _24168 _24167 _24169).
Proof. exact (MK_COMB (@lem1358508) (@lem1358507 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358510 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : ((real_add _24166 _24167) = (real_add _24168 _24169)) = ((real_add _24166 _24167) = (real_add _24168 _24169)).
Proof. exact (eq_refl ((real_add _24166 _24167) = (real_add _24168 _24169))). Qed.
Lemma lem1358511 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : (term223 _24166 _24167 _24168 _24169) = (term230 _24166 _24167 _24168 _24169).
Proof. exact (MK_COMB (@lem1358509 _24166 _24168 _24167 _24169) (@lem1358510 _24166 _24167 _24168 _24169)). Qed.
Lemma lem1358512 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : (term220 _24166 _24168 _24167 _24169) = (term230 _24166 _24167 _24168 _24169).
Proof. exact (TRANS (@lem1358494 _24166 _24167 _24168 _24169) (@lem1358511 _24166 _24167 _24168 _24169)). Qed.
Lemma lem1358514 (x : real) (h1 : term31) (h2 : term27) : term231 x.
Proof. exact (conj (@lem1358393 x h1 h2) (@lem1358401 x h2)). Qed.
Lemma lem1358516 (_24166 : real) (_24167 : real) (_24168 : real) (_24169 : real) : term230 _24166 _24167 _24168 _24169.
Proof. exact (EQ_MP (@lem1358512 _24166 _24167 _24168 _24169) (@lem1358491 _24166 _24168 _24167 _24169)). Qed.
Lemma lem1358517 (x : real) : term232 x.
Proof. exact (@lem1358516 term25 (term180 x) (term186 x) term25). Qed.
Lemma lem1358520 (x : real) (h1 : term31) (h2 : term27) : (term178 x) = (term233 x).
Proof. exact (@lem1358517 x (@lem1358514 x h1 h2)). Qed.
Lemma lem1358521 (x : real) (h1 : term31) (h2 : term27) : term234 x.
Proof. exact (fun h0 : term235 x => @lem1358520 x h1 h2). Qed.
Lemma lem1358523 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358524 (x : real) : (term234 x) = ((term178 x) = (term233 x)).
Proof. exact (@lem1358523 ((term178 x) = (term233 x))). Qed.
Lemma lem1358525 (x : real) (h1 : term31) (h2 : term27) : (term178 x) = (term233 x).
Proof. exact (EQ_MP (@lem1358524 x) (@lem1358521 x h1 h2)). Qed.
Lemma lem1358526 (x : real) (h1 : term31) (h2 : term27) : term236 x.
Proof. exact (conj (@lem1358253 x h1) (@lem1358525 x h1 h2)). Qed.
Lemma lem1358528 (x : real) (y : real) (z : real) : term211 x y z.
Proof. exact (EQ_MP (@lem1358380 x y z) (@lem1358359 y x z)). Qed.
Lemma lem1358529 (x : real) : term237 x.
Proof. exact (@lem1358528 (term178 x) (term179 x) (term233 x)). Qed.
Lemma lem1358532 (x : real) (h1 : term31) (h2 : term27) : (term179 x) = (term233 x).
Proof. exact (@lem1358529 x (@lem1358526 x h1 h2)). Qed.
Lemma lem1358533 (x : real) (h1 : term31) (h2 : term27) : term238 x.
Proof. exact (fun h0 : term239 x => @lem1358532 x h1 h2). Qed.
Lemma lem1358535 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358536 (x : real) : (term238 x) = ((term179 x) = (term233 x)).
Proof. exact (@lem1358535 ((term179 x) = (term233 x))). Qed.
Lemma lem1358537 (x : real) (h1 : term31) (h2 : term27) : (term179 x) = (term233 x).
Proof. exact (EQ_MP (@lem1358536 x) (@lem1358533 x h1 h2)). Qed.
Lemma lem1358543 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1358544 (_24157 : real) (_24158 : real) (_24159 : real) : (term63 _24159 _24157 _24158) = (term240 _24157 _24158 _24159).
Proof. exact (@lem1358543 (_24157 = _24158) (term103 _24157 _24158 _24159)). Qed.
Lemma lem1358554 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1358555 (_24157 : real) (_24158 : real) (_24159 : real) : (term241 _24159 _24157 _24158) = (term242 _24157 _24158 _24159).
Proof. exact (MK_COMB (@lem1358554) (@lem1358544 _24157 _24158 _24159)). Qed.
Lemma lem1358565 (_24157 : real) (_24158 : real) (_24159 : real) : (term240 _24157 _24158 _24159) = (term240 _24157 _24158 _24159).
Proof. exact (eq_refl (term240 _24157 _24158 _24159)). Qed.
Lemma lem1358566 (_24157 : real) (_24158 : real) (_24159 : real) : ((term63 _24159 _24157 _24158) = (term240 _24157 _24158 _24159)) = ((term240 _24157 _24158 _24159) = (term240 _24157 _24158 _24159)).
Proof. exact (MK_COMB (@lem1358555 _24157 _24158 _24159) (@lem1358565 _24157 _24158 _24159)). Qed.
Lemma lem1358568 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1358569 (x : Prop) : (x = x) = True.
Proof. exact (@lem1358568 Prop x). Qed.
Lemma lem1358570 (_24157 : real) (_24158 : real) (_24159 : real) : ((term240 _24157 _24158 _24159) = (term240 _24157 _24158 _24159)) = True.
Proof. exact (@lem1358569 (term240 _24157 _24158 _24159)). Qed.
Lemma lem1358571 (_24157 : real) (_24158 : real) (_24159 : real) : ((term63 _24159 _24157 _24158) = (term240 _24157 _24158 _24159)) = True.
Proof. exact (TRANS (@lem1358566 _24157 _24158 _24159) (@lem1358570 _24157 _24158 _24159)). Qed.
Lemma lem1358572 (_24157 : real) (_24158 : real) (_24159 : real) : True = ((term63 _24159 _24157 _24158) = (term240 _24157 _24158 _24159)).
Proof. exact (SYM (@lem1358571 _24157 _24158 _24159)). Qed.
Lemma lem1358573 (_24157 : real) (_24158 : real) (_24159 : real) : (term63 _24159 _24157 _24158) = (term240 _24157 _24158 _24159).
Proof. exact (EQ_MP (@lem1358572 _24157 _24158 _24159) (@lem0)). Qed.
Lemma lem1358574 (_24157 : real) (_24158 : real) (_24159 : real) (h1 : term10) : term240 _24157 _24158 _24159.
Proof. exact (EQ_MP (@lem1358573 _24157 _24158 _24159) (@lem1358202 _24159 _24157 _24158 h1)). Qed.
Lemma lem1358576 (b : Prop) (a : Prop) : (a \/ b) = (term197 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1358577 (_24159 : real) (_24157 : real) (_24158 : real) : (term240 _24157 _24158 _24159) = (term243 _24159 _24157 _24158).
Proof. exact (@lem1358576 (term103 _24157 _24158 _24159) (_24157 = _24158)). Qed.
Lemma lem1358579 (a : Prop) : (term204 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1358580 (_24157 : real) (_24158 : real) (_24159 : real) : (term244 _24157 _24158 _24159) = ((real_add _24157 _24159) = (real_add _24158 _24159)).
Proof. exact (@lem1358579 ((real_add _24157 _24159) = (real_add _24158 _24159))). Qed.
Lemma lem1358581 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358582 (_24157 : real) (_24158 : real) (_24159 : real) : (term245 _24157 _24158 _24159) = (term246 _24157 _24158 _24159).
Proof. exact (MK_COMB (@lem1358581) (@lem1358580 _24157 _24158 _24159)). Qed.
Lemma lem1358583 (_24157 : real) (_24158 : real) : (_24157 = _24158) = (_24157 = _24158).
Proof. exact (eq_refl (_24157 = _24158)). Qed.
Lemma lem1358584 (_24159 : real) (_24157 : real) (_24158 : real) : (term243 _24159 _24157 _24158) = (term247 _24159 _24157 _24158).
Proof. exact (MK_COMB (@lem1358582 _24157 _24158 _24159) (@lem1358583 _24157 _24158)). Qed.
Lemma lem1358585 (_24159 : real) (_24157 : real) (_24158 : real) : (term240 _24157 _24158 _24159) = (term247 _24159 _24157 _24158).
Proof. exact (TRANS (@lem1358577 _24159 _24157 _24158) (@lem1358584 _24159 _24157 _24158)). Qed.
Lemma lem1358588 (_24159 : real) (_24157 : real) (_24158 : real) (h1 : term10) : term247 _24159 _24157 _24158.
Proof. exact (EQ_MP (@lem1358585 _24159 _24157 _24158) (@lem1358574 _24157 _24158 _24159 h1)). Qed.
Lemma lem1358589 (x : real) (h1 : term10) : term248 x.
Proof. exact (@lem1358588 term25 (term180 x) (term186 x) h1). Qed.
Lemma lem1358592 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) : (term180 x) = (term186 x).
Proof. exact (@lem1358589 x h1 (@lem1358537 x h2 h3)). Qed.
Lemma lem1358593 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) : term249 x.
Proof. exact (fun h0 : term250 x => @lem1358592 x h1 h2 h3). Qed.
Lemma lem1358595 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358596 (x : real) : (term249 x) = ((term180 x) = (term186 x)).
Proof. exact (@lem1358595 ((term180 x) = (term186 x))). Qed.
Lemma lem1358597 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) : (term180 x) = (term186 x).
Proof. exact (EQ_MP (@lem1358596 x) (@lem1358593 x h1 h2 h3)). Qed.
Lemma lem1358599 (_24159 : real) (_24157 : real) (_24158 : real) (h1 : term10) : term247 _24159 _24157 _24158.
Proof. exact (EQ_MP (@lem1358585 _24159 _24157 _24158) (@lem1358574 _24157 _24158 _24159 h1)). Qed.
Lemma lem1358600 (x : real) (h1 : term10) : term251 x.
Proof. exact (@lem1358599 (real_neg x) (term32 x) x h1). Qed.
Lemma lem1358603 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) : (term32 x) = x.
Proof. exact (@lem1358600 x h1 (@lem1358597 x h1 h2 h3)). Qed.
Lemma lem1358604 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) : term252 x.
Proof. exact (fun h0 : term39 x => @lem1358603 x h1 h2 h3). Qed.
Lemma lem1358606 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358607 (x : real) : (term252 x) = ((term32 x) = x).
Proof. exact (@lem1358606 ((term32 x) = x)). Qed.
Lemma lem1358608 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1358607 x) (@lem1358604 x h1 h2 h3)). Qed.
Lemma lem1358611 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1358613 (x : real) : (term39 x) = (term253 x).
Proof. exact (@lem1358611 ((term32 x) = x)). Qed.
Lemma lem1358616 (x : real) (h1 : term39 x) : term253 x.
Proof. exact (EQ_MP (@lem1358613 x) (@lem1358190 x h1)). Qed.
Lemma lem1358619 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (@lem1358616 x h4 (@lem1358608 x h1 h2 h3)). Qed.
Lemma lem1358620 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : term254.
Proof. exact (fun h0 : ~ False => @lem1358619 x h1 h2 h3 h4). Qed.
Lemma lem1358622 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1358623 : term254 = False.
Proof. exact (@lem1358622 False). Qed.
Lemma lem1358624 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358623) (@lem1358620 x h1 h2 h3 h4)). Qed.
Lemma lem1358625 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : (term39 x) = False.
Proof. exact (prop_ext (fun h5 : term39 x => @lem1358624 x h1 h2 h3 h4) (fun h5 : False => @lem1358190 x h4)). Qed.
Lemma lem1358626 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358625 x h1 h2 h3 h4) (@lem1358190 x h4)). Qed.
Lemma lem1358627 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : (term39 x) = False.
Proof. exact (prop_ext (fun h5 : term39 x => @lem1358626 x h1 h2 h3 h4) (fun h5 : False => @lem1358061 x h4)). Qed.
Lemma lem1358628 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358627 x h1 h2 h3 h4) (@lem1358061 x h4)). Qed.
Lemma lem1358629 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : (term39 x) = False.
Proof. exact (prop_ext (fun h5 : term39 x => @lem1358628 x h1 h2 h3 h4) (fun h5 : False => @lem1358061 x h4)). Qed.
Lemma lem1358630 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358629 x h1 h2 h3 h4) (@lem1358061 x h4)). Qed.
Lemma lem1358631 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : term27 = False.
Proof. exact (prop_ext (fun h5 : term27 => @lem1358630 x h1 h2 h3 h4) (fun h5 : False => @lem1358057 h3)). Qed.
Lemma lem1358632 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358631 x h1 h2 h3 h4) (@lem1358057 h3)). Qed.
Lemma lem1358633 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : term31 = False.
Proof. exact (prop_ext (fun h5 : term31 => @lem1358632 x h1 h2 h3 h4) (fun h5 : False => @lem1358050 h2)). Qed.
Lemma lem1358634 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358633 x h1 h2 h3 h4) (@lem1358050 h2)). Qed.
Lemma lem1358635 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : (term39 x) = False.
Proof. exact (prop_ext (fun h5 : term39 x => @lem1358634 x h1 h2 h3 h4) (fun h5 : False => @lem1358038 x h4)). Qed.
Lemma lem1358636 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358635 x h1 h2 h3 h4) (@lem1358038 x h4)). Qed.
Lemma lem1358637 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : term27 = False.
Proof. exact (prop_ext (fun h5 : term27 => @lem1358636 x h1 h2 h3 h4) (fun h5 : False => @lem1357958 h3)). Qed.
Lemma lem1358638 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358637 x h1 h2 h3 h4) (@lem1357958 h3)). Qed.
Lemma lem1358639 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : term31 = False.
Proof. exact (prop_ext (fun h5 : term31 => @lem1358638 x h1 h2 h3 h4) (fun h5 : False => @lem1357939 h2)). Qed.
Lemma lem1358640 (x : real) (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term39 x) : False.
Proof. exact (EQ_MP (@lem1358639 x h1 h2 h3 h4) (@lem1357939 h2)). Qed.
Lemma lem1358641 (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term3) : False.
Proof. exact (ex_elim (@lem1357444 h4) (fun x : real => fun h0 : term41 x => @lem1358640 x h1 h2 h3 h0)). Qed.
Lemma lem1358642 (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term3) : term27 = False.
Proof. exact (prop_ext (fun h5 : term27 => @lem1358641 h1 h2 h3 h4) (fun h5 : False => @lem1357477 h3)). Qed.
Lemma lem1358643 (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem1358642 h1 h2 h3 h4) (@lem1357477 h3)). Qed.
Lemma lem1358644 (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term3) : term31 = False.
Proof. exact (prop_ext (fun h5 : term31 => @lem1358643 h1 h2 h3 h4) (fun h5 : False => @lem1357464 h2)). Qed.
Lemma lem1358645 (h1 : term10) (h2 : term31) (h3 : term27) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem1358644 h1 h2 h3 h4) (@lem1357464 h2)). Qed.
Lemma lem1358646 (h1 : term31) (h2 : term27) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1358645 h0 h1 h2 h3). Qed.
Lemma lem1358647 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1358648 (h1 : term31) (h2 : term27) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem1358647) (@lem1358646 h1 h2 h3)). Qed.
Lemma lem1358649 (h1 : term31) (h2 : term3) : term13.
Proof. exact (fun h0 : term27 => @lem1358648 h1 h0 h2). Qed.
Lemma lem1358650 (h1 : term3) : term16.
Proof. exact (fun h0 : term31 => @lem1358649 h0 h1). Qed.
Lemma lem1358651 : term18.
Proof. exact (fun h0 : term3 => @lem1358650 h0). Qed.
Lemma lem1358652 : term4.
Proof. exact (EQ_MP (@lem1357420) (@lem1358651)). Qed.
Lemma lem1358654 : term4.
Proof. exact (@lem1357273 (@lem1358652)). Qed.
Lemma lem1358655 (h1 : term3) : term15.
Proof. exact (@lem1358654 (@lem1357258 h1)). Qed.
Lemma lem1358656 (h1 : term3) : term12.
Proof. exact (@lem1358655 h1 (@lem1338238)). Qed.
Lemma lem1358657 (h1 : term3) : term8.
Proof. exact (@lem1358656 h1 (@lem1338588)). Qed.
Lemma lem1358658 (h1 : term3) : False.
Proof. exact (@lem1358657 h1 (@lem1355147)). Qed.
Lemma lem1358659 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1358658 h1) (fun h2 : False => @lem1357258 h1)). Qed.
Lemma lem1358660 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1358659 h1) (@lem1357258 h1)). Qed.
Lemma lem1358661 : term2.
Proof. exact (fun h0 : term3 => @lem1358660 h0). Qed.
Lemma lem1358662 : term1.
Proof. exact (EQ_MP (@lem1357257) (@lem1358661)). Qed.
