Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_LE_ELEMENT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_INF_LE_spec.
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
Lemma lem5282346 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5282347 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5282348 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5282347 t1) (@lem5282346 t1)). Qed.
Lemma lem5282349 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5282348 t1 t2). Qed.
Lemma lem5282350 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5282351 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5282350 t1 t2) (@lem5282349 t1 t2)). Qed.
Lemma lem5282352 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5282351 t1 t2 t3). Qed.
Lemma lem5282353 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5282354 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5282353 t1 t2 t3) (@lem5282352 t1 t2 t3)). Qed.
Lemma lem5282355 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5282354 t1 t2 t3)). Qed.
Lemma lem5282357 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5282358 : term8 = term9.
Proof. exact (@lem5282357 term8). Qed.
Lemma lem5282359 : term9 = term8.
Proof. exact (SYM (@lem5282358)). Qed.
Lemma lem5282360 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5282363 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5282364 : term12.
Proof. exact (fun h0 : term11 => @lem5282363 h0). Qed.
Lemma lem5282365 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5282366 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5282367 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5282365 h2 (@lem5282366 h1)). Qed.
Lemma lem5282368 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5282367 h1 h0). Qed.
Lemma lem5282369 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5282370 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5282368 h1 (@lem5282369 h2)). Qed.
Lemma lem5282371 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5282370 h0 h1). Qed.
Lemma lem5282372 : term14.
Proof. exact (fun h0 : term12 => @lem5282371 h0). Qed.
Lemma lem5282375 : term12.
Proof. exact (@lem5282372 (@lem5282364)). Qed.
Lemma lem5282407 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5282408 : term15 = term16.
Proof. exact (@lem5282407 term17). Qed.
Lemma lem5282437 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5282438 : term19 = term20.
Proof. exact (MK_COMB (@lem5282437) (@lem5282408)). Qed.
Lemma lem5282441 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5282448 : term11 = term22.
Proof. exact (MK_COMB (@lem5282441) (@lem5282438)). Qed.
Lemma lem5282449 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5282454 (s : real -> Prop) (a : real) (x : real) : (term24 s a x) = (term24 s a x).
Proof. exact (eq_refl (term24 s a x)). Qed.
Lemma lem5282455 (s : real -> Prop) (a : real) : (term25 s a) = (term25 s a).
Proof. exact (fun_ext (fun x : real => @lem5282454 s a x)). Qed.
Lemma lem5282456 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282457 (s : real -> Prop) (a : real) : (term26 s a) = (term26 s a).
Proof. exact (MK_COMB (@lem5282456) (@lem5282455 s a)). Qed.
Lemma lem5282460 (y : real) (b : real) : (term27 y b) = (term27 y b).
Proof. exact (eq_refl (term27 y b)). Qed.
Lemma lem5282461 (y : real) (b : real) (s : real -> Prop) (a : real) : (term28 y b s a) = (term28 y b s a).
Proof. exact (MK_COMB (@lem5282460 y b) (@lem5282457 s a)). Qed.
Lemma lem5282464 (y : real) (s : real -> Prop) : (term29 y s) = (term29 y s).
Proof. exact (eq_refl (term29 y s)). Qed.
Lemma lem5282465 (y : real) (b : real) (s : real -> Prop) (a : real) : (term30 y b s a) = (term30 y b s a).
Proof. exact (MK_COMB (@lem5282464 y s) (@lem5282461 y b s a)). Qed.
Lemma lem5282466 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5282467 (y : real) (b : real) (s : real -> Prop) (a : real) : (term31 y b s a) = (term31 y b s a).
Proof. exact (MK_COMB (@lem5282466) (@lem5282465 y b s a)). Qed.
Lemma lem5282468 (y : real) (a : real) (s : real -> Prop) (b : real) : (term32 y a s b) = (term32 y a s b).
Proof. exact (MK_COMB (@lem5282467 y b s a) (@lem5282449 s b)). Qed.
Lemma lem5282469 (a : real) (s : real -> Prop) (b : real) : (term33 a s b) = (term33 a s b).
Proof. exact (fun_ext (fun y : real => @lem5282468 y a s b)). Qed.
Lemma lem5282470 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282471 (a : real) (s : real -> Prop) (b : real) : (term34 a s b) = (term34 a s b).
Proof. exact (MK_COMB (@lem5282470) (@lem5282469 a s b)). Qed.
Lemma lem5282472 (a : real) (s : real -> Prop) : (term35 a s) = (term35 a s).
Proof. exact (fun_ext (fun b : real => @lem5282471 a s b)). Qed.
Lemma lem5282473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282474 (a : real) (s : real -> Prop) : (term36 a s) = (term36 a s).
Proof. exact (MK_COMB (@lem5282473) (@lem5282472 a s)). Qed.
Lemma lem5282475 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (fun_ext (fun a : real => @lem5282474 a s)). Qed.
Lemma lem5282476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282477 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5282476) (@lem5282475 s)). Qed.
Lemma lem5282478 : term39 = term39.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5282477 s)). Qed.
Lemma lem5282479 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5282480 : term17 = term17.
Proof. exact (MK_COMB (@lem5282479) (@lem5282478)). Qed.
Lemma lem5282481 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5282482 : term16 = term16.
Proof. exact (MK_COMB (@lem5282481) (@lem5282480)). Qed.
Lemma lem5282483 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5282484 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5282483 x)). Qed.
Lemma lem5282485 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282486 : term41 = term41.
Proof. exact (MK_COMB (@lem5282485) (@lem5282484)). Qed.
Lemma lem5282487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5282488 : term18 = term18.
Proof. exact (MK_COMB (@lem5282487) (@lem5282486)). Qed.
Lemma lem5282489 : term20 = term20.
Proof. exact (MK_COMB (@lem5282488) (@lem5282482)). Qed.
Lemma lem5282490 (s : real -> Prop) (a : real) : (term23 s a) = (term23 s a).
Proof. exact (eq_refl (term23 s a)). Qed.
Lemma lem5282491 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5282496 (s : real -> Prop) (b : real) (x : real) : (term24 s b x) = (term24 s b x).
Proof. exact (eq_refl (term24 s b x)). Qed.
Lemma lem5282497 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5282496 s b x)). Qed.
Lemma lem5282498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282499 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5282498) (@lem5282497 s b)). Qed.
Lemma lem5282500 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (fun_ext (fun b : real => @lem5282499 s b)). Qed.
Lemma lem5282501 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282502 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (MK_COMB (@lem5282501) (@lem5282500 s)). Qed.
Lemma lem5282503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282504 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (MK_COMB (@lem5282503) (@lem5282502 s)). Qed.
Lemma lem5282505 (a : real) (s : real -> Prop) : (term45 a s) = (term45 a s).
Proof. exact (MK_COMB (@lem5282504 s) (@lem5282491 a s)). Qed.
Lemma lem5282506 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5282507 (a : real) (s : real -> Prop) : (term46 a s) = (term46 a s).
Proof. exact (MK_COMB (@lem5282506) (@lem5282505 a s)). Qed.
Lemma lem5282508 (s : real -> Prop) (a : real) : (term47 s a) = (term47 s a).
Proof. exact (MK_COMB (@lem5282507 a s) (@lem5282490 s a)). Qed.
Lemma lem5282509 (s : real -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun a : real => @lem5282508 s a)). Qed.
Lemma lem5282510 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282511 (s : real -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem5282510) (@lem5282509 s)). Qed.
Lemma lem5282512 : term50 = term50.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5282511 s)). Qed.
Lemma lem5282513 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5282514 : term8 = term8.
Proof. exact (MK_COMB (@lem5282513) (@lem5282512)). Qed.
Lemma lem5282515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5282516 : term10 = term10.
Proof. exact (MK_COMB (@lem5282515) (@lem5282514)). Qed.
Lemma lem5282517 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5282518 : term21 = term21.
Proof. exact (MK_COMB (@lem5282517) (@lem5282516)). Qed.
Lemma lem5282519 : term22 = term22.
Proof. exact (MK_COMB (@lem5282518) (@lem5282489)). Qed.
Lemma lem5282600 : term11 = term22.
Proof. exact (TRANS (@lem5282448) (@lem5282519)). Qed.
Lemma lem5282601 : term22 = term11.
Proof. exact (SYM (@lem5282600)). Qed.
Lemma lem5282602 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5282603 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem5282604 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5282611 (s : real -> Prop) (b : real) (x : real) : (term24 s b x) = (term51 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5282612 (s : real -> Prop) (b : real) : (term25 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5282611 s b x)). Qed.
Lemma lem5282613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282614 (s : real -> Prop) (b : real) : (term26 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5282613) (@lem5282612 s b)). Qed.
Lemma lem5282615 (s : real -> Prop) : (term42 s) = (term54 s).
Proof. exact (fun_ext (fun b : real => @lem5282614 s b)). Qed.
Lemma lem5282616 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282617 (s : real -> Prop) : (term43 s) = (term55 s).
Proof. exact (MK_COMB (@lem5282616) (@lem5282615 s)). Qed.
Lemma lem5282618 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5282619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282620 (s : real -> Prop) : (term44 s) = (term56 s).
Proof. exact (MK_COMB (@lem5282619) (@lem5282617 s)). Qed.
Lemma lem5282621 (a : real) (s : real -> Prop) : (term45 a s) = (term57 a s).
Proof. exact (MK_COMB (@lem5282620 s) (@lem5282618 a s)). Qed.
Lemma lem5282622 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5282623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282624 (a : real) (s : real -> Prop) : (term59 a s) = (term60 a s).
Proof. exact (MK_COMB (@lem5282623) (@lem5282621 a s)). Qed.
Lemma lem5282625 (s : real -> Prop) (a : real) : (term61 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5282624 a s) (@lem5282622 s a)). Qed.
Lemma lem5282626 (s : real -> Prop) (a : real) : (term63 s a) = (term61 s a).
Proof. exact (@lem17362 (term45 a s) (term23 s a)). Qed.
Lemma lem5282627 (s : real -> Prop) (a : real) : (term63 s a) = (term62 s a).
Proof. exact (TRANS (@lem5282626 s a) (@lem5282625 s a)). Qed.
Lemma lem5282628 (P : real -> Prop) : (term64 P) = (term65 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5282629 (s : real -> Prop) : (term66 s) = (term67 s).
Proof. exact (@lem5282628 (term48 s)). Qed.
Lemma lem5282630 (s : real -> Prop) (a : real) : (term68 s a) = (term47 s a).
Proof. exact (eq_refl (term68 s a)). Qed.
Lemma lem5282631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5282632 (s : real -> Prop) (a : real) : (term69 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5282631) (@lem5282630 s a)). Qed.
Lemma lem5282633 (s : real -> Prop) (a : real) : (term69 s a) = (term62 s a).
Proof. exact (TRANS (@lem5282632 s a) (@lem5282627 s a)). Qed.
Lemma lem5282634 (s : real -> Prop) : (term70 s) = (term71 s).
Proof. exact (fun_ext (fun a : real => @lem5282633 s a)). Qed.
Lemma lem5282635 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282636 (s : real -> Prop) : (term67 s) = (term72 s).
Proof. exact (MK_COMB (@lem5282635) (@lem5282634 s)). Qed.
Lemma lem5282637 (s : real -> Prop) : (term66 s) = (term72 s).
Proof. exact (TRANS (@lem5282629 s) (@lem5282636 s)). Qed.
Lemma lem5282638 (P : type1022) : (term73 P) = (term74 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5282639 : term10 = term75.
Proof. exact (@lem5282638 term50). Qed.
Lemma lem5282640 (s : real -> Prop) : (term76 s) = (term49 s).
Proof. exact (eq_refl (term76 s)). Qed.
Lemma lem5282641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5282642 (s : real -> Prop) : (term77 s) = (term66 s).
Proof. exact (MK_COMB (@lem5282641) (@lem5282640 s)). Qed.
Lemma lem5282643 (s : real -> Prop) : (term77 s) = (term72 s).
Proof. exact (TRANS (@lem5282642 s) (@lem5282637 s)). Qed.
Lemma lem5282644 : term78 = term79.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5282643 s)). Qed.
Lemma lem5282645 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5282646 : term75 = term80.
Proof. exact (MK_COMB (@lem5282645) (@lem5282644)). Qed.
Lemma lem5282647 : term10 = term80.
Proof. exact (TRANS (@lem5282639) (@lem5282646)). Qed.
Lemma lem5282754 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5282755 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem5282754 real P Q). Qed.
Lemma lem5282756 (a : real) (s : real -> Prop) : (term85 a s) = (term86 a s).
Proof. exact (@lem5282755 (term54 s) (@IN real a s)). Qed.
Lemma lem5282757 (s : real -> Prop) (b : real) : (term87 s b) = (term53 s b).
Proof. exact (eq_refl (term87 s b)). Qed.
Lemma lem5282758 (s : real -> Prop) : (term88 s) = (term54 s).
Proof. exact (fun_ext (fun b : real => @lem5282757 s b)). Qed.
Lemma lem5282759 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282760 (s : real -> Prop) : (term89 s) = (term55 s).
Proof. exact (MK_COMB (@lem5282759) (@lem5282758 s)). Qed.
Lemma lem5282761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282762 (s : real -> Prop) : (term90 s) = (term56 s).
Proof. exact (MK_COMB (@lem5282761) (@lem5282760 s)). Qed.
Lemma lem5282763 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5282764 (a : real) (s : real -> Prop) : (term85 a s) = (term57 a s).
Proof. exact (MK_COMB (@lem5282762 s) (@lem5282763 a s)). Qed.
Lemma lem5282765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5282766 (a : real) (s : real -> Prop) : (term91 a s) = (term92 a s).
Proof. exact (MK_COMB (@lem5282765) (@lem5282764 a s)). Qed.
Lemma lem5282767 (s : real -> Prop) (b : real) : (term87 s b) = (term53 s b).
Proof. exact (eq_refl (term87 s b)). Qed.
Lemma lem5282768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282769 (s : real -> Prop) (b : real) : (term93 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5282768) (@lem5282767 s b)). Qed.
Lemma lem5282770 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5282771 (b : real) (a : real) (s : real -> Prop) : (term95 b a s) = (term96 b a s).
Proof. exact (MK_COMB (@lem5282769 s b) (@lem5282770 a s)). Qed.
Lemma lem5282772 (a : real) (s : real -> Prop) : (term97 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5282771 b a s)). Qed.
Lemma lem5282773 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282774 (a : real) (s : real -> Prop) : (term86 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5282773) (@lem5282772 a s)). Qed.
Lemma lem5282775 (a : real) (s : real -> Prop) : ((term85 a s) = (term86 a s)) = ((term57 a s) = (term99 a s)).
Proof. exact (MK_COMB (@lem5282766 a s) (@lem5282774 a s)). Qed.
Lemma lem5282776 (a : real) (s : real -> Prop) : (term57 a s) = (term99 a s).
Proof. exact (EQ_MP (@lem5282775 a s) (@lem5282756 a s)). Qed.
Lemma lem5282777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282778 (a : real) (s : real -> Prop) : (term60 a s) = (term100 a s).
Proof. exact (MK_COMB (@lem5282777) (@lem5282776 a s)). Qed.
Lemma lem5282779 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5282780 (s : real -> Prop) (a : real) : (term62 s a) = (term101 s a).
Proof. exact (MK_COMB (@lem5282778 a s) (@lem5282779 s a)). Qed.
Lemma lem5282782 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5282783 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem5282782 real P Q). Qed.
Lemma lem5282784 (s : real -> Prop) (a : real) : (term102 s a) = (term103 s a).
Proof. exact (@lem5282783 (term98 a s) (term58 s a)). Qed.
Lemma lem5282785 (b : real) (a : real) (s : real -> Prop) : (term104 a s b) = (term96 b a s).
Proof. exact (eq_refl (term104 a s b)). Qed.
Lemma lem5282786 (a : real) (s : real -> Prop) : (term105 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5282785 b a s)). Qed.
Lemma lem5282787 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282788 (a : real) (s : real -> Prop) : (term106 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5282787) (@lem5282786 a s)). Qed.
Lemma lem5282789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282790 (a : real) (s : real -> Prop) : (term107 a s) = (term100 a s).
Proof. exact (MK_COMB (@lem5282789) (@lem5282788 a s)). Qed.
Lemma lem5282791 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5282792 (s : real -> Prop) (a : real) : (term102 s a) = (term101 s a).
Proof. exact (MK_COMB (@lem5282790 a s) (@lem5282791 s a)). Qed.
Lemma lem5282793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5282794 (s : real -> Prop) (a : real) : (term108 s a) = (term109 s a).
Proof. exact (MK_COMB (@lem5282793) (@lem5282792 s a)). Qed.
Lemma lem5282795 (b : real) (a : real) (s : real -> Prop) : (term104 a s b) = (term96 b a s).
Proof. exact (eq_refl (term104 a s b)). Qed.
Lemma lem5282796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5282797 (b : real) (a : real) (s : real -> Prop) : (term110 a s b) = (term111 b a s).
Proof. exact (MK_COMB (@lem5282796) (@lem5282795 b a s)). Qed.
Lemma lem5282798 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5282799 (b : real) (s : real -> Prop) (a : real) : (term112 b s a) = (term113 b s a).
Proof. exact (MK_COMB (@lem5282797 b a s) (@lem5282798 s a)). Qed.
Lemma lem5282800 (s : real -> Prop) (a : real) : (term114 s a) = (term115 s a).
Proof. exact (fun_ext (fun b : real => @lem5282799 b s a)). Qed.
Lemma lem5282801 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282802 (s : real -> Prop) (a : real) : (term103 s a) = (term116 s a).
Proof. exact (MK_COMB (@lem5282801) (@lem5282800 s a)). Qed.
Lemma lem5282803 (s : real -> Prop) (a : real) : ((term102 s a) = (term103 s a)) = ((term101 s a) = (term116 s a)).
Proof. exact (MK_COMB (@lem5282794 s a) (@lem5282802 s a)). Qed.
Lemma lem5282804 (s : real -> Prop) (a : real) : (term101 s a) = (term116 s a).
Proof. exact (EQ_MP (@lem5282803 s a) (@lem5282784 s a)). Qed.
Lemma lem5282805 (s : real -> Prop) (a : real) : (term62 s a) = (term116 s a).
Proof. exact (TRANS (@lem5282780 s a) (@lem5282804 s a)). Qed.
Lemma lem5282806 (s : real -> Prop) : (term71 s) = (term117 s).
Proof. exact (fun_ext (fun a : real => @lem5282805 s a)). Qed.
Lemma lem5282807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282808 (s : real -> Prop) : (term72 s) = (term118 s).
Proof. exact (MK_COMB (@lem5282807) (@lem5282806 s)). Qed.
Lemma lem5282809 : term79 = term119.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5282808 s)). Qed.
Lemma lem5282810 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5282812 : term80 = term120.
Proof. exact (MK_COMB (@lem5282810) (@lem5282809)). Qed.
Lemma lem5282813 : term10 = term120.
Proof. exact (TRANS (@lem5282647) (@lem5282812)). Qed.
Lemma lem5282814 (h1 : term10) : term120.
Proof. exact (EQ_MP (@lem5282813) (@lem5282602 h1)). Qed.
Lemma lem5282815 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5282816 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5282815 x)). Qed.
Lemma lem5282817 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282826 : term41 = term41.
Proof. exact (MK_COMB (@lem5282817) (@lem5282816)). Qed.
Lemma lem5282827 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem5282826) (@lem5282603 h1)). Qed.
Lemma lem5282836 (s : real -> Prop) (a : real) (x : real) : (term121 s a x) = (term122 s a x).
Proof. exact (@lem17362 (@IN real x s) (real_le a x)). Qed.
Lemma lem5282837 (P : real -> Prop) : (term64 P) = (term65 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5282838 (s : real -> Prop) (a : real) : (term123 s a) = (term124 s a).
Proof. exact (@lem5282837 (term25 s a)). Qed.
Lemma lem5282839 (s : real -> Prop) (a : real) (x : real) : (term125 s a x) = (term24 s a x).
Proof. exact (eq_refl (term125 s a x)). Qed.
Lemma lem5282840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5282841 (s : real -> Prop) (a : real) (x : real) : (term126 s a x) = (term121 s a x).
Proof. exact (MK_COMB (@lem5282840) (@lem5282839 s a x)). Qed.
Lemma lem5282842 (s : real -> Prop) (a : real) (x : real) : (term126 s a x) = (term122 s a x).
Proof. exact (TRANS (@lem5282841 s a x) (@lem5282836 s a x)). Qed.
Lemma lem5282843 (s : real -> Prop) (a : real) : (term127 s a) = (term128 s a).
Proof. exact (fun_ext (fun x : real => @lem5282842 s a x)). Qed.
Lemma lem5282844 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5282845 (s : real -> Prop) (a : real) : (term124 s a) = (term129 s a).
Proof. exact (MK_COMB (@lem5282844) (@lem5282843 s a)). Qed.
Lemma lem5282846 (s : real -> Prop) (a : real) : (term123 s a) = (term129 s a).
Proof. exact (TRANS (@lem5282838 s a) (@lem5282845 s a)). Qed.
Lemma lem5282848 (y : real) (b : real) : (term130 y b) = (term130 y b).
Proof. exact (eq_refl (term130 y b)). Qed.
Lemma lem5282849 (y : real) (b : real) (s : real -> Prop) (a : real) : (term131 y b s a) = (term132 y b s a).
Proof. exact (MK_COMB (@lem5282848 y b) (@lem5282846 s a)). Qed.
Lemma lem5282850 (y : real) (b : real) (s : real -> Prop) (a : real) : (term133 y b s a) = (term131 y b s a).
Proof. exact (@lem17045 (real_le y b) (term26 s a)). Qed.
Lemma lem5282851 (y : real) (b : real) (s : real -> Prop) (a : real) : (term133 y b s a) = (term132 y b s a).
Proof. exact (TRANS (@lem5282850 y b s a) (@lem5282849 y b s a)). Qed.
Lemma lem5282853 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5282854 (y : real) (b : real) (s : real -> Prop) (a : real) : (term135 y b s a) = (term136 y b s a).
Proof. exact (MK_COMB (@lem5282853 y s) (@lem5282851 y b s a)). Qed.
Lemma lem5282855 (y : real) (b : real) (s : real -> Prop) (a : real) : (term137 y b s a) = (term135 y b s a).
Proof. exact (@lem17045 (@IN real y s) (term28 y b s a)). Qed.
Lemma lem5282856 (y : real) (b : real) (s : real -> Prop) (a : real) : (term137 y b s a) = (term136 y b s a).
Proof. exact (TRANS (@lem5282855 y b s a) (@lem5282854 y b s a)). Qed.
Lemma lem5282857 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5282858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5282859 (y : real) (b : real) (s : real -> Prop) (a : real) : (term138 y b s a) = (term139 y b s a).
Proof. exact (MK_COMB (@lem5282858) (@lem5282856 y b s a)). Qed.
Lemma lem5282860 (y : real) (a : real) (s : real -> Prop) (b : real) : (term140 y a s b) = (term141 y a s b).
Proof. exact (MK_COMB (@lem5282859 y b s a) (@lem5282857 s b)). Qed.
Lemma lem5282861 (y : real) (a : real) (s : real -> Prop) (b : real) : (term32 y a s b) = (term140 y a s b).
Proof. exact (@lem17265 (term30 y b s a) (term23 s b)). Qed.
Lemma lem5282862 (y : real) (a : real) (s : real -> Prop) (b : real) : (term32 y a s b) = (term141 y a s b).
Proof. exact (TRANS (@lem5282861 y a s b) (@lem5282860 y a s b)). Qed.
Lemma lem5282863 (a : real) (s : real -> Prop) (b : real) : (term33 a s b) = (term142 a s b).
Proof. exact (fun_ext (fun y : real => @lem5282862 y a s b)). Qed.
Lemma lem5282864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282865 (a : real) (s : real -> Prop) (b : real) : (term34 a s b) = (term143 a s b).
Proof. exact (MK_COMB (@lem5282864) (@lem5282863 a s b)). Qed.
Lemma lem5282866 (a : real) (s : real -> Prop) : (term35 a s) = (term144 a s).
Proof. exact (fun_ext (fun b : real => @lem5282865 a s b)). Qed.
Lemma lem5282867 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282868 (a : real) (s : real -> Prop) : (term36 a s) = (term145 a s).
Proof. exact (MK_COMB (@lem5282867) (@lem5282866 a s)). Qed.
Lemma lem5282869 (s : real -> Prop) : (term37 s) = (term146 s).
Proof. exact (fun_ext (fun a : real => @lem5282868 a s)). Qed.
Lemma lem5282870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282871 (s : real -> Prop) : (term38 s) = (term147 s).
Proof. exact (MK_COMB (@lem5282870) (@lem5282869 s)). Qed.
Lemma lem5282872 : term39 = term148.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5282871 s)). Qed.
Lemma lem5282873 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5282874 : term17 = term149.
Proof. exact (MK_COMB (@lem5282873) (@lem5282872)). Qed.
Lemma lem5282908 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5282909 (P : real -> Prop) (Q : Prop) : (term152 P Q) = (term153 P Q).
Proof. exact (@lem5282908 real P Q). Qed.
Lemma lem5282910 (a : real) (s : real -> Prop) (b : real) : (term154 a s b) = (term155 a s b).
Proof. exact (@lem5282909 (term156 b s a) (term23 s b)). Qed.
Lemma lem5282911 (y : real) (b : real) (s : real -> Prop) (a : real) : (term157 b s a y) = (term136 y b s a).
Proof. exact (eq_refl (term157 b s a y)). Qed.
Lemma lem5282912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5282913 (y : real) (b : real) (s : real -> Prop) (a : real) : (term158 b s a y) = (term139 y b s a).
Proof. exact (MK_COMB (@lem5282912) (@lem5282911 y b s a)). Qed.
Lemma lem5282914 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5282915 (y : real) (a : real) (s : real -> Prop) (b : real) : (term159 a y s b) = (term141 y a s b).
Proof. exact (MK_COMB (@lem5282913 y b s a) (@lem5282914 s b)). Qed.
Lemma lem5282916 (a : real) (s : real -> Prop) (b : real) : (term160 a s b) = (term142 a s b).
Proof. exact (fun_ext (fun y : real => @lem5282915 y a s b)). Qed.
Lemma lem5282917 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282918 (a : real) (s : real -> Prop) (b : real) : (term154 a s b) = (term143 a s b).
Proof. exact (MK_COMB (@lem5282917) (@lem5282916 a s b)). Qed.
Lemma lem5282919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5282920 (a : real) (s : real -> Prop) (b : real) : (term161 a s b) = (term162 a s b).
Proof. exact (MK_COMB (@lem5282919) (@lem5282918 a s b)). Qed.
Lemma lem5282921 (y : real) (b : real) (s : real -> Prop) (a : real) : (term157 b s a y) = (term136 y b s a).
Proof. exact (eq_refl (term157 b s a y)). Qed.
Lemma lem5282922 (b : real) (s : real -> Prop) (a : real) : (term163 b s a) = (term156 b s a).
Proof. exact (fun_ext (fun y : real => @lem5282921 y b s a)). Qed.
Lemma lem5282923 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5282924 (b : real) (s : real -> Prop) (a : real) : (term164 b s a) = (term165 b s a).
Proof. exact (MK_COMB (@lem5282923) (@lem5282922 b s a)). Qed.
Lemma lem5282925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5282926 (b : real) (s : real -> Prop) (a : real) : (term166 b s a) = (term167 b s a).
Proof. exact (MK_COMB (@lem5282925) (@lem5282924 b s a)). Qed.
Lemma lem5282927 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5282928 (a : real) (s : real -> Prop) (b : real) : (term155 a s b) = (term168 a s b).
Proof. exact (MK_COMB (@lem5282926 b s a) (@lem5282927 s b)). Qed.
Lemma lem5282929 (a : real) (s : real -> Prop) (b : real) : ((term154 a s b) = (term155 a s b)) = ((term143 a s b) = (term168 a s b)).
Proof. exact (MK_COMB (@lem5282920 a s b) (@lem5282928 a s b)). Qed.
Lemma lem5282930 (a : real) (s : real -> Prop) (b : real) : (term143 a s b) = (term168 a s b).
Proof. exact (EQ_MP (@lem5282929 a s b) (@lem5282910 a s b)). Qed.
Lemma lem5283027 (a : real) (s : real -> Prop) : (term144 a s) = (term169 a s).
Proof. exact (fun_ext (fun b : real => @lem5282930 a s b)). Qed.
Lemma lem5283028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283029 (a : real) (s : real -> Prop) : (term145 a s) = (term170 a s).
Proof. exact (MK_COMB (@lem5283028) (@lem5283027 a s)). Qed.
Lemma lem5283078 (s : real -> Prop) : (term146 s) = (term171 s).
Proof. exact (fun_ext (fun a : real => @lem5283029 a s)). Qed.
Lemma lem5283079 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283080 (s : real -> Prop) : (term147 s) = (term172 s).
Proof. exact (MK_COMB (@lem5283079) (@lem5283078 s)). Qed.
Lemma lem5283085 : term148 = term173.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283080 s)). Qed.
Lemma lem5283086 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283087 : term149 = term174.
Proof. exact (MK_COMB (@lem5283086) (@lem5283085)). Qed.
Lemma lem5283093 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5283094 (P : Prop) (Q : real -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem5283093 real P Q). Qed.
Lemma lem5283095 (y : real) (b : real) (s : real -> Prop) (a : real) : (term179 y b s a) = (term180 y b s a).
Proof. exact (@lem5283094 (term181 y b) (term128 s a)). Qed.
Lemma lem5283096 (s : real -> Prop) (a : real) (x : real) : (term182 s a x) = (term122 s a x).
Proof. exact (eq_refl (term182 s a x)). Qed.
Lemma lem5283097 (s : real -> Prop) (a : real) : (term183 s a) = (term128 s a).
Proof. exact (fun_ext (fun x : real => @lem5283096 s a x)). Qed.
Lemma lem5283098 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5283099 (s : real -> Prop) (a : real) : (term184 s a) = (term129 s a).
Proof. exact (MK_COMB (@lem5283098) (@lem5283097 s a)). Qed.
Lemma lem5283100 (y : real) (b : real) : (term130 y b) = (term130 y b).
Proof. exact (eq_refl (term130 y b)). Qed.
Lemma lem5283101 (y : real) (b : real) (s : real -> Prop) (a : real) : (term179 y b s a) = (term132 y b s a).
Proof. exact (MK_COMB (@lem5283100 y b) (@lem5283099 s a)). Qed.
Lemma lem5283102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283103 (y : real) (b : real) (s : real -> Prop) (a : real) : (term185 y b s a) = (term186 y b s a).
Proof. exact (MK_COMB (@lem5283102) (@lem5283101 y b s a)). Qed.
Lemma lem5283104 (s : real -> Prop) (a : real) (x : real) : (term182 s a x) = (term122 s a x).
Proof. exact (eq_refl (term182 s a x)). Qed.
Lemma lem5283105 (y : real) (b : real) : (term130 y b) = (term130 y b).
Proof. exact (eq_refl (term130 y b)). Qed.
Lemma lem5283106 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term187 y b s a x) = (term188 y b s a x).
Proof. exact (MK_COMB (@lem5283105 y b) (@lem5283104 s a x)). Qed.
Lemma lem5283107 (y : real) (b : real) (s : real -> Prop) (a : real) : (term189 y b s a) = (term190 y b s a).
Proof. exact (fun_ext (fun x : real => @lem5283106 y b s a x)). Qed.
Lemma lem5283108 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5283109 (y : real) (b : real) (s : real -> Prop) (a : real) : (term180 y b s a) = (term191 y b s a).
Proof. exact (MK_COMB (@lem5283108) (@lem5283107 y b s a)). Qed.
Lemma lem5283110 (y : real) (b : real) (s : real -> Prop) (a : real) : ((term179 y b s a) = (term180 y b s a)) = ((term132 y b s a) = (term191 y b s a)).
Proof. exact (MK_COMB (@lem5283103 y b s a) (@lem5283109 y b s a)). Qed.
Lemma lem5283111 (y : real) (b : real) (s : real -> Prop) (a : real) : (term132 y b s a) = (term191 y b s a).
Proof. exact (EQ_MP (@lem5283110 y b s a) (@lem5283095 y b s a)). Qed.
Lemma lem5283112 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5283113 (y : real) (b : real) (s : real -> Prop) (a : real) : (term136 y b s a) = (term192 y b s a).
Proof. exact (MK_COMB (@lem5283112 y s) (@lem5283111 y b s a)). Qed.
Lemma lem5283115 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5283116 (P : Prop) (Q : real -> Prop) : (term177 P Q) = (term178 P Q).
Proof. exact (@lem5283115 real P Q). Qed.
Lemma lem5283117 (y : real) (b : real) (s : real -> Prop) (a : real) : (term193 y b s a) = (term194 y b s a).
Proof. exact (@lem5283116 (term195 y s) (term190 y b s a)). Qed.
Lemma lem5283118 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term196 y b s a x) = (term188 y b s a x).
Proof. exact (eq_refl (term196 y b s a x)). Qed.
Lemma lem5283119 (y : real) (b : real) (s : real -> Prop) (a : real) : (term197 y b s a) = (term190 y b s a).
Proof. exact (fun_ext (fun x : real => @lem5283118 y b s a x)). Qed.
Lemma lem5283120 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5283121 (y : real) (b : real) (s : real -> Prop) (a : real) : (term198 y b s a) = (term191 y b s a).
Proof. exact (MK_COMB (@lem5283120) (@lem5283119 y b s a)). Qed.
Lemma lem5283122 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5283123 (y : real) (b : real) (s : real -> Prop) (a : real) : (term193 y b s a) = (term192 y b s a).
Proof. exact (MK_COMB (@lem5283122 y s) (@lem5283121 y b s a)). Qed.
Lemma lem5283124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283125 (y : real) (b : real) (s : real -> Prop) (a : real) : (term199 y b s a) = (term200 y b s a).
Proof. exact (MK_COMB (@lem5283124) (@lem5283123 y b s a)). Qed.
Lemma lem5283126 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term196 y b s a x) = (term188 y b s a x).
Proof. exact (eq_refl (term196 y b s a x)). Qed.
Lemma lem5283127 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5283128 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term201 y b s a x) = (term202 y b s a x).
Proof. exact (MK_COMB (@lem5283127 y s) (@lem5283126 y b s a x)). Qed.
Lemma lem5283129 (y : real) (b : real) (s : real -> Prop) (a : real) : (term203 y b s a) = (term204 y b s a).
Proof. exact (fun_ext (fun x : real => @lem5283128 y b s a x)). Qed.
Lemma lem5283130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5283131 (y : real) (b : real) (s : real -> Prop) (a : real) : (term194 y b s a) = (term205 y b s a).
Proof. exact (MK_COMB (@lem5283130) (@lem5283129 y b s a)). Qed.
Lemma lem5283132 (y : real) (b : real) (s : real -> Prop) (a : real) : ((term193 y b s a) = (term194 y b s a)) = ((term192 y b s a) = (term205 y b s a)).
Proof. exact (MK_COMB (@lem5283125 y b s a) (@lem5283131 y b s a)). Qed.
Lemma lem5283133 (y : real) (b : real) (s : real -> Prop) (a : real) : (term192 y b s a) = (term205 y b s a).
Proof. exact (EQ_MP (@lem5283132 y b s a) (@lem5283117 y b s a)). Qed.
Lemma lem5283134 (y : real) (b : real) (s : real -> Prop) (a : real) : (term136 y b s a) = (term205 y b s a).
Proof. exact (TRANS (@lem5283113 y b s a) (@lem5283133 y b s a)). Qed.
Lemma lem5283135 (b : real) (s : real -> Prop) (a : real) : (term156 b s a) = (term206 b s a).
Proof. exact (fun_ext (fun y : real => @lem5283134 y b s a)). Qed.
Lemma lem5283136 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283137 (b : real) (s : real -> Prop) (a : real) : (term165 b s a) = (term207 b s a).
Proof. exact (MK_COMB (@lem5283136) (@lem5283135 b s a)). Qed.
Lemma lem5283139 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5283140 (P : type1626) : (term210 P) = (term211 P).
Proof. exact (@lem5283139 real real P). Qed.
Lemma lem5283141 (b : real) (s : real -> Prop) (a : real) : (term212 b s a) = (term213 b s a).
Proof. exact (@lem5283140 (term214 b s a)). Qed.
Lemma lem5283142 (y : real) (b : real) (s : real -> Prop) (a : real) : (term215 b s a y) = (term204 y b s a).
Proof. exact (eq_refl (term215 b s a y)). Qed.
Lemma lem5283143 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5283144 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term216 b s a y x) = (term217 y b s a x).
Proof. exact (MK_COMB (@lem5283142 y b s a) (@lem5283143 x)). Qed.
Lemma lem5283145 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term217 y b s a x) = (term202 y b s a x).
Proof. exact (eq_refl (term217 y b s a x)). Qed.
Lemma lem5283146 (y : real) (b : real) (s : real -> Prop) (a : real) (x : real) : (term216 b s a y x) = (term202 y b s a x).
Proof. exact (TRANS (@lem5283144 y b s a x) (@lem5283145 y b s a x)). Qed.
Lemma lem5283147 (y : real) (b : real) (s : real -> Prop) (a : real) : (term218 b s a y) = (term204 y b s a).
Proof. exact (fun_ext (fun x : real => @lem5283146 y b s a x)). Qed.
Lemma lem5283148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5283149 (y : real) (b : real) (s : real -> Prop) (a : real) : (term219 b s a y) = (term205 y b s a).
Proof. exact (MK_COMB (@lem5283148) (@lem5283147 y b s a)). Qed.
Lemma lem5283150 (b : real) (s : real -> Prop) (a : real) : (term220 b s a) = (term206 b s a).
Proof. exact (fun_ext (fun y : real => @lem5283149 y b s a)). Qed.
Lemma lem5283151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283152 (b : real) (s : real -> Prop) (a : real) : (term212 b s a) = (term207 b s a).
Proof. exact (MK_COMB (@lem5283151) (@lem5283150 b s a)). Qed.
Lemma lem5283153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283154 (b : real) (s : real -> Prop) (a : real) : (term221 b s a) = (term222 b s a).
Proof. exact (MK_COMB (@lem5283153) (@lem5283152 b s a)). Qed.
Lemma lem5283155 (y : real) (b : real) (s : real -> Prop) (a : real) : (term215 b s a y) = (term204 y b s a).
Proof. exact (eq_refl (term215 b s a y)). Qed.
Lemma lem5283156 (x : real -> real) (y : real) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5283157 (b : real) (s : real -> Prop) (a : real) (x : real -> real) (y : real) : (term223 b s a x y) = (term224 b s a x y).
Proof. exact (MK_COMB (@lem5283155 y b s a) (@lem5283156 x y)). Qed.
Lemma lem5283158 (b : real) (s : real -> Prop) (a : real) (x : real -> real) (y : real) : (term224 b s a x y) = (term225 b s a x y).
Proof. exact (eq_refl (term224 b s a x y)). Qed.
Lemma lem5283159 (b : real) (s : real -> Prop) (a : real) (x : real -> real) (y : real) : (term223 b s a x y) = (term225 b s a x y).
Proof. exact (TRANS (@lem5283157 b s a x y) (@lem5283158 b s a x y)). Qed.
Lemma lem5283160 (b : real) (s : real -> Prop) (a : real) (x : real -> real) : (term226 b s a x) = (term227 b s a x).
Proof. exact (fun_ext (fun y : real => @lem5283159 b s a x y)). Qed.
Lemma lem5283161 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283162 (b : real) (s : real -> Prop) (a : real) (x : real -> real) : (term228 b s a x) = (term229 b s a x).
Proof. exact (MK_COMB (@lem5283161) (@lem5283160 b s a x)). Qed.
Lemma lem5283163 (b : real) (s : real -> Prop) (a : real) : (term230 b s a) = (term231 b s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5283162 b s a x)). Qed.
Lemma lem5283164 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5283165 (b : real) (s : real -> Prop) (a : real) : (term213 b s a) = (term232 b s a).
Proof. exact (MK_COMB (@lem5283164) (@lem5283163 b s a)). Qed.
Lemma lem5283166 (b : real) (s : real -> Prop) (a : real) : ((term212 b s a) = (term213 b s a)) = ((term207 b s a) = (term232 b s a)).
Proof. exact (MK_COMB (@lem5283154 b s a) (@lem5283165 b s a)). Qed.
Lemma lem5283167 (b : real) (s : real -> Prop) (a : real) : (term207 b s a) = (term232 b s a).
Proof. exact (EQ_MP (@lem5283166 b s a) (@lem5283141 b s a)). Qed.
Lemma lem5283168 (b : real) (s : real -> Prop) (a : real) : (term165 b s a) = (term232 b s a).
Proof. exact (TRANS (@lem5283137 b s a) (@lem5283167 b s a)). Qed.
Lemma lem5283169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283170 (b : real) (s : real -> Prop) (a : real) : (term167 b s a) = (term233 b s a).
Proof. exact (MK_COMB (@lem5283169) (@lem5283168 b s a)). Qed.
Lemma lem5283171 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283172 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term234 a s b).
Proof. exact (MK_COMB (@lem5283170 b s a) (@lem5283171 s b)). Qed.
Lemma lem5283174 {A : Type'} (P : A -> Prop) (Q : Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5283175 (P : type1028) (Q : Prop) : (term237 P Q) = (term238 P Q).
Proof. exact (@lem5283174 (real -> real) P Q). Qed.
Lemma lem5283176 (a : real) (s : real -> Prop) (b : real) : (term239 a s b) = (term240 a s b).
Proof. exact (@lem5283175 (term231 b s a) (term23 s b)). Qed.
Lemma lem5283177 (b : real) (s : real -> Prop) (a : real) (x : real -> real) : (term241 b s a x) = (term229 b s a x).
Proof. exact (eq_refl (term241 b s a x)). Qed.
Lemma lem5283178 (b : real) (s : real -> Prop) (a : real) : (term242 b s a) = (term231 b s a).
Proof. exact (fun_ext (fun x : real -> real => @lem5283177 b s a x)). Qed.
Lemma lem5283179 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5283180 (b : real) (s : real -> Prop) (a : real) : (term243 b s a) = (term232 b s a).
Proof. exact (MK_COMB (@lem5283179) (@lem5283178 b s a)). Qed.
Lemma lem5283181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283182 (b : real) (s : real -> Prop) (a : real) : (term244 b s a) = (term233 b s a).
Proof. exact (MK_COMB (@lem5283181) (@lem5283180 b s a)). Qed.
Lemma lem5283183 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283184 (a : real) (s : real -> Prop) (b : real) : (term239 a s b) = (term234 a s b).
Proof. exact (MK_COMB (@lem5283182 b s a) (@lem5283183 s b)). Qed.
Lemma lem5283185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283186 (a : real) (s : real -> Prop) (b : real) : (term245 a s b) = (term246 a s b).
Proof. exact (MK_COMB (@lem5283185) (@lem5283184 a s b)). Qed.
Lemma lem5283187 (b : real) (s : real -> Prop) (a : real) (x : real -> real) : (term241 b s a x) = (term229 b s a x).
Proof. exact (eq_refl (term241 b s a x)). Qed.
Lemma lem5283188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283189 (b : real) (s : real -> Prop) (a : real) (x : real -> real) : (term247 b s a x) = (term248 b s a x).
Proof. exact (MK_COMB (@lem5283188) (@lem5283187 b s a x)). Qed.
Lemma lem5283190 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283191 (a : real) (x : real -> real) (s : real -> Prop) (b : real) : (term249 a x s b) = (term250 a x s b).
Proof. exact (MK_COMB (@lem5283189 b s a x) (@lem5283190 s b)). Qed.
Lemma lem5283192 (a : real) (s : real -> Prop) (b : real) : (term251 a s b) = (term252 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5283191 a x s b)). Qed.
Lemma lem5283193 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5283194 (a : real) (s : real -> Prop) (b : real) : (term240 a s b) = (term253 a s b).
Proof. exact (MK_COMB (@lem5283193) (@lem5283192 a s b)). Qed.
Lemma lem5283195 (a : real) (s : real -> Prop) (b : real) : ((term239 a s b) = (term240 a s b)) = ((term234 a s b) = (term253 a s b)).
Proof. exact (MK_COMB (@lem5283186 a s b) (@lem5283194 a s b)). Qed.
Lemma lem5283196 (a : real) (s : real -> Prop) (b : real) : (term234 a s b) = (term253 a s b).
Proof. exact (EQ_MP (@lem5283195 a s b) (@lem5283176 a s b)). Qed.
Lemma lem5283197 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term253 a s b).
Proof. exact (TRANS (@lem5283172 a s b) (@lem5283196 a s b)). Qed.
Lemma lem5283198 (a : real) (s : real -> Prop) : (term169 a s) = (term254 a s).
Proof. exact (fun_ext (fun b : real => @lem5283197 a s b)). Qed.
Lemma lem5283199 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283200 (a : real) (s : real -> Prop) : (term170 a s) = (term255 a s).
Proof. exact (MK_COMB (@lem5283199) (@lem5283198 a s)). Qed.
Lemma lem5283202 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5283203 (P : type1618) : (term256 P) = (term257 P).
Proof. exact (@lem5283202 real (real -> real) P). Qed.
Lemma lem5283204 (a : real) (s : real -> Prop) : (term258 a s) = (term259 a s).
Proof. exact (@lem5283203 (term260 a s)). Qed.
Lemma lem5283205 (a : real) (s : real -> Prop) (b : real) : (term261 a s b) = (term252 a s b).
Proof. exact (eq_refl (term261 a s b)). Qed.
Lemma lem5283206 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5283207 (a : real) (s : real -> Prop) (b : real) (x : real -> real) : (term262 a s b x) = (term263 a s b x).
Proof. exact (MK_COMB (@lem5283205 a s b) (@lem5283206 x)). Qed.
Lemma lem5283208 (a : real) (x : real -> real) (s : real -> Prop) (b : real) : (term263 a s b x) = (term250 a x s b).
Proof. exact (eq_refl (term263 a s b x)). Qed.
Lemma lem5283209 (a : real) (x : real -> real) (s : real -> Prop) (b : real) : (term262 a s b x) = (term250 a x s b).
Proof. exact (TRANS (@lem5283207 a s b x) (@lem5283208 a x s b)). Qed.
Lemma lem5283210 (a : real) (s : real -> Prop) (b : real) : (term264 a s b) = (term252 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5283209 a x s b)). Qed.
Lemma lem5283211 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5283212 (a : real) (s : real -> Prop) (b : real) : (term265 a s b) = (term253 a s b).
Proof. exact (MK_COMB (@lem5283211) (@lem5283210 a s b)). Qed.
Lemma lem5283213 (a : real) (s : real -> Prop) : (term266 a s) = (term254 a s).
Proof. exact (fun_ext (fun b : real => @lem5283212 a s b)). Qed.
Lemma lem5283214 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283215 (a : real) (s : real -> Prop) : (term258 a s) = (term255 a s).
Proof. exact (MK_COMB (@lem5283214) (@lem5283213 a s)). Qed.
Lemma lem5283216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283217 (a : real) (s : real -> Prop) : (term267 a s) = (term268 a s).
Proof. exact (MK_COMB (@lem5283216) (@lem5283215 a s)). Qed.
Lemma lem5283218 (a : real) (s : real -> Prop) (b : real) : (term261 a s b) = (term252 a s b).
Proof. exact (eq_refl (term261 a s b)). Qed.
Lemma lem5283219 (x : type1627) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5283220 (a : real) (s : real -> Prop) (x : type1627) (b : real) : (term269 a s x b) = (term270 a s x b).
Proof. exact (MK_COMB (@lem5283218 a s b) (@lem5283219 x b)). Qed.
Lemma lem5283221 (a : real) (x : type1627) (s : real -> Prop) (b : real) : (term270 a s x b) = (term271 a x s b).
Proof. exact (eq_refl (term270 a s x b)). Qed.
Lemma lem5283222 (a : real) (x : type1627) (s : real -> Prop) (b : real) : (term269 a s x b) = (term271 a x s b).
Proof. exact (TRANS (@lem5283220 a s x b) (@lem5283221 a x s b)). Qed.
Lemma lem5283223 (a : real) (x : type1627) (s : real -> Prop) : (term272 a s x) = (term273 a x s).
Proof. exact (fun_ext (fun b : real => @lem5283222 a x s b)). Qed.
Lemma lem5283224 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283225 (a : real) (x : type1627) (s : real -> Prop) : (term274 a s x) = (term275 a x s).
Proof. exact (MK_COMB (@lem5283224) (@lem5283223 a x s)). Qed.
Lemma lem5283226 (a : real) (s : real -> Prop) : (term276 a s) = (term277 a s).
Proof. exact (fun_ext (fun x : type1627 => @lem5283225 a x s)). Qed.
Lemma lem5283227 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5283228 (a : real) (s : real -> Prop) : (term259 a s) = (term278 a s).
Proof. exact (MK_COMB (@lem5283227) (@lem5283226 a s)). Qed.
Lemma lem5283229 (a : real) (s : real -> Prop) : ((term258 a s) = (term259 a s)) = ((term255 a s) = (term278 a s)).
Proof. exact (MK_COMB (@lem5283217 a s) (@lem5283228 a s)). Qed.
Lemma lem5283230 (a : real) (s : real -> Prop) : (term255 a s) = (term278 a s).
Proof. exact (EQ_MP (@lem5283229 a s) (@lem5283204 a s)). Qed.
Lemma lem5283231 (a : real) (s : real -> Prop) : (term170 a s) = (term278 a s).
Proof. exact (TRANS (@lem5283200 a s) (@lem5283230 a s)). Qed.
Lemma lem5283232 (s : real -> Prop) : (term171 s) = (term279 s).
Proof. exact (fun_ext (fun a : real => @lem5283231 a s)). Qed.
Lemma lem5283233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283234 (s : real -> Prop) : (term172 s) = (term280 s).
Proof. exact (MK_COMB (@lem5283233) (@lem5283232 s)). Qed.
Lemma lem5283236 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5283237 (P : type1617) : (term281 P) = (term282 P).
Proof. exact (@lem5283236 real type1627 P). Qed.
Lemma lem5283238 (s : real -> Prop) : (term283 s) = (term284 s).
Proof. exact (@lem5283237 (term285 s)). Qed.
Lemma lem5283239 (a : real) (s : real -> Prop) : (term286 s a) = (term277 a s).
Proof. exact (eq_refl (term286 s a)). Qed.
Lemma lem5283240 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5283241 (a : real) (s : real -> Prop) (x : type1627) : (term287 s a x) = (term288 a s x).
Proof. exact (MK_COMB (@lem5283239 a s) (@lem5283240 x)). Qed.
Lemma lem5283242 (a : real) (x : type1627) (s : real -> Prop) : (term288 a s x) = (term275 a x s).
Proof. exact (eq_refl (term288 a s x)). Qed.
Lemma lem5283243 (a : real) (x : type1627) (s : real -> Prop) : (term287 s a x) = (term275 a x s).
Proof. exact (TRANS (@lem5283241 a s x) (@lem5283242 a x s)). Qed.
Lemma lem5283244 (a : real) (s : real -> Prop) : (term289 s a) = (term277 a s).
Proof. exact (fun_ext (fun x : type1627 => @lem5283243 a x s)). Qed.
Lemma lem5283245 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5283246 (a : real) (s : real -> Prop) : (term290 s a) = (term278 a s).
Proof. exact (MK_COMB (@lem5283245) (@lem5283244 a s)). Qed.
Lemma lem5283247 (s : real -> Prop) : (term291 s) = (term279 s).
Proof. exact (fun_ext (fun a : real => @lem5283246 a s)). Qed.
Lemma lem5283248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283249 (s : real -> Prop) : (term283 s) = (term280 s).
Proof. exact (MK_COMB (@lem5283248) (@lem5283247 s)). Qed.
Lemma lem5283250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283251 (s : real -> Prop) : (term292 s) = (term293 s).
Proof. exact (MK_COMB (@lem5283250) (@lem5283249 s)). Qed.
Lemma lem5283252 (a : real) (s : real -> Prop) : (term286 s a) = (term277 a s).
Proof. exact (eq_refl (term286 s a)). Qed.
Lemma lem5283253 (x : type1625) (a : real) : (x a) = (x a).
Proof. exact (eq_refl (x a)). Qed.
Lemma lem5283254 (s : real -> Prop) (x : type1625) (a : real) : (term294 s x a) = (term295 s x a).
Proof. exact (MK_COMB (@lem5283252 a s) (@lem5283253 x a)). Qed.
Lemma lem5283255 (x : type1625) (a : real) (s : real -> Prop) : (term295 s x a) = (term296 x a s).
Proof. exact (eq_refl (term295 s x a)). Qed.
Lemma lem5283256 (x : type1625) (a : real) (s : real -> Prop) : (term294 s x a) = (term296 x a s).
Proof. exact (TRANS (@lem5283254 s x a) (@lem5283255 x a s)). Qed.
Lemma lem5283257 (x : type1625) (s : real -> Prop) : (term297 s x) = (term298 x s).
Proof. exact (fun_ext (fun a : real => @lem5283256 x a s)). Qed.
Lemma lem5283258 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283259 (x : type1625) (s : real -> Prop) : (term299 s x) = (term300 x s).
Proof. exact (MK_COMB (@lem5283258) (@lem5283257 x s)). Qed.
Lemma lem5283260 (s : real -> Prop) : (term301 s) = (term302 s).
Proof. exact (fun_ext (fun x : type1625 => @lem5283259 x s)). Qed.
Lemma lem5283261 : (@ex (real -> real -> real -> real)) = (@ex (real -> real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real -> real))). Qed.
Lemma lem5283262 (s : real -> Prop) : (term284 s) = (term303 s).
Proof. exact (MK_COMB (@lem5283261) (@lem5283260 s)). Qed.
Lemma lem5283263 (s : real -> Prop) : ((term283 s) = (term284 s)) = ((term280 s) = (term303 s)).
Proof. exact (MK_COMB (@lem5283251 s) (@lem5283262 s)). Qed.
Lemma lem5283264 (s : real -> Prop) : (term280 s) = (term303 s).
Proof. exact (EQ_MP (@lem5283263 s) (@lem5283238 s)). Qed.
Lemma lem5283265 (s : real -> Prop) : (term172 s) = (term303 s).
Proof. exact (TRANS (@lem5283234 s) (@lem5283264 s)). Qed.
Lemma lem5283266 : term173 = term304.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283265 s)). Qed.
Lemma lem5283267 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283268 : term174 = term305.
Proof. exact (MK_COMB (@lem5283267) (@lem5283266)). Qed.
Lemma lem5283270 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5283271 (P : type1015) : (term306 P) = (term307 P).
Proof. exact (@lem5283270 (real -> Prop) type1625 P). Qed.
Lemma lem5283272 : term308 = term309.
Proof. exact (@lem5283271 term310). Qed.
Lemma lem5283273 (s : real -> Prop) : (term311 s) = (term302 s).
Proof. exact (eq_refl (term311 s)). Qed.
Lemma lem5283274 (x : type1625) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5283275 (s : real -> Prop) (x : type1625) : (term312 s x) = (term313 s x).
Proof. exact (MK_COMB (@lem5283273 s) (@lem5283274 x)). Qed.
Lemma lem5283276 (x : type1625) (s : real -> Prop) : (term313 s x) = (term300 x s).
Proof. exact (eq_refl (term313 s x)). Qed.
Lemma lem5283277 (x : type1625) (s : real -> Prop) : (term312 s x) = (term300 x s).
Proof. exact (TRANS (@lem5283275 s x) (@lem5283276 x s)). Qed.
Lemma lem5283278 (s : real -> Prop) : (term314 s) = (term302 s).
Proof. exact (fun_ext (fun x : type1625 => @lem5283277 x s)). Qed.
Lemma lem5283279 : (@ex (real -> real -> real -> real)) = (@ex (real -> real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real -> real))). Qed.
Lemma lem5283280 (s : real -> Prop) : (term315 s) = (term303 s).
Proof. exact (MK_COMB (@lem5283279) (@lem5283278 s)). Qed.
Lemma lem5283281 : term316 = term304.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283280 s)). Qed.
Lemma lem5283282 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283283 : term308 = term305.
Proof. exact (MK_COMB (@lem5283282) (@lem5283281)). Qed.
Lemma lem5283284 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283285 : term317 = term318.
Proof. exact (MK_COMB (@lem5283284) (@lem5283283)). Qed.
Lemma lem5283286 (s : real -> Prop) : (term311 s) = (term302 s).
Proof. exact (eq_refl (term311 s)). Qed.
Lemma lem5283287 (x : type1018) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5283288 (x : type1018) (s : real -> Prop) : (term319 x s) = (term320 x s).
Proof. exact (MK_COMB (@lem5283286 s) (@lem5283287 x s)). Qed.
Lemma lem5283289 (x : type1018) (s : real -> Prop) : (term320 x s) = (term321 x s).
Proof. exact (eq_refl (term320 x s)). Qed.
Lemma lem5283290 (x : type1018) (s : real -> Prop) : (term319 x s) = (term321 x s).
Proof. exact (TRANS (@lem5283288 x s) (@lem5283289 x s)). Qed.
Lemma lem5283291 (x : type1018) : (term322 x) = (term323 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283290 x s)). Qed.
Lemma lem5283292 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283293 (x : type1018) : (term324 x) = (term325 x).
Proof. exact (MK_COMB (@lem5283292) (@lem5283291 x)). Qed.
Lemma lem5283294 : term326 = term327.
Proof. exact (fun_ext (fun x : type1018 => @lem5283293 x)). Qed.
Lemma lem5283295 : (@ex ((real -> Prop) -> real -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real -> real))). Qed.
Lemma lem5283296 : term309 = term328.
Proof. exact (MK_COMB (@lem5283295) (@lem5283294)). Qed.
Lemma lem5283297 : (term308 = term309) = (term305 = term328).
Proof. exact (MK_COMB (@lem5283285) (@lem5283296)). Qed.
Lemma lem5283298 : term305 = term328.
Proof. exact (EQ_MP (@lem5283297) (@lem5283272)). Qed.
Lemma lem5283299 : term174 = term328.
Proof. exact (TRANS (@lem5283268) (@lem5283298)). Qed.
Lemma lem5283300 : term149 = term328.
Proof. exact (TRANS (@lem5283087) (@lem5283299)). Qed.
Lemma lem5283301 : term17 = term328.
Proof. exact (TRANS (@lem5282874) (@lem5283300)). Qed.
Lemma lem5283302 (h1 : term17) : term328.
Proof. exact (EQ_MP (@lem5283301) (@lem5282604 h1)). Qed.
Lemma lem5283303 (x : type1018) (h1 : term325 x) : term325 x.
Proof. exact (h1). Qed.
Lemma lem5283304 (s : real -> Prop) (h1 : term118 s) : term118 s.
Proof. exact (h1). Qed.
Lemma lem5283305 (s : real -> Prop) (a : real) (h1 : term116 s a) : term116 s a.
Proof. exact (h1). Qed.
Lemma lem5283306 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term113 b s a.
Proof. exact (h1). Qed.
Lemma lem5283311 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5283312 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5283311 x)). Qed.
Lemma lem5283313 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283314 : term41 = term41.
Proof. exact (MK_COMB (@lem5283313) (@lem5283312)). Qed.
Lemma lem5283315 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem5283314) (@lem5282827 h1)). Qed.
Lemma lem5283322 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283373 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term329 x s a b y) = (term329 x s a b y).
Proof. exact (eq_refl (term329 x s a b y)). Qed.
Lemma lem5283374 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term330 x s a b) = (term330 x s a b).
Proof. exact (fun_ext (fun y : real => @lem5283373 x s a b y)). Qed.
Lemma lem5283375 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283376 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term331 x s a b) = (term331 x s a b).
Proof. exact (MK_COMB (@lem5283375) (@lem5283374 x s a b)). Qed.
Lemma lem5283377 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283378 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term332 x s a b) = (term332 x s a b).
Proof. exact (MK_COMB (@lem5283377) (@lem5283376 x s a b)). Qed.
Lemma lem5283379 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term333 x a s b) = (term333 x a s b).
Proof. exact (MK_COMB (@lem5283378 x s a b) (@lem5283322 s b)). Qed.
Lemma lem5283380 (x : type1018) (a : real) (s : real -> Prop) : (term334 x a s) = (term334 x a s).
Proof. exact (fun_ext (fun b : real => @lem5283379 x a s b)). Qed.
Lemma lem5283381 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283382 (x : type1018) (a : real) (s : real -> Prop) : (term335 x a s) = (term335 x a s).
Proof. exact (MK_COMB (@lem5283381) (@lem5283380 x a s)). Qed.
Lemma lem5283383 (x : type1018) (s : real -> Prop) : (term336 x s) = (term336 x s).
Proof. exact (fun_ext (fun a : real => @lem5283382 x a s)). Qed.
Lemma lem5283384 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283385 (x : type1018) (s : real -> Prop) : (term321 x s) = (term321 x s).
Proof. exact (MK_COMB (@lem5283384) (@lem5283383 x s)). Qed.
Lemma lem5283386 (x : type1018) : (term323 x) = (term323 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283385 x s)). Qed.
Lemma lem5283387 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283388 (x : type1018) : (term325 x) = (term325 x).
Proof. exact (MK_COMB (@lem5283387) (@lem5283386 x)). Qed.
Lemma lem5283389 (x : type1018) (h1 : term325 x) : term325 x.
Proof. exact (EQ_MP (@lem5283388 x) (@lem5283303 x h1)). Qed.
Lemma lem5283398 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5283403 (a : real) (s : real -> Prop) : (@IN real a s) = (@IN real a s).
Proof. exact (eq_refl (@IN real a s)). Qed.
Lemma lem5283418 (s : real -> Prop) (b : real) (x : real) : (term51 s b x) = (term51 s b x).
Proof. exact (eq_refl (term51 s b x)). Qed.
Lemma lem5283419 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5283418 s b x)). Qed.
Lemma lem5283420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283421 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5283420) (@lem5283419 s b)). Qed.
Lemma lem5283422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5283423 (s : real -> Prop) (b : real) : (term94 s b) = (term94 s b).
Proof. exact (MK_COMB (@lem5283422) (@lem5283421 s b)). Qed.
Lemma lem5283424 (b : real) (a : real) (s : real -> Prop) : (term96 b a s) = (term96 b a s).
Proof. exact (MK_COMB (@lem5283423 s b) (@lem5283403 a s)). Qed.
Lemma lem5283425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5283426 (b : real) (a : real) (s : real -> Prop) : (term111 b a s) = (term111 b a s).
Proof. exact (MK_COMB (@lem5283425) (@lem5283424 b a s)). Qed.
Lemma lem5283427 (b : real) (s : real -> Prop) (a : real) : (term113 b s a) = (term113 b s a).
Proof. exact (MK_COMB (@lem5283426 b a s) (@lem5283398 s a)). Qed.
Lemma lem5283428 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term113 b s a.
Proof. exact (EQ_MP (@lem5283427 b s a) (@lem5283306 b s a h1)). Qed.
Lemma lem5283430 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term96 b a s.
Proof. exact (proj1 (@lem5283428 b s a h1)). Qed.
Lemma lem5283432 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term53 s b.
Proof. exact (proj1 (@lem5283430 b s a h1)). Qed.
Lemma lem5283434 (x : real) : (real_le x x) = (real_le x x).
Proof. exact (eq_refl (real_le x x)). Qed.
Lemma lem5283435 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5283434 x)). Qed.
Lemma lem5283436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283438 : term41 = term41.
Proof. exact (MK_COMB (@lem5283436) (@lem5283435)). Qed.
Lemma lem5283439 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem5283438) (@lem5283315 h1)). Qed.
Lemma lem5283441 {A : Type'} (P : A -> Prop) (Q : Prop) : (term151 A P Q) = (term150 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5283442 (P : real -> Prop) (Q : Prop) : (term153 P Q) = (term152 P Q).
Proof. exact (@lem5283441 real P Q). Qed.
Lemma lem5283443 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term337 x a s b) = (term338 x a s b).
Proof. exact (@lem5283442 (term330 x s a b) (term23 s b)). Qed.
Lemma lem5283444 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term339 x s a b y) = (term329 x s a b y).
Proof. exact (eq_refl (term339 x s a b y)). Qed.
Lemma lem5283445 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term340 x s a b) = (term330 x s a b).
Proof. exact (fun_ext (fun y : real => @lem5283444 x s a b y)). Qed.
Lemma lem5283446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283447 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term341 x s a b) = (term331 x s a b).
Proof. exact (MK_COMB (@lem5283446) (@lem5283445 x s a b)). Qed.
Lemma lem5283448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283449 (x : type1018) (s : real -> Prop) (a : real) (b : real) : (term342 x s a b) = (term332 x s a b).
Proof. exact (MK_COMB (@lem5283448) (@lem5283447 x s a b)). Qed.
Lemma lem5283450 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283451 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term337 x a s b) = (term333 x a s b).
Proof. exact (MK_COMB (@lem5283449 x s a b) (@lem5283450 s b)). Qed.
Lemma lem5283452 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283453 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term343 x a s b) = (term344 x a s b).
Proof. exact (MK_COMB (@lem5283452) (@lem5283451 x a s b)). Qed.
Lemma lem5283454 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term339 x s a b y) = (term329 x s a b y).
Proof. exact (eq_refl (term339 x s a b y)). Qed.
Lemma lem5283455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283456 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term345 x s a b y) = (term346 x s a b y).
Proof. exact (MK_COMB (@lem5283455) (@lem5283454 x s a b y)). Qed.
Lemma lem5283457 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283458 (x : type1018) (a : real) (y : real) (s : real -> Prop) (b : real) : (term347 x a y s b) = (term348 x a y s b).
Proof. exact (MK_COMB (@lem5283456 x s a b y) (@lem5283457 s b)). Qed.
Lemma lem5283459 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term349 x a s b) = (term350 x a s b).
Proof. exact (fun_ext (fun y : real => @lem5283458 x a y s b)). Qed.
Lemma lem5283460 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283461 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term338 x a s b) = (term351 x a s b).
Proof. exact (MK_COMB (@lem5283460) (@lem5283459 x a s b)). Qed.
Lemma lem5283462 (x : type1018) (a : real) (s : real -> Prop) (b : real) : ((term337 x a s b) = (term338 x a s b)) = ((term333 x a s b) = (term351 x a s b)).
Proof. exact (MK_COMB (@lem5283453 x a s b) (@lem5283461 x a s b)). Qed.
Lemma lem5283463 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term333 x a s b) = (term351 x a s b).
Proof. exact (EQ_MP (@lem5283462 x a s b) (@lem5283443 x a s b)). Qed.
Lemma lem5283464 (x : type1018) (a : real) (s : real -> Prop) : (term334 x a s) = (term352 x a s).
Proof. exact (fun_ext (fun b : real => @lem5283463 x a s b)). Qed.
Lemma lem5283465 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283466 (x : type1018) (a : real) (s : real -> Prop) : (term335 x a s) = (term353 x a s).
Proof. exact (MK_COMB (@lem5283465) (@lem5283464 x a s)). Qed.
Lemma lem5283467 (x : type1018) (s : real -> Prop) : (term336 x s) = (term354 x s).
Proof. exact (fun_ext (fun a : real => @lem5283466 x a s)). Qed.
Lemma lem5283468 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283469 (x : type1018) (s : real -> Prop) : (term321 x s) = (term355 x s).
Proof. exact (MK_COMB (@lem5283468) (@lem5283467 x s)). Qed.
Lemma lem5283470 (x : type1018) : (term323 x) = (term356 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283469 x s)). Qed.
Lemma lem5283471 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283472 (x : type1018) : (term325 x) = (term357 x).
Proof. exact (MK_COMB (@lem5283471) (@lem5283470 x)). Qed.
Lemma lem5283473 (s : real -> Prop) (b : real) : (term23 s b) = (term23 s b).
Proof. exact (eq_refl (term23 s b)). Qed.
Lemma lem5283490 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term358 x s a b y) = (term359 x s a b y).
Proof. exact (@lem19490 (term360 x a b y s) (term181 y b) (term361 x s a b y)). Qed.
Lemma lem5283493 (y : real) (s : real -> Prop) : (term134 y s) = (term134 y s).
Proof. exact (eq_refl (term134 y s)). Qed.
Lemma lem5283494 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term329 x s a b y) = (term362 x s a b y).
Proof. exact (MK_COMB (@lem5283493 y s) (@lem5283490 x s a b y)). Qed.
Lemma lem5283501 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term362 x s a b y) = (term363 x s a b y).
Proof. exact (@lem19490 (term364 x a b y s) (term195 y s) (term365 x s a b y)). Qed.
Lemma lem5283502 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term329 x s a b y) = (term363 x s a b y).
Proof. exact (TRANS (@lem5283494 x s a b y) (@lem5283501 x s a b y)). Qed.
Lemma lem5283503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5283504 (x : type1018) (s : real -> Prop) (a : real) (b : real) (y : real) : (term346 x s a b y) = (term366 x s a b y).
Proof. exact (MK_COMB (@lem5283503) (@lem5283502 x s a b y)). Qed.
Lemma lem5283505 (x : type1018) (a : real) (y : real) (s : real -> Prop) (b : real) : (term348 x a y s b) = (term367 x a y s b).
Proof. exact (MK_COMB (@lem5283504 x s a b y) (@lem5283473 s b)). Qed.
Lemma lem5283512 (x : type1018) (a : real) (y : real) (s : real -> Prop) (b : real) : (term367 x a y s b) = (term368 x a y s b).
Proof. exact (@lem19699 (term369 x a b y s) (term370 x s a b y) (term23 s b)). Qed.
Lemma lem5283513 (x : type1018) (a : real) (y : real) (s : real -> Prop) (b : real) : (term348 x a y s b) = (term368 x a y s b).
Proof. exact (TRANS (@lem5283505 x a y s b) (@lem5283512 x a y s b)). Qed.
Lemma lem5283514 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term350 x a s b) = (term371 x a s b).
Proof. exact (fun_ext (fun y : real => @lem5283513 x a y s b)). Qed.
Lemma lem5283515 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283516 (x : type1018) (a : real) (s : real -> Prop) (b : real) : (term351 x a s b) = (term372 x a s b).
Proof. exact (MK_COMB (@lem5283515) (@lem5283514 x a s b)). Qed.
Lemma lem5283517 (x : type1018) (a : real) (s : real -> Prop) : (term352 x a s) = (term373 x a s).
Proof. exact (fun_ext (fun b : real => @lem5283516 x a s b)). Qed.
Lemma lem5283518 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283519 (x : type1018) (a : real) (s : real -> Prop) : (term353 x a s) = (term374 x a s).
Proof. exact (MK_COMB (@lem5283518) (@lem5283517 x a s)). Qed.
Lemma lem5283520 (x : type1018) (s : real -> Prop) : (term354 x s) = (term375 x s).
Proof. exact (fun_ext (fun a : real => @lem5283519 x a s)). Qed.
Lemma lem5283521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283522 (x : type1018) (s : real -> Prop) : (term355 x s) = (term376 x s).
Proof. exact (MK_COMB (@lem5283521) (@lem5283520 x s)). Qed.
Lemma lem5283523 (x : type1018) : (term356 x) = (term377 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5283522 x s)). Qed.
Lemma lem5283524 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5283525 (x : type1018) : (term357 x) = (term378 x).
Proof. exact (MK_COMB (@lem5283524) (@lem5283523 x)). Qed.
Lemma lem5283526 (x : type1018) : (term325 x) = (term378 x).
Proof. exact (TRANS (@lem5283472 x) (@lem5283525 x)). Qed.
Lemma lem5283527 (x : type1018) (h1 : term325 x) : term378 x.
Proof. exact (EQ_MP (@lem5283526 x) (@lem5283389 x h1)). Qed.
Lemma lem5283539 (s : real -> Prop) (b : real) (x : real) : (term51 s b x) = (term51 s b x).
Proof. exact (eq_refl (term51 s b x)). Qed.
Lemma lem5283540 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (fun_ext (fun x : real => @lem5283539 s b x)). Qed.
Lemma lem5283541 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5283543 (s : real -> Prop) (b : real) : (term53 s b) = (term53 s b).
Proof. exact (MK_COMB (@lem5283541) (@lem5283540 s b)). Qed.
Lemma lem5283544 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term53 s b.
Proof. exact (EQ_MP (@lem5283543 s b) (@lem5283432 b s a h1)). Qed.
Lemma lem5283549 (_69151 : real) (h1 : term41) : term379 _69151.
Proof. exact (@lem5283439 h1 _69151). Qed.
Lemma lem5283550 (_69151 : real) : (term379 _69151) = (real_le _69151 _69151).
Proof. exact (eq_refl (term379 _69151)). Qed.
Lemma lem5283552 (_69152 : real -> Prop) (x : type1018) (h1 : term325 x) : term380 x _69152.
Proof. exact (@lem5283527 x h1 _69152). Qed.
Lemma lem5283553 (x : type1018) (_69152 : real -> Prop) : (term380 x _69152) = (term376 x _69152).
Proof. exact (eq_refl (term380 x _69152)). Qed.
Lemma lem5283554 (_69152 : real -> Prop) (x : type1018) (h1 : term325 x) : term376 x _69152.
Proof. exact (EQ_MP (@lem5283553 x _69152) (@lem5283552 _69152 x h1)). Qed.
Lemma lem5283555 (_69152 : real -> Prop) (_69153 : real) (x : type1018) (h1 : term325 x) : term381 x _69152 _69153.
Proof. exact (@lem5283554 _69152 x h1 _69153). Qed.
Lemma lem5283556 (x : type1018) (_69153 : real) (_69152 : real -> Prop) : (term381 x _69152 _69153) = (term374 x _69153 _69152).
Proof. exact (eq_refl (term381 x _69152 _69153)). Qed.
Lemma lem5283557 (_69153 : real) (_69152 : real -> Prop) (x : type1018) (h1 : term325 x) : term374 x _69153 _69152.
Proof. exact (EQ_MP (@lem5283556 x _69153 _69152) (@lem5283555 _69152 _69153 x h1)). Qed.
Lemma lem5283558 (_69153 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term382 x _69153 _69152 _69154.
Proof. exact (@lem5283557 _69153 _69152 x h1 _69154). Qed.
Lemma lem5283559 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69154 : real) : (term382 x _69153 _69152 _69154) = (term372 x _69153 _69152 _69154).
Proof. exact (eq_refl (term382 x _69153 _69152 _69154)). Qed.
Lemma lem5283560 (_69153 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term372 x _69153 _69152 _69154.
Proof. exact (EQ_MP (@lem5283559 x _69153 _69152 _69154) (@lem5283558 _69153 _69152 _69154 x h1)). Qed.
Lemma lem5283561 (_69153 : real) (_69152 : real -> Prop) (_69154 : real) (_69155 : real) (x : type1018) (h1 : term325 x) : term383 x _69153 _69152 _69154 _69155.
Proof. exact (@lem5283560 _69153 _69152 _69154 x h1 _69155). Qed.
Lemma lem5283562 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term383 x _69153 _69152 _69154 _69155) = (term368 x _69153 _69155 _69152 _69154).
Proof. exact (eq_refl (term383 x _69153 _69152 _69154 _69155)). Qed.
Lemma lem5283563 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term368 x _69153 _69155 _69152 _69154.
Proof. exact (EQ_MP (@lem5283562 x _69153 _69155 _69152 _69154) (@lem5283561 _69153 _69152 _69154 _69155 x h1)). Qed.
Lemma lem5283564 (_69156 : real) (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term384 s b _69156.
Proof. exact (@lem5283544 b s a h1 _69156). Qed.
Lemma lem5283565 (s : real -> Prop) (b : real) (_69156 : real) : (term384 s b _69156) = (term51 s b _69156).
Proof. exact (eq_refl (term384 s b _69156)). Qed.
Lemma lem5283567 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term385 x _69153 _69155 _69152 _69154.
Proof. exact (proj2 (@lem5283563 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5283568 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term386 x _69153 _69155 _69152 _69154.
Proof. exact (proj1 (@lem5283563 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5283572 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term58 s a.
Proof. exact (proj2 (@lem5283428 b s a h1)). Qed.
Lemma lem5283578 (_69156 : real) (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term51 s b _69156.
Proof. exact (EQ_MP (@lem5283565 s b _69156) (@lem5283564 _69156 b s a h1)). Qed.
Lemma lem5283584 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term386 x _69153 _69155 _69152 _69154) = (term387 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5282355 (term195 _69155 _69152) (term364 x _69153 _69154 _69155 _69152) (term23 _69152 _69154)). Qed.
Lemma lem5283591 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term388 x _69153 _69155 _69152 _69154) = (term389 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5282355 (term181 _69155 _69154) (term360 x _69153 _69154 _69155 _69152) (term23 _69152 _69154)). Qed.
Lemma lem5283592 (_69155 : real) (_69152 : real -> Prop) : (term134 _69155 _69152) = (term134 _69155 _69152).
Proof. exact (eq_refl (term134 _69155 _69152)). Qed.
Lemma lem5283595 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term387 x _69153 _69155 _69152 _69154) = (term390 x _69153 _69155 _69152 _69154).
Proof. exact (MK_COMB (@lem5283592 _69155 _69152) (@lem5283591 x _69153 _69155 _69152 _69154)). Qed.
Lemma lem5283597 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term386 x _69153 _69155 _69152 _69154) = (term390 x _69153 _69155 _69152 _69154).
Proof. exact (TRANS (@lem5283584 x _69153 _69155 _69152 _69154) (@lem5283595 x _69153 _69155 _69152 _69154)). Qed.
Lemma lem5283598 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term390 x _69153 _69155 _69152 _69154.
Proof. exact (EQ_MP (@lem5283597 x _69153 _69155 _69152 _69154) (@lem5283568 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5283602 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term385 x _69153 _69155 _69152 _69154) = (term391 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5282355 (term195 _69155 _69152) (term365 x _69152 _69153 _69154 _69155) (term23 _69152 _69154)). Qed.
Lemma lem5283609 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term392 x _69153 _69155 _69152 _69154) = (term393 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5282355 (term181 _69155 _69154) (term361 x _69152 _69153 _69154 _69155) (term23 _69152 _69154)). Qed.
Lemma lem5283610 (_69155 : real) (_69152 : real -> Prop) : (term134 _69155 _69152) = (term134 _69155 _69152).
Proof. exact (eq_refl (term134 _69155 _69152)). Qed.
Lemma lem5283613 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term391 x _69153 _69155 _69152 _69154) = (term394 x _69153 _69155 _69152 _69154).
Proof. exact (MK_COMB (@lem5283610 _69155 _69152) (@lem5283609 x _69153 _69155 _69152 _69154)). Qed.
Lemma lem5283615 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term385 x _69153 _69155 _69152 _69154) = (term394 x _69153 _69155 _69152 _69154).
Proof. exact (TRANS (@lem5283602 x _69153 _69155 _69152 _69154) (@lem5283613 x _69153 _69155 _69152 _69154)). Qed.
Lemma lem5283616 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term394 x _69153 _69155 _69152 _69154.
Proof. exact (EQ_MP (@lem5283615 x _69153 _69155 _69152 _69154) (@lem5283567 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5283618 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : @IN real a s.
Proof. exact (proj2 (@lem5283430 b s a h1)). Qed.
Lemma lem5283619 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term395 a s.
Proof. exact (fun h0 : term195 a s => @lem5283618 b s a h1). Qed.
Lemma lem5283621 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5283622 (a : real) (s : real -> Prop) : (term395 a s) = (@IN real a s).
Proof. exact (@lem5283621 (@IN real a s)). Qed.
Lemma lem5283623 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : @IN real a s.
Proof. exact (EQ_MP (@lem5283622 a s) (@lem5283619 b s a h1)). Qed.
Lemma lem5283625 (_69151 : real) (h1 : term41) : real_le _69151 _69151.
Proof. exact (EQ_MP (@lem5283550 _69151) (@lem5283549 _69151 h1)). Qed.
Lemma lem5283626 (a : real) (h1 : term41) : real_le a a.
Proof. exact (@lem5283625 a h1). Qed.
Lemma lem5283627 (a : real) (h1 : term41) : term397 a.
Proof. exact (fun h0 : term398 a => @lem5283626 a h1). Qed.
Lemma lem5283629 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5283630 (a : real) : (term397 a) = (real_le a a).
Proof. exact (@lem5283629 (real_le a a)). Qed.
Lemma lem5283631 (a : real) (h1 : term41) : real_le a a.
Proof. exact (EQ_MP (@lem5283630 a) (@lem5283627 a h1)). Qed.
Lemma lem5283633 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : @IN real a s.
Proof. exact (proj2 (@lem5283430 b s a h1)). Qed.
Lemma lem5283634 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term395 a s.
Proof. exact (fun h0 : term195 a s => @lem5283633 b s a h1). Qed.
Lemma lem5283636 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5283637 (a : real) (s : real -> Prop) : (term395 a s) = (@IN real a s).
Proof. exact (@lem5283636 (@IN real a s)). Qed.
Lemma lem5283638 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : @IN real a s.
Proof. exact (EQ_MP (@lem5283637 a s) (@lem5283634 b s a h1)). Qed.
Lemma lem5283640 (_69151 : real) (h1 : term41) : real_le _69151 _69151.
Proof. exact (EQ_MP (@lem5283550 _69151) (@lem5283549 _69151 h1)). Qed.
Lemma lem5283641 (a : real) (h1 : term41) : real_le a a.
Proof. exact (@lem5283640 a h1). Qed.
Lemma lem5283642 (a : real) (h1 : term41) : term397 a.
Proof. exact (fun h0 : term398 a => @lem5283641 a h1). Qed.
Lemma lem5283644 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5283645 (a : real) : (term397 a) = (real_le a a).
Proof. exact (@lem5283644 (real_le a a)). Qed.
Lemma lem5283646 (a : real) (h1 : term41) : real_le a a.
Proof. exact (EQ_MP (@lem5283645 a) (@lem5283642 a h1)). Qed.
Lemma lem5283649 (s : real -> Prop) (a : real) (h1 : term58 s a) : term58 s a.
Proof. exact (h1). Qed.
Lemma lem5283650 (s : real -> Prop) (a : real) (h1 : term58 s a) : term399 s a.
Proof. exact (fun h0 : term23 s a => @lem5283649 s a h1). Qed.
Lemma lem5283652 (p : Prop) : (term400 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5283653 (s : real -> Prop) (a : real) : (term399 s a) = (term58 s a).
Proof. exact (@lem5283652 (term23 s a)). Qed.
Lemma lem5283654 (s : real -> Prop) (a : real) (h1 : term58 s a) : term58 s a.
Proof. exact (EQ_MP (@lem5283653 s a) (@lem5283650 s a h1)). Qed.
Lemma lem5283670 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283671 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term389 x _69153 _69155 _69152 _69154) = (term401 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5283670 (term360 x _69153 _69154 _69155 _69152) (term181 _69155 _69154) (term23 _69152 _69154)). Qed.
Lemma lem5283685 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5283686 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term402 _69155 _69152 _69154) = (term403 _69152 _69155 _69154).
Proof. exact (@lem5283685 (term23 _69152 _69154) (term181 _69155 _69154)). Qed.
Lemma lem5283692 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term404 x _69153 _69154 _69155 _69152) = (term404 x _69153 _69154 _69155 _69152).
Proof. exact (eq_refl (term404 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283693 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term401 x _69153 _69155 _69152 _69154) = (term405 x _69153 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283692 x _69153 _69154 _69155 _69152) (@lem5283686 _69152 _69155 _69154)). Qed.
Lemma lem5283704 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term389 x _69153 _69155 _69152 _69154) = (term405 x _69153 _69152 _69155 _69154).
Proof. exact (TRANS (@lem5283671 x _69153 _69155 _69152 _69154) (@lem5283693 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283705 (_69155 : real) (_69152 : real -> Prop) : (term134 _69155 _69152) = (term134 _69155 _69152).
Proof. exact (eq_refl (term134 _69155 _69152)). Qed.
Lemma lem5283706 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term390 x _69153 _69155 _69152 _69154) = (term406 x _69153 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283705 _69155 _69152) (@lem5283704 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283710 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283711 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term406 x _69153 _69152 _69155 _69154) = (term407 x _69153 _69152 _69155 _69154).
Proof. exact (@lem5283710 (term360 x _69153 _69154 _69155 _69152) (term195 _69155 _69152) (term403 _69152 _69155 _69154)). Qed.
Lemma lem5283725 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283726 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term408 _69152 _69155 _69154) = (term409 _69152 _69155 _69154).
Proof. exact (@lem5283725 (term23 _69152 _69154) (term195 _69155 _69152) (term181 _69155 _69154)). Qed.
Lemma lem5283742 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term404 x _69153 _69154 _69155 _69152) = (term404 x _69153 _69154 _69155 _69152).
Proof. exact (eq_refl (term404 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283743 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term407 x _69153 _69152 _69155 _69154) = (term410 x _69153 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283742 x _69153 _69154 _69155 _69152) (@lem5283726 _69152 _69155 _69154)). Qed.
Lemma lem5283754 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term406 x _69153 _69152 _69155 _69154) = (term410 x _69153 _69152 _69155 _69154).
Proof. exact (TRANS (@lem5283711 x _69153 _69152 _69155 _69154) (@lem5283743 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283755 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term390 x _69153 _69155 _69152 _69154) = (term410 x _69153 _69152 _69155 _69154).
Proof. exact (TRANS (@lem5283706 x _69153 _69152 _69155 _69154) (@lem5283754 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283757 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term411 x _69153 _69155 _69152 _69154) = (term412 x _69153 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283756) (@lem5283755 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5283782 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term402 _69155 _69152 _69154) = (term403 _69152 _69155 _69154).
Proof. exact (@lem5283781 (term23 _69152 _69154) (term181 _69155 _69154)). Qed.
Lemma lem5283788 (_69155 : real) (_69152 : real -> Prop) : (term134 _69155 _69152) = (term134 _69155 _69152).
Proof. exact (eq_refl (term134 _69155 _69152)). Qed.
Lemma lem5283789 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term413 _69155 _69152 _69154) = (term408 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283788 _69155 _69152) (@lem5283782 _69152 _69155 _69154)). Qed.
Lemma lem5283793 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283794 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term408 _69152 _69155 _69154) = (term409 _69152 _69155 _69154).
Proof. exact (@lem5283793 (term23 _69152 _69154) (term195 _69155 _69152) (term181 _69155 _69154)). Qed.
Lemma lem5283810 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term413 _69155 _69152 _69154) = (term409 _69152 _69155 _69154).
Proof. exact (TRANS (@lem5283789 _69152 _69155 _69154) (@lem5283794 _69152 _69155 _69154)). Qed.
Lemma lem5283811 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term404 x _69153 _69154 _69155 _69152) = (term404 x _69153 _69154 _69155 _69152).
Proof. exact (eq_refl (term404 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283812 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term414 x _69153 _69155 _69152 _69154) = (term410 x _69153 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283811 x _69153 _69154 _69155 _69152) (@lem5283810 _69152 _69155 _69154)). Qed.
Lemma lem5283823 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : ((term390 x _69153 _69155 _69152 _69154) = (term414 x _69153 _69155 _69152 _69154)) = ((term410 x _69153 _69152 _69155 _69154) = (term410 x _69153 _69152 _69155 _69154)).
Proof. exact (MK_COMB (@lem5283757 x _69153 _69152 _69155 _69154) (@lem5283812 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5283826 (x : Prop) : (x = x) = True.
Proof. exact (@lem5283825 Prop x). Qed.
Lemma lem5283827 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : ((term410 x _69153 _69152 _69155 _69154) = (term410 x _69153 _69152 _69155 _69154)) = True.
Proof. exact (@lem5283826 (term410 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283828 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : ((term390 x _69153 _69155 _69152 _69154) = (term414 x _69153 _69155 _69152 _69154)) = True.
Proof. exact (TRANS (@lem5283823 x _69153 _69152 _69155 _69154) (@lem5283827 x _69153 _69152 _69155 _69154)). Qed.
Lemma lem5283829 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : True = ((term390 x _69153 _69155 _69152 _69154) = (term414 x _69153 _69155 _69152 _69154)).
Proof. exact (SYM (@lem5283828 x _69153 _69155 _69152 _69154)). Qed.
Lemma lem5283830 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term390 x _69153 _69155 _69152 _69154) = (term414 x _69153 _69155 _69152 _69154).
Proof. exact (EQ_MP (@lem5283829 x _69153 _69155 _69152 _69154) (@lem0)). Qed.
Lemma lem5283831 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term414 x _69153 _69155 _69152 _69154.
Proof. exact (EQ_MP (@lem5283830 x _69153 _69155 _69152 _69154) (@lem5283598 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5283833 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5283834 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term414 x _69153 _69155 _69152 _69154) = (term416 x _69153 _69154 _69155 _69152).
Proof. exact (@lem5283833 (term413 _69155 _69152 _69154) (term360 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283836 (a : Prop) (b : Prop) : (term417 a b) = (term418 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5283837 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term419 _69155 _69152 _69154) = (term420 _69155 _69152 _69154).
Proof. exact (@lem5283836 (term195 _69155 _69152) (term402 _69155 _69152 _69154)). Qed.
Lemma lem5283839 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5283840 (_69155 : real) (_69152 : real -> Prop) : (term422 _69155 _69152) = (@IN real _69155 _69152).
Proof. exact (@lem5283839 (@IN real _69155 _69152)). Qed.
Lemma lem5283841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5283842 (_69155 : real) (_69152 : real -> Prop) : (term423 _69155 _69152) = (term29 _69155 _69152).
Proof. exact (MK_COMB (@lem5283841) (@lem5283840 _69155 _69152)). Qed.
Lemma lem5283844 (a : Prop) (b : Prop) : (term417 a b) = (term418 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5283845 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term424 _69155 _69152 _69154) = (term425 _69155 _69152 _69154).
Proof. exact (@lem5283844 (term181 _69155 _69154) (term23 _69152 _69154)). Qed.
Lemma lem5283847 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5283848 (_69155 : real) (_69154 : real) : (term426 _69155 _69154) = (real_le _69155 _69154).
Proof. exact (@lem5283847 (real_le _69155 _69154)). Qed.
Lemma lem5283849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5283850 (_69155 : real) (_69154 : real) : (term427 _69155 _69154) = (term27 _69155 _69154).
Proof. exact (MK_COMB (@lem5283849) (@lem5283848 _69155 _69154)). Qed.
Lemma lem5283851 (_69152 : real -> Prop) (_69154 : real) : (term58 _69152 _69154) = (term58 _69152 _69154).
Proof. exact (eq_refl (term58 _69152 _69154)). Qed.
Lemma lem5283852 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term425 _69155 _69152 _69154) = (term428 _69155 _69152 _69154).
Proof. exact (MK_COMB (@lem5283850 _69155 _69154) (@lem5283851 _69152 _69154)). Qed.
Lemma lem5283853 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term424 _69155 _69152 _69154) = (term428 _69155 _69152 _69154).
Proof. exact (TRANS (@lem5283845 _69155 _69152 _69154) (@lem5283852 _69155 _69152 _69154)). Qed.
Lemma lem5283854 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term420 _69155 _69152 _69154) = (term429 _69155 _69152 _69154).
Proof. exact (MK_COMB (@lem5283842 _69155 _69152) (@lem5283853 _69155 _69152 _69154)). Qed.
Lemma lem5283855 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term419 _69155 _69152 _69154) = (term429 _69155 _69152 _69154).
Proof. exact (TRANS (@lem5283837 _69155 _69152 _69154) (@lem5283854 _69155 _69152 _69154)). Qed.
Lemma lem5283856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5283857 (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term430 _69155 _69152 _69154) = (term431 _69155 _69152 _69154).
Proof. exact (MK_COMB (@lem5283856) (@lem5283855 _69155 _69152 _69154)). Qed.
Lemma lem5283858 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term360 x _69153 _69154 _69155 _69152) = (term360 x _69153 _69154 _69155 _69152).
Proof. exact (eq_refl (term360 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283859 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term416 x _69153 _69154 _69155 _69152) = (term432 x _69153 _69154 _69155 _69152).
Proof. exact (MK_COMB (@lem5283857 _69155 _69152 _69154) (@lem5283858 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283860 (x : type1018) (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) : (term414 x _69153 _69155 _69152 _69154) = (term432 x _69153 _69154 _69155 _69152).
Proof. exact (TRANS (@lem5283834 x _69153 _69154 _69155 _69152) (@lem5283859 x _69153 _69154 _69155 _69152)). Qed.
Lemma lem5283862 (s : real -> Prop) (a : real) (h1 : term41) (h2 : term58 s a) : term433 s a.
Proof. exact (conj (@lem5283646 a h1) (@lem5283654 s a h2)). Qed.
Lemma lem5283863 (b : real) (s : real -> Prop) (a : real) (h1 : term41) (h2 : term58 s a) (h3 : term113 b s a) : term434 s a.
Proof. exact (conj (@lem5283638 b s a h3) (@lem5283862 s a h1 h2)). Qed.
Lemma lem5283865 (_69153 : real) (_69154 : real) (_69155 : real) (_69152 : real -> Prop) (x : type1018) (h1 : term325 x) : term432 x _69153 _69154 _69155 _69152.
Proof. exact (EQ_MP (@lem5283860 x _69153 _69154 _69155 _69152) (@lem5283831 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5283866 (_69153 : real) (a : real) (s : real -> Prop) (x : type1018) (h1 : term325 x) : term435 x _69153 a s.
Proof. exact (@lem5283865 _69153 a a s x h1). Qed.
Lemma lem5283869 (_69153 : real) (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term436 x _69153 a s.
Proof. exact (@lem5283866 _69153 a s x h1 (@lem5283863 b s a h2 h3 h4)). Qed.
Lemma lem5283870 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term436 x b a s.
Proof. exact (@lem5283869 b x b s a h1 h2 h3 h4). Qed.
Lemma lem5283871 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term437 x b a s.
Proof. exact (fun h0 : term438 x b a s => @lem5283870 x b s a h1 h2 h3 h4). Qed.
Lemma lem5283873 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5283874 (x : type1018) (b : real) (a : real) (s : real -> Prop) : (term437 x b a s) = (term436 x b a s).
Proof. exact (@lem5283873 (term436 x b a s)). Qed.
Lemma lem5283875 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term436 x b a s.
Proof. exact (EQ_MP (@lem5283874 x b a s) (@lem5283871 x b s a h1 h2 h3 h4)). Qed.
Lemma lem5283881 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5283882 (b : real) (_69156 : real) (s : real -> Prop) : (term51 s b _69156) = (term439 b _69156 s).
Proof. exact (@lem5283881 (real_le b _69156) (term195 _69156 s)). Qed.
Lemma lem5283888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5283889 (b : real) (_69156 : real) (s : real -> Prop) : (term440 s b _69156) = (term441 b _69156 s).
Proof. exact (MK_COMB (@lem5283888) (@lem5283882 b _69156 s)). Qed.
Lemma lem5283895 (b : real) (_69156 : real) (s : real -> Prop) : (term439 b _69156 s) = (term439 b _69156 s).
Proof. exact (eq_refl (term439 b _69156 s)). Qed.
Lemma lem5283896 (b : real) (_69156 : real) (s : real -> Prop) : ((term51 s b _69156) = (term439 b _69156 s)) = ((term439 b _69156 s) = (term439 b _69156 s)).
Proof. exact (MK_COMB (@lem5283889 b _69156 s) (@lem5283895 b _69156 s)). Qed.
Lemma lem5283898 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5283899 (x : Prop) : (x = x) = True.
Proof. exact (@lem5283898 Prop x). Qed.
Lemma lem5283900 (b : real) (_69156 : real) (s : real -> Prop) : ((term439 b _69156 s) = (term439 b _69156 s)) = True.
Proof. exact (@lem5283899 (term439 b _69156 s)). Qed.
Lemma lem5283901 (b : real) (_69156 : real) (s : real -> Prop) : ((term51 s b _69156) = (term439 b _69156 s)) = True.
Proof. exact (TRANS (@lem5283896 b _69156 s) (@lem5283900 b _69156 s)). Qed.
Lemma lem5283902 (b : real) (_69156 : real) (s : real -> Prop) : True = ((term51 s b _69156) = (term439 b _69156 s)).
Proof. exact (SYM (@lem5283901 b _69156 s)). Qed.
Lemma lem5283903 (b : real) (_69156 : real) (s : real -> Prop) : (term51 s b _69156) = (term439 b _69156 s).
Proof. exact (EQ_MP (@lem5283902 b _69156 s) (@lem0)). Qed.
Lemma lem5283904 (_69156 : real) (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term439 b _69156 s.
Proof. exact (EQ_MP (@lem5283903 b _69156 s) (@lem5283578 _69156 b s a h1)). Qed.
Lemma lem5283906 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5283907 (s : real -> Prop) (b : real) (_69156 : real) : (term439 b _69156 s) = (term442 s b _69156).
Proof. exact (@lem5283906 (term195 _69156 s) (real_le b _69156)). Qed.
Lemma lem5283909 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5283910 (_69156 : real) (s : real -> Prop) : (term422 _69156 s) = (@IN real _69156 s).
Proof. exact (@lem5283909 (@IN real _69156 s)). Qed.
Lemma lem5283911 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5283912 (_69156 : real) (s : real -> Prop) : (term443 _69156 s) = (term444 _69156 s).
Proof. exact (MK_COMB (@lem5283911) (@lem5283910 _69156 s)). Qed.
Lemma lem5283913 (b : real) (_69156 : real) : (real_le b _69156) = (real_le b _69156).
Proof. exact (eq_refl (real_le b _69156)). Qed.
Lemma lem5283914 (s : real -> Prop) (b : real) (_69156 : real) : (term442 s b _69156) = (term24 s b _69156).
Proof. exact (MK_COMB (@lem5283912 _69156 s) (@lem5283913 b _69156)). Qed.
Lemma lem5283915 (s : real -> Prop) (b : real) (_69156 : real) : (term439 b _69156 s) = (term24 s b _69156).
Proof. exact (TRANS (@lem5283907 s b _69156) (@lem5283914 s b _69156)). Qed.
Lemma lem5283918 (_69156 : real) (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term24 s b _69156.
Proof. exact (EQ_MP (@lem5283915 s b _69156) (@lem5283904 _69156 b s a h1)). Qed.
Lemma lem5283919 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term445 x s b a.
Proof. exact (@lem5283918 (x s b a a) b s a h1). Qed.
Lemma lem5283922 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term446 x s b a.
Proof. exact (@lem5283919 x b s a h4 (@lem5283875 x b s a h1 h2 h3 h4)). Qed.
Lemma lem5283923 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term447 x s b a.
Proof. exact (fun h0 : term448 x s b a => @lem5283922 x b s a h1 h2 h3 h4). Qed.
Lemma lem5283925 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5283926 (x : type1018) (s : real -> Prop) (b : real) (a : real) : (term447 x s b a) = (term446 x s b a).
Proof. exact (@lem5283925 (term446 x s b a)). Qed.
Lemma lem5283927 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term446 x s b a.
Proof. exact (EQ_MP (@lem5283926 x s b a) (@lem5283923 x b s a h1 h2 h3 h4)). Qed.
Lemma lem5283943 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283944 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term393 x _69153 _69155 _69152 _69154) = (term449 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5283943 (term361 x _69152 _69153 _69154 _69155) (term181 _69155 _69154) (term23 _69152 _69154)). Qed.
Lemma lem5283958 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5283959 (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term402 _69155 _69152 _69154) = (term403 _69152 _69155 _69154).
Proof. exact (@lem5283958 (term23 _69152 _69154) (term181 _69155 _69154)). Qed.
Lemma lem5283965 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term450 x _69152 _69153 _69154 _69155) = (term450 x _69152 _69153 _69154 _69155).
Proof. exact (eq_refl (term450 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5283966 (x : type1018) (_69153 : real) (_69152 : real -> Prop) (_69155 : real) (_69154 : real) : (term449 x _69153 _69155 _69152 _69154) = (term451 x _69153 _69152 _69155 _69154).
Proof. exact (MK_COMB (@lem5283965 x _69152 _69153 _69154 _69155) (@lem5283959 _69152 _69155 _69154)). Qed.
Lemma lem5283970 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283971 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term451 x _69153 _69152 _69155 _69154) = (term452 x _69152 _69153 _69155 _69154).
Proof. exact (@lem5283970 (term23 _69152 _69154) (term361 x _69152 _69153 _69154 _69155) (term181 _69155 _69154)). Qed.
Lemma lem5283987 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term449 x _69153 _69155 _69152 _69154) = (term452 x _69152 _69153 _69155 _69154).
Proof. exact (TRANS (@lem5283966 x _69153 _69152 _69155 _69154) (@lem5283971 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5283988 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term393 x _69153 _69155 _69152 _69154) = (term452 x _69152 _69153 _69155 _69154).
Proof. exact (TRANS (@lem5283944 x _69153 _69155 _69152 _69154) (@lem5283987 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5283989 (_69155 : real) (_69152 : real -> Prop) : (term134 _69155 _69152) = (term134 _69155 _69152).
Proof. exact (eq_refl (term134 _69155 _69152)). Qed.
Lemma lem5283990 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term394 x _69153 _69155 _69152 _69154) = (term453 x _69152 _69153 _69155 _69154).
Proof. exact (MK_COMB (@lem5283989 _69155 _69152) (@lem5283988 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5283994 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5283995 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term453 x _69152 _69153 _69155 _69154) = (term454 x _69152 _69153 _69155 _69154).
Proof. exact (@lem5283994 (term23 _69152 _69154) (term195 _69155 _69152) (term455 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284021 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term394 x _69153 _69155 _69152 _69154) = (term454 x _69152 _69153 _69155 _69154).
Proof. exact (TRANS (@lem5283990 x _69152 _69153 _69155 _69154) (@lem5283995 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5284023 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term456 x _69153 _69155 _69152 _69154) = (term457 x _69152 _69153 _69155 _69154).
Proof. exact (MK_COMB (@lem5284022) (@lem5284021 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284047 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5284048 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term365 x _69152 _69153 _69154 _69155) = (term455 x _69152 _69153 _69155 _69154).
Proof. exact (@lem5284047 (term361 x _69152 _69153 _69154 _69155) (term181 _69155 _69154)). Qed.
Lemma lem5284054 (_69155 : real) (_69152 : real -> Prop) : (term134 _69155 _69152) = (term134 _69155 _69152).
Proof. exact (eq_refl (term134 _69155 _69152)). Qed.
Lemma lem5284055 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term370 x _69152 _69153 _69154 _69155) = (term458 x _69152 _69153 _69155 _69154).
Proof. exact (MK_COMB (@lem5284054 _69155 _69152) (@lem5284048 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284066 (_69152 : real -> Prop) (_69154 : real) : (term459 _69152 _69154) = (term459 _69152 _69154).
Proof. exact (eq_refl (term459 _69152 _69154)). Qed.
Lemma lem5284067 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : (term460 x _69152 _69153 _69154 _69155) = (term454 x _69152 _69153 _69155 _69154).
Proof. exact (MK_COMB (@lem5284066 _69152 _69154) (@lem5284055 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284078 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : ((term394 x _69153 _69155 _69152 _69154) = (term460 x _69152 _69153 _69154 _69155)) = ((term454 x _69152 _69153 _69155 _69154) = (term454 x _69152 _69153 _69155 _69154)).
Proof. exact (MK_COMB (@lem5284023 x _69152 _69153 _69155 _69154) (@lem5284067 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284080 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5284081 (x : Prop) : (x = x) = True.
Proof. exact (@lem5284080 Prop x). Qed.
Lemma lem5284082 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69155 : real) (_69154 : real) : ((term454 x _69152 _69153 _69155 _69154) = (term454 x _69152 _69153 _69155 _69154)) = True.
Proof. exact (@lem5284081 (term454 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284083 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : ((term394 x _69153 _69155 _69152 _69154) = (term460 x _69152 _69153 _69154 _69155)) = True.
Proof. exact (TRANS (@lem5284078 x _69152 _69153 _69155 _69154) (@lem5284082 x _69152 _69153 _69155 _69154)). Qed.
Lemma lem5284084 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : True = ((term394 x _69153 _69155 _69152 _69154) = (term460 x _69152 _69153 _69154 _69155)).
Proof. exact (SYM (@lem5284083 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284085 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term394 x _69153 _69155 _69152 _69154) = (term460 x _69152 _69153 _69154 _69155).
Proof. exact (EQ_MP (@lem5284084 x _69152 _69153 _69154 _69155) (@lem0)). Qed.
Lemma lem5284086 (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) (x : type1018) (h1 : term325 x) : term460 x _69152 _69153 _69154 _69155.
Proof. exact (EQ_MP (@lem5284085 x _69152 _69153 _69154 _69155) (@lem5283616 _69153 _69155 _69152 _69154 x h1)). Qed.
Lemma lem5284088 (b : Prop) (a : Prop) : (a \/ b) = (term415 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5284089 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term460 x _69152 _69153 _69154 _69155) = (term461 x _69153 _69155 _69152 _69154).
Proof. exact (@lem5284088 (term370 x _69152 _69153 _69154 _69155) (term23 _69152 _69154)). Qed.
Lemma lem5284091 (a : Prop) (b : Prop) : (term417 a b) = (term418 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5284092 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term462 x _69152 _69153 _69154 _69155) = (term463 x _69152 _69153 _69154 _69155).
Proof. exact (@lem5284091 (term195 _69155 _69152) (term365 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284094 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5284095 (_69155 : real) (_69152 : real -> Prop) : (term422 _69155 _69152) = (@IN real _69155 _69152).
Proof. exact (@lem5284094 (@IN real _69155 _69152)). Qed.
Lemma lem5284096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5284097 (_69155 : real) (_69152 : real -> Prop) : (term423 _69155 _69152) = (term29 _69155 _69152).
Proof. exact (MK_COMB (@lem5284096) (@lem5284095 _69155 _69152)). Qed.
Lemma lem5284099 (a : Prop) (b : Prop) : (term417 a b) = (term418 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5284100 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term464 x _69152 _69153 _69154 _69155) = (term465 x _69152 _69153 _69154 _69155).
Proof. exact (@lem5284099 (term181 _69155 _69154) (term361 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284102 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5284103 (_69155 : real) (_69154 : real) : (term426 _69155 _69154) = (real_le _69155 _69154).
Proof. exact (@lem5284102 (real_le _69155 _69154)). Qed.
Lemma lem5284104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5284105 (_69155 : real) (_69154 : real) : (term427 _69155 _69154) = (term27 _69155 _69154).
Proof. exact (MK_COMB (@lem5284104) (@lem5284103 _69155 _69154)). Qed.
Lemma lem5284107 (a : Prop) : (term421 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5284108 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term466 x _69152 _69153 _69154 _69155) = (term467 x _69152 _69153 _69154 _69155).
Proof. exact (@lem5284107 (term467 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284109 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term465 x _69152 _69153 _69154 _69155) = (term468 x _69152 _69153 _69154 _69155).
Proof. exact (MK_COMB (@lem5284105 _69155 _69154) (@lem5284108 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284110 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term464 x _69152 _69153 _69154 _69155) = (term468 x _69152 _69153 _69154 _69155).
Proof. exact (TRANS (@lem5284100 x _69152 _69153 _69154 _69155) (@lem5284109 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284111 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term463 x _69152 _69153 _69154 _69155) = (term469 x _69152 _69153 _69154 _69155).
Proof. exact (MK_COMB (@lem5284097 _69155 _69152) (@lem5284110 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284112 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term462 x _69152 _69153 _69154 _69155) = (term469 x _69152 _69153 _69154 _69155).
Proof. exact (TRANS (@lem5284092 x _69152 _69153 _69154 _69155) (@lem5284111 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284113 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5284114 (x : type1018) (_69152 : real -> Prop) (_69153 : real) (_69154 : real) (_69155 : real) : (term470 x _69152 _69153 _69154 _69155) = (term471 x _69152 _69153 _69154 _69155).
Proof. exact (MK_COMB (@lem5284113) (@lem5284112 x _69152 _69153 _69154 _69155)). Qed.
Lemma lem5284115 (_69152 : real -> Prop) (_69154 : real) : (term23 _69152 _69154) = (term23 _69152 _69154).
Proof. exact (eq_refl (term23 _69152 _69154)). Qed.
Lemma lem5284116 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term461 x _69153 _69155 _69152 _69154) = (term472 x _69153 _69155 _69152 _69154).
Proof. exact (MK_COMB (@lem5284114 x _69152 _69153 _69154 _69155) (@lem5284115 _69152 _69154)). Qed.
Lemma lem5284117 (x : type1018) (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) : (term460 x _69152 _69153 _69154 _69155) = (term472 x _69153 _69155 _69152 _69154).
Proof. exact (TRANS (@lem5284089 x _69153 _69155 _69152 _69154) (@lem5284116 x _69153 _69155 _69152 _69154)). Qed.
Lemma lem5284119 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term473 x s b a.
Proof. exact (conj (@lem5283631 a h2) (@lem5283927 x b s a h1 h2 h3 h4)). Qed.
Lemma lem5284120 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term474 x s b a.
Proof. exact (conj (@lem5283623 b s a h4) (@lem5284119 x b s a h1 h2 h3 h4)). Qed.
Lemma lem5284122 (_69153 : real) (_69155 : real) (_69152 : real -> Prop) (_69154 : real) (x : type1018) (h1 : term325 x) : term472 x _69153 _69155 _69152 _69154.
Proof. exact (EQ_MP (@lem5284117 x _69153 _69155 _69152 _69154) (@lem5284086 _69152 _69153 _69154 _69155 x h1)). Qed.
Lemma lem5284123 (b : real) (s : real -> Prop) (a : real) (x : type1018) (h1 : term325 x) : term475 x b s a.
Proof. exact (@lem5284122 b a s a x h1). Qed.
Lemma lem5284126 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term58 s a) (h4 : term113 b s a) : term23 s a.
Proof. exact (@lem5284123 b s a x h1 (@lem5284120 x b s a h1 h2 h3 h4)). Qed.
Lemma lem5284127 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : term476 s a.
Proof. exact (fun h0 : term58 s a => @lem5284126 x b s a h1 h2 h0 h3). Qed.
Lemma lem5284129 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5284130 (s : real -> Prop) (a : real) : (term476 s a) = (term23 s a).
Proof. exact (@lem5284129 (term23 s a)). Qed.
Lemma lem5284131 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : term23 s a.
Proof. exact (EQ_MP (@lem5284130 s a) (@lem5284127 x b s a h1 h2 h3)). Qed.
Lemma lem5284134 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5284136 (s : real -> Prop) (a : real) : (term58 s a) = (term477 s a).
Proof. exact (@lem5284134 (term23 s a)). Qed.
Lemma lem5284139 (b : real) (s : real -> Prop) (a : real) (h1 : term113 b s a) : term477 s a.
Proof. exact (EQ_MP (@lem5284136 s a) (@lem5283572 b s a h1)). Qed.
Lemma lem5284142 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : False.
Proof. exact (@lem5284139 b s a h3 (@lem5284131 x b s a h1 h2 h3)). Qed.
Lemma lem5284143 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : term478.
Proof. exact (fun h0 : ~ False => @lem5284142 x b s a h1 h2 h3). Qed.
Lemma lem5284145 (p : Prop) : (term396 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5284146 : term478 = False.
Proof. exact (@lem5284145 False). Qed.
Lemma lem5284147 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : False.
Proof. exact (EQ_MP (@lem5284146) (@lem5284143 x b s a h1 h2 h3)). Qed.
Lemma lem5284148 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem5284147 x b s a h1 h2 h3) (fun h4 : False => @lem5283439 h2)). Qed.
Lemma lem5284149 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : False.
Proof. exact (EQ_MP (@lem5284148 x b s a h1 h2 h3) (@lem5283439 h2)). Qed.
Lemma lem5284150 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : (term113 b s a) = False.
Proof. exact (prop_ext (fun h4 : term113 b s a => @lem5284149 x b s a h1 h2 h3) (fun h4 : False => @lem5283428 b s a h3)). Qed.
Lemma lem5284151 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : False.
Proof. exact (EQ_MP (@lem5284150 x b s a h1 h2 h3) (@lem5283428 b s a h3)). Qed.
Lemma lem5284152 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : (term325 x) = False.
Proof. exact (prop_ext (fun h4 : term325 x => @lem5284151 x b s a h1 h2 h3) (fun h4 : False => @lem5283389 x h1)). Qed.
Lemma lem5284153 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : False.
Proof. exact (EQ_MP (@lem5284152 x b s a h1 h2 h3) (@lem5283389 x h1)). Qed.
Lemma lem5284154 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem5284153 x b s a h1 h2 h3) (fun h4 : False => @lem5283315 h2)). Qed.
Lemma lem5284155 (x : type1018) (b : real) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term113 b s a) : False.
Proof. exact (EQ_MP (@lem5284154 x b s a h1 h2 h3) (@lem5283315 h2)). Qed.
Lemma lem5284156 (x : type1018) (s : real -> Prop) (a : real) (h1 : term325 x) (h2 : term41) (h3 : term116 s a) : False.
Proof. exact (ex_elim (@lem5283305 s a h3) (fun b : real => fun h0 : term115 s a b => @lem5284155 x b s a h1 h2 h0)). Qed.
Lemma lem5284157 (x : type1018) (s : real -> Prop) (h1 : term325 x) (h2 : term41) (h3 : term118 s) : False.
Proof. exact (ex_elim (@lem5283304 s h3) (fun a : real => fun h0 : term117 s a => @lem5284156 x s a h1 h2 h0)). Qed.
Lemma lem5284158 (x : type1018) (h1 : term325 x) (h2 : term41) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5282814 h3) (fun s : real -> Prop => fun h0 : term119 s => @lem5284157 x s h1 h2 h0)). Qed.
Lemma lem5284159 (h1 : term17) (h2 : term41) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5283302 h1) (fun x : type1018 => fun h0 : term327 x => @lem5284158 x h0 h2 h3)). Qed.
Lemma lem5284160 (h1 : term17) (h2 : term41) (h3 : term10) : term41 = False.
Proof. exact (prop_ext (fun h4 : term41 => @lem5284159 h1 h2 h3) (fun h4 : False => @lem5282827 h2)). Qed.
Lemma lem5284161 (h1 : term17) (h2 : term41) (h3 : term10) : False.
Proof. exact (EQ_MP (@lem5284160 h1 h2 h3) (@lem5282827 h2)). Qed.
Lemma lem5284162 (h1 : term41) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5284161 h0 h1 h2). Qed.
Lemma lem5284163 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5284164 (h1 : term41) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5284163) (@lem5284162 h1 h2)). Qed.
Lemma lem5284165 (h1 : term10) : term20.
Proof. exact (fun h0 : term41 => @lem5284164 h0 h1). Qed.
Lemma lem5284166 : term22.
Proof. exact (fun h0 : term10 => @lem5284165 h0). Qed.
Lemma lem5284167 : term11.
Proof. exact (EQ_MP (@lem5282601) (@lem5284166)). Qed.
Lemma lem5284169 : term11.
Proof. exact (@lem5282375 (@lem5284167)). Qed.
Lemma lem5284170 (h1 : term10) : term19.
Proof. exact (@lem5284169 (@lem5282360 h1)). Qed.
Lemma lem5284171 (h1 : term10) : term15.
Proof. exact (@lem5284170 h1 (@lem1339240)). Qed.
Lemma lem5284172 (h1 : term10) : False.
Proof. exact (@lem5284171 h1 (@lem5269266)). Qed.
Lemma lem5284173 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5284172 h1) (fun h2 : False => @lem5282360 h1)). Qed.
Lemma lem5284174 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5284173 h1) (@lem5282360 h1)). Qed.
Lemma lem5284175 : term9.
Proof. exact (fun h0 : term10 => @lem5284174 h0). Qed.
Lemma lem5284176 : term8.
Proof. exact (EQ_MP (@lem5282359) (@lem5284175)). Qed.
