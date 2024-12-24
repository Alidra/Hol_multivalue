Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_o_term_abbrevs.
Require Import ETA_AX_spec.
Require Import POLYNOMIAL_FUNCTION_ADD_spec.
Require Import POLYNOMIAL_FUNCTION_CONST_spec.
Require Import POLYNOMIAL_FUNCTION_INDUCT_spec.
Require Import POLYNOMIAL_FUNCTION_MUL_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm951_spec.
Require Import thm952_spec.
Lemma lem7586373 (p : real -> real) : term0 p.
Proof. exact (@lem7577427 p). Qed.
Lemma lem7586374 (p : real -> real) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem7586375 (p : real -> real) : term1 p.
Proof. exact (EQ_MP (@lem7586374 p) (@lem7586373 p)). Qed.
Lemma lem7586376 (p : real -> real) (q : real -> real) : term2 p q.
Proof. exact (@lem7586375 p q). Qed.
Lemma lem7586377 (p : real -> real) (q : real -> real) : (term2 p q) = (term3 p q).
Proof. exact (eq_refl (term2 p q)). Qed.
Lemma lem7586378 (p : real -> real) (q : real -> real) : term3 p q.
Proof. exact (EQ_MP (@lem7586377 p q) (@lem7586376 p q)). Qed.
Lemma lem7586379 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem7586380 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term5 p q.
Proof. exact (@lem7586378 p q (@lem7586379 p q h1)). Qed.
Lemma lem7586381 (p : real -> real) (q : real -> real) : (term5 p q) = ((term5 p q) = True).
Proof. exact (@lem7 (term5 p q)). Qed.
Lemma lem7586382 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term5 p q) = True.
Proof. exact (EQ_MP (@lem7586381 p q) (@lem7586380 p q h1)). Qed.
Lemma lem7586388 (p : real -> real) : term6 p.
Proof. exact (@lem7567170 p). Qed.
Lemma lem7586389 (p : real -> real) : (term6 p) = (term7 p).
Proof. exact (eq_refl (term6 p)). Qed.
Lemma lem7586390 (p : real -> real) : term7 p.
Proof. exact (EQ_MP (@lem7586389 p) (@lem7586388 p)). Qed.
Lemma lem7586391 (p : real -> real) (q : real -> real) : term8 p q.
Proof. exact (@lem7586390 p q). Qed.
Lemma lem7586392 (p : real -> real) (q : real -> real) : (term8 p q) = (term9 p q).
Proof. exact (eq_refl (term8 p q)). Qed.
Lemma lem7586393 (p : real -> real) (q : real -> real) : term9 p q.
Proof. exact (EQ_MP (@lem7586392 p q) (@lem7586391 p q)). Qed.
Lemma lem7586394 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term4 p q.
Proof. exact (h1). Qed.
Lemma lem7586395 (p : real -> real) (q : real -> real) (h1 : term4 p q) : term10 p q.
Proof. exact (@lem7586393 p q (@lem7586394 p q h1)). Qed.
Lemma lem7586396 (p : real -> real) (q : real -> real) : (term10 p q) = ((term10 p q) = True).
Proof. exact (@lem7 (term10 p q)). Qed.
Lemma lem7586397 (p : real -> real) (q : real -> real) (h1 : term4 p q) : (term10 p q) = True.
Proof. exact (EQ_MP (@lem7586396 p q) (@lem7586395 p q h1)). Qed.
Lemma lem7586403 {A B C : Type'} (f : B -> C) : term11 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem7586404 {A B C : Type'} (f : B -> C) : (term11 A B C f) = (term12 A B C f).
Proof. exact (eq_refl (term11 A B C f)). Qed.
Lemma lem7586405 {A B C : Type'} (f : B -> C) : term12 A B C f.
Proof. exact (EQ_MP (@lem7586404 A B C f) (@lem7586403 A B C f)). Qed.
Lemma lem7586406 {A B C : Type'} (f : B -> C) (g : A -> B) : term13 A B C f g.
Proof. exact (@lem7586405 A B C f g). Qed.
Lemma lem7586407 {A B C : Type'} (f : B -> C) (g : A -> B) : (term13 A B C f g) = ((@o A B C f g) = (term14 A B C f g)).
Proof. exact (eq_refl (term13 A B C f g)). Qed.
Lemma lem7586409 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem7586410 (P : type1028) (h1 : term15) : term16 P.
Proof. exact (@lem7586409 h1 P). Qed.
Lemma lem7586411 (P : type1028) : (term16 P) = (term17 P).
Proof. exact (eq_refl (term16 P)). Qed.
Lemma lem7586412 (P : type1028) (h1 : term15) : term17 P.
Proof. exact (EQ_MP (@lem7586411 P) (@lem7586410 P h1)). Qed.
Lemma lem7586413 (P : type1028) (h1 : term18 P) : term18 P.
Proof. exact (h1). Qed.
Lemma lem7586414 (P : type1028) (h1 : term15) (h2 : term18 P) : term19 P.
Proof. exact (@lem7586412 P h1 (@lem7586413 P h2)). Qed.
Lemma lem7586415 (P : type1028) (h1 : term18 P) : term20 P.
Proof. exact (fun h0 : term15 => @lem7586414 P h0 h1). Qed.
Lemma lem7586416 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem7586417 (P : type1028) (h1 : term15) (h2 : term18 P) : term19 P.
Proof. exact (@lem7586415 P h2 (@lem7586416 h1)). Qed.
Lemma lem7586418 (P : type1028) (h1 : term15) : term17 P.
Proof. exact (fun h0 : term18 P => @lem7586417 P h1 h0). Qed.
Lemma lem7586419 (h1 : term15) : term15.
Proof. exact (fun P : type1028 => @lem7586418 P h1). Qed.
Lemma lem7586420 : term21.
Proof. exact (fun h0 : term15 => @lem7586419 h0). Qed.
Lemma lem7586421 : term15.
Proof. exact (@lem7586420 (@lem7586372)). Qed.
Lemma lem7586422 (P : type1028) : term16 P.
Proof. exact (@lem7586421 P). Qed.
Lemma lem7586423 (P : type1028) : (term16 P) = (term17 P).
Proof. exact (eq_refl (term16 P)). Qed.
Lemma lem7586425 {A : Type'} (P : Prop) : term22 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7586426 {A : Type'} (P : Prop) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem7586427 {A : Type'} (P : Prop) : term23 A P.
Proof. exact (EQ_MP (@lem7586426 A P) (@lem7586425 A P)). Qed.
Lemma lem7586428 {A : Type'} (P : Prop) (Q : A -> Prop) : term24 A P Q.
Proof. exact (@lem7586427 A P Q). Qed.
Lemma lem7586429 {A : Type'} (P : Prop) (Q : A -> Prop) : (term24 A P Q) = ((term25 A P Q) = (term26 A P Q)).
Proof. exact (eq_refl (term24 A P Q)). Qed.
Lemma lem7586431 {A B : Type'} (P : type1413 A B) : term27 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem7586432 {A B : Type'} (P : type1413 A B) : (term27 A B P) = ((term28 A B P) = (term29 A B P)).
Proof. exact (eq_refl (term27 A B P)). Qed.
Lemma lem7586435 {A B : Type'} (P : type1413 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (EQ_MP (@lem7586432 A B P) (@lem7586431 A B P)). Qed.
Lemma lem7586436 (P : type1025) : (term30 P) = (term31 P).
Proof. exact (@lem7586435 (real -> real) (real -> real) P). Qed.
Lemma lem7586437 : term32 = term33.
Proof. exact (@lem7586436 term34). Qed.
Lemma lem7586438 (p : real -> real) : (term35 p) = (term36 p).
Proof. exact (eq_refl (term35 p)). Qed.
Lemma lem7586439 (q : real -> real) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem7586440 (p : real -> real) (q : real -> real) : (term37 p q) = (term38 p q).
Proof. exact (MK_COMB (@lem7586438 p) (@lem7586439 q)). Qed.
Lemma lem7586441 (p : real -> real) (q : real -> real) : (term38 p q) = (term39 p q).
Proof. exact (eq_refl (term38 p q)). Qed.
Lemma lem7586442 (p : real -> real) (q : real -> real) : (term37 p q) = (term39 p q).
Proof. exact (TRANS (@lem7586440 p q) (@lem7586441 p q)). Qed.
Lemma lem7586443 (p : real -> real) : (term40 p) = (term36 p).
Proof. exact (fun_ext (fun q : real -> real => @lem7586442 p q)). Qed.
Lemma lem7586444 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586445 (p : real -> real) : (term41 p) = (term42 p).
Proof. exact (MK_COMB (@lem7586444) (@lem7586443 p)). Qed.
Lemma lem7586446 : term43 = term44.
Proof. exact (fun_ext (fun p : real -> real => @lem7586445 p)). Qed.
Lemma lem7586447 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586448 : term32 = term45.
Proof. exact (MK_COMB (@lem7586447) (@lem7586446)). Qed.
Lemma lem7586449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7586450 : term46 = term47.
Proof. exact (MK_COMB (@lem7586449) (@lem7586448)). Qed.
Lemma lem7586451 (p : real -> real) : (term35 p) = (term36 p).
Proof. exact (eq_refl (term35 p)). Qed.
Lemma lem7586452 (q : real -> real) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem7586453 (p : real -> real) (q : real -> real) : (term37 p q) = (term38 p q).
Proof. exact (MK_COMB (@lem7586451 p) (@lem7586452 q)). Qed.
Lemma lem7586454 (p : real -> real) (q : real -> real) : (term38 p q) = (term39 p q).
Proof. exact (eq_refl (term38 p q)). Qed.
Lemma lem7586455 (p : real -> real) (q : real -> real) : (term37 p q) = (term39 p q).
Proof. exact (TRANS (@lem7586453 p q) (@lem7586454 p q)). Qed.
Lemma lem7586456 (q : real -> real) : (term48 q) = (term49 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586455 p q)). Qed.
Lemma lem7586457 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586458 (q : real -> real) : (term50 q) = (term51 q).
Proof. exact (MK_COMB (@lem7586457) (@lem7586456 q)). Qed.
Lemma lem7586459 : term52 = term53.
Proof. exact (fun_ext (fun q : real -> real => @lem7586458 q)). Qed.
Lemma lem7586460 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586461 : term33 = term54.
Proof. exact (MK_COMB (@lem7586460) (@lem7586459)). Qed.
Lemma lem7586462 : (term32 = term33) = (term45 = term54).
Proof. exact (MK_COMB (@lem7586450) (@lem7586461)). Qed.
Lemma lem7586463 : term45 = term54.
Proof. exact (EQ_MP (@lem7586462) (@lem7586437)). Qed.
Lemma lem7586464 : term54 = term45.
Proof. exact (SYM (@lem7586463)). Qed.
Lemma lem7586494 (q : Prop) (p : Prop) (r : Prop) : (term55 p q r) = (term56 q p r).
Proof. exact (EQ_MP (@lem952 q p r) (@lem951 p q r)). Qed.
Lemma lem7586495 (p : real -> real) (q : real -> real) : (term39 p q) = (term57 p q).
Proof. exact (@lem7586494 (polynomial_function q) (polynomial_function p) (term58 p q)). Qed.
Lemma lem7586500 (q : real -> real) : (term49 q) = (term59 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586495 p q)). Qed.
Lemma lem7586501 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586502 (q : real -> real) : (term51 q) = (term60 q).
Proof. exact (MK_COMB (@lem7586501) (@lem7586500 q)). Qed.
Lemma lem7586504 {A : Type'} (P : Prop) (Q : A -> Prop) : (term25 A P Q) = (term26 A P Q).
Proof. exact (EQ_MP (@lem7586429 A P Q) (@lem7586428 A P Q)). Qed.
Lemma lem7586505 (P : Prop) (Q : type1028) : (term61 P Q) = (term62 P Q).
Proof. exact (@lem7586504 (real -> real) P Q). Qed.
Lemma lem7586506 (q : real -> real) : (term63 q) = (term64 q).
Proof. exact (@lem7586505 (polynomial_function q) (term65 q)). Qed.
Lemma lem7586507 (p : real -> real) (q : real -> real) : (term66 q p) = (term67 p q).
Proof. exact (eq_refl (term66 q p)). Qed.
Lemma lem7586508 (q : real -> real) : (term68 q) = (term68 q).
Proof. exact (eq_refl (term68 q)). Qed.
Lemma lem7586509 (p : real -> real) (q : real -> real) : (term69 q p) = (term57 p q).
Proof. exact (MK_COMB (@lem7586508 q) (@lem7586507 p q)). Qed.
Lemma lem7586510 (q : real -> real) : (term70 q) = (term59 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586509 p q)). Qed.
Lemma lem7586511 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586512 (q : real -> real) : (term63 q) = (term60 q).
Proof. exact (MK_COMB (@lem7586511) (@lem7586510 q)). Qed.
Lemma lem7586513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7586514 (q : real -> real) : (term71 q) = (term72 q).
Proof. exact (MK_COMB (@lem7586513) (@lem7586512 q)). Qed.
Lemma lem7586515 (p : real -> real) (q : real -> real) : (term66 q p) = (term67 p q).
Proof. exact (eq_refl (term66 q p)). Qed.
Lemma lem7586516 (q : real -> real) : (term73 q) = (term65 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586515 p q)). Qed.
Lemma lem7586517 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586518 (q : real -> real) : (term74 q) = (term75 q).
Proof. exact (MK_COMB (@lem7586517) (@lem7586516 q)). Qed.
Lemma lem7586519 (q : real -> real) : (term68 q) = (term68 q).
Proof. exact (eq_refl (term68 q)). Qed.
Lemma lem7586520 (q : real -> real) : (term64 q) = (term76 q).
Proof. exact (MK_COMB (@lem7586519 q) (@lem7586518 q)). Qed.
Lemma lem7586521 (q : real -> real) : ((term63 q) = (term64 q)) = ((term60 q) = (term76 q)).
Proof. exact (MK_COMB (@lem7586514 q) (@lem7586520 q)). Qed.
Lemma lem7586522 (q : real -> real) : (term60 q) = (term76 q).
Proof. exact (EQ_MP (@lem7586521 q) (@lem7586506 q)). Qed.
Lemma lem7586551 (q : real -> real) : (term51 q) = (term76 q).
Proof. exact (TRANS (@lem7586502 q) (@lem7586522 q)). Qed.
Lemma lem7586552 : term53 = term77.
Proof. exact (fun_ext (fun q : real -> real => @lem7586551 q)). Qed.
Lemma lem7586553 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586554 : term54 = term78.
Proof. exact (MK_COMB (@lem7586553) (@lem7586552)). Qed.
Lemma lem7586579 : term78 = term54.
Proof. exact (SYM (@lem7586554)). Qed.
Lemma lem7586580 (q : real -> real) (h1 : polynomial_function q) : polynomial_function q.
Proof. exact (h1). Qed.
Lemma lem7586582 (P : type1028) : term17 P.
Proof. exact (EQ_MP (@lem7586423 P) (@lem7586422 P)). Qed.
Lemma lem7586583 (q : real -> real) : term79 q.
Proof. exact (@lem7586582 (term80 q)). Qed.
Lemma lem7586584 (q : real -> real) : (term81 q) = (term82 q).
Proof. exact (eq_refl (term81 q)). Qed.
Lemma lem7586585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586586 (q : real -> real) : (term83 q) = (term84 q).
Proof. exact (MK_COMB (@lem7586585) (@lem7586584 q)). Qed.
Lemma lem7586587 (c : real) (q : real -> real) : (term85 q c) = (term86 c q).
Proof. exact (eq_refl (term85 q c)). Qed.
Lemma lem7586588 (q : real -> real) : (term87 q) = (term88 q).
Proof. exact (fun_ext (fun c : real => @lem7586587 c q)). Qed.
Lemma lem7586589 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7586590 (q : real -> real) : (term89 q) = (term90 q).
Proof. exact (MK_COMB (@lem7586589) (@lem7586588 q)). Qed.
Lemma lem7586591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586592 (q : real -> real) : (term91 q) = (term92 q).
Proof. exact (MK_COMB (@lem7586591) (@lem7586590 q)). Qed.
Lemma lem7586593 (p : real -> real) (q : real -> real) : (term93 q p) = (term58 p q).
Proof. exact (eq_refl (term93 q p)). Qed.
Lemma lem7586594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586595 (p : real -> real) (q : real -> real) : (term94 q p) = (term95 p q).
Proof. exact (MK_COMB (@lem7586594) (@lem7586593 p q)). Qed.
Lemma lem7586596 (q' : real -> real) (q : real -> real) : (term93 q q') = (term58 q' q).
Proof. exact (eq_refl (term93 q q')). Qed.
Lemma lem7586597 (p : real -> real) (q' : real -> real) (q : real -> real) : (term96 p q q') = (term97 p q' q).
Proof. exact (MK_COMB (@lem7586595 p q) (@lem7586596 q' q)). Qed.
Lemma lem7586598 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7586599 (p : real -> real) (q' : real -> real) (q : real -> real) : (term98 p q q') = (term99 p q' q).
Proof. exact (MK_COMB (@lem7586598) (@lem7586597 p q' q)). Qed.
Lemma lem7586600 (p : real -> real) (q' : real -> real) (q : real -> real) : (term100 q p q') = (term101 p q' q).
Proof. exact (eq_refl (term100 q p q')). Qed.
Lemma lem7586601 (p : real -> real) (q' : real -> real) (q : real -> real) : (term102 q p q') = (term103 p q' q).
Proof. exact (MK_COMB (@lem7586599 p q' q) (@lem7586600 p q' q)). Qed.
Lemma lem7586602 (p : real -> real) (q : real -> real) : (term104 q p) = (term105 p q).
Proof. exact (fun_ext (fun q' : real -> real => @lem7586601 p q' q)). Qed.
Lemma lem7586603 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586604 (p : real -> real) (q : real -> real) : (term106 q p) = (term107 p q).
Proof. exact (MK_COMB (@lem7586603) (@lem7586602 p q)). Qed.
Lemma lem7586605 (q : real -> real) : (term108 q) = (term109 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586604 p q)). Qed.
Lemma lem7586606 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586607 (q : real -> real) : (term110 q) = (term111 q).
Proof. exact (MK_COMB (@lem7586606) (@lem7586605 q)). Qed.
Lemma lem7586608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586609 (q : real -> real) : (term112 q) = (term113 q).
Proof. exact (MK_COMB (@lem7586608) (@lem7586607 q)). Qed.
Lemma lem7586610 (p : real -> real) (q : real -> real) : (term93 q p) = (term58 p q).
Proof. exact (eq_refl (term93 q p)). Qed.
Lemma lem7586611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586612 (p : real -> real) (q : real -> real) : (term94 q p) = (term95 p q).
Proof. exact (MK_COMB (@lem7586611) (@lem7586610 p q)). Qed.
Lemma lem7586613 (q' : real -> real) (q : real -> real) : (term93 q q') = (term58 q' q).
Proof. exact (eq_refl (term93 q q')). Qed.
Lemma lem7586614 (p : real -> real) (q' : real -> real) (q : real -> real) : (term96 p q q') = (term97 p q' q).
Proof. exact (MK_COMB (@lem7586612 p q) (@lem7586613 q' q)). Qed.
Lemma lem7586615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7586616 (p : real -> real) (q' : real -> real) (q : real -> real) : (term98 p q q') = (term99 p q' q).
Proof. exact (MK_COMB (@lem7586615) (@lem7586614 p q' q)). Qed.
Lemma lem7586617 (p : real -> real) (q' : real -> real) (q : real -> real) : (term114 q p q') = (term115 p q' q).
Proof. exact (eq_refl (term114 q p q')). Qed.
Lemma lem7586618 (p : real -> real) (q' : real -> real) (q : real -> real) : (term116 q p q') = (term117 p q' q).
Proof. exact (MK_COMB (@lem7586616 p q' q) (@lem7586617 p q' q)). Qed.
Lemma lem7586619 (p : real -> real) (q : real -> real) : (term118 q p) = (term119 p q).
Proof. exact (fun_ext (fun q' : real -> real => @lem7586618 p q' q)). Qed.
Lemma lem7586620 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586621 (p : real -> real) (q : real -> real) : (term120 q p) = (term121 p q).
Proof. exact (MK_COMB (@lem7586620) (@lem7586619 p q)). Qed.
Lemma lem7586622 (q : real -> real) : (term122 q) = (term123 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586621 p q)). Qed.
Lemma lem7586623 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586624 (q : real -> real) : (term124 q) = (term125 q).
Proof. exact (MK_COMB (@lem7586623) (@lem7586622 q)). Qed.
Lemma lem7586625 (q : real -> real) : (term126 q) = (term127 q).
Proof. exact (MK_COMB (@lem7586609 q) (@lem7586624 q)). Qed.
Lemma lem7586626 (q : real -> real) : (term128 q) = (term129 q).
Proof. exact (MK_COMB (@lem7586592 q) (@lem7586625 q)). Qed.
Lemma lem7586627 (q : real -> real) : (term130 q) = (term131 q).
Proof. exact (MK_COMB (@lem7586586 q) (@lem7586626 q)). Qed.
Lemma lem7586628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7586629 (q : real -> real) : (term132 q) = (term133 q).
Proof. exact (MK_COMB (@lem7586628) (@lem7586627 q)). Qed.
Lemma lem7586630 (p : real -> real) (q : real -> real) : (term93 q p) = (term58 p q).
Proof. exact (eq_refl (term93 q p)). Qed.
Lemma lem7586631 (p : real -> real) : (term68 p) = (term68 p).
Proof. exact (eq_refl (term68 p)). Qed.
Lemma lem7586632 (p : real -> real) (q : real -> real) : (term134 q p) = (term67 p q).
Proof. exact (MK_COMB (@lem7586631 p) (@lem7586630 p q)). Qed.
Lemma lem7586633 (q : real -> real) : (term135 q) = (term65 q).
Proof. exact (fun_ext (fun p : real -> real => @lem7586632 p q)). Qed.
Lemma lem7586634 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586635 (q : real -> real) : (term136 q) = (term75 q).
Proof. exact (MK_COMB (@lem7586634) (@lem7586633 q)). Qed.
Lemma lem7586636 (q : real -> real) : (term79 q) = (term137 q).
Proof. exact (MK_COMB (@lem7586629 q) (@lem7586635 q)). Qed.
Lemma lem7586637 (q : real -> real) : term137 q.
Proof. exact (EQ_MP (@lem7586636 q) (@lem7586583 q)). Qed.
Lemma lem7586641 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586642 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586641 real real real f g). Qed.
Lemma lem7586643 (q : real -> real) : (term139 q) = (term140 q).
Proof. exact (@lem7586642 term141 q). Qed.
Lemma lem7586645 {A B : Type'} (f : A -> B) (y : A) : (term142 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7586646 (f : real -> real) (y : real) : (term143 f y) = (f y).
Proof. exact (@lem7586645 real real f y). Qed.
Lemma lem7586647 (q : real -> real) (x : real) : (term144 q x) = (term145 q x).
Proof. exact (@lem7586646 term141 (q x)). Qed.
Lemma lem7586648 (x : real) : (term146 x) = x.
Proof. exact (eq_refl (term146 x)). Qed.
Lemma lem7586649 : term147 = term141.
Proof. exact (fun_ext (fun x : real => @lem7586648 x)). Qed.
Lemma lem7586650 (q : real -> real) (x : real) : (q x) = (q x).
Proof. exact (eq_refl (q x)). Qed.
Lemma lem7586651 (q : real -> real) (x : real) : (term144 q x) = (term145 q x).
Proof. exact (MK_COMB (@lem7586649) (@lem7586650 q x)). Qed.
Lemma lem7586652 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7586653 (q : real -> real) (x : real) : (term148 q x) = (term149 q x).
Proof. exact (MK_COMB (@lem7586652) (@lem7586651 q x)). Qed.
Lemma lem7586654 (q : real -> real) (x : real) : (term145 q x) = (q x).
Proof. exact (eq_refl (term145 q x)). Qed.
Lemma lem7586655 (q : real -> real) (x : real) : ((term144 q x) = (term145 q x)) = ((term145 q x) = (q x)).
Proof. exact (MK_COMB (@lem7586653 q x) (@lem7586654 q x)). Qed.
Lemma lem7586656 (q : real -> real) (x : real) : (term145 q x) = (q x).
Proof. exact (EQ_MP (@lem7586655 q x) (@lem7586647 q x)). Qed.
Lemma lem7586657 (q : real -> real) : (term140 q) = (term150 q).
Proof. exact (fun_ext (fun x : real => @lem7586656 q x)). Qed.
Lemma lem7586658 (q : real -> real) : (term139 q) = (term150 q).
Proof. exact (TRANS (@lem7586643 q) (@lem7586657 q)). Qed.
Lemma lem7586659 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586660 (q : real -> real) : (term82 q) = (term151 q).
Proof. exact (MK_COMB (@lem7586659) (@lem7586658 q)). Qed.
Lemma lem7586661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586662 (q : real -> real) : (term84 q) = (term152 q).
Proof. exact (MK_COMB (@lem7586661) (@lem7586660 q)). Qed.
Lemma lem7586670 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586671 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586670 real real real f g). Qed.
Lemma lem7586672 (c : real) (q : real -> real) : (term153 c q) = (term154 c q).
Proof. exact (@lem7586671 (term155 c) q). Qed.
Lemma lem7586674 {A B : Type'} (f : A -> B) (y : A) : (term142 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7586675 (f : real -> real) (y : real) : (term143 f y) = (f y).
Proof. exact (@lem7586674 real real f y). Qed.
Lemma lem7586676 (c : real) (q : real -> real) (x : real) : (term156 c q x) = (term157 c q x).
Proof. exact (@lem7586675 (term155 c) (q x)). Qed.
Lemma lem7586677 (x : real) (c : real) : (term158 c x) = c.
Proof. exact (eq_refl (term158 c x)). Qed.
Lemma lem7586678 (c : real) : (term159 c) = (term155 c).
Proof. exact (fun_ext (fun x : real => @lem7586677 x c)). Qed.
Lemma lem7586679 (q : real -> real) (x : real) : (q x) = (q x).
Proof. exact (eq_refl (q x)). Qed.
Lemma lem7586680 (c : real) (q : real -> real) (x : real) : (term156 c q x) = (term157 c q x).
Proof. exact (MK_COMB (@lem7586678 c) (@lem7586679 q x)). Qed.
Lemma lem7586681 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7586682 (c : real) (q : real -> real) (x : real) : (term160 c q x) = (term161 c q x).
Proof. exact (MK_COMB (@lem7586681) (@lem7586680 c q x)). Qed.
Lemma lem7586683 (q : real -> real) (x : real) (c : real) : (term157 c q x) = c.
Proof. exact (eq_refl (term157 c q x)). Qed.
Lemma lem7586684 (q : real -> real) (x : real) (c : real) : ((term156 c q x) = (term157 c q x)) = ((term157 c q x) = c).
Proof. exact (MK_COMB (@lem7586682 c q x) (@lem7586683 q x c)). Qed.
Lemma lem7586685 (q : real -> real) (x : real) (c : real) : (term157 c q x) = c.
Proof. exact (EQ_MP (@lem7586684 q x c) (@lem7586676 c q x)). Qed.
Lemma lem7586686 (q : real -> real) (c : real) : (term154 c q) = (term155 c).
Proof. exact (fun_ext (fun x : real => @lem7586685 q x c)). Qed.
Lemma lem7586687 (q : real -> real) (c : real) : (term153 c q) = (term155 c).
Proof. exact (TRANS (@lem7586672 c q) (@lem7586686 q c)). Qed.
Lemma lem7586688 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586689 (q : real -> real) (c : real) : (term86 c q) = (term162 c).
Proof. exact (MK_COMB (@lem7586688) (@lem7586687 q c)). Qed.
Lemma lem7586690 (q : real -> real) : (term88 q) = term163.
Proof. exact (fun_ext (fun c : real => @lem7586689 q c)). Qed.
Lemma lem7586691 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7586692 (q : real -> real) : (term90 q) = term164.
Proof. exact (MK_COMB (@lem7586691) (@lem7586690 q)). Qed.
Lemma lem7586697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586698 (q : real -> real) : (term92 q) = term165.
Proof. exact (MK_COMB (@lem7586697) (@lem7586692 q)). Qed.
Lemma lem7586716 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7586717 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7586716 p q p' q'). Qed.
Lemma lem7586718 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7586717 p q p'). Qed.
Lemma lem7586719 (p : real -> real) (q' : real -> real) (q : real -> real) : term169 p q' q.
Proof. exact (@lem7586718 (term97 p q' q) (term101 p q' q)). Qed.
Lemma lem7586720 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) : term170 p q' q p'.
Proof. exact (@lem7586719 p q' q p'). Qed.
Lemma lem7586721 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) : (term170 p q' q p') = (term171 p q' q p').
Proof. exact (eq_refl (term170 p q' q p')). Qed.
Lemma lem7586722 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) : term171 p q' q p'.
Proof. exact (EQ_MP (@lem7586721 p q' q p') (@lem7586720 p q' q p')). Qed.
Lemma lem7586723 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) (q'' : Prop) : term172 p q' q p' q''.
Proof. exact (@lem7586722 p q' q p' q''). Qed.
Lemma lem7586724 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) (q'' : Prop) : (term172 p q' q p' q'') = (term173 p q' q p' q'').
Proof. exact (eq_refl (term172 p q' q p' q'')). Qed.
Lemma lem7586725 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) (q'' : Prop) : term173 p q' q p' q''.
Proof. exact (EQ_MP (@lem7586724 p q' q p' q'') (@lem7586723 p q' q p' q'')). Qed.
Lemma lem7586729 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586730 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586729 real real real f g). Qed.
Lemma lem7586731 (p : real -> real) (q : real -> real) : (@o real real real p q) = (term138 p q).
Proof. exact (@lem7586730 p q). Qed.
Lemma lem7586732 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586733 (p : real -> real) (q : real -> real) : (term58 p q) = (term174 p q).
Proof. exact (MK_COMB (@lem7586732) (@lem7586731 p q)). Qed.
Lemma lem7586734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586735 (p : real -> real) (q : real -> real) : (term95 p q) = (term175 p q).
Proof. exact (MK_COMB (@lem7586734) (@lem7586733 p q)). Qed.
Lemma lem7586737 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586738 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586737 real real real f g). Qed.
Lemma lem7586739 (q' : real -> real) (q : real -> real) : (@o real real real q' q) = (term138 q' q).
Proof. exact (@lem7586738 q' q). Qed.
Lemma lem7586740 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586741 (q' : real -> real) (q : real -> real) : (term58 q' q) = (term174 q' q).
Proof. exact (MK_COMB (@lem7586740) (@lem7586739 q' q)). Qed.
Lemma lem7586742 (p : real -> real) (q' : real -> real) (q : real -> real) : (term97 p q' q) = (term176 p q' q).
Proof. exact (MK_COMB (@lem7586735 p q) (@lem7586741 q' q)). Qed.
Lemma lem7586745 (p : real -> real) (q' : real -> real) (q : real -> real) (q'' : Prop) : term177 p q' q q''.
Proof. exact (@lem7586725 p q' q (term176 p q' q) q''). Qed.
Lemma lem7586746 (p : real -> real) (q' : real -> real) (q : real -> real) (q'' : Prop) : term178 p q' q q''.
Proof. exact (@lem7586745 p q' q q'' (@lem7586742 p q' q)). Qed.
Lemma lem7586747 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term176 p q' q.
Proof. exact (h1). Qed.
Lemma lem7586748 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term174 q' q.
Proof. exact (proj2 (@lem7586747 p q' q h1)). Qed.
Lemma lem7586749 (q' : real -> real) (q : real -> real) : (term174 q' q) = ((term174 q' q) = True).
Proof. exact (@lem7 (term174 q' q)). Qed.
Lemma lem7586751 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term174 p q.
Proof. exact (proj1 (@lem7586747 p q' q h1)). Qed.
Lemma lem7586752 (p : real -> real) (q : real -> real) : (term174 p q) = ((term174 p q) = True).
Proof. exact (@lem7 (term174 p q)). Qed.
Lemma lem7586755 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586756 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586755 real real real f g). Qed.
Lemma lem7586757 (p : real -> real) (q' : real -> real) (q : real -> real) : (term179 p q' q) = (term180 p q' q).
Proof. exact (@lem7586756 (term181 p q') q). Qed.
Lemma lem7586759 {A B : Type'} (f : A -> B) (y : A) : (term142 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7586760 (f : real -> real) (y : real) : (term143 f y) = (f y).
Proof. exact (@lem7586759 real real f y). Qed.
Lemma lem7586761 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term182 p q' q x) = (term183 p q' q x).
Proof. exact (@lem7586760 (term181 p q') (q x)). Qed.
Lemma lem7586762 (p : real -> real) (q' : real -> real) (x : real) : (term184 p q' x) = (term185 p q' x).
Proof. exact (eq_refl (term184 p q' x)). Qed.
Lemma lem7586763 (p : real -> real) (q' : real -> real) : (term186 p q') = (term181 p q').
Proof. exact (fun_ext (fun x : real => @lem7586762 p q' x)). Qed.
Lemma lem7586764 (q : real -> real) (x : real) : (q x) = (q x).
Proof. exact (eq_refl (q x)). Qed.
Lemma lem7586765 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term182 p q' q x) = (term183 p q' q x).
Proof. exact (MK_COMB (@lem7586763 p q') (@lem7586764 q x)). Qed.
Lemma lem7586766 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7586767 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term187 p q' q x) = (term188 p q' q x).
Proof. exact (MK_COMB (@lem7586766) (@lem7586765 p q' q x)). Qed.
Lemma lem7586768 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term183 p q' q x) = (term189 p q' q x).
Proof. exact (eq_refl (term183 p q' q x)). Qed.
Lemma lem7586769 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : ((term182 p q' q x) = (term183 p q' q x)) = ((term183 p q' q x) = (term189 p q' q x)).
Proof. exact (MK_COMB (@lem7586767 p q' q x) (@lem7586768 p q' q x)). Qed.
Lemma lem7586770 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term183 p q' q x) = (term189 p q' q x).
Proof. exact (EQ_MP (@lem7586769 p q' q x) (@lem7586761 p q' q x)). Qed.
Lemma lem7586771 (p : real -> real) (q' : real -> real) (q : real -> real) : (term180 p q' q) = (term190 p q' q).
Proof. exact (fun_ext (fun x : real => @lem7586770 p q' q x)). Qed.
Lemma lem7586772 (p : real -> real) (q' : real -> real) (q : real -> real) : (term179 p q' q) = (term190 p q' q).
Proof. exact (TRANS (@lem7586757 p q' q) (@lem7586771 p q' q)). Qed.
Lemma lem7586773 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586774 (p : real -> real) (q' : real -> real) (q : real -> real) : (term101 p q' q) = (term191 p q' q).
Proof. exact (MK_COMB (@lem7586773) (@lem7586772 p q' q)). Qed.
Lemma lem7586776 (p : real -> real) (q : real -> real) : term192 p q.
Proof. exact (fun h0 : term4 p q => @lem7586397 p q h0). Qed.
Lemma lem7586777 (p : real -> real) (q' : real -> real) (q : real -> real) : term193 p q' q.
Proof. exact (@lem7586776 (term138 p q) (term138 q' q)). Qed.
Lemma lem7586778 (p : real -> real) (q : real -> real) (x : real) : (term194 p q x) = (term195 p q x).
Proof. exact (eq_refl (term194 p q x)). Qed.
Lemma lem7586779 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7586780 (p : real -> real) (q : real -> real) (x : real) : (term196 p q x) = (term197 p q x).
Proof. exact (MK_COMB (@lem7586779) (@lem7586778 p q x)). Qed.
Lemma lem7586781 (q' : real -> real) (q : real -> real) (x : real) : (term194 q' q x) = (term195 q' q x).
Proof. exact (eq_refl (term194 q' q x)). Qed.
Lemma lem7586782 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term198 p q' q x) = (term189 p q' q x).
Proof. exact (MK_COMB (@lem7586780 p q x) (@lem7586781 q' q x)). Qed.
Lemma lem7586783 (p : real -> real) (q' : real -> real) (q : real -> real) : (term199 p q' q) = (term190 p q' q).
Proof. exact (fun_ext (fun x : real => @lem7586782 p q' q x)). Qed.
Lemma lem7586784 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586785 (p : real -> real) (q' : real -> real) (q : real -> real) : (term200 p q' q) = (term191 p q' q).
Proof. exact (MK_COMB (@lem7586784) (@lem7586783 p q' q)). Qed.
Lemma lem7586786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7586787 (p : real -> real) (q' : real -> real) (q : real -> real) : (term201 p q' q) = (term202 p q' q).
Proof. exact (MK_COMB (@lem7586786) (@lem7586785 p q' q)). Qed.
Lemma lem7586788 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7586789 (p : real -> real) (q' : real -> real) (q : real -> real) : ((term200 p q' q) = True) = ((term191 p q' q) = True).
Proof. exact (MK_COMB (@lem7586787 p q' q) (@lem7586788)). Qed.
Lemma lem7586790 (p : real -> real) (q' : real -> real) (q : real -> real) : (term203 p q' q) = (term203 p q' q).
Proof. exact (eq_refl (term203 p q' q)). Qed.
Lemma lem7586791 (p : real -> real) (q' : real -> real) (q : real -> real) : (term193 p q' q) = (term204 p q' q).
Proof. exact (MK_COMB (@lem7586790 p q' q) (@lem7586789 p q' q)). Qed.
Lemma lem7586792 (p : real -> real) (q' : real -> real) (q : real -> real) : term204 p q' q.
Proof. exact (EQ_MP (@lem7586791 p q' q) (@lem7586777 p q' q)). Qed.
Lemma lem7586796 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term174 p q) = True.
Proof. exact (EQ_MP (@lem7586752 p q) (@lem7586751 p q' q h1)). Qed.
Lemma lem7586797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586798 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term175 p q) = (and True).
Proof. exact (MK_COMB (@lem7586797) (@lem7586796 p q' q h1)). Qed.
Lemma lem7586800 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term174 q' q) = True.
Proof. exact (EQ_MP (@lem7586749 q' q) (@lem7586748 p q' q h1)). Qed.
Lemma lem7586801 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term176 p q' q) = (True /\ True).
Proof. exact (MK_COMB (@lem7586798 p q' q h1) (@lem7586800 p q' q h1)). Qed.
Lemma lem7586803 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7586804 : (True /\ True) = True.
Proof. exact (@lem7586803 True). Qed.
Lemma lem7586805 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term176 p q' q) = True.
Proof. exact (TRANS (@lem7586801 p q' q h1) (@lem7586804)). Qed.
Lemma lem7586806 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : True = (term176 p q' q).
Proof. exact (SYM (@lem7586805 p q' q h1)). Qed.
Lemma lem7586807 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term176 p q' q.
Proof. exact (EQ_MP (@lem7586806 p q' q h1) (@lem0)). Qed.
Lemma lem7586808 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term191 p q' q) = True.
Proof. exact (@lem7586792 p q' q (@lem7586807 p q' q h1)). Qed.
Lemma lem7586809 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term101 p q' q) = True.
Proof. exact (TRANS (@lem7586774 p q' q) (@lem7586808 p q' q h1)). Qed.
Lemma lem7586810 (p : real -> real) (q' : real -> real) (q : real -> real) : term205 p q' q.
Proof. exact (fun h0 : term176 p q' q => @lem7586809 p q' q h0). Qed.
Lemma lem7586811 (p : real -> real) (q' : real -> real) (q : real -> real) : term206 p q' q.
Proof. exact (@lem7586746 p q' q True). Qed.
Lemma lem7586812 (p : real -> real) (q' : real -> real) (q : real -> real) : (term103 p q' q) = (term207 p q' q).
Proof. exact (@lem7586811 p q' q (@lem7586810 p q' q)). Qed.
Lemma lem7586814 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7586815 (p : real -> real) (q' : real -> real) (q : real -> real) : (term207 p q' q) = True.
Proof. exact (@lem7586814 (term176 p q' q)). Qed.
Lemma lem7586816 (p : real -> real) (q' : real -> real) (q : real -> real) : (term103 p q' q) = True.
Proof. exact (TRANS (@lem7586812 p q' q) (@lem7586815 p q' q)). Qed.
Lemma lem7586817 (p : real -> real) (q : real -> real) : (term105 p q) = term208.
Proof. exact (fun_ext (fun q' : real -> real => @lem7586816 p q' q)). Qed.
Lemma lem7586818 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586819 (p : real -> real) (q : real -> real) : (term107 p q) = term209.
Proof. exact (MK_COMB (@lem7586818) (@lem7586817 p q)). Qed.
Lemma lem7586821 {A : Type'} (t : Prop) : (term210 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7586822 (t : Prop) : (term211 t) = t.
Proof. exact (@lem7586821 (real -> real) t). Qed.
Lemma lem7586823 : term209 = True.
Proof. exact (@lem7586822 True). Qed.
Lemma lem7586824 (p : real -> real) (q : real -> real) : (term107 p q) = True.
Proof. exact (TRANS (@lem7586819 p q) (@lem7586823)). Qed.
Lemma lem7586825 (q : real -> real) : (term109 q) = term208.
Proof. exact (fun_ext (fun p : real -> real => @lem7586824 p q)). Qed.
Lemma lem7586826 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586827 (q : real -> real) : (term111 q) = term209.
Proof. exact (MK_COMB (@lem7586826) (@lem7586825 q)). Qed.
Lemma lem7586829 {A : Type'} (t : Prop) : (term210 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7586830 (t : Prop) : (term211 t) = t.
Proof. exact (@lem7586829 (real -> real) t). Qed.
Lemma lem7586831 : term209 = True.
Proof. exact (@lem7586830 True). Qed.
Lemma lem7586832 (q : real -> real) : (term111 q) = True.
Proof. exact (TRANS (@lem7586827 q) (@lem7586831)). Qed.
Lemma lem7586833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586834 (q : real -> real) : (term113 q) = (and True).
Proof. exact (MK_COMB (@lem7586833) (@lem7586832 q)). Qed.
Lemma lem7586846 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term166 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7586847 (p : Prop) (q : Prop) (p' : Prop) : term167 p q p'.
Proof. exact (fun q' : Prop => @lem7586846 p q p' q'). Qed.
Lemma lem7586848 (p : Prop) (q : Prop) : term168 p q.
Proof. exact (fun p' : Prop => @lem7586847 p q p'). Qed.
Lemma lem7586849 (p : real -> real) (q' : real -> real) (q : real -> real) : term212 p q' q.
Proof. exact (@lem7586848 (term97 p q' q) (term115 p q' q)). Qed.
Lemma lem7586850 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) : term213 p q' q p'.
Proof. exact (@lem7586849 p q' q p'). Qed.
Lemma lem7586851 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) : (term213 p q' q p') = (term214 p q' q p').
Proof. exact (eq_refl (term213 p q' q p')). Qed.
Lemma lem7586852 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) : term214 p q' q p'.
Proof. exact (EQ_MP (@lem7586851 p q' q p') (@lem7586850 p q' q p')). Qed.
Lemma lem7586853 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) (q'' : Prop) : term215 p q' q p' q''.
Proof. exact (@lem7586852 p q' q p' q''). Qed.
Lemma lem7586854 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) (q'' : Prop) : (term215 p q' q p' q'') = (term216 p q' q p' q'').
Proof. exact (eq_refl (term215 p q' q p' q'')). Qed.
Lemma lem7586855 (p : real -> real) (q' : real -> real) (q : real -> real) (p' : Prop) (q'' : Prop) : term216 p q' q p' q''.
Proof. exact (EQ_MP (@lem7586854 p q' q p' q'') (@lem7586853 p q' q p' q'')). Qed.
Lemma lem7586859 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586860 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586859 real real real f g). Qed.
Lemma lem7586861 (p : real -> real) (q : real -> real) : (@o real real real p q) = (term138 p q).
Proof. exact (@lem7586860 p q). Qed.
Lemma lem7586862 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586863 (p : real -> real) (q : real -> real) : (term58 p q) = (term174 p q).
Proof. exact (MK_COMB (@lem7586862) (@lem7586861 p q)). Qed.
Lemma lem7586864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586865 (p : real -> real) (q : real -> real) : (term95 p q) = (term175 p q).
Proof. exact (MK_COMB (@lem7586864) (@lem7586863 p q)). Qed.
Lemma lem7586867 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586868 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586867 real real real f g). Qed.
Lemma lem7586869 (q' : real -> real) (q : real -> real) : (@o real real real q' q) = (term138 q' q).
Proof. exact (@lem7586868 q' q). Qed.
Lemma lem7586870 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586871 (q' : real -> real) (q : real -> real) : (term58 q' q) = (term174 q' q).
Proof. exact (MK_COMB (@lem7586870) (@lem7586869 q' q)). Qed.
Lemma lem7586872 (p : real -> real) (q' : real -> real) (q : real -> real) : (term97 p q' q) = (term176 p q' q).
Proof. exact (MK_COMB (@lem7586865 p q) (@lem7586871 q' q)). Qed.
Lemma lem7586875 (p : real -> real) (q' : real -> real) (q : real -> real) (q'' : Prop) : term217 p q' q q''.
Proof. exact (@lem7586855 p q' q (term176 p q' q) q''). Qed.
Lemma lem7586876 (p : real -> real) (q' : real -> real) (q : real -> real) (q'' : Prop) : term218 p q' q q''.
Proof. exact (@lem7586875 p q' q q'' (@lem7586872 p q' q)). Qed.
Lemma lem7586877 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term176 p q' q.
Proof. exact (h1). Qed.
Lemma lem7586878 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term174 q' q.
Proof. exact (proj2 (@lem7586877 p q' q h1)). Qed.
Lemma lem7586879 (q' : real -> real) (q : real -> real) : (term174 q' q) = ((term174 q' q) = True).
Proof. exact (@lem7 (term174 q' q)). Qed.
Lemma lem7586881 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term174 p q.
Proof. exact (proj1 (@lem7586877 p q' q h1)). Qed.
Lemma lem7586882 (p : real -> real) (q : real -> real) : (term174 p q) = ((term174 p q) = True).
Proof. exact (@lem7 (term174 p q)). Qed.
Lemma lem7586885 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term14 A B C f g).
Proof. exact (EQ_MP (@lem7586407 A B C f g) (@lem7586406 A B C f g)). Qed.
Lemma lem7586886 (f : real -> real) (g : real -> real) : (@o real real real f g) = (term138 f g).
Proof. exact (@lem7586885 real real real f g). Qed.
Lemma lem7586887 (p : real -> real) (q' : real -> real) (q : real -> real) : (term219 p q' q) = (term220 p q' q).
Proof. exact (@lem7586886 (term221 p q') q). Qed.
Lemma lem7586889 {A B : Type'} (f : A -> B) (y : A) : (term142 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7586890 (f : real -> real) (y : real) : (term143 f y) = (f y).
Proof. exact (@lem7586889 real real f y). Qed.
Lemma lem7586891 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term222 p q' q x) = (term223 p q' q x).
Proof. exact (@lem7586890 (term221 p q') (q x)). Qed.
Lemma lem7586892 (p : real -> real) (q' : real -> real) (x : real) : (term224 p q' x) = (term225 p q' x).
Proof. exact (eq_refl (term224 p q' x)). Qed.
Lemma lem7586893 (p : real -> real) (q' : real -> real) : (term226 p q') = (term221 p q').
Proof. exact (fun_ext (fun x : real => @lem7586892 p q' x)). Qed.
Lemma lem7586894 (q : real -> real) (x : real) : (q x) = (q x).
Proof. exact (eq_refl (q x)). Qed.
Lemma lem7586895 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term222 p q' q x) = (term223 p q' q x).
Proof. exact (MK_COMB (@lem7586893 p q') (@lem7586894 q x)). Qed.
Lemma lem7586896 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7586897 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term227 p q' q x) = (term228 p q' q x).
Proof. exact (MK_COMB (@lem7586896) (@lem7586895 p q' q x)). Qed.
Lemma lem7586898 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term223 p q' q x) = (term229 p q' q x).
Proof. exact (eq_refl (term223 p q' q x)). Qed.
Lemma lem7586899 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : ((term222 p q' q x) = (term223 p q' q x)) = ((term223 p q' q x) = (term229 p q' q x)).
Proof. exact (MK_COMB (@lem7586897 p q' q x) (@lem7586898 p q' q x)). Qed.
Lemma lem7586900 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term223 p q' q x) = (term229 p q' q x).
Proof. exact (EQ_MP (@lem7586899 p q' q x) (@lem7586891 p q' q x)). Qed.
Lemma lem7586901 (p : real -> real) (q' : real -> real) (q : real -> real) : (term220 p q' q) = (term230 p q' q).
Proof. exact (fun_ext (fun x : real => @lem7586900 p q' q x)). Qed.
Lemma lem7586902 (p : real -> real) (q' : real -> real) (q : real -> real) : (term219 p q' q) = (term230 p q' q).
Proof. exact (TRANS (@lem7586887 p q' q) (@lem7586901 p q' q)). Qed.
Lemma lem7586903 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586904 (p : real -> real) (q' : real -> real) (q : real -> real) : (term115 p q' q) = (term231 p q' q).
Proof. exact (MK_COMB (@lem7586903) (@lem7586902 p q' q)). Qed.
Lemma lem7586906 (p : real -> real) (q : real -> real) : term232 p q.
Proof. exact (fun h0 : term4 p q => @lem7586382 p q h0). Qed.
Lemma lem7586907 (p : real -> real) (q' : real -> real) (q : real -> real) : term233 p q' q.
Proof. exact (@lem7586906 (term138 p q) (term138 q' q)). Qed.
Lemma lem7586908 (p : real -> real) (q : real -> real) (x : real) : (term194 p q x) = (term195 p q x).
Proof. exact (eq_refl (term194 p q x)). Qed.
Lemma lem7586909 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7586910 (p : real -> real) (q : real -> real) (x : real) : (term234 p q x) = (term235 p q x).
Proof. exact (MK_COMB (@lem7586909) (@lem7586908 p q x)). Qed.
Lemma lem7586911 (q' : real -> real) (q : real -> real) (x : real) : (term194 q' q x) = (term195 q' q x).
Proof. exact (eq_refl (term194 q' q x)). Qed.
Lemma lem7586912 (p : real -> real) (q' : real -> real) (q : real -> real) (x : real) : (term236 p q' q x) = (term229 p q' q x).
Proof. exact (MK_COMB (@lem7586910 p q x) (@lem7586911 q' q x)). Qed.
Lemma lem7586913 (p : real -> real) (q' : real -> real) (q : real -> real) : (term237 p q' q) = (term230 p q' q).
Proof. exact (fun_ext (fun x : real => @lem7586912 p q' q x)). Qed.
Lemma lem7586914 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7586915 (p : real -> real) (q' : real -> real) (q : real -> real) : (term238 p q' q) = (term231 p q' q).
Proof. exact (MK_COMB (@lem7586914) (@lem7586913 p q' q)). Qed.
Lemma lem7586916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7586917 (p : real -> real) (q' : real -> real) (q : real -> real) : (term239 p q' q) = (term240 p q' q).
Proof. exact (MK_COMB (@lem7586916) (@lem7586915 p q' q)). Qed.
Lemma lem7586918 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem7586919 (p : real -> real) (q' : real -> real) (q : real -> real) : ((term238 p q' q) = True) = ((term231 p q' q) = True).
Proof. exact (MK_COMB (@lem7586917 p q' q) (@lem7586918)). Qed.
Lemma lem7586920 (p : real -> real) (q' : real -> real) (q : real -> real) : (term203 p q' q) = (term203 p q' q).
Proof. exact (eq_refl (term203 p q' q)). Qed.
Lemma lem7586921 (p : real -> real) (q' : real -> real) (q : real -> real) : (term233 p q' q) = (term241 p q' q).
Proof. exact (MK_COMB (@lem7586920 p q' q) (@lem7586919 p q' q)). Qed.
Lemma lem7586922 (p : real -> real) (q' : real -> real) (q : real -> real) : term241 p q' q.
Proof. exact (EQ_MP (@lem7586921 p q' q) (@lem7586907 p q' q)). Qed.
Lemma lem7586926 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term174 p q) = True.
Proof. exact (EQ_MP (@lem7586882 p q) (@lem7586881 p q' q h1)). Qed.
Lemma lem7586927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7586928 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term175 p q) = (and True).
Proof. exact (MK_COMB (@lem7586927) (@lem7586926 p q' q h1)). Qed.
Lemma lem7586930 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term174 q' q) = True.
Proof. exact (EQ_MP (@lem7586879 q' q) (@lem7586878 p q' q h1)). Qed.
Lemma lem7586931 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term176 p q' q) = (True /\ True).
Proof. exact (MK_COMB (@lem7586928 p q' q h1) (@lem7586930 p q' q h1)). Qed.
Lemma lem7586933 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7586934 : (True /\ True) = True.
Proof. exact (@lem7586933 True). Qed.
Lemma lem7586935 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term176 p q' q) = True.
Proof. exact (TRANS (@lem7586931 p q' q h1) (@lem7586934)). Qed.
Lemma lem7586936 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : True = (term176 p q' q).
Proof. exact (SYM (@lem7586935 p q' q h1)). Qed.
Lemma lem7586937 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : term176 p q' q.
Proof. exact (EQ_MP (@lem7586936 p q' q h1) (@lem0)). Qed.
Lemma lem7586938 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term231 p q' q) = True.
Proof. exact (@lem7586922 p q' q (@lem7586937 p q' q h1)). Qed.
Lemma lem7586939 (p : real -> real) (q' : real -> real) (q : real -> real) (h1 : term176 p q' q) : (term115 p q' q) = True.
Proof. exact (TRANS (@lem7586904 p q' q) (@lem7586938 p q' q h1)). Qed.
Lemma lem7586940 (p : real -> real) (q' : real -> real) (q : real -> real) : term242 p q' q.
Proof. exact (fun h0 : term176 p q' q => @lem7586939 p q' q h0). Qed.
Lemma lem7586941 (p : real -> real) (q' : real -> real) (q : real -> real) : term243 p q' q.
Proof. exact (@lem7586876 p q' q True). Qed.
Lemma lem7586942 (p : real -> real) (q' : real -> real) (q : real -> real) : (term117 p q' q) = (term207 p q' q).
Proof. exact (@lem7586941 p q' q (@lem7586940 p q' q)). Qed.
Lemma lem7586944 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7586945 (p : real -> real) (q' : real -> real) (q : real -> real) : (term207 p q' q) = True.
Proof. exact (@lem7586944 (term176 p q' q)). Qed.
Lemma lem7586946 (p : real -> real) (q' : real -> real) (q : real -> real) : (term117 p q' q) = True.
Proof. exact (TRANS (@lem7586942 p q' q) (@lem7586945 p q' q)). Qed.
Lemma lem7586947 (p : real -> real) (q : real -> real) : (term119 p q) = term208.
Proof. exact (fun_ext (fun q' : real -> real => @lem7586946 p q' q)). Qed.
Lemma lem7586948 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586949 (p : real -> real) (q : real -> real) : (term121 p q) = term209.
Proof. exact (MK_COMB (@lem7586948) (@lem7586947 p q)). Qed.
Lemma lem7586951 {A : Type'} (t : Prop) : (term210 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7586952 (t : Prop) : (term211 t) = t.
Proof. exact (@lem7586951 (real -> real) t). Qed.
Lemma lem7586953 : term209 = True.
Proof. exact (@lem7586952 True). Qed.
Lemma lem7586954 (p : real -> real) (q : real -> real) : (term121 p q) = True.
Proof. exact (TRANS (@lem7586949 p q) (@lem7586953)). Qed.
Lemma lem7586955 (q : real -> real) : (term123 q) = term208.
Proof. exact (fun_ext (fun p : real -> real => @lem7586954 p q)). Qed.
Lemma lem7586956 : (@all (real -> real)) = (@all (real -> real)).
Proof. exact (eq_refl (@all (real -> real))). Qed.
Lemma lem7586957 (q : real -> real) : (term125 q) = term209.
Proof. exact (MK_COMB (@lem7586956) (@lem7586955 q)). Qed.
Lemma lem7586959 {A : Type'} (t : Prop) : (term210 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7586960 (t : Prop) : (term211 t) = t.
Proof. exact (@lem7586959 (real -> real) t). Qed.
Lemma lem7586961 : term209 = True.
Proof. exact (@lem7586960 True). Qed.
Lemma lem7586962 (q : real -> real) : (term125 q) = True.
Proof. exact (TRANS (@lem7586957 q) (@lem7586961)). Qed.
Lemma lem7586963 (q : real -> real) : (term127 q) = (True /\ True).
Proof. exact (MK_COMB (@lem7586834 q) (@lem7586962 q)). Qed.
Lemma lem7586965 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7586966 : (True /\ True) = True.
Proof. exact (@lem7586965 True). Qed.
Lemma lem7586967 (q : real -> real) : (term127 q) = True.
Proof. exact (TRANS (@lem7586963 q) (@lem7586966)). Qed.
Lemma lem7586968 (q : real -> real) : (term129 q) = term244.
Proof. exact (MK_COMB (@lem7586698 q) (@lem7586967 q)). Qed.
Lemma lem7586970 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7586971 : term244 = term164.
Proof. exact (@lem7586970 term164). Qed.
Lemma lem7586976 (q : real -> real) : (term129 q) = term164.
Proof. exact (TRANS (@lem7586968 q) (@lem7586971)). Qed.
Lemma lem7586977 (q : real -> real) : (term131 q) = (term245 q).
Proof. exact (MK_COMB (@lem7586662 q) (@lem7586976 q)). Qed.
Lemma lem7586984 (q : real -> real) : (term245 q) = (term131 q).
Proof. exact (SYM (@lem7586977 q)). Qed.
Lemma lem7586985 (c : real) : term246 c.
Proof. exact (@lem7553635 c). Qed.
Lemma lem7586986 (c : real) : (term246 c) = (term162 c).
Proof. exact (eq_refl (term246 c)). Qed.
Lemma lem7586987 (c : real) : term162 c.
Proof. exact (EQ_MP (@lem7586986 c) (@lem7586985 c)). Qed.
Lemma lem7586988 (c : real) : (term162 c) = ((term162 c) = True).
Proof. exact (@lem7 (term162 c)). Qed.
Lemma lem7586990 {A B : Type'} (t : A -> B) : term247 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem7586991 {A B : Type'} (t : A -> B) : (term247 A B t) = ((term248 A B t) = t).
Proof. exact (eq_refl (term247 A B t)). Qed.
Lemma lem7586992 {A B : Type'} (t : A -> B) : (term248 A B t) = t.
Proof. exact (EQ_MP (@lem7586991 A B t) (@lem7586990 A B t)). Qed.
Lemma lem7586993 (q : real -> real) : (polynomial_function q) = ((polynomial_function q) = True).
Proof. exact (@lem7 (polynomial_function q)). Qed.
Lemma lem7587000 (t : real -> real) : (term150 t) = t.
Proof. exact (@lem7586992 real real t). Qed.
Lemma lem7587001 (q : real -> real) : (term150 q) = q.
Proof. exact (@lem7587000 q). Qed.
Lemma lem7587002 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7587003 (q : real -> real) : (term151 q) = (polynomial_function q).
Proof. exact (MK_COMB (@lem7587002) (@lem7587001 q)). Qed.
Lemma lem7587005 (q : real -> real) (h1 : polynomial_function q) : (polynomial_function q) = True.
Proof. exact (EQ_MP (@lem7586993 q) (@lem7586580 q h1)). Qed.
Lemma lem7587006 (q : real -> real) (h1 : polynomial_function q) : (term151 q) = True.
Proof. exact (TRANS (@lem7587003 q) (@lem7587005 q h1)). Qed.
Lemma lem7587007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7587008 (q : real -> real) (h1 : polynomial_function q) : (term152 q) = (and True).
Proof. exact (MK_COMB (@lem7587007) (@lem7587006 q h1)). Qed.
Lemma lem7587014 (c : real) : (term162 c) = True.
Proof. exact (EQ_MP (@lem7586988 c) (@lem7586987 c)). Qed.
Lemma lem7587015 : term163 = term249.
Proof. exact (fun_ext (fun c : real => @lem7587014 c)). Qed.
Lemma lem7587016 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7587017 : term164 = term250.
Proof. exact (MK_COMB (@lem7587016) (@lem7587015)). Qed.
Lemma lem7587019 {A : Type'} (t : Prop) : (term210 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7587020 (t : Prop) : (term251 t) = t.
Proof. exact (@lem7587019 real t). Qed.
Lemma lem7587021 : term250 = True.
Proof. exact (@lem7587020 True). Qed.
Lemma lem7587022 : term164 = True.
Proof. exact (TRANS (@lem7587017) (@lem7587021)). Qed.
Lemma lem7587023 (q : real -> real) (h1 : polynomial_function q) : (term245 q) = (True /\ True).
Proof. exact (MK_COMB (@lem7587008 q h1) (@lem7587022)). Qed.
Lemma lem7587025 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7587026 : (True /\ True) = True.
Proof. exact (@lem7587025 True). Qed.
Lemma lem7587027 (q : real -> real) (h1 : polynomial_function q) : (term245 q) = True.
Proof. exact (TRANS (@lem7587023 q h1) (@lem7587026)). Qed.
Lemma lem7587028 (q : real -> real) (h1 : polynomial_function q) : True = (term245 q).
Proof. exact (SYM (@lem7587027 q h1)). Qed.
Lemma lem7587029 (q : real -> real) (h1 : polynomial_function q) : term245 q.
Proof. exact (EQ_MP (@lem7587028 q h1) (@lem0)). Qed.
Lemma lem7587030 (q : real -> real) (h1 : polynomial_function q) : term131 q.
Proof. exact (EQ_MP (@lem7586984 q) (@lem7587029 q h1)). Qed.
Lemma lem7587031 (q : real -> real) (h1 : polynomial_function q) : term75 q.
Proof. exact (@lem7586637 q (@lem7587030 q h1)). Qed.
Lemma lem7587032 (q : real -> real) : term76 q.
Proof. exact (fun h0 : polynomial_function q => @lem7587031 q h0). Qed.
Lemma lem7587037 : term78.
Proof. exact (fun q : real -> real => @lem7587032 q). Qed.
Lemma lem7587038 : term54.
Proof. exact (EQ_MP (@lem7586579) (@lem7587037)). Qed.
Lemma lem7587039 : term45.
Proof. exact (EQ_MP (@lem7586464) (@lem7587038)). Qed.
